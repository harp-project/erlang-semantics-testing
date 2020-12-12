#!/usr/bin/env escript
%%! -i -pa converter -pa generator/ebin -pa eqc-2.01.0/ebin

-module(scripts).

% -include_lib("eqc/include/eqc.hrl"). % This does not work on Windows Subsystem for Linux
-include("./eqc-2.01.0/include/eqc.hrl").

-compile([export_all]).

-define(REPORT_DIRECTORY, "./reports/").
-define(COQ_FILENAME, "./reports/coq_coverage.csv").

-define(ENABLE_SHRINKING, false).

remove_extension(Filename) ->
    hd(string:split(Filename, ".", trailing)).

remove_directory(Path) ->
    case string:find(Path, "/", trailing) of
        nomatch -> Path;
        Matching -> string:substr(Matching, 2)
    end.

mktmpdir() ->
    TimeInSeconds = erlang:system_time(second),
    %Date = calendar:system_time_to_rfc3339(TimeInSeconds),
    DirPath = io_lib:format("~ssemantic-tester-~p/", [?REPORT_DIRECTORY, TimeInSeconds]),
    filelib:ensure_dir(DirPath),
    io:format("Report Directory created: ~s~n", [DirPath]),
    DirPath.

report(Test, ReportDirectory, Result, Success) ->
    write_to_file(ReportDirectory ++ Test ++ ".result", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success]), write),
    case Success of
       false -> io:format("~n ~s failed ~p~n", [Test, Result]),
                io:format("X");
       true  -> io:format(".")
    end.

compare_results([{Ok, Head} | Tail]) ->
    lists:all(fun(Elem) ->
                 case Elem of
                   {Ok, {Result, _}} -> Result == Head;
                   {Ok, Result}      -> Result == Head;
                   _                 -> io:format("Illegal result format!~n"), 
                                        false
                 end
                   end, Tail);
compare_results(_) -> io:format("Illegal result format!~n"), false.

%% returns Bool
execute_and_compare_result(Test, ReportDirectory) ->
    Basename = remove_extension(Test),
    ModuleName = remove_directory(Basename),
    Result = [
        execute_erl:execute(Basename, ModuleName, ReportDirectory),
        execute_coq:execute(Basename, ModuleName, ReportDirectory)
        %execute_k:execute(Basename, ModuleName, ReportDirectory)
    ],
    Success = compare_results(Result),
    report(ModuleName, ReportDirectory, Result, Success),
    
    update_coq_coverage(Result),
    Success.


%% ---------------------------------------------------------------------
%% Coq Coverage measurement

%% CAUTION: Uses the fact, that the Coq result is the second one in the list
%% returns #{...}
update_coq_coverage(Result) ->
  case Result of
    %% [Erlresult, {Ok, {Coqresult, CoqTrace}} | Rest]
    [_, {_, {_, CoqTrace}} | _] -> process_trace(CoqTrace);
    _                           -> #{}
  end
.

%% Processes the semantic trace of the used rules, and updates the report map
%% returns #{...}
process_trace(Trace) ->
  ReportMap = get(coq_coverage_map),
  UpdatedReportMap = lists:foldr(fun(Elem, Acc) ->
                                      maps:update_with(Elem, fun(X) -> X + 1 end, Acc) 
                                 end, ReportMap, Trace),
  put(coq_coverage_map, UpdatedReportMap).

%% FILL UP INITIAL MAP WITH KEY-0 PAIRS
default_map() ->
  lists:foldr(fun(Elem, Acc) -> maps:put(Elem, 0, Acc) end, #{}, semantic_rules()).

%% RULE CATEGORIES

coq_list_rules() -> ['_LIST_CONS', '_LIST_EMPTY', '_LIST_EX_PROP', '_LIST_EX_CREATE'].
case_rules() -> ['_CASE', '_CASE_EX','_CASE_IFCLAUSE'].
case_helper_rules() -> ['_CASE_TRUE', '_CASE_FALSE', '_CASE_NOMATCH'].
apply_rules() -> ['_APP', '_APP_EX', '_APP_EX_PARAM', '_APP_EX_BADFUN', '_APP_EX_BADARITY'].
list_rules() -> ['_CONS', '_NIL', '_CONS_HD_EX', '_CONS_TL_EX'].
call_rules() -> ['_CALL', '_CALL_EX'].
primop_rules() -> ['_PRIMOP', '_PRIMOP_EX'].
try_rules() -> ['_TRY', '_CATCH'].
variable_rule() -> ['_VAR'].
funid_rule() -> ['_FUNID'].
literal_rule() -> ['_LIT'].
fun_rule() -> ['_FUN'].
tuple_rules() -> ['_TUPLE', '_TUPLE_EX'].
let_rules() -> ['_LET', '_LET_EX'].
seq_rules() -> ['_SEQ', '_SEQ_EX'].
map_rules() -> ['_MAP', '_MAP_EX'].
letrec_rule() -> ['_LETREC'].
exp_list_rules() -> ['_VALUES'].
single_rule() -> ['_SINGLE'].
error_rules() ->  ['_FAIL', '_TIMEOUT'].

%% Semantics rules not including exceptional evaluation
exceptionfree_rules() -> ['_LIST_CONS', '_LIST_EMPTY', '_CASE', '_CASE_TRUE', '_CASE_FALSE', '_CASE_NOMATCH',
                          '_APP', '_CONS', '_NIL', '_CALL', '_PRIMOP', '_VAR', '_FUNID', '_LIT',
                          '_FUN', '_TUPLE', '_LET', '_SEQ', '_MAP', '_LETREC', '_VALUES', '_SINGLE'].

%% All semantics rules
semantic_rules() -> coq_list_rules() ++ case_rules() ++ case_helper_rules() ++ apply_rules() ++ list_rules() ++ call_rules() ++
                    primop_rules() ++ try_rules() ++ variable_rule() ++ funid_rule() ++ literal_rule() ++ fun_rule() ++ error_rules() ++
                    tuple_rules() ++ let_rules() ++ seq_rules() ++ map_rules() ++ letrec_rule() ++ exp_list_rules() ++ single_rule().

%% ---------------------------------------------------------------------


write_to_file(Filename, Content, Mode) ->
    case file:open(Filename, [Mode]) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.

count_if(Pred, Lists) ->
    length(lists:filter(Pred, Lists)).

count(Elem, Lists) ->
    count_if(fun(X) -> Elem == X end, Lists).

unit_test(Tests) when is_list(Tests) ->
    ReportDirectory = mktmpdir(),
    [execute_and_compare_result(Test, ReportDirectory) || Test <- Tests].

%% ---------------------------------------------------------------------
%% QuickCheck

-define(ModuleNamePlaceHolder, "modulenameplaceholder").

save_test(String, Id, ReportDirectory) ->
    ModuleName = io_lib:format("module~p", [Id]),
    Basename = ModuleName ++ ".erl",
    Filename = ReportDirectory ++ Basename,
    write_to_file(Filename, String, write),
    Filename.

is_compilable(T) ->
    S = [erl_syntax:revert(T2) || T2 <- erl_syntax:form_list_elements(eval(T))],
    C = compile:forms(S, [strong_validation, return_errors, nowarn_unused_vars]),
    element(1, C) /= ok andalso io:format("\nnem fordul:(\n"),
    element(1, C) == ok.

random_test(NumTests) ->
    put(test_id, 0),
    random:seed(erlang:now()),
    ReportDirectory = mktmpdir(),
    G = resize(20, erlgen:module(?ModuleNamePlaceHolder, 20)),
    G2 = ?LET(M, G, case lists:keysearch(value, 1, M) of
                        {value, {_, Value}} -> Value;
                        false -> []
                    end),
    G3 = ?SUCHTHAT(T, G2, is_compilable(T)),
    P = ?FORALL(T, if ?ENABLE_SHRINKING -> G3; true -> noshrink(G3) end,
          %?WHENFAIL(io:format("~n~s~n", [erl_prettypr:format(eqc_symbolic:eval(T))]),
            begin
                TestId = get(test_id),
                ModuleName = io_lib:format("module~p", [TestId]),
                put(test_id, TestId+1),
                RawProgramText = erl_prettypr:format(eqc_symbolic:eval(T)),
                ProgramText = re:replace(RawProgramText, ?ModuleNamePlaceHolder, ModuleName, [global, {return, list}]),
                FilePath = ReportDirectory ++ ModuleName ++ ".erl",
                write_to_file(FilePath, ProgramText, write),
                execute_and_compare_result(FilePath, ReportDirectory)
            end
          %)
        ),
    [eqc:quickcheck(eqc:numtests(NumTests, P))],
    noreport.

%% ---------------------------------------------------------------------

report_result(help) ->
    io:format("wrong number of arguments~n");
report_result(noreport) ->
    noreport;
report_result(Results) ->
    io:format("All ~p Passed ~p Failed ~p~n", [
        length(Results),
        count(true, Results),
        length(Results) - count(true, Results)
    ]),
  
%% ---------------------------------------------------------------------
  %% Reporting coverage
  
  %% Rule coverage map:
    CoqCoverage = get(coq_coverage_map),
  
  %% used rule percent
    UsedRulesNr = maps:size(maps:filter(fun(_, V) -> V > 0 end, CoqCoverage)),
    Semantics_rules = semantic_rules(),
    io:format("~n~nCoq coverage data:~n"),
    io:format("Rule coverage: ~p %~n", [(UsedRulesNr / length(Semantics_rules)) * 100]),
  
  %% used exception-free rule percent
    ExcFreeRules = exceptionfree_rules(),
    UsedExceptionFreeRulesNr = maps:size(maps:filter(fun(K, V) -> lists:member(K, ExcFreeRules) and (V > 0) end, CoqCoverage)),
    io:format("Rule coverage without exceptions: ~p %~n", [(UsedExceptionFreeRulesNr / length(ExcFreeRules)) * 100]),
   
  %% How many times were specific rules used
    io:format("~nRules used:~n~n"),
    pp_map(CoqCoverage),
  
  %% Report results to coq_coverage.cs
  StatLine = maps:fold(fun(_, V, Acc) -> integer_to_list(V) ++ ";" ++ Acc end, "\n", CoqCoverage), % "~n" does not work here, only "\n"
  case filelib:is_regular(?COQ_FILENAME) of
    %% No header needed
    true  -> write_to_file(?COQ_FILENAME, StatLine, append);
    
    %% header needed
    false ->
      begin
        HeaderLine = maps:fold(fun(K, _, Acc) -> atom_to_list(K) ++ ";" ++ Acc end, "\n", CoqCoverage),
        write_to_file(?COQ_FILENAME, HeaderLine ++ StatLine, append)
      end
  end
  
%% ---------------------------------------------------------------------
    .

%% Map pretty-printer
pp_map(Map) when is_map(Map) ->
  %% workaround, we need foreach
  maps:fold(fun(K, V, Acc) -> io:format("~p rule was used ~p times~n", [K, V]), Acc end, 0, Map).

parser_main_arguments([]) ->
    help;
parser_main_arguments(Args) when is_list(Args) ->
    case Args of
        ["random", N] -> {runRandTests, list_to_integer(N)};
        _             -> {runUnitTests, Args}
    end;
parser_main_arguments(_) ->
    help.

main(Args) ->
  %% Initialize with the Coq coverage map, where all rules were used 0 times:
    put(coq_coverage_map, default_map()),

    Results = case parser_main_arguments(Args) of
        {runRandTests, NoT} -> random_test(NoT);
        {runUnitTests, LoT} -> unit_test(LoT);
        _                   -> help
    end,
    report_result(Results).
