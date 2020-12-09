#!/usr/bin/env escript
%%! -i -pa converter -pa generator/ebin -pa eqc-2.01.0/ebin

-module(scripts).

% -include_lib("eqc/include/eqc.hrl"). % This does not work on Windows Subsystem for Linux
-include("./eqc-2.01.0/include/eqc.hrl").

-compile([export_all]).

-define(REPORT_DIRECTORY, "./reports/").

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
    write_to_file(ReportDirectory ++ Test ++ ".result", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success])),
    case Success of
       false -> io:format("~n ~s failed ~p~n", [Test, Result]),
                io:format("X");
       true  -> io:format(".")
    end.

compare_results([{Ok, Head} | Tail]) ->
    lists:all(fun(Elem) ->
                 case Elem of
                   {Ok, {Result, Trace}} -> Result == Head;
                   {Ok, Result}          -> Result == Head;
                   _                     -> io:format("Illegal result format!~n"), 
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
    io:format("~n~p~n", [Result]),
    Success.


%% ---------------------------------------------------------------------
%% Coq Coverage measurement

%% CAUTION: Uses the fact, that the Coq result is the second one in the list
%% returns #{...}
update_coq_coverage(Result) ->
  case Result of
    [ErlResult, {Ok, {CoqResult, CoqTrace}} | _] -> process_trace(CoqTrace);
    _                                            -> #{}
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

coq_list_rules() -> ['_EVAL_LIST_CONS', '_EVAL_LIST_EMPTY', '_EVAL_LIST_EX_PROP', '_EVAL_LIST_EX_CREATE'].
case_rules() -> ['_EVAL_CASE', '_EVAL_CASE_EX','_EVAL_CASE_IFCLAUSE'].
case_helper_rules() -> ['_EVAL_CASE_TRUE', '_EVAL_CASE_FALSE', '_EVAL_CASE_NOMATCH'].
apply_rules() -> ['_EVAL_APP', '_EVAL_APP_EX', '_EVAL_APP_EX_PARAM', '_EVAL_APP_EX_BADFUN', '_EVAL_APP_EX_BADARITY'].
list_rules() -> ['_EVAL_CONS', '_EVAL_NIL', '_EVAL_CONS_HD_EX', '_EVAL_CONS_TL_EX'].
call_rules() -> ['_EVAL_CALL', '_EVAL_CALL_EX'].
primop_rules() -> ['_EVAL_PRIMOP', '_EVAL_PRIMOP_EX'].
try_rules() -> ['_EVAL_TRY', '_EVAL_CATCH'].
variable_rule() -> ['_EVAL_VAR'].
funid_rule() -> ['_EVAL_FUNID'].
literal_rule() -> ['_EVAL_LIT'].
fun_rule() -> ['_EVAL_FUN'].
tuple_rules() -> ['_EVAL_TUPLE', '_EVAL_TUPLE_EX'].
let_rules() -> ['_EVAL_LET', '_EVAL_LET_EX'].
seq_rules() -> ['_EVAL_SEQ', '_EVAL_SEQ_EX'].
map_rules() -> ['_EVAL_MAP', '_EVAL_MAP_EX'].
letrec_rule() -> ['_EVAL_LETREC'].
exp_list_rules() -> ['_EVAL_VALUES'].
single_rule() -> ['_EVAL_SINGLE'].
error_rules() ->  ['_FAIL', '_TIMEOUT'].

%% Semantics rules not including exceptional evaluation
exceptionfree_rules() -> ['_EVAL_LIST_CONS', '_EVAL_LIST_EMPTY', '_EVAL_CASE', '_EVAL_CASE_TRUE', '_EVAL_CASE_FALSE', '_EVAL_CASE_NOMATCH',
                          '_EVAL_APP', '_EVAL_CONS', '_EVAL_NIL', '_EVAL_CALL', '_EVAL_PRIMOP', '_EVAL_VAR', '_EVAL_FUNID', '_EVAL_LIT',
                          '_EVAL_FUN', '_EVAL_TUPLE', '_EVAL_LET', '_EVAL_SEQ', '_EVAL_MAP', '_EVAL_LETREC', '_EVAL_VALUES', '_EVAL_SINGLE'].

%% All semantics rules
semantic_rules() -> coq_list_rules() ++ case_rules() ++ case_helper_rules() ++ apply_rules() ++ list_rules() ++ call_rules() ++
                    primop_rules() ++ try_rules() ++ variable_rule() ++ funid_rule() ++ literal_rule() ++ fun_rule() ++ error_rules() ++
                    tuple_rules() ++ let_rules() ++ seq_rules() ++ map_rules() ++ letrec_rule() ++ exp_list_rules() ++ single_rule().

%% ---------------------------------------------------------------------


write_to_file(Filename, Content) ->
    case file:open(Filename, [write]) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.

generator_remove_junk(Input) ->
    hd(string:split(Input, "----------", trailing)).

generate_and_save_random_test(Id, ReportDirectory) ->
    random:seed(erlang:now()),
    ModuleName = io_lib:format("module~p", [Id]),
    Basename = ModuleName ++ ".erl",
    Filename = ReportDirectory ++ Basename,
    % TODO: egg_tester:y() should return with a string instead of printing it
    %       write_to_file(Filename, io_lib:format('-module(module~p).~n-export([main/0]).~n~p', [Id, egg_tester:y()])),
    case
        exec:shell_exec(
            io_lib:format("erl -pa eqc-2.01.0/ebin -pa generator/ebin -noshell -eval \"random:seed(erlang:now()), io:format('~~p', [erl_2020_gen:sample(module~p, ~p)])\" -eval 'init:stop()'",
                          [Id, 10])
        )
    of
        {0, Output} ->
            write_to_file(
                Filename,
                generator_remove_junk(Output)
            );
        {_, Output} ->
            io:format("Cannot generate code ~p~n", [Output])
    end,
    %NOTE: this is kinda dirty, but some generated erlang code either won't compile or
    %      crashes durring execution due to ill formed code.
    case execute_erl:execute(Filename, ModuleName, ReportDirectory) of
       {error, _} -> generate_and_save_random_test(Id, ReportDirectory);
       _          -> Filename
    end.

count_if(Pred, Lists) ->
    length(lists:filter(Pred, Lists)).

count(Elem, Lists) ->
    count_if(fun(X) -> Elem == X end, Lists).

run_multiple_test(Tests) when is_list(Tests) ->
    ReportDirectory = mktmpdir(),
    lists:map(fun(Test) -> execute_and_compare_result(Test, ReportDirectory) end, Tests).

generate_and_multiple_test(NumberOfTests) when is_number(NumberOfTests) ->
    ReportDirectory = mktmpdir(),
    lists:map(
        fun(Id) ->
            Test = generate_and_save_random_test(Id, ReportDirectory),
            Result = execute_and_compare_result(Test, ReportDirectory),
            Result
        end,
        lists:seq(1, NumberOfTests)
    ).

%% ---------------------------------------------------------------------
%% Proper integration to QC

save_test(String, Id, ReportDirectory) ->
    ModuleName = io_lib:format("module~p", [Id]),
    Basename = ModuleName ++ ".erl",
    Filename = ReportDirectory ++ Basename,
    write_to_file(Filename, String),
    Filename.

is_compilable(T) ->
    S = [erl_syntax:revert(T2) || T2 <- erl_syntax:form_list_elements(eval(T))],
    C = compile:forms(S, [strong_validation, return_errors, nowarn_unused_vars]),
    element(1, C) /= ok andalso io:format("\nnem fordul:(\n"),
    element(1, C) == ok.

generate_and_test_qc() ->
    ReportDirectory = mktmpdir(),
    ModuleName = "module1", %TODO
    G = resize(20, erlgen:module(ModuleName, 20)),
    G2 = ?LET(M, G, case lists:keysearch(value, 1, M) of
                        {value, {_, Value}} -> Value;
                        false -> []
                    end),
    G3 = ?SUCHTHAT(T, G2, is_compilable(T)),
    P = ?FORALL(T, G3, ?WHENFAIL(io:format("~n~s~n", [erl_prettypr:format(eqc_symbolic:eval(T))]),
        begin
            ProgramText = erl_prettypr:format(eqc_symbolic:eval(T)),
            FilePath = ReportDirectory ++ ModuleName ++ ".erl",
            write_to_file(FilePath, ProgramText),
            execute_and_compare_result(FilePath, ReportDirectory)
        end)),
    [eqc:quickcheck(eqc:numtests(1, P))].

%% ---------------------------------------------------------------------

parser_main_arguments([]) ->
    help;
parser_main_arguments(Args) when is_list(Args) ->
    case hd(Args) of
        "random" -> {runRandomTests, list_to_integer(lists:nth(2, Args))};
        "randomqc" -> runRandomTestQC;
        _ -> {runTests, Args}
    end;
parser_main_arguments(_) ->
    help.

report_result(help) ->
    io:format("wrong number of arguments~n");
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
    UsedRulesNr = maps:size(maps:filter(fun(K, V) -> V > 0 end, CoqCoverage)),
    io:format("~n~nCoq coverage data:~n"),
    io:format("Rule coverage: ~p %~n", [(UsedRulesNr / length(semantic_rules())) * 100]),
  
  %% used exception-free rule percent
    ExcFreeRules = exceptionfree_rules(),
    UsedExceptionFreeRulesNr = maps:size(maps:filter(fun(K, V) -> lists:member(K, ExcFreeRules) and (V > 0) end, CoqCoverage)),
    io:format("Rule coverage without exceptions: ~p %~n", [(UsedExceptionFreeRulesNr / length(ExcFreeRules)) * 100]),
   
  %% How many times were specific rules used
    io:format("~nRules used:~n~n"),
    pp_map(CoqCoverage)
%% ---------------------------------------------------------------------
    .

%% Map pretty-printer
pp_map(Map) when is_map(Map) ->
  %% workaround, we need foreach
  maps:fold(fun(K, V, Acc) -> io:format("~p rule was used ~p times~n", [K, V]), Acc end, 0, Map).

main(Args) ->
  %% Initialize with the Coq coverage map, where all rules were used 0 times:
    put(coq_coverage_map, default_map()),
    
    case parser_main_arguments(Args) of
        {runRandomTests, NoT} -> Results = generate_and_multiple_test(NoT);
        runRandomTestQC -> Results = generate_and_test_qc();
        {runTests, Tests} -> Results = run_multiple_test(Tests);
        help -> Results = help;
        true -> Results = help
    end,
    report_result(Results).
