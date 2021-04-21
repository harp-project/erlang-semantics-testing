-module(execute_coq).

-export([execute/5, setup/0, report/0, update_coverage/1, parse_coq_result/2]).

-define(COQ_FILENAME, "./reports/coq_coverage.csv").
-define(COQ_BIF_FILENAME, "./reports/coq_bif_coverage.csv").
-define(COQDIR, "Core-Erlang-Formalization/src").
-define(COQRELPATH, "Core_Erlang").
-define(COQ_RULE_LOC, coq_rule_coverage_map).
-define(COQ_BIF_LOC, coq_bif_coverage_map).

compile_coq(BaseName, ReportDirectory) ->
    %coqc -Q $COQDIR "" "tmp$num.v"
    case
        exec:shell_exec(
            io_lib:format("coqc -Q \"~s\" \"~s\" \"~s\"", [
                ?COQDIR,
                ?COQRELPATH,
                ReportDirectory ++ BaseName ++ ".v"
            ])
        )
    of
        {_, Output} ->
            Output;
        _ ->
            io:format("Error running coqc~n"),
            -1
    end.

% parse_coq_result(Output, Tracing) when is_integer(Output) ->
%    io:format("coq result should be string~n"),
%    {error, "Expected string"};
parse_coq_result(Output, Tracing) ->
  case string:split(Output, "__coqresult:", leading) of
        [_ | [Tail]] ->
          %% -----------------------------------------
          %% Coq result is a correct value
            ToParse = lists:takewhile(fun(X) -> X /= $" end, Tail),
            if Tracing -> [Result, Trace, BIFTrace] = string:split(ToParse, "%", all),
                          {ok, misc:parse(Result), misc:parse(Trace), misc:parse(BIFTrace)};
               true    -> {ok, misc:parse(ToParse)}
            end;
          %% -----------------------------------------
        _ ->
          %% -----------------------------------------
          %% Coq result is either an exception, or some error happened
            case string:split(Output, "__exceptioncoqresult:", leading) of
               %% Get the reason of the exception, which will be compared to the Erlang exception reason
                 [_ | [Tail]] ->
                      ToParse = lists:takewhile(fun(X) -> X /= $" end, Tail),
                      Result = 
                        if Tracing -> [Exception, T, BIFT] = string:split(ToParse, "%", all),
                                      {ok, misc:parse(Exception), misc:parse(T), misc:parse(BIFT)};
                           true    -> {ok, misc:parse(ToParse)}
                        end,
                      case Result of
                        % If there are details beside the reason
                         {_, {_, Reason, _}, RuleTrace, BIFTrace} -> {ok, Reason, RuleTrace, BIFTrace};
                         {_, {_, Reason, _}}                      -> {ok, Reason}
                        % If there are no details
                        % {{_, Reason, _}, RuleTrace, BIFTrace}      -> {ok, Reason, RuleTrace, BIFTrace};
                        % {_, {_, Reason, _}                             -> {ok, Reason}
                      end;
                 _ -> %% Something else was the result
                    io:format("Cannot parse: ~p~n", [Output]),
                    {error, "Cannot parse"}
            end
          %% -----------------------------------------
    end
    .

convert_erl_to_coq(TestPath, BaseName, ReportDirectory, Tracing) ->
    misc:write_to_file(ReportDirectory ++ BaseName ++ ".v", cst_to_ast:from_erl(TestPath, Tracing)).

% wrapper
execute(TestPath, BaseName, ReportDirectory, Tracing, PID) ->
  Res = execute(TestPath, BaseName, ReportDirectory, Tracing),
  % io:format("Coq is ready!: ~p~n", [element(2, Res)]),
  PID ! {Res, coq_res}.

execute(TestPath, BaseName, ReportDirectory, Tracing) ->
    convert_erl_to_coq(TestPath, BaseName, ReportDirectory, Tracing),
    Output = compile_coq(BaseName, ReportDirectory),
    parse_coq_result(Output, Tracing).


%% ---------------------------------------------------------------------
%% Coq Coverage measurement

setup() ->
  %% Initialize with the Coq coverage map, where all rules were used 0 times:
    put(?COQ_RULE_LOC, misc:init_stat_map(semantic_rules())),
    put(?COQ_BIF_LOC, misc:init_stat_map(bifs())).

update_coverage(Result) ->
  case Result of
    %% [Erlresult, {Ok, {Coqresult, CoqTrace}} | Rest]
    {_, _, RuleTrace, BIFTrace} -> misc:process_trace(RuleTrace, ?COQ_RULE_LOC), 
                                   misc:process_trace(BIFTrace, ?COQ_BIF_LOC);
    _                             -> #{}
  end.

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
% error_rules() ->  ['_FAIL', '_TIMEOUT'].

%% Semantics rules not including exceptional evaluation
exceptionfree_rules() -> ['_LIST_CONS', '_LIST_EMPTY', '_CASE', '_CASE_TRUE', '_CASE_FALSE', '_CASE_NOMATCH',
                          '_APP', '_CONS', '_NIL', '_CALL', '_PRIMOP', '_VAR', '_FUNID', '_LIT',
                          '_FUN', '_TUPLE', '_LET', '_SEQ', '_MAP', '_LETREC', '_VALUES'].

%% All semantics rules
semantic_rules() -> coq_list_rules() ++ case_rules() ++ case_helper_rules() ++ apply_rules() ++ list_rules() ++ call_rules() ++
                    primop_rules() ++ try_rules() ++ variable_rule() ++ funid_rule() ++ literal_rule() ++ fun_rule() ++ % error_rules() ++
                    tuple_rules() ++ let_rules() ++ seq_rules() ++ map_rules() ++ letrec_rule() ++ exp_list_rules() ++ single_rule().

%% All modeled BIFs
bifs() -> ['+','-','*','rem','div', 'and','or','not', 'abs', 'bsl', 'bsr',
           '==','/=','++','--','tuple_to_list','list_to_tuple'
           ,'<','=<','>','>=','length','tuple_size','tl','hd','element','setelement',
           'is_atom', 'is_integer', 'is_boolean', 'is_number'%, fwrite','fread','undef', '=:=', '=/=', '/',
           ].

report() ->
  %% Rule coverage map:
    RuleCoverage = get(?COQ_RULE_LOC),
  
  %% used rule percent
    UsedRulesNr = maps:size(maps:filter(fun(_, V) -> V > 0 end, RuleCoverage)),
    Semantics_rules = semantic_rules(),
    misc:hline(),
    io:format("Coq coverage data:~n"),
    io:format("Rule coverage: ~p %~n", [(UsedRulesNr / length(Semantics_rules)) * 100]),
  
  %% used exception-free rule percent
    ExcFreeRules = exceptionfree_rules(),
    UsedExceptionFreeRulesNr = maps:size(maps:filter(fun(K, V) -> lists:member(K, ExcFreeRules) and (V > 0) end, RuleCoverage)),
    io:format("Rule coverage without exceptions: ~p %~n", [(UsedExceptionFreeRulesNr / length(ExcFreeRules)) * 100]),
   
  % %% How many times were specific rules used
  %   io:format("~nRules used:~n~n"),
  %   pp_map(RuleCoverage),
  
  %% Report results to coq_coverage.cs
    misc:report_coverage_to_csv(RuleCoverage, ?COQ_FILENAME),
  
  %% BIF coverage:
    BIFCoverage = get(?COQ_BIF_LOC),
    UsedBIFNr = maps:size(maps:filter(fun(_, V) -> V > 0 end, BIFCoverage)),
    io:format("BIF coverage: ~p %~n", [(UsedBIFNr / length(bifs())) * 100]),
  
  %% Report results to coq_bif_coverage.csv
    misc:report_coverage_to_csv(BIFCoverage, ?COQ_BIF_FILENAME),
    misc:hline()
 .

%% Map pretty-printer
% pp_map(Map) when is_map(Map) ->
%   %% workaround, we need foreach
%   maps:fold(fun(K, V, Acc) -> io:format("~p rule was used ~p times~n", [K, V]), Acc end, 0, Map).
