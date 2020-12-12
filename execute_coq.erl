-module(execute_coq).

-export([execute/3, setup/0, report/0, update_coverage/1]).

-define(COQ_FILENAME, "./reports/coq_coverage.csv").

% map_result_to_erlang(String) ->
    % Remove = [X || X <- String, X =/= $\n, X =/= $", X =/= $`, X =/= $@],
    % L = lists:flatten(string:replace(
          % lists:flatten(string:replace(
                        % lists:flatten(string:replace(Remove, "==>", "=>", all)),
                        % "' ", "'", all)),
                      % " '", "'", all)),
    % L.

parse(Expression) ->
    {ok, Tokens, _} = erl_scan:string(Expression++"."),
    {ok, Parsed} = erl_parse:parse_exprs(Tokens),
    {value, Result, _} = erl_eval:exprs(Parsed, []),
    Result.

-define(COQDIR, "Core-Erlang-Formalization/src").

compile_coq(BaseName, ReportDirectory) ->
    %coqc -Q $COQDIR "" "tmp$num.v"
    case
        exec:shell_exec(
            io_lib:format("coqc -Q \"~s\" \"\" \"~s\"", [
                ?COQDIR,
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

parse_coq_result(Output) when is_integer(Output) ->
    io:format("coq result should be string~n"),
    {error, "Expected string"};
parse_coq_result(Output) ->
    case string:split(Output, "__coqresult:", leading) of
        [_ | [Tail]] ->
          %% -----------------------------------------
          %% Coq result is a correct value
            ToParse = lists:reverse(tl(lists:dropwhile(fun(X) -> X /= $" end, lists:reverse(Tail)))),
            {ok, parse(ToParse)};
          %% -----------------------------------------
        _ ->
          %% -----------------------------------------
          %% Coq result is either an exception, or some error happened
            case string:split(Output, "__exceptioncoqresult:", leading) of
               %% Get the reason of the exception, which will be compared to the Erlang exception reason
                 [_ | [Tail]] ->
                      ToParse = lists:reverse(tl(lists:dropwhile(fun(X) -> X /= $" end, lists:reverse(Tail)))),
                      {{_, Reason, _}, Trace} = parse(ToParse),
                      {ok, {Reason, Trace}};
                 _ -> %% Something else was the result
                    io:format("Cannot parse: ~p~n", [Output]),
                    {error, "Cannot parse"}
            end
          %% -----------------------------------------
    end
    .

convert_erl_to_coq(TestPath, BaseName, ReportDirectory) ->
    misc:write_to_file(ReportDirectory ++ BaseName ++ ".v", cst_to_ast:from_erl(TestPath, true)).

execute(TestPath, BaseName, ReportDirectory) ->
    convert_erl_to_coq(TestPath, BaseName, ReportDirectory),
    Output = compile_coq(BaseName, ReportDirectory),
    parse_coq_result(Output).


%% ---------------------------------------------------------------------
%% Coq Coverage measurement

setup() ->
  %% Initialize with the Coq coverage map, where all rules were used 0 times:
    put(coq_coverage_map, default_map()).

%% CAUTION: Uses the fact, that the Coq result is the second one in the list
%% returns #{...}
update_coverage(Result) ->
  case Result of
    %% [Erlresult, {Ok, {Coqresult, CoqTrace}} | Rest]
    [_, {_, {_, CoqTrace}} | _] -> process_trace(CoqTrace);
    _                           -> #{}
  end.

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

report() ->
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
    true  -> misc:write_to_file(?COQ_FILENAME, StatLine, append);
    
    %% header needed
    false ->
      begin
        HeaderLine = maps:fold(fun(K, _, Acc) -> atom_to_list(K) ++ ";" ++ Acc end, "\n", CoqCoverage),
        misc:write_to_file(?COQ_FILENAME, HeaderLine ++ StatLine, append)
      end
  end.

%% Map pretty-printer
pp_map(Map) when is_map(Map) ->
  %% workaround, we need foreach
  maps:fold(fun(K, V, Acc) -> io:format("~p rule was used ~p times~n", [K, V]), Acc end, 0, Map).
