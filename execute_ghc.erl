-module(execute_ghc).

-export([execute/5, setup/0, report/0, update_coverage/1]).

compile_and_run_ghc(BaseName, ReportDirectory, true) ->
    case exec:shell_exec( "ghc -dynamic -i BigStepSemanticsTraced.hs " ++ ReportDirectory ++ BaseName ++ ".hs" ) of
    {0, _} -> {0, Output} = exec:shell_exec( "./" ++ ReportDirectory ++ BaseName ), Output;
    {_, _} -> "failed"
    end;
compile_and_run_ghc(BaseName, ReportDirectory, _Tracing) ->
    case exec:shell_exec( "ghc -dynamic -i BigStepSemantics.hs " ++ ReportDirectory ++ BaseName ++ ".hs" ) of
    {0, _} -> {0, Output} = exec:shell_exec( "./" ++ ReportDirectory ++ BaseName ), Output;
    {_, _} -> "failed"
    end.


convert_erl_to_coq(TestPath, BaseName, ReportDirectory, true) ->
    misc:write_to_file(ReportDirectory ++ BaseName ++ ".hs", cst_to_ast:from_erl(TestPath, functionalSemanticHaskellTraced));
convert_erl_to_coq(TestPath, BaseName, ReportDirectory, _Tracing) ->
    misc:write_to_file(ReportDirectory ++ BaseName ++ ".hs", cst_to_ast:from_erl(TestPath, functionalSemanticHaskell)).

% wrapper
execute(TestPath, BaseName, ReportDirectory, Tracing, PID) ->
  Res = execute(TestPath, BaseName, ReportDirectory, Tracing),  
  % io:format("GHC is ready!: ~p~n", [Res]),
  PID ! {Res, coq_res}.

execute(TestPath, BaseName, ReportDirectory, Tracing) ->
    convert_erl_to_coq(TestPath, BaseName, ReportDirectory, Tracing),
    Output = compile_and_run_ghc(BaseName, ReportDirectory, Tracing),
    execute_coq:parse_coq_result(Output, Tracing).


%% ---------------------------------------------------------------------
%% Coq Coverage measurement

setup() ->
  execute_coq:setup().

update_coverage(Result) ->
  execute_coq:update_coverage(Result).


report() ->
  execute_coq:report().

