-module(execute_ghc).

-export([execute/3, setup/0, report/0, update_coverages/1]).

compile_and_run_ghc(BaseName, ReportDirectory, true) ->
    case exec:shell_exec( "ghc -dynamic -i BigStepSemanticsTraced.hs " ++ ReportDirectory ++ BaseName ++ ".hs" ) of
      {0, _} -> {0, Output} = exec:shell_exec( "./" ++ ReportDirectory ++ BaseName ), Output;
      {_, Y} -> io:format("~n~n~p~n~n", [Y]), "failed"
    end;
compile_and_run_ghc(BaseName, ReportDirectory, _Tracing) ->
    case exec:shell_exec( "ghc -dynamic -i BigStepSemantics.hs " ++ ReportDirectory ++ BaseName ++ ".hs" ) of
      {0, _} -> {0, Output} = exec:shell_exec( "./" ++ ReportDirectory ++ BaseName ), Output;
      {_, Y} -> io:format("~n~n~s~n~n", [Y]), "failed"
    end.

execute(FilePaths, ReportDirectory, Tracing) ->
  ModuleNames = cst_to_ast:from_erl(FilePaths, ReportDirectory, Tracing, true), % true = GHC export is enabled
  [{ModName, execute_coq:parse_coq_result(compile_and_run_ghc(atom_to_list(ModName), ReportDirectory, Tracing), Tracing)} || ModName <- ModuleNames].

%% ---------------------------------------------------------------------
%% Coq Coverage measurement

setup() ->
  execute_coq:setup().

update_coverages(Results) ->
  execute_coq:update_coverages(Results).


report() ->
  execute_coq:report().

