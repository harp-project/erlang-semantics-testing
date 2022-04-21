-module(execute_erl).

-export([execute/1, execute_new_shell/2, setup/0, report/0, compile/2, spawn_function/2]).

-define(GENERATOR, "generator/ebin/gen_erlang.beam").
-define(ERL_FILENAME, "./reports/erl_coverage.csv").

% TODO: deprecated, remove this:
%compile(Path, ReportDirectory) ->
%    exec:shell_exec(io_lib:format("erlc -o ~s -W0 \"~s\"", [ReportDirectory, Path])).

compile(FilePaths, ReportDirectory) ->
  lists:foreach(fun(Path) -> compile:file(Path, [{outdir, ReportDirectory}]) end, FilePaths).

run(Module, ReportDirectory) ->
    exec:shell_exec(
        io_lib:format("erl -pa ~s -noshell -eval \"io:format('~~p', [~s:main()])\" -eval 'init:stop()'", [
            ReportDirectory,
            Module
        ])
    ).


%% ---------------------------------------------------------------------------
% Workaround to avoid EQC to shut down testing:
spawn_function(Main, Mod) ->
  Main ! {ok, Mod:main()}.

evaluate_module(Mod) ->
    process_flag(trap_exit, true),
    Pid = spawn_link(execute_erl, spawn_function, [self(), Mod]),
    receive
      {ok, RetVal} -> {Mod, RetVal};
      {'EXIT', _, Reason} when Reason /= normal -> {Mod, element(1,Reason)}; % normal termination signal somehow is faster than the message sometimes
      Else -> io:format("~n~n~nWrong result format: ~p~n~n~n", [Else])
    end.

execute(FilePaths) ->
    process_flag(trap_exit, true),
    Mods = [code:load_abs(misc:remove_extension(F)) || F <- FilePaths],
    [evaluate_module(Mod) || {_, Mod} <- Mods].

%% ---------------------------------------------------------------------------

execute_new_shell(FilePaths, ReportDirectory) ->
  [begin
     ModName = misc:remove_extension(misc:remove_directory(F)),
     {list_to_atom(ModName), evaluate_module_new_shell(ModName, ReportDirectory)}
   end || F <- FilePaths].

evaluate_module_new_shell(ModuleName, ReportDirectory) ->
    case run(ModuleName, ReportDirectory) of
        %% -----------------------------------------
        %% Erlang execution succeeded
        {0, Output} ->
            misc:parse(Output);
        %% -----------------------------------------
        %% Erlang execution failed
        {RetVal, Output} ->
            try
              %% select the exception reason from the output string
              ToParse = lists:takewhile(fun(X) -> X /= $, end, tl(lists:dropwhile(fun(X) -> X /= ${ end, tl(Output)))),
            % If there are details beside the reason  
            if hd(ToParse) == ${ -> list_to_atom(tl(ToParse));
            % If there are no details beside the reason
               true              -> list_to_atom(ToParse)
              end
            catch
              _ -> {error,
                      io_lib:format(
                          "execute_erlang: failed to run command module=~p ret=~p output=~p~n",
                          [ModuleName, RetVal, Output]
                      )}
            end
        %% -----------------------------------------
    end.

%% ---------------------------------------------------------------------------
%% Erlang Generator Coverage Measurement

setup() ->
    case cover:compile_beam(?GENERATOR) of
      {ok, _} -> ok;
      _ -> io:format("Warning: Erlang tracing setup failed!")
    end.

generators() ->
    [function, funclause, pattern, statement, match_expr, application, io_statement, boolean_literal, 
     integer_literal, atom_literal, list_expr, list_comp, generator, tuple_expr, atom_expr, boolean_expr, integer_expr, 
     unbound_var, case_expr, case_clause]. % last_funclause, last_caseclause

report() ->
    misc:hline(),
    io:format("Erlang generator coverage data~n"),
    case cover:analyse(gen_erlang, calls, function) of
        {ok, Stats} -> 
                    begin  
                        CovMap = lists:foldr(
                                    fun({{_, FunName, _}, Nr}, Acc) -> 
                                        case maps:is_key(FunName, Acc) of
                                            true -> maps:update_with(FunName, fun(X) -> X + Nr end, Acc);
                                            _ -> Acc
                                        end
                                    end, misc:init_stat_map(generators()), Stats),
                        UsedRulesNr = maps:size(maps:filter(fun(_, V) -> V > 0 end, CovMap)),
                        io:format("Used generators: ~p %~n~n", [UsedRulesNr / length(generators()) * 100]),
                        % io:format("~n~nErlang coverage data raw: ~p~n~n", [Stats]),
                        % io:format("~n~nErlang coverage data: ~p~n~n", [CovMap])
                        misc:report_coverage_to_csv(CovMap, ?ERL_FILENAME)
                    end;
        P           -> io:format("Corrupt generator coverage data!~p~n~n", [P])
    end,
    misc:hline()
.

%% ---------------------------------------------------------------------
