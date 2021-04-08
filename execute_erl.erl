-module(execute_erl).

-export([execute/5, setup/0, report/0]).

-define(GENERATOR, "generator/ebin/erlgen.beam").
-define(ERL_FILENAME, "./reports/erl_coverage.csv").

compile(Path, ReportDirectory) ->
    exec:shell_exec(io_lib:format("erlc -o ~s -W0 \"~s\"", [ReportDirectory, Path])).

run(Module, ReportDirectory) ->
    exec:shell_exec(
        io_lib:format("erl -pa ~s -noshell -eval \"io:format('~~p', [~s:main()])\" -eval 'init:stop()'", [
            ReportDirectory,
            Module
        ])
    ).

% wrapper
execute(Test, ModuleName, ReportDirectory, Tracing, PID) ->
  Res = execute(Test, ModuleName, Tracing, ReportDirectory),
  io:format("Erlang is ready!: ~p~n", [Res]),  
  PID ! {Res, erl_res}.

execute(Test, ModuleName, _Tracing, ReportDirectory) ->
    % compile(Test++".erl") >>= run(ModuleName) >>= parse
    case compile(Test ++ ".erl", ReportDirectory) of
        {0, _} ->
            case run(ModuleName, ReportDirectory) of
                %% -----------------------------------------
                %% Erlang execution succeeded
                {0, Output} ->
                    {ok, misc:parse(Output)};
                %% -----------------------------------------
                %% Erlang execution failed
                {RetVal, Output} ->
                    try
                      %% select the exception reason from the output string
                      ToParse = lists:takewhile(fun(X) -> X /= $, end, tl(lists:dropwhile(fun(X) -> X /= ${ end, tl(Output)))),
                    % If there are details beside the reason  
                    if hd(ToParse) == ${ -> {ok, list_to_atom(tl(ToParse))};
                    % If there are no details beside the reason
                       true              -> {ok, list_to_atom(ToParse)}
                      end
                    catch
                      _ -> {error,
                              io_lib:format(
                                  "execute_erlang: failed to run command module=~p ret=~p output=~p~n",
                                  [ModuleName, RetVal, Output]
                              )}
                    end
                %% -----------------------------------------
            end;
        _ ->
            {error, io:format("execute_erlang: failed to compile module ~p~n", [ModuleName])}
    end.



%% ---------------------------------------------------------------------
%% Erlang Generator Coverage Measurement

setup() ->
    cover:compile_beam(?GENERATOR)
.

generators() ->
    [function, funclause, pattern, statement, match_expr, application, io_statement, boolean_literal, 
     integer_literal, atom_literal, list_expr, list_comp, generator, tuple_expr, atom_expr, boolean_expr, integer_expr, 
     unbound_var, case_expr, case_clause]. % last_funclause, last_caseclause

report() ->
    misc:hline(),
    io:format("Erlang generator coverage data~n"),
    case cover:analyse(erlgen, calls, function) of
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
        _           -> io:format("Corrupt generator coverage data!")
    end,
    misc:hline()
.

%% ---------------------------------------------------------------------
