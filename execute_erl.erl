-module(execute_erl).

-export([execute/3]).

parse(Expression) ->
    {ok, Tokens, _} = erl_scan:string(Expression++"."),
    {ok, Parsed} = erl_parse:parse_exprs(Tokens),
    {value, Result, _} = erl_eval:exprs(Parsed, []),
    Result.

compile(Path, ReportDirectory) ->
    exec:shell_exec(io_lib:format("erlc -o ~s -W0 \"~s\"", [ReportDirectory, Path])).

run(Module, ReportDirectory) ->
    exec:shell_exec(
        io_lib:format("erl -pa ~s -noshell -eval \"io:format('~~p', [~s:main()])\" -eval 'init:stop()'", [
            ReportDirectory,
            Module
        ])
    ).

execute(Test, ModuleName, ReportDirectory) ->
    % compile(Test++".erl") >>= run(ModuleName) >>= parse
    case compile(Test ++ ".erl", ReportDirectory) of
        {0, _} ->
            case run(ModuleName, ReportDirectory) of
                %% -----------------------------------------
                %% Erlang execution succeeded
                {0, Output} ->
                    {ok, parse(Output)};
                %% -----------------------------------------
                %% Erlang execution failed
                {RetVal, Output} ->
                    try
                      %% select the exception reason from the output string
                      ToParse = lists:takewhile(fun(X) -> X /= $, end, tl(lists:dropwhile(fun(X) -> X /= ${ end, tl(Output)))),
                      {ok, list_to_atom(ToParse)}
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
