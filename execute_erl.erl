-module(execute_erl).

-export([execute/3]).

remove_parenthesis(String) ->
    [X || X <- String, X =/= $(, X =/= $)].

% possible results
% - ..., -1, 0, 1, 2, ...
% - ..., (-10), (-9), ...
% - "true", "false"
% TODO: make this comment a test
parse(String) when is_list(String) ->
    Clean = string:lowercase(remove_parenthesis(string:trim(String))),
    case Clean of
        "\"true\"" -> true;
        "true" -> true;
        "True" -> true;
        "False" -> false;
        "false" -> false;
        "\"false\"" -> false;
        IntStr -> erlang:list_to_integer(IntStr)
    end;
parse(String) when true ->
    Clean = string:lowercase(remove_parenthesis(string:trim(String))),
    case Clean of
        "\"true\"" -> true;
        "true" -> true;
        "True" -> true;
        "False" -> false;
        "false" -> false;
        "\"false\"" -> false;
        IntStr -> erlang:list_to_integer(IntStr)
    end.

compile(Path, ReportDirectory) ->
    exec:shell_exec(io_lib:format("erlc -o ~s -W0 \"~p\"", [ReportDirectory, Path])).

run(Module, ReportDirectory) ->
    exec:shell_exec(
        io_lib:format("erl -pa ~s -noshell -eval \"io:format('~~p', [~p:main()])\" -eval 'init:stop()'", [
            ReportDirectory,
            Module
        ])
    ).

execute(Test, ModuleName, ReportDirectory) ->
    % compile(Test++".erl") >>= run(ModuleName) >>= parse
    case compile(Test ++ ".erl", ReportDirectory) of
        {0, _} ->
            case run(ModuleName, ReportDirectory) of
                {0, Output} ->
                    {ok, parse(Output)};
                {RetVal, Output} ->
                    {error,
                        io_lib:format(
                            "execute_erlang: failed to run command module=~p ret=~p output=~p~n",
                            [ModuleName, RetVal, Output]
                        )}
            end;
        _ ->
            {error, io:format("execute_erlang: failed to compile module ~p~n", [ModuleName])}
    end.
