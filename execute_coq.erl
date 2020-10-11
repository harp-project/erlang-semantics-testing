-module(execute_coq).

-export([execute/2]).

remove_parenthesis(String) ->
    [X || X <- String, X =/= $(, X =/= $)].

% possible results
% - ..., -1, 0, 1, 2, ...
% - ..., (-10), (-9), ...
% - "true", "false"
%
parse_int_or_bool(String) when is_list(String) ->
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
parse_int_or_bool(String) when true ->
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

-define(COQDIR, "Core-Erlang-Formalization/src").

compile_coq(Test) ->
    %coqc -Q $COQDIR "" "tmp$num.v"
    case
        exec:shell_exec(
            io_lib:format("coqc -Q \"~p\" \"\" \"~p\"", [
                ?COQDIR,
                Test ++ ".v"
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
    Lines = string:split(Output, "\n", all),
    ResultLines = lists:filter(
        fun(Line) ->
            case string:find(Line, "Some") of
                nomatch -> false;
                _ -> true
            end
        end,
        Lines
    ),
    %io:format("result code = ~p ~n result string: ~p ~n~n", [ResultCode, ResultLines]),
    case length(ResultLines) of
        1 ->
            case string:split(hd(ResultLines), " ", trailing) of
                [_ | Tail] ->
                    {ok, parse_int_or_bool(hd(Tail))};
                _ ->
                    io:format("Cannot parse: ~p~n", [ResultLines]),
                    {error, "Cannot parse"}
            end;
        _ ->
            io:format("Cannot parse: ~p~n", [Output]),
            {error, "Cannot parse"}
    end.

write_to_file(Filename, Content) ->
    case file:open(Filename, [write]) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.

convert_erl_to_coq(H) ->
    write_to_file(H ++ ".v", cst_to_ast:from_erl(H, true)).

execute(Test, _) ->
    convert_erl_to_coq(Test),
    Output = compile_coq(Test),
    parse_coq_result(Output).
