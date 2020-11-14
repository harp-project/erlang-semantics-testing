-module(execute_coq).

-export([execute/3]).

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
                    {ok, parse(hd(Tail))};
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

convert_erl_to_coq(TestPath, BaseName, ReportDirectory) ->
    write_to_file(ReportDirectory ++ BaseName ++ ".v", cst_to_ast:from_erl(TestPath, true)).

execute(TestPath, BaseName, ReportDirectory) ->
    convert_erl_to_coq(TestPath, BaseName, ReportDirectory),
    Output = compile_coq(BaseName, ReportDirectory),
    parse_coq_result(Output).
