-module(exec).

-export([shell_exec/1]).

shell_exec(Command) ->
    Port = open_port({spawn, Command}, [stream, in, stderr_to_stdout, eof, hide, exit_status]),
    get_data(Port, []).

get_data(Port, Sofar) ->
    receive
        {Port, {data, Bytes}} ->
            get_data(Port, [Sofar | Bytes]);
        {Port, eof} ->
            Port ! {self(), close},
            receive
                {Port, closed} ->
                    true
            end,
            receive
                {'EXIT', Port, _} ->
                    ok
            % force context switch
            after 1 -> ok
            end,
            ExitCode =
                receive
                    {Port, {exit_status, Code}} ->
                        Code
                end,
            {ExitCode, lists:flatten(Sofar)}
    end.
