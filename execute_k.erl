-module(execute_k).

-export([execute/2]).

%TODO: The K related code is missing! For now do exactly what _erlang does.
execute(Test, ModuleName) ->
    execute_erl:execute(Test, ModuleName).
