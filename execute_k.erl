-module(execute_k).

-export([execute/3]).

%TODO: The K related code is missing! For now do exactly what _erlang does.
execute(Test, ModuleName, ReportDirectory) ->
    execute_erl:execute(Test, ModuleName, ReportDirectory).
