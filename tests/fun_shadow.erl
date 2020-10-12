-module(fun_shadow).
-export([main/0]).

main() ->
  begin
    X = 4,
    fun(X) -> X + 1 end(5)
  end == 6.
