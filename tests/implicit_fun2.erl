-module(implicit_fun2).
-export([main/0]).

f(X) -> X + 1.

main() ->
  begin
    F = fun f/1,
	A = 1 + 0,
	Fun = F,
	Fun(1)
  end == 2.
