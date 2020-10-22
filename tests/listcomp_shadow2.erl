-module(listcomp_shadow2).
-export([main/0]).

f(X) -> X + 1.

main() ->
  begin
    X = 1,
    Y = 2,
    [{X,Y} || X <- [X, f(X), X+Y], X > 1, Y <- [X, f(X)]] == [{2,2}, {2,3}, {3,3}, {3,4}]
  end.
