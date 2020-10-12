-module(begin_end).
-export([main/0]).

f(A,B) -> A + B.

main() ->
  begin
    X = 3,
    Y = 2,
    f(X,Y)
  end == 5.

