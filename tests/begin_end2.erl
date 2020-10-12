-module(begin_end2).
-export([main/0]).

f(A,B) -> A + B.

main() ->
  begin
    foo,
    {X,Y} = {5,6},
    true
  end.

