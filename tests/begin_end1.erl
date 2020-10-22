-module(begin_end1).
-export([main/0]).

f(A,B) -> A + B.

main() ->
  begin
    foo,
    bar,
    true
  end.

