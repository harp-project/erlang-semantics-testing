-module(listcomp_shadow1).
-export([main/0]).

main() ->
  begin
    X = 1,
    [X || X > 1, X <- [1,2,3]] == []
  end.
