-module(list_pattern_match2).
-export([main/0]).

main() ->
  case [1,2,3,4] of
    [X, Y | Z] -> X + Y
  end == 3.
