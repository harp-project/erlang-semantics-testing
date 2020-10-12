-module(list_pattern_match).
-export([main/0]).

main() ->
  case [1,2,3] of
    [X | [Y,Z]] -> X + Y + Z
  end +
  case [1,2,3] of
    [X,Y | [Z]] -> X + Y + Z
  end == 12.
