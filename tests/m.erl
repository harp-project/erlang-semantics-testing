main() ->
  case [5, 6, 7, 8 | 9] of
    5 when 'true' -> 3;
	_ -> 2
  end.

f() -> [{X, Y} || X <- list:seq(1,10), Y <- lists:seq(1,5), Y > 3, X < 4].