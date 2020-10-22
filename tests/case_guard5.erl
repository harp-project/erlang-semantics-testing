-module(case_guard5).
-export([main/0]).

main() ->
  case 3 of
    3 when 3 < 2; 1 > 2 -> nok;
    3 when 3 < 2; 4 == 5; 2 < 3 -> ok
  end == ok.

