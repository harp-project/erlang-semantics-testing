-module(case_guard9).
-export([main/0]).

main() ->
  case 3 of
    3 when true -> ok;
    3 when false -> nok 
  end == ok.

