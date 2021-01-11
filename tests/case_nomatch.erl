-module(case_nomatch).
-export([main/0]).

main() -> case 1 of
             2 -> ok;
             3 -> ok
          end.
