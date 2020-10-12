-module(if1).
-export([main/0]).

f() -> ok.

main() ->
 if 1 == 1 ->
   true
 end.
