-module(if2).
-export([main/0]).

f() -> ok.

main() ->
  if 1 == 2; 1 == 1 ->
    true
  end.
