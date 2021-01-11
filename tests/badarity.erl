-module(badarity).
-export([main/0]).

main() -> X = fun(Y) -> Y end,
          X().

