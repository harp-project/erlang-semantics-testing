-module(badarity2).
-export([main/0]).

main() -> X = fun foo/1,
          X().

foo(X) -> X.