-module(apply_ex).
-export([main/0]).

main() -> (3 rem 0)(3 rem 1).

foo(X) -> X.
