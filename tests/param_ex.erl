-module(param_ex).
-export([main/0]).

main() -> foo(3 rem 0).

foo(X) -> X.
