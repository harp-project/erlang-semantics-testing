-module(implicit_fun1).
-export([main/0]).

f(X) -> X + 1.

main() -> fun f/1 (1) == 2.
