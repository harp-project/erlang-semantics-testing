-module(app_ex).
-export([main/0]).

main() -> [1 | 2] ++ 4.
