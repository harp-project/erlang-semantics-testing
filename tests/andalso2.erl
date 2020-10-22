-module(andalso2).
-export([main/0]).

main() -> (1 == 2 andalso 3 > 2) == false.
