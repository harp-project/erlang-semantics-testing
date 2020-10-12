-module(andalso3).
-export([main/0]).

main() -> (1 == 1 andalso 3 > 4) == false.
