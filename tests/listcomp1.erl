-module(listcomp1).
-export([main/0]).

main() -> [X+1 || X <- [1,2,3]] == [2,3,4].
