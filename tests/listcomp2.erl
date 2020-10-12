-module(listcomp2).
-export([main/0]).

main() -> [X || {X,1} <- [{1,1},{2,1},{3,2},alma,{3,1},100]] == [1,2,3].
