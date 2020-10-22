-module(setelement).
-export([main/0]).

main() -> setelement(2,{1,1,1,1},10) == {1,10,1,1}.
