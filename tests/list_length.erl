-module(list_length).
-export([main/0]).

main() ->
  length([]) == 0 andalso
  length([foo]) == 1 andalso
  length([1,1+1,3,4,5]) == 5.
