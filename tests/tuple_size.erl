-module(tuple_size).
-export([main/0]).

main() ->
  tuple_size({}) == 0 andalso
  tuple_size({{1,2}, foo, bar, 4}) == 4.
