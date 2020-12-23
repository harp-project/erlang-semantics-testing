-module(module26).

-export([main/0]).

main() ->
    A = tuple_to_list({[]}),
    length(tuple_to_list(list_to_tuple(A))).