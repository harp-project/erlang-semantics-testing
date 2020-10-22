-module(list_comparison3).
-export([main/0]).

main() -> [] =< [] andalso
          [foo, bar] > [bar, foo] andalso
          [foo, bar] >= [bar, foo].
