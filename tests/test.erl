-module(test).
-export([main/0]).

main() -> [foo, bar, {foo, foo}, #{1 => bar, 2 => baz}, [], {}, #{}].
