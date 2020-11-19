-module(test).
-compile([export_all]).

main() -> [foo, bar, {foo, foo}, #{1 => bar, 2 => baz}, [], {}, #{}].