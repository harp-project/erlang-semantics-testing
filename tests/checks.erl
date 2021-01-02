-module(checks).
-export([main/0]).

main() -> is_atom('foo') and is_integer(5) and is_boolean(true) and is_number(2).
