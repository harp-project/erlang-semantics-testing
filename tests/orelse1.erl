-module(orelse1).
-export([main/0]).

main() -> (false orelse true) orelse false.