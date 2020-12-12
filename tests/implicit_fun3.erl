-module(implicit_fun3).
-export([main/0]).

f(X,Y,Z) -> X + Y + Z.

main() -> 
  begin
    F = fun f/3,
    A = 1 * 2 + 1,
    Fun = F,
    Fun(1,2,3)
  end == 6.
