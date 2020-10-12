-module(if4).
-export([main/0]).

talk(Animal) ->
  Talk =
    if
      Animal == cat  -> meow;
      Animal == beef -> mooo;
      Animal == dog  -> bark;
      Animal == tree -> bark;
      true -> fgdadfgna
    end.

main() -> talk(xy) == fgdadfgna.
