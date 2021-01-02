-module(module11).

-export([main/0]).

% Precedences collide somehow (resulting in an exception). It works with parentheses.
main() -> B = 1 * 1 == length(A) + 1,
          {}.
