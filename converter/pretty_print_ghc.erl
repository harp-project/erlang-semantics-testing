-module(pretty_print_ghc).
-export([pp/2, pp/1]).
-include_lib("compiler/src/core_parse.hrl").

  
%% Adding module functions to letrec

pp_expr(#c_values{es=Es}) -> "(EValues [" ++ pp_list(Es, ", ", fun pp/1) ++ "])";
pp_expr(E) -> pp(E).

pp(#c_module{defs=Ds}) ->
	pp_list(Ds,", ",fun ({_FunId,Body}) -> io_lib:format("(~s,~s)",[pp_letrec_sign(_FunId), pp(Body, ok)]) end);

%% Pretty Printing Expressions

pp(#c_primop{name=N, args=As}) ->
  io_lib:format("(EPrimOp ~s [~s])", [pp_var(N), pp_list(As,", ", fun pp_expr/1)]);

pp(#c_case{arg=A, clauses=Cs}) ->
  io_lib:format("(ECase ~s [~s])", [pp_expr(A), pp_list(Cs, ", ", fun pp/1)]);

pp(#c_clause{pats=Ps, guard=G, body=B}) ->
  io_lib:format("((([~s]), ~s), ~s)", [pp_list(Ps,", ", fun pp_pattern/1), pp_expr(G), pp_expr(B)]);

pp(#c_apply{op=O, args=As}) ->
  io_lib:format("(EApp ~s [~s])", [pp_expr(O), pp_list(As,", ", fun pp_expr/1)]);

pp(#c_literal{val=V}) when is_list(V) ->
  pp_cons(V);
pp(#c_literal{val=V}) when is_atom(V) ->
  "(ELit (Atom \"" ++ atom_to_list(V) ++ "\"))";
pp(#c_literal{val=V}) when is_integer(V) ->
  "(ELit (Integer (" ++ integer_to_list(V) ++ ")))";

pp(#c_literal{val=V}) when is_map(V) ->
  io_lib:format("(EMap [~s])", [pp_list(maps:to_list(V), ", ", fun pp_pair/1)]);
pp(#c_literal{val=T}) when is_tuple(T) ->
  io_lib:format("(ETuple [~s])", [pp_list(tuple_to_list(T),", ", fun pp_expr/1)]);
pp(#c_var{name=N}) when is_atom(N) ->
  "(EVar \"" ++ atom_to_list(N) ++ "\")";
pp(#c_var{name=N}) when is_integer(N) ->
  io_lib:format("(EVar \"_~s\")", [integer_to_list(N)]);
pp(#c_var{name={N, A}}) ->
  io_lib:format("(EFunId ((,) \"~s\" ~s))", [atom_to_list(N), integer_to_list(A)]);

pp(#c_fun{vars=Vs, body=B}) ->
  io_lib:format("(EFun [~s] ~s)", [pp_list(Vs,", ", fun pp_var/1), pp_expr(B)]);

%% If only one expression is bound (which is not in a value list)
pp(#c_let{vars=Ds, arg=A, body=B}) ->
  io_lib:format("(ELet [~s] ~s ~s)", [pp_list(Ds,", ", fun pp_var/1), pp_expr(A), pp_expr(B)]);

pp(#c_letrec{defs=Ds, body=B}) ->
  io_lib:format("(ELetRec [~s] ~s)", [pp_list(Ds, ", ", fun pp_letrec_defs/1), pp_expr(B)]);

pp(#c_cons{hd=Hd,tl=Tl}) ->
  pp_cons([Hd|Tl]);
  
%% Correct call formalization (for future syntax) %pp(#c_call{name=N, module=M args=Es}) ->
%  io_lib:format("(ECall ~s ~s [~s])", [pp_expr(M), pp_expr(N), pp_list(Es,";", fun pp_expr/1)]);
pp(#c_call{name=N,args=Es}) ->
	io_lib:format("(ECall ~s [~s])", [pp_var(N), pp_list(Es,", ", fun pp_expr/1)]);

pp(#c_tuple{es=Es}) ->
  io_lib:format("(ETuple [~s])", [pp_list(Es,", ", fun pp_expr/1)]);

pp(#c_map{arg=_, es=Es,is_pat=_}) ->
  io_lib:format("(EMap [~s])",[pp_list(Es,", ", fun pp/1)]);

pp(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}) ->
  io_lib:format("(~s, ~s)",[pp_expr(K),pp_expr(V)]);

pp(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}) ->
  io_lib:format("(~s, ~s)",[pp_expr(K),pp_expr(V)]);

pp(#c_seq{arg=A, body=B}) ->
  io_lib:format("(ESeq ~s ~s)",[pp_expr(A),pp_expr(B)]);

pp(#c_try{arg=A, vars=Vs, body=B, evars=Evs, handler=H}) ->
	io_lib:format("(ETry ~s [~s] ~s [~s] ~s)",[pp_expr(A), pp_list(Vs,", ", fun pp_var/1), pp_expr(B), pp_list(Evs,", ", fun pp_var/1), pp_expr(H)]);

pp(I) when is_integer(I) ->
  "(ELit (Integer (" ++ integer_to_list(I) ++ ")))";
pp(A) when is_atom(A) ->
  "(ELit (Atom \"" ++ atom_to_list(A) ++ "\"))";
pp(V) when is_list(V) ->
  pp_cons(V);
pp(V) when is_map(V) ->
  io_lib:format("(EMap [~s])", [pp_list(maps:to_list(V), ", ", fun pp_pair/1)]);
pp(T) when is_tuple(T) ->
  io_lib:format("(ETuple [~s])", [pp_list(tuple_to_list(T),", ", fun pp_expr/1)]);

pp(_X) ->
  io:format("\n\n\nunsupported case: ~p\n\n\n", [_X]),
  "".

%% Function printing without EFun and varlist

pp(#c_fun{vars=Vs, body=B}, _) ->
  io_lib:format("([~s], ~s)", [pp_list(Vs, ", ", fun pp_var/1), pp_expr(B)]);
pp(_, _) -> todo.

%% PP helpers for expressions

pp_var(#c_var{name=N}) when is_atom(N) ->
  "\"" ++ atom_to_list(N) ++ "\"";
pp_var(#c_var{name=N}) when is_integer(N) ->
  "\"_"++ integer_to_list(N) ++ "\"";
pp_var(#c_literal{val=V}) ->
  "\"" ++ atom_to_list(V) ++ "\"".

pp_list(Es, S, F) -> string:join(lists:map(F, Es), S).


pp_letrec_defs({A, B}) ->
  io_lib:format("(~s, ~s)", [pp_letrec_sign(A),pp_letrec_ve(B)]).
pp_letrec_sign(#c_var{name={N, A}}) ->
  io_lib:format("(\"~s\", ~s)", [atom_to_list(N), integer_to_list(A)]).
pp_letrec_ve(#c_fun{vars=Vs, body=B}) ->
  io_lib:format("([~s], ~s)", [pp_list(Vs, ", ", fun pp_var/1), pp_expr(B)]).

pp_cons([]) ->
  "ENil";
pp_cons([A|B]) ->
  io_lib:format("(ECons ~s ~s)", [pp_expr(A),pp_expr(B)]).

pp_pair({A, B}) -> io_lib:format("(~s,~s)", [pp_expr(A),pp_expr(B)]).



%% Pretty Printing Patterns

pp_pattern(#c_literal{val=V}) when is_integer(V) ->
  "(PLit (Integer (" ++ integer_to_list(V) ++ ")))";
pp_pattern(#c_literal{val=V}) when is_atom(V) ->
  "(PLit (Atom \"" ++ atom_to_list(V) ++ "\"))";
pp_pattern(#c_var{name=N}) when is_atom(N) ->
  "(PVar \"" ++ atom_to_list(N) ++ "\")";
pp_pattern(#c_var{name=N}) when is_integer(N) ->
  "(PVar \"_" ++ integer_to_list(N) ++ "\")";
pp_pattern(#c_literal{val=L}) when is_list(L) ->
  pp_pattern_cons(L);
pp_pattern(#c_literal{val=T}) when is_tuple(T) ->
  io_lib:format("(PTuple [~s])", [pp_list(tuple_to_list(T),", ", fun pp_pattern/1)]);
pp_pattern(#c_cons{hd=H,tl=T}) ->
  io_lib:format("(PCons ~s ~s)", [pp_pattern(H), pp_pattern(T)]);
pp_pattern(#c_tuple{es=Es}) ->
  io_lib:format("(PTuple [~s])", [pp_list(Es,", ", fun pp_pattern/1)]);
pp_pattern(#c_map{arg=_, es=Es,is_pat=_}) ->
  io_lib:format("(PMap [~s])",[pp_list(Es,", ", fun pp_pattern/1)]);
pp_pattern(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}) ->
  io_lib:format("(~s, ~s)",[pp_pattern(K),pp_pattern(V)]);
pp_pattern(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}) ->
  io_lib:format("(~s, ~s)",[pp_pattern(K),pp_pattern(V)]);
pp_pattern(I) when is_integer(I) ->
  "(PLit (Integer (" ++ integer_to_list(I) ++ ")))";
pp_pattern(A) when is_atom(A) ->
  "(PLit (Atom \"" ++ atom_to_list(A) ++ "\"))";
pp_pattern(V) when is_list(V) ->
  pp_pattern_cons(V);
pp_pattern(M) when is_map(M) ->
  io_lib:format("(PMap [~s])", [pp_list(maps:to_list(M), ", ", fun pp_pattern_map/1)]);
pp_pattern(T) when is_tuple(T) ->
  io_lib:format("(PTuple [~s])", [pp_list(tuple_to_list(T),", ", fun pp_pattern/1)]);
pp_pattern(V) -> throw({unsupported_case, V}), io_lib:format("~p", [V]).

%% Helpers for pp_pattern

pp_pattern_cons([]) ->
  "PNil";
pp_pattern_cons([A|B]) ->
  io_lib:format("(PCons ~s ~s)", [pp_pattern(A),pp_pattern(B)]).

pp_pattern_map({A, B}) -> io_lib:format("(~s,~s)", [pp_pattern(A),pp_pattern(B)]).
