-module(pretty_print_coq).
-export([pp/1, pp/2]).
-include_lib("compiler/src/core_parse.hrl").

stringformat([$~,$s|F], [P|Ps]) -> P ++ stringformat(F, Ps);
stringformat([C|Fs], Ps) -> [C|stringformat(Fs, Ps)];
stringformat([], _) -> [].

%% Adding module functions to letrec

pp_expr(#c_values{es=Es}) -> "(EValues [" ++ pp_list(Es, ";", fun pp/1) ++ "])";
pp_expr(E) -> pp(E).

pp_topfun(#c_fun{vars=Vs, body=B}) ->
  stringformat("varl := [~s]; body := ~s", [pp_list(Vs, ";", fun pp_var/1), pp_expr(B)]);
pp_topfun(_) -> todo.

pp(#c_module{name=#c_literal{val=Name}, exports=Exports, attrs=Attrs, defs=Ds}) ->
  stringformat("{| name := \"~s\"%string; funcIds := [~s]; attrs := [~s]; funcs := [~s] |}",
               [atom_to_list(Name),
                pp_list(Exports,";",fun pp_var/1),
                pp_list([],";",fun pp/1), % TODO!!!
                pp_list(Ds,";",fun({FunId, Body}) -> stringformat("{| identifier := ~s ; ~s |}",[pp_letrec_sign(FunId), pp_topfun(Body)]) end)
               ]);

pp(#c_module{name=Name, exports=Exports, attrs=Attrs, defs=Ds}) ->
  io:format("~n~nWrong format: ~w~n~n", [Name]);

%% Pretty Printing Expressions

pp(#c_primop{name=N, args=As}) ->
  stringformat("(EPrimOp ~s [~s])", [pp_var(N), pp_list(As,";", fun pp_expr/1)]);

pp(#c_case{arg=A, clauses=Cs}) ->
  stringformat("(ECase ~s [~s])", [pp_expr(A), pp_list(Cs, ";", fun pp/1)]);

pp(#c_clause{pats=Ps, guard=G, body=B}) ->
  stringformat("([~s], ~s, ~s)", [pp_list(Ps,";", fun pp_pattern/1), pp_expr(G), pp_expr(B)]);

pp(#c_apply{op=O, args=As}) ->
  stringformat("(EApp ~s [~s])", [pp_expr(O), pp_list(As,";", fun pp_expr/1)]);

pp(#c_literal{val=V}) when is_list(V) ->
  pp_cons(V);
pp(#c_literal{val=V}) when is_atom(V) ->
  "(ELit (Atom \"" ++ atom_to_list(V) ++ "\"%string))";
pp(#c_literal{val=V}) when is_integer(V) ->
  "(ELit (Integer (" ++ integer_to_list(V) ++ ")))";

pp(#c_literal{val=V}) when is_map(V) ->
  stringformat("(EMap [~s])", [pp_list(maps:to_list(V), ";", fun pp_pair/1)]);
pp(#c_literal{val=T}) when is_tuple(T) ->
  stringformat("(ETuple [~s])", [pp_list(tuple_to_list(T),";", fun pp_expr/1)]);
pp(#c_var{name=N}) when is_atom(N) ->
  "(EVar \"" ++ atom_to_list(N) ++ "\"%string)";
pp(#c_var{name=N}) when is_integer(N) ->
  stringformat("(EVar \"_~s\"%string)", [integer_to_list(N)]);
pp(#c_var{name={N, A}}) ->
  stringformat("(EFunId (\"~s\"%string, ~s))", [atom_to_list(N), integer_to_list(A)]);

pp(#c_fun{vars=Vs, body=B}) ->
  stringformat("(EFun [~s] ~s)", [pp_list(Vs,";", fun pp_var/1), pp_expr(B)]);

%% If only one expression is bound (which is not in a value list)
pp(#c_let{vars=Ds, arg=A, body=B}) ->
  stringformat("(ELet [~s] ~s ~s)", [pp_list(Ds,";", fun pp_var/1), pp_expr(A), pp_expr(B)]);

pp(#c_letrec{defs=Ds, body=B}) ->
  stringformat("(ELetRec [~s] ~s)", [pp_list(Ds, ";", fun pp_letrec_defs/1), pp_expr(B)]);

pp(#c_cons{hd=Hd,tl=Tl}) ->
  pp_cons([Hd|Tl]);
  
%% Correct call formalization (for future syntax)
%pp(#c_call{name=N, module=M args=Es}) ->
%  stringformat("(ECall ~s ~s [~s])", [pp_expr(M), pp_expr(N), pp_list(Es,";", fun pp_expr/1)]);
pp(#c_call{module=M,name=N,args=Es}) ->
	stringformat("(ECall ~s ~s [~s])", [pp(M),pp(N), pp_list(Es,";", fun pp_expr/1)]);

pp(#c_tuple{es=Es}) ->
  stringformat("(ETuple [~s])", [pp_list(Es,";", fun pp_expr/1)]);

pp(#c_map{arg=_, es=Es,is_pat=_}) ->
  stringformat("(EMap [~s])",[pp_list(Es,";", fun pp/1)]);

pp(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}) ->
  stringformat("(~s, ~s)",[pp_expr(K),pp_expr(V)]);

pp(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}) ->
  stringformat("(~s, ~s)",[pp_expr(K),pp_expr(V)]);

pp(#c_seq{arg=A, body=B}) ->
  stringformat("(ESeq ~s ~s)",[pp_expr(A),pp_expr(B)]);

pp(#c_try{arg=A, vars=Vs, body=B, evars=Evs, handler=H}) ->
	stringformat("(ETry ~s [~s] ~s [~s] ~s)",[pp_expr(A), pp_list(Vs,";", fun pp_var/1), pp_expr(B), pp_list(Evs,";", fun pp_var/1), pp_expr(H)]);

pp(I) when is_integer(I) ->
  "(ELit (Integer (" ++ integer_to_list(I) ++ ")))";
pp(A) when is_atom(A) ->
  "(ELit (Atom \"" ++ atom_to_list(A) ++ "\"%string))";
pp(V) when is_list(V) ->
  pp_cons(V);
pp(V) when is_map(V) ->
  stringformat("(EMap [~s])", [pp_list(maps:to_list(V), ";", fun pp_pair/1)]);
pp(T) when is_tuple(T) ->
  stringformat("(ETuple [~s])", [pp_list(tuple_to_list(T),";", fun pp_expr/1)]);

pp(_X) ->
  io:format("\n\n\nunsupported case: ~p\n\n\n", [_X]),
  "".

%% Function printing without EFun and varlist

pp(#c_fun{vars=Vs, body=B}, _) ->
  stringformat("([~s], ~s)", [pp_list(Vs, ";", fun pp_var/1), pp_expr(B)]);
pp(_, _) -> todo.

%% PP helpers for expressions

pp_var(#c_var{name=N}) when is_atom(N) ->
  "\"" ++ atom_to_list(N) ++ "\"%string";
pp_var(#c_var{name=N}) when is_integer(N) ->
  "\"_"++ integer_to_list(N) ++ "\"%string";
pp_var(#c_literal{val=V}) ->
  "\"" ++ atom_to_list(V) ++ "\"%string";
pp_var(#c_var{name={N, A}}) ->
  stringformat("(\"~s\"%string, ~s)", [atom_to_list(N), integer_to_list(A)]).

pp_list(Es, S, F) -> string:join(lists:map(F, Es), S).


pp_letrec_defs({A, B}) ->
  stringformat("(~s, ~s)", [pp_letrec_sign(A),pp_letrec_ve(B)]).
pp_letrec_sign(#c_var{name={N, A}}) ->
  stringformat("(\"~s\"%string, ~s)", [atom_to_list(N), integer_to_list(A)]).
pp_letrec_ve(#c_fun{vars=Vs, body=B}) ->
  stringformat("([~s], ~s)", [pp_list(Vs, ";", fun pp_var/1), pp_expr(B)]).

pp_cons([]) ->
  "ENil";
pp_cons([A|B]) ->
  stringformat("(ECons ~s ~s)", [pp_expr(A),pp_expr(B)]).

pp_pair({A, B}) -> stringformat("(~s,~s)", [pp_expr(A),pp_expr(B)]).



%% Pretty Printing Patterns

pp_pattern(#c_literal{val=V}) when is_integer(V) ->
  "(PLit (Integer (" ++ integer_to_list(V) ++ ")))";
pp_pattern(#c_literal{val=V}) when is_atom(V) ->
  "(PLit (Atom \"" ++ atom_to_list(V) ++ "\"%string))";
pp_pattern(#c_var{name=N}) when is_atom(N) ->
  "(PVar \"" ++ atom_to_list(N) ++ "\"%string)";
pp_pattern(#c_var{name=N}) when is_integer(N) ->
  "(PVar \"_" ++ integer_to_list(N) ++ "\"%string)";
pp_pattern(#c_literal{val=L}) when is_list(L) ->
  pp_pattern_cons(L);
pp_pattern(#c_literal{val=T}) when is_tuple(T) ->
  stringformat("(PTuple [~s])", [pp_list(tuple_to_list(T),";", fun pp_pattern/1)]);
pp_pattern(#c_cons{hd=H,tl=T}) ->
  stringformat("(PCons ~s ~s)", [pp_pattern(H), pp_pattern(T)]);
pp_pattern(#c_tuple{es=Es}) ->
  stringformat("(PTuple [~s])", [pp_list(Es,";", fun pp_pattern/1)]);
pp_pattern(#c_map{arg=_, es=Es,is_pat=_}) ->
  stringformat("(PMap [~s])",[pp_list(Es,";", fun pp_pattern/1)]);
pp_pattern(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}) ->
  stringformat("(~s, ~s)",[pp_pattern(K),pp_pattern(V)]);
pp_pattern(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}) ->
  stringformat("(~s, ~s)",[pp_pattern(K),pp_pattern(V)]);
pp_pattern(I) when is_integer(I) ->
  "(PLit (Integer (" ++ integer_to_list(I) ++ ")))";
pp_pattern(A) when is_atom(A) ->
  "(PLit (Atom \"" ++ atom_to_list(A) ++ "\"%string))";
pp_pattern(V) when is_list(V) ->
  pp_pattern_cons(V);
pp_pattern(M) when is_map(M) ->
  stringformat("(PMap [~s])", [pp_list(maps:to_list(M), ";", fun pp_pattern_map/1)]);
pp_pattern(T) when is_tuple(T) ->
  stringformat("(PTuple [~s])", [pp_list(tuple_to_list(T),";", fun pp_pattern/1)]);
pp_pattern(V) -> throw({unsupported_case, V}), io_lib:format("~p", [V]).

%% Helpers for pp_pattern

pp_pattern_cons([]) ->
  "PNil";
pp_pattern_cons([A|B]) ->
  stringformat("(PCons ~s ~s)", [pp_pattern(A),pp_pattern(B)]).

pp_pattern_map({A, B}) -> stringformat("(~s,~s)", [pp_pattern(A),pp_pattern(B)]).
