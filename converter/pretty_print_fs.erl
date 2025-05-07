-module(pretty_print_fs).
-export([pp/1, pp_module/1]).
-include_lib("compiler/src/core_parse.hrl").

stringformat([$~,$s|F], [P|Ps]) -> P ++ stringformat(F, Ps);
stringformat([C|Fs], Ps) -> [C|stringformat(Fs, Ps)];
stringformat([], _) -> [].

%% Extend naming scheme
add_name(Var, Names) ->
  NewNames = maps:map(fun(_, V) -> V + 1 end, Names),
  VarName = case Var of
              #c_var{name={N, A}} -> {N, A};
              #c_var{name=N} -> N;
              N -> N
            end,
  maps:put(VarName, 0, NewNames).
  

add_names(Vars, Names) ->
  lists:foldr(fun add_name/2, Names, Vars).

%% Wrapper for pretty-printing - start with the empty naming environment
pp(E) ->
  pp(E, #{}).

%% Adding module functions to letrec

pp_expr(#c_values{es=Es}, Names) ->
  "(EExp (EValues [" ++ pp_list(Es, ";", fun(E) -> pp(E, Names) end) ++ "]))";
pp_expr(E, Names) -> pp(E, Names).

-define(coq_template,
"From CoreErlang Require Import Syntax.
Import ListNotations.
\n
Definition test := ELetRec [~s] (EApp (VVal (VFunId (~s, 1))) [VVal VNil]).
\n
").

% NOTE: to handle recursive calls, the funnames should be bound to 0, 1, ..., k while the fun args to k+1, k+2, ...
% Therefore, we cannot create a new naming scheme here, pp_rec_fun_defs handles that
pp_module(#c_module{defs=Ds}, Names) ->
  {Ns, _} = lists:unzip(Ds),
  CoqDefs = pp_list(Ds,";\n", fun(D) -> pp_rec_fun_defs(D, Ns, Names) end),
  ModFuns = add_names(Ns, #{}),
  stringformat(?coq_template, [CoqDefs, integer_to_list(maps:get({main, 1}, ModFuns))]);
pp_module(M, _) ->
  io:format("Not a module: ~p", [M]),
  throw(badarg).
pp_module(M) ->
  pp_module(M, #{}).

%% Pretty Printing Expressions

pp(#c_primop{name=N, args=As}, Names) ->
  stringformat("(EExp (EPrimOp ~s [~s]))", [pp_atom(N), pp_list(As,";", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_case{arg=A, clauses=Cs}, Names) ->
  stringformat("(EExp (ECase ~s [~s]))", [pp_expr(A, Names), pp_list(Cs, ";", fun(C) -> pp(C, Names) end)]);

pp(#c_clause{pats=Ps, guard=G, body=B}, Names) ->
  {PatStr, PatVars} = pp_pattern_list(Ps, ";", fun pp_pattern/1),
  NewNames = add_names(PatVars, Names),
  stringformat("([~s], ~s, ~s)", [PatStr, pp_expr(G, NewNames), pp_expr(B, NewNames)]);

pp(#c_apply{op=O, args=As}, Names) ->
  stringformat("(EExp (EApp ~s [~s]))", [pp_expr(O, Names), pp_list(As,";", fun(E) -> pp_expr(E, Names) end)]);

%% TODO: these might need to be mapped to Val and not Exp!
pp(#c_literal{val=V}, Names) when is_list(V) ->
  pp_cons(V, Names);
pp(#c_literal{val=V}, _) when is_atom(V) ->
  "(VVal (VLit (Atom \"" ++ atom_to_list(V) ++ "\"%string)))";
pp(#c_literal{val=V}, _) when is_integer(V) ->
  "(VVal (VLit (Integer (" ++ integer_to_list(V) ++ "))))";

pp(#c_literal{val=V}, Names) when is_map(V) ->
  stringformat("(EExp (EMap [~s]))", [pp_list(maps:to_list(V), ";", fun(E) -> pp_pair(E, Names) end)]);
pp(#c_literal{val=T}, Names) when is_tuple(T) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(tuple_to_list(T),";", fun(E) -> pp_expr(E, Names) end)]);
%% END OF TODO


pp(#c_var{name={N, A}}, Names) ->
  stringformat("(VVal (VFunId (~s, ~s)))", [integer_to_list(maps:get({N, A}, Names)), integer_to_list(A)]);
pp(#c_var{name=N}, Names) -> %when is_atom(N) ->
  "(VVal (VVar " ++ integer_to_list(maps:get(N, Names)) ++ "))";
% pp(#c_var{name=N}, Names) when is_integer(N) ->
%  stringformat("(VVal (VVar \"_~s\"%string))", [integer_to_list(N)]);

pp(#c_fun{vars=Vs, body=B}, Names) ->
  stringformat("(EExp (EFun ~s ~s))", [integer_to_list(length(Vs)), pp_expr(B, add_names(Vs, Names))]);

pp(#c_let{vars=Vs, arg=A, body=B}, Names) ->
  stringformat("(EExp (ELet ~s ~s ~s))", [integer_to_list(length(Vs)), pp_expr(A, Names), pp_expr(B, add_names(Vs, Names))]);

pp(#c_letrec{defs=Ds, body=B}, Names) ->
  {Ns, _} = lists:unzip(Ds),
  NewNames = add_names(Ns, Names),
  % The naming scheme for the (mutually) recursive fundefs is created individually for each fundef in pp_rec_fun_defs to ensure
  % the property outlined in the definition of pp for #c_module above
  stringformat("(EExp (ELetRec [~s] ~s))", [pp_list(Ds, ";", fun(D) -> pp_rec_fun_defs(D, Ns, Names) end), pp_expr(B, NewNames)]);

pp(#c_cons{hd=Hd,tl=Tl}, Names) ->
  pp_cons([Hd|Tl], Names);

pp(#c_call{name=N, module=M, args=Es}, Names) ->
  stringformat("(EExp (ECall ~s ~s [~s]))", [pp_expr(M, Names), pp_expr(N, Names), pp_list(Es,";", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_tuple{es=Es}, Names) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(Es,";", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_map{arg=_, es=Es,is_pat=_}, Names) ->
  stringformat("(EExp (EMap [~s]))",[pp_list(Es,";", fun(E) -> pp(E, Names) end)]);

pp(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}, Names) ->
  stringformat("(~s, ~s)",[pp_expr(K, Names),pp_expr(V, Names)]);

pp(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}, Names) ->
  stringformat("(~s, ~s)",[pp_expr(K, Names),pp_expr(V, Names)]);

pp(#c_seq{arg=A, body=B}, Names) ->
  stringformat("(EExp (ESeq ~s ~s))",[pp_expr(A, Names),pp_expr(B, Names)]);

pp(#c_try{arg=A, vars=Vs, body=B, evars=Evs, handler=H}, Names) ->
	stringformat("(EExp (ETry ~s ~s ~s ~s ~s))",[pp_expr(A, Names),
	                                             integer_to_list(length(Vs)) , pp_expr(B, add_names(Vs, Names)),
	                                             integer_to_list(length(Evs)), pp_expr(H, add_names(Evs, Names))]);

pp(I, _) when is_integer(I) ->
  "(VVal (VLit (Integer (" ++ integer_to_list(I) ++ "))))";
pp(A, _) when is_atom(A) ->
  "(VVal (VLit (Atom \"" ++ atom_to_list(A) ++ "\"%string)))";
pp(V, Names) when is_list(V) ->
  pp_cons(V, Names);
pp(V, Names) when is_map(V) ->
  stringformat("(EExp (EMap [~s]))", [pp_list(maps:to_list(V), ";", fun(E) -> pp_pair(E, Names) end)]);
pp(T, Names) when is_tuple(T) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(tuple_to_list(T),";", fun(E) -> pp_expr(E, Names) end)]);

pp(_X, _) ->
  io:format("\n\n\nunsupported case: ~p\n\n\n", [_X]),
  "".

%% Function printing without EFun and varlist
%% This function is only called from pp of #c_module

%%pp_modfuns(#c_fun{vars=Vs, body=B}, Names) ->
%%  stringformat("([~s], ~s)", [pp_list(Vs, ";", fun pp_var/1), pp_expr(B)]);
%%pp_modfuns(_, _) -> todo.

%% PP helpers for expressions

pp_atom(#c_var{name=N}) when is_atom(N) ->
  "\"" ++ atom_to_list(N) ++ "\"%string";
pp_atom(#c_var{name=N}) when is_integer(N) ->
  "\"_"++ integer_to_list(N) ++ "\"%string";
pp_atom(#c_literal{val=V}) ->
  "\"" ++ atom_to_list(V) ++ "\"%string".

pp_list(Es, S, F) -> string:join(lists:map(F, Es), S).


pp_rec_fun_defs({A, B}, NewFunNames, Names) ->
  stringformat("(~s, ~s)", [pp_rec_fun_sign(A),pp_rec_fun_body(B, NewFunNames, Names)]).
pp_rec_fun_sign(#c_var{name={_, A}}) -> % We throw away the name, it becomes a dB index
  stringformat("~s", [integer_to_list(A)]).
pp_rec_fun_body(#c_fun{vars=Vs, body=B}, NewFunNames, Names) ->
  stringformat("~s", [pp_expr(B, add_names(NewFunNames ++ Vs, Names))]).

pp_cons([], _) ->
  "(VVal VNil)";
pp_cons([A|B], Names) ->
  stringformat("(EExp (ECons ~s ~s))", [pp_expr(A, Names),pp_expr(B, Names)]).

pp_pair({A, B}, Names) -> stringformat("(~s,~s)", [pp_expr(A, Names),pp_expr(B, Names)]).



%% Pretty Printing Patterns
%% This function returns the used variables
pp_pattern(#c_literal{val=V}) when is_integer(V) ->
  {"(PLit (Integer (" ++ integer_to_list(V) ++ ")))", []};
pp_pattern(#c_literal{val=V}) when is_atom(V) ->
  {"(PLit (Atom \"" ++ atom_to_list(V) ++ "\"%string))", []};
pp_pattern(#c_var{name=N}) -> % when is_atom(N) ->
  {"PVar", [N]};
%pp_pattern(#c_var{name=N}) when is_integer(N) ->
%  {"(PVar \"_" ++ integer_to_list(N) ++ "\"%string)";
pp_pattern(#c_literal{val=L}) when is_list(L) ->
  pp_pattern_cons(L);
pp_pattern(#c_literal{val=T}) when is_tuple(T) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(T),";", fun pp_pattern/1),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(#c_cons{hd=A,tl=B}) ->
  {StrA, NA} = pp_pattern(A),
  {StrB, NB} = pp_pattern(B),
  {stringformat("(PCons ~s ~s)", [StrA, StrB]), NA ++ NB};
pp_pattern(#c_tuple{es=Es}) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(Es),";", fun pp_pattern/1),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(#c_map{arg=_, es=Es,is_pat=_}) ->
  {Str, Ns} = pp_pattern_list(Es,";", fun pp_pattern/1),
  {stringformat("(PMap [~s])", [Str]), Ns};
pp_pattern(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}) ->
  {StrK, NK} = pp_pattern(K),
  {StrV, NV} = pp_pattern(V),
  {stringformat("(~s, ~s)",[StrK, StrV]), NK ++ NV};
pp_pattern(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}) ->
  {StrK, NK} = pp_pattern(K),
  {StrV, NV} = pp_pattern(V),
  {stringformat("(~s, ~s)",[StrK, StrV]), NK ++ NV};
pp_pattern(I) when is_integer(I) ->
  {"(PLit (Integer (" ++ integer_to_list(I) ++ ")))", []};
pp_pattern(A) when is_atom(A) ->
  {"(PLit (Atom \"" ++ atom_to_list(A) ++ "\"%string))", []};
pp_pattern(V) when is_list(V) ->
  pp_pattern_cons(V);
pp_pattern(M) when is_map(M) ->
  {Str, Ns} = pp_pattern_list(maps:to_list(M), ";", fun pp_pattern_map/1),
  {stringformat("(PMap [~s])", [Str]), Ns};
pp_pattern(T) when is_tuple(T) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(T),";", fun pp_pattern/1),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(V) -> throw({unsupported_case, V}). %, io_lib:format("~p", [V]).

%% Helpers for pp_pattern
%% pp_pattern_list is almost the same as pp_list, but it also accumulates variable names
pp_pattern_list(Ps, S, F) ->
  {Strs, Nss} = lists:unzip(lists:map(F, Ps)),
  {string:join(Strs, S), lists:concat(Nss)}.
%  {"", []};
%pp_pattern_list([H|T], S, F) ->
%  {StrH, NsH} = F(H),
%  {StrT, NsT} = pp_pattern_list(T, S, F),
%  {StrH ++ ";" ++ StrT, NsH ++ NsT}.


pp_pattern_cons([]) ->
  {"PNil", []};
pp_pattern_cons([A|B]) ->
  {StrA, NA} = pp_pattern(A),
  {StrB, NB} = pp_pattern(B),
  {stringformat("(PCons ~s ~s)", [StrA, StrB]), NA ++ NB}.

pp_pattern_map({A, B}) ->
  {StrA, NA} = pp_pattern(A),
  {StrB, NB} = pp_pattern(B),
  {stringformat("(~s,~s)", [StrA, StrB]), NA ++ NB}.
