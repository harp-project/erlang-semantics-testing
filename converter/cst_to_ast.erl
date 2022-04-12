-module(cst_to_ast).
-export([from_erl/3]).
-include_lib("compiler/src/core_parse.hrl").

-define(traditional,
"Require Core_Erlang.Core_Erlang_Tactics.
Import Core_Erlang_Tactics.Tactics.
Import Core_Erlang_Syntax.Value_Notations.
Import Core_Erlang_Semantics.Semantics.
Import ListNotations.
\n
Notation \"%% v\" := (inl [v]) (at level 50).
\n 
Goal exists res, ELetRec  [~s] (EApp (EFunId (\"main\"%string,0)) []) --e-> res.
Proof.
eexists.
match goal with
| |- ?a => assert a as Main
end. { apply eval_expr_intro. eexists. eexists. timeout 240 solve. }
simpl in *. unfold ttrue, ffalse, ok in *. Check Main. exact Main.
Abort. \n\n
\n").

-define(functional,
"Require Core_Erlang.Core_Erlang_Functional_Big_Step.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.
Import Core_Erlang_Syntax.Value_Notations.
Import ListNotations.
Open Scope string_scope.
\n 
Compute result_value (fbs_expr ~p [] ~s \"mytestmodule\" 0 (ECall (ELit (Atom \"~s\")) (ELit (Atom \"main\")) []) []). \n\n
\n").
% ~p : depth, ~s: modules, ~s: module name

-define(functional_traced,
"Require Core_Erlang.Core_Erlang_Coverage.
Import Core_Erlang_Coverage.
Import Core_Erlang_Syntax.Value_Notations.
Import ListNotations.
\n 
Compute ~p. \n\n
Check ~s.
\n").

% Compute result_value (fbs_expr ~p init_logs [] 0 (ELetRec  [~s] (EApp (EFunId (\"main\"%string,0)) [])) []). \n\n

-define(functionalHaskell,
"module Main where

import qualified  Data.Maybe
import BigStepSemantics

main = Prelude.print Prelude.$ (result_value (fbs_helper ~p program))

program :: Expression
program =
  ELetRec  [~s] (EApp (EFunId ((,) \"main\" 0)) ([]))
\n").

-define(functionalHaskellTraced,
"module Main where

import qualified  Data.Maybe
import BigStepSemanticsTraced

main = Prelude.print Prelude.$ (result_value (fbs_helper ~p program))

program :: Expression
program =
  ELetRec  [~s] (EApp (EFunId ((,) \"main\" 0)) ([]))
\n").

-define(functional_limit, 1000000).
map_boolean_to_semantic_selector(true) -> functionalTraced;
map_boolean_to_semantic_selector(false) -> functionalSemantic.

from_erl(FilePaths, ReportDirectory, SemanticSelector) when is_boolean(SemanticSelector)  -> from_erl(FilePaths, ReportDirectory, map_boolean_to_semantic_selector(SemanticSelector));
from_erl(FilePaths, ReportDirectory, SemanticSelector)  -> 
  Modules = [begin
               CompResult = compile:file(Path, [to_core, no_copt, binary]),
               {element(2, CompResult), pp(element(3, CompResult), SemanticSelector)} 
             end
             || Path <- FilePaths],
  AllModules = "[" ++ lists:droplast(lists:foldr(fun({_, Code}, Acc) -> Code ++ ";" ++ Acc end, "", Modules)) ++ "]",
  [ begin
      misc:write_to_file(ReportDirectory ++ atom_to_list(Module) ++ ".v", format_cst(AllModules, atom_to_list(Module), SemanticSelector)),
      Module
    end || {Module, _} <- Modules].

% from_core(Path, SemanticSelector) when is_boolean(SemanticSelector) -> from_core(Path, map_boolean_to_semantic_selector(SemanticSelector));
% from_core(Path, SemanticSelector) -> do_pp(compile:file(Path, [from_core, to_core, binary]), SemanticSelector).

format_cst(Modules, Mod, functionalSemantic) -> io_lib:format(?functional, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functionalTraced) -> io_lib:format(?functional_traced, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functionalSemanticHaskell) -> io_lib:format(?functionalHaskell, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functionalSemanticHaskellTraced) -> io_lib:format(?functionalHaskellTraced, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, traditionalSemantic) -> io_lib:format(?traditional, [Modules, Mod]).

pp(V, functionalSemanticHaskell) ->
  pretty_print_ghc:pp(V);
pp(V, functionalSemanticHaskellTraced) ->
  pretty_print_ghc:pp(V);
pp(V, _SemanticSelector) ->
  pretty_print_coq:pp(V).

%do_pp(V, SemanticSelector) ->
%  case V of
%    {ok, _, CST     } -> format_cst(pp(CST, SemanticSelector), SemanticSelector);
%    {ok, _, CST, _Ws} -> format_cst(pp(CST, SemanticSelector), SemanticSelector);
%     error            -> error;
%    {error, _Es, _Ws} -> error
%  end.
  
