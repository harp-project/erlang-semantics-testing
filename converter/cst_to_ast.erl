-module(cst_to_ast).
-export([from_erl/4]).
-include_lib("compiler/src/core_parse.hrl").

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

% TODO: update
-define(functional_traced,
"Require Core_Erlang.Core_Erlang_Coverage.
Import Core_Erlang_Coverage.
Import Core_Erlang_Syntax.Value_Notations.
Import ListNotations.
\n 
Compute result_value (fbs_expr ~p init_logs [] ~s \"mytestmodule\" 0 (ECall (ELit (Atom \"~s\")) (ELit (Atom \"main\")) []) []). \n\n
\n").

% Compute result_value (fbs_expr ~p init_logs [] 0 (ELetRec  [~s] (EApp (EFunId (\"main\"%string,0)) [])) []). \n\n

-define(functional_haskell,
"module Main where

import qualified  Data.Maybe
import BigStepSemantics

main = Prelude.print Prelude.$ (result_value (fbs_helper ~p ~s \"mytestmodule\" program))

program :: Expression
program =
  ECall (ELit (Atom \"~s\")) (ELit (Atom \"main\")) []
\n").

% TODO: update
-define(functional_haskell_traced,
"module Main where

import qualified  Data.Maybe
import BigStepSemanticsTraced

main = Prelude.print Prelude.$ (result_value (fbs_helper ~p program))

program :: Expression
program =
  ELetRec  [~s] (EApp (EFunId ((,) \"main\" 0)) ([]))
\n").

-define(functional_limit, 1000000).

map_semantic_selector(true, true) -> functional_haskell_traced;
map_semantic_selector(false, true) -> functional_haskell;
map_semantic_selector(true, false) -> functional_traced;
map_semantic_selector(false, false) -> functional.

from_erl(FilePaths, ReportDirectory, SemanticSelector, Export)  -> 
  {Extension, Separator} = case Export of
				             true  -> {".hs", ","};
				             false -> {".v", ";"}
			               end,
  Modules = [begin
               CompResult = compile:file(Path, [to_core, no_copt, binary]),
               {element(2, CompResult), pp(element(3, CompResult), map_semantic_selector(SemanticSelector, Export))} 
             end
             || Path <- FilePaths],
  AllModules = "[" ++ lists:droplast(lists:foldr(fun({_, Code}, Acc) -> Code ++ Separator ++ Acc end, "", Modules)) ++ "]",
  [ begin
      misc:write_to_file(ReportDirectory ++ atom_to_list(Module) ++ Extension, format_cst(AllModules, atom_to_list(Module), map_semantic_selector(SemanticSelector, Export))),
      Module
    end || {Module, _} <- Modules].

format_cst(Modules, Mod, functional) -> io_lib:format(?functional, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functional_traced) -> io_lib:format(?functional_traced, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functional_haskell) -> io_lib:format(?functional_haskell, [?functional_limit, Modules, Mod]);
format_cst(Modules, Mod, functional_haskell_traced) -> io_lib:format(?functional_haskell_traced, [?functional_limit, Modules, Mod]).

pp(V, functional_haskell) ->
  pretty_print_ghc:pp(V);
pp(V, functional_haskell_traced) ->
  pretty_print_ghc:pp(V);
pp(V, _SemanticSelector) ->
  pretty_print_coq:pp(V).

