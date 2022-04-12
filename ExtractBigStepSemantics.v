Require Core_Erlang_Functional_Big_Step.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.
Import Core_Erlang_Syntax.Value_Notations.
Import ListNotations.

(********************************)
(* Extraction Language: Haskell *)
(********************************)
Extraction Language Haskell.

(***************************)
(* Use Haskell basic types *)
(***************************)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellString.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellNatInt.


(****************************************)
(* Use Haskell support for Nat handling *)
(****************************************)
(*Require Import ExtrHaskellNatNum.*)
(*Extract Inductive Datatypes.nat => "Prelude.Integer" ["0" "succ"]*)
(*"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".*)


Definition fbs_helper (limit : nat)(modules : list ErlModule)
                      (module : string)(expr : Expression) : ResultType :=
  (fbs_expr limit [] modules module 0 expr []).

Extraction "BigStepSemantics.hs" fbs_helper result_value.
