Require Core_Erlang_Coverage.
Import Core_Erlang_Coverage.
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
                      (module : string)(expr : Expression) : ResultType * Log :=
  (fbs_expr limit init_logs [] modules module 0 expr []).

Extraction "BigStepSemanticsTraced.hs" fbs_helper result_value.
