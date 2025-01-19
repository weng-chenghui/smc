From HB Require Import structures.
Require Import Reals.
From mathcomp Require Import all_ssreflect all_algebra fingroup finalg matrix Rstruct ring.
From infotheo Require Import ssrR Reals_ext realType_ext logb ssr_ext ssralg_ext bigop_ext fdist.
From infotheo Require Import proba jfdist_cond entropy graphoid.

Require Import smc_interpreter smc_entropy.

Import GRing.Theory.
Import Num.Theory.
Module scp := smc_interpreter.

(******************************************************************************)
(*                                                                            *)
(*   For Connecting the Zn-to-Z2 Protocol and the SMC Interpreter             *)
(*                                                                            *)
(*   Previous Zn-to-Z2 is a global view implementation, no parties and        *)
(*   communications like in the SMC interpreter model. In this file           *)
(*   we introduce the same model for the Zn-to-Z2 protocol.                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.
Local Open Scope chap2_scope.
Local Open Scope entropy_scope.
Local Open Scope vec_ext_scope.

Section znto_def.

Variable (TX : Type)(VX : Type).
Inductive prog : Type :=
  | Init : TX -> prog -> prog
  | ScalarProduct : nat -> nat -> VX -> (TX -> prog) -> prog
  | Ret : TX -> prog
  | Finish : prog
  | Fail : prog.

End znto_def.

Arguments Finish {TX}{VX}.
Arguments Fail {TX}{VX}.
Arguments Ret {TX}{VX}.

Section znto_prog.
  
Variable n m : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Definition pgalice (x : VX) :=
  Init x (
  ScalarProduct alice bob x (fun y =>
  ScalarProduct alice bob (x + x) (fun z => (* Don't know how to make a 'rV[TX]_n like [:: y; y+y ] *)
  Ret z))).

Let scalar_product sa sb ra yb xa xb :=
      traces (@smc_scalar_product TX VX smc_entropy_proofs.dotproduct sa sb ra yb xa xb 11).2.

Let aresult (tr : smc_scalar_product_alice_tracesT VX) (f : TX -> TX) :=
    let '(ya) := if tr is Some (inl ya, _, _, _, _, _)
                then ya else 0 in f ya.

Let bresult (tr : smc_scalar_product_bob_tracesT VX) (f : TX -> TX) :=
    let '(yb) := if tr is Some (inl yb, _, _, _, _, _)
                then yb else 0 in f yb.

Let pgtraceT := (VX * VX * TX * TX)%type.

Definition pstep (A : Type) (pg : seq (prog _ _)) (rs : seq (VX * VX * TX * TX)%type)
  (trace : seq pgtraceT)
  (yes no : ((prog _ _ * seq pgtraceT)%type -> A)) (i : nat) : A :=
  let pg := nth Fail pg in
  let p := pg i in
  let nop := no (p, trace) in
  let '(sa, sb, ra, yb) := nth (0, 0, 0, 0) rs i in
  match p with
  | ScalarProduct id1 id2 x1 f1 =>
      match pg id2 with
      |  ScalarProduct id2 id1 x2 f2 =>
           if (id1, id2) == (alice, bob) then
                yes (f1 (aresult (Option.bind fst (scalar_product sa sb ra yb x1 x2))), trace)
           else
             if (id1, id2) == (bob, alice) then
                yes (f2 (bresult (Option.bind snd (scalar_product sa sb ra yb x1 x2))), trace)
             else
               nop
      | _ => nop
      end
  | Init d next =>
      yes (next, trace)
  | Ret d =>
      yes (Finish, trace)
  | Finish | Fail =>
      nop
  end.


End znto_prog.
