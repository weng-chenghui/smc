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

Section smc_def.

Variable data : Type.
Inductive proc : Type :=
  | Init : data -> proc -> proc
  | ScalarProduct : nat -> nat -> data -> (data -> proc) -> proc
  | Finish : proc
  | Fail : proc.

Definition SMC := data -> data -> data.

Definition step (sps : seq SMC) (A : Type) (ps : seq proc)
  (trace : seq data)
  (yes no : (proc * seq data -> A)) (i : nat) : A :=
  let ps := nth Fail ps in
  let p := ps i in
  let nop := no (p, trace) in
  let '(sp) := nth (fun a _ => a) sps i in
  match p with
  | ScalarProduct id1 id2 x1 f1 =>
      match ps id2 with
      |  ScalarProduct id2 id1 x2 f2 =>
           if (id1, id2) == (alice, bob) then
                yes (f1 (sp x1 x2), trace)
           else
             if (id1, id2) == (bob, alice) then
                yes (f2 (sp x2 x1), trace)
             else
               nop
      | _ => nop
      end
  | Init d next =>
      yes (next, d :: trace)
  | Finish | Fail =>
      nop
  end.

End smc_def.

Arguments Finish {data}.
Arguments Fail {data}.

Section znto_program.
  
Variable n m : nat.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Definition data := (VX + (TX * TX))%type.
Definition inp x : data := inl x.
Definition out x : data := inr x.

Definition pgalice (xa : VX) :=
  Init (inp xa) (
  ScalarProduct alice bob (inp xa) (fun y =>
  ScalarProduct alice bob (inp (xa + xa)) (fun z => (* Don't know how to make a 'rV[TX]_n like [:: y; y+y ] *)
  Finish))).

Let results (trs :  smc_scalar_product_party_tracesT VX) :=
  let ya := if Option.bind fst trs is Some (inl ya, _, _, _, _, _)
                   then ya else 0 in
  let yb := if Option.bind snd trs is Some (inl yb, _, _, _, _, _)
                   then yb else 0 in
  out (ya, yb).

Let sp sa sb ra yb (xa xb : data) :=
      let xa_ := if xa is inl xa then xa else 0 in
      let xb_ := if xb is inl xb then xb else 0 in
      results (traces (@smc_scalar_product TX VX smc_entropy_proofs.dotproduct sa sb ra yb xa_ xb_ 11).2).

Variable (rs : seq (VX * VX * TX * TX)).

Let sps := map (fun r => let '(sa, sb, ra, yb) := r in
  sp sa sb ra yb) rs.

Check interp 11 (step sps).

End znto_program.
