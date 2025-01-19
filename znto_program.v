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

Section znto.
  
Variable n m : nat.
Variable T : finType.
Variable P : R.-fdist T.
Let TX := [the finComRingType of 'I_m.+2].
Let VX := 'rV[TX]_n.

Let scalar_product sa sb ra yb xa xb :=
      traces (@smc_scalar_product TX VX smc_entropy_proofs.dotproduct sa sb ra yb xa xb 11).2.

Check scalar_product.

End znto.
