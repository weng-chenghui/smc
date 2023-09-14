From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq.
Require Import ssrZ ZArith_ext uniq_tac ssrnat_ext.
From seplog Require Import machine_int.
Import MachineInt.

Local Open Scope machine_int_scope.

(* Because we need a `mul` version of `*, not the default version which uses `umul *)
Reserved Notation "a '`*' b" (at level 50, format "'[' a  `*  b ']'").
Notation "a '`*' b" := (mul a b) : machine_int_scope.

(* Alice: get X'a and pass it to Bob *)
Definition scalar_product_alice_step1 (Xa Ra: int 16): int 16 :=
	(Xa `+ Ra).
 
(* Alice: get ya in the SMC scalar-product. *)
Definition scalar_product_alice_fin (X'b Ra ra t: int 16): int 16 :=
	(t `- (Ra `* X'b) `+ ra).

(* Bob: get X'b and pass it to Alice *)
Definition scalar_prduct_bob_step1 (Xb Rb: int 16): int 16 :=
	(Xb `+ Rb).

(* Bob: receive X'a from Alice and get `t` then pass it to Alice *)
Definition scalar_prduct_bob_step2 (Xb X'a rb yb: int 16): int 16 :=
	Xb `* X'a `+ rb `- yb.

Definition scalar_product_bob_step_fin (yb: int 16): int 16 :=
	yb.

Definition scalar_product (Xa Ra ra Xb Rb rb yb: int 16): (int 16 * int 16) :=
	let X'a := scalar_product_alice_step1 Xa Ra in
	let X'b := scalar_prduct_bob_step1 Xb Rb in
	let t := scalar_prduct_bob_step2 Xb X'a rb yb in
	let ya := scalar_product_alice_fin X'b Ra ra t in
	(scalar_product_alice_fin X'b Ra ra t, scalar_product_bob_step_fin yb).

(* An actual test case from Golang implementation:

https://github.com/weng-chenghui/smc-golang/blob/66c6a659e5c07eade247c615a3b65d7cefbce0bf/pkg/scalarproduct/scalar_product_test.go#L40-L52

*)
Definition demo_Alice3_Bob2 : (int 16 * int 16) :=
	let Ra := `( 9 )c_16 in
	let Rb := `( 8 )c_16 in
	let ra := `( 13 )c_16 in
	let rb := `( -12 )c_16 in	(* rb =  Ra . Rb - ra *)
	let Xa := `( 3 )c_16 in
	let Xb := `( 2 )c_16 in
	let yb := `( 2 )c_16 in
	scalar_product Xa Ra ra Xb Rb rb yb.


Eval compute in (u2Zc (fst demo_Alice3_Bob2)).

(* Memo: next: build from this pure version to monadic version, by introducing state, fail and so on later. *)



Eval compute in (u2Zc (scalar_product_alice_step1 `(2)c_16 `(3)c_16)).

Check (u2Zc (`(2)c_16 `+ `(3)c_16)).

Eval compute in (u2Zc (`( 2 )c_16 `+ `( 2 )c_16)).