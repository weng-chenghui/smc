From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq.
Require Import ssrZ ZArith_ext uniq_tac ssrnat_ext.
Require Import List.
Require Import Coq.Lists.List.
Import ListNotations.
From seplog Require Import machine_int.
Import MachineInt.

Local Open Scope machine_int_scope.

(* Bitwise dot product = count how many "1" exists (dec or bin) after a bitwise AND

  1 0 0 1 (9)
  1 0 0 0 (8)
&------------
  1 0 0 0 (8)


  1 0 0 1 (9)
  1 0 0 0 (8)
.------------------
  1+0+0+0 (1)

So we cannot just `& two bit vectors.
We need to get the number of bit `1` in the result vector.
This is why we need the bitcount helper function, if we want to do dot product in bitwise way

(This is not necessary but we can save the trouble to find and use vector libraries).

*)

(* How many bits with 1 in one binary number in int 32

   The result is always positive, so can be u2Zc, no need to s2Zc.
   And consts inside also always positive. So they are c_32, not sc_32.

*)
(* Copied from: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel *)
(* And a nice explaination: https://stackoverflow.com/questions/3815165/how-to-implement-bitcount-using-only-bitwise-operators *)
Definition bitcount (v: int 32) : int 32 :=
	let _0x55555555 := `( 1431655765 )c_32 in
	let _0x33333333 := `( 858993459 )c_32 in
	let _0x0F0F0F0F := `( 252645135 )c_32 in
	let _0x00FF00FF := `( 16711935 )c_32 in
	let _0x0000FFFF := `( 65535 )c_32 in
	let step1 := ((v `& _0x55555555) `+ ((v `>> 1) `& _0x55555555)) in
	let step2 := ((step1 `& _0x33333333) `+ ((step1 `>> 2) `& _0x33333333)) in
	let step3 := ((step2 `& _0x0F0F0F0F) `+ ((step2 `>> 4) `& _0x0F0F0F0F)) in
	let step4 := ((step3 `& _0x00FF00FF) `+ ((step3 `>> 8) `& _0x00FF00FF)) in
	let step5 := ((step4 `& _0x0000FFFF) `+ ((step4 `>> 16) `& _0x0000FFFF)) in
	step5.

Lemma bitcount9to2_1001 : (u2Zc (bitcount `(9)c_32)) == 2.
Proof.
	rewrite/=.
	done.
Qed.

Lemma bitcount395to5_110001011 : (u2Zc (bitcount `(395)c_32)) == 5.
Proof.
	rewrite/=.
	done.
Qed.


(* Because I'm not sure which vector lib I should use,
   and because of all time I tried and spent on debugging dependant types:

   https://stackoverflow.com/questions/42302300/which-vector-library-to-use-in-coq

   I think current a simple list is sufficient.
*)
Fixpoint zipWith {A B: Type} (fn : A -> A -> B) (l1 : list A) (l2 : list A) : list B :=
	match l1, l2 with
	| [], _ => []
	| _, [] => []
	| a1 :: tl1, a2 :: tl2 => fn a1 a2 :: (zipWith fn tl1 tl2)
	end.

Fixpoint nth_element {A : Type} (n : nat) (l : list A) : option A :=
	match n, l with
	| 0%nat, h :: _ => Some h
	| S n', _ :: tl => nth_element n' tl
	| _, _ => None
	end.

Eval compute in (zipWith (fun a1 a2 => a1 + a2) [1;2;3] [-1;-2]).

Definition dotproduct_bitvecs (la lb: list (int 32)): list (int 32):=
	zipWith (fun a b => (bitcount (a `& b))) la lb.

(* Create a "bitwise and then bit count" operator and use it as the dot product for vectors of int 32. *)
Reserved Notation "la '`.&' lb" (at level 50, format "'[' la  `.&  lb ']'").
Notation "la '`.&' lb" := (dotproduct_bitvecs la lb).

Check dotproduct_bitvecs [ `(9)sc_32 ] [ `(8)sc_32 ].

Eval compute in (bitcount (`( 9 )sc_32 `& `( 8 )sc_32)).

Check s2Zc `( 9 )sc_32.

(* ---- SMC scalar product ---- *)
Lemma bitwisedotproduct_9_8 : (nth_element 0 (map s2Zc ([ `(9)sc_32 ] `.& [ `(8)sc_32 ]))) == Some `(1)sc_32 .
Proof.
	rewrite/=.
Qed.

(* Alice: get X'a and pass it to Bob *)
Definition scalar_product_alice_step1 (Xa Ra: list (int 32)): list (int 32) :=
	zipWith (fun x y => x `+ y) Xa Ra.
 
(* Alice: get ya in the SMC scalar-product. *)
Definition scalar_product_alice_fin {n : nat} (X'b Ra: t (int 32) n) (ra _t: int 32): (t (int 32) n) :=
	(_t `- (Ra `.& X'b) `+ ra).

Lemma test_scalar_product_alice_fin: s2Zc (scalar_product_alice_fin `(10)sc_32 `(9)sc_32 `(13)sc_32 `(-77)sc_32) == -65.
Proof.
	rewrite/=.
	done.
Qed.


(* Bob: get X'b and pass it to Alice *)
(* TODO: because adding two vectors will make their elements overflow -- 1 + 1 = 2,
   this step needs to be combined with the next step. But since in SMC,
   this step sends the added result to the counter part, it cannot be solved easily.
*)
Definition scalar_prduct_bob_step1 (Xb Rb: int 32): int 32 :=
	(Xb `+ Rb).

Lemma test_scalar_prduct_bob_step1: s2Zc (scalar_prduct_bob_step1 `( 2 )sc_32 `( 8 )sc_32) == 10.
Proof.
	rewrite/=.
	done.
Qed.

(* Bob: receive X'a from Alice and get `t` then pass it to Alice *)
Definition scalar_prduct_bob_step2 (Xb X'a rb yb: int 32): int 32 :=
	(Xb `.& X'a) `+ rb `- yb.

Definition scalar_product_bob_step_fin (yb: int 32): int 32 :=
	yb.

Definition scalar_product (Xa Ra ra Xb Rb rb yb: int 32): (int 32 * int 32) :=
	let X'a := scalar_product_alice_step1 Xa Ra in
	let X'b := scalar_prduct_bob_step1 Xb Rb in
	let t := scalar_prduct_bob_step2 Xb X'a rb yb in
	let ya := scalar_product_alice_fin X'b Ra ra t in
	(scalar_product_alice_fin X'b Ra ra t, scalar_product_bob_step_fin yb).

Definition scalar_product_commidity_rb (Ra Rb ra: int 32) : int 32 :=
	(Ra `.& Rb) `- ra.

(* Note: these variables and the result -12 are all from Golang code
   And they show the scalar_product_commidity_rb is correct.
*)	
Lemma test_scalar_product_commidity_rb: s2Zc (scalar_product_commidity_rb `( 9 )sc_32 `( 8 )sc_32 `( 13 )sc_32) == s2Zc `( -12 )sc_32.
Proof.
	rewrite/=.
	done.
Qed.

(* An actual test case from Golang implementation:

https://github.com/weng-chenghui/smc-golang/blob/66c6a659e5c07eade247c615a3b65d7cefbce0bf/pkg/scalarproduct/scalar_product_test.go#L40-L52

*)
(* Note: from here we need to use sc_32, not c_32,
   because some results in these functions could be negative.

   For the same reason we need to use s2Zc, not u2Zc when
   computing results.
*)
Definition demo_Alice3_Bob2 : (int 32 * int 32) :=
	let Ra := `( 9 )sc_32 in
	let Rb := `( 8 )sc_32 in
	let ra := `( 13 )sc_32 in
	let rb := scalar_product_commidity_rb Ra Rb ra in	(* rb =  Ra . Rb - ra *)
	let Xa := `( 3 )sc_32 in
	let Xb := `( 2 )sc_32 in
	let yb := `( 2 )sc_32 in
	scalar_product Xa Ra ra Xb Rb rb yb.

Lemma test1 : s2Zc (fst demo_Alice3_Bob2) == 1.
Proof.
	rewrite/=.
Abort.

Eval compute in (s2Zc (fst demo_Alice3_Bob2)).
Eval compute in (s2Zc (snd demo_Alice3_Bob2)).

Lemma demoequalto : (s2Zc ((fst demo_Alice3_Bob2) `+ (snd demo_Alice3_Bob2))) == (s2Zc (`( 3 )sc_32 `.& `( 2 )sc_32)).
Proof.
	rewrite/=.	(* the same as using `compute` *)
Abort.
