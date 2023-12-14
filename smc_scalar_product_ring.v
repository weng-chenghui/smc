From mathcomp Require Import all_ssreflect all_algebra ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").

Local Open Scope ring_scope.

Fixpoint zipWith {A B: Type} (fn : A -> A -> B) (l1 : list A) (l2 : list A) : list B :=
	match l1, l2 with
	| [::], _ => [::]
	| _, [::] => [::]
	| a1 :: tl1, a2 :: tl2 => fn a1 a2 :: (zipWith fn tl1 tl2)
	end.

Section smc_scalar_product.

Variable Z:ringType.

Definition dotproduct (la lb: list Z) : Z :=
	foldl (fun sum current => sum + current) 0 (zipWith (fun a b => a * b) la lb).

Definition add (la lb: list Z) : list Z :=
	zipWith (fun a b => a + b) la lb.

Notation "la '`*' lb" := (dotproduct la lb).
Notation "la '`+' lb" := (add la lb).

Definition scalar_product_alice_step1 (Xa Ra: list Z): list Z :=
	Xa `+ Ra.
 
(* Alice: get ya in the SMC scalar-product. *)
Definition scalar_product_alice_fin (X'b Ra: list Z) (ra t: Z): Z :=
	(t - (Ra `* X'b) + ra).

(* Bob: get X'b and pass it to Alice *)
Definition scalar_prduct_bob_step1 (Xb Rb: list Z): list Z :=
	Xb `+ Rb.

(* Bob: receive X'a from Alice and get `t` then pass it to Alice *)
Definition scalar_prduct_bob_step2 (Xb X'a: list Z) (rb yb: Z): Z :=
	(Xb `* X'a) + rb - yb.

Definition scalar_product_bob_step_fin (yb: Z): Z :=
	yb.

(* Because `rb` is not generated from RNG:
   rb =  Ra . Rb - ra
*)
Definition scalar_product_commidity_rb (Ra Rb: list Z) (ra: Z): Z :=
	(Ra `* Rb) - ra.

Definition scalar_product (Ra Rb: list Z) (ra rb yb: Z) (Xa Xb: list Z): (Z * Z) :=
	let X'a := scalar_product_alice_step1 Xa Ra in
	let X'b := scalar_prduct_bob_step1 Xb Rb in
	let t := scalar_prduct_bob_step2 Xb X'a rb yb in
	let ya := scalar_product_alice_fin X'b Ra ra t in
	(scalar_product_alice_fin X'b Ra ra t, scalar_product_bob_step_fin yb).

Definition demo_Alice3_Bob2 : (Z * Z) :=
	let Ra := [:: 9 ] in
	let Rb := [:: 8 ] in
	let ra := 13 in
	let rb := scalar_product_commidity_rb Ra Rb ra in	(* rb =  Ra . Rb - ra *)
	let Xa := [:: 3 ] in
	let Xb := [:: 2 ] in
	let yb := 66 in
	scalar_product Ra Rb ra rb yb Xa Xb.

Definition SMC := list Z -> list Z -> (Z * Z).

Definition is_scalar_product (sp: SMC) :=
	forall(Xa Xb: list Z),
	let (ya, yb') := sp Xa Xb in
	ya + yb' = Xa `* Xb.

End smc_scalar_product.

Notation "la '`*' lb" := (dotproduct la lb).
Notation "la '`+' lb" := (add la lb).

(* Some rings cannot be computed. *)
Eval compute in (demo_Alice3_Bob2 [ringType of int]).

(*

1. Prove it again.
2. zn-to-z2, specialize the SMC scalar-product to modp or bool

bool_comRingType
*)

Section smc_scalar_product_facts.

(* to prove, need com *)
Variable R:comRingType.

Lemma dot_productC (aa bb : list R) : aa `* bb = bb `* aa.
Admitted.

Lemma dot_productDr (aa bb cc : list R) : aa `* (bb `+ cc) = aa `* bb + aa `* cc.
Admitted.

Lemma scalar_product_correct (Ra Rb : list R) (ra yb : R) :
  let rb := scalar_product_commidity_rb Ra Rb ra in
  is_scalar_product (scalar_product Ra Rb ra rb yb).
Proof.
move=>/=Xa Xb/=.
rewrite /scalar_product_alice_fin.
rewrite /scalar_prduct_bob_step2.
rewrite /scalar_product_alice_step1.
rewrite /scalar_prduct_bob_step1.
rewrite /scalar_product_bob_step_fin.
rewrite /scalar_product_commidity_rb.
rewrite !dot_productDr.
rewrite (dot_productC Xb Xa).
rewrite (dot_productC Xb Ra).
ring.
Qed.


End smc_scalar_product_facts.

Section zn_to_z2.

Let B := bool_comRingType.

(* vectors of B *)

Definition zn_to_z2_step2_1 (sp: SMC B) (ci xi: (B * B)) : (B * B) :=
	sp [:: ci.1; xi.1; xi.1] [:: xi.2; ci.2; xi.2].

(* Step 2 for two party. *)
Definition zn_to_z2_step2_2 (ti: B * B) (ci xi xi' : B * B) :
  (B * B) * (B * B) :=
	let cai' := (ci.1 * xi.1 + ti.1) in
	let cbi' := (ci.2 * xi.2 + ti.2) in
	let yai' := (xi'.1 + cai') in
	let ybi' := (xi'.2 + cbi') in
	((cai', cbi'), (yai', ybi')).

Lemma zn_to_z2_step2_1_correct (sp: SMC B) (ci xi: B * B) :
	is_scalar_product sp ->
	let alice_input := [:: ci.1; xi.1; xi.1] in
	let bob_input := [:: xi.2; ci.2; xi.2] in
	let (tai, tbi) := zn_to_z2_step2_1 sp ci xi in
	tai + tbi = alice_input `* bob_input .
Proof.
apply.
Qed.

Check iteri.

(*let y := ([tnth xas 0], [tnth xbs 0]) in*)

Section zn_to_z2_ntuple.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).

Check leqnSn.

(*acc: carry-bit Alice, Bob will receive; results Alice, bob will receive*)
Definition zn_to_z2_folder (acc: (B * B) * list (B * B)) (i: 'I_n): B * B * list(B * B) :=
	let '(ca, cb, ys) := acc in 
	let sp := tnth sps i in
	let i_ := widen_ord (@leqnSn _) i in (* make it can use the implicit argument *)
	let i' := lift ord0 i in
	let xa := tnth xas i_ in
	let xa' := tnth xas i' in 
	let xb := tnth xbs i_ in
	let xb' := tnth xbs i' in 
	match head (0, 0) ys with (* get previous ca, cb and use them to calculate the new result, and push the new result to the acc list*)
	| (ya, yb) => 
		let '(cs, yab) := 
			zn_to_z2_step2_2 (zn_to_z2_step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb')
		in (cs, yab :: ys)
	end.

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := (0, 0, [:: (tnth xas 0, tnth xbs 0)]) in  (* For party A,B: c0=0, y0=x0 *)
	foldl zn_to_z2_folder init (ord_tuple n) .

Definition acc_correct (acc: (B * B) * list (B * B)) (i: 'I_n.+1) :=
	let '((ca, cb), ys) := acc in
	let xa := tnth xas i in
	let xb := tnth xbs i in
	let yas := unzip1 ys in
	let ybs := unzip2 ys in
	let head_y := head (0, 0) ys in
	let ca_ := head_y.1 - xa in
	let cb_ := head_y.2 - xb in
	yas `+ ybs = xa `+ xb /\	(* Correctness 1: def from the paper: [ ya_i + yb_i ... ya_0 + yb_0 ]_2 = (x_a + x_b)_2 -- SMC op result = non-SMC op result. *)
	ca_ = ca /\ cb_ = cb.			(* Correctness 2: from step 2.b, the `c_i+1` that derived from `y_i+1` and `x_i+1`, should be equal to `c` we just folded in `acc` *)


End zn_to_z2_ntuple.

(*
Memo: correctness means to find relations among those terms.
For example: `ca_ = head_y.1 - xa_nth must equal to `ca` from the acc` .
In this relation:

1. how ca relates to the list and its head is explained.
2. how ca should relate to acc is explained.

Things in the definition body will be explained such.
*)

(*
curr: current scalar-product, xai, xbi, cai, cbi

Definition curr_correct :=
	*)

(* Maybe: need an `i` parameter -- equal to the size

i + size of y ==? size of xas
*)
Lemma zn_to_z2_folder_correct acc curr (xas xbs: list B):
	let '(sp, ((xa, xa'), (xb, xb'))) := curr in
	let '(ca', cb', ys') := zn_to_z2_folder acc curr in
	let acc' := (ca', cb', ys') in
	let xa_' := head 0 (drop (size xas - (size ys').+1) xas) in
	let xb_' := head 0 (drop (size xbs - (size ys').+1) xbs) in
	(* TODO: xa' and xb' are from input in every folding process,
	   and xa_' and xb_' are from list by position by the length of current ys' .

	   Having xa_' and xb_' we can relate the xa' and xb' with the lists (xas, xbs, ys),
	   but in the proof this relation is not shown.
	*)
	is_scalar_product curr.1 -> acc_correct xas xbs acc xa xb -> acc_correct xas xbs acc' xa_' xb_'.
Proof.
(* Spliting and moving all parameters to the proof context; for once we unwrap the acc_correct we will need them *)
case: acc=>[[ca cb] ys].
case: curr=>[smc [[xa xa'] [xb xb']]]. 
(* destruct because we see the first let from zn_to_z2_folder above *)
destruct zn_to_z2_folder as [p ys'].
(* destruct because we see `let '(ca', cb') in p` *)
destruct p as [ca' cb'].
destruct acc' as [[ca_' cb_'] ys_'].
move=>smc_correct.
(* TODO: pause here because I feel I am introducing more and more symbols but not sure if they are helping the proof
   For example: ca' ca_' .... ys' and ys_'.
*)


move=>/=t_from_zn_to_z2_step2_1_correct.
(* After moving the premises to the proof context, move acc_correct's hypothesis to the proof context *)
case=>[xa_correct [xb_correct [y_correct [ca_correct [cb_correct [y_not_empty xas_xbs_size_eq]]]]]].
(* We destruct ys to its head and tail _in the proof context_. *)
destruct ys as [|[y tail]]=>//.
(* Then we can unwrap the acc_correct, and do simplification. *)
rewrite /acc_correct/=.
(* We see zn_to_z2_step2_1, so immediately apply the zn_to_z2_step2_1_correct lemma with all parameters,
   and immediately apply it to the goal. *)
have:=zn_to_z2_step2_1_correct (ca, cb) (xa, xb) t_from_zn_to_z2_step2_1_correct.
destruct zn_to_z2_step2_1 as [tai tbi].
(* Simplify the proof context. Because now we have tai, tbi, ca, cb... and other things we want. *)
simpl in *.
move=>t_equation/=.

(* head 0 (drop (size xas - size ys') xas) = head 0 (drop (size xas - (size ys').+1) xas) 

it is

   xa_nth = xa 

in acc_correct.

*

split.
2:{
	split.	(* Correctness 2 in acc_correct: the `c` is correct at each step *)
	1:{	(* ca is correct *) (* attempt: try to unwrap `tai` to ca, xa, cb, xb... so they can be simplified at once? *)
		apply ca_correct.
	}
	2:{	(* cb is correct *)
		split.
	}
}


Abort.

End zn_to_z2.
