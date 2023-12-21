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



(* Step 2 for two party. *)
Definition zn_to_z2_step2_2 (ti: B * B) (ci xi xi' : B * B) :
  (B * B) * (B * B) :=
	let cai' := (ci.1 * xi.1 + ti.1) in
	let cbi' := (ci.2 * xi.2 + ti.2) in
	let yai' := (xi'.1 + cai') in
	let ybi' := (xi'.2 + cbi') in
	((cai', cbi'), (yai', ybi')).

Lemma zn_to_z2_step2_2_correct (ti: B * B) (ci xi xi' : B * B):
	let (c, y) := zn_to_z2_step2_2 ti ci xi xi' in
	y.1 = c.1 + xi'.1 /\ y.2 = c.2 + xi'.2.
Proof.
simpl.
split.
ring.
ring.
Qed.

Definition zn_to_z2_step2_1 (sp: SMC B) (ci xi: (B * B)) : (B * B) :=
	sp [:: ci.1; xi.1; xi.1] [:: xi.2; ci.2; xi.2].

Lemma zn_to_z2_step2_1_correct (sp: SMC B) (ci xi: B * B) :
	is_scalar_product sp ->
	let alice_input := [:: ci.1; xi.1; xi.1] in
	let bob_input := [:: xi.2; ci.2; xi.2] in
	let (tai, tbi) := zn_to_z2_step2_1 sp ci xi in
	tai + tbi = alice_input `* bob_input .
Proof.
apply.
Qed.

Section zn_to_z2_ntuple.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).

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
	ca_ = ca /\ cb_ = cb /\		(* Correctness 1: from step 2.b, the `c_i+1` that derived from `y_i+1` and `x_i+1`, should be equal to `c` we just folded in `acc` *)
	head_y.1 = xa + ca /\
	head_y.2 = xb + cb .

	(* We don't need to verify head_y = (xa + xb) + ca*)
	(*yas `+ ybs = xas_so_far `+ xbs_so_far /\	*)(* Correctness 1: def from the paper: [ ya_i + yb_i ... ya_0 + yb_0 ]_2 = (x_a + x_b)_2 -- SMC op result = non-SMC op result. *)
	                            (* TODO: if we need to verify ys, we need to keep all past c_i in acc for verification, since yas `+ ybs = xas_so_far `+ xbs_so_far `+ cas_so_bar `+ cbs_so_bar *)

Lemma zn_to_z2_folder_correct acc i:
	let i_ := widen_ord (@leqnSn _) i in (* the (@...) form: makes it can use the implicit argument *)
	let i' := lift ord0 i in
	let xai_ := tnth xas i_ in
	let xbi_ := tnth xbs i_ in
	let xai' := tnth xas i' in
	let xbi' := tnth xbs i' in
	let acc' := zn_to_z2_folder acc i in
	is_scalar_product (tnth sps i) -> acc_correct acc i_ -> acc_correct acc' i'.
Proof.
(* Spliting and moving all parameters to the proof context; for once we unwrap the acc_correct we will need them *)
(* Peal until all places we can use other lemmas to support this lemma are shown. *)
case: acc=>[[cai_ cbi_] ys_].
move=> i_ i' xai_ xbi_ xai' xbi'.
rewrite /zn_to_z2_folder.
move=> spi_is_scalar_product acc_correct.  (* Then we show that the computation result acc' also satisify the acc_correct *)
have:=zn_to_z2_step2_1_correct (cai_, cbi_) (xai_, xbi_) spi_is_scalar_product. (* We add what zn_to_z2_step2_1_correct can provide us here *)
destruct zn_to_z2_step2_1 as [tai_ tbi_]. (* Then we don't need the term zn_to_z2_step2_1_correct anymore. Get ti from it. *)
have:=zn_to_z2_step2_2_correct (tai_, tbi_) (cai_, cbi_) (xai_, xbi_) (xai', xbi').
simpl.
move=>p.
case:p.
move=>ya_eq_ca_xi' yb_eq_cb_xi' ti_eq_alice_bob_inputs.

(* MEMO before pausing here:

zn_to_z2_ntuple.acc_correct
  (let (_, _) := head (0, 0) ys_ in
   (cai_ * tnth xas (widen_ord (leqnSn n) i) + tai_, cbi_ * tnth xbs (widen_ord (leqnSn n) i) + tbi_,
    (tnth xas (lift ord0 i) + (cai_ * tnth xas (widen_ord (leqnSn n) i) + tai_),
     tnth xbs (lift ord0 i) + (cbi_ * tnth xbs (widen_ord (leqnSn n) i) + tbi_)) :: ys_)) i'

-->

   let (_, _) := head (0, 0) ys_ in
   (cai', cbi', (yai', ybi'):: ys_)) i'

*)

(* WRONG: not fulfill the `zn_to_z2_step2_1_correct` with all its parameters.
   Because: from the signature, it is: `zn_to_z2_step2_1_correct (SMC B) (B*B) (B*B)`.
            However, for some uknown reasons, the correct `is_scalar_product (SMC B)` premise need to be fed at the last parameter,
			otherwise Coq says the first parameter is NOT scalar product:

			    have:=zn_to_z2_step2_1_correct spi_is_scalar_product (ca, cb) (tnth xas i_, tnth xbs i_).

			The term "spi_is_scalar_product" has type "is_scalar_product (tnth sps i)"
		    while it is expected to have type "(B * B)%type".

	Instead: the premise need to be fed at the last parameter to this Lemma: 

				have:=zn_to_z2_step2_1_correct (ca, cb) (tnth xas i_, tnth xbs i_) spi_is_scalar_product.

	It seems that if a premise is no just a parameter, like `is_scalar_product (SMC B) -> ...` not `SMC B`,
	it needs to be fed at the end.

Proof.
case: acc=>[[ca cb] ys].
move=> i_ i'.
rewrite /zn_to_z2_folder.
move=> spi_is_scalar_product acc_correct.
have:=zn_to_z2_step2_1_correct (ca, cb) (tnth xas i_, tnth xbs i_).
Abort.

*)

(* WRONG: destruct because we see the first let from zn_to_z2_folder above
   Because: if we just destruct the result of zn_to_z2_folder here,
            they just go to the proof context and no underlying SMC steps will be shown,
			so we cannot use lemma we created before to prove their correctness, like
			`zn_to_z2_step2_1_correct`.
   Instead: we `rewrite /zn_to_z2_folder` to unfold the underlying steps.

Proof.
case: acc=>[[ca cb] ys].
destruct zn_to_z2_folder as [p ys'].
Abort.

*)

(* destruct because we see `let '(ca', cb') in p` *)
Abort.

End zn_to_z2_ntuple.

Section zn_to_z2_demo.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).

Definition preset_sp (Ra Rb: list B) (ra yb: B): SMC B :=
	scalar_product Ra Rb ra (scalar_product_commidity_rb Ra Rb ra) yb. 

(* Alice: 3 = (1 1 0); Bob: 2 = (0 1 0); A+B = 5 = (1 0 1) = zn-to-z2 5*)
(*             1 2 4             1 2 4              1 2 4*)
(* Need 3 times of SMC scalar-product. *)
Definition demo_Alice3_Bob2_zn_to_z2 : B * B * seq(B * B) := 
	let sps := [tuple
		preset_sp [::9] [::8] 13 66;
		preset_sp [::32] [::43] 34 5;
		preset_sp [::57] [::40] 31 32
	] in
	let xas := [tuple 0; 1; 1; 0] in
	let xbs := [tuple 0; 1; 0; 0] in
	zn_to_z2 sps xas xbs.

(* Note: not computable (show symbols only). *)
Eval compute in (demo_Alice3_Bob2_zn_to_z2).

End zn_to_z2_demo.



(*
Memo: correctness means to find relations among those terms.
For example: `ca_ = head_y.1 - xa_nth must equal to `ca` from the acc` .
In this relation:

1. how ca relates to the list and its head is explained.
2. how ca should relate to acc is explained.

Things in the definition body will be explained such.
*)
