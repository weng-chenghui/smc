From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra Require Import all_algebra.
From mathcomp.algebra_tactics Require Import ring.
Require Import mathcomp_extra.


(*  
    Shen, Chih-Hao, Justin, Zhan, Tsan-Sheng, Hsu, Churn-Jung, Liau, and Da-Wei, Wang. "Scalar-product based secure two-party computation." . In 2008 IEEE International Conference on Granular Computing (pp. 556-561).2008.

    http://dx.doi.org/10.1109/GRC.2008.4664775
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Require Import scalarproduct.smc_interpreter.
Module scp := smc_interpreter.


Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").

Local Open Scope ring_scope.

Section def.

Definition SMC (T : Type) := list T -> list T -> (T * T).

Definition dotproduct (R : semiRingType) (la lb: list R) : R :=
	foldl +%R 0 (zipWith *%R la lb).

Fixpoint add (R : nmodType) (la lb: list R) : list R :=
    match la, lb with
    |[::], _ => lb
    |_, [::] => la
    |a::la, b::lb => a+b :: add la lb
    end.
(* The previous version `add`: map (fun a => a.1 + a.2) (zip la lb).
   Need extra hypothesis for their length,
   and thus all related proofs need those hypothesis.
   Therefore, we use this fixpoint version to save the extra work. *)

End def.

Local Notation "la '`*' lb" := (dotproduct la lb).
Local Notation "la '`+' lb" := (add la lb).

Section linear_algebra.


Lemma add_cat (R : nmodType) (s1 s2 t1 t2 : seq R) :
  size s1 = size t1 ->
  add (s1 ++ s2) (t1 ++ t2) = add s1 t1 ++ add s2 t2.
Proof. elim: s1 t1 => [|a aa IH] [|b bb] //= [Hs]. by rewrite IH. Qed.

Lemma rev_add (R : nmodType) (s t : seq R) :
  size s = size t -> rev (s `+ t) = rev s `+ rev t.
Proof.
rewrite -(revK s) -(revK t) !(size_rev (rev _)).
elim: (rev s) (rev t) => [|a aa IH] [|b bb] //= [Hs].
by rewrite !rev_cons -!cats1 add_cat ?size_rev //= !cats1 !rev_rcons IH.
Qed.

Lemma take1 (R : nmodType) (s: seq R):
  (size s > 0)%N -> take 1 s = [::head 0 s].
Proof. by case: s => [| ? []]. Qed.

End linear_algebra.

Local Notation "la '`*' lb" := (dotproduct la lb).
Local Notation "la '`+' lb" := (add la lb).


Section smc_scalar_product.

Variable R:ringType.

Definition is_scalar_product (sp: SMC R) :=
  forall Xa Xb, (sp Xa Xb).1 + (sp Xa Xb).2 = Xa `* Xb.

About scp.is_scalar_product.
About scp.scalar_product.

End smc_scalar_product.

Section zn_to_z2.
Variable R : ringType.

Section step2_1.
Variables (sp : SMC R) (ci xi : R * R).

Local Notation alice_input := [:: ci.1; xi.1; xi.1].
Local Notation bob_input := [:: xi.2; ci.2; xi.2].

Definition step2_1 : (R * R) := (sp alice_input bob_input).

Definition step2_1_correct :
  is_scalar_product sp -> step2_1.1 + step2_1.2 = alice_input `* bob_input.
Proof. exact. Qed.
End step2_1.

Section step2_2.
Variables (ti ci xi xi' : R * R).

Definition step2_2 : (R * R) * (R * R) :=
  let cai' := (ci.1 * xi.1 + ti.1) in
  let cbi' := (ci.2 * xi.2 + ti.2) in
  let yai' := (xi'.1 + cai') in
  let ybi' := (xi'.2 + cbi') in
  ((cai', cbi'), (yai', ybi')).

Definition step2_2_correct :
    let (c, y) := step2_2 in
    y.1 = c.1 + xi'.1 /\ y.2 = c.2 + xi'.2.
Proof. by split; rewrite /= addrC. Qed.
End step2_2.

End zn_to_z2.


Section zn_to_z2_ntuple.

Let B := bool.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).

Notation "t '!_' i" := (tnth t i) (at level 10). (* lv9: no parenthesis; so lv10*)

Hypothesis xan : xas!_(ord_max) = false.
Hypothesis xbn : xbs!_(ord_max) = false.
Hypothesis sps_is_sp : forall i, is_scalar_product (sps !_ i).
Hypothesis nop_sp : SMC B.

(*acc: carry-bit Alice, Bob will receive; results Alice, bob will receive*)
Definition folder i (acc: i.+1.-tuple ((B * B) * (B * B))) :
  i.+2.-tuple ((B * B) * (B * B)) :=
	let '((ca, cb), _) := acc !_ 0 in
	let sp := nth nop_sp sps i in
	let xa := xas `_ i in
	let xa' := xas `_ i.+1 in
	let xb := xbs `_ i in
	let xb' := xbs `_ i.+1 in
	step2_2 (step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb') :: acc.

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := [tuple ((0, 0), (xas`_0, xbs`_0))] in  (* For party A,B: c0=0, y0=x0 *)
	iteri_dep folder init n.

Definition carry_correct (ca cb ca' cb' xa xb : B) :=
  ((ca + cb)%R * 2 + (xa + ca' + (xb + cb'))%R = (ca' + cb')%R + (xa + xb))%N.

(* Here we expect `i < n+1` *)
Definition decimal_eq i (cas cbs yas ybs : seq B) :=
  ((cas `_ i + cbs `_ i)%R * 2 ^ i +
   \sum_(j < i) (yas `_ j + ybs `_ j)%R * 2 ^ j == 
     \sum_(j < i) ((xas `_ j)%R + (xbs `_ j)%R) * 2 ^ j)%N.

Lemma decimal_eq0:
  decimal_eq 0 [:: 0] [:: 0] [:: xas`_0] [:: xbs`_0].
Proof. by rewrite /decimal_eq /= !big_ord0 addn0. Qed.

Definition split4 i (acc: i.+1.-tuple ((B * B) * (B * B))) :=
  (unzip1 (unzip1 acc), unzip2 (unzip1 acc), unzip1 (unzip2 acc), unzip2 (unzip2 acc)).

(* Here we expect `i < n+1` *)
Definition acc_correct i (acc: i.+1.-tuple ((B * B) * (B * B))) :=
  let '(cas, cbs, yas, ybs) := split4 (rev acc) in
  [/\
    yas`_i = xas`_i + cas`_i,
    ybs`_i = xbs`_i + cbs`_i
    & decimal_eq i cas cbs yas ybs].

Lemma carry_correctP  cai_ cbi_ tai_ tbi_ i :
  tai_ + tbi_ = [:: cai_; xas`_i; xas`_i] `* [:: xbs`_i; cbi_; xbs`_i] ->
  carry_correct (cai_ * xas`_i + tai_) (cbi_ * xbs`_i + tbi_)
                cai_ cbi_ xas`_i xbs`_i.
Proof.
move => Htai_tbi.
rewrite /carry_correct /=.
rewrite -(addrC tbi_) addrA -(addrA _ tai_) (addrA tai_) {}Htai_tbi.
rewrite /dotproduct /=. (* calc dotproduct*)
by move: cai_ (xas`_i) (xbs`_i) cbi_ => [] [] [] [].
Qed.

Lemma folder_correctP i (acc : i.+1.-tuple _) :
  (i < n.+1 -> acc_correct acc)%N ->
  (i.+1 < n.+1 -> acc_correct (folder acc))%N.
Proof.
rewrite (ltnS i.+1) => Hacc Hi.
move/(_ (ltnW Hi)) in Hacc.
case: acc Hacc => acc Hsz [] /=.
move Hacc: acc Hsz => [ |[[cai cbi] [ya yb]] acc'] // Hsz.
rewrite -{-9}Hacc /= => Hyas Hybs Hdec.
rewrite /folder /= [in nth _ _ _](_ : i = Ordinal Hi) // -tnth_nth.
have := step2_1_correct (cai, cbi) (xas`_i, xbs`_i) (sps_is_sp (Ordinal Hi)).
case: step2_1 => /= tai tbi Htai_tbi.
rewrite /acc_correct /= -Hacc.
rewrite !(unzip1_rev,unzip2_rev) in Hyas Hybs Hdec *.
rewrite /step2_2 /=.
rewrite -Hacc in Hsz.
move/eqP in Hsz.
rewrite !rev_cons !nth_rcons !size_rev !size_map Hsz /= ltnn eqxx.
split => //.
rewrite /decimal_eq 2!big_ord_recr /=.
rewrite !nth_rcons ?(size_rev,size_map,Hsz) ltnn eqxx ltnSn.
move/eqP: Hdec => /= <-.
apply/eqP.
under eq_bigr do rewrite !(nth_rcons,size_rev,size_map,Hsz) ltnW ?ltnS //.
rewrite addnA addnAC [RHS]addnAC.
congr addn.
rewrite !nth_rev ?(size_rev,size_map,Hsz) // subnn Hacc /=.
rewrite expnS mulnA -!mulnDl -(carry_correctP Htai_tbi).
congr ((_ + _) * _)%N.
move: Hsz Hyas Hybs; rewrite Hacc /=; clear => /= -[Hsz].
rewrite !rev_cons !nth_rcons !size_rev !size_map Hsz /= ltnn eqxx.
by move => -> ->.
Qed.

Lemma zn_to_z2_correctP :
  let '(cas, cbs, yas, ybs) := split4 (rev zn_to_z2) in
  decimal_eq n cas cbs yas ybs.
Proof.
have [] // :=
  iteri_dep_ind (init:=[tuple ((0, 0), (xas`_0, xbs`_0))]) folder_correctP _ n.
by rewrite /acc_correct /= !addr0 decimal_eq0.
Qed.

End zn_to_z2_ntuple.
