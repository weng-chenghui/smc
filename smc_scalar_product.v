From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra Require Import all_algebra.
From mathcomp.algebra_tactics Require Import ring.
Require Import mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").

Local Open Scope ring_scope.


(*
    Du, Wenliang, and Zhĳun, Zhan. "A practical approach to solve Secure Multi-party Computation problems." . In Proceedings of the 2002 Workshop on New Security Paradigms (pp. 127–135). Association for Computing Machinery, 2002.

    https://doi.org/10.1145/844102.844125
*)

Section datatypes.
Variable T : Type.

(* Owned: genereated in or received by Alice *)
Record alice_owned :=
  AliceOwned {
    Ra  : seq T;
    Xa  : seq T;
    X'b : seq T;
    ra  : T;
    recv_t   : T;
    ya  : T;
  }.

(* Owned: genereated in or received by Bob *)
Record bob_owned :=
  BobOwned {
    Rb  : seq T;
    Xb  : seq T;
    X'a : seq T;
    rb  : T;
    send_t : T;
    yb  : T;
  }.

Definition SMC := list T -> list T -> (T * T * (alice_owned * bob_owned)).

End datatypes.


Section linear_algebra.

Section def.

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

Lemma dot_productC (R : comSemiRingType) (aa bb : list R) : aa `* bb = bb `* aa.
Proof.
rewrite /dotproduct.
elim: aa bb 0 => [| a aa IH] [| b bb] z //=.
by rewrite mulrC.
Qed.

Lemma dot_productE (R : semiRingType) (aa bb: list R) (z: R) :
  z + aa `* bb = foldl +%R z (zipWith *%R aa bb).
Proof.
rewrite /dotproduct -[in RHS](addr0 z).
elim: aa bb z 0=> [| a aa IH] [| b bb] z z2 //=.
by rewrite IH addrA.
Qed.  

Lemma dot_productDr (R : semiRingType) (aa bb cc : list R) :
  aa `* (bb `+ cc) = aa `* bb + aa `* cc.
Proof.
rewrite /dotproduct.
set z:={1 2}0.
rewrite -{1}(addr0 z).
elim: aa bb cc z 0 => [| a aa IH] [| b bb] [|c cc] z z2 //=;
  rewrite ?IH -!dot_productE //=.
- by rewrite !addrA.
- by rewrite [RHS](addrC _ z2) !addrA (addrC z).
- by rewrite mulrDr !addrA !(addrAC _ z2) !(addrAC _ (a*b)).
Qed.

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

Definition commodity_rb  (Ra Rb: list R) (ra: R): R :=
	(Ra `* Rb) - ra.

(* Put this definition in the record will make every time we have the record,
   we need to provide the hypothesis,
   so temporarily separate it from the record.
 *)
Definition is_alice_owned (ao: alice_owned R) :=
  ya ao = recv_t ao - (Ra ao `* X'b ao) + ra ao.

Definition is_bob_owned (bo: bob_owned R) :=
  send_t bo = (Xb bo `* X'a bo) + rb bo - yb bo.

Definition scalar_product (Ra Rb: list R) (ra rb yb: R) : SMC R :=
  fun Xa Xb =>
    let X'a := Xa `+ Ra in
    let X'b := Xb `+ Rb in
    let t := (Xb `* X'a) + rb - yb in
    let ya := t - (Ra `* X'b) + ra in
    (ya, yb, (AliceOwned Ra Xa X'b ra t ya, BobOwned Rb Xb X'a rb t yb)).

Definition demo_Alice3_Bob2 : (R * R) :=
	let Ra := [:: 9 ] in
	let Rb := [:: 8 ] in
	let ra := 13 in
	let rb := commodity_rb Ra Rb ra in	(* rb =  Ra . Rb - ra *)
	let Xa := [:: 3 ] in
	let Xb := [:: 2 ] in
	let yb := 66 in
	(scalar_product Ra Rb ra rb yb Xa Xb).1.

Definition is_scalar_product (sp: SMC R) :=
  forall Xa Xb, (sp Xa Xb).1.1 + (sp Xa Xb).1.2 = Xa `* Xb.

End smc_scalar_product.

Eval compute in (demo_Alice3_Bob2 int).


Section smc_scalar_product_facts.
Variable R:comRingType.

Lemma scalar_product_correct (Ra Rb : list R) (ra yb : R) :
  let rb := commodity_rb Ra Rb ra in
  is_scalar_product (scalar_product Ra Rb ra rb yb).
Proof.
move=> /= Xa Xb.
rewrite  /commodity_rb /is_scalar_product /=.
rewrite !dot_productDr (dot_productC Xb Xa) (dot_productC Xb Ra).
(* should be just "ring." *)
apply/eqP; rewrite eq_sym -3!subr_eq opprK !addrA.
by rewrite !(addrAC _ (-yb)) !(addrAC _ (-ra)).
Qed.

End smc_scalar_product_facts.


(*  
    Shen, Chih-Hao, Justin, Zhan, Tsan-Sheng, Hsu, Churn-Jung, Liau, and Da-Wei, Wang. "Scalar-product based secure two-party computation." . In 2008 IEEE International Conference on Granular Computing (pp. 556-561).2008.

    http://dx.doi.org/10.1109/GRC.2008.4664775
*)
Section zn_to_z2.
Variable R : ringType.

Section step2_1.
Variables (sp : SMC R) (ci xi : R * R).

Local Notation alice_input := [:: ci.1; xi.1; xi.1].
Local Notation bob_input := [:: xi.2; ci.2; xi.2].

Definition step2_1 : (R * R) := (sp alice_input bob_input).1.

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

(*acc: carry-bit Alice, Bob will receive; results Alice, bob will receive*)
Definition folder i (acc: i.+1.-tuple ((B * B) * (B * B))) :
  i.+2.-tuple ((B * B) * (B * B)) :=
	let '((ca, cb), _) := acc !_ 0 in
	let sp := nth (scalar_product nil nil 0 0 0 : SMC B) sps i in
	let xa := xas `_ i in
	let xa' := xas `_ i.+1 in
	let xb := xbs `_ i in
	let xb' := xbs `_ i.+1 in
	step2_2 (step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb') :: acc.

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := [tuple ((0, 0), (xas`_0, xbs`_0))] in  (* For party A,B: c0=0, y0=x0 *)
	iteri_dep folder init n.
Check zn_to_z2.

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

(* Here we expect `i < n+1` *)
Definition acc_correct i (acc: i.+1.-tuple ((B * B) * (B * B))) :=
  let acc := rev acc in
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
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
  let acc := rev zn_to_z2 in
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  decimal_eq n cas cbs yas ybs.
Proof.
have [] // :=
  iteri_dep_ind (init:=[tuple ((0, 0), (xas`_0, xbs`_0))]) folder_correctP _ n.
by rewrite /acc_correct /= !addr0 decimal_eq0.
Qed.

End zn_to_z2_ntuple.
