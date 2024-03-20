From mathcomp Require Import all_ssreflect all_algebra ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section fintype_extra.
Lemma bump0 n : bump 0 n = n.+1. Proof. by []. Qed.
End fintype_extra.

Section seq_extra.

Lemma unzip1_rev A C (s : seq (A*C)) : unzip1 (rev s) = rev (unzip1 s).
Proof. exact: map_rev. Qed.

Lemma unzip2_rev A C (s : seq (A*C)) : unzip2 (rev s) = rev (unzip2 s).
Proof. exact: map_rev. Qed.

Lemma rev1 [T : Type] (x : T) : rev [:: x] = [:: x].
Proof. by []. Qed.

(* should be split int size_seq0 and size_seqS *)
Lemma size_seq1 [T : Type] (s : seq T) :
  size s = 1%N -> exists t, s = [:: t].
Proof.
case: s => //= a s.
move/succn_inj/size0nil->.
by exists a.
Qed.

Lemma take_zip (S T : Type) (s : seq S) (t : seq T) n :
  take n (zip s t) = zip (take n s) (take n t).
Proof. by elim: n s t => [|n IH] [|s1 s] [|t1 t] //=; rewrite IH. Qed.

Lemma nth_zip' (S T : Type) (x : S) (y : T) s t i :
  i < minn (size s) (size t) ->
  nth (x, y) (zip s t) i = (nth x s i, nth y t i).
Proof.
move=> ?.
rewrite -(@nth_take (minn (size s) (size t))) //.
rewrite take_zip nth_zip; last first.
  by rewrite !size_take_min minnAC -[RHS]minnA !minnn.
by rewrite !nth_take.
Qed.

Lemma nth_unzip1 (S T : Type) x y (s : seq (S * T)) i :
  nth x (unzip1 s) i = (nth (x,y) s i).1.
Proof.
have /orP [H|?] := leqVgt (size s) i; last by rewrite (nth_map (x,y)).
by rewrite !nth_default ?size_map.
Qed.

Lemma nth_unzip2 (S T : Type) x y (s : seq (S * T)) i :
  nth y (unzip2 s) i = (nth (x,y) s i).2.
Proof.
have /orP [H|?] := leqVgt (size s) i; last by rewrite (nth_map (x,y)).
by rewrite !nth_default ?size_map.
Qed.

Fixpoint zipWith  (A B C: Type) (fn : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
	match l1, l2 with
	| [::], _ => [::]
	| _, [::] => [::]
	| a1 :: tl1, a2 :: tl2 => fn a1 a2 :: (zipWith fn tl1 tl2)
	end.

Lemma zipWithE (A B : Type) (f : A -> A -> B) (xx yy : list A) :
  zipWith f xx yy = [seq f xy.1 xy.2 | xy <- zip xx yy].
Proof.
move: yy; elim: xx; first by case.
by move=> x xx IH; case=> //= y yy; rewrite IH.
Qed.

Lemma size_zipWith {A B: Type} (fn : A -> A -> B) (l1 : list A) (l2 : list A) :
  size (zipWith fn l1 l2) = minn (size l1) (size l2).
Proof. by rewrite zipWithE size_map size_zip. Qed.

Lemma big_zipWith_cat
  [R : Type] [idx : R] (op : Monoid.com_law idx) [I : Type] (r1 r2 : seq I) 
  (P Q : pred I) (F : I -> R) :
  size [seq i <- r1 | P i] = size [seq i <- r2 | Q i] ->
  \big[op/idx]_(i <- zipWith op [seq F i | i <- r1 & P i] [seq F i | i <- r2 & Q i]) i =
    op (\big[op/idx]_(i <- r1 | P i) F i) (\big[op/idx]_(i <- r2 | Q i) F i).
Proof.
move=> H.
rewrite zipWithE big_map big_split.
rewrite -(big_map fst xpredT idfun) /= -/(unzip1 _) unzip1_zip ?size_map ?H //.
rewrite -(big_map snd xpredT idfun) /= -/(unzip2 _) unzip2_zip ?size_map ?H //.
by rewrite !big_map !big_filter.
Qed.

Arguments big_zipWith_cat [R idx] op [I] r1 r2 P Q F.

Lemma big_zipWith_cat'
  [R : Type] [idx : R] (op : Monoid.com_law idx) (r1 r2 : seq R) :
  size r1 = size r2 ->
  \big[op/idx]_(i <- zipWith op r1 r2) i =
    op (\big[op/idx]_(i <- r1) i) (\big[op/idx]_(i <- r2) i).
Proof.
have:= (big_zipWith_cat op r1 r2 xpredT xpredT idfun).
by rewrite /= !filter_predT !map_id; exact.
Qed.

Arguments big_zipWith_cat' [R idx] op r1 r2.

Lemma zipWithC (A B : Type) (f : A -> A -> B) (aa bb : seq A) :
  (forall a b, f a b = f b a) ->
  zipWith f aa bb = zipWith f bb aa.
Proof.  
move: bb; elim: aa=> //=; first by case.
by move=> a aa IH; case=> //= b bb H; rewrite H (IH _ H).
Qed.

Arguments zipWithC [A B] f.

Variable n:nat.

Lemma foldl_ord_tuple (A: Type) (f: A -> 'I_n -> A) (P: A -> nat -> Prop) (init: A) :
  (forall acc (i:'I_n), P acc i -> P (f acc i) i.+1 )->
  P init 0%N -> P (foldl f init (ord_tuple n)) n.
Proof.
move=>H.
pose i:=n.
have Hi:(i <= n)%N by [].
have ->: (0 = n - i)%N by rewrite subnn.
have ->: ord_tuple n = drop (n-i) (ord_tuple n) :> list _.
  by rewrite /= subnn drop0.
elim: i Hi init => [|i IH] Hi init Hinit.
  rewrite /=.
  rewrite subn0 drop_oversize //=.
    by rewrite subn0 in Hinit.
  by rewrite size_enum_ord.
have Hi': (n - i.+1 < n)%N by rewrite (_ : i = Ordinal Hi) // rev_ord_proof.
move /(_ init (Ordinal Hi')) in H.
have Hn': (n - i < n.+1)%N by rewrite ltnS leq_subr.
rewrite (_: (Ordinal Hi').+1 = n - i)%N in H;last first.
  by rewrite /= subnS prednK // subn_gt0.
move:(IH (ltnW Hi) _ (H Hinit)).
suff: drop (n - i.+1) (ord_tuple n) = Ordinal Hi' :: drop (n - i) (ord_tuple n).
  by move ->.
rewrite -{1}(cat_take_drop (n-i.+1) (ord_tuple n)).
rewrite drop_size_cat; last by rewrite size_takel // size_tuple leq_subr.
rewrite (drop_nth (Ordinal Hi')) ?size_tuple //.
rewrite {3}subnS prednK ?subn_gt0 //.
by rewrite {2}(_ : (n-i.+1)%N = Ordinal Hi') // -tnth_nth tnth_ord_tuple.
Qed.

End seq_extra.

Import GRing.Theory Num.Theory.

Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").

Local Open Scope ring_scope.


(*
    Du, Wenliang, and Zhĳun, Zhan. "A practical approach to solve Secure Multi-party Computation problems." . In Proceedings of the 2002 Workshop on New Security Paradigms (pp. 127–135). Association for Computing Machinery, 2002.

    https://doi.org/10.1145/844102.844125
*)

Section smc_scalar_product.

Variable R:ringType.

Definition dotproduct (la lb: list R) : R :=
	foldl +%R 0 (zipWith *%R la lb).

(*

  The previous version `add`:

    map (fun a => a.1 + a.2) (zip la lb).

  Need extra hypothesis for their length,
  and thus all related proofs need those hypothesis.

  Therefore, we use this fixpoint version to save the extra work.
*)

Fixpoint add (la lb: list R) : list R :=
    match la, lb with
    |[::], _ => lb
    |_, [::] => la
    |a::la, b::lb => a+b :: add la lb
    end.

Notation "la '`*' lb" := (dotproduct la lb).
Notation "la '`+' lb" := (add la lb).

Lemma add_cat (s1 s2 t1 t2 : seq R) :
  size s1 = size t1 ->
  add (s1 ++ s2) (t1 ++ t2) = add s1 t1 ++ add s2 t2.
Proof. elim: s1 t1 => [|a aa IH] [|b bb] //= [Hs]. by rewrite IH. Qed.

Lemma rev_add (s t : seq R) :
  size s = size t -> rev (s `+ t) = rev s `+ rev t.
Proof.
rewrite -(revK s) -(revK t) !(size_rev (rev _)).
elim: (rev s) (rev t) => [|a aa IH] [|b bb] //= [Hs].
by rewrite !rev_cons -!cats1 add_cat ?size_rev //= !cats1 !rev_rcons IH.
Qed.

Lemma take1 (s: seq R):
  (size s > 0)%N -> take 1 s = [::head 0 s].
Proof.
by case: s => [| ? []].
Qed.

Definition commodity_rb  (Ra Rb: list R) (ra: R): R :=
	(Ra `* Rb) - ra.

(* Owned: genereated in or received by Alice *)
Record alice_owned :=
  AliceOwned {
    Ra  : seq R;
    Xa  : seq R;
    X'b : seq R;
    ra  : R;
    recv_t   : R;
    ya  : R;
  }.

(* Owned: genereated in or received by Bob *)
Record bob_owned :=
  BobOwned {
    Rb  : seq R;
    Xb  : seq R;
    X'a : seq R;
    rb  : R;
    send_t : R;
    yb  : R;
  }.

(* Put this definition in the record will make every time we have the record,
   we need to provide the hypothesis,
   so temporarily separate it from the record.
 *)
Definition is_alice_owned (ao: alice_owned) :=
  ya ao = recv_t ao - (Ra ao `* X'b ao) + ra ao.

Definition is_bob_owned (bo: bob_owned) :=
  send_t bo = (Xb bo `* X'a bo) + rb bo - yb bo.


Definition scalar_product (Ra Rb: list R) (ra rb yb: R) (Xa Xb: list R): (R * R * (alice_owned * bob_owned)) :=
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

Definition SMC := list R -> list R -> (R * R * (alice_owned * bob_owned)).

Definition is_scalar_product (sp: SMC) :=
  forall(Xa Xb: list R),
  (sp Xa Xb).1.1 + (sp Xa Xb).1.2 = Xa `* Xb.

End smc_scalar_product.

Eval compute in (demo_Alice3_Bob2 [ringType of int]).

Notation "la '`*' lb" := (dotproduct la lb).
Notation "la '`+' lb" := (add la lb).

Section smc_scalar_product_facts.

(* to prove, need comRingType, not just ringtype *)
Variable R:comRingType.

Lemma dot_productC (aa bb : list R) : aa `* bb = bb `* aa.
Proof.
rewrite /dotproduct.
elim: aa bb 0 => [| a aa IH] [| b bb] z //=.
by rewrite mulrC.
Qed.

Lemma dot_productE (aa bb: list R) (z: R): z + aa `* bb = foldl +%R z (zipWith *%R aa bb).
Proof.
rewrite /dotproduct -[in RHS](addr0 z).
elim: aa bb z 0=> [| a aa IH] [| b bb] z z2 //=.
by rewrite IH addrA.
Qed.  

Lemma dot_productDr (aa bb cc : list R) :
  aa `* (bb `+ cc) = aa `* bb + aa `* cc.
Proof.
rewrite /dotproduct.
set z:={1 2}0.
rewrite -{1}(addr0 z).
elim: aa bb cc z 0 => [| a aa IH] [| b bb] [|c cc] z z2 //=;
  rewrite ?IH -!dot_productE //=; ring.
Qed.

Lemma scalar_product_correct (Ra Rb : list R) (ra yb : R) :
  let rb := commodity_rb Ra Rb ra in
  is_scalar_product (scalar_product Ra Rb ra rb yb).
Proof.
move=>/=Xa Xb/=.
rewrite /commodity_rb.
rewrite !dot_productDr.
rewrite (dot_productC Xb Xa).
rewrite (dot_productC Xb Ra).
ring.
Qed.

End smc_scalar_product_facts.

(*  
    Shen, Chih-Hao, Justin, Zhan, Tsan-Sheng, Hsu, Churn-Jung, Liau, and Da-Wei, Wang. "Scalar-product based secure two-party computation." . In 2008 IEEE International Conference on Granular Computing (pp. 556-561).2008.

    http://dx.doi.org/10.1109/GRC.2008.4664775
*)
Section zn_to_z2.

Let B := bool_comRingType.

Definition step2_1 (sp: SMC B) (ci xi: (B * B)) : (B * B) :=
  (sp [:: ci.1; xi.1; xi.1] [:: xi.2; ci.2; xi.2]).1.

Definition step2_1_correct (sp: SMC B) (ci xi: B * B) :=
    let alice_input := [:: ci.1; xi.1; xi.1] in
    let bob_input := [:: xi.2; ci.2; xi.2] in
    let t := step2_1 sp ci xi in
    t.1 + t.2 = alice_input `* bob_input .

Lemma step2_1_correctP (sp: SMC B) (ci xi: B * B) :
	is_scalar_product sp ->
        step2_1_correct sp ci xi.
Proof.
move=>Hsp.
rewrite /step2_1_correct.
rewrite /step2_1.
by rewrite Hsp.
Qed.

Definition step2_2 (ti: B * B) (ci xi xi' : B * B) :
  (B * B) * (B * B) :=
	let cai' := (ci.1 * xi.1 + ti.1) in
	let cbi' := (ci.2 * xi.2 + ti.2) in
	let yai' := (xi'.1 + cai') in
	let ybi' := (xi'.2 + cbi') in
	((cai', cbi'), (yai', ybi')).

Definition step2_2_correct (ti: B * B) (ci xi xi' : B * B) :=
    let (c, y) := step2_2 ti ci xi xi' in
    y.1 = c.1 + xi'.1 /\ y.2 = c.2 + xi'.2.

Lemma step2_2_correctP (ti: B * B) (ci xi xi' : B * B):
    step2_2_correct ti ci xi xi'.
Proof. rewrite /step2_2_correct /=; split; ring. Qed.

End zn_to_z2.

Section zn_to_z2_ntuple.

Let B := bool_comRingType.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).


Let W {n} (i : 'I_n) : 'I_n.+1 := widen_ord (@leqnSn _) i.
Let S {n} (i : 'I_n) : 'I_n.+1 := lift ord0 i.
Let Wi {n} {m : 'I_n} : 'I_m -> 'I_n := @widen_ord _ n (ltnW (ltn_ord m)).

Notation "t '!_' i" := (tnth t i) (at level 10). (* lv9: no parenthesis; so lv10*)

Hypothesis xan : xas!_(ord_max) = false.
Hypothesis xbn : xbs!_(ord_max) = false.
Hypothesis sps_is_sp : forall i, is_scalar_product (sps !_ i).

(*acc: carry-bit Alice, Bob will receive; results Alice, bob will receive*)
Definition folder (acc: list ((B * B) * (B * B))) (i: 'I_n):
  list ((B * B) * (B * B)) :=
	let '((ca, cb), _) := head ((0,0),(0,0)) acc in
	let sp := tnth sps i in
	let i_ := W i in
	let i' := S i in
	let xa := xas !_ i_ in
	let xa' := xas !_ i' in
	let xb := xbs !_ i_ in
	let xb' := xbs !_ i' in
	step2_2 (step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb') :: acc.

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := [:: ((0, 0), (tnth xas 0, tnth xbs 0))] in  (* For party A,B: c0=0, y0=x0 *)
	foldl folder init (ord_tuple n). 

Definition carry_correct (ca cb ca' cb' xa xb : B) :=
  ((ca + cb)%R * 2 + (xa + ca' + (xb + cb'))%R = (ca' + cb')%R + (xa + xb))%N.

(* Here we expect `i < n+1` *)
Definition decimal_eq (cas cbs yas ybs : list B) (i: nat) :=
  ((cas `_ i + cbs `_ i)%R * 2 ^ i +
   \sum_(j < i) (yas `_ j + ybs `_ j)%R * 2 ^ j == 
     \sum_(j < i) ((xas `_ j)%R + (xbs `_ j)%R) * 2 ^ j)%N.

Lemma decimal_eq0:
  decimal_eq [:: 0] [:: 0] [:: xas`_0] [:: xbs`_0] 0.
Proof. by rewrite /decimal_eq /= !big_ord0 addn0. Qed.

(* Here we expect `i < n+1` *)
Definition acc_correct (acc: list ((B * B) * (B * B))) (i: nat) :=
  let acc := rev acc in
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  [/\ size acc = i.+1,
    yas`_i = xas`_i + cas`_i,
    ybs`_i = xbs`_i + cbs`_i
    & decimal_eq cas cbs yas ybs i].


Lemma carry_correctP  cai_ cbi_ tai_ tbi_ (i : 'I_n) :
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

Lemma folder_correctP acc i:
  acc_correct acc (W i) -> acc_correct (folder acc i) (S i).
Proof.
move=> []. 
move Hacc: acc => [ |[[cai cbi] [ya yb]] acc'] //.
rewrite -Hacc size_rev.
move=> /= Hsz Hyas Hybs Hdec.
rewrite /folder {1}Hacc /= !(tnth_nth 0) /= bump0.
have := step2_1_correctP (cai, cbi) (xas`_i, xbs`_i) (sps_is_sp i).
rewrite /step2_1_correct /=. 
case: step2_1 => tai tbi /= Htai_tbi.
rewrite /acc_correct size_rev /= Hsz.
rewrite !(unzip1_rev,unzip2_rev) in Hyas Hybs Hdec *.
rewrite /step2_2 /=.
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
  decimal_eq cas cbs yas ybs n.
Proof.
have[|_//]:= foldl_ord_tuple folder_correctP (init:=[:: ((0, 0), (tnth xas 0, tnth xbs 0))]).
rewrite /acc_correct /= ?size_tuple //= !(tnth_nth 0) !addr0.
by rewrite decimal_eq0.
Qed.

End zn_to_z2_ntuple.

