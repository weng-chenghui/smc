From mathcomp Require Import all_ssreflect all_algebra ring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section fintype_extra.
Lemma bump0 n : bump 0 n = n.+1. Proof. by []. Qed.
End fintype_extra.

Section seq_extra.
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
End seq_extra.

Import GRing.Theory Num.Theory.

Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").

Local Open Scope ring_scope.

Fixpoint zipWith  (A B C: Type) (fn : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
	match l1, l2 with
	| [::], _ => [::]
	| _, [::] => [::]
	| a1 :: tl1, a2 :: tl2 => fn a1 a2 :: (zipWith fn tl1 tl2)
	end.

Lemma length_cons :
  forall (A : Type) (a : A) (l : list A),
  length (a :: l) = S (length l).
Proof.
move=> A a l.
rewrite //=.
Qed.

Lemma zipWith_recl  (A B C: Type) (f : A -> B -> C)  (a : A) (b : B) (l1 : list A) (l2 : list B):
  zipWith f (a :: l1) (b :: l2) = f a b :: zipWith f l1 l2.
Proof.
by rewrite /=.
Qed.

Lemma zipWith_nil_l  (A B C: Type) (f : A -> B -> C)  (lr : list B):
  zipWith f [::] lr = [::].
Proof.
by rewrite /=.
Qed.

Lemma zipWith_nil_r (A B C: Type) (f : A -> B -> C)  (ll : list A):
  zipWith f ll [::] = [::].
Proof.
rewrite /=.
elim: ll => [|??].
  by [].
move=>H.
rewrite -H //=.
Qed.

Lemma zipWith_nil (A B C: Type) (f : A -> B -> C):
  zipWith f [::] [::] = [::].
Proof.
by rewrite /=.
Qed.
  

Section smc_scalar_product.

Variable Z:ringType.

Definition dotproduct (la lb: list Z) : Z :=
	foldl +%R 0 (zipWith *%R la lb).


(*

  The previous version `add`:

    map (fun a => a.1 + a.2) (zip la lb).

  Need extra hypothesis for their length,
  and thus all related proofs need those hypothesis.

  Therefore, we use this fixpoint version to save the extra work.
*)

Fixpoint add (la lb: list Z) : list Z :=
    match la, lb with
    |[::], _ => lb
    |_, [::] => la
    |a::la, b::lb => a+b :: add la lb
    end.

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
  (sp Xa Xb).1 + (sp Xa Xb).2 = Xa `* Xb.

End smc_scalar_product.

Notation "la '`*' lb" := (dotproduct la lb).
Notation "la '`+' lb" := (add la lb).

(* Note that some rings cannot be computed.
   But this one is okay:
 *)
Eval compute in (demo_Alice3_Bob2 [ringType of int]).

Section smc_scalar_product_facts.

(* to prove, need com *)
Variable R:comRingType.


(*
TODO: Lemma for:
foldl (fun sum : R => [eta +%R sum]) 0 [::] = foldl (fun sum : R => [eta +%R sum]) 0 [::]

BigOp instead of foldling.
*)


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
elim: aa bb cc z 0=> [| a aa IH] [| b bb] [|c cc] z z2 //=.
rewrite -!dot_productE //=.
ring.
rewrite -!dot_productE //=.
ring.
rewrite IH //.
rewrite -!dot_productE //=.
ring.
Qed.

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


Definition step2_1 (sp: SMC B) (ci xi: (B * B)) : (B * B) :=
  sp [:: ci.1; xi.1; xi.1] [:: xi.2; ci.2; xi.2].

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
  
(* Step 2 for two party. *)
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
Proof.
rewrite /step2_2_correct.
simpl.
split.
ring.
ring.
Qed.

Section zn_to_z2_ntuple.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).


Let W {n} (i : 'I_n) : 'I_n.+1 := widen_ord (@leqnSn _) i.
Let S {n} (i : 'I_n) : 'I_n.+1 := lift ord0 i.
(* Memo: Use Let: things disappear after closing the section. *)

Notation "t '!_' i" := (tnth t i) (at level 10). (* lv9: no parenthesis; so lv10*)

Hypothesis xan : xas!_(ord_max) = false.
Hypothesis xbn : xbs!_(ord_max) = false.
Hypothesis sps_is_sp : forall i, is_scalar_product (sps !_ i).

(*acc: carry-bit Alice, Bob will receive; results Alice, bob will receive*)
Definition zn_to_z2_folder (acc: list ((B * B) * (B * B))) (i: 'I_n):
  list ((B * B) * (B * B)) :=
	let '((ca, cb), _) := head ((0,0),(0,0)) acc in
	let sp := tnth sps i in
	let i_ := W i in (* make it can use the implicit argument *)
	let i' := S i in
	let xa := xas !_ i_ in
	let xa' := xas !_ i' in
	let xb := xbs !_ i_ in
	let xb' := xbs !_ i' in
	step2_2 (step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb') :: acc.

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := [:: ((0, 0), (tnth xas 0, tnth xbs 0))] in  (* For party A,B: c0=0, y0=x0 *)
	foldl zn_to_z2_folder init (ord_tuple n). 

(*acc_correct acc (W i) -> acc_correct (zn_to_z2_folder acc i) (S i).*)
Lemma foldl_ord_tuple (A: Type) (f: A -> 'I_n -> A) (P: A -> 'I_n.+1 -> Prop) (init: A) :
  (forall acc i, P acc (W i) -> P (f acc i) (S i))->
  P init ord0 -> P (foldl f init (ord_tuple n)) ord_max.
Proof.
move=>H.
pose i:=n.
have Hi:(i <= n)%N. done.
have Hn:(n-i<n.+1)%N. rewrite subnn. done.
have ->: ord0 = Ordinal Hn.
apply /val_inj.
by rewrite /= subnn.
have ->: ord_tuple n = drop (n-i) (ord_tuple n) :> list _.
by rewrite /= subnn drop0.
elim: i Hi Hn init => [|i IH] Hi Hn init Hinit.
rewrite /=.
rewrite subn0 drop_oversize //=.
have ->//: ord_max = Ordinal Hn.
apply /val_inj.
by rewrite /= subn0.
by rewrite size_enum_ord.
have Hi': (n - i.+1 < n)%N. admit.
move /(_ init (Ordinal Hi')) in H.
rewrite (_:W (Ordinal Hi') = (Ordinal Hn)) in H;last by apply /val_inj.
have Hn': (n - i < n.+1)%N. admit.
rewrite (_: S (Ordinal Hi') = Ordinal Hn') in H;last first.
apply /val_inj.
rewrite /= bump0.
by rewrite subnS prednK // subn_gt0.
move:(IH (ltnW Hi) _ _ (H Hinit)).
have ->: drop (n - i.+1) (ord_tuple n) = Ordinal Hi' :: drop (n - i) (ord_tuple n).admit.
apply. 


Let Wi {n} {m : 'I_n} : 'I_m -> 'I_n := @widen_ord _ n (ltnW (ltn_ord m)).

Definition carry_correct (ca cb ca' cb' xa xb : B) :=
  ((ca + cb)%R * 2 + (xa + ca' + (xb + cb'))%R = (ca' + cb')%R + (xa + xb))%N.

Definition decimal_eq (cas cbs yas ybs : list B) (i: 'I_n.+1) := 
  ((cas `_ 0 + cbs `_ 0)%R * 2 ^ i +
   \sum_(j < i) (yas `_ j.+1 + ybs `_ j.+1)%R * 2 ^ (i-j.+1) =
     \sum_(j < i) ((xas !_ (Wi j) : nat) + xbs !_ (Wi j)) * 2 ^ j)%N.

Definition acc_correct (acc: list ((B * B) * (B * B))) (i: 'I_n.+1) :=
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  size acc = i.+1
  /\ (rev cas)`_0 = 0  (* i.e. cas`_i = 0 *)
  /\ (rev cbs)`_0 = 0
  /\ rev yas = take i.+1 xas `+ rev cas
  /\ rev ybs = take i.+1 xbs `+ rev cbs
  /\ decimal_eq cas cbs yas ybs i.

Definition step2_correct (acc: list ((B * B) * (B * B))) (i: 'I_n) :=
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  let i_ := W i in
  let sp := sps !_ i in
  let ca := (rev cas) `_ i_ in
  let cb := (rev cbs) `_ i_ in
  let xa := (xas `_ i_) in
  let xb := (xbs `_ i_) in
  acc_correct acc i_ -> @step2_1_correct sp (ca, cb) (xa, xb).

Lemma rev_add (R : ringType) (s t : seq R) :
  size s = size t -> rev (s `+ t) = rev s `+ rev t.
Proof. by move=> ?; rewrite /add -map_rev rev_zip. Qed.

Lemma nth_add' (R : ringType) (s t : seq R) (i : nat) :
  (i < minn (size s) (size t))%N -> (s `+ t) `_ i = s `_ i + t `_ i.
Proof.
move=> ist.
rewrite /add (nth_map (GRing.zero _)); last by rewrite size_zip.
by rewrite nth_zip' //.
Qed.

Lemma nth_add (R : ringType) (s t : seq R) (i : nat) :
  size s = size t -> (s `+ t) `_ i = s `_ i + t `_ i.
Proof.
move=> st.
have /orP [zst|] := leqVgt (size (zip s t)) i; last first.
  by rewrite size_zip; exact: nth_add'.
rewrite !nth_default ?addr0 //.
- by move: zst; rewrite size_zip st minnn.
- by move: zst; rewrite size_zip -st minnn.
- by rewrite size_map.
Qed.

Lemma add_cat (s1 s2 t1 t2 : seq B) :
  size s1 = size t1 ->
  add (s1 ++ s2) (t1 ++ t2) = add s1 t1 ++ add s2 t2.
Proof. by move=> Hsize; rewrite /add zip_cat // map_cat. Qed.

Lemma take1 (s: seq B):
  (size s > 0)%N -> take 1 s = [::head 0 s].
Proof.
by case: s => [| ? []].
Qed.

Lemma zn_to_z2_folder_correct acc i:
  acc_correct acc (W i) -> acc_correct (zn_to_z2_folder acc i) (S i).
Proof.
move=> []. 
case Hacc: acc => [|[[cai_ cbi_] [ya yb]] acc'] //.
rewrite -Hacc.
move=> Hsz [Hca [Hcb [Hyas [Hybs Hdec]]]].
rewrite /zn_to_z2_folder {1}Hacc /=.
have:=step2_1_correctP (cai_, cbi_) (xas !_ (W i), xbs !_ (W i)) (sps_is_sp i).
rewrite /step2_1_correct /=. 
destruct step2_1 as [tai_ tbi_].
simpl.
move=> Htai_tbi.
have Hbump : bump 0 i = (W i).+1 by [].
rewrite /acc_correct /= Hsz.
split => //.
rewrite Hbump.
rewrite (take_nth 0 (s:=xas)) ? size_tuple ? ltnS //=.
rewrite (take_nth 0 (s:=xbs)) ? size_tuple ? ltnS //=.
rewrite -!cats1 -!(cat1s _ (unzip1 _)) -!(cat1s _ (unzip2 _)).
rewrite !(add_cat,rev_cat) //;
  try by rewrite size_takel !(size_tuple,size_rev,size_map) // ltnS ltnW.
rewrite nth_cat size_rev !size_map {1}Hacc Hca /=.
rewrite nth_cat size_rev !size_map {1}Hacc Hcb /=.
rewrite Hyas Hybs !rev1 !(tnth_nth 0) /=.
have Hcc : carry_correct (cai_ * xas`_i + tai_) (cbi_ * xbs`_i + tbi_)
    (unzip1 (unzip1 acc))`_0 (unzip2 (unzip1 acc))`_0 xas`_i xbs`_i.
  rewrite /carry_correct Hacc /=.
  rewrite -(addrC tbi_) addrA -(addrA _ tai_) Htai_tbi.
  rewrite /dotproduct /=. (* calc dotproduct*)
  rewrite !(tnth_nth 0) /=.
  clear.
  by move: cai_ (xas`_i) (xbs`_i) cbi_ => [] [] [] [].
do !split => //=.
rewrite /carry_correct in Hcc.
rewrite /decimal_eq big_ord_recl /= subSS subn0.
under eq_bigr do rewrite bump0 subSS.
rewrite [RHS]big_ord_recr /=.
under [in RHS]eq_bigr do rewrite !(tnth_nth 0) /=.
move: Hdec.
rewrite /decimal_eq /=.
under [in RHS]eq_bigr do rewrite !(tnth_nth 0) /=.
move <-.
rewrite addnA [RHS]addnC addnA.
congr addn.
rewrite expnS mulnA -!mulnDl.
congr muln.
rewrite !(tnth_nth 0) /= [RHS]addnC -Hcc.
congr addn.
move: Hsz Hyas Hybs; clear.
case: acc => [| [[ca cb] [ya yb]] acc] //= => [] [] Hsz.
rewrite !rev_cons -!cats1 -addn1 !takeD.
rewrite !take1 ?size_drop ?subn_gt0 ?size_tuple 1?ltnW ?ltnS //.
rewrite -!nth0 !nth_drop addn0.
rewrite /add zip_cat; last first.
  by rewrite size_rev !size_map Hsz size_takel // size_tuple ltnW //ltnW //ltnS.
rewrite map_cat /= 2!cats1 => /rcons_inj [] _ ->.
rewrite zip_cat; last first.
  by rewrite size_rev !size_map Hsz size_takel // size_tuple ltnW //ltnW //ltnS.
rewrite map_cat /= 2!cats1 => /rcons_inj [] _ ->.
by rewrite !addrA.
Qed.

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
