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
	map (fun a => a.1 + a.2) (zip la lb).

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

(* NOTE: this is not rewritable (yet). *)
Lemma zn_to_z2_step2_1_correct (sp: SMC B) (ci xi: B * B) :
	is_scalar_product sp ->
	let alice_input := [:: ci.1; xi.1; xi.1] in
	let bob_input := [:: xi.2; ci.2; xi.2] in
	let (tai, tbi) := zn_to_z2_step2_1 sp ci xi in
	tai + tbi = alice_input `* bob_input .
Proof.
apply.
Qed.

Lemma zn_to_z2_step2_1_correct' (sp: SMC B) (ci xi: B * B) :
	is_scalar_product sp ->
	let alice_input := [:: ci.1; xi.1; xi.1] in
	let bob_input := [:: xi.2; ci.2; xi.2] in
	exists tai tbi, (tai, tbi) = zn_to_z2_step2_1 sp ci xi /\
	tai + tbi = alice_input `* bob_input .
Proof.
Admitted.

Section zn_to_z2_ntuple.

Variable (n: nat) (sps: n.-tuple (SMC B)) (xas xbs: n.+1.-tuple B).

Let W {n} (i : 'I_n) : 'I_n.+1 := widen_ord (@leqnSn _) i.
Let S {n} (i : 'I_n) : 'I_n.+1 := lift ord0 i.
(* Memo: Use Let: things disappear after closing the section. *)

Notation "t '!_' i" := (tnth t i) (at level 10). (* lv9: no parenthesis; so lv10*)

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
	let '(cs, yab) := zn_to_z2_step2_2 (zn_to_z2_step2_1 sp (ca, cb) (xa, xb)) (ca, cb) (xa, xb) (xa', xb') in
	((cs, yab) :: acc).

(* xs[0] = lowest bit *)
Definition zn_to_z2 :=
	let init := [:: ((0, 0), (tnth xas 0, tnth xbs 0))] in  (* For party A,B: c0=0, y0=x0 *)
	foldl zn_to_z2_folder init (ord_tuple n). 

Let Wi {n} {m : 'I_n} : 'I_m.+1 -> 'I_n := @widen_ord _ n (ltn_ord m).

Definition acc_correct (acc: list ((B * B) * (B * B))) (i: 'I_n.+1) :=
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  size acc = i.+1 /\ rev yas = take i.+1 xas `+ rev cas /\
  rev ybs = take i.+1 xbs `+ rev cbs.

Definition acc_correct' (acc: list ((B * B) * (B * B))) (i: 'I_n.+1) :=
  let cas := unzip1 (unzip1 acc) in
  let cbs := unzip2 (unzip1 acc) in
  let yas := unzip1 (unzip2 acc) in
  let ybs := unzip2 (unzip2 acc) in
  size acc = i.+1 /\ rev yas = take i.+1 xas `+ rev cas /\
  rev ybs = take i.+1 xbs `+ rev cbs /\
  ((cas `_ 0 + cbs `_ 0)%R * 2 ^ i.+1 +
   \sum_(j < i.+1) (yas `_ j + ybs `_ j)%R * 2 ^ (i-j) =
   \sum_(j < i.+1) ((xas !_ (Wi j) : nat) + xbs !_ (Wi j)) * 2 ^ j)%nat.

Search rev nth in seq.

Lemma add_cat (s1 s2 t1 t2 : seq B) :
  size s1 = size t1 ->
  add (s1 ++ s2) (t1 ++ t2) = add s1 t1 ++ add s2 t2.
Proof. by move=> Hsize; rewrite /add zip_cat // map_cat. Qed.

Lemma zn_to_z2_folder_correct acc i:
	is_scalar_product (sps !_ i) -> acc_correct acc (W i) -> acc_correct (zn_to_z2_folder acc i) (S i).
Proof.
move=> spi_is_scalar_product [].
case Hacc: acc => [|[[cai_ cbi_] [ya yb]] acc'] //.
rewrite -Hacc.
move=> Hsz [Hya Hyb].
rewrite /zn_to_z2_folder {1}Hacc /=.
have:=zn_to_z2_step2_1_correct (cai_, cbi_) (xas !_ (W i), xbs !_ (W i)) spi_is_scalar_product.
destruct zn_to_z2_step2_1 as [tai_ tbi_].
have:=zn_to_z2_step2_2_correct (tai_, tbi_) (cai_, cbi_) (xas !_ (W i), xbs !_ (W i)) (xas !_ (S i), xbs !_ (S i)).
simpl.
move=> _ Htai_tbi.
have Hbump : bump 0 i = (W i).+1 by [].
rewrite /acc_correct /= Hsz.
split => //.
rewrite Hbump.
rewrite (take_nth 0 (s:=xas)) ? size_tuple ? ltnS //=.
rewrite (take_nth 0 (s:=xbs)) ? size_tuple ? ltnS //=.
rewrite -!cats1 -!(cat1s _ (unzip1 _)) -!(cat1s _ (unzip2 _)).
rewrite !(add_cat,rev_cat) //;
  try by rewrite size_takel !(size_tuple,size_rev,size_map) // ltnS ltnW.
by rewrite Hya Hyb !(tnth_nth 0).
Qed.


Lemma zn_to_z2_folder_correct' acc i:
	is_scalar_product (sps !_ i) -> acc_correct' acc (W i) -> acc_correct' (zn_to_z2_folder acc i) (S i).
Proof.
move=> spi_is_scalar_product [].
case Hacc: acc => [|[[cai_ cbi_] [ya yb]] acc'] //.
rewrite -Hacc.
move=> Hsz [Hya [Hyb Hdecimal_eq]].
rewrite /zn_to_z2_folder {1}Hacc /=.
have:=zn_to_z2_step2_1_correct (cai_, cbi_) (xas !_ (W i), xbs !_ (W i)) spi_is_scalar_product.
destruct zn_to_z2_step2_1 as [tai_ tbi_].
have:=zn_to_z2_step2_2_correct (tai_, tbi_) (cai_, cbi_) (xas !_ (W i), xbs !_ (W i)) (xas !_ (S i), xbs !_ (S i)).
simpl.
move=> _ Htai_tbi.
have Hbump : bump 0 i = (W i).+1 by [].
rewrite /acc_correct' /= Hsz.
split => //.
rewrite {1 2 3}Hbump. (* only use Hbump in occurence #1, #2 and #3. *)
rewrite (take_nth 0 (s:=xas)) ? size_tuple ? ltnS //=.
rewrite (take_nth 0 (s:=xbs)) ? size_tuple ? ltnS //=.
rewrite -!cats1 -!(cat1s _ (unzip1 _)) -!(cat1s _ (unzip2 _)).
rewrite !(add_cat,rev_cat) //;
  try by rewrite size_takel !(size_tuple,size_rev,size_map) // ltnS ltnW.
rewrite Hya Hyb !(tnth_nth 0).
split => //.
split => //.

rewrite big_ord_recl /=.
rewrite [RHS] big_ord_recr /=.
rewrite /= in Hdecimal_eq.
set sum1 := (X in _ = (X + _)%N).
set sum1' := (X in _ = X) in Hdecimal_eq.
have H1 : sum1 = sum1'.
  rewrite /sum1 /sum1'.
  apply: eq_bigr.
  move=>j _.
  congr ((_ + _) * _)%N ; congr (nat_of_bool (_ !_ _)); exact: val_inj.  (* congr: make pattern more simple when there is an eq; `;` do things in parallel.*)
  (*Set Printing  Coercions*)
  (*
		val_inj for "value injection"
		A ; B. means "execute A and for all subgoals apply B"
		A. B. means "execute A and for the first subgoal in line execute B" 
  *)
rewrite H1.
set sum2 := (\sum_(j<_) _)%N.
set sum2' := (\sum_(j<_) _)%N in Hdecimal_eq.
have H2 : sum2 = sum2'.
  rewrite /sum2 /sum2'.
  apply: eq_bigr.
  move=> i0 _.
  by congr (_ * _)%N.
rewrite H2.
rewrite -Hdecimal_eq.
rewrite [in RHS] addnAC.
rewrite !addnA.
congr (_ + _)%N.
rewrite subn0.
rewrite Hacc /=.
destruct n as [|n'] => /=.
  destruct i as [i Hi] => /=.
  destruct i as [|i] => //=.
destruct i as [i Hi] => /=.
destruct i as [|i] => /=.
  destruct n' => /=.
  rewrite (_:xas `_(bump 0 0) = xas `_1%N) //.
  rewrite (_:xbs `_(bump 0 0) = xbs `_1%N) //.
  rewrite (_:(2 ^ bump 0 0 = 2)%N) //.
  rewrite (_:xas !_ (Wi ord_max) = xas `_1%N);last first.
    by rewrite (tnth_nth 0) //.
  rewrite (_:xbs !_ (Wi ord_max) = xbs `_1%N);last first.
    by rewrite (tnth_nth 0) //.
	rewrite (_:xas `_0 = true);last admit.
	rewrite (_:xbs `_0 = true);last admit.
	rewrite (_:xas `_1 = true);last admit.
	rewrite (_:xbs `_1 = true);last admit.
	rewrite (_:cai_ = true);last admit.
	rewrite (_:cbi_ = true);last admit.
	rewrite (_:tai_ = true);last admit.
	rewrite (_:tbi_ = true);last admit.
	simpl.
	rewrite !mul0n.
  


  rewrite (_:xas `_1%N = false);last first.
    rewrite nth_default //.
	rewrite size_tuple //.

  rewrite (_:Wi ord_max = ord0%N) // ; last first.
  apply val_inj => /=.
  rewrite /bump /=.

  done.

destruct i as [i Hi] => /=.
destruct i as [|i] => /=.
(**
congr (_ * _)%N.
*)
 (**rewrite subn0*) 
(**rewrite subn0 and then congr (_ * _)%N*)

(**
set sum1 := (X in _ = X + _).
set sum1' := (X in _ = X) in Hdecimal_eq.
have H1 : sum1 = sum1'.
*)

rewrite 
Qed.

(*
rewrite [in X in X /\ _]Hbump. 
rewrite Hbump.
*)
Abort.
(*
rewrite (take_nth 0 (s:=xas)) ? size_tuple ? ltnS //=.
rewrite (take_nth 0 (s:=xbs)) ? size_tuple ? ltnS //=.
rewrite -!cats1 -!(cat1s _ (unzip1 _)) -!(cat1s _ (unzip2 _)).
rewrite !(add_cat,rev_cat) //;
  try by rewrite size_takel !(size_tuple,size_rev,size_map) // ltnS ltnW.
by rewrite Hya Hyb !(tnth_nth 0).
Qed.
*)

(*
Memo: use pose instead of let in proof.

pose xai_ := xas !_ i_.
pose xbi_ := xbs !_ i_.
pose xai' := xas !_ i'.
pose xbi' := xbs !_ i'.

*)

(* WRONG: leave acc' in the stack but not `case: acc'=>[[ca' cb'] ys']` to let it in the proof-context
   Result: when the stack needs ca' cb' and ys', the proof-context has no these symbols.

   Therefore: `case: acc'=>[[ca' cb'] ys']` to get those symbols.
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
