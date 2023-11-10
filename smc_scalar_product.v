From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq tuple ssrfun.
Require Import ssrZ ZArith_ext uniq_tac ssrnat_ext.


(* Because I'm not sure which vector lib I should use,
   and because of all time I tried and spent on debugging dependant types:

   https://stackoverflow.com/questions/42302300/which-vector-library-to-use-in-coq

   I think current a simple list is sufficient.
*)
Fixpoint zipWith {A B: Type} (fn : A -> A -> B) (l1 : list A) (l2 : list A) : list B :=
	match l1, l2 with
	| [::], _ => [::]
	| _, [::] => [::]
	| a1 :: tl1, a2 :: tl2 => fn a1 a2 :: (zipWith fn tl1 tl2)
	end.

Fixpoint nth_element {A : Type} (n : nat) (l : list A) : option A :=
	match n, l with
	| 0%nat, h :: _ => Some h
	| S n', _ :: tl => nth_element n' tl
	| _, _ => None
	end.

Definition dotproduct (la lb: list Z) : Z :=
	foldl (fun sum current => sum + current) 0 (zipWith (fun a b => a * b) la lb).

Definition add (la lb: list Z) : list Z :=
	zipWith (fun a b => a + b) la lb.

Definition add_mod2 (la lb: list Z) : list Z :=
	zipWith (fun a b => (a + b) mod 2) la lb.

Reserved Notation "la '`*' lb" (at level 40, format "'[' la  `*  lb ']'").
Notation "la '`*' lb" := (dotproduct la lb).

Reserved Notation "la '`+' lb" (at level 50, format "'[' la  `+  lb ']'").
Notation "la '`+' lb" := (add la lb).

Reserved Notation "la '`+_2' lb" (at level 50, format "'[' la  `+_2  lb ']'").
Notation "la '`+_2' lb" := (add_mod2 la lb).

Eval compute in (([::1;2] `+ [::1;2;3]) `* [::-1;-2]).

(* ---- SMC Scalar-product ---- *)

(* Alice: get X'a and pass it to Bob *)
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

(* Scalar-product: (Xa1....Xan, Xb1...Xbn) |-> (ya, yb), where

	ya + yb = Xa * Xb

*)

Lemma dot_productC (aa bb : list Z) : aa `* bb = bb `* aa.
Admitted.

Lemma dot_productDr (aa bb cc : list Z) : aa `* (bb `+ cc) = aa `* bb + aa `* cc.
Admitted.

Lemma scalar_product_correct (Ra Rb : list Z) (ra yb : Z) (Xa Xb : list Z) :
  let rb := scalar_product_commidity_rb Ra Rb ra in
  let (ya, yb') := scalar_product Ra Rb ra rb yb Xa Xb in
  ya + yb' = Xa `* Xb.
Proof.
simpl.
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

Lemma demo_smc_scalar_product: fst demo_Alice3_Bob2 + snd demo_Alice3_Bob2 = 3 * 2.
Proof.
	compute.
	done.
Qed.

Definition SMC := list Z -> list Z -> (Z * Z).

Definition preset_sp (Ra Rb: list Z) (ra yb: Z): SMC :=
	scalar_product Ra Rb ra (scalar_product_commidity_rb Ra Rb ra) yb. 

(* Before we can have a Monad,
   use curried version to store the commodity, so use it like:

   (commodity Ra Rb ra yb) Xa Xb
*)
Definition commodity (Ra Rb: list Z) (ra yb: Z): SMC :=
	let rb := scalar_product_commidity_rb Ra Rb ra in
	scalar_product Ra Rb ra rb yb.

(* In most of protocols, there are more than one scalar-product,
   therefore more than one commodity is necessary.

   (A temporary workaround before we have RNG.)
   ()
*)
Fixpoint commodities (Ras Rbs: list (list Z)) (ras ybs: list Z): list SMC :=
	match Ras, Rbs, ras, ybs with
	| Ra :: tlRas, Rb :: tlRbs, ra :: tlras, yb :: tlybs =>
		commodity Ra Rb ra yb :: commodities tlRas tlRbs tlras tlybs
	| _, _, _, _ => [::]
	end.

(* Note before implementation of other protocols:

   1. Scalar-product's input is vector, but for other protocols,
      the input could be one single integer or other things,
	  it depends on the protocol design.

   2. How other protocols use scalar-product,
      and how they prepare the vector inputs to scalar-products,
	  depend on each protocol's design.

   3. The basic format of other protocol is that inputs held by Alice and Bob,
      no matter they are vectors or integers, in the form:

	      (InputA, InputB) |-> (OutputA, OutputB)

	  This law must keep:

	      InputA (non-SMC op) InputB = OutputA + OutputB
	  
	  So that in the protocol paper,

	      'Scalar-product-based Secure Two-party Computation',

	  The 'Input' is always described 'shared',
	  because Alice holds half of the Input, and Bob holds another half.
	  While this process in non-SMC will be:

	      Input -> Output

	  Now in the SMC world, one Input of unary operation becomes InputA and InputB.
	  In binary operation it becomes Input1A, Input1B, Input2A, Input2B, like in
	  the less_than protocol:

	      (Xa, Xb), (Ya, Yb) |-> (Za, Zb)
	
	  Where:
	  	
	      Za + Zb = {1, if (Xa + Xb) < (Ya + Yb); otherwise, 0 }

	  In this case, Alice holds Xa and Ya, while Bob holds Xb and Yb.
*)

(* ---- SMC Zn-to-Z2 ---- *)

(* Sidenote: maybe use int 32 from Seplog for this protocol. *)

(* Zn-to-Z2:

   (Alice: Xa, Bob: Xb) |-> (ya0...yak), (yb0...ybk), such that:
   Xa + Xb = X = (yk yk-1 ... y1 y0)2, where yi = (yia + yib) mod 2
*)

Definition zn_to_z2_step2_1 (sp: SMC) (cai cbi xai xbi: Z) : (Z * Z) :=
	sp [:: cai; xai; xai] [:: xbi; cbi; xbi].

(* Step 2 for two party. *)
Definition zn_to_z2_step2_2 (tai_tbi: Z * Z) (ci xi xi' : Z * Z) :
  (Z * Z) * (Z * Z) :=
	let (tai, tbi) := tai_tbi in
	let cai' := (ci.1 * xi.1 + tai) mod 2 in
	let cbi' := (ci.2 * xi.2 + tbi) mod 2 in
	let yai' := (xi'.1 + cai') mod 2 in
	let ybi' := (xi'.2 + cbi') mod 2 in
	((cai', cbi'), (yai', ybi')).


(* Shows it is correct if the `sp` fed to the step_2_1 is a SMC scalar-product. *)
(* Because SMC scalar-product its correctness also relies on all parameters from Ra to yb,
   parameters for both scalar_product and zn_to_z2_step2_1 are all listed.
*)
Lemma zn_to_z2_step2_1_correct (Ra Rb: list Z) (ra yb cai cbi xai xbi xai' xbi': Z) :
	let rb := scalar_product_commidity_rb Ra Rb ra in
	let alice_input := [:: cai; xai; xai] in
	let bob_input := [:: xbi; cbi; xbi] in
	let sp := scalar_product Ra Rb ra rb yb in
	let (tai, tbi) := zn_to_z2_step2_1 sp cai cbi xai xbi in
	tai + tbi = alice_input `* bob_input .
Proof. exact: scalar_product_correct. Qed.

(*TODO:


Because SMC ia a general (list Z -> list Z -> (Z * Z)) definition,
any SMC can be the `sp`. We must show what we feed to z2-to-zn, is SMC scalar-product,
so we can use the scalar_product_correct lemma.

----

Learnt:

Need to _bring_ proved properties and functions asssociated to the
new proof goal. For example, in `zn_to_z2_step2_1_correct`, 
the `sp` needs to be exactly the scalar_product function,
so previously proved things about the scalar_product function can be used.

So the proof bring more definitions and parameters than the proof target
function itself. For example, parameters for both scalar_product and zn_to_z2_step2_1
are all listed. Not just paramterrs for the proof target zn_to_z2_step2_1.

It is like proving it works in a context. While the context in this case is
all related parameters. When writing tests, there are some test environments
like mocks or configs, too.

*)

(*Memo:

    let (b, c) := f a in (b, c)

is a syntax sugar of:

    match f a with (b, c) => (b, c) end

This means you need to destruct on f a to finish the proof.

    destruct (f a)

So:

let (tai, tbi) :=
  sp [:: cai; xai; xai] [:: xbi; cbi; xbi] in
tai + tbi = [:: cai; xai; xai] `* [:: xbi; cbi; xbi]

Equals to:

match (sp [:: cai; xai; xai] [:: xbi; cbi; xbi]) with (tai + tbi = [:: cai; xai; xai] `* [:: xbi; cbi; xbi]) => (tai, tbi) end

*)

Definition zn_to_z2_folder (acc: list (Z * Z * (Z * Z))) (curr: (SMC * ((Z * Z) * (Z * Z)))): list (Z * Z * (Z * Z)) :=
	let '(sp, ((xa, xa'), (xb, xb'))) := curr in
	match head ((0, 0), (0, 0)) acc with (* get previous ca, cb and use them to calculate the new result, and push the new result to the acc list*)
	| (ca, cb, (ya, yb)) => zn_to_z2_step2_2 (zn_to_z2_step2_1 sp ca cb xa xb) (ca, cb) (xa, xb) (xa', xb') :: acc
	end.

(* Note: cannot put x0a and x0b in lists because they need to be the init vars specified in params.
   Taking them from the xas and xbs will make two cases: if the lists are empty, cannot taking them.
   So if we don't want to be bothered by using dependant type just for guaranteeing that we have x0a and x0b,
   putting them in the param list seems easier.
*)
(* result: ([ya_k...ya_0], [yb_k...yb_0]) *)
Definition zn_to_z2 (sps: list SMC) (x0a x0b: Z) (xas xbs: list Z): (list Z * list Z) :=
	(* What we need actually is: [:: (x2, x1); (x1, x0)] from high to low bits,
	   with overlapping element in each time we do foldering.
	   
	   So for example, `xas:6=1 1 0`, x0a: 0:

	   What we want:

	   [:: (x2=1, x1=1), (x1=1, x0=0)]

	   So we zip two lists, and because zip will drop extra part, we shift the first list by padding 0:

	       [:: x3=0 x2=1 x1=1 x0=0 ]   --> x3=0 is padded by cons
	       [:: x2=1 x1=1 x0=0 ]
	   zip ------------------------
	       [:: (x3,x2), (x2,x1), (x1, x0) ]
	   bhead
	       [:: (x2,x1), (x1, x0) ]
	*)
	let xas' := behead (zip (cons 0 xas) xas) in
	let xbs' := behead (zip (cons 0 xbs) xbs) in
	let init := [:: (0, 0, (x0a, x0b))] in  (* For party A,B: c0=0, y0=x0 *)
	let list_of_pairs := foldl zn_to_z2_folder init (zip sps (zip xas' xbs')) in
	let ya_bits := map (fun '(ca, cb, (ya, yb)) => ya) list_of_pairs in
	let yb_bits := map (fun '(ca, cb, (ya, yb)) => yb) list_of_pairs in
	(ya_bits, yb_bits).

(* Alice: 3 = (0 1 1); Bob: 2 = (0 1 0); A+B = 5 = (1 0 1) = zn-to-z2 5*)
(* Need 3 times of SMC scalar-product. *)
Definition demo_Alice3_Bob2_zn_to_z2 : (list Z * list Z) := 
	let sps := [:: 
		preset_sp [::9] [::8] 13 66;
		preset_sp [::32] [::43] 34 5;
		preset_sp [::57] [::40] 31 32
	] in
	let x0a := 1 in
	let x0b := 0 in
	let xas := [:: 0; 1; 1] in
	let xbs := [:: 0; 1; 0] in
	zn_to_z2 sps x0a x0b xas xbs.

Eval compute in (demo_Alice3_Bob2_zn_to_z2).

Lemma demo_smc_Alice3_Bob2_zn_to_z2: fst demo_Alice3_Bob2_zn_to_z2 `+_2 snd demo_Alice3_Bob2_zn_to_z2 = [:: 1; 0; 1].
Proof.
	compute.
	done.
Qed.
