From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq tuple.
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

Reserved Notation "la '`*' lb" (at level 50, format "'[' la  `*  lb ']'").
Notation "la '`*' lb" := (dotproduct la lb).

Reserved Notation "la '`+' lb" (at level 40, format "'[' la  `+  lb ']'").
Notation "la '`+' lb" := (add la lb).

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

Lemma demo_is_correct: fst demo_Alice3_Bob2 + snd demo_Alice3_Bob2 = 3 * 2.
Proof.
	compute.
	done.
Qed.

(* TODO: a real generic proof, not for just one case? *)

Definition SMC := list Z -> list Z -> (Z * Z).

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
(*
Fixpoint zn_to_z2 : (sps: list SMC): SMC :
	fold_left (fun sp => ) sps

*)

(* Step 2 for two party. *)
Definition zn_to_z2_step2 (sp: SMC) (cai cbi xai xbi xai' xbi': Z) : (Z * Z * Z *Z) :=
	let tai_tbi := sp [:: cai; xai; xai] [:: xbi; cbi; xbi] in
	let tai := fst tai_tbi in
	let tbi := snd tai_tbi in
	let cai' := (cai * xai + tai) mod 2 in
	let cbi' := (cbi * xbi + tbi) mod 2 in
	let yai' := (xai' + cai') mod 2 in
	let ybi' := (xbi' + cbi') mod 2 in
	(cai', cbi', yai', ybi').

(* TODO:  *)

Eval compute in (pairmap (fun prev curr => (curr, prev)) 0 [:: 4; 3; 2; 1]).

(* Note: cannot put x0a and x0b in lists because they need to be the init vars specified in params. *)
Definition zn_to_z2  (sps: list SMC) (x0a x0b: Z) (xas xbs: list Z): (list (Z * Z * Z * Z)) :=
	(* since each step 2 requires xi and xi', we need to make the list [xi] to [(xi', xi)] first *)
	(* rev because 5 = [:: x2=1; x1=0; x0=1];
	   and xs without x0 is [:: x2=1; x1=0];
	   and we need [:: (x2, x1); (x1, x0)];
	   while the natural order of `pairmap := [:: f a x_1; f x_1 x_2; ...; f x_n-1 x_n]`,
	   the `a` init value will be mapped with the highest x2, not the lowest x1 we need.
	*)
	let xas' := pairmap (fun x x' => (x', x)) x0a (rev xas)
	let xbs' := pairmap (fun x x' => (x', x)) x0b (rev xbs)
	let folder := fun `(cai, cbi, yai, ybi) `(sp, xa, xb) => 
		zn_to_z2_tai_tbi sp cia cbi yai ybi in
	(* For party A,B: c0=0,  y0=x0*)
	foldl folder [:: (0, 0, x0a, x0b)] (zip sps (zip xas xbs))

Fixpoint zn_to_z2_step_2 (sps: list SMC) (xas xbs : list Z) : (list (Z * Z)) :=
	match sps, xas, xbs with
	| sp :: tlsps, xa :: tlxas, xb :: tlxbs => 
		(zn_to_z2_tai_tbi sp ca cb xa xb :: zn_to_z2_step_2 tlsps tlxas tlxbs)
	| _, _, _ => [::]
	end.



(* According to step 1: must set cas[0] = cbs[0] = 0 *)
(* TODO: zn_to_z2_step_2 is not completed yet. See comments above. *)
Definition zn_to_z2 (sps: list SMC) (cas cbs xas xbs : list Z) : (list Z * list Z) :=
	let iteration_results := zn_to_z2_step_2 sps cas cbs xas xbs in
	(* From list of pairs to pair of lists: ([ta_k-1...ta_0], [tb_k-1...tb_0]). *)
	let to_lists := fold_left
			(fun sumlists ti_pair => (fst ti_pair :: fst sumlists, snd ti_pair :: snd sumlists))
			iteration_results
			([],[]) in
	to_lists.

