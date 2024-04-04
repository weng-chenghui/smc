From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp.algebra Require Import all_algebra.
From mathcomp.algebra_tactics Require Import ring.

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

End seq_extra.


Section iteri_dep.
Variables (A : nat -> Type) (f : forall i, A i -> A i.+1) (init : A 0).
Fixpoint iteri_dep n : A n := if n is i.+1 then f (iteri_dep i) else init.

Lemma iteri_dep_ind (P : forall {i}, A i -> Prop) :
  (forall i (acc : A i), P acc -> P (f acc)) -> P init ->
  forall n, P (iteri_dep n).
Proof. by move=> IH P0; elim => //= n /IH. Qed.
End iteri_dep.
