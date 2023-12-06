From mathcomp Require Import ssreflect eqtype ssrbool ssrnat seq tuple ssrfun ssralg.
Require Import ssrZ ZArith_ext uniq_tac ssrnat_ext.

Local Open Scope ring_scope.
Variable R : ringType.

Locate "*".

Definition dotmul u v : R := (u *m v^T)``_0.

Definition dotproduct n (a b : 'cV[R]_n) : R := (a ^T *m b) 0 0.

