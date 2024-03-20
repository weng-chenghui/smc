From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp.finmap Require Import finmap.
From mathcomp.classical Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp.classical Require Import cardinality.
From HB Require Import structures.
From mathcomp.analysis Require Import exp numfun lebesgue_measure lebesgue_integral.
From mathcomp.analysis Require Import reals ereal signed topology normedtype sequences esum measure.
From mathcomp.analysis Require Import probability.

Require Import smc_scalar_product.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We want to define sps by means of a random variable to
   turn zn_to_z2 into a probabilistic algorithm. *)

(* We may also port hierarchy.v from monae onto mathcomp0-analysis,
   skipping infotheo to make a mini-monae that we can work with until infotheo/monae are
   ported to mc2. *)

