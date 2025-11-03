(* File: PaperAppendixB.v – Formalization of Appendix B: Open Lemma *)
From Stdlib Require Import Reals.
From OpenLemma Require Import OpenLemmaQuadratic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope R_scope.

(* This file ties the formal Coq development to the paper's Appendix B. *)

Section OriginalOpenLemma.

(* State the Open Lemma in the formal shape we proved: *)
Definition OriginalOpenLemma (xi : vct) : Prop :=
  (mvmul P3 xi = vzero) -> Re (inner (mvmul Wop v) xi) = 0%R.

(* PROVEN: Quadratic case (deg f ≤ 2) via our development. *)
Theorem open_lemma_quadratic_proven :
  forall xi : vct, OriginalOpenLemma xi.
Proof.
  intros xi Hperp.
  unfold OriginalOpenLemma.
  apply open_lemma_quadratic; exact Hperp.
Qed.

End OriginalOpenLemma.
