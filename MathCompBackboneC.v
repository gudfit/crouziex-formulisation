(* MathCompBackboneC.v *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
From mathcomp.algebra   Require Import ssrnum.
From mathcomp.real_closed Require Import complex.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope ring_scope.
Open Scope complex_scope.
Section MathCompBackboneC.
Variable n : nat.
Variable R : rcfType.
Local Notation C := (complex R). 
Notation M   := 'M[C]_n.
Notation vct := 'cV[C]_n.

(* Matrix and vector products *)
(* Definition mmul  := @mulmx C n n n.   Infix "*m" := mmul. *)
Definition mvmul := @mulmx C n n 1.
Infix "*v" := mvmul (at level 40, left associativity).

Local Notation "X +m Y" := (X + Y) (at level 50, left associativity).
Local Notation "x +v y" := (x + y) (at level 50, left associativity).
Local Notation "a *:v x" := (a *: x) (at level 40, left associativity).

(* Hermitian adjoint: conjugate transpose *)
Definition adjM (X : M) : M := (map_mx conjC X)^T.
Definition outer (v xi : vct) : M := v *m (trmx xi).
Definition inner (x y : vct) : C := (@mulmx C 1 n 1 (map_mx conjC (trmx y)) x) 0 0.
Notation "[< x , y >]" := (inner x y) (at level 60).

Lemma trmxDv (x y : vct) : trmx (x +v y) = trmx x + trmx y.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmxZv (a : C) (x : vct) : trmx (a *:v x) = a *: trmx x.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma conj_map_mul (A B : M) :
  map_mx conjC (A *m B) = (map_mx conjC A) *m (map_mx conjC B).
Proof. by rewrite map_mxM. Qed.

Lemma conj_map_add (A B : M) :
  map_mx conjC (A + B) = (map_mx conjC A) + (map_mx conjC B).
Proof. by rewrite map_mxD. Qed.

Lemma mvmul_addM (X Y : M) (z : vct) :
  (X +m Y) *v z = (X *v z) +v (Y *v z).
Proof. by rewrite /mvmul mulmxDl. Qed.

Lemma mvmul_scaleM (a : C) (X : M) (z : vct) :
  (a *: X) *v z = a *:v (X *v z).
Proof. by rewrite /mvmul -scalemxAl. Qed.

Lemma mvmul_mmul (X Y : M) (z : vct) :
  (X *m Y) *v z = X *v (Y *v z).
Proof. by rewrite /mvmul mulmxA. Qed.


Lemma inner_add_l (x y z : vct) :
  [< x +v y , z >] = [< x , z >] + [< y , z >].
Proof. rewrite /inner mulmxDr !mxE; reflexivity. Qed.

Lemma inner_scale_l (a : C) (x z : vct) :
  [< a *:v x , z >] = a * [< x , z >].
Proof. rewrite /inner -scalemxAr !mxE; reflexivity. Qed.

Lemma conjC_involutive : involutive (conjC : C -> C).
Proof. by case=> a b; rewrite /conjC /= opprK. Qed.

Lemma map_conj_involutiveM (A : M) :
  map_mx conjC (map_mx conjC A) = A.
Proof. by apply/matrixP=> i j; rewrite !mxE (conjC_involutive _). Qed.


(* Adjoint compatibility: < X y , z > = < y , (adjM X) z > *)
Lemma inner_adj (X : M) (y z : vct) :
  [< X *v y , z >] = [< y , (adjM X) *v z >].
Proof.
  rewrite /inner /adjM.
  set A := map_mx conjC (trmx z).
  rewrite mulmxA.
  have -> :
    map_mx conjC (trmx (((map_mx conjC X)^T) *v z)) = A *m X.
  rewrite /A trmx_mul trmxK map_mxM map_conj_involutiveM //.
  reflexivity.
Qed.

End MathCompBackboneC.
