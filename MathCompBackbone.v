(* MathCompBackbone.v *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section MathCompBackbone.

Variable n : nat.
Variable K : fieldType.

Notation M   := 'M[K]_n. 
Notation vct := 'cV[K]_n.

Definition mmul  := @mulmx K n n n.  Infix "*m" := mmul (at level 40, left associativity).
Definition mvmul := @mulmx K n n 1.  Infix "*v" := mvmul (at level 40, left associativity).

Local Notation "X +m Y" := (X + Y) (at level 50, left associativity).
Local Notation "x +v y" := (x + y) (at level 50, left associativity).

Local Notation "a *:v x" := (a *: x) (at level 40, left associativity).

Definition adjM (X : M) : M := trmx X.

Definition outer (v xi : vct) : M := v *m trmx xi.
Definition inner (x y : vct) : K := (trmx x *m y) 0 0.
Notation "[< x , y >]" := (inner x y) (at level 60).

Lemma trmxDv (x y : vct) : trmx (x +v y) = trmx x + trmx y.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmxZv (a : K) (x : vct) : trmx (a *:v x) = a *: trmx x.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.


Lemma mvmul_addM (X Y : M) (z : vct) :
  (X +m Y) *v z = (X *v z) +v (Y *v z).
Proof. by rewrite /mvmul mulmxDl. Qed.

Lemma mvmul_scaleM (a : K) (X : M) (z : vct) :
  (a *: X) *v z = a *:v (X *v z).
Proof. by rewrite /mvmul -scalemxAl. Qed.

Lemma mvmul_mmul (X Y : M) (z : vct) :
  (X *m Y) *v z = X *v (Y *v z).
Proof. by rewrite /mvmul mulmxA. Qed.

Lemma inner_add_l (x y z : vct) :
  [< x +v y , z >] = [< x , z >] + [< y , z >].
Proof. by rewrite /inner trmxDv mulmxDl !mxE. Qed.

Lemma inner_scale_l (a : K) (x z : vct) :
  [< a *:v x , z >] = a * [< x , z >].
Proof. by rewrite /inner trmxZv -scalemxAl !mxE. Qed.

Lemma inner_adj (X : M) (y z : vct) :
  [< X *v y , z >] = [< y , (adjM X) *v z >].
Proof. by rewrite /inner /adjM trmx_mul mulmxA !mxE. Qed.

End MathCompBackbone.
