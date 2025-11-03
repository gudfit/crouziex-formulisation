(*OpenLemmaGeneral.v *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
From Stdlib Require Import Reals.
From OpenLemma Require MathCompBackbone.
Import GRing.Theory.
Local Open Scope ring_scope.
From OpenLemma Require MathCompBackbone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OpenLemmaGeneral.

Variable n : nat.
Variable K : fieldType.
Variable d : nat. (* d = 2*deg f, but abstract here *)

Notation M   := 'M[K]_n.
Notation vct := 'cV[K]_n.
Local Infix "*v" := MathCompBackbone.mvmul (at level 40, left associativity).
Local Notation "[< x , y >]" := (MathCompBackbone.inner x y) (at level 60).

Parameter Re : K -> R.
Parameter Conj : K -> K.
Parameter I : K.
Parameter Kexp : R -> K.
Parameter adjv : vct -> vct.
Parameter P3 : M.
Parameter P3_idem : P3 *m P3 = P3.
Parameter P3_selfadj : MathCompBackbone.adjM P3 = P3.

(* Data of the problem (abstract) *)
Parameter A : M.
Parameter u : vct.
Parameter fA : M. 
Parameter normv : vct -> R.
Parameter v : vct.      

Parameter c : nat -> nat -> K. 
Parameter theta_star : R.
Parameter alpha : K. 

Parameter H : M -> R -> M.
Definition inV3 (y : vct) := P3 *v y = y.

Parameter tr_adj_mul_vec :
  forall (X Y : M) (v0 xi : vct),
  \tr (X *m (MathCompBackbone.outer v0 (adjv xi)) *m Y)
  = [< (MathCompBackbone.mvmul (MathCompBackbone.adjM Y) (MathCompBackbone.mvmul X v0)) , xi >].

Parameter vzero : vct.

Fixpoint sumC_upto (m : nat) (f : nat -> K) : K :=
  match m with
  | O => f 0
  | S m' => (sumC_upto m' f) + (f (S m'))
  end.

Fixpoint sumM_upto (m : nat) (f : nat -> M) : M :=
  match m with
  | O => f 0
  | S m' => (sumM_upto m' f) + (f (S m'))
  end.

Definition sumC_d (f : nat -> K) : K := sumC_upto d f.
Definition sumM_d (f : nat -> M) : M := sumM_upto d f.

Definition Wop : M :=
  sumM_d (fun j =>
    sumM_d (fun k =>
      (c j k) *: (
         (alpha *: (MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))))
       + ((Conj alpha) *: (MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)))
      ))).

Definition termC (j k : nat) (xi : vct) : K :=
  (c j k) * (
     (alpha * (\tr ((A ^+ (S j)) *m (MathCompBackbone.outer v (adjv xi)) *m (A ^+ k))))
   + ((Conj alpha) * (\tr ((A ^+ j) *m (MathCompBackbone.outer v (adjv xi)) *m (A ^+ (S k)))))
  ).

Definition deriv (xi : vct) : R :=
  Re (sumC_d (fun j => sumC_d (fun k => termC j k xi))).

Lemma inner_scaleM (a : K) (X : M) (xi : vct) :
  [< (a *: X) *v v , xi >] = a * [< X *v v , xi >].
Proof.
  rewrite MathCompBackbone.mvmul_scaleM.
  rewrite MathCompBackbone.inner_scale_l.
  reflexivity.
Qed.

Lemma inner_add_parts (X Y : M) (xi : vct) :
  [< ((alpha *: X) + ((Conj alpha) *: Y)) *v v , xi >]
  = (alpha * [< X *v v , xi >]) + ((Conj alpha) * [< Y *v v , xi >]).
Proof.
  rewrite MathCompBackbone.mvmul_addM.
  rewrite MathCompBackbone.inner_add_l.
  rewrite !inner_scaleM.
  reflexivity.
Qed.

Lemma inner_sumM_upto (m : nat) (f : nat -> M) (xi : vct) :
  [< (sumM_upto m f) *v v , xi >] = sumC_upto m (fun k => [< (f k) *v v , xi >]).
Proof.
  elim: m => [|m IHm]; simpl; first by reflexivity.
  by rewrite MathCompBackbone.mvmul_addM MathCompBackbone.inner_add_l IHm.
Qed.

Lemma sumC_upto_ext (m : nat) (f g : nat -> K) :
  (forall i, f i = g i) -> sumC_upto m f = sumC_upto m g.
Proof.
  move=> Heq; elim: m => [|m IHm]; simpl.
  - by rewrite Heq.
  - by rewrite IHm // Heq.
Qed.

Lemma inner_to_tr_left (j k : nat) (xi : vct) :
  [< ((MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))) *v v) , xi >]
  = \tr ((A ^+ (S j)) *m (MathCompBackbone.outer v (adjv xi)) *m (A ^+ k)).
Proof. rewrite MathCompBackbone.mvmul_mmul. symmetry; apply tr_adj_mul_vec. Qed.

Lemma inner_to_tr_right (j k : nat) (xi : vct) :
  [< ((MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)) *v v) , xi >]
  = \tr ((A ^+ j) *m (MathCompBackbone.outer v (adjv xi)) *m (A ^+ (S k))).
Proof. rewrite MathCompBackbone.mvmul_mmul. symmetry; apply tr_adj_mul_vec. Qed.

Lemma termC_as_inner (j k : nat) (xi : vct) :
  termC j k xi =
  (c j k) * (
     (alpha * [< ((MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))) *v v) , xi >])
   + ((Conj alpha) * [< ((MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)) *v v) , xi >]) ).
Proof.
  rewrite /termC.
  rewrite (inner_to_tr_left j k xi).
  rewrite (inner_to_tr_right j k xi).
  reflexivity.
Qed.

Lemma open_lemma_general_equiv (xi : vct) :
  deriv xi = Re ([< (Wop *v v) , xi >]).
Proof.
  rewrite /deriv /Wop.
  apply f_equal.
  rewrite inner_sumM_upto.
  apply: sumC_upto_ext => j; simpl.
  rewrite inner_sumM_upto.
  apply: sumC_upto_ext => k; simpl.
  rewrite inner_scaleM.
  rewrite inner_add_parts.
  by rewrite -(termC_as_inner j k xi).
Qed.

Parameter mvmul_addV  : forall (X : M) (y z : vct), X *v (y + z) = (X *v y) + (X *v z).
Parameter mvmul_scaleV: forall (a : K) (X : M) (y : vct), X *v (a *: y) = a *: (X *v y).

Lemma inV3_add (y z : vct) :
  inV3 y -> inV3 z -> inV3 (y + z).
Proof.
  intros Hy Hz; unfold inV3.
  by rewrite mvmul_addV Hy Hz.
Qed.

Lemma inV3_scale (a : K) (y : vct) :
  inV3 y -> inV3 (a *: y).
Proof.
  intros Hy; unfold inV3.
  by rewrite mvmul_scaleV Hy.
Qed.

Lemma inV3_of_scaled_matrix (a : K) (X : M) :
  inV3 (X *v v) -> inV3 ((a *: X) *v v).
Proof.
  intro HX; rewrite MathCompBackbone.mvmul_scaleM; apply inV3_scale, HX.
Qed.

Lemma inV3_of_sum_matrices (X Y : M) :
  inV3 (X *v v) -> inV3 (Y *v v) -> inV3 ((X + Y) *v v).
Proof.
  intros HX HY; rewrite MathCompBackbone.mvmul_addM; apply inV3_add; assumption.
Qed.

Parameter gen_img_left : forall j k : nat,
  inV3 ((MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))) *v v).
Parameter gen_img_right : forall j k : nat,
  inV3 ((MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)) *v v).

Lemma inV3_sumM_upto (m : nat) (f : nat -> M) :
  (forall k, inV3 ((f k) *v v)) ->
  inV3 ((sumM_upto m f) *v v).
Proof.
  move=> Hall; elim: m => [|m IH] /=.
  - exact: Hall 0.
  - apply: inV3_of_sum_matrices.
    + exact: IH. 
    + exact: (Hall (S m)).
Qed.

Lemma inV3_one_term (j k : nat) :
  inV3 ( ((c j k) *:
           ( (alpha        *: (MathCompBackbone.adjM (A ^+ k)     *m (A ^+ (S j))))
           + ((Conj alpha) *: (MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)))) )
         *v v).
Proof.
  pose X := (MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))).
  pose Y := (MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)).
  have HX : inV3 (X *v v) by apply: gen_img_left.
  have HY : inV3 (Y *v v) by apply: gen_img_right.
  have HX' : inV3 ((alpha *: X) *v v).
  - rewrite MathCompBackbone.mvmul_scaleM. apply: inV3_scale. exact: HX.
  have HY' : inV3 (((Conj alpha) *: Y) *v v).
  - rewrite MathCompBackbone.mvmul_scaleM. apply: inV3_scale. exact: HY.
  have Hsum : inV3 (((alpha *: X) + ((Conj alpha) *: Y)) *v v).
  - rewrite MathCompBackbone.mvmul_addM.
    apply: inV3_add; [exact: HX' | exact: HY'].
  rewrite MathCompBackbone.mvmul_scaleM.
  apply: inV3_scale. exact: Hsum.
Qed.

Lemma Wv_in_V3_general : inV3 (Wop *v v).
Proof.
  rewrite /Wop /sumM_d.
  have Hj : forall j, inV3 ((sumM_upto d
                 (fun k =>
                    (c j k) *:
                      ( (alpha *: (MathCompBackbone.adjM (A ^+ k) *m (A ^+ (S j))))
                      + ((Conj alpha) *: (MathCompBackbone.adjM (A ^+ (S k)) *m (A ^+ j)))))) *v v).
  { move=> j.
    apply: inV3_sumM_upto => k.
    exact: (inV3_one_term j k).
  }
  apply: inV3_sumM_upto => j.
  exact: (Hj j).
Qed.

Parameter inner_zero_r : forall x, [< x , vzero >] = 0.
Parameter Re_zero : Re 0 = 0%R.

Lemma inner_proj_sym (y z : vct) :
  [< (P3 *v y) , z >] = [< y , (P3 *v z) >].
Proof.
  rewrite MathCompBackbone.inner_adj.
  now rewrite P3_selfadj.
Qed.

Lemma inner_killed_by_proj (y xi : vct) :
  inV3 y -> P3 *v xi = vzero -> Re ([< y , xi >]) = 0%R.
Proof.
  intros Hy Hperp.
  unfold inV3 in Hy.
  rewrite <- Hy.
  rewrite inner_proj_sym.
  rewrite Hperp.
  rewrite inner_zero_r.
  rewrite Re_zero.
  reflexivity.
Qed.

Corollary open_lemma_general (xi : vct) :
  (P3 *v xi = vzero) -> Re ([< (Wop *v v) , xi >]) = 0%R.
Proof.
  intros Hperp;  apply inner_killed_by_proj.
  - apply Wv_in_V3_general.
  - exact Hperp.
Qed.

End OpenLemmaGeneral.
