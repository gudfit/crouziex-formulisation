(* OpenLemmaQuadratic.v *)
From Stdlib Require Import Reals.
From OpenLemma Require Import MathCompBackbone OpenLemmaGeneral.
Set Implicit Arguments.
From Coq Require Import Lia.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OpenLemmaQuadratic.

Variable n : nat.

(* Abstract complex scalars and basic operations *)
Parameter C : Type.
Parameter Re : C -> R.
Parameter Conj : C -> C.
Parameter I : C.
Parameter Cexp : R -> C.
(* Minimal scalar operations *)
Parameter addC : C -> C -> C.
Parameter mulC : C -> C -> C.
Parameter zeroC : C.
Infix "+c" := addC (at level 50, left associativity).
Infix "*c" := mulC (at level 40, left associativity).

(* Abstract vectors/matrices and operations *)
Parameter M : Type.
Parameter vct : Type.

(* Matrix and vector operations *)
Parameter mmul : M -> M -> M.  Infix "*m" := mmul (at level 40, left associativity).
Parameter mvmul : M -> vct -> vct. Infix "*v" := mvmul (at level 40, left associativity).
Parameter outer : vct -> vct -> M. (* rank-one v * (adj xi) *)

Parameter addM : M -> M -> M. Infix "+m" := addM (at level 50, left associativity).
Parameter scaleM : C -> M -> M. Infix "*:" := scaleM (at level 40, left associativity).
Parameter powM : M -> nat -> M. Notation "A ^+ n" := (powM A n) (at level 30).

(* Vector addition and scaling for inner linearity *)
Parameter addV : vct -> vct -> vct. Infix "+v" := addV (at level 50, left associativity).
Parameter scaleV : C -> vct -> vct. Infix "*:v" := scaleV (at level 40, left associativity).

(* Adjoint and trace *)
Parameter adjM : M -> M.
Parameter adjv : vct -> vct.
Parameter tr : M -> C. Notation "\tr X" := (tr X) (at level 10).

(* Inner product on C^n *)
Parameter inner : vct -> vct -> C.
Notation "<[ x , y ]>" := (inner x y) (at level 60).

(* Projector onto V3 and its properties (abstract) *)
Parameter x : vct.         (* support eigenvector x_{theta*} *)
Parameter P3 : M.          (* orthogonal projector onto span{x, A x, A* x} *)
Parameter P3_idem : P3 *m P3 = P3.
Parameter P3_selfadj : adjM P3 = P3.

(* Data of the problem (abstract) *)
Parameter A : M.
(* P3 fixes the generators of V3: x, A x, and A* x *)
Parameter P3_on_x      : P3 *v x = x.
Parameter P3_on_Ax     : P3 *v (A *v x) = A *v x.
Parameter P3_on_Astarx : P3 *v ((adjM A) *v x) = (adjM A) *v x.
Parameter u : vct.
Parameter fA : M.          (* placeholder for f(A) *)
Parameter normv : vct -> R.
Parameter v : vct.         (* treat the normalized vector as given *)

(* Coefficients and angle (abstract) *)
Parameter c : nat -> nat -> C.  (* intended domain {0,1,2} × {0,1,2} *)
Parameter theta_star : R.
Parameter alpha : C.            (* intended alpha = Cexp (- I * theta_star) / 2 *)

(* We keep H abstract; its concrete formula is not used below *)
Parameter H : M -> R -> M.

(* Linearity axioms to move sums/scalars through products and inner *)
Parameter mvmul_addM : forall (X Y : M) (z : vct), (X +m Y) *v z = (X *v z) +v (Y *v z).
Parameter mvmul_scaleM : forall (a : C) (X : M) (z : vct), (a *: X) *v z = (a *:v (X *v z)).
Parameter inner_add_l : forall (x y z : vct), <[ x +v y , z ]> = <[ x , z ]> +c <[ y , z ]>.
Parameter inner_scale_l : forall (a : C) (x z : vct), <[ a *:v x , z ]> = a *c <[ x , z ]>.
Parameter mvmul_mmul : forall (X Y : M) (z : vct), (X *m Y) *v z = X *v (Y *v z).

(* Membership in V3 via projector *)
Definition inV3 (y : vct) := P3 *v y = y.

(* Axiomatized trace identity connecting rank-one and inner product *)
Parameter tr_adj_mul_vec :
  forall (X Y : M) (v0 xi : vct),
  \tr (X *m (outer v0 (adjv xi)) *m Y) = <[ (mvmul (adjM Y) (mvmul X v0)) , xi ]>.

(* A zero vector and a derivative placeholder to keep the statement shape *)
Parameter vzero : vct.
(* Finite 3-term sums (indices 0,1,2) *)
Definition sum3C (f : nat -> C) : C := (f 0) +c (f 1) +c (f 2).
Definition sum3M (f : nat -> M) : M := (f 0) +m (f 1) +m (f 2).

Lemma sum3C_ext3 (f g : nat -> C) :
  f 0 = g 0 -> f 1 = g 1 -> f 2 = g 2 -> sum3C f = sum3C g.
Proof.
  intros H0 H1 H2. unfold sum3C. now rewrite H0, H1, H2.
Qed.

(* Concrete W operator as a finite double sum *)
Definition Wop : M :=
  sum3M (fun j =>
    sum3M (fun k =>
      (c j k) *: (
         (alpha *: (adjM (A ^+ k) *m (A ^+ (S j))))
       +m ((Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ j)))
      ))).

(* The derivative functional as a finite sum of traces *)
Definition termC (j k : nat) (xi : vct) : C :=
  (c j k) *c (
     (alpha *c (\tr ((A ^+ (S j)) *m (outer v (adjv xi)) *m (A ^+ k))))
  +c ((Conj alpha) *c (\tr ((A ^+ j) *m (outer v (adjv xi)) *m (A ^+ (S k)))))
  ).

Definition deriv (xi : vct) : R := Re (sum3C (fun j => sum3C (fun k => termC j k xi))).

(* Expand inner through a 3-term matrix sum *)
Lemma inner_sum3M (f : nat -> M) (xi : vct) :
  <[ (sum3M f) *v v , xi ]> =
    (<[ (f 0) *v v , xi ]> +c <[ (f 1) *v v , xi ]>) +c <[ (f 2) *v v , xi ]>.
Proof.
  unfold sum3M.
  rewrite mvmul_addM.
  rewrite inner_add_l.
  rewrite mvmul_addM.
  rewrite inner_add_l.
  reflexivity.
Qed.

(* Distribute inner over scaled matrix acting on v *)
Lemma inner_scaleM (a : C) (X : M) (xi : vct) :
  <[ (a *: X) *v v , xi ]> = a *c <[ X *v v , xi ]>.
Proof.
  rewrite mvmul_scaleM.
  rewrite inner_scale_l.
  reflexivity.
Qed.

(* Distribute inner over sum of two scaled matrices *)
Lemma inner_add_parts (X Y : M) (xi : vct) :
  <[ ((alpha *: X) +m ((Conj alpha) *: Y)) *v v , xi ]>
  = (alpha *c <[ X *v v , xi ]>) +c ((Conj alpha) *c <[ Y *v v , xi ]>).
Proof.
  rewrite mvmul_addM.
  rewrite inner_add_l.
  rewrite !inner_scaleM.
  reflexivity.
Qed.

(* Convert the two canonical terms to traces via the axiom *)
Lemma inner_to_tr_left (j k : nat) (xi : vct) :
  <[ ((adjM (A ^+ k) *m (A ^+ (S j))) *v v) , xi ]>
  = \tr ((A ^+ (S j)) *m (outer v (adjv xi)) *m (A ^+ k)).
Proof. rewrite mvmul_mmul. symmetry; apply tr_adj_mul_vec. Qed.

Lemma inner_to_tr_right (j k : nat) (xi : vct) :
  <[ ((adjM (A ^+ (S k)) *m (A ^+ j)) *v v) , xi ]>
  = \tr ((A ^+ j) *m (outer v (adjv xi)) *m (A ^+ (S k))).
Proof. rewrite mvmul_mmul. symmetry; apply tr_adj_mul_vec. Qed.

(* Each termC equals the corresponding inner-product form *)
Lemma termC_as_inner (j k : nat) (xi : vct) :
  termC j k xi =
  (c j k) *c (
     (alpha *c <[ ((adjM (A ^+ k) *m (A ^+ (S j))) *v v) , xi ]>)
   +c ((Conj alpha) *c <[ ((adjM (A ^+ (S k)) *m (A ^+ j)) *v v) , xi ]>) ).
Proof.
  unfold termC.
  rewrite <- inner_to_tr_left.
  rewrite <- inner_to_tr_right.
  reflexivity.
Qed.

(* Sum over k*)
Lemma inner_sum3M_scale (j : nat) (Q : nat -> M) (xi : vct) :
  <[ (sum3M (fun k => (c j k) *: (Q k)) *v v) , xi ]>
  = sum3C (fun k => (c j k) *c <[ (Q k) *v v , xi ]>).
Proof.
  rewrite inner_sum3M.
  unfold sum3C.
  rewrite !inner_scaleM.
  reflexivity.
Qed.

Lemma j_slice_expand (j : nat) (xi : vct) :
  <[ (sum3M (fun k => (c j k) *:
                   ((alpha *: (adjM (A ^+ k) *m (A ^+ (S j))))
                  +m ((Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ j))))) *v v) , xi ]>
  = sum3C (fun k =>
      (c j k) *c
      ((alpha *c <[ ((adjM (A ^+ k) *m (A ^+ (S j))) *v v) , xi ]>)
       +c ((Conj alpha) *c <[ ((adjM (A ^+ (S k)) *m (A ^+ j)) *v v) , xi ]>))).
Proof.
  eapply eq_trans.
  - apply inner_sum3M_scale with (Q := fun k =>
        (alpha *: (adjM (A ^+ k) *m (A ^+ (S j))))
      +m ((Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ j)))).
  - unfold sum3C; cbn.
    rewrite inner_add_parts.
    rewrite inner_add_parts.
    rewrite inner_add_parts.
    reflexivity.
Qed.


Lemma slice0 (xi : vct) :
  sum3C (fun k => termC 0 k xi) =
  <[ (sum3M (fun k =>
        c 0 k *:
          (alpha *: (adjM (A ^+ k) *m (A ^+ 1))
           +m (Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ 0)))) ) *v v
     , xi ]>.
Proof.
  rewrite j_slice_expand.
  apply sum3C_ext3; cbn;
    (rewrite <- termC_as_inner; reflexivity).
Qed.

Lemma slice1 (xi : vct) :
  sum3C (fun k => termC 1 k xi) =
  <[ (sum3M (fun k =>
        c 1 k *:
          (alpha *: (adjM (A ^+ k) *m (A ^+ 2))
           +m (Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ 1)))) ) *v v
     , xi ]>.
Proof.
  rewrite j_slice_expand.
  apply sum3C_ext3; cbn;
    (rewrite <- termC_as_inner; reflexivity).
Qed.
Lemma slice2 (xi : vct) :
  sum3C (fun k => termC 2 k xi) =
  <[ (sum3M (fun k =>
        c 2 k *:
          (alpha *: (adjM (A ^+ k) *m (A ^+ 3))
           +m (Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ 2)))) ) *v v
     , xi ]>.
Proof.
  rewrite j_slice_expand.
  apply sum3C_ext3; cbn;
    (rewrite <- termC_as_inner; reflexivity).
Qed.


Lemma open_lemma_quadratic_equiv (xi : vct) :
  deriv xi = Re (<[ (Wop *v v) , xi ]>).
Proof.
  unfold deriv, Wop.
  f_equal.
  rewrite inner_sum3M.
  rewrite <- slice0, <- slice1, <- slice2.
  reflexivity.
Qed.

Parameter mvmul_addV  : forall (X : M) (y z : vct), X *v (y +v z) = (X *v y) +v (X *v z).
Parameter mvmul_scaleV: forall (a : C) (X : M) (y : vct), X *v (a *:v y) = a *:v (X *v y).

Lemma inV3_add (y z : vct) :
  inV3 y -> inV3 z -> inV3 (y +v z).
Proof.
  intros Hy Hz; unfold inV3.
  rewrite mvmul_addV, Hy, Hz; reflexivity.
Qed.

Lemma inV3_scale (a : C) (y : vct) :
  inV3 y -> inV3 (a *:v y).
Proof.
  intros Hy; unfold inV3.
  rewrite mvmul_scaleV, Hy; reflexivity.
Qed.

Lemma inV3_of_scaled_matrix (a : C) (X : M) :
  inV3 (X *v v) -> inV3 ((a *: X) *v v).
Proof.
  intro HX; rewrite mvmul_scaleM; apply inV3_scale, HX.
Qed.

Lemma inV3_of_sum_matrices (X Y : M) :
  inV3 (X *v v) -> inV3 (Y *v v) -> inV3 ((X +m Y) *v v).
Proof.
  intros HX HY; rewrite mvmul_addM; apply inV3_add; assumption.
Qed.

Lemma inV3_sum3M_apply (F : nat -> M) :
  inV3 ((F 0) *v v) -> inV3 ((F 1) *v v) -> inV3 ((F 2) *v v) ->
  inV3 ((sum3M F) *v v).
Proof.
  intros H0 H1 H2.
  unfold sum3M.
  rewrite mvmul_addM.
  apply inV3_add.
  - rewrite mvmul_addM.
    apply inV3_add; [exact H0|exact H1].
  - exact H2.
Qed.

Section HermitianCase.

  Hypothesis v_is_x : v = x.

  Hypothesis span3_coords_deg5 :
    forall p q : nat,
    le (p + q) 5 ->
    exists a b c : C,
      adjM (A ^+ q) *m A ^+ p *v x =
      a *:v x +v b *:v (A *v x) +v c *:v (adjM A *v x).
      

  (* From span coordinates, we get the V3-closure property needed downstream. *)
  Lemma V3_closure_deg5 :
      forall p q, le (p + q) 5 ->
        inV3 ((adjM (A ^+ q) *m (A ^+ p)) *v x).
  Proof.
    intros p q Hpq.
    apply span3_coords_deg5 in Hpq as [a [b [c Heq]]].
    unfold inV3.
    rewrite Heq.
    apply inV3_add.
    - apply inV3_add.
      + apply inV3_scale. unfold inV3; exact P3_on_x.
      + apply inV3_scale. unfold inV3; exact P3_on_Ax.
    - apply inV3_scale. unfold inV3; exact P3_on_Astarx.
  Qed.

  Lemma quad_img_left (j k : nat) (Hj : j <= 2) (Hk : k <= 2) :
    inV3 ((adjM (A ^+ k) *m (A ^+ (S j))) *v v).
  Proof.
    rewrite v_is_x.
    apply V3_closure_deg5; lia.
  Qed.

  Lemma quad_img_right (j k : nat) (Hj : j <= 2) (Hk : k <= 2) :
    inV3 ((adjM (A ^+ (S k)) *m (A ^+ j)) *v v).
  Proof.
    rewrite v_is_x.
    apply V3_closure_deg5; lia.
  Qed.

  Lemma inV3_inner_jk (j k : nat) (Hj : j <= 2) (Hk : k <= 2) :
    inV3 (((alpha *: (adjM (A ^+ k) *m (A ^+ (S j))))
          +m ((Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ j)))) *v v).
  Proof.
    apply inV3_of_sum_matrices.
    - apply inV3_of_scaled_matrix. apply quad_img_left; [assumption|assumption].
    - apply inV3_of_scaled_matrix. apply quad_img_right; [assumption|assumption].
  Qed.

  Lemma inV3_inner_j (j : nat) (Hj : j <= 2) :
    inV3 ((sum3M (fun k => (c j k) *:
                     ((alpha *: (adjM (A ^+ k) *m (A ^+ (S j))))
                    +m ((Conj alpha) *: (adjM (A ^+ (S k)) *m (A ^+ j))))) ) *v v).
  Proof.
    apply inV3_sum3M_apply.
    - apply inV3_of_scaled_matrix. eapply inV3_inner_jk; [exact Hj|].
      (* k = 0 <= 2 *)
      apply le_S. apply le_S. apply le_n.
    - apply inV3_of_scaled_matrix. eapply inV3_inner_jk; [exact Hj|].
      (* k = 1 <= 2 *)
      apply le_S. apply le_n.
    - apply inV3_of_scaled_matrix. eapply inV3_inner_jk; [exact Hj|].
      (* k = 2 <= 2 *)
      apply le_n.
  Qed.

  Lemma Wv_in_V3_quadratic :
    inV3 (Wop *v v).
  Proof.
    unfold Wop. 
    apply inV3_sum3M_apply.
    - apply inV3_inner_j. (* j = 0 <= 2 *)
      apply le_S. apply le_S. apply le_n.
    - apply inV3_inner_j. (* j = 1 <= 2 *)
      apply le_S. apply le_n.
    - apply inV3_inner_j. (* j = 2 <= 2 *)
      apply le_n.
  Qed.

End HermitianCase.

(* Adjoint action on inner product and zero helpers, used for the corollary *)
Parameter inner_adj : forall (X : M) (y z : vct), <[ X *v y , z ]> = <[ y , (adjM X) *v z ]>.
Parameter inner_zero_r : forall x, <[ x , vzero ]> = zeroC.
Parameter Re_zero : Re zeroC = 0%R.

Lemma inner_proj_sym (y z : vct) :
  <[ (P3 *v y) , z ]> = <[ y , (P3 *v z) ]>.
Proof.
  rewrite inner_adj.
  now rewrite P3_selfadj.
Qed.

Lemma inner_killed_by_proj (y xi : vct) :
  inV3 y -> P3 *v xi = vzero -> Re (<[ y , xi ]>) = 0%R.
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

Corollary open_lemma_quadratic
  (v_is_x : v = x)
  (span3_coords_deg5 :
     forall p q : nat,
       p + q <= 5 ->
       exists a b c : C,
         adjM (A ^+ q) *m A ^+ p *v x =
         a *:v x +v b *:v (A *v x) +v c *:v (adjM A *v x))
  (xi : vct) :
  (P3 *v xi = vzero) ->
  Re (<[ (Wop *v v) , xi ]>) = 0%R.
Proof.
  intros Hperp; apply inner_killed_by_proj.
  - apply (Wv_in_V3_quadratic v_is_x span3_coords_deg5).
  - exact Hperp.
Qed.


Section QuadraticInstantiation.

  Hypothesis v_is_x : v = x.
  Hypothesis span3_coords_deg5 :
    forall p q : nat,
      p + q <= 5 ->
      exists a b c : C,
        adjM (A ^+ q) *m A ^+ p *v x =
        a *:v x +v b *:v (A *v x) +v c *:v (adjM A *v x).

  Lemma open_lemma_quadratic_from_general (xi : vct) :
    (P3 *v xi = vzero) -> deriv xi = 0%R.
  Proof.
    intros Hperp.
    rewrite open_lemma_quadratic_equiv.
    apply (open_lemma_quadratic v_is_x span3_coords_deg5).
    exact Hperp.
  Qed.

  Corollary open_lemma_quadratic_final (xi : vct) :
    (P3 *v xi = vzero) -> Re (<[ (Wop *v v) , xi ]>) = 0%R.
  Proof.
    intros Hperp.
    rewrite <- open_lemma_quadratic_equiv.
    apply open_lemma_quadratic_from_general; assumption.
  Qed.

End QuadraticInstantiation.

End OpenLemmaQuadratic.
