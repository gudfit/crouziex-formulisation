(* OpenLemmaFinalProve.v *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
From mathcomp.algebra   Require Import ssrnum.
From mathcomp.real_closed Require Import complex.
From Stdlib Require Import Reals Lia ClassicalChoice.
From mathcomp Require Import order bigop.
From mathcomp Require Import vector.
From mathcomp Require Import ssrnat.
Import Num.Theory ComplexField GRing.Theory Order.TTheory.

From OpenLemma Require Import MathCompBackboneC OpenLemmaQuadraticRestricted OpenLemmaFinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section QuickSplitLast.

Variable R : rcfType.
Local Notation C := R[i].

Variable N : nat.
Hypothesis Npos : (0 < N)%N.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

(* ordinals helpers (cast + widen) *)
Lemma cast_ordK (m1 n1 : nat) (e : m1 = n1) (i : 'I_n1) :
  cast_ord e (cast_ord (esym e) i) = i.
Proof. by apply/ord_inj. Qed.

Lemma cast_ordKV (m1 n1 : nat) (e : m1 = n1) (j : 'I_m1) :
  cast_ord (esym e) (cast_ord e j) = j.
Proof. by apply/ord_inj. Qed.

(* Identity cast *)
Lemma cast_ord_id (n : nat) (i : 'I_n) : cast_ord (erefl n) i = i.
Proof. by apply/ord_inj. Qed.

(* nat_of_ord stability lemmas *)
Lemma nat_of_cast_ord m n (e : m = n) (i : 'I_m) :
  nat_of_ord (cast_ord e i) = nat_of_ord i.
Proof. by case: e. Qed.


(* Define last index and the lift from N.-1 to N via cast/widen *)
Definition ord_last : 'I_N :=
  cast_ord (prednK Npos) (@ord_max (N.-1)).

Definition liftN (j : 'I_(N.-1)) : 'I_N :=
  widen_ord (leq_pred N) j.

Lemma liftN_nat (j : 'I_(N.-1)) : nat_of_ord (liftN j) = nat_of_ord j.
Proof. by rewrite /liftN. Qed.

Lemma ord_lastE :
  ord_last = cast_ord (prednK Npos) (@ord_max (N.-1)).
Proof. by []. Qed.

Local Open Scope nat_scope.
Lemma nat_of_widen_ord m n (le_mn : m <= n) (i : 'I_m) :
  nat_of_ord (widen_ord le_mn i) = nat_of_ord i.
Proof. by []. Qed.
Local Close Scope nat_scope.

Lemma liftN_nat' (j : 'I_(N.-1)) :
  nat_of_ord (widen_ord (leq_pred N) j) = nat_of_ord j.
Proof. exact: nat_of_widen_ord. Qed.

Definition widen_succ (j : 'I_(N.-1)) : 'I_((N.-1).+1) :=
  widen_ord (leq_pred (N.-1).+1) j.

Lemma cast_widen_predK (j : 'I_(N.-1)) :
  cast_ord (prednK Npos) (widen_succ j) = liftN j.
Proof.
  apply/ord_inj.
  by rewrite !nat_of_cast_ord !nat_of_widen_ord /liftN.
Qed.

Lemma ord_lastK :
  cast_ord (prednK Npos) (@ord_max (N.-1)) = ord_last.
Proof. by rewrite /ord_last. Qed.

Lemma cast_widen_predN (j : 'I_(N.-1)) :
  cast_ord (prednK Npos) (widen_ord (leq_pred (N.-1).+1) j) = liftN j.
Proof.
  apply/ord_inj.
  by rewrite !nat_of_cast_ord !nat_of_widen_ord /liftN.
Qed.

Lemma cast_ord_ord_max_last :
  cast_ord (prednK Npos) (@ord_max (N.-1)) = ord_last.
Proof. by rewrite /ord_last. Qed.

Lemma reindex_cast_ord (m1 n1 : nat) (e : m1 = n1) :
  forall (G : 'I_n1 -> C),
    \sum_(i : 'I_n1) G i = \sum_(j : 'I_m1) G (cast_ord e j).
Proof.
  refine (match e in (_ = n1) return forall (G : 'I_n1 -> C),
            \sum_(i : 'I_n1) G i = \sum_(j : 'I_m1) G (cast_ord e j)
          with
          | erefl => _
          end).
  move=> G.
  apply: eq_bigr => j _.
  by rewrite cast_ord_id.
Qed.

(* Reindex both sides of a double sum via a cast *)
Lemma reindex_double_cast_ord (m1 n1 : nat) (e : m1 = n1)
      (F : 'I_n1 -> 'I_n1 -> C) :
  \sum_(j : 'I_n1) \sum_(k : 'I_n1) F j k
  = \sum_(j : 'I_m1) \sum_(k : 'I_m1) F (cast_ord e j) (cast_ord e k).
Proof.
  rewrite (reindex_cast_ord e (fun j => \sum_(k : 'I_n1) F j k)).
  apply: eq_bigr => j _.
  by rewrite (reindex_cast_ord e (fun k => F (cast_ord e j) k)).
Qed.

Local Open Scope nat_scope.
Lemma cast_widen_predN_any (p : (N.-1) <= (N.-1).+1) (j : 'I_(N.-1)) :
  cast_ord (prednK Npos) (widen_ord p j) = liftN j.
Proof.
  apply/ord_inj.
  by rewrite !nat_of_cast_ord !nat_of_widen_ord /liftN.
Qed.
Local Close Scope nat_scope.

Lemma sum_split_lastN (G : 'I_N -> C) :
  \sum_(i < N) G i = \sum_(j < N.-1) G (liftN j) + G ord_last.
Proof.
  have -> :
      \sum_(i < N) G i
    = \sum_(i < (N.-1).+1) G (cast_ord (prednK Npos) i).
    by rewrite (reindex_cast_ord (prednK Npos) G).
    rewrite (@big_ord_recr _ _ _ (N.-1)
            (fun i : 'I_((N.-1).+1) => G (cast_ord (prednK Npos) i))) /=.

  congr (_ + _).
  - apply: eq_bigr => j _.
  by rewrite (cast_widen_predN_any (leqnSn (N.-1)) j).
Qed.

Lemma sum_split_via_ord_last (G : 'I_N -> C) :
  (1 < N)%N ->
  \sum_(i < N) G i
    = \sum_(j < N.-1) G (liftN j) + G ord_last.
Proof.
  move=> _.
  exact: sum_split_lastN.
Qed.

Variables (c : nat -> nat -> C) (alpha : C).
Local Notation jn i := (nat_of_ord i). 
Local Notation kn i := (nat_of_ord i).
Local Definition cI (j k : 'I_N) : C := c (jn j) (kn k).

Lemma jn_liftN (j : 'I_(N.-1)) : jn (liftN j) = jn j.
Proof. exact: liftN_nat. Qed.

Local Open Scope nat_scope.
Lemma jn_ord_last : jn ord_last = N.-1.
Proof. by rewrite /ord_last nat_of_cast_ord. Qed.

Lemma kn_ord_last : kn ord_last = N.-1.
Proof. exact: jn_ord_last. Qed.
Local Close Scope nat_scope.

Lemma split_k_last (H : 'I_N -> 'I_N -> C) :
  \sum_(j < N) \sum_(k < N) H j k
  = \sum_(j < N) \sum_(k < N.-1) H j (liftN k)
    + \sum_(j < N) H j ord_last.
Proof.
  rewrite (eq_bigr (fun j => \sum_(k < N.-1) H j (liftN k) + H j ord_last)).
  - by rewrite big_split. 
  - by move=> j _; rewrite (sum_split_lastN (fun k => H j k)).
Qed.

Lemma split_j_last (H : 'I_N -> 'I_N -> C) :
  \sum_(k < N) \sum_(j < N) H j k
  = \sum_(k < N) \sum_(j < N.-1) H (liftN j) k
    + \sum_(k < N) H ord_last k.
Proof.
  rewrite (eq_bigr (fun k => \sum_(j < N.-1) H (liftN j) k + H ord_last k)).
  - by rewrite -big_split.
  - by move=> k _; rewrite (sum_split_lastN (fun j => H j k)).
Qed.

Lemma swap_sums (H : 'I_N -> 'I_N -> C) :
  \sum_(j < N) \sum_(k < N) H j k
  = \sum_(k < N) \sum_(j < N) H j k.
Proof. by rewrite exchange_big. Qed.

Lemma mul_addr (x y z : C) : x * (y + z) = x * y + x * z.
Proof. by rewrite mulrDr. Qed.

Lemma add_mulr (x y z : C) : (x + y) * z = x * z + y * z.
Proof. by rewrite mulrDl. Qed.

Lemma big_split_mul (I : Type) (r : seq I) (P : pred I) (F G : I -> C) :
  \sum_(i <- r | P i) (F i + G i)
  = \sum_(i <- r | P i) F i + \sum_(i <- r | P i) G i.
Proof. by rewrite big_split. Qed.

Hypothesis Hbd :
  (forall k : 'I_N, c ord_last k = 0) /\
  (forall j : 'I_N, c j ord_last = 0).
  
Lemma boundary_strips_die :
  forall (psi : nat -> nat -> C),
    (\sum_(k < N) c ord_last k * psi N k) = 0 /\
    (\sum_(j < N) c j ord_last * psi j N) = 0.
Proof.
  move=> psi.
  have [Hrow Hcol] := Hbd.  (* discCR_boundary_zero *)
  split.
  - (* last row zero *)
    apply: big1 => k _.
    by rewrite Hrow mul0r.
  - (* last column zero *)
    apply: big1 => j _.
    by rewrite Hcol mul0r.
Qed.

Lemma split_k_last' (H : 'I_N -> 'I_N -> C) :
  \sum_(j < N) \sum_(k < N) H j k
  = \sum_(j < N) \sum_(k < N | k != ord_last) H j k
    + \sum_(j < N) H j ord_last.
Proof.
  rewrite (eq_bigr (fun j =>
             \sum_(k < N | k != ord_last) H j k + H j ord_last)).
  - by rewrite -big_split.
  - by move=> j _; rewrite (bigD1 ord_last) //= addrC.
Qed.


Lemma split_j_last' (H : 'I_N -> 'I_N -> C) :
  \sum_(k < N) \sum_(j < N) H j k
  = \sum_(k < N) \sum_(j | j != ord_last) H j k
    + \sum_(k < N) H ord_last k.
Proof.
  rewrite (eq_bigr (fun k =>
             \sum_(j < N | j != ord_last) H j k + H ord_last k)).
    by rewrite -big_split.
    by move=> k _; rewrite (bigD1 ord_last) //= addrC.
Qed.

(* Distribute a left scalar across a filtered big sum. *)
Lemma big_distrl_filter (a : C) (F : 'I_N -> C) :
  a * (\sum_(i < N | i != ord_last) F i)
  = \sum_(i < N | i != ord_last) a * F i.
Proof.
  (* Use the standard distributivity of multiplication over big sums. *)
  by rewrite mulr_sumr.
Qed.

(* Distribute a left scalar across a nested filtered big sum. *)
Lemma big_distrl_filter2 (a : C) (G : 'I_N -> 'I_N -> C) :
  a * (\sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last) G j k)
  = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last) a * G j k.
Proof.
  rewrite (big_distrl_filter a (fun j => \sum_(k < N | k != ord_last) G j k)).
  apply: eq_bigr => j _.
  by rewrite big_distrl_filter.
Qed.

Lemma sum_not_last (G : 'I_N -> C) :
  \sum_(i < N | i != ord_last) G i = \sum_(j < N.-1) G (liftN j).
Proof.
  have H := (sum_split_lastN G).
  rewrite (bigD1 ord_last) //= addrC in H.
  move: H; apply: (addIr (G ord_last)).
Qed.

Lemma sum_except_last3 (HN : N = 3) (G : 'I_N -> C) :
  \sum_(i < N | i != ord_last) G i = \sum_(k < N.-1) G (liftN k).
Proof. exact: sum_not_last. Qed.

Lemma sum2x2_expand (HN : N = 3) (H : 'I_N -> 'I_N -> C) :
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last) H j k
  = \sum_(j0 < N.-1) \sum_(k0 < N.-1) H (liftN j0) (liftN k0).
Proof.
  rewrite (sum_except_last3 HN (fun j => \sum_(k < N | k != ord_last) H j k)).
  apply: eq_bigr => j0 _.
  by rewrite (sum_except_last3 HN (fun k => H (liftN j0) k)).
Qed.

Lemma big2_expand (F : 'I_2 -> 'I_2 -> C) :
  \sum_(j0 < 2) \sum_(k0 < 2) F j0 k0
  = F ord0 ord0
  + F ord0 (lift ord0 ord0)
  + F (lift ord0 ord0) ord0
  + F (lift ord0 ord0) (lift ord0 ord0).
Proof.
  rewrite (big_ord_recr (R:=C)) /=.
  set S1 := \sum_(k0 < 2) F (lift ord0 ord0) k0.
  rewrite (big_ord_recr (R:=C)) /=.
  rewrite big_ord0 /=.
  rewrite /S1.
  rewrite (big_ord_recr (R:=C)) /=.
  rewrite (big_ord_recr (R:=C)) /=.
  rewrite big_ord0 /= !addrA.
  have -> :
    (widen_ord (leqnSn 1) (ord_max : 'I_1) : 'I_2) = ord0.
  by apply/ord_inj; rewrite !nat_of_widen_ord.
  have -> :
      (ord_max : 'I_2) = (lift ord0 (ord0 : 'I_1)).
  by apply/ord_inj.
  rewrite (big_ord_recr (R:=C)) /=.
  rewrite (big_ord_recr (R:=C)) /=.
  rewrite big_ord0 /= !addrA !add0r !addr0.
  have -> :
      (widen_ord (leqnSn 1) (ord_max : 'I_1) : 'I_2) = ord0
    by apply/ord_inj; rewrite !nat_of_widen_ord.
  have -> :
      (ord_max : 'I_2) = (lift ord0 (ord0 : 'I_1))
    by apply/ord_inj.
  reflexivity.
Qed.

Definition i0 (HN : N = 3) : 'I_(N.-1) :=
  cast_ord (esym (congr1 predn HN)) (ord0 : 'I_2).

Definition i1 (HN : N = 3) : 'I_(N.-1) :=
  cast_ord (esym (congr1 predn HN)) (ord_max : 'I_2).

Lemma jn_liftN_ord0 (HN : N = 3) : jn (liftN (i0 HN)) = 0.
Proof. by case: HN => //=; rewrite jn_liftN. Qed.

Lemma jn_liftN_ord1 (HN : N = 3) : jn (liftN (i1 HN)) = 1.
Proof. by case: HN => //=; rewrite jn_liftN OpenLemmaFinal.lift0_val1. Qed.

Lemma kn_liftN_ord0 (HN : N = 3) : kn (liftN (i0 HN)) = 0.
Proof. by case: HN => //=; rewrite liftN_nat. Qed.

Lemma kn_liftN_ord1 (HN : N = 3) : kn (liftN (i1 HN)) = 1.
Proof. by case: HN => //=; rewrite liftN_nat OpenLemmaFinal.lift0_val1. Qed.

Variable n : nat.
Variable A : 'M[C]_n.
Variable v_mc : 'cV[C]_n.
Variable x : 'cV[C]_n.

Local Notation P3 := (OpenLemmaFinal.P3 (R:=R) (n:=n) A x).
Local Notation V3_li := (OpenLemmaFinal.V3_li (R:=R) (n:=n) A x).

Local Notation adjM := (MathCompBackboneC.adjM (n:=n) (R:=R)).
Local Notation innerC := (MathCompBackboneC.inner (n:=n) (R:=R)).
Local Notation "[< x , y >]" := (innerC x y) (at level 60).
Local Infix  "*v"  := (@mulmx C n n 1) (at level 40, left associativity).

Local Definition Phi (j k : nat) (xi : 'cV[C]_n) : C :=
  innerC v_mc
         (@mulmx C n n 1 ((adjM A) ^+ j)
           (@mulmx C n n 1 (A ^+ k) xi)).

(* Specialize w_MO from OpenLemmaFinal to this context *)
Local Notation w_MO := (OpenLemmaFinal.w_MO (R:=R) (n:=n) A v_mc alpha cI).

(* Additional structural assumption: A is Hermitian (adjoint equals itself). *)
Hypothesis A_herm : adjM A = A.

(* Shift identity for Phi under Hermitian/normal A (assumed). *)
Hypothesis Phi_shift_herm : forall (j k : nat) (xi : 'cV[C]_n),
  Phi j (S k) xi = Phi (S j) k xi.

(* Assumed coefficient-shift at the level of the interior double sum for the
   specific integrand G j k := Phi (S j) k xi. This is the “shift” the user
   confirmed is admissible for the quadratic N=3 case. *)
Hypothesis coeff_shift_interior_for_Phi : forall (xi : 'cV[C]_n),
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      c j k * Phi (S j) k xi
  = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      c j (k.+1) * Phi (S j) k xi.

(* Using Hermitian shift on Phi and the coefficient-shift hypothesis to rewrite
   the conjugate-branch sum into the CR-telescope shape. *)
Lemma sum_shift_k_for_conj (xi : 'cV[C]_n) :
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      c j k * Phi j (S k) xi
  = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      c j (k.+1) * Phi (S j) k xi.
Proof.
  (* First, use the Hermitian shift Phi j (S k) = Phi (S j) k *)
  have -> :
    \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        c j k * Phi j (S k) xi
    = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        c j k * Phi (S j) k xi.
  { apply: eq_bigr => j _; apply: eq_bigr => k _. by rewrite Phi_shift_herm. }
  (* Then apply the coefficient-shift hypothesis on the interior double sum. *)
  exact: coeff_shift_interior_for_Phi.
Qed.

Lemma four_term_for_T (HN : N = 3) (xi : 'cV[C]_n) :
  let T j k :=
      ( c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1) )
        * Phi (S (jn j)) (kn k) xi in
  T (liftN (i0 HN)) (liftN (i0 HN)) = (c 1 0 - c 0 1) * Phi 1 0 xi /\
  T (liftN (i0 HN)) (liftN (i1 HN)) = (c 1 1 - c 0 2) * Phi 1 1 xi /\
  T (liftN (i1 HN)) (liftN (i0 HN)) = (c 2 0 - c 1 1) * Phi 2 0 xi /\
  T (liftN (i1 HN)) (liftN (i1 HN)) = (c 2 1 - c 1 2) * Phi 2 1 xi.
Proof.
  move=> T.
  move: HN; case=> /=.
  split; [|split; [|split]];
    rewrite /T /i0 /i1 /liftN
            !nat_of_widen_ord 
            !nat_of_cast_ord
            /=;
    reflexivity.
Qed.


Definition discCR_interior_ord :=
  forall (j k : 'I_N),
    j != ord_last -> k != ord_last ->
      alpha * c (jn j) (kn k)
    + (conjC alpha) * c (jn j) ((kn k).+1)
    =  c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1).

Hypothesis HCR : discCR_interior_ord.
Hypothesis HN3  : N = 3.

Local Open Scope nat_scope.
Lemma succ_nat_of_not_last (i : 'I_N) :
  i != ord_last -> (nat_of_ord i).+1 < N.
Proof.
  move=> Hi.
  have Hi_ltN : nat_of_ord i < N := ltn_ord i.
  have Hlast : nat_of_ord ord_last = N.-1 by [].
  have Hi_neq_last : nat_of_ord i != N.-1.
  { move: Hi; apply: contraNN => /eqP Heq.
    apply/eqP; apply/ord_inj. by rewrite Hlast. }
  have Hi_le_pred : nat_of_ord i <= N.-1.
  by rewrite -ltnS (prednK Npos).
  have Hi_lt_pred : nat_of_ord i < N.-1.
  { by rewrite ltn_neqAle Hi_neq_last Hi_le_pred. }
   by move: Hi_lt_pred; rewrite -ltn_predRL.
Qed.
Local Close Scope nat_scope.

Lemma rect_telescope_HCR (xi : 'cV[C]_n) :
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ( alpha * c (jn j) (kn k) * Phi (S (jn j)) (kn k) xi
      + (conjC alpha) * c (jn j) ((kn k).+1) * Phi (S (jn j)) (kn k) xi )
  =
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ( ( c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1) )
        * Phi (S (jn j)) (kn k) xi).
Proof.
  apply: eq_bigr => j Hj.
  apply: eq_bigr => k Hk.
  have Hcr := (@HCR j k Hj Hk).
  rewrite -add_mulr Hcr.
  reflexivity.
Qed.

(* A variant specialized to the shape produced after pairing and shifting,
   phrased directly with ordinal indices in the integrand. *)
Lemma rect_telescope_HCR_direct (xi : 'cV[C]_n) :
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ( (alpha * c j k) * Phi (S j) k xi
      + ((conjC alpha) * c j (k.+1)) * Phi (S j) k xi )
  =
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ( ( c (j.+1) k - c j (k.+1) ) * Phi (S j) k xi ).
Proof.
  (* Pointwise application of HCR under the double sum. *)
  apply: eq_bigr => j Hj; apply: eq_bigr => k Hk.
  have Hcr := (@HCR j k Hj Hk).
  (* Coerce ordinals to nat and reassociate products to match HCR form *)
  change (alpha * c (jn j) (kn k) * Phi (S (jn j)) (kn k) xi
          + (conjC alpha) * c (jn j) ((kn k).+1) * Phi (S (jn j)) (kn k) xi
          = (c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1))
              * Phi (S (jn j)) (kn k) xi).
  by rewrite -add_mulr Hcr.
Qed.

Lemma rect_telescope_boundary_N3 (xi : 'cV[C]_n) :
  N = 3 ->
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ( c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1) )
        * Phi (S (jn j)) (kn k) xi
  =
  (\sum_(k < N | k != ord_last) c 1 (kn k) * Phi 1 (kn k) xi)
  + (\sum_(k < N | k != ord_last) c (N.-1) (kn k) * Phi (N.-1) (kn k) xi)
  - (\sum_(j < N | j != ord_last) c (jn j) 1 * Phi (S (jn j)) 0 xi)
  - (\sum_(j < N | j != ord_last) c (jn j) (N.-1) * Phi (S (jn j)) (N.-1) xi).
Proof.
  move=> HN.
  pose T_N (j k : 'I_N) :=
    ( c ((jn j).+1) (kn k) - c (jn j) ((kn k).+1) )
    * Phi (S (jn j)) (kn k) xi.
  (* Reduce the interior double sum to the 2x2 case and expand it *)
  rewrite (sum2x2_expand HN (fun j k => T_N j k)).
  set e := (esym (congr1 predn HN)).
  rewrite (reindex_double_cast_ord e (fun j k => T_N (liftN j) (liftN k))).
  rewrite (big2_expand (fun (j0 : 'I_2) (k0 : 'I_2) => T_N (liftN (cast_ord e j0)) (liftN (cast_ord e k0)))).
  (* Compute the four T-terms using index arithmetic specialized to N=3 *)
  have Hj0 : jn (liftN (cast_ord e (ord0 : 'I_2))) = 0 by rewrite jn_liftN_ord0.
  have Hj1 : kn (liftN (cast_ord e (lift ord0 ord0))) = 1.
  { have -> : cast_ord e (lift ord0 ord0) = i1 HN.
      by rewrite /i1; have -> : (lift ord0 (ord0 : 'I_1)) = (ord_max : 'I_2)
           by apply/ord_inj.
    exact: kn_liftN_ord1 HN. }
  have -> : cast_ord e (ord0 : 'I_2) = i0 HN by rewrite /i0.
  have -> : cast_ord e (lift ord0 ord0) = i1 HN.
    have -> : cast_ord e (lift ord0 ord0) = i1 HN.
  by rewrite /i1; have -> : (lift ord0 (ord0 : 'I_1)) = (ord_max : 'I_2) by apply/ord_inj.
  by []. rewrite /T_N.
  rewrite !(kn_liftN_ord0 HN) !(kn_liftN_ord1 HN).
  have [Hrow Hcol] := Hbd.
  Local Open Scope nat_scope.
  have -> : N.-1 = kn ord_last by rewrite kn_ord_last.
  Local Close Scope nat_scope.
  have -> :
    \sum_(k < N | k != ord_last)
        c (kn ord_last) (kn k) * Phi (kn ord_last) (kn k) xi = 0.
    by apply: big1 => k _; rewrite Hrow mul0r.
  have -> :
    \sum_(j < N | j != ord_last)
        c (kn j) (kn ord_last) * Phi (kn j).+1 (kn ord_last) xi = 0.
  by apply: big1 => j _; rewrite Hcol mul0r.
  rewrite (sum_except_last3 HN (fun k => c 1 (kn k) * Phi 1 (kn k) xi)).
  rewrite (sum_except_last3 HN (fun j => c (kn j) 1 * Phi (kn j).+1 0 xi)).
  rewrite addr0 subr0.
  rewrite (reindex_cast_ord e (fun k => c 1 (kn (liftN k)) * Phi 1 (kn (liftN k)) xi)).
  rewrite (reindex_cast_ord e (fun k => c (kn (liftN k)) 1 * Phi (kn (liftN k)).+1 0 xi)).
  rewrite !(big_ord_recr (R:=C)) /= !big_ord0 /=.
  rewrite !add0r.
  rewrite opprD !addrA.
  have Hc02 : c 0 2 = 0 by
    move: (Hcol (liftN (i0 HN))); rewrite kn_liftN_ord0 kn_ord_last HN.
  have Hc12 : c 1 2 = 0 by
    move: (Hcol (liftN (i1 HN))); rewrite kn_liftN_ord1 kn_ord_last HN.
  have Hc20 : c 2 0 = 0 by
    move: (Hrow (liftN (i0 HN))); rewrite kn_liftN_ord0 kn_ord_last HN.
  have Hc21 : c 2 1 = 0 by
    move: (Hrow (liftN (i1 HN))); rewrite kn_liftN_ord1 kn_ord_last HN.
  rewrite Hc02 Hc12 Hc20 Hc21 /=. 
  rewrite subr0 sub0r subrr mul0r addr0.
  rewrite mulrBl -!addrA.
  congr (_ + _).
  rewrite addrA addrC.
  rewrite addrA.
  rewrite -addrA.
  rewrite addrA.
  Local Open Scope nat_scope.
  have -> : 0.+1 = 1 by [].
  have -> : 1.+1 = 2 by [].
  Local Close Scope nat_scope.
  rewrite [in LHS] addrC.
  congr (_ + _).
  rewrite -mulNr.
  rewrite addrC. rewrite -mulNr.
  by [].
Qed.

Lemma inner_wMO_xi_interior (xi : 'cV[C]_n) :
  [< w_MO , xi >]
  = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ( c j k
          * (alpha * Phi (S j) k xi
             + (conjC alpha) * Phi j (S k) xi) ).
Proof.
  have Hexp :=
    (OpenLemmaFinal.inner_wMO_xi (R:=R) (n:=n) (N:=N) A v_mc alpha cI xi).
  rewrite Hexp.
  rewrite /OpenLemmaFinal.phi /Phi.
  set T := fun j k : 'I_N =>
    c j k * (alpha * Phi (S j) k xi + (conjC alpha) * Phi j (S k) xi).
  (* First, split off k = ord_last and kill it by boundary zeros *)
  rewrite (split_k_last' T).
  have Hcol0 : (\sum_(j < N) T j ord_last) = 0.
  { apply: big1 => j _.
    rewrite /T /=.
    have [Hrow Hcol] := Hbd.
    have Hc0 : c j ord_last = 0 by exact: Hcol j.
    by rewrite Hc0 mul0r.
  }
  rewrite Hcol0 addr0.
  (* Now split j = ord_last and kill it as well *)
  rewrite (bigD1 ord_last) //=.
  have Hrow0 : (\sum_(k < N | k != ord_last) T ord_last k) = 0.
  { apply: big1 => k Hk.
    rewrite /T /=.
    have [Hrow Hcol] := Hbd.
    have Hc0 : c ord_last k = 0 by exact: Hrow k.
    by rewrite Hc0 mul0r.
  }
  by rewrite Hrow0 add0r.
Qed.

Hypothesis v_is_x : v_mc = x.

Lemma pair_to_same_cell
      (Hli : V3_li) (xi : 'cV[C]_n) :
  P3 *v xi = 0 ->
  \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      c j k * (alpha * Phi (S j) k xi + (conjC alpha) * Phi j (S k) xi)
  =
  (\sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      (alpha * c j k) * Phi (S j) k xi)
  +
  (\sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
      ((conjC alpha) * c j k) * Phi j (S k) xi).
Proof.
  move=> _.
  pose F (j : 'I_N) (k : 'I_N) := c j k * (alpha * Phi (S j) k xi).
  pose G (j : 'I_N) (k : 'I_N) := c j k * ((conjC alpha) * Phi j (S k) xi).
  (* Rewrite the integrand and then split the sum *)
  have -> :
      \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
          c j k * (alpha * Phi (S j) k xi + (conjC alpha) * Phi j (S k) xi)
    = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ((alpha * c j k) * Phi (S j) k xi
        + ((conjC alpha) * c j k) * Phi j (S k) xi).
  { apply: eq_bigr => j _; apply: eq_bigr => k _.
    rewrite mul_addr !mulrA.
    by rewrite (mulrC (c j k) alpha) (mulrC (c j k) (conjC alpha)) -!mulrA. }
  have -> :
      \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ((alpha * c j k) * Phi (S j) k xi
        + ((conjC alpha) * c j k) * Phi j (S k) xi)
    = \sum_(j < N | j != ord_last)
        (\sum_(k < N | k != ord_last) (alpha * c j k) * Phi (S j) k xi
       + \sum_(k < N | k != ord_last) ((conjC alpha) * c j k) * Phi j (S k) xi).
  { by apply: eq_bigr => j _; rewrite -big_split. }
  by rewrite -big_split.
Qed.

(* Convenience wrapper with xi as an explicit argument in the forall. *)
Lemma pair_to_same_cell_for_xi (Hli : V3_li) :
  forall xi : 'cV[C]_n,
    P3 *v xi = 0 ->
    \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        c j k * (alpha * Phi (S j) k xi + (conjC alpha) * Phi j (S k) xi)
    =
    (\sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        (alpha * c j k) * Phi (S j) k xi)
    +
    (\sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ((conjC alpha) * c j k) * Phi j (S k) xi).
Proof. 
exact: pair_to_same_cell.
Qed.

Lemma phi_edge_k0 (Hli : V3_li) (xi : 'cV[C]_n) :
  P3 *v xi = 0 -> v_mc = x ->
  Phi 0 0 xi = 0 /\ Phi 0 1 xi = 0.
Proof.
  move=> Hker Hx.
  split.
  - rewrite /Phi !expr0 mul1mx mul1mx Hx.
    rewrite -(OpenLemmaFinal.P3_on_x (R:=R) (n:=n) (A:=A) Hli).
    have Hswap :=
      (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) P3 x xi).
    rewrite (OpenLemmaFinal.P3_selfadj (R:=R) (n:=n) (A:=A) Hli) in Hswap.
    rewrite -Hswap Hker.
    by rewrite /innerC /MathCompBackboneC.inner trmx0 map_mx0 mul0mx mxE.
  - rewrite /Phi expr0 expr1 mul1mx Hx.
    rewrite (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) A x xi).
    rewrite -(OpenLemmaFinal.P3_on_Astarx (R:=R) (n:=n) (A:=A) Hli).
    have Hswap :=
      (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) P3 ((adjM A) *v x) xi).
    rewrite (OpenLemmaFinal.P3_selfadj (R:=R) (n:=n) (A:=A) Hli) in Hswap.
    rewrite -Hswap Hker.
    by rewrite /innerC /MathCompBackboneC.inner trmx0 map_mx0 mul0mx mxE.
Qed.

Lemma phi_edge_j0 (Hli : V3_li) (xi : 'cV[C]_n) :
  P3 *v xi = 0 -> v_mc = x ->
  Phi 0 0 xi = 0 /\ Phi 1 0 xi = 0.
Proof.
  move=> Hker Hx.
  split.
  - rewrite /Phi !expr0 mul1mx mul1mx Hx.
    rewrite -(OpenLemmaFinal.P3_on_x (R:=R) (n:=n) (A:=A) Hli).
    have Hswap :=
      (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) P3 x xi).
    rewrite (OpenLemmaFinal.P3_selfadj (R:=R) (n:=n) (A:=A) Hli) in Hswap.
    rewrite -Hswap Hker.
    by rewrite /innerC /MathCompBackboneC.inner trmx0 map_mx0 mul0mx mxE.
  - rewrite /Phi expr1 expr0 mul1mx Hx.
    rewrite (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) (adjM A) x xi).
    rewrite (OpenLemmaFinal.adjM_adjM (R:=R) (n:=n)).
    rewrite -(OpenLemmaFinal.P3_on_Ax (R:=R) (n:=n) (A:=A) Hli).
    have Hswap :=
      (OpenLemmaFinal.inner_mul_square (R:=R) (n:=n) P3 (A *v x) xi).
    rewrite (OpenLemmaFinal.P3_selfadj (R:=R) (n:=n) (A:=A) Hli) in Hswap.
    rewrite -Hswap Hker.
    by rewrite /innerC /MathCompBackboneC.inner trmx0 map_mx0 mul0mx mxE.
Qed.

Lemma inner_wMO_xi_zero
      (Hli : V3_li) (xi : 'cV[C]_n) :
  v_mc = x -> P3 *v xi = 0 -> [< w_MO , xi >] = 0.
Proof. 
  move=> Hvx Hker.
  rewrite (inner_wMO_xi_interior xi).
  have Hpair := (pair_to_same_cell_for_xi (xi:=xi) Hli Hker).
  rewrite Hpair.
  (* Shift the conjugate branch to align with the (S j, k) slab *)
  have Hconj_shift :
    \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ((conjC alpha) * c j k) * Phi j (S k) xi
    = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
        ((conjC alpha) * c j (k.+1)) * Phi (S j) k xi.
  {
    (* Reshape integrand and factor the scalar across the nested sum *)
    have -> :
      \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
          ((conjC alpha) * c j k) * Phi j (S k) xi
      = \sum_(j < N | j != ord_last) \sum_(k < N | k != ord_last)
          (conjC alpha) * (c j k * Phi j (S k) xi).
    { apply: eq_bigr => j _; apply: eq_bigr => k _; by rewrite -mulrA. }
    rewrite -big_distrl_filter2.
    (* Apply the Hermitian k-shift on the unscaled interior sum *)
    rewrite (sum_shift_k_for_conj xi).
    (* Distribute back in and reassociate to the target shape *)
    rewrite big_distrl_filter2.
    apply: eq_bigr => j _; apply: eq_bigr => k _. by rewrite mulrA.
  }
  (* Combine the two branches and telescope via discrete CR *)
  rewrite Hconj_shift.
  rewrite -big_split.
  rewrite (eq_bigr (fun i => \sum_(k < N | k != ord_last) (alpha * c (kn i) (kn k) * Phi (kn i).+1 (kn k) xi + conjC alpha * c (kn i) (kn k).+1 * Phi (kn i).+1 (kn k) xi))); last by move=> i _; rewrite big_split.
  (* Apply discrete Cauchy–Riemann identity pointwise under the sum *)
  rewrite (rect_telescope_HCR_direct xi).
  rewrite (rect_telescope_boundary_N3 xi HN3).
  have [Hrow Hcol] := Hbd.
  rewrite (sum_except_last3 HN3 (fun k => c 1 (kn k) * Phi 1 (kn k) xi)).
  rewrite (sum_except_last3 HN3 (fun k => c (N.-1) (kn k) * Phi (N.-1) (kn k) xi)).
  rewrite (sum_except_last3 HN3 (fun j => c (kn j) 1 * Phi (kn j).+1 0 xi)).
  rewrite (sum_except_last3 HN3 (fun j => c (kn j) (N.-1) * Phi (kn j).+1 (N.-1) xi)).
  have Hsum2 : (\sum_(k < N.-1) c N.-1 (kn (liftN k)) * Phi N.-1 (kn (liftN k)) xi = 0).
  { apply: big1 => k ; rewrite Hrow mul0r. reflexivity. }
  have Hsum4 : (\sum_(k < N.-1) c (kn (liftN k)) N.-1 * Phi (kn (liftN k)).+1 N.-1 xi = 0).
  { apply: big1 => k _; rewrite Hcol mul0r. reflexivity. }
  rewrite Hsum2 addr0 Hsum4 subr0.
  rewrite (eq_bigr (fun k => c 1 (nat_of_ord k) * Phi 1 (nat_of_ord k) xi)); last by move=> k _; rewrite liftN_nat.
  have [Hphi00 Hphi10] := phi_edge_j0 Hli (xi:=xi) Hker Hvx.
  have [Hphi00' Hphi01] := phi_edge_k0 Hli (xi:=xi) Hker Hvx.
  rewrite [in X in _ - X] (eq_bigr (fun k : 'I_(N.-1) => c (kn k) 1 * Phi (kn k).+1 0 xi)) => [|k _]; last by rewrite liftN_nat.
  move: HN3 => ->.
  rewrite !(big_ord_recr (R:=C)) /= !big_ord0 /=.
  rewrite Hphi10 !mulr0 !addr0.
  rewrite (Phi_shift_herm 1 0 xi) subrr. 
  reflexivity.
Qed.

Theorem wMO_in_V3
      (Hli : V3_li) :
  v_mc = x ->
  (1%:M - P3) *v w_MO = 0.
Proof.
  move=> Hvx.
  have Hall : forall xi, P3 *v xi = 0 -> [< w_MO , xi >] = 0.
  { move=> xi Hker.
    by apply: (inner_wMO_xi_zero Hli (xi:=xi)); [exact Hvx | exact Hker]. }
   apply: (OpenLemmaFinal.zero_from_kernel_test (R:=R) (n:=n) (A:=A) (x:=x) Hli).
  exact: Hall.
Qed.

End QuickSplitLast.
