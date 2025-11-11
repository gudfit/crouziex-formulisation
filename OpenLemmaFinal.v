(* OpenLemmaFinal.v *)
From mathcomp Require Import all_ssreflect all_algebra matrix.
From mathcomp.algebra   Require Import ssrnum.
From mathcomp.real_closed Require Import complex.
From Stdlib Require Import Reals Lia ClassicalChoice.
From mathcomp Require Import order bigop.
From mathcomp Require Import vector.
From mathcomp Require Import ssrnat.
Import Num.Theory ComplexField GRing.Theory Order.TTheory.

From OpenLemma Require Import MathCompBackboneC OpenLemmaQuadraticRestricted.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section FinalOpenLemma.

Variable R : rcfType.
Local Notation C := R[i].
Local Notation "%:CC x" := ((x)%:C : C) (at level 0).
Variable n : nat.

Local Notation M   := 'M[C]_n.
Local Notation vct := 'cV[C]_n.
Local Infix  "*v"  := (@mulmx C n n 1) (at level 40, left associativity).
Local Infix "*m" := (@mulmx C _ _ _) (at level 40, left associativity).

Local Notation adjM := (MathCompBackboneC.adjM (n:=n) (R:=R)).
Local Notation "[< x , y >]" := (MathCompBackboneC.inner (n:=n) (R:=R) x y) (at level 60).

Variable A : M.
Variables x v : vct.

(* We define the “3-vector” matrix whose columns span V3. *)
Definition col1 : vct := x.
Definition col2 : vct := A *v x.
Definition col3 : vct := (adjM A) *v x.

(* B : n x 3, with columns [x | A x | A* x] *)
Definition B : 'M[C]_(n, 3) :=
  \matrix_(i < n, j < 3)
     (if j == 0 then col1 i 0
      else if j == 1 then col2 i 0
           else col3 i 0).

(* Conjugate-transpose of a rectangular matrix: *)
Definition adjNM (X : 'M[C]_(n,3)) : 'M[C]_(3,n) :=
  (map_mx conjC X)^T.

(* Gram matrix and the canonical orthogonal projector onto span(B): *)
Definition Gram : 'M[C]_3 := (adjNM B) *m B.

Definition V3_li : Prop :=
  forall (a1 a2 a3 : C),
    a1 *: col1 + a2 *: col2 + a3 *: col3 = 0 ->
    a1 = 0 /\ a2 = 0 /\ a3 = 0.

Definition invertible (X : 'M[C]_3) : Prop :=
  exists Y : 'M[C]_3,
    @mulmx C 3 3 3 X Y = 1%:M /\ @mulmx C 3 3 3 Y X = 1%:M.

Lemma invertible_unitmx (X : 'M[C]_3) :
  X \in unitmx -> invertible X.
Proof.
  move=> HX.
  exists (invmx X); split.
  - by apply: mulmxV.
  - by apply: mulVmx.
Qed.

Definition lincomb3 (a : 'cV[C]_3) : vct :=
  (a 0 0) *: col1 + (a 1 0) *: col2 + (a 2 0) *: col3.
  
Lemma lincomb3_inj (Hli : V3_li) (a : 'cV[C]_3) :
  lincomb3 a = 0 -> a = 0.
Proof.
  move=> Ha.
  have /(Hli (a 0 0) (a 1 0) (a 2 0)) : lincomb3 a = 0 by [].
  move=> [Ha1 [Ha2 Ha3]].
  apply/matrixP => i j.
  have -> : j = ord0 by apply/ord1. case: i => [k Hk].
  case: k Hk => [|[|[|k]]] Hk; simpl.
  - have -> : Ordinal Hk = (0 : 'I_3). apply: ord_inj.
    by []. by rewrite Ha1 !mxE.
  - have -> : Ordinal Hk = (1 : 'I_3). apply: ord_inj.
    by []. by rewrite Ha2 !mxE.
  - have -> : Ordinal Hk = (2 : 'I_3). apply: ord_inj.
    by []. by rewrite Ha3 !mxE.
  - move: Hk. by move=> Hk.
Qed.

Local Notation innern :=
  (MathCompBackboneC.inner (n:=n) (R:=R)).
Local Notation inner3 :=
  (MathCompBackboneC.inner (n:=3) (R:=R)).

Lemma adjNM_mxE (X : 'M[C]_(n,3)) (i : 'I_3) (j : 'I_n) :
  (adjNM X) i j = conjC (X j i).
Proof.
  rewrite /adjNM.
  rewrite !mxE.
  by [].
Qed.

Lemma map_trmx_conj m p (M : 'M[C]_(m, p)) :
  map_mx conjC (trmx M) = trmx (map_mx conjC M).
Proof.
  apply/matrixP => i j.
  by rewrite !mxE.
Qed.

Lemma map_mulmx_conj m p q (M : 'M[C]_(m, p)) (N : 'M[C]_(p, q)) :
  map_mx conjC (mulmx M N) =
  mulmx (map_mx conjC M) (map_mx conjC N).
Proof.
  apply/matrixP => i j.
  rewrite !mxE (GRing.Theory.rmorph_sum (R := C) (S := C)) /=.
  apply: eq_bigr => k _.
  by rewrite !mxE GRing.Theory.rmorphM.
Qed.

Lemma adjNM_mul_rect (X : 'M[C]_(n,3)) (c : 'cV[C]_3) :
  map_mx conjC (trmx (mulmx X c)) =
  mulmx (map_mx conjC (trmx c)) (adjNM X).
Proof.
Proof.
  rewrite /adjNM.
  rewrite map_trmx_conj.
  rewrite /adjNM !map_trmx_conj map_mulmx_conj trmx_mul.
  rewrite -map_trmx_conj.
  reflexivity.
Qed.

Lemma inner_adjNM (X : 'M[C]_(n,3)) (w : vct) (c : 'cV[C]_3) :
  [< w , X *m c >] = inner3 (adjNM X *m w) c.
Proof.
  rewrite /innern /inner3 /MathCompBackboneC.inner.
  rewrite adjNM_mul_rect.
  rewrite mulmxA.
  reflexivity.
Qed.

Lemma Gram_mul (a : 'cV[C]_3) :
  Gram *m a = adjNM B *m (B *m a).
Proof.
  by rewrite /Gram mulmxA.
Qed.

Lemma Gram_2vars (a1 a2 : 'cV[C]_3) :
  [< B *m a1 , B *m a2 >] = inner3 (Gram *m a1) a2.
Proof.
  rewrite inner_adjNM.
  by rewrite -Gram_mul.
Qed.


Lemma Gram_quadratic_form (a : 'cV[C]_3) :
  [< B *m a , B *m a >] = inner3 (Gram *m a) a.
Proof.
  exact: Gram_2vars.
Qed.

Lemma inner_self_sum (y : vct) :
  [< y , y >] = \sum_(i < n) (conjC (y i 0) * y i 0).
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  rewrite mxE.
  apply: eq_bigr => k _.
  by rewrite !mxE.
Qed.


Lemma conj_mul_is_real_nonneg (z : C) :
  conjC z * z \is Num.real /\ 0 <= conjC z * z.
Proof.
  have Hzge0 : 0 <= conjC z * z.
  { have := mul_conjC_ge0 z. by rewrite mulrC. }
  split.
  - rewrite CrealE; apply/eqP. exact: geC0_conj Hzge0.
  - exact: Hzge0.
Qed.

Definition diag_term (y : vct) (i : 'I_n) : C :=
  conjC (y i 0) * y i 0.

Lemma inner_self_real_sumC (y : vct) :
  [< y , y >] \is Num.real /\
  exists f : 'I_n -> C,
    (forall i, f i \is Num.real /\ 0 <= f i) /\
    [< y , y >] = \sum_(i < n) (f i).
Proof.
  split.
  - rewrite inner_self_sum.
    apply: rpred_sum => i _.
    have [Hreal_i _] := conj_mul_is_real_nonneg (y i 0).
    exact: Hreal_i.
  - exists (fun i => conjC (y i 0) * y i 0); split.
    + move=> i.
      have [Hreal_i Hge0_i] := conj_mul_is_real_nonneg (y i 0).
      by split.
    + by rewrite inner_self_sum.
Qed.

Lemma real_as_ReC (z : C) :
  z \is Num.real -> z = 'Re z.
Proof.
  by move/Creal_ReP.
Qed.

Lemma real_as_ReC_sym (z : C) :
  z \is Num.real -> 'Re z = z.
Proof. move=> Hz; by symmetry; apply: real_as_ReC. Qed.

Lemma ge0_Re_of_real (z : C) :
  z \is Num.real -> 0 <= z -> 0 <= 'Re z.
Proof.
  move=> Hz Hzge0.
  have -> : 'Re z = z by apply: real_as_ReC_sym.
  exact: Hzge0.
Qed.

Lemma real_ge0_as_R (z : C) :
  z \is Num.real -> 0 <= z ->
  exists r : R, 0 <= r /\ z = r%:C.
Proof.
  move=> Hz Hzge0.
  have [r Hr] : exists r : R, z = r%:C.
    by move/complex_realP : Hz.
  have Hr_ge0C : 0 <= r%:C by rewrite -Hr.
  have Hr_ge0 : 0 <= r by move: Hr_ge0C; rewrite lecR.
  exists r; split; [exact Hr_ge0 | exact Hr].
Qed.

Lemma exists_real_family
      (g : 'I_n -> C)
      (Hexists : forall i : 'I_n,
         exists r : R, 0 <= r /\ g i = r%:C) :
  exists f : 'I_n -> R,
    forall i, 0 <= f i /\ g i = (f i)%:C.
Proof.
  apply: (@choice 'I_n R (fun i r => 0 <= r /\ g i = r%:C)).
  exact Hexists.
Qed.

Lemma sum_g_as_sum_fC
      (g : 'I_n -> C) (f : 'I_n -> R) :
  (forall i, g i = (f i)%:C) ->
  \sum_(i < n) g i = (\sum_(i < n) f i)%:C.
Proof.
  move=> Hgf.
  have -> : \sum_(i < n) g i = \sum_(i < n) (f i)%:C.
  { apply: eq_bigr => i _.
    exact: Hgf. }
  by rewrite -rmorph_sum.
Qed.

Lemma sum_real_family_as_R
      (g : 'I_n -> C) :
  (forall i, g i \is Num.real /\ 0 <= g i) ->
  exists f : 'I_n -> R,
    (forall i, 0 <= f i) /\
    \sum_(i < n) g i = (\sum_(i < n) f i)%:C.
Proof.
  move=> Hg.
  have Hexists : forall i : 'I_n, exists r : R, 0 <= r /\ g i = r%:C.
  { move=> i.
    have [Hreal_i Hge0_i] := Hg i.
    exact: (real_ge0_as_R Hreal_i Hge0_i).
  }

  have [f Hf] := exists_real_family Hexists.
  exists f; split.
  - (* each f i is >= 0 *)
    move=> i.
    have [Hf_ge0 _] := Hf i.
    exact: Hf_ge0.
  - 
    apply: sum_g_as_sum_fC => i.
    have [_ Hgf_i] := Hf i.
    exact: Hgf_i.
Qed.

Lemma inner_self_real_sum (y : vct) :
  [< y , y >] \is Num.real /\
  exists f : 'I_n -> R,
    (forall i, 0 <= f i) /\
    [< y , y >] = (\sum_(i < n) (f i))%:C.
Proof.
  have [Hy_real [g [Hg Hy_eq]]] := inner_self_real_sumC y.
  split.
  - exact Hy_real.
  - have [f [Hf_ge0 Hsum_eq]] := sum_real_family_as_R Hg.
    exists f; split.
    + exact Hf_ge0.
    + by rewrite Hy_eq Hsum_eq.
Qed.

Lemma le_add_nonneg (c y : R) :
  0 <= y -> c <= c + y.
Proof.
  move=> Hy.
  rewrite -subr_ge0.
  rewrite addrC addKr.
  exact: Hy.
Qed.

Lemma sum_ge0_eq0 (f : 'I_n -> R) :
  (forall i, 0 <= f i) ->
  \sum_(i < n) f i = 0 ->
  forall i, f i = 0.
Proof.
  move=> Hge0 Hsum i.
  have Hdecomp := Hsum.
  rewrite (bigD1 i) //= in Hdecomp.
  set S := \sum_(j < n | j != i) f j in Hdecomp.
  have HS_ge0 : 0 <= S.
  { subst S.
    apply: sumr_ge0 => j _.
    exact: Hge0. }
  have HfiS_eq0 : f i + S = 0 := Hdecomp.
  have Hfi_le_fiS : f i <= f i + S.
  { apply: le_add_nonneg.
  exact: HS_ge0. }
  have Hfi_le0 : f i <= 0.
  { have H := Hfi_le_fiS. by rewrite HfiS_eq0 in H. }
  have H0_le_fi : 0 <= f i.
  { exact: Hge0. }
  apply/eqP; rewrite eq_le; apply/andP; split; [exact: Hfi_le0 | exact: H0_le_fi].
Qed.

Lemma mul_conjC (z : C) :
  z * conjC z = 'Re z ^+ 2 + 'Im z ^+ 2.
Proof. by rewrite -normCK normC2_Re_Im. Qed.
  
Lemma mul_conjC_ReImC (z : C) :
  z * conjC z = (('Re z)^+ 2 + ('Im z)^+ 2 : C).
Proof. exact: mul_conjC. Qed.

Lemma Re_mul_conjC (z : C) :
      'Re (z * conjC z) = ('Re z)^+ 2 + ('Im z)^+ 2.
Proof. 
  have [Hz_real _] := conj_mul_is_real_nonneg z.
  have -> : 'Re (z * conjC z) = z * conjC z.
  { apply: real_as_ReC_sym.
     by rewrite mulrC in Hz_real. }
  exact: mul_conjC.
Qed.

Lemma conj_mul_eq0 (z : C) :
  conjC z * z = 0 -> z = 0.
Proof.
  move=> Hz.
  case: (eqVneq z 0) => [-> //|Hz0].
  have Hz' : z * conjC z = 0 by rewrite mulrC in Hz.
  have H := congr1 (fun t => z^-1 * t) Hz'.
  have Hz_unit : z \is a GRing.unit by rewrite unitfE.
  rewrite mulr0 mulrA (mulVr Hz_unit) mul1r in H.
  have -> : z = conjC (conjC z) by rewrite conjCK.
  by rewrite H conjC0.
Qed.

Lemma r2c_inj_eq0 (r : R) :
  ((r%:C : C) = 0) -> r = 0.
Proof.
  move=> Hr0.
  case: (eqVneq r 0) => [-> // | r0].
  suff : False by [].
  have H := congr1 (fun z : C => (r^-1)%:C * z) Hr0.
  move: H; rewrite mulr0 -rmorphM (mulVf r0) => H.
  have H1 : (1 : C) = 0 by move: H; rewrite rmorph1.
  by move/eqP: H1; apply/negP: (@oner_neq0 C).
Qed.

Lemma sum_real_nonneg_eq0 (g : 'I_n -> C) :
  (forall i, g i \is Num.real /\ 0 <= g i) ->
  \sum_(i < n) g i = 0 ->
  forall i, g i = 0.
Proof.
  move=> Hg Hsum i0.
  have Hexists : forall i, exists r : R, 0 <= r /\ g i = r%:C.
  { move=> i. by have [Hr Hge] := Hg i; apply: (real_ge0_as_R Hr Hge). }
  have [f Hf] := exists_real_family Hexists.
  have Hf_ge0 : forall i, 0 <= f i by move=> i; case: (Hf i).
  have Hgf    : forall i, g i = (f i)%:C by move=> i; case: (Hf i).
  have HsumC : \sum_(i < n) g i = (\sum_(i < n) f i)%:C.
  { apply: sum_g_as_sum_fC => i; exact: Hgf. }
  have HsumR : \sum_(i < n) f i = 0.
  { apply: r2c_inj_eq0.
    by rewrite -HsumC Hsum. }
  have Hfi0 : f i0 = 0 by apply: (sum_ge0_eq0 Hf_ge0 HsumR).
  by rewrite (Hgf i0) Hfi0 rmorph0.
Qed.

Lemma inner_diag_terms_real_nonneg (y : vct) (i : 'I_n) :
  diag_term y i \is Num.real /\ 0 <= diag_term y i.
Proof.
  by rewrite /diag_term; apply: conj_mul_is_real_nonneg.
Qed.

Lemma inner_self_eq0_all_diag0 (y : vct) :
  [< y , y >] = 0 -> forall i, diag_term y i = 0.
Proof.
  move=> Hy0 i.
  have Hall : forall j : 'I_n, diag_term y j = 0.
  { apply: (sum_real_nonneg_eq0 (g := fun j : 'I_n => diag_term y j)).
    - by move=> j; apply: inner_diag_terms_real_nonneg.
    - by rewrite /diag_term -inner_self_sum Hy0. }
  exact: Hall i.
Qed.

Lemma inner_self_eq0_implies0 (y : vct) :
  [< y , y >] = 0 -> y = 0.
Proof.
  move=> Hy0; apply/matrixP => i j.
  have -> : j = ord0 by apply/ord1.
  have Hdiag0i : diag_term y i = 0 := inner_self_eq0_all_diag0 Hy0 i.
  have Hyi0 : y i 0 = 0.
  { apply: conj_mul_eq0. by rewrite /diag_term in Hdiag0i. }
  by rewrite !mxE Hyi0.
Qed.

Lemma inner3_0l (a : 'cV[C]_3) : inner3 0 a = 0.
Proof.
  rewrite /inner3 /MathCompBackboneC.inner mxE.
  rewrite big1 // => j _.
  by rewrite !mxE mulr0.
Qed.

Lemma big_ord3C (F : 'I_3 -> C) :
  \sum_(j < 3) F j = F (0 : 'I_3) + F (1 : 'I_3) + F (2 : 'I_3).
Proof.
  rewrite (big_ord_recl (R:=C)) /=.
  rewrite (big_ord_recl (R:=C)) /=.
  rewrite big_ord1 /=.
  have -> : lift ord0 ord0 = (1 : 'I_3) by apply/ord_inj.
  have -> : lift ord0 (lift ord0 ord0) = (2 : 'I_3) by apply/ord_inj.
  by rewrite addrA.
Qed.

Lemma B_col0E i : B i (0 : 'I_3) = col1 i 0.
Proof. by rewrite /B !mxE (eqxx). Qed.

Lemma B_col1E i : B i (1 : 'I_3) = col2 i 0.
Proof.
  rewrite /B !mxE.
  have H10 : (1 : 'I_3) != 0.
  { apply/eqP => H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H10) eqxx.
Qed.

Lemma B_col2E i : B i (2 : 'I_3) = col3 i 0.
Proof.
  rewrite /B !mxE.
  have H20 : (2 : 'I_3) != 0.
  { apply/eqP => H; move: (congr1 val H); discriminate. }
  have H21 : (2 : 'I_3) != 1.
  { apply/eqP => H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H20) (negbTE H21).
Qed.



Lemma B_mul_lincomb_entry (a : 'cV[C]_3) (i : 'I_n) :
  (B *m a) i 0
    = (a 0 0) * col1 i 0
    + (a 1 0) * col2 i 0
    + (a 2 0) * col3 i 0.
Proof.
  rewrite mxE.
  pose F := fun j : 'I_3 => B i j * a j 0.
  rewrite (big_ord_recl (R:=C) (idx:=0) (op:=+%R) _
                          (fun j : 'I_3 => F j)) /=.
  rewrite (big_ord_recl (R:=C) (idx:=0) (op:=+%R) _
                          (fun j : 'I_2 => F (lift ord0 j))) /=.
  rewrite big_ord1 /=.
  have -> : lift ord0 ord0 = (1 : 'I_3) by apply/ord_inj.
  have -> : lift ord0 (lift ord0 ord0) = (2 : 'I_3) by apply/ord_inj.
  rewrite /F.
  have -> : B i (0 : 'I_3) * a 0 0 = (a 0 0) * col1 i 0 by rewrite B_col0E mulrC.
  have -> : B i (1 : 'I_3) * a 1 0 = (a 1 0) * col2 i 0 by rewrite B_col1E mulrC.
  have -> : B i (2 : 'I_3) * a 2 0 = (a 2 0) * col3 i 0 by rewrite B_col2E mulrC.
  by rewrite -addrA.
Qed.

Lemma lincomb3_entry (a : 'cV[C]_3) (i : 'I_n) :
  (lincomb3 a) i 0
    = (a 0 0) * col1 i 0
    + (a 1 0) * col2 i 0
    + (a 2 0) * col3 i 0.
Proof.
  rewrite /lincomb3 !mxE.
  by rewrite -addrA.
Qed.


Lemma B_mul_lincomb (a : 'cV[C]_3) :
  B *m a = lincomb3 a.
Proof.
  apply/matrixP => i j.
  have -> : j = ord0 by apply/ord1.
  by rewrite B_mul_lincomb_entry lincomb3_entry.
Qed.

Lemma Gram_ker0 (Hli : V3_li) (a : 'cV[C]_3) :
  Gram *m a = 0 -> a = 0.
Proof.
  move=> HGa0.
  have Hquad := Gram_quadratic_form a.
  rewrite HGa0 inner3_0l in Hquad.
  have HBa0 : B *m a = 0 by apply: inner_self_eq0_implies0; exact Hquad.
  have Hlin0 : lincomb3 a = 0.
  { have H := HBa0. rewrite (B_mul_lincomb a) in H. exact H. }
  apply: (lincomb3_inj Hli).
  exact: Hlin0.
Qed.

Lemma Gram_unit_from_li :
  V3_li -> Gram \in unitmx.
Proof.
  move=> Hli.
  rewrite unitmxE.
  apply/negP => Hsing.                                   (* Hsing : (\det Gram == 0) *)
  have Hsing_tr : (\det (trmx Gram) == 0) by rewrite det_tr.
  have /det0P [a [aNZ aKer]] := Hsing_tr.
  have aKerT := congr1 trmx aKer; rewrite trmx_mul trmxK trmx0 in aKerT.
  have aT0 : trmx a = 0 by apply: (Gram_ker0 Hli (a:=trmx a)); exact: aKerT.
  by move: aNZ; rewrite -{1}(trmxK a) aT0 trmx0 eqxx.
Qed.

Lemma Gram_inv_exists :
  V3_li -> invertible Gram.
Proof.
  move=> Hli.
  apply: invertible_unitmx.
  apply: Gram_unit_from_li.
  exact Hli.
Qed.

Definition P3 : M := B *m (invmx Gram) *m (adjNM B).
Definition inV3 (y : vct) : Prop := P3 *v y = y.
Definition e0 : 'cV[C]_3 := \col_(i < 3) (if i == (0 : 'I_3) then 1 else 0).

Lemma e0_0 : e0 (0 : 'I_3) 0 = 1.
Proof. by rewrite /e0 !mxE eqxx. Qed.

Lemma e0_1 : e0 (1 : 'I_3) 0 = 0.
Proof.
  rewrite /e0 !mxE.
  have H10 : (1 : 'I_3) != 0.
  { apply/eqP => H.
      move: (congr1 val H). 
      by discriminate. }
  by rewrite (negbTE H10).
Qed.

Lemma e0_2 : e0 (2 : 'I_3) 0 = 0.
Proof.
  rewrite /e0 !mxE.
  have H20 : (2 : 'I_3) != 0.
  { apply/eqP => H.
      move: (congr1 val H). 
      by discriminate. }
  by rewrite (negbTE H20).
Qed.

Lemma B_e0 : B *m e0 = x.
Proof.
  apply/matrixP=> i j.
  have -> : j = ord0 by apply/ord1.
  rewrite B_mul_lincomb_entry /col1 e0_0 e0_1 e0_2.
  by rewrite mul1r !mul0r !addr0.
Qed.

Lemma Gram_e0 : Gram *m e0 = adjNM B *m x.
Proof.
  rewrite /Gram -mulmxA.
  by rewrite B_e0.
Qed.

Lemma Gram_invmx_adjB_x (Hli : V3_li) :
  Gram *m (invmx Gram *m (adjNM B *m x)) = adjNM B *m x.
Proof.
  have Hunit : Gram \in unitmx by exact: Gram_unit_from_li Hli.
  by rewrite mulmxA (mulmxV Hunit) mul1mx.
Qed.

Lemma invGram_adjB_x_eq_e0 (Hli : V3_li) :
  invmx Gram *m (adjNM B *m x) = e0.
Proof.
  have Hker :
     Gram *m (invmx Gram *m (adjNM B *m x) - e0) = 0.
  { by rewrite mulmxBr Gram_invmx_adjB_x // Gram_e0 subrr. }
  have Hsub :
     invmx Gram *m (adjNM B *m x) - e0 = 0
    by apply: (Gram_ker0 Hli); exact: Hker.
  move: (congr1 (fun t => t + e0) Hsub).
  by rewrite subrK add0r.
Qed.

Lemma P3_on_x (Hli : V3_li) : P3 *v x = x.
Proof.
  rewrite /P3 -!mulmxA.
  rewrite (invGram_adjB_x_eq_e0 Hli).
  exact: B_e0.
Qed.

Definition e1 : 'cV[C]_3 := \col_(i < 3) (if i == (1 : 'I_3) then 1 else 0).

Lemma e1_0 : e1 (0 : 'I_3) 0 = 0.
Proof.
  rewrite /e1 !mxE.
  have H01 : (0 : 'I_3) != 1.
  { apply/eqP=> H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H01).
Qed.

Lemma e1_1 : e1 (1 : 'I_3) 0 = 1.
Proof. by rewrite /e1 !mxE eqxx. Qed.

Lemma e1_2 : e1 (2 : 'I_3) 0 = 0.
Proof.
  rewrite /e1 !mxE.
  have H21 : (2 : 'I_3) != 1.
  { apply/eqP=> H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H21).
Qed.

Lemma B_e1 : B *m e1 = A *v x.
Proof.
  apply/matrixP=> i j; have -> : j = ord0 by apply/ord1.
  rewrite B_mul_lincomb_entry /col2 e1_0 e1_1 e1_2.
  by rewrite mul0r mul1r mul0r add0r addr0.
Qed.

Lemma Gram_e1 : Gram *m e1 = adjNM B *m (A *v x).
Proof. by rewrite /Gram -mulmxA B_e1. Qed.

Lemma Gram_invmx_adjB (Hli : V3_li) (y : vct) :
  Gram *m (invmx Gram *m (adjNM B *m y)) = adjNM B *m y.
Proof.
  have Hunit : Gram \in unitmx by exact: Gram_unit_from_li Hli.
  by rewrite mulmxA (mulmxV Hunit) mul1mx.
Qed.

Lemma invGram_adjB_Ax_eq_e1 (Hli : V3_li) :
  invmx Gram *m (adjNM B *m (A *v x)) = e1.
Proof.
  have Hker :
     Gram *m (invmx Gram *m (adjNM B *m (A *v x)) - e1) = 0.
  { by rewrite mulmxBr (Gram_invmx_adjB Hli (A *v x)) Gram_e1 subrr. }
  have Hsub :
     invmx Gram *m (adjNM B *m (A *v x)) - e1 = 0
    by apply: (Gram_ker0 Hli); exact: Hker.
  move: (congr1 (fun t => t + e1) Hsub).
  by rewrite subrK add0r.
Qed.

Lemma P3_on_Ax (Hli : V3_li) : P3 *v (A *v x) = A *v x.
Proof.
  by rewrite /P3 -!mulmxA (invGram_adjB_Ax_eq_e1 Hli) B_e1.
Qed.

Definition e2 : 'cV[C]_3 := \col_(i < 3) (if i == (2 : 'I_3) then 1 else 0).

Lemma e2_0 : e2 (0 : 'I_3) 0 = 0.
Proof.
  rewrite /e2 !mxE.
  have H02 : (0 : 'I_3) != 2.
  { apply/eqP=> H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H02).
Qed.

Lemma e2_1 : e2 (1 : 'I_3) 0 = 0.
Proof.
  rewrite /e2 !mxE.
  have H12 : (1 : 'I_3) != 2.
  { apply/eqP=> H; move: (congr1 val H); discriminate. }
  by rewrite (negbTE H12).
Qed.

Lemma e2_2 : e2 (2 : 'I_3) 0 = 1.
Proof. by rewrite /e2 !mxE eqxx. Qed.

Lemma B_e2 : B *m e2 = (adjM A) *v x.
Proof.
  apply/matrixP=> i j; have -> : j = ord0 by apply/ord1.
  rewrite B_mul_lincomb_entry /col3 e2_0 e2_1 e2_2.
  by rewrite mul0r mul0r mul1r !add0r.
Qed.

Lemma Gram_e2 : Gram *m e2 = adjNM B *m ((adjM A) *v x).
Proof. by rewrite /Gram -mulmxA B_e2. Qed.

Lemma invGram_adjB_Astarx_eq_e2 (Hli : V3_li) :
  invmx Gram *m (adjNM B *m ((adjM A) *v x)) = e2.
Proof.
  have Hker :
     Gram *m (invmx Gram *m (adjNM B *m ((adjM A) *v x)) - e2) = 0.
  { by rewrite mulmxBr (Gram_invmx_adjB Hli ((adjM A) *v x)) Gram_e2 subrr. }
  have Hsub :
     invmx Gram *m (adjNM B *m ((adjM A) *v x)) - e2 = 0
    by apply: (Gram_ker0 Hli).
  move: (congr1 (fun t => t + e2) Hsub).
  by rewrite subrK add0r.
Qed.

Lemma P3_on_Astarx (Hli : V3_li) : P3 *v ((adjM A) *v x) = (adjM A) *v x.
Proof.
  by rewrite /P3 -!mulmxA (invGram_adjB_Astarx_eq_e2 Hli) B_e2.
Qed.

Lemma adjB_B_is_Gram : adjNM B *m B = Gram.
Proof. by rewrite /Gram. Qed.

Lemma invGram_Gram_is1 (Hli : V3_li) :
  invmx Gram *m Gram = 1%:M.
Proof.
  have Hun : Gram \in unitmx by exact: Gram_unit_from_li Hli.
  exact: (mulVmx Hun).
Qed.

Lemma P3_idem' (Hli : V3_li) : P3 *m P3 = P3.
Proof.
  rewrite /P3.
  set X := B *m invmx Gram.
  set Y := adjNM B.
  rewrite mulmxA.
  rewrite [X *m Y *m X] mulmxA.
  rewrite -[(X *m Y) *m B] mulmxA.
  rewrite [Y *m B] adjB_B_is_Gram.
  rewrite -[(X *m Gram) *m invmx Gram] mulmxA.
  rewrite (mulmxV (Gram_unit_from_li Hli)) mulmx1.
  by [].
Qed.

Local Notation adj3 := (MathCompBackboneC.adjM (n:=3) (R:=R)).

Lemma map_conj_invol m p (M : 'M[C]_(m,p)) :
  map_mx conjC (map_mx conjC M) = M.
Proof. by apply/matrixP=> i j; rewrite !mxE conjCK. Qed.

Lemma trmx_map_conj_adjNM (X : 'M[C]_(n,3)) :
  trmx (map_mx conjC (adjNM X)) = X.
Proof.
  rewrite /adjNM map_trmx_conj trmxK map_conj_invol; reflexivity.
Qed.

Lemma adj3_mul (U V : 'M[C]_3) :
  adj3 (U *m V) = (adj3 V) *m (adj3 U).
Proof. by rewrite /adj3 map_mulmx_conj trmx_mul. Qed.

Lemma adj3_id : adj3 1%:M = 1%:M.
Proof.
  rewrite /adj3 /MathCompBackboneC.adjM.
  apply/matrixP=> i j; rewrite !mxE eq_sym.
  by case: eqP=> _; rewrite ?rmorph1 ?rmorph0.
Qed.

Lemma Gram_selfadj : adj3 Gram = Gram.
Proof.
  rewrite /Gram /adj3.
  rewrite map_mulmx_conj trmx_mul.
  have -> : trmx (map_mx conjC B) = adjNM B by rewrite /adjNM.
  rewrite trmx_map_conj_adjNM.
  by [].
Qed.

Lemma adj3_invmx (M : 'M[C]_3) :
  M \in unitmx -> adj3 (invmx M) = invmx (adj3 M).
Proof.
  move=> Hun.
  have HLR : (adj3 M) *m (adj3 (invmx M)) = 1%:M.
    by rewrite -adj3_mul (mulVmx Hun) adj3_id.
  have HRL : (adj3 (invmx M)) *m (adj3 M) = 1%:M.
    by rewrite -adj3_mul (mulmxV Hun) adj3_id.
  have Hun' : adj3 M \in unitmx.
  { rewrite unitmxE; apply/negP=> /eqP Hza.
    have Hdet := congr1 (fun X : 'M_3 => \det X) HLR.
    have Hdet' : \det (adj3 M) * \det (adj3 (invmx M)) = 1 by move: Hdet; rewrite det_mulmx det1.
    have H01 : (0 : C) = 1 by move: Hdet'; rewrite Hza mul0r.
      by move/negP: (@oner_neq0 C); rewrite -H01.  }
  have Hleft := congr1 (fun X : 'M_3 => invmx (adj3 M) *m X) HLR.
  by move: Hleft; rewrite mulmxA (mulVmx Hun') mul1mx mulmx1.
Qed.

Lemma adjM_sandwich (M3 : 'M[C]_3) :
  adjM (B *m M3 *m adjNM B) = B *m (adj3 M3) *m adjNM B.
Proof.
  rewrite /MathCompBackboneC.adjM.
  rewrite map_mulmx_conj trmx_mul.
  rewrite map_mulmx_conj.
  rewrite trmx_mul.
  rewrite trmx_map_conj_adjNM.
  by rewrite /adjNM -mulmxA.
Qed.

Lemma P3_selfadj (Hli : V3_li) : adjM P3 = P3.
Proof.
  rewrite /P3.
  rewrite adjM_sandwich.
  have HunG : Gram \in unitmx by apply: Gram_unit_from_li.
  rewrite (adj3_invmx HunG).
  by rewrite Gram_selfadj.
Qed.

Lemma adjM_mul (U V : M) : adjM (U *m V) = (adjM V) *m (adjM U).
Proof. by rewrite /adjM map_mulmx_conj trmx_mul. Qed.

Lemma adjM_idn : adjM (1%:M : M) = 1%:M.
Proof.
  rewrite /adjM; apply/matrixP=> i j.
  rewrite !mxE eq_sym.
  by case: eqP=> _; rewrite ?rmorph1 ?rmorph0.
Qed.

Lemma adjM_pow k : adjM (A ^+ k) = (adjM A) ^+ k.
Proof.
  elim: k => [|k IH]; first by rewrite !expr0 adjM_idn.
  by rewrite exprS adjM_mul IH exprSr.
Qed.

Definition A3 : 'M[C]_3 := invmx Gram *m (adjNM B) *m A *m B.

Lemma P3_on_B (Hli : V3_li) : P3 *m B = B.
Proof.
  rewrite /P3 -!mulmxA adjB_B_is_Gram.
  by rewrite (invGram_Gram_is1 Hli) mulmx1.
Qed.

Lemma compress_A (a : 'cV[C]_3) :
  P3 *v (A *v (B *m a)) = B *m (A3 *m a).
Proof. by rewrite /P3 !mulmxA. Qed.

Lemma adj3_adjNBAB :
  adj3 ((adjNM B) *m A *m B) = (adjNM B) *m (adjM A) *m B.
Proof.
  rewrite /adj3.
  rewrite map_mulmx_conj trmx_mul.
  rewrite map_mulmx_conj trmx_mul.
  by rewrite /adjNM /adjM trmx_map_conj_adjNM -mulmxA.
Qed.

Lemma adj3_A3 (Hli : V3_li) :
  adj3 A3 = (adjNM B) *m (adjM A) *m B *m invmx Gram.
Proof.
  rewrite /A3.
  have HunG : Gram \in unitmx by apply: Gram_unit_from_li.
  set T := (adjNM B *m A *m B).
  have -> : invmx Gram *m adjNM B *m A *m B = invmx Gram *m T.
    by rewrite /T !mulmxA.
  rewrite adj3_mul.
  rewrite /T adj3_adjNBAB.
  rewrite (adj3_invmx HunG) Gram_selfadj.
  by rewrite -!mulmxA.
Qed.

Lemma compress_Astar (a : 'cV[C]_3) :
  P3 *v ((adjM A) *v (B *m a))
    = B *m ((invmx Gram *m (adjNM B) *m (adjM A) *m B) *m a).
Proof. by rewrite /P3 !mulmxA. Qed.

Lemma compress_Astar_via_adj3 (Hli : V3_li) (a : 'cV[C]_3) :
  P3 *v ((adjM A) *v (B *m a))
    = B *m ((invmx Gram *m (adj3 A3) *m Gram) *m a).
Proof.
  rewrite compress_Astar.
  have -> :
      invmx Gram *m adjNM B *m (adjM A) *m B
    = invmx Gram *m (adj3 A3) *m Gram.
  { symmetry.
    rewrite (adj3_A3 Hli).
    rewrite -!mulmxA.
    rewrite (invGram_Gram_is1 Hli) mulmx1.
    done.
  }
  by [].
Qed.

Lemma compress_Astar_orthonormal
      (Hli : V3_li) (Horth : Gram = 1%:M) (a : 'cV[C]_3) :
  P3 *v ((adjM A) *v (B *m a)) = B *m ((adj3 A3) *m a).
Proof.
  rewrite (compress_Astar_via_adj3 Hli a).
  rewrite Horth invmx1 mul1mx mulmx1.
  reflexivity.
Qed.

Lemma compress_A_iter_pow (p : nat) :
  forall a : 'cV[C]_3,
    ((P3 *m A) ^+ p) *v (B *m a) = B *m ((A3 ^+ p) *m a).
Proof.
  elim: p => [|p IHp] a.
  - by rewrite !expr0 !mul1mx.
  - rewrite exprSr -mulmxA.
    have -> : (P3 *m A) *m (B *m a) = P3 *m (A *m (B *m a))
      by rewrite -mulmxA.
    rewrite compress_A.
    rewrite (IHp (A3 *m a)).
    apply: (congr1 (fun M => B *m M)).
    by rewrite mulmxA -[A3 ^+ p *m A3]exprSr.
Qed.

Definition leak : 'M[C]_(n,3) := (1%:M - P3) *m A *m B.

Lemma split_id_P3 : 1%:M = P3 + (1%:M - P3).
Proof. by rewrite addrC subrK. Qed.

Lemma split_by_P3 (y : vct) :
  y = P3 *m y + (1%:M - P3) *m y.
Proof.
have -> : y = 1%:M *m y by rewrite mul1mx.
rewrite [in LHS]split_id_P3 [in LHS]mulmxDl.
by rewrite !mul1mx.
Qed.

Lemma leak_apply (a : 'cV[C]_3) :
  leak *m a = (1%:M - P3) *m A *m (B *m a).
Proof. by rewrite /leak !mulmxA. Qed.

Lemma rebracket_right (M N : 'M[C]_n) (y : 'cV[C]_n) :
  M *m (N *m y) = (M *m N) *m y.
Proof. by rewrite -mulmxA. Qed.

Lemma leak_apply' (a : 'cV[C]_3) :
  (1%:M - P3) *m (A *m (B *m a)) = leak *m a.
Proof. by rewrite rebracket_right -leak_apply. Qed.

Lemma step_decompose_v (a : 'cV[C]_3) :
  A *v (B *m a) = B *m (A3 *m a) + leak *m a.
Proof.
  have -> := split_by_P3 (A *v (B *m a)).
  rewrite compress_A leak_apply'.
  done.
Qed.

Lemma A3_succ_on (k : nat) (a : 'cV[C]_3) :
  (A3 ^+ k) *m (A3 *m a) = (A3 ^+ (k.+1)) *m a.
Proof.
  rewrite mulmxA.
  rewrite -[ (A3 ^+ k) *m A3 ] exprSr. 
  done.
Qed.

Lemma B_A3_head_promote (p : nat) (a : 'cV[C]_3) :
  B *m (A3 ^+ p *m (A3 *m a)) = B *m (A3 ^+ p.+1 *m a).
Proof.
  apply: (congr1 (fun M => B *m M)).
  exact: A3_succ_on.
Qed.

Local Open Scope nat_scope.

Lemma lift0_val (p : nat) (k : 'I_p) :
  (lift ord0 k : nat) = k.+1.
Proof. by case: k => [k Hk]. Qed.

Lemma subn_lift0E (p : nat) (k : 'I_p) :
  (p - (lift ord0 k)) = (p.-1 - k).
Proof. 
have -> : (lift ord0 k : nat) = k.+1 by case: k => m Hm //=.
  rewrite subnS.
  have lt_kp : k < p by exact: ltn_ord.
  have pk_gt0 : 0 < p - k by rewrite lt0n subn_eq0 -ltnNge lt_kp.
  by rewrite predn_sub.
Qed.

Lemma expr_lift0E (M : 'M[C]_3) (p : nat) (k : 'I_p) :
  M ^+ (lift ord0 k) = M ^+ (k.+1).
Proof. by rewrite lift0_val. Qed.

Lemma F_headE (p : nat) (a : 'cV[C]_3) :
  let F := fun k : 'I_(p.+1) =>
              A ^+ (p - k) *m leak *m ((A3 ^+ k) *m a) in
  F ord0 = A ^+ p *m leak *m a.
Proof. by rewrite /= subn0 expr0 mul1mx. Qed.

Lemma F_tailE (p : nat) (a : 'cV[C]_3) (k : 'I_p) :
  let F := fun k0 : 'I_(p.+1) =>
              A ^+ (p - k0) *m leak *m ((A3 ^+ k0) *m a) in
  F (lift ord0 k)
  = A ^+ (p.-1 - k) *m leak *m ((A3 ^+ (k.+1)) *m a).
Proof.
  by rewrite /= subn_lift0E expr_lift0E.
Qed.

Local Close Scope nat_scope.

Lemma defect_sum_succ (p : nat) (a : 'cV[C]_3) :
  A ^+ p *m leak *m a
  + \sum_(k < p) A ^+ (p.-1 - k) *m leak *m ((A3 ^+ (k.+1)) *m a)
  = \sum_(k < p.+1) A ^+ (p - k) *m leak *m ((A3 ^+ k) *m a).
Proof.
  set F := fun k0 : 'I_(p.+1) =>
              A ^+ (p - k0) *m leak *m ((A3 ^+ k0) *m a).
  have -> :
      \sum_(k < p.+1) A ^+ (p - k) *m leak *m ((A3 ^+ k) *m a)
    = \sum_(k < p.+1) F k by [].
  rewrite (big_ord_recl (R:='M[C]_(n,1)) (idx:=0) (op:=+%R) _
                         (fun k0 : 'I_(p.+1) => F k0)) /=.
  rewrite /F subn0 expr0 mul1mx.
  have -> :
      \sum_(k < p) F (lift ord0 k)
    = \sum_(k < p)
        A ^+ (p.-1 - k) *m leak *m ((A3 ^+ (k.+1)) *m a).
  by apply: eq_bigr => k _; rewrite /F subn_lift0E expr_lift0E.
  by [].
Qed.

Definition A3_gadj : 'M[C]_3 := invmx Gram *m (adj3 A3) *m Gram.
Definition leak_star : 'M[C]_(n,3) := (1%:M - P3) *m (adjM A) *m B.

Lemma step_decompose_star (Hli : V3_li) (a : 'cV[C]_3) :
  (adjM A) *v (B *m a)
  = B *m (A3_gadj *m a) + leak_star *m a.
Proof.
  have -> := split_by_P3 ((adjM A) *v (B *m a)).
  rewrite (compress_Astar_via_adj3 Hli a).
  rewrite /A3_gadj /leak_star.
  rewrite [X in _ + X]mulmxA.
  rewrite [X in _ + X]mulmxA.
  reflexivity.
Qed.

Lemma A3g_succ_on (k : nat) (a : 'cV[C]_3) :
  (A3_gadj ^+ k) *m (A3_gadj *m a) = (A3_gadj ^+ k.+1) *m a.
Proof.
  rewrite mulmxA.
  rewrite -[(A3_gadj ^+ k) *m A3_gadj] exprSr.
  reflexivity.
Qed.

Local Open Scope nat_scope.

Lemma F_star_headE (q : nat) (a : 'cV[C]_3) :
  let F := fun k0 : 'I_(q.+1) =>
    (adjM A) ^+ (q - k0) *m leak_star *m (A3_gadj ^+ k0 *m a) in
  F ord0 = (adjM A) ^+ q *m leak_star *m a.
Proof. by rewrite /= subn0 expr0 mul1mx. Qed.

Lemma F_star_tailE (q : nat) (a : 'cV[C]_3) (k : 'I_q) :
  let F := fun k0 : 'I_(q.+1) =>
    (adjM A) ^+ (q - k0) *m leak_star *m (A3_gadj ^+ k0 *m a) in
  F (lift ord0 k)
  = (adjM A) ^+ (q.-1 - k) *m leak_star *m (A3_gadj ^+ (k.+1) *m a).
Proof. by rewrite /= subn_lift0E expr_lift0E. Qed.

Local Close Scope nat_scope.

Lemma defect_sum_succ_star (q : nat) (a : 'cV[C]_3) :
  (adjM A) ^+ q *m leak_star *m a
  + \sum_(k < q)
      (adjM A) ^+ (q.-1 - k) *m leak_star *m ((A3_gadj ^+ (k.+1)) *m a)
  = \sum_(k < q.+1)
      (adjM A) ^+ (q - k) *m leak_star *m ((A3_gadj ^+ k) *m a).
Proof.
  set F := fun k0 : 'I_(q.+1) =>
    (adjM A) ^+ (q - k0) *m leak_star *m ((A3_gadj ^+ k0) *m a).
  have -> :
      \sum_(k < q.+1)
        (adjM A) ^+ (q - k) *m leak_star *m ((A3_gadj ^+ k) *m a)
    = \sum_(k < q.+1) F k by [].
  rewrite (big_ord_recl (R:='M[C]_(n,1)) (idx:=0) (op:=+%R)
                        _ (fun k0 : 'I_(q.+1) => F k0)) /=.
  rewrite /F subn0 expr0 mul1mx.
  have -> :
      \sum_(k < q) F (lift ord0 k)
    = \sum_(k < q)
        (adjM A) ^+ (q.-1 - k) *m leak_star
          *m ((A3_gadj ^+ (k.+1)) *m a).
  { apply: eq_bigr => k _.
    by rewrite /F subn_lift0E expr_lift0E. }
  done.
Qed.

Lemma adj_defect_telescope
      (Hli : V3_li) (q : nat) (a : 'cV[C]_3) :
  ((adjM A) ^+ q) *v (B *m a)
  = B *m (A3_gadj ^+ q *m a)
    + \sum_(k < q)
        (adjM A) ^+ (q.-1 - k) *m leak_star *m (A3_gadj ^+ k *m a).
Proof.
  elim: q a => [|q IH] a.
  - by rewrite !expr0 !mul1mx big_ord0 addr0.
  - rewrite exprSr -mulmxA. rewrite (step_decompose_star Hli a).
    rewrite mulmxDr.
    change (((adjM A) ^+ q) *m (B *m (A3_gadj *m a)))
      with (((adjM A) ^+ q) *v (B *m (A3_gadj *m a))).
    rewrite IH.
    have -> :
      B *m (A3_gadj ^+ q *m (A3_gadj *m a))
        = B *m (A3_gadj ^+ q.+1 *m a).
    { apply: (congr1 (fun M => B *m M)). exact: (A3g_succ_on q a). }
    have -> :
      \sum_(k < q)
        (adjM A) ^+ (q.-1 - k) *m leak_star
          *m ((A3_gadj ^+ k) *m (A3_gadj *m a))
      = \sum_(k < q)
        (adjM A) ^+ (q.-1 - k) *m leak_star
          *m ((A3_gadj ^+ (k.+1)) *m a).
    { apply: eq_bigr => k _. by rewrite (A3g_succ_on k a). }
    rewrite -mulmxA.
    have -> :
      adjM A ^+ q *m ((1%:M - P3) *m adjM A *m (B *m a))
      = adjM A ^+ q *m leak_star *m a.
    { rewrite -mulmxA. rewrite -mulmxA.
    rewrite -mulmxA.
    rewrite  mulmxA. 
     reflexivity. }
     rewrite /leak_star.
     rewrite -addrA. rewrite [X in _ + X]addrC.
     rewrite [X in _ + X](defect_sum_succ_star q a).
     reflexivity.
Qed.

Lemma fwd_defect_telescope (p : nat) (a : 'cV[C]_3) :
  A ^+ p *v (B *m a)
  = B *m (A3 ^+ p *m a)
    + \sum_(k < p) A ^+ (p.-1 - k) *m leak *m (A3 ^+ k *m a).
Proof.
  elim: p a => [|p IH] a.
  - by rewrite !expr0 !mul1mx big_ord0 addr0.
  - rewrite exprSr -mulmxA.
    change (A ^+ p *m (A *m (B *m a)))
      with (A ^+ p *m (A *v (B *m a))).
    rewrite (step_decompose_v a). rewrite mulmxDr.
    change (A ^+ p *m (B *m (A3 *m a)))
      with ((A ^+ p) *v (B *m (A3 *m a))).
    rewrite IH.
    have -> :
      B *m (A3 ^+ p *m (A3 *m a)) = B *m (A3 ^+ p.+1 *m a).
   { apply: (congr1 (fun M => B *m M)).
      exact: A3_succ_on. }
    have -> :
      \sum_(k < p) A ^+ (p.-1 - k) *m leak *m ((A3 ^+ k) *m (A3 *m a))
      = \sum_(k < p) A ^+ (p.-1 - k) *m leak *m (A3 ^+ (k.+1) *m a).
    { apply: eq_bigr => k _.
      by rewrite A3_succ_on. }
    rewrite -mulmxA. rewrite -addrA.
    rewrite [X in _ + X]addrC. 
    rewrite [X in _ + (X + _)](_ :
      A ^+ p *m ((1%:M - P3) *m A *m (B *m a))
      = A ^+ p *m leak *m a).
      rewrite [X in _ + X](defect_sum_succ p a).
    reflexivity.
    rewrite -[X in A ^+ p *m X]rebracket_right.
    rewrite leak_apply'.
    by rewrite mulmxA.
Qed.

Lemma mixed_rectangle
      (Hli : V3_li) (p q : nat) (a : 'cV[C]_3) :
  ((adjM A) ^+ q *m A ^+ p) *v (B *m a)
  = B *m ((A3_gadj ^+ q) *m (A3 ^+ p) *m a)
    + \sum_(j < q)
        (adjM A) ^+ (q.-1 - j) *m leak_star
          *m ((A3_gadj ^+ j) *m (A3 ^+ p) *m a)
    + \sum_(k < p)
        ((adjM A) ^+ q) *m A ^+ (p.-1 - k) *m leak *m (A3 ^+ k *m a).
Proof.
  rewrite -mulmxA. 
  rewrite -mulmxA.
  rewrite (fwd_defect_telescope p a).
  rewrite mulmxDr.
  change ((adjM A) ^+ q *m (B *m (A3 ^+ p *m a)))
    with (((adjM A) ^+ q) *v (B *m (A3 ^+ p *m a))).
  rewrite (adj_defect_telescope Hli q (A3 ^+ p *m a)).
  rewrite !mulmxA.
  rewrite mulmx_sumr.
  have -> :
    \sum_(k < q)
      adjM A ^+ (q.-1 - k) *m leak_star *m
        (A3_gadj ^+ k *m (A3 ^+ p *m a))
  = \sum_(k < q)
      adjM A ^+ (q.-1 - k) *m leak_star *m
        (A3_gadj ^+ k *m A3 ^+ p *m a).
  apply: eq_bigr => k _.
  set t := (A3_gadj ^+ k).
  set s := (A3 ^+ p).
  set y := a.
  have -> : t *m (s *m y) = t *m s *m y by rewrite mulmxA.
  by [].
  have -> :
    \sum_(k < p)
      adjM A ^+ q *m (A ^+ (p.-1 - k) *m leak *m (A3 ^+ k *m a))
  = \sum_(k < p)
      adjM A ^+ q *m A ^+ (p.-1 - k) *m leak *m (A3 ^+ k *m a).
    by apply: eq_bigr => k _; rewrite -!mulmxA.
  by [].
Qed.

Lemma pred_lt (n1 : nat) : (0 < n1)%N -> (n1.-1 < n1)%N.
Proof. by move=> npos; rewrite -(ltn_predK npos); apply: ltnSn. Qed.

Variable alpha : C.
Variable N : nat.
Variable c : 'I_N -> 'I_N -> C.
Variable Npos : (0 < N)%N.

Definition Ham : M := alpha *: A + (conjC alpha) *: (adjM A).
Definition w_MO : vct :=
  \sum_(j < N) \sum_(k < N)
      (c j k) *: ((adjM A) ^+ k *v (Ham *v (A ^+ j *v v))).

Lemma adjM_mul_rect (X : M) (w : vct) :
  map_mx conjC (trmx (X *m w)) = map_mx conjC (trmx w) *m (adjM X).
Proof.
  rewrite trmx_mul map_mulmx_conj /adjM.
  have -> : map_mx conjC (trmx X) = trmx (map_mx conjC X)
    by apply: map_trmx_conj.
  reflexivity.
Qed.

Lemma inner_mul_square (M0 : M) (y z : vct) :
  [< y , M0 *v z >] = [< (adjM M0) *v y , z >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  rewrite adjM_mul_rect.
  rewrite mulmxA.
  reflexivity.
Qed.

Lemma map_addmx_conj m p (M1 M2 : 'M[C]_(m,p)) :
  map_mx conjC (M1 + M2) = map_mx conjC M1 + map_mx conjC M2.
Proof.
  apply/matrixP => i j.
  by rewrite !mxE GRing.Theory.rmorphD.
Qed.

Lemma map_opmx_conj m p (M : 'M[C]_(m,p)) :
  map_mx conjC (- M) = - map_mx conjC M.
Proof.
  apply/matrixP => i j.
  by rewrite !mxE GRing.Theory.rmorphN.
Qed.

Lemma adjM_sub (U V : M) :
  adjM (U - V) = adjM U - adjM V.
Proof.
  apply/matrixP => i j.
  rewrite /adjM !mxE.
  by rewrite GRing.Theory.rmorphB.
Qed.


Lemma inner_on_kerP3_rewrite (Hli : V3_li) (y xi : vct) :
  P3 *v xi = 0 -> [< y , xi >] = [< (1%:M - P3) *v y , xi >].
Proof.
  move=> Hker.
  have Hxi : (1%:M - P3) *v xi = xi.
    by rewrite mulmxBl mul1mx Hker subr0.
  rewrite -{2}Hxi.
  rewrite (inner_mul_square (1%:M - P3)).
  rewrite adjM_sub adjM_idn (P3_selfadj Hli).
  rewrite rebracket_right.
  rewrite mulmxBl mul1mx mulmxBr mulmx1 (P3_idem' Hli) subrr subr0.
  rewrite -Hxi.
  rewrite (inner_mul_square (1%:M - P3)).
  rewrite adjM_sub adjM_idn (P3_selfadj Hli).
  by rewrite Hxi.
Qed.

Definition succ_ordinal (i : 'I_N)
           (Hi : (S (nat_of_ord i) < N)%N) : 'I_N :=
  @Ordinal N (S (nat_of_ord i)) Hi.

Lemma lift0_val1 (p : nat) (k : 'I_p) :
  nat_of_ord (lift ord0 k) = S (nat_of_ord k).
Proof. by case: k => [m Hm]. Qed.

Lemma expr_lift0E1 (M : 'M[C]_3) (p : nat) (k : 'I_p) :
  M ^+ (nat_of_ord (lift ord0 k)) = M ^+ (S (nat_of_ord k)).
Proof. by case: k. Qed.

Lemma subn_lift0E1 (p : nat) (k : 'I_p) :
  subn p (nat_of_ord (lift ord0 k)) = predn (subn p (nat_of_ord k)).
Proof.
  by case: k => [m Hm] /=; rewrite subnS.
Qed.

Definition discCR_interior :=
  forall (j k : 'I_N)
         (Hj : (j.+1 < N)%N)
         (Hk : (k.+1 < N)%N),
    alpha * c j k + (conjC alpha) * c j (@succ_ordinal k Hk)
    = c (@succ_ordinal j Hj) k - c j (@succ_ordinal k Hk).
Definition ord_last : 'I_N :=
  @Ordinal N (N.-1) (pred_lt Npos).
Definition discCR_boundary_zero :=
  (forall k : 'I_N, c ord_last k = 0)
  /\ (forall j : 'I_N, c j ord_last = 0).
Hypothesis HCR : discCR_interior.
Hypothesis Hbd : discCR_boundary_zero.

Lemma P3_mul_one_minus (Hli : V3_li) :
  P3 *m (1%:M - P3) = 0.
Proof.
  rewrite mulmxBr mulmx1 (P3_idem' Hli) subrr.
  by [].
Qed.

Lemma zero_from_kernel_test (Hli : V3_li) (w : vct) :
  (forall xi, P3 *v xi = 0 -> [< w , xi >] = 0) ->
  (1%:M - P3) *v w = 0.
Proof.
  move=> Hall.
  have Hker : P3 *v ((1%:M - P3) *v w) = 0.
  { rewrite rebracket_right (P3_mul_one_minus Hli) mul0mx. by []. }
  have H0 : [< w , (1%:M - P3) *v w >] = 0.
  { apply: Hall. exact: Hker. }
  have Hz : [< w , (1%:M - P3) *v w >] = 0 by exact: Hall Hker.
  apply: inner_self_eq0_implies0.
  have Hrw :
  [< w , (1%:M - P3) *v w >]
  = [< (1%:M - P3) *v w , (1%:M - P3) *v w >]
  by apply: (inner_on_kerP3_rewrite Hli w); exact: Hker.
  rewrite -Hrw.
  exact: H0.
Qed.

Definition phi (j k : nat) (xi : vct) : C :=
  [< v , (adjM A) ^+ j *v (A ^+ k *v xi) >].

Lemma adjM_adjM (U : M) : adjM (adjM U) = U.
Proof. by rewrite /adjM map_trmx_conj trmxK map_conj_invol. Qed.


Lemma inner_left_mul (X : M) (y z : vct) :
  [< X *v y , z >] = [< y , (adjM X) *v z >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  rewrite adjM_mul_rect mulmxA. by rewrite adjM_adjM.
Qed.

Lemma trmx_addmx (U V : M) : (U + V)^T = U^T + V^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma trmx_scale (c1 : C) (U : M) : (c1 *: U)^T = c1 *: U^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma map_scale_conj m p (c1 : C) (X : 'M[C]_(m,p)) :
  map_mx conjC (c1 *: X) = (conjC c1) *: map_mx conjC X.
Proof. by apply/matrixP=> i j; rewrite !mxE GRing.Theory.rmorphM. Qed.

Lemma adjM_add (U V : M) :
  adjM (U + V) = adjM U + adjM V.
Proof. by rewrite /adjM map_addmx_conj trmx_addmx. Qed.

Lemma adjM_scale (c1 : C) (U : M) :
  adjM (c1 *: U) = (conjC c1) *: adjM U.
Proof. by rewrite /adjM map_scale_conj trmx_scale. Qed.

Lemma adjM_invol (U : M) : adjM (adjM U) = U.
Proof.
  rewrite /adjM map_trmx_conj trmxK map_conj_invol; reflexivity.
Qed.

Lemma sesquiE {m p} (Z : 'M[C]_(m,p)) :
  (Z ^t*)%sesqui = map_mx conjC (trmx Z).
Proof. reflexivity. Qed.

Lemma inner_add_r (y z1 z2 : vct) :
  [< y , z1 + z2 >] = [< y , z1 >] + [< y , z2 >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  change ((z1 + z2) ^t*)%sesqui with (map_mx conjC (trmx (z1 + z2))).
  set M12 := map_mx conjC (trmx (z1 + z2)).
  set M1  := map_mx conjC (trmx z1).
  set M2  := map_mx conjC (trmx z2).
  have -> : M12 = M1 + M2 by rewrite /M12 /M1 /M2 trmxDv map_mxD.
  rewrite mulmxDl.
  change ((z1 ^t*)%sesqui) with M1.
  change ((z2 ^t*)%sesqui) with M2.
  by rewrite !mxE.
Qed.

Lemma mulmx_scaler m p (M : 'M[C]_(m,p)) (a : C) (z : 'cV[C]_p) :
  M *m (a *: z) = a *: (M *m z).
Proof. by rewrite -scalemxAr. Qed.

Lemma inner_scale_r (a : C) (y z : vct) :
  [< y , a *: z >] = (conjC a) * [< y , z >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  change ((a *: z) ^t*)%sesqui with (map_mx conjC (trmx (a *: z))).
  rewrite trmxZv map_scale_conj -scalemxAl !mxE.
  reflexivity.
Qed.

Lemma A_mul_pow_succ (k : nat) (xi : vct) :
  A *v (A ^+ k *v xi) = (A ^+ k.+1) *v xi.
Proof. 
  change (A *v (A ^+ k *v xi)) with (A *m ((A ^+ k) *m xi)).
  rewrite mulmxA.
  by rewrite exprS.
Qed.

Lemma adjA_mul_pow_succ (j : nat) (w : vct) :
  (adjM A) ^+ j *v ((adjM A) *v w) = (adjM A) ^+ j.+1 *v w.
Proof. by rewrite mulmxA exprSr. Qed.

Lemma cell_expand (j k : nat) (xi : vct) :
  [< (adjM A) ^+ k *v (Ham *v (A ^+ j *v v)) , xi >]
    = (alpha) * (phi j.+1 k xi) + (conjC alpha) * (phi j k.+1 xi).
Proof.
  rewrite (inner_left_mul ((adjM A) ^+ k) (Ham *v (A ^+ j *v v)) xi).
  rewrite -adjM_pow adjM_invol.
  rewrite (inner_left_mul Ham (A ^+ j *v v) (A ^+ k *v xi)).
  rewrite /Ham adjM_add !adjM_scale adjM_invol.
  rewrite mulmxDl inner_add_r.
  rewrite -!scalemxAl !inner_scale_r !conjCK. 
  rewrite !inner_left_mul adjM_pow !mulmxA.
  rewrite -[adjM A ^+ j *m adjM A]exprSr.
  rewrite -mulmxA /phi -!mulmxA exprS -mulmxA addrC.
  rewrite [in RHS]exprSr [in RHS] mulmxA.
  rewrite [X in alpha * innern v X] mulmxA.
  rewrite [X in conjC alpha * innern v X + _] rebracket_right.
  rewrite [X in _ + alpha * innern v X] rebracket_right.
  rewrite [X in conjC alpha * innern v X + _] rebracket_right.
  rewrite [X in _ + alpha * innern v X] rebracket_right.
  rewrite [adjM A ^+ j *m A *m A ^+ k *m xi](_ : _ = adjM A ^+ j *m (A ^+ k * A *m xi)) //.
  - by rewrite addrC.
  - rewrite -mulmxA. 
  rewrite -[A *m A ^+ k]exprS.
  rewrite exprSr.
  by rewrite -mulmxA.
Qed.

Lemma inner_add_l (y1 y2 z : vct) :
  [< y1 + y2, z >] = [< y1, z >] + [< y2, z >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  rewrite mulmxDr mxE.
  by reflexivity.
Qed.


Lemma inner_big_sum_l (m : nat) (F : 'I_m -> vct) (z : vct) :
  [< \sum_(i < m) F i, z >] = \sum_(i < m) [< F i, z >].
Proof.
  elim: m F => [F|m IH F].
  - rewrite !big_ord0.
    rewrite /innern /MathCompBackboneC.inner.
    rewrite mulmx0. 
    rewrite mxE.
    reflexivity.
  - rewrite big_ord_recl /=.
    rewrite inner_add_l.
    have IH' := IH (fun i : 'I_m => F (lift ord0 i)).
    rewrite IH'.
    rewrite big_ord_recl /=.
    reflexivity.
Qed.

Lemma inner_scale_l (a : C) (y z : vct) :
  [< a *: y, z >] = a * [< y, z >].
Proof.
  rewrite /innern /MathCompBackboneC.inner.
  rewrite mulmx_scaler.
  rewrite !mxE.
  reflexivity.
Qed.

Lemma inner_wMO_xi (xi : vct) :
  [< w_MO , xi >]
  = \sum_(j < N) \sum_(k < N)
      c j k * (alpha * phi j.+1 k xi + (conjC alpha) * phi j k.+1 xi).
Proof.
  rewrite /w_MO.
  rewrite inner_big_sum_l.
  apply: eq_bigr => j _.
  rewrite inner_big_sum_l.
  apply: eq_bigr => k _.
  rewrite inner_scale_l.
  rewrite cell_expand.
  reflexivity.
Qed.


Local Definition CR := HCR.
Local Definition BD := Hbd.

Definition liftN (i : 'I_(N.-1)) : 'I_N :=
  widen_ord (leq_pred N) i.

Lemma lt_pred_succ (m n2 : nat) :
  (m < predn n2)%N -> (S m < n2)%N.
Proof. by rewrite -ltn_predRL. Qed.

Lemma succN_lt (j : 'I_(N.-1)) :
  (S (nat_of_ord j) < N)%N.
Proof. by have := valP j; rewrite -ltn_predRL. Qed.

Definition succN (j : 'I_(N.-1)) : 'I_N :=
  @Ordinal N (S (nat_of_ord j)) (succN_lt j).

Lemma succN_nat (j : 'I_(N.-1)) :
  nat_of_ord (succN j) = S (nat_of_ord j).
Proof. by []. Qed.

Lemma liftN_nat (k : 'I_(N.-1)) :
  nat_of_ord (liftN k) = nat_of_ord k.
Proof. by []. Qed.

Lemma c_last_row0 k : c ord_last k = 0.
Proof. by case: Hbd => /(_ k) // _ . Qed.

Lemma c_last_col0 j : c j ord_last = 0.
Proof. by case: Hbd => _ /(_ j) // . Qed.

Lemma ord_max_cast_last :
  cast_ord (prednK Npos) (@ord_max (N.-1)) = ord_last.
Proof. by apply/ord_inj. Qed.

Lemma ord_lastE :
  ord_last = cast_ord (prednK Npos) (@ord_max (N.-1)).
Proof. by rewrite -ord_max_cast_last. Qed.

Lemma liftN_widen (j : 'I_(N.-1)) :
  liftN j = widen_ord (leq_pred N) j.
Proof. by apply/ord_inj. Qed.

(* Cast utilities between 'I_{(N.-1).+1} and 'I_N *)
Lemma cast_ordK (m1 n1 : nat) (e : m1 = n1) (i : 'I_n1) :
  cast_ord e (cast_ord (esym e) i) = i.
Proof. by apply/ord_inj. Qed.

Lemma cast_ordKV (m1 n1 : nat) (e : m1 = n1) (j : 'I_m1) :
  cast_ord (esym e) (cast_ord e j) = j.
Proof. by apply/ord_inj. Qed.

Lemma ord_last_is_max (i : 'I_N) : (i <= ord_last)%O.
Proof.
  case: i => [m Hm] /=.
  rewrite /ord_last /= leEord.
  apply: (ltnSE (n := N.-1)).
  have Hm' := Hm.
  by rewrite -(prednK Npos) in Hm'.
Qed.

Lemma ge_ord_last_implies_eq (i : 'I_N) : 
  (ord_last <= i)%O -> (i <= ord_last)%O.
Proof.
  move=> _. exact: ord_last_is_max.
Qed.

Lemma i_eq_ord_last (i : 'I_N) : (ord_last <= i)%O -> i = ord_last.
Proof.
  case: i => [m Hm] Hi /=.
  have Hle : (Ordinal Hm <= ord_last)%O by apply: ord_last_is_max.
  apply/ord_inj.
  move: Hi Hle.
  rewrite /ord_last /= !leEord.
  move=> Hi_nat Hle_nat.
  apply/eqP.
  by rewrite eqn_leq; apply/andP; split.
Qed.

Lemma last_max (i : 'I_N) :
  ((ord_last <= i)%O) = (i == ord_last).
Proof.
  apply/idP/idP.
  - move=> Hle. by apply/eqP; apply: i_eq_ord_last.
  - move/eqP=> ->. by rewrite lexx.
Qed.

Lemma ord_except_lastE (i : 'I_N) :
  i != ord_last -> exists j : 'I_(predn N), i = liftN j.
Proof.
  case: i => [m Hm] Hi /=.
  have Hle_m : (m <= predn N)%N.
  { move: (ord_last_is_max (Ordinal Hm)).
    by rewrite /ord_last /= leEord. }
  have Hm_neq : m != predn N.
  { apply/eqP=> Hm_eq.
    move/negP: Hi; apply.
    apply/eqP; apply/ord_inj.
    exact: Hm_eq. }
  have Hm_lt : (m < predn N)%N.
  by rewrite ltn_neqAle Hm_neq Hle_m.
  exists (Ordinal Hm_lt).
  apply/ord_inj.
  by rewrite liftN_nat.
Qed.

Lemma neq_last_lt (i : 'I_N) :
  (i != ord_last) = (i < ord_last)%O.
Proof.
  rewrite ltNge last_max.
  by [].
Qed.

Lemma liftN_lt_last (j : 'I_(N.-1)) : (liftN j < ord_last)%O.
Proof.
  have Hneq : liftN j != ord_last.
  { apply/eqP=> H.
    have Hval := congr1 (fun i0 : 'I_N => nat_of_ord i0) H.
    rewrite liftN_nat /= in Hval.
    move: (ltn_ord j); rewrite Hval ltnn.
    by move/negP. }
  by move: Hneq; rewrite neq_last_lt.
Qed.

(* Surjectivity of liftN onto the initial segment { i | i < ord_last } *)
Lemma liftN_surj_on_initial :
  forall i : 'I_N, (i < ord_last)%O -> exists j : 'I_(N.-1), i = liftN j.
Proof.
  move=> i Hi.
  case: i Hi => [m Hm] Hi /=.
  have Hle_m : (m <= predn N)%N.
  { move: (ord_last_is_max (Ordinal Hm)). by rewrite /ord_last /= leEord. }
  have Hi_neq : (Ordinal Hm != ord_last).
  { move: Hi; rewrite -neq_last_lt => //.
  }
  have Hm_neq : m != predn N.
  { apply/eqP=> Hm_eq.
    move/negP: Hi_neq; apply.
    apply/eqP; apply/ord_inj; exact: Hm_eq. }
  have Hm_lt : (m < predn N)%N by rewrite ltn_neqAle Hm_neq Hle_m.
  exists (Ordinal Hm_lt).
  apply/ord_inj; by rewrite liftN_nat.
Qed.

Lemma eq_big_pred_last :
  [pred i : 'I_N | i != ord_last] =i [pred i : 'I_N | (i < ord_last)%O].
Proof. by move=> i; exact: (neq_last_lt i). Qed.

Lemma big_split_last (F : 'I_N -> C) :
  \sum_(i < N) F i = \sum_(i | i != ord_last) F i + F ord_last.
Proof.
  by rewrite (bigD1 ord_last) //= addrC.
Qed.

(* Helper: liftN is injective *)
Lemma inj_liftN (j1 j2 : 'I_(N.-1)) : liftN j1 = liftN j2 -> j1 = j2.
Proof.
  move=> H.
  apply/ord_inj.
  have := congr1 (fun i => nat_of_ord i) H.
  by rewrite !liftN_nat.
Qed.

(* Helper: liftN never hits ord_last *)
Lemma liftN_neq_last (j : 'I_(N.-1)) : liftN j != ord_last.
Proof. by rewrite neq_last_lt; apply: liftN_lt_last. Qed.

(* Helper 1: casting the lifted index coincides with liftN *)
Lemma cast_lift_last (j : 'I_(N.-1)) :
  cast_ord (prednK Npos) (lift (@ord_max (N.-1)) j) = liftN j.
Proof.
  apply/ord_inj.
  case: j => [m Hm] /=.
  rewrite /bump.
  case: ltnP => // Hge.
  move: Hm; rewrite ltnNge Hge.
  by move/negP.
Qed.
 
End FinalOpenLemma.
