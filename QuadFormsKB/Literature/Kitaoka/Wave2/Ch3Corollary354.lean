/-
# Kitaoka 1993, Corollary 3.5.4: representations of regular quadratic spaces over $\mathbb Q_p$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §3.5, Corollary 3.5.4, p. 63.

**Proves** `corollary354 : Corollary354` (statement in `Ch1Spaces.lean`). Let $U$, $V$ be regular quadratic spaces over
$\mathbb Q_p$ with $\dim U = m \le n = \dim V$, determinants $dU$, $dV$ (`QuadraticForm.discr'`). Then $U$ is represented
by $V$ if and only if one of the following holds: $n - m \ge 3$; $n = m$ and $V \cong U$; $n = m + 1$ and
$V \cong U \perp \langle dU\,dV\rangle$; $n = m + 2$ and ($dV \in -dU\,(\mathbb Q_p^\times)^2$ implies
$V \cong U \perp \mathbb H$).

*Proof.* Diagonalize both spaces (`exists_diag`, Mathlib's `equivalent_weightedSumSquares_units_of_nondegenerate'`),
so that $U \cong \langle a_0, \dots, a_{m-1}\rangle$ and $V \cong \langle b_0, \dots, b_{n-1}\rangle$ with
$dU = t_u^2 \prod a_i$, $dV = t_v^2 \prod b_i$ (`discr'_equiv`, `discr'_wss`).

"Only if": a representation $U \to V$ gives $V \cong U \perp W$ with $W = \langle w\rangle$ regular of dimension
$k = n - m$ (`split_of_rep`: induction on $m$, splitting off the value $a_0$ by
`QuadForm.exists_isometric_diag_cons` and cancelling it by Kitaoka's representation cancellation, Cor. 1.2.3,
`representation_cancellation` via `isRepresentedBy_tail`). For $k = 0$ the representation is an injective linear map
between spaces of equal dimension, hence an isometry. For $k = 1$, comparing determinants (`det_of_equiv_prod`),
$\langle w_0\rangle \cong \langle dU\,dV\rangle$ since $dU\,dV = (t_u t_v t \prod a_i)^2 w_0$. For $k = 2$ with
$dV = -dU c^2$ one gets $w_0 w_1 = -s^2$, hence $\langle w_0, w_1\rangle \cong \mathbb H$ (`wss2Hyperbolic`).

"If": $V \cong U \perp X$ gives $U \to V$ (`rep_of_equiv_prod`). If $k \ge 3$ (`rep_of_three_le`, O'Meara 63:21, here from
`PadicClass.represents_of_four_le`, i.e. O'Meara 63:18) or $k = 2$ and $dV \notin -dU\,(\mathbb Q_p^\times)^2$
(`rep_two_nonhyp`), $U$ is represented by $V$: induct on $m$, representing $a_0$ by $V$ (rank $\ge 4$ is universal;
for $m = 1$, $n = 3$ by `PadicClass.represents_three_iff`, Serre IV §2.2 Thm. 6, since $a_0 \not\equiv -dV$),
splitting it off, and cancelling.

**Repository results used.** `PadicClass.localHilbertField_padic`, `PadicClass.represents_of_four_le`,
`PadicClass.represents_three_iff`, `PadicClass.disc_of_isometric` (`PadicClassification.lean`);
`QuadForm.exists_isometric_diag_cons`, `isometryEquivDiagCons`, `isometricIn_iff_equivalent` (`Witt/`);
`isRepresentedBy_tail`, `isRepresentedBy_cons` (`Ch4HassePrinciple.lean`); `OMeara.IsRepresentedBy`.

The result is unconditional (no named input hypotheses).
-/
import QuadFormsKB.Literature.Kitaoka.Ch1Spaces
import QuadFormsKB.Literature.Kitaoka.Ch4HassePrinciple
import QuadFormsKB.Literature.LocalGlobal.PadicClassification

open QuadraticMap QuadFormsKB QuadFormsKB.QuadForm

noncomputable section
namespace QuadFormsKB.Kitaoka
namespace Cor354

variable (p : ℕ) [Fact p.Prime]

/-- Helper: the Mathlib form of the diagonal `QuadForm` $\langle a\rangle$ over $\mathbb Q_p$ is `weightedSumSquares`. -/
theorem toQF_diag {n : ℕ} (a : Fin n → ℚ_[p]) :
    (diag a).toQuadraticFormIn ℚ_[p] = weightedSumSquares ℚ_[p] a := by
  ext x
  rw [toQuadraticFormIn_apply, evalIn_diag]
  simp [weightedSumSquares_apply, _root_.sq]

theorem wss_equiv_iff {n : ℕ} (a b : Fin n → ℚ_[p]) :
    (weightedSumSquares ℚ_[p] a).Equivalent (weightedSumSquares ℚ_[p] b) ↔
      (diag b).IsometricIn ℚ_[p] (diag a) := by
  rw [isometricIn_iff_equivalent, toQF_diag, toQF_diag]

theorem prod_of_equiv {n : ℕ} {a b : Fin n → ℚ_[p]}
    (h : (weightedSumSquares ℚ_[p] a).Equivalent (weightedSumSquares ℚ_[p] b)) :
    ∃ t : ℚ_[p], t ≠ 0 ∧ ∏ i, a i = t ^ 2 * ∏ i, b i :=
  PadicClass.disc_of_isometric ((wss_equiv_iff p a b).mp h)

theorem discr'_wss {n : ℕ} (a : Fin n → ℚ_[p]) :
    QuadraticForm.discr' (weightedSumSquares ℚ_[p] a) = ∏ i, a i := by
  have : QuadraticForm.toMatrix' (weightedSumSquares ℚ_[p] a) = Matrix.diagonal a := by
    ext i j
    simp [QuadraticForm.toMatrix', LinearMap.toMatrix₂'_apply, associated_apply,
      weightedSumSquares_apply, Matrix.diagonal_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have key : ∀ (u v : Fin n → ℚ_[p]) (x : Fin n), a x * ((u x + v x) * (u x + v x)) -
        a x * (u x * u x) - a x * (v x * v x) = 2 * (a x * (u x * v x)) := fun u v x => by ring
    simp_rw [key, ← Finset.mul_sum]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hij), Finset.sum_eq_zero, mul_zero, mul_zero]
      intro x _
      by_cases hx : x = i
      · subst hx; simp [Ne.symm hij]
      · simp [Pi.single_apply, hx]
  rw [QuadraticForm.discr', this, Matrix.det_diagonal]

theorem discr'_equiv {n : ℕ} {Q Q' : QuadraticForm ℚ_[p] (Fin n → ℚ_[p])} (h : Q.Equivalent Q') :
    ∃ t : ℚ_[p], t ≠ 0 ∧ QuadraticForm.discr' Q = t ^ 2 * QuadraticForm.discr' Q' := by
  obtain ⟨e⟩ := h
  have hQ : Q = Q'.comp (e.toLinearEquiv : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])) := by
    ext x; exact (e.map_app x).symm
  refine ⟨(e.toLinearEquiv : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p])).toMatrix'.det, ?_, ?_⟩
  · have := LinearEquiv.isUnit_det' e.toLinearEquiv
    rw [LinearMap.det_toMatrix'] ; exact this.ne_zero
  · have := QuadraticForm.discr'_comp (Q := Q')
      (e.toLinearEquiv : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]))
    rw [← hQ] at this
    rw [this]; ring

/-- A regular form on `Fin m → ℚ_[p]` is equivalent to a nondegenerate diagonal form. -/
theorem exists_diag {m : ℕ} (Q : QuadraticForm ℚ_[p] (Fin m → ℚ_[p]))
    (hQ : QuadraticForm.discr' Q ≠ 0) :
    ∃ a : Fin m → ℚ_[p], (∀ i, a i ≠ 0) ∧ Q.Equivalent (weightedSumSquares ℚ_[p] a) := by
  have hnd : (associated (R := ℚ_[p]) Q).SeparatingLeft := by
    have h1 : (QuadraticForm.toMatrix' Q).Nondegenerate :=
      Matrix.nondegenerate_iff_det_ne_zero.mpr hQ
    have h2 : (LinearMap.BilinForm.toMatrix' (associated (R := ℚ_[p]) Q)).Nondegenerate := h1
    exact (LinearMap.BilinForm.nondegenerate_toMatrix'_iff.mp h2).1
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hnd
  have key : ∀ k, Module.finrank ℚ_[p] (Fin m → ℚ_[p]) = k →
      ∃ a : Fin k → ℚ_[p], (∀ i, a i ≠ 0) ∧ Q.Equivalent (weightedSumSquares ℚ_[p] a) := by
    intro k hk
    subst hk
    refine ⟨fun i => (w i : ℚ_[p]), fun i => (w i).ne_zero, ?_⟩
    have : weightedSumSquares ℚ_[p] w = weightedSumSquares ℚ_[p] (fun i => (w i : ℚ_[p])) := by
      ext x; simp [weightedSumSquares_apply, Units.smul_def]
    rwa [← this]
  exact key m (Module.finrank_fin_fun _)

/-! ### Representation and orthogonal sums -/

theorem rep_congr {U U' V V' : Type*} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup U']
    [Module ℚ_[p] U'] [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup V'] [Module ℚ_[p] V']
    {QU : QuadraticForm ℚ_[p] U} {QU' : QuadraticForm ℚ_[p] U'} {QV : QuadraticForm ℚ_[p] V}
    {QV' : QuadraticForm ℚ_[p] V'} (hU : QU.Equivalent QU') (hV : QV.Equivalent QV') :
    OMeara.IsRepresentedBy QU QV ↔ OMeara.IsRepresentedBy QU' QV' :=
  ⟨fun h => (OMeara.IsRepresentedBy.of_equivalent hU.symm).trans
      (h.trans (OMeara.IsRepresentedBy.of_equivalent hV)),
   fun h => (OMeara.IsRepresentedBy.of_equivalent hU).trans
      (h.trans (OMeara.IsRepresentedBy.of_equivalent hV.symm))⟩

theorem rep_of_equiv_prod {U W V : Type*} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup W]
    [Module ℚ_[p] W] [AddCommGroup V] [Module ℚ_[p] V] {QU : QuadraticForm ℚ_[p] U}
    (QW : QuadraticForm ℚ_[p] W) {QV : QuadraticForm ℚ_[p] V} (h : QV.Equivalent (QU.prod QW)) :
    OMeara.IsRepresentedBy QU QV :=
  (show OMeara.IsRepresentedBy QU (QU.prod QW) from
    ⟨⟨LinearMap.inl _ _ _, fun x => by simp [QuadraticMap.prod_apply]⟩,
      LinearMap.inl_injective⟩).trans (OMeara.IsRepresentedBy.of_equivalent h.symm)

theorem rep_zero {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (Q : QuadraticForm ℚ_[p] (Fin 0 → ℚ_[p]))
    (Q' : QuadraticForm ℚ_[p] V) : OMeara.IsRepresentedBy Q Q' :=
  ⟨⟨0, fun x => by
    have hx : x = 0 := Subsingleton.elim _ _
    subst hx
    show Q' 0 = Q 0
    rw [QuadraticMap.map_zero, QuadraticMap.map_zero]⟩,
    fun x y _ => Subsingleton.elim x y⟩

theorem rep_one {n : ℕ} (a : Fin 1 → ℚ_[p]) (ha : a 0 ≠ 0) (b y : Fin n → ℚ_[p])
    (hy : weightedSumSquares ℚ_[p] b y = a 0) :
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a) (weightedSumSquares ℚ_[p] b) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
    exact ha hy.symm
  refine ⟨⟨(LinearMap.proj (0 : Fin 1)).smulRight y, fun x => ?_⟩, ?_⟩
  · show weightedSumSquares ℚ_[p] b (x 0 • y) = _
    rw [QuadraticMap.map_smul, hy]
    simp [weightedSumSquares_apply]
    ring
  · intro x x' h
    have h' : x 0 • y = x' 0 • y := h
    have := smul_left_injective ℚ_[p] hy0 h'
    funext i
    rw [Subsingleton.elim i 0]
    exact this

/-- The value of a diagonal form at the first basis vector. -/
theorem wss_single_zero {m : ℕ} (a0 : ℚ_[p]) (a' : Fin m → ℚ_[p]) :
    weightedSumSquares ℚ_[p] (Fin.cons a0 a' : Fin (m + 1) → ℚ_[p]) (Pi.single 0 1) = a0 := by
  simp [weightedSumSquares_apply, Pi.single_apply]

theorem representsIn_of_wss {n : ℕ} (b : Fin n → ℚ_[p]) (y : Fin n → ℚ_[p]) (c : ℚ_[p])
    (hy : weightedSumSquares ℚ_[p] b y = c) : (diag b).RepresentsIn ℚ_[p] c :=
  (PadicClass.representsIn_diag_iff b c).mpr ⟨y, by
    rw [← hy]; simp [weightedSumSquares_apply, _root_.sq]⟩

theorem wss_of_representsIn {n : ℕ} (b : Fin n → ℚ_[p]) (c : ℚ_[p])
    (h : (diag b).RepresentsIn ℚ_[p] c) : ∃ y, weightedSumSquares ℚ_[p] b y = c := by
  obtain ⟨y, hy⟩ := (PadicClass.representsIn_diag_iff b c).mp h
  exact ⟨y, by rw [← hy]; simp [weightedSumSquares_apply, _root_.sq]⟩

/-- Splitting off a represented value. -/
theorem split_head {n : ℕ} (b : Fin (n + 1) → ℚ_[p]) (hb : ∀ i, b i ≠ 0) (a0 : ℚ_[p])
    (ha0 : a0 ≠ 0) (hr : ∃ y, weightedSumSquares ℚ_[p] b y = a0) :
    ∃ β : Fin n → ℚ_[p], (∀ i, β i ≠ 0) ∧
      (weightedSumSquares ℚ_[p] (Fin.cons a0 β : Fin (n + 1) → ℚ_[p])).Equivalent
        (weightedSumSquares ℚ_[p] b) := by
  obtain ⟨y, hy⟩ := hr
  obtain ⟨β, hβ, hiso⟩ := QuadForm.exists_isometric_diag_cons (nondegenerate_diag hb) ha0
    (representsIn_of_wss p b y a0 hy)
  exact ⟨β, hβ, (wss_equiv_iff p _ _).mpr hiso⟩

theorem rep_tail {m n : ℕ} (a0 : ℚ_[p]) (a' : Fin m → ℚ_[p]) (β : Fin n → ℚ_[p]) (ha0 : a0 ≠ 0)
    (hβ : ∀ i, β i ≠ 0)
    (h : OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] (Fin.cons a0 a' : Fin (m + 1) → ℚ_[p]))
      (weightedSumSquares ℚ_[p] (Fin.cons a0 β : Fin (n + 1) → ℚ_[p]))) :
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a') (weightedSumSquares ℚ_[p] β) := by
  rw [← toQF_diag p (Fin.cons a0 a'), ← toQF_diag p (Fin.cons a0 β)] at h
  have := isRepresentedBy_tail ℚ_[p] ha0 hβ h
  rwa [toQF_diag, toQF_diag] at this

theorem rep_cons {m n : ℕ} (a0 : ℚ_[p]) (a' : Fin m → ℚ_[p]) (β : Fin n → ℚ_[p])
    (h : OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a') (weightedSumSquares ℚ_[p] β)) :
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] (Fin.cons a0 a' : Fin (m + 1) → ℚ_[p]))
      (weightedSumSquares ℚ_[p] (Fin.cons a0 β : Fin (n + 1) → ℚ_[p])) := by
  rw [← toQF_diag p a', ← toQF_diag p β] at h
  have := isRepresentedBy_cons ℚ_[p] a0 h
  rwa [toQF_diag, toQF_diag] at this

/-- $\langle a_0, \beta\rangle \cong \langle a_0\rangle \perp \langle\beta\rangle$. -/
def consEquiv {n : ℕ} (a0 : ℚ_[p]) (β : Fin n → ℚ_[p]) :
    (weightedSumSquares ℚ_[p] (Fin.cons a0 β : Fin (n + 1) → ℚ_[p])).IsometryEquiv
      ((weightedSumSquares ℚ_[p] ![a0]).prod (weightedSumSquares ℚ_[p] β)) := by
  rw [← toQF_diag p (Fin.cons a0 β), ← toQF_diag p ![a0], ← toQF_diag p β]
  exact isometryEquivDiagCons ℚ_[p] a0 β

/-- $\langle\rangle \perp Q \cong Q$ for the zero-dimensional diagonal form. -/
def zeroProd {k : ℕ} (a : Fin 0 → ℚ_[p]) (b : Fin k → ℚ_[p]) :
    ((weightedSumSquares ℚ_[p] a).prod (weightedSumSquares ℚ_[p] b)).IsometryEquiv
      (weightedSumSquares ℚ_[p] b) where
  toLinearEquiv := LinearEquiv.uniqueProd
  map_app' x := by simp [weightedSumSquares_apply]

theorem prod_wss_equiv {m k : ℕ} (a : Fin m → ℚ_[p]) (w : Fin k → ℚ_[p]) :
    ((weightedSumSquares ℚ_[p] a).prod (weightedSumSquares ℚ_[p] w)).Equivalent
      (weightedSumSquares ℚ_[p] (Fin.append a w)) :=
  ⟨{ (QuadForm.finAddLinearEquiv ℚ_[p] m k).symm with
      map_app' := fun x => by
        simp [weightedSumSquares_apply, Fin.sum_univ_add, QuadForm.finAddLinearEquiv] }⟩

theorem det_of_equiv_prod {m k n : ℕ} (hn : n = m + k) {a : Fin m → ℚ_[p]} {w : Fin k → ℚ_[p]}
    {b : Fin n → ℚ_[p]}
    (h : (weightedSumSquares ℚ_[p] b).Equivalent
      ((weightedSumSquares ℚ_[p] a).prod (weightedSumSquares ℚ_[p] w))) :
    ∃ t : ℚ_[p], t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ((∏ i, a i) * ∏ i, w i) := by
  subst hn
  obtain ⟨t, ht, h⟩ := prod_of_equiv p (h.trans (prod_wss_equiv p a w))
  refine ⟨t, ht, ?_⟩
  rw [h, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-! ### Splitting off the complement -/

/-- If $\langle a\rangle \to \langle b\rangle$ with $\dim\langle b\rangle = m + k$, then
$\langle b\rangle \cong \langle a\rangle \perp \langle w\rangle$ for some regular $\langle w\rangle$ of dimension $k$. -/
theorem split_of_rep : ∀ (m k n : ℕ), n = m + k → ∀ (a : Fin m → ℚ_[p]) (b : Fin n → ℚ_[p]),
    (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a) (weightedSumSquares ℚ_[p] b) →
    ∃ w : Fin k → ℚ_[p], (∀ i, w i ≠ 0) ∧ (weightedSumSquares ℚ_[p] b).Equivalent
      ((weightedSumSquares ℚ_[p] a).prod (weightedSumSquares ℚ_[p] w))
  | 0, k, n, hn, a, b, _, hb, _ => by
    obtain rfl : n = k := by omega
    exact ⟨b, hb, ⟨(zeroProd p a b).symm⟩⟩
  | m + 1, k, n, hn, a, b, ha, hb, h => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a0, a', rfl⟩ : ∃ a0 a', a = Fin.cons a0 a' :=
      ⟨a 0, Fin.tail a, (Fin.cons_self_tail a).symm⟩
    have ha0 : a0 ≠ 0 := by simpa using ha 0
    have ha' : ∀ i, a' i ≠ 0 := fun i => by simpa using ha i.succ
    obtain ⟨y, hy⟩ := h.exists_eq (Pi.single 0 1)
    rw [wss_single_zero] at hy
    obtain ⟨β, hβ, hbeta⟩ := split_head p b hb a0 ha0 ⟨y, hy⟩
    have hrep : OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a')
        (weightedSumSquares ℚ_[p] β) :=
      rep_tail p a0 a' β ha0 hβ (h.trans (OMeara.IsRepresentedBy.of_equivalent hbeta.symm))
    obtain ⟨w, hw, e⟩ := split_of_rep m k n' (by omega) a' β ha' hβ hrep
    refine ⟨w, hw, ⟨?_⟩⟩
    exact (hbeta.some.symm.trans (consEquiv p a0 β)).trans
      ((((QuadraticMap.IsometryEquiv.refl _).prod e.some).trans
        (QuadraticForm.Witt.prodAssoc _ _ _).symm).trans
        ((consEquiv p a0 a').symm.prod (QuadraticMap.IsometryEquiv.refl _)))

/-- $\dim V \ge \dim U + 3$: $U$ is represented by $V$. -/
theorem rep_of_three_le : ∀ (m k n : ℕ), 3 ≤ k → n = m + k → ∀ (a : Fin m → ℚ_[p])
    (b : Fin n → ℚ_[p]), (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a) (weightedSumSquares ℚ_[p] b)
  | 0, k, n, _, _, a, b, _, _ => rep_zero p _ _
  | m + 1, k, n, hk, hn, a, b, ha, hb => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a0, a', rfl⟩ : ∃ a0 a', a = Fin.cons a0 a' :=
      ⟨a 0, Fin.tail a, (Fin.cons_self_tail a).symm⟩
    have ha0 : a0 ≠ 0 := by simpa using ha 0
    have ha' : ∀ i, a' i ≠ 0 := fun i => by simpa using ha i.succ
    have hr := PadicClass.represents_of_four_le (PadicClass.localHilbertField_padic p) hb
      (by omega) a0
    obtain ⟨β, hβ, hbeta⟩ := split_head p b hb a0 ha0 (wss_of_representsIn p b a0 hr)
    have hrep := rep_of_three_le m k n' hk (by omega) a' β ha' hβ
    exact (rep_cons p a0 a' β hrep).trans (OMeara.IsRepresentedBy.of_equivalent hbeta)

/-- $\dim V = \dim U + 2$ and $dV \ne -dU$ (mod squares): $U$ is represented by $V$. -/
theorem rep_two_nonhyp : ∀ (m n : ℕ), n = m + 2 → ∀ (a : Fin m → ℚ_[p]) (b : Fin n → ℚ_[p]),
    (∀ i, a i ≠ 0) → (∀ i, b i ≠ 0) →
    (¬ ∃ c : ℚ_[p], c ≠ 0 ∧ ∏ i, b i = -(∏ i, a i) * c ^ 2) →
    OMeara.IsRepresentedBy (weightedSumSquares ℚ_[p] a) (weightedSumSquares ℚ_[p] b)
  | 0, n, _, a, b, _, _, _ => rep_zero p _ _
  | 1, n, hn, a, b, ha, hb, hc => by
    obtain rfl : n = 3 := by omega
    have hb3 : b = ![b 0, b 1, b 2] := PadicClass.eq_vec_three b
    have hrep : (diag ![b 0, b 1, b 2]).RepresentsIn ℚ_[p] (a 0) :=
      (PadicClass.represents_three_iff (PadicClass.localHilbertField_padic p) (hb 0) (hb 1) (hb 2)
        (ha 0)).mpr (by
          rintro ⟨t, ht, hx⟩
          exfalso
          apply hc
          refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
          rw [Fin.prod_univ_three, Fin.prod_univ_one, hx]
          field_simp)
    rw [← hb3] at hrep
    obtain ⟨y, hy⟩ := wss_of_representsIn p b _ hrep
    exact rep_one p a (ha 0) b y hy
  | m + 2, n, hn, a, b, ha, hb, hc => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨a0, a', rfl⟩ : ∃ a0 a', a = Fin.cons a0 a' :=
      ⟨a 0, Fin.tail a, (Fin.cons_self_tail a).symm⟩
    have ha0 : a0 ≠ 0 := by simpa using ha 0
    have ha' : ∀ i, a' i ≠ 0 := fun i => by simpa using ha i.succ
    have hr := PadicClass.represents_of_four_le (PadicClass.localHilbertField_padic p) hb
      (by omega) a0
    obtain ⟨β, hβ, hbeta⟩ := split_head p b hb a0 ha0 (wss_of_representsIn p b a0 hr)
    have hc' : ¬ ∃ c : ℚ_[p], c ≠ 0 ∧ ∏ i, β i = -(∏ i, a' i) * c ^ 2 := by
      rintro ⟨c, hc0, hcc⟩
      obtain ⟨t, ht, hdet⟩ := prod_of_equiv p hbeta
      apply hc
      refine ⟨c / t, div_ne_zero hc0 ht, ?_⟩
      rw [Fin.prod_cons] at hdet ⊢
      have h1 : t ^ 2 * ∏ i, b i = a0 * (-(∏ i, a' i) * c ^ 2) := by rw [← hcc, ← hdet]
      field_simp
      linear_combination h1
    have hrep := rep_two_nonhyp (m + 1) n' (by omega) a' β ha' hβ hc'
    exact (rep_cons p a0 a' β hrep).trans (OMeara.IsRepresentedBy.of_equivalent hbeta)

/-! ### Binary spaces of determinant $-1$ -/

/-- $\langle w_0, w_1\rangle \cong \mathbb H$ when $w_0 w_1 = -s^2$, $s \ne 0$. -/
def wss2Hyperbolic (w : Fin 2 → ℚ_[p]) (h0 : w 0 ≠ 0) {s : ℚ_[p]} (hs : s ≠ 0)
    (h : w 0 * w 1 = -s ^ 2) :
    (weightedSumSquares ℚ_[p] w).IsometryEquiv (QuadraticForm.hyperbolicPlane ℚ_[p]) where
  toFun x := (x 0 - s / w 0 * x 1, w 0 * x 0 + s * x 1)
  invFun q := ![q.1 + s / w 0 * ((q.2 - w 0 * q.1) / (2 * s)), (q.2 - w 0 * q.1) / (2 * s)]
  map_add' x y := by
    ext <;> simp <;> ring
  map_smul' c x := by
    ext <;> simp <;> ring
  left_inv x := by
    funext i
    fin_cases i
    · simp; field_simp; ring
    · simp; field_simp; ring
  right_inv q := by
    ext <;> simp <;> field_simp <;> ring
  map_app' x := by
    have h1 : w 1 = -s ^ 2 / w 0 := by rw [eq_div_iff h0, mul_comm]; exact h
    simp [weightedSumSquares_apply, Fin.sum_univ_two, h1]
    field_simp
    ring

/-- Rescaling the weights by squares of nonzero elements. -/
def wssScale {ι : Type} [Fintype ι] (w w' u : ι → ℚ_[p]) (hu : ∀ i, u i ≠ 0)
    (h : ∀ i, w i = w' i * u i ^ 2) :
    (weightedSumSquares ℚ_[p] w).IsometryEquiv (weightedSumSquares ℚ_[p] w') :=
  QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares
    (fun i => Units.mk0 (u i) (hu i)) (fun i => by simpa using (h i).symm)

/-! ### The main theorem, with $n = m + k$ -/

theorem main_aux (m k : ℕ) (QU : QuadraticForm ℚ_[p] (Fin m → ℚ_[p]))
    (QV : QuadraticForm ℚ_[p] (Fin (m + k) → ℚ_[p])) (hU : QuadraticForm.discr' QU ≠ 0)
    (hV : QuadraticForm.discr' QV ≠ 0) :
    (OMeara.IsRepresentedBy QU QV ↔
      3 ≤ m + k - m ∨ (m + k = m ∧ QV.Equivalent QU) ∨
      (m + k = m + 1 ∧ QV.Equivalent (QU.prod (weightedSumSquares ℚ_[p]
        ![QuadraticForm.discr' QU * QuadraticForm.discr' QV]))) ∨
      (m + k = m + 2 ∧ ((∃ c : ℚ_[p], c ≠ 0 ∧
          QuadraticForm.discr' QV = -QuadraticForm.discr' QU * c ^ 2) →
        QV.Equivalent (QU.prod (QuadraticForm.hyperbolicPlane ℚ_[p]))))) := by
  obtain ⟨a, ha, eU⟩ := exists_diag p QU hU
  obtain ⟨b, hb, eV⟩ := exists_diag p QV hV
  obtain ⟨tu, htu, hdU⟩ := discr'_equiv p eU
  obtain ⟨tv, htv, hdV⟩ := discr'_equiv p eV
  rw [discr'_wss p a] at hdU
  rw [discr'_wss p b] at hdV
  have hPa : ∏ i, a i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hrep := rep_congr p eU eV
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  rcases hk with rfl | rfl | rfl | hk
  · constructor
    · intro h
      refine Or.inr (Or.inl ⟨rfl, ?_⟩)
      obtain ⟨σ, hσ⟩ := hrep.mp h
      have hbij : Function.Bijective σ.toLinearMap :=
        ⟨hσ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hσ⟩
      let e : (weightedSumSquares ℚ_[p] a).IsometryEquiv (weightedSumSquares ℚ_[p] b) :=
        { LinearEquiv.ofBijective σ.toLinearMap hbij with map_app' := σ.map_app }
      have e' : (weightedSumSquares ℚ_[p] a).Equivalent (weightedSumSquares ℚ_[p] b) := ⟨e⟩
      exact eV.trans (e'.symm.trans eU.symm)
    · rintro (h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · omega
      · exact OMeara.IsRepresentedBy.of_equivalent h.symm
      · omega
      · omega
  · constructor
    · intro h
      refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      obtain ⟨w, hw, e⟩ := split_of_rep p m 1 (m + 1) rfl a b ha hb (hrep.mp h)
      obtain ⟨t, ht, hdet⟩ := det_of_equiv_prod p rfl e
      rw [Fin.prod_univ_one] at hdet
      have hs : tu * tv * t * ∏ i, a i ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero htu htv) ht) hPa
      have hcd : QuadraticForm.discr' QU * QuadraticForm.discr' QV =
          (tu * tv * t * ∏ i, a i) ^ 2 * w 0 := by
        rw [hdU, hdV, hdet]; ring
      have e2 := wssScale p w ![QuadraticForm.discr' QU * QuadraticForm.discr' QV]
        (fun _ => (tu * tv * t * ∏ i, a i)⁻¹) (fun _ => inv_ne_zero hs) (fun i => by
          fin_cases i
          simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [hcd]
          field_simp)
      exact ⟨eV.some.trans (e.some.trans (((QuadraticMap.IsometryEquiv.refl _).prod e2).trans
        (eU.some.symm.prod (QuadraticMap.IsometryEquiv.refl _))))⟩
    · rintro (h | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · omega
      · omega
      · exact rep_of_equiv_prod p _ h
      · omega
  · constructor
    · intro h
      refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
      rintro ⟨c, hc, hcd⟩
      obtain ⟨w, hw, e⟩ := split_of_rep p m 2 (m + 2) rfl a b ha hb (hrep.mp h)
      obtain ⟨t, ht, hdet⟩ := det_of_equiv_prod p rfl e
      rw [Fin.prod_univ_two] at hdet
      rw [hdU, hdV, hdet] at hcd
      have key : (∏ i, a i) * (w 0 * w 1 * (tv * t) ^ 2 + (tu * c) ^ 2) = 0 := by
        linear_combination hcd
      have hw01 : w 0 * w 1 * (tv * t) ^ 2 = -(tu * c) ^ 2 := by
        rcases mul_eq_zero.mp key with h1 | h1
        · exact absurd h1 hPa
        · linear_combination h1
      have hvt : tv * t ≠ 0 := mul_ne_zero htv ht
      have hs : tu * c / (tv * t) ≠ 0 := div_ne_zero (mul_ne_zero htu hc) hvt
      have hprod : w 0 * w 1 = -(tu * c / (tv * t)) ^ 2 := by
        field_simp
        linear_combination hw01
      exact ⟨eV.some.trans (e.some.trans (((QuadraticMap.IsometryEquiv.refl _).prod
        (wss2Hyperbolic p w (hw 0) hs hprod)).trans
        (eU.some.symm.prod (QuadraticMap.IsometryEquiv.refl _))))⟩
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · omega
      · omega
      · by_cases hcond : ∃ c : ℚ_[p], c ≠ 0 ∧
            QuadraticForm.discr' QV = -QuadraticForm.discr' QU * c ^ 2
        · exact rep_of_equiv_prod p _ (h hcond)
        · refine hrep.mpr (rep_two_nonhyp p m (m + 2) rfl a b ha hb ?_)
          rintro ⟨c, hc0, hc⟩
          apply hcond
          refine ⟨tv * c / tu, div_ne_zero (mul_ne_zero htv hc0) htu, ?_⟩
          rw [hdU, hdV, hc]
          field_simp
  · constructor
    · intro _
      exact Or.inl (by omega)
    · intro _
      exact hrep.mpr (rep_of_three_le p m k (m + k) hk rfl a b ha hb)

end Cor354

open Cor354 in
/-- **Kitaoka 1993, Corollary 3.5.4** (p. 63), *proved* (unconditional): for regular spaces $U$, $V$ over
$\mathbb Q_p$ with $\dim U \le \dim V$, $U$ is represented by $V$ iff $\dim V - \dim U \ge 3$, or $V \cong U$
($n = m$), or $V \cong U \perp \langle dU\,dV\rangle$ ($n = m + 1$), or ($n = m + 2$ and $dV = -dU c^2$ implies
$V \cong U \perp \mathbb H$). See the module docstring for the proof. -/
@[kb "kitaoka1993" "§3.5, Cor. 3.5.4, p. 63"]
theorem corollary354 : Corollary354 := by
  intro p _ m n QU QV hU hV hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact main_aux p m k QU QV hU hV

end QuadFormsKB.Kitaoka
