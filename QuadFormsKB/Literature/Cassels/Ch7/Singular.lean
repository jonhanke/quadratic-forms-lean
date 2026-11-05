/-
# Cassels, Chapter 7, §4: singular forms over a principal ideal domain

**Setting.** Cassels, *Rational Quadratic Forms*, Chapter 7, §4 (pp. 108–109): $I$ a principal ideal domain with
field of fractions $k$ ($\operatorname{char} k \ne 2$ is not needed here; see the update in Lemma 4.1 for why $k$ must
be the field of fractions). A $k$-valued quadratic form
$f(\vec x) = \sum_{i,j} f_{ij}x_ix_j$ ($f_{ij} = f_{ji} \in k$) is given by its symmetric matrix $F$; $f$ is *singular*
when $\det F = 0$. Two forms are $I$-equivalent when $G = T^{t}FT$ for some $T \in \mathrm{GL}_n(I)$ (the entries of
$T$ mapped to $k$).

**Proves**
* `exists_regular_of_singular` (**Lemma 4.1**, p. 109): a singular form is $I$-equivalent to a regular form in fewer
  variables: $T^{t}FT$ has a regular $m \times m$ block in the variables $x_0, \dots, x_{m-1}$ ($m < n$) and is zero
  elsewhere. (Cassels' proof puts the radical on the first variables; the order is immaterial.)
* `not_equiv_one_var_zsqrtd` (**7.r4**, p. 109): for $I = \mathbb Z[\sqrt{-5}]$ the conclusion fails: the singular
  form $f = (2x_0 + (1 + \sqrt{-5})x_1)^{2}$ is not $I$-equivalent to a form $ay_0^{2}$ in one variable. The
  machine-read text lost Cassels' formula and this example was reconstructed (non-principal ideal
  $(2, 1 + \sqrt{-5})$) before the page image was read. The page image (p. 109) shows Cassels' form
  $\{(1 + 2\sqrt{-5})x_1 + 3x_2\}^{2}$ (ideal $(3, 1 + 2\sqrt{-5})$): it is formalized as
  `not_equiv_one_var_printed` (`Ch7/Supplement.lean`); the example here is a second illustration of the same point.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Matrix

/-- **Cassels, Ch. 7, Lemma 4.1**: *suppose that $I$ is a principal ideal domain. Then any singular quadratic form is
$I$-equivalent to a regular form in a smaller number of variables.* Here the form has symmetric matrix
$F \in M_n(k)$ with $\det F = 0$; the conclusion gives $T \in \mathrm{GL}_n(I)$, $m < n$ and an $m \times m$ matrix $G$
with $\det G \ne 0$ such that $T^{t}FT$ has $G$ in the rows and columns $0, \dots, m-1$ and zeros elsewhere, i.e.
$f(T\vec y) = g(y_0, \dots, y_{m-1})$ with $g$ regular.

*Update (missing hypothesis):* $k$ must be the field of fractions of $I$ (`IsFractionRing I k`). Cassels allows $k$
larger than the quotient field (p. 102), and the lemma then fails: for $I = \mathbb Z$, $k = \mathbb R$ and
$f = (x_0 + \sqrt2\,x_1)^{2}$ (singular), $f(\vec t) \ne 0$ for every non-zero $\vec t \in \mathbb Z^{2}$, so no column of
an invertible $T$ can carry a variable that $f(T\vec y)$ omits. Cassels' proof ("the form induced on $\Lambda_1$ is
regular") clears denominators, which uses this hypothesis. -/
@[kb "cassels1978" "Ch. 7, Lemma 4.1, p. 109"]
theorem exists_regular_of_singular {I k : Type*} [CommRing I] [IsDomain I] [IsPrincipalIdealRing I] [Field k]
    [Algebra I k] [IsFractionRing I k] {n : ℕ} (F : Matrix (Fin n) (Fin n) k)
    (hF : Fᵀ = F) (hsing : F.det = 0) :
    ∃ m < n, ∃ T : GL (Fin n) I, ∃ G : Matrix (Fin m) (Fin m) k, G.det ≠ 0 ∧
      ∀ i j : Fin n, ((T.val.map (algebraMap I k))ᵀ * F * T.val.map (algebraMap I k)) i j =
        if h : (i : ℕ) < m ∧ (j : ℕ) < m then G ⟨i, h.1⟩ ⟨j, h.2⟩ else 0 := by
  classical
  have hinj : Function.Injective (algebraMap I k) := IsFractionRing.injective I k
  have : NoZeroSMulDivisors I k := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  -- the radical `R = ker φ` of `F` inside `I^n`, with `φ x = F (x mapped to k)`
  let ι : (Fin n → I) →ₗ[I] (Fin n → k) :=
    LinearMap.pi fun i => (Algebra.linearMap I k) ∘ₗ LinearMap.proj i
  let φ : (Fin n → I) →ₗ[I] (Fin n → k) := (Matrix.mulVecLin F).restrictScalars I ∘ₗ ι
  have hφ : ∀ x, φ x = F *ᵥ (fun p => algebraMap I k (x p)) := fun x => rfl
  let S := LinearMap.range φ
  have : Module.Finite I S := Module.Finite.range φ
  have : Module.Free I S := Module.free_of_finite_type_torsion_free'
  obtain ⟨g, hg⟩ := Module.projective_lifting_property φ.rangeRestrict LinearMap.id
    φ.surjective_rangeRestrict
  have hgs : ∀ s, φ (g s) = (s : Fin n → k) := fun s =>
    congrArg Subtype.val (LinearMap.congr_fun hg s)
  have hgi : Function.Injective g := by
    intro a b h
    have h1 := LinearMap.congr_fun hg a
    have h2 := LinearMap.congr_fun hg b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, h]
  let C := LinearMap.range g
  let R := LinearMap.ker φ
  have hc : IsCompl C R := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro x ⟨s, rfl⟩ hx
      have : (s : Fin n → k) = 0 := by rw [← hgs s]; exact hx
      have : s = 0 := Subtype.ext this
      rw [this, map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨g (φ.rangeRestrict x), ⟨_, rfl⟩, x - g (φ.rangeRestrict x), ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hgs]
      simp
  have : Module.Finite I R := inferInstance
  have : Module.Free I R := inferInstance
  obtain ⟨m, r, B0, hl, hr, hnt⟩ : ∃ (m r : ℕ) (B0 : Module.Basis (Fin m ⊕ Fin r) I (Fin n → I)),
      (∀ a, B0 (Sum.inl a) ∈ C) ∧ (∀ c, B0 (Sum.inr c) ∈ R) ∧ (Nontrivial R → 0 < r) := by
    let bR := Module.finBasis I R
    let bS := Module.finBasis I S
    let bC : Module.Basis _ I C := bS.map (LinearEquiv.ofInjective g hgi)
    refine ⟨_, _, (bC.prod bR).map (Submodule.prodEquivOfIsCompl C R hc), ?_, ?_, ?_⟩
    · intro a
      simp [Module.Basis.prod_apply]
    · intro c
      simp [Module.Basis.prod_apply]
    · intro h
      simpa using Fintype.card_pos_iff.mpr bR.index_nonempty
  have hmr : m + r = n := by
    have := Fintype.card_congr (B0.indexEquiv (Pi.basisFun I (Fin n)))
    simpa using this
  let σ : Fin m ⊕ Fin r ≃ Fin n := finSumFinEquiv.trans (finCongr hmr)
  let B' : Module.Basis (Fin n) I (Fin n → I) := B0.reindex σ
  have hB'l : ∀ i : Fin n, (i : ℕ) < m → B' i ∈ C := by
    intro i hi
    obtain ⟨s, rfl⟩ := σ.surjective i
    rcases s with a | c
    · simpa [B', σ] using hl a
    · simp [σ] at hi
  have hB'r : ∀ i : Fin n, ¬ (i : ℕ) < m → B' i ∈ R := by
    intro i hi
    obtain ⟨s, rfl⟩ := σ.surjective i
    rcases s with a | c
    · simp [σ] at hi
    · simpa [B', σ] using hr c
  -- the matrix `T` with columns the adapted basis `B'`
  let T : Matrix (Fin n) (Fin n) I := (Pi.basisFun I (Fin n)).toMatrix B'
  have hT : ∀ p i, T p i = B' i p := fun p i => by simp [T, Module.Basis.toMatrix_apply]
  have hdet : IsUnit T.det := by
    rw [show T.det = (Pi.basisFun I (Fin n)).det B' from ((Pi.basisFun I (Fin n)).det_apply B').symm]
    exact (Pi.basisFun I (Fin n)).isUnit_det B'
  let Tg : GL (Fin n) I := ⟨T, T⁻¹, Matrix.mul_nonsing_inv T hdet, Matrix.nonsing_inv_mul T hdet⟩
  let A := algebraMap I k
  let TA : Matrix (Fin n) (Fin n) k := T.map A
  let M : Matrix (Fin n) (Fin n) k := TAᵀ * F * TA
  have hM : ∀ i j, M i j = (fun p => A (B' i p)) ⬝ᵥ (F *ᵥ fun p => A (B' j p)) := by
    intro i j
    simp only [M, TA, Matrix.mul_apply, dotProduct, mulVec, transpose_apply, Matrix.map_apply, hT]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hMr : ∀ i j : Fin n, ¬ (j : ℕ) < m → M i j = 0 := by
    intro i j hj
    have h0 : F *ᵥ (fun p => A (B' j p)) = 0 := hB'r j hj
    rw [hM, h0, dotProduct_zero]
  have hMl : ∀ i j : Fin n, ¬ (i : ℕ) < m → M i j = 0 := by
    intro i j hi
    have h0 : F *ᵥ (fun p => A (B' i p)) = 0 := hB'r i hi
    have hs : (fun p => A (B' i p)) ᵥ* F = F *ᵥ (fun p => A (B' i p)) := by
      conv_lhs => rw [← hF]
      exact vecMul_transpose F _
    rw [hM, Matrix.dotProduct_mulVec, hs, h0, zero_dotProduct]
  -- clearing denominators (this is where `k` = fraction field of `I` is used)
  have hclear : ∀ {N : ℕ} (y : Fin N → k), ∃ (b : I) (z : Fin N → I), b ≠ 0 ∧
      ∀ p, A (z p) = A b * y p := by
    intro N y
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors I) y
    choose z hz using hb
    refine ⟨b, z, nonZeroDivisors.coe_ne_zero b, fun p => ?_⟩
    rw [hz p, Algebra.smul_def]
  -- `m < n`: the radical is non-zero
  have hmn : m < n := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hsing
    obtain ⟨b, z, hb, hz⟩ := hclear v
    have hzR : z ∈ R := by
      have : (fun p => A (z p)) = A b • v := by
        funext p; simp [hz]
      show F *ᵥ (fun p => A (z p)) = 0
      rw [this, Matrix.mulVec_smul, hv, smul_zero]
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext p
      have := hz p
      rw [h0] at this
      simp only [Pi.zero_apply, map_zero] at this
      have hAb : A b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
      simpa [hAb] using this.symm
    have : Nontrivial R := ⟨⟨⟨z, hzR⟩, 0, fun h => hz0 (congrArg Subtype.val h)⟩⟩
    have := hnt this
    omega
  have hAb_ne : ∀ b : I, b ≠ 0 → A b ≠ 0 := fun b hb h => hb (hinj (by rw [h, map_zero]))
  -- the Gram block `G` is regular
  have hdetG : (Matrix.of fun a b : Fin m => M (Fin.castLE hmn.le a) (Fin.castLE hmn.le b)).det ≠ 0 := by
    intro hG0
    set G : Matrix (Fin m) (Fin m) k :=
      Matrix.of fun a b => M (Fin.castLE hmn.le a) (Fin.castLE hmn.le b) with hGdef
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG0
    let yt : Fin n → k := fun i => if h : (i : ℕ) < m then y ⟨i, h⟩ else 0
    have hyt : ∀ a : Fin m, yt (Fin.castLE hmn.le a) = y a := fun a => by simp [yt]
    have hyt' : ∀ i : Fin n, ¬ (i : ℕ) < m → yt i = 0 := fun i hi => by simp [yt, hi]
    obtain ⟨b, z, hb, hz⟩ := hclear yt
    have hMy : M *ᵥ yt = 0 := by
      funext i
      by_cases hi : (i : ℕ) < m
      · obtain ⟨a0, rfl⟩ : ∃ a0, i = Fin.castLE hmn.le a0 := ⟨⟨i, hi⟩, rfl⟩
        have h1 : (M *ᵥ yt) (Fin.castLE hmn.le a0) = (G *ᵥ y) a0 := by
          simp only [mulVec, dotProduct]
          symm
          refine Fintype.sum_of_injective (Fin.castLE hmn.le) (Fin.castLE_injective _) _ _ ?_ ?_
          · intro j hj
            have : ¬ (j : ℕ) < m := fun h => hj ⟨⟨j, h⟩, rfl⟩
            rw [hyt' j this, mul_zero]
          · intro a; simp [hGdef, hyt]
        rw [h1, hy]; rfl
      · simp only [mulVec, dotProduct, hMl i _ hi, zero_mul, Finset.sum_const_zero]; rfl
    have hTA : TA * (T⁻¹).map A = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv T hdet]; simp
    have hFw : F *ᵥ (TA *ᵥ yt) = 0 := by
      have h1 : TAᵀ *ᵥ (F *ᵥ (TA *ᵥ yt)) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; exact hMy
      have h2 : (((T⁻¹).map A)ᵀ * TAᵀ) = 1 := by
        rw [← Matrix.transpose_mul, hTA, Matrix.transpose_one]
      calc F *ᵥ (TA *ᵥ yt) = (((T⁻¹).map A)ᵀ * TAᵀ) *ᵥ (F *ᵥ (TA *ᵥ yt)) := by
            rw [h2, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, mulVec_zero]
    have hzsupp : ∀ j : Fin n, ¬ (j : ℕ) < m → z j = 0 := fun j hj =>
      hinj (by rw [hz j, hyt' j hj, mul_zero, map_zero])
    set x : Fin n → I := T *ᵥ z with hx
    have hAx : (fun p => A (x p)) = A b • (TA *ᵥ yt) := by
      funext p
      simp only [hx, mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, TA,
        Matrix.map_apply, hz, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hxR : x ∈ R := by
      show F *ᵥ (fun p => A (x p)) = 0
      rw [hAx, Matrix.mulVec_smul, hFw, smul_zero]
    have hxC : x ∈ C := by
      have : x = ∑ j, z j • B' j := by
        funext p; simp [hx, mulVec, dotProduct, hT, mul_comm]
      rw [this]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : (j : ℕ) < m
      · exact Submodule.smul_mem _ _ (hB'l j hj)
      · rw [hzsupp j hj, zero_smul]; exact Submodule.zero_mem _
    have hx0 : x = 0 := (Submodule.disjoint_def.mp hc.1) x hxC hxR
    have hz0 : z = 0 := by
      have : z = (T⁻¹) *ᵥ x := by
        rw [hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hdet, Matrix.one_mulVec]
      rw [this, hx0, mulVec_zero]
    apply hy0
    funext a
    have := hz (Fin.castLE hmn.le a)
    simp only [hz0, hyt, Pi.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (hAb_ne b hb)
  refine ⟨m, hmn, Tg, Matrix.of fun a b => M (Fin.castLE hmn.le a) (Fin.castLE hmn.le b), hdetG, ?_⟩
  intro i j
  show M i j = _
  by_cases h : (i : ℕ) < m ∧ (j : ℕ) < m
  · rw [dite_eq_left_of_eq_true (eq_true h)]; rfl
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    by_cases hi : (i : ℕ) < m
    · exact hMr i j fun hj => h ⟨hi, hj⟩
    · exact hMl i j hi

/-- The symmetric matrix of Cassels' example $f(x_0, x_1) = (2x_0 + (1 + \sqrt{-5})x_1)^{2}$ over
$\mathbb Z[\sqrt{-5}]$ (`ℤ√-5`): $F = vv^{t}$ with $v = (2, 1 + \sqrt{-5})$. -/
def sqrtNegFiveExample : Matrix (Fin 2) (Fin 2) (ℤ√(-5)) :=
  Matrix.vecMulVec ![2, ⟨1, 1⟩] ![2, ⟨1, 1⟩]

/-- **Cassels, Ch. 7, §4, p. 109 (7.r4)**: *the conclusion of Lemma 4.1 does not necessarily hold if $I$ is not a
principal ideal domain, e.g. $I = \mathbb Z[\sqrt{-5}]$: the form $(2x_1 + (1 + \sqrt{-5})x_2)^{2}$ is not
$\mathbb Z[\sqrt{-5}]$-equivalent to a form in 1 variable.* (Cassels' printed form is
$\{(1 + 2\sqrt{-5})x_1 + 3x_2\}^{2}$, see `not_equiv_one_var_printed`; this reconstruction, made before the page image
was read, is a second example of the same kind.) The form
is singular (`det = 0`), and there are no $T \in \mathrm{GL}_2(\mathbb Z[\sqrt{-5}])$ and $a$ with
$T^{t}FT = \begin{pmatrix} a & 0 \\ 0 & 0\end{pmatrix}$ (a form in the variable $y_0$ only; the variable $y_1$ alone is
the same after swapping the two variables). The reason is that the values $2x_0 + (1+\sqrt{-5})x_1$ fill the
non-principal ideal $(2, 1 + \sqrt{-5})$. Indices 0-based (Cassels: $x_1, x_2$). -/
@[kb "cassels1978" "Ch. 7, §4, p. 109 (a second example over ℤ[√−5], with the ideal (2, 1 + √−5); Cassels' form is in not_equiv_one_var_printed)"]
theorem not_equiv_one_var_zsqrtd :
    sqrtNegFiveExample.det = 0 ∧
      ¬ ∃ (T : GL (Fin 2) (ℤ√(-5))) (a : ℤ√(-5)),
          T.valᵀ * sqrtNegFiveExample * T.val = !![a, 0; 0, 0] := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp [sqrtNegFiveExample, vecMulVec_apply]
    ring
  · rintro ⟨T, a, h⟩
    have h11 := congrFun (congrFun h 1) 1
    have hTU : T.val * (T⁻¹).val = 1 := by simp
    have e00 := congrFun (congrFun hTU 0) 0
    have e10 := congrFun (congrFun hTU 1) 0
    have e01 := congrFun (congrFun hTU 0) 1
    have e11 := congrFun (congrFun hTU 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, one_ne_zero, not_false_eq_true, zero_ne_one, Fin.isValue] at e00 e10 e01 e11
    simp [Matrix.mul_apply, Fin.sum_univ_two, sqrtNegFiveExample] at h11
    set t00 := T.val 0 0
    set t01 := T.val 0 1
    set t10 := T.val 1 0
    set t11 := T.val 1 1
    set U00 := (T⁻¹).val 0 0
    set U01 := (T⁻¹).val 0 1
    set U10 := (T⁻¹).val 1 0
    set U11 := (T⁻¹).val 1 1
    -- `w = Tᵀ v` with `v = (2, 1 + √-5)`; `Tᵀ F T = diag(a, 0)` says `w wᵀ = diag(a, 0)`
    set w0 : ℤ√(-5) := t00 * 2 + t10 * ⟨1, 1⟩ with hw0
    set w1 : ℤ√(-5) := t01 * 2 + t11 * ⟨1, 1⟩ with hw1
    have hw1z : w1 * w1 = 0 := by rw [hw1]; linear_combination h11
    have hw1' : w1 = 0 := by
      have r := congrArg Zsqrtd.re hw1z
      have i := congrArg Zsqrtd.im hw1z
      simp at r i
      have hxy : w1.re * w1.im = 0 := by linarith
      rcases mul_eq_zero.mp hxy with h0 | h1
      · have h1 : w1.im = 0 := by rw [h0] at r; nlinarith [mul_self_nonneg w1.im]
        exact Zsqrtd.ext h0 h1
      · have h0 : w1.re = 0 := by rw [h1] at r; nlinarith [mul_self_nonneg w1.re]
        exact Zsqrtd.ext h0 h1
    -- hence `w0` divides both `2` and `1 + √-5`
    have hv0 : (2 : ℤ√(-5)) = U00 * w0 := by
      have : (2 : ℤ√(-5)) = U00 * w0 + U10 * w1 := by
        rw [hw0, hw1]; linear_combination (-2) * e00 - (⟨1, 1⟩ : ℤ√(-5)) * e10
      rw [this, hw1']; ring
    have hv1 : (⟨1, 1⟩ : ℤ√(-5)) = U01 * w0 := by
      have : (⟨1, 1⟩ : ℤ√(-5)) = U01 * w0 + U11 * w1 := by
        rw [hw0, hw1]; linear_combination (-2) * e01 - (⟨1, 1⟩ : ℤ√(-5)) * e11
      rw [this, hw1']; ring
    have n1 : w0.norm ∣ 4 := by
      have := congrArg Zsqrtd.norm hv0
      rw [Zsqrtd.norm_mul] at this
      exact ⟨U00.norm, by rw [mul_comm]; simpa [Zsqrtd.norm_def] using this⟩
    have n2 : w0.norm ∣ 6 := by
      have := congrArg Zsqrtd.norm hv1
      rw [Zsqrtd.norm_mul] at this
      exact ⟨U01.norm, by rw [mul_comm]; simpa [Zsqrtd.norm_def] using this⟩
    have n3 : w0.norm ∣ 2 := by
      have := dvd_sub n2 n1
      simpa using this
    -- `w0` lies in the ideal `(2, 1 + √-5)`, so `re ≡ im (mod 2)`, so its norm is even
    have hre : w0.re = 2 * t00.re + (t10.re - 5 * t10.im) := by
      simp [hw0]; ring
    have him : w0.im = 2 * t00.im + (t10.re + t10.im) := by
      simp [hw0]; ring
    have hN : w0.norm = w0.re * w0.re - (-5) * w0.im * w0.im := by
      simp [Zsqrtd.norm_def]
    have hnn : 0 ≤ w0.norm := by
      rw [hN]; nlinarith [mul_self_nonneg w0.re, mul_self_nonneg w0.im]
    have hle := Int.le_of_dvd (by norm_num) n3
    have hev : 2 ∣ w0.norm := by
      obtain ⟨k, hk⟩ : ∃ k, w0.re = w0.im + 2 * k := ⟨(w0.re - w0.im) / 2, by omega⟩
      exact ⟨k * (w0.re + w0.im) + 3 * w0.im * w0.im, by rw [hN, hk]; ring⟩
    have h2 : w0.norm = 2 := by
      rcases (show w0.norm = 0 ∨ w0.norm = 1 ∨ w0.norm = 2 by omega) with h | h | h
      · rw [h] at n3; simp at n3
      · omega
      · exact h
    -- but `x² + 5y² = 2` has no integer solution
    rw [hN] at h2
    have hy : w0.im = 0 ∨ w0.im ≠ 0 := em _
    rcases hy with hy | hy
    · rw [hy] at h2
      rcases (show w0.re ≤ -2 ∨ (-1 ≤ w0.re ∧ w0.re ≤ 1) ∨ 2 ≤ w0.re by omega) with h | h | h <;>
        nlinarith
    · nlinarith [mul_self_pos.mpr hy, mul_self_nonneg w0.re]

end QuadFormsKB.Cassels
