/-
# Alternating matrices and a parity lemma for $2$-adic Wall forms

Algebra used for the $2$-adic upper bound of `Section9EvenUnimodular.lean` (Conway–Sloane, *Sphere Packings,
Lattices and Groups*, Ch. 15, §9.5–9.6).

**Proves**
* `det_eq_zero_of_alternating`: over any commutative ring, a matrix $M$ with $M_{ij} = -M_{ji}$ and $M_{ii} = 0$ of odd
  size has determinant $0$ (from the generic alternating matrix over $\mathbb Z[x_{ij}]$, where
  $\det X = \det X^{\mathsf T} = -\det X$);
* `exists_sq_prod_valued` (**the level lemma**): over $F_\mathfrak p = $ `v.adicCompletion ℚ`, let $U$ be an integral
  matrix with $\lvert\det U\rvert = 1$ and $a_0, \dots, a_{m-1}$ nonzero integers such that $C = U\,\mathrm{diag}(a)^{-1}$
  has $C + C^{\mathsf T}$ integral and integral diagonal. Then $\prod_j \lvert a_j\rvert$ is a square in
  $\mathbb Z^{\mathrm m 0}$.

*Proof of the level lemma.* Reduce $U$ modulo $\mathfrak p$. If $\lvert a_j\rvert < \lvert a_i\rvert$ then
$U_{ij} \equiv 0$ (from $U_{ij} + U_{ji}a_j/a_i \in a_j\mathfrak o$), so $\bar U$ is block triangular for the levels
$\lvert a_j\rvert$ and every diagonal block is invertible (Mathlib's `Matrix.det_of_blockTriangular`). On a block of level
$\lvert t\rvert < 1$, the matrix $\bar U_{ij}\,\overline{t/a_j}$ is alternating, so the block has even size. Hence each
level below $1$ occurs an even number of times.
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.MvPolynomial.CommRing
import QuadFormsKB.LocalDensity.NFBridge

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane.Levels

/-! ### Alternating matrices of odd size -/

section Alternating

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]

/-- The generic alternating matrix over $\mathbb Z[x_{ij}]$. -/
def genericAlt : Matrix ι ι (MvPolynomial (ι × ι) ℤ) := fun i j =>
  if i < j then MvPolynomial.X (i, j) else if j < i then -MvPolynomial.X (j, i) else 0

theorem genericAlt_transpose : (genericAlt (ι := ι))ᵀ = -genericAlt := by
  funext i j
  show genericAlt j i = -genericAlt i j
  unfold genericAlt
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt_of_gt h]
  · simp
  · simp [h, not_lt_of_gt h]

theorem det_genericAlt_eq_zero (hodd : Odd (Fintype.card ι)) : (genericAlt (ι := ι)).det = 0 := by
  have h := congrArg Matrix.det (genericAlt_transpose (ι := ι))
  rw [det_transpose, det_neg, hodd.neg_one_pow, neg_one_mul] at h
  have h2 : (2 : MvPolynomial (ι × ι) ℤ) * (genericAlt (ι := ι)).det = 0 := by
    rw [two_mul]; nth_rewrite 1 [h]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exfalso
    have : (2 : MvPolynomial (ι × ι) ℤ) = MvPolynomial.C 2 := by simp
    rw [this, MvPolynomial.C_eq_zero] at h3
    norm_num at h3
  · exact h3

/-- **Alternating matrices of odd size are singular**, over any commutative ring. -/
theorem det_eq_zero_of_alternating {R : Type*} [CommRing R] (M : Matrix ι ι R) (hskew : ∀ i j, M i j = -M j i)
    (hdiag : ∀ i, M i i = 0) (hodd : Odd (Fintype.card ι)) : M.det = 0 := by
  set φ : MvPolynomial (ι × ι) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) fun p => M p.1 p.2
  have hM : (genericAlt (ι := ι)).map φ = M := by
    ext i j
    simp only [map_apply, genericAlt]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, φ]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h, φ, ← hskew]
  rw [← hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_genericAlt_eq_zero hodd, map_zero]

/-- An invertible alternating matrix has even size. -/
theorem even_card_of_alternating {R : Type*} [CommRing R] [Nontrivial R] (M : Matrix ι ι R)
    (hskew : ∀ i j, M i j = -M j i) (hdiag : ∀ i, M i i = 0) (hdet : M.det ≠ 0) : Even (Fintype.card ι) := by
  by_contra h
  exact hdet (det_eq_zero_of_alternating M hskew hdiag (Nat.not_even_iff_odd.mp h))

end Alternating

/-! ### The level lemma -/

section LevelLemma

open IsDedekindDomain NumberField WithZero

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem lt_one_of_le_lt {x y : ℤᵐ⁰} (hx : x ≤ 1) (hy : y < 1) : x * y < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_left' hx) hy

theorem lt_one_of_lt_le {x y : ℤᵐ⁰} (hx : x < 1) (hy : y ≤ 1) : x * y < 1 := by
  rw [mul_comm]; exact lt_one_of_le_lt hy hx

theorem isUnit_iff_valued (x : 𝔬) : IsUnit x ↔ Valued.v (x : Fv) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := u.val.2
    have h2 := u.inv.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
    have h3 : Valued.v ((u.val : Fv)) * Valued.v ((u.inv : Fv)) = 1 := by
      rw [← map_mul]
      have : ((u.val : 𝔬) : Fv) * ((u.inv : 𝔬) : Fv) = 1 := by
        rw [← Subring.coe_mul, u.val_inv]; rfl
      rw [this, map_one]
    by_contra hne
    have hlt : Valued.v ((u.val : Fv)) < 1 := lt_of_le_of_ne h1 hne
    have := lt_one_of_lt_le hlt h2
    rw [h3] at this
    exact lt_irrefl _ this
  · intro h
    have hx0 : (x : Fv) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hinv : (x : Fv)⁻¹ ∈ 𝔬 := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]
    refine ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (x : Fv) * (x : Fv)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    · apply Subtype.ext
      change (x : Fv)⁻¹ * (x : Fv) = 1
      exact inv_mul_cancel₀ hx0

theorem residue_eq_zero_iff_valued (x : 𝔬) : IsLocalRing.residue 𝔬 x = 0 ↔ Valued.v (x : Fv) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_valued]
  have := x.2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  constructor
  · intro h; exact lt_of_le_of_ne this h
  · intro h; exact ne_of_lt h

/-- The integral matrix with entries in $\mathfrak o$ of a matrix with integral entries. -/
def toO {m : ℕ} (U : Matrix (Fin m) (Fin m) Fv) (hU : ∀ i j, Valued.v (U i j) ≤ 1) : Matrix (Fin m) (Fin m) 𝔬 :=
  Matrix.of fun i j => ⟨U i j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hU i j)⟩

theorem toO_map {m : ℕ} (U : Matrix (Fin m) (Fin m) Fv) (hU : ∀ i j, Valued.v (U i j) ≤ 1) :
    (toO U hU).map (fun x : 𝔬 => (x : Fv)) = U := by
  ext i j; rfl

theorem det_toO {m : ℕ} (U : Matrix (Fin m) (Fin m) Fv) (hU : ∀ i j, Valued.v (U i j) ≤ 1) :
    (((toO U hU).det : 𝔬) : Fv) = U.det := by
  have := RingHom.map_det (𝔬).subtype (toO U hU)
  rw [RingHom.mapMatrix_apply] at this
  change (𝔬).subtype (toO U hU).det = _
  rw [this]
  rfl

/-- **The level lemma.** Let $U$ be an integral matrix with $\lvert\det U\rvert = 1$ and $a_j \ne 0$ integral, and
suppose $C = U\,\mathrm{diag}(a)^{-1}$ has $C + C^{\mathsf T}$ and the diagonal of $C$ integral. Then
$\prod_j \lvert a_j\rvert$ is a square. -/
theorem exists_sq_prod_valued {m : ℕ} (U : Matrix (Fin m) (Fin m) Fv) (a : Fin m → Fv)
    (hU : ∀ i j, Valued.v (U i j) ≤ 1) (hdet : Valued.v U.det = 1) (ha : ∀ j, a j ≠ 0)
    (ha1 : ∀ j, Valued.v (a j) ≤ 1) (hsym : ∀ i j, Valued.v (U i j / a j + U j i / a i) ≤ 1)
    (hdiag : ∀ i, Valued.v (U i i / a i) ≤ 1) : ∃ γ : ℤᵐ⁰, ∏ j, Valued.v (a j) = γ ^ 2 := by
  classical
  set res := IsLocalRing.residue 𝔬
  set Ub := (toO U hU).map res
  set b : Fin m → ℤᵐ⁰ := fun j => Valued.v (a j)
  have hva : ∀ j, Valued.v (a j) ≠ 0 := fun j => (Valuation.ne_zero_iff _).mpr (ha j)
  -- `Ub` is block triangular for the levels `b`
  have hlow : ∀ i j, b j < b i → Valued.v (U i j) < 1 := by
    intro i j hlt
    have h1 := hsym i j
    have hai : a i ≠ 0 := ha i
    have haj : a j ≠ 0 := ha j
    have e : U i j = a j * (U i j / a j + U j i / a i) - U j i * (a j / a i) := by
      field_simp; ring
    rw [e]
    have hbj : Valued.v (a j) < 1 := lt_of_lt_of_le hlt (ha1 i)
    have t1 : Valued.v (a j * (U i j / a j + U j i / a i)) < 1 := by
      rw [map_mul]; exact lt_one_of_lt_le hbj h1
    have t2 : Valued.v (U j i * (a j / a i)) < 1 := by
      rw [map_mul, map_div₀]
      have : Valued.v (a j) / Valued.v (a i) < 1 := by
        rw [div_lt_one₀ (zero_lt_iff.mpr (hva i))]; exact hlt
      exact lt_one_of_le_lt (hU j i) this
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt t1 t2)
  have hbt : Ub.BlockTriangular b := by
    intro i j hlt
    change res (toO U hU i j) = 0
    rw [residue_eq_zero_iff_valued]
    exact hlow i j hlt
  have hdetb : Ub.det ≠ 0 := by
    have e := RingHom.map_det res (toO U hU)
    rw [RingHom.mapMatrix_apply] at e
    change ((toO U hU).map res).det ≠ 0
    rw [← e]
    intro h0
    rw [residue_eq_zero_iff_valued, det_toO, hdet] at h0
    exact lt_irrefl _ h0
  rw [hbt.det] at hdetb
  -- each level below `1` occurs an even number of times
  have heven : ∀ k ∈ Finset.univ.image b, k < 1 → Even (Fintype.card {j // b j = k}) := by
    intro k hk hk1
    obtain ⟨j0, -, hj0⟩ := Finset.mem_image.mp hk
    have hblock : (Ub.toSquareBlock b k).det ≠ 0 := Finset.prod_ne_zero_iff.mp hdetb k hk
    set t := a j0
    have hvt : Valued.v t = k := hj0
    -- scaling units
    have hsc : ∀ j : {j // b j = k}, Valued.v (t / a j) = 1 := by
      intro j
      have hj : Valued.v (a j) = k := j.2
      rw [map_div₀, hvt, hj, div_self (by rw [← hj]; exact hva j)]
    set w : {j // b j = k} → 𝔬 := fun j =>
      ⟨t / a j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_of_eq (hsc j))⟩
    set N : Matrix {j // b j = k} {j // b j = k} (IsLocalRing.ResidueField 𝔬) :=
      Ub.toSquareBlock b k * Matrix.diagonal fun j => res (w j)
    have hNe : ∀ i j : {j // b j = k}, N i j = res (toO U hU i j * w j) := by
      intro i j
      simp only [N, mul_diagonal, toSquareBlock_def, Ub, map_apply, map_mul]
      rfl
    have hint : ∀ x : Fv, Valued.v x ≤ 1 → Valued.v (t * x) < 1 := fun x hx => by
      rw [map_mul, hvt]; exact lt_one_of_lt_le hk1 hx
    have hNskew : ∀ i j, N i j = -N j i := by
      intro i j
      rw [hNe, hNe, eq_neg_iff_add_eq_zero, ← map_add, residue_eq_zero_iff_valued]
      have : ((toO U hU i j * w j + toO U hU j i * w i : 𝔬) : Fv) = t * (U i j / a j + U j i / a i) := by
        change U i j * (t / a j) + U j i * (t / a i) = _
        ring
      rw [this]; exact hint _ (hsym i j)
    have hNdiag : ∀ i, N i i = 0 := by
      intro i
      rw [hNe, residue_eq_zero_iff_valued]
      have : ((toO U hU i i * w i : 𝔬) : Fv) = t * (U i i / a i) := by
        change U i i * (t / a i) = _
        ring
      rw [this]; exact hint _ (hdiag i)
    have hNdet : N.det ≠ 0 := by
      rw [det_mul, det_diagonal]
      refine mul_ne_zero hblock (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
      rw [Ne, residue_eq_zero_iff_valued]
      change ¬ Valued.v (t / a j) < 1
      rw [hsc j]; exact lt_irrefl _
    exact even_card_of_alternating N hNskew hNdiag hNdet
  -- assemble
  refine ⟨∏ k ∈ Finset.univ.image b, k ^ ((Finset.univ.filter fun j => b j = k).card / 2), ?_⟩
  rw [← Finset.prod_pow, ← Finset.prod_fiberwise_of_maps_to (g := b) (t := Finset.univ.image b)
    (fun j _ => Finset.mem_image_of_mem b (Finset.mem_univ j))]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Finset.prod_congr rfl (fun j hj => (Finset.mem_filter.mp hj).2), Finset.prod_const, ← pow_mul]
  rcases lt_or_eq_of_le (show k ≤ 1 from by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk; exact ha1 j) with hk1 | hk1
  · have h := heven k hk hk1
    rw [Fintype.card_subtype] at h
    rw [Nat.div_mul_cancel (even_iff_two_dvd.mp h)]
  · rw [hk1, one_pow, one_pow]

end LevelLemma

end QuadFormsKB.ConwaySloane.Levels
