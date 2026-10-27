/-
# $L(1,\chi_{-4}) = \pi/4$ and $L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$

**Layer:** $\mathbb Q$ (the quadratic fields $\mathbb Q(i)$, $\mathbb Q(\sqrt2)$).

Dirichlet's class number formula (`classNumberFormula_neg`, `classNumberFormula_pos`) gives
$L(1,\chi_{-4}) = 2\pi h/(w\sqrt4)$ and $L(1,\chi_8) = 2hR/\sqrt8$; with $h = 1$ (`classNumber_QField_neg_four`,
`classNumber_QField_eight`, Minkowski's bound) it remains to compute
* $w(\mathbb Q(i)) = 4$ (**`torsionOrder_QField_neg_four`**): the units of $\mathbb Z[i]$ are $\pm1,\pm i$
  (`card_units_QOrder_neg_four`), and for $D<0$ every unit is a root of unity (`card_units_eq_torsionOrder`);
* $R(\mathbb Q(\sqrt2)) = \log(1+\sqrt2)$ (**`regulator_QField_eight`**): every unit of $\mathbb Z[\sqrt2]$ is $\pm\eta^j$,
  $\eta = 1+\sqrt2$ (`units_QOrder_eight`; the norm-one units are $\pm(3+2\sqrt2)^k = \pm\eta^{2k}$, `pell2_units`), so
  $\eta$ is a fundamental unit, and $R = |\log w(\eta)| = \log(1+\sqrt2)$ for either real place $w$
  ($w(\eta)\in\{1+\sqrt2,\sqrt2-1\}$).
Hence **`lFunction_kronecker_neg_four_one`** $L(1,\chi_{-4}) = \pi/4$ (Leibniz's value) and
**`lFunction_kronecker_eight_one`** $L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$. Unconditional.
-/
import QuadFormsKB.Tamagawa.Classical.BinaryJacobi

open NumberField NumberField.Units NumberField.InfinitePlace QuadraticAlgebra
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary

/-! ### The roots of unity of $\mathbb Q(i)$ -/

/-- Units of `QOrder (-4)` correspond to the integer solutions of $x_0^2 + x_1^2 = 1$ (the norm is a unit of $\mathbb Z$
and nonnegative). -/
def unitsQOrderNegFourEquiv :
    (QOrder (-4))ˣ ≃ {x : ℤ × ℤ // x.1 ^ 2 + x.2 ^ 2 = 1} where
  toFun u := ⟨(u.1.re, u.1.im), by
    have h : QuadraticAlgebra.norm (u.1 : QOrder (-4)) = 1 ∨
        QuadraticAlgebra.norm (u.1 : QOrder (-4)) = -1 :=
      Int.isUnit_iff.mp (isUnit_iff_norm_isUnit.mp u.isUnit)
    rw [QuadraticAlgebra.norm_def] at h
    simp [qa, qb] at h
    show u.1.re ^ 2 + u.1.im ^ 2 = 1
    rcases h with h | h <;> nlinarith [sq_nonneg u.1.re, sq_nonneg u.1.im]⟩
  invFun x := ⟨⟨x.1.1, x.1.2⟩, ⟨x.1.1, -x.1.2⟩, by
    have := x.2
    ext <;> simp [qa, qb] <;> nlinarith [x.2], by
    have := x.2
    ext <;> simp [qa, qb] <;> nlinarith [x.2]⟩
  left_inv u := by
    apply Units.ext
    rfl
  right_inv x := rfl

/-- **The units of $\mathbb Z[i]$** (`QOrder (-4)` $= \mathbb Z[\omega]$, $\omega^2 = -1$) are $\pm1, \pm i$: four of them. -/
theorem card_units_QOrder_neg_four : Nat.card (QOrder (-4))ˣ = 4 := by
  rw [Nat.card_congr unitsQOrderNegFourEquiv]
  have : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 2 = 1} =
      ↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      have ha : a ∈ Finset.Icc (-1 : ℤ) 1 := by
        simp only [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg b]
      have hb : b ∈ Finset.Icc (-1 : ℤ) 1 := by
        simp only [Finset.mem_Icc]; constructor <;> nlinarith [sq_nonneg a]
      simp only [Finset.mem_Icc] at ha hb
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      interval_cases a <;> interval_cases b <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  have h2 : Nat.card {x : ℤ × ℤ // x.1 ^ 2 + x.2 ^ 2 = 1} =
      Nat.card (↑({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        have := Set.ext_iff.mp this x
        simpa using this))
  rw [h2, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

/-- **$w(\mathbb Q(i)) = 4$**: $\mathbb Q(i)$ = `QField (-4)` has four roots of unity
(`NumberField.Units.torsionOrder`). -/
theorem torsionOrder_QField_neg_four : torsionOrder (QField (-4)) = 4 := by
  rw [← card_units_eq_torsionOrder (by norm_num), card_units_QOrder_neg_four]

/-! ### The regulator of $\mathbb Q(\sqrt2)$ -/

/-- The unit $\eta = 1 + \sqrt2$ of $\mathbb Z[\sqrt2]$ = `QOrder 8` ($\omega^2 = 2$), inverse $-1+\sqrt2$, norm $-1$. -/
def eta8 : (QOrder 8)ˣ where
  val := ⟨1, 1⟩
  inv := ⟨-1, 1⟩
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

/-- Norm-one elements of $\mathbb Z[\sqrt2]$ (Mathlib's `Pell.Solution₁ 2`) as units of `QOrder 8`. -/
def pellToUnit8 : Pell.Solution₁ 2 →* (QOrder 8)ˣ where
  toFun s :=
    { val := ⟨s.x, s.y⟩
      inv := ⟨s.x, -s.y⟩
      val_inv := by
        have := s.prop
        ext <;> simp [qa, qb] <;> nlinarith
      inv_val := by
        have := s.prop
        ext <;> simp [qa, qb] <;> nlinarith }
  map_one' := by ext <;> simp
  map_mul' s t := by
    ext <;> simp [qa, qb, Pell.Solution₁.x_mul,
      Pell.Solution₁.y_mul] <;> ring

/-- `pellToUnit8` commutes with negation. -/
theorem pellToUnit8_neg (s : Pell.Solution₁ 2) : pellToUnit8 (-s) = -pellToUnit8 s := by
  ext <;> simp [pellToUnit8]

/-- $3 + 2\sqrt2 = (1+\sqrt2)^2$. -/
theorem pellToUnit8_fund : pellToUnit8 pell2Fund = eta8 ^ 2 := by
  ext <;> simp [pellToUnit8, pell2Fund, eta8, pow_two, qa, qb]

/-- The units of norm one of $\mathbb Z[\sqrt2]$ are $\pm(1+\sqrt2)^{2k}$ (`pell2_units`). -/
theorem units8_of_norm_one (u : (QOrder 8)ˣ) (h : (u : QOrder 8).norm = 1) :
    ∃ k : ℤ, u = eta8 ^ (2 * k) ∨ u = -eta8 ^ (2 * k) := by
  have h' : (u : QOrder 8).re ^ 2 - 2 * (u : QOrder 8).im ^ 2 = 1 := by
    rw [QuadraticAlgebra.norm_def] at h
    simp [qa, qb] at h
    nlinarith
  obtain ⟨k, hk | hk⟩ := pell2_units (Pell.Solution₁.mk _ _ h')
  · refine ⟨k, Or.inl ?_⟩
    have := congrArg pellToUnit8 hk
    rw [map_zpow, pellToUnit8_fund, ← zpow_natCast, ← zpow_mul] at this
    rw [show ((2:ℕ):ℤ) * k = 2 * k by push_cast; ring] at this
    rw [← this]
    ext <;> simp [pellToUnit8]
  · refine ⟨k, Or.inr ?_⟩
    have := congrArg pellToUnit8 hk
    rw [pellToUnit8_neg, map_zpow, pellToUnit8_fund, ← zpow_natCast, ← zpow_mul] at this
    rw [show ((2:ℕ):ℤ) * k = 2 * k by push_cast; ring] at this
    rw [← this]
    ext <;> simp [pellToUnit8]

/-- **The units of $\mathbb Z[\sqrt2]$ are $\pm(1+\sqrt2)^j$**, $j\in\mathbb Z$. -/
theorem units_QOrder_eight (u : (QOrder 8)ˣ) : ∃ j : ℤ, u = eta8 ^ j ∨ u = -eta8 ^ j := by
  have hu : IsUnit ((u : QOrder 8).norm) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  rcases Int.isUnit_iff.mp hu with h | h
  · obtain ⟨k, hk⟩ := units8_of_norm_one u h
    exact ⟨2 * k, hk⟩
  · have h2 : ((u * eta8 : (QOrder 8)ˣ) : QOrder 8).norm = 1 := by
      rw [Units.val_mul, map_mul, h]
      simp [QuadraticAlgebra.norm_def, eta8, qa, qb]
    obtain ⟨k, hk⟩ := units8_of_norm_one _ h2
    have key : ∀ v : (QOrder 8)ˣ, v * eta8 = eta8 ^ (2 * k) ∨ v * eta8 = -eta8 ^ (2 * k) →
        v = eta8 ^ (2 * k - 1) ∨ v = -eta8 ^ (2 * k - 1) := by
      intro v hv
      rw [zpow_sub_one]
      rcases hv with hv | hv
      · left; rw [← hv]; group
      · right; rw [neg_mul_eq_neg_mul, ← hv]; group
    exact ⟨2 * k - 1, key u hk⟩

/-- The image of $\eta$ in $\mathbb Q(\sqrt2)$ is $1 + \omega$. -/
theorem coe_eta8 : ((orderEquiv 8 (eta8 : QOrder 8) : 𝓞 (QField 8)) : QField 8) = 1 + ω := by
  have := IsIntegralClosure.algebraMap_equiv ℤ (QOrder 8) (QField 8) (𝓞 (QField 8)) (eta8 : QOrder 8)
  refine this.trans ?_
  ext <;> simp [eta8]

/-- Every complex embedding of $\mathbb Q(\sqrt2)$ sends $\omega$ to $\pm\sqrt2$. -/
theorem embedding_omega8 (φ : QField 8 →+* ℂ) :
    φ ω = (Real.sqrt 2 : ℂ) ∨ φ ω = -(Real.sqrt 2 : ℂ) := by
  have h := embedding_sq φ
  have hb : (qb 8 : ℂ) = 0 := by simp [qb]
  rw [hb, sub_zero] at h
  have h2 : φ ω ^ 2 = ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    have : (2 * φ ω) ^ 2 = 8 := by exact_mod_cast h
    push_cast; linear_combination this / 4
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h2

/-- $|\log w(1+\sqrt2)| = \log(1+\sqrt2)$ at every infinite place $w$ of $\mathbb Q(\sqrt2)$ (both are real, and send
$1+\sqrt2$ to $1+\sqrt2$ or to $|1-\sqrt2| = (1+\sqrt2)^{-1}$). -/
theorem abs_log_eta8 (w : InfinitePlace (QField 8)) :
    |Real.log (w ((orderEquiv 8 (eta8 : QOrder 8) : 𝓞 (QField 8)) : QField 8))| = Real.log (1 + Real.sqrt 2) := by
  rw [coe_eta8, ← NumberField.InfinitePlace.norm_embedding_eq, map_add, map_one]
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases embedding_omega8 w.embedding with h | h
  · rw [h]
    have : ‖(1 : ℂ) + (Real.sqrt 2 : ℂ)‖ = 1 + Real.sqrt 2 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [this, abs_of_pos (Real.log_pos (by linarith))]
  · rw [h]
    have : ‖(1 : ℂ) + -(Real.sqrt 2 : ℂ)‖ = Real.sqrt 2 - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonpos (by linarith)]
      ring
    have hinv : Real.sqrt 2 - 1 = (1 + Real.sqrt 2)⁻¹ := by
      field_simp
      nlinarith
    rw [this, hinv, Real.log_inv, abs_neg, abs_of_pos (Real.log_pos (by linarith))]

/-- **$R(\mathbb Q(\sqrt2)) = \log(1+\sqrt2)$**: the regulator of $\mathbb Q(\sqrt2)$ = `QField 8`
(`NumberField.Units.regulator`) is the logarithm of the fundamental unit $1+\sqrt2$. -/
theorem regulator_QField_eight : regulator (QField 8) = Real.log (1 + Real.sqrt 2) := by
  classical
  have hrank : rank (QField 8) = 1 := by
    rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_of_pos (by norm_num),
      nrComplexPlaces_of_pos (by norm_num)]
  let i₀ : Fin (rank (QField 8)) := ⟨0, by rw [hrank]; norm_num⟩
  have hi₀ : ∀ b : Fin (rank (QField 8)), b = i₀ := fun b =>
    Fin.ext (by have h : (b : ℕ) < 1 := lt_of_lt_of_eq b.2 hrank; simp [i₀]; omega)
  obtain ⟨w⟩ : Nonempty (InfinitePlace (QField 8)) := inferInstance
  rw [regulator_of_pos (by norm_num) i₀ w]
  -- the logarithm of a unit at the place w
  set ℓ : (𝓞 (QField 8))ˣ → ℝ := fun u => Real.log (w (u : QField 8)) with hℓ
  have hℓmul : ∀ u v, ℓ (u * v) = ℓ u + ℓ v := fun u v => by
    simp only [hℓ, NumberField.Units.coe_mul, map_mul]
    exact Real.log_mul (pos_iff.2 (coe_ne_zero u)).ne' (pos_iff.2 (coe_ne_zero v)).ne'
  have hℓzpow : ∀ u (n : ℤ), ℓ (u ^ n) = n * ℓ u := fun u n => by
    simp only [hℓ, NumberField.Units.coe_zpow, map_zpow₀, Real.log_zpow]
  have hℓtors : ∀ ζ ∈ torsion (QField 8), ℓ ζ = 0 := fun ζ hζ => by
    simp [hℓ, (mem_torsion (QField 8)).1 hζ w]
  have hℓneg : ∀ u, ℓ (-u) = ℓ u := fun u => by
    rw [show -u = (-1) * u by simp, hℓmul, hℓtors _ neg_one_mem_torsion, zero_add]
  -- η = 1 + √2 as a unit of the ring of integers
  set f := Units.mapEquiv (orderEquiv 8).toRingEquiv.toMulEquiv with hf
  have hfneg : ∀ u, f (-u) = -f u := fun u => Units.ext (by simp [hf])
  set ε := fundSystem (QField 8) i₀ with hε
  have hη : |ℓ (f eta8)| = Real.log (1 + Real.sqrt 2) := abs_log_eta8 w
  -- η = ζ ε^k
  obtain ⟨⟨ζ, e⟩, hx, -⟩ := exist_unique_eq_mul_prod (QField 8) (f eta8)
  have hk : ℓ (f eta8) = e i₀ * ℓ ε := by
    rw [hx, hℓmul, hℓtors _ ζ.2, zero_add,
      Finset.prod_eq_single i₀ (fun b _ hb => (hb (hi₀ b)).elim) (fun h => (h (Finset.mem_univ _)).elim),
      hℓzpow]
  -- ε = ±η^j
  obtain ⟨j, hj⟩ := units_QOrder_eight (f.symm ε)
  have hj' : ℓ ε = j * ℓ (f eta8) := by
    have hεf : ε = f (f.symm ε) := (f.apply_symm_apply ε).symm
    rcases hj with h | h
    · rw [hεf, h, map_zpow, hℓzpow]
    · rw [hεf, h, hfneg, map_zpow, hℓneg, hℓzpow]
  have hpos : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith [Real.sqrt_pos.2 (two_pos (α := ℝ))])
  have hη0 : ℓ (f eta8) ≠ 0 := fun h => by rw [h, abs_zero] at hη; linarith
  have hej : ((e i₀ * j : ℤ) : ℝ) = 1 := by
    have h1 : ℓ (f eta8) = (e i₀ * j : ℤ) * ℓ (f eta8) :=
      calc ℓ (f eta8) = e i₀ * ℓ ε := hk
        _ = e i₀ * (j * ℓ (f eta8)) := by rw [hj']
        _ = (e i₀ * j : ℤ) * ℓ (f eta8) := by push_cast; ring
    have h2 : (((e i₀ * j : ℤ) : ℝ) - 1) * ℓ (f eta8) = 0 := by linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hη0)
  have hj1 : |(j : ℝ)| = 1 := by
    have : e i₀ * j = 1 := by exact_mod_cast hej
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  show |ℓ ε| = _
  rw [hj', abs_mul, hj1, one_mul, hη]

/-! ### The two $L$-values -/

/-- **$L(1,\chi_{-4}) = \pi/4$** (Leibniz's series $1 - \frac13 + \frac15 - \cdots$; here from Dirichlet's class number
formula $L(1,\chi_{-4}) = 2\pi h/(w\sqrt4)$ with $h = 1$, $w = 4$): $\chi_{-4}$ = `kroneckerChar (-4)`, and $L(1,\chi_{-4})$
is the value at $s = 1$ of Mathlib's `DirichletCharacter.LFunction`. Unconditional. -/
@[kb "davenport2000" "Ch. 6, (15) [unverified locator]; cassels1978 App. B, Thm. 2.1, p. 371"]
theorem lFunction_kronecker_neg_four_one : (kroneckerChar (-4)).LFunction 1 = ((π / 4 : ℝ) : ℂ) := by
  rw [classNumberFormula_neg (by norm_num), classNumber_QField_neg_four, torsionOrder_QField_neg_four]
  congr 1
  have h4 : |((-4 : ℤ) : ℝ)| = 2 ^ 2 := by norm_num
  rw [h4, Real.sqrt_sq (by norm_num)]
  push_cast
  ring

/-- **$L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$** (Dirichlet's class number formula $L(1,\chi_8) = 2hR/\sqrt8$ with $h = 1$,
$R = \log(1+\sqrt2)$): $\chi_8$ = `kroneckerChar 8`, and $L(1,\chi_8)$ is the value at $s = 1$ of Mathlib's
`DirichletCharacter.LFunction`. Unconditional. -/
@[kb "davenport2000" "Ch. 6, (17) [unverified locator]; cassels1978 App. B, Thm. 2.1, p. 371"]
theorem lFunction_kronecker_eight_one :
    (kroneckerChar 8).LFunction 1 = ((Real.log (1 + Real.sqrt 2) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [classNumberFormula_pos (by norm_num), classNumber_QField_eight, regulator_QField_eight]
  congr 1
  have h8 : Real.sqrt ((8 : ℤ) : ℝ) = 2 * Real.sqrt 2 := by
    rw [show ((8 : ℤ) : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h8]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- $L(1,\chi_{-4}) = \pi/4$ for the repository's `Binary.LOne` (the real part of the $L$-value). -/
theorem LOne_neg_four : Binary.LOne (-4) = π / 4 := by
  rw [Binary.LOne, lFunction_kronecker_neg_four_one, Complex.ofReal_re]

/-- $L(1,\chi_8) = \log(1+\sqrt2)/\sqrt2$ for the repository's `Binary.LOne`. -/
theorem LOne_eight : Binary.LOne 8 = Real.log (1 + Real.sqrt 2) / Real.sqrt 2 := by
  rw [Binary.LOne, lFunction_kronecker_eight_one, Complex.ofReal_re]

end QuadFormsKB.Tamagawa.Classical
