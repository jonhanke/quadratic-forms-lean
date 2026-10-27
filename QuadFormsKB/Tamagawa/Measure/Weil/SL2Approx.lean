import QuadFormsKB.Tamagawa.Measure.Weil.SL2Finite

/-!
# Strong approximation for $\mathrm{SL}_2$ over a number field

$F$ any number field.

* **`denseRange_algebraMap_finiteAdele`**: $F$ is dense in $\mathbb A_f$ (from `exists_strong_approx` and the product
  topology on $\hat{\mathcal O} = \prod_v\mathcal O_v$).
* **`exists_mul_slEmb_inv_mem_K`** (strong approximation for $\mathrm{SL}_2$): for every $g\in\mathrm{SL}_2(\mathbb A_F)$
  there is $\gamma\in\mathrm{SL}_2(F)$ such that $g\gamma^{-1}$ has all finite components in $\mathrm{SL}_2(\hat{\mathcal O})$,
  i.e. $\mathrm{SL}_2(\mathbb A_F) = (\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O}))\,\mathrm{SL}_2(F)$.
  *Proof:* every $g$ is a product $n^-(-s)\,n(p)\,n^-(c')\,n(q)$ of elementary matrices with adelic entries (place by
  place, with $c'$ a unit for almost all $v$: `loc_factor`, `exists_factor`); the closure of the subgroup of
  $g$ whose finite part is rational contains all elementary matrices ($F$ dense in $\mathbb A_f$), hence everything; and
  $\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O})$ is open.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open QuadFormsKB.WeilRep
open scoped ENNReal NNReal Pointwise Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### $F$ is dense in $\mathbb A_f$ -/

/-- **$F$ is dense in the finite adeles.** -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §15, Thm. (strong approximation), p. 67"]
theorem denseRange_algebraMap_finiteAdele : DenseRange (algebraMap F AF) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  obtain ⟨ξ₀, hξ₀⟩ := exists_sub_mem_OHat x
  set y := x - algebraMap F AF ξ₀ with hy
  have hW' : (fun t => t + algebraMap F AF ξ₀) ⁻¹' W ∈ 𝓝 y := by
    refine (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds ?_
    simpa [hy] using hW
  let z : OProd F := fun v => ⟨y v, hξ₀ v⟩
  have hz : iK F z = y := Subtype.ext (funext fun v => rfl)
  have hzW : iK F ⁻¹' ((fun t => t + algebraMap F AF ξ₀) ⁻¹' W) ∈ 𝓝 z :=
    (isOpenEmbedding_iK (F := F)).continuous.continuousAt.preimage_mem_nhds (by rw [hz]; exact hW')
  rw [nhds_pi, Filter.mem_pi'] at hzW
  obtain ⟨I, t, ht, hsub⟩ := hzW
  have hu : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u : Set (v.adicCompletion F),
      u ∈ 𝓝 ((z v : v.adicCompletionIntegers F) : v.adicCompletion F) ∧ Subtype.val ⁻¹' u ⊆ t v :=
    fun v => by
      obtain ⟨u, hu, hus⟩ := (mem_nhds_induced _ _ _).mp (ht v)
      exact ⟨u, hu, hus⟩
  choose u hu hus using hu
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > 0, Metric.ball ((z v : v.adicCompletionIntegers F) : v.adicCompletion F) ε ⊆ u v :=
    fun v => Metric.mem_nhds_iff.mp (hu v)
  choose ε hεpos hball using hε
  have hk : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, ‖QuadFormsKB.HN.ϖ v ^ (k : ℤ)‖ < ε v := by
    intro v
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (hεpos v) (QuadFormsKB.Analysis.norm_ϖ_lt_one v)
    exact ⟨k, by rw [zpow_natCast, norm_pow]; exact hk⟩
  choose kk hkk using hk
  obtain ⟨ξ₁, hS, hnS⟩ := QuadFormsKB.Analysis.exists_strong_approx I (fun v => y v) (fun v => (kk v : ℤ))
  have hclose : ∀ v ∈ I, algebraMap F (v.adicCompletion F) ξ₁ - y v ∈
      Metric.closedBall (0 : v.adicCompletion F) ‖QuadFormsKB.HN.ϖ v ^ (kk v : ℤ)‖ := by
    intro v hv
    rw [← QuadFormsKB.Analysis.coe_latticeV, SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV]
    exact hS v hv
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) ξ₁ ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : v ∈ I
    · have h1 : Valued.v (algebraMap F (v.adicCompletion F) ξ₁ - y v) ≤ 1 :=
        (hS v hv).trans (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
      have : algebraMap F (v.adicCompletion F) ξ₁ =
          (algebraMap F (v.adicCompletion F) ξ₁ - y v) + y v := by ring
      rw [this]
      exact add_mem (show _ ∈ v.adicCompletionIntegers F from h1) (hξ₀ v)
    · exact hnS v hv
  let w : OProd F := fun v => ⟨algebraMap F (v.adicCompletion F) ξ₁, hint v⟩
  have hwI : w ∈ (I : Set (HeightOneSpectrum (𝓞 F))).pi t := by
    intro v hv
    refine hus v (hball v ?_)
    rw [Metric.mem_ball, dist_eq_norm]
    have := hclose v hv
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact lt_of_le_of_lt this (hkk v)
  have hmem := hsub hwI
  simp only [Set.mem_preimage] at hmem
  have hw : iK F w = algebraMap F AF ξ₁ := Subtype.ext (funext fun v => rfl)
  rw [hw, ← map_add] at hmem
  exact ⟨_, hmem, ξ₁ + ξ₀, rfl⟩

/-! ### Local factorization into elementary matrices -/

section LocalFactor

variable {K : Type*} [Field K]

/-- The switch $s\in\{0, 1\}$: $s = 0$ if $c\ne0$ and $a/c\in B$, else $s = 1$. -/
def locS (B : Set K) (a c : K) : K := if c ≠ 0 ∧ a * c⁻¹ ∈ B then 0 else 1

theorem locS_cprime_ne_zero {B : Set K} (hB : (-1 : K) ∈ B) {a c : K} (h : a ≠ 0 ∨ c ≠ 0) :
    c + locS B a c * a ≠ 0 := by
  unfold locS
  split_ifs with hcond
  · rw [zero_mul, add_zero]; exact hcond.1
  · rw [one_mul]
    intro h0
    by_cases hc : c = 0
    · rw [hc, zero_add] at h0
      rcases h with ha | hc'
      · exact ha h0
      · exact hc' hc
    · apply hcond
      refine ⟨hc, ?_⟩
      have : a = -c := by linear_combination h0
      rw [this, neg_mul, mul_inv_cancel₀ hc]
      exact hB

/-- **Local factorization**: if $ad - bc = 1$ and $c' = c + sa\ne0$, then
$\begin{pmatrix}a&b\\c&d\end{pmatrix} = n^-(-s)\,n(p)\,n^-(c')\,n(q)$ with $p = (a-1)/c'$, $q = (d + sb - 1)/c'$; in
closed form the four entries are $1 + pc'$, $p + q + pc'q$, $c' - s(1 + pc')$, $1 + c'q - s(p + q + pc'q)$. -/
theorem loc_factor {a b c d s : K} (hdet : a * d - b * c = 1) (hc : c + s * a ≠ 0) :
    a = 1 + (a - 1) * (c + s * a)⁻¹ * (c + s * a) ∧
    b = (a - 1) * (c + s * a)⁻¹ + (d + s * b - 1) * (c + s * a)⁻¹ +
      (a - 1) * (c + s * a)⁻¹ * (c + s * a) * ((d + s * b - 1) * (c + s * a)⁻¹) ∧
    c = (c + s * a) - s * (1 + (a - 1) * (c + s * a)⁻¹ * (c + s * a)) ∧
    d = 1 + (c + s * a) * ((d + s * b - 1) * (c + s * a)⁻¹) - s * ((a - 1) * (c + s * a)⁻¹ +
      (d + s * b - 1) * (c + s * a)⁻¹ +
      (a - 1) * (c + s * a)⁻¹ * (c + s * a) * ((d + s * b - 1) * (c + s * a)⁻¹)) := by
  set c' := c + s * a with hc'
  have hp : (a - 1) * c'⁻¹ * c' = a - 1 := inv_mul_cancel_right₀ hc _
  have hq : c' * ((d + s * b - 1) * c'⁻¹) = d + s * b - 1 := by field_simp
  have hb : (a - 1) * c'⁻¹ + (d + s * b - 1) * c'⁻¹ + (a - 1) * c'⁻¹ * c' * ((d + s * b - 1) * c'⁻¹) = b := by
    rw [hp]
    field_simp
    rw [hc']
    linear_combination hdet
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]; ring
  · rw [hb]
  · rw [hp, hc']; ring
  · rw [hb, hq]; ring

end LocalFactor


section LocalInt

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- At a place where $g$ is integral, $c' = c + sa$ is a unit. -/
theorem locS_cprime_inv_integral (w : Valuation K Γ₀) {a b c d : K} (ha : w a ≤ 1) (hb : w b ≤ 1)
    (hc : w c ≤ 1) (hd : w d ≤ 1) (hdet : a * d - b * c = 1) :
    w (c + locS {x | w x ≤ 1} a c * a)⁻¹ ≤ 1 := by
  obtain ⟨-, -, hu⟩ := isPrim_of_det w ha hb hc hd hdet
  unfold locS
  split_ifs with hcond
  · rw [zero_mul, add_zero]
    rcases hu with ⟨ha0, hai⟩ | ⟨-, hci⟩
    · have : c⁻¹ = a⁻¹ * (a * c⁻¹) := by field_simp
      rw [this, Valuation.map_mul]
      exact mul_le_one' hai hcond.2
    · exact hci
  · rw [one_mul]
    by_cases hc0 : c = 0
    · rw [hc0, zero_add]
      rcases hu with ⟨-, hai⟩ | ⟨hc0', -⟩
      · exact hai
      · exact absurd hc0 hc0'
    · have hlt : ¬ w (a * c⁻¹) ≤ 1 := fun h => hcond ⟨hc0, h⟩
      rw [Valuation.map_mul, map_inv₀, not_le] at hlt
      have hca : w c < w a := by
        have hwc : 0 < w c := by rw [Valuation.pos_iff]; exact hc0
        calc w c = w c * 1 := (mul_one _).symm
          _ < w c * (w a * (w c)⁻¹) := mul_lt_mul_of_pos_left hlt hwc
          _ = w a := by field_simp
      have hwa1 : w a = 1 := by
        rcases hu with ⟨ha0, hai⟩ | ⟨-, hci⟩
        · rw [map_inv₀] at hai
          exact le_antisymm ha (by
            have h0 : 0 < w a := by rw [Valuation.pos_iff]; exact ha0
            rw [inv_le_one₀ h0] at hai; exact hai)
        · rw [map_inv₀] at hci
          have hc1 : w c = 1 := le_antisymm hc (by
            have h0 : 0 < w c := by rw [Valuation.pos_iff]; exact hc0
            rw [inv_le_one₀ h0] at hci; exact hci)
          exact absurd (hc1 ▸ hca) (not_lt.mpr ha)
      rw [map_inv₀, Valuation.map_add_eq_of_lt_right w hca, hwa1, inv_one]

end LocalInt

/-! ### Adelic factorization into elementary matrices -/

/-- The lower unipotent $n^-(x) = \begin{pmatrix}1&0\\x&1\end{pmatrix}$. -/
def nmA (x : Adeles F) : SL2A F := ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

theorem locS_zero_or_one {K : Type*} [Field K] (B : Set K) (a c : K) : locS B a c = 0 ∨ locS B a c = 1 := by
  unfold locS; split_ifs <;> simp

/-- The adelic switch $s$. -/
def sA (a c : Adeles F) : Adeles F :=
  ((fun w => locS ballR (a.1.1 w) (c.1.1 w), fun w => locS ballC (a.1.2 w) (c.1.2 w)),
    ⟨fun v => locS (v.adicCompletionIntegers F) (a.2 v) (c.2 v), Filter.Eventually.of_forall fun v => by
      show locS (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (a.2 v) (c.2 v) ∈
        v.adicCompletionIntegers F
      rcases locS_zero_or_one (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (a.2 v) (c.2 v) with h | h
      · rw [h]; exact zero_mem _
      · rw [h]; exact one_mem _⟩)

theorem neg_one_mem_ballR : (-1 : ℝ) ∈ ballR := by simp [ballR]
theorem neg_one_mem_ballC : (-1 : ℂ) ∈ ballC := by simp [ballC]


/-- The entries of `g`. -/
abbrev gA (g : SL2A F) (i j : Fin 2) : Adeles F := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) i j

theorem gA_det (g : SL2A F) : gA g 0 0 * gA g 1 1 - gA g 0 1 * gA g 1 0 = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (Adeles F)).det = 1 := g.2
  rwa [Matrix.det_fin_two] at hdet

/-- $c' = c + sa$. -/
def cpA (g : SL2A F) : Adeles F := gA g 1 0 + sA (gA g 0 0) (gA g 1 0) * gA g 0 0

theorem ne_zero_or_of_det {K : Type*} [Field K] {a b c d : K} (h : a * d - b * c = 1) : a ≠ 0 ∨ c ≠ 0 := by
  by_contra hh
  push Not at hh
  rw [hh.1, hh.2] at h; simp at h

/-- The componentwise inverse of $c'$ (an idele). -/
def cinvA (g : SL2A F) : Adeles F :=
  ((fun w => ((cpA g).1.1 w)⁻¹, fun w => ((cpA g).1.2 w)⁻¹),
    ⟨fun v => ((cpA g).2 v)⁻¹, by
      have h00 : ∀ᶠ v in cofinite, (gA g 0 0).2 v ∈ v.adicCompletionIntegers F := (gA g 0 0).2.2
      have h01 : ∀ᶠ v in cofinite, (gA g 0 1).2 v ∈ v.adicCompletionIntegers F := (gA g 0 1).2.2
      have h10 : ∀ᶠ v in cofinite, (gA g 1 0).2 v ∈ v.adicCompletionIntegers F := (gA g 1 0).2.2
      have h11 : ∀ᶠ v in cofinite, (gA g 1 1).2 v ∈ v.adicCompletionIntegers F := (gA g 1 1).2.2
      filter_upwards [h00, h01, h10, h11] with v ha hb hc hd
      exact locS_cprime_inv_integral (valV v) ha hb hc hd (congrArg (fun z : Adeles F => z.2 v) (gA_det g))⟩)

theorem cinvA_mul_cpA (g : SL2A F) : cinvA g * cpA g = 1 := by
  have hdet := gA_det g
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) (Subtype.ext (funext fun v => ?_))
  · show ((cpA g).1.1 w)⁻¹ * (cpA g).1.1 w = 1
    refine inv_mul_cancel₀ (locS_cprime_ne_zero neg_one_mem_ballR (ne_zero_or_of_det (b := (gA g 0 1).1.1 w)
      (d := (gA g 1 1).1.1 w) (congrArg (fun z : Adeles F => z.1.1 w) hdet)))
  · show ((cpA g).1.2 w)⁻¹ * (cpA g).1.2 w = 1
    refine inv_mul_cancel₀ (locS_cprime_ne_zero neg_one_mem_ballC (ne_zero_or_of_det (b := (gA g 0 1).1.2 w)
      (d := (gA g 1 1).1.2 w) (congrArg (fun z : Adeles F => z.1.2 w) hdet)))
  · show ((cpA g).2 v)⁻¹ * (cpA g).2 v = 1
    have hm1 : (-1 : v.adicCompletion F) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      neg_mem (one_mem _)
    exact inv_mul_cancel₀ (locS_cprime_ne_zero hm1 (ne_zero_or_of_det (b := (gA g 0 1).2 v)
      (d := (gA g 1 1).2 v) (congrArg (fun z : Adeles F => z.2 v) hdet)))

/-- **Every $g\in\mathrm{SL}_2(\mathbb A_F)$ is a product of four elementary matrices**
$n^-(-s)\,n(p)\,n^-(c')\,n(q)$ with adelic entries. -/
theorem eq_factor (g : SL2A F) :
    g = nmA (-sA (gA g 0 0) (gA g 1 0)) * nA ((gA g 0 0 - 1) * cinvA g) * nmA (cpA g) *
      nA ((gA g 1 1 + sA (gA g 0 0) (gA g 1 0) * gA g 0 1 - 1) * cinvA g) := by
  have hdet := gA_det g
  have hu := cinvA_mul_cpA g
  have hc' : cpA g = gA g 1 0 + sA (gA g 0 0) (gA g 1 0) * gA g 0 0 := rfl
  rw [hc'] at hu ⊢
  generalize sA (gA g 0 0) (gA g 1 0) = s at hu ⊢
  generalize cinvA g = u at hu ⊢
  simp only [gA] at hdet hu ⊢
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  set a := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) (Adeles F)) 1 1
  fin_cases i <;> fin_cases j <;>
    simp [nmA, nA, Matrix.mul_apply, Fin.sum_univ_two, -Matrix.SpecialLinearGroup.coe_matrix_coe]
  · linear_combination (-(a - 1)) * hu
  · linear_combination (-(b + (a - 1) * (d + s * b - 1) * u)) * hu - u * hdet
  · linear_combination s * (a - 1) * hu
  · linear_combination s * ((b + (a - 1) * (d + s * b - 1) * u) * hu + u * hdet) - (d + s * b - 1) * hu


/-! ### The closure argument -/

theorem mul_mem_OHat {x y : AF} (hx : x ∈ OHat) (hy : y ∈ OHat) : x * y ∈ OHat :=
  fun v => mul_mem (hx v) (hy v)

theorem one_mem_OHat : (1 : AF) ∈ OHat := fun v => one_mem _

variable (F) in
/-- The finite part $\mathrm{SL}_2(\mathbb A_F)\to\mathrm{SL}_2(\mathbb A_f)$. -/
def finPartSL : SL2A F →* SL(2, AF) := Matrix.SpecialLinearGroup.map (RingHom.snd _ _)

variable (F) in
/-- $\mathrm{SL}_2(F)\to\mathrm{SL}_2(\mathbb A_f)$. -/
def ratFinSL : SL(2, F) →* SL(2, AF) := Matrix.SpecialLinearGroup.map (algebraMap F AF)

theorem finPartSL_slEmb (γ : SL(2, F)) : finPartSL F (slEmb F γ) = ratFinSL F γ := rfl

variable (F) in
/-- $\mathrm{SL}_2(\hat{\mathcal O})\le\mathrm{SL}_2(\mathbb A_f)$. -/
def KO : Subgroup (SL(2, AF)) where
  carrier := {M | ∀ i j, (M : Matrix (Fin 2) (Fin 2) AF) i j ∈ OHat}
  mul_mem' {M N} hM hN i j := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem_OHat (mul_mem_OHat (hM i 0) (hN 0 j)) (mul_mem_OHat (hM i 1) (hN 1 j))
  one_mem' i j := by
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]; exact one_mem_OHat
    · simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne hij]; exact zero_mem_OHat
  inv_mem' {M} hM i j := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp
    · exact hM 1 1
    · exact neg_mem_OHat (hM 0 1)
    · exact neg_mem_OHat (hM 1 0)
    · exact hM 0 0

variable (F) in
/-- $\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O})$. -/
def KSub : Subgroup (SL2A F) := (KO F).comap (finPartSL F)

theorem mem_KSub {g : SL2A F} : g ∈ KSub F ↔ ∀ i j, (gA g i j).2 ∈ OHat := Iff.rfl

theorem isOpen_KSub : IsOpen (KSub F : Set (SL2A F)) := by
  have : (KSub F : Set (SL2A F)) = ⋂ i, ⋂ j, (fun g : SL2A F => (gA g i j).2) ⁻¹' OHat := by
    ext g; simp [mem_KSub]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_OHat.preimage (continuous_snd.comp (continuous_SL2A_entry i j))

variable (F) in
/-- The subgroup of $g$ whose finite part is rational. -/
def HSub : Subgroup (SL2A F) := (ratFinSL F).range.comap (finPartSL F)

theorem continuous_nA : Continuous (nA (F := F)) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const
  · exact continuous_const

theorem continuous_nmA : Continuous (nmA (F := F)) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const

theorem nA_mem_closure (x : Adeles F) : nA x ∈ (HSub F).topologicalClosure := by
  have hc : Continuous fun y : AF => nA ((x.1, y) : Adeles F) :=
    continuous_nA.comp (continuous_const.prodMk continuous_id)
  have hmaps : Set.MapsTo (fun y : AF => nA ((x.1, y) : Adeles F)) (Set.range (algebraMap F AF))
      (HSub F) := by
    rintro _ ⟨ξ, rfl⟩
    refine ⟨nMat ξ, ?_⟩
    refine Subtype.ext (funext fun i => funext fun j => ?_)
    change ((nMat ξ : Matrix (Fin 2) (Fin 2) F).map (algebraMap F AF)) i j =
      ((nA ((x.1, algebraMap F AF ξ) : Adeles F) : Matrix (Fin 2) (Fin 2) (Adeles F)).map
        (RingHom.snd (mixedSpace F) AF)) i j
    fin_cases i <;> fin_cases j <;> simp [nMat, nA]
  have := map_mem_closure (f := fun y : AF => nA ((x.1, y) : Adeles F)) hc
    (denseRange_algebraMap_finiteAdele x.2) hmaps
  exact this

theorem nmA_mem_closure (x : Adeles F) : nmA x ∈ (HSub F).topologicalClosure := by
  have hc : Continuous fun y : AF => nmA ((x.1, y) : Adeles F) :=
    continuous_nmA.comp (continuous_const.prodMk continuous_id)
  have hmaps : Set.MapsTo (fun y : AF => nmA ((x.1, y) : Adeles F)) (Set.range (algebraMap F AF))
      (HSub F) := by
    rintro _ ⟨ξ, rfl⟩
    refine ⟨⟨!![1, 0; ξ, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
    refine Subtype.ext (funext fun i => funext fun j => ?_)
    change ((!![1, 0; ξ, 1] : Matrix (Fin 2) (Fin 2) F).map (algebraMap F AF)) i j =
      ((nmA ((x.1, algebraMap F AF ξ) : Adeles F) : Matrix (Fin 2) (Fin 2) (Adeles F)).map
        (RingHom.snd (mixedSpace F) AF)) i j
    fin_cases i <;> fin_cases j <;> simp [nmA]
  have := map_mem_closure (f := fun y : AF => nmA ((x.1, y) : Adeles F)) hc
    (denseRange_algebraMap_finiteAdele x.2) hmaps
  exact this

/-- **Strong approximation for $\mathrm{SL}_2$ over a number field**: every $g\in\mathrm{SL}_2(\mathbb A_F)$ is
$k\gamma$ with $k\in\mathrm{SL}_2(F_\infty)\times\mathrm{SL}_2(\hat{\mathcal O})$ and $\gamma\in\mathrm{SL}_2(F)$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §15, Thm. (strong approximation), p. 67 (the additive group only)"]
theorem exists_mul_slEmb_inv_mem_K (g : SL2A F) : ∃ γ : SL(2, F), g * (slEmb F γ)⁻¹ ∈ KSub F := by
  have hg : g ∈ (HSub F).topologicalClosure := by
    rw [eq_factor g]
    exact mul_mem (mul_mem (mul_mem (nmA_mem_closure _) (nA_mem_closure _)) (nmA_mem_closure _))
      (nA_mem_closure _)
  have hU : IsOpen {x : SL2A F | x * g⁻¹ ∈ KSub F} :=
    isOpen_KSub.preimage (continuous_id.mul continuous_const)
  have hgU : g ∈ {x : SL2A F | x * g⁻¹ ∈ KSub F} := by
    show g * g⁻¹ ∈ KSub F; rw [mul_inv_cancel]; exact one_mem _
  obtain ⟨x, hxU, hxH⟩ := mem_closure_iff.mp hg _ hU hgU
  obtain ⟨γ, hγ⟩ := hxH
  refine ⟨γ, ?_⟩
  have hinv : g * x⁻¹ ∈ KSub F := by
    have := inv_mem (show x * g⁻¹ ∈ KSub F from hxU)
    rwa [mul_inv_rev, inv_inv] at this
  show finPartSL F (g * (slEmb F γ)⁻¹) ∈ KO F
  have : finPartSL F (g * (slEmb F γ)⁻¹) = finPartSL F (g * x⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv, finPartSL_slEmb, hγ]
  rw [this]; exact hinv

end

end QuadFormsKB.Tamagawa.Measure.Weil
