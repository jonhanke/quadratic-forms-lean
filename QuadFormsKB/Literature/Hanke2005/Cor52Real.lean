import QuadFormsKB.Literature.Hanke2005.Cor52Form
import QuadFormsKB.Literature.OMeara.Sec101BD
import QuadFormsKB.Lattices.SpinorKernel

/-!
# The counterexample to Hanke's Corollary 5.2(ii): the real places

For $d=-(\alpha+2)=-s$ and the form $Q=Q_0'\otimes k$ of `Cor52Form.lean`:
* `exists_embedding_lt`, `exists_embedding_gt`: real embeddings with $\alpha<-2$ (where $s<0$) and $\alpha>3$ (where $s>0$);
* `not_isSquare_d`: $d$ is not a square in $k$ (it is negative at a real embedding);
* `hiso`: at every infinite place, $d$ is a square in $k_w$ or $Q$ is anisotropic over $k_w$ (at a real place either
  $s<0$, so $d>0$, or $s>0$ and $Q$ is positive definite);
* `isIndefinite_QF`: $Q$ is isotropic at a real place (where $s<0$).
-/

open Polynomial NumberField

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

open QuadFormsKB QuadFormsKB.Lattices

/-- $d=-(\alpha+2)$. -/
theorem d_eq : d = -(α + 2) := rfl

/-- A real root of $y^3-y^2-10y-7$ gives a real embedding of $k$ sending $\alpha$ to it. -/
theorem exists_embedding_of_root (r : ℝ) (hr : r ^ 3 - r ^ 2 - 10 * r - 7 = 0) :
    ∃ φ : K →+* ℝ, φ α = r := by
  have h : eval₂ (algebraMap ℚ ℝ) r poly = 0 := by
    simp [poly]
    linear_combination hr
  exact ⟨AdjoinRoot.lift (algebraMap ℚ ℝ) r h, AdjoinRoot.lift_root h⟩

theorem exists_embedding_lt : ∃ φ : K →+* ℝ, φ α < -2 := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ 3 - t ^ 2 - 10 * t - 7) (Set.Icc (-2.2) (-2)) := by fun_prop
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (by norm_num) hcont (show (0 : ℝ) ∈ Set.Icc _ _ by
    constructor <;> norm_num)
  obtain ⟨φ, hφ⟩ := exists_embedding_of_root r hr0
  refine ⟨φ, ?_⟩
  rw [hφ]
  rcases hr.2.lt_or_eq with h | h
  · exact h
  · exfalso; rw [h] at hr0; norm_num at hr0

theorem exists_embedding_gt : ∃ φ : K →+* ℝ, 3 < φ α := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ 3 - t ^ 2 - 10 * t - 7) (Set.Icc 3.9 4) := by fun_prop
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc (by norm_num) hcont (show (0 : ℝ) ∈ Set.Icc _ _ by
    constructor <;> norm_num)
  obtain ⟨φ, hφ⟩ := exists_embedding_of_root r hr0
  refine ⟨φ, ?_⟩
  rw [hφ]
  linarith [hr.1]

/-- $d$ is not a square in $k$: it is negative at a real embedding. -/
theorem not_isSquare_d : ¬ IsSquare d := by
  rintro ⟨y, hy⟩
  obtain ⟨φ, hφ⟩ := exists_embedding_gt
  have := congrArg φ hy
  rw [d_eq, map_mul, map_neg, map_add] at this
  have h2 : φ 2 = 2 := map_ofNat φ 2
  rw [h2] at this
  nlinarith [mul_self_nonneg (φ y)]

theorem d_ne_zero : d ≠ 0 := by
  intro h
  exact not_isSquare_d (h ▸ ⟨0, by simp⟩)

/-- At a real embedding $\varphi$, with $a=\varphi(\alpha)$: $16(a+1)^2-a^4=(a+2)(1+a)^2$. -/
theorem key_real (φ : K →+* ℝ) :
    4 * (4 * (φ α + 1) ^ 2) - (φ α ^ 2) ^ 2 = (φ α + 2) * (1 + φ α) ^ 2 := by
  have := congrArg φ key_identity
  simpa [map_sub, map_mul, map_pow, map_add, map_ofNat] using this

theorem phi_s_ne_zero (φ : K →+* ℝ) : φ α + 2 ≠ 0 := by
  intro h
  have h1 := congrArg φ s_mul_inv
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at h1
  rw [h] at h1
  simp at h1

theorem phi_t_ne_zero (φ : K →+* ℝ) : 1 + φ α ≠ 0 := by
  intro h
  have h1 := congrArg φ a1_mul_inv
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at h1
  rw [h] at h1
  simp at h1

section Real

variable (w : InfinitePlace K) (hw : w.IsReal)

local notation "φw" => InfinitePlace.embedding_of_isReal hw
local notation "ψw" => InfinitePlace.Completion.ringEquivRealOfIsReal hw

/-- **The form at a real place**, transported to $\mathbb R$. -/
theorem psi_eval (x : Fin 3 → w.Completion) :
    ψw (QF.evalIn w.Completion x) = ψw (x 0) ^ 2 + ψw (x 1) ^ 2 + φw (α ^ 2) * ψw (x 1) * ψw (x 2) +
      φw (4 * (α + 1) ^ 2) * ψw (x 2) ^ 2 := by
  rw [evalIn_QF]
  simp only [map_add, map_mul, map_pow]
  rw [QuadFormsKB.Lattices.ringEquivReal_algebraMap w hw, QuadFormsKB.Lattices.ringEquivReal_algebraMap w hw]
  simp only [map_one]

end Real

section Real2

variable (w : InfinitePlace K) (hw : w.IsReal)

local notation "φw" => InfinitePlace.embedding_of_isReal hw
local notation "ψw" => InfinitePlace.Completion.ringEquivRealOfIsReal hw

/-- **Anisotropy where $s>0$:** if $\varphi(\alpha)+2>0$ at a real place, the form has no nontrivial zero. -/
theorem not_isotropic_of_pos (hpos : 0 < φw α + 2) : ¬ QF.IsotropicIn w.Completion := by
  rintro ⟨x, hx0, hx⟩
  have h := psi_eval w hw x
  rw [hx, map_zero] at h
  simp only [map_pow, map_mul, map_add, map_ofNat, map_one] at h
  have hk := key_real (φw)
  have ht := phi_t_ne_zero (φw)
  set a := φw α
  set X := ψw (x 0)
  set Y := ψw (x 1)
  set Z := ψw (x 2)
  have htp : 0 < (a + 2) * (1 + a) ^ 2 := mul_pos hpos (by positivity)
  have hZ : Z = 0 := by
    by_contra hZ
    have hZ2 : 0 < Z ^ 2 := by positivity
    nlinarith [sq_nonneg X, sq_nonneg (2 * Y + a ^ 2 * Z), mul_pos htp hZ2]
  have hX : X = 0 := by
    rw [hZ] at h
    nlinarith [sq_nonneg X, sq_nonneg Y]
  have hY : Y = 0 := by
    rw [hZ] at h
    nlinarith [sq_nonneg X, sq_nonneg Y]
  apply hx0
  funext i
  have hinj : ∀ y : w.Completion, ψw y = 0 → y = 0 := fun y hy => (ψw).injective (by rw [hy, map_zero])
  fin_cases i
  · exact hinj _ hX
  · exact hinj _ hY
  · exact hinj _ hZ

end Real2

/-- **Hypothesis (ii) of the obstruction at every infinite place:** $d$ is a square in $k_w$ whenever $Q$ is isotropic
over $k_w$. -/
theorem isSquare_d_of_isotropic (w : InfinitePlace K) (hiso : QF.IsotropicIn w.Completion) :
    IsSquare (algebraMap K w.Completion d) := by
  by_cases hw : w.IsReal
  · rw [QuadFormsKB.Lattices.isSquare_algebraMap_real_iff w hw]
    by_contra hneg
    push Not at hneg
    apply not_isotropic_of_pos w hw _ hiso
    rw [d_eq, map_neg, map_add, map_ofNat] at hneg
    linarith
  · exact QuadFormsKB.Lattices.isSquare_completion_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.mp hw) _

/-- **$Q$ is indefinite:** isotropic at the real place given by an embedding with $\varphi(\alpha)<-2$
($\varphi(s)<0$). -/
theorem isIndefinite_QF : IsIndefinite QF := by
  obtain ⟨φ, hφ⟩ := exists_embedding_lt
  let φ' : K →+* ℂ := Complex.ofRealHom.comp φ
  have hreal : ComplexEmbedding.IsReal φ' := by
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    simp [φ', ComplexEmbedding.conjugate_coe_eq]
  have hw : (InfinitePlace.mk φ').IsReal := InfinitePlace.isReal_mk_iff.mpr hreal
  refine ⟨InfinitePlace.mk φ', ?_⟩
  have hemb : ∀ x, InfinitePlace.embedding_of_isReal hw x = φ x := by
    intro x
    apply Complex.ofReal_injective
    rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hreal]
    rfl
  set w := InfinitePlace.mk φ'
  have ht := phi_t_ne_zero φ
  have hk := key_real φ
  set a := φ α
  have hneg : a + 2 < 0 := by linarith
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let Z : ℝ := 2 / (1 + a)
  let Y : ℝ := -(a ^ 2) * Z / 2
  let X : ℝ := Real.sqrt (-(a + 2))
  refine ⟨![ψ.symm X, ψ.symm Y, ψ.symm Z], ?_, ?_⟩
  · intro h0
    have := congrFun h0 2
    simp at this
    have hZ : Z = 0 := by exact this
    have : (2 : ℝ) / (1 + a) = 0 := hZ
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · norm_num at h
    · exact ht h
  · apply ψ.injective
    rw [psi_eval w hw]
    have hX : X ^ 2 = -(a + 2) := Real.sq_sqrt (by linarith)
    have hZ : Z * (1 + a) = 2 := by simp only [Z]; field_simp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ψ, RingEquiv.apply_symm_apply,
      hemb, map_pow, map_mul, map_add, map_ofNat, map_one, map_zero]
    have hY : Y = -(a ^ 2) * Z / 2 := rfl
    rw [hY]
    linear_combination hX + (Z ^ 2 / 4) * hk + ((a + 2) / 4) * (Z * (1 + a) + 2) * hZ

end QuadFormsKB.Hanke2005.Cor52
