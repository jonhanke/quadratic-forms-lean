import QuadFormsKB.Literature.Hanke2005.Cor52Form
import QuadFormsKB.Literature.Hanke2005.MassFormula
import QuadFormsKB.Literature.OMeara.Sec82Max

/-!
# The standard lattice is maximal for the form of the counterexample to Hanke's Cor. 5.2(ii)

$\mathcal O_k^3$ with the form `Q₀` is $\mathcal O_k$-maximal: the Hessian determinant is $2\cdot$unit and
$2$ is inert in $k$ (the cubic $y^3+y^2+1$ is irreducible mod $2$), so $(2)$ is a maximal ideal and
O'Meara 82:19 (`OMeara.isMaximal_of_squarefree`) applies.
-/

open Polynomial NumberField

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

theorem finrank_K_max : Module.finrank ℚ K = 3 := by
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis poly_irreducible.ne_zero)]
  simp [AdjoinRoot.powerBasis_dim, poly_natDegree]

section FieldFacts
variable {k : Type*} [Field k] (a : k) (hp : a ^ 3 = a ^ 2 + 10 * a + 7)
include hp

theorem no_root_2_2_max [CharP k 2] (hq : a ^ 2 = a) : False := by grind
theorem no_root_2_4_max [CharP k 2] (hq : a ^ 4 = a) : False := by grind

end FieldFacts

theorem αI_cube_max : αI ^ 3 = αI ^ 2 + 10 * αI + 7 := by
  have h : algebraMap (𝓞 K) K αI = α := rfl
  apply IsFractionRing.injective (𝓞 K) K
  simp only [map_add, map_pow, map_mul, map_ofNat, h]
  exact α_cube

theorem eq_of_le_of_absNorm_eq' {I J : Ideal (𝓞 K)} (hle : I ≤ J)
    (h : Ideal.absNorm I = Ideal.absNorm J) (h0 : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := (Ideal.dvd_iff_le).2 hle
  have h1 : Ideal.absNorm J * Ideal.absNorm C = Ideal.absNorm J * 1 := by
    rw [← map_mul, ← hC, mul_one, h]
  have h2 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h1
  rw [Ideal.absNorm_eq_one_iff] at h2
  rw [hC, h2, Ideal.mul_top]

theorem absNorm_span_two : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 K)}) = 8 := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, finrank_K_max]
  norm_num

theorem span_two_ne_top : Ideal.span {((2 : ℕ) : 𝓞 K)} ≠ ⊤ := by
  intro h
  have := absNorm_span_two
  rw [h, Ideal.absNorm_top] at this
  omega

/-- $2$ is inert: $(2)$ is a maximal ideal of $\mathcal O_k$. -/
theorem isMaximal_span_two : (Ideal.span {((2 : ℕ) : 𝓞 K)}).IsMaximal := by
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ span_two_ne_top
  have hpP : ((2 : ℕ) : 𝓞 K) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have h8 := absNorm_span_two
  obtain ⟨C, hC⟩ := (Ideal.dvd_iff_le).2 hle
  have hdvd : Ideal.absNorm P ∣ 8 := by
    rw [← h8, hC, map_mul]; exact dvd_mul_right _ _
  have hne : Ideal.absNorm P ≠ 0 := by
    intro h; rw [h] at hdvd; omega
  have hf : Ideal.absNorm P ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 K ⧸ P) := (Ideal.absNorm_ne_zero_iff P).1 hne
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcardk : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hchar : (((2 : ℕ)) : 𝓞 K ⧸ P) = 0 := by
    have : Ideal.Quotient.mk P ((2 : ℕ) : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpP
    rwa [map_natCast] at this
  haveI : CharP (𝓞 K ⧸ P) 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 hchar
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P) 2
  set a : 𝓞 K ⧸ P := Ideal.Quotient.mk P αI with ha
  have hpoly : a ^ 3 = a ^ 2 + 10 * a + 7 := by
    have := congrArg (Ideal.Quotient.mk P) αI_cube_max
    simp only [map_add, map_pow, map_mul, map_ofNat] at this
    exact this
  have hq : a ^ (2 ^ (n : ℕ)) = a := by
    rw [← hn]; exact FiniteField.pow_card a
  have hn8 : 2 ^ (n : ℕ) ≤ 8 := by rw [← hn, hcardk]; exact hf
  have hn3 : (n : ℕ) ≤ 3 := by
    by_contra h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_le.1 h)
    omega
  have hn0 : 0 < (n : ℕ) := n.pos
  have hcardP : Ideal.absNorm P = 2 ^ (n : ℕ) := by rw [← hcardk, hn]
  have hn3' : (n : ℕ) = 3 := by
    interval_cases h : (n : ℕ)
    · exact (no_root_2_2_max a hpoly (by simpa using hq)).elim
    · exact (no_root_2_4_max a hpoly (by simpa using hq)).elim
    · rfl
  have habs : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 K)}) = Ideal.absNorm P := by
    rw [h8, hcardP, hn3']; norm_num
  rw [eq_of_le_of_absNorm_eq' hle habs hne]
  exact hP

theorem ideal_eq_top_of_two_mem_sq (I : Ideal (𝓞 K)) (h : (2 : 𝓞 K) ∈ I ^ 2) : I = ⊤ := by
  have hM := isMaximal_span_two
  have h2 : (2 : 𝓞 K) ≠ 0 := by norm_num
  have hle : Ideal.span {((2 : ℕ) : 𝓞 K)} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_le_self (two_ne_zero) (by simpa using h)
  by_contra hI
  have hIe := hM.eq_of_le hI hle
  rw [← hIe, Nat.cast_ofNat, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 : (2 : 𝓞 K) * c = 1 := by
    apply mul_left_cancel₀ h2
    linear_combination -hc
  have hu : IsUnit (2 : 𝓞 K) := IsUnit.of_mul_eq_one c h1
  apply hM.ne_top
  rw [Nat.cast_ofNat]
  exact (Ideal.span_singleton_eq_top).2 hu

/-- The squarefree condition: a submodule `b ≤ 1` of `K` with `2 ∈ b ^ 2` is `1`. -/
theorem sub_eq_one_of_two_mem_sq (b : Submodule (𝓞 K) K) (hb : b ≤ 1) (h : (2 : K) ∈ b ^ 2) :
    b = 1 := by
  let f : 𝓞 K →ₐ[𝓞 K] K := Algebra.ofId (𝓞 K) K
  have hrange : b ≤ LinearMap.range f.toLinearMap := by
    rw [Submodule.one_eq_range] at hb; exact hb
  set I : Ideal (𝓞 K) := b.comap f.toLinearMap with hI
  have hbI : b = Submodule.map f.toLinearMap I := (Submodule.map_comap_eq_of_le hrange).symm
  have hsq : b ^ 2 = Submodule.map f.toLinearMap (I ^ 2) := by
    rw [hbI, Submodule.map_pow]
  rw [hsq] at h
  obtain ⟨c, hc, hc2⟩ := Submodule.mem_map.1 h
  have hc2' : c = 2 := by
    have e : algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K 2 := by rw [map_ofNat]; exact hc2
    exact FaithfulSMul.algebraMap_injective (𝓞 K) K e
  rw [hc2'] at hc
  have := ideal_eq_top_of_two_mem_sq I hc
  rw [hbI, this, Submodule.map_top, Submodule.one_eq_range]
  rfl

open QuadFormsKB.Lattices in
theorem toQF_apply (x : Fin 3 → K) :
    (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 K) K))) x = Q₀.evalIn K x := by
  rw [QuadForm.toQuadraticForm_apply]
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map]

theorem toQF_integral (y : Fin 3 → 𝓞 K) :
    (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 K) K))) (fun i => algebraMap (𝓞 K) K (y i)) =
      algebraMap (𝓞 K) K (Q₀.evalIn (𝓞 K) y) := by
  rw [toQF_apply]
  simp [QuadForm.evalIn, map_sum, apply_ite]

/-- The coordinatewise inclusion `𝓞_K^3 → K^3`. -/
def fInt : (Fin 3 → 𝓞 K) →ₗ[𝓞 K] (Fin 3 → K) :=
  LinearMap.pi fun i => (Algebra.linearMap (𝓞 K) K) ∘ₗ LinearMap.proj i

theorem fInt_apply (y : Fin 3 → 𝓞 K) : fInt y = fun i => algebraMap (𝓞 K) K (y i) := rfl

theorem fInt_injective : Function.Injective fInt := by
  intro y z h
  funext i
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K (congrFun h i)

theorem range_fInt : LinearMap.range fInt = (QuadFormsKB.Lattices.intVec : Submodule (𝓞 K) (Fin 3 → K)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨y i, rfl⟩
  · intro hx
    choose y hy using (QuadFormsKB.Lattices.mem_intVec.1 hx)
    exact ⟨y, funext fun i => hy i⟩

/-- The standard basis of `intVec`. -/
def bInt : Module.Basis (Fin 3) (𝓞 K) (QuadFormsKB.Lattices.intVec : Submodule (𝓞 K) (Fin 3 → K)) :=
  (Pi.basisFun (𝓞 K) (Fin 3)).map
    ((LinearEquiv.ofInjective fInt fInt_injective).trans (LinearEquiv.ofEq _ _ range_fInt))

theorem bInt_apply (i : Fin 3) : ((bInt i : _) : Fin 3 → K) = Pi.single i 1 := by
  ext j
  simp [bInt, LinearEquiv.ofInjective_apply, fInt_apply, Pi.single_apply]

theorem gram_bInt [Invertible (2 : K)] :
    QuadFormsKB.OMeara.gram (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 K) K)))
        (fun i => ((bInt i : _) : Fin 3 → K)) =
      (⅟2 : K) • Q₀.hessian.map (algebraMap (𝓞 K) K) := by
  ext i j
  simp only [QuadFormsKB.OMeara.gram, QuadFormsKB.OMeara.bil, Matrix.of_apply, bInt_apply,
    QuadraticMap.associated_apply, toQF_apply]
  rw [QuadForm.polar_eq_hessian K Q₀]
  simp

theorem volume_two_pow [Invertible (2 : K)] :
    Submodule.span (𝓞 K) {(2 : K) ^ 3} *
        QuadFormsKB.OMeara.volume (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 K) K)))
          (QuadFormsKB.Lattices.intVec : Submodule (𝓞 K) (Fin 3 → K)) =
      Submodule.span (𝓞 K) {(2 : K)} := by
  have hdet : (Q₀.hessian.map (algebraMap (𝓞 K) K)).det = algebraMap (𝓞 K) K Q₀.hessian.det :=
    (RingHom.map_det (algebraMap (𝓞 K) K) Q₀.hessian).symm
  rw [QuadFormsKB.OMeara.volume_eq_span_det _ bInt, gram_bInt, Matrix.det_smul, Fintype.card_fin,
    hdet, hessian_det, Submodule.span_mul_span, Set.singleton_mul_singleton]
  obtain ⟨u, hu⟩ := isUnit_sI.mul (isUnit_tI.pow 2)
  rw [← hu]
  simp only [map_mul, map_ofNat]
  rw [Submodule.span_singleton_eq_span_singleton]
  refine ⟨u⁻¹, ?_⟩
  have h2 : (⅟2 : K) * 2 = 1 := invOf_mul_self 2
  have h3 : ((⅟2 : K) * 2) ^ 3 = 1 := by rw [h2]; simp
  have hu1 : algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * algebraMap (𝓞 K) K (u : 𝓞 K) = 1 := by
    rw [← map_mul]; simp
  rw [Units.smul_def, Algebra.smul_def]
  linear_combination (2 * ((⅟2 : K) * 2) ^ 3) * hu1 + 2 * h3

theorem one_fg : (1 : Submodule (𝓞 K) K).FG := by
  rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

theorem one_ne_bot' : (1 : Submodule (𝓞 K) K) ≠ ⊥ := by
  intro h
  have h1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.one_le.mp le_rfl
  rw [h] at h1
  simp at h1

theorem stdIsMaximal_Q₀ : QuadFormsKB.Hanke2005.StdIsMaximal Q₀ := by
  unfold QuadFormsKB.Hanke2005.StdIsMaximal
  refine QuadFormsKB.OMeara.isMaximal_of_squarefree _ ?_ ?_ ?_ ?_ ?_
  · exact one_fg
  · exact one_ne_bot'
  · exact QuadFormsKB.Lattices.intVec_isLattice
  · unfold QuadFormsKB.OMeara.normIdeal
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    choose y hy using (QuadFormsKB.Lattices.mem_intVec.1 hx)
    have hxy : x = fun i => algebraMap (𝓞 K) K (y i) := funext fun i => (hy i).symm
    rw [hxy]
    show _ ∈ (1 : Submodule (𝓞 K) K)
    rw [toQF_integral]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · intro b hb1 _ hle
    apply sub_eq_one_of_two_mem_sq b hb1
    have hfr : Module.finrank K (Fin 3 → K) = 3 := by simp
    rw [hfr] at hle
    have h1 : (1 / 1 : Submodule (𝓞 K) K) = 1 := by
      simpa using QuadFormsKB.OMeara.mul_one_div_cancel_of_fg one_fg one_ne_bot'
    rw [h1, one_pow, mul_one] at hle
    have hm := Submodule.mem_span_singleton_self (R := 𝓞 K) (2 : K)
    rw [← volume_two_pow] at hm
    exact hle hm

end QuadFormsKB.Hanke2005.Cor52
