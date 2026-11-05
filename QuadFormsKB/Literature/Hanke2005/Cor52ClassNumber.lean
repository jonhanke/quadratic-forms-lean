import QuadFormsKB.Literature.Hanke2005.Cor52Field
import QuadFormsKB.Literature.Hanke2005.Cor52Form

open Polynomial NumberField Matrix

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

theorem poly_eq : (poly : ℚ[X]) = X ^ 3 - X ^ 2 - 10 * X - 7 := by
  simp [poly]; rw [show (C 10 : ℚ[X]) = 10 from rfl, show (C 7 : ℚ[X]) = 7 from rfl]

/-- The power basis `1, α, α²`. -/
def pb : PowerBasis ℚ K := AdjoinRoot.powerBasis poly_irreducible.ne_zero

theorem pb_gen : pb.gen = α := rfl

theorem pb_dim : pb.dim = 3 := by
  show (AdjoinRoot.powerBasis poly_irreducible.ne_zero).dim = 3
  simp [AdjoinRoot.powerBasis_dim, poly_natDegree]

theorem minpoly_α : minpoly ℚ pb.gen = poly :=
  AdjoinRoot.minpoly_powerBasis_gen_of_monic poly_monic

/-- Basis indexed by `Fin 3`, `b i = α^i`. -/
def b3 : Module.Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr pb_dim)

theorem b3_apply (i : Fin 3) : b3 i = α ^ (i : ℕ) := by
  simp [b3, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, pb_gen]

theorem repr_b3 (i j : Fin 3) : b3.repr (b3 j) i = if i = j then 1 else 0 := by
  simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]

theorem α_cube' : α ^ 3 = (7 : ℚ) • b3 0 + (10 : ℚ) • b3 1 + (1 : ℚ) • b3 2 := by
  simp only [b3_apply]
  simp [Algebra.smul_def, α_cube]
  ring

theorem leftMul_α : Algebra.leftMulMatrix b3 α = !![0, 0, 7; 1, 0, 10; 0, 1, 1] := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · have : α * b3 ⟨0, by omega⟩ = b3 1 := by simp [b3_apply]
    rw [this]; fin_cases i <;> simp [repr_b3]
  · have : α * b3 ⟨1, by omega⟩ = b3 2 := by simp [b3_apply]; ring
    rw [this]; fin_cases i <;> simp [repr_b3]
  · have : α * b3 ⟨2, by omega⟩ = (7 : ℚ) • b3 0 + (10 : ℚ) • b3 1 + (1 : ℚ) • b3 2 := by
      rw [← α_cube']; simp [b3_apply]; ring
    rw [this]; fin_cases i <;> simp [repr_b3]

theorem norm_deriv : Algebra.norm ℚ (3 * α ^ 2 - 2 * α - 10 : K) = -1489 := by
  rw [Algebra.norm_eq_matrix_det b3]
  have : (3 * α ^ 2 - 2 * α - 10 : K) = (3 : ℚ) • α ^ 2 - (2 : ℚ) • α - (10 : ℚ) • 1 := by
    simp [Algebra.smul_def]
  rw [this]
  simp only [map_sub, map_smul, map_pow, map_one, leftMul_α]
  rw [Matrix.det_fin_three]
  simp only [sq, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply]
  simp
  norm_num

theorem finrank_K : Module.finrank ℚ K = 3 := by
  rw [PowerBasis.finrank pb]; exact pb_dim

theorem discr_b3 : Algebra.discr ℚ b3 = 1489 := by
  have h1 : Algebra.discr ℚ b3 = Algebra.discr ℚ pb.basis := by
    unfold b3
    rw [Module.Basis.coe_reindex]
    exact Algebra.discr_reindex ℚ pb.basis (finCongr pb_dim)
  rw [h1, Algebra.discr_powerBasis_eq_norm, minpoly_α, finrank_K]
  have hd : (poly : ℚ[X]).derivative = 3 * X ^ 2 - 2 * X - 10 := by
    rw [poly_eq]
    simp [derivative_sub, derivative_pow, derivative_X_pow]
    rw [show (C 3 : ℚ[X]) = 3 from rfl, show (C 2 : ℚ[X]) = 2 from rfl]
  rw [hd]
  have : (aeval pb.gen (3 * X ^ 2 - 2 * X - 10 : ℚ[X])) = (3 * α ^ 2 - 2 * α - 10 : K) := by
    simp [pb_gen, map_ofNat]
  rw [this, norm_deriv]
  norm_num

theorem α_isIntegral : IsIntegral ℤ α := by
  refine ⟨polyZ, polyZ_monic, ?_⟩
  simp only [polyZ, Polynomial.eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
  simp
  linear_combination α_cube

/-- `α ^ i` as an algebraic integer. -/
def v (i : Fin 3) : 𝓞 K := ⟨α ^ (i : ℕ), α_isIntegral.pow _⟩

theorem abs_discr_le : |NumberField.discr K| ≤ 1489 := by
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 3 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
    exact finrank_K
  let e := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin 3) ℤ (𝓞 K) := (RingOfIntegers.basis K).reindex e
  let B : Module.Basis (Fin 3) ℚ K :=
    Module.Basis.localizationLocalization ℚ (nonZeroDivisors ℤ) K b'
  have hB : Algebra.discr ℚ B = (NumberField.discr K : ℚ) := by
    have := Algebra.discr_localizationLocalization (Rₘ := ℚ) ℤ (nonZeroDivisors ℤ) K b'
    rw [this, NumberField.discr_eq_discr K b']; rfl
  have hv : ∀ j, (B ᵥ* ((b'.toMatrix v).map (Int.castRingHom ℚ)).map (algebraMap ℚ K)) j = b3 j := by
    intro j
    have h := congrArg (algebraMap (𝓞 K) K) (congrFun (Module.Basis.toMatrix_map_vecMul b' v) j)
    simp only [Matrix.vecMul, dotProduct, map_sum, map_mul] at h
    rw [b3_apply]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, B,
      Module.Basis.localizationLocalization_apply]
    convert h using 2
    · rename_i i _
      simp [mul_comm]
    · rfl
  have h2 : Algebra.discr ℚ b3 = ((b'.toMatrix v).det : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
    have := Algebra.discr_of_matrix_vecMul B ((b'.toMatrix v).map (Int.castRingHom ℚ))
    have hdet : (((b'.toMatrix v).map (Int.castRingHom ℚ)).det) = ((b'.toMatrix v).det : ℚ) :=
      (RingHom.map_det (Int.castRingHom ℚ) _).symm
    rw [hdet] at this
    rw [← hB, ← this]
    congr 1
    funext j; exact (hv j).symm
  have h4 : (b'.toMatrix v).det ^ 2 * NumberField.discr K = 1489 := by
    rw [discr_b3] at h2
    exact_mod_cast h2.symm
  have hd0 := NumberField.discr_ne_zero K
  have hm : (b'.toMatrix v).det ≠ 0 := by
    intro h; rw [h] at h4; simp at h4
  have hm2 : 1 ≤ (b'.toMatrix v).det ^ 2 := by
    have := pow_pos (abs_pos.mpr hm) 2
    rw [sq_abs] at this; omega
  have : |(b'.toMatrix v).det ^ 2 * NumberField.discr K| = 1489 := by rw [h4]; rfl
  rw [abs_mul, abs_of_nonneg (by positivity)] at this
  have := abs_nonneg (NumberField.discr K)
  nlinarith

/-- A real root gives a real embedding `K →+* ℝ` sending `α` to it. -/
def embOfRoot (r : ℝ) (h : r ^ 3 - r ^ 2 - 10 * r - 7 = 0) : K →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) r (by
    rw [poly_eq]; simpa using h)

theorem embOfRoot_α (r : ℝ) (h : r ^ 3 - r ^ 2 - 10 * r - 7 = 0) : embOfRoot r h α = r := by
  unfold embOfRoot α
  exact AdjoinRoot.lift_root _

theorem exists_root (a b : ℝ) (hab : a ≤ b)
    (ha : (a ^ 3 - a ^ 2 - 10 * a - 7) * (b ^ 3 - b ^ 2 - 10 * b - 7) ≤ 0) :
    ∃ r ∈ Set.Icc a b, r ^ 3 - r ^ 2 - 10 * r - 7 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - 10 * x - 7) (Set.Icc a b) := by fun_prop
  by_cases h : a ^ 3 - a ^ 2 - 10 * a - 7 ≤ 0
  · by_cases h2 : 0 ≤ b ^ 3 - b ^ 2 - 10 * b - 7
    · obtain ⟨r, hr, e⟩ := intermediate_value_Icc hab hc ⟨h, h2⟩
      exact ⟨r, hr, e⟩
    · have : a ^ 3 - a ^ 2 - 10 * a - 7 = 0 := by nlinarith
      exact ⟨a, ⟨le_rfl, hab⟩, this⟩
  · have h1 : 0 < a ^ 3 - a ^ 2 - 10 * a - 7 := by linarith
    have h2 : b ^ 3 - b ^ 2 - 10 * b - 7 ≤ 0 := by nlinarith
    obtain ⟨r, hr, e⟩ := intermediate_value_Icc' hab hc ⟨h2, h1.le⟩
    exact ⟨r, hr, e⟩

theorem nrComplexPlaces_eq_zero : NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
  obtain ⟨r1, h1, e1⟩ := exists_root (-3) (-2) (by norm_num) (by norm_num)
  obtain ⟨r2, h2, e2⟩ := exists_root (-1) 0 (by norm_num) (by norm_num)
  obtain ⟨r3, h3, e3⟩ := exists_root 3 4 (by norm_num) (by norm_num)
  classical
  let ψ : Fin 3 → (K →+* ℝ) := ![embOfRoot r1 e1, embOfRoot r2 e2, embOfRoot r3 e3]
  have hψ : ∀ i, ∃ r : ℝ, ψ i α = r ∧ (i = 0 → r ∈ Set.Icc (-3 : ℝ) (-2)) ∧
      (i = 1 → r ∈ Set.Icc (-1 : ℝ) 0) ∧ (i = 2 → r ∈ Set.Icc (3 : ℝ) 4) := by
    intro i
    fin_cases i
    · exact ⟨r1, embOfRoot_α r1 e1, fun _ => h1, by simp, by simp⟩
    · exact ⟨r2, embOfRoot_α r2 e2, by simp, fun _ => h2, by simp⟩
    · exact ⟨r3, embOfRoot_α r3 e3, by simp, by simp, fun _ => h3⟩
  have hreal : ∀ i, ComplexEmbedding.IsReal ((algebraMap ℝ ℂ).comp (ψ i)) := by
    intro i
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    show (starRingEnd ℂ) (algebraMap ℝ ℂ (ψ i x)) = algebraMap ℝ ℂ (ψ i x)
    exact Complex.conj_ofReal _
  let F : Fin 3 → {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} :=
    fun i => ⟨(algebraMap ℝ ℂ).comp (ψ i), hreal i⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have hα : ψ i α = ψ j α := by
      have := congrArg (fun φ : {φ : K →+* ℂ // ComplexEmbedding.IsReal φ} => φ.1 α) hij
      have h' : algebraMap ℝ ℂ (ψ i α) = algebraMap ℝ ℂ (ψ j α) := this
      exact Complex.ofReal_injective h'
    obtain ⟨ri, hi, hi0, hi1, hi2⟩ := hψ i
    obtain ⟨rj, hj, hj0, hj1, hj2⟩ := hψ j
    rw [hi, hj] at hα
    subst hα
    fin_cases i <;> fin_cases j <;> simp at hi0 hi1 hi2 hj0 hj1 hj2 ⊢ <;>
      first
      | rfl
      | (exfalso; simp only [Set.mem_Icc] at *; linarith)
  have hcard := Fintype.card_le_of_injective F hinj
  rw [NumberField.InfinitePlace.card_real_embeddings] at hcard
  have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [finrank_K] at this
  simp at hcard
  omega

section FieldFacts
variable {k : Type*} [Field k] (a : k) (hp : a ^ 3 = a ^ 2 + 10 * a + 7)
include hp

theorem no_root_2_2 [CharP k 2] (hq : a ^ 2 = a) : False := by grind
theorem no_root_2_4 [CharP k 2] (hq : a ^ 4 = a) : False := by grind
theorem no_root_3 [CharP k 3] (hq : a ^ 3 = a) : False := by grind
theorem no_root_5 [CharP k 5] (hq : a ^ 5 = a) : False := by grind
theorem root_7 [CharP k 7] (hq : a ^ 7 = a) : a = 0 := by grind

end FieldFacts

theorem αI_cube : αI ^ 3 = αI ^ 2 + 10 * αI + 7 := by
  have h : algebraMap (𝓞 K) K αI = α := rfl
  apply IsFractionRing.injective (𝓞 K) K
  simp only [map_add, map_pow, map_mul, map_ofNat, h]
  exact α_cube

theorem norm_αI : Algebra.norm ℤ αI = 7 := by
  have h : ((Algebra.norm ℤ αI : ℤ) : ℚ) = 7 := by
    rw [Algebra.coe_norm_int]
    show Algebra.norm ℚ α = 7
    rw [Algebra.norm_eq_matrix_det b3, leftMul_α, Matrix.det_fin_three]
    simp
  exact_mod_cast h

theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (hle : I ≤ J)
    (h : Ideal.absNorm I = Ideal.absNorm J) (h0 : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨C, hC⟩ := (Ideal.dvd_iff_le).2 hle
  have h1 : Ideal.absNorm J * Ideal.absNorm C = Ideal.absNorm J * 1 := by
    rw [← map_mul, ← hC, mul_one, h]
  have h2 : Ideal.absNorm C = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h1
  rw [Ideal.absNorm_eq_one_iff] at h2
  rw [hC, h2, Ideal.mul_top]

theorem key (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (p f : ℕ) (hp : p.Prime) (hf : 0 < f)
    (hle : p ^ f ≤ 8) (hcard : Ideal.absNorm P = p ^ f) (hpP : (p : 𝓞 K) ∈ P) :
    Submodule.IsPrincipal P := by
  have hne : Ideal.absNorm P ≠ 0 := by rw [hcard]; exact pow_ne_zero _ hp.ne_zero
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have : Finite (𝓞 K ⧸ P) := (Ideal.absNorm_ne_zero_iff P).1 hne
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcardk : Fintype.card (𝓞 K ⧸ P) = p ^ f := by
    rw [← hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hchar : ((p : ℕ) : 𝓞 K ⧸ P) = 0 := by
    have : Ideal.Quotient.mk P (p : 𝓞 K) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpP
    simpa using this
  haveI : CharP (𝓞 K ⧸ P) p := (CharP.charP_iff_prime_eq_zero hp).2 hchar
  set a : 𝓞 K ⧸ P := Ideal.Quotient.mk P αI with ha
  have hpoly : a ^ 3 = a ^ 2 + 10 * a + 7 := by
    have := congrArg (Ideal.Quotient.mk P) αI_cube
    simp only [map_add, map_pow, map_mul, map_ofNat] at this
    exact this
  have hq : a ^ (p ^ f) = a := by
    rw [← hcardk]; exact FiniteField.pow_card a
  have hf4 : f < 4 := by
    by_contra h
    push_neg at h
    have h1 := Nat.pow_le_pow_left hp.two_le f
    have h2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  have hp8 : p ≤ 8 := le_trans (Nat.le_self_pow hf.ne' p) hle
  interval_cases p <;> interval_cases f <;>
    first
    | (exfalso; revert hle; norm_num; done)
    | (exfalso; revert hp; norm_num; done)
    | skip
  · exact (no_root_2_2 a hpoly (by simpa using hq)).elim
  · exact (no_root_2_4 a hpoly (by simpa using hq)).elim
  · have hle' : Ideal.span {((2 : ℕ) : 𝓞 K)} ≤ P := by
      rw [Ideal.span_singleton_le_iff_mem]; exact hpP
    have habs : Ideal.absNorm (Ideal.span {((2 : ℕ) : 𝓞 K)}) = Ideal.absNorm P := by
      rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, finrank_K, hcard]
    exact ⟨⟨((2 : ℕ) : 𝓞 K), (eq_of_le_of_absNorm_eq hle' habs hne).symm⟩⟩
  · exact (no_root_3 a hpoly (by simpa using hq)).elim
  · exact (no_root_5 a hpoly (by simpa using hq)).elim
  · have h0 : a = 0 := root_7 a hpoly (by simpa using hq)
    have hmem : αI ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 h0
    have hle' : Ideal.span {αI} ≤ P := by
      rw [Ideal.span_singleton_le_iff_mem]; exact hmem
    have habs : Ideal.absNorm (Ideal.span {αI}) = Ideal.absNorm P := by
      rw [Ideal.absNorm_span_singleton, norm_αI, hcard]; rfl
    exact ⟨⟨αI, (eq_of_le_of_absNorm_eq hle' habs hne).symm⟩⟩

open scoped Nat Real in
theorem floor_M_le :
    ⌊(4 / π) ^ InfinitePlace.nrComplexPlaces K *
      ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        √|NumberField.discr K|)⌋₊ ≤ 8 := by
  have key : (4 / π) ^ InfinitePlace.nrComplexPlaces K *
      ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        √|NumberField.discr K|) < 9 := by
    rw [nrComplexPlaces_eq_zero, finrank_K]
    have hd : |(NumberField.discr K : ℝ)| ≤ 1489 := by exact_mod_cast abs_discr_le
    have hs : √|(NumberField.discr K : ℝ)| < 40.5 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num; linarith
    rw [pow_zero, one_mul]
    norm_num [Nat.factorial]
    linarith
  exact Nat.lt_succ_iff.1 ((Nat.floor_lt (by positivity)).2 (by exact_mod_cast key))

/-- **Main result.** The ring of integers of `K = ℚ(α)` is a principal ideal domain. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc ?_
  intro p _ hp P hPover hle
  obtain ⟨hPprime, hlies⟩ := hPover
  have hM := floor_M_le
  have hpP : (p : 𝓞 K) ∈ P := by
    have h1 : ((p : ℕ) : ℤ) ∈ Ideal.span {((p : ℕ) : ℤ)} := Ideal.mem_span_singleton_self _
    rw [Ideal.LiesOver.over (p := Ideal.span {((p : ℕ) : ℤ)}) (P := P)] at h1
    simpa using Ideal.mem_comap.mp h1
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPbot : P ≠ ⊥ := fun h => hp0 (by simpa [h] using hpP)
  haveI : P.IsMaximal := hPprime.isMaximal hPbot
  have hcard : Ideal.absNorm P = p ^ P.inertiaDeg ℤ := (Ideal.pow_inertiaDeg p P).symm
  have hf : 0 < P.inertiaDeg ℤ := by
    rcases Nat.eq_zero_or_pos (P.inertiaDeg ℤ) with h | h
    · rw [h, pow_zero, Ideal.absNorm_eq_one_iff] at hcard
      exact absurd hcard hPprime.ne_top
    · exact h
  exact key P p _ hp hf (hle.trans hM) hcard hpP

theorem classNumber_eq_one : NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff.2 isPrincipalIdealRing

end QuadFormsKB.Hanke2005.Cor52

