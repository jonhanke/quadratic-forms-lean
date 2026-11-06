/-
# O'Meara §71B: the Frobenius automorphisms of a cyclotomic extension, Formulas 71:10 and 71:11

**Setting** (O'Meara §71B, p. 193): $F$ is a number field, $m > 1$, and $K = F(\zeta)$ is an absolute $m$-cyclotomic
extension, given by a number field `K` over `F` and a primitive $m$-th root of unity `ζ` with $F(\zeta) = K$. The set
$S$ consists of the discrete spots $\mathfrak p$ of $F$ at which $m$ is a unit ($m \notin \mathfrak p$), and
$N\mathfrak p = \lvert\mathcal O_F/\mathfrak p\rvert$ is `Ideal.absNorm 𝔭.asIdeal`. The Galois group
$\mathfrak G(K/F)$ is `K ≃ₐ[F] K`, commutative by Mathlib's `IsCyclotomicExtension.isMulCommutative`.

**Defines**
* `frobCyc hζ 𝔭` (71.r4, p. 193): the Frobenius automorphism $\sigma_\mathfrak p$ of $K/F$ at $\mathfrak p \in S$, the
  unique $\sigma \in \mathfrak G(K/F)$ with $\sigma\zeta = \zeta^{N\mathfrak p}$ (`existsUnique_frobCyc`; its
  existence is Mathlib's arithmetic Frobenius `arithFrobAt` at a prime of $K$ over $\mathfrak p$);
* `frobProd hζ α` (p. 193): $\sigma_\alpha = \prod_{\mathfrak p \in S} \sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p
  \alpha}$ for $\alpha \in \dot F$ integral at every spot of $S$.

**Proves**
* Formula 71:10 (p. 193): `frobProd_sqrt` in `Sec71FrobSqrt.lean`;
* Formula 71:11 (p. 194): `exists_frobProd_zeta`.
-/
import QuadFormsKB.Literature.OMeara.Sec71A
import QuadFormsKB.Tamagawa.SquareClassParam

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {m : ℕ}
  {ζ : K}

/-- **The Frobenius automorphism exists and is unique** (O'Meara 1963, §71B, p. 193): for $K = F(\zeta)$ with $\zeta$
a primitive $m$-th root of unity and a discrete spot $\mathfrak p$ at which $m$ is a unit, there is exactly one
$\sigma \in \mathfrak G(K/F)$ with $\sigma\zeta = \zeta^{N\mathfrak p}$. -/
@[kb "omeara1963" "§71B, p. 193 (the Frobenius automorphism σ_𝔭 of K/F, σ_𝔭 ζ = ζ^{N𝔭})"]
theorem existsUnique_frobCyc (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤)
    (𝔭 : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ 𝔭.asIdeal) :
    ∃! σ : K ≃ₐ[F] K, σ ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have : NeZero m := ⟨hm0⟩
  have : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨hm0⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  have : IsGalois F K := IsCyclotomicExtension.isGalois {m} F K
  have huniq : ∀ σ τ : K ≃ₐ[F] K, σ ζ = τ ζ → σ = τ := by
    intro σ τ h
    have hint : IsIntegral F ζ := Algebra.IsIntegral.isIntegral ζ
    have hS : Algebra.adjoin F {ζ} = ⊤ := by
      have := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
      rw [← this, hK]; rfl
    have hle : Algebra.adjoin F {ζ} ≤ AlgHom.equalizer σ.toAlgHom τ.toAlgHom :=
      Algebra.adjoin_le (by simpa using h)
    rw [hS] at hle
    exact AlgEquiv.ext fun x => hle (Algebra.mem_top (x := x))
  have hex : ∃ σ : K ≃ₐ[F] K, σ ζ = ζ ^ Ideal.absNorm 𝔭.asIdeal := by
    obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) 𝔭.asIdeal
      (⊥ : Ideal (𝓞 K))
      (by
        rw [Ideal.under, Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
        exact bot_le)
    have hQne : Q ≠ ⊥ := by
      rintro rfl
      apply 𝔭.ne_bot
      rw [← hQP]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))
    have : Finite (𝓞 K ⧸ Q) := (Ideal.finiteQuotientOfFreeOfNeBot Q hQne)
    have : Algebra.IsInvariant (𝓞 F) (𝓞 K) ((𝓞 K) ≃ₐ[𝓞 F] (𝓞 K)) :=
      Algebra.isInvariant_of_isGalois' (𝓞 F) F K (𝓞 K)
    have : Finite ((𝓞 K) ≃ₐ[𝓞 F] (𝓞 K)) :=
      Finite.of_equiv _ (galRestrict (𝓞 F) F K (𝓞 K)).toEquiv
    obtain ⟨σ', hσ'⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 F) ((𝓞 K) ≃ₐ[𝓞 F] (𝓞 K)) Q
    let ζB : 𝓞 K := ⟨ζ, hζ.isIntegral (Nat.pos_of_ne_zero hm0)⟩
    have hζB : ζB ^ m = 1 := Subtype.ext hζ.pow_eq_one
    have hmQ : ((m : ℕ) : 𝓞 K) ∉ Q := by
      intro h
      apply hm
      rw [← hQP]
      simpa [Ideal.mem_comap] using h
    have h1 := hσ'.apply_of_pow_eq_one hζB hmQ
    have h2 : Nat.card ((𝓞 F) ⧸ Q.under (𝓞 F)) = Ideal.absNorm 𝔭.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      have : Q.under (𝓞 F) = 𝔭.asIdeal := hQP
      rw [this]
    rw [h2] at h1
    refine ⟨(galRestrict (𝓞 F) F K (𝓞 K)).symm σ', ?_⟩
    have e : (galRestrict (𝓞 F) F K (𝓞 K)).symm σ' (algebraMap (𝓞 K) K ζB) =
        algebraMap (𝓞 K) K (σ' ζB) :=
      galRestrict_symm_algebraMap_apply (A := 𝓞 F) (K := F) (L := K) (B := 𝓞 K) σ' ζB
    change (galRestrict (𝓞 F) F K (𝓞 K)).symm σ' (algebraMap (𝓞 K) K ζB) = _
    change σ' ζB = _ at h1
    rw [e, h1, map_pow]
    rfl
  obtain ⟨σ, hσ⟩ := hex
  exact ⟨σ, hσ, fun τ hτ => huniq _ _ (hτ.trans hσ.symm)⟩

open scoped Classical in
/-- **The Frobenius automorphism $\sigma_\mathfrak p$ of $K/F$** (O'Meara 1963, §71B, p. 193) at a discrete spot
$\mathfrak p$ at which $m$ is a unit: the unique $\sigma$ with $\sigma\zeta = \zeta^{N\mathfrak p}$
(`existsUnique_frobCyc`); it is the identity, by convention, at the other spots. -/
@[kb "omeara1963" "§71B, p. 193 (the Frobenius automorphism σ_𝔭)"]
def frobCyc (hζ : IsPrimitiveRoot ζ m) (hK : IntermediateField.adjoin F {ζ} = ⊤) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    K ≃ₐ[F] K :=
  if hm : (m : 𝓞 F) ∉ 𝔭.asIdeal then (existsUnique_frobCyc hζ hK 𝔭 hm).exists.choose else 1

/-- $\operatorname{ord}_\mathfrak p \alpha$ for $\alpha \in \dot F$ (the negative of the library's
`SqDual.ordL`, the logarithm of the valuation). -/
def ordAt (𝔭 : HeightOneSpectrum (𝓞 F)) (α : Fˣ) : ℤ := -SqDual.ordL 𝔭 α

/-- **The automorphism $\sigma_\alpha$** (O'Meara 1963, §71B, p. 193): for $\alpha \in \dot F$ integral at every spot
of $S$, $\sigma_\alpha = \prod_{\mathfrak p \in S} \sigma_\mathfrak p^{\operatorname{ord}_\mathfrak p \alpha}$ (a finite
product in the commutative group $\mathfrak G(K/F)$; only finitely many $\operatorname{ord}_\mathfrak p \alpha$ are
nonzero). -/
@[kb "omeara1963" "§71B, p. 193 (σ_α = ∏_{𝔭 ∈ S} σ_𝔭^{ord_𝔭 α})"]
def frobProd (hζ : IsPrimitiveRoot ζ m) (hm1 : 1 < m) (hK : IntermediateField.adjoin F {ζ} = ⊤) (α : Fˣ) :
    K ≃ₐ[F] K :=
  letI : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨by omega⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  letI : CommGroup (K ≃ₐ[F] K) :=
    { (inferInstance : Group (K ≃ₐ[F] K)) with
      mul_comm := fun a b => (IsCyclotomicExtension.isMulCommutative {m} F K).is_comm.comm a b }
  ∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal), frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α

/-! ### Helpers for Formula 71:11 -/

open scoped Classical in
/-- The norm from $F$ to $\mathbb Q$ as a product over the infinite places (helper for 71:11). -/
lemma frobAux_norm_cast_eq_prod (a : F) :
    ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ w : InfinitePlace F,
      (if hw : w.IsReal then ((InfinitePlace.embedding_of_isReal hw a : ℝ) : ℂ)
        else (((w a) ^ 2 : ℝ) : ℂ)) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  rw [eq_ratCast] at h1
  rw [h1]
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ : F →+* ℂ => φ a)
    (fun ψ : F →ₐ[ℚ] ℂ => ψ a) (fun _ => by simp [RingHom.equivRatAlgHom_apply])]
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : F →+* ℂ => φ a)]
  refine Finset.prod_congr rfl fun w _ => ?_
  by_cases hw : w.IsReal
  · rw [dif_pos hw]
    have : (Finset.univ.filter fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
        {InfinitePlace.embedding w} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := φ) (ψ := InfinitePlace.embedding w)
      rw [InfinitePlace.mk_embedding] at h
      have hr := ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      have h3 : ComplexEmbedding.conjugate φ = InfinitePlace.embedding w ↔
          φ = ComplexEmbedding.conjugate (InfinitePlace.embedding w) :=
        (star_involutive.eq_iff : star φ = _ ↔ φ = star _)
      rw [h, h3, hr, or_self]
    rw [this, Finset.prod_singleton, InfinitePlace.embedding_of_isReal_apply]
  · rw [dif_neg hw]
    have hne : InfinitePlace.embedding w ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding w) := by
      intro h
      exact hw (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    have : (Finset.univ.filter fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
        {InfinitePlace.embedding w, ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have h := InfinitePlace.mk_eq_iff (φ := φ) (ψ := InfinitePlace.embedding w)
      rw [InfinitePlace.mk_embedding] at h
      rw [h, ComplexEmbedding.conjugate, star_involutive.eq_iff]
    rw [this, Finset.prod_pair hne]
    simp only [ComplexEmbedding.conjugate_coe_eq]
    rw [Complex.mul_conj, ← InfinitePlace.norm_embedding_eq w a, Complex.normSq_eq_norm_sq]

open scoped Classical in
lemma frobAux_sign_norm (a : F) (ha : a ≠ 0) :
    0 < ((-1 : ℝ) ^ (Finset.univ.filter fun w : InfinitePlace F =>
      ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw a < 0).card) *
      ((Algebra.norm ℚ a : ℚ) : ℝ) := by
  have h := frobAux_norm_cast_eq_prod a
  have h2 : ((Algebra.norm ℚ a : ℚ) : ℝ) = ∏ w : InfinitePlace F,
      (if hw : w.IsReal then (InfinitePlace.embedding_of_isReal hw a : ℝ) else (w a) ^ 2) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast, h, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    by_cases hw : w.IsReal <;> simp [hw]
  have h3 : ((-1 : ℝ) ^ (Finset.univ.filter fun w : InfinitePlace F =>
      ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw a < 0).card) =
      ∏ w : InfinitePlace F, (if ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw a < 0
        then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [h2, h3, ← Finset.prod_mul_distrib]
  refine Finset.prod_pos fun w _ => ?_
  by_cases hw : w.IsReal
  · have hne : InfinitePlace.embedding_of_isReal hw a ≠ 0 := by
      simpa using ha
    rw [dif_pos hw]
    rcases lt_or_gt_of_ne hne with hl | hl
    · have : ∃ hw' : w.IsReal, InfinitePlace.embedding_of_isReal hw' a < 0 := ⟨hw, hl⟩
      rw [if_pos this]; linarith
    · have : ¬ ∃ hw' : w.IsReal, InfinitePlace.embedding_of_isReal hw' a < 0 :=
        fun ⟨hw', h'⟩ => absurd h' (not_lt.mpr hl.le)
      rw [if_neg this]; linarith
  · have : ¬ ∃ hw' : w.IsReal, InfinitePlace.embedding_of_isReal hw' a < 0 := fun ⟨hw', _⟩ => hw hw'
    rw [dif_neg hw, if_neg this, one_mul]
    exact pow_pos (InfinitePlace.pos_iff.mpr ha) 2

lemma frobAux_norm_one_add (m : ℕ) (b : 𝓞 F) :
    ((Algebra.norm ℤ (1 + (m : 𝓞 F) * b) : ℤ) : ZMod m) = 1 := by
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis ℤ (𝓞 F)),
    ← eq_intCast (Int.castRingHom (ZMod m)), RingHom.map_det]
  have : (Int.castRingHom (ZMod m)).mapMatrix
      (Algebra.leftMulMatrix (Module.Free.chooseBasis ℤ (𝓞 F)) (1 + (m : 𝓞 F) * b)) = 1 := by
    rw [map_add, map_one, map_mul, map_natCast]
    generalize Algebra.leftMulMatrix (Module.Free.chooseBasis ℤ (𝓞 F)) b = B
    rw [map_add, map_one, map_mul, map_natCast]
    have h0 : ((m : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 F))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 F)) (ZMod m))) = 0 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.natCast_apply]
      · simp [Matrix.natCast_apply, hij]
    rw [h0, zero_mul, add_zero]
  rw [this, Matrix.det_one]

lemma frobAux_natAbs_norm_eq (a : 𝓞 F) (ha : a ≠ 0) :
    (Algebra.norm ℤ a).natAbs = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Ideal.absNorm v.asIdeal ^
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors := by
  have hne : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by simpa using ha
  rw [← Ideal.absNorm_span_singleton]
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hne]
  rw [map_finprod Ideal.absNorm (Ideal.hasFiniteMulSupport hne)]
  simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]

lemma frobAux_exists_count_le (I : Ideal (𝓞 F)) (hI : I ≠ 0) :
    ∃ N : ℕ, ∀ v : HeightOneSpectrum (𝓞 F),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≤ N := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : ℤ) = 0}.Finite :=
    Filter.eventually_cofinite.mp (Associates.finite_factors hI)
  refine ⟨hfin.toFinset.sup fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors,
    fun v => ?_⟩
  by_cases h : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0
  · rw [Int.natCast_eq_zero] at h
    rw [h]; exact Nat.zero_le _
  · exact Finset.le_sup (f := fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      (hfin.mem_toFinset.mpr h)

lemma frobAux_core (m : ℕ) (hm : m ≠ 0) : ∃ N : ℕ, ∀ α : Fˣ,
    (∀ v : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∉ v.asIdeal → v.valuation F (α : F) ≤ 1) →
    (∀ v : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∈ v.asIdeal →
        v.valuation F ((α : F) - 1) ≤ WithZero.exp (-(N : ℤ))) →
    ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (α : F) ∧
      ((Algebra.norm ℤ a : ℤ) : ZMod m) = 1 ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∈ v.asIdeal → a ∉ v.asIdeal := by
  have hm0 : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hI : (Ideal.span {(m : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0 := by simpa using hm0
  obtain ⟨N, hN⟩ := frobAux_exists_count_le (F := F) _ hI
  refine ⟨N, fun α h1 h2 => ?_⟩
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (((α : F) - 1) / m) ≤ 1 := by
    intro v
    have hvm : v.valuation F (m : F) = v.intValuation (m : 𝓞 F) := by
      rw [← v.valuation_of_algebraMap (K := F)]
      simp
    by_cases hv : (m : 𝓞 F) ∈ v.asIdeal
    · rw [v.intValuation_if_neg hm0] at hvm
      rw [map_div₀, hvm]
      refine div_le_one_of_le₀ ((h2 v hv).trans ?_) zero_le
      exact WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr (hN v)))
    · have hv1 : v.valuation F (m : F) = 1 := by
        rw [hvm, v.intValuation_eq_one_iff]; exact hv
      rw [map_div₀, hv1, div_one]
      exact (Valuation.map_sub _ _ _).trans (max_le (h1 v hv) (by simp))
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint
  refine ⟨1 + (m : 𝓞 F) * b, ?_, frobAux_norm_one_add m b, ?_⟩
  · rw [map_add, map_one, map_mul, hb]
    simp only [map_natCast]
    field_simp
    ring
  · intro v hv h
    have h3 : (m : 𝓞 F) * b ∈ v.asIdeal := v.asIdeal.mul_mem_right b hv
    have h4 : (1 : 𝓞 F) ∈ v.asIdeal := by
      have := Ideal.sub_mem _ h h3
      simpa using this
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h4)

lemma frobAux_natAbs_norm_eq' {M : Type*} [CommMonoid M] (f : ℕ →* M) (a : 𝓞 F) (ha : a ≠ 0) :
    f (Algebra.norm ℤ a).natAbs = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      f (Ideal.absNorm v.asIdeal) ^
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors := by
  have hne : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by simpa using ha
  rw [← Ideal.absNorm_span_singleton]
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hne]
  have := map_finprod (f.comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom)
    (Ideal.hasFiniteMulSupport hne)
  simp only [MonoidHom.comp_apply] at this
  convert this using 1
  simp [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow]

lemma frobAux_prod_cast (m : ℕ) (r : ℕ) (a : 𝓞 F) (ha : a ≠ 0)
    (hn : ((Algebra.norm ℤ a : ℤ) : ZMod m) = 1)
    (hs : 0 < ((-1 : ℝ) ^ r) * ((Algebra.norm ℚ (algebraMap (𝓞 F) F a) : ℚ) : ℝ)) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ZMod m) ^
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors
      = (-1 : ZMod m) ^ r := by
  have h := frobAux_natAbs_norm_eq' (Nat.castRingHom (ZMod m)).toMonoidHom a ha
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, eq_natCast] at h
  rw [← h]
  set n := Algebra.norm ℤ a with hnn
  have hs' : 0 < ((-1 : ℝ) ^ r) * (n : ℝ) := by
    have : ((Algebra.norm ℚ (algebraMap (𝓞 F) F a) : ℚ) : ℝ) = (n : ℝ) := by
      rw [← Algebra.coe_norm_int]; simp [hnn]
    rwa [this] at hs
  rcases Nat.even_or_odd r with he | ho
  · rw [he.neg_one_pow, one_mul] at hs'
    rw [he.neg_one_pow]
    have : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg (by exact_mod_cast hs'.le)
    have h2 : ((n.natAbs : ℕ) : ZMod m) = (n : ZMod m) := by
      rw [← this]; simp
    rw [h2, hn]
  · rw [ho.neg_one_pow, neg_one_mul] at hs'
    rw [ho.neg_one_pow]
    have hn0 : n ≤ 0 := by
      have : (n : ℝ) < 0 := by linarith
      exact_mod_cast this.le
    have : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hn0
    have h2 : ((n.natAbs : ℕ) : ZMod m) = -(n : ZMod m) := by
      have := congrArg (fun z : ℤ => (z : ZMod m)) this
      simpa using this
    rw [h2, hn]

lemma frobAux_val_frobCyc (hζ : IsPrimitiveRoot ζ m)
    (hK : IntermediateField.adjoin F {ζ} = ⊤) (v : HeightOneSpectrum (𝓞 F))
    (hv : (m : 𝓞 F) ∉ v.asIdeal) [NeZero m] :
    ((hζ.autToPow F (frobCyc hζ hK v) : (ZMod m)ˣ) : ZMod m) = (Ideal.absNorm v.asIdeal : ZMod m) := by
  have hσ : frobCyc hζ hK v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
    unfold frobCyc
    rw [dif_pos hv]
    exact (existsUnique_frobCyc hζ hK v hv).exists.choose_spec
  have h2 := hζ.autToPow_spec F (frobCyc hζ hK v)
  rw [hσ] at h2
  have hmpos : 0 < m := Nat.pos_of_neZero m
  have h3 : (ZMod.val (hζ.autToPow F (frobCyc hζ hK v) : ZMod m)) ≡ Ideal.absNorm v.asIdeal [MOD m] := by
    have h5 : ζ ^ ((ZMod.val (hζ.autToPow F (frobCyc hζ hK v) : ZMod m)) % m) =
        ζ ^ (Ideal.absNorm v.asIdeal % m) := by
      have hmo : m = orderOf ζ := hζ.eq_orderOf
      have hmod : ∀ n : ℕ, ζ ^ (n % m) = ζ ^ n := fun n => by
        have := pow_mod_orderOf ζ n
        rwa [← hmo] at this
      rw [hmod, hmod]
      exact h2
    exact hζ.pow_inj (Nat.mod_lt _ hmpos) (Nat.mod_lt _ hmpos) h5
  have h4 := (ZMod.natCast_eq_natCast_iff _ _ m).mpr h3
  rwa [ZMod.natCast_zmod_val] at h4

lemma frobAux_frobProd_cast (hζ : IsPrimitiveRoot ζ m) (hm1 : 1 < m)
    (hK : IntermediateField.adjoin F {ζ} = ⊤) [NeZero m] (α : Fˣ) (a : 𝓞 F)
    (ha : algebraMap (𝓞 F) F a = (α : F)) (ha0 : a ≠ 0)
    (hna : ∀ v : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∈ v.asIdeal → a ∉ v.asIdeal) :
    ((hζ.autToPow F (frobProd hζ hm1 hK α) : (ZMod m)ˣ) : ZMod m) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ZMod m) ^
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors := by
  have hord : ∀ v : HeightOneSpectrum (𝓞 F), ordAt v α =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors : ℤ) := by
    intro v
    unfold ordAt SqDual.ordL
    rw [← ha, v.valuation_of_algebraMap, v.intValuation_if_neg ha0, WithZero.log_exp, neg_neg]
  have hc0 : ∀ v : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∈ v.asIdeal →
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 F))).factors = 0 := by
    intro v hv
    have h1 := (v.intValuation_if_neg ha0).symm.trans (v.intValuation_eq_one_iff.mpr (hna v hv))
    rw [← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  have : IsCyclotomicExtension {m} F K := (haveI : NeZero m := ⟨by omega⟩
    isAbsCyclotomic_iff_isCyclotomicExtension (m := m) (F := F) (K := K)).mp ⟨ζ, hζ, hK⟩
  letI : CommGroup (K ≃ₐ[F] K) :=
    { (inferInstance : Group (K ≃ₐ[F] K)) with
      mul_comm := fun a b => (IsCyclotomicExtension.isMulCommutative {m} F K).is_comm.comm a b }
  unfold frobProd
  change ((hζ.autToPow F (∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal),
    frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) : (ZMod m)ˣ) : ZMod m) = _
  have h1 : (∏ᶠ (𝔭 : HeightOneSpectrum (𝓞 F)) (_ : (m : 𝓞 F) ∉ 𝔭.asIdeal),
      frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) = ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α := by
    refine finprod_congr fun v => ?_
    by_cases hv : (m : 𝓞 F) ∈ v.asIdeal
    · have : frobCyc hζ hK v = 1 := by
        unfold frobCyc
        rw [dif_neg (not_not.mpr hv)]
      rw [this, one_zpow]
      simp [hv]
    · simp [hv]
  rw [h1]
  have hfin : Function.HasFiniteMulSupport fun 𝔭 : HeightOneSpectrum (𝓞 F) => frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α := by
    have hI : (Ideal.span {a} : Ideal (𝓞 F)) ≠ 0 := by simpa using ha0
    refine Set.Finite.subset (Filter.eventually_cofinite.mp (Associates.finite_factors hI)) ?_
    intro v hv hz
    apply hv
    simp only [Function.mem_mulSupport] at *
    have := hord v
    rw [hz] at this
    rw [this]
    simp
  let ψ' : (K ≃ₐ[F] K) →* ZMod m := (Units.coeHom (ZMod m)).comp (hζ.autToPow F)
  change ψ' (∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 F), frobCyc hζ hK 𝔭 ^ ordAt 𝔭 α) = _
  rw [MonoidHom.map_finprod ψ' hfin]
  refine finprod_congr fun v => ?_
  rw [hord v, zpow_natCast, map_pow]
  by_cases hv : (m : 𝓞 F) ∈ v.asIdeal
  · rw [hc0 v hv]; simp
  · congr 1
    exact frobAux_val_frobCyc hζ hK v hv

open scoped Classical in
/-- **Formula 71:11** (O'Meara 1963, p. 194): every $\alpha \in \dot F$ that is integral at all spots of $S$ and
sufficiently close to $1$ at all discrete spots outside $S$ (the spots dividing $m$) satisfies
$\sigma_\alpha\zeta = \zeta^{(-1)^r}$, where $r$ is the number of real spots at which $\alpha$ is negative. "Sufficiently
close" is: $\lvert\alpha - 1\rvert_\mathfrak p \le \exp(-N)$ for a suitable $N$ depending on $F$ and $m$. -/
@[kb "omeara1963" "§71B, 71:11, p. 194"]
theorem exists_frobProd_zeta (hζ : IsPrimitiveRoot ζ m) (hm1 : 1 < m) (hK : IntermediateField.adjoin F {ζ} = ⊤) :
    ∃ N : ℕ, ∀ α : Fˣ,
      (∀ 𝔭 : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∉ 𝔭.asIdeal → 𝔭.valuation F (α : F) ≤ 1) →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 F), (m : 𝓞 F) ∈ 𝔭.asIdeal →
        𝔭.valuation F ((α : F) - 1) ≤ WithZero.exp (-(N : ℤ))) →
      frobProd hζ hm1 hK α ζ =
        ζ ^ ((-1 : ℤ) ^ (Finset.univ.filter fun w : InfinitePlace F =>
          ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw (α : F) < 0).card) := by
  have hm0 : m ≠ 0 := by omega
  have : NeZero m := ⟨hm0⟩
  have : Fact (1 < m) := ⟨hm1⟩
  obtain ⟨N, hN⟩ := frobAux_core (F := F) m hm0
  refine ⟨N, fun α h1 h2 => ?_⟩
  obtain ⟨a, haα, hnorm, hna⟩ := hN α h1 h2
  have ha0 : a ≠ 0 := fun h => α.ne_zero (by rw [← haα, h, map_zero])
  have hsign := frobAux_sign_norm (α : F) α.ne_zero
  have e : Algebra.norm ℚ (algebraMap (𝓞 F) F a) = Algebra.norm ℚ (α : F) := by rw [haα]
  rw [← e] at hsign
  have hprod := frobAux_prod_cast m _ a ha0 hnorm hsign
  have hcast := frobAux_frobProd_cast hζ hm1 hK α a haα ha0 hna
  rw [hprod] at hcast
  have hspec := hζ.autToPow_spec F (frobProd hζ hm1 hK α)
  rw [← hspec]
  generalize ((hζ.autToPow F (frobProd hζ hm1 hK α) : (ZMod m)ˣ) : ZMod m) = x at hcast
  rcases Nat.even_or_odd (Finset.univ.filter fun w : InfinitePlace F =>
      ∃ hw : w.IsReal, InfinitePlace.embedding_of_isReal hw (α : F) < 0).card with he | ho
  · rw [he.neg_one_pow] at hcast
    rw [hcast, ZMod.val_one, he.neg_one_pow, zpow_one, pow_one]
  · rw [ho.neg_one_pow] at hcast
    rw [ho.neg_one_pow, zpow_neg_one]
    have hk : ζ ^ (x.val + 1) = 1 := by
      rw [hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val, hcast]
      ring
    rw [pow_succ] at hk
    exact eq_inv_of_mul_eq_one_left hk


end QuadFormsKB.OMeara
