/-
# Hasse norm theorem, step 4c–d: infinite places and the product formula

* `index_sq_infinite`: $[F_v^\times : F_v^{\times 2}] = 2$ (real) or $1$ (complex);
* `two_le_index_norm_inf`: at an infinite place where $a$ is not a square, the local norms have index $\ge 2$;
* `splitsInf_of_isSquare`: a local square at an infinite place splits in $F(\sqrt a)$;
* `prod_absNorm_pow_ordTwo`: $\prod_{v \mid 2} N(v)^{\operatorname{ord}_v 2} = N(2\mathcal O_K) = 2^{[K:\mathbb Q]}$;
* `prod_index_sq`: $\prod_{v \in S \cup \infty} [K_v^\times : K_v^{\times 2}] = 4^{|S| + r_\infty}$ for $S \supseteq$ dyadic primes
  (Milne VII, Lemma 6.6 with $n = 2$).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.LocalNorm

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [Algebra.IsQuadraticExtension F L]

/-- At a real place, $F \to F_v \cong \mathbb R$ is the real embedding. -/
lemma real_algebraMap {v : InfinitePlace F} (hv : v.IsReal) (c : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hv (algebraMap F v.Completion c) =
      InfinitePlace.embedding_of_isReal hv c := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv _


/-- The index of the squares is invariant under ring isomorphisms. -/
lemma index_sq_congr {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    (powMonoidHom 2 : Rˣ →* Rˣ).range.index = (powMonoidHom 2 : R'ˣ →* R'ˣ).range.index := by
  have hmap : (powMonoidHom 2 : Rˣ →* Rˣ).range.map (Units.mapEquiv e.toMulEquiv).toMonoidHom =
      (powMonoidHom 2 : R'ˣ →* R'ˣ).range := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨Units.mapEquiv e.toMulEquiv y, by simp⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(Units.mapEquiv e.toMulEquiv).symm y ^ 2, ⟨_, rfl⟩, ?_⟩
      simp only [powMonoidHom_apply, MulEquiv.coe_toMonoidHom, map_pow, MulEquiv.apply_symm_apply]
  rw [← Subgroup.index_map_equiv _ (Units.mapEquiv e.toMulEquiv)]
  erw [hmap]

/-- $[\mathbb R^\times : \mathbb R^{\times 2}] = 2$. -/
lemma index_sq_real : (powMonoidHom 2 : ℝˣ →* ℝˣ).range.index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨-1, fun b => ?_⟩
  have hsq : ∀ c : ℝˣ, c ∈ (powMonoidHom 2 : ℝˣ →* ℝˣ).range ↔ 0 < (c : ℝ) := by
    intro c
    constructor
    · rintro ⟨d, rfl⟩
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
      exact pow_two_pos_of_ne_zero (Units.ne_zero d)
    · intro hc
      refine ⟨Units.mk0 (Real.sqrt c) (Real.sqrt_ne_zero'.mpr hc), ?_⟩
      ext; simp [Real.sq_sqrt hc.le]
  rw [hsq, hsq]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, mul_neg, mul_one, Left.neg_pos_iff]
  rcases lt_or_gt_of_ne (Units.ne_zero b) with h | h
  · simp [h, not_lt.mpr h.le]
  · simp [h, not_lt.mpr h.le]

/-- $[\mathbb C^\times : \mathbb C^{\times 2}] = 1$. -/
lemma index_sq_complex : (powMonoidHom 2 : ℂˣ →* ℂˣ).range.index = 1 := by
  rw [Subgroup.index_eq_one, eq_top_iff]
  intro c _
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ) (n := 2) (by norm_num)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact (Units.ne_zero c) hr.symm
  exact ⟨Units.mk0 r hr0, by ext; simp [hr]⟩

open scoped Classical in
/-- **Square classes at an infinite place:** $2$ if real, $1$ if complex. -/
theorem index_sq_infinite (v : InfinitePlace F) :
    (powMonoidHom 2 : v.Completionˣ →* v.Completionˣ).range.index = if v.IsReal then 2 else 1 := by
  split_ifs with hv
  · rw [index_sq_congr (InfinitePlace.Completion.ringEquivRealOfIsReal hv), index_sq_real]
  · rw [InfinitePlace.not_isReal_iff_isComplex] at hv
    rw [index_sq_congr (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv), index_sq_complex]


/-- **Local norms at a non-split infinite place:** if $a$ is not a square in $F_v$ ($v \mid \infty$), then
$v$ is real, $a < 0$ there, the local norms are the positive reals, and their index is $\ge 2$. -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem two_le_index_norm_inf (a : F) (hd : ¬ IsSquare a) (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (v : InfinitePlace F) (hv : ¬ IsSquare (algebraMap F v.Completion a)) :
    2 ≤ (Units.map (Algebra.norm v.Completion : v.Completion ⊗[F] L →* v.Completion)).range.index := by
  classical
  set Fv := v.Completion
  set E := Fv ⊗[F] L
  have hreal : v.IsReal := by
    by_contra hc
    rw [InfinitePlace.not_isReal_iff_isComplex] at hc
    apply hv
    set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (e (algebraMap F Fv a)) (n := 2) (by norm_num)
    refine ⟨e.symm r, ?_⟩
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, ← pow_two, hr]
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hreal
  obtain ⟨t, -, ht2, hspanT, huniqT, hnormT, hrank⟩ := tensor_structure a hd s hs hspan Fv
  set α := algebraMap F Fv a with hα
  have hneg : e α < 0 := by
    by_contra hc
    push Not at hc
    apply hv
    refine ⟨e.symm (Real.sqrt (e α)), ?_⟩
    apply e.injective
    rw [map_mul, RingEquiv.apply_symm_apply, Real.mul_self_sqrt hc]
  set Nm : Eˣ →* Fvˣ := Units.map (Algebra.norm Fv : E →* Fv)
  set incl : Fvˣ →* Eˣ := Units.map (algebraMap Fv E : Fv →* E)
  have hNincl : ∀ c : Fvˣ, Nm (incl c) = c ^ 2 := by
    intro c; ext
    simp only [Nm, incl, Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
    rw [Algebra.norm_algebraMap, hrank]
  have hle : (powMonoidHom 2 : Fvˣ →* Fvˣ).range ≤ Nm.range := by
    rintro _ ⟨c, rfl⟩; exact ⟨incl c, hNincl c⟩
  have hsq2 : (powMonoidHom 2 : Fvˣ →* Fvˣ).range.index = 2 := by
    rw [index_sq_congr e, index_sq_real]
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hsq2] at hdvd
  have hne : Nm.range ≠ ⊤ := by
    intro htop
    have hm1 : (-1 : Fvˣ) ∈ Nm.range := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy⟩ := hm1
    obtain ⟨x₀, x₁, hyx⟩ := hspanT (y : E)
    have hval : Algebra.norm Fv (y : E) = -1 := by
      have := congrArg Units.val hy
      simpa [Nm] using this
    rw [hyx, hnormT] at hval
    have := congrArg e hval
    rw [map_sub, map_mul, map_pow, map_pow, map_neg, map_one] at this
    nlinarith [sq_nonneg (e x₀), sq_nonneg (e x₁)]
  have h1 : Nm.range.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have h0 : Nm.range.index ≠ 0 := fun h => by rw [h] at hdvd; norm_num at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega


/-- **A local square splits at an infinite place:** if $L = F(s)$, $s^2 = a$, $\sigma s = -s$, and $a$ is a
square in $F_v$ ($v \mid \infty$), then two places of $L$ lie over $v$.

*Proof.* Otherwise $\sigma w = w$ for the place $w$ over $v$, so for $\varphi = w$'s embedding,
$\varphi \circ \sigma^{-1} \in \{\varphi, \bar\varphi\}$. The first gives $\varphi(s) = -\varphi(s)$; the second makes
$\varphi|_F$ real and $\varphi(s)$ purely imaginary, so $a = s^2 < 0$ at the real place $v$, not a square. -/
@[kb "neukirch1999" "Ch. II §8 [unverified]"]
theorem splitsInf_of_isSquare (σ : L ≃ₐ[F] L) (s : L) (a : F) (hs : s ^ 2 = algebraMap F L a)
    (hσs : σ s = -s) (ha : a ≠ 0) (v : InfinitePlace F)
    (hsq : IsSquare (algebraMap F v.Completion a)) : SplitsInf (L := L) v := by
  classical
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := L) v
  simp only at hw
  have hcomap : (σ • w).comap (algebraMap F L) = w.comap (algebraMap F L) := by
    rw [InfinitePlace.comap_smul]
    congr 1
    ext c
    simp
  by_contra hns
  have hfix : σ • w = w := by
    by_contra hne
    exact hns ⟨σ • w, w, hne, hcomap.trans hw, hw⟩
  set φ := w.embedding
  have hφ : InfinitePlace.mk (φ.comp (σ.symm : L ≃+* L).toRingHom) = InfinitePlace.mk φ := by
    have : σ • w = InfinitePlace.mk (φ.comp (σ.symm : L ≃+* L).toRingHom) := by
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.smul_mk]; rfl
    rw [← this, hfix, InfinitePlace.mk_embedding]
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap F L).injective] at hs
    exact ha hs
  have hσinv : σ.symm s = -s := by
    have := congrArg σ.symm hσs
    rw [AlgEquiv.symm_apply_apply, map_neg] at this
    linear_combination this
  rcases InfinitePlace.mk_eq_iff.mp hφ with h | h
  · -- φ ∘ σ⁻¹ = φ
    have := congrArg (fun f : L →+* ℂ => f s) h
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    change φ (σ.symm s) = φ s at this
    rw [hσinv, map_neg] at this
    have h0 : φ s = 0 := by linear_combination -this / 2
    exact hs0 ((map_eq_zero_iff φ φ.injective).mp h0)
  · -- conj ∘ φ = φ ∘ σ⁻¹
    have hconj : ∀ y : L, (starRingEnd ℂ) (φ y) = φ (σ y) := by
      intro y
      have := congrArg (fun f : L →+* ℂ => f (σ y)) h
      simpa using this
    have hreal : ∀ c : F, (starRingEnd ℂ) (φ (algebraMap F L c)) = φ (algebraMap F L c) := by
      intro c; rw [hconj]; simp
    set z := φ s
    have hz : (starRingEnd ℂ) z = -z := by rw [hconj, hσs, map_neg]
    have hzre : z.re = 0 := by
      have := congrArg Complex.re hz
      simp at this; linarith
    have hz0 : z ≠ 0 := fun h0 => hs0 ((map_eq_zero_iff φ φ.injective).mp h0)
    have hzim : z.im ≠ 0 := by
      intro him; apply hz0; exact Complex.ext hzre him
    have hza : φ (algebraMap F L a) = z ^ 2 := by rw [← hs, map_pow]
    -- v is real, with embedding φ ∘ algebraMap
    set ψ : F →+* ℂ := φ.comp (algebraMap F L)
    have hψ : NumberField.ComplexEmbedding.IsReal ψ :=
      NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun c => hreal c)
    have hv : v = InfinitePlace.mk ψ := by
      rw [← hw, ← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk]
    have hvreal : v.IsReal := by rw [hv]; exact InfinitePlace.isReal_mk_iff.mpr hψ
    have hemb : v.embedding = ψ := by
      rw [hv]; exact InfinitePlace.embedding_mk_eq_of_isReal hψ
    obtain ⟨α, hα⟩ := hsq
    have h1 := real_algebraMap hvreal a
    rw [hα, map_mul] at h1
    have h2 := InfinitePlace.embedding_of_isReal_apply hvreal a
    rw [← h1, hemb] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.ofReal_re, ψ, RingHom.coe_comp, Function.comp_apply, hza, pow_two,
      Complex.mul_re, hzre, mul_zero, zero_sub] at h3
    have h4 : 0 ≤ (InfinitePlace.Completion.ringEquivRealOfIsReal hvreal) α *
        (InfinitePlace.Completion.ringEquivRealOfIsReal hvreal) α := mul_self_nonneg _
    have h5 : 0 < z.im * z.im := mul_self_pos.mpr hzim
    linarith


section Product

variable {K : Type*} [Field K] [NumberField K]

/-- The factor count of $v$ in $(2)$ is $\operatorname{ord}_v 2$. -/
lemma count_eq_ordTwo (v : HeightOneSpectrum (𝓞 K)) :
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(2 : 𝓞 K)})).factors = ordTwo v := by
  have h2 : (2 : 𝓞 K) ≠ 0 := two_ne_zero
  have e1 := HeightOneSpectrum.intValuation_if_neg v h2
  have e2 := HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v h2
  rw [e1, exp_inj, neg_inj, Nat.cast_inj] at e2
  exact e2

/-- **$\prod_{v \mid 2} N(v)^{\operatorname{ord}_v 2} = 2^{[K:\mathbb Q]}$**, for any finite set $S$ of primes containing
the dyadic ones. -/
theorem prod_absNorm_pow_ordTwo (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ ordTwo v = 2 ^ Module.finrank ℚ K := by
  classical
  set I : Ideal (𝓞 K) := Ideal.span {(2 : 𝓞 K)}
  have hI : I ≠ 0 := by simp [I]
  have hfact := Ideal.finprod_heightOneSpectrum_factorization hI
  have hnorm : Ideal.absNorm I = 2 ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton, show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp,
      Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  rw [← hnorm, ← hfact, map_finprod _ (Ideal.hasFiniteMulSupport hI)]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [HeightOneSpectrum.maxPowDividing, map_pow, count_eq_ordTwo]
  · intro v hv
    apply hS
    by_contra h2
    apply hv
    simp only
    rw [HeightOneSpectrum.maxPowDividing, count_eq_ordTwo]
    have : ordTwo v = 0 := by
      have e := HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v (two_ne_zero : (2 : 𝓞 K) ≠ 0)
      rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v 2).mpr h2] at e
      rw [← exp_zero, exp_inj] at e
      unfold ordTwo; omega
    rw [this, pow_zero, map_one]

open scoped Classical in
/-- **The product formula for square classes:** for $S \supseteq$ the dyadic primes,
$\prod_{v \in S} [K_v^\times : K_v^{\times2}] \cdot \prod_{v \mid \infty} [K_v^\times : K_v^{\times2}] = 4^{|S| + r_\infty}$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.6 (n = 2) [unverified]; omeara1963 §65B, 65:7, p. 178"]
theorem prod_index_sq (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index) *
      (∏ w : InfinitePlace K, (powMonoidHom 2 : w.Completionˣ →* w.Completionˣ).range.index) =
      4 ^ (S.card + Fintype.card (InfinitePlace K)) := by
  simp only [index_sq_completion, index_sq_infinite]
  rw [Finset.prod_mul_distrib, Finset.prod_const, prod_absNorm_pow_ordTwo S hS]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hc := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hreal : (Finset.univ.filter fun w : InfinitePlace K => w.IsReal).card =
      InfinitePlace.nrRealPlaces K := by
    rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
  rw [hreal, ← hr, hc, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1; ring

end Product

end QuadFormsKB.HN

end
