import QuadFormsKB.Tamagawa.Measure.Weil.GnatBaseChange

/-!
# Infinite places of a quadratic extension $K=F(\delta)$, $\delta^2=d$

**Part A.** Components of `adeleMap F K t` at the complex places $w$ of $K$: if $w|_F$ is real then
$\iota(t)_w=t_{w|_F}$ (as a complex number); if $w|_F=v$ is complex then $\iota(t)_w=t_v$ or $\overline{t_v}$ according to
whether $w\circ\mathrm{alg}=v$ or $\bar v$ as embeddings.

**Part B.** Fibres of `comap` over the infinite places of $F$ for $K=F(\delta)$, $\delta=$ `bK 1`, $\delta^2=d$
(basis `bK` of $K/F$ with `bK 0 = 1`): the key tool is the $F$-automorphism $\tau:\delta\mapsto-\delta$ (`deltaConj`);
the embeddings $K\to\mathbb C$ extending $\sigma:F\to\mathbb C$ are exactly $\varphi_0$ and $\varphi_0\circ\tau$.

* $\sigma$ real, $\sigma(d)>0$: two real places over $v$, with opposite $\delta$-values.
* $\sigma$ real, $\sigma(d)<0$: one place over $v$, complex (ramified), $\operatorname{Re}\delta=0$.
* $\sigma$ complex: two complex places over $v$.

**Part C.** $\delta^2=d$ at every place.
-/

open MeasureTheory Measure Set Function Topology NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### Part A: complex components of `adeleMap` -/

section PartA

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- **Complex places over a real place**: $\iota(t)_w=t_{w|_F}$ (viewed in $\mathbb C$). -/
theorem adeleMap_fst_snd_of_isReal_comap (t : Adeles F) (w : {w : InfinitePlace K // w.IsComplex})
    (hv : (w.1.comap (algebraMap F K)).IsReal) :
    (adeleMap F K t).1.2 w = ((t.1.1 ⟨w.1.comap (algebraMap F K), hv⟩ : ℝ) : ℂ) := by
  set v : {v : InfinitePlace F // v.IsReal} := ⟨w.1.comap (algebraMap F K), hv⟩
  let L1 : mixedSpace F →ₗ[ℝ] ℂ := (LinearMap.proj w).comp ((LinearMap.snd ℝ _ _).comp (infMap F K))
  let L2 : mixedSpace F →ₗ[ℝ] ℂ :=
    Complex.ofRealAm.toLinearMap.comp ((LinearMap.proj v).comp (LinearMap.fst ℝ _ _))
  have hL : L1 = L2 := by
    refine LinearMap.ext_on_range (span_range_mixedEmbedding F) fun x => ?_
    simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.fst_apply,
      LinearMap.snd_apply, infMap_mixedEmbedding, mixedEmbedding_apply_isReal, mixedEmbedding_apply_isComplex,
      AlgHom.toLinearMap_apply, Complex.ofRealAm_coe]
    rw [embedding_of_isReal_apply]
    show _ = (v.1.embedding x)
    show _ = (w.1.comap (algebraMap F K)).embedding x
    rw [comap_embedding_of_isReal (algebraMap F K) hv]
    rfl
  have := LinearMap.congr_fun hL t.1
  simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.snd_apply, LinearMap.fst_apply, AlgHom.toLinearMap_apply, Complex.ofRealAm_coe, Complex.conjAe_coe] at this
  exact this

/-- **Complex places over a complex place, same orientation.** -/
theorem adeleMap_fst_snd_of_comp_eq (t : Adeles F) (w : {w : InfinitePlace K // w.IsComplex})
    (hv : (w.1.comap (algebraMap F K)).IsComplex)
    (h : w.1.embedding.comp (algebraMap F K) = (w.1.comap (algebraMap F K)).embedding) :
    (adeleMap F K t).1.2 w = t.1.2 ⟨w.1.comap (algebraMap F K), hv⟩ := by
  set v : {v : InfinitePlace F // v.IsComplex} := ⟨w.1.comap (algebraMap F K), hv⟩
  let L1 : mixedSpace F →ₗ[ℝ] ℂ := (LinearMap.proj w).comp ((LinearMap.snd ℝ _ _).comp (infMap F K))
  let L2 : mixedSpace F →ₗ[ℝ] ℂ := (LinearMap.proj v).comp (LinearMap.snd ℝ _ _)
  have hL : L1 = L2 := by
    refine LinearMap.ext_on_range (span_range_mixedEmbedding F) fun x => ?_
    simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.snd_apply,
      infMap_mixedEmbedding, mixedEmbedding_apply_isComplex]
    exact congrArg (fun f : F →+* ℂ => f x) h
  have := LinearMap.congr_fun hL t.1
  simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.snd_apply, LinearMap.fst_apply, AlgHom.toLinearMap_apply, Complex.ofRealAm_coe, Complex.conjAe_coe] at this
  exact this

/-- **Complex places over a complex place, opposite orientation.** -/
theorem adeleMap_fst_snd_of_comp_eq_conj (t : Adeles F) (w : {w : InfinitePlace K // w.IsComplex})
    (hv : (w.1.comap (algebraMap F K)).IsComplex)
    (h : w.1.embedding.comp (algebraMap F K) = (starRingEnd ℂ).comp (w.1.comap (algebraMap F K)).embedding) :
    (adeleMap F K t).1.2 w = starRingEnd ℂ (t.1.2 ⟨w.1.comap (algebraMap F K), hv⟩) := by
  set v : {v : InfinitePlace F // v.IsComplex} := ⟨w.1.comap (algebraMap F K), hv⟩
  let L1 : mixedSpace F →ₗ[ℝ] ℂ := (LinearMap.proj w).comp ((LinearMap.snd ℝ _ _).comp (infMap F K))
  let L2 : mixedSpace F →ₗ[ℝ] ℂ :=
    Complex.conjAe.toLinearMap.comp ((LinearMap.proj v).comp (LinearMap.snd ℝ _ _))
  have hL : L1 = L2 := by
    refine LinearMap.ext_on_range (span_range_mixedEmbedding F) fun x => ?_
    simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.snd_apply,
      infMap_mixedEmbedding, mixedEmbedding_apply_isComplex, AlgHom.toLinearMap_apply, Complex.conjAe_coe]
    exact congrArg (fun f : F →+* ℂ => f x) h
  have := LinearMap.congr_fun hL t.1
  simp only [L1, L2, LinearMap.coe_comp, comp_apply, LinearMap.coe_proj, Function.eval, LinearMap.snd_apply, LinearMap.fst_apply, AlgHom.toLinearMap_apply, Complex.ofRealAm_coe, Complex.conjAe_coe] at this
  exact this

/-- For a complex place $w$ of $K$ over a complex place $v$ of $F$, exactly one of
$w\circ\mathrm{alg}=v$, $w\circ\mathrm{alg}=\bar v$ holds. -/
theorem embedding_comp_eq_or_conj (w : InfinitePlace K) (hv : (w.comap (algebraMap F K)).IsComplex) :
    (w.embedding.comp (algebraMap F K) = (w.comap (algebraMap F K)).embedding ∨
      w.embedding.comp (algebraMap F K) = (starRingEnd ℂ).comp (w.comap (algebraMap F K)).embedding) ∧
    ¬ (w.embedding.comp (algebraMap F K) = (w.comap (algebraMap F K)).embedding ∧
      w.embedding.comp (algebraMap F K) = (starRingEnd ℂ).comp (w.comap (algebraMap F K)).embedding) := by
  set v := w.comap (algebraMap F K) with hvdef
  have hmk : mk (w.embedding.comp (algebraMap F K)) = mk v.embedding := by
    rw [mk_embedding, hvdef, ← comap_mk, mk_embedding]
  constructor
  · rcases mk_eq_iff.1 hmk with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← h]; ext x; simp [ComplexEmbedding.conjugate]
  · rintro ⟨h1, h2⟩
    rw [h1] at h2
    have hr : ComplexEmbedding.IsReal v.embedding := by
      ext x
      have := congrArg (fun f : F →+* ℂ => f x) h2
      simp only [RingHom.comp_apply] at this
      simpa [ComplexEmbedding.conjugate] using this.symm
    exact (not_isReal_iff_isComplex.2 hv) (isReal_iff.2 hr)

end PartA

/-! ### Part B: the automorphism $\delta\mapsto-\delta$ and the fibres of `comap` -/

section PartB

variable {F K : Type} [Field F] [Field K] [Algebra F K] (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1)
  {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)

/-- The $F$-linear map $x_0+x_1\delta\mapsto x_0-x_1\delta$. -/
def deltaConjLin : K →ₗ[F] K := bK.constr F ![1, -bK 1]

omit hb₁ in
include hb₀ in
theorem deltaConjLin_one : deltaConjLin bK 1 = 1 := by
  have h : deltaConjLin bK (bK 0) = 1 := by
    rw [deltaConjLin, Module.Basis.constr_basis]; rfl
  rwa [hb₀] at h

omit hb₀ hb₁ in
theorem deltaConjLin_delta : deltaConjLin bK (bK 1) = - bK 1 := by
  rw [deltaConjLin, Module.Basis.constr_basis]; rfl

include hb₀ hb₁ in
theorem deltaConjLin_mul (x y : K) : deltaConjLin bK (x * y) = deltaConjLin bK x * deltaConjLin bK y := by
  have h : (LinearMap.mul F K).compr₂ (deltaConjLin bK) =
      ((LinearMap.mul F K).compl₁₂ (deltaConjLin bK) (deltaConjLin bK)) := by
    refine LinearMap.ext_basis bK bK fun i j => ?_
    have h1 := deltaConjLin_one bK hb₀
    have h2 := deltaConjLin_delta bK
    fin_cases i <;> fin_cases j <;>
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', Fin.zero_eta, Fin.mk_one,
        hb₀, h1, h2, one_mul, mul_one, neg_mul, mul_neg, neg_neg, hb₁, Fin.isValue]
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1]
  exact LinearMap.congr_fun₂ h x y

/-- **The $F$-automorphism of $K=F(\delta)$ with $\delta\mapsto-\delta$** (as an algebra homomorphism). -/
def deltaConj : K →ₐ[F] K :=
  AlgHom.ofLinearMap (deltaConjLin bK) (deltaConjLin_one bK hb₀) (deltaConjLin_mul bK hb₀ hb₁)

theorem deltaConj_delta : deltaConj bK hb₀ hb₁ (bK 1) = - bK 1 := deltaConjLin_delta bK

omit hb₀ in
include hb₁ in
theorem sq_delta_emb(φ : K →+* ℂ) : φ (bK 1) ^ 2 = φ (algebraMap F K d) := by
  rw [sq, ← map_mul, hb₁]

include hb₀ in
/-- A ring homomorphism $K\to\mathbb C$ is determined by its restriction to $F$ and its value at $\delta$. -/
theorem hom_ext_delta (φ ψ : K →+* ℂ) (h : ∀ a : F, φ (algebraMap F K a) = ψ (algebraMap F K a))
    (hδ : φ (bK 1) = ψ (bK 1)) : φ = ψ := by
  ext x
  have hx := bK.sum_repr x
  rw [← hx]
  simp only [Fin.sum_univ_two, map_add, Algebra.smul_def, map_mul, h, hb₀, mul_one, hδ]

include hb₀ hb₁ in
/-- The embeddings $K\to\mathbb C$ agreeing with $\varphi_0$ on $F$ are $\varphi_0$ and $\varphi_0\circ\tau$. -/
theorem eq_or_comp_deltaConj (φ φ₀ : K →+* ℂ) (h : ∀ a : F, φ (algebraMap F K a) = φ₀ (algebraMap F K a)) :
    φ = φ₀ ∨ φ = φ₀.comp (deltaConj bK hb₀ hb₁).toRingHom := by
  have hsq : φ (bK 1) ^ 2 = φ₀ (bK 1) ^ 2 := by rw [sq_delta_emb bK hb₁, sq_delta_emb bK hb₁, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
  · exact Or.inl (hom_ext_delta bK hb₀ φ φ₀ h h1)
  · refine Or.inr (hom_ext_delta bK hb₀ φ _ (fun a => ?_) ?_)
    · simp [h]
    · simp [h1, deltaConj_delta bK hb₀ hb₁]

theorem comp_deltaConj_apply_algebraMap (φ₀ : K →+* ℂ) (a : F) :
    (φ₀.comp (deltaConj bK hb₀ hb₁).toRingHom) (algebraMap F K a) = φ₀ (algebraMap F K a) := by
  simp

include hb₀ hb₁ in
theorem comp_deltaConj_delta (φ₀ : K →+* ℂ) :
    (φ₀.comp (deltaConj bK hb₀ hb₁).toRingHom) (bK 1) = - φ₀ (bK 1) := by
  simp [deltaConj_delta bK hb₀ hb₁]

omit hb₀ in
include hb₁ in
/-- $d\neq0$ (otherwise $\delta^2=0$, so $\delta=0$, contradicting that `bK 1` is a basis vector). -/
theorem d_ne_zero : d ≠ 0 := by
  rintro rfl
  rw [map_zero, mul_self_eq_zero] at hb₁
  exact bK.ne_zero 1 hb₁

omit hb₀ hb₁ in
theorem exists_extension [Module.Finite F K] (σ : F →+* ℂ) : ∃ φ : K →+* ℂ, φ.comp (algebraMap F K) = σ := by
  have := Algebra.IsAlgebraic.of_finite F K
  exact ⟨ComplexEmbedding.lift K σ, ComplexEmbedding.lift_comp_algebraMap (k := F) (K := K) σ⟩

omit hb₀ hb₁ in
theorem exists_extension_of_place (w : InfinitePlace K) (v : InfinitePlace F) (h : w.comap (algebraMap F K) = v) :
    ∃ φ : K →+* ℂ, φ.comp (algebraMap F K) = v.embedding ∧ mk φ = w := by
  have hmk : mk (w.embedding.comp (algebraMap F K)) = mk v.embedding := by
    rw [mk_embedding, ← h, ← comap_mk, mk_embedding]
  rcases mk_eq_iff.1 hmk with h1 | h1
  · exact ⟨w.embedding, h1, mk_embedding w⟩
  · refine ⟨ComplexEmbedding.conjugate w.embedding, ?_, ?_⟩
    · rw [← h1]; ext x; rfl
    · rw [mk_conjugate_eq, mk_embedding]

omit hb₀ hb₁ in
theorem comap_mk_eq (φ : K →+* ℂ) (v : InfinitePlace F) (h : φ.comp (algebraMap F K) = v.embedding) :
    (mk φ).comap (algebraMap F K) = v := by
  rw [comap_mk, h, mk_embedding]

theorem im_eq_zero_of_sq_eq_pos (z : ℂ) (r : ℝ) (h : z ^ 2 = (r : ℂ)) (hr : 0 < r) : z.im = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  by_contra hne
  have : z.re = 0 := by
    have : z.im * (2 * z.re) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · linarith
  rw [this] at h1
  have := mul_self_nonneg z.im
  nlinarith

theorem re_eq_zero_of_sq_neg (z : ℂ) (r : ℝ) (h : z ^ 2 = (r : ℂ)) (hr : r < 0) : z.re = 0 ∧ z.im ≠ 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have him : z.im ≠ 0 := by
    intro h0
    rw [h0] at h1
    nlinarith [mul_self_nonneg z.re]
  refine ⟨?_, him⟩
  have : z.im * (2 * z.re) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h him
  · linarith

omit hb₀ hb₁ in
theorem isReal_of_im_eq_zero (φ : K →+* ℂ) (hφ : ComplexEmbedding.IsReal (φ.comp (algebraMap F K)))
    (hz : (φ (bK 1)).im = 0) (hb₀ : bK 0 = 1) : ComplexEmbedding.IsReal φ := by
  rw [ComplexEmbedding.isReal_iff]
  refine hom_ext_delta bK hb₀ _ _ (fun a => ?_) ?_
  · exact congrArg (fun f : F →+* ℂ => f a) (ComplexEmbedding.isReal_iff.1 hφ)
  · exact Complex.conj_eq_iff_im.2 hz

include hb₀ hb₁ in
theorem conjugate_eq_comp_deltaConj (φ : K →+* ℂ) (hφ : ComplexEmbedding.IsReal (φ.comp (algebraMap F K)))
    (hz : (φ (bK 1)).re = 0) :
    ComplexEmbedding.conjugate φ = φ.comp (deltaConj bK hb₀ hb₁).toRingHom := by
  refine hom_ext_delta bK hb₀ _ _ (fun a => ?_) ?_
  · have := congrArg (fun f : F →+* ℂ => f a) (ComplexEmbedding.isReal_iff.1 hφ)
    simpa using this
  · rw [comp_deltaConj_delta bK hb₀ hb₁]
    apply Complex.ext <;> simp [hz]

variable [Module.Finite F K]

include hb₀ hb₁ in
/-- **Real place $v$ of $F$ with $\sigma_v(d)>0$**: exactly two places of $K$ lie over $v$, both real, with
$\delta$-values $\pm\sqrt{\sigma_v(d)}$. -/
theorem exists_two_real_places (v : {v : InfinitePlace F // v.IsReal}) (hpos : 0 < embedding_of_isReal v.2 d) :
    ∃ w₁ w₂ : {w : InfinitePlace K // w.IsReal}, w₁ ≠ w₂ ∧ w₁.1.comap (algebraMap F K) = v.1 ∧
      w₂.1.comap (algebraMap F K) = v.1 ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = w₁.1 ∨ w = w₂.1) ∧
      (∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) ≠ v.1) ∧
      embedding_of_isReal w₂.2 (bK 1) = - embedding_of_isReal w₁.2 (bK 1) := by
  have hσ : ComplexEmbedding.IsReal v.1.embedding := isReal_iff.1 v.2
  obtain ⟨φ₀, hφ₀⟩ := exists_extension (K := K) v.1.embedding
  have hφ₀a : ∀ a : F, φ₀ (algebraMap F K a) = v.1.embedding a := fun a => congrArg (fun f : F →+* ℂ => f a) hφ₀
  set τ := (deltaConj bK hb₀ hb₁).toRingHom
  have hsq : φ₀ (bK 1) ^ 2 = ((embedding_of_isReal v.2 d : ℝ) : ℂ) := by
    rw [sq_delta_emb bK hb₁, hφ₀a, embedding_of_isReal_apply]
  have him := im_eq_zero_of_sq_eq_pos _ _ hsq hpos
  have hz0 : φ₀ (bK 1) ≠ 0 := by
    intro h0
    rw [h0] at hsq
    have : ((embedding_of_isReal v.2 d : ℝ) : ℂ) = 0 := by rw [← hsq]; ring
    exact hpos.ne' (Complex.ofReal_eq_zero.1 this)
  have hr0 : ComplexEmbedding.IsReal φ₀ := isReal_of_im_eq_zero bK φ₀ (by rw [hφ₀]; exact hσ) him hb₀
  have hr1 : ComplexEmbedding.IsReal (φ₀.comp τ) := by
    refine isReal_of_im_eq_zero bK _ ?_ ?_ hb₀
    · have : (φ₀.comp τ).comp (algebraMap F K) = φ₀.comp (algebraMap F K) := by
        ext a; exact comp_deltaConj_apply_algebraMap bK hb₀ hb₁ φ₀ a
      rw [this, hφ₀]; exact hσ
    · rw [comp_deltaConj_delta bK hb₀ hb₁]; simp [him]
  have hc1 : ∀ a : F, (φ₀.comp τ) (algebraMap F K a) = v.1.embedding a := fun a => by
    rw [comp_deltaConj_apply_algebraMap bK hb₀ hb₁, hφ₀a]
  refine ⟨⟨mk φ₀, isReal_mk_iff.2 hr0⟩, ⟨mk (φ₀.comp τ), isReal_mk_iff.2 hr1⟩, ?_, comap_mk_eq φ₀ v.1 hφ₀,
    comap_mk_eq _ v.1 (by ext a; exact hc1 a), ?_, ?_, ?_⟩
  · intro h
    have h' : mk φ₀ = mk (φ₀.comp τ) := congrArg Subtype.val h
    have : φ₀ = φ₀.comp τ := by
      rcases mk_eq_iff.1 h' with h1 | h1
      · exact h1
      · rw [ComplexEmbedding.isReal_iff.1 hr0] at h1; exact h1
    have h2 : φ₀ (bK 1) = (φ₀.comp τ) (bK 1) := congrArg (fun f : K →+* ℂ => f (bK 1)) this
    rw [comp_deltaConj_delta bK hb₀ hb₁] at h2
    exact hz0 (by linear_combination h2 / 2)
  · intro w hw
    obtain ⟨φ, hφ, rfl⟩ := exists_extension_of_place w v.1 hw
    rcases eq_or_comp_deltaConj bK hb₀ hb₁ φ φ₀ (fun a => by
      rw [hφ₀a]; exact congrArg (fun f : F →+* ℂ => f a) hφ) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · intro w hw
    obtain ⟨φ, hφ, hmk⟩ := exists_extension_of_place w.1 v.1 hw
    rcases eq_or_comp_deltaConj bK hb₀ hb₁ φ φ₀ (fun a => by
      rw [hφ₀a]; exact congrArg (fun f : F →+* ℂ => f a) hφ) with h | h
    · have := isReal_mk_iff.2 (h ▸ hr0 : ComplexEmbedding.IsReal φ)
      rw [hmk] at this
      exact (not_isReal_iff_isComplex.2 w.2) this
    · have := isReal_mk_iff.2 (h ▸ hr1 : ComplexEmbedding.IsReal φ)
      rw [hmk] at this
      exact (not_isReal_iff_isComplex.2 w.2) this
  · apply Complex.ofReal_injective
    rw [embedding_of_isReal_apply, Complex.ofReal_neg, embedding_of_isReal_apply]
    show (mk (φ₀.comp τ)).embedding (bK 1) = - (mk φ₀).embedding (bK 1)
    rw [embedding_mk_eq_of_isReal hr1, embedding_mk_eq_of_isReal hr0]
    exact comp_deltaConj_delta bK hb₀ hb₁ φ₀

omit hb₀ in
include hb₁ in
/-- **(C), complex form**: $\delta^2=d$ at every embedding. -/
theorem embedding_delta_sq (w : InfinitePlace K) :
    w.embedding (bK 1) ^ 2 = (w.embedding.comp (algebraMap F K)) d := by
  rw [sq_delta_emb bK hb₁]; rfl

omit hb₀ in
include hb₁ in
/-- **(C), real form**: for a real place $w$ of $K$ over the (real) place $v$ of $F$,
$\delta_w^2=\sigma_v(d)$. -/
theorem embedding_of_isReal_delta_sq (v : {v : InfinitePlace F // v.IsReal}) (w : {w : InfinitePlace K // w.IsReal})
    (h : w.1.comap (algebraMap F K) = v.1) :
    embedding_of_isReal w.2 (bK 1) ^ 2 = embedding_of_isReal v.2 d := by
  apply Complex.ofReal_injective
  have hr : (w.1.comap (algebraMap F K)).IsReal := h ▸ v.2
  have h1 := embedding_delta_sq bK hb₁ w.1
  rw [← comap_embedding_of_isReal (algebraMap F K) hr, h] at h1
  push_cast
  rw [embedding_of_isReal_apply, embedding_of_isReal_apply]
  exact h1

omit hb₀ in
include hb₁ in
/-- Any place $w$ of $K$ over a real place $v$ of $F$ has $\delta_w^2=\sigma_v(d)$ (as complex numbers). -/
theorem embedding_delta_sq_of_comap_real (v : {v : InfinitePlace F // v.IsReal}) (w : InfinitePlace K)
    (h : w.comap (algebraMap F K) = v.1) :
    w.embedding (bK 1) ^ 2 = ((embedding_of_isReal v.2 d : ℝ) : ℂ) := by
  have hr : (w.comap (algebraMap F K)).IsReal := h ▸ v.2
  have h1 := embedding_delta_sq bK hb₁ w
  rw [← comap_embedding_of_isReal (algebraMap F K) hr, h] at h1
  rw [embedding_of_isReal_apply]
  exact h1

include hb₀ hb₁ in
/-- **Real place $v$ of $F$ with $\sigma_v(d)<0$**: exactly one place $w'$ of $K$ lies over $v$; it is complex
(ramified), with $\operatorname{Re}\delta_{w'}=0$ and $\delta_{w'}^2=\sigma_v(d)$; no real place lies over $v$. -/
theorem exists_unique_complex_place (v : {v : InfinitePlace F // v.IsReal}) (hneg : embedding_of_isReal v.2 d < 0) :
    ∃ w' : {w : InfinitePlace K // w.IsComplex}, w'.1.comap (algebraMap F K) = v.1 ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = w'.1) ∧
      (∀ w : {w : InfinitePlace K // w.IsReal}, w.1.comap (algebraMap F K) ≠ v.1) ∧
      (w'.1.embedding (bK 1)).re = 0 ∧
      w'.1.embedding (bK 1) ^ 2 = ((embedding_of_isReal v.2 d : ℝ) : ℂ) := by
  have hσ : ComplexEmbedding.IsReal v.1.embedding := isReal_iff.1 v.2
  obtain ⟨φ₀, hφ₀⟩ := exists_extension (K := K) v.1.embedding
  have hφ₀a : ∀ a : F, φ₀ (algebraMap F K a) = v.1.embedding a := fun a => congrArg (fun f : F →+* ℂ => f a) hφ₀
  have hsq : φ₀ (bK 1) ^ 2 = ((embedding_of_isReal v.2 d : ℝ) : ℂ) := by
    rw [sq_delta_emb bK hb₁, hφ₀a, embedding_of_isReal_apply]
  obtain ⟨hre, him⟩ := re_eq_zero_of_sq_neg _ _ hsq hneg
  have hnr : ¬ ComplexEmbedding.IsReal φ₀ := by
    intro hr
    apply him
    have := congrArg (fun f : K →+* ℂ => f (bK 1)) (ComplexEmbedding.isReal_iff.1 hr)
    exact Complex.conj_eq_iff_im.1 this
  have hw'c : (mk φ₀).IsComplex := isComplex_mk_iff.2 hnr
  have hcomap : (mk φ₀).comap (algebraMap F K) = v.1 := comap_mk_eq φ₀ v.1 hφ₀
  have huniq : ∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = mk φ₀ := by
    intro w hw
    obtain ⟨φ, hφ, rfl⟩ := exists_extension_of_place w v.1 hw
    rcases eq_or_comp_deltaConj bK hb₀ hb₁ φ φ₀ (fun a => by
      rw [hφ₀a]; exact congrArg (fun f : F →+* ℂ => f a) hφ) with h | h
    · rw [h]
    · rw [h, ← conjugate_eq_comp_deltaConj bK hb₀ hb₁ φ₀ (by rw [hφ₀]; exact hσ) hre, mk_conjugate_eq]
  refine ⟨⟨mk φ₀, hw'c⟩, hcomap, huniq, ?_, ?_, ?_⟩
  · intro w hw
    have := huniq w.1 hw
    exact (not_isReal_iff_isComplex.2 hw'c) (this ▸ w.2)
  · exact (re_eq_zero_of_sq_neg _ _ (embedding_delta_sq_of_comap_real bK hb₁ v (mk φ₀) hcomap) hneg).1
  · exact embedding_delta_sq_of_comap_real bK hb₁ v (mk φ₀) hcomap

include hb₀ hb₁ in
/-- **Complex place $v$ of $F$**: exactly two places of $K$ lie over $v$, both complex. -/
theorem exists_two_complex_places (v : {v : InfinitePlace F // v.IsComplex}) :
    ∃ w₁ w₂ : {w : InfinitePlace K // w.IsComplex}, w₁ ≠ w₂ ∧ w₁.1.comap (algebraMap F K) = v.1 ∧
      w₂.1.comap (algebraMap F K) = v.1 ∧
      (∀ w : InfinitePlace K, w.comap (algebraMap F K) = v.1 → w = w₁.1 ∨ w = w₂.1) := by
  have hσ : ¬ ComplexEmbedding.IsReal v.1.embedding := fun h =>
    (not_isReal_iff_isComplex.2 v.2) (isReal_iff.2 h)
  obtain ⟨φ₀, hφ₀⟩ := exists_extension (K := K) v.1.embedding
  have hφ₀a : ∀ a : F, φ₀ (algebraMap F K a) = v.1.embedding a := fun a => congrArg (fun f : F →+* ℂ => f a) hφ₀
  set τ := (deltaConj bK hb₀ hb₁).toRingHom
  have hnr : ∀ φ : K →+* ℂ, φ.comp (algebraMap F K) = v.1.embedding → ¬ ComplexEmbedding.IsReal φ := by
    intro φ hφ hr
    exact hσ (hφ ▸ hr.comp (algebraMap F K))
  have hc1 : ∀ a : F, (φ₀.comp τ) (algebraMap F K a) = v.1.embedding a := fun a => by
    rw [comp_deltaConj_apply_algebraMap bK hb₀ hb₁, hφ₀a]
  have hcomp1 : (φ₀.comp τ).comp (algebraMap F K) = v.1.embedding := by ext a; exact hc1 a
  have hd : v.1.embedding d ≠ 0 := (map_ne_zero _).2 (d_ne_zero bK hb₁)
  refine ⟨⟨mk φ₀, isComplex_mk_iff.2 (hnr φ₀ hφ₀)⟩, ⟨mk (φ₀.comp τ), isComplex_mk_iff.2 (hnr _ hcomp1)⟩, ?_,
    comap_mk_eq φ₀ v.1 hφ₀, comap_mk_eq _ v.1 hcomp1, ?_⟩
  · intro h
    have h' : mk φ₀ = mk (φ₀.comp τ) := congrArg Subtype.val h
    rcases mk_eq_iff.1 h' with h1 | h1
    · have h2 : φ₀ (bK 1) = (φ₀.comp τ) (bK 1) := congrArg (fun f : K →+* ℂ => f (bK 1)) h1
      rw [comp_deltaConj_delta bK hb₀ hb₁] at h2
      have h0 : φ₀ (bK 1) = 0 := by linear_combination h2 / 2
      apply hd
      rw [← hφ₀a, ← sq_delta_emb bK hb₁ φ₀, h0]; ring
    · apply hσ
      rw [ComplexEmbedding.isReal_iff]
      have h3 : ComplexEmbedding.conjugate (φ₀.comp (algebraMap F K)) = (φ₀.comp τ).comp (algebraMap F K) := by
        rw [← h1]; ext a; rfl
      rw [hφ₀, hcomp1] at h3
      exact h3
  · intro w hw
    obtain ⟨φ, hφ, rfl⟩ := exists_extension_of_place w v.1 hw
    rcases eq_or_comp_deltaConj bK hb₀ hb₁ φ φ₀ (fun a => by
      rw [hφ₀a]; exact congrArg (fun f : F →+* ℂ => f a) hφ) with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

end PartB

end

end QuadFormsKB.Tamagawa.Measure.Weil
