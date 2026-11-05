/-
# O'Meara §14, §15A–§15B: prolongation of a valuation to a finite separable extension (14:1, 15:1–15:3, 15:7)

**Setting.** $F$ is a field with a valuation $v$ (a Mathlib `AbsoluteValue F ℝ`, any spot $\mathfrak p$, possibly
trivial or archimedean), $E/F$ a finite separable extension of degree $n$. The completion $F_{\mathfrak p}$ is
Mathlib's `v.Completion`. The valuation induced on $F$ by a valuation $w$ of $E$ is Mathlib's `w.under F`; O'Meara's
$\mathfrak P \mid \mathfrak p$ is `(w.under F).IsEquiv v`, and in every spot $\mathfrak P \mid \mathfrak p$ there is a
valuation with `w.under F = v` exactly (for non-trivial $v$ by 12:7, `under_bijective`). For such $w$ Mathlib's
`AbsoluteValue.Completion.algebraOfLiesOver` makes the completion $E_{\mathfrak P}$ = `w.Completion` an algebra over
$F_{\mathfrak p}$; its image is the closure $F_{\mathfrak P}$ of $F$, and the map is O'Meara's
$I_{\mathfrak P}^{-1}\colon F_{\mathfrak p} \to F_{\mathfrak P}$.

**Defines**
* `localDegree w hw` (§15B, p. 31): the local degree $n(\mathfrak P|\mathfrak p) = [E_{\mathfrak P} : F_{\mathfrak P}]$;
* `localNorm w hw` (§15B, p. 32): the local norm $N_{\mathfrak P|\mathfrak p}\colon E_{\mathfrak P} \to F_{\mathfrak p}$,
  $N_{\mathfrak P|\mathfrak p}\alpha = I_{\mathfrak P}(N_{E_{\mathfrak P}/F_{\mathfrak P}}\alpha)$.

**Proves**
* `exists_unique_prolongation` (**14:1**, every complete valuation, including the trivial one; the formula
  $|\alpha| = |N_{E/F}\alpha|^{1/n}$ and completeness);
* `exists_under_eq` and `card_le_finrank` (§15A, p. 30: every spot $\mathfrak p$ is divisible by at least one and by
  at most $n$ spots of $E$), `exists_spotRepresentatives` (a finite set of representatives of the spots above
  $\mathfrak p$);
* `closure_range_eq_adjoin` (**15:1**), `isEquiv_comp_iff_minpoly_eq` (**15:2**);
* `spots_equiv_factors` (**15:7**): the spots $\mathfrak P \mid \mathfrak p$ correspond to the irreducible factors of
  $\operatorname{irr}(x, \theta, F)$ over $F_{\mathfrak p}$, the local degree being the degree of the factor;
* `sum_localDegree_eq_finrank`, `prod_localNorm_eq_norm` (**15:3**).
-/
import QuadFormsKB.Citation
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.FieldDivision
import QuadFormsKB.Literature.OMeara.Sec12C
import QuadFormsKB.Literature.OMeara.Sec14A

open Polynomial IntermediateField

namespace QuadFormsKB.OMeara

/-- A normed field is isometric to the `WithAbs` of its own absolute value. -/
private def withAbsIsometryEquiv (K : Type*) [NormedField K] :
    WithAbs (NormedField.toAbsoluteValue K) ≃ᵢ K :=
  { WithAbs.equiv _ with
    isometry_toFun := Isometry.of_dist_eq fun x y => by
      refine (dist_eq_norm _ _).trans ?_
      rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
      rfl }

private theorem completeSpace_withAbs_normedField (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue K)) :=
  (withAbsIsometryEquiv K).completeSpace_iff.2 ‹_›

private theorem exists_unique_prolongation_aux {K L : Type*} [NormedField K] [CompleteSpace K] [Field L]
    [Algebra K L] [FiniteDimensional K L] :
    ∃ w : AbsoluteValue L ℝ, (∀ x : K, w (algebraMap K L x) = ‖x‖) ∧
      (∀ a : L, w a = ‖Algebra.norm K a‖ ^ (1 / (Module.finrank K L : ℝ))) ∧ CompleteSpace (WithAbs w) ∧
      ∀ w' : AbsoluteValue L ℝ, (∀ x : K, w' (algebraMap K L x) = ‖x‖) → w' = w := by
  classical
  by_cases hna : IsNonarchimedean (NormedField.toAbsoluteValue K)
  · by_cases h2 : ∃ x : K, x ≠ 0 ∧ ‖x‖ ≠ 1
    · letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne h2
      haveI : IsUltrametricDist K :=
        IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm hna
      exact ⟨spectralAbs (K := K) (L := L), prolongation_formula (K := K) (L := L)⟩
    · push_neg at h2
      have h1 : ∀ x : K, x ≠ 0 → ‖x‖ = 1 := fun x hx => h2 x hx
      have hn : 0 < Module.finrank K L := Module.finrank_pos
      have hv : ∀ x : K, (AbsoluteValue.trivial : AbsoluteValue L ℝ) (algebraMap K L x) = ‖x‖ := by
        intro x
        by_cases hx : x = 0
        · simp [hx]
        · simp [AbsoluteValue.trivial, hx, h1 x hx]
      refine ⟨AbsoluteValue.trivial, hv, ?_, completeSpace_trivial, ?_⟩
      · intro a
        by_cases ha : a = 0
        · subst ha
          have : Algebra.norm K (0 : L) = 0 := Algebra.norm_zero (R := K) (S := L)
          rw [this]
          have : ((Module.finrank K L : ℝ))⁻¹ ≠ 0 := by positivity
          simp [AbsoluteValue.trivial, Real.zero_rpow this]
        · have hN : Algebra.norm K a ≠ 0 := by
            rw [Ne, Algebra.norm_eq_zero_iff]; exact ha
          simp [AbsoluteValue.trivial, ha, h1 _ hN]
      · intro w' hw'
        ext a
        by_cases ha : a = 0
        · simp [ha]
        · rw [eq_one_of_trivial_on_algebraic (F := K) w' (fun x hx => by rw [hw', h1 x hx]) a ha]
          simp [AbsoluteValue.trivial, ha]
  · haveI := completeSpace_withAbs_normedField K
    exact prolongation_formula_archimedean (NormedField.toAbsoluteValue K) hna

/-- **14:1 (Theorem), every complete valuation.** Let $K$ be complete under a valuation (a complete normed field; the
valuation may be trivial, non-archimedean or archimedean) and $L/K$ a finite extension of degree $n$. Then there is a
unique prolongation $w$ of the valuation to $L$; it is given by $w(\alpha) = \lVert N_{L/K}\alpha\rVert^{1/n}$, and $L$
is complete under it. (`prolongation_formula` and `prolongation_formula_archimedean` are the non-trivial
non-archimedean and the archimedean cases; for the trivial valuation the prolongation is trivial, 11:3.) -/
@[kb "omeara1963" "§14, 14:1, p. 28"]
theorem exists_unique_prolongation {K L : Type*} [NormedField K] [CompleteSpace K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    ∃! w : AbsoluteValue L ℝ, (∀ x : K, w (algebraMap K L x) = ‖x‖) ∧
      (∀ a : L, w a = ‖Algebra.norm K a‖ ^ (1 / (Module.finrank K L : ℝ))) ∧ CompleteSpace (WithAbs w) := by
  obtain ⟨w, h1, h2, h3, h4⟩ := exists_unique_prolongation_aux (K := K) (L := L)
  exact ⟨w, ⟨h1, h2, h3⟩, fun w' hw' => h4 w' hw'.1⟩

section Prolong

variable {K : Type*} [NormedField K] [CompleteSpace K]

/-- Two prolongations of the norm of a complete `K` to a finite extension agree. -/
private theorem prolong_unique {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (u u' : AbsoluteValue L ℝ) (hu : ∀ x : K, u (algebraMap K L x) = ‖x‖)
    (hu' : ∀ x : K, u' (algebraMap K L x) = ‖x‖) : u = u' := by
  obtain ⟨w, -, -, -, h4⟩ := exists_unique_prolongation_aux (K := K) (L := L)
  exact (h4 u hu).trans (h4 u' hu').symm

/-- A prolongation of the norm of a complete `K` to a finite extension is complete. -/
private theorem prolong_complete {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    (u : AbsoluteValue L ℝ) (hu : ∀ x : K, u (algebraMap K L x) = ‖x‖) : CompleteSpace (WithAbs u) := by
  obtain ⟨w, -, -, h3, h4⟩ := exists_unique_prolongation_aux (K := K) (L := L)
  rw [h4 u hu]
  exact h3

/-- A finite-dimensional intermediate field is closed for a prolongation of the norm of `K`. -/
private theorem isClosed_image_toAbs {Ω : Type*} [Field Ω] [Algebra K Ω] (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : K, u (algebraMap K Ω x) = ‖x‖) (Λ : IntermediateField K Ω) [FiniteDimensional K Λ] :
    IsClosed (WithAbs.toAbs u '' (Λ : Set Ω)) := by
  let u' : AbsoluteValue Λ ℝ := u.comp (f := Λ.val.toRingHom) Λ.val.injective
  have hu' : ∀ x : K, u' (algebraMap K Λ x) = ‖x‖ := fun x => hu x
  haveI : CompleteSpace (WithAbs u') := prolong_complete u' hu'
  let φ : WithAbs u' →+* WithAbs u := WithAbs.map u' u Λ.val.toRingHom
  have hφ : Isometry φ := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    simp only [WithAbs.norm_eq_apply_ofAbs]
    rfl
  have hrange : Set.range φ = WithAbs.toAbs u '' (Λ : Set Ω) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.ofAbs.1, x.ofAbs.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨WithAbs.toAbs u' ⟨z, hz⟩, rfl⟩
  rw [← hrange]
  exact hφ.isClosedEmbedding.isClosed_range

/-- Normed-field form of `isClosed_image_toAbs`. -/
private theorem isClosed_of_finiteDimensional_normed {Ω : Type*} [NormedField Ω] [Algebra K Ω]
    (hK : ∀ x : K, ‖algebraMap K Ω x‖ = ‖x‖) (Λ : IntermediateField K Ω) [FiniteDimensional K Λ] :
    IsClosed (Λ : Set Ω) := by
  have h := isClosed_image_toAbs (K := K) (NormedField.toAbsoluteValue Ω) hK Λ
  have h2 := h.preimage (withAbsIsometryEquiv Ω).symm.continuous
  convert h2 using 1
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe]
  exact ((WithAbs.toAbs_injective (NormedField.toAbsoluteValue Ω)).mem_set_image (a := x)).symm

end Prolong

section Extension

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)

/-- The *local degree* $n(\mathfrak P|\mathfrak p) = [E_{\mathfrak P} : F_{\mathfrak P}]$ of $E/F$ at a valuation $w$
of $E$ with $w|_F = v$ (§15B, p. 31): the dimension of the completion `w.Completion` over `v.Completion` (Mathlib's
`algebraOfLiesOver`; its image is the closure $F_{\mathfrak P}$ of $F$ in $E_{\mathfrak P}$). It depends only on the
spot $\mathfrak P$. -/
@[kb "omeara1963" "§15B, p. 31 (local degree n(P|p))"]
noncomputable def localDegree (w : AbsoluteValue E ℝ) (hw : w.under F = v) : ℕ :=
  haveI : w.LiesOver v := ⟨hw⟩
  letI := AbsoluteValue.Completion.algebraOfLiesOver v w
  Module.finrank v.Completion w.Completion

/-- The *local norm* $N_{\mathfrak P|\mathfrak p}\colon E_{\mathfrak P} \to F_{\mathfrak p}$ at a valuation $w$ of $E$
with $w|_F = v$ (§15B, p. 32): the norm of the finite extension `w.Completion` of `v.Completion`. -/
@[kb "omeara1963" "§15B, p. 32 (local norm N_{P|p})"]
noncomputable def localNorm (w : AbsoluteValue E ℝ) (hw : w.under F = v) : w.Completion →* v.Completion :=
  haveI : w.LiesOver v := ⟨hw⟩
  letI := AbsoluteValue.Completion.algebraOfLiesOver v w
  Algebra.norm v.Completion

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

section CompletionBlock

variable (w : AbsoluteValue E ℝ) [w.LiesOver v]

private theorem norm_algebraMap_completion (c : v.Completion) :
    ‖algebraMap v.Completion w.Completion c‖ = ‖c‖ := by
  have := (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w))
  rw [AddMonoidHomClass.isometry_iff_norm] at this
  rw [AbsoluteValue.Completion.algebraMap_apply v w]
  exact this c

private theorem norm_algebraMap_E (e : E) : ‖algebraMap E w.Completion e‖ = w e := by
  show ‖((WithAbs.toAbs w e : WithAbs w) : w.Completion)‖ = w e
  rw [UniformSpace.Completion.norm_coe]
  rfl

private theorem denseRange_algebraMap_E : DenseRange (algebraMap E w.Completion) := by
  have : DenseRange ((↑) : WithAbs w → w.Completion) := UniformSpace.Completion.denseRange_coe
  exact this.comp (WithAbs.toAbs_surjective w).denseRange (UniformSpace.Completion.continuous_coe _)

private theorem aeval_theta_completion (θ : E) :
    aeval (algebraMap E w.Completion θ) ((minpoly F θ).map (algebraMap F v.Completion)) = 0 := by
  rw [aeval_map_algebraMap v.Completion, aeval_algebraMap_apply, minpoly.aeval, map_zero]

/-- **The completion of `E` at `w` is `K(θ)`.** -/
private theorem adjoin_theta_eq_top {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    (v.Completion)⟮algebraMap E w.Completion θ⟯ = ⊤ := by
  set α := algebraMap E w.Completion θ with hα
  have hint : IsIntegral v.Completion α := by
    refine ⟨(minpoly F θ).map (algebraMap F v.Completion),
      (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_theta_completion v w θ
  haveI : FiniteDimensional v.Completion (v.Completion⟮α⟯) := adjoin.finiteDimensional hint
  have hclosed : IsClosed ((v.Completion⟮α⟯ : IntermediateField v.Completion w.Completion) :
      Set w.Completion) :=
    isClosed_of_finiteDimensional_normed (norm_algebraMap_completion v w) _
  have hsub : Set.range (algebraMap E w.Completion) ⊆
      ((v.Completion⟮α⟯ : IntermediateField v.Completion w.Completion) : Set w.Completion) := by
    rintro _ ⟨e, rfl⟩
    have he : e ∈ F⟮θ⟯ := hθ ▸ IntermediateField.mem_top
    have h1 : algebraMap E w.Completion e ∈
        (F⟮θ⟯).map (IsScalarTower.toAlgHom F E w.Completion) :=
      (IntermediateField.mem_map _).2 ⟨e, he, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : F⟮(IsScalarTower.toAlgHom F E w.Completion) θ⟯ ≤
        (v.Completion⟮α⟯).restrictScalars F :=
      IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.mem_adjoin_simple_self _ α)
    exact h2 h1
  have hdense := (denseRange_algebraMap_E w).closure_range
  have huniv : ((v.Completion⟮α⟯ : IntermediateField v.Completion w.Completion) : Set w.Completion)
      = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense]
    exact closure_minimal hsub hclosed
  rw [eq_top_iff]
  intro x _
  have : x ∈ ((v.Completion⟮α⟯ : IntermediateField v.Completion w.Completion) : Set w.Completion) :=
    huniv ▸ Set.mem_univ x
  exact this

/-- `[w.Completion : K] = deg (minpoly K θ)`. -/
private theorem finiteDimensional_completion {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    FiniteDimensional v.Completion w.Completion := by
  have hint : IsIntegral v.Completion (algebraMap E w.Completion θ) := by
    refine ⟨(minpoly F θ).map (algebraMap F v.Completion),
      (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_theta_completion v w θ
  have h := adjoin_theta_eq_top v w hθ
  haveI : FiniteDimensional v.Completion (v.Completion⟮algebraMap E w.Completion θ⟯) :=
    adjoin.finiteDimensional hint
  rw [h] at this
  exact (IntermediateField.topEquiv (F := v.Completion) (E := w.Completion)).toLinearEquiv.finiteDimensional

private theorem finrank_completion {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    Module.finrank v.Completion w.Completion =
      (minpoly v.Completion (algebraMap E w.Completion θ)).natDegree := by
  have hint : IsIntegral v.Completion (algebraMap E w.Completion θ) := by
    refine ⟨(minpoly F θ).map (algebraMap F v.Completion),
      (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _, ?_⟩
    rw [← aeval_def]
    exact aeval_theta_completion v w θ
  have h := adjoin_theta_eq_top v w hθ
  rw [← IntermediateField.adjoin.finrank hint, h, IntermediateField.finrank_top']

end CompletionBlock

section Algebraic

/-- `AdjoinRoot (minpoly K x) ≃ A` when `x` generates `A` over `K`. -/
private noncomputable def adjoinRootEquivOfTop {K A : Type*} [Field K] [Field A] [Algebra K A] {x : A}
    (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) : AdjoinRoot (minpoly K x) ≃ₐ[K] A :=
  (IntermediateField.adjoinRootEquivAdjoin K hint).trans
    ((IntermediateField.equivOfEq h).trans IntermediateField.topEquiv)

private theorem adjoinRootEquivOfTop_root {K A : Type*} [Field K] [Field A] [Algebra K A] {x : A}
    (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) :
    adjoinRootEquivOfTop hint h (AdjoinRoot.root (minpoly K x)) = x := by
  show IntermediateField.topEquiv ((IntermediateField.equivOfEq h)
    (IntermediateField.adjoinRootEquivAdjoin K hint (AdjoinRoot.root _))) = x
  rw [IntermediateField.adjoinRootEquivAdjoin_apply_root]
  rfl

private theorem algebraAdjoin_eq_top {K A : Type*} [Field K] [Field A] [Algebra K A] {x : A}
    (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) : Algebra.adjoin K {x} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, h]
  rfl

private theorem algHom_ext_of_top {K A B : Type*} [Field K] [Field A] [Algebra K A] [Semiring B]
    [Algebra K B] {x : A} (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) {σ τ : A →ₐ[K] B}
    (hx : σ x = τ x) : σ = τ :=
  AlgHom.ext_of_adjoin_eq_top (algebraAdjoin_eq_top hint h) (by
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact hx)

private theorem exists_algHom_of_root {K A Ω : Type*} [Field K] [Field A] [Algebra K A] [Field Ω]
    [Algebra K Ω] {x : A} (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) (r : Ω)
    (hr : aeval r (minpoly K x) = 0) : ∃ σ : A →ₐ[K] Ω, σ x = r :=
  ⟨(AdjoinRoot.liftAlgHom (minpoly K x) (Algebra.ofId K Ω) r hr).comp
      (adjoinRootEquivOfTop hint h).symm.toAlgHom, by
    have : (adjoinRootEquivOfTop hint h).symm x = AdjoinRoot.root (minpoly K x) := by
      rw [AlgEquiv.symm_apply_eq, adjoinRootEquivOfTop_root]
    show (AdjoinRoot.liftAlgHom (minpoly K x) (Algebra.ofId K Ω) r hr)
      ((adjoinRootEquivOfTop hint h).symm x) = r
    rw [this]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _⟩

private theorem mem_adjoin_simple_iff_aeval {K A : Type*} [Field K] [Field A] [Algebra K A] {a : A}
    (h : IsAlgebraic K a) (x : A) : x ∈ K⟮a⟯ ↔ ∃ q : K[X], aeval a q = x := by
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h,
    Algebra.adjoin_singleton_eq_range_aeval]
  rfl

private theorem exists_aeval_of_top {K A : Type*} [Field K] [Field A] [Algebra K A] {x : A}
    (hint : IsIntegral K x) (h : K⟮x⟯ = ⊤) (e : A) : ∃ p : K[X], aeval x p = e := by
  have he : e ∈ K⟮x⟯ := h ▸ IntermediateField.mem_top
  exact (mem_adjoin_simple_iff_aeval hint.isAlgebraic e).1 he

end Algebraic

section EqRed

variable (F) in
/-- Equivalent valuations of `E` inducing the same valuation on `F` coincide. -/
private theorem eq_of_isEquiv_of_under_eq (w w' : AbsoluteValue E ℝ) (h : w.IsEquiv w')
    (hw : w.under F = v) (hw' : w'.under F = v) : w = w' := by
  have hF : ∀ x : F, w (algebraMap F E x) = v x := fun x => DFunLike.congr_fun hw x
  have hF' : ∀ x : F, w' (algebraMap F E x) = v x := fun x => DFunLike.congr_fun hw' x
  by_cases hnt : ∃ x : F, x ≠ 0 ∧ v x ≠ 1
  · refine eq_of_isEquiv_of_eq_on_subfield w w' h (algebraMap F E).fieldRange ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [hF, hF']
    · obtain ⟨x, hx0, hx1⟩ := hnt
      exact ⟨algebraMap F E x, ⟨x, rfl⟩, by simpa using hx0, by rwa [hF]⟩
  · push Not at hnt
    ext a
    by_cases ha : a = 0
    · simp [ha]
    · rw [eq_one_of_trivial_on_algebraic (F := F) w (fun x hx => by rw [hF]; exact hnt x hx) a ha,
        eq_one_of_trivial_on_algebraic (F := F) w' (fun x hx => by rw [hF']; exact hnt x hx) a ha]

variable (F) in
/-- Every spot above `v` has a valuation inducing exactly `v`. -/
private theorem exists_under_eq_of_equiv (w : AbsoluteValue E ℝ) (h : (w.under F).IsEquiv v) :
    ∃ w' : AbsoluteValue E ℝ, w'.IsEquiv w ∧ w'.under F = v := by
  by_cases hnt : (w.under F).IsNontrivial
  · obtain ⟨⟨w', hw'⟩, hw'v⟩ := (under_bijective (F := F) w hnt).2 ⟨v, h.symm⟩
    exact ⟨w', hw', congrArg Subtype.val hw'v⟩
  · refine ⟨w, AbsoluteValue.IsEquiv.refl w, ?_⟩
    obtain ⟨c, hc, hcv⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
    have h1 := (AbsoluteValue.not_isNontrivial_iff _).1 hnt
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have h3 : v x = 1 := by
        rw [← congrFun hcv x]
        simp [h1 x hx]
      rw [h3]
      exact h1 x hx

end EqRed

section Embeddings

private theorem norm_algebraMap_F (x : F) : ‖algebraMap F v.Completion x‖ = v x := by
  show ‖((WithAbs.toAbs v x : WithAbs v) : v.Completion)‖ = v x
  rw [UniformSpace.Completion.norm_coe]
  rfl

private theorem exists_close (c : v.Completion) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : F, ‖c - algebraMap F v.Completion a‖ < δ := by
  have : DenseRange (algebraMap F v.Completion) := by
    have h : DenseRange ((↑) : WithAbs v → v.Completion) := UniformSpace.Completion.denseRange_coe
    exact h.comp (WithAbs.toAbs_surjective v).denseRange (UniformSpace.Completion.continuous_coe _)
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1 this c δ hδ
  exact ⟨a, by rwa [dist_eq_norm] at ha⟩

variable {Ω : Type*} [Field Ω] [Algebra v.Completion Ω] [Algebra F Ω]
  [IsScalarTower F v.Completion Ω]

private theorem exists_approx (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) (a b : Ω) :
    ∀ g : v.Completion[X], ∀ ε : ℝ, 0 < ε → ∃ p : F[X],
      u (aeval a g - aeval a p) < ε ∧ u (aeval b g - aeval b p) < ε := by
    intro g
    induction g using Polynomial.induction_on' with
    | add g₁ g₂ h₁ h₂ =>
      intro ε hε
      obtain ⟨p₁, h₁a, h₁b⟩ := h₁ (ε / 2) (by positivity)
      obtain ⟨p₂, h₂a, h₂b⟩ := h₂ (ε / 2) (by positivity)
      refine ⟨p₁ + p₂, ?_, ?_⟩
      · have : aeval a (g₁ + g₂) - aeval a (p₁ + p₂) =
            (aeval a g₁ - aeval a p₁) + (aeval a g₂ - aeval a p₂) := by
          simp only [map_add]; ring
        rw [this]
        calc _ ≤ _ := u.add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add h₁a h₂a
          _ = ε := by ring
      · have : aeval b (g₁ + g₂) - aeval b (p₁ + p₂) =
            (aeval b g₁ - aeval b p₁) + (aeval b g₂ - aeval b p₂) := by
          simp only [map_add]; ring
        rw [this]
        calc _ ≤ _ := u.add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add h₁b h₂b
          _ = ε := by ring
    | monomial n c =>
      intro ε hε
      set D : ℝ := 1 + u a ^ n + u b ^ n with hD
      have hDpos : 0 < D := by positivity
      obtain ⟨a', ha'⟩ := exists_close v c (div_pos hε hDpos)
      have hdiff : ∀ x : Ω, u (aeval x (monomial n c) - aeval x (monomial n a' : F[X])) =
          ‖c - algebraMap F v.Completion a'‖ * u x ^ n := by
        intro x
        have : aeval x (monomial n c) - aeval x (monomial n a' : F[X]) =
            algebraMap v.Completion Ω (c - algebraMap F v.Completion a') * x ^ n := by
          simp only [aeval_monomial, map_sub]
          rw [← IsScalarTower.algebraMap_apply F v.Completion Ω, sub_mul]
        rw [this, map_mul, hu, map_pow]
      have hlt : ‖c - algebraMap F v.Completion a'‖ * D < ε := by
        have := mul_lt_mul_of_pos_right ha' hDpos
        rwa [div_mul_cancel₀ _ hDpos.ne'] at this
      refine ⟨monomial n a', ?_, ?_⟩
      · rw [hdiff]
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hlt
        have : 0 ≤ u b ^ n := by positivity
        linarith
      · rw [hdiff]
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hlt
        have : 0 ≤ u a ^ n := by positivity
        linarith

/-- **Approximation.** If `u (p a) = u (p b)` for all `p ∈ F[X]` and `a` is a root of `g ∈ K[X]`, then
so is `b`. -/
private theorem aeval_approx (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) (a b : Ω)
    (hab : ∀ p : F[X], u (aeval a p) = u (aeval b p)) (g : v.Completion[X])
    (hg : aeval a g = 0) : aeval b g = 0 := by
  have key := exists_approx v u hu a b
  have hnorm : ∀ ε : ℝ, 0 < ε → u (aeval b g) ≤ 2 * ε := by
    intro ε hε
    obtain ⟨p, hpa, hpb⟩ := key g ε hε
    have h1 : u (aeval b g) ≤ u (aeval b g - aeval b p) + u (aeval b p) := by
      calc u (aeval b g) = u ((aeval b g - aeval b p) + aeval b p) := by ring_nf
        _ ≤ _ := u.add_le _ _
    rw [← hab p] at h1
    rw [hg, zero_sub, map_neg_eq_map] at hpa
    linarith
  have h0 : u (aeval b g) ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hnorm (ε / 2) (by positivity)
    linarith
  exact u.eq_zero.1 (le_antisymm h0 (u.nonneg _))

variable [FiniteDimensional v.Completion Ω]

private theorem minpoly_eq_of_eq {θ : E} (hθ : F⟮θ⟯ = ⊤) (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) (σ τ : E →ₐ[F] Ω)
    (h : ∀ e, u (σ e) = u (τ e)) : minpoly v.Completion (σ θ) = minpoly v.Completion (τ θ) := by
  have hroot : aeval (τ θ) (minpoly v.Completion (σ θ)) = 0 := by
    refine aeval_approx v u hu (σ θ) (τ θ) (fun p => ?_) _ (minpoly.aeval _ _)
    rw [aeval_algHom_apply, aeval_algHom_apply]
    exact h _
  exact minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
    hroot (minpoly.monic (Algebra.IsIntegral.isIntegral _))

private theorem eq_of_minpoly_eq {θ : E} (hθ : F⟮θ⟯ = ⊤) (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) (σ τ : E →ₐ[F] Ω)
    (h : minpoly v.Completion (σ θ) = minpoly v.Completion (τ θ)) : ∀ e, u (σ e) = u (τ e) := by
  intro e
  set g := minpoly v.Completion (σ θ) with hg
  have hσ : IsIntegral v.Completion (σ θ) := Algebra.IsIntegral.isIntegral _
  haveI : Fact (Irreducible g) := ⟨minpoly.irreducible hσ⟩
  have hgne : g ≠ 0 := (minpoly.monic hσ).ne_zero
  haveI : FiniteDimensional v.Completion (AdjoinRoot g) := (AdjoinRoot.powerBasis hgne).finite
  let ισ : AdjoinRoot g →ₐ[v.Completion] Ω :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId v.Completion Ω) (σ θ) (minpoly.aeval _ _)
  let ιτ : AdjoinRoot g →ₐ[v.Completion] Ω :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId v.Completion Ω) (τ θ) (by
      have := minpoly.aeval v.Completion (τ θ)
      rw [← h] at this
      exact this)
  have huσ := prolong_unique (K := v.Completion) (u.comp (f := ισ.toRingHom) ισ.toRingHom.injective)
    (u.comp (f := ιτ.toRingHom) ιτ.toRingHom.injective)
    (fun x => by
      show u (ισ (algebraMap v.Completion (AdjoinRoot g) x)) = ‖x‖
      rw [ισ.commutes]; exact hu x)
    (fun x => by
      show u (ιτ (algebraMap v.Completion (AdjoinRoot g) x)) = ‖x‖
      rw [ιτ.commutes]; exact hu x)
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have he : e ∈ Algebra.adjoin F {θ} := by rw [algebraAdjoin_eq_top hint hθ]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨p, hp⟩ := he
  have hp' : aeval θ p = e := hp
  subst hp'
  have key : ∀ (ι : AdjoinRoot g →ₐ[v.Completion] Ω) (y : E →ₐ[F] Ω), ι (AdjoinRoot.root g) = y θ →
      y (aeval θ p) = ι (aeval (AdjoinRoot.root g) (p.map (algebraMap F v.Completion))) := by
    intro ι y hι
    calc y (aeval θ p) = aeval (y θ) p := (aeval_algHom_apply y θ p).symm
      _ = aeval (y θ) (p.map (algebraMap F v.Completion)) :=
          (aeval_map_algebraMap v.Completion _ _).symm
      _ = aeval (ι (AdjoinRoot.root g)) (p.map (algebraMap F v.Completion)) := by rw [hι]
      _ = _ := aeval_algHom_apply ι _ _
  rw [key ισ σ (AdjoinRoot.liftAlgHom_root _ _ _ _), key ιτ τ (AdjoinRoot.liftAlgHom_root _ _ _ _)]
  exact DFunLike.congr_fun huσ _

private theorem comp_under_eq (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) (σ : E →ₐ[F] Ω) :
    (u.comp (f := σ.toRingHom) σ.injective).under F = v := by
  ext x
  show u (σ (algebraMap F E x)) = v x
  rw [σ.commutes, IsScalarTower.algebraMap_apply F v.Completion Ω, hu, norm_algebraMap_F]

end Embeddings

section Classification

private theorem isIntegral_theta (w : AbsoluteValue E ℝ) [w.LiesOver v] (θ : E) :
    IsIntegral v.Completion (algebraMap E w.Completion θ) :=
  ⟨(minpoly F θ).map (algebraMap F v.Completion),
    (minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _, by
      rw [← aeval_def]; exact aeval_theta_completion v w θ⟩

private theorem exists_root_of_dvd {Ω : Type*} [Field Ω] [Algebra v.Completion Ω] {θ : E}
    (hsplit : (((minpoly F θ).map (algebraMap F v.Completion)).map
      (algebraMap v.Completion Ω)).Splits) (g : v.Completion[X])
    (hg : g ∣ (minpoly F θ).map (algebraMap F v.Completion)) (hg0 : 0 < g.natDegree) :
    ∃ r : Ω, aeval r g = 0 := by
  have hfne : ((minpoly F θ).map (algebraMap F v.Completion)).map (algebraMap v.Completion Ω) ≠ 0 :=
    (((minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _).map _).ne_zero
  have hs : (g.map (algebraMap v.Completion Ω)).Splits :=
    Splits.of_dvd hsplit hfne (Polynomial.map_dvd _ hg)
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero (by
    rw [degree_map]; exact (natDegree_pos_iff_degree_pos.1 hg0).ne')
  exact ⟨r, by rwa [aeval_def, eval₂_eq_eval_map]⟩

variable {Ω : Type*} [Field Ω] [Algebra v.Completion Ω] [Algebra F Ω] [IsScalarTower F v.Completion Ω]
  [FiniteDimensional v.Completion Ω]

/-- Every valuation of `E` inducing `v` is the pull-back of the prolongation to `Ω` along an
`F`-embedding, and the embedding sends `θ` to a conjugate of the image of `θ` in the completion. -/
private theorem exists_embedding_of_lies (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) {θ : E} (hθ : F⟮θ⟯ = ⊤)
    (hsplit : (((minpoly F θ).map (algebraMap F v.Completion)).map
      (algebraMap v.Completion Ω)).Splits) (w : AbsoluteValue E ℝ) [w.LiesOver v] :
    ∃ σ : E →ₐ[F] Ω, u.comp (f := σ.toRingHom) σ.injective = w ∧
      minpoly v.Completion (σ θ) = minpoly v.Completion (algebraMap E w.Completion θ) := by
  have hα := isIntegral_theta v w θ
  have htop := adjoin_theta_eq_top v w hθ
  haveI := finiteDimensional_completion v w hθ
  have hdvd : minpoly v.Completion (algebraMap E w.Completion θ) ∣
      (minpoly F θ).map (algebraMap F v.Completion) :=
    minpoly.dvd _ _ (aeval_theta_completion v w θ)
  obtain ⟨r, hr⟩ := exists_root_of_dvd v hsplit _ hdvd (minpoly.natDegree_pos hα)
  obtain ⟨τ, hτ⟩ := exists_algHom_of_root hα htop r hr
  have hnorm : u.comp (f := τ.toRingHom) τ.toRingHom.injective =
      NormedField.toAbsoluteValue w.Completion := by
    refine prolong_unique (K := v.Completion) _ _ (fun x => ?_) (fun x => ?_)
    · show u (τ (algebraMap v.Completion w.Completion x)) = ‖x‖
      rw [τ.commutes]; exact hu x
    · exact norm_algebraMap_completion v w x
  refine ⟨(τ.restrictScalars F).comp (IsScalarTower.toAlgHom F E w.Completion), ?_, ?_⟩
  · ext e
    show u (τ (algebraMap E w.Completion e)) = w e
    have := DFunLike.congr_fun hnorm (algebraMap E w.Completion e)
    refine this.trans ?_
    exact norm_algebraMap_E w e
  · show minpoly v.Completion (τ (algebraMap E w.Completion θ)) = _
    exact minpoly.algHom_eq τ τ.toRingHom.injective _

end Classification

section SplitSection

/-- The splitting field of `f_K = minpoly F θ` over the completion `K = F_𝔭`. -/
private def SplitΩ (θ : E) : Type _ := SplittingField ((minpoly F θ).map (algebraMap F v.Completion))

private noncomputable instance (θ : E) : Field (SplitΩ v θ) :=
  inferInstanceAs (Field (SplittingField _))
private noncomputable instance (θ : E) : Algebra v.Completion (SplitΩ v θ) :=
  inferInstanceAs (Algebra v.Completion (SplittingField _))
private noncomputable instance (θ : E) : Algebra F (SplitΩ v θ) :=
  inferInstanceAs (Algebra F (SplittingField ((minpoly F θ).map (algebraMap F v.Completion))))
private instance (θ : E) : IsScalarTower F v.Completion (SplitΩ v θ) :=
  inferInstanceAs (IsScalarTower F v.Completion
    (SplittingField ((minpoly F θ).map (algebraMap F v.Completion))))
private instance (θ : E) : FiniteDimensional v.Completion (SplitΩ v θ) :=
  inferInstanceAs (FiniteDimensional v.Completion (SplittingField _))

private theorem splitΩ_splits (θ : E) :
    (((minpoly F θ).map (algebraMap F v.Completion)).map
      (algebraMap v.Completion (SplitΩ v θ))).Splits :=
  SplittingField.splits _

private noncomputable def uΩ (θ : E) : AbsoluteValue (SplitΩ v θ) ℝ :=
  (exists_unique_prolongation_aux (K := v.Completion) (L := SplitΩ v θ)).choose

private theorem uΩ_spec (θ : E) :
    ∀ x : v.Completion, uΩ v θ (algebraMap v.Completion (SplitΩ v θ) x) = ‖x‖ :=
  (exists_unique_prolongation_aux (K := v.Completion) (L := SplitΩ v θ)).choose_spec.1

/-- The minimal polynomial over `K = F_𝔭` of the image of `θ` in the completion at `w`. -/
private noncomputable def Gfac (θ : E) (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    v.Completion[X] :=
  haveI : w.LiesOver v := ⟨hw⟩
  minpoly v.Completion (algebraMap E w.Completion θ)

open Classical in
private theorem spots_aux {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    (∀ (w : AbsoluteValue E ℝ) (hw : w.under F = v), Gfac v θ w hw ∈
      UniqueFactorizationMonoid.normalizedFactors ((minpoly F θ).map (algebraMap F v.Completion))) ∧
    (∀ g ∈ UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion)),
      ∃ (w : AbsoluteValue E ℝ) (hw : w.under F = v), Gfac v θ w hw = g) ∧
    (∀ (w w' : AbsoluteValue E ℝ) (hw : w.under F = v) (hw' : w'.under F = v),
      Gfac v θ w hw = Gfac v θ w' hw' → w = w') := by
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have hfne : (minpoly F θ).map (algebraMap F v.Completion) ≠ 0 :=
    ((minpoly.monic hint).map _).ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    haveI : w.LiesOver v := ⟨hw⟩
    have hα := isIntegral_theta v w θ
    exact (Polynomial.mem_normalizedFactors_iff hfne).2 ⟨minpoly.irreducible hα, minpoly.monic hα,
      minpoly.dvd _ _ (aeval_theta_completion v w θ)⟩
  · intro g hg
    obtain ⟨hirr, hmon, hdvd⟩ := (Polynomial.mem_normalizedFactors_iff hfne).1 hg
    obtain ⟨r, hr⟩ := exists_root_of_dvd v (splitΩ_splits v θ) g hdvd hirr.natDegree_pos
    have hrf : aeval r (minpoly F θ) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [← aeval_map_algebraMap v.Completion, hc, map_mul, hr, zero_mul]
    obtain ⟨σ, hσ⟩ := exists_algHom_of_root hint hθ r hrf
    have hu := uΩ_spec v θ
    have hwσ : ((uΩ v θ).comp (f := σ.toRingHom) σ.injective).under F = v :=
      comp_under_eq v (uΩ v θ) hu σ
    refine ⟨_, hwσ, ?_⟩
    haveI : ((uΩ v θ).comp (f := σ.toRingHom) σ.injective).LiesOver v := ⟨hwσ⟩
    obtain ⟨σ', hσ'w, hσ'⟩ := exists_embedding_of_lies v (uΩ v θ) hu hθ (splitΩ_splits v θ)
      ((uΩ v θ).comp (f := σ.toRingHom) σ.injective)
    have h1 : minpoly v.Completion (σ' θ) = minpoly v.Completion (σ θ) :=
      minpoly_eq_of_eq v hθ (uΩ v θ) hu σ' σ fun e => by
        have := DFunLike.congr_fun hσ'w e
        exact this
    have h2 : minpoly v.Completion r = g :=
      (minpoly.eq_of_irreducible_of_monic hirr hr hmon).symm
    show minpoly v.Completion (algebraMap E _ θ) = g
    rw [← hσ', h1, hσ, h2]
  · intro w w' hw hw' h
    haveI : w.LiesOver v := ⟨hw⟩
    haveI : w'.LiesOver v := ⟨hw'⟩
    have hu := uΩ_spec v θ
    obtain ⟨σ, hσw, hσ⟩ := exists_embedding_of_lies v (uΩ v θ) hu hθ (splitΩ_splits v θ) w
    obtain ⟨σ', hσ'w, hσ'⟩ := exists_embedding_of_lies v (uΩ v θ) hu hθ (splitΩ_splits v θ) w'
    have h1 : minpoly v.Completion (σ θ) = minpoly v.Completion (σ' θ) := by
      rw [hσ, hσ']; exact h
    rw [← hσw, ← hσ'w]
    ext e
    exact eq_of_minpoly_eq v hθ (uΩ v θ) hu σ σ' h1 e

end SplitSection

section Factors

private theorem natDegree_minpoly_eq_finrank {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    (minpoly F θ).natDegree = Module.finrank F E := by
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral θ), hθ,
    IntermediateField.finrank_top']

private theorem Gfac_congr {θ : E} {w w' : AbsoluteValue E ℝ} (h : w = w') (hw : w.under F = v)
    (hw' : w'.under F = v) : Gfac v θ w hw = Gfac v θ w' hw' := by
  subst h; rfl

private theorem localDegree_eq {θ : E} (hθ : F⟮θ⟯ = ⊤) (w : AbsoluteValue E ℝ)
    (hw : w.under F = v) : localDegree v w hw = (Gfac v θ w hw).natDegree := by
  haveI : w.LiesOver v := ⟨hw⟩
  exact finrank_completion v w hθ

open Classical in
private theorem sum_natDegree_factors {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    ((UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion))).map Polynomial.natDegree).sum =
      Module.finrank F E := by
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have hm : ((minpoly F θ).map (algebraMap F v.Completion)).Monic := (minpoly.monic hint).map _
  have hne := hm.ne_zero
  have hfac : ∀ g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion)), g.Monic :=
    fun g hg => ((Polynomial.mem_normalizedFactors_iff hne).1 hg).2.1
  have hprod : (UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion))).prod =
      (minpoly F θ).map (algebraMap F v.Completion) := by
    refine eq_of_monic_of_associated ?_ hm (UniqueFactorizationMonoid.prod_normalizedFactors hne)
    simpa using monic_multiset_prod_of_monic _ id (by simpa using hfac)
  rw [← natDegree_multiset_prod_of_monic _ hfac, hprod, natDegree_map,
    natDegree_minpoly_eq_finrank hθ]

open Classical in
private theorem nodup_factors {θ : E} :
    (UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion))).Nodup := by
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have hsep : (minpoly F θ).Separable := Algebra.IsSeparable.isSeparable F θ
  exact (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    ((minpoly.monic hint).map _).ne_zero).1 (hsep.map).squarefree

open Classical in
private theorem sum_natDegree_toFinset {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    ∑ g ∈ (UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion))).toFinset, g.natDegree =
      Module.finrank F E := by
  rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
    Multiset.dedup_eq_self.2 (nodup_factors v), sum_natDegree_factors v hθ]

end Factors

open Classical in
private theorem spots_core {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    ∃ W : {g : v.Completion[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion))} → AbsoluteValue E ℝ,
      ∃ hW : ∀ g, (W g).under F = v,
        (∀ g g', (W g).IsEquiv (W g') ↔ g = g') ∧
        (∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃ g, (W g).IsEquiv w) ∧
        ∀ g, localDegree v (W g) (hW g) = (g : v.Completion[X]).natDegree := by
  obtain ⟨hA3, hA1, hA2⟩ := spots_aux v hθ
  have A1 : ∀ g : {g : v.Completion[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion))},
      ∃ (w : AbsoluteValue E ℝ) (hw : w.under F = v), Gfac v θ w hw = g.1 :=
    fun g => hA1 g.1 g.2
  choose W hW hG using A1
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · intro g g'
    constructor
    · intro h
      have h1 : W g = W g' := eq_of_isEquiv_of_under_eq F v _ _ h (hW g) (hW g')
      apply Subtype.ext
      rw [← hG g, ← hG g']
      exact Gfac_congr v h1 _ _
    · rintro rfl
      exact AbsoluteValue.IsEquiv.refl _
  · intro w hw
    obtain ⟨w1, hw1, hw1u⟩ := exists_under_eq_of_equiv F v w hw
    refine ⟨⟨Gfac v θ w1 hw1u, hA3 w1 hw1u⟩, ?_⟩
    have : W ⟨Gfac v θ w1 hw1u, hA3 w1 hw1u⟩ = w1 :=
      hA2 _ _ (hW _) hw1u (hG _)
    rw [this]
    exact hw1
  · intro g
    rw [localDegree_eq v hθ _ (hW g), hG g]

section NormBlock

private theorem isSeparable_completion {θ : E} (hθ : F⟮θ⟯ = ⊤) (w : AbsoluteValue E ℝ)
    [w.LiesOver v] : Algebra.IsSeparable v.Completion w.Completion := by
  have htop := adjoin_theta_eq_top v w hθ
  have hsepf0 : (minpoly F θ).Separable := Algebra.IsSeparable.isSeparable F θ
  have hsepf : ((minpoly F θ).map (algebraMap F v.Completion)).Separable := hsepf0.map
  have hsep : IsSeparable v.Completion (algebraMap E w.Completion θ) :=
    hsepf.of_dvd (minpoly.dvd _ _ (aeval_theta_completion v w θ))
  haveI : Algebra.IsSeparable v.Completion (v.Completion⟮algebraMap E w.Completion θ⟯) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  exact ⟨fun x => isSeparable_of_mem_isSeparable v.Completion w.Completion
    (L := v.Completion⟮algebraMap E w.Completion θ⟯) (by rw [htop]; exact IntermediateField.mem_top)⟩

open Classical in
/-- The local norm, mapped into an algebraically closed extension, is the product of the images of
`α` under the embeddings of `E` lying over the spot of `w`. -/
private theorem norm_local_eq_prod {θ : E} (hθ : F⟮θ⟯ = ⊤) (Ω : Type*) [Field Ω] [IsAlgClosed Ω]
    [Algebra v.Completion Ω] [Algebra F Ω] [IsScalarTower F v.Completion Ω]
    (w : AbsoluteValue E ℝ) [w.LiesOver v] (α : E) :
    algebraMap v.Completion Ω (Algebra.norm v.Completion (algebraMap E w.Completion α)) =
      ∏ σ ∈ Finset.univ.filter (fun σ : E →ₐ[F] Ω => minpoly v.Completion (σ θ) =
        minpoly v.Completion (algebraMap E w.Completion θ)), σ α := by
  have hα := isIntegral_theta v w θ
  have htop := adjoin_theta_eq_top v w hθ
  haveI := finiteDimensional_completion v w hθ
  haveI := isSeparable_completion v hθ w
  rw [Algebra.norm_eq_prod_embeddings (K := v.Completion) Ω]
  refine Finset.prod_bij
    (fun τ _ => (τ.restrictScalars F).comp (IsScalarTower.toAlgHom F E w.Completion)) ?_ ?_ ?_ ?_
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show minpoly v.Completion (τ (algebraMap E w.Completion θ)) = _
    exact minpoly.algHom_eq τ τ.toRingHom.injective _
  · intro τ _ τ' _ h
    apply algHom_ext_of_top hα htop
    exact DFunLike.congr_fun h θ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hr : aeval (σ θ) (minpoly v.Completion (algebraMap E w.Completion θ)) = 0 := by
      rw [← hσ]; exact minpoly.aeval _ _
    obtain ⟨τ, hτ⟩ := exists_algHom_of_root hα htop (σ θ) hr
    refine ⟨τ, Finset.mem_univ _, ?_⟩
    apply algHom_ext_of_top (Algebra.IsIntegral.isIntegral θ) hθ
    exact hτ
  · intro τ _
    rfl

end NormBlock

/-- **Every spot of $F$ is divisible by a spot of $E$** (§15A, p. 30): there is a valuation $w$ of $E$ with
$w|_F = v$. -/
@[kb "omeara1963" "§15A, p. 30 (every spot on F is divisible by at least one spot on E)"]
theorem exists_under_eq : ∃ w : AbsoluteValue E ℝ, w.under F = v := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨W, hW, -⟩ := spots_core v hθ
  have hsum := sum_natDegree_factors v hθ
  have hpos : 0 < Module.finrank F E := Module.finrank_pos
  obtain ⟨g, hg⟩ : ∃ g, g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion)) := by
    by_contra hc
    push Not at hc
    rw [Multiset.eq_zero_of_forall_notMem hc] at hsum
    simp at hsum
    omega
  exact ⟨W ⟨g, hg⟩, hW _⟩

/-- **At most $n$ spots of $E$ divide $\mathfrak p$** (§15A, p. 31): pairwise inequivalent valuations of $E$ inducing
the spot of $v$ are at most $[E:F]$ in number. -/
@[kb "omeara1963" "§15A, p. 31 (at most n spots on E divide p)"]
theorem card_le_finrank (s : Finset (AbsoluteValue E ℝ)) (hs : ∀ w ∈ s, (w.under F).IsEquiv v)
    (hp : (s : Set (AbsoluteValue E ℝ)).Pairwise fun w w' => ¬ w.IsEquiv w') :
    s.card ≤ Module.finrank F E := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨hA3, hA1, hA2⟩ := spots_aux v hθ
  have hex : ∀ w ∈ s, ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly F θ).map (algebraMap F v.Completion)),
      ∃ (w' : AbsoluteValue E ℝ) (hw' : w'.under F = v), w'.IsEquiv w ∧ Gfac v θ w' hw' = g := by
    intro w hw
    obtain ⟨w', hw'e, hw'u⟩ := exists_under_eq_of_equiv F v w (hs w hw)
    exact ⟨_, hA3 w' hw'u, w', hw'u, hw'e, rfl⟩
  choose! φ hφmem hφ using hex
  have hinj : Set.InjOn φ s := by
    intro w hw w' hw' h
    obtain ⟨a, ha, hae, haG⟩ := hφ w hw
    obtain ⟨b, hb, hbe, hbG⟩ := hφ w' hw'
    have hab : a = b := hA2 a b ha hb (haG.trans (h.trans hbG.symm))
    by_contra hne
    apply hp hw hw' hne
    subst hab
    exact hae.symm.trans hbe
  calc s.card ≤ (UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion))).toFinset.card :=
        Finset.card_le_card_of_injOn φ (fun w hw => Multiset.mem_toFinset.2 (hφmem w hw)) hinj
    _ ≤ Multiset.card (UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion))) := Multiset.toFinset_card_le _
    _ ≤ Module.finrank F E := by
        rw [← sum_natDegree_factors v hθ]
        have := Multiset.card_nsmul_le_sum (s := (UniqueFactorizationMonoid.normalizedFactors
          ((minpoly F θ).map (algebraMap F v.Completion))).map Polynomial.natDegree) (a := 1) (by
            intro x hx
            obtain ⟨g, hg, rfl⟩ := Multiset.mem_map.1 hx
            have hne : ((minpoly F θ).map (algebraMap F v.Completion)) ≠ 0 :=
              ((minpoly.monic (Algebra.IsIntegral.isIntegral θ)).map _).ne_zero
            exact ((Polynomial.mem_normalizedFactors_iff hne).1 hg).1.natDegree_pos)
        simpa using this

/-- **A set of representatives of the spots above $\mathfrak p$** (§15A): a finite set $T$ of valuations of $E$, each
with $w|_F = v$, containing exactly one valuation of each spot $\mathfrak P \mid \mathfrak p$. -/
theorem exists_spotRepresentatives :
    ∃ T : Finset (AbsoluteValue E ℝ), (∀ w ∈ T, w.under F = v) ∧
      ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨W, hW, hiff, hcov, -⟩ := spots_core v hθ
  refine ⟨Finset.univ.image W, ?_, ?_⟩
  · intro w hw
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hw
    exact hW g
  · intro w hw
    obtain ⟨g, hg⟩ := hcov w hw
    refine ⟨W g, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hg⟩, ?_⟩
    rintro y ⟨hy, hye⟩
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.1 hy
    have : g' = g := (hiff g' g).1 (hye.trans hg.symm)
    rw [this]

/-- **15:1 (Example).** Let $\Omega$ be a finite extension of $F_{\mathfrak p}$ with a valuation $u$ prolonging that
of $F_{\mathfrak p}$, $\theta$ a primitive element of $E/F$ and $\sigma\colon E \to \Omega$ an $F$-embedding. Then the
closure of $\sigma E$ in $\Omega$ is $F_{\mathfrak p}(\sigma\theta)$. -/
@[kb "omeara1963" "§15A, 15:1, p. 31"]
theorem closure_range_eq_adjoin {Ω : Type*} [Field Ω] [Algebra v.Completion Ω] [Algebra F Ω]
    [IsScalarTower F v.Completion Ω] [FiniteDimensional v.Completion Ω] (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) {θ : E} (hθ : F⟮θ⟯ = ⊤)
    (σ : E →ₐ[F] Ω) :
    closure (WithAbs.toAbs u '' Set.range σ) =
      WithAbs.toAbs u '' ((v.Completion⟮σ θ⟯ : IntermediateField v.Completion Ω) : Set Ω) := by
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have haK : IsIntegral v.Completion (σ θ) := Algebra.IsIntegral.isIntegral _
  haveI : FiniteDimensional v.Completion (v.Completion⟮σ θ⟯) := adjoin.finiteDimensional haK
  have hclosed := isClosed_image_toAbs u hu (v.Completion⟮σ θ⟯)
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ hclosed
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    refine ⟨σ e, ?_, rfl⟩
    obtain ⟨p, rfl⟩ := exists_aeval_of_top hint hθ e
    rw [← aeval_algHom_apply, ← aeval_map_algebraMap v.Completion]
    exact (mem_adjoin_simple_iff_aeval haK.isAlgebraic _).2 ⟨_, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨q, rfl⟩ := (mem_adjoin_simple_iff_aeval haK.isAlgebraic x).1 hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨p, hp, -⟩ := exists_approx v u hu (σ θ) (σ θ) q ε hε
    refine ⟨WithAbs.toAbs u (σ (aeval θ p)), ⟨σ (aeval θ p), ⟨_, rfl⟩, rfl⟩, ?_⟩
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
    rw [← aeval_algHom_apply]
    exact hp

/-- **15:2.** In the situation of 15:1, two $F$-embeddings $\sigma, \tau\colon E \to \Omega$ give the same spot of $E$
(the valuations $u\circ\sigma$ and $u\circ\tau$ are equivalent) if and only if $\sigma\theta$ and $\tau\theta$ are
conjugate over $F_{\mathfrak p}$ (have the same minimal polynomial). -/
@[kb "omeara1963" "§15B, 15:2, p. 31"]
theorem isEquiv_comp_iff_minpoly_eq {Ω : Type*} [Field Ω] [Algebra v.Completion Ω] [Algebra F Ω]
    [IsScalarTower F v.Completion Ω] [FiniteDimensional v.Completion Ω] (u : AbsoluteValue Ω ℝ)
    (hu : ∀ x : v.Completion, u (algebraMap v.Completion Ω x) = ‖x‖) {θ : E} (hθ : F⟮θ⟯ = ⊤)
    (σ τ : E →ₐ[F] Ω) :
    (u.comp (f := σ.toRingHom) σ.injective).IsEquiv (u.comp (f := τ.toRingHom) τ.injective) ↔
      minpoly v.Completion (σ θ) = minpoly v.Completion (τ θ) := by
  constructor
  · intro h
    have := eq_of_isEquiv_of_under_eq F v _ _ h (comp_under_eq v u hu σ) (comp_under_eq v u hu τ)
    exact minpoly_eq_of_eq v hθ u hu σ τ fun e => DFunLike.congr_fun this e
  · intro h
    have : u.comp (f := σ.toRingHom) σ.injective = u.comp (f := τ.toRingHom) τ.injective := by
      ext e
      exact eq_of_minpoly_eq v hθ u hu σ τ h e
    rw [this]
    exact AbsoluteValue.IsEquiv.refl _

open Classical in
/-- **15:7 (Example).** Let $\theta$ be a primitive element of $E/F$ and $f = \operatorname{irr}(x, \theta, F)$. Then
the spots $\mathfrak P \mid \mathfrak p$ of $E$ correspond bijectively to the monic irreducible factors $f_i$ of $f$
over $F_{\mathfrak p}$ (which are distinct, $f$ being separable), and the local degree at the spot corresponding to
$f_i$ is $\deg f_i$. Here: there is a valuation $W(g)$ with $W(g)|_F = v$ for each factor $g$, the spots of distinct
factors are distinct, every spot above $\mathfrak p$ is one of them, and $n(W(g)|\mathfrak p) = \deg g$. -/
@[kb "omeara1963" "§15B, 15:7, p. 34"]
theorem spots_equiv_factors {θ : E} (hθ : F⟮θ⟯ = ⊤) :
    ∃ W : {g : v.Completion[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors ((minpoly F θ).map (algebraMap F v.Completion))} →
        AbsoluteValue E ℝ,
      ∃ hW : ∀ g, (W g).under F = v,
        (∀ g g', (W g).IsEquiv (W g') ↔ g = g') ∧
        (∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃ g, (W g).IsEquiv w) ∧
        ∀ g, localDegree v (W g) (hW g) = (g : v.Completion[X]).natDegree :=
  spots_core v hθ

/-- **15:3 (Theorem) (1).** Let $E/F$ be finite separable of degree $n$ and $T$ a set of representatives of the spots
$\mathfrak P \mid \mathfrak p$ (each $w \in T$ with $w|_F = v$). Then $\sum_{\mathfrak P|\mathfrak p} n(\mathfrak P|\mathfrak p) = n$. -/
@[kb "omeara1963" "§15B, 15:3 (1), p. 32"]
theorem sum_localDegree_eq_finrank (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) :
    ∑ w ∈ T.attach, localDegree v w.1 (hT w.1 w.2) = Module.finrank F E := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨hA3, hA1, hA2⟩ := spots_aux v hθ
  rw [← sum_natDegree_toFinset v hθ]
  refine Finset.sum_bij (fun w _ => Gfac v θ w.1 (hT w.1 w.2)) ?_ ?_ ?_ ?_
  · intro w _
    exact Multiset.mem_toFinset.2 (hA3 _ _)
  · intro w _ w' _ h
    exact Subtype.ext (hA2 _ _ _ _ h)
  · intro g hg
    obtain ⟨w, hw, hwG⟩ := hA1 g (Multiset.mem_toFinset.1 hg)
    obtain ⟨w', ⟨hw'T, hw'e⟩, -⟩ := hrep w (by rw [hw]; exact AbsoluteValue.IsEquiv.refl v)
    have : w' = w := eq_of_isEquiv_of_under_eq F v _ _ hw'e (hT w' hw'T) hw
    subst this
    exact ⟨⟨w', hw'T⟩, Finset.mem_attach _ _, hwG⟩
  · intro w _
    exact localDegree_eq v hθ _ _

/-- **15:3 (Theorem) (2).** In the situation of 15:3 (1), $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}\alpha
= N_{E/F}\alpha$ for every $\alpha \in E$ (equality in $F_{\mathfrak p}$). -/
@[kb "omeara1963" "§15B, 15:3 (2), p. 32"]
theorem prod_localNorm_eq_norm (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) (α : E) :
    ∏ w ∈ T.attach, localNorm v w.1 (hT w.1 w.2) (α : w.1.Completion) =
      ((Algebra.norm F α : F) : v.Completion) := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨hA3, hA1, hA2⟩ := spots_aux v hθ
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  let Ω := AlgebraicClosure v.Completion
  apply (algebraMap v.Completion Ω).injective
  rw [map_prod]
  have hR : algebraMap v.Completion Ω ((Algebra.norm F α : F) : v.Completion) =
      ∏ σ : E →ₐ[F] Ω, σ α := by
    rw [← Algebra.norm_eq_prod_embeddings F Ω α,
      IsScalarTower.algebraMap_apply F v.Completion Ω]
    rfl
  rw [hR]
  have hL : ∀ w : {w // w ∈ T}, algebraMap v.Completion Ω
      (localNorm v w.1 (hT w.1 w.2) (α : w.1.Completion)) =
      ∏ σ ∈ Finset.univ.filter (fun σ : E →ₐ[F] Ω => minpoly v.Completion (σ θ) =
        Gfac v θ w.1 (hT w.1 w.2)), σ α := fun w => by
    haveI : w.1.LiesOver v := ⟨hT w.1 w.2⟩
    exact norm_local_eq_prod v hθ Ω w.1 α
  rw [Finset.prod_congr rfl (fun w _ => hL w)]
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (E →ₐ[F] Ω)), minpoly v.Completion (σ θ) ∈
      (UniqueFactorizationMonoid.normalizedFactors
        ((minpoly F θ).map (algebraMap F v.Completion))).toFinset := by
    intro σ _
    have hne : ((minpoly F θ).map (algebraMap F v.Completion)) ≠ 0 :=
      ((minpoly.monic hint).map _).ne_zero
    refine Multiset.mem_toFinset.2
      ((Polynomial.mem_normalizedFactors_iff hne).2 ⟨minpoly.irreducible
        (Algebra.IsIntegral.isIntegral _), minpoly.monic (Algebra.IsIntegral.isIntegral _), ?_⟩)
    refine minpoly.dvd _ _ ?_
    rw [aeval_map_algebraMap v.Completion, aeval_algHom_apply, minpoly.aeval, map_zero]
  rw [← Finset.prod_fiberwise_of_maps_to hmaps (fun σ => σ α)]
  refine Finset.prod_bij (fun w _ => Gfac v θ w.1 (hT w.1 w.2)) ?_ ?_ ?_ ?_
  · intro w _
    exact Multiset.mem_toFinset.2 (hA3 _ _)
  · intro w _ w' _ h
    exact Subtype.ext (hA2 _ _ _ _ h)
  · intro g hg
    obtain ⟨w, hw, hwG⟩ := hA1 g (Multiset.mem_toFinset.1 hg)
    obtain ⟨w', ⟨hw'T, hw'e⟩, -⟩ := hrep w (by rw [hw]; exact AbsoluteValue.IsEquiv.refl v)
    have : w' = w := eq_of_isEquiv_of_under_eq F v _ _ hw'e (hT w' hw'T) hw
    subst this
    exact ⟨⟨w', hw'T⟩, Finset.mem_attach _ _, hwG⟩
  · intro w _
    rfl

end Extension

end QuadFormsKB.OMeara
