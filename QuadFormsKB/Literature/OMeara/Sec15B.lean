/-
# O'Meara §15B–§15C: continuity and signs of the norm, examples, the decomposition field (15:4–15:6, 15:8–15:10a)

**Setting.** As in `Sec15A.lean`: $v$ a valuation of $F$ (the spot $\mathfrak p$), $E/F$ finite separable, the spots
$\mathfrak P \mid \mathfrak p$ represented by a finite set $T$ of valuations $w$ of $E$ with `w.under F = v`, one in each
spot (`exists_spotRepresentatives`); `localDegree v w hw` is $n(\mathfrak P|\mathfrak p)$. Real spots, positive and
negative elements are those of `Sec12A.lean` (`IsRealSpot`, `IsPositiveElt`, `IsNegativeElt`, read in the
completion).

**Defines**
* `decompositionGroupAbs w` (§15C, p. 35): the decomposition group $\mathfrak Z = \{\sigma \in G : \mathfrak P^{\sigma} =
  \mathfrak P\}$ of a Galois extension at the spot of $w$ ($\mathfrak P^{\sigma}$ is the spot of $w\circ\sigma^{-1}$, the
  unique spot making $\sigma$ topological, §11D); its fixed field is the decomposition field $Z$.

**Proves** `continuous_norm_of_le` (**15:4**), `exists_norm_sub_lt` (**15:4a**), `isPositiveElt_norm` (**15:5**),
`norm_le_one_of_forall_le_one` (**15:6**), `spots_sqrt` (**15:8**), `spots_cbrt_two` (**15:9**),
`localDegree_eq_card_decompositionGroupAbs`, `fixedField_decompositionGroupAbs_eq`,
`ramificationIndexAbs_eq_of_isAbelian` (**15:10**), `exists_intermediateField_localDegree_eq` (**15:10a**).
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec15A
import QuadFormsKB.Literature.OMeara.Sec13B
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.RingTheory.Complex
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Polynomial.SpecificDegree

open Polynomial IntermediateField

namespace QuadFormsKB.OMeara

section Helpers

/-- A normed field is isometric to the `WithAbs` of its own absolute value. -/
private def withAbsIsometryEquivB (K : Type*) [NormedField K] :
    WithAbs (NormedField.toAbsoluteValue K) ≃ᵢ K :=
  { WithAbs.equiv _ with
    isometry_toFun := Isometry.of_dist_eq fun x y => by
      refine (dist_eq_norm _ _).trans ?_
      rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
      rfl }

private theorem completeSpace_withAbs_normedFieldB (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue K)) :=
  (withAbsIsometryEquivB K).completeSpace_iff.2 ‹_›

private theorem exists_unique_prolongation_auxB {K L : Type*} [NormedField K] [CompleteSpace K] [Field L]
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
    · push Not at h2
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
  · have := completeSpace_withAbs_normedFieldB K
    exact prolongation_formula_archimedean (NormedField.toAbsoluteValue K) hna


private theorem prolong_uniqueB {K L : Type*} [NormedField K] [CompleteSpace K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u u' : AbsoluteValue L ℝ) (hu : ∀ x : K, u (algebraMap K L x) = ‖x‖)
    (hu' : ∀ x : K, u' (algebraMap K L x) = ‖x‖) : u = u' := by
  obtain ⟨w, -, -, -, h4⟩ := exists_unique_prolongation_auxB (K := K) (L := L)
  exact (h4 u hu).trans (h4 u' hu').symm

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

private theorem norm_algebraMap_completionB (w : AbsoluteValue E ℝ) [w.LiesOver v] (c : v.Completion) :
    ‖algebraMap v.Completion w.Completion c‖ = ‖c‖ := by
  have := (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w))
  rw [AddMonoidHomClass.isometry_iff_norm] at this
  rw [AbsoluteValue.Completion.algebraMap_apply v w]
  exact this c

private theorem norm_algebraMap_EB (w : AbsoluteValue E ℝ) [w.LiesOver v] (e : E) :
    ‖algebraMap E w.Completion e‖ = w e := by
  show ‖((WithAbs.toAbs w e : WithAbs w) : w.Completion)‖ = w e
  rw [UniformSpace.Completion.norm_coe]
  rfl

private theorem norm_algebraMap_FB (x : F) : ‖algebraMap F v.Completion x‖ = v x := by
  show ‖((WithAbs.toAbs v x : WithAbs v) : v.Completion)‖ = v x
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- `‖N z‖ = ‖z‖ ^ n` in a finite extension of a complete field, for the completion norm. -/
private theorem norm_norm_completionB (w : AbsoluteValue E ℝ) [w.LiesOver v]
    [FiniteDimensional v.Completion w.Completion] (z : w.Completion) :
    ‖Algebra.norm v.Completion z‖ = ‖z‖ ^ Module.finrank v.Completion w.Completion := by
  obtain ⟨u, -, hform, -, huniq⟩ := exists_unique_prolongation_auxB (K := v.Completion)
    (L := w.Completion)
  have hN : NormedField.toAbsoluteValue w.Completion = u :=
    huniq _ (fun x => norm_algebraMap_completionB v w x)
  have h1 : ‖z‖ = ‖Algebra.norm v.Completion z‖ ^ (1 / (Module.finrank v.Completion w.Completion : ℝ)) := by
    rw [← hform z, ← hN]; rfl
  have hn : (0 : ℝ) < Module.finrank v.Completion w.Completion := by
    exact_mod_cast Module.finrank_pos
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hn.ne',
    Real.rpow_one]

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

variable (F) in
/-- Equivalent valuations of `E` inducing the same valuation on `F` coincide. -/
private theorem eq_of_isEquiv_of_under_eqB (w w' : AbsoluteValue E ℝ) (h : w.IsEquiv w')
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
private theorem exists_under_eq_of_equivB (w : AbsoluteValue E ℝ) (h : (w.under F).IsEquiv v) :
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

/-- The local degree is positive (every spot above `v` is a spot of the finitely many factors). -/
private theorem localDegree_posB (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    0 < localDegree v w hw := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  obtain ⟨W, hW, hiff, hcov, hdeg⟩ := spots_equiv_factors v hθ
  obtain ⟨g, hg⟩ := hcov w (by rw [hw]; exact AbsoluteValue.IsEquiv.refl v)
  have hWg : W g = w := eq_of_isEquiv_of_under_eqB F v _ _ hg (hW g) hw
  subst hWg
  rw [hdeg g]
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have hne : ((minpoly F θ).map (algebraMap F v.Completion)) ≠ 0 :=
    ((minpoly.monic hint).map _).ne_zero
  exact ((Polynomial.mem_normalizedFactors_iff hne).1 g.2).1.natDegree_pos

private theorem finiteDimensional_completionB (w : AbsoluteValue E ℝ) [hw : w.LiesOver v] :
    FiniteDimensional v.Completion w.Completion :=
  Module.finite_of_finrank_pos (localDegree_posB v w hw.1)


open Filter Topology in
/-- The norm of a finite extension of the completion `K` (a non-discrete complete field) is continuous. -/
private theorem continuous_norm_completionB (hnt : ∃ x : F, x ≠ 0 ∧ v x ≠ 1) (w : AbsoluteValue E ℝ)
    [w.LiesOver v] [FiniteDimensional v.Completion w.Completion] :
    Continuous (Algebra.norm v.Completion : w.Completion → v.Completion) := by
  obtain ⟨x, hx0, hx1⟩ := hnt
  have h2 : ∃ y : v.Completion, y ≠ 0 ∧ ‖y‖ ≠ 1 :=
    ⟨algebraMap F v.Completion x, by simpa using hx0, by rwa [norm_algebraMap_FB]⟩
  letI : NontriviallyNormedField v.Completion := NontriviallyNormedField.ofNormNeOne h2
  letI : NormedAlgebra v.Completion w.Completion :=
    { (inferInstance : Algebra v.Completion w.Completion) with
      norm_smul_le := fun r y => by
        rw [Algebra.smul_def, norm_mul, norm_algebraMap_completionB v w]
        }
  let φ : w.Completion →ₗ[v.Completion] (w.Completion →L[v.Completion] w.Completion) :=
    (LinearMap.toContinuousLinearMap :
      (w.Completion →ₗ[v.Completion] w.Completion) ≃ₗ[v.Completion]
        (w.Completion →L[v.Completion] w.Completion)).toLinearMap ∘ₗ
      (Algebra.lmul v.Completion w.Completion).toLinearMap
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  have : (Algebra.norm v.Completion : w.Completion → v.Completion) =
      fun z => ContinuousLinearMap.det (φ z) := by
    funext z
    rw [Algebra.norm_apply]
    rfl
  rw [this]
  exact ContinuousLinearMap.continuous_det.comp hφ

open Filter Topology in
private theorem tendsto_norm_auxB (hnt : ∃ x : F, x ≠ 0 ∧ v x ≠ 1) (T : Finset (AbsoluteValue E ℝ))
    (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) (α : E)
    (l : Filter E) (hl : ∀ δ : ℝ, 0 < δ → ∀ᶠ x in l, ∀ w ∈ T, w (x - α) < δ) :
    Tendsto (fun x : E => ((Algebra.norm F x : F) : v.Completion)) l
      (𝓝 ((Algebra.norm F α : F) : v.Completion)) := by
  classical
  have hform : (fun x : E => ((Algebra.norm F x : F) : v.Completion)) = fun x : E =>
      ∏ w ∈ T.attach, localNorm v w.1 (hT w.1 w.2) (x : w.1.Completion) :=
    funext fun x => (prod_localNorm_eq_norm v T hT hrep x).symm
  rw [hform, ← prod_localNorm_eq_norm v T hT hrep α]
  refine tendsto_finsetProd _ (fun w _ => ?_)
  haveI : w.1.LiesOver v := ⟨hT w.1 w.2⟩
  haveI : FiniteDimensional v.Completion w.1.Completion := finiteDimensional_completionB v w.1
  have hcont := continuous_norm_completionB v hnt w.1
  have h1 : Tendsto (fun x : E => (x : w.1.Completion)) l (𝓝 (α : w.1.Completion)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h3 : ∀ x : E, ‖(x : w.1.Completion) - (α : w.1.Completion)‖ = w.1 (x - α) := fun x => by
      have := norm_algebraMap_EB v w.1 (x - α)
      rw [map_sub] at this
      exact this
    simp_rw [h3]
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hl ε hε] with x hx
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (w.1.nonneg _)]
    exact hx w.1 w.2
  exact (hcont.tendsto _).comp h1

private theorem exists_norm_sub_ltB (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) (α : E) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, (∀ w ∈ T, w (x - α) < δ) →
      v (Algebra.norm F x - Algebra.norm F α) < ε := by
  classical
  by_cases hnt : ∃ x : F, x ≠ 0 ∧ v x ≠ 1
  · by_contra hcon
    push Not at hcon
    choose x hx1 hx2 using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
    have hten := tendsto_norm_auxB v hnt T hT hrep α (Filter.map x Filter.atTop) (by
      intro δ hδ
      rw [Filter.eventually_map]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
      filter_upwards [Filter.eventually_ge_atTop N] with n hn w hw
      refine lt_of_lt_of_le (hx1 n w hw) (le_trans ?_ hN.le)
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by positivity) (by linarith))
    have h2 := (Filter.tendsto_map'_iff.1 hten)
    rw [Metric.tendsto_nhds] at h2
    obtain ⟨n, hn⟩ := (h2 ε hε).exists
    have h3 : dist (((Algebra.norm F (x n) : F) : v.Completion))
        ((Algebra.norm F α : F) : v.Completion) = v (Algebra.norm F (x n) - Algebra.norm F α) := by
      rw [dist_eq_norm]
      have := norm_algebraMap_FB v (Algebra.norm F (x n) - Algebra.norm F α)
      rw [map_sub] at this
      exact this
    rw [Function.comp_apply, h3] at hn
    exact absurd (hx2 n) (not_le.2 hn)
  · push Not at hnt
    obtain ⟨w0, hw0⟩ := exists_under_eq (F := F) (E := E) v
    obtain ⟨w', ⟨hw'T, -⟩, -⟩ := hrep w0 (by rw [hw0]; exact AbsoluteValue.IsEquiv.refl v)
    refine ⟨1, one_pos, fun x hx => ?_⟩
    have hF : ∀ y : F, w' (algebraMap F E y) = v y := fun y => DFunLike.congr_fun (hT w' hw'T) y
    have hxα : x - α = 0 := by
      by_contra hne
      have := eq_one_of_trivial_on_algebraic (F := F) w' (fun y hy => by rw [hF]; exact hnt y hy) _ hne
      have h' := hx w' hw'T
      rw [this] at h'
      exact lt_irrefl _ h'
    rw [sub_eq_zero.1 hxα, sub_self, map_zero]
    exact hε


/-- Transport of the norm along a ring isomorphism of the base and of the top field. -/
private theorem phi_norm_eqB {K L C : Type*} [Field K] [Field L] [Algebra K L] [CommRing C] [Algebra ℝ C]
    (φ : K ≃+* ℝ) (ψ : L ≃+* C) (h : ∀ c : K, ψ (algebraMap K L c) = algebraMap ℝ C (φ c)) (z : L) :
    φ (Algebra.norm K z) = Algebra.norm ℝ (ψ z) := by
  letI : Algebra K C := ((algebraMap ℝ C).comp φ.toRingHom).toAlgebra
  let e : L ≃ₐ[K] C := { ψ with commutes' := fun c => h c }
  have h1 : Algebra.norm K (e z) = Algebra.norm K z := Algebra.norm_eq_of_algEquiv e z
  rw [← h1]
  exact Algebra.norm_eq_of_ringEquiv φ (RingHom.ext fun c => rfl) (ψ z)

private theorem sign_localNormB (φ : v.Completion ≃+* ℝ) (hφ : ∀ y, |φ y| = ‖y‖)
    (w : AbsoluteValue E ℝ) [w.LiesOver v]
    (z : w.Completion) (hz : z ≠ 0) :
    ((IsRealSpot w ∧ IsNegativeElt z) → φ (Algebra.norm v.Completion z) < 0) ∧
    (¬ (IsRealSpot w ∧ IsNegativeElt z) → 0 < φ (Algebra.norm v.Completion z)) := by
  have h2 : ‖(2 : v.Completion)‖ = 2 := by
    rw [← hφ, map_ofNat]; norm_num
  have hL2 : ‖(2 : w.Completion)‖ = 2 := by
    rw [← map_ofNat (algebraMap v.Completion w.Completion) 2, norm_algebraMap_completionB v w, h2]
  have hnonarch : ¬ IsNonarchimedean (NormedField.toAbsoluteValue w.Completion) := by
    intro h
    have h1 := h 1 1
    change ‖(1 : w.Completion) + 1‖ ≤ max ‖(1 : w.Completion)‖ ‖(1 : w.Completion)‖ at h1
    rw [one_add_one_eq_two, hL2, norm_one, max_self] at h1
    norm_num at h1
  have hcs := completeSpace_withAbs_normedFieldB w.Completion
  obtain ⟨ρ, hρ, hρ1, (⟨ψ, hψ⟩ | ⟨ψ, hψ⟩)⟩ := complete_archimedean_rpow
    (NormedField.toAbsoluteValue w.Completion) hnonarch
  · have hg : ∀ c : v.Completion, ψ (algebraMap v.Completion w.Completion c) = φ c := by
      intro c
      have h5 := Subsingleton.elim (ψ.toRingHom.comp
        ((algebraMap v.Completion w.Completion).comp φ.symm.toRingHom)) (RingHom.id ℝ)
      have h6 : ψ (algebraMap v.Completion w.Completion (φ.symm (φ c))) = φ c :=
        RingHom.congr_fun h5 (φ c)
      rwa [RingEquiv.symm_apply_apply] at h6
    have hρ' : ρ = 1 := by
      have h3 := hψ (2 : w.Completion)
      have h4 : ψ (2 : w.Completion) = 2 := map_ofNat ψ 2
      change |ψ 2| ^ ρ = ‖(2 : w.Completion)‖ at h3
      rw [h4, hL2] at h3
      have h5 : (2:ℝ) ^ ρ = 2 ^ (1:ℝ) := by rw [Real.rpow_one]; simpa using h3
      exact (Real.rpow_right_inj (by norm_num) (by norm_num)).1 h5
    have hreal : IsRealSpot w :=
      ⟨ψ, fun y => by have := hψ y; rw [hρ', Real.rpow_one] at this; exact this⟩
    have hN : φ (Algebra.norm v.Completion z) = ψ z := by
      rw [phi_norm_eqB φ ψ hg z]
      exact congrArg (fun f => f (ψ z)) (Algebra.norm_self (R := ℝ))
    have hψz : ψ z ≠ 0 := fun h => hz (ψ.map_eq_zero_iff.1 h)
    refine ⟨fun ⟨_, hn⟩ => ?_, fun hn => ?_⟩
    · rw [hN]; exact (isNegativeElt_iff_neg ψ z).1 hn
    · rw [hN]
      have h7 : ¬ IsNegativeElt z := fun h => hn ⟨hreal, h⟩
      rw [isNegativeElt_iff_neg ψ z, not_lt] at h7
      exact lt_of_le_of_ne h7 (Ne.symm hψz)
  · let g : ℝ →+* ℂ :=
      ψ.toRingHom.comp ((algebraMap v.Completion w.Completion).comp φ.symm.toRingHom)
    have hgn : ∀ r : ℝ, ‖g r‖ ^ ρ = |r| := by
      intro r
      have h5 := hψ (algebraMap v.Completion w.Completion (φ.symm r))
      change ‖ψ _‖ ^ ρ = ‖algebraMap v.Completion w.Completion (φ.symm r)‖ at h5
      rw [norm_algebraMap_completionB v w, ← hφ, RingEquiv.apply_symm_apply] at h5
      exact h5
    have hρ' : ρ = 1 := by
      have h3 := hgn 2
      have h4 : g 2 = 2 := map_ofNat g 2
      rw [h4] at h3
      have h5 : (2:ℝ) ^ ρ = 2 ^ (1:ℝ) := by
        rw [Real.rpow_one]; simpa using h3
      exact (Real.rpow_right_inj (by norm_num) (by norm_num)).1 h5
    have hgn1 : ∀ r : ℝ, ‖g r‖ = |r| := by
      intro r; have h5 := hgn r; rwa [hρ', Real.rpow_one] at h5
    have hgcont : Continuous g := by
      have h5 : Isometry g := by
        rw [AddMonoidHomClass.isometry_iff_norm]; intro r; rw [hgn1, Real.norm_eq_abs]
      exact h5.continuous
    have hgeq : (g : ℝ → ℂ) = Complex.ofRealHom := by
      refine Continuous.ext_on Rat.denseRange_cast hgcont Complex.continuous_ofReal ?_
      rintro _ ⟨q, rfl⟩
      simp
    have hg : ∀ c : v.Completion,
        ψ (algebraMap v.Completion w.Completion c) = algebraMap ℝ ℂ (φ c) := by
      intro c
      have h5 := congrFun hgeq (φ c)
      simpa [g] using h5
    have hN : φ (Algebra.norm v.Completion z) = Complex.normSq (ψ z) := by
      rw [phi_norm_eqB φ ψ hg z, Algebra.norm_complex_apply]
    have hψz : ψ z ≠ 0 := fun h => hz (ψ.map_eq_zero_iff.1 h)
    have hnr : ¬ IsRealSpot w := by
      rintro ⟨ψ', -⟩
      have h6 : (ψ' (ψ.symm Complex.I)) ^ 2 = -1 := by
        rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_neg, map_one, map_one]
      nlinarith [sq_nonneg (ψ' (ψ.symm Complex.I))]
    refine ⟨fun ⟨h, _⟩ => absurd h hnr, fun _ => ?_⟩
    rw [hN]
    exact Complex.normSq_pos.2 hψz


private theorem sign_prodB {ι : Type*} [DecidableEq ι] (S : Finset ι) (s : ι → ℝ) (P : ι → Prop)
    [DecidablePred P]
    (h : ∀ i ∈ S, (P i → s i < 0) ∧ (¬ P i → 0 < s i)) :
    0 < (-1 : ℝ) ^ (S.filter P).card * ∏ i ∈ S, s i := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha' := h a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha]
    by_cases hP : P a
    · rw [Finset.filter_insert, if_pos hP, Finset.card_insert_of_notMem (by simp [ha]), pow_succ]
      have h1 := ha'.1 hP
      nlinarith
    · rw [Finset.filter_insert, if_neg hP]
      have h1 := ha'.2 hP
      nlinarith


end Helpers

section Norm

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

/-- **15:4.** Let $E/F$ be finite separable and $\mathfrak p$ a spot of $F$. For any topology $t$ on $E$ finer than
every $\mathfrak P$-adic topology ($\mathfrak P \mid \mathfrak p$), the norm $N_{E/F}\colon E \to F$ is continuous from
$t$ to the $\mathfrak p$-adic topology. -/
@[kb "omeara1963" "§15B, 15:4, p. 33"]
theorem continuous_norm_of_le (t : TopologicalSpace E)
    (ht : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v →
      t ≤ TopologicalSpace.induced (WithAbs.toAbs w) inferInstance) :
    @Continuous E (WithAbs v) t _ (fun x : E => WithAbs.toAbs v (Algebra.norm F x)) := by
  classical
  letI : TopologicalSpace E := t
  obtain ⟨T, hT, hrep⟩ := exists_spotRepresentatives (E := E) v
  rw [continuous_iff_continuousAt]
  intro α
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exists_norm_sub_ltB v T hT hrep α hε
  have hmem : {x : E | ∀ w ∈ T, w (x - α) < δ} ∈ nhds α := by
    have hset : {x : E | ∀ w ∈ T, w (x - α) < δ} = ⋂ w ∈ T, {x : E | w (x - α) < δ} := by
      ext; simp
    rw [hset]
    refine (Filter.biInter_finset_mem T).2 (fun w hw => ?_)
    have hopen : @IsOpen E (TopologicalSpace.induced (WithAbs.toAbs w) inferInstance)
        {x : E | w (x - α) < δ} := by
      refine ⟨Metric.ball (WithAbs.toAbs w α) δ, Metric.isOpen_ball, ?_⟩
      ext x
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs,
        Set.mem_setOf_eq]
      rfl
    have hopen' : IsOpen {x : E | w (x - α) < δ} :=
      (TopologicalSpace.le_def.1 (ht w (by rw [hT w hw]; exact AbsoluteValue.IsEquiv.refl v))) _ hopen
    exact hopen'.mem_nhds (by simp [hδ])
  filter_upwards [hmem] with x hx
  have h3 : dist (WithAbs.toAbs v (Algebra.norm F x)) (WithAbs.toAbs v (Algebra.norm F α)) =
      v (Algebra.norm F x - Algebra.norm F α) := by
    rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
    rfl
  rw [h3]
  exact h x hx

/-- **15:4a.** Let $\alpha \in E$ and $\varepsilon > 0$. There is $\delta > 0$ such that
$|N_{E/F}x - N_{E/F}\alpha|_{\mathfrak p} < \varepsilon$ whenever $|x - \alpha|_{\mathfrak P} < \delta$ for all
$\mathfrak P \mid \mathfrak p$ (one valuation $w \in T$ in each spot). -/
@[kb "omeara1963" "§15B, 15:4a, p. 33"]
theorem exists_norm_sub_lt (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) (α : E) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, (∀ w ∈ T, w (x - α) < δ) →
      v (Algebra.norm F x - Algebra.norm F α) < ε := by
  exact exists_norm_sub_ltB v T hT hrep α hε

open Classical in
/-- **15:5.** Let $\mathfrak p$ be a real spot of $F$ and $\alpha \in E$, $\alpha \ne 0$. If $\alpha$ is negative at
exactly $r$ of the real spots $\mathfrak P \mid \mathfrak p$, then $(-1)^r N_{E/F}\alpha$ is positive at $\mathfrak p$.
(O'Meara does not exclude $\alpha = 0$, for which the statement fails.) -/
@[kb "omeara1963" "§15B, 15:5, p. 33"]
theorem isPositiveElt_norm (hv : IsRealSpot v) (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) {α : E} (hα : α ≠ 0) :
    IsPositiveElt ((((-1) ^ (T.filter fun w => IsRealSpot w ∧
        IsNegativeElt ((α : w.Completion))).card * Algebra.norm F α : F)) : v.Completion) := by
  obtain ⟨φ, hφ⟩ := hv
  rw [isPositiveElt_iff_pos φ]
  set r := (T.filter fun w => IsRealSpot w ∧ IsNegativeElt ((α : w.Completion))).card with hr
  have h1 : φ ((((-1) ^ r * Algebra.norm F α : F)) : v.Completion) =
      (-1 : ℝ) ^ r * ∏ w ∈ T.attach, φ (localNorm v w.1 (hT w.1 w.2) (α : w.1.Completion)) := by
    have e1 : ((((-1) ^ r * Algebra.norm F α : F)) : v.Completion) =
        (-1 : v.Completion) ^ r * ((Algebra.norm F α : F) : v.Completion) := by
      have := map_mul (algebraMap F v.Completion) ((-1) ^ r) (Algebra.norm F α)
      rw [map_pow, map_neg, map_one] at this
      exact this
    rw [e1, map_mul, map_pow, map_neg, map_one, ← prod_localNorm_eq_norm v T hT hrep α, map_prod]
  rw [h1]
  let s : AbsoluteValue E ℝ → ℝ := fun w =>
    if h : w ∈ T then φ (localNorm v w (hT w h) (α : w.Completion)) else 1
  have h2 : ∏ w ∈ T.attach, φ (localNorm v w.1 (hT w.1 w.2) (α : w.1.Completion)) =
      ∏ w ∈ T, s w := by
    rw [← Finset.prod_attach T s]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    simp [s, w.2]
  rw [h2, hr]
  refine sign_prodB T s (fun w => IsRealSpot w ∧ IsNegativeElt ((α : w.Completion))) ?_
  intro w hw
  haveI : w.LiesOver v := ⟨hT w hw⟩
  haveI : FiniteDimensional v.Completion w.Completion := finiteDimensional_completionB v w
  have hz : (α : w.Completion) ≠ 0 := by
    intro h0
    exact hα ((algebraMap E w.Completion).injective (by simpa using h0))
  have := sign_localNormB v φ hφ w (α : w.Completion) hz
  simp only [s, dif_pos hw]
  exact this

/-- **15:6 (Example).** If $|\alpha|_{\mathfrak P} \le 1$ for all $\mathfrak P \mid \mathfrak p$, then
$|N_{E/F}\alpha|_{\mathfrak p} \le 1$, with equality if and only if $|\alpha|_{\mathfrak P} = 1$ for all
$\mathfrak P \mid \mathfrak p$. -/
@[kb "omeara1963" "§15B, 15:6, p. 34"]
theorem norm_le_one_of_forall_le_one (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) {α : E}
    (h : ∀ w ∈ T, w α ≤ 1) :
    v (Algebra.norm F α) ≤ 1 ∧ (v (Algebra.norm F α) = 1 ↔ ∀ w ∈ T, w α = 1) := by
  classical
  have key : ∀ w : {w // w ∈ T}, ‖localNorm v w.1 (hT w.1 w.2) (α : w.1.Completion)‖ =
      (w.1 α) ^ localDegree v w.1 (hT w.1 w.2) := by
    intro w
    haveI : w.1.LiesOver v := ⟨hT w.1 w.2⟩
    haveI : FiniteDimensional v.Completion w.1.Completion := finiteDimensional_completionB v w.1
    have := norm_norm_completionB v w.1 (algebraMap E w.1.Completion α)
    rw [norm_algebraMap_EB v] at this
    exact this
  have hprod : v (Algebra.norm F α) =
      ∏ w ∈ T.attach, (w.1 α) ^ localDegree v w.1 (hT w.1 w.2) := by
    rw [← norm_algebraMap_FB v]
    have hp := congrArg (fun x => ‖x‖) (prod_localNorm_eq_norm v T hT hrep α)
    simp only [norm_prod] at hp
    exact hp.symm.trans (Finset.prod_congr rfl (fun w _ => key w))
  have hpos : ∀ w : {w // w ∈ T}, 0 < localDegree v w.1 (hT w.1 w.2) :=
    fun w => localDegree_posB v w.1 _
  have hle : ∀ w ∈ T.attach, (w.1 α) ^ localDegree v w.1 (hT w.1 w.2) ≤ 1 :=
    fun w _ => pow_le_one₀ (w.1.nonneg _) (h w.1 w.2)
  refine ⟨hprod ▸ Finset.prod_le_one₀ (fun w _ => pow_nonneg (w.1.nonneg _) _) hle, ?_⟩
  constructor
  · intro h1 w hw
    rw [hprod] at h1
    have hw' : (⟨w, hw⟩ : {w // w ∈ T}) ∈ T.attach := Finset.mem_attach _ _
    have h2 : (w α) ^ localDegree v w (hT w hw) = 1 := by
      refine le_antisymm (hle _ hw') ?_
      rw [← h1, ← Finset.mul_prod_erase _ _ hw']
      have : ∏ x ∈ T.attach.erase ⟨w, hw⟩, (x.1 α) ^ localDegree v x.1 (hT x.1 x.2) ≤ 1 :=
        Finset.prod_le_one₀ (fun x _ => pow_nonneg (x.1.nonneg _) _)
          (fun x hx => hle x (Finset.mem_of_mem_erase hx))
      have h0 : 0 ≤ (w α) ^ localDegree v w (hT w hw) := pow_nonneg (w.nonneg _) _
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (w.nonneg _) (hpos ⟨w, hw⟩).ne').1 h2
  · intro h1
    rw [hprod]
    refine Finset.prod_eq_one (fun w _ => ?_)
    rw [h1 w.1 w.2, one_pow]

end Norm

section Examples

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

section ExamplesAux

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)

private theorem fd_of_adjoin_top {θ : E} (hint : IsIntegral F θ) (hE : F⟮θ⟯ = ⊤) :
    FiniteDimensional F E := by
  haveI := IntermediateField.adjoin.finiteDimensional hint
  rw [hE] at this
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

open Classical in
private theorem monic_of_mem_factors {K : Type*} [Field K] {f g : K[X]}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors f) : g.Monic := by
  classical
  have h1 := UniqueFactorizationMonoid.normalize_normalized_factor g hg
  have h0 : g ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg).ne_zero
  have := Polynomial.monic_normalize h0
  rwa [h1] at this

variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

open Classical in
private theorem exists_factor_of_mem {θ : E} (hθ : F⟮θ⟯ = ⊤) (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors ((minpoly F θ).map (algebraMap F v.Completion)),
      localDegree v w hw = g.natDegree := by
  classical
  obtain ⟨W, hW, hiff, hcov, hdeg⟩ := spots_equiv_factors v hθ
  obtain ⟨g, hg⟩ := hcov w (by rw [hw]; exact AbsoluteValue.IsEquiv.refl v)
  have hWg : W g = w := eq_of_isEquiv_of_under_eqB F v _ _ hg (hW g) hw
  refine ⟨g.1, g.2, ?_⟩
  subst hWg
  exact hdeg g

private theorem card_mul_eq_finrank (T : Finset (AbsoluteValue E ℝ)) (hT : ∀ w ∈ T, w.under F = v)
    (hrep : ∀ w : AbsoluteValue E ℝ, (w.under F).IsEquiv v → ∃! w' ∈ T, w'.IsEquiv w) (m : ℕ)
    (hm : ∀ w (h : w ∈ T), localDegree v w (hT w h) = m) :
    T.card * m = Module.finrank F E := by
  have := sum_localDegree_eq_finrank v T hT hrep
  rw [Finset.sum_congr rfl (fun x _ => hm x.1 x.2)] at this
  simpa using this

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

private theorem realSpot_or_complexSpot (φ : v.Completion ≃+* ℝ) (hφ : ∀ y, |φ y| = ‖y‖)
    (w : AbsoluteValue E ℝ) [w.LiesOver v] : IsRealSpot w ∨ IsComplexSpot w := by
  have h2 : ‖(2 : v.Completion)‖ = 2 := by
    rw [← hφ, map_ofNat]; norm_num
  have hL2 : ‖(2 : w.Completion)‖ = 2 := by
    rw [← map_ofNat (algebraMap v.Completion w.Completion) 2, norm_algebraMap_completionB v w, h2]
  have hnonarch : ¬ IsNonarchimedean (NormedField.toAbsoluteValue w.Completion) := by
    intro h
    have h1 := h 1 1
    change ‖(1 : w.Completion) + 1‖ ≤ max ‖(1 : w.Completion)‖ ‖(1 : w.Completion)‖ at h1
    rw [one_add_one_eq_two, hL2, norm_one, max_self] at h1
    norm_num at h1
  have hcs := completeSpace_withAbs_normedFieldB w.Completion
  obtain ⟨ρ, hρ, hρ1, (⟨ψ, hψ⟩ | ⟨ψ, hψ⟩)⟩ := complete_archimedean_rpow
    (NormedField.toAbsoluteValue w.Completion) hnonarch
  · have hρ' : ρ = 1 := by
      have h3 := hψ (2 : w.Completion)
      have h4 : ψ (2 : w.Completion) = 2 := map_ofNat ψ 2
      change |ψ 2| ^ ρ = ‖(2 : w.Completion)‖ at h3
      rw [h4, hL2] at h3
      have h5 : (2:ℝ) ^ ρ = 2 ^ (1:ℝ) := by rw [Real.rpow_one]; simpa using h3
      exact (Real.rpow_right_inj (by norm_num) (by norm_num)).1 h5
    exact Or.inl ⟨ψ, fun y => by have := hψ y; rw [hρ', Real.rpow_one] at this; exact this⟩
  · have hρ' : ρ = 1 := by
      have h3 := hψ (2 : w.Completion)
      have h4 : ψ (2 : w.Completion) = 2 := map_ofNat ψ 2
      change ‖ψ 2‖ ^ ρ = ‖(2 : w.Completion)‖ at h3
      rw [h4, hL2] at h3
      have h5 : (2:ℝ) ^ ρ = 2 ^ (1:ℝ) := by rw [Real.rpow_one]; simpa using h3
      exact (Real.rpow_right_inj (by norm_num) (by norm_num)).1 h5
    exact Or.inr ⟨ψ, fun y => by have := hψ y; rw [hρ', Real.rpow_one] at this; exact this⟩

private theorem finrank_eq_one_of_realSpot (φ : v.Completion ≃+* ℝ)
    (w : AbsoluteValue E ℝ) [w.LiesOver v] (h : IsRealSpot w) :
    Module.finrank v.Completion w.Completion = 1 := by
  obtain ⟨ψ, -⟩ := h
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
  refine ⟨(algebraMap v.Completion w.Completion).injective, fun y => ?_⟩
  have h5 := Subsingleton.elim (ψ.toRingHom.comp
    ((algebraMap v.Completion w.Completion).comp φ.symm.toRingHom)) (RingHom.id ℝ)
  refine ⟨φ.symm (ψ y), ψ.injective ?_⟩
  exact RingHom.congr_fun h5 (ψ y)

private theorem not_complexSpot_of_finrank_eq_one (φ : v.Completion ≃+* ℝ)
    (w : AbsoluteValue E ℝ) [w.LiesOver v] (h1 : Module.finrank v.Completion w.Completion = 1)
    (h : IsComplexSpot w) : False := by
  obtain ⟨ψ, -⟩ := h
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap] at h1
  obtain ⟨k, hk⟩ := h1.2 (ψ.symm Complex.I)
  have hk2 : algebraMap v.Completion w.Completion (k ^ 2) =
      algebraMap v.Completion w.Completion (-1) := by
    rw [map_pow, hk, map_neg, map_one, ← map_pow, Complex.I_sq, map_neg, map_one]
  have := congrArg φ ((algebraMap v.Completion w.Completion).injective hk2)
  rw [map_pow, map_neg, map_one] at this
  nlinarith [sq_nonneg (φ k)]

end ExamplesAux

/-- **15:8 (Example).** Let $E = \mathbb Q(\sqrt a)$ with $a \in \mathbb Q$ not a square (here: $E = \mathbb Q(\theta)$,
$\theta^2 = a$), and $\mathfrak p = \infty$ the archimedean spot of $\mathbb Q$. If $a > 0$ there are two spots
$\mathfrak P \mid \infty$ on $E$, both of local degree $1$; if $a < 0$ there is one, of local degree $2$. -/
@[kb "omeara1963" "§15B, 15:8, p. 35"]
theorem spots_sqrt {E : Type*} [Field E] [Algebra ℚ E] {a : ℚ} (ha : ¬ IsSquare a) {θ : E} (hθ : θ ^ 2 = algebraMap ℚ E a)
    (hE : ℚ⟮θ⟯ = ⊤) :
    ∃ T : Finset (AbsoluteValue E ℝ), ∃ hT : ∀ w ∈ T, w.under ℚ = Rat.AbsoluteValue.real,
      (∀ w : AbsoluteValue E ℝ, (w.under ℚ).IsEquiv Rat.AbsoluteValue.real → ∃! w' ∈ T, w'.IsEquiv w) ∧
      (0 < a → T.card = 2 ∧ ∀ w (hw : w ∈ T), localDegree Rat.AbsoluteValue.real w (hT w hw) = 1) ∧
      (a < 0 → T.card = 1 ∧ ∀ w (hw : w ∈ T), localDegree Rat.AbsoluteValue.real w (hT w hw) = 2) := by
  classical
  have hint : IsIntegral ℚ θ := ⟨X ^ 2 - C a, monic_X_pow_sub_C a two_ne_zero, by simp [hθ]⟩
  haveI : FiniteDimensional ℚ E := fd_of_adjoin_top hint hE
  have hirr : Irreducible (X ^ 2 - C a : ℚ[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => ha ⟨b, by rw [← hb]; ring⟩)
  have hmin : minpoly ℚ θ = X ^ 2 - C a :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C a two_ne_zero)).symm
  have hfin : Module.finrank ℚ E = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hE, IntermediateField.finrank_top', hmin, natDegree_X_pow_sub_C] at this
    exact this
  obtain ⟨φ, hφ⟩ := rat_archimedean_real_spot.2.1
  have hφa : ∀ q : ℚ, φ (algebraMap ℚ Rat.AbsoluteValue.real.Completion q) = (q : ℝ) := by
    intro q
    rw [eq_ratCast (algebraMap ℚ Rat.AbsoluteValue.real.Completion) q, map_ratCast]
  obtain ⟨T, hT, hrep⟩ := exists_spotRepresentatives (E := E) Rat.AbsoluteValue.real
  have hfac : ∀ w (hw : w ∈ T), ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((X ^ 2 - C (algebraMap ℚ Rat.AbsoluteValue.real.Completion a) :
        Rat.AbsoluteValue.real.Completion[X])),
      localDegree Rat.AbsoluteValue.real w (hT w hw) = g.natDegree := by
    intro w hw
    obtain ⟨g, hg, h⟩ := exists_factor_of_mem Rat.AbsoluteValue.real hE w (hT w hw)
    refine ⟨g, ?_, h⟩
    simpa [hmin] using hg
  refine ⟨T, hT, hrep, fun hpos => ?_, fun hneg => ?_⟩
  · set c : Rat.AbsoluteValue.real.Completion := φ.symm (Real.sqrt a) with hc
    have hc2 : c ^ 2 = algebraMap ℚ Rat.AbsoluteValue.real.Completion a := by
      apply φ.injective
      rw [map_pow, hc, RingEquiv.apply_symm_apply, hφa, Real.sq_sqrt (by exact_mod_cast hpos.le)]
    have hf : (X ^ 2 - C (algebraMap ℚ Rat.AbsoluteValue.real.Completion a) :
        Rat.AbsoluteValue.real.Completion[X]) = (X - C c) * (X + C c) := by
      rw [← hc2, map_pow]; ring
    have hone : ∀ w (hw : w ∈ T), localDegree Rat.AbsoluteValue.real w (hT w hw) = 1 := by
      intro w hw
      obtain ⟨g, hg, h⟩ := hfac w hw
      rw [h]
      have hirrg := UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg
      have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg
      rw [hf] at hdvd
      have hle : g.natDegree ≤ 1 := by
        rcases hirrg.prime.dvd_or_dvd hdvd with h1 | h1
        · simpa using Polynomial.natDegree_le_of_dvd h1 (X_sub_C_ne_zero c)
        · simpa using Polynomial.natDegree_le_of_dvd h1 (X_add_C_ne_zero c)
      have := hirrg.natDegree_pos
      omega
    refine ⟨?_, hone⟩
    have := card_mul_eq_finrank Rat.AbsoluteValue.real T hT hrep 1 hone
    rw [hfin] at this
    omega
  · have htwo : ∀ w (hw : w ∈ T), localDegree Rat.AbsoluteValue.real w (hT w hw) = 2 := by
      intro w hw
      obtain ⟨g, hg, h⟩ := hfac w hw
      rw [h]
      have hirrg := UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg
      have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg
      have hmon := monic_of_mem_factors hg
      have hf0 : (X ^ 2 - C (algebraMap ℚ Rat.AbsoluteValue.real.Completion a) :
          Rat.AbsoluteValue.real.Completion[X]) ≠ 0 := (monic_X_pow_sub_C _ two_ne_zero).ne_zero
      have hle : g.natDegree ≤ 2 := by
        simpa using Polynomial.natDegree_le_of_dvd hdvd hf0
      have hpos := hirrg.natDegree_pos
      by_contra hne
      have h1 : g.natDegree = 1 := by omega
      have hg1 := hmon.eq_X_add_C h1
      have hroot : (X ^ 2 - C (algebraMap ℚ Rat.AbsoluteValue.real.Completion a) :
          Rat.AbsoluteValue.real.Completion[X]).IsRoot (-(g.coeff 0)) := by
        rw [← Polynomial.dvd_iff_isRoot]
        rw [hg1] at hdvd
        simpa using hdvd
      have := congrArg φ (show (-(g.coeff 0)) ^ 2 = algebraMap ℚ Rat.AbsoluteValue.real.Completion a by
        simpa [sub_eq_zero] using hroot)
      rw [map_pow, hφa] at this
      nlinarith [sq_nonneg (φ (-(g.coeff 0))), (by exact_mod_cast hneg : (a : ℝ) < 0)]
    refine ⟨?_, htwo⟩
    have := card_mul_eq_finrank Rat.AbsoluteValue.real T hT hrep 2 htwo
    rw [hfin] at this
    omega

/-- **15:9 (Example).** Let $E = \mathbb Q(\sqrt[3]{2})$ (here: $E = \mathbb Q(\theta)$, $\theta^3 = 2$) and
$\mathfrak p = \infty$. Since $x^3 - 2 = (x - \sqrt[3]2)(x^2 + \sqrt[3]2x + \sqrt[3]4)$ over $\mathbb R$, there are two
spots $\mathfrak P \mid \infty$, one of local degree $1$, which is real, and one of local degree $2$, which is
complex. -/
@[kb "omeara1963" "§15B, 15:9, p. 35"]
theorem spots_cbrt_two {E : Type*} [Field E] [Algebra ℚ E] {θ : E} (hθ : θ ^ 3 = 2) (hE : ℚ⟮θ⟯ = ⊤) :
    ∃ w₁ w₂ : AbsoluteValue E ℝ, ∃ h₁ : w₁.under ℚ = Rat.AbsoluteValue.real,
      ∃ h₂ : w₂.under ℚ = Rat.AbsoluteValue.real,
      (∀ w : AbsoluteValue E ℝ, (w.under ℚ).IsEquiv Rat.AbsoluteValue.real → w.IsEquiv w₁ ∨ w.IsEquiv w₂) ∧
      ¬ w₁.IsEquiv w₂ ∧ localDegree _ w₁ h₁ = 1 ∧ localDegree _ w₂ h₂ = 2 ∧
      IsRealSpot w₁ ∧ IsComplexSpot w₂ := by
  classical
  have hint : IsIntegral ℚ θ := ⟨X ^ 3 - C 2, monic_X_pow_sub_C 2 (by norm_num), by simp [hθ]⟩
  haveI : FiniteDimensional ℚ E := fd_of_adjoin_top hint hE
  have hno : ∀ b : ℚ, b ^ 3 ≠ 2 := by
    intro b hb
    have hx : (b : ℝ) ^ 3 = ((2 : ℤ) : ℝ) := by exact_mod_cast hb
    have hv : ¬ ∃ y : ℤ, (b : ℝ) = y := by
      rintro ⟨y, hy⟩
      rw [hy] at hx
      have hy3 : y ^ 3 = 2 := by exact_mod_cast hx
      rcases le_or_gt y 1 with h | h
      · nlinarith [sq_nonneg (y + 1), sq_nonneg y]
      · nlinarith [sq_nonneg y]
    exact (irrational_nrt_of_notint_nrt 3 2 hx hv (by norm_num)) ⟨b, rfl⟩
  have hirr : Irreducible (X ^ 3 - C 2 : ℚ[X]) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_three hno
  have hmin : minpoly ℚ θ = X ^ 3 - C 2 :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C 2 (by norm_num))).symm
  obtain ⟨φ, hφ⟩ := rat_archimedean_real_spot.2.1
  have hφa : ∀ q : ℚ, φ (algebraMap ℚ Rat.AbsoluteValue.real.Completion q) = (q : ℝ) := by
    intro q
    rw [eq_ratCast (algebraMap ℚ Rat.AbsoluteValue.real.Completion) q, map_ratCast]
  obtain ⟨r, hr0, hr3⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 3 = 2 := by
    refine ⟨(2 : ℝ) ^ ((1 : ℝ) / 3), by positivity, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  set K := Rat.AbsoluteValue.real.Completion with hK
  set c : K := φ.symm r with hc
  have hc3 : c ^ 3 = 2 := by
    apply φ.injective
    rw [map_pow, hc, RingEquiv.apply_symm_apply, hr3, map_ofNat]
  have hφc : φ c = r := by rw [hc, RingEquiv.apply_symm_apply]
  set g₂ : K[X] := X ^ 2 + C c * X + C (c ^ 2) with hg₂
  have hg₂deg : g₂.natDegree = 2 := by
    rw [hg₂]; compute_degree!
  have hg₂mon : g₂.Monic := by
    rw [hg₂]; monicity!
  have hg₂irr : Irreducible g₂ := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by simp [hg₂deg]) (fun x hx => ?_)
    have h0 : x ^ 2 + c * x + c ^ 2 = 0 := by
      simpa [hg₂, Polynomial.IsRoot] using hx
    have := congrArg φ h0
    rw [map_add, map_add, map_pow, map_mul, map_pow, hφc, map_zero] at this
    nlinarith [sq_nonneg (φ x + r / 2), hr0]
  have hl1irr : Irreducible (X - C c : K[X]) := Polynomial.irreducible_X_sub_C c
  have hf : (X ^ 3 - C (algebraMap ℚ K 2) : K[X]) = (X - C c) * g₂ := by
    have : algebraMap ℚ K 2 = c ^ 3 := by rw [hc3, map_ofNat]
    rw [this, hg₂]; simp only [map_pow]; ring
  have hfac : UniqueFactorizationMonoid.normalizedFactors (X ^ 3 - C (algebraMap ℚ K 2) : K[X]) =
      {X - C c} + {g₂} := by
    rw [hf, UniqueFactorizationMonoid.normalizedFactors_mul hl1irr.ne_zero hg₂irr.ne_zero,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hl1irr,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hg₂irr,
      (monic_X_sub_C c).normalize_eq_self, hg₂mon.normalize_eq_self]
  obtain ⟨W, hW, hiff, hcov, hdeg⟩ := spots_equiv_factors Rat.AbsoluteValue.real hE
  have hmem1 : (X - C c : K[X]) ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly ℚ θ).map (algebraMap ℚ K)) := by
    rw [hmin]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hfac]; simp
  have hmem2 : g₂ ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly ℚ θ).map (algebraMap ℚ K)) := by
    rw [hmin]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    rw [hfac]; simp
  have hS : UniqueFactorizationMonoid.normalizedFactors ((minpoly ℚ θ).map (algebraMap ℚ K)) =
      {X - C c} + {g₂} := by
    rw [hmin]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    exact hfac
  let G1 : {g : K[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly ℚ θ).map (algebraMap ℚ K))} := ⟨_, hmem1⟩
  let G2 : {g : K[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly ℚ θ).map (algebraMap ℚ K))} := ⟨_, hmem2⟩
  have hne : G1 ≠ G2 := by
    intro h
    have := congrArg (fun g : {g : K[X] // g ∈ UniqueFactorizationMonoid.normalizedFactors
      ((minpoly ℚ θ).map (algebraMap ℚ K))} => g.1.natDegree) h
    simp [G1, G2, hg₂deg] at this
  have hd1 : localDegree Rat.AbsoluteValue.real (W G1) (hW G1) = 1 := by
    rw [hdeg]; simp [G1]
  have hd2 : localDegree Rat.AbsoluteValue.real (W G2) (hW G2) = 2 := by
    rw [hdeg]; simp [G2, hg₂deg]
  refine ⟨W G1, W G2, hW G1, hW G2, ?_, fun h => hne ((hiff G1 G2).1 h), hd1, hd2, ?_, ?_⟩
  · intro w hw
    obtain ⟨g, hg⟩ := hcov w hw
    have hg' : g.1 ∈ ({X - C c} + {g₂} : Multiset K[X]) :=
      (congrArg (fun m => g.1 ∈ m) hS).mp g.2
    simp only [Multiset.mem_add, Multiset.mem_singleton] at hg'
    rcases hg' with h | h
    · left
      have : g = G1 := Subtype.ext h
      rw [this] at hg
      exact hg.symm
    · right
      have : g = G2 := Subtype.ext h
      rw [this] at hg
      exact hg.symm
  · haveI : (W G1).LiesOver Rat.AbsoluteValue.real := ⟨hW G1⟩
    haveI : FiniteDimensional K (W G1).Completion := by
      refine Module.finite_of_finrank_pos ?_
      have : Module.finrank K (W G1).Completion = 1 := hd1
      omega
    rcases realSpot_or_complexSpot Rat.AbsoluteValue.real φ hφ (W G1) with h | h
    · exact h
    · exact (not_complexSpot_of_finrank_eq_one Rat.AbsoluteValue.real φ (W G1) hd1 h).elim
  · haveI : (W G2).LiesOver Rat.AbsoluteValue.real := ⟨hW G2⟩
    rcases realSpot_or_complexSpot Rat.AbsoluteValue.real φ hφ (W G2) with h | h
    · have := finrank_eq_one_of_realSpot Rat.AbsoluteValue.real φ (W G2) h
      have h2 : Module.finrank K (W G2).Completion = 2 := hd2
      exact absurd (this.symm.trans h2) (by norm_num)
    · exact h

end Examples


section Galois

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)

/-- The valuation $w\circ\rho$ of $E$ for an $F$-automorphism $\rho$. -/
private def compAut (w : AbsoluteValue E ℝ) (ρ : E ≃ₐ[F] E) : AbsoluteValue E ℝ :=
  w.comp (f := ρ.toRingEquiv.toRingHom) ρ.injective

private theorem compAut_apply (w : AbsoluteValue E ℝ) (ρ : E ≃ₐ[F] E) (x : E) :
    compAut w ρ x = w (ρ x) := rfl

private theorem compAut_under (w : AbsoluteValue E ℝ) (ρ : E ≃ₐ[F] E) :
    (compAut w ρ).under F = w.under F := by
  ext x
  show w (ρ (algebraMap F E x)) = w (algebraMap F E x)
  rw [ρ.commutes]

private theorem compAut_compAut (w : AbsoluteValue E ℝ) (ρ ρ' : E ≃ₐ[F] E) :
    compAut (compAut w ρ) ρ' = compAut w (ρ * ρ') := rfl

private theorem compAut_one (w : AbsoluteValue E ℝ) : compAut w (1 : E ≃ₐ[F] E) = w := rfl

private theorem compAut_isEquiv {w w' : AbsoluteValue E ℝ} (h : w.IsEquiv w') (ρ : E ≃ₐ[F] E) :
    (compAut w ρ).IsEquiv (compAut w' ρ) := fun x y => h (ρ x) (ρ y)

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

/-- The `K`-algebra isomorphism of completions induced by an automorphism `ρ` with
`w1 ∘ ρ = w2`. -/
private noncomputable def phiIso (w1 w2 : AbsoluteValue E ℝ) [w1.LiesOver v] [w2.LiesOver v]
    (ρ : E ≃ₐ[F] E) (h : ∀ x, w1 (ρ x) = w2 x) : w2.Completion ≃ₐ[v.Completion] w1.Completion := by
  have hiso : Isometry (WithAbs.congr w2 w1 ρ.toRingEquiv) := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply, WithAbs.ofAbs_toAbs]
    exact h _
  have hiso' : Isometry (WithAbs.congr w2 w1 ρ.toRingEquiv).symm := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_symm_apply, WithAbs.ofAbs_toAbs]
    have := h (ρ.symm x.ofAbs)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  refine AlgEquiv.ofRingEquiv (f := UniformSpace.Completion.mapRingEquiv
    (WithAbs.congr w2 w1 ρ.toRingEquiv) hiso.continuous hiso'.continuous) (fun c => ?_)
  have hfun : (⇑(WithAbs.congr w2 w1 ρ.toRingEquiv)) ∘ ⇑(WithAbs.map v w2 (algebraMap F E)) =
      ⇑(WithAbs.map v w1 (algebraMap F E)) := by
    funext x
    simp [WithAbs.map_apply]
  rw [AbsoluteValue.Completion.algebraMap_apply v w2, AbsoluteValue.Completion.algebraMap_apply v w1]
  simp only [UniformSpace.Completion.mapRingEquiv_apply, UniformSpace.Completion.mapRingHom_apply]
  rw [← Function.comp_apply (f := UniformSpace.Completion.map (⇑(WithAbs.congr w2 w1 ρ.toRingEquiv)))
    (g := UniformSpace.Completion.map (⇑(WithAbs.map v w2 (algebraMap F E)))),
    UniformSpace.Completion.map_comp hiso.uniformContinuous (WithAbs.isometry_map v w2).uniformContinuous,
    hfun]


private theorem phiIso_coe (w1 w2 : AbsoluteValue E ℝ) [w1.LiesOver v] [w2.LiesOver v]
    (ρ : E ≃ₐ[F] E) (h : ∀ x, w1 (ρ x) = w2 x) (e : E) :
    phiIso v w1 w2 ρ h (algebraMap E w2.Completion e) = algebraMap E w1.Completion (ρ e) := by
  show (phiIso v w1 w2 ρ h) ((WithAbs.toAbs w2 e : WithAbs w2) : w2.Completion) = _
  have hiso : Isometry (WithAbs.congr w2 w1 ρ.toRingEquiv) := by
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply, WithAbs.ofAbs_toAbs]
    exact h _
  simp [phiIso, UniformSpace.Completion.mapRingEquiv]
  rw [UniformSpace.Completion.map_coe hiso.uniformContinuous]
  rfl

private theorem localDegree_compAut (w : AbsoluteValue E ℝ) (hw : w.under F = v) (ρ : E ≃ₐ[F] E) :
    localDegree v (compAut w ρ) ((compAut_under w ρ).trans hw) = localDegree v w hw := by
  haveI : w.LiesOver v := ⟨hw⟩
  haveI : (compAut w ρ).LiesOver v := ⟨(compAut_under w ρ).trans hw⟩
  unfold localDegree
  exact (phiIso v w (compAut w ρ) ρ (fun x => rfl)).toLinearEquiv.finrank_eq

end Galois

section Transitive

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (v : AbsoluteValue F ℝ)

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

private theorem eq_comp_prolong (w : AbsoluteValue E ℝ) [w.LiesOver v] [FiniteDimensional v.Completion w.Completion]
    {M : Type*} [Field M] [Algebra v.Completion M] [FiniteDimensional v.Completion M]
    (u : AbsoluteValue M ℝ) (hu : ∀ x : v.Completion, u (algebraMap v.Completion M x) = ‖x‖)
    (j : w.Completion →ₐ[v.Completion] M) (e : E) : w e = u (j (algebraMap E w.Completion e)) := by
  have h := prolong_uniqueB (K := v.Completion) (L := w.Completion) (u.comp (f := j.toRingHom) j.injective)
    (NormedField.toAbsoluteValue w.Completion)
    (fun x => by
      show u (j (algebraMap v.Completion w.Completion x)) = _
      rw [j.commutes, hu])
    (fun x => norm_algebraMap_completionB v w x)
  have := congrArg (fun a : AbsoluteValue w.Completion ℝ => a (algebraMap E w.Completion e)) h
  rw [← norm_algebraMap_EB v w e]
  exact this.symm

private theorem algebraMap_comm (w : AbsoluteValue E ℝ) [w.LiesOver v] (a : F) :
    algebraMap E w.Completion (algebraMap F E a) =
      algebraMap v.Completion w.Completion (algebraMap F v.Completion a) := by
  show _ = algebraMap v.Completion w.Completion ((WithAbs.toAbs v a : WithAbs v) : v.Completion)
  rw [AbsoluteValue.Completion.algebraMap_apply v w, UniformSpace.Completion.mapRingHom_coe]
  rfl

private theorem exists_compAut_eq [FiniteDimensional F E] [IsGalois F E] (w w' : AbsoluteValue E ℝ)
    (hw : w.under F = v) (hw' : w'.under F = v) :
    ∃ ρ : E ≃ₐ[F] E, compAut w ρ = w' := by
  classical
  haveI : w.LiesOver v := ⟨hw⟩
  haveI : w'.LiesOver v := ⟨hw'⟩
  haveI := finiteDimensional_completionB v w
  haveI := finiteDimensional_completionB v w'
  let Ω := AlgebraicClosure v.Completion
  let j : w.Completion →ₐ[v.Completion] Ω := IsAlgClosed.lift
  let j' : w'.Completion →ₐ[v.Completion] Ω := IsAlgClosed.lift
  haveI : FiniteDimensional v.Completion j.fieldRange := j.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional v.Completion j'.fieldRange := j'.toLinearMap.finiteDimensional_range
  let M : IntermediateField v.Completion Ω := j.fieldRange ⊔ j'.fieldRange
  haveI : FiniteDimensional v.Completion M := IntermediateField.finiteDimensional_sup _ _
  have hj : ∀ x, j x ∈ M := fun x => le_sup_left (a := j.fieldRange) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
  have hj' : ∀ x, j' x ∈ M := fun x => le_sup_right (a := j.fieldRange) (AlgHom.mem_fieldRange.2 ⟨x, rfl⟩)
  let jM : w.Completion →ₐ[v.Completion] M :=
    { toFun := fun x => ⟨j x, hj x⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun x y => Subtype.ext (map_mul j x y)
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun x y => Subtype.ext (map_add j x y)
      commutes' := fun r => Subtype.ext (j.commutes r) }
  let jM' : w'.Completion →ₐ[v.Completion] M :=
    { toFun := fun x => ⟨j' x, hj' x⟩
      map_one' := Subtype.ext (map_one j')
      map_mul' := fun x y => Subtype.ext (map_mul j' x y)
      map_zero' := Subtype.ext (map_zero j')
      map_add' := fun x y => Subtype.ext (map_add j' x y)
      commutes' := fun r => Subtype.ext (j'.commutes r) }
  obtain ⟨u, hu1, -, -, -⟩ := exists_unique_prolongation_auxB (K := v.Completion) (L := M)
  letI : Algebra F M := ((algebraMap v.Completion M).comp (algebraMap F v.Completion)).toAlgebra
  let σ : E →ₐ[F] M :=
    { toFun := fun e => jM (algebraMap E w.Completion e)
      map_one' := by simp
      map_mul' := by simp
      map_zero' := by simp
      map_add' := by simp
      commutes' := fun a => by
        show jM (algebraMap E w.Completion (algebraMap F E a)) = algebraMap v.Completion M (algebraMap F v.Completion a)
        rw [algebraMap_comm v w, jM.commutes] }
  let σ' : E →ₐ[F] M :=
    { toFun := fun e => jM' (algebraMap E w'.Completion e)
      map_one' := by simp
      map_mul' := by simp
      map_zero' := by simp
      map_add' := by simp
      commutes' := fun a => by
        show jM' (algebraMap E w'.Completion (algebraMap F E a)) = algebraMap v.Completion M (algebraMap F v.Completion a)
        rw [algebraMap_comm v w', jM'.commutes] }
  letI : Algebra E M := σ.toRingHom.toAlgebra
  haveI : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq (fun a => (σ.commutes a).symm)
  refine ⟨AlgHom.restrictNormal' σ' E, ?_⟩
  ext e
  have h1 := AlgHom.restrictNormal_commutes σ' E e
  show w (AlgHom.restrictNormal' σ' E e) = w' e
  rw [eq_comp_prolong v w u hu1 jM (AlgHom.restrictNormal' σ' E e), eq_comp_prolong v w' u hu1 jM' e]
  exact congrArg u h1

end Transitive

section AbelianSubgroups

universe uG

private theorem exists_subgroup_card_eq_of_dvd (d : ℕ) : ∀ (G : Type uG) [CommGroup G] [Finite G],
    d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro G _ _ hd
    have hG : 0 < Nat.card G := Nat.card_pos
    have hd0 : d ≠ 0 := fun h => by rw [h] at hd; exact hG.ne' (Nat.eq_zero_of_zero_dvd hd)
    by_cases hd1 : d = 1
    · exact ⟨⊥, by rw [hd1]; simp⟩
    · have hp : (Nat.minFac d).Prime := Nat.minFac_prime hd1
      set p := Nat.minFac d with hpdef
      haveI : Fact p.Prime := ⟨hp⟩
      have hpd : p ∣ d := Nat.minFac_dvd d
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) p (hpd.trans hd)
      let P : Subgroup G := Subgroup.zpowers g
      have hP : Nat.card P = p := by rw [Nat.card_zpowers]; exact hg
      have hQ : Nat.card G = Nat.card (G ⧸ P) * p := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hP]
      obtain ⟨e, he⟩ := hpd
      have hlt : e < d := by
        rw [he]
        have := hp.two_le
        have he0 : 0 < e := by
          rcases Nat.eq_zero_or_pos e with h | h
          · rw [h] at he; omega
          · exact h
        nlinarith
      have hdQ : e ∣ Nat.card (G ⧸ P) := by
        rw [hQ, he] at hd
        exact Nat.dvd_of_mul_dvd_mul_right hp.pos (by rwa [mul_comm e p])
      obtain ⟨H', hH'⟩ := ih e hlt (G ⧸ P) hdQ
      refine ⟨H'.comap (QuotientGroup.mk' P), ?_⟩
      have hs : Function.Surjective (QuotientGroup.mk' P) := QuotientGroup.mk'_surjective P
      have h1 := Subgroup.card_mul_index (H'.comap (QuotientGroup.mk' P))
      have h2 := Subgroup.card_mul_index H'
      rw [Subgroup.index_comap_of_surjective _ hs] at h1
      have hi : 0 < H'.index := Nat.pos_of_ne_zero (Subgroup.finiteIndex_of_finite.index_ne_zero)
      have h3 : Nat.card (H'.comap (QuotientGroup.mk' P)) * H'.index = (e * p) * H'.index := by
        rw [h1, hQ, ← h2, hH']; ring
      have := Nat.eq_of_mul_eq_mul_right hi h3
      rw [this, he]
      ring

end AbelianSubgroups

section Decomposition

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The *decomposition group* of $E/F$ at the spot $\mathfrak P$ of the valuation $w$ (§15C, p. 35):
$\mathfrak Z = \{\sigma : \mathfrak P^{\sigma} = \mathfrak P\}$, where $\mathfrak P^{\sigma}$ is the spot of
$w\circ\sigma^{-1}$ (the spot carried from $\mathfrak P$ by $\sigma$, §11D). The *decomposition field* $Z$ is its fixed
field. -/
@[kb "omeara1963" "§15C, p. 35 (decomposition group and decomposition field)"]
def decompositionGroupAbs (w : AbsoluteValue E ℝ) : Subgroup (E ≃ₐ[F] E) where
  carrier := {σ | (w.comp (f := σ.symm.toRingEquiv.toRingHom) σ.symm.injective).IsEquiv w}
  mul_mem' := by
    intro a b ha hb x y
    have hb' := hb (a.symm x) (a.symm y)
    have ha' := ha x y
    exact hb'.trans ha'
  one_mem' := fun x y => Iff.rfl
  inv_mem' := by
    intro a ha x y
    exact (ha (a x) (a y)).symm.trans (by simp)

variable (v : AbsoluteValue F ℝ) [FiniteDimensional F E] [IsGalois F E]

private noncomputable instance autAct : MulAction (E ≃ₐ[F] E) (AbsoluteValue E ℝ) where
  smul σ w := compAut w σ⁻¹
  one_smul w := by
    show compAut w (1 : E ≃ₐ[F] E)⁻¹ = w
    rw [inv_one]
    exact compAut_one w
  mul_smul σ τ w := by
    show compAut w (σ * τ)⁻¹ = compAut (compAut w τ⁻¹) σ⁻¹
    rw [mul_inv_rev, compAut_compAut]

private theorem autAct_smul_def (σ : E ≃ₐ[F] E) (w : AbsoluteValue E ℝ) : σ • w = compAut w σ⁻¹ := rfl

private theorem mem_decomp_iff_stabilizer (w : AbsoluteValue E ℝ) (hw : w.under F = v)
    (σ : E ≃ₐ[F] E) :
    σ ∈ decompositionGroupAbs (F := F) w ↔ σ ∈ MulAction.stabilizer (E ≃ₐ[F] E) w := by
  rw [MulAction.mem_stabilizer_iff, autAct_smul_def]
  constructor
  · intro h
    exact eq_of_isEquiv_of_under_eqB F v _ _ h ((compAut_under w σ⁻¹).trans hw) hw
  · intro h
    show (compAut w σ⁻¹).IsEquiv w
    rw [h]
    exact AbsoluteValue.IsEquiv.refl w

private theorem decomp_eq_stabilizer (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    decompositionGroupAbs (F := F) w = MulAction.stabilizer (E ≃ₐ[F] E) w :=
  Subgroup.ext (mem_decomp_iff_stabilizer v w hw)

private theorem mem_orbit_iff_under (w : AbsoluteValue E ℝ) (hw : w.under F = v) (w' : AbsoluteValue E ℝ) :
    w' ∈ MulAction.orbit (E ≃ₐ[F] E) w ↔ w'.under F = v := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, rfl⟩
    exact (compAut_under w σ⁻¹).trans hw
  · intro hw'
    obtain ⟨ρ, hρ⟩ := exists_compAut_eq v w w' hw hw'
    exact ⟨ρ⁻¹, by rw [autAct_smul_def, inv_inv]; exact hρ⟩

private theorem localDegree_eq_of_compAut {w w' : AbsoluteValue E ℝ} (hw : w.under F = v)
    (hw' : w'.under F = v) (ρ : E ≃ₐ[F] E) (h : compAut w ρ = w') :
    localDegree v w' hw' = localDegree v w hw := by
  subst h
  exact localDegree_compAut v w hw ρ

private theorem localDegree_const (w w' : AbsoluteValue E ℝ) (hw : w.under F = v) (hw' : w'.under F = v) :
    localDegree v w' hw' = localDegree v w hw := by
  obtain ⟨ρ, hρ⟩ := exists_compAut_eq v w w' hw hw'
  exact localDegree_eq_of_compAut v hw hw' ρ hρ

private theorem localDegree_eq_card_decomp (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    localDegree v w hw = Nat.card (decompositionGroupAbs (F := F) w) := by
  classical
  obtain ⟨T, hT, hrep⟩ := exists_spotRepresentatives (E := E) v
  have hsum := sum_localDegree_eq_finrank v T hT hrep
  rw [Finset.sum_congr rfl (fun x _ => localDegree_const v w x.1 hw (hT x.1 x.2))] at hsum
  simp only [Finset.sum_const, Finset.card_attach, smul_eq_mul] at hsum
  have hmemT : ∀ w' : AbsoluteValue E ℝ, w' ∈ T ↔ w'.under F = v := by
    intro w'
    constructor
    · exact hT w'
    · intro hw'
      obtain ⟨w'', ⟨h1, h2⟩, -⟩ := hrep w' (by rw [hw']; exact AbsoluteValue.IsEquiv.refl v)
      have := eq_of_isEquiv_of_under_eqB F v _ _ h2 (hT w'' h1) hw'
      rw [← this]
      exact h1
  have horb : MulAction.orbit (E ≃ₐ[F] E) w = (T : Set (AbsoluteValue E ℝ)) := by
    ext w'
    rw [mem_orbit_iff_under v w hw, Finset.mem_coe, hmemT]
  have hidx : (MulAction.stabilizer (E ≃ₐ[F] E) w).index = T.card := by
    rw [MulAction.index_stabilizer, horb, Set.ncard_coe_finset]
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer (E ≃ₐ[F] E) w)
  rw [hidx, IsGalois.card_aut_eq_finrank F E, ← hsum, ← decomp_eq_stabilizer v w hw] at hcard
  have hpos : 0 < T.card := Finset.card_pos.2 ⟨w, (hmemT w).2 hw⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (hcard.symm.trans (mul_comm _ _))

private theorem isNonarch_of_isEquiv {K : Type*} [Field K] {a b : AbsoluteValue K ℝ} (h : a.IsEquiv b)
    (hb : IsNonarchimedean b) : IsNonarchimedean a := by
  refine (isNonarchimedean_iff_natCast_bounded a).2 ⟨1, fun n => ?_⟩
  have h1 : b (n : K) ≤ 1 := hb.apply_natCast_le_one (by simp) (map_one b)
  have := (h (n : K) 1).2 (by simpa using h1)
  simpa using this

private theorem ramificationIndexAbs_compAut (w : AbsoluteValue E ℝ) (ρ : E ≃ₐ[F] E) :
    ramificationIndexAbs (F := F) (compAut w ρ) = ramificationIndexAbs (F := F) w := by
  unfold ramificationIndexAbs
  have h1 : absValueGroup (compAut w ρ) = absValueGroup w := by
    ext u
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨ρ x, by simpa using hx, h⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨ρ.symm x, by simpa using hx, by
        show w (ρ (ρ.symm x)) = _
        simpa using h⟩
  rw [compAut_under, h1]

private theorem inertiaDegAbs_compAut (w : AbsoluteValue E ℝ) (ρ : E ≃ₐ[F] E) (hw : IsNonarchimedean w)
    (hw' : IsNonarchimedean (compAut w ρ)) :
    inertiaDegAbs (F := F) (compAut w ρ) hw' = inertiaDegAbs (F := F) w hw := by
  refine inertiaDegAbs_eq_of (F := F) (E := E) (F' := F) (E' := E) (compAut w ρ) hw' w hw (RingHom.id F)
    ρ.toRingEquiv.toRingHom (fun a => ρ.commutes a) ?_ ?_
  · refine ⟨fun x => Iff.rfl, fun x => Iff.rfl, fun y hy => ⟨ρ.symm y, ?_, ?_⟩⟩
    · show w (ρ (ρ.symm y)) ≤ 1
      simpa using hy
    · have : y - ρ.toRingEquiv.toRingHom (ρ.symm y) = 0 := by simp
      rw [this, map_zero]
      exact one_pos
  · rw [compAut_under]
    exact ResidueData.of_isEquiv (AbsoluteValue.IsEquiv.refl _)

attribute [local instance] AbsoluteValue.Completion.algebraOfLiesOver

private theorem denseRange_algebraMap_EB (w : AbsoluteValue E ℝ) :
    DenseRange (algebraMap E w.Completion) := by
  have : DenseRange ((↑) : WithAbs w → w.Completion) := UniformSpace.Completion.denseRange_coe
  exact this.comp (WithAbs.toAbs_surjective w).denseRange (UniformSpace.Completion.continuous_coe _)

private theorem phiIso_continuous (w1 w2 : AbsoluteValue E ℝ) [w1.LiesOver v] [w2.LiesOver v]
    (ρ : E ≃ₐ[F] E) (h : ∀ x, w1 (ρ x) = w2 x) : Continuous (phiIso v w1 w2 ρ h) := by
  show Continuous (UniformSpace.Completion.map (WithAbs.congr w2 w1 ρ.toRingEquiv))
  exact UniformSpace.Completion.continuous_map

private theorem apply_eq_of_mem_decomp (w : AbsoluteValue E ℝ) (hw : w.under F = v)
    {σ : E ≃ₐ[F] E} (hσ : σ ∈ decompositionGroupAbs (F := F) w) (x : E) : w (σ x) = w x := by
  have h1 := (mem_decomp_iff_stabilizer v w hw _).1 (inv_mem hσ)
  rw [MulAction.mem_stabilizer_iff, autAct_smul_def, inv_inv] at h1
  exact DFunLike.congr_fun h1 x

private theorem exists_decomp_hom (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    haveI : w.LiesOver v := ⟨hw⟩
    ∃ ψ : decompositionGroupAbs (F := F) w →* (w.Completion ≃ₐ[v.Completion] w.Completion),
      ∀ σ e, ψ σ (algebraMap E w.Completion e) = algebraMap E w.Completion ((σ : E ≃ₐ[F] E) e) := by
  haveI : w.LiesOver v := ⟨hw⟩
  have hσ : ∀ σ : decompositionGroupAbs (F := F) w, ∀ x, w ((σ : E ≃ₐ[F] E) x) = w x :=
    fun σ x => apply_eq_of_mem_decomp v w hw σ.2 x
  refine ⟨MonoidHom.mk' (fun σ => phiIso v w w (σ : E ≃ₐ[F] E) (hσ σ)) ?_, ?_⟩
  · intro σ τ
    refine AlgEquiv.ext fun z => ?_
    have := (denseRange_algebraMap_EB w).equalizer
      (g := fun z => phiIso v w w ((σ * τ : decompositionGroupAbs (F := F) w) : E ≃ₐ[F] E) (hσ _) z)
      (h := fun z => phiIso v w w (σ : E ≃ₐ[F] E) (hσ σ) (phiIso v w w (τ : E ≃ₐ[F] E) (hσ τ) z))
      (phiIso_continuous v w w _ _)
      ((phiIso_continuous v w w _ _).comp (phiIso_continuous v w w _ _))
      (funext fun e => by
        simp only [Function.comp_apply, phiIso_coe]
        rfl)
    exact congrFun this z
  · intro σ e
    exact phiIso_coe v w w _ (hσ σ) e

private theorem under_under_eq (H : IntermediateField F E) (w : AbsoluteValue E ℝ) :
    (w.under H).under F = w.under F := by
  ext x
  rfl

private theorem algebraMap_tower (H : IntermediateField F E) (w : AbsoluteValue E ℝ) [w.LiesOver v]
    [(w.under H).LiesOver v] [w.LiesOver (w.under H)] (x : v.Completion) :
    algebraMap v.Completion w.Completion x =
      algebraMap (w.under H).Completion w.Completion (algebraMap v.Completion (w.under H).Completion x) := by
  have hd := denseRange_algebraMap_EB v
  have := hd.equalizer
    (g := fun x : v.Completion => algebraMap v.Completion w.Completion x)
    (h := fun x : v.Completion => algebraMap (w.under H).Completion w.Completion
      (algebraMap v.Completion (w.under H).Completion x))
    (continuous_algebraMap _ _)
    ((continuous_algebraMap _ _).comp (continuous_algebraMap _ _))
    (funext fun a => by
      simp only [Function.comp_apply]
      rw [← algebraMap_comm v w a, ← algebraMap_comm v (w.under H) a,
        ← algebraMap_comm (w.under H) w (algebraMap F H a)]
      rfl)
  exact congrFun this x

private theorem localDegree_tower (H : IntermediateField F E) (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    localDegree v w hw = localDegree (w.under H) w rfl *
      localDegree v (w.under H) ((under_under_eq H w).trans hw) := by
  haveI : w.LiesOver v := ⟨hw⟩
  haveI : (w.under H).LiesOver v := ⟨(under_under_eq H w).trans hw⟩
  haveI : w.LiesOver (w.under H) := ⟨rfl⟩
  haveI : IsScalarTower v.Completion (w.under H).Completion w.Completion :=
    IsScalarTower.of_algebraMap_eq (algebraMap_tower v H w)
  unfold localDegree
  rw [mul_comm]
  exact (Module.finrank_mul_finrank v.Completion (w.under H).Completion w.Completion).symm

/-- **15:10 (1).** Let $E/F$ be an abelian extension (Galois with commutative Galois group) and $\mathfrak P \mid \mathfrak p$
the spot of $w$, with decomposition group $\mathfrak Z$ and decomposition field $Z$. Then
$n(\mathfrak P|\mathfrak p) = [E : Z] = |\mathfrak Z|$, and $n(\mathfrak P'|\mathfrak p) = n(\mathfrak P|\mathfrak p)$
for every other spot $\mathfrak P' \mid \mathfrak p$. -/
@[kb "omeara1963" "§15C, 15:10 (1), p. 36"]
theorem localDegree_eq_card_decompositionGroupAbs (hab : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (w : AbsoluteValue E ℝ) (hw : w.under F = v) :
    localDegree v w hw = Nat.card (decompositionGroupAbs (F := F) w) ∧
      Module.finrank (fixedField (decompositionGroupAbs (F := F) w)) E = localDegree v w hw ∧
      ∀ (w' : AbsoluteValue E ℝ) (hw' : w'.under F = v), localDegree v w' hw' = localDegree v w hw := by
  have h1 := localDegree_eq_card_decomp v w hw
  refine ⟨h1, ?_, fun w' hw' => localDegree_const v w w' hw hw'⟩
  rw [h1]
  exact IntermediateField.finrank_fixedField_eq_card _

/-- **15:10 (2).** In the situation of 15:10 (1), $Z_{\mathfrak P} = F_{\mathfrak P}$ and $Z = F_{\mathfrak P} \cap E$: an
element of $E$ lies in the decomposition field if and only if its image in $E_{\mathfrak P}$ lies in
$F_{\mathfrak P}$ (the image of $F_{\mathfrak p}$). -/
@[kb "omeara1963" "§15C, 15:10 (2), p. 36"]
theorem fixedField_decompositionGroupAbs_eq (hab : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (w : AbsoluteValue E ℝ) (hw : w.under F = v) (x : E) :
    x ∈ fixedField (decompositionGroupAbs (F := F) w) ↔
      haveI : w.LiesOver v := ⟨hw⟩
      letI := AbsoluteValue.Completion.algebraOfLiesOver v w
      (x : w.Completion) ∈ (algebraMap v.Completion w.Completion).range := by
  haveI : w.LiesOver v := ⟨hw⟩
  haveI := finiteDimensional_completionB v w
  obtain ⟨ψ, hψ⟩ := exists_decomp_hom v w hw
  have hinj : Function.Injective ψ := by
    intro σ τ h
    refine Subtype.ext (AlgEquiv.ext fun e => ?_)
    have h1 := hψ σ e
    rw [h, hψ τ e] at h1
    exact ((algebraMap E w.Completion).injective h1).symm
  let H' : Subgroup (w.Completion ≃ₐ[v.Completion] w.Completion) := ψ.range
  have hcard : Nat.card H' = Nat.card (decompositionGroupAbs (F := F) w) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfin : Module.finrank (IntermediateField.fixedField H') w.Completion =
      Module.finrank v.Completion w.Completion := by
    rw [IntermediateField.finrank_fixedField_eq_card, hcard, ← localDegree_eq_card_decomp v w hw]
    rfl
  have hbot : IntermediateField.fixedField H' = ⊥ := by
    have h1 := Module.finrank_mul_finrank v.Completion (IntermediateField.fixedField H') w.Completion
    have hpos : 0 < Module.finrank v.Completion w.Completion := Module.finrank_pos
    rw [hfin] at h1
    have h2 : Module.finrank v.Completion (IntermediateField.fixedField H') = 1 := by
      have := Nat.eq_of_mul_eq_mul_right hpos (h1.trans (one_mul _).symm)
      exact this
    exact IntermediateField.finrank_eq_one_iff.1 h2
  constructor
  · intro hx
    have hmem : (algebraMap E w.Completion x) ∈ IntermediateField.fixedField H' := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨σ, rfl⟩
      show ψ σ (algebraMap E w.Completion x) = _
      rw [hψ, (IntermediateField.mem_fixedField_iff _ _).1 hx _ σ.2]
    rw [hbot, IntermediateField.mem_bot] at hmem
    exact hmem
  · rintro ⟨c, hc⟩
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 := hψ ⟨σ, hσ⟩ x
    have h2 : ψ ⟨σ, hσ⟩ (algebraMap E w.Completion x) = algebraMap E w.Completion x := by
      have hc' : algebraMap E w.Completion x = algebraMap v.Completion w.Completion c := hc.symm
      rw [hc']
      exact (ψ ⟨σ, hσ⟩).commutes c
    rw [h2] at h1
    exact ((algebraMap E w.Completion).injective h1).symm

/-- **15:10 (3).** In the situation of 15:10, if $\mathfrak p$ is non-archimedean then all spots $\mathfrak P, \mathfrak P'
\mid \mathfrak p$ have the same ramification index and the same degree of inertia. -/
@[kb "omeara1963" "§15C, 15:10 (3), p. 36"]
theorem ramificationIndexAbs_eq_of_isAbelian (hab : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    {w w' : AbsoluteValue E ℝ} (hw : (w.under F).IsEquiv v) (hw' : (w'.under F).IsEquiv v)
    (hna : IsNonarchimedean w) (hna' : IsNonarchimedean w') :
    ramificationIndexAbs (F := F) w = ramificationIndexAbs (F := F) w' ∧
      inertiaDegAbs (F := F) w hna = inertiaDegAbs (F := F) w' hna' := by
  obtain ⟨w₀, h0e, h0u⟩ := exists_under_eq_of_equivB F v w hw
  obtain ⟨w₀', h0e', h0u'⟩ := exists_under_eq_of_equivB F v w' hw'
  obtain ⟨ρ, hρ⟩ := exists_compAut_eq v w₀ w₀' h0u h0u'
  have hn0 : IsNonarchimedean w₀ := isNonarch_of_isEquiv h0e hna
  have hn0' : IsNonarchimedean w₀' := isNonarch_of_isEquiv h0e' hna'
  subst hρ
  constructor
  · rw [← ramificationIndexAbs_congr (F := F) h0e, ← ramificationIndexAbs_congr (F := F) h0e',
      ramificationIndexAbs_compAut]
  · rw [← inertiaDegAbs_congr (F := F) hn0 hna h0e, ← inertiaDegAbs_congr (F := F) hn0' hna' h0e',
      inertiaDegAbs_compAut w₀ ρ hn0 hn0']

/-- **15:10a.** In the situation of 15:10, let $d$ divide the local degree $n_{\mathfrak p} = n(\mathfrak P|\mathfrak p)$.
Then there is a field $H$ with $Z \subseteq H \subseteq E$ such that the local degree of $H/F$ at $\mathfrak p$ (at the
spot induced by $\mathfrak P$) is $d$. -/
@[kb "omeara1963" "§15C, 15:10a, p. 37"]
theorem exists_intermediateField_localDegree_eq (hab : ∀ σ τ : E ≃ₐ[F] E, σ * τ = τ * σ)
    (w : AbsoluteValue E ℝ) (hw : w.under F = v) {d : ℕ} (hd : d ∣ localDegree v w hw) :
    ∃ H : IntermediateField F E, fixedField (decompositionGroupAbs (F := F) w) ≤ H ∧
      ∃ hH : (w.under H).under F = v, localDegree v (w.under H) hH = d := by
  have hn := localDegree_eq_card_decomp v w hw
  have hnpos := localDegree_posB v w hw
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos |> fun h => h
  letI : CommGroup (decompositionGroupAbs (F := F) w) :=
    { (inferInstance : Group (decompositionGroupAbs (F := F) w)) with
      mul_comm := fun a b => Subtype.ext (hab a b) }
  obtain ⟨K0, hK0⟩ := exists_subgroup_card_eq_of_dvd (localDegree v w hw / d)
    (decompositionGroupAbs (F := F) w) (hn ▸ Nat.div_dvd_of_dvd hd)
  let Hgrp : Subgroup (E ≃ₐ[F] E) := K0.map (decompositionGroupAbs (F := F) w).subtype
  have hHcard : Nat.card Hgrp = localDegree v w hw / d := by
    rw [← hK0]
    exact (Nat.card_congr (K0.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv).symm
  have hle : Hgrp ≤ decompositionGroupAbs (F := F) w := by
    rintro _ ⟨k, _, rfl⟩
    exact k.2
  refine ⟨IntermediateField.fixedField Hgrp, ?_, under_under_eq _ w |>.trans hw, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    exact hx σ (hle hσ)
  · have htow := localDegree_tower v (IntermediateField.fixedField Hgrp) w hw
    have hE := localDegree_eq_card_decomp (F := IntermediateField.fixedField Hgrp) (w.under _) w rfl
    have hall : decompositionGroupAbs (F := IntermediateField.fixedField Hgrp) w = ⊤ := by
      have key : ∀ σ : E ≃ₐ[IntermediateField.fixedField Hgrp] E, ∀ x, w (σ x) = w x := by
        intro σ x
        have hmem : σ.restrictScalars F ∈ IntermediateField.fixingSubgroup
            (IntermediateField.fixedField Hgrp) := by
          intro y
          exact σ.commutes y
        rw [IntermediateField.fixingSubgroup_fixedField] at hmem
        exact apply_eq_of_mem_decomp v w hw (hle hmem) x
      refine eq_top_iff.2 (fun σ _ => ?_)
      intro x y
      show w (σ.symm x) ≤ w (σ.symm y) ↔ _
      rw [key σ.symm x, key σ.symm y]
    rw [hall, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
      IntermediateField.finrank_fixedField_eq_card, hHcard] at hE
    rw [hE] at htow
    have hq : 0 < localDegree v w hw / d := by
      exact Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos
    have h2 : localDegree v w hw / d * localDegree v (w.under (IntermediateField.fixedField Hgrp))
        ((under_under_eq _ w).trans hw) = localDegree v w hw / d * d := by
      rw [← htow, Nat.div_mul_cancel hd]
    exact Nat.eq_of_mul_eq_mul_left hq h2

end Decomposition

end QuadFormsKB.OMeara
