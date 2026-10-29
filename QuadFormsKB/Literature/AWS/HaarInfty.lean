import QuadFormsKB.Literature.AWS.Adelic

open Matrix

namespace QuadFormsKB.AWS

variable {n : ℕ}

/-- Auxiliary: the real isometry matrices of a positive definite `A` form a compact set. -/
theorem isCompact_isometrySet_real (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsCompact {g : Matrix (Fin n) (Fin n) ℝ | gᵀ * A * g = A} := by
  -- a uniform lower bound for the quadratic form on the unit sphere
  have hcont : Continuous fun v : Fin n → ℝ => v ⬝ᵥ (A *ᵥ v) := by fun_prop
  obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧
      ∀ v ∈ Metric.sphere (0 : Fin n → ℝ) 1, c ≤ v ⬝ᵥ (A *ᵥ v) := by
    rcases (Metric.sphere (0 : Fin n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨v, hv, hmin⟩ :=
        (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨v ⬝ᵥ (A *ᵥ v), ?_, fun w hw => hmin hw⟩
      have : v ≠ 0 := by
        intro h0; rw [h0] at hv; simp at hv
      simpa [dotProduct_comm] using hA.re_dotProduct_pos this
  have hscale : ∀ v : Fin n → ℝ, c * ‖v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hw : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have := hcle _ (by simpa using hw)
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
      have h2 : c * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * (‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (A *ᵥ v)))) := by
        calc c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ * (‖v‖⁻¹ * (v ⬝ᵥ (A *ᵥ v)))) * ‖v‖ ^ 2 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := by ring
      calc c * ‖v‖ ^ 2 ≤ _ := h2
        _ = v ⬝ᵥ (A *ᵥ v) := by field_simp
  set C : ℝ := ∑ j, |A j j / c| + 1 with hC
  have hentry : ∀ g : Matrix (Fin n) (Fin n) ℝ, gᵀ * A * g = A →
      ∀ i j, g i j ∈ Set.Icc (-C) C := by
    intro g hg i j
    have hj : (fun k => g k j) ⬝ᵥ (A *ᵥ fun k => g k j) = A j j := by
      have := congrFun (congrFun hg j) j
      rw [← this]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h1 := hscale (fun k => g k j)
    rw [hj] at h1
    have h2 : |g i j| ≤ ‖fun k => g k j‖ := by
      simpa using norm_le_pi_norm (fun k => g k j) i
    have h3 : (g i j) ^ 2 ≤ A j j / c := by
      rw [le_div_iff₀ hc]
      have : (g i j) ^ 2 ≤ ‖fun k => g k j‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      nlinarith
    have h4 : A j j / c ≤ ∑ j, |A j j / c| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |A j j / c|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h5 : |g i j| ≤ C := by
      rw [hC]
      by_cases h : |g i j| ≤ 1
      · have : 0 ≤ ∑ j, |A j j / c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      · push Not at h
        have : |g i j| ≤ |g i j| ^ 2 := by nlinarith [abs_nonneg (g i j)]
        rw [sq_abs] at this
        linarith
    exact abs_le.mp h5
  have hclosed : IsClosed {g : Matrix (Fin n) (Fin n) ℝ | gᵀ * A * g = A} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  exact hbox.of_isClosed_subset hclosed fun g hg i _ j _ => hentry g hg i j

/-- $O(V)(\mathbb{R})$ is compact for positive definite $H$ (as a subset of $\mathrm{GL}_n(\mathbb{R})$). -/
theorem isCompact_orthGroup_real (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    IsCompact (Set.univ : Set (orthGroup H ℝ)) := by
  set A := H.map (algebraMap ℚ ℝ) with hAdef
  have hS := isCompact_isometrySet_real A hH
  set S := {g : Matrix (Fin n) (Fin n) ℝ | gᵀ * A * g = A} with hSdef
  set C : Set (GL (Fin n) ℝ) := (orthGroup H ℝ : Set (GL (Fin n) ℝ)) with hCdef
  have hCclosed : IsClosed C := by
    have : C = (fun g : GL (Fin n) ℝ => g.valᵀ * A * g.val) ⁻¹' {A} := by
      ext g; exact mem_orthGroup
    rw [this]
    exact isClosed_singleton.preimage (by
      have := Units.continuous_val (M := Matrix (Fin n) (Fin n) ℝ)
      fun_prop)
  have hclosedImg : IsClosed (Units.embedProduct (Matrix (Fin n) (Fin n) ℝ) '' C) :=
    (Units.isClosedEmbedding_embedProduct).isClosedMap _ hCclosed
  have hprod : IsCompact (S ×ˢ (MulOpposite.op '' S)) :=
    hS.prod (hS.image MulOpposite.continuous_op)
  have hsub : Units.embedProduct (Matrix (Fin n) (Fin n) ℝ) '' C ⊆
      S ×ˢ (MulOpposite.op '' S) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg, ⟨(g⁻¹).val, (orthGroup H ℝ).inv_mem hg, rfl⟩⟩
  have hCcomp : IsCompact C := by
    have := hprod.of_isClosed_subset hclosedImg hsub
    exact (Units.isEmbedding_embedProduct.isCompact_iff).mpr this
  rw [Subtype.isCompact_iff]
  simpa using hCcomp

/-- $O(V)(\mathbb{R})$ is a compact space for positive definite $H$. -/
theorem compactSpace_orthGroup_real (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosDef) :
    CompactSpace (orthGroup H ℝ) :=
  ⟨isCompact_orthGroup_real H hH⟩

end QuadFormsKB.AWS
