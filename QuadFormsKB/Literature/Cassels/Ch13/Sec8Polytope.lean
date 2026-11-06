import Mathlib

open Matrix Filter Topology

namespace QuadFormsKB.Reduction.S8

/-- Coordinate formula for the dot product on `Fin 2 → ℝ`. -/
lemma dot2 (a x : Fin 2 → ℝ) : a ⬝ᵥ x = a 0 * x 0 + a 1 * x 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- An extreme point of a planar polygon lies on two independent active constraints. -/
lemma extreme_active {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≠ 0) (x : Fin 2 → ℝ)
    (hx : x ∈ ({x : Fin 2 → ℝ | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i}).extremePoints ℝ) :
    ∃ i ∈ s, ∃ j ∈ s, a i 0 * a j 1 - a i 1 * a j 0 ≠ 0 ∧
      a i ⬝ᵥ x = c i ∧ a j ⬝ᵥ x = c j := by
  classical
  rw [mem_extremePoints] at hx
  obtain ⟨hxP, hext⟩ := hx
  by_contra hcon
  push_neg at hcon
  have hv : ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ ∀ j ∈ s, a j ⬝ᵥ x = c j → a j ⬝ᵥ v = 0 := by
    by_cases h : ∃ i ∈ s, a i ⬝ᵥ x = c i
    · obtain ⟨i, hi, hix⟩ := h
      refine ⟨![-(a i 1), a i 0], ?_, ?_⟩
      · intro h0
        apply ha i hi
        have h1 := congrFun h0 0
        have h2 := congrFun h0 1
        simp at h1 h2
        ext k; fin_cases k <;> simp [h1, h2]
      · intro j hj hjx
        have hd := hcon i hi j hj
        have : a i 0 * a j 1 - a i 1 * a j 0 = 0 := by
          by_contra hne
          exact hd hne hix hjx
        rw [dot2]
        simp
        linarith
    · push_neg at h
      refine ⟨![1, 0], ?_, ?_⟩
      · intro h0; have := congrFun h0 0; simp at this
      · intro j hj hjx; exact absurd hjx (h j hj)
  obtain ⟨v, hv0, hvj⟩ := hv
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ ∀ j ∈ s,
      a j ⬝ᵥ x + t * (a j ⬝ᵥ v) ≤ c j ∧ a j ⬝ᵥ x - t * (a j ⬝ᵥ v) ≤ c j := by
    have h0 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    refine h0.and ?_
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    rw [Filter.eventually_all_finset]
    intro j hj
    by_cases hact : a j ⬝ᵥ x = c j
    · refine Eventually.of_forall fun t => ?_
      rw [hvj j hj hact, hact]; simp
    · have hlt : a j ⬝ᵥ x < c j := lt_of_le_of_ne (hxP j hj) hact
      have c1 : Continuous fun t : ℝ => a j ⬝ᵥ x + t * (a j ⬝ᵥ v) := by fun_prop
      have c2 : Continuous fun t : ℝ => a j ⬝ᵥ x - t * (a j ⬝ᵥ v) := by fun_prop
      have e1 := c1.continuousAt (x := 0) |>.eventually_lt continuousAt_const (by simpa using hlt)
      have e2 := c2.continuousAt (x := 0) |>.eventually_lt continuousAt_const (by simpa using hlt)
      filter_upwards [e1, e2] with t h1 h2 using ⟨h1.le, h2.le⟩
  obtain ⟨t, ht, htP⟩ := hev.exists
  have m1 : x + t • v ∈ {x : Fin 2 → ℝ | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i} := by
    intro j hj; have := (htP j hj).1
    simpa [dotProduct_add, dotProduct_smul] using this
  have m2 : x - t • v ∈ {x : Fin 2 → ℝ | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i} := by
    intro j hj; have := (htP j hj).2
    simpa [dotProduct_sub, dotProduct_smul] using this
  have hmem : x ∈ openSegment ℝ (x + t • v) (x - t • v) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext k; simp; ring
  have := (hext _ m1 _ m2 hmem).1
  have h0 : t • v = 0 := by simpa using this
  rcases smul_eq_zero.mp h0 with h | h
  · exact ht.ne' h
  · exact hv0 h

theorem exists_finset_convexHull_of_halfplanes {ι : Type*} (s : Finset ι) (a : ι → Fin 2 → ℝ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≠ 0) (R : ℝ) (hb : ∀ x : Fin 2 → ℝ, (∀ i ∈ s, a i ⬝ᵥ x ≤ c i) → ‖x‖ ≤ R) :
    ∃ V : Finset (Fin 2 → ℝ), {x : Fin 2 → ℝ | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i} = convexHull ℝ (V : Set (Fin 2 → ℝ)) := by
  classical
  set P : Set (Fin 2 → ℝ) := {x : Fin 2 → ℝ | ∀ i ∈ s, a i ⬝ᵥ x ≤ c i} with hP
  have hconv : Convex ℝ P := by
    intro x hx y hy p q hp hq hpq i hi
    have := add_le_add (mul_le_mul_of_nonneg_left (hx i hi) hp) (mul_le_mul_of_nonneg_left (hy i hi) hq)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have e : p * c i + q * c i = c i := by rw [← add_mul, hpq, one_mul]
    linarith
  have hclosed : IsClosed P := by
    have : P = ⋂ i ∈ s, {x : Fin 2 → ℝ | a i ⬝ᵥ x ≤ c i} := by ext x; simp [hP]
    rw [this]
    refine isClosed_biInter fun i _ => isClosed_le ?_ continuous_const
    have e : (fun x : Fin 2 → ℝ => a i ⬝ᵥ x) = fun x => a i 0 * x 0 + a i 1 * x 1 :=
      funext (dot2 _)
    show Continuous fun x : Fin 2 → ℝ => a i ⬝ᵥ x
    rw [e]; fun_prop
  have hcomp : IsCompact P := by
    refine Metric.isCompact_of_isClosed_isBounded hclosed ?_
    exact (Metric.isBounded_closedBall (x := (0 : Fin 2 → ℝ)) (r := R)).subset
      (fun x hx => by simpa using hb x hx)
  set W : Finset (Fin 2 → ℝ) := (s ×ˢ s).image (fun p =>
    ![(c p.1 * a p.2 1 - c p.2 * a p.1 1) / (a p.1 0 * a p.2 1 - a p.1 1 * a p.2 0),
      (a p.1 0 * c p.2 - a p.2 0 * c p.1) / (a p.1 0 * a p.2 1 - a p.1 1 * a p.2 0)]) with hW
  refine ⟨W.filter (· ∈ P), ?_⟩
  have hext : P.extremePoints ℝ ⊆ ((W.filter (· ∈ P) : Finset _) : Set (Fin 2 → ℝ)) := by
    intro x hx
    obtain ⟨i, hi, j, hj, hD, h1, h2⟩ := extreme_active s a c ha x hx
    rw [dot2] at h1 h2
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    refine ⟨Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩, ?_⟩, hx.1⟩
    have e0 : (c i * a j 1 - c j * a i 1) / (a i 0 * a j 1 - a i 1 * a j 0) = x 0 := by
      rw [div_eq_iff hD]
      linear_combination (-(a j 1)) * h1 + (a i 1) * h2
    have e1 : (a i 0 * c j - a j 0 * c i) / (a i 0 * a j 1 - a i 1 * a j 0) = x 1 := by
      rw [div_eq_iff hD]
      linear_combination (-(a i 0)) * h2 + (a j 0) * h1
    ext k
    fin_cases k
    · simpa using e0
    · simpa using e1
  apply Set.Subset.antisymm
  · calc P = closure (convexHull ℝ (P.extremePoints ℝ)) := (closure_convexHull_extremePoints hcomp hconv).symm
      _ ⊆ _ := closure_minimal (convexHull_mono hext) (Set.Finite.isClosed_convexHull (𝕜 := ℝ) (Finset.finite_toSet _))
  · refine convexHull_min ?_ hconv
    intro x hx
    simpa using (Finset.mem_filter.mp hx).2

end QuadFormsKB.Reduction.S8
