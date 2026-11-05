/-
# O'Meara §93, pp. 250–251: the relations $\cong$ and $\cong \bmod \mathfrak a$

**Proves** (O'Meara 1963, §93, pp. 250–251)
* `SqEquiv.refl`, `SqEquiv.symm`, `SqEquiv.trans`: $\cong$ is an equivalence relation;
* `SqEquivMod.refl`, `SqEquivMod.symm`, `SqEquivMod.trans`: $\cong \bmod \mathfrak a$ is an equivalence relation;
* `sqEquiv_iff_unit_quadDefect_eq_bot`: $\alpha \cong \beta$ iff $\alpha/\beta \in \mathfrak u$ and $\mathfrak d(\alpha/\beta) = 0$;
* `sqEquivMod_iff_unit_quadDefect_le`: $\alpha \cong \beta \bmod \mathfrak a$ iff $\alpha/\beta \in \mathfrak u$ and
  $\mathfrak d(\alpha/\beta) \subseteq \beta^{-1}\mathfrak a$;
* `sqEquivMod_smul_maximalIdeal`: $\alpha \cong \beta \bmod \alpha\mathfrak p$ whenever $\alpha/\beta \in \mathfrak u$
  ($F$ dyadic with finite residue field).

**Added hypotheses.** The two characterizations by the quadratic defect assume `[HenselianLocalRing R]` and
`(h2 : (2 : R) ≠ 0)`: "$\mathfrak d(\xi) = 0 \Rightarrow \xi \in F^2$" (`isSquare_iff_quadDefect_eq_bot`) is false for a
non-complete $R$ (e.g. $17 \in \mathbb Q$ in $R = \mathbb Z_{(2)}$ has defect $0$ but is not a square). The
hypotheses "$\mathfrak a \ne 0$, $\mathfrak a$ finitely generated" of the book are not needed.
-/
import QuadFormsKB.Literature.OMeara.Sec93Gap3

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Equiv

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]

/-- **$\cong$ is reflexive** (O'Meara 1963, §93, p. 250): $\alpha \cong \alpha$ ($\varepsilon = 1$). -/
@[kb "omeara1963" "§93, p. 250 (≅ is an equivalence relation)"]
theorem SqEquiv.refl (α : F) : SqEquiv (R := R) α α :=
  ⟨1, isUnit_one, by simp⟩

/-- **$\cong$ is symmetric** (O'Meara 1963, §93, p. 250): $\alpha \cong \beta \Rightarrow \beta \cong \alpha$
(replace $\varepsilon$ by $\varepsilon^{-1}$). -/
@[kb "omeara1963" "§93, p. 250 (≅ is an equivalence relation)"]
theorem SqEquiv.symm {α β : F} (h : SqEquiv (R := R) α β) : SqEquiv (R := R) β α := by
  obtain ⟨ε, ⟨e, rfl⟩, h⟩ := h
  refine ⟨↑e⁻¹, (e⁻¹).isUnit, ?_⟩
  have hf : algebraMap R F ↑e⁻¹ * algebraMap R F ↑e = 1 := by
    rw [← map_mul]; simp
  rw [h]
  linear_combination (-β * (algebraMap R F ↑e⁻¹ * algebraMap R F ↑e + 1)) * hf

/-- **$\cong$ is transitive** (O'Meara 1963, §93, p. 250): $\alpha \cong \beta$, $\beta \cong \gamma \Rightarrow
\alpha \cong \gamma$ ($\varepsilon = \varepsilon_1\varepsilon_2$). -/
@[kb "omeara1963" "§93, p. 250 (≅ is an equivalence relation)"]
theorem SqEquiv.trans {α β γ : F} (h₁ : SqEquiv (R := R) α β) (h₂ : SqEquiv (R := R) β γ) :
    SqEquiv (R := R) α γ := by
  obtain ⟨ε, hε, h₁⟩ := h₁
  obtain ⟨δ, hδ, h₂⟩ := h₂
  refine ⟨ε * δ, hε.mul hδ, ?_⟩
  rw [h₁, h₂, map_mul]; ring

/-- **$\cong \bmod \mathfrak a$ is reflexive** (O'Meara 1963, §93, p. 250). -/
@[kb "omeara1963" "§93, p. 250 (≅ mod a is an equivalence relation)"]
theorem SqEquivMod.refl (a : Submodule R F) (α : F) : SqEquivMod a α α :=
  ⟨⟨1, isUnit_one, by simp⟩, 1, isUnit_one, by simp⟩

/-- **$\cong \bmod \mathfrak a$ is symmetric** (O'Meara 1963, §93, p. 250): from
$\alpha - \beta\varepsilon^2 \in \mathfrak a$ one gets $\beta - \alpha\varepsilon^{-2} = -\varepsilon^{-2}(\alpha -
\beta\varepsilon^2) \in \mathfrak a$. -/
@[kb "omeara1963" "§93, p. 250 (≅ mod a is an equivalence relation)"]
theorem SqEquivMod.symm {a : Submodule R F} {α β : F} (h : SqEquivMod a α β) : SqEquivMod a β α := by
  obtain ⟨⟨u, ⟨f, rfl⟩, h₁⟩, ε, ⟨e, rfl⟩, h₂⟩ := h
  have hf : algebraMap R F ↑f⁻¹ * algebraMap R F ↑f = 1 := by rw [← map_mul]; simp
  have he : algebraMap R F ↑e⁻¹ * algebraMap R F ↑e = 1 := by rw [← map_mul]; simp
  refine ⟨⟨↑f⁻¹, (f⁻¹).isUnit, by rw [h₁]; linear_combination (-β) * hf⟩, ↑e⁻¹, (e⁻¹).isUnit, ?_⟩
  have := a.smul_mem (-((↑e⁻¹ : R) ^ 2)) h₂
  rw [Algebra.smul_def] at this
  convert this using 1
  simp only [map_neg, map_pow]
  linear_combination (-β * (algebraMap R F ↑e⁻¹ * algebraMap R F ↑e + 1)) * he

/-- **$\cong \bmod \mathfrak a$ is transitive** (O'Meara 1963, §93, p. 250):
$\alpha - \gamma(\varepsilon\delta)^2 = (\alpha - \beta\varepsilon^2) + \varepsilon^2(\beta - \gamma\delta^2)$. -/
@[kb "omeara1963" "§93, p. 250 (≅ mod a is an equivalence relation)"]
theorem SqEquivMod.trans {a : Submodule R F} {α β γ : F} (h₁ : SqEquivMod a α β) (h₂ : SqEquivMod a β γ) :
    SqEquivMod a α γ := by
  obtain ⟨⟨u, hu, hu'⟩, ε, hε, h₃⟩ := h₁
  obtain ⟨⟨v, hv, hv'⟩, δ, hδ, h₄⟩ := h₂
  refine ⟨⟨u * v, hu.mul hv, by rw [hu', hv', map_mul]; ring⟩, ε * δ, hε.mul hδ, ?_⟩
  have := a.smul_mem (ε ^ 2) h₄
  rw [Algebra.smul_def] at this
  have := a.add_mem h₃ this
  convert this using 1
  simp only [map_mul, map_pow]; ring

end Equiv

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

private lemma isUnit_of_sq_unit {δ u : R} (hu : IsUnit u) (h : algebraMap R F δ ^ 2 = algebraMap R F u) :
    IsUnit δ := by
  have : δ ^ 2 = u := IsFractionRing.injective R F (by simpa using h)
  exact (isUnit_pow_iff two_ne_zero).1 (this ▸ hu)

private lemma exists_nonunit_of_mem {N : Submodule R F} (h1 : (1 : F) ∉ N) {x : F} (hx : x ∈ N) :
    ∃ r ∈ IsLocalRing.maximalIdeal R, algebraMap R F r = x := by
  by_cases x0 : x = 0
  · exact ⟨0, zero_mem _, by simp [x0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hd : 1 ≤ dord hπ x := by
    by_contra hlt
    have hi : 0 ≤ dord hπ x⁻¹ := by rw [B63.dord_inv' hπ x0]; omega
    obtain ⟨s, hs⟩ := exists_alg_of_nonneg hπ (inv_ne_zero x0) hi
    apply h1
    have := N.smul_mem s hx
    rwa [Algebra.smul_def, hs, inv_mul_cancel₀ x0] at this
  exact exists_max_of_pos hπ x0 hd

/-- **$\alpha \cong \beta$ iff $\alpha/\beta \in \mathfrak u$ and $\mathfrak d(\alpha/\beta) = 0$**
(O'Meara 1963, §93, p. 250), for $\alpha, \beta \ne 0$. Needs `HenselianLocalRing R` and $2 \ne 0$ in $R$
(see the file header). -/
@[kb "omeara1963" "§93, p. 250 (α ≅ β iff α/β is a unit with quadratic defect 0)"]
theorem sqEquiv_iff_unit_quadDefect_eq_bot [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) {α β : F}
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    SqEquiv (R := R) α β ↔
      (∃ u : R, IsUnit u ∧ α / β = algebraMap R F u) ∧ quadDefect R (α / β) = ⊥ := by
  constructor
  · rintro ⟨ε, hε, rfl⟩
    have e : algebraMap R F ε ^ 2 * β / β = algebraMap R F (ε ^ 2) := by
      rw [map_pow]; field_simp
    rw [e]
    exact ⟨⟨_, hε.pow 2, rfl⟩,
      (isSquare_iff_quadDefect_eq_bot h2 _).1 ⟨algebraMap R F ε, by rw [map_pow]; ring⟩⟩
  · rintro ⟨⟨u, hu, hu'⟩, hd⟩
    obtain ⟨η, hη⟩ := (isSquare_iff_quadDefect_eq_bot h2 _).2 hd
    rw [hu'] at hη
    obtain ⟨δ, rfl⟩ := exists_alg_of_sq (R := R) (η := η) (c := u) (by rw [hη]; ring)
    refine ⟨δ, isUnit_of_sq_unit hu (by rw [hη]; ring), ?_⟩
    have : α = algebraMap R F u * β := by rw [← hu']; field_simp
    rw [this, hη]; ring

/-- **$\alpha \cong \beta \bmod \mathfrak a$ iff $\alpha/\beta \in \mathfrak u$ and
$\mathfrak d(\alpha/\beta) \subseteq \beta^{-1}\mathfrak a$** (O'Meara 1963, §93, pp. 250–251), for
$\alpha, \beta \ne 0$ and $\mathfrak a$ an $R$-submodule of $F$ (the book's hypotheses "$\mathfrak a$ a nonzero
fractional ideal" are not needed). Needs `HenselianLocalRing R` and $2 \ne 0$ in $R$ for "$\Leftarrow$" (the
defect is attained). -/
@[kb "omeara1963" "§93, pp. 250–251 (α ≅ β mod a iff α/β is a unit with 𝔡(α/β) ⊆ a/β)"]
theorem sqEquivMod_iff_unit_quadDefect_le [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) (a : Submodule R F)
    {α β : F} (_hα : α ≠ 0) (hβ : β ≠ 0) :
    SqEquivMod a α β ↔
      (∃ u : R, IsUnit u ∧ α / β = algebraMap R F u) ∧ quadDefect R (α / β) ≤ β⁻¹ • a := by
  have key : ∀ ε : R, α - β * algebraMap R F ε ^ 2 ∈ a ↔ α / β - algebraMap R F ε ^ 2 ∈ β⁻¹ • a := by
    intro ε
    rw [mem_smul_pointwise_iff_exists]
    constructor
    · intro h; exact ⟨_, h, by simp only [smul_eq_mul]; field_simp⟩
    · rintro ⟨s, hs, e⟩
      have h1 : α - β * algebraMap R F ε ^ 2 = β * (α / β - algebraMap R F ε ^ 2) := by field_simp
      have h3 : β * (β⁻¹ * s) = s := by field_simp
      rw [h1, ← e, smul_eq_mul, h3]; exact hs
  have hu : (∃ u : R, IsUnit u ∧ α = algebraMap R F u * β) ↔
      ∃ u : R, IsUnit u ∧ α / β = algebraMap R F u := by
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [div_eq_iff hβ]
  constructor
  · rintro ⟨h1, ε, hε, h3⟩
    refine ⟨hu.1 h1, ?_⟩
    exact (iInf_le _ (algebraMap R F ε)).trans ((Submodule.span_singleton_le_iff_mem _ _).2 ((key ε).1 h3))
  · rintro ⟨h1, hd⟩
    refine ⟨hu.2 h1, ?_⟩
    obtain ⟨u, hu1, hu2⟩ := h1
    obtain ⟨η, hη⟩ := exists_quadDefect_eq h2 (α / β)
    have hx : α / β - η ^ 2 ∈ β⁻¹ • a := by
      apply hd; rw [← hη]; exact Submodule.mem_span_singleton_self _
    by_cases h1N : (1 : F) ∈ β⁻¹ • a
    · refine ⟨1, isUnit_one, (key 1).2 ?_⟩
      rw [map_one, one_pow, hu2]
      have : ∀ r : R, algebraMap R F r ∈ β⁻¹ • a := fun r => by
        simpa [Algebra.smul_def] using (β⁻¹ • a).smul_mem r h1N
      exact (β⁻¹ • a).sub_mem (this u) h1N
    · obtain ⟨r, hr, hr'⟩ := exists_nonunit_of_mem h1N hx
      have hsq : η ^ 2 = algebraMap R F (u - r) := by
        rw [map_sub, hr', ← hu2]; ring
      obtain ⟨δ, hδ⟩ := exists_alg_of_sq hsq
      have hunit : IsUnit (u - r) := by
        by_contra hnu
        have h5 : u - r ∈ IsLocalRing.maximalIdeal R := hnu
        have h6 : u ∈ IsLocalRing.maximalIdeal R := by simpa using add_mem h5 hr
        exact h6 hu1
      refine ⟨δ, isUnit_of_sq_unit hunit (by rw [hδ]; exact hsq), (key δ).2 ?_⟩
      rw [hδ]; exact hx

/-- **$\alpha \cong \beta \bmod \alpha\mathfrak p$ when $\alpha/\beta \in \mathfrak u$** (O'Meara 1963, §93, p. 251),
for $F$ dyadic ($2 \in \mathfrak p$) with finite residue field (so perfect of characteristic $2$: $u \equiv \delta^2
\bmod \mathfrak p$ for some unit $\delta$). -/
@[kb "omeara1963" "§93, p. 251 (α ≅ β mod α𝔭 when α/β ∈ 𝔲)"]
theorem sqEquivMod_smul_maximalIdeal [Finite (ResidueField R)] (h2p : ¬ IsUnit (2 : R)) {α β : F}
    (_hα : α ≠ 0) (h : ∃ u : R, IsUnit u ∧ α / β = algebraMap R F u) :
    SqEquivMod (α • Submodule.map (Algebra.linearMap R F) (IsLocalRing.maximalIdeal R)) α β := by
  obtain ⟨u, hu, h⟩ := h
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [div_zero] at h
    exact alg_ne_zero_of_unit hu h.symm
  have hα' : α = algebraMap R F u * β := (div_eq_iff hβ).1 h
  obtain ⟨y, hy⟩ := exists_sq_mod h2p u
  have hyu : IsUnit y := by
    by_contra hny
    have h5 : y ∈ IsLocalRing.maximalIdeal R := hny
    have h6 : u ∈ IsLocalRing.maximalIdeal R := by
      simpa using add_mem hy ((IsLocalRing.maximalIdeal R).pow_mem_of_mem h5 2 (by norm_num))
    exact h6 hu
  refine ⟨⟨u, hu, hα'⟩, y, hyu, ?_⟩
  rw [mem_smul_pointwise_iff_exists]
  have hw : algebraMap R F ((hu.unit⁻¹ : Rˣ) : R) * algebraMap R F u = 1 := by
    rw [← map_mul]; simp
  refine ⟨algebraMap R F (((hu.unit⁻¹ : Rˣ) : R) * (u - y ^ 2)),
    Submodule.mem_map.2 ⟨_, (IsLocalRing.maximalIdeal R).mul_mem_left _ hy, rfl⟩, ?_⟩
  simp only [smul_eq_mul, map_mul, map_sub, map_pow]
  linear_combination
    (algebraMap R F ((hu.unit⁻¹ : Rˣ) : R) * (algebraMap R F u - algebraMap R F y ^ 2) - 1) * hα' +
    (β * (algebraMap R F u - algebraMap R F y ^ 2)) * hw

end DVR

end QuadFormsKB.OMeara
