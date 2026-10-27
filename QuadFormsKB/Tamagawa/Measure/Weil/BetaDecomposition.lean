/-
# The β-decomposition of the covolume for noncompact `G_∞`

**Layer:** abstract group and measure theory (no topology, no number theory). Generalizes `NeatCovolume.lean`
(`NeatCovolume.lean`), where `Γ ∩ βKβ⁻¹` was trivial (neat level) and `G_∞` compact.

**Setting.** `G = A × B` (`A = G_∞`, `B = G_f`), `Γ ≤ A × B` countable, `K' ≤ B` a measurable subgroup, and
`β : ι → B` (`ι` countable) exact representatives of the double cosets `Γ_f \\ B / K'` (`Γ_f` = image of `Γ` in `B`).
For each `i` put
`Γ_i = {γ ∈ Γ : γ_f ∈ β_i K' β_i⁻¹}` and let `Γ_{β_i} ≤ A` be its image under the projection to `A`.
(In the application `Γ_{β_i}` is the arithmetic group `Γ ∩ (G_∞ × β_iK'β_i⁻¹)` viewed in `G_∞`.)

**Proves** `covolume_eq_measure_mul_tsum_covolume`:
`covol(Γ, A × B, μ_A × μ_B) = μ_B(K') · Σ_{i} covol(Γ_{β_i}, A, μ_A)`,
given exact measurable fundamental domains `D_i` for the `Γ_{β_i}` on `A` (these exist by
`exists_measurableSet_forall_existsUnique_smul_mem` when `Γ_{β_i}` is a discrete subgroup of a second-countable `A`)
and injectivity of `Γ_i → A` (`hinjA`). The fundamental domain is `⊔_i D_i × β_iK'`, exact.

*Recovering `NeatCovolume.lean`:* for a neat level `Γ_i` is trivial, `D_i = A`, and the formula is
`μ_A(A) · μ_B(K') · #ι` (`covolume_eq_of_isNeat_reps`).
-/
import QuadFormsKB.Tamagawa.Measure.NeatCovolume
import QuadFormsKB.Citation

open MeasureTheory MulAction Set
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

section Beta

variable {A B : Type*} [Group A] [Group B] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableMul A] [MeasurableMul B]

/-- The conjugate `b K' b⁻¹` of a subgroup `K'`, as a subgroup of `B`. -/
def conjSub (K' : Subgroup B) (b : B) : Subgroup B where
  carrier := {x | b⁻¹ * x * b ∈ K'}
  mul_mem' := fun {x y} hx hy => by
    have := K'.mul_mem hx hy
    simpa [mul_assoc] using this
  one_mem' := by simp
  inv_mem' := fun {x} hx => by
    have := K'.inv_mem hx
    simpa [mul_assoc] using this

theorem mem_conjSub {K' : Subgroup B} {b x : B} : x ∈ conjSub K' b ↔ b⁻¹ * x * b ∈ K' := Iff.rfl

/-- `Γ_i = {γ ∈ Γ : γ_f ∈ β K' β⁻¹}`, as a subgroup of `A × B`. -/
def levelStab (Γ : Subgroup (A × B)) (K' : Subgroup B) (b : B) : Subgroup (A × B) :=
  Γ ⊓ (conjSub K' b).comap (MonoidHom.snd A B)

/-- `Γ_β ≤ A`: the image of `Γ ∩ (A × βK'β⁻¹)` in `A`. -/
def levelGroup (Γ : Subgroup (A × B)) (K' : Subgroup B) (b : B) : Subgroup A :=
  (levelStab Γ K' b).map (MonoidHom.fst A B)

/-- **The exact fundamental domain** `⊔_i D_i × β_iK'` for `Γ` on `A × B`. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem exists_unique_smul_mem_beta (Γ : Subgroup (A × B)) (K' : Subgroup B)
    {ι : Type*} (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i) (x : A × B) :
    ∃! γ : Γ, γ • x ∈ (⋃ i, D i ×ˢ (β i • (K' : Set B))) := by
  have hmemD : ∀ (γ : Γ) i, γ • x ∈ D i ×ˢ (β i • (K' : Set B)) ↔
      (γ : A × B).1 * x.1 ∈ D i ∧ ∃ k ∈ K', (γ : A × B).2 * x.2 = β i * k := by
    intro γ i
    simp only [mem_prod, mem_smul_set, SetLike.mem_coe, smul_eq_mul]
    show _ ∧ (∃ k ∈ K', β i * k = (γ : A × B).2 * x.2) ↔ _
    exact and_congr Iff.rfl ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩
  -- uniqueness
  have uniq : ∀ ε₁ ε₂ : Γ, ε₁ • x ∈ (⋃ i, D i ×ˢ (β i • (K' : Set B))) →
      ε₂ • x ∈ (⋃ i, D i ×ˢ (β i • (K' : Set B))) → ε₁ = ε₂ := by
    intro ε₁ ε₂ h1 h2
    obtain ⟨i₁, h1⟩ := mem_iUnion.mp h1
    obtain ⟨i₂, h2⟩ := mem_iUnion.mp h2
    obtain ⟨hD1, k₁, hk₁, e₁⟩ := (hmemD ε₁ i₁).mp h1
    obtain ⟨hD2, k₂, hk₂, e₂⟩ := (hmemD ε₂ i₂).mp h2
    have hζ : ((ε₂ : A × B) * (ε₁ : A × B)⁻¹) ∈ Γ := Γ.mul_mem ε₂.2 (Γ.inv_mem ε₁.2)
    have hζ2 : ((ε₂ : A × B) * (ε₁ : A × B)⁻¹).2 * β i₁ * k₁ = β i₂ * k₂ := by
      rw [mul_assoc, ← e₁, ← e₂]; simp only [Prod.snd_mul, Prod.snd_inv]; group
    obtain rfl := hdisj i₁ i₂ _ hζ k₁ hk₁ k₂ hk₂ hζ2
    set ζ : A × B := (ε₂ : A × B) * (ε₁ : A × B)⁻¹ with hζdef
    have hζS : ζ ∈ levelStab Γ K' (β i₁) := by
      refine ⟨hζ, ?_⟩
      show (β i₁)⁻¹ * ζ.2 * β i₁ ∈ K'
      have : (β i₁)⁻¹ * ζ.2 * β i₁ = k₂ * k₁⁻¹ := by
        rw [show ζ.2 = β i₁ * k₂ * k₁⁻¹ * (β i₁)⁻¹ by rw [← hζ2]; group]; group
      rw [this]; exact K'.mul_mem hk₂ (K'.inv_mem hk₁)
    have hζA : ζ.1 * ((ε₁ : A × B).1 * x.1) = (ε₂ : A × B).1 * x.1 := by
      simp only [ζ, Prod.fst_mul, Prod.fst_inv]; group
    let t : levelGroup Γ K' (β i₁) := ⟨ζ.1, Subgroup.mem_map.mpr ⟨ζ, hζS, rfl⟩⟩
    obtain ⟨s₀, -, hs₀⟩ := hD i₁ ((ε₁ : A × B).1 * x.1)
    have ht : t = s₀ := hs₀ t (by show ζ.1 * _ ∈ D i₁; rw [hζA]; exact hD2)
    have h1' : (1 : levelGroup Γ K' (β i₁)) = s₀ := hs₀ 1 (by show (1 : A) * _ ∈ D i₁; rw [one_mul]; exact hD1)
    have hζ1 : ζ.1 = 1 := congrArg Subtype.val (ht.trans h1'.symm)
    have hζ1' : ζ = 1 := hinjA i₁ ζ hζS hζ1
    apply Subtype.ext
    have := mul_inv_eq_one.mp hζ1'
    exact this.symm
  obtain ⟨i, γ, hγ, k, hk, hx⟩ := hcov x.2
  obtain ⟨s, hs, -⟩ := hD i ((γ⁻¹ : A × B).1 * x.1)
  obtain ⟨δ, hδ, hδs⟩ := Subgroup.mem_map.mp s.2
  have hε : δ * γ⁻¹ ∈ Γ := Γ.mul_mem hδ.1 (Γ.inv_mem hγ)
  have hmem : (⟨δ * γ⁻¹, hε⟩ : Γ) • x ∈ (⋃ i, D i ×ˢ (β i • (K' : Set B))) := by
    refine mem_iUnion.mpr ⟨i, (hmemD _ i).mpr ⟨?_, (β i)⁻¹ * δ.2 * β i * k, ?_, ?_⟩⟩
    · show (δ * γ⁻¹).1 * x.1 ∈ D i
      have : (δ * γ⁻¹).1 * x.1 = (s : A) * ((γ⁻¹ : A × B).1 * x.1) := by
        rw [← hδs]; simp [mul_assoc]
      rw [this]; exact hs
    · exact K'.mul_mem hδ.2 hk
    · show (δ * γ⁻¹).2 * x.2 = β i * ((β i)⁻¹ * δ.2 * β i * k)
      rw [hx]; simp only [Prod.snd_mul, Prod.snd_inv]; group
  exact ⟨⟨δ * γ⁻¹, hε⟩, hmem, fun ε' h' => uniq ε' _ h' hmem⟩

/-- **The β-decomposition of the covolume** (generalizing `covolume_eq_of_isNeat_reps` to noncompact `G_∞`).
Let `Γ ≤ A × B` be countable, `K' ≤ B` measurable, `β : ι → B` (`ι` countable) exact representatives of the double
cosets `Γ_f \ B / K'` (`hcov`, `hdisj`), `Γ_i → A` injective (`hinjA`), and `D_i` an exact measurable fundamental
domain for `Γ_{β_i} = levelGroup Γ K' β_i` on `A`. Then for left-invariant s-finite measures
`covol(Γ, A × B, μ_A × μ_B) = μ_B(K') · Σ_i covol(Γ_{β_i}, A, μ_A)`. -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) = vol(G_𝔸/G_k)); finiteness via mean value"]
theorem covolume_eq_measure_mul_tsum_covolume (Γ : Subgroup (A × B)) [Countable Γ] (K' : Subgroup B)
    (hK' : MeasurableSet (K' : Set B)) {ι : Type*} [Countable ι] (β : ι → B)
    (hcov : ∀ g : B, ∃ i, ∃ γ ∈ Γ, ∃ k ∈ K', g = γ.2 * β i * k)
    (hdisj : ∀ i j, ∀ γ ∈ Γ, ∀ k ∈ K', ∀ k' ∈ K', γ.2 * β i * k = β j * k' → i = j)
    (hinjA : ∀ i, ∀ γ ∈ levelStab Γ K' (β i), γ.1 = 1 → γ = 1)
    (D : ι → Set A) (hDm : ∀ i, MeasurableSet (D i))
    (hD : ∀ i (a : A), ∃! s : levelGroup Γ K' (β i), s • a ∈ D i)
    (μA : Measure A) (μB : Measure B) [SFinite μA] [SFinite μB] [μA.IsMulLeftInvariant]
    [μB.IsMulLeftInvariant] [∀ i, Countable (levelGroup Γ K' (β i))]
    [∀ i, SMulInvariantMeasure (levelGroup Γ K' (β i)) A μA]
    [∀ i, MeasurableConstSMul (levelGroup Γ K' (β i)) A] :
    covolume Γ (A × B) (μA.prod μB) = μB K' * ∑' i, covolume (levelGroup Γ K' (β i)) A μA := by
  have hdom : IsFundamentalDomain Γ (⋃ i, D i ×ˢ (β i • (K' : Set B))) (μA.prod μB) :=
    IsFundamentalDomain.mk'
      (MeasurableSet.iUnion fun i => (hDm i).prod (hK'.const_smul (β i))).nullMeasurableSet
      (exists_unique_smul_mem_beta Γ K' β hcov hdisj hinjA D hD)
  have hdisjSet : Pairwise (Function.onFun Disjoint fun i => D i ×ˢ (β i • (K' : Set B))) := by
    intro i j hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ⟨a, b⟩ ⟨-, k, hk, rfl⟩ ⟨-, k', hk', hb⟩
    exact hne (hdisj i j 1 Γ.one_mem k hk k' hk' (by simpa using hb.symm))
  have hcovD : ∀ i, covolume (levelGroup Γ K' (β i)) A μA = μA (D i) := fun i =>
    (IsFundamentalDomain.mk' (hDm i).nullMeasurableSet (hD i)).covolume_eq_volume μA
  rw [hdom.covolume_eq_volume, measure_iUnion hdisjSet
    (fun i => (hDm i).prod (hK'.const_smul (β i))), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [hcovD, Measure.prod_prod, measure_smul, mul_comm]

end Beta

end QuadFormsKB.Tamagawa.Measure.Weil
