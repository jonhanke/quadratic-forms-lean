/-
# Counting orbits: transport along an equivariant bijection, and independence of the double coset representative

**Layer:** abstract group actions (the setting of `ThetaUnfold.lean`).

* `orbitQuotEquiv`: a bijection $f : S \simeq T$ under which "same $G$-orbit" corresponds to "same $H$-orbit" induces a
  bijection of the orbit spaces $G\backslash S \simeq H\backslash T$.
* **`tsum_orbits_repSet_eq`**: the number of orbits of the unit group $\Gamma_b$ = `levelGroup Γ K' b` on the
  representations $S_b$ = `repSet … b` depends only on the double coset $\Gamma_f\,b\,K'$: for $b' = \gamma_fbk$
  ($\gamma\in\Gamma$, $k\in K'$), $y\mapsto\gamma_\infty y$ carries $S_b$ onto $S_{b'}$ and $\Gamma_b$-orbits onto
  $\Gamma_{b'}$-orbits ($\Gamma_{b'} = \gamma_\infty\Gamma_b\gamma_\infty^{-1}$).
-/
import QuadFormsKB.Tamagawa.Indefinite.ThetaUnfold

open MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

/-- **Orbit spaces along a bijection that matches the orbit relations.** -/
def orbitQuotEquiv {G H S T : Type*} [Group G] [MulAction G S] [Group H] [MulAction H T] (f : S ≃ T)
    (hf : ∀ s s' : S, (∃ g : G, g • s' = s) ↔ ∃ h : H, h • f s' = f s) :
    orbitRel.Quotient G S ≃ orbitRel.Quotient H T :=
  Quotient.congr f fun s s' => by
    show s ∈ orbit G s' ↔ f s ∈ orbit H (f s')
    simp only [mem_orbit_iff]
    exact hf s s'

/-- The number of orbits is preserved by `orbitQuotEquiv`. -/
theorem tsum_orbitQuot_eq {G H S T : Type*} [Group G] [MulAction G S] [Group H] [MulAction H T] (f : S ≃ T)
    (hf : ∀ s s' : S, (∃ g : G, g • s' = s) ↔ ∃ h : H, h • f s' = f s) :
    (∑' _ : orbitRel.Quotient G S, (1 : ℝ≥0∞)) = ∑' _ : orbitRel.Quotient H T, (1 : ℝ≥0∞) :=
  (orbitQuotEquiv f hf).tsum_eq (fun _ => (1 : ℝ≥0∞))

section RepSet

variable {A B : Type*} [Group A] [Group B] {Γ : Subgroup (A × B)} {X : Type*} [MulAction Γ X]
  {Y : Type*} [MulAction A Y] {Yf : Type*} [MulAction B Yf]
  {jA : X → Y} {jB : X → Yf} (hjA : ∀ (γ : Γ) η, jA (γ • η) = (γ : A × B).1 • jA η)
  (hjB : ∀ (γ : Γ) η, jB (γ • η) = (γ : A × B).2 • jB η) {K' : Subgroup B} {Λ : Set Yf}
  (hΛ : ∀ k ∈ K', ∀ y, k • y ∈ Λ ↔ y ∈ Λ)

theorem mem_levelGroup_iff {K' : Subgroup B} (b : B) (a : A) :
    a ∈ levelGroup Γ K' b ↔ ∃ g ∈ Γ, g.1 = a ∧ b⁻¹ * g.2 * b ∈ K' := by
  constructor
  · rintro ⟨g, ⟨hg, hgK⟩, rfl⟩
    exact ⟨g, hg, rfl, hgK⟩
  · rintro ⟨g, hg, rfl, hgK⟩
    exact ⟨g, ⟨hg, hgK⟩, rfl⟩

include hjA hjB hΛ in
/-- `γ_∞` carries $S_b$ into $S_{\gamma_f b k}$. -/
theorem smul_mem_repSet {b : B} {γ : A × B} (hγ : γ ∈ Γ) {k : B} (hk : k ∈ K') {y : Y}
    (hy : y ∈ repSet hjA hjB hΛ b) : γ.1 • y ∈ repSet hjA hjB hΛ (γ.2 * b * k) := by
  obtain ⟨η, hη, rfl⟩ := hy
  refine ⟨(⟨γ, hγ⟩ : Γ) • η, ?_, hjA _ η⟩
  obtain ⟨z, hz, hzη⟩ := hη
  refine ⟨k⁻¹ • z, (hΛ k hk _).1 (by rwa [smul_inv_smul]), ?_⟩
  show (γ.2 * b * k) • k⁻¹ • z = jB ((⟨γ, hγ⟩ : Γ) • η)
  rw [hjB, ← hzη, smul_smul, mul_inv_cancel_right, mul_smul]

include hjA hjB hΛ in
/-- **The count of orbits on the representations depends only on the double coset.** -/
theorem tsum_orbits_repSet_eq (b : B) {γ : A × B} (hγ : γ ∈ Γ) {k : B} (hk : k ∈ K') :
    (∑' _ : orbitRel.Quotient (levelGroup Γ K' (γ.2 * b * k)) (repSet hjA hjB hΛ (γ.2 * b * k)), (1 : ℝ≥0∞)) =
      ∑' _ : orbitRel.Quotient (levelGroup Γ K' b) (repSet hjA hjB hΛ b), (1 : ℝ≥0∞) := by
  set b' := γ.2 * b * k with hb'
  have hγi : γ⁻¹ ∈ Γ := Γ.inv_mem hγ
  have hb : b = γ⁻¹.2 * b' * k⁻¹ := by
    rw [hb', Prod.snd_inv]; group
  have hki : k⁻¹ ∈ K' := K'.inv_mem hk
  -- the bijection `y ↦ γ_∞⁻¹ y` from `S_{b'}` to `S_b`
  let f : repSet hjA hjB hΛ b' ≃ repSet hjA hjB hΛ b :=
    { toFun := fun y => ⟨γ⁻¹.1 • (y : Y), by
        have := smul_mem_repSet hjA hjB hΛ hγi hki y.2
        rwa [← hb] at this⟩
      invFun := fun y => ⟨γ.1 • (y : Y), smul_mem_repSet hjA hjB hΛ hγ hk y.2⟩
      left_inv := fun y => Subtype.ext (by
        show γ.1 • γ⁻¹.1 • (y : Y) = y
        rw [smul_smul, Prod.fst_inv, mul_inv_cancel, one_smul])
      right_inv := fun y => Subtype.ext (by
        show γ⁻¹.1 • γ.1 • (y : Y) = y
        rw [smul_smul, Prod.fst_inv, inv_mul_cancel, one_smul]) }
  refine tsum_orbitQuot_eq f fun s s' => ?_
  constructor
  · rintro ⟨⟨a, ha⟩, hs⟩
    obtain ⟨g, hg, rfl, hgK⟩ := (mem_levelGroup_iff b' a).1 ha
    refine ⟨⟨(γ⁻¹ * g * γ).1, (mem_levelGroup_iff b _).2 ⟨γ⁻¹ * g * γ, Γ.mul_mem (Γ.mul_mem hγi hg) hγ, rfl, ?_⟩⟩,
      Subtype.ext ?_⟩
    · have e : b⁻¹ * (γ⁻¹ * g * γ).2 * b = k * (b'⁻¹ * g.2 * b') * k⁻¹ := by
        rw [hb', Prod.snd_mul, Prod.snd_mul, Prod.snd_inv]; group
      rw [e]
      exact K'.mul_mem (K'.mul_mem hk hgK) hki
    · have hs' : g.1 • (s' : Y) = s := congrArg Subtype.val hs
      show (γ⁻¹ * g * γ).1 • γ⁻¹.1 • (s' : Y) = γ⁻¹.1 • (s : Y)
      rw [← hs', smul_smul, smul_smul, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv]
      group
  · rintro ⟨⟨a, ha⟩, hs⟩
    obtain ⟨g, hg, rfl, hgK⟩ := (mem_levelGroup_iff b a).1 ha
    refine ⟨⟨(γ * g * γ⁻¹).1, (mem_levelGroup_iff b' _).2 ⟨γ * g * γ⁻¹, Γ.mul_mem (Γ.mul_mem hγ hg) hγi, rfl, ?_⟩⟩,
      Subtype.ext ?_⟩
    · have e : b'⁻¹ * (γ * g * γ⁻¹).2 * b' = k⁻¹ * (b⁻¹ * g.2 * b) * k := by
        rw [hb', Prod.snd_mul, Prod.snd_mul, Prod.snd_inv]; group
      rw [e]
      exact K'.mul_mem (K'.mul_mem hki hgK) hk
    · have hs' : g.1 • γ⁻¹.1 • (s' : Y) = γ⁻¹.1 • (s : Y) := congrArg Subtype.val hs
      show (γ * g * γ⁻¹).1 • (s' : Y) = s
      have := congrArg (fun y => γ.1 • y) hs'
      simp only [smul_smul, Prod.fst_inv, mul_inv_cancel, one_smul] at this
      rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← this, mul_smul, mul_smul, mul_smul, mul_smul]

end RepSet

end QuadFormsKB.Tamagawa.Indefinite
