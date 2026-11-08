/-
# Gan–Hanke–Yu 2001, §3: units are norms from the unramified quadratic extension, uniformizers are not

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §3, pp. 105–106.

Gan–Hanke–Yu choose the representative $\alpha$ of the discriminant class in $F^\times/NE^\times$ to be a unit or a uniformizer
("with minimum possible valuation"), and Table 1 (odd unitary groups, $E/F$ unramified) distinguishes the rows by
"$\alpha\in A^\times$" / "$\alpha\notin A^\times$", while Prop. 4.4 uses "$\alpha\notin NL_v^\times$". The two agree because for
$E = F(\sqrt\delta)$ unramified over $F$ every unit of $F$ is a norm from $E$ and no uniformizer is, i.e. in terms of the
Hilbert symbol, $(u,\delta) = 1$ for units $u$ and $(\pi,\delta) = -1$ for uniformizers $\pi$ (O'Meara 63:11a). This file
proves that at every finite place of a number field, dyadic places included, for $\delta$ with $F_v(\sqrt\delta)/F_v$
unramified (`Hanke2005.IsUnramSqrt`; nonsquare for the second statement). This is the reading of Table 1 used in
`unitaryGbar` (`LambdaTables.lean`).

*Proof.* $\delta c^2 = \Delta := 1 + 4y$ with $\Delta$ a unit. If $\delta$ is not a square, neither is $\Delta$, and the quadratic
defect of $\Delta$ is contained in $\Delta - 1^2 = 4y\in4\mathfrak o$; by O'Meara 63:2 it is then exactly $4\mathfrak o$ (the other
possible values $\mathfrak p^d\supsetneq 4\mathfrak o$ at dyadic places, $\mathfrak o = 4\mathfrak o$ at non-dyadic places, and $0$ for squares).
Then O'Meara 63:11a (`OMeara.hilbertSymbol_unit_delta`, `OMeara.hilbertSymbol_prime_delta`) applies to $\Delta$, and
$(\cdot,\delta) = (\cdot,\Delta)$ since they differ by a square.
-/
import QuadFormsKB.Literature.Hanke2005.LocalTypesAux
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiThree

set_option linter.unusedSectionVars false

noncomputable section

open NumberField IsDedekindDomain

namespace QuadFormsKB.GanHankeYu2001

open QuadFormsKB.Hanke2005 (IsUnramSqrt)
open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **An unramified nonsquare is a unit of quadratic defect $4\mathfrak o$ times a square** (O'Meara 63:2, 63:3–63:4): if
$F_v(\sqrt\delta)/F_v$ is unramified and $\delta$ is not a square, then $\delta = \Delta c^2$ with $\Delta$ a unit of quadratic defect
$4\mathfrak o$ and $c\ne0$. -/
theorem exists_unit_defect_four_of_isUnramSqrt {δ : Fv} (hδ : IsUnramSqrt v δ) (hns : ¬ IsSquare δ) :
    ∃ Δ : 𝔬, IsUnit Δ ∧ OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) = Submodule.span 𝔬 {(4 : Fv)} ∧
      ∃ c : Fv, c ≠ 0 ∧ δ = (Δ : Fv) * c ^ 2 := by
  obtain ⟨c, hc, y, hu, hδc⟩ := hδ
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  set Δ : 𝔬 := 1 + 4 * y with hΔ
  have hΔF : (Δ : Fv) = 1 + 4 * (y : Fv) := by
    change algebraMap 𝔬 Fv (1 + 4 * y) = _
    rw [map_add, map_mul, map_one, map_ofNat]
    rfl
  have hδeq : δ = (Δ : Fv) * c⁻¹ ^ 2 := by
    rw [hΔF, ← hδc]; field_simp
  have hΔns : ¬ IsSquare (algebraMap 𝔬 Fv Δ) := by
    rintro ⟨s, hs⟩
    apply hns
    refine ⟨s * c⁻¹, ?_⟩
    rw [hδeq]
    change (algebraMap 𝔬 Fv Δ) * c⁻¹ ^ 2 = _
    rw [hs]; ring
  -- the defect is contained in `4𝔬`
  have hle : OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) ≤ Submodule.span 𝔬 {(4 : Fv)} := by
    refine (iInf_le _ 1).trans ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.mem_span_singleton.2 ⟨y, ?_⟩
    change (y : Fv) * 4 = (Δ : Fv) - 1 ^ 2
    rw [hΔF]; ring
  have hbot : OMeara.quadDefect 𝔬 (algebraMap 𝔬 Fv Δ) ≠ ⊥ := fun h =>
    hΔns ((OMeara.isSquare_iff_quadDefect_eq_bot (R := 𝔬) h2ne _).2 h)
  refine ⟨Δ, hu, ?_, c⁻¹, inv_ne_zero hc, hδeq⟩
  by_cases h2 : IsUnit (2 : 𝔬)
  · rcases OMeara.quadDefect_unit_nondyadic (R := 𝔬) (F := Fv) h2 hu with h | h
    · exact absurd h hbot
    · -- `𝔬 = 4𝔬` at a non-dyadic place
      refine le_antisymm hle ?_
      rw [h, Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      exact Submodule.mem_one.2 ⟨4, by rw [hz]; exact map_ofNat (algebraMap 𝔬 Fv) 4⟩
  · rcases OMeara.quadDefect_unit_dyadic (R := 𝔬) (F := Fv) h2ne h2 (NF.irreducible_π v) hu with
      h | h | ⟨d, -, hlt, h⟩
    · exact absurd h hbot
    · exact h
    · exact absurd (h ▸ hle) (not_le_of_gt hlt)

/-- **Gan–Hanke–Yu 2001, §3 / Table 1: a unit is a norm from the unramified quadratic extension** (O'Meara 63:11a): if
$F_v(\sqrt\delta)/F_v$ is unramified (`IsUnramSqrt`), then $(u,\delta)_v = 1$ for every unit $u$ of $\mathfrak o_v$. -/
@[kb "ganhankeyu2001" "§3, p. 105; Table 1, p. 106 (α ∈ A^× iff α ∈ NE^× for E unramified)"]
theorem hilbertSymbol_unit_of_isUnramSqrt {δ : Fv} (hδ : IsUnramSqrt v δ) {u : 𝔬} (hu : IsUnit u) :
    hilbertSymbol Fv (u : Fv) δ = 1 := by
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  by_cases hsq : IsSquare δ
  · obtain ⟨s, hs⟩ := hsq
    have hδ0 : δ ≠ 0 := by
      obtain ⟨c, hc, y, hy, h⟩ := hδ
      intro h0
      rw [h0, zero_mul] at h
      have : ((1 + 4 * y : 𝔬) : Fv) = 0 := by push_cast; exact h.symm
      exact hy.ne_zero (Subtype.ext this)
    have hs0 : s ≠ 0 := by rintro rfl; exact hδ0 (by simpa using hs)
    unfold hilbertSymbol
    classical
    exact (ite_eq_left_iff).2 fun h => absurd ⟨0, 1, s, by simp [hs0], by rw [hs]; ring⟩ h
  · obtain ⟨Δ, hΔu, hΔd, c, hc, rfl⟩ := exists_unit_defect_four_of_isUnramSqrt v hδ hsq
    rw [hilbertSymbol_comm, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm]
    exact OMeara.hilbertSymbol_unit_delta (R := 𝔬) (F := Fv) h2ne hΔu hΔd hu

/-- **Gan–Hanke–Yu 2001, §3 / Table 1: a uniformizer is not a norm from the unramified quadratic extension** (O'Meara 63:11a): if
$F_v(\sqrt\delta)/F_v$ is unramified (`IsUnramSqrt`) and $\delta$ is not a square (so $F_v(\sqrt\delta)$ is a field), then
$(\pi,\delta)_v = -1$ for every prime element $\pi$ of $\mathfrak o_v$. -/
@[kb "ganhankeyu2001" "§3, p. 105; Table 1, p. 106 (α ∈ A^× iff α ∈ NE^× for E unramified)"]
theorem hilbertSymbol_uniformizer_of_isUnramSqrt {δ : Fv} (hδ : IsUnramSqrt v δ) (hns : ¬ IsSquare δ) {π : 𝔬}
    (hπ : Irreducible π) : hilbertSymbol Fv (π : Fv) δ = -1 := by
  have h2ne : (2 : 𝔬) ≠ 0 := NF.two_ne_zero' v
  obtain ⟨Δ, hΔu, hΔd, c, hc, rfl⟩ := exists_unit_defect_four_of_isUnramSqrt v hδ hns
  rw [hilbertSymbol_comm, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm]
  exact OMeara.hilbertSymbol_prime_delta (R := 𝔬) (F := Fv) h2ne hΔu hΔd hπ

end QuadFormsKB.GanHankeYu2001
