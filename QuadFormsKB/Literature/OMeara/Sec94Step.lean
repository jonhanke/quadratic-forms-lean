/-
# O'Meara §94: the two splitting steps from a base

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring (O'Meara's $\mathfrak o$, maximal ideal
$\mathfrak p$) with fraction field $F$, $2 \ne 0$ in $F$, a quadratic space $(V, Q)$ over $F$ with O'Meara's bilinear
form $B$ = `bil Q`, lattices = `Submodule R V`, $\mathfrak sL$ = `scale Q L`.

**Proves** the two steps of the procedure of §94 (O'Meara 1973 printing, pp. 279–280) that split off a component of
a lattice $L$ from a base, in the form of explicit corrections of a vector $x \in L$:
* `exists_orth_step_one` (p. 279): if $Q(x_1)\mathfrak o = \mathfrak sL$ then $B(x_1, x)/Q(x_1) \in \mathfrak o$ and
  $y = x - \frac{B(x_1, x)}{Q(x_1)}x_1 \in L$ is orthogonal to $x_1$;
* `exists_orth_step_two` (pp. 279–280, the dyadic case): if $B(x_1, x_2)\mathfrak o = \mathfrak sL$ and
  $Q(x_1)\mathfrak o, Q(x_2)\mathfrak o \subsetneq \mathfrak sL$, then for every $x \in L$ the equations
  $$B(x_1, x) + \xi Q(x_1) + \eta B(x_1, x_2) = 0, \qquad B(x_2, x) + \xi B(x_1, x_2) + \eta Q(x_2) = 0$$
  have integral solutions $\xi, \eta$, and $y = x + \xi x_1 + \eta x_2 \in L$ is orthogonal to $x_1$ and $x_2$.
Applied to the base vectors $x = x_j$ these give O'Meara's base $x_1, y_2, \dots, y_n$ (resp. $x_1, x_2, y_3, \dots,
y_n$) and the splittings $L = \mathfrak ox_1 \perp (\mathfrak oy_2 + \cdots)$, resp.
$L = (\mathfrak ox_1 + \mathfrak ox_2) \perp (\mathfrak oy_3 + \cdots)$; the splittings themselves are
`OMeara.splits_of_isModular_of_scale_eq` (82:15a) and, in Gram-matrix form, `LocalDensity.DVR.dvr_stepGen`.
-/
import QuadFormsKB.Literature.OMeara.Sec94Norm

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The first splitting step of §94** (O'Meara 1973, p. 279): if $x_1 \in L$ has $Q(x_1)\mathfrak o = \mathfrak sL$
then for every $x \in L$, $c = B(x_1, x)/Q(x_1) \in \mathfrak o$ and $y = x - cx_1 \in L$ satisfies $B(x_1, y) = 0$. -/
@[kb "omeara1963" "§94, p. 279 (Q(x₁)o = sL: y_j = x_j − B(x₁, x_j)Q(x₁)⁻¹x₁ is orthogonal to x₁)"]
theorem exists_orth_step_one {L : Submodule R V} {x₁ : V} (hx₁ : x₁ ∈ L) (hQ : R ∙ Q x₁ = scale Q L)
    (hQ0 : Q x₁ ≠ 0) {x : V} (hx : x ∈ L) :
    ∃ c : R, algebraMap R F c = bil Q x₁ x / Q x₁ ∧ x - c • x₁ ∈ L ∧ bil Q x₁ (x - c • x₁) = 0 := by
  have hB : bil Q x₁ x ∈ R ∙ Q x₁ := hQ ▸ bil_mem_scale Q hx₁ hx
  obtain ⟨c, hc⟩ := mem_span_singleton.mp hB
  have hcF : algebraMap R F c = bil Q x₁ x / Q x₁ := by
    rw [eq_div_iff hQ0, ← hc, Algebra.smul_def]
  refine ⟨c, hcF, L.sub_mem hx (L.smul_mem c hx₁), ?_⟩
  rw [bil_sub_right, ← algebraMap_smul F c x₁, bil_smul_right, bil_self, hcF]
  field_simp
  ring

/-- **The second splitting step of §94** (O'Meara 1973, pp. 279–280, dyadic case): if $x_1, x_2 \in L$ have
$B(x_1, x_2)\mathfrak o = \mathfrak sL$ and $Q(x_1), Q(x_2) \in \mathfrak p\,\mathfrak sL$ (i.e.
$Q(x_i)\mathfrak o \subsetneq \mathfrak sL$), then for every $x \in L$ the two linear equations
$B(x_1, x) + \xi Q(x_1) + \eta B(x_1, x_2) = 0$, $B(x_2, x) + \xi B(x_1, x_2) + \eta Q(x_2) = 0$ have solutions
$\xi, \eta \in \mathfrak o$, and $y = x + \xi x_1 + \eta x_2 \in L$ is orthogonal to $x_1$ and $x_2$. -/
@[kb "omeara1963" "§94, pp. 279–280 (the equations for ξ_i, η_i have integral solutions; y_i ⊥ x₁, x₂)"]
theorem exists_orth_step_two {L : Submodule R V} {x₁ x₂ : V} (hx₁ : x₁ ∈ L) (hx₂ : x₂ ∈ L)
    (hB : R ∙ bil Q x₁ x₂ = scale Q L)
    (hq₁ : ∃ q : R, q ∈ maximalIdeal R ∧ Q x₁ = algebraMap R F q * bil Q x₁ x₂)
    (hq₂ : ∃ q : R, q ∈ maximalIdeal R ∧ Q x₂ = algebraMap R F q * bil Q x₁ x₂) {x : V} (hx : x ∈ L) :
    ∃ ξ η : R,
      bil Q x₁ x + algebraMap R F ξ * Q x₁ + algebraMap R F η * bil Q x₁ x₂ = 0 ∧
      bil Q x₂ x + algebraMap R F ξ * bil Q x₁ x₂ + algebraMap R F η * Q x₂ = 0 ∧
      x + ξ • x₁ + η • x₂ ∈ L ∧ bil Q x₁ (x + ξ • x₁ + η • x₂) = 0 ∧ bil Q x₂ (x + ξ • x₁ + η • x₂) = 0 := by
  obtain ⟨q₁, hq₁m, hQ₁⟩ := hq₁
  obtain ⟨q₂, hq₂m, hQ₂⟩ := hq₂
  set b := bil Q x₁ x₂ with hb
  obtain ⟨u₁, hu₁⟩ := mem_span_singleton.mp (hB ▸ bil_mem_scale Q hx₁ hx : bil Q x₁ x ∈ R ∙ b)
  obtain ⟨u₂, hu₂⟩ := mem_span_singleton.mp (hB ▸ bil_mem_scale Q hx₂ hx : bil Q x₂ x ∈ R ∙ b)
  -- `q₁q₂ - 1` is a unit
  have hunit : IsUnit (q₁ * q₂ - 1) := by
    by_contra h
    have h1 : q₁ * q₂ - 1 ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h
    have h2 : q₁ * q₂ ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hq₁m
    have := (maximalIdeal R).sub_mem h2 h1
    rw [sub_sub_cancel] at this
    exact (mem_maximalIdeal _).mp this isUnit_one
  obtain ⟨w, hw⟩ : ∃ w : R, (q₁ * q₂ - 1) * w = 1 := ⟨↑hunit.unit⁻¹, hunit.mul_val_inv⟩
  set ξ := (u₂ - u₁ * q₂) * w
  set η := (u₁ - u₂ * q₁) * w
  have hwF : (algebraMap R F q₁ * algebraMap R F q₂ - 1) * algebraMap R F w = 1 := by
    rw [← map_mul, ← map_one (algebraMap R F), ← map_sub, ← map_mul, hw]
  have e1 : bil Q x₁ x + algebraMap R F ξ * Q x₁ + algebraMap R F η * b = 0 := by
    rw [← hu₁, hQ₁, Algebra.smul_def]
    simp only [ξ, η, map_mul, map_sub]
    linear_combination (-(algebraMap R F u₁) * b) * hwF
  have e2 : bil Q x₂ x + algebraMap R F ξ * b + algebraMap R F η * Q x₂ = 0 := by
    rw [← hu₂, hQ₂, Algebra.smul_def]
    simp only [ξ, η, map_mul, map_sub]
    linear_combination (-(algebraMap R F u₂) * b) * hwF
  refine ⟨ξ, η, e1, e2, L.add_mem (L.add_mem hx (L.smul_mem ξ hx₁)) (L.smul_mem η hx₂), ?_, ?_⟩
  · rw [bil_add_right, bil_add_right, ← algebraMap_smul F ξ x₁, ← algebraMap_smul F η x₂, bil_smul_right,
      bil_smul_right, bil_self]
    linear_combination e1
  · rw [bil_add_right, bil_add_right, ← algebraMap_smul F ξ x₁, ← algebraMap_smul F η x₂, bil_smul_right,
      bil_smul_right, bil_self, bil_comm Q x₂ x₁]
    linear_combination e2

end QuadFormsKB.OMeara
