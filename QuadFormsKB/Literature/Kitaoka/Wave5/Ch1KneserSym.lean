/-
# Kitaoka 1993, Theorem 1.2.2 (Kneser): symmetries and the groups $S(J)$

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.2, Theorem 1.2.2 and the beginning of its proof,
pp. 6–7 (printed pages); the symmetry $\tau_x$ of p. 6.

**Setting** (as in `Kitaoka.Theorem122`, `Ch1Spaces.lean`). $R$ is a local ring, $\tilde R$ an $R$-algebra, $U$ a
module over $\tilde R$ (and over $R$ through $\tilde R$) with a quadratic form $q : U \to \tilde R$ and
$b(x, y) = q(x+y) - q(x) - q(y)$ (`QuadraticMap.polar`).

**Defines**
* `symMap q z c`, `symEquiv`: the symmetry $\tau_z(x) = x - c\,b(x, z)z$ with $c = q(z)^{-1}$ (an involutive
  isometry of $U$);
* `InS q J g`: $g$ is a product of symmetries $\tau_z$ with $z \in J$ and $q(z) \in R^\times$ (Kitaoka's group $S(J)$).

**Proves** for $g \in S(J)$: $g$ is an isometry (`InS.isom`), fixes every $x$ with $b(x, J) = 0$ (`InS.fix`), maps
every $R$-submodule $X \supseteq J$ with $b(X, J) \subseteq R$ into itself with $g(x) \equiv x \bmod J$
(`InS.mapsTo`, `InS.sub_mem`), and $S(J)$ is a group (`InS.trans`, `InS.symm`).
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Monotonicity

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Kneser

variable {R Rt U : Type} [CommRing R] [CommRing Rt] [Algebra R Rt]
  [AddCommGroup U] [Module Rt U] [Module R U] [IsScalarTower R Rt U]
variable (q : QuadraticForm Rt U)

/-- The symmetry $\tau_z(x) = x - c\,b(x, z)\,z$ (with $c = q(z)^{-1}$ in use). -/
def symMap (z : U) (c : Rt) : U →ₗ[Rt] U :=
  LinearMap.id - (c • (polarBilin q).flip z).smulRight z

theorem symMap_apply (z : U) (c : Rt) (x : U) : symMap q z c x = x - (c * polar q x z) • z := by
  simp [symMap, polarBilin_apply_apply]

theorem polar_symMap {z : U} {c : Rt} (hc : c * q z = 1) (x : U) :
    polar q (symMap q z c x) z = -polar q x z := by
  rw [symMap_apply, polar_sub_left, polar_smul_left, QuadraticMap.polar_self, smul_eq_mul, two_nsmul]
  linear_combination (-2 * polar q x z) * hc

theorem symMap_symMap {z : U} {c : Rt} (hc : c * q z = 1) (x : U) : symMap q z c (symMap q z c x) = x := by
  rw [symMap_apply q z c (symMap q z c x), polar_symMap q hc, symMap_apply]
  rw [mul_neg, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem q_symMap {z : U} {c : Rt} (hc : c * q z = 1) (x : U) : q (symMap q z c x) = q x := by
  rw [symMap_apply, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add q, QuadraticMap.map_smul, polar_smul_right,
    smul_eq_mul, smul_eq_mul]
  linear_combination (c * polar q x z * polar q x z) * hc

/-- The symmetry as a linear automorphism (it is an involution). -/
def symEquiv (z : U) (c : Rt) (hc : c * q z = 1) : U ≃ₗ[Rt] U :=
  LinearEquiv.ofInvolutive (symMap q z c) (symMap_symMap q hc)

@[simp] theorem symEquiv_apply (z : U) (c : Rt) (hc : c * q z = 1) (x : U) :
    symEquiv q z c hc x = symMap q z c x := rfl

theorem symEquiv_symm (z : U) (c : Rt) (hc : c * q z = 1) : (symEquiv q z c hc).symm = symEquiv q z c hc := by
  ext x
  apply (symEquiv q z c hc).injective
  simp [symMap_symMap q hc]

/-- **Kitaoka's group $S(J)$**: the products of symmetries $\tau_z$ with $z \in J$ and $q(z) = u \in R^\times$. -/
inductive InS (J : Submodule R U) : (U ≃ₗ[Rt] U) → Prop
  | refl : InS J (LinearEquiv.refl Rt U)
  | step (z : U) (u : R) (c : Rt) (hz : z ∈ J) (hu : IsUnit u) (hq : q z = algebraMap R Rt u)
      (hc : c * q z = 1) {g : U ≃ₗ[Rt] U} : InS J g → InS J ((symEquiv q z c hc).trans g)

variable {q}

theorem InS.isom {J : Submodule R U} {g : U ≃ₗ[Rt] U} (h : InS q J g) (x : U) : q (g x) = q x := by
  induction h generalizing x with
  | refl => rfl
  | @step z u c hz hu hq hc g' _ ih =>
    simp only [LinearEquiv.trans_apply, symEquiv_apply]
    rw [ih, q_symMap q hc]

theorem InS.fix {J : Submodule R U} {g : U ≃ₗ[Rt] U} (h : InS q J g) (x : U) (hx : ∀ z ∈ J, polar q x z = 0) :
    g x = x := by
  induction h with
  | refl => rfl
  | @step z u c hz hu hq hc g' _ ih =>
    simp only [LinearEquiv.trans_apply, symEquiv_apply]
    rw [symMap_apply, hx z hz, mul_zero, zero_smul, sub_zero, ih]

/-- The coefficient $c\,b(x, z)$ of a symmetry lies in $R$ when $b(x, z)$ does. -/
theorem coeff_mem {z : U} {u : R} {c : Rt} (hu : IsUnit u) (hq : q z = algebraMap R Rt u) (hc : c * q z = 1)
    {x : U} (hx : polar q x z ∈ (algebraMap R Rt).range) :
    ∃ r : R, (c * polar q x z) • z = r • z := by
  obtain ⟨s, hs⟩ := hx
  obtain ⟨v, rfl⟩ := hu
  refine ⟨(↑v⁻¹ : R) * s, ?_⟩
  have hcv : c = algebraMap R Rt (↑v⁻¹ : R) := by
    have h1 : algebraMap R Rt (↑v⁻¹ : R) * q z = 1 := by
      rw [hq, ← map_mul, Units.inv_mul, map_one]
    calc c = c * (q z * algebraMap R Rt (↑v⁻¹ : R)) := by rw [mul_comm (q z), h1, mul_one]
      _ = (c * q z) * algebraMap R Rt (↑v⁻¹ : R) := by ring
      _ = _ := by rw [hc, one_mul]
  rw [hcv, ← hs, ← map_mul, algebraMap_smul]

/-- An element of $S(J)$ maps every $R$-submodule $X \supseteq J$ with $b(X, J) \subseteq R$ into itself, with
$g(x) - x \in J$. -/
theorem InS.sub_mem {J X : Submodule R U} (hJX : J ≤ X)
    (hXJ : ∀ x ∈ X, ∀ z ∈ J, polar q x z ∈ (algebraMap R Rt).range) {g : U ≃ₗ[Rt] U} (h : InS q J g) :
    ∀ x ∈ X, g x ∈ X ∧ g x - x ∈ J := by
  induction h with
  | refl => intro x hx; simp [hx]
  | @step z u c hz hu hq hc g' _ ih =>
    intro x hx
    obtain ⟨r, hr⟩ := coeff_mem hu hq hc (hXJ x hx z hz)
    have h1 : symMap q z c x = x - r • z := by rw [symMap_apply, hr]
    have hmem : symMap q z c x ∈ X := by rw [h1]; exact X.sub_mem hx (X.smul_mem r (hJX hz))
    obtain ⟨ih1, ih2⟩ := ih _ hmem
    simp only [LinearEquiv.trans_apply, symEquiv_apply]
    refine ⟨ih1, ?_⟩
    have : g' (symMap q z c x) - x = (g' (symMap q z c x) - symMap q z c x) + (symMap q z c x - x) := by abel
    rw [this]
    refine J.add_mem ih2 ?_
    rw [h1, sub_sub_cancel_left]
    exact J.neg_mem (J.smul_mem r hz)

theorem InS.trans {J : Submodule R U} {g g' : U ≃ₗ[Rt] U} (h : InS q J g) (h' : InS q J g') :
    InS q J (g.trans g') := by
  induction h with
  | refl => simpa using h'
  | @step z u c hz hu hq hc g' _ ih =>
    rw [LinearEquiv.trans_assoc]
    exact InS.step z u c hz hu hq hc ih

theorem InS.sym {J : Submodule R U} {z : U} {u : R} {c : Rt} (hz : z ∈ J) (hu : IsUnit u)
    (hq : q z = algebraMap R Rt u) (hc : c * q z = 1) : InS q J (symEquiv q z c hc) := by
  simpa using InS.step z u c hz hu hq hc (InS.refl (q := q) (J := J))

theorem InS.symm {J : Submodule R U} {g : U ≃ₗ[Rt] U} (h : InS q J g) : InS q J g.symm := by
  induction h with
  | refl => simpa using (InS.refl (q := q) (J := J))
  | @step z u c hz hu hq hc g' _ ih =>
    have e : ((symEquiv q z c hc).trans g').symm = g'.symm.trans (symEquiv q z c hc) := by
      ext x
      apply ((symEquiv q z c hc).trans g').injective
      simp only [LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply, symEquiv_apply]
      rw [symMap_symMap q hc, LinearEquiv.apply_symm_apply]
    rw [e]
    exact ih.trans (InS.sym hz hu hq hc)

theorem InS.mono {J J' : Submodule R U} (hJ : J ≤ J') {g : U ≃ₗ[Rt] U} (h : InS q J g) : InS q J' g := by
  induction h with
  | refl => exact InS.refl
  | @step z u c hz hu hq hc g' _ ih => exact InS.step z u c (hJ hz) hu hq hc ih

end QuadFormsKB.Kitaoka.Kneser
