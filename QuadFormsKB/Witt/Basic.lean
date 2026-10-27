/-
# Witt's theorem, part 0: the elementary isometries

This file sets up the tools for Witt's theorem (`QuadFormsKB/Witt/Extension.lean`) for a quadratic
form $Q$ (Mathlib's `QuadraticForm K V`) on a vector space $V$ over an **arbitrary field** $K$,
including characteristic $2$. Write $b(x, y) = Q(x + y) - Q(x) - Q(y)$ for the polar form
(Mathlib's `QuadraticMap.polar Q`, bundled as `QuadraticMap.polarBilin Q`). It is never divided
by $2$, so everything here works in every characteristic. Its radical is
$\operatorname{rad} b = \{v : b(v, \cdot) = 0\}$ (`LinearMap.ker (polarBilin Q)`).

**The three elementary isometries** (all of them are linear maps $V \to V$ defined by explicit
formulas, so no complements or gluing are needed):

* `QuadraticForm.Witt.reflection` (for $Q(z) \neq 0$): $\tau_z(v) = v - \dfrac{b(z, v)}{Q(z)}\, z$.
  In characteristic $2$ this is the "orthogonal transvection" (O'Meara, §42E, p. 96, calls $\tau_z$ a
  symmetry; he works in characteristic $\ne 2$ throughout, §41A, p. 82).
* `QuadraticForm.Witt.eichler` (for $z$ isotropic and $b(z, u) = 0$): the Eichler (Siegel)
  transformation $E_{z,u}(v) = v + b(z, v)\, u - \big(b(u, v) + Q(u)\, b(z, v)\big)\, z$.
* `QuadraticForm.Witt.hypScale` (for a hyperbolic pair $z, z'$, i.e. $Q(z) = Q(z') = 0$,
  $b(z, z') = 1$, and $c \neq 0$): $v \mapsto v + (c - 1)\, b(z', v)\, z + (c^{-1} - 1)\, b(z, v)\, z'$,
  which scales $z$ by $c$, $z'$ by $c^{-1}$ and fixes $\{z, z'\}^\perp$.

**Two linear-algebra facts.**

* `QuadraticForm.Witt.isometryEquivOfMapApp`: if the quadratic radical
  `QuadraticMap.radical Q` $= \{v \in \operatorname{rad} b : Q(v) = 0\}$ is $0$ (and $V$ is
  finite-dimensional), every linear map $f : V \to V$ with $Q \circ f = Q$ is bijective, hence an
  isometry of $V$.
* `QuadraticForm.Witt.exists_polar_ne_zero`: if $x \notin U + \operatorname{rad} b$ then some
  $u \perp U$ has $b(u, x) \neq 0$ (the bilinear "double orthogonal" statement
  $(U^\perp)^\perp = U + \operatorname{rad} b$, in the form it is used).

Sources: O'Meara §§42–43, pp. 88–111; Elman–Karpenko–Merkurjev (EKM) §7–8; Lam Ch. I §4.
-/
import Mathlib
import QuadFormsKB.Citation

open Module QuadraticMap

namespace QuadraticForm.Witt

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
variable (Q : QuadraticForm K V)

/-! ### Expanding `Q` -/

theorem map_add_eq (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  simp only [polar]; ring

theorem map_add_smul (x z : V) (t : K) :
    Q (x + t • z) = Q x + t ^ 2 * Q z + t * polar Q x z := by
  rw [map_add_eq, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul, smul_eq_mul]; ring

theorem polar_self_eq (x : V) : polar Q x x = 2 * Q x := by
  rw [polar_self, two_nsmul, two_mul]

theorem mem_ker_polarBilin {v : V} :
    v ∈ LinearMap.ker (polarBilin Q) ↔ ∀ w, polar Q v w = 0 := by
  simp [LinearMap.ext_iff]

theorem mem_radical_iff {v : V} :
    v ∈ Q.radical ↔ Q v = 0 ∧ v ∈ LinearMap.ker (polarBilin Q) := Iff.rfl

variable {Q} in
/-- A map preserving `Q` preserves the polar form. -/
theorem polar_map_of_map_app {Q' : QuadraticForm K V'} {f : V →ₗ[K] V'}
    (hf : ∀ v, Q' (f v) = Q v) (x y : V) : polar Q' (f x) (f y) = polar Q x y := by
  simp only [polar, ← map_add, hf]

variable {Q} in
/-- An isometry equivalence preserves the radical of the polar form. -/
theorem _root_.QuadraticMap.IsometryEquiv.mem_ker_polarBilin_iff {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q')
    {v : V} : e v ∈ LinearMap.ker (polarBilin Q') ↔ v ∈ LinearMap.ker (polarBilin Q) := by
  rw [mem_ker_polarBilin, mem_ker_polarBilin]
  constructor
  · intro h w
    rw [← h (e w)]
    exact (polar_map_of_map_app (f := e.toLinearEquiv.toLinearMap) e.map_app v w).symm
  · intro h w
    obtain ⟨w, rfl⟩ := e.surjective w
    rw [← h w]
    exact polar_map_of_map_app (f := e.toLinearEquiv.toLinearMap) e.map_app v w

variable {Q} in
/-- An isometry equivalence preserves the polar form. -/
theorem _root_.QuadraticMap.IsometryEquiv.polar_map {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') (x y : V) :
    polar Q' (e x) (e y) = polar Q x y :=
  polar_map_of_map_app (f := e.toLinearEquiv.toLinearMap) e.map_app x y

/-! ### Isometries of `V` from maps preserving `Q` -/

variable {Q} in
/-- If the quadratic radical of `Q` is `0`, a linear map preserving `Q` is injective. -/
theorem injective_of_map_app (hQ : Q.radical = ⊥) {f : V →ₗ[K] V'} {Q' : QuadraticForm K V'}
    (hf : ∀ v, Q' (f v) = Q v) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [← hQ, mem_radical_iff, mem_ker_polarBilin]
  refine ⟨by rw [← hf, hv, map_zero], fun w => ?_⟩
  rw [← polar_map_of_map_app hf, hv, polar_zero_left]

/-- **A linear map preserving $Q$ is an isometry of $V$** when $V$ is finite-dimensional and the
quadratic radical `QuadraticMap.radical Q` is $0$: it is injective (`injective_of_map_app`), hence
bijective. -/
noncomputable def isometryEquivOfMapApp [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    (f : V →ₗ[K] V) (hf : ∀ v, Q (f v) = Q v) : Q.IsometryEquiv Q :=
  { LinearEquiv.ofBijective f
      ⟨injective_of_map_app hQ hf,
        LinearMap.injective_iff_surjective.mp (injective_of_map_app hQ hf)⟩ with
    map_app' := hf }

@[simp] theorem isometryEquivOfMapApp_apply [FiniteDimensional K V] (hQ : Q.radical = ⊥)
    (f : V →ₗ[K] V) (hf : ∀ v, Q (f v) = Q v) (v : V) :
    isometryEquivOfMapApp Q hQ f hf v = f v := rfl

/-! ### Reflections -/

/-- **The reflection (symmetry) along $z$**: $\tau_z(v) = v - \dfrac{b(z, v)}{Q(z)}\, z$. It is an
isometry when $Q(z) \neq 0$ (`reflection_map_app`), in every characteristic. -/
noncomputable def reflection (z : V) : V →ₗ[K] V :=
  LinearMap.id - ((Q z)⁻¹ • polarBilin Q z).smulRight z

theorem reflection_apply (z v : V) :
    reflection Q z v = v - ((Q z)⁻¹ * polar Q z v) • z := by
  simp [reflection]

theorem reflection_map_app {z : V} (hz : Q z ≠ 0) (v : V) : Q (reflection Q z v) = Q v := by
  rw [reflection_apply, sub_eq_add_neg, ← neg_smul, map_add_smul, polar_comm Q v z]
  field_simp
  ring

/-! ### Eichler transformations -/

/-- **The Eichler (Siegel) transformation** $E_{z,u}(v) = v + b(z, v)\, u - \big(b(u, v) +
Q(u)\, b(z, v)\big)\, z$. It is an isometry when $Q(z) = 0$ and $b(z, u) = 0$
(`eichler_map_app`). It fixes every $v$ with $b(z, v) = b(u, v) = 0$. -/
noncomputable def eichler (z u : V) : V →ₗ[K] V :=
  LinearMap.id + (polarBilin Q z).smulRight u - (polarBilin Q u + Q u • polarBilin Q z).smulRight z

theorem eichler_apply (z u v : V) :
    eichler Q z u v = v + polar Q z v • u - (polar Q u v + Q u * polar Q z v) • z := by
  simp [eichler]

theorem eichler_map_app {z u : V} (hz : Q z = 0) (hzu : polar Q z u = 0) (v : V) :
    Q (eichler Q z u v) = Q v := by
  rw [eichler_apply, sub_eq_add_neg, ← neg_smul, map_add_smul, map_add_smul, polar_add_left,
    polar_smul_left, smul_eq_mul, polar_comm Q u z, hzu, hz, polar_comm Q v u, polar_comm Q v z]
  ring

/-! ### Scaling a hyperbolic pair -/

/-- **Scaling a hyperbolic pair**: for $z, z'$ with $Q(z) = Q(z') = 0$, $b(z, z') = 1$ and
$c \neq 0$, the map $v \mapsto v + (c - 1)\, b(z', v)\, z + (c^{-1} - 1)\, b(z, v)\, z'$ is an
isometry (`hypScale_map_app`) sending $z \mapsto c z$, $z' \mapsto c^{-1} z'$ and fixing
$\{z, z'\}^\perp$. -/
noncomputable def hypScale (z z' : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + ((c - 1) • polarBilin Q z').smulRight z +
    ((c⁻¹ - 1) • polarBilin Q z).smulRight z'

theorem hypScale_apply (z z' : V) (c : K) (v : V) :
    hypScale Q z z' c v = v + ((c - 1) * polar Q z' v) • z + ((c⁻¹ - 1) * polar Q z v) • z' := by
  simp [hypScale]

theorem hypScale_map_app {z z' : V} {c : K} (hc : c ≠ 0) (hz : Q z = 0) (hz' : Q z' = 0)
    (hzz' : polar Q z z' = 1) (v : V) : Q (hypScale Q z z' c v) = Q v := by
  rw [hypScale_apply, map_add_smul, map_add_smul, polar_add_left, polar_smul_left, smul_eq_mul,
    hz, hz', hzz', polar_comm Q v z, polar_comm Q v z']
  have : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination (polar Q z v * polar Q z' v) * this

/-! ### The double orthogonal -/

/-- **Separation by the polar form.** If $V$ is finite-dimensional and
$x \notin U + \operatorname{rad} b$, then there is $u \in V$ with $b(u, w) = 0$ for all $w \in U$
and $b(u, x) \neq 0$. (Equivalently $(U^\perp)^\perp \subseteq U + \operatorname{rad} b$.) -/
@[kb "cassels1978" "Ch. 2, Lemma 1.1, p. 11"]
theorem exists_polar_ne_zero [FiniteDimensional K V] {U : Submodule K V} {x : V}
    (hx : x ∉ U ⊔ LinearMap.ker (polarBilin Q)) :
    ∃ u, (∀ w ∈ U, polar Q u w = 0) ∧ polar Q u x ≠ 0 := by
  obtain ⟨f, hfx, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hfU : ∀ w ∈ U ⊔ LinearMap.ker (polarBilin Q), f w = 0 := fun w hw => by
    have : f w ∈ (U ⊔ LinearMap.ker (polarBilin Q)).map f := Submodule.mem_map_of_mem hw
    rw [hf] at this
    simpa using this
  have hmem : f ∈ (LinearMap.ker (polarBilin Q)).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    exact fun w hw => hfU w (Submodule.mem_sup_right hw)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  obtain ⟨v, rfl⟩ := (Module.evalEquiv K V).surjective φ
  have key : ∀ w, f w = polar Q v w := fun w => by
    rw [← hφ]
    simp [polar_comm]
  refine ⟨v, fun w hw => ?_, ?_⟩
  · rw [← key]; exact hfU w (Submodule.mem_sup_left hw)
  · rw [← key]; exact hfx

/-- **Hyperbolic partner.** If $Q(z) = 0$ and $b(u, z) = 1$, then $z' = u - Q(u)\, z$ satisfies
$Q(z') = 0$ and $b(z, z') = 1$: $(z, z')$ is a hyperbolic pair. -/
@[kb "cassels1978" "Ch. 2, Lemma 2.1, p. 15"]
theorem hyperbolic_partner {z u : V} (hz : Q z = 0) (hu : polar Q u z = 1) :
    Q (u - Q u • z) = 0 ∧ polar Q z (u - Q u • z) = 1 := by
  constructor
  · rw [sub_eq_add_neg, ← neg_smul, map_add_smul, hz, hu]; ring
  · rw [polar_sub_right, polar_smul_right, polar_comm Q z u, hu, polar_self_eq, hz]; simp

end QuadraticForm.Witt
