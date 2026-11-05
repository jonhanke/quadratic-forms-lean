/-
# O'Meara §54: invertible vectors in an algebra compatible with $V$ (p. 132)

**Setting.** A field $F$, a quadratic form $Q$ on an $F$-space $V$, and an $F$-algebra $A$ *compatible* with $V$
(O'Meara §54, p. 131): $V$ is contained in $A$ (here: an $F$-linear map $j : V \to A$) and $x^2 = Q(x)1_A$ for all
$x \in V$ (hypothesis `hj`, as in `Sec54Dim.lean`). $A$ is nontrivial ($1_A \ne 0$).

**Proves** (54.r4, p. 132): `isUnit_iff_anisotropic`, a vector $x$ is invertible in $A$ if and only if it is
anisotropic, and `mul_inv_eq_one`, `inv_mul_eq_one`: then $x^{-1} = Q(x)^{-1}x$.
-/
import Mathlib
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.OMeara.Inv54

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
variable {A : Type*} [Ring A] [Algebra F A] (j : V →ₗ[F] A)
  (hj : ∀ x, j x * j x = algebraMap F A (Q x))
include hj

/-- **54.r4, the inverse** (O'Meara 1963, §54, p. 132): in an algebra $A$ compatible with $V$, an anisotropic $x$
($Q(x) \ne 0$) has the inverse $x^{-1} = Q(x)^{-1}x$: $x \cdot Q(x)^{-1}x = 1_A$. -/
@[kb "omeara1963" "§54, p. 132 (x⁻¹ = Q(x)⁻¹x for anisotropic x)"]
theorem mul_inv_eq_one {x : V} (hx : Q x ≠ 0) : j x * ((Q x)⁻¹ • j x) = 1 := by
  rw [mul_smul_comm, hj, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx, map_one]

theorem inv_mul_eq_one {x : V} (hx : Q x ≠ 0) : ((Q x)⁻¹ • j x) * j x = 1 := by
  rw [smul_mul_assoc, hj, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx, map_one]

/-- **54.r4** (O'Meara 1963, §54, p. 132): in an algebra $A$ compatible with $V$ (with $1_A \ne 0$), a vector
$x \in V$ is invertible in $A$ if and only if it is anisotropic, $Q(x) \ne 0$. (If $Q(x) = 0$ then $x^2 = 0$, so an
invertible $x$ would give $x = 0$ and $1_A = 0$.) -/
@[kb "omeara1963" "§54, p. 132 (x ∈ V invertible in A iff anisotropic)"]
theorem isUnit_iff_anisotropic [Nontrivial A] (x : V) : IsUnit (j x) ↔ Q x ≠ 0 := by
  constructor
  · intro hu h0
    have h2 : j x * j x = 0 := by rw [hj, h0, map_zero]
    have hx0 : j x = 0 := by
      obtain ⟨u, hu⟩ := hu
      have := congrArg (· * (↑u⁻¹ : A)) h2
      simp only [zero_mul] at this
      rw [← hu, mul_assoc, Units.mul_inv, mul_one] at this
      rw [← hu, this]
    rw [hx0] at hu
    exact not_isUnit_zero hu
  · intro hx
    exact ⟨⟨j x, (Q x)⁻¹ • j x, mul_inv_eq_one Q j hj hx, inv_mul_eq_one Q j hj hx⟩, rfl⟩

end QuadFormsKB.OMeara.Inv54
