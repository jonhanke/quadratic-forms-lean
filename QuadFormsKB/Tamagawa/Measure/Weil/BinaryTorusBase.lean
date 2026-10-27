import QuadFormsKB.Tamagawa.Measure.Weil.BinaryReduce
import QuadFormsKB.Tamagawa.Measure.Weil.BaseChangeQuat

/-!
# The norm-one torus of a binary form: shared definitions
**Layer:** number fields. $F$ is a number field, $D\in\mathcal O_F$, $Q_0 = \langle1,D\rangle$ = `diagForm1 D`, $d = -D$
(`dD D`), $E = F[\omega]$, $\omega^2 = d$, and $E\otimes_F\mathbb A_F$ = `QuadAdele F d` $=\mathbb A_F[\omega]$.
For $-D$ not a square, $SO(\langle1,D\rangle)\cong R^1_{E/F}\mathbb G_m\cong R_{E/F}\mathbb G_m/\mathbb G_m$ (Hilbert 90), so
$SO(V)(\mathbb A)\cong(E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$.

**Defines**
* `dD D` $= -D\in F$;
* `quadScalar d` : $\mathbb A_F^\times\to(E\otimes\mathbb A_F)^\times$, the scalars;
* `TorA D` $= (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$ (quotient group, quotient topology) and `torMk D` the projection;
* `quadDiagUnit d` : $E^\times\to(E\otimes\mathbb A_F)^\times$ (`quadDiag` on units) and `torGamma D`, the image of
  $E^\times$ in `TorA D`.
-/

open NumberField

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F]

/-- $d = -D$: the square of $\omega$ in $E = F[\omega]$ for the form $\langle1,D\rangle = x_0^2 + Dx_1^2$
($N(x_0 + x_1\omega) = x_0^2 - dx_1^2 = x_0^2 + Dx_1^2$). -/
abbrev dD (D : 𝓞 F) : F := -(algebraMap (𝓞 F) F D)

/-! ### Topology of $E\otimes\mathbb A_F$ and of its units -/

section Topology

variable (d : F)

/-- The coordinates $z\mapsto(\mathrm{re}\,z,\mathrm{im}\,z)$ as a homeomorphism $E\otimes\mathbb A_F\cong\mathbb A_F^2$. -/
def quadCoordHomeo : QuadAdele F d ≃ₜ Adeles F × Adeles F where
  toFun z := (z.re, z.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_quadCoord d
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance : T2Space (QuadAdele F d) := (quadCoordHomeo d).isEmbedding.t2Space

instance : LocallyCompactSpace (QuadAdele F d) := (quadCoordHomeo d).isClosedEmbedding.locallyCompactSpace

instance : SecondCountableTopology (QuadAdele F d) := (quadCoordHomeo d).isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuadAdele F d)ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := QuadAdele F d)).symm.isEmbedding.secondCountableTopology

instance : SecondCountableTopology (QuadAdele F d)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology

end Topology

/-- **The scalars** $\mathbb A_F^\times\to(E\otimes\mathbb A_F)^\times$, $c\mapsto c + 0\,\omega$. -/
def quadScalar (d : F) : (Adeles F)ˣ →* (QuadAdele F d)ˣ :=
  Units.map (algebraMap (Adeles F) (QuadAdele F d)).toMonoidHom

/-- **$T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$** for $T = R_{E/F}\mathbb G_m/\mathbb G_m$ (quotient group with
the quotient topology); it is isomorphic to $SO(\langle1,D\rangle)(\mathbb A)$ by $z\mapsto z/\bar z$. -/
abbrev TorA (D : 𝓞 F) : Type := (QuadAdele F (dD D))ˣ ⧸ (quadScalar (dD D)).range

/-- The projection $(E\otimes\mathbb A_F)^\times\to T(\mathbb A)$. -/
abbrev torMk (D : 𝓞 F) : (QuadAdele F (dD D))ˣ →* TorA D := QuotientGroup.mk' _

/-- **The global points** $E^\times\to(E\otimes\mathbb A_F)^\times$, $z\mapsto z$ diagonally (`quadDiag`). -/
abbrev quadDiagUnit (d : F) : (QuadraticAlgebra F d 0)ˣ →* (QuadAdele F d)ˣ :=
  Units.map (quadDiag d).toMonoidHom

/-- **$T(F) = E^\times F^\times/F^\times$ inside $T(\mathbb A)$**: the image of $E^\times$. -/
abbrev torGamma (D : 𝓞 F) : Subgroup (TorA D) := (quadDiagUnit (dD D)).range.map (torMk D)

end QuadFormsKB.Tamagawa.Measure.Weil
