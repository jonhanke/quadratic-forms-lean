import QuadFormsKB.Tamagawa.Measure.Weil.BinaryComparison
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryFiniteGlueValues

/-!
# Weil's $\tau = 2$ for every anisotropic binary form over every number field
**Layer:** number fields. $F$ any number field, $Q_0$ any nondegenerate anisotropic binary form over $\mathcal O_F$ (any
signature at the real places, complex places allowed), $E$ its discriminant field, $\mu^{\chi_E}_{\mathrm{Tam}}$ = `muTamBin`
(Weil's Tamagawa measure with the convergence factors $L_v(1,\chi_E)$).

**Proves (unconditional)**
* **`binaryTorusComparison`**: the measure comparison `BinaryTorusComparison F` holds for every number field: Weil's
  quotient measure of $T(\mathbb A) = (E\otimes\mathbb A_F)^\times/\mathbb A_F^\times$, carried to $SO(\langle1,D\rangle)(\mathbb A)$ by
  $z\mapsto z/\bar z$, is $L(1,\chi_E)\cdot\mu^{\chi_E}_{\mathrm{Tam}}$ (`torComparison_of_finiteFactor` with the finite factor
  `exists_finiteFactor`; the archimedean and finite local ratios multiply to $1$: `shellRatio`$\cdot$`finRatio` $= 1$);
* **`tauTwoBinaryAll_uncond`**: `TauTwoBinaryAll F` — for every nondegenerate anisotropic binary $Q_0$ and every
  discriminant field $E$, $\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu^{\chi_E}_{\mathrm{Tam}}) = 2$.

Route (no class field theory): $T(F)\backslash T(\mathbb A)\cong E^\times\mathbb A_F^1\backslash\mathbb A_E^1$ has volume $2\rho_E/\rho_F$
(`covolume_muTorSO`), and $L(1,\chi_E) = \rho_E/\rho_F$ (`hasLOne_relChar`).-/

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField

/-- **Weil's local-ratio identity for the norm-one torus of a binary form, over every number field** (unconditional). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, product formula); §2.3, p. 21 (convergence factors) [unverified page]"]
theorem binaryTorusComparison (F : Type) [Field F] [NumberField F] : BinaryTorusComparison F := by
  intro D hD _ E _ _ _ b hb0 hb1
  obtain ⟨Af, N, K', hAf, hK', hKf, hfin, h0, ht⟩ := exists_finiteFactor hb0 hb1 hD
  refine torComparison_of_finiteFactor hb0 hb1 hD hAf N K' hK' hKf ?_ h0 ht
  rw [hfin]
  rfl

/-- **Weil's theorem $\tau = 2$ in dimension $2$, for every anisotropic binary form over every number field**
(unconditional): for every nondegenerate anisotropic binary $Q_0$ over $\mathcal O_F$, any signature at the real places,
complex places allowed, and every discriminant field $E$ of $Q_0$,
$$\mathrm{covol}\bigl(SO(V)(F),\ SO(V)(\mathbb A),\ \mu^{\chi_E}_{\mathrm{Tam}}\bigr) = 2,$$
$\mu^{\chi_E}_{\mathrm{Tam}}$ = Weil's Tamagawa measure with the convergence factors $L_v(1,\chi_E)$ and the global factor
$L(1,\chi_E)^{-1}$ (Ono's $\tau(R^1_{E/F}\mathbb G_m) = 2$). -/
@[kb "weil1982" "§2.4, p. 23; Thm 2.3.1; Thm 3.2.1, p. 43; ono1963 (τ of the norm-one torus) [unverified]"]
theorem tauTwoBinaryAll_uncond (F : Type) [Field F] [NumberField F] : TauTwoBinaryAll F :=
  tauTwoBinaryAll_of_comparison (binaryTorusComparison F)

end QuadFormsKB.Tamagawa.Measure.Weil
