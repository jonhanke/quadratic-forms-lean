import QuadFormsKB.Tamagawa.Unitary.Global
import QuadFormsKB.Binary.RelDensities

/-!
# $\tau(U(V)) = 2$: the cited input (Kottwitz, Ono; Gan–Hanke–Yu 2001, (4.3))

**Layer:** Gan–Hanke–Yu's setting (Gan–Hanke–Yu 2001, §4): $F$ a totally real number field, $E = F(\theta)$ a quadratic extension with
$\bar\theta = -\theta$, $\theta^2 = -D$, $\chi = \chi_{E/F}$; $H_0$ an integral hermitian $m\times m$ matrix over $\mathcal O_F[\omega]$,
$\omega^2 = -D$, $m\ge1$, nondegenerate and totally definite (its trace form is positive definite at every real
embedding). `tauU D H₀ hD hH hdet E` is the covolume of $U(V)(F)$ in $U(V)(\mathbb A)$ for Weil's Tamagawa measure
`muTamU` (`Global.lean`), a defined quantity.

**Defines** the named input **`TauUnitaryTwo`**: $\tau(U(V)) = 2$ (Gan–Hanke–Yu (4.3), citing Kottwitz [K] and Ono [O, p. 128]).

*Why this is an input, and what is proved around it.* Gan–Hanke–Yu do not prove (4.3); they cite it. Ono's route is
$1\to SU(V)\to U(V)\xrightarrow{\det}U(1)\to1$ and $\tau(U(V)) = \tau(U(1))\,\tau(SU(V))$. In this library:
* $\tau(U(1)) = 2$ is **proved** for every quadratic extension of every number field (`tauU1_eq_two`, from the class
  number formula route of the binary forms);
* $\det : U(V)(K)\to U(1)(K)$ is **proved** surjective for every field $K\supseteq F$ of characteristic $0$
  (`detU_surjective`), and the covolume identity along a surjection with a fibred measure is **proved**
  (`covolume_fibMeas`, `covolume_fibMeas_eq_two_mul`: covolume $= 2\cdot$ covolume of the kernel);
* $\prod_v\beta^h_v/\lambda_v$ converges (`multipliable_hermDensity_div_lamL`), so `muTamU` is normalized by a genuine
  Euler product.
What is missing is (a) **$\tau(SU(V)) = 1$**, Weil's conjecture for the simply connected group $SU(V)$ (Weil 1965 for
these classical groups, through the Siegel–Weil formula; Kottwitz 1988 in general): a genuinely missing theory (Siegel–Weil
for unitary groups, or Langlands' computation of the constant term of Eisenstein series); and (b) the compatibility
of the Tamagawa measures along $\det$ (the local fibrations $\omega_{U} = \omega_{SU}\wedge\det^*\omega_{U(1)}$ at every place,
Weil 1982, Thm 2.4.4), which is formalization work, not missing theory. Until both
exist, (4.3) enters as this named statement; it is a statement about the covolume `tauU`, not definitionally any
mass formula derived from it.
-/

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open NumberField QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

/-- **$\tau(U(V)) = 2$** (Gan–Hanke–Yu 2001, (4.3); Kottwitz, Ono) — a **named input**. For $F$ totally real, $E = F(\theta)$ with
$\bar\theta = -\theta$, $\theta^2 = -D$ ($-D$ not a square in $F$), and $H_0$ a nondegenerate totally definite integral
hermitian $m\times m$ matrix over $\mathcal O_F[\omega]$ with $m\ge1$: the covolume of $U(V)(F)$ in $U(V)(\mathbb A)$ for Weil's
Tamagawa measure `muTamU` (convergence factors $L_v(1,\chi_{E/F})$) is $2$.

Field: `tau_eq` ($\tau(U(V)) = 2$, i.e. `tauU D H₀ hD hH hdet E = 2`).

The parameters other than the field are conditions (the hypotheses under which the cited theorem holds): `hm`
($m\ge1$; for $m = 0$ the convergence factors are not those of the trivial group), `hsq` ($E/F$ quadratic, $-D$ not a
square), `hθ`, `hθD` ($E = F(\theta)$, $\theta^2 = -D$, so $\chi_{E/F}$ is the character of $F(\omega)/F$). -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (τ(G) = 2, by Kottwitz [K] and Ono [O, p. 128])"]
structure TauUnitaryTwo [IsTotallyReal F] [∀ ρ : F →+* ℝ, Fact (IsPosDefR (traceQR D H₀ ρ))] (hm : 1 ≤ m)
    (hD : D ≠ 0) (hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-D))) (hH : H₀.IsHermitian) (hdet : (HK D F H₀).det ≠ 0)
    (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E] {θ : 𝓞 E}
    (hθ : Binary.Rel.conjO F E θ = -θ) (hθD : algebraMap (𝓞 F) (𝓞 E) (-D) = θ ^ 2) : Prop where
  tau_eq : tauU D H₀ hD hH hdet E = 2

end QuadFormsKB.Tamagawa.Unitary
