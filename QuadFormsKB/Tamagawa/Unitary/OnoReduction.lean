import QuadFormsKB.Tamagawa.Measure.Weil.NormalFibration
import QuadFormsKB.Tamagawa.Measure.Weil.FundamentalDomain

/-!
# Ono's reduction: covolumes along a surjective homomorphism

**Generic statement** (no unitary groups here; they are the intended application).
Let $N : G\to Q$ be a surjective measurable homomorphism of second countable locally compact groups (standard Borel),
$K = \ker N$, $\Gamma\le G$ a countable subgroup, $\mu_K$, $\mu_Q$ left-invariant measures, and $\nu$ = `NormalFib.fibMeas`
the measure on $G$ fibred over $\mu_Q$ with fibre $\mu_K$ (Weil 1982, §2.4, Thm 2.4.4). If conjugation by $G$ preserves
$\mu_K$ and $\Gamma$, $\Gamma\cap K$, $N(\Gamma)$ have exact fundamental domains (automatic for discrete subgroups of
second countable groups, `exists_measurableSet_forall_existsUnique_smul_mem`), then
$$\mathrm{covol}(\Gamma, G, \nu) = \mathrm{covol}(\Gamma\cap K, K, \mu_K)\cdot\mathrm{covol}(N(\Gamma), Q, \mu_Q)$$
(**`covolume_fibMeas`**).

**Ono's route to $\tau(U(V)) = 2$** (Gan–Hanke–Yu 2001, (4.3), citing Ono [O, p. 128] and Kottwitz [K]): for
$1\to SU(V)\to U(V)\xrightarrow{\det}U(1)\to1$, $\det$ is surjective on $F$-points (`Unitary.detU_surjective`), so
$N(\Gamma) = U(1)(F)$, and the Tamagawa measure of $U(V)$ is fibred over that of $U(1)$ (same convergence factors
$L_v(1,\chi_{E/F})$) with fibre the Tamagawa measure of $SU(V)$ (no convergence factors). Hence
$\tau(U(V)) = \tau(SU(V))\,\tau(U(1)) = \tau(SU(V))\cdot2$ (**`covolume_fibMeas_eq_two_mul`**, with
$\tau(U(1)) = 2$ = `Unitary.tauU1_eq_two`).
-/

open MeasureTheory Measure Function
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.Weil.NormalFib

variable {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q] [StandardBorelSpace G] [MeasurableSpace.CountablySeparated Q]
  (N : G →* Q) (hN : Surjective N) (Γ : Subgroup G) [Countable Γ]

/-- **Covolumes multiply along a fibration** (Weil 1982, §2.4, Thm 2.4.4 and Lemma 2.4.1; Ono's reduction): for exact
fundamental domains of $\Gamma$, $\Gamma\cap\ker N$ and $N(\Gamma)$,
$\mathrm{covol}(\Gamma,\nu) = \mathrm{covol}(\Gamma\cap\ker N,\mu_K)\,\mathrm{covol}(N(\Gamma),\mu_Q)$ for the fibred measure
$\nu$ = `fibMeas N hN μQ μK`. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]; ganhankeyu2001 (4.3), p. 110 (Ono's route)"]
theorem covolume_fibMeas (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant] (μK : Measure N.ker)
    [SFinite μK] [μK.IsMulLeftInvariant] (hconj : ∀ g : G, μK.map (adK N g) = μK)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK)
    {DQ : Set Q} (hDQ : IsExactFD (Γ := gammaQ N Γ) DQ) :
    covolume Γ G (fibMeas N hN μQ μK) = covolume (gammaK N Γ) N.ker μK * covolume (gammaQ N Γ) Q μQ := by
  have := isMulLeftInvariant_fibMeas N hN hNm μQ μK
  rw [(hD.isFundamentalDomain _).covolume_eq_volume, (hDK.isFundamentalDomain _).covolume_eq_volume,
    (hDQ.isFundamentalDomain _).covolume_eq_volume]
  exact fibMeas_exactFD N hN Γ hNm μQ μK hconj hD hDK hDQ

/-- **Ono's reduction with $\tau$ of the quotient equal to $2$**: if the image $N(\Gamma)$ is a subgroup $\Gamma_Q$ of
covolume $2$ (for $U(V)\to U(1)$: $\det(U(V)(F)) = U(1)(F)$ and $\tau(U(1)) = 2$), then
$\mathrm{covol}(\Gamma,\nu) = 2\,\mathrm{covol}(\Gamma\cap\ker N,\mu_K)$, i.e. $\tau(U(V)) = 2\,\tau(SU(V))$. -/
@[kb "ganhankeyu2001" "(4.3), p. 110 (τ(G) = 2 from τ(U(1)) = 2 and τ(SU(V)) = 1; Ono [O, p. 128])"]
theorem covolume_fibMeas_eq_two_mul (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant]
    (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] (hconj : ∀ g : G, μK.map (adK N g) = μK)
    {ΓQ : Subgroup Q} (himage : Γ.map N = ΓQ) (htwo : covolume ΓQ Q μQ = 2)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK)
    {DQ : Set Q} (hDQ : IsExactFD (Γ := gammaQ N Γ) DQ) :
    covolume Γ G (fibMeas N hN μQ μK) = 2 * covolume (gammaK N Γ) N.ker μK := by
  rw [covolume_fibMeas N hN Γ hNm μQ μK hconj hD hDK hDQ, mul_comm]
  congr 1
  rw [← htwo]
  subst himage
  rfl

end QuadFormsKB.Tamagawa.Unitary
