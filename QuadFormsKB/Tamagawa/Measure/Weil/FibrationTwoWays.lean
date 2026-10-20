import QuadFormsKB.Tamagawa.Measure.Weil.NormalFibration

/-!
# The covolume identity on invariant sets, and "computing one integral two ways"

**Generic, Mathlib-only hypotheses (upstreamable).** Extends `NormalFib.fibMeas_exactFD`
(Weil's fibration of $\Gamma\backslash G$ over $N(\Gamma)\backslash Q$) from exact fundamental domains $D$ to the pieces
$D\cap W$ cut out by a left-$\Gamma$-invariant measurable set $W\subseteq G$:

* **`NormalFib.tsum_kern_exactFD_inter`**: $\sum_{\delta\in N(\Gamma)}\kappa(\delta q)(D\cap W) = \mu_K\big(D_K\cap\{k : k\,g_q\in W\}\big)$;
* **`NormalFib.fibMeas_exactFD_inter`**: $\nu(D\cap W) = \int_{D_Q}\mu_K\big(D_K\cap\{k : k\,g_q\in W\}\big)\,d\mu_Q(q)$;
* **`NormalFib.fibMeas_exactFD_preimage`**: for $W = N^{-1}(B)$ with $B$ invariant under $N(\Gamma)$:
  $\nu(D\cap N^{-1}B) = \mu_K(D_K)\,\mu_Q(D_Q\cap B)$;
* **`NormalFib.two_ways`**: if one measure $\mu_G$ on $G$ is fibred in two ways, along $p : G\to A$ (fibre $S$) and along
  $\pi : G\to P$ (fibre $Z$), and the $Z$-fibres meet $p^{-1}(B)$ in a set of constant measure $c$ (modulo $\Gamma\cap Z$), then
  $$\mu_S(D_S)\,\mu_A(D_A\cap B) = c\,\mu_P(D_P).$$

This is the measure-theoretic core of Weil's computation of $\int_{\Gamma\backslash G}f(\|\operatorname{nrd}g\|)\,dg$ in two ways
(Weil 1982, §3.2, proof of Thm 3.2.1, p. 43, for $D^\times$, and its analogue for $G^\natural$), where
$B = \{1\le\|a\|<e\}$, $S = \mathrm{SL}_1$, $Z = \mathbb A^\times$ is the centre and $c = \tfrac12\operatorname{vol}(F^\times\backslash\mathbb A^1)$
because $\|\operatorname{nrd}z\| = \|z\|^2$ on the centre.

The proofs follow `tsum_kern_exactFD` (the sets $E_\delta$ form an exact fundamental domain for $g^{-1}(\Gamma\cap K)g$),
plus Mathlib's `IsFundamentalDomain.measure_set_eq` for invariant sets.
-/

open MeasureTheory Measure Set Function
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NormalFib

variable {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q]

variable (N : G →* Q) (hN : Surjective N) (Γ : Subgroup G) [Countable Γ]
  [StandardBorelSpace G] [MeasurableSpace.CountablySeparated Q]

/-- **The fibre sum on an invariant set**: for a left-$\Gamma$-invariant measurable $W$,
$\sum_{\delta\in N(\Gamma)}\kappa(\delta q)(D\cap W) = \mu_K(D_K\cap\{k : k\,g_q\in W\})$, $g_q$ = `surjInv hN q`. -/
theorem tsum_kern_exactFD_inter (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant]
    (hconj : ∀ g : G, μK.map (adK N g) = μK) {D : Set G} (hD : IsExactFD (Γ := Γ) D)
    {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK) {W : Set G} (hWm : MeasurableSet W)
    (hW : ∀ γ ∈ Γ, ∀ x, γ * x ∈ W ↔ x ∈ W) (q : Q) :
    ∑' δ : gammaQ N Γ, kern N hN μK ((δ : Q) * q) (D ∩ W) =
      μK (DK ∩ {k : N.ker | (k : G) * surjInv hN q ∈ W}) := by
  classical
  set g := surjInv hN q
  have hlift : ∀ δ : gammaQ N Γ, ∃ γ : Γ, N γ = δ := by
    rintro ⟨_, γ, hγ, rfl⟩; exact ⟨⟨γ, hγ⟩, rfl⟩
  choose γd hγd using hlift
  let E : gammaQ N Γ → Set N.ker := fun δ => (fun k : N.ker => (γd δ : G) * g * (k : G)) ⁻¹' D
  let Wg : Set N.ker := {k : N.ker | g * (k : G) ∈ W}
  have hWgm : MeasurableSet Wg := hWm.preimage (measurable_mul_val N g)
  have hEm : ∀ δ, MeasurableSet (E δ) := fun δ => hD.1.preimage (measurable_mul_val N _)
  have hkern : ∀ δ : gammaQ N Γ, kern N hN μK ((δ : Q) * q) (D ∩ W) = μK (E δ ∩ Wg) := by
    intro δ
    have : (δ : Q) * q = N ((γd δ : G) * g) := by rw [map_mul, hγd, surjInv_eq hN q]
    rw [this, kern_apply_N, fibK_apply N μK _ (hD.1.inter hWm)]
    congr 1
    ext k
    simp only [mem_preimage, mem_inter_iff, E, Wg, mem_ofPred_eq]
    rw [mul_assoc, hW _ (γd δ).2]
  have hdisj : Pairwise (Disjoint on fun δ => E δ ∩ Wg) := by
    intro δ₁ δ₂ hne
    refine Set.disjoint_left.2 fun k h₁ h₂ => hne ?_
    have h₁' : (γd δ₁) • (g * (k : G)) ∈ D := by simpa [Subgroup.smul_def, E, mul_assoc] using h₁.1
    have h₂' : (γd δ₂) • (g * (k : G)) ∈ D := by simpa [Subgroup.smul_def, E, mul_assoc] using h₂.1
    have := (hD.2 (g * (k : G))).unique h₁' h₂'
    apply Subtype.ext; rw [← hγd δ₁, ← hγd δ₂, this]
  simp_rw [hkern]
  rw [← measure_iUnion hdisj fun δ => (hEm δ).inter hWgm, ← iUnion_inter]
  set U := ⋃ δ, E δ
  set U' := adK N g⁻¹ ⁻¹' U
  set W' : Set N.ker := {k : N.ker | (k : G) * g ∈ W}
  have hU'm : MeasurableSet U' := (MeasurableSet.iUnion hEm).preimage (measurable_adK N _)
  have hW'm : MeasurableSet W' := hWm.preimage (measurable_subtype_coe.mul_const g)
  have hpre : adK N g⁻¹ ⁻¹' (U ∩ Wg) = U' ∩ W' := by
    ext k
    simp only [U', W', Wg, mem_preimage, mem_inter_iff, mem_ofPred_eq, coe_adK, inv_inv]
    rw [show g * (g⁻¹ * (k : G) * g) = (k : G) * g by group]
  have hmU : μK (U' ∩ W') = μK (U ∩ Wg) := by
    rw [← hpre, ← Measure.map_apply (measurable_adK N _) ((MeasurableSet.iUnion hEm).inter hWgm), hconj]
  have hmemU' : ∀ k : N.ker, k ∈ U' ↔ ∃ δ, (γd δ : G) * (k : G) * g ∈ D := by
    intro k
    simp only [U', U, E, mem_preimage, mem_iUnion, adK, inv_inv]
    refine exists_congr fun δ => ?_
    rw [show (γd δ : G) * g * (g⁻¹ * (k : G) * g) = (γd δ : G) * (k : G) * g by group]
  have hU' : IsExactFD (Γ := gammaK N Γ) U' := by
    refine ⟨hU'm, fun k => ?_⟩
    obtain ⟨γ, hγ, huniq⟩ := hD.2 ((k : G) * g)
    set δ : gammaQ N Γ := ⟨N γ, γ, γ.2, rfl⟩
    have hεK : (γd δ : G)⁻¹ * γ ∈ N.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hγd δ, inv_mul_cancel]
    have hεΓ : ((⟨(γd δ : G)⁻¹ * γ, hεK⟩ : N.ker) : G) ∈ Γ := Γ.mul_mem (Γ.inv_mem (γd δ).2) γ.2
    let ε : gammaK N Γ := ⟨⟨(γd δ : G)⁻¹ * γ, hεK⟩, hεΓ⟩
    refine ⟨ε, ?_, fun ε' hε' => ?_⟩
    · show ε • k ∈ U'
      rw [hmemU']
      refine ⟨δ, ?_⟩
      have : (γd δ : G) * ((ε • k : N.ker) : G) * g = γ • ((k : G) * g) := by
        rw [coe_smul_gammaK, Subgroup.smul_def, smul_eq_mul]
        simp only [ε]; group
      rw [this]; exact hγ
    · change ε' • k ∈ U' at hε'
      rw [hmemU'] at hε'
      obtain ⟨δ', hδ'⟩ := hε'
      have h1 : (⟨(γd δ' : G) * ((ε' : N.ker) : G), Γ.mul_mem (γd δ').2 ε'.2⟩ : Γ) • ((k : G) * g) ∈ D := by
        rw [coe_smul_gammaK] at hδ'
        rw [Subgroup.smul_def, smul_eq_mul]
        convert hδ' using 1
        simp only [mul_assoc]
      have h2 := huniq _ h1
      have hN' : (δ' : Q) = δ := by
        have := congrArg (fun x : Γ => N (x : G)) h2
        simp only [map_mul] at this
        have hε'1 : N (((ε' : N.ker) : G)) = 1 := (ε' : N.ker).2
        rw [hε'1, mul_one, hγd δ'] at this
        exact this
      have hδeq : δ' = δ := Subtype.ext hN'
      subst hδeq
      apply Subtype.ext; apply Subtype.ext
      have := congrArg (fun x : Γ => (x : G)) h2
      simp only at this
      simp only [ε]
      rw [← this]; group
  rw [← hmU, inter_comm U' W', inter_comm DK W']
  refine (hU'.isFundamentalDomain μK).measure_set_eq (hDK.isFundamentalDomain μK) hW'm fun ε => ?_
  ext k
  simp only [W', mem_preimage, mem_ofPred_eq, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
  exact hW _ ε.2 _

/-- **The covolume identity on an invariant set**: for a left-$\Gamma$-invariant measurable $W\subseteq G$,
$\nu(D\cap W) = \int_{D_Q}\mu_K(D_K\cap\{k : k\,g_q\in W\})\,d\mu_Q(q)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]"]
theorem fibMeas_exactFD_inter (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant] (μK : Measure N.ker)
    [SFinite μK] [μK.IsMulLeftInvariant] (hconj : ∀ g : G, μK.map (adK N g) = μK)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK)
    {DQ : Set Q} (hDQ : IsExactFD (Γ := gammaQ N Γ) DQ) {W : Set G} (hWm : MeasurableSet W)
    (hW : ∀ γ ∈ Γ, ∀ x, γ * x ∈ W ↔ x ∈ W) :
    fibMeas N hN μQ μK (D ∩ W) = ∫⁻ q in DQ, μK (DK ∩ {k : N.ker | (k : G) * surjInv hN q ∈ W}) ∂μQ := by
  rw [fibMeas_apply N hN hNm μQ μK (hD.1.inter hWm),
    (hDQ.isFundamentalDomain μQ).lintegral_eq_tsum'' (fun q => kern N hN μK q (D ∩ W))]
  have hm := measurable_kern_apply N hN hNm μK (hD.1.inter hWm)
  simp_rw [Subgroup.smul_def, smul_eq_mul]
  have h := lintegral_tsum (μ := μQ.restrict DQ)
    (f := fun (δ : gammaQ N Γ) x => kern N hN μK ((δ : Q) * x) (D ∩ W))
    (fun δ => (hm.comp (measurable_const_mul (δ : Q))).aemeasurable)
  rw [← h]
  simp_rw [tsum_kern_exactFD_inter N hN Γ μK hconj hD hDK hWm hW]

/-- **The covolume identity on a preimage**: for $B\subseteq Q$ measurable and invariant under $N(\Gamma)$,
$\nu(D\cap N^{-1}B) = \mu_K(D_K)\,\mu_Q(D_Q\cap B)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]"]
theorem fibMeas_exactFD_preimage (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant] (μK : Measure N.ker)
    [SFinite μK] [μK.IsMulLeftInvariant] (hconj : ∀ g : G, μK.map (adK N g) = μK)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK)
    {DQ : Set Q} (hDQ : IsExactFD (Γ := gammaQ N Γ) DQ) {B : Set Q} (hBm : MeasurableSet B)
    (hB : ∀ δ ∈ gammaQ N Γ, ∀ y, δ * y ∈ B ↔ y ∈ B) :
    fibMeas N hN μQ μK (D ∩ N ⁻¹' B) = μK DK * μQ (DQ ∩ B) := by
  have hW : ∀ γ ∈ Γ, ∀ x, γ * x ∈ N ⁻¹' B ↔ x ∈ N ⁻¹' B := fun γ hγ x => by
    simp only [mem_preimage, map_mul]; exact hB _ ⟨γ, hγ, rfl⟩ _
  rw [fibMeas_exactFD_inter N hN Γ hNm μQ μK hconj hD hDK hDQ (hBm.preimage hNm) hW]
  have : ∀ q, μK (DK ∩ {k : N.ker | (k : G) * surjInv hN q ∈ N ⁻¹' B}) = B.indicator (fun _ => μK DK) q := by
    intro q
    have hk : ∀ k : N.ker, (k : G) * surjInv hN q ∈ N ⁻¹' B ↔ q ∈ B := fun k => by
      have hk1 : N (k : G) = 1 := k.2
      simp only [mem_preimage, map_mul, hk1, one_mul, surjInv_eq hN q]
    by_cases hq : q ∈ B
    · rw [indicator_of_mem hq]; congr 1; ext k
      simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]; exact fun _ => (hk k).2 hq
    · rw [indicator_of_notMem hq]; convert measure_empty (μ := μK); ext k
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => hq ((hk k).1 h)
  simp_rw [this]
  rw [lintegral_indicator_const hBm, Measure.restrict_apply hBm, inter_comm, mul_comm]

/-- **Weil's integral computed two ways** (abstract form). A measure $\mu_G$ on $G$ is fibred along $p : G\to A$ with fibre
$\mu_S$ on $S = \ker p$ and along $\pi : G\to P$ with fibre $\mu_Z$ on $Z = \ker\pi$ (both fibre measures conjugation invariant).
Let $B\subseteq A$ be measurable and $p(\Gamma)$-invariant, and suppose the $Z$-fibres of $p^{-1}(B)$ have constant measure modulo
$\Gamma\cap Z$: $\mu_Z(D_Z\cap\{z : z\,g\in p^{-1}B\}) = c$ for every $g$. Then for exact fundamental domains
$$\mu_S(D_S)\,\mu_A(D_A\cap B) = c\,\mu_P(D_P).$$
Both sides are $\mu_G(D\cap p^{-1}B)$ (`fibMeas_exactFD_preimage`, `fibMeas_exactFD_inter`). -/
@[kb "weil1982" "§3.2, proof of Thm 3.2.1, p. 43 (the two fibrations of D^×)"]
theorem two_ways {A P : Type*} [Group A] [Group P] [MeasurableSpace A] [MeasurableSpace P] [MeasurableMul A]
    [MeasurableMul P] [MeasurableSpace.CountablySeparated A] [MeasurableSpace.CountablySeparated P]
    (p : G →* A) (hp : Surjective p) (hpm : Measurable p) (π : G →* P) (hπ : Surjective π) (hπm : Measurable π)
    (μA : Measure A) [μA.IsMulLeftInvariant] (μS : Measure p.ker) [SFinite μS] [μS.IsMulLeftInvariant]
    (μP : Measure P) [μP.IsMulLeftInvariant] (μZ : Measure π.ker) [SFinite μZ] [μZ.IsMulLeftInvariant]
    (hμ : fibMeas p hp μA μS = fibMeas π hπ μP μZ)
    (hconjS : ∀ g : G, μS.map (adK p g) = μS) (hconjZ : ∀ g : G, μZ.map (adK π g) = μZ)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DS : Set p.ker} (hDS : IsExactFD (Γ := gammaK p Γ) DS)
    {DA : Set A} (hDA : IsExactFD (Γ := gammaQ p Γ) DA) {DZ : Set π.ker} (hDZ : IsExactFD (Γ := gammaK π Γ) DZ)
    {DP : Set P} (hDP : IsExactFD (Γ := gammaQ π Γ) DP) {B : Set A} (hBm : MeasurableSet B)
    (hB : ∀ δ ∈ gammaQ p Γ, ∀ y, δ * y ∈ B ↔ y ∈ B) (c : ℝ≥0∞)
    (hc : ∀ g : G, μZ (DZ ∩ {z : π.ker | (z : G) * g ∈ p ⁻¹' B}) = c) :
    μS DS * μA (DA ∩ B) = c * μP DP := by
  rw [← fibMeas_exactFD_preimage p hp Γ hpm μA μS hconjS hD hDS hDA hBm hB, hμ]
  have hW : ∀ γ ∈ Γ, ∀ x, γ * x ∈ p ⁻¹' B ↔ x ∈ p ⁻¹' B := fun γ hγ x => by
    simp only [mem_preimage, map_mul]; exact hB _ ⟨γ, hγ, rfl⟩ _
  rw [fibMeas_exactFD_inter π hπ Γ hπm μP μZ hconjZ hD hDZ hDP (hBm.preimage hpm) hW]
  simp_rw [hc]
  rw [setLIntegral_const]

end NormalFib

end

end QuadFormsKB.Tamagawa.Measure.Weil
