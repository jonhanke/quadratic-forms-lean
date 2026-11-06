/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.BinaryMassSum
import QuadFormsKB.Literature.Hanke2011Structure.BinaryGlobal
import QuadFormsKB.Literature.Hanke2011Ternary.TwoSplit

/-!
# Hanke 2011, Theorem 7.11: the total mass of totally definite binary lattices (2 split completely)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §7, Definition 7.5, Theorem 7.6 (proof, tables), Remark 7.7,
Lemmas 7.8 and 7.10, Theorem 7.11, pp. 29–33.

**Setting.** $F$ totally real, $2$ split completely in $F$ (`TwoSplitsCompletely F`), $S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times,U_f)$
with $\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2) \ne \emptyset$, and the paper's local data of $S$ at each prime $\mathfrak p$
(`LocalDatum`): $\nu_{\mathfrak p} = \operatorname{ord}_{\mathfrak p}(S)$, $q = N\mathfrak p$, whether $\mathfrak p \mid 2$,
$\chi_{\mathfrak p} = \chi_{\widetilde S}(\mathfrak p) \in \{\pm1\}$ and whether $\widetilde S_{\mathfrak p} \equiv 3 \pmod 4$; put
$\gamma_{\mathfrak p} = 1 - \chi_{\mathfrak p}/q$.

**Input** (`BinaryTableHolds S d`, named): the tables in the proof of Theorem 7.6 hold for the true local genera, with the
generic densities of Definition 7.5 / Lemma 7.10 ($\beta_{2,\mathfrak p} = \gamma_{\mathfrak p}$ at $\mathfrak p \nmid 2$ and
$\gamma_{\mathfrak p}/2$ at $\mathfrak p \mid 2$), and with the corrected dyadic value $B^* = +1$ at $\nu = 0$,
$\widetilde S \equiv 3 \pmod 4$ (*Erratum knock-on* of the repository's correction of Lemma 7.2, row $(\bar2)$; see
`BinarySeries.lean`).

**Products over all primes** (*Clarification*): $\prod_{\mathfrak p\nmid I(S)}\gamma_{\mathfrak p}^{-1}$ converges only
conditionally; it is read as the regularized product `prodGammaInvNotDvd d`
$= L_F(1,\chi)\prod_{\mathfrak p\mid I(S)}\gamma_{\mathfrak p}$ ($\chi = (\chi_{\mathfrak p})_{\mathfrak p}$), the same convention as
$\beta^{-1}_{2,f}(\widetilde S)$ in Lemma 7.8, for which Lemma 7.10 becomes $\beta^{-1}_{2,f}(\widetilde S) = 2^{[F:\mathbb Q]}L_F(1,\chi)$
(`betaInvReg_eq_lemma_7_10`).

**Headline.** **`theorem_7_11_two`**: Theorem 7.11 as an identity of the sum over the classes,
$$\sum_{L\in\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2)}\frac1{|\mathrm{Aut}(L)|} =
  \frac{\kappa(S)\,|\Delta_F|^{1/2}\,N_{F/\mathbb Q}(I(S))^{1/2}}{2\,(2\pi)^{[F:\mathbb Q]}}\prod_{\mathfrak p\nmid I(S)}\gamma_{\mathfrak p}(\widetilde S)^{-1},$$
with $\kappa(S) = 2$ if $I(S)$ is a square and $\widetilde S \equiv 3 \pmod 4$, and $\kappa(S) = 1$ otherwise (`kappaCorr`).
*Erratum knock-on*: the printed $\kappa(S)$ is $2$ or $0$ according as
$\tau$ is even or odd; with the corrected Lemma 7.2 the dyadic factor of $B^*$ at $\nu = 0$ is $+1 = A^*$, so
$B^*(S) = A^*(S)$ (no sign $(-1)^\tau$) and $\kappa(S) = 2$ whenever $I(S)$ is a square and $\widetilde S \equiv 3 \pmod 4$. With
the printed table the algebra gives the printed $\kappa$ (`theorem_7_11_finite`).
*Conditional on* `BinaryLocalGeneraFinite F` and `BinaryTableHolds S d`.
-/

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real
open QuadFormsKB.NFEuler QuadFormsKB.RegProd QuadFormsKB.Hanke2011Ternary.NF

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The corrected table and $\kappa$ -/

/-- **The dyadic table value $B^*_{\mathfrak p;2}(u\pi^\nu)$, corrected** ($F_{\mathfrak p} = \mathbb Q_2$): as `bDyadic`, except
$B^* = +1$ (not $-1$) for $\nu = 0$, $u \equiv 3 \pmod 4$ (the genus there has $c_{\mathfrak p} = +1$, corrected Lemma 7.2,
`lemma_7_2_dyadic_bar_two`). -/
def bDyadicCorr (u3 : Bool) (χ : ℝ) (ν : ℕ) : ℝ := if u3 = true ∧ ν = 0 then 1 else bDyadic u3 χ ν

/-- $B^*_{\mathfrak p;2}$ at one prime from the corrected table. -/
def LocalDatum.bCorr (d : LocalDatum ℝ) : ℝ :=
  if d.dyadic then bDyadicCorr d.u3 d.chi d.nu else bNondyadic d.chi d.q d.nu

/-- $\gamma_{\mathfrak p} = 1 - \chi_{\mathfrak p}/q$ for the datum at $\mathfrak p$. -/
def LocalDatum.gamma (d : LocalDatum ℝ) : ℝ := gammaP d.chi d.q

/-- **The generic densities of Definition 7.5 and Lemma 7.10**: $\beta_{2,\mathfrak p}(\widetilde S_{\mathfrak p}) = \gamma_{\mathfrak p}$
at $\mathfrak p \nmid 2$ and $\gamma_{\mathfrak p}/2$ at $\mathfrak p \mid 2$ (i.e. $\beta^{-1} = 2\gamma^{-1}$). -/
@[kb "hanke2011structure" "Def. 7.5, p. 29, and Lemma 7.10, proof, p. 32 (generic densities)"]
def betaGen75 (d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if (d v).dyadic then (d v).gamma / 2 else (d v).gamma

/-- **The constant $\kappa(S)$ of Theorem 7.11, corrected**: $2$ if every $\nu_{\mathfrak p}$ is even ($I(S)$ is a square) and
$\widetilde S \equiv 3 \pmod 4$ at every dyadic prime, $1$ otherwise. -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (κ(S), corrected)"]
def kappaCorr (d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ) : ℝ :=
  open Classical in
  if ∀ v, Even (d v).nu ∧ ((d v).dyadic = true → (d v).u3 = true) then 2 else 1

/-- **$\prod_{\mathfrak p\nmid I(S)}\gamma_{\mathfrak p}^{-1}$, regularized**: $\mathrm{regProd}(\chi, 1, f)$ with
$f(\mathfrak p) = \gamma_{\mathfrak p}^{-1}$ for $\nu_{\mathfrak p} = 0$ and $1$ otherwise, i.e. $L_F(1,\chi)\prod_{\mathfrak p\mid I(S)}\gamma_{\mathfrak p}$.
*Clarification:* the printed product converges only conditionally. -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (∏_{p ∤ I(S)} γ_p^{-1}, regularized)"]
def prodGammaInvNotDvd (d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ) : ℝ :=
  regProd (fun v => (d v).chi) 1 fun v => if (d v).nu = 0 then ((d v).gamma)⁻¹ else 1

/-- **The tables of Theorem 7.6 and the generic densities of Lemma 7.10 for the true binary local genera** (named input;
Hanke 2011, Def. 7.5, Thm. 7.6 (proof, the two tables, from Lemmas 7.2, 7.3 and the Conway–Sloane $p$-mass formula),
Lemma 7.10, pp. 29–32), for $S$ and its local data $d$ ($d_{\mathfrak p}$ = `d v`).

Fields:
- `nu_eq`: $\nu_{\mathfrak p} = \operatorname{ord}_{\mathfrak p}(S)$;
- `q_eq`: $q_{\mathfrak p} = N\mathfrak p$;
- `dyadic_iff`: the dyadic flag is $\mathfrak p \mid 2$;
- `chi_pm`: $\chi_{\mathfrak p} = \pm1$ (it is $\chi_{\widetilde S}(\mathfrak p)$, the paper's extended Kronecker symbol at $\mathfrak p \mid 2$);
- `generic`: at $\mathfrak p \nmid 2$ with $\nu_{\mathfrak p} = 0$, every admissible binary local genus has density $\gamma_{\mathfrak p}$
  (Lemma 7.10, proof);
- `table_a`: $A^*_{\mathfrak p;2}(S_{\mathfrak p})$, normalized by `betaGen75`, is the table value `LocalDatum.a`;
- `table_b`: $B^*_{\mathfrak p;2}(S_{\mathfrak p})$, normalized by `betaGen75`, is the corrected table value `LocalDatum.bCorr`.

Over $\mathbb Q$ the binary tables are the content of Lemmas 7.2 (proved, `lemma_7_2_*`) and 7.3 (proved, `lemma_7_3_odd`,
`lemma_7_3_two`); over a general $F$ with $2$ split they need the Conway–Sloane/Pall local mass formula over
$F_{\mathfrak p}$ (Remark 7.4), not formalized. Not equivalent to Theorem 7.11 (it says nothing about global classes). -/
@[kb "hanke2011structure" "Def. 7.5, p. 29; Thm. 7.6, proof (tables), pp. 30-31; Lemma 7.10, p. 32 (over F_p)"]
structure BinaryTableHolds (S : AdelicSqCl F) (d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ) : Prop where
  nu_eq : ∀ v, (((d v).nu : ℕ) : ℤ) = adelicOrd v S
  q_eq : ∀ v, (d v).q = (normP v : ℝ)
  dyadic_iff : ∀ v, (d v).dyadic = true ↔ (2 : 𝓞 F) ∈ v.asIdeal
  chi_pm : ∀ v, (d v).chi = 1 ∨ (d v).chi = -1
  generic : ∀ v, (2 : 𝓞 F) ∉ v.asIdeal → adelicOrd v S = 0 → ∀ G ∈ admGenTwo S v, G.beta = (d v).gamma
  table_a : ∀ v, astarLoc S (betaGen75 d) v = (d v).a
  table_b : ∀ v, bstarLoc S (betaGen75 d) v = (d v).bCorr

/-! ### Theorem 7.11 -/

section Main

variable [IsTotallyReal F]

theorem LocalDatum.bCorr_eq_a {d : LocalDatum ℝ} (he : Even d.nu) (hu : d.dyadic = true → d.u3 = true) :
    d.bCorr = d.a := by
  obtain ⟨h1, -, h3⟩ := remark_7_7_local d.chi d.q d.nu
  unfold LocalDatum.bCorr LocalDatum.a
  cases hd : d.dyadic
  · simp [h1, he]
  · have hu3 := hu hd
    by_cases h0 : d.nu = 0
    · simp [bDyadicCorr, hu3, h0, aDyadic]
    · simp [bDyadicCorr, hu3, h0, h3, he]

theorem LocalDatum.bCorr_eq_zero {d : LocalDatum ℝ} (h : ¬ Even d.nu ∨ (d.dyadic = true ∧ ¬ d.u3 = true)) :
    d.bCorr = 0 := by
  obtain ⟨h1, h2, h3⟩ := remark_7_7_local d.chi d.q d.nu
  unfold LocalDatum.bCorr
  rcases h with hodd | ⟨hd, hu⟩
  · have h0 : d.nu ≠ 0 := by rintro h; exact hodd (h ▸ (⟨0, rfl⟩ : Even 0))
    cases hd : d.dyadic
    · simp [h1, hodd]
    · cases hu : d.u3
      · simp [bDyadicCorr, h2]
      · simp [bDyadicCorr, h3, h0, hodd]
  · simp only [hd, if_true]
    simp only [Bool.not_eq_true] at hu
    simp [bDyadicCorr, hu, h2]

/-- **Lemma 7.10, regularized** ($2$ split completely): with the generic densities of Definition 7.5,
$\beta^{-1}_{2,f}(\widetilde S) = \mathrm{regProd}(\chi, 1, \beta_{\mathrm{gen}}^{-1}) = 2^{[F:\mathbb Q]}\,L_F(1,\chi)$, the paper's
$2^{[F:\mathbb Q]}\prod_{\mathfrak p}\gamma_{\mathfrak p}^{-1}$ with $\prod_{\mathfrak p}\gamma_{\mathfrak p}^{-1}$ read as $L_F(1,\chi)$. -/
@[kb "hanke2011structure" "Lemma 7.10, p. 32 (regularized product)"]
theorem betaInvReg_eq_lemma_7_10 (hs : TwoSplitsCompletely F) {S : AdelicSqCl F}
    {d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ} (hd : BinaryTableHolds S d) :
    betaInvReg (fun v => (d v).chi) (betaGen75 d) = 2 ^ Module.finrank ℚ F * LOne (fun v => (d v).chi) := by
  classical
  have hlam : ∀ v, (d v).gamma = 1 - (d v).chi / (normP v : ℝ) := fun v => by
    rw [LocalDatum.gamma, gammaP, hd.q_eq]
  have hpos : ∀ v, 0 < (d v).gamma := fun v => by
    rw [hlam]
    refine one_sub_div_pos ?_ v
    rcases hd.chi_pm v with h | h <;> simp [h]
  set Dy := (finite_dyadic (F := F)).toFinset
  have hg : ∀ v, (betaGen75 d v)⁻¹ * (1 - (d v).chi / (normP v : ℝ)) ^ (1 : ℤ) =
      if (2 : 𝓞 F) ∈ v.asIdeal then 2 else 1 := fun v => by
    have := (hpos v).ne'
    rw [zpow_one, ← hlam, betaGen75]
    by_cases h2 : (2 : 𝓞 F) ∈ v.asIdeal
    · rw [if_pos ((hd.dyadic_iff v).mpr h2), if_pos h2]; field_simp
    · rw [if_neg (fun h => h2 ((hd.dyadic_iff v).mp h)), if_neg h2]; field_simp
  have hsupp : Function.mulSupport (fun v => (betaGen75 d v)⁻¹ * (1 - (d v).chi / (normP v : ℝ)) ^ (1 : ℤ)) ⊆
      Dy := by
    intro v hv
    rw [Function.mem_mulSupport, hg] at hv
    by_contra h
    apply hv
    exact if_neg (fun h2 => h ((Set.Finite.mem_toFinset _).mpr h2))
  unfold betaInvReg regProd
  rw [tprod_eq_prod' hsupp, zpow_one, Finset.prod_congr rfl fun v hv => hg v]
  have hpr : ∏ v ∈ Dy, (if (2 : 𝓞 F) ∈ v.asIdeal then (2 : ℝ) else 1) = ∏ v ∈ Dy, (2 : ℝ) :=
    Finset.prod_congr rfl fun v hv => if_pos ((Set.Finite.mem_toFinset _).mp hv)
  rw [hpr, Finset.prod_const]
  have hc : Dy.card = Module.finrank ℚ F := hs
  rw [hc, mul_comm]

/-- **Theorem 7.11** (Hanke 2011, p. 33), as an identity of the total mass, corrected $\kappa$: for $F$ totally real with $2$
split completely, the totally positive definite signature $\vec\sigma^+_\infty$, every $S$ with
$\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2) \ne \emptyset$ and its local data $d$ satisfying the tables (`BinaryTableHolds`),
$$\sum_{L\in\mathrm{Cls}^*(S,\vec\sigma^+_\infty;2)}\frac1{|\mathrm{Aut}(L)|} =
  \frac{\kappa(S)\,|\Delta_F|^{1/2}\,N_{F/\mathbb Q}(I(S))^{1/2}}{2\,(2\pi)^{[F:\mathbb Q]}}\prod_{\mathfrak p\nmid I(S)}\gamma_{\mathfrak p}(\widetilde S)^{-1}$$
(`kappaCorr`, `prodGammaInvNotDvd`; the left side is the sum of the masses of the genera). *Proof:* Lemma 7.8
(`lemma_7_8_two`) with the generic densities of Definition 7.5, Lemma 7.10 (`betaInvReg_eq_lemma_7_10`), the table
values of $A^*$, $B^*$ (`LocalDatum.a_eq`, `LocalDatum.bCorr_eq_a`, `LocalDatum.bCorr_eq_zero`). *Conditional on* the named
inputs `BinaryLocalGeneraFinite F` and `BinaryTableHolds S d`. -/
@[kb "hanke2011structure" "Thm. 7.11, p. 33 (identity of the total mass; corrected κ)"]
theorem theorem_7_11_two (H : BinaryLocalGeneraFinite F) (hs : TwoSplitsCompletely F) (S : AdelicSqCl F)
    (hne : (GenStar S (totPosSig F 2) ∅ (fun _ => 1)).Nonempty)
    {d : HeightOneSpectrum (𝓞 F) → LocalDatum ℝ} (hd : BinaryTableHolds S d) :
    ∑ᶠ t ∈ GenStar S (totPosSig F 2) ∅ (fun _ => 1), massOfTuple S (totPosSig F 2) ∅ (fun _ => 1) t =
      kappaCorr d * |(discr F : ℝ)| ^ ((1 : ℝ) / 2) * normAssoc S ^ ((1 : ℝ) / 2) /
        (2 * (2 * π) ^ Module.finrank ℚ F) * prodGammaInvNotDvd d := by
  classical
  set χ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (d v).chi with hχdef
  have hlam : ∀ v, (d v).gamma = 1 - (d v).chi / (normP v : ℝ) := fun v => by
    rw [LocalDatum.gamma, gammaP, hd.q_eq]
  have hchi1 : ∀ v, |χ v| ≤ 1 := fun v => by
    rcases hd.chi_pm v with h | h <;> simp [χ, h]
  have hpos : ∀ v, 0 < (d v).gamma := fun v => by rw [hlam]; exact one_sub_div_pos (hchi1 v) v
  -- the bad primes
  set T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_dyadic_two.union (supp_finite S)).toFinset with hT
  have hTout : ∀ v ∉ T, (2 : 𝓞 F) ∉ v.asIdeal ∧ adelicOrd v S = 0 := fun v hv => by
    simp only [hT, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, supp, not_or, not_not] at hv
    exact hv
  have hnu0 : ∀ v ∉ T, (d v).nu = 0 ∧ (d v).dyadic = false := fun v hv => by
    obtain ⟨h2, h0⟩ := hTout v hv
    refine ⟨by have := hd.nu_eq v; omega, ?_⟩
    cases h : (d v).dyadic
    · rfl
    · exact absurd ((hd.dyadic_iff v).mp h) h2
  -- the generic family
  have hgen : IsGenericFamily S (betaGen75 d) χ := by
    refine ⟨fun v => ?_, hchi1, ?_, ?_⟩
    · unfold betaGen75; have := (hpos v).ne'; split_ifs <;> positivity
    · refine T.finite_toSet.subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_setOf_eq] at hv
      apply hv
      intro G hG
      obtain ⟨h2, h0⟩ := hTout v h
      rw [hd.generic v h2 h0 G hG, betaGen75, if_neg (by rw [(hnu0 v h).2]; decide)]
    · refine finite_dyadic_two.subset fun v hv => ?_
      by_contra h
      apply hv
      simp only [Set.mem_setOf_eq] at h
      show betaGen75 d v = 1 - χ v / (normP v : ℝ)
      rw [betaGen75, if_neg (fun h' => h ((hd.dyadic_iff v).mp h')), hlam]
  rw [lemma_7_8_two H S hne hgen, betaInvReg_eq_lemma_7_10 hs hd, epsInf_totPosSig_two]
  -- admissibility of the data
  obtain ⟨t₀, ht₀⟩ := hne
  have hF := genStar_subset_genStarF S (totPosSig F 2) ∅ (fun _ => 1) ht₀
  have hapos : ∀ v, 0 < (d v).a := fun v => by
    rw [← hd.table_a v]
    unfold astarLoc
    have hfin : (admGenTwo S v).Finite := H.finite v _
    have hmem : t₀ v ∈ admGenTwo S v := hF.1 v
    have hβg : 0 < betaGen75 d v := by
      unfold betaGen75; have := hpos v; split_ifs <;> positivity
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.sum_pos (fun G hG => ?_) ⟨t₀ v, (Set.Finite.mem_toFinset _).mpr hmem⟩
    exact div_pos hβg (LocGenus.beta_pos_rank v G ((Set.Finite.mem_toFinset _).mp hG).1)
  have hadm : ∀ v, (d v).Admissible := fun v => by
    refine ⟨hd.chi_pm v, by rw [hd.q_eq]; have := two_le_normP v; positivity, (hpos v).ne', fun hdy => ?_⟩
    have h2 : (2 : 𝓞 F) ∈ v.asIdeal := (hd.dyadic_iff v).mp hdy
    have ha := hapos v
    unfold LocalDatum.a at ha
    rw [if_pos hdy] at ha
    refine ⟨by rw [hd.q_eq]; exact_mod_cast hs.qv_eq_two v h2, fun h1 => ?_, fun h0 => ?_⟩
    · simp [aDyadic, h1] at ha
    · cases hu : (d v).u3
      · simp [aDyadic, h0, hu] at ha
      · rfl
  -- the finite products
  set G : ℝ := ∏ v ∈ T, (if (d v).nu = 0 then 1 else (d v).gamma) with hGdef
  set N : ℝ := ∏ v ∈ T, (d v).q ^ (d v).nu with hNdef
  have hNS : normAssoc S = N := by
    unfold normAssoc
    rw [Tamagawa.finprod_eq_prod_of_one T fun v hv => by rw [(hTout v hv).2, zpow_zero]]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hd.q_eq, ← hd.nu_eq v, zpow_natCast]
  have hNpos : 0 < N := Finset.prod_pos fun v _ => by
    rw [hd.q_eq]; have := two_le_normP v; positivity
  have hA : astarTwo S (betaGen75 d) = N⁻¹ * G := by
    unfold astarTwo
    rw [finprod_congr hd.table_a]
    rw [Tamagawa.finprod_eq_prod_of_one T fun v hv => by
      obtain ⟨h0, hdy⟩ := hnu0 v hv
      simp [LocalDatum.a, hdy, aNondyadic, h0]]
    rw [Finset.prod_congr rfl fun v _ => LocalDatum.a_eq (hadm v), Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    rfl
  have hB : bstarTwo S (betaGen75 d) = (kappaCorr d - 1) * astarTwo S (betaGen75 d) := by
    unfold bstarTwo
    rw [finprod_congr hd.table_b]
    have hout : ∀ v ∉ T, (d v).bCorr = 1 := fun v hv => by
      obtain ⟨h0, hdy⟩ := hnu0 v hv
      simp [LocalDatum.bCorr, hdy, bNondyadic, h0]
    rw [Tamagawa.finprod_eq_prod_of_one T hout]
    unfold kappaCorr
    split_ifs with h
    · unfold astarTwo
      rw [finprod_congr hd.table_a, Tamagawa.finprod_eq_prod_of_one T fun v hv => by
        obtain ⟨h0, hdy⟩ := hnu0 v hv
        simp [LocalDatum.a, hdy, aNondyadic, h0]]
      rw [Finset.prod_congr rfl fun v _ => LocalDatum.bCorr_eq_a (h v).1 (h v).2]
      ring
    · push Not at h
      obtain ⟨v, hv⟩ := h
      have hvT : v ∈ T := by
        by_contra hn
        obtain ⟨h0, hdy⟩ := hnu0 v hn
        have h1 := hv (by rw [h0]; exact ⟨0, rfl⟩)
        rw [hdy] at h1
        exact absurd h1.1 (by decide)
      rw [Finset.prod_eq_zero hvT (LocalDatum.bCorr_eq_zero (by
        by_cases he : Even (d v).nu
        · exact Or.inr ⟨(hv he).1, (hv he).2⟩
        · exact Or.inl he))]
      ring
  have hP : prodGammaInvNotDvd d = LOne χ * G := by
    unfold prodGammaInvNotDvd regProd
    have he : ∀ v, (if (d v).nu = 0 then ((d v).gamma)⁻¹ else 1) * (1 - (d v).chi / (normP v : ℝ)) ^ (1 : ℤ) =
        if (d v).nu = 0 then 1 else (d v).gamma := fun v => by
      rw [zpow_one, ← hlam]
      split_ifs
      · exact inv_mul_cancel₀ (hpos v).ne'
      · exact one_mul _
    have hsupp : Function.mulSupport (fun v => (if (d v).nu = 0 then ((d v).gamma)⁻¹ else 1) *
        (1 - (d v).chi / (normP v : ℝ)) ^ (1 : ℤ)) ⊆ T := by
      intro v hv
      rw [Function.mem_mulSupport, he] at hv
      by_contra h
      exact hv (if_pos (hnu0 v h).1)
    rw [tprod_eq_prod' hsupp, zpow_one, Finset.prod_congr rfl fun v _ => he v]
  rw [hB, hA, hP, hNS]
  have hN32 : N ^ ((3 : ℝ) / 2) = N * N ^ ((1 : ℝ) / 2) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  rw [hN32]
  have h4 : (4 * π) ^ Module.finrank ℚ F = 2 ^ Module.finrank ℚ F * (2 * π) ^ Module.finrank ℚ F := by
    rw [← mul_pow]; ring
  rw [h4]
  have h2π : (2 * π) ^ Module.finrank ℚ F ≠ 0 := by positivity
  have h2d : (2 : ℝ) ^ Module.finrank ℚ F ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end Main

end

end QuadFormsKB.Hanke2011Structure
