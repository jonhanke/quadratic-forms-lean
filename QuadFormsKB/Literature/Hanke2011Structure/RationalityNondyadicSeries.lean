/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicGenusNF
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicDensity
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddGenus

/-!
# Paper 6, Theorem 5.4 and Corollary 5.5 at $\mathfrak p \nmid 2$ of every number field, every rank $n$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23, and Cor. 5.5, p. 24.

Let $F$ be a number field, $\mathfrak p$ (`v`) a finite prime with $2 \notin \mathfrak p$, $\mathcal O_{\mathfrak p}$
the completion's integers, $\pi$ = `NF.π v` its uniformizer, $q = |\mathcal O_{\mathfrak p}/\mathfrak p|$.  For a unit
$w \in \mathcal O_{\mathfrak p}^\times$ and a reference genus $G_0$ (nondegenerate, primitive, $\det_H G_0 = [w]$) the
fixed-unit local series
$$\sum_{\nu \ge 0} A^*_{\mathfrak p;n}([\pi^\nu w])\,X^\nu,\qquad \sum_{\nu\ge0} B^*_{\mathfrak p;n}([\pi^\nu w])\,X^\nu
\qquad (X = q^{-s})$$
are rational functions of $X$ (`theorem_5_4_nd_A`, `theorem_5_4_nd_B`), where $A^*$, $B^*$ (`trueAstarNF`,
`trueBstarNF`) are the sums of $\beta(G_0)/\beta(G)$ over the nondegenerate primitive $\mathcal O_{\mathfrak p}$-genera
$G$ of rank $n$ with $\det_H G = [\pi^\nu w]$, without / with the Hasse invariant as a sign.  Corollary 5.5 is the case
$w = 1$ (the distinguished family $\lambda(\pi^i) = \pi^i$).  Unconditional.

*Proof* (the paper's, p. 24: Jordan decompositions at $\mathfrak p \nmid 2$ are diagonal and classified by their
Conway–Sloane-type symbols, O'Meara 92:2).  Every nondegenerate genus is `genND z x`, the genus of
$\operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$ (`exists_genND`); `genND z x = genND z' x'` iff
`symC z x = symC z' x'` (`genND_eq_iff`).  Primitivity, $\det_H$, the Hasse invariant and $\beta$ are read off the
symbol (`prim_genND_iff`, `det_genND_iff`, `hasse_genND`, `beta_genND`).  So the mass sum over
$\mathrm{Gen}^*_{\mathfrak p}([\pi^\nu w],\varepsilon;n)$ is a constant times the $X^\nu$ coefficient of the symbol
generating series with the weights $M_q$, $a_q$ (`sum_genStar_nd_eq`), rational by `RatOdd.rat_Pn`.

Over $F = \mathbb Q$ this recovers `RatOdd.theorem_5_4_odd_A_rank` (the two `A^*` sums are the same definition,
`trueAstarNF_eq`).

Indices are 0-based.
-/

open Finset Matrix IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure
  QuadFormsKB.Hanke2011Structure.RatOdd QuadFormsKB.ConwaySloane QuadFormsKB.Odd7 QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

section NF

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The normalized local mass sum $A^*_{\mathfrak p;n}(S)$** (Def. 4.6) of the local genera of rank $n$ at a finite
prime $\mathfrak p$ of a number field: the sum of $\beta(G_0)/\beta(G)$ over the nondegenerate primitive local genera
$G$ with $\det_H G = S$ (both Hasse invariants). -/
@[kb "hanke2011structure" "Def. 4.6, p. 15 (A*_{p;n}(S), true local genera, every number field)"]
def trueAstarNF (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S 1}, G₀.beta / G.beta) +
    ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S (-1)}, G₀.beta / G.beta

/-- **The normalized local mass sum $B^*_{\mathfrak p;n}(S)$** (Def. 4.6; Hasse invariant as a sign). -/
@[kb "hanke2011structure" "Def. 4.6, p. 15 (B*_{p;n}(S), true local genera, every number field)"]
def trueBstarNF (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S 1}, G₀.beta / G.beta) -
    ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S (-1)}, G₀.beta / G.beta

/-- Over $\mathbb Q$ these are the sums of `RationalityOddGenus`. -/
theorem trueAstarNF_eq (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) :
    trueAstarNF v n G₀ S = trueAstar v n G₀ S := rfl

theorem trueBstarNF_eq (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) :
    trueBstarNF v n G₀ S = trueBstar v n G₀ S := rfl

/-- Every valid finitely supported odd symbol of rank $n$ is `symC z x` (purely combinatorial; the auxiliary prime
$3$ of `RatOdd.exists_symC` plays no role in the conclusion). -/
theorem exists_symC' {σ : OddSymbol} {n : ℕ} (hV : Valid σ) (hF : FinSupp σ) (hr : rkC σ = n) :
    ∃ (z : Fin n → ℕ) (x : Fin n → ℤˣ), symC z x = σ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact exists_symC (p := 3) (by norm_num) hV hF hr

/-- The genus of a symbol: `GsND c n σ` is `genND v c z x` for any `(z, x)` with `symC z x = σ`. -/
def GsND (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F) (n : ℕ) (σ : OddSymbol) : LocGenus v n := by
  classical
  exact if h : ∃ zx : (Fin n → ℕ) × (Fin n → ℤˣ), symC zx.1 zx.2 = σ then genND v c h.choose.1 h.choose.2
    else genND v c (fun _ => 0) (fun _ => 1)

theorem GsND_symC (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) : GsND v c n (symC z x) = genND v c z x := by
  classical
  have h : ∃ zx : (Fin n → ℕ) × (Fin n → ℤˣ), symC zx.1 zx.2 = symC z x := ⟨(z, x), rfl⟩
  unfold GsND
  rw [dif_pos h]
  exact (genND_eq_iff hv hcU hc _ _ _ _).2 h.choose_spec

/-- The unit class $e = \chi(2)^n\chi(w)$ of the symbols of determinant $[\pi^\nu w]$. -/
def eND (n : ℕ) (w : 𝔬) : ℤˣ := sgn 𝔬 (2 : 𝔬) ^ n * sgn 𝔬 w

/-- **The genera of $\mathrm{Gen}^*_{\mathfrak p}([\pi^\nu w],\varepsilon;n)$ are the genera of the symbols of
`symTarget`.** -/
theorem genStar_nd_eq_image (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    {w : 𝔬} (hw : IsUnit w) (ν : ℕ) (ε : ℤ) :
    {G : LocGenus v n | G.IsGenStar (sqNF (LocalDensity.NF.π v ^ ν * w)) ε} =
      GsND v c n '' symTarget (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε n ν := by
  ext G
  constructor
  · rintro ⟨hN, hP, hd, hh⟩
    obtain ⟨z, x, rfl⟩ := exists_genND hv hcU hc G hN
    rw [prim_genND_iff hv hcU] at hP
    rw [det_genND_iff hv hcU hc z x hw] at hd
    rw [hasse_genND hv hcU hc] at hh
    refine ⟨symC z x, ⟨⟨?_, (one_le_dim_symC_iff z x).2 hP⟩, ?_, ?_⟩, GsND_symC hv hcU hc z x⟩
    · rw [← hd.1]; exact symC_mem z x
    · rw [statC_symC]; simp only [evZ_mul_odZ]; exact hd.2
    · rw [hasse_obs_symC]; exact hh
  · rintro ⟨σ, ⟨⟨hσ, hdim⟩, hc1, hc2⟩, rfl⟩
    obtain ⟨z, x, rfl⟩ := exists_symC' hσ.1 hσ.2.1 hσ.2.2.1
    have hzs : ∑ i, z i = ν := by rw [← zsC_symC z x]; exact hσ.2.2.2
    rw [GsND_symC hv hcU hc]
    refine ⟨nondeg_genND hv hcU z x, (prim_genND_iff hv hcU z x).2 ((one_le_dim_symC_iff z x).1 hdim),
      (det_genND_iff hv hcU hc z x hw ν).2 ⟨hzs, ?_⟩, ?_⟩
    · rw [statC_symC] at hc1; simp only [evZ_mul_odZ] at hc1; exact hc1
    · rw [hasse_genND hv hcU hc]; rw [hasse_obs_symC] at hc2; exact hc2

theorem genStar_nd_injOn (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (eps e : ℤˣ) (ε : ℤ) (ν : ℕ) : Set.InjOn (GsND v c n) (symTarget eps e ε n ν) := by
  intro σ₁ h₁ σ₂ h₂ h
  obtain ⟨z₁, x₁, rfl⟩ := exists_symC' h₁.1.1.1 h₁.1.1.2.1 h₁.1.1.2.2.1
  obtain ⟨z₂, x₂, rfl⟩ := exists_symC' h₂.1.1.1 h₂.1.1.2.1 h₂.1.1.2.2.1
  rw [GsND_symC hv hcU hc, GsND_symC hv hcU hc] at h
  exact (genND_eq_iff hv hcU hc _ _ _ _).1 h

/-- The factor weight at $\mathfrak p$: $M_q$ with $q = |\mathcal O_{\mathfrak p}/\mathfrak p|$ and $e = \chi(-1)$. -/
def MND (v : HeightOneSpectrum (𝓞 F)) : ℕ → Sign → ℝ :=
  Mq (DVR.q (v.adicCompletionIntegers F)) (sgn (v.adicCompletionIntegers F) (-1 : v.adicCompletionIntegers F))

/-- The gap weight at $\mathfrak p$: $a_q$. -/
def aND (v : HeightOneSpectrum (𝓞 F)) : ℕ → ℝ := aq (DVR.q (v.adicCompletionIntegers F))

/-- **The mass sum over $\mathrm{Gen}^*_{\mathfrak p}([\pi^\nu w],\varepsilon;n)$ is a coefficient of the symbol
generating series** (a constant independent of $\nu$ and $\varepsilon$ times it). -/
theorem sum_genStar_nd_eq (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    {w : 𝔬} (hw : IsUnit w) (G₀ : LocGenus v n) (hN₀ : G₀.Nondeg) :
    ∃ K : ℝ, ∀ (ν : ℕ) (ε : ℤ),
      ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (sqNF (LocalDensity.NF.π v ^ ν * w)) ε}, G₀.beta / G.beta =
        K * coef (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε) n ν := by
  obtain ⟨z₀, x₀, rfl⟩ := exists_genND hv hcU hc G₀ hN₀
  refine ⟨(wtC (MND v) (aND v) (symC z₀ x₀))⁻¹, fun ν ε => ?_⟩
  rw [genStar_nd_eq_image hv hcU hc hw ν ε, finsum_mem_image (genStar_nd_injOn hv hcU hc _ _ _ _)]
  have step : ∀ σ ∈ symTarget (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε n ν,
      (genND v c z₀ x₀).beta / (GsND v c n σ).beta =
        (wtC (MND v) (aND v) (symC z₀ x₀))⁻¹ * wtC (MND v) (aND v) σ := by
    intro σ hσ
    obtain ⟨z, x, rfl⟩ := exists_symC' hσ.1.1.1 hσ.1.1.2.1 hσ.1.1.2.2.1
    rw [GsND_symC hv hcU hc, beta_genND hv hcU hc, beta_genND hv hcU hc, div_eq_mul_inv, inv_inv, mul_inv]
    unfold MND aND
    ring
  rw [finsum_mem_congr rfl step, ← mul_finsum_mem]
  congr 1
  unfold coef
  set T := symTarget (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε n ν with hT
  set s : Set OddSymbol := {σ | σ ∈ symSet n ν ∧ (fun f : OddFactor => 1 ≤ f.dim) (σ 0)} with hs
  have hsf : s.Finite := (symSet_finite n ν).subset (fun σ h => h.1)
  have hTs : T ⊆ s := fun σ h => h.1
  rw [← finsum_mem_add_sdiff hTs hsf]
  have h0 : ∑ᶠ σ ∈ s \ T, phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε (statC σ) * wtC (MND v) (aND v) σ = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    have : ¬ ((statC σ).1 * (statC σ).2.1 = eND n w ∧
        ((hasseObs (sgn 𝔬 (-1 : 𝔬)) (statC σ) : ℤˣ) : ℤ) = ε) := fun h => hσ.2 ⟨hσ.1, h⟩
    unfold phiObs
    rw [if_neg this, zero_mul]
  have h1 : ∑ᶠ σ ∈ T, phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) ε (statC σ) * wtC (MND v) (aND v) σ =
      ∑ᶠ σ ∈ T, wtC (MND v) (aND v) σ := by
    refine finsum_mem_congr rfl fun σ hσ => ?_
    unfold phiObs
    rw [if_pos hσ.2, one_mul]
  rw [h0, h1, add_zero]

theorem exists_nonres_nf (hv : (2 : 𝓞 F) ∉ v.asIdeal) : ∃ c : 𝔬, IsUnit c ∧ chiR c = -1 :=
  exists_nonres (LocalDensity.NF.irreducible_π v) (not_dvd_two_nf v hv)

/-- **Theorem 5.4 (for $A^*$) at $\mathfrak p \nmid 2$ of a number field $F$, every rank $n$.**  For a finite prime
$\mathfrak p \nmid 2$ of $F$, a unit $w \in \mathcal O_{\mathfrak p}^\times$ and a reference genus $G_0$ with
$G_0 \in \mathrm{Gen}^*_{\mathfrak p}([w],\varepsilon_0;n)$ for some $\varepsilon_0$, the fixed-unit series
$\sum_\nu A^*_{\mathfrak p;n}([\pi^\nu w])X^\nu$ ($X = q^{-s}$, $\pi$ a uniformizer) is a rational function of $X$:
$P/Q$ for polynomials $P$, $Q$ with $Q(0) \ne 0$.  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (A*, every rank n, every number field, p ∤ 2)"]
theorem theorem_5_4_nd_A (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {w : 𝔬} (hw : IsUnit w)
    (G₀ : LocGenus v n) (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (sqNF w) ε₀) :
    RatSeries (PowerSeries.mk fun ν : ℕ =>
      trueAstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  obtain ⟨K, hK⟩ := sum_genStar_nd_eq hv hcU hc hw G₀ (by obtain ⟨ε₀, h, -⟩ := hG₀; exact h)
  have hM : MND v 0 Sign.plus = 1 := Mq_zero _ _
  have ha : aND v 0 = 1 := aq_zero _
  have e : (PowerSeries.mk fun ν : ℕ => trueAstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) 1) n +
          ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueAstarNF, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (rat_Pn hM ha n _))

/-- **Theorem 5.4 (for $B^*$) at $\mathfrak p \nmid 2$ of a number field $F$, every rank $n$**: the fixed-unit series
$\sum_\nu B^*_{\mathfrak p;n}([\pi^\nu w])X^\nu$ is a rational function of $X = q^{-s}$.  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (B*, every rank n, every number field, p ∤ 2)"]
theorem theorem_5_4_nd_B (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} {w : 𝔬} (hw : IsUnit w)
    (G₀ : LocGenus v n) (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (sqNF w) ε₀) :
    RatSeries (PowerSeries.mk fun ν : ℕ =>
      trueBstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) := by
  obtain ⟨c, hcU, hc⟩ := exists_nonres_nf hv
  obtain ⟨K, hK⟩ := sum_genStar_nd_eq hv hcU hc hw G₀ (by obtain ⟨ε₀, h, -⟩ := hG₀; exact h)
  have hM : MND v 0 Sign.plus = 1 := Mq_zero _ _
  have ha : aND v 0 = 1 := aq_zero _
  have e : (PowerSeries.mk fun ν : ℕ => trueBstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) 1) n +
          PowerSeries.C (-1) * PowerSeries.X ^ 0 *
            ser (MND v) (aND v) (fun f => 1 ≤ f.dim) (phiObs (sgn 𝔬 (-1 : 𝔬)) (eND n w) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueBstarNF, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
    ring
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (RatSeries.CXpowMul (-1) 0 (rat_Pn hM ha n _)))

/-- **Corollary 5.5 for $A^*$ at $\mathfrak p \nmid 2$ of a number field, every rank $n$** (distinguished family
$\lambda(\pi^i) = \pi^i$, i.e. $w = 1$): the Euler factor $\sum_iA^*_{\mathfrak p;n}([\pi^i])\,q^{-is}$ is a rational
function of $q^{-s}$. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, every rank n, every number field, p ∤ 2, lambda(π^i) = π^i)"]
theorem cor_5_5_nd_A (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n)
    (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (sqNF (1 : 𝔬)) ε₀) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueAstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ i))) := by
  simpa only [mul_one] using theorem_5_4_nd_A hv isUnit_one G₀ hG₀

/-- **Corollary 5.5 for $B^*$ at $\mathfrak p \nmid 2$ of a number field, every rank $n$** ($\lambda(\pi^i) = \pi^i$). -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, every rank n, every number field, p ∤ 2, lambda(π^i) = π^i)"]
theorem cor_5_5_nd_B (hv : (2 : 𝓞 F) ∉ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n)
    (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (sqNF (1 : 𝔬)) ε₀) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueBstarNF v n G₀ (sqNF (LocalDensity.NF.π v ^ i))) := by
  simpa only [mul_one] using theorem_5_4_nd_B hv isUnit_one G₀ hG₀

end NF

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.theorem_5_4_nd_A
#print axioms QuadFormsKB.Hanke2011Structure.RatND.theorem_5_4_nd_B
#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_A
#print axioms QuadFormsKB.Hanke2011Structure.RatND.cor_5_5_nd_B
