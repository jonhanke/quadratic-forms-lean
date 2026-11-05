/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Table

/-!
# Paper 7 at odd primes: the true local mass sums are $A^*_p$ and $B^*_p$

For a place $v \nmid 2$ of $\mathbb Q$ with $p = p_v$ and a squareclass $S \in
\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$ of valuation $\nu = \operatorname{ord}S \ge 0$, the set
$\mathrm{Gen}^*_v(S,\varepsilon;3)$ (`LocGenus.IsGenStar S ε`) of nondegenerate primitive ternary local genera of
Hessian determinant class $S$ and Hasse invariant $\varepsilon$ is, by Lemma 2.1 (`exists_tuple`, `tupG_inj`), in
bijection with the Jordan tuples $(a, b; u_1, u_2, u_3)$ of paper 7 with $a + b = \nu$, $u_1u_2u_3 = u$ and
$c_p = \varepsilon$ (`oddGenera`, `oddHasse`), and the normalized density $(1 - p^{-2})/\beta_{G,v}(G)$ of the genus of a
tuple is paper 7's `normDensity` (`invBeta_eq_normDensity`). Hence:

* `odd_finite`: $\mathrm{Gen}^*_v(S,\varepsilon;3)$ is finite;
* `odd_A`, `odd_B`: $\sum_{G\in\mathrm{Gen}^*(S,1)} \frac{1-p^{-2}}{\beta_G} \pm \sum_{G\in\mathrm{Gen}^*(S,-1)}
  \frac{1-p^{-2}}{\beta_G} = A^*_p$, resp. $B^*_p$ of paper 7 (`Hanke2011Ternary.Astar`, `Bstar` at $(\nu, u=1)$, $\varepsilon' =
  \left(\frac{-1}{p}\right)$); the true unit class of $S$ enters only through the unit $u$ of the Jordan tuples, and
  paper 7's Table 2 shows the sums do not depend on $u$ (`Astar_eq_sum`, `Bstar_eq_sum`);
* `odd_unimodular`: for $\nu = 0$ there is exactly one genus, with $c_p = 1$ and $\beta = 1 - p^{-2}$.

All unconditional. Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "ordS" => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-- The genus map on tuples. -/
def gTup (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℤ) (t : (ℕ × ℕ) × ℤˣ × ℤˣ × ℤˣ) : LocGenus v 3 :=
  tupG v c t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2

theorem gTup_injOn (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (ν : ℕ) (u : ℤˣ) :
    Set.InjOn (gTup v c) (↑(oddGenera ν u) : Set ((ℕ × ℕ) × ℤˣ × ℤˣ × ℤˣ)) := by
  rintro ⟨⟨a, b⟩, e₁, e₂, e₃⟩ ht ⟨⟨a', b'⟩, e₁', e₂', e₃'⟩ ht' h
  simp only [Finset.mem_coe, oddGenera, Finset.mem_filter] at ht ht'
  obtain ⟨h1, h2, h3, h4, h5⟩ := tupG_inj v hv hc ht.2.1 ht'.2.1 h
  subst h1 h2 h3 h4 h5
  rfl

/-- **The genera of $\mathrm{Gen}^*(S, \cdot)$ are the genera of the tuples** (any Hasse invariant): every
$G$ in `{G | G.IsGenStar S c}` is `tupG` of a Jordan tuple with $a + b = \operatorname{ord}S$. -/
theorem genStar_subset (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c₀ : ℤ} (hc : jacobiSym c₀ (pv v) = -1)
    (S : LocalSqCl v) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c} ⊆
      gTup v c₀ '' ↑((antidiagonal (ordS S).toNat) ×ˢ (Finset.univ : Finset (ℤˣ × ℤˣ × ℤˣ))) := by
  have hp2 := pv_ne_two v hv
  rintro G ⟨hN, hP, hd, -⟩
  obtain ⟨a, b, e₁, e₂, e₃, hJ, rfl⟩ := exists_tuple v hv hc G hN hP
  rw [det_tupG hp2 hc] at hd
  have hord := ordZ_zSqCl_odd v (a + b) (not_dvd_detUnit hp2 hc e₁ e₂ e₃)
  rw [hd] at hord
  have hn : (ordS S).toNat = a + b := by rw [hord]; exact Int.toNat_natCast (a + b)
  refine ⟨((a, b), e₁, e₂, e₃), ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ, and_true]
  exact hn.symm

/-- **Finiteness of $\mathrm{Gen}^*_v(S, \varepsilon; 3)$** at $v \nmid 2$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, pp. 4–5 (finiteness of the genera of given determinant)"]
theorem odd_finite (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) (S : LocalSqCl v) (c : ℤ) :
    {G : LocGenus v 3 | G.IsGenStar S c}.Finite := by
  obtain ⟨c₀, hc₀⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  exact ((Finset.finite_toSet _).image (gTup v c₀)).subset (genStar_subset hv hc₀ S c)

/-- **The sets $\mathrm{Gen}^*(S, \varepsilon)$ as images of the tuples of Lemma 2.1.** For $\operatorname{ord}S = \nu$ there is
$u = \pm1$ (the Legendre symbol of the unit part of $S$, up to the factor $8$) such that for $\varepsilon = \pm1$ the set
`{G | G.IsGenStar S ε}` is the image under `gTup` of the tuples of `oddGenera ν u` with Hasse invariant $\varepsilon$. -/
theorem genStar_set (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (S : LocalSqCl v)
    (ν : ℕ) (hS : ordS S = ν) :
    ∃ u : ℤˣ, ∀ cu : ℤˣ, {G : LocGenus v 3 | G.IsGenStar S (cu : ℤ)} =
      gTup v c '' ↑((oddGenera ν u).filter fun t =>
        oddHasse (negOneChar (pv v)) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 = cu) := by
  have hp2 := pv_ne_two v hv
  obtain ⟨u, hu⟩ := exists_u hp2 hc S ν hS
  refine ⟨u, fun cu => ?_⟩
  ext G
  constructor
  · rintro ⟨hN, hP, hd, hh⟩
    obtain ⟨a, b, e₁, e₂, e₃, hJ, rfl⟩ := exists_tuple v hv hc G hN hP
    have hd' := (hu a b e₁ e₂ e₃).1 hd
    have hh' := hasse_tupG hv hc a b e₁ e₂ e₃
    rw [hh] at hh'
    have hcu : oddHasse (negOneChar (pv v)) a b e₁ e₂ e₃ = cu := Units.ext hh'.symm
    refine ⟨((a, b), e₁, e₂, e₃), ?_, rfl⟩
    simp only [Finset.mem_coe, oddGenera, Finset.mem_filter, Finset.mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ, and_true]
    exact ⟨⟨hd'.1, hJ, hd'.2⟩, hcu⟩
  · rintro ⟨⟨⟨a, b⟩, e₁, e₂, e₃⟩, ht, rfl⟩
    simp only [Finset.mem_coe, oddGenera, Finset.mem_filter, Finset.mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ, and_true] at ht
    obtain ⟨⟨hab, hJ, hprod⟩, hcu⟩ := ht
    refine ⟨nondeg_tupG hp2 hc a b e₁ e₂ e₃, prim_tupG hc a b e₁ e₂ e₃,
      (hu a b e₁ e₂ e₃).2 ⟨hab, hprod⟩, ?_⟩
    show (tupG v c a b e₁ e₂ e₃).hasse = _
    rw [hasse_tupG hv hc, hcu]

/-- **The mass sum over $\mathrm{Gen}^*(S, \varepsilon)$ is $\widetilde M^{*,\varepsilon}_p$** of paper 7
(`Hanke2011Ternary.Mstar`), at the unit $u$ of `genStar_set`. -/
theorem sum_genStar (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (S : LocalSqCl v)
    (ν : ℕ) (hS : ordS S = ν) :
    ∃ u : ℤˣ, ∀ cu : ℤˣ,
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (cu : ℤ)}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) =
        ((Mstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) ν u cu : ℚ) : ℝ) := by
  obtain ⟨u, hu⟩ := genStar_set hv hc S ν hS
  refine ⟨u, fun cu => ?_⟩
  rw [hu cu, finsum_mem_image ((gTup_injOn hv hc ν u).mono (by intro t ht; exact (Finset.mem_filter.1 ht).1)),
    finsum_mem_coe_finset, Mstar, Rat.cast_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨⟨a, b⟩, e₁, e₂, e₃⟩ := t
  have hJ := (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2.1
  exact invBeta_eq_normDensity hv hc hJ

section Sums

variable (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal)
include hv

/-- **Paper 7, Theorem 2.4 (Table 2, $A^*$ column) for the true local genera.** For $v \nmid 2$ and $S$ of valuation
$\nu \ge 0$,
$$\sum_{G\in\mathrm{Gen}^*_v(S,1;3)}\frac{1-p^{-2}}{\beta_{G,v}(G)} + \sum_{G\in\mathrm{Gen}^*_v(S,-1;3)}\frac{1-p^{-2}}{\beta_{G,v}(G)}
= A^*_p(\nu)$$
with $A^*_p$ = `Hanke2011Ternary.Astar` at $q = p$, $\varepsilon' = \left(\frac{-1}{p}\right)$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (A* column, true local genera)"]
theorem odd_A (S : LocalSqCl v) (hS : 0 ≤ ordS S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Astar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat 1 : ℚ) : ℝ) := by
  obtain ⟨c, hc⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  have hS' : ordS S = ((ordS S).toNat : ℤ) := (Int.toNat_of_nonneg hS).symm
  obtain ⟨u, hu⟩ := sum_genStar hv hc S _ hS'
  have h1 := hu 1
  have h2 := hu (-1)
  simp only [Units.val_one, Units.val_neg] at h1 h2
  rw [h1, h2, ← Rat.cast_add]
  congr 1
  have hq := cast_pv_gt_one (v := v)
  have e : Mstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u 1 +
      Mstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u (-1) =
      Astar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u := rfl
  rw [e]
  exact (Astar_eq_sum hq (negOneChar (pv v)) _ u).trans (Astar_eq_sum hq (negOneChar (pv v)) _ 1).symm

/-- **Paper 7, Theorem 2.4 (Table 2, $B^*$ column) for the true local genera.** For $v \nmid 2$ and $S$ of valuation
$\nu \ge 0$,
$$\sum_{G\in\mathrm{Gen}^*_v(S,1;3)}\frac{1-p^{-2}}{\beta_{G,v}(G)} - \sum_{G\in\mathrm{Gen}^*_v(S,-1;3)}\frac{1-p^{-2}}{\beta_{G,v}(G)}
= B^*_p(\nu)$$
with $B^*_p$ = `Hanke2011Ternary.Bstar` at $q = p$, $\varepsilon' = \left(\frac{-1}{p}\right)$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (B* column, true local genera)"]
theorem odd_B (S : LocalSqCl v) (hS : 0 ≤ ordS S) :
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Bstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat 1 : ℚ) : ℝ) := by
  obtain ⟨c, hc⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  have hS' : ordS S = ((ordS S).toNat : ℤ) := (Int.toNat_of_nonneg hS).symm
  obtain ⟨u, hu⟩ := sum_genStar hv hc S _ hS'
  have h1 := hu 1
  have h2 := hu (-1)
  simp only [Units.val_one, Units.val_neg] at h1 h2
  rw [h1, h2, ← Rat.cast_sub]
  congr 1
  have hq := cast_pv_gt_one (v := v)
  have e : Mstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u 1 -
      Mstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u (-1) =
      Bstar ((pv v : ℕ) : ℚ) (negOneChar (pv v)) (ordS S).toNat u := rfl
  rw [e]
  exact (Bstar_eq_sum hq (negOneChar (pv v)) _ u).trans (Bstar_eq_sum hq (negOneChar (pv v)) _ 1).symm

/-- **The unimodular case.** For $v \nmid 2$ and $\operatorname{ord}S = 0$ there is exactly one nondegenerate primitive
ternary local genus $G_0$ of Hessian determinant class $S$: it has Hasse invariant $+1$ (so
$\mathrm{Gen}^*_v(S,-1;3) = \emptyset$) and $\beta_{G_0,v}(G_0) = 1 - p^{-2}$. Unconditional. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, case 1, p. 6 (unimodular genus, true local genera)"]
theorem odd_unimodular (S : LocalSqCl v) (hS : ordS S = 0) :
    {G : LocGenus v 3 | G.IsGenStar S (-1)} = ∅ ∧
      ∃ G₀ : LocGenus v 3, {G : LocGenus v 3 | G.IsGenStar S 1} = {G₀} ∧
        G₀.beta = 1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨c, hc⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  have hS' : ordS S = ((0 : ℕ) : ℤ) := by rw [hS]; rfl
  obtain ⟨u, hu⟩ := genStar_set hv hc S 0 hS'
  have hF : oddGenera 0 u = {((0, 0), 1, 1, u)} := by
    ext ⟨⟨a, b⟩, e₁, e₂, e₃⟩
    simp only [oddGenera, Finset.mem_filter, Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_univ,
      and_true, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hab, ⟨-, h1, -, -⟩, hprod⟩
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha hb
      obtain ⟨rfl, rfl⟩ := h1 rfl rfl
      simpa using hprod
    · rintro ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩
      simp [IsJordanTuple]
  have hJ : IsJordanTuple 0 0 1 1 u := by simp [IsJordanTuple]
  have hH : oddHasse (negOneChar (pv v)) 0 0 1 1 u = 1 := oddHasse_case1 _ _ _ _
  have hq := cast_pv_gt_one (v := v)
  have hbeta : (1 - (((pv v : ℕ) : ℝ) ^ 2)⁻¹) / (tupG v c 0 0 1 1 u).beta = 1 := by
    rw [invBeta_eq_normDensity hv hc hJ, normDensity_case1 hq]
    simp
  have hbeta0 : (tupG v c 0 0 1 1 u).beta ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hbeta
    exact zero_ne_one hbeta
  refine ⟨?_, tupG v c 0 0 1 1 u, ?_, ?_⟩
  · have := hu (-1)
    simp only [Units.val_neg, Units.val_one] at this
    rw [this, hF]
    ext G
    simp [hH]
  · have := hu 1
    simp only [Units.val_one] at this
    rw [this, hF]
    ext G
    simp [hH, gTup]
    exact eq_comm
  · exact ((div_eq_one_iff_eq hbeta0).1 hbeta).symm

end Sums

end

end QuadFormsKB.Odd7

#print axioms QuadFormsKB.Odd7.odd_finite
#print axioms QuadFormsKB.Odd7.odd_A
#print axioms QuadFormsKB.Odd7.odd_B
#print axioms QuadFormsKB.Odd7.odd_unimodular
