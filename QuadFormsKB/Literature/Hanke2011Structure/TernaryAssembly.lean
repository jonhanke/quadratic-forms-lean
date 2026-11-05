/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.RationalLocalTuples
import QuadFormsKB.Literature.Hanke2011Structure.TernaryTupleSum
import QuadFormsKB.Tamagawa.Dyadic7Table
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Paper 6, Theorem 4.8 for the true local genera over $\mathbb Q$, $n = 3$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 4.8, p. 17, Rem. 4.14, p. 20, and Cor. 4.15, p. 20, for $F = \mathbb Q$,
$n = 3$, $\varepsilon_\infty = 1$, $\mathbb S = \emptyset$; with paper 7 (`hanke2011ternary`), §§2–7.

This file assembles the primitive total adelic mass $M^*_{1;3}(N)$ (Def. 3.5, `totalMassM`, a sum over the tuples of true
local genera) from local information at each prime:

* **Part A (valuations).** The class of $N$ in $\mathrm{SqCl}(\mathbb Q_p^\times,\mathbb Z_p^\times)$ has valuation
  $\operatorname{ord}_p N$ (`ordZ_zSqCl_eq`), and the local component of $\mathrm{ratS}(N)$ is that class.
* **Part B (the assembly).** Given a base tuple $(b_p)$ of local genera, equal to the unique admissible genus at the
  primes $p \nmid 2N$ and with $\prod_p\beta(b_p)^{-1} = 4\zeta(2)$ (Rem. 4.14 over $\mathbb Q$), the sign-constrained sum over
  tuples (`finsum_tuple_sign`) gives
  $$M^*_{1;3}(N) = 4\zeta(2)\cdot\tfrac12\Bigl[\prod_{p\mid 2N}A^*_p(N) + \prod_{p\mid 2N}B^*_p(N)\Bigr],$$
  $A^*_p$, $B^*_p$ the normalized local mass sums (Def. 4.6) relative to $b_p$ (`totalMassM_eq_half`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset

namespace QuadFormsKB.Hanke2011Structure

open QuadFormsKB.Dyadic7 QuadFormsKB.ConwaySloane QuadFormsKB.ConwaySloane.Mass QuadFormsKB.NFEuler Cassels

open Classical

noncomputable section

/-! ### Part A: the valuation of the class of an integer -/

section Valuation

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- $n \in \mathfrak p^k$ iff $p^k \mid n$, for a rational integer $n$ and the prime $\mathfrak p = p\mathbb Z$. -/
theorem intCast_mem_pow_iff (k : ℕ) (n : ℤ) :
    (n : 𝓞 ℚ) ∈ v.asIdeal ^ k ↔ ((ConwaySloane.Mass.pv v : ℤ) ^ k) ∣ n := by
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
  change _ ↔ n ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} ^ k
  rw [Rat.HeightOneSpectrum.span_natGenerator, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap,
    Tamagawa.RatHeadline3.intEquiv_symm_intCast]

/-- **The valuation of the class of a nonzero integer:** $\operatorname{ord}_p[n] = \operatorname{ord}_p(n)$. -/
theorem ordZ_zSqCl_eq {n : ℤ} (hn : n ≠ 0) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v n) = padicValInt (ConwaySloane.Mass.pv v) n := by
  have hp : (ConwaySloane.Mass.pv v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  haveI := Fact.mk hp
  set k := padicValInt (ConwaySloane.Mass.pv v) n with hk
  have h1 : v.intValuation (n : 𝓞 ℚ) ≤ WithZero.exp (-((k : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ k).mpr ((intCast_mem_pow_iff v k n).mpr (padicValInt_dvd n))
  have h2 : ¬ v.intValuation (n : 𝓞 ℚ) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := fun h => by
    have hd := (intCast_mem_pow_iff v (k + 1) n).mp ((v.intValuation_le_pow_iff_mem _ (k + 1)).mp h)
    rcases (padicValInt_dvd_iff (k + 1) n).mp hd with h0 | h0
    · exact hn h0
    · omega
  have hvalQ : v.valuation ℚ (n : ℚ) = v.intValuation (n : 𝓞 ℚ) := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v (n : 𝓞 ℚ)
    simpa only [map_intCast] using this
  have hne : v.intValuation (n : 𝓞 ℚ) ≠ 0 := by
    rw [← hvalQ]; exact (Valuation.ne_zero_iff _).mpr (by exact_mod_cast hn)
  have hval : Valued.v (((n : ℚ) : v.adicCompletion ℚ)) = v.intValuation (n : 𝓞 ℚ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
    simp only [map_intCast] at h
    rw [show (((n : ℚ) : v.adicCompletion ℚ)) = ((n : ℤ) : v.adicCompletion ℚ) by push_cast; rfl]
    rw [← hvalQ, ← h]
  rw [zSqCl_of_ne v hn, SqCl.ordZ_mk]
  change -WithZero.log (Valued.v (((n : ℚ) : v.adicCompletion ℚ))) = _
  rw [hval]
  have hk' := WithZero.exp_log hne
  rw [← hk'] at h1 h2
  rw [WithZero.exp_le_exp] at h1 h2
  push_cast at h1 h2
  omega

end Valuation

/-! ### Part B: the assembly over the tuples of local genera -/

section Assembly

/-- The admissible local genera at $v$ for the adelic squareclass $S$: nondegenerate, primitive, $\det_H = S_v$
(the set $\mathrm{Gen}^*_v(S_v,+;3) \cup \mathrm{Gen}^*_v(S_v,-;3)$). -/
def admGen (S : AdelicSqCl ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (LocGenus v 3) :=
  {G | G.Nondeg ∧ G.Prim ∧ G.det = AdelicSqCl.comp v S}

theorem genStarF_eq_admGen (S : AdelicSqCl ℚ) : (GenStarF S 1 ∅ (fun _ => 1) : Set (LocTuple ℚ 3)) =
    {t | (∀ v, t v ∈ admGen S v) ∧ (Function.mulSupport fun v => (t v).hasse).Finite ∧
      ∏ᶠ v, (t v).hasse = 1} := by
  ext t
  simp [GenStarF, admGen]

/-- **Theorem 4.8 for the true local genera over $\mathbb Q$, $n = 3$** (sign-sum form): for a base tuple $(b_v)$ that is the only
admissible genus outside the finite set $P$, with $c_v(b_v) = 1$ there and $\prod_v\beta(b_v)^{-1} = C$,
$$M^*_{1;3}(S) = C\cdot\frac12\Bigl[\prod_{v\in P}\sum_{G}\frac{\beta(b_v)}{\beta(G)} + \prod_{v\in P}\sum_{G}c_v(G)\frac{\beta(b_v)}{\beta(G)}\Bigr],$$
the sums over the admissible genera at $v$. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, and its proof, eqs. (11)-(12), p. 18 (F = Q, n = 3, true local genera)"]
theorem totalMassM_eq_half (S : AdelicSqCl ℚ) (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (b : LocTuple ℚ 3) (C : ℝ)
    (hout : ∀ v ∉ P, admGen S v = {b v}) (hb1 : ∀ v ∉ P, (b v).hasse = 1) (hbnd : ∀ v, (b v).Nondeg)
    (hfin : ∀ v ∈ P, (admGen S v).Finite) (hprod : HasProd (fun v => ((b v).beta)⁻¹) C) :
    totalMassM 3 S 1 ∅ (fun _ => 1) = C * ((∏ v ∈ P, ∑ᶠ G ∈ admGen S v, (b v).beta / G.beta) +
      ∏ v ∈ P, ∑ᶠ G ∈ admGen S v, ((G.hasse : ℤ) : ℝ) * ((b v).beta / G.beta)) / 2 := by
  unfold totalMassM
  rw [genStarF_eq_admGen]
  have hT : ∀ t ∈ {t : LocTuple ℚ 3 | (∀ v, t v ∈ admGen S v) ∧
      (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = 1},
      invDensityTuple t = C * ∏ v ∈ P, (b v).beta / (t v).beta := by
    rintro t ⟨hA, -⟩
    have hout' : ∀ v ∉ P, (t v).beta = (b v).beta := fun v hv => by
      have h := hA v
      rw [hout v hv] at h
      rw [Set.mem_singleton_iff.mp h]
    obtain ⟨hm, he⟩ := invDensity_factor P (fun v => (b v).beta) (fun v => (t v).beta) hout'
      (fun v => (Dyadic7.LocGenus.beta_pos _ _ (hbnd v)).ne')
      (fun v => (Dyadic7.LocGenus.beta_pos _ _ (hA v).1).ne') hprod.multipliable
    unfold invDensityTuple
    rw [if_pos hm, he, hprod.tprod_eq]
  rw [finsum_mem_congr rfl hT, ← mul_finsum_mem,
    finsum_tuple_sign P b (admGen S) (fun v G => G.hasse) (fun v G => (b v).beta / G.beta) hout hb1 hfin
      (fun v G => Dyadic7.LocGenus.hasse_pm _ G)]
  ring

theorem admGen_eq_union (S : AdelicSqCl ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    admGen S v = {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} ∪
      {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
  ext G
  simp only [admGen, LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_union]
  rcases Dyadic7.LocGenus.hasse_pm _ G with h | h <;> simp [h]

/-- The sum over the admissible genera splits by the Hasse invariant: $A^* = \widetilde M^+ + \widetilde M^-$. -/
theorem finsum_admGen_split (S : AdelicSqCl ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocGenus v 3 → ℝ)
    (hfin : (admGen S v).Finite) :
    ∑ᶠ G ∈ admGen S v, f G = (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) +
      ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have hU : admGen S v = {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} ∪
      {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
    ext G
    simp only [admGen, LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_union]
    rcases Dyadic7.LocGenus.hasse_pm _ G with h | h <;> simp [h]
  have hD : Disjoint {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}
      {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)} := by
    rw [Set.disjoint_left]
    rintro G ⟨-, -, -, h1⟩ ⟨-, -, -, h2⟩
    rw [h1] at h2; exact absurd h2 (by decide)
  rw [hU] at hfin ⊢
  exact finsum_mem_union hD (hfin.subset Set.subset_union_left) (hfin.subset Set.subset_union_right)

/-- $B^* = \widetilde M^+ - \widetilde M^-$. -/
theorem finsum_admGen_split_hasse (S : AdelicSqCl ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) (f : LocGenus v 3 → ℝ)
    (hfin : (admGen S v).Finite) :
    ∑ᶠ G ∈ admGen S v, ((G.hasse : ℤ) : ℝ) * f G =
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1}, f G) -
        ∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}, f G := by
  have h2fin : {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) (-1)}.Finite := by
    rw [admGen_eq_union] at hfin; exact hfin.subset Set.subset_union_right
  rw [finsum_admGen_split S v _ hfin, sub_eq_add_neg, ← finsum_mem_neg_distrib _ h2fin]
  congr 1
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp
  · refine finsum_mem_congr rfl fun G hG => ?_
    rw [hG.2.2.2]; simp

end Assembly

/-! ### Part C: the local data of $N$ -/

section LocalN

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The local component of $\mathrm{ratS}(N)$ at $v$ is the class of $N$. -/
theorem comp_ratS_natCast {N : ℕ} (hN : (N : ℚ) ≠ 0) :
    AdelicSqCl.comp v (ratS (Units.mk0 (N : ℚ) hN)) = zSqCl v (N : ℤ) := by
  have hN' : ((N : ℤ)) ≠ 0 := by exact_mod_cast hN
  rw [zSqCl_of_ne v hN', ratS, AdelicSqCl.comp_mk, ideleComp_unitEmbedding]
  congr 1
  apply Units.ext
  simp [unitsToLocal]

theorem pv_prime' (v : HeightOneSpectrum (𝓞 ℚ)) : (ConwaySloane.Mass.pv v).Prime :=
  Rat.HeightOneSpectrum.prime_natGenerator v

/-- The valuation of the class of $N$ at $v$ is $\operatorname{ord}_p N$. -/
theorem ordZ_comp_ratS {N : ℕ} (hN : (N : ℚ) ≠ 0) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (AdelicSqCl.comp v (ratS (Units.mk0 (N : ℚ) hN))) =
      (N.factorization (ConwaySloane.Mass.pv v) : ℤ) := by
  have hN' : ((N : ℤ)) ≠ 0 := by exact_mod_cast hN
  rw [comp_ratS_natCast v hN, ordZ_zSqCl_eq v hN', padicValInt.of_nat, Nat.factorization_def _
    (pv_prime' v)]

/-- **No primitive ternary $\mathbb Z_2$-genus has odd Hessian determinant** (Hanke 2011, Lemma 2.5, $n = 3$): at $v \mid 2$ the
admissible set of a squareclass of valuation $0$ is empty. -/
theorem admGen_two_empty (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (S : AdelicSqCl ℚ)
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) (AdelicSqCl.comp v S) = 0) : admGen S v = ∅ := by
  ext G
  simp only [admGen, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hn, -, hd⟩
  obtain ⟨D, hD, h0, hdim, hev, rfl⟩ := exists_genusOf v h2 G hn
  have hpo : Odd (unitProd D) :=
    Int.not_even_iff_odd.mp (fun he => odd_unitProd _ hD (even_iff_two_dvd.mp he))
  rw [det_genusOf v hD h0 hdim hev] at hd
  have hval : valSum D = 0 := by
    have := congrArg (SqCl.ordZ (localOrd v) (localUnits_le_ker v)) hd
    rw [ordZ_zSqCl v h2 _ hpo, hS] at this
    exact_mod_cast this
  have h2d := hessian_det_mem_span_two_of_odd (R := ℤ) (n := 3) (by decide) (formZ 3 D)
  rw [hessian_formZ hdim h0 hev, det_hessZ hdim h0, hval, pow_zero, one_mul, Ideal.mem_span_singleton] at h2d
  exact (Int.not_even_iff_odd.mpr hpo) (even_iff_two_dvd.mpr h2d)

end LocalN

/-! ### Part D: primes of $\mathbb Q$ as places, and the Euler product of the base densities -/

section Places

open Rat.HeightOneSpectrum

/-- The places of $\mathbb Q$ above the prime divisors of $M$. -/
def placesOf (M : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  M.primeFactors.attach.image fun p => primesEquiv.symm (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)

theorem pv_primesEquiv_symm (p : Nat.Primes) : ConwaySloane.Mass.pv (primesEquiv.symm p) = p :=
  congrArg Subtype.val (primesEquiv.apply_symm_apply p)

theorem pv_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (ConwaySloane.Mass.pv v).Prime := prime_natGenerator v

theorem mem_placesOf {M : ℕ} (hM : M ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf M ↔ ConwaySloane.Mass.pv v ∣ M := by
  constructor
  · rintro hv
    rw [placesOf] at hv
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hv
    have e := pv_primesEquiv_symm (⟨p.1, Nat.prime_of_mem_primeFactors p.2⟩ : Nat.Primes)
    have hd := Nat.dvd_of_mem_primeFactors p.2
    calc ConwaySloane.Mass.pv _ = p.1 := e
      _ ∣ M := hd
  · intro h
    rw [placesOf]
    refine Finset.mem_image.mpr ⟨⟨ConwaySloane.Mass.pv v, Nat.mem_primeFactors.mpr ⟨pv_prime v, h, hM⟩⟩,
      Finset.mem_attach _ _, ?_⟩
    apply primesEquiv.injective
    exact primesEquiv.apply_symm_apply _

theorem prod_placesOf (M : ℕ) (F : ℕ → ℝ) :
    ∏ v ∈ placesOf M, F (ConwaySloane.Mass.pv v) = ∏ p ∈ M.primeFactors, F p := by
  rw [placesOf, Finset.prod_image]
  · rw [← Finset.prod_attach M.primeFactors F]
    exact Finset.prod_congr rfl fun x _ => congrArg F (pv_primesEquiv_symm _)
  · intro p _ q _ h
    have := congrArg Subtype.val (primesEquiv.symm.injective h)
    exact Subtype.ext this

theorem two_mem_iff_pv (v : HeightOneSpectrum (𝓞 ℚ)) :
    (2 : 𝓞 ℚ) ∈ v.asIdeal ↔ ConwaySloane.Mass.pv v = 2 := by
  refine ⟨ConwaySloane.Mass.pv_eq_two_of_two_mem v, fun h => ?_⟩
  have := (Tamagawa.RatHeadline3.intCast_mem_iff v 2).mpr (by
    show ((ConwaySloane.Mass.pv v : ℕ) : ℤ) ∣ 2
    rw [h]; norm_num)
  exact_mod_cast this

/-- **The Euler product of the base densities:** $\prod_v g_v = 4\zeta(2)$ for $g_v = (1 - p^{-2})^{-1}$ ($p$ odd) and
$g_2 = 16/3$. -/
theorem hasProd_baseInv :
    HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if (2 : 𝓞 ℚ) ∈ v.asIdeal then (16 / 3 : ℝ) else (1 - ((ConwaySloane.Mass.pv v : ℝ) ^ 2)⁻¹)⁻¹)
      (4 * zetaR 2) := by
  have h0 : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) => (1 - ((ConwaySloane.Mass.pv v : ℕ) : ℝ) ^ (-(2 : ℝ)))⁻¹)
      (zetaR 2) :=
    (primesEquiv.hasProd_iff (f := fun p : Nat.Primes => (1 - ((p : ℕ) : ℝ) ^ (-(2 : ℝ)))⁻¹)).mpr
      (hasProd_zetaR (by norm_num))
  let v₂ : HeightOneSpectrum (𝓞 ℚ) := primesEquiv.symm (⟨2, Nat.prime_two⟩ : Nat.Primes)
  have hv₂ : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal ↔ v = v₂ := by
    intro v
    rw [two_mem_iff_pv]
    constructor
    · intro h
      apply primesEquiv.injective
      exact (Subtype.ext h : primesEquiv v = (⟨2, Nat.prime_two⟩ : Nat.Primes)).trans
        (primesEquiv.apply_symm_apply _).symm
    · rintro rfl
      exact pv_primesEquiv_symm _
  have hc : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) => if (2 : 𝓞 ℚ) ∈ v.asIdeal then (4 : ℝ) else 1) 4 := by
    have := hasProd_single (f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if (2 : 𝓞 ℚ) ∈ v.asIdeal then (4 : ℝ) else 1) v₂ (fun w hw => by
        simp only [hv₂ w, hw, if_false])
    simpa [hv₂ v₂] using this
  have h := h0.mul hc
  rw [mul_comm] at h
  refine h.congr_fun fun v => ?_
  have hrp : ((ConwaySloane.Mass.pv v : ℕ) : ℝ) ^ (-(2 : ℝ)) = ((ConwaySloane.Mass.pv v : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrp]
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · rw [if_pos h2, if_pos h2, (two_mem_iff_pv v).mp h2]
    norm_num
  · rw [if_neg h2, if_neg h2, mul_one]

end Places

/-! ### Part E: $M^*_{1;3}(N) = 2\zeta(2)(A^*_3(N) + B^*_3(N))$ from the local tables -/

section Main

open Hanke2011Ternary

local notation "pv" => ConwaySloane.Mass.pv
local notation "ordS" v => SqCl.ordZ (localOrd v) (localUnits_le_ker v)

/-- **The odd-prime local input, as used by the assembly** (to be supplied by the identification of paper 7's
model at $p \nmid 2$ with the true local genera): finiteness, the values $A^*_p$, $B^*_p$ of Table 2 for the normalized
local mass sums, and the unimodular case. -/
structure OddTernaryLocalData : Prop where
  fin : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → ∀ (S : LocalSqCl v) (c : ℤ),
    {G : LocGenus v 3 | G.IsGenStar S c}.Finite
  A_eq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → ∀ S : LocalSqCl v, 0 ≤ (ordS v) S →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((pv v : ℝ) ^ 2)⁻¹) / G.beta) +
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((pv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Astar (pv v) (negOneChar (pv v)) ((ordS v) S).toNat 1 : ℚ) : ℝ)
  B_eq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → ∀ S : LocalSqCl v, 0 ≤ (ordS v) S →
    (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S 1}, (1 - ((pv v : ℝ) ^ 2)⁻¹) / G.beta) -
      (∑ᶠ G ∈ {G : LocGenus v 3 | G.IsGenStar S (-1)}, (1 - ((pv v : ℝ) ^ 2)⁻¹) / G.beta) =
      ((Bstar (pv v) (negOneChar (pv v)) ((ordS v) S).toNat 1 : ℚ) : ℝ)
  unimod : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∉ v.asIdeal → ∀ S : LocalSqCl v, (ordS v) S = 0 →
    {G : LocGenus v 3 | G.IsGenStar S (-1)} = ∅ ∧
      ∃ G₀ : LocGenus v 3, {G : LocGenus v 3 | G.IsGenStar S 1} = {G₀} ∧ G₀.beta = 1 - ((pv v : ℝ) ^ 2)⁻¹

/-- The base genus at $v \mid 2$: $\det_H = \widetilde S$ for $S = [2^a u]$. -/
theorem base_det_two {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) (a : ℕ) :
    (genusOf v 3 (baseList u)).Nondeg ∧ (genusOf v 3 (baseList u)).Prim ∧
      (genusOf v 3 (baseList u)).det = tildeTernary v (zSqCl v (2 ^ a * u)) := by
  obtain ⟨hv, h0, hn, hev, hpr, hval, hunit, -⟩ := baseList_props hu
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  refine ⟨nondeg_genusOf v hv h0 hn hev, (prim_genusOf_iff v h2 hn).mpr hpr, ?_⟩
  rw [tildeTernary_zSqCl h2 a huo, det_genusOf v hv h0 hn hev, hval]
  have hpo : Odd (unitProd (baseList u)) := Int.not_even_iff_odd.mp (fun he =>
    odd_unitProd _ hv (even_iff_two_dvd.mp he))
  have := (zSqCl_eq_iff v h2 1 hpo huo).mpr hunit
  simpa using this

/-- $c_2(G_0) = -(-1,u)_2$ for the base genus of unit class $u$ (`hasseQ` of `baseList u`). -/
theorem hasseQ_baseList {u : ℤ} (hu : u ∈ sqUnits) :
    hasseQ (baseList u) = -((negOneChar u.toNat : ℤˣ) : ℤ) := by
  simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

theorem dyadicA_zero : dyadicA 0 = 0 := by
  norm_num [dyadicA, dyadicA4, single, family, family20, Finset.sum_range_succ]

theorem dyadicBmag_zero : dyadicBmag 0 = 0 := by
  norm_num [dyadicBmag, single, family, family20, Finset.sum_range_succ]

/-- The unit part of $N$ at $2$ has the same $(-1,\cdot)_2$ as the representative $u$ of its class mod $8$. -/
theorem negOneChar_unitPart {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {N : ℕ} (hN : (N : ℚ) ≠ 0)
    {u : ℤ} (hu : u ∈ sqUnits)
    (hS : AdelicSqCl.comp v (ratS (Units.mk0 (N : ℚ) hN)) = zSqCl v (2 ^ N.factorization 2 * u)) :
    Hanke2011Ternary.negOneChar (N / 2 ^ N.factorization 2) = Hanke2011Ternary.negOneChar u.toNat := by
  have hN0 : N ≠ 0 := by exact_mod_cast hN
  set a := N.factorization 2
  set m := N / 2 ^ a with hm
  have hNm : N = 2 ^ a * m := (Nat.ordProj_mul_ordCompl_eq_self N 2).symm
  have hmo : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hN0
  have huo : Odd u := by simp [sqUnits] at hu; rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hmz : Odd (m : ℤ) := by
    rw [Int.odd_iff]; omega
  have hS' : zSqCl v (2 ^ a * (m : ℤ)) = zSqCl v (2 ^ a * u) := by
    rw [← hS, comp_ratS_natCast v hN]
    congr 1
    conv_rhs => rw [hNm]
    push_cast; ring
  have hmod := (zSqCl_eq_iff v h2 a hmz huo).mp hS'
  have hm4 : m % 4 = u.toNat % 4 := by
    simp [sqUnits] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> simp <;> omega
  unfold Hanke2011Ternary.negOneChar; rw [hm4]

/-- The Conway–Sloane 2-mass of the base symbol $1^{2}_{\mathrm{II}}\,2^{1}_{c}$: $m_2 = \frac13\cdot2\cdot2^{-2} = \frac16$
(diagonal product $\frac23\cdot1\cdot\frac12$, cross term $\sqrt2^{\,2}$, type factor $2^{0-2}$). -/
theorem pMassTwo_baseList {u : ℤ} (hu : u ∈ sqUnits) :
    ConwaySloane.Mass.pMassTwo (blockSymbol (baseList u)) 2 = 1 / 6 := by
  simp only [sqUnits, Finset.mem_insert, Finset.mem_singleton] at hu
  have hd : ConwaySloane.Mass.diagProdTwo (blockSymbol (baseList u)) 2 = 1 / 3 := by
    rcases hu with rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) [ConwaySloane.Mass.diagProdTwo, ConwaySloane.Mass.halfFactor,
        blockSymbol, baseList, Finset.prod_range_succ, ConwaySloane.Mass.twoSpecies, ConwaySloane.Mass.IsBound,
        ConwaySloane.Mass.octane, ConwaySloane.Mass.Species.diagFactor, ConwaySloane.Mass.lowerProd]
      simp [DyBlock.dim]
      norm_num
  have hc : ConwaySloane.Mass.crossExp (fun k => (blockSymbol (baseList u) k).dim) 2 = 2 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hII : ConwaySloane.Mass.nII (blockSymbol (baseList u)) 2 = 2 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  have hII' : ConwaySloane.Mass.nII' (blockSymbol (baseList u)) 2 = 0 := by
    rcases hu with rfl | rfl | rfl | rfl <;> decide
  rw [ConwaySloane.Mass.pMassTwo, hd, hc, hII, hII']
  norm_num

/-- **The dyadic generic density for $n = 3$ over $\mathbb Q$** (Hanke 2011, Rem. 4.14, value at $p = 2$; there quoted from
Gan–Hanke–Yu): the base genus $G_0$ of Hessian determinant class $2u$ has $\beta_2(G_0) = 3/16$, from Conway–Sloane's 2-mass. -/
@[kb "hanke2011structure" "Rem. 4.14, p. 20 (the dyadic factor of the generic density, n = 3, F = Q)"]
theorem beta_baseList {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : ℤ} (hu : u ∈ sqUnits) :
    (genusOf v 3 (baseList u)).beta = 3 / 16 := by
  obtain ⟨hv, h0, hn, hev, -, hval, -, hsupp⟩ := baseList_props hu
  rw [beta_genusOf_three v ConwaySloane.Mass.Two.pMassFormulaTwo_holds h2 hv h0 hn hev hsupp, hval,
    pMassTwo_baseList hu]
  norm_num

/-- **Paper 6, Theorem 4.8 with Remark 4.14 for the true local genera over $\mathbb Q$, $n = 3$, from the local tables:**
$$M^*_{1;3}(N) = 2\zeta(2)\bigl(A^*_3(N) + B^*_3(N)\bigr),$$
given the odd-prime local data (`OddTernaryLocalData`), Table 5.3 at $p = 2$ (`Dyadic7.DyadicTernaryLocalMassTable`) and the
dyadic base density $\beta_2(G_0) = 3/16$. -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, p. 20 (F = Q, n = 3, true local genera)"]
theorem totalMassM_ternary_of_tables (HO : OddTernaryLocalData) (H2 : DyadicTernaryLocalMassTable)
    (Hβ2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal → ∀ u ∈ sqUnits,
      (genusOf v 3 (baseList u)).beta = 3 / 16)
    (N : ℕ) (hN : (N : ℚ) ≠ 0) :
    totalMassM 3 (ratS (Units.mk0 (N : ℚ) hN)) 1 ∅ (fun _ => 1) =
      2 * (Real.pi ^ 2 / 6) * ((globalA N + globalB N : ℚ) : ℝ) := by
  classical
  set S := ratS (Units.mk0 (N : ℚ) hN) with hSdef
  have hN0 : N ≠ 0 := by exact_mod_cast hN
  set P := placesOf (2 * N) with hPdef
  have hP : ∀ v, v ∈ P ↔ pv v ∣ 2 * N := fun v => mem_placesOf (by omega) v
  have hord : ∀ v, (ordS v) (AdelicSqCl.comp v S) = (N.factorization (pv v) : ℤ) :=
    fun v => ordZ_comp_ratS v hN
  have hord2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → (ordS v) (AdelicSqCl.comp v S) = (N.factorization 2 : ℤ) := by
    intro v h2; rw [hord, (two_mem_iff_pv v).mp h2]
  have hu2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → ∃ u ∈ sqUnits,
      AdelicSqCl.comp v S = zSqCl v (2 ^ N.factorization 2 * u) :=
    fun v h2 => exists_zSqCl_eq v h2 _ _ (hord2 v h2)
  -- the base tuple
  have hbase : ∀ v, ∃ G : LocGenus v 3, G.Nondeg ∧
      (G.beta)⁻¹ = (if (2 : 𝓞 ℚ) ∈ v.asIdeal then (16 / 3 : ℝ) else (1 - ((pv v : ℝ) ^ 2)⁻¹)⁻¹) ∧
      (v ∉ P → admGen S v = {G} ∧ G.hasse = 1) ∧
      ((2 : 𝓞 ℚ) ∈ v.asIdeal → ∃ u ∈ sqUnits, AdelicSqCl.comp v S = zSqCl v (2 ^ N.factorization 2 * u) ∧
        G = genusOf v 3 (baseList u)) := by
    intro v
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨u, hu, hS⟩ := hu2 v h2
      refine ⟨genusOf v 3 (baseList u), (base_det_two h2 hu 0).1, ?_, fun hv => ?_, fun _ => ⟨u, hu, hS, rfl⟩⟩
      · rw [if_pos h2, Hβ2 v h2 u hu]; norm_num
      · exact absurd ((hP v).mpr (by rw [(two_mem_iff_pv v).mp h2]; exact dvd_mul_right 2 N)) hv
    · by_cases hvP : v ∈ P
      · have h1 : (ordS v) (zSqCl v 1) = 0 := by
          rw [ordZ_zSqCl_eq v one_ne_zero]; simp
        obtain ⟨-, G₀, hs, hb⟩ := HO.unimod v h2 _ h1
        have hmem : G₀ ∈ {G : LocGenus v 3 | G.IsGenStar (zSqCl v 1) 1} := by rw [hs]; rfl
        exact ⟨G₀, hmem.1, by rw [if_neg h2, hb], fun h => absurd hvP h, fun h => absurd h h2⟩
      · have hnd : ¬ pv v ∣ N := fun h => hvP ((hP v).mpr (dvd_mul_of_dvd_right h 2))
        have h0 : (ordS v) (AdelicSqCl.comp v S) = 0 := by
          rw [hord, Nat.factorization_eq_zero_of_not_dvd hnd]; rfl
        obtain ⟨he, G₀, hs, hb⟩ := HO.unimod v h2 _ h0
        have hmem : G₀ ∈ {G : LocGenus v 3 | G.IsGenStar (AdelicSqCl.comp v S) 1} := by rw [hs]; rfl
        refine ⟨G₀, hmem.1, by rw [if_neg h2, hb], fun _ => ⟨?_, hmem.2.2.2⟩, fun h => absurd h h2⟩
        rw [admGen_eq_union, hs, he, Set.union_empty]
  choose b hbnd hbeta hout hb2 using hbase
  have hfin : ∀ v ∈ P, (admGen S v).Finite := by
    intro v _
    rw [admGen_eq_union]
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨u, hu, hS⟩ := hu2 v h2
      rw [hS, genStar_eq_image h2 _ hu, genStar_eq_image h2 _ hu]
      exact (Finset.finite_toSet _).union (Finset.finite_toSet _)
    · exact (HO.fin v h2 _ 1).union (HO.fin v h2 _ (-1))
  have hprod : HasProd (fun v => ((b v).beta)⁻¹) (4 * zetaR 2) :=
    hasProd_baseInv.congr_fun fun v => by rw [hbeta v]
  rw [totalMassM_eq_half S P b (4 * zetaR 2) (fun v hv => (hout v hv).1) (fun v hv => (hout v hv).2) hbnd hfin
    hprod]
  -- the local factors
  set FA : ℕ → ℝ := fun p => if p = 2 then ((dyadicA (N.factorization 2) : ℚ) : ℝ) else
    ((Astar p (negOneChar p) (N.factorization p) 1 : ℚ) : ℝ) with hFA
  set FB : ℕ → ℝ := fun p => if p = 2 then
    ((dyadicB (negOneChar (N / 2 ^ N.factorization 2)) (N.factorization 2) : ℚ) : ℝ) else
    ((Bstar p (negOneChar p) (N.factorization p) 1 : ℚ) : ℝ) with hFB
  have hoddbeta : ∀ v, (2 : 𝓞 ℚ) ∉ v.asIdeal → (b v).beta = 1 - ((pv v : ℝ) ^ 2)⁻¹ := by
    intro v h2
    have := hbeta v
    rw [if_neg h2] at this
    exact inv_injective this
  have hloc : ∀ v ∈ P, (∑ᶠ G ∈ admGen S v, (b v).beta / G.beta) = FA (pv v) ∧
      (∑ᶠ G ∈ admGen S v, ((G.hasse : ℤ) : ℝ) * ((b v).beta / G.beta)) = FB (pv v) := by
    intro v hvP
    rw [finsum_admGen_split S v _ (hfin v hvP), finsum_admGen_split_hasse S v _ (hfin v hvP)]
    by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
    · have hp2 : pv v = 2 := (two_mem_iff_pv v).mp h2
      simp only [hFA, hFB, hp2, if_true]
      obtain ⟨u, hu, hS, hbv⟩ := hb2 v h2
      by_cases ha : N.factorization 2 = 0
      · have hemp := admGen_two_empty v h2 S (by rw [hord2 v h2, ha]; rfl)
        rw [admGen_eq_union, Set.union_empty_iff] at hemp
        rw [hemp.1, hemp.2, ha, dyadicA_zero, dyadicB, dyadicBmag_zero]
        simp
      · have h1 : 1 ≤ (ordS v) (AdelicSqCl.comp v S) := by rw [hord2 v h2]; omega
        have hd := base_det_two h2 hu (N.factorization 2)
        rw [← hS, ← hbv] at hd
        refine ⟨?_, ?_⟩
        · rw [H2.A_eq v h2 _ (b v) h1 hd.1 hd.2.1 hd.2.2, hord2 v h2, Int.toNat_natCast]
        · rw [H2.B_eq v h2 _ (b v) h1 hd.1 hd.2.1 hd.2.2, hord2 v h2, Int.toNat_natCast, hbv]
          obtain ⟨hvl, h0, hn, hev, -⟩ := baseList_props hu
          rw [hasse_genusOf v h2 hvl h0 hn hev, hasseQ_baseList hu, dyadicB,
            negOneChar_unitPart h2 hN hu hS]
          push_cast
          ring
    · have hp2 : pv v ≠ 2 := fun h => h2 ((two_mem_iff_pv v).mpr h)
      simp only [hFA, hFB, hp2, if_false]
      have hnn : 0 ≤ (ordS v) (AdelicSqCl.comp v S) := by rw [hord]; positivity
      have hA := HO.A_eq v h2 _ hnn
      have hB := HO.B_eq v h2 _ hnn
      rw [hord, Int.toNat_natCast] at hA hB
      rw [hoddbeta v h2]
      exact ⟨hA, hB⟩
  rw [Finset.prod_congr rfl fun v hv => (hloc v hv).1, Finset.prod_congr rfl fun v hv => (hloc v hv).2,
    prod_placesOf, prod_placesOf]
  have hpf : (2 * N).primeFactors = insert 2 (N.primeFactors.erase 2) := by
    rw [Nat.primeFactors_mul two_ne_zero hN0, Nat.Prime.primeFactors Nat.prime_two]
    ext p; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.mem_erase]
    tauto
  have h2n : (2 : ℕ) ∉ N.primeFactors.erase 2 := by simp
  rw [hpf, Finset.prod_insert h2n, Finset.prod_insert h2n]
  have hA : FA 2 * ∏ p ∈ N.primeFactors.erase 2, FA p = ((globalA N : ℚ) : ℝ) := by
    simp only [globalA, ArithmeticFunction.coe_mk, hN0, if_false, Rat.cast_mul, Rat.cast_prod, hFA, if_true]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [if_neg (Finset.ne_of_mem_erase hp)]
  have hB : FB 2 * ∏ p ∈ N.primeFactors.erase 2, FB p = ((globalB N : ℚ) : ℝ) := by
    simp only [globalB, ArithmeticFunction.coe_mk, hN0, if_false, Rat.cast_mul, Rat.cast_prod, hFB, if_true]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [if_neg (Finset.ne_of_mem_erase hp)]
  rw [hA, hB, zetaR_two]
  push_cast
  ring

/-- **Paper 7's local input `TernaryLocalMassFormula` from the local tables** (the dyadic base density is proved,
`beta_baseList`). -/
@[kb "hanke2011structure" "Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–7 (F = Q, n = 3)"]
theorem ternaryLocalMassFormula_of_tables (HO : OddTernaryLocalData) (H2 : DyadicTernaryLocalMassTable) :
    TernaryLocalMassFormula :=
  ⟨fun N hN => totalMassM_ternary_of_tables HO H2 (fun _ h2 _ hu => beta_baseList h2 hu) N hN⟩

end Main

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.totalMassM_eq_half
#print axioms QuadFormsKB.Hanke2011Structure.beta_baseList
#print axioms QuadFormsKB.Hanke2011Structure.totalMassM_ternary_of_tables
