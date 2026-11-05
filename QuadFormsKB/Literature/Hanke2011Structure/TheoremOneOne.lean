/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.RankAssembly
import QuadFormsKB.Literature.Hanke2011Structure.FormalSeries
import QuadFormsKB.Literature.Hanke2011Structure.TernaryAssembly
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddGenus
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoFinite

/-!
# Paper 6, Theorem 1.1: $D_{T^*;n} = \kappa_n[D_{A^*;n} + D_{B^*;n}]$ for $n$ odd over $\mathbb Q$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 1.1, p. 2 (the summary of Thm. 4.8, p. 17, Cor. 4.13 and 4.15, p. 20).

**Theorem 1.1** (positive definite forms over $\mathbb Q$, $n$ odd): the formal Dirichlet series
$D_{T^*;n}(s) = \sum_{N\ge1}T^*_n(N)N^{-s}$ of the primitive total non-archimedean masses is
$\kappa_n[D_{A^*;n}(s) + D_{B^*;n}(s)]$ for two Eulerian series and an explicit constant $\kappa_n$. Here, for $n = 2r+1$:

* `theorem_1_1`: there is $\kappa > 0$ such that for every $N \ge 1$
  $$T^*_{(n,0);n}(N) = \kappa\,\bigl[A(N) + B(N)\bigr],\qquad A(N) = \prod_pA_p([N]_p),\quad B(N) = \prod_pB_p([N]_p),$$
  where $T^*$ is `totalMassT` (Def. 3.4: the sum over the genera of primitive positive definite $\mathbb Z$-valued forms of
  Hessian determinant $N$ of $\prod_p\beta_p^{-1}$), $[N]_p \in \mathrm{SqCl}(\mathbb Q_p^\times,\mathbb Z_p^\times)$ the class of $N$, and
  $A(N)$, $B(N)$ are the coefficients `eulerCoeff` of the **Euler products** (§4, p. 14) with local factors
  $A_p = $ `Aloc`, $B_p = $ `Bloc`: the normalized local mass sums of Definition 4.6 for the true local genera,
  $$A_p(S_p) = \sum_{G}\frac{w_p}{\beta_p(G)},\qquad B_p(S_p) = \sum_G c_p(G)\frac{w_p}{\beta_p(G)}$$
  over the nondegenerate primitive $\mathbb Z_p$-genera $G$ with $\det_H(G) = S_p$; $w_p = \beta_{n,p}(\widetilde S_p) =
  \prod_{i=1}^r(1-p^{-2i})$ for $p$ odd (the generic density, Rem. 4.14 / Lemma 3.6) and $w_2 = 1$ (for $n$ odd the generic
  density at $2$ is a constant, Rem. 4.14, absorbed into $\kappa$). The local factors are $1$ on the unit classes at every
  odd $p$ (`aloc_good`, `bloc_good`: Lemma 4.7), so both are Euler families (`isEulerFamily_aloc`, `isEulerFamily_bloc`), and
  $$\kappa = \tfrac12\prod_{i=1}^r\zeta(2i)\cdot\prod_{i=1}^r(1-2^{-2i}).$$
* The theorem is **unconditional**. The finiteness of the local sums is proved at every prime: at odd $p$ here
  (`admLoc_finite_odd`, from Conway–Sloane's classification), at $p = 2$ in `RationalityTwoFinite.lean`
  (`RatTwo.admGen_finite_two`, from Conway–Sloane's 2-adic Jordan decompositions), giving `dyadicGeneraFinite`.

*Clarification* (proposed by the formalization): the "Eulerian" claim is formalized in the language of
§4 (multiplicative formal squareclass series: the factor at $p$ depends on the class $[N]_p$, i.e. on $\operatorname{ord}_p N$ and on
the unit part of $N$ at $p$). Writing these as Euler products of Dirichlet series in $N$ needs the local factors to depend on
$\operatorname{ord}_pN$ only; by Theorem 5.7 this holds for $A^*$, and for $B^*$ at odd $p$, but for $n \equiv 3 \pmod 4$ the factor
$B_2$ changes by $(u,u)_2$ under unit scaling (see the Corrections entry for Cor. 4.13), which is absorbed by the character
$\chi_{-4}$ at the odd primes.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Finset

namespace QuadFormsKB.Hanke2011Structure

open Classical

noncomputable section

/-! ### Local admissible sets; the good primes (any number field) -/

section Good

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

variable (n) in
/-- The admissible local genera of rank $n$ at $\mathfrak p$ for a local squareclass $s$: nondegenerate, primitive,
$\det_H = s$ (the set $\mathrm{Gen}^*_{\mathfrak p}(s,+;n)\cup\mathrm{Gen}^*_{\mathfrak p}(s,-;n)$). -/
def admLoc (v : HeightOneSpectrum (𝓞 F)) (s : LocalSqCl v) : Set (LocGenus v n) :=
  {G | G.Nondeg ∧ G.Prim ∧ G.det = s}

theorem admGenRank_eq_admLoc (S : AdelicSqCl F) (v : HeightOneSpectrum (𝓞 F)) :
    admGenRank n S v = admLoc n v (AdelicSqCl.comp v S) := rfl

theorem not_dvd_two_of_not_mem (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
  have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
  rwa [pow_one, map_ofNat] at this

/-- **The good primes** (Lemma 4.7 and Theorem 2.6 for $\mathfrak p \nmid 2$, true local genera): for a unit class $s$ there is a
form $Q$ with unit Hessian determinant whose genus is the only admissible genus of determinant $s$, and its Hasse invariant
is $1$. -/
@[kb "hanke2011structure" "Lemma 4.7, p. 16 (true local genera, every rank, every number field)"]
theorem admLoc_good (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {s : LocalSqCl v}
    (hs : s ∈ localUnitSqCl F v) :
    ∃ Q : QuadForm (v.adicCompletionIntegers F) n, IsUnit Q.hessian.det ∧
      admLoc n v s = {LocGenus.mk Q} ∧ (LocGenus.mk Q).hasse = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨x, ⟨u, rfl⟩, hxs⟩ := hs
  have hπ := LocalDensity.NF.irreducible_π v
  have h2' := not_dvd_two_of_not_mem v h2
  obtain ⟨Q, hQdet, ⟨a, haU, hiso, hhasse⟩, huniq⟩ :=
    lemma_4_7_exists_with_det hπ h2' (v.adicCompletion F) (k := k) u.isUnit
  have hQunit : IsUnit Q.hessian.det := hQdet ▸ u.isUnit
  have hQne : algebraMap _ (v.adicCompletion F) Q.hessian.det ≠ 0 :=
    (algebraMap_ne_zero_iff (v := v)).mpr hQunit.ne_zero
  have hdetQ : (LocGenus.mk Q).det = s := by
    rw [LocGenus.det_mk, detSqForm_of_ne hQne, ← hxs]
    congr 1
    apply Units.ext
    simp [hQdet]
  refine ⟨Q, hQunit, ?_, ?_⟩
  · ext G
    simp only [admLoc, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN, hP, hd⟩
      obtain ⟨T, rfl⟩ := Quotient.exists_rep G
      change LocGenus.mk T = LocGenus.mk Q
      have hTne : algebraMap _ (v.adicCompletion F) T.hessian.det ≠ 0 :=
        (algebraMap_ne_zero_iff (v := v)).mpr ((LocGenus.nondeg_mk T).mp hN)
      change (LocGenus.mk T).det = s at hd
      rw [LocGenus.det_mk, detSqForm_of_ne hTne, ← hdetQ, LocGenus.det_mk, detSqForm_of_ne hQne] at hd
      obtain ⟨w, ⟨u0, hu0⟩, hwe⟩ := SqCl.exists_eq_mul_sq hd.symm
      have hdetT : T.hessian.det = (u0 : v.adicCompletionIntegers F) ^ 2 * Q.hessian.det := by
        apply IsFractionRing.injective (v.adicCompletionIntegers F) (v.adicCompletion F)
        have := congrArg Units.val hwe
        rw [Units.val_mul, Units.val_pow_eq_pow_val, ← hu0] at this
        change algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) T.hessian.det =
          algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) Q.hessian.det *
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (u0 : v.adicCompletionIntegers F)) ^ 2
          at this
        rw [map_mul, map_pow, this, mul_comm]
      rw [hQdet] at hdetT
      exact (LocGenus.mk_eq_mk.mpr (huniq T u0 u0.isUnit hdetT)).symm
    · rintro rfl
      exact ⟨(LocGenus.nondeg_mk Q).mpr hQunit.ne_zero,
        (LocGenus.prim_mk Q).mpr (isPrimitiveForm_of_isUnit_det (by omega) Q hQunit), hdetQ⟩
  · rw [LocGenus.hasse_mk, hasseForm_of_isometricGL hiso]
    unfold hasseForm
    rw [Odd7.map_diag_eq, hasseC_diag v _ (fun i => (algebraMap_ne_zero_iff (v := v)).mpr (haU i).ne_zero)]
    exact hhasse

end Good

/-! ### Over $\mathbb Q$: densities at the good primes, finiteness at the odd primes -/

section Rat

local notation "pv" => ConwaySloane.Mass.pv

/-- The generic density $\prod_{i=1}^r(1 - q^{-2i})$ of a unimodular form in $2r+1$ variables at an odd prime (Lemma 3.6). -/
def gOdd (r : ℕ) (q : ℝ) : ℝ := ∏ i ∈ range r, (1 - (q ^ (2 * (i + 1)))⁻¹)

theorem gOdd_pos (r : ℕ) {q : ℝ} (hq : 1 < q) : 0 < gOdd r q := by
  refine prod_pos fun i _ => ?_
  have : (q ^ (2 * (i + 1)))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  linarith

theorem pv_ne_two_of_not_mem {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) : pv v ≠ 2 :=
  fun h => h2 ((two_mem_iff_pv v).mpr h)

/-- **The density of the unimodular genus at an odd prime** (Lemma 3.6, $n = 2r+1$): $\beta = \prod_{i=1}^r(1 - p^{-2i})$. -/
theorem beta_good_odd {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (r : ℕ)
    (Q : QuadForm (v.adicCompletionIntegers ℚ) (2 * r + 1)) (hQ : IsUnit Q.hessian.det) :
    (LocGenus.mk Q).beta = gOdd r (pv v) := by
  have hne : Q.hessian.det ≠ 0 := hQ.ne_zero
  have hπ := LocalDensity.NF.irreducible_π v
  have h2' := not_dvd_two_of_not_mem v h2
  have hd := lemma_3_6_density_odd hπ h2' r Q (LocalDensity.DVR.dvr_not_dvd_of_isUnit hπ hQ)
  rw [LocGenus.beta_mk]
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v Q hne, ConwaySloane.Mass.norm_two_completion v (pv_ne_two_of_not_mem h2),
    one_pow, one_mul]
  unfold LocalDensity.DVR.siegelDensity
  simp only [ite_true]
  rw [gOdd, ← ConwaySloane.Mass.q_eq v, ← hd]
  ring

/-- **Finiteness at the odd primes**: for $p$ odd and $N \ge 1$ there are finitely many admissible genera of
$\det_H = [N]_p$ (Conway–Sloane's classification: they are the genera of finitely many symbols). -/
theorem admLoc_finite_odd {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) (n N : ℕ) (hN : N ≠ 0) :
    (admLoc n v (Dyadic7.zSqCl v (N : ℤ))).Finite := by
  have hp : (pv v).Prime := pv_prime v
  haveI : Fact (pv v).Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := ConwaySloane.Mass.exists_nonresidue (p := pv v) (pv_ne_two_of_not_mem h2)
  set ν := N.factorization (pv v)
  set w : ℕ := N / pv v ^ ν
  have hNw : ((N : ℕ) : ℤ) = (((pv v : ℕ) : ℤ)) ^ ν * (w : ℤ) := by
    have := Nat.ordProj_mul_ordCompl_eq_self N (pv v)
    exact_mod_cast this.symm
  have hw : ¬ ((pv v : ℕ) : ℤ) ∣ (w : ℤ) := by
    rw [Int.natCast_dvd_natCast]
    exact Nat.not_dvd_ordCompl hp hN
  have hU : admLoc n v (Dyadic7.zSqCl v (N : ℤ)) =
      {G : LocGenus v n | G.IsGenStar (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w)) 1} ∪
        {G : LocGenus v n | G.IsGenStar (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w)) (-1)} := by
    rw [hNw]
    ext G
    simp only [admLoc, LocGenus.IsGenStar, Set.mem_setOf_eq, Set.mem_union]
    rcases LocGenus.hasse_pm_rank v G with h | h <;> simp [h]
  rw [hU]
  refine Set.Finite.union ?_ ?_ <;>
  · rw [RatOdd.genStar_eq_image h2 hc hw ν]
    exact ((RatOdd.symSet_finite n ν).subset fun σ h => h.1.1).image _

end Rat

/-! ### The Euler families and Theorem 1.1 -/

section Theorem

local notation "pv" => ConwaySloane.Mass.pv

variable (r : ℕ)

/-- The normalizing weight $w_p$: $\prod_{i=1}^r(1 - p^{-2i})$ for $p$ odd, $1$ at $p = 2$. -/
def wRef (v : HeightOneSpectrum (𝓞 ℚ)) : ℝ := if (2 : 𝓞 ℚ) ∈ v.asIdeal then 1 else gOdd r (pv v)

/-- **The local factor $A_p$** (Definition 4.6 for the true local genera, $n = 2r+1$): $\sum_G w_p/\beta_p(G)$ over the
admissible genera of determinant $s$. -/
@[kb "hanke2011structure" "Def. 4.6, p. 16 (A*_p for the true local genera, F = Q, n odd)"]
def Aloc (v : HeightOneSpectrum (𝓞 ℚ)) (s : LocalSqCl v) : ℝ :=
  ∑ᶠ G ∈ admLoc (2 * r + 1) v s, wRef r v / G.beta

/-- **The local factor $B_p$** (Definition 4.6): $\sum_G c_p(G)\,w_p/\beta_p(G)$. -/
@[kb "hanke2011structure" "Def. 4.6, p. 16 (B*_p for the true local genera, F = Q, n odd)"]
def Bloc (v : HeightOneSpectrum (𝓞 ℚ)) (s : LocalSqCl v) : ℝ :=
  ∑ᶠ G ∈ admLoc (2 * r + 1) v s, ((G.hasse : ℤ) : ℝ) * (wRef r v / G.beta)

theorem wRef_pos (v : HeightOneSpectrum (𝓞 ℚ)) : 0 < wRef r v := by
  unfold wRef
  split_ifs with h
  · exact one_pos
  · exact gOdd_pos r (by exact_mod_cast (pv_prime v).one_lt)

/-- At an odd prime and a unit class: the unique admissible genus has density $w_p$ and Hasse invariant $1$. -/
theorem good_genus {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) {s : LocalSqCl v}
    (hs : s ∈ localUnitSqCl ℚ v) :
    ∃ b : LocGenus v (2 * r + 1), admLoc (2 * r + 1) v s = {b} ∧ b.hasse = 1 ∧ b.beta = wRef r v := by
  obtain ⟨Q, hQ, hadm, hh⟩ := admLoc_good (n := 2 * r + 1) (by omega) v h2 hs
  refine ⟨LocGenus.mk Q, hadm, hh, ?_⟩
  rw [beta_good_odd h2 r Q hQ, wRef, if_neg h2]

/-- **Lemma 4.7 for the local factors**: $A_p(s) = 1$ at an odd prime and a unit class. -/
theorem aloc_good {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) {s : LocalSqCl v}
    (hs : s ∈ localUnitSqCl ℚ v) : Aloc r v s = 1 := by
  obtain ⟨b, hadm, -, hb⟩ := good_genus r h2 hs
  rw [Aloc, hadm, finsum_mem_singleton, hb, div_self (wRef_pos r v).ne']

/-- **Lemma 4.7 for the local factors**: $B_p(s) = 1$ at an odd prime and a unit class. -/
theorem bloc_good {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) {s : LocalSqCl v}
    (hs : s ∈ localUnitSqCl ℚ v) : Bloc r v s = 1 := by
  obtain ⟨b, hadm, hh, hb⟩ := good_genus r h2 hs
  rw [Bloc, hadm, finsum_mem_singleton, hb, div_self (wRef_pos r v).ne', hh]
  simp

theorem eventually_odd : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, (2 : 𝓞 ℚ) ∉ v.asIdeal :=
  Lattices.eventually_not_mem (two_ne_zero : (2 : 𝓞 ℚ) ≠ 0)

/-- $A_p$ is an Euler family (§4, p. 14). -/
theorem isEulerFamily_aloc : IsEulerFamily ℚ (Aloc r) := by
  filter_upwards [eventually_odd] with v hv s hs
  exact aloc_good r hv hs

/-- $B_p$ is an Euler family (§4, p. 14). -/
theorem isEulerFamily_bloc : IsEulerFamily ℚ (Bloc r) := by
  filter_upwards [eventually_odd] with v hv s hs
  exact bloc_good r hv hs

/-- **Finiteness of the dyadic admissible genera** (for $\mathbb Z_2$, rank $n$): for every $s \in \mathrm{SqCl}(\mathbb Q_2^\times,
\mathbb Z_2^\times)$ there are finitely many nondegenerate primitive $\mathbb Z_2$-genera of Hessian determinant $s$. The only
hypothesis of `theorem_1_1_of_dyadicGeneraFinite`; proved for every $n$ (`dyadicGeneraFinite`). -/
def DyadicGeneraFinite (n : ℕ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal → ∀ s : LocalSqCl v, (admLoc n v s).Finite

/-- The constant $C = \prod_pw_p^{-1} = \prod_{i=1}^r\zeta(2i)\cdot\prod_{i=1}^r(1 - 2^{-2i})$. -/
def constC1 : ℝ := (∏ i ∈ range r, NFEuler.zetaR (2 * ((i : ℝ) + 1))) * gOdd r 2

theorem gOdd_inv_eq (r : ℕ) (p : ℕ) (hp : 0 < p) :
    (gOdd r p)⁻¹ = ∏ i ∈ range r, (1 - ((p : ℕ) : ℝ) ^ (-(2 * ((i : ℝ) + 1))))⁻¹ := by
  rw [gOdd, ← prod_inv_distrib]
  refine prod_congr rfl fun i _ => ?_
  congr 2
  rw [Real.rpow_neg (by positivity), show (2 * ((i : ℝ) + 1)) = ((2 * (i + 1) : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]

/-- **The Euler product of the weights**: $\prod_pw_p^{-1} = C$. -/
theorem hasProd_wRef : HasProd (fun v => (wRef r v)⁻¹) (constC1 r) := by
  open Rat.HeightOneSpectrum in
  have h0 : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      ∏ i ∈ range r, (1 - ((pv v : ℕ) : ℝ) ^ (-(2 * ((i : ℝ) + 1))))⁻¹)
      (∏ i ∈ range r, NFEuler.zetaR (2 * ((i : ℝ) + 1))) := by
    refine hasProd_prod fun i _ => ?_
    exact (primesEquiv.hasProd_iff (f := fun p : Nat.Primes =>
      (1 - ((p : ℕ) : ℝ) ^ (-(2 * ((i : ℝ) + 1))))⁻¹)).mpr (NFEuler.hasProd_zetaR (by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith))
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
  have hc : HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if (2 : 𝓞 ℚ) ∈ v.asIdeal then gOdd r 2 else 1) (gOdd r 2) := by
    have := hasProd_single (f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
      if (2 : 𝓞 ℚ) ∈ v.asIdeal then gOdd r 2 else 1) v₂ (fun w hw => by
        simp only [hv₂ w, hw, if_false])
    simpa [hv₂ v₂] using this
  have h := h0.mul hc
  refine h.congr_fun fun v => ?_
  have hp := (pv_prime v).pos
  rw [← gOdd_inv_eq r (pv v) hp]
  unfold wRef
  by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
  · rw [if_pos h2, if_pos h2, (two_mem_iff_pv v).mp h2, inv_one]
    push_cast
    rw [inv_mul_cancel₀ (gOdd_pos r (by norm_num : (1 : ℝ) < 2)).ne']
  · rw [if_neg h2, if_neg h2, mul_one]

theorem constC1_pos : 0 < constC1 r := by
  have h := hasProd_wRef r
  have hpos : ∀ v, 0 < (wRef r v)⁻¹ := fun v => inv_pos.mpr (wRef_pos r v)
  unfold constC1
  refine mul_pos (prod_pos fun i _ => ?_) (gOdd_pos r (by norm_num))
  have hs : (1 : ℝ) < 2 * ((i : ℝ) + 1) := by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  exact lt_of_lt_of_le one_pos (NFEuler.one_le_zetaR hs)

/-- **Lemma 3.7 over $\mathbb Q$, positive definite, every rank** ($T^* = M^*$ for $N \ge 1$). -/
theorem totalMassT_eq_totalMassM_rat (n : ℕ) (hn : 1 ≤ n) {N : ℕ} (hN0 : 0 < N) (hN : (N : ℚ) ≠ 0) :
    totalMassT (ratS (Units.mk0 (N : ℚ) hN)) (sigPos n) ∅ (fun _ => 1) =
      totalMassM n (ratS (Units.mk0 (N : ℚ) hN)) 1 ∅ (fun _ => 1) := by
  rw [← epsInf_sigPos n]
  refine (lemma_3_7 hn _ _ _ _ (Units.mk0 (N : ℚ) hN) (fun v => ?_) (fun w => ?_)).2
  · simp only [ratS, AdelicSqCl.comp_mk, ideleComp_unitEmbedding, rhoLocal_mk]
  · let _ : Algebra ℚ w.1.Completion := InfinitePlace.Completion.instAlgebra w.1 ℚ
    obtain ⟨q, -, hq⟩ := exists_sq_realPlace w.2 (show (0 : ℚ) < (-1) ^ (sigPos n w).1.2 * N by
      simp [sigPos]; exact_mod_cast hN0)
    refine ⟨q, ?_⟩
    rw [eq_ratCast (algebraMap ℚ w.1.Completion), Units.val_mk0, ← hq, sq]

/-- **Theorem 1.1** (Hanke 2011, p. 2; the summary of Thm. 4.8, Cor. 4.13 and 4.15 for positive definite forms over
$\mathbb Q$, $n = 2r+1$ odd): there is a constant $\kappa > 0$ such that for every $N \ge 1$
$$T^*_{(n,0);n}(N) = \kappa\,\bigl[A(N) + B(N)\bigr],$$
$A(N)$, $B(N)$ the coefficients at $[N]$ of the Euler products with local factors $A_p$ = `Aloc`, $B_p$ = `Bloc` (the
normalized local mass sums of the true local genera, Def. 4.6), which are Euler families (`isEulerFamily_aloc`,
`isEulerFamily_bloc`); $\kappa = \frac12\prod_{i=1}^r\zeta(2i)\prod_{i=1}^r(1-2^{-2i})$. This version takes the
finiteness of the $\mathbb Z_2$-genera of given determinant (`DyadicGeneraFinite`) as a hypothesis; it is proved in
`dyadicGeneraFinite`, so `theorem_1_1` is unconditional. -/
theorem theorem_1_1_of_dyadicGeneraFinite (H2 : DyadicGeneraFinite (2 * r + 1)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (hN0 : 0 < N),
      totalMassT (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne'))) (sigPos (2 * r + 1)) ∅ (fun _ => 1) =
        κ * (eulerCoeff (Aloc r) (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne'))) +
          eulerCoeff (Bloc r) (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne')))) := by
  refine ⟨constC1 r / 2, by have := constC1_pos r; positivity, fun N hN0 => ?_⟩
  have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
  set S := ratS (Units.mk0 (N : ℚ) hN)
  rw [totalMassT_eq_totalMassM_rat (2 * r + 1) (by omega) hN0 hN]
  set P := placesOf (2 * N)
  have h2N : 2 * N ≠ 0 := by omega
  -- the primes outside `P` are odd and `N` is a unit there
  have hgood : ∀ v ∉ P, (2 : 𝓞 ℚ) ∉ v.asIdeal ∧ AdelicSqCl.comp v S ∈ localUnitSqCl ℚ v := by
    intro v hv
    rw [mem_placesOf h2N] at hv
    refine ⟨fun h2 => hv ?_, ?_⟩
    · rw [(two_mem_iff_pv v).mp h2]; exact dvd_mul_right 2 N
    · refine mem_localUnitSqCl_of_ordZ v ?_
      rw [ordZ_comp_ratS v hN]
      have : N.factorization (pv v) = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun h => hv (dvd_mul_of_dvd_right h 2)
      rw [this]; rfl
  have hspec : ∀ v ∉ P, ∃ b : LocGenus v (2 * r + 1), admLoc (2 * r + 1) v (AdelicSqCl.comp v S) = {b} ∧
      b.hasse = 1 ∧ b.beta = wRef r v := fun v hv => good_genus r (hgood v hv).1 (hgood v hv).2
  let b : LocTuple ℚ (2 * r + 1) := fun v =>
    if hv : v ∉ P then Classical.choose (hspec v hv) else LocGenus.mk ⟨0, fun _ _ _ => rfl⟩
  have hb : ∀ v (hv : v ∉ P), b v = Classical.choose (hspec v hv) := fun v hv => by
    simp only [b, dif_pos hv]
  have hM := totalMassM_eq_half_rank S P b (wRef r) (constC1 r)
    (fun v hv => by rw [hb v hv]; exact (Classical.choose_spec (hspec v hv)).1)
    (fun v hv => by rw [hb v hv]; exact (Classical.choose_spec (hspec v hv)).2.1)
    (fun v hv => by rw [hb v hv]; exact (Classical.choose_spec (hspec v hv)).2.2.symm)
    (fun v => (wRef_pos r v).ne')
    (fun v hvP => by
      rw [admGenRank_eq_admLoc]
      by_cases h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal
      · exact H2 v h2 _
      · rw [comp_ratS_natCast v hN]
        exact admLoc_finite_odd h2 (2 * r + 1) N hN0.ne')
    (hasProd_wRef r)
  rw [hM]
  have hA : eulerCoeff (Aloc r) S = ∏ v ∈ P, ∑ᶠ G ∈ admGenRank (2 * r + 1) S v, wRef r v / G.beta :=
    eulerCoeff_eq_prod S P fun v hv => aloc_good r (hgood v hv).1 (hgood v hv).2
  have hB : eulerCoeff (Bloc r) S =
      ∏ v ∈ P, ∑ᶠ G ∈ admGenRank (2 * r + 1) S v, ((G.hasse : ℤ) : ℝ) * (wRef r v / G.beta) :=
    eulerCoeff_eq_prod S P fun v hv => bloc_good r (hgood v hv).1 (hgood v hv).2
  rw [hA, hB]
  ring

/-- **Finiteness of the dyadic admissible genera, every rank** (`DyadicGeneraFinite n` holds): from Conway–Sloane's 2-adic
Jordan decompositions (`RatTwo.admGen_finite_two`). -/
theorem dyadicGeneraFinite (n : ℕ) : DyadicGeneraFinite n := fun _ h2 s => RatTwo.admGen_finite_two h2 n s

/-- **Theorem 1.1** (Hanke 2011, p. 2; the summary of Thm. 4.8, Cor. 4.13 and 4.15 for positive definite forms over
$\mathbb Q$, $n = 2r+1$ odd), **unconditional**: there is a constant $\kappa > 0$ such that for every $N \ge 1$
$$T^*_{(n,0);n}(N) = \kappa\,\bigl[A(N) + B(N)\bigr],$$
where $T^*_{(n,0);n}(N)$ is `totalMassT` (Def. 3.4) for the class $[N]$, and $A(N)$, $B(N)$ are the coefficients at $[N]$ of
the Euler products with local factors $A_p$ = `Aloc`, $B_p$ = `Bloc` (the normalized local mass sums of the true local
genera, Def. 4.6), which are Euler families (`isEulerFamily_aloc`, `isEulerFamily_bloc`); one may take
$\kappa = \frac12\prod_{i=1}^r\zeta(2i)\prod_{i=1}^r(1-2^{-2i})$. -/
@[kb "hanke2011structure" "Thm. 1.1, p. 2 (n odd, F = Q, positive definite; via Thm. 4.8, Cor. 4.13, 4.15)"]
theorem theorem_1_1 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ) (hN0 : 0 < N),
      totalMassT (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne'))) (sigPos (2 * r + 1)) ∅ (fun _ => 1) =
        κ * (eulerCoeff (Aloc r) (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne'))) +
          eulerCoeff (Bloc r) (ratS (Units.mk0 (N : ℚ) (by exact_mod_cast hN0.ne')))) :=
  theorem_1_1_of_dyadicGeneraFinite r (dyadicGeneraFinite _)

end Theorem

end

end QuadFormsKB.Hanke2011Structure
