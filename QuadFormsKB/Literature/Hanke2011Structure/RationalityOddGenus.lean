/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Tamagawa.Odd7Beta
import QuadFormsKB.Tamagawa.Odd7Classify
import QuadFormsKB.Tamagawa.Odd7Hasse
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddMass
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddStats

/-!
# Paper 6, Theorem 5.4 at odd primes, every rank $n$, for the true local genera over $\mathbb Q$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23.

For an odd prime $p = p_v$ and every rank $n$ this file proves that the fixed-unit local series
$$\sum_\nu A^*_{p;n}([p^\nu w])\,X^\nu,\qquad \sum_\nu B^*_{p;n}([p^\nu w])\,X^\nu\qquad(X = p^{-s},\ p \nmid w)$$
of the **true** local genera (`trueAstar`, `trueBstar`: sums over the nondegenerate primitive $\mathbb Z_p$-genera $G$
of $\det_H G = [p^\nu w]$ of $\beta(G_0)/\beta(G)$, without / with the Hasse invariant as a sign) are rational
functions of $X$ (`theorem_5_4_odd_A_rank`, `theorem_5_4_odd_B_rank`; `RatOdd.RatSeries`: $S\,Q = P$, $Q(0) \ne 0$).
Unconditional.

*Proof.* Every nondegenerate genus is the genus `genZ z x` of $\sum_ip^{z_i}\mathrm{rep}(x_i)X_i^2$ ($x_i = \pm1$ the
Legendre symbols; `exists_genZ`, Conway–Sloane's Theorem 9), and `genZ z x = genZ z' x'` iff the Conway–Sloane symbols
`symC z x`, `symC z' x'` agree (`genZ_eq_iff`).  Its invariants are read off the symbol: $\det_H$ has valuation
$\sum z_i$ and unit class $\left(\frac2p\right)^n\prod x_i$ (`det_genZ_iff`), it is primitive iff $n_0 \ge 1$
(`prim_genZ_iff`), its Hasse invariant is $\varepsilon'^{\binom{d_o}{2}}(EO)^{d_o}O$ in terms of the state
$(E, O, d_e, d_o)$ of the symbol (`hasse_genZ`, `hasseZ_closed`), and $\beta(G)^{-1} = 2\,\mathrm{wt}(\sigma)$ with
$\mathrm{wt}$ the weight of `RationalityOddMass` (`beta_genZ`: Conway–Sloane's formula (3) at odd $p$,
`pMassFormulaOdd`).  Hence the mass sum over $\mathrm{Gen}^*_p([p^\nu w],\varepsilon;n)$ is a constant times the
$X^\nu$ coefficient of a generating series of symbols (`sum_genStar_eq`, `genStar_eq_image`), and these are rational
for every rank by `RatOdd.rat_Pn` (`RationalityOddSeries`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Hanke2011Structure.RatOdd

open QuadFormsKB.Odd7 QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section Gen

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- The diagonal entries $p^{z_i}\,\mathrm{rep}(x_i)$ of the integral representative form. -/
def vecZ (p : ℕ) (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : Fin n → ℤ :=
  fun i => (p : ℤ) ^ z i * rep c (x i)

/-- The integral diagonal form $\sum_ip^{z_i}\mathrm{rep}(x_i)X_i^2$. -/
def formZ (p : ℕ) (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : QuadForm ℤ n :=
  QuadForm.diag (vecZ p c z x)

/-- Its Gram matrix. -/
def matZ (p : ℕ) (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal (vecZ p c z x)

/-- The local genus of the diagonal form with exponents `z` and unit characters `x`. -/
def genZ (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : LocGenus v n :=
  LocGenus.mk ((formZ (pv v) c z x).map (algebraMap ℤ (v.adicCompletionIntegers ℚ)))

theorem prod_vecZ (p : ℕ) (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    ∏ i, vecZ p c z x i = (p : ℤ) ^ (∑ i, z i) * ∏ i, rep c (x i) := by
  unfold vecZ
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- The unit part $2^n\prod_i\mathrm{rep}(x_i)$ of the Hessian determinant. -/
def detUnitZ (c : ℤ) {n : ℕ} (x : Fin n → ℤˣ) : ℤ := 2 ^ n * ∏ i, rep c (x i)

theorem not_dvd_detUnitZ (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (x : Fin n → ℤˣ) :
    ¬ (pv v : ℤ) ∣ detUnitZ c x := by
  have hpp := Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)
  unfold detUnitZ
  intro h
  rcases hpp.dvd_or_dvd h with h | h
  · have := hpp.dvd_of_dvd_pow h
    have h2 : pv v ∣ 2 := by exact_mod_cast this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : (pv v).Prime) Nat.prime_two).1 h2)
  · rcases (Prime.dvd_finset_prod_iff hpp _).1 h with ⟨i, _, hi⟩
    exact not_dvd_rep hc _ hi


theorem hessian_genZ (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).hessian.det =
      ((((pv v : ℕ) : ℤ) ^ (∑ i, z i) * detUnitZ c x : ℤ) : 𝔬) := by
  unfold formZ
  rw [map_diag_eq, hessian_diag_gen, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← map_prod, prod_vecZ]
  simp only [eq_intCast, detUnitZ]
  push_cast
  ring

theorem det_genZ {c : ℤ} (hp2 : pv v ≠ 2) (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) :
    (genZ v c z x).det = Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ (∑ i, z i) * detUnitZ c x) := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : detUnitZ c x ≠ 0 := fun h => not_dvd_detUnitZ hp2 hc x (h ▸ dvd_zero _)
  have hz : ((pv v : ℕ) : ℤ) ^ (∑ i, z i) * detUnitZ c x ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hu
  unfold genZ
  rw [LocGenus.det_mk, Dyadic7.zSqCl_of_ne v hz]
  have hdet := hessian_genZ (v := v) c z x
  have hne : algebraMap 𝔬 Fv ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).hessian.det ≠ 0 := by
    rw [hdet]; simpa using hz
  rw [detSqForm_of_ne hne]
  congr 1
  apply Units.ext
  simp only [Units.val_mk0, hdet]
  simp only [Rat.cast_intCast]
  rfl

theorem nondeg_genZ {c : ℤ} (hp2 : pv v ≠ 2) (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) : (genZ v c z x).Nondeg := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : detUnitZ c x ≠ 0 := fun h => not_dvd_detUnitZ hp2 hc x (h ▸ dvd_zero _)
  have hz : ((pv v : ℕ) : ℤ) ^ (∑ i, z i) * detUnitZ c x ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hu
  unfold genZ
  rw [LocGenus.nondeg_mk, hessian_genZ]
  exact fun h => hz (RingHom.injective_int (algebraMap ℤ 𝔬) (by simpa using h))

theorem coeff_genZ (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) (i j : Fin n) :
    ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).coeff i j =
      if i = j then algebraMap ℤ 𝔬 (vecZ (pv v) c z x i) else 0 := by
  unfold formZ
  rw [map_diag_eq]
  show (Matrix.diagonal _) i j = _
  rw [Matrix.diagonal_apply]

theorem prim_genZ_iff {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genZ v c z x).Prim ↔ ∃ i, z i = 0 := by
  unfold genZ
  rw [LocGenus.prim_mk]
  unfold Hanke2011Structure.IsPrimitiveForm
  constructor
  · intro hP
    by_contra hnot
    push_neg at hnot
    have hle : Ideal.span (Set.range fun q : Fin n × Fin n =>
          ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).coeff q.1 q.2) ≤
        Ideal.span {eInt v (pv v : ℤ_[pv v])} := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      beta_reduce
      rw [coeff_genZ]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, SetLike.mem_coe, Ideal.mem_span_singleton]
        have : algebraMap ℤ 𝔬 (vecZ (pv v) c z x i) =
            eInt v (((pv v : ℕ) : ℤ_[pv v]) ^ z i * ((rep c (x i) : ℤ) : ℤ_[pv v])) := by
          unfold vecZ
          simp
        rw [this]
        exact map_dvd (eInt v) (dvd_mul_of_dvd_left (dvd_pow_self _ (hnot i)) _)
      · rw [if_neg hij]; exact Ideal.zero_mem _
    rw [hP, top_le_iff, Ideal.span_singleton_eq_top] at hle
    exact PadicInt.irreducible_p.not_isUnit ((MulEquiv.isUnit_map (eInt v).toMulEquiv).1 hle)
  · rintro ⟨i, hi⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨(i, i), rfl⟩) ?_
    show IsUnit (((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).coeff i i)
    rw [coeff_genZ, if_pos rfl]
    have : vecZ (pv v) c z x i = rep c (x i) := by simp [vecZ, hi]
    rw [this, eq_intCast]
    exact intCast_unit_o v (not_dvd_rep hc _)


theorem vecZ_ne_zero {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) (i : Fin n) :
    vecZ (pv v) c z x i ≠ 0 := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  exact mul_ne_zero (pow_ne_zero _ hpz) (fun h => not_dvd_rep hc (x i) (h ▸ dvd_zero _))

/-- The Hilbert symbol of two entries `p^a rep(e)`, `p^b rep(f)` at an odd prime, as a unit. -/
theorem hilb_pair (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e f : ℤˣ) :
    hilbertSymbol ℚ_[pv v] (((((pv v : ℕ) : ℤ) ^ a * rep c e : ℤ)) : ℚ_[pv v])
        (((((pv v : ℕ) : ℤ) ^ b * rep c f : ℤ)) : ℚ_[pv v]) =
      ((hp (negOneChar (pv v)) a b e f : ℤˣ) : ℤ) := by
  have h1 : ∀ (k : ℕ) (g : ℤˣ), (((((pv v : ℕ) : ℤ) ^ k * rep c g : ℤ)) : ℚ_[pv v]) =
      ((pv v : ℕ) : ℚ_[pv v]) ^ k * (((repU hc g : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]) := by
    intro k g
    rw [repU_val]
    push_cast
    rfl
  rw [h1, h1, hilbertSymbol_odd_formula hp2, unitChar_repU hc, unitChar_repU hc]
  unfold hp
  rw [show a * b * ((pv v - 1) / 2) = (pv v - 1) / 2 * (a * b) by ring, pow_mul, negOne_pow hp2]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]

theorem hasse_genZ (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genZ v c z x).hasse = ((hasseZ (negOneChar (pv v)) z x : ℤˣ) : ℤ) := by
  have hp2 := pv_ne_two v hv
  classical
  set d := vecZ (pv v) c z x with hd
  have hnz : ∀ i, algebraMap ℚ Fv (((d i : ℤ) : ℚ)) ≠ 0 := by
    intro i
    refine (map_ne_zero _).2 ?_
    exact_mod_cast vecZ_ne_zero hc z x i
  have hiso : ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)).map (algebraMap 𝔬 Fv) =
      QuadForm.diag (fun i => algebraMap ℚ Fv (((d i : ℤ) : ℚ))) := by
    unfold formZ
    rw [map_diag_eq, map_diag_eq]
    congr 1
    funext i
    simp [hd]
  unfold genZ
  rw [LocGenus.hasse_mk, hasseForm, hiso, hasseC_diag v _ hnz]
  have e2 : PadicClass.hasseVec (fun i => algebraMap ℚ Fv (((d i : ℤ) : ℚ))) =
      (NFPlace.finite v).hasseSerre (fun i => ((d i : ℤ) : ℚ)) := by
    unfold NFPlace.hasseSerre PadicClass.hasseVec
    simp only [NFPlace.hilbert, eq_ratCast]
    try rfl
  rw [e2, NFPlace.hasseSerre_rat]
  have e3 : (NFPlace.finite v).toRatPlace.hasseSerre (fun i => ((d i : ℤ) : ℚ)) =
      hasseInvariant ℚ_[pv v] (fun i => ((d i : ℤ) : ℚ)) :=
    RatPlace.hasseSerre_finite (Rat.HeightOneSpectrum.primesEquiv v) _
  rw [e3]
  have e4 : hasseInvariant ℚ_[pv v] (fun i => ((d i : ℤ) : ℚ)) =
      PadicClass.hasseVec (fun i : Fin n => (((d i : ℤ) : ℚ) : ℚ_[pv v])) := rfl
  rw [e4]
  unfold PadicClass.hasseVec hasseZ
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · have := hilb_pair hp2 hc (z i) (z j) (x i) (x j)
    simpa [hd, vecZ] using this
  · simp


theorem gram_genZ (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    gramQp (eInt v) ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)) =
      (matZ (pv v) c z x).map (Int.cast : ℤ → ℚ_[pv v]) := by
  have h : (formZ (pv v) c z x).map (algebraMap ℤ 𝔬) =
      QuadForm.diag (fun i => eInt v (((vecZ (pv v) c z x i : ℤ) : ℤ_[pv v]))) := by
    unfold formZ
    rw [map_diag_eq]
    congr 1
    funext i
    rw [map_intCast]
    exact eq_intCast (algebraMap ℤ 𝔬) _
  rw [h, gramQp_diag]
  unfold matZ
  rw [Matrix.diagonal_map (Int.cast_zero)]
  congr 1

theorem isOddSymbolOf_matZ (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) :
    IsOddSymbolOf (pv v) ((matZ (pv v) c z x).map (Int.cast : ℤ → ℚ_[pv v])) (symC z x) := by
  have k : (fun i => chiU (repU hc (x i))) = x := by
    funext i; exact chiU_repU hc (x i)
  refine ⟨z, fun i => (((repU hc (x i) : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]), fun i => ?_, ?_, ?_⟩
  · show ‖(((repU hc (x i) : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])‖ = 1
    rw [PadicInt.norm_coe]
    exact PadicInt.isUnit_iff.1 (repU hc (x i)).isUnit
  · have : (matZ (pv v) c z x).map (Int.cast : ℤ → ℚ_[pv v]) =
        Matrix.diagonal (fun i => ((pv v : ℕ) : ℚ_[pv v]) ^ z i *
          (((repU hc (x i) : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v])) := by
      unfold matZ
      rw [Matrix.diagonal_map (Int.cast_zero)]
      congr 1
      funext i
      simp [vecZ, repU_val]
    rw [this]
    exact ZpEquiv.refl _
  · rw [oddSymbolOfDiag_eq_symC hp2, k]

theorem isOddSymbolOf_genZ (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) :
    IsOddSymbolOf (pv v) (gramQp (eInt v) ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬))) (symC z x) := by
  rw [gram_genZ]; exact isOddSymbolOf_matZ hp2 hc z x

/-- **Two diagonal genera coincide iff their symbols do** (Conway–Sloane's Theorem 9). -/
theorem genZ_eq_iff (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z z' : Fin n → ℕ)
    (x x' : Fin n → ℤˣ) : genZ v c z x = genZ v c z' x' ↔ symC z x = symC z' x' := by
  unfold genZ
  rw [LocGenus.mk_eq_mk, isometricGL_iff_zpEquiv_gram (eInt v)]
  constructor
  · intro h
    exact oddSymbol_eq_of_zpEquiv hp2 h (isOddSymbolOf_genZ hp2 hc z x) (isOddSymbolOf_genZ hp2 hc z' x')
  · intro h
    refine zpEquiv_of_oddSymbol_eq hp2 (isOddSymbolOf_genZ hp2 hc z x) ?_
    rw [h]; exact isOddSymbolOf_genZ hp2 hc z' x'

/-- **Every nondegenerate local genus (odd $p$) is the genus of a diagonal form** `genZ z x`. -/
theorem exists_genZ (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    (G : LocGenus v n) (hN : G.Nondeg) : ∃ (z : Fin n → ℕ) (x : Fin n → ℤˣ), G = genZ v c z x := by
  have hp2 := pv_ne_two v hv
  induction G using Quotient.inductionOn with
  | _ T =>
  have hT : T.hessian.det ≠ 0 := (LocGenus.nondeg_mk T).1 hN
  obtain ⟨σ, hσ⟩ := exists_isOddSymbolOf hp2 (gramQp_symm (eInt v) T) (gramQp_det (eInt v) T hT)
    (gramQp_norm hp2 (eInt v) T)
  obtain ⟨z, u, hu, hZ, rfl⟩ := hσ
  have hunit : ∀ i, IsUnit (⟨u i, (PadicInt.mem_subring_iff (pv v)).2 (hu i).le⟩ : ℤ_[pv v]) := fun i => by
    refine PadicInt.isUnit_iff.2 ?_
    exact hu i
  set w : Fin n → ℤ_[pv v]ˣ := fun i => (hunit i).unit with hw
  have hu' : u = fun i => (((w i : ℤ_[pv v]ˣ) : ℤ_[pv v]) : ℚ_[pv v]) := rfl
  refine ⟨z, fun i => chiU (w i), ?_⟩
  unfold genZ
  show LocGenus.mk T = LocGenus.mk _
  rw [LocGenus.mk_eq_mk, isometricGL_iff_zpEquiv_gram (eInt v)]
  refine zpEquiv_of_oddSymbol_eq hp2 ⟨z, u, hu, hZ, rfl⟩ ?_
  rw [hu', oddSymbolOfDiag_eq_symC hp2]
  exact isOddSymbolOf_genZ hp2 hc z _


theorem det_matZ (c : ℤ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (matZ (pv v) c z x).det = ((pv v : ℕ) : ℤ) ^ (∑ i, z i) * ∏ i, rep c (x i) := by
  unfold matZ
  rw [Matrix.det_diagonal, prod_vecZ]

theorem matZ_det_ne {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (matZ (pv v) c z x).det ≠ 0 := by
  unfold matZ
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => vecZ_ne_zero hc z x i

theorem padicVal_matZ {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    padicValInt (pv v) (matZ (pv v) c z x).det = ∑ i, z i := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : ∏ i, rep c (x i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => fun h =>
    not_dvd_rep hc (x i) (h ▸ dvd_zero _)
  have hnd : ¬ (pv v : ℤ) ∣ ∏ i, rep c (x i) := by
    have hpp := Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)
    intro h
    rcases (Prime.dvd_finset_prod_iff hpp _).1 h with ⟨i, _, hi⟩
    exact not_dvd_rep hc _ hi
  rw [det_matZ, padicValInt.mul (pow_ne_zero _ hpz) hu, padicValInt.eq_zero_of_not_dvd hnd, add_zero]
  have : (((pv v : ℕ) : ℤ) ^ (∑ i, z i)) = (((pv v) ^ (∑ i, z i) : ℕ) : ℤ) := (Nat.cast_pow (pv v) _).symm
  rw [this, padicValInt.of_nat, padicValNat.prime_pow]

theorem beta_genZ_alpha {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genZ v c z x).beta = (1 / 2 : ℝ) * alphaP (pv v) (matZ (pv v) c z x) := by
  unfold genZ
  rw [LocGenus.beta_mk]
  unfold betaForm
  have hG : Hanke2005.gramOf v ((formZ (pv v) c z x).map (algebraMap ℤ 𝔬)) =
      ((matZ (pv v) c z x).map (algebraMap ℤ 𝔬)).map (algebraMap 𝔬 Fv) := by
    unfold Hanke2005.gramOf formZ matZ
    rw [map_diag_eq, hessian_diag_gen]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with hij
    · simp only [map_mul, map_ofNat]
      field_simp
    · simp
  rw [hG]
  exact hankeBeta_eq_half_alphaP v (Matrix.isSymm_diagonal _) (matZ_det_ne hc z x)

theorem sqrt_pow_eq (p : ℕ) (a ν : ℕ) :
    (p : ℝ) ^ (((ν : ℝ) * ((a : ℝ) + 1)) / 2) = Real.sqrt p ^ ((a + 1) * ν) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  push_cast
  ring

/-- **The inverse local density of a diagonal genus is twice its weight**: $\beta(G)^{-1} = 2\,\mathrm{wt}(\sigma)$,
$\sigma$ the symbol (for odd $p$, any rank $n$). -/
theorem beta_genZ (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genZ v c z x).beta = (2 * wtC (Mw (pv v)) (aw (pv v)) (symC z x))⁻¹ := by
  have hp2 := pv_ne_two v hv
  have hpr := (Fact.out : (pv v).Prime)
  have hα := alphaP_eq_div hpr (A := matZ (pv v) c z x) (Matrix.isSymm_diagonal _) (matZ_det_ne hc z x)
  have hm : pMassDensity (pv v) (matZ (pv v) c z x) = pMassOdd (pv v) (symC z x) (bnd z) :=
    (pMassFormulaOdd hp2).pMass_eq _ (Matrix.isSymm_diagonal _) (matZ_det_ne hc z x) _ (bnd z)
      (isOddSymbolOf_matZ hp2 hc z x) (trivFrom_symC z x (lt_bnd z))
  have hw := wtC_mul_pow (pv v) hpr.pos (trivFrom_symC z x (lt_bnd z))
  rw [rkC_symC, zsC_symC] at hw
  rw [beta_genZ_alpha hc, hα, hm, padicVal_matZ hc, sqrt_pow_eq, ← hw]
  have hs : Real.sqrt (pv v) ^ ((n + 1) * ∑ i, z i) ≠ 0 :=
    pow_ne_zero _ (Real.sqrt_pos.2 (Nat.cast_pos.2 hpr.pos)).ne'
  field_simp

theorem exists_symC {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {σ : OddSymbol} {n : ℕ} (hV : Valid σ) (hF : FinSupp σ)
    (hr : rkC σ = n) : ∃ (z : Fin n → ℕ) (x : Fin n → ℤˣ), symC z x = σ := by
  obtain ⟨N, hN⟩ := hF
  have hdim : ∑ k ∈ range N, (σ k).dim = n := by
    have h1 : rkC σ = rk σ N := stable_rk.cut_eq hN
    rw [← hr, h1]; rfl
  obtain ⟨z, w, hz, hw, hs⟩ := exists_int_diag_dim hp2 (σ := σ) (N := N) (n := n) hN (fun k => hV k) hdim
  refine ⟨z, fun i => chiU (cu (hw i)), ?_⟩
  have h1 := oddSymbolOfDiag_eq_symC hp2 z (fun i => cu (hw i))
  rw [← h1, ← hs]
  congr 2

/-- The symbol of a genus: `Gs σ` is the genus `genZ z x` for any `(z, x)` with `symC z x = σ`. -/
def Gs (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℤ) (n : ℕ) (σ : OddSymbol) : LocGenus v n := by
  classical
  exact if h : ∃ zx : (Fin n → ℕ) × (Fin n → ℤˣ), symC zx.1 zx.2 = σ then genZ v c h.choose.1 h.choose.2
    else genZ v c (fun _ => 0) (fun _ => 1)

theorem Gs_symC (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) : Gs v c n (symC z x) = genZ v c z x := by
  classical
  have h : ∃ zx : (Fin n → ℕ) × (Fin n → ℤˣ), symC zx.1 zx.2 = symC z x := ⟨(z, x), rfl⟩
  unfold Gs
  rw [dif_pos h]
  exact (genZ_eq_iff hp2 hc _ _ _ _).2 h.choose_spec

theorem not_dvd_two_int (hp2 : pv v ≠ 2) : ¬ (pv v : ℤ) ∣ 2 := by
  intro h
  have h2 : pv v ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : (pv v).Prime) Nat.prime_two).1 h2)

/-- The character of $2$: $\left(\frac2p\right)$. -/
def chi2 (hp2 : pv v ≠ 2) : ℤˣ := chiU (cu (not_dvd_two_int hp2))

theorem chiU_cu_detUnitZ (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} (x : Fin n → ℤˣ) :
    chiU (cu (not_dvd_detUnitZ hp2 hc x)) = chi2 hp2 ^ n * ∏ i, x i := by
  have h : cu (not_dvd_detUnitZ hp2 hc x) = (cu (not_dvd_two_int hp2)) ^ n * ∏ i, repU hc (x i) := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, cu_val, repU_val, detUnitZ]
    push_cast
    rfl
  rw [h, map_mul, map_pow, map_prod]
  simp [chi2, chiU_repU]

theorem det_genZ_iff (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) (ν : ℕ) :
    (genZ v c z x).det = Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w) ↔
      ∑ i, z i = ν ∧ ∏ i, x i = chi2 (pv_ne_two v hv) ^ n * chiU (cu hw) := by
  have hp2 := pv_ne_two v hv
  rw [det_genZ hp2 hc, zSqCl_eq_iff_odd v hp2 _ _ (not_dvd_detUnitZ hp2 hc x) hw, chiU_cu_detUnitZ hp2 hc x]
  refine and_congr Iff.rfl ?_
  set a := chi2 hp2 ^ n
  have ha : a * a = 1 := Int.units_mul_self _
  constructor
  · intro h
    calc ∏ i, x i = (a * a) * ∏ i, x i := by rw [ha, one_mul]
      _ = a * (a * ∏ i, x i) := by rw [mul_assoc]
      _ = _ := by rw [h]
  · intro h
    rw [h, ← mul_assoc, ha, one_mul]

theorem one_le_dim_symC_iff {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : 1 ≤ (symC z x 0).dim ↔ ∃ i, z i = 0 := by
  rw [symC_dim, ← Finset.card_filter, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero,
    ← Ne, ← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty]

/-- The Hasse invariant as a function of the state. -/
def hasseObs (e : ℤˣ) (s : State) : ℤˣ := hclosed e s.1 s.2.1 s.2.2.2

/-- The observable: the indicator of "unit class $e$ and Hasse invariant $\varepsilon$". -/
def phiObs (eps e : ℤˣ) (ε : ℤ) (s : State) : ℝ :=
  open Classical in if s.1 * s.2.1 = e ∧ ((hasseObs eps s : ℤˣ) : ℤ) = ε then 1 else 0

/-- The set of symbols corresponding to $\mathrm{Gen}^*_p(S, \varepsilon; n)$. -/
def symTarget (eps e : ℤˣ) (ε : ℤ) (n ν : ℕ) : Set OddSymbol :=
  {σ | (σ ∈ symSet n ν ∧ 1 ≤ (σ 0).dim) ∧
    ((statC σ).1 * (statC σ).2.1 = e ∧ ((hasseObs eps (statC σ) : ℤˣ) : ℤ) = ε)}

theorem hasse_obs_symC (e : ℤˣ) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    hasseObs e (statC (symC z x)) = hasseZ e z x := by
  rw [statC_symC, hasseZ_closed]; rfl

/-- **The genera of $\mathrm{Gen}^*_p(S,\varepsilon;n)$ are the genera of the symbols of `symTarget`.** -/
theorem genStar_eq_image (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) (ν : ℕ) (ε : ℤ) :
    {G : LocGenus v n | G.IsGenStar (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w)) ε} =
      Gs v c n '' symTarget (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) ε n ν := by
  have hp2 := pv_ne_two v hv
  ext G
  constructor
  · rintro ⟨hN, hP, hd, hh⟩
    obtain ⟨z, x, rfl⟩ := exists_genZ hv hc G hN
    rw [prim_genZ_iff hc] at hP
    rw [det_genZ_iff hv hc] at hd
    rw [hasse_genZ hv hc] at hh
    refine ⟨symC z x, ⟨⟨?_, (one_le_dim_symC_iff z x).2 hP⟩, ?_, ?_⟩, Gs_symC hp2 hc z x⟩
    · rw [← hd.1]; exact symC_mem z x
    · rw [statC_symC]; simp only [evZ_mul_odZ]; exact hd.2
    · rw [hasse_obs_symC]; exact hh
  · rintro ⟨σ, ⟨⟨hσ, hdim⟩, hc1, hc2⟩, rfl⟩
    obtain ⟨z, x, rfl⟩ := exists_symC hp2 hσ.1 hσ.2.1 hσ.2.2.1
    have hzs : ∑ i, z i = ν := by rw [← zsC_symC z x]; exact hσ.2.2.2
    rw [Gs_symC hp2 hc]
    refine ⟨nondeg_genZ hp2 hc z x, (prim_genZ_iff hc z x).2 ((one_le_dim_symC_iff z x).1 hdim),
      (det_genZ_iff hv hc z x hw ν).2 ⟨hzs, ?_⟩, ?_⟩
    · rw [statC_symC] at hc1; simp only [evZ_mul_odZ] at hc1; exact hc1
    · rw [hasse_genZ hv hc]; rw [hasse_obs_symC] at hc2; exact hc2

theorem genStar_injOn (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ}
    (eps e : ℤˣ) (ε : ℤ) (ν : ℕ) : Set.InjOn (Gs v c n) (symTarget eps e ε n ν) := by
  have hp2 := pv_ne_two v hv
  intro σ₁ h₁ σ₂ h₂ h
  obtain ⟨z₁, x₁, rfl⟩ := exists_symC hp2 h₁.1.1.1 h₁.1.1.2.1 h₁.1.1.2.2.1
  obtain ⟨z₂, x₂, rfl⟩ := exists_symC hp2 h₂.1.1.1 h₂.1.1.2.1 h₂.1.1.2.2.1
  rw [Gs_symC hp2 hc, Gs_symC hp2 hc] at h
  exact (genZ_eq_iff hp2 hc _ _ _ _).1 h

/-- **The mass sum over $\mathrm{Gen}^*_p(S,\varepsilon;n)$ is a coefficient of the generating series.** -/
theorem sum_genStar_eq (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) {n : ℕ} {w : ℤ}
    (hw : ¬ (pv v : ℤ) ∣ w) (G₀ : LocGenus v n) (hN₀ : G₀.Nondeg) :
    ∃ K : ℝ, ∀ (ν : ℕ) (ε : ℤ),
      ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w)) ε},
          G₀.beta / G.beta =
        K * coef (Mw (pv v)) (aw (pv v)) (fun f => 1 ≤ f.dim)
          (phiObs (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) ε) n ν := by
  have hp2 := pv_ne_two v hv
  obtain ⟨z₀, x₀, rfl⟩ := exists_genZ hv hc G₀ hN₀
  refine ⟨(wtC (Mw (pv v)) (aw (pv v)) (symC z₀ x₀))⁻¹, fun ν ε => ?_⟩
  rw [genStar_eq_image hv hc hw ν ε, finsum_mem_image (genStar_injOn hv hc _ _ _ _)]
  have step : ∀ σ ∈ symTarget (negOneChar (pv v)) (chi2 hp2 ^ n * chiU (cu hw)) ε n ν,
      (genZ v c z₀ x₀).beta / (Gs v c n σ).beta =
        (wtC (Mw (pv v)) (aw (pv v)) (symC z₀ x₀))⁻¹ * wtC (Mw (pv v)) (aw (pv v)) σ := by
    intro σ hσ
    obtain ⟨z, x, rfl⟩ := exists_symC hp2 hσ.1.1.1 hσ.1.1.2.1 hσ.1.1.2.2.1
    rw [Gs_symC hp2 hc, beta_genZ hv hc, beta_genZ hv hc, div_eq_mul_inv, inv_inv, mul_inv]
    ring
  rw [finsum_mem_congr rfl step, ← mul_finsum_mem]
  congr 1
  unfold coef
  set T := symTarget (negOneChar (pv v)) (chi2 hp2 ^ n * chiU (cu hw)) ε n ν with hT
  set s : Set OddSymbol := {σ | σ ∈ symSet n ν ∧ (fun f : OddFactor => 1 ≤ f.dim) (σ 0)} with hs
  have hsf : s.Finite := (symSet_finite n ν).subset (fun σ h => h.1)
  have hTs : T ⊆ s := fun σ h => h.1
  rw [← finsum_mem_add_sdiff hTs hsf]
  have h0 : ∑ᶠ σ ∈ s \ T, phiObs (negOneChar (pv v)) (chi2 hp2 ^ n * chiU (cu hw)) ε (statC σ) *
      wtC (Mw (pv v)) (aw (pv v)) σ = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero fun σ hσ => ?_
    have : ¬ ((statC σ).1 * (statC σ).2.1 = chi2 hp2 ^ n * chiU (cu hw) ∧
        ((hasseObs (negOneChar (pv v)) (statC σ) : ℤˣ) : ℤ) = ε) := fun h => hσ.2 ⟨hσ.1, h⟩
    unfold phiObs
    rw [if_neg this, zero_mul]
  have h1 : ∑ᶠ σ ∈ T, phiObs (negOneChar (pv v)) (chi2 hp2 ^ n * chiU (cu hw)) ε (statC σ) *
      wtC (Mw (pv v)) (aw (pv v)) σ = ∑ᶠ σ ∈ T, wtC (Mw (pv v)) (aw (pv v)) σ := by
    refine finsum_mem_congr rfl fun σ hσ => ?_
    unfold phiObs
    rw [if_pos hσ.2, one_mul]
  rw [h0, h1, add_zero]

/-- **The normalized local mass sum $A^*_{p;n}(S)$ of the true local genera** (Def. 4.6), $p$ odd, rank $n$: the
sum of $\beta(G_0)/\beta(G)$ over the nondegenerate primitive local genera $G$ with $\det_H(G) = S$ (both Hasse
invariants), $G_0$ the reference (unimodular) genus. -/
def trueAstar (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S 1}, G₀.beta / G.beta) +
    ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S (-1)}, G₀.beta / G.beta

/-- **The normalized local mass sum $B^*_{p;n}(S)$ of the true local genera** (Hasse invariant as a sign). -/
def trueBstar (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (G₀ : LocGenus v n) (S : LocalSqCl v) : ℝ :=
  (∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S 1}, G₀.beta / G.beta) -
    ∑ᶠ G ∈ {G : LocGenus v n | G.IsGenStar S (-1)}, G₀.beta / G.beta

/-- **Theorem 5.4 (for $A^*$) at an odd prime, every rank $n$, $F = \mathbb Q$, true local genera.**  For $p \nmid 2$,
$w$ an integer prime to $p$ and $G_0$ the (unimodular, $\det_H = [w]$) reference genus, the fixed-unit series
$\sum_\nu A^*_{p;n}([p^\nu w])X^\nu$, $X = p^{-s}$, is a rational function of $X$: it is $P/Q$ for polynomials
$P$, $Q$ with $Q(0) \ne 0$.  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (A*, every rank n, F = Q, p odd)"]
theorem theorem_5_4_odd_A_rank (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {n : ℕ} {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w)
    (G₀ : LocGenus v n) (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (Dyadic7.zSqCl v w) ε₀) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueAstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w))) := by
  obtain ⟨c, hc⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  obtain ⟨K, hK⟩ := sum_genStar_eq hv hc hw G₀ (by obtain ⟨ε₀, h, -⟩ := hG₀; exact h)
  have hM := Mw_zero (pv v)
  have ha := aw_zero (pv v)
  have e : (PowerSeries.mk fun ν : ℕ => trueAstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (Mw (pv v)) (aw (pv v)) (fun f => 1 ≤ f.dim)
            (phiObs (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) 1) n +
          ser (Mw (pv v)) (aw (pv v)) (fun f => 1 ≤ f.dim)
            (phiObs (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueAstar, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (rat_Pn hM ha n _))

/-- **Theorem 5.4 (for $B^*$) at an odd prime, every rank $n$, $F = \mathbb Q$, true local genera**: the fixed-unit
series $\sum_\nu B^*_{p;n}([p^\nu w])X^\nu$ is a rational function of $X = p^{-s}$. Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (B*, every rank n, F = Q, p odd)"]
theorem theorem_5_4_odd_B_rank (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {n : ℕ} {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w)
    (G₀ : LocGenus v n) (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (Dyadic7.zSqCl v w) ε₀) :
    RatSeries (PowerSeries.mk fun ν : ℕ => trueBstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w))) := by
  obtain ⟨c, hc⟩ := exists_nonresidue (p := pv v) (pv_ne_two v hv)
  obtain ⟨K, hK⟩ := sum_genStar_eq hv hc hw G₀ (by obtain ⟨ε₀, h, -⟩ := hG₀; exact h)
  have hM := Mw_zero (pv v)
  have ha := aw_zero (pv v)
  have e : (PowerSeries.mk fun ν : ℕ => trueBstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ ν * w))) =
      PowerSeries.C K * PowerSeries.X ^ 0 *
        (ser (Mw (pv v)) (aw (pv v)) (fun f => 1 ≤ f.dim)
            (phiObs (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) 1) n +
          PowerSeries.C (-1) * PowerSeries.X ^ 0 *
            ser (Mw (pv v)) (aw (pv v)) (fun f => 1 ≤ f.dim)
              (phiObs (negOneChar (pv v)) (chi2 (pv_ne_two v hv) ^ n * chiU (cu hw)) (-1)) n) := by
    ext ν
    rw [PowerSeries.coeff_mk, trueBstar, hK ν 1, hK ν (-1)]
    simp [ser, PowerSeries.coeff_mk, mul_add]
    ring
  rw [e]
  exact RatSeries.CXpowMul K 0 ((rat_Pn hM ha n _).add (RatSeries.CXpowMul (-1) 0 (rat_Pn hM ha n _)))

/-- **Corollary 5.5 for $A^*$ at an odd prime, every rank $n$, $F = \mathbb Q$** (distinguished family
$\lambda(p^i) = p^i$, i.e. $w = 1$): the Euler factor $\sum_iA^*_{p;n}([p^i])\,p^{-is}$ is a rational function of
$p^{-s}$. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, every rank n, F = Q, p odd, lambda(p^i) = p^i)"]
theorem cor_5_5_odd_A_rank (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n)
    (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (Dyadic7.zSqCl v 1) ε₀) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueAstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ i))) := by
  have h := theorem_5_4_odd_A_rank hv (w := 1) (Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)).not_dvd_one G₀ hG₀
  simpa only [mul_one] using h

/-- **Corollary 5.5 for $B^*$ at an odd prime, every rank $n$, $F = \mathbb Q$** ($\lambda(p^i) = p^i$). -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, every rank n, F = Q, p odd, lambda(p^i) = p^i)"]
theorem cor_5_5_odd_B_rank (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {n : ℕ} (G₀ : LocGenus v n)
    (hG₀ : ∃ ε₀ : ℤ, G₀.IsGenStar (Dyadic7.zSqCl v 1) ε₀) :
    RatSeries (PowerSeries.mk fun i : ℕ => trueBstar v n G₀ (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ i))) := by
  have h := theorem_5_4_odd_B_rank hv (w := 1) (Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)).not_dvd_one G₀ hG₀
  simpa only [mul_one] using h

end Gen

end

end QuadFormsKB.Hanke2011Structure.RatOdd

#print axioms QuadFormsKB.Hanke2011Structure.RatOdd.sum_genStar_eq
