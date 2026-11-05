/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityOddStats
import QuadFormsKB.Literature.Hanke2005.DensityOddJordan
import QuadFormsKB.Literature.Hanke2005.DensityOddProduct
import QuadFormsKB.Tamagawa.TernaryBadDVR
import QuadFormsKB.Tamagawa.OrthFq

/-!
# Paper 6, Theorem 5.4 at $\mathfrak p \nmid 2$ of a number field: the density of a diagonal genus

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23.

This file is the density step of the proof of Theorem 5.4 at a prime $\mathfrak p \nmid 2$ of an arbitrary number
field $F$, every rank $n$ (the analogue of `RatOdd.beta_genZ` for $F = \mathbb Q$).  It is stated for an arbitrary
discrete valuation ring $R$ with uniformizer $\pi \nmid 2$ and finite residue field $\mathbb F$ of size $q$ (later:
$R = \mathcal O_{\mathfrak p}$).

Fix a unit $c \in R^\times$ whose residue is a nonsquare in $\mathbb F$ (`chiR c = -1`), put
$\operatorname{rep}(\pm1) = 1, c$ (`repR`), and $e = \chi(-1) \in \{\pm1\}$ (a unit `e` with $e = \chi(-1)$).  For exponents
$z_i \in \mathbb N$ and signs $x_i \in \{\pm1\}$ ($i < n$) let $D(z,x) = \operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$
(`diagVec`).  Its Conway–Sloane-style symbol is `RatOdd`'s `symC z x` (multiplicity $n_k = \#\{i : z_i = k\}$ and sign
$\prod_{z_i = k}x_i$ at scale $k$).

**Main result** (`loc_diag`): the self-density $\alpha_\pi(D(z,x), D(z,x))$ (`DVR.localDensityForm`, the full density
counting the orthogonal group, twice Hanke's $\beta$) equals the inverse weight
$$\alpha_\pi(D(z,x), D(z,x)) = \mathrm{wt}(\operatorname{symC}(z,x))^{-1},\qquad
  \mathrm{wt}(\sigma) = \prod_kM_q(n_k,\varepsilon_k)\prod_ka_{\rho_k},\quad a_\rho = q^{-\rho(\rho+1)/2},$$
with the unimodular factor $M_q(d,\varepsilon) = P_q(d,\varepsilon)^{-1}$,
$P_q(0,+) = 1$, $P_q(2m+1,\cdot) = 2\prod_{i=1}^m(1-q^{-2i})$,
$P_q(2m,\varepsilon) = 2(1-\chi_Dq^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$, $\chi_D = e^m\varepsilon$ (`Pq`, `Mq`, `aq`).

*Proof.* Strong induction on $n + \sum_iz_i$.  If every $z_i \ge 1$ then $D(z,x) = \pi D(z-1,x)$ and
$\alpha(\pi Q) = q^{n(n+1)/2}\alpha(Q)$ (`Tamagawa.localDensityForm_smul_pi`).  Otherwise permute the $a \ge 1$ unit
entries to the front (`DVR.IsGLEquiv` for permutations), so $D \cong \langle u\rangle\perp T$ with all coefficients of
$T$ divisible by $\pi$, and $\alpha = \alpha(\langle u\rangle)\alpha(T)$ (`Hanke2005.localDensityForm_unitSum`); the
unimodular factor is the closed form `DVR.localDensityForm_self_odd` / `_even` (`loc_unit_diag`).  This matches the
peeling recursion `RatOdd.wtC_cons` of the weight.

Indices are 0-based.
-/

open Finset Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure.RatOdd
  QuadFormsKB.ConwaySloane QuadFormsKB.Odd7

noncomputable section

/-! ### The weights -/

/-- The density factor $P_q(d,\varepsilon)$ of a unimodular constituent of dimension $d$ and sign $\varepsilon$
(here $\varepsilon = \prod x_i$ of its unit entries; `e` is $\chi(-1)$): $1$ for $d = 0$,
$2\prod_{i=1}^m(1-q^{-2i})$ for $d = 2m+1$, and $2(1-e^m\varepsilon q^{-m})\prod_{i=1}^{m-1}(1-q^{-2i})$ for
$d = 2m$, $m \ge 1$. -/
def Pq (q : ℕ) (e : ℤˣ) (d : ℕ) (s : Sign) : ℝ :=
  if d = 0 then 1
  else if d % 2 = 1 then 2 * ∏ i ∈ range (d / 2), (1 - ((q : ℝ) ^ (2 * (i + 1)))⁻¹)
  else 2 * (1 - (((e ^ (d / 2) * signU s : ℤˣ) : ℤ) : ℝ) * ((q : ℝ) ^ (d / 2))⁻¹) *
    ∏ i ∈ range (d / 2 - 1), (1 - ((q : ℝ) ^ (2 * (i + 1)))⁻¹)

/-- **The factor weight** $M_q(d,\varepsilon) = P_q(d,\varepsilon)^{-1}$. -/
def Mq (q : ℕ) (e : ℤˣ) (d : ℕ) (s : Sign) : ℝ := (Pq q e d s)⁻¹

/-- **The gap weight** $a_\rho = q^{-\rho(\rho+1)/2}$. -/
def aq (q : ℕ) (ρ : ℕ) : ℝ := ((q : ℝ) ^ (ρ * (ρ + 1) / 2))⁻¹

theorem Mq_zero (q : ℕ) (e : ℤˣ) : Mq q e 0 Sign.plus = 1 := by simp [Mq, Pq]

theorem aq_zero (q : ℕ) : aq q 0 = 1 := by simp [aq]

/-! ### Units, characters and the representatives -/

section Gen

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

/-- The quadratic character of the residue field at the residue of $r \in R$. -/
def chiR (r : R) : ℤ := quadraticChar 𝔽 (res r)

/-- The representative of the sign $x \in \{\pm1\}$: $1$ for $x = 1$, the fixed nonsquare unit $c$ for $x = -1$. -/
def repR (c : R) (x : ℤˣ) : R := if x = 1 then 1 else c

/-- The diagonal entries $\pi^{z_i}\operatorname{rep}(x_i)$. -/
def diagVec (π c : R) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : Fin n → R :=
  fun i => π ^ z i * repR c (x i)

theorem chiR_one : chiR (1 : R) = 1 := by simp [chiR]

theorem chiR_repR {c : R} (hc : chiR c = -1) (x : ℤˣ) : chiR (repR c x) = (x : ℤ) := by
  unfold repR
  split_ifs with h
  · rw [chiR_one, h]; rfl
  · rw [hc]
    rcases Int.units_eq_one_or x with h' | h'
    · exact absurd h' h
    · rw [h']; rfl

theorem isUnit_repR {c : R} (hc : IsUnit c) (x : ℤˣ) : IsUnit (repR c x) := by
  unfold repR; split_ifs
  · exact isUnit_one
  · exact hc

theorem chiR_mul (a b : R) : chiR (a * b) = chiR a * chiR b := by
  simp [chiR, map_mul]

theorem chiR_prod {ι : Type*} (s : Finset ι) (f : ι → R) : chiR (∏ i ∈ s, f i) = ∏ i ∈ s, chiR (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chiR_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, chiR_mul, ih]

/-! ### The unimodular constituent -/

section Unit

variable {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {c : R} (hcU : IsUnit c) (hc : chiR c = -1)
  {e : ℤˣ} (he : (e : ℤ) = quadraticChar (IsLocalRing.ResidueField R) (-1 : IsLocalRing.ResidueField R))

include hπ h2 hcU in
theorem not_dvd_hessian_diag_rep {a : ℕ} (x : Fin a → ℤˣ) :
    ¬ π ∣ (QuadForm.diag fun i => repR c (x i)).hessian.det := by
  rw [det_hessian_diag]
  have h2u : IsUnit (2 : R) := dvr_isUnit_of_not_dvd hπ h2
  refine dvr_not_dvd_of_isUnit hπ ((h2u.pow _).mul (IsUnit.prod_univ_iff.2 fun i => isUnit_repR hcU _))

include hπ h2 hcU hc in
theorem chiDisc_diag_rep {a : ℕ} (x : Fin a → ℤˣ) :
    chiDisc (QuadForm.diag fun i => repR c (x i)) =
      quadraticChar (IsLocalRing.ResidueField R) (-1 : IsLocalRing.ResidueField R) ^ (a / 2) *
        ∏ i, ((x i : ℤˣ) : ℤ) := by
  have h2F : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := res_ne_zero hπ h2; rwa [map_ofNat] at this
  unfold chiDisc resGramDet
  rw [det_hessian_diag]
  have hres : IsLocalRing.residue R (2 ^ a * ∏ i, repR c (x i)) / (2 : IsLocalRing.ResidueField R) ^ a =
      ∏ i, IsLocalRing.residue R (repR c (x i)) := by
    rw [map_mul, map_pow, map_ofNat, map_prod]
    field_simp
  rw [hres, map_mul, map_pow, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have := chiR_repR hc (x i)
  exact this

include hπ h2 hcU hc he in
/-- **The self-density of a unimodular diagonal form** $\langle\operatorname{rep}(x_i)\rangle$ is $P_q(a,\varepsilon)$,
$\varepsilon = \prod_ix_i$ (as a sign). -/
theorem loc_unit_diag {a : ℕ} (x : Fin a → ℤˣ) :
    localDensityForm (QuadForm.diag fun i => repR c (x i)) (QuadForm.diag fun i => repR c (x i)) π =
      Pq (q R) e a (if ∏ i, x i = 1 then Sign.plus else Sign.minus) := by
  have hnd := not_dvd_hessian_diag_rep hπ h2 hcU x
  rcases Nat.even_or_odd' a with ⟨m, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [Pq]
      exact Hanke2005.localDensityForm_zero _ π
    · have := localDensityForm_self_even π m hm (QuadForm.diag fun i => repR c (x i)) hπ h2 hnd
      rw [this]
      have hm0 : 2 * m ≠ 0 := by omega
      have hmod : ¬ (2 * m) % 2 = 1 := by omega
      simp only [Pq, hm0, hmod, if_false, Nat.mul_div_cancel_left _ (two_pos)]
      rw [chiDisc_diag_rep hπ h2 hcU hc, ← he, signU_ite]
      congr 4
      · push_cast
        rw [Nat.mul_div_cancel_left _ two_pos]
  · have := localDensityForm_self_odd π m (QuadForm.diag fun i => repR c (x i)) hπ h2 hnd
    rw [this]
    have hm0 : 2 * m + 1 ≠ 0 := by omega
    have hmod : (2 * m + 1) % 2 = 1 := by omega
    simp only [Pq, hm0, hmod, if_false, if_true]
    congr 3
    omega

end Unit


/-! ### Splitting off the unit entries -/

section Split

variable {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {c : R} (hcU : IsUnit c) (hc : chiR c = -1)
  {e : ℤˣ} (he : (e : ℤ) = quadraticChar (IsLocalRing.ResidueField R) (-1 : IsLocalRing.ResidueField R))

include hπ h2 hcU in
theorem nondeg_diagVec {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (QuadForm.diag (diagVec π c z x)).Nondegenerate := by
  have h20 : (2 : R) ≠ 0 := (dvr_isUnit_of_not_dvd hπ h2).ne_zero
  unfold QuadForm.Nondegenerate
  rw [det_hessian_diag]
  refine mul_ne_zero (pow_ne_zero _ h20) (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
  exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (isUnit_repR hcU _).ne_zero

/-- The identification `Fin a ⊕ Fin b ≃ Fin (b + a)` (the units first). -/
def psi (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (b + a) := finSumFinEquiv.trans (finCongr (Nat.add_comm a b))

theorem psi_inl_val {a b : ℕ} (i : Fin a) : (psi a b (Sum.inl i)).val = i.val := by
  simp [psi]

theorem psi_inr_val {a b : ℕ} (j : Fin b) : (psi a b (Sum.inr j)).val = a + j.val := by
  simp [psi, Nat.add_comm]

theorem cseq_psi {b : ℕ} (t : Fin b → R) {a : ℕ} (u : Fin a → R) (s : Fin a ⊕ Fin b) :
    Hanke2005.cseq t a u (psi a b s) = Sum.elim u t s := by
  rcases s with i | j
  · rw [Hanke2005.cseq_lt t a u (psi a b (Sum.inl i)) (by rw [psi_inl_val]; exact i.2)]
    simp only [Sum.elim_inl]
    congr 1
  · rw [Hanke2005.cseq_ge t a u (psi a b (Sum.inr j)) (by rw [psi_inr_val]; omega)]
    simp only [Sum.elim_inr]
    congr 1
    exact Fin.ext (by simp [psi_inr_val])

/-- Splitting the indices into those with $z_i = 0$ and the rest. -/
theorem exists_split {n : ℕ} (z : Fin n → ℕ) :
    ∃ (a b : ℕ) (_ : b + a = n) (e0 : Fin a ⊕ Fin b ≃ Fin n),
      (∀ i, z (e0 (Sum.inl i)) = 0) ∧ (∀ j, z (e0 (Sum.inr j)) ≠ 0) := by
  classical
  let p : Fin n → Prop := fun i => z i = 0
  let e1 := Equiv.sumCompl p
  let ea := Fintype.equivFin {i // p i}
  let eb := Fintype.equivFin {i // ¬ p i}
  have hcard : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = n := by
    rw [← Fintype.card_sum, Fintype.card_congr e1, Fintype.card_fin]
  refine ⟨Fintype.card {i // p i}, Fintype.card {i // ¬ p i}, by omega,
    (Equiv.sumCongr ea.symm eb.symm).trans e1, fun i => ?_, fun j => ?_⟩
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, e1, Equiv.sumCompl_apply_inl]
    exact (ea.symm i).2
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, e1, Equiv.sumCompl_apply_inr]
    exact (eb.symm j).2

/-- **The symbol of a form with the unit entries split off.** -/
theorem symC_split {n a b : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (z : Fin n → ℕ) (x : Fin n → ℤˣ)
    (hz0 : ∀ i, z (e0 (Sum.inl i)) = 0) (hz1 : ∀ j, z (e0 (Sum.inr j)) ≠ 0) :
    symC z x = consS ⟨a, if ∏ i, x (e0 (Sum.inl i)) = 1 then Sign.plus else Sign.minus⟩
      (symC (fun j => z (e0 (Sum.inr j)) - 1) (fun j => x (e0 (Sum.inr j)))) := by
  funext k
  have hsum : ∀ f : Fin n → ℕ, ∑ i, f i = ∑ i, f (e0 (Sum.inl i)) + ∑ j, f (e0 (Sum.inr j)) := by
    intro f
    rw [← Equiv.sum_comp e0 f, Fintype.sum_sum_type]
  have hprod : ∀ f : Fin n → ℤˣ, ∏ i, f i = (∏ i, f (e0 (Sum.inl i))) * ∏ j, f (e0 (Sum.inr j)) := by
    intro f
    rw [← Equiv.prod_comp e0 f, Fintype.prod_sum_type]
  cases k with
  | zero =>
    simp only [symC, consS_zero]
    congr 1
    · rw [hsum]
      simp [hz0, hz1]
    · have : ∏ i, (if z i = 0 then x i else 1) = ∏ i, x (e0 (Sum.inl i)) := by
        rw [hprod]
        simp [hz0, hz1]
      rw [this]
  | succ k =>
    simp only [symC, consS_succ]
    have hkz : ∀ j, (z (e0 (Sum.inr j)) = k + 1 ↔ z (e0 (Sum.inr j)) - 1 = k) := by
      intro j; have := hz1 j; omega
    congr 1
    · rw [hsum]
      simp [hz0, hkz]
    · have : ∏ i, (if z i = k + 1 then x i else 1) = ∏ j, (if z (e0 (Sum.inr j)) - 1 = k then
          x (e0 (Sum.inr j)) else 1) := by
        rw [hprod]
        simp [hz0, hkz]
      rw [this]

theorem symC_all_pos {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) (hz : ∀ i, 1 ≤ z i) :
    symC z x = consS OddFactor.trivial (symC (fun i => z i - 1) x) := by
  funext k
  cases k with
  | zero =>
    simp only [symC, consS_zero]
    have h : ∀ i, z i ≠ 0 := fun i => by have := hz i; omega
    simp [h, OddFactor.trivial]
  | succ k =>
    simp only [symC, consS_succ]
    have hkz : ∀ i, (z i = k + 1 ↔ z i - 1 = k) := by
      intro i; have := hz i; omega
    simp [hkz]


include hπ h2 hcU hc he in
/-- **The density of a diagonal form splits** into the unimodular part (the entries with $z_i = 0$, a family of $a$
indices) and $\pi$ times a diagonal form with exponents lowered by one:
$\alpha(D(z,x)) = P_q(a,\varepsilon)\,q^{b(b+1)/2}\,\alpha(D(z',x'))$. -/
theorem loc_split {a b : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin (b + a)) (z : Fin (b + a) → ℕ) (x : Fin (b + a) → ℤˣ)
    (hz0 : ∀ i, z (e0 (Sum.inl i)) = 0) (hz1 : ∀ j, z (e0 (Sum.inr j)) ≠ 0) :
    localDensityForm (QuadForm.diag (diagVec π c z x)) (QuadForm.diag (diagVec π c z x)) π =
      Pq (q R) e a (if ∏ i, x (e0 (Sum.inl i)) = 1 then Sign.plus else Sign.minus) *
        ((q R : ℝ) ^ (b * (b + 1) / 2) *
          localDensityForm (QuadForm.diag (diagVec π c (fun j => z (e0 (Sum.inr j)) - 1)
            (fun j => x (e0 (Sum.inr j)))))
            (QuadForm.diag (diagVec π c (fun j => z (e0 (Sum.inr j)) - 1) (fun j => x (e0 (Sum.inr j))))) π) := by
  set d := diagVec π c z x with hd
  set σ : Equiv.Perm (Fin (b + a)) := (psi a b).symm.trans e0 with hσ
  set u : Fin a → R := fun i => repR c (x (e0 (Sum.inl i))) with hu
  set t : Fin b → R := fun j => d (e0 (Sum.inr j)) with ht
  have hiso := Siegel.Kneser.isometricGL_of_isGLEquiv (Hanke2005.isGLEquiv_diag_perm d σ)
  have hdσ : d ∘ σ = Hanke2005.cseq t a u := by
    funext j
    obtain ⟨s, rfl⟩ := (psi a b).surjective j
    rw [cseq_psi]
    rcases s with i | k
    · simp only [Function.comp, hσ, Equiv.trans_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      simp [hd, diagVec, hz0, hu]
    · simp only [Function.comp, hσ, Equiv.trans_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      rfl
  rw [localDensityForm_congr_left hiso, localDensityForm_congr_right _ hiso, hdσ,
    ← Hanke2005.unitSum_diag t a u]
  have hTnd : (QuadForm.diag t).Nondegenerate := by
    have h20 : (2 : R) ≠ 0 := (dvr_isUnit_of_not_dvd hπ h2).ne_zero
    unfold QuadForm.Nondegenerate
    rw [det_hessian_diag]
    refine mul_ne_zero (pow_ne_zero _ h20) (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    exact mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (isUnit_repR hcU _).ne_zero
  have ht1 : ∀ j, t j = π * (π ^ (z (e0 (Sum.inr j)) - 1) * repR c (x (e0 (Sum.inr j)))) := by
    intro j
    simp only [ht, hd, diagVec]
    have := hz1 j
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 this)]
  have hT : ∀ i j, ∃ c', (QuadForm.diag t).coeff i j = π * c' := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact ⟨π ^ (z (e0 (Sum.inr i)) - 1) * repR c (x (e0 (Sum.inr i))), by simp [QuadForm.diag, ht1]⟩
    · exact ⟨0, by simp [QuadForm.diag, hij]⟩
  have hunit : ∀ i, IsUnit (u i) := fun i => isUnit_repR hcU _
  rw [Hanke2005.localDensityForm_unitSum hπ h2 (QuadForm.diag t) hTnd hT a u hunit]
  rw [loc_unit_diag hπ h2 hcU hc he (fun i => x (e0 (Sum.inl i)))]
  congr 1
  rw [Tamagawa.localDensityForm_smul_pi hπ (Q := QuadForm.diag (diagVec π c (fun j => z (e0 (Sum.inr j)) - 1)
    (fun j => x (e0 (Sum.inr j))))) (Q' := QuadForm.diag t) (nondeg_diagVec hπ h2 hcU _ _)]
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [QuadForm.diag, ht1, diagVec]
  · simp [QuadForm.diag, hij]

theorem wtC_triv_from_zero (M : ℕ → Sign → ℝ) (a : ℕ → ℝ) (hM : M 0 Sign.plus = 1) (ha : a 0 = 1)
    {σ : OddSymbol} (h : TrivFrom σ 0) : wtC M a σ = 1 := by
  unfold wtC
  rw [(stable_wtN M a hM ha).cut_eq h, wtN_zero]

include hπ h2 hcU hc he in
/-- **The self-density of a diagonal genus is the inverse weight of its symbol**:
$\alpha_\pi(D(z,x), D(z,x)) = \mathrm{wt}(\operatorname{symC}(z,x))^{-1}$ (every rank $n$). -/
theorem loc_diag : ∀ (m n : ℕ) (z : Fin n → ℕ) (x : Fin n → ℤˣ), n + ∑ i, z i ≤ m →
    localDensityForm (QuadForm.diag (diagVec π c z x)) (QuadForm.diag (diagVec π c z x)) π =
      (wtC (Mq (q R) e) (aq (q R)) (symC z x))⁻¹ := by
  have hM := Mq_zero (q R) e
  have ha := aq_zero (q R)
  intro m
  induction m with
  | zero =>
    intro n z x hm
    have hn : n = 0 := by omega
    subst hn
    rw [Hanke2005.localDensityForm_zero]
    have : symC z x = triv := by
      funext k; simp [symC, triv, OddFactor.trivial]
    rw [this, wtC_triv_from_zero _ _ hM ha triv_trivFrom]; simp
  | succ m ih =>
    intro n z x hm
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Hanke2005.localDensityForm_zero]
      have : symC z x = triv := by
        funext k; simp [symC, triv, OddFactor.trivial]
      rw [this, wtC_triv_from_zero _ _ hM ha triv_trivFrom]; simp
    by_cases hz : ∃ i, z i = 0
    · -- some unit entry
      obtain ⟨a, b, rfl, e0, hz0, hz1⟩ := exists_split z
      have ha1 : 1 ≤ a := by
        obtain ⟨i, hi⟩ := hz
        obtain ⟨s, rfl⟩ := e0.surjective i
        rcases s with i' | j
        · exact Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact i'.elim0)
        · exact absurd hi (hz1 j)
      have hsum : ∑ j, (z (e0 (Sum.inr j)) - 1) + b ≤ ∑ i, z i := by
        have h1 : ∑ i, z i = ∑ i, z (e0 (Sum.inl i)) + ∑ j, z (e0 (Sum.inr j)) := by
          rw [← Equiv.sum_comp e0 z, Fintype.sum_sum_type]
        have h2' : ∑ j, (z (e0 (Sum.inr j)) - 1) + b = ∑ j, z (e0 (Sum.inr j)) := by
          have : ∀ j, z (e0 (Sum.inr j)) - 1 + 1 = z (e0 (Sum.inr j)) := fun j => by
            have := hz1 j; omega
          calc ∑ j, (z (e0 (Sum.inr j)) - 1) + b = ∑ j, (z (e0 (Sum.inr j)) - 1 + 1) := by
                rw [Finset.sum_add_distrib]; simp
            _ = _ := Finset.sum_congr rfl fun j _ => this j
        omega
      rw [loc_split hπ h2 hcU hc he e0 z x hz0 hz1,
        ih b _ _ (by omega), symC_split e0 z x hz0 hz1,
        wtC_cons _ _ hM ha (finSupp_symC _ _), rkC_symC]
      simp only [mul_inv, Mq, inv_inv, aq]
      ring
    · -- all exponents positive
      have hall : ∀ i, 1 ≤ z i := fun i => by
        by_contra h; exact hz ⟨i, by omega⟩
      have hsum : ∑ i, (z i - 1) + n = ∑ i, z i := by
        calc ∑ i, (z i - 1) + n = ∑ i, (z i - 1 + 1) := by
              rw [Finset.sum_add_distrib]; simp
          _ = _ := Finset.sum_congr rfl fun i _ => by have := hall i; omega
      have hQ := Tamagawa.localDensityForm_smul_pi hπ
        (Q := QuadForm.diag (diagVec π c (fun i => z i - 1) x)) (Q' := QuadForm.diag (diagVec π c z x))
        (nondeg_diagVec hπ h2 hcU _ _) (by
          intro i j
          by_cases hij : i = j
          · subst hij
            simp only [QuadForm.diag, Matrix.diagonal_apply, if_true, diagVec]
            rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hall i)]
          · simp [QuadForm.diag, hij])
      rw [hQ, ih n _ x (by omega), symC_all_pos z x hall, wtC_cons _ _ hM ha (finSupp_symC _ _), rkC_symC]
      simp only [mul_inv, Mq_zero, OddFactor.trivial, one_mul, aq, inv_inv]



include hπ h2 hcU hc he in
/-- **Stage 1 (closed form of the density of a diagonal genus).** For $R$ a discrete valuation ring with finite
residue field $\mathbb F$ and uniformizer $\pi \nmid 2$, $c \in R^\times$ with $\chi(\bar c) = -1$, $e = \chi(-1)$,
$z : \mathrm{Fin}\,n \to \mathbb N$, $x : \mathrm{Fin}\,n \to \{\pm1\}$: the self-density of
$\operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$ is the inverse weight of its symbol. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (density of a diagonal genus, p ∤ 2, every number field, every n)"]
theorem loc_diag_eq {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    localDensityForm (QuadForm.diag (diagVec π c z x)) (QuadForm.diag (diagVec π c z x)) π =
      (wtC (Mq (q R) e) (aq (q R)) (symC z x))⁻¹ :=
  loc_diag hπ h2 hcU hc he (n + ∑ i, z i) n z x le_rfl

end Split

end Gen

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.loc_diag_eq
