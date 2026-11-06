/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicInjective
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.LocalDensity.DyadicArf

/-!
# Paper 6, Theorem 5.4 at $\mathfrak p \nmid 2$ of a number field: the genera of diagonal forms

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24 (O'Meara 92:2).

**This file (generic part).**  Let $R$ be a complete discrete valuation ring with finite residue field and uniformizer
$\pi \nmid 2$, $c \in R^\times$ a unit with nonsquare residue (`chiR c = -1`), and
$D(z,x) = \operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$.

* `isometricGL_cseq`: block sums of $\mathrm{GL}$-equivalent diagonal forms are $\mathrm{GL}$-equivalent;
* `isometricGL_of_symC_eq` (the converse of `symC_eq_of_isometricGL`): if $\mathrm{symC}(z,x) = \mathrm{symC}(z',x')$
  then $D(z,x) \cong D(z',x')$.  Proof by induction as for the density: if all $z_i \ge 1$ divide by $\pi$; otherwise
  split off the unimodular constituents (equivalent by the classification of unimodular forms,
  `Lattices.Nbr.isometricGL_of_unimodular_dvr` = O'Meara 92:1, because the products of their signs agree and a unit whose
  residue has quadratic character $1$ is a square by Hensel) and apply induction to the rest;
* `exists_rep_diag`: every unit diagonal form $\operatorname{diag}(\pi^{\nu_i}u_i)$ is $\mathrm{GL}$-equivalent to some
  $D(\nu, x)$ (Hensel again).

Indices are 0-based.
-/

open Finset Matrix

namespace QuadFormsKB.Hanke2011Structure.RatND

open QuadFormsKB QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Hanke2011Structure.RatOdd
  QuadFormsKB.ConwaySloane QuadFormsKB.Odd7 QuadFormsKB.Siegel

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

section Block

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]

theorem isometricGL_diag_smul {n : ℕ} (d d' : Fin n → R) (p : R) (h : IsometricGL (QuadForm.diag d) (QuadForm.diag d')) :
    IsometricGL (QuadForm.diag fun i => p * d i) (QuadForm.diag fun i => p * d' i) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun y => ?_⟩
  have h1 := hg y
  rw [Kneser.eval_diag, Kneser.eval_diag] at h1
  rw [Kneser.eval_diag, Kneser.eval_diag]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h1]

theorem eval_cseq {a b : ℕ} (t : Fin b → R) (u : Fin a → R) (y : Fin (b + a) → R) :
    (QuadForm.diag (Hanke2005.cseq t a u)).eval y =
      (QuadForm.diag u).eval (fun i => y (psi a b (Sum.inl i))) +
        (QuadForm.diag t).eval (fun k => y (psi a b (Sum.inr k))) := by
  rw [Kneser.eval_diag, Kneser.eval_diag, Kneser.eval_diag, ← Equiv.sum_comp (psi a b), Fintype.sum_sum_type]
  have h1 : ∀ i, Hanke2005.cseq t a u (psi a b (Sum.inl i)) = u i := fun i => by
    simpa using cseq_psi t u (Sum.inl i)
  have h2 : ∀ k, Hanke2005.cseq t a u (psi a b (Sum.inr k)) = t k := fun k => by
    simpa using cseq_psi t u (Sum.inr k)
  simp only [h1, h2]

/-- **Block sums of $\mathrm{GL}$-equivalent diagonal forms are $\mathrm{GL}$-equivalent.** -/
theorem isometricGL_cseq {a b : ℕ} (t t' : Fin b → R) (u u' : Fin a → R)
    (hT : IsometricGL (QuadForm.diag t) (QuadForm.diag t'))
    (hU : IsometricGL (QuadForm.diag u) (QuadForm.diag u')) :
    IsometricGL (QuadForm.diag (Hanke2005.cseq t a u)) (QuadForm.diag (Hanke2005.cseq t' a u')) := by
  obtain ⟨gT, hgT⟩ := hT
  obtain ⟨gU, hgU⟩ := hU
  let G0 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R := Matrix.fromBlocks gU.val 0 0 gT.val
  let G : Matrix (Fin (b + a)) (Fin (b + a)) R := G0.submatrix (psi a b).symm (psi a b).symm
  have hdet : IsUnit G.det := by
    have e1 : G.det = G0.det := Matrix.det_submatrix_equiv_self (psi a b).symm G0
    have e2 : G0.det = gU.val.det * gT.val.det := by
      simp only [G0]
      exact Matrix.det_fromBlocks_zero₂₁ _ _ _
    rw [e1, e2]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 gU.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 gT.isUnit)
  refine ⟨((Matrix.isUnit_iff_isUnit_det G).2 hdet).unit, fun y => ?_⟩
  rw [IsUnit.unit_spec, eval_cseq, eval_cseq]
  have hmv : (fun j => (G *ᵥ y) j) ∘ (psi a b) = G0 *ᵥ (y ∘ psi a b) := by
    have := Matrix.submatrix_mulVec_equiv G0 y (psi a b).symm (psi a b).symm
    simp only [G] at *
    rw [this]
    funext s
    simp
  have hy : y ∘ psi a b = Sum.elim (fun i => y (psi a b (Sum.inl i))) (fun k => y (psi a b (Sum.inr k))) := by
    funext s; rcases s with i | k <;> rfl
  have hG0 : G0 *ᵥ Sum.elim (fun i => y (psi a b (Sum.inl i))) (fun k => y (psi a b (Sum.inr k))) =
      Sum.elim (gU.val *ᵥ (fun i => y (psi a b (Sum.inl i)))) (gT.val *ᵥ (fun k => y (psi a b (Sum.inr k)))) := by
    simp only [G0, Matrix.fromBlocks_mulVec]
    simp
  rw [hy, hG0] at hmv
  have h1 : (fun i => (G *ᵥ y) (psi a b (Sum.inl i))) = gU.val *ᵥ (fun i => y (psi a b (Sum.inl i))) := by
    funext i
    have := congrFun hmv (Sum.inl i)
    simpa using this
  have h2 : (fun k => (G *ᵥ y) (psi a b (Sum.inr k))) = gT.val *ᵥ (fun k => y (psi a b (Sum.inr k))) := by
    funext k
    have := congrFun hmv (Sum.inr k)
    simpa using this
  rw [h1, h2, hgU, hgT]

end Block

/-! ### Equal symbols give equivalent forms -/

section Conv

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) {c : R} (hcU : IsUnit c) (hc : chiR c = -1)

local notation "res" => IsLocalRing.residue R

include hπ h2 in
/-- **Units with a square product differ by a square**: if $P, P'$ are units with $\chi(\overline{PP'}) = 1$ then
$P' = w^2P$ for a unit $w$ (Hensel). -/
theorem unit_sq_rel {P P' : R} (hP : IsUnit P) (hP' : IsUnit P')
    (h : quadraticChar (IsLocalRing.ResidueField R) (res (P * P')) = 1) :
    ∃ w : R, IsUnit w ∧ P' = w ^ 2 * P := by
  have hsq : IsSquare (P * P') :=
    (isSquare_iff_quadraticChar_residue hπ h2 (dvr_not_dvd_of_isUnit hπ (hP.mul hP'))).2 h
  obtain ⟨s, hs⟩ := hsq
  have hsU : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ hP.mul hP')
  obtain ⟨Pu, rfl⟩ := hP
  refine ⟨s * ↑Pu⁻¹, hsU.mul (Units.isUnit _), ?_⟩
  have hI : (↑Pu⁻¹ : R) * ↑Pu = 1 := Units.inv_mul Pu
  calc P' = (↑Pu * P') * ↑Pu⁻¹ := by
        rw [mul_comm (↑Pu : R) P', mul_assoc, mul_comm (↑Pu : R), hI, mul_one]
    _ = (s * s) * ↑Pu⁻¹ := by rw [hs]
    _ = (s * ↑Pu⁻¹) ^ 2 * ↑Pu := by
        calc (s * s) * ↑Pu⁻¹ = (s * s) * (↑Pu⁻¹ * (↑Pu⁻¹ * ↑Pu)) := by rw [hI, mul_one]
          _ = _ := by ring

include hπ h2 hcU hc in
/-- **Unimodular diagonal forms with the same sign product are equivalent.** -/
theorem isometricGL_unit_diag {a : ℕ} (x x' : Fin a → ℤˣ) (hprod : ∏ i, x i = ∏ i, x' i) :
    IsometricGL (QuadForm.diag fun i => repR c (x i)) (QuadForm.diag fun i => repR c (x' i)) := by
  have hu : ∀ i, IsUnit (repR c (x i)) := fun i => isUnit_repR hcU _
  have hu' : ∀ i, IsUnit (repR c (x' i)) := fun i => isUnit_repR hcU _
  have hP : IsUnit (∏ i, repR c (x i)) := IsUnit.prod_iff.2 fun i _ => hu i
  have hP' : IsUnit (∏ i, repR c (x' i)) := IsUnit.prod_iff.2 fun i _ => hu' i
  have hchi : quadraticChar (IsLocalRing.ResidueField R)
      (res ((∏ i, repR c (x i)) * ∏ i, repR c (x' i))) = 1 := by
    have e : quadraticChar (IsLocalRing.ResidueField R) (res ((∏ i, repR c (x i)) * ∏ i, repR c (x' i))) =
        chiR (∏ i, repR c (x i)) * chiR (∏ i, repR c (x' i)) := by
      unfold chiR; rw [map_mul, map_mul]
    rw [e, chiR_prod, chiR_prod]
    simp only [chiR_repR hc]
    have : (∏ i, ((x i : ℤˣ) : ℤ)) = (((∏ i, x i : ℤˣ)) : ℤ) := by push_cast; rfl
    have this' : (∏ i, ((x' i : ℤˣ) : ℤ)) = (((∏ i, x' i : ℤˣ)) : ℤ) := by push_cast; rfl
    rw [this, this', ← hprod, ← Units.val_mul]
    simp
  obtain ⟨w, hw, hwe⟩ := unit_sq_rel hπ h2 hP hP' hchi
  exact Lattices.Nbr.isometricGL_of_unimodular_dvr hπ h2 (QuadForm.diag fun i => repR c (x i))
    (QuadForm.diag fun i => repR c (x' i)) (not_dvd_hessian_diag_rep hπ h2 hcU x) hw (by
      rw [det_hessian_diag, det_hessian_diag, hwe]; ring)

include hπ h2 hcU in
/-- **A diagonal form with the unit entries split off is equivalent to the block form** $\langle u\rangle\perp\pi W$. -/
theorem isometricGL_split {a b : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin (b + a)) (z : Fin (b + a) → ℕ)
    (x : Fin (b + a) → ℤˣ) (hz0 : ∀ i, z (e0 (Sum.inl i)) = 0) (hz1 : ∀ j, z (e0 (Sum.inr j)) ≠ 0) :
    IsometricGL (QuadForm.diag (diagVec π c z x))
      (QuadForm.diag (Hanke2005.cseq
        (fun j => π * diagVec π c (fun j => z (e0 (Sum.inr j)) - 1) (fun j => x (e0 (Sum.inr j))) j) a
        (fun i => repR c (x (e0 (Sum.inl i)))))) := by
  set d := diagVec π c z x with hd
  set σ : Equiv.Perm (Fin (b + a)) := (psi a b).symm.trans e0 with hσ
  have hiso := Kneser.isometricGL_of_isGLEquiv (Hanke2005.isGLEquiv_diag_perm d σ)
  have hdσ : d ∘ σ = Hanke2005.cseq
      (fun j => π * diagVec π c (fun j => z (e0 (Sum.inr j)) - 1) (fun j => x (e0 (Sum.inr j))) j) a
      (fun i => repR c (x (e0 (Sum.inl i)))) := by
    funext j
    obtain ⟨s, rfl⟩ := (psi a b).surjective j
    rw [cseq_psi]
    rcases s with i | k
    · simp only [Function.comp, hσ, Equiv.trans_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      simp [hd, diagVec, hz0]
    · simp only [Function.comp, hσ, Equiv.trans_apply, Equiv.symm_apply_apply, Sum.elim_inr]
      simp only [hd, diagVec]
      have := hz1 k
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 this)]
  rw [← hdσ]
  exact hiso

include hπ h2 hcU hc in
/-- **Equal symbols give equivalent diagonal forms** (the converse of `symC_eq_of_isometricGL`; O'Meara 92:2,
sufficiency, $\mathfrak p \nmid 2$): if $\mathrm{symC}(z,x) = \mathrm{symC}(z',x')$ then $D(z,x) \cong D(z',x')$. -/
@[kb "omeara1963" "§92, 92:2, p. 247 (same Jordan type and discriminants give isometric lattices, p ∤ 2)"]
theorem isometricGL_of_symC_eq : ∀ (m n : ℕ) (z z' : Fin n → ℕ) (x x' : Fin n → ℤˣ), n + ∑ i, z i ≤ m →
    symC z x = symC z' x' →
      IsometricGL (QuadForm.diag (diagVec π c z x)) (QuadForm.diag (diagVec π c z' x')) := by
  intro m
  induction m with
  | zero =>
    intro n z z' x x' hm _
    have hn : n = 0 := by omega
    subst hn
    exact Kneser.isometricGL_zero _ _
  | succ m ih =>
    intro n z z' x x' hm hsym
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Kneser.isometricGL_zero _ _
    by_cases hz : ∃ i, z i = 0
    · obtain ⟨a, b, rfl, e0, hz0, hz1⟩ := exists_split z
      obtain ⟨a', b', hn', e0', hz0', hz1'⟩ := exists_split z'
      rw [symC_split e0 z x hz0 hz1] at hsym
      rw [symC_split e0' z' x' hz0' hz1'] at hsym
      obtain ⟨hf, hrest⟩ := consS_inj hsym
      simp only [OddFactor.mk.injEq] at hf
      obtain ⟨rfl, hsign⟩ := hf
      have hb : b = b' := by omega
      subst hb
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
      have hprod : ∏ i, x (e0 (Sum.inl i)) = ∏ i, x' (e0' (Sum.inl i)) := by
        revert hsign
        rcases Int.units_eq_one_or (∏ i, x (e0 (Sum.inl i))) with h | h <;>
          rcases Int.units_eq_one_or (∏ i, x' (e0' (Sum.inl i))) with h' | h' <;> simp [h, h']
      have hT := isometricGL_diag_smul _ _ π
        (ih b _ _ (fun j => x (e0 (Sum.inr j))) (fun j => x' (e0' (Sum.inr j))) (by omega) hrest)
      have hU := isometricGL_unit_diag hπ h2 hcU hc (fun i => x (e0 (Sum.inl i)))
        (fun i => x' (e0' (Sum.inl i))) hprod
      have hB := isometricGL_cseq _ _ _ _ hT hU
      exact (isometricGL_split hπ h2 hcU e0 z x hz0 hz1).trans
        (hB.trans (isometricGL_split hπ h2 hcU e0' z' x' hz0' hz1').symm)
    · have hall : ∀ i, 1 ≤ z i := fun i => by
        by_contra h; exact hz ⟨i, by omega⟩
      have hall' : ∀ i, 1 ≤ z' i := fun i => by
        by_contra h
        have h0 : z' i = 0 := by omega
        have e1 : (symC z x 0).dim = 0 := by
          simp only [symC]
          exact Finset.sum_eq_zero fun j _ => by simp [Nat.pos_iff_ne_zero.1 (hall j)]
        have e2 : (symC z' x' 0).dim ≥ 1 := by
          simp only [symC]
          calc 1 = (if z' i = 0 then 1 else 0) := by simp [h0]
            _ ≤ ∑ j, (if z' j = 0 then 1 else 0) :=
              Finset.single_le_sum (f := fun j => if z' j = 0 then 1 else 0) (fun j _ => Nat.zero_le _)
                (Finset.mem_univ i)
        rw [hsym] at e1
        omega
      rw [symC_all_pos z x hall, symC_all_pos z' x' hall'] at hsym
      have hrest := (consS_inj hsym).2
      have hsum : ∑ i, (z i - 1) + n = ∑ i, z i := by
        calc ∑ i, (z i - 1) + n = ∑ i, (z i - 1 + 1) := by
              rw [Finset.sum_add_distrib]; simp
          _ = _ := Finset.sum_congr rfl fun i _ => by have := hall i; omega
      have hI := isometricGL_diag_smul _ _ π
        (ih n (fun i => z i - 1) (fun i => z' i - 1) x x' (by omega) hrest)
      have e1 : (fun i => π * diagVec π c (fun i => z i - 1) x i) = diagVec π c z x := by
        funext i
        simp only [diagVec]
        rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hall i)]
      have e2 : (fun i => π * diagVec π c (fun i => z' i - 1) x' i) = diagVec π c z' x' := by
        funext i
        simp only [diagVec]
        rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hall' i)]
      rw [e1, e2] at hI
      exact hI

include hπ h2 hcU hc in
/-- **Every unit is a square times a representative**: $u = w^2\operatorname{rep}(x)$ with $x = \chi(\bar u)$. -/
theorem exists_rep_unit {u : R} (hu : IsUnit u) : ∃ x : ℤˣ, ∃ w : R, IsUnit w ∧ u = w ^ 2 * repR c x := by
  have hres : res u ≠ 0 := (hu.map _).ne_zero
  rcases quadraticChar_dichotomy hres with h | h
  · obtain ⟨w, hw, hwe⟩ := unit_sq_rel hπ h2 (P := 1) (P' := u) isUnit_one hu (by
      rw [one_mul]; exact h)
    exact ⟨1, w, hw, by rw [hwe, repR]; simp⟩
  · obtain ⟨w, hw, hwe⟩ := unit_sq_rel hπ h2 (P := c) (P' := u) hcU hu (by
      have : quadraticChar (IsLocalRing.ResidueField R) (res (c * u)) = chiR c * quadraticChar
          (IsLocalRing.ResidueField R) (res u) := by unfold chiR; rw [map_mul, map_mul]
      rw [this, hc, h]; norm_num)
    exact ⟨-1, w, hw, by rw [hwe, repR]; simp⟩

include hπ h2 hcU hc in
/-- **Every unit diagonal form $\langle\pi^{\nu_i}u_i\rangle$ is $\mathrm{GL}$-equivalent to some $D(\nu,x)$.** -/
theorem exists_rep_diag {n : ℕ} (ν : Fin n → ℕ) (u : Fin n → R) (hu : ∀ i, IsUnit (u i)) :
    ∃ x : Fin n → ℤˣ, IsometricGL (QuadForm.diag fun i => π ^ ν i * u i) (QuadForm.diag (diagVec π c ν x)) := by
  choose x w hw hxe using fun i => exists_rep_unit hπ h2 hcU hc (hu i)
  refine ⟨x, ?_⟩
  have hdet : IsUnit (Matrix.diagonal w).det := by
    rw [Matrix.det_diagonal]; exact IsUnit.prod_iff.2 fun i _ => hw i
  refine IsometricGL.symm ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, fun y => ?_⟩
  rw [IsUnit.unit_spec, Kneser.eval_diag, Kneser.eval_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [diagVec, Matrix.mulVec_diagonal, hxe i]
  ring

end Conv

/-! ### Generic complements: a nonsquare unit, the sign of a unit, determinant classes -/

section Misc

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)

local notation "res" => IsLocalRing.residue R

include hπ h2 in
/-- **There is a unit with nonsquare residue** ($\pi \nmid 2$). -/
theorem exists_nonres : ∃ c : R, IsUnit c ∧ chiR c = -1 := by
  have hF := ringChar_residueField_ne_two hπ h2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective a
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hcπ : ¬ π ∣ c := fun h => ha0 (by rw [← hc]; exact (residue_eq_zero_iff_dvd hπ c).2 h)
  refine ⟨c, dvr_isUnit_of_not_dvd hπ hcπ, ?_⟩
  unfold chiR
  rw [hc]
  exact quadraticChar_neg_one_iff_not_isSquare.2 ha

variable (R) in
/-- The sign of $r \in R$: $+1$ if $\chi(\bar r) = 1$, else $-1$ (for a unit, $\chi(\bar r)$ as a unit of $\mathbb Z$). -/
def sgn (r : R) : ℤˣ := if chiR r = 1 then 1 else -1

theorem sgn_val {r : R} (hr : IsUnit r) : ((sgn R r : ℤˣ) : ℤ) = chiR r := by
  unfold sgn
  have hres : res r ≠ 0 := (hr.map _).ne_zero
  rcases quadraticChar_dichotomy hres with h | h
  · have : chiR r = 1 := h
    simp [this]
  · have : chiR r = -1 := h
    simp [this]

theorem sgn_mul {r s : R} (hr : IsUnit r) (hs : IsUnit s) : sgn R (r * s) = sgn R r * sgn R s := by
  apply Units.ext
  rw [Units.val_mul, sgn_val (hr.mul hs), sgn_val hr, sgn_val hs, chiR_mul]

theorem sgn_pow {r : R} (hr : IsUnit r) (k : ℕ) : sgn R (r ^ k) = sgn R r ^ k := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sgn_val (hr.pow k), sgn_val hr]
  unfold chiR
  rw [map_pow, map_pow]

include hπ in
theorem pow_mul_unit_eq {a b : ℕ} {u u' : R} (hu : IsUnit u) (hu' : IsUnit u') (h : π ^ a * u = π ^ b * u') :
    a = b ∧ u = u' := by
  have key : ∀ {a b : ℕ} {u u' : R}, IsUnit u → IsUnit u' → π ^ a * u = π ^ b * u' → a ≤ b → a = b ∧ u = u' := by
    intro a b u u' hu hu' h hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have h' : π ^ a * u = π ^ a * (π ^ d * u') := by rw [h, pow_add]; ring
    have h'' := mul_left_cancel₀ (pow_ne_zero a hπ.ne_zero) h'
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at h''; exact ⟨by simp, h''⟩
    · exfalso
      have : π ∣ u := by
        rw [h'', ← Nat.succ_pred_eq_of_pos hd, pow_succ]
        exact dvd_mul_of_dvd_left (dvd_mul_left π _) u'
      exact hπ.not_isUnit (isUnit_of_dvd_unit this hu)
  rcases le_total a b with hab | hab
  · exact key hu hu' h hab
  · obtain ⟨h1, h2⟩ := key hu' hu h.symm hab
    exact ⟨h1.symm, h2.symm⟩

end Misc

end

end QuadFormsKB.Hanke2011Structure.RatND
