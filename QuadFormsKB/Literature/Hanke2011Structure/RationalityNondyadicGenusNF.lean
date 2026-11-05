/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicGenus
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37

/-!
# Paper 6, Theorem 5.4 at $\mathfrak p \nmid 2$ of a number field: the invariants of a diagonal genus

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, proof, p. 24.

Let $F$ be a number field, $\mathfrak p$ (`v`) a finite prime with $2 \notin \mathfrak p$, $\mathcal O_{\mathfrak p}$
the completion's integers, $\pi$ = `NF.π v`, $c \in \mathcal O_{\mathfrak p}^\times$ with nonsquare residue.  For
$z : \mathrm{Fin}\,n \to \mathbb N$, $x : \mathrm{Fin}\,n \to \{\pm1\}$ the local genus of
$D(z,x) = \operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$ is `genND v c z x`.  This file reads off, for the genus
`genND v c z x` (the analogues of `RatOdd.genZ_eq_iff`, `exists_genZ`, `det_genZ_iff`, `prim_genZ_iff`,
`hasse_genZ`, `beta_genZ`):

* `genND_eq_iff`: `genND z x = genND z' x'` iff `symC z x = symC z' x'` (the stages 3 and 2 of the generic files);
* `exists_genND`: every nondegenerate local genus is some `genND z x` (diagonalization with powers of $\pi$);
* `prim_genND_iff`: primitive iff some $z_i = 0$;
* `det_genND_iff`: $\det_H = [\pi^\nu w]$ ($w$ a unit) iff $\sum z_i = \nu$ and
  $\prod x_i = \chi(2)^n\chi(w)$ (squareclass computation in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$);
* `hasse_genND`: the Hasse invariant is `hasseZ e z x`, $e = \chi(-1)$, because the Hilbert symbol at a nondyadic prime
  of a number field is $(\pi^au, \pi^bu')_{\mathfrak p} = (\chi(-1))^{ab}\chi(u)^b\chi(u')^a$ (`hilb_pair`, from
  bimultiplicativity, $(u,u')=1$ for units and $(\pi,u) = \chi(u)$);
* `beta_genND`: Hanke's density is $\beta = (2\,\mathrm{wt}(\operatorname{symC}(z,x)))^{-1}$.

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

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem not_dvd_two_nf (hv : (2 : 𝓞 F) ∉ v.asIdeal) : ¬ LocalDensity.NF.π v ∣ (2 : 𝔬) := by
  have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
  rwa [pow_one, map_ofNat] at this

/-- **The local genus of the diagonal form** $D(z,x) = \operatorname{diag}(\pi^{z_i}\operatorname{rep}(x_i))$. -/
def genND (c : 𝔬) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) : LocGenus v n :=
  LocGenus.mk (QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x))

variable {v}

theorem genND_eq_iff (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (z z' : Fin n → ℕ) (x x' : Fin n → ℤˣ) :
    genND v c z x = genND v c z' x' ↔ symC z x = symC z' x' := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  unfold genND
  rw [LocGenus.mk_eq_mk]
  constructor
  · exact symC_eq_of_isometricGL hπ h2 hcU hc
  · exact isometricGL_of_symC_eq hπ h2 hcU hc (n + ∑ i, z i) n z z' x x' le_rfl

/-- **Every nondegenerate local genus is the genus of a diagonal form** $D(z,x)$. -/
theorem exists_genND (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (G : LocGenus v n) (hN : G.Nondeg) : ∃ (z : Fin n → ℕ) (x : Fin n → ℤˣ), G = genND v c z x := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  induction G using Quotient.inductionOn with
  | _ T =>
  have hT : T.Nondegenerate := (LocGenus.nondeg_mk T).1 hN
  obtain ⟨ν, u, hu, hE⟩ := Hanke2005.exists_diag_pi T hT hπ h2
  obtain ⟨x, hx⟩ := exists_rep_diag hπ h2 hcU hc ν u hu
  refine ⟨ν, x, ?_⟩
  unfold genND
  show LocGenus.mk T = LocGenus.mk _
  rw [LocGenus.mk_eq_mk]
  exact (Kneser.isometricGL_of_isGLEquiv hE).trans hx

theorem nondeg_genND (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) : (genND v c z x).Nondeg := by
  unfold genND
  rw [LocGenus.nondeg_mk]
  exact nondeg_diagVec (LocalDensity.NF.irreducible_π v) (not_dvd_two_nf v hv) hcU z x

theorem prim_genND_iff (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) : (genND v c z x).Prim ↔ ∃ i, z i = 0 := by
  have hπ := LocalDensity.NF.irreducible_π v
  unfold genND
  rw [LocGenus.prim_mk]
  unfold IsPrimitiveForm
  have hcoef : ∀ i j, (QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x)).coeff i j =
      if i = j then diagVec (LocalDensity.NF.π v) c z x i else 0 := by
    intro i j
    simp [QuadForm.diag, Matrix.diagonal_apply]
  constructor
  · intro hP
    by_contra hnot
    push_neg at hnot
    have hle : Ideal.span (Set.range fun q : Fin n × Fin n =>
          (QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x)).coeff q.1 q.2) ≤
        Ideal.span {LocalDensity.NF.π v} := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      beta_reduce
      rw [hcoef]
      rw [SetLike.mem_coe, Ideal.mem_span_singleton]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        exact dvd_mul_of_dvd_left (dvd_pow_self _ (hnot i)) _
      · rw [if_neg hij]; exact dvd_zero _
    rw [hP, top_le_iff, Ideal.span_singleton_eq_top] at hle
    exact hπ.not_isUnit hle
  · rintro ⟨i, hi⟩
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨(i, i), rfl⟩) ?_
    show IsUnit ((QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x)).coeff i i)
    rw [hcoef, if_pos rfl]
    simp only [diagVec, hi, pow_zero, one_mul]
    exact isUnit_repR hcU _

/-! ### The determinant squareclass -/

/-- Equality in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$: $[x] = [y]$ iff $y = t^2x$ for a unit
$t$ of $\mathcal O_{\mathfrak p}$. -/
theorem sqCl_mk_eq_iff_nf (x y : (v.adicCompletion F)ˣ) :
    (SqCl.mk x : LocalSqCl v) = SqCl.mk y ↔ ∃ t : 𝔬ˣ, ((t : 𝔬) : Fv) ^ 2 * (x : Fv) = y := by
  change (QuotientGroup.mk x : (v.adicCompletion F)ˣ ⧸ (localUnits v).map (powMonoidHom 2)) =
    QuotientGroup.mk y ↔ _
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨g, ⟨t, rfl⟩, hg⟩
    refine ⟨t, ?_⟩
    have := congrArg (fun z : (v.adicCompletion F)ˣ => ((x * z : (v.adicCompletion F)ˣ) : Fv)) hg
    simp only [powMonoidHom_apply, mul_inv_cancel_left] at this
    rw [← this, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]
    rfl
  · rintro ⟨t, ht⟩
    refine ⟨Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom t, ⟨t, rfl⟩, ?_⟩
    apply Units.ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← ht]
    have hx : (x : Fv) ≠ 0 := x.ne_zero
    change ((t : 𝔬) : Fv) ^ 2 = (x : Fv)⁻¹ * (((t : 𝔬) : Fv) ^ 2 * x)
    field_simp

open Classical in
/-- The class in $\mathrm{SqCl}(F_{\mathfrak p}^\times, \mathcal O_{\mathfrak p}^\times)$ of an element of
$\mathcal O_{\mathfrak p}$ (the trivial class for $0$). -/
def sqNF (x : 𝔬) : LocalSqCl v :=
  if h : x = 0 then 1 else SqCl.mk (Units.mk0 ((x : 𝔬) : Fv) (by simpa using h))

theorem sqNF_of_ne {x : 𝔬} (h : x ≠ 0) :
    sqNF x = (SqCl.mk (Units.mk0 ((x : 𝔬) : Fv) (by simpa using h)) : LocalSqCl v) := by
  unfold sqNF; rw [dif_neg h]

theorem sqNF_eq_iff {x y : 𝔬} (hx : x ≠ 0) (hy : y ≠ 0) :
    (sqNF x : LocalSqCl v) = sqNF y ↔ ∃ t : 𝔬ˣ, (t : 𝔬) ^ 2 * x = y := by
  rw [sqNF_of_ne hx, sqNF_of_ne hy, sqCl_mk_eq_iff_nf]
  simp only [Units.val_mk0]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, Subtype.ext ?_⟩
    simpa using ht
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have := congrArg (fun z : 𝔬 => (z : Fv)) ht
    simpa using this

theorem sgn_prod {ι : Type*} (s : Finset ι) (f : ι → 𝔬) (hf : ∀ i, IsUnit (f i)) :
    sgn 𝔬 (∏ i ∈ s, f i) = ∏ i ∈ s, sgn 𝔬 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    apply Units.ext
    rw [sgn_val isUnit_one]
    simp [chiR_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, sgn_mul (hf i) (IsUnit.prod_iff.2 fun j _ => hf j), ih]

theorem sgn_repR {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) (x : ℤˣ) : sgn 𝔬 (repR c x) = x := by
  apply Units.ext
  rw [sgn_val (isUnit_repR hcU x), chiR_repR hc]

variable (v) in
/-- The unit $2^n\prod_i\operatorname{rep}(x_i)$ of the Hessian determinant. -/
def detUnitND (c : 𝔬) {n : ℕ} (x : Fin n → ℤˣ) : 𝔬 := 2 ^ n * ∏ i, repR c (x i)

theorem isUnit_detUnitND (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) {n : ℕ} (x : Fin n → ℤˣ) :
    IsUnit (detUnitND v c x) := by
  have h2u : IsUnit (2 : 𝔬) :=
    dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) (not_dvd_two_nf v hv)
  exact (h2u.pow _).mul (IsUnit.prod_iff.2 fun i _ => isUnit_repR hcU _)

theorem hessian_det_genND (c : 𝔬) {n : ℕ} (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x)).hessian.det =
      LocalDensity.NF.π v ^ (∑ i, z i) * detUnitND v c x := by
  rw [det_hessian_diag, detUnitND]
  simp only [diagVec]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem det_genND_eq (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) {n : ℕ} (z : Fin n → ℕ)
    (x : Fin n → ℤˣ) :
    (genND v c z x).det = sqNF (LocalDensity.NF.π v ^ (∑ i, z i) * detUnitND v c x) := by
  have hπ := LocalDensity.NF.irreducible_π v
  have hne : LocalDensity.NF.π v ^ (∑ i, z i) * detUnitND v c x ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (isUnit_detUnitND hv hcU x).ne_zero
  have hdet := hessian_det_genND (v := v) c z x
  unfold genND
  rw [LocGenus.det_mk]
  have hne' : algebraMap 𝔬 Fv (QuadForm.diag (diagVec (LocalDensity.NF.π v) c z x)).hessian.det ≠ 0 := by
    rw [algebraMap_ne_zero_iff, hdet]; exact hne
  rw [detSqForm_of_ne hne', sqNF_of_ne hne]
  congr 1
  apply Units.ext
  simp only [Units.val_mk0]
  rw [hdet]
  rfl

/-- **The determinant squareclass of a diagonal genus**: $\det_H(\mathrm{genND}(z,x)) = [\pi^\nu w]$ for a unit $w$
iff $\sum_iz_i = \nu$ and $\prod_ix_i = \chi(2)^n\chi(w)$ (signs). -/
theorem det_genND_iff (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) {w : 𝔬} (hw : IsUnit w) (ν : ℕ) :
    (genND v c z x).det = sqNF (LocalDensity.NF.π v ^ ν * w) ↔
      ∑ i, z i = ν ∧ ∏ i, x i = sgn 𝔬 (2 : 𝔬) ^ n * sgn 𝔬 w := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  have hU := isUnit_detUnitND hv hcU x
  have h2u : IsUnit (2 : 𝔬) := dvr_isUnit_of_not_dvd hπ h2
  have hA : LocalDensity.NF.π v ^ (∑ i, z i) * detUnitND v c x ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hU.ne_zero
  have hB : LocalDensity.NF.π v ^ ν * w ≠ 0 := mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hw.ne_zero
  have hsU : sgn 𝔬 (detUnitND v c x) = sgn 𝔬 (2 : 𝔬) ^ n * ∏ i, x i := by
    unfold detUnitND
    rw [sgn_mul (h2u.pow _) (IsUnit.prod_iff.2 fun i _ => isUnit_repR hcU _), sgn_pow h2u,
      sgn_prod _ _ (fun i => isUnit_repR hcU _)]
    simp only [sgn_repR hcU hc]
  rw [det_genND_eq hv hcU, sqNF_eq_iff hA hB]
  have hsq : ∀ a : ℤˣ, a * a = 1 := fun a => Int.units_mul_self a
  constructor
  · rintro ⟨t, ht⟩
    have ht' : LocalDensity.NF.π v ^ (∑ i, z i) * ((t : 𝔬) ^ 2 * detUnitND v c x) =
        LocalDensity.NF.π v ^ ν * w := by rw [← ht]; ring
    obtain ⟨hZ, hUw⟩ := pow_mul_unit_eq hπ ((t.isUnit.pow 2).mul hU) hw ht'
    refine ⟨hZ, ?_⟩
    have hs : sgn 𝔬 w = sgn 𝔬 (detUnitND v c x) := by
      rw [← hUw, sgn_mul (t.isUnit.pow 2) hU, sgn_pow t.isUnit]
      rw [sq, hsq, one_mul]
    rw [hs, hsU, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2, pow_mul, sq, hsq, one_pow, one_mul]
  · rintro ⟨hZ, hprod⟩
    have hs : sgn 𝔬 (detUnitND v c x) = sgn 𝔬 w := by
      rw [hsU, hprod, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2, pow_mul, sq, hsq, one_pow, one_mul]
    have hchi : quadraticChar (IsLocalRing.ResidueField 𝔬)
        (IsLocalRing.residue 𝔬 (detUnitND v c x * w)) = 1 := by
      have e : quadraticChar (IsLocalRing.ResidueField 𝔬) (IsLocalRing.residue 𝔬 (detUnitND v c x * w)) =
          chiR (detUnitND v c x) * chiR w := by unfold chiR; rw [map_mul, map_mul]
      rw [e, ← sgn_val hU, ← sgn_val hw, hs]
      rw [← Units.val_mul, hsq]; rfl
    obtain ⟨s, hsU', hse⟩ := unit_sq_rel hπ h2 hU hw hchi
    refine ⟨hsU'.unit, ?_⟩
    rw [IsUnit.unit_spec, hZ, hse]
    ring

/-! ### The Hilbert symbol and the Hasse invariant -/

section Hilbert

local notation "πF" => (((LocalDensity.NF.π v : 𝔬)) : Fv)

theorem hilb_comm (a b : Fv) : hilbertSymbol Fv a b = hilbertSymbol Fv b a := by
  exact hilbertSymbol_comm Fv a b

theorem hilb_pow_left (a : ℕ) {x y : Fv} (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol Fv (x ^ a) y = hilbertSymbol Fv x y ^ a := by
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  induction a with
  | zero => simp [PadicClass.hs_one_left]
  | succ a ih => rw [pow_succ, hK.mul_left _ _ _ (pow_ne_zero a hx) hx hy, ih, pow_succ]

theorem hilb_pow_right (a : ℕ) {x y : Fv} (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol Fv x (y ^ a) = hilbertSymbol Fv x y ^ a := by
  rw [hilb_comm, hilb_pow_left a hy hx, hilb_comm]

theorem hilb_mul_left {x x' y : Fv} (hx : x ≠ 0) (hx' : x' ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol Fv (x * x') y = hilbertSymbol Fv x y * hilbertSymbol Fv x' y :=
  (HasseIsoNF.localHilbertField_adicCompletion v).mul_left _ _ _ hx hx' hy

theorem hilb_mul_right {x y y' : Fv} (hx : x ≠ 0) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    hilbertSymbol Fv x (y * y') = hilbertSymbol Fv x y * hilbertSymbol Fv x y' :=
  (HasseIsoNF.localHilbertField_adicCompletion v).mul_right hx hy hy'

theorem coe_ne_zero_nf' {u : 𝔬} (hu : u ≠ 0) : ((u : 𝔬) : Fv) ≠ 0 := fun h => hu (Subtype.ext h)

theorem coe_ne_zero_nf {u : 𝔬} (hu : IsUnit u) : ((u : 𝔬) : Fv) ≠ 0 := coe_ne_zero_nf' hu.ne_zero

theorem pi_ne_zero_nf : πF ≠ 0 := coe_ne_zero_nf' (LocalDensity.NF.irreducible_π v).ne_zero

/-- Every nonzero element of $F_{\mathfrak p}$ is a square times $\pi^k w$, $k \in \mathbb N$, $w \in \mathcal O_{\mathfrak p}^\times$. -/
theorem exists_decomp (x : Fv) (hx : x ≠ 0) :
    ∃ (s : Fv) (k : ℕ) (w : 𝔬), s ≠ 0 ∧ IsUnit w ∧ x = s ^ 2 * (πF ^ k * (w : Fv)) := by
  have hπ := LocalDensity.NF.irreducible_π v
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝔬) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx; rw [← hab]; simp
  obtain ⟨m, u1, hu1⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  obtain ⟨l, u2, hu2⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  have hP : πF ≠ 0 := pi_ne_zero_nf
  have hU2 : (((u2 : 𝔬ˣ) : 𝔬) : Fv) ≠ 0 := coe_ne_zero_nf u2.isUnit
  have hA : algebraMap 𝔬 Fv a = (((u1 : 𝔬ˣ) : 𝔬) : Fv) * πF ^ m := by
    rw [hu1]; simp
  have hB : algebraMap 𝔬 Fv b = (((u2 : 𝔬ˣ) : 𝔬) : Fv) * πF ^ l := by
    rw [hu2]; simp
  have hbF : (algebraMap 𝔬 Fv b) ≠ 0 := by
    rw [hB]; exact mul_ne_zero hU2 (pow_ne_zero _ hP)
  refine ⟨(algebraMap 𝔬 Fv b)⁻¹, m + l, (u1 : 𝔬) * (u2 : 𝔬), inv_ne_zero hbF, (u1.isUnit.mul u2.isUnit), ?_⟩
  rw [← hab, hA, hB]
  have : (((u1 : 𝔬ˣ) : 𝔬) * ((u2 : 𝔬ˣ) : 𝔬) : 𝔬) = (((u1 : 𝔬ˣ) : 𝔬) * ((u2 : 𝔬ˣ) : 𝔬) : 𝔬) := rfl
  push_cast
  field_simp
  ring

/-- **The Hilbert symbol of a uniformizer with a unit is the quadratic character of the unit**
(nondyadic $\mathfrak p$): $(\pi, u)_{\mathfrak p} = \chi(\bar u)$. -/
theorem hilb_pi_unit (hv : (2 : 𝓞 F) ∉ v.asIdeal) {u : 𝔬} (hu : IsUnit u) :
    hilbertSymbol Fv πF (u : Fv) = chiR u := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have hres : IsLocalRing.residue 𝔬 u ≠ 0 := (hu.map _).ne_zero
  have huF := coe_ne_zero_nf (v := v) hu
  rcases quadraticChar_dichotomy hres with h | h
  · have hχ : chiR u = 1 := h
    rw [hχ]
    obtain ⟨s, hs⟩ := (isSquare_iff_quadraticChar_residue hπ h2 (dvr_not_dvd_of_isUnit hπ hu)).2 h
    exact PadicClass.hs_of_isSquare _ _ huF ⟨(s : Fv), by rw [hs]; push_cast; rfl⟩
  · have hχ : chiR u = -1 := h
    rw [hχ]
    have hnsq : ¬ IsSquare ((u : 𝔬) : Fv) := by
      rintro ⟨y, hy⟩
      have hint : IsIntegral 𝔬 y := by
        refine ⟨Polynomial.X ^ 2 - Polynomial.C u, Polynomial.monic_X_pow_sub_C u two_ne_zero, ?_⟩
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
        rw [sq, ← hy]; simp
      obtain ⟨y', hy'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hsq : u = y' * y' := by
        apply Subtype.ext
        have : ((u : 𝔬) : Fv) = (y' : Fv) * (y' : Fv) := by
          rw [hy]; rw [← hy']; rfl
        simpa using this
      have := (isSquare_iff_quadraticChar_residue hπ h2 (dvr_not_dvd_of_isUnit hπ hu)).1 ⟨y', hsq⟩
      rw [h] at this
      exact absurd this (by norm_num)
    obtain ⟨x, hx0, hx⟩ := hK.exists_neg_one _ huF hnsq
    obtain ⟨s, k, w, hs0, hw, hxe⟩ := exists_decomp (v := v) x hx0
    have hwF := coe_ne_zero_nf (v := v) hw
    have hP := pi_ne_zero_nf (v := v)
    rw [hxe, hilbertSymbol_comm] at hx
    rw [PadicClass.hs_sq_left _ _ _ hs0, hilb_mul_left (pow_ne_zero _ hP) hwF huF,
      hilb_pow_left k hP huF] at hx
    have hww : hilbertSymbol Fv (w : Fv) (u : Fv) = 1 := by
      have := hilbertSymbol_units_dvr hπ h2 Fv hw hu
      simpa using this
    rw [hww, mul_one] at hx
    rcases PadicClass.hs_pm (K := Fv) πF (u : Fv) with h1 | h1
    · rw [h1, one_pow] at hx; norm_num at hx
    · exact h1

/-- **The Hilbert symbol of two entries** $\pi^au$, $\pi^bu'$ ($u, u'$ units) at a nondyadic prime:
$(\pi^au,\pi^bu')_{\mathfrak p} = \chi(-1)^{ab}\chi(\bar u)^b\chi(\bar u')^a$. -/
theorem hilb_pair (hv : (2 : 𝓞 F) ∉ v.asIdeal) (a b : ℕ) {u u' : 𝔬} (hu : IsUnit u) (hu' : IsUnit u') :
    hilbertSymbol Fv (πF ^ a * (u : Fv)) (πF ^ b * (u' : Fv)) =
      (((sgn 𝔬 (-1 : 𝔬)) ^ (a * b) * sgn 𝔬 u ^ b * sgn 𝔬 u' ^ a : ℤˣ) : ℤ) := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  have hK := HasseIsoNF.localHilbertField_adicCompletion v
  have hP : πF ≠ 0 := pi_ne_zero_nf
  have huF := coe_ne_zero_nf (v := v) hu
  have hu'F := coe_ne_zero_nf (v := v) hu'
  have hPb : πF ^ b * (u' : Fv) ≠ 0 := mul_ne_zero (pow_ne_zero _ hP) hu'F
  have h1 : hilbertSymbol Fv (u : Fv) (u' : Fv) = 1 := by
    have := hilbertSymbol_units_dvr hπ h2 Fv hu hu'
    simpa using this
  have hm1 : IsUnit (-1 : 𝔬) := isUnit_one.neg
  have hpp : hilbertSymbol Fv πF πF = chiR (-1 : 𝔬) := by
    rw [hK.self hP]
    have := hilb_pi_unit hv hm1
    simpa using this
  rw [hilb_mul_left (pow_ne_zero a hP) huF hPb, hilb_pow_left a hP hPb, hilb_mul_right hP (pow_ne_zero b hP) hu'F,
    hilb_pow_right b hP hP, hilb_mul_right huF (pow_ne_zero b hP) hu'F, hilb_pow_right b huF hP, h1, hpp,
    hilb_pi_unit hv hu', hilbertSymbol_comm Fv (u : Fv) πF, hilb_pi_unit hv hu]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, sgn_val hu, sgn_val hu', sgn_val hm1]
  ring

local notation "map_diag_nf" => Matrix.diagonal_map

theorem hasse_genND (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genND v c z x).hasse = ((hasseZ (sgn 𝔬 (-1 : 𝔬)) z x : ℤˣ) : ℤ) := by
  have hπ := LocalDensity.NF.irreducible_π v
  set D := diagVec (LocalDensity.NF.π v) c z x with hD
  have hnz : ∀ i, algebraMap 𝔬 Fv (D i) ≠ 0 := by
    intro i
    exact coe_ne_zero_nf' (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) (isUnit_repR hcU _).ne_zero)
  have hmap : (QuadForm.diag D).map (algebraMap 𝔬 Fv) = QuadForm.diag (fun i => algebraMap 𝔬 Fv (D i)) :=
    QuadForm.ext (Matrix.diagonal_map (map_zero _))
  unfold genND
  rw [LocGenus.hasse_mk, hasseForm, hmap, hasseC_diag v _ hnz]
  unfold PadicClass.hasseVec hasseZ
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs with hij
  · have := hilb_pair hv (z i) (z j) (isUnit_repR hcU (x i)) (isUnit_repR hcU (x j))
    simp only [hD, diagVec, map_mul, map_pow]
    rw [show algebraMap 𝔬 Fv (LocalDensity.NF.π v) = πF from rfl,
      show algebraMap 𝔬 Fv (repR c (x i)) = ((repR c (x i) : 𝔬) : Fv) from rfl,
      show algebraMap 𝔬 Fv (repR c (x j)) = ((repR c (x j) : 𝔬) : Fv) from rfl, this]
    unfold hp
    simp only [sgn_repR hcU hc]
  · simp

end Hilbert

/-! ### The density -/

theorem norm_two_nf (hv : (2 : 𝓞 F) ∉ v.asIdeal) : ‖(2 : Fv)‖ = 1 := by
  have h2u : IsUnit (2 : 𝔬) :=
    dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) (not_dvd_two_nf v hv)
  have := Tamagawa.norm_coe_unit v h2u
  have e : (((2 : 𝔬)) : Fv) = 2 := map_ofNat (algebraMap 𝔬 Fv) 2
  rwa [e] at this

theorem sgn_neg_one_val : ((sgn 𝔬 (-1 : 𝔬) : ℤˣ) : ℤ) =
    quadraticChar (IsLocalRing.ResidueField 𝔬) (-1 : IsLocalRing.ResidueField 𝔬) := by
  rw [sgn_val (isUnit_one.neg)]
  unfold chiR
  rw [map_neg, map_one]

/-- **The inverse local density of a diagonal genus is twice its weight**:
$\beta(G)^{-1} = 2\,\mathrm{wt}(\operatorname{symC}(z,x))$ (nondyadic $\mathfrak p$ of a number field, every rank). -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23 (density of a diagonal genus, p ∤ 2, every number field, every n)"]
theorem beta_genND (hv : (2 : 𝓞 F) ∉ v.asIdeal) {c : 𝔬} (hcU : IsUnit c) (hc : chiR c = -1) {n : ℕ}
    (z : Fin n → ℕ) (x : Fin n → ℤˣ) :
    (genND v c z x).beta =
      (2 * wtC (Mq (DVR.q 𝔬) (sgn 𝔬 (-1 : 𝔬))) (aq (DVR.q 𝔬)) (symC z x))⁻¹ := by
  have hπ := LocalDensity.NF.irreducible_π v
  have h2 := not_dvd_two_nf v hv
  have hne := (nondeg_genND hv hcU z x)
  have hloc := loc_diag_eq hπ h2 hcU hc (e := sgn 𝔬 (-1 : 𝔬)) sgn_neg_one_val z x
  unfold genND at hne ⊢
  rw [LocGenus.beta_mk, betaForm, Hanke2005.hankeBeta_std_hessian v _ ((LocGenus.nondeg_mk _).1 hne),
    norm_two_nf hv, one_pow, one_mul]
  unfold DVR.siegelDensity
  rw [if_pos rfl, hloc]
  rw [one_div, mul_inv]

end NF

end

end QuadFormsKB.Hanke2011Structure.RatND

#print axioms QuadFormsKB.Hanke2011Structure.RatND.beta_genND
#print axioms QuadFormsKB.Hanke2011Structure.RatND.hasse_genND
#print axioms QuadFormsKB.Hanke2011Structure.RatND.det_genND_iff
#print axioms QuadFormsKB.Hanke2011Structure.RatND.exists_genND
#print axioms QuadFormsKB.Hanke2011Structure.RatND.genND_eq_iff
