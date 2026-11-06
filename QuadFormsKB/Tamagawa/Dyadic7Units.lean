/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Dyadic7Blocks
import QuadFormsKB.Literature.ConwaySloane.Mass.StdForm

/-!
# Paper 7 at $p = 2$: $\mathbb Z_2 \cong \mathbb Z_v$ and the unit squareclasses at $v \mid 2$

For the place $v \mid 2$ of $\mathbb Q$:
* `e2`: the ring isomorphism $\mathbb Z_2 \cong \mathbb Z_v$ (Mathlib's `padicIntEquiv`, transported along $p_v = 2$);
* `exists_unit_sq_mul`: two units of $\mathbb Z_2$ congruent mod $8$ differ by a unit square (Hensel, via
  `HilbertLocal.isSquare_two_adic_unit_iff`);
* `zSqCl z`: the class of a nonzero integer in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$, and the
  classification of the classes of valuation $a$: they are the classes of $2^a u$, $u \in \{1,3,5,7\}$, and
  $2^a w$, $2^a w'$ ($w, w'$ odd) have the same class iff $w \equiv w' \pmod 8$.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Dyadic7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal

noncomputable section

/-- Transport of $\mathbb Z_p$ along an equality of primes. -/
def zpCast {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : ℤ_[p] ≃+* ℤ_[q] := by
  subst h; exact RingEquiv.refl _

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **The ring isomorphism $\mathbb Z_2 \cong \mathfrak o_v$** at the place $v \mid 2$ of $\mathbb Q$. -/
def e2 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : ℤ_[2] ≃+* 𝔬 :=
  (zpCast (pv_eq_two_of_two_mem v h2).symm).trans (eInt v)

theorem e2_intCast (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (z : ℤ) : e2 v h2 (z : ℤ_[2]) = (z : 𝔬) := map_intCast _ z

/-- Two $2$-adic units with the same residue mod $8$ differ by the square of a unit. -/
theorem exists_unit_sq_mul {r r' : ℤ_[2]ˣ}
    (h : PadicInt.toZModPow 3 (r : ℤ_[2]) = PadicInt.toZModPow 3 (r' : ℤ_[2])) :
    ∃ s : ℤ_[2]ˣ, s ^ 2 * r = r' := by
  set c : ℤ_[2]ˣ := r' * r⁻¹ with hc
  have hc1 : PadicInt.toZModPow 3 (c : ℤ_[2]) = 1 := by
    have hr : IsUnit (PadicInt.toZModPow 3 (r : ℤ_[2])) := r.isUnit.map _
    rw [hc, Units.val_mul, map_mul, ← h]
    have : PadicInt.toZModPow 3 ((r⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * PadicInt.toZModPow 3 (r : ℤ_[2]) = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rw [mul_comm]; exact this
  obtain ⟨x, hx⟩ := (isSquare_two_adic_unit_iff c).mpr hc1
  have hcn : ‖((c : ℤ_[2]) : ℚ_[2])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 c.isUnit
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_mul] at hcn
    nlinarith [norm_nonneg x]
  set y : ℤ_[2] := ⟨x, hx1.le⟩
  have hy : IsUnit y := PadicInt.isUnit_iff.2 hx1
  refine ⟨hy.unit, ?_⟩
  have hyc : y * y = (c : ℤ_[2]) := by
    apply Subtype.ext
    show x * x = ((c : ℤ_[2]) : ℚ_[2])
    exact hx.symm
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, hyc, hc, Units.val_mul, mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- A $2$-adic unit squared is $\equiv 1 \pmod 8$. -/
theorem toZModPow_sq_unit (s : ℤ_[2]ˣ) : PadicInt.toZModPow 3 ((s : ℤ_[2]) ^ 2) = 1 := by
  have key : ∀ y : ZMod (2 ^ 3), IsUnit y → y ^ 2 = 1 := by decide
  rw [map_pow]; exact key _ (s.isUnit.map _)

/-- The class in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$ of a nonzero integer ($1$ for $z = 0$). -/
def zSqCl (z : ℤ) : LocalSqCl v :=
  if h : z = 0 then 1 else SqCl.mk (Units.mk0 ((z : ℚ) : Fv) (by simpa using h))

theorem zSqCl_of_ne {z : ℤ} (h : z ≠ 0) : zSqCl v z = SqCl.mk (Units.mk0 ((z : ℚ) : Fv) (by simpa using h)) := by
  unfold zSqCl; simp [h]

/-- Equality in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$: $[x] = [y]$ iff $y = t^2 x$ for a unit $t$ of $\mathbb Z_v$. -/
theorem sqCl_mk_eq_iff (x y : Fvˣ) :
    (SqCl.mk x : LocalSqCl v) = SqCl.mk y ↔ ∃ t : 𝔬ˣ, ((t : 𝔬) : Fv) ^ 2 * (x : Fv) = y := by
  change (QuotientGroup.mk x : Fvˣ ⧸ (localUnits v).map (powMonoidHom 2)) = QuotientGroup.mk y ↔ _
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨g, ⟨t, rfl⟩, hg⟩
    refine ⟨t, ?_⟩
    have := congrArg (fun z : Fvˣ => ((x * z : Fvˣ) : Fv)) hg
    simp only [powMonoidHom_apply, mul_inv_cancel_left] at this
    rw [← this, Units.val_mul, Units.val_pow_eq_pow_val, mul_comm]
    rfl
  · rintro ⟨t, ht⟩
    refine ⟨Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom t, ⟨t, rfl⟩, ?_⟩
    apply Units.ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← ht]
    have hx : (x : Fv) ≠ 0 := x.ne_zero
    change ((t : 𝔬) : Fv) ^ 2 = (x : Fv)⁻¹ * (((t : 𝔬) : Fv) ^ 2 * x)
    field_simp

theorem coe_intCast_o (z : ℤ) : (((z : 𝔬)) : Fv) = (z : Fv) := by
  simp

theorem intCast_unit_o (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {w : ℤ} (hw : Odd w) : IsUnit (w : 𝔬) := by
  rw [← e2_intCast v h2]
  exact (Cassels.dyadic_isUnit_int_cast_of_odd hw).map _

/-- $[2^a w] = [2^a w']$ in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$, $v \mid 2$, $w, w'$ odd, iff $w \equiv w' \pmod 8$. -/
@[kb "hanke2011ternary" "§4, Def. 4.5, p. 11 (SqCl(O_p^×) = (Z/8Z)^× at F_p = Q_2)"]
theorem zSqCl_eq_iff (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a : ℕ) {w w' : ℤ} (hw : Odd w) (hw' : Odd w') :
    zSqCl v (2 ^ a * w) = zSqCl v (2 ^ a * w') ↔ w % 8 = w' % 8 := by
  have hw0 : w ≠ 0 := by rintro rfl; exact absurd hw (by decide)
  have hw0' : w' ≠ 0 := by rintro rfl; exact absurd hw' (by decide)
  have hz : (2 : ℤ) ^ a * w ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hw0
  have hz' : (2 : ℤ) ^ a * w' ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hw0'
  rw [zSqCl_of_ne v hz, zSqCl_of_ne v hz', sqCl_mk_eq_iff]
  simp only [Units.val_mk0]
  push_cast
  have h2a : ((2 : Fv) ^ a) ≠ 0 := pow_ne_zero _ two_ne_zero
  constructor
  · rintro ⟨t, ht⟩
    have ht' : ((t : 𝔬) : Fv) ^ 2 * (w : Fv) = (w' : Fv) := by
      have := ht
      rw [mul_left_comm] at this
      exact mul_left_cancel₀ h2a this
    have hO : (t : 𝔬) ^ 2 * (w : 𝔬) = (w' : 𝔬) := by
      apply Subtype.ext
      simpa using ht'
    set s := (e2 v h2).symm (t : 𝔬) with hs
    have hsu : IsUnit s := t.isUnit.map _
    have hZ : s ^ 2 * (w : ℤ_[2]) = (w' : ℤ_[2]) := by
      apply (e2 v h2).injective
      rw [map_mul, map_pow, hs, RingEquiv.apply_symm_apply, e2_intCast, e2_intCast, hO]
    have hm := congrArg (PadicInt.toZModPow 3) hZ
    have hsq := toZModPow_sq_unit hsu.unit
    rw [IsUnit.unit_spec] at hsq
    rw [map_mul, hsq, one_mul, map_intCast, map_intCast] at hm
    exact (ZMod.intCast_eq_intCast_iff' w w' 8).mp hm
  · intro h
    have hm : PadicInt.toZModPow 3 ((Cassels.dyadic_isUnit_int_cast_of_odd hw).unit : ℤ_[2]) =
        PadicInt.toZModPow 3 ((Cassels.dyadic_isUnit_int_cast_of_odd hw').unit : ℤ_[2]) := by
      simp only [IsUnit.unit_spec, map_intCast]
      exact (ZMod.intCast_eq_intCast_iff' w w' 8).mpr h
    obtain ⟨s, hs⟩ := exists_unit_sq_mul hm
    refine ⟨Units.map (e2 v h2).toMonoidHom s, ?_⟩
    have hs' := congrArg (fun z : ℤ_[2]ˣ => ((e2 v h2) (z : ℤ_[2]) : Fv)) hs
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, e2_intCast,
      coe_intCast_o] at hs'
    change ((e2 v h2 (s : ℤ_[2]) : 𝔬) : Fv) ^ 2 * (2 ^ a * (w : Fv)) = 2 ^ a * (w' : Fv)
    rw [← hs']
    push_cast
    ring

theorem zSqCl_mul {z z' : ℤ} (hz : z ≠ 0) (hz' : z' ≠ 0) : zSqCl v (z * z') = zSqCl v z * zSqCl v z' := by
  rw [zSqCl_of_ne v hz, zSqCl_of_ne v hz', zSqCl_of_ne v (mul_ne_zero hz hz'), ← map_mul]
  congr 1
  apply Units.ext
  simp

theorem twoSqCl_eq : twoSqCl v = zSqCl v 2 := by
  rw [zSqCl_of_ne v two_ne_zero]
  unfold twoSqCl
  congr 1

theorem ordZ_zSqCl_odd (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {w : ℤ} (hw : Odd w) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v w) = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; exact absurd hw (by decide)
  rw [zSqCl_of_ne v hw0, SqCl.ordZ_mk]
  have hmem : Units.mk0 ((w : ℚ) : Fv) (by simpa using hw0) ∈ localUnits v := by
    refine ⟨(intCast_unit_o v h2 hw).unit, ?_⟩
    apply Units.ext
    simp
  have := localUnits_le_ker v hmem
  rw [MonoidHom.mem_ker] at this
  rw [this]; rfl

theorem ordZ_zSqCl_two (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v 2) = 1 := by
  rw [← twoSqCl_eq]
  unfold twoSqCl
  rw [SqCl.ordZ_mk, localOrd_two v h2]
  rfl

/-- $\operatorname{ord}_2[2^a w] = a$ for $w$ odd. -/
theorem ordZ_zSqCl (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (a : ℕ) {w : ℤ} (hw : Odd w) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (zSqCl v (2 ^ a * w)) = a := by
  have hw0 : w ≠ 0 := by rintro rfl; exact absurd hw (by decide)
  have hpow : ∀ k : ℕ, zSqCl v (2 ^ k) = zSqCl v 2 ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, zSqCl_of_ne v one_ne_zero]; simp
    | succ k ih => rw [pow_succ, zSqCl_mul v (pow_ne_zero _ two_ne_zero) two_ne_zero, ih, pow_succ]
  rw [zSqCl_mul v (pow_ne_zero _ two_ne_zero) hw0, SqCl.ordZ_mul, hpow, ← zpow_natCast, SqCl.ordZ_zpow,
    ordZ_zSqCl_two v h2, ordZ_zSqCl_odd v h2 hw]
  simp

/-- Every class of valuation $a \ge 0$ in $\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$, $v \mid 2$, is $[2^a u]$ for some
$u \in \{1,3,5,7\}$. -/
@[kb "hanke2011ternary" "§4, Def. 4.5, p. 11 (SqCl(O_p^×) = (Z/8Z)^× at F_p = Q_2)"]
theorem exists_zSqCl_eq (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (S : LocalSqCl v) (a : ℕ)
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = a) :
    ∃ u ∈ sqUnits, S = zSqCl v (2 ^ a * u) := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  rw [SqCl.ordZ_mk] at hS
  set two : Fvˣ := Units.mk0 (algebraMap ℚ Fv 2) (by simp) with htwo
  set y : Fvˣ := x * two ^ (-(a : ℤ)) with hy
  have hyo : localOrd v y = 1 := by
    rw [hy, map_mul, map_zpow, htwo, localOrd_two v h2, ← hS]
    simp [← ofAdd_zsmul]
  have hval : Valued.v (y : Fv) = 1 := by
    have h := hyo
    change Multiplicative.ofAdd (-WithZero.log (Valued.v (y : Fv))) = 1 at h
    have hne : Valued.v (y : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
    have hl : WithZero.log (Valued.v (y : Fv)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [← WithZero.exp_log hne, hl]; rfl
  have hinv : Valued.v ((y⁻¹ : Fvˣ) : Fv) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
  let t : 𝔬ˣ :=
    { val := ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hval.le⟩
      inv := ⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hinv.le⟩
      val_inv := Subtype.ext (Units.mul_inv y)
      inv_val := Subtype.ext (Units.inv_mul y) }
  have ht : ((t : 𝔬) : Fv) = y := rfl
  set r : ℤ_[2]ˣ := Units.map (e2 v h2).symm.toMonoidHom t with hr
  set z := PadicInt.toZModPow 3 (r : ℤ_[2]) with hz
  have hzu : IsUnit z := r.isUnit.map _
  have hval8 : ∀ z : ZMod (2 ^ 3), IsUnit z → z.val = 1 ∨ z.val = 3 ∨ z.val = 5 ∨ z.val = 7 := by decide
  have hcast : ∀ z : ZMod (2 ^ 3), ((z.val : ℤ) : ZMod (2 ^ 3)) = z := fun z => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  set u : ℤ := (z.val : ℤ) with hu
  have hus : u ∈ sqUnits := by
    rcases hval8 z hzu with h | h | h | h <;> simp [hu, h, sqUnits]
  have huo : Odd u := by
    rcases hval8 z hzu with h | h | h | h <;> rw [hu, h] <;> decide
  refine ⟨u, hus, ?_⟩
  have hu0 : (2 : ℤ) ^ a * u ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) (by rintro h; rw [h] at huo; exact absurd huo (by decide))
  rw [zSqCl_of_ne v hu0, eq_comm, sqCl_mk_eq_iff]
  have hm : PadicInt.toZModPow 3 ((Cassels.dyadic_isUnit_int_cast_of_odd huo).unit : ℤ_[2]) =
      PadicInt.toZModPow 3 (r : ℤ_[2]) := by
    rw [IsUnit.unit_spec, map_intCast, ← hz, hu, hcast]
  obtain ⟨s, hs⟩ := exists_unit_sq_mul hm
  refine ⟨Units.map (e2 v h2).toMonoidHom s, ?_⟩
  have hs' := congrArg (fun q : ℤ_[2]ˣ => ((e2 v h2) (q : ℤ_[2]) : Fv)) hs
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_mul, map_pow, e2_intCast,
    coe_intCast_o] at hs'
  have hrt : ((e2 v h2) (r : ℤ_[2]) : Fv) = y := by
    rw [hr]; simp [ht]
  have hxy : (x : Fv) = (y : Fv) * (2 : Fv) ^ a := by
    rw [hy, Units.val_mul, Units.val_zpow_eq_zpow_val, htwo, Units.val_mk0, map_ofNat, mul_assoc,
      ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    simp
  change ((e2 v h2 (s : ℤ_[2]) : 𝔬) : Fv) ^ 2 * (((2 ^ a * u : ℤ) : ℚ) : Fv) = x
  rw [hxy, ← hrt, ← hs']
  push_cast
  ring

/-- **The Hessian determinant squareclass of a block genus**: $\det_H(G_D) = [2^{h}w]$, $h$ = `valSum D`,
$w$ = `unitProd D` (`det_dyMatInt`). -/
@[kb "hanke2011structure" "§1.3, p. 6 (det_H of a local genus)"]
theorem det_genusOf {n : ℕ} {D : List DyBlock} (hD : ∀ b ∈ D, b.Valid) (h0 : ∀ b ∈ D, 0 ≤ blockExp b)
    (hn : dyDim D = n) (hev : ∀ b ∈ D, ¬ IsOddUnimodBlock b) :
    (genusOf v n D).det = zSqCl v (2 ^ valSum D * unitProd D) := by
  have hu : unitProd D ≠ 0 := fun h => odd_unitProd D hD (h ▸ dvd_zero 2)
  have hz : (2 : ℤ) ^ valSum D * unitProd D ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hu
  unfold genusOf
  rw [LocGenus.det_mk, zSqCl_of_ne v hz]
  have hdet : ((formZ n D).map (algebraMap ℤ 𝔬)).hessian.det = ((2 ^ valSum D * unitProd D : ℤ) : 𝔬) := by
    rw [QuadForm.hessian_map', hessian_formZ hn h0 hev, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      det_hessZ hn h0]
    simp
  have hne : algebraMap 𝔬 Fv ((formZ n D).map (algebraMap ℤ 𝔬)).hessian.det ≠ 0 := by
    rw [hdet]; simpa using hz
  rw [detSqForm_of_ne hne]
  congr 1
  apply Units.ext
  simp only [Units.val_mk0, hdet]
  simp only [Rat.cast_intCast]
  rfl

end

end QuadFormsKB.Dyadic7

#print axioms QuadFormsKB.Dyadic7.zSqCl_eq_iff
#print axioms QuadFormsKB.Dyadic7.exists_zSqCl_eq
#print axioms QuadFormsKB.Dyadic7.det_genusOf
#print axioms QuadFormsKB.Dyadic7.ordZ_zSqCl
