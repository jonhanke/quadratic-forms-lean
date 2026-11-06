/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Classify
import QuadFormsKB.Tamagawa.Dyadic7Units

/-!
# Paper 7 at odd primes: the Hessian determinant squareclasses of the tuples

For a place $v \nmid 2$ of $\mathbb Q$ with $p = p_v$, the squareclass group
$\mathrm{SqCl}(\mathbb Q_v^\times, \mathbb Z_v^\times)$ is $\{p^k u\}$ with $u \in \mathbb Z_p^\times/(\mathbb Z_p^\times)^2 =
\{\pm1\}$ (the Legendre symbol). This file proves:

* `exists_unit_sq_mul`: two units of $\mathbb Z_p$ with the same Legendre symbol differ by the square of a unit;
* `localOrd_p`: $\operatorname{ord}_v(p) = 1$;
* `zSqCl_eq_iff_odd`: $[p^aw] = [p^{a'}w'] \iff a = a' \wedge \left(\frac wp\right) = \left(\frac{w'}p\right)$
  (for integers $w, w'$ prime to $p$; `Dyadic7.zSqCl` is the class of an integer);
* `exists_zSqCl_eq_odd`: every class of valuation $a \ge 0$ is $[p^aw]$;
* `det_tupG`: $\det_H$ of the genus of a tuple is $[8p^{a+b}u_1u_2u_3]$; `nondeg_tupG`, `prim_tupG`;
* `exists_u`: for $S$ with $\operatorname{ord} S = \nu \ge 0$ there is a unit $u = \pm1$ with
  $\det_H(\mathrm{tupG}) = S \iff a + b = \nu \wedge u_1u_2u_3 = u$.

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section Gen

variable {p : ℕ} [hp : Fact p.Prime]

/-- The unit of $\mathbb Z_p$ given by an integer prime to $p$. -/
def cu {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : ℤ_[p]ˣ := (isUnit_intCast_of_not_dvd hz).unit

theorem cu_val {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : ((cu hz : ℤ_[p]ˣ) : ℤ_[p]) = ((z : ℤ) : ℤ_[p]) := rfl

/-- **Two $p$-adic units with the same Legendre symbol differ by the square of a unit** ($p$ odd; Hensel). -/
theorem exists_unit_sq_mul (hp2 : p ≠ 2) {r r' : ℤ_[p]ˣ} (h : chiU r = chiU r') :
    ∃ s : ℤ_[p]ˣ, s ^ 2 * r = r' := by
  set c : ℤ_[p]ˣ := r' * r⁻¹ with hc
  have hc1 : chiU c = 1 := by
    rw [hc, map_mul, map_inv, ← h]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := (isSquare_coe_unit_iff hp2 c).2 hc1
  have hcn : ‖((c : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 c.isUnit
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_mul] at hcn
    nlinarith [norm_nonneg x]
  set y : ℤ_[p] := ⟨x, hx1.le⟩
  have hy : IsUnit y := PadicInt.isUnit_iff.2 hx1
  refine ⟨hy.unit, ?_⟩
  have hyc : y * y = (c : ℤ_[p]) := by
    apply Subtype.ext
    show x * x = ((c : ℤ_[p]) : ℚ_[p])
    exact hx.symm
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, hyc, hc, Units.val_mul, mul_assoc,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- Units differing by a unit square have the same Legendre symbol. -/
theorem chiU_eq_of_sq_mul {r r' s : ℤ_[p]ˣ} (h : s ^ 2 * r = r') : chiU r = chiU r' := by
  rw [← h, map_mul, map_pow, Int.units_sq, one_mul]

end Gen

/-! ### The prime $p$ in $\mathbb Q_v$ -/

section AtV

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem pv_ne_zero : ((pv v : ℕ) : ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : (pv v).Prime).ne_zero

theorem intCast_mem_pow_iff (n : ℤ) (k : ℕ) :
    (n : 𝓞 ℚ) ∈ v.asIdeal ^ k ↔ ((Rat.HeightOneSpectrum.natGenerator v : ℤ) ^ k) ∣ n := by
  rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, Rat.HeightOneSpectrum.span_natGenerator,
    ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap, RatHeadline3.intEquiv_symm_intCast]

theorem pv_mem : ((pv v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h : (((pv v : ℕ) : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by
    refine (RatHeadline3.intCast_mem_iff v _).mpr ?_
    exact dvd_refl _
  exact_mod_cast h

theorem pv_not_mem_sq : ((pv v : ℕ) : 𝓞 ℚ) ∉ v.asIdeal ^ 2 := by
  intro h
  have h' : (((pv v : ℕ) : ℤ) : 𝓞 ℚ) ∈ v.asIdeal ^ 2 := by exact_mod_cast h
  rw [intCast_mem_pow_iff] at h'
  have hp := (Fact.out : (pv v).Prime)
  have hd : ((pv v : ℕ) : ℤ) ^ 2 ∣ ((pv v : ℕ) : ℤ) := h'
  have hd' : (pv v) ^ 2 ∣ pv v := by exact_mod_cast hd
  have := Nat.le_of_dvd hp.pos hd'
  have h2 := hp.two_le
  nlinarith

/-- **$\operatorname{ord}_v(p) = 1$** for the prime $v = (p)$ of $\mathbb Q$. -/
theorem localOrd_p :
    localOrd v (Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) ((pv v : ℕ) : ℚ)) (by simpa using pv_ne_zero v)) =
      Multiplicative.ofAdd 1 := by
  have h1 : v.intValuation ((pv v : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ 1).mpr (by simpa using pv_mem v)
  have h2' : ¬ v.intValuation ((pv v : ℕ) : 𝓞 ℚ) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => pv_not_mem_sq v ((v.intValuation_le_pow_iff_mem _ 2).mp h)
  have hvalQ : v.valuation ℚ ((pv v : ℕ) : ℚ) = v.intValuation ((pv v : ℕ) : 𝓞 ℚ) := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := ℚ) v ((pv v : ℕ) : 𝓞 ℚ)
    simpa only [map_natCast] using this
  have hne : v.intValuation ((pv v : ℕ) : 𝓞 ℚ) ≠ 0 := by
    rw [← hvalQ]; exact (Valuation.ne_zero_iff _).mpr (pv_ne_zero v)
  have hval : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((pv v : ℕ) : ℚ)) =
      v.intValuation ((pv v : ℕ) : 𝓞 ℚ) := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((pv v : ℕ) : 𝓞 ℚ)
    simp only [map_natCast] at h ⊢
    rw [h, hvalQ]
  change Multiplicative.ofAdd (-WithZero.log (Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((pv v : ℕ) : ℚ)))) = _
  rw [hval]
  have hk := WithZero.exp_log hne
  rw [← hk] at h1 h2'
  rw [WithZero.exp_le_exp] at h1 h2'
  have : WithZero.log (v.intValuation ((pv v : ℕ) : 𝓞 ℚ)) = -1 := by push_cast at h1 h2'; omega
  rw [this]; rfl

theorem coe_intCast_o (z : ℤ) : (((z : 𝔬)) : Fv) = (z : Fv) := by
  simp

theorem intCast_unit_o {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) : IsUnit (w : 𝔬) := by
  have := (isUnit_intCast_of_not_dvd hw).map (eInt v)
  rwa [map_intCast] at this

theorem ordZ_zSqCl_unit {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (Dyadic7.zSqCl v w) = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  rw [Dyadic7.zSqCl_of_ne v hw0, SqCl.ordZ_mk]
  have hmem : Units.mk0 ((w : ℚ) : Fv) (by simpa using hw0) ∈ localUnits v := by
    refine ⟨(intCast_unit_o v hw).unit, ?_⟩
    apply Units.ext
    simp
  have := localUnits_le_ker v hmem
  rw [MonoidHom.mem_ker] at this
  rw [this]; rfl

theorem zSqCl_p : Dyadic7.zSqCl v ((pv v : ℕ) : ℤ) =
    SqCl.mk (Units.mk0 (algebraMap ℚ (v.adicCompletion ℚ) ((pv v : ℕ) : ℚ)) (by simpa using pv_ne_zero v)) := by
  have hz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  rw [Dyadic7.zSqCl_of_ne v hz]
  congr 1

theorem ordZ_zSqCl_p :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (Dyadic7.zSqCl v ((pv v : ℕ) : ℤ)) = 1 := by
  rw [zSqCl_p, SqCl.ordZ_mk, localOrd_p]
  rfl

/-- $\operatorname{ord}_v[p^aw] = a$ for $w$ prime to $p$. -/
theorem ordZ_zSqCl_odd (a : ℕ) {w : ℤ} (hw : ¬ (pv v : ℤ) ∣ w) :
    SqCl.ordZ (localOrd v) (localUnits_le_ker v) (Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a * w)) = a := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hpow : ∀ k : ℕ, Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ k) = Dyadic7.zSqCl v ((pv v : ℕ) : ℤ) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Dyadic7.zSqCl_of_ne v one_ne_zero]; simp
    | succ k ih => rw [pow_succ, Dyadic7.zSqCl_mul v (pow_ne_zero _ hpz) hpz, ih, pow_succ]
  rw [Dyadic7.zSqCl_mul v (pow_ne_zero _ hpz) hw0, SqCl.ordZ_mul, hpow, ← zpow_natCast, SqCl.ordZ_zpow,
    ordZ_zSqCl_p, ordZ_zSqCl_unit v hw]
  simp

/-- $[p^aw] = [p^aw']$ iff $\left(\frac{w}{p}\right) = \left(\frac{w'}{p}\right)$ ($w, w'$ prime to $p$). -/
theorem zSqCl_eq_iff_same (hp2 : pv v ≠ 2) (a : ℕ) {w w' : ℤ} (hw : ¬ (pv v : ℤ) ∣ w)
    (hw' : ¬ (pv v : ℤ) ∣ w') :
    Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a * w) = Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a * w') ↔
      chiU (cu hw) = chiU (cu hw') := by
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  have hw0' : w' ≠ 0 := by rintro rfl; exact hw' (dvd_zero _)
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hz : ((pv v : ℕ) : ℤ) ^ a * w ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hw0
  have hz' : ((pv v : ℕ) : ℤ) ^ a * w' ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hw0'
  rw [Dyadic7.zSqCl_of_ne v hz, Dyadic7.zSqCl_of_ne v hz', Dyadic7.sqCl_mk_eq_iff]
  simp only [Units.val_mk0]
  push_cast
  have hpa : (((pv v : ℕ) : Fv)) ^ a ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero)
  constructor
  · rintro ⟨t, ht⟩
    have ht' : ((t : 𝔬) : Fv) ^ 2 * (w : Fv) = (w' : Fv) := by
      have := ht
      rw [mul_left_comm] at this
      exact mul_left_cancel₀ hpa this
    have hO : (t : 𝔬) ^ 2 * (w : 𝔬) = (w' : 𝔬) := by
      apply Subtype.ext
      simpa using ht'
    set s := (eInt v).symm (t : 𝔬) with hs
    have hsu : IsUnit s := t.isUnit.map _
    have hZ : s ^ 2 * ((w : ℤ) : ℤ_[pv v]) = ((w' : ℤ) : ℤ_[pv v]) := by
      apply (eInt v).injective
      rw [map_mul, map_pow, hs, RingEquiv.apply_symm_apply, map_intCast, map_intCast, hO]
    apply Units.ext
    rw [chiU_val, chiU_val, cu_val, cu_val, ← hZ, chi_mul, chi_sq hsu, one_mul]
  · intro h
    obtain ⟨s, hs⟩ := exists_unit_sq_mul hp2 h
    refine ⟨Units.map (eInt v).toMonoidHom s, ?_⟩
    have hs' := congrArg (fun z : ℤ_[pv v]ˣ => ((eInt v) (z : ℤ_[pv v]) : Fv)) hs
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, cu_val, map_mul, map_pow, map_intCast,
      coe_intCast_o] at hs'
    show ((eInt v (s : ℤ_[pv v]) : 𝔬) : Fv) ^ 2 * _ = _
    rw [← hs']
    push_cast
    ring

/-- **The squareclasses $[p^aw]$**: $[p^aw] = [p^{a'}w'] \iff a = a' \wedge \left(\frac wp\right) = \left(\frac{w'}p\right)$. -/
theorem zSqCl_eq_iff_odd (hp2 : pv v ≠ 2) (a a' : ℕ) {w w' : ℤ} (hw : ¬ (pv v : ℤ) ∣ w)
    (hw' : ¬ (pv v : ℤ) ∣ w') :
    Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a * w) = Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a' * w') ↔
      a = a' ∧ chiU (cu hw) = chiU (cu hw') := by
  constructor
  · intro h
    have ha : a = a' := by
      have h1 := ordZ_zSqCl_odd v a hw
      have h2 := ordZ_zSqCl_odd v a' hw'
      rw [h] at h1
      omega
    subst ha
    exact ⟨rfl, (zSqCl_eq_iff_same v hp2 a hw hw').1 h⟩
  · rintro ⟨rfl, h⟩
    exact (zSqCl_eq_iff_same v hp2 a hw hw').2 h

/-- **Every squareclass of valuation $a \ge 0$ is $[p^aw]$ with $w$ an integer prime to $p$.** -/
theorem exists_zSqCl_eq_odd (hp2 : pv v ≠ 2) (S : LocalSqCl v) (a : ℕ)
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = a) :
    ∃ (w : ℤ) (hw : ¬ (pv v : ℤ) ∣ w), S = Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ a * w) := by
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  rw [SqCl.ordZ_mk] at hS
  set pU : Fvˣ := Units.mk0 (algebraMap ℚ Fv ((pv v : ℕ) : ℚ)) (by simpa using pv_ne_zero v) with hpU
  set y : Fvˣ := x * pU ^ (-(a : ℤ)) with hy
  have hyo : localOrd v y = 1 := by
    rw [hy, map_mul, map_zpow, hpU, localOrd_p, ← hS]
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
  set r : ℤ_[pv v]ˣ := Units.map (eInt v).symm.toMonoidHom t with hr
  set w : ℤ := ((PadicInt.toZMod (r : ℤ_[pv v])).val : ℤ) with hw
  have hcast : ((w : ℤ) : ZMod (pv v)) = PadicInt.toZMod (r : ℤ_[pv v]) := by
    rw [hw, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hwr : ¬ (pv v : ℤ) ∣ w := by
    intro hdvd
    have h0 : ((w : ℤ) : ZMod (pv v)) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd w (pv v)).2 hdvd
    rw [hcast] at h0
    exact (r.isUnit.map (PadicInt.toZMod (p := pv v))).ne_zero h0
  refine ⟨w, hwr, ?_⟩
  have hu0 : ((pv v : ℕ) : ℤ) ^ a * w ≠ 0 := by
    have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
    exact mul_ne_zero (pow_ne_zero _ hpz) (fun h => hwr (h ▸ dvd_zero _))
  rw [Dyadic7.zSqCl_of_ne v hu0, eq_comm, Dyadic7.sqCl_mk_eq_iff]
  have hch : chiU (cu hwr) = chiU r := by
    apply Units.ext
    rw [chiU_val, chiU_val, cu_val]
    unfold chi
    rw [map_intCast, hcast]
  obtain ⟨s, hs⟩ := exists_unit_sq_mul hp2 hch
  refine ⟨Units.map (eInt v).toMonoidHom s, ?_⟩
  have hs' := congrArg (fun q : ℤ_[pv v]ˣ => ((eInt v) (q : ℤ_[pv v]) : Fv)) hs
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, cu_val, map_mul, map_pow, map_intCast,
    coe_intCast_o] at hs'
  have hrt : ((eInt v) (r : ℤ_[pv v]) : Fv) = y := by
    rw [hr]; simp [ht]
  have hp0 : ((pv v : ℕ) : Fv) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hxy : (x : Fv) = (y : Fv) * ((pv v : ℕ) : Fv) ^ a := by
    rw [hy, Units.val_mul, Units.val_zpow_eq_zpow_val, hpU, Units.val_mk0, map_natCast, mul_assoc,
      ← zpow_natCast, ← zpow_add₀ hp0]
    simp
  show ((eInt v (s : ℤ_[pv v]) : 𝔬) : Fv) ^ 2 * _ = _
  rw [hxy, ← hrt, ← hs']
  simp only [Units.val_mk0]
  push_cast
  ring

/-! ### The genus of a tuple: nondegeneracy, primitivity, determinant -/

variable {v}

theorem tupleVec_zero (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : tupleVec p c a b e₁ e₂ e₃ 0 = rep c e₁ := rfl
theorem tupleVec_one (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    tupleVec p c a b e₁ e₂ e₃ 1 = (p : ℤ) ^ a * rep c e₂ := rfl
theorem tupleVec_two (p : ℕ) (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    tupleVec p c a b e₁ e₂ e₃ 2 = (p : ℤ) ^ b * rep c e₃ := rfl

theorem not_dvd_rep {c : ℤ} (hc : jacobiSym c (pv v) = -1) (e : ℤˣ) : ¬ (pv v : ℤ) ∣ rep c e := by
  unfold rep
  split_ifs
  · exact (Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)).not_dvd_one
  · exact not_dvd_of_jacobiSym hc

theorem not_dvd_eight (hp2 : pv v ≠ 2) : ¬ (pv v : ℤ) ∣ 8 := by
  intro h
  have hpp := Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)
  have h' : (pv v : ℤ) ∣ 2 ^ 3 := by simpa using h
  have := hpp.dvd_of_dvd_pow h'
  have : pv v ∣ 2 := by exact_mod_cast this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : (pv v).Prime) Nat.prime_two).1 this)

/-- The integer $8u_1u_2u_3$ (representatives) of the Hessian determinant of the tuple, without the power of $p$. -/
def detUnit (c : ℤ) (e₁ e₂ e₃ : ℤˣ) : ℤ := 8 * rep c e₁ * rep c e₂ * rep c e₃

theorem not_dvd_detUnit (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (e₁ e₂ e₃ : ℤˣ) :
    ¬ (pv v : ℤ) ∣ detUnit c e₁ e₂ e₃ := by
  have hpp := Nat.prime_iff_prime_int.mp (Fact.out : (pv v).Prime)
  unfold detUnit
  intro h
  rcases hpp.dvd_or_dvd h with h | h
  · rcases hpp.dvd_or_dvd h with h | h
    · rcases hpp.dvd_or_dvd h with h | h
      · exact not_dvd_eight hp2 h
      · exact not_dvd_rep hc e₁ h
    · exact not_dvd_rep hc e₂ h
  · exact not_dvd_rep hc e₃ h

theorem hessian_tupG (c : ℤ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    ((tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬)).hessian.det =
      ((((pv v : ℕ) : ℤ) ^ (a + b) * detUnit c e₁ e₂ e₃ : ℤ) : 𝔬) := by
  unfold tupleForm
  rw [map_diag_eq, hessian_diag_gen, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [tupleVec_zero, tupleVec_one, tupleVec_two, eq_intCast, detUnit]
  push_cast
  ring

theorem det_tupG {c : ℤ} (hp2 : pv v ≠ 2) (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupG v c a b e₁ e₂ e₃).det =
      Dyadic7.zSqCl v (((pv v : ℕ) : ℤ) ^ (a + b) * detUnit c e₁ e₂ e₃) := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : detUnit c e₁ e₂ e₃ ≠ 0 := fun h =>
    not_dvd_detUnit hp2 hc e₁ e₂ e₃ (h ▸ dvd_zero _)
  have hz : ((pv v : ℕ) : ℤ) ^ (a + b) * detUnit c e₁ e₂ e₃ ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hu
  unfold tupG
  rw [LocGenus.det_mk, Dyadic7.zSqCl_of_ne v hz]
  have hdet := hessian_tupG (v := v) c a b e₁ e₂ e₃
  have hne : algebraMap 𝔬 Fv ((tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬)).hessian.det ≠ 0 := by
    rw [hdet]; simpa using hz
  rw [detSqForm_of_ne hne]
  congr 1
  apply Units.ext
  simp only [Units.val_mk0, hdet]
  simp only [Rat.cast_intCast]
  rfl

theorem nondeg_tupG {c : ℤ} (hp2 : pv v ≠ 2) (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupG v c a b e₁ e₂ e₃).Nondeg := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hu : detUnit c e₁ e₂ e₃ ≠ 0 := fun h =>
    not_dvd_detUnit hp2 hc e₁ e₂ e₃ (h ▸ dvd_zero _)
  have hz : ((pv v : ℕ) : ℤ) ^ (a + b) * detUnit c e₁ e₂ e₃ ≠ 0 := mul_ne_zero (pow_ne_zero _ hpz) hu
  unfold tupG
  rw [LocGenus.nondeg_mk, hessian_tupG]
  exact fun h => hz (RingHom.injective_int (algebraMap ℤ 𝔬) (by simpa using h))

theorem prim_tupG {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    (tupG v c a b e₁ e₂ e₃).Prim := by
  unfold tupG
  rw [LocGenus.prim_mk]
  unfold Hanke2011Structure.IsPrimitiveForm
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨(0, 0), rfl⟩) ?_
  show IsUnit (algebraMap ℤ 𝔬 (tupleVec (pv v) c a b e₁ e₂ e₃ 0))
  rw [tupleVec_zero, eq_intCast]
  exact intCast_unit_o v (not_dvd_rep hc e₁)

/-- **The Hessian determinant squareclass of a tuple fixes $(a+b, u_1u_2u_3)$**: for $S$ with
$\operatorname{ord}S = \nu \ge 0$ there is $u = \pm1$ with $\det_H(\text{genus of the tuple}) = S$ iff $a + b = \nu$
and $u_1u_2u_3 = u$. -/
theorem exists_u (hp2 : pv v ≠ 2) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (S : LocalSqCl v) (ν : ℕ)
    (hS : SqCl.ordZ (localOrd v) (localUnits_le_ker v) S = ν) :
    ∃ u : ℤˣ, ∀ (a b : ℕ) (e₁ e₂ e₃ : ℤˣ),
      (tupG v c a b e₁ e₂ e₃).det = S ↔ a + b = ν ∧ e₁ * e₂ * e₃ = u := by
  obtain ⟨w, hw, hSw⟩ := exists_zSqCl_eq_odd v hp2 S ν hS
  have h8 := not_dvd_eight (v := v) hp2
  refine ⟨chiU (cu h8) * chiU (cu hw), fun a b e₁ e₂ e₃ => ?_⟩
  rw [det_tupG hp2 hc, hSw, zSqCl_eq_iff_odd v hp2 _ _ (not_dvd_detUnit hp2 hc e₁ e₂ e₃) hw]
  have hcu : chiU (cu (not_dvd_detUnit hp2 hc e₁ e₂ e₃)) = chiU (cu h8) * e₁ * e₂ * e₃ := by
    have : cu (not_dvd_detUnit hp2 hc e₁ e₂ e₃) =
        cu h8 * repU hc e₁ * repU hc e₂ * repU hc e₃ := by
      apply Units.ext
      simp only [Units.val_mul, cu_val, repU_val, detUnit]
      push_cast
      ring
    rw [this, map_mul, map_mul, map_mul, chiU_repU, chiU_repU, chiU_repU]
  rw [hcu]
  refine and_congr Iff.rfl ?_
  have hsq : ∀ x : ℤˣ, x * x = 1 := fun x => by rw [← sq]; exact Int.units_sq x
  constructor
  · intro h
    calc e₁ * e₂ * e₃ = (chiU (cu h8) * chiU (cu h8)) * (e₁ * e₂ * e₃) := by rw [hsq, one_mul]
      _ = chiU (cu h8) * (chiU (cu h8) * e₁ * e₂ * e₃) := by group
      _ = chiU (cu h8) * chiU (cu hw) := by rw [h]
  · intro h
    calc chiU (cu h8) * e₁ * e₂ * e₃ = chiU (cu h8) * (e₁ * e₂ * e₃) := by group
      _ = chiU (cu h8) * (chiU (cu h8) * chiU (cu hw)) := by rw [h]
      _ = chiU (cu hw) := by rw [← mul_assoc, hsq, one_mul]

end AtV

end

end QuadFormsKB.Odd7
