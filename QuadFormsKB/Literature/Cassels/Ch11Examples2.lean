/-
# Cassels, Chapter 11, Example 10 (p. 253): the bound $m(a, p, f)$ for isotropic forms

**Layer:** an integer-valued form `f : QuadForm ℤ n` evaluated over $\mathbb Z_p$ (`ℤ_[p]`, `f.evalIn ℤ_[p]`) and over
$\mathbb Q_p$ (`f.IsotropicIn ℚ_[p]`); a vector of $\mathbb Z_p^n$ is *primitive* when one of its coordinates is a unit.

**Proves** Example 10 (p. 253), the statement left to the reader at the beginning of §9 (p. 235): *let $f$ be a form
in $n > 2$ variables with integer values that is isotropic over $\mathbb Q_p$. Then there is $M = M(f, p)$ such that if
$a$ is represented by $f$ over $\mathbb Z_p$, there is $m = m(a, p, f)$ with $0 \le m < M$ such that $p^{-2m}a$ is
primitively represented over $\mathbb Z_p$* (`ex10`).

*Reading of the scan:* the exponent is garbled in the scan of the exercise; §9 (p. 235) prints the statement with
$p^{-2m}a$ and "$\mathbb Z_p$" (the subscript is lost in the exercise); we use $a \in \mathbb Z_p$, $p^{-2m}a$ meaning
"$a = p^{2m}b$ with $b$ primitively represented", and do not assume that $f$ is regular (the proof does not need it).

*Proof (ours; the book leaves it to the reader).* Let $u$ be a primitive isotropic vector. If $u$ is in the radical of
the bilinear form, every representation $a = f(x)$ becomes primitive on replacing $x$ by $x + u$ (or $x$ is already
primitive), so $M = 1$. Otherwise there is $v$ with $c = B(u, v) \ne 0$, $c = p^k\cdot$unit; every $a$ with
$p^{2k+1} \mid a$ is primitively represented by $su + tv$ with $t = a/c$ and $s = 1 - ae/c^2$ ($e = f(v)$, $s$ a
unit, $t \in p\mathbb Z_p$); for other $a$, write a representation as $p^jx'$ with $x'$ primitive: $j \le k$, so
$M = k + 1$ works.
-/
import QuadFormsKB.Defs.QuadForm
import Mathlib

open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels

variable {n : ℕ}

/-- Helper: $Q(c\vec x) = c^2 Q(\vec x)$ over any commutative $R$-algebra $K$. -/
theorem evalIn_smul_ex {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (Q : QuadForm R n) (c : K)
    (x : Fin n → K) : Q.evalIn K (c • x) = c ^ 2 * Q.evalIn K x := by
  simp only [QuadForm.evalIn, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Helper: evaluation commutes with the inclusion $\mathbb Z_p \to \mathbb Q_p$. -/
theorem evalIn_coe_padic (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n) (u : Fin n → ℤ_[p]) :
    f.evalIn ℚ_[p] (fun i => (u i : ℚ_[p])) = ((f.evalIn ℤ_[p] u : ℤ_[p]) : ℚ_[p]) := by
  simp [QuadForm.evalIn, eq_intCast, apply_ite (fun z : ℤ_[p] => (z : ℚ_[p]))]

/-- Helper: in a local ring, a unit plus a non-unit is a unit. -/
theorem isUnit_add_nonunit' {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ nonunits R := h
  have h2 : -b ∈ nonunits R := by
    rw [mem_nonunits_iff, IsUnit.neg_iff]; exact hb
  have h3 := IsLocalRing.nonunits_add h1 h2
  rw [mem_nonunits_iff] at h3
  apply h3
  simpa using ha

/-- Helper: an element divisible by $p$ is not a unit of $\mathbb Z_p$. -/
theorem not_isUnit_of_p_dvd (p : ℕ) [Fact p.Prime] {t : ℤ_[p]} (h : (p : ℤ_[p]) ∣ t) : ¬ IsUnit t := fun hu =>
  (mem_nonunits_iff.mp (PadicInt.p_nonunit (p := p))) (isUnit_of_dvd_unit h hu)

/-- Helper: a nonzero vector of $\mathbb Q_p^n$ is $p^z$ times a primitive vector of $\mathbb Z_p^n$. -/
theorem exists_primitive_smul (p : ℕ) [Fact p.Prime] (x : Fin n → ℚ_[p]) (hx : x ≠ 0) :
    ∃ (z : ℤ) (u : Fin n → ℤ_[p]), (∃ i, IsUnit (u i)) ∧ ∀ i, x i = (p : ℚ_[p]) ^ z * (u i : ℚ_[p]) := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) ⟨j, Finset.mem_univ j⟩
  have hi0 : x i0 ≠ 0 := by
    intro h0
    have := hmax j (Finset.mem_univ j)
    rw [h0, norm_zero] at this
    exact hj (norm_le_zero_iff.mp this)
  set z : ℤ := (x i0).valuation with hz
  have hpz : (p : ℚ_[p]) ^ z ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hnorm : ‖(p : ℚ_[p]) ^ z‖ = ‖x i0‖ := by
    rw [norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hi0, ← hz, inv_zpow, zpow_neg]
  have hle : ∀ i, ‖x i / (p : ℚ_[p]) ^ z‖ ≤ 1 := fun i => by
    rw [norm_div, hnorm]
    exact (div_le_one (norm_pos_iff.mpr hi0)).mpr (hmax i (Finset.mem_univ i))
  refine ⟨z, fun i => ⟨x i / (p : ℚ_[p]) ^ z, (by exact hle i)⟩, ⟨i0, ?_⟩, fun i => ?_⟩
  · refine PadicInt.isUnit_iff.mpr ?_
    show ‖x i0 / (p : ℚ_[p]) ^ z‖ = 1
    rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hi0)]
  · show x i = (p : ℚ_[p]) ^ z * (x i / (p : ℚ_[p]) ^ z)
    field_simp

/-- Helper: a nonzero vector of $\mathbb Z_p^n$ is $p^j$ times a primitive vector. -/
theorem exists_primitive_smul_int (p : ℕ) [Fact p.Prime] (x : Fin n → ℤ_[p]) (hx : x ≠ 0) :
    ∃ (j : ℕ) (u : Fin n → ℤ_[p]), (∃ i, IsUnit (u i)) ∧ x = (p : ℤ_[p]) ^ j • u := by
  have hx' : (fun i => (x i : ℚ_[p])) ≠ 0 := by
    intro h
    apply hx
    funext i
    exact PadicInt.coe_eq_zero.mp (congrFun h i)
  obtain ⟨z, u, ⟨i0, hi0⟩, hxu⟩ := exists_primitive_smul p _ hx'
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hz : 0 ≤ z := by
    by_contra hneg
    push Not at hneg
    have h1 : ‖(x i0 : ℚ_[p])‖ ≤ 1 := (x i0).2
    have hu1 : ‖(u i0 : ℚ_[p])‖ = 1 := by
      rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.mp hi0
    have h2 : ‖(x i0 : ℚ_[p])‖ = ((p : ℝ)⁻¹) ^ z := by
      rw [hxu i0, norm_mul, norm_zpow, Padic.norm_p, hu1, mul_one]
    rw [h2, inv_zpow] at h1
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have h3 : (p : ℝ) ^ z < 1 := zpow_lt_one_of_neg₀ hp1 hneg
    have h4 : (0 : ℝ) < (p : ℝ) ^ z := zpow_pos (by linarith) z
    have : 1 < ((p : ℝ) ^ z)⁻¹ := one_lt_inv₀ h4 |>.mpr h3
    linarith
  refine ⟨z.toNat, u, ⟨i0, hi0⟩, funext fun i => PadicInt.ext ?_⟩
  have e := hxu i
  rw [show z = (z.toNat : ℤ) by omega, zpow_natCast] at e
  simpa using e

/-- **Cassels, Ch. 11, Example 10** (p. 253): *let $f$ be an isotropic form in $n > 2$ variables taking integer values
(here: `f : QuadForm ℤ n` isotropic over $\mathbb Q_p$, `hiso`). Then there is $M = M(f, p)$ such that, if $a$ is
represented by $f$ over $\mathbb Z_p$, there is $m = m(a, p, f)$ with $0 \le m < M$ such that $p^{-2m}a$ is
primitively represented over $\mathbb Z_p$.* Arguments: `n` the number of variables (`hn : 2 < n`), `p` the prime,
`f` the form, `hiso` the isotropy over $\mathbb Q_p$; `M` is the bound, `a` the represented element of $\mathbb Z_p$,
`m` the exponent, `b` $= p^{-2m}a$ and `y` the primitive representation of `b`. The form is not required to be
regular. -/
@[kb "cassels1978" "Ch. 11, Ex. 10, p. 253 (statement of §9, p. 235)"]
theorem ex10 (_hn : 2 < n) (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n) (hiso : f.IsotropicIn ℚ_[p]) :
    ∃ M : ℕ, ∀ a : ℤ_[p], (∃ x : Fin n → ℤ_[p], f.evalIn ℤ_[p] x = a) →
      ∃ m < M, ∃ b : ℤ_[p], a = (p : ℤ_[p]) ^ (2 * m) * b ∧
        ∃ y : Fin n → ℤ_[p], (∃ i, IsUnit (y i)) ∧ f.evalIn ℤ_[p] y = b := by
  obtain ⟨x, hx0, hx⟩ := hiso
  obtain ⟨z, u, ⟨i0, hi0⟩, hxu⟩ := exists_primitive_smul p x hx0
  have hEu : f.evalIn ℤ_[p] u = 0 := by
    have hxe : x = (p : ℚ_[p]) ^ z • (fun i => (u i : ℚ_[p])) := funext fun i => by simp [hxu i]
    rw [hxe, evalIn_smul_ex, evalIn_coe_padic] at hx
    have hp0 : (p : ℚ_[p]) ^ z ≠ 0 := zpow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have := (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 hp0)
    exact PadicInt.coe_eq_zero.mp this
  set H := f.hessian.map (algebraMap ℤ ℤ_[p]) with hH
  have polar : ∀ x y : Fin n → ℤ_[p], f.evalIn ℤ_[p] (x + y) - f.evalIn ℤ_[p] x - f.evalIn ℤ_[p] y =
      x ⬝ᵥ (H *ᵥ y) := fun x y => QuadForm.polar_eq_hessian ℤ_[p] f x y
  by_cases hrad : ∀ v : Fin n → ℤ_[p], u ⬝ᵥ (H *ᵥ v) = 0
  · refine ⟨1, fun a ⟨x', hx'⟩ => ⟨0, by norm_num, a, by simp, ?_⟩⟩
    by_cases hprim : ∃ i, IsUnit (x' i)
    · exact ⟨x', hprim, hx'⟩
    · push Not at hprim
      refine ⟨u + x', ⟨i0, ?_⟩, ?_⟩
      · simpa using isUnit_add_nonunit' hi0 (hprim i0)
      · have := polar u x'
        rw [hrad x', hEu, hx'] at this
        linear_combination this
  · push Not at hrad
    obtain ⟨v, hv⟩ := hrad
    have hcs := PadicInt.unitCoeff_spec hv
    set c := u ⬝ᵥ (H *ᵥ v) with hc
    set c' : ℤ_[p]ˣ := PadicInt.unitCoeff hv with hc'
    set k := c.valuation with hk
    set e := f.evalIn ℤ_[p] v with he
    refine ⟨k + 1, fun a ⟨x', hx'⟩ => ?_⟩
    by_cases hdiv : (p : ℤ_[p]) ^ (2 * k + 1) ∣ a
    · obtain ⟨a1, ha1⟩ := hdiv
      refine ⟨0, by omega, a, by simp, ?_⟩
      obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], (c' : ℤ_[p]) * w = 1 := ⟨((c'⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), by simp⟩
      refine ⟨(1 - p * (a1 * e * w ^ 2)) • u + (p ^ (k + 1) * (a1 * w)) • v, ⟨i0, ?_⟩, ?_⟩
      · have hs : IsUnit (1 - (p : ℤ_[p]) * (a1 * e * w ^ 2)) := by
          rw [sub_eq_add_neg]
          exact isUnit_add_nonunit' isUnit_one (by
            rw [IsUnit.neg_iff]; exact not_isUnit_of_p_dvd p (dvd_mul_right _ _))
        have ht : ¬ IsUnit ((p : ℤ_[p]) ^ (k + 1) * (a1 * w)) :=
          not_isUnit_of_p_dvd p ⟨p ^ k * (a1 * w), by ring⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact isUnit_add_nonunit' (hs.mul hi0) (fun h => ht (isUnit_of_mul_isUnit_left h))
      · have := polar ((1 - p * (a1 * e * w ^ 2)) • u) ((p ^ (k + 1) * (a1 * w)) • v)
        rw [evalIn_smul_ex, evalIn_smul_ex, hEu, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul] at this
        simp only [smul_eq_mul] at this
        rw [← he, hcs] at this
        rw [ha1]
        linear_combination this + ((p : ℤ_[p]) ^ (2 * k + 1) * a1 * (1 - p * (a1 * e * w ^ 2))) * hw
    · have hx'0 : x' ≠ 0 := by
        rintro rfl
        apply hdiv
        have : a = 0 := by rw [← hx']; simp [QuadForm.evalIn]
        rw [this]; exact dvd_zero _
      obtain ⟨j, w', hw', hxw⟩ := exists_primitive_smul_int p x' hx'0
      have hval : a = (p : ℤ_[p]) ^ (2 * j) * f.evalIn ℤ_[p] w' := by
        rw [← hx', hxw, evalIn_smul_ex]; ring
      refine ⟨j, ?_, f.evalIn ℤ_[p] w', hval, w', hw', rfl⟩
      by_contra hjk
      push Not at hjk
      apply hdiv
      rw [hval]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

end QuadFormsKB.Cassels
