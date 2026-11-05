/-
# Cassels, Chapter 3, Examples 12, 13 and 15 (pp. 50–51)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 3, *Examples*, pp. 50–51.

**Proves.**
* Ex. 12 (p. 50): if $|a - 1|_p \le p^{-1}$ ($p \ne 3$), resp. $|a-1|_3 \le 3^{-2}$, then $a$ is a cube in
  $\mathbb Q_p$ (`ex12_ne_three`, `ex12_three`, `ex12`).
* Ex. 13 (p. 50): Hensel lifting of a simple root of $x^{2} + bx + c$ with unit discriminant, for every prime $p$
  including $2$ (`ex13`).
* Ex. 15 (p. 51), matrices over $\mathbb Z_2$: (i) $A \equiv I \pmod 4$, $A \ne I$ has infinite order (`ex15_i`);
  (ii) $A \equiv I \pmod 2$ has $A^{2} = I$ or infinite order (`ex15_ii`); (iii) a finite group of matrices
  $\equiv I \pmod 2$ has order $2^{m}$ with $m \le n$ (`ex15_iii`); (iv) a finite group of invertible matrices over
  $\mathbb Z_2$ has order dividing $2^{n}\prod_{j<n}(2^{n} - 2^{j})$ (`ex15_iv`).

Indices are $0$-based. "Infinite order" for a matrix $A$ means $A^{k} \ne I$ for all $k \ge 1$, as in
`Ch3Ex.ex14_i`.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Cassels.Ch3.Exercises

open Filter Topology

noncomputable section

namespace QuadFormsKB.Cassels.Ch3Ex

section Hensel

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Cassels, Ch. 3, Ex. 12 (p. 50), case $p \ne 3$.** Let $a \in \mathbb Q_p$ with $|a - 1|_p \le p^{-1}$ and
$p \ne 3$. Then $a$ is a cube in $\mathbb Q_p$. (Hensel's lemma for $x^{3} - a$ at $x = 1$, where the derivative $3$ is
a unit.) -/
@[kb "cassels1978" "Ch. 3, Ex. 12, p. 50"]
theorem ex12_ne_three (hp3 : p ≠ 3) {a : ℚ_[p]} (ha : ‖a - 1‖ ≤ (p : ℝ)⁻¹) : ∃ x : ℚ_[p], x ^ 3 = a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have ha1 : ‖a‖ ≤ 1 := by
    have : a = (a - 1) + 1 := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha.trans hlt.le) (by simp))
  let a' : ℤ_[p] := ⟨a, ha1⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 3 - Polynomial.C a'
  have hF1 : F.aeval (1 : ℤ_[p]) = 1 - a' := by simp [F]
  have hF2 : F.derivative.aeval (1 : ℤ_[p]) = 3 := by simp [F]; norm_num
  have h3 : ‖(3 : ℤ_[p])‖ = 1 := by
    have : ((3 : ℤ) : ℤ_[p]) = 3 := by norm_num
    rw [← this]
    refine (lt_or_eq_of_le (PadicInt.norm_le_one _)).resolve_left ?_
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hd
    have h' : p ∣ 3 := by exact_mod_cast hd
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h'
    exact hp3 this
  have hn : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF1, hF2, h3]
    have : ‖1 - a'‖ = ‖a - 1‖ := by
      rw [PadicInt.norm_def, norm_sub_rev]; rfl
    rw [this]
    simpa using ha.trans_lt hlt
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  refine ⟨(z : ℚ_[p]), ?_⟩
  have : z ^ 3 = a' := by simpa [F, sub_eq_zero] using hz
  have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) this
  simpa using this

/-- **Cassels, Ch. 3, Ex. 12 (p. 50), case $p = 3$.** Let $a \in \mathbb Q_3$ with $|a - 1|_3 \le 3^{-2}$. Then $a$
is a cube in $\mathbb Q_3$. Since the bound is not strict, Hensel's lemma at $x = 1$ does not apply directly. We
substitute $x = 1 + 3t$: then $x^{3} - a = 9\,g(t)$ with
$g(t) = 3t^{3} + 3t^{2} + t - (a - 1)/9 \in \mathbb Z_3[t]$, and $g'(t) \equiv 1 \pmod 3$, $g(t_0) \equiv 0 \pmod 3$
for $t_0 = (a-1)/9$. Hensel's lemma gives a root $t$. -/
@[kb "cassels1978" "Ch. 3, Ex. 12, p. 50"]
theorem ex12_three {a : ℚ_[3]} (ha : ‖a - 1‖ ≤ (3 : ℝ) ^ (-2 : ℤ)) : ∃ x : ℚ_[3], x ^ 3 = a := by
  have h9 : ‖(9 : ℚ_[3])‖ = (3 : ℝ) ^ (-2 : ℤ) := by
    have : (9 : ℚ_[3]) = ((3 : ℕ) : ℚ_[3]) ^ 2 := by norm_num
    rw [this, norm_pow, Padic.norm_p]
    norm_num
  have hc : ‖(a - 1) / 9‖ ≤ 1 := by
    rw [norm_div, h9, div_le_one (by positivity)]
    exact ha
  let c : ℤ_[3] := ⟨(a - 1) / 9, hc⟩
  have hcq : (c : ℚ_[3]) = (a - 1) / 9 := rfl
  let G : Polynomial ℤ_[3] :=
    3 * Polynomial.X ^ 3 + 3 * Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c
  have h3lt : ‖(3 : ℤ_[3])‖ < 1 := by
    have : ((3 : ℕ) : ℤ_[3]) = 3 := by norm_num
    rw [← this, PadicInt.norm_lt_one_iff_dvd]
  have hG1 : G.aeval c = 3 * c ^ 3 + 3 * c ^ 2 := by simp [G]
  have hG2 : G.derivative.aeval c = 9 * c ^ 2 + 6 * c + 1 := by
    simp [G]
    ring
  have hy : ‖(3 : ℤ_[3]) * (3 * c ^ 2 + 2 * c)‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) h3lt
  have hn1 : ‖G.derivative.aeval c‖ = 1 := by
    rw [hG2]
    have : (9 * c ^ 2 + 6 * c + 1 : ℤ_[3]) = 1 + 3 * (3 * c ^ 2 + 2 * c) := by ring
    rw [this, PadicInt.norm_add_eq_max_of_ne (by rw [norm_one]; exact hy.ne')]
    rw [norm_one]
    exact max_eq_left hy.le
  have hn : ‖G.aeval c‖ < ‖G.derivative.aeval c‖ ^ 2 := by
    rw [hn1, hG1, one_pow]
    have : (3 * c ^ 3 + 3 * c ^ 2 : ℤ_[3]) = 3 * (c ^ 3 + c ^ 2) := by ring
    rw [this, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) h3lt
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  have hz' : (3 : ℤ_[3]) * z ^ 3 + 3 * z ^ 2 + z = c := by
    have : G.aeval z = 3 * z ^ 3 + 3 * z ^ 2 + z - c := by simp [G]
    rw [this] at hz
    exact sub_eq_zero.mp hz
  have hq : 3 * (z : ℚ_[3]) ^ 3 + 3 * (z : ℚ_[3]) ^ 2 + z = (a - 1) / 9 := by
    have := congrArg (fun w : ℤ_[3] => (w : ℚ_[3])) hz'
    push_cast at this
    rw [← hcq]; exact this
  refine ⟨1 + 3 * (z : ℚ_[3]), ?_⟩
  linear_combination 9 * hq

/-- **Cassels, Ch. 3, Ex. 12 (p. 50).** Let $a \in \mathbb Q_p$ with $|a - 1|_p \le p^{-1}$ if $p \ne 3$, resp.
$|a - 1|_3 \le 3^{-2}$ if $p = 3$. Then $a$ is a cube in $\mathbb Q_p$, i.e. $a \in \mathbb Q_p^{\times 3}$. -/
@[kb "cassels1978" "Ch. 3, Ex. 12, p. 50"]
theorem ex12 {a : ℚ_[p]} (ha : ‖a - 1‖ ≤ if p = 3 then (3 : ℝ) ^ (-2 : ℤ) else (p : ℝ)⁻¹) :
    ∃ x : ℚ_[p], x ^ 3 = a := by
  by_cases h3 : p = 3
  · subst h3
    simp only [↓reduceIte] at ha
    exact ex12_three ha
  · simp only [h3, ↓reduceIte] at ha
    exact ex12_ne_three h3 ha

/-- **Cassels, Ch. 3, Ex. 13 (p. 50).** Let $f(x) = x^{2} + bx + c$ with $b, c \in \mathbb Z_p$ and
$|b^{2} - 4c|_p = 1$ (unit discriminant; $p = 2$ is allowed). Suppose $f(v) \equiv 0 \pmod p$ for some
$v \in \mathbb Z_p$. Then there is $u \in \mathbb Z_p$ with $f(u) = 0$ and $u \equiv v \pmod p$. -/
@[kb "cassels1978" "Ch. 3, Ex. 13, p. 50"]
theorem ex13 {b c : ℤ_[p]} (hdisc : ‖b ^ 2 - 4 * c‖ = 1) {v : ℤ_[p]}
    (hv : ((p : ℕ) : ℤ_[p]) ∣ v ^ 2 + b * v + c) :
    ∃ u : ℤ_[p], u ^ 2 + b * u + c = 0 ∧ ((p : ℕ) : ℤ_[p]) ∣ u - v := by
  let F : Polynomial ℤ_[p] :=
    Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c
  have hF1 : F.aeval v = v ^ 2 + b * v + c := by simp [F]
  have hF2 : F.derivative.aeval v = 2 * v + b := by
    simp [F]
    left; norm_num
  have h1 : ‖v ^ 2 + b * v + c‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr hv
  have h2 : ‖2 * v + b‖ = 1 := by
    refine (lt_or_eq_of_le (PadicInt.norm_le_one _)).resolve_left fun hlt => ?_
    have e : b ^ 2 - 4 * c = (2 * v + b) ^ 2 - 4 * (v ^ 2 + b * v + c) := by ring
    have hsq : ‖(2 * v + b) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
    have h4 : ‖4 * (v ^ 2 + b * v + c)‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) h1
    have : ‖b ^ 2 - 4 * c‖ < 1 := by
      rw [e]
      rw [sub_eq_add_neg]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hsq ?_)
      rwa [norm_neg]
    rw [hdisc] at this
    exact lt_irrefl _ this
  have hn : ‖F.aeval v‖ < ‖F.derivative.aeval v‖ ^ 2 := by
    rw [hF1, hF2, h2]; simpa using h1
  obtain ⟨z, hz, hzv, -⟩ := hensels_lemma hn
  refine ⟨z, by simpa [F] using hz, ?_⟩
  rw [← PadicInt.norm_lt_one_iff_dvd, ]
  rwa [hF2, h2] at hzv

end Hensel

section Ex15

variable {n : ℕ}

/-- Reduction modulo $2$ of matrices over $\mathbb Z_2$, entrywise via `PadicInt.toZMod`. -/
def red2 : Matrix (Fin n) (Fin n) ℤ_[2] →+* Matrix (Fin n) (Fin n) (ZMod 2) :=
  (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).mapMatrix

/-- An element of $\mathbb Z_2$ is divisible by $2$ iff its residue modulo $2$ vanishes. -/
theorem two_dvd_iff_toZMod {x : ℤ_[2]} : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    have h2 : PadicInt.toZMod (2 : ℤ_[2]) = 0 := by
      have := map_natCast (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) 2
      simp only [Nat.cast_ofNat] at this
      rw [this]; decide
    rw [map_mul, h2, zero_mul]
  · intro h
    simpa using dvd_of_toZMod_eq_zero (p := 2) h

/-- $A \equiv I \pmod 2$ (entrywise divisibility of $A - I$ by $2$) iff the reduction of $A$ is the identity. -/
theorem red2_eq_one_iff {A : Matrix (Fin n) (Fin n) ℤ_[2]} :
    red2 A = 1 ↔ ∀ i j, (2 : ℤ_[2]) ∣ (A - 1) i j := by
  have h : red2 A = 1 ↔ red2 (A - 1) = 0 := by
    rw [map_sub, map_one, sub_eq_zero]
  rw [h]
  constructor
  · intro h i j
    rw [two_dvd_iff_toZMod]
    have := congrFun (congrFun h i) j
    simpa [red2] using this
  · intro h
    ext i j
    have := (two_dvd_iff_toZMod).mp (h i j)
    simpa [red2] using this

/-- A matrix over $\mathbb Z_2$ whose reduction modulo $2$ is the identity is invertible (its determinant is a
unit). -/
theorem isUnit_of_red2_eq_one {M : Matrix (Fin n) (Fin n) ℤ_[2]} (h : red2 M = 1) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hd : PadicInt.toZMod M.det = 1 := by
    have := RingHom.map_det (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) M
    rw [this]
    have h' : (PadicInt.toZMod : ℤ_[2] →+* ZMod 2).mapMatrix M = 1 := h
    rw [h', Matrix.det_one]
  by_contra hu
  have hm : M.det ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [PadicInt.ker_toZMod]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hu
  rw [RingHom.mem_ker, hd] at hm
  exact one_ne_zero hm

/-- Cancelling a nonzero scalar from a matrix over $\mathbb Z_2$. -/
theorem eq_zero_of_smul_eq_zero {c : ℤ_[2]} (hc : c ≠ 0) {X : Matrix (Fin n) (Fin n) ℤ_[2]}
    (h : c • X = 0) : X = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simpa [hc] using this

/-- If every entry of `D` is divisible by `c`, then `D = c • D'`. -/
theorem exists_smul_of_dvd' {c : ℤ_[2]} {D : Matrix (Fin n) (Fin n) ℤ_[2]} (h : ∀ i j, c ∣ D i j) :
    ∃ D' : Matrix (Fin n) (Fin n) ℤ_[2], D = c • D' := by
  refine ⟨Matrix.of fun i j => (h i j).choose, ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (h i j).choose_spec

/-- $A \equiv I \pmod c$: every entry of $A - I$ is divisible by $c$. -/
def CongOneBy (c : ℤ_[2]) (A : Matrix (Fin n) (Fin n) ℤ_[2]) : Prop :=
  ∀ i j, c ∣ (A - 1) i j

theorem CongOneBy.mul {c : ℤ_[2]} {A B : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : CongOneBy c A)
    (hB : CongOneBy c B) : CongOneBy c (A * B) := by
  intro i j
  have : (A * B - 1) i j = (A * (B - 1)) i j + (A - 1) i j := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.sub_apply]; ring
  rw [this]
  refine dvd_add ?_ (hA i j)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hB k j) _

theorem CongOneBy.pow {c : ℤ_[2]} {A : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : CongOneBy c A) (m : ℕ) :
    CongOneBy c (A ^ m) := by
  induction m with
  | zero => intro i j; simp
  | succ m ih => rw [pow_succ]; exact ih.mul hA

/-- A matrix $A \equiv I \pmod 2$ of odd finite order is the identity. -/
theorem eq_one_of_pow_odd {A : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : red2 A = 1) {m : ℕ} (hm : Odd m)
    (h : A ^ m = 1) : A = 1 := by
  obtain ⟨D, hD⟩ := exists_smul_of_dvd' (red2_eq_one_iff.mp hA)
  set S : Matrix (Fin n) (Fin n) ℤ_[2] := ∑ i ∈ Finset.range m, A ^ i with hS
  have h1 : (A - 1) * S = 0 := by rw [hS, mul_geom_sum, h, sub_self]
  have hS1 : red2 S = 1 := by
    simp only [hS, map_sum, map_pow, hA, one_pow, Finset.sum_const, Finset.card_range]
    obtain ⟨k, rfl⟩ := hm
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by decide
      simp [h2]
    rw [this, one_smul]
  have hSu := isUnit_of_red2_eq_one hS1
  rw [hD, Matrix.smul_mul] at h1
  have h2 := eq_zero_of_smul_eq_zero (by norm_num) h1
  have hD0 : D = 0 := (hSu.mul_left_eq_zero).mp h2
  rw [hD0, smul_zero] at hD
  exact sub_eq_zero.mp hD

/-- A matrix $A \equiv I \pmod 4$ with $A^{2} = I$ is the identity. -/
theorem eq_one_of_sq_eq_one {A : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : CongOneBy 4 A) (h : A ^ 2 = 1) :
    A = 1 := by
  obtain ⟨D, hD⟩ := exists_smul_of_dvd' hA
  have hA' : A = 1 + (4 : ℤ_[2]) • D := by rw [← hD]; abel
  have h1 : (8 : ℤ_[2]) • (D * (1 + (2 : ℤ_[2]) • D)) = 0 := by
    have e : (8 : ℤ_[2]) • (D * (1 + (2 : ℤ_[2]) • D)) = A ^ 2 - 1 := by
      rw [hA', pow_two]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
      module
    rw [e, h, sub_self]
  have h2 := eq_zero_of_smul_eq_zero (by norm_num) h1
  have hu : IsUnit (1 + (2 : ℤ_[2]) • D) := by
    refine isUnit_of_red2_eq_one (red2_eq_one_iff.mpr fun i j => ?_)
    simp
  have hD0 : D = 0 := (hu.mul_left_eq_zero).mp h2
  rw [hA', hD0]; simp

/-- **Cassels, Ch. 3, Ex. 15 (i) (p. 51).** Let $A$ be an $n \times n$ matrix over $\mathbb Z_2$ with
$A \equiv I \pmod 4$ (every entry of $A - I$ is divisible by $4$) but $A \ne I$. Then $A$ has infinite order:
$A^{k} \ne I$ for all $k \ge 1$. -/
@[kb "cassels1978" "Ch. 3, Ex. 15 (i), p. 51"]
theorem ex15_i {A : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : ∀ i j, (4 : ℤ_[2]) ∣ (A - 1) i j) (hne : A ≠ 1)
    (k : ℕ) (hk : 1 ≤ k) : A ^ k ≠ 1 := by
  intro hk1
  have hA4 : CongOneBy 4 A := hA
  have hred : red2 A = 1 := by
    refine red2_eq_one_iff.mpr fun i j => ?_
    exact (show (2 : ℤ_[2]) ∣ 4 from ⟨2, by norm_num⟩).trans (hA i j)
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  have hB : A ^ (2 ^ a) = 1 := by
    refine eq_one_of_pow_odd (m := m) (by rw [map_pow, hred, one_pow]) hm ?_
    rw [← pow_mul]; exact hk1
  clear hk1 hk
  apply hne
  induction a with
  | zero => simpa using hB
  | succ a ih =>
    refine ih ?_
    refine eq_one_of_sq_eq_one (hA4.pow _) ?_
    rw [← pow_mul, ← pow_succ]; exact hB

/-- **Cassels, Ch. 3, Ex. 15 (ii) (p. 51).** Let $A$ be an $n \times n$ matrix over $\mathbb Z_2$ with
$A \equiv I \pmod 2$. Then either $A^{2} = I$ or $A$ has infinite order ($A^{k} \ne I$ for all $k \ge 1$). -/
@[kb "cassels1978" "Ch. 3, Ex. 15 (ii), p. 51"]
theorem ex15_ii {A : Matrix (Fin n) (Fin n) ℤ_[2]} (hA : ∀ i j, (2 : ℤ_[2]) ∣ (A - 1) i j) :
    A ^ 2 = 1 ∨ ∀ k : ℕ, 1 ≤ k → A ^ k ≠ 1 := by
  by_cases hfin : ∃ k : ℕ, 1 ≤ k ∧ A ^ k = 1
  · left
    obtain ⟨k, hk, hk1⟩ := hfin
    obtain ⟨D, hD⟩ := exists_smul_of_dvd' hA
    have hA' : A = 1 + (2 : ℤ_[2]) • D := by rw [← hD]; abel
    have hB : ∀ i j, (4 : ℤ_[2]) ∣ (A ^ 2 - (1 : Matrix (Fin n) (Fin n) ℤ_[2])) i j := by
      intro i j
      have e : A ^ 2 - 1 = (4 : ℤ_[2]) • (D + D * D) := by
        rw [hA', pow_two]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul]
        module
      rw [e]
      exact ⟨(D + D * D) i j, by simp⟩
    by_contra hne
    exact ex15_i hB hne k hk (by rw [← pow_mul, mul_comm, pow_mul, hk1, one_pow])
  · right
    intro k hk h
    exact hfin ⟨k, hk, h⟩

universe u

/-- A finite set `S` of pairwise commuting involutions ($s^{2} = 1$) of a $d$-dimensional vector space over a field
in which $2 \ne 0$ has at most $2^{d}$ elements. (Common eigenspace decomposition, by induction on $d$.) -/
theorem card_le_two_pow_finrank {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) :
    ∀ (d : ℕ) (W : Type u) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
      Module.finrank K W = d → ∀ S : Finset (Module.End K W), (∀ s ∈ S, s * s = 1) →
        (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → S.card ≤ 2 ^ d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W _ _ _ hd S hS hc
  classical
  by_cases hex : ∃ s ∈ S, s ≠ 1 ∧ s ≠ -1
  · obtain ⟨s, hsS, hs1, hs2⟩ := hex
    have hss : ∀ x, s (s x) = x := fun x => by
      have := congrArg (fun f : Module.End K W => f x) (hS s hsS)
      simpa using this
    let U₁ : Submodule K W := Module.End.eigenspace s 1
    let U₂ : Submodule K W := Module.End.eigenspace s (-1)
    have hU₁ : ∀ x, x ∈ U₁ ↔ s x = x := fun x => by simp [U₁]
    have hU₂ : ∀ x, x ∈ U₂ ↔ s x = -x := fun x => by simp [U₂]
    have hmaps₁ : ∀ t ∈ S, ∀ x ∈ U₁, t x ∈ U₁ := by
      intro t ht x hx
      rw [hU₁] at hx ⊢
      have := congrArg (fun f : Module.End K W => f x) (hc s hsS t ht)
      simp only [Module.End.mul_apply] at this
      rw [this, hx]
    have hmaps₂ : ∀ t ∈ S, ∀ x ∈ U₂, t x ∈ U₂ := by
      intro t ht x hx
      rw [hU₂] at hx ⊢
      have := congrArg (fun f : Module.End K W => f x) (hc s hsS t ht)
      simp only [Module.End.mul_apply] at this
      rw [this, hx, map_neg]
    have hcompl : IsCompl U₁ U₂ := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x h1 h2'
        rw [hU₁] at h1
        rw [hU₂] at h2'
        have : (2 : K) • x = 0 := by
          rw [two_smul]
          nth_rewrite 1 [← h1]
          rw [h2']; simp
        exact (smul_eq_zero.mp this).resolve_left h2
      · rw [codisjoint_iff, eq_top_iff]
        intro x _
        have hx : x = (2⁻¹ : K) • (x + s x) + (2⁻¹ : K) • (x - s x) := by
          rw [← smul_add]
          have : x + s x + (x - s x) = (2 : K) • x := by rw [two_smul]; abel
          rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
        rw [hx]
        refine Submodule.add_mem_sup ?_ ?_
        · rw [hU₁, map_smul, map_add, hss, add_comm]
        · rw [hU₂, map_smul, map_sub, hss, ← smul_neg, neg_sub]
    have hfr : Module.finrank K U₁ + Module.finrank K U₂ = d := by
      rw [← hd]; exact Submodule.finrank_add_eq_of_isCompl hcompl
    have hlt₁ : Module.finrank K U₁ < d := by
      rw [← hd]
      refine Submodule.finrank_lt (fun h => hs1 ?_)
      ext x
      have : x ∈ U₁ := h ▸ Submodule.mem_top
      simpa using (hU₁ x).mp this
    have hlt₂ : Module.finrank K U₂ < d := by
      rw [← hd]
      refine Submodule.finrank_lt (fun h => hs2 ?_)
      ext x
      have : x ∈ U₂ := h ▸ Submodule.mem_top
      simpa using (hU₂ x).mp this
    let r : (U : Submodule K W) → Module.End K W → Module.End K U := fun U t =>
      if h : ∀ x ∈ U, t x ∈ U then t.restrict h else 0
    have hr : ∀ (U : Submodule K W) (t : Module.End K W) (h : ∀ x ∈ U, t x ∈ U) (x : U),
        ((r U t x : U) : W) = t x := by
      intro U t h x
      have : r U t = t.restrict h := by simp only [r]; split_ifs; rfl
      rw [this]; rfl
    have key : ∀ U : Submodule K W, (∀ t ∈ S, ∀ x ∈ U, t x ∈ U) → Module.finrank K U < d →
        (S.image (r U)).card ≤ 2 ^ Module.finrank K U := by
      intro U hm hlt
      refine ih _ hlt U rfl (S.image (r U)) ?_ ?_
      · intro s' hs'
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs'
        refine LinearMap.ext fun x => Subtype.ext ?_
        rw [Module.End.mul_apply, hr U t (hm t ht), hr U t (hm t ht)]
        have := congrArg (fun f : Module.End K W => f x) (hS t ht)
        simpa using this
      · intro s' hs' s'' hs''
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs'
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hs''
        refine LinearMap.ext fun x => Subtype.ext ?_
        rw [Module.End.mul_apply, Module.End.mul_apply, hr U t (hm t ht), hr U t' (hm t' ht'),
          hr U t' (hm t' ht'), hr U t (hm t ht)]
        have := congrArg (fun f : Module.End K W => f x) (hc t ht t' ht')
        simpa using this
    have k₁ := key U₁ hmaps₁ hlt₁
    have k₂ := key U₂ hmaps₂ hlt₂
    have hinj : S.card ≤ (S.image (r U₁) ×ˢ S.image (r U₂)).card := by
      refine Finset.card_le_card_of_injOn (fun t => (r U₁ t, r U₂ t)) ?_ ?_
      · intro t ht
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ht, Finset.mem_image_of_mem _ ht⟩
      · intro t ht t' ht' heq
        have ht : t ∈ S := ht
        have ht' : t' ∈ S := ht'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨e₁, e₂⟩ := heq
        have q₁ : Set.EqOn t t' U₁ := by
          intro x hx
          have := congrArg (fun f : Module.End K U₁ => ((f ⟨x, hx⟩ : U₁) : W)) e₁
          simpa only [hr U₁ t (hmaps₁ t ht), hr U₁ t' (hmaps₁ t' ht')] using this
        have q₂ : Set.EqOn t t' U₂ := by
          intro x hx
          have := congrArg (fun f : Module.End K U₂ => ((f ⟨x, hx⟩ : U₂) : W)) e₂
          simpa only [hr U₂ t (hmaps₂ t ht), hr U₂ t' (hmaps₂ t' ht')] using this
        refine LinearMap.ext fun x => ?_
        exact LinearMap.eqOn_sup q₁ q₂ (by rw [hcompl.sup_eq_top]; trivial)
    calc S.card ≤ (S.image (r U₁) ×ˢ S.image (r U₂)).card := hinj
      _ = (S.image (r U₁)).card * (S.image (r U₂)).card := Finset.card_product _ _
      _ ≤ 2 ^ Module.finrank K U₁ * 2 ^ Module.finrank K U₂ := Nat.mul_le_mul k₁ k₂
      _ = 2 ^ d := by rw [← pow_add, hfr]
  · have hall : ∀ s ∈ S, s = 1 ∨ s = -1 := fun s hs => by
      by_cases h1 : s = 1
      · exact Or.inl h1
      · exact Or.inr (by_contra fun h2 => hex ⟨s, hs, h1, h2⟩)
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · have : Subsingleton W := Module.finrank_zero_iff.mp hd
      simpa using Finset.card_le_one_of_subsingleton S
    · calc S.card ≤ ({1, -1} : Finset (Module.End K W)).card := by
            refine Finset.card_le_card fun s hs => ?_
            rcases hall s hs with h | h <;> simp [h]
        _ ≤ 2 := Finset.card_le_two
        _ = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hpos

/-- The ring homomorphism $M_n(\mathbb Z_2) \to \operatorname{End}_{\mathbb Q_2}(\mathbb Q_2^{n})$ letting a matrix act
on column vectors over $\mathbb Q_2$. -/
def actQ2 : Matrix (Fin n) (Fin n) ℤ_[2] →+* Module.End ℚ_[2] (Fin n → ℚ_[2]) :=
  (Matrix.toLinAlgEquiv' (R := ℚ_[2]) (n := Fin n)).toRingEquiv.toRingHom.comp
    (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]).mapMatrix

theorem actQ2_injective : Function.Injective (actQ2 (n := n)) := by
  intro A B h
  have h1 := (Matrix.toLinAlgEquiv' (R := ℚ_[2]) (n := Fin n)).injective h
  have h2 : A.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) = B.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) :=
    h1
  exact Matrix.map_injective (f := (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]))
    (fun a b hab => Subtype.ext hab) h2

/-- In a group in which every element squares to $1$, any two elements commute. -/
theorem comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) (a b : G) : a * b = b * a := by
  have hi : ∀ g : G, g⁻¹ = g := fun g => inv_eq_of_mul_eq_one_right (h g)
  calc a * b = (a * b)⁻¹ := (hi _).symm
    _ = b * a := by rw [mul_inv_rev, hi, hi]

/-- Every element of a subgroup $H$ of $GL_n(\mathbb Z_2)$ all of whose elements are $\equiv I \pmod 2$ and which
is finite squares to the identity matrix (Ex. 15 (ii) applied to the finite order of each element). -/
theorem sq_eq_one_of_finite (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℤ_[2])) [Finite H]
    (hH : ∀ g ∈ H, ∀ i j, (2 : ℤ_[2]) ∣ ((g : Matrix (Fin n) (Fin n) ℤ_[2]) - 1) i j) (g : H) :
    g * g = 1 := by
  obtain ⟨k, hk, hk1⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  have hmat : ((g : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) : Matrix (Fin n) (Fin n) ℤ_[2]) ^ 2 = 1 := by
    rcases ex15_ii (hH g g.2) with h | h
    · exact h
    · exfalso
      refine h k hk ?_
      have := congrArg (fun u : H => ((u : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) :
        Matrix (Fin n) (Fin n) ℤ_[2])) hk1
      simpa using this
  apply Subtype.ext
  apply Units.ext
  simpa [pow_two] using hmat

/-- **Cassels, Ch. 3, Ex. 15 (iii) (p. 51).** Let $H$ be a finite group of $n \times n$ invertible matrices over
$\mathbb Z_2$ all of whose elements are $\equiv I \pmod 2$. Then $|H| = 2^{m}$ for some $m \le n$.
(Proof as in the hint: $H$ has exponent $2$ by (ii), hence is abelian; its elements are simultaneously
diagonalizable over $\mathbb Q_2$ with eigenvalues $\pm 1$, so $H$ embeds in $\{\pm1\}^{n}$. We use the
common eigenspace decomposition `card_le_two_pow_finrank`.) -/
@[kb "cassels1978" "Ch. 3, Ex. 15 (iii), p. 51"]
theorem ex15_iii (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℤ_[2])) [Finite H]
    (hH : ∀ g ∈ H, ∀ i j, (2 : ℤ_[2]) ∣ ((g : Matrix (Fin n) (Fin n) ℤ_[2]) - 1) i j) :
    ∃ m : ℕ, m ≤ n ∧ Nat.card H = 2 ^ m := by
  have hsq := sq_eq_one_of_finite H hH
  have hcomm := comm_of_sq_eq_one hsq
  have : Fintype H := Fintype.ofFinite H
  classical
  let φ : H → Module.End ℚ_[2] (Fin n → ℚ_[2]) := fun g =>
    actQ2 ((g : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) : Matrix (Fin n) (Fin n) ℤ_[2])
  have hφ : Function.Injective φ := by
    intro g h e
    exact Subtype.ext (Units.ext (actQ2_injective e))
  have hbound : Nat.card H ≤ 2 ^ n := by
    have := card_le_two_pow_finrank (K := ℚ_[2]) (two_ne_zero) n (Fin n → ℚ_[2]) (by simp)
      (Finset.univ.image φ) ?_ ?_
    · rwa [Finset.card_image_of_injective _ hφ, Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    · intro s hs
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hs
      have := congrArg (fun u : H => ((u : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) :
        Matrix (Fin n) (Fin n) ℤ_[2])) (hsq g)
      simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] at this
      simp only [φ, ← map_mul, this, map_one]
    · intro s hs t ht
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp ht
      have := congrArg (fun u : H => ((u : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) :
        Matrix (Fin n) (Fin n) ℤ_[2])) (hcomm g h)
      simp only [Subgroup.coe_mul, Units.val_mul] at this
      simp only [φ, ← map_mul, this]
  have hp : IsPGroup 2 H := fun g => ⟨1, by simpa [pow_two] using hsq g⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  refine ⟨m, ?_, hm⟩
  rw [hm] at hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hbound

/-- **Cassels, Ch. 3, Ex. 15 (iv) (p. 51).** Let $G$ be a finite group of invertible $n \times n$ matrices over
$\mathbb Z_2$. Then $|G|$ divides $2^{n}(2^{n} - 1)(2^{n} - 2)\cdots(2^{n} - 2^{n-1})$. (The kernel of reduction
modulo $2$ is a finite group as in (iii), of order dividing $2^{n}$; the image lies in $GL_n(\mathbb F_2)$, whose
order is $\prod_{j<n}(2^{n} - 2^{j})$, Ch. 2 Ex. 12.) -/
@[kb "cassels1978" "Ch. 3, Ex. 15 (iv), p. 51"]
theorem ex15_iv (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℤ_[2])) [Finite G] :
    Nat.card G ∣ 2 ^ n * ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) := by
  let f : G →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)).comp G.subtype
  let H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) := f.ker.map G.subtype
  have hHcard : Nat.card H = Nat.card f.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective G)
  have hH : ∀ g ∈ H, ∀ i j, (2 : ℤ_[2]) ∣ ((g : Matrix (Fin n) (Fin n) ℤ_[2]) - 1) i j := by
    intro g hg i j
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    have hk1 : f k = 1 := hk
    have h1 : ((k : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) : Matrix (Fin n) (Fin n) ℤ_[2]).map
        PadicInt.toZMod = 1 := by
      have := congrArg (fun u : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
        (u : Matrix (Fin n) (Fin n) (ZMod 2))) hk1
      simpa [f, Matrix.GeneralLinearGroup.map] using this
    have hr : red2 ((k : Matrix.GeneralLinearGroup (Fin n) ℤ_[2]) : Matrix (Fin n) (Fin n) ℤ_[2]) = 1 := h1
    exact red2_eq_one_iff.mp hr i j
  have hfin : Finite H :=
    (Set.Finite.subset (Set.toFinite (G : Set (Matrix.GeneralLinearGroup (Fin n) ℤ_[2])))
      (by rintro g ⟨k, -, rfl⟩; exact k.2)).to_subtype
  obtain ⟨m, hm, hcardH⟩ := ex15_iii H hH
  have h1 := Subgroup.card_ker_mul_card_range f
  have hdvd : Nat.card f.range ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Subgroup.card_subgroup_dvd_card f.range
  have : Fintype (ZMod 2) := ZMod.fintype 2
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_eq_prod_range (fun i => 2 ^ n - 2 ^ i) n] at hdvd
  rw [← h1, ← hHcard, hcardH]
  exact mul_dvd_mul (pow_dvd_pow 2 hm) hdvd

end Ex15

end QuadFormsKB.Cassels.Ch3Ex
