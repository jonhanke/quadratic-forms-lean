/-
# Hanke 2011 (ternary masses), §2: local ternary computations at primes $p \nmid 2$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §2, pp. 4–7.

**Setting.** $F$ is a number field, $\mathfrak p \nmid 2$ a prime of $F$ with residue field of size $q$ (an odd prime
power), $\pi_{\mathfrak p}$ a uniformizer. For $\mathfrak p \nmid 2$ the unit square classes
$\mathrm{SqCl}(\mathcal O_{\mathfrak p}^\times)$ form a group of order $2$, identified with $\{\pm 1\} = $ `ℤˣ` by the
Legendre symbol $u \mapsto \left(\frac{u}{\mathfrak p}\right)$. The paper writes
$\varepsilon_i := \left(\frac{u_i}{\mathfrak p}\right)$ and
$\varepsilon' := \left(\frac{-1}{\mathfrak p}\right) = (-1)^{(q-1)/2}$; in Lean a unit square class $u_i$ is
represented by its Legendre symbol `e i : ℤˣ`, and $\varepsilon'$ is a parameter `ε' : ℤˣ`. The paper's indices
$u_1, u_2, u_3$ are Lean's `e₁ e₂ e₃` (the names keep the paper's 1-based numbering).

**What is here.**

* `IsJordanTuple`, `unitChoices`, `oddGenera` (**Lemma 2.1**): the tuples $T_{\mathfrak p} = (a, b; u_1, u_2, u_3)$,
  $0 \le a \le b$, subject to the constraints (1)–(3), with $a + b = \nu$ and $u_1u_2u_3 = u$. The paper's bijection
  with $\mathcal O_{\mathfrak p}$-classes of primitive ternary forms is the normalization
  $Q_{\mathfrak p} \sim u_1x^2 + \pi^a u_2y^2 + \pi^b u_3z^2$ (O'Meara §92:1–2); the lattice-level bijection is not
  formalized here, so the tuples are the model of the local genera.
* `oddHasse` (**Lemma 2.2**): $c_{\mathfrak p} = \varepsilon_1^{a+b}\varepsilon_2^b\varepsilon_3^a(\varepsilon')^{ab}$,
  with the special cases (4)–(6); `lemma_2_2_padic` **proves** the formula from the definition
  $c_p = \prod_{i<j}(a_i, a_j)_p$ over $\mathbb{Q}_p$ ($F = \mathbb{Q}$, $p$ odd).
* `invLocalDensity`, `normDensity` (**Lemma 2.3**, the Conway–Sloane local mass formula, cited): the reciprocal local
  density of a Jordan decomposition. *Erratum (proposed by the formalization):* the paper prints
  the factor $q^{2\operatorname{ord}_{\mathfrak p}(\det_G Q)}$; the exponent must be $-2\operatorname{ord}_{\mathfrak p}
  (\det_G Q)$, which is what Table 1 uses (`normDensity_case4`: $(1-q^{-2})/(4q^{2a+b})$; with the printed sign it would
  be $(1-q^{-2})q^{2a+3b}/4$).
* `Mstar`, `Astar`, `Bstar`: the normalized local mass sums $M^{*,\pm}_{\mathfrak p}(S)$ and
  $A^*_{\mathfrak p} = M^{*,+} + M^{*,-}$, $B^*_{\mathfrak p} = M^{*,+} - M^{*,-}$ of paper 6 (Hanke 2011,
  *The structure of masses…*, Def. 4.6, p. 16), computed over the tuples of Lemma 2.1.
* **Theorem 2.4**: Table 1 (`normDensity_case1` … `normDensity_case4`, the Hasse invariant counts
  `table1_case2a` … `table1_case4b`) and Table 2 (`table2_A`, `table2_B`, and `Astar_eq_sum`, `Bstar_eq_sum`).
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Series
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

namespace QuadFormsKB.Hanke2011Ternary

open Finset

/-! ## Lemma 2.1: the tuples parametrizing local genera -/

/-- **The constraints of Lemma 2.1** (Hanke 2011, p. 4) on a tuple $T_{\mathfrak p} = (a, b; u_1, u_2, u_3)$, with
the unit square classes $u_i$ represented by their Legendre symbols `e₁ e₂ e₃ : ℤˣ`:
$0 \le a \le b$, and
(1) $0 = a = b \Rightarrow u_1 = u_2 = 1$; (2) $0 = a \ne b \Rightarrow u_1 = 1$; (3) $0 \ne a = b \Rightarrow u_2 = 1$.
The tuple stands for the diagonal form $u_1x^2 + \pi^a u_2y^2 + \pi^b u_3z^2$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, (1)–(3), pp. 4–5"]
def IsJordanTuple (a b : ℕ) (e₁ e₂ _e₃ : ℤˣ) : Prop :=
  a ≤ b ∧ (a = 0 → b = 0 → e₁ = 1 ∧ e₂ = 1) ∧ (a = 0 → b ≠ 0 → e₁ = 1) ∧ (a ≠ 0 → a = b → e₂ = 1)

instance (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : Decidable (IsJordanTuple a b e₁ e₂ e₃) := by
  unfold IsJordanTuple; infer_instance

/-- **The unit decorations of the valuations $(a, b)$ with determinant unit $u$** (Lemma 2.1): the triples
$(u_1, u_2, u_3)$ (as Legendre symbols) with $(a, b; u_1, u_2, u_3)$ satisfying the constraints of Lemma 2.1 and
$u_1u_2u_3 = u$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, p. 5"]
def unitChoices (a b : ℕ) (u : ℤˣ) : Finset (ℤˣ × ℤˣ × ℤˣ) :=
  univ.filter fun e => IsJordanTuple a b e.1 e.2.1 e.2.2 ∧ e.1 * e.2.1 * e.2.2 = u

/-- **The local genera of Gram determinant square class $S = \pi^\nu u$** (Lemma 2.1, p. 5): the tuples
$((a, b), (u_1, u_2, u_3))$ satisfying the constraints of Lemma 2.1 with $a + b = \nu$ and $u_1u_2u_3 = u$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.1, p. 5"]
def oddGenera (ν : ℕ) (u : ℤˣ) : Finset ((ℕ × ℕ) × ℤˣ × ℤˣ × ℤˣ) :=
  (antidiagonal ν ×ˢ univ).filter fun t =>
    IsJordanTuple t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 ∧ t.2.1 * t.2.2.1 * t.2.2.2 = u

/-! ## Lemma 2.2: the Hasse invariant -/

/-- **The Hasse invariant of the tuple $T_{\mathfrak p}$** (Lemma 2.2, p. 5):
$$c_{\mathfrak p} = \left(\tfrac{u_1}{\mathfrak p}\right)^{a+b}\left(\tfrac{u_2}{\mathfrak p}\right)^{b}
\left(\tfrac{u_3}{\mathfrak p}\right)^{a}\left(\tfrac{-1}{\mathfrak p}\right)^{ab}
= \varepsilon_1^{a+b}\varepsilon_2^b\varepsilon_3^a(\varepsilon')^{ab}.$$
Fields of the arguments: `ε'` $= \left(\frac{-1}{\mathfrak p}\right)$, `a b` the valuations, `e₁ e₂ e₃` the Legendre
symbols $\varepsilon_i$ of $u_i$. `lemma_2_2_padic` proves this from $c_p := \prod_{i<j}(a_i, a_j)_p$ over
$\mathbb{Q}_p$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, p. 5"]
def oddHasse (ε' : ℤˣ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : ℤˣ :=
  e₁ ^ (a + b) * e₂ ^ b * e₃ ^ a * ε' ^ (a * b)

theorem units_pow_even {e : ℤˣ} {n : ℕ} (h : Even n) : e ^ n = 1 := by
  obtain ⟨k, rfl⟩ := h; rw [← two_mul, pow_mul, Int.units_sq, one_pow]

theorem units_pow_odd {e : ℤˣ} {n : ℕ} (h : Odd n) : e ^ n = e := by
  obtain ⟨k, rfl⟩ := h; rw [pow_succ, pow_mul, Int.units_sq, one_pow, one_mul]

/-- **Lemma 2.2, (4):** $0 = a = b \Rightarrow c_{\mathfrak p} = 1$. -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, (4), p. 5"]
theorem oddHasse_case1 (ε' e₁ e₂ e₃ : ℤˣ) : oddHasse ε' 0 0 e₁ e₂ e₃ = 1 := by
  simp [oddHasse]

/-- **Lemma 2.2, (5):** $0 = a < b \Rightarrow c_{\mathfrak p} = \varepsilon_2^b$ (for tuples, $u_1 = 1$). -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, (5), p. 5"]
theorem oddHasse_case2 (ε' e₂ e₃ : ℤˣ) (b : ℕ) : oddHasse ε' 0 b 1 e₂ e₃ = e₂ ^ b := by
  simp [oddHasse]

/-- **Lemma 2.2, (6):** $0 < a = b \Rightarrow c_{\mathfrak p} = \left(\frac{-1}{\mathfrak p}\right)^b\varepsilon_3^b$
(for tuples, $u_2 = 1$). -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, (6), p. 5"]
theorem oddHasse_case3 (ε' e₁ e₃ : ℤˣ) (b : ℕ) : oddHasse ε' b b e₁ 1 e₃ = ε' ^ b * e₃ ^ b := by
  have h1 : e₁ ^ (b + b) = 1 := by rw [← two_mul, pow_mul, Int.units_sq, one_pow]
  have h2 : ε' ^ (b * b) = ε' ^ b := by
    rcases Nat.even_or_odd b with h | h
    · rw [units_pow_even h, units_pow_even (h.mul_right b)]
    · rw [units_pow_odd h, units_pow_odd (h.mul h)]
  simp only [oddHasse, h1, h2, one_pow, one_mul]
  exact mul_comm _ _

open QuadFormsKB.HilbertLocal in
/-- **Lemma 2.2 over $\mathbb{Q}_p$** (Hanke 2011, p. 5; the case $F = \mathbb{Q}$, $p$ odd, $\pi_p = p$): for
$p$-adic units $u_1, u_2, u_3$ and $a, b \ge 0$, the Hasse invariant
$c_p = \prod_{i<j}(a_i, a_j)_p$ of $\langle u_1, p^a u_2, p^b u_3\rangle$ is
$$c_p = \left(\tfrac{u_1}{p}\right)^{a+b}\left(\tfrac{u_2}{p}\right)^{b}\left(\tfrac{u_3}{p}\right)^{a}
\left((-1)^{(p-1)/2}\right)^{ab},$$
with $(-1)^{(p-1)/2} = \left(\frac{-1}{p}\right)$. Here `unitChar u` is the Legendre symbol of the residue of $u$, and
the Hilbert symbols are `hilbertSymbol ℚ_[p]` (the repository's Hasse invariant convention, $i < j$). -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, p. 5 (over Q_p)"]
theorem lemma_2_2_padic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (a b : ℕ) (u₁ u₂ u₃ : ℤ_[p]ˣ) :
    hilbertSymbol ℚ_[p] ((u₁ : ℤ_[p]) : ℚ_[p]) ((p : ℚ_[p]) ^ a * ((u₂ : ℤ_[p]) : ℚ_[p])) *
      hilbertSymbol ℚ_[p] ((u₁ : ℤ_[p]) : ℚ_[p]) ((p : ℚ_[p]) ^ b * ((u₃ : ℤ_[p]) : ℚ_[p])) *
      hilbertSymbol ℚ_[p] ((p : ℚ_[p]) ^ a * ((u₂ : ℤ_[p]) : ℚ_[p]))
        ((p : ℚ_[p]) ^ b * ((u₃ : ℤ_[p]) : ℚ_[p])) =
      unitChar u₁ ^ (a + b) * unitChar u₂ ^ b * unitChar u₃ ^ a * ((-1) ^ ((p - 1) / 2)) ^ (a * b) := by
  have e₀ : ((u₁ : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ 0 * ((u₁ : ℤ_[p]) : ℚ_[p]) := by simp
  rw [e₀, hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2, hilbertSymbol_odd_formula hp2]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  rw [← pow_mul, show a * b * ((p - 1) / 2) = (p - 1) / 2 * (a * b) by ring, pow_add]
  ring

/-! ## Lemma 2.3: the local mass formula -/

/-- **A Jordan component** $\pi^{\alpha}Q_i$ of a quadratic form over $\mathcal O_{\mathfrak p}$, $\mathfrak p \nmid 2$
(Lemma 2.3, p. 5). Fields:
* `scale` $= \alpha_i$, the $\pi$-power scaling the unimodular form $Q_i$;
* `dim` $= n_i = \dim Q_i$;
* `chi` $= \chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right)$ where $u$ is the determinant square class of
  $Q_i$ (used only when $n_i = 2$). -/
structure JordanBlock where
  /-- The scale exponent $\alpha_i$. -/
  scale : ℕ
  /-- The dimension $n_i$. -/
  dim : ℕ
  /-- $\chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right)$, $u$ the determinant of the unimodular block. -/
  chi : ℤ

/-- **The local mass factor $M_{\mathfrak p}(Q_i)$** (Lemma 2.3, p. 6): $1$ if $n_i = 0$, $\frac12$ if $n_i = 1$,
$\frac{1}{2(1 - \chi_u(\mathfrak p)/q)}$ if $n_i = 2$, $\frac{1}{2(1 - 1/q^2)}$ if $n_i = 3$ (the paper defines it only
for $n_i \le 3$; Lean returns $0$ for $n_i > 3$). -/
@[kb "hanke2011ternary" "§2, Lemma 2.3, p. 6"]
noncomputable def localMassFactor (q : ℚ) (B : JordanBlock) : ℚ :=
  match B.dim with
  | 0 => 1
  | 1 => 1 / 2
  | 2 => 1 / (2 * (1 - B.chi * q⁻¹))
  | 3 => 1 / (2 * (1 - q⁻¹ ^ 2))
  | _ => 0

/-- **The reciprocal local density $\beta_{Q,\mathfrak p}(Q)^{-1}$ of a ternary Jordan decomposition**
$Q \cong \bigoplus_i \pi^{\alpha_i} Q_i$ (Lemma 2.3, p. 5–6, from Conway–Sloane 1988, eq. (3), p. 263), for a list
`J` of Jordan components with non-decreasing scales:
$$\beta_{Q,\mathfrak p}(Q)^{-1} = q^{-2\operatorname{ord}_{\mathfrak p}(\det_G Q)} \cdot 2 \prod_i M_{\mathfrak p}(Q_i)
\cdot \prod_{i<j} q^{\frac{(\alpha_j - \alpha_i) n_i n_j}{2}},
\qquad \operatorname{ord}_{\mathfrak p}(\det_G Q) = \sum_i \alpha_i n_i.$$
*Erratum (proposed by the formalization):* the paper prints $q^{+2\operatorname{ord}_{\mathfrak p}
(\det_G Q)}$; Table 1 (and Conway–Sloane's normalization) need the exponent $-2\operatorname{ord}_{\mathfrak p}
(\det_G Q)$, used here. The exponents $\frac{(\alpha_j-\alpha_i)n_in_j}{2}$ are combined into one integer exponent
(`Int` division by $2$); for $n = \sum n_i = 3$ the sum $\sum_{i<j}(\alpha_j-\alpha_i)n_in_j$ is always even. -/
@[kb "hanke2011ternary" "§2, Lemma 2.3, pp. 5–6 (exponent sign corrected)"]
noncomputable def invLocalDensity (q : ℚ) (J : List JordanBlock) : ℚ :=
  q ^ (-(2 * ((J.map fun B => (B.scale * B.dim : ℤ)).sum))) * 2 * (J.map (localMassFactor q)).prod *
    q ^ ((∑ i : Fin J.length, ∑ j : Fin J.length,
      if i < j then (((J.get j).scale : ℤ) - (J.get i).scale) * (J.get i).dim * (J.get j).dim else 0) / 2)

/-- **The Jordan decomposition of the tuple $T_{\mathfrak p}$** (proof of Lemma 2.1): the form
$u_1x^2 + \pi^a u_2y^2 + \pi^b u_3z^2$ has Jordan components $[\,(0,3)\,]$ if $0 = a = b$;
$[\,(0, 2, \chi), (b, 1)\,]$ with $\chi = \left(\frac{-u_1u_2}{\mathfrak p}\right) = \varepsilon'\varepsilon_1\varepsilon_2$
if $0 = a < b$; $[\,(0,1), (a, 2, \chi)\,]$ with $\chi = \varepsilon'\varepsilon_2\varepsilon_3$ if $0 < a = b$;
$[\,(0,1), (a,1), (b,1)\,]$ if $0 < a < b$. -/
def jordanBlocks (ε' : ℤˣ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : List JordanBlock :=
  if a = 0 ∧ b = 0 then [⟨0, 3, 0⟩]
  else if a = 0 then [⟨0, 2, ((ε' * e₁ * e₂ : ℤˣ) : ℤ)⟩, ⟨b, 1, 0⟩]
  else if a = b then [⟨0, 1, 0⟩, ⟨a, 2, ((ε' * e₂ * e₃ : ℤˣ) : ℤ)⟩]
  else [⟨0, 1, 0⟩, ⟨a, 1, 0⟩, ⟨b, 1, 0⟩]

/-- **The normalized local density** $(1 - q^{-2})\,\beta_{Q,\mathfrak p}(Q)^{-1}$ of the local genus of the tuple
$T_{\mathfrak p}$ (Table 1, last column, p. 6). Since the generic (unimodular) density is $(1-q^{-2})^{-1}$
(`normDensity_case1`), this is the ratio $\beta_{3,\mathfrak p}(\widetilde S)/\beta_{G,\mathfrak p}(G)$ of paper 6,
Def. 4.6. -/
@[kb "hanke2011ternary" "§2, Table 1, p. 6"]
noncomputable def normDensity (q : ℚ) (ε' : ℤˣ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) : ℚ :=
  (1 - q⁻¹ ^ 2) * invLocalDensity q (jordanBlocks ε' a b e₁ e₂ e₃)

/-! ## Theorem 2.4, Table 1: normalized densities -/

theorem jordanBlocks_case1 (ε' e₁ e₂ e₃ : ℤˣ) : jordanBlocks ε' 0 0 e₁ e₂ e₃ = [⟨0, 3, 0⟩] := by
  simp [jordanBlocks]

theorem jordanBlocks_case2 (ε' e₁ e₂ e₃ : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    jordanBlocks ε' 0 b e₁ e₂ e₃ = [⟨0, 2, ((ε' * e₁ * e₂ : ℤˣ) : ℤ)⟩, ⟨b, 1, 0⟩] := by
  simp [jordanBlocks, hb]

theorem jordanBlocks_case3 (ε' e₁ e₂ e₃ : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    jordanBlocks ε' b b e₁ e₂ e₃ = [⟨0, 1, 0⟩, ⟨b, 2, ((ε' * e₂ * e₃ : ℤˣ) : ℤ)⟩] := by
  simp [jordanBlocks, hb]

theorem jordanBlocks_case4 (ε' e₁ e₂ e₃ : ℤˣ) {a b : ℕ} (ha : a ≠ 0) (hab : a ≠ b) :
    jordanBlocks ε' a b e₁ e₂ e₃ = [⟨0, 1, 0⟩, ⟨a, 1, 0⟩, ⟨b, 1, 0⟩] := by
  simp [jordanBlocks, ha, hab]

section Table1

variable {q : ℚ} (hq : 1 < q)
include hq

/-- **Table 1, case 1** ($0 = a = b$, $\nu = 0$): the normalized density is $1$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, case 1, p. 6"]
theorem normDensity_case1 (ε' e₁ e₂ e₃ : ℤˣ) : normDensity q ε' 0 0 e₁ e₂ e₃ = 1 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hq4 : 1 + q ≠ 0 := by linarith
  rw [normDensity, jordanBlocks_case1]
  simp [invLocalDensity, localMassFactor]
  field_simp

/-- **Table 1, case 2** ($0 = a < b$, Jordan type $(2,1)$): the normalized density is
$\dfrac{1 + \varepsilon'\varepsilon_1\varepsilon_2/q}{2q^b}$ (for tuples $\varepsilon_1 = 1$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 2a–2b, p. 6"]
theorem normDensity_case2 (ε' e₁ e₂ e₃ : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    normDensity q ε' 0 b e₁ e₂ e₃ = (1 + ((ε' * e₁ * e₂ : ℤˣ) : ℤ) * q⁻¹) * q⁻¹ ^ b / 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hq4 : 1 + q ≠ 0 := by linarith
  rw [normDensity, jordanBlocks_case2 _ _ _ _ hb]
  simp [invLocalDensity, Fin.sum_univ_two, localMassFactor]
  rw [show (2 * (b : ℤ)) = ((2 * b : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rcases Int.units_eq_one_or (ε' * e₁ * e₂) with h | h <;>
  · have h' := congrArg (fun x : ℤˣ => ((x : ℤ) : ℚ)) h
    push_cast at h'
    rw [h']
    have key : (q ^ 2 - 1) * (1 + q)⁻¹ = q - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (1 + q) by ring, mul_assoc, mul_inv_cancel₀ hq4, mul_one]
    field_simp
    first | ring1 | linear_combination (q ^ (b * 2)) * key | linear_combination (q ^ (b * 4)) * key

/-- **Table 1, case 3** ($0 < a = b$, Jordan type $(1,2)$): the normalized density is
$\dfrac{1 + \varepsilon'\varepsilon_2\varepsilon_3/q}{2q^{3b}}$ (for tuples $\varepsilon_2 = 1$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 3a–3b, p. 6"]
theorem normDensity_case3 (ε' e₁ e₂ e₃ : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    normDensity q ε' b b e₁ e₂ e₃ = (1 + ((ε' * e₂ * e₃ : ℤˣ) : ℤ) * q⁻¹) * q⁻¹ ^ (3 * b) / 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hq4 : 1 + q ≠ 0 := by linarith
  rw [normDensity, jordanBlocks_case3 _ _ _ _ hb]
  simp [invLocalDensity, Fin.sum_univ_two, localMassFactor]
  rw [show (2 * ((b : ℤ) * 2)) = ((4 * b : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  rcases Int.units_eq_one_or (ε' * e₂ * e₃) with h | h <;>
  · have h' := congrArg (fun x : ℤˣ => ((x : ℤ) : ℚ)) h
    push_cast at h'
    rw [h']
    have key : (q ^ 2 - 1) * (1 + q)⁻¹ = q - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (1 + q) by ring, mul_assoc, mul_inv_cancel₀ hq4, mul_one]
    field_simp
    first | ring1 | linear_combination (q ^ (b * 2)) * key | linear_combination (q ^ (b * 4)) * key

/-- **Table 1, case 4** ($0 < a < b$, Jordan type $(1,1,1)$): the normalized density is
$\dfrac{1 - q^{-2}}{4q^{2a+b}}$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 4a–4b, p. 6"]
theorem normDensity_case4 (ε' e₁ e₂ e₃ : ℤˣ) {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    normDensity q ε' a b e₁ e₂ e₃ = (1 - q⁻¹ ^ 2) * q⁻¹ ^ (2 * a + b) / 4 := by
  have hq0 : q ≠ 0 := by positivity
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  have hq2 : q + 1 ≠ 0 := by linarith
  have hq3 : q ^ 2 - 1 ≠ 0 := by nlinarith
  have hq4 : 1 + q ≠ 0 := by linarith
  have e : ∀ z : ℤ, z = 2 * b → z / 2 = b := by intro z hz; omega
  rw [normDensity, jordanBlocks_case4 _ _ _ _ ha (by omega)]
  simp [invLocalDensity, Fin.sum_univ_three, localMassFactor]
  rw [e _ (by split_ifs with h0 <;> first | ring1 | (simp at h0) | omega), show (2 * ((a : ℤ) + b)) = ((2 * a + 2 * b : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, zpow_natCast]
  field_simp
  ring

end Table1

/-! ## Theorem 2.4, Table 1: distribution of Hasse invariants -/

/-- The unit choices for $0 = a = b$ (Lemma 2.1, constraint (1)): $u_1 = u_2 = 1$, $u_3 = u$. -/
theorem unitChoices_case1 (u : ℤˣ) : unitChoices 0 0 u = {(1, 1, u)} := by
  ext ⟨e₁, e₂, e₃⟩
  constructor
  · intro h
    simp only [unitChoices, mem_filter, mem_univ, true_and] at h
    obtain ⟨⟨-, h1, -⟩, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h1 rfl rfl
    simp
  · intro h
    simp only [mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [unitChoices, IsJordanTuple]

/-- The unit choices for $0 = a < b$ (Lemma 2.1, constraint (2)): $u_1 = 1$, $u_2$ free, $u_3 = u u_2$. -/
theorem unitChoices_case2 {b : ℕ} (hb : b ≠ 0) (u : ℤˣ) :
    unitChoices 0 b u = {(1, 1, u), (1, -1, -u)} := by
  ext ⟨e₁, e₂, e₃⟩
  constructor
  · intro h
    simp only [unitChoices, mem_filter, mem_univ, true_and] at h
    obtain ⟨⟨-, -, h1, -⟩, rfl⟩ := h
    obtain rfl := h1 rfl hb
    rcases Int.units_eq_one_or e₂ with rfl | rfl <;> simp
  · intro h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [unitChoices, IsJordanTuple, hb]

/-- The unit choices for $0 < a = b$ (Lemma 2.1, constraint (3)): $u_2 = 1$, $u_3$ free, $u_1 = u u_3$. -/
theorem unitChoices_case3 {b : ℕ} (hb : b ≠ 0) (u : ℤˣ) :
    unitChoices b b u = {(u, 1, 1), (-u, 1, -1)} := by
  ext ⟨e₁, e₂, e₃⟩
  constructor
  · intro h
    simp only [unitChoices, mem_filter, mem_univ, true_and] at h
    obtain ⟨⟨-, -, -, h1⟩, rfl⟩ := h
    obtain rfl := h1 hb rfl
    rcases Int.units_eq_one_or e₃ with rfl | rfl <;> simp
  · intro h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [unitChoices, IsJordanTuple, hb]

/-- The unit choices for $0 < a < b$: $u_1, u_2$ free, $u_3 = u u_1 u_2$ (four choices). -/
theorem unitChoices_case4 {a b : ℕ} (ha : a ≠ 0) (hab : a < b) (u : ℤˣ) :
    unitChoices a b u = {(1, 1, u), (1, -1, -u), (-1, 1, -u), (-1, -1, u)} := by
  have hab' : a ≠ b := by omega
  ext ⟨e₁, e₂, e₃⟩
  constructor
  · intro h
    simp only [unitChoices, mem_filter, mem_univ, true_and] at h
    obtain ⟨-, rfl⟩ := h
    rcases Int.units_eq_one_or e₁ with rfl | rfl <;> rcases Int.units_eq_one_or e₂ with rfl | rfl <;> simp
  · intro h
    simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      simp [unitChoices, IsJordanTuple, ha, hab', hab.le]

/-- The number of local genera of valuation type $(a, b)$ and unit $u$ with Hasse invariant $c$. -/
def hasseCount (ε' : ℤˣ) (a b : ℕ) (u c : ℤˣ) : ℕ :=
  ((unitChoices a b u).filter fun e => oddHasse ε' a b e.1 e.2.1 e.2.2 = c).card

/-- **Table 1, case 1** ($\nu = 0$): one genus (for $u = $ the determinant unit), with $c_{\mathfrak p} = 1$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, case 1, p. 6"]
theorem table1_case1 (ε' u : ℤˣ) : hasseCount ε' 0 0 u 1 = 1 ∧ hasseCount ε' 0 0 u (-1) = 0 := by
  simp only [hasseCount, unitChoices_case1, filter_singleton, oddHasse_case1]
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

/-- **Table 1, cases 2a–2b** ($0 = a < b$): if $b$ is even, both genera have $c_{\mathfrak p} = 1$; if $b$ is odd,
one has $c_{\mathfrak p} = 1$ ($\varepsilon_2 = 1$) and one has $c_{\mathfrak p} = -1$ ($\varepsilon_2 = -1$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 2a–2b, p. 6"]
theorem table1_case2 (ε' u : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    (Even b → hasseCount ε' 0 b u 1 = 2 ∧ hasseCount ε' 0 b u (-1) = 0) ∧
    (Odd b → hasseCount ε' 0 b u 1 = 1 ∧ hasseCount ε' 0 b u (-1) = 1) := by
  simp only [hasseCount, unitChoices_case2 hb, filter_insert, filter_singleton, oddHasse_case2]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [units_pow_even h]
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  · simp only [units_pow_odd h]
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide

/-- **Table 1, cases 3a–3b** ($0 < a = b$): if $b$ is even, both genera have $c_{\mathfrak p} = 1$; if $b$ is odd,
one has $c_{\mathfrak p} = 1$ ($\varepsilon_3 = \varepsilon'$) and one has $c_{\mathfrak p} = -1$
($\varepsilon_3 = -\varepsilon'$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 3a–3b, p. 6"]
theorem table1_case3 (ε' u : ℤˣ) {b : ℕ} (hb : b ≠ 0) :
    (Even b → hasseCount ε' b b u 1 = 2 ∧ hasseCount ε' b b u (-1) = 0) ∧
    (Odd b → hasseCount ε' b b u 1 = 1 ∧ hasseCount ε' b b u (-1) = 1) := by
  simp only [hasseCount, unitChoices_case3 hb, filter_insert, filter_singleton, oddHasse_case3]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [units_pow_even h, one_mul]
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  · simp only [units_pow_odd h]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;> decide

/-- **Table 1, cases 4a–4b** ($0 < a < b$): if $a \equiv b \equiv 0 \pmod 2$, all four genera have
$c_{\mathfrak p} = 1$; otherwise two have $c_{\mathfrak p} = 1$ and two have $c_{\mathfrak p} = -1$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 1, cases 4a–4b, p. 6"]
theorem table1_case4 (ε' u : ℤˣ) {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    (Even a ∧ Even b → hasseCount ε' a b u 1 = 4 ∧ hasseCount ε' a b u (-1) = 0) ∧
    (¬ (Even a ∧ Even b) → hasseCount ε' a b u 1 = 2 ∧ hasseCount ε' a b u (-1) = 2) := by
  simp only [hasseCount, unitChoices_case4 ha hab, filter_insert, filter_singleton, oddHasse]
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun h => ?_⟩
  · simp only [units_pow_even h1, units_pow_even h2, units_pow_even (h1.add h2), units_pow_even (h1.mul_right b)]
    rcases Int.units_eq_one_or u with rfl | rfl <;> decide
  · rcases Nat.even_or_odd a with h1 | h1 <;> rcases Nat.even_or_odd b with h2 | h2
    · exact absurd ⟨h1, h2⟩ h
    · simp only [units_pow_even h1, units_pow_odd h2, units_pow_odd (h1.add_odd h2),
        units_pow_even (h1.mul_right b)]
      rcases Int.units_eq_one_or u with rfl | rfl <;> decide
    · simp only [units_pow_odd h1, units_pow_even h2, units_pow_odd (h1.add_even h2),
        units_pow_even (h2.mul_left a)]
      rcases Int.units_eq_one_or u with rfl | rfl <;> decide
    · simp only [units_pow_odd h1, units_pow_odd h2, units_pow_even (h1.add_odd h2), units_pow_odd (h1.mul h2)]
      rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;> decide

/-! ## Theorem 2.4, Table 2: contributions to $A^*_{\mathfrak p}$ and $B^*_{\mathfrak p}$ -/

/-- **The normalized local mass sum $\widetilde M^{*,c}_{\mathfrak p}(S)$** (paper 6, Def. 4.6, p. 16) for
$\mathfrak p \nmid 2$ and $S = \pi^\nu u$: the sum of the normalized densities
$\beta_{3,\mathfrak p}(\widetilde S)/\beta_{G,\mathfrak p}(G) = (1 - q^{-2})\beta_{G,\mathfrak p}(G)^{-1}$ over the local
genera $G$ (tuples of Lemma 2.1) of determinant $S$ with Hasse invariant $c_{\mathfrak p}(G) = c$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, p. 6 (paper 6, Def. 4.6)"]
noncomputable def Mstar (q : ℚ) (ε' : ℤˣ) (ν : ℕ) (u c : ℤˣ) : ℚ :=
  ∑ t ∈ (oddGenera ν u).filter (fun t => oddHasse ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 = c),
    normDensity q ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2

/-- **$A^*_{\mathfrak p}(S) := \widetilde M^{*,+}_{\mathfrak p}(S) + \widetilde M^{*,-}_{\mathfrak p}(S)$**
(paper 6, Def. 4.6), for $\mathfrak p \nmid 2$, $S = \pi^\nu u$, $n = 3$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (paper 6, Def. 4.6)"]
noncomputable def Astar (q : ℚ) (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) : ℚ := Mstar q ε' ν u 1 + Mstar q ε' ν u (-1)

/-- **$B^*_{\mathfrak p}(S) := \widetilde M^{*,+}_{\mathfrak p}(S) - \widetilde M^{*,-}_{\mathfrak p}(S)$**
(paper 6, Def. 4.6), for $\mathfrak p \nmid 2$, $S = \pi^\nu u$, $n = 3$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7 (paper 6, Def. 4.6)"]
noncomputable def Bstar (q : ℚ) (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) : ℚ := Mstar q ε' ν u 1 - Mstar q ε' ν u (-1)

theorem oddHasse_eq_one_or (ε' : ℤˣ) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) :
    oddHasse ε' a b e₁ e₂ e₃ = 1 ∨ oddHasse ε' a b e₁ e₂ e₃ = -1 := Int.units_eq_one_or _

/-- $A^*_{\mathfrak p}(S)$ is the sum of the normalized densities of all local genera of determinant $S$. -/
theorem Astar_eq (q : ℚ) (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) :
    Astar q ε' ν u = ∑ t ∈ oddGenera ν u, normDensity q ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 := by
  rw [Astar, Mstar, Mstar, ← Finset.sum_union]
  · congr 1; ext t; simp only [mem_union, mem_filter]
    rcases oddHasse_eq_one_or ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 with h | h <;> simp [h]
  · rw [Finset.disjoint_filter]; intro t _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)

/-- $B^*_{\mathfrak p}(S)$ is the sum of $c_{\mathfrak p}(G)$ times the normalized density, over the local genera $G$
of determinant $S$. -/
theorem Bstar_eq (q : ℚ) (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) :
    Bstar q ε' ν u = ∑ t ∈ oddGenera ν u, ((oddHasse ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 : ℤ) : ℚ) *
      normDensity q ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 := by
  rw [Bstar, Mstar, Mstar, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rcases oddHasse_eq_one_or ε' t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 with h | h <;> simp [h]

/-- The sum over local genera of determinant $\pi^\nu u$ splits as a sum over valuation types $(a, b)$,
$a + b = \nu$, $a \le b$, of sums over unit choices. -/
theorem sum_oddGenera (ν : ℕ) (u : ℤˣ) (f : ℕ → ℕ → ℤˣ → ℤˣ → ℤˣ → ℚ) :
    ∑ t ∈ oddGenera ν u, f t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2 =
      ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2),
        ∑ e ∈ unitChoices ab.1 ab.2 u, f ab.1 ab.2 e.1 e.2.1 e.2.2 := by
  rw [oddGenera, Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [unitChoices, Finset.sum_filter]
  split_ifs with h
  · rfl
  · rw [Finset.sum_eq_zero]; intro e _; rw [if_neg]; rintro ⟨⟨h', -⟩, -⟩; exact h h'

/-- **Table 2, column $A^*_{\mathfrak p}$** (Hanke 2011, p. 7): the contribution of the valuation type $(a, b)$:
$1$ (case 1), $q^{-b}$ (case 2), $q^{-3b}$ (case 3), $(1 - q^{-2})q^{-(2a+b)}$ (case 4). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
noncomputable def rowA (q : ℚ) (a b : ℕ) : ℚ :=
  if a = 0 ∧ b = 0 then 1 else if a = 0 then q⁻¹ ^ b else if a = b then q⁻¹ ^ (3 * b)
  else (1 - q⁻¹ ^ 2) * q⁻¹ ^ (2 * a + b)

/-- **Table 2, column $B^*_{\mathfrak p}$** (Hanke 2011, p. 7): $1$ (case 1); $q^{-b}$ (2a, $b$ even),
$\varepsilon' q^{-(b+1)}$ (2b, $b$ odd); $q^{-3b}$ (3a, $b$ even), $q^{-(3b+1)}$ (3b, $b$ odd);
$(1 - q^{-2})q^{-(2a+b)}$ (4a, $a \equiv b \equiv 0 \pmod 2$), $0$ (4b, otherwise). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
noncomputable def rowB (q : ℚ) (ε' : ℤˣ) (a b : ℕ) : ℚ :=
  if a = 0 ∧ b = 0 then 1
  else if a = 0 then (if Even b then q⁻¹ ^ b else (ε' : ℤ) * q⁻¹ ^ (b + 1))
  else if a = b then (if Even b then q⁻¹ ^ (3 * b) else q⁻¹ ^ (3 * b + 1))
  else if Even a ∧ Even b then (1 - q⁻¹ ^ 2) * q⁻¹ ^ (2 * a + b) else 0

section Table2

variable {q : ℚ} (hq : 1 < q)
include hq

/-- **Theorem 2.4, Table 2, $A^*$ column** (p. 7): for each valuation type $(a, b)$ with $a \le b$, the sum of the
normalized densities over the unit choices of determinant unit $u$ is `rowA q a b` (independent of $u$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
theorem table2_A (ε' u : ℤˣ) {a b : ℕ} (hab : a ≤ b) :
    ∑ e ∈ unitChoices a b u, normDensity q ε' a b e.1 e.2.1 e.2.2 = rowA q a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by omega
    rw [unitChoices_case1, sum_singleton, normDensity_case1 hq]; simp [rowA]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [unitChoices_case2 (by omega), sum_pair (by simp), normDensity_case2 hq _ _ _ _ (by omega),
      normDensity_case2 hq _ _ _ _ (by omega)]
    simp only [rowA, show b ≠ 0 by omega, and_false, if_false, if_true]
    push_cast; ring
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [unitChoices_case3 (by omega), sum_pair (by simp), normDensity_case3 hq _ _ _ _ (by omega),
      normDensity_case3 hq _ _ _ _ (by omega)]
    simp only [rowA, show a ≠ 0 by omega, false_and, if_false, if_true]
    push_cast; ring
  · rw [unitChoices_case4 (by omega) hlt]
    rw [sum_insert (by simp), sum_insert (by simp), sum_pair (by simp)]
    simp only [normDensity_case4 hq _ _ _ _ (show a ≠ 0 by omega) hlt]
    simp only [rowA, show a ≠ 0 by omega, show a ≠ b by omega, false_and, if_false]
    ring

/-- **Theorem 2.4, Table 2, $B^*$ column** (p. 7): for each valuation type $(a, b)$ with $a \le b$, the sum of
$c_{\mathfrak p}$ times the normalized density over the unit choices of determinant unit $u$ is `rowB q ε' a b`
(independent of $u$). -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
theorem table2_B (ε' u : ℤˣ) {a b : ℕ} (hab : a ≤ b) :
    ∑ e ∈ unitChoices a b u, ((oddHasse ε' a b e.1 e.2.1 e.2.2 : ℤ) : ℚ) * normDensity q ε' a b e.1 e.2.1 e.2.2 =
      rowB q ε' a b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain rfl : a = 0 := by omega
    rw [unitChoices_case1, sum_singleton, normDensity_case1 hq, oddHasse_case1]; simp [rowB]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [unitChoices_case2 (by omega), sum_pair (by simp), normDensity_case2 hq _ _ _ _ (by omega),
      normDensity_case2 hq _ _ _ _ (by omega), oddHasse_case2, oddHasse_case2]
    simp only [rowB, show b ≠ 0 by omega, and_false, if_false, if_true]
    rcases Nat.even_or_odd b with h | h
    · rw [if_pos h, units_pow_even h, units_pow_even h]; push_cast; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr h), units_pow_odd h, units_pow_odd h]
      rcases Int.units_eq_one_or ε' with rfl | rfl <;> push_cast <;> ring
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [unitChoices_case3 (by omega), sum_pair (by simp), normDensity_case3 hq _ _ _ _ (by omega),
      normDensity_case3 hq _ _ _ _ (by omega), oddHasse_case3, oddHasse_case3]
    simp only [rowB, show a ≠ 0 by omega, false_and, if_false, if_true]
    rcases Nat.even_or_odd a with h | h
    · rw [if_pos h, units_pow_even h, units_pow_even h, units_pow_even h]; push_cast; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr h), units_pow_odd h, units_pow_odd h, units_pow_odd h]
      rcases Int.units_eq_one_or ε' with rfl | rfl <;> push_cast <;> ring
  · rw [unitChoices_case4 (by omega) hlt]
    rw [sum_insert (by simp), sum_insert (by simp), sum_pair (by simp)]
    simp only [normDensity_case4 hq _ _ _ _ (show a ≠ 0 by omega) hlt]
    simp only [rowB, show a ≠ 0 by omega, show a ≠ b by omega, false_and, if_false]
    rw [← add_mul, ← add_mul, ← add_mul]
    congr 1
    simp only [oddHasse]
    rcases Nat.even_or_odd a with h1 | h1 <;> rcases Nat.even_or_odd b with h2 | h2
    · simp only [units_pow_even h1, units_pow_even h2, units_pow_even (h1.add h2),
        units_pow_even (h1.mul_right b), if_pos (And.intro h1 h2)]
      norm_num <;> ring_nf
    · simp only [units_pow_even h1, units_pow_odd h2, units_pow_odd (h1.add_odd h2),
        units_pow_even (h1.mul_right b), Nat.not_even_iff_odd.mpr h2, and_false, if_false]
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num <;> ring_nf
    · simp only [units_pow_odd h1, units_pow_even h2, units_pow_odd (h1.add_even h2),
        units_pow_even (h2.mul_left a), Nat.not_even_iff_odd.mpr h1, false_and, if_false]
      rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num <;> ring_nf
    · simp only [units_pow_odd h1, units_pow_odd h2, units_pow_even (h1.add_odd h2), units_pow_odd (h1.mul h2),
        Nat.not_even_iff_odd.mpr h1, false_and, if_false]
      rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;> norm_num <;> ring_nf

/-- **Theorem 2.4** (Table 2, summed): $A^*_{\mathfrak p}(\pi^\nu u) = \sum_{a+b=\nu,\ a\le b}$ `rowA q a b`;
in particular it does not depend on the unit $u$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
theorem Astar_eq_sum (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) :
    Astar q ε' ν u = ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2), rowA q ab.1 ab.2 := by
  rw [Astar_eq, sum_oddGenera ν u (fun a b e₁ e₂ e₃ => normDensity q ε' a b e₁ e₂ e₃)]
  refine Finset.sum_congr rfl fun ab hab => ?_
  exact table2_A hq ε' u (mem_filter.mp hab).2

/-- **Theorem 2.4** (Table 2, summed): $B^*_{\mathfrak p}(\pi^\nu u) = \sum_{a+b=\nu,\ a\le b}$ `rowB q ε' a b`;
in particular it does not depend on the unit $u$. -/
@[kb "hanke2011ternary" "§2, Thm. 2.4, Table 2, p. 7"]
theorem Bstar_eq_sum (ε' : ℤˣ) (ν : ℕ) (u : ℤˣ) :
    Bstar q ε' ν u = ∑ ab ∈ (antidiagonal ν).filter (fun ab => ab.1 ≤ ab.2), rowB q ε' ab.1 ab.2 := by
  rw [Bstar_eq, sum_oddGenera ν u (fun a b e₁ e₂ e₃ => ((oddHasse ε' a b e₁ e₂ e₃ : ℤ) : ℚ) *
    normDensity q ε' a b e₁ e₂ e₃)]
  refine Finset.sum_congr rfl fun ab hab => ?_
  exact table2_B hq ε' u (mem_filter.mp hab).2

end Table2

end QuadFormsKB.Hanke2011Ternary
