/-
# Chenevier–Lannes, Theorem A at $p = 2, 3$ and the neighbour graph $K_{16}(p)$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.2, pp. 3–4 (Theorem A; "$K_{16}(p)$ is the connected graph
with $2$ vertices … compatible with the bound $|\tau(p)| < 2p^{11/2}$ (Deligne–Ramanujan)"), §3.3.1–3.3.2, pp. 57–59
(the matrices of $T_2$ and $T_3$ on $\mathbb{Z}[X_{16}]$). Printed page numbers.

**Layer.** Earlier files (`TheoremsAB.lean`: `TheoremA`, `thmAScalar`, `HeckeTwoSixteen`, `HeckeThreeSixteen`), and
(`Consequences.lean`: `theoremA_odd_iff`, `neighborGraphConnected_sixteen_of_pos`). Ramanujan's $\tau$ is
`Lattices.ramanujanTau`, the $q$-expansion coefficients of Mathlib's `ModularForm.discriminant`.

**Proves** (unconditional unless said):
- `ramanujanTau_two`, `ramanujanTau_three`: $\tau(2) = -24$, $\tau(3) = 252$, from Mathlib's
  $1728\Delta = E_4^3 - E_6^2$ (`ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded`) and the Eisenstein
  coefficients. *Credit:* the argument is the one of Tau Ceti's `TauCeti.ModularForm.discriminant_qExpansion_coeff_two`
  and `_three` (`TauCeti/NumberTheory/ModularForms/LevelOne/QExpansion.lean`, commit d2083f0f), re-proved here
  without depending on Tau Ceti;
- `thmAScalar_two`, `thmAScalar_three`: the scalar of Theorem A is $45$ at $p = 2$ and $10240$ at $p = 3$;
- `theoremA_two_iff`, `theoremA_three_iff`: Theorem A at $p = 2$ (resp. $3$) is exactly the explicit matrix
  `HeckeTwoSixteen` (resp. `HeckeThreeSixteen`) of §3.3;
- `heckeThreeSixteen_iff`: `HeckeThreeSixteen` is equivalent to the single entry $N_3(E_8 \oplus E_8, E_{16}) = 4147200$;
- `neighborGraphConnected_sixteen_of_theoremA` (**conditional** on `TheoremA` and the named input `DeligneBound`):
  $K_{16}(p)$ is connected for every odd prime $p$.

**States** (named input): `DeligneBound`, Deligne's bound $|\tau(p)| \le 2p^{11/2}$ (the Ramanujan conjecture for
$\Delta$, proved by Deligne; not formalized).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Consequences
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open Matrix ModularForm

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Lattices

open EisensteinSeries UpperHalfPlane MatrixGroups

private theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by decide +kernel

private theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by decide +kernel

private theorem E₄_coeff_two' : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four', ArithmeticFunction.sigma_apply,
    Nat.prime_two.divisors]

private theorem E₄_coeff_three' : (qExpansion 1 E₄).coeff 3 = 6720 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, bernoulli_four', ArithmeticFunction.sigma_apply,
    Nat.prime_three.divisors]

private theorem E₆_coeff_two' : (qExpansion 1 E₆).coeff 2 = -16632 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six', ArithmeticFunction.sigma_apply,
    Nat.prime_two.divisors]

private theorem E₆_coeff_three' : (qExpansion 1 E₆).coeff 3 = -122976 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, bernoulli_six', ArithmeticFunction.sigma_apply,
    Nat.prime_three.divisors]

private theorem qExp_disc' :
    qExpansion 1 ModularForm.discriminant =
      (1728 : ℂ)⁻¹ • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  simpa [CuspForm.coe_discriminant] using congr(ModularForm.qExpansionAlgHom 1 one_pos
    one_mem_strictPeriods_SL $discriminant_eq_E₄_cube_sub_E₆_sq_graded)

/-- **$\tau(2) = -24$.** -/
theorem ramanujanTau_two : ramanujanTau 2 = -24 := by
  rw [ramanujanTau, qExp_disc']
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_coeff_two', E₆_coeff_two',
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- **$\tau(3) = 252$.** -/
theorem ramanujanTau_three : ramanujanTau 3 = 252 := by
  rw [ramanujanTau, qExp_disc']
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_coeff_two', E₆_coeff_two', E₄_coeff_three', E₆_coeff_three',
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- $c_{16}(2) = 2^{15} - 1 + 2^7 = 32895$. -/
theorem cn_sixteen_two : cn 16 2 = 32895 := by
  simp [cn, Finset.sum_range_succ]

/-- $c_{16}(3) = (3^{15} - 1)/2 + 3^7 = 7176640$. -/
theorem cn_sixteen_three : cn 16 3 = 7176640 := by
  simp [cn, Finset.sum_range_succ]

/-- The scalar of Theorem A at $p = 2$: $(1 + 2 + 4 + 8)(1 + 2^{11} + 24)/691 = 15 \cdot 3 = 45$. -/
theorem thmAScalar_two : thmAScalar 2 = 45 := by
  rw [thmAScalar, ramanujanTau_two]
  norm_num

/-- The scalar of Theorem A at $p = 3$: $(1 + 3 + 9 + 27)(1 + 3^{11} - 252)/691 = 40 \cdot 256 = 10240$. -/
theorem thmAScalar_three : thmAScalar 3 = 10240 := by
  rw [thmAScalar, ramanujanTau_three]
  norm_num

/-- **Theorem A at $p = 2$ is the matrix of §3.3.1** (Chenevier–Lannes, p. 3 and p. 57): the four equalities of
Theorem A at $p = 2$ hold iff $T_2 = \begin{pmatrix}20025&18225\\12870&14670\end{pmatrix}$ in the basis
$(E_{16}, E_8 \oplus E_8)$ (`HeckeTwoSixteen`). Unconditional (arithmetic: $c = 45$, $c_{16}(2) = 32895$). -/
@[kb "chenevierlannes2019" "Thm. A, p. 3, at p = 2; §3.3.1, p. 57"]
theorem theoremA_two_iff :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ((nbCount twoE8 2 (classOf twoE8) : ℂ) = cn 16 2 - 405 * thmAScalar 2 ∧
      (nbCount twoE8 2 (classOf gamma16) : ℂ) = 405 * thmAScalar 2 ∧
      (nbCount gamma16 2 (classOf twoE8) : ℂ) = 286 * thmAScalar 2 ∧
      (nbCount gamma16 2 (classOf gamma16) : ℂ) = cn 16 2 - 286 * thmAScalar 2) ↔ HeckeTwoSixteen := by
  unfold HeckeTwoSixteen
  rw [thmAScalar_two, cn_sixteen_two]
  have e1 : ((32895 : ℕ) : ℂ) - 405 * 45 = ((14670 : ℕ) : ℂ) := by norm_num
  have e2 : (405 : ℂ) * 45 = ((18225 : ℕ) : ℂ) := by norm_num
  have e3 : (286 : ℂ) * 45 = ((12870 : ℕ) : ℂ) := by norm_num
  have e4 : ((32895 : ℕ) : ℂ) - 286 * 45 = ((20025 : ℕ) : ℂ) := by norm_num
  rw [e1, e2, e4, e3]
  simp only [Nat.cast_inj]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩⟩

/-- **Theorem A at $p = 3$ is the matrix of §3.3.2** (Chenevier–Lannes, p. 3 and pp. 58–59): the four equalities of
Theorem A at $p = 3$ hold iff
$T_3 = \begin{pmatrix}4248000&4147200\\2928640&3029440\end{pmatrix}$ (`HeckeThreeSixteen`). Unconditional. -/
@[kb "chenevierlannes2019" "Thm. A, p. 3, at p = 3; §3.3.2, pp. 58–59"]
theorem theoremA_three_iff :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    ((nbCount twoE8 3 (classOf twoE8) : ℂ) = cn 16 3 - 405 * thmAScalar 3 ∧
      (nbCount twoE8 3 (classOf gamma16) : ℂ) = 405 * thmAScalar 3 ∧
      (nbCount gamma16 3 (classOf twoE8) : ℂ) = 286 * thmAScalar 3 ∧
      (nbCount gamma16 3 (classOf gamma16) : ℂ) = cn 16 3 - 286 * thmAScalar 3) ↔ HeckeThreeSixteen := by
  unfold HeckeThreeSixteen
  rw [thmAScalar_three, cn_sixteen_three]
  have e1 : ((7176640 : ℕ) : ℂ) - 405 * 10240 = ((3029440 : ℕ) : ℂ) := by norm_num
  have e2 : (405 : ℂ) * 10240 = ((4147200 : ℕ) : ℂ) := by norm_num
  have e3 : (286 : ℂ) * 10240 = ((2928640 : ℕ) : ℂ) := by norm_num
  have e4 : ((7176640 : ℕ) : ℂ) - 286 * 10240 = ((4248000 : ℕ) : ℂ) := by norm_num
  rw [e1, e2, e4, e3]
  simp only [Nat.cast_inj]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩⟩

/-- **The matrix of $T_3$ on $\mathbb{Z}[X_{16}]$ reduces to one entry** (Chenevier–Lannes, §3.3.2, pp. 58–59):
`HeckeThreeSixteen` holds iff $N_3(E_8 \oplus E_8, E_{16}) = 4147200$. Unconditional (`theoremA_odd_iff` at $p = 3$). -/
@[kb "chenevierlannes2019" "§3.3.2, pp. 58–59 (reduction to one entry)"]
theorem heckeThreeSixteen_iff :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    HeckeThreeSixteen ↔ nbCount twoE8 3 (classOf gamma16) = 4147200 := by
  have h := theoremA_odd_iff (p := 3) (by norm_num)
  rw [← theoremA_three_iff]
  have e : (nbCount twoE8 3 (classOf gamma16) : ℂ) = 405 * thmAScalar 3 ↔
      nbCount twoE8 3 (classOf gamma16) = 4147200 := by
    rw [thmAScalar_three]
    have e2 : (405 : ℂ) * 10240 = ((4147200 : ℕ) : ℂ) := by norm_num
    rw [e2, Nat.cast_inj]
  rw [← e]
  exact h

/-- **Theorem A gives the matrices of $T_2$ and $T_3$** (Chenevier–Lannes, §3.3, pp. 57–59): **conditional** on
`TheoremA`. -/
theorem heckeTwoThree_of_theoremA (hA : TheoremA) : HeckeTwoSixteen ∧ HeckeThreeSixteen := by
  exact ⟨theoremA_two_iff.1 (hA 2), theoremA_three_iff.1 (hA 3)⟩

/-- **Input: Deligne's bound for Ramanujan's $\tau$** (the Ramanujan conjecture for $\Delta$, proved by Deligne, 1974;
quoted by Chenevier–Lannes, §1.2, p. 4): $|\tau(p)| \le 2p^{11/2}$ for every prime $p$. A cited theorem, assumed here,
not proved (it rests on the Weil conjectures). -/
@[kb "chenevierlannes2019" "§1.2, p. 4 (Deligne–Ramanujan bound, cited)"]
structure DeligneBound : Prop where
  /-- $|\tau(p)| \le 2p^{11/2}$ for every prime $p$. -/
  bound : ∀ p : ℕ, p.Prime → ‖ramanujanTau p‖ ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)

/-- **$K_{16}(p)$ is connected** (Chenevier–Lannes, §1.2, p. 4: "The graph $K_{16}(p)$ is the connected graph with
$2$ vertices (Kneser). This is, of course, compatible with the bound $|\tau(p)| < 2p^{11/2}$ … and the formula for
$N_p(E_8 \oplus E_8, E_{16})$ given by Theorem A"): **conditional** on `TheoremA` and `DeligneBound`, for every odd
prime $p$ the two classes of $X_{16}$ are $p$-neighbours, so $K_{16}(p)$ is connected. *Proof:* by Theorem A,
$N_p(E_8 \oplus E_8, E_{16}) = 405\,c$ with $691c = (1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))$, and
$|\tau(p)| \le 2p^{11/2} < 1 + p^{11}$, so $c \ne 0$ (`neighborGraphConnected_sixteen_of_pos`). -/
@[kb "chenevierlannes2019" "§1.2, p. 4 (K_16(p) connected; conditional on Thm. A and Deligne)"]
theorem neighborGraphConnected_sixteen_of_theoremA (hA : TheoremA) (hD : DeligneBound) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : NeighborGraphConnected 16 p := by
  have hp := (Fact.out : p.Prime)
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  apply neighborGraphConnected_sixteen_of_pos hp2
  by_contra hz
  have hz0 : nbCount twoE8 p (classOf gamma16) = 0 := by omega
  have h1 := (hA p).2.1
  rw [hz0] at h1
  have hc : thmAScalar p = 0 := by
    have : (405 : ℂ) * thmAScalar p = 0 := by simpa using h1.symm
    simpa using this
  have hne : (1 + (p : ℂ) ^ 11 - ramanujanTau p) ≠ 0 := by
    intro h0
    have hτ : ramanujanTau p = 1 + (p : ℂ) ^ 11 := by linear_combination -h0
    have hb := hD.bound p hp
    rw [hτ] at hb
    set s : ℝ := (p : ℝ) ^ ((11 : ℝ) / 2) with hs
    have hs1 : 1 < s := Real.one_lt_rpow (by linarith) (by norm_num)
    have hs2 : s ^ 2 = (p : ℝ) ^ 11 := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have hn : ‖(1 : ℂ) + (p : ℂ) ^ 11‖ = 1 + s ^ 2 := by
      have : (1 : ℂ) + (p : ℂ) ^ 11 = ((1 + (p : ℝ) ^ 11 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity), hs2]
    rw [hn] at hb
    nlinarith
  have h4 : (1 + (p : ℂ) + (p : ℂ) ^ 2 + (p : ℂ) ^ 3) ≠ 0 := by
    have : (0 : ℝ) < 1 + p + p ^ 2 + p ^ 3 := by positivity
    exact_mod_cast this.ne'
  rw [thmAScalar] at hc
  simp [hne, h4] at hc

end QuadFormsKB.ChenevierLannes
