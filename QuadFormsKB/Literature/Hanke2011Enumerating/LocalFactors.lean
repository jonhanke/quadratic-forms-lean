/-
# Hanke 2011 (enumerating maximal definite forms): the local factors $\lambda_{\mathrm{odd},p}$, $\lambda_{\mathrm{even},p}$,
# the Gan–Hanke–Yu mass-types, and Lemma 7.2

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (`hanke2011enumerating`), §4, pp. 6–7 (Tables of $\lambda_{\mathrm{odd},p}$, $\lambda_{\mathrm{even},p}$ and of the
Gan–Hanke–Yu mass-types) and Lemma 7.2, p. 11.

The local quadratic space $(V_p, Q_p)$ of dimension $n$ has Gan–Hanke–Yu invariants $(n,\delta_p,w_p)$ (Lemma 5.1); its **Gan–Hanke–Yu
mass-type** is a label for the column/row of the tables:
* $n$ odd: `OddType.gen` ($w = 1$, $\mathrm{ord}_p\delta$ even: $\lambda = 1$), `OddType.I` ($w = -1$, $\mathrm{ord}_p\delta$ even),
  `OddType.IIplus` / `OddType.IIminus` ($\mathrm{ord}_p\delta$ odd, $w = \pm1$);
* $n$ even: `EvenType.gen` ($w = 1$ and $E_\delta = \mathbb Q_p(\sqrt\delta)$ unramified: $\lambda = 1$), `EvenType.I` ($\delta$ a square,
  $w = -1$), `EvenType.II` ($E_\delta/\mathbb Q_p$ unramified quadratic, $w = -1$), `EvenType.III` ($E_\delta/\mathbb Q_p$ ramified).

The tables give, with $p$ the prime (Gan–Hanke–Yu's $q_v$; we allow any real $p$ in the definitions):
$$\lambda_{\mathrm{odd},p} = 1,\ \frac{p^{n-1}-1}{2(p+1)},\ \frac{p^{\frac{n-1}2}+1}2,\ \frac{p^{\frac{n-1}2}-1}2;\qquad
\lambda_{\mathrm{even},p} = 1,\ \frac{(p^{\frac{n-2}2}-1)(p^{\frac n2}-1)}{2(p+1)},\ \frac{(p^{\frac{n-2}2}+1)(p^{\frac n2}+1)}{2(p+1)},\ \frac12.$$
They agree with Gan–Hanke–Yu's Props. 7.4, 7.5 as formalized in `Hanke2005.lambdaGHYOdd`, `Hanke2005.lambdaGHYEven`
(comparison lemmas in `Comparison.lean`).

**Lemma 7.2** (`lemma_7_2_odd`, `lemma_7_2_even`, `lemma_7_2_half`): for a prime $p$ and $n\ge3$, $\lambda_p<1$ only for
$n = 3$, $p = 2$, type I or II$^-$; $n = 4$, $p = 2$, type I; or $n$ even, type III; and then $\lambda_p = 1/2$. Hence
$\lambda_p\ge1/2$ always (`half_le_lambdaOdd`, `half_le_lambdaEven`).

*Clarification (table header, even $n$):* as extracted from the PDF the even table heads the type-III column
"$\mathrm{ord}_p(\delta)$ odd / $E_\delta$ ramified". For odd $p$, $E_\delta$ is ramified iff $\mathrm{ord}_p\delta$ is odd, but at $p = 2$
a unit $\delta\equiv3\bmod4$ (e.g. $\delta = -1$) also gives a ramified $E_\delta$; the type is determined by ramification
(as in Gan–Hanke–Yu Prop. 7.5 and in the proof of Thm. 4.2: "$E_\delta/\mathbb Q_p$ is ramified iff $p\mid\mathrm{Cond}(\chi)$").
-/
import Mathlib
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

/-! ### Gan–Hanke–Yu mass-types -/

/-- **Odd-dimensional Gan–Hanke–Yu mass-types** (Hanke 2011, table "Odd dim'l Gan–Hanke–Yu Mass-types", p. 7), the local type of
$(V_p,Q_p)$ with Gan–Hanke–Yu invariants $(n,\delta,w)$, $n$ odd: `gen` ("–": $w = 1$, $\mathrm{ord}_p\delta$ even, the generic type,
$\lambda = 1$); `I` ($w = -1$, $\mathrm{ord}_p\delta$ even); `IIplus` (II$^+$: $w = 1$, $\mathrm{ord}_p\delta$ odd); `IIminus`
(II$^-$: $w = -1$, $\mathrm{ord}_p\delta$ odd). -/
@[kb "hanke2011enumerating" "§4, p. 7 (Odd dim'l Gan–Hanke–Yu Mass-types)"]
inductive OddType
  | gen
  | I
  | IIplus
  | IIminus
  deriving DecidableEq

/-- **Even-dimensional Gan–Hanke–Yu mass-types** (Hanke 2011, table "Even dim'l Gan–Hanke–Yu Mass-types", p. 7), $n$ even, with
$E_\delta = \mathbb Q_p(\sqrt\delta)$: `gen` ("–": $w = 1$ and $E_\delta/\mathbb Q_p$ split or unramified, $\lambda = 1$); `I`
($\delta$ a square, i.e. $E_\delta$ split, and $w = -1$); `II` ($E_\delta/\mathbb Q_p$ an unramified field extension and
$w = -1$); `III` ($E_\delta/\mathbb Q_p$ ramified, either $w$). -/
@[kb "hanke2011enumerating" "§4, p. 7 (Even dim'l Gan–Hanke–Yu Mass-types)"]
inductive EvenType
  | gen
  | I
  | II
  | III
  deriving DecidableEq

/-! ### The local factors -/

/-- **$\lambda_{\mathrm{odd},p}$** (Hanke 2011, "Table of $\lambda_{\mathrm{odd},p}$", p. 6; from Gan–Hanke–Yu 2001, Prop. 7.4) for the
prime $p$ (any real `p` is allowed), the odd dimension $n$ and the mass-type: `gen` $\mapsto1$,
`I` $\mapsto\frac{p^{n-1}-1}{2(p+1)}$, `IIplus` $\mapsto\frac{p^{(n-1)/2}+1}2$, `IIminus` $\mapsto\frac{p^{(n-1)/2}-1}2$. -/
@[kb "hanke2011enumerating" "§4, Table of λ_odd,p, p. 6"]
def lambdaOdd (p : ℝ) (n : ℕ) : OddType → ℝ
  | .gen => 1
  | .I => (p ^ (n - 1) - 1) / (2 * (p + 1))
  | .IIplus => (p ^ ((n - 1) / 2) + 1) / 2
  | .IIminus => (p ^ ((n - 1) / 2) - 1) / 2

/-- **$\lambda_{\mathrm{even},p}$** (Hanke 2011, "Table of $\lambda_{\mathrm{even},p}$", p. 6; from Gan–Hanke–Yu 2001, Prop. 7.5) for the
prime $p$, the even dimension $n$ and the mass-type: `gen` $\mapsto1$,
`I` $\mapsto\frac{(p^{(n-2)/2}-1)(p^{n/2}-1)}{2(p+1)}$, `II` $\mapsto\frac{(p^{(n-2)/2}+1)(p^{n/2}+1)}{2(p+1)}$,
`III` $\mapsto\frac12$. -/
@[kb "hanke2011enumerating" "§4, Table of λ_even,p, p. 6"]
def lambdaEven (p : ℝ) (n : ℕ) : EvenType → ℝ
  | .gen => 1
  | .I => (p ^ ((n - 2) / 2) - 1) * (p ^ (n / 2) - 1) / (2 * (p + 1))
  | .II => (p ^ ((n - 2) / 2) + 1) * (p ^ (n / 2) + 1) / (2 * (p + 1))
  | .III => 1 / 2

/-! ### Lemma 7.2 -/

section Lemma72

variable {p : ℕ} {n : ℕ}

private theorem two_le_cast (hp : 2 ≤ p) : (2 : ℝ) ≤ p := by exact_mod_cast hp

/-- **Lemma 7.2, odd $n$** (Hanke 2011, p. 11): for $p\ge2$ an integer (e.g. a prime), $n\ge3$ odd and any mass-type $T$,
$\lambda_{\mathrm{odd},p}(T) < 1$ implies $n = 3$, $p = 2$ and $T\in\{\mathrm I,\mathrm{II}^-\}$. -/
@[kb "hanke2011enumerating" "Lemma 7.2, p. 11 (n odd)"]
theorem lemma_7_2_odd (hp : 2 ≤ p) (hn : 3 ≤ n) (hodd : Odd n) (T : OddType)
    (hlt : lambdaOdd p n T < 1) : n = 3 ∧ p = 2 ∧ (T = .I ∨ T = .IIminus) := by
  have hp2 := two_le_cast hp
  obtain ⟨k, rfl⟩ := hodd
  have hk : 1 ≤ k := by omega
  have e1 : 2 * k + 1 - 1 = 2 * k := by omega
  have e2 : (2 * k + 1 - 1) / 2 = k := by omega
  cases T with
  | gen => simp [lambdaOdd] at hlt
  | IIplus =>
    simp only [lambdaOdd, e2] at hlt
    have : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_pow₀ (by linarith)
    rw [div_lt_one (by norm_num)] at hlt
    linarith
  | I =>
    simp only [lambdaOdd, e1] at hlt
    rw [div_lt_one (by positivity)] at hlt
    -- `p^(2k) < 2p+3`
    by_cases hk1 : k = 1
    · subst hk1
      have hsq : (p : ℝ) ^ (2 * 1) = (p : ℝ) * p := by ring
      rw [hsq] at hlt
      have hp' : (p : ℝ) < 3 := by nlinarith
      have : p < 3 := by exact_mod_cast hp'
      refine ⟨rfl, by omega, Or.inl rfl⟩
    · exfalso
      have hk2 : 2 ≤ k := by omega
      have h4 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ (2 * k) := pow_le_pow_right₀ (by linarith) (by omega)
      have h16 : (p : ℝ) ^ 4 = ((p : ℝ) * p) * ((p : ℝ) * p) := by ring
      have hpp : (4 : ℝ) ≤ (p : ℝ) * p := by nlinarith
      have : 4 * ((p : ℝ) * p) ≤ (p : ℝ) ^ 4 := by rw [h16]; nlinarith
      nlinarith
  | IIminus =>
    simp only [lambdaOdd, e2] at hlt
    rw [div_lt_one (by norm_num)] at hlt
    by_cases hk1 : k = 1
    · subst hk1
      have : (p : ℝ) < 3 := by linarith [pow_one (p : ℝ)]
      have : p < 3 := by exact_mod_cast this
      exact ⟨rfl, by omega, Or.inr rfl⟩
    · exfalso
      have h2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) (by omega)
      nlinarith

/-- **Lemma 7.2, even $n$** (Hanke 2011, p. 11): for $p\ge2$ an integer, $n\ge4$ even and any mass-type $T$,
$\lambda_{\mathrm{even},p}(T) < 1$ implies ($n = 4$, $p = 2$, $T = \mathrm I$) or $T = \mathrm{III}$. -/
@[kb "hanke2011enumerating" "Lemma 7.2, p. 11 (n even)"]
theorem lemma_7_2_even (hp : 2 ≤ p) (hn : 4 ≤ n) (heven : Even n) (T : EvenType)
    (hlt : lambdaEven p n T < 1) : (n = 4 ∧ p = 2 ∧ T = .I) ∨ T = .III := by
  have hp2 := two_le_cast hp
  obtain ⟨k, rfl⟩ := heven
  have hk : 2 ≤ k := by omega
  have e1 : (k + k - 2) / 2 = k - 1 := by omega
  have e2 : (k + k) / 2 = k := by omega
  cases T with
  | gen => simp [lambdaEven] at hlt
  | III => exact Or.inr rfl
  | II =>
    exfalso
    simp only [lambdaEven, e1, e2] at hlt
    rw [div_lt_one (by positivity)] at hlt
    have h1 : (p : ℝ) ≤ (p : ℝ) ^ (k - 1) := by
      simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p) (by omega : 1 ≤ k - 1)
    have h2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
    nlinarith
  | I =>
    simp only [lambdaEven, e1, e2] at hlt
    rw [div_lt_one (by positivity)] at hlt
    by_cases hk2 : k = 2
    · subst hk2
      norm_num at hlt
      have : (p : ℝ) < 3 := by nlinarith
      have : p < 3 := by exact_mod_cast this
      exact Or.inl ⟨rfl, by omega, rfl⟩
    · exfalso
      have hk3 : 3 ≤ k := by omega
      have h1 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by linarith) (by omega)
      have h2 : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk3
      have h3 : (3 : ℝ) ≤ (p : ℝ) ^ 2 - 1 := by nlinarith
      have h4 : (7 : ℝ) ≤ (p : ℝ) ^ 3 - 1 := by nlinarith
      have h5 : 3 * ((p : ℝ) ^ 3 - 1) ≤ ((p : ℝ) ^ (k - 1) - 1) * ((p : ℝ) ^ k - 1) := by nlinarith
      nlinarith

/-- **Lemma 7.2, the values** (Hanke 2011, p. 11: "In each of these cases, we have $\lambda_{\mathrm{odd/even},p} = 1/2$"):
$\lambda_{\mathrm{odd},2}(\mathrm I) = \lambda_{\mathrm{odd},2}(\mathrm{II}^-) = 1/2$ for $n = 3$, $\lambda_{\mathrm{even},2}(\mathrm I) = 1/2$ for
$n = 4$, and $\lambda_{\mathrm{even},p}(\mathrm{III}) = 1/2$. -/
@[kb "hanke2011enumerating" "Lemma 7.2, p. 11 (λ = 1/2 in these cases)"]
theorem lemma_7_2_half :
    lambdaOdd 2 3 .I = 1 / 2 ∧ lambdaOdd 2 3 .IIminus = 1 / 2 ∧ lambdaEven 2 4 .I = 1 / 2 ∧
      ∀ (q : ℝ) (m : ℕ), lambdaEven q m .III = 1 / 2 := by
  refine ⟨?_, ?_, ?_, fun _ _ => rfl⟩ <;> norm_num [lambdaOdd, lambdaEven]

/-- **$\lambda_{\mathrm{odd},p}\ge1/2$**, and $\lambda_{\mathrm{odd},p}\ge1$ unless $n = 3$, $p = 2$, type I or II$^-$ (Lemma 7.2). -/
theorem lambdaOdd_ge (hp : 2 ≤ p) (hn : 3 ≤ n) (hodd : Odd n) (T : OddType) :
    1 ≤ lambdaOdd p n T ∨ (n = 3 ∧ p = 2 ∧ (T = .I ∨ T = .IIminus) ∧ lambdaOdd p n T = 1 / 2) := by
  by_cases h : 1 ≤ lambdaOdd p n T
  · exact Or.inl h
  · obtain ⟨rfl, rfl, hT⟩ := lemma_7_2_odd hp hn hodd T (lt_of_not_ge h)
    refine Or.inr ⟨rfl, rfl, hT, ?_⟩
    rcases hT with rfl | rfl <;> norm_num [lambdaOdd]

/-- **$\lambda_{\mathrm{even},p}\ge1$ or $=1/2$** ($n\ge4$ even), the latter only for type III or ($n = 4$, $p = 2$, type I). -/
theorem lambdaEven_ge (hp : 2 ≤ p) (hn : 4 ≤ n) (heven : Even n) (T : EvenType) :
    1 ≤ lambdaEven p n T ∨ (((n = 4 ∧ p = 2 ∧ T = .I) ∨ T = .III) ∧ lambdaEven p n T = 1 / 2) := by
  by_cases h : 1 ≤ lambdaEven p n T
  · exact Or.inl h
  · have hT := lemma_7_2_even hp hn heven T (lt_of_not_ge h)
    refine Or.inr ⟨hT, ?_⟩
    rcases hT with ⟨rfl, rfl, rfl⟩ | rfl <;> norm_num [lambdaEven]

theorem half_le_lambdaOdd (hp : 2 ≤ p) (hn : 3 ≤ n) (hodd : Odd n) (T : OddType) : 1 / 2 ≤ lambdaOdd p n T := by
  rcases lambdaOdd_ge hp hn hodd T with h | ⟨-, -, -, h⟩ <;> [linarith; rw [h]]

theorem half_le_lambdaEven (hp : 2 ≤ p) (hn : 4 ≤ n) (heven : Even n) (T : EvenType) :
    1 / 2 ≤ lambdaEven p n T := by
  rcases lambdaEven_ge hp hn heven T with h | ⟨-, h⟩ <;> [linarith; rw [h]]

end Lemma72

end QuadFormsKB.Hanke2011Enumerating
