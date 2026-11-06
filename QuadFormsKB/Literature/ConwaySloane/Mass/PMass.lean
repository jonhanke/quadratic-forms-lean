/-
# Conway–Sloane 1988, §§4–7: species, diagonal factors and the $p$-mass of a genus symbol

J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices. IV. The mass formula", *Proc. R. Soc. Lond. A* **419**
(1988), pp. 259–286 (bibliography key `conwaysloane1988`), §4, formula (3); §5, Tables 1 and 2, formula (5); §6 (love
forms); §7, formula (6), and §9, (17).

The paper writes the $p$-mass of a form $f$ with $p$-adic Jordan decomposition $f = \sum_q qf_q$ ($q$ running over all
powers of $p$, negative exponents included; almost all $f_q$ have dimension $0$, the "love forms" of §6) as
$$m_p(f) = \prod_q M_p(f_q)\cdot\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')}\cdot 2^{n(\mathrm{I,I}) - n(\mathrm{II})} \qquad (3)$$
(the last factor only for $p = 2$). This file defines the right-hand side on the genus symbols of the Chapter 15 files
(`ConwaySloane.OddSymbol`, `ConwaySloane.TwoSymbol`: a function $k \mapsto$ the constituent of scale $p^k$, $k \ge 0$),
and proves the elementary facts the paper states about it. The left-hand side (the $p$-mass defined by counting, §12)
and the identification of the two are in other files.

**Conventions.**
* A *species* (§5, p. 264) is $N$ ($N$ odd) or $N\pm$ ($N$ even); here `Species` is a dimension $N$ and a sign, the sign
  being ignored for odd $N$ (`Species.diagFactor` does not read it).
* The constituents of negative exponent are zero-dimensional. Of them only $f_{1/2}$ can be *bound* (§5, p. 265: bound
  if $f_{q/2}$ or $f_{2q}$ has type I), namely when $f_1$ has type I; it contributes $M_2(1) = \frac12$ then, and $1$
  otherwise (§6, p. 266). It is the factor `halfFactor`.
* The *octane value* (§5, p. 265) of a 2-adic constituent is its oddity $t_q$ plus $4$ if its sign $\varepsilon_q$ is
  $-$ (the paper's own reformulation, p. 265); for type II the Chapter 15 symbols have $t_q = 0$, so the octane value
  is $0$ or $4$ according as $\varepsilon_q = \pm$, i.e. $\det f_q \equiv \pm1$ or $\pm3 \pmod 8$, as on p. 265.
* The cross-product $\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')}$ is $\sqrt p^{\,c}$ with
  $c = \sum_{k<k'}(k'-k)\,n_k n_{k'}$ (`crossExp`).
* All products run over the scales $p^k$, $k < N$, for a bound $N$ beyond which the symbol is trivial; for $p = 2$ the
  diagonal product also includes $k = N$ (the love form $f_{2^N}$ is bound when $f_{2^{N-1}}$ has type I). The value does
  not depend on $N$ (`pMassOdd_congr`, `pMassTwo_congr`).

**Defines** `Species`, `Species.diagFactor` ($M_p$, (5) and Table 2), `oddSpecies` (Table 1, odd $p$), `octane`,
`twoSpecies` (Table 1, $p = 2$), `IsBound`, `crossExp`, `typeExp`, `pMassOdd`, `pMassTwo` ((3)), `stdP` ((6)).

**Proves** Table 2 entry by entry, (17), the independence of the bound $N$, and that the 2-adic $p$-mass is invariant
under sign walking and oddity fusion (`pMassTwo_moveEquiv`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.ConwaySloane.Symbol

namespace QuadFormsKB.ConwaySloane.Mass

open Finset

/-! ### Species and diagonal factors -/

/-- A **species** of an orthogonal group over $\mathbb F_p$ (Conway–Sloane 1988, §5, pp. 263–264): $N$ for $N$ odd
(one group $O_N(p)$), $N+$ or $N-$ for $N$ even (the groups $O_{N+}(p)$, $O_{N-}(p)$). Fields: `dim` is $N$; `sign`
is the $\pm$ of an even species (ignored when $N$ is odd). -/
@[kb "conwaysloane1988" "§5, pp. 263–264 (species)"]
structure Species where
  /-- The dimension $N$. -/
  dim : ℕ
  /-- The sign of the species $N\pm$ ($N$ even); not used for odd $N$. -/
  sign : Sign
  deriving DecidableEq

/-- $\prod_{i=1}^{m}(1 - p^{-2i})$. -/
def lowerProd (p : ℚ) (m : ℕ) : ℚ := ∏ i ∈ range m, (1 - (p ^ (2 * (i + 1)))⁻¹)

/-- The **diagonal factor** $M_p$ of a species (Conway–Sloane 1988, (5), p. 265, and Table 2, p. 264):
$$M_p(2s-1) = \frac1{2(1-p^{-2})(1-p^{-4})\cdots(1-p^{2-2s})},\qquad
  M_p(2s\pm) = \frac1{2(1-p^{-2})\cdots(1-p^{2-2s})(1\mp p^{-s})},$$
and $M_p(0+) = 1$ (Table 2; formula (5) is not defined there). The species $0-$ never occurs (Table 1); it is given the
value $1$ as well. -/
@[kb "conwaysloane1988" "(5), p. 265; Table 2, p. 264"]
def Species.diagFactor (p : ℕ) (σ : Species) : ℚ :=
  if σ.dim = 0 then 1
  else if Odd σ.dim then (2 * lowerProd p (σ.dim / 2))⁻¹
  else (2 * lowerProd p (σ.dim / 2 - 1) * (1 - σ.sign.toInt * ((p : ℚ) ^ (σ.dim / 2))⁻¹))⁻¹

/-- The species $N$ (odd $N$), $N+$, $N-$. -/
def Species.odd (N : ℕ) : Species := ⟨N, .plus⟩
/-- The species $N+$. -/
def Species.plus (N : ℕ) : Species := ⟨N, .plus⟩
/-- The species $N-$. -/
def Species.minus (N : ℕ) : Species := ⟨N, .minus⟩

/-! #### Table 2 -/

section Table2

variable (p : ℕ)

/-- **Table 2, general $p$** (Conway–Sloane 1988, p. 264): $M_p(0+) = 1$, $M_p(1) = \frac12$,
$M_p(2-) = \frac{p}{2p+2}$, $M_p(2+) = \frac{p}{2p-2}$, $M_p(3) = \frac{p^2}{2(p^2-1)}$,
$M_p(4-) = \frac{p^4}{2(p^4-1)}$, $M_p(4+) = \frac{p^4}{2(p^2-1)^2}$, $M_p(5) = \frac{p^6}{2(p^2-1)(p^4-1)}$. -/
@[kb "conwaysloane1988" "Table 2, p. 264 (column p)"]
theorem table2_general (hp : 2 ≤ p) :
    (Species.plus 0).diagFactor p = 1 ∧ (Species.odd 1).diagFactor p = 1 / 2 ∧
    (Species.minus 2).diagFactor p = p / (2 * p + 2) ∧ (Species.plus 2).diagFactor p = p / (2 * p - 2) ∧
    (Species.odd 3).diagFactor p = p ^ 2 / (2 * (p ^ 2 - 1)) ∧
    (Species.minus 4).diagFactor p = p ^ 4 / (2 * (p ^ 4 - 1)) ∧
    (Species.plus 4).diagFactor p = p ^ 4 / (2 * (p ^ 2 - 1) ^ 2) ∧
    (Species.odd 5).diagFactor p = p ^ 6 / (2 * (p ^ 2 - 1) * (p ^ 4 - 1)) := by
  have hp' : (2 : ℚ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℚ) - 1 ≠ 0 := by linarith
  have h1' : (p : ℚ) + 1 ≠ 0 := by linarith
  have h0 : (p : ℚ) ≠ 0 := by linarith
  have h2 : (p : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h4 : (p : ℚ) ^ 4 - 1 ≠ 0 := by
    have : (1 : ℚ) < p ^ 4 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  have h4' : (p : ℚ) ^ 2 + 1 ≠ 0 := by positivity
  simp only [Species.diagFactor, Species.plus, Species.minus, Species.odd, lowerProd, Sign.toInt]
  refine ⟨by simp, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Finset.prod_range_succ] <;> field_simp <;> ring_nf

/-- **Table 2, $p = 2$** (Conway–Sloane 1988, p. 264): $1, \frac12, \frac13, 1, \frac23, \frac8{15}, \frac89,
\frac{32}{45}$ for the species $0+, 1, 2-, 2+, 3, 4-, 4+, 5$. -/
@[kb "conwaysloane1988" "Table 2, p. 264 (column p = 2)"]
theorem table2_two :
    (Species.plus 0).diagFactor 2 = 1 ∧ (Species.odd 1).diagFactor 2 = 1 / 2 ∧
    (Species.minus 2).diagFactor 2 = 1 / 3 ∧ (Species.plus 2).diagFactor 2 = 1 ∧
    (Species.odd 3).diagFactor 2 = 2 / 3 ∧ (Species.minus 4).diagFactor 2 = 8 / 15 ∧
    (Species.plus 4).diagFactor 2 = 8 / 9 ∧ (Species.odd 5).diagFactor 2 = 32 / 45 := by
  simp only [Species.diagFactor, Species.plus, Species.minus, Species.odd, lowerProd, Sign.toInt]
  norm_num [Finset.prod_range_succ]

/-- **Table 2, $p = 3$** (Conway–Sloane 1988, p. 264): $1, \frac12, \frac38, \frac34, \frac9{16}, \frac{81}{160},
\frac{81}{128}, \frac{729}{1280}$. -/
@[kb "conwaysloane1988" "Table 2, p. 264 (column p = 3)"]
theorem table2_three :
    (Species.plus 0).diagFactor 3 = 1 ∧ (Species.odd 1).diagFactor 3 = 1 / 2 ∧
    (Species.minus 2).diagFactor 3 = 3 / 8 ∧ (Species.plus 2).diagFactor 3 = 3 / 4 ∧
    (Species.odd 3).diagFactor 3 = 9 / 16 ∧ (Species.minus 4).diagFactor 3 = 81 / 160 ∧
    (Species.plus 4).diagFactor 3 = 81 / 128 ∧ (Species.odd 5).diagFactor 3 = 729 / 1280 := by
  simp only [Species.diagFactor, Species.plus, Species.minus, Species.odd, lowerProd, Sign.toInt]
  norm_num [Finset.prod_range_succ]

/-- **Table 2, $p = 5$** (Conway–Sloane 1988, p. 264): $1, \frac12, \frac5{12}, \frac58, \frac{25}{48},
\frac{625}{1248}, \frac{625}{1152}, \frac{15625}{29952}$. -/
@[kb "conwaysloane1988" "Table 2, p. 264 (column p = 5)"]
theorem table2_five :
    (Species.plus 0).diagFactor 5 = 1 ∧ (Species.odd 1).diagFactor 5 = 1 / 2 ∧
    (Species.minus 2).diagFactor 5 = 5 / 12 ∧ (Species.plus 2).diagFactor 5 = 5 / 8 ∧
    (Species.odd 3).diagFactor 5 = 25 / 48 ∧ (Species.minus 4).diagFactor 5 = 625 / 1248 ∧
    (Species.plus 4).diagFactor 5 = 625 / 1152 ∧ (Species.odd 5).diagFactor 5 = 15625 / 29952 := by
  simp only [Species.diagFactor, Species.plus, Species.minus, Species.odd, lowerProd, Sign.toInt]
  norm_num [Finset.prod_range_succ]

/-- **Table 2, $p = 7$** (Conway–Sloane 1988, p. 264): $1, \frac12, \frac7{16}, \frac7{12}, \frac{49}{96},
\frac{2401}{4800}, \frac{2401}{4608}, \frac{117649}{230400}$. -/
@[kb "conwaysloane1988" "Table 2, p. 264 (column p = 7)"]
theorem table2_seven :
    (Species.plus 0).diagFactor 7 = 1 ∧ (Species.odd 1).diagFactor 7 = 1 / 2 ∧
    (Species.minus 2).diagFactor 7 = 7 / 16 ∧ (Species.plus 2).diagFactor 7 = 7 / 12 ∧
    (Species.odd 3).diagFactor 7 = 49 / 96 ∧ (Species.minus 4).diagFactor 7 = 2401 / 4800 ∧
    (Species.plus 4).diagFactor 7 = 2401 / 4608 ∧ (Species.odd 5).diagFactor 7 = 117649 / 230400 := by
  simp only [Species.diagFactor, Species.plus, Species.minus, Species.odd, lowerProd, Sign.toInt]
  norm_num [Finset.prod_range_succ]

end Table2

/-! ### Table 1: the species of a Jordan constituent -/

/-- **The species of a constituent at an odd prime** (Conway–Sloane 1988, Table 1, lower half, p. 264): a constituent
$f_q$ of dimension $n$ and sign $\varepsilon_q = \left(\frac{d_q}{p}\right)$ has species $n$ if $n$ is odd, and for
$n$ even species $n\pm$ with the sign $\varepsilon_q$ if $n \equiv 0 \pmod 4$ or $p \equiv 1 \pmod 4$, and
$-\varepsilon_q$ if $n \equiv 2 \pmod 4$ and $p \equiv 3 \pmod 4$. Dimension $0$ gives $0+$. -/
@[kb "conwaysloane1988" "Table 1, p. 264 (p odd)"]
def oddSpecies (p : ℕ) (f : OddFactor) : Species :=
  ⟨f.dim, if f.dim = 0 ∨ Odd f.dim then .plus
    else if f.dim % 4 = 2 ∧ p % 4 = 3 then f.sign.flip else f.sign⟩

/-- The **octane value** of a 2-adic constituent (Conway–Sloane 1988, §5, p. 265): the oddity $t_q$, plus $4$ if the
sign $\varepsilon_q$ is $-$. -/
@[kb "conwaysloane1988" "§5, p. 265 (octane value)"]
def octane (f : TwoFactor) : ZMod 8 := f.oddity + if f.sign = .minus then 4 else 0

/-- **The species of a 2-adic constituent** (Conway–Sloane 1988, Table 1, upper half, p. 264): a constituent of type
$\mathrm{II}_{2t}$, $\mathrm I_{2t+1}$ or $\mathrm I_{2t+2}$ has species $2t+1$ if it is bound or its octane value is
$\pm2$; otherwise $2t+$ if the octane value is $0$ or $\pm1$, and $2t-$ if it is $\pm3$ or $4$. -/
@[kb "conwaysloane1988" "Table 1, p. 264 (p = 2)"]
def twoSpecies (f : TwoFactor) (bound : Prop) [Decidable bound] : Species :=
  let t := if f.type = .II then f.dim / 2 else (f.dim - 1) / 2
  if bound ∨ octane f = 2 ∨ octane f = 6 then ⟨2 * t + 1, .plus⟩
  else if octane f = 3 ∨ octane f = 4 ∨ octane f = 5 then ⟨2 * t, .minus⟩
  else ⟨2 * t, .plus⟩

/-- A 2-adic constituent $f_q$, $q = 2^k$, is **bound** (Conway–Sloane 1988, §5, p. 265) if one of the adjacent
constituents $f_{q/2}$, $f_{2q}$ has type I. For $k = 0$ the constituent $f_{1/2}$ is zero-dimensional (type II). -/
@[kb "conwaysloane1988" "§5, p. 265 (bound and free)"]
def IsBound (σ : TwoSymbol) (k : ℕ) : Prop :=
  (k ≠ 0 ∧ (σ (k - 1)).type = .I) ∨ (σ (k + 1)).type = .I

instance (σ : TwoSymbol) (k : ℕ) : Decidable (IsBound σ k) := by unfold IsBound; infer_instance

/-- The factor of the zero-dimensional constituent $f_{1/2}$ (Conway–Sloane 1988, §6, p. 266): $\frac12$ if it is bound
($f_1$ of type I), $1$ otherwise. -/
def halfFactor (σ : TwoSymbol) : ℚ := if (σ 0).type = .I then 1 / 2 else 1

/-! ### The $p$-mass of a symbol, formula (3) -/

/-- The exponent of the **cross-product** (Conway–Sloane 1988, (3), p. 263):
$\prod_{q<q'}(q'/q)^{\frac12n(q)n(q')} = \sqrt p^{\,c}$, $c = \sum_{k<k'<N}(k'-k)\,n_k n_{k'}$. -/
@[kb "conwaysloane1988" "(3), p. 263 (cross-product)"]
def crossExp (dim : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ k' ∈ range N, ∑ k ∈ range k', (k' - k) * dim k * dim k'

/-- $n(\mathrm{II})$, the sum of the dimensions of the type II constituents (Conway–Sloane 1988, p. 263). -/
def nII (σ : TwoSymbol) (N : ℕ) : ℕ := ∑ k ∈ range N, if (σ k).type = .II then (σ k).dim else 0

/-- $n(\mathrm{I,I})$, the number of pairs of adjacent constituents $f_q$, $f_{2q}$ both of type I (Conway–Sloane 1988,
p. 263). -/
def nII' (σ : TwoSymbol) (N : ℕ) : ℕ :=
  ∑ k ∈ range N, if (σ k).type = .I ∧ (σ (k + 1)).type = .I then 1 else 0

/-- **The $p$-mass of a $p$-adic symbol, $p$ odd** (Conway–Sloane 1988, (3), p. 263): the diagonal product
$\prod_q M_p(f_q)$ (species by Table 1) times the cross-product, over the scales $p^k$, $k < N$. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264 (p odd)"]
noncomputable def pMassOdd (p : ℕ) (σ : OddSymbol) (N : ℕ) : ℝ :=
  ((∏ k ∈ range N, (oddSpecies p (σ k)).diagFactor p : ℚ) : ℝ) * Real.sqrt p ^ crossExp (fun k => (σ k).dim) N

/-- The **diagonal product at $p = 2$** (Conway–Sloane 1988, (3), p. 263; §6, p. 266): the factor of $f_{1/2}$ times
$\prod_{k \le N} M_2(f_{2^k})$, the species read from Table 1 with the bound/free status. -/
@[kb "conwaysloane1988" "(3), p. 263; Table 1, p. 264 (p = 2); §6, p. 266"]
def diagProdTwo (σ : TwoSymbol) (N : ℕ) : ℚ :=
  halfFactor σ * ∏ k ∈ range (N + 1), (twoSpecies (σ k) (IsBound σ k)).diagFactor 2

/-- **The 2-mass of a 2-adic symbol** (Conway–Sloane 1988, (3), p. 263): diagonal product, cross-product and the type
factor $2^{n(\mathrm{I,I}) - n(\mathrm{II})}$. -/
@[kb "conwaysloane1988" "(3), p. 263 (p = 2)"]
noncomputable def pMassTwo (σ : TwoSymbol) (N : ℕ) : ℝ :=
  (diagProdTwo σ N : ℝ) * Real.sqrt 2 ^ crossExp (fun k => (σ k).dim) N *
    (2 : ℝ) ^ ((nII' σ N : ℤ) - nII σ N)

/-! ### The standard $p$-mass, formula (6) -/

/-- **The standard $p$-mass** (Conway–Sloane 1988, (6), p. 266): for a form of dimension $n = 2s$ or $2s - 1$ and
determinant $d$,
$$\mathrm{std}_p(f) = \frac1{2(1-p^{-2})(1-p^{-4})\cdots(1-p^{2-2s})(1-\epsilon p^{-s})},$$
$\epsilon = 0$ for $n$ odd and otherwise the Legendre symbol $(D/p)$, $D = (-1)^sd$, read as $0$ if $p \mid 2d$. -/
@[kb "conwaysloane1988" "(6), p. 266"]
def stdP (p n : ℕ) (d : ℤ) : ℚ :=
  let s := (n + 1) / 2
  let ε : ℤ := if Odd n ∨ p = 2 then 0 else jacobiSym ((-1) ^ s * d) p
  (2 * lowerProd p (s - 1) * (1 - ε * ((p : ℚ) ^ s)⁻¹))⁻¹

/-- **(17)** (Conway–Sloane 1988, p. 272): when $p \mid 2d$, $\mathrm{std}_p(f) = M_p(n)$ for $n$ odd and $M_p(n-1)$ for
$n$ even ($n \ge 1$). -/
@[kb "conwaysloane1988" "(17), p. 272"]
theorem stdP_of_dvd {p n : ℕ} [hp : Fact p.Prime] {d : ℤ} (hn : 1 ≤ n) (hd : (p : ℤ) ∣ 2 * d) :
    stdP p n d = (Species.odd (if Odd n then n else n - 1)).diagFactor p := by
  have hε : (if Odd n ∨ p = 2 then (0 : ℤ) else jacobiSym ((-1) ^ ((n + 1) / 2) * d) p) = 0 := by
    split_ifs with h
    · rfl
    · have hodd : p ≠ 2 := fun h' => h (Or.inr h')
      have hpd : (p : ℤ) ∣ d := by
        rcases (Int.Prime.dvd_mul' hp.out hd) with h2 | h2
        · exfalso
          have : p ∣ 2 := by exact_mod_cast h2
          exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
        · exact h2
      have h0 : ((-1) ^ ((n + 1) / 2) * d) % (p : ℤ) = 0 :=
        Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right hpd _)
      rw [jacobiSym.mod_left, h0, jacobiSym.zero_left hp.out.one_lt]
  simp only [stdP, hε, Int.cast_zero, zero_mul, sub_zero, mul_one, Species.diagFactor, Species.odd]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hk : 1 ≤ k := by omega
    have hno : ¬ Odd (k + k) := by rw [Nat.not_odd_iff_even]; exact ⟨k, rfl⟩
    have ho : Odd (k + k - 1) := ⟨k - 1, by omega⟩
    split_ifs <;> first | omega | (congr 3; omega)
  · have ho : Odd (2 * k + 1) := ⟨k, rfl⟩
    have e1 : (2 * k + 1 + 1) / 2 - 1 = (2 * k + 1) / 2 := by omega
    simp only [e1, ho, if_true, show ¬ (2 * k + 1 = 0) by omega, if_false]

/-! ### Independence of the bound $N$ -/

theorem twoSpecies_trivial_free {b : Prop} [Decidable b] (hb : ¬ b) :
    twoSpecies TwoFactor.trivial b = Species.plus 0 := by
  simp only [twoSpecies, hb, octane, TwoFactor.trivial, false_or]
  decide

theorem twoSpecies_trivial_bound {b : Prop} [Decidable b] (hb : b) :
    twoSpecies TwoFactor.trivial b = Species.odd 1 := by
  simp [twoSpecies, hb, TwoFactor.trivial, Species.odd]

theorem crossExp_congr {dim : ℕ → ℕ} {N M : ℕ} (hN : ∀ k, N ≤ k → dim k = 0) (hNM : N ≤ M) :
    crossExp dim M = crossExp dim N := by
  unfold crossExp
  rw [← Finset.sum_range_add_sum_Ico _ hNM]
  rw [Finset.sum_eq_zero (s := Ico N M) fun k hk => by
    rw [Finset.sum_eq_zero fun i _ => by rw [hN k (Finset.mem_Ico.mp hk).1, mul_zero]]]
  simp

theorem pMassOdd_congr (p : ℕ) {σ : OddSymbol} {N M : ℕ} (hN : ∀ k, N ≤ k → σ k = OddFactor.trivial)
    (hNM : N ≤ M) : pMassOdd p σ M = pMassOdd p σ N := by
  unfold pMassOdd
  rw [crossExp_congr (fun k hk => by rw [hN k hk]; rfl) hNM, ← Finset.prod_range_mul_prod_Ico _ hNM,
    Finset.prod_eq_one (s := Ico N M) fun k hk => by
      rw [hN k (Finset.mem_Ico.mp hk).1]; simp [oddSpecies, OddFactor.trivial, Species.diagFactor]]
  simp

theorem pMassTwo_congr {σ : TwoSymbol} {N M : ℕ} (hN : ∀ k, N ≤ k → σ k = TwoFactor.trivial)
    (hNM : N ≤ M) : pMassTwo σ M = pMassTwo σ N := by
  have hd : ∀ k, N ≤ k → (σ k).dim = 0 := fun k hk => by rw [hN k hk]; rfl
  have hII : nII σ M = nII σ N := by
    unfold nII
    rw [← Finset.sum_range_add_sum_Ico _ hNM, Finset.sum_eq_zero (s := Ico N M) fun k hk => by
      rw [hd k (Finset.mem_Ico.mp hk).1]; simp]
    simp
  have hII' : nII' σ M = nII' σ N := by
    unfold nII'
    rw [← Finset.sum_range_add_sum_Ico _ hNM, Finset.sum_eq_zero (s := Ico N M) fun k hk => by
      rw [hN k (Finset.mem_Ico.mp hk).1]; simp [TwoFactor.trivial]]
    simp
  have hdiag : diagProdTwo σ M = diagProdTwo σ N := by
    unfold diagProdTwo
    congr 1
    rw [← Finset.prod_range_mul_prod_Ico _ (Nat.succ_le_succ hNM),
      Finset.prod_eq_one (s := Ico (N + 1) (M + 1)) fun k hk => by
        have hk := Finset.mem_Ico.mp hk
        have hfree : ¬ IsBound σ k := by
          rintro (⟨-, h⟩ | h)
          · rw [hN (k - 1) (by omega)] at h; exact absurd h (by decide)
          · rw [hN (k + 1) (by omega)] at h; exact absurd h (by decide)
        rw [hN k (by omega), twoSpecies_trivial_free hfree]; rfl]
    simp
  unfold pMassTwo
  rw [hdiag, hII, hII', crossExp_congr hd hNM]

/-! ### Invariance under sign walking and oddity fusion -/

theorem twoSpecies_of_bound {f g : TwoFactor} {b b' : Prop} [Decidable b] [Decidable b'] (hb : b) (hb' : b')
    (hdim : f.dim = g.dim) (htype : f.type = g.type) : twoSpecies f b = twoSpecies g b' := by
  simp [twoSpecies, hb, hb', hdim, htype]

theorem twoSpecies_congr {f g : TwoFactor} {b b' : Prop} [Decidable b] [Decidable b'] (hb : b ↔ b')
    (hdim : f.dim = g.dim) (htype : f.type = g.type) (hoct : octane f = octane g) :
    twoSpecies f b = twoSpecies g b' := by
  simp only [twoSpecies, hb, hdim, htype, hoct]

/-- Two symbols with the same dimensions and types and the same species at every scale have the same 2-mass. -/
theorem pMassTwo_eq_of_species {σ τ : TwoSymbol} (N : ℕ) (hdim : ∀ k, (τ k).dim = (σ k).dim)
    (htype : ∀ k, (τ k).type = (σ k).type)
    (hsp : ∀ k, twoSpecies (τ k) (IsBound τ k) = twoSpecies (σ k) (IsBound σ k)) :
    pMassTwo τ N = pMassTwo σ N := by
  have hII : nII τ N = nII σ N := by unfold nII; simp only [hdim, htype]
  have hII' : nII' τ N = nII' σ N := by unfold nII'; simp only [htype]
  have hdiag : diagProdTwo τ N = diagProdTwo σ N := by
    unfold diagProdTwo halfFactor
    rw [htype 0, Finset.prod_congr rfl fun k _ => by rw [hsp k]]
  unfold pMassTwo
  rw [hdiag, hII, hII']
  simp only [hdim]

theorem isBound_iff_of_type {σ τ : TwoSymbol} (htype : ∀ k, (τ k).type = (σ k).type) (k : ℕ) :
    IsBound τ k ↔ IsBound σ k := by
  simp only [IsBound, htype]

theorem octane_walk (f : TwoFactor) :
    octane { f with sign := f.sign.flip, oddity := f.oddity + 4 } = octane f := by
  cases hs : f.sign <;> simp [octane, hs, Sign.flip, add_assoc, show (4 : ZMod 8) + 4 = 0 from rfl]

/-- **The 2-mass is invariant under one elementary move** (sign walking, oddity fusion; Conway–Sloane, *Sphere Packings, Lattices and Groups* Ch. 15,
§7.5): the constituents whose sign or oddity changes are either bound (their species depends only on the type and
dimension) or keep their octane value. -/
theorem pMassTwo_step {σ τ : TwoSymbol} (h : Step σ τ) (N : ℕ) : pMassTwo τ N = pMassTwo σ N := by
  cases h with
  | walk j i hi hI =>
    refine pMassTwo_eq_of_species N (fun _ => rfl) (fun _ => rfl) fun k => ?_
    have hb := isBound_iff_of_type (σ := σ) (τ := walkStep σ j i) (fun _ => rfl) k
    by_cases hk : k = j ∨ k = j + 1
    · by_cases hki : k = i
      · subst hki
        refine twoSpecies_congr (f := walkStep σ j k k) (g := σ k) hb rfl rfl ?_
        simp only [walkStep, hk, if_true]
        exact octane_walk (σ k)
      · have hbk : IsBound σ k := by
          rcases hi with rfl | rfl <;> rcases hk with rfl | rfl
          · exact absurd rfl hki
          · exact Or.inl ⟨by omega, by simpa [IsTypeI] using hI⟩
          · exact Or.inr hI
          · exact absurd rfl hki
        exact twoSpecies_of_bound (hb.2 hbk) hbk rfl rfl
    · have : walkStep σ j i k = σ k := by
        have hki : k ≠ i := by rintro rfl; rcases hi with rfl | rfl <;> simp_all
        simp only [walkStep, hk, if_false, hki]
      rw [this]
      exact twoSpecies_congr hb rfl rfl rfl
  | fuse j c h₁ h₂ =>
    refine pMassTwo_eq_of_species N (fun _ => rfl) (fun _ => rfl) fun k => ?_
    have hb := isBound_iff_of_type (σ := σ) (τ := fuseStep σ j c) (fun _ => rfl) k
    by_cases hk : k = j ∨ k = j + 1
    · have hbk : IsBound σ k := by
        rcases hk with rfl | rfl
        · exact Or.inr h₂
        · exact Or.inl ⟨by omega, by simpa [IsTypeI] using h₁⟩
      exact twoSpecies_of_bound (hb.2 hbk) hbk rfl rfl
    · have : fuseStep σ j c k = σ k := by
        have h1 : k ≠ j := fun h => hk (Or.inl h)
        have h2 : k ≠ j + 1 := fun h => hk (Or.inr h)
        simp [fuseStep, h1, h2]
      rw [this]
      exact twoSpecies_congr hb rfl rfl rfl

/-- **The 2-mass of a 2-adic symbol depends only on its class under sign walking and oddity fusion**; with Theorem 10
of *Sphere Packings, Lattices and Groups* Ch. 15 (`TwoAdic.zpEquiv_iff_moveEquiv`) it is an invariant of the $\mathbb Z_2$-class of the form
(Conway–Sloane 1988, §5, p. 265: "the species associated with any particular $f_q$ may depend on other constituents",
which is why the bound/free status enters). -/
@[kb "conwaysloane1988" "§5, p. 265 (several Jordan decompositions)"]
theorem pMassTwo_moveEquiv {σ τ : TwoSymbol} (h : MoveEquiv σ τ) (N : ℕ) : pMassTwo σ N = pMassTwo τ N := by
  induction h with
  | rel _ _ h => exact (pMassTwo_step h N).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end QuadFormsKB.ConwaySloane.Mass
