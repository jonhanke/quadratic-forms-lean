/-
# Conway–Sloane's $p$-excess, oddity and the oddity formula

**Source.** Conway and Sloane, *Sphere Packings, Lattices and Groups*, Ch. 15, "On the Classification of
Integral Quadratic Forms", printed pp. 352–405 (checked 2026-10-21 against the chapter: a
Springer New York copy marked "© 1998", printed page = PDF page + 351; the bibliography key `conwaysloane1999` is the
3rd ed., whose main-text pagination this is). Locators below are printed pages. (The same invariants appear in
Conway–Sloane, "Low-dimensional lattices IV: the mass formula", `conwaysloane1988`; not checked here.)

**The book's definitions** (§5.1, pp. 370–371). Write a rational number as $A = p^{\alpha}a$ with $a$ prime to $p$
($a > 0$ if $p = -1$, the book's name for the archimedean place, Note in §4.4, p. 370). A **$p$-adic antisquare** is a
number $p^{\mathrm{odd}}u_-$ ($p \ge 3$, $u_-$ a nonresidue unit, i.e. $\alpha$ odd and $(a/p) = -1$) or
$2^{\mathrm{odd}}u_{\pm3}$ ($p = 2$, $a \equiv \pm 3 \bmod 8$); there are no $(-1)$-adic antisquares. For
$f = \mathrm{diag}\{p^{\alpha}a, p^{\beta}b, \dots\}$ the **$p$-signature** is
$$p^{\alpha} + p^{\beta} + \dots + 4m \ (p \ne 2), \qquad a + b + \dots + 4m \ (p = 2) \pmod 8,$$
$m$ the number of $p$-adic antisquares among the entries. The $(-1)$-signature is the signature; the 2-signature is the
**oddity**. The **$p$-excess** is $p$-signature $-$ dimension for $p \ne 2$ (including $p = -1$) and
dimension $-$ 2-signature for $p = 2$ (so the 2-excess is $n - \mathrm{oddity}$). The sum formula (15) is
$\sum_{\text{all } p} p\text{-excess}(f) \equiv 0$, and treating $p = -1$ and $p = 2$ separately gives the
**oddity formula** (16)
$$\mathrm{signature}(f) + \sum_{p \ge 3} p\text{-excess}(f) \equiv \mathrm{oddity}(f) \pmod 8.$$
For Jordan symbols (§7.7, p. 383, "The oddity condition"; constituents $q f_q$ of §7.1, p. 379 and §7.3, p. 380, with
$n_q = \dim f_q$, sign $\varepsilon_q = (\det f_q / p)$, and for $p = 2$ the oddity $t_q$ of $f_q$, $t_q = 0$ for type II):
$$p\text{-excess}(f) \equiv \sum_q n_q(q-1) + 4k_p, \qquad \mathrm{oddity}(f) \equiv \sum_q t_q + 4k_2 \pmod 8,$$
$k_p$ the number of **antisquare terms** ($q$ not a square and $\varepsilon_q = -1$); then (30) is (16) again.
The Hasse–Minkowski invariant is (17) $(f)_p = \prod_{i<j}(A_i,A_j)_p$ (§5.3, p. 373), recovered from the $p$-excess.

**Formalization.** All of this for **diagonal** forms $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in \mathbb{Z}\setminus\{0\}$
(0-based; the book's $A_1,\dots,A_n$ are `a 0`, ..., `a (n-1)`). Writing $a_i = p^{e_i}u_i$ with $p \nmid u_i$, each entry
contributes a rank-one quantity (`pExcessEntry` $= p^{e_i} - 1 + 4[\text{antisquare}]$, `oddityEntry`
$= u_i + 4[\text{antisquare}]$, `pSignatureEntry`), and the invariants are sums over the entries
(`pExcess`, `oddity`, `pSignature`, `signature`; `pExcess_eq_pSignature_sub` is the book's definition
$p$-excess $= p$-signature $- n$). The $q = p^e$-constituent of the diagonal form is $\perp_{e_i = e}\langle u_i\rangle$, so
$n_q(q-1) = \sum_{e_i = e}(p^{e_i}-1)$, $t_q = \sum_{e_i=e} u_i$, and $4k \equiv 4\,\#\{i : e_i = e \text{ odd},\ u_i
\text{ bad}\}$ since $(\cdot/p)$ and $u \mapsto [u \equiv \pm3 \bmod 8]$ are characters: `pExcessJordan`, `oddityJordan`
are the §7.7 formulas, equal to the entry-wise ones by `pExcess_eq_pExcessJordan`, `oddity_eq_oddityJordan`.
`twoExcess` $= n - \mathrm{oddity}$, `negOneExcess` $= \mathrm{signature} - n$ and `excess` (all places) are the book's
remaining normalizations.

**Verification against the book (2026-10-21).** Every definition above agrees with the book exactly, including signs and
normalizations; nothing needed fixing. The book's example $\mathrm{diag}\{1,3,-3\}$ (p. 371) is
`example_diag_one_three_neg_three`.

Main results:
* **Oddity formula** (16) = (30) (`oddity_formula`, `oddity_formula_of_adapted`), proved from Hilbert reciprocity over
  $\mathbb{Q}$ (`hilbert_product_formula`): the defect $D(a) = \mathrm{sign}(a) + \sum_{p\ge3} p\text{-excess}\langle
  a\rangle - \mathrm{oddity}\langle a\rangle$ satisfies $D(ab) = D(a) + D(b) - 4\,\#\{v : (a,b)_v = -1\} = D(a) + D(b)$, and
  $D$ vanishes on $-1$, $2$ and the odd primes. The sum formula (15): `sum_excess_eq_zero`, `sum_formula_pSignature`.
* **Relation to the Hasse invariant** (`pExcess_eq_hasse`, `oddity_eq_hasse`, `signature_eq_hasse`): with
  $d = \prod a_i$ and Serre's $\varepsilon_v = \prod_{i<j}(a_i,a_j)_v$ (`RatPlace.hasseSerre`, which is the book's (17),
  `RatPlace.hasseConwaySloane`), writing $[\![\varepsilon]\!] = 4$ if $\varepsilon = -1$ and $0$ if $\varepsilon = 1$,
  $$p\text{-excess}(f) \equiv p\text{-excess}\langle d\rangle + [\![\varepsilon_p(f)]\!],\quad
    \mathrm{oddity}(f) \equiv \mathrm{oddity}\langle d\rangle + (n-1) + [\![\varepsilon_2(f)]\!],\quad
    \mathrm{sig}(f) \equiv \mathrm{sign}(d) + (n-1) + [\![\varepsilon_\infty(f)]\!] \pmod 8.$$
  The book's §5.3 statement ("$(f)_p = \pm 1$ according as the $p$-excess of $f$ is or is not $\equiv$ that of
  $f_0 = \mathrm{diag}\{A_1\cdots A_n,1,\dots,1\}$") is `hasseConwaySloane_eq_one_iff`, at every place including $2$ and
  $-1$. The local binary identities behind them (`pExcessEntry_mul`, `oddityEntry_mul`, `sign_mul_hilbert`) say that
  each rank-one quantity is a homomorphism up to the Hilbert symbol.
* $p$-excesses are even, and $\equiv 0 \bmod 4$ if $p \equiv 1 \bmod 4$ (§5.2, Remark (2), p. 373): `pExcess_even`.

*Normalization traps*. (1) The oddity is **not** the 2-excess: the 2-excess
is $n - \mathrm{oddity}$ (p. 371), with the opposite sign convention to the $p$-excesses for $p \ne 2$, which is why the
oddity formula has the oddity alone on the right. (2) In (15), "odd $p$" **includes $p = -1$**
(`sum_formula_pSignature`). (3) The $p$-excess uses $q - 1$ with $q = p^e$ the **scale** of the constituent, not
$p - 1$; for $e$ even this contributes $0$ mod 8. (4) $k_p$ counts only constituents with $q$ an **odd** power of $p$.
(5) (17) is the $i<j$ product (Cassels/Serre), not O'Meara's $i \le j$ (`hasseOMeara`); the book calls it "a common
one" of "several different conventions".

*Related work.* Neither Mathlib nor Tau Ceti has the $p$-excess, the oddity or the oddity formula (searched
2026-10-20). Tau Ceti's Hasse invariants are cited in `HasseConventionsNF.lean`.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace QuadFormsKB

namespace ConwaySloane

open Finset

variable {n : ℕ}

/-! ### Rank-one quantities -/

/-- **The unit part $u$ of $a = p^{e}u$**, $e = v_p(a)$ (`padicValInt`), $p \nmid u$ for $a \ne 0$ and $p$ prime
(`not_dvd_unitPart`). -/
def unitPart (p : ℕ) (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

/-- **The $p$-excess of the rank-one form $\langle a \rangle$**, $a = p^e u$ ($p$ odd):
$(p^e - 1) + 4\,[e \text{ odd and } (u/p) = -1] \in \mathbb{Z}/8$. The symbol $(u/p)$ is the Jacobi symbol
`jacobiSym u p`, which is the Legendre symbol for $p$ prime. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, pp. 370–371"]
def pExcessEntry (p : ℕ) (a : ℤ) : ZMod 8 :=
  ((p : ZMod 8) ^ padicValInt p a - 1) +
    if Odd (padicValInt p a) ∧ jacobiSym (unitPart p a) p = -1 then 4 else 0

/-- **The oddity of the rank-one form $\langle a \rangle$**, $a = 2^e u$, $u$ odd:
$u + 4\,[e \text{ odd and } u \equiv \pm 3 \pmod 8] \in \mathbb{Z}/8$ (the book's 2-signature of $\langle a\rangle$;
$u \equiv \pm 3 \pmod 8$ is $(u/2) = -1$ in the book's extended Jacobi–Legendre symbol, §4.3, p. 368). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, pp. 370–371; §4.3, p. 368"]
def oddityEntry (a : ℤ) : ZMod 8 :=
  (unitPart 2 a : ZMod 8) +
    if Odd (padicValInt 2 a) ∧ ((unitPart 2 a : ZMod 8) = 3 ∨ (unitPart 2 a : ZMod 8) = 5) then 4 else 0

/-! ### The invariants of a diagonal form -/

/-- **Conway–Sloane's $p$-excess of $\langle a_0,\dots,a_{n-1}\rangle$**, $a_i \in \mathbb{Z}\setminus\{0\}$, $p$ an
odd prime: $\sum_i$ `pExcessEntry p (a i)` $\in \mathbb{Z}/8$ (equal to the Jordan-constituent formula
$\sum_q n_q(q-1) + 4k_q$ by `pExcess_eq_pExcessJordan`). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def pExcess (p : ℕ) (a : Fin n → ℤ) : ZMod 8 := ∑ i, pExcessEntry p (a i)

/-- **Conway–Sloane's oddity (the $2$-adic invariant) of $\langle a_0,\dots,a_{n-1}\rangle$**,
$a_i \in \mathbb{Z}\setminus\{0\}$: $\sum_i$ `oddityEntry (a i)` $\in \mathbb{Z}/8$ (equal to the
Jordan-constituent formula $\sum_q t_q + 4k_q$ by `oddity_eq_oddityJordan`). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def oddity (a : Fin n → ℤ) : ZMod 8 := ∑ i, oddityEntry (a i)

/-- **The signature $n_+ - n_-$ of $\langle a_0,\dots,a_{n-1}\rangle$** (number of positive minus number of negative
entries; for nonzero entries). This is Conway–Sloane's $(-1)$-signature $p^{\alpha} + p^{\beta} + \cdots$ at $p = -1$
(their name for $\infty$; the $p$-part of $A$ at $p = -1$ is $\pm 1$ and there are no $(-1)$-adic antisquares; Conway–Sloane,
Ch. 15, §5.1, pp. 370–371), the ordinary signature by Sylvester's law. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def signature (a : Fin n → ℤ) : ℤ := ∑ i, Int.sign (a i)

/-! ### Jordan-constituent formulas -/

/-- **The $p$-excess by Jordan constituents** (Conway–Sloane's formula, for the Jordan decomposition of the diagonal
form): over the exponents $e$ occurring among $e_i = v_p(a_i)$, the $p^e$-constituent is $\perp_{e_i = e}\langle u_i\rangle$
of dimension $n_e$ and determinant $\varepsilon_e = \prod_{e_i = e} u_i$, contributing $n_e(p^e - 1) + 4k_e$ with
$k_e = 1$ iff $e$ is odd and $(\varepsilon_e/p) = -1$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 383 (oddity condition); §7.1, p. 379"]
def pExcessJordan (p : ℕ) (a : Fin n → ℤ) : ZMod 8 :=
  ∑ e ∈ univ.image (fun i => padicValInt p (a i)),
    ((((univ.filter fun i => padicValInt p (a i) = e).card : ℕ) : ZMod 8) * ((p : ZMod 8) ^ e - 1) +
      if Odd e ∧ jacobiSym (∏ i ∈ univ.filter (fun i => padicValInt p (a i) = e), unitPart p (a i)) p = -1
      then 4 else 0)

/-- **The oddity by Jordan constituents** (Conway–Sloane's formula): over the exponents $e$ occurring among
$e_i = v_2(a_i)$, the $2^e$-constituent $\perp_{e_i = e}\langle u_i\rangle$ contributes $t_e + 4k_e$, with trace
$t_e = \sum_{e_i = e} u_i$ and $k_e = 1$ iff $e$ is odd and $\varepsilon_e = \prod_{e_i = e} u_i \equiv \pm 3 \pmod 8$.
(Conway–Sloane, Ch. 15, §7.7, p. 383: $\sum_q t_q + 4k_2$, $k_2$ the number of antisquare terms.) All constituents of a diagonal form
are of type I; the book's type II constituents ($t_q = 0$, §7.3, p. 380) do not arise here. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 383 (oddity condition); §7.3, p. 380"]
def oddityJordan (a : Fin n → ℤ) : ZMod 8 :=
  ∑ e ∈ univ.image (fun i => padicValInt 2 (a i)),
    ((∑ i ∈ univ.filter (fun i => padicValInt 2 (a i) = e), (unitPart 2 (a i) : ZMod 8)) +
      if Odd e ∧ (((∏ i ∈ univ.filter (fun i => padicValInt 2 (a i) = e), unitPart 2 (a i) : ℤ) : ZMod 8) = 3 ∨
        ((∏ i ∈ univ.filter (fun i => padicValInt 2 (a i) = e), unitPart 2 (a i) : ℤ) : ZMod 8) = 5)
      then 4 else 0)

/-! ### Signs as flags (internal) -/

/-- $\pm 1$ from a flag: `sgn true = -1`, `sgn false = 1`. Internal. -/
def sgn (S : Bool) : ℤ := if S then -1 else 1

/-- The $\mathbb{Z}/8$-valued "logarithm" of a sign: $4$ for $-1$, $0$ otherwise (the map $\{\pm1\} \to \mathbb{Z}/8$,
$-1 \mapsto 4$). Internal. -/
def sgn4 (s : ℤ) : ZMod 8 := if s = -1 then 4 else 0

theorem sgn_mul (S T : Bool) : sgn S * sgn T = sgn (S ^^ T) := by
  cases S <;> cases T <;> simp [sgn]

theorem sgn4_sgn (S : Bool) : sgn4 (sgn S) = if S then 4 else 0 := by
  cases S <;> simp [sgn, sgn4]

theorem neg_one_pow_eq_sgn (m : ℕ) : (-1 : ℤ) ^ m = sgn (decide (Odd m)) := by
  rcases Nat.even_or_odd m with h | h
  · simp [sgn, h.neg_one_pow, Nat.not_odd_iff_even.mpr h]
  · simp [sgn, h.neg_one_pow, h]

theorem sgn_pow (S : Bool) (m : ℕ) : sgn S ^ m = sgn (decide (Odd m) && S) := by
  cases S
  · simp [sgn]
  · simp only [sgn, if_true, Bool.and_true]; exact neg_one_pow_eq_sgn m

theorem eq_sgn_of_pm {s : ℤ} (h : s = 1 ∨ s = -1) : s = sgn (decide (s = -1)) := by
  rcases h with rfl | rfl <;> simp [sgn]

theorem sgn4_mul {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    sgn4 (s * t) = sgn4 s + sgn4 t := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [sgn4] <;> decide

/-! ### Unit parts -/

section UnitPart

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_pow_mul_unitPart (a : ℤ) : a = (p : ℤ) ^ padicValInt p a * unitPart p a :=
  (Int.mul_ediv_cancel' (padicValInt_dvd a)).symm

theorem not_dvd_unitPart {a : ℤ} (ha : a ≠ 0) : ¬ (p : ℤ) ∣ unitPart p a := by
  rintro ⟨c, hc⟩
  have e := eq_pow_mul_unitPart (p := p) a
  rw [hc] at e
  have hd : (p : ℤ) ^ (padicValInt p a + 1) ∣ a := ⟨c, by rw [pow_succ, mul_assoc]; exact e⟩
  rcases (padicValInt_dvd_iff (p := p) _ a).mp hd with h | h
  · exact ha h
  · omega

theorem unitPart_ne_zero {a : ℤ} (ha : a ≠ 0) : unitPart p a ≠ 0 := by
  intro h
  have e := eq_pow_mul_unitPart (p := p) a
  rw [h, mul_zero] at e
  exact ha e

theorem unitPart_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitPart p (a * b) = unitPart p a * unitPart p b := by
  have e := eq_pow_mul_unitPart (p := p) (a * b)
  have ea := eq_pow_mul_unitPart (p := p) a
  have eb := eq_pow_mul_unitPart (p := p) b
  rw [padicValInt.mul ha hb, pow_add] at e
  have hp0 : ((p : ℤ) ^ padicValInt p a * (p : ℤ) ^ padicValInt p b) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
      (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
  refine (mul_left_cancel₀ hp0 ?_).symm
  calc (p : ℤ) ^ padicValInt p a * (p : ℤ) ^ padicValInt p b * (unitPart p a * unitPart p b)
      = ((p : ℤ) ^ padicValInt p a * unitPart p a) * ((p : ℤ) ^ padicValInt p b * unitPart p b) := by ring
    _ = a * b := by rw [← ea, ← eb]
    _ = _ := e

theorem unitPart_of_not_dvd {a : ℤ} (h : ¬ (p : ℤ) ∣ a) : unitPart p a = a := by
  simp [unitPart, padicValInt.eq_zero_of_not_dvd h]

/-- A unit of $\mathbb{Z}_p$ from an integer prime to $p$. -/
theorem exists_unit_of_not_dvd (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) : ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) = m := by
  have h1 : ‖(m : ℤ_[p])‖ = 1 := by
    have := PadicInt.norm_le_one (m : ℤ_[p])
    have h2 := (PadicInt.norm_int_lt_one_iff_dvd m).not.2 hm
    push_neg at h2; linarith
  exact ⟨(PadicInt.isUnit_iff.2 h1).unit, rfl⟩

end UnitPart

/-! ### Local Hilbert symbols of integers -/

/-- **The Hilbert symbol at an odd prime $p$ of $x = p^\alpha m$, $y = p^\beta n$** ($m, n \in \mathbb{Z}$ prime to $p$):
$(x,y)_p = (-1)^{\alpha\beta(p-1)/2}\left(\frac{m}{p}\right)^\beta\left(\frac{n}{p}\right)^\alpha$
(Serre III §1.2, Thm. 1, from `HilbertLocal.hilbertSymbol_odd_formula`). -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem hilbert_odd_int (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (α β : ℕ) (m n : ℤ) (x y : ℚ)
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) (hx : x = (p : ℚ) ^ α * m) (hy : y = (p : ℚ) ^ β * n) :
    (RatPlace.finite ⟨p, hp.out⟩).hilbert x y =
      (-1) ^ (α * β * ((p - 1) / 2)) * legendreSym p m ^ β * legendreSym p n ^ α := by
  obtain ⟨u, hu⟩ := exists_unit_of_not_dvd m hm
  obtain ⟨v, hv⟩ := exists_unit_of_not_dvd n hn
  have hx' : ((x : ℚ) : ℚ_[p]) = (p : ℚ_[p]) ^ α * ((u : ℤ_[p]) : ℚ_[p]) := by
    rw [hu, hx]; push_cast; rfl
  have hy' : ((y : ℚ) : ℚ_[p]) = (p : ℚ_[p]) ^ β * ((v : ℤ_[p]) : ℚ_[p]) := by
    rw [hv, hy]; push_cast; rfl
  show hilbertSymbol ℚ_[p] (x : ℚ_[p]) (y : ℚ_[p]) = _
  rw [hx', hy', HilbertLocal.hilbertSymbol_odd_formula hp2]
  simp only [HilbertLocal.unitChar, hu, hv, map_intCast]
  rfl

/-- **The Hilbert symbol at $2$ of $x = 2^\alpha m$, $y = 2^\beta n$** ($m, n$ odd integers):
$(x,y)_2 = (-1)^{\varepsilon(m)\varepsilon(n) + \alpha\,\omega(n) + \beta\,\omega(m)}$
(Serre III §1.2, Thm. 1, from `HilbertLocal.hilbertSymbol_two_formula`). -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 [unverified]"]
theorem hilbert_two_int (α β : ℕ) (m n : ℤ) (x y : ℚ) (hm : ¬ (2 : ℤ) ∣ m) (hn : ¬ (2 : ℤ) ∣ n)
    (hx : x = (2 : ℚ) ^ α * m) (hy : y = (2 : ℚ) ^ β * n) :
    (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert x y = (-1) ^
      (HilbertLocal.twoEps (m : ZMod 8) * HilbertLocal.twoEps (n : ZMod 8) +
        α * HilbertLocal.twoOmega (n : ZMod 8) + β * HilbertLocal.twoOmega (m : ZMod 8)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_unit_of_not_dvd (p := 2) m (by exact_mod_cast hm)
  obtain ⟨v, hv⟩ := exists_unit_of_not_dvd (p := 2) n (by exact_mod_cast hn)
  have hx' : ((x : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ α * ((u : ℤ_[2]) : ℚ_[2]) := by
    rw [hu, hx]; push_cast; rfl
  have hy' : ((y : ℚ) : ℚ_[2]) = (2 : ℚ_[2]) ^ β * ((v : ℤ_[2]) : ℚ_[2]) := by
    rw [hv, hy]; push_cast; rfl
  show hilbertSymbol ℚ_[2] (x : ℚ_[2]) (y : ℚ_[2]) = _
  rw [hx', hy', HilbertLocal.hilbertSymbol_two_formula]
  simp only [hu, hv, map_intCast]


/-! ### The local binary identities -/

theorem sgn_eq_neg_one_iff (S : Bool) : sgn S = -1 ↔ S = true := by
  cases S <;> simp [sgn]

theorem natCast_zmod8_odd {p : ℕ} (hp : Odd p) :
    (p : ZMod 8) = 1 ∨ (p : ZMod 8) = 3 ∨ (p : ZMod 8) = 5 ∨ (p : ZMod 8) = 7 := by
  rw [← ZMod.natCast_mod p 8]
  have h := Nat.odd_iff.mp hp
  have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem odd_half_iff {p : ℕ} (hp : Odd p) :
    Odd ((p - 1) / 2) ↔ ((p : ZMod 8) = 3 ∨ (p : ZMod 8) = 7) := by
  rw [← ZMod.natCast_mod p 8, Nat.odd_iff]
  have h := Nat.odd_iff.mp hp
  have : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  have key : (((p % 8 : ℕ) : ZMod 8) = 3 ∨ ((p % 8 : ℕ) : ZMod 8) = 7) ↔ (p % 8 = 3 ∨ p % 8 = 7) := by
    rcases this with h8 | h8 | h8 | h8 <;> rw [h8] <;> decide
  rw [key]
  omega

theorem pow_zmod8_eq {r : ZMod 8} (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) (m : ℕ) :
    r ^ m = if Odd m then r else 1 := by
  have h2 : r ^ 2 = 1 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_neg (Nat.not_odd_iff_even.mpr ⟨k, rfl⟩), ← two_mul, pow_mul, h2, one_pow]
  · rw [if_pos ⟨k, rfl⟩, pow_succ, pow_mul, h2, one_pow, one_mul]

/-- **The $p$-excess is additive up to the Hilbert symbol** ($p$ odd prime, $a, b \in \mathbb{Z}\setminus\{0\}$):
$$p\text{-excess}\langle a\rangle + p\text{-excess}\langle b\rangle \equiv p\text{-excess}\langle ab\rangle +
  [\![(a,b)_p]\!] \pmod 8,$$
$[\![-1]\!] = 4$, $[\![1]\!] = 0$. This is the rank-two case of `pExcess_eq_hasse`. -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373 (derived, n = 2)"]
theorem pExcessEntry_mul (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    pExcessEntry p a + pExcessEntry p b =
      pExcessEntry p (a * b) + sgn4 ((RatPlace.finite ⟨p, hp.out⟩).hilbert a b) := by
  have hpo : Odd p := hp.out.odd_of_ne_two hp2
  have hr := natCast_zmod8_odd hpo
  have hH := hilbert_odd_int p hp2 (padicValInt p a) (padicValInt p b) (unitPart p a) (unitPart p b)
    a b (not_dvd_unitPart ha) (not_dvd_unitPart hb) (by exact_mod_cast eq_pow_mul_unitPart (p := p) a)
    (by exact_mod_cast eq_pow_mul_unitPart (p := p) b)
  have hLu := legendreSym.eq_one_or_neg_one p
    (a := unitPart p a) (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_unitPart ha)
  have hLw := legendreSym.eq_one_or_neg_one p
    (a := unitPart p b) (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_unitPart hb)
  obtain ⟨X, hX⟩ : ∃ X, legendreSym p (unitPart p a) = sgn X := ⟨_, eq_sgn_of_pm hLu⟩
  obtain ⟨Y, hY⟩ : ∃ Y, legendreSym p (unitPart p b) = sgn Y := ⟨_, eq_sgn_of_pm hLw⟩
  have hodd := odd_half_iff hpo
  unfold pExcessEntry
  rw [hH, padicValInt.mul ha hb, unitPart_mul ha hb, jacobiSym.mul_left,
    ← jacobiSym.legendreSym.to_jacobiSym, ← jacobiSym.legendreSym.to_jacobiSym, hX, hY,
    pow_zmod8_eq hr, pow_zmod8_eq hr, pow_zmod8_eq hr]
  simp only [neg_one_pow_eq_sgn, sgn_pow, sgn_mul, sgn4_sgn, sgn_eq_neg_one_iff, Nat.odd_add, Nat.odd_mul,
    hodd, ← Nat.not_odd_iff_even]
  generalize (p : ZMod 8) = r at hr ⊢
  by_cases hA : Odd (padicValInt p a) <;> by_cases hB : Odd (padicValInt p b) <;>
    simp only [hA, hB, true_and, false_and, and_true, and_false, true_iff, false_iff, not_true_eq_false,
      not_false_eq_true, if_true, if_false, decide_true, decide_false, Bool.true_and, Bool.false_and,
      iff_true, iff_false] <;>
    rcases hr with rfl | rfl | rfl | rfl <;> cases X <;> cases Y <;> decide

theorem intCast_zmod8_odd {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    (m : ZMod 8) = 1 ∨ (m : ZMod 8) = 3 ∨ (m : ZMod 8) = 5 ∨ (m : ZMod 8) = 7 := by
  have e : ((m % 8 : ℤ) : ZMod 8) = (m : ZMod 8) := by simpa using ZMod.intCast_mod m 8
  rw [← e]
  have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

/-- **The oddity is additive up to the Hilbert symbol at 2** ($a, b \in \mathbb{Z}\setminus\{0\}$):
$$\mathrm{oddity}\langle a\rangle + \mathrm{oddity}\langle b\rangle \equiv \mathrm{oddity}\langle ab\rangle + 1 +
  [\![(a,b)_2]\!] \pmod 8.$$ -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373 (derived, n = 2)"]
theorem oddityEntry_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    oddityEntry a + oddityEntry b =
      oddityEntry (a * b) + 1 + sgn4 ((RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert a b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := not_dvd_unitPart (p := 2) ha
  have hw := not_dvd_unitPart (p := 2) hb
  have hH := hilbert_two_int (padicValInt 2 a) (padicValInt 2 b) (unitPart 2 a) (unitPart 2 b) a b
    (by exact_mod_cast hu) (by exact_mod_cast hw)
    (by exact_mod_cast eq_pow_mul_unitPart (p := 2) a) (by exact_mod_cast eq_pow_mul_unitPart (p := 2) b)
  have hr := intCast_zmod8_odd (by exact_mod_cast hu)
  have hs := intCast_zmod8_odd (by exact_mod_cast hw)
  unfold oddityEntry
  rw [hH, padicValInt.mul ha hb, unitPart_mul ha hb, Int.cast_mul]
  simp only [neg_one_pow_eq_sgn, sgn4_sgn, Nat.odd_add, Nat.odd_mul, ← Nat.not_odd_iff_even]
  generalize ((unitPart 2 a : ℤ) : ZMod 8) = r at hr ⊢
  generalize ((unitPart 2 b : ℤ) : ZMod 8) = t at hs ⊢
  by_cases hA : Odd (padicValInt 2 a) <;> by_cases hB : Odd (padicValInt 2 b) <;>
    simp only [hA, hB, true_and, false_and, and_true, and_false, true_iff, false_iff, not_true_eq_false,
      not_false_eq_true, if_true, if_false, decide_true, decide_false, Bool.true_and, Bool.false_and,
      iff_true, iff_false] <;>
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide

/-- **The sign is additive up to the Hilbert symbol at $\infty$** ($a, b \in \mathbb{Z}\setminus\{0\}$):
$\mathrm{sign}(a) + \mathrm{sign}(b) \equiv \mathrm{sign}(ab) + 1 + [\![(a,b)_\infty]\!] \pmod 8$. -/
theorem sign_mul_hilbert {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((Int.sign a : ℤ) : ZMod 8) + (Int.sign b : ZMod 8) =
      (Int.sign (a * b) : ZMod 8) + 1 + sgn4 (RatPlace.infinite.hilbert a b) := by
  rw [hilbert_infinite_eq _ _ (by exact_mod_cast ha) (by exact_mod_cast hb), Int.sign_mul]
  rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb' <;>
    simp [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, ha', hb', sgn4, ha'.not_gt, hb'.not_gt,
      ha'.le.not_gt] <;> decide


/-! ### Relation to the Hasse invariant -/

theorem sgn4_mul_hilbert (v : RatPlace) (x y : ℚ) (t : ℤ) (ht : t = 1 ∨ t = -1) :
    sgn4 (v.hilbert x y * t) = sgn4 (v.hilbert x y) + sgn4 t :=
  sgn4_mul (RatPlace.hilbert_pm v x y) ht

theorem prod_pm {ι : Type*} (s : Finset ι) (f : ι → ℤ) (h : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    ∏ i ∈ s, f i = 1 ∨ ∏ i ∈ s, f i = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [prod_insert hk]
    rcases h k (mem_insert_self _ _) with h1 | h1 <;>
      rcases ih (fun i hi => h i (mem_insert_of_mem hi)) with h2 | h2 <;> simp [h1, h2]

theorem hasseSerre_pm (v : RatPlace) {m : ℕ} (c : Fin m → ℚ) :
    v.hasseSerre c = 1 ∨ v.hasseSerre c = -1 :=
  prod_pm _ _ fun i _ => prod_pm _ _ fun j _ => by
    split_ifs
    · exact RatPlace.hilbert_pm v _ _
    · exact Or.inl rfl

/-- **Peeling off the first entry:** $\varepsilon_v\langle c_0,\dots,c_n\rangle =
(c_0, c_1\cdots c_n)_v\,\varepsilon_v\langle c_1,\dots,c_n\rangle$. -/
theorem hasseSerre_succ (v : RatPlace) {m : ℕ} (c : Fin (m + 1) → ℚ) (hc : ∀ i, c i ≠ 0) :
    v.hasseSerre c = v.hilbert (c 0) (∏ j : Fin m, c j.succ) * v.hasseSerre (fun j => c j.succ) := by
  unfold RatPlace.hasseSerre
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [lt_self_iff_false, if_false, one_mul, Fin.succ_pos, if_true]
    rw [RatPlace.hilbert_comm, RatPlace.hilbert_prod_left v (c 0) (hc 0) univ (fun j : Fin m => c j.succ)
      (fun j _ => hc j.succ)]
    exact prod_congr rfl fun j _ => RatPlace.hilbert_comm v _ _
  · refine prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.succ_lt_succ_iff, (Fin.succ_pos i).not_gt, if_false, one_mul]

/-- **The $p$-excess and Serre's Hasse invariant at $p$** ($p$ an odd prime, $a_i \in \mathbb{Z}\setminus\{0\}$,
$d = \prod_i a_i$):
$$p\text{-excess}\langle a_0,\dots,a_{n-1}\rangle \equiv p\text{-excess}\langle d\rangle + [\![\varepsilon_p]\!]
\pmod 8,\qquad \varepsilon_p = \prod_{i<j}(a_i,a_j)_p,$$
$[\![-1]\!] = 4$, $[\![1]\!] = 0$. So the $p$-excess determines and is determined by $\varepsilon_p$, given the
square class of $d$ (which fixes $p\text{-excess}\langle d\rangle$). -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17) (derived); serre1973 Ch. IV, §2.1"]
theorem pExcess_eq_hasse (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ {n : ℕ} (a : Fin n → ℤ), (∀ i, a i ≠ 0) →
      pExcess p a = pExcessEntry p (∏ i, a i) +
        sgn4 ((RatPlace.finite ⟨p, hp.out⟩).hasseSerre fun i => (a i : ℚ))
  | 0, a, _ => by
    simp [pExcess, pExcessEntry, RatPlace.hasseSerre, sgn4, padicValInt.one]
  | m + 1, a, ha => by
    have ih := pExcess_eq_hasse p hp2 (fun j => a j.succ) (fun j => ha j.succ)
    have hd : (∏ j : Fin m, a j.succ) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => ha j.succ
    unfold pExcess at ih ⊢
    rw [Fin.sum_univ_succ, ih, ← add_assoc, pExcessEntry_mul p hp2 (ha 0) hd, Fin.prod_univ_succ,
      hasseSerre_succ _ _ (fun i => by exact_mod_cast ha i), add_assoc]
    congr 1
    push_cast
    rw [sgn4_mul_hilbert _ _ _ _ (hasseSerre_pm _ _)]

/-- **The $p$-excess and O'Meara's Hasse symbol at $p$** ($p$ odd prime): $p\text{-excess}(f) \equiv
p\text{-excess}\langle d\rangle + [\![S_p]\!] + [\![(d,d)_p]\!] \pmod 8$ (from `pExcess_eq_hasse` and
$\varepsilon_p = S_p\,(d,d)_p$, `hasseSerre_eq`). -/
@[kb "omeara1963" "§63B, p. 167 (Hasse symbol; derived identity)"]
theorem pExcess_eq_hasseOMeara (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    pExcess p a = pExcessEntry p (∏ i, a i) +
      sgn4 ((RatPlace.finite ⟨p, hp.out⟩).hasseOMeara fun i => (a i : ℚ)) +
      sgn4 ((RatPlace.finite ⟨p, hp.out⟩).hilbert (diagDet fun i => (a i : ℚ)) (diagDet fun i => (a i : ℚ))) := by
  have hc : ∀ i, (a i : ℚ) ≠ 0 := fun i => by exact_mod_cast ha i
  have hpm : (RatPlace.finite ⟨p, hp.out⟩).hasseOMeara (fun i => (a i : ℚ)) = 1 ∨
      (RatPlace.finite ⟨p, hp.out⟩).hasseOMeara (fun i => (a i : ℚ)) = -1 := by
    rw [hasseOMeara_eq _ _ hc]
    rcases hasseSerre_pm (RatPlace.finite ⟨p, hp.out⟩) (fun i => (a i : ℚ)) with h | h <;>
      rcases RatPlace.hilbert_pm (RatPlace.finite ⟨p, hp.out⟩) (diagDet fun i => (a i : ℚ))
        (diagDet fun i => (a i : ℚ)) with h' | h' <;> simp [h, h']
  rw [pExcess_eq_hasse p hp2 a ha, hasseSerre_eq _ _ hc, add_assoc,
    sgn4_mul hpm (RatPlace.hilbert_pm _ _ _)]

/-- **The oddity and Serre's Hasse invariant at 2** ($a_i \in \mathbb{Z}\setminus\{0\}$, $d = \prod a_i$):
$$\mathrm{oddity}\langle a_0,\dots,a_{n-1}\rangle \equiv \mathrm{oddity}\langle d\rangle + (n-1) +
[\![\varepsilon_2]\!] \pmod 8.$$ -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17) (derived); serre1973 Ch. IV, §2.1"]
theorem oddity_eq_hasse : ∀ {n : ℕ} (a : Fin n → ℤ), (∀ i, a i ≠ 0) →
    oddity a = oddityEntry (∏ i, a i) + ((n : ZMod 8) - 1) +
      sgn4 ((RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre fun i => (a i : ℚ))
  | 0, a, _ => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    simp [oddity, oddityEntry, RatPlace.hasseSerre, sgn4, unitPart, padicValInt.one]
  | m + 1, a, ha => by
    have ih := oddity_eq_hasse (fun j => a j.succ) (fun j => ha j.succ)
    have hd : (∏ j : Fin m, a j.succ) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => ha j.succ
    unfold oddity at ih ⊢
    rw [Fin.sum_univ_succ, ih, Fin.prod_univ_succ,
      hasseSerre_succ _ _ (fun i => by exact_mod_cast ha i)]
    push_cast
    rw [sgn4_mul_hilbert _ _ _ _ (hasseSerre_pm _ _)]
    have := oddityEntry_mul (ha 0) hd
    push_cast at this
    linear_combination this

/-- **The signature and the Hasse invariant at $\infty$** ($a_i \in \mathbb{Z}\setminus\{0\}$, $d = \prod a_i$):
$\mathrm{sig}\langle a_0,\dots,a_{n-1}\rangle \equiv \mathrm{sign}(d) + (n-1) + [\![\varepsilon_\infty]\!] \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373, eq. (17) (derived, p = -1)"]
theorem signature_eq_hasse : ∀ {n : ℕ} (a : Fin n → ℤ), (∀ i, a i ≠ 0) →
    (signature a : ZMod 8) = (Int.sign (∏ i, a i) : ZMod 8) + ((n : ZMod 8) - 1) +
      sgn4 (RatPlace.infinite.hasseSerre fun i => (a i : ℚ))
  | 0, a, _ => by simp [signature, RatPlace.hasseSerre, sgn4]
  | m + 1, a, ha => by
    have ih := signature_eq_hasse (fun j => a j.succ) (fun j => ha j.succ)
    have hd : (∏ j : Fin m, a j.succ) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => ha j.succ
    unfold signature at ih ⊢
    rw [Fin.sum_univ_succ, Int.cast_add, ih, Fin.prod_univ_succ,
      hasseSerre_succ _ _ (fun i => by exact_mod_cast ha i)]
    push_cast
    rw [sgn4_mul_hilbert _ _ _ _ (hasseSerre_pm _ _)]
    have := sign_mul_hilbert (ha 0) hd
    push_cast at this
    linear_combination this

/-! ### The oddity formula -/

/-- `pExcessEntry` vanishes at primes not dividing the entry. -/
theorem pExcessEntry_of_not_dvd {p : ℕ} {a : ℤ} (h : ¬ (p : ℤ) ∣ a) : pExcessEntry p a = 0 := by
  simp [pExcessEntry, padicValInt.eq_zero_of_not_dvd h]

/-- A set of odd primes **adapted** to $a$: it contains every odd prime dividing $a$. Internal. -/
def Adapted (S : Finset Nat.Primes) (a : ℤ) : Prop :=
  (∀ p ∈ S, p.1 ≠ 2) ∧ ∀ p : Nat.Primes, p.1 ≠ 2 → (p.1 : ℤ) ∣ a → p ∈ S

theorem sgn4_prod {ι : Type*} (T : Finset ι) (h : ι → ℤ) (hpm : ∀ i, h i = 1 ∨ h i = -1) :
    sgn4 (∏ i ∈ T, h i) = ∑ i ∈ T, sgn4 (h i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sgn4]
  | insert j T hj ih =>
    have hT : (∏ i ∈ T, h i) = 1 ∨ (∏ i ∈ T, h i) = -1 := by
      clear ih
      induction T using Finset.induction_on with
      | empty => simp
      | insert k T hk ih' =>
        rw [prod_insert hk]
        rcases hpm k with h1 | h1 <;> rcases ih' (fun h => hj (mem_insert_of_mem h)) with h2 | h2 <;>
          simp [h1, h2]
    rw [prod_insert hj, sum_insert hj, sgn4_mul (hpm j) hT, ih]

/-- **Hilbert reciprocity, additively:** for $a, b \in \mathbb{Z}\setminus\{0\}$ and a set $S$ of odd primes adapted to
$ab$, $[\![(a,b)_\infty]\!] + [\![(a,b)_2]\!] + \sum_{p \in S}[\![(a,b)_p]\!] = 0$ in $\mathbb{Z}/8$
(`hilbert_product_formula`). -/
theorem sum_sgn4_hilbert {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) {S : Finset Nat.Primes} (hS : Adapted S (a * b)) :
    sgn4 (RatPlace.infinite.hilbert a b) + sgn4 ((RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert a b) +
      ∑ p ∈ S, sgn4 ((RatPlace.finite p).hilbert a b) = 0 := by
  classical
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  obtain ⟨-, hprod⟩ := finprod_hilbert (a : ℚ) (b : ℚ) ha' hb'
  set T : Finset RatPlace :=
    insert RatPlace.infinite (insert (RatPlace.finite ⟨2, Nat.prime_two⟩) (S.image RatPlace.finite)) with hT
  have hsub : Function.mulSupport (fun v : RatPlace => v.hilbert a b) ⊆ T := by
    intro v hv
    by_contra hvT
    apply hv
    cases v with
    | infinite => exact absurd (mem_insert_self _ _) hvT
    | finite ℓ =>
      have h2 : ℓ.1 ≠ 2 := fun h => hvT (by
        rw [hT]; exact mem_insert_of_mem (by
          have : ℓ = ⟨2, Nat.prime_two⟩ := Subtype.ext h
          rw [this]; exact mem_insert_self _ _))
      have hℓS : ℓ ∉ S := fun h => hvT (by
        rw [hT]; exact mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ h)))
      have hnd : ¬ (ℓ.1 : ℤ) ∣ a * b := fun h => hℓS (hS.2 ℓ h2 h)
      have : Fact (ℓ.1).Prime := ⟨ℓ.2⟩
      have hva : padicValRat ℓ.1 (a : ℚ) = 0 := by
        rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (fun h => hnd (dvd_mul_of_dvd_left h b))]
        rfl
      have hvb : padicValRat ℓ.1 (b : ℚ) = 0 := by
        rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd (fun h => hnd (dvd_mul_of_dvd_right h a))]
        rfl
      exact HilbertLocal.hilbert_eq_one_of_padicValRat h2 _ _ ha' hb' hva hvb
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hprod
  have h0 := congrArg sgn4 hprod
  rw [sgn4_prod _ _ (fun v => RatPlace.hilbert_pm v _ _)] at h0
  have hinf : RatPlace.infinite ∉ insert (RatPlace.finite ⟨2, Nat.prime_two⟩) (S.image RatPlace.finite) := by
    simp
  have h2n : RatPlace.finite ⟨2, Nat.prime_two⟩ ∉ S.image RatPlace.finite := by
    simp only [mem_image, not_exists, not_and]
    intro x hx e
    injection e with e
    exact hS.1 x hx (by rw [e])
  rw [hT, sum_insert hinf, sum_insert h2n,
    sum_image (fun x _ y _ e => by injection e)] at h0
  have h1 : sgn4 1 = 0 := by simp [sgn4]
  rw [h1, ← add_assoc] at h0
  exact h0


/-- The rank-one oddity formula holds for $a$, for every adapted set of odd primes. Internal. -/
def Good (a : ℤ) : Prop :=
  ∀ S : Finset Nat.Primes, Adapted S a →
    ((Int.sign a : ℤ) : ZMod 8) + ∑ p ∈ S, pExcessEntry p.1 a = oddityEntry a

theorem good_mul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hA : Good a) (hB : Good b) : Good (a * b) := by
  intro S hS
  have e1 := hA S ⟨hS.1, fun p h2 h => hS.2 p h2 (h.trans (dvd_mul_right a b))⟩
  have e2 := hB S ⟨hS.1, fun p h2 h => hS.2 p h2 (h.trans (dvd_mul_left b a))⟩
  have es := sign_mul_hilbert ha hb
  have eo := oddityEntry_mul ha hb
  have hR := sum_sgn4_hilbert ha hb hS
  have h8 : (2 : ZMod 8) * sgn4 ((RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert a b) = 0 := by
    unfold sgn4; split_ifs <;> decide
  have ep : ∑ p ∈ S, pExcessEntry p.1 (a * b) = ∑ p ∈ S, pExcessEntry p.1 a + ∑ p ∈ S, pExcessEntry p.1 b -
      ∑ p ∈ S, sgn4 ((RatPlace.finite p).hilbert a b) := by
    rw [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨q, hq⟩ := p
    have : Fact q.Prime := ⟨hq⟩
    have h := pExcessEntry_mul q (hS.1 _ hp) ha hb
    linear_combination -h
  rw [ep]
  linear_combination e1 + e2 - es + eo - hR + h8

theorem not_dvd_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) : ¬ (p : ℤ) ∣ (q : ℤ) := by
  rw [Int.natCast_dvd_natCast]
  exact fun hd => h ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)

theorem good_neg_one : Good (-1) := by
  intro S _
  have hsum : ∑ p ∈ S, pExcessEntry p.1 (-1) = 0 := Finset.sum_eq_zero fun p _ =>
    pExcessEntry_of_not_dvd fun h => p.2.ne_one (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (by simpa using h)))
  rw [hsum]
  simp [oddityEntry, unitPart, padicValInt]

theorem good_two : Good 2 := by
  intro S hS
  have hsum : ∑ p ∈ S, pExcessEntry p.1 2 = 0 := Finset.sum_eq_zero fun p hp =>
    pExcessEntry_of_not_dvd (by exact_mod_cast not_dvd_of_prime_ne p.2 Nat.prime_two (hS.1 p hp))
  rw [hsum]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : padicValInt 2 2 = 1 := padicValInt_self
  simp [oddityEntry, unitPart, h1]
  decide

theorem good_odd_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : Good q := by
  intro S hS
  have : Fact q.Prime := ⟨hq⟩
  have hmem : (⟨q, hq⟩ : Nat.Primes) ∈ S := hS.2 ⟨q, hq⟩ hq2 dvd_rfl
  have hsum : ∑ p ∈ S, pExcessEntry p.1 (q : ℤ) = pExcessEntry q q := by
    refine Finset.sum_eq_single_of_mem (⟨q, hq⟩ : Nat.Primes) hmem ?_
    intro p _ hpq
    exact pExcessEntry_of_not_dvd (not_dvd_of_prime_ne p.2 hq fun h => hpq (Subtype.ext h))
  rw [hsum]
  have h1 : padicValInt q q = 1 := padicValInt_self
  have h2 : padicValInt 2 (q : ℤ) = 0 :=
    padicValInt.eq_zero_of_not_dvd (by exact_mod_cast not_dvd_of_prime_ne Nat.prime_two hq hq2.symm)
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h3 : (q : ℤ) / q = 1 := Int.ediv_self hq0
  simp [pExcessEntry, oddityEntry, unitPart, h1, h2, h3, jacobiSym.one_left,
    Int.sign_natCast_of_ne_zero hq.ne_zero] <;> ring

theorem good_of_ne_zero (a : ℤ) (ha : a ≠ 0) : Good a := by
  have hnat : ∀ m : ℕ, m ≠ 0 → Good m := by
    intro m
    induction m using induction_on_primes with
    | zero => intro h; exact absurd rfl h
    | one =>
      intro _
      have := good_mul (by norm_num) (by norm_num) good_neg_one good_neg_one
      simpa using this
    | prime_mul q m hq ih =>
      intro h
      have hm : m ≠ 0 := by rintro rfl; simp at h
      have hqg : Good q := by
        rcases eq_or_ne q 2 with rfl | hq2
        · exact_mod_cast good_two
        · exact good_odd_prime hq hq2
      have := good_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hm) hqg (ih hm)
      exact_mod_cast this
  have hm : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  rcases Int.natAbs_eq a with h | h
  · rw [h]; exact hnat _ hm
  · rw [h, neg_eq_neg_one_mul]
    exact good_mul (by norm_num) (by exact_mod_cast hm) good_neg_one (hnat _ hm)

/-- **The rank-one defect vanishes:** for $a \in \mathbb{Z}\setminus\{0\}$ and a set $S$ of odd primes adapted to $a$,
$\mathrm{sign}(a) + \sum_{p\in S} p\text{-excess}\langle a\rangle \equiv \mathrm{oddity}\langle a\rangle \pmod 8$. -/
theorem oddity_formula_entry (a : ℤ) (ha : a ≠ 0) (S : Finset Nat.Primes) (hS : Adapted S a) :
    ((Int.sign a : ℤ) : ZMod 8) + ∑ p ∈ S, pExcessEntry p.1 a = oddityEntry a :=
  good_of_ne_zero a ha S hS

/-- **Conway–Sloane's oddity formula** for a diagonal form $\langle a_0,\dots,a_{n-1}\rangle$, $a_i \in
\mathbb{Z}\setminus\{0\}$, summing over any finite set $S$ of odd primes containing those dividing $\prod_i a_i$:
$$\mathrm{signature}(f) + \sum_{p \in S} p\text{-excess}(f) \equiv \mathrm{oddity}(f) \pmod 8.$$ -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371, eq. (16); §7.7, p. 383, eq. (30)"]
theorem oddity_formula_of_adapted (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (S : Finset Nat.Primes)
    (hS : Adapted S (∏ i, a i)) :
    (signature a : ZMod 8) + ∑ p ∈ S, pExcess p.1 a = oddity a := by
  unfold signature pExcess oddity
  rw [sum_comm, Int.cast_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => oddity_formula_entry (a i) (ha i) S ⟨hS.1, fun p hp2 hp => ?_⟩
  exact hS.2 p hp2 (hp.trans (dvd_prod_of_mem _ (mem_univ i)))

/-- **The odd primes dividing $\prod_i a_i$**, as a set of `Nat.Primes`. -/
def oddPrimeSet (a : Fin n → ℤ) : Finset Nat.Primes :=
  (((∏ i, a i).natAbs.primeFactors).erase 2).subtype Nat.Prime

theorem adapted_oddPrimeSet (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) : Adapted (oddPrimeSet a) (∏ i, a i) := by
  have hd : (∏ i, a i) ≠ 0 := prod_ne_zero_iff.mpr fun i _ => ha i
  refine ⟨fun p hp => ?_, fun p hp2 hp => ?_⟩
  · have h : (p : ℕ) ∈ ((∏ i, a i).natAbs.primeFactors).erase 2 := Finset.mem_subtype.mp hp
    exact (mem_erase.mp h).1
  · exact Finset.mem_subtype.mpr (mem_erase.mpr ⟨hp2, Nat.mem_primeFactors.mpr
      ⟨p.2, Int.natCast_dvd.mp hp, Int.natAbs_ne_zero.mpr hd⟩⟩)

/-- **Conway–Sloane's oddity formula** (*Sphere Packings, Lattices and Groups*, Ch. 15, §5.1, p. 371, eq. (16);
restated for Jordan symbols as eq. (30), §7.7, p. 383):
for a nondegenerate diagonal form $f = \langle a_0,\dots,a_{n-1}\rangle$ with $a_i \in \mathbb{Z}\setminus\{0\}$,
$$\mathrm{signature}(f) + \sum_{p \ge 3} p\text{-excess}(f) \equiv \mathrm{oddity}(f) \pmod 8,$$
the sum running over the odd primes (only those dividing $\prod_i a_i$ contribute, `oddPrimeSet`). Proved from
Hilbert reciprocity over $\mathbb{Q}$. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371, eq. (16); §7.7, p. 383, eq. (30)"]
theorem oddity_formula (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    (signature a : ZMod 8) + ∑ p ∈ oddPrimeSet a, pExcess p.1 a = oddity a :=
  oddity_formula_of_adapted a ha _ (adapted_oddPrimeSet a ha)


/-! ### The entry-wise and Jordan-constituent formulas agree -/

theorem jacobiSym_prod_left {ι : Type*} (T : Finset ι) (f : ι → ℤ) (p : ℕ) :
    jacobiSym (∏ i ∈ T, f i) p = ∏ i ∈ T, jacobiSym (f i) p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [jacobiSym.one_left]
  | insert j T hj ih => rw [prod_insert hj, prod_insert hj, jacobiSym.mul_left, ih]

theorem ite_odd_sgn4 (e : ℕ) (J : ℤ) :
    (if Odd e ∧ J = -1 then (4 : ZMod 8) else 0) = if Odd e then sgn4 J else 0 := by
  by_cases h : Odd e <;> simp [h, sgn4]

/-- **The entry-wise $p$-excess equals Conway–Sloane's Jordan-constituent formula** for a diagonal form
($p$ an odd prime, $a_i \ne 0$). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371; §7.7, p. 383"]
theorem pExcess_eq_pExcessJordan (p : ℕ) [hp : Fact p.Prime] (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    pExcess p a = pExcessJordan p a := by
  classical
  unfold pExcess pExcessJordan
  rw [← sum_fiberwise_of_maps_to (g := fun i => padicValInt p (a i)) (t := univ.image fun i => padicValInt p (a i))
    (fun i _ => mem_image_of_mem _ (mem_univ i))]
  refine sum_congr rfl fun e _ => ?_
  have hJ : ∀ i, jacobiSym (unitPart p (a i)) p = 1 ∨ jacobiSym (unitPart p (a i)) p = -1 := fun i => by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact legendreSym.eq_one_or_neg_one p
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact not_dvd_unitPart (ha i))
  rw [ite_odd_sgn4, jacobiSym_prod_left, sgn4_prod _ _ (fun i => hJ i)]
  have : ∀ i ∈ univ.filter (fun i => padicValInt p (a i) = e), pExcessEntry p (a i) =
      ((p : ZMod 8) ^ e - 1) + if Odd e then sgn4 (jacobiSym (unitPart p (a i)) p) else 0 := by
    intro i hi
    rw [(mem_filter.mp hi).2.symm, pExcessEntry, ite_odd_sgn4]
  rw [sum_congr rfl this, sum_add_distrib, sum_const, nsmul_eq_mul]
  by_cases he : Odd e
  · simp only [he, if_true]
  · simp only [he, if_false, sum_const_zero]

/-- The character $u \mapsto -1$ iff $u \equiv \pm 3 \pmod 8$ on odd residues. Internal. -/
def twoChar (r : ZMod 8) : ℤ := if r = 3 ∨ r = 5 then -1 else 1

def OddRes (r : ZMod 8) : Prop := r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7

theorem twoChar_prod {ι : Type*} (T : Finset ι) (f : ι → ZMod 8) (hf : ∀ i ∈ T, OddRes (f i)) :
    OddRes (∏ i ∈ T, f i) ∧ twoChar (∏ i ∈ T, f i) = ∏ i ∈ T, twoChar (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact ⟨Or.inl rfl, (by decide : twoChar 1 = 1)⟩
  | insert j T hj ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (mem_insert_of_mem hi)
    rw [prod_insert hj, prod_insert hj, ← h2]
    have hj' := hf j (mem_insert_self _ _)
    generalize f j = r at hj' ⊢
    generalize ∏ i ∈ T, f i = t at h1 ⊢
    unfold OddRes at hj' h1 ⊢
    rcases hj' with rfl | rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl | rfl <;> decide

theorem ite_odd_twoChar (e : ℕ) (r : ZMod 8) :
    (if Odd e ∧ (r = 3 ∨ r = 5) then (4 : ZMod 8) else 0) = if Odd e then sgn4 (twoChar r) else 0 := by
  by_cases h : Odd e <;> by_cases h' : r = 3 ∨ r = 5 <;> simp [h, h', sgn4, twoChar]

/-- **The entry-wise oddity equals Conway–Sloane's Jordan-constituent formula** for a diagonal form ($a_i \ne 0$). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371; §7.7, p. 383"]
theorem oddity_eq_oddityJordan (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) : oddity a = oddityJordan a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold oddity oddityJordan
  rw [← sum_fiberwise_of_maps_to (g := fun i => padicValInt 2 (a i)) (t := univ.image fun i => padicValInt 2 (a i))
    (fun i _ => mem_image_of_mem _ (mem_univ i))]
  refine sum_congr rfl fun e _ => ?_
  have hodd : ∀ i, OddRes ((unitPart 2 (a i) : ℤ) : ZMod 8) := fun i =>
    intCast_zmod8_odd (by exact_mod_cast not_dvd_unitPart (p := 2) (ha i))
  obtain ⟨-, hprod⟩ := twoChar_prod (univ.filter fun i => padicValInt 2 (a i) = e)
    (fun i => ((unitPart 2 (a i) : ℤ) : ZMod 8)) (fun i _ => hodd i)
  rw [Int.cast_prod, ite_odd_twoChar, hprod, sgn4_prod _ _ (fun i => by unfold twoChar; split_ifs <;> simp)]
  have : ∀ i ∈ univ.filter (fun i => padicValInt 2 (a i) = e), oddityEntry (a i) =
      ((unitPart 2 (a i) : ℤ) : ZMod 8) + if Odd e then sgn4 (twoChar (unitPart 2 (a i) : ZMod 8)) else 0 := by
    intro i hi
    rw [(mem_filter.mp hi).2.symm, oddityEntry, ite_odd_twoChar]
  rw [sum_congr rfl this, sum_add_distrib]
  by_cases he : Odd e
  · simp only [he, if_true]
  · simp only [he, if_false, sum_const_zero]

/-! ### Conway–Sloane's own normalizations: $p$-signatures, excesses at every place, eq. (15) and (17) -/

/-- **Conway–Sloane's rational $p$-signature of the rank-one form $\langle a \rangle$** ($p$ odd,
$a = p^e u$, $p \nmid u$): $p^e + 4\,[p^e u \text{ is a } p\text{-adic antisquare}] \in \mathbb{Z}/8$, where an
antisquare is $p^{\mathrm{odd}}u_-$, i.e. $e$ odd and $(u/p) = -1$ (Conway–Sloane, Ch. 15, §5.1, p. 370). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, pp. 370–371"]
def pSignatureEntry (p : ℕ) (a : ℤ) : ZMod 8 :=
  (p : ZMod 8) ^ padicValInt p a +
    if Odd (padicValInt p a) ∧ jacobiSym (unitPart p a) p = -1 then 4 else 0

/-- **Conway–Sloane's rational $p$-signature** of $f = \mathrm{diag}\{p^{\alpha}a, p^{\beta}b, \dots\}$ ($p$ odd):
$$p\text{-signature}(f) = p^{\alpha} + p^{\beta} + \dots + 4m \pmod 8,$$
$m$ the number of $p$-adic antisquares among the entries (Conway–Sloane, Ch. 15, §5.1, p. 371, first display). For $p = 2$ the
book's 2-signature $a + b + \dots + 4m$ is the oddity (`oddity`), and for $p = -1$ (the book's name for $\infty$) the
$(-1)$-signature is the ordinary signature (`signature`). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def pSignature (p : ℕ) (a : Fin n → ℤ) : ZMod 8 := ∑ i, pSignatureEntry p (a i)

/-- **The $p$-excess is the $p$-signature minus the dimension** ($p$ odd), Conway–Sloane's definition of the
$p$-excess (Conway–Sloane, Ch. 15, §5.1, p. 371): `pExcess` (defined entry-wise) agrees with it. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
theorem pExcess_eq_pSignature_sub (p : ℕ) (a : Fin n → ℤ) :
    pExcess p a = pSignature p a - n := by
  simp [pExcess, pSignature, pExcessEntry, pSignatureEntry, sub_add_eq_add_sub, sum_sub_distrib]

/-- **Conway–Sloane's 2-excess**: dimension minus 2-signature, $n - \mathrm{oddity}(f)$ (Conway–Sloane, Ch. 15, §5.1, p. 371).
Note the reversed sign relative to the $p$-excess for $p \ne 2$. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def twoExcess (a : Fin n → ℤ) : ZMod 8 := (n : ZMod 8) - oddity a

/-- **Conway–Sloane's $(-1)$-excess**: $(-1)$-signature minus dimension, $\mathrm{signature}(f) - n$
(Conway–Sloane, Ch. 15, §5.1, p. 371: the $p$-excess for $p \ne 2$, with $p = -1$ included). -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def negOneExcess (a : Fin n → ℤ) : ZMod 8 := (signature a : ZMod 8) - n

/-- **Conway–Sloane's $p$-excess at every place $v$ of $\mathbb{Q}$** (Conway–Sloane, Ch. 15, §5.1, p. 371): the
$(-1)$-excess at $\infty$ (their "prime $-1$"), the 2-excess $n - \mathrm{oddity}$ at $2$, and the $p$-excess
$p\text{-signature} - n$ at an odd prime $p$. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371"]
def excess : RatPlace → (Fin n → ℤ) → ZMod 8
  | .infinite, a => negOneExcess a
  | .finite p, a => if p.1 = 2 then twoExcess a else pExcess p.1 a

/-- **Conway–Sloane's sum formula (15)**: for a diagonal form $f = \langle a_0,\dots,a_{n-1}\rangle$,
$a_i \in \mathbb{Z}\setminus\{0\}$,
$$\sum_{\text{all } p} p\text{-excess}(f) \equiv 0 \pmod 8,$$
the sum over $p = -1$ ($\infty$), $p = 2$ and the odd primes (only those dividing $\prod_i a_i$ contribute,
`oddPrimeSet`). Equivalent to the oddity formula (16) = (30) (`oddity_formula`), from which it is derived. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371, eq. (15)"]
theorem sum_excess_eq_zero (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    excess .infinite a + excess (.finite ⟨2, Nat.prime_two⟩) a +
      ∑ p ∈ oddPrimeSet a, excess (.finite p) a = 0 := by
  have hS := adapted_oddPrimeSet a ha
  have h : ∑ p ∈ oddPrimeSet a, excess (.finite p) a = ∑ p ∈ oddPrimeSet a, pExcess p.1 a :=
    sum_congr rfl fun p hp => by simp [excess, hS.1 p hp]
  rw [h]
  simp only [excess, if_true, negOneExcess, twoExcess]
  linear_combination oddity_formula a ha

/-- **Conway–Sloane's sum formula (15), in $p$-signature form**:
$$2\text{-signature} - \text{dimension} \equiv \sum_{\text{odd } p} \big(p\text{-signature} - \text{dimension}\big)
\pmod 8,$$
where "odd $p$" **includes $p = -1$** (the book's prime $-1$, here the `signature` term); the $p \ge 3$ terms are over
the odd primes dividing $\prod_i a_i$ (`oddPrimeSet`; the others vanish).
*Clarification:* read with "odd $p$" meaning $p \ge 3$ only, (15) is false: for $\mathrm{diag}\{1,3,-3\}$ (the book's
example, p. 371) the left side is $1 - 3 = -2$ and the $p \ge 3$ terms sum to $8 \equiv 0$. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371, eq. (15)"]
theorem sum_formula_pSignature (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    oddity a - n = ((signature a : ZMod 8) - n) + ∑ p ∈ oddPrimeSet a, (pSignature p.1 a - n) := by
  have h : ∑ p ∈ oddPrimeSet a, (pSignature p.1 a - n) = ∑ p ∈ oddPrimeSet a, pExcess p.1 a :=
    sum_congr rfl fun p _ => (pExcess_eq_pSignature_sub p.1 a).symm
  rw [h]
  linear_combination -(oddity_formula a ha)

/-- **Conway–Sloane's "standard" form** $f_0 = \mathrm{diag}\{A_1A_2\cdots A_n, 1, \dots, 1\}$ with the same
determinant and dimension as $f = \mathrm{diag}\{A_1,\dots,A_n\}$, $n \ge 1$ (Conway–Sloane, Ch. 15, §5.3, p. 373; 0-based
here: entry $0$ is $\prod_i a_i$, the others are $1$). -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373"]
def standardForm {m : ℕ} (a : Fin (m + 1) → ℤ) : Fin (m + 1) → ℤ := Fin.cons (∏ i, a i) fun _ => 1

theorem sgn4_eq_zero_iff {s : ℤ} (hs : s = 1 ∨ s = -1) : sgn4 s = 0 ↔ s = 1 := by
  rcases hs with rfl | rfl <;> simp [sgn4] <;> decide

theorem neg_sgn4 (s : ℤ) : -sgn4 s = sgn4 s := by
  unfold sgn4; split_ifs <;> decide

theorem pExcess_standardForm (p : ℕ) [Fact p.Prime] {m : ℕ} (a : Fin (m + 1) → ℤ) :
    pExcess p (standardForm a) = pExcessEntry p (∏ i, a i) := by
  have h1 : pExcessEntry p 1 = 0 := by simp [pExcessEntry, padicValInt.one]
  simp [pExcess, standardForm, Fin.sum_univ_succ, h1]

theorem oddity_standardForm {m : ℕ} (a : Fin (m + 1) → ℤ) :
    oddity (standardForm a) = oddityEntry (∏ i, a i) + m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : oddityEntry 1 = 1 := by simp [oddityEntry, unitPart, padicValInt.one]
  simp [oddity, standardForm, Fin.sum_univ_succ, h1]

theorem signature_standardForm {m : ℕ} (a : Fin (m + 1) → ℤ) :
    (signature (standardForm a) : ZMod 8) = (Int.sign (∏ i, a i) : ZMod 8) + m := by
  simp [signature, standardForm, Fin.sum_univ_succ]

/-- **Conway–Sloane's recovery of the Hasse–Minkowski invariant from the $p$-excess** (Conway–Sloane, Ch. 15, §5.3, p. 373):
for $f = \mathrm{diag}\{A_1,\dots,A_n\}$, $n \ge 1$, $A_i \in \mathbb{Z}\setminus\{0\}$, and every place $p$ of
$\mathbb{Q}$ (including $p = -1$, i.e. $\infty$, and $p = 2$), the invariant
$(f)_p = \prod_{i<j}(A_i,A_j)_p$ of eq. (17) (`RatPlace.hasseConwaySloane`) is $+1$ or $-1$ according as the
$p$-excess of $f$ (`excess`: the $(-1)$-excess, the 2-excess $n - \mathrm{oddity}$, or the $p$-excess) is or is not
congruent mod 8 to that of the standard form $f_0 = \mathrm{diag}\{A_1\cdots A_n, 1, \dots, 1\}$ (`standardForm`).
The book states this without proof; it follows from `pExcess_eq_hasse`, `oddity_eq_hasse`, `signature_eq_hasse`. -/
@[kb "conwaysloane1999" "Ch. 15, §5.3, p. 373"]
theorem hasseConwaySloane_eq_one_iff (v : RatPlace) {m : ℕ} (a : Fin (m + 1) → ℤ) (ha : ∀ i, a i ≠ 0) :
    v.hasseConwaySloane (fun i => (a i : ℚ)) = 1 ↔ excess v a = excess v (standardForm a) := by
  rw [RatPlace.hasseConwaySloane_eq_hasseSerre, ← sub_eq_zero (a := excess v a)]
  have hpm := hasseSerre_pm v fun i => (a i : ℚ)
  rw [← sgn4_eq_zero_iff hpm]
  suffices h : excess v a - excess v (standardForm a) = sgn4 (v.hasseSerre fun i => (a i : ℚ)) by rw [h]
  rcases v with _ | ⟨p, hp⟩
  · have h := signature_eq_hasse a ha
    simp only [excess, negOneExcess]
    rw [h, signature_standardForm]; push_cast; ring
  · by_cases h2 : p = 2
    · subst h2
      have h := oddity_eq_hasse a ha
      simp only [excess, if_true, twoExcess]
      rw [h, oddity_standardForm]; push_cast
      linear_combination neg_sgn4 ((RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre fun i => (a i : ℚ))
    · have : Fact p.Prime := ⟨hp⟩
      have h := pExcess_eq_hasse p h2 a ha
      simp only [excess, h2, ite_false]
      rw [h, pExcess_standardForm]; ring

/-- **Conway–Sloane: $p$-excesses are always even, and divisible by 4 if $p \equiv 1 \pmod 4$**
(Conway–Sloane, Ch. 15, §5.2, Remark (2), p. 373), for $p$ an odd prime, in $\mathbb{Z}/8$: $4\cdot p\text{-excess} = 0$, and
$2 \cdot p\text{-excess} = 0$ when $p \equiv 1 \pmod 4$. (For any integers $a_i$; no nonvanishing needed.) -/
@[kb "conwaysloane1999" "Ch. 15, §5.2, Remark (2), p. 373"]
theorem pExcess_even (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a : Fin n → ℤ) :
    4 * pExcess p a = 0 ∧ (p % 4 = 1 → 2 * pExcess p a = 0) := by
  have hr := natCast_zmod8_odd (hp.out.odd_of_ne_two hp2)
  have h4 : p % 4 = 1 → (p : ZMod 8) = 1 ∨ (p : ZMod 8) = 5 := by
    intro h
    rw [← ZMod.natCast_mod p 8]
    have : p % 8 = 1 ∨ p % 8 = 5 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  unfold pExcess
  rw [mul_sum, mul_sum]
  refine ⟨sum_eq_zero fun i _ => ?_, fun h => sum_eq_zero fun i _ => ?_⟩
  · unfold pExcessEntry
    rw [pow_zmod8_eq hr]
    generalize (p : ZMod 8) = r at hr ⊢
    split_ifs <;> rcases hr with rfl | rfl | rfl | rfl <;> decide
  · unfold pExcessEntry
    rw [pow_zmod8_eq hr]
    have h' := h4 h
    generalize (p : ZMod 8) = r at h' ⊢
    split_ifs <;> rcases h' with rfl | rfl <;> decide

/-- **Conway–Sloane's worked example** (Conway–Sloane, Ch. 15, §5.1, p. 371): for $f = \mathrm{diag}\{1, 3, -3\}$, the
signature is $1+1-1 = 1$, the 3-excess is $0+2+2+4 = 8 \equiv 0$ ($-3$ is a 3-adic antisquare), and the oddity is
$1+3-3 = 1$, so (16) reads $1 + 8 + 0 + \dots \equiv 1 \pmod 8$. A check of the definitions against the book. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, p. 371 (Example)"]
theorem example_diag_one_three_neg_three :
    signature ![(1 : ℤ), 3, -3] = 1 ∧ pExcess 3 ![(1 : ℤ), 3, -3] = 0 ∧ oddity ![(1 : ℤ), 3, -3] = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨by decide, ?_, ?_⟩
  · have h3 : padicValInt 3 3 = 1 := padicValInt_self
    have h3' : padicValInt 3 (-3) = 1 := by simp [padicValInt]
    simp [pExcess, pExcessEntry, Fin.sum_univ_succ, unitPart, h3, h3', padicValInt.one]
    norm_num
    decide
  · have h3 : padicValInt 2 3 = 0 := padicValInt.eq_zero_of_not_dvd (by decide)
    have h3' : padicValInt 2 (-3) = 0 := padicValInt.eq_zero_of_not_dvd (by decide)
    simp [oddity, oddityEntry, Fin.sum_univ_succ, unitPart, h3, h3', padicValInt.one]

end ConwaySloane

end QuadFormsKB
