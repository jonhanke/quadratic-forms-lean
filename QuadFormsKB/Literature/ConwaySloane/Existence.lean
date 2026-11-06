/-
# Conway–Sloane, Ch. 15, §7.7: the conditions on putative $p$-adic symbols

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §7.7, pp. 382–384
(`conwaysloane1999`).

Which systems of $p$-adic symbols come from integral forms: the determinant conditions (29), the oddity condition
(30), and the existence conditions (31)–(35) on the individual Jordan constituents.

**Conventions.** Symbols are those of `Symbol.lean` (functions on the exponents $k \ge 0$ of the scales $p^k$); a
symbol is *supported below $N$* if its constituents of scale $\ge p^N$ are zero-dimensional (type II, sign $+$,
oddity $0$ at $p = 2$). Sums over the constituents are taken over $k < N$.

**Defines**
* `OddFactor.Exists` (31) and `TwoFactor.Exists` (32)–(35): the existence conditions for one constituent;
* `OddSymbol.pExcess` ($\sum_q n_q(q-1) + 4k_p$) and `TwoSymbol.oddity` ($\sum_q t_q + 4k_2$), with $k_p$ the number of
  antisquare terms ($q$ an odd power of $p$ and $\varepsilon_q = -$), §7.7, p. 383;
* `OddSymbol.DetCond`, `TwoSymbol.DetCond` (29): the power of $p$ and the sign product match the determinant;
* `GenusSymbolData`: a putative system of symbols for all $p$ (dimension, determinant, $(-1)$-adic symbol, a $p$-adic
  symbol for every prime) and `GenusSymbolData.Conditions`: (29)–(35).

**Proves**
* `TwoFactor.exists_iff_of_dim_one`, `TwoFactor.exists_iff_of_dim_two_typeI`: (33), (34) as stated;
* `TwoFactor.Exists.typeI_of_odd`: $n$ odd $\Rightarrow$ type I ((35));
* `pExcess_congr`, `oddity_congr`: the sums do not depend on the bound $N$ beyond the support.
-/
import QuadFormsKB.Literature.ConwaySloane.Symbol

namespace QuadFormsKB.ConwaySloane

open Finset

/-! ### Existence conditions for one constituent -/

/-- **Existence condition (31)** for a Jordan constituent at an odd prime (Conway–Sloane, §7.7, p. 383): a
zero-dimensional constituent has sign $+$. (At $p = -1$ the symbol $+^r-^s$ has no signs.) -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (31), p. 383"]
def OddFactor.Exists (f : OddFactor) : Prop := f.dim = 0 → f.sign = .plus

/-- **Existence conditions (32)–(35)** for a 2-adic Jordan constituent $q_t^{\varepsilon n}$ (Conway–Sloane, §7.7,
p. 383):
* (32) if $n = 0$: type II and $\varepsilon = +$;
* (33) if $n = 1$: $\varepsilon = + \Rightarrow t \equiv \pm1$, $\varepsilon = - \Rightarrow t \equiv \pm3 \pmod 8$;
* (34) if $n = 2$ and type I: $\varepsilon = + \Rightarrow t \equiv 0, \pm2$, $\varepsilon = - \Rightarrow t \equiv 4, \pm2$;
* (35) $t \equiv n \pmod 2$ for type I, and $t \equiv 0 \pmod 8$ for type II (so $n$ odd $\Rightarrow$ type I).

The book states $t \equiv n \pmod 2$ "for general $n$" and $t \equiv 0$ for type II; for type II this forces $n$ even.
Here the parity condition is stated for both types (`(f.oddity.val % 2 = f.dim % 2)`), which for type II says $n$ is
even. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (32)–(35), p. 383"]
def TwoFactor.Exists (f : TwoFactor) : Prop :=
  (f.dim = 0 → f.type = .II ∧ f.sign = .plus) ∧
  (f.dim = 1 → (f.sign = .plus → f.oddity = 1 ∨ f.oddity = 7) ∧ (f.sign = .minus → f.oddity = 3 ∨ f.oddity = 5)) ∧
  (f.dim = 2 → f.type = .I →
    (f.sign = .plus → f.oddity = 0 ∨ f.oddity = 2 ∨ f.oddity = 6) ∧
    (f.sign = .minus → f.oddity = 4 ∨ f.oddity = 2 ∨ f.oddity = 6)) ∧
  f.oddity.val % 2 = f.dim % 2 ∧ (f.type = .II → f.oddity = 0)

set_option synthInstance.maxSize 1024 in
instance (f : TwoFactor) : Decidable f.Exists := by unfold TwoFactor.Exists; infer_instance

instance (f : OddFactor) : Decidable f.Exists := inferInstanceAs (Decidable (_ → _))

/-- (35): a 2-adic constituent of odd dimension has type I. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (35), p. 383"]
theorem TwoFactor.Exists.typeI_of_odd {f : TwoFactor} (h : f.Exists) (hn : f.dim % 2 = 1) : f.type = .I := by
  obtain ⟨-, -, -, hpar, hII⟩ := h
  cases ht : f.type with
  | I => rfl
  | II =>
    have := hII ht
    rw [this] at hpar
    simp at hpar
    omega

/-- (33): a one-dimensional 2-adic constituent $q_t^{\pm1}$ exists iff it is of type I with $t \equiv \pm1$ (sign $+$)
or $t \equiv \pm3$ (sign $-$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (33), p. 383"]
theorem TwoFactor.exists_iff_of_dim_one (f : TwoFactor) (h1 : f.dim = 1) :
    f.Exists ↔ f.type = .I ∧ ((f.sign = .plus ∧ (f.oddity = 1 ∨ f.oddity = 7)) ∨
      (f.sign = .minus ∧ (f.oddity = 3 ∨ f.oddity = 5))) := by
  obtain ⟨n, s, t, o⟩ := f
  simp only at h1; subst h1
  cases s <;> cases t <;> revert o <;> decide

/-- (34): a two-dimensional 2-adic constituent of type I exists iff $t \equiv 0, \pm2$ (sign $+$) or
$t \equiv 4, \pm2$ (sign $-$). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (34), p. 383"]
theorem TwoFactor.exists_iff_of_dim_two_typeI (f : TwoFactor) (h2 : f.dim = 2) (hI : f.type = .I) :
    f.Exists ↔ ((f.sign = .plus ∧ (f.oddity = 0 ∨ f.oddity = 2 ∨ f.oddity = 6)) ∨
      (f.sign = .minus ∧ (f.oddity = 4 ∨ f.oddity = 2 ∨ f.oddity = 6))) := by
  obtain ⟨n, s, t, o⟩ := f
  simp only at h2 hI; subst h2; subst hI
  cases s <;> revert o <;> decide

/-! ### The invariants of the oddity formula, from the symbols -/

/-- The indicator $[\,c\,] \in \mathbb Z/8$ of a decidable condition. -/
def ind8 (c : Prop) [Decidable c] : ZMod 8 := if c then 1 else 0

/-- **The $p$-excess from a $p$-adic symbol** (Conway–Sloane, §7.7, p. 383): $\sum_q n_q(q - 1) + 4k_p \pmod 8$, $q = p^k$,
where $k_p$ is the number of *antisquare terms*: $q$ not a square ($k$ odd) and $\varepsilon_q = -$. Summed over
$k < N$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 383"]
def OddSymbol.pExcess (p : ℕ) (σ : OddSymbol) (N : ℕ) : ZMod 8 :=
  ∑ k ∈ range N, (((σ k).dim : ZMod 8) * ((p : ZMod 8) ^ k - 1) + 4 * ind8 (Odd k ∧ (σ k).sign = .minus))

/-- **The oddity from a 2-adic symbol** (Conway–Sloane, §7.7, p. 383): $\sum_q t_q + 4k_2 \pmod 8$, where $k_2$ is the
number of antisquare terms ($q = 2^k$ with $k$ odd and $\varepsilon_q = -$). Summed over $k < N$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 383"]
def TwoSymbol.oddity (σ : TwoSymbol) (N : ℕ) : ZMod 8 :=
  ∑ k ∈ range N, ((σ k).oddity + 4 * ind8 (Odd k ∧ (σ k).sign = .minus))

/-- The $p$-adic symbol has only zero-dimensional constituents (with sign $+$) from the scale $p^N$ on. -/
def OddSymbol.SupportedBelow (σ : OddSymbol) (N : ℕ) : Prop := ∀ k, N ≤ k → σ k = OddFactor.trivial

/-- The 2-adic symbol has only zero-dimensional constituents (type II, sign $+$, oddity $0$) from the scale $2^N$
on. -/
def TwoSymbol.SupportedBelow (σ : TwoSymbol) (N : ℕ) : Prop := ∀ k, N ≤ k → σ k = TwoFactor.trivial

theorem OddSymbol.pExcess_congr (p : ℕ) {σ : OddSymbol} {N M : ℕ} (hN : σ.SupportedBelow N) (hNM : N ≤ M) :
    σ.pExcess p M = σ.pExcess p N := by
  unfold OddSymbol.pExcess
  rw [← Finset.sum_range_add_sum_Ico _ hNM]
  rw [Finset.sum_eq_zero (s := Ico N M) fun k hk => by
    rw [hN k (Finset.mem_Ico.mp hk).1]; simp [OddFactor.trivial, ind8]]
  simp

theorem TwoSymbol.oddity_congr {σ : TwoSymbol} {N M : ℕ} (hN : σ.SupportedBelow N) (hNM : N ≤ M) :
    σ.oddity M = σ.oddity N := by
  unfold TwoSymbol.oddity
  rw [← Finset.sum_range_add_sum_Ico _ hNM]
  rw [Finset.sum_eq_zero (s := Ico N M) fun k hk => by
    rw [hN k (Finset.mem_Ico.mp hk).1]; simp [TwoFactor.trivial, ind8]]
  simp

/-! ### The determinant conditions (29) -/

/-- The product of the signs $\varepsilon_q$, $q = p^k$, $k < N$, as a sign. -/
def signProd (s : ℕ → Sign) : ℕ → Sign
  | 0 => .plus
  | N + 1 => (signProd s N).mul (s N)

/-- **The determinant condition (29) at an odd prime $p$** (Conway–Sloane, §7.7, pp. 382–383): for $\det f = p^\alpha a$
with $(a, p) = 1$, the powers of $p$ in the symbol account for $p^\alpha$ ($\sum_q k\,n_q = \alpha$, $q = p^k$) and the
product of the signs is $\left(\frac{a}{p}\right)$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29), pp. 382–383"]
def OddSymbol.DetCond (p : ℕ) (σ : OddSymbol) (N : ℕ) (d : ℤ) : Prop :=
  ∑ k ∈ range N, k * (σ k).dim = padicValInt p d ∧
    signProd (fun k => (σ k).sign) N = Sign.ofInt (jacobiSym (d / (p : ℤ) ^ padicValInt p d) p)

/-- The extended Jacobi–Legendre symbol at $2$ of an odd integer (Conway–Sloane, §4.3, p. 368): $+1$ if
$\nu \equiv \pm1 \pmod 8$, $-1$ if $\nu \equiv \pm3 \pmod 8$. -/
@[kb "conwaysloane1999" "Ch. 15, §4.3, p. 368"]
def jacobiTwo (ν : ℤ) : Sign := if ν % 8 = 1 ∨ ν % 8 = 7 then .plus else .minus

/-- **The determinant condition (29) at $p = 2$** (Conway–Sloane, §7.7, pp. 382–383): for $\det f = 2^\alpha a$, $a$
odd, $\sum_q k\,n_q = \alpha$ and the product of the signs is $\left(\frac{a}{2}\right)$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29), pp. 382–383"]
def TwoSymbol.DetCond (σ : TwoSymbol) (N : ℕ) (d : ℤ) : Prop :=
  ∑ k ∈ range N, k * (σ k).dim = padicValInt 2 d ∧
    signProd (fun k => (σ k).sign) N = jacobiTwo (d / 2 ^ padicValInt 2 d)

/-! ### A putative genus -/

/-- **A putative system of local symbols** (Conway–Sloane, §7.7, p. 382: "which conceivable systems of invariants
actually correspond to quadratic forms"): dimension $n$, determinant $d \ne 0$, the $(-1)$-adic symbol $+^r-^s$, and a
$p$-adic symbol for every prime $p$, all supported below a common bound $N$. -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, p. 382"]
structure GenusSymbolData where
  /-- The dimension $n$. -/
  n : ℕ
  /-- The determinant $d$. -/
  det : ℤ
  /-- The $(-1)$-adic symbol $+^r-^s$. -/
  real : RealSymbol
  /-- The $p$-adic symbols for the odd primes $p$. -/
  odd : ℕ → OddSymbol
  /-- The 2-adic symbol. -/
  two : TwoSymbol
  /-- A common bound: every symbol is supported below $N$. -/
  N : ℕ

namespace GenusSymbolData

variable (G : GenusSymbolData)

/-- The signature $r - s$ of the $(-1)$-adic symbol. -/
def signature : ℤ := (G.real.pos : ℤ) - G.real.neg

/-- **The conditions (29)–(35) of §7.7** (Conway–Sloane, pp. 382–383) on a putative system of symbols:
* the dimensions: $r + s = n$, and every $p$-adic symbol has total dimension $n$;
* (29) the determinant conditions at every prime, and the sign of $d$ is $(-1)^s$;
* (30) the oddity formula $\text{signature} + \sum_{p \ge 3} p\text{-excess} \equiv \text{oddity} \pmod 8$ (the
  $p$-excess vanishes for $p \nmid 2d$, so the sum is over the odd primes dividing $d$);
* (31)–(35) every Jordan constituent exists;
* at an odd prime not dividing $d$ the symbol is $1^{\pm n}$ (only the scale $1$), as forced by (29). -/
@[kb "conwaysloane1999" "Ch. 15, §7.7, (29)–(35), pp. 382–383"]
structure Conditions : Prop where
  ne_zero : G.det ≠ 0
  real_dim : G.real.pos + G.real.neg = G.n
  real_sign : (G.det < 0 ↔ Odd G.real.neg)
  odd_supp : ∀ p, (G.odd p).SupportedBelow G.N
  two_supp : G.two.SupportedBelow G.N
  odd_dim : ∀ p, p.Prime → p ≠ 2 → ∑ k ∈ range G.N, (G.odd p k).dim = G.n
  two_dim : ∑ k ∈ range G.N, (G.two k).dim = G.n
  odd_det : ∀ p, p.Prime → p ≠ 2 → (G.odd p).DetCond p G.N G.det
  two_det : G.two.DetCond G.N G.det
  odd_exists : ∀ p, p.Prime → p ≠ 2 → ∀ k, (G.odd p k).Exists
  two_exists : ∀ k, (G.two k).Exists
  oddity_formula : (G.signature : ZMod 8) +
      ∑ p ∈ (G.det.natAbs.primeFactors.filter (· ≠ 2)), (G.odd p).pExcess p G.N = G.two.oddity G.N

end GenusSymbolData

end QuadFormsKB.ConwaySloane
