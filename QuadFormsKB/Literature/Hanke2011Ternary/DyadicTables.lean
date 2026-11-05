/-
# Hanke 2011 (ternary masses), §5: Table 5.3, the partial Euler factors at $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §5, Table 5.3, pp. 21–22.

Table 5.3 lists, for each of the 20 partial local genus symbols of Lemma 4.2, the contributions
$4\cdot A^*_{2^\nu}$ and $4\cdot B^*_{2^\nu}$ to the local quantities $A^*_{\mathfrak p}(S_{\mathfrak p})$,
$B^*_{\mathfrak p}(S_{\mathfrak p})$ of paper 6 (Def. 4.6), where $\nu = \operatorname{ord}_2(\det_G Q)$ is the valuation
of the Gram determinant ($\nu \ge -2$). These values are the output of Theorem 4.12 (computed from Tables 5.1 and
5.2, i.e. from Conway–Sloane's 2-adic mass formula); the 2-adic genus theory behind them is **not** formalized here,
so the table is recorded as data, row by row.

**Indexing.** The local Dirichlet series of §6 are in $N(I(S_{\mathfrak p}))^{-s} = 2^{-hs}$ where
$h = \operatorname{ord}_2(\det_H Q) = \nu + 3$ is the valuation of the **Hessian** determinant
($\det_H = 2^3\det_G$ for $n = 3$). Lean indexes the table by $h \in \mathbb{N}$ (so $h \ge 1$), and each row records
the paper's $\nu$ as $h - 3$.

* `dyadicA4 h`: the sum over the 20 rows of the $4\cdot A^*_{2^\nu}$ column at $\nu = h - 3$.
* `dyadicBmag h`: the sum over the 20 rows of the absolute value of the $4\cdot B^*_{2^\nu}$ column; the paper's
  entry is $-\varepsilon_u\cdot$`dyadicBmag` with $\varepsilon_u = (-1,u)_2$, i.e. negative when $u \equiv 1 \pmod 4$
  and positive when $u \equiv 3 \pmod 4$ (`dyadicB4`).
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Series

namespace QuadFormsKB.Hanke2011Ternary

open Finset

/-- A table row with a single entry: value `v` at Hessian valuation `h₀`. -/
def single (h₀ : ℕ) (v : ℚ) (h : ℕ) : ℚ := if h = h₀ then v else 0

/-- A table row family indexed by a parameter $b \ge b_0$: value `val b` at Hessian valuation `hOf b`
(the sum runs over the at most one $b \le h$ with `hOf b = h`; all `hOf` used below satisfy `hOf b ≥ b`). -/
def family (b₀ : ℕ) (hOf : ℕ → ℕ) (val : ℕ → ℚ) (h : ℕ) : ℚ :=
  ∑ b ∈ range (h + 1), if b₀ ≤ b ∧ hOf b = h then val b else 0

/-- Row 20 of Table 5.3, $(1 :: 1 :: 1)$, with two parameters $b \ge 3$, $c \ge b + 3$ and $\nu = b + c$: value
`val b c` at Hessian valuation $b + c + 3$. -/
def family20 (val : ℕ → ℕ → ℚ) (h : ℕ) : ℚ :=
  ∑ b ∈ range (h + 1), ∑ c ∈ range (h + 1), if 3 ≤ b ∧ b + 3 ≤ c ∧ b + c + 3 = h then val b c else 0

/-- **Table 5.3, column $4\cdot A^*_{2^\nu}$** (Hanke 2011, pp. 21–22), indexed by the Hessian valuation
$h = \nu + 3$. Rows (partial local genus symbol: allowed $\nu$, entry):
1 $(3)$: $\nu = 0$, $2^{-1}$; 2 $(2,1)$: $\nu = 1$, $2^{-4}\cdot3$; 3 $(2;1)$: $\nu = 2$, $2^{-5}\cdot 3$;
4 $(2::1)$: $\nu = b \ge 3$, $2^{-b-3}\cdot3$; 5 $(\bar2,1)$: $\nu = -2$, $4$;
6 $(\bar2::1)$: $\nu = b-2 \ge -1$, $2^{2-b}$; 7 $(1,2)$: $\nu = 2$, $2^{-6}\cdot3$; 8 $(1;2)$: $\nu = 4$, $2^{-9}\cdot3$;
9 $(1::2)$: $\nu = 2b \ge 6$, $2^{-3b-3}\cdot 3$; 10 $(1,\bar2)$: $\nu = 2$, $2^{-6}$;
11 $(1::\bar2)$: $\nu = 2b \ge 4$, $2^{-3b-3}$; 12 $(1,1,1)$: $\nu = 3$, $2^{-7}\cdot3$;
13 $(1,1;1)$: $\nu = 4$, $2^{-8}\cdot3$; 14 $(1;1,1)$: $\nu = 5$, $2^{-10}\cdot3$; 15 $(1;1;1)$: $\nu = 6$, $2^{-11}\cdot3$;
16 $(1,1::1)$: $\nu = c+1 \ge 5$, $2^{-c-5}\cdot3$; 17 $(1::1,1)$: $\nu = 2b+1 \ge 7$, $2^{-3b-4}\cdot3$;
18 $(1::1;1)$: $\nu = 2b+2 \ge 8$, $2^{-3b-5}\cdot 3$; 19 $(1;1::1)$: $\nu = c+2 \ge 7$, $2^{-c-7}\cdot3$;
20 $(1::1::1)$: $\nu = b+c \ge 9$, $b \ge 3$, $c \ge b+3$, $2^{-2b-c-3}\cdot 3$. -/
@[kb "hanke2011ternary" "§5, Table 5.3, column 4·A*, pp. 21–22"]
noncomputable def dyadicA4 (h : ℕ) : ℚ :=
  single 3 (1 / 2) h + single 4 (3 * (1 / 2) ^ 4) h + single 5 (3 * (1 / 2) ^ 5) h +
  family 3 (fun b => b + 3) (fun b => 3 * (1 / 2) ^ (b + 3)) h + single 1 4 h +
  family 1 (fun b => b + 1) (fun b => 4 * (1 / 2) ^ b) h + single 5 (3 * (1 / 2) ^ 6) h +
  single 7 (3 * (1 / 2) ^ 9) h + family 3 (fun b => 2 * b + 3) (fun b => 3 * (1 / 2) ^ (3 * b + 3)) h +
  single 5 ((1 / 2) ^ 6) h + family 2 (fun b => 2 * b + 3) (fun b => (1 / 2) ^ (3 * b + 3)) h +
  single 6 (3 * (1 / 2) ^ 7) h + single 7 (3 * (1 / 2) ^ 8) h + single 8 (3 * (1 / 2) ^ 10) h +
  single 9 (3 * (1 / 2) ^ 11) h + family 4 (fun c => c + 4) (fun c => 3 * (1 / 2) ^ (c + 5)) h +
  family 3 (fun b => 2 * b + 4) (fun b => 3 * (1 / 2) ^ (3 * b + 4)) h +
  family 3 (fun b => 2 * b + 5) (fun b => 3 * (1 / 2) ^ (3 * b + 5)) h +
  family 5 (fun c => c + 5) (fun c => 3 * (1 / 2) ^ (c + 7)) h +
  family20 (fun b c => 3 * (1 / 2) ^ (2 * b + c + 3)) h

/-- **Table 5.3, column $4\cdot B^*_{2^\nu}$, absolute values** (Hanke 2011, pp. 21–22), indexed by $h = \nu + 3$;
the entry is $-\varepsilon_u$ times this, $\varepsilon_u = (-1, u)_2$. Rows with nonzero entries:
1: $2^{-2}$; 3: $2^{-6}\cdot3$; 4: $2^{-b-4}\cdot 3$ if $b$ is even (else $0$); 5: $4$;
6: $2^{2-b}$ if $b$ is even, $2^{1-b}$ if $b$ is odd; 8: $2^{-10}\cdot3$; 9: $2^{-3b-4}\cdot3$ if $b$ is even
(else $0$); 10: $2^{-6}$; 11: $2^{-3b-3}$ if $b$ is odd, $2^{-3b-4}$ if $b$ is even; 15: $2^{-12}\cdot3$;
18: $2^{-3b-6}\cdot 3$ if $b$ is even (else $0$); 19: $2^{-c-8}\cdot3$ if $c$ is even (else $0$);
20: $2^{-2b-c-4}\cdot 3$ if $b$ and $c$ are even (else $0$). Rows 2, 7, 12, 13, 14, 16, 17 have entry $0$. -/
@[kb "hanke2011ternary" "§5, Table 5.3, column 4·B*, pp. 21–22"]
noncomputable def dyadicBmag (h : ℕ) : ℚ :=
  single 3 ((1 / 2) ^ 2) h + single 5 (3 * (1 / 2) ^ 6) h +
  family 3 (fun b => b + 3) (fun b => if Even b then 3 * (1 / 2) ^ (b + 4) else 0) h + single 1 4 h +
  family 1 (fun b => b + 1) (fun b => if Even b then 4 * (1 / 2) ^ b else 2 * (1 / 2) ^ b) h +
  single 7 (3 * (1 / 2) ^ 10) h +
  family 3 (fun b => 2 * b + 3) (fun b => if Even b then 3 * (1 / 2) ^ (3 * b + 4) else 0) h +
  single 5 ((1 / 2) ^ 6) h +
  family 2 (fun b => 2 * b + 3) (fun b => if Even b then (1 / 2) ^ (3 * b + 4) else (1 / 2) ^ (3 * b + 3)) h +
  single 9 (3 * (1 / 2) ^ 12) h +
  family 3 (fun b => 2 * b + 5) (fun b => if Even b then 3 * (1 / 2) ^ (3 * b + 6) else 0) h +
  family 5 (fun c => c + 5) (fun c => if Even c then 3 * (1 / 2) ^ (c + 8) else 0) h +
  family20 (fun b c => if Even b ∧ Even c then 3 * (1 / 2) ^ (2 * b + c + 4) else 0) h

/-- **$A^*_{\mathfrak p}(S_{\mathfrak p})$ at $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$** (Table 5.3):
$\frac14$ of the $4\cdot A^*$ column at Hessian valuation $h$; it does not depend on the unit square class $u$. -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 21–22"]
noncomputable def dyadicA (h : ℕ) : ℚ := dyadicA4 h / 4

/-- **$B^*_{\mathfrak p}(S_{\mathfrak p})$ at $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$** (Table 5.3), for
$S_{\mathfrak p} = 2^h u$ with $\varepsilon_u = (-1, u)_2$ (`εu`): $-\varepsilon_u/4$ times `dyadicBmag h`. -/
@[kb "hanke2011ternary" "§5, Table 5.3, pp. 21–22"]
noncomputable def dyadicB (εu : ℤˣ) (h : ℕ) : ℚ := -((εu : ℤ) : ℚ) * dyadicBmag h / 4

end QuadFormsKB.Hanke2011Ternary
