/-
# Hanke 2011 (ternary masses), §1 and §8: total masses of positive definite ternary forms over $\mathbb{Z}$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §1, pp. 1–2, and §8, pp. 26–28.

**Definitions** ($F = \mathbb{Q}$, positive definite, integer-valued, $n = 3$; Hessian determinant
$\det_H(Q) = \det(\partial^2 Q/\partial x_i\partial x_j)$):
* `ternaryClasses N`, `primitiveTernaryClasses N`: the $\mathrm{GL}_3(\mathbb{Z})$-classes $\mathrm{Cls}(N; 3)$,
  $\mathrm{Cls}^*(N; 3)$ of (primitive) positive definite integer-valued ternary forms with $\det_H = N$;
* `TMass3 N` $= \mathrm{TMass}_3(N) = \sum_{[Q]\in\mathrm{Cls}(N;3)} 1/|\mathrm{Aut}(Q)|$ and `TMass3star N`
  $= \mathrm{TMass}^*_3(N)$ (§1, p. 1); `DMass3`, `DMass3star`: the total mass Dirichlet series
  $D_{\mathrm{Mass};3}(s) = \sum_N \mathrm{TMass}_3(N)N^{-s}$ and $D_{\mathrm{Mass}^*;3}(s)$ (§1, p. 2; §8, p. 26).

**Statements.**
* `Cor82` (**Corollary 8.2**, with **Theorem 1.1**, *stated*):
  $D_{\mathrm{Mass}^*;3}(s) = \frac{1}{48\cdot2^s}\cdot\frac{\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)}{\zeta(3s)}$ and
  $D_{\mathrm{Mass};3}(s) = \frac{1}{48\cdot2^s}[\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)]$.
* `theorem_1_1_divisor_sum`: the second identity gives
  $\mathrm{TMass}_3(2m) = \frac1{48}\sum_{m = ab^2,\ a,b>0}(ab - b^2)$ (**proved** from the Dirichlet series identity).
* `PrimitiveMassLocalFormula` (**named input**: paper 6, Cor. 6.4 and Cor. 4.15, with the local identifications of
  this paper's §§2–5) and `cor_8_2_primitive`: under this input, the first identity of Corollary 8.2 **holds**
  (it follows from `cor_7_2_A`, `cor_7_2_B`).
-/
import QuadFormsKB.Literature.Hanke2011Ternary.Global
import QuadFormsKB.Siegel.Genus

namespace QuadFormsKB.Hanke2011Ternary

open Finset ArithmeticFunction QuadFormsKB.Siegel Real

/-- **A primitive integral form**: the coefficients $c_{ij}$ of $Q = \sum_{i\le j}c_{ij}x_ix_j$ have no common
divisor other than units ($\gcd(c_{ij}) = 1$). -/
def IsPrimitiveForm {n : ℕ} (Q : QuadForm ℤ n) : Prop := ∀ d : ℤ, (∀ i j, d ∣ Q.coeff i j) → IsUnit d

/-- **$\mathrm{Cls}(N; 3)$** (§1, p. 1): the $\mathrm{GL}_3(\mathbb{Z})$-classes of positive definite integer-valued
ternary forms $Q$ with Hessian determinant $\det_H(Q) = N$. -/
@[kb "hanke2011ternary" "§1, p. 1 (Cls(S; n))"]
def ternaryClasses (N : ℕ) : Set (QClass 3) :=
  {c | ∃ Q : QuadForm ℤ 3, classOf Q = c ∧ IntQF.PosDef Q ∧ Q.hessian.det = N}

/-- **$\mathrm{Cls}^*(N; 3)$** (§1, p. 1): the classes of primitive positive definite integer-valued ternary forms
with $\det_H(Q) = N$. -/
@[kb "hanke2011ternary" "§1, p. 1 (Cls*(S; n))"]
def primitiveTernaryClasses (N : ℕ) : Set (QClass 3) :=
  {c | ∃ Q : QuadForm ℤ 3, classOf Q = c ∧ IntQF.PosDef Q ∧ IsPrimitiveForm Q ∧ Q.hessian.det = N}

/-- **The total mass** $\mathrm{TMass}_3(N) = \sum_{[Q]\in\mathrm{Cls}(N;3)} \frac{1}{|\mathrm{Aut}(Q)|}$ (§1, p. 1),
$\mathrm{Aut}(Q) \le \mathrm{GL}_3(\mathbb{Z})$. (A `finsum`; the set of classes is finite by Hermite reduction.) -/
@[kb "hanke2011ternary" "§1, p. 1 (TMass_n(S))"]
noncomputable def TMass3 (N : ℕ) : ℚ := ∑ᶠ c ∈ ternaryClasses N, ((c.autCard : ℚ))⁻¹

/-- **The primitive total mass** $\mathrm{TMass}^*_3(N) = \sum_{[Q]\in\mathrm{Cls}^*(N;3)} \frac{1}{|\mathrm{Aut}(Q)|}$
(§1, p. 1). -/
@[kb "hanke2011ternary" "§1, p. 1 (TMass*_n(S))"]
noncomputable def TMass3star (N : ℕ) : ℚ := ∑ᶠ c ∈ primitiveTernaryClasses N, ((c.autCard : ℚ))⁻¹

/-- **The total mass Dirichlet series** $D_{\mathrm{Mass};3}(s) = \sum_{N\ge1}\mathrm{TMass}_3(N)N^{-s}$
(§1, p. 2; §8, p. 27, with $F = \mathbb{Q}$, $\lambda(a\mathbb{Z}) = |a|$). -/
@[kb "hanke2011ternary" "§1, p. 2; §8, p. 27"]
noncomputable def DMass3 : ArithmeticFunction ℚ := ⟨fun N => if N = 0 then 0 else TMass3 N, by simp⟩

/-- **The primitive total mass Dirichlet series** $D_{\mathrm{Mass}^*;3}(s) = \sum_{N\ge1}\mathrm{TMass}^*_3(N)N^{-s}$
(§8, p. 26, with $F = \mathbb{Q}$). -/
@[kb "hanke2011ternary" "§8, p. 26"]
noncomputable def DMass3star : ArithmeticFunction ℚ := ⟨fun N => if N = 0 then 0 else TMass3star N, by simp⟩

/-- **$\zeta(ks + j)$ for an integer shift $j$** (e.g. $\zeta(s-1)$, $\zeta(2s-2)$): $\sum_{m\ge1}m^{-j}(m^k)^{-s}$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1 and §8 (zeta functions as formal Dirichlet series)"]
noncomputable def zetaShiftZ (k : ℕ) (j : ℤ) : ArithmeticFunction ℚ := powPush k fun m => (m : ℚ) ^ (-j)

/-- **Corollary 8.2** (Hanke 2011, p. 27; also **Theorem 1.1**, p. 2), *stated*: for positive definite
$\mathbb{Z}$-valued ternary forms (whose Hessian determinants lie in $2\mathbb{N}$),
$$D_{\mathrm{Mass}^*;3}(s) = \frac{1}{48\cdot 2^s}\cdot\Big[\frac{\zeta(s-1)\zeta(2s-1)}{\zeta(3s)}
  - \frac{\zeta(2s-2)\zeta(s)}{\zeta(3s)}\Big],\qquad
D_{\mathrm{Mass};3}(s) = \frac{1}{48\cdot 2^s}\big[\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)\big].$$
Fields: `primitive` (the first identity), `total` (the second), as identities of formal Dirichlet series.
This paper derives it from Theorem 8.1 (via paper 6); see `cor_8_2_primitive` for the first identity under the named
input `PrimitiveMassLocalFormula`. -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, p. 27; Thm. 1.1, p. 2"]
structure Cor82 : Prop where
  /-- $D_{\mathrm{Mass}^*;3}(s) = \frac{1}{48\cdot2^s}[\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)]/\zeta(3s)$. -/
  primitive : DMass3star = (1 / 48 : ℚ) • (twoPowNegS *
    ((zetaShiftZ 1 (-1) * zetaShiftZ 2 (-1) - zetaShiftZ 2 (-2) * zetaShiftZ 1 0) * zetaShiftInv 3 0))
  /-- $D_{\mathrm{Mass};3}(s) = \frac{1}{48\cdot2^s}[\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)]$. -/
  total : DMass3 = (1 / 48 : ℚ) • (twoPowNegS *
    (zetaShiftZ 1 (-1) * zetaShiftZ 2 (-1) - zetaShiftZ 2 (-2) * zetaShiftZ 1 0))

/-- **Named input: paper 6's mass structure for ternary forms over $\mathbb{Q}$, with the local computations of
this paper.** For every $N \ge 1$,
$$\mathrm{TMass}^*_3(N) = \frac{N^2}{64\pi^2}\cdot\frac12\,\beta^{-1}_{3,f}\cdot\big(A^*_3(N) + B^*_3(N)\big),
\qquad \beta^{-1}_{3,f} = 4\zeta(2) = 4\cdot\frac{\pi^2}{6},$$
where $A^*_3(N)$, $B^*_3(N)$ are `globalA N`, `globalB N`. Field: `mass_eq`.

This combines (all cited, not proved here):
* Hanke, *The structure of masses of rank $n$ quadratic lattices of varying determinant over number fields*
  (`hanke2011structure`), Cor. 6.4, p. 26: $D_{\mathrm{Mass}^*}(s) = |\Delta_F|^{3/2}(64\pi^2)^{-[F:\mathbb{Q}]}
  D_{M^*}(s-2)$ (here $F = \mathbb{Q}$, so the coefficient of $N^{-s}$ is $N^2 M^*(N)/(64\pi^2)$);
* ibid., Cor. 4.15, p. 20: $D_{M^*} = \frac12\beta^{-1}_{3,f}[D_{A^*} + \varepsilon_\infty D_{B^*}]$, with
  $\varepsilon_\infty = c_\infty(\sigma) = 1$ for positive definite forms;
* this paper, Theorem 7.1 (generic density product $4\zeta(2)$), and the identification of the local quantities
  $A^*_p$, $B^*_p$ with the tuples of Lemma 2.1 and the mass formula of Lemma 2.3 ($p$ odd) and with Table 5.3
  (Theorem 4.12, $p = 2$).

It is not the conclusion: Corollary 8.2 (`cor_8_2_primitive`) further needs Corollary 7.2 (`cor_7_2_A`,
`cor_7_2_B`), which is proved. -/
@[kb "hanke2011structure" "Cor. 6.4, p. 26, and Cor. 4.15, p. 20; hanke2011ternary §7, Thm. 7.1, and §§2–5"]
structure PrimitiveMassLocalFormula : Prop where
  /-- $\mathrm{TMass}^*_3(N) = \frac{N^2}{64\pi^2}\cdot\frac12\cdot4\zeta(2)\cdot(A^*_3(N) + B^*_3(N))$. -/
  mass_eq : ∀ N : ℕ, N ≠ 0 → ((TMass3star N : ℚ) : ℝ) =
    (N : ℝ) ^ 2 / (64 * π ^ 2) * ((1 / 2) * (4 * (π ^ 2 / 6))) * ((globalA N + globalB N : ℚ) : ℝ)

/-! ### The shift $s \mapsto s - 2$ -/

/-- Multiplying the coefficients by $n^2$, i.e. $D(s) \mapsto D(s-2)$. -/
noncomputable def sqTwist (f : ArithmeticFunction ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n => (n : ℚ) ^ 2 * f n, by simp⟩

theorem sqTwist_apply (f : ArithmeticFunction ℚ) (n : ℕ) : sqTwist f n = (n : ℚ) ^ 2 * f n := rfl

theorem sqTwist_mul (f g : ArithmeticFunction ℚ) : sqTwist (f * g) = sqTwist f * sqTwist g := by
  ext n
  rw [sqTwist_apply, mul_apply, mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [sqTwist_apply, sqTwist_apply, ← hx.1]
  push_cast; ring

theorem sqTwist_add (f g : ArithmeticFunction ℚ) : sqTwist (f + g) = sqTwist f + sqTwist g := by
  ext n; simp [sqTwist_apply, mul_add]

theorem sqTwist_neg (f : ArithmeticFunction ℚ) : sqTwist (-f) = -sqTwist f := by
  ext n; simp [sqTwist_apply]

theorem powPush_congr {k : ℕ} {h h' : ℕ → ℚ} (hh : ∀ m, m ≠ 0 → h m = h' m) : powPush k h = powPush k h' := by
  ext n
  rw [powPush_apply, powPush_apply]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hh m (Nat.pos_of_mem_divisors hm).ne']

theorem sqTwist_powPush (k : ℕ) (h : ℕ → ℚ) :
    sqTwist (powPush k h) = powPush k (fun m => (m : ℚ) ^ (2 * k) * h m) := by
  ext n
  rw [sqTwist_apply, powPush_apply, powPush_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs with hm
  · rw [← hm]; push_cast; ring
  · simp

theorem sqTwist_zetaShift (k j : ℕ) : sqTwist (zetaShift k j) = zetaShiftZ k ((j : ℤ) - 2 * k) := by
  rw [zetaShift, sqTwist_powPush, zetaShiftZ]
  refine powPush_congr fun m hm => ?_
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hm']
  congr 1; push_cast; ring

theorem sqTwist_zetaShiftInv : sqTwist (zetaShiftInv 3 6) = zetaShiftInv 3 0 := by
  rw [zetaShiftInv, sqTwist_powPush, zetaShiftInv]
  refine powPush_congr fun m hm => ?_
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  field_simp
  ring

theorem sqTwist_twoPowNegS : sqTwist twoPowNegS = (4 : ℚ) • twoPowNegS := by
  ext n
  show (n : ℚ) ^ 2 * (if n = 2 then 1 else 0) = 4 * (if n = 2 then 1 else 0)
  split_ifs with h
  · subst h; norm_num
  · simp

/-- **Corollary 8.2, primitive part** (Hanke 2011, p. 27), under the named input `PrimitiveMassLocalFormula`:
$$D_{\mathrm{Mass}^*;3}(s) = \frac{1}{48\cdot 2^s}\cdot
\frac{\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)}{\zeta(3s)}.$$
The proof is the paper's: Theorem 8.1 for $F = \mathbb{Q}$ from Corollary 7.2 (`cor_7_2_A`, `cor_7_2_B`). -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, p. 27 (primitive part); Thm. 8.1, p. 27 (F = Q)"]
theorem cor_8_2_primitive (H : PrimitiveMassLocalFormula) :
    DMass3star = (1 / 48 : ℚ) • (twoPowNegS *
      ((zetaShiftZ 1 (-1) * zetaShiftZ 2 (-1) - zetaShiftZ 2 (-2) * zetaShiftZ 1 0) * zetaShiftInv 3 0)) := by
  have hrat : DMass3star = (1 / 192 : ℚ) • sqTwist (globalA + globalB) := by
    ext N
    by_cases hN : N = 0
    · subst hN; simp [DMass3star]
    have h := H.mass_eq N hN
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have h' : ((TMass3star N : ℚ) : ℝ) = (((N : ℚ) ^ 2 * (globalA N + globalB N) / 192 : ℚ) : ℝ) := by
      rw [h]; push_cast; field_simp; ring
    have h'' := Rat.cast_injective h'
    show (if N = 0 then 0 else TMass3star N) = _
    rw [if_neg hN, h'']
    show _ = (1 / 192 : ℚ) * ((N : ℚ) ^ 2 * (globalA N + globalB N))
    ring
  rw [hrat, cor_7_2_A, cor_7_2_B, ← sub_eq_add_neg, show ∀ f g : ArithmeticFunction ℚ, f - g = f + -g from
    fun f g => sub_eq_add_neg f g, sqTwist_add, sqTwist_neg, sqTwist_mul, sqTwist_mul, sqTwist_mul, sqTwist_mul,
    sqTwist_mul, sqTwist_mul, sqTwist_twoPowNegS, sqTwist_zetaShift, sqTwist_zetaShift, sqTwist_zetaShift,
    sqTwist_zetaShift, sqTwist_zetaShiftInv]
  simp only [smul_mul_assoc, smul_smul, mul_sub, sub_mul]
  norm_num
  module

/-! ### Theorem 1.1: the divisor sum -/

theorem af_sub_apply (f g : ArithmeticFunction ℚ) (n : ℕ) : (f - g) n = f n - g n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, ← sub_eq_add_neg]

theorem powPush_one_mul_two_apply (f g : ℕ → ℚ) (m : ℕ) :
    (powPush 1 f * powPush 2 g) m =
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m), f ab.1 * g ab.2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [ArithmeticFunction.mul_apply]
  have h1 : ∀ x ∈ m.divisorsAntidiagonal, powPush 1 f x.1 * powPush 2 g x.2 =
      ∑ b ∈ x.2.divisors.filter (fun b => b ^ 2 = x.2), f x.1 * g b := by
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h0 : x.1 ≠ 0 := left_ne_zero_of_mul (hx'.1 ▸ hm.ne')
    have := powPush_apply_pow (k := 1) one_pos f h0
    rw [pow_one] at this
    rw [this, powPush_apply, Finset.mul_sum, Finset.sum_filter]
    simp [mul_ite]
  rw [Finset.sum_congr rfl h1, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => (p.1.1, p.2)) (fun q => ⟨(q.1, q.2 ^ 2), q.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨x1, x2⟩, b⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Nat.mem_divisors] at hp
    obtain ⟨⟨hx, -⟩, ⟨-, -⟩, hb2⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors]
    subst hb2
    exact ⟨⟨⟨Dvd.intro _ hx, hm.ne'⟩, ⟨(dvd_pow_self b two_ne_zero).trans (Dvd.intro_left _ hx), hm.ne'⟩⟩, hx⟩
  · rintro ⟨a, b⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Nat.mem_divisors] at hq
    obtain ⟨⟨⟨ha, -⟩, ⟨hb, -⟩⟩, hab⟩ := hq
    have hb0 : b ≠ 0 := by rintro rfl; simp at hab; omega
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hab, hm.ne'⟩, ⟨dvd_pow_self b two_ne_zero, pow_ne_zero _ hb0⟩, trivial⟩
  · rintro ⟨⟨x1, x2⟩, b⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_filter, Nat.mem_divisors] at hp
    obtain ⟨-, -, hb2⟩ := hp
    subst hb2
    rfl
  · intro q _; rfl
  · intro p _; rfl

/-- The coefficient of $\zeta(s-1)\zeta(2s-1)$ at $m$ is $\sum_{ab^2 = m} ab$. -/
theorem zeta_s1_2s1_apply (m : ℕ) :
    (zetaShiftZ 1 (-1) * zetaShiftZ 2 (-1)) m =
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m), (ab.1 : ℚ) * ab.2 := by
  unfold zetaShiftZ
  rw [powPush_one_mul_two_apply]
  simp

/-- The coefficient of $\zeta(2s-2)\zeta(s)$ at $m$ is $\sum_{ab^2 = m} b^2$. -/
theorem zeta_2s2_s_apply (m : ℕ) :
    (zetaShiftZ 2 (-2) * zetaShiftZ 1 0) m =
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m), ((ab.2 : ℚ)) ^ 2 := by
  unfold zetaShiftZ
  rw [mul_comm, powPush_one_mul_two_apply]
  simp

/-- **Theorem 1.1, divisor sum form** (Hanke 2011, p. 2): if
$D_{\mathrm{Mass};3}(s) = \frac{1}{48\cdot2^s}[\zeta(s-1)\zeta(2s-1) - \zeta(2s-2)\zeta(s)]$ (Corollary 8.2), then
for every $m \ge 1$
$$\mathrm{TMass}_3(2m) = \frac{1}{48}\sum_{\substack{m = a\cdot b^2\\ a, b > 0}} (ab - b^2)$$
(the paper writes $S/2 = a\cdot b^2$ with $S = 2m$), and $\mathrm{TMass}_3(N) = 0$ for odd $N$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2"]
theorem theorem_1_1_divisor_sum (H : Cor82) (m : ℕ) (hm : m ≠ 0) :
    TMass3 (2 * m) = (1 / 48) * ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
      ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2) := by
  have h := congrArg (fun f : ArithmeticFunction ℚ => f (2 * m)) H.total
  have h2m : 2 * m ≠ 0 := by omega
  change DMass3 (2 * m) = (1 / 48 : ℚ) * _ at h
  rw [show DMass3 (2 * m) = TMass3 (2 * m) from if_neg h2m,
    twoPowNegS_mul_apply _ h2m, if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left _ two_pos,
    af_sub_apply, zeta_s1_2s1_apply, zeta_2s2_s_apply, ← Finset.sum_sub_distrib] at h
  exact h

/-- **Theorem 1.1, odd determinants**: under Corollary 8.2, $\mathrm{TMass}_3(N) = 0$ for odd $N$. -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2"]
theorem theorem_1_1_odd (H : Cor82) (N : ℕ) (hN : ¬ 2 ∣ N) : TMass3 N = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℚ => f N) H.total
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero 2)
  change DMass3 N = (1 / 48 : ℚ) * _ at h
  rw [show DMass3 N = TMass3 N from if_neg hN0, twoPowNegS_mul_apply _ hN0, if_neg hN, mul_zero] at h
  exact h

end QuadFormsKB.Hanke2011Ternary
