/-
# Conway–Sloane 1988, §8: the functional equation, the Bernoulli formula and the closed formula for $\zeta_D(s)$ ((11)–(13))

J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices IV: the mass formula*, Proc. R. Soc. Lond. A **419** (1988),
259–286 (`conwaysloane1988`), §8, p. 268. Conway–Sloane follow Apostol, *Introduction to analytic number theory* (1976),
Theorems 12.11 and 12.13.

**Notation (book $\to$ Lean).**
* A Dirichlet character $\psi$ modulo $k_1$ is a `DirichletCharacter ℂ k₁`; its $L$-function $L(s, \psi)$ is Mathlib's
  `DirichletCharacter.LFunction`, the analytic continuation of $\sum_{m \ge 1}\psi(m)m^{-s}$ to all $s \in \mathbb C$
  (for $\psi$ trivial, with a pole at $s = 1$). For a function $\Phi$ on $\mathbb Z/N$ the same continuation is
  `ZMod.LFunction Φ`.
* The Gauss sum $G(\psi) = \sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}$ is `gaussSum ψ stdAddChar`, with Mathlib's standard
  additive character $r \mapsto e^{2\pi i r/k_1}$ of $\mathbb Z/k_1$ (the term $r = k_1$ of the book is the term $r = 0$).
* $B_s(x)$ is the Bernoulli polynomial `Polynomial.bernoulli s` (rational coefficients), evaluated at the rational number
  $r/k_1$ and then cast to $\mathbb C$.
* $i^{\pm s}$ is the complex power `I ^ (± s)` (principal branch, $i^s = e^{\pi i s/2}$); $\bar\psi = \psi^{-1}$.
* The book's "$\psi$ primitive modulo $k_1$" is Mathlib's `DirichletCharacter.IsPrimitive` (conductor $= k_1$).

**Proves**
* `LFunction_one_sub_bernoulli` ((12)): for any $\Phi : \mathbb Z/N \to \mathbb C$ and natural $s \ge 2$,
  $L(1 - s, \Phi) = -\frac{N^{s-1}}{s}\sum_{r=1}^{N}\Phi(r)B_s(r/N)$.
* `LFunction_one_sub_primitive` ((11)): for $\psi$ primitive modulo $k_1$ and $s \notin \{0, -1, -2, \dots\}$ (and
  $s \ne 1$ if $k_1 = 1$),
  $L(1-s,\psi) = \frac{k_1^{s-1}\Gamma(s)}{(2\pi)^s}\bigl(i^{-s} + \psi(-1)i^s\bigr)G(\psi)L(s,\bar\psi)$.
* `LFunction_nat_primitive` ((11) and (12) combined): for $\psi$ primitive and real ($\bar\psi = \psi$), natural $s \ge 2$ with
  $\psi(-1) = (-1)^s$ and $G(\psi) \ne 0$,
  $L(s,\psi) = \frac{-(2\pi)^s}{s!\,(i^{-s}+\psi(-1)i^s)}\cdot\frac{\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)}{G(\psi)}$.
* `LD_eq_LFunction_mul` ((10) for all $s$): if $\chi_D = \chi_1\psi$ on $\mathbb Z/4\lvert D\rvert$ (i.e. the function `Phi D`
  is the character $\psi$ of level $k_1 \mid 4\lvert D\rvert$ viewed at level $4\lvert D\rvert$), then the analytic continuation of
  $\zeta_D$ is $L(s,\psi)\prod_{p \mid 4D}(1 - \psi(p)p^{-s})$ (for $s \ne 1$ or $\psi$ nontrivial).
* `zetaD_formula` ((13)): the resulting closed formula
  $$\zeta_D(s) = \prod_{p\mid 4D}\Bigl(1-\frac{\psi(p)}{p^s}\Bigr)\cdot\frac{-(2\pi)^s}{s!\,(i^{-s}+\psi(-1)i^s)}\cdot
  \frac{\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)}{\sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}}$$
  for natural $s \ge 2$ with $\psi(-1) = (-1)^s$.

**Differences with the printed statements.**
* (11) is printed with $L(s, \psi)$ on the right; the general statement (Apostol, Theorem 12.11) has $L(s, \bar\psi)$, the
  same for the real characters of §8.
* (12) and (13) are proved here for $s \ge 2$. (12) for every $s \ge 1$ is `LFunction_one_sub_bernoulli'`
  (`Mass/HurwitzZero.lean`), from the value of the Hurwitz zeta function at $0$ (`hurwitzZeta_zero_of_mem_Ioc`), which
  Mathlib does not provide; the values $\zeta_D(1)$ used later are obtained from Dirichlet's class number formula.
* The product in (13) is printed over the primes $p \mid k$ (the modulus of $\chi_D$); here it is over the primes dividing
  $4\lvert D\rvert$, which differ only by primes $p$ with $\psi(p)$ determined by the same identity $\chi_D = \chi_1\psi$ (in every
  case of Table 4 the two sets of primes coincide).
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.Characters

namespace QuadFormsKB.ConwaySloane.Mass

open Complex ZMod Finset HurwitzZeta
open scoped Real

/-! ### (12): values at non-positive integers -/

/-- A sum over $\mathbb Z/N$ as a sum over $r = 1, \dots, N$ (the class $0$ is represented by $r = N$). -/
theorem sum_zmod_eq_sum_Icc {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (G : ℕ → ℂ) (h0 : F 0 = G N)
    (h : ∀ r : ℕ, 0 < r → r < N → F r = G r) :
    ∑ x : ZMod N, F x = ∑ r ∈ Icc 1 N, G r := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun x => if x = 0 then N else x.val) (fun r => (r : ZMod N)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simp only [mem_Icc]
    split_ifs with hx
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).1 h)), (ZMod.val_lt x).le⟩
  · intro r _; exact mem_univ _
  · intro x _
    split_ifs with hx
    · simp [hx]
    · simp
  · intro r hr
    simp only [mem_Icc] at hr
    rcases eq_or_lt_of_le hr.2 with rfl | hlt
    · simp
    · have hne : (r : ZMod N) ≠ 0 := by
        intro h0
        rw [ZMod.natCast_eq_zero_iff] at h0
        exact absurd (Nat.le_of_dvd hr.1 h0) (by omega)
      simp only [hne, ↓reduceIte, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  · intro x _
    split_ifs with hx
    · rw [hx, h0]
    · have hv : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).1 h))
      rw [← h x.val hv (ZMod.val_lt x), ZMod.natCast_zmod_val]

/-- **(12), p. 268** (Apostol, Theorem 12.13): for a function $\Phi$ on $\mathbb Z/N$ (in particular a Dirichlet character
$\psi$ modulo $k_1 = N$) and a natural number $s \ge 2$,
$$L(1-s,\Phi) = -\frac{N^{s-1}}{s}\sum_{r=1}^{N}\Phi(r)\,B_s\!\Bigl(\frac rN\Bigr),$$
$B_s$ the Bernoulli polynomial. (The case $s = 1$ is not covered: see the module docstring.) -/
@[kb "conwaysloane1988" "§8 (12), p. 268"]
theorem LFunction_one_sub_bernoulli {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) {s : ℕ} (hs : 2 ≤ s) :
    ZMod.LFunction Φ (1 - s) = -((N : ℂ) ^ (s - 1) / s) *
      ∑ r ∈ Icc 1 N, Φ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : k ≠ 0 := by omega
  have e1 : (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) := by push_cast; ring
  rw [e1, ZMod.LFunction, neg_neg, Nat.add_sub_cancel, Finset.mul_sum, Finset.mul_sum]
  have hB : ∀ j : ZMod N, hurwitzZeta (toAddCircle j) (-(k : ℂ)) =
      -1 / ((k : ℂ) + 1) * (((Polynomial.bernoulli (k + 1)).eval ((j.val : ℚ) / N) : ℚ) : ℂ) := by
    intro j
    have hx : ((j.val : ℝ) / N) ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.mpr ⟨by positivity,
      (div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr <| Nat.cast_le.mpr (ZMod.val_lt j).le⟩
    rw [toAddCircle_apply, hurwitzZeta_neg_nat hk hx]
    congr 1
    have e : ((((j.val : ℝ) / N : ℝ)) : ℂ) = algebraMap ℚ ℂ ((j.val : ℚ) / N) := by
      simp only [eq_ratCast, Rat.cast_div, Rat.cast_natCast, Complex.ofReal_div, Complex.ofReal_natCast]
    rw [e, Polynomial.eval_map, Polynomial.eval₂_hom]
    simp
  simp_rw [hB, Complex.cpow_natCast]
  apply sum_zmod_eq_sum_Icc
  · have h1 : (Polynomial.bernoulli (k + 1)).eval 1 = (Polynomial.bernoulli (k + 1)).eval 0 := by
      rw [Polynomial.bernoulli_eval_one, Polynomial.bernoulli_eval_zero,
        bernoulli_eq_bernoulli'_of_ne_one (by omega)]
    have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    simp only [ZMod.val_zero, Nat.cast_zero, zero_div, ZMod.natCast_self, div_self hN, h1]
    push_cast
    ring
  · intro r hr hrN
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hrN]
    push_cast
    ring

/-! ### (11): the functional equation -/

theorem LFunction_const_mul {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => by ring)

theorem I_cpow (s : ℂ) : I ^ s = cexp (π * I * s / 2) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I]
  ring_nf

theorem inv_apply_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  rcases χ.even_or_odd with h | h
  · rw [h, inv_one]
  · rw [h, inv_neg, inv_one]

/-- **(11), p. 268** (the functional equation; Apostol, Theorem 12.11): for a primitive Dirichlet character $\psi$ modulo
$k_1$ and $s \in \mathbb C$ not in $\{0, -1, -2, \dots\}$ (with $s \ne 1$ when $k_1 = 1$),
$$L(1-s,\psi) = \frac{k_1^{s-1}\,\Gamma(s)}{(2\pi)^s}\bigl(i^{-s} + \psi(-1)\,i^s\bigr)\,G(\psi)\,L(s,\bar\psi),\qquad
G(\psi) = \sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}.$$
(The book writes $L(s,\psi)$ for $L(s,\bar\psi)$; they agree for the real characters it uses.) Derived from Mathlib's
`ZMod.LFunction_one_sub` and the Fourier transform of a primitive character. -/
@[kb "conwaysloane1988" "§8 (11), p. 268"]
theorem LFunction_one_sub_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs1 : N ≠ 1 ∨ s ≠ 1) :
    χ.LFunction (1 - s) = (N : ℂ) ^ (s - 1) * Gamma s / (2 * π) ^ s * (I ^ (-s) + χ (-1) * I ^ s) *
      gaussSum χ stdAddChar * χ⁻¹.LFunction s := by
  have h0 : (χ : ZMod N → ℂ) 0 = 0 ∨ s ≠ 1 := by
    rcases hs1 with h | h
    · exact Or.inl (DirichletCharacter.map_zero' χ h)
    · exact Or.inr h
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (χ (-1) * gaussSum χ stdAddChar) * χ⁻¹ k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul, map_mul, inv_apply_neg_one]
    ring
  have hFn : 𝓕 (fun x => (χ : ZMod N → ℂ) (-x)) = fun k => gaussSum χ stdAddChar * χ⁻¹ k := by
    funext k
    rw [dft_comp_neg]
    simp only
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]
    ring
  unfold DirichletCharacter.LFunction
  rw [ZMod.LFunction_one_sub _ hs h0, hF, hFn, LFunction_const_mul, LFunction_const_mul,
    I_cpow, I_cpow, cpow_neg]
  ring_nf

/-- **(11) and (12) combined** (the $L$-value part of (13), p. 268): for a primitive real character $\psi$ modulo $k_1$
($\bar\psi = \psi$), a natural number $s \ge 2$ of the parity of $\psi$ ($\psi(-1) = (-1)^s$) and $G(\psi) \ne 0$,
$$L(s,\psi) = \frac{-(2\pi)^s}{s!\,(i^{-s}+\psi(-1)\,i^s)}\cdot\frac{\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)}{G(\psi)}.$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268"]
theorem LFunction_nat_primitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hreal : χ⁻¹ = χ) {s : ℕ} (hs : 2 ≤ s) (hpar : χ (-1) = (-1) ^ s) (hG : gaussSum χ stdAddChar ≠ 0) :
    χ.LFunction s = -(2 * π) ^ s / ((s.factorial : ℂ) * (I ^ (-(s : ℂ)) + χ (-1) * I ^ (s : ℂ))) *
      (∑ r ∈ Icc 1 N, χ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ)) /
        gaussSum χ stdAddChar := by
  have hs' : ∀ n : ℕ, (s : ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (s : ℝ) ≤ 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have h11 := LFunction_one_sub_primitive hχ hs' (Or.inr (by norm_cast; omega))
  have h12 := LFunction_one_sub_bernoulli (χ : ZMod N → ℂ) hs
  unfold DirichletCharacter.LFunction at h11 ⊢
  rw [hreal, h12] at h11
  have hc : I ^ (-(s : ℂ)) + χ (-1) * I ^ (s : ℂ) = 2 * (I ^ s)⁻¹ := by
    rw [cpow_neg, cpow_natCast, hpar]
    have : (I ^ s) ^ 2 = (-1) ^ s := by rw [← pow_mul, mul_comm, pow_mul, I_sq]
    have hI : I ^ s ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    rw [this, ← mul_pow]
    norm_num
  rw [hc] at h11 ⊢
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hG' : Gamma ((k + 1 : ℕ) : ℂ) = k.factorial := by
    rw [Nat.cast_add, Nat.cast_one, Complex.Gamma_nat_eq_factorial]
  rw [hG', Nat.add_sub_cancel] at h11
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hπ : (2 * (π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hI : I ^ (k + 1) ≠ 0 := pow_ne_zero _ I_ne_zero
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [Nat.factorial_succ, Nat.cast_mul]
  have e1 : ((N : ℂ) ^ (((k + 1 : ℕ) : ℂ) - 1)) = (N : ℂ) ^ k := by
    rw [show (((k + 1 : ℕ) : ℂ) - 1) = (k : ℂ) by push_cast; ring, cpow_natCast]
  have e2 : (2 * (π : ℂ)) ^ (((k + 1 : ℕ) : ℂ)) = (2 * (π : ℂ)) ^ (k + 1) := cpow_natCast _ _
  rw [e1, e2] at h11
  have hNk : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ hN
  have hπk : (2 * (π : ℂ)) ^ (k + 1) ≠ 0 := pow_ne_zero _ hπ
  field_simp at h11
  set L := ZMod.LFunction (χ : ZMod N → ℂ) ((k + 1 : ℕ) : ℂ)
  set S := ∑ x ∈ Icc 1 N, χ x * (((Polynomial.bernoulli (k + 1)).eval ((x : ℚ) / N) : ℚ) : ℂ)
  have hd : ((k + 1 : ℕ) : ℂ) * k.factorial * 2 * gaussSum χ stdAddChar ≠ 0 := by
    have : (k : ℂ) + 1 ≠ 0 := by norm_cast
    simp [hG, hf, this]
  have key : L = -(S * (2 * π) ^ (k + 1) * I ^ (k + 1)) /
      (((k + 1 : ℕ) : ℂ) * k.factorial * 2 * gaussSum χ stdAddChar) := by
    rw [h11]; field_simp
  rw [key]
  field_simp

/-! ### (10) for all $s$ and (13) for $\zeta_D$ -/

/-- The value of a character of level $N$ viewed at level $M$ ($N \mid M$) at a natural number $m$: $\chi(m)$ if $m$ is
coprime to $M$, and $0$ otherwise. -/
theorem changeLevel_natCast {N M : ℕ} (h : N ∣ M) (χ : DirichletCharacter ℂ N) (m : ℕ) :
    DirichletCharacter.changeLevel h χ (m : ZMod M) = if m.Coprime M then χ m else 0 := by
  split_ifs with hm
  · have hc : IsCoprime (m : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ h hc
    simpa using this
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- **(10) for all $s$** (p. 268): if $\chi_D$ (the function `Phi D` on $\mathbb Z/4\lvert D\rvert$) is the Dirichlet character
$\psi$ of level $k_1 \mid 4\lvert D\rvert$ viewed at level $4\lvert D\rvert$, then for every $s$ ($s \ne 1$, or $\psi$ nontrivial)
the analytic continuation of $\zeta_D$ is $L(s,\psi)\prod_{p \mid 4D}(1 - \psi(p)p^{-s})$. -/
@[kb "conwaysloane1988" "§8 (10), p. 268"]
theorem LD_eq_LFunction_mul {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    {s : ℂ} (hs : χ ≠ 1 ∨ s ≠ 1) :
    LD D hD s = χ.LFunction s * ∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) := by
  have := neZero_four_natAbs hD
  have hPhi : Phi D = (DirichletCharacter.changeLevel hdvd χ : ZMod (4 * D.natAbs) → ℂ) := by
    funext x
    rw [← ZMod.natCast_zmod_val x, Phi_natCast, hval]
  unfold LD
  rw [hPhi]
  exact DirichletCharacter.LFunction_changeLevel hdvd χ hs

/-- For real $s > 1$ the analytic continuation `LD D` takes the real value $\zeta_D(s)$. -/
theorem LD_eq_ofReal {D : ℤ} (hD : D ≠ 0) {s : ℝ} (hs : 1 < s) : LD D hD (s : ℂ) = (zetaD D s : ℂ) := by
  have hre : 1 < (s : ℂ).re := by simpa using hs
  rw [LD_eq_LSeries hD hre, ← (hasSum_zetaD hD hs).tsum_eq, Complex.ofReal_tsum, LSeries]
  congr 1
  funext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [chiD_zero]
  · rw [LSeries.term_of_ne_zero hn.ne']
    have h1 : ((n : ℂ) ^ (s : ℂ)) = (((n : ℝ) ^ s : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
    rw [h1]
    push_cast
    rfl

/-- **(13), p. 268**: Conway–Sloane's closed formula for $\zeta_D(s)$. Let $\psi$ be a primitive real Dirichlet character
modulo $k_1$ such that $\chi_D = \chi_1\psi$ on $\mathbb Z/4\lvert D\rvert$ (hypothesis `hval`, with $k_1 \mid 4\lvert D\rvert$), let
$s \ge 2$ be a natural number with $\psi(-1) = (-1)^s$, and $G(\psi) \ne 0$. Then
$$\zeta_D(s) = \prod_{p\mid 4D}\Bigl(1-\frac{\psi(p)}{p^s}\Bigr)\cdot\frac{-(2\pi)^s}{s!\,(i^{-s}+\psi(-1)i^s)}\cdot
\frac{\sum_{r=1}^{k_1}\psi(r)B_s(r/k_1)}{\sum_{r=1}^{k_1}\psi(r)e^{2\pi i r/k_1}}.$$ -/
@[kb "conwaysloane1988" "§8 (13), p. 268"]
theorem zetaD_formula {D : ℤ} (hD : D ≠ 0) {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hreal : χ⁻¹ = χ) (hdvd : N ∣ 4 * D.natAbs)
    (hval : ∀ m : ℕ, (chiD D m : ℂ) = DirichletCharacter.changeLevel hdvd χ (m : ZMod (4 * D.natAbs)))
    {s : ℕ} (hs : 2 ≤ s) (hpar : χ (-1) = (-1) ^ s) (hG : gaussSum χ stdAddChar ≠ 0) :
    (zetaD D s : ℂ) = (∏ p ∈ (4 * D.natAbs).primeFactors, (1 - χ p * (p : ℂ) ^ (-(s : ℂ)))) *
      (-(2 * π) ^ s / ((s.factorial : ℂ) * (I ^ (-(s : ℂ)) + χ (-1) * I ^ (s : ℂ)))) *
      (∑ r ∈ Icc 1 N, χ r * (((Polynomial.bernoulli s).eval ((r : ℚ) / N) : ℚ) : ℂ)) /
        gaussSum χ stdAddChar := by
  have hs1 : (1 : ℝ) < s := by exact_mod_cast hs
  have h := LD_eq_ofReal hD hs1
  rw [Complex.ofReal_natCast] at h
  rw [← h, LD_eq_LFunction_mul hD χ hdvd hval (Or.inr (by norm_cast; omega)),
    LFunction_nat_primitive hχ hreal hs hpar hG]
  ring

end QuadFormsKB.ConwaySloane.Mass
