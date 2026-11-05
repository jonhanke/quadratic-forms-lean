/-
# Cassels, Chapter 6, §4: Legendre's original form of Theorem 4.1

**Setting.** Cassels, *Rational Quadratic Forms*, Ch. 6, §4 and the Notes of Ch. 6: $g(\vec x) = a_0x_0^2 + a_1x_1^2 +
a_2x_2^2$ with integers $a_j$ and $a_0a_1a_2$ squarefree (Cassels' $a_1, a_2, a_3$ are $a_0, a_1, a_2$ here; indices of
`Fin 3` are taken modulo $3$, so $j + 1$, $j + 2$ are the two other indices). A zero is $\vec b \in \mathbb Z^3$,
$\vec b \ne \vec 0$, with $g(\vec b) = 0$. "Indefinite" means that some $a_i$ is positive and some $a_j$ is negative.

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6)
* the Note after Corollary 2 to Theorem 4.1 (p. 82): in the theorem actually proved by Legendre one has $p_0 = 2$, so
  the conditions (ii) and (iii) of Theorem 4.1 (the conditions at $2$) may be omitted provided $g$ is indefinite:
  `legendre_indefinite`;
* Legendre's original form (Notes of Ch. 6, p. 97): if $a_0a_1a_2$ is squarefree, $g$ is indefinite and there are
  integers $e_j$ with $a_{j+2} \mid a_je_j^2 + a_{j+1}$ for every $j$, then $g$ has a nontrivial integral zero:
  `legendre_original`.

**Reconstructed.** Neither statement is proved in the book, which only indicates the argument for the first; the proof
below is that argument made explicit. The Note says Theorem 4.1 is proved with $p_0 = 2$ in Cassels' Corollary 2:
for the ternary form $g$ we check isotropy over $\mathbb R$ (indefinite), and over $\mathbb Q_p$ for every odd prime $p$
(`isotropic_padic_of_cond`, the converse of Lemma 4.2 for odd $p$: if $p \nmid a_0a_1a_2$ the Hilbert symbol
$(-a_0a_1, -a_0a_2)_p$ of two $p$-adic units is $1$; if $p \mid a_j$, then by condition (i) the Hilbert symbol equals
the Legendre symbol $\left(\frac{-a_{j+1}a_{j+2}}{p}\right) = 1$, using the explicit formula for odd $p$,
`ConwaySloane.hilbert_odd_int`). Corollary 2 (`isotropic_of_isotropic_except`, with the exceptional place $p_0 = 2$)
then gives a rational zero, and clearing denominators gives an integral one.

The 1-based printed congruences (£) $a_1e_1^2 + a_2 \equiv 0 \pmod{a_3}$, $a_2e_2^2 + a_3 \equiv 0 \pmod{a_1}$,
$a_3e_3^2 + a_1 \equiv 0 \pmod{a_2}$ are, with 0-based indices, $a_{j+2} \mid a_je_j^2 + a_{j+1}$ for $j = 0, 1, 2$
(with $e_j$ playing the role of Cassels' $e_{j+1}$). They imply condition (i) of Theorem 4.1 at every odd prime
(`cond_i_of_original`): if a prime $p \mid a_j$, then (£) at the index $j + 1$ says $a_j = a_{(j+1)+2} \mid
a_{j+1}e_{j+1}^2 + a_{j+2}$, so $r = e_{j+1}$ works.
-/
import QuadFormsKB.Literature.Cassels.Ch6.Sec4
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.ConwaySloane

namespace QuadFormsKB.Cassels.Ch6

open QuadFormsKB

section Helpers

/-- Helper: the value of the diagonal ternary form $\langle a, b, c\rangle$ over a field $K \supseteq \mathbb Q$ on a
vector $t \in K^3$ (the arguments $a, b, c \in \mathbb Q$ are the coefficients, $t$ the vector). -/
private lemma evalIn_diag3 (K : Type*) [Field K] [CharZero K] (a b c : ℚ) (t : Fin 3 → K) :
    QuadForm.evalIn K (QuadForm.diag ![a, b, c]) t =
      algebraMap ℚ K a * t 0 ^ 2 + algebraMap ℚ K b * t 1 ^ 2 + algebraMap ℚ K c * t 2 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_three, Matrix.diagonal]
  ring

/-- Helper: isotropy of $\langle x, y, z\rangle$ (nonzero integers $x, y, z$) over $\mathbb Q_p$ is equivalent to
$(-xy, -xz)_p = 1$, where $p$ is a prime. -/
private theorem isotropic_diag_iff_hilbert (p : ℕ) [hp : Fact p.Prime] (x y z : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) :
    (QuadForm.diag ![(x : ℚ), y, z]).IsotropicIn ℚ_[p] ↔
      (RatPlace.finite ⟨p, hp.out⟩).hilbert ((-(x * y) : ℤ) : ℚ) ((-(x * z) : ℤ) : ℚ) = 1 := by
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  rw [HM3.isotropic_diag_three_iff ℚ_[p] _ _ _ hx' (by exact_mod_cast hy) (by exact_mod_cast hz)]
  have hc : ((1 / x : ℚ) : ℚ_[p]) ≠ 0 := by
    have : (1 / x : ℚ) ≠ 0 := by simp [hx']
    exact_mod_cast this
  have e : ∀ w : ℤ, algebraMap ℚ ℚ_[p] (-w / x) =
      (((-(x * w) : ℤ) : ℚ) : ℚ_[p]) * ((1 / x : ℚ) : ℚ_[p]) ^ 2 := by
    intro w
    rw [eq_ratCast]
    push_cast
    field_simp
  rw [e, e, HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm,
    HM3.hilbertSymbol_mul_sq_left _ _ _ _ hc, hilbertSymbol_comm]
  rfl

/-- Helper: a prime $p$ does not divide a nonzero integer coprime-to-$p$ product's factor: if $p \mid u$ then
$\neg\, p \mid v$ and $\neg\, p \mid w$ whenever $uvw$ is squarefree (the arguments $u, v, w$ are the three
coefficients, in the order of the product). -/
private lemma not_dvd_of_sqfree (p : ℕ) (hp : p.Prime) (u v w : ℤ) (hsq : Squarefree (u * v * w))
    (hu : (p : ℤ) ∣ u) : ¬ (p : ℤ) ∣ v ∧ ¬ (p : ℤ) ∣ w ∧ ¬ (p : ℤ) * p ∣ u := by
  have hpu : ¬ IsUnit (p : ℤ) := fun h => hp.not_isUnit (Int.ofNat_isUnit.mp h)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := h
    exact hpu (hsq p ⟨a * b * w, by ring⟩)
  · obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := h
    exact hpu (hsq p ⟨a * v * b, by ring⟩)
  · obtain ⟨a, rfl⟩ := h
    exact hpu (hsq p ⟨a * v * w, by ring⟩)

/-- Helper: if $\langle y, z, x\rangle$ has a zero over a field $K \supseteq \mathbb Q$, so has $\langle x, y,
z\rangle$ (cyclic rotation of the coefficients $x, y, z \in \mathbb Q$). -/
private lemma isotropic_rot (K : Type*) [Field K] [CharZero K] (x y z : ℚ)
    (h : (QuadForm.diag ![y, z, x]).IsotropicIn K) : (QuadForm.diag ![x, y, z]).IsotropicIn K := by
  obtain ⟨t, ht, hq⟩ := h
  refine ⟨![t 2, t 0, t 1], ?_, ?_⟩
  · intro h0
    apply ht
    funext i
    fin_cases i
    · exact congrFun h0 1
    · exact congrFun h0 2
    · exact congrFun h0 0
  · rw [evalIn_diag3] at hq ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linear_combination hq

/-- Helper: the Legendre symbol identity $(-1)^{(p-1)/2} = \left(\frac{-1}{p}\right)$ for an odd prime $p$. -/
private lemma neg_one_pow_eq_legendreSym (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (-1 : ℤ) ^ ((p - 1) / 2) = legendreSym p (-1) := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hodd]
  congr 1
  omega

/-- Helper: **isotropy over $\mathbb Q_p$ at a prime not dividing the coefficients** ($p$ odd): for nonzero integers
$x, y, z$ not divisible by the odd prime $p$, $\langle x, y, z\rangle$ is isotropic over $\mathbb Q_p$ (the Hilbert
symbol $(-xy, -xz)_p$ of two $p$-adic units is $1$). -/
private theorem isotropic_padic_unit (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (x y z : ℤ)
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (hz : ¬ (p : ℤ) ∣ z) :
    (QuadForm.diag ![(x : ℚ), y, z]).IsotropicIn ℚ_[p] := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have nz : ∀ w : ℤ, ¬ (p : ℤ) ∣ w → w ≠ 0 := fun w h h0 => h (h0 ▸ dvd_zero _)
  have hxy : ¬ (p : ℤ) ∣ -(x * y) := by
    rw [dvd_neg]; exact fun h => (hpr.dvd_or_dvd h).elim hx hy
  have hxz : ¬ (p : ℤ) ∣ -(x * z) := by
    rw [dvd_neg]; exact fun h => (hpr.dvd_or_dvd h).elim hx hz
  rw [isotropic_diag_iff_hilbert p x y z (nz _ hx) (nz _ hy) (nz _ hz)]
  have := ConwaySloane.hilbert_odd_int p hp2 0 0 (-(x * y)) (-(x * z)) ((-(x * y) : ℤ) : ℚ) ((-(x * z) : ℤ) : ℚ) hxy hxz (by simp) (by simp)
  rw [this]
  simp

/-- Helper: **isotropy over $\mathbb Q_p$ at a prime dividing the first coefficient** ($p$ odd; the converse of
Cassels' Lemma 4.2 at an odd prime): let $x, y, z$ be integers with $xyz$ squarefree, $p$ an odd prime with $p \mid x$,
and suppose $yr^2 + z \equiv 0 \pmod p$ for some $r$ (condition (i) of Theorem 4.1); then $\langle x, y, z\rangle$ is
isotropic over $\mathbb Q_p$. -/
private theorem isotropic_padic_dvd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (x y z : ℤ)
    (hsq : Squarefree (x * y * z)) (hpx : (p : ℤ) ∣ x) (hr : ∃ r : ℤ, (p : ℤ) ∣ y * r ^ 2 + z) :
    (QuadForm.diag ![(x : ℚ), y, z]).IsotropicIn ℚ_[p] := by
  obtain ⟨hy, hz, hx2⟩ := not_dvd_of_sqfree p hp.out x y z hsq hpx
  obtain ⟨m, rfl⟩ := hpx
  have hm : ¬ (p : ℤ) ∣ m := fun h => hx2 (mul_dvd_mul_left _ h)
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have nz : ∀ w : ℤ, ¬ (p : ℤ) ∣ w → w ≠ 0 := fun w h h0 => h (h0 ▸ dvd_zero _)
  have hx0 : (p : ℤ) * m ≠ 0 := hsq.ne_zero ∘ fun h => by simp [h]
  have hmy : ¬ (p : ℤ) ∣ -(m * y) := by
    rw [dvd_neg]; exact fun h => (hpr.dvd_or_dvd h).elim hm hy
  have hmz : ¬ (p : ℤ) ∣ -(m * z) := by
    rw [dvd_neg]; exact fun h => (hpr.dvd_or_dvd h).elim hm hz
  rw [isotropic_diag_iff_hilbert p _ y z hx0 (nz _ hy) (nz _ hz)]
  have key := ConwaySloane.hilbert_odd_int p hp2 1 1 (-(m * y)) (-(m * z)) ((-((p : ℤ) * m * y) : ℤ) : ℚ)
    ((-((p : ℤ) * m * z) : ℤ) : ℚ) hmy hmz
    (by push_cast; ring) (by push_cast; ring)
  rw [key]
  simp only [one_mul, mul_one, pow_one]
  rw [neg_one_pow_eq_legendreSym p hp2]
  -- the product of the three Legendre symbols is the symbol of a square modulo `p`
  obtain ⟨r, hrd⟩ := hr
  have hr0 : ((r : ℤ) : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    apply hz
    have : (p : ℤ) ∣ (y * r ^ 2 + z) - y * r ^ 2 := dvd_sub hrd (Dvd.dvd.mul_left (dvd_pow h0 two_ne_zero) y)
    simpa using this
  have hy0 : ((y : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hm0 : ((m : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← legendreSym.mul, ← legendreSym.mul]
  have hz' : (z : ZMod p) = -((y : ZMod p) * (r : ZMod p) ^ 2) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hrd
    push_cast at this
    linear_combination this
  have : ((-1 * -(m * y) * -(m * z) : ℤ) : ZMod p) = ((m : ZMod p) * y * r) ^ 2 := by
    push_cast
    rw [hz']
    ring
  unfold legendreSym
  rw [this]
  exact quadraticChar_sq_one' (mul_ne_zero (mul_ne_zero hm0 hy0) hr0)

end Helpers

/-- **Local isotropy at odd primes under condition (i)** (the converse of Cassels' Lemma 4.2 for odd $p$): let
$a_0, a_1, a_2$ be integers with $a_0a_1a_2$ squarefree satisfying condition (i) of Theorem 4.1 (for every odd prime
$p \mid a_j$ there is $r$ with $a_{j+1}r^2 + a_{j+2} \equiv 0 \pmod p$), and let $p$ be an odd prime; then the form
$a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ is isotropic over $\mathbb Q_p$. The case $p \nmid a_0a_1a_2$ is a unit form; the case
$p \mid a_j$ uses the explicit formula for the Hilbert symbol. Cassels' Lemma 4.2 (p. 79) is the converse
implication (isotropy over $\mathbb Q_p$ gives the congruence). -/
@[kb "cassels1978" "Ch. 6, Lemma 4.2, p. 79 (converse, odd p)"]
theorem isotropic_padic_of_cond (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (QuadForm.diag ![(a 0 : ℚ), a 1, a 2]).IsotropicIn ℚ_[p] := by
  have sq1 : Squarefree (a 1 * a 2 * a 0) := by
    have : a 1 * a 2 * a 0 = a 0 * a 1 * a 2 := by ring
    rwa [this]
  have sq2 : Squarefree (a 2 * a 0 * a 1) := by
    have : a 2 * a 0 * a 1 = a 0 * a 1 * a 2 := by ring
    rwa [this]
  by_cases h0 : (p : ℤ) ∣ a 0
  · exact isotropic_padic_dvd p hp2 _ _ _ hsq h0 (hi p hp.out hp2 0 h0)
  by_cases h1 : (p : ℤ) ∣ a 1
  · exact isotropic_rot ℚ_[p] _ _ _
      (isotropic_padic_dvd p hp2 _ _ _ sq1 h1 (hi p hp.out hp2 1 h1))
  by_cases h2 : (p : ℤ) ∣ a 2
  · exact isotropic_rot ℚ_[p] _ _ _ (isotropic_rot ℚ_[p] _ _ _
      (isotropic_padic_dvd p hp2 _ _ _ sq2 h2 (hi p hp.out hp2 2 h2)))
  · exact isotropic_padic_unit p hp2 _ _ _ h0 h1 h2

/-- Helper: an indefinite diagonal ternary form with integer coefficients $a_0, a_1, a_2$ (some $a_i > 0$, some
$a_j < 0$) is isotropic over $\mathbb R$. -/
private theorem isotropic_real (a : Fin 3 → ℤ) (hpos : ∃ i, 0 < a i) (hneg : ∃ j, a j < 0) :
    (QuadForm.diag ![(a 0 : ℚ), a 1, a 2]).IsotropicIn ℝ := by
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  have hij : j ≠ i := fun h => by subst h; omega
  have hi' : (0 : ℝ) < a i := by exact_mod_cast hi
  have hj' : (a j : ℝ) < 0 := by exact_mod_cast hj
  set t : Fin 3 → ℝ := fun k => if k = i then √(-(a j : ℝ)) else if k = j then √(a i : ℝ) else 0 with ht
  have tpos : 0 < t i := by
    simp only [ht, ite_true]
    exact Real.sqrt_pos.mpr (by linarith)
  refine ⟨t, fun h0 => (tpos.ne' (congrFun h0 i)), ?_⟩
  rw [evalIn_diag3]
  simp only [eq_ratCast, Rat.cast_intCast]
  have hsum : (a 0 : ℝ) * t 0 ^ 2 + a 1 * t 1 ^ 2 + a 2 * t 2 ^ 2 = ∑ k, (a k : ℝ) * t k ^ 2 := by
    rw [Fin.sum_univ_three]
  rw [hsum, Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij.symm]
  · have e1 : t i = √(-(a j : ℝ)) := by simp [ht]
    have e2 : t j = √(a i : ℝ) := by simp [ht, hij]
    rw [e1, e2, Real.sq_sqrt (by linarith), Real.sq_sqrt hi'.le]
    ring
  · intro k _ hk
    simp [ht, hk.1, hk.2]

/-- Helper: **clearing denominators** — a rational zero of $a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ ($a_j \in \mathbb Z$) gives a
nonzero integral zero. -/
private theorem exists_int_zero_of_rat (a : Fin 3 → ℤ)
    (h : (QuadForm.diag ![(a 0 : ℚ), a 1, a 2]).IsotropicIn ℚ) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 := by
  obtain ⟨x, hx, hq⟩ := h
  rw [evalIn_diag3] at hq
  simp only [eq_ratCast, Rat.cast_id] at hq
  set D : ℕ := ∏ i, (x i).den with hD
  have hDpos : (D : ℚ) ≠ 0 := by
    have : 0 < D := Finset.prod_pos (fun i _ => (x i).den_pos)
    exact_mod_cast this.ne'
  have hb : ∀ i, ∃ z : ℤ, (z : ℚ) = x i * D := by
    intro i
    obtain ⟨k, hk⟩ : (x i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(x i).num * k, ?_⟩
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num (x i)]
    ring
  choose b hb using hb
  refine ⟨b, ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have := hb i
    rw [h0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hDpos
  · have : ((∑ i, a i * b i ^ 2 : ℤ) : ℚ) = 0 := by
      push_cast
      simp only [Fin.sum_univ_three, hb]
      linear_combination (D : ℚ) ^ 2 * hq
    exact_mod_cast this

/-- **Cassels, Ch. 6, §4, Note after Corollary 2 to Theorem 4.1 (p. 82): Legendre's form with $p_0 = 2$.** *In the
theorem actually proved by Legendre one has $p_0 = 2$; thus in Theorem 4.1 one may omit the conditions (ii) and (iii)
(the conditions at $2$) provided one adds that $g$ is indefinite.* Let $g = a_0x_0^2 + a_1x_1^2 + a_2x_2^2$ with
$a = (a_0, a_1, a_2)$ integers, `hsq`: $a_0a_1a_2$ squarefree; `hi`: condition (i) of Theorem 4.1 (for every odd prime
$p \mid a_j$ there is an integer $r$ with $a_{j+1}r^2 + a_{j+2} \equiv 0 \pmod p$, as in `legendre`); and
indefiniteness: some $a_i > 0$ and some $a_j < 0$. Then there are $b_0, b_1, b_2 \in \mathbb Z$, not all $0$, with
$g(\vec b) = 0$.

*Proof.* The form is isotropic over $\mathbb R$ (indefinite) and over $\mathbb Q_p$ for every odd prime $p$
(`isotropic_padic_of_cond`); Corollary 2 (`isotropic_of_isotropic_except`) with the exceptional place $2$ gives a
rational zero, and clearing denominators an integral one. -/
@[kb "cassels1978" "Ch. 6, §4, Note after Cor. 2 to Thm. 4.1, p. 82 (Legendre's form: p₀ = 2)"]
theorem legendre_indefinite (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2))
    (hindef : (∃ i, 0 < a i) ∧ (∃ j, a j < 0)) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 := by
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    apply hsq.ne_zero
    fin_cases i <;> simp_all
  have hQ : (QuadForm.diag ![(a 0 : ℚ), a 1, a 2]).Nondegenerate := by
    refine QuadForm.nondegenerate_diag (fun i => ?_)
    fin_cases i <;> simpa using ha _
  have hiso := isotropic_of_isotropic_except _ hQ (RatPlace.finite ⟨2, Nat.prime_two⟩) (fun v hv => by
    cases v with
    | infinite => exact isotropic_real a hindef.1 hindef.2
    | finite p =>
      have : Fact (p : ℕ).Prime := ⟨p.2⟩
      have hp2 : (p : ℕ) ≠ 2 := fun h => hv (by congr; exact Subtype.ext h)
      exact isotropic_padic_of_cond a hsq hi p hp2)
  exact exists_int_zero_of_rat a hiso

/-- Helper: **Legendre's congruences (£) imply condition (i) of Theorem 4.1** (0-based): if $a_{j+2} \mid a_je_j^2 +
a_{j+1}$ for $j = 0, 1, 2$, then for every prime $p \ne 2$ with $p \mid a_j$ there is $r$ with $a_{j+1}r^2 + a_{j+2}
\equiv 0 \pmod p$. Here $a$ is the coefficient vector and $e$ the vector of integers $e_j$ of (£); the proof applies
(£) at the index $j + 1$, which says $a_{j+3} = a_j \mid a_{j+1}e_{j+1}^2 + a_{j+2}$, so $r = e_{j+1}$. -/
private theorem cond_i_of_original (a : Fin 3 → ℤ) (e : Fin 3 → ℤ)
    (he : ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1)) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ j : Fin 3, (p : ℤ) ∣ a j →
      ∃ r : ℤ, (p : ℤ) ∣ a (j + 1) * r ^ 2 + a (j + 2) := by
  intro p _ _ j hj
  refine ⟨e (j + 1), dvd_trans hj ?_⟩
  have h := he (j + 1)
  have e1 : j + 1 + 2 = j := by
    fin_cases j <;> decide
  have e2 : j + 1 + 1 = j + 2 := by
    fin_cases j <;> decide
  rwa [e1, e2] at h

/-- **Cassels, Ch. 6, Notes, p. 97: Legendre's original form of Theorem 4.1.** *Let $g = a_0x_0^2 + a_1x_1^2 +
a_2x_2^2$ with integers $a_j$, $a_0a_1a_2$ squarefree, and suppose there are integers $e_0, e_1, e_2$ with the
congruences (£) $a_0e_0^2 + a_1 \equiv 0 \pmod{a_2}$, $a_1e_1^2 + a_2 \equiv 0 \pmod{a_0}$, $a_2e_2^2 + a_0 \equiv 0
\pmod{a_1}$ (0-based form of Cassels' $a_1e_1^2 + a_2 \equiv 0 \pmod{a_3}$, etc.: $a_{j+2} \mid a_je_j^2 + a_{j+1}$).
If $g$ is indefinite (some $a_i > 0$ and some $a_j < 0$), then $g(\vec b) = 0$ for some $\vec b \in \mathbb Z^3
\setminus \{\vec 0\}$.* Here `e` is the vector $(e_0, e_1, e_2)$.

*Proof.* (£) implies condition (i) at every prime (`cond_i_of_original`); apply `legendre_indefinite`. -/
@[kb "cassels1978" "Ch. 6, Notes, p. 97 (Legendre's original form of Thm. 4.1, conditions (£))"]
theorem legendre_original (a : Fin 3 → ℤ) (hsq : Squarefree (a 0 * a 1 * a 2))
    (hcong : ∃ e : Fin 3 → ℤ, ∀ j : Fin 3, a (j + 2) ∣ a j * e j ^ 2 + a (j + 1))
    (hindef : (∃ i, 0 < a i) ∧ (∃ j, a j < 0)) :
    ∃ b : Fin 3 → ℤ, b ≠ 0 ∧ ∑ i, a i * b i ^ 2 = 0 := by
  obtain ⟨e, he⟩ := hcong
  exact legendre_indefinite a hsq (cond_i_of_original a e he) hindef

end QuadFormsKB.Cassels.Ch6
