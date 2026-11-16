import QuadFormsKB.Historical.Gauss.ResidueForms
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Genus characters and characteristic numbers (Disquisitiones Arithmeticae, Art. 233 II-III)

(Art. 233 II) and (Art. 233 III).

Write $f(x, y) = a x^2 + 2 b x y + c y^2$ for Gauss's form $(a, b, c)$ and $D = b^2 - ac$ for its determinant.

* Art. 233 II: if $M(a, b, c)$ is a quadratic residue of $m$ (`IsResidueForm`) with value $(g, h)$, then
  $M f(x, y) \equiv (g x + h y)^2 \pmod m$ (`art233_two_identity`). Hence, for $m = p^\mu$ with $p$ a prime and
  $M$ prime to $p$, the Legendre symbol of every value of $f$ prime to $p$ equals that of $M$
  (`art233_two_prime_power`); for $m = 4$ every odd value of $f$ is $\equiv M \pmod 4$ (`art233_two_four`); and for
  $m = 2^k$, $k \ge 3$, every odd value is $\equiv M \pmod 8$ (`art233_two_two_power`).
* Art. 233 III (converse): if $m = p^\kappa$ ($p$ an odd prime, $\kappa \ge 1$), $m = 4$ or $m = 2^k$ ($k \ge 3$)
  divides the determinant $D$, $M$ is prime to $m$ and $M$ agrees with the character of $(a, b, c)$ (some value
  $f(x, y)$ prime to $p$ with the same Legendre symbol as $M$, resp. an odd value $\equiv M \pmod 4$, resp.
  $\pmod 8$), then $M(a, b, c)$ is a quadratic residue of $m$ (`art233_three_prime_power`, `art233_three_four`,
  `art233_three_two_power`).

All of these are proved, unconditionally. The converse is proved without Gauss's reduction to coprime $(x, y)$ and
a completing substitution: the identity $f(x, y) f(X, Y) = B^2 - D\,(xY - yX)^2$, with
$B = a x X + b (x Y + y X) + c y Y$, gives directly $g = N' s u$, $h = N' s v$ with $N = f(x, y)$, $N'$ an inverse
of $N$ modulo $m$, $s^2 \equiv M N$, $u = a x + b y$, $v = b x + c y$. Squares modulo prime powers are lifted
by hand (Hensel step for odd $p$; for $2^k$ an odd number $\equiv 1 \pmod 8$ is a square).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **Art. 233 II, key identity:** if $(g, h)$ is a value of
$\sqrt{M(a, b, c)} \pmod m$, then $M (a x^2 + 2 b x y + c y^2) \equiv (g x + h y)^2 \pmod m$ for all $x, y$.
Valid for every modulus $m$. -/
@[kb "gauss1801" "Art. 233 II"]
theorem art233_two_identity {M a b c m g h : ℤ}
    (h1 : g ^ 2 ≡ M * a [ZMOD m]) (h2 : g * h ≡ M * b [ZMOD m]) (h3 : h ^ 2 ≡ M * c [ZMOD m]) (x y : ℤ) :
    M * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ≡ (g * x + h * y) ^ 2 [ZMOD m] := by
  have := ((h1.mul_left (x ^ 2)).add (h2.mul_left (2 * x * y))).add (h3.mul_left (y ^ 2))
  refine Int.ModEq.symm ?_
  convert this using 1 <;> ring

/-- **Art. 233 II for odd primes and prime powers:** if $M(a, b, c)$ is a quadratic
residue of $m = p^\mu$ ($p$ prime, $\mu \ge 1$) and $M$ is prime to $p$, then for all $x, y$ with $f(x, y)$ prime to
$p$ the Legendre symbols agree: $\left(\frac{f(x, y)}{p}\right) = \left(\frac{M}{p}\right)$, i.e. the character of
$(a, b, c)$ for $p$ is $R p$ or $N p$ according as $M$ is a residue or a non-residue of $p$. Gauss assumes $p$ odd;
the statement is proved for every prime $p$ (not needed to exclude $p = 2$). -/
@[kb "gauss1801" "Art. 233 II"]
theorem art233_two_prime_power {M a b c : ℤ} {p μ : ℕ} [Fact p.Prime] (hμ : 1 ≤ μ)
    (hres : IsResidueForm M a b c ((p : ℤ) ^ μ)) (hM : ¬ (p : ℤ) ∣ M) (x y : ℤ)
    (hf : ¬ (p : ℤ) ∣ a * x ^ 2 + 2 * b * x * y + c * y ^ 2) :
    legendreSym p (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = legendreSym p M := by
  obtain ⟨g, h, h1, h2, h3⟩ := hres
  have key := (art233_two_identity h1 h2 h3 x y).of_dvd (dvd_pow_self (p : ℤ) (by omega : μ ≠ 0))
  set N := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with hN
  have hM0 : (M : ZMod p) ≠ 0 := fun h0 => hM ((ZMod.intCast_zmod_eq_zero_iff_dvd M p).mp h0)
  have hN0 : (N : ZMod p) ≠ 0 := fun h0 => hf ((ZMod.intCast_zmod_eq_zero_iff_dvd N p).mp h0)
  have hMN0 : ((M * N : ℤ) : ZMod p) ≠ 0 := by push_cast; exact mul_ne_zero hM0 hN0
  have hcast : ((M * N : ℤ) : ZMod p) = (((g * x + h * y) ^ 2 : ℤ) : ZMod p) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr key
  have hsq : legendreSym p (M * N) = 1 := by
    have : legendreSym p (M * N) = legendreSym p ((g * x + h * y) ^ 2) := by
      simp only [legendreSym]; rw [hcast]
    rw [this]
    apply legendreSym.sq_one'
    intro h0
    apply hMN0
    rw [hcast]; rw [Int.cast_pow, h0]; simp
  rw [legendreSym.mul] at hsq
  rcases legendreSym.eq_one_or_neg_one p hM0 with h5 | h5 <;>
    rcases legendreSym.eq_one_or_neg_one p hN0 with h6 | h6 <;> rw [h5, h6] at hsq ⊢ <;> simp_all

/-- **Art. 233 II for the modulus $4$:** if $M(a, b, c)$ is a quadratic residue of $4$,
$M$ odd, then every odd value $f(x, y)$ is $\equiv M \pmod 4$. -/
@[kb "gauss1801" "Art. 233 II"]
theorem art233_two_four {M a b c : ℤ} (hres : IsResidueForm M a b c 4) (hM : Odd M) (x y : ℤ)
    (hf : Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2)) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 4] := by
  obtain ⟨g, h, h1, h2, h3⟩ := hres
  have key := art233_two_identity h1 h2 h3 x y
  set N := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with hN
  have hM4 : M % 4 = 1 ∨ M % 4 = 3 := by rcases hM with ⟨j, hj⟩; omega
  have hN4 : N % 4 = 1 ∨ N % 4 = 3 := by rcases hf with ⟨j, hj⟩; omega
  unfold Int.ModEq at key ⊢
  have e1 : (M * N) % 4 = ((M % 4) * (N % 4)) % 4 := Int.mul_emod _ _ _
  have e2 : ((g * x + h * y) ^ 2) % 4 = 0 ∨ ((g * x + h * y) ^ 2) % 4 = 1 := by
    rcases Int.emod_two_eq_zero_or_one (g * x + h * y) with h0 | h0
    · left
      obtain ⟨j, hj⟩ : ∃ j, g * x + h * y = 2 * j := ⟨(g * x + h * y) / 2, by omega⟩
      rw [hj]; ring_nf; omega
    · right
      obtain ⟨j, hj⟩ : ∃ j, g * x + h * y = 2 * j + 1 := ⟨(g * x + h * y) / 2, by omega⟩
      rw [hj]; ring_nf; omega
  rcases hM4 with h5 | h5 <;> rcases hN4 with h6 | h6 <;> rw [h5, h6] at e1 <;> omega

/-- **Art. 233 II for the modulus $2^k$, $k \ge 3$:** if $M(a, b, c)$ is a quadratic
residue of $2^k$ with $k \ge 3$ and $M$ odd, then every odd value $f(x, y)$ is $\equiv M \pmod 8$. (Gauss states
this for $m = 8$ and "$m = 2^k \ge 8$".) -/
@[kb "gauss1801" "Art. 233 II"]
theorem art233_two_two_power {M a b c : ℤ} {k : ℕ} (hk : 3 ≤ k) (hres : IsResidueForm M a b c ((2 : ℤ) ^ k))
    (hM : Odd M) (x y : ℤ) (hf : Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2)) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 8] := by
  obtain ⟨g, h, h1, h2, h3⟩ := hres
  have key := (art233_two_identity h1 h2 h3 x y).of_dvd
    (show (8 : ℤ) ∣ 2 ^ k from by
      have : (2 : ℤ) ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk
      simpa using this)
  set N := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with hN
  set s := g * x + h * y
  have hM8 : M % 8 = 1 ∨ M % 8 = 3 ∨ M % 8 = 5 ∨ M % 8 = 7 := by rcases hM with ⟨j, hj⟩; omega
  have hN8 : N % 8 = 1 ∨ N % 8 = 3 ∨ N % 8 = 5 ∨ N % 8 = 7 := by rcases hf with ⟨j, hj⟩; omega
  have hs8 : s % 8 = 0 ∨ s % 8 = 1 ∨ s % 8 = 2 ∨ s % 8 = 3 ∨ s % 8 = 4 ∨ s % 8 = 5 ∨ s % 8 = 6 ∨ s % 8 = 7 := by
    omega
  have es : s ^ 2 % 8 = ((s % 8) * (s % 8)) % 8 := by rw [pow_two]; exact Int.mul_emod _ _ _
  have e1 : (M * N) % 8 = ((M % 8) * (N % 8)) % 8 := Int.mul_emod _ _ _
  unfold Int.ModEq at key ⊢
  rcases hM8 with h5 | h5 | h5 | h5 <;> rcases hN8 with h6 | h6 | h6 | h6 <;>
    rcases hs8 with h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7 <;>
    rw [h5, h6] at e1 <;> rw [h7] at es <;> omega


/-- Squares lift from modulus $p$ to modulus $p^k$ for an odd prime $p$ (Hensel step, by induction on $k$). -/
theorem exists_sq_modEq_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n s0 : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (h0 : s0 ^ 2 ≡ n [ZMOD p]) (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : ℤ, s ^ 2 ≡ n [ZMOD (p : ℤ) ^ k] := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  induction k, hk using Nat.le_induction with
  | base => exact ⟨s0, by simpa using h0⟩
  | succ k hk ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hs
    have hs1 : s ^ 2 ≡ n [ZMOD p] := by
      have := hs.of_dvd (dvd_pow_self (p : ℤ) (by omega : k ≠ 0))
      simpa using this
    have hps : ¬ (p : ℤ) ∣ s := by
      intro hd
      apply hn
      have h1 : (p : ℤ) ∣ n - s ^ 2 := Int.modEq_iff_dvd.mp hs1
      have h2 : (p : ℤ) ∣ s ^ 2 := dvd_pow hd (by norm_num)
      simpa using dvd_add h1 h2
    have hp2' : ¬ (p : ℤ) ∣ 2 := by
      intro hd
      have : p ∣ 2 := by exact_mod_cast hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
    have hcop : IsCoprime (p : ℤ) (2 * s) := by
      rw [Irreducible.coprime_iff_not_dvd hpz.irreducible]
      intro hd
      rcases hpz.dvd_or_dvd hd with h | h
      · exact hp2' h
      · exact hps h
    obtain ⟨u, v, huv⟩ := hcop
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨s + e * v * (p : ℤ) ^ (j + 1), Int.modEq_iff_dvd.mpr ⟨e * u - (e * v) ^ 2 * (p : ℤ) ^ j, ?_⟩⟩
    linear_combination he - (p : ℤ) ^ (j + 1) * e * huv

/-- An odd number congruent to $1$ modulo $8$ is a square modulo every power $2^k$, $k \ge 3$ (with an odd root). -/
theorem exists_sq_modEq_two_pow {n : ℤ} (hn : n ≡ 1 [ZMOD 8]) (k : ℕ) (hk : 3 ≤ k) :
    ∃ s : ℤ, s ^ 2 ≡ n [ZMOD (2 : ℤ) ^ k] := by
  suffices H : ∃ s : ℤ, Odd s ∧ s ^ 2 ≡ n [ZMOD (2 : ℤ) ^ k] from by
    obtain ⟨s, -, hs⟩ := H; exact ⟨s, hs⟩
  induction k, hk using Nat.le_induction with
  | base => exact ⟨1, odd_one, by simpa using hn.symm⟩
  | succ k hk ih =>
    obtain ⟨s, ⟨r, hr⟩, hs⟩ := ih
    obtain ⟨e, he⟩ := Int.modEq_iff_dvd.mp hs
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    rcases Int.even_or_odd' e with ⟨jj, hj | hj⟩
    · refine ⟨s, ⟨r, hr⟩, Int.modEq_iff_dvd.mpr ⟨jj, ?_⟩⟩
      rw [he, hj]; ring
    · refine ⟨s + 2 ^ (j + 2), ⟨r + 2 ^ (j + 1), by rw [hr]; ring⟩,
        Int.modEq_iff_dvd.mpr ⟨jj - r - 2 ^ j, ?_⟩⟩
      subst hr
      rw [hj] at he
      linear_combination he

/-- The converse core of Art. 233 III: if $m \mid D$, $N = f(x, y)$ is invertible modulo $m$ and
$s^2 \equiv M N \pmod m$, then $M(a, b, c)$ is a quadratic residue of $m$ (value
$g = N' s (a x + b y)$, $h = N' s (b x + c y)$ with $N' N \equiv 1$). -/
theorem isResidueForm_of_sq_unit {M a b c m s x y : ℤ} (hD : m ∣ gaussDet a b c)
    (hcop : IsCoprime (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) m)
    (hs : s ^ 2 ≡ M * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) [ZMOD m]) :
    IsResidueForm M a b c m := by
  set N := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with hN
  obtain ⟨N', t, hN'⟩ := hcop
  have hinv : N' * N ≡ 1 [ZMOD m] := Int.modEq_iff_dvd.mpr ⟨t, by linear_combination (-1 : ℤ) * hN'⟩
  have hu1 : (a * x + b * y) ^ 2 ≡ N * a [ZMOD m] := by
    refine Int.modEq_iff_dvd.mpr (dvd_trans hD ⟨-(y ^ 2), ?_⟩)
    rw [hN]; simp only [gaussDet]; ring
  have hu2 : (a * x + b * y) * (b * x + c * y) ≡ N * b [ZMOD m] := by
    refine Int.modEq_iff_dvd.mpr (dvd_trans hD ⟨x * y, ?_⟩)
    rw [hN]; simp only [gaussDet]; ring
  have hu3 : (b * x + c * y) ^ 2 ≡ N * c [ZMOD m] := by
    refine Int.modEq_iff_dvd.mpr (dvd_trans hD ⟨-(x ^ 2), ?_⟩)
    rw [hN]; simp only [gaussDet]; ring
  have hs' := hs.symm
  refine ⟨N' * s * (a * x + b * y), N' * s * (b * x + c * y), ?_, ?_, ?_⟩
  · calc (N' * s * (a * x + b * y)) ^ 2 = N' ^ 2 * (s ^ 2 * (a * x + b * y) ^ 2) := by ring
      _ ≡ N' ^ 2 * ((M * N) * (N * a)) [ZMOD m] := (hs.mul hu1).mul_left _
      _ = M * a * (N' * N) ^ 2 := by ring
      _ ≡ M * a * 1 ^ 2 [ZMOD m] := (hinv.pow 2).mul_left _
      _ = M * a := by ring
  · calc N' * s * (a * x + b * y) * (N' * s * (b * x + c * y))
        = N' ^ 2 * (s ^ 2 * ((a * x + b * y) * (b * x + c * y))) := by ring
      _ ≡ N' ^ 2 * ((M * N) * (N * b)) [ZMOD m] := (hs.mul hu2).mul_left _
      _ = M * b * (N' * N) ^ 2 := by ring
      _ ≡ M * b * 1 ^ 2 [ZMOD m] := (hinv.pow 2).mul_left _
      _ = M * b := by ring
  · calc (N' * s * (b * x + c * y)) ^ 2 = N' ^ 2 * (s ^ 2 * (b * x + c * y) ^ 2) := by ring
      _ ≡ N' ^ 2 * ((M * N) * (N * c)) [ZMOD m] := (hs.mul hu3).mul_left _
      _ = M * c * (N' * N) ^ 2 := by ring
      _ ≡ M * c * 1 ^ 2 [ZMOD m] := (hinv.pow 2).mul_left _
      _ = M * c := by ring

/-- **Art. 233 III, odd prime power:** let $p$ be an odd prime, $\kappa \ge 1$, and
$p^\kappa$ divide the determinant $b^2 - ac$. If $M$ is prime to $p$ and agrees with the character of $(a, b, c)$
for $p$, in the sense that some value $f(x, y) = a x^2 + 2 b x y + c y^2$ is prime to $p$ and has the same Legendre
symbol as $M$, then $M(a, b, c)$ is a quadratic residue of $p^\kappa$. Proof differs from Gauss's (no reduction
to coprime $(x, y)$ and no completion to a substitution of determinant $1$); see the module docstring. -/
@[kb "gauss1801" "Art. 233 III"]
theorem art233_three_prime_power {M a b c : ℤ} {p κ : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hκ : 1 ≤ κ)
    (hdet : (p : ℤ) ^ κ ∣ gaussDet a b c) (hM : ¬ (p : ℤ) ∣ M)
    (hchar : ∃ x y : ℤ, ¬ (p : ℤ) ∣ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ∧
      legendreSym p (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) = legendreSym p M) :
    IsResidueForm M a b c ((p : ℤ) ^ κ) := by
  obtain ⟨x, y, hf, hleg⟩ := hchar
  set N := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with hN
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hM0 : (M : ZMod p) ≠ 0 := fun h0 => hM ((ZMod.intCast_zmod_eq_zero_iff_dvd M p).mp h0)
  have hN0 : (N : ZMod p) ≠ 0 := fun h0 => hf ((ZMod.intCast_zmod_eq_zero_iff_dvd N p).mp h0)
  have hMN0 : ((M * N : ℤ) : ZMod p) ≠ 0 := by push_cast; exact mul_ne_zero hM0 hN0
  have hMN : ¬ (p : ℤ) ∣ M * N := fun h0 => hMN0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h0)
  have hleg1 : legendreSym p (M * N) = 1 := by
    rw [legendreSym.mul, hleg, ← pow_two]; exact legendreSym.sq_one p hM0
  have hsq := (legendreSym.eq_one_iff p hMN0).mp hleg1
  obtain ⟨r, hr⟩ := hsq
  have h0 : ((r.val : ℤ) ^ 2) ≡ M * N [ZMOD p] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
    push_cast at hr ⊢
    rw [hr, ZMod.natCast_zmod_val, pow_two]
  obtain ⟨s, hs⟩ := exists_sq_modEq_prime_pow hp.out hp2 hMN h0 κ hκ
  have hcop : IsCoprime N ((p : ℤ) ^ κ) := by
    have : IsCoprime (p : ℤ) N := (Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hf
    exact this.symm.pow_right
  exact isResidueForm_of_sq_unit hdet hcop hs

/-- Odd squares are $\equiv 1 \pmod 8$. -/
theorem odd_mul_self_modEq_one_eight {M : ℤ} (hM : Odd M) : M * M ≡ 1 [ZMOD 8] := by
  have hM8 : M % 8 = 1 ∨ M % 8 = 3 ∨ M % 8 = 5 ∨ M % 8 = 7 := by rcases hM with ⟨j, hj⟩; omega
  have e : (M * M) % 8 = ((M % 8) * (M % 8)) % 8 := Int.mul_emod _ _ _
  unfold Int.ModEq
  rcases hM8 with h | h | h | h <;> rw [h] at e <;> omega

/-- Odd numbers are coprime to every power of $2$. -/
theorem isCoprime_two_pow_of_odd {N : ℤ} (hN : Odd N) (k : ℕ) : IsCoprime N ((2 : ℤ) ^ k) := by
  obtain ⟨j, hj⟩ := hN
  have : IsCoprime N 2 := ⟨1, -j, by rw [hj]; ring⟩
  exact this.pow_right

/-- **Art. 233 III, modulus $4$:** if $4$ divides the determinant $b^2 - ac$, $M$ is odd
and some odd value $f(x, y)$ is $\equiv M \pmod 4$ (the character of $(a, b, c)$ for $4$ agrees with $M$), then
$M(a, b, c)$ is a quadratic residue of $4$. -/
@[kb "gauss1801" "Art. 233 III"]
theorem art233_three_four {M a b c : ℤ} (hdet : (4 : ℤ) ∣ gaussDet a b c) (hM : Odd M)
    (hchar : ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 4]) :
    IsResidueForm M a b c 4 := by
  obtain ⟨x, y, hf, hMN⟩ := hchar
  have hcop : IsCoprime (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ((2 : ℤ) ^ 2) := isCoprime_two_pow_of_odd hf 2
  refine isResidueForm_of_sq_unit (s := 1) hdet (by simpa using hcop) ?_
  obtain ⟨j, hj⟩ := hM
  have h1 : M * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ≡ M * M [ZMOD 4] := hMN.mul_left M
  have h2 : 1 ^ 2 ≡ M * M [ZMOD 4] := Int.modEq_iff_dvd.mpr ⟨j * (j + 1), by rw [hj]; ring⟩
  exact h2.trans h1.symm

/-- **Art. 233 III, modulus $2^k$, $k \ge 3$:** if $2^k$ divides the determinant
$b^2 - ac$, $M$ is odd and some odd value $f(x, y)$ is $\equiv M \pmod 8$, then $M(a, b, c)$ is a quadratic residue
of $2^k$. -/
@[kb "gauss1801" "Art. 233 III"]
theorem art233_three_two_power {M a b c : ℤ} {k : ℕ} (hk : 3 ≤ k) (hdet : (2 : ℤ) ^ k ∣ gaussDet a b c)
    (hM : Odd M)
    (hchar : ∃ x y : ℤ, Odd (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ∧
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 ≡ M [ZMOD 8]) :
    IsResidueForm M a b c ((2 : ℤ) ^ k) := by
  obtain ⟨x, y, hf, hMN⟩ := hchar
  have hcop := isCoprime_two_pow_of_odd hf k
  have h1 : M * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) ≡ 1 [ZMOD 8] :=
    (hMN.mul_left M).trans (odd_mul_self_modEq_one_eight hM)
  obtain ⟨s, hs⟩ := exists_sq_modEq_two_pow h1 k hk
  exact isResidueForm_of_sq_unit hdet hcop hs

end QuadFormsKB.Historical.Gauss
