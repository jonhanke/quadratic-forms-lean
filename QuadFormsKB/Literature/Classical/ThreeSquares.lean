/-
# Legendre's three-squares theorem: the hard direction

**Theorem.** If $n \in \mathbb{N}$ is not of the form $4^a(8b + 7)$, then $n = x_0^2 + x_1^2 + x_2^2$
with $x_i \in \mathbb{N}$.

*Proof* (Serre, *A Course in Arithmetic*, Ch. IV, Appendix "Sums of three squares", pp. 45–47). Let
$Q = \langle 1, 1, 1 \rangle = x_0^2 + x_1^2 + x_2^2$ and $n \ge 1$.
1. **Locally.** $Q$ represents $n$ over $\mathbb{R}$ ($n > 0$) and over every $\mathbb{Q}_p$:
   * $p$ odd: by Chevalley–Warning in the form $\mathbb{F}_p = \{b^2 + c^2\}$ (Mathlib's
     `ZMod.sq_add_sq`) pick $y_1, y_2 \in \mathbb{Z}$ with $y_1^2 + y_2^2 \equiv n - 1 \pmod p$; then
     $n - y_1^2 - y_2^2 \equiv 1 \pmod p$ is a square in $\mathbb{Z}_p$ by Hensel's lemma.
   * $p = 2$: $n = 4^a m$ with $4 \nmid m$ and, by hypothesis, $m \not\equiv 7 \pmod 8$; so
     $m \bmod 8 \in \{1, 2, 3, 5, 6\}$ and $m - y_1^2 - y_2^2 \equiv 1 \pmod 8$ for suitable
     $y_1, y_2 \in \{0, 1, 2\}$, which is a square in $\mathbb{Z}_2$ by Hensel's lemma. Multiply by $2^a$.
   (This replaces Serre's Hilbert-symbol computation, IV §2.2 Thm. 6 and its Corollary, pp. 36–37, via Lemma A of the Appendix, pp. 45–46, by explicit
   Hensel lifting; the content is the same.)
2. **Globally over $\mathbb{Q}$.** Hasse–Minkowski (`QuadFormsKB.represents_iff_everywhere`, proved
   in this repository) gives $n = x_0^2 + x_1^2 + x_2^2$ with $x_i \in \mathbb{Q}$.
3. **Over $\mathbb{Z}$.** The Davenport–Cassels lemma for $\langle 1, 1, 1 \rangle$
   (`QuadFormsKB.DavenportCassels.sum_sq_int_of_rat`).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.Classical.DavenportCassels

open Polynomial

namespace QuadFormsKB.ThreeSquares

/-- **Hensel's lemma for square roots in $\mathbb{Z}_p$:** if $N, a \in \mathbb{Z}$ satisfy
$\lVert a^2 - N \rVert_p < \lVert 2a \rVert_p^2$, then $N = z^2$ for some $z \in \mathbb{Z}_p$.
*Proof.* Mathlib's `hensels_lemma` for $F = X^2 - N$, whose derivative at $a$ is $2a$. -/
theorem exists_sq_padicInt (p : ℕ) [Fact p.Prime] (N a : ℤ)
    (h : ‖((a ^ 2 - N : ℤ) : ℤ_[p])‖ < ‖((2 * a : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], z ^ 2 = (N : ℤ_[p]) := by
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := (X ^ 2 - C N : Polynomial ℤ)) (a := (a : ℤ_[p]))
    (by simpa [derivative_X_pow, map_ofNat] using h)
  exact ⟨z, by simpa [sub_eq_zero] using hz⟩

/-- **Odd primes:** for an odd prime $p$, every integer $n$ is a sum of three squares in
$\mathbb{Q}_p$: $n = x_0^2 + x_1^2 + x_2^2$ with $x_i \in \mathbb{Q}_p$. -/
theorem three_sq_padic_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (n : ℤ) :
    ∃ x y z : ℚ_[p], x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ_[p]) := by
  obtain ⟨b, c, hbc⟩ := ZMod.sq_add_sq p ((n - 1 : ℤ) : ZMod p)
  set y₁ : ℤ := (b.val : ℤ)
  set y₂ : ℤ := (c.val : ℤ)
  have hdvd : (p : ℤ) ∣ 1 ^ 2 - (n - y₁ ^ 2 - y₂ ^ 2) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hb : ((y₁ : ℤ) : ZMod p) = b := by simp [y₁]
    have hc : ((y₂ : ℤ) : ZMod p) = c := by simp [y₂]
    push_cast at hbc ⊢
    rw [hb, hc]; linear_combination hbc
  have h2 : ‖((2 * 1 : ℤ) : ℤ_[p])‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
    have : (p : ℤ) ∣ 2 := by simpa using hlt
    have hle := Int.le_of_dvd (by norm_num) this
    have := hp.out.two_le
    have : p = 2 := by omega
    exact hp2 this
  obtain ⟨w, hw⟩ := exists_sq_padicInt p (n - y₁ ^ 2 - y₂ ^ 2) 1 (by
    rw [h2, one_pow]; simpa using (PadicInt.norm_int_lt_one_iff_dvd _).mpr hdvd)
  refine ⟨(w : ℚ_[p]), (y₁ : ℚ_[p]), (y₂ : ℚ_[p]), ?_⟩
  have := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hw
  push_cast at this
  rw [this]; ring

/-- **The prime $2$, reduced case:** if $m \in \mathbb{Z}$ and $m \bmod 8 \in \{1, 2, 3, 5, 6\}$, then
$m = x_0^2 + x_1^2 + x_2^2$ with $x_i \in \mathbb{Q}_2$. -/
theorem three_sq_two_adic_of_mod (m : ℤ)
    (hm : m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 6) :
    ∃ x y z : ℚ_[2], x ^ 2 + y ^ 2 + z ^ 2 = (m : ℚ_[2]) := by
  have key : ∃ y₁ y₂ : ℤ, (8 : ℤ) ∣ 1 ^ 2 - (m - y₁ ^ 2 - y₂ ^ 2) := by
    rcases hm with h | h | h | h | h
    · exact ⟨0, 0, by omega⟩
    · exact ⟨1, 0, by omega⟩
    · exact ⟨1, 1, by omega⟩
    · exact ⟨2, 0, by omega⟩
    · exact ⟨2, 1, by omega⟩
  obtain ⟨y₁, y₂, hdvd⟩ := key
  have hlt : ‖((1 ^ 2 - (m - y₁ ^ 2 - y₂ ^ 2) : ℤ) : ℤ_[2])‖ < ‖((2 * 1 : ℤ) : ℤ_[2])‖ ^ 2 := by
    have h8 : ‖((1 ^ 2 - (m - y₁ ^ 2 - y₂ ^ 2) : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) := by
      have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := 1 ^ 2 - (m - y₁ ^ 2 - y₂ ^ 2))
        (n := 3)).mpr (by norm_num; exact hdvd)
      exact_mod_cast this
    have h2 : ‖((2 * 1 : ℤ) : ℤ_[2])‖ = 1 / 2 := by
      have := PadicInt.norm_p (p := 2)
      simp only [mul_one, Int.cast_ofNat]
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, this]; norm_num
    rw [h2]
    refine lt_of_le_of_lt h8 ?_
    norm_num
  obtain ⟨w, hw⟩ := exists_sq_padicInt 2 (m - y₁ ^ 2 - y₂ ^ 2) 1 hlt
  refine ⟨(w : ℚ_[2]), (y₁ : ℚ_[2]), (y₂ : ℚ_[2]), ?_⟩
  have := congrArg ((↑) : ℤ_[2] → ℚ_[2]) hw
  push_cast at this
  rw [this]; ring

/-- **The prime $2$:** if $n \in \mathbb{N}$ is not of the form $4^a(8b + 7)$, then
$n = x_0^2 + x_1^2 + x_2^2$ with $x_i \in \mathbb{Q}_2$.
*Proof.* Strong induction: if $4 \mid n$, scale a representation of $n/4$ by $2$; otherwise
$n \bmod 8 \in \{0, \dots, 7\} \setminus \{0, 4, 7\}$ and `three_sq_two_adic_of_mod` applies. -/
theorem three_sq_two_adic (n : ℕ) (hn : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℚ_[2], x ^ 2 + y ^ 2 + z ^ 2 = (n : ℚ_[2]) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, 0, 0, by simp⟩
  by_cases h4 : 4 ∣ n
  · obtain ⟨k, rfl⟩ := h4
    have hk : ¬ ∃ a b : ℕ, k = 4 ^ a * (8 * b + 7) := by
      rintro ⟨a, b, rfl⟩; exact hn ⟨a + 1, b, by ring⟩
    obtain ⟨x, y, z, h⟩ := ih k (by omega) hk
    refine ⟨2 * x, 2 * y, 2 * z, ?_⟩
    push_cast
    linear_combination 4 * h
  · have h7 : n % 8 ≠ 7 := fun h => hn ⟨0, n / 8, by omega⟩
    have := three_sq_two_adic_of_mod (n : ℤ) (by omega)
    simpa using this

/-- **Local representability** (Serre, *A Course in Arithmetic*, Ch. IV, Appendix, Lemma A, pp. 45–46): if $n \in \mathbb{N}$ is
not of the form $4^a(8b + 7)$, then $\langle 1, 1, 1 \rangle$ represents $n$ over $\mathbb{R}$ and over
every $\mathbb{Q}_p$. -/
theorem represents_everywhere (n : ℕ) (hn : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    RatPlace.Everywhere fun K _ _ =>
      (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))).RepresentsIn K (n : ℚ) := by
  have hsum : ∀ (K : Type) [Field K] [CharZero K] (x y z : K), x ^ 2 + y ^ 2 + z ^ 2 = (n : K) →
      (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))).RepresentsIn K (n : ℚ) := by
    intro K _ _ x y z h
    refine ⟨![x, y, z], ?_⟩
    rw [QuadForm.evalIn_diag, Fin.sum_univ_three]
    simp [h]
  intro v
  cases v with
  | infinite =>
    refine hsum ℝ (Real.sqrt n) 0 0 ?_
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    show (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))).RepresentsIn ℚ_[p.1] (n : ℚ)
    by_cases hp2 : p.1 = 2
    · obtain ⟨p, hp⟩ := p
      simp only at hp2
      subst hp2
      obtain ⟨x, y, z, h⟩ := three_sq_two_adic n hn
      exact hsum _ x y z h
    · obtain ⟨x, y, z, h⟩ := three_sq_padic_odd p.1 hp2 n
      exact hsum _ x y z (by simpa using h)

/-- **Legendre's three-squares theorem, hard direction** (Legendre 1798, Gauss 1801; Serre,
*A Course in Arithmetic*, Ch. IV, Appendix, Theorem (Gauss), p. 45; Grosswald, Ch. 4 [locator unverified, not on disk]): if $n \in \mathbb{N}$ is not of the
form $4^a(8b + 7)$ with $a, b \in \mathbb{N}$, then $n = x_0^2 + x_1^2 + x_2^2$ with $x_i \in \mathbb{N}$.

*Proof.* `represents_everywhere`, Hasse–Minkowski (`QuadFormsKB.represents_iff_everywhere`), then
Davenport–Cassels (`QuadFormsKB.DavenportCassels.sum_sq_int_of_rat`). -/
@[kb "serre1973" "Ch. IV, Appendix, p. 45"]
theorem three_squares_of_not_form (n : ℕ) (hn : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨0, 0, 0, rfl⟩
  have hQ : (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))).Nondegenerate :=
    QuadForm.nondegenerate_diag fun _ => one_ne_zero
  have hrat := (represents_iff_everywhere _ hQ (n : ℚ) (by exact_mod_cast hn0)).mpr
    (represents_everywhere n hn)
  obtain ⟨x, hx⟩ := hrat
  rw [QuadForm.evalIn_diag] at hx
  obtain ⟨y, hy⟩ := DavenportCassels.sum_sq_int_of_rat (m := 3) le_rfl (n : ℤ)
    ⟨x, by simpa using hx⟩
  refine ⟨(y 0).natAbs, (y 1).natAbs, (y 2).natAbs, ?_⟩
  rw [Fin.sum_univ_three] at hy
  have : (((y 0).natAbs ^ 2 + (y 1).natAbs ^ 2 + (y 2).natAbs ^ 2 : ℕ) : ℤ) = n := by
    push_cast [Int.natCast_natAbs, sq_abs]
    exact hy
  exact_mod_cast this

end QuadFormsKB.ThreeSquares
