/-
# Cassels, Chapter 14, Example 3: values of a binary form prime to $p$

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Examples, Ex. 3, p. 359: *define $(D/p)$ as in Ex. 2 for
$p \nmid D$ and put $(D/p) = 0$ if $p \mid D$. Let $f$ be a primitive integral form of discriminant $D$. Then the
number $N$ of pairs $(x, y) \bmod p$ with $f(x, y)$ prime to $p$ is $N = (p - 1)(p - (D/p))$. [$p = 2$ is not
excluded.]* The symbol is Siegel's `kroneckerSym` (Ex. 2's definition; it is $0$ when $p \mid D$).
-/
import QuadFormsKB.Siegel.ThetaCharacter
import QuadFormsKB.Binary.FormsIdeals

namespace QuadFormsKB.Composition

open BinQF

section Ex3Aux

variable (p : ℕ) [Fact p.Prime]

/-- For odd $p$, the number of $X \in \mathbb F_p$ with $X^2 = D Y^2$ is $1$ if $Y = 0$ and $1 + \chi(D)$ otherwise. -/
private lemma ex3_sqrt_count (hp : p ≠ 2) (D Y : ZMod p) :
    (((Finset.univ.filter (fun X : ZMod p => X ^ 2 = D * Y ^ 2)).card : ℕ) : ℤ) =
      if Y = 0 then 1 else quadraticChar (ZMod p) D + 1 := by
  split_ifs with hY
  · subst hY
    simp [Finset.filter_eq']
  · have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    have := quadraticChar_card_sqrts hF (D * Y ^ 2)
    have e : (Finset.univ.filter (fun X : ZMod p => X ^ 2 = D * Y ^ 2)) =
        {x : ZMod p | x ^ 2 = D * Y ^ 2}.toFinset := by
      ext x; simp
    rw [e, this, map_mul, map_pow]
    have : quadraticChar (ZMod p) Y ^ 2 = 1 := by
      exact quadraticChar_sq_one hY
    rw [this]; ring

/-- For odd $p$, $\#\{(X, Y) : X^2 \ne D Y^2\} = (p - 1)(p - \chi(D))$. -/
private lemma ex3_count_g (hp : p ≠ 2) (D : ZMod p) :
    (((Finset.univ.filter (fun v : ZMod p × ZMod p => v.1 ^ 2 ≠ D * v.2 ^ 2)).card : ℕ) : ℤ) =
      ((p : ℤ) - 1) * (p - quadraticChar (ZMod p) D) := by
  have hcard : (Fintype.card (ZMod p) : ℤ) = p := by simp
  have h1 : ∀ Y : ZMod p,
      (((Finset.univ.filter (fun X : ZMod p => X ^ 2 ≠ D * Y ^ 2)).card : ℕ) : ℤ) =
      p - (if Y = 0 then 1 else quadraticChar (ZMod p) D + 1) := by
    intro Y
    rw [← ex3_sqrt_count p hp D Y, ← hcard, ← Finset.card_univ,
      ← Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
        (fun X : ZMod p => X ^ 2 = D * Y ^ 2)]
    push_cast; ring
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  push_cast
  have h2 : ∀ Y : ZMod p, (∑ X : ZMod p, (if X ^ 2 ≠ D * Y ^ 2 then (1 : ℤ) else 0)) =
      p - (if Y = 0 then 1 else quadraticChar (ZMod p) D + 1) := by
    intro Y
    rw [← h1 Y, Finset.card_filter]; push_cast; rfl
  simp only [h2]
  rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp [Finset.filter_eq', Finset.filter_ne', Finset.card_erase_of_mem]
  have hp1 : (((p - 1 : ℕ)) : ℤ) = (p : ℤ) - 1 := by
    have := (Fact.out : p.Prime).pos; omega
  have e : quadraticCharFun (ZMod p) D = quadraticChar (ZMod p) D := rfl
  rw [hp1, e]; ring

/-- For odd $p$ and $a \ne 0$ in $\mathbb F_p$: the count of nonzero values of $a x^2 + b x y + c y^2$. -/
private lemma ex3_count_a (hp : p ≠ 2) (a b c : ZMod p) (ha : a ≠ 0) :
    (((Finset.univ.filter (fun v : ZMod p × ZMod p =>
        a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 ≠ 0)).card : ℕ) : ℤ) =
      ((p : ℤ) - 1) * (p - quadraticChar (ZMod p) (b ^ 2 - 4 * a * c)) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this
    exact hp this
  have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
  have h4a : 4 * a ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this, mul_assoc]; exact mul_ne_zero h2 h2a
  let e : ZMod p × ZMod p ≃ ZMod p × ZMod p :=
    { toFun := fun v => (2 * a * v.1 + b * v.2, v.2)
      invFun := fun w => ((w.1 - b * w.2) / (2 * a), w.2)
      left_inv := fun v => by
        ext
        · simp only; field_simp; ring
        · rfl
      right_inv := fun w => by
        ext
        · simp only; field_simp; ring
        · rfl }
  rw [← ex3_count_g p hp (b ^ 2 - 4 * a * c)]
  congr 1
  refine Finset.card_equiv e ?_
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.coe_fn_mk]
  have : (2 * a * v.1 + b * v.2) ^ 2 - (b ^ 2 - 4 * a * c) * v.2 ^ 2 =
      4 * a * (a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2) := by ring
  rw [Ne, Ne, ← sub_eq_zero (a := (2 * a * v.1 + b * v.2) ^ 2), this]
  simp [h4a]

/-- For odd $p$ and coefficients not all zero in $\mathbb F_p$, the count of nonzero values. -/
private lemma ex3_count_odd (hp : p ≠ 2) (a b c : ZMod p) (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    (((Finset.univ.filter (fun v : ZMod p × ZMod p =>
        a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 ≠ 0)).card : ℕ) : ℤ) =
      ((p : ℤ) - 1) * (p - quadraticChar (ZMod p) (b ^ 2 - 4 * a * c)) := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · have hb : b ≠ 0 := fun hb => h ⟨ha, hb, hc⟩
      subst ha hc
      have : (Finset.univ.filter (fun v : ZMod p × ZMod p =>
          (0 : ZMod p) * v.1 ^ 2 + b * v.1 * v.2 + 0 * v.2 ^ 2 ≠ 0)) =
          (Finset.univ.erase (0 : ZMod p)) ×ˢ (Finset.univ.erase (0 : ZMod p)) := by
        ext ⟨x, y⟩
        simp [hb]
      rw [this, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _)]
      have hp1 : (((p - 1 : ℕ)) : ℤ) = (p : ℤ) - 1 := by
        have := (Fact.out : p.Prime).pos; omega
      have hq : quadraticChar (ZMod p) (b ^ 2 - 4 * 0 * 0) = 1 := by
        simpa using quadraticChar_sq_one' hb
      simp only [Finset.card_univ, ZMod.card, hq]
      push_cast [hp1]
      ring
    · have := ex3_count_a p hp c b a hc
      have e : (Finset.univ.filter (fun v : ZMod p × ZMod p =>
          a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 ≠ 0)).card =
          (Finset.univ.filter (fun v : ZMod p × ZMod p =>
          c * v.1 ^ 2 + b * v.1 * v.2 + a * v.2 ^ 2 ≠ 0)).card := by
        refine Finset.card_equiv (Equiv.prodComm _ _) ?_
        intro v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodComm_apply, Prod.fst_swap,
          Prod.snd_swap]
        rw [show c * v.2 ^ 2 + b * v.2 * v.1 + a * v.1 ^ 2 =
          a * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 by ring]
      rw [e, this]
      rw [show b ^ 2 - 4 * c * a = b ^ 2 - 4 * a * c by ring]
  · exact ex3_count_a p hp a b c ha

/-- The reduction $\mathbb Z/8 \to \mathbb Z/2$. -/
private abbrev ex3h28 : ZMod 8 →+* ZMod 2 := ZMod.castHom (show 2 ∣ 8 by norm_num) (ZMod 2)

/-- The Kronecker symbol $(D/2)$ in terms of $D \bmod 8$. -/
private lemma ex3_kr_two (D : ℤ) : Siegel.kroneckerSym D 2 =
    if ex3h28 (D : ZMod 8) = 0 then 0 else ZMod.χ₈ (D : ZMod 8) := by
  have h1 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have h2 : (2 : ℕ) / 2 ^ 1 = 1 := by norm_num
  have hev : Even D ↔ ex3h28 (D : ZMod 8) = 0 := by
    rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
    simp
  rw [Siegel.kroneckerSym, h1, h2, pow_one, jacobiSym.one_right, mul_one]
  by_cases h : Even D
  · simp only [h, hev.1 h, ↓reduceIte]
  · simp only [h, mt hev.2 h, ↓reduceIte]

/-- The case $p = 2$, by a finite check over $\mathbb Z/8$. -/
private lemma ex3_two_key : ∀ A B C : ZMod 8, (ex3h28 A ≠ 0 ∨ ex3h28 B ≠ 0 ∨ ex3h28 C ≠ 0) →
    (((Finset.univ.filter (fun v : ZMod 2 × ZMod 2 =>
      ex3h28 A * v.1 ^ 2 + ex3h28 B * v.1 * v.2 + ex3h28 C * v.2 ^ 2 ≠ 0)).card : ℕ) : ℤ) =
    (2 - 1) * (2 - (if ex3h28 (B ^ 2 - 4 * A * C) = 0 then 0 else ZMod.χ₈ (B ^ 2 - 4 * A * C))) := by
  decide

/-- Integer-coefficient form of Ex. 3. -/
private lemma ex3_int (a b c : ℤ) (hf : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) :
    ((Finset.univ.filter (fun v : ZMod p × ZMod p =>
        (a : ZMod p) * v.1 ^ 2 + b * v.1 * v.2 + c * v.2 ^ 2 ≠ 0)).card : ℤ) =
      ((p : ℤ) - 1) * (p - Siegel.kroneckerSym (b ^ 2 - 4 * a * c) p) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hnot : ex3h28 (a : ZMod 8) ≠ 0 ∨ ex3h28 (b : ZMod 8) ≠ 0 ∨ ex3h28 (c : ZMod 8) ≠ 0 := by
      simp only [map_intCast, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
      by_contra hcon
      simp only [not_or, not_not] at hcon
      have := hf 2 (by exact_mod_cast hcon.1) (by exact_mod_cast hcon.2.1) (by exact_mod_cast hcon.2.2)
      rcases Int.isUnit_iff.1 this with h | h <;> omega
    have key := ex3_two_key _ _ _ hnot
    simp only [map_intCast] at key
    have hd : (((b ^ 2 - 4 * a * c : ℤ)) : ZMod 8) = (b : ZMod 8) ^ 2 - 4 * (a : ZMod 8) * c := by
      push_cast; ring
    rw [ex3_kr_two, hd]
    push_cast
    exact_mod_cast key
  · have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hnot : ¬((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0) := by
      simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
      rintro ⟨h1, h2, h3⟩
      have := hf p h1 h2 h3
      have h2p := (Fact.out : p.Prime).two_le
      rcases Int.isUnit_iff.1 this with h | h <;> omega
    rw [ex3_count_odd p hp2 _ _ _ hnot, Siegel.kroneckerSym_of_odd _ hodd,
      ← jacobiSym.legendreSym.to_jacobiSym]
    rw [legendreSym]
    push_cast
    rfl

end Ex3Aux

/-- **Cassels, Ch. 14, Ex. 3** (p. 359): *for a primitive integral binary form $f$ of discriminant $D$ and a prime
$p$ (including $p = 2$), the number of $(x, y) \in (\mathbb Z/p)^2$ with $f(x, y) \not\equiv 0 \pmod p$ is
$(p - 1)(p - (D/p))$.* -/
@[kb "cassels1978" "Ch. 14, Ex. 3, p. 359"]
theorem ex3 (p : ℕ) [Fact p.Prime] {f : BinQF} (hf : f.IsPrimitive) :
    ((Finset.univ.filter (fun v : ZMod p × ZMod p =>
        (f.a : ZMod p) * v.1 ^ 2 + f.b * v.1 * v.2 + f.c * v.2 ^ 2 ≠ 0)).card : ℤ) =
      ((p : ℤ) - 1) * (p - Siegel.kroneckerSym f.disc p) :=
  ex3_int p f.a f.b f.c hf

end QuadFormsKB.Composition
