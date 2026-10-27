/-
# Hilbert reciprocity over $\mathbb{Q}$

$\prod_v (a,b)_v = 1$ for $a, b \in \mathbb{Q}^\times$ (Serre III §2.1, Thm. 3), proved from the local
theory in `HilbertLocal.lean` and quadratic reciprocity. Kept in its own low-level file so that
everything above it (prescribed symbols, Hasse–Minkowski) can use it.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Equiv.Hilbert

namespace QuadFormsKB

open RatPlace

/-! ### Hilbert reciprocity -/

/-- Hilbert's product formula: `(a, b)_v = -1` at only finitely many places, and at an
even number of them (equivalently `∏_v (a, b)_v = 1`). -/
@[kb "serre1973" "Ch. III, §2.1, Thm. 3; cassels1978 Ch. 3, Lemma 3.4, p. 46"]
theorem hilbert_product_formula (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : RatPlace | v.hilbert a b = -1}.Finite ∧
      Even {v : RatPlace | v.hilbert a b = -1}.ncard := by
  classical
  have hpm : ∀ (v : RatPlace) (a b : ℚ), v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
    intro v a b
    cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
  have hfin : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → Function.HasFiniteMulSupport (fun v : RatPlace => v.hilbert a b) := by
    intro a b ha hb
    refine (HilbertLocal.hilbert_support_finite a b ha hb).subset ?_
    intro v hv
    rcases hpm v a b with h | h
    · exact absurd h hv
    · exact h
  obtain ⟨G, hG⟩ : ∃ G : ℚ → ℚ → ℤ, ∀ a b, G a b = ∏ᶠ v : RatPlace, v.hilbert a b := ⟨_, fun _ _ => rfl⟩
  have hmul : ∀ a a' b : ℚ, a ≠ 0 → a' ≠ 0 → b ≠ 0 → G (a * a') b = G a b * G a' b := by
    intro a a' b ha ha' hb
    rw [hG, hG, hG, ← finprod_mul_distrib (hfin a b ha hb) (hfin a' b ha' hb)]
    exact finprod_congr fun v => HilbertLocal.RatPlace.hilbert_mul_left v a a' b ha ha' hb
  have hcomm : ∀ a b : ℚ, G a b = G b a := by
    intro a b
    rw [hG, hG]
    exact finprod_congr fun v => by cases v <;> exact hilbertSymbol_comm _ _ _
  have hsq1 : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → G a b * G a b = 1 := by
    intro a b ha hb
    rw [hG, ← finprod_mul_distrib (hfin a b ha hb) (hfin a b ha hb)]
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rcases hpm v a b with h | h <;> rw [h] <;> norm_num
  have hself : ∀ x : ℚ, x ≠ 0 → G x x = G x (-1) := by
    intro x hx
    have h1 : G (-x) x = 1 := by
      rw [hG]
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      cases v
      · simp only [RatPlace.hilbert]; rw [hilbertSymbol_comm]; push_cast; exact hilbertSymbol_self_neg _ _
      · simp only [RatPlace.hilbert]; rw [hilbertSymbol_comm]; push_cast; exact hilbertSymbol_self_neg _ _
    have h2 : G (-x) x = G (-1) x * G x x := by
      rw [← hmul _ _ _ (by norm_num) hx hx]; ring_nf
    have h3 := hsq1 (-1) x (by norm_num) hx
    rw [hcomm x (-1)]
    calc G x x = G (-1) x * G (-1) x * G x x := by rw [h3, one_mul]
      _ = G (-1) x * G (-x) x := by rw [h2]; ring
      _ = G (-1) x := by rw [h1, mul_one]
  have hint : ∀ (P : ℚ → Prop), (∀ a b : ℚ, a ≠ 0 → b ≠ 0 → P a → P b → P (a * b)) → P (-1) →
      (∀ p : ℕ, p.Prime → P p) → ∀ m : ℤ, m ≠ 0 → P m := by
    intro P hPm hP1 hPp
    have hn : ∀ n : ℕ, n ≠ 0 → P n := by
      intro n
      induction n using induction_on_primes with
      | zero => intro h; exact absurd rfl h
      | one => intro _; have := hPm _ _ (by norm_num) (by norm_num) hP1 hP1; norm_num at this; exact_mod_cast this
      | prime_mul p a hp ih =>
        intro h
        have ha : a ≠ 0 := by rintro rfl; simp at h
        have := hPm _ _ (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha) (hPp p hp) (ih ha)
        exact_mod_cast this
    intro m hm
    have hm' : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
    rcases Int.natAbs_eq m with h | h
    · rw [h, Int.cast_natCast]; exact hn _ hm'
    · rw [h, Int.cast_neg, Int.cast_natCast]
      have := hPm _ _ (by norm_num) (by exact_mod_cast hm') hP1 (hn _ hm')
      simpa using this
  have hunit : ∀ (p : ℕ) [Fact p.Prime] (m : ℤ), ¬ (p:ℤ) ∣ m → ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) = m := by
    intro p _ m hm
    have h1 : ‖(m : ℤ_[p])‖ = 1 := by
      have := PadicInt.norm_le_one (m : ℤ_[p])
      have h2 := (PadicInt.norm_int_lt_one_iff_dvd m).not.2 hm
      push Not at h2; linarith
    exact ⟨(PadicInt.isUnit_iff.2 h1).unit, rfl⟩
  have Hodd : ∀ (p : ℕ) [hp : Fact p.Prime], p ≠ 2 → ∀ (α β : ℕ) (m n : ℤ) (x y : ℚ), ¬ (p:ℤ) ∣ m → ¬ (p:ℤ) ∣ n →
      x = (p:ℚ)^α * m → y = (p:ℚ)^β * n →
      (RatPlace.finite ⟨p, hp.out⟩).hilbert x y = (-1)^(α*β*((p-1)/2)) * legendreSym p m ^ β * legendreSym p n ^ α := by
    intro p hp hp2 α β m n x y hm hn hx hy
    obtain ⟨u, hu⟩ := hunit p m hm
    obtain ⟨v, hv⟩ := hunit p n hn
    have hx' : ((x:ℚ) : ℚ_[p]) = (p:ℚ_[p])^α * ((u:ℤ_[p]) : ℚ_[p]) := by
      rw [hu, hx]; push_cast; rfl
    have hy' : ((y:ℚ) : ℚ_[p]) = (p:ℚ_[p])^β * ((v:ℤ_[p]) : ℚ_[p]) := by
      rw [hv, hy]; push_cast; rfl
    show hilbertSymbol ℚ_[p] (x : ℚ_[p]) (y : ℚ_[p]) = _
    rw [hx', hy', HilbertLocal.hilbertSymbol_odd_formula hp2]
    simp only [HilbertLocal.unitChar, hu, hv, map_intCast]
    rfl
  have H2 : ∀ (α β : ℕ) (m n : ℤ) (x y : ℚ), ¬ (2:ℤ) ∣ m → ¬ (2:ℤ) ∣ n →
      x = (2:ℚ)^α * m → y = (2:ℚ)^β * n →
      (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert x y = (-1) ^
      (HilbertLocal.twoEps (m : ZMod (2^3)) * HilbertLocal.twoEps (n : ZMod (2^3)) +
          α * HilbertLocal.twoOmega (n : ZMod (2^3)) + β * HilbertLocal.twoOmega (m : ZMod (2^3))) := by
    intro α β m n x y hm hn hx hy
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := hunit 2 m (by exact_mod_cast hm)
    obtain ⟨v, hv⟩ := hunit 2 n (by exact_mod_cast hn)
    have hx' : ((x:ℚ) : ℚ_[2]) = (2:ℚ_[2])^α * ((u:ℤ_[2]) : ℚ_[2]) := by
      rw [hu, hx]; push_cast; rfl
    have hy' : ((y:ℚ) : ℚ_[2]) = (2:ℚ_[2])^β * ((v:ℤ_[2]) : ℚ_[2]) := by
      rw [hv, hy]; push_cast; rfl
    show hilbertSymbol ℚ_[2] (x : ℚ_[2]) (y : ℚ_[2]) = _
    rw [hx', hy', HilbertLocal.hilbertSymbol_two_formula]
    simp only [hu, hv, map_intCast]
  have Hout : ∀ (x y : ℚ) (s : Finset RatPlace), x ≠ 0 → y ≠ 0 → RatPlace.infinite ∈ s →
      RatPlace.finite ⟨2, Nat.prime_two⟩ ∈ s →
      (∀ ℓ : Nat.Primes, RatPlace.finite ℓ ∉ s → padicValRat ℓ x = 0 ∧ padicValRat ℓ y = 0) →
      G x y = ∏ v ∈ s, v.hilbert x y := by
    intro x y s hx hy hinf h2 hval
    rw [hG]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hvs
    apply hv
    cases v with
    | infinite => exact absurd hinf hvs
    | finite ℓ =>
      obtain ⟨hx0, hy0⟩ := hval ℓ hvs
      have : Fact (ℓ:ℕ).Prime := ⟨ℓ.2⟩
      have hl2 : (ℓ:ℕ) ≠ 2 := by
        intro h
        apply hvs
        have : ℓ = ⟨2, Nat.prime_two⟩ := Subtype.ext h
        rw [this]; exact h2
      exact HilbertLocal.hilbert_eq_one_of_padicValRat hl2 x y hx hy hx0 hy0
  have hmem : ∀ (ℓ : Nat.Primes) (s : Finset RatPlace) (p : ℕ) (hp : p.Prime),
      RatPlace.finite ⟨p, hp⟩ ∈ s → RatPlace.finite ℓ ∉ s → (ℓ:ℕ) ≠ p := by
    intro ℓ s p hp h1 h2 h
    apply h2
    have : ℓ = ⟨p, hp⟩ := Subtype.ext h
    rw [this]; exact h1
  have hne : ∀ (p q : ℕ) (hp : p.Prime) (hq : q.Prime), p ≠ q →
      RatPlace.finite ⟨p, hp⟩ ≠ RatPlace.finite ⟨q, hq⟩ := by
    intro p q hp hq h e
    injection e with e'
    exact h (congrArg Subtype.val e')
  have hinf1 : ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → (0 < x ∨ 0 < y) → RatPlace.infinite.hilbert x y = 1 := by
    intro x y hx hy hxy
    rcases hpm RatPlace.infinite x y with h | h
    · exact h
    · exfalso
      have := (hilbertSymbol_real (x:ℝ) (y:ℝ) (by exact_mod_cast hx) (by exact_mod_cast hy)).1 h
      have h1 : x < 0 := by exact_mod_cast this.1
      have h2 : y < 0 := by exact_mod_cast this.2
      rcases hxy with h3 | h3 <;> linarith
  have hvneg1 : ∀ ℓ : ℕ, padicValRat ℓ (-1) = 0 := by intro ℓ; simp
  have hvp : ∀ ℓ p : ℕ, p.Prime → ℓ.Prime → ℓ ≠ p → padicValRat ℓ (p : ℚ) = 0 := by
    intro ℓ p hp hl hlp
    rw [padicValRat.of_nat]
    have : ¬ ℓ ∣ p := fun h => hlp ((Nat.prime_dvd_prime_iff_eq hl hp).1 h)
    simp [padicValNat.eq_zero_of_not_dvd this]
  have hvp2 : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → padicValRat ℓ (2 : ℚ) = 0 := by
    intro ℓ hl hl2
    have := hvp ℓ 2 Nat.prime_two hl hl2
    exact_mod_cast this
  have hndvd : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → ¬ (p:ℤ) ∣ (q:ℤ) := by
    intro p q hp hq hpq h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (Int.natCast_dvd_natCast.1 h))
  have hndvd1 : ∀ p : ℕ, p.Prime → ¬ (p:ℤ) ∣ (-1:ℤ) := by
    intro p hp h
    rw [Int.dvd_neg] at h
    exact hp.not_dvd_one (by exact_mod_cast h)
  have hndvd1' : ∀ p : ℕ, p.Prime → ¬ (p:ℤ) ∣ (1:ℤ) := by
    intro p hp h
    exact hp.not_dvd_one (by exact_mod_cast h)
  have hEps : ∀ p : ℕ, p % 2 = 1 → HilbertLocal.twoEps ((p:ℤ) : ZMod (2^3)) = (p/2) % 2 := by
    intro p hp
    have h8 : ((p:ℤ) : ZMod (2^3)) = ((p % 8 : ℕ) : ZMod (2^3)) := by
      rw [Int.cast_natCast]; exact (ZMod.natCast_mod p (2^3)).symm
    rw [h8]
    rcases (by omega : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) with h | h | h | h <;>
      rw [h] <;> [rw [show p/2%2 = 0 by omega]; rw [show p/2%2 = 1 by omega];
        rw [show p/2%2 = 0 by omega]; rw [show p/2%2 = 1 by omega]] <;> decide
  have hOm : ∀ p : ℕ, p % 2 = 1 → (-1:ℤ) ^ HilbertLocal.twoOmega ((p:ℤ) : ZMod (2^3)) = ZMod.χ₈ p := by
    intro p hp
    have h8 : ((p:ℤ) : ZMod (2^3)) = ((p % 8 : ℕ) : ZMod (2^3)) := by
      rw [Int.cast_natCast]; exact (ZMod.natCast_mod p (2^3)).symm
    rw [h8, ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
    rcases (by omega : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) with h | h | h | h <;>
      rw [h] <;> decide
  have hsqm1 : ∀ n : ℕ, (-1:ℤ)^n * (-1)^n = 1 := by
    intro n; rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hA : G (-1) (-1) = 1 := by
    rw [Hout (-1) (-1) {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩} (by norm_num) (by norm_num)
      (by simp) (by simp) (fun ℓ _ => ⟨hvneg1 _, hvneg1 _⟩)]
    rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    have hinf : RatPlace.infinite.hilbert (-1) (-1) = -1 := by
      show hilbertSymbol ℝ _ _ = -1
      push_cast
      exact (hilbertSymbol_real _ _ (by norm_num) (by norm_num)).2 ⟨by norm_num, by norm_num⟩
    rw [hinf, H2 0 0 (-1) (-1) (-1) (-1) (by decide) (by decide) (by simp) (by simp)]
    simp [HilbertLocal.twoEps]
    decide
  have hB : G (-1) 2 = 1 := by
    rw [Hout (-1) 2 {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩} (by norm_num) (by norm_num)
      (by simp) (by simp) (fun ℓ hℓ => ⟨hvneg1 _, hvp2 _ ℓ.2 (hmem ℓ _ 2 Nat.prime_two (by simp) hℓ)⟩)]
    rw [Finset.prod_insert (by simp), Finset.prod_singleton]
    rw [hinf1 _ _ (by norm_num) (by norm_num) (by norm_num),
      H2 0 1 (-1) 1 (-1) 2 (by decide) (by decide) (by simp) (by simp)]
    simp [HilbertLocal.twoEps, HilbertLocal.twoOmega]
    decide
  have hC : ∀ p : ℕ, p.Prime → p ≠ 2 → G (-1) p = 1 := by
    intro p hp hp2
    have := Fact.mk hp
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    rw [Hout (-1) p {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩, RatPlace.finite ⟨p, hp⟩}
      (by norm_num) (by exact_mod_cast hp.ne_zero) (by simp) (by simp)
      (fun ℓ hℓ => ⟨hvneg1 _, hvp _ _ hp ℓ.2 (hmem ℓ _ p hp (by simp) hℓ)⟩)]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp [hne 2 p Nat.prime_two hp (Ne.symm hp2)]),
      Finset.prod_singleton]
    rw [hinf1 _ _ (by norm_num) (by exact_mod_cast hp.ne_zero) (Or.inr (by exact_mod_cast hp.pos)),
      H2 0 0 (-1) p (-1) p (by decide) (by omega) (by simp) (by simp),
      Hodd p hp2 0 1 (-1) 1 (-1) p (hndvd1 p hp) (hndvd1' p hp) (by simp) (by simp)]
    have h7 : HilbertLocal.twoEps ((-1:ℤ) : ZMod (2^3)) = 1 := by decide
    simp only [legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hpodd, hEps p hpodd, h7,
      one_mul, zero_mul, add_zero, pow_zero, pow_one, legendreSym.at_one, mul_one]
    rw [← neg_one_pow_eq_pow_mod_two, hsqm1]
  have hD : ∀ p : ℕ, p.Prime → p ≠ 2 → G 2 p = 1 := by
    intro p hp hp2
    have := Fact.mk hp
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    rw [Hout 2 p {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩, RatPlace.finite ⟨p, hp⟩}
      (by norm_num) (by exact_mod_cast hp.ne_zero) (by simp) (by simp)
      (fun ℓ hℓ => ⟨hvp2 _ ℓ.2 (hmem ℓ _ 2 Nat.prime_two (by simp) hℓ), hvp _ _ hp ℓ.2 (hmem ℓ _ p hp (by simp) hℓ)⟩)]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp [hne 2 p Nat.prime_two hp (Ne.symm hp2)]),
      Finset.prod_singleton]
    rw [hinf1 _ _ (by norm_num) (by exact_mod_cast hp.ne_zero) (Or.inr (by exact_mod_cast hp.pos)),
      H2 1 0 1 p 2 p (by decide) (by omega) (by simp) (by simp),
      Hodd p hp2 0 1 2 1 2 p (hndvd p 2 hp Nat.prime_two hp2) (hndvd1' p hp) (by simp) (by simp)]
    have h7 : HilbertLocal.twoEps ((1:ℤ) : ZMod (2^3)) = 0 := by decide
    simp only [h7, zero_mul, zero_add, one_mul, add_zero, pow_one, pow_zero, legendreSym.at_one, mul_one]
    have h8 := legendreSym.at_two hp2
    push_cast at h8
    rw [h8, hOm p hpodd, ← hOm p hpodd, hsqm1]
  have hE : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ 2 → q ≠ 2 → p ≠ q → G p q = 1 := by
    intro p q hp hq hp2 hq2 hpq
    have := Fact.mk hp
    have := Fact.mk hq
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    have hqodd : q % 2 = 1 := Nat.odd_iff.1 (hq.odd_of_ne_two hq2)
    rw [Hout p q {RatPlace.infinite, RatPlace.finite ⟨2, Nat.prime_two⟩, RatPlace.finite ⟨p, hp⟩,
        RatPlace.finite ⟨q, hq⟩}
      (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero) (by simp) (by simp)
      (fun ℓ hℓ => ⟨hvp _ _ hp ℓ.2 (hmem ℓ _ p hp (by simp) hℓ), hvp _ _ hq ℓ.2 (hmem ℓ _ q hq (by simp) hℓ)⟩)]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp [hne 2 p Nat.prime_two hp (Ne.symm hp2),
        hne 2 q Nat.prime_two hq (Ne.symm hq2)]),
      Finset.prod_insert (by simp [hne p q hp hq hpq]), Finset.prod_singleton]
    rw [hinf1 _ _ (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero) (Or.inr (by exact_mod_cast hq.pos)),
      H2 0 0 p q p q (by omega) (by omega) (by simp) (by simp),
      Hodd p hp2 1 0 1 q p q (hndvd1' p hp) (hndvd p q hp hq hpq) (by simp) (by simp),
      Hodd q hq2 0 1 p 1 p q (hndvd q p hq hp (Ne.symm hpq)) (hndvd1' q hq) (by simp) (by simp)]
    simp only [hEps p hpodd, hEps q hqodd, zero_mul, mul_zero, add_zero, pow_one, pow_zero,
      legendreSym.at_one, one_mul, mul_one]
    have hqr := legendreSym.quadratic_reciprocity hp2 hq2 hpq
    rw [neg_one_pow_eq_pow_mod_two] at hqr
    rw [neg_one_pow_eq_pow_mod_two, ← Nat.mul_mod, mul_comm (legendreSym p q), hqr, hsqm1]
  have hm1 : ∀ q : ℕ, q.Prime → G (-1) q = 1 := by
    intro q hq
    by_cases hq2 : q = 2
    · subst hq2; exact_mod_cast hB
    · exact hC q hq hq2
  have hdist : ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q → G p q = 1 := by
    intro p q hp hq hpq
    by_cases hp2 : p = 2
    · subst hp2; exact_mod_cast hD q hq (Ne.symm hpq)
    · by_cases hq2 : q = 2
      · subst hq2; rw [hcomm]; exact_mod_cast hD p hp hp2
      · exact hE p q hp hq hp2 hq2 hpq
  have hgen : ∀ x y : ℚ, (x = -1 ∨ ∃ p : ℕ, p.Prime ∧ x = p) → (y = -1 ∨ ∃ p : ℕ, p.Prime ∧ y = p) →
      G x y = 1 := by
    intro x y hx hy
    rcases hx with rfl | ⟨p, hp, rfl⟩ <;> rcases hy with rfl | ⟨q, hq, rfl⟩
    · exact hA
    · exact hm1 q hq
    · rw [hcomm]; exact hm1 p hp
    · by_cases hpq : p = q
      · subst hpq
        rw [hself _ (by exact_mod_cast hp.ne_zero), hcomm]; exact hm1 p hp
      · exact hdist p q hp hq hpq
  have hY : ∀ y : ℚ, (y = -1 ∨ ∃ p : ℕ, p.Prime ∧ y = p) → ∀ n : ℤ, n ≠ 0 → G n y = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rcases hy with rfl | ⟨p, hp, rfl⟩
      · norm_num
      · exact_mod_cast hp.ne_zero
    refine hint (fun x => G x y = 1) ?_ (hgen _ _ (Or.inl rfl) hy) (fun p hp => hgen _ _ (Or.inr ⟨p, hp, rfl⟩) hy)
    intro a b ha hb h1 h2
    rw [hmul _ _ _ ha hb hy0, h1, h2, one_mul]
  have hZ : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 → G m n = 1 := by
    intro m n hm hn
    have hn0 : (n:ℚ) ≠ 0 := by exact_mod_cast hn
    refine hint (fun x => G x n = 1) ?_ ?_ ?_ m hm
    · intro a b ha hb h1 h2
      rw [hmul _ _ _ ha hb hn0, h1, h2, one_mul]
    · rw [hcomm]; exact hY _ (Or.inl rfl) n hn
    · intro p hp; rw [hcomm]; exact hY _ (Or.inr ⟨p, hp, rfl⟩) n hn
  have hdec : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → G a b = G (a.num : ℚ) b * G (a.den : ℚ) b := by
    intro a b ha hb
    have hn : (a.num : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr ha
    have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have hd' : (1 / (a.den : ℚ)) ≠ 0 := by simpa using hd
    have : a = ((a.num : ℚ) * a.den) * ((1 / a.den) * (1 / a.den)) := by
      conv_lhs => rw [← Rat.num_div_den a]
      field_simp
    conv_lhs => rw [this]
    rw [hmul _ _ _ (mul_ne_zero hn hd) (mul_ne_zero hd' hd') hb, hmul _ _ _ hn hd hb,
      hmul _ _ _ hd' hd' hb, hsq1 _ _ hd' hb, mul_one]
  have hQZ : ∀ (a : ℚ) (n : ℤ), a ≠ 0 → n ≠ 0 → G a n = 1 := by
    intro a n ha hn
    rw [hdec a n ha (by exact_mod_cast hn), hZ _ _ (Rat.num_ne_zero.mpr ha) hn]
    have := hZ a.den n (by exact_mod_cast a.den_nz) hn
    push_cast at this
    rw [this, one_mul]
  have main : G a b = 1 := by
    rw [hdec a b ha hb, hcomm, hQZ _ _ hb (Rat.num_ne_zero.mpr ha), hcomm]
    have := hQZ b a.den hb (by exact_mod_cast a.den_nz)
    push_cast at this
    rw [this, one_mul]
  have hF := HilbertLocal.hilbert_support_finite a b ha hb
  refine ⟨hF, ?_⟩
  have hms : Function.mulSupport (fun v : RatPlace => v.hilbert a b) = {v | v.hilbert a b = -1} := by
    ext v
    rcases hpm v a b with h | h <;> simp [Function.mem_mulSupport, h]
  rw [hG, finprod_eq_prod_of_mulSupport_subset _ (s := hF.toFinset) (by rw [hms]; simp)] at main
  rw [Finset.prod_congr rfl (fun v hv => (by simpa using hv : v.hilbert a b = -1))] at main
  rw [Finset.prod_const, neg_one_pow_eq_one_iff_even (by decide)] at main
  rwa [Set.ncard_eq_toFinset_card _ hF]

end QuadFormsKB
