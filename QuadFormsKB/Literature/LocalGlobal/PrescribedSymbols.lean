/-
# Rational numbers with prescribed local Hilbert symbols: the blueprint

Serre, *A Course in Arithmetic*, III §2.2, Thm. 4. Given $a_i \in \mathbb{Q}^\times$ ($i$ in a finite
set) and signs $\varepsilon_{i,v} \in \{\pm 1\}$, there is $x \in \mathbb{Q}^\times$ with
$(a_i, x)_v = \varepsilon_{i,v}$ for all $i, v$ iff

1. $\varepsilon_{i,v} = 1$ for almost all $(i, v)$;
2. $\prod_v \varepsilon_{i,v} = 1$ for every $i$ (Hilbert reciprocity);
3. for every place $v$ there is $x_v \in \mathbb{Q}_v^\times$ with $(a_i, x_v)_v = \varepsilon_{i,v}$.

This is the key input to Hasse–Minkowski for $n = 4$. The proof needs density of
$\mathbb{Q}$ in $\mathbb{Q}_v$ up to squares, simultaneous approximation (CRT), and Dirichlet's
theorem on primes in progressions (Mathlib: `Nat.forall_exists_prime_gt_and_eq_mod`).

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertReciprocity

namespace QuadFormsKB.Prescribed

open RatPlace

/-! ### Density and approximation -/

/-- **Every $p$-adic square class contains a rational:** for $x \in \mathbb{Q}_p^\times$ there is
$q \in \mathbb{Q}^\times$ with $x / q$ a square in $\mathbb{Q}_p$. -/
@[kb "serre1973" "Ch. II §3.3 [unverified]"]
theorem exists_rat_sq_class (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    ∃ q : ℚ, q ≠ 0 ∧ IsSquare (x / (q : ℚ_[p])) := by
  have h4 : (4:ℚ_[p]) ≠ 0 := by norm_num
  have hc : 0 < ‖(4:ℚ_[p])‖ := norm_pos_iff.mpr h4
  have hc1 : ‖(4:ℚ_[p])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := p) 4
    simpa using this
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨r, hr⟩ := Padic.rat_dense p x (mul_pos hxn hc)
  set a : ℚ_[p] := (r : ℚ_[p]) / x with ha
  have ha1 : ‖a - 1‖ < ‖(4:ℚ_[p])‖ := by
    have : a - 1 = ((r:ℚ_[p]) - x) / x := by rw [ha]; field_simp
    rw [this, norm_div, div_lt_iff₀ hxn, norm_sub_rev, mul_comm]; exact hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp [ha] at ha1
    linarith
  have hale : ‖a‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (a - 1) 1
    simp only [sub_add_cancel, norm_one] at this
    refine this.trans (max_le (by linarith) le_rfl)
  let A : ℤ_[p] := ⟨a, hale⟩
  have hAc : (A : ℚ_[p]) = a := rfl
  have hA : ‖Polynomial.eval 1 (Polynomial.X ^ 2 - Polynomial.C A)‖ <
      ‖Polynomial.eval 1 (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C A))‖ ^ 2 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      one_pow, sub_zero, Polynomial.eval_mul]
    have e1 : ‖(1 : ℤ_[p]) - A‖ = ‖a - 1‖ := by
      rw [norm_sub_rev, PadicInt.norm_def]; simp [hAc]
    have e2 : ‖((2:ℕ) : ℤ_[p]) * 1‖ ^ 2 = ‖(4:ℚ_[p])‖ := by
      rw [mul_one, ← norm_pow, PadicInt.norm_def, PadicInt.coe_pow, PadicInt.coe_natCast]
      norm_num
    rw [e1, e2]; exact ha1
  obtain ⟨z, hz, -⟩ := hensels_lemma hA
  have hz' : z ^ 2 = A := by
    simpa [sub_eq_zero] using hz
  refine ⟨r, hr0, ?_⟩
  have : IsSquare a := by
    refine ⟨((z : ℤ_[p]) : ℚ_[p]), ?_⟩
    rw [← hAc, ← hz']; push_cast; ring
  rw [← inv_div]
  exact this.inv

/-- **The local Hilbert symbol only depends on square classes (second argument):** over a field
$K$, if $x' / x$ is a nonzero square then $(a, x')_K = (a, x)_K$. -/
@[kb "serre1973" "Ch. III §1.1 [unverified]"]
theorem hilbertSymbol_eq_of_isSquare_div (K : Type*) [Field K] (a x x' : K) (hx : x ≠ 0)
    (hx' : x' ≠ 0) (h : IsSquare (x' / x)) :
    hilbertSymbol K a x' = hilbertSymbol K a x := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    rcases hc with h | h <;> contradiction
  have hx'eq : x' = x * c ^ 2 := by
    rw [div_eq_iff hx] at hc
    rw [hc]; ring
  have key : (∃ X Y Z : K, (X, Y, Z) ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + x' * Y ^ 2) ↔
      (∃ X Y Z : K, (X, Y, Z) ≠ 0 ∧ Z ^ 2 = a * X ^ 2 + x * Y ^ 2) := by
    constructor
    · rintro ⟨X, Y, Z, hne, heq⟩
      refine ⟨X, c * Y, Z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
        rcases h0 with ⟨h1, h2 | h2, h3⟩
        · exact absurd h2 hc0
        · exact ⟨h1, h2, h3⟩
      · rw [heq, hx'eq]; ring
    · rintro ⟨X, Y, Z, hne, heq⟩
      refine ⟨X, Y / c, Z, ?_, ?_⟩
      · intro h0
        apply hne
        simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
        rcases h0 with ⟨h1, h2 | h2, h3⟩
        · exact ⟨h1, h2, h3⟩
        · exact absurd h2 hc0
      · rw [heq, hx'eq]; field_simp
  unfold hilbertSymbol
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.mp h1) h2
  · exact absurd (key.mpr h2) h1
  · rfl

/-- **Simultaneous approximation of square classes (CRT):** given a finite set $T$ of primes,
a nonzero rational $q_p$ for each $p \in T$ and a sign $s \in \{\pm 1\}$, there is
$x \in \mathbb{Q}^\times$ with $x / q_p$ a square in $\mathbb{Q}_p$ for every $p \in T$ and with the
sign of $x$ equal to $s$. -/
@[kb "serre1973" "Ch. III §2.2, Lemma 2 [unverified]"]
theorem exists_rat_approx_sq_classes (T : Finset Nat.Primes) (q : Nat.Primes → ℚ)
    (hq : ∀ p ∈ T, q p ≠ 0) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃ x : ℚ, x ≠ 0 ∧ (0 < x ↔ s = 1) ∧
      ∀ p ∈ T, haveI : Fact p.1.Prime := ⟨p.2⟩; IsSquare ((x : ℚ_[p.1]) / (q p : ℚ_[p.1])) := by
  have hensel : ∀ (p : ℕ) [Fact p.Prime] (y : ℚ_[p]), ‖y - 1‖ < ‖(2:ℚ_[p])‖ ^ 2 → IsSquare y := by
    intro p _ y hy
    have h2 : ‖(2:ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) 2
      simpa using this
    have hy1 : ‖y‖ ≤ 1 := by
      have : y = (y - 1) + 1 := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (by simp))
      nlinarith [norm_nonneg (2:ℚ_[p])]
    set z : ℤ_[p] := ⟨y, hy1⟩
    obtain ⟨w, hw, -⟩ := hensels_lemma (p := p) (R := ℤ_[p]) (F := Polynomial.X ^ 2 - Polynomial.C z) (a := 1) (by
      simp
      have : ‖(1:ℤ_[p]) - z‖ = ‖y - 1‖ := by
        rw [← norm_neg, neg_sub, PadicInt.norm_def]; rfl
      have h2' : ‖(1 + 1:ℤ_[p])‖ = ‖(2:ℚ_[p])‖ := by
        rw [PadicInt.norm_def]; push_cast; norm_num
      rw [this, h2']
      exact hy)
    refine ⟨(w : ℚ_[p]), ?_⟩
    simp at hw
    have : (w:ℚ_[p]) ^ 2 = y := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (sub_eq_zero.mp hw)
      simpa [z] using this
    rw [← this]; ring
  have localStep : ∀ (p : ℕ) [Fact p.Prime] (A a : ℤ) (b : ℕ) (hb : 0 < b) (q : ℚ) (haq : (a : ℚ) = b * q) (ha0 : a ≠ 0) (N : ℕ) (hN : N = (4 * a).natAbs) (hdvd : (p:ℤ) ^ N ∣ A - a),
      IsSquare (((A / b : ℚ) : ℚ_[p]) / (q : ℚ_[p])) := by
    intro p _ A a b hb q haq ha0 N hN hdvd
    have hq' : (q : ℚ_[p]) = (a : ℚ_[p]) / b := by
      have hb' : (b:ℚ) ≠ 0 := by exact_mod_cast hb.ne'
      have : q = a / b := by rw [haq]; field_simp
      rw [this]; push_cast; rfl
    have hb'' : (b:ℚ_[p]) ≠ 0 := by exact_mod_cast hb.ne'
    have ha'' : (a:ℚ_[p]) ≠ 0 := by exact_mod_cast ha0
    have key : ((A / b : ℚ) : ℚ_[p]) / (q : ℚ_[p]) = (A : ℚ_[p]) / a := by
      rw [hq']; push_cast; field_simp
    rw [key]
    apply hensel
    have e1 : (A : ℚ_[p]) / a - 1 = ((A - a : ℤ) : ℚ_[p]) / a := by
      push_cast; field_simp
    rw [e1, norm_div]
    have b1 : ‖((A - a : ℤ) : ℚ_[p])‖ ≤ (p:ℝ) ^ (-(N : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mpr hdvd
    have b2 : (p:ℝ) ^ (-(N : ℤ)) < ‖((4 * a : ℤ) : ℚ_[p])‖ := by
      by_contra hc
      have hc' := not_lt.mp hc
      have h := (Padic.norm_int_le_pow_iff_dvd _ _).mp hc'
      have h4 : 4 * a ≠ 0 := by omega
      have := Int.natAbs_dvd_natAbs.mpr h
      rw [Int.natAbs_pow] at this
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr h4) this
      have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
      have := Nat.lt_pow_self (n := N) hp1
      simp at *
      omega
    have e2 : ‖((4 * a : ℤ) : ℚ_[p])‖ = ‖(2:ℚ_[p])‖ ^ 2 * ‖(a:ℚ_[p])‖ := by
      push_cast
      rw [norm_mul, show (4:ℚ_[p]) = 2 * 2 by norm_num, norm_mul]; ring
    have hapos : 0 < ‖(a:ℚ_[p])‖ := norm_pos_iff.mpr ha''
    rw [div_lt_iff₀ hapos]
    linarith
  set b : ℕ := ∏ p ∈ T, (q p).den with hb
  have hbpos : 0 < b := Finset.prod_pos (fun p _ => (q p).den_pos)
  set a : Nat.Primes → ℤ := fun p => (q p).num * ∏ p' ∈ T.erase p, ((q p').den : ℤ) with ha
  have haq : ∀ p ∈ T, (a p : ℚ) = b * q p := by
    intro p hp
    simp only [ha, hb]
    push_cast
    rw [← Finset.mul_prod_erase T _ hp]
    nth_rw 3 [← Rat.num_div_den (q p)]
    field_simp
  have ha0 : ∀ p ∈ T, a p ≠ 0 := by
    intro p hp h
    have := haq p hp
    rw [h] at this
    simp at this
    rcases this with h | h
    · omega
    · exact hq p hp h
  set N : Nat.Primes → ℕ := fun p => (4 * a p).natAbs with hN
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun p : Nat.Primes => Ideal.span {((p:ℕ):ℤ)}) N
    (by
      intro p _
      have hp : (p:ℕ).Prime := p.2
      rw [Ideal.prime_iff_isPrime (by simpa using hp.ne_zero), Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
      exact Nat.prime_iff_prime_int.mp hp)
    (by
      intro i _ j _ hij h
      apply hij
      have := (Ideal.span_singleton_eq_span_singleton).mp h
      rw [Int.associated_iff] at this
      rcases this with h | h
      · exact Nat.Primes.coe_nat_injective (by exact_mod_cast h)
      · have := i.2.pos; have := j.2.pos; omega)
    (fun p => a p.1)
  set M : ℤ := ∏ p ∈ T, ((p:ℕ):ℤ) ^ (N p) with hM
  have hMpos : 0 < M := Finset.prod_pos (fun p _ => pow_pos (by exact_mod_cast p.2.pos) _)
  set A : ℤ := y + s * M * (|y| + 1) with hA
  have hAdvd : ∀ p ∈ T, ((p:ℕ):ℤ) ^ (N p) ∣ A - a p := by
    intro p hp
    have h1 := hy p hp
    simp only [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    have h2 : ((p:ℕ):ℤ) ^ (N p) ∣ M := Finset.dvd_prod_of_mem _ hp
    have : A - a p = (y - a p) + s * M * (|y| + 1) := by rw [hA]; ring
    rw [this]
    exact dvd_add h1 (Dvd.dvd.mul_right (Dvd.dvd.mul_left h2 _) _)
  have hAsign : A ≠ 0 ∧ (0 < A ↔ s = 1) := by
    rcases hs with h | h
    · subst h
      have : 0 < A := by rw [hA]; nlinarith [le_abs_self y, neg_abs_le y]
      exact ⟨this.ne', by simp [this]⟩
    · subst h
      have : A < 0 := by rw [hA]; nlinarith [le_abs_self y, neg_abs_le y]
      exact ⟨this.ne, by simp [this.not_gt]⟩
  refine ⟨(A : ℚ) / b, ?_, ?_, ?_⟩
  · have : (b:ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
    exact div_ne_zero (by exact_mod_cast hAsign.1) this
  · rw [div_pos_iff_of_pos_right (by exact_mod_cast hbpos)]
    exact_mod_cast hAsign.2
  · intro p hp
    haveI : Fact (p:ℕ).Prime := ⟨p.2⟩
    exact localStep p.1 A (a p) b hbpos (q p) (haq p hp) (ha0 p hp) (N p) rfl (hAdvd p hp)

/-- **A prime in a given residue class, avoiding a finite set** (Dirichlet): for $m \ge 1$ and $r$
coprime to $m$, and any finite set $T$ of primes, there is a prime $\ell \notin T$ with
$\ell \equiv r \pmod m$. -/
@[kb "serre1973" "Ch. VI §4 [unverified]"]
theorem exists_prime_mod_not_mem (m : ℕ) (hm : 0 < m) (r : ℤ) (hr : IsCoprime r m)
    (T : Finset ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ T ∧ (ℓ : ℤ) ≡ r [ZMOD m] := by
  haveI : NeZero m := ⟨by omega⟩
  have hu : IsUnit (r : ZMod m) := by
    obtain ⟨u, v, huv⟩ := hr
    have h := congrArg (fun z : ℤ => (z : ZMod m)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
      add_zero, Int.cast_one] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  obtain ⟨p, hpgt, hp, hpr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu (T.sup id)
  refine ⟨p, hp, ?_, ?_⟩
  · intro hmem
    have := Finset.le_sup (f := id) hmem
    simp at this
    omega
  · rw [← ZMod.intCast_eq_intCast_iff]
    simpa using hpr

/-- **The last place is forced by reciprocity:** let $a, x \in \mathbb{Q}^\times$ and let
$\varepsilon_v \in \{\pm 1\}$ be signs with finitely many $-1$'s and an even number of them. If
$(a, x)_v = \varepsilon_v$ at every place $v \ne w$, then also $(a, x)_w = \varepsilon_w$ (both sides
satisfy Hilbert reciprocity). -/
@[kb "serre1973" "Ch. III §2.2 [unverified]"]
theorem hilbert_eq_at_remaining_place (a x : ℚ) (ha : a ≠ 0) (hx : x ≠ 0) (ε : RatPlace → ℤ)
    (hε : ∀ v, ε v = 1 ∨ ε v = -1) (hfin : {v : RatPlace | ε v = -1}.Finite)
    (heven : Even {v : RatPlace | ε v = -1}.ncard) (w : RatPlace)
    (hagree : ∀ v, v ≠ w → v.hilbert a x = ε v) : w.hilbert a x = ε w := by
  have hpm : w.hilbert a x = 1 ∨ w.hilbert a x = -1 := by
    cases w <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
  obtain ⟨hSfin, hSeven⟩ := hilbert_product_formula a x ha hx
  by_contra hne
  set S := {v : RatPlace | v.hilbert a x = -1} with hS
  set E := {v : RatPlace | ε v = -1} with hE
  have key : ∀ v, v ≠ w → (v ∈ S ↔ v ∈ E) := by
    intro v hv
    simp only [hS, hE, Set.mem_setOf_eq, hagree v hv]
  rcases hpm with h | h <;> rcases hε w with h' | h'
  · exact hne (h.trans h'.symm)
  · -- w ∈ E, w ∉ S
    have hEq : E = insert w S := by
      ext v
      by_cases hv : v = w
      · subst hv; simp [hE, hS, h, h']
      · simp [hv, key v hv]
    have hw : w ∉ S := by simp [hS, h]
    rw [hEq, Set.ncard_insert_of_notMem hw hSfin] at heven
    exact (Nat.not_even_iff_odd.mpr (Even.add_one hSeven)) heven
  · have hEq : S = insert w E := by
      ext v
      by_cases hv : v = w
      · subst hv; simp [hE, hS, h, h']
      · simp [hv, key v hv]
    have hw : w ∉ E := by simp [hE, h']
    rw [hEq, Set.ncard_insert_of_notMem hw hfin] at hSeven
    exact (Nat.not_even_iff_odd.mpr (Even.add_one heven)) hSeven
  · exact hne (h.trans h'.symm)

/-- **Congruent integers differ by a $p$-adic square:** for a prime $p$ and integers $u, w$ not
divisible by $p$, if $u \equiv w \pmod p$ ($p$ odd) or $u \equiv w \pmod 8$ ($p = 2$), then $u / w$
is a square in $\mathbb{Q}_p$. -/
@[kb "serre1973" "Ch. II §3.3 [unverified]"]
theorem isSquare_div_of_modEq (p : ℕ) [Fact p.Prime] (u w : ℤ) (hu : ¬ (p : ℤ) ∣ u)
    (hw : ¬ (p : ℤ) ∣ w) (h : u ≡ w [ZMOD (if p = 2 then 8 else p)]) :
    IsSquare ((u : ℚ_[p]) / (w : ℚ_[p])) := by
  have hensel : ∀ (y : ℚ_[p]), ‖y - 1‖ < ‖(2:ℚ_[p])‖ ^ 2 → IsSquare y := by
    intro y hy
    have h2 : ‖(2:ℚ_[p])‖ ≤ 1 := by
      have := Padic.norm_int_le_one (p := p) 2
      simpa using this
    have hy1 : ‖y‖ ≤ 1 := by
      have : y = (y - 1) + 1 := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le ?_ (by simp))
      nlinarith [norm_nonneg (2:ℚ_[p])]
    set z : ℤ_[p] := ⟨y, hy1⟩
    obtain ⟨w, hw, -⟩ := hensels_lemma (p := p) (R := ℤ_[p]) (F := Polynomial.X ^ 2 - Polynomial.C z) (a := 1) (by
      simp
      have : ‖(1:ℤ_[p]) - z‖ = ‖y - 1‖ := by
        rw [← norm_neg, neg_sub, PadicInt.norm_def]; rfl
      have h2' : ‖(1 + 1:ℤ_[p])‖ = ‖(2:ℚ_[p])‖ := by
        rw [PadicInt.norm_def]; push_cast; norm_num
      rw [this, h2']
      exact hy)
    refine ⟨(w : ℚ_[p]), ?_⟩
    simp at hw
    have : (w:ℚ_[p]) ^ 2 = y := by
      have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (sub_eq_zero.mp hw)
      simpa [z] using this
    rw [← this]; ring
  have hw1 : ‖(w:ℚ_[p])‖ = 1 := by
    have a1 := Padic.norm_int_le_one (p := p) w
    have a2 : ¬ ‖(w:ℚ_[p])‖ < 1 := fun h => hw (Padic.norm_intCast_lt_one_iff.mp h)
    push_neg at a2
    exact le_antisymm a1 a2
  have hw0 : (w:ℚ_[p]) ≠ 0 := by
    intro h0; rw [h0] at hw1; simp at hw1
  apply hensel
  have e1 : (u : ℚ_[p]) / w - 1 = ((u - w : ℤ) : ℚ_[p]) / w := by
    push_cast; field_simp
  rw [e1, norm_div, hw1, div_one]
  have hd : ((if p = 2 then 8 else p : ℕ) : ℤ) ∣ u - w := by
    have := (Int.ModEq.dvd h)
    rw [← dvd_neg, neg_sub] at this
    push_cast; exact this
  by_cases hp : p = 2
  · subst hp
    simp at hd
    have b1 : ‖((u - w : ℤ) : ℚ_[2])‖ ≤ (2:ℝ) ^ (-(3:ℤ)) := by
      have := (Padic.norm_int_le_pow_iff_dvd (p := 2) (u - w) 3).mpr (by norm_num; exact hd)
      exact_mod_cast this
    have b2 : ‖(2:ℚ_[2])‖ = 1/2 := by
      have := Padic.norm_p (p := 2)
      simpa using this
    rw [b2]
    refine lt_of_le_of_lt b1 ?_
    norm_num
  · simp [hp] at hd
    have b1 : ‖((u - w : ℤ) : ℚ_[p])‖ < 1 := Padic.norm_intCast_lt_one_iff.mpr hd
    have b2 : ‖(2:ℚ_[p])‖ = 1 := by
      have a1 := Padic.norm_int_le_one (p := p) 2
      have a2 : ¬ ‖((2:ℤ):ℚ_[p])‖ < 1 := by
        intro h
        have h2 := Padic.norm_intCast_lt_one_iff.mp h
        have : p ∣ 2 := by exact_mod_cast h2
        have hp' := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
        exact hp hp'
      push_neg at a2
      have := le_antisymm a1 a2
      simpa using this
    rw [b2]; simpa using b1

/-! ### The theorem -/

/-- **Rationals with prescribed local Hilbert symbols** (Serre III §2.2, Thm. 4). Let $a_i$
($i \in \iota$, finite) be nonzero rationals and $\varepsilon_{i,v} \in \{\pm 1\}$. If
(1) $\varepsilon_{i,v} = -1$ for only finitely many $(i, v)$, (2) for each $i$ the number of places
with $\varepsilon_{i,v} = -1$ is even, and (3) at each place $v$ some $x_v \in \mathbb{Q}_v^\times$ has
$(a_i, x_v)_v = \varepsilon_{i,v}$ for all $i$, then some $x \in \mathbb{Q}^\times$ has
$(a_i, x)_v = \varepsilon_{i,v}$ for all $i$ and all $v$. -/
@[kb "serre1973" "Ch. III §2.2, Thm. 4 [unverified]"]
theorem exists_rat_prescribed_hilbert {ι : Type} [Fintype ι] (a : ι → ℚ) (ha : ∀ i, a i ≠ 0)
    (ε : ι → RatPlace → ℤ) (hε : ∀ i v, ε i v = 1 ∨ ε i v = -1)
    (h1 : {v : RatPlace | ∃ i, ε i v = -1}.Finite)
    (h2 : ∀ i, Even {v : RatPlace | ε i v = -1}.ncard)
    (h3 : ∀ v : RatPlace, v.atPlace fun K _ _ =>
      ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap ℚ K (a i)) x = ε i v) :
    ∃ x : ℚ, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v := by
  classical
  have hcomm : ∀ (v : RatPlace) (a b : ℚ), v.hilbert a b = v.hilbert b a := by
    intro v a b; cases v <;> simp only [RatPlace.hilbert] <;> exact hilbertSymbol_comm _ _ _
  have hpm : ∀ (v : RatPlace) (a b : ℚ), v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
    intro v a b
    cases v <;> simp only [RatPlace.hilbert, hilbertSymbol] <;> split_ifs <;> simp
  have hmulr : ∀ (v : RatPlace) (a b b' : ℚ), a ≠ 0 → b ≠ 0 → b' ≠ 0 →
      v.hilbert a (b * b') = v.hilbert a b * v.hilbert a b' := by
    intro v a b b' ha hb hb'
    rw [hcomm, HilbertLocal.RatPlace.hilbert_mul_left v b b' a hb hb' ha, hcomm v b, hcomm v b']
  have hsq : ∀ (v : RatPlace) (a c : ℚ), a ≠ 0 → c ≠ 0 → v.hilbert a (c * c) = 1 := by
    intro v a c ha hc
    rw [hmulr v a c c ha hc hc]
    rcases hpm v a c with h | h <;> rw [h] <;> norm_num
  have Lev : ∀ (l : Nat.Primes), (l:ℕ) ≠ 2 → ∀ (b w : ℚ), b ≠ 0 → w ≠ 0 →
      padicValRat l b = 0 → Even (padicValRat l w) → (RatPlace.finite l).hilbert b w = 1 := by
    intro l hl2 b w hb hw hvb hvw
    haveI : Fact (l:ℕ).Prime := ⟨l.2⟩
    obtain ⟨k, hk⟩ := hvw
    set c : ℚ := ((l:ℕ):ℚ) ^ k with hc
    have hc0 : c ≠ 0 := zpow_ne_zero _ (by exact_mod_cast l.2.ne_zero)
    have hvc : padicValRat l c = k := by
      rw [hc, padicValRat.zpow, padicValRat.self l.2.one_lt, mul_one]
    have hw0 : w / (c * c) ≠ 0 := div_ne_zero hw (mul_ne_zero hc0 hc0)
    have hv0 : padicValRat l (w / (c * c)) = 0 := by
      rw [padicValRat.div hw (mul_ne_zero hc0 hc0), padicValRat.mul hc0 hc0, hvc, hk]; ring
    have : w = w / (c * c) * (c * c) := by field_simp
    rw [this, hmulr _ _ _ _ hb hw0 (mul_ne_zero hc0 hc0), hsq _ _ _ hb hc0, mul_one]
    exact HilbertLocal.hilbert_eq_one_of_padicValRat hl2 b _ hb hw0 hvb hv0
  have Lodd : ∀ (l : Nat.Primes), (l:ℕ) ≠ 2 → ∀ (b z z' : ℚ), b ≠ 0 → z ≠ 0 → z' ≠ 0 →
      padicValRat l b = 0 → Odd (padicValRat l z) → Odd (padicValRat l z') →
      (RatPlace.finite l).hilbert b z = (RatPlace.finite l).hilbert b z' := by
    intro l hl2 b z z' hb hz hz' hvb ho ho'
    haveI : Fact (l:ℕ).Prime := ⟨l.2⟩
    have hq : z / z' ≠ 0 := div_ne_zero hz hz'
    have : z = z' * (z / z') := by field_simp
    rw [this, hmulr _ _ _ _ hb hz' hq, Lev l hl2 b _ hb hq hvb, mul_one]
    rw [padicValRat.div hz hz']
    exact Odd.sub_odd ho ho'
  have P : ∀ p : Nat.Primes, ∃ q : ℚ, q ≠ 0 ∧ ∀ i, (RatPlace.finite p).hilbert (a i) q = ε i (RatPlace.finite p) := by
    intro p
    have := h3 (RatPlace.finite p)
    simp only [RatPlace.atPlace] at this
    obtain ⟨x, hx, hxi⟩ := this
    haveI : Fact (p:ℕ).Prime := ⟨p.2⟩
    obtain ⟨q, hq, hsq⟩ := exists_rat_sq_class p x hx
    refine ⟨q, hq, fun i => ?_⟩
    have hq' : (q:ℚ_[p]) ≠ 0 := by exact_mod_cast hq
    show hilbertSymbol ℚ_[p] (a i) q = _
    rw [← hxi i, eq_ratCast]
    exact (hilbertSymbol_eq_of_isSquare_div _ _ _ _ hq' hx hsq).symm
  have Pinf : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ q : ℚ, q ≠ 0 → (0 < q ↔ s = 1) → ∀ i, RatPlace.infinite.hilbert (a i) q = ε i RatPlace.infinite := by
    have := h3 RatPlace.infinite
    simp only [RatPlace.atPlace] at this
    obtain ⟨x, hx, hxi⟩ := this
    refine ⟨if 0 < x then 1 else -1, by split_ifs <;> simp, fun q hq hqs i => ?_⟩
    have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast hq
    show hilbertSymbol ℝ (a i) q = _
    rw [← hxi i, eq_ratCast]
    have hpos : 0 < (q:ℝ) / x := by
      rcases lt_or_gt_of_ne hx with h | h
      · have : ¬ (0 < q) := by rw [hqs]; simp [h.not_gt]
        have : (q:ℝ) < 0 := by exact_mod_cast lt_of_le_of_ne (not_lt.mp this) hq
        exact div_pos_of_neg_of_neg this h
      · have : 0 < q := by rw [hqs]; simp [h]
        have : (0:ℝ) < q := by exact_mod_cast this
        positivity
    exact hilbertSymbol_eq_of_isSquare_div _ _ _ _ hx hq' ⟨Real.sqrt _, (Real.mul_self_sqrt hpos.le).symm⟩
  choose q hq0 hqε using P
  obtain ⟨s, hs, hsε⟩ := Pinf
  set N : ℕ := 2 * ∏ i, ((a i).num.natAbs * (a i).den) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    refine mul_ne_zero two_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ?_ (a i).den_ne_zero)
    exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr (ha i))
  set S : Finset Nat.Primes := N.primeFactors.subtype Nat.Prime with hSdef
  have hmemS : ∀ l : Nat.Primes, l ∈ S ↔ (l:ℕ) ∣ N := by
    intro l
    rw [hSdef]
    refine Finset.mem_subtype.trans ?_
    rw [Nat.mem_primeFactors]
    exact ⟨fun h => h.2.1, fun h => ⟨l.2, h, hN0⟩⟩
  have h2S : ∀ l : Nat.Primes, l ∉ S → (l:ℕ) ≠ 2 := by
    intro l hl h
    apply hl
    rw [hmemS, h, hN]
    exact dvd_mul_right _ _
  have hvS : ∀ l : Nat.Primes, l ∉ S → ∀ i, padicValRat l (a i) = 0 := by
    intro l hl i
    rw [hmemS] at hl
    have hdi : (a i).num.natAbs * (a i).den ∣ N := by
      rw [hN]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
    have h1' : ¬ (l:ℕ) ∣ (a i).num.natAbs := fun h => hl (h.trans ((dvd_mul_right _ _).trans hdi))
    have h2' : ¬ (l:ℕ) ∣ (a i).den := fun h => hl (h.trans ((dvd_mul_left _ _).trans hdi))
    unfold padicValRat padicValInt
    rw [padicValNat.eq_zero_of_not_dvd h1', padicValNat.eq_zero_of_not_dvd h2']
    simp
  obtain ⟨x', hx'0, hx's, hx'sq⟩ := exists_rat_approx_sq_classes S q (fun p _ => hq0 p) s hs
  set B : Set Nat.Primes := {l | ∃ i, ε i (RatPlace.finite l) * (RatPlace.finite l).hilbert (a i) x' = -1} with hB
  have hBfin : B.Finite := by
    have hU : ({v : RatPlace | ∃ i, ε i v = -1} ∪ ⋃ i, {v : RatPlace | v.hilbert (a i) x' = -1}).Finite :=
      h1.union (Set.finite_iUnion fun i => HilbertLocal.hilbert_support_finite _ _ (ha i) hx'0)
    refine (hU.preimage (f := RatPlace.finite) (fun _ _ _ _ h => by cases h; rfl)).subset ?_
    rintro l ⟨i, hi⟩
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
    rcases hε i (RatPlace.finite l) with h | h
    · right; exact ⟨i, by rw [h] at hi; simpa using hi⟩
    · left; exact ⟨i, h⟩
  set T' : Finset Nat.Primes := hBfin.toFinset \ S with hT'
  have hmemT' : ∀ l, l ∈ T' ↔ l ∈ B ∧ l ∉ S := by
    intro l; rw [hT', Finset.mem_sdiff, Set.Finite.mem_toFinset]
  set A : ℕ := ∏ l ∈ T', (l:ℕ) with hA
  set m : ℕ := 8 * ∏ l ∈ S, (l:ℕ) with hm
  have hA0 : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => l.2.ne_zero
  have hm0 : 0 < m := by
    rw [hm]; exact Nat.mul_pos (by norm_num) (Finset.prod_pos fun l _ => l.2.pos)
  have hcop : Nat.Coprime A m := by
    rw [hA]
    refine Nat.Coprime.prod_left fun l hl => ?_
    rw [hmemT'] at hl
    rw [hm]
    refine Nat.Coprime.mul_right ?_ (Nat.Coprime.prod_right fun l' hl' => ?_)
    · rw [show (8:ℕ) = 2^3 by norm_num]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes l.2 Nat.prime_two).mpr (h2S l hl.2))
    · refine (Nat.coprime_primes l.2 l'.2).mpr fun h => hl.2 ?_
      have : l = l' := Subtype.ext h
      rw [this]; exact hl'
  obtain ⟨p, hp, hpT, hpmod⟩ := exists_prime_mod_not_mem m hm0 (A:ℤ)
    (Nat.isCoprime_iff_coprime.mpr hcop) (S.image Subtype.val ∪ T'.image Subtype.val)
  set P : Nat.Primes := ⟨p, hp⟩ with hP
  have hPS : P ∉ S := fun h => hpT (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
  have hPT : P ∉ T' := fun h => hpT (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
  set y : ℚ := ((A * p : ℕ) : ℚ) with hy
  have hy0 : y ≠ 0 := by rw [hy]; exact_mod_cast mul_ne_zero hA0 hp.ne_zero
  have hypos : 0 < y := by rw [hy]; exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero hA0 hp.ne_zero)
  have hx0 : x' * y ≠ 0 := mul_ne_zero hx'0 hy0
  have hndA : ∀ l : Nat.Primes, l ∉ T' → ¬ (l:ℕ) ∣ A := by
    intro l hl hd
    rw [hA] at hd
    obtain ⟨l', hl', hdl⟩ := ((Nat.Prime.prime l.2).dvd_finset_prod_iff _).mp hd
    have : l = l' := Subtype.ext ((Nat.prime_dvd_prime_iff_eq l.2 l'.2).mp hdl)
    exact hl (this ▸ hl')
  have hndp : ∀ l : Nat.Primes, l ≠ P → ¬ (l:ℕ) ∣ p := by
    intro l hl hd
    exact hl (Subtype.ext ((Nat.prime_dvd_prime_iff_eq l.2 hp).mp hd))
  have main : ∀ i v, v ≠ RatPlace.finite P → v.hilbert (a i) (x' * y) = ε i v := by
    intro i v hv
    cases v with
    | infinite =>
      refine hsε _ hx0 ?_ i
      rw [← hx's, mul_pos_iff_of_pos_right hypos]
    | finite l =>
      have hlP : l ≠ P := by rintro rfl; exact hv rfl
      haveI : Fact (l:ℕ).Prime := ⟨l.2⟩
      by_cases hlS : l ∈ S
      · have hlT : l ∉ T' := fun h => ((hmemT' l).mp h).2 hlS
        have hnd : ¬ (l:ℕ) ∣ A * p := fun h => ((Nat.Prime.dvd_mul l.2).mp h).elim (hndA l hlT) (hndp l hlP)
        have hnd2 : ¬ (l:ℕ) ∣ A * A := fun h => ((Nat.Prime.dvd_mul l.2).mp h).elim (hndA l hlT) (hndA l hlT)
        have hmod : ((A * p : ℕ) : ℤ) ≡ ((A * A : ℕ) : ℤ) [ZMOD (if (l:ℕ) = 2 then 8 else (l:ℕ))] := by
          push_cast
          refine (hpmod.mul_left (A:ℤ)).of_dvd ?_
          rw [hm]
          split_ifs
          · push_cast; exact dvd_mul_right _ _
          · push_cast; exact dvd_mul_of_dvd_right (by exact_mod_cast Finset.dvd_prod_of_mem _ hlS) _
        have hsq1 := isSquare_div_of_modEq (l:ℕ) ((A * p : ℕ) : ℤ) ((A * A : ℕ) : ℤ)
          (by exact_mod_cast hnd) (by exact_mod_cast hnd2) hmod
        have hAl : ((A:ℚ_[l])) ≠ 0 := by exact_mod_cast hA0
        have hysq : IsSquare ((y : ℚ_[l])) := by
          have : (y : ℚ_[l]) = (((A * p : ℕ) : ℤ) : ℚ_[l]) / (((A * A : ℕ) : ℤ) : ℚ_[l]) * ((A:ℚ_[l]) * A) := by
            rw [hy]; push_cast; field_simp
          rw [this]; exact hsq1.mul ⟨A, rfl⟩
        have hq' : ((q l : ℚ) : ℚ_[l]) ≠ 0 := by exact_mod_cast hq0 l
        have hxy' : ((x' * y : ℚ) : ℚ_[l]) ≠ 0 := by exact_mod_cast hx0
        have hsq2 : IsSquare (((x' * y : ℚ) : ℚ_[l]) / (q l : ℚ_[l])) := by
          have : ((x' * y : ℚ) : ℚ_[l]) / (q l : ℚ_[l]) = ((x' : ℚ_[l]) / (q l : ℚ_[l])) * (y : ℚ_[l]) := by
            push_cast; ring
          rw [this]; exact (hx'sq l hlS).mul hysq
        rw [← hqε l i]
        exact hilbertSymbol_eq_of_isSquare_div _ _ _ _ hq' hxy' hsq2
      · have hl2 := h2S l hlS
        rw [hmulr _ _ _ _ (ha i) hx'0 hy0]
        by_cases hlT : l ∈ T'
        · obtain ⟨⟨i0, hi0⟩, -⟩ := (hmemT' l).mp hlT
          set z := q l * x' with hz
          have hz0 : z ≠ 0 := mul_ne_zero (hq0 l) hx'0
          have hzi : ∀ j, (RatPlace.finite l).hilbert (a j) z = ε j (RatPlace.finite l) * (RatPlace.finite l).hilbert (a j) x' := by
            intro j; rw [hz, hmulr _ _ _ _ (ha j) (hq0 l) hx'0, hqε l j]
          have hzodd : Odd (padicValRat l z) := by
            by_contra hc
            rw [Int.not_odd_iff_even] at hc
            have := Lev l hl2 (a i0) z (ha i0) hz0 (hvS l hlS i0) hc
            rw [hzi i0, hi0] at this
            norm_num at this
          have hyodd : Odd (padicValRat l y) := by
            have hAe : A = (l:ℕ) * ∏ l' ∈ T'.erase l, (l':ℕ) := (Finset.mul_prod_erase T' _ hlT).symm
            have hA'0 : ∏ l' ∈ T'.erase l, (l':ℕ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ => l.2.ne_zero
            have hnd' : ¬ (l:ℕ) ∣ ∏ l' ∈ T'.erase l, (l':ℕ) := by
              intro hd
              obtain ⟨l', hl', hdl⟩ := ((Nat.Prime.prime l.2).dvd_finset_prod_iff _).mp hd
              have : l = l' := Subtype.ext ((Nat.prime_dvd_prime_iff_eq l.2 l'.2).mp hdl)
              exact (Finset.notMem_erase l T') (this ▸ hl')
            rw [hy, padicValRat.of_nat, hAe, padicValNat.mul (mul_ne_zero l.2.ne_zero hA'0) hp.ne_zero,
              padicValNat.mul l.2.ne_zero hA'0, padicValNat_self, padicValNat.eq_zero_of_not_dvd hnd',
              padicValNat.eq_zero_of_not_dvd (hndp l hlP)]
            simp
          rw [Lodd l hl2 (a i) y z (ha i) hy0 hz0 (hvS l hlS i) hyodd hzodd, hzi i]
          rcases hpm (RatPlace.finite l) (a i) x' with h | h <;> rw [h] <;> ring
        · have hlB : l ∉ B := fun h => hlT ((hmemT' l).mpr ⟨h, hlS⟩)
          have hyv : padicValRat l y = 0 := by
            rw [hy, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd]
            · simp
            · exact fun h => ((Nat.Prime.dvd_mul l.2).mp h).elim (hndA l hlT) (hndp l hlP)
          rw [Lev l hl2 (a i) y (ha i) hy0 (hvS l hlS i) (by rw [hyv]; exact ⟨0, rfl⟩), mul_one]
          have hne : ε i (RatPlace.finite l) * (RatPlace.finite l).hilbert (a i) x' ≠ -1 := fun h => hlB ⟨i, h⟩
          rcases hpm (RatPlace.finite l) (a i) x' with h | h <;> rcases hε i (RatPlace.finite l) with h' | h' <;>
            simp only [h, h'] at hne ⊢ <;> norm_num at hne
  refine ⟨x' * y, hx0, fun i v => ?_⟩
  by_cases hv : v = RatPlace.finite P
  · subst hv
    exact hilbert_eq_at_remaining_place (a i) (x' * y) (ha i) hx0 (ε i) (hε i)
      (h1.subset fun v hv => ⟨i, hv⟩) (h2 i) _ (fun v hv => main i v hv)
  · exact main i v hv

end QuadFormsKB.Prescribed
