/-
# Cassels, Chapter 13: examples

Formalization of examples from Cassels, *Rational Quadratic Forms* (1978), Ch. 13, *Examples*, pp. 328–329: Ex. 1
(proper automorphs of definite binary forms), Ex. 3 (i)–(ii) and Ex. 4 (i)–(ii) (non-representation and
non-equivalence of indefinite binary forms), Ex. 5, Ex. 7 (finiteness of Hermite-reduced binary forms) and Ex. 8
(i)–(ii) (stabilizers of vectors in ternary automorph groups). The "find" exercises (Ex. 2, 3 (iii), 4 (iii), 6, 9, 10,
11, 8 (iii)) ask for computations whose answers the book does not give and are not formalized.

Conventions as in `Ch13/Sec3.lean`: `cform a b c` $= ax^2 + 2bxy + cy^2$ (classically integral), `BinQF.mk A B C`
$= Ax^2 + Bxy + Cy^2$ (integer-valued).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Sec3
import QuadFormsKB.Literature.Cassels.Ch13.Sec11
import QuadFormsKB.Literature.Cassels.Ch13.Sec8
import QuadFormsKB.Literature.Cassels.Ch13.ExamplesTernary
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight

open Matrix

namespace QuadFormsKB.Reduction

/-- Helper: the structure of a proper integral automorph of a primitive form with `a ≠ 0`: there is `k` with
`2 r = a k`, `2 q = -c k`, `s - p = b k` and `(p + s)² + d k² = 4`, where `T = [[p, q], [r, s]]`
(`t = (p+s)/2`, `u = k/2` in Cassels' (3.14)). -/
theorem ex1_struct {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1) (ha0 : a ≠ 0) {T : GL (Fin 2) ℤ}
    (hT : T ∈ Siegel.AutPlus (cform a b c)) :
    ∃ k : ℤ, 2 * T.val 1 0 = a * k ∧ 2 * T.val 0 1 = -c * k ∧ T.val 1 1 - T.val 0 0 = b * k ∧
      (T.val 0 0 + T.val 1 1) ^ 2 + (a * c - b ^ 2) * k ^ 2 = 4 := by
  obtain ⟨r1, r2, r3, hd⟩ := autPlus_rel hT
  have hdvd : a ∣ 2 * T.val 1 0 := by
    refine dvd_of_gcd3 hprim ?_ ?_
    · exact ⟨T.val 1 1 - T.val 0 0, by linarith⟩
    · exact ⟨-2 * T.val 0 1, by linarith⟩
  obtain ⟨k, hk⟩ := hdvd
  have hs : T.val 1 1 - T.val 0 0 = b * k := by
    apply mul_left_cancel₀ ha0
    have : a * (b * k) = b * (a * k) := by ring
    rw [r1, this, ← hk]; ring
  have hq : 2 * T.val 0 1 = -c * k := by
    apply mul_left_cancel₀ ha0
    have : a * (-c * k) = -c * (a * k) := by ring
    rw [this, ← hk]; linear_combination 2 * r2
  refine ⟨k, hk, hq, hs, ?_⟩
  linear_combination (T.val 1 1 - T.val 0 0 + b * k) * hs + 4 * hd + (2 * T.val 1 0) * hq - c * k * hk

/-- Helper: the element of `GL₂(ℤ)` with matrix `[[p, q], [r, s]]` when `ps - qr = 1`. -/
def glOf (p q r s : ℤ) (h : p * s - q * r = 1) : GL (Fin 2) ℤ :=
  Matrix.SpecialLinearGroup.toGL ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h⟩

/-- Helper: the matrix of `glOf`. -/
theorem glOf_val (p q r s : ℤ) (h : p * s - q * r = 1) : (glOf p q r s h).val = !![p, q; r, s] := rfl

/-- Helper: conversely, every `(σ, κ)` with `σ² + dκ² = 4` and the parity conditions comes from a proper automorph. -/
theorem ex1_exists {a b c : ℤ} (σ κ : ℤ) (ht : σ ^ 2 + (a * c - b ^ 2) * κ ^ 2 = 4)
    (h1 : 2 ∣ σ - b * κ) (h2 : 2 ∣ a * κ) (h3 : 2 ∣ c * κ) :
    ∃ T ∈ Siegel.AutPlus (cform a b c), T.val 0 0 + T.val 1 1 = σ ∧ 2 * T.val 1 0 = a * κ := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨r, hr⟩ := h2
  obtain ⟨m, hm⟩ := h3
  have htQ : (σ : ℚ) ^ 2 + (a * c - b ^ 2) * κ ^ 2 = 4 := by exact_mod_cast ht
  have hpQ : (p : ℚ) = (σ - b * κ) / 2 := by
    have : (σ : ℚ) - b * κ = 2 * p := by exact_mod_cast hp
    linarith
  have hrQ : (r : ℚ) = a * κ / 2 := by
    have : (a : ℚ) * κ = 2 * r := by exact_mod_cast hr
    linarith
  have hmQ : (m : ℚ) = c * κ / 2 := by
    have : (c : ℚ) * κ = 2 * m := by exact_mod_cast hm
    linarith
  have hdet : p * (σ - p) - (-m) * r = 1 := by
    have : ((p * (σ - p) - (-m) * r : ℤ) : ℚ) = 1 := by
      push_cast
      rw [hpQ, hrQ, hmQ]
      linear_combination (1 / 4 : ℚ) * htQ
    exact_mod_cast this
  refine ⟨glOf p (-m) r (σ - p) hdet, ?_, by simp [glOf_val], by simp [glOf_val]; linarith⟩
  refine Siegel.mem_autPlus_iff.mpr ⟨fun x => ?_, ?_⟩
  · apply Int.cast_injective (α := ℚ)
    simp only [eval_cform, Matrix.mulVec, dotProduct, Fin.sum_univ_two, glOf_val]
    simp
    rw [hpQ, hrQ, hmQ]
    linear_combination (((a : ℚ) * x 0 ^ 2 + 2 * b * x 0 * x 1 + c * x 1 ^ 2) / 4) * htQ
  · rw [glOf_val, Matrix.det_fin_two_of]; exact hdet

/-- Helper: the number of proper automorphs of a primitive form with `a > 0` is the number of pairs `(σ, κ)`
(`σ = 2t`, `κ = 2u`) with `σ² + dκ² = 4` and the parity conditions. -/
theorem ex1_card {a b c : ℤ} (hprim : Int.gcd a (Int.gcd b c) = 1) (ha : 0 < a) :
    Nat.card (Siegel.AutPlus (cform a b c)) =
      Set.ncard {x : ℤ × ℤ | x.1 ^ 2 + (a * c - b ^ 2) * x.2 ^ 2 = 4 ∧ 2 ∣ x.1 - b * x.2 ∧
        2 ∣ a * x.2 ∧ 2 ∣ c * x.2} := by
  have ha0 : a ≠ 0 := ha.ne'
  let Φ : Siegel.AutPlus (cform a b c) → ℤ × ℤ := fun T => (T.1.val 0 0 + T.1.val 1 1, 2 * T.1.val 1 0 / a)
  have hk : ∀ T : Siegel.AutPlus (cform a b c), ∃ k, 2 * T.1.val 1 0 = a * k ∧ 2 * T.1.val 0 1 = -c * k ∧
      T.1.val 1 1 - T.1.val 0 0 = b * k ∧
      (T.1.val 0 0 + T.1.val 1 1) ^ 2 + (a * c - b ^ 2) * k ^ 2 = 4 ∧ Φ T = (T.1.val 0 0 + T.1.val 1 1, k) := by
    intro T
    obtain ⟨k, h1, h2, h3, h4⟩ := ex1_struct hprim ha0 T.2
    refine ⟨k, h1, h2, h3, h4, ?_⟩
    simp only [Φ]
    rw [h1, Int.mul_ediv_cancel_left _ ha0]
  have hΦ : Function.Injective Φ := by
    intro T T' h
    obtain ⟨k, e1, e2, e3, e4, e5⟩ := hk T
    obtain ⟨k', e1', e2', e3', e4', e5'⟩ := hk T'
    rw [e5, e5'] at h
    obtain ⟨hσ, hkk⟩ := Prod.mk.inj h
    subst hkk
    apply Subtype.ext
    apply Units.ext
    ext i j
    generalize b * k = X at *
    generalize -c * k = Y at *
    generalize a * k = Z at *
    fin_cases i <;> fin_cases j <;> simp <;> omega
  have hrange : Set.range Φ = {x : ℤ × ℤ | x.1 ^ 2 + (a * c - b ^ 2) * x.2 ^ 2 = 4 ∧ 2 ∣ x.1 - b * x.2 ∧
        2 ∣ a * x.2 ∧ 2 ∣ c * x.2} := by
    ext ⟨σ, κ⟩
    constructor
    · rintro ⟨T, hT⟩
      obtain ⟨k, e1, e2, e3, e4, e5⟩ := hk T
      rw [e5] at hT
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hT
      refine ⟨e4, ⟨T.1.val 0 0, ?_⟩, ⟨T.1.val 1 0, ?_⟩, ⟨-T.1.val 0 1, ?_⟩⟩
      · show T.1.val 0 0 + T.1.val 1 1 - b * k = _
        generalize b * k = X at *; omega
      · show a * k = _
        omega
      · show c * k = _
        linarith
    · rintro ⟨ht, h1, h2, h3⟩
      obtain ⟨T, hT, e1, e2⟩ := ex1_exists σ κ ht h1 h2 h3
      refine ⟨⟨T, hT⟩, ?_⟩
      simp only [Φ]
      rw [e1, e2, Int.mul_ediv_cancel_left _ ha0]
  rw [← Nat.card_coe_set_eq, ← hrange, Nat.card_range_of_injective hΦ]

/-- **Example 1** (Cassels, Ch. 13, p. 328): let $f = ax^2 + 2bxy + cy^2$ be positive definite ($a > 0$, $d = ac - b^2 > 0$),
primitive and classically integral. Its only proper integral automorphs are $\pm I$ except when $d = 1$ or $3$. In the
exceptional cases: for $d = 1$ there are $4$ proper automorphs; for $d = 3$ there are $6$ if $f$ is improperly
primitive ($a$, $c$ even) and $2$ otherwise. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 1, p. 328"]
theorem example_1 {a b c : ℤ} (ha : 0 < a) (hd : 0 < a * c - b ^ 2) (hprim : Int.gcd a (Int.gcd b c) = 1) :
    (a * c - b ^ 2 ≠ 1 → a * c - b ^ 2 ≠ 3 → ∀ T ∈ Siegel.AutPlus (cform a b c), T = 1 ∨ T = -1) ∧
    (a * c - b ^ 2 = 1 → Nat.card (Siegel.AutPlus (cform a b c)) = 4) ∧
    (a * c - b ^ 2 = 3 → Even a → Even c → Nat.card (Siegel.AutPlus (cform a b c)) = 6) ∧
    (a * c - b ^ 2 = 3 → ¬ (Even a ∧ Even c) → Nat.card (Siegel.AutPlus (cform a b c)) = 2) := by
  have ha0 : a ≠ 0 := ha.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hd1 hd3 T hT
    obtain ⟨k, e1, e2, e3, e4⟩ := ex1_struct hprim ha0 hT
    have hk0 : k = 0 := by
      by_contra hk
      have hk2 : 1 ≤ k ^ 2 := by have := sq_pos_of_ne_zero hk; omega
      obtain ⟨d, hdd⟩ : ∃ d, d = a * c - b ^ 2 := ⟨_, rfl⟩
      rw [← hdd] at hd hd1 hd3 e4
      have hd4 : d ≤ 4 := by nlinarith [sq_nonneg (T.val 0 0 + T.val 1 1)]
      have hk1 : k = 1 ∨ k = -1 := by
        have : k ^ 2 ≤ 2 := by
          have hd2 : 2 ≤ d := by omega
          nlinarith [sq_nonneg (T.val 0 0 + T.val 1 1), mul_nonneg (sub_nonneg.mpr hd2) (sq_nonneg k)]
        have hlo : -1 ≤ k := by
          by_contra h
          have : k ≤ -2 := by omega
          nlinarith
        have hhi : k ≤ 1 := by
          by_contra h
          have : 2 ≤ k := by omega
          nlinarith
        omega
      have hk1' : k ^ 2 = 1 := by rcases hk1 with rfl | rfl <;> norm_num
      rw [hk1'] at e4
      have hσ : (T.val 0 0 + T.val 1 1) ^ 2 = 4 - d := by linarith
      have hd24 : d = 2 ∨ d = 4 := by omega
      rcases hd24 with rfl | rfl
      · have hlo : -1 ≤ T.val 0 0 + T.val 1 1 := by nlinarith
        have hhi : T.val 0 0 + T.val 1 1 ≤ 1 := by nlinarith
        generalize T.val 0 0 + T.val 1 1 = σ at *
        interval_cases σ <;> omega
      · have : T.val 0 0 + T.val 1 1 = 0 := by nlinarith [sq_nonneg (T.val 0 0 + T.val 1 1)]
        have h2 : (2 : ℤ) ∣ ((Int.gcd a (Int.gcd b c) : ℕ) : ℤ) := by
          apply Int.dvd_coe_gcd
          · rcases hk1 with rfl | rfl <;> omega
          · apply Int.dvd_coe_gcd
            · rcases hk1 with rfl | rfl <;> omega
            · rcases hk1 with rfl | rfl <;> omega
        rw [hprim] at h2
        omega
    subst hk0
    have hr : T.val 1 0 = 0 := by omega
    have hq : T.val 0 1 = 0 := by omega
    have hs : T.val 1 1 = T.val 0 0 := by omega
    have hdet := (autPlus_rel hT).2.2.2
    rw [hr, hq, hs] at hdet
    have hp : T.val 0 0 = 1 ∨ T.val 0 0 = -1 := by
      have : (T.val 0 0 - 1) * (T.val 0 0 + 1) = 0 := by linear_combination hdet
      rcases mul_eq_zero.mp this with h | h
      · left; omega
      · right; omega
    rcases hp with hp | hp
    · left
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp, hr, hq, hs]
    · right
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hp, hr, hq, hs]
  · intro hd1
    rw [ex1_card hprim ha, hd1]
    have : {x : ℤ × ℤ | x.1 ^ 2 + 1 * x.2 ^ 2 = 4 ∧ 2 ∣ x.1 - b * x.2 ∧ 2 ∣ a * x.2 ∧ 2 ∣ c * x.2} =
        ↑({(2, 0), (-2, 0), (0, 2), (0, -2)} : Finset (ℤ × ℤ)) := by
      ext ⟨σ, κ⟩
      simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨h, -, -, -⟩
        have h1 : -2 ≤ σ := by nlinarith
        have h2 : σ ≤ 2 := by nlinarith
        have h3 : -2 ≤ κ := by nlinarith
        have h4 : κ ≤ 2 := by nlinarith
        interval_cases σ <;> interval_cases κ <;> omega
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> omega
    rw [this, Set.ncard_coe_finset]
    rfl
  · intro hd3 hae hce
    rw [ex1_card hprim ha, hd3]
    have hbo : b % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one b with h | h
      · exfalso
        obtain ⟨a', ha'⟩ := hae
        obtain ⟨c', hc'⟩ := hce
        subst ha' hc'
        have : b = 2 * (b / 2) := by omega
        rw [this] at hd3
        have e1 : (a' + a') * (c' + c') = 4 * (a' * c') := by ring
        have e2 : (2 * (b / 2)) ^ 2 = 4 * (b / 2) ^ 2 := by ring
        omega
      · exact h
    have : {x : ℤ × ℤ | x.1 ^ 2 + 3 * x.2 ^ 2 = 4 ∧ 2 ∣ x.1 - b * x.2 ∧ 2 ∣ a * x.2 ∧ 2 ∣ c * x.2} =
        ↑({(2, 0), (-2, 0), (1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℤ × ℤ)) := by
      ext ⟨σ, κ⟩
      simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      have hae' : a % 2 = 0 := Int.even_iff.mp hae
      have hce' : c % 2 = 0 := Int.even_iff.mp hce
      constructor
      · rintro ⟨h, -, -, -⟩
        have h1 : -2 ≤ σ := by nlinarith
        have h2 : σ ≤ 2 := by nlinarith
        have h3 : -1 ≤ κ := by nlinarith
        have h4 : κ ≤ 1 := by nlinarith
        interval_cases σ <;> interval_cases κ <;> omega
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
          refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> omega
    rw [this, Set.ncard_coe_finset]
    rfl
  · intro hd3 hnot
    rw [ex1_card hprim ha, hd3]
    have hnot' : ¬ (a % 2 = 0 ∧ c % 2 = 0) := fun h => hnot ⟨Int.even_iff.mpr h.1, Int.even_iff.mpr h.2⟩
    have : {x : ℤ × ℤ | x.1 ^ 2 + 3 * x.2 ^ 2 = 4 ∧ 2 ∣ x.1 - b * x.2 ∧ 2 ∣ a * x.2 ∧ 2 ∣ c * x.2} =
        ↑({(2, 0), (-2, 0)} : Finset (ℤ × ℤ)) := by
      ext ⟨σ, κ⟩
      simp only [Set.mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨h, -, h2, h3⟩
        have h1 : -2 ≤ σ := by nlinarith
        have h2' : σ ≤ 2 := by nlinarith
        have h3' : -1 ≤ κ := by nlinarith
        have h4 : κ ≤ 1 := by nlinarith
        interval_cases σ <;> interval_cases κ <;> omega
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> refine ⟨by norm_num, ?_, ?_, ?_⟩ <;> omega
    rw [this, Set.ncard_coe_finset]
    rfl

/-- Helper: descent for `a² - 79 b² = 5` along the unit `80 + 9√79` of norm `1`. -/
theorem no_sol_79_aux : ∀ n : ℕ, ∀ a b : ℤ, b.natAbs = n → a ^ 2 - 79 * b ^ 2 ≠ 5 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn hab
    have hA : |a| ^ 2 - 79 * |b| ^ 2 = 5 := by rw [sq_abs, sq_abs]; exact hab
    have hA0 : 0 ≤ |a| := abs_nonneg a
    have hB0 : 0 ≤ |b| := abs_nonneg b
    have hBn : |b|.natAbs = n := by rw [Int.natAbs_abs]; exact hn
    clear hab hn
    generalize |a| = A at *
    generalize |b| = B at *
    by_cases hB : B < 21
    · have hAle : A < 179 := by nlinarith
      have key : ∀ B < 21, ∀ A < 179, A * A ≠ 79 * B * B + 5 := by decide +kernel
      lift A to ℕ using hA0
      lift B to ℕ using hB0
      have := key B (by exact_mod_cast hB) A (by exact_mod_cast hAle)
      apply this
      have h2 : ((A * A : ℕ) : ℤ) = ((79 * B * B + 5 : ℕ) : ℤ) := by push_cast; nlinarith
      exact_mod_cast h2
    · rw [not_lt] at hB
      have h1 : 80 * B - 9 * A < B := by
        by_contra hc; rw [not_lt] at hc; nlinarith
      have h2 : 0 ≤ 80 * B - 9 * A := by
        by_contra hc; rw [not_le] at hc; nlinarith
      have hlt : (80 * B - 9 * A).natAbs < n := by omega
      refine ih _ hlt (80 * A - 711 * B) (80 * B - 9 * A) rfl ?_
      linear_combination hA

/-- **Example 3 (i)** (Cassels, Ch. 13, p. 329): $5$ is not represented integrally by $x^2 - 79y^2$. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 3 (i), p. 329"]
theorem example_3_i : ¬ ∃ x y : ℤ, x ^ 2 - 79 * y ^ 2 = 5 := by
  rintro ⟨a, b, h⟩
  exact no_sol_79_aux _ a b rfl h

/-- **Example 3 (ii)** (Cassels, Ch. 13, p. 329): $x^2 - 79y^2$ and $5x^2 + 4xy - 15y^2$ are not integrally equivalent
(both have determinant $-79$; Cassels adds that they are in the same genus, not formalized here). -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 3 (ii), p. 329 (not equivalent)"]
theorem example_3_ii : ¬ Siegel.IntEquiv (cform 1 0 (-79)) (cform 5 2 (-15)) := by
  rintro ⟨g, hg⟩
  have h := hg ![1, 0]
  rw [eval_cform, eval_cform] at h
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  exact example_3_i ⟨g.val 0 0, g.val 1 0, by linarith⟩

/-- Helper: value of `BinQF.mk A B C`. -/
theorem eval_binqf_mk (A B C : ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval (BinQF.mk A B C) x = A * x 0 ^ 2 + B * x 0 * x 1 + C * x 1 ^ 2 := by
  simp [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, BinQF.mk, QuadForm.ofUpper]
  ring

/-- Helper: descent for `x² + xy - 36y² = ±4` with `(x, y)` primitive (Bezout form), along the unit `11 + 2ω`
of norm `-1` of the order of discriminant `145`. -/
theorem no_sol_145_aux : ∀ n : ℕ, ∀ x y s : ℤ, y.natAbs = n → (s = 4 ∨ s = -4) →
    (∃ p q : ℤ, p * x + q * y = 1) → x ^ 2 + x * y - 36 * y ^ 2 ≠ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y s hn hs ⟨p, q, hpq⟩ h
    -- reduce to y ≥ 0
    obtain ⟨x, y, hy0, hn, p, q, hpq, h⟩ : ∃ x y : ℤ, 0 ≤ y ∧ y.natAbs = n ∧ ∃ p q : ℤ, p * x + q * y = 1 ∧
        x ^ 2 + x * y - 36 * y ^ 2 = s := by
      rcases le_total 0 y with hy | hy
      · exact ⟨x, y, hy, hn, p, q, hpq, h⟩
      · exact ⟨-x, -y, by omega, by rw [Int.natAbs_neg]; exact hn, -p, -q, by linarith, by linear_combination h⟩
    rcases hy0.eq_or_lt with h0 | hpos
    · subst h0
      have hx2 : x ^ 2 = s := by linarith
      rcases hs with rfl | rfl
      · have : (x - 2) * (x + 2) = 0 := by linear_combination hx2
        rcases mul_eq_zero.mp this with h1 | h1
        · have : x = 2 := by omega
          subst this; omega
        · have : x = -2 := by omega
          subst this; omega
      · nlinarith [sq_nonneg x]
    · have hu2 : (2 * x + y) ^ 2 = 145 * y ^ 2 + 4 * s := by linear_combination 4 * h
      have hs' : -4 ≤ s := by rcases hs with rfl | rfl <;> norm_num
      have hs'' : s ≤ 4 := by rcases hs with rfl | rfl <;> norm_num
      have hy1 : 1 ≤ y := hpos
      rcases le_or_gt 0 (2 * x + y) with hu | hu
      · have hu0 : 0 < 2 * x + y := by
          rcases hu.eq_or_lt with h0 | h0
          · rw [← h0] at hu2; nlinarith
          · exact h0
        have h1 : 2 * x + y < 13 * y := by
          by_contra hc; rw [not_lt] at hc; nlinarith
        have h2 : 11 * y < 2 * x + y := by
          by_contra hc; rw [not_lt] at hc; nlinarith
        have hlt : (2 * x - 11 * y).natAbs < n := by omega
        refine ih _ hlt (-13 * x + 72 * y) (2 * x - 11 * y) (-s) rfl
          (by rcases hs with rfl | rfl <;> simp) ⟨11 * p + 2 * q, 72 * p + 13 * q, by linear_combination hpq⟩ ?_
        linear_combination (-1 : ℤ) * h
      · have h1 : -13 * y < 2 * x + y := by
          by_contra hc; rw [not_lt] at hc; nlinarith
        have h2 : 2 * x + y < -11 * y := by
          by_contra hc; rw [not_lt] at hc; nlinarith
        have hlt : (2 * x + 13 * y).natAbs < n := by omega
        refine ih _ hlt (11 * x + 72 * y) (2 * x + 13 * y) (-s) rfl
          (by rcases hs with rfl | rfl <;> simp) ⟨-13 * p + 2 * q, 72 * p - 11 * q, by linear_combination hpq⟩ ?_
        linear_combination (-1 : ℤ) * h

/-- **Example 4 (i)** (Cassels, Ch. 13, p. 329): $4$ is not represented primitively by $x^2 + xy - 36y^2$. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 4 (i), p. 329"]
theorem example_4_i : ¬ ∃ x y : ℤ, Int.gcd x y = 1 ∧ x ^ 2 + x * y - 36 * y ^ 2 = 4 := by
  rintro ⟨x, y, hg, h⟩
  refine no_sol_145_aux _ x y 4 rfl (Or.inl rfl) ⟨Int.gcdA x y, Int.gcdB x y, ?_⟩ h
  have := Int.gcd_eq_gcd_ab x y
  rw [hg] at this
  push_cast at this
  linarith

/-- **Example 4 (ii)** (Cassels, Ch. 13, p. 329): $x^2 + xy - 36y^2$ and $4x^2 + xy - 9y^2$ (both of discriminant $145$)
are not integrally equivalent. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 4 (ii), p. 329"]
theorem example_4_ii : ¬ Siegel.IntEquiv (BinQF.mk 1 1 (-36)) (BinQF.mk 4 1 (-9)) := by
  rintro ⟨g, hg⟩
  have h := hg ![1, 0]
  rw [eval_binqf_mk, eval_binqf_mk] at h
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  have hdet : IsUnit (g.val.det) := Matrix.isUnits_det_units g
  rw [Matrix.det_fin_two, Int.isUnit_iff] at hdet
  refine no_sol_145_aux _ (g.val 0 0) (g.val 1 0) 4 rfl (Or.inl rfl) ?_ (by linarith)
  rcases hdet with hd | hd
  · exact ⟨g.val 1 1, -g.val 0 1, by linarith⟩
  · exact ⟨-g.val 1 1, g.val 0 1, by linarith⟩

/-- Helper: descent for `x² + z² - (k+2)xz = -m` in positive integers (`0 < m < k`). -/
theorem ex5_aux {k m : ℤ} (hk : 0 < k) (hm0 : 0 < m) (hmk : m < k) :
    ∀ n : ℕ, ∀ x z : ℤ, 0 < x → 0 < z → (x + z).natAbs = n → x ^ 2 + z ^ 2 - (k + 2) * x * z ≠ -m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key : ∀ x z : ℤ, 0 < x → x ≤ z → (x + z).natAbs = n →
        x ^ 2 + z ^ 2 - (k + 2) * x * z = -m → False := by
      intro x z hx hxz hn h
      have hz : 0 < z := by omega
      have hzz : z * ((k + 2) * x - z) = x ^ 2 + m := by linear_combination (-1 : ℤ) * h
      have hz' : 0 < (k + 2) * x - z := by
        by_contra hc; rw [not_lt] at hc
        nlinarith [mul_nonneg hz.le (neg_nonneg.mpr hc), sq_nonneg x]
      by_cases hlt : (k + 2) * x - z < z
      · have : (x + ((k + 2) * x - z)).natAbs < n := by omega
        exact ih _ this x ((k + 2) * x - z) hx hz' rfl (by linear_combination h) |>.elim
      · rw [not_lt] at hlt
        have hzz2 : z ^ 2 ≤ x ^ 2 + m := by nlinarith
        rcases hxz.eq_or_lt with h0 | hj
        · subst h0
          nlinarith
        · obtain ⟨j, hjdef⟩ : ∃ j, j = z - x := ⟨_, rfl⟩
          have hj1 : 1 ≤ j := by omega
          have hzj : z = x + j := by omega
          subst hzj
          have e1 : 2 * x * j + j ^ 2 ≤ m := by nlinarith
          have e2 : k * x * (x + j) = j ^ 2 + m := by linear_combination (-1 : ℤ) * h
          have e3 : 2 * k ≤ k * x * (x + j) := by
            have : 2 ≤ x * (x + j) := by nlinarith
            nlinarith
          nlinarith
    intro x z hx hz hn h
    rcases le_total x z with hxz | hzx
    · exact key x z hx hxz hn h
    · exact key z x hz hzx (by rw [add_comm]; exact hn) (by linear_combination h)

/-- **Example 5** (Cassels, Ch. 13, p. 329): for a positive integer $k$, $kx^2 + kxy - y^2$ does not represent any
integer $m$ with $0 < m < k$. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 5, p. 329"]
theorem example_5 {k m : ℤ} (hk : 0 < k) (hm0 : 0 < m) (hmk : m < k) :
    ¬ ∃ x y : ℤ, k * x ^ 2 + k * x * y - y ^ 2 = m := by
  rintro ⟨x, y, h⟩
  have h1 : x ^ 2 + (x + y) ^ 2 - (k + 2) * x * (x + y) = -m := by linear_combination (-1 : ℤ) * h
  have hpos : 0 < x * (x + y) := by
    by_contra hc; rw [not_lt] at hc
    nlinarith [sq_nonneg y, mul_nonneg hk.le (neg_nonneg.mpr hc)]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hz : x + y < 0 := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    exact ex5_aux hk hm0 hmk _ (-x) (-(x + y)) (by omega) (by omega) rfl (by linear_combination h1)
  · subst hx; simp at hpos
  · have hz : 0 < x + y := by
      by_contra hc; rw [not_lt] at hc; nlinarith
    exact ex5_aux hk hm0 hmk _ x (x + y) hx hz rfl h1

/-- **Example 7** (Cassels, Ch. 13, p. 329): there are only finitely many Hermite-reduced integral forms
$ax^2 + 2bxy + cy^2$ with given determinant $d \ne 0$ (Cassels asks for a proof "from first principles"; here it is the
case $n = 2$ of Theorem 11.1, `finite_isMajorantReduced_classical`). -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 7, p. 329"]
theorem example_7 {d : ℤ} (hd : d ≠ 0) :
    {p : ℤ × ℤ × ℤ | p.1 * p.2.2 - p.2.1 ^ 2 = d ∧
      IsMajorantReduced (realMat (cform p.1 p.2.1 p.2.2))}.Finite := by
  have hfin := finite_isMajorantReduced_classical 2 (d : ℝ) (by exact_mod_cast hd)
  have hinj : Function.Injective (fun p : ℤ × ℤ × ℤ => cform p.1 p.2.1 p.2.2) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    have h1 := congrArg BinQF.a h
    have h2 := congrArg BinQF.b h
    have h3 := congrArg BinQF.c h
    simp [cform, BinQF.a, BinQF.b, BinQF.c, BinQF.mk, QuadForm.ofUpper] at h1 h2 h3
    simp [h1, h3, h2]
  refine (hfin.preimage hinj.injOn).subset ?_
  rintro ⟨a, b, c⟩ ⟨hdet, hred⟩
  refine ⟨?_, ?_, hred⟩
  · refine ⟨!![a, b; b, c], ?_, fun x => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · rw [eval_cform]
      simp [gramForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  · show (realMat (cform a b c)).det = d
    rw [realMat_cform, Matrix.det_fin_two_of]
    have : ((a * c - b ^ 2 : ℤ) : ℝ) = d := by exact_mod_cast hdet
    push_cast at this
    linarith

/-- **Example 8 (i)–(ii)** (Cassels, Ch. 13, p. 329): let $f$ be a classically integral ternary form, real-equivalent to
$X^2 + Y^2 - Z^2$, let $\vec{b} \in \mathbb{Z}^3$ and let $G$ consist of the integral automorphs $T$ of $f$ with
$T\vec{b} = \vec{b}$. (i) If $f(\vec{b}) < 0$ then $G$ is finite. (ii) If $f$ is anisotropic and $f(\vec{b}) > 0$ then $G$
is infinite. -/
@[kb "cassels1978" "Ch. 13, Examples, Ex. 8 (i)–(ii), p. 329"]
theorem example_8 {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : A.IsSymm) {L : Matrix (Fin 3) (Fin 3) ℝ}
    (hL : IsUnit L.det) (hF : A.map (Int.cast : ℤ → ℝ) = Lᵀ * diagonal ![1, 1, -1] * L) (b : Fin 3 → ℤ) :
    (b ⬝ᵥ (A *ᵥ b) < 0 → {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Finite) ∧
    (¬ (Siegel.ofGram A).IsotropicIn ℚ → 0 < b ⬝ᵥ (A *ᵥ b) →
      {T | T ∈ Siegel.Aut (Siegel.ofGram A) ∧ T.val *ᵥ b = b}.Infinite) :=
  ex8_main hA hL hF b

end QuadFormsKB.Reduction
