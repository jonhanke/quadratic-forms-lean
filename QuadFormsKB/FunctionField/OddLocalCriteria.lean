/-
# Checking the odd local axioms from a finite residue field

Two generic results that reduce `FF.OddLocalAxioms K` (`OddLocal.lean`) to facts about a finite residue
field, for any complete field $K$ with a discrete valuation $v : K \to \mathbb{Z}_{(0)}$:

* `isSquare_of_v_sub_one_lt` (the local square theorem away from $2$, Serre, Ch. II §3.3, Thm. 3;
  O'Meara 63:1): if $K$ is complete, $v(2) = 1$ and some $\pi$ has $v(\pi) = \exp(-1)$, then every $x$
  with $v(x - 1) < 1$ is a square. *Proof:* the Newton map $y \mapsto (e - y^2)/2$, $e = x - 1$, is a
  contraction of the closed ball of radius $|e|$ (the proof of `NFLocal.isSquare_of_valuation_sub_one_lt_nf`,
  which treats the completions of a number field), for the norm $|x| = 2^{\log v(x)}$.
* `oddLocalAxioms_of_residue`: suppose a ring $R$ maps to $K$ by $\rho$ with $v(\rho(r)) \le 1$, and onto a
  finite field $\kappa$ of odd characteristic by $\mu$, with $\mu(r) = 0 \iff v(\rho(r)) < 1$ (so $\kappa$ is
  the residue field and $\rho(R)$ meets every residue class); suppose every unit of $K$ is $\rho(r)\, s^2$
  with $\mu(r) \ne 0$. Then the five axioms hold. The two counting axioms come from the finite field
  ($\kappa^\times / \kappa^{\times 2}$ has order $2$; $x^2 - c y^2 = d$ is solvable in $\kappa$), lifted by
  the local square theorem.

At a place of $\mathbb{F}_q(t)$ one takes $R = \mathbb{F}_q[t]$, $\kappa = \mathbb{F}_q[t]/(P)$ at the finite
place $P$, and $R = \kappa = \mathbb{F}_q$ at infinity (`RatFuncLocal.lean`).

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.OddLocal

open WithZero

namespace QuadFormsKB.FF

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- **The local square theorem away from $2$** for a complete discretely valued field $K$
($v(2) = 1$, a uniformizer exists): if $v(x - 1) < 1$ then $x$ is a square. -/
@[kb "serre1973" "Ch. II §3.3, Thm. 3 [unverified]; omeara1963 §63A, 63:1, p. 159"]
theorem isSquare_of_v_sub_one_lt [CompleteSpace K] (hπ : ∃ π : K, Valued.v π = exp (-1 : ℤ))
    (h2 : Valued.v (2 : K) = 1) (x : K) (hx : Valued.v (x - 1) < 1) : IsSquare x := by
  obtain ⟨π, hπ⟩ := hπ
  letI hR : Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰) :=
    { hom' := (WithZeroMulInt.toNNReal (e := 2) two_ne_zero).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := (WithZeroMulInt.toNNReal_strictMono one_lt_two).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      exists_val_nontrivial := ⟨π, by rw [hπ]; exact exp_ne_zero, by rw [hπ]; decide⟩ }
  letI : NormedField K := Valued.toNormedField K ℤᵐ⁰
  have hn2 : ‖(2 : K)‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr h2
  have h2K : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn2; exact zero_ne_one hn2
  set e : K := x - 1 with he
  have hr : ‖e‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hx
  set r := ‖e‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg _
  let f : K → K := fun y => (e - y ^ 2) / 2
  let s := Metric.closedBall (0 : K) r
  have hmaps : Set.MapsTo f s s := by
    intro y hy
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy ⊢
    simp only [f, norm_div, hn2, div_one]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg, norm_pow]
    have := mul_le_mul hy hy (norm_nonneg y) hr0
    nlinarith
  have hcon : ContractingWith ‖e‖₊ (hmaps.restrict f s s) := by
    refine ⟨hr, LipschitzWith.of_dist_le_mul fun y y' => ?_⟩
    have hy := y.2; have hy' := y'.2
    simp only [s, Metric.mem_closedBall, dist_zero_right] at hy hy'
    change dist (f (y : K)) (f y') ≤ (‖e‖₊ : ℝ) * dist (y : K) y'
    simp only [f, coe_nnnorm]
    rw [dist_eq_norm, dist_eq_norm]
    have : (e - (y : K) ^ 2) / 2 - (e - (y' : K) ^ 2) / 2 = -((y : K) - y') * ((y : K) + y') / 2 := by
      ring
    rw [this, norm_div, norm_mul, norm_neg, hn2, div_one]
    have : ‖(y : K) + y'‖ ≤ r := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hy')
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  obtain ⟨y, -, hfix, -⟩ := ContractingWith.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hmaps hcon (x := 0) (by simp [s, hr0])
    (edist_ne_top _ _)
  refine ⟨1 + y, ?_⟩
  have : f y = y := hfix
  simp only [f] at this
  have h2' : (2 : K) * y = e - y ^ 2 := by
    have h3 : (2 : K) * ((e - y ^ 2) / 2) = 2 * y := by rw [this]
    rw [mul_div_cancel₀ _ h2K] at h3
    exact h3.symm
  rw [he] at h2'
  linear_combination -h2'

/-- **Finite field square classes:** in a finite field of odd characteristic, for $c, d \ne 0$ one of
$c$, $d$, $cd$ is a square. -/
lemma FiniteField.isSquare_or_of_ne_zero {κ : Type*} [Field κ] [Fintype κ] (hκ : ringChar κ ≠ 2)
    {c d : κ} (hc : c ≠ 0) (hd : d ≠ 0) : IsSquare c ∨ IsSquare d ∨ IsSquare (c * d) := by
  classical
  by_cases h1 : IsSquare c
  · exact Or.inl h1
  by_cases h2 : IsSquare d
  · exact Or.inr (Or.inl h2)
  right; right
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hc hd), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr h1, quadraticChar_neg_one_iff_not_isSquare.mpr h2]
  norm_num

/-- **The odd local axioms from a finite residue field.** Let $K$ be complete for a discrete valuation
with a uniformizer. Let $\rho : R \to K$ and $\mu : R \to \kappa$ be ring homomorphisms, $\kappa$ a finite
field of odd characteristic, $\mu$ onto, with $v(\rho(r)) \le 1$ and $\mu(r) = 0 \iff v(\rho(r)) < 1$
for all $r \in R$; and suppose every $y \in K$ with $v(y) \le 1$ is congruent to some $\rho(r)$
($v(y - \rho(r)) < 1$; so $\kappa$ is the residue field of $K$). Then `OddLocalAxioms K` holds. -/
@[kb "serre1973" "Ch. II §3.3 and Ch. III §1.2 (p odd) [unverified]; omeara1963 §63A [unverified]"]
theorem oddLocalAxioms_of_residue [CompleteSpace K] {R : Type*} [CommRing R] {κ : Type*} [Field κ]
    [Finite κ] (hκ : ringChar κ ≠ 2) (ρ : R →+* K) (μ : R →+* κ) (hμ : Function.Surjective μ)
    (hint : ∀ r, Valued.v (ρ r) ≤ 1) (hker : ∀ r, μ r = 0 ↔ Valued.v (ρ r) < 1)
    (hπ : ∃ π : K, Valued.v π = exp (-1 : ℤ))
    (hres : ∀ y : K, Valued.v y ≤ 1 → ∃ r : R, Valued.v (y - ρ r) < 1) :
    OddLocalAxioms K := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  have unit : ∀ r, μ r ≠ 0 → Valued.v (ρ r) = 1 := fun r hr =>
    le_antisymm (hint r) (not_lt.mp fun h => hr ((hker r).mpr h))
  have ne0 : ∀ r, μ r ≠ 0 → ρ r ≠ 0 := fun r hr h0 => by
    have := unit r hr; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have h2μ : μ 2 ≠ 0 := by
    rw [map_ofNat]; exact Ring.two_ne_zero hκ
  have h2 : Valued.v (2 : K) = 1 := by
    have := unit 2 h2μ; rwa [map_ofNat] at this
  have hsq := isSquare_of_v_sub_one_lt hπ h2
  -- every unit is `ρ r · s²` with `μ r ≠ 0`
  have hrep : ∀ a : K, Valued.v a = 1 → ∃ (r : R) (s : K), μ r ≠ 0 ∧ s ≠ 0 ∧ a = ρ r * s ^ 2 := by
    intro a ha
    obtain ⟨r, hr⟩ := hres a ha.le
    have hrv : Valued.v (ρ r) = 1 := by
      have e : ρ r = a - (a - ρ r) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [ha]; exact hr), ha]
    have hμr : μ r ≠ 0 := fun h => by
      have := (hker r).mp h; rw [hrv] at this; exact lt_irrefl _ this
    have hρr := ne0 r hμr
    obtain ⟨z, hz⟩ := hsq (a / ρ r) (by
      have e : a / ρ r - 1 = (a - ρ r) / ρ r := by field_simp
      rw [e, map_div₀, hrv, div_one]; exact hr)
    have ha0 : a ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at ha; exact zero_ne_one ha
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [mul_zero, div_eq_zero_iff] at hz
      rcases hz with h | h
      · exact ha0 h
      · exact hρr h
    refine ⟨r, z, hμr, hz0, ?_⟩
    have : a = a / ρ r * ρ r := by field_simp
    rw [this, hz]; ring
  -- same residue ⇒ the quotient is a square
  have same : ∀ r r', μ r = μ r' → μ r' ≠ 0 → IsSquare (ρ r / ρ r') := by
    intro r r' he hr'
    apply hsq
    have e : ρ r / ρ r' - 1 = ρ (r - r') / ρ r' := by
      rw [map_sub]; field_simp [ne0 r' hr']
    rw [e, map_div₀, unit r' hr', div_one]
    exact (hker _).mp (by rw [map_sub, he, sub_self])
  -- a square residue lifts to a square
  have lift : ∀ r, μ r ≠ 0 → IsSquare (μ r) → IsSquare (ρ r) := by
    rintro r hr ⟨c, hc⟩
    obtain ⟨t, rfl⟩ := hμ c
    have hq := same r (t * t) (by rw [hc, map_mul]) (by rw [map_mul, ← hc]; exact hr)
    have ht : ρ (t * t) ≠ 0 := ne0 _ (by rw [map_mul, ← hc]; exact hr)
    obtain ⟨z, hz⟩ := hq
    refine ⟨z * ρ t, ?_⟩
    have : ρ r = ρ r / ρ (t * t) * ρ (t * t) := by field_simp
    rw [this, hz, map_mul]; ring
  refine ⟨fun h => by rw [h, Valuation.map_zero] at h2; exact zero_ne_one h2, hπ, hsq, ?_, ?_, ?_⟩
  rotate_left 2
  · -- a nonsquare residue lifts to a nonsquare unit
    obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hκ
    have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by ring⟩
    obtain ⟨r, rfl⟩ := hμ c
    refine ⟨ρ r, unit r hc0, ?_⟩
    rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact ne0 r hc0 hs
    have hsv : Valued.v s = 1 := by
      have h1 : Valued.v s * Valued.v s = 1 := by rw [← map_mul, ← hs, unit r hc0]
      have hv0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0
      rw [← exp_log hv0, ← exp_add, exp_eq_one] at h1
      rw [← exp_log hv0, exp_eq_one]; omega
    obtain ⟨r₃, hr₃⟩ := hres s hsv.le
    apply hc
    refine ⟨μ r₃, ?_⟩
    rw [← map_mul, ← sub_eq_zero, ← map_sub, hker, map_sub, map_mul, hs]
    have e : s * s - ρ r₃ * ρ r₃ = (s - ρ r₃) * (s + ρ r₃) := by ring
    rw [e, map_mul]
    have hle : Valued.v (s + ρ r₃) ≤ 1 :=
      (Valued.v.map_add _ _).trans (max_le hsv.le (hint r₃))
    calc Valued.v (s - ρ r₃) * Valued.v (s + ρ r₃) ≤ Valued.v (s - ρ r₃) * 1 :=
          mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hr₃
  · intro a b ha hb
    obtain ⟨r, s, hr, hs, rfl⟩ := hrep a ha
    obtain ⟨r', t, hr', ht, rfl⟩ := hrep b hb
    rcases FiniteField.isSquare_or_of_ne_zero hκ hr hr' with h' | h' | h'
    · exact Or.inl ((lift r hr h').mul ⟨s, by ring⟩)
    · exact Or.inr (Or.inl ((lift r' hr' h').mul ⟨t, by ring⟩))
    · right; right
      have hrr : μ (r * r') ≠ 0 := by rw [map_mul]; exact mul_ne_zero hr hr'
      have := (lift (r * r') hrr (by rw [map_mul]; exact h')).mul (⟨s * t, rfl⟩ : IsSquare ((s * t) * (s * t)))
      convert this using 1
      rw [map_mul]; ring
  · intro a c ha hc
    obtain ⟨r, s, hr, hs, rfl⟩ := hrep a ha
    obtain ⟨r', t, hr', ht, rfl⟩ := hrep c hc
    -- solve `x² - μ r y² = μ r'` in κ
    have hodd : Fintype.card κ % 2 = 1 := by
      have := mt FiniteField.even_card_iff_char_two.mpr hκ
      omega
    have hf : (Polynomial.X ^ 2 : Polynomial κ).degree = 2 := Polynomial.degree_X_pow 2
    have hg : (Polynomial.C (-μ r) * Polynomial.X ^ 2 + Polynomial.C (-μ r')).degree = 2 := by
      rw [Polynomial.degree_add_C, Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hr)]
      · rfl
      rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hr)]; norm_num
    obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hxy
    obtain ⟨x', rfl⟩ := hμ x
    obtain ⟨y', rfl⟩ := hμ y
    set m := x' ^ 2 - r * y' ^ 2 with hm
    have hmμ : μ m = μ r' := by
      rw [hm, map_sub, map_mul, map_pow, map_pow]; linear_combination hxy
    obtain ⟨z, hz⟩ := same m r' hmμ hr'
    have hr'0 := ne0 r' hr'
    have hm0 : ρ m ≠ 0 := ne0 m (by rw [hmμ]; exact hr')
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hz
      rcases hz with h' | h'
      · exact hm0 h'
      · exact hr'0 h'
    refine ⟨ρ x' * t / z, ρ y' * t / (z * s), ?_⟩
    have e : ρ r' = ρ m / (z * z) := by
      rw [← hz]; field_simp
    rw [e, hm, map_sub, map_mul, map_pow, map_pow]
    field_simp

end QuadFormsKB.FF
