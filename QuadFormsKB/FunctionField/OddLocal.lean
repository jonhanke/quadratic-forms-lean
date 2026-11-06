/-
# The Hilbert symbol is multiplicative over an odd local field (abstract form)

Let $K$ be a field with a discrete valuation $v : K \to \mathbb{Z}_{(0)}$ (Mathlib's `Valued K ℤᵐ⁰`).
`OddLocalAxioms K` collects six local facts that hold at every place of a global field whose residue
field is finite of odd characteristic (number field places above an odd prime, and every place of
$\mathbb{F}_q(t)$, $q$ odd):

* `two_ne_zero`: $2 \ne 0$ in $K$;
* `exists_uniformizer`: some $\pi \in K$ has $v(\pi) = \exp(-1)$;
* `isSquare_of_near_one`: if $v(x - 1) < 1$ then $x$ is a square (the local square theorem; Hensel);
* `unit_sq_classes`: for units $a, b$ ($v(a) = v(b) = 1$), one of $a$, $b$, $ab$ is a square
  (the unit square classes form a group of order $\le 2$);
* `unit_norm`: for units $a, c$ there are $x, y \in K$ with $x^2 - a y^2 = c$ (every unit is a norm from
  $K(\sqrt a)$; over the finite residue field this is the pigeonhole count);
* `exists_nonsquare_unit`: some unit is not a square (the residue field has a nonsquare; used only for
  the local classification, `OddLocalClassification.lean`, not for multiplicativity).

**Theorem** (`OddLocalAxioms.hilbertSymbol_mul_right`, `hilbertSymbol_mul_left`): under these axioms the
Hilbert symbol is multiplicative in each argument. This is Serre, Ch. III §1.2, Thm. 2 (there for
$\mathbb{Q}_p$, $p$ odd, from the explicit formula) and O'Meara 63:11 (bimultiplicativity, for a
non-dyadic local field). *Proof* (following the source's explicit computation, organized by square
classes of the first argument $a$): write each $b \ne 0$ as $b = \pi^k w$ with $v(w) = 1$.
If $a$ is a square, $(a, b) = 1$. If $a$ is a nonsquare unit, $(a, b) = (-1)^k$. If $v(a)$ is odd, $a$ is
a square times a uniformizer $\pi'$, and $(\pi', b) = 1$ iff $(-1)^k w$ is a square (expanding $b$ in
$\pi'$). In each case the right side is multiplicative in $b$.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Defs.Hilbert
import QuadFormsKB.Equiv.Hilbert

open WithZero

namespace QuadFormsKB.FF

/-- **Local axioms of an odd local field** (a condition on a valued field $K$, proved at the completions
of $\mathbb{F}_q(t)$ in `RatFuncLocal.lean`): $2 \ne 0$; a uniformizer exists; elements with
$v(x - 1) < 1$ are squares; among units $a, b$ one of $a, b, ab$ is a square; every unit $c$ has the form
$x^2 - a y^2$ for every unit $a$; some unit is not a square. -/
structure OddLocalAxioms (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Prop where
  two_ne_zero : (2 : K) ≠ 0
  exists_uniformizer : ∃ π : K, Valued.v π = exp (-1 : ℤ)
  isSquare_of_near_one : ∀ x : K, Valued.v (x - 1) < 1 → IsSquare x
  unit_sq_classes : ∀ a b : K, Valued.v a = 1 → Valued.v b = 1 →
    IsSquare a ∨ IsSquare b ∨ IsSquare (a * b)
  unit_norm : ∀ a c : K, Valued.v a = 1 → Valued.v c = 1 → ∃ x y : K, x ^ 2 - a * y ^ 2 = c
  exists_nonsquare_unit : ∃ u : K, Valued.v u = 1 ∧ ¬ IsSquare u

namespace OddLocalAxioms

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-! ### Generic Hilbert symbol facts (any field) -/

lemma hs_pm (a b : K) : hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

lemma hs_one_iff (a b : K) :
    hilbertSymbol K a b = 1 ↔ ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

lemma hs_eq_of_iff {a b c : K}
    (h : hilbertSymbol K a (b * c) = 1 ↔ (hilbertSymbol K a b = 1 ↔ hilbertSymbol K a c = 1)) :
    hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c := by
  rcases hs_pm a (b * c) with h1 | h1 <;> rcases hs_pm a b with h2 | h2 <;>
    rcases hs_pm a c with h3 | h3 <;> simp only [h1, h2, h3] at h ⊢ <;> simp_all

/-- Square factors in the second argument do not matter. -/
lemma hs_mul_sq_right (a b s : K) (hs : s ≠ 0) :
    hilbertSymbol K a (b * s ^ 2) = hilbertSymbol K a b := by
  have key : hilbertSymbol K a (b * s ^ 2) = 1 ↔ hilbertSymbol K a b = 1 := by
    rw [hs_one_iff, hs_one_iff]
    constructor
    · rintro ⟨x, y, z, hne, he⟩
      refine ⟨x, y * s, z, ?_, by rw [he]; ring⟩
      intro h0
      apply hne
      simp only [Prod.mk_eq_zero, mul_eq_zero] at h0 ⊢
      tauto
    · rintro ⟨x, y, z, hne, he⟩
      refine ⟨x, y / s, z, ?_, by rw [he]; field_simp⟩
      intro h0
      apply hne
      simp only [Prod.mk_eq_zero, div_eq_zero_iff] at h0 ⊢
      tauto
  rcases hs_pm a (b * s ^ 2) with h1 | h1 <;> rcases hs_pm a b with h2 | h2 <;>
    simp only [h1, h2] at key ⊢ <;> simp_all

/-- Square factors in the first argument do not matter. -/
lemma hs_mul_sq_left (a b s : K) (hs : s ≠ 0) :
    hilbertSymbol K (a * s ^ 2) b = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm, hs_mul_sq_right _ _ _ hs, hilbertSymbol_comm]

/-- A norm $x^2 - a y^2$ has symbol $1$. -/
lemma hs_of_norm {a b x y : K} (h : x ^ 2 - a * y ^ 2 = b) : hilbertSymbol K a b = 1 := by
  rw [hs_one_iff]
  exact ⟨y, 1, x, by simp, by rw [← h]; ring⟩

/-- A square first argument gives symbol $1$. -/
lemma hs_of_isSquare {a : K} (ha : IsSquare a) (b : K) : hilbertSymbol K a b = 1 := by
  obtain ⟨s, rfl⟩ := ha
  rw [hs_one_iff]
  exact ⟨1, 0, s, by simp, by ring⟩

/-- For a nonsquare $a$, symbol $1$ means $b$ is a norm $x^2 - a y^2$. -/
lemma norm_of_hs {a b : K} (ha : ¬ IsSquare a) (h : hilbertSymbol K a b = 1) :
    ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  rw [hs_one_iff] at h
  obtain ⟨x, y, z, hne, he⟩ := h
  by_cases hy : y = 0
  · subst hy
    exfalso
    by_cases hx : x = 0
    · subst hx
      apply hne
      have : z = 0 := by simpa using he
      simp [this]
    · exact ha ⟨z / x, by field_simp; rw [he]; ring⟩
  · exact ⟨z / y, x / y, by field_simp; rw [he]; ring⟩

/-! ### Valuation logarithms -/

/-- The logarithm $\log v(x) \in \mathbb{Z}$ of the valuation (so $v(x) = \exp(L(x))$ for $x \ne 0$). -/
noncomputable def L (x : K) : ℤ := WithZero.log (Valued.v x)

lemma v_ne_zero {x : K} (hx : x ≠ 0) : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx

lemma v_eq_exp {x : K} (hx : x ≠ 0) : Valued.v x = exp (L x) := (exp_log (v_ne_zero hx)).symm

lemma L_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : L (x * y) = L x + L y := by
  unfold L; rw [map_mul, log_mul (v_ne_zero hx) (v_ne_zero hy)]

lemma L_sq {x : K} (hx : x ≠ 0) : L (x ^ 2) = 2 * L x := by
  rw [pow_two, L_mul hx hx]; ring

lemma L_neg (x : K) : L (-x) = L x := by unfold L; rw [Valuation.map_neg]

lemma L_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : L (x / y) = L x - L y := by
  unfold L; rw [map_div₀, log_div (v_ne_zero hx) (v_ne_zero hy)]

lemma L_of_v {x : K} {n : ℤ} (h : Valued.v x = exp n) : L x = n := by
  unfold L; rw [h, log_exp]

lemma v_lt_one_iff {x : K} (hx : x ≠ 0) : Valued.v x < 1 ↔ L x < 0 := by
  rw [v_eq_exp hx, exp_lt_one_iff]

lemma L_zpow {π : K} (hπ : Valued.v π = exp (-1 : ℤ)) (n : ℤ) : L (π ^ n) = -n := by
  apply L_of_v
  rw [map_zpow₀, hπ, ← exp_zsmul]
  congr 1
  simp

lemma ne_zero_of_v {π : K} {g : ℤᵐ⁰} (hg : g ≠ 0) (hπ : Valued.v π = g) : π ≠ 0 := by
  rintro rfl; rw [Valuation.map_zero] at hπ; exact hg hπ.symm

/-- **Ultrametric equality:** if $L(p) \ne L(q)$ then $p - q \ne 0$ and $L(p - q) = \max(L p, L q)$. -/
lemma L_sub_of_ne {p q : K} (hp : p ≠ 0) (hq : q ≠ 0) (h : L p ≠ L q) :
    p - q ≠ 0 ∧ L (p - q) = max (L p) (L q) := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hv : Valued.v p < Valued.v q := by rw [v_eq_exp hp, v_eq_exp hq, exp_lt_exp]; exact hlt
    have e := Valuation.map_sub_eq_of_lt_right (Valued.v) hv
    have hne : p - q ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at e; exact v_ne_zero hq e.symm
    refine ⟨hne, ?_⟩
    rw [max_eq_right hlt.le]
    unfold L; rw [e]
  · have hv : Valued.v q < Valued.v p := by rw [v_eq_exp hp, v_eq_exp hq, exp_lt_exp]; exact hlt
    have e := Valuation.map_sub_eq_of_lt_left (Valued.v) hv
    have hne : p - q ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero] at e; exact v_ne_zero hp e.symm
    refine ⟨hne, ?_⟩
    rw [max_eq_left hlt.le]
    unfold L; rw [e]

lemma L_sub_le {p q : K} (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p - q ≠ 0) :
    L (p - q) ≤ max (L p) (L q) := by
  have h := Valuation.map_sub (Valued.v) p q
  rw [v_eq_exp hp, v_eq_exp hq, v_eq_exp hpq] at h
  rcases le_total (L p) (L q) with hle | hle
  · rw [max_eq_right hle]
    rw [max_eq_right (exp_le_exp.mpr hle), exp_le_exp] at h; exact h
  · rw [max_eq_left hle]
    rw [max_eq_left (exp_le_exp.mpr hle), exp_le_exp] at h; exact h

lemma not_isSquare_of_L_odd {x : K} (hx : x ≠ 0) (h : Odd (L x)) : ¬ IsSquare x := by
  rintro ⟨s, rfl⟩
  have hs : s ≠ 0 := by rintro rfl; simp at hx
  rw [← pow_two, L_sq hs] at h
  exact Int.not_odd_iff_even.mpr (even_two_mul _) h

lemma isSquare_of_L_sub_one (h : OddLocalAxioms K) {t : K} (ht : t - 1 ≠ 0) (hL : L (t - 1) < 0) :
    IsSquare t :=
  h.isSquare_of_near_one t ((v_lt_one_iff ht).mpr hL)

/-! ### The unit case -/

/-- For a nonsquare unit $u$: $(u, b) = 1$ iff $v(b)$ is an even power. -/
lemma unit_hs_iff (h : OddLocalAxioms K) {π : K} (hπ : Valued.v π = exp (-1 : ℤ)) {u : K}
    (hu : Valued.v u = 1) (hns : ¬ IsSquare u) {b : K} (hb : b ≠ 0) :
    hilbertSymbol K u b = 1 ↔ Even (L b) := by
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  have hu0 : u ≠ 0 := ne_zero_of_v one_ne_zero hu
  have hLu : L u = 0 := L_of_v (by rw [hu]; rfl)
  constructor
  · intro hs
    obtain ⟨x, y, hxy⟩ := norm_of_hs hns hs
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := by rintro rfl; apply hb; rw [← hxy]; ring
      have : b = -(u * y ^ 2) := by rw [← hxy]; ring
      rw [this, L_neg, L_mul hu0 (pow_ne_zero 2 hy), L_sq hy, hLu]
      exact ⟨L y, by ring⟩
    by_cases hy : y = 0
    · subst hy
      have : b = x ^ 2 := by rw [← hxy]; ring
      rw [this, L_sq hx]; exact ⟨L x, by ring⟩
    have hp : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hq : u * y ^ 2 ≠ 0 := mul_ne_zero hu0 (pow_ne_zero 2 hy)
    have hLp : L (x ^ 2) = 2 * L x := L_sq hx
    have hLq : L (u * y ^ 2) = 2 * L y := by rw [L_mul hu0 (pow_ne_zero 2 hy), L_sq hy, hLu]; ring
    by_cases hne : L (x ^ 2) = L (u * y ^ 2)
    · -- equal valuations: either `L b = L (x^2)` or `u` is a square
      by_contra hodd
      have hle := L_sub_le hp hq (by rw [hxy]; exact hb)
      rw [hxy, ← hne, max_self] at hle
      have hlt : L b < L (x ^ 2) := by
        rcases lt_or_eq_of_le hle with h' | h'
        · exact h'
        · exfalso; apply hodd; rw [h', hLp]; exact ⟨L x, by ring⟩
      apply hns
      have ht : x ^ 2 / (u * y ^ 2) - 1 = b / (u * y ^ 2) := by
        rw [← hxy]; field_simp
      have hb' : b / (u * y ^ 2) ≠ 0 := div_ne_zero hb hq
      obtain ⟨s, hs⟩ := h.isSquare_of_L_sub_one (t := x ^ 2 / (u * y ^ 2)) (by rw [ht]; exact hb')
        (by rw [ht, L_div hb hq, ← hne]; omega)
      have hs0 : s ≠ 0 := by
        rintro rfl
        simp only [mul_zero, div_eq_zero_iff] at hs
        rcases hs with h1 | h1
        · exact hp h1
        · exact hq h1
      refine ⟨x / (y * s), ?_⟩
      have : u = x ^ 2 / (y ^ 2 * (s * s)) := by
        rw [← hs]; field_simp
      rw [this]; ring
    · obtain ⟨-, hmax⟩ := L_sub_of_ne hp hq hne
      rw [hxy] at hmax
      rw [hmax]
      rcases max_choice (L (x ^ 2)) (L (u * y ^ 2)) with hm | hm <;> rw [hm]
      · rw [hLp]; exact ⟨L x, by ring⟩
      · rw [hLq]; exact ⟨L y, by ring⟩
  · rintro ⟨j, hj⟩
    set w := b * π ^ (L b) with hw
    have hwv : Valued.v w = 1 := by
      rw [hw, map_mul, map_zpow₀, hπ, v_eq_exp hb, ← exp_zsmul, ← exp_add]
      simp
    have hbw : b = w * (π ^ (-j)) ^ 2 := by
      rw [hw, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hπ0, hj]
      have : j + j + -j * ((2 : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [this, zpow_zero, mul_one]
    rw [hbw, hs_mul_sq_right _ _ _ (zpow_ne_zero _ hπ0)]
    obtain ⟨x, y, hxy⟩ := h.unit_norm u w hu hwv
    exact hs_of_norm hxy

/-! ### The uniformizer case -/

lemma unif_not_isSquare {π' : K} (hπ' : Valued.v π' = exp (-1 : ℤ)) : ¬ IsSquare π' :=
  not_isSquare_of_L_odd (ne_zero_of_v exp_ne_zero hπ') (by rw [L_of_v hπ']; decide)

/-- For a uniformizer $\pi'$ and a unit $w$: $(\pi', w) = 1$ iff $w$ is a square. -/
lemma unif_hs_unit_iff (h : OddLocalAxioms K) {π' : K} (hπ' : Valued.v π' = exp (-1 : ℤ)) {w : K}
    (hw : Valued.v w = 1) : hilbertSymbol K π' w = 1 ↔ IsSquare w := by
  have hπ0 : π' ≠ 0 := ne_zero_of_v exp_ne_zero hπ'
  have hw0 : w ≠ 0 := ne_zero_of_v one_ne_zero hw
  have hLπ : L π' = -1 := L_of_v hπ'
  have hLw : L w = 0 := L_of_v (by rw [hw]; rfl)
  constructor
  · intro hs
    obtain ⟨x, y, hxy⟩ := norm_of_hs (unif_not_isSquare hπ') hs
    by_cases hy : y = 0
    · subst hy; exact ⟨x, by rw [← hxy]; ring⟩
    by_cases hx : x = 0
    · exfalso
      subst hx
      have : w = -(π' * y ^ 2) := by rw [← hxy]; ring
      have h2 := congrArg L this
      rw [L_neg, L_mul hπ0 (pow_ne_zero 2 hy), L_sq hy, hLπ, hLw] at h2
      omega
    have hp : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hq : π' * y ^ 2 ≠ 0 := mul_ne_zero hπ0 (pow_ne_zero 2 hy)
    have hLp : L (x ^ 2) = 2 * L x := L_sq hx
    have hLq : L (π' * y ^ 2) = -1 + 2 * L y := by
      rw [L_mul hπ0 (pow_ne_zero 2 hy), L_sq hy, hLπ]
    obtain ⟨-, hmax⟩ := L_sub_of_ne hp hq (by rw [hLp, hLq]; omega)
    rw [hxy, hLw] at hmax
    have hq0 : L (π' * y ^ 2) < 0 := by
      have := le_max_right (L (x ^ 2)) (L (π' * y ^ 2))
      rw [← hmax] at this
      rcases lt_or_eq_of_le this with h' | h'
      · exact h'
      · exfalso; rw [hLq] at h'; omega
    have hp0 : L (x ^ 2) = 0 := by
      rcases max_choice (L (x ^ 2)) (L (π' * y ^ 2)) with hm | hm
      · rw [← hm, hmax]
      · rw [hm] at hmax; omega
    have ht : w / x ^ 2 - 1 = -(π' * y ^ 2) / x ^ 2 := by
      rw [← hxy]; field_simp; ring
    obtain ⟨s, hs⟩ := h.isSquare_of_L_sub_one (t := w / x ^ 2)
      (by rw [ht]; exact div_ne_zero (neg_ne_zero.mpr hq) hp)
      (by rw [ht, L_div (neg_ne_zero.mpr hq) hp, L_neg, hp0]; omega)
    refine ⟨s * x, ?_⟩
    have : w = (w / x ^ 2) * x ^ 2 := by field_simp
    rw [this, hs]; ring
  · rintro ⟨s, rfl⟩
    exact hs_of_norm (a := π') (x := s) (y := 0) (by ring)

/-- For a uniformizer $\pi'$ and a unit $w$: $(\pi', \pi' w) = 1$ iff $-w$ is a square. -/
lemma unif_hs_unif_iff (h : OddLocalAxioms K) {π' : K} (hπ' : Valued.v π' = exp (-1 : ℤ)) {w : K}
    (hw : Valued.v w = 1) : hilbertSymbol K π' (π' * w) = 1 ↔ IsSquare (-w) := by
  have hπ0 : π' ≠ 0 := ne_zero_of_v exp_ne_zero hπ'
  have hw0 : w ≠ 0 := ne_zero_of_v one_ne_zero hw
  have hLπ : L π' = -1 := L_of_v hπ'
  have hLw : L w = 0 := L_of_v (by rw [hw]; rfl)
  have hLπw : L (π' * w) = -1 := by rw [L_mul hπ0 hw0, hLπ, hLw]; ring
  constructor
  · intro hs
    obtain ⟨x, y, hxy⟩ := norm_of_hs (unif_not_isSquare hπ') hs
    by_cases hx : x = 0
    · subst hx
      refine ⟨y, ?_⟩
      have : π' * (-w - y * y) = 0 := by linear_combination hxy
      have := (mul_eq_zero.mp this).resolve_left hπ0
      linear_combination this
    by_cases hy : y = 0
    · exfalso
      subst hy
      have : π' * w = x ^ 2 := by rw [← hxy]; ring
      have h2 := congrArg L this
      rw [hLπw, L_sq hx] at h2
      omega
    have hp : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hq : π' * y ^ 2 ≠ 0 := mul_ne_zero hπ0 (pow_ne_zero 2 hy)
    have hLp : L (x ^ 2) = 2 * L x := L_sq hx
    have hLq : L (π' * y ^ 2) = -1 + 2 * L y := by
      rw [L_mul hπ0 (pow_ne_zero 2 hy), L_sq hy, hLπ]
    obtain ⟨-, hmax⟩ := L_sub_of_ne hp hq (by rw [hLp, hLq]; omega)
    rw [hxy, hLπw] at hmax
    have hLy : L y = 0 := by
      rcases max_choice (L (x ^ 2)) (L (π' * y ^ 2)) with hm | hm
      · rw [hm, hLp] at hmax; omega
      · rw [hm, hLq] at hmax; omega
    have hpl : L (x ^ 2) < -1 := by
      have := le_max_left (L (x ^ 2)) (L (π' * y ^ 2))
      rw [← hmax] at this
      rcases lt_or_eq_of_le this with h' | h'
      · exact h'
      · exfalso; rw [hLp] at h'; omega
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have ht : -w / y ^ 2 - 1 = -(x ^ 2 / π') / y ^ 2 := by
      have : x ^ 2 = π' * (w + y ^ 2) := by linear_combination hxy
      rw [this]; field_simp; ring
    have hxπ : x ^ 2 / π' ≠ 0 := div_ne_zero hp hπ0
    obtain ⟨s, hs⟩ := h.isSquare_of_L_sub_one (t := -w / y ^ 2)
      (by rw [ht]; exact div_ne_zero (neg_ne_zero.mpr hxπ) hy2)
      (by rw [ht, L_div (neg_ne_zero.mpr hxπ) hy2, L_neg, L_div hp hπ0, L_sq hy, hLy, hLπ]; omega)
    refine ⟨s * y, ?_⟩
    have : -w = (-w / y ^ 2) * y ^ 2 := by field_simp
    rw [this, hs]; ring
  · rintro ⟨s, hs⟩
    exact hs_of_norm (a := π') (x := 0) (y := s) (by linear_combination π' * hs)

/-- Squares of units form a subgroup of index $\le 2$: for units $w_1, w_2$, $w_1 w_2$ is a square iff
$w_1$ and $w_2$ are both squares or both nonsquares. -/
lemma isSquare_mul_iff (h : OddLocalAxioms K) {w₁ w₂ : K} (h₁ : Valued.v w₁ = 1)
    (h₂ : Valued.v w₂ = 1) : IsSquare (w₁ * w₂) ↔ (IsSquare w₁ ↔ IsSquare w₂) := by
  have h10 : w₁ ≠ 0 := ne_zero_of_v one_ne_zero h₁
  have h20 : w₂ ≠ 0 := ne_zero_of_v one_ne_zero h₂
  have div_sq : ∀ {x y : K}, y ≠ 0 → IsSquare (x * y) → IsSquare y → IsSquare x := by
    rintro x y hy ⟨r, hr⟩ ⟨t, rfl⟩
    have ht : t ≠ 0 := by rintro rfl; simp at hy
    exact ⟨r / t, by field_simp; linear_combination hr⟩
  constructor
  · intro hp
    constructor
    · intro hs1; exact div_sq h10 (by rw [mul_comm]; exact hp) hs1
    · intro hs2; exact div_sq h20 hp hs2
  · intro hiff
    by_cases hs1 : IsSquare w₁
    · exact hs1.mul (hiff.mp hs1)
    · rcases h.unit_sq_classes w₁ w₂ h₁ h₂ with h' | h' | h'
      · exact absurd h' hs1
      · exact absurd (hiff.mpr h') hs1
      · exact h'

/-- For a uniformizer $\pi'$ and $b \ne 0$: $(\pi', b) = 1$ iff $b \, (-\pi')^{L(b)}$ (a unit) is a
square. -/
lemma unif_hs_iff (h : OddLocalAxioms K) {π' : K} (hπ' : Valued.v π' = exp (-1 : ℤ)) {b : K}
    (hb : b ≠ 0) : hilbertSymbol K π' b = 1 ↔ IsSquare (b * (-π') ^ (L b)) := by
  have hπ0 : π' ≠ 0 := ne_zero_of_v exp_ne_zero hπ'
  have hnπ : Valued.v (-π') = exp (-1 : ℤ) := by rw [Valuation.map_neg, hπ']
  have hnπ0 : -π' ≠ 0 := neg_ne_zero.mpr hπ0
  set φ := b * (-π') ^ (L b) with hφ
  have hφv : Valued.v φ = 1 := by
    rw [hφ, map_mul, map_zpow₀, hnπ, v_eq_exp hb, ← exp_zsmul, ← exp_add]
    simp
  have hφ0 : φ ≠ 0 := ne_zero_of_v one_ne_zero hφv
  have hbφ : b = φ * (-π') ^ (-(L b)) := by
    rw [hφ, mul_assoc, ← zpow_add₀ hnπ0, add_neg_cancel, zpow_zero, mul_one]
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (L b)
  · have hb' : b = φ * ((-π') ^ (-j)) ^ 2 := by
      rw [hbφ, hj, ← zpow_natCast, ← zpow_mul]
      congr 2; push_cast; ring
    rw [hb', hs_mul_sq_right _ _ _ (zpow_ne_zero _ hnπ0)]
    exact h.unif_hs_unit_iff hπ' hφv
  · have hb' : b = π' * (-φ) * (π'⁻¹ * (-π') ^ (-j)) ^ 2 := by
      rw [hbφ, hj, mul_pow, ← zpow_natCast ((-π') ^ (-j)), ← zpow_mul]
      have e : -(2 * j + 1) = ((-j) * ((2 : ℕ) : ℤ)) + (-1) := by push_cast; ring
      rw [e, zpow_add₀ hnπ0, zpow_neg_one]
      field_simp
    rw [hb', hs_mul_sq_right _ _ _ (mul_ne_zero (inv_ne_zero hπ0) (zpow_ne_zero _ hnπ0)),
      h.unif_hs_unif_iff hπ' (by rw [Valuation.map_neg, hφv]), neg_neg]

/-- **Multiplicativity in the second argument** under `OddLocalAxioms`:
$(a, bc)_K = (a, b)_K (a, c)_K$ for $a, b, c \in K^\times$. -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 (p odd) [unverified]; omeara1963 §63B, 63:11 [unverified]"]
theorem hilbertSymbol_mul_right (h : OddLocalAxioms K) (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    hilbertSymbol K a (b * c) = hilbertSymbol K a b * hilbertSymbol K a c := by
  apply hs_eq_of_iff
  by_cases hsq : IsSquare a
  · simp only [hs_of_isSquare hsq]
  obtain ⟨π, hπ⟩ := h.exists_uniformizer
  have hπ0 : π ≠ 0 := ne_zero_of_v exp_ne_zero hπ
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' (L a)
  · -- `a = u · (π^(-j))²` with `u` a nonsquare unit
    set u := a * π ^ (L a) with hu
    have huv : Valued.v u = 1 := by
      rw [hu, map_mul, map_zpow₀, hπ, v_eq_exp ha, ← exp_zsmul, ← exp_add]
      simp
    have hau : a = u * (π ^ (-j)) ^ 2 := by
      rw [hu, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hπ0, hj]
      have : 2 * j + -j * ((2 : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [this, zpow_zero, mul_one]
    have hsj : π ^ (-j) ≠ 0 := zpow_ne_zero _ hπ0
    have hns : ¬ IsSquare u := by
      intro hus; apply hsq; rw [hau]; exact hus.mul ⟨π ^ (-j), by ring⟩
    rw [hau, hs_mul_sq_left _ _ _ hsj, hs_mul_sq_left _ _ _ hsj, hs_mul_sq_left _ _ _ hsj,
      h.unit_hs_iff hπ huv hns hbc, h.unit_hs_iff hπ huv hns hb, h.unit_hs_iff hπ huv hns hc,
      L_mul hb hc, Int.even_add]
  · -- `a = π' · (π^(-(j+1)))²` with `π'` a uniformizer
    set π' := a * π ^ (2 * j + 2) with hπ'
    have hπ'v : Valued.v π' = exp (-1 : ℤ) := by
      rw [hπ', map_mul, map_zpow₀, hπ, v_eq_exp ha, ← exp_zsmul, ← exp_add, hj]
      congr 1; simp; ring
    have hπ'0 : π' ≠ 0 := ne_zero_of_v exp_ne_zero hπ'v
    have hsj : π ^ (-(j + 1)) ≠ 0 := zpow_ne_zero _ hπ0
    have haπ : a = π' * (π ^ (-(j + 1))) ^ 2 := by
      rw [hπ', ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hπ0]
      have : 2 * j + 2 + -(j + 1) * ((2 : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [this, zpow_zero, mul_one]
    have hnπ0 : -π' ≠ 0 := neg_ne_zero.mpr hπ'0
    have hnπv : Valued.v (-π') = exp (-1 : ℤ) := by rw [Valuation.map_neg, hπ'v]
    have unitv : ∀ {x : K}, x ≠ 0 → Valued.v (x * (-π') ^ (L x)) = 1 := by
      intro x hx
      rw [map_mul, map_zpow₀, hnπv, v_eq_exp hx, ← exp_zsmul, ← exp_add]
      simp
    rw [haπ, hs_mul_sq_left _ _ _ hsj, hs_mul_sq_left _ _ _ hsj, hs_mul_sq_left _ _ _ hsj,
      h.unif_hs_iff hπ'v hbc, h.unif_hs_iff hπ'v hb, h.unif_hs_iff hπ'v hc, L_mul hb hc,
      zpow_add₀ hnπ0]
    have e : b * c * ((-π') ^ L b * (-π') ^ L c) = (b * (-π') ^ L b) * (c * (-π') ^ L c) := by ring
    rw [e]
    exact h.isSquare_mul_iff (unitv hb) (unitv hc)

/-- **Multiplicativity in the first argument** under `OddLocalAxioms`:
$(ab, c)_K = (a, c)_K (b, c)_K$ for $a, b, c \in K^\times$ (from `hilbertSymbol_mul_right` and
symmetry). -/
@[kb "serre1973" "Ch. III §1.2, Thm. 2 (p odd) [unverified]; omeara1963 §63B, 63:11 [unverified]"]
theorem hilbertSymbol_mul_left (h : OddLocalAxioms K) (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) :
    hilbertSymbol K (a * b) c = hilbertSymbol K a c * hilbertSymbol K b c := by
  rw [hilbertSymbol_comm K (a * b), hilbertSymbol_comm K a, hilbertSymbol_comm K b]
  exact h.hilbertSymbol_mul_right c a b hc ha hb

end OddLocalAxioms

end QuadFormsKB.FF
