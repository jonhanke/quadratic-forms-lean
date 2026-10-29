/-
# O'Meara §12: archimedean valuations (12:1, 12:5 – 12:12)

**Setting.** Valuations are Mathlib `AbsoluteValue F ℝ`; a *spot* is an equivalence class of valuations
(`AbsoluteValue.IsEquiv`, shown equivalent to O'Meara's "same topology" in `Sec11A.lean`). A valuation is
archimedean when it is not non-archimedean (`¬ IsNonarchimedean`).

**Proves**
* `rat_archimedean_exists_rpow`, `rat_archimedean_spot_unique` (**12:1**): every archimedean valuation of $\mathbb Q$
  is $|\ |_\infty^{\varrho}$ with $0 < \varrho \le 1$, and the archimedean spot of $\mathbb Q$ is unique. Deduced from
  Mathlib's Ostrowski theorem (`Rat.AbsoluteValue.equiv_real_of_unbounded`) and 11:1;
* `ordinary_unique` (**12:5**, uniqueness half) and `ordinary_rpow` (**12:6**): the *ordinary* absolute value of an
  archimedean spot is the valuation with $|m| = m$ for natural $m$ (`IsOrdinaryAbs`), unique in its spot, and every
  valuation of the spot is its power $\varrho \in (0, 1]$;
* `IsRealSpot`, `IsComplexSpot`, `normalizedSpotAbs` (**12:8**, **12:9**, definitions);
* `normalizedSpotAbs_add_le_of_real`, `normalizedSpotAbs_sum_le_of_complex` (**12:10**): the normalized valuation is a true
  valuation at a real spot and satisfies $|\sum_{i=1}^r \alpha_i|_{\mathfrak p} \le 2^{r-1}\sum |\alpha_i|_{\mathfrak p}$
  at a complex spot;
* `IsPositiveElt`, `IsNegativeElt` (**12:11**, definitions) and `isPositiveElt_iff_pos`, `isNegativeElt_iff_neg`,
  `trichotomy_positive`, `isPositiveElt_mul`, `isPositiveElt_inv` (**12:12**).

**Not proved here.** 12:2, 12:3, 12:4 (a complete archimedean field is $\mathbb R$ or $\mathbb C$) and the *existence*
half of 12:5 depend on them; Mathlib has only the Gelfand–Mazur step (`NormedAlgebra.Real.nonempty_algEquiv_or`).

**Conventions that differ from the book.** The completion $F_{\mathfrak p}$ is Mathlib's `v.Completion` (unique up to
isometric isomorphism by 11:15). `IsRealSpot v` / `IsComplexSpot v` ask for an *isometric* ring isomorphism of
`v.Completion` with $\mathbb R$ (resp. $\mathbb C$) for the valuation $v$ itself, so they are meant for $v$ the
ordinary absolute value at the spot (O'Meara's topological isomorphism is isometric for that normalization).
-/
import QuadFormsKB.Citation
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Algebra.Order.Chebyshev
import QuadFormsKB.Literature.OMeara.Sec11A
import QuadFormsKB.Literature.OMeara.Sec11B

open Filter Topology

namespace QuadFormsKB.OMeara

/-- Every archimedean valuation of $\mathbb Q$ is equivalent to the usual absolute value
(`Rat.AbsoluteValue.real`); this is Mathlib's Ostrowski theorem in the unbounded case, with unboundedness on $\mathbb N$
equivalent to being archimedean by 11:1. -/
theorem rat_archimedean_equiv_real (v : AbsoluteValue ℚ ℝ) (hv : ¬ IsNonarchimedean v) :
    v.IsEquiv Rat.AbsoluteValue.real := by
  have notbdd : ¬ ∀ n : ℕ, v n ≤ 1 := by
    intro h
    exact hv ((isNonarchimedean_iff_natCast_bounded v).2 ⟨1, h⟩)
  exact Rat.AbsoluteValue.equiv_real_of_unbounded notbdd

/-- The usual absolute value of $\mathbb Q$ is archimedean. -/
theorem real_not_nonarchimedean : ¬ IsNonarchimedean Rat.AbsoluteValue.real := by
  intro h
  have := h 1 1
  simp at this
  norm_num at this

/-- **12:1 (first half).** Every archimedean valuation $|\ |$ of $\mathbb Q$ has the form
$|x| = |x|_\infty^{\varrho}$ for all $x \in \mathbb Q$, with $0 < \varrho \le 1$ ($|\ |_\infty$ the usual absolute
value). The bound $\varrho \le 1$ is the triangle law at $2 = 1 + 1$. -/
@[kb "omeara1963" "§12, 12:1, p. 14"]
theorem rat_archimedean_exists_rpow (v : AbsoluteValue ℚ ℝ) (hv : ¬ IsNonarchimedean v) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x : ℚ, v x = |(x : ℝ)| ^ ρ := by
  obtain ⟨c, hc, h⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1
    ((rat_archimedean_equiv_real v hv).symm)
  have hx : ∀ x : ℚ, v x = |(x : ℝ)| ^ c := fun x => by
    have := congrFun h x
    rw [← this]
    simp [Rat.AbsoluteValue.real_eq_abs]
  refine ⟨c, hc, ?_, hx⟩
  have h2 : v 2 ≤ 2 := by
    have := v.add_le 1 1
    norm_num at this
    exact this
  have h3 := hx 2
  norm_num at h3
  rw [h3] at h2
  by_contra hlt
  rw [not_le] at hlt
  have : (2 : ℝ) ^ (1 : ℝ) < 2 ^ c := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  norm_num at this
  linarith


/-- **12:1 (second half).** There is exactly one archimedean spot on $\mathbb Q$: any two archimedean valuations
of $\mathbb Q$ are equivalent (and the usual absolute value is archimedean, `real_not_nonarchimedean`). -/
@[kb "omeara1963" "§12, 12:1, p. 14"]
theorem rat_archimedean_spot_unique (v w : AbsoluteValue ℚ ℝ) (hv : ¬ IsNonarchimedean v)
    (hw : ¬ IsNonarchimedean w) : v.IsEquiv w :=
  (rat_archimedean_equiv_real v hv).trans (rat_archimedean_equiv_real w hw).symm

section Ordinary

universe u
variable {F : Type u} [Field F]

/-- The valuation $w$ of $F$ is the *ordinary absolute value* in the sense of 12:5 when $|m| = m$ for every
natural number $m$ (the image of $m \in \mathbb N$ in $F$). -/
@[kb "omeara1963" "§12, 12:5 (definition of the ordinary absolute value), p. 19"]
def IsOrdinaryAbs (w : AbsoluteValue F ℝ) : Prop := ∀ n : ℕ, w (n : F) = n

/-- If $2^c = 2$ for a real exponent $c$ then $c = 1$. -/
theorem two_rpow_eq_two {c : ℝ} (h : (2 : ℝ) ^ c = 2) : c = 1 := by
  have h2 := congrArg Real.log h
  rw [Real.log_rpow (by norm_num)] at h2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (c - 1) * Real.log 2 = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hl.ne'

/-- **12:5 (uniqueness half).** Two equivalent valuations of a field $F$ that are both ordinary absolute values
($|m| = m$ for all natural $m$) are equal. (O'Meara's existence statement, that each archimedean spot contains an
ordinary absolute value, needs 12:4 and is not proved here.) -/
@[kb "omeara1963" "§12, 12:5, p. 19"]
theorem ordinary_unique (v w : AbsoluteValue F ℝ) (hv : IsOrdinaryAbs v) (hw : IsOrdinaryAbs w)
    (h : v.IsEquiv w) : v = w := by
  obtain ⟨c, hc, hvw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h
  have h2 := congrFun hvw 2
  have e1 := hv 2
  have e2 := hw 2
  simp only [Nat.cast_ofNat] at e1 e2
  rw [e1] at h2
  simp only [e2] at h2
  have := two_rpow_eq_two h2
  subst this
  ext x
  simpa using congrFun hvw x

/-- **12:6.** Let $w$ be the ordinary absolute value ($|m|_w = m$) of an archimedean spot $\mathfrak p$ of $F$. Every
valuation $v$ in the spot (equivalent to $w$) is $v = w^{\varrho}$ for some $0 < \varrho \le 1$. -/
@[kb "omeara1963" "§12, 12:6, p. 19"]
theorem ordinary_rpow (w v : AbsoluteValue F ℝ) (hw : IsOrdinaryAbs w) (h : v.IsEquiv w) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, v x = w x ^ ρ := by
  obtain ⟨c, hc, hvw⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h.symm
  have hx : ∀ x, v x = w x ^ c := fun x => (congrFun hvw x).symm
  refine ⟨c, hc, ?_, hx⟩
  have h2 : v 2 ≤ 2 := by
    have := v.add_le 1 1
    norm_num at this
    exact this
  have h3 := hx 2
  have e2 := hw 2
  simp only [Nat.cast_ofNat] at e2
  rw [e2] at h3
  rw [h3] at h2
  by_contra hlt
  rw [not_le] at hlt
  have : (2 : ℝ) ^ (1 : ℝ) < 2 ^ c := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
  norm_num at this
  linarith

end Ordinary


section Spots

universe u
variable {F : Type u} [Field F]

/-- The valuation $v$ of $F$ is at a *real spot* (12:8): its completion $F_v$, Mathlib's `v.Completion`, is
isometrically ring-isomorphic to $\mathbb R$ with its usual absolute value. -/
@[kb "omeara1963" "§12, 12:8 (definition of real and complex spots), p. 19"]
def IsRealSpot (v : AbsoluteValue F ℝ) : Prop :=
  ∃ φ : v.Completion ≃+* ℝ, ∀ y, |φ y| = ‖y‖

/-- The valuation $v$ of $F$ is at a *complex spot* (12:8): its completion $F_v$, Mathlib's `v.Completion`, is
isometrically ring-isomorphic to $\mathbb C$ with its usual absolute value. -/
@[kb "omeara1963" "§12, 12:8 (definition of real and complex spots), p. 19"]
def IsComplexSpot (v : AbsoluteValue F ℝ) : Prop :=
  ∃ φ : v.Completion ≃+* ℂ, ∀ y, ‖φ y‖ = ‖y‖

/-- The *normalized valuation* of $x \in F$ at the spot of the ordinary absolute value $v$ (12:9): $|x|_v$ at a
real spot and $|x|_v^2$ at a complex spot. (At a spot that is neither, the value is $|x|_v$.) -/
@[kb "omeara1963" "§12, 12:9 (definition of the normalized valuation), p. 19"]
noncomputable def normalizedSpotAbs (v : AbsoluteValue F ℝ) (x : F) : ℝ :=
  open Classical in if IsComplexSpot v then v x ^ 2 else v x

/-- Unfolding of `normalizedSpotAbs` away from complex spots. -/
theorem normalizedSpotAbs_of_real {v : AbsoluteValue F ℝ} (h : ¬ IsComplexSpot v) (x : F) :
    normalizedSpotAbs v x = v x := by
  simp [normalizedSpotAbs, h]

/-- Unfolding of `normalizedSpotAbs` at a complex spot. -/
theorem normalizedSpotAbs_of_complex {v : AbsoluteValue F ℝ} (h : IsComplexSpot v) (x : F) :
    normalizedSpotAbs v x = v x ^ 2 := by
  simp [normalizedSpotAbs, h]

/-- **12:10 (real spots).** The normalized valuation is a true valuation away from complex spots: it satisfies the
triangle law. -/
@[kb "omeara1963" "§12, 12:10, p. 19"]
theorem normalizedSpotAbs_add_le_of_real {v : AbsoluteValue F ℝ} (h : ¬ IsComplexSpot v) (a b : F) :
    normalizedSpotAbs v (a + b) ≤ normalizedSpotAbs v a + normalizedSpotAbs v b := by
  simp only [normalizedSpotAbs_of_real h]
  exact v.add_le a b

/-- For a valuation $v$: $v(\sum_{i \in s} a_i)^2 \le |s|\sum_{i\in s} v(a_i)^2$. -/
theorem sq_sum_le (v : AbsoluteValue F ℝ) {ι : Type*} (s : Finset ι) (a : ι → F) :
    v (∑ i ∈ s, a i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, v (a i) ^ 2 := by
  calc v (∑ i ∈ s, a i) ^ 2 ≤ (∑ i ∈ s, v (a i)) ^ 2 :=
        pow_le_pow_left₀ (v.nonneg _) (v.sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, v (a i) ^ 2 := sq_sum_le_card_mul_sum_sq

/-- **12:10 (complex spots).** At a complex spot, for $r \ge 1$ elements $\alpha_1, \dots, \alpha_r$ (here a
nonempty finite family) the normalized valuation satisfies
$|\sum_{i=1}^r \alpha_i|_{\mathfrak p} \le 2^{r-1} \sum_{i=1}^r |\alpha_i|_{\mathfrak p}$; for $r = 2$ this is
$|\alpha + \beta|_{\mathfrak p} \le 2(|\alpha|_{\mathfrak p} + |\beta|_{\mathfrak p})$. -/
@[kb "omeara1963" "§12, 12:10, p. 19"]
theorem normalizedSpotAbs_sum_le_of_complex {v : AbsoluteValue F ℝ} (h : IsComplexSpot v) {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (a : ι → F) :
    normalizedSpotAbs v (∑ i ∈ s, a i) ≤ 2 ^ (s.card - 1) * ∑ i ∈ s, normalizedSpotAbs v (a i) := by
  simp only [normalizedSpotAbs_of_complex h]
  refine (sq_sum_le v s a).trans ?_
  have hc : (s.card : ℝ) ≤ 2 ^ (s.card - 1) := by
    obtain ⟨n, hn⟩ : ∃ n, s.card = n + 1 := ⟨s.card - 1, by have := hs.card_pos; omega⟩
    rw [hn]
    simp only [Nat.add_sub_cancel]
    exact_mod_cast (Nat.lt_two_pow_self (n := n))
  gcongr

end Spots


section Positive

/-- An element $x$ of a field $E$ is *positive* (12:11) if it is a non-zero square of $E$. For $E = F_{\mathfrak p}$ at a
real spot this is O'Meara's "$\alpha \in F_{\mathfrak p}^{\times 2}$"; an element of $F$ is positive at $\mathfrak p$ when
its image in $F_{\mathfrak p}$ is. -/
@[kb "omeara1963" "§12, 12:11 (definition of positive and negative elements), p. 20"]
def IsPositiveElt {E : Type*} [Field E] (x : E) : Prop := x ≠ 0 ∧ IsSquare x

/-- An element $x$ of a field $E$ is *negative* (12:11) if $-x$ is positive. -/
@[kb "omeara1963" "§12, 12:11 (definition of positive and negative elements), p. 20"]
def IsNegativeElt {E : Type*} [Field E] (x : E) : Prop := IsPositiveElt (-x)

/-- **12:12 (positive elements of $F_{\mathfrak p} \cong \mathbb R$).** For a ring isomorphism $\varphi\colon E \to \mathbb R$,
$x \in E$ is positive (a non-zero square) iff $\varphi(x) > 0$. -/
@[kb "omeara1963" "§12, 12:12, p. 20"]
theorem isPositiveElt_iff_pos {E : Type*} [Field E] (φ : E ≃+* ℝ) (x : E) :
    IsPositiveElt x ↔ 0 < φ x := by
  constructor
  · rintro ⟨hx, y, rfl⟩
    have : φ y ≠ 0 := fun h => hx (by simp [(φ.map_eq_zero_iff).1 h])
    rw [map_mul]
    exact mul_self_pos.2 this
  · intro h
    refine ⟨fun h0 => by simp [h0] at h, φ.symm (Real.sqrt (φ x)), ?_⟩
    apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact (Real.mul_self_sqrt h.le).symm

/-- **12:12 (negative elements).** For a ring isomorphism $\varphi\colon E \to \mathbb R$, $x$ is negative iff
$\varphi(x) < 0$. -/
@[kb "omeara1963" "§12, 12:12, p. 20"]
theorem isNegativeElt_iff_neg {E : Type*} [Field E] (φ : E ≃+* ℝ) (x : E) :
    IsNegativeElt x ↔ φ x < 0 := by
  unfold IsNegativeElt
  rw [isPositiveElt_iff_pos φ, map_neg]
  constructor <;> intro h <;> linarith

/-- **12:12 (disjoint union).** For a ring isomorphism $E \cong \mathbb R$, every $x \in E$ is exactly one of
negative, zero, positive: $E = -E^{+} \sqcup \{0\} \sqcup E^{+}$. -/
@[kb "omeara1963" "§12, 12:12, p. 20"]
theorem trichotomy_positive {E : Type*} [Field E] (φ : E ≃+* ℝ) (x : E) :
    (IsNegativeElt x ∧ x ≠ 0 ∧ ¬ IsPositiveElt x) ∨ (x = 0 ∧ ¬ IsNegativeElt x ∧ ¬ IsPositiveElt x) ∨
      (IsPositiveElt x ∧ x ≠ 0 ∧ ¬ IsNegativeElt x) := by
  rw [isNegativeElt_iff_neg φ, isPositiveElt_iff_pos φ]
  have hx : x = 0 ↔ φ x = 0 := ⟨fun h => by simp [h], fun h => φ.injective (by simpa using h)⟩
  rcases lt_trichotomy (φ x) 0 with h | h | h
  · left; exact ⟨h, fun h0 => by rw [hx.1 h0] at h; exact lt_irrefl _ h, not_lt.2 h.le⟩
  · right; left; exact ⟨hx.2 h, by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩
  · right; right; exact ⟨h, fun h0 => by rw [hx.1 h0] at h; exact lt_irrefl _ h, not_lt.2 h.le⟩

/-- **12:12 (subgroup).** The positive elements are closed under products (part of: they form a subgroup of
$E^\times$; the index $2$ and openness are not stated here). -/
@[kb "omeara1963" "§12, 12:12, p. 20"]
theorem isPositiveElt_mul {E : Type*} [Field E] {x y : E} (hx : IsPositiveElt x)
    (hy : IsPositiveElt y) : IsPositiveElt (x * y) :=
  ⟨mul_ne_zero hx.1 hy.1, hx.2.mul hy.2⟩

/-- **12:12 (subgroup).** The positive elements are closed under inverses. -/
@[kb "omeara1963" "§12, 12:12, p. 20"]
theorem isPositiveElt_inv {E : Type*} [Field E] {x : E} (hx : IsPositiveElt x) :
    IsPositiveElt x⁻¹ :=
  ⟨inv_ne_zero hx.1, by obtain ⟨y, rfl⟩ := hx.2; exact ⟨y⁻¹, by simp⟩⟩

end Positive

end QuadFormsKB.OMeara
