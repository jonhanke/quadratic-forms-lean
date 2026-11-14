/-
# The local Hilbert symbol at every place of $\mathbb{F}_q(t)$ is multiplicative

For a finite field $k$ of odd characteristic, the completions of $k(t)$ satisfy the odd local axioms
(`FF.OddLocalAxioms`), so the Hilbert symbol is multiplicative at every place
(`localHilbertMul`, which proves the named input `RatFuncPlace.LocalHilbertMul k` of
`RatFuncHMFour.lean`). The proof is purely local; it is the case $F = \mathbb{F}_q(t)$ of O'Meara 63:11
(Serre, Ch. III, Thm. 2 for $\mathbb{Q}_p$, $p$ odd), checked through `FF.oddLocalAxioms_of_residue`:

* at a finite place $P$: $R = k[t]$, $\kappa = k[t]/(P)$ (finite, odd characteristic). A unit $a$ of
  $k(t)_P$ is close to some $g = p/q \in k(t)$ (density), with $p, q \notin (P)$ because they are coprime
  and $v_P(g) = 1$; so $a = pq \cdot q^{-2} \cdot (a/g)$, and $a / g$ is a square by the local square theorem.
* at infinity: $R = \kappa = k$. A unit $a$ of $k((t^{-1}))$ is close to some $g = p/q$ with
  $\deg p = \deg q$; with $c = \operatorname{lc}(p)/\operatorname{lc}(q) \in k^\times$,
  $v_\infty(g/c - 1) < 1$, so $a = c \cdot (\text{square})$.

Indices are 0-based.
-/
import QuadFormsKB.FunctionField.OddLocalCriteria
import QuadFormsKB.FunctionField.RatFuncHMFour

open IsDedekindDomain Polynomial WithZero

namespace QuadFormsKB.RatFuncPlace

open scoped Classical

variable {k : Type} [Field k]

/-! ### Generic helpers -/

/-- In a valued field, the ball $\{y : v(a - y) < 1\}$ is open. -/
lemma isOpen_ball_sub {K : Type*} [Field K] [Valued K ℤᵐ⁰] (a : K) :
    IsOpen {y : K | Valued.v (a - y) < 1} := by
  have hb := Valued.isOpen_ball K ((Valued.v : Valuation K ℤᵐ⁰).restrict 1)
  have e : {y : K | Valued.v (a - y) < 1} =
      (fun y => a - y) ⁻¹' {x | (Valued.v : Valuation K ℤᵐ⁰).restrict x <
        (Valued.v : Valuation K ℤᵐ⁰).restrict 1} := by
    ext y
    simp [Valuation.restrict_lt_iff_lt_embedding]
  rw [e]
  exact hb.preimage (continuous_const.sub continuous_id)

/-- A dense subset meets every ball of radius $1$. -/
lemma exists_near {K L : Type*} [Field K] [Valued K ℤᵐ⁰] (f : L → K) (hf : DenseRange f) (a : K) :
    ∃ g : L, Valued.v (a - f g) < 1 := by
  obtain ⟨g, hg⟩ := hf.exists_mem_open (isOpen_ball_sub a)
    ⟨a, show Valued.v (a - a) < 1 by rw [sub_self, Valuation.map_zero]; exact zero_lt_one⟩
  exact ⟨g, hg⟩

/-- If $v(a) = 1$ and $v(a - b) < 1$ then $v(b) = 1$. -/
lemma v_eq_one_of_near {K : Type*} [Field K] [Valued K ℤᵐ⁰] {a b : K} (ha : Valued.v a = 1)
    (h : Valued.v (a - b) < 1) : Valued.v b = 1 := by
  have e : b = a - (a - b) := by ring
  rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [ha]; exact h), ha]

/-- If $v(a) \le 1$ and $v(a - b) < 1$ then $v(b) \le 1$. -/
lemma v_le_one_of_near {K : Type*} [Field K] [Valued K ℤᵐ⁰] {a b : K} (ha : Valued.v a ≤ 1)
    (h : Valued.v (a - b) < 1) : Valued.v b ≤ 1 := by
  have e : b = a - (a - b) := by ring
  rw [e]
  exact (Valuation.map_sub _ _ _).trans (max_le ha h.le)

/-- Closeness is transitive: $v(a - b) < 1$ and $v(b - c) < 1$ give $v(a - c) < 1$. -/
lemma near_trans {K : Type*} [Field K] [Valued K ℤᵐ⁰] {a b c : K} (h₁ : Valued.v (a - b) < 1)
    (h₂ : Valued.v (b - c) < 1) : Valued.v (a - c) < 1 := by
  have e : a - c = (a - b) + (b - c) := by ring
  rw [e]
  exact Valuation.map_add_lt _ h₁ h₂

/-- If $v(b) = 1$ and $v(a - b) < 1$ then $a / b$ is a square (local square theorem). -/
lemma isSquare_div_of_near {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K]
    (hπ : ∃ π : K, Valued.v π = exp (-1 : ℤ)) (h2 : Valued.v (2 : K) = 1) {a b : K}
    (hb : Valued.v b = 1) (h : Valued.v (a - b) < 1) : IsSquare (a / b) := by
  have hb0 : b ≠ 0 := by rintro rfl; rw [Valuation.map_zero] at hb; exact zero_ne_one hb
  apply FF.isSquare_of_v_sub_one_lt hπ h2
  have e : a / b - 1 = (a - b) / b := by field_simp
  rw [e, map_div₀, hb, div_one]; exact h

lemma two_ne_zero_k (hk : ringChar k ≠ 2) : (2 : k) ≠ 0 := Ring.two_ne_zero hk

/-- The residue field $k[t]/(P)$ is finite when $k$ is. -/
lemma finite_quotient [Finite k] (w : HeightOneSpectrum k[X]) : Finite (k[X] ⧸ w.asIdeal) := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set g := f * C f.leadingCoeff⁻¹ with hg
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf0
  have hgI : g ∈ w.asIdeal := w.asIdeal.mul_mem_right _ hf
  haveI := hgm.finite_quotient
  haveI : Finite (k[X] ⧸ Ideal.span {g}) := Module.finite_of_finite k
  have hle : Ideal.span {g} ≤ w.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hgI
  exact Finite.of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)

/-! ### The finite places -/

section Finite

variable (w : HeightOneSpectrum k[X])

local notation "Kw" => w.adicCompletion (RatFunc k)

lemma v_finite_poly (p : k[X]) :
    Valued.v (algebraMap (RatFunc k) Kw (algebraMap k[X] (RatFunc k) p)) = w.intValuation p := by
  rw [FF.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

/-- **The odd local axioms at a finite place of $k(t)$.** -/
theorem oddLocalAxioms_finite [Fintype k] (hk : ringChar k ≠ 2) : FF.OddLocalAxioms Kw := by
  letI : Field (k[X] ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  haveI := finite_quotient w
  set ρ : k[X] →+* Kw := (algebraMap (RatFunc k) Kw).comp (algebraMap k[X] (RatFunc k)) with hρ
  have hρv : ∀ p, Valued.v (ρ p) = w.intValuation p := fun p => v_finite_poly w p
  set μ : k[X] →+* k[X] ⧸ w.asIdeal := Ideal.Quotient.mk w.asIdeal
  have hker : ∀ r, μ r = 0 ↔ Valued.v (ρ r) < 1 := by
    intro r
    rw [hρv, HeightOneSpectrum.intValuation_lt_one_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  have hκ : ringChar (k[X] ⧸ w.asIdeal) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : k[X] ⧸ w.asIdeal) = 0 := by rw [← h]; exact ringChar.Nat.cast_ringChar
    have : μ (C 2) = 0 := by rw [map_ofNat]; exact_mod_cast h0
    rw [hker, hρv, HeightOneSpectrum.intValuation_lt_one_iff_mem] at this
    have hu : IsUnit (C (2 : k)) := isUnit_C.mpr (Ne.isUnit (two_ne_zero_k hk))
    exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this hu)
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer (RatFunc k)
  have hπ' : ∃ π : Kw, Valued.v π = exp (-1 : ℤ) :=
    ⟨algebraMap _ Kw π, by rw [FF.valued_algebraMap, hπ]⟩
  have h2 : Valued.v (2 : Kw) = 1 := by
    have e : (2 : Kw) = ρ 2 := (map_ofNat ρ 2).symm
    have hu : IsUnit (2 : k[X]) := by
      rw [show (2 : k[X]) = C 2 from (map_ofNat C 2).symm]
      exact isUnit_C.mpr (Ne.isUnit (two_ne_zero_k hk))
    rw [e, hρv]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr (fun hm =>
      w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu))
  refine FF.oddLocalAxioms_of_residue hκ ρ μ Ideal.Quotient.mk_surjective
    (fun r => by rw [hρv]; exact w.intValuation_le_one r) hker hπ' ?_
  intro y hy
  obtain ⟨g, hg⟩ := exists_near (algebraMap (RatFunc k) Kw)
    (HeightOneSpectrum.denseRange_algebraMap _ w) y
  have hgv : Valued.v (algebraMap (RatFunc k) Kw g) ≤ 1 := v_le_one_of_near hy hg
  set p := g.num
  set q := g.denom
  have hq0 : q ≠ 0 := g.denom_ne_zero
  have hgpq : g = algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q :=
    (g.num_div_denom).symm
  have hqK : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hq0
  have hpg : ρ p = algebraMap (RatFunc k) Kw g * ρ q := by
    rw [hρ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hgpq, div_mul_cancel₀ _ hqK]
  -- the denominator is prime to `P`
  have hq : q ∉ w.asIdeal := by
    intro hqm
    have hp : p ∉ w.asIdeal := by
      intro hpm
      obtain ⟨u, v', huv⟩ := g.isCoprime_num_denom
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← huv]
      exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hpm) (w.asIdeal.mul_mem_left _ hqm)
    have h1 : Valued.v (ρ p) = 1 := by
      rw [hρv]; exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hp
    have h2' : Valued.v (ρ q) < 1 := by
      rw [hρv]; exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).mpr hqm
    have : Valued.v (ρ p) < 1 := by
      rw [hpg, map_mul]
      calc Valued.v (algebraMap (RatFunc k) Kw g) * Valued.v (ρ q)
          ≤ 1 * Valued.v (ρ q) := mul_le_mul_left hgv _
        _ < 1 := by rw [one_mul]; exact h2'
    rw [h1] at this; exact lt_irrefl _ this
  have hμq : μ q ≠ 0 := fun h => hq (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨q', hq'⟩ := Ideal.Quotient.mk_surjective (μ q)⁻¹
  have hρq1 : Valued.v (ρ q) = 1 := by
    rw [hρv]; exact HeightOneSpectrum.intValuation_eq_one_iff.mpr hq
  have hρq : ρ q ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hρq1; exact zero_ne_one hρq1
  refine ⟨p * q', near_trans hg ?_⟩
  have e : algebraMap (RatFunc k) Kw g - ρ (p * q') = ρ p * ρ (1 - q * q') / ρ q := by
    rw [map_mul, map_sub, map_one, map_mul, eq_div_iff hρq]
    linear_combination (-1 : Kw) * hpg
  rw [e, map_div₀, hρq1, div_one, map_mul]
  have h1 : Valued.v (ρ (1 - q * q')) < 1 := by
    rw [← hker, map_sub, map_one, map_mul]
    change 1 - μ q * Ideal.Quotient.mk w.asIdeal q' = 0
    rw [hq', mul_inv_cancel₀ hμq, sub_self]
  calc Valued.v (ρ p) * Valued.v (ρ (1 - q * q')) ≤ 1 * Valued.v (ρ (1 - q * q')) :=
        mul_le_mul_left (by rw [hρv]; exact w.intValuation_le_one p) _
    _ < 1 := by rw [one_mul]; exact h1

end Finite

/-! ### The place at infinity -/

section Infinite

local notation "Ki" => RatFunc.CompletionAtInfty k

lemma v_infty (g : RatFunc k) :
    (Valued.v : Valuation Ki ℤᵐ⁰) (algebraMap (RatFunc k) Ki g) = RatFunc.inftyValuation k g :=
  @Valued.valuedCompletion_apply (RatFunc k) _ ℤᵐ⁰ _ (RatFunc.inftyValued k) g

lemma completeSpace_infty : CompleteSpace Ki :=
  @UniformSpace.Completion.completeSpace (RatFunc k) (RatFunc.CompletionAtInfty.instUniformSpace k)

lemma denseRange_infty : DenseRange (algebraMap (RatFunc k) Ki) :=
  @UniformSpace.Completion.denseRange_coe (RatFunc k) (RatFunc.CompletionAtInfty.instUniformSpace k)

lemma v_infty_poly {p : k[X]} (hp : p ≠ 0) :
    RatFunc.inftyValuation k (algebraMap k[X] (RatFunc k) p) = exp (p.natDegree : ℤ) :=
  RatFunc.inftyValuation.polynomial k hp

/-- **Every integral element at infinity is close to a constant:** for $y \in k((t^{-1}))$ with $v_\infty(y) \le 1$
there is $c \in k$ with $v_\infty(y - c) < 1$ (the residue field at $\infty$ is $k$). *Proof:* approximate $y$ by
$g = p/q \in k(t)$ with $\deg p \le \deg q$ and take $c$ the quotient of the coefficients of $t^{\deg q}$. -/
lemma exists_const_near_infty (y : Ki) (hy : Valued.v y ≤ 1) :
    ∃ c : k, Valued.v (y - algebraMap (RatFunc k) Ki (RatFunc.C c)) < 1 := by
  obtain ⟨g, hg⟩ := exists_near (algebraMap (RatFunc k) Ki) denseRange_infty y
  have hgv : Valued.v (algebraMap (RatFunc k) Ki g) ≤ 1 := v_le_one_of_near hy hg
  by_cases hg0 : g = 0
  · refine ⟨0, ?_⟩
    rw [hg0, map_zero] at hg
    rwa [map_zero]
  set p := g.num
  set q := g.denom
  have hq0 : q ≠ 0 := g.denom_ne_zero
  have hp0 : p ≠ 0 := RatFunc.num_ne_zero hg0
  have hgpq : g = algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q :=
    (g.num_div_denom).symm
  have hqK : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr hq0
  have hdeg : p.natDegree ≤ q.natDegree := by
    have h1 := hgv
    rw [v_infty, hgpq, map_div₀, v_infty_poly hp0, v_infty_poly hq0,
      div_le_one₀ (zero_lt_iff.mpr exp_ne_zero), exp_le_exp] at h1
    exact_mod_cast h1
  set d := q.natDegree with hd
  set c : k := p.coeff d / q.leadingCoeff with hc
  refine ⟨c, near_trans hg ?_⟩
  rw [← map_sub, v_infty]
  have e : g - RatFunc.C c = algebraMap k[X] (RatFunc k) (p - C c * q) /
      algebraMap k[X] (RatFunc k) q := by
    rw [hgpq, map_sub, map_mul, sub_div, mul_div_assoc, div_self hqK, mul_one]
    rfl
  rw [e, map_div₀, v_infty_poly hq0]
  by_cases h0 : p - C c * q = 0
  · rw [h0, map_zero, Valuation.map_zero, zero_div]; exact zero_lt_one
  · rw [v_infty_poly h0, div_lt_one₀ (zero_lt_iff.mpr exp_ne_zero), exp_lt_exp]
    have hle : (p - C c * q).natDegree ≤ d :=
      (natDegree_sub_le _ _).trans (max_le hdeg ((natDegree_C_mul_le _ _).trans le_rfl))
    have hcoeff : (p - C c * q).coeff d = 0 := by
      rw [coeff_sub, coeff_C_mul, hc, hd, ← leadingCoeff,
        div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr hq0), sub_self]
    have hne : (p - C c * q).natDegree ≠ d := by
      intro heq
      apply h0
      rw [← leadingCoeff_eq_zero, leadingCoeff, heq, hcoeff]
    exact_mod_cast lt_of_le_of_ne hle hne

/-- **The odd local axioms at the place at infinity of $k(t)$.** -/
theorem oddLocalAxioms_infty [Fintype k] (hk : ringChar k ≠ 2) : FF.OddLocalAxioms Ki := by
  haveI := completeSpace_infty (k := k)
  set ρ : k →+* Ki := (algebraMap (RatFunc k) Ki).comp RatFunc.C with hρ
  have hρv : ∀ c : k, c ≠ 0 → Valued.v (ρ c) = 1 := by
    intro c hc
    rw [hρ, RingHom.comp_apply, v_infty, RatFunc.inftyValuation.C k hc]
  have hρ0 : ∀ c : k, ρ c = 0 ↔ c = 0 := by
    intro c
    constructor
    · intro h; by_contra hc; have := hρv c hc; rw [h, Valuation.map_zero] at this
      exact zero_ne_one this
    · rintro rfl; exact map_zero ρ
  have hker : ∀ r : k, (RingHom.id k) r = 0 ↔ Valued.v (ρ r) < 1 := by
    intro r
    by_cases hr : r = 0
    · simp [hr]
    · simp only [RingHom.id_apply, hr, false_iff, not_lt]; rw [hρv r hr]
  have hπ : ∃ π : Ki, Valued.v π = exp (-1 : ℤ) :=
    ⟨algebraMap _ Ki (1 / RatFunc.X : RatFunc k), by rw [v_infty]; exact RatFunc.inftyValuation.X_inv k⟩
  have h2 : Valued.v (2 : Ki) = 1 := by
    have e : (2 : Ki) = ρ 2 := by rw [map_ofNat]
    rw [e, hρv 2 (two_ne_zero_k hk)]
  refine FF.oddLocalAxioms_of_residue hk ρ (RingHom.id k) Function.surjective_id
    (fun r => by
      by_cases hr : r = 0
      · rw [hr, map_zero, Valuation.map_zero]; exact zero_le_one
      · rw [hρv r hr]) hker hπ ?_
  intro y hy
  obtain ⟨c, hc⟩ := exists_const_near_infty y hy
  exact ⟨c, hc⟩

end Infinite

/-- **The local Hilbert symbol is multiplicative at every place of $\mathbb{F}_q(t)$**, $q$ odd
(O'Meara 63:11 for the completions of $\mathbb{F}_q(t)$; Serre, Ch. III, Thm. 2 for $\mathbb{Q}_p$):
the named input `LocalHilbertMul k`, proved. -/
@[kb "omeara1963" "§63B, 63:11 [unverified] (F = F_q(t)); serre1973 Ch. III §1.2, Thm. 2 [unverified]"]
theorem localHilbertMul [Fintype k] (hk : ringChar k ≠ 2) : LocalHilbertMul k := by
  refine ⟨fun v => ?_⟩
  cases v with
  | finite w => exact fun a b c ha hb hc =>
      (oddLocalAxioms_finite w hk).hilbertSymbol_mul_left a b c ha hb hc
  | infinite => exact fun a b c ha hb hc =>
      (oddLocalAxioms_infty hk).hilbertSymbol_mul_left a b c ha hb hc

end QuadFormsKB.RatFuncPlace
