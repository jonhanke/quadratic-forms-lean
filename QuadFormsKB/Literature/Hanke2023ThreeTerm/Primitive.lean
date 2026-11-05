import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Basic
import QuadFormsKB.Literature.Hanke2023ThreeTerm.NonTrivialRelation
import QuadFormsKB.Siegel.Inputs

/-!
# Saha–Hanke, Lemma 3.3: theta series and strongly primitive theta series

Source: R. Saha and J. Hanke, arXiv:2307.00747v1, §3.1, Lemma 3.3, pp. 4–5
(bib key `hanke2023threeterm`).

Every non-zero $v \in \mathbb{Z}^2$ is uniquely $v = \pm g\, w$ with $g = \gcd(v) \ge 1$ and $w$
strongly primitive, and $Q(v) = g^2 Q(w)$. Hence for $m \ge 1$
$$r_Q(m) = \sum_{g \ge 1,\ g^2 \mid m} 2\, r^{\tilde *}_Q(m / g^2)$$
(`repNum_eq_sum_spRepNum`), and a linear relation among the $r_{Q_i}$ is equivalent to the same
relation among the $r^{\tilde *}_{Q_i}$ when $\sum_i \alpha_i = 0$ (Lemma 3.3,
`lemma_3_3`).

*Erratum (Lemma 3.3, proof):* the source writes $r_{Q_i}(m) = \sum_{d \mid m} 2 r^{\tilde *}_{Q_i}(d)$
and inverts it with the Möbius function over all divisors. The correct decomposition runs over the
square divisors, $r_Q(m) = \sum_{g^2 \mid m} 2 r^{\tilde *}_Q(m/g^2)$, since $Q(g w) = g^2 Q(w)$
(e.g. $Q = x^2 + y^2$, $m = 2$: $r_Q(2) = 4$, while $\sum_{d \mid 2} 2 r^{\tilde *}_Q(d) =
2(1 + 2) = 6$). The statement of Lemma 3.3 is unaffected; the inversion is done here by strong
induction on $m$.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- The square divisors of $m$: the $g \in \{1, \dots, |m|\}$ with $g^2 \mid m$. -/
def sqDivisors (m : ℤ) : Finset ℕ :=
  (Finset.Icc 1 m.natAbs).filter fun g => ((g : ℤ) ^ 2 ∣ m)

lemma mem_sqDivisors {m : ℤ} (hm : m ≠ 0) {g : ℕ} :
    g ∈ sqDivisors m ↔ 1 ≤ g ∧ (g : ℤ) ^ 2 ∣ m := by
  simp only [sqDivisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have h3 : ((g : ℤ) ^ 2).natAbs ∣ m.natAbs := Int.natAbs_dvd_natAbs.2 h2
    have h4 := Nat.le_of_dvd (Int.natAbs_pos.2 hm) h3
    have : g ≤ g ^ 2 := by nlinarith
    simp [Int.natAbs_pow] at h4
    omega

/-- `Q (g • w) = g² Q(w)`. -/
lemma eval_smul (Q : BinQF) (g x y : ℤ) : Q.eval (g * x) (g * y) = g ^ 2 * Q.eval x y := by
  simp only [BinQF.eval_eq]; ring

lemma eval_neg (Q : BinQF) (x y : ℤ) : Q.eval (-x) (-y) = Q.eval x y := by
  simp only [BinQF.eval_eq]; ring

lemma eval_zero (Q : BinQF) : Q.eval 0 0 = 0 := by simp [BinQF.eval_eq]

/-- A primitive vector $w$ ($\gcd = 1$) is strongly primitive or its negative is, and not both. -/
lemma sp_or_neg_sp {w : ℤ × ℤ} (hw : Int.gcd w.1 w.2 = 1) :
    StronglyPrimitive w ∨ StronglyPrimitive (-w.1, -w.2) := by
  have hn : Int.gcd (-w.1) (-w.2) = 1 := by rw [Int.neg_gcd, Int.gcd_neg]; exact hw
  unfold StronglyPrimitive
  rcases lt_trichotomy w.2 0 with h | h | h
  · exact Or.inr ⟨hn, Or.inl (by simp only; omega)⟩
  · have : w.1 ≠ 0 := by
      intro h1; rw [h1, h] at hw; simp at hw
    rcases lt_or_gt_of_ne this with h1 | h1
    · exact Or.inr ⟨hn, Or.inr ⟨by simp only; omega, by simp only; omega⟩⟩
    · exact Or.inl ⟨hw, Or.inr ⟨h, h1⟩⟩
  · exact Or.inl ⟨hw, Or.inl h⟩

lemma not_sp_and_neg_sp {w : ℤ × ℤ} (h1 : StronglyPrimitive w)
    (h2 : StronglyPrimitive (-w.1, -w.2)) : False := by
  unfold StronglyPrimitive at h1 h2
  simp only [neg_pos, neg_eq_zero] at h2
  omega

lemma sp_ne_zero {w : ℤ × ℤ} (h : StronglyPrimitive w) : w ≠ (0, 0) := by
  rintro rfl; simp [StronglyPrimitive] at h

/-- $R_Q(m)$ as a subset of $\mathbb{Z}^n$ (`repSet`) and as pairs $(x, y)$. -/
def repSetEquiv (Q : BinQF) (k : ℤ) : (repSet Q k) ≃ {v : ℤ × ℤ // Q.eval v.1 v.2 = k} where
  toFun x := ⟨(x.1 0, x.1 1), by
    have h := x.2
    simp only [repSet, Set.mem_ofPred_eq] at h
    have hx : (![x.1 0, x.1 1] : Fin 2 → ℤ) = x.1 := by
      funext i; fin_cases i <;> rfl
    simp only [BinQF.eval, hx]; exact h⟩
  invFun p := ⟨![p.1.1, p.1.2], p.2⟩
  left_inv x := by ext1; funext i; fin_cases i <;> rfl
  right_inv p := by ext <;> rfl

lemma finite_rep (Q : BinQF) (hQ : IntQF.PosDef Q) (k : ℤ) :
    Finite {v : ℤ × ℤ // Q.eval v.1 v.2 = k} := by
  have : Finite (repSet Q k) := (IntQF.PosDef.repSet_finite hQ k).to_subtype
  exact Finite.of_equiv _ (repSetEquiv Q k)

lemma finite_sp (Q : BinQF) (hQ : IntQF.PosDef Q) (k : ℤ) :
    Finite {w : ℤ × ℤ // StronglyPrimitive w ∧ Q.eval w.1 w.2 = k} := by
  have := finite_rep Q hQ k
  exact Finite.of_injective (fun w => (⟨w.1, w.2.2⟩ : {v : ℤ × ℤ // Q.eval v.1 v.2 = k}))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- The target of the decomposition: triples $(g, \pm, w)$ with $g^2 \mid m$ and $w$ strongly
primitive with $Q(w) = m / g^2$. -/
abbrev DecompT (Q : BinQF) (m : ℤ) : Type :=
  Σ g : sqDivisors m, Bool × {w : ℤ × ℤ // StronglyPrimitive w ∧
    Q.eval w.1 w.2 = m / ((g : ℕ) : ℤ) ^ 2}

/-- The sign $\pm 1$ attached to a Boolean. -/
def sgn (s : Bool) : ℤ := if s then 1 else -1

lemma sgn_sq (s : Bool) : sgn s ^ 2 = 1 := by cases s <;> simp [sgn]

lemma sgn_natAbs (s : Bool) : (sgn s).natAbs = 1 := by cases s <;> simp [sgn]

/-- The composition map $(g, \pm, w) \mapsto \pm g w$. -/
def compose (Q : BinQF) {m : ℤ} (hm : m ≠ 0) (t : DecompT Q m) :
    {v : ℤ × ℤ // Q.eval v.1 v.2 = m} :=
  ⟨(sgn t.2.1 * (t.1 : ℕ) * t.2.2.1.1, sgn t.2.1 * (t.1 : ℕ) * t.2.2.1.2), by
    have hg' := (mem_sqDivisors hm).1 t.1.2
    rw [eval_smul, t.2.2.2.2, mul_pow, sgn_sq, one_mul]
    exact Int.mul_ediv_cancel' hg'.2⟩

lemma gcd_compose (Q : BinQF) {m : ℤ} (hm : m ≠ 0) (t : DecompT Q m) :
    Int.gcd (compose Q hm t).1.1 (compose Q hm t).1.2 = (t.1 : ℕ) := by
  simp only [compose]
  rw [Int.gcd_mul_left, t.2.2.2.1.1, Int.natAbs_mul, sgn_natAbs]
  simp

lemma compose_bijective (Q : BinQF) {m : ℤ} (hm : m ≠ 0) : Function.Bijective (compose Q hm) := by
  constructor
  · rintro ⟨⟨g, hg⟩, s, w, hw, hwv⟩ ⟨⟨g', hg'⟩, s', w', hw', hwv'⟩ h
    have hgg : g = g' := by
      have h1 := gcd_compose Q hm ⟨⟨g, hg⟩, s, w, hw, hwv⟩
      have h2 := gcd_compose Q hm ⟨⟨g', hg'⟩, s', w', hw', hwv'⟩
      rw [h] at h1; rw [h1] at h2; exact h2
    subst hgg
    have hgpos : (0 : ℤ) < g := by exact_mod_cast ((mem_sqDivisors hm).1 hg).1
    simp only [compose, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : sgn s * w.1 = sgn s' * w'.1 := by
      apply mul_left_cancel₀ hgpos.ne'; linear_combination h1
    have e2 : sgn s * w.2 = sgn s' * w'.2 := by
      apply mul_left_cancel₀ hgpos.ne'; linear_combination h2
    by_cases hs : s = s'
    · subst hs
      have hσ : sgn s ≠ 0 := by cases s <;> simp [sgn]
      have : w = w' := Prod.ext (mul_left_cancel₀ hσ e1) (mul_left_cancel₀ hσ e2)
      subst this; rfl
    · exfalso
      have hw'' : w' = (-w.1, -w.2) := by
        cases s <;> cases s' <;> simp [sgn] at e1 e2 hs <;>
          exact Prod.ext (by simp; linarith) (by simp; linarith)
      rw [hw''] at hw'
      exact not_sp_and_neg_sp hw hw'
  · rintro ⟨v, hv⟩
    have hv0 : v ≠ (0, 0) := by
      intro h; rw [h, eval_zero] at hv; exact hm hv.symm
    have hg : 0 < Int.gcd v.1 v.2 := Int.gcd_pos_iff.2 (by
      by_contra h; push Not at h; exact hv0 (Prod.ext h.1 h.2))
    have hw : Int.gcd (v.1 / Int.gcd v.1 v.2) (v.2 / Int.gcd v.1 v.2) = 1 :=
      Int.gcd_div_gcd_div_gcd hg
    have hvw : v = ((Int.gcd v.1 v.2 : ℤ) * (v.1 / Int.gcd v.1 v.2),
        (Int.gcd v.1 v.2 : ℤ) * (v.2 / Int.gcd v.1 v.2)) := by
      ext
      · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
      · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
    generalize Int.gcd v.1 v.2 = g at hg hw hvw
    obtain ⟨w, hw', hvw⟩ : ∃ w : ℤ × ℤ, Int.gcd w.1 w.2 = 1 ∧ v = ((g : ℤ) * w.1, (g : ℤ) * w.2) :=
      ⟨(v.1 / g, v.2 / g), hw, hvw⟩
    clear hw
    have hQ : Q.eval v.1 v.2 = (g : ℤ) ^ 2 * Q.eval w.1 w.2 := by
      rw [hvw]; exact eval_smul Q _ _ _
    have hgm : g ∈ sqDivisors m := (mem_sqDivisors hm).2 ⟨hg, ⟨_, hv ▸ hQ⟩⟩
    have hval : Q.eval w.1 w.2 = m / (g : ℤ) ^ 2 := by
      rw [← hv, hQ, Int.mul_ediv_cancel_left]
      exact pow_ne_zero _ (by exact_mod_cast hg.ne')
    rcases sp_or_neg_sp hw' with hs | hs
    · refine ⟨⟨⟨g, hgm⟩, true, ⟨w, hs, hval⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [compose, sgn, ite_true, one_mul]
      exact hvw.symm
    · refine ⟨⟨⟨g, hgm⟩, false, ⟨(-w.1, -w.2), hs, by rw [eval_neg]; exact hval⟩⟩, ?_⟩
      apply Subtype.ext
      simp only [compose, sgn]
      rw [hvw]; ext <;> simp

/-- The decomposition $v = \pm g w$, as an equivalence for $m \ne 0$:
$R_Q(m) \simeq \coprod_{g^2 \mid m} \{\pm 1\} \times R^{\tilde *}_Q(m/g^2)$. -/
noncomputable def repDecomp (Q : BinQF) {m : ℤ} (hm : m ≠ 0) :
    {v : ℤ × ℤ // Q.eval v.1 v.2 = m} ≃ DecompT Q m :=
  (Equiv.ofBijective _ (compose_bijective Q hm)).symm

/-- **Lemma 3.3, decomposition (corrected).** For a positive definite integral binary form $Q$ and
$m \ne 0$, $r_Q(m) = \sum_{g \ge 1,\ g^2 \mid m} 2\, r^{\tilde *}_Q(m/g^2)$. -/
@[kb "hanke2023threeterm" "§3.1, proof of Lemma 3.3, p. 4"]
theorem repNum_eq_sum_spRepNum (Q : BinQF) (hQ : IntQF.PosDef Q) {m : ℤ} (hm : m ≠ 0) :
    repNum Q m = ∑ g ∈ sqDivisors m, 2 * spRepNum Q (m / (g : ℤ) ^ 2) := by
  have := fun k => finite_sp Q hQ k
  rw [repNum_eq_card_prod, Nat.card_congr (repDecomp Q hm), Nat.card_sigma]
  rw [← Finset.sum_coe_sort (sqDivisors m)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  rfl


lemma spRepNum_nonpos (Q : BinQF) (hQ : IntQF.PosDef Q) {m : ℤ} (hm : m ≤ 0) :
    spRepNum Q m = 0 := by
  rw [spRepNum, Nat.card_eq_zero]
  left
  constructor
  rintro ⟨w, hw, hv⟩
  have hw0 := sp_ne_zero hw
  have := hQ ![w.1, w.2] (by
    intro h
    apply hw0
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact Prod.ext h0 h1)
  have : 0 < Q.eval w.1 w.2 := this
  omega

/-- The linear combination $\sum_i \alpha_i r^{\tilde *}_{Q_i}(k)$. -/
noncomputable def spComb (Q₁ Q₂ Q₃ : BinQF) (α₁ α₂ α₃ : ℝ) (k : ℤ) : ℝ :=
  α₁ * spRepNum Q₁ k + α₂ * spRepNum Q₂ k + α₃ * spRepNum Q₃ k

lemma comb_eq_sum (Q₁ Q₂ Q₃ : BinQF) (h₁ : IntQF.PosDef Q₁) (h₂ : IntQF.PosDef Q₂)
    (h₃ : IntQF.PosDef Q₃) (α₁ α₂ α₃ : ℝ) {m : ℤ} (hm : m ≠ 0) :
    α₁ * repNum Q₁ m + α₂ * repNum Q₂ m + α₃ * repNum Q₃ m =
      ∑ g ∈ sqDivisors m, 2 * spComb Q₁ Q₂ Q₃ α₁ α₂ α₃ (m / (g : ℤ) ^ 2) := by
  rw [repNum_eq_sum_spRepNum Q₁ h₁ hm, repNum_eq_sum_spRepNum Q₂ h₂ hm,
    repNum_eq_sum_spRepNum Q₃ h₃ hm]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [spComb]; ring

/-- **Lemma 3.3 (relating $\theta_Q$ and $\theta^{\tilde *}_Q$).** Let $Q_1, Q_2, Q_3$ be positive
definite integral binary forms and $\alpha_1, \alpha_2, \alpha_3 \in \mathbb{R}$ with
$\alpha_1 + \alpha_2 + \alpha_3 = 0$. Then $\alpha_1 \theta_{Q_1} + \alpha_2 \theta_{Q_2} +
\alpha_3 \theta_{Q_3} = 0$ (coefficientwise, `ThetaRelation3`) if and only if
$\alpha_1 \theta^{\tilde *}_{Q_1} + \alpha_2 \theta^{\tilde *}_{Q_2} + \alpha_3 \theta^{\tilde *}_{Q_3}
= 0$, i.e. $\sum_i \alpha_i r^{\tilde *}_{Q_i}(m) = 0$ for every $m \ge 0$. -/
@[kb "hanke2023threeterm" "§3.1, Lemma 3.3, p. 4"]
theorem lemma_3_3 {Q₁ Q₂ Q₃ : BinQF} (h₁ : IntQF.PosDef Q₁) (h₂ : IntQF.PosDef Q₂)
    (h₃ : IntQF.PosDef Q₃) {α₁ α₂ α₃ : ℝ} (hα : α₁ + α₂ + α₃ = 0) :
    ThetaRelation3 Q₁ Q₂ Q₃ α₁ α₂ α₃ ↔
      ∀ m : ℕ, α₁ * spRepNum Q₁ m + α₂ * spRepNum Q₂ m + α₃ * spRepNum Q₃ m = 0 := by
  constructor
  · intro h m
    show spComb Q₁ Q₂ Q₃ α₁ α₂ α₃ m = 0
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [spComb, spRepNum_nonpos _ h₁ le_rfl, spRepNum_nonpos _ h₂ le_rfl,
          spRepNum_nonpos _ h₃ le_rfl]
      have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
      have e := h m
      rw [comb_eq_sum Q₁ Q₂ Q₃ h₁ h₂ h₃ α₁ α₂ α₃ hm'] at e
      have h1 : (1 : ℕ) ∈ sqDivisors m := (mem_sqDivisors hm').2 ⟨le_rfl, by simp⟩
      rw [Finset.sum_eq_single_of_mem 1 h1] at e
      · simpa using e
      · intro g hg hg1
        obtain ⟨hg1', k, hk⟩ := (mem_sqDivisors hm').1 hg
        have hgpos : (0 : ℤ) < (g : ℤ) ^ 2 := by positivity
        have hkm : (m : ℤ) / (g : ℤ) ^ 2 = k := by
          rw [hk, Int.mul_ediv_cancel_left _ hgpos.ne']
        rw [hkm]
        have hk0 : 0 < k := by
          by_contra hk0; push Not at hk0
          have : (m : ℤ) ≤ 0 := by rw [hk]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le hk0
          omega
        have hg2 : 2 ≤ g := by omega
        have hklt : k < m := by
          have : (4 : ℤ) ≤ (g : ℤ) ^ 2 := by
            have : (2 : ℤ) ≤ g := by exact_mod_cast hg2
            nlinarith
          rw [hk]; nlinarith
        lift k to ℕ using hk0.le
        have := ih k (by exact_mod_cast hklt)
        simp [this]
  · intro h m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [repNum_zero h₁, repNum_zero h₂, repNum_zero h₃]; linarith
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [comb_eq_sum Q₁ Q₂ Q₃ h₁ h₂ h₃ α₁ α₂ α₃ hm']
    refine Finset.sum_eq_zero fun g hg => ?_
    obtain ⟨_, k, hk⟩ := (mem_sqDivisors hm').1 hg
    have hgpos : (0 : ℤ) < (g : ℤ) ^ 2 := by
      have := ((mem_sqDivisors hm').1 hg).1; positivity
    have hkm : (m : ℤ) / (g : ℤ) ^ 2 = k := by
      rw [hk, Int.mul_ediv_cancel_left _ hgpos.ne']
    rw [hkm]
    rcases le_or_gt k 0 with hk0 | hk0
    · simp [spComb, spRepNum_nonpos _ h₁ hk0, spRepNum_nonpos _ h₂ hk0, spRepNum_nonpos _ h₃ hk0]
    · lift k to ℕ using hk0.le
      have := h k
      simp only [spComb]; rw [this, mul_zero]

end QuadFormsKB.Hanke2023ThreeTerm
