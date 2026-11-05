import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Basic
import QuadFormsKB.Siegel.Inputs

/-!
# Saha–Hanke, three-term theta relations: irrational relations (Lemma 5.1)

Source: R. Saha and J. Hanke, *On three-term linear relations for theta series of positive-definite
binary quadratic forms*, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §5.1, Lemma 5.1, p. 9.

If $\alpha_1\theta_{Q_1} + \alpha_2\theta_{Q_2} + \alpha_3\theta_{Q_3} = 0$ for positive definite
integral binary forms and some ratio $\alpha_i/\alpha_j$ is irrational, then the three theta series
coincide.

Proof (not the source's, which assumes without loss of generality $\alpha_1,\alpha_2 \ge 0 >
\alpha_3$; no sign normalization is needed). The constant term gives $\alpha_1+\alpha_2+\alpha_3=0$.
For each $m$, with $d_1 = r_{Q_1}(m) - r_{Q_3}(m)$ and $d_2 = r_{Q_2}(m) - r_{Q_3}(m)$ integers,
the relation reads $\alpha_1 d_1 + \alpha_2 d_2 = 0$. If $(d_1, d_2) \ne (0,0)$, then
$(\alpha_1, \alpha_2, \alpha_3)$ is a rational multiple of a single real number, so all defined
ratios $\alpha_i/\alpha_j$ are rational; contradiction.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- **Some ratio of coefficients is irrational** (hypothesis of Lemma 5.1): there are indices
$i, j \in \{0,1,2\}$ (0-based; $\alpha_1, \alpha_2, \alpha_3$ of the paper are `α₁ α₂ α₃` here) with
$\alpha_j \ne 0$ and $\alpha_i/\alpha_j \notin \mathbb{Q}$. -/
def HasIrrationalRatio (α₁ α₂ α₃ : ℝ) : Prop :=
  ∃ i j : Fin 3, (![α₁, α₂, α₃] : Fin 3 → ℝ) j ≠ 0 ∧
    Irrational ((![α₁, α₂, α₃] : Fin 3 → ℝ) i / (![α₁, α₂, α₃] : Fin 3 → ℝ) j)

/-- If the coefficients are rational multiples of one real number, no ratio is irrational. -/
private lemma not_irrational_of_ratmul (α : Fin 3 → ℝ) (q : Fin 3 → ℚ) (t : ℝ)
    (hq : ∀ i, α i = (q i : ℝ) * t) (i j : Fin 3) (hj : α j ≠ 0) :
    ¬ Irrational (α i / α j) := by
  rw [hq j] at hj
  obtain ⟨hqj, ht⟩ := mul_ne_zero_iff.mp hj
  intro hirr
  apply hirr
  refine ⟨q i / q j, ?_⟩
  rw [hq i, hq j]
  push_cast
  field_simp

/-- A nontrivial integer relation $\alpha_1 d_1 + \alpha_2 d_2 = 0$ with $\alpha_1+\alpha_2+\alpha_3=0$
forces all ratios to be rational. -/
private lemma no_irrational_of_int_relation (α₁ α₂ α₃ : ℝ) (d₁ d₂ : ℤ) (hd : d₁ ≠ 0 ∨ d₂ ≠ 0)
    (hs : α₁ + α₂ + α₃ = 0) (he : α₁ * d₁ + α₂ * d₂ = 0) : ¬ HasIrrationalRatio α₁ α₂ α₃ := by
  rintro ⟨i, j, hj, hirr⟩
  by_cases h1 : d₁ = 0
  · have h2 : d₂ ≠ 0 := hd.resolve_left (not_not.mpr h1)
    subst h1
    have hα2 : α₂ = 0 := by
      have : α₂ * (d₂ : ℝ) = 0 := by simpa using he
      exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast h2)
    refine not_irrational_of_ratmul ![α₁, α₂, α₃] ![1, 0, -1] α₁ ?_ i j hj hirr
    intro k
    fin_cases k <;> simp [hα2] <;> linarith
  · have hd1 : (d₁ : ℝ) ≠ 0 := by exact_mod_cast h1
    have hα1 : α₁ = -((d₂ : ℚ) / d₁ : ℚ) * α₂ := by
      push_cast
      field_simp
      linarith
    refine not_irrational_of_ratmul ![α₁, α₂, α₃] ![-((d₂ : ℚ) / d₁), 1, (d₂ : ℚ) / d₁ - 1] α₂
      ?_ i j hj hirr
    intro k
    fin_cases k
    · simpa using hα1
    · simp
    · simp
      push_cast
      have : α₃ = -α₁ - α₂ := by linarith
      rw [this, hα1]
      push_cast
      ring

/-- **Lemma 5.1 (irrational 3-term linear relations).** Let $Q_1, Q_2, Q_3$ be positive definite
integral binary quadratic forms (`IntQF.PosDef`) satisfying the three-term theta relation
$\alpha_1\theta_{Q_1} + \alpha_2\theta_{Q_2} + \alpha_3\theta_{Q_3} = 0$
(`ThetaRelation3`, i.e. $\alpha_1 r_{Q_1}(m) + \alpha_2 r_{Q_2}(m) + \alpha_3 r_{Q_3}(m) = 0$ for all
$m \ge 0$), with real coefficients $\alpha_1,\alpha_2,\alpha_3$ such that some ratio
$\alpha_i/\alpha_j$ with $\alpha_j \ne 0$ is irrational (`HasIrrationalRatio`). Then the three theta
series are equal: $r_{Q_1}(m) = r_{Q_2}(m) = r_{Q_3}(m)$ for every $m \ge 0$. -/
@[kb "hanke2023threeterm" "§5.1, Lemma 5.1, p. 9"]
theorem irrational_three_term {Q₁ Q₂ Q₃ : BinQF} (hp₁ : IntQF.PosDef Q₁) (hp₂ : IntQF.PosDef Q₂)
    (hp₃ : IntQF.PosDef Q₃) {α₁ α₂ α₃ : ℝ} (h : ThetaRelation3 Q₁ Q₂ Q₃ α₁ α₂ α₃)
    (hirr : HasIrrationalRatio α₁ α₂ α₃) :
    (∀ m : ℕ, repNum Q₁ m = repNum Q₂ m) ∧ (∀ m : ℕ, repNum Q₂ m = repNum Q₃ m) := by
  have hs : α₁ + α₂ + α₃ = 0 := by
    have := h 0
    simpa [repNum_zero hp₁, repNum_zero hp₂, repNum_zero hp₃] using this
  have key : ∀ m : ℕ, repNum Q₁ m = repNum Q₃ m ∧ repNum Q₂ m = repNum Q₃ m := by
    intro m
    by_contra hne
    apply no_irrational_of_int_relation α₁ α₂ α₃ ((repNum Q₁ m : ℤ) - repNum Q₃ m)
      ((repNum Q₂ m : ℤ) - repNum Q₃ m) ?_ hs ?_ hirr
    · by_contra hc
      push_neg at hc
      apply hne
      constructor <;> omega
    · have := h m
      push_cast
      linear_combination this - (repNum Q₃ (m : ℤ) : ℝ) * hs
  exact ⟨fun m => by rw [(key m).1, (key m).2], fun m => by rw [(key m).2]⟩

end QuadFormsKB.Hanke2023ThreeTerm
