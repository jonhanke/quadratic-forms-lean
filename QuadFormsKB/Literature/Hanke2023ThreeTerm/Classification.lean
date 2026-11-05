import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Reduced
import QuadFormsKB.Literature.Hanke2023ThreeTerm.KeyLemma
import QuadFormsKB.Literature.Cassels.Ch9Examples8
import QuadFormsKB.Equiv.Binary

/-!
# Saha–Hanke: relations with $a + b = 1$ and $a + b \ge 4$ (§6.1, Lemma 6.4)

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §6.1 and §6.4.

For coprime $a, b \ge 0$ the normalized relation (6) $\frac{a}{a+b}\theta_{Q_1} +
\frac{b}{a+b}\theta_{Q_2} = \theta_{Q_3}$ among reduced forms is equivalent (Lemma 3.3) to
$a\, r^{\tilde *}_{Q_1}(m) + b\, r^{\tilde *}_{Q_2}(m) = (a+b)\, r^{\tilde *}_{Q_3}(m)$ for all $m$.

* $a + b = 1$ (§6.1, $\theta_{Q_1} = \theta_{Q_3}$): reduced forms with the same theta series are
  equal (`reduced_eq_of_theta_eq`). This is Schiemann's two-term result in dimension $2$.
* $a + b \ge 4$ (Lemma 6.4): every reduced solution is diagonal, $Q_1 = Q_2 = Q_3$
  (`reduced_diagonal_of_ge_four`).

## Proof

*Update (proof route):* the source obtains both statements by running its Extended Refinement
Algorithm (by computer for $a + b = 1$: 13 iterations, then an argument discarding the $Q_2$ data;
for $a + b \ge 4$ the zero-cone computations of Cases 2a–2c). Here they are proved directly, with
the same key input as Cases 2a–2c: a reduced form has at most three strongly primitive
representations of any $m \le d = a + c - b$ (`lt_of_four_le`), and the first three strongly
primitive values $a \le c \le d$ determine the form (`eq_of_spRepNum_eq`). Let $m^*$ be the first
$m$ at which $r^{\tilde *}_{Q_1}(m), r^{\tilde *}_{Q_2}(m), r^{\tilde *}_{Q_3}(m)$ are not all equal.
By the Key Lemma (5.7) one of them is $\ge a + b \ge 4$, so that form has $d < m^*$; since all three
counts agree below $m^*$, all three forms have $d < m^*$, hence are equal.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm

open QuadFormsKB QuadFormsKB.Siegel

/-- If $f$ is reduced with $d_f < M$ and $g$ is reduced with the same strongly primitive counts
below $M$, then also $d_g < M$. -/
lemma dval_lt_of_agree {f g : BinQF} (hf : IsReduced f) (hg : IsReduced g) {M : ℕ}
    (hfM : dval f < M) (h : ∀ m : ℕ, m < M → spRepNum f m = spRepNum g m) : dval g < M := by
  obtain ⟨f0, f1, f2, f3⟩ := hf
  have hdf := dval_ge ⟨f0, f1, f2, f3⟩
  obtain ⟨t, rfl⟩ : ∃ t, M = t + 1 := ⟨M - 1, by omega⟩
  have hc : spCount f t = spCount g t := by
    refine Finset.sum_congr rfl fun m hm => h m ?_
    have := Finset.mem_range.1 hm; omega
  have h3 := spCount_ge ⟨f0, f1, f2, f3⟩ t
  rw [if_pos (by push_cast at hfM ⊢; omega), if_pos (by push_cast at hfM ⊢; omega),
    if_pos (by push_cast at hfM ⊢; omega), hc] at h3
  by_contra hlt; push Not at hlt
  rw [spCount_lt hg (by push_cast at hlt ⊢; omega)] at h3
  split_ifs at h3 <;> omega

/-- A bound $M$ above $d_f$ and $d_g$. -/
lemma exists_bound (f g h : BinQF) : ∃ M : ℕ, dval f < M ∧ dval g < M ∧ dval h < M :=
  ⟨(max (max (dval f) (dval g)) (dval h)).toNat + 1, by omega, by omega, by omega⟩

/-- **§6.1 ($a + b = 1$): reduced forms with equal strongly primitive counts are equal.** -/
theorem reduced_eq_of_spRepNum_eq {f g : BinQF} (hf : IsReduced f) (hg : IsReduced g)
    (h : ∀ m : ℕ, spRepNum f m = spRepNum g m) : f = g := by
  obtain ⟨M, h1, h2, -⟩ := exists_bound f g g
  exact eq_of_spRepNum_eq hf hg h1 h2 fun m _ => h m

/-- **§6.1 ($a + b = 1$, $\theta_{Q_1} = \theta_{Q_3}$).** Two reduced integral binary forms with
the same theta series (i.e. $r_{Q_1}(m) = r_{Q_3}(m)$ for all $m \ge 0$) are equal. -/
@[kb "hanke2023threeterm" "§6.1, p. 16"]
theorem reduced_eq_of_theta_eq {Q₁ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₃ : IsReduced Q₃)
    (h : ∀ m : ℕ, repNum Q₁ m = repNum Q₃ m) : Q₁ = Q₃ := by
  have hrel : ThetaRelation3 Q₁ Q₁ Q₃ 1 0 (-1) := fun m => by rw [h m]; ring
  have hs := (lemma_3_3 h₁.posDef h₁.posDef h₃.posDef (by norm_num)).1 hrel
  refine reduced_eq_of_spRepNum_eq h₁ h₃ fun m => ?_
  have := hs m
  have : (spRepNum Q₁ m : ℝ) = spRepNum Q₃ m := by linarith
  exact_mod_cast this

/-- **Lemma 6.4 (no non-trivial solutions for $a + b \ge 4$), strongly primitive form.** Let
$a, b \ge 0$ be coprime with $a + b \ge 4$, and let $Q_1, Q_2, Q_3$ be reduced integral binary
forms with $a\, r^{\tilde *}_{Q_1}(m) + b\, r^{\tilde *}_{Q_2}(m) = (a+b)\, r^{\tilde *}_{Q_3}(m)$
for all $m \ge 0$. Then $Q_1 = Q_2 = Q_3$. -/
theorem reduced_diagonal_of_ge_four_sp {a b : ℕ} (hcop : Nat.Coprime a b) (hab : 4 ≤ a + b)
    {Q₁ Q₂ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₂ : IsReduced Q₂) (h₃ : IsReduced Q₃)
    (h : ∀ m : ℕ, a * spRepNum Q₁ m + b * spRepNum Q₂ m = (a + b) * spRepNum Q₃ m) :
    Q₁ = Q₂ ∧ Q₂ = Q₃ := by
  classical
  by_cases hall : ∀ m : ℕ, spRepNum Q₁ m = spRepNum Q₃ m ∧ spRepNum Q₂ m = spRepNum Q₃ m
  · have e13 := reduced_eq_of_spRepNum_eq h₁ h₃ fun m => (hall m).1
    have e23 := reduced_eq_of_spRepNum_eq h₂ h₃ fun m => (hall m).2
    exact ⟨e13.trans e23.symm, e23⟩
  push Not at hall
  let M := Nat.find hall
  have hM := Nat.find_spec hall
  have hbelow : ∀ m : ℕ, m < M → spRepNum Q₁ m = spRepNum Q₃ m ∧ spRepNum Q₂ m = spRepNum Q₃ m :=
    fun m hm => by
      have := Nat.find_min hall hm
      push Not at this
      exact this
  obtain ⟨c₁, c₂, c₃, e1, e2, e3⟩ := key_coprime a b _ _ _ hcop (h M)
  have hc : c₂ ≠ 0 ∨ c₃ ≠ 0 := by
    by_contra hc; push Not at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp at e1 e2 e3
    exact hM (by rw [e1, e3]) (by rw [e2, e3])
  -- the form with ≥ 4 strongly primitive representations at M has d < M
  have hd : dval Q₁ < M ∨ dval Q₂ < M := by
    rcases hc with hc | hc
    · left
      exact lt_of_four_le h₁ (by
        have : 1 ≤ c₂ := Nat.one_le_iff_ne_zero.2 hc
        rw [e1]; nlinarith)
    · right
      exact lt_of_four_le h₂ (by
        have : 1 ≤ c₃ := Nat.one_le_iff_ne_zero.2 hc
        rw [e2]; nlinarith)
  have h13 : ∀ m : ℕ, m < M → spRepNum Q₁ m = spRepNum Q₃ m := fun m hm => (hbelow m hm).1
  have h23 : ∀ m : ℕ, m < M → spRepNum Q₂ m = spRepNum Q₃ m := fun m hm => (hbelow m hm).2
  have hd3 : dval Q₃ < M := by
    rcases hd with hd | hd
    · exact dval_lt_of_agree h₁ h₃ hd h13
    · exact dval_lt_of_agree h₂ h₃ hd h23
  have hd1 : dval Q₁ < M := dval_lt_of_agree h₃ h₁ hd3 fun m hm => (h13 m hm).symm
  have hd2 : dval Q₂ < M := dval_lt_of_agree h₃ h₂ hd3 fun m hm => (h23 m hm).symm
  have e13 := eq_of_spRepNum_eq h₁ h₃ hd1 hd3 h13
  have e23 := eq_of_spRepNum_eq h₂ h₃ hd2 hd3 h23
  exact ⟨e13.trans e23.symm, e23⟩

/-- **Lemma 6.4 ($a + b \ge 4$: only diagonal solutions).** Let $a, b \ge 0$ be coprime with
$a + b \ge 4$, and let $Q_1, Q_2, Q_3$ be reduced integral binary forms satisfying the normalized
relation (6), $\frac{a}{a+b}\theta_{Q_1} + \frac{b}{a+b}\theta_{Q_2} = \theta_{Q_3}$
(coefficientwise). Then $Q_1 = Q_2 = Q_3$, i.e. $(Q_1, Q_2, Q_3) \in \Delta$. -/
@[kb "hanke2023threeterm" "§6.4, Lemma 6.4, p. 18"]
theorem reduced_diagonal_of_ge_four {a b : ℕ} (hcop : Nat.Coprime a b) (hab : 4 ≤ a + b)
    {Q₁ Q₂ Q₃ : BinQF} (h₁ : IsReduced Q₁) (h₂ : IsReduced Q₂) (h₃ : IsReduced Q₃)
    (h : ThetaRelation3 Q₁ Q₂ Q₃ ((a : ℝ) / (a + b)) ((b : ℝ) / (a + b)) (-1)) :
    Q₁ = Q₂ ∧ Q₂ = Q₃ := by
  have hpos : (0 : ℝ) < a + b := by exact_mod_cast (show 0 < a + b by omega)
  have hsum : (a : ℝ) / (a + b) + (b : ℝ) / (a + b) + (-1) = 0 := by
    field_simp; ring
  have hs := (lemma_3_3 h₁.posDef h₂.posDef h₃.posDef hsum).1 h
  refine reduced_diagonal_of_ge_four_sp hcop hab h₁ h₂ h₃ fun m => ?_
  have e := hs m
  have : (a : ℝ) * spRepNum Q₁ m + b * spRepNum Q₂ m = (a + b) * spRepNum Q₃ m := by
    field_simp at e; linarith
  exact_mod_cast this

end QuadFormsKB.Hanke2023ThreeTerm
