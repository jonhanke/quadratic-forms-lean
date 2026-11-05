import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2023ThreeTerm.Reduced
import QuadFormsKB.Literature.Hanke2023ThreeTerm.RefinementDefs

/-!
# Saha–Hanke §6.2–6.3: the cumulative strongly primitive count and the twelve vectors $V$

Source: R. Saha and J. Hanke, arXiv:2307.00747v1 (bib key `hanke2023threeterm`), §3.3 and §5.3.

For a reduced form $f = [a, b, c]$ let $N_f(t) = \sum_{0 \le m \le t} r^{\tilde *}_f(m)$ (`spCountZ`, the number of
strongly primitive vectors $v$ with $f(v) \le t$). With $V$ the twelve strongly primitive vectors of
`RefinementDefs.lean`:

* `value_ge_of_not_mem_V`: every strongly primitive $v \notin V$ has $f(v) \ge 16a - 4b + c$ or $f(v) \ge 6c$;
* `cntV_le_spCountZ`: $N_f(t) \ge \#\{v \in V : f(v) \le t\} = $ `cntV a b c t`;
* `spCountZ_eq_cntV`: equality for $t < 16a - 4b + c$ and $t < 6c$.

These are the only facts about binary forms used by the case trees (`RefinementAB11.lean`, `RefinementAB12.lean`);
they play the role of the source's successive minima and K-sets (§3.3, §4) for the first twelve values.
-/

namespace QuadFormsKB.Hanke2023ThreeTerm.Refinement

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Hanke2023ThreeTerm

/-- The twelve strongly primitive vectors $V$. -/
def Vset : Finset (ℤ × ℤ) :=
  {(1, 0), (0, 1), (-1, 1), (1, 1), (-2, 1), (2, 1), (-3, 1), (3, 1), (-1, 2), (1, 2), (-3, 2), (3, 2)}

lemma sp_of_mem_Vset {v : ℤ × ℤ} (hv : v ∈ Vset) : StronglyPrimitive v := by
  simp only [Vset, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [StronglyPrimitive] <;> decide

/-- **Strongly primitive vectors outside $V$ have large values:** for $f$ reduced and $v \notin V$ strongly
primitive, $f(v) \ge 16a - 4b + c$ or $f(v) \ge 6c$. -/
theorem value_ge_of_not_mem_V {f : BinQF} (hf : IsReduced f) {v : ℤ × ℤ} (hv : StronglyPrimitive v)
    (hV : v ∉ Vset) : 16 * f.a - 4 * f.b + f.c ≤ f.eval v.1 v.2 ∨ 6 * f.c ≤ f.eval v.1 v.2 := by
  obtain ⟨hb0, hba, hac, ha⟩ := hf
  obtain ⟨x, y⟩ := v
  obtain ⟨hg, hpos⟩ := hv
  simp only at hg hpos
  rw [BinQF.eval_eq]
  simp only [Vset, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hV
  rcases hpos with hy | ⟨rfl, hx⟩
  · rcases (show y = 1 ∨ y = 2 ∨ 3 ≤ y by omega) with rfl | rfl | hy3
    · -- y = 1, |x| ≥ 4
      left
      dsimp only
      have hx4 : 4 ≤ x ∨ x ≤ -4 := by omega
      rcases hx4 with hx4 | hx4
      · nlinarith [mul_nonneg ha.le (show (0 : ℤ) ≤ (x - 4) * (x + 4) by nlinarith),
          mul_nonneg hb0 (show (0 : ℤ) ≤ x + 4 by omega)]
      · have h1 : f.a * (x - 4) + f.b ≤ 0 := by nlinarith
        nlinarith [mul_nonneg_of_nonpos_of_nonpos (show x + 4 ≤ 0 by omega) h1]
    · -- y = 2, x odd, |x| ≥ 5
      left
      have hodd : ¬ (2 : ℤ) ∣ x := by
        intro h2
        have : (2 : ℤ) ∣ (Int.gcd x 2 : ℤ) := Int.dvd_coe_gcd h2 (dvd_refl 2)
        rw [hg] at this; norm_num at this
      dsimp only
      have hx5 : 5 ≤ x ∨ x ≤ -5 := by omega
      rcases hx5 with hx5 | hx5
      · nlinarith [mul_nonneg ha.le (show (0 : ℤ) ≤ (x - 4) * (x + 4) by nlinarith),
          mul_nonneg hb0 (show (0 : ℤ) ≤ x + 2 by omega)]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ f.a - f.b by omega) (show x ≤ 0 by omega),
          mul_nonneg ha.le (show (0 : ℤ) ≤ x * (x + 2) - 15 by nlinarith)]
    · -- y ≥ 3: 4a f(x,y) = (2ax + by)^2 + (4ac - b^2) y^2 ≥ 27 a c
      right
      dsimp only
      have key : 4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) =
          (2 * f.a * x + f.b * y) ^ 2 + (4 * f.a * f.c - f.b ^ 2) * y ^ 2 := by ring
      have hdisc : 3 * f.a * f.c ≤ 4 * f.a * f.c - f.b ^ 2 := by nlinarith
      have hy9 : 9 ≤ y ^ 2 := by nlinarith
      have h1 : 27 * f.a * f.c ≤ 4 * f.a * (f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2) := by
        rw [key]; nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]
      by_contra hlt; push Not at hlt
      nlinarith
  · simp at hg
    omega

/-- The value of $f$ at each vector of $V$. -/
lemma sum_Vset_eq_cntV (f : BinQF) (t : ℤ) :
    ∑ v ∈ Vset, (if f.eval v.1 v.2 ≤ t then (1 : ℤ) else 0) = cntV f.a f.b f.c t := by
  simp only [Vset]
  repeat rw [Finset.sum_insert (by simp)]
  rw [Finset.sum_singleton]
  simp only [BinQF.eval_eq, cntV, ind]
  ring_nf

lemma eval_nonneg_of_mem_Vset {f : BinQF} (hf : IsReduced f) {v : ℤ × ℤ} (hv : v ∈ Vset) :
    0 ≤ f.eval v.1 v.2 := by
  obtain ⟨hb0, hba, hac, ha⟩ := hf
  simp only [Vset, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [BinQF.eval_eq] <;> nlinarith

/-- $r^{\tilde *}_f(m) \ge \#\{v \in V : f(v) = m\}$. -/
lemma card_filter_le_spRepNum {f : BinQF} (hf : IsReduced f) (m : ℤ) :
    (Vset.filter fun v => f.eval v.1 v.2 = m).card ≤ spRepNum f m := by
  have hfin := finite_sp f hf.posDef m
  have hinj : Function.Injective (fun v : (Vset.filter (fun v => f.eval v.1 v.2 = m)) =>
      (⟨v.1, by
          have hv := Finset.mem_filter.1 v.2
          exact ⟨sp_of_mem_Vset hv.1, hv.2⟩⟩ :
        {v : ℤ × ℤ // StronglyPrimitive v ∧ f.eval v.1 v.2 = m})) := by
    intro a b h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_finsetCard] at this

/-- $r^{\tilde *}_f(m) = \#\{v \in V : f(v) = m\}$ for $m < 16a - 4b + c$, $m < 6c$. -/
lemma spRepNum_eq_card_filter {f : BinQF} (hf : IsReduced f) {m : ℤ} (h1 : m < 16 * f.a - 4 * f.b + f.c)
    (h2 : m < 6 * f.c) : spRepNum f m = (Vset.filter fun v => f.eval v.1 v.2 = m).card := by
  have hT : ∀ v : ℤ × ℤ, (StronglyPrimitive v ∧ f.eval v.1 v.2 = m) ↔
      (v ∈ Vset.filter (fun v => f.eval v.1 v.2 = m)) := by
    intro v
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hv, hvm⟩
      refine ⟨?_, hvm⟩
      by_contra hmem
      rcases value_ge_of_not_mem_V hf hv hmem with h | h <;> omega
    · rintro ⟨hv, hvm⟩
      exact ⟨sp_of_mem_Vset hv, hvm⟩
  rw [spRepNum, Nat.card_congr (Equiv.subtypeEquivRight hT), Nat.card_eq_finsetCard]

/-- The cumulative strongly primitive count $N_f(t) = \sum_{0 \le m \le t} r^{\tilde *}_f(m)$, as an integer
($0$ for $t < 0$). -/
noncomputable def spCountZ (f : BinQF) (t : ℤ) : ℤ :=
  ∑ m ∈ Finset.range (t.toNat + 1), (spRepNum f m : ℤ)

lemma sum_filter_card (f : BinQF) (hf : IsReduced f) (t : ℤ) (ht : 0 ≤ t) :
    ∑ m ∈ Finset.range (t.toNat + 1), ((Vset.filter fun v => f.eval v.1 v.2 = (m : ℤ)).card : ℤ) =
      cntV f.a f.b f.c t := by
  rw [← sum_Vset_eq_cntV]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => ?_
  have h0 := eval_nonneg_of_mem_Vset hf hv
  have := sum_ind (f.eval v.1 v.2) h0 t.toNat
  have e : ((f.eval v.1 v.2 ≤ (t.toNat : ℤ)) ↔ f.eval v.1 v.2 ≤ t) := by
    rw [Int.toNat_of_nonneg ht]
  rw [← Nat.cast_inj (R := ℤ)] at this
  push_cast at this
  rw [this]
  simp only [e]

/-- **Lower bound:** $N_f(t) \ge $ `cntV a b c t` for $t \ge 0$. -/
theorem cntV_le_spCountZ {f : BinQF} (hf : IsReduced f) (t : ℤ) (ht : 0 ≤ t) :
    cntV f.a f.b f.c t ≤ spCountZ f t := by
  rw [← sum_filter_card f hf t ht, spCountZ]
  exact Finset.sum_le_sum fun m _ => by exact_mod_cast card_filter_le_spRepNum hf m

/-- **Exact count below the bound:** $N_f(t) = $ `cntV a b c t` for $0 \le t < \min(16a - 4b + c, 6c)$. -/
theorem spCountZ_eq_cntV {f : BinQF} (hf : IsReduced f) (t : ℤ) (ht : 0 ≤ t)
    (h1 : t < 16 * f.a - 4 * f.b + f.c) (h2 : t < 6 * f.c) : spCountZ f t = cntV f.a f.b f.c t := by
  rw [← sum_filter_card f hf t ht, spCountZ]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : (m : ℤ) ≤ t := by
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have : (m : ℤ) ≤ (t.toNat : ℤ) := by exact_mod_cast this
    rwa [Int.toNat_of_nonneg ht] at this
  rw [spRepNum_eq_card_filter hf (by omega) (by omega)]

/-- **The relation for cumulative counts:** if $a\, r^{\tilde *}_{Q_1} + b\, r^{\tilde *}_{Q_2} =
c\, r^{\tilde *}_{Q_3}$ pointwise, then $a N_1 + b N_2 = c N_3$. -/
lemma spCountZ_rel {Q₁ Q₂ Q₃ : BinQF} {a b c : ℤ}
    (h : ∀ m : ℕ, a * spRepNum Q₁ m + b * spRepNum Q₂ m = c * spRepNum Q₃ m) (t : ℤ) :
    a * spCountZ Q₁ t + b * spCountZ Q₂ t = c * spCountZ Q₃ t := by
  simp only [spCountZ, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun m _ => h m

end QuadFormsKB.Hanke2023ThreeTerm.Refinement
