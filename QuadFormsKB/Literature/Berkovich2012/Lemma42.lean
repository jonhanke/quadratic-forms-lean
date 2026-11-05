import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Densities
import QuadFormsKB.LocalDensity.Table2
import QuadFormsKB.LocalDensity.LowerBounds

/-!
# Berkovich–Hanke–Jagy, S-genus identities: Lemma 4.2

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary
quadratic forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §4, Lemma 4.2, p. 4.

**Statement.** For an odd prime $p$, $p \nmid \alpha$ and $m \ne 0$, the local density of
$\alpha x^2 + \alpha p\, y^2 + p\, z^2$ is $\beta_p(m) = $ `betaG p ε m` with
$\varepsilon = \left(\frac{-\alpha}{p}\right)$ (`lemma42`).  Unconditional.

**Proof** (the paper's, via the reduction of Hanke 2004, §3).  Write $a = (\alpha, \alpha p, p)$,
so $S_0 = \{0\}$, $S_1 = \{1, 2\}$, $S_2 = \emptyset$; a solution mod $p^k$ that is not of Zero
type is of Good type ($p \nmid x_0$) or of Bad type I ($p \mid x_0$, some of $x_1, x_2$ a unit);
there is no Bad type II.
* Good: by Lemma 3.2 (`repCountGood_add_diag`) the count is $p^{2(k-1)}$ times the count mod $p$,
  which is $p^2 (1 + (\frac{\alpha m}{p}))$ if $p \nmid m$ and $0$ if $p \mid m$ (`unit_k`).
* Bad I (`repCountBadI_eq`): $p^2$ times the Good count of $Q' = p\alpha x^2 + \alpha y^2 + z^2$ at
  $m/p$ mod $p^{k-1}$, which is $p(p - \varepsilon)$ if $p \nmid m/p$ and
  $p(p-1)(1+\varepsilon)$ if $p \mid m/p$ (binary counts mod $p$, `repCount_one_Q'`, `good1_Q'`).
  Hence the non-Zero density is $1 - \varepsilon/p$ resp. $(1 - 1/p)(1 + \varepsilon)$ (`nz_k`).
* Zero: $r^{\mathrm{Zero}}_{p^k}(p^2 T) = p^3 r_{p^{k-2}}(T)$ (`repCountZero_eq`), giving the
  recursion $\beta(p^2 T) = (1 - 1/p)(1+\varepsilon) + \beta(T)/p$, matched by `betaG_sq_mul`.
Induction on $|m|$ finishes (`main`).
-/

namespace QuadFormsKB.Berkovich2012.L42

open QuadFormsKB QuadFormsKB.LocalDensity

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient vector. -/
def aV (α : ℤ) : Fin 3 → ℤ := ![α, α * p, p]

theorem p_ne_zero_int : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

variable {p} {n : ℕ}

theorem aV_ne (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : ∀ i, aV p α i ≠ 0 := by
  have h0 : α ≠ 0 := by rintro rfl; exact hα (dvd_zero _)
  have := p_ne_zero_int p
  have hp' : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  intro i; fin_cases i <;> simp [aV, h0, hp']

theorem val_p : padicValInt p (p : ℤ) = 1 := by
  simp [padicValInt]

theorem val_alpha_p (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : padicValInt p (α * p) = 1 := by
  have h0 : α ≠ 0 := by rintro rfl; exact hα (dvd_zero _)
  rw [padicValInt.mul h0 (p_ne_zero_int p), padicValInt.eq_zero_of_not_dvd hα, val_p]

theorem badI_aV (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : badIForm (aV p α) p = ![p * α, α, 1] := by
  funext i
  have hp := p_ne_zero_int p
  fin_cases i
  · simp [badIForm, aV, padicValInt.eq_zero_of_not_dvd hα]
  · simp [badIForm, aV, val_alpha_p α hα, Int.mul_ediv_cancel _ hp]
  · simp [badIForm, aV, val_p, Int.ediv_self hp]

theorem S₀_eq_filter (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    S₀ a p = Finset.univ.filter fun i => ¬ (p : ℤ) ∣ a i := by
  ext i
  simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hd
    have := (padicValInt_dvd_iff (p := p) 1 (a i)).1 (by simpa using hd)
    rcases this with h1 | h1
    · exact ha i h1
    · omega
  · intro h; exact padicValInt.eq_zero_of_not_dvd h

theorem S₀_aV (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : S₀ (aV p α) p = {0} := by
  rw [S₀_eq_filter _ (aV_ne α hα)]
  have hp : ¬ (p : ℤ) ∣ 1 := fun h => by
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  fin_cases i
  · simp [aV, hα]
  · simp [aV]
  · simp [aV]

theorem S₁_aV (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : (S₁ (aV p α) p).card = 2 := by
  have : S₁ (aV p α) p = {1, 2} := by
    ext i
    simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    fin_cases i
    · simp [aV, padicValInt.eq_zero_of_not_dvd hα]
    · simp [aV, val_alpha_p α hα]
    · simp [aV, val_p]
  rw [this]; decide

theorem S₂_aV (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : (S₂ (aV p α) p).card = 0 := by
  have : S₂ (aV p α) p = ∅ := by
    ext i
    simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_le]
    fin_cases i
    · simp [aV, padicValInt.eq_zero_of_not_dvd hα]
    · simp [aV, val_alpha_p α hα]
    · simp [aV, val_p]
  rw [this]; rfl

section Level1

theorem diagCountModP_cons_zero {m : ℕ} (a : Fin m → ZMod p) (c : ZMod p) :
    diagCountModP (Fin.cons (0 : ZMod p) a : Fin (m + 1) → ZMod p) c = p * diagCountModP a c := by
  rw [diagCountModP_cons]; simp

theorem ne_zero_zmod (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : (α : ZMod p) ≠ 0 := fun h =>
  hα ((ZMod.intCast_zmod_eq_zero_iff_dvd α p).mp h)

theorem repCount_one_Q (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (c : ℤ) :
    (repCount (QuadForm.diag (aV p α)) p 1 c : ℤ) =
      (p : ℤ) ^ 2 * (1 + quadraticChar (ZMod p) ((α : ZMod p) * c)) := by
  rw [repCount_diag_one_eq]
  have hv : (fun i => ((aV p α i : ℤ) : ZMod p)) = ![(α : ZMod p), 0, 0] := by
    funext i; fin_cases i <;> simp [aV]
  rw [hv]
  have h1 : diagCountModP ![(α : ZMod p), 0, 0] (c : ZMod p) =
      ∑ y : ZMod p, diagCountModP ![(0 : ZMod p), 0] ((c : ZMod p) - α * y ^ 2) :=
    diagCountModP_cons _ _ _
  have h2 : ∀ d : ZMod p, diagCountModP ![(0 : ZMod p), 0] d = p * (p * (if d = 0 then 1 else 0)) := by
    intro d
    have e1 : diagCountModP ![(0 : ZMod p), 0] d = p * diagCountModP ![(0 : ZMod p)] d :=
      diagCountModP_cons_zero _ _
    have e2 : diagCountModP ![(0 : ZMod p)] d = p * diagCountModP (![] : Fin 0 → ZMod p) d :=
      diagCountModP_cons_zero _ _
    rw [e1, e2, diagCountModP_zero]
  rw [h1]
  simp_rw [h2]
  have h3 := sum_ite_mul_sq_eq hp2 (α : ZMod p) (c : ZMod p) (ne_zero_zmod α hα)
  have h4 : ∀ y : ZMod p, ((if (c : ZMod p) - α * y ^ 2 = 0 then 1 else 0 : ℤ)) =
      if (α : ZMod p) * y ^ 2 = c then 1 else 0 := by
    intro y
    simp only [sub_eq_zero, eq_comm]
  simp_rw [h4, ← Finset.mul_sum, h3]
  ring

theorem repCount_one_Q' (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (c : ℤ) :
    (repCount (QuadForm.diag ![(p : ℤ) * α, α, 1]) p 1 c : ℤ) =
      p * ((p - quadraticChar (ZMod p) (-(α : ZMod p))) +
        quadraticChar (ZMod p) (-(α : ZMod p)) * p * (if (c : ZMod p) = 0 then 1 else 0)) := by
  rw [repCount_diag_one_eq]
  have hv : (fun i => (((![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i : ℤ) : ZMod p)) =
      ![(0 : ZMod p), α, 1] := by
    funext i; fin_cases i <;> simp
  rw [hv]
  have e1 : diagCountModP ![(0 : ZMod p), α, 1] (c : ZMod p) =
      p * diagCountModP ![(α : ZMod p), 1] (c : ZMod p) := diagCountModP_cons_zero _ _
  have e2 : diagCountModP ![(α : ZMod p), 1] (c : ZMod p) =
      (p - quadraticChar (ZMod p) (-((α : ZMod p) * 1))) * p ^ 0 +
        quadraticChar (ZMod p) (-((α : ZMod p) * 1)) * p *
          diagCountModP (![] : Fin 0 → ZMod p) (c : ZMod p) :=
    diagCountModP_cons_cons hp2 (α : ZMod p) 1 (ne_zero_zmod α hα) one_ne_zero _ _
  rw [e1, e2, diagCountModP_zero]
  simp

end Level1

section Good1

theorem evalIn_diag_zmod {n : ℕ} (a : Fin n → ℤ) (N : ℕ) (x : Fin n → ZMod N) :
    (QuadForm.diag a).evalIn (ZMod N) x = ∑ i, (a i : ZMod N) * x i ^ 2 := by
  simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

theorem cast_p_zero : (p : ZMod (p ^ 1)) = 0 :=
  (ZMod.natCast_eq_zero_iff p (p ^ 1)).2 (by simp)

instance instFactPrimePow1 : Fact (Nat.Prime (p ^ 1)) := ⟨by rw [pow_one]; exact Fact.out⟩

theorem dvd_iff_zero (y : ZMod (p ^ 1)) : (p : ZMod (p ^ 1)) ∣ y ↔ y = 0 := by
  rw [cast_p_zero, zero_dvd_iff]

theorem card_split {α : Type*} [Finite α] (P T : α → Prop) :
    Nat.card {x // P x} = Nat.card {x // P x ∧ T x} + Nat.card {x // P x ∧ ¬ T x} := by
  classical
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter P) T,
    Finset.filter_filter, Finset.filter_filter]

theorem good_Q_iff (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (x : Fin 3 → ZMod (p ^ 1)) :
    IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ aV p α i) p 1 x ↔ x 0 ≠ 0 := by
  have hS : (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ aV p α i) = {0} := by
    rw [← S₀_eq_filter _ (aV_ne α hα), S₀_aV α hα]
  rw [hS]
  simp only [IsGoodType, IsZeroType, Finset.mem_singleton, exists_eq_left, dvd_iff_zero]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun hz => h (by simpa [dvd_iff_zero] using hz 0), h⟩

theorem eval_Q_of (α : ℤ) (x : Fin 3 → ZMod (p ^ 1)) :
    (QuadForm.diag (aV p α)).evalIn (ZMod (p ^ 1)) x = (α : ZMod (p ^ 1)) * x 0 ^ 2 := by
  rw [evalIn_diag_zmod, Fin.sum_univ_three]
  have := cast_p_zero (p := p)
  simp [aV, this]

theorem good1_Q_unit (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    repCountOf (QuadForm.diag (aV p α)) p 1 m
        (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ aV p α i) p 1) =
      repCount (QuadForm.diag (aV p α)) p 1 m := by
  unfold repCountOf repCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [good_Q_iff α hα]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun h0 => hm ?_⟩
    rw [eval_Q_of, h0] at h
    simp at h
    exact (intCast_zmod_pow_one_eq_zero (p := p)).1 h.symm

theorem good1_Q_dvd (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ) (hm : (p : ℤ) ∣ m) :
    repCountOf (QuadForm.diag (aV p α)) p 1 m
        (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ aV p α i) p 1) = 0 := by
  unfold repCountOf
  rw [Nat.card_eq_zero]; left
  refine ⟨fun ⟨x, hx, hg⟩ => ?_⟩
  rw [good_Q_iff α hα] at hg
  rw [eval_Q_of, (intCast_zmod_pow_one_eq_zero (p := p)).2 hm] at hx
  have hα' : (α : ZMod (p ^ 1)) ≠ 0 := by
    rw [Ne, intCast_zmod_pow_one_eq_zero]; exact hα
  have : x 0 ^ 2 = 0 := by
    rcases mul_eq_zero.1 hx with h | h
    · exact absurd h hα'
    · exact h
  exact hg (pow_eq_zero_iff (two_ne_zero) |>.1 this)

theorem good_Q'_iff (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (x : Fin 3 → ZMod (p ^ 1)) :
    IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i) p 1 x ↔
      (x 1 ≠ 0 ∨ x 2 ≠ 0) := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := fun h => by
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast this)
  have hS : (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i) =
      {1, 2} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    fin_cases i
    · simp
    · simp [hα]
    · simp [hp1]
  rw [hS]
  simp only [IsGoodType, IsZeroType, Finset.mem_insert, Finset.mem_singleton, dvd_iff_zero]
  constructor
  · rintro ⟨_, i, hi | hi, h⟩
    · subst hi; exact Or.inl h
    · subst hi; exact Or.inr h
  · intro h
    refine ⟨fun hz => ?_, ?_⟩
    · rcases h with h | h
      · exact h (by simpa [dvd_iff_zero] using hz 1)
      · exact h (by simpa [dvd_iff_zero] using hz 2)
    · rcases h with h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨2, Or.inr rfl, h⟩

theorem eval_Q'_of (α : ℤ) (x : Fin 3 → ZMod (p ^ 1)) :
    (QuadForm.diag (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ)).evalIn (ZMod (p ^ 1)) x =
      (α : ZMod (p ^ 1)) * x 1 ^ 2 + x 2 ^ 2 := by
  rw [evalIn_diag_zmod, Fin.sum_univ_three]
  have := cast_p_zero (p := p)
  simp [this]

theorem card_axis :
    Nat.card {x : Fin 3 → ZMod (p ^ 1) // x 1 = 0 ∧ x 2 = 0} = p := by
  have : Nat.card {x : Fin 3 → ZMod (p ^ 1) // x 1 = 0 ∧ x 2 = 0} = Nat.card (ZMod (p ^ 1)) := by
    refine Nat.card_congr
      { toFun := fun x => x.1 0
        invFun := fun y => ⟨![y, 0, 0], rfl, rfl⟩
        left_inv := ?_
        right_inv := fun y => rfl }
    rintro ⟨x, h1, h2⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [h1, h2]
  rw [this, Nat.card_zmod]; simp

theorem good1_Q' (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (n : ℤ) :
    repCount (QuadForm.diag (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ)) p 1 n =
      repCountOf (QuadForm.diag (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ)) p 1 n
        (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i) p 1) +
        (if (p : ℤ) ∣ n then p else 0) := by
  unfold repCountOf repCount
  rw [card_split _ (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i) p 1)]
  congr 1
  simp_rw [good_Q'_iff α hα]
  split_ifs with h
  · have hn : (n : ZMod (p ^ 1)) = 0 := (intCast_zmod_pow_one_eq_zero (p := p)).2 h
    refine (Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)).trans (card_axis (p := p))
    rw [eval_Q'_of, hn]
    simp only [not_or, not_not]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [h1, h2]; simp
  · have hn : (n : ZMod (p ^ 1)) ≠ 0 := fun h' => h ((intCast_zmod_pow_one_eq_zero (p := p)).1 h')
    rw [Nat.card_eq_zero]; left
    refine ⟨fun ⟨x, hx, hg⟩ => ?_⟩
    simp only [not_or, not_not] at hg
    rw [eval_Q'_of, hg.1, hg.2] at hx
    simp at hx
    exact hn hx.symm

end Good1

section LevelK

theorem S₁_aV_eq (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) : S₁ (aV p α) p = {1, 2} := by
  ext i
  simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  fin_cases i
  · simp [aV, padicValInt.eq_zero_of_not_dvd hα]
  · simp [aV, val_alpha_p α hα]
  · simp [aV]

theorem unit_k (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m)
    (k : ℕ) (hk : 2 ≤ k) :
    (repCount (QuadForm.diag (aV p α)) p k m : ℝ) / (p : ℝ) ^ (k * (3 - 1)) =
      1 + (quadraticChar (ZMod p) ((α : ZMod p) * m) : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨l, rfl⟩ : ∃ l, k = 1 + l := ⟨k - 1, by omega⟩
  set Q := QuadForm.diag (aV p α) with hQ
  set S := Finset.univ.filter (fun i => ¬ (p : ℤ) ∣ aV p α i) with hS
  have h1 := repCount_eq_add_types Q S p (1 + l) m
  have hbad := repCountBad_eq_zero (aV p α) p m (1 + l) (by omega) hm
  rw [S₀_eq_filter _ (aV_ne α hα)] at hbad
  have hz := repCountZero_eq Q p m (1 + l) hk
  have hm2 : ¬ (p : ℤ) ^ 2 ∣ m := fun h => hm (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  rw [if_neg hm2] at hz
  have hg := repCountGood_add_diag (aV p α) p m 1 l (by simp [hp2])
  rw [good1_Q_unit α hα m hm] at hg
  have hr1 := repCount_one_Q hp2 α hα m
  have : repCount Q p (1 + l) m = p ^ (2 * l) * repCount Q p 1 m := by
    rw [h1, hz, hbad]
    simpa using hg
  have hr : (repCount Q p (1 + l) m : ℝ) = (p : ℝ) ^ (2 * l) *
      ((p : ℝ) ^ 2 * (1 + (quadraticChar (ZMod p) ((α : ZMod p) * m) : ℝ))) := by
    rw [this]
    have : (repCount Q p 1 m : ℝ) = (p : ℝ) ^ 2 * (1 + (quadraticChar (ZMod p) ((α : ZMod p) * m) : ℝ)) := by
      exact_mod_cast hr1
    push_cast
    rw [this]
  rw [hr, show (1 + l) * (3 - 1) = 2 * l + 2 by omega, pow_add]
  field_simp

theorem nz_k (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ) (hm : (p : ℤ) ∣ m)
    (k : ℕ) (hk : 2 ≤ k) :
    (repCountOf (QuadForm.diag (aV p α)) p k m (fun x => ¬ IsZeroType p k x) : ℝ) /
        (p : ℝ) ^ (k * (3 - 1)) =
      if (p : ℤ) ∣ m / p then (1 - 1 / (p : ℝ)) * (1 + (quadraticChar (ZMod p) (-(α : ZMod p)) : ℝ))
      else 1 - (quadraticChar (ZMod p) (-(α : ZMod p)) : ℝ) / p := by
  have hpp := Fact.out (p := p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
  set a := aV p α with ha
  set Q := QuadForm.diag a with hQ
  set S := Finset.univ.filter (fun i => ¬ (p : ℤ) ∣ a i) with hS
  have ha0 := aV_ne α hα
  have h1 := repCount_eq_add_types Q S p (l + 2) m
  have h2 := repCount_eq_zero_add_nonZero Q p (l + 2) m
  have hg := repCountGood_add_diag a p m 1 (l + 1) (by simp [hp2])
  rw [good1_Q_dvd α hα m hm] at hg
  have hgood : repCountOf Q p (l + 2) m (IsGoodType S p (l + 2)) = 0 := by
    have : 1 + (l + 1) = l + 2 := by omega
    rw [this] at hg
    simpa using hg
  -- the Bad type is Bad type I
  have hbadI : repCountOf Q p (l + 2) m (IsBadType S p (l + 2)) =
      repCountOf Q p (l + 2) m (fun x => IsBadType (S₀ a p) p (l + 2) x ∧
        ∃ i ∈ S₁ a p, ¬ (p : ZMod (p ^ (l + 2))) ∣ x i) := by
    unfold repCountOf
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [hS, ← S₀_eq_filter _ ha0]
    constructor
    · rintro ⟨he, hb⟩
      refine ⟨he, hb, ?_⟩
      by_contra hcon
      push Not at hcon
      apply hb.1
      intro i
      have h0 : ∀ i ∈ S₀ a p, (p : ZMod (p ^ (l + 2))) ∣ x i := by
        intro i hi
        by_contra h
        exact hb.2 ⟨hb.1, i, hi, h⟩
      fin_cases i
      · exact h0 0 (by rw [ha, S₀_aV α hα]; simp)
      · exact hcon 1 (by rw [ha, S₁_aV_eq α hα]; simp)
      · exact hcon 2 (by rw [ha, S₁_aV_eq α hα]; simp)
    · rintro ⟨he, hb, _⟩
      exact ⟨he, hb⟩
  have hBI := repCountBadI_eq a ha0 p m (l + 2) hk hm
  rw [ha, S₁_aV α hα, S₂_aV α hα, badI_aV α hα] at hBI
  have hb0 : ∀ i, (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i ≠ 0 := by
    have h0 : α ≠ 0 := by rintro rfl; exact hα (dvd_zero _)
    have hp' : p ≠ 0 := hpp.ne_zero
    intro i; fin_cases i <;> simp [h0, hp']
  rw [S₀_eq_filter _ hb0, show l + 2 - 1 = 1 + l by omega] at hBI
  have hg' := repCountGood_add_diag (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) p (m / p) 1 l (by simp [hp2])
  rw [hg'] at hBI
  have hq1 := good1_Q' α hα (m / p)
  have hq2 := repCount_one_Q' hp2 α hα (m / p)
  have hiff : (((m / p : ℤ) : ZMod p) = 0) ↔ (p : ℤ) ∣ m / p := ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  set G' := repCountOf (QuadForm.diag (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ)) p 1 (m / p)
    (IsGoodType (Finset.univ.filter fun i => ¬ (p : ℤ) ∣ (![(p : ℤ) * α, α, 1] : Fin 3 → ℤ) i) p 1)
    with hG'
  have hnz : repCountOf Q p (l + 2) m (fun x => ¬ IsZeroType p (l + 2) x) =
      p ^ (2 + 0) * (p ^ ((3 - 1) * l) * G') := by
    rw [← hBI, ← hbadI]; omega
  set η := quadraticChar (ZMod p) (-(α : ZMod p)) with hη
  have hq3 : (G' : ℝ) = p * ((p - η) + η * p * (if (p : ℤ) ∣ m / p then 1 else 0)) -
      (if (p : ℤ) ∣ m / p then p else 0) := by
    have e : (G' : ℤ) = p * ((p - η) + η * p * (if ((m / p : ℤ) : ZMod p) = 0 then 1 else 0)) -
        (if (p : ℤ) ∣ m / p then p else 0) := by
      have := congrArg (fun z : ℕ => (z : ℤ)) hq1
      simp only [Nat.cast_add] at this
      rw [hq2] at this
      split_ifs at this ⊢ <;> simp_all <;> linarith
    have e2 := congrArg (fun z : ℤ => (z : ℝ)) e
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_add, Int.cast_natCast, apply_ite (Int.cast : ℤ → ℝ),
      Int.cast_ofNat, Int.cast_one, Int.cast_zero] at e2
    rw [if_congr hiff rfl rfl] at e2
    exact_mod_cast e2
  rw [hnz]
  push_cast
  rw [show (l + 2) * (3 - 1) = 2 * l + 4 by omega]
  by_cases hd : (p : ℤ) ∣ m / p
  · rw [if_pos hd]
    rw [if_pos hd, if_pos hd] at hq3
    rw [hq3]
    field_simp
    ring
  · rw [if_neg hd]
    rw [if_neg hd, if_neg hd] at hq3
    rw [hq3]
    field_simp
    ring

end LevelK

section Algebra

theorem geomSum_succ (k : ℕ) : geomSum p (k + 1) = 1 + geomSum p k / p := by
  unfold geomSum
  rw [Finset.sum_range_succ', Finset.sum_div]
  have : ∀ j ∈ Finset.range k, (1 / (p : ℚ)) ^ (j + 1) = (1 / (p : ℚ)) ^ j / p := by
    intro j _; rw [pow_succ]; ring
  rw [Finset.sum_congr rfl this]; simp [add_comm]

theorem padicValInt_sq_mul (T : ℤ) (hT : T ≠ 0) :
    padicValInt p ((p : ℤ) ^ 2 * T) = padicValInt p T + 2 := by
  have hp : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (p_ne_zero_int p)
  rw [padicValInt.mul hp hT]
  have : padicValInt p ((p : ℤ) ^ 2) = 2 := by
    simp [padicValInt, Int.natAbs_pow]
  omega

theorem sqFree_sq_mul (T : ℤ) (hT : T ≠ 0) : sqFree p ((p : ℤ) ^ 2 * T) = sqFree p T := by
  unfold sqFree
  rw [padicValInt_sq_mul T hT]
  rw [show 2 * ((padicValInt p T + 2) / 2) = 2 + 2 * (padicValInt p T / 2) by omega, pow_add]
  have hpos : (0 : ℤ) < (p : ℤ) ^ 2 := by
    have := (Fact.out : p.Prime).pos
    positivity
  exact Int.mul_ediv_mul_of_pos _ _ hpos

/-- Recursion: $\beta_G(p^2 T) = (1 - 1/p)(1 + \varepsilon) + \beta_G(T)/p$. -/
theorem betaG_sq_mul (ε : ℤ) (T : ℤ) (hT : T ≠ 0) :
    betaG p ε ((p : ℤ) ^ 2 * T) = (1 - 1 / (p : ℚ)) * (1 + ε) + betaG p ε T / p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold betaG chiOf
  rw [sqFree_sq_mul T hT, padicValInt_sq_mul T hT]
  simp only []
  rw [show (padicValInt p T + 2) / 2 = padicValInt p T / 2 + 1 by omega,
    show (padicValInt p T + 2) % 2 = padicValInt p T % 2 by omega]
  split_ifs
  · simp only [geomSum_succ]; field_simp; ring
  · simp only [geomSum_succ]; field_simp; ring

theorem betaG_unit (ε : ℤ) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    betaG p ε m = 1 + ε * legendreSym p (-m) := by
  unfold betaG chiOf sqFree
  rw [padicValInt.eq_zero_of_not_dvd hm]
  simp [geomSum]

theorem betaG_ord_one (ε : ℤ) (m : ℤ) (hm : padicValInt p m = 1) :
    betaG p ε m = 1 - ε / p := by
  unfold betaG
  simp only [hm]
  norm_num [geomSum]

theorem leg_neg (α : ℤ) : legendreSym p (-α) = quadraticChar (ZMod p) (-(α : ZMod p)) := by
  rw [legendreSym]; push_cast; rfl

end Algebra

section Main

theorem not_dvd_div (m : ℤ) (h1 : (p : ℤ) ∣ m) (h2 : ¬ (p : ℤ) ^ 2 ∣ m) : ¬ (p : ℤ) ∣ m / p := by
  obtain ⟨c, rfl⟩ := h1
  rw [Int.mul_ediv_cancel_left _ (p_ne_zero_int p)]
  rintro ⟨d, rfl⟩
  exact h2 ⟨d, by ring⟩

theorem main (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ) (hm : m ≠ 0) :
    localDensity (QuadForm.diag (aV p α)) p m =
      ((betaG p (quadraticChar (ZMod p) (-(α : ZMod p))) m : ℚ) : ℝ) := by
  have hpp := Fact.out (p := p.Prime)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hQ : (QuadForm.diag (aV p α)).Nondegenerate := LocalDensity.nondegenerate_diag _ (aV_ne α hα)
  induction' hn : m.natAbs using Nat.strong_induction_on with n ih generalizing m
  by_cases h1 : (p : ℤ) ∣ m
  · by_cases h2 : (p : ℤ) ^ 2 ∣ m
    · obtain ⟨T, rfl⟩ := h2
      have hT : T ≠ 0 := by rintro rfl; simp at hm
      have hlt : T.natAbs < n := by
        rw [← hn, Int.natAbs_mul]
        have := hpp.two_le
        simp only [Int.natAbs_pow, Int.natAbs_natCast]
        have : 0 < T.natAbs := Int.natAbs_pos.2 hT
        have : 2 ≤ p ^ 2 := by nlinarith
        nlinarith
      have ih' := ih _ hlt T hT rfl
      have hpZ : ((p : ℤ) ^ 2) ≠ 0 := pow_ne_zero _ (p_ne_zero_int p)
      have e1 := localDensity_eventually_eq _ hQ p ((p : ℤ) ^ 2 * T) hm
      have e2 := (Filter.tendsto_sub_atTop_nat 2).eventually
        (localDensity_eventually_eq _ hQ p T hT)
      obtain ⟨k, hk1, hk2, hk⟩ := (e1.and (e2.and (Filter.eventually_ge_atTop 2))).exists
      have hs := normalized_split (QuadForm.diag (aV p α)) p (by norm_num) T k hk
      rw [hk1, hk2] at hs
      have hdiv : (p : ℤ) ^ 2 * T / p = p * T := by
        rw [pow_two, mul_assoc, Int.mul_ediv_cancel_left _ (p_ne_zero_int p)]
      have hnz := nz_k hp2 α hα ((p : ℤ) ^ 2 * T) (Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _) k
        (by omega)
      rw [hdiv, if_pos (dvd_mul_right _ _)] at hnz
      rw [hnz] at hs
      rw [hs, betaG_sq_mul _ _ hT, ih']
      push_cast
      norm_num
      ring
    · have hv : padicValInt p m = 1 := by
        have h2' : ¬ 2 ≤ padicValInt p m := fun h =>
          h2 ((padicValInt_dvd_iff 2 m).2 (Or.inr h))
        have h1' : 1 ≤ padicValInt p m := by
          have := (padicValInt_dvd_iff (p := p) 1 m).1 (by simpa using h1)
          rcases this with h | h
          · exact absurd h hm
          · exact h
        omega
      have : localDensity (QuadForm.diag (aV p α)) p m =
          1 - (quadraticChar (ZMod p) (-(α : ZMod p)) : ℝ) / p := by
        unfold localDensity
        apply limUnder_eq_of_eventually
        filter_upwards [Filter.eventually_ge_atTop 2] with k hk
        rw [repCount_eq_zero_add_nonZero, repCountZero_eq _ p m k hk, if_neg h2, Nat.cast_add]
        simp only [Nat.cast_zero, zero_add]
        rw [nz_k hp2 α hα m h1 k hk, if_neg (not_dvd_div m h1 h2)]
      rw [this, betaG_ord_one _ m hv]
      push_cast
      ring
  · have : localDensity (QuadForm.diag (aV p α)) p m =
        1 + (quadraticChar (ZMod p) ((α : ZMod p) * m) : ℝ) := by
      unfold localDensity
      apply limUnder_eq_of_eventually
      filter_upwards [Filter.eventually_ge_atTop 2] with k hk
      exact unit_k hp2 α hα m h1 k hk
    rw [this, betaG_unit _ m h1, leg_neg m]
    have hmul : quadraticChar (ZMod p) ((α : ZMod p) * m) =
        quadraticChar (ZMod p) (-(α : ZMod p)) * quadraticChar (ZMod p) (-(m : ZMod p)) := by
      rw [← map_mul]; congr 1; ring
    rw [hmul]
    push_cast
    ring

end Main

end QuadFormsKB.Berkovich2012.L42

namespace QuadFormsKB.Berkovich2012

/-- **Lemma 4.2 (BHJ).** For an odd prime $p$, $p \nmid \alpha$ and $m \ne 0$, the local density of
$\alpha x^2 + \alpha p\, y^2 + p\, z^2$ at $p$ is given by `betaG` with
$\varepsilon = \left(\frac{-\alpha}{p}\right)$: with $\operatorname{ord}_p(m) = 2k$ or $2k+1$,
$(1 - \frac1p)(1+\varepsilon) G_k + p^{-k}(1 + \varepsilon\chi)$ resp.
$(1 - \frac1p)(1+\varepsilon) G_k + p^{-k}(1 - \varepsilon/p)$, $\chi = \left(\frac{-m/p^{2k}}{p}\right)$.
Unconditional. -/
@[kb "berkovich2012" "§4, Lemma 4.2, p. 4"]
theorem lemma42 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (α : ℤ) (hα : ¬ (p : ℤ) ∣ α) (m : ℤ)
    (hm : m ≠ 0) :
    QuadFormsKB.LocalDensity.localDensity (QuadForm.diag ![α, α * p, (p : ℤ)]) p m =
      (betaG p (legendreSym p (-α)) m : ℝ) := by
  rw [L42.leg_neg]
  exact L42.main hp2 α hα m hm

end QuadFormsKB.Berkovich2012
