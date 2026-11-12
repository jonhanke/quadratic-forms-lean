/-
# Moreno–Wagstaff 2005, Chapter 2: Euler-type recurrences (§2.4)

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §2.4, pp. 18–20.

**Proves**
* `theorem23` (Theorem 2.3, **proved**): the book's single application of the Second Fundamental Identity
  (`theorem22`) with $\lambda = 3/2$, $\mu = 1/2$ and
  $F(x, y, z) = (-1)^{(x+z)/2+y}$ for $x, z$ odd, $0$ otherwise.
* `theorem24` (Theorem 2.4, **proved**, by a different route than the book): logarithmic derivative of the
  truncated Euler products $\prod_{k<N}(1 - X^{k+1})$ in $\mathbb Z[[X]]$ against Mathlib's pentagonal number
  theorem (`PowerSeries.pentagonalSeries`).
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Liouville
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

namespace QuadFormsKB.MorenoWagstaff

/-! ### The function $F$ -/

/-- The sign $(-1)^k$ as an integer, for $k \in \mathbb Z$. -/
private def sg (k : ℤ) : ℤ := if Even k then 1 else -1

/-- The book's $F(x, y, z) = (-1)^{(x+z)/2 + y}$ if $x, z$ are both odd and $0$ otherwise. -/
private noncomputable def Fe (x y z : ℤ) : ℝ :=
  if Odd x ∧ Odd z then (sg ((x + z) / 2 + y) : ℝ) else 0

private lemma Fe_oddx : IsOddIn₁ Fe := by
  intro x y z
  unfold Fe sg
  simp only [Int.odd_iff, Int.even_iff]
  split_ifs <;> first | omega | norm_num

private lemma Fe_odd23 : IsOddIn₂₃ Fe := by
  intro x y z
  unfold Fe sg
  simp only [Int.odd_iff, Int.even_iff]
  split_ifs <;> first | omega | norm_num

private lemma sg_ne_zero (k : ℤ) : (sg k : ℝ) ≠ 0 := by
  unfold sg; split_ifs <;> norm_num

private lemma sg_neg (k : ℤ) : sg (-k) = sg k := by
  unfold sg; simp only [Int.even_iff]; split_ifs <;> omega

private lemma finsum_mem_neg' {α : Type*} (s : Set α) (f : α → ℝ) :
    ∑ᶠ i ∈ s, -f i = -∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
  exact finsum_congr fun i => by by_cases h : i ∈ s <;> simp [Set.indicator, h]

/-! ### $U = 0$ and $W = 0$ -/

private lemma U_zero (n : ℕ) : liouvilleU Fe (3 / 2) (1 / 2) n = 0 := by
  unfold liouvilleU
  refine finsum_mem_eq_zero_of_forall_eq_zero fun p hp => ?_
  have h := hp.2.2.1
  unfold Fe
  split_ifs with h1
  · exfalso
    obtain ⟨h1, -⟩ := h1
    rw [Int.ModEq] at h
    rw [Int.odd_iff] at h1
    omega
  · rfl

private lemma W_zero (n : ℕ) : liouvilleW Fe (3 / 2) (1 / 2) n = 0 := by
  unfold liouvilleW
  have hbij : Set.BijOn (fun p : ℤ × ℤ × ℤ => (p.1, p.2.2, p.2.1))
      (liouvilleC (3 / 2) (1 / 2) n) (liouvilleC (3 / 2) (1 / 2) n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨h2, h1, by simp only; rw [h3]; ring⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2.2 h.2.1)
    · intro q hq
      obtain ⟨h1, h2, h3⟩ := hq
      exact ⟨(q.1, q.2.2, q.2.1), ⟨h2, h1, by simp only; rw [h3]; ring⟩, rfl⟩
  have key := finsum_mem_eq_of_bijOn (f := fun p : ℤ × ℤ × ℤ => Fe (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2))
    (g := fun p : ℤ × ℤ × ℤ => -Fe (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2)) _ hbij (fun p _ => by
      simp only
      unfold Fe sg
      simp only [Int.odd_iff, Int.even_iff]
      split_ifs <;> first | omega | norm_num)
  rw [finsum_mem_neg'] at key
  linarith

/-! ### $T_1 - T_2$ -/

private lemma card_odd_Icc (s : ℤ) (hs : 0 < s) :
    (((Finset.Icc (1 : ℤ) (2 * s - 1)).filter Odd).card : ℝ) = s := by
  have h : ((Finset.Icc (1 : ℤ) (2 * s - 1)).filter Odd).card = (Finset.Icc (1 : ℤ) s).card := by
    refine Finset.card_nbij' (fun j => (j + 1) / 2) (fun k => 2 * k - 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hj ⊢
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hk ⊢
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hj ⊢
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk ⊢
      omega
  rw [h, Int.card_Icc]
  have : (s + 1 - 1).toNat = s.toNat := by simp
  rw [this]
  have := Int.toNat_of_nonneg hs.le
  exact_mod_cast this

private lemma TTerm_eq (s : ℤ) (hs : 0 < s) : liouvilleTTerm Fe s = -(sg s : ℝ) * s := by
  unfold liouvilleTTerm
  rw [abs_of_pos hs]
  have : ∀ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1),
      Fe (2 * s - j) s (2 * s - j) = if Odd j then -(sg s : ℝ) else 0 := by
    intro j _
    unfold Fe sg
    simp only [Int.odd_iff, Int.even_iff]
    split_ifs <;> first | omega | norm_num
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_odd_Icc s hs]
  ring

private lemma E_pos (σ : ℤ) (n : ℕ) :
    liouvilleE (3 / 2) ((σ : ℝ) / 2) n ∩ {s | 0 < s} = {s | 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + σ * s} := by
  ext s
  simp only [Set.mem_inter_iff, liouvilleE, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have : ((2 * (n : ℤ) : ℤ) : ℝ) = ((3 * s ^ 2 + σ * s : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    have : ((2 * (n : ℤ) : ℤ) : ℝ) = ((3 * s ^ 2 + σ * s : ℤ) : ℝ) := by rw [h2]
    push_cast at this
    linarith

private lemma T_empty (σ : ℤ) (n : ℕ) (h : ¬ ∃ s : ℤ, 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + σ * s) :
    liouvilleT₁ Fe (3 / 2) ((σ : ℝ) / 2) n = 0 := by
  unfold liouvilleT₁
  have : liouvilleE (3 / 2) ((σ : ℝ) / 2) n ∩ {s | 0 < s} = ∅ := by
    rw [E_pos]
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hs => h ⟨s, hs⟩
  rw [this, finsum_mem_empty]

private lemma T_single (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) (s0 : ℤ) (hs0 : 0 < s0)
    (h : 2 * (n : ℤ) = 3 * s0 ^ 2 + σ * s0) :
    liouvilleT₁ Fe (3 / 2) ((σ : ℝ) / 2) n = -(sg s0 : ℝ) * s0 := by
  unfold liouvilleT₁
  have : liouvilleE (3 / 2) ((σ : ℝ) / 2) n ∩ {s | 0 < s} = {s0} := by
    rw [E_pos]
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have : (s - s0) * (3 * (s + s0) + σ) = 0 := by linear_combination h - h2
      rcases mul_eq_zero.1 this with h3 | h3
      · omega
      · omega
    · rintro rfl
      exact ⟨hs0, h⟩
  rw [this, finsum_mem_singleton, TTerm_eq s0 hs0]

/-! ### The sum $S$ -/

private lemma mem_pentIdx (n : ℕ) (i : ℤ) : i ∈ pentIdx n ↔ i * (3 * i + 1) < 2 * (n : ℤ) := by
  have h2 := two_mul_natCast_pentagonal_neg i
  unfold pentIdx
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · by_contra hc
      have h1 : i ≤ -1 := by omega
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -i) (by omega : (0 : ℤ) ≤ -i - 1)]
    · by_contra hc
      have h1 : 1 ≤ i := by omega
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ i) (by omega : (0 : ℤ) ≤ i - 1)]

/-- $N_i = n - (3i^2+i)/2$ as a natural number. -/
private def Nn (n : ℕ) (i : ℤ) : ℕ := n - pentagonal (-i)

private lemma Nn_spec (n : ℕ) (i : ℤ) (hi : i ∈ pentIdx n) :
    2 * (Nn n i : ℤ) = 2 * n - i * (3 * i + 1) := by
  have h2 := two_mul_natCast_pentagonal_neg i
  rw [mem_pentIdx] at hi
  unfold Nn
  omega

private def rn (σ : ℤ) : ℕ := if σ = 1 then 2 else 1

private lemma rn_spec (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) : (σ = 1 ∧ rn σ = 2) ∨ (σ = -1 ∧ rn σ = 1) := by
  rcases hσ with h | h
  · left; simp [rn, h]
  · right; simp [rn, h]

private noncomputable def gS (p : ℤ × ℤ × ℤ) : ℝ := if Odd p.2.2 then (sg p.1 : ℝ) else 0

private lemma gS_ne_zero (p : ℤ × ℤ × ℤ) : gS p ≠ 0 ↔ Odd p.2.2 := by
  unfold gS
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => sg_ne_zero _⟩
  · simp [h]

private lemma Fe_S (p : ℤ × ℤ × ℤ) :
    Fe (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) = gS p := by
  unfold Fe gS sg
  simp only [Int.odd_iff, Int.even_iff]
  split_ifs <;> first | omega | norm_num

private lemma memA (σ : ℤ) (n : ℕ) (p : ℤ × ℤ × ℤ) :
    p ∈ liouvilleA (3 / 2) ((σ : ℝ) / 2) n ↔
      0 < p.2.1 ∧ 0 < p.2.2 ∧ 2 * (n : ℤ) = 3 * p.1 ^ 2 + σ * p.1 + (3 * p.2.2 + σ) * p.2.1 := by
  simp only [liouvilleA, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    have : ((2 * (n : ℤ) : ℤ) : ℝ) = ((3 * p.1 ^ 2 + σ * p.1 + (3 * p.2.2 + σ) * p.2.1 : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · intro h
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    linarith

private def Sset (σ : ℤ) (n : ℕ) : Finset (Σ _ : ℤ, ℕ) :=
  (pentIdx n).sigma fun i => (Nn n i).divisors.filter fun e => e % 3 = rn σ

private def phi (σ : ℤ) (n : ℕ) (x : Σ _ : ℤ, ℕ) : ℤ × ℤ × ℤ :=
  (σ * x.1, (Nn n x.1 : ℤ) / (x.2 : ℤ), (2 * (x.2 : ℤ) - σ) / 3)

private lemma Sset_mem (σ : ℤ) (n : ℕ) (i : ℤ) (e : ℕ) :
    (⟨i, e⟩ : Σ _ : ℤ, ℕ) ∈ Sset σ n ↔
      i ∈ pentIdx n ∧ (e ∣ Nn n i ∧ Nn n i ≠ 0) ∧ e % 3 = rn σ := by
  simp [Sset, Finset.mem_sigma, Finset.mem_filter, Nat.mem_divisors]

private lemma S_mapsTo (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) (i : ℤ) (e : ℕ)
    (hx : (⟨i, e⟩ : Σ _ : ℤ, ℕ) ∈ Sset σ n) :
    phi σ n ⟨i, e⟩ ∈ liouvilleA (3 / 2) ((σ : ℝ) / 2) n ∩ Function.support gS := by
  rw [Sset_mem] at hx
  obtain ⟨hi, ⟨⟨k, hk⟩, hN0⟩, he3⟩ := hx
  have hr := rn_spec σ hσ
  have h4 := Nn_spec n i hi
  have hepos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact hN0 hk)
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact hN0 hk)
  have hNe : (Nn n i : ℤ) = e * k := by exact_mod_cast hk
  have hd : (Nn n i : ℤ) / (e : ℤ) = k := by
    rw [hNe]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hepos.ne')
  have h3 : 3 * ((2 * (e : ℤ) - σ) / 3) + σ = 2 * e := by omega
  have hsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · rw [memA]
    simp only [phi]
    rw [hd, h3]
    refine ⟨by exact_mod_cast hkpos, by omega, ?_⟩
    linear_combination (-1) * h4 + 2 * hNe - (3 * i ^ 2 + i) * hsq
  · rw [Function.mem_support, gS_ne_zero]
    simp only [phi]
    rw [Int.odd_iff]
    omega

private lemma S_injOn (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) :
    Set.InjOn (phi σ n) (↑(Sset σ n)) := by
  rintro ⟨i, e⟩ hx ⟨i', e'⟩ hy h
  rw [Finset.mem_coe, Sset_mem] at hx hy
  have hr := rn_spec σ hσ
  simp only [phi, Prod.mk.injEq] at h
  obtain ⟨h1, -, h3⟩ := h
  have hii : i = i' := by rcases hσ with rfl | rfl <;> omega
  have hee : e = e' := by omega
  subst hii hee
  rfl

private lemma S_surjOn (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) :
    Set.SurjOn (phi σ n) (↑(Sset σ n)) (liouvilleA (3 / 2) ((σ : ℝ) / 2) n ∩ Function.support gS) := by
  rintro ⟨i0, d, δ⟩ ⟨hpA, hps⟩
  rw [memA] at hpA
  rw [Function.mem_support, gS_ne_zero] at hps
  simp only at hpA hps
  obtain ⟨hd, hδ, heq⟩ := hpA
  rw [Int.odd_iff] at hps
  have hr := rn_spec σ hσ
  have hsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = (3 * δ + σ) / 2 :=
    ⟨((3 * δ + σ) / 2).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨i, hi⟩ : ∃ i, i = σ * i0 := ⟨_, rfl⟩
  have hi0 : i0 = σ * i := by
    rw [hi, ← mul_assoc]
    have : σ * σ = 1 := by rw [← sq]; exact hsq
    rw [this, one_mul]
  have h3 : 3 * δ + σ = 2 * e := by omega
  have H1 : 2 * (n : ℤ) = 3 * i ^ 2 + i + 2 * e * d := by
    rw [hi0, h3] at heq
    linear_combination heq + (3 * i ^ 2 + i) * hsq
  have hed : 0 < (e : ℤ) * d := mul_pos (by omega) hd
  have hmem : i ∈ pentIdx n := by
    rw [mem_pentIdx]
    nlinarith
  have h4 := Nn_spec n i hmem
  have hNe : (Nn n i : ℤ) = e * d := by nlinarith
  have hepos : 0 < e := by omega
  refine ⟨⟨i, e⟩, ?_, ?_⟩
  · rw [Finset.mem_coe, Sset_mem]
    refine ⟨hmem, ⟨?_, ?_⟩, by omega⟩
    · exact Int.natCast_dvd_natCast.1 ⟨d, hNe⟩
    · intro h0
      rw [h0] at hNe
      simp at hNe
      omega
  · simp only [phi]
    refine Prod.ext (by show σ * i = i0; exact hi0.symm) (Prod.ext ?_ ?_)
    · simp only
      rw [hNe]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hepos.ne')
    · simp only; omega

private lemma S_eval (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℕ) :
    liouvilleS Fe (3 / 2) ((σ : ℝ) / 2) n =
      ∑ i ∈ pentIdx n, (sg i : ℝ) * (((Nn n i).divisors.filter (· % 3 = rn σ)).card : ℝ) := by
  unfold liouvilleS
  rw [finsum_mem_congr rfl (fun p _ => Fe_S p), ← finsum_mem_inter_support gS]
  have hbij : Set.BijOn (phi σ n) (↑(Sset σ n))
      (liouvilleA (3 / 2) ((σ : ℝ) / 2) n ∩ Function.support gS) :=
    ⟨fun x hx => by
        obtain ⟨i, e⟩ := x
        exact S_mapsTo σ hσ n i e (Finset.mem_coe.1 hx),
      S_injOn σ hσ n, S_surjOn σ hσ n⟩
  rw [← finsum_mem_eq_of_bijOn (f := fun x : Σ _ : ℤ, ℕ => (sg x.1 : ℝ)) (phi σ n) hbij ?_]
  · rw [finsum_mem_coe_finset, Sset, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  · rintro ⟨i, e⟩ hx
    rw [Finset.mem_coe, Sset_mem] at hx
    have hr := rn_spec σ hσ
    obtain ⟨-, -, he3⟩ := hx
    unfold gS phi
    simp only
    have hodd : Odd ((2 * (e : ℤ) - σ) / 3) := by rw [Int.odd_iff]; omega
    simp only [hodd, ite_true]
    rcases hσ with rfl | rfl
    · simp
    · simp [sg_neg]

/-! ### Theorem 2.3 -/

private lemma sg_eq (i : ℤ) : ((-1 : ℤ) ^ i.natAbs) = sg i := by
  unfold sg
  split_ifs with h
  · exact Even.neg_one_pow (Int.natAbs_even.2 h)
  · exact Odd.neg_one_pow (by rw [← Nat.not_even_iff_odd]; exact fun h' => h (Int.natAbs_even.1 h'))

private lemma key (n : ℕ) (hn : 0 < n) :
    ((∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i)) : ℤ) : ℝ) =
      liouvilleT₁ Fe (3 / 2) (((-1 : ℤ) : ℝ) / 2) n - liouvilleT₁ Fe (3 / 2) (((1 : ℤ) : ℝ) / 2) n := by
  have h := theorem22 (3 / 2) (((1 : ℤ) : ℝ) / 2) (by norm_num) Fe Fe_oddx Fe_odd23 n hn
  have hneg : -(((1 : ℤ) : ℝ) / 2) = ((-1 : ℤ) : ℝ) / 2 := by push_cast; ring
  rw [hneg] at h
  have hW : liouvilleW Fe (3 / 2) (((1 : ℤ) : ℝ) / 2) n = 0 := by simpa using W_zero n
  have hU : liouvilleU Fe (3 / 2) (((1 : ℤ) : ℝ) / 2) n = 0 := by simpa using U_zero n
  rw [S_eval 1 (Or.inl rfl) n, S_eval (-1) (Or.inr rfl) n, hW, hU] at h
  have r1 : rn 1 = 2 := by simp [rn]
  have r2 : rn (-1) = 1 := by simp [rn]
  rw [r1, r2] at h
  have : ((∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i)) : ℤ) : ℝ) =
      -(∑ i ∈ pentIdx n, (sg i : ℝ) * (((Nn n i).divisors.filter (· % 3 = 2)).card : ℝ) -
        ∑ i ∈ pentIdx n, (sg i : ℝ) * (((Nn n i).divisors.filter (· % 3 = 1)).card : ℝ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsg : (-1 : ℝ) ^ i.natAbs = (sg i : ℝ) := by rw [← sg_eq]; push_cast; ring
    rw [hsg]
    unfold omega3 Nn
    push_cast
    ring
  rw [this]
  linarith

private lemma pos_neg_impossible (n : ℕ) (s s0 : ℤ) (hs : 0 < s) (hs0 : 0 < s0)
    (h1 : 2 * (n : ℤ) = 3 * s ^ 2 + (-1) * s) (h2 : 2 * (n : ℤ) = 3 * s0 ^ 2 + 1 * s0) : False := by
  have : (s + s0) * (3 * (s - s0) - 1) = 0 := by linear_combination h2 - h1
  rcases mul_eq_zero.1 this with h | h <;> omega

/-- **Moreno–Wagstaff, Theorem 2.3** (Recursion formula for $\omega$; p. 20), proved: the book's single application
of the Second Fundamental Identity (`theorem22`) with $\lambda = 3/2$, $\mu = 1/2$ and
$F(x, y, z) = (-1)^{(x+z)/2+y}$ for $x, z$ odd, $0$ otherwise. Here $U = W = 0$, $T_1 - T_2$ is the
pentagonal term, and $S - S'$ is $-\sum_i (-1)^i \omega(n - (3i^2+i)/2)$ after $\delta = 2k \mp 1$ and
$i \mapsto -i$ in partition (b). -/
@[kb "morenowagstaff2005" "Theorem 2.3, p. 20"]
theorem theorem23 : Theorem23 := by
  intro n hn
  dsimp only
  have hk := key n hn
  constructor
  · intro hno
    have e1 : ¬ ∃ s : ℤ, 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + (1 : ℤ) * s := by
      rintro ⟨s, -, hs⟩
      have h2 := two_mul_natCast_pentagonal_neg s
      apply hno s
      have : (pentagonal (-s) : ℤ) = n := by nlinarith
      exact_mod_cast this
    have e2 : ¬ ∃ s : ℤ, 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + (-1 : ℤ) * s := by
      rintro ⟨s, -, hs⟩
      have h2 := two_mul_natCast_pentagonal_neg (-s)
      apply hno (-s)
      have : (pentagonal (-(-s)) : ℤ) = n := by nlinarith
      exact_mod_cast this
    rw [T_empty 1 n e1, T_empty (-1) n e2] at hk
    have : ((∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i)) : ℤ) : ℝ) = 0 := by
      rw [hk]; ring
    exact_mod_cast this
  · intro s0 hs0
    have h2 := two_mul_natCast_pentagonal_neg s0
    have hs2 : 2 * (n : ℤ) = 3 * s0 ^ 2 + s0 := by
      have : (pentagonal (-s0) : ℤ) = n := by exact_mod_cast hs0
      nlinarith
    rcases lt_trichotomy s0 0 with hlt | heq | hgt
    · have e1 : ¬ ∃ s : ℤ, 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + (1 : ℤ) * s := by
        rintro ⟨s, hs, hs'⟩
        exact pos_neg_impossible n (-s0) s (by omega) hs (by nlinarith) hs'
      rw [T_empty 1 n e1, T_single (-1) (Or.inr rfl) n (-s0) (by omega) (by nlinarith)] at hk
      have : ((∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i)) : ℤ) : ℝ) =
          (((-1 : ℤ) ^ s0.natAbs * s0 : ℤ) : ℝ) := by
        rw [hk, sg_eq]
        have : sg (-s0) = sg s0 := sg_neg s0
        rw [this]
        push_cast
        ring
      exact_mod_cast this
    · subst heq
      have : n = 0 := by simpa using hs2
      omega
    · have e2 : ¬ ∃ s : ℤ, 0 < s ∧ 2 * (n : ℤ) = 3 * s ^ 2 + (-1 : ℤ) * s := by
        rintro ⟨s, hs, hs'⟩
        exact pos_neg_impossible n s s0 hs hgt hs' (by nlinarith)
      rw [T_empty (-1) n e2, T_single 1 (Or.inl rfl) n s0 hgt (by nlinarith)] at hk
      have : ((∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs * omega3 (n - pentagonal (-i)) : ℤ) : ℝ) =
          (((-1 : ℤ) ^ s0.natAbs * s0 : ℤ) : ℝ) := by
        rw [hk, sg_eq]
        push_cast
        ring
      exact_mod_cast this

/-! ### Theorem 2.4: logarithmic derivative of Euler's product -/

section PS

open PowerSeries

/-- $\sum_{j \ge 1} d\,X^{jd}$, i.e. $d X^d / (1 - X^d)$. -/
private noncomputable def Bser (d : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => if d ∣ m ∧ 0 < m then (d : ℤ) else 0

private lemma Bser_mul (d : ℕ) (hd : 0 < d) : (1 - X ^ d) * Bser d = C (d : ℤ) * X ^ d := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_C_mul, coeff_X_pow]
  simp only [Bser, coeff_mk]
  by_cases h1 : d ≤ m
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h1
    simp only [h1, ite_true, Nat.add_sub_cancel_left]
    by_cases h2 : m' = 0
    · subst h2; simp [hd]
    · have h5 : d ∣ d + m' ↔ d ∣ m' := Nat.dvd_add_right (dvd_refl d)
      have h3 : d + m' ≠ d := by omega
      by_cases h4 : d ∣ m' <;> simp [h5, h4, h2, Nat.pos_of_ne_zero h2, hd]
  · have : ¬ (d ∣ m ∧ 0 < m) := fun ⟨h, h'⟩ => h1 (Nat.le_of_dvd h' h)
    have h3 : m ≠ d := by omega
    simp [h1, this, h3]

private noncomputable def Pser (N : ℕ) : ℤ⟦X⟧ := ∏ k ∈ Finset.range N, (1 - X ^ (k + 1))
private noncomputable def Aser (N : ℕ) : ℤ⟦X⟧ := ∑ k ∈ Finset.range N, Bser (k + 1)

private lemma logderiv (N : ℕ) :
    X * derivative (R := ℤ) (Pser N) = -(Pser N * Aser N) := by
  induction N with
  | zero => simp [Pser, Aser]
  | succ N ih =>
    have hP : Pser (N + 1) = Pser N * (1 - X ^ (N + 1)) := Finset.prod_range_succ _ _
    have hA : Aser (N + 1) = Aser N + Bser (N + 1) := Finset.sum_range_succ _ _
    have hg : X * derivative (R := ℤ) (1 - X ^ (N + 1)) = -((1 - X ^ (N + 1)) * Bser (N + 1)) := by
      rw [Bser_mul _ (Nat.succ_pos N), map_sub, derivative_one, derivative_pow, derivative_X]
      simp only [map_natCast, Nat.add_sub_cancel, Nat.succ_eq_add_one]
      push_cast
      ring
    rw [hP, hA, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    calc X * (Pser N * derivative (R := ℤ) (1 - X ^ (N + 1)) +
          (1 - X ^ (N + 1)) * derivative (R := ℤ) (Pser N))
        = Pser N * (X * derivative (R := ℤ) (1 - X ^ (N + 1))) +
          (1 - X ^ (N + 1)) * (X * derivative (R := ℤ) (Pser N)) := by ring
      _ = _ := by rw [hg, ih]; ring

private lemma coeff_Aser (N m : ℕ) (hm : m ≤ N) : coeff m (Aser N) = (ArithmeticFunction.sigma 1 m : ℤ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp [Aser, Bser, coeff_mk]
  have h1 : coeff m (Aser N) = ∑ k ∈ Finset.range N,
      (if (k + 1) ∣ m ∧ 0 < m then (((k + 1 : ℕ)) : ℤ) else 0) := by
    simp [Aser, Bser, coeff_mk, map_sum]
  rw [h1]
  have h2 : ∑ k ∈ Finset.range N, (if (k + 1) ∣ m ∧ 0 < m then (((k + 1 : ℕ)) : ℤ) else 0) =
      ∑ i ∈ Finset.range (N + 1), (if i ∣ m then (i : ℤ) else 0) := by
    rw [Finset.sum_range_succ']
    have h0 : ¬ (0 ∣ m) := by rw [zero_dvd_iff]; omega
    simp [h0, hpos]
  rw [h2, ← Finset.sum_filter, ArithmeticFunction.sigma_one_apply]
  have h3 : (Finset.range (N + 1)).filter (· ∣ m) = m.divisors := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, -⟩; exact ⟨by have := Nat.le_of_dvd hpos h; omega, h⟩
  rw [h3]
  push_cast
  rfl

private lemma coeff_eq (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    coeff n (Pser N) * (n : ℤ) = -∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      coeff p.1 (Pser N) * (ArithmeticFunction.sigma 1 p.2 : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := congrArg (coeff (m + 1)) (logderiv N)
  rw [coeff_succ_X_mul, coeff_derivative, map_neg, coeff_mul] at h
  rw [show ((m.succ : ℕ) : ℤ) = (m : ℤ) + 1 by push_cast; ring, h]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_Aser N p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)]

private lemma exists_N (n : ℕ) :
    ∃ N, n ≤ N ∧ ∀ j ≤ n, coeff j (Pser N) = coeff j (pentagonalSeries ℤ) := by
  have h : ∀ j ∈ Finset.range (n + 1), ∀ᶠ s in Filter.atTop,
      coeff j (∏ k ∈ s, (1 - X ^ (k + 1) : ℤ⟦X⟧)) = coeff j (pentagonalSeries ℤ) :=
    fun j _ => coeff_prod_one_sub_X_pow_eventually_eq ℤ j
  rw [← Filter.eventually_all_finset] at h
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.1 h
  obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range s0
  refine ⟨max n M, le_max_left _ _, fun j hj => ?_⟩
  exact hs0 (Finset.range (max n M)) (hM.trans (Finset.range_mono (le_max_right _ _))) j
    (Finset.mem_range.2 (by omega))

private lemma negOnePow_cast (i : ℤ) : ((Int.negOnePow (-i) : ℤˣ) : ℤ) = (-1 : ℤ) ^ i.natAbs := by
  rw [Int.negOnePow_neg]
  by_cases h : Even i
  · rw [Int.negOnePow_even _ h, Even.neg_one_pow (Int.natAbs_even.2 h)]; rfl
  · have ho : Odd i := Int.not_even_iff_odd.1 h
    rw [Int.negOnePow_odd _ ho, Odd.neg_one_pow
      (by rw [← Nat.not_even_iff_odd]; exact fun h' => h (Int.natAbs_even.1 h'))]
    rfl

private lemma sum_reindex (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff p.1 (pentagonalSeries ℤ) * (ArithmeticFunction.sigma 1 p.2 : ℤ) =
      ∑ i ∈ pentIdx n, (-1 : ℤ) ^ i.natAbs *
        (ArithmeticFunction.sigma 1 (n - pentagonal (-i)) : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
  simp only [Nat.sub_self, ArithmeticFunction.map_zero, Nat.cast_zero, mul_zero, add_zero]
  have hext := fun k : ℕ => coeff_pentagonalSeries_mul_eq_extend ℤ k (fun k => (ArithmeticFunction.sigma 1 (n - k) : ℤ))
  rw [Finset.sum_congr rfl fun k _ => hext k]
  set F : ℕ → ℤ := Function.extend pentagonal
    (fun k : ℤ => (k.negOnePow : ℤ) * (ArithmeticFunction.sigma 1 (n - pentagonal k) : ℤ)) 0 with hF
  have hinj : Set.InjOn (fun i : ℤ => pentagonal (-i)) (↑(pentIdx n)) :=
    fun a _ b _ h => neg_injective (pentagonal_injective h)
  have hsub : (pentIdx n).image (fun i : ℤ => pentagonal (-i)) ⊆ Finset.range n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Finset.mem_filter.1 hi).2
  rw [← Finset.sum_subset hsub, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [pentagonal_injective.extend_apply, negOnePow_cast]
    simp
  · intro x hx hxT
    apply Function.extend_apply'
    rintro ⟨k, hk⟩
    apply hxT
    refine Finset.mem_image.2 ⟨-k, ?_, by rw [neg_neg, hk]⟩
    rw [mem_pentIdx]
    have h2 := two_mul_natCast_pentagonal_neg (-k)
    rw [neg_neg] at h2
    have := Finset.mem_range.1 hx
    rw [hk] at h2
    omega

/-- **Moreno–Wagstaff, Theorem 2.4** (Euler's recurrence for $\sigma$; p. 22), proved by a different route than the
book (which uses the First Fundamental Identity): logarithmic differentiation of Mathlib's pentagonal number
theorem. For the truncated products $P_N = \prod_{k<N}(1 - X^{k+1})$ one has $X P_N' = -P_N A_N$ with
$A_N = \sum_{k<N} \sum_{j \ge 1} (k+1) X^{j(k+1)}$, whose $m$-th coefficient is $\sigma(m)$ for $m \le N$; letting
$N$ be large (`PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq`) gives $n\,c_n = -\sum_{j+m=n} c_j \sigma(m)$ with
$c_j$ the coefficients of the pentagonal series. -/
@[kb "morenowagstaff2005" "Theorem 2.4, p. 22"]
theorem theorem24 : Theorem24 := by
  intro n hn
  dsimp only
  obtain ⟨N, hNn, hN⟩ := exists_N n
  have h := coeff_eq n N hn hNn
  have hsum : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff p.1 (Pser N) * (ArithmeticFunction.sigma 1 p.2 : ℤ) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff p.1 (pentagonalSeries ℤ) * (ArithmeticFunction.sigma 1 p.2 : ℤ) :=
    Finset.sum_congr rfl fun p hp => by
      rw [hN p.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)]
  rw [hsum, sum_reindex, hN n le_rfl] at h
  constructor
  · intro hno
    have h0 : coeff n (pentagonalSeries ℤ) = 0 := by
      apply coeff_pentagonalSeries_eq_zero
      rintro ⟨k, hk⟩
      apply hno (-k)
      rw [neg_neg]; exact hk
    rw [h0] at h
    linarith
  · intro s hs
    have h1 := coeff_pentagonalSeries_pentagonal ℤ (-s)
    rw [hs] at h1
    rw [h1] at h
    have h2 : ((Int.negOnePow (-s) : ℤˣ) : ℤ) = (-1) ^ s.natAbs := negOnePow_cast s
    simp only [Int.coe_negOnePow, Int.natAbs_neg] at h2 h
    rw [pow_succ]
    linarith

end PS

end QuadFormsKB.MorenoWagstaff
