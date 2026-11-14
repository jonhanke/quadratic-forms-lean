/-
# Moreno–Wagstaff 2005, Chapter 2: the identities (2.4)–(2.8) of §2.5 "More identities"

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §2.5, printed pp. 23–25.

**Contents.**
* Definitions: `sqBrace` (the book's brace notation $\{E\}$), and the six partitions of $n$ used in §2.5:
  `sqPartA` (a), `sqPartC` (c), `sqPartE` (e), `sqPartF` (f), `sqPartA1` ($a_1$), `sqPartC1` ($c_1$).
  Triples are always written in the order of `liouvilleA`, i.e. `(i, d, δ)` and `(h, Δ, Δ')`.
* Statements (`def … : Prop`): `Eq24`, `Eq25`, `Eq26`, `Eq27`, `Eq28`.
* Proofs (all **unconditional**): `eq24` is Theorem 2.1 (`theorem21`) at $\lambda = 1$, $\mu = 0$ with $T$ and $U$
  evaluated; `eq25`–`eq28` specialize `eq24` to the book's four choices of $F$ and reindex the sums by explicit
  bijections of the partition sets.
* *Erratum* (found by the numerical check and the proof): the printed right-hand side of (2.7) has the term
  $\{(-1)^{(s-1)/2}\, s\, f(s)\}$; the correct term is $\{(-1)^{(s-1)/2} f(s)\}$ (no factor $s$), because the book's $U$
  is an alternating sum of $s$ signs, which equals $(-1)^{(s-1)/2}$, not $s(-1)^{(s-1)/2}$. `Eq27` states the corrected
  identity.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Liouville

namespace QuadFormsKB.MorenoWagstaff

/-! ### Signs and the brace notation -/

/-- The sign $(-1)^k \in \{1, -1\}$ of an integer $k$, as a real number. -/
private noncomputable def sgnZ (k : ℤ) : ℝ := if k % 2 = 0 then 1 else -1

private lemma neg_one_zpow_eq (k : ℤ) : (-1 : ℝ) ^ k = sgnZ k := by
  unfold sgnZ
  split_ifs with h
  · exact Even.neg_one_zpow (by rw [Int.even_iff]; exact h)
  · exact Odd.neg_one_zpow (by rw [Int.odd_iff]; omega)

private lemma sq_emod_two (i : ℤ) : i ^ 2 % 2 = i % 2 := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
  · subst hk
    have : (2 * k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    omega
  · subst hk
    have : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    omega

private lemma isSquare_of_eq_sq {n : ℕ} {c : ℤ} (h : (n : ℤ) = c ^ 2) : IsSquare n := by
  refine ⟨c.natAbs, ?_⟩
  have h2 : (n : ℤ) = (c.natAbs : ℤ) * c.natAbs := by
    rw [Int.natCast_natAbs, abs_mul_abs_self, h]; ring
  exact_mod_cast h2

open scoped Classical in
/-- **The brace notation $\{E\}$** (Moreno–Wagstaff §2.5, p. 24): for a natural number $n$ and an expression
$E = E(s)$ depending on an integer $s$, `sqBrace n E` is $E(s)$ if $n = s^2$ for a natural number $s$ (taken to be
$s = \lfloor\sqrt n\rfloor$) and $0$ otherwise. For $n > 0$ this is the book's $\{E\}$ ($E$ evaluated at the
positive integer $s$ with $s^2 = n$ if there is one, else $0$). -/
@[kb "morenowagstaff2005" "§2.5, notation {E}, p. 24"]
noncomputable def sqBrace (n : ℕ) (E : ℤ → ℝ) : ℝ :=
  if IsSquare n then E (Nat.sqrt n : ℕ) else 0

private lemma sqBrace_of_sq {n m : ℕ} (hm : n = m * m) (E : ℤ → ℝ) : sqBrace n E = E (m : ℤ) := by
  unfold sqBrace
  rw [if_pos ⟨m, hm⟩, show Nat.sqrt n = m by rw [hm]; exact Nat.sqrt_eq m]

private lemma sqBrace_of_not {n : ℕ} (h : ¬ IsSquare n) (E : ℤ → ℝ) : sqBrace n E = 0 := by
  unfold sqBrace
  rw [if_neg h]

private lemma sqBrace_congr {n : ℕ} (hn : 0 < n) {E E' : ℤ → ℝ}
    (h : ∀ s : ℤ, 0 < s → s ^ 2 = (n : ℤ) → E s = E' s) : sqBrace n E = sqBrace n E' := by
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm, sqBrace_of_sq hm]
    apply h
    · have : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
      exact_mod_cast this
    · have : (n : ℤ) = m * m := by exact_mod_cast hm
      rw [this]; ring
  · rw [sqBrace_of_not hsq, sqBrace_of_not hsq]

private lemma sqBrace_zero (n : ℕ) : sqBrace n (fun _ => 0) = 0 := by
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm]
  · rw [sqBrace_of_not hsq]

private lemma sqBrace_mul (n : ℕ) (c : ℝ) (E : ℤ → ℝ) :
    sqBrace n (fun s => c * E s) = c * sqBrace n E := by
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm, sqBrace_of_sq hm]
  · simp [sqBrace_of_not hsq]

private lemma sqBrace_sub (n : ℕ) (E E' : ℤ → ℝ) :
    sqBrace n (fun s => E s - E' s) = sqBrace n E - sqBrace n E' := by
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm, sqBrace_of_sq hm, sqBrace_of_sq hm]
  · simp [sqBrace_of_not hsq]

/-! ### The partitions of §2.5 -/

/-- **Partition (a)** at $\lambda = 1$, $\mu = 0$ (Moreno–Wagstaff §2.5, p. 23): triples $(i, d, \delta)$ with
$i \in \mathbb Z$, $d, \delta > 0$ and $n = i^2 + \delta d$. (This is `liouvilleA 1 0 n`, see `liouvilleA_one`;
partition (b) is the same set.) -/
@[kb "morenowagstaff2005" "§2.5, partition (a), p. 23"]
def sqPartA (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℤ) = p.1 ^ 2 + p.2.2 * p.2.1}

/-- **Partition (c)** at $\lambda = 1$, $\mu = 0$ (p. 23): triples $(h, \Delta, \Delta')$ with $h \in \mathbb Z$,
$\Delta, \Delta' > 0$ and $n = h^2 + \Delta\Delta'$. (This is `liouvilleC 1 0 n`.) -/
@[kb "morenowagstaff2005" "§2.5, partition (c), p. 23"]
def sqPartC (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℤ) = p.1 ^ 2 + p.2.1 * p.2.2}

/-- **Partition (e)** (p. 24): triples $(i, d, \delta)$ with $i \in \mathbb Z$, $d, \delta > 0$, $d$ odd and
$n = i^2 + 2d\delta$. -/
@[kb "morenowagstaff2005" "§2.5, partition (e), p. 24"]
def sqPartE (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ Odd p.2.1 ∧ (n : ℤ) = p.1 ^ 2 + 2 * p.2.1 * p.2.2}

/-- **Partition (f)** (p. 24): triples $(h, \Delta, \Delta')$ with $h \in \mathbb Z$, $\Delta, \Delta' > 0$ and
$n = 4h^2 + \Delta\Delta'$. (For odd $n$, $\Delta$ and $\Delta'$ are then odd.) -/
@[kb "morenowagstaff2005" "§2.5, partition (f), p. 24"]
def sqPartF (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℤ) = 4 * p.1 ^ 2 + p.2.1 * p.2.2}

/-- **Partition $(a_1)$** (p. 25): triples $(i, d, \delta)$ with $i \in \mathbb Z$, $d, \delta > 0$ and
$n = i^2 + 4d\delta$. -/
@[kb "morenowagstaff2005" "§2.5, partition (a1), p. 25"]
def sqPartA1 (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℤ) = p.1 ^ 2 + 4 * p.2.1 * p.2.2}

/-- **Partition $(c_1)$** (p. 25): triples $(h, \Delta, \Delta')$ with $h \in \mathbb Z$, $\Delta, \Delta' > 0$ and
$n = h^2 + 4\Delta\Delta'$. -/
@[kb "morenowagstaff2005" "§2.5, partition (c1), p. 25"]
def sqPartC1 (n : ℕ) : Set (ℤ × ℤ × ℤ) :=
  {p | 0 < p.2.1 ∧ 0 < p.2.2 ∧ (n : ℤ) = p.1 ^ 2 + 4 * p.2.1 * p.2.2}

@[simp] private lemma mem_sqPartA (n : ℕ) (i d δ : ℤ) :
    (i, d, δ) ∈ sqPartA n ↔ 0 < d ∧ 0 < δ ∧ (n : ℤ) = i ^ 2 + δ * d := Iff.rfl
@[simp] private lemma mem_sqPartC (n : ℕ) (h a b : ℤ) :
    (h, a, b) ∈ sqPartC n ↔ 0 < a ∧ 0 < b ∧ (n : ℤ) = h ^ 2 + a * b := Iff.rfl
@[simp] private lemma mem_sqPartE (n : ℕ) (i d δ : ℤ) :
    (i, d, δ) ∈ sqPartE n ↔ 0 < d ∧ 0 < δ ∧ Odd d ∧ (n : ℤ) = i ^ 2 + 2 * d * δ := Iff.rfl
@[simp] private lemma mem_sqPartF (n : ℕ) (h a b : ℤ) :
    (h, a, b) ∈ sqPartF n ↔ 0 < a ∧ 0 < b ∧ (n : ℤ) = 4 * h ^ 2 + a * b := Iff.rfl
@[simp] private lemma mem_sqPartA1 (n : ℕ) (i d δ : ℤ) :
    (i, d, δ) ∈ sqPartA1 n ↔ 0 < d ∧ 0 < δ ∧ (n : ℤ) = i ^ 2 + 4 * d * δ := Iff.rfl
@[simp] private lemma mem_sqPartC1 (n : ℕ) (h a b : ℤ) :
    (h, a, b) ∈ sqPartC1 n ↔ 0 < a ∧ 0 < b ∧ (n : ℤ) = h ^ 2 + 4 * a * b := Iff.rfl

private lemma liouvilleA_one (n : ℕ) : liouvilleA 1 0 n = sqPartA n := by
  ext p
  simp only [liouvilleA, sqPartA, Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    have : ((n : ℤ) : ℝ) = ((p.1 ^ 2 + p.2.2 * p.2.1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    linarith

private lemma liouvilleC_one (n : ℕ) : liouvilleC 1 0 n = sqPartC n := by
  ext p
  simp only [liouvilleC, sqPartC, Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    have : ((n : ℤ) : ℝ) = ((p.1 ^ 2 + p.2.1 * p.2.2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    linarith

private lemma liouvilleE_one (n : ℕ) : liouvilleE 1 0 n = {s : ℤ | (n : ℤ) = s ^ 2} := by
  ext s
  simp only [liouvilleE, Set.mem_setOf_eq, one_mul, zero_mul, add_zero]
  constructor <;> intro h <;> exact_mod_cast h

private lemma mem_D (n : ℕ) (p : ℤ × ℤ) : p ∈ liouvilleD 1 0 n ↔
    0 < p.1 ∧ 0 < p.2 ∧ p.1 ≡ p.2 [ZMOD 2] ∧ (n : ℤ) * 4 = (p.1 + p.2) ^ 2 := by
  simp only [liouvilleD, Set.mem_setOf_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro h
    have : (((n : ℤ) * 4 : ℤ) : ℝ) = (((p.1 + p.2) ^ 2 : ℤ) : ℝ) := by
      push_cast at h ⊢; linarith
    exact_mod_cast this
  · intro h
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this ⊢
    linarith

/-! ### Generic finsum and finset helpers -/

private lemma finsum_mem_neg' {α : Type*} (s : Set α) (f : α → ℝ) :
    ∑ᶠ i ∈ s, -f i = -∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, finsum_mem_def, ← finsum_neg_distrib]
  exact finsum_congr fun i => by by_cases h : i ∈ s <;> simp [Set.indicator, h]

/-- Restrict a sum over `A` whose summand is `g` on the part where `P` holds and `0` elsewhere. -/
private lemma finsum_mem_ite' {α : Type*} (A : Set α) (P : α → Prop) [DecidablePred P] (G g : α → ℝ)
    (h : ∀ p, G p = if P p then g p else 0) :
    ∑ᶠ p ∈ A, G p = ∑ᶠ p ∈ A ∩ {p | P p}, g p := by
  rw [finsum_mem_def, finsum_mem_def]
  refine finsum_congr fun p => ?_
  by_cases hA : p ∈ A <;> by_cases hP : P p <;> simp [Set.indicator, hA, hP, h p]

private lemma finsum_mem_reindex {α β : Type*} (A : Set α) (P : α → Prop) [DecidablePred P]
    (G g : α → ℝ) (h : ∀ p, G p = if P p then g p else 0) (B : Set β) (φ : β → α)
    (hφ : Set.BijOn φ B (A ∩ {p | P p})) (g' : β → ℝ) (he : ∀ b ∈ B, g' b = g (φ b)) :
    ∑ᶠ p ∈ A, G p = ∑ᶠ b ∈ B, g' b :=
  (finsum_mem_ite' A P G g h).trans (finsum_mem_eq_of_bijOn φ hφ he).symm

private lemma card_odd_Icc' (s : ℤ) (hs : 0 < s) (c : ℝ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), (if Odd j then c else 0) = s * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
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
  have h1 : ((s + 1 - 1).toNat : ℤ) = s := by omega
  have h2 : (((s + 1 - 1).toNat : ℕ) : ℝ) = (s : ℝ) := by exact_mod_cast h1
  rw [h2]

private lemma sum_odd_reindex (g : ℤ → ℝ) (s : ℤ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), (if Odd j then g j else 0) =
      ∑ k ∈ Finset.Icc (1 : ℤ) s, g (2 * k - 1) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => (j + 1) / 2) (fun k => 2 * k - 1) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.odd_iff] at hj
    show g j = g (2 * ((j + 1) / 2) - 1)
    congr 1
    omega

private lemma sum_even_reindex (G : ℤ → ℝ) (s : ℤ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), (if Even j then G ((2 * s - j) / 2) else 0) =
      ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), G k := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => (2 * s - j) / 2) (fun k => 2 * s - 2 * k) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.even_iff] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.even_iff] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Int.even_iff] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro j hj
    rfl

/-- The alternating sum $\sum_{r=0}^{2m} (-1)^r = 1$. -/
private lemma alt_range (m : ℕ) : ∑ r ∈ Finset.range (2 * m + 1), sgnZ (r : ℤ) = 1 := by
  induction m with
  | zero => simp [sgnZ]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    unfold sgnZ
    push_cast
    split_ifs <;> first | omega | norm_num

/-- For $s = 2m + 1$: $\sum_{k=1}^{s} (-1)^{(2k-1-s)/2} = (-1)^m$. -/
private lemma alt_sum (m : ℕ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) (2 * (m : ℤ) + 1), sgnZ ((2 * k - 1 - (2 * (m : ℤ) + 1)) / 2) =
      sgnZ (m : ℤ) := by
  have h1 : ∑ k ∈ Finset.Icc (1 : ℤ) (2 * (m : ℤ) + 1), sgnZ ((2 * k - 1 - (2 * (m : ℤ) + 1)) / 2) =
      ∑ r ∈ Finset.range (2 * m + 1), sgnZ ((r : ℤ) - m) := by
    refine Finset.sum_nbij' (fun k => (k - 1).toNat) (fun r => (r : ℤ) + 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro r hr
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      show sgnZ ((2 * k - 1 - (2 * (m : ℤ) + 1)) / 2) = sgnZ (((k - 1).toNat : ℤ) - m)
      congr 1
      omega
  have h2 : ∀ r : ℕ, sgnZ ((r : ℤ) - m) = sgnZ r * sgnZ m := by
    intro r
    unfold sgnZ
    split_ifs <;> first | omega | norm_num
  rw [h1, Finset.sum_congr rfl (fun r _ => h2 r), ← Finset.sum_mul, alt_range, one_mul]

/-- If `G (-y) = -G y` ... : a sum over a set stable under an involution that negates the summand vanishes. -/
private lemma W_zero_of_neg (G : ℤ → ℤ → ℤ → ℝ) (hG : ∀ x y z, G x (-y) z = -G x y z) (n : ℕ) :
    ∑ᶠ p ∈ sqPartC n, G (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) = 0 := by
  have hbij : Set.BijOn (fun p : ℤ × ℤ × ℤ => (-p.1, p.2.1, p.2.2)) (sqPartC n) (sqPartC n) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨h, a, b⟩ hp
      simp only [mem_sqPartC] at hp ⊢
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨h1, h2, by rw [h3]; ring⟩
    · rintro ⟨h, a, b⟩ _ ⟨h', a', b'⟩ _ hh
      simp only [Prod.mk.injEq] at hh
      obtain ⟨e1, e2, e3⟩ := hh
      rw [neg_inj] at e1
      rw [e1, e2, e3]
    · rintro ⟨h, a, b⟩ hq
      simp only [mem_sqPartC] at hq
      obtain ⟨h1, h2, h3⟩ := hq
      refine ⟨(-h, a, b), ?_, by simp⟩
      simp only [mem_sqPartC]
      exact ⟨h1, h2, by rw [h3]; ring⟩
  have key := finsum_mem_eq_of_bijOn
    (f := fun p : ℤ × ℤ × ℤ => G (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2))
    (g := fun p : ℤ × ℤ × ℤ => -G (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2)) _ hbij (fun p _ => by
      show G (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) = -G (p.2.1 + p.2.2) (-p.1) (p.2.1 - p.2.2)
      rw [hG]; ring)
  rw [finsum_mem_neg'] at key
  linarith

/-! ### (2.4): the first fundamental identity at $\lambda = 1$, $\mu = 0$ -/

private lemma T_eval (F : ℤ → ℤ → ℤ → ℝ) (n : ℕ) (hn : 0 < n) :
    liouvilleT F 1 0 n =
      sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F (2 * s - j) s (2 * s - j)) := by
  unfold liouvilleT
  rw [liouvilleE_one]
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm]
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hset : {s : ℤ | (n : ℤ) = s ^ 2} = {(m : ℤ), -(m : ℤ)} := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      have : (n : ℤ) = (m : ℤ) ^ 2 := by rw [hm]; push_cast; ring
      rw [this]
      constructor
      · intro h
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by linarith)
      · rintro (h | h) <;> rw [h] <;> ring
    rw [hset, finsum_mem_pair (by omega)]
    show _ = 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1), F (2 * (m : ℤ) - j) m (2 * (m : ℤ) - j)
    unfold liouvilleTTerm
    rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
    ring
  · have : {s : ℤ | (n : ℤ) = s ^ 2} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hsq (isSquare_of_eq_sq h)
    rw [this, finsum_mem_empty, sqBrace_of_not hsq]

private lemma U_eval (F : ℤ → ℤ → ℤ → ℝ) (n : ℕ) (hn : 0 < n) :
    liouvilleU F 1 0 n =
      sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F (2 * s) (j - s) (2 * j - 2 * s)) := by
  unfold liouvilleU
  by_cases hsq : IsSquare n
  · obtain ⟨m, hm⟩ := hsq
    rw [sqBrace_of_sq hm]
    show _ = ∑ j ∈ Finset.Icc (1 : ℤ) (2 * (m : ℤ) - 1), F (2 * (m : ℤ)) (j - m) (2 * j - 2 * m)
    have hn' : (n : ℤ) = (m : ℤ) * m := by exact_mod_cast hm
    have hbij : Set.BijOn (fun j : ℤ => (j, 2 * (m : ℤ) - j)) (↑(Finset.Icc (1 : ℤ) (2 * m - 1)))
        (liouvilleD 1 0 n) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_Icc] at hj
        rw [mem_D]
        dsimp only
        refine ⟨by omega, by omega, by rw [Int.ModEq]; omega, ?_⟩
        show (n : ℤ) * 4 = (j + (2 * m - j)) ^ 2
        rw [hn']; ring
      · intro a _ b _ h
        simp only [Prod.mk.injEq] at h
        exact h.1
      · rintro ⟨a, b⟩ hp
        rw [mem_D] at hp
        obtain ⟨h1, h2, h3, h4⟩ := hp
        simp only at h1 h2 h3 h4
        have hprod : (a + b - 2 * m) * (a + b + 2 * m) = 0 := by
          linear_combination (-1) * h4 + 4 * hn'
        have hm0 : 0 ≤ (m : ℤ) := Int.natCast_nonneg m
        rcases mul_eq_zero.1 hprod with h | h
        · refine ⟨a, ?_, ?_⟩
          · rw [Finset.mem_coe, Finset.mem_Icc]; omega
          · exact Prod.ext rfl (by show 2 * (m : ℤ) - a = b; omega)
        · exfalso; omega
    have key := finsum_mem_eq_of_bijOn
      (f := fun j : ℤ => F (2 * (m : ℤ)) (j - m) (2 * j - 2 * m))
      (g := fun p : ℤ × ℤ => F (p.1 + p.2) ((p.1 - p.2) / 2) (p.1 - p.2)) _ hbij (fun j _ => by
        show F (2 * (m : ℤ)) (j - m) (2 * j - 2 * m) =
          F (j + (2 * m - j)) ((j - (2 * m - j)) / 2) (j - (2 * m - j))
        have e2 : (j - (2 * (m : ℤ) - j)) / 2 = j - m := by omega
        have e3 : j - (2 * (m : ℤ) - j) = 2 * j - 2 * m := by ring
        have e1 : j + (2 * (m : ℤ) - j) = 2 * m := by ring
        rw [e2, e3, e1])
    rw [← key, finsum_mem_coe_finset]
  · have : liouvilleD 1 0 n = ∅ := by
      ext p
      rw [mem_D]
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3, h4⟩
      apply hsq
      rw [Int.ModEq] at h3
      refine isSquare_of_eq_sq (c := (p.1 + p.2) / 2) ?_
      have : p.1 + p.2 = 2 * ((p.1 + p.2) / 2) := by omega
      nlinarith
    rw [this, finsum_mem_empty, sqBrace_of_not hsq]

/-- **Moreno–Wagstaff (2.4)** (p. 23): the First Fundamental Identity at $\lambda = 1$, $\mu = 0$. For every
$F : \mathbb Z^3 \to \mathbb R$ that is odd in $x$ and even in $(y, z)$ and every positive integer $n$,
$$2\sum_{(a)} F(\delta - 2i,\ d + i,\ 2d + 2i - \delta) = \sum_{(c)} F(\Delta + \Delta',\ h,\ \Delta - \Delta')
 + T - U,$$
where (a) is `sqPartA n` (triples $(i, d, \delta)$, $n = i^2 + \delta d$), (c) is `sqPartC n` (triples
$(h, \Delta, \Delta')$, $n = h^2 + \Delta\Delta'$), and, with the brace notation `sqBrace` ($\{E\}$ is $E(s)$ if
$n = s^2$ with $s > 0$, else $0$), $T = \{2\sum_{j=1}^{2s-1} F(2s - j, s, 2s - j)\}$ and
$U = \{\sum_{j=1}^{2s-1} F(2s, j - s, 2j - 2s)\}$. -/
@[kb "morenowagstaff2005" "(2.4), p. 23"]
def Eq24 : Prop :=
  ∀ F : ℤ → ℤ → ℤ → ℝ, IsOddIn₁ F → IsEvenIn₂₃ F → ∀ n : ℕ, 0 < n →
    2 * ∑ᶠ p ∈ sqPartA n, F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartC n, F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) +
      sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F (2 * s - j) s (2 * s - j)) -
      sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F (2 * s) (j - s) (2 * j - 2 * s))

/-- **Moreno–Wagstaff (2.4)** (p. 23), proved: Theorem 2.1 (`theorem21`) with $\lambda = 1$, $\mu = 0$, where
$S = S'$ (partitions (a) and (b) coincide), the sum $T$ over (e) $= \{s : n = s^2\} = \{\pm s\}$ doubles the inner sum,
and the sum $U$ over (d) $= \{(j, 2s - j) : 1 \le j \le 2s - 1\}$ becomes the stated sum over $j$. -/
@[kb "morenowagstaff2005" "(2.4), p. 23"]
theorem eq24 : Eq24 := by
  intro F hx hyz n hn
  have h := theorem21 1 0 (by norm_num) F hx hyz n hn
  rw [neg_zero, T_eval F n hn, U_eval F n hn] at h
  have hS : liouvilleS F 1 0 n =
      ∑ᶠ p ∈ sqPartA n, F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) := by
    unfold liouvilleS; rw [liouvilleA_one]
  have hW : liouvilleW F 1 0 n = ∑ᶠ p ∈ sqPartC n, F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) := by
    unfold liouvilleW; rw [liouvilleC_one]
  rw [hS, hW] at h
  linarith

/-! ### (2.5) -/

/-- The book's $F$ for (2.5): $0$ if $x$ or $z$ is even, else $(-1)^{(x+z)/2 + y} f(y)$. -/
private noncomputable def F5 (f : ℤ → ℝ) (x y z : ℤ) : ℝ :=
  if Odd x ∧ Odd z then sgnZ ((x + z) / 2 + y) * f y else 0

private lemma F5_oddx (f : ℤ → ℝ) : IsOddIn₁ (F5 f) := by
  intro x y z
  unfold F5 sgnZ
  simp only [Int.odd_iff]
  split_ifs <;> first | omega | ring1

private lemma F5_even (f : ℤ → ℝ) (hf : ∀ t, f (-t) = -f t) : IsEvenIn₂₃ (F5 f) := by
  intro x y z
  unfold F5 sgnZ
  simp only [Int.odd_iff, hf]
  split_ifs <;> first | omega | ring1

private lemma F5_neg (f : ℤ → ℝ) (hf : ∀ t, f (-t) = -f t) (x y z : ℤ) :
    F5 f x (-y) z = -F5 f x y z := by
  unfold F5 sgnZ
  simp only [hf]
  split_ifs <;> first | omega | ring1

private lemma F5A (f : ℤ → ℝ) (p : ℤ × ℤ × ℤ) :
    F5 f (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      if Odd p.2.2 then sgnZ p.1 * f (p.2.1 + p.1) else 0 := by
  unfold F5 sgnZ
  simp only [Int.odd_iff]
  split_ifs <;> first | omega | ring1

private lemma F5T (f : ℤ → ℝ) (s : ℤ) (hs : 0 < s) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F5 f (2 * s - j) s (2 * s - j) =
      s * (sgnZ (s - 1) * f s) := by
  have pw : ∀ j : ℤ, F5 f (2 * s - j) s (2 * s - j) = if Odd j then sgnZ (s - 1) * f s else 0 := by
    intro j
    unfold F5 sgnZ
    simp only [Int.odd_iff]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl (fun j _ => pw j), card_odd_Icc' s hs]

private lemma F5U (f : ℤ → ℝ) (s : ℤ) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F5 f (2 * s) (j - s) (2 * j - 2 * s) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ Odd (2 * s) := by rw [Int.odd_iff]; omega
  unfold F5
  rw [if_neg (fun h => this h.1)]

/-- **Moreno–Wagstaff (2.5)** (p. 24): for every odd function $f : \mathbb Z \to \mathbb R$ (hypothesis
`∀ t, f (-t) = -f t`) and every positive integer $n$,
$$\sum_{(a),\ \delta\ \mathrm{odd}} (-1)^i f(d + i) = \{(-1)^{s-1}\, s\, f(s)\},$$
where (a) is `sqPartA n` (triples $(i, d, \delta)$, $n = i^2 + \delta d$) restricted to odd $\delta$, and
$\{E\}$ is `sqBrace`. It is (2.4) for $F(x, y, z) = (-1)^{(x+z)/2 + y} f(y)$ if $x, z$ are both odd and $0$
otherwise. -/
@[kb "morenowagstaff2005" "(2.5), p. 24"]
def Eq25 : Prop :=
  ∀ f : ℤ → ℝ, (∀ t, f (-t) = -f t) → ∀ n : ℕ, 0 < n →
    ∑ᶠ p ∈ sqPartA n ∩ {p | Odd p.2.2}, (-1 : ℝ) ^ p.1 * f (p.2.1 + p.1) =
      sqBrace n (fun s => (-1 : ℝ) ^ (s - 1) * (s : ℝ) * f s)

/-- **Moreno–Wagstaff (2.5)** (p. 24), proved from `eq24` with the book's $F$ (the sum over (c) vanishes
by the involution $h \mapsto -h$, $U = 0$ since $x = 2s$ is even, and $T = \{2(-1)^{s-1} s f(s)\}$). -/
@[kb "morenowagstaff2005" "(2.5), p. 24"]
theorem eq25 : Eq25 := by
  intro f hf n hn
  have h := eq24 (F5 f) (F5_oddx f) (F5_even f hf) n hn
  have hA : ∑ᶠ p ∈ sqPartA n, F5 f (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartA n ∩ {p | Odd p.2.2}, sgnZ p.1 * f (p.2.1 + p.1) :=
    finsum_mem_ite' _ (fun p : ℤ × ℤ × ℤ => Odd p.2.2) _ _ (F5A f)
  have hW : ∑ᶠ p ∈ sqPartC n, F5 f (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) = 0 :=
    W_zero_of_neg _ (F5_neg f hf) n
  have hT : sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F5 f (2 * s - j) s (2 * s - j)) =
      2 * sqBrace n (fun s => sgnZ (s - 1) * s * f s) := by
    rw [← sqBrace_mul]
    apply sqBrace_congr hn
    intro s hs _
    simp only [F5T f s hs]
    ring
  have hU : sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F5 f (2 * s) (j - s) (2 * j - 2 * s))
      = 0 := by
    have : (fun s : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F5 f (2 * s) (j - s) (2 * j - 2 * s)) =
        fun _ => 0 := funext fun s => F5U f s
    rw [this, sqBrace_zero]
  rw [hA, hW, hT, hU] at h
  have hB : sqBrace n (fun s => (-1 : ℝ) ^ (s - 1) * (s : ℝ) * f s) =
      sqBrace n (fun s => sgnZ (s - 1) * s * f s) :=
    sqBrace_congr hn (fun s _ _ => by simp only [neg_one_zpow_eq])
  have hz : ∀ p : ℤ × ℤ × ℤ, (-1 : ℝ) ^ p.1 * f (p.2.1 + p.1) = sgnZ p.1 * f (p.2.1 + p.1) :=
    fun p => by rw [neg_one_zpow_eq]
  rw [hB, finsum_mem_congr rfl (fun p _ => hz p)]
  linarith

/-! ### (2.6) and (2.7): the functions `F6`, `F7` and the bijections for (e), (f) -/

private lemma odd_of_sqPartE {n : ℕ} (hn : n % 2 = 1) (i d δ : ℤ) (hp : (i, d, δ) ∈ sqPartE n) :
    i % 2 = 1 := by
  simp only [mem_sqPartE] at hp
  obtain ⟨-, -, -, h⟩ := hp
  have h1 := sq_emod_two i
  have h2 : 2 * d * δ = 2 * (d * δ) := by ring
  omega

private lemma bij_E (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun p : ℤ × ℤ × ℤ => (-p.1, p.2.1, 2 * p.2.2)) (sqPartE n)
      (sqPartA n ∩ {p | Even (p.2.2 - 2 * p.1) ∧ Even (p.2.1 + p.1)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, d, δ⟩ hp
    have hi := odd_of_sqPartE hn i d δ hp
    simp only [mem_sqPartE] at hp
    obtain ⟨hd, hδ, hodd, h⟩ := hp
    rw [Int.odd_iff] at hodd
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartA, Int.even_iff]
    refine ⟨⟨hd, by omega, by rw [h]; ring⟩, by omega, by omega⟩
  · rintro ⟨i, d, δ⟩ _ ⟨i', d', δ'⟩ _ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨e1, e2, e3⟩ := hh
    have : i = i' := by omega
    have : δ = δ' := by omega
    subst_vars
    rfl
  · rintro ⟨i, d, δ⟩ hq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartA, Int.even_iff] at hq
    obtain ⟨⟨hd, hδ, h⟩, h1, h2⟩ := hq
    obtain ⟨k, hk⟩ : ∃ k, δ = 2 * k := ⟨δ / 2, by omega⟩
    have h3 : δ * d = 2 * (k * d) := by rw [hk]; ring
    have h4 := sq_emod_two i
    have hn' : ((n : ℕ) : ℤ) % 2 = 1 := by omega
    refine ⟨(-i, d, k), ?_, ?_⟩
    · simp only [mem_sqPartE]
      refine ⟨hd, by omega, by rw [Int.odd_iff]; omega, ?_⟩
      linear_combination h + d * hk
    · simp only [Prod.mk.injEq]
      refine ⟨by ring, by simp, by omega⟩

private lemma bij_F (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun p : ℤ × ℤ × ℤ => (2 * p.1, p.2.1, p.2.2)) (sqPartF n)
      (sqPartC n ∩ {p | Even (p.2.1 + p.2.2) ∧ Even p.1}) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h, a, b⟩ hp
    simp only [mem_sqPartF] at hp
    obtain ⟨ha, hb, heq⟩ := hp
    have hodd : Odd (a * b) := by rw [Int.odd_iff]; omega
    obtain ⟨hao, hbo⟩ := Int.odd_mul.1 hodd
    rw [Int.odd_iff] at hao hbo
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartC, Int.even_iff]
    refine ⟨⟨ha, hb, by rw [heq]; ring⟩, by omega, by omega⟩
  · rintro ⟨i, d, δ⟩ _ ⟨i', d', δ'⟩ _ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨e1, e2, e3⟩ := hh
    have : i = i' := by omega
    subst_vars
    rfl
  · rintro ⟨h, a, b⟩ hq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartC, Int.even_iff] at hq
    obtain ⟨⟨ha, hb, heq⟩, h1, h2⟩ := hq
    obtain ⟨k, hk⟩ : ∃ k, h = 2 * k := ⟨h / 2, by omega⟩
    refine ⟨(k, a, b), ?_, ?_⟩
    · simp only [mem_sqPartF]
      refine ⟨ha, hb, ?_⟩
      rw [heq, hk]; ring
    · simp only [Prod.mk.injEq]
      refine ⟨by omega, by simp⟩

/-- The book's $F$ for (2.6): $0$ if $x$ or $y$ is odd, else $f(x/2)$. -/
private noncomputable def F6 (f : ℤ → ℝ) (x y _z : ℤ) : ℝ :=
  if Even x ∧ Even y then f (x / 2) else 0

private lemma F6_oddx (f : ℤ → ℝ) (hf : ∀ t, f (-t) = -f t) : IsOddIn₁ (F6 f) := by
  intro x y z
  unfold F6
  simp only [Int.even_iff]
  split_ifs <;> first | omega | (rw [show (-x) / 2 = -(x / 2) by omega, hf]) | simp

private lemma F6_even (f : ℤ → ℝ) : IsEvenIn₂₃ (F6 f) := by
  intro x y z
  unfold F6
  simp only [Int.even_iff]
  split_ifs <;> first | omega | rfl

/-- **Moreno–Wagstaff (2.6)** (p. 25): for every odd function $f : \mathbb Z \to \mathbb R$ and every odd positive
integer $n$,
$$\sum_{(f)} f\!\left(\frac{\Delta + \Delta'}{2}\right) = 2\sum_{(e)} f(\delta + i) + \{s\, f(s)\},$$
where (f) is `sqPartF n` (triples $(h, \Delta, \Delta')$ with $n = 4h^2 + \Delta\Delta'$; then $\Delta, \Delta'$ are
odd, so $(\Delta+\Delta')/2$ is an integer), (e) is `sqPartE n` (triples $(i, d, \delta)$ with $d$ odd and
$n = i^2 + 2d\delta$) and $\{E\}$ is `sqBrace`. It is (2.4) for $F(x, y, z) = f(x/2)$ if $x, y$ are both even and
$0$ otherwise, followed by $i \mapsto -i$. -/
@[kb "morenowagstaff2005" "(2.6), p. 25"]
def Eq26 : Prop :=
  ∀ f : ℤ → ℝ, (∀ t, f (-t) = -f t) → ∀ n : ℕ, 0 < n → Odd n →
    ∑ᶠ p ∈ sqPartF n, f ((p.2.1 + p.2.2) / 2) =
      2 * ∑ᶠ p ∈ sqPartE n, f (p.2.2 + p.1) + sqBrace n (fun s => (s : ℝ) * f s)

private lemma F6U (f : ℤ → ℝ) (s : ℤ) (hs : s % 2 = 1) (hs0 : 0 < s) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F6 f (2 * s) (j - s) (2 * j - 2 * s) = s * f s := by
  have pw : ∀ j : ℤ, F6 f (2 * s) (j - s) (2 * j - 2 * s) = if Odd j then f s else 0 := by
    intro j
    unfold F6
    rw [show 2 * s / 2 = s by omega]
    simp only [Int.even_iff, Int.odd_iff]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl (fun j _ => pw j), card_odd_Icc' s hs0]

private lemma F6T (f : ℤ → ℝ) (s : ℤ) (hs : s % 2 = 1) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F6 f (2 * s - j) s (2 * s - j) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  have : ¬ Even s := by rw [Int.even_iff]; omega
  unfold F6
  rw [if_neg (fun h => this h.2)]

private lemma odd_sq_of_odd {n : ℕ} (hn : n % 2 = 1) {s : ℤ} (hs : s ^ 2 = (n : ℤ)) : s % 2 = 1 := by
  have := sq_emod_two s
  omega

/-- **Moreno–Wagstaff (2.6)** (p. 25), proved from `eq24` (see `Eq26`). -/
@[kb "morenowagstaff2005" "(2.6), p. 25"]
theorem eq26 : Eq26 := by
  intro f hf n hn hodd
  have hn2 : n % 2 = 1 := Nat.odd_iff.1 hodd
  have h := eq24 (F6 f) (F6_oddx f hf) (F6_even f) n hn
  have hA : ∑ᶠ p ∈ sqPartA n, F6 f (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartE n, f (p.2.2 + p.1) :=
    finsum_mem_reindex (sqPartA n)
      (fun p : ℤ × ℤ × ℤ => Even (p.2.2 - 2 * p.1) ∧ Even (p.2.1 + p.1)) _
      (fun p => f ((p.2.2 - 2 * p.1) / 2)) (fun p => rfl) (sqPartE n) _ (bij_E n hn2)
      (fun p => f (p.2.2 + p.1)) (fun b _ => by
        show f (b.2.2 + b.1) = f ((2 * b.2.2 - 2 * -b.1) / 2)
        congr 1; omega)
  have hW : ∑ᶠ p ∈ sqPartC n, F6 f (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartF n, f ((p.2.1 + p.2.2) / 2) :=
    finsum_mem_reindex (sqPartC n) (fun p : ℤ × ℤ × ℤ => Even (p.2.1 + p.2.2) ∧ Even p.1) _
      (fun p => f ((p.2.1 + p.2.2) / 2)) (fun p => rfl) (sqPartF n) _ (bij_F n hn2)
      (fun p => f ((p.2.1 + p.2.2) / 2)) (fun b _ => rfl)
  have hT : sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F6 f (2 * s - j) s (2 * s - j))
      = 0 := by
    refine (sqBrace_congr hn (E' := fun _ => 0) (fun s _ hs => ?_)).trans (sqBrace_zero n)
    simp only [F6T f s (odd_sq_of_odd hn2 hs), mul_zero]
  have hU : sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F6 f (2 * s) (j - s) (2 * j - 2 * s))
      = sqBrace n (fun s => (s : ℝ) * f s) :=
    sqBrace_congr hn (fun s h0 hs => F6U f s (odd_sq_of_odd hn2 hs) h0)
  rw [hA, hW, hT, hU] at h
  linarith

/-- The book's $F$ for (2.7): $0$ if $x$ or $y$ is odd, else $(-1)^{y/2} f(x/2)$. -/
private noncomputable def F7 (f : ℤ → ℝ) (x y _z : ℤ) : ℝ :=
  if Even x ∧ Even y then sgnZ (y / 2) * f (x / 2) else 0

private lemma F7_oddx (f : ℤ → ℝ) (hf : ∀ t, f (-t) = -f t) : IsOddIn₁ (F7 f) := by
  intro x y z
  unfold F7
  simp only [Int.even_iff]
  split_ifs <;> first | omega | (rw [show (-x) / 2 = -(x / 2) by omega, hf]; ring) | simp

private lemma F7_even (f : ℤ → ℝ) : IsEvenIn₂₃ (F7 f) := by
  intro x y z
  unfold F7 sgnZ
  simp only [Int.even_iff]
  split_ifs <;> first | omega | rfl | ring1

/-- **Moreno–Wagstaff (2.7)** (p. 25), *corrected form*: for every odd function $f : \mathbb Z \to \mathbb R$ and every
odd positive integer $n$,
$$\sum_{(f)} (-1)^h f\!\left(\frac{\Delta + \Delta'}{2}\right)
 = 2\sum_{(e)} (-1)^{(d-1)/2 + (i-1)/2} f(\delta + i) + \{(-1)^{(s-1)/2} f(s)\},$$
with (f) = `sqPartF n` (triples $(h, \Delta, \Delta')$), (e) = `sqPartE n` (triples $(i, d, \delta)$; $d$ and $i$ are
odd for odd $n$, so $(d-1)/2$, $(i-1)/2$ are integers) and $\{E\}$ = `sqBrace`.
*Erratum:* the printed identity has $\{(-1)^{(s-1)/2}\, s\, f(s)\}$ as last term. That is false (e.g. $n = 9$, $f(t) = t$:
left side $1$, printed right side $-5$); the factor $s$ must be dropped, since
$U = \sum_{j} (-1)^{(j-s)/2} f(s)$ over odd $j \in [1, 2s-1]$ is an alternating sum of $s$ signs, equal to
$(-1)^{(s-1)/2} f(s)$. -/
@[kb "morenowagstaff2005" "(2.7), p. 25"]
def Eq27 : Prop :=
  ∀ f : ℤ → ℝ, (∀ t, f (-t) = -f t) → ∀ n : ℕ, 0 < n → Odd n →
    ∑ᶠ p ∈ sqPartF n, (-1 : ℝ) ^ p.1 * f ((p.2.1 + p.2.2) / 2) =
      2 * ∑ᶠ p ∈ sqPartE n, (-1 : ℝ) ^ ((p.2.1 - 1) / 2 + (p.1 - 1) / 2) * f (p.2.2 + p.1) +
      sqBrace n (fun s => (-1 : ℝ) ^ ((s - 1) / 2) * f s)

private lemma F7U (f : ℤ → ℝ) (s : ℤ) (hs : s % 2 = 1) (hs0 : 0 < s) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F7 f (2 * s) (j - s) (2 * j - 2 * s) =
      sgnZ ((s - 1) / 2) * f s := by
  have pw : ∀ j : ℤ, F7 f (2 * s) (j - s) (2 * j - 2 * s) =
      if Odd j then sgnZ ((j - s) / 2) * f s else 0 := by
    intro j
    unfold F7
    rw [show 2 * s / 2 = s by omega]
    simp only [Int.even_iff, Int.odd_iff]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl (fun j _ => pw j), sum_odd_reindex (fun j => sgnZ ((j - s) / 2) * f s) s]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s = 2 * (m : ℤ) + 1 := ⟨(s / 2).toNat, by omega⟩
  subst hm
  rw [← Finset.sum_mul, alt_sum m]
  congr 2
  omega

/-- **Moreno–Wagstaff (2.7)** (p. 25), proved from `eq24` (see `Eq27` for the corrected statement). -/
@[kb "morenowagstaff2005" "(2.7), p. 25"]
theorem eq27 : Eq27 := by
  intro f hf n hn hodd
  have hn2 : n % 2 = 1 := Nat.odd_iff.1 hodd
  have h := eq24 (F7 f) (F7_oddx f hf) (F7_even f) n hn
  have hA : ∑ᶠ p ∈ sqPartA n, F7 f (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartE n, sgnZ ((p.2.1 - 1) / 2 + (p.1 - 1) / 2) * f (p.2.2 + p.1) := by
    refine (finsum_mem_reindex (sqPartA n)
      (fun p : ℤ × ℤ × ℤ => Even (p.2.2 - 2 * p.1) ∧ Even (p.2.1 + p.1)) _
      (fun p => sgnZ ((p.2.1 + p.1) / 2) * f ((p.2.2 - 2 * p.1) / 2)) (fun p => rfl) (sqPartE n) _
      (bij_E n hn2) (fun p => sgnZ ((p.2.1 - p.1) / 2) * f (p.2.2 + p.1)) (fun b _ => by
        show sgnZ ((b.2.1 - b.1) / 2) * f (b.2.2 + b.1) =
          sgnZ ((b.2.1 + -b.1) / 2) * f ((2 * b.2.2 - 2 * -b.1) / 2)
        have e : (2 * b.2.2 - 2 * -b.1) / 2 = b.2.2 + b.1 := by omega
        rw [e]
        congr 2)).trans ?_
    refine finsum_mem_congr rfl (fun p hp => ?_)
    obtain ⟨i, d, δ⟩ := p
    have hi := odd_of_sqPartE hn2 i d δ hp
    have hd : d % 2 = 1 := by
      have := hp
      simp only [mem_sqPartE, Int.odd_iff] at this
      exact this.2.2.1
    show sgnZ ((d - i) / 2) * f (δ + i) = sgnZ ((d - 1) / 2 + (i - 1) / 2) * f (δ + i)
    congr 1
    unfold sgnZ
    split_ifs <;> first | omega | rfl
  have hW : ∑ᶠ p ∈ sqPartC n, F7 f (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartF n, sgnZ p.1 * f ((p.2.1 + p.2.2) / 2) :=
    finsum_mem_reindex (sqPartC n) (fun p : ℤ × ℤ × ℤ => Even (p.2.1 + p.2.2) ∧ Even p.1) _
      (fun p => sgnZ (p.1 / 2) * f ((p.2.1 + p.2.2) / 2)) (fun p => rfl) (sqPartF n) _ (bij_F n hn2)
      (fun p => sgnZ p.1 * f ((p.2.1 + p.2.2) / 2)) (fun b _ => by
        show sgnZ b.1 * f ((b.2.1 + b.2.2) / 2) = sgnZ (2 * b.1 / 2) * f ((b.2.1 + b.2.2) / 2)
        rw [show 2 * b.1 / 2 = b.1 by omega])
  have hT : sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F7 f (2 * s - j) s (2 * s - j))
      = 0 := by
    refine (sqBrace_congr hn (E' := fun _ => 0) (fun s _ hs => ?_)).trans (sqBrace_zero n)
    have hso := odd_sq_of_odd hn2 hs
    have : ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F7 f (2 * s - j) s (2 * s - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have : ¬ Even s := by rw [Int.even_iff]; omega
      unfold F7
      rw [if_neg (fun h => this h.2)]
    simp only [this, mul_zero]
  have hU : sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F7 f (2 * s) (j - s) (2 * j - 2 * s))
      = sqBrace n (fun s => sgnZ ((s - 1) / 2) * f s) :=
    sqBrace_congr hn (fun s hs0 hs => F7U f s (odd_sq_of_odd hn2 hs) hs0)
  rw [hA, hW, hT, hU] at h
  have hB : sqBrace n (fun s => (-1 : ℝ) ^ ((s - 1) / 2) * f s) =
      sqBrace n (fun s => sgnZ ((s - 1) / 2) * f s) :=
    sqBrace_congr hn (fun s _ _ => by simp only [neg_one_zpow_eq])
  have hz1 : ∀ p : ℤ × ℤ × ℤ, (-1 : ℝ) ^ p.1 * f ((p.2.1 + p.2.2) / 2) =
      sgnZ p.1 * f ((p.2.1 + p.2.2) / 2) := fun p => by rw [neg_one_zpow_eq]
  have hz2 : ∀ p : ℤ × ℤ × ℤ, (-1 : ℝ) ^ ((p.2.1 - 1) / 2 + (p.1 - 1) / 2) * f (p.2.2 + p.1) =
      sgnZ ((p.2.1 - 1) / 2 + (p.1 - 1) / 2) * f (p.2.2 + p.1) := fun p => by rw [neg_one_zpow_eq]
  rw [hB, finsum_mem_congr rfl (fun p _ => hz1 p), finsum_mem_congr rfl (fun p _ => hz2 p)]
  linarith

/-! ### (2.8) -/

/-- The book's $F$ for (2.8): $0$ if $x$ is odd or $y$ is even, else $f(x/2)$. -/
private noncomputable def F8 (f : ℤ → ℝ) (x y _z : ℤ) : ℝ :=
  if Even x ∧ Odd y then f (x / 2) else 0

private lemma F8_oddx (f : ℤ → ℝ) (hf : ∀ t, f (-t) = -f t) : IsOddIn₁ (F8 f) := by
  intro x y z
  unfold F8
  simp only [Int.even_iff, Int.odd_iff]
  split_ifs <;> first | omega | (rw [show (-x) / 2 = -(x / 2) by omega, hf]) | simp

private lemma F8_even (f : ℤ → ℝ) : IsEvenIn₂₃ (F8 f) := by
  intro x y z
  unfold F8
  simp only [Int.even_iff, Int.odd_iff]
  split_ifs <;> first | omega | rfl

private lemma bij_A1 (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun p : ℤ × ℤ × ℤ => (-p.1, 2 * p.2.1, 2 * p.2.2)) (sqPartA1 n)
      (sqPartA n ∩ {p | Even (p.2.2 - 2 * p.1) ∧ Odd (p.2.1 + p.1)}) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, d, δ⟩ hp
    simp only [mem_sqPartA1] at hp
    obtain ⟨hd, hδ, h⟩ := hp
    have h1 := sq_emod_two i
    have h2 : 4 * d * δ = 2 * (2 * (d * δ)) := by ring
    have hi : i % 2 = 1 := by omega
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartA, Int.even_iff, Int.odd_iff]
    refine ⟨⟨by omega, by omega, by rw [h]; ring⟩, by omega, by omega⟩
  · rintro ⟨i, d, δ⟩ _ ⟨i', d', δ'⟩ _ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨e1, e2, e3⟩ := hh
    have : i = i' := by omega
    have : d = d' := by omega
    have : δ = δ' := by omega
    subst_vars
    rfl
  · rintro ⟨i, d, δ⟩ hq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartA, Int.even_iff, Int.odd_iff] at hq
    obtain ⟨⟨hd, hδ, h⟩, h1, h2⟩ := hq
    obtain ⟨k, hk⟩ : ∃ k, δ = 2 * k := ⟨δ / 2, by omega⟩
    have h3 : δ * d = 2 * (k * d) := by rw [hk]; ring
    have h4 := sq_emod_two i
    have hi : i % 2 = 1 := by omega
    obtain ⟨e, he⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    refine ⟨(-i, e, k), ?_, ?_⟩
    · simp only [mem_sqPartA1]
      refine ⟨by omega, by omega, ?_⟩
      rw [h, hk, he]; ring
    · simp only [Prod.mk.injEq]
      refine ⟨by ring, by omega, by omega⟩

private lemma bij_C1 (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun p : ℤ × ℤ × ℤ => (p.1, 2 * p.2.1, 2 * p.2.2)) (sqPartC1 n)
      (sqPartC n ∩ {p | Even (p.2.1 + p.2.2) ∧ Odd p.1}) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h, a, b⟩ hp
    simp only [mem_sqPartC1] at hp
    obtain ⟨ha, hb, heq⟩ := hp
    have h1 := sq_emod_two h
    have h2 : 4 * a * b = 2 * (2 * (a * b)) := by ring
    have hh : h % 2 = 1 := by omega
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartC, Int.even_iff, Int.odd_iff]
    refine ⟨⟨by omega, by omega, by rw [heq]; ring⟩, by omega, hh⟩
  · rintro ⟨i, d, δ⟩ _ ⟨i', d', δ'⟩ _ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨e1, e2, e3⟩ := hh
    have : d = d' := by omega
    have : δ = δ' := by omega
    subst_vars
    rfl
  · rintro ⟨h, a, b⟩ hq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_sqPartC, Int.even_iff, Int.odd_iff] at hq
    obtain ⟨⟨ha, hb, heq⟩, h1, h2⟩ := hq
    have h3 := sq_emod_two h
    have hprod : Even (a * b) := by
      rw [Int.even_iff]
      omega
    have hab : a % 2 = 0 ∧ b % 2 = 0 := by
      rcases Int.even_mul.1 hprod with hE | hE <;> rw [Int.even_iff] at hE <;> omega
    obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' := ⟨a / 2, by omega⟩
    obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
    refine ⟨(h, a', b'), ?_, ?_⟩
    · simp only [mem_sqPartC1]
      refine ⟨by omega, by omega, ?_⟩
      rw [heq, ha', hb']; ring
    · simp only [Prod.mk.injEq]
      exact ⟨by simp, by omega, by omega⟩

/-- **Moreno–Wagstaff (2.8)** (p. 25): for every odd function $f : \mathbb Z \to \mathbb R$ and every positive
integer $n \equiv 1 \pmod 4$,
$$2\sum_{(a_1)} f(\delta + i) = \sum_{(c_1)} f(\Delta + \Delta')
 + \Bigl\{2\sum_{k=1}^{s-1} f(k) - (s-1) f(s)\Bigr\},$$
where $(a_1)$ is `sqPartA1 n` (triples $(i, d, \delta)$ with $n = i^2 + 4d\delta$), $(c_1)$ is `sqPartC1 n`
(triples $(h, \Delta, \Delta')$ with $n = h^2 + 4\Delta\Delta'$) and $\{E\}$ is `sqBrace`. It is (2.4) for
$F(x, y, z) = f(x/2)$ if $x$ is even and $y$ is odd, and $0$ otherwise. (The proof uses only that $n$ is odd.) -/
@[kb "morenowagstaff2005" "(2.8), p. 25"]
def Eq28 : Prop :=
  ∀ f : ℤ → ℝ, (∀ t, f (-t) = -f t) → ∀ n : ℕ, 0 < n → n % 4 = 1 →
    2 * ∑ᶠ p ∈ sqPartA1 n, f (p.2.2 + p.1) =
      ∑ᶠ p ∈ sqPartC1 n, f (p.2.1 + p.2.2) +
      sqBrace n (fun s => 2 * ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k - ((s : ℝ) - 1) * f s)

private lemma F8T (f : ℤ → ℝ) (s : ℤ) (hs : s % 2 = 1) (hs0 : 0 < s) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F8 f (2 * s - j) s (2 * s - j) =
      ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k := by
  have pw : ∀ j : ℤ, F8 f (2 * s - j) s (2 * s - j) = if Even j then f ((2 * s - j) / 2) else 0 := by
    intro j
    unfold F8
    simp only [Int.even_iff, Int.odd_iff]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl (fun j _ => pw j), sum_even_reindex f s]

private lemma F8U (f : ℤ → ℝ) (s : ℤ) (hs : s % 2 = 1) (hs0 : 0 < s) :
    ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F8 f (2 * s) (j - s) (2 * j - 2 * s) =
      ((s : ℝ) - 1) * f s := by
  have pw : ∀ j : ℤ, F8 f (2 * s) (j - s) (2 * j - 2 * s) =
      if Even j then (fun _ : ℤ => f s) ((2 * s - j) / 2) else 0 := by
    intro j
    unfold F8
    rw [show 2 * s / 2 = s by omega]
    simp only [Int.even_iff, Int.odd_iff]
    split_ifs <;> first | omega | rfl
  rw [Finset.sum_congr rfl (fun j _ => pw j), sum_even_reindex (fun _ => f s) s, Finset.sum_const,
    nsmul_eq_mul, Int.card_Icc]
  have h1 : ((s - 1 + 1 - 1).toNat : ℤ) = s - 1 := by omega
  have h2 : (((s - 1 + 1 - 1).toNat : ℕ) : ℝ) = (s : ℝ) - 1 := by
    have : (((s - 1 + 1 - 1).toNat : ℕ) : ℝ) = (((s - 1 + 1 - 1).toNat : ℤ) : ℝ) := by norm_cast
    rw [this, h1]; push_cast; ring
  rw [h2]

/-- **Moreno–Wagstaff (2.8)** (p. 25), proved from `eq24` (see `Eq28`). -/
@[kb "morenowagstaff2005" "(2.8), p. 25"]
theorem eq28 : Eq28 := by
  intro f hf n hn hn4
  have hn2 : n % 2 = 1 := by omega
  have h := eq24 (F8 f) (F8_oddx f hf) (F8_even f) n hn
  have hA : ∑ᶠ p ∈ sqPartA n, F8 f (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartA1 n, f (p.2.2 + p.1) :=
    finsum_mem_reindex (sqPartA n)
      (fun p : ℤ × ℤ × ℤ => Even (p.2.2 - 2 * p.1) ∧ Odd (p.2.1 + p.1)) _
      (fun p => f ((p.2.2 - 2 * p.1) / 2)) (fun p => rfl) (sqPartA1 n) _ (bij_A1 n hn2)
      (fun p => f (p.2.2 + p.1)) (fun b _ => by
        show f (b.2.2 + b.1) = f ((2 * b.2.2 - 2 * -b.1) / 2)
        congr 1; omega)
  have hW : ∑ᶠ p ∈ sqPartC n, F8 f (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) =
      ∑ᶠ p ∈ sqPartC1 n, f (p.2.1 + p.2.2) :=
    finsum_mem_reindex (sqPartC n) (fun p : ℤ × ℤ × ℤ => Even (p.2.1 + p.2.2) ∧ Odd p.1) _
      (fun p => f ((p.2.1 + p.2.2) / 2)) (fun p => rfl) (sqPartC1 n) _ (bij_C1 n hn2)
      (fun p => f (p.2.1 + p.2.2)) (fun b _ => by
        show f (b.2.1 + b.2.2) = f ((2 * b.2.1 + 2 * b.2.2) / 2)
        congr 1; omega)
  have hT : sqBrace n (fun s => 2 * ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F8 f (2 * s - j) s (2 * s - j))
      = sqBrace n (fun s => 2 * ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k) :=
    sqBrace_congr hn (fun s hs0 hs => by
      simp only [F8T f s (odd_sq_of_odd hn2 hs) hs0])
  have hU : sqBrace n (fun s => ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1), F8 f (2 * s) (j - s) (2 * j - 2 * s))
      = sqBrace n (fun s => ((s : ℝ) - 1) * f s) :=
    sqBrace_congr hn (fun s hs0 hs => F8U f s (odd_sq_of_odd hn2 hs) hs0)
  have hsub : sqBrace n (fun s => 2 * ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k - ((s : ℝ) - 1) * f s) =
      sqBrace n (fun s => 2 * ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k) -
        sqBrace n (fun s => ((s : ℝ) - 1) * f s) :=
    sqBrace_sub n (fun s => 2 * ∑ k ∈ Finset.Icc (1 : ℤ) (s - 1), f k) (fun s => ((s : ℝ) - 1) * f s)
  rw [hA, hW, hT, hU] at h
  rw [hsub]
  linarith

end QuadFormsKB.MorenoWagstaff
