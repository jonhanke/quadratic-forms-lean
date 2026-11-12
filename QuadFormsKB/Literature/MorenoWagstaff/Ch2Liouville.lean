/-
# Moreno–Wagstaff 2005, Chapter 2: Liouville's fundamental identities (Theorems 2.1, 2.2)

**Source.** C. J. Moreno and S. S. Wagstaff Jr., *Sums of Squares of Integers* (2005), §2.3, pp. 15–18.

**Proves**
* `theorem21` (Theorem 2.1, **proved**) and `theorem22` (Theorem 2.2, **proved**): the book's argument.
  Split $S$ according to the sign of $2i + d - \delta$. The part $>0$ vanishes by the involution
  $(i, d, \delta) \mapsto (\delta - i, 2i + d - \delta, \delta)$ (oddness of $F$ in $x$); the part $=0$ is the
  part of $T$ with $s > 0$; the part $<0$ is the part of $W$ with $\Delta' - \Delta + 2h > 0$
  (bijection $(i,d,\delta) \mapsto (d + i, d, \delta - d - 2i)$). For $S'$ one passes from the part of $W$ with
  $\Delta' - \Delta + 2h > 0$ over (c) for $-\mu$ to the part with $< 0$ over (c) for $\mu$ by
  $(h, \Delta, \Delta') \mapsto (-h, \Delta', \Delta)$ and the parity of $F$ in $(y, z)$; the part of $W$ with
  $\Delta' - \Delta + 2h = 0$ is $U$.
-/
import QuadFormsKB.Literature.MorenoWagstaff.Ch2Statements

namespace QuadFormsKB.MorenoWagstaff

/-! ### Generic finsum helpers -/

private lemma split_pred {α : Type*} {s : Set α} (hs : s.Finite) (P : α → Prop) (f : α → ℝ) :
    ∑ᶠ x ∈ s, f x = ∑ᶠ x ∈ s ∩ {x | P x}, f x + ∑ᶠ x ∈ s ∩ {x | ¬ P x}, f x := by
  rw [← finsum_mem_inter_add_sdiff {x | P x} hs, Set.sdiff_eq]
  rfl

/-! ### Finiteness of the partition sets -/

private lemma key_ineq (lam mu : ℝ) (h : |mu| < lam) (k : ℤ) :
    (lam - |mu|) * |(k : ℝ)| ≤ lam * (k : ℝ) ^ 2 + mu * k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have h2 : -(|mu| * |(k : ℝ)|) ≤ mu * k := by
    have := neg_abs_le (mu * k)
    rwa [abs_mul] at this
  have h3 : (k : ℝ) ^ 2 = |(k : ℝ)| ^ 2 := (sq_abs _).symm
  have h4 : 0 ≤ |mu| := abs_nonneg _
  have h5 : 0 < lam := by linarith
  have h6 : lam * |(k : ℝ)| ≤ lam * |(k : ℝ)| ^ 2 := by
    have := mul_nonneg (mul_nonneg h5.le (by linarith : (0 : ℝ) ≤ |(k : ℝ)|))
      (by linarith : (0 : ℝ) ≤ |(k : ℝ)| - 1)
    nlinarith
  rw [h3]
  nlinarith

private lemma abs_le_ceil (eps : ℝ) (heps : 0 < eps) (n : ℕ) (x : ℤ) (h : eps * |(x : ℝ)| ≤ n) :
    |x| ≤ (⌈(n : ℝ) / eps⌉₊ : ℤ) := by
  have h1 : |(x : ℝ)| ≤ (n : ℝ) / eps := by
    rw [le_div_iff₀ heps]; linarith
  have h2 : (n : ℝ) / eps ≤ (⌈(n : ℝ) / eps⌉₊ : ℝ) := Nat.le_ceil _
  have : |(x : ℝ)| ≤ ((⌈(n : ℝ) / eps⌉₊ : ℤ) : ℝ) := by push_cast; linarith
  have h3 : ((|x| : ℤ) : ℝ) ≤ ((⌈(n : ℝ) / eps⌉₊ : ℤ) : ℝ) := by push_cast at this ⊢; exact this
  exact_mod_cast h3

private lemma finite_E (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) : (liouvilleE lam mu n).Finite := by
  have heps : 0 < lam - |mu| := by linarith
  apply (Set.finite_Icc (-(⌈(n : ℝ) / (lam - |mu|)⌉₊ : ℤ)) (⌈(n : ℝ) / (lam - |mu|)⌉₊ : ℤ)).subset
  intro s hs
  have hs' : (n : ℝ) = lam * (s : ℝ) ^ 2 + mu * s := hs
  have := abs_le_ceil _ heps n s (by have := key_ineq lam mu h s; linarith)
  rw [abs_le] at this
  exact this

private lemma finite_C (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) : (liouvilleC lam mu n).Finite := by
  have heps : 0 < lam - |mu| := by linarith
  set N : ℤ := (⌈(n : ℝ) / (lam - |mu|)⌉₊ : ℤ) with hN
  apply ((Set.finite_Icc (-N) N).prod ((Set.finite_Icc 1 N).prod (Set.finite_Icc 1 N))).subset
  rintro ⟨k, a, b⟩ ⟨ha, hb, he⟩
  simp only at ha hb he
  have hk := key_ineq lam mu h k
  have hab : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbb : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlam : 0 < lam := by linarith [abs_nonneg mu]
  have hab0 : (0 : ℝ) ≤ (lam - |mu|) * |(k : ℝ)| := by positivity
  have hprod : lam * (a : ℝ) ≤ lam * a * b := by
    have := mul_nonneg (mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤ a)) (by linarith : (0 : ℝ) ≤ b - 1)
    nlinarith
  have hprod' : lam * (b : ℝ) ≤ lam * a * b := by
    have := mul_nonneg (mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤ b)) (by linarith : (0 : ℝ) ≤ a - 1)
    nlinarith
  have hab2 : 0 ≤ lam * (a : ℝ) * b :=
    mul_nonneg (mul_nonneg hlam.le (by linarith)) (by linarith)
  have hle :(lam - |mu|) * |(a : ℝ)| ≤ n := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < a)]
    have : (lam - |mu|) * a ≤ lam * a := by nlinarith [abs_nonneg mu]
    nlinarith
  have hle' : (lam - |mu|) * |(b : ℝ)| ≤ n := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < b)]
    have : (lam - |mu|) * b ≤ lam * b := by nlinarith [abs_nonneg mu]
    nlinarith
  have h1 := abs_le_ceil _ heps n k (by linarith)
  have h2 := abs_le_ceil _ heps n a hle
  have h3 := abs_le_ceil _ heps n b hle'
  rw [abs_le] at h1
  rw [abs_of_pos ha] at h2
  rw [abs_of_pos hb] at h3
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨h1, ⟨by omega, h2⟩, ⟨by omega, h3⟩⟩

private lemma finite_A (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) : (liouvilleA lam mu n).Finite := by
  have heps : 0 < lam - |mu| := by linarith
  set N : ℤ := (⌈(n : ℝ) / (lam - |mu|)⌉₊ : ℤ) with hN
  apply ((Set.finite_Icc (-N) N).prod ((Set.finite_Icc 1 N).prod (Set.finite_Icc 1 N))).subset
  rintro ⟨i, d, e⟩ ⟨hd, he, hn⟩
  simp only at hd he hn
  have hi := key_ineq lam mu h i
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hee : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hlam : 0 < lam := by linarith [abs_nonneg mu]
  have hm : 0 ≤ |mu| := abs_nonneg _
  have hmu : -|mu| ≤ mu := neg_abs_le mu
  have hcoef : (lam - |mu|) * e ≤ lam * e + mu := by nlinarith
  have hpos : 0 ≤ (lam - |mu|) * (e : ℝ) * d := by positivity
  have hpd : (lam - |mu|) * (e : ℝ) * d ≤ (lam * e + mu) * d := by nlinarith
  have hi' : (lam - |mu|) * |(i : ℝ)| ≤ n := by
    have : 0 ≤ (lam - |mu|) * (e : ℝ) * d := hpos
    nlinarith
  have hd' : (lam - |mu|) * |(d : ℝ)| ≤ n := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < d)]
    have h1 : (lam - |mu|) * d ≤ (lam - |mu|) * e * d := by nlinarith
    have : 0 ≤ lam * (i : ℝ) ^ 2 + mu * i := le_trans (by positivity) hi
    nlinarith
  have he' : (lam - |mu|) * |(e : ℝ)| ≤ n := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < e)]
    have h1 : (lam - |mu|) * e ≤ (lam - |mu|) * e * d := by nlinarith
    have : 0 ≤ lam * (i : ℝ) ^ 2 + mu * i := le_trans (by positivity) hi
    nlinarith
  have h1 := abs_le_ceil _ heps n i hi'
  have h2 := abs_le_ceil _ heps n d hd'
  have h3 := abs_le_ceil _ heps n e he'
  rw [abs_le] at h1
  rw [abs_of_pos hd] at h2
  rw [abs_of_pos he] at h3
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨h1, ⟨by omega, h2⟩, ⟨by omega, h3⟩⟩

private lemma Fc {F : ℤ → ℤ → ℤ → ℝ} {a a' b b' c c' : ℤ} (ha : a = a') (hb : b = b') (hc : c = c') :
    F a b c = F a' b' c' := by
  subst ha hb hc; rfl

/-! ### The part $2i + d - \delta > 0$ of $S$ vanishes -/

private lemma S1_zero (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) (hF : IsOddIn₁ F) :
    ∑ᶠ p ∈ liouvilleA lam mu n ∩ {p | 0 < 2 * p.1 + p.2.1 - p.2.2},
      F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) = 0 := by
  set s := liouvilleA lam mu n ∩ {p : ℤ × ℤ × ℤ | 0 < 2 * p.1 + p.2.1 - p.2.2} with hs
  have hfin : s.Finite := (finite_A lam mu h n).subset Set.inter_subset_left
  have hmaps : Set.MapsTo (fun p : ℤ × ℤ × ℤ => (p.2.2 - p.1, 2 * p.1 + p.2.1 - p.2.2, p.2.2)) s s := by
    rintro ⟨i, d, e⟩ ⟨⟨hd, he, hn⟩, ht⟩
    replace hd : 0 < d := hd
    replace he : 0 < e := he
    replace ht : 0 < 2 * i + d - e := ht
    have hn : (n : ℝ) = lam * (i : ℝ) ^ 2 + mu * i + (lam * e + mu) * d := hn
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show 0 < 2 * i + d - e; omega
    · show 0 < e; omega
    · show (n : ℝ) = lam * ((e - i : ℤ) : ℝ) ^ 2 + mu * ((e - i : ℤ) : ℝ) +
        (lam * ((e : ℤ) : ℝ) + mu) * ((2 * i + d - e : ℤ) : ℝ)
      push_cast
      linear_combination hn
    · show 0 < 2 * (e - i) + (2 * i + d - e) - e; omega
  have hbij : Set.BijOn (fun p : ℤ × ℤ × ℤ => (p.2.2 - p.1, 2 * p.1 + p.2.1 - p.2.2, p.2.2)) s s := by
    refine Set.InvOn.bijOn (f' := fun p : ℤ × ℤ × ℤ => (p.2.2 - p.1, 2 * p.1 + p.2.1 - p.2.2, p.2.2))
      ⟨?_, ?_⟩ hmaps hmaps
    · rintro ⟨i, d, e⟩ _
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
    · rintro ⟨i, d, e⟩ _
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
  have h1 : ∑ᶠ p ∈ s, F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
      ∑ᶠ p ∈ s, -F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) := by
    refine finsum_mem_eq_of_bijOn _ hbij ?_
    rintro ⟨i, d, e⟩ _
    have e1 : F (e - 2 * i) (d + i) (2 * d + 2 * i - e) =
        -F (2 * i - e) (d + i) (2 * d + 2 * i - e) := by
      rw [show 2 * i - e = -(e - 2 * i) by ring, hF, neg_neg]
    dsimp only
    rw [e1]
    congr 1
    exact Fc (by ring) (by ring) (by ring)
  rw [finsum_mem_neg_distrib _ hfin] at h1
  linarith

/-! ### The part $2i + d - \delta = 0$ of $S$ is part of $T$ -/

private lemma finsum_sigma_Icc {E : Set ℤ} (hE : E.Finite) (u : ℤ → ℤ) (g : ℤ → ℤ → ℝ) :
    ∑ᶠ s ∈ E, ∑ j ∈ Finset.Icc (1 : ℤ) (u s), g s j =
      ∑ᶠ q ∈ {q : ℤ × ℤ | q.1 ∈ E ∧ q.2 ∈ Finset.Icc (1 : ℤ) (u q.1)}, g q.1 q.2 := by
  classical
  set Xf : Finset (ℤ × ℤ) :=
    hE.toFinset.biUnion (fun s => (Finset.Icc 1 (u s)).image (fun j => (s, j))) with hXf
  have hX : {q : ℤ × ℤ | q.1 ∈ E ∧ q.2 ∈ Finset.Icc (1 : ℤ) (u q.1)} = (Xf : Set (ℤ × ℤ)) := by
    ext ⟨s, j⟩
    simp [hXf]; tauto
  rw [hX, finsum_mem_coe_finset, finsum_mem_eq_finite_toFinset_sum _ hE]
  rw [Finset.sum_finset_product Xf hE.toFinset (fun s => Finset.Icc 1 (u s))
    (by rintro ⟨s, j⟩; simp [hXf])]

private lemma S2_eq (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) :
    ∑ᶠ p ∈ liouvilleA lam mu n ∩ {p | 2 * p.1 + p.2.1 - p.2.2 = 0},
      F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) = liouvilleT₁ F lam mu n := by
  have hEfin : (liouvilleE lam mu n ∩ {s | 0 < s}).Finite :=
    (finite_E lam mu h n).subset Set.inter_subset_left
  unfold liouvilleT₁
  have h1 : ∑ᶠ s ∈ liouvilleE lam mu n ∩ {s | 0 < s}, liouvilleTTerm F s =
      ∑ᶠ s ∈ liouvilleE lam mu n ∩ {s | 0 < s}, ∑ j ∈ Finset.Icc (1 : ℤ) (2 * s - 1),
        F (2 * s - j) s (2 * s - j) := by
    refine finsum_mem_congr rfl ?_
    intro s hs
    have : 0 < s := hs.2
    unfold liouvilleTTerm
    rw [abs_of_pos this]
  rw [h1, finsum_sigma_Icc hEfin (fun s => 2 * s - 1) (fun s j => F (2 * s - j) s (2 * s - j))]
  refine finsum_mem_eq_of_bijOn (fun p : ℤ × ℤ × ℤ => (p.1 + p.2.1, p.2.2)) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun q : ℤ × ℤ => (q.2 - q.1, 2 * q.1 - q.2, q.2)) ⟨?_, ?_⟩ ?_ ?_
    · rintro ⟨i, d, e⟩ ⟨_, ht⟩
      replace ht : 2 * i + d - e = 0 := ht
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
    · rintro ⟨s, j⟩ _
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
    · rintro ⟨i, d, e⟩ ⟨⟨hd, he, hn⟩, ht⟩
      replace hd : 0 < d := hd
      replace he : 0 < e := he
      replace ht : 2 * i + d - e = 0 := ht
      have hn : (n : ℝ) = lam * (i : ℝ) ^ 2 + mu * i + (lam * e + mu) * d := hn
      have he' : (e : ℝ) = 2 * i + d := by exact_mod_cast (by omega : e = 2 * i + d)
      rw [he'] at hn
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show (n : ℝ) = lam * ((i + d : ℤ) : ℝ) ^ 2 + mu * ((i + d : ℤ) : ℝ)
        push_cast
        linear_combination hn
      · show 0 < i + d; omega
      · show e ∈ Finset.Icc 1 (2 * (i + d) - 1)
        rw [Finset.mem_Icc]; omega
    · rintro ⟨s, j⟩ ⟨⟨hs, hs0⟩, hj⟩
      have hs : (n : ℝ) = lam * (s : ℝ) ^ 2 + mu * s := hs
      replace hs0 : 0 < s := hs0
      have hj : j ∈ Finset.Icc 1 (2 * s - 1) := hj
      rw [Finset.mem_Icc] at hj
      obtain ⟨hj1, hj2⟩ := hj
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show 0 < 2 * s - j; omega
      · show 0 < j; omega
      · show (n : ℝ) = lam * ((j - s : ℤ) : ℝ) ^ 2 + mu * ((j - s : ℤ) : ℝ) +
          (lam * (j : ℝ) + mu) * ((2 * s - j : ℤ) : ℝ)
        push_cast
        linear_combination hs
      · show 2 * (j - s) + (2 * s - j) - j = 0; omega
  · rintro ⟨i, d, e⟩ ⟨_, ht⟩
    replace ht : 2 * i + d - e = 0 := ht
    dsimp only
    exact Fc (by omega) (by omega) (by omega)

/-! ### The part $2i + d - \delta < 0$ of $S$ is part of $W$ -/

private lemma S3_eq (lam mu : ℝ) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) :
    ∑ᶠ p ∈ liouvilleA lam mu n ∩ {p | 2 * p.1 + p.2.1 - p.2.2 < 0},
      F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2) =
    ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | 0 < p.2.2 - p.2.1 + 2 * p.1},
      F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) := by
  refine finsum_mem_eq_of_bijOn
    (fun p : ℤ × ℤ × ℤ => (p.2.1 + p.1, p.2.1, p.2.2 - p.2.1 - 2 * p.1)) ?_ ?_
  · refine Set.InvOn.bijOn
      (f' := fun q : ℤ × ℤ × ℤ => (q.1 - q.2.1, q.2.1, q.2.2 - q.2.1 + 2 * q.1)) ⟨?_, ?_⟩ ?_ ?_
    · rintro ⟨i, d, e⟩ _
      dsimp only
      simp only [Prod.mk.injEq, true_and]; omega
    · rintro ⟨h, a, b⟩ _
      dsimp only
      simp only [Prod.mk.injEq, true_and]; omega
    · rintro ⟨i, d, e⟩ ⟨⟨hd, he, hn⟩, ht⟩
      replace hd : 0 < d := hd
      replace he : 0 < e := he
      replace ht : 2 * i + d - e < 0 := ht
      have hn : (n : ℝ) = lam * (i : ℝ) ^ 2 + mu * i + (lam * e + mu) * d := hn
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show 0 < d; omega
      · show 0 < e - d - 2 * i; omega
      · show (n : ℝ) = lam * ((d + i : ℤ) : ℝ) ^ 2 + mu * ((d + i : ℤ) : ℝ) +
          lam * (d : ℝ) * ((e - d - 2 * i : ℤ) : ℝ)
        push_cast
        linear_combination hn
      · show 0 < (e - d - 2 * i) - d + 2 * (d + i); omega
    · rintro ⟨h, a, b⟩ ⟨⟨ha, hb, hn⟩, hc⟩
      replace ha : 0 < a := ha
      replace hb : 0 < b := hb
      replace hc : 0 < b - a + 2 * h := hc
      have hn : (n : ℝ) = lam * (h : ℝ) ^ 2 + mu * h + lam * a * b := hn
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show 0 < a; omega
      · show 0 < b - a + 2 * h; omega
      · show (n : ℝ) = lam * ((h - a : ℤ) : ℝ) ^ 2 + mu * ((h - a : ℤ) : ℝ) +
          (lam * ((b - a + 2 * h : ℤ) : ℝ) + mu) * (a : ℝ)
        push_cast
        linear_combination hn
      · show 2 * (h - a) + a - (b - a + 2 * h) < 0; omega
  · rintro ⟨i, d, e⟩ _
    dsimp only
    exact Fc (by omega) (by omega) (by omega)

/-! ### Passing from $S'$ to the part of $W$ with $\Delta' - \Delta + 2h < 0$ -/

private lemma Wneg (lam mu : ℝ) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) (ε : ℝ)
    (hε : ∀ x y z, F x (-y) (-z) = ε * F x y z) (hεε : ε * ε = 1) :
    ∑ᶠ p ∈ liouvilleC lam (-mu) n ∩ {p | 0 < p.2.2 - p.2.1 + 2 * p.1},
      F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) =
    ε * ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | p.2.2 - p.2.1 + 2 * p.1 < 0},
      F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) := by
  rw [mul_finsum_mem]
  refine finsum_mem_eq_of_bijOn (fun p : ℤ × ℤ × ℤ => (-p.1, p.2.2, p.2.1)) ?_ ?_
  · refine Set.InvOn.bijOn (f' := fun p : ℤ × ℤ × ℤ => (-p.1, p.2.2, p.2.1)) ⟨?_, ?_⟩ ?_ ?_
    · rintro ⟨h, a, b⟩ _
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
    · rintro ⟨h, a, b⟩ _
      dsimp only
      simp only [Prod.mk.injEq, and_true]; omega
    · rintro ⟨h, a, b⟩ ⟨⟨ha, hb, hn⟩, hc⟩
      replace ha : 0 < a := ha
      replace hb : 0 < b := hb
      replace hc : 0 < b - a + 2 * h := hc
      have hn : (n : ℝ) = lam * (h : ℝ) ^ 2 + (-mu) * h + lam * a * b := hn
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show 0 < b; omega
      · show 0 < a; omega
      · show (n : ℝ) = lam * ((-h : ℤ) : ℝ) ^ 2 + mu * ((-h : ℤ) : ℝ) + lam * (b : ℝ) * (a : ℝ)
        push_cast
        linear_combination hn
      · show a - b + 2 * (-h) < 0; omega
    · rintro ⟨h, a, b⟩ ⟨⟨ha, hb, hn⟩, hc⟩
      replace ha : 0 < a := ha
      replace hb : 0 < b := hb
      replace hc : b - a + 2 * h < 0 := hc
      have hn : (n : ℝ) = lam * (h : ℝ) ^ 2 + mu * h + lam * a * b := hn
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · show 0 < b; omega
      · show 0 < a; omega
      · show (n : ℝ) = lam * ((-h : ℤ) : ℝ) ^ 2 + (-mu) * ((-h : ℤ) : ℝ) + lam * (b : ℝ) * (a : ℝ)
        push_cast
        linear_combination hn
      · show 0 < a - b + 2 * (-h); omega
  · rintro ⟨h, a, b⟩ _
    dsimp only
    have : F (b + a) (-h) (b - a) = F (a + b) (-h) (-(a - b)) := Fc (by ring) rfl (by ring)
    rw [this, hε, ← mul_assoc, hεε, one_mul]

/-! ### $W = W_{>} + W_{<} + U$ -/

private lemma W_split (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) :
    liouvilleW F lam mu n =
      ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | 0 < p.2.2 - p.2.1 + 2 * p.1},
        F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) +
      ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | p.2.2 - p.2.1 + 2 * p.1 < 0},
        F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) + liouvilleU F lam mu n := by
  have hC := finite_C lam mu h n
  have hU : ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | p.2.2 - p.2.1 + 2 * p.1 = 0},
      F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) = liouvilleU F lam mu n := by
    refine finsum_mem_eq_of_bijOn (fun p : ℤ × ℤ × ℤ => (p.2.1, p.2.2)) ?_ ?_
    · refine Set.InvOn.bijOn (f' := fun q : ℤ × ℤ => ((q.1 - q.2) / 2, q.1, q.2)) ⟨?_, ?_⟩ ?_ ?_
      · rintro ⟨h, a, b⟩ ⟨_, hc⟩
        replace hc : b - a + 2 * h = 0 := hc
        dsimp only
        simp only [Prod.mk.injEq, and_true]; omega
      · rintro ⟨a, b⟩ _
        rfl
      · rintro ⟨h, a, b⟩ ⟨⟨ha, hb, hn⟩, hc⟩
        replace ha : 0 < a := ha
        replace hb : 0 < b := hb
        replace hc : b - a + 2 * h = 0 := hc
        have hn : (n : ℝ) = lam * (h : ℝ) ^ 2 + mu * h + lam * a * b := hn
        have hh : (h : ℝ) = ((a : ℝ) - b) / 2 := by
          have : (2 : ℝ) * h = (a : ℝ) - b := by exact_mod_cast (by omega : 2 * h = a - b)
          linarith
        rw [hh] at hn
        refine ⟨ha, hb, ?_, ?_⟩
        · show a ≡ b [ZMOD 2]
          unfold Int.ModEq; omega
        · show (n : ℝ) = lam * (((a + b : ℤ) : ℝ) / 2) ^ 2 + mu * (((a - b : ℤ) : ℝ) / 2)
          push_cast
          linear_combination hn
      · rintro ⟨a, b⟩ ⟨ha, hb, hab, hn⟩
        replace ha : 0 < a := ha
        replace hb : 0 < b := hb
        have hab : a ≡ b [ZMOD 2] := hab
        unfold Int.ModEq at hab
        have hn : (n : ℝ) = lam * (((a + b : ℤ) : ℝ) / 2) ^ 2 + mu * (((a - b : ℤ) : ℝ) / 2) := hn
        have hh : ((((a - b) / 2 : ℤ)) : ℝ) = ((a : ℝ) - b) / 2 := by
          have : (2 : ℝ) * (((a - b) / 2 : ℤ) : ℝ) = (a : ℝ) - b := by
            exact_mod_cast (by omega : 2 * ((a - b) / 2) = a - b)
          linarith
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · show 0 < a; exact ha
        · show 0 < b; exact hb
        · show (n : ℝ) = lam * ((((a - b) / 2 : ℤ)) : ℝ) ^ 2 + mu * ((((a - b) / 2 : ℤ)) : ℝ) +
            lam * (a : ℝ) * (b : ℝ)
          rw [hh]
          push_cast at hn
          linear_combination hn
        · show b - a + 2 * ((a - b) / 2) = 0; omega
    · rintro ⟨h, a, b⟩ ⟨_, hc⟩
      replace hc : b - a + 2 * h = 0 := hc
      dsimp only
      exact Fc rfl (by omega) rfl
  have e1 : liouvilleC lam mu n ∩ {p | ¬ (0 < p.2.2 - p.2.1 + 2 * p.1)} ∩
      {p | p.2.2 - p.2.1 + 2 * p.1 < 0} =
      liouvilleC lam mu n ∩ {p | p.2.2 - p.2.1 + 2 * p.1 < 0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, _⟩, h2⟩; exact ⟨hp, h2⟩
    · rintro ⟨hp, h2⟩; exact ⟨⟨hp, by omega⟩, h2⟩
  have e2 : liouvilleC lam mu n ∩ {p | ¬ (0 < p.2.2 - p.2.1 + 2 * p.1)} ∩
      {p | ¬ (p.2.2 - p.2.1 + 2 * p.1 < 0)} =
      liouvilleC lam mu n ∩ {p | p.2.2 - p.2.1 + 2 * p.1 = 0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, h1⟩, h2⟩; exact ⟨hp, by omega⟩
    · rintro ⟨hp, h2⟩; exact ⟨⟨hp, by omega⟩, by omega⟩
  unfold liouvilleW
  have h1 := split_pred hC (fun p : ℤ × ℤ × ℤ => 0 < p.2.2 - p.2.1 + 2 * p.1)
    (fun p => F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2))
  have h2 := split_pred (s := liouvilleC lam mu n ∩ {p | ¬ (0 < p.2.2 - p.2.1 + 2 * p.1)})
    (hC.subset Set.inter_subset_left)
    (fun p : ℤ × ℤ × ℤ => p.2.2 - p.2.1 + 2 * p.1 < 0)
    (fun p => F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2))
  rw [h1, h2, e1, e2, hU]
  ring

/-! ### $T = T_1(\mu) + T_1(-\mu)$ -/

private lemma T_split (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) :
    liouvilleT F lam mu n = liouvilleT₁ F lam mu n + liouvilleT₁ F lam (-mu) n := by
  have hE := finite_E lam mu h n
  have hz : ∑ᶠ s ∈ liouvilleE lam mu n ∩ {s | ¬ (0 < s)} ∩ {s | ¬ (s < 0)}, liouvilleTTerm F s = 0 := by
    refine finsum_mem_eq_zero_of_forall_eq_zero ?_
    rintro s ⟨⟨_, h1⟩, h2⟩
    have h1 : ¬ (0 < s) := h1
    have h2 : ¬ (s < 0) := h2
    have : s = 0 := by omega
    subst this
    simp [liouvilleTTerm]
  have hneg : ∑ᶠ s ∈ liouvilleE lam mu n ∩ {s | ¬ (0 < s)} ∩ {s | s < 0}, liouvilleTTerm F s =
      liouvilleT₁ F lam (-mu) n := by
    unfold liouvilleT₁
    refine finsum_mem_eq_of_bijOn (fun s : ℤ => -s) ?_ ?_
    · refine Set.InvOn.bijOn (f' := fun s : ℤ => -s) ⟨?_, ?_⟩ ?_ ?_
      · intro s _; simp
      · intro s _; simp
      · rintro s ⟨⟨hs, _⟩, h2⟩
        have hs : (n : ℝ) = lam * (s : ℝ) ^ 2 + mu * s := hs
        have h2 : s < 0 := h2
        refine ⟨?_, ?_⟩
        · show (n : ℝ) = lam * ((-s : ℤ) : ℝ) ^ 2 + (-mu) * ((-s : ℤ) : ℝ)
          push_cast
          linear_combination hs
        · show 0 < -s; omega
      · rintro s ⟨hs, h2⟩
        have hs : (n : ℝ) = lam * (s : ℝ) ^ 2 + (-mu) * s := hs
        have h2 : 0 < s := h2
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · show (n : ℝ) = lam * ((-s : ℤ) : ℝ) ^ 2 + mu * ((-s : ℤ) : ℝ)
          push_cast
          linear_combination hs
        · show ¬ (0 < -s); omega
        · show -s < 0; omega
    · intro s _
      simp [liouvilleTTerm, abs_neg]
  unfold liouvilleT
  have h1 := split_pred hE (fun s : ℤ => 0 < s) (fun s => liouvilleTTerm F s)
  have h2 := split_pred (s := liouvilleE lam mu n ∩ {s | ¬ (0 < s)})
    (hE.subset Set.inter_subset_left) (fun s : ℤ => s < 0) (fun s => liouvilleTTerm F s)
  rw [h1, h2, hz, hneg]
  unfold liouvilleT₁
  ring

/-! ### Assembly -/

private lemma S_decomp (lam mu : ℝ) (h : |mu| < lam) (n : ℕ) (F : ℤ → ℤ → ℤ → ℝ) (hF : IsOddIn₁ F) :
    liouvilleS F lam mu n = liouvilleT₁ F lam mu n +
      ∑ᶠ p ∈ liouvilleC lam mu n ∩ {p | 0 < p.2.2 - p.2.1 + 2 * p.1},
        F (p.2.1 + p.2.2) p.1 (p.2.1 - p.2.2) := by
  have hA := finite_A lam mu h n
  have e1 : liouvilleA lam mu n ∩ {p | ¬ (0 < 2 * p.1 + p.2.1 - p.2.2)} ∩
      {p | 2 * p.1 + p.2.1 - p.2.2 < 0} =
      liouvilleA lam mu n ∩ {p | 2 * p.1 + p.2.1 - p.2.2 < 0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, _⟩, h2⟩; exact ⟨hp, h2⟩
    · rintro ⟨hp, h2⟩; exact ⟨⟨hp, by omega⟩, h2⟩
  have e2 : liouvilleA lam mu n ∩ {p | ¬ (0 < 2 * p.1 + p.2.1 - p.2.2)} ∩
      {p | ¬ (2 * p.1 + p.2.1 - p.2.2 < 0)} =
      liouvilleA lam mu n ∩ {p | 2 * p.1 + p.2.1 - p.2.2 = 0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hp, h1⟩, h2⟩; exact ⟨hp, by omega⟩
    · rintro ⟨hp, h2⟩; exact ⟨⟨hp, by omega⟩, by omega⟩
  unfold liouvilleS
  have h1 := split_pred hA (fun p : ℤ × ℤ × ℤ => 0 < 2 * p.1 + p.2.1 - p.2.2)
    (fun p => F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2))
  have h2 := split_pred (s := liouvilleA lam mu n ∩ {p | ¬ (0 < 2 * p.1 + p.2.1 - p.2.2)})
    (hA.subset Set.inter_subset_left)
    (fun p : ℤ × ℤ × ℤ => 2 * p.1 + p.2.1 - p.2.2 < 0)
    (fun p => F (p.2.2 - 2 * p.1) (p.2.1 + p.1) (2 * p.2.1 + 2 * p.1 - p.2.2))
  rw [h1, h2, e1, e2, S1_zero lam mu h n F hF, S2_eq lam mu h n F, S3_eq]
  ring

/-- **Moreno–Wagstaff, Theorem 2.1** (First Fundamental Identity, Liouville; p. 15), proved: the book's argument
(§2.3, pp. 15–17). $S$ splits by the sign of $2i + d - \delta$; the part $> 0$ is $0$ by an involution and the
oddness of $F$ in $x$, the part $= 0$ is $T_1$, the part $< 0$ is the part of $W$ with $\Delta' - \Delta + 2h > 0$;
$S'$ is treated the same way and its $W$-part is turned into the part with $\Delta' - \Delta + 2h < 0$ by
$(h, \Delta, \Delta') \mapsto (-h, \Delta', \Delta)$ and evenness of $F$ in $(y, z)$; the part of $W$ with
$\Delta' - \Delta + 2h = 0$ is $U$. Finiteness of all partition sets follows from $\lambda > |\mu|$. -/
@[kb "morenowagstaff2005" "Theorem 2.1, p. 15"]
theorem theorem21 : Theorem21 := by
  intro lam mu h F hodd heven n _
  have h' : |-mu| < lam := by rwa [abs_neg]
  have hS := S_decomp lam mu h n F hodd
  have hS' := S_decomp lam (-mu) h' n F hodd
  have hW := Wneg lam mu n F 1 (fun x y z => by rw [heven x y z, one_mul]) (by norm_num)
  have hWs := W_split lam mu h n F
  have hT := T_split lam mu h n F
  rw [one_mul] at hW
  linarith

/-- **Moreno–Wagstaff, Theorem 2.2** (Second Fundamental Identity; p. 18), proved: as `theorem21`, with $F$ odd in
$(y, z)$ so that the $W$-part of $S'$ passes to the part of $W$ with $\Delta' - \Delta + 2h < 0$ with a sign. -/
@[kb "morenowagstaff2005" "Theorem 2.2, p. 18"]
theorem theorem22 : Theorem22 := by
  intro lam mu h F hodd hodd' n _
  have h' : |-mu| < lam := by rwa [abs_neg]
  have hS := S_decomp lam mu h n F hodd
  have hS' := S_decomp lam (-mu) h' n F hodd
  have hW := Wneg lam mu n F (-1) (fun x y z => by rw [hodd' x y z]; ring) (by norm_num)
  have hWs := W_split lam mu h n F
  linarith

end QuadFormsKB.MorenoWagstaff
