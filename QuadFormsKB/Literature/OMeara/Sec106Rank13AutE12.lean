/-
# O'Meara §106: the automorphism group of $E_{12}$ is contained in the signed permutations of even sign parity

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^{12}$ with $Q = x_0^2 + \dots + x_{11}^2$ (`sumSqForm 12`), the lattice
$E_{12} = D_{12}^+$ (`omearaE 12`: vectors with all coordinates in $\mathbb Z$ or all in $\mathbb Z + \tfrac12$ and even
coordinate sum, via `omeara106_11`), automorphism group `autLat`. Indices are 0-based.

**Proves** (unconditional, no `sorry`)
* `card_autLat_omearaE_twelve_le`: $|O(E_{12})| \le 2^{11}\cdot 12!$.

**Method.** An automorphism $\gamma$ is an orthogonal matrix preserving $E_{12}$. The roots $e_a \pm e_b$ of $E_{12}$ are
sent by $\gamma^{-1} = \gamma^{\mathsf T}$ to norm-$2$ vectors of $E_{12}$, which have integer coordinates
(`omearaE_int_of_even_norm`: a half-integral vector of $E_{12}$ has norm $\equiv 12/4 \equiv 3 \pmod 2$ odd). Hence each
column of $\gamma$ has all entries in $\tfrac12\mathbb Z$ with pairwise integral differences and norm $1$, so it is
$\pm$ a standard basis vector (`autLat_col`); $\gamma$ is a signed permutation matrix (`presE_signed_perm`). Since
$(\tfrac12, \dots, \tfrac12) \in E_{12}$, the sum of the signs is divisible by $4$, which determines the last sign from
the first eleven. This gives an injection into $S_{12} \times \{\pm1\}^{11}$.
(The bound is in fact an equality, $|O(E_{12})| = 2^{11} \cdot 12!$, but only the upper bound is proved here.)
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank9

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- An odd integer has square $\equiv 1 \pmod 8$. -/
theorem odd_sq_eq {m : ℤ} (h : m % 2 = 1) : ∃ q : ℤ, m ^ 2 = 8 * q + 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self t
  refine ⟨r, ?_⟩
  have : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
  rw [this, hr]; ring

/-- **Parity lemma.** A vector of $E_{12}$ whose norm $\sum v_i^2$ is an even integer has integer coordinates. -/
theorem omearaE_int_of_even_norm {v : Fin 12 → ℚ} (hv : v ∈ omearaE 12) {k : ℤ}
    (hk : ∑ i, v i ^ 2 = 2 * k) : ∀ i, ∃ m : ℤ, v i = m := by
  obtain ⟨h2, hd, -⟩ := (omeara106_11 (by norm_num) (by norm_num) v).mp hv
  by_cases h0 : ∃ m : ℤ, v 0 = m
  · obtain ⟨m0, hm0⟩ := h0
    intro i
    obtain ⟨n, hn⟩ := hd i 0
    exact ⟨n + m0, by push_cast; linarith⟩
  · exfalso
    choose m hm using h2
    have hodd : ∀ i, m i % 2 = 1 := by
      intro i
      by_contra hne
      obtain ⟨r, hr⟩ : ∃ r, m i = 2 * r := ⟨m i / 2, by omega⟩
      obtain ⟨n, hn⟩ := hd i 0
      apply h0
      refine ⟨r - n, ?_⟩
      have h := hm i
      rw [hr] at h
      push_cast at h ⊢
      linarith
    choose q hq using fun i => odd_sq_eq (hodd i)
    have h1 : ∑ i, ((m i : ℚ)) ^ 2 = 8 * k := by
      have : ∀ i, (m i : ℚ) ^ 2 = 4 * v i ^ 2 := by intro i; rw [← hm i]; ring
      simp only [this, ← Finset.mul_sum, hk]; ring
    have h2 : ∑ i, (m i) ^ 2 = 8 * k := by exact_mod_cast h1
    have h3 : ∑ i, (m i) ^ 2 = ∑ i, (8 * q i + 1) := Finset.sum_congr rfl fun i _ => hq i
    rw [h3, Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    simp at h2
    omega

/-- An isometry of $I_n$ over $\mathbb Q$ has $\gamma^{\mathsf T}\gamma = 1$. -/
theorem orth_gram_sumSq {n : ℕ} {γ : GL (Fin n) ℚ} (h : γ ∈ orthGroup (sumSqForm n) ℚ) :
    γ.valᵀ * γ.val = 1 := by
  have hm : (sumSqForm n).hessian.map (algebraMap ℚ ℚ) = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    have e : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
      · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]
    rw [e]; ext i j; simp [Matrix.one_apply]
  rw [mem_orthGroup, hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at h
  exact smul_right_injective _ (two_ne_zero : (2 : ℚ) ≠ 0) (by simpa using h)

/-- An orthogonal matrix preserves $\sum x_i^2$. -/
theorem sumSq_mulVec_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) ℚ} (hM : Mᵀ * M = 1) (y : Fin n → ℚ) :
    ∑ i, (M *ᵥ y) i ^ 2 = ∑ i, y i ^ 2 := by
  have h : (M *ᵥ y) ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  simpa [dotProduct, sq] using h

/-- **Hypotheses on a matrix $M$** coming from $\gamma \in O(E_{12})$: orthogonal, and $M$ maps $E_{12}$ onto $E_{12}$. -/
def PresE (M : Matrix (Fin 12) (Fin 12) ℚ) : Prop :=
  Mᵀ * M = 1 ∧ (∀ y ∈ omearaE 12, M *ᵥ y ∈ omearaE 12) ∧
    ∀ x ∈ omearaE 12, ∃ y ∈ omearaE 12, M *ᵥ y = x

/-- An automorphism of $E_{12}$ satisfies `PresE`. -/
theorem presE_of_autLat {γ : GL (Fin 12) ℚ} (hO : γ ∈ orthGroup (sumSqForm 12) ℚ)
    (hA : glImage γ (omearaE 12) = omearaE 12) : PresE γ.val := by
  refine ⟨orth_gram_sumSq hO, fun y hy => ?_, fun x hx => ?_⟩
  · rw [← hA]; exact mulVec_mem_glImage hy
  · rw [← hA] at hx
    obtain ⟨y, hy, rfl⟩ := (mem_glImage).mp hx
    exact ⟨y, hy, rfl⟩

/-- Integer vectors with even coordinate sum lie in $E_{12}$. -/
theorem intVec_mem_E (z : Fin 12 → ℤ) (h : ∃ m : ℤ, ∑ i, z i = 2 * m) :
    (fun i => (z i : ℚ)) ∈ omearaE 12 := by
  obtain ⟨m, hm⟩ := h
  rw [omeara106_11 (by norm_num) (by norm_num)]
  refine ⟨fun i => ⟨2 * z i, by push_cast; ring⟩, fun i j => ⟨z i - z j, by push_cast; ring⟩, ⟨m, ?_⟩⟩
  have := congrArg (Int.cast : ℤ → ℚ) hm
  push_cast at this
  exact this

/-- For $\gamma^{-1}$ applied to an integer norm-$2$ vector of $E_{12}$ the result is integral:
$\sum_i M_{ij} z_i \in \mathbb Z$. -/
theorem presE_entries_int {M : Matrix (Fin 12) (Fin 12) ℚ} (hP : PresE M) {z : Fin 12 → ℤ}
    (hz : ∃ m : ℤ, ∑ i, z i = 2 * m) (hz2 : ∑ i, (z i : ℚ) ^ 2 = 2) (j : Fin 12) :
    ∃ m : ℤ, ∑ i, M i j * z i = m := by
  obtain ⟨hM, -, hsurj⟩ := hP
  obtain ⟨y, hy, hMy⟩ := hsurj _ (intVec_mem_E z hz)
  have hy2 : ∑ i, y i ^ 2 = 2 * 1 := by
    rw [← sumSq_mulVec_eq hM y, hMy]; simpa using hz2
  obtain ⟨m, hm⟩ := omearaE_int_of_even_norm hy hy2 j
  refine ⟨m, ?_⟩
  have hyj : y = Mᵀ *ᵥ (fun i => (z i : ℚ)) := by
    rw [← hMy, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  rw [← hm, hyj]
  simp [Matrix.mulVec, dotProduct]

/-- Sums and differences of two distinct entries of a column are integers. -/
theorem presE_col_pm {M : Matrix (Fin 12) (Fin 12) ℚ} (hP : PresE M) (j a b : Fin 12) (hab : a ≠ b) :
    (∃ m : ℤ, M a j + M b j = m) ∧ ∃ m : ℤ, M a j - M b j = m := by
  have key : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∃ m : ℤ, M a j + σ * M b j = m := by
    intro σ hσ
    let z : Fin 12 → ℤ := fun i => (if i = a then 1 else 0) + σ * (if i = b then 1 else 0)
    have hz : ∃ m : ℤ, ∑ i, z i = 2 * m := by
      have : ∑ i, z i = 1 + σ := by
        simp [z, Finset.sum_add_distrib, ← Finset.mul_sum]
      rcases hσ with rfl | rfl
      · exact ⟨1, by rw [this]; norm_num⟩
      · exact ⟨0, by rw [this]; norm_num⟩
    have hz2 : ∑ i, (z i : ℚ) ^ 2 = 2 := by
      have : ∀ i, (z i : ℚ) ^ 2 = (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
        intro i
        have hba : b ≠ a := Ne.symm hab
        by_cases h1 : i = a
        · subst h1
          rcases hσ with rfl | rfl <;> simp [z, hab, hba]
        · by_cases h2 : i = b
          · subst h2
            rcases hσ with rfl | rfl <;> simp [z, hab, hba]
          · simp [z, h1, h2]
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      norm_num
    obtain ⟨m, hm⟩ := presE_entries_int hP hz hz2 j
    refine ⟨m, ?_⟩
    rw [← hm]
    simp [z, mul_add, Finset.sum_add_distrib]
    ring
  obtain ⟨m1, h1⟩ := key 1 (Or.inl rfl)
  obtain ⟨m2, h2⟩ := key (-1) (Or.inr rfl)
  exact ⟨⟨m1, by simpa using h1⟩, ⟨m2, by simpa [sub_eq_add_neg] using h2⟩⟩

/-- **Columns.** Each column of $M$ is $\pm$ a standard basis vector. -/
theorem autLat_col {M : Matrix (Fin 12) (Fin 12) ℚ} (hP : PresE M) (j : Fin 12) :
    ∃ c : Fin 12, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ a, M a j = if a = c then (s : ℚ) else 0 := by
  have hnorm : ∑ a, M a j ^ 2 = 1 := by
    have := congrFun (congrFun hP.1 j) j
    simpa [Matrix.mul_apply, sq] using this
  have hdiff : ∀ a b, ∃ m : ℤ, M a j - M b j = m := by
    intro a b
    by_cases hab : a = b
    · exact ⟨0, by simp [hab]⟩
    · exact (presE_col_pm hP j a b hab).2
  have hdbl : ∀ a, ∃ m : ℤ, 2 * M a j = m := by
    intro a
    have hne : a + 1 ≠ a := by revert a; decide
    obtain ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩ := presE_col_pm hP j a (a + 1) (Ne.symm hne)
    exact ⟨m1 + m2, by push_cast; linarith⟩
  by_cases hint : ∃ m : ℤ, M 0 j = m
  · obtain ⟨m0, hm0⟩ := hint
    have hall : ∀ a, ∃ m : ℤ, M a j = m := by
      intro a
      obtain ⟨n, hn⟩ := hdiff a 0
      exact ⟨n + m0, by push_cast; linarith⟩
    choose z hz using hall
    have hz1 : ∑ a, z a ^ 2 = 1 := by
      have : ∑ a, ((z a : ℚ)) ^ 2 = 1 := by simpa [hz] using hnorm
      exact_mod_cast this
    have hex : ∃ c, z c ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      simp [hcon] at hz1
    obtain ⟨c, hc⟩ := hex
    have hle : ∀ a, z a ^ 2 ≤ 1 := by
      intro a
      rw [← hz1]
      exact Finset.single_le_sum (f := fun a => z a ^ 2) (fun a _ => sq_nonneg _) (Finset.mem_univ a)
    have hc1 : z c ^ 2 = 1 := by
      have := hle c
      have : 0 < z c ^ 2 := by positivity
      omega
    have hs : z c = 1 ∨ z c = -1 := by
      have := hle c
      have h1 : z c ≤ 1 := by nlinarith
      have h2 : -1 ≤ z c := by nlinarith
      omega
    refine ⟨c, z c, hs, fun a => ?_⟩
    by_cases hac : a = c
    · subst hac; simp [hz]
    · have hpair : z a ^ 2 + z c ^ 2 ≤ 1 := by
        rw [← hz1, ← Finset.sum_pair hac (f := fun a => z a ^ 2)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
      have : z a = 0 := by
        have : z a ^ 2 ≤ 0 := by omega
        exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
      simp [hz, hac, this]
  · exfalso
    choose m hm using hdbl
    have hm0 : ∀ a, m a ≠ 0 := by
      intro a h0
      apply hint
      obtain ⟨n, hn⟩ := hdiff 0 a
      refine ⟨n, ?_⟩
      have := hm a
      rw [h0] at this
      push_cast at this
      linarith
    have hge : ∀ a, (1 / 4 : ℚ) ≤ M a j ^ 2 := by
      intro a
      have h1 : 0 < m a ^ 2 := by have := hm0 a; positivity
      have h2 : (1 : ℚ) ≤ (m a : ℚ) ^ 2 := by exact_mod_cast h1
      have h3 : (m a : ℚ) ^ 2 = 4 * M a j ^ 2 := by rw [← hm a]; ring
      linarith
    have := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hge a)
    simp at this
    linarith

/-- **Signed permutation matrices of even sign parity.** If `PresE M`, then $M = (s_j\,\delta_{a,\sigma(j)})$ with
$s_j = \pm1$, $\sigma$ a permutation, and $\sum_j s_j \equiv 0 \pmod 4$. -/
theorem presE_signed_perm {M : Matrix (Fin 12) (Fin 12) ℚ} (hP : PresE M) :
    ∃ σ : Equiv.Perm (Fin 12), ∃ s : Fin 12 → ℤ, (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ a j, M a j = if a = σ j then (s j : ℚ) else 0) ∧ ∃ m : ℤ, ∑ j, s j = 4 * m := by
  choose c s hs hc using autLat_col hP
  have hinj : Function.Injective c := by
    intro j j' hjj
    by_contra hne
    have h0 : ∑ a, M a j * M a j' = 0 := by
      have := congrFun (congrFun hP.1 j) j'
      simpa [Matrix.mul_apply, hne] using this
    have h1 : ∑ a, M a j * M a j' = (s j : ℚ) * s j' := by
      have : ∀ a, M a j * M a j' = if a = c j' then (s j : ℚ) * s j' else 0 := by
        intro a
        rw [hc j a, hc j' a, hjj]
        by_cases h : a = c j' <;> simp [h]
      simp [this]
    have h2 : (s j : ℚ) * s j' = 0 := by rw [← h1, h0]
    rcases hs j with h | h <;> rcases hs j' with h' | h' <;> simp [h, h'] at h2
  refine ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), s, hs,
    fun a j => by simpa using hc j a, ?_⟩
  have hh : (fun _ : Fin 12 => (1 / 2 : ℚ)) ∈ omearaE 12 := by
    rw [omeara106_11 (by norm_num) (by norm_num)]
    exact ⟨fun i => ⟨1, by norm_num⟩, fun i j => ⟨0, by simp⟩, ⟨3, by simp [Finset.sum_const]; norm_num⟩⟩
  obtain ⟨-, -, m, hm⟩ := (omeara106_11 (by norm_num) (by norm_num) _).mp (hP.2.1 _ hh)
  refine ⟨m, ?_⟩
  have hcol : ∀ j, ∑ i, M i j = s j := by intro j; simp [hc j]
  have : ∑ i, (M *ᵥ fun _ : Fin 12 => (1 / 2 : ℚ)) i = (1 / 2) * ∑ j, (s j : ℚ) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum]
    ring
  rw [this] at hm
  have h4 : ∑ j, (s j : ℚ) = 4 * m := by linarith
  exact_mod_cast h4

/-- **|O(E₁₂)| ≤ 2¹¹·12!** (cf. O'Meara §106E, the lattice $E_{12} = D_{12}^+$ of 106.r38, $n = 12$): the
automorphism group of $E_{12}$ is contained in the signed permutations of $\{0, \dots, 11\}$ with an even number of
minus signs, a set of size $12!\cdot 2^{11}$. (In fact $|O(E_{12})| = 2^{11} \cdot 12!$, but only the upper bound is
proved here.) Unconditional. -/
theorem card_autLat_omearaE_twelve_le :
    Nat.card (autLat (sumSqForm 12) (omearaE 12)) ≤ 2 ^ 11 * Nat.factorial 12 := by
  have key : ∀ γ : autLat (sumSqForm 12) (omearaE 12), ∃ σ : Equiv.Perm (Fin 12), ∃ s : Fin 12 → ℤ,
      (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ a j, ((γ : orthGroup (sumSqForm 12) ℚ) : GL (Fin 12) ℚ).val a j =
        if a = σ j then (s j : ℚ) else 0) ∧ ∃ m : ℤ, ∑ j, s j = 4 * m := fun γ =>
    presE_signed_perm (presE_of_autLat γ.1.2 γ.2)
  choose σ s hs hM m hm using key
  let Φ : autLat (sumSqForm 12) (omearaE 12) → Equiv.Perm (Fin 12) × (Fin 11 → Bool) :=
    fun γ => (σ γ, fun j => decide (s γ j.castSucc = -1))
  have hΦ : Function.Injective Φ := by
    intro γ γ' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨hσ, hb⟩ := h
    have hlow : ∀ k : Fin 11, s γ k.castSucc = s γ' k.castSucc := by
      intro k
      have := congrFun hb k
      simp only [decide_eq_decide] at this
      rcases hs γ k.castSucc with h1 | h1 <;> rcases hs γ' k.castSucc with h2 | h2 <;>
        simp_all
    have hall : ∀ j, s γ j = s γ' j := by
      intro j
      refine Fin.lastCases ?_ (fun k => hlow k) j
      have e1 := hm γ
      have e2 := hm γ'
      rw [Fin.sum_univ_castSucc] at e1 e2
      simp only [hlow] at e1
      have := hs γ (Fin.last 11)
      have := hs γ' (Fin.last 11)
      omega
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    ext a j
    rw [hM γ a j, hM γ' a j, hσ, hall j]
  calc Nat.card (autLat (sumSqForm 12) (omearaE 12))
      ≤ Nat.card (Equiv.Perm (Fin 12) × (Fin 11 → Bool)) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 ^ 11 * Nat.factorial 12 := by
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_perm, Fintype.card_fun, Fintype.card_bool, mul_comm]

end QuadFormsKB.Lattices
