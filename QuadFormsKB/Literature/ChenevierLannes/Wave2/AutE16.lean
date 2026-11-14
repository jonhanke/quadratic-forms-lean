/-
# Chenevier–Lannes: $|O(E_{16})| \le 2^{15}\cdot 16!$ (the signed-permutation bound for $\Gamma_{16}$)

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.3.1, Variant, p. 58 ($O(E_{16}) \cong S_{16} \ltimes
(\{\pm1\}^{16})_0$). Printed page numbers. Indices are 0-based.

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^{16}$ with $Q = x_0^2 + \dots + x_{15}^2$ (`sumSqForm 16`), the lattice
$E_{16} = D_{16}^+$ (`omearaE 16`: all coordinates in $\mathbb Z$ or all in $\mathbb Z + \tfrac12$, even coordinate sum,
via `omeara106_11`), which is Cassels' $\Gamma_{16}$ (`casselsGamma_eq_omearaE`); the integral form `gamma16` has as
Hessian the Gram matrix of the basis `gamma16Basis`.

**Proves** (unconditional)
* `card_autLat_omearaE_sixteen_le`: $|O(E_{16})| \le 2^{15}\cdot 16!$ for the lattice automorphism group `autLat`;
* `e16Data`: the `EBasisData 16` of the basis `gamma16Basis` ($W = 2B$, $V = 2B^{-1}$, $G$ = `gamma16.hessian`);
* `card_aut_gamma16_le`: $|\mathrm{Aut}(\gamma_{16})| \le 2^{15}\cdot 16!$ (the bound for the integral form).

**Method** (adapted from `Sec106Rank13AutE12.lean`, O'Meara §106). An automorphism $\gamma$ is an orthogonal matrix
preserving $E_{16}$. The roots $e_a \pm e_b$ of $E_{16}$ are sent by $\gamma^{-1} = \gamma^{\mathsf T}$ to norm-$2$
vectors of $E_{16}$. These have integer coordinates (`omearaE_int_of_norm_two_sixteen`): for $n = 16$ the parity trick
of the $E_{12}$ case fails (half-integral vectors of $E_{16}$ have even norm), but a half-integral vector has every
$|v_i| \ge \tfrac12$, hence norm $\ge 16/4 = 4 > 2$. Hence each column of $\gamma$ has all entries in $\tfrac12\mathbb Z$
with pairwise integral differences and norm $1$, so it is $\pm$ a standard basis vector (`autLat_col16`); $\gamma$ is a
signed permutation matrix (`presE16_signed_perm`). Since $(\tfrac12, \dots, \tfrac12) \in E_{16}$, the sum of the signs
is divisible by $4$, which determines the last sign from the first fifteen. This gives an injection into
$S_{16} \times \{\pm1\}^{15}$. The bridge to `gamma16` uses `EBasisData.glImage_gl`, `card_aut_le_card_autLat`,
`ofMatrixZ_hessian` ($\mathrm{ofMatrixZ}(H_Q) = 2Q$) and `Binary.aut_smul` ($\mathrm{Aut}(2Q) = \mathrm{Aut}(Q)$).
(The bound is in fact an equality, `card_aut_gamma16`, proved in `Witt.lean` using the mass.)
-/
import QuadFormsKB.Literature.OMeara.Sec106Rank13Aut
import QuadFormsKB.Literature.OMeara.Sec106Rank13AutE12
import QuadFormsKB.Literature.Cassels.AppA.Gamma16
import QuadFormsKB.Literature.ChenevierLannes.EvenUnimodular
import QuadFormsKB.Binary.SiegelNonPrimitive

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Lattices QuadFormsKB.Siegel QuadFormsKB.LocalDensity

/-! ### Parity lemma for $E_{16}$ -/

/-- **Parity lemma for $E_{16}$.** A vector of $E_{16}$ with $\sum v_i^2 = 2$ has integer coordinates (a half-integral
vector of $E_{16}$ has all $|v_i| \ge \tfrac12$, hence norm $\ge 4$). -/
theorem omearaE_int_of_norm_two_sixteen {v : Fin 16 → ℚ} (hv : v ∈ omearaE 16)
    (hk : ∑ i, v i ^ 2 = 2) : ∀ i, ∃ m : ℤ, v i = m := by
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
    have hge : ∀ i, (1 / 4 : ℚ) ≤ v i ^ 2 := by
      intro i
      have h1 : 0 < m i ^ 2 := by
        have : m i ≠ 0 := by have := hodd i; omega
        positivity
      have h2 : (1 : ℚ) ≤ (m i : ℚ) ^ 2 := by exact_mod_cast h1
      have h3 : (m i : ℚ) ^ 2 = 4 * v i ^ 2 := by rw [← hm i]; ring
      linarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hge i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hk] at hsum
    norm_num at hsum

/-! ### Matrices preserving $E_{16}$ -/

/-- **Hypotheses on a matrix $M$** coming from $\gamma \in O(E_{16})$: orthogonal, and $M$ maps $E_{16}$ onto
$E_{16}$. -/
def PresE16 (M : Matrix (Fin 16) (Fin 16) ℚ) : Prop :=
  Mᵀ * M = 1 ∧ (∀ y ∈ omearaE 16, M *ᵥ y ∈ omearaE 16) ∧
    ∀ x ∈ omearaE 16, ∃ y ∈ omearaE 16, M *ᵥ y = x

/-- An automorphism of $E_{16}$ satisfies `PresE16`. -/
theorem presE16_of_autLat {γ : GL (Fin 16) ℚ} (hO : γ ∈ orthGroup (sumSqForm 16) ℚ)
    (hA : glImage γ (omearaE 16) = omearaE 16) : PresE16 γ.val := by
  refine ⟨orth_gram_sumSq hO, fun y hy => ?_, fun x hx => ?_⟩
  · rw [← hA]; exact mulVec_mem_glImage hy
  · rw [← hA] at hx
    obtain ⟨y, hy, rfl⟩ := (mem_glImage).mp hx
    exact ⟨y, hy, rfl⟩

/-- Integer vectors in $\mathbb Q^{16}$ with even coordinate sum lie in $E_{16}$. -/
theorem intVec_mem_E16 (z : Fin 16 → ℤ) (h : ∃ m : ℤ, ∑ i, z i = 2 * m) :
    (fun i => (z i : ℚ)) ∈ omearaE 16 := by
  obtain ⟨m, hm⟩ := h
  rw [omeara106_11 (by norm_num) (by norm_num)]
  refine ⟨fun i => ⟨2 * z i, by push_cast; ring⟩, fun i j => ⟨z i - z j, by push_cast; ring⟩, ⟨m, ?_⟩⟩
  have := congrArg (Int.cast : ℤ → ℚ) hm
  push_cast at this
  exact this

/-- For $\gamma^{-1}$ applied to an integer norm-$2$ vector of $E_{16}$ the result is integral:
$\sum_i M_{ij} z_i \in \mathbb Z$. -/
theorem presE16_entries_int {M : Matrix (Fin 16) (Fin 16) ℚ} (hP : PresE16 M) {z : Fin 16 → ℤ}
    (hz : ∃ m : ℤ, ∑ i, z i = 2 * m) (hz2 : ∑ i, (z i : ℚ) ^ 2 = 2) (j : Fin 16) :
    ∃ m : ℤ, ∑ i, M i j * z i = m := by
  obtain ⟨hM, -, hsurj⟩ := hP
  obtain ⟨y, hy, hMy⟩ := hsurj _ (intVec_mem_E16 z hz)
  have hy2 : ∑ i, y i ^ 2 = 2 := by
    rw [← sumSq_mulVec_eq hM y, hMy]; exact hz2
  obtain ⟨m, hm⟩ := omearaE_int_of_norm_two_sixteen hy hy2 j
  refine ⟨m, ?_⟩
  have hyj : y = Mᵀ *ᵥ (fun i => (z i : ℚ)) := by
    rw [← hMy, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  rw [← hm, hyj]
  simp [Matrix.mulVec, dotProduct]

/-- Sums and differences of two distinct entries of a column are integers. -/
theorem presE16_col_pm {M : Matrix (Fin 16) (Fin 16) ℚ} (hP : PresE16 M) (j a b : Fin 16) (hab : a ≠ b) :
    (∃ m : ℤ, M a j + M b j = m) ∧ ∃ m : ℤ, M a j - M b j = m := by
  have key : ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∃ m : ℤ, M a j + σ * M b j = m := by
    intro σ hσ
    let z : Fin 16 → ℤ := fun i => (if i = a then 1 else 0) + σ * (if i = b then 1 else 0)
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
    obtain ⟨m, hm⟩ := presE16_entries_int hP hz hz2 j
    refine ⟨m, ?_⟩
    rw [← hm]
    simp [z, mul_add, Finset.sum_add_distrib]
    ring
  obtain ⟨m1, h1⟩ := key 1 (Or.inl rfl)
  obtain ⟨m2, h2⟩ := key (-1) (Or.inr rfl)
  exact ⟨⟨m1, by simpa using h1⟩, ⟨m2, by simpa [sub_eq_add_neg] using h2⟩⟩

/-- **Columns.** Each column of $M$ is $\pm$ a standard basis vector. -/
theorem autLat_col16 {M : Matrix (Fin 16) (Fin 16) ℚ} (hP : PresE16 M) (j : Fin 16) :
    ∃ c : Fin 16, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ a, M a j = if a = c then (s : ℚ) else 0 := by
  have hnorm : ∑ a, M a j ^ 2 = 1 := by
    have := congrFun (congrFun hP.1 j) j
    simpa [Matrix.mul_apply, sq] using this
  have hdiff : ∀ a b, ∃ m : ℤ, M a j - M b j = m := by
    intro a b
    by_cases hab : a = b
    · exact ⟨0, by simp [hab]⟩
    · exact (presE16_col_pm hP j a b hab).2
  have hdbl : ∀ a, ∃ m : ℤ, 2 * M a j = m := by
    intro a
    have hne : a + 1 ≠ a := by revert a; decide
    obtain ⟨⟨m1, h1⟩, ⟨m2, h2⟩⟩ := presE16_col_pm hP j a (a + 1) (Ne.symm hne)
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

/-- **Signed permutation matrices of even sign parity.** If `PresE16 M`, then $M = (s_j\,\delta_{a,\sigma(j)})$ with
$s_j = \pm1$, $\sigma$ a permutation, and $\sum_j s_j \equiv 0 \pmod 4$. -/
theorem presE16_signed_perm {M : Matrix (Fin 16) (Fin 16) ℚ} (hP : PresE16 M) :
    ∃ σ : Equiv.Perm (Fin 16), ∃ s : Fin 16 → ℤ, (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ a j, M a j = if a = σ j then (s j : ℚ) else 0) ∧ ∃ m : ℤ, ∑ j, s j = 4 * m := by
  choose c s hs hc using autLat_col16 hP
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
  have hh : (fun _ : Fin 16 => (1 / 2 : ℚ)) ∈ omearaE 16 := by
    rw [omeara106_11 (by norm_num) (by norm_num)]
    exact ⟨fun i => ⟨1, by norm_num⟩, fun i j => ⟨0, by simp⟩, ⟨4, by simp [Finset.sum_const]; norm_num⟩⟩
  obtain ⟨-, -, m, hm⟩ := (omeara106_11 (by norm_num) (by norm_num) _).mp (hP.2.1 _ hh)
  refine ⟨m, ?_⟩
  have hcol : ∀ j, ∑ i, M i j = s j := by intro j; simp [hc j]
  have : ∑ i, (M *ᵥ fun _ : Fin 16 => (1 / 2 : ℚ)) i = (1 / 2) * ∑ j, (s j : ℚ) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum]
    ring
  rw [this] at hm
  have h4 : ∑ j, (s j : ℚ) = 4 * m := by linarith
  exact_mod_cast h4

/-- **$|O(E_{16})| \le 2^{15}\cdot 16!$** (Chenevier–Lannes, §3.3.1, Variant, p. 58: $O(E_{16}) \subseteq S_{16}
\ltimes (\{\pm1\}^{16})_0$): the automorphism group of $E_{16} = D_{16}^+$ is contained in the signed permutations of
$\{0, \dots, 15\}$ with an even number of minus signs, a set of size $16!\cdot 2^{15}$. Unconditional. -/
theorem card_autLat_omearaE_sixteen_le :
    Nat.card (autLat (sumSqForm 16) (omearaE 16)) ≤ 2 ^ 15 * Nat.factorial 16 := by
  have key : ∀ γ : autLat (sumSqForm 16) (omearaE 16), ∃ σ : Equiv.Perm (Fin 16), ∃ s : Fin 16 → ℤ,
      (∀ j, s j = 1 ∨ s j = -1) ∧
      (∀ a j, ((γ : orthGroup (sumSqForm 16) ℚ) : GL (Fin 16) ℚ).val a j =
        if a = σ j then (s j : ℚ) else 0) ∧ ∃ m : ℤ, ∑ j, s j = 4 * m := fun γ =>
    presE16_signed_perm (presE16_of_autLat γ.1.2 γ.2)
  choose σ s hs hM m hm using key
  let Φ : autLat (sumSqForm 16) (omearaE 16) → Equiv.Perm (Fin 16) × (Fin 15 → Bool) :=
    fun γ => (σ γ, fun j => decide (s γ j.castSucc = -1))
  have hΦ : Function.Injective Φ := by
    intro γ γ' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨hσ, hb⟩ := h
    have hlow : ∀ k : Fin 15, s γ k.castSucc = s γ' k.castSucc := by
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
      have := hs γ (Fin.last 15)
      have := hs γ' (Fin.last 15)
      omega
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    ext a j
    rw [hM γ a j, hM γ' a j, hσ, hall j]
  calc Nat.card (autLat (sumSqForm 16) (omearaE 16))
      ≤ Nat.card (Equiv.Perm (Fin 16) × (Fin 15 → Bool)) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 ^ 15 * Nat.factorial 16 := by
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_perm, Fintype.card_fun, Fintype.card_bool, mul_comm]

/-! ### The basis data of $\Gamma_{16}$ -/

/-- Twice the basis matrix of $\Gamma_{16}$ (`2 • gamma16Basis`): columns $2b_0 = 4e_0$, $2b_j = 2e_j - 2e_{j-1}$,
$2b_{15} = (1, \dots, 1)$. -/
def e16W : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of fun i j =>
  if j.val = 15 then 1
  else if j.val = 0 then (if i.val = 0 then 4 else 0)
  else if i = j then 2
  else if i.val + 1 = j.val then -2
  else 0

/-- Twice the inverse of the basis matrix of $\Gamma_{16}$: with $x = \sum_j c_jb_j$ one has $c_{15} = 2x_{15}$,
$c_i = \sum_{k=i}^{14}x_k - (15 - i)x_{15}$ for $1 \le i \le 14$, and
$c_0 = \tfrac12(\sum_{k=0}^{14}x_k - 15x_{15})$. -/
def e16V : Matrix (Fin 16) (Fin 16) ℤ := Matrix.of fun r c =>
  if r.val = 15 then (if c.val = 15 then 4 else 0)
  else if r.val = 0 then (if c.val = 15 then -15 else 1)
  else if c.val = 15 then -2 * (15 - (r.val : ℤ))
  else if r.val ≤ c.val then 2
  else 0

/-- `e16W * e16V = 4`. -/
theorem e16_hWV : e16W * e16V = (4 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  unfold e16W e16V; decide +kernel

/-- `e16V * e16W = 4`. -/
theorem e16_hVW : e16V * e16W = (4 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) := by
  unfold e16W e16V; decide +kernel

/-- `Wᵀ W = 4 G` with $G$ the Hessian of `gamma16`. -/
theorem e16_hgram : e16Wᵀ * e16W = (4 : ℤ) • Lattices.gamma16.hessian := by
  unfold e16W; decide +kernel

/-- Columns of $W$ have entries of one parity and sum divisible by $4$. -/
theorem e16_hcol : ∀ j, (∀ i i', (e16W i j - e16W i' j) % 2 = 0) ∧ (∑ i, e16W i j) % 4 = 0 := by
  unfold e16W; decide +kernel

/-- Rows of $V$ have entries of one parity and sum divisible by $4$. -/
theorem e16_hrow : ∀ r, (∀ i i', (e16V r i - e16V r i') % 2 = 0) ∧ (∑ i, e16V r i) % 4 = 0 := by
  unfold e16V; decide +kernel

/-- **The basis data of $\Gamma_{16} = E_{16}$** (`gamma16Basis`), with Gram matrix `gamma16.hessian`. -/
def e16Data : EBasisData 16 where
  W := e16W
  V := e16V
  G := Lattices.gamma16.hessian
  hWV := e16_hWV
  hVW := e16_hVW
  hgram := e16_hgram
  hcol := e16_hcol
  hrow := e16_hrow

/-- The Gram matrix of `e16Data` is the Hessian of `gamma16`. -/
theorem e16Data_G : e16Data.G = Lattices.gamma16.hessian := rfl

/-- **$|\mathrm{Aut}(E_{16})| \le 2^{15}\cdot 16!$** for the integral form `gamma16` (Cassels' $\Gamma_{16}$), i.e.
$O(E_{16}) \subseteq S_{16} \ltimes (\{\pm1\}^{16})_0$ (Chenevier–Lannes, §3.3.1, Variant, p. 58). Unconditional. -/
@[kb "chenevierlannes2019" "§3.3.1, Variant, p. 58 (O(E_16) ⊆ S_16 ⋉ ({±1}^16)_0)"]
theorem card_aut_gamma16_le : Nat.card (Aut Lattices.gamma16) ≤ 2 ^ 15 * Nat.factorial 16 := by
  have h1 : Nat.card (Aut (ofMatrixZ e16Data.G)) ≤ 2 ^ 15 * Nat.factorial 16 := by
    refine (card_aut_le_card_autLat e16Data.posDefGram_G.intPosDef e16Data.gl e16Data.gram_gl).trans ?_
    rw [e16Data.glImage_gl (by norm_num) (by norm_num)]
    exact card_autLat_omearaE_sixteen_le
  have h2 : ofMatrixZ e16Data.G = (2 : ℤ) • Lattices.gamma16 := ofMatrixZ_hessian Lattices.gamma16
  rw [h2, Binary.aut_smul (by norm_num)] at h1
  exact h1

end QuadFormsKB.ChenevierLannes
