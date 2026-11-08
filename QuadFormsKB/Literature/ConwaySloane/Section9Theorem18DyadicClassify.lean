/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ for every lattice

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18 ("based on Theorem 81 of [Wat3]"), the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicLevel.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$). Indices are $0$-based.

**The classification.** Rescale $L_2$ by a power of $2$ so that $Q$ is integral on it (this changes neither the
automorphisms nor the root group, `theorem18OnlyIf_congr`), and take a $2$-adic Jordan basis (`exists_dyadic_basis`,
O'Meara 93:15): $G$ is block diagonal with $1 \times 1$ blocks (the *single* indices) and $2 \times 2$ blocks
$\{i, i'\}$ with $\lvert G_{ii}\rvert, \lvert G_{i'i'}\rvert \le \lvert 2G_{ii'}\rvert$ (the *paired* indices, even
constituents). Write $e_i$ for the order of $G_{ii'}$ (paired) or of $G_{ii}$ (single). Then (`theorem18OnlyIf_of_jordan`):
* no paired index: $L_2$ has an orthogonal basis, `theorem18OnlyIf_of_diag`;
* two paired indices with $e$ of different parity, a single index with $e$ of the parity of a paired one, three
  single indices with the same $e$, or two single indices $k, l$ with the same $e$ and $u_k + u_l \equiv 2 \pmod 4$:
  the root group is everything (`rootGroup_eq_top_of_binary_binary`, `rootGroup_eq_top_of_binary_single`,
  `rootGroup_eq_top_of_three`, `rootGroup_eq_top_of_sum`), so Theorem 18 holds trivially;
* otherwise the basis has the level shape (`LevelShape`, with $p$ the parity of the paired exponents and
  $\lambda_i = \lfloor (e_i - p)/2\rfloor$), and `theorem18OnlyIf_of_levelShape` applies.

**Proves**
* `theorem18OnlyIf_of_jordan` (Theorem 18, "only if", for a basis of Jordan type; the inverse Gram matrix $N$ of the
  level shape is written down blockwise);
* **`theorem18OnlyIf_dyadic`** (Theorem 18, "only if", at $p = 2$ for **every** regular
  form and lattice; unconditional);
* **`theorem18DyadicResidual11_holds`**: the named statement `Theorem18DyadicResidual11` (the last open case) is a theorem;
* **`theorem18Statement_holds`**: Conway–Sloane's Theorem 18 (`Theorem18Statement`, every prime, both directions),
  unconditional.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicLevel
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicResidual11
import QuadFormsKB.Literature.ConwaySloane.Section9DyadicOdd

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices Wall Levels EvenUnimodular

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section Classify

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ

set_option hygiene false in
local notation "𝐆" => locGram Q v γ

/-- **Theorem 18, "only if", for a basis of Jordan type** (see the module docstring): if every row of
$G$ = `locGram Q v γ` has at most one nonzero off-diagonal entry (`hB1`), and a nonzero off-diagonal entry $G_{ij}$
dominates the diagonal, $\lvert G_{ii}\rvert \le \lvert 2G_{ij}\rvert$ (`hB2`), then Theorem 18 ("only if") holds
for $L$ at the prime over $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': every 2-adic Jordan basis)"]
theorem theorem18OnlyIf_of_jordan (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v))
    (hB1 : ∀ i j j', j ≠ i → j' ≠ i → locGram Q v γ i j ≠ 0 → locGram Q v γ i j' ≠ 0 → j = j')
    (hB2 : ∀ i j, i ≠ j → locGram Q v γ i j ≠ 0 →
      Valued.v (locGram Q v γ i i) ≤ Valued.v (2 * locGram Q v γ i j)) :
    Theorem18OnlyIf Q L v hQ := by
  classical
  have hsym : ∀ i j, 𝐆 j i = 𝐆 i j := fun i j => locGram_symm' γ j i
  have hv2 := valued_two_eq (v := v) h2
  -- the partner of an index
  set HasP : Fin n → Prop := fun i => ∃ j, j ≠ i ∧ 𝐆 i j ≠ 0 with hHasP
  set partner : Fin n → Fin n := fun i => if h : HasP i then h.choose else i with hpartner
  set Sg : Finset (Fin n) := Finset.univ.filter fun i => ¬ HasP i with hSg
  have hmemSg : ∀ i, i ∈ Sg ↔ ¬ HasP i := fun i => by simp [hSg]
  have hp_ne : ∀ i, i ∉ Sg → partner i ≠ i ∧ 𝐆 i (partner i) ≠ 0 := by
    intro i hi
    have h : HasP i := by rw [hmemSg] at hi; push_neg at hi; exact hi
    simp only [hpartner, dif_pos h]
    exact h.choose_spec
  have hp_eq : ∀ i, i ∈ Sg → partner i = i := by
    intro i hi
    have h : ¬ HasP i := (hmemSg i).mp hi
    simp only [hpartner, dif_neg h]
  have hzero : ∀ i j, j ≠ i → j ≠ partner i → 𝐆 i j = 0 := by
    intro i j hji hjp
    by_contra hne
    by_cases hi : i ∈ Sg
    · exact (hmemSg i).mp hi ⟨j, hji, hne⟩
    · exact hjp (hB1 i j (partner i) hji (hp_ne i hi).1 hne (hp_ne i hi).2)
  have hpp : ∀ i, i ∉ Sg → partner i ∉ Sg ∧ partner (partner i) = i := by
    intro i hi
    obtain ⟨h1, h2'⟩ := hp_ne i hi
    have hP : partner i ∉ Sg := by
      rw [hmemSg]; push_neg; exact ⟨i, Ne.symm h1, by rw [hsym]; exact h2'⟩
    refine ⟨hP, ?_⟩
    by_contra hne
    exact h2' (by rw [← hsym]; exact hzero (partner i) i (Ne.symm h1) (Ne.symm hne))
  have hGne : ∀ i, 𝐆 i (partner i) ≠ 0 := by
    intro i
    by_cases hi : i ∈ Sg
    · rw [hp_eq i hi]
      refine locGram_diag_ne_zero hQ γ fun m hm => ?_
      rw [hsym]; exact hzero i m hm (by rw [hp_eq i hi]; exact hm)
    · exact (hp_ne i hi).2
  -- the scale exponents
  set E : Fin n → ℤ := fun i => -log (Valued.v (𝐆 i (partner i))) with hE
  have hvE : ∀ i, Valued.v (𝐆 i (partner i)) = exp (-(E i)) := by
    intro i
    simp only [hE, neg_neg]
    exact (exp_log ((Valuation.ne_zero_iff _).mpr (hGne i))).symm
  have hEp : ∀ i, E (partner i) = E i := by
    intro i
    by_cases hi : i ∈ Sg
    · rw [hp_eq i hi]
    · simp only [hE, (hpp i hi).2, hsym]
  have hdiagP : ∀ i, i ∉ Sg → Valued.v (𝐆 i i) ≤ exp (-(E i + 1)) := by
    intro i hi
    have := hB2 i (partner i) (Ne.symm (hp_ne i hi).1) (hp_ne i hi).2
    rwa [map_mul, hv2, hvE, ← exp_add, show -1 + -E i = -(E i + 1) by ring] at this
  have hdiagS : ∀ i, i ∈ Sg → Valued.v (𝐆 i i) = exp (-(E i)) := by
    intro i hi; have := hvE i; rwa [hp_eq i hi] at this
  -- case: no paired index
  by_cases hall : ∀ i, i ∈ Sg
  · exact theorem18OnlyIf_of_diag hQ h2 γ hγ fun i j hij =>
      hzero i j (Ne.symm hij) (by rw [hp_eq i (hall i)]; exact Ne.symm hij)
  push_neg at hall
  obtain ⟨i0, hi0⟩ := hall
  set j0 := partner i0 with hj0
  obtain ⟨hj0i0, hG0⟩ := hp_ne i0 hi0
  obtain ⟨hj0S, hj0p⟩ := hpp i0 hi0
  have horth : ∀ m, m ≠ i0 → m ≠ j0 → 𝐆 m i0 = 0 ∧ 𝐆 m j0 = 0 := by
    intro m hm1 hm2
    refine ⟨by rw [hsym]; exact hzero i0 m hm1 hm2, ?_⟩
    rw [hsym]; exact hzero j0 m hm2 (by rw [hj0p]; exact hm1)
  have hi : Valued.v (𝐆 i0 i0) ≤ Valued.v (2 * 𝐆 i0 j0) := hB2 i0 j0 (Ne.symm hj0i0) hG0
  have hj : Valued.v (𝐆 j0 j0) ≤ Valued.v (2 * 𝐆 i0 j0) := by
    have := hB2 j0 i0 hj0i0 (by rw [hsym]; exact hG0)
    rwa [hsym i0 j0] at this
  have hunits := units_le_rootGroup_of_binary h2 γ hγ (Ne.symm hj0i0) horth hG0 hi hj
  set p := E i0 with hp
  -- case (a): paired exponents of both parities
  by_cases ha : ∃ a, a ∉ Sg ∧ (E a - p) % 2 = 1
  · obtain ⟨a, haS, hapar⟩ := ha
    set a' := partner a
    obtain ⟨ha'a, hGa⟩ := hp_ne a haS
    obtain ⟨ha'S, ha'p⟩ := hpp a haS
    refine theorem18OnlyIf_of_eq_top hQ (rootGroup_eq_top_of_binary_binary h2 γ hγ (Ne.symm hj0i0)
      (Ne.symm ha'a) horth hG0 hi hj (k := a) (l := a') ?_ hGa (hB2 a a' (Ne.symm ha'a) hGa) ?_
      ((-(p + E a) - 1) / 2) ?_)
    · intro m hm1 hm2
      refine ⟨by rw [hsym]; exact hzero a m hm1 hm2, ?_⟩
      rw [hsym]; exact hzero a' m hm2 (by rw [ha'p]; exact hm1)
    · have := hB2 a' a ha'a (by rw [hsym]; exact hGa)
      rwa [hsym a a'] at this
    · rw [map_mul, hvE i0, hvE a, ← exp_add]
      congr 1; omega
  push_neg at ha
  -- case (b): a single index with the parity of the paired ones
  by_cases hb : ∃ k, k ∈ Sg ∧ (E k - p) % 2 = 0
  · obtain ⟨k, hkS, hkpar⟩ := hb
    refine theorem18OnlyIf_of_eq_top hQ (rootGroup_eq_top_of_binary_single h2 γ hγ (Ne.symm hj0i0) horth hG0
      hi hj (k := k) (fun m hm => by rw [hsym]; exact hzero k m hm (by rw [hp_eq k hkS]; exact hm))
      ((-(p + E k)) / 2) ?_)
    rw [map_mul, map_div₀, hvE i0, hdiagS k hkS, hv2, div_eq_mul_inv, ← WithZero.exp_neg, ← exp_add, ← exp_add]
    congr 1; omega
  push_neg at hb
  -- case (c): three single indices with the same exponent
  by_cases hc : ∃ a b c, a ∈ Sg ∧ b ∈ Sg ∧ c ∈ Sg ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ E b = E a ∧ E c = E a
  · obtain ⟨a, b, c, haS, hbS, hcS, hab, hac, hbc, hba, hca⟩ := hc
    have hcol : ∀ k ∈ Sg, ∀ m, m ≠ k → 𝐆 m k = 0 := fun k hk m hm => by
      rw [hsym]; exact hzero k m hm (by rw [hp_eq k hk]; exact hm)
    exact theorem18OnlyIf_of_eq_top hQ (rootGroup_eq_top_of_three h2 hQ γ hγ hab hac hbc (hcol a haS)
      (hcol b hbS) (hcol c hcS) (by rw [hdiagS b hbS, hdiagS a haS, hba]) (by rw [hdiagS c hcS, hdiagS a haS, hca]))
  push_neg at hc
  -- case (d): two single indices with the same exponent and `u + u' ≡ 2 mod 4`
  by_cases hd : ∃ a b, a ∈ Sg ∧ b ∈ Sg ∧ a ≠ b ∧ E b = E a ∧
      Valued.v (𝐆 a a + 𝐆 b b) = Valued.v (2 * 𝐆 a a)
  · obtain ⟨a, b, haS, hbS, hab, hba, hsum⟩ := hd
    have hcol : ∀ k ∈ Sg, ∀ m, m ≠ k → 𝐆 m k = 0 := fun k hk m hm => by
      rw [hsym]; exact hzero k m hm (by rw [hp_eq k hk]; exact hm)
    exact theorem18OnlyIf_of_eq_top hQ (rootGroup_eq_top_of_sum h2 hQ γ hγ hunits hab (hcol a haS) (hcol b hbS)
      (by rw [hdiagS b hbS, hdiagS a haS, hba]) hsum)
  push_neg at hd
  -- the level shape
  set lam : Fin n → ℤ := fun i => (E i - p - if i ∈ Sg then 1 else 0) / 2 with hlam
  have hlev : ∀ i, levE p lam Sg i = E i := by
    intro i
    simp only [levE, hlam]
    by_cases hiS : i ∈ Sg
    · have := hb i hiS; simp only [hiS, if_true]; omega
    · have := ha i hiS; simp only [hiS, if_false]; omega
  -- the inverse matrix
  set d : Fin n → Fv := fun i => 𝐆 i i * 𝐆 (partner i) (partner i) - 𝐆 i (partner i) * 𝐆 i (partner i) with hd'
  have hvd : ∀ i, i ∉ Sg → Valued.v (d i) = exp (-(2 * E i)) := by
    intro i hi
    have hsq : Valued.v (𝐆 i (partner i) * 𝐆 i (partner i)) = exp (-(2 * E i)) := by
      rw [map_mul, hvE, ← exp_add]; congr 1; ring
    have hlt : Valued.v (𝐆 i i * 𝐆 (partner i) (partner i)) < exp (-(2 * E i)) := by
      have h1 := hdiagP i hi
      have h2' := hdiagP (partner i) (hpp i hi).1
      rw [hEp] at h2'
      calc Valued.v (𝐆 i i * 𝐆 (partner i) (partner i)) ≤ exp (-(E i + 1)) * exp (-(E i + 1)) := by
            rw [map_mul]; exact mul_le_mul' h1 h2'
        _ < exp (-(2 * E i)) := by rw [← exp_add, exp_lt_exp]; omega
    simp only [hd']
    have hlt' : Valued.v (𝐆 i i * 𝐆 (partner i) (partner i)) <
        Valued.v (-(𝐆 i (partner i) * 𝐆 i (partner i))) := by rw [Valuation.map_neg, hsq]; exact hlt
    rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hlt', Valuation.map_neg, hsq]
  have hd0 : ∀ i, i ∉ Sg → d i ≠ 0 := fun i hi h0 => by
    have := hvd i hi; rw [h0, map_zero] at this; exact exp_ne_zero.symm this
  have hdp : ∀ i, i ∉ Sg → d (partner i) = d i := by
    intro i hi
    simp only [hd', (hpp i hi).2]
    rw [hsym (partner i) i]; ring
  set N : Matrix (Fin n) (Fin n) Fv := Matrix.of fun i j =>
    if i ∈ Sg then (if j = i then (𝐆 i i)⁻¹ else 0)
    else if j = i then 𝐆 (partner i) (partner i) / d i
    else if j = partner i then -𝐆 i j / d i else 0 with hN
  have hGN : 𝐆 * N = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hiS : i ∈ Sg
    · rw [Finset.sum_eq_single i (fun l _ hl => by rw [hzero i l hl (by rw [hp_eq i hiS]; exact hl), zero_mul])
        (by simp)]
      simp only [hN, of_apply, hiS, if_true, Matrix.one_apply]
      by_cases hji : j = i
      · subst hji; simp [mul_inv_cancel₀ ((hp_eq j hiS) ▸ hGne j)]
      · simp [hji, Ne.symm hji]
    · set q := partner i with hq
      obtain ⟨hqi, hGq⟩ := hp_ne i hiS
      obtain ⟨hqS, hqq⟩ := hpp i hiS
      have hsum : ∑ l, 𝐆 i l * N l j = 𝐆 i i * N i j + 𝐆 i q * N q j := by
        rw [← Finset.sum_pair (f := fun l => 𝐆 i l * N l j) (Ne.symm hqi)]
        refine (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_).symm
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
        rw [hzero i l hl.1 hl.2, zero_mul]
      rw [hsum]
      have hdq := hdp i hiS
      have hdi := hd0 i hiS
      have hdidef : d i = 𝐆 i i * 𝐆 q q - 𝐆 i q * 𝐆 i q := rfl
      have hNi : N i j = if j = i then 𝐆 q q / d i else if j = q then -𝐆 i j / d i else 0 := by
        simp only [hN, of_apply, if_neg hiS]
        rfl
      have hNq : N q j = if j = q then 𝐆 i i / d i else if j = i then -𝐆 q j / d i else 0 := by
        simp only [hN, of_apply]
        rw [if_neg hqS, hqq, hdq]
      rw [hNi, hNq]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, if_neg (Ne.symm hqi), if_pos rfl, Matrix.one_apply_eq]
        have e1 : 𝐆 j j * (𝐆 q q / d j) + 𝐆 j q * (-𝐆 q j / d j) = d j / d j := by
          rw [hsym j q, hdidef]; ring
        rw [e1, div_self hdi]
      · by_cases hjq : j = q
        · subst hjq
          rw [if_neg hji, if_pos rfl, if_pos rfl, Matrix.one_apply_ne (Ne.symm hji)]
          ring
        · rw [if_neg hji, if_neg hjq, if_neg hjq, if_neg hji, Matrix.one_apply_ne (Ne.symm hji)]
          ring
  have hs : LevelShape v 𝐆 N p lam Sg := by
    refine ⟨fun i j => ?_, fun i j => ?_, fun i hi => ?_, fun k hk m hm => ?_, fun k hk l hl hlk hll => ?_⟩
    · rw [hlev, hlev]
      by_cases hji : j = i
      · subst hji
        rw [max_self]
        by_cases hjS : j ∈ Sg
        · exact (hdiagS j hjS).le
        · exact ord_mono (hdiagP j hjS) (by omega)
      by_cases hjp : j = partner i
      · subst hjp; rw [hEp, max_self]; exact (hvE i).le
      · rw [hzero i j hji hjp, map_zero]; exact zero_le'
    · rw [hlev, hlev, neg_neg]
      simp only [hN, of_apply]
      by_cases hiS : i ∈ Sg
      · simp only [hiS, if_true]
        split_ifs with hji
        · subst hji; rw [min_self, map_inv₀, hdiagS j hiS, ← WithZero.exp_neg, neg_neg]
        · simp
      · simp only [hiS, if_false]
        have hd2 := hvd i hiS
        split_ifs with hji hjp
        · subst hji
          rw [min_self, map_div₀, hd2]
          have h1 := hdiagP (partner j) (hpp j hiS).1
          rw [hEp] at h1
          rw [div_le_iff₀ (zero_lt_iff.mpr exp_ne_zero), ← exp_add]
          exact h1.trans (exp_le_exp.mpr (by omega))
        · subst hjp
          rw [hEp, min_self, map_div₀, Valuation.map_neg, hvE, hd2, div_eq_mul_inv, ← WithZero.exp_neg, ← exp_add]
          exact exp_le_exp.mpr (by omega)
        · simp
    · rw [hlev]; exact hdiagP i hi
    · rw [hsym]; exact hzero k m hm (by rw [hp_eq k hk]; exact hm)
    · have hEl : E l = E k := by
        have h1 := hlev l; have h2' := hlev k
        rw [levE_of_mem hl] at h1; rw [levE_of_mem hk] at h2'
        rw [← h1, ← h2', hll]
      refine ⟨fun l' hl' hl'k hl'l => ?_, ?_⟩
      · by_contra hne
        have hEl' : E l' = E k := by
          have h1 := hlev l'; have h2' := hlev k
          rw [levE_of_mem hl'] at h1; rw [levE_of_mem hk] at h2'
          rw [← h1, ← h2', hl'l]
        exact hc k l l' hk hl hl' (Ne.symm hlk) (Ne.symm hl'k) (Ne.symm hne) hEl hEl'
      · rw [hlev]
        have hvl : Valued.v (𝐆 l l) = Valued.v (𝐆 k k) := by rw [hdiagS l hl, hdiagS k hk, hEl]
        have hle : Valued.v (𝐆 k k + 𝐆 l l) ≤ Valued.v (2 * 𝐆 k k) :=
          valued_add_le_two_mul h2 (by have := hGne k; rwa [hp_eq k hk] at this) hvl.symm
        have hne := hd k l hk hl (Ne.symm hlk) hEl
        have hlt : Valued.v (𝐆 k k + 𝐆 l l) < Valued.v (2 * 𝐆 k k) := lt_of_le_of_ne hle hne
        have := valued_le_two_mul_of_lt h2 hlt
        rwa [← mul_assoc, map_mul, map_mul, hv2, hdiagS k hk, ← exp_add, ← exp_add,
          show -1 + -1 + -E k = -(E k + 2) by ring] at this
  exact theorem18OnlyIf_of_levelShape hQ h2 γ hγ N hGN hs (Ne.symm hj0i0) horth hG0 hi hj

/-- **Theorem 18, "only if", at $p = 2$ for every lattice** (Conway–Sloane §9.5, p. 391, "based on Theorem 81 of
[Wat3]"; unconditional): for every regular form $Q$ over $\mathbb Q$, every lattice $L$ and the prime $v$ over $2$,
every element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of $2$-adic root
vectors. *Proof.* Rescale $L_2$ by $2^k$ so that $Q$ is integral on it (same automorphisms and root group), take a
$2$-adic Jordan basis (`exists_dyadic_basis`) and apply `theorem18OnlyIf_of_jordan`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if', every lattice)"]
theorem theorem18OnlyIf_dyadic (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (L : Lat ℚ n) :
    Theorem18OnlyIf Q L v hQ := by
  classical
  obtain ⟨γ0, hγ0⟩ := exists_locAct_std_model (v := v) L
  obtain ⟨a, ha0, ha⟩ : ∃ a : ℤ, 0 ≤ a ∧ ∀ i j, Valued.v (locGram Q v γ0 i j) ≤ exp a := by
    refine ⟨∑ i, ∑ j, max 0 (log (Valued.v (locGram Q v γ0 i j))),
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_left _ _, fun i j => ?_⟩
    by_cases h0 : locGram Q v γ0 i j = 0
    · rw [h0, map_zero]; exact zero_le'
    · have hv : Valued.v (locGram Q v γ0 i j) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
      rw [← exp_log hv, exp_le_exp]
      calc log (Valued.v (locGram Q v γ0 i j)) ≤ max 0 (log (Valued.v (locGram Q v γ0 i j))) :=
            le_max_right _ _
        _ ≤ ∑ j', max 0 (log (Valued.v (locGram Q v γ0 i j'))) :=
            Finset.single_le_sum (f := fun j' => max 0 (log (Valued.v (locGram Q v γ0 i j'))))
              (fun _ _ => le_max_left _ _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', max 0 (log (Valued.v (locGram Q v γ0 i' j'))) :=
            Finset.single_le_sum (f := fun i' => ∑ j', max 0 (log (Valued.v (locGram Q v γ0 i' j'))))
              (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_left _ _) (Finset.mem_univ i)
  set c : Fv := (2 : Fv) ^ (a + 1) with hc
  have hc0 : c ≠ 0 := zpow_ne_zero _ two_ne_zero
  set D : GL (Fin n) Fv := diagGL (fun _ : Fin n => c) (fun _ => hc0) with hD
  have hcomm : γ0 * D = D * γ0 := by
    ext i j
    simp only [hD, Units.val_mul, diagGL_val, mul_diagonal, diagonal_mul]
    ring
  obtain ⟨L1, hL1⟩ := exists_lat_loc_eq v (γ0 * D)
  have hloc : loc v L1.1 = locAct v D (loc v L.1) := by rw [hL1, hγ0, hcomm, locAct_mul]
  have hstab : locStabV Q v L = locStabV Q v L1 := by
    ext σ
    change locAct v (σ : GL (Fin n) Fv) (loc v L.1) = loc v L.1 ↔
      locAct v (σ : GL (Fin n) Fv) (loc v L1.1) = loc v L1.1
    have hσD : (σ : GL (Fin n) Fv) * D = D * (σ : GL (Fin n) Fv) := by
      ext i j
      simp only [hD, Units.val_mul, diagGL_val, mul_diagonal, diagonal_mul]
      ring
    rw [hloc, ← locAct_mul, hσD, locAct_mul]
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg (locAct v D⁻¹) h
      rwa [locAct_inv_locAct, locAct_inv_locAct] at this
  rw [theorem18OnlyIf_congr hQ hstab]
  have hG1 : ∀ i j, Valued.v (locGram Q v (γ0 * D) i j) ≤ exp (-1) := by
    intro i j
    rw [hD, locGram_mul_diagGL, mul_diagonal, diagonal_mul]
    refine ord_mono (ord_mul (ord_mul (ord_two_zpow h2 (a + 1)) (b := -a) (by rw [neg_neg]; exact ha i j)) (ord_two_zpow h2 (a + 1))) ?_
    omega
  have hint : ∀ x ∈ loc v L1.1, Valued.v (Q.evalIn Fv x) ≤ 1 := by
    intro x hx
    rw [hL1, mem_locAct] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' := mem_std_iff.mp hy
    have e : 2 * Q.evalIn Fv ((γ0 * D).val *ᵥ y) = y ⬝ᵥ (locGram Q v (γ0 * D) *ᵥ y) := by
      rw [two_mul_evalIn_eq, qbil_mulVec_locGram]
    have hdot : Valued.v (y ⬝ᵥ (locGram Q v (γ0 * D) *ᵥ y)) ≤ exp (-(1 + 0)) := by
      refine ord_sum _ _ fun i _ => ?_
      have hyi : Valued.v (y i) ≤ exp (-0) := by rw [ord_zero_iff]; exact hy' i
      have hin : Valued.v ((locGram Q v (γ0 * D) *ᵥ y) i) ≤ exp (-1) := by
        refine ord_sum _ _ fun j _ => ?_
        have hyj : Valued.v (y j) ≤ exp (-0) := by rw [ord_zero_iff]; exact hy' j
        exact ord_mono (ord_mul (hG1 i j) hyj) (by omega)
      exact ord_mono (ord_mul hyi hin) (by omega)
    rw [← e] at hdot
    rw [← ord_zero_iff]
    exact ord_cancel (valued_two_eq h2) hdot
  have h2' : ¬ LocalDensity.NF.π v ^ 2 ∣ 2 := fun h =>
    Tamagawa.Indefinite.two_not_mem_sq h2 ((LocalDensity.NF.π_pow_dvd_two_iff v 2).mp h)
  obtain ⟨γ', P, ν, hγ', -, hzero, hdisj, hpair, -⟩ :=
    exists_dyadic_basis hQ (valued_two_dyadic v h2) h2' L1 (γ0 * D) hL1 hint
  have hmem : ∀ i j, j ≠ i → locGram Q v γ' i j ≠ 0 → (i, j) ∈ P ∨ (j, i) ∈ P := by
    intro i j hji hne
    by_contra hc'
    push_neg at hc'
    exact hne (hzero i j (Ne.symm hji) hc'.1 hc'.2)
  have hsame : ∀ i, ∀ e ∈ P, ∀ e' ∈ P, (e.1 = i ∨ e.2 = i) → (e'.1 = i ∨ e'.2 = i) → e = e' := by
    intro i e he e' he' hi hi'
    by_contra hne
    obtain ⟨h1, h2'', h3, h4⟩ := hdisj e he e' he' hne
    rcases hi with hi | hi <;> rcases hi' with hi' | hi'
    · exact h1 (hi.trans hi'.symm)
    · exact h2'' (hi.trans hi'.symm)
    · exact h3 (hi.trans hi'.symm)
    · exact h4 (hi.trans hi'.symm)
  refine theorem18OnlyIf_of_jordan hQ h2 γ' hγ' (fun i j j' hji hj'i hj hj' => ?_) (fun i j hij hne => ?_)
  · rcases hmem i j hji hj with h | h <;> rcases hmem i j' hj'i hj' with h' | h'
    · have := hsame i _ h _ h' (Or.inl rfl) (Or.inl rfl)
      exact (Prod.ext_iff.mp this).2
    · have := hsame i _ h _ h' (Or.inl rfl) (Or.inr rfl)
      exact absurd (Prod.ext_iff.mp this).1 (Ne.symm hj'i)
    · have := hsame i _ h _ h' (Or.inr rfl) (Or.inl rfl)
      exact absurd (Prod.ext_iff.mp this).1 hji
    · have := hsame i _ h _ h' (Or.inr rfl) (Or.inr rfl)
      exact (Prod.ext_iff.mp this).1
  · rcases hmem i j (Ne.symm hij) hne with h | h
    · exact (hpair _ h).2.2.1
    · have := (hpair _ h).2.2.2
      rwa [locGram_symm' γ' j i] at this

/-- **The eleventh residual statement holds** (`Theorem18DyadicResidual11`, the last named statement left open, is a
theorem): by `theorem18OnlyIf_dyadic`. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2: the last residual statement is proved)"]
theorem theorem18DyadicResidual11_holds : Theorem18DyadicResidual11 :=
  ⟨fun _ _ hQ L _ h2 _ => theorem18OnlyIf_dyadic hQ h2 L⟩

/-- **Conway–Sloane's Theorem 18, unconditional** (`Theorem18Statement`: every prime, both directions; Ch. 15, §9.5,
p. 391, "based on Theorem 81 of [Wat3]"). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (unconditional)"]
theorem theorem18Statement_holds : Theorem18Statement :=
  theorem18Statement_of_residual11 theorem18DyadicResidual11_holds

end Classify

end QuadFormsKB.ConwaySloane
