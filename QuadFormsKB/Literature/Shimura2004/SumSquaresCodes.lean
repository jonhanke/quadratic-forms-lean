/-
# $\mathbb Z$-maximal lattices over $\mathbb Z^n$ for the sum of squares, and binary codes

Let $\varphi[x] = x_0^2 + \dots + x_{n-1}^2$ on $V = \mathbb Q^n$ and let $M \supseteq \mathbb Z^n$ be a lattice with
$\varphi[M] \subseteq \mathbb Z$. Then $2x \in \mathbb Z^n$ for $x \in M$ (since $2x_i = \varphi[x + e_i] - \varphi[x]
- 1$), and the set $\operatorname{odd}(x)$ of coordinates where $x_i \notin \mathbb Z$ has cardinality divisible by $4$
(`four_dvd_card_oddSet`). So $M = \mathbb Z^n + \tfrac12 C$ for a doubly even binary code $C$, and $M$ is
$\mathbb Z$-maximal iff $C$ is a maximal doubly even code.

This file proves the facts about half-integral vectors used for the classification, and the case $n = 5$ of
`SumSqMaxOverIntVec` (`sumSqMaxOverIntVec_five`): the maximal doubly even codes of length $5$ are $\{0, w\}$ with $w$ of
weight $4$, and two of them differ by a transposition of coordinates.

Indices are 0-based.
-/
import QuadFormsKB.Literature.Shimura2004.SumSquaresOneClass

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices Classical

variable {n : ℕ}

/-! ### Half-integral vectors -/

/-- A rational number is an integer. -/
def IsIntQ (q : ℚ) : Prop := ∃ m : ℤ, q = m

/-- **The odd set** of $x \in \mathbb Q^n$: the coordinates $i$ with $x_i \notin \mathbb Z$ (for $2x \in \mathbb Z^n$,
the support of the binary word $2x \bmod 2$). -/
def oddSet (x : Fin n → ℚ) : Finset (Fin n) := Finset.univ.filter fun i => ¬ IsIntQ (x i)

theorem mem_oddSet {x : Fin n → ℚ} {i : Fin n} : i ∈ oddSet x ↔ ¬ IsIntQ (x i) := by
  simp [oddSet]

theorem mem_intVec_iff_int {x : Fin n → ℚ} :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, IsIntQ (x i) := by
  rw [mem_intVec]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Rat.ringOfIntegersEquiv a, by rw [Rat.ringOfIntegersEquiv_apply_coe]; exact ha.symm⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : 𝓞 ℚ), by rw [hm]; simp⟩

theorem mem_intVec_of_oddSet_eq_empty {x : Fin n → ℚ} (h : oddSet x = ∅) :
    x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
  rw [mem_intVec_iff_int]
  intro i
  by_contra hi
  have : i ∈ oddSet x := mem_oddSet.mpr hi
  rw [h] at this
  simp at this

/-- $x$ is half-integral: $2x \in \mathbb Z^n$. -/
def IsHalfInt (x : Fin n → ℚ) : Prop := ∀ i, ∃ k : ℤ, 2 * x i = k

theorem isIntQ_iff_even {q : ℚ} {k : ℤ} (hk : 2 * q = k) : IsIntQ q ↔ Even k := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by exact_mod_cast (by linarith : (k : ℚ) = m + m)⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast at hk; linarith⟩

theorem IsHalfInt.add {x y : Fin n → ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) : IsHalfInt (x + y) := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  exact ⟨a + b, by simp only [Pi.add_apply]; push_cast; linarith⟩

theorem IsHalfInt.neg {x : Fin n → ℚ} (hx : IsHalfInt x) : IsHalfInt (-x) := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  exact ⟨-a, by simp only [Pi.neg_apply]; push_cast; linarith⟩

theorem IsHalfInt.sub {x y : Fin n → ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) : IsHalfInt (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

/-- **The odd set of a sum** of half-integral vectors is the symmetric difference of the odd sets. -/
theorem oddSet_add {x y : Fin n → ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    oddSet (x + y) = symmDiff (oddSet x) (oddSet y) := by
  ext i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  have hab : 2 * (x + y) i = ((a + b : ℤ) : ℚ) := by simp only [Pi.add_apply]; push_cast; linarith
  rw [Finset.mem_symmDiff, mem_oddSet, mem_oddSet, mem_oddSet, isIntQ_iff_even hab, isIntQ_iff_even ha,
    isIntQ_iff_even hb, Int.even_add]
  tauto

theorem oddSet_neg {x : Fin n → ℚ} (hx : IsHalfInt x) : oddSet (-x) = oddSet x := by
  ext i
  obtain ⟨a, ha⟩ := hx i
  have ha' : 2 * (-x) i = ((-a : ℤ) : ℚ) := by simp only [Pi.neg_apply]; push_cast; linarith
  rw [mem_oddSet, mem_oddSet, isIntQ_iff_even ha', isIntQ_iff_even ha, even_neg]

theorem oddSet_sub {x y : Fin n → ℚ} (hx : IsHalfInt x) (hy : IsHalfInt y) :
    oddSet (x - y) = symmDiff (oddSet x) (oddSet y) := by
  rw [sub_eq_add_neg, oddSet_add hx hy.neg, oddSet_neg hy]

/-- For an integer vector $k$, $\sum_i k_i^2 \equiv \#\{i : k_i \text{ odd}\} \pmod 4$. -/
theorem four_dvd_sum_sq_sub_card (k : Fin n → ℤ) :
    (4 : ℤ) ∣ ∑ i, k i ^ 2 - ((Finset.univ.filter fun i => ¬ Even (k i)).card : ℤ) := by
  rw [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  rcases Int.even_or_odd (k i) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have : ¬ ¬ Even (k i) := not_not.mpr ⟨m, hm⟩
    rw [if_neg this, hm]; push_cast; exact ⟨m ^ 2, by ring⟩
  · have : ¬ Even (k i) := Int.not_even_iff_odd.mpr ⟨m, hm⟩
    rw [if_pos this, hm]; push_cast; exact ⟨m ^ 2 + m, by ring⟩

/-- **For half-integral $x$: $\varphi[x] \in \mathbb Z$ iff $4 \mid \#\operatorname{odd}(x)$.** -/
theorem isIntQ_sum_sq_iff {x : Fin n → ℚ} (hx : IsHalfInt x) :
    IsIntQ (∑ i, x i ^ 2) ↔ 4 ∣ (oddSet x).card := by
  choose k hk using hx
  have hodd : oddSet x = Finset.univ.filter fun i => ¬ Even (k i) := by
    ext i; rw [mem_oddSet, isIntQ_iff_even (hk i)]; simp
  have hsum : (4 : ℚ) * ∑ i, x i ^ 2 = ((∑ i, k i ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hk i]; ring
  obtain ⟨t, ht⟩ := four_dvd_sum_sq_sub_card k
  rw [hodd]
  set c := (Finset.univ.filter fun i => ¬ Even (k i)).card
  constructor
  · rintro ⟨m, hm⟩
    have h1 : ((∑ i, k i ^ 2 : ℤ) : ℚ) = ((4 * m : ℤ) : ℚ) := by rw [← hsum, hm]; push_cast; ring
    have h2 : (∑ i, k i ^ 2 : ℤ) = 4 * m := by exact_mod_cast h1
    have : (c : ℤ) = 4 * (m - t) := by linarith
    have h4 : (4 : ℤ) ∣ (c : ℤ) := ⟨m - t, this⟩
    exact_mod_cast h4
  · rintro ⟨d, hd⟩
    refine ⟨d + t, ?_⟩
    have h2 : (∑ i, k i ^ 2 : ℤ) = 4 * (d + t) := by
      have : (c : ℤ) = 4 * d := by exact_mod_cast hd
      linarith
    have : (4 : ℚ) * ∑ i, x i ^ 2 = 4 * ((d + t : ℤ) : ℚ) := by rw [hsum, h2]; push_cast; ring
    linarith

/-! ### Lattices over $\mathbb Z^n$ with integral norm -/

theorem sosQ_eval_eq (x : Fin n → ℚ) : (sosQ n).eval x = ∑ i, x i ^ 2 := by
  rw [← omeara_Q_eq]; exact sosQ_toQF_eq x

/-- An integral-norm lattice: $\varphi[x] \in \mathbb Z$ for $x \in M$. -/
def IntNorm (M : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop := ∀ x ∈ M, IsIntQ (∑ i, x i ^ 2)

theorem intNorm_of_isGMaximal {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M) : IntNorm M.1 := by
  intro x hx
  have h := hM.2.1 (OMeara.Q_mem_normIdeal _ hx)
  obtain ⟨m, hm⟩ := (mem_one_iff_int _).mp h
  exact ⟨m, by rw [← hm, sosQ_toQF_eq]⟩

theorem normIdeal_le_one_of_intNorm {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IntNorm M) :
    OMeara.normIdeal (sosQ n).toQuadraticForm M ≤ 1 := by
  rw [OMeara.normIdeal, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm⟩ := hM x hx
  exact (mem_one_iff_int _).mpr ⟨m, by rw [sosQ_toQF_eq]; exact hm⟩

/-- In an integral-norm lattice containing $\mathbb Z^n$, every vector is half-integral. -/
theorem isHalfInt_of_mem {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IntNorm M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M) {x : Fin n → ℚ} (hx : x ∈ M) : IsHalfInt x := by
  intro i
  set e1 : Fin n → ℚ := Pi.single i 1 with he1
  have he : e1 ∈ M := hZ (single_one_mem_intVec i)
  obtain ⟨a, ha⟩ := hM _ (M.add_mem hx he)
  obtain ⟨b, hb⟩ := hM x hx
  refine ⟨a - b - 1, ?_⟩
  have e : ∑ j, (x + e1) j ^ 2 = ∑ j, x j ^ 2 + (2 * x i + 1) := by
    have : ∀ j, (x + e1) j ^ 2 = x j ^ 2 + (if i = j then 2 * x i + 1 else 0) := by
      intro j
      by_cases hj : i = j
      · subst hj; simp [he1]; ring
      · simp [he1, hj, Ne.symm hj]
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp
  push_cast
  linarith

theorem four_dvd_card_oddSet {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IntNorm M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M) {x : Fin n → ℚ} (hx : x ∈ M) : 4 ∣ (oddSet x).card :=
  (isIntQ_sum_sq_iff (isHalfInt_of_mem hM hZ hx)).mp (hM x hx)

/-- If $\gamma M \subseteq M'$ with $M$ $\mathbb Z$-maximal and $M'$ of integral norm, then $\gamma M = M'$. -/
theorem image_eq_of_le {M M' : Lat ℚ n} (hM : IsGMaximal (sosQ n) M) (hM' : IntNorm M'.1) {γ : GL (Fin n) ℚ}
    (hγ : γ ∈ orthGroup (sosQ n) ℚ) (hle : glImage γ M.1 ≤ M'.1) : IsIsometric (sosQ n) M.1 M'.1 :=
  ⟨γ, hγ, ((isGMaximal_image hM hγ).2.2 M'.1 M'.2 hle (normIdeal_le_one_of_intNorm hM')).symm⟩

/-! ### Permutations of coordinates -/

/-- **The permutation matrix** of $\sigma$, acting by $(Px)_i = x_{\sigma(i)}$. -/
def permGL (σ : Equiv.Perm (Fin n)) : GL (Fin n) ℚ :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl],
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]⟩

theorem permGL_mulVec (σ : Equiv.Perm (Fin n)) (x : Fin n → ℚ) : (permGL σ).val *ᵥ x = x ∘ σ :=
  PEquiv.toMatrix_toPEquiv_mulVec σ x

theorem permGL_mem_orth (σ : Equiv.Perm (Fin n)) : permGL σ ∈ orthGroup (sosQ n) ℚ := by
  refine mem_orthGroup_of_eval _ fun z => ?_
  rw [permGL_mulVec, sosQ_eval_eq, sosQ_eval_eq]
  exact Equiv.sum_comp σ (fun i => z i ^ 2)

theorem mem_oddSet_comp {x : Fin n → ℚ} (σ : Equiv.Perm (Fin n)) {i : Fin n} :
    i ∈ oddSet (x ∘ σ) ↔ σ i ∈ oddSet x := by
  simp [mem_oddSet]

theorem isHalfInt_comp {x : Fin n → ℚ} (hx : IsHalfInt x) (σ : Equiv.Perm (Fin n)) : IsHalfInt (x ∘ σ) :=
  fun i => hx (σ i)

/-! ### Maximality -/

theorem isIntQ_int (m : ℤ) : IsIntQ (m : ℚ) := ⟨m, rfl⟩

theorem not_isIntQ_half : ¬ IsIntQ (1 / 2 : ℚ) := by
  rintro ⟨m, hm⟩
  have : (2 * m : ℤ) = 1 := by exact_mod_cast (by linarith : (2 : ℚ) * m = 1)
  omega

theorem isHalfInt_of_intVec {x : Fin n → ℚ} (hx : x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ))) :
    IsHalfInt x := by
  intro i
  obtain ⟨m, hm⟩ := mem_intVec_iff_int.mp hx i
  exact ⟨2 * m, by rw [hm]; push_cast; ring⟩

theorem oddSet_eq_empty_of_intVec {x : Fin n → ℚ} (hx : x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ))) :
    oddSet x = ∅ := by
  ext i
  simp only [mem_oddSet, Finset.notMem_empty, iff_false, not_not]
  exact mem_intVec_iff_int.mp hx i

/-- $2x \in \mathbb Z^n$ for half-integral $x$. -/
theorem two_smul_mem_intVec {x : Fin n → ℚ} (hx : IsHalfInt x) :
    (2 : ℚ) • x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
  rw [mem_intVec_iff_int]
  intro i
  obtain ⟨k, hk⟩ := hx i
  exact ⟨k, by simp [hk]⟩

theorem int_smul_mem_intVec_of_even {x : Fin n → ℚ} (hx : IsHalfInt x) {k : ℤ} (hk : Even k) :
    (k : ℚ) • x ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
  obtain ⟨m, rfl⟩ := hk
  have : ((m + m : ℤ) : ℚ) • x = ((m : 𝓞 ℚ)) • ((2 : ℚ) • x) := by
    rw [show ((m : 𝓞 ℚ)) • ((2 : ℚ) • x) = ((m : ℚ)) • ((2 : ℚ) • x) from by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]]
    rw [smul_smul]; push_cast; ring_nf
  rw [this]
  exact Submodule.smul_mem _ _ (two_smul_mem_intVec hx)

/-- **Adjoining a compatible half-vector keeps the norm integral**: if $M \supseteq \mathbb Z^n$ has integral norm,
$x$ is half-integral and $4 \mid \#\operatorname{odd}(y + x)$ for all $y \in M$, then $M + \mathbb Zx$ has integral
norm. -/
theorem intNorm_sup {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hM : IntNorm M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M) {x : Fin n → ℚ} (hx : IsHalfInt x)
    (hc : ∀ y ∈ M, 4 ∣ (oddSet (y + x)).card) : IntNorm (M ⊔ Submodule.span (𝓞 ℚ) {x}) := by
  intro z hz
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = c :=
    ⟨Rat.ringOfIntegersEquiv c, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply c)⟩
  subst hk
  have hcx : ((k : ℤ) : 𝓞 ℚ) • x = (k : ℚ) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  rw [hcx]
  rcases Int.even_or_odd k with he | ho
  · exact hM _ (M.add_mem hy (hZ (int_smul_mem_intVec_of_even hx he)))
  · have he : Even (k - 1) := by
      rcases ho with ⟨m, hm⟩; exact ⟨m, by omega⟩
    have hy' : y + ((k - 1 : ℤ) : ℚ) • x ∈ M := M.add_mem hy (hZ (int_smul_mem_intVec_of_even hx he))
    have e : y + (k : ℚ) • x = (y + ((k - 1 : ℤ) : ℚ) • x) + x := by
      push_cast; rw [sub_smul, one_smul]; abel
    rw [e]
    exact (isIntQ_sum_sq_iff ((isHalfInt_of_mem hM hZ hy').add hx)).mpr (hc _ hy')

/-- **Maximality**: if $M \supseteq \mathbb Z^n$ is $\mathbb Z$-maximal and $x$ is half-integral with
$4 \mid \#\operatorname{odd}(y + x)$ for every $y \in M$, then $x \in M$. -/
theorem mem_of_isGMaximal {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1) {x : Fin n → ℚ} (hx : IsHalfInt x)
    (hc : ∀ y ∈ M.1, 4 ∣ (oddSet (y + x)).card) : x ∈ M.1 := by
  have hK := intNorm_sup (intNorm_of_isGMaximal hM) hZ hx hc
  have hlat : (M.1 ⊔ Submodule.span (𝓞 ℚ) {x}).IsLattice ℚ := by
    refine ⟨M.2.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    rw [eq_top_iff, ← M.2.span_eq_top]
    exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)
  have heq := hM.2.2 _ hlat le_sup_left (normIdeal_le_one_of_intNorm hK)
  rw [← heq]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

/-! ### Dimension 5 -/

section Five

/-- The vector $h = \tfrac12(e_0 + e_1 + e_2 + e_3)$ in $\mathbb Q^5$. -/
def hFive : Fin 5 → ℚ := ![1 / 2, 1 / 2, 1 / 2, 1 / 2, 0]

theorem isHalfInt_hFive : IsHalfInt hFive := by
  intro i
  fin_cases i
  · exact ⟨1, by simp [hFive]⟩
  · exact ⟨1, by simp [hFive]⟩
  · exact ⟨1, by simp [hFive]⟩
  · exact ⟨1, by simp [hFive]⟩
  · exact ⟨0, by simp [hFive]⟩

theorem oddSet_hFive : oddSet hFive = Finset.univ.erase 4 := by
  ext i
  rw [mem_oddSet]
  fin_cases i
  · simpa [hFive] using not_isIntQ_half
  · simpa [hFive] using not_isIntQ_half
  · simpa [hFive] using not_isIntQ_half
  · simpa [hFive] using not_isIntQ_half
  · simpa [hFive] using isIntQ_int 0

theorem eq_erase_of_card_four {s : Finset (Fin 5)} (h : s.card = 4) : ∃ i, s = Finset.univ.erase i := by
  have hc : sᶜ.card = 1 := by rw [Finset.card_compl, h]; rfl
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  refine ⟨i, ?_⟩
  rw [← compl_compl s, hi]
  ext j; simp

theorem card_cases_five {s : Finset (Fin 5)} (h : 4 ∣ s.card) : s = ∅ ∨ ∃ i, s = Finset.univ.erase i := by
  have hle : s.card ≤ 5 := by simpa using Finset.card_le_univ s
  obtain ⟨c, hc⟩ := h
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · exact Or.inl (Finset.card_eq_zero.mp hc)
  · exact Or.inr (eq_erase_of_card_four hc)

theorem card_symmDiff_erase_five : ∀ i j : Fin 5, i ≠ j →
    (symmDiff (Finset.univ.erase i) (Finset.univ.erase j)).card = 2 := by
  decide

/-- **A $\mathbb Z$-maximal $M \supseteq \mathbb Z^5$ has a half-vector with odd set of size $4$**, and then every
vector of $M$ has odd set $\emptyset$ or that set. -/
theorem exists_erase_five {M : Lat ℚ 5} (hM : IsGMaximal (sosQ 5) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 5 → ℚ)) ≤ M.1) :
    ∃ x ∈ M.1, ∃ i, oddSet x = Finset.univ.erase i ∧
      ∀ y ∈ M.1, oddSet y = ∅ ∨ oddSet y = Finset.univ.erase i := by
  have hN := intNorm_of_isGMaximal hM
  have hcase : ∀ y ∈ M.1, oddSet y = ∅ ∨ ∃ i, oddSet y = Finset.univ.erase i :=
    fun y hy => card_cases_five (four_dvd_card_oddSet hN hZ hy)
  by_cases hall : ∀ y ∈ M.1, oddSet y = ∅
  · exfalso
    have hmem : hFive ∈ M.1 := by
      refine mem_of_isGMaximal hM hZ isHalfInt_hFive fun y hy => ?_
      rw [oddSet_add (isHalfInt_of_mem hN hZ hy) isHalfInt_hFive, hall y hy, oddSet_hFive]
      decide
    have := hall _ hmem
    rw [oddSet_hFive] at this
    exact absurd this (by decide)
  push Not at hall
  obtain ⟨x, hx, hx0⟩ := hall
  obtain ⟨i, hi⟩ := (hcase x hx).resolve_left (Finset.nonempty_iff_ne_empty.mp hx0)
  refine ⟨x, hx, i, hi, fun y hy => ?_⟩
  rcases hcase y hy with h | ⟨j, hj⟩
  · exact Or.inl h
  · right
    by_contra hne
    have hij : i ≠ j := fun h => hne (h ▸ hj)
    have h4 := four_dvd_card_oddSet hN hZ (M.1.add_mem hx hy)
    rw [oddSet_add (isHalfInt_of_mem hN hZ hx) (isHalfInt_of_mem hN hZ hy), hi, hj,
      card_symmDiff_erase_five i j hij] at h4
    omega

/-- **`SumSqMaxOverIntVec 5`**: two $\mathbb Z$-maximal lattices over $\mathbb Z^5$ for the sum of five squares are
isometric, by a transposition of coordinates. (Each is $\mathbb Z^5 + \mathbb Z\tfrac12(\mathbf 1 - e_i)$.) -/
theorem sumSqMaxOverIntVec_five : SumSqMaxOverIntVec 5 := by
  refine ⟨fun M M' hM hM' hZ hZ' => ?_⟩
  obtain ⟨x, hx, i, hi, hM5⟩ := exists_erase_five hM hZ
  obtain ⟨x', hx', i', hi', -⟩ := exists_erase_five hM' hZ'
  have hN := intNorm_of_isGMaximal hM
  have hN' := intNorm_of_isGMaximal hM'
  let σ : Equiv.Perm (Fin 5) := Equiv.swap i i'
  refine image_eq_of_le hM hN' (permGL_mem_orth σ) ?_
  rintro _ ⟨y, hy, rfl⟩
  change (permGL σ).val *ᵥ y ∈ M'.1
  rw [permGL_mulVec]
  have hyh := isHalfInt_of_mem hN hZ hy
  rcases hM5 y hy with h0 | h1
  · apply hZ'
    apply mem_intVec_of_oddSet_eq_empty
    ext k
    rw [mem_oddSet_comp, h0]
    simp
  · have hc : oddSet (y ∘ σ) = Finset.univ.erase i' := by
      ext k
      rw [mem_oddSet_comp, h1, Finset.mem_erase, Finset.mem_erase]
      simp only [Finset.mem_univ, and_true]
      constructor
      · intro h hk; apply h; rw [hk]; exact Equiv.swap_apply_right i i'
      · intro h hk; apply h
        have := congrArg σ hk
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    have hd : y ∘ σ - x' ∈ (intVec : Submodule (𝓞 ℚ) (Fin 5 → ℚ)) := by
      apply mem_intVec_of_oddSet_eq_empty
      rw [oddSet_sub (isHalfInt_comp hyh σ) (isHalfInt_of_mem hN' hZ' hx'), hc, hi']
      simp
    have := M'.1.add_mem (hZ' hd) hx'
    rwa [sub_add_cancel] at this

end Five

/-! ### The code of a lattice over $\mathbb Z^n$ -/

section Code

variable {n : ℕ}

/-- $T$ is a word of the code of $M$: $T = \operatorname{odd}(y)$ for some $y \in M$. -/
def InCode (M : Submodule (𝓞 ℚ) (Fin n → ℚ)) (T : Finset (Fin n)) : Prop := ∃ y ∈ M, oddSet y = T

/-- The half-vector $\tfrac12 \mathbf 1_T$. -/
def halfVec (T : Finset (Fin n)) : Fin n → ℚ := fun i => if i ∈ T then 1 / 2 else 0

theorem isHalfInt_halfVec (T : Finset (Fin n)) : IsHalfInt (halfVec T) := by
  intro i
  by_cases hi : i ∈ T
  · exact ⟨1, by simp [halfVec, hi]⟩
  · exact ⟨0, by simp [halfVec, hi]⟩

theorem oddSet_halfVec (T : Finset (Fin n)) : oddSet (halfVec T) = T := by
  ext i
  rw [mem_oddSet]
  by_cases hi : i ∈ T
  · simpa [halfVec, hi] using not_isIntQ_half
  · simpa [halfVec, hi] using isIntQ_int 0

variable {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (hN : IntNorm M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M)
include hN hZ

theorem InCode.symmDiff {T U : Finset (Fin n)} (hT : InCode M T) (hU : InCode M U) :
    InCode M (symmDiff T U) := by
  obtain ⟨y, hy, rfl⟩ := hT
  obtain ⟨z, hz, rfl⟩ := hU
  exact ⟨y + z, M.add_mem hy hz, oddSet_add (isHalfInt_of_mem hN hZ hy) (isHalfInt_of_mem hN hZ hz)⟩

theorem InCode.four_dvd {T : Finset (Fin n)} (hT : InCode M T) : 4 ∣ T.card := by
  obtain ⟨y, hy, rfl⟩ := hT
  exact four_dvd_card_oddSet hN hZ hy

/-- **Representatives**: a half-integral vector whose odd set is a code word lies in $M$. -/
theorem mem_of_inCode {T : Finset (Fin n)} (hT : InCode M T) {z : Fin n → ℚ} (hz : IsHalfInt z)
    (hzT : oddSet z = T) : z ∈ M := by
  obtain ⟨y, hy, rfl⟩ := hT
  have hd : z - y ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
    apply mem_intVec_of_oddSet_eq_empty
    rw [oddSet_sub hz (isHalfInt_of_mem hN hZ hy), hzT, symmDiff_self]
    rfl
  have := M.add_mem (hZ hd) hy
  rwa [sub_add_cancel] at this

omit hN in
theorem inCode_empty : InCode M ∅ :=
  ⟨0, M.zero_mem, oddSet_eq_empty_of_intVec (Submodule.zero_mem _)⟩

end Code

/-- **Maximality for code words**: if $M \supseteq \mathbb Z^n$ is $\mathbb Z$-maximal, $4 \mid \#T$ and
$4 \mid \#(U \mathbin\triangle T)$ for every code word $U$ of $M$, then $T$ is a code word. -/
theorem inCode_of_isGMaximal {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1) {T : Finset (Fin n)}
    (hc : ∀ U, InCode M.1 U → 4 ∣ (symmDiff U T).card) : InCode M.1 T := by
  have hN := intNorm_of_isGMaximal hM
  refine ⟨halfVec T, mem_of_isGMaximal hM hZ (isHalfInt_halfVec T) fun y hy => ?_, oddSet_halfVec T⟩
  rw [oddSet_add (isHalfInt_of_mem hN hZ hy) (isHalfInt_halfVec T), oddSet_halfVec]
  exact hc _ ⟨y, hy, rfl⟩

/-- Two $\mathbb Z$-maximal lattices over $\mathbb Z^n$ whose codes contain a set $S$ that is *self-maximal* (every
$T$ with $4 \mid \#T$ and $4 \mid \#(T \mathbin\triangle U)$ for all $U \in S$ lies in $S$) are equal. -/
theorem eq_of_code_ge {M M' : Lat ℚ n} (hM : IsGMaximal (sosQ n) M) (hM' : IsGMaximal (sosQ n) M')
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1) (hZ' : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M'.1)
    (S : Finset (Finset (Fin n))) (hS : ∀ T : Finset (Fin n), 4 ∣ T.card → (∀ U ∈ S, 4 ∣ (symmDiff T U).card) → T ∈ S)
    (hSM : ∀ U ∈ S, InCode M.1 U) (hSM' : ∀ U ∈ S, InCode M'.1 U) : IsIsometric (sosQ n) M.1 M'.1 := by
  have hN := intNorm_of_isGMaximal hM
  have hN' := intNorm_of_isGMaximal hM'
  refine image_eq_of_le hM hN' (orthGroup (sosQ n) ℚ).one_mem ?_
  rw [glImage_one]
  intro y hy
  have hT : oddSet y ∈ S := hS _ (four_dvd_card_oddSet hN hZ hy) fun U hU =>
    ((InCode.symmDiff hN hZ ⟨y, hy, rfl⟩ (hSM U hU))).four_dvd hN hZ
  exact mem_of_inCode hN' hZ' (hSM' _ hT) (isHalfInt_of_mem hN hZ hy) rfl

/-! ### Transport by permutations -/

theorem intVec_le_image_perm {M : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M) (σ : Equiv.Perm (Fin n)) :
    (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ glImage (permGL σ) M := by
  intro z hz
  refine ⟨z ∘ σ.symm, hZ ?_, ?_⟩
  · rw [mem_intVec_iff_int] at hz ⊢
    exact fun i => hz (σ.symm i)
  · change (permGL σ).val *ᵥ (z ∘ σ.symm) = z
    rw [permGL_mulVec]; funext i; simp

theorem inCode_image_perm {M : Submodule (𝓞 ℚ) (Fin n → ℚ)} (σ : Equiv.Perm (Fin n)) {T : Finset (Fin n)}
    (hT : InCode M (T.map σ.toEmbedding)) : InCode (glImage (permGL σ) M) T := by
  obtain ⟨y, hy, hyT⟩ := hT
  refine ⟨y ∘ σ, ⟨y, hy, permGL_mulVec σ y⟩, ?_⟩
  ext i
  rw [mem_oddSet_comp, hyT]
  simp

/-- **Permutations from labels**: if two labellings $f, g$ of a finite set have fibres of equal sizes, then
$f \circ \sigma = g$ for a permutation $\sigma$. -/
theorem exists_perm_of_fiber {α β : Type*} [Fintype α] [DecidableEq β] (f g : α → β)
    (hf : ∀ x, (Finset.univ.filter fun y => f y = f x).card = (Finset.univ.filter fun y => g y = f x).card)
    (hg : ∀ x, (Finset.univ.filter fun y => f y = g x).card = (Finset.univ.filter fun y => g y = g x).card) :
    ∃ σ : Equiv.Perm α, ∀ x, f (σ x) = g x := by
  have hb : ∀ b, Fintype.card {x // g x = b} = Fintype.card {x // f x = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases h1 : ∃ x, f x = b
    · obtain ⟨x, rfl⟩ := h1; exact (hf x).symm
    by_cases h2 : ∃ x, g x = b
    · obtain ⟨x, rfl⟩ := h2; exact hg x |>.symm
    push Not at h1 h2
    rw [Finset.card_eq_zero.mpr, Finset.card_eq_zero.mpr]
    · exact Finset.filter_eq_empty_iff.mpr fun x _ => h1 x
    · exact Finset.filter_eq_empty_iff.mpr fun x _ => h2 x
  let e : ∀ b, {x // g x = b} ≃ {x // f x = b} := fun b => Fintype.equivOfCardEq (hb b)
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)),
    fun x => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.sigmaCongrRight_apply]
  exact (e (g x) ⟨x, rfl⟩).2

/-- The label of $x$ with respect to a list of sets: which of them contain $x$. -/
def lab (l : List (Finset (Fin n))) (x : Fin n) : List Bool := l.map fun T => decide (x ∈ T)

/-- **Labels determine images**: if $\operatorname{lab}_l(\sigma x) = \operatorname{lab}_{l_0}(x)$ for all $x$, then
$\sigma$ maps the $k$-th set of $l_0$ onto the $k$-th set of $l$. -/
theorem map_eq_of_lab {l l0 : List (Finset (Fin n))} {σ : Equiv.Perm (Fin n)} (h : ∀ x, lab l (σ x) = lab l0 x)
    (k : ℕ) (hk : k < l.length) (hk0 : k < l0.length) : (l0[k]).map σ.toEmbedding = l[k] := by
  have hx : ∀ x, (σ x ∈ l[k]) ↔ x ∈ l0[k] := by
    intro x
    have := congrArg (fun L : List Bool => L[k]?) (h x)
    simp only [lab, List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk0,
      Option.map_some, Option.some.injEq, decide_eq_decide] at this
    exact this
  ext y
  rw [Finset.mem_map_equiv]
  have := hx (σ.symm y)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

end QuadFormsKB.Shimura2004
