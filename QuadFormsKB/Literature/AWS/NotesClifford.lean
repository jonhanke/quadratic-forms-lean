/-
# Hanke, Arizona Winter School 2009 notes, §3.2: Clifford algebras are central simple (Thm 3.2.4)

J. Hanke, *Quadratic Forms and Automorphic Forms*, notes from the 2009 Arizona Winter School,
arXiv:1105.5759 v3 (bibkey `hanke2011aws`), §3.2, Theorem 3.2.4, p. 47.

**Proves.** For a non-degenerate quadratic space $(V,Q)$ of finite dimension $n$ over a field $K$ with
$2 \in K^\times$: $C(V)$ (Mathlib's `CliffordAlgebra Q`) is a central simple $K$-algebra when $n$ is even
(`theorem_3_2_4_even`), and $C_0(V)$ (`CliffordAlgebra.even Q`) is a central simple $K$-algebra when $n$ is odd
(`theorem_3_2_4_odd`). Unconditional.

**Method.** No dimension count or tensor decomposition is used. With an orthogonal basis $e_0,\dots,e_{n-1}$ of
anisotropic vectors, write $u_j = \iota(e_j)$ and $w_\ell = u_{\ell_1}\cdots u_{\ell_r}$ for a word $\ell$.
Conjugation by a vector, or by a product $u_iu_j$, acts diagonally on words (by a sign
$(-1)^{|\ell| + \#_j\ell}$, resp. $(-1)^{\#_i\ell + \#_j\ell}$), so averaging projectors
$\tfrac12(1 \pm R)$ split any element into joint eigencomponents.
A joint eigencomponent is spanned by words that all have the same parity of letter counts, hence by a single word
up to scalars (O'Meara 54:4 machinery, `OMeara.Cl54`). This gives both centrality (the eigencomponent must be
a scalar) and simplicity (a nonzero eigencomponent of an ideal is a unit multiple of an invertible word).

Indices are 0-based (`Fin n`).
-/
import QuadFormsKB.Literature.OMeara.Sec54
import QuadFormsKB.Literature.OMeara.Sec54Dim

open CliffordAlgebra QuadFormsKB.OMeara QuadFormsKB.OMeara.Cl54

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.AWS.Notes

/-! Helper lemmas live in `Cliff324` to keep names globally unique. -/
namespace Cliff324

section Words

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {n : ℕ} (e : Module.Basis (Fin n) F V)

/-- The span of the basis words $w_\ell$ with $\ell$ satisfying a predicate `A`. -/
def WS (A : List (Fin n) → Prop) : Submodule F (CliffordAlgebra Q) :=
  Submodule.span F {w | ∃ l, A l ∧ bw Q e l = w}

theorem WS_mono {A B : List (Fin n) → Prop} (h : ∀ l, A l → B l) : WS Q e A ≤ WS Q e B :=
  Submodule.span_mono (by rintro _ ⟨l, hl, rfl⟩; exact ⟨l, h l hl, rfl⟩)

theorem mem_WS_true (g : CliffordAlgebra Q) : g ∈ WS Q e (fun _ => True) := by
  refine Submodule.span_mono ?_ (mem_span_bw Q e g)
  rintro _ ⟨l, rfl⟩
  exact ⟨l, trivial, rfl⟩

/-- The projector $\tfrac12(1 + (-1)^k R)$, for an operator $R$ acting on each word by the sign $(-1)^{m(\ell)}$,
maps $\mathrm{span}\{w_\ell : A(\ell)\}$ into $\mathrm{span}\{w_\ell : A(\ell),\ m(\ell) + k \text{ even}\}$. -/
theorem proj_mem (R : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q) (m : List (Fin n) → ℕ)
    (hR : ∀ l, R (bw Q e l) = (-1 : F) ^ m l • bw Q e l) (k : ℕ)
    {A : List (Fin n) → Prop} {z : CliffordAlgebra Q} (hz : z ∈ WS Q e A) :
    (1 / 2 : F) • (z + (-1 : F) ^ k • R z) ∈ WS Q e (fun l => A l ∧ Even (m l + k)) := by
  let P : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q :=
    (1 / 2 : F) • (LinearMap.id + (-1 : F) ^ k • R)
  have hP : ∀ l, P (bw Q e l) = if Even (m l + k) then bw Q e l else 0 := by
    intro l
    have h0 : P (bw Q e l) = (1 / 2 : F) • (bw Q e l + (-1 : F) ^ k • R (bw Q e l)) := rfl
    rw [h0, hR, smul_smul, ← pow_add, show k + m l = m l + k by ring]
    split_ifs with h
    · rw [h.neg_one_pow, one_smul, ← two_smul F, smul_smul]
      have : (2 : F) ≠ 0 := two_ne_zero
      field_simp
      simp
    · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow, neg_one_smul, add_neg_cancel, smul_zero]
  have hmem : P z ∈ (WS Q e A).map P := Submodule.mem_map_of_mem hz
  rw [WS, Submodule.map_span] at hmem
  have key : P z ∈ WS Q e (fun l => A l ∧ Even (m l + k)) := by
    refine (Submodule.span_le (p := WS Q e (fun l => A l ∧ Even (m l + k)))).mpr ?_ hmem
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hP]
    split_ifs with h
    · exact Submodule.subset_span ⟨l, ⟨hl, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  exact key

/-- A joint eigenvector of commuting-type operators $R_i$ (acting by signs on words) with eigenvalues
$(-1)^{k_i}$ lies in the span of the words with matching sign pattern. -/
theorem eigen_mem {ι : Type*} [DecidableEq ι] (R : ι → CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q)
    (m : ι → List (Fin n) → ℕ) (hR : ∀ i l, R i (bw Q e l) = (-1 : F) ^ m i l • bw Q e l)
    (k : ι → ℕ) {g : CliffordAlgebra Q} (hg : ∀ i, R i g = (-1 : F) ^ k i • g)
    {A : List (Fin n) → Prop} (hA : g ∈ WS Q e A) (s : Finset ι) :
    g ∈ WS Q e (fun l => A l ∧ ∀ i ∈ s, Even (m i l + k i)) := by
  induction s using Finset.induction_on with
  | empty => exact WS_mono Q e (fun l hl => ⟨hl, by simp⟩) hA
  | insert j s hj ih =>
    have h := proj_mem Q e (R j) (m j) (hR j) (k j) ih
    have h1 : ((-1 : F) ^ k j * (-1) ^ k j) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hgj : (1 / 2 : F) • (g + (-1 : F) ^ k j • R j g) = g := by
      rw [hg, smul_smul, h1, one_smul, ← two_smul F, smul_smul]
      have : (2 : F) ≠ 0 := two_ne_zero
      field_simp
      simp
    rw [hgj] at h
    refine WS_mono Q e (fun l hl => ⟨hl.1.1, fun i hi => ?_⟩) h
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hl.2
    · exact hl.1.2 i hi'

/-- **Pattern extraction.** A nonzero element $y$ of an $F$-subspace $J$ stable under the operators $R_i$ has a
nonzero joint-eigencomponent in $J$, lying in the span of the words of one fixed sign pattern. -/
theorem exists_pattern {ι : Type*} [DecidableEq ι] (R : ι → CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q)
    (m : ι → List (Fin n) → ℕ) (hR : ∀ i l, R i (bw Q e l) = (-1 : F) ^ m i l • bw Q e l)
    (J : Submodule F (CliffordAlgebra Q)) (hJ : ∀ i, ∀ z ∈ J, R i z ∈ J)
    {A : List (Fin n) → Prop} {y : CliffordAlgebra Q} (hy : y ∈ J) (hy0 : y ≠ 0) (hyA : y ∈ WS Q e A)
    (s : Finset ι) :
    ∃ k : ι → ℕ, ∃ y' ∈ J, y' ≠ 0 ∧ y' ∈ WS Q e (fun l => A l ∧ ∀ i ∈ s, Even (m i l + k i)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, y, hy, hy0, WS_mono Q e (fun l hl => ⟨hl, by simp⟩) hyA⟩
  | insert j s hj ih =>
    obtain ⟨k, y', hy'J, hy'0, hy'W⟩ := ih
    have key : ∀ v : ℕ, (1 / 2 : F) • (y' + (-1 : F) ^ v • R j y') ≠ 0 →
        ∃ k' : ι → ℕ, ∃ y'' ∈ J, y'' ≠ 0 ∧
          y'' ∈ WS Q e (fun l => A l ∧ ∀ i ∈ insert j s, Even (m i l + k' i)) := by
      intro v hv
      refine ⟨Function.update k j v, _, ?_, hv, ?_⟩
      · exact J.smul_mem _ (J.add_mem hy'J (J.smul_mem _ (hJ j _ hy'J)))
      · have h := proj_mem Q e (R j) (m j) (hR j) v hy'W
        refine WS_mono Q e (fun l hl => ⟨hl.1.1, fun i hi => ?_⟩) h
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · simpa using hl.2
        · have hne : i ≠ j := fun h => hj (h ▸ hi')
          simpa [Function.update_of_ne hne] using hl.1.2 i hi'
    by_cases ha : (1 / 2 : F) • (y' + (-1 : F) ^ 0 • R j y') = 0
    · refine key 1 fun hb => hy'0 ?_
      have hsum : y' = (1 / 2 : F) • (y' + (-1 : F) ^ 0 • R j y') +
          (1 / 2 : F) • (y' + (-1 : F) ^ 1 • R j y') := by
        have h2 : (2 : F) ≠ 0 := two_ne_zero
        simp only [pow_zero, pow_one]
        match_scalars <;> field_simp <;> ring
      rw [hsum, ha, hb, zero_add]
    · exact key 0 ha

theorem WS_le_range {A : List (Fin n) → Prop}
    (h : ∀ l, A l → bw Q e l ∈ Set.range (algebraMap F (CliffordAlgebra Q))) :
    WS Q e A ≤ LinearMap.range (Algebra.linearMap F (CliffordAlgebra Q)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨c, hc⟩ := h l hl
  exact ⟨c, hc⟩

theorem sum_count (l : List (Fin n)) : ∑ j : Fin n, l.count j = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem arith_even (hn : Even n) (d : Fin n → ℕ) (t : ℕ) (h : ∀ j, Even (t + d j))
    (hs : ∑ j, d j = t) : ∀ j, Even (d j) := by
  have h1 : ∀ j, d j % 2 = t % 2 := fun j => by have := Nat.even_iff.mp (h j); omega
  have h2 : t % 2 = 0 := by
    have h3 := Finset.sum_nat_mod Finset.univ 2 d
    have h4 : ∑ i, d i % 2 = ∑ _i : Fin n, t % 2 := Finset.sum_congr rfl fun i _ => h1 i
    rw [hs, h4] at h3
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
    obtain ⟨a, rfl⟩ := hn
    rcases Nat.mod_two_eq_zero_or_one t with h0 | h0
    · exact h0
    · rw [h0] at h3; omega
  intro j
  rw [Nat.even_iff]
  have := h1 j
  omega

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem arith_odd (hn : Odd n) (d : Fin n → ℕ) (h : ∀ i j, Even (d i + d j))
    (hs : Even (∑ j, d j)) : ∀ j, Even (d j) := by
  intro j
  have h1 : ∀ i, d i % 2 = d j % 2 := fun i => by have := Nat.even_iff.mp (h i j); omega
  have h3 := Finset.sum_nat_mod Finset.univ 2 d
  have h4 : ∑ i, d i % 2 = ∑ _i : Fin n, d j % 2 := Finset.sum_congr rfl fun i _ => h1 i
  have hs' := Nat.even_iff.mp hs
  rw [h4] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  obtain ⟨a, rfl⟩ := hn
  rw [Nat.even_iff]
  rcases Nat.mod_two_eq_zero_or_one (d j) with h0 | h0
  · exact h0
  · rw [h0] at h3; omega

/-- Two words with the same sign pattern for all single-vector conjugations have letter counts of equal parity
(for $n$ even). -/
theorem same_class_even (hn : Even n) (l l0 : List (Fin n)) (k : Fin n → ℕ)
    (hl : ∀ j, Even (l.length + l.count j + k j)) (hl0 : ∀ j, Even (l0.length + l0.count j + k j)) :
    ∀ j, Even (l.count j + l0.count j) := by
  refine arith_even hn (fun j => l.count j + l0.count j) (l.length + l0.length) (fun j => ?_) ?_
  · have a := Nat.even_iff.mp (hl j)
    have b := Nat.even_iff.mp (hl0 j)
    rw [Nat.even_iff]; omega
  · simp only [Finset.sum_add_distrib, sum_count]

/-- Two even-length words with the same sign pattern for all conjugations by $u_iu_j$ have letter counts of equal
parity (for $n$ odd). -/
theorem same_class_odd (hn : Odd n) (l l0 : List (Fin n)) (hlen : Even l.length) (hlen0 : Even l0.length)
    (k : Fin n × Fin n → ℕ)
    (hl : ∀ p, Even ((l.length + l.count p.1) + (l.length + l.count p.2) + k p))
    (hl0 : ∀ p, Even ((l0.length + l0.count p.1) + (l0.length + l0.count p.2) + k p)) :
    ∀ j, Even (l.count j + l0.count j) := by
  refine arith_odd hn (fun j => l.count j + l0.count j) (fun i j => ?_) ?_
  · have a := Nat.even_iff.mp (hl (i, j))
    have b := Nat.even_iff.mp (hl0 (i, j))
    rw [Nat.even_iff]; simp only at a b ⊢; omega
  · simp only [Finset.sum_add_distrib, sum_count]
    exact Even.add hlen hlen0

end Words

section Ops

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {n : ℕ} (e : Module.Basis (Fin n) F V)

/-- The linear map $z \mapsto c\,(a z b)$. -/
def conjOp (a b : CliffordAlgebra Q) (c : F) : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q :=
  c • (LinearMap.mulLeft F a ∘ₗ LinearMap.mulRight F b)

theorem conjOp_apply (a b : CliffordAlgebra Q) (c : F) (z : CliffordAlgebra Q) :
    conjOp Q a b c z = c • (a * (z * b)) := rfl

theorem conjOp_comm (a b : CliffordAlgebra Q) (c r : F) (g : CliffordAlgebra Q) (hg : a * g = g * a)
    (hab : a * b = algebraMap F _ r) (hc : c * r = 1) : conjOp Q a b c g = g := by
  rw [conjOp_apply, ← mul_assoc, hg, mul_assoc, hab, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, hc,
    one_smul]

/-- Conjugation by the basis vector $u_j$, normalised by $Q(e_j)^{-1}$. -/
def R1 (j : Fin n) : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q :=
  conjOp Q (ub Q e j) (ub Q e j) (Q (e j))⁻¹

/-- Conjugation by $u_iu_j$, normalised by $(Q(e_i)Q(e_j))^{-1}$. -/
def R2 (p : Fin n × Fin n) : CliffordAlgebra Q →ₗ[F] CliffordAlgebra Q :=
  conjOp Q (ub Q e p.1 * ub Q e p.2) (ub Q e p.2 * ub Q e p.1) (Q (e p.1) * Q (e p.2))⁻¹

theorem ub_conj_bw (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0) (j : Fin n)
    (l : List (Fin n)) :
    ub Q e j * (bw Q e l * ub Q e j) = ((-1 : F) ^ (l.length + l.count j) * Q (e j)) • bw Q e l := by
  rw [← mul_assoc, ub_mul_bw Q e he hea, smul_mul_assoc, mul_assoc, ι_sq_scalar, ← Algebra.commutes,
    ← Algebra.smul_def, smul_smul]

theorem R1_bw (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0) (j : Fin n)
    (l : List (Fin n)) :
    R1 Q e j (bw Q e l) = (-1 : F) ^ (l.length + l.count j) • bw Q e l := by
  rw [R1, conjOp_apply, ub_conj_bw Q e he hea, smul_smul, mul_left_comm, inv_mul_cancel₀ (hea j), mul_one]

theorem R2_bw (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0) (p : Fin n × Fin n)
    (l : List (Fin n)) :
    R2 Q e p (bw Q e l) =
      (-1 : F) ^ ((l.length + l.count p.1) + (l.length + l.count p.2)) • bw Q e l := by
  rw [R2, conjOp_apply]
  have h : (ub Q e p.1 * ub Q e p.2) * (bw Q e l * (ub Q e p.2 * ub Q e p.1)) =
      ((-1 : F) ^ (l.length + l.count p.2) * Q (e p.2)) •
        (((-1 : F) ^ (l.length + l.count p.1) * Q (e p.1)) • bw Q e l) := by
    have e1 : (ub Q e p.1 * ub Q e p.2) * (bw Q e l * (ub Q e p.2 * ub Q e p.1)) =
        ub Q e p.1 * ((ub Q e p.2 * (bw Q e l * ub Q e p.2)) * ub Q e p.1) := by simp only [mul_assoc]
    rw [e1, ub_conj_bw Q e he hea p.2, smul_mul_assoc, mul_smul_comm, ub_conj_bw Q e he hea p.1]
  rw [h, smul_smul, smul_smul]
  congr 1
  have h1 := hea p.1
  have h2 := hea p.2
  rw [pow_add (-1 : F) (l.length + l.count p.1)]
  field_simp

end Ops

section Main

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {n : ℕ} (e : Module.Basis (Fin n) F V)

theorem ub_pair_mul (i j : Fin n) :
    ub Q e i * ub Q e j * (ub Q e j * ub Q e i) = algebraMap F (CliffordAlgebra Q) (Q (e i) * Q (e j)) := by
  rw [mul_assoc, ← mul_assoc (ub Q e j), ι_sq_scalar, Algebra.commutes, ← mul_assoc, ι_sq_scalar, ← map_mul]

/-- **A word times its reverse is a nonzero scalar** (the word is invertible). -/
theorem bw_rev_mul (hea : ∀ i, Q (e i) ≠ 0) (l : List (Fin n)) :
    ∃ b : F, b ≠ 0 ∧ bw Q e l.reverse * bw Q e l = algebraMap F (CliffordAlgebra Q) b := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, by simp [bw_nil]⟩
  | cons i l ih =>
    obtain ⟨b, hb0, hb⟩ := ih
    refine ⟨Q (e i) * b, mul_ne_zero (hea i) hb0, ?_⟩
    simp only [List.reverse_cons, bw_append, bw_cons, bw_nil, mul_one]
    rw [mul_assoc, ← mul_assoc (ub Q e i) (ub Q e i), ι_sq_scalar, ← mul_assoc, ← Algebra.commutes,
      mul_assoc, hb, ← map_mul]

/-- **Words with letter counts of the same parity are proportional.** -/
theorem bw_eq_smul (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0)
    (l l0 : List (Fin n)) (hd : ∀ j, Even (l.count j + l0.count j)) :
    ∃ c : F, bw Q e l = c • bw Q e l0 := by
  obtain ⟨a, ha⟩ := bw_mem_range_of_even Q e he hea (l ++ l0.reverse) (fun j => by
    simpa [List.count_append, List.count_reverse] using hd j)
  obtain ⟨b, hb0, hb⟩ := bw_rev_mul Q e hea l0
  have h1 : bw Q e l * algebraMap F (CliffordAlgebra Q) b = algebraMap F (CliffordAlgebra Q) a * bw Q e l0 := by
    rw [← hb, ← mul_assoc, ← bw_append, ← ha]
  have h2 : b • bw Q e l = a • bw Q e l0 := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.commutes, h1]
  refine ⟨a / b, ?_⟩
  rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hb0, one_smul]

/-- A word of even length lies in the even subalgebra $C_0$. -/
theorem bw_mem_even (l : List (Fin n)) (hl : Even l.length) : bw Q e l ∈ CliffordAlgebra.even Q := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    match l, hl with
    | [], _ => simp [bw_nil]
    | [i], hl => simp at hl
    | i :: j :: l', hl =>
      have h2 : Even l'.length := by
        have h3 : Even (l'.length + 2) := by simpa using hl
        exact (Nat.even_add.mp h3).mpr even_two
      have h4 := ih l'.length (by rw [← h]; simp) l' h2 rfl
      have h5 : bw Q e (i :: j :: l') = (ub Q e i * ub Q e j) * bw Q e l' := by
        simp only [bw_cons, mul_assoc]
      rw [h5]
      exact (CliffordAlgebra.even Q).mul_mem (ι_mul_ι_mem_evenOdd_zero Q (e i) (e j)) h4

/-- **An element of $C_0$ is a combination of even-length words.** -/
theorem mem_WS_even {g : CliffordAlgebra Q} (hg : g ∈ CliffordAlgebra.even Q) :
    g ∈ WS Q e (fun l => Even l.length) := by
  classical
  have h := eigen_mem Q e (fun _ : Unit => (involute : CliffordAlgebra Q →ₐ[F] _).toLinearMap)
    (fun _ l => l.length) (fun _ l => by simpa using involute_bw Q e l) (fun _ => 0) (g := g)
    (fun _ => by simp [involute_eq_of_mem_even hg]) (mem_WS_true Q e g) Finset.univ
  exact WS_mono Q e (fun l hl => by simpa using hl.2 () (Finset.mem_univ _)) h

/-- **Centre, $n$ even:** an element of $C(V)$ commuting with every vector is a scalar. -/
theorem center_scalar_even (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0)
    (hn : Even n) (g : CliffordAlgebra Q) (hg : ∀ x : V, g * ι Q x = ι Q x * g) :
    ∃ c : F, g = algebraMap F (CliffordAlgebra Q) c := by
  classical
  have heig : ∀ j, R1 Q e j g = (-1 : F) ^ ((fun _ => 0) j) • g := fun j => by
    simp only [pow_zero, one_smul]
    exact conjOp_comm Q _ _ _ (Q (e j)) g (hg (e j)).symm (ι_sq_scalar Q (e j)) (inv_mul_cancel₀ (hea j))
  have hW := eigen_mem Q e (R1 Q e) (fun j l => l.length + l.count j) (R1_bw Q e he hea) (fun _ => 0)
    (g := g) heig (mem_WS_true Q e g) Finset.univ
  have hbw : ∀ l, (True ∧ ∀ i ∈ (Finset.univ : Finset (Fin n)), Even (l.length + l.count i + 0)) →
      bw Q e l ∈ Set.range (algebraMap F (CliffordAlgebra Q)) := by
    intro l hl
    have hc := arith_even hn (fun j => l.count j) l.length
      (fun j => by simpa using hl.2 j (Finset.mem_univ j)) (sum_count l)
    exact bw_mem_range_of_even Q e he hea l hc
  obtain ⟨c, hc⟩ := WS_le_range Q e hbw hW
  exact ⟨c, hc.symm⟩

/-- **Centre of $C_0$, $n$ odd:** an even element commuting with every $u_iu_j$ is a scalar. -/
theorem center_scalar_odd (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0)
    (hn : Odd n) (g : CliffordAlgebra Q) (hg : g ∈ CliffordAlgebra.even Q)
    (hc : ∀ i j, (ub Q e i * ub Q e j) * g = g * (ub Q e i * ub Q e j)) :
    ∃ c : F, g = algebraMap F (CliffordAlgebra Q) c := by
  classical
  have heig : ∀ p, R2 Q e p g = (-1 : F) ^ ((fun _ => 0) p) • g := fun p => by
    simp only [pow_zero, one_smul]
    exact conjOp_comm Q _ _ _ (Q (e p.1) * Q (e p.2)) g (hc p.1 p.2) (ub_pair_mul Q e p.1 p.2)
      (inv_mul_cancel₀ (mul_ne_zero (hea p.1) (hea p.2)))
  have hW := eigen_mem Q e (R2 Q e) (fun p l => (l.length + l.count p.1) + (l.length + l.count p.2))
    (R2_bw Q e he hea) (fun _ => 0) (g := g) heig (mem_WS_even Q e hg) Finset.univ
  have hbw : ∀ l, (Even l.length ∧ ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
      Even ((l.length + l.count p.1) + (l.length + l.count p.2) + 0)) →
      bw Q e l ∈ Set.range (algebraMap F (CliffordAlgebra Q)) := by
    intro l hl
    have hc := arith_odd hn (fun j => l.count j) (fun i j => by
      have h' : Even ((l.length + l.count i) + (l.length + l.count j) + 0) := hl.2 (i, j) (Finset.mem_univ _)
      have := Nat.even_iff.mp h'
      rw [Nat.even_iff]; omega) (by rw [sum_count]; exact hl.1)
    exact bw_mem_range_of_even Q e he hea l hc
  obtain ⟨c, hc⟩ := WS_le_range Q e hbw hW
  exact ⟨c, hc.symm⟩

/-- **Simplicity of $C(V)$, $n$ even.** -/
theorem isSimpleRing_of_even [Nontrivial (CliffordAlgebra Q)]
    (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0) (hn : Even n) :
    IsSimpleRing (CliffordAlgebra Q) := by
  classical
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  rw [← TwoSidedIdeal.one_mem_iff]
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (TwoSidedIdeal.ext fun x => by
      rw [TwoSidedIdeal.mem_bot]; exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩)
  let J : Submodule F (CliffordAlgebra Q) :=
    { carrier := {x | x ∈ I}
      add_mem' := fun {_ _} ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c x hx => by
        rw [Algebra.smul_def]; exact I.mul_mem_left _ _ hx }
  have hJR : ∀ j, ∀ z ∈ J, R1 Q e j z ∈ J := fun j z hz => by
    rw [R1, conjOp_apply]
    exact J.smul_mem _ (I.mul_mem_left _ _ (I.mul_mem_right _ _ hz))
  obtain ⟨k, y', hy'J, hy'0, hy'W⟩ := exists_pattern Q e (R1 Q e) (fun j l => l.length + l.count j)
    (R1_bw Q e he hea) J hJR (A := fun _ => True) (y := y) hyI hy0 (mem_WS_true Q e y) Finset.univ
  have hex : ∃ l0 : List (Fin n), ∀ j, Even (l0.length + l0.count j + k j) := by
    by_contra hne
    apply hy'0
    have hle : WS Q e (fun l => True ∧ ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Even (l.length + l.count i + k i)) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, hl, rfl⟩
      exact (hne ⟨l, fun j => hl.2 j (Finset.mem_univ j)⟩).elim
    exact (Submodule.mem_bot F).mp (hle hy'W)
  obtain ⟨l0, hl0⟩ := hex
  have hle : WS Q e (fun l => True ∧ ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Even (l.length + l.count i + k i)) ≤ Submodule.span F {bw Q e l0} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, hc⟩ := bw_eq_smul Q e he hea l l0
      (same_class_even hn l l0 k (fun j => hl.2 j (Finset.mem_univ j)) hl0)
    rw [SetLike.mem_coe, hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle hy'W)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy'0
    rw [← hc, zero_smul]
  have hbw0 : bw Q e l0 ∈ I := by
    have : bw Q e l0 = c⁻¹ • y' := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact J.smul_mem _ hy'J
  obtain ⟨b, hb0, hb⟩ := bw_rev_mul Q e hea l0
  have h1 : (1 : CliffordAlgebra Q) = algebraMap F _ b⁻¹ * (bw Q e l0.reverse * bw Q e l0) := by
    rw [hb, ← map_mul, inv_mul_cancel₀ hb0, map_one]
  rw [h1]
  exact I.mul_mem_left _ _ (I.mul_mem_left _ _ hbw0)

/-- **Simplicity of $C_0(V)$, $n$ odd.** -/
theorem isSimpleRing_even_of_odd [Nontrivial (CliffordAlgebra Q)]
    (he : ∀ i j, i ≠ j → bil Q (e i) (e j) = 0) (hea : ∀ i, Q (e i) ≠ 0) (hn : Odd n) :
    IsSimpleRing (CliffordAlgebra.even Q) := by
  classical
  have : Nontrivial (CliffordAlgebra.even Q) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I => ?_
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  rw [← TwoSidedIdeal.one_mem_iff]
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (TwoSidedIdeal.ext fun x => by
      rw [TwoSidedIdeal.mem_bot]; exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩)
  let J : Submodule F (CliffordAlgebra Q) :=
    { carrier := {x | ∃ a : CliffordAlgebra.even Q, a ∈ I ∧ (a : CliffordAlgebra Q) = x}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, I.add_mem ha hb, rfl⟩
      zero_mem' := ⟨0, I.zero_mem, rfl⟩
      smul_mem' := by
        rintro c _ ⟨a, ha, rfl⟩
        refine ⟨c • a, ?_, rfl⟩
        rw [Algebra.smul_def]
        exact I.mul_mem_left _ _ ha }
  have hyJ : (y : CliffordAlgebra Q) ∈ J := ⟨y, hyI, rfl⟩
  have hy0' : (y : CliffordAlgebra Q) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hJR : ∀ p, ∀ z ∈ J, R2 Q e p z ∈ J := by
    rintro p _ ⟨a, ha, rfl⟩
    let P1 : CliffordAlgebra.even Q := ⟨ub Q e p.1 * ub Q e p.2, ι_mul_ι_mem_evenOdd_zero Q _ _⟩
    let P2 : CliffordAlgebra.even Q := ⟨ub Q e p.2 * ub Q e p.1, ι_mul_ι_mem_evenOdd_zero Q _ _⟩
    refine ⟨(Q (e p.1) * Q (e p.2))⁻¹ • (P1 * (a * P2)), ?_, rfl⟩
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ (I.mul_mem_left _ _ (I.mul_mem_right _ _ ha))
  obtain ⟨k, y', hy'J, hy'0, hy'W⟩ := exists_pattern Q e (R2 Q e)
    (fun p l => (l.length + l.count p.1) + (l.length + l.count p.2))
    (R2_bw Q e he hea) J hJR hyJ hy0' (mem_WS_even Q e y.2) Finset.univ
  have hex : ∃ l0 : List (Fin n), Even l0.length ∧ ∀ p : Fin n × Fin n,
      Even ((l0.length + l0.count p.1) + (l0.length + l0.count p.2) + k p) := by
    by_contra hne
    apply hy'0
    have hle : WS Q e (fun l => Even l.length ∧ ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
        Even ((l.length + l.count p.1) + (l.length + l.count p.2) + k p)) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, hl, rfl⟩
      exact (hne ⟨l, hl.1, fun p => hl.2 p (Finset.mem_univ p)⟩).elim
    exact (Submodule.mem_bot F).mp (hle hy'W)
  obtain ⟨l0, hl0e, hl0⟩ := hex
  have hle : WS Q e (fun l => Even l.length ∧ ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)),
      Even ((l.length + l.count p.1) + (l.length + l.count p.2) + k p)) ≤
        Submodule.span F {bw Q e l0} := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨c, hc⟩ := bw_eq_smul Q e he hea l l0
      (same_class_odd hn l l0 hl.1 hl0e k (fun p => hl.2 p (Finset.mem_univ p)) hl0)
    rw [SetLike.mem_coe, hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hle hy'W)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy'0
    rw [← hc, zero_smul]
  have hbw0 : bw Q e l0 ∈ J := by
    have : bw Q e l0 = c⁻¹ • y' := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [this]
    exact J.smul_mem _ hy'J
  obtain ⟨a, haI, ha⟩ := hbw0
  obtain ⟨b, hb0, hb⟩ := bw_rev_mul Q e hea l0
  have hrev : Even l0.reverse.length := by simpa using hl0e
  let P : CliffordAlgebra.even Q := ⟨bw Q e l0.reverse, bw_mem_even Q e _ hrev⟩
  have hPa : P * a = algebraMap F (CliffordAlgebra.even Q) b := by
    apply Subtype.ext
    show bw Q e l0.reverse * (a : CliffordAlgebra Q) = algebraMap F (CliffordAlgebra Q) b
    rw [ha, hb]
  have h1 : (1 : CliffordAlgebra.even Q) = algebraMap F _ b⁻¹ * (P * a) := by
    rw [hPa, ← map_mul, inv_mul_cancel₀ hb0, map_one]
  rw [h1]
  exact I.mul_mem_left _ _ (I.mul_mem_left _ _ haI)

end Main

end Cliff324

open Cliff324

section Thm324

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (Q : QuadraticForm K V)

theorem nontrivial_cliffordAlgebra : Nontrivial (CliffordAlgebra Q) :=
  Module.nontrivial_of_finrank_pos (R := K)
    (by rw [CliffordDim.finrank_cliffordAlgebra]; positivity)

/-- **Theorem 3.2.4, even dimension** (Hanke, Arizona Winter School notes, §3.2, p. 47). Let $V$ be a finite-dimensional
quadratic space over a field $K$ in which $2$ is invertible (`Invertible (2 : K)`, i.e. $\operatorname{char} K \ne 2$),
with quadratic form $Q$ (`Q`) that is non-degenerate (`hQ`: the associated symmetric bilinear form
$B(x,y) = \tfrac12(Q(x+y)-Q(x)-Q(y))$ is non-degenerate). If $n = \dim_K V$ is even (`hn`), then the Clifford algebra
$C(V)$ (`CliffordAlgebra Q`) is a central simple $K$-algebra: its centre is $K$
(`Algebra.IsCentral K (CliffordAlgebra Q)`) and it is a simple ring (`IsSimpleRing`). For $n = 0$ this is
$C(V) = K$.

Finite-dimensionality of $C(V)$ ($\dim_K C(V) = 2^n$) is `QuadFormsKB.OMeara.CliffordDim.finrank_cliffordAlgebra`.
Unconditional; the proof is self-contained (see the file docstring), not through the tensor-product-of-quaternion-algebras
decomposition. -/
@[kb "hanke2011aws" "§3.2, Thm. 3.2.4, p. 47 (n even)"]
theorem theorem_3_2_4_even (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Even (Module.finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra Q) ∧ IsSimpleRing (CliffordAlgebra Q) := by
  have := nontrivial_cliffordAlgebra Q
  obtain ⟨e, he, hea⟩ := exists_orthogonal_anisotropic_basis Q hQ
  refine ⟨⟨fun x hx => ?_⟩, isSimpleRing_of_even Q e he hea hn⟩
  rw [Subalgebra.mem_center_iff] at hx
  obtain ⟨c, hc⟩ := center_scalar_even Q e he hea hn x (fun v => (hx (ι Q v)).symm)
  exact Algebra.mem_bot.mpr ⟨c, hc.symm⟩

/-- **Theorem 3.2.4, odd dimension** (Hanke, Arizona Winter School notes, §3.2, p. 47). Same hypotheses as `theorem_3_2_4_even`
(`Invertible (2 : K)`, finite dimension, non-degenerate `hQ`), but $n = \dim_K V$ is odd (`hn`). Then the even
Clifford algebra $C_0(V)$ (`CliffordAlgebra.even Q`, the subalgebra spanned by products of an even number of vectors)
is a central simple $K$-algebra: `Algebra.IsCentral K (CliffordAlgebra.even Q)` and `IsSimpleRing`.
Unconditional; finite-dimensionality ($\dim C_0(V) = 2^{n-1}$) is `QuadFormsKB.OMeara` `finrank_even`. -/
@[kb "hanke2011aws" "§3.2, Thm. 3.2.4, p. 47 (n odd)"]
theorem theorem_3_2_4_odd (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hn : Odd (Module.finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra.even Q) ∧ IsSimpleRing (CliffordAlgebra.even Q) := by
  have := nontrivial_cliffordAlgebra Q
  obtain ⟨e, he, hea⟩ := exists_orthogonal_anisotropic_basis Q hQ
  refine ⟨⟨fun x hx => ?_⟩, isSimpleRing_even_of_odd Q e he hea hn⟩
  rw [Subalgebra.mem_center_iff] at hx
  obtain ⟨c, hc⟩ := center_scalar_odd Q e he hea hn (x : CliffordAlgebra Q) x.2 (fun i j => by
    have := hx ⟨ub Q e i * ub Q e j, ι_mul_ι_mem_evenOdd_zero Q _ _⟩
    exact congrArg Subtype.val this)
  refine Algebra.mem_bot.mpr ⟨c, Subtype.ext ?_⟩
  exact hc.symm

end Thm324

end QuadFormsKB.AWS.Notes
