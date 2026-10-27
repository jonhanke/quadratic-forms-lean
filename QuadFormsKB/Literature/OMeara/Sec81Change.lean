/-
# O'Meara §81C: change of base

**Setting** (as in `Sec81.lean`): $R$ a Dedekind domain with fraction field $F$, $V$ a vector space over $F$,
fractional ideals are non-zero finitely generated $R$-submodules of $F$. Two lattices on $V$ are given in adapted
bases, $L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ and $K = \mathfrak b_1y_1 + \cdots + \mathfrak b_ny_n$, and the
bases are related by $y_i = \sum_j a_{ij}x_j$. Here (index shift: O'Meara's $x_1, \dots, x_n$ are
`x 0, …, x (n-1)`) the coefficient $a_{ij}$ is `x.repr (y i) j`, and the matrix $(a_{ij})$ is the transpose of
Mathlib's `x.toMatrix y` (whose $(j, i)$ entry is `x.repr (y i) j`); the two have the same determinant.

**Proves** (O'Meara 1963, §81C, pp. 213–214):
* `le_iff_of_adapted` (**81:7**): $K \subseteq L$ if and only if $a_{ij}\mathfrak b_i \subseteq \mathfrak a_j$ for all
  $i, j$;
* `eq_iff_prod_of_adapted` (**81:8**): if $K \subseteq L$ then $K = L$ if and only if
  $\mathfrak a_1 \cdots \mathfrak a_n = \mathfrak b_1 \cdots \mathfrak b_n \det(a_{ij})$;
* `span_eq_iff_unimodular` (**81:9**), `span_update_eq` (**81:10**).
-/
import QuadFormsKB.Literature.OMeara.Sec81

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Ring

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- **Proposition 81:7** (O'Meara 1963, p. 213). Let $L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ and
$K = \mathfrak b_1y_1 + \cdots + \mathfrak b_ny_n$ for bases $x$, $y$ of $V$, with $y_i = \sum_j a_{ij}x_j$. Then
$K \subseteq L$ if and only if $a_{ij}\mathfrak b_i \subseteq \mathfrak a_j$ for all $i, j$. (The OCR text of the
inclusion is garbled; it is restored from the proof: $\mathfrak b_iy_i \subseteq L$ if and only if
$\mathfrak b_i(a_{i1}x_1 + \cdots + a_{in}x_n) \subseteq \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$.) -/
@[kb "omeara1963" "§81C, 81:7, p. 213"]
theorem le_iff_of_adapted {ι : Type*} [Fintype ι] (x y : Basis ι F V) (a b : ι → Submodule R F) :
    (⨆ i, b i • span R {y i}) ≤ (⨆ i, a i • span R {x i}) ↔
      ∀ i j, span R {x.repr (y i) j} * b i ≤ a j := by
  constructor
  · intro h i j
    rw [Submodule.span_singleton_mul]
    intro t ht
    obtain ⟨β, hβ, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ht
    have h1 : β • y i ∈ ⨆ i, b i • span R {y i} :=
      Submodule.mem_iSup_of_mem i (Submodule.smul_mem_smul hβ (Submodule.mem_span_singleton_self _))
    have := (mem_iSup_smul_span_iff x a _).mp (h h1) j
    simpa [mul_comm] using this
  · intro h
    refine iSup_le fun i => (Submodule.smul_le).mpr fun β hβ n hn => ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [mem_iSup_smul_span_iff]
    intro j
    have h2 : x.repr (y i) j * β ∈ a j :=
      h i j (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hβ)
    have e : β • c • y i = (β * algebraMap R F c) • y i := by
      rw [← algebraMap_smul F c (y i), smul_smul]
    rw [e, map_smul]
    have := Submodule.smul_of_tower_mem (a j) c h2
    simp only [Finsupp.smul_apply, smul_eq_mul]
    simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using this

/-- **Example 81:10** (O'Meara 1963, p. 214). Let $v_1, \dots, v_r$ be vectors in $V$, $\varepsilon$ a unit of
$\mathfrak o$ and $\alpha_2, \dots, \alpha_r \in \mathfrak o$. Then
$\mathfrak ov_1 + \mathfrak ov_2 + \cdots + \mathfrak ov_r = \mathfrak ov_1' + \mathfrak ov_2 + \cdots + \mathfrak ov_r$
with $v_1' = \varepsilon v_1 + \alpha_2v_2 + \cdots + \alpha_rv_r$. (Here $v_1, \dots, v_r$ are `v 0, …, v r` and
$\alpha_{i+2}$ is `α i`; any commutative ring $R$.) -/
@[kb "omeara1963" "§81C, 81:10, p. 214"]
theorem span_update_eq {r : ℕ} (v : Fin (r + 1) → V) (ε : Rˣ) (α : Fin r → R) :
    span R (Set.range (Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ))) =
      span R (Set.range v) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [Function.update_self]
      refine add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.succ, rfl⟩))
    · rw [Function.update_of_ne (Fin.succ_ne_zero k)]
      exact Submodule.subset_span ⟨k.succ, rfl⟩
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · have hu : ((ε⁻¹ : Rˣ) : R) • (Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ) 0
          - ∑ i, α i • Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ) i.succ) = v 0 := by
        simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
        rw [add_sub_cancel_right, smul_smul]
        simp
      have hm : ((ε⁻¹ : Rˣ) : R) • (Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ) 0
          - ∑ i, α i • Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ) i.succ) ∈
          span R (Set.range (Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ))) :=
        Submodule.smul_mem _ _ (sub_mem (Submodule.subset_span ⟨0, rfl⟩)
          (Submodule.sum_mem _ fun (k : Fin r) _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.succ, rfl⟩)))
      rwa [hu] at hm
    · have : v k.succ = Function.update v 0 ((ε : R) • v 0 + ∑ i, α i • v i.succ) k.succ := by
        rw [Function.update_of_ne (Fin.succ_ne_zero k)]
      rw [this]
      exact Submodule.subset_span ⟨k.succ, rfl⟩

/-- Products of submodules are monotone. -/
theorem prod_le_prod_submodule {ι : Type*} (s : Finset ι) (p q : ι → Submodule R F)
    (h : ∀ i, p i ≤ q i) : ∏ i ∈ s, p i ≤ ∏ i ∈ s, q i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul' (h a) ih

/-- Leibniz bound for determinants against products of submodules. -/
theorem span_det_mul_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι F)
    (c d : ι → Submodule R F) (h : ∀ k l, span R {N k l} * d k ≤ c l) :
    span R {N.det} * ∏ k, d k ≤ ∏ l, c l := by
  rw [Submodule.span_singleton_mul]
  intro t ht
  obtain ⟨s, hs, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ht
  rw [Matrix.det_apply, Finset.sum_smul]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h1 : (∏ k, N (σ k) k) • s ∈ ∏ l, c l := by
    have hd : ∏ k, d (σ k) = ∏ k, d k := Equiv.prod_comp σ d
    have hs' : s ∈ ∏ k, d (σ k) := by rw [hd]; exact hs
    have h2 : span R {∏ k, N (σ k) k} * ∏ k, d (σ k) ≤ ∏ l, c l := by
      rw [← Submodule.prod_span_singleton, ← Finset.prod_mul_distrib]
      exact prod_le_prod_submodule _ _ _ fun k => h (σ k) k
    exact h2 (by simpa using Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hs')
  rw [smul_assoc, Units.smul_def]
  exact zsmul_mem h1 _

/-- Coordinates of a vector in `span R (range x)` for a base `x` of `V` are integral, and conversely. -/
theorem mem_span_range_iff_integral {ι : Type*} [Fintype ι] (x : Basis ι F V) (v : V) :
    v ∈ span R (Set.range x) ↔ ∀ i, x.repr v i ∈ (algebraMap R F).range := by
  classical
  constructor
  · intro hv
    refine span_induction (p := fun v _ => ∀ i, x.repr v i ∈ (algebraMap R F).range) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩ i
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      exacts [⟨1, map_one _⟩, ⟨0, map_zero _⟩]
    · intro i; simp
    · intro a b _ _ ha hb i
      rw [map_add, Finsupp.add_apply]; exact add_mem (ha i) (hb i)
    · intro r a _ ha i
      rw [← algebraMap_smul F r a, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨r, rfl⟩ (ha i)
  · intro h
    rw [← x.sum_repr v]
    refine sum_mem fun i _ => ?_
    obtain ⟨r, hr⟩ := h i
    rw [← hr, algebraMap_smul]
    exact smul_mem _ _ (subset_span ⟨i, rfl⟩)

end Ring

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]


/-- A finite product of non-zero finitely generated submodules of `F` is such. -/
theorem prod_fg_ne_bot {ι : Type*} (s : Finset ι) (p : ι → Submodule R F)
    (h : ∀ i, (p i).FG ∧ p i ≠ ⊥) : (∏ i ∈ s, p i).FG ∧ ∏ i ∈ s, p i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.one_eq_span, Submodule.fg_span_singleton]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine ⟨(h a).1.mul ih.1, ?_⟩
    rw [← Submodule.zero_eq_bot] at *
    exact mul_ne_zero (h a).2 ih.2

/-- **Proposition 81:8** (O'Meara 1963, pp. 213–214). Let $L = \mathfrak a_1x_1 + \cdots + \mathfrak a_nx_n$ and
$K = \mathfrak b_1y_1 + \cdots + \mathfrak b_ny_n$ with fractional ideals $\mathfrak a_i, \mathfrak b_i$ and bases
related by $y_i = \sum_j a_{ij}x_j$, and suppose $K \subseteq L$. Then $K = L$ if and only if
$\mathfrak a_1 \cdots \mathfrak a_n = \mathfrak b_1 \cdots \mathfrak b_n \det(a_{ij})$. (O'Meara assumes all
$\mathfrak a_i, \mathfrak b_i$ are fractional ideals; the proof only needs this for the $\mathfrak b_i$, so the
$\mathfrak a_i$ are arbitrary $R$-submodules of $F$ here.) -/
@[kb "omeara1963" "§81C, 81:8, pp. 213–214"]
theorem eq_iff_prod_of_adapted {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : Basis ι F V)
    (a b : ι → Submodule R F) (hb : ∀ i, (b i).FG ∧ b i ≠ ⊥)
    (hKL : (⨆ i, b i • span R {y i}) ≤ (⨆ i, a i • span R {x i})) :
    (⨆ i, b i • span R {y i}) = (⨆ i, a i • span R {x i}) ↔
      ∏ i, a i = (∏ i, b i) * span R {(x.toMatrix y).det} := by
  classical
  set A : Matrix ι ι F := Matrix.transpose (x.toMatrix y) with hA
  set B : Matrix ι ι F := Matrix.transpose (y.toMatrix x) with hB
  have hAij : ∀ i j, A i j = x.repr (y i) j := fun i j => by
    simp [hA, Basis.toMatrix_apply]
  have hBij : ∀ i j, B i j = y.repr (x i) j := fun i j => by
    simp [hB, Basis.toMatrix_apply]
  have hAB : A * B = 1 := by
    rw [hA, hB, ← Matrix.transpose_mul, Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self,
      Matrix.transpose_one]
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hdetA : A.det = (x.toMatrix y).det := Matrix.det_transpose _
  have hdetne : A.det ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hadj : A.adjugate = A.det • B := by
    calc A.adjugate = A.adjugate * (A * B) := by rw [hAB, mul_one]
      _ = (A.adjugate * A) * B := by rw [mul_assoc]
      _ = A.det • B := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  have hBadj : ∀ i j, B i j = (A.det)⁻¹ * A.adjugate i j := fun i j => by
    rw [hadj]; simp [hdetne]
  have hle1 := le_iff_of_adapted x y a b
  rw [← hdetA]
  have hle2' := le_iff_of_adapted y x b a
  have h1 : ∀ i j, span R {A i j} * b i ≤ a j := by
    intro i j; rw [hAij]; exact hle1.mp hKL i j
  constructor
  · intro heq
    have h2 : ∀ i j, span R {B i j} * a i ≤ b j := by
      intro i j; rw [hBij]; exact hle2'.mp heq.ge i j
    have l1 := span_det_mul_prod_le A a b h1
    have l2 := span_det_mul_prod_le B b a h2
    apply le_antisymm
    · calc ∏ i, a i = span R {A.det * B.det} * ∏ i, a i := by
            rw [hdet, ← Submodule.one_eq_span, one_mul]
        _ = span R {A.det} * (span R {B.det} * ∏ i, a i) := by
            rw [← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton]
        _ ≤ span R {A.det} * ∏ i, b i := mul_le_mul' le_rfl l2
        _ = (∏ i, b i) * span R {A.det} := mul_comm _ _
    · rw [mul_comm]; exact l1
  · intro hprod
    refine le_antisymm hKL ?_
    rw [hle2']
    intro i j
    rw [← hBij]
    obtain ⟨hPfg, hPne⟩ := prod_fg_ne_bot (Finset.univ.erase j) b hb
    set P : Submodule R F := ∏ k ∈ Finset.univ.erase j, b k with hP
    have hPinv := mul_one_div_cancel_of_fg hPfg hPne
    let N : Matrix ι ι F := A.updateRow j (Pi.single i 1)
    let d : ι → Submodule R F := Function.update b j (a i)
    have hN : ∀ k l, span R {N k l} * d k ≤ a l := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [N, d, Matrix.updateRow_self, Function.update_self]
        by_cases hl : l = i
        · subst hl; simp; rw [← Submodule.one_eq_span, one_mul]
        · simp [hl]
      · simp only [N, d, Matrix.updateRow_ne hk, Function.update_of_ne hk]
        exact h1 k l
    have key := span_det_mul_prod_le N a d hN
    have hdprod : ∏ k, d k = a i * P := by
      rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ j)]
      congr 1
      · simp [d]
      · exact Finset.prod_congr rfl fun k hk => by simp [d, Finset.ne_of_mem_erase hk]
    have hbprod : ∏ k, b k = b j * P := (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm
    have hNdet : N.det = A.adjugate i j := by rw [Matrix.adjugate_apply]
    rw [hNdet, hdprod, ← mul_assoc, hprod, hbprod] at key
    have key2 : span R {A.adjugate i j} * a i ≤ b j * span R {A.det} := by
      have h3 := mul_le_mul' key (le_refl (1 / P))
      calc span R {A.adjugate i j} * a i = span R {A.adjugate i j} * a i * (P * (1 / P)) := by
            rw [hPinv, mul_one]
        _ = span R {A.adjugate i j} * a i * P * (1 / P) := by ring
        _ ≤ b j * P * span R {A.det} * (1 / P) := h3
        _ = b j * span R {A.det} * (P * (1 / P)) := by ring
        _ = b j * span R {A.det} := by rw [hPinv, mul_one]
    calc span R {B i j} * a i
        = span R {(A.det)⁻¹} * (span R {A.adjugate i j} * a i) := by
          rw [hBadj, ← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton]
      _ ≤ span R {(A.det)⁻¹} * (b j * span R {A.det}) := mul_le_mul' le_rfl key2
      _ = b j * (span R {(A.det)⁻¹} * span R {A.det}) := by ring
      _ = b j := by
          rw [Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hdetne,
            ← Submodule.one_eq_span, mul_one]

/-- **Proposition 81:9** (O'Meara 1963, p. 214). Let $L$ be a free lattice with base $x_1, \dots, x_n$ (a base of $V$
with $L = \mathfrak ox_1 + \cdots + \mathfrak ox_n$), and let $y_i = \sum_j a_{ij}x_j$ for another base $y$ of $V$.
Then $y_1, \dots, y_n$ is a base for $L$ (i.e. $L = \mathfrak oy_1 + \cdots + \mathfrak oy_n$) if and only if the
matrix $(a_{ij})$ is unimodular: integral with determinant a unit of $\mathfrak o$. -/
@[kb "omeara1963" "§81C, 81:9, p. 214"]
theorem span_eq_iff_unimodular {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : Basis ι F V) :
    span R (Set.range y) = span R (Set.range x) ↔
      ∃ A : Matrix ι ι R, IsUnit A.det ∧ ∀ i j, x.repr (y i) j = algebraMap R F (A i j) := by
  constructor
  · intro h
    have hyx : ∀ i j, x.repr (y i) j ∈ (algebraMap R F).range := fun i =>
      (mem_span_range_iff_integral x (y i)).mp (h ▸ subset_span ⟨i, rfl⟩)
    have hxy : ∀ i j, y.repr (x i) j ∈ (algebraMap R F).range := fun i =>
      (mem_span_range_iff_integral y (x i)).mp (h.symm ▸ subset_span ⟨i, rfl⟩)
    choose A hA using hyx
    choose B hB using hxy
    refine ⟨Matrix.of A, ?_, fun i j => (hA i j).symm⟩
    have hAB : Matrix.of A * Matrix.of B = 1 := by
      apply Matrix.ext
      intro i k
      apply IsFractionRing.injective R F
      have h1 := congrArg y.repr (x.sum_repr (y i))
      rw [map_sum] at h1
      have h2 := congrArg (fun f => f k) h1
      simp only [map_smul, Basis.repr_self, Finsupp.single_apply, Finsupp.coe_finsetSum,
        Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at h2
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.one_apply, Matrix.of_apply]
      simp only [hA, hB]
      rw [h2]
      split_ifs with hik
      · simp
      · simp
    exact Matrix.isUnit_det_of_right_inverse hAB
  · rintro ⟨A, hdet, hA⟩
    have hy : ∀ i, y i = ∑ j, A i j • x j := by
      intro i
      conv_lhs => rw [← x.sum_repr (y i)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA, algebraMap_smul]
    have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
    have hx : ∀ i, x i = ∑ j, A⁻¹ i j • y j := by
      intro i
      have : ∑ j, A⁻¹ i j • y j = ∑ k, (A⁻¹ * A) i k • x k := by
        simp only [hy, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
        exact Finset.sum_comm
      rw [this, hBA]
      simp [Matrix.one_apply]
    apply le_antisymm
    · refine span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hy i]
      exact sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩)
    · refine span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hx i]
      exact sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩)

end Dedekind

end QuadFormsKB.OMeara
