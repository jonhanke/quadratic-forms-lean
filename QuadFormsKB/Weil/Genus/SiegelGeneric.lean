/-
# Generic translates into the big cell of $\mathrm{Sp}_{2g}$

**Layer:** pure algebra over a field $k$.

**Setting.** $k$ a field, $g \in \mathbb{N}$, $\gamma \in \mathrm{Sp}_{2g}(k)$ (`Sp g k`), written in blocks
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix}$ with $c = $ `toBlocks₂₁ γ`, $d = $ `toBlocks₂₂ γ`.

**Results.**
* `toBlocks₂₁_mul_spN_spW`: the lower-left block of $\gamma\,n(T)\,w$ is $-(cT + d)$.
* `exists_symm_det_ne`: for every $\gamma$ there is a symmetric $T$ with $\det(cT + d) \ne 0$
  (the "big cell" statement: $\gamma\, n(T)\, w$ has invertible lower-left block).
* `exists_symm_det_ne_list`: over an infinite field, one symmetric $T$ works simultaneously for a finite list of $\gamma$'s.
* `exists_spN_spW_generic`: consequently $\gamma\,n(T)\,w$ has invertible lower-left block for all $\gamma$ in the list.

**Method.** For `exists_symm_det_ne`, induction on $\dim\ker d$: if $d$ is singular, pick $v \ne 0$ with $dv = 0$ and an index
$i$ with $v_i \ne 0$, put $z = e_i$, $S = zz^{\mathsf T}$, and replace $\gamma$ by $\gamma\,n(S)$ (same $c$, new $d' = cS + d$).
The symplectic identities ${}^ta d - {}^tc b = 1$ and ${}^tb d = {}^td b$ show that $cz \in \mathrm{im}\, d$ would force
$z \perp \ker d$, contradicting $z\cdot v = v_i \ne 0$; hence $\ker d' \subsetneq \ker d$. For the list version, induct on
the list and move along the line $T_1 + t(T_2 - T_1)$: each $\det$ is a nonzero polynomial in $t$, and a finite product of
nonzero polynomials has a non-root over an infinite field.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Symplectic

open Matrix Polynomial

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

variable {g : ℕ} {k : Type*} [Field k]

/-- **Lower-left block of $\gamma\,n(T)\,w$.** For $\gamma \in \mathrm{Sp}_{2g}(k)$ with lower blocks $c, d$
(`toBlocks₂₁ γ`, `toBlocks₂₂ γ`) and symmetric $T$ (hypothesis `hT : Tᵀ = T`),
$$\text{lower-left block of } \gamma\,n(T)\,w = -(cT + d).$$ -/
theorem toBlocks₂₁_mul_spN_spW (γ : Sp g k) (T : Matrix (Fin g) (Fin g) k) (hT : Tᵀ = T) :
    toBlocks₂₁ ((γ * (spN T hT * spW) : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      -(toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)) := by
  have h : ((γ * (spN T hT * spW) : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * (fromBlocks 1 T 0 1 * fromBlocks 0 1 (-1) 0) := rfl
  rw [h]
  conv_lhs => rw [← fromBlocks_toBlocks (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)]
  rw [fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp
  abel

/-- Blocks of $\gamma\,n(S)$: same $c$, and $d' = cS + d$. -/
private lemma blocks_mul_spN (γ : Sp g k) (S : Matrix (Fin g) (Fin g) k) (hS : Sᵀ = S) :
    toBlocks₂₁ ((γ * spN S hS : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) ∧
    toBlocks₂₂ ((γ * spN S hS : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * S +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) := by
  have h : ((γ * spN S hS : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * fromBlocks 1 S 0 1 := rfl
  rw [h]
  rw [← fromBlocks_toBlocks (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k), fromBlocks_multiply]
  simp

/-- Orthogonality: if $cz \in \mathrm{im}\,d$ (say $cz = dy$) and $dv = 0$ then $z\cdot v = 0$. -/
private lemma dot_eq_zero_of_blocks (γ : Sp g k) (z y v : Fin g → k)
    (hzy : toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) *ᵥ z =
      toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) *ᵥ y)
    (hv : toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) *ᵥ v = 0) :
    z ⬝ᵥ v = 0 := by
  have hmem := γ.2
  rw [← fromBlocks_toBlocks (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)] at hmem
  obtain ⟨-, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hmem
  set b := toBlocks₁₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
  set c := toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
  set d := toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
  set a := toBlocks₁₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
  have hvv : v = -(cᵀ *ᵥ (b *ᵥ v)) := by
    have : (aᵀ * d - cᵀ * b) *ᵥ v = v := by rw [h3, one_mulVec]
    rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, mulVec_zero, zero_sub] at this
    exact this.symm
  have e1 : z ⬝ᵥ (cᵀ *ᵥ (b *ᵥ v)) = (c *ᵥ z) ⬝ᵥ (b *ᵥ v) := by
    rw [dotProduct_mulVec, vecMul_transpose]
  have e2 : (d *ᵥ y) ⬝ᵥ (b *ᵥ v) = y ⬝ᵥ (dᵀ *ᵥ (b *ᵥ v)) := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have e3 : dᵀ *ᵥ (b *ᵥ v) = 0 := by
    rw [mulVec_mulVec, ← h2, ← mulVec_mulVec, hv, mulVec_zero]
  rw [hvv, dotProduct_neg, e1, hzy, e2, e3]
  simp

/-- **Existence of a symmetric $T$ with $cT + d$ invertible.** For every $\gamma \in \mathrm{Sp}_{2g}(k)$ with lower blocks
$c = $ `toBlocks₂₁ γ`, $d = $ `toBlocks₂₂ γ`, there is a symmetric $T$ (`Tᵀ = T`) with $\det(cT + d) \ne 0$. -/
@[kb "kudla1996" "§I.1 (the big cell of $\\mathrm{Sp}_{2g}$) [unverified]"]
theorem exists_symm_det_ne (γ : Sp g k) :
    ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧
      (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 := by
  suffices H : ∀ n : ℕ, ∀ γ : Sp g k,
      Module.finrank k (LinearMap.ker (Matrix.mulVecLin
        (toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)))) = n →
      ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧
        (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T +
          toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 from H _ γ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hn
    by_cases hdet : (toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det = 0
    swap
    · exact ⟨0, transpose_zero, by simpa using hdet⟩
    obtain ⟨v, hv0, hdv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    set z : Fin g → k := Pi.single i 1 with hz
    set S : Matrix (Fin g) (Fin g) k := vecMulVec z z with hSdef
    have hS : Sᵀ = S := by
      ext p q; simp [hSdef, vecMulVec, mul_comm]
    have hSx : ∀ x : Fin g → k, S *ᵥ x = x i • z := by
      intro x
      ext p
      simp [hSdef, vecMulVec, mulVec, dotProduct, hz, Pi.single_apply, mul_comm]
    obtain ⟨hc', hd'⟩ := blocks_mul_spN γ S hS
    set c := toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) with hc
    set d := toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) with hd
    have key : ∀ x, (c * S + d) *ᵥ x = 0 → d *ᵥ x = 0 ∧ x i = 0 := by
      intro x hx
      rw [add_mulVec, ← mulVec_mulVec, hSx, mulVec_smul] at hx
      by_cases hxi : x i = 0
      · refine ⟨?_, hxi⟩
        rw [hxi, zero_smul, zero_add] at hx
        exact hx
      · exfalso
        have hzy : c *ᵥ z = d *ᵥ (-(x i)⁻¹ • x) := by
          rw [mulVec_smul]
          have : d *ᵥ x = -(x i • c *ᵥ z) := eq_neg_of_add_eq_zero_right hx
          rw [this, smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hxi]
          simp
        have := dot_eq_zero_of_blocks γ z _ v hzy hdv
        simp [hz, dotProduct, Pi.single_apply] at this
        exact hi this
    obtain ⟨T', hT', hdetT'⟩ := ih _ (by
      rw [← hn]
      apply Submodule.finrank_lt_finrank_of_lt
      rw [IsConcreteLE.lt_iff_le_and_exists]
      refine ⟨?_, v, ?_, ?_⟩
      · intro x hx
        have hx' : (toBlocks₂₂ (((γ * spN S hS : Sp g k)) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)) *ᵥ x = 0 := by simpa using hx
        rw [hd'] at hx'
        exact (key x hx').1
      · exact hdv
      · intro hvin
        have hx' : (toBlocks₂₂ (((γ * spN S hS : Sp g k)) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)) *ᵥ v = 0 := by simpa using hvin
        rw [hd'] at hx'
        exact hi (key v hx').2) (γ * spN S hS) rfl
    refine ⟨S + T', by rw [transpose_add, hS, hT'], ?_⟩
    rw [hc', hd'] at hdetT'
    convert hdetT' using 2
    rw [Matrix.mul_add, add_assoc, add_comm (c * T'), ← add_assoc, add_assoc, add_comm (c * T')]
    abel

/-- Polynomial in `t` evaluating to $\det(A + tB)$. -/
private lemma exists_poly_det (A B : Matrix (Fin g) (Fin g) k) :
    ∃ p : k[X], ∀ t : k, p.eval t = (A + t • B).det := by
  refine ⟨((A.map C : Matrix (Fin g) (Fin g) k[X]) + (X : k[X]) • B.map C).det, fun t => ?_⟩
  have := RingHom.map_det (Polynomial.evalRingHom t) ((A.map C : Matrix (Fin g) (Fin g) k[X]) +
    (X : k[X]) • B.map C)
  rw [Polynomial.coe_evalRingHom] at this
  rw [this]
  congr 1
  ext p q
  simp
  exact mul_comm _ _

/-- Over an infinite field, finitely many "lines" $t \mapsto A_j + tB_j$ each having a point of nonzero
determinant have a common point of nonzero determinant. -/
private lemma exists_forall_det_ne [Infinite k] (S : List (Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k))
    (h : ∀ q ∈ S, ∃ t : k, (q.1 + t • q.2).det ≠ 0) :
    ∃ t : k, ∀ q ∈ S, (q.1 + t • q.2).det ≠ 0 := by
  classical
  choose p hp using fun q : Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k =>
    exists_poly_det q.1 q.2
  by_contra hcon
  push Not at hcon
  have hP : (S.map p).prod = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_list_prod, Polynomial.eval_zero, List.map_map]
    obtain ⟨q, hq, hq0⟩ := hcon t
    apply List.prod_eq_zero
    rw [List.mem_map]
    exact ⟨q, hq, by simp [Function.comp, hp, hq0]⟩
  rw [List.prod_eq_zero_iff, List.mem_map] at hP
  obtain ⟨q, hq, hq0⟩ := hP
  obtain ⟨t, ht⟩ := h q hq
  have := hp q t
  rw [hq0, Polynomial.eval_zero] at this
  exact ht this.symm

/-- **A common symmetric $T$ for finitely many $\gamma$'s.** Over an infinite field $k$ (hypothesis `Infinite k`), for any
finite list $L$ of elements of $\mathrm{Sp}_{2g}(k)$ there is a symmetric $T$ with $\det(c_\gamma T + d_\gamma) \ne 0$ for all
$\gamma \in L$, where $c_\gamma = $ `toBlocks₂₁ γ`, $d_\gamma = $ `toBlocks₂₂ γ`. -/
@[kb "kudla1996" "§I.1 (the big cell of $\\mathrm{Sp}_{2g}$) [unverified]"]
theorem exists_symm_det_ne_list [Infinite k] (L : List (Sp g k)) :
    ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧ ∀ γ ∈ L,
      (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 := by
  induction L with
  | nil => exact ⟨0, transpose_zero, by simp⟩
  | cons γ₀ L ih =>
    obtain ⟨T₁, hT₁, h₁⟩ := ih
    obtain ⟨T₂, hT₂, h₂⟩ := exists_symm_det_ne γ₀
    let blk : Sp g k → Matrix (Fin g) (Fin g) k × Matrix (Fin g) (Fin g) k := fun γ =>
      (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * T₁ +
        toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k),
       toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * (T₂ - T₁))
    have hline : ∀ (γ : Sp g k) (t : k),
        (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) * (T₁ + t • (T₂ - T₁)) +
          toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)) = (blk γ).1 + t • (blk γ).2 := by
      intro γ t
      simp only [blk, Matrix.mul_add, Matrix.mul_smul]
      abel
    obtain ⟨t, ht⟩ := exists_forall_det_ne ((γ₀ :: L).map blk) (by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨γ, hγ, rfl⟩ := hq
      rcases List.mem_cons.1 hγ with rfl | hγL
      · refine ⟨1, ?_⟩
        rw [← hline γ 1, one_smul, add_sub_cancel]
        exact h₂
      · refine ⟨0, ?_⟩
        rw [zero_smul, add_zero]
        exact h₁ γ hγL)
    refine ⟨T₁ + t • (T₂ - T₁), ?_, ?_⟩
    · rw [transpose_add, transpose_smul, transpose_sub, hT₁, hT₂]
    · intro γ hγ
      rw [hline]
      exact ht _ (List.mem_map.2 ⟨γ, hγ, rfl⟩)

/-- **Generic translate into the big cell.** Over an infinite field $k$ (hypothesis `Infinite k`), for any finite list $L$
of elements of $\mathrm{Sp}_{2g}(k)$ there is a symmetric $T$ (`hT : Tᵀ = T`) such that the lower-left block of
$\gamma\,n(T)\,w$ is invertible for every $\gamma \in L$. -/
theorem exists_spN_spW_generic [Infinite k] (L : List (Sp g k)) :
    ∃ T : Matrix (Fin g) (Fin g) k, ∃ hT : Tᵀ = T, ∀ γ ∈ L,
      (toBlocks₂₁ ((γ * (spN T hT * spW) : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0 := by
  obtain ⟨T, hT, h⟩ := exists_symm_det_ne_list L
  refine ⟨T, hT, fun γ hγ => ?_⟩
  rw [toBlocks₂₁_mul_spN_spW, det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h γ hγ)

end QuadFormsKB.WeilRep.Genus
