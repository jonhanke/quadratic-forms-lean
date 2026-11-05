/-
# O'Meara 93:28, sufficiency: unimodular lattices on hyperbolic spaces

**Setting** (as in `Sec93E.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276, the final step "Then
$K_1 \cong L_1$" of each case)
* `exists_orth_span_eq`: Witt's theorem for families: two families of vectors with the same non-singular matrix
  $(B(p_i, p_j))$ span subspaces that are carried onto each other by some $\sigma \in O(V)$;
* `isometricLat_of_blockBase`: unimodular lattices with block bases $A(c_k, 0)$ of the same length and the same norm
  group are isometric (93:16);
* `isometricLat_of_hyp`: unimodular lattices of the same rank and norm group on hyperbolic spaces are isometric.
-/
import QuadFormsKB.Literature.OMeara.Sec93FMain

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreHyp

open NecBlock Merge28 SuffWitt Uni93

section Witt

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Witt's theorem for families** (O'Meara 1963, 42:17, p. 98): if $p, p' : \iota \to V$ have the same matrix
$(B(p_i, p_j)) = (B(p'_i, p'_j))$ and this matrix is non-singular, then some $\sigma \in O(V)$ carries the span of the
$p_i$ onto the span of the $p'_i$. -/
theorem exists_orth_span_eq (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R F]
    [IsFractionRing R F] [Module R V] [IsScalarTower R F V] (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p p' : ι → V} (hG : gram Q p = gram Q p') (hdet : (gram Q p).det ≠ 0) :
    ∃ σ ∈ orth Q, Submodule.map (σ : V →ₗ[F] V) (span F (Set.range p)) = span F (Set.range p') := by
  have hli : LinearIndependent R p := linearIndependent_of_det_gram_ne_zero (R := R) Q hdet
  have hli' : LinearIndependent R p' := linearIndependent_of_det_gram_ne_zero (R := R) Q (hG ▸ hdet)
  set A : Submodule R V := span R (Set.range p) with hA
  set A' : Submodule R V := span R (Set.range p') with hA'
  let b : Basis ι R A := Basis.span hli
  let b' : Basis ι R A' := Basis.span hli'
  have hb : ∀ i, (b i : V) = p i := fun i => congrArg Subtype.val (Basis.span_apply hli i)
  have hb' : ∀ i, (b' i : V) = p' i := fun i => congrArg Subtype.val (Basis.span_apply hli' i)
  have hiso : IsometricLat Q Q A A' := isometricLat_of_gram_eq Q Q b b' (by
    have e1 : (fun i => (b i : V)) = p := funext hb
    have e2 : (fun i => (b' i : V)) = p' := funext hb'
    rw [e1, e2, hG])
  have hAfg : A.FG := Submodule.fg_span (Set.finite_range p)
  have hAreg : IsRegular Q A := by
    intro x hx h0
    set c : ι → R := fun i => b.repr ⟨x, hx⟩ i with hc
    have hxc : x = ∑ i, c i • p i := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, hb] at this
      exact this.symm
    have hv : Matrix.vecMul (fun i => algebraMap R F (c i)) (gram Q p) = 0 := by
      funext j
      have hj := h0 (p j) (subset_span ⟨j, rfl⟩)
      rw [hxc, bil_sum_left] at hj
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gram, Matrix.of_apply]
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bil_rsmul_left]
    have hc0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
    rw [hxc]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : algebraMap R F (c i) = 0 := congrFun hc0 i
    rw [(map_eq_zero_iff _ (IsFractionRing.injective R F)).1 this, zero_smul]
  obtain ⟨σ, hσ, hσA⟩ := exists_orth_latMap_eq Q hQ hAfg hAreg hiso
  refine ⟨σ, hσ, ?_⟩
  have h1 : span F (Set.range p) = span F (A : Set V) := (Submodule.span_span_of_tower R F _).symm
  have h2 : span F (Set.range p') = span F (A' : Set V) := (Submodule.span_span_of_tower R F _).symm
  rw [h1, h2, Submodule.map_span, ← hσA]
  rfl

end Witt

section Blocks

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The hyperbolic pairs of a block base: for blocks $(e_k, f_k)$ with matrix $A(c_k, 0)$, the vectors
$u_k = 2e_k - c_k f_k$ and $f_k$ satisfy $Q(u_k) = 0$ and $B(u_k, f_k) = 2$. -/
def hypVec {m : ℕ} (x : Fin m → V × V) : Fin m ⊕ Fin m → V
  | .inl k => (2 : F) • (x k).1 - Q (x k).1 • (x k).2
  | .inr k => (x k).2

/-- The matrix of the hyperbolic pairs: $\begin{pmatrix} 0 & 2I \\ 2I & 0 \end{pmatrix}$. -/
theorem gram_hypVec {K : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q K x) :
    gram Q (hypVec Q x) = Matrix.fromBlocks 0 (2 : Matrix (Fin m) (Fin m) F) 2 0 := by
  obtain ⟨-, hf, hef, hee, hefo, hff⟩ := hx
  have hfe : ∀ k l, k ≠ l → bil Q (x k).2 (x l).1 = 0 := fun k l h => by
    rw [bil_comm]; exact hefo l k (Ne.symm h)
  ext (k | k) (l | l)
  · simp only [gram, hypVec, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    rw [bil_sub_left, bil_sub_right, bil_sub_right, bil_smul_left, bil_smul_left, bil_smul_right, bil_smul_right,
      bil_smul_left, bil_smul_right, bil_smul_right, bil_smul_left]
    by_cases h : k = l
    · subst h
      rw [bil_self, bil_self, hf, bil_comm Q (x k).2 (x k).1, hef]; ring
    · rw [hee k l h, hefo k l h, hfe k l h, hff k l h]; ring
  · simp only [gram, hypVec, Matrix.of_apply, Matrix.fromBlocks_apply₁₂]
    rw [bil_sub_left, bil_smul_left, bil_smul_left]
    by_cases h : k = l
    · subst h
      rw [hef, bil_self, hf]; simp [Matrix.ofNat_apply]
    · rw [hefo k l h, hff k l h]
      simp [Matrix.ofNat_apply, h]
  · simp only [gram, hypVec, Matrix.of_apply, Matrix.fromBlocks_apply₂₁]
    rw [bil_sub_right, bil_smul_right, bil_smul_right]
    by_cases h : k = l
    · subst h
      rw [bil_comm, hef, bil_self, hf]; simp [Matrix.ofNat_apply]
    · rw [hfe k l h, hff k l h]
      simp [Matrix.ofNat_apply, h]
  · simp only [gram, hypVec, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    by_cases h : k = l
    · subst h; rw [bil_self, hf]
    · exact hff k l h

/-- The matrix of the hyperbolic pairs is non-singular. -/
theorem det_gram_hypVec_ne_zero {K : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q K x) :
    (gram Q (hypVec Q x)).det ≠ 0 := by
  rw [gram_hypVec Q hx]
  set M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := Matrix.fromBlocks 0 (2 : Matrix (Fin m) (Fin m) F) 2 0
  have hsq : M * M = (4 : F) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) := by
    simp only [M, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.ofNat_apply, Matrix.mul_apply, Matrix.one_apply] <;>
      split_ifs <;> norm_num
  intro h0
  have := congrArg Matrix.det hsq
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero (two_ne_zero' F) (two_ne_zero' F)
  exact pow_ne_zero _ h4 this.symm

/-- The hyperbolic pairs span the same subspace as the block base. -/
theorem span_hypVec {K : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q K x) :
    span F (Set.range (hypVec Q x)) = span F (K : Set V) := by
  rw [← hx.1, pairSpan, Submodule.span_span_of_tower]
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨k | k, rfl⟩
    · exact sub_mem (smul_mem _ _ (subset_span (Or.inl ⟨k, rfl⟩))) (smul_mem _ _ (subset_span (Or.inr ⟨k, rfl⟩)))
    · exact subset_span (Or.inr ⟨k, rfl⟩)
  · rw [span_le]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · show (x k).1 ∈ _
      have hu : hypVec Q x (.inl k) ∈ span F (Set.range (hypVec Q x)) := subset_span ⟨_, rfl⟩
      have hf : hypVec Q x (.inr k) ∈ span F (Set.range (hypVec Q x)) := subset_span ⟨_, rfl⟩
      have : (x k).1 = (2 : F)⁻¹ • (hypVec Q x (.inl k) + Q (x k).1 • hypVec Q x (.inr k)) := by
        simp only [hypVec, sub_add_cancel, smul_smul, inv_mul_cancel₀ (two_ne_zero' F), one_smul]
      rw [SetLike.mem_coe, this]
      exact smul_mem _ _ (add_mem hu (smul_mem _ _ hf))
    · exact subset_span ⟨.inr k, rfl⟩

/-- A lattice with a block base of length $m$ has rank $2m$. -/
theorem finrank_of_blockBase {K : Submodule R V} {m : ℕ} {x : Fin m → V × V} (hx : IsBlockBase Q K x) :
    finrank R K = 2 * m := by
  have hli : LinearIndependent R (hypVec Q x) :=
    linearIndependent_of_det_gram_ne_zero (R := R) Q (det_gram_hypVec_ne_zero Q hx)
  rw [finrank_eq_finrank_span (F := F) K, ← span_hypVec Q hx, ← Submodule.span_span_of_tower R F,
    ← finrank_eq_finrank_span (F := F), finrank_span_eq_card hli]
  simp [two_mul]

/-- **Unimodular lattices with block bases of the same length and the same norm group are isometric** (O'Meara
1963, 93:16 with Witt's theorem 42:17): both span hyperbolic spaces of the same dimension. -/
theorem isometricLat_of_blockBase (hQ : (QuadraticMap.associated Q).Nondegenerate) {X Y : Submodule R V} {m : ℕ}
    {x y : Fin m → V × V} (hx : IsBlockBase Q X x) (hy : IsBlockBase Q Y y) (hXU : IsUnimodular Q X)
    (hYU : IsUnimodular Q Y) (hg : normGroup Q X = normGroup Q Y) : IsometricLat Q Q X Y := by
  have hXfg : X.FG := hx.1 ▸ Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))
  have hYfg : Y.FG := hy.1 ▸ Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨σ, hσ, hσs⟩ := exists_orth_span_eq Q R hQ ((gram_hypVec Q hx).trans (gram_hypVec Q hy).symm)
    (det_gram_hypVec_ne_zero Q hx)
  have h1 : IsometricLat Q Q X (latMap σ X) := isometricLat_latMap Q hσ X
  have hσfg : (latMap σ X).FG := hXfg.map _
  have hspan : span F (latMap σ X : Set V) = span F (Y : Set V) := by
    rw [← span_hypVec Q hy, ← hσs, span_hypVec Q hx, Submodule.map_span]
    rfl
  have h2 : IsometricLat Q Q (latMap σ X) Y := by
    refine isometricLat_of_normGroup_eq_of_span Q hσfg hYfg hspan.symm (h1.isModular Q Q hXfg hXU) hYU ?_
    rw [← adj_normGroup_eq Q Q h1, hg]
  exact adj_isometricLat_trans Q Q Q h1 h2

/-- **Unimodular lattices on hyperbolic spaces** (O'Meara 1963, §93F, p. 273, with 93:3 and 93:16): if $L$, $K$ are
unimodular lattices of the same rank and the same norm group and each of $FL$, $FK$ contains a totally isotropic
subspace of half its dimension, then $L \cong K$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, p. 273 (L₁ ≅ K₁ for unimodular lattices on hyperbolic spaces)"]
theorem isometricLat_of_hyp (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} (hLfg : L.FG)
    (hKfg : K.FG) (hLU : IsUnimodular Q L) (hKU : IsUnimodular Q K) (hrk : finrank R L = finrank R K)
    (hg : normGroup Q L = normGroup Q K)
    (hTL : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (L : Set V)) ∧
      finrank R L ≤ 2 * finrank F T)
    (hTK : ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (K : Set V)) ∧
      finrank R K ≤ 2 * finrank F T) :
    IsometricLat Q Q L K := by
  have blocks : ∀ {M : Submodule R V}, M.FG → IsUnimodular Q M →
      (∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (M : Set V)) ∧
        finrank R M ≤ 2 * finrank F T) →
      ∃ B : Submodule R V, ∃ m, ∃ x : Fin m → V × V, IsBlockBase Q B x ∧ IsUnimodular Q B ∧
        normGroup Q B = normGroup Q M ∧ finrank R M = 2 * m ∧ IsometricLat Q Q M B := by
    intro M hMfg hMU ⟨T, hTiso, hTM, hTdim⟩
    obtain ⟨B, hMB, hBM, hBfg, hBU, hgB, hrB, m, x, hx⟩ :=
      exists_unimodular_blocks Q hMfg (hMU.isRegular Q hMfg) hMU.2.1 hTiso hTM hTdim
    have hspan : span F (B : Set V) = span F (M : Set V) :=
      le_antisymm (span_le.mpr fun b hb => hBM b hb) (span_mono hMB)
    refine ⟨B, m, x, hx, hBU, hgB, hrB ▸ finrank_of_blockBase Q hx, ?_⟩
    exact isometricLat_of_normGroup_eq_of_span Q hMfg hBfg hspan hMU hBU hgB.symm
  obtain ⟨BL, m, x, hx, hBLU, hgL, hmL, hL⟩ := blocks hLfg hLU hTL
  obtain ⟨BK, m', y, hy, hBKU, hgK, hmK, hK⟩ := blocks hKfg hKU hTK
  have hm : m' = m := by omega
  subst hm
  have hB := isometricLat_of_blockBase Q hQ hx hy hBLU hBKU (by rw [hgL, hgK, hg])
  exact adj_isometricLat_trans Q Q Q (adj_isometricLat_trans Q Q Q hL hB) (adj_isometricLat_symm Q Q hK)

end Blocks

section Core

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

open Suff28

/-- **The computational core of the sufficiency in 93:28, reduced** (O'Meara 1963, §93F, proof of the sufficiency,
steps 4–8, pp. 274–276), *named statement*: in the situation reached by the reductions of step 2 (as in `SuffCore`:
both Jordan splittings saturated, all fundamental dimensions $\ge 3$, every space $FL_k$ hyperbolic, $L_1$ unimodular,
the same fundamental invariants and conditions (i)–(iii)), $K$ has a saturated Jordan splitting
$K = K_1' \perp \cdots \perp K_t'$ whose first space $FK_1'$ is hyperbolic (a totally isotropic subspace $T$ with
$\dim K_1' \le 2 \dim T$). Each of O'Meara's steps 4–8 ends with "Then $K_1 \cong L_1$", which he reads off the
forms $K_1 \cong \langle A(a_1, 0)\rangle \perp \langle A(b_1, 0)\rangle \cong L_1$ (93:18 (vi)) obtained in that
step; such a $K_1$ spans a hyperbolic space, and conversely `isometricLat_of_hyp` (93:3, 93:16, Witt) recovers
$K_1' \cong L_1$ from hyperbolicity, so this statement is what remains of `SuffCore`
(`suffCore_of_hyp_of_resplit`). As for `SuffCore`, the dimensions are only assumed $\ge 3$; O'Meara's steps run
after his reduction to dimension $4$ (93:18, 93:14). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4–8, pp. 274–276 (FK₁ hyperbolic)"]
structure SuffCoreHyp : Prop where
  core : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧
        ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ks' 0 : Set V)) ∧
          finrank R (Ks' 0) ≤ 2 * finrank F T

variable {R F}

/-- **`SuffCore` from `SuffCoreHyp`**, given that conditions (i)–(iii) do not depend on the Jordan splitting of $K$
(O'Meara 1963, p. 273: "conditions (i)–(iii) will continue to hold if the given splitting $K_1 \perp \cdots \perp K_t$
is replaced by any other Jordan splitting"). The new first component $K_1'$ is unimodular with
$\mathfrak gK_1' = \mathfrak g_1 = \mathfrak gL_1$ (saturation) on a hyperbolic space, so $K_1' \cong L_1$ by
`isometricLat_of_hyp`. -/
theorem suffCore_of_hyp_of_resplit
    (hres : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
      (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
      ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] {t : ℕ} (Ls Ks Ks' : Fin t → Submodule R V)
        (a : Fin t → F), IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → IsJordanSplitting Q K Ks' →
        SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → Cond93 Q L Ls Ks' a)
    (h : SuffCoreHyp.{u, v} R F) : SuffCore.{u, v} R F := by
  refine ⟨fun {V} _ _ _ _ _ Q h2p hQ L K _ _ m Ls Ks a hLs hKs hd hT hsc hS hC => ?_⟩
  obtain ⟨Ks', hKs', hTK⟩ := h.core Q h2p hQ L K m Ls Ks a hLs hKs hd hT hsc hS hC
  refine ⟨Ks', hKs', ?_, hres Q h2p hQ L K Ls Ks Ks' a hLs.1 hKs.1 hKs'.1 hS hC⟩
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hS' := SuffMain.sameFund_resplit Q hKfg hKs.1 hKs'.1 hS
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := hS'
  have hc : Fin.cast h0 0 = 0 := Fin.ext (by simp)
  obtain ⟨hrk, hsc', hg⟩ := hTy 0
  rw [hc] at hrk hsc' hg
  have hL0fg : (Ls 0).FG := FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls 0)
  have hK0fg : (Ks' 0).FG := FG.of_le hKfg (hKs'.1.split.iSup_eq ▸ le_iSup Ks' 0)
  have hLU : IsUnimodular Q (Ls 0) := by
    have := hLs.1.modular 0; rwa [hsc] at this
  have hKU : IsUnimodular Q (Ks' 0) := by
    have := hKs'.1.modular 0; rwa [← hsc', hsc] at this
  exact isometricLat_of_hyp Q hQ hL0fg hK0fg hLU hKU hrk (by rw [hLs.2 0, hKs'.2 0, hg]) (hT 0) hTK

end Core

end QuadFormsKB.OMeara.CoreHyp
