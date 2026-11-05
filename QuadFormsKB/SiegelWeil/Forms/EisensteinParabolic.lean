/-
# The Siegel parabolic subgroup of $\mathrm{Sp}_{2r}$
**Layer:** algebra over a field $k$ (every field; used for $k = F$ a number field and $k = F_v$).

**Setting.** $\mathrm{Sp}_{2r}(k)$ = `Sp r k` (Mathlib's `symplecticGroup (Fin r) k`, block indices `Fin r ⊕ Fin r`, 0-based),
$g = \begin{pmatrix}A&B\\C&D\end{pmatrix}$. The Siegel parabolic subgroup is
$$P(k) = \{g \in \mathrm{Sp}_{2r}(k) : C = 0\} = N(k)M(k),\qquad n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix},\ m(A) = \begin{pmatrix}A&0\\0&{}^tA^{-1}\end{pmatrix}.$$

**Results.**
* `siegelP` (**the Siegel parabolic subgroup**) and `PQuot` ($P(k)\backslash\mathrm{Sp}_{2r}(k)$, Mathlib's `rightRel`).
* `exists_spN_spM_of_mem_siegelP` (**Levi decomposition**): every $p \in P(k)$ is $n(B)\,m(A)$ with $B = {}^tB$, $A = $ the upper-left
  block of $p$; and conversely $n(B)m(A) \in P(k)$ (`spN_spM_mem_siegelP`).
* `blockD_mul_of_mem_siegelP`: the bottom blocks of $pg$ are $D_p$ times those of $g$ (used for the height).
* `locSp`: the map $\mathrm{Sp}_{2r}(k) \to \mathrm{Sp}_{2r}(k')$ along a ring map $k \to k'$ (e.g. $F \to F_v$), compatible with $n$, $m$, $w$.

For $r = 1$ these are `borel`, `BQuot` and `eq_cell_of_c_eq_zero` (`SiegelWeil/Eisenstein.lean`).

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Kudla, *Some extensions of the Siegel–Weil
formula* (2008), §1 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Symplectic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep.Genus

variable {k : Type*} [Field k] {r : ℕ}

/-- The lower-left block $C$ of $g = \begin{pmatrix}A&B\\C&D\end{pmatrix}$. -/
def blockC (g : Sp r k) : Matrix (Fin r) (Fin r) k := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₂₁

/-- The lower-right block $D$ of $g$. -/
def blockD (g : Sp r k) : Matrix (Fin r) (Fin r) k := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₂₂

/-- The upper-left block $A$ of $g$. -/
def blockA (g : Sp r k) : Matrix (Fin r) (Fin r) k := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₁₁

/-- The upper-right block $B$ of $g$. -/
def blockB (g : Sp r k) : Matrix (Fin r) (Fin r) k := (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₁₂

lemma eq_fromBlocks (g : Sp r k) :
    (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = fromBlocks (blockA g) (blockB g) (blockC g) (blockD g) :=
  (fromBlocks_toBlocks _).symm

lemma mem_symplectic_blocks (g : Sp r k) :
    fromBlocks (blockA g) (blockB g) (blockC g) (blockD g) ∈ symplecticGroup (Fin r) k := by
  rw [← eq_fromBlocks]; exact g.2

/-- **The Siegel parabolic subgroup** $P(k) = \{g \in \mathrm{Sp}_{2r}(k) : C = 0\}$. -/
@[kb "kudla1996" "§I.1 (the Siegel parabolic $P = MN$) [unverified]"]
def siegelP (r : ℕ) (k : Type*) [Field k] : Subgroup (Sp r k) where
  carrier := {g | blockC g = 0}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    have e : ((g * h : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        fromBlocks (blockA g) (blockB g) (blockC g) (blockD g) *
          fromBlocks (blockA h) (blockB h) (blockC h) (blockD h) := by
      rw [← eq_fromBlocks, ← eq_fromBlocks]; rfl
    unfold blockC
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₁, hg, hh]
    simp
  one_mem' := by
    simp only [Set.mem_setOf_eq, blockC]
    ext i j
    simp [toBlocks₂₁]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have e : ((g⁻¹ : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
        -Matrix.J (Fin r) k * (fromBlocks (blockA g) (blockB g) (blockC g) (blockD g))ᵀ *
          Matrix.J (Fin r) k := by
      rw [SymplecticGroup.coe_inv, ← eq_fromBlocks]
    unfold blockC
    rw [e, hg]
    simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg]

lemma mem_siegelP_iff {g : Sp r k} : g ∈ siegelP r k ↔ blockC g = 0 := Iff.rfl

/-- $P(k)\backslash\mathrm{Sp}_{2r}(k)$: the quotient by $\gamma \sim \gamma'$ iff $\gamma'\gamma^{-1} \in P(k)$. -/
abbrev PQuot (r : ℕ) (k : Type*) [Field k] : Type _ := Quotient (QuotientGroup.rightRel (siegelP r k))

lemma spN_mem_siegelP (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) : spN B hB ∈ siegelP r k := by
  show blockC _ = 0
  simp [blockC]

lemma spM_mem_siegelP (A : GL (Fin r) k) : spM A ∈ siegelP r k := by
  show blockC _ = 0
  simp [blockC]

lemma spN_spM_mem_siegelP (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) (A : GL (Fin r) k) :
    spN B hB * spM A ∈ siegelP r k :=
  (siegelP r k).mul_mem (spN_mem_siegelP B hB) (spM_mem_siegelP A)

/-- For $p \in P(k)$: ${}^tA_p\,D_p = 1$ (so $A_p$ is invertible with $A_p^{-1} = {}^tD_p$) and $A_p\,{}^tB_p$ is symmetric. -/
lemma blocks_of_mem_siegelP {p : Sp r k} (hp : p ∈ siegelP r k) :
    (blockA p)ᵀ * blockD p = 1 ∧ (blockB p * (blockA p)ᵀ)ᵀ = blockB p * (blockA p)ᵀ := by
  have hC : blockC p = 0 := hp
  have h1 := (SymplecticGroup.fromBlocks_mem_iff.mp (mem_symplectic_blocks p)).2.2
  rw [hC, transpose_zero, zero_mul, sub_zero] at h1
  refine ⟨h1, ?_⟩
  have hT := SymplecticGroup.transpose_mem (mem_symplectic_blocks p)
  rw [fromBlocks_transpose] at hT
  have h2 := (SymplecticGroup.fromBlocks_mem_iff.mp hT).1
  rw [transpose_transpose, transpose_transpose] at h2
  rw [transpose_mul, transpose_transpose]
  exact h2

/-- The upper-left block of $p \in P(k)$ as an element of $\mathrm{GL}_r(k)$. -/
def levi {p : Sp r k} (hp : p ∈ siegelP r k) : GL (Fin r) k where
  val := blockA p
  inv := (blockD p)ᵀ
  val_inv := by
    have h := (blocks_of_mem_siegelP hp).1
    have := congrArg transpose h
    rw [transpose_mul, transpose_transpose, transpose_one] at this
    exact mul_eq_one_comm.mp this
  inv_val := by
    have h := (blocks_of_mem_siegelP hp).1
    have := congrArg transpose h
    rwa [transpose_mul, transpose_transpose, transpose_one] at this

/-- **Levi decomposition of the Siegel parabolic**: $p = n(B)\,m(A)$ with $A$ = the upper-left block of $p$ (`levi`) and
$B = B_p\,{}^tA_p$ symmetric. -/
@[kb "kudla1996" "§I.1 ($P = MN$) [unverified]"]
theorem exists_spN_spM_of_mem_siegelP {p : Sp r k} (hp : p ∈ siegelP r k) :
    ∃ (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B), p = spN B hB * spM (levi hp) := by
  obtain ⟨h1, h2⟩ := blocks_of_mem_siegelP hp
  refine ⟨blockB p * (blockA p)ᵀ, h2, ?_⟩
  have hC : blockC p = 0 := hp
  have hAD : ((levi hp)⁻¹ : GL (Fin r) k) = ((blockD p)ᵀ : Matrix (Fin r) (Fin r) k) := rfl
  apply Subtype.ext
  rw [eq_fromBlocks p, hC]
  show _ = fromBlocks 1 _ 0 1 * fromBlocks (blockA p) 0 0 ((((levi hp)⁻¹ : GL (Fin r) k) :
    Matrix (Fin r) (Fin r) k)ᵀ)
  rw [hAD, transpose_transpose, fromBlocks_multiply]
  have hD : blockB p * (blockA p)ᵀ * blockD p = blockB p := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  simp [hD]

/-- **The bottom blocks of $pg$**: for $p \in P(k)$, $(C_{pg}\ D_{pg}) = D_p\,(C_g\ D_g)$. -/
lemma blockCD_mul_of_mem_siegelP {p : Sp r k} (hp : p ∈ siegelP r k) (g : Sp r k) :
    blockC (p * g) = blockD p * blockC g ∧ blockD (p * g) = blockD p * blockD g := by
  have hC : blockC p = 0 := hp
  have e : ((p * g : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) =
      fromBlocks (blockA p) (blockB p) (blockC p) (blockD p) *
        fromBlocks (blockA g) (blockB g) (blockC g) (blockD g) := by
    rw [← eq_fromBlocks, ← eq_fromBlocks]; rfl
  constructor
  · show ((p * g : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₂₁ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₁, hC, Matrix.zero_mul, zero_add]
  · show ((p * g : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).toBlocks₂₂ = _
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₂, hC, Matrix.zero_mul, zero_add]

/-- $\det D_p = (\det A_p)^{-1}$ for $p \in P(k)$. -/
lemma det_blockD_of_mem_siegelP {p : Sp r k} (hp : p ∈ siegelP r k) :
    (blockD p).det * (blockA p).det = 1 := by
  have h := congrArg det (blocks_of_mem_siegelP hp).1
  rw [det_mul, det_transpose, det_one] at h
  rw [mul_comm]; exact h

/-! ### Base change -/

variable {k' : Type*} [Field k']

/-- **The map $\mathrm{Sp}_{2r}(k) \to \mathrm{Sp}_{2r}(k')$** along a ring map $\iota : k \to k'$ (entrywise). -/
def locSp (ι : k →+* k') : Sp r k →* Sp r k' where
  toFun g := ⟨(g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map ι, SymplecticGroup.map_mem g.2 ι⟩
  map_one' := by
    apply Subtype.ext
    simp only [OneMemClass.coe_one]
    exact Matrix.map_one ι (map_zero ι) (map_one ι)
  map_mul' g h := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    exact Matrix.map_mul

lemma locSp_coe (ι : k →+* k') (g : Sp r k) :
    ((locSp ι g : Sp r k') : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k') =
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k).map ι := rfl

lemma locSp_spN (ι : k →+* k') (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    locSp ι (spN B hB) = spN (B.map ι) (by rw [← transpose_map, hB]) := by
  apply Subtype.ext
  rw [locSp_coe, spN_coe, spN_coe, fromBlocks_map]
  simp [Matrix.map_one ι (map_zero ι) (map_one ι)]

lemma locSp_spM (ι : k →+* k') (A : GL (Fin r) k) :
    locSp ι (spM A) = spM (Matrix.GeneralLinearGroup.map ι A) := by
  apply Subtype.ext
  rw [locSp_coe, spM_coe, spM_coe, fromBlocks_map]
  simp [Matrix.GeneralLinearGroup.map, transpose_map]

lemma locSp_mem_siegelP (ι : k →+* k') {p : Sp r k} (hp : p ∈ siegelP r k) : locSp ι p ∈ siegelP r k' := by
  have hC : blockC p = 0 := hp
  show blockC _ = 0
  unfold blockC at hC ⊢
  ext i j
  have := congrFun (congrFun hC i) j
  simp only [toBlocks₂₁, of_apply, Matrix.zero_apply] at this
  simp [toBlocks₂₁, locSp_coe, this]

end QuadFormsKB.SiegelWeil.Forms
