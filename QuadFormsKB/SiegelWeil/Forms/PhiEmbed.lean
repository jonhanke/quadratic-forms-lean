/-
# The embedding $\mathrm{Sp}_{2r} \to \mathrm{Sp}_{2r+2}$ on the variables $1, \dots, r$ (for $\Phi E^{(r+1)} = E^{(r)}$)

**Layer:** linear algebra over any field $k$.

**Setting.** $\mathrm{Sp}_{2r}(k)$ is realized on $k^{r}\oplus k^{r}$ (`Sp r k`, blocks $\begin{pmatrix}A&B\\C&D\end{pmatrix}$, 0-based indices). Siegel's
$\Phi$ operator adds a new variable with index $0$ (`blockZ`, `extZero`); accordingly $\mathrm{Sp}_{2r}(k)$ is embedded in $\mathrm{Sp}_{2r+2}(k)$ on
the variables $1, \dots, r$ (renumbered $0, \dots, r-1$), with the identity on the variable $0$.

**Results.**
* `extC c X`: the $(r+1)\times(r+1)$ matrix with corner entry $c$ at $(0, 0)$, zero elsewhere in row and column $0$, and $X$ in the
  variables $1, \dots, r$; it is compatible with sums, products, transposes (`extC_add`, `extC_mul`, `extC_transpose`, ...).
* **`embSp`**: the monoid homomorphism $\iota : \mathrm{Sp}_{2r}(k) \to \mathrm{Sp}_{2r+2}(k)$,
  $\iota\begin{pmatrix}A&B\\C&D\end{pmatrix} = \begin{pmatrix}\mathrm{extC}\,1\,A&\mathrm{extC}\,0\,B\\\mathrm{extC}\,0\,C&\mathrm{extC}\,1\,D\end{pmatrix}$, with
  `blockC_embSp`, `blockD_embSp`, `embSp_spN` ($\iota(n(B)) = n(\mathrm{extC}\,0\,B)$), `embSp_spM` ($\iota(m(A)) = m(\mathrm{extC}\,1\,A)$).

Source: Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 (the embedding used for the $\Phi$ operator on Eisenstein
series) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinParabolic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.WeilRep.Genus

variable {k : Type*} [Field k] {r : ℕ}

/-- **The extension of $X$ by the corner $c$**: $(\mathrm{extC}\,c\,X)_{00} = c$, $(\mathrm{extC}\,c\,X)_{0,j+1} = (\mathrm{extC}\,c\,X)_{i+1,0} = 0$,
$(\mathrm{extC}\,c\,X)_{i+1,j+1} = X_{ij}$. -/
def extC (c : k) (X : Matrix (Fin r) (Fin r) k) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => X i' j') j) i

@[simp] lemma extC_zero_zero (c : k) (X : Matrix (Fin r) (Fin r) k) : extC c X 0 0 = c := rfl
@[simp] lemma extC_zero_succ (c : k) (X : Matrix (Fin r) (Fin r) k) (j : Fin r) : extC c X 0 j.succ = 0 := rfl
@[simp] lemma extC_succ_zero (c : k) (X : Matrix (Fin r) (Fin r) k) (i : Fin r) : extC c X i.succ 0 = 0 := rfl
@[simp] lemma extC_succ_succ (c : k) (X : Matrix (Fin r) (Fin r) k) (i j : Fin r) :
    extC c X i.succ j.succ = X i j := rfl

lemma extC_ext {M N : Matrix (Fin (r + 1)) (Fin (r + 1)) k} (h00 : M 0 0 = N 0 0) (h0 : ∀ j : Fin r, M 0 j.succ = N 0 j.succ)
    (h1 : ∀ i : Fin r, M i.succ 0 = N i.succ 0) (h : ∀ i j : Fin r, M i.succ j.succ = N i.succ j.succ) : M = N := by
  ext i j
  induction i using Fin.cases with
  | zero => induction j using Fin.cases with
    | zero => exact h00
    | succ j => exact h0 j
  | succ i => induction j using Fin.cases with
    | zero => exact h1 i
    | succ j => exact h i j

lemma extC_add (c d : k) (X Y : Matrix (Fin r) (Fin r) k) : extC c X + extC d Y = extC (c + d) (X + Y) :=
  extC_ext (by simp) (by simp) (by simp) (by simp)

lemma extC_sub (c d : k) (X Y : Matrix (Fin r) (Fin r) k) : extC c X - extC d Y = extC (c - d) (X - Y) :=
  extC_ext (by simp) (by simp) (by simp) (by simp)

lemma extC_mul (c d : k) (X Y : Matrix (Fin r) (Fin r) k) : extC c X * extC d Y = extC (c * d) (X * Y) :=
  extC_ext (by simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by simp [Matrix.mul_apply, Fin.sum_univ_succ])
    (by simp [Matrix.mul_apply, Fin.sum_univ_succ]) (by simp [Matrix.mul_apply, Fin.sum_univ_succ])

lemma extC_transpose (c : k) (X : Matrix (Fin r) (Fin r) k) : (extC c X)ᵀ = extC c Xᵀ :=
  extC_ext (by simp) (by simp) (by simp) (by simp)

lemma extC_one : extC (1 : k) (1 : Matrix (Fin r) (Fin r) k) = 1 :=
  extC_ext (by simp) (fun j => by simp [Matrix.one_apply, (Fin.succ_ne_zero j).symm])
    (fun i => by simp [Matrix.one_apply, Fin.succ_ne_zero i]) (by simp [Matrix.one_apply])

lemma extC_zero : extC (0 : k) (0 : Matrix (Fin r) (Fin r) k) = 0 :=
  extC_ext (by simp) (by simp) (by simp) (by simp)

/-- The matrix of $\iota(g)$. -/
def embMat (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k :=
  fromBlocks (extC 1 M.toBlocks₁₁) (extC 0 M.toBlocks₁₂) (extC 0 M.toBlocks₂₁) (extC 1 M.toBlocks₂₂)

lemma embMat_mul (M N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) : embMat (M * N) = embMat M * embMat N := by
  conv_lhs => rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N]
  rw [embMat, embMat, embMat, fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, extC_mul,
    extC_add]
  norm_num

lemma embMat_one : embMat (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = 1 := by
  rw [embMat, ← fromBlocks_one]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, extC_one, extC_zero]
  rw [← fromBlocks_one]

lemma embMat_mem (g : Sp r k) : embMat (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) ∈ symplecticGroup (Fin (r + 1)) k := by
  have h := g.2
  rw [← fromBlocks_toBlocks (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k), SymplecticGroup.fromBlocks_mem_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [embMat, SymplecticGroup.fromBlocks_mem_iff]
  simp only [extC_transpose, extC_mul, extC_sub]
  refine ⟨by rw [h1]; norm_num, by rw [h2]; norm_num, ?_⟩
  rw [h3]; norm_num; exact extC_one

/-- **The embedding** $\iota : \mathrm{Sp}_{2r}(k) \to \mathrm{Sp}_{2r+2}(k)$ on the variables $1, \dots, r$ (identity on the variable $0$). -/
def embSp : Sp r k →* Sp (r + 1) k where
  toFun g := ⟨embMat (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k), embMat_mem g⟩
  map_one' := Subtype.ext embMat_one
  map_mul' g h := Subtype.ext (embMat_mul _ _)

lemma embSp_coe (g : Sp r k) :
    ((embSp g : Sp (r + 1) k) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) k) =
      embMat (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) := rfl

lemma blockA_embSp (g : Sp r k) : blockA (embSp g) = extC 1 (blockA g) := by
  simp [blockA, embSp_coe, embMat]

lemma blockB_embSp (g : Sp r k) : blockB (embSp g) = extC 0 (blockB g) := by
  simp [blockB, embSp_coe, embMat]

lemma blockC_embSp (g : Sp r k) : blockC (embSp g) = extC 0 (blockC g) := by
  simp [blockC, embSp_coe, embMat]

lemma blockD_embSp (g : Sp r k) : blockD (embSp g) = extC 1 (blockD g) := by
  simp [blockD, embSp_coe, embMat]

lemma extC_symm {B : Matrix (Fin r) (Fin r) k} (hB : Bᵀ = B) (c : k) : (extC c B)ᵀ = extC c B := by
  rw [extC_transpose, hB]

/-- $\iota(n(B)) = n(\mathrm{extC}\,0\,B)$. -/
lemma embSp_spN (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    embSp (spN B hB) = spN (extC 0 B) (extC_symm hB 0) := by
  apply Subtype.ext
  rw [embSp_coe, spN_coe, spN_coe, embMat]
  simp [extC_one, extC_zero]

/-- The invertible matrix $\mathrm{extC}\,1\,A$ for $A \in \mathrm{GL}_r(k)$. -/
def extGL (A : GL (Fin r) k) : GL (Fin (r + 1)) k where
  val := extC 1 (A : Matrix (Fin r) (Fin r) k)
  inv := extC 1 ((A⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)
  val_inv := by rw [extC_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, extC_one]
  inv_val := by rw [extC_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, extC_one]

/-- $\iota(m(A)) = m(\mathrm{extC}\,1\,A)$. -/
lemma embSp_spM (A : GL (Fin r) k) : embSp (spM A) = spM (extGL A) := by
  apply Subtype.ext
  rw [embSp_coe, spM_coe, spM_coe, embMat]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, extC_zero]
  congr 1
  rw [← extC_transpose]; rfl

end QuadFormsKB.SiegelWeil.Forms
