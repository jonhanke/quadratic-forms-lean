/-
# The big Bruhat cell of $P(k)\backslash\mathrm{Sp}_{2r}(k)$ (for the unfolding of the Fourier coefficients)

**Layer:** algebra over a field $k$ (every field; used for $k = F$ a number field).

**Setting.** $\mathrm{Sp}_{2r}(k)$ = `Sp r k`, $g = \begin{pmatrix}A&B\\C&D\end{pmatrix}$, the Siegel parabolic $P(k) = \{C = 0\}$ (`siegelP`), the
coset space $P(k)\backslash\mathrm{Sp}_{2r}(k)$ (`PQuot`), $n(B) = \begin{pmatrix}1&B\\0&1\end{pmatrix}$ (`spN`), $w = \begin{pmatrix}0&1\\-1&0\end{pmatrix}$ (`spW`).

**Results.**
* `isUnit_det_blockC_mul`: $\det C$ is nonzero on a whole coset $P(k)g$ or on none of it ($C_{pg} = D_pC_g$), so the **big cell**
  $\{P(k)g : \det C_g \ne 0\}$ (`bigCell`) is well defined.
* **`bigCellEquiv`**: $\mathrm{Sym}_r(k) \cong$ big cell, $B \mapsto P(k)\,w\,n(B)$; the inverse sends $P(k)g$ to $C_g^{-1}D_g$
  (`mk_eq_spW_spN`: $g \in P(k)\,w\,n(C^{-1}D)$, and $C^{-1}D$ is symmetric because $CD^{\mathsf T} = DC^{\mathsf T}$).
* `bigCellMap_mul_spN`: the right action of $N(k)$ on the big cell is translation, $P\,w\,n(B)\cdot n(X) = P\,w\,n(B + X)$.

This is the first step of the unfolding of the $T$-th Fourier coefficient of the Siegel Eisenstein series: the big-cell part of
$\sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f(\gamma n(X)g)$ is $\sum_{B\in\mathrm{Sym}_r(F)}f(wn(B + X)g)$, whose $T$-th Fourier coefficient over
$\mathrm{Sym}_r(F)\backslash\mathrm{Sym}_r(\mathbb A)$ is the global Whittaker integral $\int_{\mathrm{Sym}_r(\mathbb A)}f(wn(X)g)\psi(-\operatorname{tr}TX)\,dX$.
For $r = 1$ the big cell is the $c \ne 0$ part of `BQuot` (`SiegelWeil/Eisenstein.lean`).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 (the Bruhat decomposition $P\backslash G = \bigsqcup_jP w_jN$)
[unverified]; Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.EisensteinParabolic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep.Genus

variable {k : Type*} [Field k] {r : ℕ}

/-- The blocks of $wn(B) = \begin{pmatrix}0&1\\-1&-B\end{pmatrix}$. -/
lemma spW_spN_coe (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) :
    ((spW * spN B hB : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) = fromBlocks 0 1 (-1) (-B) := by
  show ((spW : Sp r k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k) * (spN B hB : Sp r k) = _
  rw [spW_coe, spN_coe, fromBlocks_multiply]
  simp

lemma blockC_spW_spN (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) : blockC (spW * spN B hB) = -1 := by
  unfold blockC; rw [spW_spN_coe]; simp

/-- $CD^{\mathsf T} = DC^{\mathsf T}$ for $g \in \mathrm{Sp}_{2r}(k)$ (from $g^{\mathsf T} \in \mathrm{Sp}_{2r}(k)$). -/
lemma blockC_mul_blockD_transpose (g : Sp r k) : blockC g * (blockD g)ᵀ = blockD g * (blockC g)ᵀ := by
  have h := SymplecticGroup.transpose_mem g.2
  rw [eq_fromBlocks g, fromBlocks_transpose, SymplecticGroup.fromBlocks_mem_iff] at h
  simpa using h.2.1

/-- **Left $P(k)$-invariance of the big cell condition:** $\det C_{pg} \ne 0 \iff \det C_g \ne 0$ for $p \in P(k)$. -/
lemma isUnit_det_blockC_mul {p : Sp r k} (hp : p ∈ siegelP r k) (g : Sp r k) :
    (blockC (p * g)).det ≠ 0 ↔ (blockC g).det ≠ 0 := by
  rw [(blockCD_mul_of_mem_siegelP hp g).1, det_mul]
  have hD : (blockD p).det ≠ 0 := by
    intro h0; have := det_blockD_of_mem_siegelP hp; rw [h0, zero_mul] at this; exact zero_ne_one this
  exact ⟨fun h h0 => h (by rw [h0, mul_zero]), fun h => mul_ne_zero hD h⟩

/-- $P(k)g = P(k)g'$ in `PQuot` iff $g'g^{-1} \in P(k)$. -/
lemma mk_eq_mk_iff {g g' : Sp r k} :
    (Quotient.mk _ g : PQuot r k) = Quotient.mk _ g' ↔ g' * g⁻¹ ∈ siegelP r k := by
  rw [Quotient.eq]; exact QuotientGroup.rightRel_apply

/-- **The big cell condition on cosets:** $\det C \ne 0$ for one (equivalently every) representative. -/
def IsBigCell (c : PQuot r k) : Prop :=
  Quotient.liftOn c (fun g => (blockC g).det ≠ 0) (fun g g' h => by
    have h' : g' * g⁻¹ ∈ siegelP r k := QuotientGroup.rightRel_apply.mp h
    have e : g' = (g' * g⁻¹) * g := by group
    apply propext
    rw [e, isUnit_det_blockC_mul h' g])

lemma isBigCell_mk (g : Sp r k) : IsBigCell (Quotient.mk _ g : PQuot r k) ↔ (blockC g).det ≠ 0 := Iff.rfl

/-- **The big cell** $\{P(k)g : \det C_g \ne 0\} \subseteq P(k)\backslash\mathrm{Sp}_{2r}(k)$. -/
def bigCell (r : ℕ) (k : Type*) [Field k] : Set (PQuot r k) := {c | IsBigCell c}

/-- The symmetric $r\times r$ matrices over $k$. -/
abbrev SymMat (r : ℕ) (k : Type*) [Field k] : Type _ := {B : Matrix (Fin r) (Fin r) k // Bᵀ = B}

/-- $B \mapsto P(k)\,w\,n(B)$. -/
def bigCellMap (B : SymMat r k) : PQuot r k := Quotient.mk _ (spW * spN B.1 B.2)

lemma bigCellMap_mem (B : SymMat r k) : bigCellMap B ∈ bigCell r k := by
  show (blockC (spW * spN B.1 B.2)).det ≠ 0
  rw [blockC_spW_spN, det_neg, det_one]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) one_ne_zero

/-- $(w n(B'))(w n(B))^{-1} = \begin{pmatrix}1&0\\B - B'&1\end{pmatrix}$. -/
lemma blockC_spW_spN_mul_inv (B B' : SymMat r k) :
    blockC ((spW * spN B'.1 B'.2) * (spW * spN B.1 B.2)⁻¹) = B.1 - B'.1 := by
  unfold blockC
  rw [Submonoid.coe_mul, SymplecticGroup.coe_inv, spW_spN_coe, spW_spN_coe]
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, B.2, sub_eq_add_neg]

/-- **Injectivity:** $P\,w\,n(B) = P\,w\,n(B')$ implies $B = B'$. -/
theorem bigCellMap_injective : Function.Injective (bigCellMap : SymMat r k → PQuot r k) := by
  intro B B' h
  have h1 := mk_eq_mk_iff.mp h
  have h2 : blockC ((spW * spN B'.1 B'.2) * (spW * spN B.1 B.2)⁻¹) = 0 := h1
  rw [blockC_spW_spN_mul_inv, sub_eq_zero] at h2
  exact Subtype.ext h2

/-- $C^{-1}D$ is symmetric when $\det C \ne 0$. -/
lemma inv_blockC_mul_blockD_symm (g : Sp r k) (hC : (blockC g).det ≠ 0) :
    ((blockC g)⁻¹ * blockD g)ᵀ = (blockC g)⁻¹ * blockD g := by
  have hu : IsUnit (blockC g).det := isUnit_iff_ne_zero.mpr hC
  have h := blockC_mul_blockD_transpose g
  rw [transpose_mul, transpose_nonsing_inv]
  -- (Dᵀ) (Cᵀ)⁻¹ = C⁻¹ D  ⟸  C Dᵀ = D Cᵀ
  have huT : IsUnit (blockC g)ᵀ.det := by rwa [det_transpose]
  calc (blockD g)ᵀ * ((blockC g)ᵀ)⁻¹ = (blockC g)⁻¹ * (blockC g * (blockD g)ᵀ) * ((blockC g)ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (blockC g)⁻¹ * (blockD g * (blockC g)ᵀ) * ((blockC g)ᵀ)⁻¹ := by rw [h]
    _ = (blockC g)⁻¹ * blockD g := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ huT, Matrix.mul_one]

/-- **Every big-cell coset is $P(k)\,w\,n(C^{-1}D)$.** -/
theorem mk_eq_spW_spN (g : Sp r k) (hC : (blockC g).det ≠ 0) :
    (Quotient.mk _ g : PQuot r k) = bigCellMap ⟨_, inv_blockC_mul_blockD_symm g hC⟩ := by
  have hu : IsUnit (blockC g).det := isUnit_iff_ne_zero.mpr hC
  set B0 := (blockC g)⁻¹ * blockD g
  have hB0 : B0ᵀ = B0 := inv_blockC_mul_blockD_symm g hC
  have h1 : g * (spW * spN B0 hB0)⁻¹ ∈ siegelP r k := by
    show blockC _ = 0
    unfold blockC
    rw [Submonoid.coe_mul, SymplecticGroup.coe_inv, spW_spN_coe, eq_fromBlocks g]
    simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, hB0]
    rw [show blockC g * B0 = blockD g by simp only [B0]; rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]]
    abel
  have h2 := (siegelP r k).inv_mem h1
  rw [_root_.mul_inv_rev, inv_inv] at h2
  exact mk_eq_mk_iff.mpr h2

/-- **The big cell is $\mathrm{Sym}_r(k)$:** $B \mapsto P(k)\,w\,n(B)$ is a bijection from the symmetric $r\times r$ matrices onto the big
cell $\{P(k)g : \det C_g \ne 0\}$ of $P(k)\backslash\mathrm{Sp}_{2r}(k)$; the inverse is $P(k)g \mapsto C_g^{-1}D_g$. -/
@[kb "kudla2008" "§1 (the big Bruhat cell $PwN$) [unverified]"]
def bigCellEquiv (r : ℕ) (k : Type*) [Field k] : SymMat r k ≃ bigCell r k :=
  Equiv.ofBijective (fun B => ⟨bigCellMap B, bigCellMap_mem B⟩) ⟨fun B B' h => bigCellMap_injective (congrArg Subtype.val h),
    fun ⟨c, hc⟩ => by
      induction c using Quotient.inductionOn with
      | h g =>
        have hC : (blockC g).det ≠ 0 := hc
        exact ⟨⟨_, inv_blockC_mul_blockD_symm g hC⟩, Subtype.ext (mk_eq_spW_spN g hC).symm⟩⟩

@[simp] lemma bigCellEquiv_apply (B : SymMat r k) : (bigCellEquiv r k B : PQuot r k) = bigCellMap B := rfl

/-- **The right action of $N(k)$ on the big cell is translation:** $P\,w\,n(B)\,n(X) = P\,w\,n(B + X)$. -/
theorem bigCellMap_mul_spN (B X : SymMat r k) :
    (Quotient.mk _ (spW * spN B.1 B.2 * spN X.1 X.2) : PQuot r k) =
      bigCellMap ⟨B.1 + X.1, by rw [transpose_add, B.2, X.2]⟩ := by
  unfold bigCellMap
  rw [mul_assoc, ← spN_add]

end QuadFormsKB.SiegelWeil.Forms
