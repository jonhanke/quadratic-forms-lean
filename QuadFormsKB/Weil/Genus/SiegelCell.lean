/-
# The big cell $\Omega = PwP$ of $\mathrm{Sp}_{2g}$ and the cell map $\rho$

**Layer:** pure algebra over a field $k$ (genus $g \in \mathbb N$, 0-based indices).

**Setting.** `Sp g k` and the generators $n(B)$, $m(A)$, $w$ (`spN`, `spM`, `spW`) of `Weil/Genus/Symplectic.lean`;
maps $N$ (on matrices), $A$ (on $\mathrm{GL}_g(k)$) and an element $W$ of a monoid $H$ satisfying `SiegelRelations`
(`hR`). For $\gamma \in \mathrm{Sp}_{2g}(k)$ write $a, b, c, d$ for its blocks (`blkA`, `blkB`, `blkC`, `blkD`).

**The big cell** (`bigCell`): $\Omega = \{\gamma : \det c \ne 0\}$.

**Decomposition** (`sp_eq_decomp`): for $c$ invertible, $ac^{-1}$ and $c^{-1}d$ are symmetric and
$$\gamma = n(ac^{-1})\,m(-{}^tc^{-1})\,w\,n(c^{-1}d).$$

**The cell map** (`rhoCell`): $\rho(\gamma) = N(ac^{-1})\,A(-{}^tc^{-1})\,W\,N(c^{-1}d)$ on $\Omega$, and $1$ off $\Omega$.

**Results.**
* `rhoCell_pwp`: $\rho(n(B_1)m(A_1)\,w\,n(B_2)m(A_2)) = N(B_1)A(A_1)\,W\,N(B_2)A(A_2)$ (and the product lies in
  $\Omega$, `pwp_mem_bigCell`);
* values $\rho(w) = W$, $\rho(n(B)w) = N(B)W$, $\rho(m(a)w) = A(a)W$ and the membership of these elements in $\Omega$;
* `rhoCell_mul`: $\rho(xy) = \rho(x)\rho(y)$ whenever $x, y, xy \in \Omega$.

**Method.** Block multiplication gives the decomposition (using the block relations of `Sp`, `sp_blocks`) and
the blocks of $n(B_1)m(A_1)wn(B_2)m(A_2)$; multiplicativity writes $xy = n(X_1)m(Y_1)\,[w\,n(S_0)m(Y_2)\,w]\,n(Z_2)$,
rewrites the bracket with `spW_spN_spW` (in $\mathrm{Sp}$) and `W_N_W` (in $H$), and compares both sides with
`rhoCell_pwp`. No presentation hypothesis is used: everything is unconditional given `SiegelRelations`.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Rao, Pacific J. Math. 157
(1993), §2 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Symplectic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

variable {g : ℕ} {k : Type*} [Field k]

/-- Upper-left block $a$ of $\gamma \in \mathrm{Sp}_{2g}(k)$. -/
abbrev blkA (γ : Sp g k) : Matrix (Fin g) (Fin g) k :=
  toBlocks₁₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
/-- Upper-right block $b$. -/
abbrev blkB (γ : Sp g k) : Matrix (Fin g) (Fin g) k :=
  toBlocks₁₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
/-- Lower-left block $c$. -/
abbrev blkC (γ : Sp g k) : Matrix (Fin g) (Fin g) k :=
  toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)
/-- Lower-right block $d$. -/
abbrev blkD (γ : Sp g k) : Matrix (Fin g) (Fin g) k :=
  toBlocks₂₂ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)

lemma sp_eq_fromBlocks (γ : Sp g k) :
    (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) = fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) :=
  (fromBlocks_toBlocks _).symm

/-- The symplectic block relations. -/
lemma sp_blocks (γ : Sp g k) :
    (blkA γ)ᵀ * blkC γ = (blkC γ)ᵀ * blkA γ ∧ blkC γ * (blkD γ)ᵀ = blkD γ * (blkC γ)ᵀ ∧
      (blkB γ)ᵀ * blkD γ = (blkD γ)ᵀ * blkB γ ∧
      (blkA γ)ᵀ * blkD γ - (blkC γ)ᵀ * blkB γ = 1 := by
  have hm := γ.2
  have ht := SymplecticGroup.transpose_mem γ.2
  rw [sp_eq_fromBlocks γ] at hm ht
  rw [fromBlocks_transpose] at ht
  have h1 := SymplecticGroup.fromBlocks_mem_iff.1 hm
  have h2 := SymplecticGroup.fromBlocks_mem_iff.1 ht
  simp only [transpose_transpose] at h2
  exact ⟨h1.1, h2.2.1, h1.2.1, h1.2.2⟩

/-- The big cell $\Omega = \{\gamma : \det c \ne 0\}$ (the block $c$ invertible). -/
@[kb "kudla1996" "§I.1 (the big cell $P w P$) [unverified]"]
def bigCell : Set (Sp g k) := {γ | (toBlocks₂₁ (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k)).det ≠ 0}

/-- An invertible matrix as an element of $\mathrm{GL}_g(k)$. -/
def glOfDet (c : Matrix (Fin g) (Fin g) k) (h : c.det ≠ 0) : GL (Fin g) k :=
  ((Matrix.isUnit_iff_isUnit_det c).2 (isUnit_iff_ne_zero.2 h)).unit

@[simp] lemma glOfDet_coe (c : Matrix (Fin g) (Fin g) k) (h : c.det ≠ 0) :
    ((glOfDet c h : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = c := rfl

lemma det_ne_zero_of_gl (C : GL (Fin g) k) : (C : Matrix (Fin g) (Fin g) k).det ≠ 0 :=
  isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 C.isUnit)

lemma mem_bigCell_iff {γ : Sp g k} : γ ∈ bigCell ↔ (blkC γ).det ≠ 0 := Iff.rfl

lemma exists_gl_of_mem_bigCell {γ : Sp g k} (h : γ ∈ bigCell) :
    ∃ C : GL (Fin g) k, blkC γ = C := ⟨glOfDet _ h, rfl⟩

lemma blkA_symm {γ : Sp g k} {C : GL (Fin g) k} (hc : blkC γ = C) :
    (blkA γ * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k))ᵀ =
      blkA γ * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
  obtain ⟨h1, -⟩ := sp_blocks γ
  rw [hc] at h1
  have e1 : ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (C : Matrix (Fin g) (Fin g) k)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  have e2 : (C : Matrix (Fin g) (Fin g) k) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.mul_inv C
  rw [transpose_mul]
  calc _ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ *
        ((blkA γ)ᵀ * (C : Matrix (Fin g) (Fin g) k)) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
        simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
    _ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ *
        ((C : Matrix (Fin g) (Fin g) k)ᵀ * blkA γ) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
        rw [h1]
    _ = _ := by simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]

lemma blkD_symm {γ : Sp g k} {C : GL (Fin g) k} (hc : blkC γ = C) :
    (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD γ)ᵀ =
      ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD γ := by
  obtain ⟨-, h2, -⟩ := sp_blocks γ
  rw [hc] at h2
  have e3 : ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * (C : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.inv_mul C
  have e1 : (C : Matrix (Fin g) (Fin g) k)ᵀ * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ = 1 := by
    rw [← transpose_mul, e3, transpose_one]
  rw [transpose_mul]
  calc _ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) *
        ((C : Matrix (Fin g) (Fin g) k) * (blkD γ)ᵀ) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := by
        simp only [← Matrix.mul_assoc, e3, Matrix.one_mul]
    _ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) *
        (blkD γ * (C : Matrix (Fin g) (Fin g) k)ᵀ) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := by
        rw [h2]
    _ = _ := by simp only [Matrix.mul_assoc, e1, Matrix.mul_one]


lemma spM_neg_invT_coe (C : GL (Fin g) k) :
    ((spM (-invT C) : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks (-((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) 0 0
        (-(C : Matrix (Fin g) (Fin g) k)) := by
  rw [spM_coe]
  congr 1

lemma decomp_matrix (a b c d : Matrix (Fin g) (Fin g) k) (C : GL (Fin g) k) (hc : c = C)
    (h4 : aᵀ * d - cᵀ * b = 1)
    (hs : (a * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k))ᵀ =
      a * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) :
    fromBlocks a b c d =
      fromBlocks 1 (a * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) 0 1 *
        fromBlocks (-((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) 0 0 (-(C : Matrix (Fin g) (Fin g) k)) *
        fromBlocks 0 1 (-1) 0 *
        fromBlocks 1 (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * d) 0 1 := by
  subst hc
  have e2 : (C : Matrix (Fin g) (Fin g) k) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.mul_inv C
  have e3 : ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * (C : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.inv_mul C
  have e1 : ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (C : Matrix (Fin g) (Fin g) k)ᵀ = 1 := by
    rw [← transpose_mul, e2, transpose_one]
  have hb : b = a * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * d -
      ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := by
    have h6 : aᵀ * d = 1 + (C : Matrix (Fin g) (Fin g) k)ᵀ * b := sub_eq_iff_eq_add.1 h4
    have h5 : (C : Matrix (Fin g) (Fin g) k)ᵀ * b = aᵀ * d - 1 := by rw [h6]; abel
    calc b = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * ((C : Matrix (Fin g) (Fin g) k)ᵀ * b) := by
          rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
      _ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (aᵀ * d - 1) := by rw [h5]
      _ = (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * aᵀ) * d -
          ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.mul_one]
      _ = _ := by rw [← transpose_mul, hs]
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
    add_zero, zero_add, Matrix.mul_neg, neg_neg, neg_zero]
  have x1 : a * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * (C : Matrix (Fin g) (Fin g) k) = a := by
    rw [Matrix.mul_assoc, e3, Matrix.mul_one]
  have x2 : (C : Matrix (Fin g) (Fin g) k) * (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * d) = d := by
    rw [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [x1, x2, hb]
  simp only [Matrix.mul_assoc, sub_eq_add_neg]

/-- **The decomposition on the big cell**: for $\gamma \in \mathrm{Sp}_{2g}(k)$ with $c = C$ invertible,
$\gamma = n(ac^{-1})\,m(-{}^tc^{-1})\,w\,n(c^{-1}d)$. -/
lemma sp_eq_decomp (γ : Sp g k) {C : GL (Fin g) k} (hc : blkC γ = C) :
    γ = spN (blkA γ * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) (blkA_symm hc) * spM (-invT C) * spW *
      spN (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD γ) (blkD_symm hc) := by
  apply Subtype.ext
  obtain ⟨-, -, -, h4⟩ := sp_blocks γ
  simp only [Submonoid.coe_mul, spN_coe, spM_neg_invT_coe, spW_coe]
  exact (sp_eq_fromBlocks γ).trans (decomp_matrix _ _ _ _ C hc h4 (blkA_symm hc))

open Classical in
/-- **The cell map** $\rho(\gamma) = N(ac^{-1})\,A(-{}^tc^{-1})\,W\,N(c^{-1}d)$ on the big cell
($\det c \ne 0$) and $1$ off it. -/
def rhoCell {H : Type*} [Monoid H] (N : Matrix (Fin g) (Fin g) k → H) (A : GL (Fin g) k → H) (W : H)
    (γ : Sp g k) : H :=
  if h : (blkC γ).det ≠ 0 then
    N (blkA γ * (blkC γ)⁻¹) * A (-invT (glOfDet _ h)) * W * N ((blkC γ)⁻¹ * blkD γ)
  else 1

lemma rhoCell_of_blocks {H : Type*} [Monoid H] (N : Matrix (Fin g) (Fin g) k → H)
    (A : GL (Fin g) k → H) (W : H) (γ : Sp g k) (C : GL (Fin g) k) (X Z : Matrix (Fin g) (Fin g) k)
    (hc : blkC γ = C) (ha : blkA γ = X * C) (hd : blkD γ = C * Z) :
    rhoCell N A W γ = N X * A (-invT C) * W * N Z := by
  have hdet : (blkC γ).det ≠ 0 := by rw [hc]; exact det_ne_zero_of_gl C
  unfold rhoCell
  split_ifs
  have hg : glOfDet _ hdet = C := Units.ext (by simpa using hc)
  have hi : (blkC γ)⁻¹ = ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
    rw [hc, Matrix.coe_units_inv]
  have e2 : (C : Matrix (Fin g) (Fin g) k) * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.mul_inv C
  have e3 : ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * (C : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.inv_mul C
  rw [hg, hi, ha, hd, Matrix.mul_assoc X, e2, Matrix.mul_one, ← Matrix.mul_assoc, e3, Matrix.one_mul]


private lemma invT_invT_aux (a : GL (Fin g) k) : invT (invT a) = a := Units.ext (transpose_transpose _)

lemma invT_mul (u v : GL (Fin g) k) : invT (u * v) = invT u * invT v :=
  Units.ext (by simp [transpose_mul])

lemma invT_neg (u : GL (Fin g) k) : invT (-u) = -invT u :=
  Units.ext (by simp [Units.val_neg])

section pwp

variable (B₁ B₂ : Matrix (Fin g) (Fin g) k) (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂) (A₁ A₂ : GL (Fin g) k)

lemma pwp_blkC :
    blkC (spN B₁ h₁ * spM A₁ * spW * spN B₂ h₂ * spM A₂) = ((-(invT A₁ * A₂) : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
  simp [blkC, Submonoid.coe_mul, fromBlocks_multiply, Units.val_neg]

lemma pwp_blkA :
    blkA (spN B₁ h₁ * spM A₁ * spW * spN B₂ h₂ * spM A₂) =
      B₁ * ((-(invT A₁ * A₂) : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := by
  simp [blkA, Matrix.mul_assoc, Submonoid.coe_mul, fromBlocks_multiply, Units.val_neg]

lemma pwp_blkD :
    blkD (spN B₁ h₁ * spM A₁ * spW * spN B₂ h₂ * spM A₂) =
      ((-(invT A₁ * A₂) : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) *
        (((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * B₂ * ((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) := by
  simp [blkD, Submonoid.coe_mul, fromBlocks_multiply, Units.val_neg]
  have e : (A₂ : Matrix (Fin g) (Fin g) k) * (A₂ : Matrix (Fin g) (Fin g) k)⁻¹ = 1 := by
    rw [← Matrix.coe_units_inv]; exact Units.mul_inv A₂
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (A₂ : Matrix (Fin g) (Fin g) k), e, Matrix.one_mul]

end pwp


/-- $A\,(A^{-1}TA^{-\mathsf T})\,A^{\mathsf T} = T$ for $A \in \mathrm{GL}_g(k)$. -/
lemma conj_inv_conj (Y : GL (Fin g) k) (T : Matrix (Fin g) (Fin g) k) :
    (Y : Matrix (Fin g) (Fin g) k) *
      (((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * T * ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) *
        (Y : Matrix (Fin g) (Fin g) k)ᵀ = T := by
  have h1 : (Y : Matrix (Fin g) (Fin g) k) * ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = 1 :=
    Units.mul_inv Y
  have h2 : ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (Y : Matrix (Fin g) (Fin g) k)ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  calc _ = ((Y : Matrix (Fin g) (Fin g) k) * ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) * T *
        (((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * (Y : Matrix (Fin g) (Fin g) k)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = T := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

lemma symm_conj_inv {T : Matrix (Fin g) (Fin g) k} (hT : Tᵀ = T) (Y : GL (Fin g) k) :
    (((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * T * ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ)ᵀ =
      ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * T * ((Y⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := by
  simp [transpose_mul, hT, Matrix.mul_assoc]

/-- **The cell map on a product $n(B_1)\,m(A_1)\,w\,n(B_2)\,m(A_2)$** (hypotheses: `hR` the Siegel relations for
$N, A, W$; $B_1, B_2$ symmetric by `h₁`, `h₂`; $A_1, A_2 \in \mathrm{GL}_g(k)$):
$$\rho(n(B_1)m(A_1)\,w\,n(B_2)m(A_2)) = N(B_1)A(A_1)\,W\,N(B_2)A(A_2).$$
*Proof:* $c = -{}^tA_1^{-1}A_2$, so $ac^{-1} = B_1$, $A(-{}^tc^{-1}) = A(A_1)A({}^tA_2^{-1})$,
$c^{-1}d = A_2^{-1}B_2\,{}^tA_2^{-1}$; then `A_N` and `W_A` move $A(A_2)$ past $N$ and $W$. -/
@[kb "kudla1996" "§I.1 (the map $\\rho$ on $PwP$) [unverified]"]
theorem rhoCell_pwp {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (B₁ B₂ : Matrix (Fin g) (Fin g) k) (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂)
    (A₁ A₂ : GL (Fin g) k) :
    rhoCell N A W (spN B₁ h₁ * spM A₁ * spW * spN B₂ h₂ * spM A₂) = N B₁ * A A₁ * W * N B₂ * A A₂ := by
  have hZ := symm_conj_inv h₂ A₂
  rw [rhoCell_of_blocks N A W _ (-(invT A₁ * A₂)) B₁ _ (pwp_blkC B₁ B₂ h₁ h₂ A₁ A₂)
    (pwp_blkA B₁ B₂ h₁ h₂ A₁ A₂) (pwp_blkD B₁ B₂ h₁ h₂ A₁ A₂)]
  have hneg : -invT (-(invT A₁ * A₂)) = A₁ * invT A₂ := by
    rw [invT_neg, invT_mul, invT_invT_aux, neg_neg]
  rw [hneg, hR.A_mul]
  have hBZ : N B₂ * A A₂ = A A₂ * N (((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * B₂ *
      ((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) := by
    rw [hR.A_N A₂ _ hZ, conj_inv_conj]
  calc _ = N B₁ * A A₁ * (A (invT A₂) * W) * N (((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * B₂ *
      ((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) := by simp only [Monoid.mul_assoc]
    _ = N B₁ * A A₁ * (W * A A₂) * N (((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * B₂ *
      ((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) := by rw [hR.W_A]
    _ = N B₁ * A A₁ * W * (A A₂ * N (((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * B₂ *
      ((A₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ)) := by simp only [Monoid.mul_assoc]
    _ = _ := by rw [← hBZ]; simp only [Monoid.mul_assoc]


/-! ### Values on the generators and the big cell -/

lemma pwp_mem_bigCell (B₁ B₂ : Matrix (Fin g) (Fin g) k) (h₁ : B₁ᵀ = B₁) (h₂ : B₂ᵀ = B₂) (A₁ A₂ : GL (Fin g) k) :
    spN B₁ h₁ * spM A₁ * spW * spN B₂ h₂ * spM A₂ ∈ bigCell := by
  show (blkC _).det ≠ 0
  rw [pwp_blkC]
  exact det_ne_zero_of_gl _

/-- $w \in \Omega$. -/
lemma spW_mem_bigCell : (spW : Sp g k) ∈ bigCell := by
  have h := pwp_mem_bigCell (0 : Matrix (Fin g) (Fin g) k) 0 (by simp) (by simp) 1 1
  simpa only [spN_zero, spM_one, one_mul, mul_one] using h

/-- $n(B)\,w \in \Omega$. -/
lemma spN_spW_mem_bigCell (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) : (spN B hB * spW : Sp g k) ∈ bigCell := by
  have h := pwp_mem_bigCell B (0 : Matrix (Fin g) (Fin g) k) hB (by simp) 1 1
  simpa only [spN_zero, spM_one, mul_one] using h

/-- $m(a)\,w \in \Omega$. -/
lemma spM_spW_mem_bigCell (a : GL (Fin g) k) : (spM a * spW : Sp g k) ∈ bigCell := by
  have h := pwp_mem_bigCell (0 : Matrix (Fin g) (Fin g) k) 0 (by simp) (by simp) a 1
  simpa only [spN_zero, spM_one, one_mul, mul_one] using h

/-- $\rho(w) = W$ (hypothesis `hR`: the Siegel relations). -/
theorem rhoCell_spW {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) : rhoCell N A W (spW : Sp g k) = W := by
  have h := rhoCell_pwp hR 0 0 (by simp) (by simp) 1 1
  simpa only [spN_zero, spM_one, one_mul, mul_one, hR.N_zero, hR.A_one] using h

/-- $\rho(n(B)\,w) = N(B)\,W$ ($B$ symmetric by `hB`). -/
theorem rhoCell_spN_spW {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) :
    rhoCell N A W (spN B hB * spW : Sp g k) = N B * W := by
  have h := rhoCell_pwp hR B 0 hB (by simp) 1 1
  simpa only [spN_zero, spM_one, one_mul, mul_one, hR.N_zero, hR.A_one] using h

/-- $\rho(m(a)\,w) = A(a)\,W$ ($a \in \mathrm{GL}_g(k)$). -/
theorem rhoCell_spM_spW {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (a : GL (Fin g) k) : rhoCell N A W (spM a * spW : Sp g k) = A a * W := by
  have h := rhoCell_pwp hR 0 0 (by simp) (by simp) a 1
  simpa only [spN_zero, spM_one, one_mul, mul_one, hR.N_zero, hR.A_one] using h


/-! ### Multiplicativity on the big cell -/

/-- $-S^{-1}$ as a matrix, for $S \in \mathrm{GL}_g(k)$. -/
abbrev negInv (S : GL (Fin g) k) : Matrix (Fin g) (Fin g) k := -((S⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)

lemma negInv_symm {S : GL (Fin g) k} (hS : (S : Matrix (Fin g) (Fin g) k)ᵀ = S) : (negInv S)ᵀ = negInv S :=
  symm_neg_inv hS

lemma sp_core (Y Sg : GL (Fin g) k) (hS : (Sg : Matrix (Fin g) (Fin g) k)ᵀ = Sg) (T : Matrix (Fin g) (Fin g) k)
    (hT : Tᵀ = T) (hTS : T = (Y : Matrix (Fin g) (Fin g) k) * Sg * (Y : Matrix (Fin g) (Fin g) k)ᵀ) :
    spW * spN T hT * spM Y * spW =
      spM (invT Y) * (spN (negInv Sg) (negInv_symm hS) * spM (-Sg⁻¹) * spW * spN (negInv Sg) (negInv_symm hS)) := by
  subst hTS
  have h1 := spM_spN Y (Sg : Matrix (Fin g) (Fin g) k) hS
  calc _ = spW * (spN _ hT * spM Y) * spW := by simp only [mul_assoc]
    _ = spW * (spM Y * spN (Sg : Matrix (Fin g) (Fin g) k) hS) * spW := by rw [h1]
    _ = spW * spM Y * spN (Sg : Matrix (Fin g) (Fin g) k) hS * spW := by simp only [mul_assoc]
    _ = spM (invT Y) * spW * spN (Sg : Matrix (Fin g) (Fin g) k) hS * spW := by rw [spW_spM]
    _ = spM (invT Y) * (spW * spN (Sg : Matrix (Fin g) (Fin g) k) hS * spW) := by simp only [mul_assoc]
    _ = _ := by rw [spW_spN_spW Sg hS]

lemma H_core {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (Y Sg : GL (Fin g) k) (hS : (Sg : Matrix (Fin g) (Fin g) k)ᵀ = Sg)
    (T : Matrix (Fin g) (Fin g) k)
    (hTS : T = (Y : Matrix (Fin g) (Fin g) k) * Sg * (Y : Matrix (Fin g) (Fin g) k)ᵀ) :
    W * N T * A Y * W = A (invT Y) * (N (negInv Sg) * A (-Sg⁻¹) * W * N (negInv Sg)) := by
  have hA : A Y * N Sg = N T * A Y := by rw [hR.A_N Y _ hS, ← hTS]
  calc _ = W * (N T * A Y) * W := by simp only [Monoid.mul_assoc]
    _ = W * (A Y * N Sg) * W := by rw [hA]
    _ = (W * A Y) * N Sg * W := by simp only [Monoid.mul_assoc]
    _ = A (invT Y) * (W * N Sg * W) := by rw [hR.W_A]; simp only [Monoid.mul_assoc]
    _ = _ := by rw [hR.W_N_W Sg hS]

lemma blkC_seven (X₁ T Z₂ : Matrix (Fin g) (Fin g) k) (h₁ : X₁ᵀ = X₁) (hT : Tᵀ = T) (h₂ : Z₂ᵀ = Z₂)
    (Y₁ Y₂ : GL (Fin g) k) :
    blkC (spN X₁ h₁ * spM Y₁ * spW * spN T hT * spM Y₂ * spW * spN Z₂ h₂) =
      (invT Y₁ : Matrix (Fin g) (Fin g) k) * T * (invT Y₂ : Matrix (Fin g) (Fin g) k) := by
  simp [blkC, Submonoid.coe_mul, fromBlocks_multiply, Matrix.mul_assoc]


/-- $PBP^{\mathsf T}$ for $P \in \mathrm{GL}_g(k)$ (conjugation of $B$ by $P$). -/
abbrev conjMat (P : GL (Fin g) k) (B : Matrix (Fin g) (Fin g) k) : Matrix (Fin g) (Fin g) k :=
  (P : Matrix (Fin g) (Fin g) k) * B * (P : Matrix (Fin g) (Fin g) k)ᵀ

lemma conjMat_symm (P : GL (Fin g) k) {B : Matrix (Fin g) (Fin g) k} (hB : Bᵀ = B) : (conjMat P B)ᵀ = conjMat P B := by
  simp [transpose_mul, hB, Matrix.mul_assoc]

lemma spM_spN' (P : GL (Fin g) k) (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) :
    spM P * spN B hB = spN (conjMat P B) (conjMat_symm P hB) * spM P := spM_spN P B hB

/-- **The multiplicativity computation for pieces** $x = n(X_1)m(Y_1)\,w\,n(Z_1)$,
$y = n(X_2)m(Y_2)\,w\,n(Z_2)$ (hypotheses: `hR` the Siegel relations; $X_i, Z_i$ symmetric; $S \in
\mathrm{GL}_g(k)$ symmetric with $Z_1 + X_2 = Y_2\,S\,{}^tY_2$, i.e. `hT`):
$\rho(xy) = \rho(x)\rho(y)$ in terms of $N, A, W$. -/
theorem rhoCell_mul_core {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (X₁ Z₁ X₂ Z₂ : Matrix (Fin g) (Fin g) k)
    (hX₁ : X₁ᵀ = X₁) (hZ₁ : Z₁ᵀ = Z₁) (hX₂ : X₂ᵀ = X₂) (hZ₂ : Z₂ᵀ = Z₂)
    (Y₁ Y₂ Sg : GL (Fin g) k) (hS : (Sg : Matrix (Fin g) (Fin g) k)ᵀ = Sg)
    (hT : Z₁ + X₂ = (Y₂ : Matrix (Fin g) (Fin g) k) * Sg * (Y₂ : Matrix (Fin g) (Fin g) k)ᵀ) :
    rhoCell N A W ((spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂)) =
      (N X₁ * A Y₁ * W * N Z₁) * (N X₂ * A Y₂ * W * N Z₂) := by
  have hT' : (Z₁ + X₂)ᵀ = Z₁ + X₂ := by rw [transpose_add, hZ₁, hX₂]
  have hV := negInv_symm hS
  have hU := conjMat_symm (Y₁ * invT Y₂) hV
  have hXU : (X₁ + conjMat (Y₁ * invT Y₂) (negInv Sg))ᵀ = X₁ + conjMat (Y₁ * invT Y₂) (negInv Sg) := by
    rw [transpose_add, hX₁, hU]
  have hVZ : (negInv Sg + Z₂)ᵀ = negInv Sg + Z₂ := by rw [transpose_add, hV, hZ₂]
  have E : (spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂) =
      spN (X₁ + conjMat (Y₁ * invT Y₂) (negInv Sg)) hXU * spM (Y₁ * invT Y₂ * (-Sg⁻¹)) * spW *
        spN (negInv Sg + Z₂) hVZ * spM 1 := by
    have e1 : spN Z₁ hZ₁ * spN X₂ hX₂ = spN (Z₁ + X₂) hT' := (spN_add Z₁ X₂ hZ₁ hX₂).symm
    have hprod : (spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂) =
        spN X₁ hX₁ * spM Y₁ * (spW * spN (Z₁ + X₂) hT' * spM Y₂ * spW) * spN Z₂ hZ₂ := by
      rw [← e1]; simp only [mul_assoc]
    have hM : ∀ z : Sp g k, spM Y₁ * (spM (invT Y₂) * (spN (negInv Sg) hV * z)) =
        spN (conjMat (Y₁ * invT Y₂) (negInv Sg)) hU * (spM Y₁ * (spM (invT Y₂) * z)) := by
      intro z
      have h := spM_spN' (Y₁ * invT Y₂) (negInv Sg) hV
      rw [spM_mul] at h
      calc _ = (spM Y₁ * spM (invT Y₂) * spN (negInv Sg) hV) * z := by simp only [mul_assoc]
        _ = (spN (conjMat (Y₁ * invT Y₂) (negInv Sg)) hU * (spM Y₁ * spM (invT Y₂))) * z := by rw [h]
        _ = _ := by simp only [mul_assoc]
    rw [hprod, sp_core Y₂ Sg hS _ hT' hT, spN_add X₁ _ hX₁ hU, spN_add _ Z₂ hV hZ₂, spM_mul, spM_mul,
      spM_one, mul_one]
    simp only [mul_assoc, hM]
  have hA : ∀ z : H, A Y₁ * (A (invT Y₂) * (N (negInv Sg) * z)) =
      N (conjMat (Y₁ * invT Y₂) (negInv Sg)) * (A Y₁ * (A (invT Y₂) * z)) := by
    intro z
    have h := hR.A_N (Y₁ * invT Y₂) (negInv Sg) hV
    rw [hR.A_mul] at h
    calc _ = (A Y₁ * A (invT Y₂) * N (negInv Sg)) * z := by simp only [Monoid.mul_assoc]
      _ = (N (conjMat (Y₁ * invT Y₂) (negInv Sg)) * (A Y₁ * A (invT Y₂))) * z := by rw [h]
      _ = _ := by simp only [Monoid.mul_assoc]
  have hN : N Z₁ * N X₂ = N (Z₁ + X₂) := (hR.N_add Z₁ X₂ hZ₁ hX₂).symm
  have hH := H_core hR Y₂ Sg hS (Z₁ + X₂) hT
  rw [E, rhoCell_pwp hR _ _ hXU hVZ _ _, hR.N_add X₁ _ hX₁ hU, hR.N_add _ Z₂ hV hZ₂, hR.A_mul, hR.A_mul,
    hR.A_one, Monoid.mul_one]
  calc _ = N X₁ * A Y₁ * (A (invT Y₂) * (N (negInv Sg) * A (-Sg⁻¹) * W * N (negInv Sg))) * N Z₂ := by
        simp only [Monoid.mul_assoc, hA]
    _ = N X₁ * A Y₁ * (W * N (Z₁ + X₂) * A Y₂ * W) * N Z₂ := by rw [hH]
    _ = _ := by rw [← hN]; simp only [Monoid.mul_assoc]


/-- The cell map in terms of the decomposition: if $c = C$ is invertible then
$\rho(\gamma) = N(aC^{-1})\,A(-{}^tC^{-1})\,W\,N(C^{-1}d)$. -/
lemma rhoCell_eq {H : Type*} [Monoid H] (N : Matrix (Fin g) (Fin g) k → H) (A : GL (Fin g) k → H) (W : H)
    (γ : Sp g k) {C : GL (Fin g) k} (hc : blkC γ = C) :
    rhoCell N A W γ = N (blkA γ * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) * A (-invT C) * W *
      N (((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD γ) :=
  rhoCell_of_blocks N A W γ C _ _ hc
    (by rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one])
    (by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])

/-- Multiplicativity for decomposed pieces, with the big-cell hypothesis `hxy` on the product. -/
theorem rhoCell_mul_aux {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) (X₁ Z₁ X₂ Z₂ : Matrix (Fin g) (Fin g) k)
    (hX₁ : X₁ᵀ = X₁) (hZ₁ : Z₁ᵀ = Z₁) (hX₂ : X₂ᵀ = X₂) (hZ₂ : Z₂ᵀ = Z₂) (Y₁ Y₂ : GL (Fin g) k)
    (hxy : (spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂) ∈ bigCell) :
    rhoCell N A W ((spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂)) =
      (N X₁ * A Y₁ * W * N Z₁) * (N X₂ * A Y₂ * W * N Z₂) := by
  have hT' : (Z₁ + X₂)ᵀ = Z₁ + X₂ := by rw [transpose_add, hZ₁, hX₂]
  have e1 : spN Z₁ hZ₁ * spN X₂ hX₂ = spN (Z₁ + X₂) hT' := (spN_add Z₁ X₂ hZ₁ hX₂).symm
  have hprod : (spN X₁ hX₁ * spM Y₁ * spW * spN Z₁ hZ₁) * (spN X₂ hX₂ * spM Y₂ * spW * spN Z₂ hZ₂) =
      spN X₁ hX₁ * spM Y₁ * spW * spN (Z₁ + X₂) hT' * spM Y₂ * spW * spN Z₂ hZ₂ := by
    rw [← e1]; simp only [mul_assoc]
  rw [hprod, mem_bigCell_iff, blkC_seven] at hxy
  have hdet : (Z₁ + X₂).det ≠ 0 := by
    intro h0
    apply hxy
    rw [det_mul, det_mul, h0]
    simp
  have hc : ((Y₂⁻¹ * glOfDet _ hdet * invT Y₂ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) =
      ((Y₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * (Z₁ + X₂) *
        ((Y₂⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ := rfl
  refine rhoCell_mul_core hR X₁ Z₁ X₂ Z₂ hX₁ hZ₁ hX₂ hZ₂ Y₁ Y₂ (Y₂⁻¹ * glOfDet _ hdet * invT Y₂) ?_ ?_
  · rw [hc]; exact symm_conj_inv hT' Y₂
  · rw [hc]; exact (conj_inv_conj Y₂ _).symm

/-- **Multiplicativity of the cell map on the big cell** (hypotheses: `hR` the Siegel relations for $N, A, W$;
$x, y, xy \in \Omega$): $\rho(xy) = \rho(x)\rho(y)$.
*Proof:* write $x = n(X_1)m(Y_1)\,w\,n(Z_1)$, $y = n(X_2)m(Y_2)\,w\,n(Z_2)$ (`sp_eq_decomp`); then
$xy = n(X_1)m(Y_1)\,[\,w\,n(S_0)\,m(Y_2)\,w\,]\,n(Z_2)$ with $S_0 = Z_1 + X_2$, whose lower-left block is
${}^tY_1^{-1}S_0\,{}^tY_2^{-1}$, so $S_0$ is invertible; `W_N_W` rewrites the bracket and `A_N`, `W_A`, `N_add`
reorganize both sides to $N(\cdot)A(\cdot)\,W\,N(\cdot)$ (`rhoCell_mul_core`, `rhoCell_pwp`). -/
@[kb "kudla1996" "§I.1 (the cell map $\\rho$ is multiplicative when $x, y, xy \\in PwP$) [unverified]"]
theorem rhoCell_mul {H : Type*} [Monoid H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}
    (hR : SiegelRelations N A W) {x y : Sp g k} (hx : x ∈ bigCell) (hy : y ∈ bigCell) (hxy : x * y ∈ bigCell) :
    rhoCell N A W (x * y) = rhoCell N A W x * rhoCell N A W y := by
  obtain ⟨Cx, hCx⟩ := exists_gl_of_mem_bigCell hx
  obtain ⟨Cy, hCy⟩ := exists_gl_of_mem_bigCell hy
  have dx := sp_eq_decomp x hCx
  have dy := sp_eq_decomp y hCy
  have h := rhoCell_mul_aux hR _ _ _ _ (blkA_symm hCx) (blkD_symm hCx) (blkA_symm hCy) (blkD_symm hCy)
    (-invT Cx) (-invT Cy) (by rw [← dx, ← dy]; exact hxy)
  rw [← dx, ← dy] at h
  rw [h, rhoCell_eq N A W x hCx, rhoCell_eq N A W y hCy]

end QuadFormsKB.WeilRep.Genus
