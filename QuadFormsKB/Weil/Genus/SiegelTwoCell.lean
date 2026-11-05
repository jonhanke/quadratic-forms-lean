/-
# The presentation of $\mathrm{Sp}_{2g}(k)$ from two linear-algebra conditions, for every field

**Layer:** pure algebra over a field $k$ (every field, finite or not).

**Setting.** `Sp g k` with the generators $n(B)$, $m(a)$, $w$ (`spN`, `spM`, `spW`), the big cell
$\Omega = \{\gamma : \det c \ne 0\}$ (`bigCell`) and the cell map $\rho_\Omega$ (`rhoCell`) of
`Weil/Genus/SiegelCell.lean`, for maps $N$, $A$ and an element $W$ of a group $H$ satisfying `SiegelRelations`.
For $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix}$ and symmetric $T$ put $z_T = n(T)\,w$; then
$z_T \in \Omega$ and $\gamma z_T \in \Omega \iff \det(cT + d) \ne 0$ (`toBlocks₂₁_mul_spN_spW`).

**The two conditions** (linear algebra only; named inputs):
* `CellGraphConnected g k`: if $\det c = 0$, any two symmetric $T, T'$ with $\det(cT + d) \ne 0 \ne \det(cT' + d)$ are
  joined by a chain $T = T_0, T_1, \dots, T_n = T'$ of such matrices with $\det(T_{i} - T_{i+1}) \ne 0$;
* `TwoRowTransversal g k`: if $\det c = 0$ or $\det a = 0$, some symmetric $T$ has $\det(cT + d) \ne 0$ and
  $\det(aT + b) \ne 0$.
In terms of Lagrangian subspaces: the Lagrangians transverse to two given non-transverse Lagrangians form a connected
graph under transversality, and three Lagrangians of which two meet and two are transverse have a common transversal.
The second is proved for every field in `TwoRowTransversal.lean` (`twoRowTransversal`); the first remains a named input.

**Results.** `siegelPresentation_of_twoCell`: the two conditions imply the named input `SiegelPresentation g k`.
`siegelPresentationSmallField_of_twoCell`: the conditions for the finite fields with at most $3g$ elements imply the
smaller named input `SiegelPresentationSmallField g k` of `SiegelPresSmall.lean`.

**Method** (no genericity, so no condition on the size of $k$). Put
$F(\gamma) = \rho_\Omega(\gamma z_T)\,\rho_\Omega(z_T)^{-1}$ for any symmetric $T$ with $\det(cT + d) \ne 0$ (such $T$
exists for every $\gamma$, `exists_symm_det_ne`). It does not depend on $T$: for $\gamma \in \Omega$ it equals
$\rho_\Omega(\gamma)$ (`rhoCell_mul`), and otherwise along an edge $T \sim T'$ of the chain
$u = z_T^{-1}z_{T'} \in \Omega$ (its lower-left block is $T - T'$), so `rhoCell_mul` gives
$\rho_\Omega(\gamma z_{T'}) = \rho_\Omega(\gamma z_T)\rho_\Omega(u)$ and $\rho_\Omega(z_{T'}) = \rho_\Omega(z_T)\rho_\Omega(u)$.
Then $F(n(B)\gamma) = N(B)F(\gamma)$, $F(m(a)\gamma) = A(a)F(\gamma)$ (the same $T$ works) and $F(w\gamma) = WF(\gamma)$
(if $\gamma, w\gamma \in \Omega$ by `rhoCell_mul`; otherwise with the $T$ of `TwoRowTransversal`, for which $z_T$, $\gamma z_T$ and
$w\gamma z_T$ all lie in $\Omega$). Since $n(B)$, $m(a)$, $w$ generate $\mathrm{Sp}_{2g}(k)$ as a monoid, $\varphi(\gamma) =
F(\gamma)F(1)^{-1}$ is a homomorphism with the required values (`exists_hom_of_left_action`).

**Evidence.** Both conditions are checked by brute force over all of $\mathrm{Sp}_{2g}(\mathbb F_q)$ for
$(g, q) = (1, 2), (1, 5), (2, 2), (2, 3), (3, 2)$ (checked by a computer calculation, outside Lean) and, in the transversality form, for
$(2, 5), (3, 3), (4, 2)$ (likewise). The graph of `CellGraphConnected` even has diameter at
most $2$ for $(g, q) = (2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (5, 2)$ (likewise). The four-Lagrangian
statement without the cross-transversality hypothesis is false (by a computer search, outside Lean), so the
hypotheses of the conditions cannot be dropped.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Weil, Acta Math. 111 (1964),
§§1–2 (the big-cell construction) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelPresSmall

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u v

/-! ### A homomorphism from a function intertwining left multiplication by generators -/

section Abstract

variable {G H : Type*} [Monoid G] [Group H]

/-- **A homomorphism from a left-equivariant function.** Let $s : \iota \to G$ be a family generating the monoid
$G$ (`hS`), and let $F : G \to H$ and $\sigma : \iota \to H$ satisfy $F(s_i x) = \sigma_i F(x)$ for all $i$ and $x$
(`hF`). Then $\varphi(x) = F(x)F(1)^{-1}$ is a monoid homomorphism with $\varphi(s_i) = \sigma_i$. -/
theorem exists_hom_of_left_action {ι : Type*} (s : ι → G) (hS : Submonoid.closure (Set.range s) = ⊤)
    (F : G → H) (σ : ι → H) (hF : ∀ i x, F (s i * x) = σ i * F x) :
    ∃ φ : G →* H, ∀ i, φ (s i) = σ i := by
  let φ : G → H := fun x => F x * (F 1)⁻¹
  have hs : ∀ i, φ (s i) = σ i := by
    intro i
    have h1 := hF i 1
    rw [mul_one] at h1
    simp [φ, h1]
  have key : ∀ y, ∀ x, F (y * x) = φ y * F x := by
    intro y
    have hy : y ∈ Submonoid.closure (Set.range s) := by rw [hS]; trivial
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro x
      rw [hs, hF]
    | one => intro x; simp [φ]
    | mul y₁ y₂ _ _ ih₁ ih₂ =>
      intro x
      have h12 := ih₁ y₂
      rw [mul_assoc, ih₁, ih₂]
      show _ = F (y₁ * y₂) * (F 1)⁻¹ * F x
      rw [h12]
      simp only [φ]
      group
  exact ⟨MonoidHom.mk' φ fun x y => by simp only [φ, key x y]; group, hs⟩

end Abstract

variable {g : ℕ} {k : Type v} [Field k]

/-! ### The linear-algebra conditions -/

/-- $T$ is symmetric and $\det(cT + d) \ne 0$ for the lower blocks $c$, $d$ of $\gamma$ (equivalently
$\gamma\,n(T)\,w \in \Omega$). -/
def CellGood (γ : Sp g k) (T : Matrix (Fin g) (Fin g) k) : Prop :=
  Tᵀ = T ∧ (blkC γ * T + blkD γ).det ≠ 0

/-- The edge relation of the graph of `CellGraphConnected`: both ends good for $\gamma$ and
$\det(T - T') \ne 0$. -/
def CellEdge (γ : Sp g k) (T T' : Matrix (Fin g) (Fin g) k) : Prop :=
  CellGood γ T ∧ CellGood γ T' ∧ (T - T').det ≠ 0

/-- **Connectedness of the transversality graph** (a named input; linear algebra over $k$), field `connected`: for
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{Sp}_{2g}(k)$ with $\det c = 0$ and symmetric $T, T'$ with
$\det(cT + d) \ne 0$ and $\det(cT' + d) \ne 0$, there is a chain from $T$ to $T'$ of symmetric $T_i$ with
$\det(cT_i + d) \ne 0$ and $\det(T_i - T_{i+1}) \ne 0$ (the reflexive-transitive closure of `CellEdge γ`).
Equivalently: the Lagrangians transverse to two given non-transverse Lagrangians form a connected graph, two of them
adjacent when transverse. Checked by computer for small $(g, q)$ (module docstring). -/
@[kb "kudla1996" "§I.1 (the big cell $PwP$ and its translates; linear algebra behind the presentation of $\\mathrm{Sp}_{2g}$) [unverified]"]
structure CellGraphConnected (g : ℕ) (k : Type v) [Field k] : Prop where
  connected : ∀ γ : Sp g k, (blkC γ).det = 0 → ∀ T T' : Matrix (Fin g) (Fin g) k,
    CellGood γ T → CellGood γ T' → Relation.ReflTransGen (CellEdge γ) T T'

/-- **A common transversal for the two rows** (a named input; linear algebra over $k$), field `two_rows`: for
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{Sp}_{2g}(k)$ with $\det c = 0$ or $\det a = 0$, some
symmetric $T$ has $\det(cT + d) \ne 0$ and $\det(aT + b) \ne 0$ (that is, $\gamma\,n(T)\,w$ and $w\gamma\,n(T)\,w$
both lie in the big cell). Checked by computer for small $(g, q)$ (module docstring). -/
@[kb "kudla1996" "§I.1 (the big cell $PwP$ and its translates; linear algebra behind the presentation of $\\mathrm{Sp}_{2g}$) [unverified]"]
structure TwoRowTransversal (g : ℕ) (k : Type v) [Field k] : Prop where
  two_rows : ∀ γ : Sp g k, ((blkC γ).det = 0 ∨ (blkA γ).det = 0) →
    ∃ T : Matrix (Fin g) (Fin g) k, Tᵀ = T ∧ (blkC γ * T + blkD γ).det ≠ 0 ∧ (blkA γ * T + blkB γ).det ≠ 0

/-! ### Block computations -/

lemma cellGood_iff_mem (γ : Sp g k) {T : Matrix (Fin g) (Fin g) k} (hT : Tᵀ = T) :
    γ * (spN T hT * spW) ∈ bigCell ↔ (blkC γ * T + blkD γ).det ≠ 0 := by
  rw [mem_bigCell_iff, blkC, toBlocks₂₁_mul_spN_spW, det_neg]
  simp [blkC, blkD]

lemma blkC_spW_mul (γ : Sp g k) : blkC (spW * γ) = -blkA γ := by
  have h : ((spW * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks 0 1 (-1) 0 * fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  rw [blkC, h, fromBlocks_multiply]
  simp

lemma blkD_spW_mul (γ : Sp g k) : blkD (spW * γ) = -blkB γ := by
  have h : ((spW * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks 0 1 (-1) 0 * fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  rw [blkD, h, fromBlocks_multiply]
  simp

lemma blkC_spN_mul (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) (γ : Sp g k) :
    blkC (spN B hB * γ) = blkC γ ∧ blkD (spN B hB * γ) = blkD γ := by
  have h : ((spN B hB * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks 1 B 0 1 * fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  rw [blkC, blkD, h, fromBlocks_multiply]
  simp

lemma blkC_spM_mul (a : GL (Fin g) k) (γ : Sp g k) :
    blkC (spM a * γ) = ((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * blkC γ ∧
      blkD (spM a * γ) = ((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ * blkD γ := by
  have h : ((spM a * γ : Sp g k) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) k) =
      fromBlocks (a : Matrix (Fin g) (Fin g) k) 0 0 (((a⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)ᵀ) *
        fromBlocks (blkA γ) (blkB γ) (blkC γ) (blkD γ) := by
    rw [← sp_eq_fromBlocks]; rfl
  rw [blkC, blkD, h, fromBlocks_multiply]
  simp

/-- The lower unipotent element $\begin{pmatrix}1&0\\S&1\end{pmatrix}$, $S$ symmetric. -/
def spLow (S : Matrix (Fin g) (Fin g) k) (hS : Sᵀ = S) : Sp g k :=
  ⟨fromBlocks 1 0 S 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp [hS], by simp, by simp⟩⟩

/-- $z_T^{-1} z_{T'} = \begin{pmatrix}1&0\\T - T'&1\end{pmatrix}$ for $z_T = n(T)\,w$. -/
lemma spN_spW_inv_mul (T T' : Matrix (Fin g) (Fin g) k) (hT : Tᵀ = T) (hT' : T'ᵀ = T') :
    (spN T hT * spW)⁻¹ * (spN T' hT' * spW) = spLow (T - T') (by rw [transpose_sub, hT, hT']) := by
  rw [inv_mul_eq_iff_eq_mul]
  apply Subtype.ext
  simp only [Submonoid.coe_mul, spN_coe, spW_coe, spLow, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg]
  congr 1
  abel

lemma spLow_mem_bigCell {S : Matrix (Fin g) (Fin g) k} (hS : Sᵀ = S) (h : S.det ≠ 0) :
    spLow S hS ∈ bigCell := by
  rw [mem_bigCell_iff]
  simpa [blkC, spLow] using h

/-! ### The function $F$ -/

section Group

variable {H : Type*} [Group H] {N : Matrix (Fin g) (Fin g) k → H} {A : GL (Fin g) k → H} {W : H}

/-- $\rho_\Omega(\gamma z_T)\,\rho_\Omega(z_T)^{-1}$ for $z_T = n(T)\,w$ ($T$ symmetric; junk otherwise). -/
def cellVal (N : Matrix (Fin g) (Fin g) k → H) (A : GL (Fin g) k → H) (W : H) (γ : Sp g k)
    (T : Matrix (Fin g) (Fin g) k) : H :=
  rhoCell N A W (γ * spNext T * spW) * (rhoCell N A W (spNext T * spW))⁻¹

lemma cellVal_eq (γ : Sp g k) {T : Matrix (Fin g) (Fin g) k} (hT : Tᵀ = T) :
    cellVal N A W γ T = rhoCell N A W (γ * (spN T hT * spW)) * (rhoCell N A W (spN T hT * spW))⁻¹ := by
  rw [cellVal, spNext_of_symm hT, mul_assoc]

/-- On the big cell the value is $\rho_\Omega(\gamma)$. -/
lemma cellVal_of_mem (hR : SiegelRelations N A W) {γ : Sp g k} (hγ : γ ∈ bigCell)
    {T : Matrix (Fin g) (Fin g) k} (hT : CellGood γ T) : cellVal N A W γ T = rhoCell N A W γ := by
  rw [cellVal_eq γ hT.1, rhoCell_mul hR hγ (spN_spW_mem_bigCell T hT.1) ((cellGood_iff_mem γ hT.1).2 hT.2),
    mul_inv_cancel_right]

/-- Along an edge the value does not change. -/
lemma cellVal_edge (hR : SiegelRelations N A W) {γ : Sp g k} {T T' : Matrix (Fin g) (Fin g) k}
    (h : CellEdge γ T T') : cellVal N A W γ T = cellVal N A W γ T' := by
  obtain ⟨⟨hT, hgT⟩, ⟨hT', hgT'⟩, hd⟩ := h
  have hS : (T - T')ᵀ = T - T' := by rw [transpose_sub, hT, hT']
  have hu : spLow (T - T') hS ∈ bigCell := spLow_mem_bigCell hS hd
  have hz : spN T' hT' * spW = (spN T hT * spW) * spLow (T - T') hS := by
    rw [← spN_spW_inv_mul T T' hT hT', mul_inv_cancel_left]
  have e1 := rhoCell_mul hR (spN_spW_mem_bigCell T hT) hu (hz ▸ spN_spW_mem_bigCell T' hT')
  have e2 := rhoCell_mul hR ((cellGood_iff_mem γ hT).2 hgT) hu
    (by rw [mul_assoc, ← hz]; exact (cellGood_iff_mem γ hT').2 hgT')
  rw [cellVal_eq γ hT, cellVal_eq γ hT', hz, ← mul_assoc γ (spN T hT * spW), e1, e2]
  group

/-- **Independence of $T$** (hypothesis `hC`: the two linear-algebra conditions). -/
lemma cellVal_indep (hR : SiegelRelations N A W) (hC : CellGraphConnected g k) {γ : Sp g k}
    {T T' : Matrix (Fin g) (Fin g) k} (hT : CellGood γ T) (hT' : CellGood γ T') :
    cellVal N A W γ T = cellVal N A W γ T' := by
  by_cases hγ : γ ∈ bigCell
  · rw [cellVal_of_mem hR hγ hT, cellVal_of_mem hR hγ hT']
  · have hc : (blkC γ).det = 0 := by
      rw [mem_bigCell_iff, not_not] at hγ; exact hγ
    have hp := hC.connected γ hc T T' hT hT'
    clear hT'
    induction hp with
    | refl => rfl
    | tail _ he ih => exact ih.trans (cellVal_edge hR he)

lemma exists_cellGood (γ : Sp g k) : ∃ T, CellGood γ T := exists_symm_det_ne γ

/-- $F(\gamma) = \rho_\Omega(\gamma z_T)\rho_\Omega(z_T)^{-1}$ for a chosen good $T$. -/
def cellF (N : Matrix (Fin g) (Fin g) k → H) (A : GL (Fin g) k → H) (W : H) (γ : Sp g k) : H :=
  cellVal N A W γ (exists_cellGood γ).choose

lemma cellF_eq (hR : SiegelRelations N A W) (hC : CellGraphConnected g k) {γ : Sp g k}
    {T : Matrix (Fin g) (Fin g) k} (hT : CellGood γ T) : cellF N A W γ = cellVal N A W γ T :=
  cellVal_indep hR hC (exists_cellGood γ).choose_spec hT

/-! ### Left multiplication by the generators -/

lemma rhoCell_spN_mul (hR : SiegelRelations N A W) (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) {x : Sp g k}
    (hx : x ∈ bigCell) : rhoCell N A W (spN B hB * x) = N B * rhoCell N A W x := by
  obtain ⟨C, hC⟩ := exists_gl_of_mem_bigCell hx
  set X := blkA x * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)
  set Z := ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD x
  have hX : Xᵀ = X := blkA_symm hC
  have hZ : Zᵀ = Z := blkD_symm hC
  have dx : x = spN X hX * spM (-invT C) * spW * spN Z hZ * spM 1 := by
    rw [spM_one, mul_one]; exact sp_eq_decomp x hC
  have hBX : (B + X)ᵀ = B + X := by rw [transpose_add, hB, hX]
  have dx2 : spN B hB * x = spN (B + X) hBX * spM (-invT C) * spW * spN Z hZ * spM 1 := by
    rw [dx, spN_add _ _ hB hX]; simp only [mul_assoc]
  rw [dx2, rhoCell_pwp hR, dx, rhoCell_pwp hR, hR.N_add _ _ hB hX]
  simp only [mul_assoc]

lemma rhoCell_spM_mul (hR : SiegelRelations N A W) (a : GL (Fin g) k) {x : Sp g k}
    (hx : x ∈ bigCell) : rhoCell N A W (spM a * x) = A a * rhoCell N A W x := by
  obtain ⟨C, hC⟩ := exists_gl_of_mem_bigCell hx
  set X := blkA x * ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)
  set Z := ((C⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * blkD x
  have hX : Xᵀ = X := blkA_symm hC
  have hZ : Zᵀ = Z := blkD_symm hC
  have dx : x = spN X hX * spM (-invT C) * spW * spN Z hZ * spM 1 := by
    rw [spM_one, mul_one]; exact sp_eq_decomp x hC
  have hX' : ((a : Matrix (Fin g) (Fin g) k) * X * (a : Matrix (Fin g) (Fin g) k)ᵀ)ᵀ =
      (a : Matrix (Fin g) (Fin g) k) * X * (a : Matrix (Fin g) (Fin g) k)ᵀ := by
    simp [transpose_mul, hX, Matrix.mul_assoc]
  have dx2 : spM a * x = spN _ hX' * spM (a * -invT C) * spW * spN Z hZ * spM 1 := by
    rw [dx]
    simp only [← mul_assoc]
    rw [spM_spN a X hX, spM_mul]
    simp only [mul_assoc]
  rw [dx2, rhoCell_pwp hR, dx, rhoCell_pwp hR, hR.A_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (A a) (N X), hR.A_N a X hX]
  simp only [mul_assoc]

lemma cellF_spN_mul (hR : SiegelRelations N A W) (hC : CellGraphConnected g k) (B : Matrix (Fin g) (Fin g) k)
    (hB : Bᵀ = B) (γ : Sp g k) : cellF N A W (spN B hB * γ) = N B * cellF N A W γ := by
  obtain ⟨T, hT⟩ := exists_cellGood γ
  have hT' : CellGood (spN B hB * γ) T := by
    refine ⟨hT.1, ?_⟩
    rw [(blkC_spN_mul B hB γ).1, (blkC_spN_mul B hB γ).2]; exact hT.2
  rw [cellF_eq hR hC hT, cellF_eq hR hC hT', cellVal_eq _ hT.1, cellVal_eq _ hT.1, mul_assoc,
    rhoCell_spN_mul hR B hB ((cellGood_iff_mem γ hT.1).2 hT.2), mul_assoc]

lemma cellF_spM_mul (hR : SiegelRelations N A W) (hC : CellGraphConnected g k) (a : GL (Fin g) k)
    (γ : Sp g k) : cellF N A W (spM a * γ) = A a * cellF N A W γ := by
  obtain ⟨T, hT⟩ := exists_cellGood γ
  have hT' : CellGood (spM a * γ) T := by
    refine ⟨hT.1, ?_⟩
    rw [(blkC_spM_mul a γ).1, (blkC_spM_mul a γ).2, Matrix.mul_assoc, ← Matrix.mul_add, det_mul]
    exact mul_ne_zero (by rw [det_transpose]; exact det_ne_zero_of_gl _) hT.2
  rw [cellF_eq hR hC hT, cellF_eq hR hC hT', cellVal_eq _ hT.1, cellVal_eq _ hT.1, mul_assoc,
    rhoCell_spM_mul hR a ((cellGood_iff_mem γ hT.1).2 hT.2), mul_assoc]

lemma cellF_spW_mul (hR : SiegelRelations N A W) (hC : CellGraphConnected g k) (hT₂ : TwoRowTransversal g k)
    (γ : Sp g k) :
    cellF N A W (spW * γ) = W * cellF N A W γ := by
  by_cases h : γ ∈ bigCell ∧ spW * γ ∈ bigCell
  · obtain ⟨T, hT⟩ := exists_cellGood γ
    obtain ⟨T', hT'⟩ := exists_cellGood (spW * γ)
    rw [cellF_eq hR hC hT, cellF_eq hR hC hT', cellVal_of_mem hR h.1 hT, cellVal_of_mem hR h.2 hT',
      rhoCell_mul hR spW_mem_bigCell h.1 h.2, rhoCell_spW hR]
  · have hor : (blkC γ).det = 0 ∨ (blkA γ).det = 0 := by
      rw [mem_bigCell_iff, mem_bigCell_iff, blkC_spW_mul, det_neg] at h
      by_contra hc
      push Not at hc
      exact h ⟨hc.1, mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.2⟩
    obtain ⟨T, hTs, hc, ha⟩ := hT₂.two_rows γ hor
    have hT : CellGood γ T := ⟨hTs, hc⟩
    have hT' : CellGood (spW * γ) T := by
      refine ⟨hTs, ?_⟩
      rw [blkC_spW_mul, blkD_spW_mul, neg_mul, ← neg_add, det_neg]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ha
    have hm := (cellGood_iff_mem γ hTs).2 hc
    have hm' := (cellGood_iff_mem (spW * γ) hTs).2 hT'.2
    rw [cellF_eq hR hC hT, cellF_eq hR hC hT', cellVal_eq _ hTs, cellVal_eq _ hTs, mul_assoc,
      rhoCell_mul hR spW_mem_bigCell hm (by rw [← mul_assoc]; exact hm'), rhoCell_spW hR, mul_assoc]

end Group

/-! ### Generation and the presentation -/

/-- The generators $n(B)$, $m(a)$, $w$, indexed by `{B // Bᵀ = B} ⊕ GL (Fin g) k ⊕ Unit`. -/
def spGen : {B : Matrix (Fin g) (Fin g) k // Bᵀ = B} ⊕ GL (Fin g) k ⊕ Unit → Sp g k
  | .inl B => spN B.1 B.2
  | .inr (.inl a) => spM a
  | .inr (.inr _) => spW

lemma spGen_closure : Submonoid.closure (Set.range (spGen (g := g) (k := k))) = ⊤ := by
  have hN : ∀ B (hB : Bᵀ = B), spN B hB ∈ Submonoid.closure (Set.range (spGen (g := g) (k := k))) :=
    fun B hB => Submonoid.subset_closure ⟨.inl ⟨B, hB⟩, rfl⟩
  have hM : ∀ a, spM a ∈ Submonoid.closure (Set.range (spGen (g := g) (k := k))) :=
    fun a => Submonoid.subset_closure ⟨.inr (.inl a), rfl⟩
  have hW : (spW : Sp g k) ∈ Submonoid.closure (Set.range (spGen (g := g) (k := k))) :=
    Submonoid.subset_closure ⟨.inr (.inr ()), rfl⟩
  have hΩ : ∀ x ∈ (bigCell : Set (Sp g k)), x ∈ Submonoid.closure (Set.range (spGen (g := g) (k := k))) := by
    intro x hx
    obtain ⟨C, hC⟩ := exists_gl_of_mem_bigCell hx
    rw [sp_eq_decomp x hC]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hN _ _) (hM _)) hW) (hN _ _)
  have hWinv : (spW : Sp g k)⁻¹ = spW * spM (-1 : GL (Fin g) k) := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, spW_sq, ← spM_mul, neg_one_mul, neg_neg, spM_one]
  rw [eq_top_iff]
  intro γ _
  obtain ⟨T, hT, hd⟩ := exists_symm_det_ne γ
  have hz := (cellGood_iff_mem γ hT).2 hd
  have hγ : γ = (γ * (spN T hT * spW)) * (spW⁻¹ * spN (-T) (by rw [transpose_neg, hT])) := by
    have : spN T hT * spN (-T) (by rw [transpose_neg, hT]) = 1 := by
      apply Subtype.ext
      simp [fromBlocks_multiply, fromBlocks_one]
    rw [mul_assoc, mul_assoc, ← mul_assoc spW, mul_inv_cancel, one_mul, this, mul_one]
  rw [hγ, hWinv]
  exact Submonoid.mul_mem _ (hΩ _ hz) (Submonoid.mul_mem _ (Submonoid.mul_mem _ hW (hM _)) (hN _ _))

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ from the two linear-algebra conditions** (every field $k$, every
genus $g$; hypotheses `hC : CellGraphConnected g k` and `hT₂ : TwoRowTransversal g k`): the named input
`SiegelPresentation g k` holds. See the module docstring for the method. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation_of_twoCell (hC : CellGraphConnected g k) (hT₂ : TwoRowTransversal g k) :
    SiegelPresentation.{u} g k := by
  refine ⟨fun M _ N A W hR => ?_⟩
  have hU := siegelRelations_units hR
  let σ : {B : Matrix (Fin g) (Fin g) k // Bᵀ = B} ⊕ GL (Fin g) k ⊕ Unit → Mˣ
    | .inl B => unitsN hR B.1
    | .inr (.inl a) => unitsA hR a
    | .inr (.inr _) => unitsW hR
  obtain ⟨φ, hφ⟩ := exists_hom_of_left_action spGen spGen_closure
    (cellF (unitsN hR) (unitsA hR) (unitsW hR)) σ (by
      rintro (B | a | _) x
      · exact cellF_spN_mul hU hC B.1 B.2 x
      · exact cellF_spM_mul hU hC a x
      · exact cellF_spW_mul hU hC hT₂ x)
  refine ⟨(Units.coeHom M).comp φ, fun B hB => ?_, fun a => ?_, ?_⟩
  · have := hφ (.inl ⟨B, hB⟩)
    simp only [spGen] at this
    simp [this, σ, unitsN_val hR hB]
  · have := hφ (.inr (.inl a))
    simp only [spGen] at this
    simp [this, σ, unitsA]
  · have := hφ (.inr (.inr ()))
    simp only [spGen] at this
    simp [this, σ, unitsW]

/-- **The small-field input from the linear-algebra conditions** (every genus $g$; hypothesis `h`: for $k$ finite with
at most $3g$ elements, `CellGraphConnected g k` and `TwoRowTransversal g k`): the named input
`SiegelPresentationSmallField g k` holds. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations; finite fields with at most $3g$ elements) [unverified]"]
theorem siegelPresentationSmallField_of_twoCell
    (h : Finite k → Nat.card k ≤ 3 * g → CellGraphConnected g k ∧ TwoRowTransversal g k) :
    SiegelPresentationSmallField.{u} g k :=
  ⟨fun hf hc => siegelPresentation_of_twoCell (h hf hc).1 (h hf hc).2⟩

end QuadFormsKB.WeilRep.Genus
