/-
# The cosets $P\gamma$ with vanishing column $0$ of $C$ (for $\Phi E^{(r+1)} = E^{(r)}$)

**Layer:** linear algebra over any field $k$.

**Setting.** $P = P_{r+1}(k)$ is the Siegel parabolic of $\mathrm{Sp}_{2r+2}(k)$ (`siegelP`), $\gamma = \begin{pmatrix}A&B\\C&D\end{pmatrix}$, and
$\iota : \mathrm{Sp}_{2r}(k) \to \mathrm{Sp}_{2r+2}(k)$ the embedding on the variables $1, \dots, r$ (`embSp`, `PhiEmbed.lean`). The condition
"column $0$ of $C$ vanishes" (`IsColZero`) depends only on the coset $P\gamma$, since $C_{p\gamma} = D_pC_\gamma$.

**Results.**
* `isColZero_embSp`: $\iota(\delta)$ satisfies it.
* **`exists_embSp_rel`**: every $\gamma$ with $C_{\cdot 0} = 0$ lies in $P\,\iota(\delta)$ for some $\delta \in \mathrm{Sp}_{2r}(k)$. *Proof:* the column
  $u = A_{\cdot 0}$ satisfies $C^{\mathsf T}u = A^{\mathsf T}C_{\cdot 0} = 0$ and $D^{\mathsf T}u = e_0 + B^{\mathsf T}C_{\cdot 0} = e_0$; an invertible $R$ with
  row $0$ equal to $u^{\mathsf T}$ and its other rows orthogonal to $D_{\cdot 0}$ (rows of $1 - D_{\cdot 0}u^{\mathsf T}$, one of them replaced) gives
  $m({}^tR^{-1})\gamma$ with $C = \mathrm{extC}\,0\,C_1$, $D = \mathrm{extC}\,1\,D_1$; its blocks on the variables $1, \dots, r$ form $\delta$.
* `embSp_rel_iff` (injectivity): $P\iota(\delta) = P\iota(\delta')$ iff $P_r\delta = P_r\delta'$.
* **`colZeroEquiv`**: $P_r(k)\backslash\mathrm{Sp}_{2r}(k) \simeq \{P\gamma : C_{\cdot 0} = 0\}$, $P_r\delta \mapsto P\iota(\delta)$.

Source: Klingen, *Introductory lectures on Siegel modular forms* (1990), §5 (the coset decomposition used for $\Phi$ of
Eisenstein series) [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.PhiEmbed
import QuadFormsKB.SiegelWeil.Forms.EisensteinConv

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open QuadFormsKB.WeilRep.Genus

variable {k : Type*} [Field k] {r : ℕ}

/-- **Column $0$ of $C$ vanishes.** -/
def IsColZero (g : Sp (r + 1) k) : Prop := ∀ i, blockC g i 0 = 0

lemma isColZero_embSp (δ : Sp r k) : IsColZero (embSp δ) := by
  intro i
  rw [blockC_embSp]
  induction i using Fin.cases with
  | zero => rfl
  | succ i => rfl

lemma isColZero_mul_iff {p : Sp (r + 1) k} (hp : p ∈ siegelP (r + 1) k) (g : Sp (r + 1) k) :
    IsColZero (p * g) ↔ IsColZero g := by
  have hC := (blockCD_mul_of_mem_siegelP hp g).1
  have hD : IsUnit (blockD p).det := by
    have := det_blockD_of_mem_siegelP hp
    exact IsUnit.of_mul_eq_one _ this
  have hcol : ∀ g' : Sp (r + 1) k, IsColZero g' ↔ (blockC g' *ᵥ Pi.single 0 1) = 0 := by
    intro g'
    constructor
    · intro h; funext i; simp [mulVec_single, h i]
    · intro h i; have := congrFun h i; simpa [mulVec_single] using this
  rw [hcol, hcol, hC, ← mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (fun v => (blockD p)⁻¹ *ᵥ v) h
    simpa [mulVec_mulVec, nonsing_inv_mul _ hD] using this
  · intro h; rw [h, mulVec_zero]

lemma isColZero_of_rel {g g' : Sp (r + 1) k} (h : QuotientGroup.rightRel (siegelP (r + 1) k) g g') :
    IsColZero g ↔ IsColZero g' := by
  rw [QuotientGroup.rightRel_apply] at h
  have := isColZero_mul_iff h g
  rw [inv_mul_cancel_right] at this
  exact this.symm

/-! ### The symplectic block relations -/

lemma blocks_rel (g : Sp r k) :
    (blockA g)ᵀ * blockC g = (blockC g)ᵀ * blockA g ∧ (blockB g)ᵀ * blockD g = (blockD g)ᵀ * blockB g ∧
      (blockA g)ᵀ * blockD g - (blockC g)ᵀ * blockB g = 1 :=
  (SymplecticGroup.fromBlocks_mem_iff).mp (mem_symplectic_blocks g)

lemma blocks_rel_t (g : Sp r k) :
    blockA g * (blockB g)ᵀ = blockB g * (blockA g)ᵀ ∧ blockC g * (blockD g)ᵀ = blockD g * (blockC g)ᵀ ∧
      blockA g * (blockD g)ᵀ - blockB g * (blockC g)ᵀ = 1 := by
  have h := SymplecticGroup.transpose_mem (mem_symplectic_blocks g)
  rw [fromBlocks_transpose, SymplecticGroup.fromBlocks_mem_iff] at h
  simpa only [transpose_transpose] using h

/-! ### Every coset with vanishing column $0$ of $C$ comes from $\mathrm{Sp}_{2r}$ -/

section Exists

variable (g : Sp (r + 1) k)

/-- $u = A_{\cdot 0}$. -/
def colU : Fin (r + 1) → k := fun i => blockA g i 0

lemma colU_C (hg : IsColZero g) (j : Fin (r + 1)) : ∑ i, colU g i * blockC g i j = 0 := by
  have h := congrFun (congrFun (blocks_rel g).1 0) j
  simp only [mul_apply, transpose_apply] at h
  rw [show (∑ i, blockC g i 0 * blockA g i j) = 0 from Finset.sum_eq_zero fun i _ => by rw [hg i, zero_mul]] at h
  exact h

lemma colU_D (hg : IsColZero g) (j : Fin (r + 1)) :
    ∑ i, colU g i * blockD g i j = if j = 0 then 1 else 0 := by
  have h := congrFun (congrFun (blocks_rel g).2.2 0) j
  simp only [Matrix.sub_apply, mul_apply, transpose_apply, one_apply] at h
  rw [show (∑ i, blockC g i 0 * blockB g i j) = 0 from Finset.sum_eq_zero fun i _ => by rw [hg i, zero_mul],
    sub_zero] at h
  simp only [colU]
  rw [h]; simp [eq_comm]

/-- Row $i$ of $1 - D_{\cdot 0}u^{\mathsf T}$. -/
def rowP (i : Fin (r + 1)) : Fin (r + 1) → k := fun j => (if j = i then 1 else 0) - blockD g i 0 * colU g j

lemma rowP_dot_D (hg : IsColZero g) (i : Fin (r + 1)) : ∑ j, rowP g i j * blockD g j 0 = 0 := by
  have hu := colU_D g hg 0
  simp only [ite_true] at hu
  simp only [rowP, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum, hu, mul_one, sub_self]

lemma rowP_dot (x : Fin (r + 1) → k) (i : Fin (r + 1)) :
    ∑ j, rowP g i j * x j = x i - blockD g i 0 * ∑ j, colU g j * x j := by
  simp only [rowP, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]

lemma exists_colU_ne_zero (hg : IsColZero g) : ∃ k0, colU g k0 ≠ 0 := by
  by_contra h
  push Not at h
  have hu := colU_D g hg 0
  simp [h] at hu

/-- **The row operation** $R$: row $0$ is $u^{\mathsf T}$, row $i \ne 0$ is row $\sigma(i)$ of $1 - D_{\cdot 0}u^{\mathsf T}$, $\sigma = (0\ k_0)$. -/
def rowR (k0 : Fin (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) k :=
  fun i => if i = 0 then colU g else rowP g (Equiv.swap 0 k0 i)

lemma rowR_det_ne_zero {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : (rowR g k0).det ≠ 0 := by
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
  have hux : ∑ j, colU g j * x j = 0 := by
    have := congrFun hx 0
    simpa [mulVec, dotProduct, rowR] using this
  have hxj : ∀ j, j ≠ k0 → x j = 0 := by
    intro j hj
    set i := Equiv.swap 0 k0 j with hi
    have hi0 : i ≠ 0 := by
      intro h; apply hj
      have := congrArg (Equiv.swap 0 k0) h
      simpa [hi] using this
    have := congrFun hx i
    simp only [mulVec, dotProduct, rowR, hi0, ite_false, Pi.zero_apply] at this
    rw [rowP_dot, hux, mul_zero, sub_zero] at this
    simpa [hi] using this
  apply hx0
  funext j
  by_cases hj : j = k0
  · subst hj
    have : ∑ l, colU g l * x l = colU g j * x j :=
      Finset.sum_eq_single j (fun l _ hl => by rw [hxj l hl, mul_zero]) (by simp)
    rw [this] at hux
    simpa [hk0] using hux
  · exact hxj j hj

variable {g}

/-- $m(A_0)$ with $({}^tA_0^{-1}) = R$, i.e. $A_0 = ({}^tR)^{-1}$. -/
def levR {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : GL (Fin (r + 1)) k :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [det_transpose]; exact isUnit_iff_ne_zero.mpr (rowR_det_ne_zero g hk0)) : IsUnit (rowR g k0)ᵀ).unit⁻¹

lemma blockD_spM_levR {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : blockD (spM (levR hk0)) = rowR g k0 := by
  simp [blockD, spM_coe, levR]

/-- $\gamma' = m(A_0)\gamma$, with bottom blocks $RC$, $RD$. -/
def gamR {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : Sp (r + 1) k := spM (levR hk0) * g

lemma blockC_gamR {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : blockC (gamR hk0) = rowR g k0 * blockC g := by
  rw [gamR, (blockCD_mul_of_mem_siegelP (spM_mem_siegelP _) g).1, blockD_spM_levR]

lemma blockD_gamR {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0) : blockD (gamR hk0) = rowR g k0 * blockD g := by
  rw [gamR, (blockCD_mul_of_mem_siegelP (spM_mem_siegelP _) g).2, blockD_spM_levR]

lemma rowR_mul_apply_zero (M : Matrix (Fin (r + 1)) (Fin (r + 1)) k) (k0 : Fin (r + 1)) (j : Fin (r + 1)) :
    (rowR g k0 * M) 0 j = ∑ l, colU g l * M l j := by
  simp [mul_apply, rowR]

lemma rowR_mul_apply_succ (M : Matrix (Fin (r + 1)) (Fin (r + 1)) k) (k0 : Fin (r + 1)) (i : Fin r) (j : Fin (r + 1)) :
    (rowR g k0 * M) i.succ j = ∑ l, rowP g (Equiv.swap 0 k0 i.succ) l * M l j := by
  simp [mul_apply, rowR, Fin.succ_ne_zero]

variable (hg : IsColZero g) {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0)
include hg

lemma gamR_C_col (i : Fin (r + 1)) : blockC (gamR hk0) i 0 = 0 := by
  rw [blockC_gamR, mul_apply]; exact Finset.sum_eq_zero fun l _ => by rw [hg l, mul_zero]

lemma gamR_C_row (j : Fin (r + 1)) : blockC (gamR hk0) 0 j = 0 := by
  rw [blockC_gamR, rowR_mul_apply_zero, colU_C g hg]

lemma gamR_D_row (j : Fin (r + 1)) : blockD (gamR hk0) 0 j = if j = 0 then 1 else 0 := by
  rw [blockD_gamR, rowR_mul_apply_zero, colU_D g hg]

lemma gamR_D_col (i : Fin r) : blockD (gamR hk0) i.succ 0 = 0 := by
  rw [blockD_gamR, rowR_mul_apply_succ, rowP_dot_D g hg]

/-- $A'_{i0} = \delta_{i0}$ for $\gamma'$ (from $A'{}^tD' - B'{}^tC' = 1$, column $0$). -/
lemma gamR_A_col (i : Fin (r + 1)) : blockA (gamR hk0) i 0 = if i = 0 then 1 else 0 := by
  have h := congrFun (congrFun (blocks_rel_t (gamR hk0)).2.2 i) 0
  simp only [Matrix.sub_apply, mul_apply, transpose_apply, one_apply] at h
  rw [Finset.sum_eq_single 0 (fun l _ hl => by rw [gamR_D_row hg hk0, if_neg hl, mul_zero]) (by simp),
    Finset.sum_eq_zero (fun l _ => by rw [gamR_C_row hg hk0, mul_zero]), gamR_D_row hg hk0] at h
  simpa using h

end Exists

/-! ### The element $\delta$ and the coset bijection -/

/-- The block of a matrix on the variables $1, \dots, r$. -/
def subBlk (M : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : Matrix (Fin r) (Fin r) k := fun i j => M i.succ j.succ

lemma subBlk_mul_transpose {M N : Matrix (Fin (r + 1)) (Fin (r + 1)) k} (h : ∀ i j : Fin r, M i.succ 0 * N j.succ 0 = 0) :
    subBlk M * (subBlk N)ᵀ = subBlk (M * Nᵀ) := by
  ext i j
  simp [subBlk, mul_apply, Fin.sum_univ_succ, h i j]

lemma subBlk_sub (M N : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : subBlk (M - N) = subBlk M - subBlk N := rfl

lemma subBlk_one : subBlk (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) k) = 1 := by
  ext i j; simp [subBlk, one_apply]

section Delta

variable {g : Sp (r + 1) k} (hg : IsColZero g) {k0 : Fin (r + 1)} (hk0 : colU g k0 ≠ 0)
include hg

lemma gamR_A_succ (i : Fin r) : blockA (gamR hk0) i.succ 0 = 0 := by
  rw [gamR_A_col hg hk0]; simp [Fin.succ_ne_zero]

lemma deltaR_mem : fromBlocks (subBlk (blockA (gamR hk0))) (subBlk (blockB (gamR hk0))) (subBlk (blockC (gamR hk0)))
    (subBlk (blockD (gamR hk0))) ∈ symplecticGroup (Fin r) k := by
  obtain ⟨h1, h2, h3⟩ := blocks_rel_t (gamR hk0)
  have hA := gamR_A_succ hg hk0
  have hC := gamR_C_col hg hk0
  have e1 := subBlk_mul_transpose (M := blockA (gamR hk0)) (N := blockB (gamR hk0)) fun i j => by rw [hA, zero_mul]
  have e2 := subBlk_mul_transpose (M := blockB (gamR hk0)) (N := blockA (gamR hk0)) fun i j => by rw [hA, mul_zero]
  have e3 := subBlk_mul_transpose (M := blockC (gamR hk0)) (N := blockD (gamR hk0)) fun i j => by rw [hC, zero_mul]
  have e4 := subBlk_mul_transpose (M := blockD (gamR hk0)) (N := blockC (gamR hk0)) fun i j => by rw [hC, mul_zero]
  have e5 := subBlk_mul_transpose (M := blockA (gamR hk0)) (N := blockD (gamR hk0)) fun i j => by rw [hA, zero_mul]
  have e6 := subBlk_mul_transpose (M := blockB (gamR hk0)) (N := blockC (gamR hk0)) fun i j => by rw [hC, mul_zero]
  apply SymplecticGroup.transpose_mem_iff.mp
  rw [fromBlocks_transpose, SymplecticGroup.fromBlocks_mem_iff]
  simp only [transpose_transpose]
  refine ⟨by rw [e1, e2, h1], by rw [e3, e4, h2], by rw [e5, e6, ← subBlk_sub, h3, subBlk_one]⟩

/-- **The element $\delta \in \mathrm{Sp}_{2r}(k)$**: the blocks of $\gamma' = m(A_0)\gamma$ on the variables $1, \dots, r$. -/
def deltaR : Sp r k := ⟨_, deltaR_mem hg hk0⟩

lemma blockC_gamR_eq : blockC (gamR hk0) = blockC (embSp (deltaR hg hk0)) := by
  rw [blockC_embSp]
  refine extC_ext (gamR_C_col hg hk0 0) (fun j => gamR_C_row hg hk0 _) (fun i => gamR_C_col hg hk0 _) fun i j => ?_
  simp [deltaR, blockC, subBlk]

lemma blockD_gamR_eq : blockD (gamR hk0) = blockD (embSp (deltaR hg hk0)) := by
  rw [blockD_embSp]
  refine extC_ext (by rw [gamR_D_row hg hk0]; simp) (fun j => by rw [gamR_D_row hg hk0]; simp [Fin.succ_ne_zero])
    (fun i => gamR_D_col hg hk0 _) fun i j => ?_
  simp [deltaR, blockD, subBlk]

end Delta

/-- **Every coset with vanishing column $0$ of $C$ is $P\,\iota(\delta)$.** -/
theorem exists_embSp_rel (g : Sp (r + 1) k) (hg : IsColZero g) :
    ∃ δ : Sp r k, QuotientGroup.rightRel (siegelP (r + 1) k) (embSp δ) g := by
  obtain ⟨k0, hk0⟩ := exists_colU_ne_zero g hg
  refine ⟨deltaR hg hk0, ?_⟩
  have h1 : QuotientGroup.rightRel (siegelP (r + 1) k) (embSp (deltaR hg hk0)) (gamR hk0) := by
    refine rightRel_of_botR_eq 1 ?_
    rw [Matrix.one_mul]
    funext i x
    cases x with
    | inl j => exact congrFun (congrFun (blockC_gamR_eq hg hk0) i) j
    | inr j => exact congrFun (congrFun (blockD_gamR_eq hg hk0) i) j
  have h2 : QuotientGroup.rightRel (siegelP (r + 1) k) (gamR hk0) g := by
    rw [QuotientGroup.rightRel_apply, gamR, _root_.mul_inv_rev, mul_inv_cancel_left]
    exact inv_mem (spM_mem_siegelP _)
  exact (QuotientGroup.rightRel (siegelP (r + 1) k)).iseqv.trans h1 h2

lemma embSp_mem_siegelP {p : Sp r k} (hp : p ∈ siegelP r k) : embSp p ∈ siegelP (r + 1) k := by
  show blockC _ = 0
  rw [blockC_embSp, show blockC p = 0 from hp, extC_zero]

lemma mem_siegelP_of_embSp {p : Sp r k} (hp : embSp p ∈ siegelP (r + 1) k) : p ∈ siegelP r k := by
  have h : blockC (embSp p) = 0 := hp
  rw [blockC_embSp] at h
  show blockC p = 0
  ext i j
  have := congrFun (congrFun h i.succ) j.succ
  simpa using this

/-- $P\iota(\delta) = P\iota(\delta')$ iff $P_r\delta = P_r\delta'$. -/
lemma embSp_rel_iff (δ δ' : Sp r k) :
    QuotientGroup.rightRel (siegelP (r + 1) k) (embSp δ) (embSp δ') ↔ QuotientGroup.rightRel (siegelP r k) δ δ' := by
  rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← map_inv, ← map_mul]
  exact ⟨mem_siegelP_of_embSp, embSp_mem_siegelP⟩

/-- The coset condition "column $0$ of $C$ vanishes" on $P\backslash\mathrm{Sp}_{2r+2}(k)$. -/
def IsColZeroQ (q : PQuot (r + 1) k) : Prop :=
  Quotient.liftOn q IsColZero fun _ _ h => propext (isColZero_of_rel h)

/-- $P_r\delta \mapsto P\iota(\delta)$. -/
def embQ (q : PQuot r k) : PQuot (r + 1) k :=
  Quotient.map embSp (fun _ _ h => (embSp_rel_iff _ _).mpr h) q

lemma embQ_mk (δ : Sp r k) : embQ (Quotient.mk _ δ : PQuot r k) = Quotient.mk _ (embSp δ) := rfl

lemma isColZeroQ_embQ (q : PQuot r k) : IsColZeroQ (embQ q) := by
  induction q using Quotient.inductionOn with
  | h δ => exact isColZero_embSp δ

/-- **The coset bijection** $P_r(k)\backslash\mathrm{Sp}_{2r}(k) \simeq \{P\gamma \in P\backslash\mathrm{Sp}_{2r+2}(k) : C_{\cdot 0} = 0\}$,
$P_r\delta \mapsto P\iota(\delta)$. -/
@[kb "klingen1990" "§5 (cosets for the Φ operator on Eisenstein series) [unverified]"]
def colZeroEquiv : PQuot r k ≃ {q : PQuot (r + 1) k // IsColZeroQ q} :=
  Equiv.ofBijective (fun q => ⟨embQ q, isColZeroQ_embQ q⟩) (by
    constructor
    · intro q q' h
      induction q using Quotient.inductionOn with
      | h δ =>
        induction q' using Quotient.inductionOn with
        | h δ' =>
          have h' : embQ (Quotient.mk _ δ : PQuot r k) = embQ (Quotient.mk _ δ') := congrArg Subtype.val h
          rw [embQ_mk, embQ_mk, Quotient.eq] at h'
          exact Quotient.sound ((embSp_rel_iff δ δ').mp h')
    · rintro ⟨q, hq⟩
      induction q using Quotient.inductionOn with
      | h g =>
        obtain ⟨δ, hδ⟩ := exists_embSp_rel g hq
        exact ⟨Quotient.mk _ δ, Subtype.ext (by show embQ (Quotient.mk _ δ : PQuot r k) = _; rw [embQ_mk]; exact Quotient.sound hδ)⟩)

lemma colZeroEquiv_apply (δ : Sp r k) :
    (colZeroEquiv (Quotient.mk _ δ : PQuot r k) : PQuot (r + 1) k) = Quotient.mk _ (embSp δ) := rfl

end QuadFormsKB.SiegelWeil.Forms
