/-
# Transport along $N = M$, and frame data at infinity in $1 + k$ variables

**Layer:** number fields. The forms headlines are stated for forms in $r + n'$ variables (for $r = 1$: `QuadForm (𝓞 F) (1 + k)`),
the numbers headlines for forms in $k + 1$ variables; $1 + k$ and $k + 1$ are equal but not definitionally. As in
`siegelIndefiniteForms_unary_consistent`, a form $Q$ in $N$ variables is transported along $h : N = M$ (`h ▸ Q`).

**Defines** (all by `subst`; for $h$ = `rfl` they are identities)
* `gCast h Q` : $G_\infty(Q)\cong G_\infty(h\triangleright Q)$, `vCast h` : $V_\infty^{(N)}\cong V_\infty^{(M)}$, `stabCast h Q y` :
  $H_y\cong H_{\mathrm{vCast}\,y}$, `dcTransport h Q` : classes of $Q$ $\cong$ classes of $h\triangleright Q$; coordinates are
  re-indexed by `Fin.cast` (the identity on values);
* `FrameTowerAlg.toSplitDataInfCast`: the frame data at infinity (`SplitDataInf`) of $h\triangleright Q_1$,
  $h : 1 + k = k + 1$, for a rational $1$-frame of $\langle m\rangle$ with algebraic frame data `D` of $Q_1$: $g$ is
  $[\Xi\mid C]$ re-indexed, $Q'' = $ `D.Q''`, $\iota = $ `gCast` $\circ$ `D.ιInf`.

**Proves** (unconditional): the transport rules (`gCast_smul`, `matR_gCast`, `matC_gCast`, `hessian_cast`, `eval_cast`,
`coe_stabCast_symm`, `repMeasureOf_cast`), `vCast_ratAT`.
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareFrames
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteChecks

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex
  LocalDensity

variable {F : Type} [Field F] [NumberField F]

/-! ### Transport along $N = M$ -/

section Cast

variable {N M : ℕ}

/-- $G_\infty(Q)\cong G_\infty(h\triangleright Q)$. -/
def gCast (h : N = M) (Q : QuadForm (𝓞 F) N) : GInfSO Q ≃* GInfSO (h ▸ Q : QuadForm (𝓞 F) M) := by
  subst h; exact MulEquiv.refl _

theorem measurable_gCast (h : N = M) (Q : QuadForm (𝓞 F) N) : Measurable (gCast h Q) := by
  subst h; exact measurable_id

/-- $V_\infty^{(N)}\cong V_\infty^{(M)}$. -/
def vCast (h : N = M) : VInf F N ≃ VInf F M := by
  subst h; exact Equiv.refl _

theorem vCast_fst (h : N = M) (v : VInf F N) (w : {w : InfinitePlace F // w.IsReal}) (i : Fin M) :
    (vCast h v).1 w i = v.1 w (Fin.cast h.symm i) := by
  subst h; rfl

theorem vCast_snd (h : N = M) (v : VInf F N) (w : {w : InfinitePlace F // w.IsComplex}) (i : Fin M) :
    (vCast h v).2 w i = v.2 w (Fin.cast h.symm i) := by
  subst h; rfl

theorem gCast_smul (h : N = M) (Q : QuadForm (𝓞 F) N) (a : GInfSO Q) (v : VInf F N) :
    gCast h Q a • vCast h v = vCast h (a • v) := by
  subst h; rfl

theorem matR_gCast (h : N = M) (Q : QuadForm (𝓞 F) N) (a : GInfSO Q) (w : {w : InfinitePlace F // w.IsReal}) :
    ((ArchSO.incl _ ((gCast h Q a).1 w) : GL (Fin M) ℝ) : Matrix (Fin M) (Fin M) ℝ) =
      ((ArchSO.incl _ (a.1 w) : GL (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ).submatrix (Fin.cast h.symm)
        (Fin.cast h.symm) := by
  subst h; ext i j; rfl

theorem matC_gCast (h : N = M) (Q : QuadForm (𝓞 F) N) (a : GInfSO Q) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((ArchSOC.incl _ ((gCast h Q a).2 w) : GL (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ) =
      ((ArchSOC.incl _ (a.2 w) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).submatrix (Fin.cast h.symm)
        (Fin.cast h.symm) := by
  subst h; ext i j; rfl

theorem hessian_cast (h : N = M) (Q : QuadForm (𝓞 F) N) :
    ((h ▸ Q : QuadForm (𝓞 F) M).map (algebraMap (𝓞 F) F)).hessian =
      ((Q.map (algebraMap (𝓞 F) F)).hessian).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h; ext i j; rfl

theorem eval_cast (h : N = M) (Q : QuadForm (𝓞 F) N) (v : Fin M → F) :
    ((h ▸ Q : QuadForm (𝓞 F) M).map (algebraMap (𝓞 F) F)).eval v =
      (Q.map (algebraMap (𝓞 F) F)).eval fun i => v (Fin.cast h i) := by
  subst h; rfl

/-- $H_y\cong H_{\mathrm{vCast}\,y}$. -/
def stabCast (h : N = M) (Q : QuadForm (𝓞 F) N) (y : VInf F N) :
    stabilizer (GInfSO Q) y ≃* stabilizer (GInfSO (h ▸ Q : QuadForm (𝓞 F) M)) (vCast h y) := by
  subst h; exact MulEquiv.refl _

theorem coe_stabCast_symm (h : N = M) (Q : QuadForm (𝓞 F) N) (y : VInf F N)
    (s : stabilizer (GInfSO (h ▸ Q : QuadForm (𝓞 F) M)) (vCast h y)) :
    ((stabCast h Q y).symm s : GInfSO Q) = (gCast h Q).symm s := by
  subst h; rfl

theorem measurable_stabCast_symm (h : N = M) (Q : QuadForm (𝓞 F) N) (y : VInf F N) :
    Measurable (stabCast h Q y).symm := by
  subst h; exact measurable_id

/-- The classes of $Q$ and of $h\triangleright Q$. -/
def dcTransport (h : N = M) (Q : QuadForm (𝓞 F) N) : DC Q ≃ DC (h ▸ Q : QuadForm (𝓞 F) M) := by
  subst h; exact Equiv.refl _

/-- **Measures of representations under transport** along $N = M$. -/
theorem repMeasureOf_cast (h : N = M) (Q : QuadForm (𝓞 F) N) (m : F)
    (μ : (y : VInf F M) → Measure (stabilizer (GInfSO (h ▸ Q : QuadForm (𝓞 F) M)) y)) (i : DC Q) :
    repMeasureOf (unitGroup (h ▸ Q : QuadForm (𝓞 F) M) (dcTransport h Q i)) (reps (h ▸ Q : QuadForm (𝓞 F) M) m (dcTransport h Q i)) μ =
      repMeasureOf (unitGroup Q i) (reps Q m i) fun y => (μ (vCast h y)).map (stabCast h Q y).symm := by
  subst h
  show repMeasureOf _ _ μ = repMeasureOf _ _ _
  congr 1
  funext y
  exact (Measure.map_id).symm

end Cast

/-! ### Frame data at infinity in $1 + k$ variables -/

section Adapter

variable {k : ℕ} {Q₁ : QuadForm (𝓞 F) (1 + k)} {hQ₁ : Q₁.Nondegenerate} {m : 𝓞 F}
  {Ξ : RatFrame Q₁ (DVR.unary m)}

/-! Re-indexing helpers along $k + 1 = 1 + k$. -/

theorem castAd_zero : Fin.cast (Nat.add_comm 1 k).symm (0 : Fin (k + 1)) = Fin.castAdd k (0 : Fin 1) :=
  Fin.ext (by simp)

theorem castAd_succ (b : Fin k) : Fin.cast (Nat.add_comm 1 k).symm b.succ = Fin.natAdd 1 b :=
  Fin.ext (by simp [Nat.add_comm])

theorem castAd_submatrix_blockMat {K : Type*} [CommRing K] (P : Matrix (Fin 1) (Fin 1) K)
    (B : Matrix (Fin k) (Fin k) K) :
    (Frames.blockMat P 0 0 B).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) =
      cornerMat (P 0 0) B := by
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
    simp only [Matrix.submatrix_apply, castAd_zero, castAd_succ, cornerMat_zero_zero, cornerMat_zero_succ,
      cornerMat_succ_zero, cornerMat_succ_succ, Frames.blockMat_castAdd_castAdd, Frames.blockMat_castAdd_natAdd,
      Frames.blockMat_natAdd_castAdd, Frames.blockMat_natAdd_natAdd, Matrix.zero_apply]

theorem castAd_wittG (Ξ' : Matrix (Fin (1 + k)) (Fin 1) F) (C : Matrix (Fin (1 + k)) (Fin k) F) :
    (wittG Ξ' C).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) =
      splitMat (fun i => Ξ' (Fin.cast (Nat.add_comm 1 k).symm i) 0) (C.submatrix (Fin.cast (Nat.add_comm 1 k).symm) id) := by
  ext i j
  refine Fin.cases ?_ (fun b => ?_) j
  · simp only [Matrix.submatrix_apply, splitMat, Matrix.of_apply, Fin.cases_zero, wittG, castAd_zero,
      Fin.addCases_left]
  · simp only [Matrix.submatrix_apply, splitMat, Matrix.of_apply, Fin.cases_succ, wittG, castAd_succ,
      Fin.addCases_right, id]

theorem castAd_gram {K : Type*} [CommRing K] (W H : Matrix (Fin (1 + k)) (Fin (1 + k)) K) :
    (W.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm))ᵀ *
        H.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) *
        W.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) =
      (Wᵀ * H * W).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) := by
  have e1 := Matrix.submatrix_mul_equiv Wᵀ H (finCongr (Nat.add_comm 1 k).symm) (finCongr (Nat.add_comm 1 k).symm)
    (finCongr (Nat.add_comm 1 k).symm)
  have e2 := Matrix.submatrix_mul_equiv (Wᵀ * H) W (finCongr (Nat.add_comm 1 k).symm)
    (finCongr (Nat.add_comm 1 k).symm) (finCongr (Nat.add_comm 1 k).symm)
  rw [Matrix.transpose_submatrix]
  refine Eq.trans ?_ e2
  exact congrArg (· * W.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm)) e1

theorem castAd_det {K : Type*} [CommRing K] (W : Matrix (Fin (1 + k)) (Fin (1 + k)) K) :
    (W.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm)).det = W.det :=
  Matrix.det_submatrix_equiv_self (finCongr (Nat.add_comm 1 k).symm) W

theorem castAd_mul_right {K : Type*} [CommRing K] {a : ℕ} (A : Matrix (Fin (1 + k)) (Fin (1 + k)) K)
    (B : Matrix (Fin (1 + k)) (Fin a) K) :
    (A * B).submatrix (Fin.cast (Nat.add_comm 1 k).symm) id =
      A.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) *
        B.submatrix (Fin.cast (Nat.add_comm 1 k).symm) id := by
  ext i j
  show ∑ l, A (Fin.cast (Nat.add_comm 1 k).symm i) l * B l j =
    ∑ l, A (Fin.cast (Nat.add_comm 1 k).symm i) (Fin.cast (Nat.add_comm 1 k).symm l) *
      B (Fin.cast (Nat.add_comm 1 k).symm l) j
  exact (Fintype.sum_equiv (finCongr (Nat.add_comm 1 k).symm) _ _ (fun x => rfl)).symm

theorem castAd_mulVec {K : Type*} [CommRing K] (M : Matrix (Fin (1 + k)) (Fin (1 + k)) K) (v : Fin (1 + k) → K)
    (hv : M *ᵥ v = v) :
    M.submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) *ᵥ
        (fun j => v (Fin.cast (Nat.add_comm 1 k).symm j)) = fun j => v (Fin.cast (Nat.add_comm 1 k).symm j) := by
  funext i
  have h := congrFun hv (Fin.cast (Nat.add_comm 1 k).symm i)
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at h ⊢
  exact (Fintype.sum_equiv (finCongr (Nat.add_comm 1 k).symm) _ _ (fun x => rfl)).trans h

/-- The Gram matrix of the $1$-frame $\Xi$ of $\langle m\rangle$: $\Xi^{\mathsf T}H\Xi = (2m)$. -/
theorem ratFrame_gram_unary (Ξ' : RatFrame Q₁ (DVR.unary m)) :
    ((Ξ'.1)ᵀ * (Q₁.map (algebraMap (𝓞 F) F)).hessian * Ξ'.1) 0 0 = 2 * (m : F) := by
  have h := congrArg (fun q : QuadForm F 1 => q.hessian 0 0) Ξ'.2
  simp only [QuadForm.hessian_compMat] at h
  rw [h]
  simp [QuadForm.hessian, DVR.unary, QuadForm.map, QuadForm.diag, two_mul]

theorem FrameTowerAlg.gram_castMat (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) :
    (wittG Ξ.1 D.Cm)ᵀ * (Q₁.map (algebraMap (𝓞 F) F)).hessian * wittG Ξ.1 D.Cm =
      Frames.blockMat ((Ξ.1)ᵀ * (Q₁.map (algebraMap (𝓞 F) F)).hessian * Ξ.1) 0 0 (D.Q''.map (algebraMap (𝓞 F) F)).hessian := by
  rw [← D.hCH]
  exact wittG_gram _ (witt_hessian_symm _) Ξ.1 D.Cm (fun j => D.hΞC j)

/-- With $m\ne0$ the matrix $[\Xi\mid C]$ is invertible. (The hypothesis `hm` is necessary: for $k = 0$, $m = 0$ the frame is
$\xi = 0$.) -/
theorem FrameTowerAlg.isUnit_det_castMat (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (hm : (m : F) ≠ 0) :
    IsUnit ((wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm)).det := by
  rw [castAd_det, isUnit_iff_ne_zero]
  intro h0
  have h := congrArg Matrix.det D.gram_castMat
  rw [Frames.det_blockMat_diag, Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_fin_one, ratFrame_gram_unary] at h
  have hH'' := witt_nd _ D.hQ''
  unfold QuadForm.Nondegenerate at hH''
  have : (2 * (m : F)) * (D.Q''.map (algebraMap (𝓞 F) F)).hessian.det = 0 := by rw [← h]; ring
  rcases mul_eq_zero.1 this with h3 | h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact hm h4
  · exact hH'' h3

theorem FrameTowerAlg.mulVec_ξ_real_cast (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (h : GInfSO D.Q'')
    (w : {w : InfinitePlace F // w.IsReal}) :
    (ArchSO.incl _ ((D.ιInf h).1 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℝ) *ᵥ (fun j => σR w (Ξ.1 j 0)) =
      fun j => σR w (Ξ.1 j 0) := by
  have e := D.fix ((h, 1) : SOAdele D.Q'')
  have hd : ∀ c : F, (diag F c).1.1 w = σR w c := fun c => mixedEmbedding.mixedEmbedding_apply_isReal F c w
  funext i
  have h1 : ((ArchSO.incl _ ((D.ιInf h).1 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℝ) *ᵥ
      fun j => (diag F (cols Ξ.1 0 j)).1.1 w) i = (diag F (cols Ξ.1 0 i)).1.1 w :=
    congrArg (fun y => (y 0 i).1.1 w) e
  simpa only [hd] using h1

theorem FrameTowerAlg.mulVec_ξ_complex_cast (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (h : GInfSO D.Q'')
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (ArchSOC.incl _ ((D.ιInf h).2 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℂ) *ᵥ (fun j => σC w (Ξ.1 j 0)) =
      fun j => σC w (Ξ.1 j 0) := by
  have e := D.fix ((h, 1) : SOAdele D.Q'')
  have hd : ∀ c : F, (diag F c).1.2 w = σC w c := fun c => mixedEmbedding.mixedEmbedding_apply_isComplex F c w
  funext i
  have h1 : ((ArchSOC.incl _ ((D.ιInf h).2 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℂ) *ᵥ
      fun j => (diag F (cols Ξ.1 0 j)).1.2 w) i = (diag F (cols Ξ.1 0 i)).1.2 w :=
    congrArg (fun y => (y 0 i).1.2 w) e
  simpa only [hd] using h1

/-- **The frame data at infinity of $h\triangleright Q_1$** ($h : 1 + k = k + 1$) for the rational $1$-frame $\Xi$ of
$\langle m\rangle$, $m\ne0$, from algebraic frame data `D` of $Q_1$: $g = [\Xi\mid C]$ re-indexed by `Fin.cast`,
$Q'' = $ `D.Q''`, $\iota = $ `gCast` $\circ$ `D.ιInf`. -/
def FrameTowerAlg.toSplitDataInfCast (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (hm : (m : F) ≠ 0) :
    SplitDataInf (Nat.add_comm 1 k ▸ Q₁) (m : F) (fun i => Ξ.1 (Fin.cast (Nat.add_comm 1 k).symm i) 0) where
  Q'' := D.Q''
  hQ'' := D.hQ''
  g := Matrix.nonsingInvUnit _ (D.isUnit_det_castMat hm)
  hess := by
    show (splitForm (m : F) (D.Q''.map (algebraMap (𝓞 F) F))).hessian =
      ((wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm))ᵀ *
        ((Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)).map (algebraMap (𝓞 F) F)).hessian *
        (wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm)
    rw [hessian_splitForm, hessian_cast, castAd_gram, D.gram_castMat, castAd_submatrix_blockMat,
      ratFrame_gram_unary]
  base := by
    show (wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) *ᵥ
      Pi.single 0 1 = _
    rw [castAd_wittG]
    funext i
    simp [splitMat, Matrix.mulVec, dotProduct, Pi.single_apply]
  ι := (gCast (Nat.add_comm 1 k) Q₁).toMonoidHom.comp D.ιInf
  measurable_ι := (measurable_gCast _ _).comp D.measurable_ιInf
  matR_ι := fun h w => by
    refine (matR_gCast (Nat.add_comm 1 k) Q₁ (D.ιInf h) w).trans ?_
    have key : (ArchSO.incl _ ((D.ιInf h).1 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℝ) * D.Cm.map (σR w) =
        D.Cm.map (σR w) * (ArchSO.incl _ (h.1 w) : Matrix (Fin k) (Fin k) ℝ) := D.hCR ((h, 1) : SOAdele D.Q'') w
    refine mul_cornerMat_conj (σR w) _ (D.Cm.submatrix (Fin.cast (Nat.add_comm 1 k).symm) id)
      (Matrix.nonsingInvUnit _ (D.isUnit_det_castMat hm)) (castAd_wittG Ξ.1 D.Cm) _ _ ?_ ?_
    · show _ * (D.Cm.map (σR w)).submatrix (Fin.cast (Nat.add_comm 1 k).symm) id = _
      rw [← castAd_mul_right, key]
      rfl
    · exact castAd_mulVec _ _ (D.mulVec_ξ_real_cast h w)
  matC_ι := fun h w => by
    refine (matC_gCast (Nat.add_comm 1 k) Q₁ (D.ιInf h) w).trans ?_
    have key : (ArchSOC.incl _ ((D.ιInf h).2 w) : Matrix (Fin (1 + k)) (Fin (1 + k)) ℂ) * D.Cm.map (σC w) =
        D.Cm.map (σC w) * (ArchSOC.incl _ (h.2 w) : Matrix (Fin k) (Fin k) ℂ) := D.hCC ((h, 1) : SOAdele D.Q'') w
    refine mul_cornerMat_conj (σC w) _ (D.Cm.submatrix (Fin.cast (Nat.add_comm 1 k).symm) id)
      (Matrix.nonsingInvUnit _ (D.isUnit_det_castMat hm)) (castAd_wittG Ξ.1 D.Cm) _ _ ?_ ?_
    · show _ * (D.Cm.map (σC w)).submatrix (Fin.cast (Nat.add_comm 1 k).symm) id = _
      rw [← castAd_mul_right, key]
      rfl
    · exact castAd_mulVec _ _ (D.mulVec_ξ_complex_cast h w)

theorem FrameTowerAlg.toSplitDataInfCast_g (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (hm : (m : F) ≠ 0) :
    ((D.toSplitDataInfCast hm).g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) =
      (wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm) := rfl

theorem FrameTowerAlg.toSplitDataInfCast_ι (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) (hm : (m : F) ≠ 0)
    (x : GInfSO D.Q'') : (D.toSplitDataInfCast hm).ι x = gCast (Nat.add_comm 1 k) Q₁ (D.ιInf x) := rfl

/-- The archimedean point of the frame, transported. -/
theorem vCast_ratAT : vCast (Nat.add_comm 1 k) (ratAT Q₁ (DVR.unary m) Ξ 0) =
    ξInf (k := k) (fun i => Ξ.1 (Fin.cast (Nat.add_comm 1 k).symm i) 0) := by
  refine Prod.ext (funext fun w => funext fun i => ?_) (funext fun w => funext fun i => ?_)
  · obtain ⟨w, hw⟩ := w
    rw [vCast_fst]
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding.mixedEmbedding_apply_isReal, ξInf,
      cols, σR]
  · obtain ⟨w, hw⟩ := w
    rw [vCast_snd]
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding.mixedEmbedding_apply_isComplex, ξInf,
      cols, σC]

theorem det_castMat (D : FrameTowerAlg Q₁ hQ₁ k (cols Ξ.1)) :
    ((wittG Ξ.1 D.Cm).submatrix (Fin.cast (Nat.add_comm 1 k).symm) (Fin.cast (Nat.add_comm 1 k).symm)).det =
      (wittG Ξ.1 D.Cm).det :=
  castAd_det _

end Adapter

end QuadFormsKB.Tamagawa.Indefinite
