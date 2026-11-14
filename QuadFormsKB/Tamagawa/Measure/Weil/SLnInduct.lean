import QuadFormsKB.Tamagawa.Measure.Weil.SLnMeasure

/-!
# The Tamagawa measure `muSL` of $\mathrm{SL}_n(\mathbb A_F)$ and its invariance

$F$ a number field. **`muSL F k`** is the measure on $\mathrm{SL}_{k+1}(\mathbb A_F)$ defined by induction on $k$
(module docstring of `SLnMeasure.lean`): the point mass for $\mathrm{SL}_1$, and
$\mu_{k+2} = \Psi_*(dy|_X\otimes\mu_P)$, $\mu_P = \operatorname{blk}_*(\mu_{k+1}\otimes dc)$.

**`good_muSL`**: every `muSL F k` is σ-finite, nonzero, left invariant and invariant under right translation by
$\mathrm{SL}_{k+1}(F)$ (`Good`). The last property, needed for Weil's quotient $G_{\mathbb A}/G_k$, is proved through the
right-invariance subgroup (`rightInvSub`, a normal subgroup by `rightInvSub_normal`): it contains the $F$-points of
the stabilizer $P$ of $e_0$ (`stabMap_mem_rightInvSub` and the induction hypothesis), hence every element of
$\mathrm{SL}_n(F)$ fixing some basis vector $e_m$ (conjugate by the signed swap $Q_m$), hence all of
$\mathrm{SL}_n(F)$: transvections fix a basis vector, and so do $\operatorname{diag}(\dots,a,\dots,a^{-1},\dots)$ for
$n\ge3$ (Mathlib's `diagonal_transvection_induction'`); for $n = 2$, `SL2.transvection_induction`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-! ### Right translation by the stabilizer -/

/-- Right translation by $q\in P$ preserves $\Psi_*(\nu\otimes\mu_P)$ if it preserves $\mu_P$. -/
theorem coe_mem_rightInvSub_fibMeasure (μP : Measure (orbSec F k).stab) [SigmaFinite μP]
    {q : (orbSec F k).stab} (hq : q ∈ rightInvSub μP) :
    (q : SLnA F (Fin (k + 2))) ∈ rightInvSub ((orbSec F k).fibMeasure (nuX F k) μP) := by
  rw [mem_rightInvSub]
  have hcomp : (fun g => g * (q : SLnA F (Fin (k + 2)))) ∘ (orbSec F k).ofCoord =
      (orbSec F k).ofCoord ∘ Prod.map id (fun p => p * q) := by
    funext p; simp [OrbitSection.ofCoord, mul_assoc]
  have hq' : μP.map (fun p => p * q) = μP := hq
  rw [OrbitSection.fibMeasure, Measure.map_map (measurable_mul_const _) (orbSec F k).measurable_ofCoord, hcomp,
    ← Measure.map_map (orbSec F k).measurable_ofCoord (measurable_id.prodMap (measurable_mul_const q)),
    ← Measure.map_prod_map _ _ measurable_id (measurable_mul_const q), Measure.map_id, hq']

/-! ### $F$-points of the stabilizer -/

theorem slnEmb_eq_blk (γ : SpecialLinearGroup (Fin (k + 2)) F)
    (hγ : (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    slnEmb F (Fin (k + 2)) γ = blk (slnEmb F (Fin (k + 1)) (lowBlkSL γ hγ)) (diagVec F (Fin (k + 1)) (topRow γ)) := by
  refine Subtype.ext ?_
  show (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F).map (diagRing F) = _
  conv_lhs => rw [eq_blkM hγ]
  rw [blkM_map]
  rfl

theorem slnEmb_mem_stab (γ : SpecialLinearGroup (Fin (k + 2)) F)
    (hγ : (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    slnEmb F (Fin (k + 2)) γ =
      ((stabMap (slnEmb F (Fin (k + 1)) (lowBlkSL γ hγ), diagVec F (Fin (k + 1)) (topRow γ)) :
        (orbSec F k).stab) : SLnA F (Fin (k + 2))) :=
  slnEmb_eq_blk γ hγ

/-! ### The invariance properties -/

/-- The properties of the Tamagawa measure carried through the induction: σ-finite, left invariant, invariant under
right translation by $\mathrm{SL}_m(F)$, nonzero. -/
structure Good {m : ℕ} (μ : Measure (SLnA F (Fin m))) : Prop where
  sigmaFinite : SigmaFinite μ
  leftInv : μ.IsMulLeftInvariant
  rightInv : ∀ γ : SpecialLinearGroup (Fin m) F, slnEmb F (Fin m) γ ∈ rightInvSub μ
  ne_zero : μ ≠ 0

instance subsingleton_SL1 {R : Type*} [CommRing R] : Subsingleton (SpecialLinearGroup (Fin 1) R) := by
  refine ⟨fun a b => Subtype.ext ?_⟩
  have ha := a.2
  have hb := b.2
  rw [det_fin_one] at ha hb
  ext i j
  fin_cases i; fin_cases j
  simp only [Fin.zero_eta, Fin.isValue]
  rw [ha, hb]

theorem good_dirac : Good (Measure.dirac (1 : SLnA F (Fin 1))) := by
  refine ⟨inferInstance, ⟨fun a => ?_⟩, fun γ => ?_, ?_⟩
  · rw [Subsingleton.elim a 1]
    simp only [one_mul, Measure.map_id']
  · rw [mem_rightInvSub]
    have : (fun x : SLnA F (Fin 1) => x * slnEmb F (Fin 1) γ) = id := funext fun x => Subsingleton.elim _ _
    rw [this, Measure.map_id]
  · exact Measure.dirac_ne_zero

theorem exists_ne_ne {i j : Fin (k + 3)} : ∃ m : Fin (k + 3), m ≠ i ∧ m ≠ j := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one] at h0 h1 h2
  omega

/-- **The induction step**: the fibration measure built from a good measure on $\mathrm{SL}_{k+1}(\mathbb A_F)$ is
good on $\mathrm{SL}_{k+2}(\mathbb A_F)$. -/
theorem good_succ {μ : Measure (SLnA F (Fin (k + 1)))} (hμ : Good μ) :
    Good ((orbSec F k).fibMeasure (nuX F k) (muP μ)) := by
  have := hμ.sigmaFinite
  have := hμ.leftInv
  have := sigmaFinite_muP (F := F) μ
  have := isMulLeftInvariant_muP (F := F) μ
  set μG := (orbSec F k).fibMeasure (nuX F k) (muP μ)
  have hne : μG ≠ 0 := by
    intro h0
    have h := congrArg (fun ν : Measure (SLnA F (Fin (k + 2))) => ν Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    rw [OrbitSection.fibMeasure_apply _ _ _ MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
      Measure.prod_prod, muP, Measure.map_apply measurable_stabMap MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod, nuX_apply_univ] at h
    have hA : ∀ m : ℕ, muAddVec F (Fin m) Set.univ ≠ 0 := fun m =>
      (isOpen_univ.measure_pos (muAddVec F (Fin m)) Set.univ_nonempty).ne'
    have hμu : μ Set.univ ≠ 0 := fun h => hμ.ne_zero (Measure.measure_univ_eq_zero.mp h)
    rcases mul_eq_zero.mp h with h | h
    · exact hA _ h
    · rcases mul_eq_zero.mp h with h | h
      · exact hμu h
      · exact hA _ h
  refine ⟨inferInstance, inferInstance, fun γ => ?_, hne⟩
  -- the right-invariance subgroup of `μG` is normal
  obtain ⟨U, hUm, hU0, hUt⟩ := OrbitSection.exists_pos_lt_top (X := SLnA F (Fin (k + 2))) μG hne
  have hnorm := rightInvSub_normal hUm hU0 hUt
  set N := rightInvSub μG
  -- elements fixing `e₀`
  have hP : ∀ δ : SpecialLinearGroup (Fin (k + 2)) F,
      (δ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
        slnEmb F (Fin (k + 2)) δ ∈ N := by
    intro δ hδ
    rw [slnEmb_mem_stab δ hδ]
    exact coe_mem_rightInvSub_fibMeasure _ (stabMap_mem_rightInvSub μ (hμ.rightInv _) _)
  -- elements fixing some `e_m`
  have hfix : ∀ (δ : SpecialLinearGroup (Fin (k + 2)) F) (m : Fin (k + 2)),
      (δ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single m 1 = Pi.single m 1 →
        slnEmb F (Fin (k + 2)) δ ∈ N := by
    intro δ m hδ
    set δ' := qSL m * δ * qInvSL m
    have hδ' : (δ' : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      show (qMat m * (δ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) * qInv m) *ᵥ Pi.single 0 1 = Pi.single 0 1
      rw [← mulVec_mulVec, qInv_mulVec_single, ← mulVec_mulVec, hδ, qMat_mulVec_single]
    have hmem := hP δ' hδ'
    have hinv : (qSL m)⁻¹ = qInvSL (R := F) m := (inv_eq_of_mul_eq_one_right (qSL_mul_qInvSL m))
    have hδeq : δ = (qSL m)⁻¹ * δ' * qSL m := by
      rw [show δ' = qSL m * δ * (qSL m)⁻¹ by rw [hinv]]; group
    rw [hδeq, map_mul, map_mul, map_inv]
    have := hnorm.conj_mem _ hmem (slnEmb F (Fin (k + 2)) (qSL m))⁻¹
    simpa using this
  have hmul : ∀ A B : SpecialLinearGroup (Fin (k + 2)) F, slnEmb F (Fin (k + 2)) A ∈ N →
      slnEmb F (Fin (k + 2)) B ∈ N → slnEmb F (Fin (k + 2)) (A * B) ∈ N := fun A B hA hB => by
    rw [map_mul]; exact N.mul_mem hA hB
  have htr : ∀ (i j : Fin (k + 2)) (hij : i ≠ j) (c : F),
      slnEmb F (Fin (k + 2)) (SpecialLinearGroup.transvection hij c) ∈ N := by
    intro i j hij c
    refine hfix _ i ?_
    funext r
    rw [show ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin (k + 2)) F) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) F) = transvection i j c from rfl, transvection_mulVec_apply]
    simp [Pi.single_apply, Ne.symm hij]
  cases k with
  | zero => exact SL2.transvection_induction (fun δ => slnEmb F (Fin 2) δ ∈ N) htr hmul γ
  | succ k =>
    refine SpecialLinearGroup.diagonal_transvection_induction' (fun δ => slnEmb F (Fin (k + 3)) δ ∈ N) γ
      (fun i j hij c hc => ?_) htr hmul
    obtain ⟨m, hmi, hmj⟩ := exists_ne_ne (i := i) (j := j)
    refine hfix _ m ?_
    rw [SpecialLinearGroup.diag2n_coe]
    funext r
    rw [mulVec_diagonal]
    by_cases hr : r = m
    · subst hr; simp [hmi, hmj]
    · simp [Pi.single_apply, hr]

variable (F) in
/-- **The Tamagawa measure of $\mathrm{SL}_{k+1}(\mathbb A_F)$**, by induction on $k$: the point mass on
$\mathrm{SL}_1(\mathbb A_F) = 1$, and the fibration measure $\Psi_*(dy|_X\otimes\operatorname{blk}_*(\mu_{k+1}\otimes dc))$
on $\mathrm{SL}_{k+2}(\mathbb A_F)$ (Weil 1982, §2.4, Thm 2.4.3: $\omega_{\mathrm{SL}_n} = dy\wedge\omega_{\mathrm{SL}_{n-1}}\wedge dc$,
all additive measures self-dual). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 and Thm 2.4.3 (fibration G → G/H, H the stabilizer of e₀); §2.3 (λ_v = 1) [unverified pages]"]
def muSL : (k : ℕ) → Measure (SLnA F (Fin (k + 1)))
  | 0 => Measure.dirac 1
  | k + 1 => (orbSec F k).fibMeasure (nuX F k) (muP (muSL k))

theorem muSL_zero : muSL F 0 = Measure.dirac 1 := rfl

theorem muSL_succ (k : ℕ) : muSL F (k + 1) = (orbSec F k).fibMeasure (nuX F k) (muP (muSL F k)) := rfl

/-- **`muSL` is good**: σ-finite, nonzero, left invariant, right invariant under $\mathrm{SL}_{k+1}(F)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.3 and p. 23 (G_𝔸/G_k carries an invariant measure) [unverified pages]"]
theorem good_muSL : ∀ k, Good (muSL F k)
  | 0 => good_dirac
  | k + 1 => good_succ (good_muSL k)

instance (k : ℕ) : SigmaFinite (muSL F k) := (good_muSL k).sigmaFinite
instance (k : ℕ) : (muSL F k).IsMulLeftInvariant := (good_muSL k).leftInv

/-- `muSL F k` is invariant under the right action $\gamma\cdot g = g\gamma^{-1}$ of $\mathrm{SL}_{k+1}(F)$. -/
instance smulInvariantMeasure_muSL (k : ℕ) :
    SMulInvariantMeasure (SpecialLinearGroup (Fin (k + 1)) F) (SLnA F (Fin (k + 1))) (muSL F k) := by
  refine ⟨fun γ s hs => ?_⟩
  have h : (muSL F k).map (· * (slnEmb F (Fin (k + 1)) γ)⁻¹) = muSL F k :=
    (rightInvSub (muSL F k)).inv_mem ((good_muSL k).rightInv γ)
  have : (fun g : SLnA F (Fin (k + 1)) => γ • g) = (· * (slnEmb F (Fin (k + 1)) γ)⁻¹) := rfl
  rw [this, ← Measure.map_apply (measurable_mul_const _) hs, h]

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
