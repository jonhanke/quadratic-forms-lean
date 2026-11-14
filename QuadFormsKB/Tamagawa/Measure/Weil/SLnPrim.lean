import QuadFormsKB.Tamagawa.Measure.Weil.SLnLocal
import QuadFormsKB.Tamagawa.Measure.Weil.SL2Prim
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# Primitive vectors of $\mathbb A_F^n$ and a measurable section of $g\mapsto ge_0$ on $\mathrm{SL}_n(\mathbb A_F)$


$F$ a number field, $n = k + 2\ge 2$. Generalizes `SL2Section.lean` (the case $n = 2$, with a different local formula).

* **Primitive vectors** `primSetN F k` $\subseteq\mathbb A_F^n$: $y_w\ne0$ at every place $w$, and $y_v$ primitive in
  $\mathcal O_v^n$ for almost all finite $v$ (`IsPrimN`). This is the image of the orbit map $g\mapsto ge_0$:
  `col_mem_primSetN` and `col_secN`.
* **The section** `secN`: place by place the local section $s_B(z) = Q_i^{-1}L(Q_iz)$ of `SLnLocal.lean` (with $B$ the
  closed unit ball at the archimedean places and $\mathcal O_v$ at the finite places); it lies in $\mathrm{SL}_n(\mathcal O_v)$
  whenever $y_v$ is primitive, hence defines an element of $\mathrm{SL}_n(\mathbb A_F)$ (`det_secMatA`), and it is
  **measurable** (`measurable_secN`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical MatrixGroups RestrictedProduct

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

/-! ### Measurability of the local section -/

section MeasLocal

variable {K : Type*} [Field K] [MeasurableSpace K] [MeasurableAdd₂ K] [MeasurableMul₂ K] [MeasurableInv K]
  [MeasurableSingletonClass K] {k : ℕ}

theorem measurableSet_pivP {B : Set K} (hB : MeasurableSet B) (i : Fin (k + 2)) :
    MeasurableSet {z : Fin (k + 2) → K | PivP B z i} := by
  simp only [PivP, Set.ofPred_and, Set.ofPred_forall]
  refine ((measurableSet_singleton 0).compl.preimage (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun j => hB.preimage ((measurable_pi_apply j).mul (measurable_pi_apply i).inv))

theorem measurableSet_piv_eq {B : Set K} (hB : MeasurableSet B) (i : Fin (k + 2)) :
    MeasurableSet {z : Fin (k + 2) → K | piv B z = i} := by
  have hex : MeasurableSet {z : Fin (k + 2) → K | ∃ i, PivP B z i} := by
    simp only [Set.ofPred_exists]; exact MeasurableSet.iUnion fun j => measurableSet_pivP hB j
  have e : {z : Fin (k + 2) → K | piv B z = i} =
      ({z | ∃ i, PivP B z i} ∩ ({z | PivP B z i} ∩ ⋂ j, ⋂ (_ : j < i), {z | PivP B z j}ᶜ)) ∪
        ({z | ∃ i, PivP B z i}ᶜ ∩ {_z | i = 0}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, piv_eq_iff]
  rw [e]
  refine (hex.inter ((measurableSet_pivP hB i).inter (MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => (measurableSet_pivP hB j).compl))).union (hex.compl.inter ?_)
  exact MeasurableSet.const _

theorem measurable_lowM_apply {f : (Fin (k + 2) → K) → Fin (k + 2) → K} (hf : ∀ j, Measurable fun z => f z j)
    (r c : Fin (k + 2)) : Measurable fun z => lowM (f z) r c := by
  simp only [lowM, of_apply]
  split_ifs
  · exact hf r
  · exact (hf 0).inv
  · exact measurable_const
  · exact measurable_const

theorem measurable_qMat_mulVec (i : Fin (k + 2)) (j : Fin (k + 2)) :
    Measurable fun z : Fin (k + 2) → K => (qMat i *ᵥ z) j := by
  show Measurable fun z : Fin (k + 2) → K => ∑ s, qMat i j s * z s
  exact Finset.measurable_sum _ fun s _ => (measurable_pi_apply s).const_mul _

/-- **The local section is measurable** (entrywise). -/
theorem measurable_secM_apply {B : Set K} (hB : MeasurableSet B) (r c : Fin (k + 2)) :
    Measurable fun z : Fin (k + 2) → K => secM B z r c := by
  have hsum : (fun z : Fin (k + 2) → K => secM B z r c) = fun z => ∑ i : Fin (k + 2),
      if piv B z = i then (qInv i * lowM (qMat i *ᵥ z) : Matrix (Fin (k + 2)) (Fin (k + 2)) K) r c else 0 := by
    funext z
    rw [Finset.sum_ite_eq Finset.univ (piv B z), if_pos (Finset.mem_univ _)]
    rfl
  rw [hsum]
  refine Finset.measurable_sum _ fun i _ => Measurable.ite (measurableSet_piv_eq hB i) ?_ measurable_const
  show Measurable fun z : Fin (k + 2) → K => ∑ s, qInv i r s * lowM (qMat i *ᵥ z) s c
  exact Finset.measurable_sum _ fun s _ =>
    (measurable_lowM_apply (fun j => measurable_qMat_mulVec i j) s c).const_mul _

end MeasLocal

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Primitive vectors -/

/-- $\mathcal O_v$ as a subring of $F_v$. -/
abbrev finO (v : HeightOneSpectrum (𝓞 F)) : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring

/-- The real component at `w` of a vector of $\mathbb A_F^n$. -/
abbrev compR (y : AdeleSpace F (Fin (k + 2))) (w : {w : InfinitePlace F // w.IsReal}) : Fin (k + 2) → ℝ :=
  fun j => (y j).1.1 w

/-- The complex component at `w`. -/
abbrev compC (y : AdeleSpace F (Fin (k + 2))) (w : {w : InfinitePlace F // w.IsComplex}) : Fin (k + 2) → ℂ :=
  fun j => (y j).1.2 w

/-- The component at the finite place `v`. -/
abbrev compV (y : AdeleSpace F (Fin (k + 2))) (v : HeightOneSpectrum (𝓞 F)) : Fin (k + 2) → v.adicCompletion F :=
  fun j => (y j).2 v

variable (F k) in
/-- **Primitive vectors** of $\mathbb A_F^n$, $n = k + 2$: nonzero at every place, primitive at almost all finite places. -/
def primSetN : Set (AdeleSpace F (Fin (k + 2))) :=
  {y | (∀ w, compR y w ≠ 0) ∧ (∀ w, compC y w ≠ 0) ∧ (∀ v, compV y v ≠ 0) ∧
    ∀ᶠ v in cofinite, IsPrimN (finO v) (compV y v)}

/-! ### The adelic section -/

/-- The archimedean part of the entry $(r,c)$ of the section. -/
def secInf (y : AdeleSpace F (Fin (k + 2))) (r c : Fin (k + 2)) : mixedSpace F :=
  (fun w => secM ballR (compR y w) r c, fun w => secM ballC (compC y w) r c)

/-- The finite part of the entry $(r,c)$ of the section, on the eventually primitive vectors. -/
def secFinOf (y : AdeleSpace F (Fin (k + 2))) (h : ∀ᶠ v in cofinite, IsPrimN (finO v) (compV y v))
    (r c : Fin (k + 2)) : AF :=
  ⟨fun v => secM (finO v : Set (v.adicCompletion F)) (compV y v) r c,
    h.mono fun v hv => secM_mem hv.1 (inv_piv_mem _ hv) r c⟩

/-- The finite part of the entry $(r,c)$ of the section (junk `0` off the primitive vectors). -/
def secFin (y : AdeleSpace F (Fin (k + 2))) (r c : Fin (k + 2)) : AF :=
  if h : ∀ᶠ v in cofinite, IsPrimN (finO v) (compV y v) then secFinOf y h r c else 0

theorem secFin_apply (y : AdeleSpace F (Fin (k + 2))) (r c : Fin (k + 2)) (v : HeightOneSpectrum (𝓞 F)) :
    secFin y r c v = if ∀ᶠ v in cofinite, IsPrimN (finO v) (compV y v) then
      secM (finO v : Set (v.adicCompletion F)) (compV y v) r c else 0 := by
  unfold secFin
  by_cases h : ∀ᶠ v in cofinite, IsPrimN (finO v) (compV y v)
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl
  · simp only [h, ↓reduceDIte, ↓reduceIte]; rfl

/-- The matrix of the section. -/
def secMatA (y : AdeleSpace F (Fin (k + 2))) : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F) :=
  fun r c => (secInf y r c, secFin y r c)

/-- Projection of the adeles to a real place. -/
def projR (w : {w : InfinitePlace F // w.IsReal}) : Adeles F →+* ℝ :=
  (Pi.evalRingHom _ w).comp ((RingHom.fst _ _).comp (RingHom.fst (mixedSpace F) AF))

/-- Projection of the adeles to a complex place. -/
def projC (w : {w : InfinitePlace F // w.IsComplex}) : Adeles F →+* ℂ :=
  (Pi.evalRingHom _ w).comp ((RingHom.snd _ _).comp (RingHom.fst (mixedSpace F) AF))

/-- Projection of the adeles to a finite place. -/
def projV (v : HeightOneSpectrum (𝓞 F)) : Adeles F →+* v.adicCompletion F :=
  (evalAt v).comp (RingHom.snd (mixedSpace F) AF)

/-- An adele is determined by its components. -/
theorem adele_ext {a b : Adeles F} (hR : ∀ w, projR w a = projR w b) (hC : ∀ w, projC w a = projC w b)
    (hV : ∀ v, projV v a = projV v b) : a = b := by
  refine Prod.ext (Prod.ext (funext hR) (funext hC)) ?_
  exact Subtype.ext (funext hV)

theorem det_secMatA {y : AdeleSpace F (Fin (k + 2))} (hy : y ∈ primSetN F k) : (secMatA y).det = 1 := by
  obtain ⟨hR, hC, hV, hP⟩ := hy
  refine adele_ext (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · rw [RingHom.map_det, map_one]
    have : (projR w).mapMatrix (secMatA y) = secM ballR (compR y w) := by ext r c; rfl
    rw [this]
    exact det_secM (exists_pivP_norm (hR w))
  · rw [RingHom.map_det, map_one]
    have : (projC w).mapMatrix (secMatA y) = secM ballC (compC y w) := by ext r c; rfl
    rw [this]
    exact det_secM (exists_pivP_norm (hC w))
  · rw [RingHom.map_det, map_one]
    have : (projV v).mapMatrix (secMatA y) = secM (finO v : Set (v.adicCompletion F)) (compV y v) := by
      refine Matrix.ext fun r c => ?_
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      show evalAt v (secFin y r c) = _
      rw [evalAt_apply, secFin_apply, if_pos hP]
    rw [this]
    exact det_secM (exists_pivP_valuationSubring _ (hV v))

/-- **The section** $s : \mathbb A_F^n\to\mathrm{SL}_n(\mathbb A_F)$, $s(y)e_0 = y$ on the primitive vectors (and $1$
off them). -/
def secN (y : AdeleSpace F (Fin (k + 2))) : SLnA F (Fin (k + 2)) :=
  if hy : y ∈ primSetN F k then ⟨secMatA y, det_secMatA hy⟩ else 1

theorem secN_apply (y : AdeleSpace F (Fin (k + 2))) (r c : Fin (k + 2)) :
    (secN y : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) r c =
      if y ∈ primSetN F k then secMatA y r c else (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) r c := by
  by_cases hy : y ∈ primSetN F k
  · simp only [secN, hy, ↓reduceDIte, ↓reduceIte]
  · simp only [secN, hy, ↓reduceDIte, ↓reduceIte, Matrix.SpecialLinearGroup.coe_one]

/-! ### The first column -/

/-- The first column $ge_0$. -/
def col (g : SLnA F (Fin (k + 2))) : AdeleSpace F (Fin (k + 2)) :=
  fun i => (g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) i 0

theorem col_secN {y : AdeleSpace F (Fin (k + 2))} (hy : y ∈ primSetN F k) : col (secN y) = y := by
  funext r
  simp only [col, secN_apply, if_pos hy]
  refine adele_ext (fun w => ?_) (fun w => ?_) (fun v => ?_)
  · exact secM_col _ (compR y w) r
  · exact secM_col _ (compC y w) r
  · show secFin y r 0 v = (y r).2 v
    rw [secFin_apply, if_pos hy.2.2.2]
    exact secM_col _ (compV y v) r

theorem col_mul (g h : SLnA F (Fin (k + 2))) :
    col (g * h) = (g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ col h := by
  funext i
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- **The first column of every $g\in\mathrm{SL}_n(\mathbb A_F)$ is primitive.** -/
theorem col_mem_primSetN (g : SLnA F (Fin (k + 2))) : col g ∈ primSetN F k := by
  set M := (g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F))
  have hdet : M.det = 1 := g.2
  have hcol : ∀ {L : Type} [Field L] (φ : Adeles F →+* L), (fun j => φ (M j 0)) ≠ 0 := by
    intro L _ φ h0
    have h1 : (φ.mapMatrix M).det = 1 := by rw [← RingHom.map_det, hdet, map_one]
    have h2 : (φ.mapMatrix M).det = 0 :=
      det_eq_zero_of_column_eq_zero 0 fun j => congrFun h0 j
    rw [h1] at h2; exact one_ne_zero h2
  refine ⟨fun w => hcol (projR w), fun w => hcol (projC w), fun v => hcol (projV v), ?_⟩
  -- almost all finite components of `g` are integral
  have hint : ∀ᶠ v in cofinite, ∀ r c, (M r c).2 v ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun r c => (M r c).2.2
  filter_upwards [hint] with v hv
  have h1 : ((projV v).mapMatrix M).det = 1 := by rw [← RingHom.map_det, hdet, map_one]
  exact isPrimN_col (v.adicCompletionIntegers F) (g := (projV v).mapMatrix M) (fun r c => hv r c) h1

/-! ### Measurability -/

theorem measurable_compR (w : {w : InfinitePlace F // w.IsReal}) :
    Measurable fun y : AdeleSpace F (Fin (k + 2)) => compR y w :=
  measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply w).comp (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply j)))

theorem measurable_compC (w : {w : InfinitePlace F // w.IsComplex}) :
    Measurable fun y : AdeleSpace F (Fin (k + 2)) => compC y w :=
  measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply w).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply j)))

theorem measurable_compV (v : HeightOneSpectrum (𝓞 F)) :
    Measurable fun y : AdeleSpace F (Fin (k + 2)) => compV y v :=
  measurable_pi_iff.mpr fun j => (measurable_finiteAdele_eval v).comp (measurable_snd.comp (measurable_pi_apply j))

theorem measurableSet_isPrimN (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {y : AdeleSpace F (Fin (k + 2)) | IsPrimN (finO v) (compV y v)} := by
  have hO := measurableSet_O v
  have hc : ∀ j, Measurable fun y : AdeleSpace F (Fin (k + 2)) => (y j).2 v := fun j =>
    (measurable_finiteAdele_eval v).comp (measurable_snd.comp (measurable_pi_apply j))
  simp only [IsPrimN, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  refine (MeasurableSet.iInter fun j => hO.preimage (hc j)).inter (MeasurableSet.iUnion fun j => ?_)
  exact ((measurableSet_singleton 0).compl.preimage (hc j)).inter (hO.preimage (hc j).inv)

theorem measurableSet_primSetN : MeasurableSet (primSetN F k) := by
  unfold primSetN
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · exact MeasurableSet.iInter fun w => (measurableSet_singleton 0).compl.preimage (measurable_compR w)
  · exact MeasurableSet.iInter fun w => (measurableSet_singleton 0).compl.preimage (measurable_compC w)
  · exact MeasurableSet.iInter fun v => (measurableSet_singleton 0).compl.preimage (measurable_compV v)
  · exact measurableSet_eventually_cofinite measurableSet_isPrimN

theorem measurable_secInf (r c : Fin (k + 2)) :
    Measurable fun y : AdeleSpace F (Fin (k + 2)) => secInf y r c := by
  refine Measurable.prodMk (measurable_pi_iff.mpr fun w => ?_) (measurable_pi_iff.mpr fun w => ?_)
  · exact (measurable_secM_apply Metric.isClosed_closedBall.measurableSet r c).comp (measurable_compR w)
  · exact (measurable_secM_apply Metric.isClosed_closedBall.measurableSet r c).comp (measurable_compC w)

theorem measurable_secFin (r c : Fin (k + 2)) :
    Measurable fun y : AdeleSpace F (Fin (k + 2)) => secFin y r c := by
  refine measurable_finiteAdele_of_forall_eval fun v => ?_
  simp only [secFin_apply]
  exact Measurable.ite (measurableSet_eventually_cofinite measurableSet_isPrimN)
    ((measurable_secM_apply (measurableSet_O v) r c).comp (measurable_compV v)) measurable_const

/-- **The section is measurable.** -/
theorem measurable_secN : Measurable (secN (F := F) (k := k)) := by
  refine measurable_SLnA_iff.mpr fun r c => ?_
  simp only [secN_apply]
  exact Measurable.ite measurableSet_primSetN ((measurable_secInf r c).prodMk (measurable_secFin r c))
    measurable_const

theorem measurable_col : Measurable (col (F := F) (k := k)) :=
  measurable_pi_iff.mpr fun i => measurable_SLnA_entry i 0

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
