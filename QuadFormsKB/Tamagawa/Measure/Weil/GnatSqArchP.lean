import QuadFormsKB.Tamagawa.Measure.Weil.ArchPolarGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArchSO
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqCombine
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqAnyD

/-!
# The $\mathrm{SL}_1$ factor of the square model on a cone test set

**Layer:** $F$ any number field (complex places allowed), $D = \mathbb H[F,a,b]$ any quaternion algebra, the norm forms
$Q_w = \langle1,-a,-b,ab\rangle^{\sigma_w}$ at the archimedean places, sets $A_w\subseteq\{Q_w = 1\}$ and radial sets $T_w$
($\log$-radii at a real place with $0\in T_w$; $1\in T_w\subseteq\{\operatorname{Re}\beta>0\}$ at a complex place), and the finite data
$S$, $m_v$.

The test set of the $\mathrm{SL}_1$ factor is
$$E = \{x\in(D\otimes\mathbb A)^\times : x_w\in\mathrm{cone}(T_w,A_w)\ \forall w\mid\infty,\ x_f\in E_S^{\mathrm f}\}$$
(`Eset`), an open set; $E\cap\mathrm{SL}_1$ consists of the $x$ of reduced norm $1$ with $x_w\in A_w$ and $x_f\in E^{\mathrm f}_S$.

* **`muSL1N_Eset_mul`** (the reduced-norm fibration of `tamQuat` on $E$, every number field):
  $$\mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\omega_\infty(N)\,\mu_f(N_E) = \omega^{D^\times}_\infty(Y)\cdot\mu_{D^\times}(E^{\mathrm f}_S),$$
  $Y$ the archimedean cone (`archCone`), $N$ its reduced-norm shell (`nrdShell`), $N_E$ = `NE S m`.

Together with `omegaQuatInf_archCone_eq` ($\omega^{D^\times}_\infty(Y) = 8^{r_2}\sigma(A)\,\omega_\infty(N)$) this computes the
$\mathrm{SL}_1$ factor of $\mu_P$ in terms of the sphere Leray measures.
-/

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain WithZero
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ArchPolar LerayPadic

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}

/-! ### Coordinates and reduced norms at a place -/

theorem quatCoordR_eq_qVec (w : {w : InfinitePlace F // w.IsReal}) (y : QuatInf (a : F) (b : F)) :
    quatCoordR (a : F) (b : F) w y = qVec (projR (a : F) (b : F) w y) := by
  funext i; fin_cases i <;> rfl

theorem quatCoordC_eq_qVec (w : {w : InfinitePlace F // w.IsComplex}) (y : QuatInf (a : F) (b : F)) :
    quatCoordC (a : F) (b : F) w y = qVec (projC (a : F) (b : F) w y) := by
  funext i; fin_cases i <;> rfl

theorem nrd_projR (w : {w : InfinitePlace F // w.IsReal}) (y : QuatInf (a : F) (b : F)) :
    nrd (projR (a : F) (b : F) w y) = (nrdInf (a : F) (b : F) y).1 w := by
  rw [nrd, nrdInf]
  simp only [projR_re, projR_imI, projR_imJ, projR_imK, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Prod.fst_add, Prod.fst_mul,
    Prod.fst_sub, Prod.fst_neg, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Prod.fst_zero, Pi.zero_apply,
    mixedEmbedding_apply_isReal]
  ring

theorem nrd_projC (w : {w : InfinitePlace F // w.IsComplex}) (y : QuatInf (a : F) (b : F)) :
    nrd (projC (a : F) (b : F) w y) = (nrdInf (a : F) (b : F) y).2 w := by
  rw [nrd, nrdInf]
  simp only [projC_re, projC_imI, projC_imJ, projC_imK, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Prod.snd_add, Prod.snd_mul,
    Prod.snd_sub, Prod.snd_neg, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Prod.snd_zero, Pi.zero_apply,
    mixedEmbedding_apply_isComplex]
  ring

theorem eval_quatCoordR (w : {w : InfinitePlace F // w.IsReal}) (y : QuatInf (a : F) (b : F)) :
    (QRe (qSq a b) w).eval (quatCoordR (a : F) (b : F) w y) = (nrdInf (a : F) (b : F) y).1 w := by
  rw [quatCoordR_eq_qVec, eval_qRe_qSq, vecQ_qVec, nrd_projR]

theorem eval_quatCoordC (w : {w : InfinitePlace F // w.IsComplex}) (y : QuatInf (a : F) (b : F)) :
    (QCx (qSq a b) w).eval (quatCoordC (a : F) (b : F) w y) = (nrdInf (a : F) (b : F) y).2 w := by
  rw [quatCoordC_eq_qVec, eval_qCx_qSq, vecQ_qVec, nrd_projC]

theorem qVec_unitAtR (w : {w : InfinitePlace F // w.IsReal}) (x : (QuatAdele (a : F) (b : F))ˣ) :
    qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w) =
      quatCoordR (a : F) (b : F) w ((quatUnitsEquiv (a : F) (b : F) x).1 : QuatInf (a : F) (b : F)) := by
  rw [quatCoordR_eq_qVec]; rfl

theorem qVec_unitAtC (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatAdele (a : F) (b : F))ˣ) :
    qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w) =
      quatCoordC (a : F) (b : F) w ((quatUnitsEquiv (a : F) (b : F) x).1 : QuatInf (a : F) (b : F)) := by
  rw [quatCoordC_eq_qVec]; rfl

theorem qVec_algebraMap_mul {K : Type*} [Field K] {A B : K} (r : K) (y : ℍ[K,A,B]) :
    qVec (algebraMap K ℍ[K,A,B] r * y) = r • qVec y := by
  funext i; fin_cases i <;> simp [qVec, QuaternionAlgebra.algebraMap_eq]

theorem nrd_algebraMap_quat {K : Type*} [Field K] {A B : K} (r : K) : nrd (algebraMap K ℍ[K,A,B] r) = r ^ 2 := by
  simp [nrd, QuaternionAlgebra.algebraMap_eq]

/-! ### Membership in the cones after a scalar -/

theorem mem_coneR_smul_iff {Q : QuadForm ℝ 4} {T : Set ℝ} {A : Set (SphereLeray.Sph Q 1)} {s : ℝ} (hs : s ∈ T)
    (p : SphereLeray.Sph Q 1) : Real.exp s • (p : Fin 4 → ℝ) ∈ coneR Q T A ↔ p ∈ A := by
  constructor
  · rintro ⟨⟨t, x⟩, ⟨-, hx⟩, h⟩
    have := SphereLeray.pol_injective (Q := Q) one_ne_zero (show SphereLeray.pol Q 1 (t, x) =
      SphereLeray.pol Q 1 (s, p) from h)
    rw [Prod.mk.injEq] at this
    rw [← this.2]; exact hx
  · intro hp; exact ⟨(s, p), ⟨hs, hp⟩, rfl⟩

/-! ### The test set -/

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ)

/-- **The test set** $E = \{x : x_\infty\in Y,\ x_f\in E^{\mathrm f}_S\}$ (`archCone` at the norm forms). -/
def Eset (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
    (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QRe (qSq a b) w) 1))
    (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
    (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QCx (qSq a b) w) 1)) :
    Set (QuatAdele (a : F) (b : F))ˣ :=
  quatUnitsEquiv (a : F) (b : F) ⁻¹'
    (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC ×ˢ
      (econgS a b S m : Set (QuatFin (a : F) (b : F))ˣ))

variable (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
  (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QRe (qSq a b) w) 1))
  (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
  (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QCx (qSq a b) w) 1))

theorem mem_Eset {x : (QuatAdele (a : F) (b : F))ˣ} :
    x ∈ Eset S m TR AR TC AC ↔
      (∀ w, qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w) ∈ coneR (QRe (qSq a b) w) (TR w) (AR w)) ∧
      (∀ w, qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w) ∈ coneC (QCx (qSq a b) w) (TC w) (AC w)) ∧
      quatFinPart a b x ∈ econgS a b S m := by
  simp only [qVec_unitAtR, qVec_unitAtC]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem measurableSet_Eset (hm1 : ∀ v, 1 ≤ m v) (hTRm : ∀ w, MeasurableSet (TR w)) (hARm : ∀ w, MeasurableSet (AR w))
    (hTCm : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hACm : ∀ w, MeasurableSet (AC w)) :
    MeasurableSet (Eset S m TR AR TC AC) :=
  (((measurableSet_archConeSet (a := (a : F)) (b := (b : F)) _ _ TR AR TC AC hTRm hARm hTCm hTh hACm).preimage
    Units.continuous_val.measurable).prod (isOpen_econgS S m hm1).measurableSet).preimage
      (quatUnitsEquiv (a : F) (b : F)).continuous.measurable

/-! ### Reduced norms on the test set -/

/-- $\operatorname{nrd}$ is multiplicative on $\mathbb A$-points: the general form of `nrdUnit_mkAdeleUnit_eq`. -/
theorem nrdUnit_mkAdeleUnit_eq_gen (t : (Adeles F)ˣ)
    (βR : ∀ w : {w : InfinitePlace F // w.IsReal}, (HRe a b w)ˣ)
    (βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (HCx a b w)ˣ)
    (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV (a : F) (b : F) v)ˣ) (hev)
    (hR : ∀ w, nrd ((βR w : (HRe a b w)ˣ) : HRe a b w) = (t : Adeles F).1.1 w)
    (hC : ∀ w, nrd ((βC w : (HCx a b w)ˣ) : HCx a b w) = (t : Adeles F).1.2 w)
    (hF : ∀ v, nrdLoc _ _ ((β v : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v) :
    nrdUnit (mkAdeleUnit (a : F) (b : F) βR βC β hev) = t := by
  apply Units.ext
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) (Subtype.ext (funext fun v => ?_))
  · rw [← nrd_unitAtR, unitAtR_mkAdeleUnit, hR]
  · rw [← nrd_unitAtC, unitAtC_mkAdeleUnit, hC]
  · change ((nrdUnit _ : (Adeles F)ˣ) : Adeles F).2 v = (t : Adeles F).2 v
    rw [← nrd_unitAtA, unitAtA_mkAdeleUnit, ← nrdLoc_eq_nrd, hF]

theorem finPart_nrd_mem_NE (hsm : ∀ v ∈ S, sExp v < m v) {x : (QuatAdele (a : F) (b : F))ˣ}
    (hx : x ∈ ES a b S m) : finPart (nrdUnit x) ∈ NE S m := by
  have hx' := (mem_ES a b S m).1 hx
  intro v
  have hval : ((unitAt (finPart (nrdUnit x)) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      nrdLoc _ _ ((unitAtA (a : F) (b : F) v x : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) := by
    rw [nrdLoc_eq_nrd, nrd_unitAtA]; rfl
  split_ifs with hv
  · show Valued.v (((unitAt (finPart (nrdUnit x)) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) - 1) ≤ _
    rw [hval]
    exact valued_nrdLoc_sub_one_le v a b (valued_two_eq v) (hsm v hv).le (hx'.2 v hv)
  · show Valued.v ((unitAt (finPart (nrdUnit x)) v : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1
    rw [hval]
    exact ((mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w)
      (fun w => valued_algebraMap_le_one b w) _).1 (hx'.1 v)).2

theorem exists_local_econg (hm1 : ∀ v, 1 ≤ m v)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hsm : ∀ v ∈ S, sExp v < m v) (t : (Adeles F)ˣ) (hfin : finPart t ∈ NE S m) :
    ∃ y : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV (a : F) (b : F) v)ˣ,
      (∀ v, y v ∈ lamLocUnits (a : F) (b : F) v) ∧
      (∀ v, nrdLoc _ _ ((y v : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v) ∧
      (∀ v ∈ S, y v ∈ oneAddCong v a b (m v)) := by
  have hloc : ∀ v, ∃ y : (QuatV (a : F) (b : F) v)ˣ, y ∈ lamLocUnits (a : F) (b : F) v ∧
      nrdLoc _ _ (y : QuatV (a : F) (b : F) v) = (t : Adeles F).2 v ∧ (v ∈ S → y ∈ oneAddCong v a b (m v)) := by
    intro v
    have h := hfin v
    by_cases hv : v ∈ S
    · rw [if_pos hv] at h
      obtain ⟨y, hy, hyt⟩ := exists_oneAddCong_nrd v (a := a) (b := b) (valued_two_eq v) (hsm v hv)
        (show Valued.v ((t : Adeles F).2 v - 1) ≤ _ from h)
      exact ⟨y, hy.1, hyt, fun _ => hy⟩
    · rw [if_neg hv] at h
      obtain ⟨y, hy, hyt⟩ := exists_lamLocUnits_nrd v (a := a) (b := b) (hS v hv).1 (hS v hv).2.1
        (show Valued.v ((t : Adeles F).2 v) = 1 from h)
      exact ⟨y, hy, hyt, fun h' => absurd h' hv⟩
  choose y hyL hyt hyS using hloc
  exact ⟨y, hyL, hyt, hyS⟩

theorem eval_qVec_unitAtR (w : {w : InfinitePlace F // w.IsReal}) (x : (QuatAdele (a : F) (b : F))ˣ) :
    (QRe (qSq a b) w).eval (qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w)) =
      ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.1 w := by
  rw [eval_qRe_qSq, vecQ_qVec, nrd_unitAtR]

theorem eval_qVec_unitAtC (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatAdele (a : F) (b : F))ˣ) :
    (QCx (qSq a b) w).eval (qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w)) =
      ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.2 w := by
  rw [eval_qCx_qSq, vecQ_qVec, nrd_unitAtC]

/-- **The reduced norm of the test set** lies in $N\times N_E$. -/
theorem nrd_mem_of_mem_Eset (hsm : ∀ v ∈ S, sExp v < m v) {x : (QuatAdele (a : F) (b : F))ˣ}
    (hx : x ∈ Eset S m TR AR TC AC) :
    nrdUnit x ∈ idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NE S m) := by
  obtain ⟨hR, hC, hf⟩ := (mem_Eset S m TR AR TC AC).1 hx
  refine ⟨⟨fun w => ?_, fun w => ?_⟩, finPart_nrd_mem_NE S m hsm hf⟩
  · obtain ⟨⟨t, p⟩, ⟨ht, -⟩, hp⟩ := hR w
    refine ⟨t, ht, ?_⟩
    change Real.exp (2 * t) = ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.1 w
    rw [← eval_qVec_unitAtR, ← hp, SphereLeray.eval_pol, mul_one]
  · obtain ⟨⟨β, p⟩, ⟨hβ, -⟩, hp⟩ := hC w
    refine ⟨β, ⟨β, hβ, rfl⟩, ?_⟩
    change (β : ℂ) ^ 2 = ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.2 w
    rw [← eval_qVec_unitAtC, ← hp, SphereLerayC.eval_polC, mul_one]

/-! ### The fibration -/

/-- The point of $S_1$ given by the $w$-component of an element of reduced norm $1$. -/
def sphPtOfR (w : {w : InfinitePlace F // w.IsReal}) (k : (QuatAdele (a : F) (b : F))ˣ) (hk : nrdUnit k = 1) :
    SphereLeray.Sph (QRe (qSq a b) w) 1 :=
  ⟨qVec ((unitAtR (a : F) (b : F) w k : (HRe a b w)ˣ) : HRe a b w), by
    show (QRe (qSq a b) w).eval _ = 1
    rw [eval_qVec_unitAtR, hk]; rfl⟩

def sphPtOfC (w : {w : InfinitePlace F // w.IsComplex}) (k : (QuatAdele (a : F) (b : F))ˣ) (hk : nrdUnit k = 1) :
    SphereLerayC.SphC (QCx (qSq a b) w) 1 :=
  ⟨qVec ((unitAtC (a : F) (b : F) w k : (HCx a b w)ˣ) : HCx a b w), by
    show (QCx (qSq a b) w).eval _ = 1
    rw [eval_qVec_unitAtC, hk]; rfl⟩

set_option maxHeartbeats 1600000 in
/-- **The reduced-norm fibration of `tamQuat` on the test set**:
$\mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\omega_\infty(N)\,\mu_f(N_E) = \omega^{D^\times}_\infty(Y)\cdot\mu_{D^\times}(E^{\mathrm f}_S)$
(every number field, every quaternion algebra). -/
theorem muSL1N_Eset_mul (ha : a ≠ 0) (hb : b ≠ 0) (hm1 : ∀ v, 1 ≤ m v)
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hsm : ∀ v ∈ S, sExp v < m v)
    (hTRm : ∀ w, MeasurableSet (TR w)) (hARm : ∀ w, MeasurableSet (AR w))
    (hTCm : ∀ w, MeasurableSet (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hACm : ∀ w, MeasurableSet (AC w))
    (h0 : ∀ w, (0 : ℝ) ∈ TR w) (h1 : ∀ w, (1 : ℂˣ) ∈ TC w) :
    muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ Eset S m TR AR TC AC} *
        (omegaInf F (nrdShell F TR TC) * muFinUnits F (NE S m)) =
      omegaQuatInf (a : F) (b : F)
          (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC) *
        muFinQuat (a : F) (b : F) (econgS a b S m) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  have hb' : (b : F) ≠ 0 := by simpa using hb
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  have hEm := measurableSet_Eset S m TR AR TC AC hm1 hTRm hARm hTCm hTh hACm
  have hNm : MeasurableSet (idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NE S m)) :=
    (((measurableSet_shellSet (F := F) hTRm hTCm hTh).preimage Units.continuous_val.measurable).prod
      (measurableSet_ideleBox S _ fun v _ => measurableSet_nU m v)).preimage (idelesEquiv F).continuous.measurable
  set X : Set (posA (a : F) (b : F)) := Subtype.val ⁻¹' (idelesEquiv F ⁻¹' (nrdShell F TR TC ×ˢ NE S m)) with hX
  have hXmeas : MeasurableSet X := hNm.preimage measurable_subtype_coe
  -- the key property of a scalar base point
  have hkey : ∀ q ∈ X, ∃ x₀ : (QuatAdele (a : F) (b : F))ˣ, nrdPos (a : F) (b : F) x₀ = q ∧
      ∀ k : (QuatAdele (a : F) (b : F))ˣ, nrdUnit k = 1 → (x₀ * k ∈ Eset S m TR AR TC AC ↔ k ∈ Eset S m TR AR TC AC) := by
    intro q hq
    obtain ⟨⟨hqR, hqC⟩, hqf⟩ := hq
    choose s hs hs' using hqR
    choose β hβ using hqC
    obtain ⟨y, hyL, hyt, hyS⟩ := exists_local_econg S m hm1 hS hsm (q : (Adeles F)ˣ) hqf
    set βR : ∀ w : {w : InfinitePlace F // w.IsReal}, (HRe a b w)ˣ := fun w =>
      Units.map (algebraMap ℝ (HRe a b w)).toMonoidHom (Units.mk0 (Real.exp (s w)) (Real.exp_pos _).ne')
    have hβ0 : ∀ w, ((β w : ℂ)) ≠ 0 := fun w => by
      obtain ⟨⟨γ, -, hγ⟩, -⟩ := hβ w; rw [← hγ]; exact γ.ne_zero
    set βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (HCx a b w)ˣ := fun w =>
      Units.map (algebraMap ℂ (HCx a b w)).toMonoidHom (Units.mk0 (β w) (hβ0 w))
    refine ⟨mkAdeleUnit (a : F) (b : F) βR βC y (Filter.Eventually.of_forall hyL), Subtype.ext ?_, fun k hk => ?_⟩
    · refine nrdUnit_mkAdeleUnit_eq_gen _ βR βC y _ (fun w => ?_) (fun w => ?_) hyt
      · change nrd (algebraMap ℝ (HRe a b w) (Real.exp (s w))) = _
        rw [nrd_algebraMap_quat]
        exact (by rw [← Real.exp_nat_mul]; push_cast; ring_nf : Real.exp (s w) ^ 2 = Real.exp (2 * s w)).trans (hs' w)
      · change nrd (algebraMap ℂ (HCx a b w) (β w)) = _
        rw [nrd_algebraMap_quat]; exact (hβ w).2
    · rw [mem_Eset, mem_Eset]
      refine and_congr (forall_congr' fun w => ?_) (and_congr (forall_congr' fun w => ?_) ?_)
      · rw [map_mul, unitAtR_mkAdeleUnit, Units.val_mul]
        change qVec (algebraMap ℝ (HRe a b w) (Real.exp (s w)) * _) ∈ _ ↔ _
        rw [qVec_algebraMap_mul]
        have e1 := mem_coneR_smul_iff (A := AR w) (hs w) (sphPtOfR w k hk)
        have e2 := mem_coneR_smul_iff (A := AR w) (h0 w) (sphPtOfR w k hk)
        rw [Real.exp_zero, one_smul] at e2
        exact e1.trans e2.symm
      · rw [map_mul, unitAtC_mkAdeleUnit, Units.val_mul]
        change qVec (algebraMap ℂ (HCx a b w) (β w) * _) ∈ _ ↔ _
        rw [qVec_algebraMap_mul]
        obtain ⟨⟨γ, hγT, hγ⟩, -⟩ := hβ w
        have hβw : (β w : ℂ) = (γ : ℂ) := hγ.symm
        have e1 := mem_coneC_iff (QCx (qSq a b) w) (A := AC w) (hTh w) (hTh w hγT) (sphPtOfC w k hk)
        have e2 := mem_coneC_iff (QCx (qSq a b) w) (A := AC w) (hTh w) (hTh w (h1 w)) (sphPtOfC w k hk)
        rw [Units.val_one, one_smul] at e2
        rw [hβw]
        exact (e1.trans (and_iff_right hγT)).trans ((and_iff_right (h1 w)).symm.trans e2.symm)
      · rw [map_mul]
        have hx₀ : quatFinPart a b (mkAdeleUnit (a : F) (b : F) βR βC y (Filter.Eventually.of_forall hyL)) ∈
            econgS a b S m := by
          rw [mem_econgS]
          refine ⟨fun v => ?_, fun v hv => ?_⟩
          · change unitAtA _ _ v _ ∈ _; rw [unitAtA_mkAdeleUnit]; exact hyL v
          · change unitAtA _ _ v _ ∈ _; rw [unitAtA_mkAdeleUnit]; exact hyS v hv
        exact (econgS a b S m).mul_mem_cancel_left hx₀
  have hcE : muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ Eset S m TR AR TC AC} =
      muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ Eset S m TR AR TC AC} :=
    (muSL1P_eq_muSL1 ha hb _ hEm).trans (muSL1N_eq_muSL1 ha hb _ hEm).symm
  have hT : tamQuat (a : F) (b : F) (Eset S m TR AR TC AC) =
      omegaQuatInf (a : F) (b : F)
          (archCone (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) TR AR TC AC) *
        muFinQuat (a : F) (b : F) (econgS a b S m) := tamQuat_prod _ _
  rw [← hT, ← tamIdeles_prod, ← fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb']
  rw [fibMeas_apply_of_kern _ _ measurable_nrdPos _ _ hEm hXmeas
    (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
      {k : (nrdPos (a : F) (b : F)).ker | (k : (QuatAdele (a : F) (b : F))ˣ) ∈ Eset S m TR AR TC AC}) ?_ ?_, hcE]
  · congr 1
    symm
    rw [muPosA, measurableEmbedding_posA.comap_apply]
    congr 1
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩; exact hq
    · intro h
      have hR : ∀ w, ((idelesEquiv F t).1 : mixedSpace F).1 w ∈ (fun s : ℝ => Real.exp (2 * s)) '' TR w := h.1.1
      have hpos : t ∈ posA (a : F) (b : F) := fun w hw _ => by
        obtain ⟨s, -, hs⟩ := hR ⟨w, hw⟩
        change 0 < ((t : Adeles F)).1.1 ⟨w, hw⟩
        rw [show ((t : Adeles F)).1.1 ⟨w, hw⟩ = Real.exp (2 * s) from hs.symm]
        exact Real.exp_pos _
      exact ⟨⟨t, hpos⟩, h, rfl⟩
  · intro q hq
    obtain ⟨x₀, hx₀, hk⟩ := hkey q hq
    refine ⟨x₀, hx₀, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hEm]
    congr 1
    ext k
    exact hk k ((mem_ker_nrdPos).1 k.2)
  · intro x hx
    rw [NormalFib.fibK_apply _ _ _ hEm]
    convert measure_empty (μ := muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb')
    ext k
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hxk
    apply hx
    have h := nrd_mem_of_mem_Eset S m TR AR TC AC hsm hxk
    rw [nrdUnit_mul, mem_ker_nrdPos.1 k.2, mul_one] at h
    exact h

end QuadFormsKB.Tamagawa.Measure.Weil

end
