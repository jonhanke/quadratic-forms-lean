/-
# Hanke 2005, §4.2: $\mathrm{vol}_C(C_{\mathbb R})$ is the volume of the fibre of $F_{\mathbb R}$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** A real place where $\varphi_v$ is indefinite: $\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t\ge r$
(`phiQ r t`), $n = q + r$; $G_{\mathbb R} = SO(q, r)$ with the repository's Leray measure $\mu$ (`lerayMeasure`,
coefficient coordinates; Hanke's $\widetilde\omega_G$, in Gram coordinates, is $2^{n(n-1)/2}\mu$), the symmetric space
$Z_{\mathbb R}$ and $F_{\mathbb R}$ of (4.2.3)–(4.2.5) (`ArchSymmetricReal.lean`), and Shimura's invariant measure
$\mu_Z = \delta(z)^{-n/2}\,dz$ on $Z_{\mathbb R}$ ((4.2.8), `muZR`), $dz = \prod_{i,k}dz_{ik}$ the Lebesgue measure on
$\mathbb R^{q\times r}$.

**Main result** (`map_FR_hankeHaar`, unconditional): Hanke's Haar measure pushed forward by $F_{\mathbb R}$ is
$\mathrm{vol}_C(C_{\mathbb R})\cdot\mu_Z$:
$$(F_{\mathbb R})_*\big(2^{n(n-1)/2}\mu\big) = \mathrm{vol}_C(C_{\mathbb R})\,\mu_Z,\qquad
\mathrm{vol}_C(C_{\mathbb R}) = 2\cdot2^{-rn/2}\tau_{\mathbb R}(SO_q(\mathbb R))\,\tau_{\mathbb R}(SO_r(\mathbb R))$$
(`volCReal`), i.e. for every measurable $B\subseteq Z_{\mathbb R}$ the set $F_{\mathbb R}^{-1}(B)\subseteq G_{\mathbb R}$ has
Hanke-volume $\mathrm{vol}_C(C_{\mathbb R})\,\mu_Z(B)$. This is the content of Hanke's computation of $\omega_C$ and
$\int_{C_{\mathbb R}}\omega_C$ (pp. 12–13): the fibres $F_{\mathbb R}^{-1}(z) = \alpha C_{\mathbb R}$ carry total mass
$\mathrm{vol}_C(C_{\mathbb R})$ for the fibre measure with $\widetilde\omega_G = \omega_C\wedge F_{\mathbb R}^*\omega_Z$.

**Proof** (measure-theoretic; no differential forms). By the Leray chart (`volume_region_FR`),
$\mathrm{Leb}\{X : \det X > 0,\ \|\Phi(X) - c_\varphi\|\le\varepsilon,\ \mathrm{zOf}(X_2)\in B\} = \mu(F_{\mathbb R}^{-1}B)
\int_{B_\varepsilon}\rho$. The same region is computed explicitly (`volume_regionR`): write $X = (X_1\mid X_2)$,
$X_2 = P(z)m$ (`lintegral_frames`, Jacobian $2^{-r^2-tr/2}|\det m|^q$), integrate $X_1$ over the fibre
(`lintegral_inner`, Jacobian $\tfrac12|\det T|^{-q/2}$, $T = -{}^tm\,\xi(z)m$) and $m$ by the weighted Gram formula
($\det\xi(z)^{-r/2}$); the powers of $\delta(z) = \det\xi(z)$ combine to $\delta^{q/2}\delta^{-q}\delta^{-r/2} = \delta^{-n/2}$,
Shimura's density. Hence $\mathrm{Leb}(\dots) = 2^{-r^2-tr/2}\tfrac12\,\mu_Z(B)\,I_\varepsilon$, and the box averages
(`tendsto_avg_rho`, `tendsto_Iint`) give $\mu(F_{\mathbb R}^{-1}B) = 2^{-n(n-1)/2}\cdot2^{-r^2-tr/2}\tfrac12c_qc_r\,\mu_Z(B)$,
$c_k = 2\tau_{\mathbb R}(SO_k)$.
-/
import QuadFormsKB.Literature.Hanke2005.ArchBoxReal
import QuadFormsKB.Literature.Hanke2005.ArchFrameCoV
import QuadFormsKB.Literature.Hanke2005.Archimedean

open MeasureTheory Measure Matrix Set Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.ArchVol QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.ArchSOMeasure

variable {r t : ℕ}

/-- **Shimura's invariant measure on $Z_{\mathbb R}$** (Hanke thesis, (4.2.8), p. 12, from Shimura 1999, §4.2):
$\omega_Z = \delta(z)^{-n/2}\bigwedge_{i,k}dz_{ik}$, $n = q + r$, as the measure
$\delta(z)^{-n/2}\,dz$ on $Z_{\mathbb R}\subseteq\mathbb R^{q\times r}$ (Lebesgue measure $dz$ in the $qr$ entries). -/
@[kb "hanke2005crelle" "(4.2.8), p. 12 (ω_Z on Z_R)"]
def muZR (r t : ℕ) : Measure (Fin (r + t) → Fin r → ℝ) :=
  (volume.restrict (ZR r t)).withDensity fun z => ENNReal.ofReal (deltaR z ^ (-((r + t + r : ℕ) : ℝ) / 2))

/-! ### Measurability of $Z_{\mathbb R}$ and auxiliary identities -/

theorem continuous_xiR : Continuous (xiR : (Fin (r + t) → Fin r → ℝ) → Matrix (Fin r) (Fin r) ℝ) := by
  unfold xiR xBlk yBlk; fun_prop

theorem measurableSet_ZR : MeasurableSet (ZR r t) := by
  have hset : ZR r t = (⋂ x : Fin r → ℝ, {z | 0 ≤ x ⬝ᵥ (xiR z *ᵥ x)}) ∩ {z | (xiR z).det ≠ 0} := by
    ext z
    simp only [ZR, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    have hH : (xiR z).IsHermitian := by
      rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, xiR_transpose]
    constructor
    · intro h; exact ⟨fun x => by simpa using h.posSemidef.dotProduct_mulVec_nonneg x, h.det_pos.ne'⟩
    · rintro ⟨h1, h2⟩
      have hps : (xiR z).PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => by simpa using h1 x
      exact hps.posDef_iff_det_ne_zero.mpr h2
  rw [hset]
  have hc : ∀ x : Fin r → ℝ, Continuous fun z : Fin (r + t) → Fin r → ℝ => x ⬝ᵥ (xiR z *ᵥ x) := fun x =>
    continuous_const.dotProduct ((continuous_xiR (r := r) (t := t)).matrix_mulVec continuous_const)
  refine MeasurableSet.inter (isClosed_iInter fun x => isClosed_le continuous_const (hc x)).measurableSet ?_
  · exact (isOpen_ne_fun (continuous_xiR.matrix_det) continuous_const).measurableSet

/-- Upper coordinates of a matrix. -/
def upperOf {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) : UIdx k → ℝ := fun p => S p.1.1 p.1.2

theorem symU_upperOf {k : ℕ} {S : Matrix (Fin k) (Fin k) ℝ} (hS : Sᵀ = S) : symU (upperOf S) = S := by
  ext i j
  simp only [symU, upperOf, of_apply]
  split_ifs
  · rfl
  · exact (congrFun (congrFun hS i) j)

theorem continuous_upperOf {k : ℕ} : Continuous (upperOf : Matrix (Fin k) (Fin k) ℝ → UIdx k → ℝ) := by
  refine continuous_pi fun p => ?_
  unfold upperOf; fun_prop

/-- Columns to matrix. -/
def ofColsR {k m : ℕ} (Y : Fin k → Fin m → ℝ) : Matrix (Fin m) (Fin k) ℝ := Matrix.of fun i j => Y j i

theorem gramH_eq_upperOf {k m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (Y : Fin k → Fin m → ℝ) :
    gramH H Y = upperOf ((ofColsR Y)ᵀ * H * ofColsR Y) := by
  funext p
  simp only [gramH, upperOf, ofColsR, Matrix.mul_apply, transpose_apply, of_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramMat_eq {k m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (Y : Fin k → Fin m → ℝ) :
    gramMat H Y = (ofColsR Y)ᵀ * H * ofColsR Y := by
  ext c d
  simp only [gramMat, ofColsR, Matrix.mul_apply, transpose_apply, of_apply, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem lastColsX_append (X1 : Fin (r + t) → Fin (r + t + r) → ℝ) (X2 : Fin r → Fin (r + t + r) → ℝ) :
    lastColsX (Fin.append X1 X2) = ofColsR X2 := by
  ext i j; simp [lastColsX, ofColsR]

theorem posDef_of_mem_boxD {k : ℕ} {ε : ℝ} (hε : ε * k < 1) {S : Matrix (Fin k) (Fin k) ℝ} (hS : Sᵀ = S)
    (h : upperOf S ∈ boxD k ε) : S.PosDef := by
  refine posDef_of_near_one hS hε fun i j => ?_
  have hb := mem_boxD.mp h
  rcases le_total i j with hij | hij
  · have := hb ⟨(i, j), hij⟩
    have hw := wt_ge_one (⟨(i, j), hij⟩ : UIdx k)
    simp only [upperOf, idU] at this
    have hε0 : 0 ≤ ε := by
      have := (abs_nonneg _).trans this
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (by linarith)
    rw [one_apply]
    convert this.trans (div_le_self hε0 hw) using 2
  · have := hb ⟨(j, i), hij⟩
    have hw := wt_ge_one (⟨(j, i), hij⟩ : UIdx k)
    simp only [upperOf, idU] at this
    have hε0 : 0 ≤ ε := by
      have := (abs_nonneg _).trans this
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) fun h => absurd h.2 (by linarith)
    have hsym : S j i = S i j := by rw [← transpose_apply S i j, hS]
    rw [hsym] at this
    rw [one_apply]
    have hif : (if j = i then (1 : ℝ) else 0) = if i = j then 1 else 0 := if_congr eq_comm rfl rfl
    rw [hif] at this
    exact this.trans (div_le_self hε0 hw)

/-! ### The region and its volume -/

/-- **The Leray region over $B$**: $\{X : \det X > 0,\; \|\Phi(X) - c_\varphi\|_\infty\le\varepsilon,\; \mathrm{zOf}(X_2)\in B\}$. -/
def regionR (r t : ℕ) (ε : ℝ) (B : Set (Fin (r + t) → Fin r → ℝ)) : Set (Fin (r + t + r) → Fin (r + t + r) → ℝ) :=
  {X | 0 < (Matrix.of X).det ∧ pullCoeff (phiQ r t) X ∈ Metric.closedBall (coeffU (phiQ r t)) ε ∧
    zOf (lastColsX X) ∈ B}

/-- The integrand over the frames: $G(u) = [{}^tu\varphi u\in-\mathrm{boxD}_r,\; \mathrm{zOf}\,u\in B]\cdot
\tfrac12|\det({}^tu\varphi u)|^{-q/2}J_\varepsilon({}^tu\varphi u)$. -/
def frameIntegrand (r t : ℕ) (ε : ℝ) (B : Set (Fin (r + t) → Fin r → ℝ)) (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    ℝ≥0∞ :=
  {u : Matrix (Fin (r + t + r)) (Fin r) ℝ | upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B}.indicator
    (fun u => ENNReal.ofReal (|(uᵀ * phiR r t * u).det| ^ (-((r + t : ℕ) : ℝ) / 2) / 2) *
      Jint (r + t) r ε (uᵀ * phiR r t * u)) u

theorem measurable_Jint (q r : ℕ) (ε : ℝ) : Measurable (Jint q r ε) := by
  have hg : Measurable fun p : Matrix (Fin r) (Fin r) ℝ × (Fin q → Fin r → ℝ) => gramH p.1⁻¹ p.2 := by
    have hc : Continuous fun p : Matrix (Fin r) (Fin r) ℝ × (Fin q → Fin r → ℝ) => gramH p.1 p.2 := by
      refine continuous_pi fun p => ?_
      simp only [gramH, dotProduct, mulVec]; fun_prop
    exact hc.measurable.comp (measurable_inv_matrix.prodMap measurable_id)
  have hm : Measurable fun p : Matrix (Fin r) (Fin r) ℝ × (Fin q → Fin r → ℝ) =>
      (box12 q r ε).indicator (fun A => shiftInt q ε (gramH p.1⁻¹ A)) p.2 := by
    have : (fun p : Matrix (Fin r) (Fin r) ℝ × (Fin q → Fin r → ℝ) =>
        (box12 q r ε).indicator (fun A => shiftInt q ε (gramH p.1⁻¹ A)) p.2) =
        fun p => (box12 q r ε).indicator (fun _ => (1 : ℝ≥0∞)) p.2 * shiftInt q ε (gramH p.1⁻¹ p.2) := by
      funext p; by_cases h : p.2 ∈ box12 q r ε <;> simp [h]
    rw [this]
    exact ((measurable_const.indicator (measurableSet_box12 q r ε)).comp measurable_snd).mul
      ((measurable_shiftInt q ε).comp hg)
  exact hm.lintegral_prod_right'

theorem measurable_frameIntegrand (ε : ℝ) {B : Set (Fin (r + t) → Fin r → ℝ)} (hB : MeasurableSet B) :
    Measurable (frameIntegrand r t ε B) := by
  have hT : Continuous fun u : Matrix (Fin (r + t + r)) (Fin r) ℝ => uᵀ * phiR r t * u := by fun_prop
  refine Measurable.indicator ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp ((((continuous_abs.comp (hT.matrix_det)).measurable).pow_const _).div_const
      _)).mul ((measurable_Jint _ _ ε).comp hT.measurable)
  · exact ((measurableSet_boxD r ε).preimage (continuous_upperOf.comp hT.neg).measurable).inter
      (measurable_zOf hB)

theorem transpose_phiR_mul_symm (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) :
    (uᵀ * phiR r t * u)ᵀ = uᵀ * phiR r t * u := by
  rw [transpose_mul, transpose_mul, transpose_transpose, phiR, diagonal_transpose, Matrix.mul_assoc]

theorem frameIntegrand_eq_zero {ε : ℝ} (hε : ε * r < 1) {B : Set (Fin (r + t) → Fin r → ℝ)}
    (u : Matrix (Fin (r + t + r)) (Fin r) ℝ) (hu : (wBlk u + cBlk u).det = 0) : frameIntegrand r t ε B u = 0 := by
  unfold frameIntegrand
  refine Set.indicator_of_notMem (fun h => ?_) _
  have hpd := posDef_of_mem_boxD hε (by rw [transpose_neg, transpose_phiR_mul_symm]) h.1
  exact det_wc_ne_zero hpd hu

/-- **The region in frame coordinates**: the Lebesgue measure of the region is $\int G(X_2)\,dX_2$. -/
theorem volume_regionR_eq_frames (ht : 1 ≤ r + t) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε * r < 1)
    {B : Set (Fin (r + t) → Fin r → ℝ)} (hB : MeasurableSet B) :
    volume (regionR r t ε B) = ∫⁻ X2 : Fin r → Fin (r + t + r) → ℝ, frameIntegrand r t ε B (ofColsR X2) := by
  have hmR : MeasurableSet (regionR r t ε B) := by
    have hdc : Continuous fun X : Fin (r + t + r) → Fin (r + t + r) → ℝ => (Matrix.of X).det := by
      have : (fun X : Fin (r + t + r) → Fin (r + t + r) → ℝ => (Matrix.of X).det) = fun X => (ofCols X).det :=
        funext fun X => (det_ofCols X).symm
      rw [this]; exact continuous_ofCols.matrix_det
    have hl : Continuous (lastColsX : (Fin (r + t + r) → Fin (r + t + r) → ℝ) → _) := by
      unfold lastColsX; fun_prop
    exact (measurableSet_lt measurable_const hdc.measurable).inter
      ((Metric.isClosed_closedBall.measurableSet.preimage (continuous_pullCoeff _).measurable).inter
        (measurable_zOf.comp hl.measurable hB))
  rw [← lintegral_indicator_one hmR, lintegral_finAppend (measurable_one.indicator hmR)]
  refine lintegral_congr fun X2 => ?_
  set u := ofColsR X2
  have hsplit : ∀ X1 : Fin (r + t) → Fin (r + t + r) → ℝ,
      (regionR r t ε B).indicator 1 (Fin.append X1 X2) =
        {u : Matrix (Fin (r + t + r)) (Fin r) ℝ | upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B}.indicator
          (1 : Matrix (Fin (r + t + r)) (Fin r) ℝ → ℝ≥0∞) u *
        {X1 : Fin (r + t) → Fin (r + t + r) → ℝ | 0 < (Matrix.of (Fin.append X1 X2)).det ∧
          gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
          (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε}.indicator
            (1 : (Fin (r + t) → Fin (r + t + r) → ℝ) → ℝ≥0∞) X1 := by
    intro X1
    have h22 : gramH (-phiQR (r + t) r) X2 = upperOf (-(uᵀ * phiR r t * u)) := by
      rw [gramH_eq_upperOf, Matrix.mul_neg, Matrix.neg_mul]; rfl
    have hreg : Fin.append X1 X2 ∈ regionR r t ε B ↔
        (upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B) ∧
        (0 < (Matrix.of (Fin.append X1 X2)).det ∧ gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
          (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε) := by
      simp only [regionR, Set.mem_setOf_eq, mem_closedBall_iff_boxes hε0, lastColsX_append, h22]
      tauto
    by_cases hA : upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B
    · by_cases hB' : 0 < (Matrix.of (Fin.append X1 X2)).det ∧ gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
          (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε
      · rw [Set.indicator_of_mem (hreg.mpr ⟨hA, hB'⟩), Set.indicator_of_mem (show u ∈ {u : Matrix (Fin (r + t + r))
          (Fin r) ℝ | upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B} from hA),
          Set.indicator_of_mem (show X1 ∈ {X1 : Fin (r + t) → Fin (r + t + r) → ℝ |
            0 < (Matrix.of (Fin.append X1 X2)).det ∧ gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
            (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε} from hB')]
        simp
      · rw [Set.indicator_of_notMem (fun h => hB' (hreg.mp h).2),
          Set.indicator_of_notMem (show X1 ∉ {X1 : Fin (r + t) → Fin (r + t + r) → ℝ |
            0 < (Matrix.of (Fin.append X1 X2)).det ∧ gramH (phiQR (r + t) r) X1 ∈ boxD (r + t) ε ∧
            (fun a c => X1 a ⬝ᵥ (phiQR (r + t) r *ᵥ X2 c)) ∈ box12 (r + t) r ε} from hB'), mul_zero]
    · rw [Set.indicator_of_notMem (fun h => hA (hreg.mp h).1),
        Set.indicator_of_notMem (show u ∉ {u : Matrix (Fin (r + t + r)) (Fin r) ℝ |
          upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B} from hA), zero_mul]
  simp_rw [hsplit]
  rw [lintegral_const_mul' _ _ (by unfold Set.indicator; split_ifs <;> simp)]
  unfold frameIntegrand
  by_cases hin : u ∈ {u : Matrix (Fin (r + t + r)) (Fin r) ℝ | upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B}
  · rw [Set.indicator_of_mem hin, Set.indicator_of_mem hin, Pi.one_apply, one_mul]
    have hT : (-(gramMat (phiQR (r + t) r) X2)).PosDef := by
      rw [gramMat_eq]
      exact posDef_of_mem_boxD hε (by rw [transpose_neg]; exact congrArg Neg.neg (transpose_phiR_mul_symm u)) hin.1
    rw [lintegral_inner hT ht ε, gramMat_eq]
    rfl
  · rw [Set.indicator_of_notMem hin, Set.indicator_of_notMem hin, zero_mul]

theorem det_transpose_mul_mul (m H : Matrix (Fin r) (Fin r) ℝ) : (mᵀ * H * m).det = m.det ^ 2 * H.det := by
  rw [det_mul, det_mul, det_transpose]; ring

theorem xi_conj_symm (z : Fin (r + t) → Fin r → ℝ) (m : Matrix (Fin r) (Fin r) ℝ) :
    (mᵀ * xiR z * m)ᵀ = mᵀ * xiR z * m := by
  rw [transpose_mul, transpose_mul, transpose_transpose, xiR_transpose, Matrix.mul_assoc]

theorem real_frame_const {d δ s : ℝ} (hd : d ≠ 0) (hδ : 0 < δ) (q : ℕ) (hs : |s| = d ^ 2 * δ) :
    |d| ^ q * (|s| ^ (-(q : ℝ) / 2) / 2) = δ ^ (-(q : ℝ) / 2) / 2 := by
  have hd' : 0 < |d| := abs_pos.mpr hd
  rw [hs, Real.mul_rpow (sq_nonneg _) hδ.le, ← sq_abs, ← Real.rpow_natCast |d| 2, ← Real.rpow_mul hd'.le,
    ← Real.rpow_natCast |d| q, mul_div_assoc', ← mul_assoc, ← Real.rpow_add hd']
  have : ((q : ℕ) : ℝ) + ((2 : ℕ) : ℝ) * (-(q : ℝ) / 2) = 0 := by push_cast; ring
  rw [this, Real.rpow_zero, one_mul]

/-- **The integral over $m$ for fixed $z$**: $\int|\det m|^q\,G(P(z)m)\,dm = [z\in B\cap Z_{\mathbb R}]\,
\delta(z)^{-n/2}\cdot\tfrac12 I_\varepsilon$. -/
theorem lintegral_frame_z {ε : ℝ} (hε : ε * r < 1) {B : Set (Fin (r + t) → Fin r → ℝ)}
    (z : Fin (r + t) → Fin r → ℝ) :
    ∫⁻ Y : Fin r → Fin r → ℝ, ENNReal.ofReal (|(Matrix.of fun i j => Y j i).det| ^ (r + t)) *
        frameIntegrand r t ε B (frameOf z (Matrix.of fun i j => Y j i)) =
      (B ∩ ZR r t).indicator (fun z => ENNReal.ofReal (deltaR z ^ (-((r + t + r : ℕ) : ℝ) / 2)) *
        (ENNReal.ofReal (1 / 2) * Iint (r + t) r ε)) z := by
  have hbox : ∀ Y : Fin r → Fin r → ℝ, upperOf (-((frameOf z (ofColsR Y))ᵀ * phiR r t * frameOf z (ofColsR Y))) =
      gramH (xiR z) Y := by
    intro Y; rw [transpose_frameOf_mul, neg_neg, gramH_eq_upperOf]
  have hpd : ∀ Y : Fin r → Fin r → ℝ, gramH (xiR z) Y ∈ boxD r ε →
      ((ofColsR Y)ᵀ * xiR z * ofColsR Y).PosDef := fun Y hY =>
    posDef_of_mem_boxD hε (xi_conj_symm z _) (by rw [← gramH_eq_upperOf]; exact hY)
  have hdetm : ∀ Y : Fin r → Fin r → ℝ, gramH (xiR z) Y ∈ boxD r ε → (ofColsR Y).det ≠ 0 := by
    intro Y hY h0
    have := (hpd Y hY).det_pos
    rw [det_transpose_mul_mul, h0] at this; simp at this
  have hmem : ∀ Y : Fin r → Fin r → ℝ,
      frameOf z (ofColsR Y) ∈ {u : Matrix (Fin (r + t + r)) (Fin r) ℝ |
        upperOf (-(uᵀ * phiR r t * u)) ∈ boxD r ε ∧ zOf u ∈ B} ↔
      gramH (xiR z) Y ∈ boxD r ε ∧ zOf (frameOf z (ofColsR Y)) ∈ B := by
    intro Y; rw [Set.mem_setOf_eq, hbox]
  by_cases hz : z ∈ ZR r t
  · have hξ : (xiR z).PosDef := hz
    have hδ : 0 < deltaR z := hξ.det_pos
    set c : ℝ≥0∞ := ENNReal.ofReal (deltaR z ^ (-((r + t : ℕ) : ℝ) / 2) / 2)
    have hpt : ∀ Y : Fin r → Fin r → ℝ, ENNReal.ofReal (|(Matrix.of fun i j => Y j i).det| ^ (r + t)) *
        frameIntegrand r t ε B (frameOf z (Matrix.of fun i j => Y j i)) =
        B.indicator (fun _ => (1 : ℝ≥0∞)) z *
          (boxD r ε).indicator (fun s => c * Jint (r + t) r ε (-(symU s))) (gramH (xiR z) Y) := by
      intro Y
      change ENNReal.ofReal (|(ofColsR Y).det| ^ (r + t)) * frameIntegrand r t ε B (frameOf z (ofColsR Y)) = _
      unfold frameIntegrand
      by_cases hY : gramH (xiR z) Y ∈ boxD r ε
      · have hm := hdetm Y hY
        have hzz : zOf (frameOf z (ofColsR Y)) = z := zOf_frameOf z (isUnit_iff_ne_zero.mpr hm)
        rw [Set.indicator_of_mem hY]
        by_cases hzB : z ∈ B
        · rw [Set.indicator_of_mem ((hmem Y).mpr ⟨hY, by rw [hzz]; exact hzB⟩), Set.indicator_of_mem hzB, one_mul,
            transpose_frameOf_mul, gramH_eq_upperOf, symU_upperOf (xi_conj_symm z _), ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          refine real_frame_const hm hδ (r + t) ?_
          rw [det_neg, det_transpose_mul_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
            abs_mul, abs_pow, sq_abs, abs_of_pos (show 0 < (xiR z).det from hδ)]
          rfl
        · rw [Set.indicator_of_notMem (fun h => hzB (hzz ▸ ((hmem Y).mp h).2)), Set.indicator_of_notMem hzB,
            zero_mul, mul_zero]
      · rw [Set.indicator_of_notMem (fun h => hY ((hmem Y).mp h).1), Set.indicator_of_notMem hY, mul_zero,
          mul_zero]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ (by unfold Set.indicator; split_ifs <;> simp)]
    have hf : Measurable fun s : UIdx r → ℝ => (boxD r ε).indicator (fun s => c * Jint (r + t) r ε (-(symU s))) s :=
      (measurable_const.mul ((measurable_Jint _ _ ε).comp (continuous_symU.neg.measurable))).indicator
        (measurableSet_boxD r ε)
    rw [lintegral_gramH hξ hf]
    have hI : ∫⁻ s, densR r s * (boxD r ε).indicator (fun s => c * Jint (r + t) r ε (-(symU s))) s =
        c * Iint (r + t) r ε := by
      rw [Iint, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1; funext s
      by_cases hs : s ∈ boxD r ε
      · simp only [Set.indicator_of_mem hs]; ring
      · simp only [Set.indicator_of_notMem hs, mul_zero]
    rw [hI]
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB, Set.indicator_of_mem (show z ∈ B ∩ ZR r t from ⟨hzB, hz⟩), one_mul,
        ← mul_assoc, ← mul_assoc]
      congr 1
      have hδ' : 0 < (xiR z).det := hδ
      have e : (xiR z).det ^ (-(r : ℝ) / 2) * ((xiR z).det ^ (-((r + t : ℕ) : ℝ) / 2) / 2) =
          (xiR z).det ^ (-((r + t + r : ℕ) : ℝ) / 2) * (1 / 2) := by
        rw [mul_div_assoc', ← Real.rpow_add hδ']
        have : -(r : ℝ) / 2 + -(((r + t : ℕ)) : ℝ) / 2 = -(((r + t + r : ℕ)) : ℝ) / 2 := by push_cast; ring
        rw [this]; ring
      simp only [c, deltaR]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ'.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ'.le _), e]
    · rw [Set.indicator_of_notMem hzB, Set.indicator_of_notMem (fun h => hzB h.1), zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hz h.2)]
    have h0 : ∀ Y : Fin r → Fin r → ℝ, ENNReal.ofReal (|(Matrix.of fun i j => Y j i).det| ^ (r + t)) *
        frameIntegrand r t ε B (frameOf z (Matrix.of fun i j => Y j i)) = 0 := by
      intro Y
      change ENNReal.ofReal (|(ofColsR Y).det| ^ (r + t)) * frameIntegrand r t ε B (frameOf z (ofColsR Y)) = 0
      unfold frameIntegrand
      refine mul_eq_zero_of_right _ (Set.indicator_of_notMem (fun h => hz ?_) _)
      have h' := (hmem Y).mp h
      have hm := hdetm Y h'.1
      have hu := zOf_mem_ZR (u := frameOf z (ofColsR Y)) (by rw [transpose_frameOf_mul, neg_neg]; exact hpd Y h'.1)
      rwa [zOf_frameOf z (isUnit_iff_ne_zero.mpr hm)] at hu
    simp_rw [h0, lintegral_zero]

theorem measurable_deltaR_rpow (a : ℝ) :
    Measurable fun z : Fin (r + t) → Fin r → ℝ => ENNReal.ofReal (deltaR z ^ a) :=
  ENNReal.measurable_ofReal.comp ((continuous_xiR.matrix_det.measurable).pow_const a)

theorem muZR_apply {B : Set (Fin (r + t) → Fin r → ℝ)} (hB : MeasurableSet B) :
    muZR r t B = ∫⁻ z in B ∩ ZR r t, ENNReal.ofReal (deltaR z ^ (-((r + t + r : ℕ) : ℝ) / 2)) := by
  rw [muZR, withDensity_apply _ hB, Measure.restrict_restrict hB]

/-- **The volume of the region**, computed in the coordinates $(z, m, A, B)$:
$\mathrm{Leb}(\text{region}) = 2^{-r^2}2^{-tr/2}\cdot\tfrac12\,\mu_Z(B)\,I_\varepsilon$. -/
theorem volume_regionR (ht : 1 ≤ r + t) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε * r < 1)
    {B : Set (Fin (r + t) → Fin r → ℝ)} (hB : MeasurableSet B) :
    volume (regionR r t ε B) = ENNReal.ofReal ((2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2)) *
      (ENNReal.ofReal (1 / 2) * muZR r t B * Iint (r + t) r ε) := by
  rw [volume_regionR_eq_frames ht hε0 hε hB]
  rw [show (∫⁻ X2 : Fin r → Fin (r + t + r) → ℝ, frameIntegrand r t ε B (ofColsR X2)) =
      ∫⁻ X2 : Fin r → Fin (r + t + r) → ℝ, frameIntegrand r t ε B (Matrix.of fun i j => X2 j i) from rfl,
    lintegral_frames (measurable_frameIntegrand ε hB) (frameIntegrand_eq_zero hε)]
  congr 1
  simp_rw [lintegral_frame_z hε]
  rw [lintegral_indicator (hB.inter measurableSet_ZR), lintegral_mul_const _ (measurable_deltaR_rpow _),
    ← muZR_apply hB]
  ring

/-- $c_k = 2\tau_{\mathbb R}(SO_k(\mathbb R))$. -/
theorem cprod_eq_two_mul_tauR (k : ℕ) : cprod k = 2 * tauR k := by
  rw [cprod_eq, tauR, Finset.prod_div_distrib, prod_range_pi_rpow, div_eq_mul_inv, Finset.prod_inv_distrib]
  ring

/-- The constant: $2^{-r^2}2^{-tr/2}\cdot\tfrac12\,c_qc_r = \mathrm{vol}_C(C_{\mathbb R})$. -/
theorem const_eq_volCReal :
    (2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2) * (1 / 2) * (cprod (r + t) * cprod r) =
      volCReal (r + t) r := by
  rw [cprod_eq_two_mul_tauR, cprod_eq_two_mul_tauR, volCReal, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have : -((r : ℝ) ^ 2) + -((t : ℝ) * r) / 2 = -((r : ℝ) * (((r + t : ℕ) : ℝ) + r)) / 2 := by push_cast; ring
  rw [this]; ring

/-! ### Box volumes -/

/-- The splitting of the upper index pairs of `Fin (q + r)`. -/
def uidxSplit (q r : ℕ) : UIdx q ⊕ (Fin q × Fin r) ⊕ UIdx r → UIdx (q + r) :=
  Sum.elim e11 (Sum.elim (fun ac => e12 ac.1 ac.2) e22)

theorem uidxSplit_bijective (q r : ℕ) : Function.Bijective (uidxSplit q r) := by
  constructor
  · have hv : ∀ {x y : UIdx (q + r)}, x.1.1.val = y.1.1.val → x.1.2.val = y.1.2.val → x = y :=
      fun h1 h2 => Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
    have hv' : ∀ {k : ℕ} {x y : UIdx k}, x.1.1.val = y.1.1.val → x.1.2.val = y.1.2.val → x = y :=
      fun h1 h2 => Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2))
    rintro (p | ⟨a, c⟩ | p) (p' | ⟨a', c'⟩ | p') h
    all_goals
      have h1 := congrArg (fun x : UIdx (q + r) => x.1.1.val) h
      have h2 := congrArg (fun x : UIdx (q + r) => x.1.2.val) h
      simp only [uidxSplit, Sum.elim_inl, Sum.elim_inr, e11, e12, e22, Fin.val_castAdd, Fin.val_natAdd] at h1 h2
    · exact congrArg Sum.inl (Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)))
    · exfalso; have := p.1.2.isLt; omega
    · exfalso; have := p.1.1.isLt; omega
    · exfalso; have := a.isLt; omega
    · have ha : a = a' := Fin.ext h1
      have hc : c = c' := Fin.ext (by omega)
      rw [ha, hc]
    · exfalso; have := a.isLt; omega
    · exfalso; have := p'.1.1.isLt; omega
    · exfalso; have := a'.isLt; omega
    · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))))
  · intro p
    have := (forall_UIdx_add (q := q) (r := r) (P := fun p => ∃ x, uidxSplit q r x = p)).mpr
      ⟨fun p => ⟨Sum.inl p, rfl⟩, fun a c => ⟨Sum.inr (Sum.inl (a, c)), rfl⟩, fun p => ⟨Sum.inr (Sum.inr p), rfl⟩⟩
    exact this p

theorem volume_box_wt_eq_Vbox (q r : ℕ) (t0 : UIdx (q + r) → ℝ) (ε : ℝ) :
    volume (box t0 wt ε) = Vbox q r ε := by
  rw [volume_box, Vbox, volume_boxD, volume_boxD, volume_box12,
    ← (Equiv.ofBijective _ (uidxSplit_bijective q r)).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Equiv.ofBijective_apply, uidxSplit, Sum.elim_inl, Sum.elim_inr, wt_e11, wt_e12, wt_e22,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [show 2 * (ε / 2) = ε by ring]
  ring

theorem toReal_volume_ball_eq (ε : ℝ) (hε : 0 < ε) :
    (volume (Metric.closedBall (coeffU (phiQ r t)) ε)).toReal =
      (Vbox (r + t) r ε).toReal * (2 : ℝ) ^ ((r + t + r) * (r + t + r - 1) / 2) := by
  rw [toReal_volume_closedBall _ hε, volume_box_wt_eq_Vbox]

/-! ### The main theorem -/

/-- **The fibre volume at a real indefinite place** (Hanke thesis, §4.2, pp. 12–13), in the repository's
normalization: for every measurable $B$, $\mu(F_{\mathbb R}^{-1}B) = 2^{-n(n-1)/2}\,\mathrm{vol}_C(C_{\mathbb R})\,\mu_Z(B)$,
$\mu$ = `lerayMeasure (phiQ r t)` (coefficient coordinates). -/
theorem map_FRG_lerayMeasure (ht : 1 ≤ r + t) :
    (lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero).map FRG =
      ENNReal.ofReal (volCReal (r + t) r / (2 : ℝ) ^ ((r + t + r) * (r + t + r - 1) / 2)) • muZR r t := by
  set N2 : ℝ := (2 : ℝ) ^ ((r + t + r) * (r + t + r - 1) / 2)
  have hN2 : 0 < N2 := by positivity
  set K : ℝ := (2 : ℝ) ^ (-((r : ℝ) ^ 2)) * (2 : ℝ) ^ (-((t : ℝ) * r) / 2)
  have hK : 0 < K := by positivity
  ext B hB
  rw [Measure.map_apply measurable_FRG hB, Measure.smul_apply, smul_eq_mul]
  set L := lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero (FRG ⁻¹' B)
  set μ := muZR r t B
  set κ : ℝ → ℝ≥0∞ := fun ε => ∫⁻ c in Metric.closedBall (coeffU (phiQ r t)) ε,
    ENNReal.ofReal (rho (diagRev r t) c)
  set I : ℝ → ℝ≥0∞ := fun ε => Iint (r + t) r ε
  -- the identity for small ε
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), L * κ ε = ENNReal.ofReal K * (ENNReal.ofReal (1 / 2) * μ * I ε) := by
    have h1 := eventually_closedBall_subset (diagRev r t)
    have h2 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε * (r : ℝ) < 1 := by
      have : Tendsto (fun ε : ℝ => ε * (r : ℝ)) (𝓝[>] 0) (𝓝 0) := by
        have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (r : ℝ)
        simpa using this.mono_left nhdsWithin_le_nhds
      exact this.eventually (eventually_lt_nhds one_pos)
    filter_upwards [h1, h2, self_mem_nhdsWithin] with ε hsub hεr hε
    have hreg := volume_region_FR Metric.isClosed_closedBall.measurableSet hsub hB
    rw [← volume_regionR ht (le_of_lt hε) hεr hB]
    exact hreg.symm
  have hκ := tendsto_avg_rho (diagRev r t)
  have hI := tendsto_Iint (r + t) r
  -- positivity and finiteness of κ ε and I ε, eventually
  have hκpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (κ ε).toReal := by
    have := hκ.eventually (eventually_gt_nhds one_pos)
    filter_upwards [this, self_mem_nhdsWithin] with ε hε hε0
    by_contra hneg; push Not at hneg
    have h0 : (κ ε).toReal = 0 := le_antisymm hneg ENNReal.toReal_nonneg
    simp only [κ] at hε h0; rw [h0, zero_div] at hε; exact absurd hε (by norm_num)
  have hIpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (I ε).toReal := by
    have hc : 0 < cprod (r + t) * cprod r := mul_pos (cprod_pos _) (cprod_pos _)
    have := hI.eventually (eventually_gt_nhds hc)
    filter_upwards [this] with ε hε
    by_contra hneg; push Not at hneg
    have h0 : (I ε).toReal = 0 := le_antisymm hneg ENNReal.toReal_nonneg
    simp only [I] at h0; rw [h0, zero_div] at hε; linarith
  have hconst : volCReal (r + t) r / N2 = K * (1 / 2) * (cprod (r + t) * cprod r) / N2 := by
    rw [← const_eq_volCReal]
  by_cases hμ : μ = ⊤
  · obtain ⟨ε, hε1, hε2, hε3⟩ := (hev.and (hκpos.and hIpos)).exists
    have hκt : κ ε ≠ ⊤ := fun h => by rw [h] at hε2; simp at hε2
    have hIne : I ε ≠ 0 := fun h => by rw [h] at hε3; simp at hε3
    have hRHS : ENNReal.ofReal K * (ENNReal.ofReal (1 / 2) * μ * I ε) = ⊤ := by
      rw [hμ, ENNReal.mul_top (by simp), ENNReal.top_mul hIne, ENNReal.mul_top (by simp [hK])]
    rw [hRHS] at hε1
    have hL : L = ⊤ := by
      by_contra hL
      exact ENNReal.mul_ne_top hL hκt hε1
    rw [hL, hμ, ENNReal.mul_top]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    rw [hconst]
    exact div_pos (mul_pos (mul_pos hK (by norm_num)) (mul_pos (cprod_pos _) (cprod_pos _))) hN2
  · -- finite case: compare the real limits
    have hLfin : L ≠ ⊤ := by
      obtain ⟨ε, hε1, hε2, hε3⟩ := (hev.and (hκpos.and hIpos)).exists
      have hIt : I ε ≠ ⊤ := fun h => by rw [h] at hε3; simp at hε3
      have hκ0 : κ ε ≠ 0 := fun h => by rw [h] at hε2; simp at hε2
      intro hL
      rw [hL, ENNReal.top_mul hκ0] at hε1
      exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top hμ) hIt)) hε1.symm
    -- real form of the identity, divided by the ball volume
    have hlim1 : Tendsto (fun ε => L.toReal * ((κ ε).toReal /
        (volume (Metric.closedBall (coeffU (phiQ r t)) ε)).toReal)) (𝓝[>] 0) (𝓝 (L.toReal * 1)) :=
      hκ.const_mul _
    have hlim2 : Tendsto (fun ε => K * (1 / 2) * μ.toReal * ((I ε).toReal / (Vbox (r + t) r ε).toReal) / N2)
        (𝓝[>] 0) (𝓝 (K * (1 / 2) * μ.toReal * (cprod (r + t) * cprod r) / N2)) :=
      (hI.const_mul _).div_const _
    have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), L.toReal * ((κ ε).toReal /
        (volume (Metric.closedBall (coeffU (phiQ r t)) ε)).toReal) =
        K * (1 / 2) * μ.toReal * ((I ε).toReal / (Vbox (r + t) r ε).toReal) / N2 := by
      filter_upwards [hev, self_mem_nhdsWithin] with ε h hε
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal (by norm_num)] at h'
      rw [toReal_volume_ball_eq ε hε]
      have hV : 0 < (Vbox (r + t) r ε).toReal := ENNReal.toReal_pos (Vbox_pos _ _ hε).ne' (Vbox_ne_top _ _ ε)
      field_simp
      rw [h']; ring
    have := tendsto_nhds_unique (hlim1.congr' heq) hlim2
    rw [mul_one] at this
    rw [← ENNReal.ofReal_toReal hLfin, this, ← ENNReal.ofReal_toReal hμ, ← ENNReal.ofReal_mul (by
      rw [hconst]
      exact (div_pos (mul_pos (mul_pos hK (by norm_num)) (mul_pos (cprod_pos _) (cprod_pos _))) hN2).le), hconst]
    congr 1
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; ring

/-- **Hanke's Haar measure on $SO(q, r)$**: $\widetilde\omega_G = 2^{n(n-1)/2}\cdot$`lerayMeasure` (Gram coordinates;
the same factor as in `muArchHanke` at a real place, and as in `tauR_eq_two_pow_mul_archVolSO` in the definite
case). -/
@[kb "hanke2005crelle" "§2, (2.4)–(2.7), p. 4–5; Calculation 4.1, pp. 9–10 (ω̃_G at a real place)"]
def hankeHaarR (r t : ℕ) : Measure (ArchSO (phiQ r t)) :=
  ENNReal.ofReal ((2 : ℝ) ^ ((r + t + r) * (r + t + r - 1) / 2)) • lerayMeasure (phiQ r t) gramDetR_phiQ_ne_zero

/-- **$\mathrm{vol}_C(C_{\mathbb R})$ is the fibre volume** (Hanke thesis, §4.2, pp. 12–13): at a real place with
$\varphi_v = \mathrm{diag}[1_q, -1_r]$, $q = r + t\ge1$,
$$(F_{\mathbb R})_*\widetilde\omega_G = \mathrm{vol}_C(C_{\mathbb R})\cdot\omega_Z,\qquad
\mathrm{vol}_C(C_{\mathbb R}) = 2\cdot2^{-rn/2}\tau_{\mathbb R}(SO_q(\mathbb R))\,\tau_{\mathbb R}(SO_r(\mathbb R)),$$
i.e. $\widetilde\omega_G(F_{\mathbb R}^{-1}B) = \mathrm{vol}_C(C_{\mathbb R})\,\mu_Z(B)$ for every measurable $B$. Unconditional.
For $r = 0$ (definite place) $Z_{\mathbb R}$ is a point and this is $\tau_{\mathbb R}(SO_q(\mathbb R)) = \widetilde\omega_G(G)$. -/
@[kb "hanke2005crelle" "§4.2, pp. 12–13 (ω_C and vol_C(C_R))"]
theorem map_FR_hankeHaar (ht : 1 ≤ r + t) :
    (hankeHaarR r t).map FRG = ENNReal.ofReal (volCReal (r + t) r) • muZR r t := by
  rw [hankeHaarR, Measure.map_smul _ measurable_FRG.aemeasurable, map_FRG_lerayMeasure ht, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity), mul_div_cancel₀ _ (by positivity)]

end QuadFormsKB.Hanke2005.ArchReal

