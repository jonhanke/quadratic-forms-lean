import QuadFormsKB.Literature.Hanke2005.Eq56
import QuadFormsKB.Literature.Hanke2005.LemmaA1Real
import QuadFormsKB.Citation

open MeasureTheory Measure
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.Arch56

open QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Hanke2005.ArchReal QuadFormsKB.Hanke2005.ArchCx

variable {ιR ιC : Type*} [Fintype ιR] [Fintype ιC] [DecidableEq ιR] [DecidableEq ιC]
  (r t : ιR → ℕ) (n : ℕ)

/-- **The set $Z = \prod_vZ_v\subseteq$ `ZA`** on which Hanke's action is the genuine action: $z_i\in Z_{\mathbb R}$
at the real places and $\mathrm{skew}(z_j)\in Z_{\mathbb C}$ at the complex places. -/
def ZAset (ιC : Type*) : Set (ZA r t n ιC) :=
  {z | (∀ i, z.1 i ∈ ZR (r i) (t i)) ∧ ∀ j, ArchCx.skewOf (z.2 j) ∈ ZC n}

/-- A real component fixes $Z_{\mathbb R}$ pointwise iff it is $\pm1$ (when $r\ge1$; vacuous otherwise). -/
theorem real_fix_of {r t : ℕ} (g : ArchSO (phiQ r t))
    (h : 1 ≤ r → ArchSOInst.mat _ g = 1 ∨ ArchSOInst.mat _ g = -1) :
    ∀ z ∈ ZR r t, g • z = z := by
  intro z hz
  by_cases hr : 1 ≤ r
  · rw [ArchReal.smul_def, actZR_of_mem g hz]
    exact (lemmaA1_real hr (orth_mat g)).mpr (h hr) z hz
  · have : r = 0 := by omega
    subst this
    exact Subsingleton.elim _ _

theorem real_fix_imp {r t : ℕ} (hr : 1 ≤ r) (g : ArchSO (phiQ r t)) (h : ∀ z ∈ ZR r t, g • z = z) :
    ArchSOInst.mat _ g = 1 ∨ ArchSOInst.mat _ g = -1 :=
  (lemmaA1_real hr (orth_mat g)).mp fun z hz => by
    have := h z hz
    rwa [ArchReal.smul_def, actZR_of_mem g hz] at this

theorem cx_fix_of (hn : 3 ≤ n) (g : ArchSOC (sumSqC n))
    (h : ArchSOC.mat _ g = 1 ∨ ArchSOC.mat _ g = -1) :
    ∀ v : LIdx n → ℝ, skewOf v ∈ ZC n → g • v = v := by
  intro v hv
  rw [ArchCx.smul_def, actZC_of_mem g hv, (lemmaA1_complex hn (mat_mem_SOC g)).mpr h (skewOf v) hv,
    lowerOf_skewOf]

theorem cx_fix_imp (hn : 3 ≤ n) (g : ArchSOC (sumSqC n))
    (h : ∀ v : LIdx n → ℝ, skewOf v ∈ ZC n → g • v = v) :
    ArchSOC.mat _ g = 1 ∨ ArchSOC.mat _ g = -1 := by
  refine (lemmaA1_complex hn (mat_mem_SOC g)).mp fun z hz => ?_
  have hv : skewOf (lowerOf z) = z := skewOf_lowerOf hz.1
  have hm : skewOf (lowerOf z) ∈ ZC n := by rw [hv]; exact hz
  have h1 := h (lowerOf z) hm
  rw [ArchCx.smul_def, actZC_of_mem g hm, hv] at h1
  calc actC (ArchSOC.mat _ g) z = skewOf (lowerOf (actC (ArchSOC.mat _ g) z)) :=
        (skewOf_lowerOf (actC_mem (mat_mem_SOC g) hz).2.1).symm
    _ = skewOf (lowerOf z) := by rw [h1]
    _ = z := hv

theorem skewOf_zero {n : ℕ} : skewOf (0 : LIdx n → ℝ) = 0 := by
  ext i j
  simp [skewOf]

theorem skewOf_zero_mem {n : ℕ} : skewOf (0 : LIdx n → ℝ) ∈ ZC n := by
  rw [skewOf_zero]; exact zero_mem_ZC

/-- **Lemma A1 for $G_a$** (Hanke thesis, Lemma A1, p. 21; used for $S$ in the proof of Theorem 5.1, p. 17): for
$n\ge3$, $g = (g_i, g_j)\in G_a = \prod_iSO(\varphi_i)\times\prod_jSO_n(\mathbb C)$ fixes every point of
$Z = \prod_vZ_v$ iff $g_i = \pm1$ at every indefinite real place ($r_i\ge1$) and $g_j = \pm1$ at every complex place.
(At a definite real place $r_i = 0$, $Z_i$ is a point and there is no condition.) So the kernel $S$ of the action is
$\{(\pm1)_v\}$ at the indefinite and complex places. -/
@[kb "hanke2005crelle" "Lemma A1, p. 21; proof of Theorem 5.1, p. 17 (S = {(±1)_v})"]
theorem fixes_ZA_iff (hn : 3 ≤ n) (g : GA r t n ιC) :
    (∀ z ∈ ZAset r t n ιC, g • z = z) ↔
      (∀ i, 1 ≤ r i → ArchSOInst.mat _ (g.1 i) = 1 ∨ ArchSOInst.mat _ (g.1 i) = -1) ∧
      (∀ j, ArchSOC.mat _ (g.2 j) = 1 ∨ ArchSOC.mat _ (g.2 j) = -1) := by
  constructor
  · intro hfix
    refine ⟨fun i hr => real_fix_imp hr (g.1 i) fun z0 hz0 => ?_, fun j => cx_fix_imp n hn (g.2 j) fun v0 hv0 => ?_⟩
    · have hz : (Function.update (fun i' => pR (r i') (t i')) i z0, fun _ : ιC => (0 : LIdx n → ℝ)) ∈
          ZAset r t n ιC := by
        refine ⟨fun i' => ?_, fun j => skewOf_zero_mem⟩
        by_cases h : i' = i
        · subst h; simpa using hz0
        · simpa [Function.update_of_ne h] using pR_mem_ZR
      have := congrArg (fun p => p.1 i) (hfix _ hz)
      simpa [smul_ZA] using this
    · have hz : (fun i' => pR (r i') (t i'), Function.update (fun _ : ιC => (0 : LIdx n → ℝ)) j v0) ∈
          ZAset r t n ιC := by
        refine ⟨fun i' => pR_mem_ZR, fun j' => ?_⟩
        by_cases h : j' = j
        · subst h; simpa using hv0
        · simpa [Function.update_of_ne h] using skewOf_zero_mem
      have := congrArg (fun p => p.2 j) (hfix _ hz)
      simpa [smul_ZA] using this
  · rintro ⟨h1, h2⟩ z hz
    rw [smul_ZA]
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · exact real_fix_of (g.1 i) (h1 i) _ (hz.1 i)
    · exact cx_fix_of n hn (g.2 j) (h2 j) _ (hz.2 j)

end QuadFormsKB.Hanke2005.Arch56
