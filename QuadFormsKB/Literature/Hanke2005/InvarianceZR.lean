/-
# Hanke 2005, (4.2.8): $\omega_Z$ is $G_{\mathbb R}$-invariant

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

Hanke (p. 12) uses "the $G_{\mathbb R}$-invariant volume form $\omega_Z = \delta(z)^{-n/2}\bigwedge dz_{ik}$ on $Z_{\mathbb R}$ constructed
in [Shi, §4.2]". The invariance is a consequence of the fibration identity `map_FR_hankeHaar`: $F_*\widetilde\omega_G$ is
invariant because $\widetilde\omega_G$ is left invariant and $F$ is equivariant, and it equals $\mathrm{vol}_C(C_{\mathbb R})\,\omega_Z$
with $0 < \mathrm{vol}_C(C_{\mathbb R}) < \infty$.

**Proves** `map_smul_muZR` (unconditional): $(z\mapsto gz)_*\omega_Z = \omega_Z$ for every $g\in SO(q, r)$.
-/
import QuadFormsKB.Literature.Hanke2005.Eq56

open MeasureTheory Measure
open scoped ENNReal

noncomputable section

namespace QuadFormsKB.Hanke2005.ArchReal

open QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal

variable {r t : ℕ}

/-- **Shimura's measure on $Z_{\mathbb R}$ is invariant** (Hanke thesis, (4.2.8), p. 12; Shimura 1999, §4.2), derived from
the fibration identity: $(z\mapsto gz)_*\omega_Z = \omega_Z$ for $g\in SO(\varphi_v)$, $q = r + t\ge1$. -/
@[kb "hanke2005crelle" "(4.2.8), p. 12 (ω_Z is G_R-invariant)"]
theorem map_smul_muZR (ht : 1 ≤ r + t) (g : ArchSO (phiQ r t)) : (muZR r t).map (g • ·) = muZR r t := by
  have hv : 0 < volCReal (r + t) r := Arch56.volCReal_pos _ _
  have hc0 : ENNReal.ofReal (volCReal (r + t) r) ≠ 0 := by simpa using hv
  have hcT : ENNReal.ofReal (volCReal (r + t) r) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsm : Measurable fun z : Fin (r + t) → Fin r → ℝ => g • z := measurable_const_smul g
  have hmul : Measurable fun h : ArchSO (phiQ r t) => g * h := measurable_const_mul g
  have key : ENNReal.ofReal (volCReal (r + t) r) • (muZR r t).map (g • ·) =
      ENNReal.ofReal (volCReal (r + t) r) • muZR r t := by
    rw [← Measure.map_smul _ hsm.aemeasurable, ← map_FR_hankeHaar ht, Measure.map_map hsm measurable_FRG]
    have : (fun z => g • z) ∘ FRG = FRG ∘ (fun h : ArchSO (phiQ r t) => g * h) := by
      funext h; simp only [Function.comp, FRG_mul]
    rw [this, ← Measure.map_map measurable_FRG hmul, map_mul_left_eq_self]
  ext B hB
  have := congrArg (fun μ : Measure _ => μ B) key
  simp only [Measure.smul_apply, smul_eq_mul] at this
  exact (ENNReal.mul_right_inj hc0 hcT).mp this

end QuadFormsKB.Hanke2005.ArchReal
