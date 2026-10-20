/-
# The local ratio at a bad place for $\langle1,-a,-b,ab\rangle$

**Layer:** a number field $F$, a finite place $v$ (dyadic and ramified places included), $a, b\in\mathcal O_F\setminus0$ with
$|2|_v = q^{-s}$, $|a|_v = q^{-e_a}$, $|b|_v = q^{-e_b}$, and $m\ge2(4s+2e_a+2e_b)+1$.

**`local_ratio_sq`** (real numbers):
$$\mu^{(4)}_v(K_m)\,\omega_v(1+\pi^{m+s}\mathfrak o_v)\,\omega_v(\Lambda^{(m)}_v)\,q^{3(e_a+e_b)} =
\mu^{(3)}_v(K_m)^2\,\omega_v(1+\pi^m\Lambda_v)\,\omega_v(\mathfrak o_v^\times),$$
i.e. Weil's local ratio $r_v = |ab|_v^{-3}$ between $\mu_P$ (through $P\cong\mathrm{SL}_1\rtimes PD^\times$) and $\mu^{SO_4}_v$, from
`muLoc_congSub_qSq_eq` ($n = 4$ vs $n = 3$ congruence volumes), `omegaQuatV_lamCong_mul`, `omegaQuatV_oneAddCong` and
`omegaV_oneAdd`.

Source: Weil 1982, §2.3, Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqBox

open MeasureTheory Set NumberField IsDedekindDomain WithZero
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic LocalDensity

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

theorem toReal_q_pow_pos (k : ℕ) : 0 < ((DVR.q 𝔬 : ℝ≥0∞) ^ k).toReal := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_natCast]
  exact pow_pos (by exact_mod_cast DVR.q_pos (R := 𝔬)) k

set_option maxHeartbeats 800000 in
/-- **The local ratio at a bad place** ($r_v = |ab|_v^{-3}$). -/
@[kb "weil1982" "§2.3, Thm 2.3.1 (local ratios) [unverified]"]
theorem local_ratio_sq {s eA eB m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v Av = exp (-(eA : ℤ)))
    (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : 2 * (4 * s + 2 * eA + 2 * eB) + 1 ≤ m) :
    (Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) m (by omega) : Set _)).toReal *
        (omegaV v {r : Fvˣ | Valued.v ((r : Fv) - 1) ≤ exp (-((m + s : ℕ) : ℤ))}).toReal *
        (omegaQuatV v (a : F) (b : F) (lamCong v a b m (by omega))).toReal * (DVR.q 𝔬 : ℝ) ^ (3 * (eA + eB)) =
      (Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) m (by omega) : Set _)).toReal ^ 2 *
        (omegaQuatV v (a : F) (b : F) (oneAddCong v a b m)).toReal * (omegaV v (unitsVSub v)).toReal := by
  have hm1 : 1 ≤ m := by omega
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast DVR.q_pos (R := 𝔬)
  -- the four ingredients, in real numbers
  have h1 := congrArg ENNReal.toReal (omegaQuatV_lamCong_mul v a b ha hb hs hA hB (m := m) (by omega))
  have h2 := congrArg ENNReal.toReal (muLoc_congSub_qSq_eq ha hb hQ hs hA hB hm)
  have h3 := congrArg ENNReal.toReal (omegaQuatV_oneAddCong v a b hm1)
  have h4 := congrArg ENNReal.toReal (omegaV_oneAdd v (k := m + s) (by omega))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h1 h2 h3 h4
  rw [selfDualV_latticeV_nat, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h3 h4
  set L3 := (Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) m (by omega) : Set _)).toReal
  set L4 := (Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) m (by omega) : Set _)).toReal
  set wl := (omegaQuatV v (a : F) (b : F) (lamCong v a b m (by omega))).toReal
  set wu := (omegaV v (unitsVSub v)).toReal
  set ν : ℝ := (Analysis.selfDualV v (Analysis.latticeV v 0)).toReal
  set q : ℝ := (DVR.q 𝔬 : ℝ)
  rw [h3, h4]
  have hL4 : L4 = q ^ (4 * s) * L3 / q ^ (3 * m) := by
    field_simp; linarith [h2]
  have hwl : wl = wu * ν ^ 3 * L3 / q ^ (3 * (s + eA + eB)) := by
    field_simp; linarith [h1]
  rw [hL4, hwl]
  have hq0 : q ≠ 0 := hq.ne'
  field_simp
  rw [show (m + s) = m + s from rfl]
  simp only [← pow_mul, ← pow_add]
  ring_nf

end QuadFormsKB.Tamagawa.Measure.Weil
