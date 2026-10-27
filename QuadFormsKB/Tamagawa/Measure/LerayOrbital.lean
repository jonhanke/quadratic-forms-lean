import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayProps
import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.LocalUnimodular
import QuadFormsKB.Tamagawa.OrbitalEuler
import QuadFormsKB.Siegel.NFMainTerm

/-!
# The local orbital identity in measure form, on $SO(L_v)$

Setting of `LocalOrbital.lean` and `LocalOrbitalBad.lean`: $Q_0 = \langle m\rangle\perp Q_0'$ (`splitForm m Q₀'`) over
$\mathcal O_F$ in $n + 1$ variables, $m \ne 0$, $Q_0'$
nondegenerate, $L_v = \mathcal O_v^{n+1} = \mathcal O_ve_0\perp L'_v$, $G = SO(V_v)$, $H = SO(e_0^\perp) = SO(V'_v)$, $K = SO(L_v)$,
$K_H = SO(L'_v)$ ($= K\cap H$ for the split lattice: an isometry of $L_v$ fixing $e_0$ preserves $L_v\cap e_0^\perp = L_v'$).

Measures: $\mu_G = $ `muLocSO v Q₀ 1` and $\mu_H = $ `muLocSO v Q₀' 1` ($\lambda_v = 1$), and the Leray measure
$\sigma_m = $ `lerayMeasure` of $Q_0$ at $\rho = m$ for the standard Haar measure `haarV` ($\mathrm{vol}\,\mathcal O_v = 1$) on $F_v$,
which is the measure $dx/dQ_0$ on the sphere $T(m)_v = \{Q_0 = m\}$.

**`localOrbitalIdentity_measure`** (the orbital identity in measure form, for the test function $\Phi_v = \mathbf 1_{L_v}$):
$$W_v\cdot\mu_G(K)\cdot|2m|_v^{\,n} = \mu_H(K_H)\cdot\sigma_m(T(m)_v\cap L_v),$$
$W_v = \sum_t w_v(t)$ the sum of the local weights over the $K$-orbit types of $T(m)_v\cap L_v$ (the `locTypeSum`; $W_v = 1$ if
$v \nmid 2m$). It is the counting identity with $\alpha_v(L,L) = \mu_G(K)$ (`muLocSO_soStabSO`),
$\alpha_v(L',L') = \mu_H(K_H)$ and $\beta_v(L, m) = \sigma_m(T(m)_v\cap L_v)$ (this file's `lerayMeasure_latL`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology
open scoped ENNReal NNReal
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.LerayFinite

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

/-- **The local orbital identity in measure form** (Weil 1982, §3.4 [unverified]; every finite place, dyadic included):
$W_v\,\mu_G(SO(L_v))\,|2m|_v^n = \mu_H(SO(L'_v))\,\sigma_m(L_v)$. -/
@[kb "weil1982" "§3.4 (local orbital identity, measure form) [unverified]"]
theorem localOrbitalIdentity_measure (m₀ : 𝓞 F) (hm : m₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) n) (hQ' : Q₀'.Nondegenerate) :
    locTypeSum v (algebraMap (𝓞 F) F m₀) (Q₀'.map (algebraMap (𝓞 F) F)) *
        (muLocSO v (splitForm m₀ Q₀') 1 (soStabSO v (splitForm m₀ Q₀') : Set (SOv v (splitForm m₀ Q₀')))).toReal *
        absTwoM v m₀ ^ n =
      (muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀'))).toReal *
        (lerayMeasure v (haarV v) (NF.Qp v (splitForm m₀ Q₀')) (NF.nondegenerate_Qp v (by
            rw [QuadForm.Nondegenerate, det_hessian_splitForm]
            exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'))
          ((NF.ι v m₀ : v.adicCompletionIntegers F) : v.adicCompletion F) (LocalZeta.latL v (n + 1))).toReal := by
  have hQ : (splitForm m₀ Q₀').Nondegenerate := by
    rw [QuadForm.Nondegenerate, det_hessian_splitForm]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hm) hQ'
  have hW := (localOrbitalIdentityAt_local v m₀ hm Q₀' hQ').typeSum_eq
  have hα : 0 < NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀') := siegelDensity_pos v _ hQ
  have hα' : 0 < NF.siegelDensity v Q₀' Q₀' := siegelDensity_pos v _ hQ'
  have hβ : 0 ≤ NF.localDensity v (splitForm m₀ Q₀') m₀ := QuadFormsKB.Siegel.localDensityNF_nonneg v _ hQ hm
  have h1 : (muLocSO v (splitForm m₀ Q₀') 1 (soStabSO v (splitForm m₀ Q₀') : Set (SOv v (splitForm m₀ Q₀')))).toReal =
      NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀') := by
    rw [muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal hα.le]
  have h2 : (muLocSO v Q₀' 1 (soStabSO v Q₀' : Set (SOv v Q₀'))).toReal = NF.siegelDensity v Q₀' Q₀' := by
    rw [muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal hα'.le]
  have h3 := lerayMeasure_latL v (haarV v) (NF.Qp v (splitForm m₀ Q₀'))
    (NF.nondegenerate_Qp v hQ) (n := n + 1) (by omega) (NF.ι v m₀) (NF.ι_ne_zero v hm)
  rw [h1, h2]
  have hden : DVR.localDensity (NF.Qp v (splitForm m₀ Q₀')) (NF.π v) (NF.ι v m₀) =
      NF.localDensity v (splitForm m₀ Q₀') m₀ := (NF.localDensity_eq_completion v _ _).symm
  rw [hden, haarV_real_O, one_pow, mul_one] at h3
  rw [h3, ENNReal.toReal_ofReal hβ]
  exact hW

section Invariance

open Matrix QuadFormsKB.Lattices

local notation "Fv" => v.adicCompletion F

theorem evalIn_QF (Q₀ : QuadForm (𝓞 F) n) (x : Fin n → Fv) :
    (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv x = Q₀.evalIn Fv x := by
  simp only [QuadForm.evalIn, QuadForm.map]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [Matrix.map_apply, ← IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
  · rfl

/-- Elements of $O(V)(F_v)$ preserve the quadratic function $x \mapsto Q(x)$ on $F_v^n$. -/
theorem evalIn_orthGroup (Q₀ : QuadForm (𝓞 F) n) (g : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)
    (x : Fin n → Fv) :
    Q₀.evalIn Fv ((g : GL (Fin n) Fv).val *ᵥ x) = Q₀.evalIn Fv x := by
  rw [← evalIn_QF v Q₀, ← evalIn_QF v Q₀]
  have hg := g.2
  rw [mem_orthGroup] at hg
  have h1 := two_mul_evalIn (Q := Q₀.map (algebraMap (𝓞 F) F)) (R := Fv) ((g : GL (Fin n) Fv).val *ᵥ x)
  have h2 := two_mul_evalIn (Q := Q₀.map (algebraMap (𝓞 F) F)) (R := Fv) x
  have h3 : ((g : GL (Fin n) Fv).val *ᵥ x) ⬝ᵥ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F Fv) *ᵥ
      ((g : GL (Fin n) Fv).val *ᵥ x)) =
      x ⬝ᵥ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F Fv) *ᵥ x) := by
    set M := (g : GL (Fin n) Fv).val with hM
    set H := (Q₀.map (algebraMap (𝓞 F) F)).hessian.map (algebraMap F Fv) with hH
    have key : (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x)) = x ⬝ᵥ (Mᵀ *ᵥ (H *ᵥ (M *ᵥ x))) := by
      rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    rw [key, mulVec_mulVec, mulVec_mulVec, hg]
  have h4 : (2 : Fv) * (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv ((g : GL (Fin n) Fv).val *ᵥ x) =
      2 * (Q₀.map (algebraMap (𝓞 F) F)).evalIn Fv x := by rw [h1, h2, h3]
  exact mul_left_cancel₀ two_ne_zero h4

/-- **$SO(V)(F_v)$-invariance of the Leray measure** (the first half of the orbital identity: $\sigma_\rho$ is the invariant
measure on the sphere $T(\rho)_v$ and on the cone $C^\circ_v$): for $g \in SO(V)(F_v)$ (the `SOv`), $g_*\sigma_\rho = \sigma_\rho$. -/
theorem lerayMeasure_map_soSub (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (ρ : Fv) (g : SOv v Q₀) :
    Measure.map (fun x : Fin n → Fv => ((g.1 : GL (Fin n) Fv) : Matrix (Fin n) (Fin n) Fv) *ᵥ x)
        (lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) ρ) =
      lerayMeasure v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) ρ := by
  refine lerayMeasure_map_mulVec v (haarV v) (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) ρ (g.1 : GL (Fin n) Fv) ?_ ?_
  · intro x
    simp only [Qv, NF.evalIn_Qp]
    exact evalIn_orthGroup v Q₀ g.1 x
  · have : GeneralLinearGroup.det (g.1 : GL (Fin n) Fv) = 1 := Units.ext g.2
    rw [this, map_one]

end Invariance

end QuadFormsKB.Tamagawa.Measure.LerayFinite
