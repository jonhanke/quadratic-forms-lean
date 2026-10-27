/-
# Siegel's formula for representations of forms by forms: the unconditional statements

**Layer:** $F$ a totally real number field; $Q_0$ a totally positive definite form of rank $N$ and $T_0$ a totally positive definite form
of rank $r \ge 1$ over $\mathcal O_F$ (neither is assumed split); $L = \mathcal O_F^N$. This file assembles the frame theorems of
`FrameSiegelGen`, `FrameSiegelReg`, `FrameSiegelSmall` into statements with **no hypotheses beyond total positive definiteness and the
ranks**: the local identity at every prime is `frameLocalIdentityGen`, the frame comes from a representation of $T_0$ by $Q_0$ over $F$
(`exists_adaptedFrameT`), $\tau(SO(Q')) = 2$ for the complement is `complementTauTwo_totallyReal` (rank $\ge 3$) resp.
`binaryTamagawaTwoReg_nf` (rank $2$), and the mass formula for $Q_0$ is `massFormula_all_ranks_totallyReal` (rank $\ge 4$) resp. the ternary
case. If $Q_0$ does **not** represent $T_0$ over $F$, both sides vanish (local-global principle `exists_local_not_rep`: some local density is $0$).

**Proves**
* `siegelFormsAt_totallyReal_general` ($N \ge r + 3$), `siegelFormsAtReg_totallyReal` ($N = r + 2$, regularized product),
  `siegelFormsAt_totallyReal_codimOne` ($N = r + 1$, $r \ge 2$), `siegelFormsAt_totallyReal_full` ($N = r \ge 3$) and the corollary
  `siegelFormsAt_self_three` ($T = Q$, $N = 3$: the ternary mass formula);
* `siegelFormsAtReg_natural` (complement of rank $2$, natural order): given only `NaturalOrderEulerOne (chiForms Q₀ T₀)`, the partial
  products $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(Q,T)$ converge to the regularized product, and Siegel's formula holds;
* over $\mathbb Q$ (`naturalOrderEulerOne_chiForms_rat`, `siegelFormsAtReg_natural_rat`): `NaturalOrderEulerOne (chiForms Q₀ T₀)` is a theorem,
  since $\chi$ is a Kronecker character $\chi_D$ off a finite set ($D < 0$), so the natural-order statement is unconditional.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelGen
import QuadFormsKB.Tamagawa.FrameSiegelReg
import QuadFormsKB.Tamagawa.FrameSiegelSmall
import QuadFormsKB.Tamagawa.FrameLocalGen
import QuadFormsKB.Tamagawa.FrameHM
import QuadFormsKB.Tamagawa.RatHeadline3

open NumberField Matrix
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain QuadFormsKB.RegProd NFEuler
  QuadFormsKB.HilbertModular Filter

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-! ### The mass formula for $Q_0$ in rank $\ge 3$ -/

/-- **The mass formula for every totally positive definite $Q_0$ of rank $N \ge 3$ over a totally real field** (rank $\ge 4$:
`massFormula_all_ranks_totallyReal`; rank $3$: `massFormula` with `tamagawaNumberTwo_ternary_nf`). -/
theorem massFormulaHolds_of_three_le [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (hN : 3 ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : MassFormulaHolds Q₀ := by
  rcases Nat.lt_or_ge N 4 with h | h
  · obtain rfl : N = 3 := by omega
    exact massFormula Q₀ (nondegenerate_of_map hpd.nondegenerate) (by norm_num) hpd (isIntegral_stdLat_map Q₀)
      (tamagawaNumberTwo_ternary_nf Q₀ hpd)
  · exact Measure.Weil.massFormula_all_ranks_totallyReal h Q₀ hpd

/-! ### The case where $T_0$ is not represented -/

/-- **Siegel's formula when $Q_0$ does not represent $T_0$ over $F$:** both sides are $0$ ($r \le N$). -/
theorem siegelFormsAt_of_not_rep [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hrN : r ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)) : SiegelFormsAt Q₀ T₀ := by
  refine ⟨?_⟩
  rw [repMassT_eq_zero_of_not_rep _ _ _ h]
  unfold siegelProductT
  rw [tprod_siegelDensity_eq_zero_of_not_rep Q₀ T₀ hrN hpd hpdT h]
  simp

/-- The regularized product vanishes when $Q_0$ does not represent $T_0$ over $F$ (a local density is $0$). -/
theorem regProd_siegelDensity_eq_zero_of_not_rep [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hrN : r ≤ N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)) :
    regProd (chiForms Q₀ T₀) 1 (fun v => NF.siegelDensity v Q₀ T₀) = 0 := by
  obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
  have hT0 : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
  have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ hT0 hrN hv
  have hz : (∏' w : HeightOneSpectrum (𝓞 F),
      NF.siegelDensity w Q₀ T₀ * (1 - chiForms Q₀ T₀ w / (normP w : ℝ)) ^ (1 : ℤ)) = 0 :=
    tprod_of_exists_eq_zero ⟨v, by unfold NF.siegelDensity; rw [h0]; simp⟩
  unfold regProd
  rw [hz, mul_zero]

/-- A product with a vanishing factor converges to $0$ in the natural order. -/
theorem hasProd_normOrder_zero_of_eq_zero {f : HeightOneSpectrum (𝓞 F) → ℝ} (v₀ : HeightOneSpectrum (𝓞 F))
    (h : f v₀ = 0) : HasProd f 0 (normOrder F) := by
  rw [hasProd_normOrder_iff]
  unfold IsEulerProductValueNF eulerPartialProdNF
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (normP v₀)] with X hX
  exact (Finset.prod_eq_zero (mem_primesNormLe.mpr hX) h).symm

/-! ### The unconditional theorems -/

/-- **Siegel's formula for representations of forms by forms, $N - r \ge 3$, over every totally real field (unconditional)** for every
totally positive definite $Q_0$ of rank $N$ (not necessarily split) and $T_0$ of rank $r \ge 1$ over $\mathcal O_F$:
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\,|d_F|^{-r(2N-r-1)/4}\prod_\sigma\beta_\sigma(Q_0,T_0)
  \prod_\mathfrak p\beta_\mathfrak p(Q_0,T_0).$$
*Proof:* if $Q_0$ represents $T_0$ over $F$, `exists_adaptedFrameT` gives an adapted frame and `siegelFormsAt_of_frame` applies, with the
local identity `frameLocalIdentityGen`, $\tau = 2$ for the complement (`complementTauTwo_totallyReal`) and the mass formula; otherwise
both sides vanish (`siegelFormsAt_of_not_rep`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r ≥ 3, general Q, unconditional [unverified]"]
theorem siegelFormsAt_totallyReal_general [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hrN : r + 3 ≤ N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAt Q₀ T₀ := by
  obtain ⟨n', rfl⟩ : ∃ n', N = r + n' := ⟨N - r, by omega⟩
  by_cases h : ∃ X : Matrix (Fin (r + n')) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    have hpdQ' := isTotallyPosDef_of_blockForm_right (isTotallyPosDef_blockForm_frame fr hpd)
    exact siegelFormsAt_of_frame Q₀ T₀ hr (by omega) hpd hpdT fr
      (fun v => frameLocalIdentityGen v Q₀ hQ T₀ hT fr)
      ((complementTauTwo_totallyReal (F := F) (by omega : 3 ≤ n')).tau_eq_two fr.Q' hpdQ')
      (massFormulaHolds_of_three_le Q₀ (by omega) hpd)
  · exact siegelFormsAt_of_not_rep Q₀ T₀ (by omega) hpd hpdT h

/-- **Siegel's formula for forms by forms with complement of rank $2$ (regularized product), over every totally real field
(unconditional):** for $Q_0$ totally positive definite of rank $N = r + 2$ and $T_0$ of rank $r \ge 1$,
$$\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(L)\cdot S^{\mathrm{reg}}(Q_0,T_0).$$ -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r = 2, regularized, unconditional [unverified]"]
theorem siegelFormsAtReg_totallyReal [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hN : N = r + 2) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAtReg Q₀ T₀ := by
  subst hN
  by_cases h : ∃ X : Matrix (Fin (r + 2)) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    exact siegelFormsAtReg_of_frame_totallyReal Q₀ T₀ hr hpd hpdT fr
      (fun v => frameLocalIdentityGen v Q₀ hQ T₀ hT fr)
  · refine ⟨?_⟩
    rw [repMassT_eq_zero_of_not_rep _ _ _ h]
    unfold siegelProductTReg
    rw [regProd_siegelDensity_eq_zero_of_not_rep Q₀ T₀ (by omega) hpd hpdT h]
    simp

/-- **Siegel's formula for forms by forms in codimension one ($N = r + 1$, $r \ge 2$), over every totally real field
(unconditional):** with the single global factor $\tfrac12$ (`epsCodimOne`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r = 1, unconditional [unverified]"]
theorem siegelFormsAt_totallyReal_codimOne [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 2 ≤ r) (hN : N = r + 1) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAt Q₀ T₀ := by
  subst hN
  by_cases h : ∃ X : Matrix (Fin (r + 1)) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    exact siegelFormsAt_of_frame_codimOne Q₀ T₀ hr hpd hpdT fr
      (fun v => frameLocalIdentityGen v Q₀ hQ T₀ hT fr)
      (massFormulaHolds_of_three_le Q₀ (by omega) hpd)
  · exact siegelFormsAt_of_not_rep Q₀ T₀ (by omega) hpd hpdT h

/-- **Siegel's formula for a form by a form of the same rank ($N = r \ge 3$), over every totally real field (unconditional).** -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N = r, unconditional [unverified]"]
theorem siegelFormsAt_totallyReal_full [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 3 ≤ r) (hN : N = r) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAt Q₀ T₀ := by
  subst hN
  by_cases h : ∃ X : Matrix (Fin N) (Fin N) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT (r := N) (n' := 0) _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    exact siegelFormsAt_of_frame_full' Q₀ T₀ hr hpd hpdT fr
      (fun v => frameLocalIdentityGen (r := N) (n' := 0) v Q₀ hQ T₀ hT fr)
      (massFormulaHolds_of_three_le Q₀ hr hpd)
  · exact siegelFormsAt_of_not_rep Q₀ T₀ le_rfl hpd hpdT h

/-- **Siegel's formula for $T = Q$ over every totally real field in rank $N = 3$** (the ternary mass formula); together with
`siegelFormsAt_self` ($N \ge 4$) this covers every rank $\ge 3$. -/
@[kb "siegel1935" "Hauptsatz, T = S, N = 3 [unverified]"]
theorem siegelFormsAt_self_three [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAt Q₀ Q₀ :=
  (siegelFormsAt_self_iff Q₀ (by norm_num) hpd).mpr (massFormulaHolds_of_three_le Q₀ le_rfl hpd)

/-! ### The natural-order reading (complement of rank $2$) -/

/-- **Siegel's formula for forms by forms with complement of rank $2$, natural order:** given only `NaturalOrderEulerOne (chiForms Q₀ T₀)`
(the prime ideal theorem for $\chi$), the partial products $\prod_{N\mathfrak p\le X}\beta_\mathfrak p(Q_0,T_0)$ converge to the regularized
product, and Siegel's formula holds with it. If $Q_0$ does not represent $T_0$, a local factor is $0$ and both statements are trivial. -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r = 2, natural order [unverified]"]
theorem siegelFormsAtReg_natural [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)
    (hr : 1 ≤ r) (hN : N = r + 2) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F)))
    (hN' : NaturalOrderEulerOne (chiForms Q₀ T₀)) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => NF.siegelDensity v Q₀ T₀)
      (regProd (chiForms Q₀ T₀) 1 fun v => NF.siegelDensity v Q₀ T₀) (normOrder F) ∧ SiegelFormsAtReg Q₀ T₀ := by
  refine ⟨?_, siegelFormsAtReg_totallyReal Q₀ T₀ hr hN hpd hpdT⟩
  subst hN
  by_cases h : ∃ X : Matrix (Fin (r + 2)) (Fin r) F,
      (Q₀.map (algebraMap (𝓞 F) F)).compMat X = T₀.map (algebraMap (𝓞 F) F)
  · obtain ⟨X, hX⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrameT _ _ hpdT.nondegenerate X hX
    have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
    have hT : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    exact hasProd_normOrder_siegelDensity_forms Q₀ T₀ hr hpd hpdT fr
      (fun v => frameLocalIdentityGen v Q₀ hQ T₀ hT fr) hN'
  · obtain ⟨v, hv⟩ := exists_local_not_rep Q₀ T₀ hpd hpdT h
    have hT0 : T₀.Nondegenerate := nondegenerate_of_map hpdT.nondegenerate
    have h0 := localDensityForm_eq_zero_of_not_rep v Q₀ T₀ hT0 (by omega) hv
    rw [regProd_siegelDensity_eq_zero_of_not_rep Q₀ T₀ (by omega) hpd hpdT h]
    exact hasProd_normOrder_zero_of_eq_zero v (by unfold NF.siegelDensity; rw [h0]; simp)

/-! ### Over $\mathbb Q$: the natural order is unconditional -/

section Rat

open QuadFormsKB.Tamagawa.RatHeadline3 QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat RatBridge

/-- **$\chi$ is a Kronecker character off a finite set over $\mathbb Q$, hence `NaturalOrderEulerOne (chiForms Q₀ T₀)` is a theorem:**
$\delta = -\det H_{Q_0}\det H_{T_0}$ is a negative integer, so $(\delta/\mathfrak p) = \chi_D(p)$ for a fundamental discriminant $D < 0$ and all
$p \nmid 2\delta uw$ (`exists_isQuadDisc_sq`, `charNF_intCast_eq_legendreSym`, `kronZ_odd_prime`), and
`naturalOrderEulerOne_of_almost_kron` applies. -/
theorem naturalOrderEulerOne_chiForms_rat (Q₀ : QuadForm (𝓞 ℚ) N) (T₀ : QuadForm (𝓞 ℚ) r)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 ℚ) ℚ))) :
    NaturalOrderEulerOne (chiForms Q₀ T₀) := by
  obtain ⟨k0, hk0, hk0eq⟩ := exists_int_of_pos (realEmb_det_hessian_pos hpd)
  obtain ⟨k1, hk1, hk1eq⟩ := exists_int_of_pos (realEmb_det_hessian_pos hpdT)
  set k : ℤ := k0 * k1 with hk
  have hk1' : 1 ≤ k := by rw [hk]; nlinarith
  obtain ⟨D, hD, hneg, u, w, hu, hw, hDuw⟩ := exists_isQuadDisc_sq hk1'
  have hδ : deltaForms Q₀ T₀ = ((-k : ℤ) : 𝓞 ℚ) := by
    unfold deltaForms
    rw [← hk0eq, ← hk1eq, hk]
    push_cast
    ring
  have hN : (2 * k * u * w).natAbs ≠ 0 := by
    refine Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by omega)) hu) hw)
  have key : ∀ v ∉ (finite_natGenerator_dvd hN).toFinset, chiForms Q₀ T₀ v = kronChi D v := by
    intro v hv
    set p := Rat.HeightOneSpectrum.natGenerator v with hpdef
    have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
    have : Fact p.Prime := ⟨hpp⟩
    have hndiv : ¬ (p : ℤ) ∣ 2 * k * u * w := fun h =>
      hv ((Set.Finite.mem_toFinset _).mpr (Int.natCast_dvd.mp h))
    have h2 : ¬ (p : ℤ) ∣ 2 := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right h _) _) _)
    have hkd : ¬ (p : ℤ) ∣ k := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left h _) _) _)
    have hud : ¬ (p : ℤ) ∣ u := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
    have hwd : ¬ (p : ℤ) ∣ w := fun h => hndiv (Dvd.dvd.mul_left h _)
    have hp2 : p ≠ 2 := fun h => h2 (by rw [h]; norm_num)
    have hnk : ¬ (p : ℤ) ∣ -k := fun h => hkd (by simpa using h)
    have h2I : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
      have := (intCast_mem_iff v 2).not.mpr h2
      simpa using this
    have hδI : deltaForms Q₀ T₀ ∉ v.asIdeal := by
      rw [hδ]; exact (intCast_mem_iff v (-k)).not.mpr hnk
    rw [chiForms, if_pos ⟨h2I, hδI⟩, hδ, charNF_intCast_eq_legendreSym v hnk]
    have hleg : legendreSym p (-k) = legendreSym p D := by
      have e : D * u ^ 2 = (-k) * w ^ 2 := by linarith
      have hu' : (u : ZMod p) ≠ 0 := fun h => hud ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
      have hw' : (w : ZMod p) ≠ 0 := fun h => hwd ((ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp h)
      have := congrArg (legendreSym p) e
      rwa [legendreSym.mul, legendreSym.mul, legendreSym.sq_one' p hu', legendreSym.sq_one' p hw', mul_one,
        mul_one, eq_comm] at this
    rw [kronChi, kronR, kronZ_odd_prime p hp2, hleg]
  have := hD
  exact (naturalOrderEulerOne_of_almost_kron (D := D) (abs_chiForms_le Q₀ T₀) _ key).1

/-- **Siegel's formula for forms by forms over $\mathbb Q$, complement of rank $2$, natural order (unconditional):** for totally positive
definite $Q_0$ of rank $N = r + 2$ and $T_0$ of rank $r \ge 1$ over $\mathbb Z$, the partial products $\prod_{p\le X}\beta_p(Q,T)$ converge to
the regularized product and $\sum r_M(T_0)/|O(M)| = \mathrm{Mass}\cdot S^{\mathrm{reg}}$. -/
@[kb "siegel1935" "Hauptsatz (forms by forms), N - r = 2, natural order over ℚ, unconditional [unverified]"]
theorem siegelFormsAtReg_natural_rat (Q₀ : QuadForm (𝓞 ℚ) N) (T₀ : QuadForm (𝓞 ℚ) r)
    (hr : 1 ≤ r) (hN : N = r + 2) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 ℚ) ℚ))) :
    HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) => NF.siegelDensity v Q₀ T₀)
      (regProd (chiForms Q₀ T₀) 1 fun v => NF.siegelDensity v Q₀ T₀) (normOrder ℚ) ∧ SiegelFormsAtReg Q₀ T₀ :=
  siegelFormsAtReg_natural Q₀ T₀ hr hN hpd hpdT (naturalOrderEulerOne_chiForms_rat Q₀ T₀ hpd hpdT)

end Rat

end QuadFormsKB.Tamagawa.Frames
