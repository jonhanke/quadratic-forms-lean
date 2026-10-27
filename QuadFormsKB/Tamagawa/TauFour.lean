/-
# $\tau(SO_4) = 2$ from $\tau(SO_3) = 2$ (Weil 1982, §3.7, Thm. 3.7.1, and the induction step)

Weil proves $\tau(SO_m) = 2$ for $m = 3$ and $m = 4$ separately (§3.7, pp. 61–65; Thm. 3.7.1, p. 65). In the combinatorial setting of this
repository the case $m = 4$ follows from $m = 3$ by the induction step (`tamagawaNumberTwo_succ'`), once Siegel's formula
for numbers is known in rank $4$; over a totally real $F$ of degree $\ge 2$ with $\mathcal O_F$ a PID that is
`HilbertModular.siegelFormulaAt_of_pid_four` (via Hilbert–Eisenstein series of weight $2$).

* `TernaryTamagawaTwo F` (**named input**): $\tau(SO(V)) = 2$, in the sense (`TamagawaNumberTwo`), for every nondegenerate
  totally positive definite ternary $Q_0'$ over $\mathcal O_F$ with $\mathcal O_F^3$ integral.
* `tamagawaNumberTwo_four_of_three`: then $\tau(SO(V)) = 2$ for every split quaternary form $\langle m\rangle\perp Q_0'$
  ($m \gg 0$) with $\mathcal O_F^4$ integral; `massFormula_four_of_three`: the mass formula for its genus.

**Scope.** Split lattices $\mathcal O_Fe_0 \perp L'$ only (the setting). The $\tau$ is now proved invariant under change of
lattice (`LatChange.tauSO_smul_compMat`), and `LatChange.tamagawaNumberTwo_four_all` / `massFormula_four_all` extend these results
to every totally positive definite quaternary genus. $h_F = 1$ and $[F:\mathbb Q] \ge 2$ come from the rank-4
Siegel formula (over $\mathbb Q$ it is `Siegel.siegelFormula_quaternary`, for forms over $\mathbb Z$; its bridge to the
`SiegelFormulaAt` is not formalized).
-/
import QuadFormsKB.Tamagawa.LocalUnimodular
import QuadFormsKB.HilbertModular.SiegelFormulaNF4

open NumberField

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **Input: $\tau(SO_3) = 2$ over $F$** (Weil 1982, §3.7(a), p. 62, Thm. 3.7.1, p. 65, via §§3.1–3.2; equivalently the mass formula for
every ternary genus): for every ternary $Q_0'$ over $\mathcal O_F$ that is nondegenerate, totally positive definite over $F$ and
has $\mathcal O_F^3$ integral, the $\tau(SO(V)) = \mu_{\mathrm{Tam}}(K_{SO})\cdot\mathrm{mass}_{SO}$ equals $2$.

Field:
- `tau_eq_two`: the statement above.

*Hypothesis hygiene.* This is the ternary base case of Weil's induction; it is used here only to derive the **quaternary** case,
so it is not equivalent to the conclusion it is used for. Its proof (Weil's route: $SO_3 \cong D^\times/F^\times$; the zeta
function of $D$, §3.1) is open. It is reduced to the pure quaternion forms $\langle -a,-b,ab\rangle$
(`LatChange.ternaryTamagawaTwo_of_pureForm`) and shown equivalent to Weil's comparison of residues for the standard orders
(`LatChange.ternaryTamagawaTwo_iff_residues`). -/
@[kb "weil1982" "§3.7(a), p. 62; Thm. 3.7.1 (m = 3), p. 65; via §3.1-3.2, pp. 30-44"]
structure TernaryTamagawaTwo (F : Type) [Field F] [NumberField F] : Prop where
  tau_eq_two : ∀ Q₀' : QuadForm (𝓞 F) 3, Q₀'.Nondegenerate → IsTotallyPosDef (Q₀'.map (algebraMap (𝓞 F) F)) →
    IsIntegral (Q₀'.map (algebraMap (𝓞 F) F)) (stdLat F 3).1 → TamagawaNumberTwo Q₀'

variable [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- **$\tau(SO_4) = 2$ from $\tau(SO_3) = 2$** (Weil 1982, Thm. 3.7.1, $m = 4$, by the step instead of Weil's
$(R^{(1)}\times R^{(1)})/\pm1$ and norm-torus computations): for $F$ totally real with $h_F = 1$, $m_0 \in \mathcal O_F$
totally positive and $Q_0'$ ternary over $\mathcal O_F$ with $\langle m_0\rangle\perp Q_0'$ totally positive definite and
$\mathcal O_F^4$ integral, $\tau(SO(\langle m_0\rangle \perp Q_0')) = 2$, given $\tau(SO(Q_0')) = 2$.

*Proof.* Siegel's formula for the number $m_0$ in rank $4$ (the hypothesis `hS`: `siegelFormulaAt_of_pid_four` for
$[F:\mathbb Q] \ge 2$, via `RatBridge.siegelFormulaAt_rat_four` for $F = \mathbb Q$), the mass formula in rank $3$ (the
`massFormula` from `hτ`), and the induction step with the local orbital identity proved at every prime
(`tamagawaNumberTwo_succ'`). -/
@[kb "weil1982" "§3.7, pp. 62-65; Thm. 3.7.1 (m = 4), p. 65; given rank-4 Siegel (any totally real F, ℚ included)"]
theorem tamagawaNumberTwo_four_of_three_of_siegel {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1)
    (hS : SiegelFormulaAt (splitForm m₀ Q₀') m₀)
    (hτ : TamagawaNumberTwo Q₀') : TamagawaNumberTwo (splitForm m₀ Q₀') := by
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    simpa using hm v
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [map_splitForm_alg] at hpd₀ hLi₀
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_map hpd'.nondegenerate
  have hIH : MassFormulaHolds Q₀' := massFormula Q₀' hQ' (by norm_num) hpd' hLi' hτ
  exact tamagawaNumberTwo_succ' m₀ hm0 Q₀' le_rfl hpd hLi hS hIH

/-- `tamagawaNumberTwo_four_of_three_of_siegel` with rank-4 Siegel ($[F:\mathbb Q] \ge 2$). -/
@[kb "weil1982" "§3.7, pp. 62-65; Thm. 3.7.1 (m = 4), p. 65; here via the induction step of §4.5"]
theorem tamagawaNumberTwo_four_of_three (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1)
    (hτ : TamagawaNumberTwo Q₀') : TamagawaNumberTwo (splitForm m₀ Q₀') :=
  tamagawaNumberTwo_four_of_three_of_siegel hm Q₀' hpd hLi
    (HilbertModular.siegelFormulaAt_of_pid_four (n := 4) hpd rfl hd hm) hτ

/-- **$\tau(SO_4) = 2$ for split quaternary forms, given the ternary input** (`TernaryTamagawaTwo F`). -/
@[kb "weil1982" "§3.7, pp. 62-65; Thm. 3.7.1 (m = 4), p. 65"]
theorem tamagawaNumberTwo_four (I : TernaryTamagawaTwo F) (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1) :
    TamagawaNumberTwo (splitForm m₀ Q₀') := by
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [map_splitForm_alg] at hpd₀ hLi₀
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  exact tamagawaNumberTwo_four_of_three hd hm Q₀' hpd hLi
    (I.tau_eq_two Q₀' (nondegenerate_of_map hpd'.nondegenerate) hpd' hLi')

/-- **The mass formula for split quaternary genera, given the ternary input:**
$\mathrm{Mass}(\mathcal O_F^4, \langle m_0\rangle\perp Q_0') = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$ (`massFormula`). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 4), p. 65; mass formula"]
theorem massFormula_four (I : TernaryTamagawaTwo F) (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1) :
    MassFormulaHolds (splitForm m₀ Q₀') :=
  massFormula _ (nondegenerate_of_map hpd.nondegenerate) (by norm_num) hpd hLi
    (tamagawaNumberTwo_four I hd hm Q₀' hpd hLi)

/-! ### The converse: $\tau(SO_3) = 2$ from $\tau(SO_4) = 2$ -/

omit [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] in
/-- **Local Siegel self-densities are positive:** $\alpha_\mathfrak p(L, L) > 0$ for nondegenerate $Q$ (the identity is a
solution of $X^{\mathsf T}AX \equiv A \bmod \mathfrak p^k$ for every $k$, and the normalized counts are eventually constant). -/
theorem siegelDensity_self_pos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {n : ℕ} (Q : QuadForm (𝓞 F) n)
    (hQ : Q.Nondegenerate) : 0 < LocalDensity.NF.siegelDensity v Q Q := by
  obtain ⟨k, hk⟩ := (LocalDensity.NF.localDensityForm_self_eventually_eq v Q hQ).exists
  have hfin : Finite (𝓞 F ⧸ v.asIdeal ^ k) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have hcount : 0 < LocalDensity.NF.repCountForm v Q Q k := by
    unfold LocalDensity.NF.repCountForm
    have : Nonempty {X : Matrix (Fin n) (Fin n) (𝓞 F ⧸ v.asIdeal ^ k) //
        (Q.map (Ideal.Quotient.mk _)).compMat X = Q.map (Ideal.Quotient.mk _)} :=
      ⟨⟨1, QuadForm.compMat_one _⟩⟩
    exact Nat.card_pos
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  have hd : 0 < LocalDensity.NF.localDensityForm v Q Q := by
    rw [← hk]; exact div_pos (by exact_mod_cast hcount) (pow_pos hN _)
  unfold LocalDensity.NF.siegelDensity
  simp only [↓reduceIte]
  linarith

omit [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] in
/-- $\prod_\mathfrak p\alpha_\mathfrak p(L', L') \ne 0$ in rank $3$ (finitely many positive bad factors times $\zeta_F(2)^{-1}$). -/
theorem tprod_siegelDensity_three_ne_zero (Q : QuadForm (𝓞 F) 3) (hQ : Q.Nondegenerate) :
    ∏' v, LocalDensity.NF.siegelDensity v Q Q ≠ 0 := by
  rw [(hasProd_siegelDensity_odd 1 Q hQ).tprod_eq]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ =>
    div_ne_zero (siegelDensity_self_pos v Q hQ).ne' (genericOdd_pos 1 v).ne') ?_
  refine Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero ?_
  have := NFEuler.one_le_dedekindZetaR (F := F) (s := ((2 * (i + 1) : ℕ) : ℝ)) (by
    have : (2 : ℝ) ≤ ((2 * (i + 1) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * (i + 1) by omega)
    linarith)
  linarith

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- **$\tau(SO_3) = 2$ from $\tau(SO_4) = 2$** (the converse of `tamagawaNumberTwo_four_of_three`, same scope): for $F$ totally
real of degree $\ge 2$ with $h_F = 1$, $m_0 \gg 0$ and $\langle m_0\rangle\perp Q_0'$ totally positive definite with $\mathcal O_F^4$
integral, $\tau(SO(\langle m_0\rangle\perp Q_0')) = 2$ implies $\tau(SO(Q_0')) = 2$.

*Proof.* The reduction and Siegel's formula give $\mathrm{Mass}(L)\,S(L, m_0) = \mathrm{Mass}(L')\,W$ with $W > 0$; the
local
orbital identity (proved at every prime; its convergence input $\prod_\mathfrak p\alpha_\mathfrak p(L') \ne 0$ is
`tprod_siegelDensity_three_ne_zero`) and the archimedean identity give $W\mu(K_{SO}(L)) = \mu(K_{SO}(L'))\,S(L, m_0)$; so
$\mathrm{Mass}(L) = \mu(K_{SO}(L))^{-1}$ forces $\mathrm{Mass}(L') = \mu(K_{SO}(L'))^{-1}$.

So, given rank-4 Siegel, **the two base cases of Weil's Theorem 3.7.1 are equivalent** for split lattices: $\tau(SO(Q_0')) = 2
\iff \tau(SO(\langle m_0\rangle\perp Q_0')) = 2$ (`tamagawaNumberTwo_three_iff_four`). Rank-4 Siegel for $m_0$ is the
hypothesis `hS` (for $[F:\mathbb Q] \ge 2$ see `tamagawaNumberTwo_three_of_four`; via
`RatBridge.siegelFormulaAt_rat_four` for $F = \mathbb Q$). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 3 from m = 4), p. 65; given rank-4 Siegel (any totally real F, ℚ included)"]
theorem tamagawaNumberTwo_three_of_four_of_siegel {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1)
    (hS : SiegelFormulaAt (splitForm m₀ Q₀') m₀)
    (hτ : TamagawaNumberTwo (splitForm m₀ Q₀')) : TamagawaNumberTwo Q₀' := by
  have hm0 : m₀ ≠ 0 := by
    rintro rfl
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    simpa using hm v
  have hQ4 : (splitForm m₀ Q₀').Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hQ' : Q₀'.Nondegenerate := nondegenerate_of_posDef_split m₀ Q₀' hpd
  have hloc : LocalOrbitalIdentity Q₀' m₀ :=
    localOrbitalIdentity_of_local' m₀ hm0 Q₀' hpd hLi
      (fun v _ => localOrbitalIdentityAt_local v m₀ hm0 Q₀' hQ')
      (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ4)
      (multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ')
      (tprod_siegelDensity_three_ne_zero Q₀' hQ')
  have hMF : MassFormulaHolds (splitForm m₀ Q₀') := massFormula _ hQ4 (by norm_num) hpd hLi hτ
  unfold MassFormulaHolds at hMF
  set QF' := Q₀'.map (algebraMap (𝓞 F) F)
  set mF := algebraMap (𝓞 F) F m₀
  have hsplit := map_splitForm_alg m₀ Q₀'
  have hpd₀ := hpd
  have hLi₀ := hLi
  rw [hsplit] at hpd₀ hLi₀ hMF
  have hS' := hS.repMass_eq
  rw [hsplit] at hS'
  have hmF : mF ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm0
  have hpd' := isTotallyPosDef_of_splitForm hpd₀
  have hLi' := isIntegral_of_splitForm hLi₀
  have hR := repMass_eq_mass_mul mF QF' (stdLat F (3 + 1)) hpd₀ hLi₀ hmF hpd' hLi'
  have hW := typeSum_pos hpd₀ hLi₀ hmF
  have hloc' := hloc.typeSum_eq
  set W := ∑ᶠ t : MulAction.orbitRel.Quotient (OAf QF') (CompSet mF QF' (stdLat F (3 + 1))),
    typeWeight mF QF' (stdLat F (3 + 1)) t
  set A := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
    LocalDensity.NF.siegelDensity v (splitForm m₀ Q₀') (splitForm m₀ Q₀')
  set A' := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), LocalDensity.NF.siegelDensity v Q₀' Q₀'
  set B := ∏' v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), LocalDensity.NF.localDensity v (splitForm m₀ Q₀') m₀
  set Pr := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO (3 + 1) (detGram (splitForm m₀ Q₀') σ)
  set Pr' := ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 3 (detGram Q₀' σ)
  set ρ := ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (3 + 1) ‖σ mF‖ (detGram (splitForm m₀ Q₀') σ)
  set Nm := normTwoM m₀
  set δ := |(discr F : ℝ)|
  have hδ : 0 < δ := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have harch : Pr * Nm ^ 3 = Pr' * ρ := archProd_splitForm m₀ hm0 Q₀' hQ'
  have hT : tamagawaK (splitForm m₀ Q₀') = δ ^ (-(((3 + 1 : ℕ) : ℝ) * ((3 + 1 : ℕ) - 1) / 4)) * Pr * A := rfl
  have hT' : tamagawaK Q₀' = δ ^ (-((3 : ℝ) * (3 - 1) / 4)) * Pr' * A' := rfl
  have hSP : siegelProduct (splitForm m₀ Q₀') m₀ = δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2) * ρ * B := rfl
  have hδe : δ ^ (-(((3 + 1 : ℕ) : ℝ) * ((3 + 1 : ℕ) - 1) / 4)) =
      δ ^ (-((3 : ℝ) * (3 - 1) / 4)) * δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  -- positivity
  have hmassL := mass_pos hpd₀ (stdLat F (3 + 1)) hLi₀
  have hmassL' := mass_pos hpd' (stdLat F 3) hLi'
  have hTpos : 0 < tamagawaK (splitForm m₀ Q₀') := by rw [hMF] at hmassL; exact inv_pos.mp hmassL
  -- `Mass(L) S = Mass(L') W`
  have e : mass (splitForm mF QF') (stdLat F (3 + 1)) * siegelProduct (splitForm m₀ Q₀') m₀ =
      mass QF' (stdLat F 3) * W := hS'.symm.trans hR
  have hSpos : 0 < siegelProduct (splitForm m₀ Q₀') m₀ := by
    have h1 : 0 < mass (splitForm mF QF') (stdLat F (3 + 1)) * siegelProduct (splitForm m₀ Q₀') m₀ := by
      rw [e]; exact mul_pos hmassL' hW
    exact pos_of_mul_pos_right h1 hmassL.le
  -- `W μ(L) = μ(L') S`
  set D' := δ ^ (-((3 : ℝ) * (3 - 1) / 4))
  set Ds := δ ^ (-(((3 + 1 : ℕ) : ℝ) - 1) / 2)
  have key : W * tamagawaK (splitForm m₀ Q₀') = tamagawaK Q₀' * siegelProduct (splitForm m₀ Q₀') m₀ := by
    rw [hT, hδe, hT', hSP]
    linear_combination (D' * Ds * Pr) * hloc' + (D' * Ds * A' * B) * harch
  have hT'pos : 0 < tamagawaK Q₀' := by
    have h1 : 0 < tamagawaK Q₀' * siegelProduct (splitForm m₀ Q₀') m₀ := by rw [← key]; exact mul_pos hW hTpos
    exact pos_of_mul_pos_left h1 hSpos.le
  refine tamagawaNumberTwo_of_massFormula Q₀' hQ' (by norm_num) hpd' hLi' ?_
  unfold MassFormulaHolds
  rw [hMF] at e
  -- `Mass(L') = S/(μ(L) W) = 1/μ(L')`
  have hW0 := hW.ne'
  have hT0 := hTpos.ne'
  have hT'0 := hT'pos.ne'
  have hS0 := hSpos.ne'
  field_simp
  have e2 : mass QF' (stdLat F 3) * W * tamagawaK (splitForm m₀ Q₀') = siegelProduct (splitForm m₀ Q₀') m₀ := by
    rw [← e]; field_simp
  nlinarith [e2, key]

/-- `tamagawaNumberTwo_three_of_four_of_siegel` with rank-4 Siegel ($[F:\mathbb Q] \ge 2$). -/
@[kb "weil1982" "Thm. 3.7.1 (m = 3 from m = 4), p. 65; induction step of §4.5 read backwards"]
theorem tamagawaNumberTwo_three_of_four (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1)
    (hτ : TamagawaNumberTwo (splitForm m₀ Q₀')) : TamagawaNumberTwo Q₀' :=
  tamagawaNumberTwo_three_of_four_of_siegel hm Q₀' hpd hLi
    (HilbertModular.siegelFormulaAt_of_pid_four (n := 4) hpd rfl hd hm) hτ

/-- **The base cases of Weil's Theorem 3.7.1 are equivalent** for split lattices (given rank-4 Siegel; $h_F = 1$,
$[F:\mathbb Q] \ge 2$): $\tau(SO(Q_0')) = 2 \iff \tau(SO(\langle m_0\rangle\perp Q_0')) = 2$. -/
@[kb "weil1982" "Thm. 3.7.1, p. 65 (m = 3 ⟺ m = 4 for split lattices)"]
theorem tamagawaNumberTwo_three_iff_four (hd : 2 ≤ Fintype.card (InfinitePlace F)) {m₀ : 𝓞 F}
    (hm : ∀ v, 0 < HilbertModular.realEmb F v (algebraMap (𝓞 F) F m₀)) (Q₀' : QuadForm (𝓞 F) 3)
    (hpd : IsTotallyPosDef ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)))
    (hLi : IsIntegral ((splitForm m₀ Q₀').map (algebraMap (𝓞 F) F)) (stdLat F 4).1) :
    TamagawaNumberTwo Q₀' ↔ TamagawaNumberTwo (splitForm m₀ Q₀') :=
  ⟨tamagawaNumberTwo_four_of_three hd hm Q₀' hpd hLi, tamagawaNumberTwo_three_of_four hd hm Q₀' hpd hLi⟩

end QuadFormsKB.Tamagawa
