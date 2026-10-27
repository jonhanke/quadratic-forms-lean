import QuadFormsKB.Tamagawa.SiegelRank3
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Binary.RelDensities
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowskiNF
import QuadFormsKB.Literature.HasseNorm.GoodPrimes
import QuadFormsKB.HilbertModular.ThetaPosDef

/-!
# Siegel's formula in rank 3: the frame identity

**Layer:** forms over $\mathcal O_F$, $F$ totally real; a totally positive definite ternary form $Q_0$ ($L = \mathcal O_F^3$,
Hessian $H$, $d_Q = \det(H/2)$), a totally positive $m \in \mathcal O_F$, and an adapted frame
$Q_0\circ g = \langle m\rangle\perp Q_0'$ (`AdaptedFrame`) with **binary** complement $Q_0'$.

This is the rank-3 analogue of `two_mul_tamagawaK_mul_repMass_frame` (which needs $N \ge 4$: in rank 3 the plain products
$\prod\beta_\mathfrak p$ and $\prod\alpha_\mathfrak p(Q_0')$ do not converge unconditionally).

**1. The character $\chi_m$ is quadratic.** With $\delta_m = -2\det H\cdot m$ (`deltaTern`; $\chi_m(\mathfrak p) =
(\delta_m/\mathfrak p)$, `chiTern`), $\delta_m$ is totally negative, hence not a square, and $E_m = F(\sqrt{\delta_m})$ is a
quadratic extension (`exists_sqrtExt_deltaTern`). At every $\mathfrak p \nmid 2\delta_m$, $\chi_m(\mathfrak p) = \chi_{E_m/F}(\mathfrak p)$
(`relChar_eq_charNF`), so `chiTern Q₀ m` is `IsAlmostRelChar` and **$L_F(1,\chi_m)$ exists and is positive**
(`lOne_chiTern_pos`, via `exists_hasLOne_of_almost_relChar`). No hypothesis.

**2. $\chi' = \chi_m$.** The binary character $\chi'(\mathfrak p)$ = `chiP` of $Q_0'$ is $(-\det H'/\mathfrak p)$ at good
$\mathfrak p$ (`chiP_binary_eq_charNF`). The frame gives $\det(g)^2\det H = 2m\det H'$, so $-\det H' = \theta'^2$ with
$\theta' = \sqrt{\delta_m}\,\det g/(2m) \in E_m$: $\chi'$ is also almost $\chi_{E_m/F}$, and **$\chi' = \chi_m$ outside a finite
set** (`chiP_frame_eq_chiTern`).

**3. Good-prime values.** $\alpha_\mathfrak p(Q_0') = 1 - \chi'(\mathfrak p)/N\mathfrak p$ at $\mathfrak p \nmid 2\det H'$
(`siegelDensity_binary_good`), so $\alpha_\mathfrak p(Q_0')(1-\chi'(\mathfrak p)/N\mathfrak p)^{-1}$ has finite support
(`multipliable_siegelDensity_binary_reg`, `regProd_siegelDensity_binary`). For $\beta_\mathfrak p$: `localDensity_mul_one_sub_chiTern`.

**4. The regularized rank-2 Tamagawa measure.** `tamagawaKReg Q'` $= |d_F|^{-1/2}\prod_\sigma\mathrm{vol}(SO(V'_\sigma))\cdot
L_F(1,\chi')^{-1}\prod_\mathfrak p\alpha_\mathfrak p(Q')(1-\chi'(\mathfrak p)/N\mathfrak p)^{-1}$ (convergence factors
$\lambda_\mathfrak p = L_\mathfrak p(1,\chi')$), and `tauSOReg Q'` $=$ `tamagawaKReg Q'` $\cdot\,\mathrm{mass}_{SO}$, exactly as `tauSO` with the regularized measure (`tauSOReg_eq`: $= $ `tamagawaKReg Q'` $\cdot\,2\,\mathrm{Mass}(Q')$).
`regProd_congr_finite`: the regularized product does not see a change of $\chi$ at finitely many primes.

**5. The rank-3 frame identity** (`two_mul_tamagawaK_mul_repMass_frame3`), unconditional:
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(Q_0))\cdot\mathrm{repMass}(\mathcal O_F^3, m) = \tau^{\mathrm{reg}}(SO(Q_0'))\cdot S_3(L, m),$$
$S_3$ = `siegelProduct3` (regularized). No hypothesis: the local orbital identities are the theorem
`orbitalLocalIdentities`. With $\tau(SO(Q_0)) = 2$ (`TamagawaNumberTwo`, from `TernaryTamagawaTwo`) and
$\tau^{\mathrm{reg}}(SO(Q_0')) = 2$ it is `SiegelFormulaAt3 Q₀ m` (`siegelFormulaAt3_of_frame`); for every $m$ with the
named input `BinaryTamagawaTwoReg F` (`siegelFormulaAt3_of_tau`, using
`siegelProduct3_eq_zero_of_not_rep` when $Q_0$ does not represent $m$ over $F$).

-/

open NumberField IsDedekindDomain Matrix Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### 1. $\chi_m$ is the character of $E_m = F(\sqrt{-2\det H\cdot m})$ -/

section CharTern

/-- **$\delta_m = -2\det H\cdot m$**, the element whose residue symbol is $\chi_m$ at the good primes (it is $16\cdot(-m\,d_Q)$,
the same square class as $-m\,d_Q$). Written exactly as in `Siegel.psiNF` for $n = 3$. -/
def deltaTern (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) : 𝓞 F :=
  (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m

theorem deltaTern_ne_zero {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) :
    deltaTern Q₀ m ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (mul_ne_zero two_ne_zero hQ)) hm

/-- At $\mathfrak p \nmid 2\delta_m$: $\chi_m(\mathfrak p) = (\delta_m/\mathfrak p)$. -/
theorem chiTern_eq_charNF_of_not_mem (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))
    (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hδ : deltaTern Q₀ m ∉ v.asIdeal) :
    chiTern Q₀ m v = (Siegel.charNF v (deltaTern Q₀ m) : ℝ) := by
  have hd : Q₀.hessian.det ∉ v.asIdeal := fun h => hδ (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _
    (v.asIdeal.mul_mem_left _ h)))
  unfold chiTern Siegel.psiNF
  rw [if_pos ⟨h2, hd⟩]
  rfl

variable [IsTotallyReal F]

/-- $\sigma(\det H) > 0$ at every real place, for $Q_0$ totally positive definite. -/
theorem realEmb_det_hessian_pos {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} (hpd : IsTotallyPosDef (formF Q₀))
    (w : InfinitePlace F) : 0 < realEmb F w (algebraMap (𝓞 F) F Q₀.hessian.det) := by
  have h := (isTotPosGram_of_isTotallyPosDef hpd w).det_pos
  rw [show ((gramF Q₀).map (realEmb F w)).det = realEmb F w (gramF Q₀).det from
    (RingHom.map_det _ _).symm, gramF_eq, det_smul, map_mul, hessF,
    show (Q₀.hessian.map (algebraMap (𝓞 F) F)).det = algebraMap (𝓞 F) F Q₀.hessian.det from
      (RingHom.map_det _ _).symm] at h
  have h2 : 0 < realEmb F w ((1 / 2 : F) ^ Fintype.card (Fin n)) := by
    rw [map_pow, map_div₀, map_one, map_ofNat]; positivity
  exact pos_of_mul_pos_right h h2.le

/-- **$\delta_m$ is not a square in $F$** ($\delta_m$ is totally negative for $Q_0$ totally positive definite and $m$ totally
positive). So $\chi_m$ is never trivial. -/
theorem not_isSquare_deltaTern {Q₀ : QuadForm (𝓞 F) 3} (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ¬ IsSquare (algebraMap (𝓞 F) F (deltaTern Q₀ m)) := by
  rintro ⟨r, hr⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := congrArg (realEmb F w) hr
  have hd := realEmb_det_hessian_pos hpd w
  have hmw := hm w
  simp only [deltaTern, map_mul, map_pow, map_neg, map_one, map_ofNat] at h
  have : realEmb F w r * realEmb F w r ≥ 0 := mul_self_nonneg _
  norm_num at h
  nlinarith

/-- **$E_m = F(\sqrt{\delta_m})$:** a quadratic extension with $s^2 = \delta_m$ and $\sigma s = -s$ for its nontrivial
automorphism $\sigma$ (`Binary.Rel.conj`). -/
theorem exists_sqrtExt_deltaTern {Q₀ : QuadForm (𝓞 F) 3} (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (_ : Algebra.IsQuadraticExtension F E) (s : E),
      s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (deltaTern Q₀ m)) ∧ Binary.Rel.conj F E s = -s := by
  have hd := not_isSquare_deltaTern hpd hm
  obtain ⟨E, _, _, _, s, hs, hspan⟩ := Lam.exists_quadExt _ hd
  obtain ⟨hQ, -⟩ := HN.quadData _ hd s hs hspan
  refine ⟨E, inferInstance, inferInstance, inferInstance, hQ, s, hs, ?_⟩
  have hsq : (Binary.Rel.conj F E s - s) * (Binary.Rel.conj F E s + s) = 0 := by
    have : (Binary.Rel.conj F E s) ^ 2 = s ^ 2 := by
      rw [← map_pow, hs, AlgEquiv.commutes]
    linear_combination this
  rcases mul_eq_zero.mp hsq with h | h
  · exfalso
    apply Binary.Rel.conj_ne_one F E
    ext y
    obtain ⟨b₀, b₁, rfl⟩ := hspan y
    rw [sub_eq_zero] at h
    simp [h]
  · linear_combination h

end CharTern

section AlmostRel

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- **A residue-symbol character is almost $\chi_{E/F}$:** if $\theta \in E$, $\theta^2 = \delta \in \mathcal O_F \setminus 0$,
$\sigma\theta = -\theta$, and $\chi(\mathfrak p) = (\delta/\mathfrak p)$ at every $\mathfrak p \nmid 2\delta$ outside a finite set $S$, then
$\chi = \chi_{E/F}$ outside a finite set (`relChar_eq_charNF`). -/
theorem isAlmostRelChar_of_sqrt {δ : 𝓞 F} (hδ : δ ≠ 0) {θ : E}
    (hθ2 : θ ^ 2 = algebraMap F E (algebraMap (𝓞 F) F δ)) (hθc : Binary.Rel.conj F E θ = -θ)
    {χ : HeightOneSpectrum (𝓞 F) → ℝ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v, v ∉ S → (2 : 𝓞 F) ∉ v.asIdeal → δ ∉ v.asIdeal → χ v = (Siegel.charNF v δ : ℝ)) :
    IsAlmostRelChar χ E := by
  classical
  have hint : IsIntegral ℤ θ := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hθ2]
    exact (RingOfIntegers.isIntegral_coe δ).algebraMap
  set θO : 𝓞 E := ⟨θ, hint⟩
  have hθO : Binary.Rel.conjO F E θO = -θO := by
    apply RingOfIntegers.coe_injective
    rw [Binary.Rel.algebraMap_conjO]
    exact hθc
  have hδO : algebraMap (𝓞 F) (𝓞 E) δ = θO ^ 2 := by
    apply RingOfIntegers.coe_injective
    show algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) δ) = algebraMap (𝓞 E) E (θO ^ 2)
    rw [map_pow, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact hθ2.symm
  have h2δ : (2 * δ : 𝓞 F) ≠ 0 := mul_ne_zero two_ne_zero hδ
  refine ⟨S ∪ (Siegel.finite_mem_asIdeal h2δ).toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or] at hv
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun h => hv.2 (v.asIdeal.mul_mem_right _ h)
  have hδv : δ ∉ v.asIdeal := fun h => hv.2 (v.asIdeal.mul_mem_left _ h)
  rw [hχ v hv.1 h2 hδv, Binary.Rel.relChar_eq_charNF hθO hδO h2 hδv]

/-- **$\chi_m$ is $\chi_{E_m/F}$ off a finite set** (any $E$, $s$ with $s^2 = \delta_m$, $\sigma s = -s$). -/
theorem isAlmostRelChar_chiTern {Q₀ : QuadForm (𝓞 F) 3} (hQ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) {s : E}
    (hs : s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (deltaTern Q₀ m))) (hsc : Binary.Rel.conj F E s = -s) :
    IsAlmostRelChar (chiTern Q₀ m) E :=
  isAlmostRelChar_of_sqrt (deltaTern_ne_zero hQ hm) hs hsc ∅ fun v _ h2 hδ =>
    chiTern_eq_charNF_of_not_mem Q₀ m v h2 hδ

end AlmostRel

section LOne

variable [IsTotallyReal F]

theorem ne_zero_of_totallyPos {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    m ≠ 0 := by
  rintro rfl
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have := hm w
  rw [map_zero, map_zero] at this
  exact lt_irrefl 0 this

/-- **$L_F(1,\chi_m)$ exists and is positive** for $Q_0$ totally positive definite and $m$ totally positive (no hypothesis:
$\chi_m$ is the character of the CM extension $E_m/F$ off a finite set; `exists_hasLOne_of_almost_relChar`). -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 (L(1, χ_{E/F}) = ρ_E/ρ_F ≠ 0) [unverified]"]
theorem lOne_chiTern_pos {Q₀ : QuadForm (𝓞 F) 3} (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    0 < LOne (chiTern Q₀ m) ∧ HasLOne (chiTern Q₀ m) (LOne (chiTern Q₀ m)) := by
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_deltaTern hpd hm
  have hQ : Q₀.Nondegenerate := by
    have := hpd.nondegenerate
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  exact exists_hasLOne_of_almost_relChar (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    (fun v => abs_chiTern_le v Q₀ m) (isAlmostRelChar_chiTern hQ (ne_zero_of_totallyPos hm) hs hsc)

end LOne


/-! ### 2. $\chi' = \chi_m$ off a finite set -/

section Binary

variable (v : HeightOneSpectrum (𝓞 F))

local notation "𝔽" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)
local notation "res" => IsLocalRing.residue (v.adicCompletionIntegers F)

/-- **The binary character at a good prime:** for $\mathfrak p \nmid 2\det H'$, `chiP v Q'` $= (-\det H'/\mathfrak p)$ (the
discriminant $(-1)\det(H'/2) = -\det H'/4$, and $4$ is a square). -/
theorem chiP_binary_eq_charNF (Q' : QuadForm (𝓞 F) 2) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hd : Q'.hessian.det ∉ v.asIdeal) :
    chiP v Q' = (Siegel.charNF v (-Q'.hessian.det) : ℝ) := by
  have h2' := res_two_ne_zero v h2
  unfold chiP
  rw [if_neg (not_or.2 ⟨h2, hd⟩)]
  congr 1
  rw [DVR.chiDisc, DVR.resGramDet, NF.det_hessian_Qp, Siegel.charNF]
  have e : (-1 : 𝔽) ^ (2 / 2) * (res (NF.ι v Q'.hessian.det) / 2 ^ 2) =
      res (NF.ι v (-Q'.hessian.det)) * ((2 : 𝔽) ^ 2)⁻¹ := by
    simp only [map_neg, Nat.div_self two_pos, pow_one]
    field_simp
  rw [e, quadraticChar_mul_inv_sq h2']

end Binary

section FrameChar

/-- **The determinant relation of a ternary frame over $F$:** $\det H_0\,(\det g)^2 = 2\rho\,\det H'$. -/
theorem det_frame3 (Q₀ : QuadForm (𝓞 F) 3) {ρ : F} (fr : AdaptedFrame (formF Q₀) ρ) :
    algebraMap (𝓞 F) F Q₀.hessian.det * fr.g.val.det ^ 2 =
      2 * ρ * algebraMap (𝓞 F) F fr.Q'.hessian.det := by
  have h1 := congrArg (fun S : QuadForm F (2 + 1) => S.hessian.det) fr.compMat_eq
  simp only [hessian_compMat, det_mul, det_transpose, det_hessian_splitForm, hessian_map,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  linear_combination h1

variable {E : Type} [Field E] [NumberField E] [Algebra F E] [Algebra.IsQuadraticExtension F E]

/-- **$\chi'$ is $\chi_{E_m/F}$ off a finite set:** $-\det H' = \theta'^2$ with $\theta' = s\det g/(2m)$, $s^2 = \delta_m$
(`det_frame3`), and $\sigma\theta' = -\theta'$. -/
theorem isAlmostRelChar_chiP_frame {Q₀ : QuadForm (𝓞 F) 3} (hQF : (formF Q₀).Nondegenerate) {m : 𝓞 F}
    (hm : m ≠ 0) (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) {s : E}
    (hs : s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F (deltaTern Q₀ m))) (hsc : Binary.Rel.conj F E s = -s) :
    IsAlmostRelChar (fun v => chiP v fr.Q') E := by
  have hmF : algebraMap (𝓞 F) F m ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hm
  have hQ' : fr.Q'.Nondegenerate := fr.nondegenerate hQF hmF
  have hδ' : (-fr.Q'.hessian.det : 𝓞 F) ≠ 0 := neg_ne_zero.2 hQ'
  set c : F := fr.g.val.det / (2 * algebraMap (𝓞 F) F m)
  refine isAlmostRelChar_of_sqrt hδ' (θ := s * algebraMap F E c) ?_ ?_ ∅ fun v _ h2 hδ => ?_
  · have hrel := det_frame3 Q₀ fr
    rw [mul_pow, hs, ← map_pow, ← map_mul]
    congr 1
    simp only [deltaTern, c, map_mul, map_pow, map_neg, map_one, map_ofNat]
    field_simp
    linear_combination (-1 : F) * hrel
  · rw [map_mul, hsc, AlgEquiv.commutes]; ring
  · exact chiP_binary_eq_charNF v fr.Q' h2 fun h => hδ (v.asIdeal.neg_mem_iff.2 h)

variable [IsTotallyReal F] in
/-- **$\chi' = \chi_m$ outside a finite set**: the character of the binary complement of a
frame adapted to $m$ agrees with the ternary character $\chi_m$ at almost all primes. -/
theorem chiP_frame_eq_chiTern {Q₀ : QuadForm (𝓞 F) 3} (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, chiP v fr.Q' = chiTern Q₀ m v := by
  classical
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_deltaTern hpd hm
  have hQ : Q₀.Nondegenerate := by
    have := hpd.nondegenerate
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hm0 := ne_zero_of_totallyPos hm
  obtain ⟨S₁, hS₁⟩ := isAlmostRelChar_chiP_frame hpd.nondegenerate hm0 fr hs hsc
  obtain ⟨S₂, hS₂⟩ := isAlmostRelChar_chiTern hQ hm0 hs hsc
  refine ⟨S₁ ∪ S₂, fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact (hS₁ v hv.1).trans (hS₂ v hv.2).symm

end FrameChar

/-! ### 3. Good-prime values of the binary densities -/

section BinaryGood

/-- **$\alpha_\mathfrak p(Q') = 1 - \chi'(\mathfrak p)/N\mathfrak p$** at $\mathfrak p \nmid 2\det H'$ (`volSO_good_even`, $m = 1$). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem siegelDensity_binary_good (Q' : QuadForm (𝓞 F) 2) (hQ : Q'.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ badPrimes Q') : NF.siegelDensity v Q' Q' = 1 - chiP v Q' / (normP v : ℝ) := by
  rw [siegelDensity_good_even 1 le_rfl Q' hQ v hv, genericEven, genericOdd]
  simp [Real.rpow_neg_one, div_eq_mul_inv]

/-- **The regularized binary factors have finite support:** if $\chi = \chi'$ off a finite set $S$, then
$\alpha_\mathfrak p(Q')(1-\chi(\mathfrak p)/N\mathfrak p)^{-1} = 1$ outside $S$ and the primes $\mathfrak p \mid 2\det H'$. -/
theorem hasFiniteMulSupport_siegelDensity_binary_reg {Q' : QuadForm (𝓞 F) 2} (hQ : Q'.Nondegenerate)
    {χ : HeightOneSpectrum (𝓞 F) → ℝ} (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, chiP v Q' = χ v) :
    Function.HasFiniteMulSupport fun v =>
      NF.siegelDensity v Q' Q' * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) := by
  refine ((S : Set (HeightOneSpectrum (𝓞 F))).toFinite.union (finite_badPrimes Q' hQ)).subset fun v hv => ?_
  by_contra h
  rw [Set.mem_union, not_or] at h
  apply hv
  show NF.siegelDensity v Q' Q' * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) = 1
  rw [siegelDensity_binary_good Q' hQ v h.2, hS v h.1, _root_.zpow_neg_one,
    mul_inv_cancel₀ (one_sub_div_pos (by rw [← hS v h.1]; exact abs_chiP_le Q' v) v).ne']

theorem multipliable_siegelDensity_binary_reg {Q' : QuadForm (𝓞 F) 2} (hQ : Q'.Nondegenerate)
    {χ : HeightOneSpectrum (𝓞 F) → ℝ} (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, chiP v Q' = χ v) :
    Multipliable fun v => NF.siegelDensity v Q' Q' * (1 - χ v / (normP v : ℝ)) ^ (-1 : ℤ) :=
  multipliable_of_hasFiniteMulSupport (hasFiniteMulSupport_siegelDensity_binary_reg hQ S hS)

end BinaryGood

/-! ### 4. The regularized rank-2 Tamagawa measure -/

section TamagawaReg

/-- **`regProd` does not see a change of $\chi$ at finitely many primes**, provided $L_F(1,\cdot)$ exists for one of the two
characters and the corrected product converges: the finite factors of $L_F(1,\chi)^e$ and of the corrected product cancel. -/
theorem regProd_congr_finite {χ χ' : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1)
    (hχ' : ∀ v, |χ' v| ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, χ v = χ' v)
    (hL : HasLOne χ' (LOne χ')) (e : ℤ) (f : HeightOneSpectrum (𝓞 F) → ℝ)
    (hf : Multipliable fun v => f v * (1 - χ' v / (normP v : ℝ)) ^ e) :
    regProd χ e f = regProd χ' e f := by
  have hL1 := (hL.congr_finite hχ hχ' S hS).lOne_eq
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => 1 - χ v / (normP v : ℝ)
  set b : HeightOneSpectrum (𝓞 F) → ℝ := fun v => 1 - χ' v / (normP v : ℝ)
  have ha : ∀ v, a v ≠ 0 := fun v => (one_sub_div_pos (hχ v) v).ne'
  have hb : ∀ v, b v ≠ 0 := fun v => (one_sub_div_pos (hχ' v) v).ne'
  have hlf : ∀ v, lFactor χ 1 v / lFactor χ' 1 v = b v / a v := fun v => by
    simp only [lFactor, Real.rpow_neg_one, a, b, div_eq_mul_inv, inv_inv]
    ring
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (a v / b v) ^ e
  have hr : HasProd r (∏ v ∈ S, r v) := hasProd_prod_of_ne_finset_one fun v hv => by
    simp only [r, a, b, hS v hv, div_self (hb v), _root_.one_zpow]
  have h : HasProd (fun v => f v * a v ^ e) ((∏' v, f v * b v ^ e) * ∏ v ∈ S, r v) := by
    refine (hf.hasProd.mul hr).congr_fun fun v => ?_
    simp only [r, div_zpow]
    field_simp [zpow_ne_zero e (hb v)]
    rfl
  unfold regProd
  rw [h.tprod_eq, hL1, Finset.prod_congr rfl fun v _ => hlf v, mul_zpow, ← Finset.prod_zpow]
  have hc : (∏ v ∈ S, (b v / a v) ^ e) * ∏ v ∈ S, r v = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    simp only [r, ← mul_zpow, div_mul_div_comm, mul_comm (b v), div_self (mul_ne_zero (ha v) (hb v)), _root_.one_zpow]
  calc LOne χ' ^ e * (∏ v ∈ S, (b v / a v) ^ e) * ((∏' v, f v * b v ^ e) * ∏ v ∈ S, r v)
      = LOne χ' ^ e * (∏' v, f v * b v ^ e) * ((∏ v ∈ S, (b v / a v) ^ e) * ∏ v ∈ S, r v) := by ring
    _ = _ := by rw [hc, mul_one]

variable (Q' : QuadForm (𝓞 F) 2)

/-- **The regularized Tamagawa measure of $K_{SO}(Q')$ in rank 2** (convergence factors $\lambda_\mathfrak p = L_\mathfrak p(1,\chi')$,
$\chi'$ = `chiP · Q'`):
$$\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO}) = |d_F|^{-1/2}\prod_\sigma\mathrm{vol}(SO(V'_\sigma))\cdot
L_F(1,\chi')^{-1}\prod_\mathfrak p\alpha_\mathfrak p(Q')\bigl(1-\chi'(\mathfrak p)N\mathfrak p^{-1}\bigr)^{-1}.$$
`tamagawaK` with `tprod` replaced by `regProd (chiP · Q') (-1)` (the plain product diverges). The corrected product has
finite support (`multipliable_siegelDensity_binary_reg`). -/
@[kb "weil1982" "§2.3 and Lemma 2.4.2 (convergence factors λ_v = L_v(1, χ)) [unverified]"]
def tamagawaKReg : ℝ :=
  (|(discr F : ℝ)|) ^ (-((2 : ℝ) * (2 - 1) / 4)) * (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q' σ)) *
    regProd (fun v => chiP v Q') (-1) fun v => NF.siegelDensity v Q' Q'

/-- **$\tau^{\mathrm{reg}}(SO(V'))$ for a totally definite binary $V'$:** `tamagawaKReg Q'` times the $SO$-mass, exactly as `tauSO`. Its value $2$ is `BinaryTamagawaTwoReg`. -/
@[kb "weil1982" "§2.4, p. 23 and Lemma 2.4.2, p. 26 (rank 2, regularized measure) [unverified]"]
def tauSOReg : ℝ :=
  tamagawaKReg Q' * dcMass ((ratPoints (formF Q')).subgroupOf (soAf (formF Q')))
    ((locStab (formF Q') (stdLat F 2)).subgroupOf (soAf (formF Q')))

variable [IsTotallyReal F] in
theorem tauSOReg_eq (hQ : Q'.Nondegenerate) (hpd : IsTotallyPosDef (formF Q')) :
    tauSOReg Q' = tamagawaKReg Q' * (2 * mass (formF Q') (stdLat F 2)) := by
  rw [tauSOReg, mass_SO_eq_two_mul_mass Q' hQ (by norm_num) hpd (HilbertModular.isIntegral_stdLat Q')]

end TamagawaReg

/-! ### 5. The rank-3 frame identity -/

section Frame3

variable [IsTotallyReal F]

/-- `two_mul_tamagawaK_mul_repMass_frame3` with the form in $2 + 1$ variables (the frame-identity proof at $n = 2$, with the
regularized products). -/
theorem two_mul_tamagawaK_mul_repMass_frame3_aux (Q₀ : QuadForm (𝓞 F) (2 + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) :
    2 * tamagawaK Q₀ * repMass (formF Q₀) (stdLat F (2 + 1)) (algebraMap (𝓞 F) F m) =
      tauSOReg fr.Q' * siegelProduct3 Q₀ m := by
  classical
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := by
    have := hQF
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    exact fun h => this (by rw [h, map_zero])
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  have hpd' : IsTotallyPosDef (formF fr.Q') := by
    have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
    rw [fr.compMat_eq] at h1
    exact isTotallyPosDef_of_splitForm h1
  have hgli : ∀ v, OrbitalLocalIdentityAt v Q₀ fr := fun v =>
    orbitalLocalIdentityAt_all (orbitalLocalIdentities Q₀ hQ₀) hQ₀ (by norm_num) hρ fr v
  -- the local factors
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locW v fr 0
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) /
      ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F m)‖ ^ 2
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.localDensity v Q₀ m
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F m) ≠ 0 :=
      (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hαpos : ∀ v, 0 < α v := fun v => siegelDensity_pos v Q₀ hQ₀
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  have hW : ∀ v, W0 v = α' v * E v * β v / α v := by
    intro v
    have hj := (hgli v).eq 0
    simp only [zero_mul, zpow_zero, mul_zero, mul_one] at hj
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F m) =
      algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F m) by rw [map_mul, map_ofNat]] at hj
    rw [betaZ_algebraMap v Q₀ m] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have h2ρ : 0 < ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F m)‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    have hα : 0 < NF.siegelDensity v Q₀ Q₀ := siegelDensity_pos v Q₀ hQ₀
    simp only [W0, E, α, α', β]
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (2 + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * algebraMap (𝓞 F) F m)‖ ^ 2 = B2 at hj h2ρ ⊢
    rw [eq_div_iff hα.ne']
    calc locW v fr 0 * NF.siegelDensity v Q₀ Q₀
        = locW v fr 0 * NF.siegelDensity v Q₀ Q₀ * B2 * D⁻¹ * D / B2 := by field_simp
      _ = _ := by rw [hj]; ring
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | frameLat v fr.g ≠ std v ∨
      v.valuation F (algebraMap (𝓞 F) F m) ≠ 1 ∨ v.valuation F 2 ≠ 1}.Finite := by
    refine ((Filter.eventually_cofinite.mp (loc_eventually_std (glImage_isLattice fr.g⁻¹ intVec_isLattice))).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => ?_
    simpa [frameLat, or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show locW v fr 0 = 1
    unfold locW
    rw [zpow_zero, h.1]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union
      (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  -- the absolutely convergent products
  have hαm : Multipliable α := multipliable_siegelDensity (N := 2 + 1) (by omega) (by omega) Q₀ hQ₀
  have hA : 0 < ∏' v, α v := tprod_siegelDensity_pos (N := 2 + 1) (by omega) Q₀ hQ₀
  have hW0p : HasProd W0 (∏ᶠ v, W0 v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hW0fin).hasProd
    rwa [tprod_eq_finprod hW0fin] at this
  have hEp : HasProd E (∏ᶠ v, E v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hEfin).hasProd
    rwa [tprod_eq_finprod hEfin] at this
  have hEprod : 0 < ∏ᶠ v, E v := by
    rw [finprod_eq_prod_of_mulSupport_subset E (s := hEfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hEpos v
  -- the character and the regularized products
  obtain ⟨hL0, hL⟩ := lOne_chiTern_pos hpd hm
  obtain ⟨S, hS⟩ := chiP_frame_eq_chiTern hpd hm fr
  have hχ : ∀ v, |chiTern Q₀ m v| ≤ 1 := fun v => abs_chiTern_le v Q₀ m
  have hlam : ∀ v, 0 < 1 - chiTern Q₀ m v / (normP v : ℝ) := fun v => one_sub_div_pos (hχ v) v
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => α' v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (-1 : ℤ)
  have hgfin : Function.HasFiniteMulSupport g := hasFiniteMulSupport_siegelDensity_binary_reg hQ'nd S hS
  have hgpos : ∀ v, 0 < g v := fun v => mul_pos (hα'pos v) (zpow_pos (hlam v) _)
  have hGp : HasProd g (∏ᶠ v, g v) := by
    have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hgfin).hasProd
    rwa [tprod_eq_finprod hgfin] at this
  have hG : 0 < ∏ᶠ v, g v := by
    rw [finprod_eq_prod_of_mulSupport_subset g (s := hgfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hgpos v
  have hβp : HasProd (fun v => β v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ))
      ((∏ᶠ v, W0 v) * (∏' v, α v) / ((∏ᶠ v, E v) * ∏ᶠ v, g v)) := by
    refine ((hW0p.mul hαm.hasProd).div₀ (hEp.mul hGp) (mul_pos hEprod hG).ne').congr_fun fun v => ?_
    simp only [g, hW v, zpow_one, _root_.zpow_neg_one]
    have := hα'pos v; have := hEpos v; have := hαpos v; have := (hlam v).ne'
    field_simp
  have hreg3 : regProd (chiTern Q₀ m) 1 β =
      LOne (chiTern Q₀ m) * ((∏ᶠ v, W0 v) * (∏' v, α v) / ((∏ᶠ v, E v) * ∏ᶠ v, g v)) := by
    show LOne (chiTern Q₀ m) ^ (1 : ℤ) * ∏' v, β v * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ) = _
    rw [hβp.tprod_eq, zpow_one]
  have hreg2 : regProd (fun v => chiP v fr.Q') (-1) α' = (LOne (chiTern Q₀ m))⁻¹ * ∏ᶠ v, g v := by
    rw [regProd_congr_finite (fun v => abs_chiP_le fr.Q' v) hχ S hS hL (-1) α'
      (multipliable_of_hasFiniteMulSupport hgfin)]
    show LOne (chiTern Q₀ m) ^ (-1 : ℤ) * ∏' v, g v = _
    rw [hGp.tprod_eq, _root_.zpow_neg_one]
  -- `repMass` through the frame
  have hrep : repMass (formF Q₀) (stdLat F (2 + 1)) (algebraMap (𝓞 F) F m) =
      mass (formF fr.Q') (stdLat F 2) * ∏ᶠ v, W0 v := by
    have h1 := repMass_eq_mass_mul_finprod Q₀ hpd hρ fr (β := 1) one_ne_zero
    rw [one_pow, one_mul] at h1
    rw [h1]
    congr 1
  -- the archimedean products
  have key : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 + 1) (detGram Q₀ σ)) * ∏ᶠ v, E v =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (2 + 1) ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ) := by
    rw [finprod_frameJac fr hρ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => arch_place_siegel Q₀ hpd fr hρ σ
  have hδ : 0 < |(NumberField.discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [hrep, tauSOReg_eq fr.Q' hQ'nd hpd']
  unfold tamagawaK tamagawaKReg siegelProduct3 siegelProductWith
  rw [hreg2, hreg3]
  have hδe : |(NumberField.discr F : ℝ)| ^ (-(((2 + 1 : ℕ) : ℝ) * (((2 + 1 : ℕ) : ℝ) - 1) / 4)) =
      |(NumberField.discr F : ℝ)| ^ (-((2 : ℝ) * (2 - 1) / 4)) *
        |(NumberField.discr F : ℝ)| ^ (-(((3 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  have hV₀ : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO (2 + 1) (detGram Q₀ σ)) =
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram fr.Q' σ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ)) / ∏ᶠ v, E v := by
    rw [eq_div_iff hEprod.ne']; exact key
  rw [hδe, hV₀]
  have hL0' := hL0.ne'
  have hG' := hG.ne'
  have hE' := hEprod.ne'
  field_simp
  ring

/-- **The rank-3 frame identity** (Siegel's theorem for one number in rank $3$, with the stabilizer's regularized Tamagawa
number; Weil 1982, §4.5, p. 100 and p. 109 [unverified], at $N = 3$). For $Q_0$ totally positive definite ternary over
$\mathcal O_F$ ($F$ totally real, any class number), $m \in \mathcal O_F$ totally positive and any adapted frame
$Q_0\circ g = \langle m\rangle\perp Q_0'$:
$$2\,\mu_{\mathrm{Tam}}(K_{SO}(Q_0))\cdot\mathrm{repMass}(\mathcal O_F^3, m) = \tau^{\mathrm{reg}}(SO(Q_0'))\cdot S_3(L, m),$$
$S_3$ = `siegelProduct3` (with $L_F(1,\chi_m)$), $\tau^{\mathrm{reg}}$ = `tauSOReg` (with $L_F(1,\chi')^{-1}$). **Unconditional**: the
local orbital identities are the theorem `orbitalLocalIdentities`.
*Proof.* the proof (`two_mul_tamagawaK_mul_repMass_frame_aux`) with $n = 2$; the two divergent products are replaced by
$\prod\beta_\mathfrak p(1-\chi_m/N\mathfrak p)$ (absolutely convergent) and $\prod\alpha_\mathfrak p(Q_0')(1-\chi_m/N\mathfrak p)^{-1}$ (finite support,
`hasFiniteMulSupport_siegelDensity_binary_reg`, using $\chi' = \chi_m$ off a finite set, `chiP_frame_eq_chiTern`); the factors
$L_F(1,\chi_m)^{\pm1}$ cancel (`lOne_chiTern_pos`, `regProd_congr_finite`). -/
@[kb "weil1982" "§4.5, p. 100 and p. 109 (Siegel's theorem from the fibration over T(ρ), one number; N = 3, regularized) [unverified]"]
theorem two_mul_tamagawaK_mul_repMass_frame3 (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) :
    2 * tamagawaK Q₀ * repMass (formF Q₀) (stdLat F 3) (algebraMap (𝓞 F) F m) =
      tauSOReg fr.Q' * siegelProduct3 Q₀ m :=
  two_mul_tamagawaK_mul_repMass_frame3_aux Q₀ hpd hm fr

/-- **Numbers not represented over $F$:** $S_3(L, m) = 0$ (Hasse–Minkowski gives a prime with $\beta_\mathfrak p(L, m) = 0$, and the
corrected product has that zero factor). -/
theorem siegelProduct3_eq_zero_of_not_rep (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (h : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m) : siegelProduct3 Q₀ m = 0 := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  have hQF := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hnot : ¬ (formF Q₀).RepresentsIn F (algebraMap (𝓞 F) F m) := by
    rintro ⟨x, hx⟩; exact h ⟨x, hx⟩
  rw [represents_iff_everywhere_nf (formF Q₀) hQF _ hρ] at hnot
  simp only [NFPlace.Everywhere, not_forall] at hnot
  obtain ⟨p, hp⟩ := hnot
  cases p with
  | infinite w => exact absurd (representsIn_real Q₀ hpd hm w) hp
  | finite v =>
    have h0 : NF.localDensity v Q₀ m = 0 := by
      rw [← betaZ_algebraMap]; exact betaZ_eq_zero_of_not_rep Q₀ hQ₀ (by omega) v hρ hp
    unfold siegelProduct3 siegelProductWith regProd
    rw [tprod_of_exists_eq_zero ⟨v, by simp only [h0, zero_mul]⟩, mul_zero, mul_zero]

end Frame3

/-! ### The interface: $\tau^{\mathrm{reg}}(SO_2) = 2$ -/

/-- **Input: the regularized Tamagawa number of every totally definite binary form over $\mathcal O_F$ is $2$**
($\tau^{\mathrm{reg}}(SO(V')) = 2$; Ono / Weil for the norm torus $R^1_{E/F}\mathbb G_m$, with convergence factors
$\lambda_\mathfrak p = L_\mathfrak p(1,\chi')$ [unverified]).

Field:
- `tau_eq_two`: `tauSOReg Q' = 2` for every `Q' : QuadForm (𝓞 F) 2` with `formF Q'` totally positive definite.

*Status.* A theorem: over ℚ (`binaryTamagawaTwoReg_rat`, by the backwards Weil step $1\to2$ from the binary Siegel formula and
$\tau(SO_1) = 1$, `tauSO_rankOne_eq_one`) and over every totally real $F$ (`binaryTamagawaTwoReg_nf`).
*Independence (hypothesis hygiene):* a statement about binary forms only (their regularized local volumes and $SO$-mass);
it mentions no ternary form, no number $m$ and no representation count, so it is not equivalent to Siegel's formula in
rank 3 (which also needs `TernaryTamagawaTwo` and the frame identity). -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors [unverified]"]
structure BinaryTamagawaTwoReg (F : Type) [Field F] [NumberField F] : Prop where
  tau_eq_two : ∀ Q' : QuadForm (𝓞 F) 2, IsTotallyPosDef (formF Q') → tauSOReg Q' = 2

section Siegel3

variable [IsTotallyReal F]

/-- **Siegel's formula in rank 3 from one frame:** if $\tau(SO(Q_0)) = 2$ and the complement $Q_0'$ of some frame adapted to $m$ has
$\tau^{\mathrm{reg}}(SO(Q_0')) = 2$, then `SiegelFormulaAt3 Q₀ m`. -/
theorem siegelFormulaAt3_of_frame (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (hτ : TamagawaNumberTwo Q₀) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (fr : AdaptedFrame (formF Q₀) (algebraMap (𝓞 F) F m)) (hτ' : tauSOReg fr.Q' = 2) : SiegelFormulaAt3 Q₀ m := by
  refine ⟨?_⟩
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  show repMass (formF Q₀) (stdLat F 3) (algebraMap (𝓞 F) F m) = mass (formF Q₀) (stdLat F 3) * siegelProduct3 Q₀ m
  have key := two_mul_tamagawaK_mul_repMass_frame3 Q₀ hpd hm fr
  rw [hτ'] at key
  have hmass := massFormula Q₀ hQ₀ (by norm_num) hpd (HilbertModular.isIntegral_stdLat Q₀) hτ
  have hpos := mass_pos hpd (stdLat F 3) (HilbertModular.isIntegral_stdLat Q₀)
  have hμ : tamagawaK Q₀ ≠ 0 := by
    intro h0; rw [hmass, h0, _root_.inv_zero] at hpos; exact lt_irrefl 0 hpos
  rw [hmass]
  field_simp
  linarith

/-- **Siegel's formula in rank 3** (`SiegelFormulaAt3`) for every totally positive $m$, from $\tau(SO(Q_0)) = 2$ and
`BinaryTamagawaTwoReg F` (both sides vanish when $Q_0$ does not represent $m$ over $F$). With `TernaryTamagawaTwo`
this leaves `BinaryTamagawaTwoReg` as the only rank-3 input. -/
@[kb "siegel1935" "Hauptsatz, n = 3 (regularized; from τ(SO_3) = τ(SO_2) = 2) [unverified]"]
theorem siegelFormulaAt3_of_tau (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (hτ : TamagawaNumberTwo Q₀) (h2 : BinaryTamagawaTwoReg F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3 Q₀ m := by
  have hρ : algebraMap (𝓞 F) F m ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  by_cases h : ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m
  · obtain ⟨ξ, hξ⟩ := h
    obtain ⟨fr⟩ := exists_adaptedFrame (formF Q₀) hξ hρ
    have hpd' : IsTotallyPosDef (formF fr.Q') := by
      have h1 := isTotallyPosDef_compMat (formF Q₀) fr.g hpd
      rw [fr.compMat_eq] at h1
      exact isTotallyPosDef_of_splitForm h1
    exact siegelFormulaAt3_of_frame Q₀ hpd hτ hm fr (h2.tau_eq_two fr.Q' hpd')
  · refine ⟨?_⟩
    show repMass (formF Q₀) (stdLat F 3) (algebraMap (𝓞 F) F m) = mass (formF Q₀) (stdLat F 3) * siegelProduct3 Q₀ m
    rw [repMass_eq_zero_of_not_rep _ _ h, siegelProduct3_eq_zero_of_not_rep Q₀ hpd hm h, mul_zero]

end Siegel3
end QuadFormsKB.Tamagawa
