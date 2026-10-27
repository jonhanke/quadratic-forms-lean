/-
# Binary regularized bookkeeping: $\tau^{\mathrm{reg}}(SO_2)$ under change of lattice and rescaling

**Layer:** a totally real number field $F$ (any class number); binary forms $Q'$ over $\mathcal O_F$, totally positive definite.
We define $\tau^{\mathrm{reg}}(Q')$ (`tauSOReg`) as the combinatorial $\tau(SO)$ with the divergent rank-2 product
$\prod_\mathfrak p\alpha_\mathfrak p$ replaced by
`regProd (chiP · Q') (-1)`. The rank $\ge3$ invariance theorems (`tauSO_compMat_nf`, `tauSO_smul_compMat_diagonal`) need $n\ne2$ only
to split $\prod\alpha_\mathfrak p\cdot\prod r_\mathfrak p$; here the same local identities are used, with the finitely supported
corrections moved through `regProd` instead.

**Proves** (no `IsPrincipalIdealRing`, no `hn2`):
* `regProd_mul_fin`, `regProd_transport`: $\mathrm{regProd}_{\chi_1}(-1,\alpha_0 g) = \mathrm{regProd}_{\chi_0}(-1,\alpha_0)\prod_Sg$ for $g$ finitely supported,
  $\chi_1 = \chi_0$ off a finite set; `lOne_chiP_binary`: $L_F(1,\chi')$ exists and is positive for every totally definite binary $Q'$;
  `chiP_eq_of_det_sq` ($\chi'$ depends only on the square class of $\det H'$ off a finite set).
* **`tauSOReg_compMat`**: $\tau^{\mathrm{reg}}(Q'\circ G) = \tau^{\mathrm{reg}}(Q')$ for every $G\in M_2(\mathcal O_F)$, $\det G\ne0$.
* **`tauSOReg_smul_compMat_diagonal`**, **`tauSOReg_smul_compMat`**: $\tau^{\mathrm{reg}}(c\,(Q'\circ G)) = \tau^{\mathrm{reg}}(Q')$.
* **`tauSOReg_eq_diag`**: $\tau^{\mathrm{reg}}(Q') = \tau^{\mathrm{reg}}(\langle1,D\rangle)$, $D=\det H'$ (the norm form of $\mathcal O_F[\sqrt{-D}]$), and
  **`BinaryTamagawaTwoRegDiag`**: $\tau^{\mathrm{reg}}(\langle1,D\rangle)=2$ for all totally definite $\langle1,D\rangle$ $\Leftrightarrow$ `BinaryTamagawaTwoReg F` (`binaryTamagawaTwoReg_iff`); more generally
  `binaryTamagawaTwoReg_of_family` (any family of representatives of the square classes of $\det H'$).

Sources: Weil 1982, §2.2.1, p. 14; Thm. 2.3.1, pp. 21–22; §2.4, p. 22 (independence of the choice of gauge form and lattice).
-/
import QuadFormsKB.Tamagawa.SiegelRank3Frame
import QuadFormsKB.Tamagawa.LatticeChangeNF

open NumberField IsDedekindDomain Matrix Filter Topology
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open Lattices NFEuler RegProd LocalDensity QuadForm QuadFormsKB.HilbertModular LatChange

variable {F : Type} [Field F] [NumberField F]

/-! ### 1. `regProd` with finitely supported corrections -/

/-- **A finitely supported factor passes through `regProd`:** $\mathrm{regProd}_\chi(e, fg) = \mathrm{regProd}_\chi(e, f)\prod_{\mathfrak p\in S}g(\mathfrak p)$
when $g = 1$ off $S$ and $f\,(1-\chi/N)^e$ is multipliable. -/
theorem regProd_mul_fin (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ) {f g : HeightOneSpectrum (𝓞 F) → ℝ}
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hg : ∀ v ∉ S, g v = 1)
    (hf : Multipliable fun v => f v * (1 - χ v / (normP v : ℝ)) ^ e) :
    regProd χ e (fun v => f v * g v) = regProd χ e f * ∏ v ∈ S, g v := by
  have hgm : Multipliable g := multipliable_of_ne_finset_one hg
  have h : (fun v => f v * g v * (1 - χ v / (normP v : ℝ)) ^ e) =
      fun v => (f v * (1 - χ v / (normP v : ℝ)) ^ e) * g v := by
    funext v; ring
  unfold regProd
  rw [h, hf.tprod_mul hgm, tprod_eq_prod hg]
  ring

/-! ### 2. The character $\chi'$ of a binary form -/

/-- **$\chi'$ depends only on the square class of $\det H'$ (off a finite set):** if $\det H_2 = u^2\det H_1$, $u\ne0$,
`chiP v Q₂ = chiP v Q₁` outside the primes dividing $2u\det H_1$. -/
theorem chiP_eq_of_det_sq {Q₁ Q₂ : QuadForm (𝓞 F) 2} (hQ : Q₁.Nondegenerate) {u : 𝓞 F} (hu : u ≠ 0)
    (h : Q₂.hessian.det = u ^ 2 * Q₁.hessian.det) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, chiP v Q₂ = chiP v Q₁ := by
  classical
  have hne : (2 * u * Q₁.hessian.det : 𝓞 F) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hu) hQ
  refine ⟨(Siegel.finite_mem_asIdeal hne).toFinset, fun v hv => ?_⟩
  have hv' : 2 * u * Q₁.hessian.det ∉ v.asIdeal := fun hm => hv (by simpa using hm)
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ hm))
  have hu' : u ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ hm))
  have hd1 : Q₁.hessian.det ∉ v.asIdeal := fun hm => hv' (v.asIdeal.mul_mem_left _ hm)
  have hd2 : Q₂.hessian.det ∉ v.asIdeal := by
    rw [h]
    intro hm
    rcases v.isPrime.mem_or_mem hm with hm | hm
    · exact hu' (v.isPrime.mem_of_pow_mem 2 hm)
    · exact hd1 hm
  rw [chiP_binary_eq_charNF v Q₁ h2 hd1, chiP_binary_eq_charNF v Q₂ h2 hd2, h]
  have hres : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v u) ≠ 0 := fun h0 =>
    hu' ((NF.π_dvd_ι_iff v u).1 ((DVR.residue_eq_zero_iff_dvd (NF.irreducible_π v) _).1 h0))
  congr 1
  unfold Siegel.charNF
  have e : IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v (-(u ^ 2 * Q₁.hessian.det))) =
      (IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v u)) ^ 2 *
        IsLocalRing.residue (v.adicCompletionIntegers F) (NF.ι v (-Q₁.hessian.det)) := by
    simp only [map_neg, map_mul, map_pow]; ring
  rw [e, map_mul, quadraticChar_sq_one' hres, one_mul]

section Real

variable [IsTotallyReal F]

/-- **$E = F(\sqrt\delta)$ for a non-square $\delta\in\mathcal O_F$:** a quadratic extension with $s^2=\delta$, $\sigma s=-s$
(the proof of `exists_sqrtExt_deltaTern`, for an arbitrary non-square). -/
theorem exists_sqrtExt_of_not_isSquare {δ : 𝓞 F} (hd : ¬ IsSquare (algebraMap (𝓞 F) F δ)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (_ : Algebra.IsQuadraticExtension F E) (s : E),
      s ^ 2 = algebraMap F E (algebraMap (𝓞 F) F δ) ∧ Binary.Rel.conj F E s = -s := by
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

theorem nondegenerate_of_isTotallyPosDef {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} (hpd : IsTotallyPosDef (formF Q₀)) :
    Q₀.Nondegenerate := by
  have := hpd.nondegenerate
  rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact fun h => this (by rw [h, map_zero])

/-- **$L_F(1,\chi')$ exists and is positive for every totally definite binary form** (`chiP · Q'` is $\chi_{E/F}$ for
$E=F(\sqrt{-\det H'})$ off a finite set; `exists_hasLOne_of_almost_relChar`). -/
@[kb "neukirch1999" "Ch. VII §5, Cor. 5.11 (L(1, χ_{E/F}) = ρ_E/ρ_F ≠ 0) [unverified]"]
theorem lOne_chiP_binary {Q' : QuadForm (𝓞 F) 2} (hpd : IsTotallyPosDef (formF Q')) :
    0 < LOne (fun v => chiP v Q') ∧ HasLOne (fun v => chiP v Q') (LOne fun v => chiP v Q') := by
  have hQ := nondegenerate_of_isTotallyPosDef hpd
  have hsq : ¬ IsSquare (algebraMap (𝓞 F) F (-Q'.hessian.det)) := by
    rintro ⟨r, hr⟩
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := congrArg (realEmb F w) hr
    have hd := realEmb_det_hessian_pos hpd w
    rw [map_neg, map_neg] at h
    have : realEmb F w r * realEmb F w r ≥ 0 := mul_self_nonneg _
    rw [map_mul] at h
    nlinarith
  obtain ⟨E, _, _, _, _, s, hs, hsc⟩ := exists_sqrtExt_of_not_isSquare hsq
  exact exists_hasLOne_of_almost_relChar (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    (fun v => abs_chiP_le Q' v)
    (isAlmostRelChar_of_sqrt (neg_ne_zero.2 hQ) hs hsc ∅ fun v _ h2 hδ =>
      chiP_binary_eq_charNF v Q' h2 fun h => hδ (v.asIdeal.neg_mem_iff.2 h))

/-! ### 3. Transport of the regularized product along a finitely supported density ratio -/

/-- **The regularized rank-2 product under a finitely supported change of densities:** if
$\alpha_\mathfrak p(Q_1) = \alpha_\mathfrak p(Q_0)\,g(\mathfrak p)$ with $g = 1$ off a finite set $S$, and $\chi'_{Q_1} = \chi'_{Q_0}$ off a finite set, then
$\mathrm{regProd}_{\chi'_{Q_1}}(-1,\alpha(Q_1)) = \mathrm{regProd}_{\chi'_{Q_0}}(-1,\alpha(Q_0))\prod_Sg$. -/
theorem regProd_transport {Q₀ Q₁ : QuadForm (𝓞 F) 2} (h₀ : Q₀.Nondegenerate)
    (hpd₀ : IsTotallyPosDef (formF Q₀)) {g : HeightOneSpectrum (𝓞 F) → ℝ}
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hg : ∀ v ∉ S, g v = 1)
    (hα : ∀ v, NF.siegelDensity v Q₁ Q₁ = NF.siegelDensity v Q₀ Q₀ * g v)
    (hχ : ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S₂, chiP v Q₁ = chiP v Q₀) :
    regProd (fun v => chiP v Q₁) (-1) (fun v => NF.siegelDensity v Q₁ Q₁) =
      regProd (fun v => chiP v Q₀) (-1) (fun v => NF.siegelDensity v Q₀ Q₀) * ∏ v ∈ S, g v := by
  obtain ⟨S₂, hS₂⟩ := hχ
  have hm : Multipliable fun v => NF.siegelDensity v Q₀ Q₀ * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ) :=
    multipliable_siegelDensity_binary_reg h₀ ∅ fun _ _ => rfl
  rw [show (fun v => NF.siegelDensity v Q₁ Q₁) = fun v => NF.siegelDensity v Q₀ Q₀ * g v from funext hα]
  have hmg : Multipliable fun v => NF.siegelDensity v Q₀ Q₀ * g v * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ) := by
    have := hm.mul (multipliable_of_ne_finset_one hg)
    refine this.congr fun v => ?_
    ring
  rw [regProd_congr_finite (fun v => abs_chiP_le Q₁ v) (fun v => abs_chiP_le Q₀ v) S₂ (fun v hv => hS₂ v hv)
    (lOne_chiP_binary hpd₀).2 (-1) _ hmg]
  exact regProd_mul_fin _ (-1) S hg hm

end Real

/-! ### 4. Change of lattice -/

section Change

variable [IsTotallyReal F]

theorem hessian_det_compMat (Q : QuadForm (𝓞 F) 2) (G : Matrix (Fin 2) (Fin 2) (𝓞 F)) :
    (Q.compMat G).hessian.det = G.det ^ 2 * Q.hessian.det := by
  rw [hessian_compMat, det_mul, det_mul, det_transpose]; ring

/-- **$\mu^{\mathrm{reg}}_{\mathrm{Tam}}(K_{SO})$ of $Q'\circ G$ is that of the lattice $G\mathcal O_F^2$ for $Q'$** (the rank-2 regularized analogue of
`tamagawaK_compMat_eq`): $\mu^{\mathrm{reg}}(Q'\circ G) = \mu^{\mathrm{reg}}(Q')\cdot r(K(G\mathcal O_F^2), K(\mathcal O_F^2))$. The local factors of
$Q'\circ G$ and of $Q'$ differ by the finitely supported ratio $r_\mathfrak p/\|\det G\|_\mathfrak p^{3}$ (the $\alpha$ law at every prime,
`latLocalFactor_eq`), which is moved through `regProd` (`regProd_transport`), and the Jacobians cancel by the product formula. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), regularized in rank 2"]
theorem tamagawaKReg_compMat (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) (hpd : IsTotallyPosDef (formF Q))
    (G : Matrix (Fin 2) (Fin 2) (𝓞 F)) (hG : G.det ≠ 0) :
    tamagawaKReg (Q.compMat G) = tamagawaKReg Q *
      relRatio (locStab (formF Q) (Lat.image (glF G hG) (stdLat F 2))) (locStab (formF Q) (stdLat F 2)) := by
  classical
  set QF := formF Q
  set M : Lat F 2 := Lat.image (glF G hG) (stdLat F 2)
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v M.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std M.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v M.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v M.1)) (stdStab QF v)
  have hr1 : ∀ v ∉ S, r v = 1 := fun v hv => by
    simp only [r]; rw [hS v hv, ← stdStab_eq_stabLat, relRatio_self]
  have hR : relRatio (locStab QF M) (locStab QF (stdLat F 2)) = ∏ v ∈ S, r v := by
    rw [relRatio_symm', relRatio_locStab_eq_prod QF M S hS, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (relRatio_symm' _ _).symm
  set x : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F G.det)‖
  have hGF : algebraMap (𝓞 F) F G.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hx0 : ∀ v, x v ≠ 0 := fun v => norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hGF)
  have hfacQ : ∀ v, latLocalFactor v Q (G.map (NF.ι v)) = NF.siegelDensity v Q Q * r v := fun v => by
    rw [latLocalFactor_eq v Q hQ _ (det_map_ι_ne_zero v hG), ← loc_image_glF v G hG]
    simp only [r]; rw [relRatio_stab_eq_KL]
  have hfacG : ∀ v, latLocalFactor v Q (G.map (NF.ι v)) =
      NF.siegelDensity v (Q.compMat G) (Q.compMat G) * x v ^ (2 + 1) := fun v => by
    unfold latLocalFactor
    have e1 : (NF.Qp v Q).compMat (G.map (NF.ι v)) = NF.Qp v (Q.compMat G) := map_compMat _ _ _
    have e2 : ‖(((G.map (NF.ι v)).det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = x v := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e1, e2]
    simp only [NF.siegelDensity, ite_true, NF.localDensityForm_eq_completion]
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | G.det ∈ v.asIdeal}.Finite := Siegel.finite_mem_asIdeal hG
  set U := S ∪ hTfin.toFinset
  have hx1 : ∀ v ∉ U, x v = 1 := fun v hv =>
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v G.det).mpr (fun h =>
      hv (Finset.mem_union_right _ (hTfin.mem_toFinset.mpr h)))
  have hr1' : ∀ v ∉ U, r v = 1 := fun v hv => hr1 v (fun h => hv (Finset.mem_union_left _ h))
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => r v / x v ^ 3
  have hg1 : ∀ v ∉ U, g v = 1 := fun v hv => by simp only [g, hr1' v hv, hx1 v hv]; norm_num
  have hα : ∀ v, NF.siegelDensity v (Q.compMat G) (Q.compMat G) = NF.siegelDensity v Q Q * g v := fun v => by
    have h := (hfacQ v).symm.trans (hfacG v)
    have hx3 : x v ^ 3 ≠ 0 := pow_ne_zero _ (hx0 v)
    simp only [g]
    rw [← mul_div_assoc, eq_div_iff hx3]
    linear_combination (-1 : ℝ) * h
  have hχ := chiP_eq_of_det_sq hQ hG (Q₂ := Q.compMat G) (hessian_det_compMat Q G)
  have hT := regProd_transport hQ hpd U hg1 hα hχ
  -- the Jacobian
  have hxinv1 : ∀ v ∉ U, (x v)⁻¹ = 1 := fun v hv => by rw [hx1 v hv, inv_one]
  have hN := tprod_norm_inv hG
  rw [tprod_eq_prod hxinv1] at hN
  set Nd := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F G.det)‖
  have hpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (algebraMap (𝓞 F) F G.det)‖ := fun σ =>
    norm_pos_iff.mpr ((map_ne_zero σ).mpr hGF)
  have hNd : 0 < Nd := Finset.prod_pos fun σ _ => hpos σ
  have hxU : ∏ v ∈ U, x v ^ 3 = (Nd ^ 3)⁻¹ := by
    rw [← hN, Finset.prod_inv_distrib, inv_pow, inv_inv, Finset.prod_pow]
  have hrU : ∏ v ∈ U, r v = ∏ v ∈ S, r v :=
    (Finset.prod_subset Finset.subset_union_left fun v _ hv => hr1 v hv).symm
  have hgU : ∏ v ∈ U, g v = (∏ v ∈ S, r v) * Nd ^ 3 := by
    simp only [g]
    rw [Finset.prod_div_distrib, hxU, hrU]
    field_simp
  -- the archimedean factors
  have hσ : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram (Q.compMat G) σ) =
      (‖σ (algebraMap (𝓞 F) F G.det)‖ ^ (2 + 1))⁻¹ * archVolSO 2 (detGram Q σ) := fun σ => by
    rw [detGram_compMat, archVolSO_mul 2 (d := detGram Q σ) (by positivity) (norm_nonneg _)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos σ).le, ← Real.rpow_natCast, ← Real.rpow_neg (hpos σ).le]
    congr 1; push_cast; ring
  unfold tamagawaKReg
  rw [hT, hgU, hR, Finset.prod_congr rfl fun σ _ => hσ σ, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_pow]
  have hNd' : (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F G.det)‖) ≠ 0 := hNd.ne'
  simp only [show (2 : ℕ) + 1 = 3 from rfl]
  field_simp
  have e : (∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F G.det)‖) = Nd := rfl
  rw [e]; ring

/-- **$\tau^{\mathrm{reg}}(SO)$ is invariant under every integral change of lattice** (rank 2, no `hn2`):
$\tau^{\mathrm{reg}}(Q'\circ G) = \tau^{\mathrm{reg}}(Q')$ for $G\in M_2(\mathcal O_F)$, $\det G\ne0$ (any class number).
*Proof:* $\mathrm{Mass}(Q'\circ G) = \mathrm{Mass}(Q', G\mathcal O_F^2)$ (`mass_similar`), $= \mathrm{Mass}(Q')\,r(K(\mathcal O_F^2),K(G\mathcal O_F^2))$ and
`tamagawaKReg_compMat`; the two relative indices are inverse. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), regularized in rank 2"]
theorem tauSOReg_compMat (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) (hpd : IsTotallyPosDef (formF Q))
    (G : Matrix (Fin 2) (Fin 2) (𝓞 F)) (hG : G.det ≠ 0) :
    tauSOReg (Q.compMat G) = tauSOReg Q := by
  set QF := formF Q
  set M : Lat F 2 := Lat.image (glF G hG) (stdLat F 2)
  have hQG : (Q.compMat G).Nondegenerate := nondegenerate_compMat_of_det hQ hG
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdG : IsTotallyPosDef (formF (Q.compMat G)) := by
    rw [formF, ← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF
  have hmass : mass (formF (Q.compMat G)) (stdLat F 2) = mass QF M := by
    have e : formF (Q.compMat G) = (1 : F) • QF.compMat (glF G hG).val := by
      rw [one_smul_form, glF_val, formF, map_compMat]
    rw [e]; exact mass_similar QF one_ne_zero (glF G hG) _
  have hm2 := mass_eq_mass_mul_relRatio hpd (stdLat F 2) M (isIntegral_std Q)
    (isIntegral_image Q G _ (glF_val G hG))
  have hc := commensurable_locStab QF (stdLat F 2) M
  have h1 : relRatio (locStab QF M) (locStab QF (stdLat F 2)) *
      relRatio (locStab QF (stdLat F 2)) (locStab QF M) = 1 :=
    relRatio_mul_relRatio_symm ⟨hc.2.relIndex_ne_zero, hc.1.relIndex_ne_zero⟩
  rw [tauSOReg_eq _ hQG hpdG, tauSOReg_eq Q hQ hpd, hmass, tamagawaKReg_compMat Q hQ hpd G hG, hm2]
  linear_combination (tamagawaKReg Q * 2 * mass QF (stdLat F 2)) * h1

end Change

/-! ### 5. Rescaling -/

section Scaling

variable [IsTotallyReal F]

/-- **$\tau^{\mathrm{reg}}(SO)$ is invariant under $Q_0\mapsto c\,(Q_0\circ D)$, $D$ diagonal** (rank 2, no `hn2`; the regularized
analogue of `tauSO_smul_compMat_diagonal`). The local identity $\alpha_\mathfrak p(Q_1)\,r_\mathfrak p = |w|_\mathfrak p^{-1}\alpha_\mathfrak p(Q_0)$
(`localDensity_mul_relRatio`) makes $\alpha_\mathfrak p(Q_1) = \alpha_\mathfrak p(Q_0)\cdot g(\mathfrak p)$ with $g = |w|^{-1}_\mathfrak p/r_\mathfrak p$ finitely supported
(`regProd_transport`), and $\prod_\mathfrak p|w|_\mathfrak p^{-1} = \prod_\sigma|\sigma(w)|$ cancels the archimedean volumes. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), regularized in rank 2"]
theorem tauSOReg_smul_compMat_diagonal (Q₀ : QuadForm (𝓞 F) 2) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) {c : 𝓞 F} (hc : c ≠ 0) (cv : Fin 2 → 𝓞 F) (hcv : ∀ a, cv a ≠ 0)
    (hpd₁ : IsTotallyPosDef (formF (c • Q₀.compMat (diagonal cv)))) :
    tauSOReg (c • Q₀.compMat (diagonal cv)) = tauSOReg Q₀ := by
  classical
  set QF := formF Q₀
  set Q₁ := c • Q₀.compMat (diagonal cv)
  set M : Lat F 2 := Lat.image (gDiag cv hcv) (stdLat F 2)
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_Q₁ hc hQ₀ hcv
  have hm1 : mass (formF Q₁) (stdLat F 2) = mass QF M := by
    rw [show formF Q₁ = Q1F Q₀ (c := c) cv hcv from map_Q₁ Q₀ c cv hcv]
    exact mass_similar QF (coe_ne_zero hc) _ _
  have hm2 := mass_eq_mass_mul_relRatio hpd (stdLat F 2) M (isIntegral_std Q₀)
    (isIntegral_image Q₀ (diagonal cv) _ (gDiag_val_map cv hcv))
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v M.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std M.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v M.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => relRatio (stdStab QF v) (stabB v Q₀ hc cv hcv)
  have hstab : ∀ v, stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v M.1) = stabB v Q₀ hc cv hcv :=
    fun v => by rw [stabB_eq, ← loc_image_gDiag]
  have hR : relRatio (locStab QF (stdLat F 2)) (locStab QF M) = ∏ v ∈ S, r v := by
    rw [relRatio_locStab_eq_prod QF M S hS]
    exact Finset.prod_congr rfl fun v _ => by rw [hstab]
  have hr1 : ∀ v ∉ S, r v = 1 := fun v hv => by
    simp only [r]; rw [← hstab, hS v hv, ← stdStab_eq_stabLat, relRatio_self]
  have hr0 : ∀ v, r v ≠ 0 := fun v => by
    simp only [r]; rw [← hstab, stdStab_eq_stabLat]
    exact (relRatio_pos (commens_stabLat v _ (std_isLattice v) (loc_isLattice v M.2))).ne'
  set w := jac c cv
  have hw : w ≠ 0 := jac_ne_zero hc hcv
  set Φ : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ∏ p : DVR.UpperIdx 2, (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ ord (NF.irreducible_π v) (NF.ι v (wts c cv p))
  have hΦ : ∀ v, Φ v = ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F w)‖⁻¹ :=
    fun v => prod_q_pow_ord_eq v hc hcv
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | w ∈ v.asIdeal}.Finite := Siegel.finite_mem_asIdeal hw
  set S' := S ∪ hTfin.toFinset
  have hΦ1 : ∀ v ∉ S', Φ v = 1 := fun v hv => by
    rw [hΦ, (NumberField.FinitePlace.norm_eq_one_iff_notMem F v w).mpr, inv_one]
    intro h; exact hv (Finset.mem_union_right _ (hTfin.mem_toFinset.mpr h))
  have hr1' : ∀ v ∉ S', r v = 1 := fun v hv => hr1 v (fun h => hv (Finset.mem_union_left _ h))
  have hloc : ∀ v, r v * NF.siegelDensity v Q₁ Q₁ = Φ v * NF.siegelDensity v Q₀ Q₀ := fun v => by
    have := localDensity_mul_relRatio v Q₀ hc cv hcv hQ₀
    simp only [NF.siegelDensity, ite_true]
    linear_combination (1 / 2 : ℝ) * this
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Φ v / r v
  have hg1 : ∀ v ∉ S', g v = 1 := fun v hv => by simp only [g, hΦ1 v hv, hr1' v hv]; norm_num
  have hα : ∀ v, NF.siegelDensity v Q₁ Q₁ = NF.siegelDensity v Q₀ Q₀ * g v := fun v => by
    simp only [g]
    rw [← mul_div_assoc, eq_div_iff (hr0 v)]
    linear_combination hloc v
  have hχ := chiP_eq_of_det_sq hQ₀ (u := c * ∏ a, cv a) (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun a _ => hcv a))
    (Q₂ := Q₁) (by rw [show Q₁.hessian.det = c ^ 2 * (∏ a, cv a) ^ 2 * Q₀.hessian.det from by
      have := det_hessian_Q₁ c Q₀ cv; simpa using this]; ring)
  have hT := regProd_transport hQ₀ hpd S' hg1 hα hχ
  have hSS' : ∏ v ∈ S', r v = ∏ v ∈ S, r v :=
    (Finset.prod_subset Finset.subset_union_left fun v _ hv => hr1 v hv).symm
  have hΦprod : ∏ v ∈ S', Φ v = ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F w)‖ := by
    have hΦt : ∏' v, Φ v = ∏ v ∈ S', Φ v := tprod_eq_prod hΦ1
    rw [← hΦt]
    rw [show Φ = fun v => ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F w)‖⁻¹ from funext hΦ]
    exact tprod_norm_inv hw
  set Nw := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F w)‖
  set R := ∏ v ∈ S, r v
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hr0 v
  have hgS : ∏ v ∈ S', g v = Nw / R := by
    simp only [g]; rw [Finset.prod_div_distrib, hΦprod, hSS']
  have hA : (∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q₁ σ)) * Nw = ∏ σ : F →ₐ[ℚ] ℂ, archVolSO 2 (detGram Q₀ σ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => archVolSO_Q₁ Q₀ hc hcv σ
  rw [tauSOReg_eq _ hQ₁ hpd₁, tauSOReg_eq _ hQ₀ hpd, hm1, hm2, hR]
  unfold tamagawaKReg
  rw [hT, hgS, ← hA]
  field_simp
  ring

/-- **$\tau^{\mathrm{reg}}(c\,(Q'\circ G)) = \tau^{\mathrm{reg}}(Q')$ for every integral $G$ with $\det G\ne0$ and every $c\ne0$** (any number field, no PID,
no `hn2`): the binary regularized analogue of `tauSO_smul_compMat_nf`. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), regularized in rank 2"]
theorem tauSOReg_smul_compMat (Q : QuadForm (𝓞 F) 2) (hQ : Q.Nondegenerate) (hpd : IsTotallyPosDef (formF Q))
    {c : 𝓞 F} (hc : c ≠ 0) (G : Matrix (Fin 2) (Fin 2) (𝓞 F)) (hG : G.det ≠ 0)
    (hpd₁ : IsTotallyPosDef (formF (c • Q.compMat G))) :
    tauSOReg (c • Q.compMat G) = tauSOReg Q := by
  have hQG : (Q.compMat G).Nondegenerate := nondegenerate_compMat_of_det hQ hG
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdG : IsTotallyPosDef (formF (Q.compMat G)) := by
    rw [formF, ← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF
  have e : c • Q.compMat G = c • (Q.compMat G).compMat (diagonal fun _ => (1 : 𝓞 F)) := by
    rw [diagonal_one, compMat_one]
  rw [e] at hpd₁ ⊢
  rw [tauSOReg_smul_compMat_diagonal _ hQG hpdG hc _ (fun _ => one_ne_zero) hpd₁, tauSOReg_compMat Q hQ hpd G hG]

end Scaling

/-! ### 6. Reduction to the diagonal forms $\langle1,D\rangle$ -/

section Reduction

/-- **The representative $\langle1,D\rangle = x^2+Dy^2$** ($=$ the norm form of $\mathcal O_F[\sqrt{-D}]$; $\det H = 4D$). -/
def diagForm1 {A : Type*} [CommRing A] (D : A) : QuadForm A 2 := QuadForm.diag ![1, D]

theorem hessian_diagForm1 {A : Type*} [CommRing A] (D : A) : (diagForm1 D).hessian = !![2, 0; 0, 2 * D] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diagForm1, QuadForm.hessian, QuadForm.diag, Matrix.diagonal]
  <;> ring

theorem hessian_det_diagForm1 {A : Type*} [CommRing A] (D : A) : (diagForm1 D).hessian.det = 4 * D := by
  rw [hessian_diagForm1]; simp [Matrix.det_fin_two]; ring

/-- **The completion of the square:** $\langle1,D\rangle\circ\begin{pmatrix}2a&b\\0&1\end{pmatrix} = 4a\cdot Q$ for $Q = ax^2+bxy+cy^2$,
$D = \det H_Q = 4ac-b^2$. -/
theorem diagForm1_compMat {A : Type*} [CommRing A] (Q : QuadForm A 2) :
    (diagForm1 Q.hessian.det).compMat !![2 * Q.coeff 0 0, Q.coeff 0 1; 0, 1] = (4 * Q.coeff 0 0) • Q := by
  have h10 : Q.coeff 1 0 = 0 := Q.upper (show (0 : Fin 2) < 1 by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compMat_coeff, diagForm1, QuadForm.diag, Matrix.diagonal, QuadForm.eval, QuadForm.evalIn, QuadForm.hessian,
      h10, Matrix.det_fin_two, Fin.sum_univ_two, dotProduct, Matrix.mulVec] <;> ring

variable [IsTotallyReal F]

open scoped ComplexOrder in
/-- A form $S\circ G$ totally positive definite, $\det G\ne0$ over $\mathcal O_F$, forces $S$ to be (the converse of
`isTotallyPosDef_compMat_of_det`). -/
theorem isTotallyPosDef_of_compMat_binary {R : QuadForm (𝓞 F) 2} {G : Matrix (Fin 2) (Fin 2) (𝓞 F)} (hG : G.det ≠ 0)
    (h : IsTotallyPosDef (formF (R.compMat G))) : IsTotallyPosDef (formF R) := by
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  intro x hx
  have h2 : G.map (algebraMap (𝓞 F) F) *ᵥ ((G.map (algebraMap (𝓞 F) F))⁻¹ *ᵥ x) = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hGF), one_mulVec]
  have h1 := h ((G.map (algebraMap (𝓞 F) F))⁻¹ *ᵥ x) (fun h0 => hx (by rw [← h2, h0, mulVec_zero]))
  rwa [formF, ← map_compMat, eval_compMat, ← formF, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit hGF),
    one_mulVec] at h1

open scoped ComplexOrder in
/-- **Reduction of a totally definite binary form to $\langle1,D\rangle$, $D=\det H'$** (completion of the square): the form
$\langle1,D\rangle$ is totally positive definite and $\tau^{\mathrm{reg}}(Q') = \tau^{\mathrm{reg}}(\langle1,\det H'\rangle)$.
*Proof:* $\langle1,D\rangle\circ\begin{pmatrix}2a&b\\0&1\end{pmatrix} = 4a\,Q'$ (`diagForm1_compMat`), then `tauSOReg_compMat` and
`tauSOReg_smul_compMat`. -/
@[kb "weil1982" "§2.4, p. 22 (independent of the choice of lattice), regularized in rank 2"]
theorem tauSOReg_eq_diag {Q' : QuadForm (𝓞 F) 2} (hpd : IsTotallyPosDef (formF Q')) :
    IsTotallyPosDef (formF (diagForm1 Q'.hessian.det)) ∧ tauSOReg Q' = tauSOReg (diagForm1 Q'.hessian.det) := by
  have hQ := nondegenerate_of_isTotallyPosDef hpd
  set a := Q'.coeff 0 0
  have ha : IsTotallyPos (algebraMap (𝓞 F) F a) := by
    have := hpd ![1, 0] (fun h => by simpa using congrFun h 0)
    convert this using 1
    simp [formF, QuadForm.map, QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_two, a]
  have ha0 : a ≠ 0 := by
    rintro h0
    obtain ⟨σ⟩ : Nonempty (F →ₐ[ℚ] ℂ) := Fintype.card_pos_iff.mp card_embeddings_pos
    have := ha σ
    rw [h0, map_zero, map_zero] at this
    exact lt_irrefl _ this
  have h4a : (4 * a : 𝓞 F) ≠ 0 := mul_ne_zero (by norm_num) ha0
  set M : Matrix (Fin 2) (Fin 2) (𝓞 F) := !![2 * a, Q'.coeff 0 1; 0, 1]
  have hM : M.det ≠ 0 := by
    simp only [M, Matrix.det_fin_two_of]; simpa using mul_ne_zero two_ne_zero ha0
  have key : (diagForm1 Q'.hessian.det).compMat M = (4 * a) • Q' := diagForm1_compMat Q'
  have hpd₁ : IsTotallyPosDef (formF ((4 * a) • Q')) := by
    intro x hx
    have e : (formF ((4 * a) • Q')).eval x = algebraMap (𝓞 F) F (4 * a) * (formF Q').eval x := by
      rw [show formF ((4 * a) • Q') = (algebraMap (𝓞 F) F (4 * a)) • formF Q' from by
        ext i j; simp [formF, QuadForm.map]]
      simp only [QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
        Algebra.algebraMap_self, RingHom.id_apply, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [e]
    refine isTotallyPos_mul (fun σ => ?_) (hpd x hx)
    have := ha σ
    simp only [map_mul, map_ofNat]
    exact mul_pos (by norm_num) this
  have hRpd : IsTotallyPosDef (formF (diagForm1 Q'.hessian.det)) :=
    isTotallyPosDef_of_compMat_binary hM (by rw [key]; exact hpd₁)
  have hR : (diagForm1 Q'.hessian.det).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1]; exact mul_ne_zero (by norm_num) hQ
  refine ⟨hRpd, ?_⟩
  have h1 := tauSOReg_compMat _ hR hRpd M hM
  rw [key] at h1
  have h2 := tauSOReg_smul_compMat Q' hQ hpd h4a 1 (by rw [det_one]; exact one_ne_zero) (by rwa [compMat_one])
  rw [compMat_one] at h2
  rw [← h2, h1]

/-- $\tau^{\mathrm{reg}}\langle1,Dt^2\rangle = \tau^{\mathrm{reg}}\langle1,D\rangle$ for $t\ne0$. -/
theorem tauSOReg_diag_mul_sq {D t : 𝓞 F} (hpd : IsTotallyPosDef (formF (diagForm1 D))) (hD : D ≠ 0) (ht : t ≠ 0) :
    IsTotallyPosDef (formF (diagForm1 (D * t ^ 2))) ∧ tauSOReg (diagForm1 (D * t ^ 2)) = tauSOReg (diagForm1 D) := by
  have hR : (diagForm1 D).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1]; exact mul_ne_zero (by norm_num) hD
  set G : Matrix (Fin 2) (Fin 2) (𝓞 F) := !![1, 0; 0, t]
  have hG : G.det ≠ 0 := by simpa [G, Matrix.det_fin_two_of] using ht
  have key : (diagForm1 D).compMat G = diagForm1 (D * t ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [G, compMat_coeff, diagForm1, QuadForm.diag, Matrix.diagonal, QuadForm.eval, QuadForm.evalIn, QuadForm.hessian,
        Fin.sum_univ_two, dotProduct, Matrix.mulVec]
    ring
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  rw [← key]
  exact ⟨by rw [formF, ← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF,
    tauSOReg_compMat _ hR hpd G hG⟩

/-- **$\tau^{\mathrm{reg}}$ depends only on the square class of $\det H'$:** for totally definite binary $Q_1,Q_2$ with
$\det H_2\,u^2 = \det H_1\,w^2$ ($u,w\ne0$), $\tau^{\mathrm{reg}}(Q_1) = \tau^{\mathrm{reg}}(Q_2)$ (any number field, any class number). -/
theorem tauSOReg_eq_of_det {Q₁ Q₂ : QuadForm (𝓞 F) 2} (h₁ : IsTotallyPosDef (formF Q₁)) (h₂ : IsTotallyPosDef (formF Q₂))
    {u w : 𝓞 F} (hu : u ≠ 0) (hw : w ≠ 0) (h : Q₂.hessian.det * u ^ 2 = Q₁.hessian.det * w ^ 2) :
    tauSOReg Q₁ = tauSOReg Q₂ := by
  obtain ⟨p₁, e₁⟩ := tauSOReg_eq_diag h₁
  obtain ⟨p₂, e₂⟩ := tauSOReg_eq_diag h₂
  have hD₁ : Q₁.hessian.det ≠ 0 := nondegenerate_of_isTotallyPosDef h₁
  have hD₂ : Q₂.hessian.det ≠ 0 := nondegenerate_of_isTotallyPosDef h₂
  obtain ⟨-, e₃⟩ := tauSOReg_diag_mul_sq p₂ hD₂ hu
  obtain ⟨-, e₄⟩ := tauSOReg_diag_mul_sq p₁ hD₁ hw
  rw [e₁, e₂, ← e₃, ← e₄, h]

end Reduction

/-! ### 7. The reduction of `BinaryTamagawaTwoReg` to representatives -/

section Interface

variable [IsTotallyReal F]

/-- **Input (the reduced form of `BinaryTamagawaTwoReg`): $\tau^{\mathrm{reg}}\langle1,D\rangle = 2$** for the diagonal forms
$x^2+Dy^2$ ($=$ norm forms of $\mathcal O_F[\sqrt{-D}]$) that are totally positive definite.

Field:
- `tau_eq_two`: `tauSOReg (diagForm1 D) = 2` for every `D : 𝓞 F` with `formF (diagForm1 D)` totally positive definite.

*Status.* Equivalent to `BinaryTamagawaTwoReg F` (`binaryTamagawaTwoReg_iff`), by the regularized change of lattice and rescaling;
this is the smaller statement that needs only one representative per square class of $\det H'$
(`binaryTamagawaTwoReg_of_family`). *Independence:* a statement about binary forms only, as `BinaryTamagawaTwoReg`. -/
@[kb "weil1982" "Thm. 3.7.1 (τ = 2), rank 2 with convergence factors, norm forms [unverified]"]
structure BinaryTamagawaTwoRegDiag (F : Type) [Field F] [NumberField F] : Prop where
  tau_eq_two : ∀ D : 𝓞 F, IsTotallyPosDef (formF (diagForm1 D)) → tauSOReg (diagForm1 D) = 2

/-- **`BinaryTamagawaTwoReg` from the representatives $\langle1,D\rangle$:** $\tau^{\mathrm{reg}}(Q') = \tau^{\mathrm{reg}}\langle1,\det H'\rangle$
(`tauSOReg_eq_diag`). -/
theorem BinaryTamagawaTwoRegDiag.toReg (h : BinaryTamagawaTwoRegDiag F) : BinaryTamagawaTwoReg F :=
  ⟨fun Q' hpd => by
    obtain ⟨hp, e⟩ := tauSOReg_eq_diag hpd
    rw [e]; exact h.tau_eq_two _ hp⟩

theorem BinaryTamagawaTwoReg.toDiag (h : BinaryTamagawaTwoReg F) : BinaryTamagawaTwoRegDiag F :=
  ⟨fun _ hD => h.tau_eq_two _ hD⟩

theorem binaryTamagawaTwoReg_iff : BinaryTamagawaTwoReg F ↔ BinaryTamagawaTwoRegDiag F :=
  ⟨BinaryTamagawaTwoReg.toDiag, BinaryTamagawaTwoRegDiag.toReg⟩

/-- **Reduction to any family of representatives of the square classes of $\det H'$** (e.g. over ℚ the primitive forms of
fundamental discriminant, `PosForms D`; or scaled norm forms): if
$\tau^{\mathrm{reg}}(R) = 2$ for all totally definite $R$ in a
family $\mathcal R$ such that every totally definite binary $Q'$ has some $R\in\mathcal R$ with $\det H_R\,u^2 = \det H_{Q'}\,w^2$ for nonzero
$u,w\in\mathcal O_F$, then `BinaryTamagawaTwoReg F`. -/
theorem binaryTamagawaTwoReg_of_family (𝓡 : Set (QuadForm (𝓞 F) 2))
    (h𝓡 : ∀ R ∈ 𝓡, IsTotallyPosDef (formF R) → tauSOReg R = 2)
    (hcov : ∀ Q' : QuadForm (𝓞 F) 2, IsTotallyPosDef (formF Q') → ∃ R ∈ 𝓡, IsTotallyPosDef (formF R) ∧
      ∃ u w : 𝓞 F, u ≠ 0 ∧ w ≠ 0 ∧ R.hessian.det * u ^ 2 = Q'.hessian.det * w ^ 2) :
    BinaryTamagawaTwoReg F :=
  ⟨fun Q' hpd => by
    obtain ⟨R, hR, hRpd, u, w, hu, hw, h⟩ := hcov Q' hpd
    rw [tauSOReg_eq_of_det hpd hRpd hu hw h]
    exact h𝓡 R hR hRpd⟩

/-- **Siegel's formula in rank 3 from the reduced input:** `TernaryTamagawaTwo`-type hypothesis $\tau(SO(Q_0)) = 2$ and
`BinaryTamagawaTwoRegDiag F` give `SiegelFormulaAt3 Q₀ m` for every totally positive $m$. -/
theorem siegelFormulaAt3_of_diag (Q₀ : QuadForm (𝓞 F) 3) (hpd : IsTotallyPosDef (formF Q₀))
    (hτ : TamagawaNumberTwo Q₀) (h2 : BinaryTamagawaTwoRegDiag F) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) : SiegelFormulaAt3 Q₀ m :=
  siegelFormulaAt3_of_tau Q₀ hpd hτ h2.toReg hm

end Interface

end QuadFormsKB.Tamagawa
