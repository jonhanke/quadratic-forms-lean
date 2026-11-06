/-
# Hanke 2011, Corollary 6.3 for every lattice over a totally real field

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, Theorem 6.2 and Corollary 6.3, pp. 25–26.

For $F$ totally real, $Q_0$ totally positive definite over $\mathcal O_F$ in $n \ge 3$ variables and **any** $\mathcal O_F$-valued
lattice $L$ on $(F^n, Q_0)$ (any Steinitz class), with $S = \det_H(L)$ and local genera $G_{\mathfrak p}$ of $L_{\mathfrak p}$:
$$\mathrm{Mass}(L) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}
\cdot\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$$
(`mass_eq_local`), from the repository's mass formula for arbitrary lattices (`Tamagawa.LatChange.massFormula_lat_nf`,
`Tamagawa.LatChange.tamagawaKLat_eq_local_gen`) and the product formula. `normAssoc S` $= N_{F/\mathbb Q}(I(S))$.
-/
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist
import QuadFormsKB.Literature.Hanke2011Structure.RationalLocalTuples
import QuadFormsKB.Tamagawa.LatticeLocalGenNF
import QuadFormsKB.Tamagawa.LocalZeta

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The norm of the associated ideal** $N_{F/\mathbb Q}(I(S)) = \prod_{\mathfrak p}N(\mathfrak p)^{\operatorname{ord}_{\mathfrak p}(S)}$ (Definition 2.4). -/
@[kb "hanke2011structure" "Def. 2.4, p. 8 (N(I(S)))"]
def normAssoc (S : AdelicSqCl F) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S

/-- $\|x\|_{\mathfrak p} = N(\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}(x)}$ for a representative $x$ of $S_{\mathfrak p}$. -/
theorem norm_eq_of_comp (v : HeightOneSpectrum (𝓞 F)) (S : AdelicSqCl F) {x : (v.adicCompletion F)ˣ}
    (hx : AdelicSqCl.comp v S = SqCl.mk x) :
    ‖(x : v.adicCompletion F)‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ := by
  rw [LocalZeta.norm_eq_absNorm_pow v x.ne_zero, adelicOrd, hx, SqCl.ordZ_mk, ← _root_.zpow_neg]
  congr 1
  change WithZero.log (Valued.v (x : v.adicCompletion F)) = -(-WithZero.log (Valued.v (x : v.adicCompletion F)))
  ring

section Local

variable (v : HeightOneSpectrum (𝓞 F))

/-- The local genus of $L_{\mathfrak p} = \mathcal O_{\mathfrak p}^n$ is the class of $Q_0$ over $\mathcal O_{\mathfrak p}$, with density
`localBeta`. -/
theorem beta_locGenusOf_of_std (Q₀ : QuadForm (𝓞 F) n) (L : Lat F n) (hL : IsIntegral (formF Q₀) L.1)
    (hv : loc v L.1 = std v) : (locGenusOf v (formF Q₀) L hL).beta = localBeta v Q₀ := by
  have h1 : loc v L.1 = locAct v 1 (std v) := by rw [locAct_one]; exact hv
  rw [locGenusOf_eq v _ L hL h1, LocGenus.beta_mk, betaForm]
  have e : QuadForm.toO v (localForm (formF Q₀) v 1) (localForm_coeff_integral v _ L hL h1) = LocalDensity.NF.Qp v Q₀ := by
    apply QuadForm.map_injective_O v
    simp only
    rw [QuadForm.map_toO, localForm, Units.val_one, QuadForm.compMat_one, Tamagawa.map_Qp_eq]
  rw [e]
  rfl

/-- **The local density of a local genus in Gram coordinates**: $\beta_{G,\mathfrak p} = |2|^{n(n-1)/2}\cdot\tfrac12\beta_{\mathrm{coeff}}(T,T)$
for the representative $T$ of $L_{\mathfrak p}$ in the basis `locBasis`. -/
theorem beta_locGenusOf_eq (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral Q L.1) :
    (locGenusOf v Q L hL).beta = ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) *
      ((1 / 2 : ℝ) * LocalDensity.DVR.localDensityForm
        (QuadForm.toO v (localForm Q v (locBasis v L)) (localForm_coeff_integral v Q L hL (locBasis_spec v L)))
        (QuadForm.toO v (localForm Q v (locBasis v L)) (localForm_coeff_integral v Q L hL (locBasis_spec v L)))
        (LocalDensity.NF.π v)) := by
  have hnd := (det_locGenusOf v Q hQ L hL).1
  unfold locGenusOf at hnd ⊢
  rw [LocGenus.nondeg_mk] at hnd
  rw [LocGenus.beta_mk, betaForm, Hanke2005.hankeBeta_std_hessian v _ hnd]
  unfold LocalDensity.DVR.siegelDensity
  rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]

end Local


section Main

variable [IsTotallyReal F]

/-- The local factor $\|2\|_{\mathfrak p}^{-k}\|\det P_{\mathfrak p}\|^{n+1}$ is $1$ at almost every prime. -/
theorem finite_mulSupport_detFactor (L : Lat F n) (k : ℕ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(locBasis v L).val.det‖ ^ (n + 1)).Finite := by
  have h2 := (Hanke2005.hasFiniteMulSupport_norm_two (F := F))
  have hL : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  refine (h2.union hL).subset fun v hv => ?_
  by_contra hn
  simp only [Set.mem_union, Function.mem_mulSupport, Set.mem_ofPred_eq, not_or, not_not] at hn
  apply hv
  have hstd : locAct v (locBasis v L) (std v) = std v := by rw [← locBasis_spec]; exact hn.2
  obtain ⟨P₀, hP₀⟩ := exists_gl_o_of_locAct_eq v hstd
  have hdet : ‖(locBasis v L).val.det‖ = 1 := by
    rw [← hP₀]
    show ‖(P₀.val.map (algebraMap _ (v.adicCompletion F))).det‖ = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Tamagawa.norm_coe_unit v (P₀.isUnit.map Matrix.detMonoidHom)
  show (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(locBasis v L).val.det‖ ^ (n + 1) = 1
  rw [hn.1, hdet, one_pow, one_pow, inv_one, one_mul]


/-- The local densities of the local genera of $L$ are multipliable ($n \ge 3$): they agree with those of
$\mathcal O_F^n$ at almost every prime. -/
theorem multipliable_beta_locGenusOf (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (L : Lat F n)
    (hL : IsIntegral (formF Q₀) L.1) : Multipliable fun v => (locGenusOf v (formF Q₀) L hL).beta := by
  classical
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => localBeta v Q₀ with hg
  have hgform : ∀ v, g v = ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) *
      LocalDensity.NF.siegelDensity v Q₀ Q₀ := fun v => Hanke2005.hankeBeta_gramV v Q₀ hQ₀
  have hgpos : ∀ v, 0 < g v := fun v => by
    rw [hgform]
    have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
    exact mul_pos (pow_pos h2 _) (Tamagawa.siegelDensity_pos v Q₀ hQ₀)
  have hgm : Multipliable g := by
    have hm2 : Multipliable fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) :=
      multipliable_of_hasFiniteMulSupport (Hanke2005.hasFiniteMulSupport_norm_two.pow _)
    have hms := Tamagawa.multipliable_siegelDensity (by omega) (by omega) Q₀ hQ₀
    have : g = fun v => ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) * LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
      funext hgform
    rw [this]; exact hm2.mul hms
  have hev : ∀ᶠ v in Filter.cofinite, (locGenusOf v (formF Q₀) L hL).beta = g v := by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact beta_locGenusOf_of_std v Q₀ L hL hv
  have hratio : Multipliable fun v => (locGenusOf v (formF Q₀) L hL).beta / g v := by
    refine multipliable_of_hasFiniteMulSupport ?_
    refine (Filter.eventually_cofinite.mp hev).subset fun v hv => ?_
    intro he
    apply hv
    show (locGenusOf v (formF Q₀) L hL).beta / g v = 1
    rw [he, div_self (hgpos v).ne']
  have e : (fun v => (locGenusOf v (formF Q₀) L hL).beta) =
      fun v => g v * ((locGenusOf v (formF Q₀) L hL).beta / g v) := by
    funext v; field_simp [(hgpos v).ne']
  rw [e]
  exact hgm.mul hratio


/-- **Corollary 6.3 for one genus, every lattice** (totally real $F$, $Q_0$ totally positive definite, $n \ge 3$, $L$ any
$\mathcal O_F$-valued lattice on $(F^n, Q_0)$, $S = \det_H(L)$):
$$\mathrm{Mass}(L) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}
\cdot\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1},$$
$G_{\mathfrak p}$ the local genus of $L_{\mathfrak p}$. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (one genus, every lattice); Thm. 6.2, proof, p. 26"]
theorem mass_eq_local (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral (formF Q₀) L.1) :
    mass (formF Q₀) L = |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
      normAssoc (detH (formF Q₀) hQ L) ^ (((n : ℝ) + 1) / 2) /
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) *
      (∏' v, (locGenusOf v (formF Q₀) L hL).beta)⁻¹ := by
  classical
  have hQ₀ : Q₀.Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  set d := Module.finrank ℚ F with hd
  set k := n * (n - 1) / 2 with hk
  set S := detH (formF Q₀) hQ L with hSdef
  set D : F := (formF Q₀).hessian.det with hD
  set P : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F) := fun v => locBasis v L with hP
  set T : ∀ v : HeightOneSpectrum (𝓞 F), QuadForm (v.adicCompletionIntegers F) n := fun v =>
    QuadForm.toO v (localForm (formF Q₀) v (P v)) (localForm_coeff_integral v _ L hL (locBasis_spec v L)) with hTdef
  have hT : ∀ v, (T v).map (algebraMap _ (v.adicCompletion F)) =
      ((LocalDensity.NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).compMat (P v).val := by
    intro v; simp only [hTdef]; rw [QuadForm.map_toO, Tamagawa.map_Qp_eq]; rfl
  have h1 := Tamagawa.LatChange.tamagawaKLat_eq_local_gen (by omega) (by omega) Q₀ hQ₀ L P T hT
    (fun v => locBasis_spec v L)
  have h2 := Tamagawa.LatChange.massFormula_lat_nf Q₀ hQ₀ (by omega) hpd
    (Tamagawa.tamagawaNumberTwo_totallyReal hn Q₀ hpd) L hL
  -- the local factors in the paper's normalization
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (locGenusOf v (formF Q₀) L hL).beta with hβ
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(P v).val.det‖ ^ (n + 1)
    with ha
  have hfac : ∀ v, (1 / 2 : ℝ) * LocalDensity.DVR.localDensityForm (T v) (T v) (LocalDensity.NF.π v) *
      ‖(P v).val.det‖ ^ (n + 1) = β v * a v := by
    intro v
    have hb := beta_locGenusOf_eq v (formF Q₀) hQ L hL
    have h2v : (‖(2 : v.adicCompletion F)‖ ^ k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr two_ne_zero)
    simp only [hβ, ha, hb]
    field_simp
    ring
  simp_rw [hfac] at h1
  have hβm := multipliable_beta_locGenusOf hn Q₀ hQ₀ L hL
  have ham : Multipliable a := multipliable_of_hasFiniteMulSupport (finite_mulSupport_detFactor L k)
  rw [hβm.tprod_mul ham] at h1
  -- the finite product `∏ a`
  have hX : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ := Finset.prod_pos fun σ _ =>
    norm_pos_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hQ)
  set X := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ with hXdef
  have hnormD : ∀ v : HeightOneSpectrum (𝓞 F), 0 < ‖algebraMap F (v.adicCompletion F) D‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hQ)
  -- `‖D‖ ‖det P‖² = N(𝔭)^{-ord}`
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) D‖ * ‖(P v).val.det‖ ^ 2 =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ := by
    intro v
    have hc := detH_comp (formF Q₀) hQ L v (locBasis_spec v L)
    rw [← norm_eq_of_comp v S hc, localHessDet, Units.val_mk0, norm_mul, norm_pow]
  -- a finite set outside of which everything is trivial
  have hfinD : {v : HeightOneSpectrum (𝓞 F) | ‖algebraMap F (v.adicCompletion F) D‖ ≠ 1}.Finite := by
    have := (Tamagawa.finite_valuation_ne_one hQ)
    refine this.subset fun v hv => ?_
    intro h
    apply hv
    exact Tamagawa.norm_algebraMap_eq_one' h
  have hfin2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖).Finite :=
    Hanke2005.hasFiniteMulSupport_norm_two (F := F)
  set T₀ : Finset (HeightOneSpectrum (𝓞 F)) :=
    (finite_mulSupport_detFactor L k).toFinset ∪ hfinD.toFinset ∪ (supp_finite S).toFinset ∪ hfin2.toFinset
    with hT₀
  have hout : ∀ v ∉ T₀, a v = 1 ∧ ‖algebraMap F (v.adicCompletion F) D‖ = 1 ∧ adelicOrd v S = 0 ∧
      ‖(2 : v.adicCompletion F)‖ = 1 := by
    intro v hv
    simp only [hT₀, Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h1
    · simpa using h2
    · simpa [supp] using h3
    · simpa using h4
  have hA : ∏' v, a v = ∏ v ∈ T₀, a v := by
    rw [tprod_eq_finprod (L := SummationFilter.unconditional _) (finite_mulSupport_detFactor L k)]
    exact Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).1
  have hNS : normAssoc S = ∏ v ∈ T₀, (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S := by
    unfold normAssoc
    exact Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => by rw [(hout v hv).2.2.1, zpow_zero]
  have hXT : ∏ v ∈ T₀, ‖algebraMap F (v.adicCompletion F) D‖ = X⁻¹ := by
    rw [← Tamagawa.finprod_norm_eq D hQ]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.1).symm
  have h2T : ∏ v ∈ T₀, ‖(2 : v.adicCompletion F)‖ = ((2 : ℝ) ^ d)⁻¹ := by
    rw [← Hanke2005.tprod_norm_two, tprod_eq_finprod (L := SummationFilter.unconditional _) hfin2]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.2.2).symm
  -- the finite product
  have e : ((n : ℝ) + 1) / 2 = (((n : ℝ) + 1) / 2) := rfl
  have hdetP : ∀ v : HeightOneSpectrum (𝓞 F), ‖(P v).val.det‖ ^ (n + 1) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖) ^
        (((n : ℝ) + 1) / 2) := by
    intro v
    have h := hloc v
    have hsq : ‖(P v).val.det‖ ^ 2 =
        ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖ := by
      rw [← h]; field_simp [(hnormD v).ne']
    rw [← hsq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  have hprodA : ∏ v ∈ T₀, a v = (2 : ℝ) ^ (d * k) * (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) := by
    simp only [ha, Finset.prod_mul_distrib, hdetP]
    rw [Finset.prod_inv_distrib, Finset.prod_pow, h2T, Real.finsetProd_rpow _ _ (fun v _ =>
        div_nonneg (inv_nonneg.mpr (zpow_nonneg (Nat.cast_nonneg _) _)) (norm_nonneg _)),
      Finset.prod_div_distrib, Finset.prod_inv_distrib, ← hNS, hXT, inv_pow, inv_inv, ← pow_mul]
    congr 1
    rw [div_inv_eq_mul, inv_mul_eq_div]
  -- the archimedean product
  have hDcast : algebraMap (𝓞 F) F Q₀.hessian.det = D := by
    rw [hD, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hgram : ∀ σ : F →ₐ[ℚ] ℂ, Tamagawa.detGram Q₀ σ = ‖σ D‖ / 2 ^ n := by
    intro σ
    unfold Tamagawa.detGram
    rw [hDcast, map_div₀, map_pow, map_ofNat, norm_div, norm_pow, Complex.norm_two]
  have harch : ∏ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO n (Tamagawa.detGram Q₀ σ) =
      (X / (2 : ℝ) ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) * (volV n / 2 ^ k) ^ d := by
    simp only [hgram]
    have hav : ∀ σ : F →ₐ[ℚ] ℂ, Tamagawa.archVolSO n (‖σ D‖ / 2 ^ n) =
        (‖σ D‖ / 2 ^ n) ^ (-((n : ℝ) + 1) / 2) * Tamagawa.archVolSO n 1 :=
      fun σ => Hanke2005.archVolSO_eq_rpow_mul n _
    rw [Finset.prod_congr rfl (fun σ _ => hav σ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      AlgHom.card]
    rw [Real.finsetProd_rpow _ _ (fun σ _ => div_nonneg (norm_nonneg _) (by positivity)), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, AlgHom.card, ← pow_mul, mul_comm n d, ← hXdef]
    congr 1
    rw [volV_eq_tauR, Hanke2005.tauR_eq_two_pow_mul_archVolSO, ← hk,
      mul_div_cancel_left₀ _ (by positivity : (2 : ℝ) ^ k ≠ 0)]
  -- assemble
  rw [h2, h1, hA, hprodA, harch]
  have hNSpos : 0 < normAssoc S := by
    rw [hNS]
    exact Finset.prod_pos fun v _ =>
      zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))) _
  have hV : 0 < volV n := by rw [volV_eq_tauR]; exact Hanke2005.tauR_pos n
  have hΔ : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have h2nd : (0 : ℝ) < 2 ^ (n * d) := by positivity
  have e1 : ((2 : ℝ) ^ (n * d)) ^ (((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have e2 : (X / (2 : ℝ) ^ (n * d)) ^ (-((n : ℝ) + 1) / 2) = ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) /
      X ^ (((n : ℝ) + 1) / 2) := by
    rw [show -((n : ℝ) + 1) / 2 = -(((n : ℝ) + 1) / 2) by ring, Real.rpow_neg (by positivity),
      Real.div_rpow hX.le h2nd.le, e1, inv_div]
  have e3 : (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) = X ^ (((n : ℝ) + 1) / 2) / normAssoc S ^ (((n : ℝ) + 1) / 2) :=
    Real.div_rpow hX.le hNSpos.le _
  have e4 : |(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) = (|(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4))⁻¹ :=
    Real.rpow_neg hΔ.le _
  rw [e2, e3, e4]
  have hXp : 0 < X ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hX _
  have hNp : 0 < normAssoc S ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hNSpos _
  have h2p : 0 < ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
  have hΔp : 0 < |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) := Real.rpow_pos_of_pos hΔ _
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_pow, ← pow_mul, mul_comm k d]
  field_simp
  ring

end Main

end

end QuadFormsKB.Hanke2011Structure
