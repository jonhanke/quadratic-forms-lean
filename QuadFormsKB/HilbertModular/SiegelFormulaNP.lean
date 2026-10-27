/-
# Siegel's formula over a totally real field, any class number, $n \ge 6$

**Setting.** $F$ a totally real number field of **any class number**, $Q_0$ a totally positive definite quadratic form over $\mathcal O_F$ in
$n = 2k \ge 6$ variables, $L = \mathcal O_F^n$, its genus classes $\mathrm{cls}(M)$, $|O(M)|$ the full orthogonal group, $r_M(\nu)$
(`latRepF`), $\mathrm{Mass}(L)$.

**Main theorem** (`siegelFormula_nf'`): given the named input `PrincipalPrimeSupply F` (infinitely many rational primes all of whose prime
ideals in $\mathcal O_F$ are principal; Hilbert class field + Chebotarev, `HeckeVanishingNP.lean`), for every totally positive $\nu \in \mathcal O_F$
$$\frac{1}{\mathrm{Mass}(L)}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(\nu)}{|O(M)|} = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu).$$
For $\mathcal O_F$ a PID the input is a theorem (`principalPrimeSupply_of_pid`), recovering `siegelFormula_nf`.

**What changed against the class number one case** (`SiegelFormulaNF.lean`, $h_F = 1$):
1. The genus of $\mathcal O_F^n$ is free for every $F$ (`genusFree_formF`, Steinitz), so the modularity, the cusp-form
property ($\theta_{\mathrm{Gen}} - E_Q \in S_k$), the coefficients of $E_Q$ and `EisHeckeRel` hold for every $F$
(`SteinitzGenus.lean`);
2. Kneser neighbours at **principal** primes stay in the genus for every $F$ (`NeighborsNP.lean`), giving the $T(\pi^2)$ relation of the genus
   average (`HeckeGenusNP.lean`);
3. the vanishing argument uses only the principal primes, hence the input (`eq_zero_of_heckeRel'`).

**Where the class group enters.** Only in step 3: at a non-principal prime $\mathfrak p$ the $\mathfrak p$-neighbour sum of $r_{M'}(\nu)$ involves
$r_{\mathfrak p^{-1}M}(\nu)$, a representation number of the genus of $\mathfrak p^{-1}L$ (Steinitz class $[\mathfrak p]^{-n}$), i.e. another
component of the adelic Hilbert modular form; theta series of single lattices live on one group, and no multi-component form is needed anywhere
else. Removing the input needs either class field theory (the input itself) or the $h_F$-component version of the theta-series and Eisenstein-series results (theta series of the
non-free lattices $\mathfrak a^{-1}\mathcal O_F^n$ and the Eisenstein series of their genera).

Sources: Siegel, Ann. Math. 36 (1935) and 38 (1937) [unverified]; Hanke 2004, (5.3); Kneser 1957; Eichler 1952 [unverified].
-/
import QuadFormsKB.HilbertModular.SiegelFormulaNF
import QuadFormsKB.HilbertModular.SteinitzGenus
import QuadFormsKB.HilbertModular.HeckeGenusNP
import QuadFormsKB.HilbertModular.HeckeVanishingNP

open Matrix NumberField Complex Filter
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "I1" => (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
local notation "ιO" => algebraMap (𝓞 F) F

section Main

variable {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
  (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

/-- $r_{Q_\gamma}(\nu) = r_{\gamma\mathcal O_F^n}(\nu)$. -/
lemma repNumF_gramZ' (γ : GL (Fin n) F)
    (h : IsIntegral (formF Q₀) (latOf γ)) (hpos : IsTotPosGram (gramF (gramZ (formF Q₀) γ h)))
    (ν : 𝓞 F) : repNumF (gramZ (formF Q₀) γ h) ν = latRepF (formF Q₀) (latOf γ) ν := by
  have hL : latOf γ = glImage γ (Nbr.stdLat (𝓞 F) F n) := by rw [latOf, intVec_eq_stdLat]
  rw [hL, latRepF_glImage_eq γ h, latRep_stdLat (fun M => finite_repSetF hpos M)]
  rfl

include hQ hn hlev h𝔑 in
/-- **The $q$-coefficients of $\theta_{\mathrm{Gen}}$**: $a_{\nu_m}(\theta_{\mathrm{Gen}}) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}|O(M)|^{-1}a_{\nu_m}(\theta_M)$,
with $a_\nu(\theta_M) = r_M(\nu)$ for $\nu \in \mathcal O_F$ and $0$ for $\nu \in \mathfrak d^{-1}\setminus\mathcal O_F$ (`latCoeff`). -/
@[kb "siegel1935" "the q-coefficients of θ_Gen are the genus averages r_Gen(ν), over F, any class number [unverified]"]
theorem qCoeff_thetaGen' (m : Fin (Module.finrank ℚ F) → ℤ) :
    qCoeff (thetaGen (formF Q₀) stdLat) (koecherBasis I1) (realVec (QuadFormsKB.Analysis.dualElt I1 m)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * latCoeff (formF Q₀) c.out.1 m := by
  classical
  set C := (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset
  have hfree := genusFree_formF hQ
  have hmod : ∀ c ∈ C, thetaLatt (formF Q₀) c.out.1 ∈
      modularFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k := by
    intro c hc
    have hc' := sameGenus_out (L := stdLat) ((Set.Finite.mem_toFinset _).mp hc)
    exact (thetaLatt_genus hQ hn hlev h𝔑 hc' (hfree _ hc')).1
  rw [thetaGen_eq_sum (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)), Finset.smul_sum]
  simp_rw [smul_smul]
  rw [← dualVec_koecherBasis, qCoeff_sum_smul _ _ (fun c hc => (hmod c hc).1.2.1)
    (fun c hc => isLatticePeriodic_of_mem_modularFormChar (hmod c hc)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [mul_assoc]
  congr 1
  congr 1
  -- the coefficient of one class
  have hc' := sameGenus_out (L := stdLat) ((Set.Finite.mem_toFinset _).mp hc)
  obtain ⟨γ, hγ⟩ := hfree _ hc'
  have hi : IsIntegral (formF Q₀) (latOf γ) := by
    rw [← hγ]; exact SameGenus.isIntegral _ (isIntegral_stdLat Q₀) hc'
  have hpos := isTotPosGram_gramZ hQ γ hi
  have hθ : thetaLatt (formF Q₀) c.out.1 = thetaQ (gramZ (formF Q₀) γ hi) := by
    rw [hγ, thetaLatt_latOf _ γ hi]
  have hper : IsLatticePeriodic (thetaQ (gramZ (formF Q₀) γ hi)) (koecherBasis I1) := by
    rw [← hθ]; exact isLatticePeriodic_of_mem_modularFormChar (hmod c hc)
  rw [hθ, dualVec_koecherBasis, qCoeff_thetaQ hpos hper, thetaCoeffQ, latCoeff]
  split_ifs with h
  · rw [repNumF_gramZ' γ hi hpos, ← hγ]
  · rfl

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} = E$ from cuspidality and the $T(\pi^2)$ relations** (Siegel's formula over $F$, Hecke/Kneser route; $k \ge 3$,
i.e. every even $n \ge 6$, every degree $[F:\mathbb Q]$, **any class number**, given the named input `PrincipalPrimeSupply F`). If $E$ is a function with
$\theta_{\mathrm{Gen}} - E \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$, $E$ satisfies the $T(\pi^2)$ relations with the Eichler eigenvalues (`EisHeckeRel`),
then $\theta_{\mathrm{Gen}} = E$. (Neighbours at principal primes stay in the genus, `NeighborsNP.nbrInGenus'`; the genus is free,
`genusFree_formF`; the vanishing uses `eq_zero_of_heckeRel'`.) -/
@[kb "siegel1935" "θ_Gen = E via Hecke/Kneser over F, any class number, n ≥ 6, given PrincipalPrimeSupply [unverified]"]
theorem thetaGen_eq_of_sub_mem_cuspFormChar' (hPS : PrincipalPrimeSupply F) (hk : 3 ≤ k) {E : (InfinitePlace F → UpperHalfPlane) → ℂ}
    (hcusp : thetaGen (formF Q₀) stdLat - E ∈ cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k)
    (hE : EisHeckeRel Q₀ E) : thetaGen (formF Q₀) stdLat = E := by
  classical
  obtain ⟨mE, hmE, hErel⟩ := hE
  set θ := thetaGen (formF Q₀) stdLat with hθdef
  set b := koecherBasis I1
  have hθ := thetaGen_mem_modularFormChar hQ hn hlev h𝔑 (genusFree_formF hQ)
  have hθhol : IsHolomorphic θ := hθ.1.2.1
  have hθper : IsLatticePeriodic θ b := isLatticePeriodic_of_mem_modularFormChar hθ
  have hghol : IsHolomorphic (θ - E) := hcusp.1.2.1
  have hgper : IsLatticePeriodic (θ - E) b := isLatticePeriodic_of_mem_cuspFormChar hcusp
  have hEeq : E = θ + (-1 : ℂ) • (θ - E) := by funext z; simp
  have hEhol : IsHolomorphic E := by rw [hEeq]; exact hθhol.add (hghol.const_smul _)
  have hEper : IsLatticePeriodic E b := by
    intro m x y hy
    have h1 := hθper m x y hy
    have h2 := hgper m x y hy
    simp only [Pi.sub_apply] at h2
    linear_combination h1 - h2
  -- the bad primes
  set m₀ : ℕ := mE * nm (2 * Q₀.hessian.det) with hm₀def
  have hdet0 : Q₀.hessian.det ≠ 0 := by
    have h := (isTotPosGram_Q₀ hQ)
    intro h0
    have := IsTotallyPosDef.nondegenerate hQ
    apply this
    have e : (formF Q₀).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
      ext i j; simp [QuadForm.hessian, QuadForm.map]
    have e2 : (Q₀.hessian.map (algebraMap (𝓞 F) F)).det = algebraMap (𝓞 F) F Q₀.hessian.det :=
      (RingHom.map_det _ _).symm
    rw [e, e2, h0, map_zero]
  have hm₀ : 0 < m₀ := by
    refine Nat.mul_pos hmE ?_
    rw [Nat.pos_iff_ne_zero, nm, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero two_ne_zero hdet0
  have hgood : ∀ π : 𝓞 F, ¬ π ∣ (m₀ : 𝓞 F) → ¬ π ∣ (mE : 𝓞 F) ∧ ¬ π ∣ 2 ∧ ¬ π ∣ Q₀.hessian.det := by
    intro π hπ
    have h1 : ((nm (2 * Q₀.hessian.det) : ℕ) : 𝓞 F) ∣ (m₀ : 𝓞 F) := by
      rw [hm₀def]; push_cast; exact dvd_mul_left _ _
    have h2 : (mE : 𝓞 F) ∣ (m₀ : 𝓞 F) := by rw [hm₀def]; push_cast; exact dvd_mul_right _ _
    refine ⟨fun h => hπ (h.trans h2), fun h => hπ ?_, fun h => hπ ?_⟩
    · exact ((h.trans (dvd_mul_right _ _)).trans (dvd_nm _)).trans h1
    · exact ((h.trans (dvd_mul_left _ _)).trans (dvd_nm _)).trans h1
  have hsub := eq_zero_of_heckeRel' hPS h𝔑 hk hcusp (lam := fun π => if h : Prime π then heckeEigen Q₀ h else 0)
    hm₀ ?_ ?_
  · exact sub_eq_zero.mp hsub
  · intro π hπ hπm m hu
    obtain ⟨hπE, hπ2, hπd⟩ := hgood π hπm
    obtain ⟨m', hm'⟩ := exists_dualElt_mul (π ^ 2) m
    have hm'' : (π : F) ^ 2 * QuadFormsKB.Analysis.dualElt I1 m = QuadFormsKB.Analysis.dualElt I1 m' := by
      rw [hm']; push_cast; rfl
    rw [hm'', dif_pos hπ, ← dualVec_koecherBasis, ← dualVec_koecherBasis,
      qCoeff_sub hθhol hEhol hθper hEper, qCoeff_sub hθhol hEhol hθper hEper]
    have hEr := hErel π hπ hπE hπ2 hπd m hu
    rw [hm'', ← dualVec_koecherBasis, ← dualVec_koecherBasis] at hEr
    rw [hEr, mul_sub]
    congr 1
    -- the θ part
    rw [dualVec_koecherBasis, dualVec_koecherBasis, qCoeff_thetaGen' hQ hn hlev h𝔑,
      qCoeff_thetaGen' hQ hn hlev h𝔑, mul_left_comm]
    congr 1
    by_cases hint : ∃ ν : 𝓞 F, (ν : F) = QuadFormsKB.Analysis.dualElt I1 m
    · obtain ⟨ν, hν⟩ := hint
      have hνπ : ¬ π ∣ ν := by
        rintro ⟨t, rfl⟩
        obtain ⟨x, y, hx, -, hxy⟩ := hu
        apply hx
        refine ⟨t * y, IsFractionRing.injective (𝓞 F) F ?_⟩
        have h1 : QuadFormsKB.Analysis.dualElt I1 m * algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F x := hxy
        have h2 : algebraMap (𝓞 F) F (π * t) = QuadFormsKB.Analysis.dualElt I1 m := hν
        rw [← h1, ← h2, map_mul, map_mul, map_mul]; ring
      have hν' : algebraMap (𝓞 F) F ν = QuadFormsKB.Analysis.dualElt I1 m := hν
      have hint' : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 m' :=
        ⟨π ^ 2 * ν, by
          show algebraMap (𝓞 F) F (π ^ 2 * ν) = _
          rw [← hm'', ← hν', map_mul, map_pow]⟩
      have hc1 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m = latRepF (formF Q₀) c.out.1 ν := by
        intro c
        have h1 : ∃ ν : 𝓞 F, (ν : F) = QuadFormsKB.Analysis.dualElt I1 m := ⟨ν, hν⟩
        rw [latCoeff, dif_pos h1]
        congr 2
        exact IsFractionRing.injective (𝓞 F) F (h1.choose_spec.trans hν.symm)
      have hc2 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m' =
          latRepF (formF Q₀) c.out.1 (π ^ 2 * ν) := by
        intro c
        rw [latCoeff, dif_pos hint']
        congr 2
        apply IsFractionRing.injective (𝓞 F) F
        have h3 : algebraMap (𝓞 F) F hint'.choose = QuadFormsKB.Analysis.dualElt I1 m' := hint'.choose_spec
        rw [h3, ← hm'', ← hν', map_mul, map_pow]
      simp_rw [hc1, hc2]
      exact NP.genus_sum_latRepF_sq' hQ hπ hπ2 hπd (by rw [hn]; exact even_two_mul k)
        (by omega) hνπ
    · have hc1 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m = 0 := fun c => by
        rw [latCoeff, dif_neg hint]
      have hint' : ¬ ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 m' := by
        rintro ⟨ν', hν'⟩
        exact hint (mem_int_of_sq_mul' hπ hu (hν'.trans hm''.symm))
      have hc2 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m' = 0 := fun c => by
        rw [latCoeff, dif_neg hint']
      simp [hc1, hc2]
  · intro π hπ _
    simp only [dif_pos hπ]
    exact norm_heckeEigen_ge hn (by omega) hπ


include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} = E_Q$ for every totally real $F$, $n \ge 6$** (given `PrincipalPrimeSupply F`). -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E_Q over F, n ≥ 6, any class number (given PrincipalPrimeSupply) [unverified]"]
theorem thetaGen_eq_eisQ' (hPS : PrincipalPrimeSupply F) (hk : 3 ≤ k) :
    thetaGen (formF Q₀) stdLat = eisQ Q₀ k :=
  thetaGen_eq_of_sub_mem_cuspFormChar' hQ hn hlev h𝔑 hPS hk
    (thetaGen_sub_eisQ_mem_cuspFormChar' hQ hn hlev h𝔑 hk) (eisHeckeRel_eisQ' hQ hn hlev h𝔑 hk)

include hQ hn hlev h𝔑 in
/-- **The coefficients of $E_Q$ are the genus averages**, every totally real $F$, $n \ge 6$ (given `PrincipalPrimeSupply F`). -/
@[kb "siegel1935" "r_Gen(ν) = ν-th coefficient of E_Q, over F, any class number (given PrincipalPrimeSupply) [unverified]"]
theorem qCoeff_eisQ_eq_genus_avg' (hPS : PrincipalPrimeSupply F) (hk : 3 ≤ k) (ν : 𝓞 F) :
    qCoeff (eisQ Q₀ k) (koecherBasis I1) (realVec (ν : F)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  classical
  rw [← thetaGen_eq_eisQ' hQ hn hlev h𝔑 hPS hk, ← dualElt_mOf ν, qCoeff_thetaGen' hQ hn hlev h𝔑]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 (mOf ν) := ⟨ν, (dualElt_mOf ν).symm⟩
  rw [latCoeff, dif_pos h1]
  congr 3
  exact IsFractionRing.injective (𝓞 F) F (h1.choose_spec.trans (dualElt_mOf ν))

end Main

/-- **Siegel's formula over a totally real field of any class number, $n \ge 6$** (Siegel's Hauptsatz in degree one; conditional only on the
named input `PrincipalPrimeSupply F`, a theorem of class field theory, and unconditional for $h_F = 1$ via `principalPrimeSupply_of_pid`).
For $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k \ge 6$ variables and $\nu \in \mathcal O_F$ totally positive,
$$\mathrm{Mass}(\mathcal O_F^n)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{r_M(\nu)}{|O(M)|}
  = |d_F|^{-(n-1)/2}\,\beta_\infty(\nu)\prod_\mathfrak p\beta_\mathfrak p(\nu)\quad(= |d_F|^{-(n-1)/2}\,\texttt{aENF}\ Q_0\ \nu),$$
classes with the full orthogonal group $O(M)$ (proper and improper isometries), $\beta_\mathfrak p$ = `LocalDensity.NF.localDensity`
($\operatorname{Vol}(\mathfrak o_\mathfrak p) = 1$). -/
@[kb "siegel1935" "Hauptsatz over a totally real F, any class number, n ≥ 6 (given PrincipalPrimeSupply) [unverified]"]
theorem siegelFormula_nf' (hPS : PrincipalPrimeSupply F) {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
    (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have h1 := qCoeff_eisQ_eq_genus_avg' hQ hn hlev h𝔑 hPS hk ν
  have h2 := eisQ_coeff_eq_discr_mul_aENF' hQ hn hlev h𝔑 hk hν
  have h3 := h1.symm.trans h2
  apply Complex.ofReal_injective
  rw [← h3]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [div_eq_inv_mul]

/-- **Siegel's formula over $F$ with the `repMass`**, any class number, $n \ge 6$ (given `PrincipalPrimeSupply F`). -/
@[kb "siegel1935" "Hauptsatz over F (repMass form), any class number, n ≥ 6 (given PrincipalPrimeSupply) [unverified]"]
theorem siegelFormula_nf_repMass' (hPS : PrincipalPrimeSupply F) {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    QuadFormsKB.Tamagawa.repMass (formF Q₀) stdLat (ιO ν) =
      mass (formF Q₀) stdLat * ((Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν) := by
  have hm : 0 < mass (formF Q₀) stdLat := mass_pos hQ stdLat (isIntegral_stdLat Q₀)
  rw [← siegelFormula_nf' hPS hQ hn hk hν, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul,
    QuadFormsKB.Tamagawa.repMass, finsum_mem_eq_finite_toFinset_sum _
      (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 2
  conv_lhs => rw [← Quotient.out_eq c]
  rfl

/-- **The input `SiegelFormulaAt` is a theorem for every totally real $F$** ($n = 2k \ge 6$, $m \gg 0$), given
`PrincipalPrimeSupply F`. -/
@[kb "siegel1935" "Hauptsatz over F: The SiegelFormulaAt, any class number, n ≥ 6 (given PrincipalPrimeSupply) [unverified]"]
theorem siegelFormulaAt' (hPS : PrincipalPrimeSupply F) {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
    (hn : n = 2 * k) (hk : 3 ≤ k) {m : 𝓞 F} (hm : ∀ v, 0 < realEmb F v (ιO m)) :
    QuadFormsKB.Tamagawa.SiegelFormulaAt Q₀ m := by
  refine ⟨?_⟩
  rw [siegelProduct_eq_discr_mul_aENF (isTotPosGram_Q₀ hQ) (by omega) hm]
  exact siegelFormula_nf_repMass' hPS hQ hn hk hm

/-- **Consistency check**: for $\mathcal O_F$ a PID, `siegelFormula_nf'` with the input discharged by `principalPrimeSupply_of_pid` is
`siegelFormula_nf`'s statement. -/
theorem siegelFormula_nf_of_pid' [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n}
    (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ} (hn : n = 2 * k)
    (hk : 3 ≤ k) {ν : 𝓞 F} (hν : ∀ v, 0 < realEmb F v (ιO ν)) :
    (mass (formF Q₀) stdLat)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          (latRepF (formF Q₀) c.out.1 ν : ℝ) / (LatClass.autCard (formF Q₀) c : ℝ) =
      (Real.sqrt |(discr F : ℝ)|)⁻¹ ^ (n - 1) * QuadFormsKB.Siegel.aENF Q₀ ν :=
  siegelFormula_nf' (principalPrimeSupply_of_pid F) hQ hn hk hν

end QuadFormsKB.HilbertModular

end
