/-
# Siegel's formula over a totally real field by the Hecke/Kneser route: $\theta_{\mathrm{Gen}} = E_Q$

**Setting.** $F$ totally real with $\mathcal O_F$ a PID, $Q_0$ a totally positive definite form over $\mathcal O_F$ in $n = 2k$ variables,
$\mathfrak N \ne 0$ a theta level (`IsThetaLevelF`), $\chi_Q$ its character, $\theta_{\mathrm{Gen}}$ the genus theta series (`SteinitzGenus.lean`; the classes,
weights $1/|O(M)|$), $a_\nu$ = `qCoeff · (koecherBasis 1) (realVec ν)` the $q$-coefficients ($\nu \in \mathfrak d^{-1}$).

**Main theorems.**
* `thetaGen_eq_of_sub_mem_cuspFormChar` (any $k \ge 2$): if $E$ is a function with $\theta_{\mathrm{Gen}} - E \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$ whose
  coefficients satisfy the $T(\pi^2)$ relations with the Eichler eigenvalue (`EisHeckeRel Q₀ E`), then $\theta_{\mathrm{Gen}} = E$.
* **`thetaGen_eq_eisQ`** ($n \ge 6$): $\theta_{\mathrm{Gen}} = E_Q$ for the Eisenstein series $E_Q$ (`eisQ`), with
  $\theta_{\mathrm{Gen}} - E_Q \in S_k$ from `thetaGen_sub_eisQ_mem_cuspFormChar_of_pid`).
* `thetaGen_eq_of_wt2` ($n = 4$): the same with $\theta_{\mathrm{Gen}} - E \in S_2$ as the named hypothesis `ThetaGenSubCusp2`, to be
  discharged by the weight-2 Eisenstein series (`Cuspidal2.lean`).
* **`qCoeff_eisQ_eq_genus_avg`** (coefficients): $a_\nu(E_Q) = r_{\mathrm{Gen}}(\nu) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}r_M(\nu)/|O(M)|$
  for $\nu \in \mathcal O_F$.

**Proof.** $g = \theta_{\mathrm{Gen}} - E$ is a cusp form. For a good prime $\pi \nmid 2\det H\cdot m_E$ and $\nu \in \mathfrak d^{-1}$ a unit at $\pi$,
$a_{\pi^2\nu}(\theta_{\mathrm{Gen}}) = \lambda_\pi a_\nu(\theta_{\mathrm{Gen}})$: for $\nu \in \mathcal O_F$ this is the genus-averaged Kneser relation
(`genus_sum_latRepF_sq_of_pid`: Kneser neighbours, which stay in the genus by `nbrInGenus_of_pid`; with
$a_\nu(\theta_M) = r_M(\nu)$, `qCoeff_thetaQ`); for $\nu \notin \mathcal O_F$ both sides vanish. The same relation for $E$
is `EisHeckeRel`. So $a(g)$ satisfies it, with $|\lambda_\pi| = |q^{n-2} + \chi_\pi q^{k-1} + 1| \ge \frac12q^{n-2}$, and `eq_zero_of_heckeRel`
(the vanishing argument for every even $n \ge 4$ and every degree $d$) gives $g = 0$.

**Inputs (named, none equivalent to the conclusion).** (That Kneser neighbours stay in the genus is *proved*:
`nbrInGenus_of_pid`, via the classification of unimodular forms over $\mathfrak o_\mathfrak p$.)
* `EisHeckeRel Q₀ E`: the $T(\pi^2)$ relations for the coefficients of $E$ (the local-density formula
  $a_\nu(E_Q) = c_\infty N(\nu)^{k-1}\prod_\mathfrak q\beta_\mathfrak q(\nu)$ gives them prime by prime; not equivalent to $\theta_{\mathrm{Gen}} = E$).
* `ThetaGenSubCusp2` ($n = 4$ only): $\theta_{\mathrm{Gen}} - E \in S_2$ (`Cuspidal2.lean`).

**Status.** Both are now theorems for every $E$ used, so they are hypotheses on the arbitrary $E$ of the generic lemmas
only (as conditions): `EisHeckeRel` for $E_Q$ is `eisHeckeRel_eisQ'` / `eisHeckeRel_eisQ_of_pid` ($n \ge 6$)
and `eisHeckeRel_eisQ2'` / `eisHeckeRel_eisQ2_of_pid` ($n = 4$, $d \ge 2$), from the explicit coefficients and a local identity at $\pi$
(`aENF_mul_pi_sq`); `ThetaGenSubCusp2` for $E_Q$ is `thetaGenSubCusp2_eisQ2'`. The unconditional forms of this file's $E_Q$ statements are
`thetaGen_eq_eisQ_of_pid`, `qCoeff_eisQ_eq_genus_avg_of_pid` (`SiegelFormulaNF.lean`) and `thetaGen_eq_eisQ2_of_pid`,
`qCoeff_eisQ2_eq_genus_avg_of_pid` (`SiegelFormulaNF4.lean`).

Over $\mathbb Q$: `Siegel.GenusEis.siegelFormula_quaternary`, the template.
-/
import QuadFormsKB.HilbertModular.HeckeGenusLocal
import QuadFormsKB.HilbertModular.HeckeTheta
import QuadFormsKB.HilbertModular.Cuspidal

open Matrix NumberField Complex Filter
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

open QuadFormsKB.Lattices QuadFormsKB.Lattices.Nbr

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

local notation "I1" => (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-! ### The inputs -/

/-- **The $T(\pi^2)$ relations for a function $E$ with the eigenvalues of $\theta_{\mathrm{Gen}}(Q_0)$**: there is $m_E \ge 1$ such that for
every prime $\pi \nmid 2m_E\det H(Q_0)$ and every $\nu \in \mathfrak d^{-1}$ (`dualElt 1 m`) that is a unit at $\pi$ (`IsUnitAt`),
$$a_{\pi^2\nu}(E) = \lambda_\pi\,a_\nu(E),\qquad \lambda_\pi = q^{n-2} + \chi_\pi q^{n/2-1} + 1\ (\text{`heckeEigen`}).$$
For $E = E_Q$ this follows from the Siegel–Weil coefficient formula $a_\nu(E_Q) = c\,N(\nu)^{k-1}\prod_\mathfrak q\beta_\mathfrak q(\nu)$ and the
good-prime densities ($\beta_\mathfrak q(\pi^2\nu) = \beta_\mathfrak q(\nu)$ for $\mathfrak q \ne (\pi)$, and Hanke 2004, Table 2 / (5.8)
at $\pi$). Parameters: `Q₀` (gives $\lambda_\pi$), `E` (the function). -/
@[kb "siegel1935" "T(𝔭²) relations for the Eisenstein coefficients (input) [unverified]"]
def EisHeckeRel (Q₀ : QuadForm (𝓞 F) n) (E : (InfinitePlace F → UpperHalfPlane) → ℂ) : Prop :=
  ∃ mE : ℕ, 0 < mE ∧ ∀ (π : 𝓞 F) (hπ : Prime π), ¬ π ∣ (mE : 𝓞 F) → ¬ π ∣ 2 → ¬ π ∣ Q₀.hessian.det →
    ∀ m : Fin (Module.finrank ℚ F) → ℤ, IsUnitAt π (QuadFormsKB.Analysis.dualElt I1 m) →
      qCoeff E (koecherBasis I1) (realVec ((π : F) ^ 2 * QuadFormsKB.Analysis.dualElt I1 m)) =
        heckeEigen Q₀ hπ * qCoeff E (koecherBasis I1) (realVec (QuadFormsKB.Analysis.dualElt I1 m))

/-- **$\theta_{\mathrm{Gen}} - E$ is a weight-2 cusp form** (the $n = 4$ input, to be discharged by `Cuspidal2.lean`). Parameters: `Q₀`, `E`, `𝔑`, `χ`. -/
@[kb "siegel1935" "θ_Gen − E ∈ S₂ (input for n = 4) [unverified]"]
def ThetaGenSubCusp2 (Q₀ : QuadForm (𝓞 F) n) (E : (InfinitePlace F → UpperHalfPlane) → ℂ) (𝔑 : Ideal (𝓞 F))
    (χ : MulChar (𝓞 F ⧸ 𝔑) ℂ) : Prop :=
  thetaGen (formF Q₀) stdLat - E ∈ cuspFormChar 𝔑 χ 2

/-! ### Auxiliary facts -/

lemma isLatticePeriodic_of_mem_modularFormChar {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ}
    {k : ℤ} {f : (InfinitePlace F → UpperHalfPlane) → ℂ} (hf : f ∈ modularFormChar 𝔑 χ k) :
    IsLatticePeriodic f (koecherBasis I1) :=
  isLatticePeriodic_of_transl hf.1.1 1 fun β hβ => transl_mem_Gamma1 𝔑 (by simpa using hβ)

lemma abs_chiPi_le {Q₀ : QuadForm (𝓞 F) n} {π : 𝓞 F} (hπ : Prime π) : |chiPi Q₀ hπ| ≤ 1 := by
  unfold chiPi LocalDensity.DVR.chiDisc
  set a := ((-1 : _) ^ (n / 2) * LocalDensity.DVR.resGramDet (LocalDensity.NF.Qp (hosOf hπ) Q₀))
  by_cases ha : a = 0
  · rw [ha, quadraticChar_zero]; norm_num
  · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num

/-- $|\lambda_\pi| \ge \frac12 q^{n-2}$: $\lambda_\pi = x^2 + \chi_\pi x + 1$ with $x = q^{k-1}$, $|\chi_\pi| \le 1$, and $x^2/2 - x + 1 > 0$. -/
lemma norm_heckeEigen_ge {Q₀ : QuadForm (𝓞 F) n} {k : ℕ} (hn : n = 2 * k) (hk : 1 ≤ k) {π : 𝓞 F}
    (hπ : Prime π) : (nm π : ℝ) ^ (2 * k - 2) / 2 ≤ ‖heckeEigen Q₀ hπ‖ := by
  set x : ℝ := (nm π : ℝ) ^ (k - 1)
  have hx : (nm π : ℝ) ^ (2 * k - 2) = x ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  have hn1 : n - 2 = 2 * k - 2 := by omega
  have hn2 : n / 2 - 1 = k - 1 := by omega
  have e : heckeEigen Q₀ hπ = ((x ^ 2 + (chiPi Q₀ hπ : ℝ) * x + 1 : ℝ) : ℂ) := by
    rw [heckeEigen, hn1, hn2, ← hx]; simp only [x]; push_cast; ring
  rw [e, Complex.norm_real, hx]
  have hχ : |(chiPi Q₀ hπ : ℝ)| ≤ 1 := by exact_mod_cast abs_chiPi_le hπ
  have hx0 : 0 ≤ x := by positivity
  have h1 : -x ≤ (chiPi Q₀ hπ : ℝ) * x := by
    have := abs_le.mp hχ
    nlinarith
  have h2 : 0 ≤ x ^ 2 + (chiPi Q₀ hπ : ℝ) * x + 1 := by nlinarith
  rw [Real.norm_of_nonneg h2]
  nlinarith [sq_nonneg (x - 2)]

/-! ### The coefficients of $\theta_{\mathrm{Gen}}$ -/

section ThetaGen

variable [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
  (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

open Classical in
/-- The coefficient of $\theta_M$ on $\mathfrak d^{-1}$: $r_M(\nu)$ if $\nu_m = \nu \in \mathcal O_F$, else $0$. -/
noncomputable def latCoeff (Q : QuadForm F n) (M : Submodule (𝓞 F) (Fin n → F))
    (m : Fin (Module.finrank ℚ F) → ℤ) : ℂ :=
  if h : ∃ ν : 𝓞 F, (ν : F) = QuadFormsKB.Analysis.dualElt I1 m then (latRepF Q M h.choose : ℂ) else 0

/-- $r_{Q_\gamma}(\nu) = r_{\gamma\mathcal O_F^n}(\nu)$. -/
lemma repNumF_gramZ (γ : GL (Fin n) F)
    (h : IsIntegral (formF Q₀) (latOf γ)) (hpos : IsTotPosGram (gramF (gramZ (formF Q₀) γ h)))
    (ν : 𝓞 F) : repNumF (gramZ (formF Q₀) γ h) ν = latRepF (formF Q₀) (latOf γ) ν := by
  have hL : latOf γ = glImage γ (Nbr.stdLat (𝓞 F) F n) := by rw [latOf, intVec_eq_stdLat]
  rw [hL, latRepF_glImage_eq γ h, latRep_stdLat (fun M => finite_repSetF hpos M)]
  rfl

include hQ hn hlev h𝔑 in
/-- **The $q$-coefficients of $\theta_{\mathrm{Gen}}$**: $a_{\nu_m}(\theta_{\mathrm{Gen}}) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)}|O(M)|^{-1}a_{\nu_m}(\theta_M)$,
with $a_\nu(\theta_M) = r_M(\nu)$ for $\nu \in \mathcal O_F$ and $0$ for $\nu \in \mathfrak d^{-1}\setminus\mathcal O_F$ (`latCoeff`). -/
@[kb "siegel1935" "the q-coefficients of θ_Gen are the genus averages r_Gen(ν), over F [unverified]"]
theorem qCoeff_thetaGen (m : Fin (Module.finrank ℚ F) → ℤ) :
    qCoeff (thetaGen (formF Q₀) stdLat) (koecherBasis I1) (realVec (QuadFormsKB.Analysis.dualElt I1 m)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * latCoeff (formF Q₀) c.out.1 m := by
  classical
  set C := (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset
  have hfree := genusFree_of_isPrincipalIdealRing (formF Q₀) (stdLat (F := F) (n := n))
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
  · rw [repNumF_gramZ γ hi hpos, ← hγ]
  · rfl

end ThetaGen

/-! ### $\theta_{\mathrm{Gen}} = E$ -/

section Main

variable [IsPrincipalIdealRing (𝓞 F)] {Q₀ : QuadForm (𝓞 F) n} (hQ : IsTotallyPosDef (formF Q₀)) {k : ℕ}
  (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q₀ 𝔑) (h𝔑 : 𝔑 ≠ ⊥)

/-- A $\pi$-unit $\nu$ with $\pi^2\nu \in \mathcal O_F$ is in $\mathcal O_F$. -/
lemma mem_int_of_sq_mul {π : 𝓞 F} (hπ : Prime π) {ν : F} (hν : IsUnitAt π ν) {ν' : 𝓞 F}
    (h : (ν' : F) = (π : F) ^ 2 * ν) : ∃ t : 𝓞 F, (t : F) = ν := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hν
  have hy0 : (y : F) ≠ 0 := by
    intro h0; apply hy
    rw [show y = 0 from IsFractionRing.injective (𝓞 F) F (by rw [map_zero]; exact h0)]
    exact dvd_zero π
  -- `ν' y = π² x`
  have e : ν' * y = π ^ 2 * x := by
    apply IsFractionRing.injective (𝓞 F) F
    have h1 : algebraMap (𝓞 F) F ν' = algebraMap (𝓞 F) F π ^ 2 * ν := h
    have h2 : ν * algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F x := hxy
    rw [map_mul, map_mul, map_pow, h1, mul_assoc, h2]
  have hcop : IsCoprime y (π ^ 2) := ((Prime.coprime_iff_not_dvd hπ).mpr hy).symm.pow_right
  have hdvd : y ∣ x := hcop.dvd_of_dvd_mul_left ⟨ν', by rw [← e]; ring⟩
  obtain ⟨t, rfl⟩ := hdvd
  refine ⟨t, ?_⟩
  apply mul_left_cancel₀ hy0
  have h2 : ν * algebraMap (𝓞 F) F y = algebraMap (𝓞 F) F (y * t) := hxy
  change algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t = algebraMap (𝓞 F) F y * ν
  rw [mul_comm (algebraMap (𝓞 F) F y) ν, h2, map_mul]

include hQ hn hlev h𝔑 in
/-- **$\theta_{\mathrm{Gen}} = E$ from cuspidality and the $T(\pi^2)$ relations** (Siegel's formula over $F$, Hecke/Kneser route; any $k \ge 2$,
i.e. every even $n \ge 4$, every degree $[F:\mathbb Q]$, $\mathcal O_F$ a PID). If $E$ is a function with
$\theta_{\mathrm{Gen}} - E \in S_k(\Gamma_0(\mathfrak N), \chi_Q)$, $E$ satisfies the $T(\pi^2)$ relations with the Eichler eigenvalues (`EisHeckeRel`),
then $\theta_{\mathrm{Gen}} = E$. (That Kneser neighbours stay in the genus is proved, `nbrInGenus_of_pid`.) -/
@[kb "siegel1935" "θ_Gen = E via Hecke/Kneser over F [unverified]"]
theorem thetaGen_eq_of_sub_mem_cuspFormChar (hk : 2 ≤ k) {E : (InfinitePlace F → UpperHalfPlane) → ℂ}
    (hcusp : thetaGen (formF Q₀) stdLat - E ∈ cuspFormChar 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑) k)
    (hE : EisHeckeRel Q₀ E) : thetaGen (formF Q₀) stdLat = E := by
  classical
  obtain ⟨mE, hmE, hErel⟩ := hE
  set θ := thetaGen (formF Q₀) stdLat with hθdef
  set b := koecherBasis I1
  have hθ := thetaGen_mem_modularFormChar hQ hn hlev h𝔑 (genusFree_of_isPrincipalIdealRing _ _)
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
  have hsub := eq_zero_of_heckeRel h𝔑 hk hcusp (lam := fun π => if h : Prime π then heckeEigen Q₀ h else 0)
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
    rw [dualVec_koecherBasis, dualVec_koecherBasis, qCoeff_thetaGen hQ hn hlev h𝔑,
      qCoeff_thetaGen hQ hn hlev h𝔑, mul_left_comm]
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
      exact genus_sum_latRepF_sq_of_pid hQ hπ hπ2 hπd (by rw [hn]; exact even_two_mul k)
        (by omega) hνπ
    · have hc1 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m = 0 := fun c => by
        rw [latCoeff, dif_neg hint]
      have hint' : ¬ ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 m' := by
        rintro ⟨ν', hν'⟩
        exact hint (mem_int_of_sq_mul hπ hu (hν'.trans hm''.symm))
      have hc2 : ∀ c : LatClass (formF Q₀), latCoeff (formF Q₀) c.out.1 m' = 0 := fun c => by
        rw [latCoeff, dif_neg hint']
      simp [hc1, hc2]
  · intro π hπ _
    simp only [dif_pos hπ]
    exact norm_heckeEigen_ge hn (by omega) hπ

include hQ hn hlev h𝔑 in
/-- **Siegel's formula over $F$, $n \ge 6$: $\theta_{\mathrm{Gen}} = E_Q$** (Hecke/Kneser route). For $F$ totally real with $\mathcal O_F$ a PID,
$Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2k \ge 6$ variables and $\mathfrak N \ne 0$ a theta level, the genus theta series equals
The Eisenstein series of the genus, given the input `EisHeckeRel Q₀ (eisQ Q₀ k)`. -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E_Q over F, n ≥ 6 [unverified]"]
theorem thetaGen_eq_eisQ (hk : 3 ≤ k) (hE : EisHeckeRel Q₀ (eisQ Q₀ k)) :
    thetaGen (formF Q₀) stdLat = eisQ Q₀ k :=
  thetaGen_eq_of_sub_mem_cuspFormChar hQ hn hlev h𝔑 (by omega)
    (thetaGen_sub_eisQ_mem_cuspFormChar_of_pid hQ hn hlev h𝔑 hk) hE

include hQ hlev h𝔑 in
/-- **Siegel's formula over $F$, $n = 4$: $\theta_{\mathrm{Gen}} = E$** for any $E$ with $\theta_{\mathrm{Gen}} - E \in S_2(\Gamma_0(\mathfrak N), \chi_Q)$
(`ThetaGenSubCusp2`, to be discharged by the weight-2 Eisenstein series of `Cuspidal2.lean`) and the $T(\pi^2)$ relations (`EisHeckeRel`). -/
@[kb "siegel1935" "Hauptsatz, θ_Gen = E over F, n = 4 [unverified]"]
theorem thetaGen_eq_of_wt2 (hn : n = 2 * 2) {E : (InfinitePlace F → UpperHalfPlane) → ℂ}
    (hcusp : ThetaGenSubCusp2 Q₀ E 𝔑 (thetaCharF (isTotPosGram_Q₀ hQ) hn hlev h𝔑))
    (hE : EisHeckeRel Q₀ E) : thetaGen (formF Q₀) stdLat = E :=
  thetaGen_eq_of_sub_mem_cuspFormChar hQ hn hlev h𝔑 le_rfl (by exact_mod_cast hcusp) hE

include hQ hn hlev h𝔑 in
/-- **The coefficients of $E_Q$ are the genus averages** ($n \ge 6$, inputs as in `thetaGen_eq_eisQ`): for $\nu \in \mathcal O_F$,
$$a_\nu(E_Q) = r_{\mathrm{Gen}}(\nu) = \mathrm{Mass}^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^n)}\frac{r_M(\nu)}{|O(M)|}.$$
(The coefficient formula identifies the left side with $c_\infty N(\nu)^{k-1}\prod_\mathfrak q\beta_\mathfrak q(\nu)$.) -/
@[kb "siegel1935" "r_Gen(ν) = ν-th coefficient of E_Q, over F, n ≥ 6 [unverified]"]
theorem qCoeff_eisQ_eq_genus_avg (hk : 3 ≤ k) (hE : EisHeckeRel Q₀ (eisQ Q₀ k)) (ν : 𝓞 F) :
    qCoeff (eisQ Q₀ k) (koecherBasis I1) (realVec (ν : F)) =
      ((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
        ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
          ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * (latRepF (formF Q₀) c.out.1 ν : ℂ) := by
  classical
  rw [← thetaGen_eq_eisQ hQ hn hlev h𝔑 hk hE, ← dualElt_mOf ν, qCoeff_thetaGen hQ hn hlev h𝔑]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : ∃ ν' : 𝓞 F, (ν' : F) = QuadFormsKB.Analysis.dualElt I1 (mOf ν) := ⟨ν, (dualElt_mOf ν).symm⟩
  rw [latCoeff, dif_pos h1]
  congr 3
  exact IsFractionRing.injective (𝓞 F) F (h1.choose_spec.trans (dualElt_mOf ν))

end Main

end QuadFormsKB.HilbertModular
