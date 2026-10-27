import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.RelGenusExact
import QuadFormsKB.Binary.RelGenus
import QuadFormsKB.Siegel.NFDyadicGood

/-!
# Local densities of the norm form at dyadic primes prime to the discriminant

$E/F$ quadratic, $b$ an $\mathcal O_F$-basis of $\mathcal O_E$, $Q_b(x) = N_{E/F}(x_0b_0 + x_1b_1)$ (`normFormBasis`), $\det H(Q_b) = -\Delta_{E/F}(b)$,
$-\det H = \theta_b^2$ with $\theta_b = b_0\sigma b_1 - \sigma b_0\,b_1$, $\sigma\theta_b = -\theta_b$.

* **`hessian_det_mem_of_ramified`** (every residue characteristic): a ramified $\mathfrak p$ divides $\Delta_{E/F}(b)$. *Proof:* $\sigma$ acts
  trivially on $\mathcal O_E/\mathfrak P$ ($f = 1$, $\sigma\mathfrak P = \mathfrak P$), so $\theta_b \in \mathfrak P$ and $\theta_b^2 \in \mathfrak P \cap \mathcal O_F = \mathfrak p$.
* **`relChar_eq_quadSymbol`**: for $\mathfrak p \nmid \Delta_{E/F}(b)$ (dyadic or not), $\chi_{E/F}(\mathfrak p) = 1$ iff $-\det H(Q_b)$ is a square in
  $F_\mathfrak p$, and $\chi_{E/F}(\mathfrak p) = -1$ otherwise (`isSquare_of_split`, `not_isSquare_of_not_split`).
* **`isLocalLevel_zero_of_isUnit_det`**: a binary form over a commutative ring with unit Hessian determinant has local level
  $\pi^0$ (its Hessian inverse $\det^{-1}\operatorname{adj}H$ has even diagonal).
* **`localDensity_normFormBasis_dyadic`** (*the unramified dyadic primes*): for $\mathfrak p \mid 2$, $\mathfrak p \nmid \Delta_{E/F}(b)$ and $\nu$ a
  $\mathfrak p$-unit, $\beta_\mathfrak p(Q_b, \nu) = 1 - \chi_{E/F}(\mathfrak p)/N\mathfrak p$ — the same value as at the non-dyadic good primes
  (`localDensity_normFormBasis_good`, $v_\mathfrak p(\nu) = 0$), from Hanke Remark 3.4.1(a) at dyadic $\mathfrak p \nmid N$
  (`DVR.localDensity_unit_of_level_zero_dyadic`) and the Arf sign (`Siegel.arfSignQ_eq_quadSymbolNF`). Also the value at
  $v_\mathfrak p(\nu) = 1$ (`localDensity_normFormBasis_dyadic_ord_one`): $(1 - \chi/N\mathfrak p)(1 + \chi)$.

So at every prime $\mathfrak p \nmid \Delta_{E/F}(b)\nu$ (dyadic or not) $\beta_\mathfrak p(Q_b, \nu) = 1 - \chi_{E/F}(\mathfrak p)N\mathfrak p^{-1}$: the factors that the
regularized product absorbs into $L(1, \chi_{E/F})^{-1}$ are the true local densities.

Sources: Hanke (2004), Remark 3.4.1(a), Remark 5.4.1(b); O'Meara 93:16, p. 259 (background); Neukirch I §8 [unverified].
-/

open NumberField Module IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.LocalDensity.DVR

variable {R : Type*} [CommRing R]

/-- **A binary form with unit Hessian determinant has local level $\pi^0$:** $W = \det(H)^{-1}\operatorname{adj}(H)$ is symmetric with even
diagonal and $HW = 1$. -/
theorem isLocalLevel_zero_of_isUnit_det (Q : QuadForm R 2) (π : R) (h : IsUnit Q.hessian.det) :
    IsLocalLevel Q π 0 := by
  obtain ⟨u, hu⟩ := h
  refine ⟨(u⁻¹ : Rˣ).val • Q.hessian.adjugate, ?_, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, ← hu, smul_smul, Units.inv_mul, one_smul, pow_zero, one_smul]
  · have hs : Q.hessian.transpose = Q.hessian := by
      ext i j; simp only [QuadForm.hessian, Matrix.transpose_apply, Matrix.add_apply]; ring
    rw [Matrix.transpose_smul, Matrix.adjugate_transpose, hs]
  · intro i
    rw [Matrix.adjugate_fin_two]
    have hd : ∀ j, Q.hessian j j = 2 * Q.coeff j j := fun j => by
      simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]; ring
    fin_cases i
    · simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
        Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      rw [hd]; exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _
    · simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, smul_eq_mul, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero]
      rw [hd]; exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _

end QuadFormsKB.LocalDensity.DVR

namespace QuadFormsKB.Binary.Rel

open LocalDensity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **Ramified primes divide the discriminant of the norm form** (every residue characteristic): if $\chi_{E/F}(\mathfrak p) = 0$ then
$\det H(Q_b) = -\Delta_{E/F}(b) \in \mathfrak p$. -/
@[kb "neukirch1999" "Ch. III, Thm. 2.6 (ramified primes divide the discriminant) [unverified]"]
theorem hessian_det_mem_of_ramified (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h𝔭 : relChar E 𝔭 = 0) : (normFormBasis b).hessian.det ∈ 𝔭.asIdeal := by
  obtain ⟨P, hσ, -, hf⟩ := conjIdeal_prime_eq h𝔭
  have hP := P.2
  have : P.1.IsPrime := hP.1
  have : P.1.LiesOver 𝔭.asIdeal := hP.2
  have : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have : P.1.IsMaximal := isMaximal_of_primesOver P
  -- σ is trivial mod P
  have htriv : ∀ x : 𝓞 E, x - conjO F E x ∈ P.1 := by
    intro x
    obtain ⟨c, hc⟩ := exists_sub_mem_of_inertiaDeg_one 𝔭.asIdeal P.1 hf x
    have h1 : conjO F E (x - algebraMap (𝓞 F) (𝓞 E) c) ∈ conjIdeal F P.1 := Ideal.mem_map_of_mem _ hc
    rw [hσ, map_sub, conjO_algebraMap] at h1
    have e : x - conjO F E x = (x - algebraMap (𝓞 F) (𝓞 E) c) - (conjO F E x - algebraMap (𝓞 F) (𝓞 E) c) := by
      ring
    rw [e]; exact P.1.sub_mem hc h1
  have hθ : thetaB b ∈ P.1 := by
    have e : thetaB b = -(b 0 * (b 1 - conjO F E (b 1))) + b 1 * (b 0 - conjO F E (b 0)) := by
      rw [thetaB]; ring
    rw [e]
    exact P.1.add_mem (P.1.neg_mem (P.1.mul_mem_left _ (htriv _))) (P.1.mul_mem_left _ (htriv _))
  have hmem : algebraMap (𝓞 F) (𝓞 E) (-(normFormBasis b).hessian.det) ∈ P.1 := by
    rw [algebraMap_neg_hessian_det, pow_two]; exact P.1.mul_mem_left _ hθ
  have hover := Ideal.LiesOver.over (P := P.1) (p := 𝔭.asIdeal)
  have : -(normFormBasis b).hessian.det ∈ 𝔭.asIdeal := by rw [hover]; exact hmem
  simpa using this

/-- $\theta_b \ne 0$ when $\det H(Q_b) \ne 0$. -/
theorem thetaB_ne_zero (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) (hd : (normFormBasis b).hessian.det ≠ 0) :
    algebraMap (𝓞 E) E (thetaB b) ≠ 0 := by
  intro h0
  apply hd
  have h := algebraMap_neg_hessian_det b
  have : thetaB b = 0 := FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h0, map_zero])
  rw [this, pow_two, mul_zero] at h
  have := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E) (h.trans (map_zero _).symm)
  simpa using this

theorem algebraMap_neg_hessian_det_E (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) :
    algebraMap F E (algebraMap (𝓞 F) F (-(normFormBasis b).hessian.det)) = (algebraMap (𝓞 E) E (thetaB b)) ^ 2 := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E, algebraMap_neg_hessian_det,
    map_pow]

theorem conj_thetaB (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) :
    conj F E (algebraMap (𝓞 E) E (thetaB b)) = -algebraMap (𝓞 E) E (thetaB b) := by
  rw [← algebraMap_conjO, conjO_thetaB, map_neg]

open Classical in
/-- **The splitting character is the quadratic symbol of the discriminant** at every $\mathfrak p \nmid \Delta_{E/F}(b)$, dyadic included:
$\chi_{E/F}(\mathfrak p) = 1$ if $-\det H(Q_b)$ is a square in $F_\mathfrak p$, and $-1$ otherwise. -/
@[kb "neukirch1999" "Ch. I §8 [unverified]; omeara1963 §63A, 63:3, p. 161 (unramified quadratic extensions)"]
theorem relChar_eq_quadSymbol (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (hΔ : (normFormBasis b).hessian.det ∉ 𝔭.asIdeal) :
    relChar E 𝔭 = if IsSquare (algebraMap F (𝔭.adicCompletion F)
      (algebraMap (𝓞 F) F (-(normFormBasis b).hessian.det))) then 1 else -1 := by
  have hd : (normFormBasis b).hessian.det ≠ 0 := fun h => hΔ (h ▸ 𝔭.asIdeal.zero_mem)
  have ha0 : algebraMap (𝓞 F) F (-(normFormBasis b).hessian.det) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr (neg_ne_zero.mpr hd)
  have hram : relChar E 𝔭 ≠ 0 := fun h => hΔ (hessian_det_mem_of_ramified b h)
  rcases relChar_trichotomy (E := E) 𝔭 with h | h | h
  · rw [if_pos (isSquare_of_split h ha0 (algebraMap_neg_hessian_det_E b)), h]
  · rw [if_neg (not_isSquare_of_not_split (by rw [h]; norm_num) (thetaB_ne_zero b hd) (conj_thetaB b)
      (algebraMap_neg_hessian_det_E b)), h]
  · exact absurd h hram

theorem notDvdLevel_normFormBasis (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (hΔ : (normFormBasis b).hessian.det ∉ 𝔭.asIdeal) : NF.NotDvdLevel 𝔭 (normFormBasis b) := by
  refine DVR.isLocalLevel_zero_of_isUnit_det _ _ ?_
  rw [NF.det_hessian_Qp]
  exact DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π 𝔭) (fun h => hΔ ((NF.π_dvd_ι_iff 𝔭 _).mp h))

theorem arfSignQ_normFormBasis (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h2 : (2 : 𝓞 F) ∈ 𝔭.asIdeal) (hΔ : (normFormBasis b).hessian.det ∉ 𝔭.asIdeal) :
    DVR.arfSignQ (NF.Qp 𝔭 (normFormBasis b)) (NF.π 𝔭) = relChar E 𝔭 := by
  rw [Siegel.arfSignQ_eq_quadSymbolNF 𝔭 h2 (notDvdLevel_normFormBasis b hΔ) (by norm_num),
    relChar_eq_quadSymbol b hΔ, Siegel.quadSymbolNF]
  have hx : (-1 : 𝓞 F) ^ (2 / 2) * (normFormBasis b).hessian.det = -(normFormBasis b).hessian.det := by
    norm_num
  have hxm : -(normFormBasis b).hessian.det ∉ 𝔭.asIdeal := fun h => hΔ (by simpa using 𝔭.asIdeal.neg_mem h)
  rw [hx, if_neg hxm]
  congr 1

/-- **Local densities of the norm form at the unramified dyadic primes, $\nu$ a unit:** for $\mathfrak p \mid 2$, $\mathfrak p \nmid \Delta_{E/F}(b)$,
$\nu \notin \mathfrak p$: $\beta_\mathfrak p(Q_b, \nu) = 1 - \chi_{E/F}(\mathfrak p)/N\mathfrak p$. -/
@[kb "hanke2004" "Remark 3.4.1(a), p. 361 (dyadic p ∤ N); cf. D5 localDensity_good_binary"]
theorem localDensity_normFormBasis_dyadic (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h2 : (2 : 𝓞 F) ∈ 𝔭.asIdeal) (hΔ : (normFormBasis b).hessian.det ∉ 𝔭.asIdeal) {ν : 𝓞 F}
    (hν : ν ∉ 𝔭.asIdeal) :
    NF.localDensity 𝔭 (normFormBasis b) ν = 1 - (relChar E 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
  classical
  rw [NF.localDensity_eq_completion, DVR.localDensity_unit_of_level_zero_dyadic _ (NF.irreducible_π 𝔭)
    (NF.π_dvd_two 𝔭 h2) (NF.two_ne_zero' 𝔭) (notDvdLevel_normFormBasis b hΔ) (by norm_num) _
    (fun h => hν ((NF.π_dvd_ι_iff 𝔭 _).mp h)), arfSignQ_normFormBasis b h2 hΔ, NF.q_completion]
  norm_num

/-- **$v_\mathfrak p(\nu) = 1$ at an unramified dyadic prime:** $\beta_\mathfrak p(Q_b, \nu) = (1 - \chi/N\mathfrak p)(1 + \chi)$, $\chi = \chi_{E/F}(\mathfrak p)$ (Hanke
Remark 5.4.1(b) with $n = 2$) — again the good-prime formula $(1 - \chi/q)\sum_{j \le 1}\chi^j$. -/
@[kb "hanke2004" "Remark 5.4.1(b), p. 370 (dyadic p ∤ N)"]
theorem localDensity_normFormBasis_dyadic_ord_one (b : Basis (Fin 2) (𝓞 F) (𝓞 E)) {𝔭 : HeightOneSpectrum (𝓞 F)}
    (h2 : (2 : 𝓞 F) ∈ 𝔭.asIdeal) (hΔ : (normFormBasis b).hessian.det ∉ 𝔭.asIdeal) {ν : 𝓞 F}
    (hν1 : ν ∈ 𝔭.asIdeal) (hν2 : ν ∉ 𝔭.asIdeal ^ 2) :
    NF.localDensity 𝔭 (normFormBasis b) ν =
      (1 - (relChar E 𝔭 : ℝ) / (Ideal.absNorm 𝔭.asIdeal : ℝ)) * (1 + (relChar E 𝔭 : ℝ)) := by
  classical
  have hπ2 : ¬ NF.π 𝔭 ^ 2 ∣ NF.ι 𝔭 ν := by rw [NF.π_pow_dvd_ι_iff]; exact hν2
  rw [NF.localDensity_eq_completion, DVR.localDensity_ord_one_of_level_zero_dyadic _ (NF.irreducible_π 𝔭)
    (NF.π_dvd_two 𝔭 h2) (NF.two_ne_zero' 𝔭) (notDvdLevel_normFormBasis b hΔ) (by norm_num) _
    ((NF.π_dvd_ι_iff 𝔭 _).mpr hν1) hπ2, arfSignQ_normFormBasis b h2 hΔ, NF.q_completion]
  norm_num

end QuadFormsKB.Binary.Rel
