/-
# The local bound for the standard section of degree $r$
**Layer:** local, non-archimedean: every finite place $v$ of a number field $F$, dyadic places included, and every
Schwartz–Bruhat function $\Phi \in S(V_v^r)$.

**Results.**
* `eq_factor_of_isIntSp`: every $k \in \mathrm{Sp}_{2r}(\mathcal O_v)$ is $n(X)\,(w\,n(Y)\,w^{-1})\,m(A)\,n(Z)$ with $X, Y, Z$ integral
  symmetric and $A \in \mathrm{GL}_r(\mathcal O_v)$ (from `symplectic_factor_local`).
* `norm_secRV_int_le`, `exists_bound_secRV_int` (**$f_\Phi$ is bounded on $\mathrm{Sp}_{2r}(\mathcal O_v)$**):
  $|f_\Phi(k)| \le |\gamma_V^rc_B^r|\int|\omega(w)\omega(n(Z))\Phi|$ for the $Z$ of the factorization (writing
  $w^{-1}m(A) = w\,m(-A)$, $w\,m(A') = m({}^tA'^{-1})w$, and using $|\det A'|_v = 1$), so $|f_\Phi| \le C$ on $\mathrm{Sp}_{2r}(\mathcal O_v)$ by
  the uniform bound `exists_bound_integral_opWg_opNg`.
* `norm_secRV_le_of_int_bound` (Iwasawa, `iwasawaR`): $|f_\Phi(g)| \le C\,\|g\|_v^{-m}$ for all $g \in \mathrm{Sp}_{2r}(F_v)$.
* **`exists_norm_secSR_le`** (**the local bound**): $|f_v(g, s)| \le C\,\|g\|_v^{-(\operatorname{Re}s+\rho_r)}$ for the standard section,
  every $g$ and $s$.

For $r = 1$ this is `exists_norm_secS_le_Sn` (`SiegelWeil/EisensteinAdelic.lean`).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Weil, Acta Math. 113 (1965), Ch. II
[unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.Forms.EisensteinIwasawa
import QuadFormsKB.SiegelWeil.Forms.EisensteinGlobal
import QuadFormsKB.SiegelWeil.Convergence
import QuadFormsKB.SiegelWeil.Forms.EisensteinFourierBound

open MeasureTheory Matrix IsDedekindDomain NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

open WeilRep WeilRep.LocalData WeilRep.Genus QuadFormsKB.Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- **The factorization of an integral symplectic matrix**: $k = n(X)\,(w\,n(Y)\,w^{-1})\,m(A)\,n(Z)$ with $X, Y, Z$ symmetric with
entries in $\mathcal O_v$ and $A, A^{-1}$ with entries in $\mathcal O_v$. -/
theorem eq_factor_of_isIntSp (k : Sp r Fv) (hk : IsIntSp v k) :
    ∃ (X : Matrix (Fin r) (Fin r) Fv) (hX : Xᵀ = X) (Y : Matrix (Fin r) (Fin r) Fv) (hY : Yᵀ = Y)
      (Z : Matrix (Fin r) (Fin r) Fv) (hZ : Zᵀ = Z) (A : GL (Fin r) Fv),
      (∀ i j, ‖Z i j‖ ≤ 1) ∧ (∀ i j, ‖(A : Matrix (Fin r) (Fin r) Fv) i j‖ ≤ 1) ∧
      (∀ i j, ‖((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) i j‖ ≤ 1) ∧
      k = spN X hX * (spW * spN Y hY * spW⁻¹) * spM A * spN Z hZ := by
  obtain ⟨X, Y, Z, A, hX, hY, hZ, hA, hfac⟩ := symplectic_factor_local (intMatSp_mem v k hk)
  have hint : ∀ (M : Matrix (Fin r) (Fin r) 𝔬) i j, ‖(M.map (algebraMap 𝔬 Fv)) i j‖ ≤ 1 :=
    fun M i j => (norm_le_one_iff_valued v).mpr (valued_algebraMap_le_one v (M i j))
  have hXs : (-(X.map (algebraMap 𝔬 Fv)))ᵀ = -(X.map (algebraMap 𝔬 Fv)) := by
    rw [transpose_neg, ← transpose_map, hX]
  have hYs : (-(Y.map (algebraMap 𝔬 Fv)))ᵀ = -(Y.map (algebraMap 𝔬 Fv)) := by
    rw [transpose_neg, ← transpose_map, hY]
  have hZs : (Z.map (algebraMap 𝔬 Fv))ᵀ = Z.map (algebraMap 𝔬 Fv) := by rw [← transpose_map, hZ]
  have hAu : IsUnit (A.map (algebraMap 𝔬 Fv)).det := by
    have h := RingHom.map_det (algebraMap 𝔬 Fv) A
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]; exact hA.map _
  set AG : GL (Fin r) Fv := ((Matrix.isUnit_iff_isUnit_det _).mpr hAu).unit
  have hAG : (AG : Matrix (Fin r) (Fin r) Fv) = A.map (algebraMap 𝔬 Fv) := rfl
  have hAGinv : ((AG⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) = A⁻¹.map (algebraMap 𝔬 Fv) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hAG, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨_, hXs, _, hYs, _, hZs, AG, hint Z, by rw [hAG]; exact hint A, by rw [hAGinv]; exact hint _, ?_⟩
  apply Subtype.ext
  have h1 : (1 : Matrix (Fin r) (Fin r) 𝔬).map (algebraMap 𝔬 Fv) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix (Fin r) (Fin r) 𝔬).map (algebraMap 𝔬 Fv) = 0 := Matrix.map_zero _ (map_zero _)
  have hnX : (-X).map (algebraMap 𝔬 Fv) = -(X.map (algebraMap 𝔬 Fv)) := Matrix.map_neg _ (map_neg _) X
  rw [← intMatSp_map v k hk, hfac]
  simp only [Matrix.map_mul, fromBlocks_map, Submonoid.coe_mul, spN_coe, spM_coe, spW_coe,
    SymplecticGroup.coe_inv, hAGinv, hAG, h1, h0, hnX, ← transpose_map]
  simp only [Matrix.J, fromBlocks_multiply, fromBlocks_transpose, transpose_map, fromBlocks_neg, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_one, transpose_zero,
    transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_zero, neg_neg]

/-! ### The operators in absolute value -/

lemma secRV_spN_mul (Φ : Sg (localDataV v) m r) (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) (g : Sp r Fv) :
    secRV v a Φ (spN B hB * g) = secRV v a Φ g := secR_spN_mul Φ B hB g

/-- $f_\Phi(wh) = \gamma_V^rc_B^r\int\omega(h)\Phi$. -/
lemma secRV_spW_mul (Φ : Sg (localDataV v) m r) (h : Sp r Fv) :
    secRV v a Φ (spW * h) = (localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r *
      ∫ X, ((weilRepSpV v a r h Φ : Sg (localDataV v) m r) : PtG m r Fv → ℂ) X ∂muG (localDataV v) m r := by
  rw [secRV_eq, map_mul, Module.End.mul_apply, weilRepSpV_spW, endW_apply]
  simp [opWg, BX]

lemma norm_weilRep_spN_apply (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) (φ : Sg (localDataV v) m r)
    (X : PtG m r Fv) :
    ‖((weilRepSpV v a r (spN B hB) φ : Sg (localDataV v) m r) : PtG m r Fv → ℂ) X‖ =
      ‖(φ : PtG m r Fv → ℂ) X‖ := by
  rw [weilRepSpV_spN, endN_apply _ _ hB]
  simp [opNg]

lemma norm_det_eq_one_of_int {A : GL (Fin r) Fv} (hA : ∀ i j, ‖(A : Matrix (Fin r) (Fin r) Fv) i j‖ ≤ 1)
    (hA' : ∀ i j, ‖((A⁻¹ : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv) i j‖ ≤ 1) :
    ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ = 1 := by
  have := valued_det_eq_one v (A := A) (fun i j => (norm_le_one_iff_valued v).mp (hA i j))
    (fun i j => (norm_le_one_iff_valued v).mp (hA' i j))
  exact WeilRep.norm_eq_one_of_valued this

lemma norm_weilRep_spM_apply (A : GL (Fin r) Fv) (hA : ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ = 1)
    (φ : Sg (localDataV v) m r) (X : PtG m r Fv) :
    ‖((weilRepSpV v a r (spM A) φ : Sg (localDataV v) m r) : PtG m r Fv → ℂ) X‖ =
      ‖(φ : PtG m r Fv → ℂ) (X * (A : Matrix (Fin r) (Fin r) Fv))‖ := by
  have hd : (A : Matrix (Fin r) (Fin r) Fv).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id Fv) A = A := by ext; rfl
  rw [weilRepSpV_spM, endM_apply, hmap]
  simp only [opMg, norm_mul, norm_chiV_V, md_eq_norm' v hd, hA, norm_pow, Complex.norm_real, norm_one, one_pow,
    one_mul]

lemma integral_norm_comp_mulRight (A : GL (Fin r) Fv) (hA : ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ = 1)
    (f : PtG m r Fv → ℂ) :
    ∫ X, ‖f (X * (A : Matrix (Fin r) (Fin r) Fv))‖ ∂muG (localDataV v) m r = ∫ X, ‖f X‖ ∂muG (localDataV v) m r := by
  have key := integral_comp_mulRight (m := m) (muG (localDataV v) m r) A (fun X => ((‖f X‖ : ℝ) : ℂ))
  have hcA := cA_eq (D := localDataV v) (m := m) (isModel_V v) (by
    show (Metric.closedBall (0 : Fv) 1).indicator (fun _ => (1 : ℂ)) ∈ SBK Fv
    exact indicator_closedBall_mem_SBK 0 one_pos) A
  have hd : (A : Matrix (Fin r) (Fin r) Fv).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  rw [md_eq_norm' v hd, hA, one_pow] at hcA
  rw [hcA, inv_one, one_smul, integral_complex_ofReal, integral_complex_ofReal] at key
  exact_mod_cast key

lemma spW_inv_eq : (spW : Sp r Fv)⁻¹ = spW * spM (-1 : GL (Fin r) Fv) := by
  have h1 : spM (-1 : GL (Fin r) Fv) * spM (-1 : GL (Fin r) Fv) = 1 := by
    rw [← spM_mul, neg_one_mul, neg_neg, spM_one]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← spW_sq, ← h1, ← spW_sq]
  simp only [mul_assoc]

/-- **$f_\Phi$ on $\mathrm{Sp}_{2r}(\mathcal O_v)$ in terms of $\omega(w)\omega(n(Z))\Phi$**: for integral $k$ there is an integral symmetric $Z$
with $|f_\Phi(k)| \le |\gamma_V^rc_B^r|\int|\omega(w)\omega(n(Z))\Phi|$. -/
theorem norm_secRV_int_le (Φ : Sg (localDataV v) m r) (k : Sp r Fv) (hk : IsIntSp v k) :
    ∃ Z : Matrix (Fin r) (Fin r) Fv, (∀ i j, ‖Z i j‖ ≤ 1) ∧
      ‖secRV v a Φ k‖ ≤ ‖(localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r‖ *
        ∫ X, ‖opWg (localDataV v) a (opNg (localDataV v) a Z Φ) X‖ ∂muG (localDataV v) m r := by
  obtain ⟨X, hX, Y, hY, Z, hZ, A, hZi, hA, hA', rfl⟩ := eq_factor_of_isIntSp v k hk
  refine ⟨Z, hZi, ?_⟩
  set A1 : GL (Fin r) Fv := (-1 : GL (Fin r) Fv) * A
  have hrest : spN X hX * (spW * spN Y hY * spW⁻¹) * spM A * spN Z hZ =
      spN X hX * (spW * (spN Y hY * (spM (invT A1) * (spW * spN Z hZ)))) := by
    rw [spW_inv_eq]
    simp only [mul_assoc]
    rw [← mul_assoc (spM (-1 : GL (Fin r) Fv)), ← spM_mul, ← mul_assoc spW (spM A1), spW_spM, mul_assoc]
  have hdA : ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ = 1 := norm_det_eq_one_of_int v hA hA'
  have hdA2 : ‖((invT A1 : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv).det‖ = 1 := by
    have : ((invT A1 : GL (Fin r) Fv) : Matrix (Fin r) (Fin r) Fv).det *
        (A1 : Matrix (Fin r) (Fin r) Fv).det = 1 := by
      rw [invT_coe, det_transpose, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have hA1 : ‖(A1 : Matrix (Fin r) (Fin r) Fv).det‖ = 1 := by
      simp only [A1, Units.val_mul, Units.val_neg, Units.val_one, det_mul, det_neg, det_one, norm_mul, norm_pow,
        norm_neg, norm_one, one_pow, mul_one, hdA]
    have h2 := congrArg norm this
    rwa [norm_mul, hA1, mul_one, norm_one] at h2
  rw [hrest, secRV_spN_mul, secRV_spW_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [map_mul, map_mul]
  simp only [Module.End.mul_apply]
  simp only [norm_weilRep_spN_apply, norm_weilRep_spM_apply v a _ hdA2]
  rw [integral_norm_comp_mulRight v _ hdA2 (fun X => ((weilRepSpV v a r (spW * spN Z hZ) Φ :
    Sg (localDataV v) m r) : PtG m r Fv → ℂ) X)]
  have hZid : Z.map (RingHom.id Fv) = Z := by funext i j; rfl
  rw [map_mul, Module.End.mul_apply, weilRepSpV_spW, endW_apply, weilRepSpV_spN, endN_apply _ _ hZ, hZid]

/-! ### The bound on $\mathrm{Sp}_{2r}(F_v)$ -/

lemma htR_pos (g : Sp r Fv) : 0 < htR v g := by
  rw [htR_eq_maxMinor]; exact norm_pos_iff.mpr (minor_hMax_ne_zero v g)

/-- **From $\mathrm{Sp}_{2r}(\mathcal O_v)$ to $\mathrm{Sp}_{2r}(F_v)$ (Iwasawa)**: if $|f_\Phi| \le C$ on $\mathrm{Sp}_{2r}(\mathcal O_v)$, then
$|f_\Phi(g)| \le C\,\|g\|_v^{-m}$ for every $g$. -/
theorem norm_secRV_le_of_int_bound (Φ : Sg (localDataV v) m r) {C : ℝ}
    (hC : ∀ k : Sp r Fv, IsIntSp v k → ‖secRV v a Φ k‖ ≤ C) (g : Sp r Fv) :
    ‖secRV v a Φ g‖ ≤ C * htR v g ^ (-(m : ℝ)) := by
  obtain ⟨p, hp, k, hk, rfl⟩ := iwasawaR v g
  obtain ⟨B, hB, hpe⟩ := exists_spN_spM_of_mem_siegelP hp
  set A := levi hp
  have hd : (A : Matrix (Fin r) (Fin r) Fv).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hpos : 0 < ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ := norm_pos_iff.mpr hd
  have hht : htR v (p * k) = ‖(A : Matrix (Fin r) (Fin r) Fv).det‖⁻¹ := by
    rw [hpe, htR_spN_spM_mul, htR_eq_one_of_int v hk, mul_one]
  rw [hht, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv,
    Real.rpow_natCast, hpe, secRV_parabolic, norm_mul, norm_mul, norm_chiV_V, md_eq_norm' v hd, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_norm, one_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC k hk) (pow_nonneg hpos.le _)

/-- **The standard section from a bound on $\mathrm{Sp}_{2r}(\mathcal O_v)$**: $|f_v(g, s)| \le C\,\|g\|_v^{-(\operatorname{Re}s+\rho_r)}$,
$\rho_r = \frac{r+1}2$. -/
theorem norm_secSR_le_of_int_bound (Φ : Sg (localDataV v) m r) {C : ℝ}
    (hC : ∀ k : Sp r Fv, IsIntSp v k → ‖secRV v a Φ k‖ ≤ C) (g : Sp r Fv) (s : ℂ) :
    ‖secSR v a Φ g s‖ ≤ C * htR v g ^ (-(s.re + ((r : ℝ) + 1) / 2)) := by
  have hpos := htR_pos v g
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 fun x y => by
    rcases x with i | i <;> rcases y with j | j <;> by_cases h : i = j <;> simp [h])
  unfold secSR
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-(s - sZero m r)).re = -(s.re - ((m : ℝ) - ((r : ℝ) + 1) / 2)) := by
    simp [sZero]
  rw [hre]
  calc ‖secRV v a Φ g‖ * htR v g ^ (-(s.re - ((m : ℝ) - ((r : ℝ) + 1) / 2)))
      ≤ C * htR v g ^ (-(m : ℝ)) * htR v g ^ (-(s.re - ((m : ℝ) - ((r : ℝ) + 1) / 2))) :=
        mul_le_mul_of_nonneg_right (norm_secRV_le_of_int_bound v a Φ hC g) (Real.rpow_nonneg hpos.le _)
    _ = C * htR v g ^ (-(s.re + ((r : ℝ) + 1) / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; congr 2; ring

/-- **$f_\Phi$ is bounded on $\mathrm{Sp}_{2r}(\mathcal O_v)$**, for every $\Phi \in S(V_v^r)$ (`norm_secRV_int_le` and the uniform
bound `exists_bound_integral_opWg_opNg`). -/
theorem exists_bound_secRV_int (Φ : Sg (localDataV v) m r) :
    ∃ C : ℝ, ∀ k : Sp r Fv, IsIntSp v k → ‖secRV v a Φ k‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_integral_opWg_opNg v a Φ.2
  refine ⟨‖(localDataV v).gammaV a ^ r * (localDataV v).cB a ^ r‖ * C, fun k hk => ?_⟩
  obtain ⟨Z, hZ, hle⟩ := norm_secRV_int_le v a Φ k hk
  exact hle.trans (mul_le_mul_of_nonneg_left (hC Z hZ) (norm_nonneg _))

/-- **The local bound for the standard section of degree $r$** (every finite place, dyadic included, every
$\Phi \in S(V_v^r)$): there is $C$ with $|f_v(g, s)| \le C\,\|g\|_v^{-(\operatorname{Re}s+\rho_r)}$ for all $g \in \mathrm{Sp}_{2r}(F_v)$ and
$s \in \mathbb C$, $\rho_r = \frac{r+1}2$. -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; weil1965 Ch. II [unverified]"]
theorem exists_norm_secSR_le (Φ : Sg (localDataV v) m r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Sp r Fv) (s : ℂ), ‖secSR v a Φ g s‖ ≤ C * htR v g ^ (-(s.re + ((r : ℝ) + 1) / 2)) := by
  obtain ⟨C, hC⟩ := exists_bound_secRV_int v a Φ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 fun x y => by
    rcases x with i | i <;> rcases y with j | j <;> by_cases h : i = j <;> simp [h])
  exact ⟨C, hC0, norm_secSR_le_of_int_bound v a Φ hC⟩

end QuadFormsKB.SiegelWeil.Forms
