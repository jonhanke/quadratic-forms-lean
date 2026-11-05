/-
# The Siegel–Weil formula for every totally positive form over $\mathcal O_F$
**Layer:** local at each finite place (dyadic places included), then global over a totally real number field $F$.

**Setting.** $Q_0$ a quadratic form over $\mathcal O_F$ in $n = 2m$ variables, not necessarily diagonal, with lattice $L = \mathcal O_F^n$.
The Weil representation of the library is written in diagonal coordinates (`Weil/Model.lean`: $Q(y) = \sum_id_iy_i^2$). A global
diagonalization $Q_0\circ P = \langle d_0, \dots, d_{n-1}\rangle$ with $P \in M_n(\mathcal O_F)$, $\det P \ne 0$ (`exists_diag_global`) is an
isometry $y \mapsto Py$ from $(F^n, \langle d\rangle)$ onto $(F^n, Q_0)$; it carries the lattice
$$L' = P^{-1}\mathcal O_F^n = \{y : Py \in \mathcal O_F^n\}$$
onto $L$. At a finite place $v$ the local datum is $\Phi_v = \mathbf 1_{L'_v}$, $\Phi_v(y) = \mathbf 1_{\mathcal O_v^n}(Py)$ (`latInd`). It is not a
pure tensor in general (at a dyadic place $L_v$ need not have an orthogonal basis), but it is a finite sum of translates of
$\mathbf 1_{\mathcal O_v^n}$, so it lies in the Schwartz–Bruhat space (`latInd_mem_Sn`); $\Phi_v = \mathbf 1_{\mathcal O_v^n}$ when $\det P$ is a $v$-unit
(`latInd_eq_oneV`).

**Results (local).**
* `latInd_mem_Sn`, `latInd_eq_oneV`.
* `integral_psiV_latInd`: $\int_{F_v^n}\psi_v(b\langle d\rangle(y))\,\Phi_v(y)\,dy = |\det P|_v^{-1}\int_{\mathcal O_v^n}\psi_v(bQ_0(x))\,dx$ (change of variables
  $x = Py$, `map_mulVec_eq_glHaarChar_inv`); `secV_latS_eq_locAvg`: $f_v(wn(u)) = \gamma_{V,v}c_{B,v}\operatorname{vol}(\mathcal O_v)^n|\det P|_v^{-1}A_v(Q_0; u, e)$.

**Results (global).**
* `finSecL`, `globalSecL`, `eisensteinL`: the section and the Siegel Eisenstein series $E^P$ of $\Phi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L'_v}$; left
  $B(F)$-invariance (`globalSecL_borel`), the Bruhat expansion (`eisensteinL_eq_bruhat`); for $P = 1$ they are `finSec` and `eisenstein`
  (`finSecL_one`, `eisensteinL_one`).
* `finSecL_wMat_nMat`: $f_f^P(wn(u), s_0) = \kappa_f(d)\,|N(\det P)|\,G_{Q_0}(-u)$; `thetaK_compMat`: $K_{\langle d\rangle}|N(\det P)| = K_{Q_0}$.
* **`eisensteinL_archSec_eq_eisQ`**: $E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}E_{Q_0}(z)$, absolutely convergent ($n \ge 6$).
* **`siegelWeil_formula_lattice`** ($E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\theta_{\mathrm{Gen}}(z)$, given `PrincipalPrimeSupply F`) and
  **`siegelWeil_formula_lattice_of_pid`** ($h_F = 1$, unconditional, with the explicit genus average). No `GenusFree` hypothesis
  (`genusFree_formF`).

Sources: Weil, Acta Math. 113 (1965) [unverified]; O'Meara (1973), §93 (dyadic lattices without orthogonal bases).
-/
import QuadFormsKB.SiegelWeil.SiegelWeilFormula
import QuadFormsKB.SiegelWeil.Convergence
import QuadFormsKB.HilbertModular.SteinitzGenus
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling
import QuadFormsKB.Tamagawa.FrameDiag

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups
open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ}

/-- The matrix $P$ over $F_v$. -/
abbrev matV (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv :=
  P.map (algebraMap (𝓞 F) Fv)

/-- **The transported lattice indicator** $\Phi_v(y) = \mathbf 1_{\mathcal O_v^n}(Py)$, the indicator of $L'_v = P^{-1}\mathcal O_v^n$. -/
def latInd (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) : (Fin (2 * m) → Fv) → ℂ :=
  fun y => oneV v (2 * m) (matV v P *ᵥ y)

lemma ballIndV_mem_SBK (c : Fv) : ballIndV v c 0 ∈ SBK Fv := by
  have e : ballIndV v c 0 = (Metric.closedBall c 1).indicator fun _ => (1 : ℂ) := by
    unfold ballIndV; rw [ballIndV_eq]; simp
  rw [e]; exact indicator_closedBall_mem_SBK c one_pos

lemma valued_matV_le_one (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (i j : Fin (2 * m)) :
    Valued.v (matV v P i j) ≤ 1 := by
  show Valued.v (algebraMap (𝓞 F) Fv (P i j)) ≤ 1
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
  have := valued_algebraMap_int_le_of_mem v (b := P i j) (n := 0) (by simp)
  simpa using this

/-- An integral matrix maps $\mathcal O_v^n$ into itself. -/
lemma valued_mulVec_le_one (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) {y : Fin (2 * m) → Fv}
    (hy : ∀ i, Valued.v (y i) ≤ 1) (i : Fin (2 * m)) : Valued.v ((matV v P *ᵥ y) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (valued_matV_le_one v P i j) (hy j)

lemma oneV_eq_ite' (x : Fin (2 * m) → Fv) :
    oneV v (2 * m) x = if ∀ i, Valued.v (x i) ≤ 1 then 1 else 0 := oneV_eq_ite v x

/-- $\Phi_v$ is invariant under translation by $\mathcal O_v^n$. -/
lemma latInd_add (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (y w : Fin (2 * m) → Fv)
    (hw : ∀ i, Valued.v (w i) ≤ 1) : latInd v P (y + w) = latInd v P y := by
  unfold latInd
  rw [Matrix.mulVec_add, oneV_eq_ite', oneV_eq_ite']
  have hPw := valued_mulVec_le_one v P hw
  congr 1
  apply propext
  constructor
  · intro h i
    have e : (matV v P *ᵥ y) i = (matV v P *ᵥ y + matV v P *ᵥ w) i - (matV v P *ᵥ w) i := by
      simp
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le (h i) (hPw i))
  · intro h i
    exact (Valuation.map_add _ _ _).trans (max_le (h i) (hPw i))

/-- The uniformizer $\varpi_v$ in $F_v$, $|\varpi_v|_v = q_v^{-1}$. -/
abbrev piV : Fv := ((LocalDensity.NF.π v : 𝔬) : Fv)

lemma piV_ne_zero : piV v ≠ 0 := by
  intro h
  have := LocalDensity.NF.valued_π v
  rw [show ((LocalDensity.NF.π v : 𝔬) : Fv) = 0 from h, map_zero] at this
  exact exp_ne_zero this.symm

/-- **$L'_v \subseteq \varpi_v^{-k}\mathcal O_v^n$** when $|\det P|_v = q_v^{-k}$: $\det P\cdot y = \operatorname{adj}(P)(Py)$. -/
lemma valued_piV_pow_mul_le_one (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) {k : ℕ}
    (hk : Valued.v (algebraMap (𝓞 F) Fv P.det) = exp (-(k : ℤ))) {y : Fin (2 * m) → Fv}
    (hy : ∀ i, Valued.v ((matV v P *ᵥ y) i) ≤ 1) (i : Fin (2 * m)) :
    Valued.v (piV v ^ k * y i) ≤ 1 := by
  have hadj : (matV v P.adjugate) *ᵥ (matV v P *ᵥ y) = algebraMap (𝓞 F) Fv P.det • y := by
    rw [Matrix.mulVec_mulVec]
    have : matV v P.adjugate * matV v P = algebraMap (𝓞 F) Fv P.det • (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) := by
      have h1 : matV v P.adjugate = Matrix.adjugate (matV v P) :=
        (algebraMap (𝓞 F) Fv).map_adjugate P
      rw [h1, Matrix.adjugate_mul]
      congr 1
      exact ((algebraMap (𝓞 F) Fv).map_det P).symm
    rw [this, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hDy : Valued.v (algebraMap (𝓞 F) Fv P.det * y i) ≤ 1 := by
    have := valued_mulVec_le_one v P.adjugate hy i
    rwa [hadj, Pi.smul_apply, smul_eq_mul] at this
  rw [map_mul] at hDy ⊢
  rwa [map_pow, LocalDensity.NF.valued_π, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one, ← hk]

lemma ptensor_ballIndV_eq_ite (c x : Fin (2 * m) → Fv) :
    ptensor (fun i => ballIndV v (c i) 0) x = if ∀ i, Valued.v (x i - c i) ≤ 1 then 1 else 0 := by
  unfold ptensor
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => by
      show ballIndV v (c i) 0 (x i) = 1
      unfold ballIndV
      exact Set.indicator_of_mem (by simpa using h i) _
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      show ballIndV v (c i) 0 (x i) = 0
      unfold ballIndV
      exact Set.indicator_of_notMem (by simpa using hi) _)

lemma valued_piV_pow (k : ℕ) : Valued.v (piV v ^ k) = exp (-(k : ℤ)) := by
  rw [map_pow, LocalDensity.NF.valued_π, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]

/-- The coset centres $c_z = \varpi_v^{-k}\tilde z$, $z \in (\mathcal O_v/\mathfrak p_v^k)^n$. -/
abbrev cosetCtr (k : ℕ) (z : Fin (2 * m) → RQ v k) : Fin (2 * m) → Fv := fun i => (piV v ^ k)⁻¹ * liftR v k z i

/-- $y \in c_z + \mathcal O_v^n$ iff $\varpi_v^ky \in \tilde z + (\mathfrak p_v^k)^n$. -/
lemma valued_sub_ctr_le_one_iff (k : ℕ) (z : Fin (2 * m) → RQ v k) (y : Fin (2 * m) → Fv) (i : Fin (2 * m)) :
    Valued.v (y i - cosetCtr v k z i) ≤ 1 ↔ Valued.v (piV v ^ k * y i - liftR v k z i) ≤ exp (-(k : ℤ)) := by
  have hp : piV v ^ k ≠ 0 := pow_ne_zero _ (piV_ne_zero v)
  have e : piV v ^ k * y i - liftR v k z i = piV v ^ k * (y i - cosetCtr v k z i) := by
    simp only [cosetCtr]; field_simp
  rw [e, map_mul, valued_piV_pow]
  constructor
  · intro h
    calc exp (-(k : ℤ)) * Valued.v (y i - cosetCtr v k z i) ≤ exp (-(k : ℤ)) * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    calc Valued.v (y i - cosetCtr v k z i)
        = exp (k : ℤ) * (exp (-(k : ℤ)) * Valued.v (y i - cosetCtr v k z i)) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ ≤ exp (k : ℤ) * exp (-(k : ℤ)) := by gcongr
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

/-- **The coset decomposition of $\Phi_v$**: with $|\det P|_v = q_v^{-k}$,
$\Phi_v = \sum_{z\in(\mathcal O_v/\mathfrak p_v^k)^n}\Phi_v(c_z)\,\mathbf 1_{c_z + \mathcal O_v^n}$. -/
lemma latInd_eq_sum (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) {k : ℕ}
    (hk : Valued.v (algebraMap (𝓞 F) Fv P.det) = exp (-(k : ℤ))) [Fintype (RQ v k)] (y : Fin (2 * m) → Fv) :
    latInd v P y = ∑ z : Fin (2 * m) → RQ v k,
      latInd v P (cosetCtr v k z) * ptensor (fun i => ballIndV v (cosetCtr v k z i) 0) y := by
  classical
  simp_rw [ptensor_ballIndV_eq_ite]
  by_cases h : ∀ i, Valued.v (piV v ^ k * y i) ≤ 1
  · set z0 := redR v k (fun i => piV v ^ k * y i) h
    have hmem : (fun i => piV v ^ k * y i) ∈ fiberR v k z0 := (mem_fiberR_iff v k).mpr ⟨h, rfl⟩
    have hz0 : ∀ i, Valued.v (y i - cosetCtr v k z0 i) ≤ 1 := fun i =>
      (valued_sub_ctr_le_one_iff v k z0 y i).mpr (hmem i (Set.mem_univ _))
    rw [Finset.sum_eq_single z0]
    · split_ifs
      rw [mul_one]
      have e : cosetCtr v k z0 = y + (cosetCtr v k z0 - y) := by abel
      rw [e, latInd_add v P y (cosetCtr v k z0 - y) fun i => by
        rw [Pi.sub_apply, ← neg_sub, Valuation.map_neg]; exact hz0 i]
    · intro z _ hz
      split_ifs with hzy
      swap; · rw [mul_zero]
      exfalso
      apply hz
      have hmz : (fun i => piV v ^ k * y i) ∈ fiberR v k z := fun i _ =>
        (valued_sub_ctr_le_one_iff v k z y i).mp (hzy i)
      obtain ⟨_, e⟩ := (mem_fiberR_iff v k).mp hmz
      exact e.symm
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · have hy0 : latInd v P y = 0 := by
      unfold latInd
      rw [oneV_eq_ite', ite_eq_right_iff]
      intro hPy
      exact absurd (valued_piV_pow_mul_le_one v P hk hPy) h
    rw [hy0]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with hzy
    · have e : y = cosetCtr v k z + (y - cosetCtr v k z) := by abel
      have h1 : latInd v P (cosetCtr v k z) = latInd v P y := by
        conv_rhs => rw [e]
        rw [latInd_add v P (cosetCtr v k z) (y - cosetCtr v k z) fun i => hzy i]
      rw [h1, hy0, zero_mul]
    · rw [mul_zero]

/-- **$\Phi_v = \mathbf 1_{P^{-1}\mathcal O_v^n}$ is a Schwartz–Bruhat function** (every finite place, dyadic included; $\det P \ne 0$): a finite
sum of translates of $\mathbf 1_{\mathcal O_v^n}$, each a pure tensor of ball indicators. -/
theorem latInd_mem_Sn (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0) :
    latInd v P ∈ (localDataV v).Sn (2 * m) := by
  classical
  set k := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {P.det})).factors
  have hk : Valued.v (algebraMap (𝓞 F) Fv P.det) = exp (-(k : ℤ)) :=
    (HN.valued_algebraMap_int v P.det).trans (v.intValuation_if_neg hP)
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) k
  let _ : Fintype (RQ v k) := Fintype.ofFinite _
  have hfun : latInd v P = ∑ z : Fin (2 * m) → RQ v k,
      latInd v P (cosetCtr v k z) • ptensor (fun i => ballIndV v (cosetCtr v k z i) 0) := by
    funext y
    rw [latInd_eq_sum v P hk y, Finset.sum_apply]
    rfl
  rw [hfun]
  exact Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _
    (ptensor_mem_Sn fun i => ballIndV_mem_SBK v _)

/-- **$\Phi_v = \mathbf 1_{\mathcal O_v^n}$ when $\det P$ is a $v$-unit** ($P \in \mathrm{GL}_n(\mathcal O_v)$ preserves $\mathcal O_v^n$). -/
theorem latInd_eq_oneV (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F))
    (hP : Valued.v (algebraMap (𝓞 F) Fv P.det) = 1) : latInd v P = oneV v (2 * m) := by
  funext y
  unfold latInd
  rw [oneV_eq_ite', oneV_eq_ite']
  congr 1
  apply propext
  constructor
  · intro h i
    have := valued_piV_pow_mul_le_one v P (k := 0) (by rw [hP]; simp) h i
    simpa using this
  · intro h i
    exact valued_mulVec_le_one v P h i

lemma matV_det (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) :
    (matV v P).det = algebraMap (𝓞 F) Fv P.det :=
  ((algebraMap (𝓞 F) Fv).map_det P).symm

lemma algebraMap_det_ne_zero {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) :
    algebraMap (𝓞 F) Fv P.det ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
  exact (map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP)

/-- **The change of variables $x = Py$ on $F_v^n$**: for $\det P \ne 0$ and any $g$,
$\int_{F_v^n}g(Py)\,dy = |\det P|_v^{-1}\int_{F_v^n}g(x)\,dx$ (`map_mulVec_eq_glHaarChar_inv`, `glHaarChar_eq_of_field`). -/
theorem integral_comp_matV (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0)
    (g : (Fin (2 * m) → Fv) → ℂ) :
    ∫ y, g (matV v P *ᵥ y) ∂(localDataV v).muN (2 * m) =
      ((‖algebraMap (𝓞 F) Fv P.det‖⁻¹ : ℝ) : ℂ) * ∫ x, g x ∂(localDataV v).muN (2 * m) := by
  have hdet : (matV v P).det ≠ 0 := by rw [matV_det]; exact algebraMap_det_ne_zero v hP
  set M : GL (Fin (2 * m)) Fv := GeneralLinearGroup.mkOfDetNeZero (matV v P) hdet
  have hM : (M : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) = matV v P := rfl
  have hcont : ∀ A : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv, Continuous fun y : Fin (2 * m) → Fv => A *ᵥ y :=
    fun A => continuous_const.matrix_mulVec continuous_id
  let e : (Fin (2 * m) → Fv) ≃ᵐ (Fin (2 * m) → Fv) :=
    { toFun := fun y => (M : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) *ᵥ y
      invFun := fun y => ((M⁻¹ : GL (Fin (2 * m)) Fv) : Matrix (Fin (2 * m)) (Fin (2 * m)) Fv) *ᵥ y
      left_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      right_inv := fun y => by
        simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      measurable_toFun := (hcont _).measurable
      measurable_invFun := (hcont _).measurable }
  have hmu : (localDataV v).muN (2 * m) = Measure.pi fun _ : Fin (2 * m) => selfDualV v := rfl
  have : (Measure.pi fun _ : Fin (2 * m) => selfDualV v).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hmap := map_mulVec_eq_glHaarChar_inv (Measure.pi fun _ : Fin (2 * m) => selfDualV v) M
  rw [← hmu] at hmap
  rw [glHaarChar_eq_of_field] at hmap
  have hχ : ((distribHaarChar Fv (GeneralLinearGroup.det M) : NNReal) : ℝ) = ‖algebraMap (𝓞 F) Fv P.det‖ := by
    have hne : algebraMap (𝓞 F) Fv P.det ≠ 0 := algebraMap_det_ne_zero v hP
    have h1 : GeneralLinearGroup.det M = Units.mk0 _ hne := by
      ext; simp [M, matV_det]
    rw [h1, ← Analysis.Weil.modK_of_ne hne]
    exact modK_eq_norm v hne
  calc ∫ y, g (matV v P *ᵥ y) ∂(localDataV v).muN (2 * m)
      = ∫ y, g (e y) ∂(localDataV v).muN (2 * m) := rfl
    _ = ∫ x, g x ∂(Measure.map e ((localDataV v).muN (2 * m))) := (e.measurableEmbedding.integral_map _).symm
    _ = ∫ x, g x ∂((distribHaarChar Fv (GeneralLinearGroup.det M))⁻¹ • (localDataV v).muN (2 * m)) := by
        rw [← hmap]; rfl
    _ = _ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv, hχ, Complex.real_smul]

/-- $\langle d\rangle(y) = Q_0(Py)$ in $F_v$ when $Q_0\circ P = \langle d\rangle$. -/
lemma evalIn_compMat_matV (Q₀ : QuadForm (𝓞 F) (2 * m)) (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F))
    (y : Fin (2 * m) → Fv) : (Q₀.compMat P).evalIn Fv y = Q₀.evalIn Fv (matV v P *ᵥ y) := by
  rw [Lattices.evalIn_eq_eval_map, Lattices.evalIn_eq_eval_map, ← QuadForm.map_compMat, QuadForm.eval_compMat]

/-- **The local Gauss integral of the transported lattice**: if $Q_0\circ P = \langle d\rangle$, $\det P \ne 0$, then for $b \in F_v$
$$\int_{F_v^n}\psi_v\big(b\langle d\rangle(y)\big)\Phi_v(y)\,dy = |\det P|_v^{-1}\int_{\mathcal O_v^n}\psi_v\big(bQ_0(x)\big)\,dx.$$ -/
@[kb "weil1965" "Ch. II (the local factor of the Eisenstein series for a lattice) [unverified]"]
theorem integral_psiV_latInd (Q₀ : QuadForm (𝓞 F) (2 * m)) (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F))
    (hP : P.det ≠ 0) (b : Fv) :
    ∫ y, (psiV v (b * (Q₀.compMat P).evalIn Fv y) : ℂ) * latInd v P y ∂(localDataV v).muN (2 * m) =
      ((‖algebraMap (𝓞 F) Fv P.det‖⁻¹ : ℝ) : ℂ) *
        ∫ x, (psiV v (b * Q₀.evalIn Fv x) : ℂ) * oneV v (2 * m) x ∂(localDataV v).muN (2 * m) := by
  simp_rw [evalIn_compMat_matV v Q₀ P]
  exact integral_comp_matV v P hP fun x => (psiV v (b * Q₀.evalIn Fv x) : ℂ) * oneV v (2 * m) x

end Local

/-! ### The global lattice section and its Eisenstein series -/

section Global

open SingularNF HilbertModular QuadFormsKB.Lattices
open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

variable {m : ℕ} (a : Fin (2 * m) → Fˣ) (P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (hP : P.det ≠ 0)

/-- **The local datum** $\Phi_v = \mathbf 1_{P^{-1}\mathcal O_v^n}$ (`latInd`) as an element of the Schwartz–Bruhat space. -/
def latS (v : HeightOneSpectrum (𝓞 F)) : (localDataV v).Sn (2 * m) := ⟨latInd v P, latInd_mem_Sn v P hP⟩

/-- **The finite part of the lattice section**: $f_f^P(\gamma, s) = \prod_{v<\infty}f_v(\gamma_v, s)$, $f_v$ = `secS` for
$\Phi_v = \mathbf 1_{L'_v}$, $L' = P^{-1}\mathcal O_F^n$ (a finite product, `hasFiniteMulSupport_secSL`). For $P = 1$ it is `finSec`
(`finSecL_one`). -/
@[kb "kudla2008" "§1 (the standard section $\\Phi(s) = \\otimes_v\\Phi_v(s)$) [unverified]"]
def finSecL (γ : SL(2, F)) (s : ℂ) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), secS v (aV a v) (latS P hP v) (locSL v γ) s

/-- The finite places dividing $\det P$. -/
abbrev detPlaces : Finset (HeightOneSpectrum (𝓞 F)) := suppI (span_ne_bot hP)

lemma valued_det_eq_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ detPlaces P hP) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) P.det) = 1 := by
  have h0 : ordI v (Ideal.span {P.det}) = 0 := by
    by_contra h
    exact hv ((mem_suppI _ v).mpr ((ordI_ne_zero_iff (span_ne_bot hP) v).mp h))
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F, valued_algebraMap_eq_ordI v hP, h0]
  simp

lemma latS_eq_oneS {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ detPlaces P hP) : latS P hP v = oneS v m :=
  Subtype.ext (latInd_eq_oneV v P (valued_det_eq_one P hP hv))

lemma hasFiniteMulSupport_secSL (γ : SL(2, F)) (s : ℂ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      secS v (aV a v) (latS P hP v) (locSL v γ) s :=
  ((badPlaces_finite a γ).union (detPlaces P hP).finite_toSet).subset fun v hv => by
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, not_or] at h
    apply hv
    simp only
    rw [latS_eq_oneS P hP h.2]
    exact secS_eq_one_of_not_bad a h.1 s

lemma latInd_one (v : HeightOneSpectrum (𝓞 F)) :
    latInd v (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) = oneV v (2 * m) := by
  funext y
  simp [latInd, matV, Matrix.map_one]

lemma det_one_ne_zero : (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)).det ≠ 0 := by simp

/-- For $P = 1$ the lattice section is the standard one: $f_f^1 = f_f$ (`finSec`). -/
theorem finSecL_one (γ : SL(2, F)) (s : ℂ) : finSecL a 1 det_one_ne_zero γ s = finSec a γ s := by
  have h : ∀ v : HeightOneSpectrum (𝓞 F), latS (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) det_one_ne_zero v =
      oneS v m := fun v => Subtype.ext (latInd_one v)
  unfold finSecL finSec
  simp_rw [h]

/-- $f_v(1, s) = \Phi_v(0) = 1$ for the lattice datum. -/
lemma secS_latS_one (v : HeightOneSpectrum (𝓞 F)) (b : Fin (2 * m) → (v.adicCompletion F)ˣ) (s : ℂ) :
    secS v b (latS P hP v) 1 s = 1 := by
  have h0 : latInd v P 0 = 1 := by simp [latInd, oneV, ptensor, Analysis.ballIndV]
  simp only [secS, secV, sec_one]
  rw [show ((latS P hP v : (localDataV v).Sn (2 * m)) : (Fin (2 * m) → v.adicCompletion F) → ℂ) 0 = latInd v P 0
    from rfl, h0]
  simp [htV]

lemma finSecL_one_apply (s : ℂ) : finSecL a P hP 1 s = 1 := by
  simp [finSecL, map_one, secS_latS_one]

/-- **The Borel law of the lattice section** (place by place, `secS_borel`). -/
theorem finSecL_borel (β : F) (t : Fˣ) (γ : SL(2, F)) (s : ℂ) :
    finSecL a P hP (nMat β * mMat t * γ) s = (∏ᶠ v, borelFactorV a t s v) * finSecL a P hP γ s := by
  unfold finSecL
  rw [← finprod_mul_distrib (hasFiniteMulSupport_borelFactorV a t s) (hasFiniteMulSupport_secSL a P hP γ s)]
  congr 1; funext v
  rw [map_mul, map_mul, locSL_nMat, locSL_mMat, secS_borel]
  rfl

/-- **The global lattice section** $f^P(\gamma, s) = f_\infty(\gamma)\,f_f^P(\gamma, s)$. -/
def globalSecL (fInf : SL(2, F) → ℂ) (s : ℂ) (γ : SL(2, F)) : ℂ := fInf γ * finSecL a P hP γ s

/-- **The global lattice section is left $B(F)$-invariant** (Hilbert reciprocity and the product formula,
`borelFactor_prod_eq_one`). -/
theorem globalSecL_borel {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) {b : SL(2, F)}
    (hb : b ∈ borel F) (γ : SL(2, F)) : globalSecL a P hP fInf s (b * γ) = globalSecL a P hP fInf s γ := by
  have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
  set u : Fˣ := Units.mk0 _ (a_ne_zero_of_c_eq_zero hb')
  set x : F := (b : Matrix (Fin 2) (Fin 2) F) 0 1 / (b : Matrix (Fin 2) (Fin 2) F) 0 0
  have hbe : b = nMat ((u : F) ^ 2 * x) * mMat u := by
    rw [← mMat_nMat]; exact eq_cell_of_c_eq_zero b hb'
  unfold globalSecL
  rw [hbe, hInf, finSecL_borel]
  have := borelFactor_prod_eq_one a u s
  linear_combination (fInf γ * finSecL a P hP γ s) * this

/-- **The Siegel Eisenstein series of the lattice $L' = P^{-1}\mathcal O_F^n$**:
$E^P(s) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma)f_f^P(\gamma, s)$ (`tsum`, $0$ if not summable), i.e.
$E((g_\infty, 1), s, \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L'_v})$. For $P = 1$ it is `eisenstein` (`eisensteinL_one`). -/
@[kb "kudla2008" "§1 [unverified]; Weil (1965) [unverified]"]
def eisensteinL {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) : ℂ :=
  ∑' q : BQuot F, Quotient.lift (globalSecL a P hP fInf s) (fun g g' h => by
    have h' : QuotientGroup.rightRel (borel F) g g' := h
    rw [QuotientGroup.rightRel_apply] at h'
    have := globalSecL_borel a P hP hInf h' g
    rw [inv_mul_cancel_right] at this
    exact this.symm) q

/-- For $P = 1$, $E^P$ is the Eisenstein series `eisenstein` of $\mathcal O_F^n$. -/
theorem eisensteinL_one {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s) :
    eisensteinL a 1 det_one_ne_zero hInf = eisenstein a hInf := by
  unfold eisensteinL eisenstein
  congr 1; funext q
  induction q using Quotient.inductionOn with
  | h g => show globalSecL a 1 _ fInf s g = globalSec a fInf s g; rw [globalSecL, globalSec, finSecL_one]

/-- **The Bruhat expansion** of $E^P$: $E^P(s) = f_\infty(1) + \sum_{\beta\in F}f^P(wn(\beta), s)$ when the big-cell sum converges. -/
theorem eisensteinL_eq_bruhat {fInf : SL(2, F) → ℂ} {s : ℂ} (hInf : IsArchSection a fInf s)
    (hsum : Summable fun β : F => globalSecL a P hP fInf s (wMat * nMat β)) :
    eisensteinL a P hP hInf = fInf 1 + ∑' β : F, globalSecL a P hP fInf s (wMat * nMat β) := by
  unfold eisensteinL
  rw [← (bruhatEquiv (k := F)).tsum_eq]
  have hval : ∀ x : Unit ⊕ F, Quotient.lift (s := QuotientGroup.rightRel (borel F)) (globalSecL a P hP fInf s)
      (fun g g' h => by
        have h' : QuotientGroup.rightRel (borel F) g g' := h
        rw [QuotientGroup.rightRel_apply] at h'
        have := globalSecL_borel a P hP hInf h' g
        rw [inv_mul_cancel_right] at this
        exact this.symm) (bruhatEquiv (k := F) x) = globalSecL a P hP fInf s (bruhatRep x) := fun x => rfl
  simp only [hval]
  have h1 : HasSum (fun x : Unit ⊕ F => globalSecL a P hP fInf s (bruhatRep x))
      (fInf 1 + ∑' β : F, globalSecL a P hP fInf s (wMat * nMat β)) := by
    refine HasSum.sum ?_ hsum.hasSum
    have : (fun u : Unit => globalSecL a P hP fInf s (bruhatRep (Sum.inl u))) = fun _ => fInf 1 := by
      funext u; simp [bruhatRep, globalSecL, finSecL_one_apply]
    simp only [Function.comp_def, this]
    simp
  exact h1.tsum_eq

/-! ### The big cell at $s_0$: the Gauss average of $Q_0$ -/

variable (Q₀ : QuadForm (𝓞 F) (2 * m)) (d : Fin (2 * m) → 𝓞 F) (hd : ∀ i, d i ≠ 0)

lemma secV_latS_wMat_nMat (v : HeightOneSpectrum (𝓞 F)) (b : v.adicCompletion F) :
    secV v (aV (unitsOfInt d hd) v) (latS P hP v) (wMat * nMat b) =
      (localDataV v).gammaV (aV (unitsOfInt d hd) v) * (localDataV v).cB (aV (unitsOfInt d hd) v) *
        ∫ x, (psiV v (b * Qform (aV (unitsOfInt d hd) v) x) : ℂ) * latInd v P x
          ∂(localDataV v).muN (2 * m) := by
  unfold secV
  rw [sec_wMat_nMat]
  rfl

lemma norm_algebraMap_det (v : HeightOneSpectrum (𝓞 F)) :
    ‖algebraMap (𝓞 F) (v.adicCompletion F) P.det‖ = ‖algebraMap F (v.adicCompletion F) (ιO P.det)‖ := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]

/-- **The local section of the lattice on the big cell** (every finite place, dyadic included): if $Q_0\circ P = \langle d\rangle$ and
$|u|_v \le q_v^e$,
$$f_v(wn(u)) = \gamma_{V,v}c_{B,v}\operatorname{vol}(\mathcal O_v)^n\cdot|\det P|_v^{-1}\cdot A_v(Q_0; u, e).$$ -/
theorem secV_latS_eq_locAvg (hQP : Q₀.compMat P = QuadForm.diag d) (v : HeightOneSpectrum (𝓞 F)) (u : F) (e : ℕ)
    (hu : Valued.v (algebraMap F (v.adicCompletion F) u) ≤ exp (e : ℤ)) :
    secV v (aV (unitsOfInt d hd) v) (latS P hP v) (wMat * nMat (algebraMap F (v.adicCompletion F) u)) =
      ((localDataV v).gammaV (aV (unitsOfInt d hd) v) * (localDataV v).cB (aV (unitsOfInt d hd) v) *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ)) *
        ((‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ : ℝ) : ℂ) * locAvg v Q₀ u e := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) e
  let _ : Fintype (RQ v e) := Fintype.ofFinite _
  have hfin : Finite (𝓞 F ⧸ v.asIdeal ^ e) := finite_quot (pow_ne_zero _ v.ne_bot)
  let _ : Fintype (𝓞 F ⧸ v.asIdeal ^ e) := Fintype.ofFinite _
  rw [secV_latS_wMat_nMat]
  simp_rw [Qform_aV_eq_evalIn v d hd, ← hQP]
  rw [integral_psiV_latInd v Q₀ P hP, integral_psiV_oneV_of_congr v
    (fun x => algebraMap F (v.adicCompletion F) u * Q₀.evalIn (v.adicCompletion F) x) e
    (fun _ _ hx hx' hxx => psiV_evalIn_congr v Q₀ hu hx hx' hxx),
    sum_RQ_eq_sum_quot v Q₀ e hu, locAvg, finsum_eq_sum_of_fintype, selfDualV_real_latticeV_nat,
    norm_algebraMap_det]
  push_cast
  rw [mul_pow, inv_pow, ← pow_mul]
  ring

/-- **The finite lattice section on the big cell is the global Gauss average of $Q_0$** (every finite place, dyadic included):
if $Q_0\circ P = \langle d\rangle$ ($\det P \ne 0$), then for $u \in F$
$$f_f^P(wn(u), s_0) = \kappa_f(d)\cdot|N(\det P)|\cdot G_{Q_0}(-u),$$
$\kappa_f(d)$ = `kappaF` of the diagonal model, $G_{Q_0}$ = `SingularNF.gaussAvg`. *Proof:* the change of variables $x = Py$ at each
place (`integral_psiV_latInd`), the local Gauss averages of $Q_0$ (any form, `finprod_locAvg`) and the product formula
$\prod_v|\det P|_v^{-1} = |N(\det P)|$ (`finprod_normV`). -/
@[kb "weil1965" "Ch. II (the local factors of the Eisenstein series at the big cell) [unverified]; Siegel (1935), §3 (Gauss sums) [unverified]"]
theorem finSecL_wMat_nMat (hQP : Q₀.compMat P = QuadForm.diag d) (u : F) :
    finSecL (unitsOfInt d hd) P hP (wMat * nMat u) ((m : ℂ) - 1) =
      kappaF m (unitsOfInt d hd) * (normAbs (ιO P.det) : ℂ) * gaussAvg Q₀ (-u) := by
  classical
  set a := unitsOfInt d hd
  have hdet0 : ιO P.det ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      secS v (aV a v) (latS P hP v) (locSL v (wMat * nMat u)) ((m : ℂ) - 1) =
        ((localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
          (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ)) *
          ((‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ : ℝ) : ℂ) * locAvg v Q₀ u (denExp u v) := by
    intro v
    rw [map_mul, locSL_wMat, locSL_nMat, secS_s₀']
    exact secV_latS_eq_locAvg P hP Q₀ d hd hQP v u _ (valued_le_of_isDen v (den_ne_zero u) (isDen_den u))
  have hinv : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ := (hasFiniteMulSupport_normV hdet0).inv
  have hN : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ : ℝ) : ℂ) :=
    hinv.subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  have hprodN : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ : ℝ) : ℂ) =
      (normAbs (ιO P.det) : ℂ) := by
    have e := (map_finprod Complex.ofRealHom hinv).symm
    simp only [Complex.ofRealHom_eq_coe] at e
    rw [e, finprod_inv_distrib, finprod_normV hdet0, inv_inv]
  have hfg : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ)) *
        ((‖algebraMap F (v.adicCompletion F) (ιO P.det)‖⁻¹ : ℝ) : ℂ) := (hasFiniteMulSupport_kappa a).mul hN
  unfold finSecL
  simp_rw [hloc]
  rw [finprod_mul_distrib hfg (hasFiniteMulSupport_locAvg Q₀ u),
    finprod_mul_distrib (hasFiniteMulSupport_kappa a) hN, ← kappaF, hprodN, finprod_locAvg]

/-! ### The constants: $C_{Q_0} = C_{\langle d\rangle}\,|N(\det P)|$ -/

lemma det_map_map (X : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) (w : InfinitePlace F) :
    ((X.map ιO).map (realEmb F w)).det = realEmb F w (ιO X.det) := by
  rw [RingHom.map_det, RingHom.map_det]; rfl

omit [IsTotallyReal F] in
lemma gramF_compMat (Q : QuadForm (𝓞 F) (2 * m)) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)) :
    gramF (Q.compMat X) = (X.map ιO)ᵀ * gramF Q * X.map ιO := by
  rw [gramF, gramF, QuadForm.hessian_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.mul_smul, Matrix.smul_mul]

lemma det_gramF_compMat (Q : QuadForm (𝓞 F) (2 * m)) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F))
    (w : InfinitePlace F) :
    ((gramF (Q.compMat X)).map (realEmb F w)).det =
      realEmb F w (ιO X.det) ^ 2 * ((gramF Q).map (realEmb F w)).det := by
  rw [gramF_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.det_mul, Matrix.det_mul, Matrix.transpose_map,
    Matrix.det_transpose, det_map_map]
  ring

/-- **Positivity transfers to the diagonal model**: if $Q_0$ is totally positive definite and $Q_0\circ P = \langle d\rangle$ with
$\det P \ne 0$, then every $d_i$ is totally positive. -/
theorem pos_of_compMat {Q₀ : QuadForm (𝓞 F) (2 * m)} (hQ : IsTotallyPosDef (formF Q₀))
    {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) {d : Fin (2 * m) → 𝓞 F}
    (hQP : Q₀.compMat P = QuadForm.diag d) (i : Fin (2 * m)) (w : InfinitePlace F) :
    0 < realEmb F w (ιO (d i)) := by
  have h := isTotPosGram_Q₀ hQ w
  have hinj : Function.Injective ((P.map ιO).map (realEmb F w)).mulVec := by
    refine Matrix.mulVec_injective_iff_isUnit.mpr ?_
    rw [Matrix.isUnit_iff_isUnit_det, det_map_map]
    exact (isUnit_iff_ne_zero).mpr ((map_ne_zero _).mpr ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP))
  have h2 := h.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    ← gramF_compMat, hQP, gramF_diag, Matrix.diagonal_map (map_zero _)] at h2
  simpa using h2.diag_pos (i := i)

/-- **The theta constants**: $K_{\langle d\rangle}\,|N(\det P)| = K_{Q_0}$ when $Q_0\circ P = \langle d\rangle$, $\det P \ne 0$ (the determinant of the
Gram matrix scales by $\sigma_w(\det P)^2$ at each real place $w$). -/
theorem thetaK_compMat {Q₀ : QuadForm (𝓞 F) (2 * m)}
    {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) {d : Fin (2 * m) → 𝓞 F}
    (hQP : Q₀.compMat P = QuadForm.diag d) :
    thetaK (QuadForm.diag d) * normAbs (ιO P.det) = thetaK Q₀ := by
  have hS : ∀ w : InfinitePlace F, Real.sqrt ((gramF (QuadForm.diag d)).map (realEmb F w)).det =
      |realEmb F w (ιO P.det)| * Real.sqrt ((gramF Q₀).map (realEmb F w)).det := fun w => by
    rw [← hQP, det_gramF_compMat, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have h0 : normAbs (ιO P.det) ≠ 0 :=
    (normAbs_pos ((map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hP)).ne'
  unfold thetaK
  simp_rw [hS]
  rw [Finset.prod_mul_distrib, mul_inv, ← normAbs]
  field_simp

end Global

/-! ### The Siegel–Weil formula for every totally positive form over $\mathcal O_F$ -/

section Formula

open SingularNF HilbertModular QuadFormsKB.Lattices
open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

variable {m : ℕ}

/-- **The Siegel Eisenstein series of a lattice at $s_0$ is $\prod_wy_w^{m/2}$ times the Eisenstein series of the genus**, for every
totally positive definite form $Q_0$ over $\mathcal O_F$ (not necessarily diagonal; at dyadic places $\mathcal O_v^n$ need not have an
orthogonal basis): $F$ totally real, $n = 2m \ge 6$, $Q_0\circ P = \langle d_0, \dots, d_{n-1}\rangle$ a diagonalization over $\mathcal O_F$ with
$\det P \ne 0$ (one exists, `exists_diag_global`). In the diagonal model $(F^n, \langle d\rangle)$ the lattice $L = \mathcal O_F^n$ of $Q_0$ is
$L' = P^{-1}\mathcal O_F^n$, and with $\Phi = \varphi_\infty\otimes\bigotimes_v\mathbf 1_{L'_v}$ the adelic series
$E(g_z, s_0, \Phi)$ (`eisensteinL`) converges absolutely (its big-cell terms are absolutely summable) and
$$E(g_z, s_0, \Phi) = \prod_wy_w^{m/2}\cdot E_{Q_0}(z),$$
$E_{Q_0}$ = `eisQ`. *Proof:* Bruhat; on the big cell $f_f^P(wn(u), s_0) = \kappa_f(d)\,|N(\det P)|\,G_{Q_0}(-u)$ (`finSecL_wMat_nMat`);
$\kappa_f(d) = (-1)^{md}C_{\langle d\rangle}$ (`kappaF_eq`) and $C_{\langle d\rangle}|N(\det P)| = C_{Q_0}$ (`thetaK_compMat`); then the series $E_{Q_0}$ term by term.
No hypothesis on the genus: `GenusFree` holds for every totally positive form (`genusFree_formF`). -/
@[kb "weil1965" "Ch. II–IV (the Siegel Eisenstein series of a lattice, at s₀) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisensteinL_archSec_eq_eisQ (hm : 3 ≤ m) {Q₀ : QuadForm (𝓞 F) (2 * m)} (hQ : IsTotallyPosDef (formF Q₀))
    {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) {d : Fin (2 * m) → 𝓞 F} (hd : ∀ i, d i ≠ 0)
    (hQP : Q₀.compMat P = QuadForm.diag d) (z : InfinitePlace F → UpperHalfPlane) :
    (Summable fun u : F => ‖globalSecL (unitsOfInt d hd) P hP (archSec m z) ((m : ℂ) - 1) (wMat * nMat u)‖) ∧
      eisensteinL (unitsOfInt d hd) P hP (isArchSection_archSec d hd (pos_of_compMat hQ hP hQP) z) =
        (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * eisQ Q₀ m z := by
  classical
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  have hfree := genusFree_formF hQ
  have hn : 2 * m = 2 * m := rfl
  set f := thetaGen (formF Q₀) stdLat
  set W := eisGenWeight f (m : ℤ)
  set C := eisCst Q₀ m
  set Y := ∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)
  have hf : HasCuspLimits f (m : ℤ) := hasCuspLimits_thetaGen hQ hn hlev h𝔑 hfree
  have hW : EisWeight W (m : ℤ) :=
    eisWeight_eisGenWeight h𝔑 hf (thetaGen_mem_modularFormChar hQ hn hlev h𝔑 hfree).2
  have hsumO : Summable fun o : UOrbit F => ‖eisTerm W (m : ℤ) o.out (fun v => (z v : ℂ))‖ := by
    obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
    obtain ⟨h, hs, hbd⟩ := exists_summable_bound_hecke hW (s := 0) (by norm_num; omega)
      (∑ v, |(z v).re| + 1) hB
    refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) fun o => ?_
    rw [← heckeTerm_zero]
    refine hbd z (fun v => ⟨?_, (hBv v).le⟩) o
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith
  set g : F → ℂ := fun u => SingularNF.gaussAvg Q₀ (-u)
  set bt : F → ℂ := fun u => g u * eisDen ((1 : F), u) (fun v => (z v : ℂ)) ^ (-(m : ℤ))
  have hterm : ∀ u, eisTerm W (m : ℤ) (rho u).out (fun v => (z v : ℂ)) = C * bt u := by
    intro u
    rw [eisTerm_rho hf, phiF_thetaGen hQ hn hlev h𝔑 hfree, mul_assoc]
  have hC : C ≠ 0 := eisCst_ne_zero (isTotPosGram_Q₀ hQ) m
  have hbsum : Summable fun u => ‖bt u‖ := by
    have h1 := (hsumO.comp_injective rho_injective).mul_left ‖C‖⁻¹
    refine h1.congr fun u => ?_
    simp only [Function.comp, hterm, norm_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hC), one_mul]
  have hE : eisQ Q₀ m z = 1 + C * ∑' u, bt u := by
    rw [eisQ, eisGen, eisSeries, eisSeriesC_eq_const_add (fun v => (z v : ℂ)) hsumO,
      eisConst_eisQ_eq_one hQ hn hlev h𝔑 hfree, tsum_congr hterm, tsum_mul_left]
  -- the constants
  have hκ := kappaF_eq (by omega) d hd (pos_of_compMat hQ hP hQP)
  have hκ' : kappaF m (unitsOfInt d hd) * (normAbs (ιO P.det) : ℂ) =
      (-1) ^ (m * Fintype.card (InfinitePlace F)) * C := by
    rw [hκ]
    simp only [C, eisCst]
    rw [← thetaK_compMat hP hQP]
    push_cast; ring
  have hglob : ∀ u : F, globalSecL (unitsOfInt d hd) P hP (archSec m z) ((m : ℂ) - 1) (wMat * nMat u) =
      Y * C * bt u := by
    intro u
    rw [globalSecL, archSec_wMat_nMat, finSecL_wMat_nMat P hP Q₀ d hd hQP, hκ']
    have hsq : ((-1 : ℂ) ^ (m * Fintype.card (InfinitePlace F))) * (-1) ^ (m * Fintype.card (InfinitePlace F)) = 1 := by
      rw [← mul_pow]; norm_num
    simp only [bt, g, C, Y]
    linear_combination (Y * C * bt u) * hsq
  have hsum : Summable fun u : F =>
      ‖globalSecL (unitsOfInt d hd) P hP (archSec m z) ((m : ℂ) - 1) (wMat * nMat u)‖ := by
    refine (hbsum.mul_left ‖Y * C‖).congr fun u => ?_
    rw [hglob, norm_mul (Y * C)]
  refine ⟨hsum, ?_⟩
  rw [eisensteinL_eq_bruhat _ _ _ _ hsum.of_norm, archSec_one, tsum_congr hglob, tsum_mul_left, hE]
  ring

/-- **The Siegel–Weil formula in degree one for every totally positive form over $\mathcal O_F$, any class number** (given the named
input `PrincipalPrimeSupply F`): for $F$ totally real, $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2m \ge 6$ variables (not
necessarily diagonal, dyadic places included), a diagonalization $Q_0\circ P = \langle d\rangle$ ($\det P \ne 0$), $L' = P^{-1}\mathcal O_F^n$ and
$z \in \mathbb H^d$,
$$E(g_z, s_0, \varphi_\infty\otimes\textstyle\bigotimes_v\mathbf 1_{L'_v}) = \prod_wy_w^{m/2}\cdot\theta_{\mathrm{Gen}}(z),\qquad
  \theta_{\mathrm{Gen}} = \mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{\theta_M}{|O(M)|}.$$ -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula: Eisenstein series = theta integral), degree one, n ≥ 6 [unverified]; Siegel (1935), Hauptsatz [unverified]"]
theorem siegelWeil_formula_lattice (hm : 3 ≤ m) {Q₀ : QuadForm (𝓞 F) (2 * m)} (hQ : IsTotallyPosDef (formF Q₀))
    {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0) {d : Fin (2 * m) → 𝓞 F} (hd : ∀ i, d i ≠ 0)
    (hQP : Q₀.compMat P = QuadForm.diag d) (hPS : PrincipalPrimeSupply F) (z : InfinitePlace F → UpperHalfPlane) :
    eisensteinL (unitsOfInt d hd) P hP (isArchSection_archSec d hd (pos_of_compMat hQ hP hQP) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) * thetaGen (formF Q₀) stdLat z := by
  obtain ⟨𝔑, h𝔑, hlev⟩ := exists_isThetaLevelF (isTotPosGram_Q₀ hQ)
  rw [(eisensteinL_archSec_eq_eisQ hm hQ hP hd hQP z).2, thetaGen_eq_eisQ' hQ rfl hlev h𝔑 hPS hm]

/-- **The Siegel–Weil formula in degree one for every totally positive form over $\mathcal O_F$, class number one** (unconditional):
for $F$ totally real with $\mathcal O_F$ a principal ideal domain, $Q_0$ totally positive definite over $\mathcal O_F$ in $n = 2m \ge 6$ variables
(not necessarily diagonal; dyadic places included), $Q_0\circ P = \langle d\rangle$ with $\det P \ne 0$, and $z \in \mathbb H^d$,
$$E(g_z, s_0, \varphi_\infty\otimes\textstyle\bigotimes_v\mathbf 1_{L'_v}) = \prod_wy_w^{m/2}\cdot\mathrm{Mass}(L)^{-1}\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}
  \frac{\theta_M(z)}{|O(M)|},\qquad L' = P^{-1}\mathcal O_F^n,$$
the series absolutely convergent. -/
@[kb "weil1965" "Ch. IV (the Siegel–Weil formula), degree one, n ≥ 6, h_F = 1 [unverified]; Siegel (1935), Hauptsatz [unverified]"]
theorem siegelWeil_formula_lattice_of_pid [IsPrincipalIdealRing (𝓞 F)] (hm : 3 ≤ m) {Q₀ : QuadForm (𝓞 F) (2 * m)}
    (hQ : IsTotallyPosDef (formF Q₀)) {P : Matrix (Fin (2 * m)) (Fin (2 * m)) (𝓞 F)} (hP : P.det ≠ 0)
    {d : Fin (2 * m) → 𝓞 F} (hd : ∀ i, d i ≠ 0) (hQP : Q₀.compMat P = QuadForm.diag d)
    (z : InfinitePlace F → UpperHalfPlane) :
    eisensteinL (unitsOfInt d hd) P hP (isArchSection_archSec d hd (pos_of_compMat hQ hP hQP) z) =
      (∏ v, ((z v).im : ℂ) ^ ((m : ℂ) / 2)) *
        (((mass (formF Q₀) stdLat : ℝ) : ℂ)⁻¹ *
          ∑ c ∈ (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀)).toFinset,
            ((LatClass.autCard (formF Q₀) c : ℂ))⁻¹ * thetaLatt (formF Q₀) c.out.1 z) := by
  rw [siegelWeil_formula_lattice hm hQ hP hd hQP (principalPrimeSupply_of_pid F) z,
    thetaGen_eq_sum (genusClasses_finite hQ stdLat (isIntegral_stdLat Q₀))]
  simp [Finset.sum_apply, smul_eq_mul]

end Formula

end QuadFormsKB.SiegelWeil
