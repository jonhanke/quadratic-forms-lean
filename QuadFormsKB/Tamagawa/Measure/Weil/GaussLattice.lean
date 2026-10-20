import QuadFormsKB.Tamagawa.Measure.Weil.SL2Gauss

/-!
# Gaussians and lattices in $F_\infty^\iota$: Poisson summation and theta bounds

$F$ any number field, $V = F_\infty$ (Mathlib's mixed space), $W = V^\iota$ ($\iota$ finite) with the coordinate self-dual
measure $\mu = \mu_\infty^{\iota}$ (`muInfVec`) and the trace pairing $\beta(y,z) = \sum_i\operatorname{Tr}_\infty(y_iz_i)$
(`betaV`; the $\iota$-version of `betaW`).

* `betaV` is symmetric and **nondegenerate** (`betaV_nondegenerate`), so every basis has a $\beta$-dual basis
  (Mathlib's `BilinForm.dualBasis`) and the dual of a lattice is the span of the dual basis
  (`BilinForm.dualSubmodule_span_of_basis`).
* **The self-dual Gaussian** $G(y) = \prod_i g(y_i)$, $g$ = `gR`, as a Schwartz function (`gaussV`), with
  $G = e^{-\pi q}$ for the positive definite quadratic form $q(y) = \sum_i(\sum_{w\ \mathrm{real}}y_{i,w}^2 +
  2\sum_{w\ \mathrm{complex}}|y_{i,w}|^2)$ (`qV`, `gV_eq_exp`) and $\hat G = G$ for $\beta$ (`fourierV_gaussV`).
* **Poisson summation for every $\mathbb Z$-lattice** $L\subset W$ (`IsZLattice`): for the $\mathbb R$-basis $b$ of a
  $\mathbb Z$-basis of $L$ (`latBasis`),
  $$\sum_{z\in L}G(z) = \mu(P_b)^{-1}\sum_{\eta\in L^\vee}G(\eta),\qquad L^\vee = \{\eta : \beta(L,\eta)\subseteq\mathbb Z\}$$
  (`poisson_latGauss`; from `poisson_basis`).
* **Matrix bound** (`qV_mulVec_le`): $q(My)\le K(M)\,q(y)$, $K(M) = \sum_{i,j}\|M_{ij}\|^2$.

**Outside results used**: the Poisson formula for
$\mathbb Z^N\subset\mathbb R^N$ vendored from Sphere-Packing-Lean (via `poisson_basis`); Mathlib's
`LinearMap.BilinForm.dualBasis`, `LinearMap.BilinForm.dualSubmodule_span_of_basis` (dual lattice = span of the dual
basis), `Module.Basis.ofZLatticeBasis`, `ZLattice.module_free`, `MeasureTheory.integral_fintype_prod_eq_prod`
(Fubini for the Gaussian's Fourier transform) and `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Real
open scoped ENNReal NNReal Pointwise FourierTransform Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

local notation "V" => mixedSpace F

/-! ### The trace pairing on $V^\iota$ -/

variable (F ι) in
/-- $\beta(y, z) = \sum_i\operatorname{Tr}_\infty(y_iz_i)$ on $V^\iota$. -/
def betaV : LinearMap.BilinForm ℝ (ι → V) :=
  LinearMap.mk₂ ℝ (fun y z => ∑ i, Analysis.traceInf (y i * z i))
    (fun y₁ y₂ z => by simp only [Pi.add_apply, add_mul, Analysis.traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp only [Pi.smul_apply, smul_mul_assoc, Analysis.traceInf_smul, Finset.mul_sum, smul_eq_mul])
    (fun y z₁ z₂ => by simp only [Pi.add_apply, mul_add, Analysis.traceInf_add, Finset.sum_add_distrib])
    (fun c y z => by simp only [Pi.smul_apply, mul_smul_comm, Analysis.traceInf_smul, Finset.mul_sum, smul_eq_mul])

theorem betaV_apply (y z : ι → V) : betaV F ι y z = ∑ i, Analysis.traceInf (y i * z i) := rfl

theorem betaV_isSymm : (betaV F ι).IsSymm := ⟨fun y z => by simp only [betaV_apply, mul_comm]⟩

/-- $\operatorname{Tr}_\infty(y\bar y) = \sum_{w\ \mathrm{real}}y_w^2 + 2\sum_{w\ \mathrm{complex}}|y_w|^2$. -/
theorem traceInf_mul_star (y : V) :
    Analysis.traceInf (y * star y) = (∑ w, (y.1 w) ^ 2) + 2 * ∑ w, ‖y.2 w‖ ^ 2 := by
  simp only [Analysis.traceInf, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Prod.fst_star, Prod.snd_star,
    Pi.star_apply, star_trivial]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => by ring) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem sq_add_eq_zero_iff (y : V) : (∑ w, (y.1 w) ^ 2) + 2 * ∑ w, ‖y.2 w‖ ^ 2 = 0 ↔ y = 0 := by
  constructor
  · intro h
    have h1 : 0 ≤ ∑ w, (y.1 w) ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
    have h2 : 0 ≤ ∑ w, ‖y.2 w‖ ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
    have e1 : ∑ w, (y.1 w) ^ 2 = 0 := by linarith
    have e2 : ∑ w, ‖y.2 w‖ ^ 2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg _] at e1 e2
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp (e1 w (Finset.mem_univ _))
    · have := e2 w (Finset.mem_univ _)
      simpa using this
  · rintro rfl; simp

/-- **The trace pairing is nondegenerate.** -/
theorem betaV_nondegenerate : (betaV F ι).Nondegenerate := by
  have hl : ∀ y : ι → V, (∀ z, betaV F ι y z = 0) → y = 0 := by
    intro y hy
    funext i
    have := hy (Pi.single i (star (y i)))
    rw [betaV_apply, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero,
      traceInf_zero']) (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, traceInf_mul_star] at this
    exact (sq_add_eq_zero_iff _).mp this
  exact ⟨hl, fun z hz => hl z fun y => by rw [betaV_isSymm.eq]; exact hz y⟩

/-! ### The self-dual Gaussian -/

variable (F ι) in
/-- The Euclidean structure used to build the Gaussian on $V^\iota$. -/
def gaussTV : (ι → V) ≃L[ℝ] PiLp 2 (fun _ : ι => euclidean.mixedSpace F) :=
  (ContinuousLinearEquiv.piCongrRight fun _ => Analysis.gaussT (F := F)).trans
    (PiLp.continuousLinearEquiv 2 ℝ _).symm

theorem norm_gaussTV_sq (y : ι → V) : ‖gaussTV F ι y‖ ^ 2 = ∑ i, ‖Analysis.gaussT (y i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

variable (F ι) in
/-- **The self-dual Gaussian** on $V^\iota$ as a Schwartz function. -/
def gaussV : SchwartzMap (ι → V) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussTV F ι)
    (Analysis.gaussianSchwartz (π : ℂ) (by simp [Real.pi_pos]))

/-- $G(y) = \prod_i g(y_i)$. -/
def gV (y : ι → V) : ℝ := ∏ i, gR (y i)

/-- $q(y) = \sum_i(\sum_w y_{i,w}^2 + 2\sum_w|y_{i,w}|^2)$. -/
def qV (y : ι → V) : ℝ := ∑ i, ((∑ w, ((y i).1 w) ^ 2) + 2 * ∑ w, ‖(y i).2 w‖ ^ 2)

theorem qV_nonneg (y : ι → V) : 0 ≤ qV y :=
  Finset.sum_nonneg fun i _ => add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun w _ => sq_nonneg _))

theorem gV_eq_exp (y : ι → V) : gV y = Real.exp (-π * qV y) := by
  rw [gV, qV, Finset.mul_sum, Real.exp_sum]
  rfl

theorem gV_pos (y : ι → V) : 0 < gV y := Finset.prod_pos fun i _ => gR_pos _

theorem gV_le_one (y : ι → V) : gV y ≤ 1 := by
  rw [gV_eq_exp]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, qV_nonneg y])

theorem gV_zero : gV (0 : ι → V) = 1 := by simp [gV, gR_zero]

theorem gaussV_apply (y : ι → V) : gaussV F ι y = (gV y : ℂ) := by
  rw [gaussV, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    Analysis.gaussianSchwartz_apply, norm_gaussTV_sq, gV, Complex.ofReal_prod]
  simp_rw [Analysis.norm_gaussT_sq]
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gR, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem qV_eq_zero_iff (y : ι → V) : qV y = 0 ↔ y = 0 := by
  rw [qV, Finset.sum_eq_zero_iff_of_nonneg fun i _ => add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun w _ => sq_nonneg _))]
  simp only [Finset.mem_univ, true_imp_iff, sq_add_eq_zero_iff]
  exact ⟨fun h => funext h, fun h i => by rw [h]; rfl⟩

theorem qV_smul (c : ℝ) (y : ι → V) : qV (c • y) = c ^ 2 * qV y := by
  simp only [qV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.real_smul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, mul_add, Finset.mul_sum]
  exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun w _ => by ring)

theorem gV_smul (c : ℝ) (y : ι → V) : gV (c • y) = Real.exp (-π * c ^ 2 * qV y) := by
  rw [gV_eq_exp, qV_smul]; ring_nf

theorem addChar_finset_sum {κ : Type*} (ψ : AddChar ℝ Circle) (s : Finset κ) (f : κ → ℝ) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, ih, Finset.prod_insert ha]

/-- **The Fourier transform of the self-dual Gaussian is itself**: $\int_W G(y)e(\beta(y,z))\,d\mu(y) = G(z)$. -/
theorem fourierV_gaussV (z : ι → V) :
    ∫ y, gaussV F ι y * ((𝐞 (betaV F ι y z) : Circle) : ℂ) ∂muInfVec F ι = (gV z : ℂ) := by
  have hfun : (fun y : ι → V => gaussV F ι y * ((𝐞 (betaV F ι y z) : Circle) : ℂ)) =
      fun y => ∏ i, ((gR (y i) : ℂ) * (Analysis.psiInf (y i * z i) : ℂ)) := by
    funext y
    rw [gaussV_apply, gV, betaV_apply, addChar_finset_sum, Complex.ofReal_prod]
    have hc : ((∏ i, 𝐞 (Analysis.traceInf (y i * z i)) : Circle) : ℂ) =
        ∏ i, ((𝐞 (Analysis.traceInf (y i * z i)) : Circle) : ℂ) := map_prod Circle.coeHom _ _
    rw [hc, ← Finset.prod_mul_distrib]
    rfl
  rw [hfun, muInfVec, integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun (i : ι) (y : V) => (gR y : ℂ) * (Analysis.psiInf (y * z i) : ℂ))]
  have hi : ∀ i : ι, ∫ y, (gR y : ℂ) * (Analysis.psiInf (y * z i) : ℂ) ∂Analysis.selfDualInf = (gR (z i) : ℂ) := by
    intro i
    have h := fourierInf_gR_mul (F := F) 1 (z i)
    simp only [Units.val_one, one_mul, inv_one] at h
    rw [show modInf (1 : Vˣ) = 1 by rw [modInf, map_one, NNReal.coe_one], inv_one, one_mul] at h
    exact h
  simp_rw [hi, gV]
  push_cast
  rfl

/-! ### Lattices: bases, duals, Poisson summation -/

section Lattice

variable (L : Submodule ℤ (ι → mixedSpace F)) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The rank of the lattice. -/
def latN : ℕ := Module.finrank ℤ L

/-- A $\mathbb Z$-basis of $L$, indexed by `Fin (latN L)`. -/
def latZBasis : Module.Basis (Fin (latN L)) ℤ L :=
  haveI := ZLattice.module_free ℝ L
  haveI := ZLattice.module_finite ℝ L
  Module.finBasis ℤ L

/-- The $\mathbb R$-basis of $W$ given by a $\mathbb Z$-basis of $L$. -/
def latBasis : Module.Basis (Fin (latN L)) ℝ (ι → V) := (latZBasis L).ofZLatticeBasis ℝ L

/-- The $\beta$-dual basis. -/
def latDual : Module.Basis (Fin (latN L)) ℝ (ι → V) := (betaV F ι).dualBasis betaV_nondegenerate (latBasis L)

theorem latBasis_apply (j : Fin (latN L)) : latBasis L j = (latZBasis L j : ι → V) :=
  Module.Basis.ofZLatticeBasis_apply ℝ L _ j

theorem span_latBasis : Submodule.span ℤ (Set.range (latBasis L)) = L :=
  Module.Basis.ofZLatticeBasis_span ℝ L _

theorem betaV_latBasis_latDual (i j : Fin (latN L)) :
    betaV F ι (latBasis L i) (latDual L j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right betaV_nondegenerate betaV_isSymm _ i j

/-- **The dual lattice** $L^\vee = \{\eta : \beta(L,\eta)\subseteq\mathbb Z\}$ is spanned by the dual basis. -/
theorem dualSubmodule_eq_span :
    (betaV F ι).dualSubmodule L = Submodule.span ℤ (Set.range (latDual L)) := by
  conv_lhs => rw [← span_latBasis L]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis _ betaV_nondegenerate _

theorem mem_dualSubmodule_iff {η : ι → V} :
    η ∈ (betaV F ι).dualSubmodule L ↔ ∀ z ∈ L, ∃ n : ℤ, betaV F ι η z = n := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one]
  exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← hn]; rfl⟩, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; rfl⟩⟩

/-- Sums over $L$ are sums over $\mathbb Z^N$ in the basis `latBasis`. -/
theorem tsum_lattice (f : (ι → V) → ℝ≥0∞) :
    ∑' z : L, f z = ∑' k : Fin (latN L) → ℤ, f (∑ j, (k j : ℝ) • latBasis L j) := by
  rw [← (latZBasis L).equivFun.symm.toEquiv.tsum_eq]
  refine tsum_congr fun k => ?_
  congr 1
  simp only [LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    latBasis_apply]
  exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℝ _ _).symm

theorem linearIndependent_latDual : LinearIndependent ℤ (latDual L) :=
  (latDual L).linearIndependent.restrict_scalars' ℤ

/-- Sums over $L^\vee$ are sums over $\mathbb Z^N$ in the dual basis. -/
theorem tsum_dual (f : (ι → V) → ℝ≥0∞) :
    ∑' η : (betaV F ι).dualSubmodule L, f η = ∑' m : Fin (latN L) → ℤ, f (∑ j, (m j : ℝ) • latDual L j) := by
  set B := Module.Basis.span (linearIndependent_latDual L)
  let e : (betaV F ι).dualSubmodule L ≃ Submodule.span ℤ (Set.range (latDual L)) :=
    (LinearEquiv.ofEq _ _ (dualSubmodule_eq_span L)).toEquiv
  rw [← e.symm.tsum_eq, ← B.equivFun.symm.toEquiv.tsum_eq]
  refine tsum_congr fun m => ?_
  congr 1
  have hcoe : ((e.symm (B.equivFun.symm.toEquiv m) : (betaV F ι).dualSubmodule L) : ι → V) =
      ((B.equivFun.symm m : Submodule.span ℤ (Set.range (latDual L))) : ι → V) := rfl
  rw [hcoe]
  simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul, B, Module.Basis.span_apply]
  exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℝ _ _).symm

theorem summable_gV_basis {N : ℕ} (b : Module.Basis (Fin N) ℝ (ι → V)) :
    Summable fun k : Fin N → ℤ => gV (∑ j, (k j : ℝ) • b j) := by
  have h := summable_basis b (gaussV F ι)
  refine h.congr fun k => ?_
  rw [gaussV_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gV_pos _)]

/-- **Poisson summation for the Gaussian on a lattice**:
$\sum_{z\in L}G(z) = \mu(P_b)^{-1}\sum_{\eta\in L^\vee}G(\eta)$, $b$ = `latBasis L`. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem poisson_latGauss :
    ∑' z : L, ENNReal.ofReal (gV (z : ι → V)) = (muInfVec F ι (latBasis L).parallelepiped)⁻¹ *
      ∑' η : (betaV F ι).dualSubmodule L, ENNReal.ofReal (gV (η : ι → V)) := by
  rw [tsum_lattice L (fun z => ENNReal.ofReal (gV z)), tsum_dual L (fun z => ENNReal.ofReal (gV z))]
  have hP := poisson_basis (muInfVec F ι) (latBasis L) (betaV F ι) (latDual L) (betaV_latBasis_latDual L)
    (gaussV F ι) 0
  simp only [fourierV_gaussV] at hP
  simp only [zero_add, map_zero, LinearMap.zero_apply, neg_zero, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one, gaussV_apply] at hP
  have h1 := summable_gV_basis (latBasis L)
  have h2 := summable_gV_basis (latDual L)
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_mul] at hP
  have hreal := Complex.ofReal_injective hP
  have hμ0 : muInfVec F ι (latBasis L).parallelepiped ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ (latBasis L).parallelepiped.interior_nonempty).ne'
  have hμT : muInfVec F ι (latBasis L).parallelepiped ≠ ⊤ := (latBasis L).parallelepiped.isCompact.measure_lt_top.ne
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (gV_pos _).le) h1,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => (gV_pos _).le) h2, hreal,
    ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.ofReal_inv_of_pos
      (ENNReal.toReal_pos hμ0 hμT), ENNReal.ofReal_toReal hμT]

end Lattice

/-! ### Matrices over $V$: the adjoint for $\beta$ and the bound $q(My)\le K(M)q(y)$ -/

section Matrix

open Matrix

theorem traceInf_finset_sum {κ : Type*} (s : Finset κ) (f : κ → V) :
    Analysis.traceInf (∑ k ∈ s, f k) = ∑ k ∈ s, Analysis.traceInf (f k) :=
  map_sum Analysis.traceInfL f s

/-- **The $\beta$-adjoint of a matrix is its transpose**: $\beta(My, z) = \beta(y, M^{\mathsf T}z)$. -/
theorem betaV_mulVec (M : Matrix ι ι V) (y z : ι → V) :
    betaV F ι (M *ᵥ y) z = betaV F ι y (M.transpose *ᵥ z) := by
  simp only [betaV_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum,
    traceInf_finset_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring_nf

/-- $K(M) = \sum_{i,j}\|M_{ij}\|^2$ (sup norm on $V$). -/
def matK (M : Matrix ι ι V) : ℝ := ∑ i, ∑ j, ‖M i j‖ ^ 2

theorem matK_nonneg (M : Matrix ι ι V) : 0 ≤ matK M :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem matK_transpose (M : Matrix ι ι V) : matK M.transpose = matK M := by
  rw [matK, matK, Finset.sum_comm]; rfl

theorem matK_smul (c : ℝ) (M : Matrix ι ι V) : matK (c • M) = c ^ 2 * matK M := by
  simp only [matK, Matrix.smul_apply, _root_.norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem norm_fst_apply_le (m : V) (w : {w : InfinitePlace F // w.IsReal}) : |m.1 w| ≤ ‖m‖ :=
  (norm_le_pi_norm m.1 w).trans (norm_fst_le m)

theorem norm_snd_apply_le (m : V) (w : {w : InfinitePlace F // w.IsComplex}) : ‖m.2 w‖ ≤ ‖m‖ :=
  (norm_le_pi_norm m.2 w).trans (norm_snd_le m)

/-- One coordinate of the bound: for a row $(M_{ij})_j$,
$q_1(\sum_jM_{ij}y_j)\le(\sum_j\|M_{ij}\|^2)\sum_jq_1(y_j)$. -/
theorem q1_sum_le (m y : ι → V) :
    (∑ w, ((∑ j, m j * y j).1 w) ^ 2) + 2 * ∑ w, ‖(∑ j, m j * y j).2 w‖ ^ 2 ≤
      (∑ j, ‖m j‖ ^ 2) * ∑ j, ((∑ w, ((y j).1 w) ^ 2) + 2 * ∑ w, ‖(y j).2 w‖ ^ 2) := by
  have hreal : ∀ w, ((∑ j, m j * y j).1 w) ^ 2 ≤ (∑ j, ‖m j‖ ^ 2) * ∑ j, ((y j).1 w) ^ 2 := by
    intro w
    have h1 : (∑ j, m j * y j).1 w = ∑ j, (m j).1 w * (y j).1 w := by
      simp [Prod.fst_sum, Finset.sum_apply]
    rw [h1]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg fun j _ => sq_nonneg _))
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (norm_fst_apply_le _ w) 2
  have hcplx : ∀ w, ‖(∑ j, m j * y j).2 w‖ ^ 2 ≤ (∑ j, ‖m j‖ ^ 2) * ∑ j, ‖(y j).2 w‖ ^ 2 := by
    intro w
    have h1 : (∑ j, m j * y j).2 w = ∑ j, (m j).2 w * (y j).2 w := by
      simp [Prod.snd_sum, Finset.sum_apply]
    rw [h1]
    calc ‖∑ j, (m j).2 w * (y j).2 w‖ ^ 2 ≤ (∑ j, ‖(m j).2 w‖ * ‖(y j).2 w‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
      _ ≤ (∑ j, ‖(m j).2 w‖ ^ 2) * ∑ j, ‖(y j).2 w‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_snd_apply_le _ w) 2)
          (Finset.sum_nonneg fun j _ => sq_nonneg _)
  calc (∑ w, ((∑ j, m j * y j).1 w) ^ 2) + 2 * ∑ w, ‖(∑ j, m j * y j).2 w‖ ^ 2
      ≤ (∑ w, (∑ j, ‖m j‖ ^ 2) * ∑ j, ((y j).1 w) ^ 2) +
          2 * ∑ w, (∑ j, ‖m j‖ ^ 2) * ∑ j, ‖(y j).2 w‖ ^ 2 := by
        gcongr with w _ w _
        · exact hreal w
        · exact hcplx w
    _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (f := fun w j => ((y j).1 w) ^ 2),
          Finset.sum_comm (f := fun w j => ‖(y j).2 w‖ ^ 2), Finset.sum_add_distrib, ← Finset.mul_sum]
        ring

/-- **$q(My)\le K(M)\,q(y)$.** -/
theorem qV_mulVec_le (M : Matrix ι ι V) (y : ι → V) : qV (M *ᵥ y) ≤ matK M * qV y := by
  rw [qV, matK, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := q1_sum_le (M i) y
  simpa [Matrix.mulVec, dotProduct, qV] using this

end Matrix

/-! ### The theta tail bound -/

section Theta

variable (L₀ : Submodule ℤ (ι → mixedSpace F)) [DiscreteTopology L₀] [IsZLattice ℝ L₀]

/-- The scaled Gaussian $e^{-\pi q(\zeta)/K}$ has finite sum over the dual lattice. -/
theorem tsum_dual_exp_ne_top {K : ℝ} (hK : 0 < K) :
    ∑' ζ : (betaV F ι).dualSubmodule L₀, ENNReal.ofReal (Real.exp (-π * qV (ζ : ι → V) / K)) ≠ ⊤ := by
  set c : ℝ := (Real.sqrt K)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hK).ne'
  have hc2 : c ^ 2 = K⁻¹ := by rw [inv_pow, Real.sq_sqrt hK.le]
  set b' : Module.Basis (Fin (latN L₀)) ℝ (ι → V) := (latDual L₀).map (LinearEquiv.smulOfNeZero ℝ _ c hc)
  have hb' : ∀ j, b' j = c • latDual L₀ j := fun j => rfl
  rw [tsum_dual L₀ (fun ζ => ENNReal.ofReal (Real.exp (-π * qV ζ / K)))]
  have hval : ∀ m : Fin (latN L₀) → ℤ, Real.exp (-π * qV (∑ j, (m j : ℝ) • latDual L₀ j) / K) =
      gV (∑ j, (m j : ℝ) • b' j) := by
    intro m
    simp_rw [hb', smul_comm _ c, ← Finset.smul_sum]
    rw [gV_smul, hc2]; ring_nf
  simp_rw [hval]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => (gV_pos _).le) (summable_gV_basis b')]
  exact ENNReal.ofReal_ne_top

theorem exp_qV_lt_one {K : ℝ} (hK : 0 < K) {ζ : ι → V} (hζ : ζ ≠ 0) : Real.exp (-π * qV ζ / K) < 1 := by
  have hq : 0 < qV ζ := lt_of_le_of_ne (qV_nonneg ζ) (fun h => hζ ((qV_eq_zero_iff ζ).mp h.symm))
  have : 0 < π * qV ζ / K := div_pos (mul_pos Real.pi_pos hq) hK
  exact Real.exp_lt_one_iff.mpr (by linarith [show -π * qV ζ / K = -(π * qV ζ / K) by ring])

/-- **The theta tail bound**: there are $0\le\delta < 1$ and $\Theta < \infty$ with
$\sum_{0\ne\zeta\in L_0^\vee}e^{-\pi\lambda q(\zeta)/K}\le\delta^{\lambda-1}\Theta$ for every $\lambda\ge1$. -/
theorem theta_tail_bound {K : ℝ} (hK : 0 < K) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 ∧ ∃ Θ : ℝ≥0∞, Θ ≠ ⊤ ∧ ∀ l : ℝ, 1 ≤ l →
      ∑' ζ : (betaV F ι).dualSubmodule L₀, (if (ζ : ι → V) = 0 then 0 else
        ENNReal.ofReal (Real.exp (-π * l * qV (ζ : ι → V) / K))) ≤ ENNReal.ofReal (δ ^ (l - 1)) * Θ := by
  set g : (betaV F ι).dualSubmodule L₀ → ℝ := fun ζ => Real.exp (-π * qV (ζ : ι → V) / K) with hg
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ => (Real.exp_pos _).le
  have hfin := tsum_dual_exp_ne_top L₀ hK
  -- the finitely many ζ with g ζ ≥ 1/2
  have hcof := ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hfin
  have hev : ∀ᶠ ζ in cofinite, ENNReal.ofReal (g ζ) < ENNReal.ofReal (1 / 2) :=
    hcof.eventually (gt_mem_nhds (by norm_num))
  set S : Set ((betaV F ι).dualSubmodule L₀) := {ζ | ¬ ENNReal.ofReal (g ζ) < ENNReal.ofReal (1 / 2)}
  have hS : S.Finite := hev
  set T : Set ℝ := g '' {ζ ∈ S | (ζ : ι → V) ≠ 0}
  have hT : T.Finite := (hS.subset fun ζ hζ => hζ.1).image g
  set δ : ℝ := max (1 / 2) (sSup T)
  have hT1 : sSup T < 1 := by
    rcases T.eq_empty_or_nonempty with he | hne
    · rw [he, Real.sSup_empty]; norm_num
    · rw [hT.csSup_lt_iff hne]
      rintro _ ⟨ζ, ⟨_, hζ0⟩, rfl⟩
      exact exp_qV_lt_one hK hζ0
  have hδ1 : δ < 1 := max_lt (by norm_num) hT1
  have hδ0 : 0 ≤ δ := le_max_of_le_left (by norm_num)
  have hgδ : ∀ ζ : (betaV F ι).dualSubmodule L₀, (ζ : ι → V) ≠ 0 → g ζ ≤ δ := by
    intro ζ hζ
    by_cases h : ENNReal.ofReal (g ζ) < ENNReal.ofReal (1 / 2)
    · have := (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mp h
      exact this.le.trans (le_max_left _ _)
    · exact (le_csSup hT.bddAbove ⟨ζ, ⟨h, hζ⟩, rfl⟩).trans (le_max_right _ _)
  refine ⟨δ, hδ0, hδ1, _, hfin, fun l hl => ?_⟩
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ζ => ?_
  split_ifs with hζ
  · exact bot_le
  · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ0 _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : Real.exp (-π * l * qV (ζ : ι → V) / K) = g ζ ^ l := by
      rw [hg, ← Real.exp_mul]; ring_nf
    rw [h1, show g ζ ^ l = g ζ ^ (l - 1) * g ζ by
      rw [← Real.rpow_add_one' (hg0 ζ) (by linarith)]; ring_nf]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hg0 ζ) (hgδ ζ hζ) (by linarith)) (hg0 ζ)

end Theta

/-! ### Poisson summation for the $\mathbb Z$-span of any basis -/

section BasisLattice

variable {N : ℕ} (b : Module.Basis (Fin N) ℝ (ι → mixedSpace F))

/-- The $\beta$-dual basis of `b`. -/
def basisDual : Module.Basis (Fin N) ℝ (ι → V) := (betaV F ι).dualBasis betaV_nondegenerate b

theorem betaV_basis_basisDual (i j : Fin N) : betaV F ι (b i) (basisDual b j) = if i = j then 1 else 0 :=
  LinearMap.BilinForm.apply_dualBasis_right betaV_nondegenerate betaV_isSymm _ i j

theorem dualSubmodule_span_eq :
    (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b)) = Submodule.span ℤ (Set.range (basisDual b)) :=
  LinearMap.BilinForm.dualSubmodule_span_of_basis _ betaV_nondegenerate _

theorem tsum_span_basis (b' : Module.Basis (Fin N) ℝ (ι → V)) (f : (ι → V) → ℝ≥0∞) :
    ∑' z : Submodule.span ℤ (Set.range b'), f z = ∑' k : Fin N → ℤ, f (∑ j, (k j : ℝ) • b' j) := by
  set B := Module.Basis.span (b'.linearIndependent.restrict_scalars' ℤ)
  rw [← B.equivFun.symm.toEquiv.tsum_eq]
  refine tsum_congr fun k => ?_
  congr 1
  simp only [LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    B, Module.Basis.span_apply]
  exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℝ _ _).symm

theorem tsum_dual_basis (f : (ι → V) → ℝ≥0∞) :
    ∑' η : (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b)), f η =
      ∑' m : Fin N → ℤ, f (∑ j, (m j : ℝ) • basisDual b j) := by
  let e : (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b)) ≃
      Submodule.span ℤ (Set.range (basisDual b)) := (LinearEquiv.ofEq _ _ (dualSubmodule_span_eq b)).toEquiv
  rw [← e.symm.tsum_eq]
  exact tsum_span_basis (basisDual b) f

/-- **Poisson summation for the Gaussian on the lattice of a basis**:
$\sum_{z\in L_b}G(z) = \mu(P_b)^{-1}\sum_{\eta\in L_b^\vee}G(\eta)$, $L_b = \mathbb Zb_1 + \cdots + \mathbb Zb_N$. -/
@[kb "serre1973" "Ch. VII §6.1, Poisson formula [unverified]"]
theorem poisson_basisGauss :
    ∑' z : Submodule.span ℤ (Set.range b), ENNReal.ofReal (gV (z : ι → V)) =
      (muInfVec F ι b.parallelepiped)⁻¹ *
        ∑' η : (betaV F ι).dualSubmodule (Submodule.span ℤ (Set.range b)), ENNReal.ofReal (gV (η : ι → V)) := by
  rw [tsum_span_basis b (fun z => ENNReal.ofReal (gV z)), tsum_dual_basis b (fun z => ENNReal.ofReal (gV z))]
  have hP := poisson_basis (muInfVec F ι) b (betaV F ι) (basisDual b) (betaV_basis_basisDual b) (gaussV F ι) 0
  simp only [fourierV_gaussV] at hP
  simp only [zero_add, map_zero, LinearMap.zero_apply, neg_zero, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one, gaussV_apply] at hP
  have h1 := summable_gV_basis b
  have h2 := summable_gV_basis (basisDual b)
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, ← Complex.ofReal_mul] at hP
  have hreal := Complex.ofReal_injective hP
  have hμ0 : muInfVec F ι b.parallelepiped ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ b.parallelepiped.interior_nonempty).ne'
  have hμT : muInfVec F ι b.parallelepiped ≠ ⊤ := b.parallelepiped.isCompact.measure_lt_top.ne
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (gV_pos _).le) h1,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => (gV_pos _).le) h2, hreal,
    ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.ofReal_inv_of_pos
      (ENNReal.toReal_pos hμ0 hμT), ENNReal.ofReal_toReal hμT]

end BasisLattice

end

end QuadFormsKB.Tamagawa.Measure.Weil
