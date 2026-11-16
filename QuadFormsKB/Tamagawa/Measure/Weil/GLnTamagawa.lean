import QuadFormsKB.Tamagawa.Measure.Weil.SLnHaar
import QuadFormsKB.Tamagawa.Measure.Weil.SLnTamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Finite
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleClassVolume
import QuadFormsKB.Tamagawa.Measure.Weil.Fujisaki
import QuadFormsKB.Tamagawa.Measure.Weil.CovolumeTransport
import QuadFormsKB.Tamagawa.Unitary.OnoReduction

/-!
# $\tau(\mathrm{GL}_n) = 1$ over every number field

$F$ is a number field, $\mathbb A = \mathbb A_F$, $n = k + 1\ge1$ the size of the matrices (indices $0,\dots,n-1$).

**The groups.**
* `GLA F k` $=\mathrm{GL}_n(\mathbb A)$ (Mathlib's units of $M_n(\mathbb A)$, with the units topology);
* `GLOne F k` $=\mathrm{GL}_n(\mathbb A)^1 = \{g : \|\det g\|_{\mathbb A} = 1\}$, a closed subgroup;
* `detOne F k` $:\mathrm{GL}_n(\mathbb A)^1\to\mathbb A^1$ (the determinant), surjective (`detOne_surjective`, section
  $t\mapsto\operatorname{diag}(t, 1, \dots, 1)$, `diagSec`), with kernel $\mathrm{SL}_n(\mathbb A)$ (`kerEquivSL`);
* `GammaGL F k` $=\mathrm{GL}_n(F)$ diagonally in $\mathrm{GL}_n(\mathbb A)^1$ (product formula), discrete.

**The Tamagawa measure** (Weil 1982, §2.4, Thm 2.4.4 and §3.1 for $\mathbb G_m$; convergence factors
$\lambda_v = 1 - q_v^{-1}$ and global factor $\rho_F^{-1}$, $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$): the gauge form
of $\mathrm{GL}_n$ is $\omega_{\mathrm{SL}_n}\wedge\det^*(dx/x)$, so the Tamagawa measure of $\mathrm{GL}_n(\mathbb A)^1$ is
$$\mu_{\mathrm{GL}_n}^1 = \rho_F^{-1}\int_{\mathbb A^1}(g_t\cdot)_*\mu_{\mathrm{SL}_n}\,d\mu^1(t),\qquad \det g_t = t,$$
with $\mu_{\mathrm{SL}_n}$ the Tamagawa measure of $\mathrm{SL}_n(\mathbb A)$ (`SLn.muSL`, no convergence factors) and
$\mu^1$ the norm-one part of $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ on $\mathbb A^\times$ (`muIdeleOne`,
$\mu = \mu^1\times dt/t$). This is `muGL F k` (Weil's fibred measure `NormalFib.fibMeas`, section-free).

**Main results.**
* `map_adK_muSLK` (unimodularity input of the fibration): conjugation by every $g\in\mathrm{GL}_n(\mathbb A)^1$ preserves
  $\mu_{\mathrm{SL}_n}$. *Proof:* $\operatorname{Ad}(g)_*\mu_{\mathrm{SL}_n} = c(g)\,\mu_{\mathrm{SL}_n}$ (Haar uniqueness);
  $c$ is multiplicative, $c = 1$ on $\mathrm{SL}_n(\mathbb A)$ (unimodular: it has the lattice $\mathrm{SL}_n(F)$) and on
  $\mathrm{GL}_n(F)$ ($\operatorname{Ad}(\gamma)$ preserves $\mathrm{SL}_n(F)$, hence the covolume $1$); $c$ is bounded on
  the compact set $\operatorname{diag}(C,1,\dots,1)$, $C$ Fujisaki's compact set with $\mathbb A^1 = F^\times C$
  (`exists_isCompact_ideleOne_mul_mem`); a bounded subgroup of $\mathbb R_{>0}$ is trivial.
* **`tamagawa_GLn`**: $\tau(\mathrm{GL}_n) = \operatorname{vol}(\mathrm{GL}_n(F)\backslash\mathrm{GL}_n(\mathbb A)^1,
  \mu^1_{\mathrm{GL}_n}) = 1$ for every $n\ge1$ and every number field. *Proof:* Weil's fibration
  (`Unitary.covolume_fibMeas`): $\operatorname{covol} = \rho_F^{-1}\cdot\tau(\mathrm{SL}_n)\cdot
  \operatorname{vol}(F^\times\backslash\mathbb A^1,\mu^1) = \rho_F^{-1}\cdot1\cdot\rho_F$ (`SLn.tamagawa_SLn`,
  `muIdeleClass_univ_eq_residue`).

*Normalization note.* As for $\mathrm{SL}_n$ ($n\ge3$) and $\mathrm{SL}_1(D)$ in this library, the Tamagawa measure is
defined through Weil's fibration theorem (Thm 2.4.4) rather than as a restricted product of local measures
$|\omega|_v$; the comparison with the local product ("box computation") is not formalized here (loose end).

Sources: Weil, *Adeles and Algebraic Groups* (1982), §2.4 Thm 2.4.4, §3.1 Thm 3.1.1 (iii), Ch. III
($\tau(\mathrm{GL}_n) = \tau(\mathrm{SL}_n)\,\tau(\mathbb G_m) = 1$) [unverified locators].
-/

open IsDedekindDomain NumberField MeasureTheory Measure Matrix Set Function
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil.GLn

open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.Weil.SLn
  QuadFormsKB.Tamagawa.Measure.Weil.NormalFib

noncomputable section

variable {F : Type} [Field F] [NumberField F] (k : ℕ)

local notation "ι" => Fin (k + 1)

/-! ### $\mathrm{GL}_n(\mathbb A)$ and $\mathrm{GL}_n(\mathbb A)^1$ -/

variable (F) in
/-- $\mathrm{GL}_n(\mathbb A_F)$, $n = k + 1$: the units of $M_n(\mathbb A_F)$ with the units topology. -/
abbrev GLA : Type := GL (Fin (k + 1)) (Adeles F)

instance : T2Space (GLA F k) := inferInstance

instance : SecondCountableTopology (Matrix ι ι (Adeles F))ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := Matrix ι ι (Adeles F))).symm.isEmbedding.secondCountableTopology

instance : LocallyCompactSpace (GLA F k) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

instance : SecondCountableTopology (GLA F k) :=
  Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology

theorem continuous_GLA_val : Continuous fun g : GLA F k => (g : Matrix ι ι (Adeles F)) := Units.continuous_val

variable (F) in
/-- The determinant $\mathrm{GL}_n(\mathbb A)\to\mathbb A^\times$. -/
def detA : GLA F k →* (Adeles F)ˣ := Matrix.GeneralLinearGroup.det

theorem coe_detA (g : GLA F k) : ((detA F k g : (Adeles F)ˣ) : Adeles F) = (g : Matrix ι ι (Adeles F)).det := rfl

theorem continuous_detA : Continuous (detA F k) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_id.matrix_det).comp (continuous_GLA_val k)
  · show Continuous fun g : GLA F k => ((g⁻¹ : GLA F k) : Matrix ι ι (Adeles F)).det
    exact (continuous_id.matrix_det).comp ((continuous_GLA_val k).comp continuous_inv)

variable (F) in
/-- $\mathrm{GL}_n(\mathbb A)^1 = \{g : \|\det g\|_{\mathbb A} = 1\}$. -/
def GLOneSub : Subgroup (GLA F k) := (ideleOne F).comap (detA F k)

variable (F) in
abbrev GLOne : Type := GLOneSub F k

theorem isClosed_GLOneSub : IsClosed (GLOneSub F k : Set (GLA F k)) :=
  isClosed_ideleOne.preimage (continuous_detA k)

instance : LocallyCompactSpace (GLOne F k) :=
  (isClosed_GLOneSub k).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (GLOne F k) := TopologicalSpace.Subtype.secondCountableTopology _

instance measurableSpace_GLOne : MeasurableSpace (GLOne F k) := borel _
instance : BorelSpace (GLOne F k) := ⟨rfl⟩

instance : StandardBorelSpace (GLOne F k) := by
  have := polishSpace_of_isTopologicalGroup (GLOne F k)
  infer_instance

instance : MeasurableMul₂ (GLOne F k) := ContinuousMul.measurableMul₂
instance : MeasurableInv (GLOne F k) := ContinuousInv.measurableInv
instance : MeasurableMul (GLOne F k) := inferInstance

variable (F) in
/-- The determinant $\mathrm{GL}_n(\mathbb A)^1\to\mathbb A^1$. -/
def detOne : GLOne F k →* ideleOne F :=
  ((detA F k).comp (GLOneSub F k).subtype).codRestrict (ideleOne F) fun g => g.2

@[simp] theorem coe_detOne (g : GLOne F k) : ((detOne F k g : ideleOne F) : (Adeles F)ˣ) = detA F k g := rfl

theorem continuous_detOne : Continuous (detOne F k) :=
  ((continuous_detA k).comp continuous_subtype_val).subtype_mk _

theorem measurable_detOne : Measurable (detOne F k) := (continuous_detOne k).measurable

/-! ### The section $t\mapsto\operatorname{diag}(t,1,\dots,1)$ -/

/-- $\operatorname{diag}(t, 1, \dots, 1)$ for a unit $t$ of a commutative ring. -/
def diagMat {R : Type*} [CommRing R] (t : Rˣ) : GL ι R where
  val := Matrix.diagonal (Function.update 1 0 (t : R))
  inv := Matrix.diagonal (Function.update 1 0 ((t⁻¹ : Rˣ) : R))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    by_cases h : i = 0
    · subst h; simp
    · simp [Function.update_of_ne h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    by_cases h : i = 0
    · subst h; simp
    · simp [Function.update_of_ne h]

theorem det_diagMat {R : Type*} [CommRing R] (t : Rˣ) :
    ((diagMat k t : GL ι R) : Matrix ι ι R).det = t := by
  show (Matrix.diagonal (Function.update 1 0 (t : R))).det = t
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

theorem diagMat_mul {R : Type*} [CommRing R] (s t : Rˣ) : diagMat k (s * t) = diagMat k s * diagMat k t := by
  apply Units.ext
  show (Matrix.diagonal (Function.update (1 : ι → R) 0 ((s * t : Rˣ) : R)) : Matrix ι ι R) =
    Matrix.diagonal (Function.update (1 : ι → R) 0 (s : R)) * Matrix.diagonal (Function.update (1 : ι → R) 0 (t : R))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i
  by_cases h : i = 0
  · subst h; simp
  · simp [Function.update_of_ne h]

variable (F) in
/-- The section $\mathbb A^1\to\mathrm{GL}_n(\mathbb A)^1$, $t\mapsto\operatorname{diag}(t,1,\dots,1)$ (a homomorphism). -/
def diagSec : ideleOne F →* GLOne F k where
  toFun t := ⟨diagMat k (t : (Adeles F)ˣ), by
    show detA F k _ ∈ ideleOne F
    have : detA F k (diagMat k (t : (Adeles F)ˣ)) = (t : (Adeles F)ˣ) := Units.ext (det_diagMat k _)
    rw [this]; exact t.2⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show (Matrix.diagonal (Function.update (1 : ι → Adeles F) 0 ((1 : (Adeles F)ˣ) : Adeles F)) :
      Matrix ι ι (Adeles F)) = 1
    rw [← Matrix.diagonal_one]
    congr 1; funext i; by_cases h : i = 0
    · subst h; simp
    · simp [Function.update_of_ne h]
  map_mul' s t := by
    apply Subtype.ext
    show diagMat k ((s * t : ideleOne F) : (Adeles F)ˣ) = diagMat k (s : (Adeles F)ˣ) * diagMat k (t : (Adeles F)ˣ)
    rw [Subgroup.coe_mul, diagMat_mul]

theorem detOne_diagSec (t : ideleOne F) : detOne F k (diagSec F k t) = t :=
  Subtype.ext (Units.ext (det_diagMat k _))

theorem detOne_surjective : Surjective (detOne F k) := fun t => ⟨diagSec F k t, detOne_diagSec k t⟩

theorem continuous_diagSec : Continuous (diagSec F k) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : ideleOne F => Matrix.diagonal (Function.update 1 0 (((t : (Adeles F)ˣ)) : Adeles F))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      by_cases h : i = 0
      · subst h; simp only [Function.update_self]
        exact Units.continuous_val.comp continuous_subtype_val
      · simp only [Function.update_of_ne h]; exact continuous_const
    · simp only [hij, ite_false]; exact continuous_const
  · show Continuous fun t : ideleOne F =>
      Matrix.diagonal (Function.update 1 0 ((((t : (Adeles F)ˣ))⁻¹ : (Adeles F)ˣ) : Adeles F))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      by_cases h : i = 0
      · subst h; simp only [Function.update_self]
        exact Units.continuous_coe_inv.comp continuous_subtype_val
      · simp only [Function.update_of_ne h]; exact continuous_const
    · simp only [hij, ite_false]; exact continuous_const

/-! ### The kernel is $\mathrm{SL}_n(\mathbb A)$ -/

theorem det_of_mem_ker {g : GLOne F k} (hg : g ∈ (detOne F k).ker) :
    ((g : GLA F k) : Matrix ι ι (Adeles F)).det = 1 := by
  have := congrArg (fun t : ideleOne F => ((t : (Adeles F)ˣ) : Adeles F)) (MonoidHom.mem_ker.mp hg)
  simpa [coe_detA] using this

variable (F) in
/-- $\ker(\det)\to\mathrm{SL}_n(\mathbb A)$. -/
def kerToSL : (detOne F k).ker →* SLnA F ι where
  toFun g := ⟨((g : GLOne F k) : GLA F k), det_of_mem_ker k g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (F) in
/-- $\mathrm{SL}_n(\mathbb A)\to\ker(\det)$. -/
def slToKer : SLnA F ι →* (detOne F k).ker where
  toFun h := ⟨⟨Matrix.SpecialLinearGroup.toGL h, by
      show detA F k _ ∈ ideleOne F
      have : detA F k (Matrix.SpecialLinearGroup.toGL h) = 1 := Units.ext (by
        rw [coe_detA]; exact h.2)
      rw [this]; exact one_mem _⟩, by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext; apply Units.ext
    show ((Matrix.SpecialLinearGroup.toGL h : GLA F k) : Matrix ι ι (Adeles F)).det = 1
    exact h.2⟩
  map_one' := Subtype.ext (Subtype.ext (Units.ext rfl))
  map_mul' _ _ := Subtype.ext (Subtype.ext (Units.ext rfl))

variable (F) in
/-- **$\ker(\det : \mathrm{GL}_n(\mathbb A)^1\to\mathbb A^1)\cong\mathrm{SL}_n(\mathbb A)$** as topological groups. -/
def kerEquivSL : (detOne F k).ker ≃ₜ* SLnA F ι where
  toFun := kerToSL F k
  invFun := slToKer F k
  left_inv g := Subtype.ext (Subtype.ext (Units.ext rfl))
  right_inv h := Subtype.ext rfl
  map_mul' := (kerToSL F k).map_mul
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_GLA_val k).comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    show Continuous fun h : SLnA F ι => ((h⁻¹ : SLnA F ι) : Matrix ι ι (Adeles F))
    exact continuous_subtype_val.comp continuous_inv

theorem isClosed_ker : IsClosed ((detOne F k).ker : Set (GLOne F k)) :=
  isClosed_eq (continuous_detOne k) continuous_const

instance : LocallyCompactSpace (detOne F k).ker :=
  (isClosed_ker k).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : SecondCountableTopology (detOne F k).ker := TopologicalSpace.Subtype.secondCountableTopology _

/-! ### The Tamagawa measure -/

variable (F) in
/-- **The Tamagawa measure of $\mathrm{SL}_n(\mathbb A)$ on the kernel of $\det$**: `SLn.muSL` transported along
`kerEquivSL`. -/
def muSLK : Measure (detOne F k).ker := (muSL F k).map (kerEquivSL F k).symm

theorem map_muSLK : (muSLK F k).map (kerEquivSL F k) = muSL F k := by
  have h1 : Measurable (kerEquivSL F k) := (kerEquivSL F k).continuous.measurable
  have h2 : Measurable (kerEquivSL F k).symm := (kerEquivSL F k).symm.continuous.measurable
  rw [muSLK, Measure.map_map h1 h2]
  convert Measure.map_id
  funext g
  exact (kerEquivSL F k).apply_symm_apply g

instance : (muSLK F k).IsHaarMeasure := by
  have := isHaarMeasure_muSL (F := F) k
  exact ContinuousMulEquiv.isHaarMeasure_map _ _

instance : SFinite (muSLK F k) := inferInstance

variable (F) in
/-- **The Tamagawa measure of $\mathrm{GL}_n(\mathbb A)^1$** (convergence factors $\lambda_v = 1-q_v^{-1}$, global factor
$\rho_F^{-1}$): $\rho_F^{-1}$ times Weil's fibred measure of $\mu^1$ (`muIdeleOne`) and $\mu_{\mathrm{SL}_n}$ along
$\det$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.1 (convergence factors λ_v, global factor ρ_k^{-1}) [unverified locators]"]
def muGL : Measure (GLOne F k) :=
  (ENNReal.ofReal (dedekindZeta_residue F))⁻¹ •
    fibMeas (detOne F k) (detOne_surjective k) (muIdeleOne F) (muSLK F k)

/-! ### $\mathrm{GL}_n(F)$ -/

variable (F) in
/-- $\mathrm{GL}_n(F)\to\mathrm{GL}_n(\mathbb A)$, entrywise diagonal embedding. -/
def glEmbA : GL ι F →* GLA F k := Units.map (diagRing F).mapMatrix.toMonoidHom

theorem detA_glEmbA (γ : GL ι F) : detA F k (glEmbA F k γ) = diagUnits F (Matrix.GeneralLinearGroup.det γ) := by
  apply Units.ext
  show ((γ : Matrix ι ι F).map (diagRing F)).det = diagRing F (γ : Matrix ι ι F).det
  rw [← RingHom.mapMatrix_apply, RingHom.map_det]

variable (F) in
/-- $\mathrm{GL}_n(F)\to\mathrm{GL}_n(\mathbb A)^1$ (product formula: $\|\det\gamma\|_{\mathbb A} = 1$). -/
def glEmb : GL ι F →* GLOne F k :=
  (glEmbA F k).codRestrict (GLOneSub F k) fun γ => by
    show detA F k _ ∈ ideleOne F
    rw [detA_glEmbA]; exact diagUnitsSub_le_ideleOne ⟨_, rfl⟩

variable (F) in
/-- **$\mathrm{GL}_n(F)$, diagonally in $\mathrm{GL}_n(\mathbb A)^1$.** -/
def GammaGL : Subgroup (GLOne F k) := (glEmb F k).range

instance : Countable (Matrix ι ι F) := inferInstanceAs (Countable (ι → ι → F))

instance : Countable (GL ι F) :=
  Function.Injective.countable (f := fun g : GL ι F => (g : Matrix ι ι F)) Units.val_injective

instance : Countable (GammaGL F k) := by
  have h : ((GammaGL F k : Subgroup _) : Set (GLOne F k)) = Set.range (glEmb F k) := MonoidHom.coe_range _
  exact (h ▸ Set.countable_range (glEmb F k)).to_subtype

theorem glEmb_coe_apply (γ : GL ι F) (i j : ι) :
    (((glEmb F k γ : GLOne F k) : GLA F k) : Matrix ι ι (Adeles F)) i j = diag F ((γ : Matrix ι ι F) i j) := rfl

/-- **$\mathrm{GL}_n(F)$ is discrete in $\mathrm{GL}_n(\mathbb A)^1$.** -/
theorem discreteTopology_GammaGL : DiscreteTopology (GammaGL F k) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  set V : Set (GLOne F k) := {g | ∀ i j, ((g : GLA F k) : Matrix ι ι (Adeles F)) i j -
    (1 : Matrix ι ι (Adeles F)) i j ∈ U}
  have hV : IsOpen V := by
    simp only [V, Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_
    have hc : Continuous fun g : GLOne F k => ((g : GLA F k) : Matrix ι ι (Adeles F)) :=
      (continuous_GLA_val k).comp continuous_subtype_val
    exact ((continuous_apply j).comp ((continuous_apply i).comp hc)).sub continuous_const
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr ⟨V, hV, ?_⟩)
  ext ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := hg
  simp only [Set.mem_preimage, Set.mem_singleton_iff, V]
  constructor
  · intro h
    have hγ : γ = 1 := by
      ext i j
      have h' := h i j
      rw [glEmb_coe_apply] at h'
      have : diag F ((γ : Matrix ι ι F) i j - (1 : Matrix ι ι F) i j) ∈ U := by
        rw [← diagRing_apply, map_sub, diagRing_apply]
        convert h' using 2
        rcases eq_or_ne i j with rfl | hij
        · simp [Matrix.one_apply_eq, map_one]
        · simp [Matrix.one_apply_ne hij]
      exact sub_eq_zero.mp (hUdiag _ this)
    subst hγ
    exact Subtype.ext (map_one _)
  · intro h i j
    have h1 : glEmb F k γ = 1 := congrArg Subtype.val h
    rw [h1]
    simp [h0U]

instance : DiscreteTopology (GammaGL F k) := discreteTopology_GammaGL k

/-- $\det(\mathrm{GL}_n(F)) = F^\times$, inside $\mathbb A^1$. -/
theorem gammaQ_eq : gammaQ (detOne F k) (GammaGL F k) = diagUnitsOne F := by
  ext t
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ⟨Matrix.GeneralLinearGroup.det γ, ?_⟩
    show diagUnits F _ = detA F k (glEmbA F k γ)
    rw [detA_glEmbA]
  · intro ht
    obtain ⟨ξ, hξ⟩ := Subgroup.mem_subgroupOf.mp ht
    refine ⟨glEmb F k (diagMat k ξ), ⟨_, rfl⟩, ?_⟩
    apply Subtype.ext
    show detA F k (glEmbA F k (diagMat k ξ)) = (t : (Adeles F)ˣ)
    rw [detA_glEmbA, ← hξ]
    congr 1
    exact Units.ext (det_diagMat k ξ)

/-! ### $\mathrm{SL}_n(\mathbb A)$ is unimodular, and $\operatorname{covol}(\mathrm{SL}_n(F)) = 1$ for left translation -/

/-- Scalars in front of a Haar measure are unique. -/
theorem nnreal_smul_inj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {a b : ℝ≥0}
    (h : a • μ = b • μ) : a = b := by
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts G))
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  exact_mod_cast (ENNReal.mul_left_inj h0 ht).1 this

/-- A Haar measure invariant under right translation by `g` has `Δ(g) = 1`. -/
theorem modularCharacter_eq_one_of_map {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.InnerRegular]
    (g : G) (h : μ.map (· * g) = μ) : Measure.modularCharacter g = 1 := by
  have h' := Measure.map_right_mul_eq_modularCharacterFun_smul μ g
  rw [h] at h'
  have : (1 : ℝ≥0) • μ = Measure.modularCharacterFun g • μ := by rw [one_smul]; exact h'
  exact (nnreal_smul_inj μ this).symm

/-- **$\mathrm{SL}_n(\mathbb A)$ is unimodular**: `muSL` is right invariant (lattice $\mathrm{SL}_n(F)$ of covolume $1$,
on which the modular character is trivial). -/
theorem isMulRightInvariant_muSL : (muSL F k).IsMulRightInvariant := by
  have := isHaarMeasure_muSL (F := F) k
  obtain ⟨D, hDm, hD⟩ : ∃ D : Set (SLnA F ι), MeasurableSet D ∧
      ∀ g : SLnA F ι, ∃! γ : SpecialLinearGroup ι F, γ • g ∈ D :=
    exists_measurableSet_forall_existsUnique_right'
  have hFD : IsFundamentalDomain (SpecialLinearGroup ι F) D (muSL F k) :=
    IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hD1 : muSL F k D = 1 := by rw [← hFD.covolume_eq_volume]; exact tamagawa_SLn (F := F) k
  have hΔγ : ∀ γ : SpecialLinearGroup ι F, Measure.modularCharacter (slnEmb F ι γ)⁻¹ = 1 := by
    intro γ
    refine modularCharacter_eq_one_of_map (muSL F k) _ ?_
    ext s hs
    rw [Measure.map_apply (measurable_mul_const _) hs]
    exact measure_preimage_smul (μ := muSL F k) γ s
  refine isMulRightInvariant_of_rightFD (muSL F k) (Γ := SpecialLinearGroup ι F) (fun γ g x => ?_)
    (fun γ x => ?_) hFD (by rw [hD1]; exact one_ne_zero) (by rw [hD1]; exact ENNReal.one_ne_top)
  · simp only [slnRight_smul_def, mul_assoc]
  · rw [slnRight_smul_def, map_mul, hΔγ, mul_one]

/-- $\operatorname{covol}(\mathrm{SL}_n(F)\backslash\mathrm{SL}_n(\mathbb A), \mu_{\mathrm{SL}_n}) = 1$ for the left
translation action of the subgroup $\mathrm{SL}_n(F)$ (from `tamagawa_SLn`, right translation, by inversion). -/
theorem covolume_slnSub : covolume (slnSub F ι) (SLnA F ι) (muSL F k) = 1 := by
  have := isHaarMeasure_muSL (F := F) k
  have := isMulRightInvariant_muSL (F := F) k
  have hinv : (muSL F k).map (fun x => x⁻¹) = muSL F k := map_inv_eq_self_of_isMulRightInvariant _
  have : Countable (slnSub F ι) := by
    have h : ((slnSub F ι : Subgroup _) : Set (SLnA F ι)) = Set.range (slnEmb F ι) := MonoidHom.coe_range _
    exact (h ▸ Set.countable_range (slnEmb F ι)).to_subtype
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (slnSub F ι)
  have hFD : IsFundamentalDomain (slnSub F ι) D (muSL F k) := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  -- the inverted set is a fundamental domain for the right action
  have hD' : ∀ g : SLnA F ι, ∃! γ : SpecialLinearGroup ι F, γ • g ∈ (fun x => x⁻¹) ⁻¹' D := by
    intro g
    obtain ⟨⟨_, γ, rfl⟩, hγ, huniq⟩ := hD g⁻¹
    refine ⟨γ, ?_, fun δ hδ => ?_⟩
    · show (g * (slnEmb F ι γ)⁻¹)⁻¹ ∈ D
      rw [_root_.mul_inv_rev, inv_inv]; exact hγ
    · have hδ' : (⟨slnEmb F ι δ, δ, rfl⟩ : slnSub F ι) • g⁻¹ ∈ D := by
        show slnEmb F ι δ * g⁻¹ ∈ D
        have : (g * (slnEmb F ι δ)⁻¹)⁻¹ ∈ D := hδ
        rwa [_root_.mul_inv_rev, inv_inv] at this
      exact slnEmb_injective (congrArg Subtype.val (huniq _ hδ'))
  have hFD' : IsFundamentalDomain (SpecialLinearGroup ι F) ((fun x => x⁻¹) ⁻¹' D) (muSL F k) :=
    IsFundamentalDomain.mk' (measurable_inv hDm).nullMeasurableSet hD'
  have hsmul : SMulInvariantMeasure (slnSub F ι) (SLnA F ι) (muSL F k) :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  rw [hFD.covolume_eq_volume, ← tamagawa_SLn (F := F) k, hFD'.covolume_eq_volume,
    ← Measure.map_apply measurable_inv hDm, hinv]

/-! ### Conjugation by $\mathrm{GL}_n(\mathbb A)^1$ preserves $\mu_{\mathrm{SL}_n}$ -/

local notation "N" => detOne F k

instance : (muSLK F k).IsMulRightInvariant := by
  have := isMulRightInvariant_muSL (F := F) k
  rw [muSLK]
  refine ⟨fun g => ?_⟩
  set e := (kerEquivSL F k).symm
  have he : Measurable e := e.continuous.measurable
  rw [Measure.map_map (measurable_mul_const g) he]
  have : (fun x => x * g) ∘ e = e ∘ (fun y => y * e.symm g) := by
    funext y; simp [e]
  rw [this, ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

/-- $\Gamma\cap\ker\det$ corresponds to $\mathrm{SL}_n(F)$ under `kerEquivSL`. -/
theorem gammaK_map : (gammaK N (GammaGL F k)).map (kerEquivSL F k).toMulEquiv.toMonoidHom = slnSub F ι := by
  ext h
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := (hx : ((x : (detOne F k).ker) : GLOne F k) ∈ GammaGL F k)
    have h1 : (((glEmb F k γ : GLOne F k) : GLA F k) : Matrix ι ι (Adeles F)).det = 1 := by
      rw [hγ]; exact det_of_mem_ker k x.2
    have hdet : (γ : Matrix ι ι F).det = 1 := by
      have h2 : diagRing F ((γ : Matrix ι ι F).det) = diagRing F 1 := by
        rw [map_one, RingHom.map_det]
        exact h1
      exact diag_injective h2
    refine ⟨⟨γ, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_⟩
    show diag F ((γ : Matrix ι ι F) i j) = (((x : (detOne F k).ker) : GLOne F k) : GLA F k) i j
    rw [show ((x : (detOne F k).ker) : GLOne F k) = glEmb F k γ from hγ.symm]; rfl
  · rintro ⟨γ, rfl⟩
    refine ⟨slToKer F k (slnEmb F ι γ), ?_, Matrix.SpecialLinearGroup.ext _ _ fun _ _ => rfl⟩
    show ((slToKer F k (slnEmb F ι γ) : (detOne F k).ker) : GLOne F k) ∈ GammaGL F k
    exact ⟨Matrix.SpecialLinearGroup.toGL γ, Subtype.ext (Units.ext rfl)⟩

theorem covolume_gammaK : covolume (gammaK N (GammaGL F k)) (detOne F k).ker (muSLK F k) = 1 := by
  have := isHaarMeasure_muSL (F := F) k
  rw [covolume_eq_of_map (gammaK N (GammaGL F k)) (slnSub F ι) (kerEquivSL F k).toMulEquiv
    (kerEquivSL F k).continuous.measurable (kerEquivSL F k).symm.continuous.measurable (gammaK_map k)
    (muSLK F k) (muSL F k) (map_muSLK k)]
  exact covolume_slnSub k

instance (g : GLOne F k) : ((muSLK F k).map (adK N g)).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map (muSLK F k) (adKEquiv N g)

variable (F) in
/-- The modulus of conjugation by `g` on $\mu_{\mathrm{SL}_n}$: $\operatorname{Ad}(g)_*\mu = c(g)\,\mu$. -/
def cAd (g : GLOne F k) : ℝ≥0 := haarScalarFactor ((muSLK F k).map (adK N g)) (muSLK F k)

theorem map_adK_eq (g : GLOne F k) : (muSLK F k).map (adK N g) = cAd F k g • muSLK F k :=
  isMulLeftInvariant_eq_smul _ _

theorem measurable_adK' (g : GLOne F k) : Measurable (adK N g) := (adKEquiv N g).continuous.measurable

theorem cAd_mul (g h : GLOne F k) : cAd F k (g * h) = cAd F k g * cAd F k h := by
  have hcomp : adK N (g * h) = adK N g ∘ adK N h := by
    funext x; apply Subtype.ext; simp [mul_assoc]
  have : (cAd F k (g * h)) • muSLK F k = (cAd F k g * cAd F k h) • muSLK F k := by
    rw [← map_adK_eq, hcomp, ← Measure.map_map (measurable_adK' k g) (measurable_adK' k h), map_adK_eq,
      Measure.map_smul, map_adK_eq, smul_smul, mul_comm]
    all_goals exact (measurable_adK' k _).aemeasurable
  exact nnreal_smul_inj _ this

theorem cAd_ker (x : (detOne F k).ker) : cAd F k x = 1 := by
  have : (cAd F k x) • muSLK F k = (1 : ℝ≥0) • muSLK F k := by
    rw [← map_adK_eq, one_smul]
    have h : adK N (x : GLOne F k) = (fun y => y * x⁻¹) ∘ (fun y => x * y) := by
      funext y; apply Subtype.ext; simp
    rw [h, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]
  exact nnreal_smul_inj _ this

theorem cAd_gamma {γ : GLOne F k} (hγ : γ ∈ GammaGL F k) : cAd F k γ = 1 := by
  have hmap : (gammaK N (GammaGL F k)).map (adKEquiv N γ).toMulEquiv.toMonoidHom = gammaK N (GammaGL F k) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show γ * ((y : (detOne F k).ker) : GLOne F k) * γ⁻¹ ∈ GammaGL F k
      exact mul_mem (mul_mem hγ hy) (inv_mem hγ)
    · intro hx
      refine ⟨adK N γ⁻¹ x, ?_, ?_⟩
      · show γ⁻¹ * ((x : (detOne F k).ker) : GLOne F k) * γ⁻¹⁻¹ ∈ GammaGL F k
        exact mul_mem (mul_mem (inv_mem hγ) hx) (inv_mem (inv_mem hγ))
      · exact (adKEquiv N γ).right_inv x
  have h := covolume_eq_of_map (gammaK N (GammaGL F k)) (gammaK N (GammaGL F k)) (adKEquiv N γ).toMulEquiv
    (measurable_adK' k γ) (adKEquiv N γ).symm.continuous.measurable hmap (muSLK F k)
    ((muSLK F k).map (adK N γ)) rfl
  rw [map_adK_eq, ENNReal.smul_def, covolume_smul _ _ (by
      intro h0
      have := haarScalarFactor_pos_of_isHaarMeasure ((muSLK F k).map (adK N γ)) (muSLK F k)
      exact this.ne' (by exact_mod_cast h0)),
    covolume_gammaK, mul_one] at h
  exact_mod_cast h.symm

/-- $c$ is bounded on compact sets. -/
theorem exists_bound_cAd {S : Set (GLOne F k)} (hS : IsCompact S) : ∃ B : ℝ≥0, ∀ g ∈ S, cAd F k g ≤ B := by
  obtain ⟨U⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (detOne F k).ker))
  have hU0 : muSLK F k U ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ U.interior_nonempty).ne'
  -- the compact set `S⁻¹ U S` in the kernel
  set W : Set (GLOne F k) := (fun p : GLOne F k × (GLOne F k × GLOne F k) => p.1⁻¹ * p.2.1 * p.2.2) ''
    (S ×ˢ ((Subtype.val '' (U : Set (detOne F k).ker)) ×ˢ S))
  have hWc : IsCompact W := by
    refine (hS.prod ((U.isCompact.image continuous_subtype_val).prod hS)).image ?_
    fun_prop
  have hker : IsClosed ((detOne F k).ker : Set (GLOne F k)) :=
    isClosed_eq (continuous_detOne k) continuous_const
  have hWK : IsCompact ((Subtype.val : (detOne F k).ker → GLOne F k) ⁻¹' W) :=
    hker.isClosedEmbedding_subtypeVal.isCompact_preimage hWc
  have hWt : muSLK F k (Subtype.val ⁻¹' W) ≠ ⊤ := hWK.measure_lt_top.ne
  refine ⟨(muSLK F k (Subtype.val ⁻¹' W) / muSLK F k U).toNNReal, fun g hg => ?_⟩
  have hsub : adK N g ⁻¹' (U : Set (detOne F k).ker) ⊆ Subtype.val ⁻¹' W := by
    intro x hx
    refine ⟨(g, ((adK N g x : (detOne F k).ker) : GLOne F k), g), ⟨hg, ⟨_, hx, rfl⟩, hg⟩, ?_⟩
    simp [mul_assoc]
  have hle : (cAd F k g : ℝ≥0∞) * muSLK F k U ≤ muSLK F k (Subtype.val ⁻¹' W) := by
    calc (cAd F k g : ℝ≥0∞) * muSLK F k U = ((muSLK F k).map (adK N g)) U := by
          rw [map_adK_eq]; rfl
      _ = muSLK F k (adK N g ⁻¹' U) := Measure.map_apply (measurable_adK' k g) U.isCompact.measurableSet
      _ ≤ _ := measure_mono hsub
  have hUt : muSLK F k U ≠ ⊤ := U.isCompact.measure_lt_top.ne
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.div_ne_top hWt hU0)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hU0) (Or.inl hUt)).2 hle

/-- **Conjugation by $\mathrm{GL}_n(\mathbb A)^1$ preserves the Tamagawa measure of $\mathrm{SL}_n(\mathbb A)$.** -/
theorem cAd_eq_one (g : GLOne F k) : cAd F k g = 1 := by
  -- the homomorphism `t ↦ c(diag(t,1,…,1))`
  set χ : ideleOne F → ℝ≥0 := fun t => cAd F k (diagSec F k t)
  have hχmul : ∀ s t, χ (s * t) = χ s * χ t := fun s t => by simp only [χ, map_mul, cAd_mul]
  have hχγ : ∀ t ∈ diagUnitsOne F, χ t = 1 := by
    intro t ht
    obtain ⟨ξ, hξ⟩ := Subgroup.mem_subgroupOf.mp ht
    refine cAd_gamma k ⟨diagMat k ξ, ?_⟩
    apply Subtype.ext; apply Units.ext
    show (diagMat k ξ : Matrix ι ι F).map (diagRing F) = diagMat k ((t : ideleOne F) : (Adeles F)ˣ)
    rw [← hξ]
    refine Matrix.ext fun i j => ?_
    show (Matrix.diagonal (Function.update 1 0 (ξ : F))).map (diagRing F) i j =
      Matrix.diagonal (Function.update 1 0 ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F)) i j
    rw [Matrix.diagonal_map (map_zero _)]
    congr 2; funext i
    by_cases h : i = 0
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem F
  obtain ⟨B, hB⟩ := exists_bound_cAd k (hC.image (continuous_diagSec k))
  have hbound : ∀ t, χ t ≤ B := by
    intro t
    obtain ⟨γ, hγ, hmem⟩ := hCx t
    have : t = γ * (γ⁻¹ * t) := by group
    rw [this, hχmul, hχγ γ hγ, one_mul]
    exact hB _ ⟨_, hmem, rfl⟩
  have hχpos : ∀ t, 0 < χ t := fun t => by
    show 0 < cAd F k _
    exact haarScalarFactor_pos_of_isHaarMeasure _ _
  have hχone : χ 1 = 1 := by show cAd F k (diagSec F k 1) = 1; rw [map_one]; exact cAd_ker k 1
  have hχ1 : ∀ t, χ t = 1 := by
    intro t
    have hm : ∀ (m : ℕ) (s : ideleOne F), χ (s ^ m) = χ s ^ m := by
      intro m s; induction m with
      | zero => simp only [pow_zero]; exact hχone
      | succ m ih => rw [pow_succ, hχmul, ih, pow_succ]
    have hinv : χ t⁻¹ = (χ t)⁻¹ := by
      have h1 : χ t * χ t⁻¹ = 1 := by rw [← hχmul, mul_inv_cancel]; exact hχone
      exact eq_inv_of_mul_eq_one_right h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgt' : 1 < (χ t)⁻¹ := one_lt_inv_iff₀.mpr ⟨hχpos t, hlt⟩
      obtain ⟨m, hmB⟩ := pow_unbounded_of_one_lt (B : ℝ≥0) hgt'
      have := hbound (t⁻¹ ^ m)
      rw [hm, hinv] at this
      exact absurd this (not_le.mpr hmB)
    · obtain ⟨m, hmB⟩ := pow_unbounded_of_one_lt (B : ℝ≥0) hgt
      have := hbound (t ^ m)
      rw [hm] at this
      exact absurd this (not_le.mpr hmB)
  -- general `g`: `g = diag(det g) · k` with `k` in the kernel
  set s := diagSec F k (detOne F k g)
  have hk : s⁻¹ * g ∈ (detOne F k).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, detOne_diagSec, inv_mul_cancel]
  have : g = s * (s⁻¹ * g) := by group
  rw [this, cAd_mul, cAd_ker k ⟨_, hk⟩, mul_one]
  exact hχ1 _

theorem map_adK_muSLK (g : GLOne F k) : (muSLK F k).map (adK N g) = muSLK F k := by
  rw [map_adK_eq, cAd_eq_one, one_smul]

/-! ### $\tau(\mathrm{GL}_n) = 1$ -/

theorem covolume_gammaQ : covolume (gammaQ N (GammaGL F k)) (ideleOne F) (muIdeleOne F) =
    ENNReal.ofReal (dedekindZeta_residue F) := by
  rw [gammaQ_eq, ← muIdeleClass_univ_eq_residue, muIdeleClass_univ isFundamentalDomain_ideleClassFD]
  have : SMulInvariantMeasure (diagUnitsOne F) (ideleOne F) (muIdeleOne F) :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  exact isFundamentalDomain_ideleClassFD.covolume_eq_volume

/-- **The Tamagawa number of $\mathrm{GL}_n$ over every number field is $1$** (with Weil's convergence factors
$\lambda_v = 1 - q_v^{-1}$ and global factor $\rho_F^{-1}$): for every $n = k + 1\ge1$,
$\operatorname{vol}(\mathrm{GL}_n(F)\backslash\mathrm{GL}_n(\mathbb A)^1, \mu^1_{\mathrm{GL}_n}) = 1$.
Unconditional. -/
@[kb "weil1982" "Ch. III and §2.4 Thm 2.4.4 (τ(GL_n) = τ(SL_n) τ(G_m) = 1, convergence factors 1 - q_v^{-1}, global factor ρ_k^{-1}) [unverified locators]"]
theorem tamagawa_GLn : covolume (GammaGL F k) (GLOne F k) (muGL F k) = 1 := by
  have := isHaarMeasure_muSL (F := F) k
  have hρ : 0 < dedekindZeta_residue F := dedekindZeta_residue_pos F
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
  have hρt : ENNReal.ofReal (dedekindZeta_residue F) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinvL := isMulLeftInvariant_fibMeas N (detOne_surjective k) (measurable_detOne k) (muIdeleOne F)
    (muSLK F k)
  -- exact fundamental domains
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaGL F k)
  have hdK : DiscreteTopology (gammaK N (GammaGL F k)) :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : gammaK N (GammaGL F k) => (⟨((x : (detOne F k).ker) : GLOne F k), x.2⟩ : GammaGL F k))
      (by fun_prop) (fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h)))
  obtain ⟨DK, hDKm, hDK⟩ := exists_measurableSet_forall_existsUnique_smul_mem (gammaK N (GammaGL F k))
  have hdQ : DiscreteTopology (gammaQ N (GammaGL F k)) := by rw [gammaQ_eq]; infer_instance
  obtain ⟨DQ, hDQm, hDQ⟩ := exists_measurableSet_forall_existsUnique_smul_mem (gammaQ N (GammaGL F k))
  rw [muGL, covolume_smul _ _ (ENNReal.inv_ne_zero.mpr hρt),
    QuadFormsKB.Tamagawa.Unitary.covolume_fibMeas N (detOne_surjective k) (GammaGL F k) (measurable_detOne k)
      (muIdeleOne F) (muSLK F k) (map_adK_muSLK k) ⟨hDm, hD⟩ ⟨hDKm, hDK⟩ ⟨hDQm, hDQ⟩,
    covolume_gammaK, covolume_gammaQ, one_mul]
  exact ENNReal.inv_mul_cancel hρ0 hρt

end

end QuadFormsKB.Tamagawa.Measure.Weil.GLn
