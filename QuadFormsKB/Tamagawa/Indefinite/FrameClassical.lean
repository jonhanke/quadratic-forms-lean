/-
# Frames at infinity, representations of a form, and the classical theta integral

**Layer:** number fields; the library's adelic groups. The frame version of the `ClassicalSetup`/`ClassicalMeasures`.
$F$ a number field, $Q_0$ over $\mathcal O_F$ in $N$ variables (any signature), $T_0$ over $\mathcal O_F$ of rank $r$,
$L = \mathcal O_F^N$, classes $M_i$ (`DC Q₀`) with unit groups $\Gamma_i$ (`unitGroup`).

**Defines**
* `RatFrame Q₀ T₀`: the rational frames $X\in F^{N\times r}$ with $Q_0\circ X = T_0$ (columns $x_0,\dots,x_{r-1}$), with the
  action of $\Gamma = SO(V)(F)$;
* `ratAT`, `ratFT`: their archimedean ($V_\infty^r$) and finite ($\mathbb A_f^{N\times r}$) embeddings, column by column;
  `latHatT` $=\hat L^r$;
* `repsT Q₀ T₀ i` $= R(M_i, T_0) = \{X\in M_i^r : Q\circ X = T_0\}\subseteq V_\infty^r$ (a $\Gamma_i$-set);
* **`repMeasureT`** $\rho(M_i, T_0) = \sum_{X\in\Gamma_i\backslash R(M_i,T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H_X, \mu_{H_X})$
  (Siegel's *Darstellungsmaß* for forms), $H_X$ the stabilizer of $X$ in $G_\infty$, $\mu_{H_X}$ from an archimedean
  fibration `𝔉` over a set of frames containing the $X$.

**Proves** `lintegral_theta_classicalT`, `lintegral_theta_mul_tsum_unitVolumeT`: the classical theta integral of frames,
$\int_E\theta = \mu_f(SO(\hat L))\cdot c\cdot\sum_i\rho(M_i,T_0)\cdot\int\Phi\circ\tau\,d\sigma$ (generic
`lintegral_theta_eq`). Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.Indefinite.ClassicalMeasures
import QuadFormsKB.Tamagawa.FrameRepMass

open MeasureTheory MulAction Set NumberField IsDedekindDomain Matrix
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
open NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F] {N r : ℕ} (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Rational frames -/

/-- **The rational frames of $T_0$**: $X\in F^{N\times r}$ with $Q_0\circ X = T_0$. -/
def RatFrame : Type := {X : Matrix (Fin N) (Fin r) F // (QF).compMat X = T₀.map (algebraMap (𝓞 F) F)}

instance : Countable (RatFrame Q₀ T₀) := by
  haveI : Countable (Matrix (Fin N) (Fin r) F) := inferInstanceAs (Countable (Fin N → Fin r → F))
  exact inferInstanceAs (Countable {X : Matrix (Fin N) (Fin r) F // (QF).compMat X = T₀.map (algebraMap (𝓞 F) F)})

/-- The columns of a matrix. -/
abbrev cols (X : Matrix (Fin N) (Fin r) F) : Fin r → Fin N → F := fun j i => X i j

/-- **$\Gamma = SO(V)(F)$ acts on the rational frames** by matrices. -/
instance instMulActionRatFrame : MulAction (GammaSOAdele Q₀) (RatFrame Q₀ T₀) where
  smul γ X := ⟨ratMat Q₀ ((gammaEquiv Q₀).symm γ) * X.1, by
    rw [Frames.compMat_orth (QF) ((gammaEquiv Q₀).symm γ : orthGroup QF F).2]; exact X.2⟩
  one_smul X := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm 1) * X.1 = X.1
    rw [map_one]
    show ((1 : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * X.1 = X.1
    rw [Units.val_one, Matrix.one_mul])
  mul_smul γ δ X := Subtype.ext (by
    show ratMat Q₀ ((gammaEquiv Q₀).symm (γ * δ)) * X.1 =
      ratMat Q₀ ((gammaEquiv Q₀).symm γ) * (ratMat Q₀ ((gammaEquiv Q₀).symm δ) * X.1)
    rw [map_mul, ← Matrix.mul_assoc]; rfl)

theorem ratFrame_smul_val (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) :
    (γ • X).1 = ratMat Q₀ ((gammaEquiv Q₀).symm γ) * X.1 := rfl

theorem cols_smul (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) (j : Fin r) :
    cols (γ • X).1 j = ratMat Q₀ ((gammaEquiv Q₀).symm γ) *ᵥ cols X.1 j := by
  funext i
  simp [ratFrame_smul_val, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The adelic frame of a rational frame, column by column. -/
def ratFrameA (X : RatFrame Q₀ T₀) : Fin r → AdeleSpace F (Fin N) := fun j => diagVec F (Fin N) (cols X.1 j)

theorem ratFrameA_smul (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) :
    ratFrameA Q₀ T₀ (γ • X) = (γ : SOAdele Q₀) • ratFrameA Q₀ T₀ X := by
  funext j
  show diagVec F (Fin N) (cols (γ • X).1 j) = (γ : SOAdele Q₀) • diagVec F (Fin N) (cols X.1 j)
  rw [cols_smul, coe_eq_diagSOAdele_symm, diagSOAdele_smul_diagVec]

/-! ### The archimedean and finite embeddings -/

/-- **The archimedean embedding** $X\mapsto(\sigma_w(x_j))_{w, j}\in V_\infty^r$. -/
def ratAT (X : RatFrame Q₀ T₀) : Fin r → VInf F N := fun j => archVec (ratFrameA Q₀ T₀ X j)

/-- **The finite embedding** $X\mapsto(x_j)_j\in(\mathbb A_f^N)^r$ (diagonal). -/
def ratFT (X : RatFrame Q₀ T₀) : Fin r → Fin N → AF := fun j => finVec (ratFrameA Q₀ T₀ X j)

theorem ratAT_smul (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) :
    ratAT Q₀ T₀ (γ • X) = (γ : SOAdele Q₀).1 • ratAT Q₀ T₀ X := by
  funext j
  simp only [ratAT, ratFrameA_smul, Pi.smul_apply, archVec_smul]

theorem ratFT_smul (γ : GammaSOAdele Q₀) (X : RatFrame Q₀ T₀) :
    ratFT Q₀ T₀ (γ • X) = (γ : SOAdele Q₀).2 • ratFT Q₀ T₀ X := by
  funext j
  simp only [ratFT, ratFrameA_smul, Pi.smul_apply, finVec_smul]

/-- **The archimedean embedding of the rational frames is injective.** -/
theorem ratAT_injective : Function.Injective (ratAT Q₀ T₀) := by
  intro X X' h
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases w.isReal_or_isComplex with hw | hw
  · have := congrArg (fun x : Fin r → VInf F N => (x j).1 ⟨w, hw⟩ i) h
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding_apply_isReal] at this
    exact (embedding_of_isReal hw).injective this
  · have := congrArg (fun x : Fin r → VInf F N => (x j).2 ⟨w, hw⟩ i) h
    simp only [ratAT, ratFrameA, archVec, diagVec_apply, diag_fst, mixedEmbedding_apply_isComplex] at this
    exact w.embedding.injective this

variable (F N r) in
/-- $\hat L^r$: frames with every column in $\hat L$. -/
def latHatT : Set (Fin r → Fin N → AF) := {Z | ∀ j, Z j ∈ latHat F N}

/-- **$SO(\hat L)$ preserves $\hat L^r$.** -/
theorem latHatT_stable (k : SOAf Q₀) (hk : k ∈ KSO Q₀) (Z : Fin r → Fin N → AF) :
    k • Z ∈ latHatT F N r ↔ Z ∈ latHatT F N r :=
  ⟨fun h j => (latHat_stable Q₀ k hk (Z j)).mp (h j), fun h j => (latHat_stable Q₀ k hk (Z j)).mpr (h j)⟩

/-! ### Representations and their measure -/

/-- **The representations of $T_0$ by the class $i$**: $R(M_i, T_0) = \{X\in M_i^r : Q\circ X = T_0\}$, embedded in
$V_\infty^r$; a $\Gamma_i$-set. -/
def repsT (i : DC Q₀) : SubMulAction (unitGroup Q₀ i) (Fin r → VInf F N) :=
  repSet (ratAT_smul Q₀ T₀) (ratFT_smul Q₀ T₀) (latHatT_stable Q₀) (dcRep Q₀ i)

variable (hQ : Q₀.Nondegenerate)
variable {T : Type*} [MeasurableSpace T] {P : Set (Fin r → VInf F N)} {σ : Measure T} {τ : T → Fin r → VInf F N}
  {c : ℝ≥0∞}

/-- **Siegel's measure of the representations of $T_0$ by the class $i$** (*Darstellungsmaß*):
$$\rho(M_i, T_0) = \sum_{X\in\Gamma_i\backslash R(M_i, T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H_X, \mu_{H_X}),$$
$H_X$ the stabilizer of the frame $X$ in $G_\infty$, $\mu_{H_X}$ the stabilizer measures of the archimedean fibration `𝔉`.
Parameters: `Q₀`, `T₀`, `hQ`, `𝔉`, `i`. -/
@[kb "siegel1935" "Über die analytische Theorie der quadratischen Formen; measure of representations of forms [unverified]"]
def repMeasureT (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c) (i : DC Q₀) : ℝ≥0∞ :=
  repMeasureOf (unitGroup Q₀ i) (repsT Q₀ T₀ i) 𝔉.μH

/-! ### The theta integral -/

theorem continuous_GInf_smulT : Continuous fun p : GInfSO Q₀ × (Fin r → VInf F N) => p.1 • p.2 :=
  continuous_pi fun j => (continuous_GInf_smul Q₀).comp
    (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))

theorem measurable_GInf_inv_smulT {Φ : (Fin r → VInf F N) → ℝ≥0∞} (hΦ : Measurable Φ) (y : Fin r → VInf F N) :
    Measurable fun a : GInfSO Q₀ => Φ (a⁻¹ • y) :=
  hΦ.comp (Measurable.of_eval fun j =>
    ((continuous_GInf_smul Q₀).comp ((continuous_inv).prodMk (continuous_const (y := y j)))).measurable)

/-- **Exact measurable fundamental domain of the arithmetic stabilizer of a frame** $\Gamma_{b,y}$ in
$\operatorname{Stab}_{G_\infty}(y)$. -/
theorem exists_fd_stabArithT (b : SOAf Q₀) (y : Fin r → VInf F N) :
    ∃ DH : Set (stabilizer (GInfSO Q₀) y), MeasurableSet DH ∧
      ∀ h : stabilizer (GInfSO Q₀) y, ∃! γ : stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y, γ • h ∈ DH := by
  haveI := discreteTopology_levelGroup Q₀ b
  haveI : DiscreteTopology (stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y) :=
    DiscreteTopology.of_continuous_injective
      (f := fun γ : stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y =>
        (⟨((γ : stabilizer (GInfSO Q₀) y) : GInfSO Q₀), γ.2⟩ : levelGroup (GammaSOAdele Q₀) (KSO Q₀) b))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      fun a c hac => Subtype.ext (Subtype.ext (congrArg
        (fun z : levelGroup (GammaSOAdele Q₀) (KSO Q₀) b => (z : GInfSO Q₀)) hac))
  haveI : SecondCountableTopology (stabilizer (GInfSO Q₀) y) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact exists_measurableSet_forall_existsUnique_smul_mem (G := stabilizer (GInfSO Q₀) y)
    (stabArith (levelGroup (GammaSOAdele Q₀) (KSO Q₀) b) y)

/-- **The theta integral of frames, classically** (Siegel 1935/1936; Weil 1982 §2.4): for every archimedean fibration
`𝔉` of $\mu_\infty$ over a set `P` of frames containing the archimedean images of the rational frames of $T_0$, every
fundamental domain $E$ of $SO(V)(F)$ in $SO(V)(\mathbb A)$ and every measurable $\Phi\ge0$ on $V_\infty^r$,
$$\int_E\theta\,d\mu = \mu_f(SO(\hat L))\cdot c\cdot\sum_i\rho(M_i, T_0)\cdot\int_T\Phi\circ\tau\,d\sigma,\qquad
  \theta(g) = \sum_{X}\Phi(g_\infty^{-1}X)\,1_{\hat L^r}(g_f^{-1}X).$$ -/
@[kb "siegel1935" "Über die analytische Theorie der quadratischen Formen (measure form, forms) [unverified]"]
theorem lintegral_theta_classicalT [SFinite σ] (𝔉 : ArchFibration (muArchTamSO Q₀ hQ) P σ τ c)
    (hP : ∀ X : RatFrame Q₀ T₀, ratAT Q₀ T₀ X ∈ P) (Φ : (Fin r → VInf F N) → ℝ≥0∞) (hΦ : Measurable Φ)
    (hΦτ : Measurable fun x => Φ (τ x)) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E (muTam Q₀ hQ fun _ => 1)) :
    ∫⁻ g in E, thetaFn (ratAT Q₀ T₀) (ratFT Q₀ T₀) Φ (latHatT F N r) g ∂muTam Q₀ hQ (fun _ => 1) =
      muFin Q₀ (fun _ => 1) (KSO Q₀) * c * (∑' i, repMeasureT Q₀ T₀ hQ 𝔉 i) * ∫⁻ x, Φ (τ x) ∂σ := by
  have := countable_GammaSOAdele Q₀
  exact lintegral_theta_eq (Γ := GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (dcRep Q₀)
    (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFin Q₀ fun _ => 1) (ratAT_smul Q₀ T₀) (ratFT_smul Q₀ T₀) (ratAT_injective Q₀ T₀)
    (latHatT_stable Q₀) 𝔉 hP (fun i y => exists_fd_stabArithT Q₀ (dcRep Q₀ i) y) Φ
    (measurable_GInf_inv_smulT Q₀ hΦ) hΦτ hE

end QuadFormsKB.Tamagawa.Indefinite
