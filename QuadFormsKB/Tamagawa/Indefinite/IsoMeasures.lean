/-
# The norm-one measures of representations with an isotropic rank-2 complement

**Layer:** number fields. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 2$ variables (any
signature), $T_0$ nondegenerate of rank $r$, $\Xi$ a rational frame ($Q_0\circ\Xi = T_0$), and the complement
$W = \Xi^\perp$ **isotropic**: $\delta = -\det H_{Q_0}\det H_{T_0}$ (`deltaForms`) is a square in $F$ (`hiso`; by
`complAnisotropic_iff` this is the isotropy of $W$ for every rational frame). Then $H_\Xi\cong SO(W)(F_\infty)$ is a split
torus and every classical stabilizer volume $\operatorname{vol}(\Gamma_{i,X}\backslash H_X)$ is infinite.

**Defines**
* `isoTower`: algebraic frame data `FrameTowerAlg Q₀ hQ 2 (cols Ξ.1)` (chosen), with complement form $Q''$ (binary,
  isotropic: `isotropicF_isoTower`), an isotropic vector `isoVec` of $Q''$, $\chi$ its eigenvalue character;
* `isoFrameLam` $=\prod_{w\mid\infty}|\det g|_w^3/c_F(2)$ ($g = [\Xi\mid C]$, as in `frameLamRank2`);
* `isoStabBase` $=\lambda\cdot\mu^{\mathrm{Tam}}_{Q'',\infty}|_{\{0\le\log|\chi|_\infty<1\}}$ on $SO(Q'')(F_\infty)$ and
  **`isoStabMeasure X`**: at $X = a\,\Xi_\infty$ its transport by $h\mapsto a\,\iota_\infty(h)\,a^{-1}$ to $H_X$ (well defined
  because $H_\Xi$ is commutative); the restriction to the shell makes
  $\operatorname{covol}(\Gamma_{i,X}, \text{this measure}) = \operatorname{vol}(\Gamma_{i,X}\backslash H^1_X)$, the volume of the
  norm-one stabilizer $H^1_X = \ker|\chi_X|_\infty$ for $\mu = \mu^1\times dt/t$;
* **`repMeasureIso`** $\rho^1(M_i,T_0) = \sum_{X\in\Gamma_i\backslash R(M_i,T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H^1_X)$,
  Siegel's measure of representations, regularized.
-/
import QuadFormsKB.Tamagawa.Indefinite.IsoOrbitAlg
import QuadFormsKB.Tamagawa.Indefinite.IsoTorus
import QuadFormsKB.Tamagawa.Indefinite.Rank2Compl
import QuadFormsKB.Tamagawa.Measure.Weil.BinaryIsoFacts

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F]

/-! ### Generic facts on the algebraic frame data -/

section Generic

variable {r n' : ℕ} (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (Ξ : RatFrame Q₀ T₀) (D : FrameTowerAlg Q₀ hQ n' (cols Ξ.1))

/-- $\iota_\infty(h)$ fixes $\Xi_\infty$. -/
theorem FrameTowerAlg.ιInf_smul_ratAT (h : GInfSO D.Q'') : D.ιInf h • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
  have := congrArg splitFrame (D.fix ((h, 1) : SOAdele D.Q''))
  rw [splitFrame_smul Q₀, splitFrame_ratFrame] at this
  exact congrArg Prod.fst this

/-- $\iota_f(h)$ fixes $\Xi_f$. -/
theorem FrameTowerAlg.ιFin_smul_ratFT (h : SOAf D.Q'') : D.ιFin h • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
  have := congrArg splitFrame (D.fix ((1, h) : SOAdele D.Q''))
  rw [splitFrame_smul Q₀, splitFrame_ratFrame] at this
  exact congrArg Prod.snd this

/-- $\iota_\infty$ is injective. -/
theorem FrameTowerAlg.ιInf_injective : Function.Injective D.ιInf := fun a b hab => by
  have := D.injective (a₁ := ((a, 1) : SOAdele D.Q'')) (a₂ := (b, 1)) (Prod.ext hab (by simp))
  exact congrArg Prod.fst this

/-- $\iota_f$ is injective. -/
theorem FrameTowerAlg.ιFin_injective : Function.Injective D.ιFin := fun a b hab => by
  have := D.injective (a₁ := ((1, a) : SOAdele D.Q'')) (a₂ := (1, b)) (Prod.ext (by simp) hab)
  exact congrArg Prod.snd this

/-- The stabilizer of $\Xi_\infty$ in $G_\infty$ is $\iota_\infty(SO(Q'')(F_\infty))$. -/
theorem FrameTowerAlg.stab_ιInf (g : GInfSO Q₀) (hg : g • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ) : ∃ h, D.ιInf h = g := by
  obtain ⟨h, hh⟩ := IsoAlg.stabIn_frameCprod Q₀ hQ T₀ Ξ D (g, 1) (by rw [prod_smul_def, hg, one_smul])
  exact ⟨h.1, congrArg Prod.fst hh⟩

/-- The stabilizer of $\Xi_f$ in $G(\mathbb A_f)$ is $\iota_f(SO(Q'')(\mathbb A_f))$. -/
theorem FrameTowerAlg.stab_ιFin (g : SOAf Q₀) (hg : g • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ) : ∃ h, D.ιFin h = g :=
  stab_iotaB (IsoAlg.stabIn_frameCprod Q₀ hQ T₀ Ξ D) g hg

theorem FrameTowerAlg.measurableEmbedding_ιInf : MeasurableEmbedding D.ιInf := by
  have := polishSpace_of_isTopologicalGroup (GInfSO D.Q'')
  have := polishSpace_of_isTopologicalGroup (GInfSO Q₀)
  have : MeasurableSpace.CountablySeparated (GInfSO Q₀) := inferInstance
  exact D.measurable_ιInf.measurableEmbedding (D.ιInf_injective Q₀ hQ T₀ Ξ)

include D in
/-- **Witt's theorem for frames** with the algebraic frame data ($n'\ge1$): $SO(V)(F)$ is transitive on the rational
frames of $T_0$. -/
theorem FrameTowerAlg.exists_smul_eq_ratFrame (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') (X : RatFrame Q₀ T₀) :
    ∃ γ : GammaSOAdele Q₀, γ • Ξ = X := by
  obtain ⟨φ, hφO, hdet, hφΞ⟩ := witt_core (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F))
    (D.Q''.map (algebraMap (𝓞 F) F)) (witt_nd T₀ hT) (witt_nd _ D.hQ'') hn' Ξ.1 D.Cm Ξ.2 D.hCH D.hΞC
    (X := X.1) X.2
  refine ⟨gammaEquiv Q₀ ⟨⟨φ, hφO⟩, hdet⟩, Subtype.ext ?_⟩
  rw [ratFrame_smul_val, MulEquiv.symm_apply_apply]
  exact hφΞ

/-- **The conjugated stabilizer embedding** $h\mapsto a\,\iota_\infty(h)\,a^{-1}$, $SO(Q'')(F_\infty)\to H_{a\Xi}$. -/
def FrameTowerAlg.conjInf (a : GInfSO Q₀) : GInfSO D.Q'' →* stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ) where
  toFun h := ⟨a * D.ιInf h * a⁻¹, by
    show (a * D.ιInf h * a⁻¹) • a • ratAT Q₀ T₀ Ξ = a • ratAT Q₀ T₀ Ξ
    rw [mul_smul, mul_smul, inv_smul_smul, D.ιInf_smul_ratAT]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' h h' := Subtype.ext (by simp [mul_assoc])

theorem FrameTowerAlg.conjInf_apply (a : GInfSO Q₀) (h : GInfSO D.Q'') :
    ((D.conjInf Q₀ hQ T₀ Ξ a h : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ)) : GInfSO Q₀) = a * D.ιInf h * a⁻¹ :=
  rfl

theorem FrameTowerAlg.measurable_conjInf (a : GInfSO Q₀) : Measurable (D.conjInf Q₀ hQ T₀ Ξ a) :=
  (((measurable_const_mul a).comp D.measurable_ιInf).mul_const _).subtype_mk

end Generic

/-! ### The isotropic complement -/

section Iso

variable {r : ℕ} (Q₀ : QuadForm (𝓞 F) (r + 2)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r)
  (hT : T₀.Nondegenerate) (hiso : IsSquare (algebraMap (𝓞 F) F (deltaForms Q₀ T₀))) (Ξ : RatFrame Q₀ T₀)

/-- **The algebraic frame data of $\Xi$** (complement of rank $2$; chosen). -/
def isoTower : FrameTowerAlg Q₀ hQ 2 (cols Ξ.1) :=
  Classical.choice (nonempty_frameTowerAlg_ratFrame (by norm_num) Q₀ hQ T₀ hT Ξ)

include hiso in
/-- **The complement form is isotropic.** -/
theorem isotropicF_isoTower : IsotropicF (isoTower Q₀ hQ T₀ hT Ξ).Q'' := by
  rw [isotropicF_iff_not_anisotropicF]
  intro hA
  exact ((anisotropicF_adapted_iff Q₀ T₀ hT (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT)).1 hA) hiso

/-- An isotropic vector of the complement form. -/
def isoVec : Fin 2 → F := (isotropicF_isoTower Q₀ hQ T₀ hT hiso Ξ).choose

theorem isIsoVec_isoVec : IsIsoVec (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoVec Q₀ hQ T₀ hT hiso Ξ) :=
  (isotropicF_isoTower Q₀ hQ T₀ hT hiso Ξ).choose_spec

open Classical in
/-- **The scale of the stabilizer measures**: $\lambda = \prod_{w\mid\infty}|\det g|_w^{3}/c_F(2)$ (normalized absolute values,
$g = [\Xi\mid C]$), as in `frameLamRank2`. -/
def isoFrameLam : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal},
      |σR w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT).g.val.det| ^ (2 + 1)) *
    (∏ w : {w : InfinitePlace F // w.IsComplex},
      ‖σC w (IsoAlg.towerAdapted Q₀ hQ T₀ Ξ (isoTower Q₀ hQ T₀ hT Ξ) hT).g.val.det‖ ^ (2 * (2 + 1))) / cF F 2)

/-- **The norm-one stabilizer measure at $\Xi$**, on $SO(Q'')(F_\infty)$: $\lambda$ times Weil's archimedean Tamagawa
measure (`muArchTamSO`) restricted to the shell $\{0\le\log|\chi(h)|_\infty<1\}$. -/
def isoStabBase : Measure (GInfSO (isoTower Q₀ hQ T₀ hT Ξ).Q'') :=
  isoFrameLam Q₀ hQ T₀ hT Ξ • (muArchTamSO (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'').restrict
    (isoShellInf (isoTower Q₀ hQ T₀ hT Ξ).Q'' (isoTower Q₀ hQ T₀ hT Ξ).hQ'' (isIsoVec_isoVec Q₀ hQ T₀ hT hiso Ξ))

/-- The norm-one stabilizer measure at $X = a\,\Xi_\infty$: the transport of `isoStabBase` by
$h\mapsto a\,\iota_\infty(h)\,a^{-1}$. -/
def isoStabAt (a : GInfSO Q₀) {X : Fin r → VInf F (r + 2)} (hX : a • ratAT Q₀ T₀ Ξ = X) :
    Measure (stabilizer (GInfSO Q₀) X) := by
  subst hX
  exact (isoStabBase Q₀ hQ T₀ hT hiso Ξ).map ((isoTower Q₀ hQ T₀ hT Ξ).conjInf Q₀ hQ T₀ Ξ a)

open Classical in
/-- **The norm-one stabilizer measures**: at $X$ in the $G_\infty$-orbit of $\Xi_\infty$, `isoStabAt` for a chosen
$a$ with $a\,\Xi_\infty = X$ (the choice does not matter: $H_\Xi$ is commutative); $0$ elsewhere. -/
def isoStabMeasure (X : Fin r → VInf F (r + 2)) : Measure (stabilizer (GInfSO Q₀) X) :=
  if hX : ∃ a : GInfSO Q₀, a • ratAT Q₀ T₀ Ξ = X then isoStabAt Q₀ hQ T₀ hT hiso Ξ hX.choose hX.choose_spec else 0

/-- **Siegel's measure of representations, regularized** (norm-one stabilizers):
$$\rho^1(M_i, T_0) = \sum_{X\in\Gamma_i\backslash R(M_i,T_0)}\operatorname{vol}(\Gamma_{i,X}\backslash H^1_X),$$
each term the covolume of $\Gamma_{i,X}$ in $H_X$ for `isoStabMeasure X` (the measure on the shell
$\{0\le\log|\chi_X|_\infty<1\}$, which for $\mu = \mu^1\times dt/t$ is the norm-one volume). Parameters: `Q₀`, `hQ`, `T₀`,
`hT`, `hiso`, `Ξ`, `i`. -/
@[kb "siegel1944indef" "On the theory of indefinite quadratic forms (measure of representations; the excluded case n - m = 2 with square determinant, regularized) [unverified]"]
def repMeasureIso (i : DC Q₀) : ℝ≥0∞ :=
  repMeasureOf (unitGroup Q₀ i) (repsT Q₀ T₀ i) (isoStabMeasure Q₀ hQ T₀ hT hiso Ξ)

end Iso

end QuadFormsKB.Tamagawa.Indefinite
