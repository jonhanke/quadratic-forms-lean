import QuadFormsKB.Tamagawa.Measure.Weil.SphereOrbitsNF
import QuadFormsKB.Tamagawa.Measure.Weil.SphereUnfoldAbstract
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures
import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling

/-!
# The adelic spherical unfolding $Z^+(s) = \sum_\rho\frac{\operatorname{covol}(G'_\rho)}2Z(s,\rho)$

$F$ any number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $m = k+1\ge2$ variables (any signature; no
anisotropy is needed for this step), $G = SO(V)$, $\Gamma = G(F)$ diagonally in $G(\mathbb A)$ = `SOAdele Q₀` with Weil's
Tamagawa measure $\mu$ = `muTam Q₀ hQ 1`, $\mathbb A^\times$ with $\nu$ = `tamIdeles F` and
$F^\times$ = `diagUnitsSub F`. For $\Phi : \mathbb A_F^m\to[0,\infty]$ measurable and fundamental domains $D$ of $\Gamma$ and
$D_M$ of $F^\times$, Weil's additive zeta function (Weil 1982, §4.4, (4), p. 97; §4.5, p. 109; only $Q(\xi)\ne0$) is
$$Z^+(s) = \int_D\int_{D_M}\|z\|^{m+2s}\sum_{\xi\in F^m,\ Q(\xi)\ne0}\Phi(z\,g^{-1}\xi)\,d\nu(z)\,d\mu(g)
  \qquad(\texttt{adelicZetaPlus}).$$

**The adelic sphere data.** For each square class $c\in F^\times/F^{\times2}$ represented by $Q$ over $F$ (`RepClasses`),
$\rho_c$ = `Quotient.out c`, an `AdelicSphereData` consists of a base point $\xi_c\in T(\rho_c)(F)$, a form $Q'_c$ in $k$
variables (the complement $\xi_c^\perp$), a homomorphism $\iota_c : SO(Q'_c)(\mathbb A)\to SO(V)(\mathbb A)$, a set
$T_c\subseteq\mathbb A_F^m$ (the adelic sphere $T(\rho_c)_{\mathbb A}$), a measure $\sigma_c$ on it and coordinates
$T_c\times SO(Q'_c)(\mathbb A)\cong SO(V)(\mathbb A)$. Its properties (`AdelicSphereFibration`, **input**: Weil's
Lemma 2.4.1/Thm 2.4.3 for $G/G'_\rho = T(\rho)$ adelically, i.e. the assembly of the local fibration identities
with the product formula) say that the coordinates are $(x, h)\mapsto\iota(h)s(x)^{-1}$-shaped, that
$\iota_c$ identifies $SO(Q'_c)(F)$ with the stabilizer of $\xi_c$ in $SO(V)(F)$, and that
$\mu = \mathrm{coord}_*(\sigma_c\otimes\mu'_c)$ with $\mu'_c$ = `muTam (Q' c)` (constant exactly $1$).

**Main results.**
* **`adelicZetaPlus_eq_tsum_covolume`** (Step 1, exact constants, in $[0,\infty]$, **no hypothesis on
  $\operatorname{vol}(\Gamma\backslash G)$**, every real $s$):
  $$Z^+(s) = \sum_{c}\frac{\operatorname{covol}(SO(Q'_c)(F)\backslash SO(Q'_c)(\mathbb A))}{2}\,Z(s,c),\qquad
    Z(s,c) = \int_{T_c}\int_{\mathbb A^\times}\|z\|^{m+2s}\Phi(zx)\,d\nu(z)\,d\sigma_c(x)\quad(\texttt{adelicSphZeta}).$$
  Proved from the abstract unfolding (`SphereUnfoldAbstract.lean`), the shells and Witt's theorem
  (`SphereOrbitsNF.lean`) and the adelic action (`SOAdeleAction.lean`), given `AdelicSphereFibration`.
* **`adelicZetaPlus_eq_tsum_of_complementTauTwo`**: with the induction hypothesis `AdelicComplementTauTwo`
  ($\tau(SO(Q'_c)) = 2$ for the $(m-1)$-dimensional complements; exactly `TamagawaNumberTwoAdelic (Q' c)`):
  $Z^+(s) = \sum_cZ(s,c)$.
* **`adelicZetaPlus_lt_top`** (in `TauTwoAnisotropic.lean`, which imports the spherical Euler product file):
  in addition, if each $Z(s,c)$ is $\kappa$ times the Euler product $Z(s,\rho_c)$ = `sphericalZetaAtNF`
  (`AdelicSphericalEuler`, input), then $Z^+(s) < \infty$ for $s > 0$ and $m\ge5$
  (the summability of the spherical sum over all square classes).

The factor $\frac12$ is the two-to-one parametrization $F^\times\times T(\rho)(F)\to\{Q\in\rho F^{\times2}\}$
(Weil p. 109, "runs twice"; cf. the erratum recorded in `AdditiveGenus.lean`).
-/

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure QuadFormsKB.SphericalZeta

variable {F : Type} [Field F] [NumberField F]

/-! ### The weight $\|z\|^{m+2s}$ and the multiplicative transform -/

/-- The weight $\|z\|_{\mathbb A}^{m+2s}$ on $\mathbb A^\times$. -/
def zetaWeight (s : ℝ) (m : ℕ) (z : (Adeles F)ˣ) : ℝ≥0∞ := ENNReal.ofReal (ideleNorm F z ^ ((m : ℝ) + 2 * s))

theorem measurable_zetaWeight (s : ℝ) (m : ℕ) : Measurable (zetaWeight (F := F) s m) :=
  ENNReal.measurable_ofReal.comp ((continuous_ideleNorm.rpow_const fun z =>
    Or.inl (ideleNorm_pos z).ne').measurable)

/-- $\|\lambda z\| = \|z\|$ for $\lambda\in F^\times$ (product formula). -/
theorem zetaWeight_mul_diag (s : ℝ) (m : ℕ) (l : diagUnitsSub F) (z : (Adeles F)ˣ) :
    zetaWeight s m ((l : (Adeles F)ˣ) * z) = zetaWeight s m z := by
  obtain ⟨_, a, rfl⟩ := l
  simp only [zetaWeight, ideleNorm_mul, ideleNorm_diagUnits, one_mul]

variable {n : ℕ}

/-- The ideles act on $\mathbb A_F^n$ measurably. -/
theorem measurable_units_smul :
    Measurable fun p : (Adeles F)ˣ × AdeleSpace F (Fin n) => p.1 • p.2 :=
  ((Units.continuous_val.comp continuous_fst).smul continuous_snd).measurable

/-- **The multiplicative transform** $M_s\Phi(y) = \int_{\mathbb A^\times}\|z\|^{m+2s}\Phi(zy)\,d\nu(z)$. -/
def mellinPhi (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (s : ℝ) (y : AdeleSpace F (Fin n)) : ℝ≥0∞ :=
  ∫⁻ z, zetaWeight s n z * Φ (z • y) ∂tamIdeles F

theorem measurable_mellinPhi {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ) (s : ℝ) :
    Measurable (mellinPhi Φ s) := by
  have : Measurable fun p : AdeleSpace F (Fin n) × (Adeles F)ˣ => zetaWeight s n p.2 * Φ (p.2 • p.1) :=
    ((measurable_zetaWeight s n).comp measurable_snd).mul
      (hΦ.comp (measurable_units_smul.comp (measurable_snd.prodMk measurable_fst)))
  exact this.lintegral_prod_right'

/-! ### Weil's additive zeta function -/

open Classical in
/-- **Weil's additive zeta function** (Weil 1982, §4.4, (4), p. 97, the part $Q(\xi)\ne0$; §4.5, p. 109), adelic form:
$$Z^+(s) = \int_D\int_{D_M}\|z\|^{n+2s}\sum_{\xi\in F^n,\ Q(\xi)\ne0}\Phi(z\,g^{-1}\xi)\,d\nu(z)\,d\mu(g)$$
in $[0,\infty]$, with $D$ a fundamental domain of $SO(V)(F)$ in $SO(V)(\mathbb A)$ (left action, `muTam`), $D_M$ one of
$F^\times$ in $\mathbb A^\times$ (`tamIdeles`). Parameters: `Q₀`, `hQ`, `Φ`, `D`, `DM`, `s`. -/
@[kb "weil1982" "§4.4, (4), p. 97 (Z⁺, Q(ξ) ≠ 0); §4.5, p. 109"]
def adelicZetaPlus (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞)
    (D : Set (SOAdele Q₀)) (DM : Set (Adeles F)ˣ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in D, ∫⁻ z in DM, zetaWeight s n z *
    ∑' ξ : Fin n → F, (if qF Q₀ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0) ∂tamIdeles F ∂muTam Q₀ hQ 1

/-- The square classes represented by $Q$ over $F$: $T(\rho_c)(F)\ne\emptyset$. -/
def RepClasses (Q₀ : QuadForm (𝓞 F) n) : Type :=
  {c : SqClasses F // ∃ η : Fin n → F, qF Q₀ η = ((Quotient.out c : Fˣ) : F)}

instance (Q₀ : QuadForm (𝓞 F) n) : Countable (RepClasses Q₀) := by
  unfold RepClasses
  haveI : Countable (SqClasses F) := QuotientGroup.mk_surjective.countable
  infer_instance

/-! ### The adelic sphere data and Weil's fibration (input) -/

variable {k : ℕ}

/-- **Adelic data for the sphere $T(\rho)$** (Weil 1982, §4.5, p. 109; Lemma 2.4.1, Thm 2.4.3): a base point
$\xi\in T(\rho)(F)$, the embedding $\iota : SO(Q')(\mathbb A)\to SO(V)(\mathbb A)$ of the stabilizer (complement form $Q'$
in $k$ variables), the adelic sphere $T\subseteq\mathbb A_F^{k+1}$ with a measure $\sigma$, and coordinates
$T\times SO(Q')(\mathbb A)\cong SO(V)(\mathbb A)$. Pure data, no properties (those are `AdelicSphereFibration`).
Fields: `ξ`, `ι`, `T`, `σ`, `coord`. -/
structure AdelicSphereData (Q₀ : QuadForm (𝓞 F) (k + 1)) (ρ : F) (Q' : QuadForm (𝓞 F) k) where
  /-- The base point $\xi\in T(\rho)(F)$. -/
  ξ : RatSphere Q₀ ρ
  /-- The embedding of $SO(\xi^\perp)(\mathbb A)$. -/
  ι : SOAdele Q' →* SOAdele Q₀
  /-- The adelic sphere $T(\rho)_{\mathbb A}$. -/
  T : Set (AdeleSpace F (Fin (k + 1)))
  /-- Its measure $\sigma$. -/
  σ : Measure T
  /-- The coordinates $T\times SO(Q')(\mathbb A)\cong SO(V)(\mathbb A)$. -/
  coord : T × SOAdele Q' ≃ᵐ SOAdele Q₀

/-- **Weil's adelic fibration over $T(\rho)$** (**input**; Weil 1982, Lemma 2.4.1, Thm 2.4.3, applied on p. 109 to
$G/G'_\rho = T(\rho)$). For data `D`:
* `mul`, `orbit`: $\mathrm{coord}(x, h'h) = \iota(h')\mathrm{coord}(x,h)$ and $\mathrm{coord}(x,h)^{-1}\xi = x$;
* `gamma_mem`, `stab`: $\iota$ maps $SO(Q')(F)$ into $SO(V)(F)$, onto the stabilizer of $\xi$;
* `sFinite`: $\sigma$ is s-finite;
* `fib`: **$\mu_{SO(V)} = \mathrm{coord}_*(\sigma\otimes\mu_{SO(Q')})$** for Weil's Tamagawa measures (`muTam`, $\lambda_v = 1$),
  with constant exactly $1$ (the local constants $|2\rho|_v^{-k}$ of the local fibration identities multiply to $1$).
It says nothing about the covolume of $SO(V)(F)$ or of $SO(Q')(F)$. Proving it needs the adelic section (local
two-reflection sections, integral at almost all $v$), the restricted product of the local Leray measures, and the
local fibration identities. -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 109 (fibration over T(ρ))"]
structure AdelicSphereFibration (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) {ρ : F}
    {Q' : QuadForm (𝓞 F) k} (hQ' : Q'.Nondegenerate) (D : AdelicSphereData Q₀ ρ Q') : Prop where
  /-- Left equivariance in the fibre coordinate. -/
  mul : ∀ (x : D.T) (h h' : SOAdele Q'), D.coord (x, h' * h) = D.ι h' * D.coord (x, h)
  /-- The first coordinate is the orbit point $g^{-1}\xi$. -/
  orbit : ∀ (x : D.T) (h : SOAdele Q'), (D.coord (x, h))⁻¹ • diagVec F (Fin (k + 1)) D.ξ.1 = x.1
  /-- $\iota(SO(Q')(F))\subseteq SO(V)(F)$. -/
  gamma_mem : ∀ h ∈ GammaSOAdele Q', D.ι h ∈ GammaSOAdele Q₀
  /-- The stabilizer of $\xi$ in $SO(V)(F)$ is contained in $\iota(SO(Q')(F))$. -/
  stab : ∀ γ ∈ GammaSOAdele Q₀, γ • diagVec F (Fin (k + 1)) D.ξ.1 = diagVec F (Fin (k + 1)) D.ξ.1 →
    ∃ h ∈ GammaSOAdele Q', D.ι h = γ
  /-- $\sigma$ is s-finite. -/
  sFinite : SFinite D.σ
  /-- The fibration identity of Tamagawa measures, constant $1$. -/
  fib : muTam Q₀ hQ 1 = (D.σ.prod (muTam Q' hQ' 1)).map D.coord

/-- **The adelic spherical zeta function** $Z(s,\rho) = \int_{T(\rho)_{\mathbb A}}\int_{\mathbb A^\times}
\|z\|^{m+2s}\Phi(zx)\,d\nu(z)\,d\sigma(x)$ (Weil 1982, §4.5, (1), p. 102, and p. 109), for the data `D`. -/
@[kb "weil1982" "§4.5, (1), p. 102; p. 109 (Z(s,ρ) = ∫_{T(ρ)_A}…)"]
def adelicSphZeta {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F} {Q' : QuadForm (𝓞 F) k} (D : AdelicSphereData Q₀ ρ Q')
    (Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, mellinPhi Φ s x.1 ∂D.σ

/-! ### Auxiliary algebra -/

/-- $\lambda\xi\mapsto\lambda\cdot\xi$: the diagonal embedding is $F^\times$-equivariant. -/
theorem diagVec_units_smul (l : Fˣ) (η : Fin n → F) :
    diagVec F (Fin n) ((l : F) • η) = diagUnits F l • diagVec F (Fin n) η := by
  funext i
  show diagRing F ((l : F) * η i) = diagRing F (l : F) * diagRing F (η i)
  exact map_mul _ _ _

/-- $F^\times\cong$ `diagUnitsSub F`. -/
def unitsEquivDiag : Fˣ ≃ diagUnitsSub F :=
  (MonoidHom.ofInjective (f := diagUnits F) fun ξ η h =>
    Units.ext ((diagRing F).injective (congrArg Units.val h))).toEquiv

theorem unitsEquivDiag_coe (l : Fˣ) : ((unitsEquivDiag l : diagUnitsSub F) : (Adeles F)ˣ) = diagUnits F l := rfl

open Classical in
/-- The indicator sum over $\{Q = \rho\}$ is the sum over the rational sphere. -/
theorem tsum_ite_eq_tsum_ratSphere (Q₀ : QuadForm (𝓞 F) n) (ρ : F) (f : (Fin n → F) → ℝ≥0∞) :
    ∑' η : Fin n → F, (if qF Q₀ η = ρ then f η else 0) = ∑' η : RatSphere Q₀ ρ, f η.1 := by
  rw [show (fun η => if qF Q₀ η = ρ then f η else 0) = {η | qF Q₀ η = ρ}.indicator f from
    funext fun η => by simp [Set.indicator_apply]]
  exact (tsum_subtype {η | qF Q₀ η = ρ} f).symm

/-- The representative $\rho_c$ of a represented square class. -/
abbrev repρ {Q₀ : QuadForm (𝓞 F) n} (c : RepClasses Q₀) : F := ((Quotient.out c.1 : Fˣ) : F)

theorem repρ_ne_zero {Q₀ : QuadForm (𝓞 F) n} (c : RepClasses Q₀) : repρ c ≠ 0 := (Quotient.out c.1).ne_zero

open Classical in
/-- **Pointwise rational algebra** (Weil 1982, §4.5, p. 109): for $y_\xi = g^{-1}\xi$,
$$\sum_{Q(\xi)\ne0}\Phi(z\,g^{-1}\xi) = \frac12\sum_{c}\sum_{\eta\in T(\rho_c)(F)}\sum_{\lambda\in F^\times}
  \Phi(z\lambda\,g^{-1}\eta).$$ -/
theorem tsum_ne_zero_eq_tsum_repClasses (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞)
    (g : SOAdele Q₀) (z : (Adeles F)ˣ) :
    ∑' ξ : Fin n → F, (if qF Q₀ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0) =
      2⁻¹ * ∑' c : RepClasses Q₀, ∑' η : RatSphere Q₀ (repρ c), ∑' l : diagUnitsSub F,
        Φ (z • (l : (Adeles F)ˣ) • g⁻¹ • diagVec F (Fin n) η.1) := by
  rw [tsum_ne_zero_eq_tsum_sqClasses (qF Q₀) (qF_smul Q₀) (fun ξ => Φ (z • g⁻¹ • diagVec F (Fin n) ξ))]
  congr 1
  set T : SqClasses F → ℝ≥0∞ := fun c => ∑' η : RatSphere Q₀ ((Quotient.out c : Fˣ) : F), ∑' l : diagUnitsSub F,
    Φ (z • (l : (Adeles F)ˣ) • g⁻¹ • diagVec F (Fin n) η.1) with hT
  have hterm : ∀ c : SqClasses F, ∑' l : Fˣ, ∑' η : Fin n → F,
      (if qF Q₀ η = ((Quotient.out c : Fˣ) : F) then Φ (z • g⁻¹ • diagVec F (Fin n) ((l : F) • η)) else 0) = T c := by
    intro c
    rw [tsum_congr fun l : Fˣ => tsum_ite_eq_tsum_ratSphere Q₀ _
      (fun η => Φ (z • g⁻¹ • diagVec F (Fin n) ((l : F) • η))), ENNReal.tsum_comm]
    refine tsum_congr fun η => ?_
    rw [← (unitsEquivDiag (F := F)).tsum_eq (fun l : diagUnitsSub F =>
      Φ (z • (l : (Adeles F)ˣ) • g⁻¹ • diagVec F (Fin n) η.1))]
    refine tsum_congr fun l => ?_
    rw [unitsEquivDiag_coe, diagVec_units_smul, smul_units_comm]
  simp_rw [hterm]
  have hsupp : Function.support T ⊆ {c | ∃ η : Fin n → F, qF Q₀ η = ((Quotient.out c : Fˣ) : F)} := by
    intro c hc
    by_contra h
    apply hc
    simp only [hT]
    haveI : IsEmpty (RatSphere Q₀ ((Quotient.out c : Fˣ) : F)) := ⟨fun η => h ⟨η.1, η.2⟩⟩
    exact tsum_empty
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

/-! ### The inner integral over $\mathbb A^\times/F^\times$ -/

open Classical in
/-- The inner integral of $Z^+$: $\int_{D_M}\|z\|^{n+2s}\sum_{Q(\xi)\ne0}\Phi(z\,g^{-1}\xi)\,d\nu(z)$, a function of $g$. -/
def adelicInner (Q₀ : QuadForm (𝓞 F) n) (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (DM : Set (Adeles F)ˣ) (s : ℝ)
    (g : SOAdele Q₀) : ℝ≥0∞ :=
  ∫⁻ z in DM, zetaWeight s n z *
    ∑' ξ : Fin n → F, (if qF Q₀ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0) ∂tamIdeles F

theorem adelicZetaPlus_eq_lintegral_inner (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (Φ : AdeleSpace F (Fin n) → ℝ≥0∞) (D : Set (SOAdele Q₀)) (DM : Set (Adeles F)ˣ) (s : ℝ) :
    adelicZetaPlus Q₀ hQ Φ D DM s = ∫⁻ g in D, adelicInner Q₀ Φ DM s g ∂muTam Q₀ hQ 1 := rfl

open Classical in
/-- **The multiplicative stage, for fixed $g$** (Weil 1982, §4.5, p. 109): the inner integral of $Z^+$ is
$\frac12\sum_c\sum_{\eta\in T(\rho_c)(F)}M_s\Phi(g^{-1}\eta)$. No fibration is needed here. -/
@[kb "weil1982" "§4.5, p. 109 (the k^×-sum unfolds 𝔸^×/k^× to 𝔸^×)"]
theorem adelicInner_eq (Q₀ : QuadForm (𝓞 F) n) {Φ : AdeleSpace F (Fin n) → ℝ≥0∞} (hΦ : Measurable Φ)
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ)
    (g : SOAdele Q₀) :
    adelicInner Q₀ Φ DM s g =
      2⁻¹ * ∑' c : RepClasses Q₀, ∑' η : RatSphere Q₀ (repρ c), mellinPhi Φ s (g⁻¹ • diagVec F (Fin n) η.1) := by
  have hmz : ∀ y : AdeleSpace F (Fin n), Measurable fun z : (Adeles F)ˣ => Φ (z • y) := fun y =>
    hΦ.comp (measurable_units_smul.comp (measurable_id.prodMk measurable_const))
  rw [adelicInner]
  have h1 : ∀ z : (Adeles F)ˣ, zetaWeight s n z *
      ∑' ξ : Fin n → F, (if qF Q₀ ξ ≠ 0 then Φ (z • g⁻¹ • diagVec F (Fin n) ξ) else 0) =
      2⁻¹ * ∑' c : RepClasses Q₀, ∑' η : RatSphere Q₀ (repρ c), zetaWeight s n z *
        ∑' l : diagUnitsSub F, Φ (z • (l : (Adeles F)ˣ) • g⁻¹ • diagVec F (Fin n) η.1) := by
    intro z
    rw [tsum_ne_zero_eq_tsum_repClasses, mul_left_comm]
    simp_rw [ENNReal.tsum_mul_left]
  rw [lintegral_congr h1, lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr two_ne_zero)]
  congr 1
  rw [lintegral_tsum fun c => ?_]
  · refine tsum_congr fun c => ?_
    rw [lintegral_tsum fun η => ?_]
    · refine tsum_congr fun η => ?_
      rw [mellinPhi]
      rw [← lintegral_mul_quotient hDM (zetaWeight s n) (zetaWeight_mul_diag s n) Φ _
        ((measurable_zetaWeight s n).mul (hmz _))]
    · exact ((measurable_zetaWeight s n).mul (Measurable.ennreal_tsum fun l => hmz _)).aemeasurable
  · exact (Measurable.ennreal_tsum fun (η : RatSphere Q₀ _) => (measurable_zetaWeight s n).mul
      (Measurable.ennreal_tsum fun (l : diagUnitsSub F) => hmz _)).aemeasurable

/-! ### The unfolding -/

/-- For data satisfying the fibration, $\iota(h)$ fixes $\xi$ (adelically). -/
theorem OrbitCoord.ι_smul {G H T Y : Type*} [Group G] [Group H] [MeasurableSpace G] [MeasurableSpace H]
    [MeasurableSpace T] [MulAction G Y] {ι : H →* G} {τ : T → Y} {y₀ : Y} (C : OrbitCoord ι τ y₀) (h : H) :
    ι h • y₀ = y₀ := by
  obtain ⟨x, _⟩ := C.coord.symm 1
  have h1 := C.orbit x 1
  have h2 := C.orbit x h
  rw [C.coord_eq x h] at h2
  have h3 : (C.coord (x, 1))⁻¹ • ((ι h)⁻¹ • y₀) = (C.coord (x, 1))⁻¹ • y₀ := by
    rw [smul_smul, ← _root_.mul_inv_rev, h2, h1]
  have h4 : (ι h)⁻¹ • y₀ = y₀ := MulAction.injective _ h3
  exact (inv_smul_eq_iff.mp h4).symm

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {hQ : Q₀.Nondegenerate}

/-- The orbit coordinates of `AdelicSphereData` satisfying the fibration. -/
def AdelicSphereFibration.orbitCoord {ρ : F} {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ ρ Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A) :
    OrbitCoord A.ι (Subtype.val : A.T → AdeleSpace F (Fin (k + 1))) (diagVec F (Fin (k + 1)) A.ξ.1) :=
  ⟨A.coord, hA.mul, hA.orbit⟩

/-- $g^{-1}\eta$ for $\eta = \gamma\xi$ in terms of the coordinates: $= x$ for $(x, h) = \mathrm{coord}^{-1}(\gamma^{-1}g)$. -/
theorem AdelicSphereFibration.inv_smul_eq {ρ : F} {Q' : QuadForm (𝓞 F) k} {hQ' : Q'.Nondegenerate}
    {A : AdelicSphereData Q₀ ρ Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A) (γ : GammaSOAdele Q₀)
    (g : SOAdele Q₀) :
    g⁻¹ • diagVec F (Fin (k + 1)) (γ • A.ξ).1 = (A.coord.symm ((γ : SOAdele Q₀)⁻¹ * g)).1.1 := by
  rw [diagVec_smul_ratSphere, smul_smul, show g⁻¹ * (γ : SOAdele Q₀) = ((γ : SOAdele Q₀)⁻¹ * g)⁻¹ by group]
  exact hA.orbitCoord.inv_smul_eq _

/-- Measurability of the orbit sum $g\mapsto\sum_{\eta\in T(\rho)(F)}f(g^{-1}\eta)$. -/
theorem AdelicSphereFibration.measurable_orbitSum {ρ : F} (hρ : ρ ≠ 0) (hk : 1 ≤ k) {Q' : QuadForm (𝓞 F) k}
    {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ ρ Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    {f : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun g : SOAdele Q₀ => ∑' η : RatSphere Q₀ ρ, f (g⁻¹ • diagVec F (Fin (k + 1)) η.1) := by
  refine Measurable.ennreal_tsum fun η => ?_
  obtain ⟨γ, rfl⟩ := exists_smul_eq_ratSphere Q₀ hQ (by omega) hρ A.ξ η
  simp_rw [hA.inv_smul_eq]
  exact hf.comp (measurable_subtype_coe.comp (measurable_fst.comp
    (A.coord.symm.measurable.comp (measurable_const_mul _))))

/-- **The unfolding along one sphere** (Weil 1982, §4.5, p. 109; the abstract `lintegral_sphere_unfold` instantiated):
$$\int_D\sum_{\eta\in T(\rho)(F)}f(g^{-1}\eta)\,d\mu(g) = \operatorname{covol}(SO(Q')(F)\backslash SO(Q')(\mathbb A))
  \cdot\int_{T}f\,d\sigma.$$ -/
@[kb "weil1982" "§4.5, p. 109 (unfolding along T(ρ)); Lemma 2.4.1, Thm 2.4.3 [unverified page]"]
theorem AdelicSphereFibration.lintegral_unfold {ρ : F} (hρ : ρ ≠ 0) (hk : 1 ≤ k) {Q' : QuadForm (𝓞 F) k}
    {hQ' : Q'.Nondegenerate} {A : AdelicSphereData Q₀ ρ Q'} (hA : AdelicSphereFibration Q₀ hQ hQ' A)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {f : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g in D, ∑' η : RatSphere Q₀ ρ, f (g⁻¹ • diagVec F (Fin (k + 1)) η.1) ∂muTam Q₀ hQ 1 =
      covolume (GammaSOAdele Q') (SOAdele Q') (muTam Q' hQ' 1) * ∫⁻ x, f x.1 ∂A.σ := by
  have := discreteTopology_GammaSOAdele Q'
  have := countable_GammaSOAdele Q₀
  have := countable_GammaSOAdele Q'
  haveI := hA.sFinite
  obtain ⟨DH, hDH, hDHx⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q')
  have hfix : ∀ (h : SOAdele Q') (hh : h ∈ GammaSOAdele Q'),
      (⟨A.ι h, hA.gamma_mem h hh⟩ : GammaSOAdele Q₀) • A.ξ = A.ξ := by
    intro h hh
    apply Subtype.ext
    have e : diagVec F (Fin (k + 1)) ((⟨A.ι h, hA.gamma_mem h hh⟩ : GammaSOAdele Q₀) • A.ξ).1 =
        diagVec F (Fin (k + 1)) A.ξ.1 := by
      rw [diagVec_smul_ratSphere]; exact hA.orbitCoord.ι_smul h
    funext i
    exact diag_injective (congrFun e i)
  have key := lintegral_sphere_unfold (Γ := GammaSOAdele Q₀) (μ := muTam Q₀ hQ 1) (ΓH := GammaSOAdele Q')
    (μH := muTam Q' hQ' 1) (fun η : RatSphere Q₀ ρ => diagVec F (Fin (k + 1)) η.1)
    (fun γ η => diagVec_smul_ratSphere Q₀ γ η) A.ξ
    (fun η => exists_smul_eq_ratSphere Q₀ hQ (by omega) hρ A.ξ η) A.ι A.σ Subtype.val hA.orbitCoord
    hA.gamma_mem hfix (fun γ hγ => hA.stab γ γ.2 (by rw [← diagVec_smul_ratSphere, hγ]))
    hDH hDHx 1 (by rw [one_smul]; exact hA.fib) hD f (hf.comp measurable_subtype_coe)
  rwa [one_mul] at key

/-- **Data for every represented square class**: complement forms $Q'_c$ in $k$ variables and adelic sphere data for
$\rho_c$ = `Quotient.out c`. Fields: `Q'`, `hQ'`, `data`. -/
structure AdelicSphereFamily (Q₀ : QuadForm (𝓞 F) (k + 1)) where
  /-- The complement forms. -/
  Q' : RepClasses Q₀ → QuadForm (𝓞 F) k
  /-- They are nondegenerate. -/
  hQ' : ∀ c, (Q' c).Nondegenerate
  /-- The sphere data. -/
  data : ∀ c, AdelicSphereData Q₀ (repρ c) (Q' c)

/-- **Weil's fibration for every represented square class** (**input**, `AdelicSphereFibration` for each class). -/
@[kb "weil1982" "Lemma 2.4.1, Thm 2.4.3 [unverified page]; §4.5, p. 109 (fibration over T(ρ))"]
structure AdelicSphereFamily.Fibration {Q₀ : QuadForm (𝓞 F) (k + 1)} (hQ : Q₀.Nondegenerate)
    (S : AdelicSphereFamily Q₀) : Prop where
  /-- The fibration for each class. -/
  fib : ∀ c, AdelicSphereFibration Q₀ hQ (S.hQ' c) (S.data c)

/-- The covolume of the stabilizer $SO(Q'_c)(F)$ in $SO(Q'_c)(\mathbb A)$ (a priori in $[0,\infty]$). -/
def AdelicSphereFamily.covol {Q₀ : QuadForm (𝓞 F) (k + 1)} (S : AdelicSphereFamily Q₀) (c : RepClasses Q₀) : ℝ≥0∞ :=
  covolume (GammaSOAdele (S.Q' c)) (SOAdele (S.Q' c)) (muTam (S.Q' c) (S.hQ' c) 1)

/-- **The adelic spherical unfolding with exact constants** (Weil 1982, §4.5, p. 109, Step 1; the lattice
analogue): for a nondegenerate $Q_0$ in $m = k + 1\ge2$ variables over a number field $F$
(any signature), measurable $\Phi\ge0$ and every real $s$,
$$Z^+(s) = \sum_{c}\frac{\operatorname{covol}(SO(Q'_c)(F)\backslash SO(Q'_c)(\mathbb A))}{2}\,Z(s,c)$$
in $[0,\infty]$, with **no hypothesis on $\operatorname{vol}(SO(V)(F)\backslash SO(V)(\mathbb A))$**. Input: Weil's adelic
fibration over each sphere (`AdelicSphereFamily.Fibration`). -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) = Σ_ρ (τ(G'_ρ)/2)Z(s,ρ) before τ(G'_ρ) = 2 is used)"]
theorem adelicZetaPlus_eq_tsum_covolume (hk : 1 ≤ k) (S : AdelicSphereFamily Q₀) (hS : S.Fibration hQ)
    {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ) :
    adelicZetaPlus Q₀ hQ Φ D DM s = ∑' c, S.covol c / 2 * adelicSphZeta (S.data c) Φ s := by
  rw [adelicZetaPlus_eq_lintegral_inner]
  simp_rw [adelicInner_eq Q₀ hΦ hDM s]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr two_ne_zero),
    lintegral_tsum fun c => ((hS.fib c).measurable_orbitSum (repρ_ne_zero c) hk
      (measurable_mellinPhi hΦ s)).aemeasurable,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun c => ?_
  rw [(hS.fib c).lintegral_unfold (repρ_ne_zero c) hk hD (measurable_mellinPhi hΦ s), adelicSphZeta, AdelicSphereFamily.covol,
    div_eq_mul_inv]
  ring

/-- The inner integral is measurable in $g$ (through the fibration coordinates). -/
theorem AdelicSphereFamily.Fibration.measurable_adelicInner (hk : 1 ≤ k) {S : AdelicSphereFamily Q₀}
    (hS : S.Fibration hQ) {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ) :
    Measurable (adelicInner Q₀ Φ DM s) := by
  rw [show adelicInner Q₀ Φ DM s = fun g => 2⁻¹ * ∑' c : RepClasses Q₀, ∑' η : RatSphere Q₀ (repρ c),
      mellinPhi Φ s (g⁻¹ • diagVec F (Fin (k + 1)) η.1) from funext (adelicInner_eq Q₀ hΦ hDM s)]
  exact measurable_const.mul (Measurable.ennreal_tsum fun c =>
    (hS.fib c).measurable_orbitSum (repρ_ne_zero c) hk (measurable_mellinPhi hΦ s))

/-! ### With the induction hypothesis -/

/-- **The induction hypothesis** (adelic analogue of the lattice route's `AdditiveZeta.ComplementTauTwo`; **input**):
$\tau(SO(Q'_c)) = 2$ for every complement form $Q'_c$ of the family, i.e. `TamagawaNumberTwoAdelic (Q' c)`. It is a
statement about the $(m-1)$-dimensional complements only. Field: `tau_two`. -/
@[kb "weil1982" "§4.5, p. 109 (induction on dim: τ(G'_ρ) = 2)"]
structure AdelicComplementTauTwo {Q₀ : QuadForm (𝓞 F) (k + 1)} (S : AdelicSphereFamily Q₀) : Prop where
  /-- $\tau(SO(Q'_c)) = 2$ for every class. -/
  tau_two : ∀ c, TamagawaNumberTwoAdelic (S.Q' c) (S.hQ' c)

/-- **$Z^+(s) = \sum_cZ(s,c)$** given the induction hypothesis (Weil 1982, §4.5, p. 109: "$Z^+(s) = Z(s)$"). -/
@[kb "weil1982" "§4.5, p. 109 (Z⁺(s) = Σ_ρ Z(s,ρ) under τ(G'_ρ) = 2)"]
theorem adelicZetaPlus_eq_tsum_of_complementTauTwo (hk : 1 ≤ k) (S : AdelicSphereFamily Q₀) (hS : S.Fibration hQ)
    (hτ : AdelicComplementTauTwo S)
    {Φ : AdeleSpace F (Fin (k + 1)) → ℝ≥0∞} (hΦ : Measurable Φ)
    {D : Set (SOAdele Q₀)} (hD : IsFundamentalDomain (GammaSOAdele Q₀) D (muTam Q₀ hQ 1))
    {DM : Set (Adeles F)ˣ} (hDM : IsFundamentalDomain (diagUnitsSub F) DM (tamIdeles F)) (s : ℝ) :
    adelicZetaPlus Q₀ hQ Φ D DM s = ∑' c, adelicSphZeta (S.data c) Φ s := by
  rw [adelicZetaPlus_eq_tsum_covolume hk S hS hΦ hD hDM s]
  refine tsum_congr fun c => ?_
  have h2 : S.covol c = 2 := hτ.tau_two c
  rw [h2, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end QuadFormsKB.Tamagawa.Measure.Weil
