/-
# The global count of representations for frames of corank one

**Layer:** number fields, adeles. $F$ any number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + 1$ variables
(any signature), $L = \mathcal O_F^N$, $T_0$ nondegenerate over $\mathcal O_F$ of rank $r$, $\Xi$ a rational frame of $T_0$
($Q_0\circ\Xi = T_0$). Since $n' = N - r = 1$, the stabilizer of every frame of $T_0$ in $SO(V)$ is $SO_1 = 1$ (at every
place; `eq_one_of_smul_ratAT`, `eq_one_of_smul_ratFT`), so Siegel's measure of the representations of $T_0$ by a class
$M_i$ is a multiple of the **number of classes of representations modulo units**
$$n(M_i, T_0) = \#\bigl(\Gamma_i\backslash R(M_i, T_0)\bigr),\qquad R(M_i,T_0) = \{X\in M_i^r : Q\circ X = T_0\}$$
(`repCount`, in $[0,\infty]$; $\Gamma_i = SO(M_i)$ the unit group, possibly infinite).

**Proves**
* `archFibTriv`: the archimedean fibration with trivial stabilizers (stabilizer measures $\delta_1$, constant $1$, measure
  $\mu_\infty$ on $T = SO(V)(F_\infty)$, $\tau(x) = x^{-1}\Xi_\infty$), and `repMeasureT_archFibTriv`: its measure of
  representations is `repCount`;
* **`tsum_repCount_eq`**: $\sum_in(M_i,T_0)$ is the number of $SO(\hat L)$-orbits of integral finite-adelic frames in
  $SO(V)(\mathbb A_f)\,\Xi_f$ (`FinOrbit`). *Proof:* the theta integral over a fundamental domain of $SO(V)(F)$ for
  $\mu_\infty\times\mu^1_f$ ($\mu^1_f(SO(\hat L)) = 1$) computed classically (`lintegral_theta_eq`) and adelically
  (`lintegral_sphere_unfold` with trivial stabilizer, then Tonelli and
  $\{b : b^{-1}\Xi_f\in\hat L^r\} = \bigsqcup_Og_O^{-1}SO(\hat L)$). No Tamagawa number is used.
-/
import QuadFormsKB.Tamagawa.Indefinite.CorankOneTower

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames

variable {F : Type} [Field F] [NumberField F] {r : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Trivial groups -/

/-- The covolume of a subgroup of a trivial group is the total mass. -/
theorem covolume_of_subsingleton {G : Type*} [Group G] [MeasurableSpace G] [Subsingleton G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) : covolume Γ G μ = μ univ := by
  have hs : ∀ (c : Γ) (x : G), c • x = x := fun c x => Subsingleton.elim _ _
  have hm : MeasurableConstSMul Γ G :=
    ⟨fun c => by
      have : (fun x : G => c • x) = id := funext (hs c)
      rw [this]; exact measurable_id⟩
  have hi : SMulInvariantMeasure Γ G μ :=
    ⟨fun c s _ => by
      have : (fun x : G => c • x) = id := funext (hs c)
      rw [this]; rfl⟩
  have hG : Subsingleton Γ := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hfd : IsFundamentalDomain Γ (univ : Set G) μ :=
    ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun x => ⟨1, mem_univ _⟩,
      fun g h hgh => absurd (hG.elim g h) hgh⟩
  exact hfd.covolume_eq_volume μ

/-- On a trivial group the Dirac measure is left invariant. -/
theorem isMulLeftInvariant_dirac_of_subsingleton {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Subsingleton G] : (Measure.dirac (1 : G)).IsMulLeftInvariant :=
  ⟨fun g => by
    rw [Subsingleton.elim g 1]
    have : (fun x : G => 1 * x) = id := funext fun x => one_mul x
    rw [this, Measure.map_id]⟩

/-! ### The finite Haar measure with $\mu(SO(\hat L)) = 1$ -/

section MuFinK

variable {N : ℕ} (Q₀ : QuadForm (𝓞 F) N)

/-- The Haar measure $\mu^1_f$ on $SO(V)(\mathbb A_f)$ with $\mu^1_f(SO(\hat L)) = 1$ (any dimension). -/
def muFinK : Measure (SOAf Q₀) := haarNorm (KSO Q₀) (isCompact_KSO Q₀) (isOpen_KSO Q₀) 1

instance : (muFinK Q₀).IsMulLeftInvariant := by unfold muFinK; infer_instance

theorem muFinK_KSO : muFinK Q₀ (KSO Q₀ : Set (SOAf Q₀)) = 1 := by
  rw [muFinK, haarNorm_self]; rfl

instance sigmaFinite_muFinK : SigmaFinite (muFinK Q₀) := by
  have := countable_SOAf_quot Q₀
  refine Measure.sigmaFinite_of_countable (S := Set.range fun q : SOAf Q₀ ⧸ KSO Q₀ =>
      (Quotient.out q : SOAf Q₀) • (KSO Q₀ : Set (SOAf Q₀))) (Set.countable_range _) ?_ ?_
  · rintro _ ⟨q, rfl⟩
    rw [measure_smul, muFinK_KSO]; exact ENNReal.one_lt_top
  · refine Set.eq_univ_of_forall fun g => ?_
    refine Set.mem_sUnion.mpr ⟨_, ⟨(QuotientGroup.mk g : SOAf Q₀ ⧸ KSO Q₀), rfl⟩, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KSO Q₀) g
    refine Set.mem_smul_set.mpr ⟨(k : SOAf Q₀)⁻¹, (KSO Q₀).inv_mem k.2, ?_⟩
    rw [smul_eq_mul, hk, mul_inv_cancel_right]

end MuFinK

variable (Q₀ : QuadForm (𝓞 F) (r + 1)) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
  (Ξ : RatFrame Q₀ T₀)

/-! ### The number of classes of representations -/

/-- **The number of classes of representations of $T_0$ by the class $i$ modulo units**:
$n(M_i, T_0) = \#(\Gamma_i\backslash R(M_i, T_0))\in[0,\infty]$, $R(M_i,T_0) = \{X\in M_i^r : Q\circ X = T_0\}$ (`repsT`),
$\Gamma_i$ = `unitGroup Q₀ i`. Parameters: `Q₀`, `T₀`, `i`. -/
def repCount {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (i : DC Q₀) : ℝ≥0∞ :=
  ∑' _q : orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ T₀ i), (1 : ℝ≥0∞)

/-! ### The archimedean fibration with trivial stabilizers -/

/-- The archimedean orbit of $\Xi_\infty$. -/
abbrev orbInf : Set (Fin r → VInf F (r + 1)) := Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ

include hT in
theorem subsingleton_stabilizer_orbInf {y : Fin r → VInf F (r + 1)} (hy : y ∈ orbInf Q₀ T₀ Ξ) :
    Subsingleton (stabilizer (GInfSO Q₀) y) := by
  obtain ⟨a, rfl⟩ := hy
  refine ⟨fun s t => Subtype.ext ?_⟩
  have key : ∀ s : stabilizer (GInfSO Q₀) (a • ratAT Q₀ T₀ Ξ), (s : GInfSO Q₀) = 1 := by
    intro s
    have hs : (s : GInfSO Q₀) • a • ratAT Q₀ T₀ Ξ = a • ratAT Q₀ T₀ Ξ := s.2
    have h1 : (a⁻¹ * s * a) • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
      rw [mul_smul, mul_smul, hs, inv_smul_smul]
    have h2 := eq_one_of_smul_ratAT Q₀ T₀ hT Ξ h1
    have : (s : GInfSO Q₀) = a * (a⁻¹ * s * a) * a⁻¹ := by group
    rw [this, h2]; group
  rw [key s, key t]

/-- The orbit coordinates at $y = a_y\Xi_\infty$: $(x, h)\mapsto a_yx$. -/
def archCoordTriv (y : Fin r → VInf F (r + 1)) (hy : y ∈ orbInf Q₀ T₀ Ξ) :
    OrbitCoord (stabilizer (GInfSO Q₀) y).subtype (fun x : GInfSO Q₀ => x⁻¹ • ratAT Q₀ T₀ Ξ) y :=
  haveI := subsingleton_stabilizer_orbInf Q₀ T₀ hT Ξ hy
  { coord := (prodSubsingletonEquiv _ _ 1).trans (MeasurableEquiv.mulLeft hy.choose)
    mul := fun x h h' => by
      have : h' = 1 := Subsingleton.elim _ _
      subst this
      simp
    orbit := fun x h => by
      show (hy.choose * x)⁻¹ • y = x⁻¹ • ratAT Q₀ T₀ Ξ
      have e : hy.choose • ratAT Q₀ T₀ Ξ = y := hy.choose_spec
      calc (hy.choose * x)⁻¹ • y = (hy.choose * x)⁻¹ • hy.choose • ratAT Q₀ T₀ Ξ := by rw [e]
        _ = x⁻¹ • ratAT Q₀ T₀ Ξ := by rw [_root_.mul_inv_rev, mul_smul, inv_smul_smul] }

open Classical in
/-- **The archimedean fibration with trivial stabilizers** over the orbit of $\Xi_\infty$: $T = SO(V)(F_\infty)$ with
$\mu_\infty$, $\tau(x) = x^{-1}\Xi_\infty$, stabilizer measures $\delta_1$, constant $1$. -/
def archFibTriv :
    ArchFibration (muArchTamSO Q₀ hQ) (orbInf Q₀ T₀ Ξ) (muArchTamSO Q₀ hQ)
      (fun x : GInfSO Q₀ => x⁻¹ • ratAT Q₀ T₀ Ξ) 1 where
  μH y := if y ∈ orbInf Q₀ T₀ Ξ then Measure.dirac 1 else 0
  coord y hy := archCoordTriv Q₀ T₀ hT Ξ y hy
  sigmaFinite y := by
    split_ifs <;> infer_instance
  leftInv y := by
    split_ifs with hy
    · haveI := subsingleton_stabilizer_orbInf Q₀ T₀ hT Ξ hy
      exact isMulLeftInvariant_dirac_of_subsingleton
    · exact ⟨fun g => by simp⟩
  fib y hy := by
    rw [if_pos hy, one_smul, Measure.prod_dirac, Measure.map_map (archCoordTriv Q₀ T₀ hT Ξ y hy).coord.measurable
      measurable_prodMk_right]
    have : ((archCoordTriv Q₀ T₀ hT Ξ y hy).coord ∘ fun x : GInfSO Q₀ => (x, (1 : stabilizer (GInfSO Q₀) y))) =
        fun x => hy.choose * x := rfl
    rw [this, map_mul_left_eq_self]

include hQ hT in
/-- Every representation of $T_0$ lies in the archimedean orbit of $\Xi_\infty$ (Witt). -/
theorem ratAT_mem_orbInf (X : RatFrame Q₀ T₀) : ratAT Q₀ T₀ X ∈ orbInf Q₀ T₀ Ξ := by
  obtain ⟨γ, rfl⟩ := exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ (towerCorankOne Q₀ hQ T₀ hT Ξ) hT le_rfl X
  exact ⟨(γ : SOAdele Q₀).1, (ratAT_smul Q₀ T₀ γ Ξ).symm⟩

/-- **With trivial stabilizers the measure of representations is the count**: `repMeasureT` for `archFibTriv` is
$n(M_i,T_0)$. -/
theorem repMeasureT_archFibTriv (i : DC Q₀) :
    repMeasureT Q₀ T₀ hQ (archFibTriv Q₀ hQ T₀ hT Ξ) i = repCount Q₀ T₀ i := by
  classical
  unfold repMeasureT repMeasureOf repCount
  refine tsum_congr fun q => ?_
  set y := ((q.out : repsT Q₀ T₀ i) : Fin r → VInf F (r + 1)) with hydef
  have hy : y ∈ orbInf Q₀ T₀ Ξ := by
    obtain ⟨X, -, hX⟩ := (q.out : repsT Q₀ T₀ i).2
    rw [hydef, ← hX]
    exact ratAT_mem_orbInf Q₀ hQ T₀ hT Ξ X
  haveI := subsingleton_stabilizer_orbInf Q₀ T₀ hT Ξ hy
  haveI : Countable (stabArith (unitGroup Q₀ i) y) := by
    haveI : Subsingleton (stabArith (unitGroup Q₀ i) y) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance
  rw [covolume_of_subsingleton]
  show (if y ∈ orbInf Q₀ T₀ Ξ then Measure.dirac 1 else 0) univ = 1
  rw [if_pos hy, Measure.dirac_apply_of_mem (mem_univ _)]

/-! ### The adelic side -/

/-- The adelic orbit coordinates with trivial stabilizer: $T = SO(V)(\mathbb A)$, $\tau(x) = x^{-1}\Xi$. -/
def adelicCoordTriv :
    OrbitCoord (1 : Unit →* SOAdele Q₀) (fun x : SOAdele Q₀ => x⁻¹ • ratFrameA Q₀ T₀ Ξ) (ratFrameA Q₀ T₀ Ξ) where
  coord := prodSubsingletonEquiv _ _ ()
  mul x h h' := by
    show x = (1 : Unit →* SOAdele Q₀) h' * x
    rw [MonoidHom.one_apply, one_mul]
  orbit _ _ := rfl

/-- The test function along $x\mapsto x^{-1}\Xi$ splits into archimedean and finite parts. -/
theorem testFnT_inv_smul (Φ : (Fin r → VInf F (r + 1)) → ℝ≥0∞) (x : SOAdele Q₀) :
    testFnT Φ (x⁻¹ • ratFrameA Q₀ T₀ Ξ) =
      Φ (x.1⁻¹ • ratAT Q₀ T₀ Ξ) * (latHatT F (r + 1) r).indicator 1 (x.2⁻¹ • ratFT Q₀ T₀ Ξ) := by
  rw [testFnT, splitFrame_smul]
  rfl

theorem measurable_latSet :
    MeasurableSet {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r} :=
  (red_isOpen_latSet Q₀ (ratFT Q₀ T₀ Ξ)).measurableSet

theorem indicator_latSet_eq :
    (fun b : SOAf Q₀ => (latHatT F (r + 1) r).indicator (1 : (Fin r → Fin (r + 1) → AF) → ℝ≥0∞) (b⁻¹ • ratFT Q₀ T₀ Ξ)) =
      {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r}.indicator 1 := by
  funext b; rfl

set_option maxHeartbeats 800000 in
include hT in
/-- **The theta integral with trivial stabilizers, adelically**: for every left-invariant $\mu_f$ and every fundamental
domain $E$ of $SO(V)(F)$ for $\mu_\infty\times\mu_f$,
$$\int_E\theta = \int\Phi(a^{-1}\Xi_\infty)\,d\mu_\infty(a)\cdot\mu_f\{b : b^{-1}\Xi_f\in\hat L^r\}.$$ -/
theorem lintegral_theta_triv {μB : Measure (SOAf Q₀)} [SFinite μB] [μB.IsMulLeftInvariant]
    {Φ : (Fin r → VInf F (r + 1)) → ℝ≥0∞} (hΦ : Measurable Φ) {E : Set (SOAdele Q₀)}
    (hE : IsFundamentalDomain (GammaSOAdele Q₀) E ((muArchTamSO Q₀ hQ).prod μB)) :
    ∫⁻ g in E, thetaFn (ratAT Q₀ T₀) (ratFT Q₀ T₀) Φ (latHatT F (r + 1) r) g ∂(muArchTamSO Q₀ hQ).prod μB =
      (∫⁻ a, Φ (a⁻¹ • ratAT Q₀ T₀ Ξ) ∂muArchTamSO Q₀ hQ) *
        μB {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r} := by
  have := countable_GammaSOAdele Q₀
  haveI : MeasurableConstSMul (⊤ : Subgroup Unit) Unit := ⟨fun _ => Subsingleton.measurable⟩
  haveI : SMulInvariantMeasure (⊤ : Subgroup Unit) Unit (Measure.dirac ()) :=
    ⟨fun c s _ => by
      have : (fun x : Unit => c • x) = id := funext fun _ => Subsingleton.elim _ _
      rw [this]; rfl⟩
  set μ := (muArchTamSO Q₀ hQ).prod μB with hμ
  have hιΓ : ∀ h ∈ (⊤ : Subgroup Unit), (1 : Unit →* SOAdele Q₀) h ∈ GammaSOAdele Q₀ := fun h _ => by
    rw [MonoidHom.one_apply]; exact one_mem _
  have hfix : ∀ (h : Unit) (hh : h ∈ (⊤ : Subgroup Unit)),
      (⟨(1 : Unit →* SOAdele Q₀) h, hιΓ h hh⟩ : GammaSOAdele Q₀) • Ξ = Ξ := by
    intro h hh
    have e : (⟨(1 : Unit →* SOAdele Q₀) h, hιΓ h hh⟩ : GammaSOAdele Q₀) = 1 :=
      Subtype.ext rfl
    rw [e, one_smul]
  have hstab : ∀ γ : GammaSOAdele Q₀, γ • Ξ = Ξ → ∃ h ∈ (⊤ : Subgroup Unit), (1 : Unit →* SOAdele Q₀) h = γ := by
    intro γ hγ
    have h1 : (γ : SOAdele Q₀) • ratFrameA Q₀ T₀ Ξ = ratFrameA Q₀ T₀ Ξ := by rw [← ratFrameA_smul, hγ]
    exact ⟨(), trivial, by rw [MonoidHom.one_apply, eq_one_of_smul_ratFrameA Q₀ T₀ hT Ξ h1]⟩
  have hDHx : ∀ h : Unit, ∃! γ : (⊤ : Subgroup Unit), γ • h ∈ (univ : Set Unit) :=
    fun h => ⟨1, mem_univ _, fun γ _ => Subtype.ext (Subsingleton.elim _ _)⟩
  have hfib : μ = (1 : ℝ≥0∞) • (μ.prod (Measure.dirac ())).map (adelicCoordTriv Q₀ T₀ Ξ).coord := by
    rw [one_smul, Measure.prod_dirac, Measure.map_map (adelicCoordTriv Q₀ T₀ Ξ).coord.measurable
      measurable_prodMk_right]
    exact (Measure.map_id).symm
  have hmeas : Measurable fun x : SOAdele Q₀ => testFnT Φ (x⁻¹ • ratFrameA Q₀ T₀ Ξ) := by
    simp_rw [testFnT_inv_smul]
    refine Measurable.mul ((measurable_GInf_inv_smulT Q₀ hΦ _).comp measurable_fst) ?_
    have : (fun x : SOAdele Q₀ => (latHatT F (r + 1) r).indicator (1 : (Fin r → Fin (r + 1) → AF) → ℝ≥0∞) (x.2⁻¹ • ratFT Q₀ T₀ Ξ)) =
        fun x => {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r}.indicator 1 x.2 := by
      funext x; rfl
    rw [this]
    exact (measurable_one.indicator (measurable_latSet Q₀ T₀ Ξ)).comp measurable_snd
  have key := lintegral_sphere_unfold (Γ := GammaSOAdele Q₀) (μ := μ) (ΓH := (⊤ : Subgroup Unit))
    (μH := Measure.dirac ()) (fun η : RatFrame Q₀ T₀ => ratFrameA Q₀ T₀ η) (fun γ η => ratFrameA_smul Q₀ T₀ γ η) Ξ
    (fun η => exists_smul_eq_ratFrame Q₀ hQ T₀ Ξ (towerCorankOne Q₀ hQ T₀ hT Ξ) hT le_rfl η)
    (1 : Unit →* SOAdele Q₀) μ (fun x => x⁻¹ • ratFrameA Q₀ T₀ Ξ) (adelicCoordTriv Q₀ T₀ Ξ) hιΓ hfix hstab
    (DH := univ) MeasurableSet.univ hDHx 1 hfib hE (testFnT Φ) hmeas
  rw [covolume_of_subsingleton, measure_univ, one_mul, one_mul] at key
  have hθ : ∀ g : SOAdele Q₀, thetaFn (ratAT Q₀ T₀) (ratFT Q₀ T₀) Φ (latHatT F (r + 1) r) g =
      ∑' η : RatFrame Q₀ T₀, testFnT Φ (g⁻¹ • ratFrameA Q₀ T₀ η) := fun g => by
    unfold thetaFn
    refine tsum_congr fun η => ?_
    rw [testFnT, splitFrame_smul]
    rfl
  simp_rw [hθ]
  rw [key]
  simp_rw [testFnT_inv_smul]
  have hf : AEMeasurable (fun a : GInfSO Q₀ => Φ (a⁻¹ • ratAT Q₀ T₀ Ξ)) (muArchTamSO Q₀ hQ) :=
    (measurable_GInf_inv_smulT Q₀ hΦ _).aemeasurable
  have hg : AEMeasurable (fun b : SOAf Q₀ => (latHatT F (r + 1) r).indicator (1 : (Fin r → Fin (r + 1) → AF) → ℝ≥0∞) (b⁻¹ • ratFT Q₀ T₀ Ξ))
      μB := by
    rw [indicator_latSet_eq]
    exact (measurable_one.indicator (measurable_latSet Q₀ T₀ Ξ)).aemeasurable
  rw [hμ, lintegral_prod_mul hf hg, indicator_latSet_eq, lintegral_indicator_one (measurable_latSet Q₀ T₀ Ξ)]

include hT in
/-- **The integral finite-adelic frames are a disjoint union of translates of $SO(\hat L)$**:
$\mu_f\{b : b^{-1}\Xi_f\in\hat L^r\} = \#\mathrm{FinOrbit}\cdot\mu_f(SO(\hat L))$ (trivial stabilizer of $\Xi_f$). -/
theorem measure_latSet_eq (μB : Measure (SOAf Q₀)) [μB.IsMulLeftInvariant] :
    μB {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r} =
      (∑' _O : FinOrbit Q₀ T₀ Ξ, (1 : ℝ≥0∞)) * μB (KSO Q₀ : Set (SOAf Q₀)) := by
  set S : FinOrbit Q₀ T₀ Ξ → Set (SOAf Q₀) := fun O => {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈
    (KSO Q₀ : Set (SOAf Q₀)) • ({finOrbitRep Q₀ T₀ Ξ O • ratFT Q₀ T₀ Ξ} : Set (Fin r → Fin (r + 1) → AF))} with hS
  have hU : {b : SOAf Q₀ | b⁻¹ • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r} = ⋃ O, S O := by
    ext b
    simp only [mem_setOf_eq, mem_iUnion, hS]
    constructor
    · intro h
      refine ⟨Quotient.mk (finOrbitSetoid Q₀ T₀ Ξ) ⟨b⁻¹, h⟩, ?_⟩
      exact Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ)
        (⟨b⁻¹, h⟩ : {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + 1) r})
    · rintro ⟨O, k, hk, y, hy, hz⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [← hz]
      exact (latHatT_stable Q₀ k hk _).2 (orb_rep_mem Q₀ T₀ Ξ O)
  have hdisj : Pairwise (Function.onFun Disjoint S) := fun i j hij =>
    (orb_disjoint Q₀ T₀ Ξ hij).preimage (fun b : SOAf Q₀ => b⁻¹ • ratFT Q₀ T₀ Ξ)
  have hmeas : ∀ O, MeasurableSet (S O) := fun O =>
    (orb_isOpen_orbitSet Q₀ (ratFT Q₀ T₀ Ξ) (finOrbitRep Q₀ T₀ Ξ O • ratFT Q₀ T₀ Ξ)).measurableSet
  have hSO : ∀ O, S O = (finOrbitRep Q₀ T₀ Ξ O)⁻¹ • (KSO Q₀ : Set (SOAf Q₀)) := by
    intro O
    set g := finOrbitRep Q₀ T₀ Ξ O
    ext b
    simp only [hS, mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, y, hy, hz⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : (b * k * g) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
        have hz' : k • g • ratFT Q₀ T₀ Ξ = b⁻¹ • ratFT Q₀ T₀ Ξ := hz
        rw [mul_smul, mul_smul, hz', smul_inv_smul]
      have h2 := eq_one_of_smul_ratFT Q₀ T₀ hT Ξ h1
      refine Set.mem_smul_set.2 ⟨k⁻¹, (KSO Q₀).inv_mem hk, ?_⟩
      show g⁻¹ * k⁻¹ = b
      have : b = (b * k * g) * g⁻¹ * k⁻¹ := by group
      rw [this, h2]; group
    · intro hb
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hb
      refine ⟨k⁻¹, (KSO Q₀).inv_mem hk, g • ratFT Q₀ T₀ Ξ, rfl, ?_⟩
      show k⁻¹ • g • ratFT Q₀ T₀ Ξ = (g⁻¹ * k)⁻¹ • ratFT Q₀ T₀ Ξ
      rw [_root_.mul_inv_rev, inv_inv, mul_smul]
  rw [hU, measure_iUnion hdisj hmeas, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun O => ?_
  rw [hSO, measure_smul, one_mul]

include hQ hT in
/-- **The global count** (corank one): the number of classes of representations of $T_0$ over the genus of $L$ is the
number of $SO(\hat L)$-orbits of integral finite-adelic frames in $SO(V)(\mathbb A_f)\,\Xi_f$:
$$\sum_in(M_i, T_0) = \#\mathrm{FinOrbit}.$$ -/
theorem tsum_repCount_eq :
    ∑' i, repCount Q₀ T₀ i = ∑' _O : FinOrbit Q₀ T₀ Ξ, (1 : ℝ≥0∞) := by
  classical
  have := countable_GammaSOAdele Q₀
  have := discreteTopology_GammaSOAdele Q₀
  obtain ⟨E, hE⟩ := exists_measurableSet_forall_existsUnique_smul_mem (GammaSOAdele Q₀)
  have hEf : IsFundamentalDomain (GammaSOAdele Q₀) E ((muArchTamSO Q₀ hQ).prod (muFinK Q₀)) :=
    IsFundamentalDomain.mk' hE.1.nullMeasurableSet hE.2
  -- a compact neighbourhood of `1` and the test function
  haveI : (muArchTamSO Q₀ hQ).IsHaarMeasure := by
    have := LerayArch.isHaarMeasure_muArchLeray (QRe Q₀) (QCx Q₀) (gramDetR_QRe_ne_zero Q₀ hQ)
      (gramDetC_QCx_ne_zero Q₀ hQ)
    unfold muArchTamSO LerayArch.muArchNF
    rw [ofReal_smul_eq]
    exact Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr
      (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _) cxWeil_pos)).ne'
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : GInfSO Q₀)
  have hU0 : muArchTamSO Q₀ hQ U ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hU1).ne'
  have hUt : muArchTamSO Q₀ hQ U ≠ ⊤ := hUc.measure_lt_top.ne
  set orbMap : GInfSO Q₀ → Fin r → VInf F (r + 1) := fun a => a⁻¹ • ratAT Q₀ T₀ Ξ with horbMap
  have hcont : Continuous orbMap :=
    (continuous_GInf_smulT Q₀).comp (continuous_inv.prodMk continuous_const)
  haveI : OpensMeasurableSpace (Fin r → VInf F (r + 1)) := Pi.opensMeasurableSpace
  have hSm : MeasurableSet (orbMap '' U) := (hUc.image hcont).isClosed.measurableSet
  set Φ : (Fin r → VInf F (r + 1)) → ℝ≥0∞ := (orbMap '' U).indicator 1 with hΦdef
  have hΦ : Measurable Φ := measurable_one.indicator hSm
  have hΦU : ∀ a, Φ (orbMap a) = U.indicator 1 a := by
    intro a
    by_cases ha : a ∈ U
    · rw [Set.indicator_of_mem ha, hΦdef, Set.indicator_of_mem (Set.mem_image_of_mem _ ha)]; rfl
    · rw [Set.indicator_of_notMem ha, hΦdef, Set.indicator_of_notMem]
      rintro ⟨u, hu, hua⟩
      have h1 : (u * a⁻¹) • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ := by
        have : u⁻¹ • ratAT Q₀ T₀ Ξ = a⁻¹ • ratAT Q₀ T₀ Ξ := hua
        rw [mul_smul, ← this, smul_inv_smul]
      have h2 := eq_one_of_smul_ratAT Q₀ T₀ hT Ξ h1
      have : u = a := by
        have := congrArg (· * a) h2
        simpa using this
      exact ha (this ▸ hu)
  have hI : ∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ = muArchTamSO Q₀ hQ U := by
    simp_rw [hΦU]
    exact lintegral_indicator_one hUc.measurableSet
  -- the two computations
  have h1 := lintegral_theta_eq (Γ := GammaSOAdele Q₀) (KSO Q₀) (isOpen_KSO Q₀).measurableSet (dcRep Q₀)
    (dcRep_cov Q₀) (fun i j γ hγ k hk k' hk' h => dcRep_disj Q₀ i j γ hγ k hk k' hk' h)
    (fun i γ hγ h1 => GammaSOAdele_injA Q₀ γ hγ.1 h1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.1)
    (fun i => (exists_fd_levelGroup Q₀ (dcRep Q₀ i)).choose_spec.2)
    (muArchTamSO Q₀ hQ) (muFinK Q₀) (ratAT_smul Q₀ T₀) (ratFT_smul Q₀ T₀) (ratAT_injective Q₀ T₀)
    (latHatT_stable Q₀) (archFibTriv Q₀ hQ T₀ hT Ξ) (ratAT_mem_orbInf Q₀ hQ T₀ hT Ξ)
    (fun i y => exists_fd_stabArithT Q₀ (dcRep Q₀ i) y) Φ
    (measurable_GInf_inv_smulT Q₀ hΦ) (measurable_GInf_inv_smulT Q₀ hΦ _) hEf
  have h2 := lintegral_theta_triv Q₀ hQ T₀ hT Ξ hΦ hEf
  rw [measure_latSet_eq Q₀ T₀ hT Ξ, muFinK_KSO, mul_one] at h2
  rw [h2, muFinK_KSO] at h1
  simp only [one_mul, mul_one] at h1
  have hsum : (∑' i, repMeasureOf (levelGroup (GammaSOAdele Q₀) (KSO Q₀) (dcRep Q₀ i))
      (repSet (ratAT_smul Q₀ T₀) (ratFT_smul Q₀ T₀) (latHatT_stable Q₀) (dcRep Q₀ i))
      (archFibTriv Q₀ hQ T₀ hT Ξ).μH) = ∑' i, repCount Q₀ T₀ i :=
    tsum_congr fun i => repMeasureT_archFibTriv Q₀ hQ T₀ hT Ξ i
  rw [hsum] at h1
  change (∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ) * _ = _ * ∫⁻ a, Φ (orbMap a) ∂muArchTamSO Q₀ hQ at h1
  rw [hI, mul_comm] at h1
  exact ((ENNReal.mul_left_inj hU0 hUt).mp h1).symm

end QuadFormsKB.Tamagawa.Indefinite
