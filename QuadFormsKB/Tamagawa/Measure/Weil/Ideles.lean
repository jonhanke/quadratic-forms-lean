import QuadFormsKB.Tamagawa.Measure.Weil.GLScaling
import QuadFormsKB.Tamagawa.Measure.Weil.FundamentalDomain

/-!
# The idele group $\mathbb A_F^\times$ ($A = F$)

The multiplicative layer for $A = F$ ($F$ any number field), with $\mathbb A_F^\times$ = `(Adeles F)ˣ` (the units of the
adele ring with the units topology, $x\mapsto(x, x^{-1})$):

* topology: $\hat{\mathcal O}^\times$ (`OHatUnits`) is a compact open subgroup of $\mathbb A_f^\times$; $\mathbb A_f^\times$,
  $F_\infty^\times$ and $\mathbb A_F^\times$ are locally compact and second countable (Borel measurable spaces);
* **`discreteTopology_diagUnitsSub`**: $F^\times$ (`diagUnitsSub`) is discrete in $\mathbb A_F^\times$;
* **`ideleNorm_diagUnits`** (product formula, Weil's measure-theoretic proof): $\|\xi\|_{\mathbb A} = 1$ for $\xi\in F^\times$,
  because multiplication by $\xi$ maps a fundamental domain of $F$ in $\mathbb A_F$ to another one, and multiplies the
  measure by $\|\xi\|_{\mathbb A}$;
* **`continuous_ideleNorm`**: the idele norm is a continuous homomorphism `ideleNormHom`; $\mathbb A_F^1$ = `ideleOne`
  is a closed subgroup containing $F^\times$; `normSection t` has norm $t$ (all archimedean components $t^{1/[F:\mathbb Q]}$),
  so $\mathbb A_F^\times = \mathbb A_F^1\cdot\operatorname{normSection}(\mathbb R_{>0})$ (`mul_normSection_inv_mem_ideleOne`);
* **`exists_isFundamentalDomain_ideles`**, **`exists_isFundamentalDomain_ideleOne`**: measurable fundamental domains for
  $F^\times$ in $\mathbb A_F^\times$ and in $\mathbb A_F^1$;
* local measures: `unitsV v` $=\mathcal O_v^\times$, **`selfDualV_unitsV`**: $\operatorname{vol}(\mathcal O_v^\times) =
  (1 - N(v)^{-1})\operatorname{vol}(\mathcal O_v)$, so with Weil's convergence factor $\lambda_v = 1 - N(v)^{-1}$ (the convention $\lambda_v^{-1}\omega_v$, $\omega_v = |x|_v^{-1}dx_v$, which is $dx_v$ on $\mathcal O_v^\times$):
  $\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v)$ (`lamV_inv_mul_selfDualV_unitsV`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology RestrictedProduct NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Topology on $\mathbb A_f^\times$, $F_\infty^\times$, $\mathbb A_F^\times$ -/

instance : T2Space AF :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))

instance : SecondCountableTopology AFᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := AF)).symm.isEmbedding.secondCountableTopology

variable (F) in
/-- $\hat{\mathcal O}^\times = \prod_v\mathcal O_v^\times\le\mathbb A_f^\times$. -/
def OHatUnits : Subgroup AFˣ where
  carrier := {u | (u : AF) ∈ OHat ∧ ((u⁻¹ : AFˣ) : AF) ∈ OHat}
  one_mem' := ⟨fun v => one_mem (v.adicCompletionIntegers F), fun v => one_mem (v.adicCompletionIntegers F)⟩
  mul_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    refine ⟨fun v => mul_mem (hu v) (hw v), fun v => ?_⟩
    rw [mul_inv_rev]
    exact mul_mem (hw' v) (hu' v)
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨hu', by rw [inv_inv]; exact hu⟩

theorem mem_OHatUnits {u : AFˣ} :
    u ∈ OHatUnits F ↔ (u : AF) ∈ OHat ∧ ((u⁻¹ : AFˣ) : AF) ∈ OHat := Iff.rfl

theorem isOpen_OHatUnits : IsOpen (OHatUnits F : Set AFˣ) :=
  (isOpen_OHat.preimage Units.continuous_val).inter (isOpen_OHat.preimage Units.continuous_coe_inv)

theorem isCompact_OHatUnits : IsCompact (OHatUnits F : Set AFˣ) := by
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hK : IsCompact ((OHat : Set AF) ×ˢ (MulOpposite.op '' (OHat : Set AF))) :=
    isCompact_OHat.prod (isCompact_OHat.image MulOpposite.continuous_op)
  have hC : IsClosed {p : AF × AFᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} :=
    (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
      (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  have hset : Units.embedProduct AF '' (OHatUnits F : Set AFˣ) =
      ((OHat : Set AF) ×ˢ (MulOpposite.op '' (OHat : Set AF))) ∩
        {p : AF × AFᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, ⟨hu, hu'⟩, h⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨hu, ⟨_, hu', rfl⟩⟩, u.mul_inv, u.inv_mul⟩
    · rintro ⟨⟨hx, ⟨y', hy', rfl⟩⟩, h1, h2⟩
      exact ⟨⟨x, y', h1, h2⟩, ⟨hx, hy'⟩, rfl⟩
  rw [hset]
  exact hK.inter_right hC

instance : LocallyCompactSpace AFˣ :=
  isCompact_OHatUnits.locallyCompactSpace_of_mem_nhds_of_group
    (isOpen_OHatUnits.mem_nhds (OHatUnits F).one_mem)

instance : SecondCountableTopology AFˣ := Units.isEmbedding_embedProduct.secondCountableTopology

instance measurableSpace_finUnits : MeasurableSpace AFˣ := borel AFˣ

instance : BorelSpace AFˣ := ⟨rfl⟩

instance : LocallyCompactSpace (mixedSpace F)ˣ := Units.isOpenEmbedding_val.locallyCompactSpace

instance : SecondCountableTopology (mixedSpace F)ˣ :=
  Units.isEmbedding_embedProduct.secondCountableTopology

instance : LocallyCompactSpace (Adeles F)ˣ := Homeomorph.prodUnits.isOpenEmbedding.locallyCompactSpace

instance : SecondCountableTopology (Adeles F)ˣ := Homeomorph.prodUnits.isEmbedding.secondCountableTopology

instance measurableSpace_ideles : MeasurableSpace (Adeles F)ˣ := borel (Adeles F)ˣ

instance : BorelSpace (Adeles F)ˣ := ⟨rfl⟩

/-! ### $F^\times$ in $\mathbb A_F^\times$ -/

variable (F) in
/-- The diagonal ring embedding $F\to\mathbb A_F$ (`diagRing_apply`: it is `diag F`). -/
def diagRing : F →+* Adeles F := (mixedEmbedding F).prod (algebraMap F AF)

theorem diagRing_apply (ξ : F) : diagRing F ξ = diag F ξ := rfl

variable (F) in
/-- $F^\times\to\mathbb A_F^\times$. -/
def diagUnits : Fˣ →* (Adeles F)ˣ := Units.map (diagRing F).toMonoidHom

@[simp] theorem diagUnits_val (ξ : Fˣ) : ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F) = diag F ξ := rfl

variable (F) in
/-- $F^\times\le\mathbb A_F^\times$. -/
def diagUnitsSub : Subgroup (Adeles F)ˣ := (diagUnits F).range

/-- **$F^\times$ is discrete in $\mathbb A_F^\times$.** -/
theorem discreteTopology_diagUnitsSub : DiscreteTopology (diagUnitsSub F) := by
  obtain ⟨U, hU, h0U, hUdiag⟩ := exists_isOpen_diag_mem_iff (F := F)
  set V : Set (Adeles F)ˣ := (fun u : (Adeles F)ˣ => (u : Adeles F) - 1) ⁻¹' U
  have hV : IsOpen V := hU.preimage (Units.continuous_val.sub continuous_const)
  refine discreteTopology_of_isOpen_singleton_one (isOpen_induced_iff.mpr ⟨V, hV, ?_⟩)
  ext ⟨u, hu⟩
  obtain ⟨ξ, rfl⟩ := hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, V]
  constructor
  · intro h
    have h' : diag F ((ξ : F) - 1) ∈ U := by
      rw [← diagRing_apply, map_sub, map_one]; exact h
    have : (ξ : F) = 1 := sub_eq_zero.mp (hUdiag _ h')
    have hξ : ξ = 1 := Units.ext this
    subst hξ
    exact Subtype.ext (map_one _)
  · intro h
    have h1 : diagUnits F ξ = 1 := congrArg Subtype.val h
    change ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F) - 1 ∈ U
    rw [h1, Units.val_one, sub_self]
    exact h0U

instance : DiscreteTopology (diagUnitsSub F) := discreteTopology_diagUnitsSub

instance : Countable (diagUnitsSub F) := by
  have : Countable Fˣ := Function.Injective.countable (f := fun u : Fˣ => (u : F)) Units.val_injective
  exact (diagUnits F).rangeRestrict_surjective.countable

/-! ### The product formula -/

theorem diagUnits_mul_mem (ξ : Fˣ) {γ : Adeles F} (hγ : γ ∈ diagSub F) :
    ((diagUnits F ξ : (Adeles F)ˣ) : Adeles F) * γ ∈ diagSub F := by
  obtain ⟨η, rfl⟩ := hγ
  exact ⟨(ξ : F) * η, by rw [← diagRing_apply, map_mul]; rfl⟩

theorem ideleNorm_inv (g : (Adeles F)ˣ) : ideleNorm F g⁻¹ = (ideleNorm F g)⁻¹ := by
  rw [← distribHaarChar_adeles, ← distribHaarChar_adeles, map_inv, NNReal.coe_inv]

/-- **The product formula** $\|\xi\|_{\mathbb A} = 1$ for $\xi\in F^\times$ (Weil's measure-theoretic proof: $\xi$ maps a
fundamental domain of $F$ in $\mathbb A_F$ to another one, and scales the measure by $\|\xi\|_{\mathbb A}$). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem ideleNorm_diagUnits (ξ : Fˣ) : ideleNorm F (diagUnits F ξ) = 1 := by
  set g := diagUnits F ξ
  have hfd := isAddFundamentalDomain_fundDom (F := F) (muAdd F)
  have hq : QuasiMeasurePreserving (fun x : Adeles F => g⁻¹ • x) (muAdd F) (muAdd F) :=
    ⟨measurable_const_smul _, by rw [map_smul_muAdd]; exact Measure.smul_absolutelyContinuous⟩
  set e : diagSub F → diagSub F := fun γ => ⟨(g : Adeles F) * γ, diagUnits_mul_mem ξ γ.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun γ δ h => Subtype.ext ?_, fun δ => ⟨⟨((g⁻¹ : (Adeles F)ˣ) : Adeles F) * δ, ?_⟩, ?_⟩⟩
    · exact (Units.mul_right_inj g).mp (congrArg Subtype.val h)
    · rw [show g⁻¹ = diagUnits F ξ⁻¹ by rw [map_inv]]; exact diagUnits_mul_mem ξ⁻¹ δ.2
    · exact Subtype.ext (by simp [e])
  have hef : ∀ γ : diagSub F, Function.Semiconj (fun x : Adeles F => g⁻¹ • x) (e γ +ᵥ ·) (γ +ᵥ ·) := by
    intro γ x
    change ((g⁻¹ : (Adeles F)ˣ) : Adeles F) * ((g : Adeles F) * γ + x) =
      (γ : Adeles F) + ((g⁻¹ : (Adeles F)ˣ) : Adeles F) * x
    rw [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
  have hfd' := hfd.preimage_of_equiv hq he hef
  have hmeq := hfd.measure_eq hfd'
  rw [muAdd_fundDom, ← Measure.map_apply (measurable_const_smul _) measurableSet_fundDom, map_smul_muAdd,
    Measure.smul_apply, muAdd_fundDom, smul_eq_mul, mul_one, ideleNorm_inv, inv_inv] at hmeq
  have h := congrArg ENNReal.toReal hmeq
  rwa [ENNReal.toReal_one, ENNReal.toReal_ofReal (ideleNorm_pos g).le, eq_comm] at h

/-! ### The norm as a continuous homomorphism; $\mathbb A_F^1$ -/

variable (F) in
/-- $\|\cdot\|_{\mathbb A}:\mathbb A_F^\times\to\mathbb R_{>0}$ as a homomorphism (`coe_ideleNormHom`). -/
def ideleNormHom : (Adeles F)ˣ →* ℝ≥0 := distribHaarChar (Adeles F)

theorem coe_ideleNormHom (g : (Adeles F)ˣ) : (ideleNormHom F g : ℝ) = ideleNorm F g := distribHaarChar_adeles g

theorem modAt_eq_one_of_mem {g : AFˣ} (hg : g ∈ OHatUnits F) (v : HeightOneSpectrum (𝓞 F)) : modAt g v = 1 :=
  distribHaarChar_eq_one_of_mem _ (hg.1 v) (hg.2 v)

theorem continuous_finPart : Continuous (finPart : (Adeles F)ˣ → AFˣ) :=
  Units.continuous_iff.mpr ⟨continuous_snd.comp Units.continuous_val, continuous_snd.comp Units.continuous_coe_inv⟩

theorem continuous_infPart : Continuous (infPart : (Adeles F)ˣ → (mixedSpace F)ˣ) :=
  Units.continuous_iff.mpr ⟨continuous_fst.comp Units.continuous_val, continuous_fst.comp Units.continuous_coe_inv⟩

theorem continuous_abs_det_mulLeft :
    Continuous fun t : mixedSpace F => |LinearMap.det (LinearMap.mulLeft ℝ t)| := by
  simp_rw [det_mulLeft_mixedSpace]
  refine Continuous.abs (Continuous.mul ?_ ?_)
  · exact continuous_finsetProd _ fun w _ => (continuous_apply w).comp continuous_fst
  · exact continuous_finsetProd _ fun w _ =>
      Complex.continuous_normSq.comp ((continuous_apply w).comp continuous_snd)

/-- **The idele norm is continuous** (on the open subgroup $F_\infty^\times\times\hat{\mathcal O}^\times$ it is
$|\det(g_\infty\cdot)|$). -/
theorem continuous_ideleNormHom : Continuous (ideleNormHom F) := by
  refine continuous_of_continuousAt_one _ ?_
  have hW : finPart ⁻¹' (OHatUnits F : Set AFˣ) ∈ 𝓝 (1 : (Adeles F)ˣ) :=
    (isOpen_OHatUnits.preimage continuous_finPart).mem_nhds (by
      show finPart 1 ∈ OHatUnits F
      rw [show finPart (1 : (Adeles F)ˣ) = 1 from Units.ext rfl]; exact (OHatUnits F).one_mem)
  have hc : Continuous fun g : (Adeles F)ˣ =>
      Real.toNNReal |LinearMap.det (LinearMap.mulLeft ℝ ((infPart g : (mixedSpace F)ˣ) : mixedSpace F))| :=
    continuous_real_toNNReal.comp (continuous_abs_det_mulLeft.comp (Units.continuous_val.comp continuous_infPart))
  refine (hc.continuousAt.congr ?_)
  filter_upwards [hW] with g hg
  apply NNReal.coe_injective
  rw [coe_ideleNormHom, ideleNorm, Real.coe_toNNReal _ (abs_nonneg _),
    finprod_eq_one_of_forall_eq_one fun v => by rw [modAt_eq_one_of_mem hg v, NNReal.coe_one], mul_one]

theorem continuous_ideleNorm : Continuous (ideleNorm F) := by
  have : ideleNorm F = fun g => (ideleNormHom F g : ℝ) := funext fun g => (coe_ideleNormHom g).symm
  rw [this]; exact NNReal.continuous_coe.comp continuous_ideleNormHom

variable (F) in
/-- **$\mathbb A_F^1$**, the ideles of norm $1$. -/
def ideleOne : Subgroup (Adeles F)ˣ := (ideleNormHom F).ker

theorem mem_ideleOne {g : (Adeles F)ˣ} : g ∈ ideleOne F ↔ ideleNorm F g = 1 := by
  rw [ideleOne, MonoidHom.mem_ker, ← coe_ideleNormHom, NNReal.coe_eq_one]

theorem isClosed_ideleOne : IsClosed (ideleOne F : Set (Adeles F)ˣ) :=
  isClosed_eq continuous_ideleNormHom continuous_const

/-- $F^\times\le\mathbb A_F^1$ (the product formula). -/
theorem diagUnitsSub_le_ideleOne : diagUnitsSub F ≤ ideleOne F := by
  rintro _ ⟨ξ, rfl⟩; exact mem_ideleOne.mpr (ideleNorm_diagUnits ξ)

/-! ### A section of the norm: $\mathbb A_F^\times = \mathbb A_F^1\cdot\mathbb R_{>0}$ -/

variable (F) in
/-- The idele with every archimedean component $t^{1/[F:\mathbb Q]}$ (real, also at complex places) and every finite
component $1$; its norm is $t$ (`ideleNorm_normSection`). -/
def normSection (t : ℝ) (ht : 0 < t) : (Adeles F)ˣ where
  val := ((fun _ => t ^ ((Module.finrank ℚ F : ℝ)⁻¹), fun _ => ((t ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ)), 1)
  inv := ((fun _ => (t ^ ((Module.finrank ℚ F : ℝ)⁻¹))⁻¹,
    fun _ => (((t ^ ((Module.finrank ℚ F : ℝ)⁻¹))⁻¹ : ℝ) : ℂ)), 1)
  val_inv := by
    have h : t ^ ((Module.finrank ℚ F : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    refine Prod.ext (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)) (one_mul _)
    · exact mul_inv_cancel₀ h
    · change ((t ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) * (((t ^ ((Module.finrank ℚ F : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ h, Complex.ofReal_one]
  inv_val := by
    have h : t ^ ((Module.finrank ℚ F : ℝ)⁻¹) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    refine Prod.ext (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)) (one_mul _)
    · exact inv_mul_cancel₀ h
    · change (((t ^ ((Module.finrank ℚ F : ℝ)⁻¹))⁻¹ : ℝ) : ℂ) * ((t ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ h, Complex.ofReal_one]

theorem modAt_one (v : HeightOneSpectrum (𝓞 F)) : modAt (1 : AFˣ) v = 1 := by
  rw [modAt, show unitAt (1 : AFˣ) v = 1 from Units.ext rfl, map_one]

/-- $\|\operatorname{normSection}(t)\|_{\mathbb A} = t$ (uses $r_1 + 2r_2 = [F:\mathbb Q]$). -/
theorem ideleNorm_normSection (t : ℝ) (ht : 0 < t) : ideleNorm F (normSection F t ht) = t := by
  have hfin : finPart (normSection F t ht) = 1 := Units.ext rfl
  set s := t ^ ((Module.finrank ℚ F : ℝ)⁻¹) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos ht _
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [ideleNorm, hfin, finprod_eq_one_of_forall_eq_one fun v => by rw [modAt_one, NNReal.coe_one], mul_one]
  change |LinearMap.det (LinearMap.mulLeft ℝ ((fun _ => s, fun _ => (s : ℂ)) : mixedSpace F))| = t
  rw [det_mulLeft_mixedSpace]
  simp only [Finset.prod_const, Finset.card_univ, Complex.normSq_ofReal]
  rw [abs_of_pos (by positivity), ← pow_two, ← pow_mul, ← pow_add]
  change s ^ (InfinitePlace.nrRealPlaces F + 2 * InfinitePlace.nrComplexPlaces F) = t
  rw [InfinitePlace.card_add_two_mul_card_eq_rank, hs, ← Real.rpow_natCast, ← Real.rpow_mul ht.le,
    inv_mul_cancel₀ hn, Real.rpow_one]

/-- **$\mathbb A_F^\times = \mathbb A_F^1\cdot\mathbb R_{>0}$**: $g\cdot\operatorname{normSection}(\|g\|)^{-1}\in\mathbb A_F^1$. -/
theorem mul_normSection_inv_mem_ideleOne (g : (Adeles F)ˣ) :
    g * (normSection F (ideleNorm F g) (ideleNorm_pos g))⁻¹ ∈ ideleOne F := by
  rw [mem_ideleOne, ideleNorm_mul, ideleNorm_inv, ideleNorm_normSection, mul_inv_cancel₀ (ideleNorm_pos g).ne']

/-! ### Fundamental domains for $F^\times$ -/

/-- A measurable fundamental domain for $F^\times$ in $\mathbb A_F^\times$, for every measure. -/
theorem exists_isFundamentalDomain_ideles (μ : Measure (Adeles F)ˣ) :
    ∃ D : Set (Adeles F)ˣ, IsFundamentalDomain (diagUnitsSub F) D μ :=
  exists_isFundamentalDomain _ μ

instance : SecondCountableTopology (ideleOne F) := TopologicalSpace.Subtype.secondCountableTopology _

variable (F) in
/-- $F^\times$ as a subgroup of $\mathbb A_F^1$. -/
def diagUnitsOne : Subgroup (ideleOne F) := (diagUnitsSub F).subgroupOf (ideleOne F)

instance : DiscreteTopology (diagUnitsOne F) := by
  refine DiscreteTopology.of_continuous_injective (f := fun x : diagUnitsOne F =>
    (⟨(x : ideleOne F), x.2⟩ : diagUnitsSub F)) ?_ ?_
  · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  · intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : diagUnitsSub F => (z : (Adeles F)ˣ)) h))

/-- A measurable fundamental domain for $F^\times$ in $\mathbb A_F^1$, for every measure. -/
theorem exists_isFundamentalDomain_ideleOne (μ : Measure (ideleOne F)) :
    ∃ D : Set (ideleOne F), IsFundamentalDomain (diagUnitsOne F) D μ :=
  exists_isFundamentalDomain _ μ

/-! ### Local units and the convergence factors $\lambda_v$ -/

/-- $\mathcal O_v^\times = \{x\in F_v : |x|_v = 1\}$. -/
def unitsV (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F) := {x | Valued.v x = 1}

theorem unitsV_eq (v : HeightOneSpectrum (𝓞 F)) :
    unitsV v = (Analysis.latticeV v 0 : Set (v.adicCompletion F)) \ (Analysis.latticeV v 1 : Set _) := by
  ext x
  simp only [unitsV, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, Analysis.mem_latticeV, neg_zero,
    WithZero.exp_zero]
  constructor
  · intro h
    rw [h]
    refine ⟨le_rfl, fun h1 => ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v x ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le)
    rw [← WithZero.exp_log hx0] at h1 h2 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    rw [WithZero.exp_le_exp] at h2
    rw [← WithZero.exp_zero]
    congr 1
    omega

theorem measurableSet_unitsV (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (unitsV v) := by
  rw [unitsV_eq]
  exact (Analysis.measurableSet_latticeV v 0).diff (Analysis.measurableSet_latticeV v 1)

/-- **$\operatorname{vol}(\mathcal O_v^\times) = (1 - N(v)^{-1})\operatorname{vol}(\mathcal O_v)$** for the self-dual measure
($\mathcal O_v^\times = \mathcal O_v\setminus\varpi\mathcal O_v$, and $\operatorname{vol}(\varpi\mathcal O_v) =
N(v)^{-1}\operatorname{vol}(\mathcal O_v)$). -/
theorem selfDualV_unitsV (v : HeightOneSpectrum (𝓞 F)) :
    Analysis.selfDualV v (unitsV v) = ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v := by
  have hsub : (Analysis.latticeV v 1 : Set (v.adicCompletion F)) ⊆ Analysis.latticeV v 0 := by
    intro x hx
    rw [SetLike.mem_coe, Analysis.mem_latticeV] at hx ⊢
    exact hx.trans (by rw [WithZero.exp_le_exp]; omega)
  have h0 : Analysis.selfDualV v (Analysis.latticeV v 0 : Set (v.adicCompletion F)) = volO v := by
    rw [volO, coe_adicCompletionIntegers_eq]
  have h1 : Analysis.selfDualV v (Analysis.latticeV v 1 : Set (v.adicCompletion F)) =
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v := by
    rw [show (1 : ℤ) = 0 + 1 from rfl, Analysis.latticeV_succ, ← distribHaarChar_mul, ← Analysis.modV, h0,
      ← Analysis.modV_eq, ENNReal.ofReal_coe_nnreal]
  have hfin : Analysis.selfDualV v (Analysis.latticeV v 1 : Set (v.adicCompletion F)) ≠ ⊤ :=
    ne_top_of_le_ne_top (h0 ▸ volO_ne_top v) (measure_mono hsub)
  rw [unitsV_eq, measure_sdiff hsub (Analysis.measurableSet_latticeV v 1).nullMeasurableSet hfin, h0, h1,
    ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, ENNReal.sub_mul (fun _ _ => volO_ne_top v), one_mul]

/-- **Weil's convergence factor for $\mathbb G_m$**: $\lambda_v = 1 - N(v)^{-1} = L_v(1)^{-1}$. -/
def lamV (v : HeightOneSpectrum (𝓞 F)) : ℝ := 1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega)

theorem lamV_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < lamV v := by
  rw [lamV, sub_pos]; exact inv_lt_one_of_one_lt₀ (one_lt_absNorm v)

/-- **Local normalization of the Tamagawa measure of $\mathbb G_m$** (the convention $\lambda_v^{-1}\omega_v$,
$\omega_v = |x|_v^{-1}dx_v$, which equals $dx_v$ on $\mathcal O_v^\times$): $\lambda_v^{-1}\operatorname{vol}(\mathcal O_v^\times) =
\operatorname{vol}(\mathcal O_v)$, so $\prod_v\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = \prod_v\operatorname{vol}(\mathcal O_v)
= |d_F|^{-1/2}$ converges (`ohatVol_eq_finprod`). -/
@[kb "weil1982" "§2.3, p. 21 (convergence factors λ_v)"]
theorem lamV_inv_mul_selfDualV_unitsV (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (lamV v)⁻¹ * Analysis.selfDualV v (unitsV v) = volO v := by
  rw [selfDualV_unitsV, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (lamV_pos v).le), ← lamV,
    inv_mul_cancel₀ (lamV_pos v).ne', ENNReal.ofReal_one, one_mul]

/-! ### The Tamagawa measure on $\mathbb A_f^\times$ -/

variable (F) in
/-- $\hat{\mathcal O}^\times$ as a positive compact. -/
def OHatUnitsCompacts : TopologicalSpace.PositiveCompacts AFˣ where
  carrier := OHatUnits F
  isCompact' := isCompact_OHatUnits
  interior_nonempty' := ⟨1, by rw [isOpen_OHatUnits.interior_eq]; exact (OHatUnits F).one_mem⟩

variable (F) in
/-- **The Tamagawa measure $\prod_v\lambda_v^{-1}\omega_v$ on $\mathbb A_f^\times$** ($\lambda_v = 1 - N(v)^{-1}$,
$\omega_v = |x|_v^{-1}dx_v$ with $dx_v$ self-dual): the Haar measure with
$\mu(\hat{\mathcal O}^\times) = \prod_v\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = |d_F|^{-1/2}$
(`muFinUnits_OHatUnits_eq_finprod`). -/
def muFinUnits : Measure AFˣ := ENNReal.ofReal (ohatVol F) • Measure.haarMeasure (OHatUnitsCompacts F)

instance : (muFinUnits F).IsHaarMeasure :=
  Measure.IsHaarMeasure.smul _ (by simp [ohatVol_pos]) ENNReal.ofReal_ne_top

theorem muFinUnits_OHatUnits : muFinUnits F (OHatUnits F) = ENNReal.ofReal (ohatVol F) := by
  rw [muFinUnits, Measure.smul_apply, smul_eq_mul]
  have := Measure.haarMeasure_self (K₀ := OHatUnitsCompacts F)
  change ENNReal.ofReal (ohatVol F) * Measure.haarMeasure (OHatUnitsCompacts F) (OHatUnitsCompacts F : Set _) = _
  rw [this, mul_one]

/-- **Normalization of the Tamagawa measure on $\mathbb A_f^\times$**:
$\mu(\hat{\mathcal O}^\times) = \prod_v\lambda_v^{-1}\operatorname{vol}(\mathcal O_v^\times)$ (a convergent product equal
to $|d_F|^{-1/2}$). -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure ∏_v λ_v^{-1} ω_v)"]
theorem muFinUnits_OHatUnits_eq_finprod :
    (muFinUnits F (OHatUnits F)).toReal =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), (lamV v)⁻¹ * (Analysis.selfDualV v).real (unitsV v) := by
  rw [muFinUnits_OHatUnits, ENNReal.toReal_ofReal ohatVol_pos.le, ohatVol_eq_finprod]
  refine finprod_congr fun v => ?_
  have h := congrArg ENNReal.toReal (lamV_inv_mul_selfDualV_unitsV v)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (lamV_pos v).le)] at h
  rw [Measure.real, Measure.real, h, volO, coe_adicCompletionIntegers_eq]

end

end QuadFormsKB.Tamagawa.Measure.Weil
