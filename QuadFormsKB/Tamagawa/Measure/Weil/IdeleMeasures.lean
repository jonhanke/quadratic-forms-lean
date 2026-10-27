import QuadFormsKB.Tamagawa.Measure.Weil.Ideles
import QuadFormsKB.Tamagawa.Measure.Weil.HaarSplitting
import QuadFormsKB.Tamagawa.Measure.Weil.UnitsHaar

/-!
# Weil's Tamagawa measure on $\mathbb A_F^\times$, $\mathbb A_F^1$ and $\mathbb A_F^1/F^\times$

$F$ is any number field. With $\Delta$ the modulus (`distribHaarChar`) and the library's self-dual additive measures:

* **`omegaInf F`** on $F_\infty^\times$: Weil's $\omega_\infty = |x|_\infty^{-1}dx$ (`omegaInf_eq`: the density is
  $|\det(x\cdot)|^{-1}$ against the self-dual `selfDualInf`, i.e. $\prod_{\text{real}}dx_w/|x_w|\cdot
  \prod_{\text{complex}}2\,dx_w\,dy_w/|z_w|^2$); a Haar measure (`unitsHaar`, generic).
* **`omegaV v`** on $F_v^\times$: $\omega_v = |x|_v^{-1}dx_v$, a Haar measure; **`omegaV_unitsVSub`**:
  $\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v^\times)$, so (**`lamV_inv_mul_omegaV_unitsVSub`**)
  $\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v)$, the factor of `muFinUnits` on $\hat{\mathcal O}^\times$
  (`muFinUnits_OHatUnits_eq_finprod`).
* **`tamIdeles F`** $=\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ on $\mathbb A_F^\times = F_\infty^\times\times\mathbb A_f^\times$
  (Weil's Tamagawa measure for $A = F$ without the global factor $\rho_F^{-1}$, which stays separate as in AAG §2.3,
  p. 21); a Haar measure; `tamIdeles_prod` on boxes.
* **`ideleSplit F`**: $\mathbb A_F^\times\cong\mathbb A_F^1\times\mathbb R_{>0}$, $g\mapsto(g\,s(\|g\|)^{-1}, \|g\|)$ with the
  section `normSection`; **`map_ideleSplit_tamIdeles`**: the image of `tamIdeles` is $\mu^1\times dt/t$ for the Haar
  measure **`muIdeleOne F`** on $\mathbb A_F^1$; **`muIdeleOne_apply`**: $\mu^1(E) = \mu(\{g : g\,s(\|g\|)^{-1}\in E,\
  1\le\|g\|\le e\})$.
* **`muIdeleClass F`** on $F^\times\backslash\mathbb A_F^1$: the image of $\mu^1$ restricted to a fundamental domain;
  **`map_restrict_eq_muIdeleClass`**: it does not depend on the fundamental domain; `muIdeleClass_univ`: its total mass
  is $\mu^1(D)$ for every fundamental domain $D$.

*Remark (not proved here; the job).* Weil's Theorem 3.1.1 (iii) for $A = F$ (Tate) gives
$\operatorname{vol}(F^\times\backslash\mathbb A_F^1) = \rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$ for the measure
$\mu^1$ (no $\rho_F^{-1}$), i.e. $c_F = \rho_F$ (the class number formula, KB's `dedekindZeta_residue`).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Set
open scoped ENNReal NNReal

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### $\omega_\infty$ on $F_\infty^\times$ -/

instance measurableSpace_infUnits : MeasurableSpace (mixedSpace F)ˣ := borel _

instance : BorelSpace (mixedSpace F)ˣ := ⟨rfl⟩

theorem continuous_distribHaarChar_mixedSpace :
    Continuous (distribHaarChar (mixedSpace F) : (mixedSpace F)ˣ → ℝ≥0) := by
  have h : (fun u : (mixedSpace F)ˣ => (distribHaarChar (mixedSpace F) u : ℝ)) =
      fun u : (mixedSpace F)ˣ => |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))| :=
    funext distribHaarChar_mixedSpace
  have hc : Continuous fun u : (mixedSpace F)ˣ => (distribHaarChar (mixedSpace F) u : ℝ) := by
    rw [h]; exact continuous_abs_det_mulLeft.comp Units.continuous_val
  exact continuous_induced_rng.mpr hc

open scoped Classical in
theorem isOpenEmbedding_val_mixedSpace : IsOpenEmbedding (Units.val : (mixedSpace F)ˣ → mixedSpace F) :=
  Units.isOpenEmbedding_val

variable (F) in
/-- **Weil's $\omega_\infty$ on $F_\infty^\times$**: $|x|_\infty^{-1}dx$ with $dx$ the self-dual measure (`omegaInf_eq`). -/
def omegaInf : Measure (mixedSpace F)ˣ := unitsHaar (mixedSpace F) (Analysis.selfDualInf (F := F))

instance : (omegaInf F).IsHaarMeasure :=
  isHaarMeasure_unitsHaar isOpenEmbedding_val_mixedSpace continuous_distribHaarChar_mixedSpace _

/-- **$\omega_\infty = |\det(x\cdot)|^{-1}\,dx$** on $F_\infty^\times$ ($= \prod_{\text{real}}dx_w/|x_w|\cdot
\prod_{\text{complex}}2\,dx_w\,dy_w/|z_w|^2$, by `det_mulLeft_mixedSpace`). -/
@[kb "weil1982" "§2.3 [unverified page] (ω_∞ = |x|^{-1}dx at the archimedean places)"]
theorem omegaInf_eq : omegaInf F = ((Analysis.selfDualInf (F := F)).comap Units.val).withDensity
    fun u => ENNReal.ofReal |LinearMap.det (LinearMap.mulLeft ℝ (u : mixedSpace F))|⁻¹ := by
  rw [omegaInf, unitsHaar]
  congr 1
  funext u
  rw [← ENNReal.ofReal_coe_nnreal, map_inv, NNReal.coe_inv, distribHaarChar_mixedSpace]

/-! ### $\omega_v$ on $F_v^\times$ -/

instance measurableSpace_unitsAt (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩

theorem isOpenEmbedding_val_adic (v : HeightOneSpectrum (𝓞 F)) :
    IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) = {0}ᶜ := by
    ext x
    simp only [mem_range, mem_compl_iff, mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [this]
  exact isOpen_compl_singleton

theorem continuous_distribHaarChar_adic (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (distribHaarChar (v.adicCompletion F) : (v.adicCompletion F)ˣ → ℝ≥0) := by
  refine continuous_distribHaarChar_of_eventually_eq_one ?_
  have hW : IsOpen {u : (v.adicCompletion F)ˣ | (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F} :=
    ((isOpen_adicCompletionIntegers v).preimage Units.continuous_val).inter
      ((isOpen_adicCompletionIntegers v).preimage Units.continuous_coe_inv)
  filter_upwards [hW.mem_nhds ⟨one_mem _, by rw [inv_one]; exact one_mem _⟩] with u hu
  exact distribHaarChar_eq_one_of_mem u hu.1 hu.2

/-- **Weil's $\omega_v = |x|_v^{-1}dx_v$ on $F_v^\times$** ($dx_v$ self-dual). -/
def omegaV (v : HeightOneSpectrum (𝓞 F)) : Measure (v.adicCompletion F)ˣ :=
  unitsHaar (v.adicCompletion F) (Analysis.selfDualV v)

instance (v : HeightOneSpectrum (𝓞 F)) : (omegaV v).IsHaarMeasure :=
  isHaarMeasure_unitsHaar (isOpenEmbedding_val_adic v) (continuous_distribHaarChar_adic v) _

/-- $\mathcal O_v^\times$ as a subset of $F_v^\times$. -/
def unitsVSub (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F)ˣ := {u | Valued.v (u : v.adicCompletion F) = 1}

theorem val_image_unitsVSub (v : HeightOneSpectrum (𝓞 F)) : Units.val '' unitsVSub v = unitsV v := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [unitsV, mem_ofPred_eq, h0, map_zero] at hx; exact zero_ne_one hx
    exact ⟨Units.mk0 x hx0, hx, rfl⟩

theorem measurableSet_unitsVSub (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (unitsVSub v) :=
  Units.continuous_val.measurable (measurableSet_unitsV v)

theorem distribHaarChar_eq_one_of_mem_unitsVSub {v : HeightOneSpectrum (𝓞 F)} {u : (v.adicCompletion F)ˣ}
    (hu : u ∈ unitsVSub v) : distribHaarChar (v.adicCompletion F) u = 1 := by
  have h1 : Valued.v (u : v.adicCompletion F) = 1 := hu
  have h2 : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, h1, inv_one]
  refine distribHaarChar_eq_one_of_mem u ?_ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, h1]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, h2]

/-- **$\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v^\times)$** ($|x|_v = 1$ there). -/
theorem omegaV_unitsVSub (v : HeightOneSpectrum (𝓞 F)) :
    omegaV v (unitsVSub v) = Analysis.selfDualV v (unitsV v) := by
  rw [omegaV, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_adic v) (continuous_distribHaarChar_adic v) _
    (measurableSet_unitsVSub v) fun u hu => distribHaarChar_eq_one_of_mem_unitsVSub hu, val_image_unitsVSub]

/-- **Local normalization**: $\lambda_v^{-1}\omega_v(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v)$, the local factor of
`muFinUnits F` on $\hat{\mathcal O}^\times$ (`muFinUnits_OHatUnits_eq_finprod`). -/
@[kb "weil1982" "§2.3, p. 21 (λ_v^{-1}ω_v, ω_v = |x|_v^{-1}dx_v)"]
theorem lamV_inv_mul_omegaV_unitsVSub (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (lamV v)⁻¹ * omegaV v (unitsVSub v) = volO v := by
  rw [omegaV_unitsVSub, lamV_inv_mul_selfDualV_unitsV]

/-! ### The Tamagawa measure on $\mathbb A_F^\times$ -/

variable (F) in
/-- $\mathbb A_F^\times = F_\infty^\times\times\mathbb A_f^\times$ as topological groups. -/
def idelesEquiv : (Adeles F)ˣ ≃ₜ* ((mixedSpace F)ˣ × AFˣ) where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := Homeomorph.prodUnits.continuous
  continuous_invFun := Homeomorph.prodUnits.symm.continuous

@[simp] theorem idelesEquiv_apply (g : (Adeles F)ˣ) : idelesEquiv F g = (infPart g, finPart g) := rfl

variable (F) in
/-- **Weil's Tamagawa measure on $\mathbb A_F^\times$** (convergence factors $\lambda_v = 1 - N(v)^{-1}$; the global factor
$\rho_F^{-1}$ of AAG §2.3 is kept separate): $\omega_\infty\times\prod_v\lambda_v^{-1}\omega_v$ (`tamIdeles_prod`). -/
def tamIdeles : Measure (Adeles F)ˣ := ((omegaInf F).prod (muFinUnits F)).map (idelesEquiv F).symm

instance : (tamIdeles F).IsHaarMeasure := by
  rw [tamIdeles]; infer_instance

/-- **`tamIdeles` on boxes**: $\mu(\{g : g_\infty\in A,\ g_f\in B\}) = \omega_\infty(A)\cdot\mu_f(B)$. -/
@[kb "weil1982" "§2.3, p. 21 (Tamagawa measure of A_𝔸^×)"]
theorem tamIdeles_prod (A : Set (mixedSpace F)ˣ) (B : Set AFˣ) :
    tamIdeles F (idelesEquiv F ⁻¹' (A ×ˢ B)) = omegaInf F A * muFinUnits F B := by
  have : ((idelesEquiv F).symm : _ → (Adeles F)ˣ) = (idelesEquiv F).symm.toHomeomorph.toMeasurableEquiv := rfl
  rw [tamIdeles, this, MeasurableEquiv.map_apply]
  change ((omegaInf F).prod (muFinUnits F)) ((idelesEquiv F).symm ⁻¹' (idelesEquiv F ⁻¹' (A ×ˢ B))) = _
  rw [← preimage_comp]
  have h2 : (idelesEquiv F ∘ (idelesEquiv F).symm) = id := funext fun p => (idelesEquiv F).apply_symm_apply p
  rw [h2, preimage_id, Measure.prod_prod]

/-! ### $\mathbb A_F^\times = \mathbb A_F^1\times\mathbb R_{>0}$ and the measure $\mu^1$ -/

variable (F) in
/-- $g\mapsto\log\|g\|_{\mathbb A}$, as a homomorphism $\mathbb A_F^\times\to\mathbb R_{>0}$ = `Multiplicative ℝ`. -/
def ideleLogNorm : (Adeles F)ˣ →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (Real.log (ideleNorm F g))
  map_one' := by rw [ideleNorm_one, Real.log_one]; rfl
  map_mul' g h := by
    rw [ideleNorm_mul, Real.log_mul (ideleNorm_pos g).ne' (ideleNorm_pos h).ne']; rfl

theorem continuous_ideleLogNorm : Continuous (ideleLogNorm F) :=
  continuous_ofAdd.comp
    (Real.continuousOn_log.comp_continuous continuous_ideleNorm fun g => (ideleNorm_pos g).ne')

theorem mem_ideleOne_iff_logNorm (g : (Adeles F)ˣ) : g ∈ ideleOne F ↔ ideleLogNorm F g = 1 := by
  rw [mem_ideleOne]
  change _ ↔ Multiplicative.ofAdd (Real.log (ideleNorm F g)) = 1
  rw [ofAdd_eq_one]
  constructor
  · intro h; rw [h, Real.log_one]
  · intro h; rw [← Real.exp_log (ideleNorm_pos g), h, Real.exp_zero]

theorem normSection_mul (t t' : ℝ) (ht : 0 < t) (ht' : 0 < t') :
    normSection F (t * t') (mul_pos ht ht') = normSection F t ht * normSection F t' ht' := by
  refine Units.ext (Prod.ext (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)) (mul_one 1).symm)
  · exact Real.mul_rpow ht.le ht'.le
  · change (((t * t') ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) =
      ((t ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) * ((t' ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ)
    rw [Real.mul_rpow ht.le ht'.le, Complex.ofReal_mul]

theorem normSection_one : normSection F 1 one_pos = 1 := by
  refine Units.ext (Prod.ext (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)) rfl)
  · exact Real.one_rpow _
  · change (((1 : ℝ) ^ ((Module.finrank ℚ F : ℝ)⁻¹) : ℝ) : ℂ) = 1
    rw [Real.one_rpow, Complex.ofReal_one]

variable (F) in
/-- The section $t\mapsto\operatorname{normSection}(t)$ as a homomorphism $\mathbb R_{>0}\to\mathbb A_F^\times$. -/
def normSectionHom : Multiplicative ℝ →* (Adeles F)ˣ where
  toFun a := normSection F (Real.exp a.toAdd) (Real.exp_pos _)
  map_one' := by
    have : Real.exp (Multiplicative.toAdd (1 : Multiplicative ℝ)) = 1 := by rw [toAdd_one, Real.exp_zero]
    rw [← normSection_one (F := F)]
    congr 1
  map_mul' a b := by
    rw [← normSection_mul]
    congr 1
    rw [toAdd_mul, Real.exp_add]

theorem continuous_normSectionHom : Continuous (normSectionHom F) := by
  set c : ℝ := (Module.finrank ℚ F : ℝ)⁻¹
  have h : Continuous fun a : Multiplicative ℝ => Real.exp a.toAdd ^ c :=
    (Real.continuous_exp.comp continuous_toAdd).rpow_const fun _ => Or.inl (Real.exp_pos _).ne'
  have h' : Continuous fun a : Multiplicative ℝ => (Real.exp a.toAdd ^ c)⁻¹ :=
    h.inv₀ fun _ => (Real.rpow_pos_of_pos (Real.exp_pos _) _).ne'
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun a : Multiplicative ℝ =>
      (((fun _ => Real.exp a.toAdd ^ c, fun _ => ((Real.exp a.toAdd ^ c : ℝ) : ℂ)) : mixedSpace F), (1 : AF))
    exact ((continuous_pi fun _ => h).prodMk (continuous_pi fun _ => Complex.continuous_ofReal.comp h)).prodMk
      continuous_const
  · change Continuous fun a : Multiplicative ℝ =>
      (((fun _ => (Real.exp a.toAdd ^ c)⁻¹, fun _ => (((Real.exp a.toAdd ^ c)⁻¹ : ℝ) : ℂ)) : mixedSpace F), (1 : AF))
    exact ((continuous_pi fun _ => h').prodMk (continuous_pi fun _ => Complex.continuous_ofReal.comp h')).prodMk
      continuous_const

theorem ideleLogNorm_normSectionHom (a : Multiplicative ℝ) : ideleLogNorm F (normSectionHom F a) = a := by
  change Multiplicative.ofAdd (Real.log (ideleNorm F (normSection F (Real.exp a.toAdd) (Real.exp_pos _)))) = a
  rw [ideleNorm_normSection, Real.log_exp]; rfl

instance : LocallyCompactSpace (ideleOne F) :=
  isClosed_ideleOne.isClosedEmbedding_subtypeVal.locallyCompactSpace

variable (F) in
/-- **$\mathbb A_F^\times\cong\mathbb A_F^1\times\mathbb R_{>0}$**, $g\mapsto(g\,\operatorname{normSection}(\|g\|)^{-1},
\log\|g\|)$ (`splitEquiv`). -/
def ideleSplit : (Adeles F)ˣ ≃ₜ* (ideleOne F × Multiplicative ℝ) :=
  splitEquiv (ideleLogNorm F) (normSectionHom F) (ideleOne F) mem_ideleOne_iff_logNorm ideleLogNorm_normSectionHom
    (fun _ _ => mul_comm _ _) continuous_ideleLogNorm continuous_normSectionHom

theorem ideleSplit_apply_snd (g : (Adeles F)ˣ) :
    (ideleSplit F g).2 = Multiplicative.ofAdd (Real.log (ideleNorm F g)) := rfl

variable (F) in
/-- **The Haar measure $\mu^1$ on $\mathbb A_F^1$**: the unique measure with $(\text{`ideleSplit`})_*\mu = \mu^1\times dt/t$
(`map_ideleSplit_tamIdeles`, `splitMeasure_unique`). -/
def muIdeleOne : Measure (ideleOne F) := splitMeasure (ideleSplit F) (tamIdeles F) dtt

instance : (muIdeleOne F).IsHaarMeasure := isHaarMeasure_splitMeasure _ _ _

/-- **Measure splitting $\mathbb A_F^\times\cong\mathbb A_F^1\times\mathbb R_{>0}$**: the Tamagawa measure is
$\mu^1\times dt/t$. -/
@[kb "weil1982" "§2.3 [unverified page] (A_𝔸^× = A_𝔸^1 × ℝ_{>0}, ω = ω^1 × dt/t)"]
theorem map_ideleSplit_tamIdeles : (tamIdeles F).map (ideleSplit F) = (muIdeleOne F).prod dtt :=
  map_eq_prod_splitMeasure _ _ _

theorem mem_ideleSplit_preimage {E : Set (ideleOne F)} {g : (Adeles F)ˣ} :
    g ∈ ideleSplit F ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1)) ↔
      (ideleSplit F g).1 ∈ E ∧ 1 ≤ ideleNorm F g ∧ ideleNorm F g ≤ Real.exp 1 := by
  have hp := ideleNorm_pos g
  simp only [mem_preimage, mem_prod, ideleSplit_apply_snd, toAdd_ofAdd, mem_Icc]
  rw [Real.log_nonneg_iff hp, Real.log_le_iff_le_exp hp]

/-- **$\mu^1(E) = \mu(\{g\in\mathbb A_F^\times : g\,s(\|g\|)^{-1}\in E,\ 1\le\|g\|_{\mathbb A}\le e\})$** (since
$\int_1^e dt/t = 1$; the condition is `mem_ideleSplit_preimage`). -/
@[kb "weil1982" "§2.3 [unverified page] (the measure ω^1 on A_𝔸^1)"]
theorem muIdeleOne_apply (E : Set (ideleOne F)) :
    muIdeleOne F E = tamIdeles F (ideleSplit F ⁻¹' (E ×ˢ (Multiplicative.toAdd ⁻¹' Icc (0 : ℝ) 1))) := by
  rw [muIdeleOne, splitMeasure_apply _ _ _ (by rw [dtt_ofAdd_Icc]; exact one_ne_zero)
    (by rw [dtt_ofAdd_Icc]; exact ENNReal.one_ne_top), dtt_ofAdd_Icc, div_one]

/-! ### The quotient $F^\times\backslash\mathbb A_F^1$ -/

instance : Countable (diagUnitsOne F) :=
  Function.Injective.countable (f := fun x : diagUnitsOne F => (⟨(x : ideleOne F), x.2⟩ : diagUnitsSub F))
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : diagUnitsSub F => (z : (Adeles F)ˣ)) h))

variable (F) in
/-- A fixed measurable fundamental domain of $F^\times$ in $\mathbb A_F^1$ for $\mu^1$. -/
def ideleClassFD : Set (ideleOne F) := (exists_isFundamentalDomain_ideleOne (muIdeleOne F)).choose

theorem isFundamentalDomain_ideleClassFD : IsFundamentalDomain (diagUnitsOne F) (ideleClassFD F) (muIdeleOne F) :=
  (exists_isFundamentalDomain_ideleOne (muIdeleOne F)).choose_spec

variable (F) in
/-- $F^\times\backslash\mathbb A_F^1$ (orbits of the left multiplication action). -/
abbrev IdeleClassOne := Quotient (MulAction.orbitRel (diagUnitsOne F) (ideleOne F))

variable (F) in
/-- The projection $\mathbb A_F^1	o F^	imesackslash\mathbb A_F^1$. -/
abbrev ideleClassMk : ideleOne F → IdeleClassOne F := Quotient.mk (MulAction.orbitRel (diagUnitsOne F) (ideleOne F))

theorem measurable_ideleClassMk : Measurable (ideleClassMk F) := fun _ hs => hs

variable (F) in
/-- **The quotient measure on $F^\times\backslash\mathbb A_F^1$**: the image of $\mu^1$ restricted to a fundamental domain
(independent of it, `map_restrict_eq_muIdeleClass`). -/
def muIdeleClass : Measure (IdeleClassOne F) :=
  ((muIdeleOne F).restrict (ideleClassFD F)).map (ideleClassMk F)

/-- **The quotient measure does not depend on the fundamental domain.** -/
@[kb "weil1982" "§2.3 [unverified page] (measure on A_𝔸^1/A^×)"]
theorem map_restrict_eq_muIdeleClass {D : Set (ideleOne F)}
    (hD : IsFundamentalDomain (diagUnitsOne F) D (muIdeleOne F)) :
    ((muIdeleOne F).restrict D).map (ideleClassMk F) = muIdeleClass F := by
  ext A hA
  have hm := measurable_ideleClassMk (F := F)
  rw [muIdeleClass, Measure.map_apply hm hA, Measure.map_apply hm hA, Measure.restrict_apply (hm hA),
    Measure.restrict_apply (hm hA)]
  refine hD.measure_set_eq isFundamentalDomain_ideleClassFD (hm hA) fun γ => ?_
  ext x
  simp only [mem_preimage]
  have : ideleClassMk F (γ • x) = ideleClassMk F x := Quotient.sound ⟨γ, rfl⟩
  rw [this]

/-- The total mass of $F^\times\backslash\mathbb A_F^1$ is $\mu^1(D)$ for every fundamental domain $D$. -/
theorem muIdeleClass_univ {D : Set (ideleOne F)} (hD : IsFundamentalDomain (diagUnitsOne F) D (muIdeleOne F)) :
    muIdeleClass F univ = muIdeleOne F D := by
  rw [← map_restrict_eq_muIdeleClass hD, Measure.map_apply measurable_ideleClassMk MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]

end

end QuadFormsKB.Tamagawa.Measure.Weil
