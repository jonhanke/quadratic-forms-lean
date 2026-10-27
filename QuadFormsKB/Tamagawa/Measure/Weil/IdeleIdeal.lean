import QuadFormsKB.Tamagawa.Measure.Weil.IdeleChart
import QuadFormsKB.Tamagawa.IdeleClass
import QuadFormsKB.Weil.ProductFormulas
import QuadFormsKB.Analysis.DifferentLocal

/-!
# The idele → ideal map $\mathbb A_f^\times\to I_F$

$F$ is any number field, $I_F$ = `IdeleClass.FracIdeal F` the group of nonzero fractional ideals.

* **`ordAt z v`** $=\operatorname{ord}_v(z_v)\in\mathbb Z$ ($v(z_v) = \exp(-\operatorname{ord}_v z_v)$), additive in $z$,
  finitely supported.
* **`ideleIdeal F : AFˣ →* FracIdeal F`**, $z\mapsto\prod_v\mathfrak p_v^{\operatorname{ord}_v z_v}$ (a finite product), with
  `count_ideleIdeal` ($\operatorname{ord}_v$ of the ideal is $\operatorname{ord}_v z_v$, Mathlib's
  `FractionalIdeal.count_finprod`);
  **`ideleIdeal_eq_one_iff`**: the kernel is $\hat{\mathcal O}^\times$ (`OHatUnits F`);
  **`ideleIdeal_surjective`** (single-place uniformizer powers, `mulSingleAt`);
  **`ideleIdeal_algebraMap`**: on $F^\times$ it is $\gamma\mapsto(\gamma)$ (`toPrincipalIdeal`), via
  `Analysis.valuation_eq_exp_neg_count`;
  **`finprod_modAt_eq`**: $\prod_v|z_v|_v = N(\mathfrak a(z))^{-1}$, so
  **`ideleNorm_eq_div`**: $\|z\|_{\mathbb A} = N(z_\infty)/N(\mathfrak a(z_f))$, which is `IdeleClass.ideleNorm`.

This is the map that identifies the concrete model $(x,\mathfrak a)$ of the unramified ideles with
$\mathbb A_F^\times/\hat{\mathcal O}^\times$ (Weil 1982, §2.1 [unverified page]; Neukirch, *Algebraic Number Theory*,
Ch. VI, (1.5) [unverified]).
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding MeasureTheory Set WithZero
open scoped ENNReal NNReal nonZeroDivisors

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### The local orders -/

/-- $\operatorname{ord}_v(z_v)$ for a finite idele $z$: $v(z_v) = \exp(-\operatorname{ord}_v z_v)$. -/
def ordAt (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : ℤ := -log (Valued.v ((z : AF) v))

theorem valued_unit_ne_zero (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : Valued.v ((z : AF) v) ≠ 0 := by
  rw [Ne, map_eq_zero]
  exact (unitAt z v).ne_zero

theorem valued_eq_exp_ordAt (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((z : AF) v) = exp (-ordAt z v) := by
  rw [ordAt, neg_neg, exp_log (valued_unit_ne_zero z v)]

theorem ordAt_mul (z w : AFˣ) (v : HeightOneSpectrum (𝓞 F)) : ordAt (z * w) v = ordAt z v + ordAt w v := by
  simp only [ordAt]
  rw [show ((z * w : AFˣ) : AF) v = (z : AF) v * (w : AF) v from rfl, map_mul,
    log_mul (valued_unit_ne_zero z v) (valued_unit_ne_zero w v)]
  ring

theorem ordAt_one (v : HeightOneSpectrum (𝓞 F)) : ordAt (1 : AFˣ) v = 0 := by
  simp only [ordAt]
  rw [show ((1 : AFˣ) : AF) v = 1 from rfl, map_one, log_one, neg_zero]

theorem ordAt_eq_zero_iff (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ordAt z v = 0 ↔ Valued.v ((z : AF) v) = 1 := by
  rw [valued_eq_exp_ordAt]
  constructor
  · intro h; rw [h, neg_zero, exp_zero]
  · intro h
    have := congrArg log h
    rw [log_exp, log_one, neg_eq_zero] at this
    exact this

theorem valued_mul_inv (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((z : AF) v) * Valued.v (((z⁻¹ : AFˣ) : AF) v) = 1 := by
  rw [← map_mul, show (z : AF) v * ((z⁻¹ : AFˣ) : AF) v = ((z * z⁻¹ : AFˣ) : AF) v from rfl, mul_inv_cancel]
  exact map_one _

theorem ordAt_eq_zero_iff_mem (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ordAt z v = 0 ↔ (z : AF) v ∈ v.adicCompletionIntegers F ∧
      ((z⁻¹ : AFˣ) : AF) v ∈ v.adicCompletionIntegers F := by
  rw [ordAt_eq_zero_iff, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.mem_adicCompletionIntegers]
  have hp := valued_mul_inv z v
  constructor
  · intro h
    rw [h, one_mul] at hp
    exact ⟨h.le, hp.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    rw [not_le] at hlt
    have : Valued.v ((z : AF) v) * Valued.v (((z⁻¹ : AFˣ) : AF) v) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [hp] at this
    exact lt_irrefl _ this

theorem finite_ordAt (z : AFˣ) : {v | ordAt z v ≠ 0}.Finite :=
  (finite_bad z).subset fun v hv => by
    simp only [mem_ofPred_eq] at hv ⊢
    exact (not_and_or.mp fun h => hv ((ordAt_eq_zero_iff_mem z v).2 h))

theorem eventually_ordAt (z : AFˣ) : ∀ᶠ v in Filter.cofinite, ordAt z v = 0 := by
  have := (finite_ordAt z).eventually_cofinite_notMem
  filter_upwards [this] with v hv
  simpa using hv

theorem mem_OHatUnits_iff_ordAt (z : AFˣ) : z ∈ OHatUnits F ↔ ∀ v, ordAt z v = 0 := by
  rw [mem_OHatUnits]
  simp only [ordAt_eq_zero_iff_mem]
  exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

/-! ### The ideal of an idele -/

local notation "FI" => IdeleClass.FracIdeal F

/-- The prime $\mathfrak p_v$ as a unit of the monoid of fractional ideals. -/
def primeUnit (v : HeightOneSpectrum (𝓞 F)) : FI :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- Two nonzero fractional ideals with the same orders at every prime are equal. -/
theorem fracIdeal_ext_count {I J : FI}
    (h : ∀ v, FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.count F v (J : FractionalIdeal (𝓞 F)⁰ F)) : I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) I.ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := F) J.ne_zero]
  simp_rw [h]

theorem hasFiniteMulSupport_primeUnit_zpow (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : {v | e v ≠ 0}.Finite) :
    (Function.mulSupport fun v => primeUnit v ^ e v).Finite :=
  he.subset fun v hv => by
    simp only [Function.mem_mulSupport, mem_ofPred_eq] at hv ⊢
    intro h0; exact hv (by rw [h0, zpow_zero])

/-- $\prod_v\mathfrak p_v^{e_v}$ as a fractional ideal unit. -/
def primeProd (e : HeightOneSpectrum (𝓞 F) → ℤ) : FI := ∏ᶠ v, primeUnit v ^ e v

theorem coe_primeProd (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : {v | e v ≠ 0}.Finite) :
    ((primeProd e : FI) : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v := by
  rw [primeProd, show ((∏ᶠ v, primeUnit v ^ e v : FI) : FractionalIdeal (𝓞 F)⁰ F) =
    (Units.coeHom (FractionalIdeal (𝓞 F)⁰ F)) (∏ᶠ v, primeUnit v ^ e v) from rfl,
    MonoidHom.map_finprod _ (hasFiniteMulSupport_primeUnit_zpow e he)]
  refine finprod_congr fun v => ?_
  rw [map_zpow]
  rfl

theorem count_primeProd (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : {v | e v ≠ 0}.Finite)
    (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v ((primeProd e : FI) : FractionalIdeal (𝓞 F)⁰ F) = e v := by
  rw [coe_primeProd e he]
  refine FractionalIdeal.count_finprod F v e ?_
  filter_upwards [he.eventually_cofinite_notMem] with w hw
  simpa using hw

variable (F) in
/-- **The ideal of a finite idele**: $\mathfrak a(z) = \prod_v\mathfrak p_v^{\operatorname{ord}_v z_v}$, a homomorphism
$\mathbb A_f^\times\to I_F$. -/
def ideleIdeal : AFˣ →* FI where
  toFun z := primeProd (ordAt z)
  map_one' := by
    refine fracIdeal_ext_count fun v => ?_
    rw [count_primeProd _ (by simp [ordAt_one]), ordAt_one, Units.val_one, FractionalIdeal.count_one]
  map_mul' z w := by
    refine fracIdeal_ext_count fun v => ?_
    rw [count_primeProd _ (finite_ordAt _), Units.val_mul,
      FractionalIdeal.count_mul F v (Units.ne_zero _) (Units.ne_zero _),
      count_primeProd _ (finite_ordAt _), count_primeProd _ (finite_ordAt _), ordAt_mul]

/-- $\operatorname{ord}_v\mathfrak a(z) = \operatorname{ord}_v z_v$. -/
theorem count_ideleIdeal (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v ((ideleIdeal F z : FI) : FractionalIdeal (𝓞 F)⁰ F) = ordAt z v :=
  count_primeProd _ (finite_ordAt z) v

/-- **The kernel of $z\mapsto\mathfrak a(z)$ is $\hat{\mathcal O}^\times$.** -/
theorem ideleIdeal_eq_one_iff (z : AFˣ) : ideleIdeal F z = 1 ↔ z ∈ OHatUnits F := by
  rw [mem_OHatUnits_iff_ordAt]
  constructor
  · intro h v
    rw [← count_ideleIdeal, h, Units.val_one, FractionalIdeal.count_one]
  · intro h
    refine fracIdeal_ext_count fun v => ?_
    rw [count_ideleIdeal, h, Units.val_one, FractionalIdeal.count_one]

theorem ker_ideleIdeal : (ideleIdeal F).ker = OHatUnits F := by
  ext z; exact ideleIdeal_eq_one_iff z

open scoped Classical in
theorem ordAt_mulSingleAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ordAt (mulSingleAt w x) v = if v = w then -log (Valued.v (x : w.adicCompletion F)) else 0 := by
  split_ifs with h
  · subst h
    rw [ordAt, ← unitAt_val, unitAt_mulSingleAt]
  · rw [ordAt, ← unitAt_val, unitAt_mulSingleAt_of_ne h, Units.val_one, map_one, log_one, neg_zero]

/-- The uniformizer $\varpi_v$ as a unit of $F_v$. -/
def uniformizerUnit (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ := Units.mk0 (HN.ϖ v) (HN.ϖ_ne_zero v)

theorem ideleIdeal_mulSingleAt_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ideleIdeal F (mulSingleAt v (uniformizerUnit v)) = primeUnit v := by
  refine fracIdeal_ext_count fun w => ?_
  classical
  rw [count_ideleIdeal, ordAt_mulSingleAt, primeUnit, Units.val_mk0]
  split_ifs with h
  · subst h
    rw [FractionalIdeal.count_self, uniformizerUnit, Units.val_mk0, HN.valued_ϖ, log_exp, neg_neg]
  · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm h)]

/-- **$z\mapsto\mathfrak a(z)$ is surjective.** -/
theorem ideleIdeal_surjective : Function.Surjective (ideleIdeal F) := by
  intro I
  have hI : I = primeProd fun v => FractionalIdeal.count F v (I : FractionalIdeal (𝓞 F)⁰ F) :=
    fracIdeal_ext_count fun v => by
      rw [count_primeProd _ (FractionalIdeal.finite_factors (K := F) _)]
  have hmem : ∀ v, primeUnit v ∈ (ideleIdeal F).range := fun v =>
    ⟨_, ideleIdeal_mulSingleAt_uniformizer v⟩
  have : I ∈ (ideleIdeal F).range := by
    rw [hI, primeProd]
    exact finprod_induction (· ∈ (ideleIdeal F).range) (one_mem _) (fun _ _ => mul_mem)
      fun v => zpow_mem (hmem v) _
  exact this

/-! ### Principal ideles -/

/-- $F^\times\to\mathbb A_f^\times$. -/
abbrev finDiag : Fˣ →* AFˣ := Units.map (algebraMap F AF).toMonoidHom

theorem ordAt_finDiag (γ : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ordAt (finDiag γ) v =
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F)) := by
  have h : Valued.v (((finDiag γ : AFˣ) : AF) v) = v.valuation F (γ : F) :=
    HN.valued_algebraMap v (γ : F)
  rw [ordAt, h, Analysis.valuation_eq_exp_neg_count v γ.ne_zero, log_exp, neg_neg]

/-- **On principal ideles $z\mapsto\mathfrak a(z)$ is $\gamma\mapsto(\gamma)$.** -/
theorem ideleIdeal_finDiag (γ : Fˣ) : ideleIdeal F (finDiag γ) = toPrincipalIdeal (𝓞 F) F γ := by
  refine fracIdeal_ext_count fun v => ?_
  rw [count_ideleIdeal, ordAt_finDiag, coe_toPrincipalIdeal]

theorem finPart_diagUnits (γ : Fˣ) : finPart (diagUnits F γ) = finDiag γ := Units.ext rfl

theorem infPart_diagUnits_val (γ : Fˣ) :
    ((infPart (diagUnits F γ) : (mixedSpace F)ˣ) : mixedSpace F) = mixedEmbedding F (γ : F) := rfl

/-! ### Norms -/

theorem modAt_eq_zpow (z : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (modAt z v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordAt z v) := by
  have h := QuadFormsKB.WeilRep.modK_eq_norm v (Units.ne_zero (unitAt z v))
  rw [Analysis.Weil.modK_of_ne (Units.ne_zero (unitAt z v)), Units.mk0_val] at h
  rw [modAt, h, WeilRep.norm_eq_absNorm_pow v (Units.ne_zero _), unitAt_val, ordAt, neg_neg]

theorem idealNorm_primeProd (e : HeightOneSpectrum (𝓞 F) → ℤ) (he : {v | e v ≠ 0}.Finite) :
    IdeleClass.idealNorm F (primeProd e) = ∏ᶠ v, (Ideal.absNorm v.asIdeal : ℝ) ^ e v := by
  rw [IdeleClass.idealNorm, coe_primeProd e he]
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v :=
    he.subset fun v hv => by
      simp only [Function.mem_mulSupport, mem_ofPred_eq] at hv ⊢
      intro h0; exact hv (by rw [h0, zpow_zero])
  rw [show FractionalIdeal.absNorm (∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v) =
      (FractionalIdeal.absNorm : FractionalIdeal (𝓞 F)⁰ F →*₀ ℚ).toMonoidHom
        (∏ᶠ v, (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v) from rfl, MonoidHom.map_finprod _ hfin]
  have hfin' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((FractionalIdeal.absNorm : FractionalIdeal (𝓞 F)⁰ F →*₀ ℚ).toMonoidHom
        ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v)) :=
    he.subset fun v hv => by
      simp only [Function.mem_mulSupport, mem_ofPred_eq] at hv ⊢
      intro h0; exact hv (by rw [h0, zpow_zero, map_one])
  rw [show (((∏ᶠ v, (FractionalIdeal.absNorm : FractionalIdeal (𝓞 F)⁰ F →*₀ ℚ).toMonoidHom
      ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v)) : ℚ) : ℝ) =
      (Rat.castHom ℝ).toMonoidHom (∏ᶠ v, (FractionalIdeal.absNorm : FractionalIdeal (𝓞 F)⁰ F →*₀ ℚ).toMonoidHom
        ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ e v)) from rfl, MonoidHom.map_finprod _ hfin']
  refine finprod_congr fun v => ?_
  simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]

/-- **$\prod_v|z_v|_v = N(\mathfrak a(z))^{-1}$.** -/
theorem finprod_modAt_eq (z : AFˣ) :
    ∏ᶠ v, (modAt z v : ℝ) = (IdeleClass.idealNorm F (ideleIdeal F z))⁻¹ := by
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := fun v =>
    (zero_lt_one.trans (one_lt_absNorm v)).ne'
  have h1 : Function.HasFiniteMulSupport fun v => (modAt z v : ℝ) :=
    (finite_ordAt z).subset fun v hv => by
      simp only [Function.mem_mulSupport, mem_ofPred_eq] at hv ⊢
      intro h0; exact hv (by rw [modAt_eq_zpow, h0, neg_zero, zpow_zero])
  have h2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ ordAt z v :=
    (finite_ordAt z).subset fun v hv => by
      simp only [Function.mem_mulSupport, mem_ofPred_eq] at hv ⊢
      intro h0; exact hv (by rw [h0, zpow_zero])
  rw [← mul_eq_one_iff_eq_inv₀ (IdeleClass.idealNorm_pos F _).ne', ideleIdeal, MonoidHom.coe_mk, OneHom.coe_mk,
    idealNorm_primeProd _ (finite_ordAt z), ← finprod_mul_distrib h1 h2]
  rw [← finprod_one (α := HeightOneSpectrum (𝓞 F)) (M := ℝ)]
  refine finprod_congr fun v => ?_
  rw [modAt_eq_zpow, ← zpow_add₀ (hN v), neg_add_cancel, zpow_zero]

/-- **The idele norm in the ideal model**: $\|z\|_{\mathbb A} = N(z_\infty)/N(\mathfrak a(z_f))$, i.e. the
`IdeleClass.ideleNorm` of $(z_\infty,\mathfrak a(z_f))$. -/
theorem ideleNorm_eq_ideleClass (g : (Adeles F)ˣ) :
    ideleNorm F g = IdeleClass.ideleNorm F (infPart g : mixedSpace F) (ideleIdeal F (finPart g)) := by
  rw [ideleNorm, IdeleClass.ideleNorm, finprod_modAt_eq, IdeleClass.abs_det_mulLeft_mixedSpace, div_eq_mul_inv]

end

end QuadFormsKB.Tamagawa.Measure.Weil
