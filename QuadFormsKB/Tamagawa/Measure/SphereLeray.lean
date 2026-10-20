import QuadFormsKB.Tamagawa.Measure.LerayReal

/-!
# Leray measures on the spheres $\{Q = c\}$ at a real place, any signature

For a real quadratic form $Q$ in $n \ge 1$ variables (any signature, possibly degenerate here) and $c \ne 0$, let
$S_c = \{x \in \mathbb R^n : Q(x) = c\}$ (`Sph Q c`). The open cone $\{x : cQ(x) > 0\}$ (`posSet Q c`) is
$\mathbb R_{>0}\cdot S_c$, and the **polar map** $(t, x) \mapsto e^t x$, $\mathbb R \times S_c \to \mathbb R^n$ (`pol`), is a
measurable embedding onto it. We define

* the **cone measure** $\nu_c(A) = n\cdot\mathrm{Leb}\{e^tx : t \le 0,\ x \in A\}$ (`nu`), and
* the **Leray measure** $\sigma_c = \nu_c/(2|c|)$ (`sig`), Weil's $|dx/dQ|$ on $S_c$,

and prove:

* `comap_pol`: **polar coordinates**, $dx = e^{nt}\,dt \otimes \nu_c$ on $\mathbb R \times S_c$;
* `lintegral_posSet_fibration`: **the Leray fibration** $dx = \sigma_t \otimes dt$, in the form
  $\int_{cQ > 0} f\,dx = |c|\int_0^\infty u^{n/2-1}\int_{S_c} f(\sqrt u\,x)\,d\sigma_c(x)\,du$ (with $t = cu$ and
  $\sigma_t$ the transport of $u^{n/2-1}\sigma_c$ by $x \mapsto \sqrt u\,x$, this is $\int dt\int_{S_t} f\,d\sigma_t$);
* `map_sphAct_sig`: $\sigma_c$ is invariant under $SO(Q)(\mathbb R)$ (under every $g$ with $g^{\mathsf T}Ag = A$, $|\det g| = 1$);
* `sig_scale`: **homogeneity**, $\sigma_{a^2c} = a^{n-2}\,(x \mapsto ax)_*\sigma_c$ for $a > 0$.

No differential forms: the cone measure is defined by a volume, and the fibration is a change of variables.
-/

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Matrix Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.SphereLeray

open QuadFormsKB.Siegel Matrix

variable {n : ℕ}

/-! ### The sphere and the polar map -/

/-- **The sphere** $S_c = \{x \in \mathbb R^n : Q(x) = c\}$. -/
def sph (Q : QuadForm ℝ n) (c : ℝ) : Set (Fin n → ℝ) := {x | Q.eval x = c}

/-- $S_c$ as a type (closed subspace of $\mathbb R^n$, Borel structure). -/
abbrev Sph (Q : QuadForm ℝ n) (c : ℝ) : Type := ↥(sph Q c)

theorem isClosed_sph (Q : QuadForm ℝ n) (c : ℝ) : IsClosed (sph Q c) :=
  isClosed_eq (continuous_eval_real Q) continuous_const

instance (Q : QuadForm ℝ n) (c : ℝ) : PolishSpace (Sph Q c) := (isClosed_sph Q c).polishSpace

theorem measurableSet_sph (Q : QuadForm ℝ n) (c : ℝ) : MeasurableSet (sph Q c) :=
  (isClosed_sph Q c).measurableSet

/-- **The open cone** $\{x : cQ(x) > 0\} = \mathbb R_{>0}\cdot S_c$. -/
def posSet (Q : QuadForm ℝ n) (c : ℝ) : Set (Fin n → ℝ) := {x | 0 < c * Q.eval x}

theorem isOpen_posSet (Q : QuadForm ℝ n) (c : ℝ) : IsOpen (posSet Q c) :=
  isOpen_lt continuous_const (continuous_const.mul (continuous_eval_real Q))

/-- **The polar map** $(t, x) \mapsto e^tx$. -/
def pol (Q : QuadForm ℝ n) (c : ℝ) (p : ℝ × Sph Q c) : Fin n → ℝ := Real.exp p.1 • (p.2 : Fin n → ℝ)

theorem continuous_pol (Q : QuadForm ℝ n) (c : ℝ) : Continuous (pol Q c) :=
  (Real.continuous_exp.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd)

theorem eval_pol (Q : QuadForm ℝ n) (c : ℝ) (p : ℝ × Sph Q c) : Q.eval (pol Q c p) = Real.exp (2 * p.1) * c := by
  rw [pol, eval_smul_real, p.2.2, ← Real.exp_nat_mul]; norm_num

theorem pol_injective {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) : Function.Injective (pol Q c) := by
  rintro ⟨t, x⟩ ⟨t', x'⟩ h
  have h1 := congrArg Q.eval h
  rw [eval_pol, eval_pol] at h1
  have ht : t = t' := by
    have := mul_right_cancel₀ hc h1
    have := Real.exp_injective this
    linarith
  subst ht
  have : (x : Fin n → ℝ) = x' := by
    have h2 : Real.exp t • (x : Fin n → ℝ) = Real.exp t • (x' : Fin n → ℝ) := h
    exact smul_right_injective _ (Real.exp_pos t).ne' h2
  rw [Subtype.ext this]

theorem measurableEmbedding_pol {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) : MeasurableEmbedding (pol Q c) :=
  (continuous_pol Q c).measurableEmbedding (pol_injective hc)

theorem range_pol {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) : range (pol Q c) = posSet Q c := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    show 0 < c * Q.eval (pol Q c p)
    rw [eval_pol]
    have := Real.exp_pos (2 * p.1)
    have : 0 < c * c := mul_self_pos.mpr hc
    nlinarith
  · intro hy
    have hy' : 0 < c * Q.eval y := hy
    have hq : 0 < Q.eval y / c := by
      have : Q.eval y / c = c * Q.eval y / (c * c) := by field_simp
      rw [this]; exact div_pos hy' (mul_self_pos.mpr hc)
    set t := Real.log (Q.eval y / c) / 2
    have het : Real.exp (2 * t) = Q.eval y / c := by
      rw [show 2 * t = Real.log (Q.eval y / c) by simp only [t]; ring, Real.exp_log hq]
    have hx : Q.eval (Real.exp (-t) • y) = c := by
      rw [eval_smul_real, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * -t = -(2 * t) by push_cast; ring,
        Real.exp_neg, het]
      have hQy : Q.eval y ≠ 0 := by intro h; rw [h, mul_zero] at hy'; exact lt_irrefl _ hy'
      field_simp
    refine ⟨(t, ⟨_, hx⟩), ?_⟩
    simp only [pol, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-! ### The cone measure and the Leray measure -/

/-- **The cone measure** $\nu_c(A) = n\cdot\mathrm{Leb}\{e^tx : t \le 0,\ x \in A\}$ (`nu_apply`). -/
def nu (Q : QuadForm ℝ n) (c : ℝ) : Measure (Sph Q c) :=
  (n : ℝ≥0∞) • ((Measure.comap (pol Q c) volume).restrict (Iic 0 ×ˢ univ)).map Prod.snd

theorem nu_apply {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) {A : Set (Sph Q c)} (hA : MeasurableSet A) :
    nu Q c A = n * volume (pol Q c '' (Iic 0 ×ˢ A)) := by
  rw [nu, Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  congr 1
  rw [show Prod.snd ⁻¹' A ∩ Iic (0 : ℝ) ×ˢ (univ : Set (Sph Q c)) = Iic 0 ×ˢ A by
    ext p; simp [and_comm]]
  exact (measurableEmbedding_pol hc).comap_apply volume _

/-- **The Leray measure** $\sigma_c = \nu_c/(2|c|)$ on $S_c$ (Weil's $|dx/dQ|$, `lintegral_posSet_fibration`). -/
@[kb "weil1982" "§2.2 (gauge forms; the form dx/dQ on a level set) [unverified]"]
def sig (Q : QuadForm ℝ n) (c : ℝ) : Measure (Sph Q c) := ENNReal.ofReal (1 / (2 * |c|)) • nu Q c

theorem image_pol_Iic (Q : QuadForm ℝ n) (c a : ℝ) (A : Set (Sph Q c)) :
    pol Q c '' (Iic a ×ˢ A) = Real.exp a • pol Q c '' (Iic 0 ×ˢ A) := by
  ext y
  constructor
  · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    refine ⟨pol Q c (t - a, x), ⟨(t - a, x), ⟨?_, hx⟩, rfl⟩, ?_⟩
    · show t - a ≤ 0; have : t ≤ a := ht; linarith
    · simp only [pol, smul_smul, ← Real.exp_add, add_sub_cancel]
  · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
    refine ⟨(a + t, x), ⟨?_, hx⟩, ?_⟩
    · show a + t ≤ a; have : t ≤ 0 := ht; linarith
    · simp only [pol, smul_smul, ← Real.exp_add]

theorem volume_image_pol_Iic (Q : QuadForm ℝ n) (c a : ℝ) (A : Set (Sph Q c)) :
    volume (pol Q c '' (Iic a ×ˢ A)) = ENNReal.ofReal (Real.exp (n * a)) * volume (pol Q c '' (Iic 0 ×ˢ A)) := by
  rw [image_pol_Iic, addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos (Real.exp_pos a) n),
    ← Real.exp_nat_mul]

/-- The radial measure $e^{nt}\,dt$ on $\mathbb R$. -/
def rad (n : ℕ) : Measure ℝ := volume.withDensity fun t => ENNReal.ofReal (Real.exp (n * t))

theorem rad_Iic (hn : 1 ≤ n) (a : ℝ) : rad n (Iic a) = ENNReal.ofReal (Real.exp (n * a) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [rad, withDensity_apply _ measurableSet_Iic, ← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Iic hn' a) (Eventually.of_forall fun t => (Real.exp_pos _).le),
    integral_exp_mul_Iic hn']

instance (n : ℕ) : SigmaFinite (rad n) := by
  unfold rad; infer_instance

theorem volume_image_pol_bounded {Q : QuadForm ℝ n} {c : ℝ} {A : Set (Sph Q c)} {R : ℝ}
    (hR : ∀ x ∈ A, ‖(x : Fin n → ℝ)‖ ≤ R) : volume (pol Q c '' (Iic 0 ×ˢ A)) < ⊤ := by
  refine (measure_mono ?_).trans_lt (measure_closedBall_lt_top (x := (0 : Fin n → ℝ)) (r := R))
  rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, pol, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have h1 : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht
  have h2 := hR x hx
  calc Real.exp t * ‖(x : Fin n → ℝ)‖ ≤ 1 * ‖(x : Fin n → ℝ)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ R := by rw [one_mul]; exact h2

/-- **Polar coordinates**: $\mathrm{pol}^*(dx) = e^{nt}\,dt \otimes \nu_c$ ($n \ge 1$, $c \ne 0$). -/
theorem comap_pol {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) :
    Measure.comap (pol Q c) volume = (rad n).prod (nu Q c) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let D : Set (Set (Sph Q c)) := {A | MeasurableSet A ∧ ∃ R : ℝ, ∀ x ∈ A, ‖(x : Fin n → ℝ)‖ ≤ R}
  let Bk : ℕ → Set (Sph Q c) := fun k => {x | ‖(x : Fin n → ℝ)‖ ≤ k}
  have hBk : ∀ k, MeasurableSet (Bk k) := fun k =>
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  have hBkU : (⋃ k, Bk k) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
    obtain ⟨k, hk⟩ := exists_nat_ge ‖(x : Fin n → ℝ)‖
    exact ⟨k, hk⟩
  refine (Measure.prod_eq_generateFrom (C := range Iic) (D := D) (borel_eq_generateFrom_Iic ℝ).symm ?_ isPiSystem_Iic ?_
    ?_ ?_ ?_).symm
  · refine le_antisymm (MeasurableSpace.generateFrom_le fun A hA => hA.1) fun A hA => ?_
    have : A = ⋃ k, A ∩ Bk k := by rw [← inter_iUnion, hBkU, inter_univ]
    rw [this]
    exact MeasurableSet.iUnion fun k => MeasurableSpace.measurableSet_generateFrom
      ⟨hA.inter (hBk k), k, fun x hx => hx.2⟩
  · rintro A ⟨hA, R, hR⟩ B ⟨hB, R', hR'⟩ _
    exact ⟨hA.inter hB, R, fun x hx => hR x hx.1⟩
  · refine ⟨fun k => Iic (k : ℝ), fun k => ⟨k, rfl⟩, fun k => ?_, ?_⟩
    · rw [rad_Iic hn]; exact ENNReal.ofReal_lt_top
    · refine eq_univ_of_forall fun t => mem_iUnion.mpr ?_
      obtain ⟨k, hk⟩ := exists_nat_ge t
      exact ⟨k, hk⟩
  · refine ⟨Bk, fun k => ⟨hBk k, k, fun x hx => hx⟩, fun k => ?_, hBkU⟩
    rw [nu_apply hc (hBk k)]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (volume_image_pol_bounded (R := k) fun x hx => hx)
  · rintro _ ⟨a, rfl⟩ A ⟨hA, R, hR⟩
    rw [(measurableEmbedding_pol hc).comap_apply volume, volume_image_pol_Iic, rad_Iic hn, nu_apply hc hA,
      ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hn'.le),
      div_mul_cancel₀ _ hn'.ne']

theorem nu_bounded_lt_top {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (k : ℝ) :
    nu Q c {x | ‖(x : Fin n → ℝ)‖ ≤ k} < ⊤ := by
  have hmeas : MeasurableSet {x : Sph Q c | ‖(x : Fin n → ℝ)‖ ≤ k} :=
    measurableSet_le (continuous_norm.comp continuous_subtype_val).measurable measurable_const
  rw [nu_apply hc hmeas]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top n) (volume_image_pol_bounded (R := k) fun x hx => hx)

theorem sigmaFinite_nu {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) : SigmaFinite (nu Q c) := by
  let Bk : ℕ → Set (Sph Q c) := fun k => {x | ‖(x : Fin n → ℝ)‖ ≤ k}
  refine ⟨⟨⟨Bk, fun _ => mem_univ _, fun k => nu_bounded_lt_top hc k, ?_⟩⟩⟩
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  obtain ⟨k, hk⟩ := exists_nat_ge ‖(x : Fin n → ℝ)‖
  exact ⟨k, hk⟩

theorem sigmaFinite_sig {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) : SigmaFinite (sig Q c) := by
  have := sigmaFinite_nu (Q := Q) hc
  have e : sig Q c = (Real.toNNReal (1 / (2 * |c|))) • nu Q c := by
    ext s _; simp [sig, ENNReal.ofReal]
  rw [e]; infer_instance

/-- **Integration in polar coordinates**: for $f \ge 0$ measurable,
$\int_{cQ>0} f\,dx = \int_{\mathbb R} e^{nt}\int_{S_c} f(e^tx)\,d\nu_c(x)\,dt$. -/
theorem lintegral_posSet_pol {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y in posSet Q c, f y = ∫⁻ t, ENNReal.ofReal (Real.exp (n * t)) * ∫⁻ x, f (Real.exp t • (x : Fin n → ℝ)) ∂nu Q c := by
  have hm : Measurable fun p => f (pol Q c p) := hf.comp (continuous_pol Q c).measurable
  have := sigmaFinite_nu (Q := Q) hc
  rw [← range_pol hc, ← (measurableEmbedding_pol hc).map_comap, lintegral_map hf (continuous_pol Q c).measurable,
    comap_pol hc hn, lintegral_prod (fun p => f (pol Q c p)) hm.aemeasurable, rad,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm.lintegral_prod_right']
  rfl

/-! ### The Leray fibration $dx = \sigma_t \otimes dt$ -/

/-- **The Leray fibration** ($n \ge 1$, $c \ne 0$): for $f \ge 0$ measurable,
$$\int_{cQ>0} f\,dx = |c|\int_0^\infty u^{n/2-1}\int_{S_c} f(\sqrt u\,x)\,d\sigma_c(x)\,du.$$
With $t = cu$ ($dt = |c|\,du$) and $\sigma_t := u^{n/2-1}(x \mapsto \sqrt u\,x)_*\sigma_c$ (`sig_scale`), this is
$dx = \sigma_t \otimes dt$, i.e. $\sigma_c$ is the Leray measure $dx/dQ$ on $S_c$. -/
@[kb "weil1982" "§2.2 (gauge forms; dx = ω_c ∧ dQ on the fibres of Q) [unverified]"]
theorem lintegral_posSet_fibration {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (hn : 1 ≤ n)
    {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in posSet Q c, f y =
      ∫⁻ u in Ioi 0, ENNReal.ofReal (|c| * u ^ ((n : ℝ) / 2 - 1)) *
        ∫⁻ x, f (Real.sqrt u • (x : Fin n → ℝ)) ∂sig Q c := by
  rw [lintegral_posSet_pol hc hn hf]
  have himg : (fun t : ℝ => Real.exp (2 * t)) '' univ = Ioi 0 := by
    rw [image_univ]
    ext u
    constructor
    · rintro ⟨t, rfl⟩; exact Real.exp_pos _
    · intro hu
      exact ⟨Real.log u / 2, by simp only; rw [show 2 * (Real.log u / 2) = Real.log u by ring,
        Real.exp_log hu]⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f' := fun t => 2 * Real.exp (2 * t))
    (fun t _ => by
      have h : HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * (2 * 1)) t :=
        ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
      convert h.hasDerivWithinAt using 1; ring)
    (fun t _ t' _ h => by
      have := Real.exp_injective h
      linarith), Measure.restrict_univ]
  refine lintegral_congr fun t => ?_
  have hsq : Real.sqrt (Real.exp (2 * t)) = Real.exp t := by
    rw [show 2 * t = t + t by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos t).le]
  have hrp : Real.exp (2 * t) ^ ((n : ℝ) / 2 - 1) = Real.exp ((n - 2) * t) := by
    rw [← Real.exp_mul]; congr 1; ring
  simp only [hsq, sig, lintegral_smul_measure, hrp]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (2 * t)), smul_eq_mul, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hc' : 0 < |c| := abs_pos.mpr hc
  rw [show (n : ℝ) * t = 2 * t + (n - 2) * t by ring, Real.exp_add]
  field_simp

/-! ### Invariance under $SO(Q)$ -/

theorem eval_mulVec_of_isometry (Q : QuadForm ℝ n) {g : Matrix (Fin n) (Fin n) ℝ}
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) (x : Fin n → ℝ) : Q.eval (g *ᵥ x) = Q.eval x := by
  rw [eval_real_eq_gramR, eval_real_eq_gramR]
  conv_rhs => rw [← hg]
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x gᵀ, vecMul_transpose]

/-- **The action of an isometry on $S_c$**: $x \mapsto gx$. -/
def sphMap (Q : QuadForm ℝ n) (c : ℝ) (g : Matrix (Fin n) (Fin n) ℝ)
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) (x : Sph Q c) : Sph Q c :=
  ⟨g *ᵥ (x : Fin n → ℝ), by
    show Q.eval _ = c; rw [eval_mulVec_of_isometry Q hg]; exact x.2⟩

theorem continuous_sphMap (Q : QuadForm ℝ n) (c : ℝ) (g : Matrix (Fin n) (Fin n) ℝ)
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) : Continuous (sphMap Q c g hg) :=
  ((Matrix.toLin' g).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

/-- **Invariance of the cone measure** under every isometry $g$ with $|\det g| = 1$. -/
theorem map_sphMap_nu {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (g : Matrix (Fin n) (Fin n) ℝ)
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) (hdet : |g.det| = 1) :
    (nu Q c).map (sphMap Q c g hg) = nu Q c := by
  ext A hA
  have hm := (continuous_sphMap Q c g hg).measurable
  rw [Measure.map_apply hm hA, nu_apply hc (hm hA), nu_apply hc hA]
  congr 1
  have h0 : g.det ≠ 0 := by intro h; rw [h, abs_zero] at hdet; exact zero_ne_one hdet
  have himg : Matrix.toLin' g '' (pol Q c '' (Iic 0 ×ˢ (sphMap Q c g hg ⁻¹' A))) = pol Q c '' (Iic 0 ×ˢ A) := by
    ext y
    constructor
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      exact ⟨(t, sphMap Q c g hg x), ⟨ht, hx⟩, by simp [pol, sphMap]⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.mpr h0)
      have hig : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.mpr h0)
      have hgi' : (g⁻¹)ᵀ * gramMatrixR Q * g⁻¹ = gramMatrixR Q := by
        have : (g⁻¹)ᵀ * (gᵀ * gramMatrixR Q * g) * g⁻¹ = gramMatrixR Q := by
          rw [show (g⁻¹)ᵀ * (gᵀ * gramMatrixR Q * g) * g⁻¹ = (g * g⁻¹)ᵀ * gramMatrixR Q * (g * g⁻¹) by
            rw [transpose_mul]; simp only [Matrix.mul_assoc], hgi, transpose_one, Matrix.one_mul, Matrix.mul_one]
        rwa [hg] at this
      refine ⟨pol Q c (t, sphMap Q c g⁻¹ hgi' x), ⟨(t, sphMap Q c g⁻¹ hgi' x), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show sphMap Q c g hg (sphMap Q c g⁻¹ hgi' x) ∈ A
        have : sphMap Q c g hg (sphMap Q c g⁻¹ hgi' x) = x := by
          apply Subtype.ext; simp [sphMap, mulVec_mulVec, hgi]
        rw [this]; exact hx
      · simp [pol, sphMap, mulVec_mulVec, hgi]
  rw [← himg, addHaar_image_linearMap, LinearMap.det_toLin', hdet, ENNReal.ofReal_one, one_mul]

/-- **$\sigma_c$ is $SO(Q)(\mathbb R)$-invariant** (more generally invariant under isometries with $|\det| = 1$). -/
@[kb "weil1982" "§2.2 (invariant gauge form on a homogeneous space) [unverified]"]
theorem map_sphMap_sig {Q : QuadForm ℝ n} {c : ℝ} (hc : c ≠ 0) (g : Matrix (Fin n) (Fin n) ℝ)
    (hg : gᵀ * gramMatrixR Q * g = gramMatrixR Q) (hdet : |g.det| = 1) :
    (sig Q c).map (sphMap Q c g hg) = sig Q c := by
  rw [sig, Measure.map_smul, map_sphMap_nu hc g hg hdet]
  exact (continuous_sphMap Q c g hg).measurable.aemeasurable

/-! ### Homogeneity -/

/-- The scaling $S_c \to S_{a^2c}$, $x \mapsto ax$. -/
def sphScale (Q : QuadForm ℝ n) (c a : ℝ) (x : Sph Q c) : Sph Q (a ^ 2 * c) :=
  ⟨a • (x : Fin n → ℝ), by show Q.eval _ = _; rw [eval_smul_real, x.2]⟩

theorem continuous_sphScale (Q : QuadForm ℝ n) (c a : ℝ) : Continuous (sphScale Q c a) :=
  Continuous.subtype_mk (by fun_prop : Continuous fun x : Sph Q c => a • (x : Fin n → ℝ)) _

theorem nu_scale {Q : QuadForm ℝ n} {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a) :
    nu Q (a ^ 2 * c) = ENNReal.ofReal (a ^ n) • (nu Q c).map (sphScale Q c a) := by
  have hc' : a ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero _ ha.ne') hc
  ext A hA
  have hm := (continuous_sphScale Q c a).measurable
  rw [Measure.smul_apply, Measure.map_apply hm hA, nu_apply hc' hA, nu_apply hc (hm hA), smul_eq_mul,
    mul_left_comm]
  congr 1
  have himg : pol Q (a ^ 2 * c) '' (Iic 0 ×ˢ A) = a • pol Q c '' (Iic 0 ×ˢ (sphScale Q c a ⁻¹' A)) := by
    ext y
    constructor
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      have hx' : Q.eval (a⁻¹ • (x : Fin n → ℝ)) = c := by
        rw [eval_smul_real, x.2, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
      refine ⟨pol Q c (t, ⟨_, hx'⟩), ⟨(t, ⟨_, hx'⟩), ⟨ht, ?_⟩, rfl⟩, ?_⟩
      · show sphScale Q c a ⟨_, hx'⟩ ∈ A
        have : sphScale Q c a ⟨_, hx'⟩ = x := by
          apply Subtype.ext; simp [sphScale, smul_smul, mul_inv_cancel₀ ha.ne']
        rw [this]; exact hx
      · simp only [pol, smul_smul]
        rw [mul_comm a, mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]
    · rintro ⟨_, ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, rfl⟩
      exact ⟨(t, sphScale Q c a x), ⟨ht, hx⟩, by simp only [pol, sphScale, smul_smul, mul_comm]⟩
  rw [himg, addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos ha n)]

/-- **Homogeneity of the Leray measure**: $\sigma_{a^2c} = a^{n-2}\,(x \mapsto ax)_*\sigma_c$ for $a > 0$ (with $t = a^2$:
the factor $|t|^{n/2-1}$). -/
@[kb "weil1982" "§2.2 (gauge forms; homogeneity of dx/dQ) [unverified]"]
theorem sig_scale {Q : QuadForm ℝ n} {c a : ℝ} (hc : c ≠ 0) (ha : 0 < a) (hn : 2 ≤ n) :
    sig Q (a ^ 2 * c) = ENNReal.ofReal (a ^ (n - 2)) • (sig Q c).map (sphScale Q c a) := by
  rw [sig, sig, nu_scale hc ha, Measure.map_smul, smul_smul, smul_smul, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  swap; · exact (continuous_sphScale Q c a).measurable.aemeasurable
  congr 2
  have hc' : 0 < |c| := abs_pos.mpr hc
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < a ^ 2)]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + k - 2 = k by omega, pow_add]
  field_simp

end QuadFormsKB.Tamagawa.Measure.SphereLeray
