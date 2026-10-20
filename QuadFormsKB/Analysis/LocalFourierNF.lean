import QuadFormsKB.Analysis.LocalFourier
import QuadFormsKB.Literature.HasseNorm.SquareClasses

/-!
# The standard character of a completion $F_v$ of a number field

For a number field $F$ and a finite place $v$ (a height-one prime of $\mathcal O_F$), with completion
$F_v$ = `v.adicCompletion F` and residue characteristic $p$:

* `padicToV`: the continuous embedding $\mathbb{Q}_p \hookrightarrow F_v$ (Mathlib's `padicEquiv` $\mathbb{Q}_p \cong \mathbb{Q}_{(p)}$
  followed by the map of completions induced by $\mathbb{Q} \subset F$), making $F_v$ a $\mathbb{Q}_p$-algebra;
* `finiteDimensional_padic`: $[F_v : \mathbb{Q}_p] < \infty$ (the $\mathbb{Q}_p$-span of a $\mathbb{Q}$-basis of $F$ is closed and
  contains the dense subfield $F$);
* `traceV`: the local trace $\operatorname{Tr}_{F_v/\mathbb{Q}_p}$, continuous;
* `psiV`: the standard character $\psi_v(x) = \psi_p(\operatorname{Tr}_{F_v/\mathbb{Q}_p} x)$, a continuous additive character
  $F_v \to \mathbb{C}^1$ (`continuous_psiV`);
* `psiV_eq_one_of_le_one`: $\psi_v$ is trivial on $\mathcal O_v$ (because $\operatorname{Tr}(\mathcal O_v) \subseteq \mathbb{Z}_p$,
  `traceV_mem_of_le_one`);
* `psiV_nontrivial`: $\psi_v\big((np)^{-1}\big) = e(-1/p) \ne 1$ for $n = [F_v : \mathbb{Q}_p]$;
* `invDiffV`, `exists_diffExp`, `diffExp`: the conductor of $\psi_v$, i.e. the local inverse different
  $\mathfrak d_v^{-1} = \{y : \psi_v(y\mathcal O_v) = 1\}$, is $\mathfrak p_v^{-d_v}$ with $d_v \ge 0$;
  `annihV_latticeV`: $(\mathfrak p_v^k)^\perp = \mathfrak p_v^{-k-d_v}$;
* `haarV` ($\operatorname{vol}(\mathcal O_v) = 1$), `haarV_real_latticeV`: $\operatorname{vol}(\mathfrak p_v^k) = \Delta_v^k$ with
  $\Delta_v$ = `modV` the modulus of a uniformizer, and `modV_eq`: $\Delta_v = N(v)^{-1}$;
* `selfDualV`: the self-dual measure, `selfDualV_real_mul`: $\operatorname{vol}(L)\operatorname{vol}(L^\perp) = 1$,
  `selfDualV_real_Ov`: $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$, $N(\mathfrak d_v) = N(v)^{d_v}$;
* `fourierV`, `fourierV_ballIndV`: $\widehat{\mathbf 1_{c+\mathfrak p_v^k}}(y) =
  \operatorname{vol}(\mathfrak p_v^k)\psi_v(cy)\mathbf 1_{\mathfrak p_v^{-k-d_v}}(y)$; `fourierInvV_fourierV_of_isSchwartzBruhat`:
  Fourier inversion for Schwartz–Bruhat functions on $F_v$.

Not done: identifying $\mathfrak p_v^{d_v}$ with Mathlib's `differentIdeal` (or with the global different);
complex places.

Sources: Tate's thesis, Cassels–Fröhlich Ch. XV §2.2 [unverified]; Weil, *Basic Number Theory*, Ch. VIII §4
(the different and the standard character) [unverified].
-/

open IsDedekindDomain NumberField WithZero
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- The prime $(p) = v \cap \mathbb{Z}$ of $\mathbb{Z}$ under $v$. -/
def vUnder : HeightOneSpectrum ℤ where
  asIdeal := v.asIdeal.comap (algebraMap ℤ (𝓞 F))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.IsIntegral.under_ne_bot ℤ v.ne_bot

instance : v.asIdeal.LiesOver (vUnder v).asIdeal := ⟨rfl⟩

/-- The residue characteristic $p$ of $v$. -/
def resChar : ℕ := (Rat.HeightOneSpectrum.primesEquiv (vUnder v) : ℕ)

instance : Fact (resChar v).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv (vUnder v)).2⟩

/-- The map of completions $\mathbb{Q}_{(p)} \to F_v$ induced by $\mathbb{Q} \subset F$. -/
def compQ : (vUnder v).adicCompletion ℚ →+* Fv :=
  (HeightOneSpectrum.adicCompletion.equiv F v).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((vUnder v).valuation ℚ)) (WithVal (v.valuation F)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver ℚ F (vUnder v) v).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv ℚ (vUnder v)).toRingHom)

lemma continuous_compQ : Continuous (compQ v) := by
  unfold compQ
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion F v).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion ℚ (vUnder v)))

/-- **The embedding $\mathbb{Q}_p \hookrightarrow F_v$** ($p$ = `resChar v`). -/
def padicToV : ℚ_[resChar v] →+* Fv :=
  (compQ v).comp
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vUnder v)).symm.toAlgEquiv.toRingHom

lemma continuous_padicToV : Continuous (padicToV v) :=
  (continuous_compQ v).comp
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (vUnder v)).symm.continuous

/-- $F_v$ as a $\mathbb{Q}_p$-algebra, via `padicToV`. -/
instance algebraPadic : Algebra ℚ_[resChar v] Fv := (padicToV v).toAlgebra

lemma algebraMap_padic_eq : algebraMap ℚ_[resChar v] Fv = padicToV v := rfl

instance : IsScalarTower ℚ ℚ_[resChar v] Fv := IsScalarTower.of_algebraMap_eq fun c =>
  DFunLike.congr_fun (RingHom.ext_rat (algebraMap ℚ Fv)
    ((algebraMap ℚ_[resChar v] Fv).comp (algebraMap ℚ ℚ_[resChar v]))) c

instance : ContinuousSMul ℚ_[resChar v] Fv := by
  refine ⟨?_⟩
  simp_rw [Algebra.smul_def, algebraMap_padic_eq]
  exact ((continuous_padicToV v).comp continuous_fst).mul continuous_snd

/-- **$F_v$ is finite-dimensional over $\mathbb{Q}_p$:** the $\mathbb{Q}_p$-span of a $\mathbb{Q}$-basis of $F$ is finite-dimensional,
hence closed, and it contains the dense subfield $F$. -/
instance finiteDimensional_padic : FiniteDimensional ℚ_[resChar v] Fv := by
  let b := Module.finBasis ℚ F
  let w : Fin (Module.finrank ℚ F) → Fv := fun i => algebraMap F Fv (b i)
  let S := Submodule.span ℚ_[resChar v] (Set.range w)
  have : FiniteDimensional ℚ_[resChar v] S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hS : IsClosed (S : Set Fv) := S.closed_of_finiteDimensional
  have hsub : Set.range (algebraMap F Fv) ⊆ S := by
    rintro _ ⟨a, rfl⟩
    rw [← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_rat_smul, ← algebraMap_smul ℚ_[resChar v]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have htop : S = ⊤ := by
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    exact hS.closure_subset_iff.mpr hsub (HeightOneSpectrum.denseRange_algebraMap F v x)
  exact ⟨htop ▸ Submodule.fg_span (Set.finite_range w)⟩

/-- **The local trace** $\operatorname{Tr}_{F_v/\mathbb{Q}_p} : F_v \to \mathbb{Q}_p$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def traceV : Fv →ₗ[ℚ_[resChar v]] ℚ_[resChar v] := Algebra.trace ℚ_[resChar v] Fv

lemma continuous_traceV : Continuous (traceV v) := LinearMap.continuous_of_finiteDimensional _

/-- **The standard character of $F_v$:** $\psi_v(x) = \psi_p(\operatorname{Tr}_{F_v/\mathbb{Q}_p} x)
= e\big(-\{\operatorname{Tr}_{F_v/\mathbb{Q}_p} x\}_p\big)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, $\\psi_v = \\psi_p \\circ \\mathrm{Tr}$ [unverified]"]
def psiV : AddChar Fv Circle := (psiP (p := resChar v)).compAddMonoidHom (traceV v).toAddMonoidHom

lemma psiV_apply (x : Fv) : psiV v x = psiP (traceV v x) := rfl

/-- **$\psi_v$ is continuous.** -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem continuous_psiV : Continuous (psiV v) := continuous_psiP.comp (continuous_traceV v)

/-- **$\psi_v$ is nontrivial:** with $n = [F_v : \mathbb{Q}_p]$, $\operatorname{Tr}\big((np)^{-1}\big) = p^{-1}$, so
$\psi_v\big((np)^{-1}\big) = \psi_p(p^{-1}) = e(-1/p) \ne 1$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem psiV_nontrivial :
    psiV v (algebraMap ℚ_[resChar v] Fv
      (((Module.finrank ℚ_[resChar v] Fv : ℚ_[resChar v]) * (resChar v : ℚ_[resChar v]))⁻¹)) ≠ 1 := by
  have hn : (Module.finrank ℚ_[resChar v] Fv : ℚ_[resChar v]) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have htr : traceV v (algebraMap ℚ_[resChar v] Fv
      (((Module.finrank ℚ_[resChar v] Fv : ℚ_[resChar v]) * (resChar v : ℚ_[resChar v]))⁻¹)) =
      (resChar v : ℚ_[resChar v])⁻¹ := by
    rw [traceV, Algebra.trace_algebraMap, nsmul_eq_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hn,
      one_mul]
  rw [psiV_apply, htr]
  exact psiP_inv_p.2

/-! ### $\psi_v$ is trivial on $\mathcal O_v$ -/

/-- For $a \in \mathcal O_F$, $\operatorname{Tr}_{F_v/\mathbb{Q}_p}(a) \in \mathbb{Z}_p$: it is integral over $\mathbb{Z}$, and $\mathbb{Z}_p$ is
integrally closed. -/
lemma norm_traceV_algebraMap_int_le_one (a : 𝓞 F) : ‖traceV v (algebraMap F Fv (a : F))‖ ≤ 1 := by
  have hint : IsIntegral ℤ (algebraMap F Fv (a : F)) :=
    (RingOfIntegers.isIntegral_coe a).algebraMap
  have h1 : IsIntegral ℤ (traceV v (algebraMap F Fv (a : F))) := Algebra.isIntegral_trace hint
  have h2 : IsIntegral ℤ_[resChar v] (traceV v (algebraMap F Fv (a : F))) := h1.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hz]
  exact z.norm_le_one

/-- **Approximation of $\mathcal O_v$ by $\mathcal O_F$:** for $x \in F_v$ with $v(x) \le 1$ and $N \in \mathbb{N}$ there is
$a \in \mathcal O_F$ with $v(x - a) \le \exp(-N)$. -/
lemma exists_int_approx_pow (N : ℕ) : ∀ x : Fv, Valued.v x ≤ 1 →
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F Fv (a : F)) ≤ exp (-(N : ℤ)) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.intValuation_exists_uniformizer v
  have hπv : Valued.v (algebraMap F Fv (π : F)) = exp (-1 : ℤ) := by
    rw [HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hπ0 : algebraMap F Fv (π : F) ≠ 0 := by
    intro h; rw [h, map_zero] at hπv; exact WithZero.zero_ne_coe hπv
  induction N with
  | zero => intro x hx; exact ⟨0, by simpa using hx⟩
  | succ N ih =>
    intro x hx
    obtain ⟨a₀, ha₀⟩ := HN.exists_int_approx v ⟨x, hx⟩
    have ha₀' : Valued.v (x - algebraMap F Fv (a₀ : F)) ≤ exp (-1 : ℤ) := by
      refine HN.valued_le_exp_neg_one v ?_
      convert ha₀ using 3
      rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        HeightOneSpectrum.algebraMap_adicCompletion (𝓞 F)]
      rfl
    set x₁ := (x - algebraMap F Fv (a₀ : F)) / algebraMap F Fv (π : F) with hx₁
    have hx₁v : Valued.v x₁ ≤ 1 := by
      rw [hx₁, map_div₀, hπv, div_le_iff₀ (by simp)]
      simpa using ha₀'
    obtain ⟨a₁, ha₁⟩ := ih x₁ hx₁v
    refine ⟨a₀ + π * a₁, ?_⟩
    have e : x - algebraMap F Fv ((a₀ + π * a₁ : 𝓞 F) : F) =
        algebraMap F Fv (π : F) * (x₁ - algebraMap F Fv (a₁ : F)) := by
      have hc : ((a₀ + π * a₁ : 𝓞 F) : F) = (a₀ : F) + (π : F) * (a₁ : F) := rfl
      rw [hx₁, hc, map_add, map_mul]; field_simp; ring
    rw [e, map_mul, hπv]
    calc exp (-1 : ℤ) * Valued.v (x₁ - algebraMap F Fv (a₁ : F)) ≤ exp (-1 : ℤ) * exp (-(N : ℤ)) :=
          mul_le_mul_right ha₁ _
      _ = exp (-((N + 1 : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring

lemma norm_ϖ_lt_one : ‖HN.ϖ v‖ < 1 := by
  rw [← norm_one (α := Fv)]
  refine (Valued.toNormedField.norm_lt_iff).mpr ?_
  rw [HN.valued_ϖ, map_one]
  exact exp_lt_one_iff.mpr (by norm_num)

/-- The trace is $\mathbb{Z}_p$-valued on a small enough ball $\{v(x) \le \exp(-N)\}$ (continuity at $0$). -/
lemma exists_traceV_small : ∃ N : ℕ, ∀ x : Fv, Valued.v x ≤ exp (-(N : ℤ)) → ‖traceV v x‖ ≤ 1 := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp ((continuous_traceV v).continuousAt (x := 0)) 1
    one_pos
  have hϖ1 := norm_ϖ_lt_one v
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hϖ1
  refine ⟨n + 1, fun x hx => ?_⟩
  have hxn : ‖x‖ < ‖HN.ϖ v ^ n‖ := by
    refine (Valued.toNormedField.norm_lt_iff).mpr ?_
    rw [HN.valued_ϖ_pow]
    exact hx.trans_lt (exp_lt_exp.mpr (by push_cast; omega))
  have := hδ' (x := x) (by rw [dist_zero_right]; exact hxn.trans (by rw [norm_pow]; exact hn))
  rw [map_zero, dist_zero_right] at this
  exact this.le

/-- **$\operatorname{Tr}_{F_v/\mathbb{Q}_p}(\mathcal O_v) \subseteq \mathbb{Z}_p$.** Proof: approximate $x \in \mathcal O_v$ by $a \in \mathcal O_F$
(`exists_int_approx_pow`); $\operatorname{Tr}(a) \in \mathbb{Z}_p$ by integrality, and $\operatorname{Tr}(x - a) \in \mathbb{Z}_p$ by continuity
(`exists_traceV_small`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem norm_traceV_le_one {x : Fv} (hx : Valued.v x ≤ 1) : ‖traceV v x‖ ≤ 1 := by
  obtain ⟨N, hN⟩ := exists_traceV_small v
  obtain ⟨a, ha⟩ := exists_int_approx_pow v N x hx
  have : traceV v x = traceV v (algebraMap F Fv (a : F)) + traceV v (x - algebraMap F Fv (a : F)) := by
    rw [← map_add, add_sub_cancel]
  rw [this]
  exact (Padic.nonarchimedean _ _).trans
    (max_le (norm_traceV_algebraMap_int_le_one v a) (hN _ ha))

/-- **$\psi_v$ is trivial on $\mathcal O_v$** (the conductor of $\psi_v$, the inverse different, contains $\mathcal O_v$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem psiV_eq_one_of_le_one {x : Fv} (hx : Valued.v x ≤ 1) : psiV v x = 1 := by
  rw [psiV_apply, psiP_eq_one_iff]
  exact norm_traceV_le_one v hx

/-! ### The conductor of $\psi_v$: the local inverse different -/

/-- $v(\varpi^k) = \exp(-k)$ for $k \in \mathbb{Z}$, where $\varpi$ = `HN.ϖ v` is a uniformizer. -/
lemma valued_ϖ_zpow (k : ℤ) : Valued.v (HN.ϖ v ^ k) = exp (-k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, HN.valued_ϖ_pow]
  · rw [zpow_neg, zpow_natCast, map_inv₀, HN.valued_ϖ_pow, neg_neg, ← exp_neg, neg_neg]

/-- **The local inverse different**, defined by duality as the annihilator of $\mathcal O_v$ under $\psi_v$:
$$\mathfrak d_v^{-1} = \{y \in F_v : \psi_v(xy) = 1 \text{ for all } x \in \mathcal O_v\}.$$
`exists_diffExp` shows it is $\mathfrak p_v^{-d_v}$ for a unique $d_v \ge 0$ (`diffExp`), the exponent of the different
$\mathfrak d_{F_v/\mathbb{Q}_p}$. (Identifying $\mathfrak d_v$ with Mathlib's `differentIdeal` is not done here.) -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Lemma 2.2.1 (conductor of $\\psi_v$ = inverse different) [unverified]"]
def invDiffV : Set Fv := {y | ∀ x : Fv, Valued.v x ≤ 1 → psiV v (x * y) = 1}

lemma one_mem_invDiffV : (1 : Fv) ∈ invDiffV v := fun x hx => by
  rw [mul_one]; exact psiV_eq_one_of_le_one v hx

/-- $\mathfrak d_v^{-1}$ is an $\mathcal O_v$-module: it is closed under $y \mapsto y'$ whenever $v(y') \le v(y)$. -/
lemma mem_invDiffV_of_le {y y' : Fv} (hy : y ∈ invDiffV v) (h : Valued.v y' ≤ Valued.v y) :
    y' ∈ invDiffV v := by
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, le_zero_iff, Valuation.zero_iff] at h
    intro x _; rw [h, mul_zero, AddChar.map_zero_eq_one]
  intro x hx
  have hu : Valued.v (x * (y' / y)) ≤ 1 := by
    rw [map_mul, map_div₀]
    calc Valued.v x * (Valued.v y' / Valued.v y) ≤ 1 * 1 := by
          gcongr
          exact div_le_one_of_le₀ h zero_le
      _ = 1 := one_mul 1
  have := hy _ hu
  rwa [mul_assoc, div_mul_cancel₀ _ hy0] at this

/-- The element $x_0 = (np)^{-1}$ of `psiV_nontrivial`. -/
def x₀ : Fv := algebraMap ℚ_[resChar v] Fv
  (((Module.finrank ℚ_[resChar v] Fv : ℚ_[resChar v]) * (resChar v : ℚ_[resChar v]))⁻¹)

lemma x₀_ne_zero : x₀ v ≠ 0 := by
  intro h
  have := psiV_nontrivial v
  rw [← x₀, h, AddChar.map_zero_eq_one] at this
  exact this rfl

/-- $\mathfrak d_v^{-1}$ is bounded: $v(y) < v(x_0)$ for $y \in \mathfrak d_v^{-1}$. -/
lemma valued_lt_of_mem_invDiffV {y : Fv} (hy : y ∈ invDiffV v) : Valued.v y < Valued.v (x₀ v) := by
  by_contra h
  push Not at h
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h; exact x₀_ne_zero v h
  have hx : Valued.v (x₀ v / y) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ h zero_le
  have := hy _ hx
  rw [div_mul_cancel₀ _ hy0] at this
  exact psiV_nontrivial v this

/-- **The conductor of $\psi_v$ is $\mathfrak p_v^{-d}$:** there is $d \in \mathbb{N}$ with
$\mathfrak d_v^{-1} = \{y : v(y) \le \exp(d)\}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Lemma 2.2.1 [unverified]"]
theorem exists_diffExp : ∃ d : ℕ, ∀ y : Fv, y ∈ invDiffV v ↔ Valued.v y ≤ exp (d : ℤ) := by
  let P : ℕ → Prop := fun m => ∀ y : Fv, Valued.v y ≤ exp (m : ℤ) → y ∈ invDiffV v
  have hex : ∃ m, ¬ P (m + 1) := by
    obtain ⟨k₀, hk₀⟩ := HN.exists_exp_eq v (x₀_ne_zero v)
    refine ⟨k₀.toNat, fun hP => ?_⟩
    have := valued_lt_of_mem_invDiffV v (hP (x₀ v) (by rw [hk₀, exp_le_exp]; push_cast; omega))
    exact lt_irrefl _ this
  classical
  refine ⟨Nat.find hex, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · by_contra h
    push Not at h
    have hy0 : y ≠ 0 := by intro h0; rw [h0, map_zero] at h; exact not_lt_zero h
    obtain ⟨k, hk⟩ := HN.exists_exp_eq v hy0
    rw [hk, exp_lt_exp] at h
    apply Nat.find_spec hex
    intro y' hy'
    refine mem_invDiffV_of_le v hy (hy'.trans ?_)
    rw [hk, exp_le_exp]; push_cast; omega
  · rcases hd : Nat.find hex with _ | d'
    · rw [hd] at hy
      exact mem_invDiffV_of_le v (one_mem_invDiffV v) (by rw [map_one]; simpa using hy)
    · have := Nat.find_min hex (show d' < Nat.find hex by omega)
      push Not at this
      exact this y (by rw [hd] at hy; exact_mod_cast hy)

/-- **The different exponent** $d_v$: $\mathfrak d_v^{-1} = \mathfrak p_v^{-d_v}$ (`mem_invDiffV_iff`), so
$N(\mathfrak d_v) = N(v)^{d_v}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def diffExp : ℕ := (exists_diffExp v).choose

theorem mem_invDiffV_iff (y : Fv) : y ∈ invDiffV v ↔ Valued.v y ≤ exp (diffExp v : ℤ) :=
  (exists_diffExp v).choose_spec y

/-! ### Lattices $\mathfrak p_v^k$ and their duals -/

/-- The fractional ideal $\mathfrak p_v^k = \{x \in F_v : v(x) \le \exp(-k)\}$, $k \in \mathbb{Z}$, as an additive subgroup. -/
def latticeV (k : ℤ) : AddSubgroup Fv where
  carrier := {x | Valued.v x ≤ exp (-k)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    exact (Valuation.map_add _ x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa [Valuation.map_neg] using hx

lemma mem_latticeV {k : ℤ} {x : Fv} : x ∈ latticeV v k ↔ Valued.v x ≤ exp (-k) := by
  simp [latticeV]

/-- The annihilator $S^\perp = \{y : \psi_v(xy) = 1 \ \forall x \in S\}$ of $S \subseteq F_v$. -/
def annihV (S : Set Fv) : Set Fv := {y | ∀ x ∈ S, psiV v (x * y) = 1}

/-- **The dual of $\mathfrak p_v^k$** under $\psi_v(xy)$ is $\mathfrak d_v^{-1}\mathfrak p_v^{-k} = \mathfrak p_v^{-k-d_v}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem annihV_latticeV (k : ℤ) :
    annihV v (latticeV v k) = latticeV v (-k - diffExp v) := by
  ext y
  simp only [annihV, SetLike.mem_coe, mem_latticeV, Set.mem_ofPred_eq]
  constructor
  · intro h
    have hmem : HN.ϖ v ^ k * y ∈ invDiffV v := by
      intro x hx
      have := h (x * HN.ϖ v ^ k) (by
        rw [map_mul, valued_ϖ_zpow]
        calc Valued.v x * exp (-k) ≤ 1 * exp (-k) := by gcongr
          _ = exp (-k) := one_mul _)
      rwa [mul_assoc] at this
    rw [mem_invDiffV_iff, map_mul, valued_ϖ_zpow] at hmem
    have e : exp (-(-k - (diffExp v : ℤ))) = exp k * exp (diffExp v : ℤ) := by
      rw [← exp_add]; congr 1; ring
    rw [e]
    calc Valued.v y = exp k * (exp (-k) * Valued.v y) := by
          rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
      _ ≤ exp k * exp (diffExp v : ℤ) := by gcongr
  · intro hy x hx
    have hxy : x * y ∈ invDiffV v := by
      rw [mem_invDiffV_iff, map_mul]
      calc Valued.v x * Valued.v y ≤ exp (-k) * exp (-(-k - (diffExp v : ℤ))) := by gcongr
        _ = exp (diffExp v : ℤ) := by rw [← exp_add]; congr 1; ring
    have := hxy 1 (by rw [map_one])
    rwa [one_mul] at this

/-! ### Haar measure on $F_v$ -/

/-- The Borel $\sigma$-algebra on $F_v$. -/
instance : MeasurableSpace Fv := borel Fv

instance : BorelSpace Fv := ⟨rfl⟩

/-- $F_v$ is locally compact (it is a finite-dimensional $\mathbb{Q}_p$-vector space). -/
instance : LocallyCompactSpace Fv :=
  ((Module.finBasis ℚ_[resChar v] Fv).equivFun.toContinuousLinearEquiv).toHomeomorph.isOpenEmbedding.locallyCompactSpace

/-- $F_v$ is a nontrivially normed field ($0 < \|\varpi\| < 1$). -/
instance : NontriviallyNormedField Fv :=
  .ofNormNeOne ⟨HN.ϖ v, HN.ϖ_ne_zero v, (norm_ϖ_lt_one v).ne⟩

instance : ProperSpace Fv := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace Fv

/-- $\mathfrak p_v^k$ is the closed ball of radius $\|\varpi^k\|$. -/
lemma coe_latticeV (k : ℤ) : (latticeV v k : Set Fv) = Metric.closedBall 0 ‖HN.ϖ v ^ k‖ := by
  ext x
  rw [SetLike.mem_coe, mem_latticeV, Metric.mem_closedBall, dist_zero_right,
    Valued.toNormedField.norm_le_iff, valued_ϖ_zpow]

lemma measurableSet_latticeV (k : ℤ) : MeasurableSet (latticeV v k : Set Fv) := by
  rw [coe_latticeV]; exact measurableSet_closedBall

lemma isCompact_latticeV (k : ℤ) : IsCompact (latticeV v k : Set Fv) := by
  rw [coe_latticeV]; exact isCompact_closedBall _ _

lemma interior_latticeV_nonempty (k : ℤ) : (interior (latticeV v k : Set Fv)).Nonempty := by
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  rw [coe_latticeV]
  refine (IsUltrametricDist.isOpen_closedBall (0 : Fv) ?_).mem_nhds
    (Metric.mem_closedBall_self (norm_nonneg _))
  exact (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))).ne'

/-- $\mathcal O_v = \mathfrak p_v^0$ as a compact set with nonempty interior. -/
def OvCompacts : TopologicalSpace.PositiveCompacts Fv where
  carrier := latticeV v 0
  isCompact' := isCompact_latticeV v 0
  interior_nonempty' := interior_latticeV_nonempty v 0

/-- The Haar measure on $F_v$ with $\operatorname{vol}(\mathcal O_v) = 1$. -/
def haarV : MeasureTheory.Measure Fv := MeasureTheory.Measure.addHaarMeasure (OvCompacts v)

instance : (haarV v).IsAddHaarMeasure := by unfold haarV; infer_instance

instance : (haarV v).Regular := by unfold haarV; infer_instance

lemma haarV_latticeV_zero : haarV v (latticeV v 0) = 1 :=
  MeasureTheory.Measure.addHaarMeasure_self

/-- The uniformizer as a unit of $F_v$. -/
def ϖU : Fvˣ := Units.mk0 (HN.ϖ v) (HN.ϖ_ne_zero v)

/-- The modulus $\Delta_v = \operatorname{mod}(\varpi)$ of a uniformizer: $\mu(\varpi S) = \Delta_v\,\mu(S)$ for every Haar
measure $\mu$ (Mathlib's `distribHaarChar`). (It equals $N(v)^{-1}$; that identification is not proved here.) -/
def modV : NNReal := MeasureTheory.distribHaarChar Fv (ϖU v)

lemma modV_pos : 0 < modV v := MeasureTheory.distribHaarChar_pos

/-- $\mathfrak p_v^{k+1} = \varpi\,\mathfrak p_v^k$. -/
lemma latticeV_succ (k : ℤ) : (latticeV v (k + 1) : Set Fv) = ϖU v • (latticeV v k : Set Fv) := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · intro hx
    refine ⟨x / HN.ϖ v, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_latticeV, map_div₀, HN.valued_ϖ, div_le_iff₀ (by simp), ← exp_add]
      have := (mem_latticeV v).mp hx
      convert this using 2; ring
    · rw [Units.smul_def, ϖU, Units.val_mk0, smul_eq_mul, mul_div_cancel₀ _ (HN.ϖ_ne_zero v)]
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_latticeV, Units.smul_def, ϖU, Units.val_mk0, smul_eq_mul, map_mul,
      HN.valued_ϖ]
    have := (mem_latticeV v).mp hy
    calc exp (-1 : ℤ) * Valued.v y ≤ exp (-1 : ℤ) * exp (-k) := by gcongr
      _ = exp (-(k + 1)) := by rw [← exp_add]; congr 1; ring

/-- **Volumes of the lattices:** $\operatorname{vol}(\mathfrak p_v^k) = \Delta_v^k\operatorname{vol}(\mathcal O_v)$ for `haarV`
(where $\operatorname{vol}(\mathcal O_v) = 1$). -/
theorem haarV_real_latticeV (k : ℤ) :
    (haarV v).real (latticeV v k) = (modV v : ℝ) ^ k := by
  have hstep : ∀ k : ℤ, (haarV v).real (latticeV v (k + 1)) = modV v * (haarV v).real (latticeV v k) := by
    intro k
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.real, latticeV_succ,
      ← MeasureTheory.distribHaarChar_mul, ENNReal.toReal_mul]
    rfl
  have hpos : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v
  induction k using Int.induction_on with
  | zero => simp [MeasureTheory.Measure.real, haarV_latticeV_zero]
  | succ k ih => rw [hstep, ih, zpow_add_one₀ hpos.ne', mul_comm]
  | pred k ih =>
    have h := hstep (-(k : ℤ) - 1)
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih] at h
    rw [zpow_sub_one₀ hpos.ne', h]
    field_simp

/-! ### The self-dual measure and the Fourier transform on $F_v$ -/

open MeasureTheory

/-- **The self-dual Haar measure on $F_v$:** $dx_v = \Delta_v^{d_v/2}\cdot$ `haarV`, so that
$\operatorname{vol}(\mathcal O_v) = \Delta_v^{d_v/2}$ $\big(= N(\mathfrak d_v)^{-1/2}$ once $\Delta_v = N(v)^{-1}\big)$ and
$\operatorname{vol}(L)\operatorname{vol}(L^\perp) = 1$ for every lattice $L = \mathfrak p_v^k$ (`selfDualV_real_mul`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, self-dual measure, $\\mathrm{vol}(\\mathcal O_v) = N(\\mathfrak d_v)^{-1/2}$ [unverified]"]
def selfDualV : Measure Fv := ((modV v) ^ ((diffExp v : ℝ) / 2) : NNReal) • haarV v

instance : (selfDualV v).IsAddHaarMeasure := by
  unfold selfDualV
  exact MeasureTheory.Measure.IsAddHaarMeasure.nnreal_smul (haarV v) (NNReal.rpow_pos (modV_pos v)).ne'

/-- $\operatorname{vol}(\mathfrak p_v^k) = \Delta_v^{d_v/2}\,\Delta_v^{k}$ for the self-dual measure. -/
theorem selfDualV_real_latticeV (k : ℤ) :
    (selfDualV v).real (latticeV v k) = (modV v : ℝ) ^ ((diffExp v : ℝ) / 2) * (modV v : ℝ) ^ k := by
  rw [selfDualV, Measure.real, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ← Measure.real, haarV_real_latticeV]
  simp

/-- **Self-duality:** $\operatorname{vol}(\mathfrak p_v^k)\cdot\operatorname{vol}\big((\mathfrak p_v^k)^\perp\big) = 1$, where
$(\mathfrak p_v^k)^\perp = \mathfrak p_v^{-k-d_v}$ (`annihV_latticeV`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem selfDualV_real_mul (k : ℤ) :
    (selfDualV v).real (latticeV v k) * (selfDualV v).real (latticeV v (-k - diffExp v)) = 1 := by
  have hpos : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v
  rw [selfDualV_real_latticeV, selfDualV_real_latticeV]
  have h1 : (modV v : ℝ) ^ ((diffExp v : ℝ) / 2) * (modV v : ℝ) ^ ((diffExp v : ℝ) / 2) =
      (modV v : ℝ) ^ (diffExp v : ℤ) := by
    rw [← Real.rpow_add hpos, add_halves, Real.rpow_natCast, zpow_natCast]
  calc (modV v : ℝ) ^ ((diffExp v : ℝ) / 2) * (modV v : ℝ) ^ k *
        ((modV v : ℝ) ^ ((diffExp v : ℝ) / 2) * (modV v : ℝ) ^ (-k - diffExp v))
      = ((modV v : ℝ) ^ ((diffExp v : ℝ) / 2) * (modV v : ℝ) ^ ((diffExp v : ℝ) / 2)) *
          ((modV v : ℝ) ^ k * (modV v : ℝ) ^ (-k - diffExp v)) := by ring
    _ = 1 := by
      rw [h1, ← zpow_add₀ hpos.ne', ← zpow_add₀ hpos.ne',
        show (diffExp v : ℤ) + (k + (-k - diffExp v)) = 0 by ring, zpow_zero]

/-- **The Fourier transform on $F_v$:** $\hat f(y) = \int_{F_v} f(x)\,\psi_v(xy)\,dx_v$ (self-dual measure). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def fourierV (f : Fv → ℂ) (y : Fv) : ℂ := ∫ x, f x * (psiV v (x * y) : ℂ) ∂selfDualV v

/-- The inverse transform $\check g(x) = \int_{F_v} g(y)\,\psi_v(-xy)\,dy_v$. -/
def fourierInvV (g : Fv → ℂ) (x : Fv) : ℂ := ∫ y, g y * (psiV v (-(x * y)) : ℂ) ∂selfDualV v

/-- The character $x \mapsto \psi_v(xy)$. -/
def psiVMul (y : Fv) : AddChar Fv Circle := (psiV v).compAddMonoidHom (AddMonoidHom.mulRight y)

@[simp] lemma psiVMul_apply (y x : Fv) : psiVMul v y x = psiV v (x * y) := rfl

/-- The indicator $\mathbf 1_{c + \mathfrak p_v^k}$ of $\{x : v(x - c) \le \exp(-k)\}$. -/
def ballIndV (c : Fv) (k : ℤ) : Fv → ℂ := {x : Fv | Valued.v (x - c) ≤ exp (-k)}.indicator fun _ => 1

lemma ballIndV_eq (c : Fv) (k : ℤ) :
    {x : Fv | Valued.v (x - c) ≤ exp (-k)} = Metric.closedBall c ‖HN.ϖ v ^ k‖ := by
  ext x
  rw [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm, Valued.toNormedField.norm_le_iff,
    valued_ϖ_zpow]

open scoped Classical in
/-- **Fourier transform of a lattice coset in $F_v$:**
$\widehat{\mathbf 1_{c + \mathfrak p_v^k}}(y) = \operatorname{vol}(\mathfrak p_v^k)\,\psi_v(cy)\,\mathbf 1_{\mathfrak p_v^{-k-d_v}}(y)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem fourierV_ballIndV (c : Fv) (k : ℤ) (y : Fv) :
    fourierV v (ballIndV v c k) y =
      if y ∈ latticeV v (-k - diffExp v) then
        ((selfDualV v).real (latticeV v k) : ℂ) * (psiV v (c * y) : ℂ) else 0 := by
  unfold fourierV
  rw [← integral_add_right_eq_self _ c]
  have hfun : (fun x => ballIndV v c k (x + c) * (psiV v ((x + c) * y) : ℂ)) =
      fun x => (psiV v (c * y) : ℂ) * (latticeV v k : Set Fv).indicator
        (fun x => (psiVMul v y x : ℂ)) x := by
    ext x
    by_cases hx : x ∈ (latticeV v k : Set Fv)
    · have hx' : x + c ∈ {x : Fv | Valued.v (x - c) ≤ exp (-k)} := by
        rw [Set.mem_ofPred_eq, add_sub_cancel_right]; exact (mem_latticeV v).mp hx
      rw [ballIndV, Set.indicator_of_mem hx', Set.indicator_of_mem hx, one_mul, psiVMul_apply,
        ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · have hx' : x + c ∉ {x : Fv | Valued.v (x - c) ≤ exp (-k)} := by
        rw [Set.mem_ofPred_eq, add_sub_cancel_right]; exact fun h => hx ((mem_latticeV v).mpr h)
      rw [ballIndV, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx, zero_mul, mul_zero]
  rw [hfun, integral_const_mul, integral_indicator (measurableSet_latticeV v k),
    setIntegral_addChar_addSubgroup _ _ (measurableSet_latticeV v k)]
  have hiff : (∀ x ∈ latticeV v k, psiVMul v y x = 1) ↔ y ∈ latticeV v (-k - diffExp v) := by
    rw [← SetLike.mem_coe, ← annihV_latticeV]
    simp [annihV]
  simp only [hiff]
  split_ifs
  · ring
  · simp

/-- **Fourier inversion for lattice cosets in $F_v$** (self-dual measure): $\check{\hat f} = f$ for
$f = \mathbf 1_{c + \mathfrak p_v^k}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 2.2.2 [unverified]"]
theorem fourierInvV_fourierV_ballIndV (c : Fv) (k : ℤ) :
    fourierInvV v (fourierV v (ballIndV v c k)) = ballIndV v c k := by
  ext x
  unfold fourierInvV
  obtain ⟨k', hk'⟩ : ∃ k', k' = -k - (diffExp v : ℤ) := ⟨_, rfl⟩
  have hfun : (fun y => fourierV v (ballIndV v c k) y * (psiV v (-(x * y)) : ℂ)) =
      fun y => ((selfDualV v).real (latticeV v k) : ℂ) *
        (ballIndV v 0 k' y * (psiV v (y * (c - x)) : ℂ)) := by
    ext y
    rw [fourierV_ballIndV, ← hk']
    by_cases hy : y ∈ latticeV v k'
    · have hy' : y ∈ {z : Fv | Valued.v (z - 0) ≤ exp (-k')} := by
        rw [Set.mem_ofPred_eq, sub_zero]; exact (mem_latticeV v).mp hy
      simp only [hy, ↓reduceIte]
      rw [ballIndV, Set.indicator_of_mem hy', one_mul, mul_assoc]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    · have hy' : y ∉ {z : Fv | Valued.v (z - 0) ≤ exp (-k')} := by
        rw [Set.mem_ofPred_eq, sub_zero]; exact fun h => hy ((mem_latticeV v).mpr h)
      simp only [hy, ↓reduceIte]
      rw [ballIndV, Set.indicator_of_notMem hy']
      simp
  rw [hfun, integral_const_mul]
  have h2 := fourierV_ballIndV v 0 k' (c - x)
  unfold fourierV at h2
  rw [h2, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
  have hk : -k' - (diffExp v : ℤ) = k := by rw [hk']; ring
  rw [hk]
  unfold ballIndV
  by_cases hx : c - x ∈ latticeV v k
  · have hx' : x ∈ {z : Fv | Valued.v (z - c) ≤ exp (-k)} := by
      rw [Set.mem_ofPred_eq, ← Valuation.map_neg, neg_sub]; exact (mem_latticeV v).mp hx
    simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_mem hx', ← Complex.ofReal_mul, mul_comm]
    conv_lhs => rw [← hk]
    rw [selfDualV_real_mul, Complex.ofReal_one]
  · have hx' : x ∉ {z : Fv | Valued.v (z - c) ≤ exp (-k)} := by
      rw [Set.mem_ofPred_eq, ← Valuation.map_neg, neg_sub]; exact fun h => hx ((mem_latticeV v).mpr h)
    simp only [hx, ↓reduceIte]
    rw [Set.indicator_of_notMem hx', mul_zero]

/-! ### The modulus of a uniformizer and $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ -/

/-- $\mathcal O_v$ is the disjoint union of $N(v)$ translates of $\mathfrak p_v$, so
$\operatorname{vol}(\mathcal O_v) = N(v)\operatorname{vol}(\mathfrak p_v)$. -/
lemma haarV_latticeV_zero_eq :
    haarV v (latticeV v 0) = (Ideal.absNorm v.asIdeal : ENNReal) * haarV v (latticeV v 1) := by
  classical
  let I : Ideal (v.adicCompletionIntegers F) := Ideal.span {HN.ϖO v ^ 1}
  let Q := (v.adicCompletionIntegers F) ⧸ I
  have hcard : Nat.card Q = Ideal.absNorm v.asIdeal := by
    rw [HN.card_quot_ϖ_pow, pow_one]
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN0)
  let _ : Fintype Q := Fintype.ofFinite Q
  let o : Q → v.adicCompletionIntegers F := fun q => (Ideal.Quotient.mk_surjective q).choose
  have ho : ∀ q, Ideal.Quotient.mk I (o q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
  let A : Q → Set Fv := fun q => {x : Fv | Valued.v (x - (o q : Fv)) ≤ exp (-(1 : ℤ))}
  have hA : ∀ q, A q = Metric.closedBall ((o q : Fv)) ‖HN.ϖ v ^ (1 : ℤ)‖ := fun q => ballIndV_eq v _ 1
  have hU : (latticeV v 0 : Set Fv) = ⋃ q, A q := by
    ext x
    rw [SetLike.mem_coe, mem_latticeV, neg_zero, exp_zero, Set.mem_iUnion]
    constructor
    · intro hx
      let z : v.adicCompletionIntegers F := ⟨x, hx⟩
      refine ⟨Ideal.Quotient.mk I z, ?_⟩
      have hmem : z - o (Ideal.Quotient.mk I z) ∈ I := by
        rw [← Ideal.Quotient.eq, ho]
      have := (HN.mem_span_ϖ_pow v 1 _).mp hmem
      simpa [A] using this
    · rintro ⟨q, hq⟩
      have h1 : Valued.v (o q : Fv) ≤ 1 := (o q).2
      have : x = (x - (o q : Fv)) + (o q : Fv) := by ring
      rw [this]
      refine (Valuation.map_add _ _ _).trans (max_le (hq.trans ?_) h1)
      exact exp_le_one_iff.mpr (by norm_num)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    apply hqq'
    rw [← ho q, ← ho q', Ideal.Quotient.eq, HN.mem_span_ϖ_pow]
    have e : ((o q - o q' : v.adicCompletionIntegers F) : Fv) =
        -(x - (o q : Fv)) + (x - (o q' : Fv)) := by push_cast; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hx')
    rw [Valuation.map_neg]; exact hx
  rw [hU, measure_iUnion hdisj (fun q => by rw [hA]; exact measurableSet_closedBall)]
  simp_rw [hA, Measure.addHaar_closedBall_center, ← coe_latticeV]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    hcard]

/-- **The modulus of a uniformizer:** $\Delta_v = \operatorname{mod}_{F_v}(\varpi) = N(v)^{-1}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem modV_eq : (modV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have h1 := haarV_real_latticeV v 1
  have h0 := haarV_latticeV_zero_eq v
  rw [haarV_latticeV_zero] at h0
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h0' : (1 : ℝ) = Ideal.absNorm v.asIdeal * (haarV v).real (latticeV v 1) := by
    have := congrArg ENNReal.toReal h0
    rwa [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  rw [h1, zpow_one] at h0'
  field_simp
  linarith

/-- **$\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$** for the self-dual measure, where
$N(\mathfrak d_v) = N(v)^{d_v}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
theorem selfDualV_real_Ov :
    (selfDualV v).real (latticeV v 0) =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) := by
  have hN : (0 : ℝ) ≤ Ideal.absNorm v.asIdeal := Nat.cast_nonneg _
  rw [selfDualV_real_latticeV, zpow_zero, mul_one, modV_eq, Real.inv_rpow hN, ← Real.rpow_natCast,
    ← Real.rpow_mul hN, ← Real.rpow_neg hN]
  congr 1
  ring

/-! ### Schwartz–Bruhat functions on $F_v$ -/

lemma continuous_psiV_comp {X : Type*} [TopologicalSpace X] {g : X → Fv} (hg : Continuous g) :
    Continuous fun x => (psiV v (g x) : ℂ) :=
  continuous_subtype_val.comp ((continuous_psiV v).comp hg)

lemma integrable_ballIndV_mul (c : Fv) (k : ℤ) {g : Fv → ℂ} (hg : Continuous g) :
    Integrable (fun x => ballIndV v c k x * g x) (selfDualV v) := by
  have h := (hg.continuousOn.integrableOn_compact (μ := selfDualV v)
    (isCompact_closedBall c ‖HN.ϖ v ^ k‖)).integrable_indicator measurableSet_closedBall
  rw [← ballIndV_eq] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ {x : Fv | Valued.v (x - c) ≤ exp (-k)}
  · show _ = ballIndV v c k x * g x
    rw [ballIndV, Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · show _ = ballIndV v c k x * g x
    rw [ballIndV, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

lemma fourierV_ballIndV_eq (c : Fv) (k : ℤ) :
    fourierV v (ballIndV v c k) = fun y => ballIndV v 0 (-k - diffExp v) y *
      (((selfDualV v).real (latticeV v k) : ℂ) * (psiV v (c * y) : ℂ)) := by
  classical
  ext y
  rw [fourierV_ballIndV]
  by_cases hy : y ∈ latticeV v (-k - diffExp v)
  · have hy' : y ∈ {z : Fv | Valued.v (z - 0) ≤ exp (-(-k - (diffExp v : ℤ)))} := by
      rw [Set.mem_ofPred_eq, sub_zero]; exact (mem_latticeV v).mp hy
    simp only [hy, ↓reduceIte]
    rw [ballIndV, Set.indicator_of_mem hy', one_mul]
  · have hy' : y ∉ {z : Fv | Valued.v (z - 0) ≤ exp (-(-k - (diffExp v : ℤ)))} := by
      rw [Set.mem_ofPred_eq, sub_zero]; exact fun h => hy ((mem_latticeV v).mpr h)
    simp only [hy, ↓reduceIte]
    rw [ballIndV, Set.indicator_of_notMem hy', zero_mul]

/-- **Schwartz–Bruhat functions on $F_v$:** finite linear combinations
$\sum_{i<n} a_i \mathbf 1_{c_i + \mathfrak p_v^{k_i}}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified]"]
def IsSchwartzBruhatV (f : Fv → ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ) (c : Fin n → Fv) (k : Fin n → ℤ),
    f = fun x => ∑ i, a i * ballIndV v (c i) (k i) x

lemma fourierV_sum {n : ℕ} (a : Fin n → ℂ) (c : Fin n → Fv) (k : Fin n → ℤ) :
    fourierV v (fun x => ∑ i, a i * ballIndV v (c i) (k i) x) =
      fun y => ∑ i, a i * fourierV v (ballIndV v (c i) (k i)) y := by
  ext y
  unfold fourierV
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact (integrable_ballIndV_mul v (c i) (k i)
      (continuous_psiV_comp v (continuous_id.mul continuous_const))).const_mul (a i)

/-- **Fourier inversion for Schwartz–Bruhat functions on $F_v$** (self-dual measure):
$f(x) = \int_{F_v}\hat f(y)\,\psi_v(-xy)\,dy_v$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 2.2.2 [unverified]"]
theorem fourierInvV_fourierV_of_isSchwartzBruhat {f : Fv → ℂ} (hf : IsSchwartzBruhatV v f) :
    fourierInvV v (fourierV v f) = f := by
  obtain ⟨n, a, c, k, rfl⟩ := hf
  rw [fourierV_sum]
  ext x
  unfold fourierInvV
  simp_rw [Finset.sum_mul, mul_assoc]
  have hint : ∀ i, Integrable (fun y => a i * (fourierV v (ballIndV v (c i) (k i)) y *
      (psiV v (-(x * y)) : ℂ))) (selfDualV v) := by
    intro i
    refine Integrable.const_mul ?_ _
    rw [fourierV_ballIndV_eq]
    simp_rw [mul_assoc]
    exact integrable_ballIndV_mul v 0 _ (continuous_const.mul
      ((continuous_psiV_comp v (continuous_const.mul continuous_id)).mul
        (continuous_psiV_comp v (continuous_const.mul continuous_id).neg)))
  rw [integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  have := congrFun (fourierInvV_fourierV_ballIndV v (c i) (k i)) x
  unfold fourierInvV at this
  rw [this]

end

end QuadFormsKB.Analysis
