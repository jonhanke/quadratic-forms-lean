import QuadFormsKB.Analysis.GlobalCharacter

/-!
# Fractional ideals by local exponents; the different

For a Dedekind domain $R$ with fraction field $K$ and a height-one prime $v$:

* `valuation_eq_exp_neg_count`: $v(x) = \exp(-\operatorname{ord}_v(x))$ for $x \ne 0$, where $\operatorname{ord}_v(x)$ is
  Mathlib's `FractionalIdeal.count` of the principal fractional ideal $(x)$;
* `le_one_iff_count_nonneg`: a nonzero fractional ideal is integral iff all its exponents are $\ge 0$;
* `mem_iff_forall_valuation_le`: **membership is local**, $x \in I \iff v(x) \le \exp(-\operatorname{ord}_v I)$ for all $v$.

For a number field $F$:

* `idealOfExps k` $= \prod_v\mathfrak p_v^{k_v}$ (`k` of finite support): `mem_idealOfExps_iff`
  ($x \in \prod_v\mathfrak p_v^{k_v} \iff v(x) \le \exp(-k_v)\ \forall v$), `absNorm_idealOfExps`
  ($N = \prod_v N(v)^{k_v}$);
* `mem_dual_one_iff`, `count_dual_one`, `dual_one_eq_idealOfExps`: the inverse different
  $\mathfrak d^{-1}$ = `FractionalIdeal.dual ℤ ℚ 1` is $\prod_v\mathfrak p_v^{-d_v}$, where $d_v$ = `diffExp v` is the local
  exponent (the conductor of $\psi_v$ is $\mathfrak p_v^{-d_v}$); so $d_v = \operatorname{ord}_v \mathfrak d$ and
  `finite_support_diffExp`;
* `finprod_absNorm_pow_diffExp`: $\prod_v N(v)^{d_v} = |d_F|$ (from Mathlib's `absNorm_differentIdeal`);
* `mem_dual_idealOfExps_iff`: the trace dual of $\prod_v\mathfrak p_v^{k_v}$ is $\prod_v\mathfrak p_v^{-k_v-d_v}$.

Sources: Neukirch, *Algebraic Number Theory*, Ch. I §3 and Ch. III §2 [unverified]; Tate's thesis,
Cassels–Fröhlich Ch. XV §2.2 [unverified].
-/

open IsDedekindDomain NumberField WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

lemma count_coe_span_singleton {r : R} (hr : r ≠ 0) :
    FractionalIdeal.count K v ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) =
      (multiplicity v.asIdeal (Ideal.span {r}) : ℤ) := by
  have hI : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have h := Ideal.finprod_heightOneSpectrum_pow_multiplicity hI
  have hfin : Function.HasFiniteMulSupport fun w : HeightOneSpectrum R =>
      w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {r}) := by
    refine (Ideal.finite_factors hI).subset fun w hw => ?_
    rw [Function.mem_mulSupport] at hw
    rw [Set.mem_ofPred_eq]
    by_contra h'
    exact hw (by rw [multiplicity_eq_zero_of_not_dvd h', pow_zero, Ideal.one_eq_top])
  have h2 : ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) =
      ∏ᶠ w : HeightOneSpectrum R, ((w.asIdeal : FractionalIdeal R⁰ K)) ^
        ((multiplicity w.asIdeal (Ideal.span {r}) : ℕ) : ℤ) := by
    conv_lhs => rw [← h]
    rw [show ((∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {r}) :
        Ideal R) : FractionalIdeal R⁰ K) = (FractionalIdeal.coeIdealHom R⁰ K).toMonoidHom
          (∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ multiplicity w.asIdeal (Ideal.span {r})) from rfl,
      MonoidHom.map_finprod _ hfin]
    refine finprod_congr fun w => ?_
    simp [zpow_natCast, FractionalIdeal.coeIdeal_pow]
  rw [h2, FractionalIdeal.count_finprod]
  refine (Ideal.finite_factors hI).subset fun w hw => ?_
  rw [Set.mem_ofPred_eq]
  by_contra h'
  exact hw (by simp [multiplicity_eq_zero_of_not_dvd h'])

/-- **Valuation and factorization:** for $x \ne 0$, $v(x) = \exp(-\operatorname{ord}_v x)$ where
$\operatorname{ord}_v x$ is the exponent of $v$ in the fractional ideal $(x)$. -/
theorem valuation_eq_exp_neg_count {x : K} (hx : x ≠ 0) :
    v.valuation K x = exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
  simp only at hx ⊢
  have hn : n ≠ 0 := by
    rintro rfl; exact hx (by simp)
  have hd : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hn' : ((Ideal.span {n} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hn
  have hd' : ((Ideal.span {(d : R)} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hd
  rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_mul K v hn' (inv_ne_zero hd'),
    FractionalIdeal.count_inv, count_coe_span_singleton v hn, count_coe_span_singleton v hd,
    map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hn,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hd, ← exp_neg, ← exp_add]
  congr 1
  ring

omit [IsFractionRing R K] in
lemma coe_finprod_pow (e : HeightOneSpectrum R → ℕ) (he : Function.HasFiniteMulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ e w) :
    ((∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ e w : Ideal R) : FractionalIdeal R⁰ K) =
      ∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ K) ^ e w := by
  rw [show ((∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ e w : Ideal R) : FractionalIdeal R⁰ K) =
      (FractionalIdeal.coeIdealHom R⁰ K).toMonoidHom (∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ e w)
      from rfl, MonoidHom.map_finprod _ he]
  exact finprod_congr fun w => by simp [FractionalIdeal.coeIdeal_pow]

/-- A nonzero fractional ideal is integral iff all its exponents are $\ge 0$. -/
theorem le_one_iff_count_nonneg {J : FractionalIdeal R⁰ K} (hJ : J ≠ 0) :
    J ≤ 1 ↔ ∀ w : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K w J := by
  constructor
  · intro h w
    obtain ⟨J', rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp h
    exact FractionalIdeal.count_coe_nonneg K w J'
  · intro h
    have hfin : {w : HeightOneSpectrum R | FractionalIdeal.count K w J ≠ 0}.Finite :=
      FractionalIdeal.finite_factors (K := K) J
    set e : HeightOneSpectrum R → ℕ := fun w => (FractionalIdeal.count K w J).toNat
    have he : Function.HasFiniteMulSupport fun w : HeightOneSpectrum R => w.asIdeal ^ e w := by
      refine hfin.subset fun w hw => ?_
      rw [Function.mem_mulSupport] at hw
      rw [Set.mem_ofPred_eq]
      intro h0
      exact hw (by simp [e, h0, Ideal.one_eq_top])
    have hJ' : J = ((∏ᶠ w : HeightOneSpectrum R, w.asIdeal ^ e w : Ideal R) : FractionalIdeal R⁰ K) := by
      rw [coe_finprod_pow e he]
      conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
      refine finprod_congr fun w => ?_
      rw [← zpow_natCast]
      congr 1
      simp [e, Int.toNat_of_nonneg (h w)]
    rw [hJ']
    exact FractionalIdeal.coeIdeal_le_one

/-- **Membership in a fractional ideal is local:** for $I \ne 0$, $x \in I$ iff
$v(x) \le \exp(-\operatorname{ord}_v I)$ for every $v$. -/
@[kb "neukirch1999" "Ch. I, §3 (unique factorization of fractional ideals) [unverified]"]
theorem mem_iff_forall_valuation_le {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ w : HeightOneSpectrum R, w.valuation K x ≤ exp (-FractionalIdeal.count K w I) := by
  by_cases hx : x = 0
  · simp [hx, I.zero_mem]
  have hs : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  have h1 : FractionalIdeal.spanSingleton R⁰ x ≤ I ↔ FractionalIdeal.spanSingleton R⁰ x * I⁻¹ ≤ 1 := by
    constructor
    · intro h
      calc _ ≤ I * I⁻¹ := mul_le_mul' h le_rfl
        _ = 1 := mul_inv_cancel₀ hI
    · intro h
      calc FractionalIdeal.spanSingleton R⁰ x = FractionalIdeal.spanSingleton R⁰ x * I⁻¹ * I := by
            rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
        _ ≤ 1 * I := mul_le_mul' h le_rfl
        _ = I := one_mul I
  rw [h1, le_one_iff_count_nonneg (mul_ne_zero hs (inv_ne_zero hI))]
  refine forall_congr' fun w => ?_
  rw [FractionalIdeal.count_mul K w hs (inv_ne_zero hI), FractionalIdeal.count_inv,
    valuation_eq_exp_neg_count w hx, exp_le_exp]
  omega

end General

section NF

variable {F : Type} [Field F] [NumberField F]

local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-- The fractional ideal $\prod_v \mathfrak p_v^{k_v}$ with prescribed exponents $k_v$ (meaningful when only
finitely many $k_v \ne 0$). -/
def idealOfExps (k : HeightOneSpectrum (𝓞 F) → ℤ) : FI :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FI) ^ k v

lemma coe_heightOne_ne_zero (v : HeightOneSpectrum (𝓞 F)) : (v.asIdeal : FI) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact v.ne_bot

lemma idealOfExps_ne_zero (k : HeightOneSpectrum (𝓞 F) → ℤ) : idealOfExps k ≠ 0 :=
  finprod_induction (fun I : FI => I ≠ 0) one_ne_zero (fun _ _ hx hy => mul_ne_zero hx hy)
    fun v => zpow_ne_zero _ (coe_heightOne_ne_zero v)

lemma count_idealOfExps {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite)
    (v : HeightOneSpectrum (𝓞 F)) : FractionalIdeal.count F v (idealOfExps k) = k v :=
  FractionalIdeal.count_finprod F v k (Filter.eventually_cofinite.mpr hk)

/-- $x \in \prod_v\mathfrak p_v^{k_v}$ iff $v(x) \le \exp(-k_v)$ for every $v$. -/
theorem mem_idealOfExps_iff {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite)
    (x : F) : x ∈ idealOfExps k ↔
      ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) x) ≤ exp (-k v) := by
  rw [mem_iff_forall_valuation_le (idealOfExps_ne_zero k)]
  simp only [count_idealOfExps hk, HN.valued_algebraMap]

/-- $N\big(\prod_v \mathfrak p_v^{k_v}\big) = \prod_v N(v)^{k_v}$. -/
theorem absNorm_idealOfExps {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite) :
    FractionalIdeal.absNorm (idealOfExps k) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ k v := by
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (v.asIdeal : FI) ^ k v :=
    hk.subset fun v hv => by
      rw [Function.mem_mulSupport] at hv
      intro h0; exact hv (by rw [h0, zpow_zero])
  rw [idealOfExps, show FractionalIdeal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FI) ^ k v) =
    (FractionalIdeal.absNorm (R := 𝓞 F) (K := F)).toMonoidHom
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), (v.asIdeal : FI) ^ k v) from rfl, MonoidHom.map_finprod _ hfin]
  refine finprod_congr fun v => ?_
  change FractionalIdeal.absNorm _ = _
  rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]

/-! ### The inverse different and $d_v$ -/

/-- $x \in \mathfrak d^{-1} = $ `dual ℤ ℚ 1` iff $v(x) \le \exp(d_v)$ at every $v$. -/
theorem mem_dual_one_iff (x : F) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FI) ↔
      ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v (algebraMap F (v.adicCompletion F) x) ≤ exp (diffExp v : ℤ) := by
  simp_rw [← mem_invDiffV_iff]
  rw [← trace_int_iff_forall_mem_invDiffV, FractionalIdeal.mem_dual one_ne_zero]
  constructor
  · intro h a
    obtain ⟨m, hm⟩ := h (a : F) ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm]; simp⟩
  · intro h a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := h a'
    exact ⟨m, by rw [Algebra.traceForm_apply]; simp [hm]⟩

lemma dual_one_ne_zero : FractionalIdeal.dual ℤ ℚ (1 : FI) ≠ 0 :=
  FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero

open Classical in
lemma count_mul_coe (I : FI) (hI : I ≠ 0) (v w : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    FractionalIdeal.count F w (I * (v.asIdeal : FI) ^ n) =
      FractionalIdeal.count F w I + if v = w then n else 0 := by
  classical
  rw [FractionalIdeal.count_mul F w hI (zpow_ne_zero _ (coe_heightOne_ne_zero v)),
    FractionalIdeal.count_zpow, FractionalIdeal.count_maximal]
  split_ifs <;> simp

/-- **$d_v$ is the exponent of $v$ in the different:** $\operatorname{ord}_v(\mathfrak d^{-1}) = -d_v$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 (the local different and the conductor of $\\psi_v$) [unverified]"]
theorem count_dual_one (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F v (FractionalIdeal.dual ℤ ℚ (1 : FI)) = -(diffExp v : ℤ) := by
  classical
  set D : FI := FractionalIdeal.dual ℤ ℚ 1 with hD
  have hD0 : D ≠ 0 := dual_one_ne_zero
  have memD : ∀ x : F, x ∈ D ↔ ∀ u : HeightOneSpectrum (𝓞 F), u.valuation F x ≤ exp (diffExp u : ℤ) := by
    intro x
    rw [hD, mem_dual_one_iff]
    simp only [HN.valued_algebraMap]
  have hv0 : ∀ n : ℤ, D * (v.asIdeal : FI) ^ n ≠ 0 := fun n =>
    mul_ne_zero hD0 (zpow_ne_zero _ (coe_heightOne_ne_zero v))
  -- part 1: `-ord_w D ≤ d_w` for every `w`
  have part1 : ∀ w : HeightOneSpectrum (𝓞 F), -FractionalIdeal.count F w D ≤ diffExp w := by
    intro w
    by_contra hlt
    have hw0 : D * (w.asIdeal : FI) ^ (1 : ℤ) ≠ 0 :=
      mul_ne_zero hD0 (zpow_ne_zero _ (coe_heightOne_ne_zero w))
    have hle : D ≤ D * (w.asIdeal : FI) ^ (1 : ℤ) := by
      intro x hx
      rw [mem_iff_forall_valuation_le hw0]
      intro u
      rw [count_mul_coe D hD0 w u]
      by_cases hu : w = u
      · subst hu
        simp only [↓reduceIte]
        refine ((memD x).mp hx w).trans (exp_le_exp.mpr ?_)
        omega
      · simp only [hu, ↓reduceIte, add_zero]
        exact (mem_iff_forall_valuation_le hD0 x).mp hx u
    have := FractionalIdeal.count_mono F w hD0 hle
    rw [count_mul_coe D hD0 w w] at this
    simp only [↓reduceIte] at this
    omega
  -- part 2: `ord_v D ≤ -d_v`
  refine le_antisymm ?_ (by have := part1 v; omega)
  by_contra hlt
  have hle : D * (v.asIdeal : FI) ^ (-1 : ℤ) ≤ D := by
    intro x hx
    rw [mem_iff_forall_valuation_le (hv0 _)] at hx
    rw [memD]
    intro u
    have hxu := hx u
    rw [count_mul_coe D hD0 v u] at hxu
    by_cases hu : v = u
    · subst hu
      simp only [↓reduceIte] at hxu
      refine hxu.trans (exp_le_exp.mpr ?_)
      omega
    · simp only [hu, ↓reduceIte, add_zero] at hxu
      refine hxu.trans (exp_le_exp.mpr ?_)
      have := part1 u
      omega
  have := FractionalIdeal.count_mono F v (hv0 _) hle
  rw [count_mul_coe D hD0 v v] at this
  simp only [↓reduceIte] at this
  omega

/-- Only finitely many $d_v$ are nonzero. -/
theorem finite_support_diffExp :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => (diffExp v : ℤ)).Finite := by
  refine (FractionalIdeal.finite_factors (K := F) (FractionalIdeal.dual ℤ ℚ (1 : FI))).subset
    fun v hv => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, count_dual_one, neg_eq_zero]
  simpa using hv

/-- The negated exponents $-d_v$. -/
lemma finite_support_neg_diffExp :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) => -(diffExp v : ℤ)).Finite := by
  simpa using finite_support_diffExp (F := F)

/-- **The inverse different** is $\mathfrak d^{-1} = \prod_v \mathfrak p_v^{-d_v}$. -/
theorem dual_one_eq_idealOfExps :
    FractionalIdeal.dual ℤ ℚ (1 : FI) = idealOfExps fun v => -(diffExp v : ℤ) := by
  conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F dual_one_ne_zero]
  exact finprod_congr fun v => by rw [count_dual_one]

/-- **$\prod_v N(v)^{d_v} = |d_F|$**, i.e. $N(\mathfrak d_{F/\mathbb{Q}}) = |d_F|$ with $\mathfrak d_v = \mathfrak p_v^{d_v}$. -/
@[kb "neukirch1999" "Ch. III, Thm. 2.9 ($N(\\mathfrak d) = |d_F|$) [unverified]"]
theorem finprod_absNorm_pow_diffExp :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (diffExp v : ℤ) =
      |(NumberField.discr F : ℚ)| := by
  have h1 := absNorm_idealOfExps (F := F) finite_support_neg_diffExp
  rw [← dual_one_eq_idealOfExps] at h1
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ (1 : FI)) =
      ((NumberField.discr F).natAbs : ℚ)⁻¹ := by
    have := congrArg (FractionalIdeal.absNorm (R := 𝓞 F) (K := F))
      (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
    rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal F (𝓞 F), map_inv₀] at this
    rw [← inv_inv (FractionalIdeal.absNorm _), ← this]
  rw [h2] at h1
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (diffExp v : ℤ) =
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (-(diffExp v : ℤ)))⁻¹ := by
    rw [← finprod_inv_distrib]
    exact finprod_congr fun v => by rw [zpow_neg, inv_inv]
  rw [h3, ← h1, inv_inv, Nat.cast_natAbs, Int.cast_abs]

/-- **The dual of $\prod_v\mathfrak p_v^{k_v}$ for the trace form** is $\prod_v\mathfrak p_v^{-k_v-d_v}$:
$x \in \mathfrak a^\vee$ iff $v(x) \le \exp(k_v + d_v)$ for every $v$. -/
@[kb "neukirch1999" "Ch. III, §2 ($\\mathfrak a^\\vee = \\mathfrak a^{-1}\\mathfrak d^{-1}$) [unverified]"]
theorem mem_dual_idealOfExps_iff {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite)
    (x : F) : x ∈ FractionalIdeal.dual ℤ ℚ (idealOfExps k) ↔
      ∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v (algebraMap F (v.adicCompletion F) x) ≤ exp (k v + diffExp v) := by
  have hne : FractionalIdeal.dual ℤ ℚ (1 : FI) * (idealOfExps k)⁻¹ ≠ 0 :=
    mul_ne_zero dual_one_ne_zero (inv_ne_zero (idealOfExps_ne_zero k))
  rw [FractionalIdeal.dual_eq_mul_inv, mem_iff_forall_valuation_le hne]
  refine forall_congr' fun v => ?_
  rw [FractionalIdeal.count_mul F v dual_one_ne_zero (inv_ne_zero (idealOfExps_ne_zero k)),
    FractionalIdeal.count_inv, count_dual_one, count_idealOfExps hk, HN.valued_algebraMap]
  congr! 2
  ring

end NF

end

end QuadFormsKB.Analysis
