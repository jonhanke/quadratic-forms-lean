/-
# Very strong approximation in a number field (O'Meara 33G)

**Layer:** a number field $F$, its finite completions $F_\mathfrak p$ and its infinite places $w$ (absolute values,
`InfinitePlace F`), with the mixed embedding $F \to F_{\mathbb R} = \mathbb R^{r_1} \times \mathbb C^{r_2}$
(Mathlib's `mixedEmbedding`).

**Proves** `exists_very_strong_approx` (O'Meara 1973, 33:? (§33G) [unverified], the form used in step 4 of 104:3): for a
finite set $T$ of finite primes with neighbourhoods $O_\mathfrak p$ of points $b_\mathfrak p$, an infinite place $q_0$, a set
$S$ of infinite places with $q_0 \notin S$ and bounds $\delta > 0$, $R$, there is $\beta \in F$ with $\beta \in O_\mathfrak p$ on
$T$, $\beta$ integral at every other finite prime, $w(\beta) < \delta$ for $w \in S$ and $w(\beta) > R$ for $w \notin S$.

*Proof.* Strong approximation at the finite places gives $\beta_1$; perturb by $m t \gamma$ with $m \in \mathcal O_F$ deep in
the primes of $T$, $t \in \mathcal O_F \setminus 0$ small at every $w \ne q_0$ (Minkowski,
`exists_ne_zero_mem_ringOfIntegers_lt`), and $\gamma \in \mathcal O_F$ within a bounded distance of a prescribed point of
$F_{\mathbb R}$ after rescaling by $(mt)^{-1}$ (`exists_near_integer`: the lattice $\mathcal O_F$ is cocompact). The large value
at $q_0$ is put into the target, so no product formula is needed.
-/
import QuadFormsKB.Lattices.SAApprox

open NumberField IsDedekindDomain WithZero Topology NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **$\mathcal O_F$ is cocompact in $F_{\mathbb R}$:** every point is within a fixed distance $C$ (at every place) of the
image of an algebraic integer. Take integer parts of the coordinates in a $\mathbb Z$-basis of $\mathcal O_F$. -/
theorem exists_near_integer : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : mixedSpace F, ∃ γ : 𝓞 F,
    ∀ w : InfinitePlace F, normAtPlace w (x - mixedEmbedding F (algebraMap (𝓞 F) F γ)) ≤ C := by
  classical
  set b := latticeBasis F
  refine ⟨∑ w : InfinitePlace F, ∑ i, normAtPlace w (b i), Finset.sum_nonneg fun w _ =>
    Finset.sum_nonneg fun i _ => normAtPlace_nonneg _ _, fun x => ?_⟩
  set c := b.repr x
  refine ⟨∑ i, (⌊c i⌋ : ℤ) • RingOfIntegers.basis F i, fun w => ?_⟩
  have hemb : mixedEmbedding F (algebraMap (𝓞 F) F (∑ i, (⌊c i⌋ : ℤ) • RingOfIntegers.basis F i)) =
      ∑ i, ((⌊c i⌋ : ℤ) : ℝ) • b i := by
    simp only [map_sum, map_zsmul, b, latticeBasis_apply, integralBasis_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  have hx : x = ∑ i, c i • b i := (b.sum_repr x).symm
  rw [hemb]
  conv_lhs => rw [hx]
  rw [← Finset.sum_sub_distrib]
  have key : ∀ s : Finset _, normAtPlace w (∑ i ∈ s, (c i • b i - ((⌊c i⌋ : ℤ) : ℝ) • b i)) ≤
      ∑ i ∈ s, normAtPlace w (b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      refine (normAtPlace_add_le _ _ _).trans (add_le_add ?_ ih)
      rw [← sub_smul, normAtPlace_smul]
      have h0 : 0 ≤ c j - ⌊c j⌋ := Int.fract_nonneg _
      have h1 : c j - ⌊c j⌋ < 1 := Int.fract_lt_one _
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (normAtPlace_nonneg _ _) h1.le
  exact (key _).trans (Finset.single_le_sum (f := fun w => ∑ i, normAtPlace w (b i))
    (fun w _ => Finset.sum_nonneg fun i _ => normAtPlace_nonneg _ _) (Finset.mem_univ w))

/-- **Minkowski:** a nonzero algebraic integer that is small at every infinite place other than $q_0$. -/
theorem exists_small_away (q₀ : InfinitePlace F) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : 𝓞 F, t ≠ 0 ∧ ∀ w, w ≠ q₀ → w (algebraMap (𝓞 F) F t) < ε := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound F 1 < (convexBodyLTFactor F) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
      (ne_of_lt (minkowskiBound_lt_top F 1))
  let f : InfinitePlace F → NNReal := fun _ => ⟨ε, hε.le⟩
  have hf : ∀ w, w ≠ q₀ → f w ≠ 0 := fun w _ h =>
    hε.ne' (congrArg (fun x : NNReal => (x : ℝ)) h :)
  obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f F B hf
  obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt F (f := g)
    (by rw [convexBodyLT_volume]; convert hB; congrm $h_gprod)
  refine ⟨y, h_ynz, fun w hw => ?_⟩
  have := h_yle w
  rw [h_geqf w hw] at this
  exact this

/-- **Very strong approximation** (O'Meara 1973, §33G [unverified]); see the module docstring. -/
@[kb "omeara1963" "§33G, very strong approximation [unverified]"]
theorem exists_very_strong_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (O : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hO : ∀ v ∈ T, O v ∈ 𝓝 (b v))
    (q₀ : InfinitePlace F) (S : Finset (InfinitePlace F)) (hq₀ : q₀ ∉ S) {δ : ℝ} (hδ : 0 < δ) (Rb : ℝ) :
    ∃ β : F, (∀ v ∈ T, algebraMap F (v.adicCompletion F) β ∈ O v) ∧
      (∀ v ∉ T, Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1) ∧
      (∀ w ∈ S, w β < δ) ∧ ∀ w ∉ S, Rb < w β := by
  classical
  -- finite places
  obtain ⟨β₁, hβ₁T, hβ₁out⟩ := exists_scalar_approx T b (fun v => interior (O v))
    fun v hv => interior_mem_nhds.mpr (hO v hv)
  choose! kv hkv using fun v (hv : v ∈ T) =>
    exists_valued_le_of_mem_nhds v (isOpen_interior.mem_nhds (hβ₁T v hv))
  set I : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ (kv v).toNat
  have hI : I ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]; push Not
    intro v _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨m, hmI, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hmv : ∀ v ∈ T, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) ≤ exp (-kv v) := by
    intro v hv
    have hle : I ≤ v.asIdeal ^ (kv v).toNat := Ideal.prod_le_inf.trans (Finset.inf_le hv)
    refine (valued_le_of_mem_pow v (hle hmI)).trans ?_
    rw [exp_le_exp]; omega
  -- archimedean data
  obtain ⟨C, hC0, hC⟩ := exists_near_integer (F := F)
  have hmF : algebraMap (𝓞 F) F m ≠ 0 := by simpa using hm0
  set Mw : ℝ := ∑ w : InfinitePlace F, w (algebraMap (𝓞 F) F m)
  have hMw : 0 ≤ Mw := Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  set ε : ℝ := δ / (C * Mw + 1)
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨t, ht0, htw⟩ := exists_small_away q₀ hε
  have htF : algebraMap (𝓞 F) F t ≠ 0 := by simpa using ht0
  set mt : F := algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F t
  have hmt : mt ≠ 0 := mul_ne_zero hmF htF
  have herr : ∀ w, w ≠ q₀ → C * w mt < δ := by
    intro w hw
    have hwm : w (algebraMap (𝓞 F) F m) ≤ Mw :=
      Finset.single_le_sum (f := fun w => w (algebraMap (𝓞 F) F m)) (fun w _ => AbsoluteValue.nonneg _ _)
        (Finset.mem_univ w)
    rw [show w mt = w (algebraMap (𝓞 F) F m) * w (algebraMap (𝓞 F) F t) from map_mul _ _ _]
    calc C * (w (algebraMap (𝓞 F) F m) * w (algebraMap (𝓞 F) F t))
        ≤ C * (Mw * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hwm (htw w hw).le (AbsoluteValue.nonneg _ _) hMw) hC0
      _ < δ := by
          simp only [ε]
          rw [← mul_assoc, mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  -- the target point
  set Rbig : ℝ := |Rb| + δ + C * q₀ mt + 1
  set r : InfinitePlace F → ℝ := fun w => if w ∈ S then 0 else Rbig
  set y : mixedSpace F := (fun w => r w.1, fun w => (r w.1 : ℂ))
  have hy : ∀ w, normAtPlace w y = |r w| := by
    intro w
    by_cases hw : w.IsReal
    · rw [normAtPlace_apply_of_isReal hw]; simp [y, Real.norm_eq_abs]
    · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
      simp [y, Complex.norm_real, Real.norm_eq_abs]
  set x : mixedSpace F := (mixedEmbedding F (-β₁) + y) * mixedEmbedding F mt⁻¹
  obtain ⟨γ, hγ⟩ := hC x
  set β : F := β₁ + mt * algebraMap (𝓞 F) F γ
  -- `β = y - err` in the mixed space
  set err : mixedSpace F := mixedEmbedding F mt * (x - mixedEmbedding F (algebraMap (𝓞 F) F γ))
  have hβemb : mixedEmbedding F β = y - err := by
    have e : mixedEmbedding F mt * mixedEmbedding F mt⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hmt, map_one]
    simp only [β, err, x, map_add, map_mul, map_neg]
    linear_combination (-(mixedEmbedding F β₁) + y) * e
  have herrw : ∀ w, normAtPlace w err ≤ C * w mt := by
    intro w
    rw [map_mul, normAtPlace_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hγ w) (AbsoluteValue.nonneg _ _)
  have hwβ : ∀ w, w β = normAtPlace w (y - err) := fun w => by rw [← hβemb, normAtPlace_apply]
  have hlow : ∀ w, normAtPlace w y - normAtPlace w err ≤ w β := by
    intro w
    rw [hwβ]
    have := normAtPlace_add_le w (y - err) err
    rw [sub_add_cancel] at this
    linarith
  have hcoe : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : 𝓞 F),
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F z) = algebraMap (𝓞 F) (v.adicCompletion F) z :=
    fun v z => (IsScalarTower.algebraMap_apply _ _ _ _).symm
  refine ⟨β, fun v hv => ?_, fun v hv => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · apply interior_subset
    apply hkv v hv
    simp only [β, mt, map_add, add_sub_cancel_left, map_mul, hcoe]
    calc Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) * Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) t) *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) γ)
        ≤ exp (-kv v) * 1 * 1 := by
          gcongr
          · exact hmv v hv
          · exact valued_int_le_one v t
          · exact valued_int_le_one v γ
      _ = exp (-kv v) := by rw [mul_one, mul_one]
  · simp only [β, mt, map_add, map_mul, hcoe]
    refine (Valuation.map_add _ _ _).trans (max_le (hβ₁out v hv) ?_)
    rw [map_mul, map_mul]
    exact mul_le_one' (mul_le_one' (valued_int_le_one v m) (valued_int_le_one v t)) (valued_int_le_one v γ)
  · have hwq : w ≠ q₀ := fun h => hq₀ (h ▸ hw)
    rw [hwβ]
    have := normAtPlace_add_le w y (-err)
    rw [← sub_eq_add_neg, normAtPlace_neg, hy] at this
    have hr : r w = 0 := by simp [r, hw]
    rw [hr, abs_zero, zero_add] at this
    exact this.trans_lt ((herrw w).trans_lt (herr w hwq))
  · have hr : r w = Rbig := by simp [r, hw]
    have h1 := hlow w
    rw [hy, hr, abs_of_pos (by positivity)] at h1
    by_cases hwq : w = q₀
    · subst hwq
      have := herrw w
      have : |Rb| < Rbig - C * w mt := by simp only [Rbig]; linarith
      linarith [le_abs_self Rb]
    · have := (herrw w).trans (herr w hwq).le
      have h0 : 0 ≤ C * q₀ mt := mul_nonneg hC0 (q₀.1.nonneg mt)
      have : |Rb| < Rbig - δ := by simp only [Rbig]; linarith
      linarith [le_abs_self Rb]

/-! ### The free place a finite prime -/

/-- **A power of a prime is principal**: $\mathfrak p^h = (g)$ with $h$ the class number. -/
theorem exists_span_eq_pow (p : HeightOneSpectrum (𝓞 F)) :
    ∃ g : 𝓞 F, g ≠ 0 ∧ Ideal.span {g} = p.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) := by
  classical
  have hp0 : p.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero p.ne_bot
  have h1 : ClassGroup.mk0 ⟨p.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)), pow_mem hp0 _⟩ = 1 := by
    rw [show (⟨p.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)), pow_mem hp0 _⟩ : (Ideal (𝓞 F))⁰) =
      ⟨p.asIdeal, hp0⟩ ^ Fintype.card (ClassGroup (𝓞 F)) from rfl, map_pow, pow_card_eq_one]
  obtain ⟨g, hg⟩ := ((ClassGroup.mk0_eq_one_iff _).mp h1).principal
  refine ⟨g, ?_, hg.symm⟩
  rintro rfl
  have h0 : p.asIdeal ^ Fintype.card (ClassGroup (𝓞 F)) = 0 := by
    rw [hg, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact pow_ne_zero _ (show p.asIdeal ≠ 0 from p.ne_bot) h0

/-- **An element small at every infinite place, integral away from $\mathfrak p$, not integral at $\mathfrak p$**
(Minkowski for $s$ with $w(s) < \varepsilon\,w(g)^k$, $t = s/g^k$, $(g) = \mathfrak p^h$; non-integrality at $\mathfrak p$ from
$|N(t)| < 1$). -/
theorem exists_small_away_prime (p : HeightOneSpectrum (𝓞 F)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ t : F, (∀ w : InfinitePlace F, w t < ε) ∧ (∀ v, v ≠ p → v.valuation F t ≤ 1) ∧ 1 < p.valuation F t := by
  classical
  obtain ⟨g, hg0, hg⟩ := exists_span_eq_pow p
  set h := Fintype.card (ClassGroup (𝓞 F))
  have hgF : algebraMap (𝓞 F) F g ≠ 0 := by simpa using hg0
  have hgv : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ p → g ∉ v.asIdeal := by
    intro v hv hgin
    have : p.asIdeal ^ h ≤ v.asIdeal := by rw [← hg, Ideal.span_le]; simpa using hgin
    have hpv : p.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le this
    exact hv (HeightOneSpectrum.ext ((p.isMaximal.eq_of_le v.isPrime.ne_top hpv).symm))
  -- the norm of `g`
  set Ng : ℝ := ∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F g) ^ mult w
  have hNg : (2 : ℝ) ≤ Ng := by
    have e1 : Ng = ((Algebra.norm ℤ g).natAbs : ℝ) := by
      simp only [Ng]
      rw [prod_eq_abs_norm, ← Algebra.coe_norm_int, Nat.cast_natAbs]
      push_cast; rfl
    have h2 : (Algebra.norm ℤ g).natAbs = (Ideal.absNorm p.asIdeal) ^ h := by
      rw [← Ideal.absNorm_span_singleton, hg, map_pow]
    have hp2 : 2 ≤ Ideal.absNorm p.asIdeal := by
      have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
      have h1' : Ideal.absNorm p.asIdeal ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
      omega
    have hh : 1 ≤ h := Fintype.card_pos
    rw [e1, h2]; push_cast
    calc (2 : ℝ) ≤ (Ideal.absNorm p.asIdeal : ℝ) := by exact_mod_cast hp2
      _ ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ h :=
          le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm p.asIdeal)) (by omega)
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound F 1 < (convexBodyLTFactor F) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
      (ne_of_lt (minkowskiBound_lt_top F 1))
  set d := Module.finrank ℚ F
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (B : ℝ) ≤ ε ^ d * Ng ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B : ℝ) / ε ^ d) (by linarith : (1 : ℝ) < Ng)
    refine ⟨k, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hk
    linarith
  let f : InfinitePlace F → NNReal := fun w => ⟨ε * w (algebraMap (𝓞 F) F g) ^ k, by positivity⟩
  have hprod : ((∏ w, f w ^ mult w : NNReal) : ℝ) = ε ^ d * Ng ^ k := by
    push_cast
    rw [Finset.prod_congr rfl fun w _ => show ((f w : ℝ)) ^ mult w =
      ε ^ mult w * (w (algebraMap (𝓞 F) F g) ^ mult w) ^ k by change (ε * w (algebraMap (𝓞 F) F g) ^ k) ^ mult w = _; ring,
      Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, sum_mult_eq, Finset.prod_pow]
  obtain ⟨s', hs'0, hs'⟩ := exists_ne_zero_mem_ringOfIntegers_lt F (f := f) (by
    rw [convexBodyLT_volume]
    refine hB.trans_le (mul_le_mul' le_rfl ?_)
    have h1 : ((B : NNReal) : ENNReal) ≤ ((∏ w, f w ^ mult w : NNReal) : ENNReal) :=
      ENNReal.coe_le_coe.mpr (by rw [← NNReal.coe_le_coe, hprod]; push_cast; exact hk)
    simpa using h1)
  have hs'F : algebraMap (𝓞 F) F s' ≠ 0 := by simpa using hs'0
  have hgk : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F g) ^ k := fun w =>
    pow_pos (AbsoluteValue.pos _ hgF) k
  set t : F := algebraMap (𝓞 F) F s' / algebraMap (𝓞 F) F g ^ k
  have ht0 : t ≠ 0 := div_ne_zero hs'F (pow_ne_zero _ hgF)
  have htw : ∀ w : InfinitePlace F, w t < ε := by
    intro w
    have := hs' w
    simp only [f, NNReal.coe_mk] at this
    change w (algebraMap (𝓞 F) F s') < ε * w (algebraMap (𝓞 F) F g) ^ k at this
    rw [map_div₀, map_pow, div_lt_iff₀ (hgk w)]; exact this
  have htv : ∀ v, v ≠ p → v.valuation F t ≤ 1 := by
    intro v hv
    rw [map_div₀, map_pow, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr (hgv v hv),
      one_pow, div_one]
    exact v.intValuation_le_one s'
  refine ⟨t, htw, htv, ?_⟩
  by_contra hle
  push Not at hle
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F t fun v => by
    by_cases hv : v = p
    · rw [hv]; exact hle
    · exact htv v hv
  have hr' : ((r : F)) = t := hr
  have hN1 : (1 : ℝ) ≤ ∏ w : InfinitePlace F, w t ^ mult w := by
    rw [prod_eq_abs_norm, ← hr', ← Algebra.coe_norm_int]
    have hz : Algebra.norm ℤ r ≠ 0 := by
      intro h0
      have := Algebra.coe_norm_int (K := F) r
      rw [h0, Int.cast_zero, hr'] at this
      exact (Algebra.norm_ne_zero_iff.mpr ht0) this.symm
    have : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hz
    simpa using this
  have hN2 : ∏ w : InfinitePlace F, w t ^ mult w < 1 := by
    calc ∏ w : InfinitePlace F, w t ^ mult w ≤ ∏ w : InfinitePlace F, ε ^ mult w :=
          Finset.prod_le_prod₀ (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _)
            (fun w _ => pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) (htw w).le _)
      _ = ε ^ d := by rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]
      _ < 1 := pow_lt_one₀ hε.le hε1 Module.finrank_pos.ne'
  linarith

/-- **Very strong approximation with the free place a finite prime $\mathfrak p$** (O'Meara §33G [unverified]): for a
finite set $T \not\ni \mathfrak p$ of primes with neighbourhoods $O_\mathfrak q$, a set $S$ of infinite places and bounds, there
is $\beta \in F$ with $\beta \in O_\mathfrak q$ on $T$, integral at every prime $\notin T \cup \{\mathfrak p\}$, $w(\beta) < \delta$
on $S$, $w(\beta) > R$ off $S$, and $v_\mathfrak p(\beta) > e^{K}$. -/
@[kb "omeara1963" "§33G, very strong approximation [unverified]"]
theorem exists_very_strong_approx_at (p : HeightOneSpectrum (𝓞 F)) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hpT : p ∉ T) (b : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (O : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hO : ∀ v ∈ T, O v ∈ 𝓝 (b v))
    (S : Finset (InfinitePlace F)) {δ : ℝ} (hδ : 0 < δ) (Rb : ℝ) (Kp : ℤ) :
    ∃ β : F, (∀ v ∈ T, algebraMap F (v.adicCompletion F) β ∈ O v) ∧
      (∀ v ∉ T, v ≠ p → Valued.v (algebraMap F (v.adicCompletion F) β) ≤ 1) ∧
      (∀ w ∈ S, w β < δ) ∧ (∀ w ∉ S, Rb < w β) ∧
      exp Kp < Valued.v (algebraMap F (p.adicCompletion F) β) := by
  classical
  obtain ⟨β₁, hβ₁T, hβ₁out⟩ := exists_scalar_approx T b (fun v => interior (O v))
    fun v hv => interior_mem_nhds.mpr (hO v hv)
  choose! kv hkv using fun v (hv : v ∈ T) =>
    exists_valued_le_of_mem_nhds v (isOpen_interior.mem_nhds (hβ₁T v hv))
  set I : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ (kv v).toNat
  have hI : I ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]; push Not
    intro v _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨m, hmI, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hmv : ∀ v ∈ T, Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) ≤ exp (-kv v) := by
    intro v hv
    have hle : I ≤ v.asIdeal ^ (kv v).toNat := Ideal.prod_le_inf.trans (Finset.inf_le hv)
    refine (valued_le_of_mem_pow v (hle hmI)).trans ?_
    rw [exp_le_exp]; omega
  have hcoe : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : 𝓞 F),
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F z) = algebraMap (𝓞 F) (v.adicCompletion F) z :=
    fun v z => (IsScalarTower.algebraMap_apply _ _ _ _).symm
  obtain ⟨C, hC0, hC⟩ := exists_near_integer (F := F)
  have hmF : algebraMap (𝓞 F) F m ≠ 0 := by simpa using hm0
  set Mw : ℝ := ∑ w : InfinitePlace F, w (algebraMap (𝓞 F) F m)
  have hMw : 0 ≤ Mw := Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  set ε : ℝ := min (1 / 2) (δ / (4 * (C + 1) * (Mw + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  obtain ⟨t, htw, htv, htp⟩ := exists_small_away_prime p hε hε1
  have ht0 : t ≠ 0 := by rintro rfl; rw [map_zero] at htp; exact not_lt.mpr zero_le_one htp
  set mt : F := algebraMap (𝓞 F) F m * t
  have hmt : mt ≠ 0 := mul_ne_zero hmF ht0
  have hwm : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F m) ≤ Mw := fun w =>
    Finset.single_le_sum (f := fun w => w (algebraMap (𝓞 F) F m)) (fun w _ => AbsoluteValue.nonneg _ _)
      (Finset.mem_univ w)
  have hsmall : ∀ w : InfinitePlace F, (C + 1) * w mt < δ / 4 := by
    intro w
    rw [show w mt = w (algebraMap (𝓞 F) F m) * w t from map_mul _ _ _]
    calc (C + 1) * (w (algebraMap (𝓞 F) F m) * w t) ≤ (C + 1) * (Mw * ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hwm w) (htw w).le (AbsoluteValue.nonneg _ _) hMw) (by linarith)
      _ ≤ (C + 1) * (Mw * (δ / (4 * (C + 1) * (Mw + 1)))) := by gcongr; exact min_le_right _ _
      _ < δ / 4 := by
          rw [show (C + 1) * (Mw * (δ / (4 * (C + 1) * (Mw + 1)))) = δ / 4 * (Mw / (Mw + 1)) by
            field_simp]
          have : Mw / (Mw + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
          nlinarith
  -- the archimedean target
  set Rbig : ℝ := |Rb| + δ + 1
  set r : InfinitePlace F → ℝ := fun w => if w ∈ S then 0 else Rbig
  set y : mixedSpace F := (fun w => r w.1, fun w => (r w.1 : ℂ))
  have hy : ∀ w, normAtPlace w y = |r w| := by
    intro w
    by_cases hw : w.IsReal
    · rw [normAtPlace_apply_of_isReal hw]; simp [y, Real.norm_eq_abs]
    · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
      simp [y, Complex.norm_real, Real.norm_eq_abs]
  set x : mixedSpace F := (mixedEmbedding F (-β₁) + y) * mixedEmbedding F mt⁻¹
  obtain ⟨γ, hγ⟩ := hC x
  set β₂ : F := β₁ + mt * algebraMap (𝓞 F) F γ
  set err : mixedSpace F := mixedEmbedding F mt * (x - mixedEmbedding F (algebraMap (𝓞 F) F γ))
  have hβemb : mixedEmbedding F β₂ = y - err := by
    have e : mixedEmbedding F mt * mixedEmbedding F mt⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hmt, map_one]
    simp only [β₂, err, x, map_add, map_mul, map_neg]
    linear_combination (-(mixedEmbedding F β₁) + y) * e
  have herrw : ∀ w, normAtPlace w err ≤ C * w mt := by
    intro w
    rw [map_mul, normAtPlace_apply, mul_comm]
    exact mul_le_mul_of_nonneg_right (hγ w) (AbsoluteValue.nonneg _ _)
  -- the p-adic correction `η = m t^N`
  have htp0 : algebraMap F (p.adicCompletion F) t ≠ 0 := (map_ne_zero _).mpr ht0
  obtain ⟨a, ha⟩ := exists_valued_eq_exp p htp0
  have ha1 : 1 ≤ a := by
    have : Valued.v (algebraMap F (p.adicCompletion F) t) = p.valuation F t := valued_algebraMap p t
    rw [ha] at this
    have h := htp
    rw [← this, ← exp_zero, exp_lt_exp] at h; omega
  have hmp0 : algebraMap (𝓞 F) (p.adicCompletion F) m ≠ 0 := by rw [← hcoe]; exact (map_ne_zero _).mpr hmF
  obtain ⟨bm, hbm⟩ := exists_valued_eq_exp p hmp0
  obtain ⟨kb, hkb⟩ := exists_valued_le p (algebraMap F (p.adicCompletion F) β₂)
  set N : ℕ := (Kp - bm).natAbs + ((kb : ℤ) - bm).natAbs + 1
  set η : F := algebraMap (𝓞 F) F m * t ^ N
  have hηp : Valued.v (algebraMap F (p.adicCompletion F) η) = exp (bm + N * a) := by
    simp only [η, map_mul, map_pow, hcoe, hbm, ha, ← exp_nsmul, ← exp_add]; congr 1
  have hNa : (N : ℤ) ≤ N * a := by nlinarith
  have hηw : ∀ w : InfinitePlace F, w η < δ / 4 := by
    intro w
    have h1 : w t ^ N ≤ w t := pow_le_of_le_one (AbsoluteValue.nonneg _ _) (htw w |>.le.trans hε1.le) (by omega)
    calc w η = w (algebraMap (𝓞 F) F m) * w t ^ N := by simp [η, map_mul, map_pow]
      _ ≤ w (algebraMap (𝓞 F) F m) * w t := mul_le_mul_of_nonneg_left h1 (AbsoluteValue.nonneg _ _)
      _ = w mt := (map_mul _ _ _).symm
      _ ≤ (C + 1) * w mt := le_mul_of_one_le_left (AbsoluteValue.nonneg _ _) (by linarith)
      _ < δ / 4 := hsmall w
  refine ⟨β₂ + η, fun v hv => ?_, fun v hv hvp => ?_, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · apply interior_subset
    apply hkv v hv
    have hvp : v ≠ p := fun h => hpT (h ▸ hv)
    have htv' : Valued.v (algebraMap F (v.adicCompletion F) t) ≤ 1 := by rw [valued_algebraMap]; exact htv v hvp
    simp only [β₂, η, mt, map_add, map_mul, map_pow, hcoe, add_sub_cancel_left]
    rw [show algebraMap F (v.adicCompletion F) β₁ +
        algebraMap (𝓞 F) (v.adicCompletion F) m * algebraMap F _ t * algebraMap (𝓞 F) _ γ +
        algebraMap (𝓞 F) (v.adicCompletion F) m * algebraMap F _ t ^ N - algebraMap F _ β₁ =
        algebraMap (𝓞 F) (v.adicCompletion F) m * (algebraMap F _ t * algebraMap (𝓞 F) _ γ +
          algebraMap F _ t ^ N) by ring, map_mul]
    calc Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) m) *
          Valued.v (algebraMap F (v.adicCompletion F) t * algebraMap (𝓞 F) _ γ + algebraMap F _ t ^ N)
        ≤ exp (-kv v) * 1 := by
          gcongr
          · exact hmv v hv
          · refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
            · rw [map_mul]; exact mul_le_one' htv' (valued_int_le_one v γ)
            · rw [map_pow]; exact pow_le_one₀ zero_le htv'
      _ = exp (-kv v) := mul_one _
  · have htv' : Valued.v (algebraMap F (v.adicCompletion F) t) ≤ 1 := by rw [valued_algebraMap]; exact htv v hvp
    simp only [β₂, η, mt, map_add, map_mul, map_pow, hcoe]
    refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le (hβ₁out v hv) ?_)) ?_)
    · rw [map_mul, map_mul]
      exact mul_le_one' (mul_le_one' (valued_int_le_one v m) htv') (valued_int_le_one v γ)
    · rw [map_mul, map_pow]; exact mul_le_one' (valued_int_le_one v m) (pow_le_one₀ zero_le htv')
  · have hr : r w = 0 := by simp [r, hw]
    have h1 : w β₂ ≤ normAtPlace w y + normAtPlace w err := by
      rw [← normAtPlace_apply, hβemb, sub_eq_add_neg, ← normAtPlace_neg w err]; exact normAtPlace_add_le _ _ _
    rw [hy, hr, abs_zero, zero_add] at h1
    calc w (β₂ + η) ≤ w β₂ + w η := AbsoluteValue.add_le _ _ _
      _ < δ := by have := herrw w; have := hsmall w; have := hηw w; nlinarith
  · have hr : r w = Rbig := by simp [r, hw]
    have h1 : normAtPlace w y ≤ w β₂ + normAtPlace w err := by
      have := normAtPlace_add_le w (y - err) err
      rwa [sub_add_cancel, ← hβemb, normAtPlace_apply] at this
    rw [hy, hr, abs_of_pos (by simp only [Rbig]; positivity)] at h1
    have h2 : w β₂ ≤ w (β₂ + η) + w η := by
      have := AbsoluteValue.add_le w.1 (β₂ + η) (-η)
      rwa [add_neg_cancel_right, AbsoluteValue.map_neg] at this
    have := herrw w; have := hsmall w; have := hηw w
    have : |Rb| < Rbig - δ := by simp only [Rbig]; linarith
    nlinarith [le_abs_self Rb]
  · rw [map_add]
    have hlt : Valued.v (algebraMap F (p.adicCompletion F) β₂) < Valued.v (algebraMap F (p.adicCompletion F) η) := by
      rw [hηp]; refine hkb.trans_lt ?_; rw [exp_lt_exp]; omega
    rw [Valuation.map_add_eq_of_lt_right _ hlt, hηp, exp_lt_exp]; omega

end QuadFormsKB.Lattices
