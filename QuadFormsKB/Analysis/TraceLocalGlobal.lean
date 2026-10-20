import QuadFormsKB.Analysis.LocalFourierNF

/-!
# Global trace = sum of local traces

For a number field $F$, a rational prime $p$ and the finite places $v \mid p$ (`Sp F p`, the height-one primes
$v$ of $\mathcal O_F$ with residue characteristic `resChar v = p`):

* `resChar_eq_iff`: $v \mid p \iff p \in v$; `Sp F p` is finite.
* `distribHaarChar_pU`, `distribHaarChar_pU_eq_norm`, `resChar_pow_finrank`: the Haar modulus of
  multiplication by $p$ on $F_v$ is $p^{-[F_v:\mathbb{Q}_p]}$ (via $F_v \cong \mathbb{Q}_p^{d}$ and the product
  measure) and also $N(v)^{-e_v}$ (via $p = u\varpi^{e_v}$, $e_v = \operatorname{ord}_v p$ = `ramIdx v`), so
  $p^{[F_v:\mathbb{Q}_p]} = N(v)^{e_v}$.
* `prod_absNorm_pow_ramIdx`, `sum_finrank_Sp`: $\prod_{v\mid p} N(v)^{e_v} = N(p\mathcal O_F) = p^{[F:\mathbb{Q}]}$, hence
  $\sum_{v \mid p}[F_v : \mathbb{Q}_p] = [F:\mathbb{Q}]$.
* `exists_int_approx_Sp`: approximation by $\mathcal O_F$ at all $v \mid p$ simultaneously (Chinese remainder
  theorem).
* `WQ_eq_top`, `basisPQ`: the diagonal images of a $\mathbb{Q}$-basis of $F$ form a $\mathbb{Q}_p$-basis of
  $P = \prod_{v\mid p}F_v$ (they span: the span is closed and contains $\mathcal O_F$, which is dense in
  $\prod_{v \mid p}\mathcal O_v$; the dimensions agree). This is $\mathbb{Q}_p \otimes_{\mathbb{Q}} F \cong \prod_{v\mid p}F_v$.
* `trace_PQ_diagQ`, `Algebra.trace_pi'`, **`prod_psiV_Sp`**: for $x \in F$,
  $\operatorname{Tr}_{F/\mathbb{Q}}(x) = \sum_{v\mid p}\operatorname{Tr}_{F_v/\mathbb{Q}_p}(x)$ in $\mathbb{Q}_p$, hence
  $\prod_{v \mid p}\psi_v(x) = \psi_p(\operatorname{Tr}_{F/\mathbb{Q}}x)$.

Each $F_v$ ($v \mid p$) is made a $\mathbb{Q}_p$-algebra for the fixed $p$ through the type synonym `FvQ p v`
(a cast $\mathbb{Q}_p \cong \mathbb{Q}_{\mathrm{resChar}\,v}$, `padicCast`), so that the places above $p$ can be put
into one product.

Sources: Neukirch, *Algebraic Number Theory*, Ch. II, Prop. 8.3 and Cor. 8.4 [unverified]; Cassels–Fröhlich
Ch. II (Cassels, *Global fields*) §10 [unverified]; Tate's thesis, Cassels–Fröhlich Ch. XV §2.2 [unverified].
-/

open IsDedekindDomain NumberField WithZero MeasureTheory
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

lemma resChar_dvd_iff (n : ℕ) :
    resChar v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  change Rat.HeightOneSpectrum.natGenerator (vUnder v) ∣ n ↔ _
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, Ideal.mem_map_of_equiv]
  have he : ∀ x : ℤ, (Rat.IsIntegralClosure.intEquiv ℤ) x = x := fun x => by
    have : ((Rat.IsIntegralClosure.intEquiv ℤ : ℤ ≃+* ℤ) : ℤ →+* ℤ) = RingHom.id ℤ := RingHom.ext_int _ _
    exact DFunLike.congr_fun this x
  simp only [he, exists_eq_right]
  change algebraMap ℤ (𝓞 F) n ∈ v.asIdeal ↔ _
  simp

lemma resChar_eq_iff (p : ℕ) [hp : Fact p.Prime] :
    resChar v = p ↔ (p : 𝓞 F) ∈ v.asIdeal := by
  rw [← resChar_dvd_iff, Nat.prime_dvd_prime_iff_eq (Fact.out) hp.out]

/-- The finite places above $p$. -/
abbrev Sp (F : Type) [Field F] [NumberField F] (p : ℕ) := {v : HeightOneSpectrum (𝓞 F) // resChar v = p}

lemma finite_Sp (p : ℕ) [hp : Fact p.Prime] : Finite (Sp F p) := by
  have h0 : Ideal.span {(p : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have := (Ideal.finite_factors h0).to_subtype
  refine Finite.of_injective (fun v : Sp F p => (⟨v.1, ?_⟩ : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {(p : 𝓞 F)}})) ?_
  · rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
    exact (resChar_eq_iff v.1 p).mp v.2
  · intro a b h
    exact Subtype.ext (congrArg Subtype.val h :)

instance (p : ℕ) [Fact p.Prime] : Fintype (Sp F p) := @Fintype.ofFinite _ (finite_Sp p)



lemma resChar_ne_zero_Fv : ((resChar v : ℕ) : Fv) ≠ 0 := by
  exact_mod_cast (Fact.out : (resChar v).Prime).ne_zero

/-- $p$ as a unit of $F_v$. -/
def pU : Fvˣ := Units.mk0 ((resChar v : ℕ) : Fv) (resChar_ne_zero_Fv v)

lemma padic_smul_closedBall_one (q : ℕ) [hq : Fact q.Prime] :
    (q : ℚ_[q]) • Metric.closedBall (0 : ℚ_[q]) 1 = Metric.closedBall 0 ((q : ℝ) ^ (-(1 : ℤ))) := by
  have hq0 : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  rw [smul_closedBall' hq0, smul_zero, mul_one, Padic.norm_p, zpow_neg, zpow_one]

theorem distribHaarChar_pU :
    (distribHaarChar Fv (pU v) : ℝ) = ((resChar v : ℝ)⁻¹) ^ Module.finrank ℚ_[resChar v] Fv := by
  set q := resChar v with hqdef
  set d := Module.finrank ℚ_[q] Fv
  let b := Module.finBasis ℚ_[q] Fv
  let T : (Fin d → ℚ_[q]) ≃L[ℚ_[q]] Fv := b.equivFun.symm.toContinuousLinearEquiv
  let ν : Measure (Fin d → ℚ_[q]) := Measure.pi fun _ => haarP q
  let μ : Measure Fv := Measure.map T ν
  have : μ.IsAddHaarMeasure := T.isAddHaarMeasure_map ν
  have hTK : ∀ A, μ (T '' A) = ν A := by
    intro A
    rw [show μ = Measure.map T.toHomeomorph.toMeasurableEquiv ν from rfl, MeasurableEquiv.map_apply]
    congr 1
    exact T.toHomeomorph.toEquiv.preimage_image A
  let K : Set (Fin d → ℚ_[q]) := Set.univ.pi fun _ => Metric.closedBall 0 1
  have hq0 : (q : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hK : ν K = 1 := by
    simp only [ν, K, Measure.pi_pi]
    have := haarP_closedBall (p := q) 0
    simp only [neg_zero, zpow_zero, ENNReal.ofReal_one] at this
    simp [this]
  have hqK : (pU v) • (T '' K) = T '' (Set.univ.pi fun _ => Metric.closedBall 0 ((q : ℝ) ^ (-(1 : ℤ)))) := by
    have e1 : (Set.univ.pi fun _ : Fin d => Metric.closedBall (0 : ℚ_[q]) ((q : ℝ) ^ (-(1 : ℤ)))) =
        (q : ℚ_[q]) • K := by
      ext y
      simp only [K, Set.mem_smul_set_iff_inv_smul_mem₀ hq0, Set.mem_pi, Set.mem_univ, true_implies,
        Pi.smul_apply, smul_eq_mul]
      refine forall_congr' fun i => ?_
      rw [← padic_smul_closedBall_one, Set.mem_smul_set_iff_inv_smul_mem₀ hq0, smul_eq_mul]
    rw [e1, ← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
    refine Set.image_congr fun y _ => ?_
    rw [map_smul, Algebra.smul_def, map_natCast, Units.smul_def]
    rfl
  have hqKμ : μ ((pU v) • (T '' K)) = (((q : NNReal)⁻¹) ^ d : NNReal) * μ (T '' K) := by
    rw [hqK, hTK, hTK, hK, mul_one]
    simp only [ν, Measure.pi_pi, haarP_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [zpow_neg, zpow_one, ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fact.out : q.Prime).pos)]
    simp [ENNReal.inv_pow]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (G := Fvˣ) (A := Fv) (μ := μ) (g := pU v)
    (by rw [hTK, hK]; exact one_ne_zero) (by rw [hTK, hK]; exact ENNReal.one_ne_top) hqKμ
  rw [h]
  push_cast
  rfl

/-- $e_v = \operatorname{ord}_v(p)$, the absolute ramification index of $v$ over $p$ = `resChar v`. -/
def ramIdx : ℕ := multiplicity v.asIdeal (Ideal.span {((resChar v : ℕ) : 𝓞 F)})

lemma resChar_ne_zero_O : ((resChar v : ℕ) : 𝓞 F) ≠ 0 := by
  exact_mod_cast (Fact.out : (resChar v).Prime).ne_zero

/-- $v(p) = \exp(-e_v)$. -/
lemma valued_resChar : Valued.v ((resChar v : ℕ) : Fv) = exp (-(ramIdx v : ℤ)) := by
  have : ((resChar v : ℕ) : Fv) = algebraMap F Fv (algebraMap (𝓞 F) F (resChar v : ℕ)) := by
    rw [map_natCast, map_natCast]
  rw [this, HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ (resChar_ne_zero_O v)]
  rfl

lemma distribHaarChar_eq_one_of_valued (w : Fvˣ) (hw : Valued.v (w : Fv) = 1) :
    distribHaarChar Fv w = 1 := by
  have hs : w • (latticeV v 0 : Set Fv) = latticeV v 0 := by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, SetLike.mem_coe, mem_latticeV,
      mem_latticeV, Units.smul_def, smul_eq_mul, map_mul, map_units_inv, hw, inv_one, one_mul]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := haarV v) (s := (latticeV v 0 : Set Fv))
    (by rw [haarV_latticeV_zero]; exact one_ne_zero) (by rw [haarV_latticeV_zero]; exact ENNReal.one_ne_top) ?_
  rw [hs]; simp

theorem distribHaarChar_pU_eq_norm :
    (distribHaarChar Fv (pU v) : ℝ) = ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^ ramIdx v := by
  set e := ramIdx v
  set u : Fvˣ := pU v * (ϖU v ^ e)⁻¹ with hu
  have hpu : pU v = u * ϖU v ^ e := by rw [hu, inv_mul_cancel_right]
  have hϖ : Valued.v ((ϖU v ^ e : Fvˣ) : Fv) = exp (-(e : ℤ)) := by
    rw [Units.val_pow_eq_pow_val]
    exact HN.valued_ϖ_pow v e
  have hu1 : Valued.v (u : Fv) = 1 := by
    rw [hu, Units.val_mul, map_mul, map_units_inv, hϖ]
    change Valued.v ((resChar v : ℕ) : Fv) * _ = 1
    rw [valued_resChar, ← exp_neg, neg_neg, ← exp_add, neg_add_cancel, exp_zero]
  rw [hpu, map_mul, map_pow, distribHaarChar_eq_one_of_valued v u hu1, one_mul]
  push_cast
  change ((modV v : ℝ)) ^ e = _
  rw [modV_eq]

/-- **Local degree:** $p^{[F_v:\mathbb{Q}_p]} = N(v)^{e_v}$, where $e_v = \operatorname{ord}_v(p)$ (`ramIdx`). -/
@[kb "neukirch1999" "Ch. II, §8 ($[F_v:\\mathbb{Q}_p] = e_v f_v$) [unverified]"]
theorem resChar_pow_finrank :
    resChar v ^ Module.finrank ℚ_[resChar v] Fv = Ideal.absNorm v.asIdeal ^ ramIdx v := by
  have h := (distribHaarChar_pU v).symm.trans (distribHaarChar_pU_eq_norm v)
  rw [inv_pow, inv_pow, inv_inj] at h
  exact_mod_cast h

lemma absNorm_span_natCast (q : ℕ) : Ideal.absNorm (Ideal.span {(q : 𝓞 F)}) = q ^ Module.finrank ℚ F := by
  rw [Ideal.absNorm_span_singleton]
  have : (q : 𝓞 F) = algebraMap ℤ (𝓞 F) q := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp

/-- $\prod_{v \mid p} N(v)^{e_v} = N(p\mathcal O_F) = p^{[F:\mathbb{Q}]}$. -/
theorem prod_absNorm_pow_ramIdx (q : ℕ) [hq : Fact q.Prime] :
    ∏ v : Sp F q, Ideal.absNorm v.1.asIdeal ^ ramIdx v.1 = q ^ Module.finrank ℚ F := by
  set I : Ideal (𝓞 F) := Ideal.span {(q : 𝓞 F)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.out.ne_zero
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.asIdeal ^ multiplicity v.asIdeal I := by
    refine (Ideal.finite_factors hI0).subset fun v hv => ?_
    rw [Function.mem_mulSupport] at hv
    rw [Set.mem_ofPred_eq]
    by_contra h
    exact hv (by rw [multiplicity_eq_zero_of_not_dvd h, pow_zero, Ideal.one_eq_top])
  have h1 := congrArg Ideal.absNorm (Ideal.finprod_heightOneSpectrum_pow_multiplicity hI0)
  rw [absNorm_span_natCast] at h1
  rw [← h1]
  have h2 := MonoidHom.map_finprod (Ideal.absNorm (S := 𝓞 F)).toMonoidHom hfin
  rw [show Ideal.absNorm (∏ᶠ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ multiplicity v.asIdeal I) =
    (Ideal.absNorm (S := 𝓞 F)).toMonoidHom (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      v.asIdeal ^ multiplicity v.asIdeal I) from rfl, h2]
  simp only [map_pow]
  rw [finprod_eq_prod_of_mulSupport_subset (s := (Finset.univ : Finset (Sp F q)).map
    ⟨Subtype.val, Subtype.val_injective⟩) _ ?_, Finset.prod_map]
  · refine Finset.prod_congr rfl fun v _ => ?_
    simp only [Function.Embedding.coeFn_mk, ramIdx, v.2, I]
    rfl
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    have hm : multiplicity v.asIdeal I ≠ 0 := by
      intro h; exact hv (by rw [h, pow_zero])
    have hd : v.asIdeal ∣ I := by
      by_contra h; exact hm (multiplicity_eq_zero_of_not_dvd h)
    rw [hI, Ideal.dvd_span_singleton, ← resChar_eq_iff] at hd
    simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Function.Embedding.coeFn_mk]
    exact ⟨⟨v, hd⟩, rfl⟩

/-- $\sum_{v \mid p} [F_v : \mathbb{Q}_p] = [F : \mathbb{Q}]$. -/
@[kb "neukirch1999" "Ch. II, Prop. 8.3 [unverified]"]
theorem sum_finrank_Sp (q : ℕ) [hq : Fact q.Prime] :
    ∑ v : Sp F q, Module.finrank ℚ_[resChar v.1] (v.1.adicCompletion F) = Module.finrank ℚ F := by
  have h := prod_absNorm_pow_ramIdx (F := F) q
  have h' : ∏ v : Sp F q, q ^ Module.finrank ℚ_[resChar v.1] (v.1.adicCompletion F) =
      q ^ Module.finrank ℚ F := by
    rw [← h]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← resChar_pow_finrank]
    exact congrArg (· ^ _) v.2.symm
  rw [Finset.prod_pow_eq_pow_sum] at h'
  exact Nat.pow_right_injective hq.out.two_le h'

/-! ### The product $\prod_{v \mid p} F_v$ as a $\mathbb{Q}_p$-algebra -/

/-- $\mathbb{Q}_a \cong \mathbb{Q}_b$ for $a = b$. -/
def padicCast {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (h : a = b) : ℚ_[a] ≃+* ℚ_[b] := by
  subst h; exact RingEquiv.refl _

/-- $F_v$ for $v \mid p$, as a $\mathbb{Q}_p$-algebra for the fixed prime $p$ (a type synonym). -/
abbrev FvQ (q : ℕ) (v : Sp F q) : Type := v.1.adicCompletion F

variable (q : ℕ) [Fact q.Prime] (w : Sp F q)


instance : Algebra ℚ_[q] (FvQ q w) :=
  ((padicToV w.1).comp (padicCast w.2.symm).toRingHom).toAlgebra

lemma algebraMap_FvQ (c : ℚ_[q]) :
    algebraMap ℚ_[q] (FvQ q w) c = padicToV w.1 (padicCast w.2.symm c) := rfl

lemma continuous_padicCast {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (h : a = b) :
    Continuous (padicCast h) := by
  subst h; exact continuous_id

instance : ContinuousSMul ℚ_[q] (FvQ q w) := by
  refine ⟨?_⟩
  simp_rw [Algebra.smul_def, algebraMap_FvQ]
  exact (((continuous_padicToV w.1).comp (continuous_padicCast _)).comp continuous_fst).mul
    continuous_snd

instance : FiniteDimensional ℚ_[q] (FvQ q w) := by
  obtain ⟨w, rfl⟩ := w
  exact finiteDimensional_padic w

lemma finrank_FvQ : Module.finrank ℚ_[q] (FvQ q w) =
    Module.finrank ℚ_[resChar w.1] (w.1.adicCompletion F) := by
  obtain ⟨w, rfl⟩ := w
  rfl

lemma psiP_trace_FvQ (x : F) :
    psiP (Algebra.trace ℚ_[q] (FvQ q w) (algebraMap F (w.1.adicCompletion F) x)) =
      psiV w.1 (algebraMap F (w.1.adicCompletion F) x) := by
  obtain ⟨w, rfl⟩ := w
  rfl

/-! ### Weak approximation at the places above $p$ -/

omit [Fact q.Prime] in
/-- Small balls $\{x : v(x - c) \le \exp(-N)\}$ form a basis of neighbourhoods of $c$ in $F_v$. -/
lemma exists_N_of_mem_nhds {t : Set Fv} {c : Fv} (ht : t ∈ nhds c) :
    ∃ N : ℕ, ∀ x : Fv, Valued.v (x - c) ≤ exp (-(N : ℤ)) → x ∈ t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_ϖ_lt_one v)
  refine ⟨N, fun x hx => hball ?_⟩
  have hx' : x ∈ {x : Fv | Valued.v (x - c) ≤ exp (-(N : ℤ))} := hx
  rw [ballIndV_eq, Metric.mem_closedBall, zpow_natCast, norm_pow] at hx'
  exact Metric.mem_ball.mpr (hx'.trans_lt hN)

/-- **Approximation by integers at the places above $p$** (Chinese remainder theorem): for $y_v \in \mathcal O_v$
($v \mid p$) and $N$, there is $a \in \mathcal O_F$ with $v(y_v - a) \le \exp(-N)$ for all $v \mid p$. -/
theorem exists_int_approx_Sp (y : ∀ w : Sp F q, w.1.adicCompletion F) (hy : ∀ w, Valued.v (y w) ≤ 1)
    (N : ℕ) : ∃ a : 𝓞 F, ∀ w : Sp F q,
      Valued.v (y w - algebraMap F (w.1.adicCompletion F) (a : F)) ≤ exp (-(N : ℤ)) := by
  classical
  choose a ha using fun w : Sp F q => exists_int_approx_pow w.1 N (y w) (hy w)
  let s : Finset (HeightOneSpectrum (𝓞 F)) := (Finset.univ : Finset (Sp F q)).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hs : ∀ v ∈ s, resChar v = q := by
    intro v hv
    simp only [s, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hv
    obtain ⟨w, rfl⟩ := hv
    exact w.2
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => N)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => a ⟨v.1, hs v.1 v.2⟩)
  refine ⟨b, fun w => ?_⟩
  have hw : w.1 ∈ s := by simp [s]
  have h1 := hb w.1 hw
  have h2 : Valued.v (algebraMap F (w.1.adicCompletion F)
      (((b - a ⟨w.1, hs w.1 hw⟩ : 𝓞 F)) : F)) ≤ exp (-(N : ℤ)) := by
    rw [HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr h1
  have e : y w - algebraMap F (w.1.adicCompletion F) (b : F) =
      (y w - algebraMap F (w.1.adicCompletion F) (a w : F)) -
        algebraMap F (w.1.adicCompletion F) (((b - a ⟨w.1, hs w.1 hw⟩ : 𝓞 F)) : F) := by
    have : (⟨w.1, hs w.1 hw⟩ : Sp F q) = w := rfl
    rw [this]; push_cast; ring
  rw [e]
  refine (Valuation.map_sub _ _ _).trans (max_le (ha w) h2)

theorem _root_.Algebra.trace_pi' {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, FiniteDimensional R (A i)] (x : ∀ i, A i) :
    Algebra.trace R (∀ i, A i) x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let s : ∀ i, Module.Basis (Fin (Module.finrank R (A i))) R (A i) := fun i => Module.finBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis s), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace (s i), Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
  congr 2
  simp [Pi.mul_apply]

/-! ### $\mathbb{Q}_p \otimes F \cong \prod_{v \mid p} F_v$ and the trace -/

/-- $P = \prod_{v \mid p} F_v$, a $\mathbb{Q}_p$-algebra. -/
abbrev PQ := ∀ w : Sp F q, FvQ q w

/-- The diagonal embedding $F \to \prod_{v \mid p} F_v$. -/
def diagQ : F →+* PQ (F := F) q :=
  RingHom.pi fun w => (algebraMap F (w.1.adicCompletion F) : F →+* FvQ q w)

lemma diagQ_apply (x : F) (w : Sp F q) :
    diagQ q x w = (algebraMap F (w.1.adicCompletion F) x : FvQ q w) := rfl

lemma ratCast_smul_eq (r : ℚ) (z : PQ (F := F) q) : (r : ℚ_[q]) • z = diagQ q (r : F) * z := by
  funext w
  change algebraMap ℚ_[q] (FvQ q w) r * z w = _
  rw [algebraMap_FvQ, map_ratCast, map_ratCast]
  change _ = (algebraMap F (w.1.adicCompletion F) (r : F)) * z w
  rw [map_ratCast]

/-- The $\mathbb{Q}_p$-span of $\{\mathrm{diag}(b_j)\}$ for the basis $b$ = `Module.finBasis ℚ F`. -/
def WQ : Submodule ℚ_[q] (PQ (F := F) q) :=
  Submodule.span ℚ_[q] (Set.range fun j => diagQ q (Module.finBasis ℚ F j))

lemma diagQ_eq_sum (z : F) : diagQ q z = ∑ j, (((Module.finBasis ℚ F).repr z j : ℚ) : ℚ_[q]) •
    diagQ q (Module.finBasis ℚ F j) := by
  conv_lhs => rw [← (Module.finBasis ℚ F).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ratCast_smul_eq, ← map_mul, Rat.smul_def]

lemma diagQ_mem_WQ (z : F) : diagQ q z ∈ WQ (F := F) q := by
  rw [diagQ_eq_sum]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma isClosed_WQ : IsClosed (WQ (F := F) q : Set (PQ (F := F) q)) :=
  Submodule.closed_of_finiteDimensional _

lemma mem_WQ_of_integral (y : PQ (F := F) q)
    (hy : ∀ w : Sp F q, Valued.v (y w : w.1.adicCompletion F) ≤ 1) : y ∈ WQ (F := F) q := by
  classical
  rw [← SetLike.mem_coe, ← (isClosed_WQ q).closure_eq, mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose N hN using fun w : Sp F q => exists_N_of_mem_nhds w.1 (t := t w) (c := y w) (ht w)
  obtain ⟨a, ha⟩ := exists_int_approx_Sp q y hy (Finset.univ.sup N)
  refine ⟨diagQ q (a : F), hsub fun w _ => hN w _ ?_, diagQ_mem_WQ q _⟩
  rw [diagQ_apply, Valuation.map_sub_swap]
  refine (ha w).trans (exp_le_exp.mpr ?_)
  exact neg_le_neg (by exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ w))

lemma WQ_eq_top : WQ (F := F) q = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  have hq0 : ((q : ℕ) : ℚ_[q]) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  -- a power of `q` makes `y` integral at every `v ∣ q`
  have hk : ∀ w : Sp F q, ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Valued.v (((q : ℕ) : w.1.adicCompletion F) ^ m * y w) ≤ 1 := by
    intro w
    have hqv : Valued.v ((q : ℕ) : w.1.adicCompletion F) ≤ exp (-1 : ℤ) := by
      refine HN.valued_le_exp_neg_one w.1 ?_
      have : ((q : ℕ) : w.1.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (q : 𝓞 F)) := by
        simp
      rw [this, HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact (resChar_eq_iff w.1 q).mp w.2
    by_cases h0 : (y w : w.1.adicCompletion F) = 0
    · exact ⟨0, fun m _ => by rw [h0, mul_zero, map_zero]; exact zero_le⟩
    obtain ⟨k, hk⟩ := HN.exists_exp_eq w.1 h0
    refine ⟨k.toNat, fun m hm => ?_⟩
    rw [map_mul, map_pow, hk]
    calc Valued.v ((q : ℕ) : w.1.adicCompletion F) ^ m * exp k ≤ exp (-1 : ℤ) ^ m * exp k :=
          mul_le_mul_left (pow_le_pow_left₀ zero_le hqv m) _
      _ = exp (-(m : ℤ) + k) := by rw [← exp_nsmul, ← exp_add]; congr 1; simp
      _ ≤ 1 := by
          rw [← exp_zero, exp_le_exp]
          have : (k.toNat : ℤ) ≤ m := by exact_mod_cast hm
          linarith [Int.self_le_toNat k]
  choose k hk using hk
  set m := Finset.univ.sup k
  have hy' : ((q : ℕ) : ℚ_[q]) ^ m • y ∈ WQ (F := F) q := by
    refine mem_WQ_of_integral q _ fun w => ?_
    have e : (((q : ℕ) : ℚ_[q]) ^ m • y) w = (((q : ℕ) : w.1.adicCompletion F) ^ m * y w :) := by
      change algebraMap ℚ_[q] (FvQ q w) _ * y w = _
      rw [algebraMap_FvQ, map_pow, map_pow, map_natCast, map_natCast]
    rw [e]
    exact hk w m (Finset.le_sup (Finset.mem_univ w))
  have := Submodule.smul_mem _ ((((q : ℕ) : ℚ_[q]) ^ m)⁻¹) hy'
  rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hq0), one_smul] at this

lemma finrank_PQ : Module.finrank ℚ_[q] (PQ (F := F) q) = Module.finrank ℚ F := by
  rw [Module.finrank_pi_fintype, ← sum_finrank_Sp (F := F) q]
  exact Finset.sum_congr rfl fun w _ => finrank_FvQ q w

/-- The $\mathbb{Q}_p$-basis $\{\mathrm{diag}(b_j)\}$ of $\prod_{v \mid p} F_v$. -/
def basisPQ : Module.Basis (Fin (Module.finrank ℚ F)) ℚ_[q] (PQ (F := F) q) :=
  basisOfTopLeSpanOfCardEqFinrank (fun j => diagQ q (Module.finBasis ℚ F j))
    (by rw [← WQ, WQ_eq_top]) (by rw [Fintype.card_fin, finrank_PQ])

lemma basisPQ_repr_diagQ (z : F) (j : Fin (Module.finrank ℚ F)) :
    (basisPQ q).repr (diagQ q z) j = (((Module.finBasis ℚ F).repr z j : ℚ) : ℚ_[q]) := by
  have h : diagQ q z = ∑ j, (((Module.finBasis ℚ F).repr z j : ℚ) : ℚ_[q]) • basisPQ q j := by
    rw [diagQ_eq_sum]
    simp [basisPQ, coe_basisOfTopLeSpanOfCardEqFinrank]
  rw [h, Module.Basis.repr_sum_self]

/-- **Global trace = sum of local traces:** $\operatorname{Tr}_{F/\mathbb{Q}}(x) = \operatorname{Tr}_{P/\mathbb{Q}_p}(\mathrm{diag}\,x)$. -/
@[kb "neukirch1999" "Ch. II, Cor. 8.4 [unverified]"]
theorem trace_PQ_diagQ (x : F) :
    Algebra.trace ℚ_[q] (PQ (F := F) q) (diagQ q x) = ((Algebra.trace ℚ F x : ℚ) : ℚ_[q]) := by
  rw [Algebra.trace_eq_matrix_trace (basisPQ q), Algebra.trace_eq_matrix_trace (Module.finBasis ℚ F),
    Matrix.trace, Matrix.trace, Rat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [show basisPQ q j = diagQ q (Module.finBasis ℚ F j) by
    simp [basisPQ, coe_basisOfTopLeSpanOfCardEqFinrank], ← map_mul, basisPQ_repr_diagQ]

lemma addChar_map_sum {ι A M : Type*} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M)
    (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- **Local–global compatibility of the standard characters at $p$:** for $x \in F$,
$\prod_{v \mid p} \psi_v(x) = \psi_p(\operatorname{Tr}_{F/\mathbb{Q}} x)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 and §4.1 [unverified]"]
theorem prod_psiV_Sp (x : F) :
    ∏ w : Sp F q, psiV w.1 (algebraMap F (w.1.adicCompletion F) x) =
      psiP (((Algebra.trace ℚ F x : ℚ)) : ℚ_[q]) := by
  classical
  rw [← trace_PQ_diagQ, Algebra.trace_pi', addChar_map_sum]
  exact Finset.prod_congr rfl fun w _ => (psiP_trace_FvQ q w x).symm

end

end QuadFormsKB.Analysis
