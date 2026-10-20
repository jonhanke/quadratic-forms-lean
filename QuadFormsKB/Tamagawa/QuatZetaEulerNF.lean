/-
# The zeta function of a maximal order for every class number: Euler product and residue

**Layer:** $F$ a number field (any class number), $D=(a,b)_F$ ($ab \ne 0$), $\mathcal O \subset D$ a maximal order.
Basis-free counterpart of `QuatZetaEuler`: with $c(\mathfrak n) = \#\{J : \operatorname{nrd}J = \mathfrak n\}$ (`idealCountO`),
$$\sum_{\mathfrak n}c(\mathfrak n)\,N\mathfrak n^{-s} = \zeta_F(s)\,\zeta_F(s-1)\prod_{\mathfrak p\in\mathrm{Ram}_f(D)}(1 - N\mathfrak p^{1-s})\qquad(s>2)$$
(`Gen.hasSum_zetaO`) and its residue at $s = 2$ (`Gen.tendsto_sub_mul_zetaO`). The PID file passes through principal ideals $(n)$; here
every integral ideal $\mathfrak n$ is used directly: `Gen.finprod_zetaTerm_ideal` ($\prod_vf_v(\operatorname{ord}_v\mathfrak n) = c(\mathfrak n)N\mathfrak n^{-s}$,
from `card_ideal_nrd_eq_N`), and `exists_eq_ideal_of_count_nonneg` (a fractional ideal with nonnegative valuations is an integral ideal).

Sources: Voight, *Quaternion Algebras* (2021), (26.3.2), (26.3.12), Cor. 26.4.7, Thm. 26.5.4 (proof).
-/
import QuadFormsKB.Tamagawa.QuatZetaEuler
import QuadFormsKB.Tamagawa.IdealLocalGlobalNF

open NumberField IsDedekindDomain Quaternion Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF QuadFormsKB.Tamagawa QuadFormsKB.NFEuler QuadFormsKB.GlobalZeta

section CountNF

variable {F : Type} [Field F] [NumberField F]

open FractionalIdeal in
/-- `FractionalIdeal.count` of an integral ideal is the multiplicity `cI`. -/
theorem count_coe_eq_cI (v : HeightOneSpectrum (𝓞 F)) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) :
    count F v (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = (cI v 𝔫 : ℤ) :=
  count_coe F v h𝔫

open FractionalIdeal in
/-- **A fractional ideal with nonnegative valuations is integral** (any class number): it is the coercion of an ideal of $\mathcal O_F$. -/
theorem exists_eq_ideal_of_count_nonneg (𝔟 : IdeleClass.FracIdeal F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), 0 ≤ count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
  set I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F := (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  have hI0 : I ≠ 0 := 𝔟.ne_zero
  have hle : I ≤ 1 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F).zero_mem
    have hsp : spanSingleton (nonZeroDivisors (𝓞 F)) x ≤ I := by
      rw [spanSingleton_le_iff_mem]; exact hx
    have hcount : ∀ v : HeightOneSpectrum (𝓞 F), 0 ≤ count F v (spanSingleton (nonZeroDivisors (𝓞 F)) x) :=
      fun v => (h v).trans (count_mono F v (spanSingleton_ne_zero_iff.mpr hx0) hsp)
    have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F x ≤ 1 := by
      intro v
      have h1 := valued_eq_exp_neg_count v hx0
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      change Valued.v (algebraMap F (v.adicCompletion F) x) ≤ 1
      rw [h1, ← WithZero.exp_zero, WithZero.exp_le_exp]
      linarith [hcount v]
    obtain ⟨n, hn⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) x hval
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨n, hn⟩
  obtain ⟨𝔫, h𝔫⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  refine ⟨𝔫, fun h0 => hI0 ?_, h𝔫.symm⟩
  rw [← h𝔫, h0, FractionalIdeal.coeIdeal_bot]

end CountNF

namespace Gen

section Zeta

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

theorem aLoc_zero (v : HeightOneSpectrum (𝓞 F)) : aLoc a b v 0 = 1 := by
  unfold aLoc; split_ifs <;> simp


theorem mem_ramFin (ha : a ≠ 0) (hb : b ≠ 0) {v : HeightOneSpectrum (𝓞 F)} :
    v ∈ ramFin ha hb ↔ IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) := by
  simp [ramFin]


theorem zetaTerm_natCast (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    zetaTerm a b s v (k : ℤ) = (aLoc a b v k : ℝ) * ((normP v : ℝ) ^ (-s)) ^ k := by
  simp [zetaTerm]


open Classical in
/-- **The local factor as a sum over $\mathbb Z$.** -/
theorem hasSum_zetaTerm (ha : a ≠ 0) (hb : b ≠ 0) {s : ℝ} (hs : 1 < s) (v : HeightOneSpectrum (𝓞 F)) :
    HasSum (zetaTerm a b s v) ((1 - (normP v : ℝ) ^ (-s))⁻¹ * (1 - (normP v : ℝ) ^ (-(s - 1)))⁻¹ *
      (if v ∈ ramFin ha hb then 1 - (normP v : ℝ) ^ (-(s - 1)) else 1)) := by
  classical
  have hq : (1 : ℝ) ≤ normP v := by exact_mod_cast (le_trans (by norm_num) (two_le_normP v))
  have hq0 : (0 : ℝ) < normP v := by linarith
  set X := (normP v : ℝ) ^ (-s)
  have hX : 0 ≤ X := Real.rpow_nonneg hq0.le _
  have hqX : (normP v : ℝ) * X = (normP v : ℝ) ^ (-(s - 1)) := by
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add hq0, Real.rpow_one]
  have hqX1 : (normP v : ℝ) * X < 1 := by
    rw [hqX]; exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Nat.lt_of_lt_of_le one_lt_two
      (two_le_normP v))) (by linarith)
  have hX1 : X < 1 := lt_of_le_of_lt (by nlinarith) hqX1
  -- reduce to a sum over ℕ
  have hsupp : ∀ j ∉ Set.range (fun k : ℕ => (k : ℤ)), zetaTerm a b s v j = 0 := by
    intro j hn
    have : ¬ 0 ≤ j := fun h0 => hn ⟨j.toNat, Int.toNat_of_nonneg h0⟩
    simp [zetaTerm, this]
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff hsupp]
  simp only [Function.comp_def, zetaTerm_natCast]
  by_cases hram : v ∈ ramFin ha hb
  · have hr : IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) :=
      (mem_ramFin ha hb).1 hram
    have h1 : ∀ k, (aLoc a b v k : ℝ) = 1 := fun k => by simp [aLoc, hr]
    simp only [h1, if_pos hram]
    convert hasSum_localFactor_ramified hX hX1 using 1
    rw [← hqX, inv_mul_cancel_right₀ (sub_ne_zero.2 (ne_of_lt hqX1).symm)]
  · have hr : ¬ IsRamifiedAt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F b) (NFPlace.finite v) :=
      fun h => hram ((mem_ramFin ha hb).2 h)
    have h1 : ∀ k, (aLoc a b v k : ℝ) = ∑ i ∈ Finset.range (k + 1), (normP v : ℝ) ^ i := fun k => by
      simp [aLoc, hr]
    simp only [h1, if_neg hram, mul_one]
    convert hasSum_localFactor_split hq hX hqX1 using 1
    rw [hqX, mul_comm]


open FractionalIdeal in
/-- The summand at the integral ideal $\mathfrak n$: $\prod_vf_v(\operatorname{ord}_v\mathfrak n) = c(\mathfrak n)\,N(\mathfrak n)^{-s}$. -/
theorem finprod_zetaTerm_ideal (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) (s : ℝ)
    {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) :
    ∏ᶠ v, zetaTerm a b s v (count F v (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) =
      (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s) := by
  classical
  obtain ⟨n, hn𝔫, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔫
  set S := primeSupport hn
  have hord0 : ∀ v ∉ S, cI v 𝔫 = 0 := fun v hv =>
    cI_eq_zero_of_mem_not_mem h𝔫 hn𝔫 fun h => hv ((mem_primeSupport hn).2 h)
  have e1 : ∏ᶠ v, zetaTerm a b s v (count F v (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) =
      ∏ v ∈ S, (aLoc a b v (cI v 𝔫) : ℝ) * ((normP v : ℝ) ^ (-s)) ^ cI v 𝔫 := by
    simp_rw [count_coe_eq_cI _ h𝔫, zetaTerm_natCast]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS; apply hv
    show (aLoc a b v (cI v 𝔫) : ℝ) * ((normP v : ℝ) ^ (-s)) ^ cI v 𝔫 = 1
    rw [hord0 v hvS, aLoc_zero]; simp
  have e2 : (idealCountO O 𝔫 : ℝ) = ∏ v ∈ S, (aLoc a b v (cI v 𝔫) : ℝ) := by
    rw [idealCountO, card_ideal_nrd_eq_N ha hb hO h𝔫 hn hn𝔫, Nat.cast_prod]
    rfl
  have e3 : (Ideal.absNorm 𝔫 : ℝ) = ∏ v ∈ S, (normP v : ℝ) ^ cI v 𝔫 := by
    have hI0 : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
      rw [Ne, coeIdeal_eq_zero]; exact h𝔫
    have h1 := idealNorm_eq_finprod F (Units.mk0 _ hI0)
    have h2 : IdeleClass.idealNorm F (Units.mk0 _ hI0) = (Ideal.absNorm 𝔫 : ℝ) := by
      rw [IdeleClass.idealNorm, Units.val_mk0, coeIdeal_absNorm]; push_cast; rfl
    rw [← h2, h1]
    simp_rw [Units.val_mk0, count_coe_eq_cI _ h𝔫, zpow_natCast]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS; apply hv
    show (Ideal.absNorm v.asIdeal : ℝ) ^ cI v 𝔫 = 1
    rw [hord0 v hvS, pow_zero]
  rw [e1, e2, e3, Finset.prod_mul_distrib, ← Real.finsetProd_rpow _ _ (fun v _ => by positivity)]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul (by positivity),
    Real.rpow_natCast]

/-- **The Euler product of the zeta function of a maximal order** ($\mathcal O_F$ a PID, $ab \ne 0$, real $s > 2$):
$$\sum_{\mathfrak n}c(\mathfrak n)\,N\mathfrak n^{-s} = \zeta_F(s)\,\zeta_F(s-1)\prod_{\mathfrak p\in\mathrm{Ram}_f(D)}(1 - N\mathfrak p^{1-s}),$$
$c(\mathfrak n)$ = `idealCountO O 𝔫` the number of left ideals of reduced norm $\mathfrak n$.

Source: Voight 2021, (26.3.2), (26.3.12), Cor. 26.4.7 (there in the variable $2s$). -/
@[kb "voight2021" "(26.3.12); Cor. 26.4.7"]
theorem hasSum_zetaO (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {s : ℝ} (hs : 2 < s) :
    HasSum (fun 𝔫 : Ideal (𝓞 F) => (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s))
      (dedekindZetaR F s * dedekindZetaR F (s - 1) *
        ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(s - 1)))) := by
  classical
  have hs1 : 1 < s := by linarith
  have hs2 : 1 < s - 1 := by linarith
  set P := dedekindZetaR F s * dedekindZetaR F (s - 1) * ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(s - 1)))
  have hloc := hasSum_zetaTerm (a := a) (b := b) ha hb hs1
  have hf0 : ∀ v j, 0 ≤ zetaTerm a b s v j := by
    intro v j; unfold zetaTerm; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)
    · exact le_rfl
  have hf1 : ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))), zetaTerm a b s v 0 = 1 := fun v _ => by
    simp [zetaTerm, aLoc_zero]
  have hP : HasProd (fun v => ∑' j, zetaTerm a b s v j) P := by
    have e : (fun v => ∑' j, zetaTerm a b s v j) = fun v =>
        (1 - (normP v : ℝ) ^ (-s))⁻¹ * (1 - (normP v : ℝ) ^ (-(s - 1)))⁻¹ *
          (if v ∈ ramFin ha hb then 1 - (normP v : ℝ) ^ (-(s - 1)) else 1) := funext fun v => (hloc v).tsum_eq
    rw [e]
    refine ((hasProd_dedekindZeta hs1).mul (hasProd_dedekindZeta hs2)).mul ?_
    have h : HasProd (fun v => if v ∈ ramFin ha hb then 1 - (normP v : ℝ) ^ (-(s - 1)) else 1)
        (∏ v ∈ ramFin ha hb, if v ∈ ramFin ha hb then 1 - (normP v : ℝ) ^ (-(s - 1)) else 1) :=
      hasProd_prod_of_ne_finset_one (fun v hv => if_neg hv)
    convert h using 1
    exact (Finset.prod_congr rfl fun v hv => if_pos hv).symm
  have hE := hasSum_finsupp_finprod (zetaTerm a b s) hf0 ∅ hf1 (fun v => (hloc v).summable) hP
  have hEb : HasSum (fun 𝔟 : IdeleClass.FracIdeal F =>
      ∏ᶠ v, zetaTerm a b s v (FractionalIdeal.count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))) P := by
    have := (fracIdealEquiv F).hasSum_iff.mpr hE
    convert this using 2 with 𝔟
    simp only [Function.comp_apply, fracIdealEquiv_apply]
  -- restrict to the integral ideals
  let φ : {𝔫 : Ideal (𝓞 F) // 𝔫 ≠ ⊥} → IdeleClass.FracIdeal F := fun 𝔫 =>
    Units.mk0 ((𝔫.1 : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
      (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact 𝔫.2)
  have hφinj : Function.Injective φ := by
    intro x y h
    exact Subtype.ext (FractionalIdeal.coeIdeal_injective (congrArg Units.val h))
  have hsupp : ∀ 𝔟 ∉ Set.range φ, ∏ᶠ v, zetaTerm a b s v
      (FractionalIdeal.count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) = 0 := by
    intro 𝔟 h𝔟
    by_contra hne
    have hfin : (Function.mulSupport fun v => zetaTerm a b s v
        (FractionalIdeal.count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))).Finite := by
      refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors
        (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))).subset fun v hv => ?_
      intro h0; apply hv; simp only at h0 ⊢; rw [h0]; exact hf1 v (Finset.notMem_empty v)
    have hnn : ∀ v, 0 ≤ FractionalIdeal.count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      intro v
      by_contra hneg
      exact hne (finprod_eq_zero _ v (by simp [zetaTerm, hneg]) hfin)
    obtain ⟨𝔫, h𝔫, hbn⟩ := exists_eq_ideal_of_count_nonneg 𝔟 hnn
    exact h𝔟 ⟨⟨𝔫, h𝔫⟩, Units.ext hbn.symm⟩
  have h1 := (hφinj.hasSum_iff hsupp).2 hEb
  have hterm : ∀ 𝔫 : {𝔫 : Ideal (𝓞 F) // 𝔫 ≠ ⊥}, (fun 𝔟 : IdeleClass.FracIdeal F => ∏ᶠ v, zetaTerm a b s v
      (FractionalIdeal.count F v (𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))) (φ 𝔫) =
      (idealCountO O 𝔫.1 : ℝ) * (Ideal.absNorm 𝔫.1 : ℝ) ^ (-s) := by
    rintro ⟨𝔫, h𝔫⟩
    exact finprod_zetaTerm_ideal ha hb hO s h𝔫
  have h2 : HasSum (fun 𝔫 : {𝔫 : Ideal (𝓞 F) // 𝔫 ≠ ⊥} =>
      (idealCountO O 𝔫.1 : ℝ) * (Ideal.absNorm 𝔫.1 : ℝ) ^ (-s)) P := by
    convert h1 using 1; funext 𝔫; exact (hterm 𝔫).symm
  refine (Subtype.val_injective.hasSum_iff fun 𝔫 h𝔫 => ?_).1 h2
  have : 𝔫 = ⊥ := by by_contra h; exact h𝔫 ⟨⟨𝔫, h⟩, rfl⟩
  subst this
  rw [Ideal.absNorm_bot, Nat.cast_zero, Real.zero_rpow (by linarith), mul_zero]

/-- $\zeta_F$ is continuous at real $s_0 > 1$ (an $L$-series inside its half-plane of absolute convergence). -/
theorem continuousAt_dedekindZetaR {s₀ : ℝ} (hs₀ : 1 < s₀) : ContinuousAt (dedekindZetaR F) s₀ := by
  set t : ℝ := (1 + s₀) / 2
  have ht : 1 < t := by simp only [t]; linarith
  have habs : LSeries.abscissaOfAbsConv (fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℂ)) <
      ((s₀ : ℂ)).re := by
    refine lt_of_le_of_lt ((lSeriesSummable_dedekindZeta (F := F) ht).abscissaOfAbsConv_le) ?_
    simp only [Complex.ofReal_re, t]
    exact_mod_cast (by linarith : (1 + s₀) / 2 < s₀)
  have hd := (LSeries_hasDerivAt habs).continuousAt
  have hc : ContinuousAt (fun s : ℝ => dedekindZeta F (s : ℂ)) s₀ :=
    hd.comp Complex.continuous_ofReal.continuousAt
  exact (Complex.continuous_re.continuousAt).comp hc

/-- **The residue of $\zeta_{\mathcal O}$ at $s = 2$** ($\mathcal O_F$ a PID, $ab \ne 0$):
$$\lim_{s\to2^+}(s-2)\sum_{\mathfrak n}c(\mathfrak n)N\mathfrak n^{-s} = \rho_F\,\zeta_F(2)\prod_{\mathfrak p\in\mathrm{Ram}_f(D)}(1 - N\mathfrak p^{-1}),$$
$\rho_F$ = `dedekindZeta_residue F` (the residue of $\zeta_F$ at $1$).

Source: Voight 2021, proof of Thm. 26.5.4 (the residue of $\zeta_{\mathcal O}$; there in the variable $2s$, at $s = 1$). -/
@[kb "voight2021" "Thm. 26.5.4 (proof: residue of ζ_O)"]
theorem tendsto_sub_mul_zetaO (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) :
    Tendsto (fun s : ℝ => (s - 2) * ∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s))
      (𝓝[>] 2) (𝓝 (dedekindZeta_residue F * dedekindZetaR F 2 *
        ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))))) := by
  -- (s - 2) ζ_F(s - 1) → ρ_F
  have h1 : Tendsto (fun s : ℝ => (s - 2) * dedekindZetaR F (s - 1)) (𝓝[>] 2) (𝓝 (dedekindZeta_residue F)) := by
    have hmap : Tendsto (fun s : ℝ => s - 2) (𝓝[>] 2) (𝓝[>] 0) := by
      have hc : Tendsto (fun s : ℝ => s - 2) (𝓝 2) (𝓝 (2 - 2)) :=
        ((continuous_id.sub continuous_const : Continuous fun s : ℝ => s - 2).tendsto 2)
      rw [sub_self] at hc
      refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.2 (Set.mem_Ioi.1 hs)
    have := (tendsto_mul_dedekindZetaR_one_add (F := F)).comp hmap
    refine this.congr fun s => ?_
    simp only [Function.comp_apply]
    congr 2; ring
  -- ζ_F(s) → ζ_F(2)
  have h2 : Tendsto (fun s : ℝ => dedekindZetaR F s) (𝓝[>] 2) (𝓝 (dedekindZetaR F 2)) :=
    (continuousAt_dedekindZetaR (by norm_num)).tendsto.mono_left nhdsWithin_le_nhds
  -- the finite product
  have h3 : Tendsto (fun s : ℝ => ∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(s - 1)))) (𝓝[>] 2)
      (𝓝 (∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ))))) := by
    refine (tendsto_finsetProd _ fun v _ => ?_).mono_left nhdsWithin_le_nhds
    have hq : (0 : ℝ) < normP v := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (two_le_normP v))
    have : ContinuousAt (fun s : ℝ => 1 - (normP v : ℝ) ^ (-(s - 1))) 2 :=
      continuousAt_const.sub ((Real.continuousAt_const_rpow hq.ne').comp
        ((continuous_id.sub continuous_const).neg.continuousAt))
    convert this.tendsto using 2; norm_num
  have h := (h1.mul h2).mul h3
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [(hasSum_zetaO ha hb hO hs).tsum_eq]
  ring

end Zeta
end Gen
end QuadFormsKB.QuatOrder
