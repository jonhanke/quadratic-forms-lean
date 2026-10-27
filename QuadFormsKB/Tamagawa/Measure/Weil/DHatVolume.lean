import QuadFormsKB.Tamagawa.Measure.Weil.SL2Tamagawa
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicLattice
import QuadFormsKB.Analysis.DifferentLocal

/-!
# The self-dual volume of the inverse different $\hat{\mathfrak d}^{-1}$

Let $F$ be a number field and $\mu_f$ the self-dual Haar measure on the finite adeles $\mathbb A_f$ (`muFin`), so that
$\mu_f(\hat{\mathcal O}) = |d_F|^{-1/2}$ (`muFin_OHat`). This file proves
$$\mu_f(\hat{\mathcal O})\cdot\mu_f(\hat{\mathfrak d}^{-1}) = 1,$$
i.e. $\mu_f(\hat{\mathfrak d}^{-1}) = |d_F|^{1/2}$ (`muFin_OHat_mul_muFin_DHat`), and the same for the $\iota$-fold
products (`muFinVec_OHatVec_mul_DHatVec`).

**Proof.** The open subgroup $U = \hat{\mathfrak d}^{-1}\subseteq\mathbb A_f$ (`DHatSub`, open because it contains
$\hat{\mathcal O}$) cuts out from $F$ the lattice $\mathfrak d^{-1}$ (`algebraMap_mem_DHat_iff`). Take an
$\mathbb R$-basis $b$ of $F_\infty$ that is a $\mathbb Z$-basis of $\mathfrak d^{-1}$ (Mathlib's
`fractionalIdealLatticeBasis`). The covolume theorem `fundamentalDomain_mul_eq_one` (the quotient $\mathbb A_F/F$ has
volume $1$) gives $\mu_\infty(P_b)\,\mu_f(U) = 1$. The self-dual covolume of the ideal lattice is
$N(\mathfrak d^{-1})\,|d_F|^{1/2} = |d_F|^{-1/2}$ (`selfDual_covolume_idealLattice` and
$N(\mathfrak d) = |d_F|$ from Mathlib's `absNorm_differentIdeal`), so $\mu_\infty(P_b) = \mu_f(\hat{\mathcal O})$.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding
open scoped ENNReal NNReal Pointwise Classical nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F
local notation "AF" => FiniteAdeleRing (𝓞 F) F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-! ### $\hat{\mathfrak d}^{-1}$ as an open subgroup -/

/-- $\hat{\mathfrak d}^{-1}$ as an additive subgroup of $\mathbb A_f$. -/
def DHatSub : AddSubgroup AF where
  carrier := DHat
  add_mem' := add_mem_DHat
  zero_mem' := zero_mem_DHat
  neg_mem' := fun {a} ha v => by
    show Valued.v (-(a v)) ≤ _
    rw [Valuation.map_neg]; exact ha v

theorem coe_DHatSub : (DHatSub (F := F) : Set AF) = DHat := rfl

/-- $\hat{\mathcal O}\subseteq\hat{\mathfrak d}^{-1}$ (the exponents $d_v$ are natural numbers). -/
theorem OHat_subset_DHat : (OHat : Set AF) ⊆ DHat := fun a ha v => by
  have h1 : Valued.v (a v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (ha v)
  refine h1.trans ?_
  rw [← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le _)

/-- $\hat{\mathfrak d}^{-1}$ is open in $\mathbb A_f$. -/
theorem isOpen_DHat : IsOpen (DHat : Set AF) := by
  have : IsOpen (DHatSub (F := F) : Set AF) :=
    AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (isOpen_OHat.mem_nhds zero_mem_OHat) OHat_subset_DHat)
  exact this

variable {ι : Type}

variable (F) in
/-- $\{c\in\mathbb A_f^\iota : c_i\in\hat{\mathfrak d}^{-1}\ \forall i\}$ as an additive subgroup. -/
def DHatVecSub (ι : Type) : AddSubgroup (ι → AF) where
  carrier := {c | ∀ i, c i ∈ DHat}
  add_mem' := fun ha hb i => add_mem_DHat (ha i) (hb i)
  zero_mem' := fun _ => zero_mem_DHat
  neg_mem' := fun {_} ha i => (DHatSub (F := F)).neg_mem (ha i)

theorem isOpen_DHatVec [Finite ι] : IsOpen {c : ι → AF | ∀ i, c i ∈ DHat} := by
  have : {c : ι → AF | ∀ i, c i ∈ DHat} = Set.univ.pi fun _ => DHat := by ext; simp
  rw [this]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_DHat

theorem measurableSet_DHatVec [Finite ι] : MeasurableSet {c : ι → AF | ∀ i, c i ∈ DHat} :=
  isOpen_DHatVec.measurableSet

/-! ### The covolume computation -/

variable (F) in
/-- The inverse different $\mathfrak d^{-1}$ as a unit of the group of fractional ideals. -/
def invDifferent : FIˣ := Units.mk0 (FractionalIdeal.dual ℤ ℚ (1 : FI)) Analysis.dual_one_ne_zero

theorem coe_invDifferent : ((invDifferent F : FIˣ) : FI) = FractionalIdeal.dual ℤ ℚ (1 : FI) := rfl

/-- $N(\mathfrak d^{-1}) = |d_F|^{-1}$. -/
theorem absNorm_dual_one :
    FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ (1 : FI)) = ((discr F).natAbs : ℚ)⁻¹ := by
  have := congrArg (FractionalIdeal.absNorm (R := 𝓞 F) (K := F))
    (coeIdeal_differentIdeal ℤ ℚ F (𝓞 F))
  rw [FractionalIdeal.coeIdeal_absNorm, NumberField.absNorm_differentIdeal F (𝓞 F), map_inv₀] at this
  rw [← inv_inv (FractionalIdeal.absNorm _), ← this]

variable (F) in
/-- The $\mathbb R$-basis of $F_\infty^{\mathrm{Fin}\,1}$ coming from a $\mathbb Z$-basis of $\mathfrak d^{-1}$. -/
def dualBasis1 : Module.Basis (Module.Free.ChooseBasisIndex ℤ (invDifferent F : FI)) ℝ (Fin 1 → V) :=
  (fractionalIdealLatticeBasis F (invDifferent F)).map (LinearEquiv.funUnique (Fin 1) ℝ V).symm

theorem span_dualBasis1 :
    Submodule.span ℤ (Set.range (dualBasis1 F)) = adelicLat (DHatVecSub F (Fin 1)) := by
  ext z
  rw [mem_adelicLat]
  have hr : Set.range (dualBasis1 F) =
      ((LinearEquiv.funUnique (Fin 1) ℝ V).symm.toLinearMap.restrictScalars ℤ) ''
        Set.range (fractionalIdealLatticeBasis F (invDifferent F)) := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Submodule.map_span, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have := (mem_span_fractionalIdealLatticeBasis F (invDifferent F)).mp hy
    obtain ⟨x, hx, rfl⟩ := this
    refine ⟨fun _ => x, fun i => ?_, ?_⟩
    · exact (algebraMap_mem_DHat_iff x).mpr hx
    · funext i; rfl
  · rintro ⟨ξ, hξ, rfl⟩
    refine ⟨mixedEmbedding F (ξ 0), (mem_span_fractionalIdealLatticeBasis F (invDifferent F)).mpr
      ⟨ξ 0, (algebraMap_mem_DHat_iff _).mp (hξ 0), rfl⟩, ?_⟩
    funext i
    have : i = 0 := Subsingleton.elim _ _
    subst this; rfl

theorem fundamentalDomain_dualBasis1 :
    ZSpan.fundamentalDomain (dualBasis1 F) =
      Set.univ.pi fun _ => ZSpan.fundamentalDomain (fractionalIdealLatticeBasis F (invDifferent F)) := by
  ext m
  simp only [ZSpan.mem_fundamentalDomain, Set.mem_univ_pi, dualBasis1]
  constructor
  · intro h j i
    have : j = 0 := Subsingleton.elim _ _
    subst this; simpa using h i
  · intro h i; simpa using h 0 i

/-- $\mu_\infty(P_b) = |d_F|^{-1/2}$ for the fundamental parallelotope of $\mathfrak d^{-1}$. -/
theorem muInfVec_dualBasis1 :
    muInfVec F (Fin 1) (ZSpan.fundamentalDomain (dualBasis1 F)) = ENNReal.ofReal (ohatVol F) := by
  rw [fundamentalDomain_dualBasis1, muInfVec, Measure.pi_pi, Fin.prod_univ_one, Analysis.selfDualInf,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hfd := ZLattice.covolume_eq_measure_fundamentalDomain (mixedEmbedding.idealLattice F (invDifferent F))
    (volume : Measure V) (fundamentalDomain_idealLattice F (invDifferent F))
  have hcov := Analysis.selfDual_covolume_idealLattice (F := F) (invDifferent F)
  rw [coe_invDifferent, absNorm_dual_one] at hcov
  have hfin : (volume : Measure V)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis F (invDifferent F))) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hv : (volume : Measure V)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis F (invDifferent F))) =
      ENNReal.ofReal (ZLattice.covolume (mixedEmbedding.idealLattice F (invDifferent F))) := by
    rw [hfd, Measure.real, ENNReal.ofReal_toReal hfin]
  have h2 : (((2 : NNReal) ^ NumberField.InfinitePlace.nrComplexPlaces F : NNReal) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [h2, hv, ← ENNReal.ofReal_mul (by positivity), hcov]
  congr 1
  have hd : (0 : ℝ) < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
  have hs : 0 < Real.sqrt |(discr F : ℝ)| := Real.sqrt_pos.mpr hd
  have hsq := Real.mul_self_sqrt hd.le
  have hc : (((discr F).natAbs : ℚ)⁻¹ : ℚ) = ((|(discr F : ℝ)|)⁻¹ : ℝ) := by
    push_cast [Nat.cast_natAbs, Int.cast_abs]; rfl
  rw [hc, ohatVol]
  field_simp
  nlinarith [hsq]

theorem muFinVec_DHatVec_fin1 :
    muFinVec F (Fin 1) {c : Fin 1 → AF | ∀ i, c i ∈ DHat} = muFin F DHat := by
  have : {c : Fin 1 → AF | ∀ i, c i ∈ DHat} = Set.univ.pi fun _ => DHat := by ext; simp
  rw [this, muFinVec, Measure.pi_pi, Fin.prod_univ_one]

/-- **$\mu_f(\hat{\mathcal O})\,\mu_f(\hat{\mathfrak d}^{-1}) = 1$**, i.e. $\mu_f(\hat{\mathfrak d}^{-1}) = |d_F|^{1/2}$
for the self-dual measure $\mu_f$ on the finite adeles of a number field $F$ (the covolume of $F\subset\mathbb A_F$ is $1$
and $N(\mathfrak d^{-1}) = |d_F|^{-1}$). Unconditional. -/
theorem muFin_OHat_mul_muFin_DHat : muFin F OHat * muFin F (DHat (F := F)) = 1 := by
  have h := fundamentalDomain_mul_eq_one (DHatVecSub F (Fin 1)) (dualBasis1 F) (span_dualBasis1)
    (by
      have := isOpen_DHatVec (F := F) (ι := Fin 1)
      exact this)
  rw [muInfVec_dualBasis1] at h
  rw [muFin_OHat]
  rw [← muFinVec_DHatVec_fin1]
  exact h

theorem muFin_DHat_ne_zero : muFin F (DHat (F := F)) ≠ 0 := by
  intro h
  have := muFin_OHat_mul_muFin_DHat (F := F)
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem muFin_DHat_ne_top : muFin F (DHat (F := F)) ≠ ⊤ := by
  intro h
  have := muFin_OHat_mul_muFin_DHat (F := F)
  rw [h, muFin_OHat, ENNReal.mul_top (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'] at this
  exact ENNReal.top_ne_one this

/-- The $\iota$-fold version: $\mu_f^\iota(\hat{\mathcal O}^\iota)\,\mu_f^\iota((\hat{\mathfrak d}^{-1})^\iota) = 1$. -/
theorem muFinVec_OHatVec_mul_DHatVec [Fintype ι] :
    muFinVec F ι OHatVec * muFinVec F ι {c : ι → AF | ∀ i, c i ∈ DHat} = 1 := by
  have : {c : ι → AF | ∀ i, c i ∈ DHat} = Set.univ.pi fun _ => DHat := by ext; simp
  rw [this, muFinVec_OHatVec, muFinVec, Measure.pi_pi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun _ _ => muFin_OHat_mul_muFin_DHat

/-- The valuation at `v` of $N(v)^k$ is at most $\exp(-k)$. -/
theorem valued_absNorm_pow_le (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    Valued.v (((Ideal.absNorm v.asIdeal ^ k : ℕ) : v.adicCompletion F)) ≤ WithZero.exp (-(k : ℤ)) := by
  have h1 : Valued.v (((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F)
        = algebraMap F _ (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) := by simp
    rw [this, HN.valued_algebraMap]
    have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hm
    generalize v.valuation F (algebraMap (𝓞 F) F ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)) = x at this ⊢
    rcases eq_or_ne x 0 with rfl | hx
    · exact zero_le
    have h2 : WithZero.log x < 0 := (WithZero.log_lt_iff_lt_exp hx).mpr (by simpa using this)
    calc x = WithZero.exp (WithZero.log x) := (WithZero.exp_log hx).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (by omega)
  rw [Nat.cast_pow, map_pow]
  calc _ ≤ (WithZero.exp (-1 : ℤ)) ^ k := pow_le_pow_left₀ zero_le h1 k
    _ = _ := by rw [← WithZero.exp_nsmul]; simp

/-- **Bounded denominators of $\hat{\mathfrak d}^{-1}$**: $d\,\hat{\mathfrak d}^{-1}\subseteq\hat{\mathcal O}$ for some integer $d\ne0$. -/
theorem exists_nat_mul_DHat_subset_OHat :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ a ∈ (DHat (F := F)), (d : AF) * a ∈ OHat := by
  classical
  set S := (Analysis.finite_support_diffExp (F := F)).toFinset with hS
  set d : ℕ := ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ (Analysis.diffExp v : ℤ).toNat with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  refine ⟨d, hd0, fun a ha w => ?_⟩
  change evalAt w ((d : AF) * a) ∈ w.adicCompletionIntegers F
  rw [map_mul, map_natCast, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
  have hdle : Valued.v ((d : w.adicCompletion F)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := w)).mp (natCast_mem_O d w)
  have haw : Valued.v (evalAt w a) ≤ WithZero.exp (Analysis.diffExp w : ℤ) := ha w
  by_cases hw : w ∈ S
  · rw [hd, ← Finset.mul_prod_erase S _ hw, Nat.cast_mul]
    have h1 := valued_absNorm_pow_le (F := F) w (Analysis.diffExp w : ℤ).toNat
    have h2 : Valued.v (((∏ x ∈ S.erase w, Ideal.absNorm x.asIdeal ^ (Analysis.diffExp x : ℤ).toNat : ℕ) :
        w.adicCompletion F)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := w)).mp (natCast_mem_O _ w)
    have h3 : Valued.v (((Ideal.absNorm w.asIdeal ^ (Analysis.diffExp w : ℤ).toNat : ℕ) *
        (∏ x ∈ S.erase w, Ideal.absNorm x.asIdeal ^ (Analysis.diffExp x : ℤ).toNat : ℕ) : w.adicCompletion F))
        ≤ WithZero.exp (-((Analysis.diffExp w : ℤ).toNat : ℤ)) := by
      rw [map_mul]
      calc _ ≤ WithZero.exp (-((Analysis.diffExp w : ℤ).toNat : ℤ)) * 1 := mul_le_mul' h1 h2
        _ = _ := mul_one _
    calc _ ≤ WithZero.exp (-((Analysis.diffExp w : ℤ).toNat : ℤ)) * WithZero.exp (Analysis.diffExp w : ℤ) :=
          mul_le_mul' h3 haw
      _ = WithZero.exp (-((Analysis.diffExp w : ℤ).toNat : ℤ) + (Analysis.diffExp w : ℤ)) := by
          rw [WithZero.exp_add]
      _ ≤ 1 := by
          rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)
  · have h0 : (Analysis.diffExp w : ℤ) = 0 := by
      by_contra hne
      exact hw ((Set.Finite.mem_toFinset _).mpr hne)
    rw [h0, WithZero.exp_zero] at haw
    calc _ ≤ 1 * 1 := mul_le_mul' hdle haw
      _ = 1 := one_mul 1

end

end QuadFormsKB.Tamagawa.Measure.Weil
