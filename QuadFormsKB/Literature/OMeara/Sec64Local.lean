/-
# O'Meara §64 (local part): the completions $E_\mathfrak P \supseteq F_\mathfrak p$ and the local norms

**Setting.** $E/F$ is an extension of number fields (finite and separable, O'Meara §64, p. 173). A finite spot
$\mathfrak p$ of $F$ is a height-one prime `v : HeightOneSpectrum (𝓞 F)`, a finite spot $\mathfrak P$ of $E$ is
`w : HeightOneSpectrum (𝓞 E)`, and $\mathfrak P \mid \mathfrak p$ is Mathlib's `w.asIdeal.LiesOver v.asIdeal`. The
completions are `v.adicCompletion F` $= F_\mathfrak p$ and `w.adicCompletion E` $= E_\mathfrak P$ with Mathlib's
normalized norms $\lVert x\rVert = N(\mathfrak p)^{-\operatorname{ord}_\mathfrak p x}$ (`FinitePlace.norm_def`), which are
O'Meara's normalized valuations $\lvert\cdot\rvert_\mathfrak p$ (§33A). $e = e(\mathfrak P|\mathfrak p)$ is
`w.asIdeal.ramificationIdx (𝓞 F)` and $f = f(\mathfrak P|\mathfrak p)$ is `w.asIdeal.inertiaDeg (𝓞 F)`.

**Defines**
* `localMap v w`: the continuous embedding $F_\mathfrak p \to E_\mathfrak P$ extending $F \subseteq E$ (O'Meara's
  $I_\mathfrak P^{-1}$ of §15B), and the resulting `Algebra` instance (an instance, available whenever
  `w.asIdeal.LiesOver v.asIdeal` is);
* `localNormFin v w`: the local norm $N_{\mathfrak P|\mathfrak p} = N_{E_\mathfrak P/F_\mathfrak p}\colon E_\mathfrak P \to
  F_\mathfrak p$ (§15B, p. 32; used in §64, p. 173).

**Proves**
* `norm_localMap`: $\lVert x\rVert_\mathfrak P = \lVert x\rVert_\mathfrak p^{ef}$ for $x \in F_\mathfrak p$;
* `norm_localNormFin_le_one`, `norm_localNormFin_eq_one`: the local norm maps integers to integers and units to units.
-/
import QuadFormsKB.Analysis.LocalFourierNF
import QuadFormsKB.Literature.OMeara.Sec64

open NumberField IsDedekindDomain WithZero WithZeroMulInt

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section LocalMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- **The embedding $F_\mathfrak p \to E_\mathfrak P$** for $\mathfrak P \mid \mathfrak p$: the map of completions
induced by $F \subseteq E$ (uniformly continuous by Mathlib's `uniformContinuous_algebraMap_liesOver`). -/
def localMap : v.adicCompletion F →+* w.adicCompletion E :=
  (HeightOneSpectrum.adicCompletion.equiv E w).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation E)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom)

/-- `localMap` extends $F \to E$. -/
lemma localMap_algebraMap (c : F) :
    localMap v w (algebraMap F (v.adicCompletion F) c) =
      algebraMap E (w.adicCompletion E) (algebraMap F E c) := by
  simp only [localMap, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]
  erw [UniformSpace.Completion.mapRingHom_coe]
  rfl

/-- `localMap` is continuous. -/
lemma continuous_localMap : Continuous (localMap v w) := by
  unfold localMap
  simp only [RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))

/-- $E_\mathfrak P$ as an $F_\mathfrak p$-algebra via `localMap`, for $\mathfrak P \mid \mathfrak p$. -/
instance algebraAdicCompletionLiesOver : Algebra (v.adicCompletion F) (w.adicCompletion E) :=
  (localMap v w).toAlgebra

lemma algebraMap_adicCompletion_liesOver :
    algebraMap (v.adicCompletion F) (w.adicCompletion E) = localMap v w := rfl

instance : IsScalarTower F (v.adicCompletion F) (w.adicCompletion E) := .of_algebraMap_eq fun c => by
  rw [algebraMap_adicCompletion_liesOver, localMap_algebraMap, IsScalarTower.algebraMap_apply F E]

instance : ContinuousSMul (v.adicCompletion F) (w.adicCompletion E) where
  continuous_smul := ((continuous_localMap v w).comp continuous_fst).mul continuous_snd

example : Module.Finite (v.adicCompletion F) (w.adicCompletion E) := inferInstance

/-- Changing the base of `toNNReal` from $q$ to $q^f$ ($f \ne 0$) raises the value to the $f$-th power. -/
lemma toNNReal_pow_base {q : NNReal} (hq : q ≠ 0) {f : ℕ} (hf : f ≠ 0) (z : ℤᵐ⁰) :
    toNNReal (pow_ne_zero f hq) z = toNNReal hq z ^ f := by
  by_cases hz : z = 0
  · subst hz
    simp [hf]
  · rw [toNNReal_neg_apply _ hz, toNNReal_neg_apply _ hz, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
      ← zpow_mul, mul_comm]

lemma toNNReal_eq_of_eq {q q' : NNReal} (hq : q ≠ 0) (hq' : q' ≠ 0) (h : q = q') (z : ℤᵐ⁰) :
    toNNReal hq z = toNNReal hq' z := by
  subst h; rfl

/-- $N(\mathfrak P) = N(\mathfrak p)^f$. -/
lemma absNorm_liesOver :
    Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) :=
  (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm

lemma absNorm_liesOver_nnreal :
    (Ideal.absNorm w.asIdeal : NNReal) = (Ideal.absNorm v.asIdeal : NNReal) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  exact_mod_cast absNorm_liesOver v w

include v in
lemma inertiaDeg_ne_zero : w.asIdeal.inertiaDeg (𝓞 F) ≠ 0 := by
  have := w.isPrime
  exact (Ideal.inertiaDeg_pos w.asIdeal (𝓞 F)).ne'

/-- `toNNReal` at base $N(\mathfrak P)$ is the $f$-th power of `toNNReal` at base $N(\mathfrak p)$. -/
lemma toNNReal_liesOver (z : ℤᵐ⁰) :
    toNNReal (HeightOneSpectrum.absNorm_ne_zero w) z =
      toNNReal (HeightOneSpectrum.absNorm_ne_zero v) z ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  rw [toNNReal_eq_of_eq _ (pow_ne_zero _ (HeightOneSpectrum.absNorm_ne_zero v)) (absNorm_liesOver_nnreal v w),
    toNNReal_pow_base _ (inertiaDeg_ne_zero v w)]

/-- **The norm of $E_\mathfrak P$ restricted to $F_\mathfrak p$:** $\lVert x\rVert_\mathfrak P =
\lVert x\rVert_\mathfrak p^{ef}$ (both normalized). -/
theorem norm_localMap (x : v.adicCompletion F) :
    ‖localMap v w x‖ = ‖x‖ ^ (w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F)) := by
  have hcl : IsClosed {x : v.adicCompletion F |
      ‖localMap v w x‖ = ‖x‖ ^ (w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F))} :=
    isClosed_eq ((continuous_localMap v w).norm) (continuous_norm.pow _)
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on x hcl fun c => ?_
  rw [localMap_algebraMap, FinitePlace.norm_def, FinitePlace.norm_def]
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap F E c),
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) c]
  rw [← HeightOneSpectrum.valuation_liesOver E v w c, map_pow, toNNReal_liesOver v w, ← pow_mul,
    mul_comm]
  push_cast
  rfl

/-- The valuation form of `norm_localMap`: $\operatorname{ord}_\mathfrak P(x) = e\operatorname{ord}_\mathfrak p(x)$
for $x \in F_\mathfrak p$. -/
theorem valued_localMap (x : v.adicCompletion F) :
    Valued.v (localMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 F) := by
  have h := norm_localMap v w x
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  have h' : toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (Valued.v (localMap v w x)) =
      toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 F)) := by
    rw [map_pow (toNNReal (HeightOneSpectrum.absNorm_ne_zero w)), toNNReal_liesOver v w (Valued.v x),
      ← pow_mul, mul_comm]
    exact_mod_cast h
  exact (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).injective h'

end LocalMap

/-! ### Continuity and integrality of the local norm -/

section NormContinuous

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [Field L] [Algebra K L]
  [TopologicalSpace L] [IsTopologicalRing L] [ContinuousSMul K L] [T2Space L] [FiniteDimensional K L]

/-- The norm of a finite extension $L/K$ of a complete field, $L$ with a Hausdorff ring topology making $K$ act
continuously, is continuous (a determinant of a matrix whose entries are linear in $x$). -/
theorem continuous_algebraNorm : Continuous (fun x : L => Algebra.norm K x) := by
  let b := Module.finBasis K L
  have hfun : (fun x : L => Algebra.norm K x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [hfun]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have : (fun x : L => Algebra.leftMulMatrix b x i j) = fun x => (b.coord i) (x * b j) := by
    funext x; rw [Algebra.leftMulMatrix_eq_repr_mul]; rfl
  rw [this]
  exact (LinearMap.continuous_of_finiteDimensional ((b.coord i).comp (LinearMap.mulRight K (b j))))

end NormContinuous

section LocalNorm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- **The local norm** $N_{\mathfrak P|\mathfrak p}\colon E_\mathfrak P \to F_\mathfrak p$ (O'Meara 1963, §15B,
p. 32, used in §64, p. 173): the norm of the finite extension $E_\mathfrak P/F_\mathfrak p$. -/
@[kb "omeara1963" "§64, p. 173 (the norm map N_{𝔓|𝔭} : E_𝔓 → F_𝔭 of §15B at a finite spot)"]
def localNormFin : w.adicCompletion E →* v.adicCompletion F :=
  Algebra.norm (v.adicCompletion F)

lemma localNormFin_apply (y : w.adicCompletion E) :
    localNormFin v w y = Algebra.norm (v.adicCompletion F) y := rfl

/-- **The local norm of an integer is an integer.** (The image of the compact ball $\lVert y\rVert \le 1$ under the
continuous norm is bounded, and $N(y^k) = N(y)^k$.) -/
theorem norm_localNormFin_le_one {y : w.adicCompletion E} (hy : ‖y‖ ≤ 1) : ‖localNormFin v w y‖ ≤ 1 := by
  have hK : IsCompact (Metric.closedBall (0 : w.adicCompletion E) 1) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := (hK.image (continuous_algebraNorm (K := v.adicCompletion F))).isBounded.exists_norm_le
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hlt
  have hyk : y ^ k ∈ Metric.closedBall (0 : w.adicCompletion E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hy
  have := hC (Algebra.norm (v.adicCompletion F) (y ^ k)) ⟨_, hyk, rfl⟩
  rw [map_pow, norm_pow] at this
  exact absurd (lt_of_le_of_lt this hk) (lt_irrefl _)

/-- **The local norm of a unit is a unit.** -/
theorem norm_localNormFin_eq_one {y : w.adicCompletion E} (hy : ‖y‖ = 1) : ‖localNormFin v w y‖ = 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have h1 := norm_localNormFin_le_one v w hy.le
  have h2 := norm_localNormFin_le_one v w (y := y⁻¹) (by rw [norm_inv, hy, inv_one])
  have hm : localNormFin v w y * localNormFin v w y⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
  have hm' : ‖localNormFin v w y‖ * ‖localNormFin v w y⁻¹‖ = 1 := by rw [← norm_mul, hm, norm_one]
  nlinarith [norm_nonneg (localNormFin v w y), norm_nonneg (localNormFin v w y⁻¹)]

end LocalNorm

/-! ### The lower bound $e f \le [E_\mathfrak P : F_\mathfrak p]$ -/

section LowerBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

local notation "Fv" => v.adicCompletion F
local notation "Ew" => w.adicCompletion E
local notation "e" => w.asIdeal.ramificationIdx (𝓞 F)
local notation "f" => w.asIdeal.inertiaDeg (𝓞 F)

include v in
lemma ramificationIdx_pos : 0 < e :=
  Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot

lemma inertiaDeg_eq_finrank_quot :
    f = Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w.asIdeal) := by
  have := v.isMaximal; have := w.isMaximal
  exact Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal

/-- Lifts $\rho_0, \dots, \rho_{f-1} \in \mathcal O_E$ of a basis of $\mathcal O_E/\mathfrak P$ over
$\mathcal O_F/\mathfrak p$. -/
lemma exists_residue_basis : ∃ ρ : Fin f → 𝓞 E,
    LinearIndependent (𝓞 F ⧸ v.asIdeal) (fun k => Ideal.Quotient.mk w.asIdeal (ρ k)) := by
  have := v.isMaximal; have := w.isMaximal
  let : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  let : Field (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hpos : 0 < Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w.asIdeal) := by
    rw [← inertiaDeg_eq_finrank_quot v w]; have := w.isPrime; exact Ideal.inertiaDeg_pos w.asIdeal (𝓞 F)
  have : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w.asIdeal) := Module.finite_of_finrank_pos hpos
  let b := Module.finBasisOfFinrankEq (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w.asIdeal)
    (inertiaDeg_eq_finrank_quot v w).symm
  refine ⟨fun k => (Ideal.Quotient.mk_surjective (b k)).choose, ?_⟩
  convert b.linearIndependent with k
  exact (Ideal.Quotient.mk_surjective (b k)).choose_spec

lemma valued_coe_int_le_one (x : 𝓞 E) : Valued.v ((x : E) : Ew) ≤ 1 := by
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one x

/-- **Residue independence.** If $\rho_k \in \mathcal O_E$ reduce to independent residues over $\mathcal O_F/\mathfrak
p$ and $a_k \in \mathcal O_\mathfrak p$ with some $a_k$ a unit, then $\sum_k a_k\rho_k$ is a unit of $E_\mathfrak P$. -/
lemma valued_sum_eq_one (ρ : Fin f → 𝓞 E)
    (hρ : LinearIndependent (𝓞 F ⧸ v.asIdeal) (fun k => Ideal.Quotient.mk w.asIdeal (ρ k)))
    (a : Fin f → Fv) (ha : ∀ k, Valued.v (a k) ≤ 1) (k₀ : Fin f) (hk₀ : Valued.v (a k₀) = 1) :
    Valued.v (∑ k, localMap v w (a k) * ((ρ k : E) : Ew)) = 1 := by
  classical
  choose α hα using fun k => HN.exists_int_approx v ⟨a k, ha k⟩
  -- the global approximation `x = ∑ α_k ρ_k ∈ 𝓞 E`
  set x : 𝓞 E := ∑ k, algebraMap (𝓞 F) (𝓞 E) (α k) * ρ k with hx
  have hαcoe : ∀ k, (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (α k) : Fv) =
      algebraMap F Fv ((α k : 𝓞 F) : F) := fun k => rfl
  have hval_α : Valued.v (algebraMap F Fv ((α k₀ : 𝓞 F) : F)) = 1 := by
    have h1 := hα k₀
    rw [hαcoe] at h1
    have := Valuation.map_eq_of_sub_lt Valued.v (x := a k₀) (y := algebraMap F Fv ((α k₀ : 𝓞 F) : F))
      (by rw [← neg_sub, Valuation.map_neg, hk₀]; exact h1)
    rw [this, hk₀]
  have hα0 : α k₀ ∉ v.asIdeal := by
    intro hmem
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (α k₀)).2 hmem
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    exact absurd (hval_α ▸ this) (lt_irrefl _)
  have hxw : x ∉ w.asIdeal := by
    intro hmem
    have h0 : Ideal.Quotient.mk w.asIdeal x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hsum : ∑ k, Ideal.Quotient.mk v.asIdeal (α k) • Ideal.Quotient.mk w.asIdeal (ρ k) = 0 := by
      rw [← h0, hx, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, map_mul, Ideal.Quotient.algebraMap_mk_of_liesOver]
    have := Fintype.linearIndependent_iff.1 hρ _ hsum k₀
    exact hα0 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  have hvx : Valued.v (((x : 𝓞 E) : E) : Ew) = 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) w).2 hxw
  have hcoe_x : (((x : 𝓞 E) : E) : Ew) = ∑ k, localMap v w (algebraMap F Fv ((α k : 𝓞 F) : F)) *
      ((ρ k : E) : Ew) := by
    have hxE : ((x : 𝓞 E) : E) = ∑ k, algebraMap F E ((α k : 𝓞 F) : F) * (ρ k : E) := by
      rw [hx]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
    show algebraMap E Ew ((x : 𝓞 E) : E) = _
    rw [hxE, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, localMap_algebraMap]
    rfl
  have hdiff : Valued.v ((∑ k, localMap v w (a k) * ((ρ k : E) : Ew)) - (((x : 𝓞 E) : E) : Ew)) < 1 := by
    rw [hcoe_x, ← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun k _ => ?_
    rw [← sub_mul, ← map_sub, map_mul, valued_localMap]
    calc Valued.v (a k - algebraMap F Fv ((α k : 𝓞 F) : F)) ^ e * Valued.v ((ρ k : E) : Ew)
        ≤ Valued.v (a k - algebraMap F Fv ((α k : 𝓞 F) : F)) ^ e * 1 := by
          gcongr; exact valued_coe_int_le_one w (ρ k)
      _ < 1 := by
          rw [mul_one]
          have h1 := hα k
          rw [hαcoe] at h1
          exact pow_lt_one₀ zero_le h1 (ramificationIdx_pos v w).ne'
  rw [← hvx]
  exact Valuation.map_eq_of_sub_lt _ (by rw [hvx]; exact hdiff)

/-- **The valuation of $\sum_k a_k\rho_k$** is $\max_k \lvert a_k\rvert^e$ (as a supremum over `Fin f`). -/
lemma valued_sum_eq_sup (ρ : Fin f → 𝓞 E)
    (hρ : LinearIndependent (𝓞 F ⧸ v.asIdeal) (fun k => Ideal.Quotient.mk w.asIdeal (ρ k)))
    (a : Fin f → Fv) (k₀ : Fin f) (hk₀ : ∀ k, Valued.v (a k) ≤ Valued.v (a k₀)) :
    Valued.v (∑ k, localMap v w (a k) * ((ρ k : E) : Ew)) = Valued.v (a k₀) ^ e := by
  by_cases h0 : a k₀ = 0
  · have : ∀ k, a k = 0 := fun k => by
      have := hk₀ k; rw [h0, map_zero, le_zero_iff, map_eq_zero] at this; exact this
    simp [this, (ramificationIdx_pos v w).ne']
  set a' : Fin f → Fv := fun k => a k / a k₀
  have ha' : ∀ k, Valued.v (a' k) ≤ 1 := fun k => by
    simp only [a', map_div₀]
    exact div_le_one_of_le₀ (hk₀ k) zero_le
  have hk₀' : Valued.v (a' k₀) = 1 := by simp [a', div_self h0]
  have hsplit : ∑ k, localMap v w (a k) * ((ρ k : E) : Ew) =
      localMap v w (a k₀) * ∑ k, localMap v w (a' k) * ((ρ k : E) : Ew) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← map_mul]
    simp only [a', mul_div_cancel₀ _ h0]
  rw [hsplit, map_mul, valued_sum_eq_one v w ρ hρ a' ha' k₀ hk₀', mul_one, valued_localMap]

/-- **$e f \le [E_\mathfrak P : F_\mathfrak p]$**: the elements $\pi^j\rho_k$ ($0 \le j < e$, $0 \le k < f$; $\pi$ a
prime element at $\mathfrak P$, $\rho_k$ lifts of a residue basis) are linearly independent over $F_\mathfrak p$. -/
theorem ef_le_finrank : e * f ≤ Module.finrank Fv Ew := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_residue_basis v w
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer' E
  set πw : Ew := ((π : E) : Ew)
  have hπw : Valued.v πw = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  let b : Fin e × Fin f → Ew := fun jk => πw ^ jk.1.val * ((ρ jk.2 : E) : Ew)
  suffices hli : LinearIndependent Fv b by
    have := hli.fintype_card_le_finrank
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- regroup the relation by powers of `πw`
  set T : Fin e → Ew := fun j => ∑ k, localMap v w (g (j, k)) * ((ρ k : E) : Ew)
  have hT : ∑ j : Fin e, πw ^ j.val * T j = 0 := by
    rw [← hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [b, Algebra.smul_def, algebraMap_adicCompletion_liesOver]
    ring
  -- each `T j` has valuation `max_k |g(j,k)|^e`
  have hmax : ∀ j : Fin e, ∃ k₀ : Fin f, ∀ k, Valued.v (g (j, k)) ≤ Valued.v (g (j, k₀)) := fun j => by
    have hne : (Finset.univ : Finset (Fin f)).Nonempty :=
      Finset.univ_nonempty_iff.2 ⟨⟨0, Nat.pos_of_ne_zero (inertiaDeg_ne_zero v w)⟩⟩
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_max_image Finset.univ (fun k => Valued.v (g (j, k))) hne
    exact ⟨k₀, fun k => hk₀ k (Finset.mem_univ _)⟩
  choose kmax hkmax using hmax
  have hvT : ∀ j, Valued.v (T j) = Valued.v (g (j, kmax j)) ^ e := fun j =>
    valued_sum_eq_sup v w ρ hρ (fun k => g (j, k)) (kmax j) (hkmax j)
  by_contra hne
  push Not at hne
  obtain ⟨⟨j₁, k₁⟩, hjk⟩ := hne
  -- the term of largest valuation
  have hnonempty : (Finset.univ : Finset (Fin e)).Nonempty := ⟨j₁, Finset.mem_univ _⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j => Valued.v (πw ^ j.val * T j)) hnonempty
  have hTj₁ : T j₁ ≠ 0 := by
    intro h0
    have h1 := hvT j₁
    rw [h0, map_zero] at h1
    have h2 : g (j₁, kmax j₁) = 0 := by
      have := h1.symm; rwa [pow_eq_zero_iff (ramificationIdx_pos v w).ne', map_eq_zero] at this
    have := hkmax j₁ k₁
    rw [h2, map_zero, le_zero_iff, map_eq_zero] at this
    exact hjk this
  have hπ0 : πw ≠ 0 := by intro h; rw [h, map_zero] at hπw; exact exp_ne_zero hπw.symm
  have hpos : Valued.v (πw ^ j₀.val * T j₀) ≠ 0 := by
    intro h0
    have := hj₀ j₁ (Finset.mem_univ _)
    rw [h0, le_zero_iff, map_mul, mul_eq_zero, map_pow, pow_eq_zero_iff', map_eq_zero, map_eq_zero] at this
    rcases this with ⟨h, -⟩ | h
    · exact hπ0 h
    · exact hTj₁ h
  have hTj₀ : g (j₀, kmax j₀) ≠ 0 := by
    intro h0
    apply hpos
    rw [map_mul, hvT, h0, map_zero, zero_pow (ramificationIdx_pos v w).ne', mul_zero]
  -- distinct powers have distinct valuations modulo `e`
  have hlog : ∀ j : Fin e, T j ≠ 0 → Valued.v (πw ^ j.val * T j) =
      exp (-(j.val : ℤ) + e * log (Valued.v (g (j, kmax j)))) := fun j hj => by
    have hg0 : g (j, kmax j) ≠ 0 := by
      intro h0; apply hj
      have := hvT j
      rw [h0, map_zero, zero_pow (ramificationIdx_pos v w).ne'] at this
      exact (Valuation.zero_iff _).1 this
    have hv0 : Valued.v (g (j, kmax j)) ≠ 0 := (Valuation.ne_zero_iff _).2 hg0
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (g (j, kmax j)) = exp m := ⟨log _, (exp_log hv0).symm⟩
    rw [map_mul, map_pow, hπw, hvT, hm, log_exp, ← exp_nsmul, ← exp_nsmul, ← exp_add]
    congr 1; simp
  have hTj₀' : T j₀ ≠ 0 := by
    intro h; apply hpos; rw [h, mul_zero, map_zero]
  have hdistinct : ∀ j : Fin e, Valued.v (πw ^ j.val * T j) = Valued.v (πw ^ j₀.val * T j₀) → j = j₀ := by
    intro j heq
    by_cases hTj : T j = 0
    · rw [hTj, mul_zero, map_zero] at heq; exact absurd heq.symm hpos
    rw [hlog j hTj, hlog j₀ hTj₀', exp_inj] at heq
    have he : (0 : ℤ) < e := by exact_mod_cast ramificationIdx_pos v w
    have h1 : (-(j.val : ℤ)) % e = (-(j₀.val : ℤ)) % e := by
      have := heq
      have hm : (-(j.val : ℤ) + e * log (Valued.v (g (j, kmax j)))) % e = (-(j.val : ℤ)) % e := by
        rw [Int.add_mul_emod_self_left]
      have hm₀ : (-(j₀.val : ℤ) + e * log (Valued.v (g (j₀, kmax j₀)))) % e = (-(j₀.val : ℤ)) % e := by
        rw [Int.add_mul_emod_self_left]
      rw [← hm, ← hm₀, heq]
    have hj1 : (j.val : ℤ) < e := by exact_mod_cast j.2
    have hj01 : (j₀.val : ℤ) < e := by exact_mod_cast j₀.2
    have hd : (e : ℤ) ∣ (j.val : ℤ) - j₀ := by
      have := Int.ModEq.dvd (n := (e : ℤ)) (a := -(j.val : ℤ)) (b := -(j₀.val : ℤ)) h1
      simpa [neg_add_eq_sub] using this
    have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    apply Fin.ext
    omega
  have hne_val : ∀ j : Fin e, j ≠ j₀ → Valued.v (πw ^ j.val * T j) ≠ Valued.v (πw ^ j₀.val * T j₀) := by
    intro j hj' heq
    exact hj' (hdistinct j heq)
  have hlt : ∀ j ∈ Finset.univ.erase j₀,
      Valued.v (πw ^ j.val * T j) < Valued.v (πw ^ j₀.val * T j₀) := fun j hj =>
    lt_of_le_of_ne (hj₀ j (Finset.mem_univ _)) (hne_val j (Finset.ne_of_mem_erase hj))
  have hsum := Valuation.map_sum_eq_of_lt Valued.v (Finset.mem_univ j₀)
    (fun j hj => hlt j (by rwa [Finset.sdiff_singleton_eq_erase] at hj))
  rw [hT, map_zero] at hsum
  exact hpos hsum.symm

end LowerBound

/-! ### Norms on a product of fields, and $K \otimes_F E \cong \prod_i A_i$ -/

section ProductNorm

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Type*)
  [∀ i, Field (A i)] [∀ i, Algebra K (A i)] [∀ i, FiniteDimensional K (A i)]

/-- $\prod_i A_i \cong A_{i_0} \times \prod_{i \ne i_0} A_i$ as $K$-modules. -/
def piSplitAtLinear (i₀ : ι) : ((i : ι) → A i) ≃ₗ[K] A i₀ × ((j : {j // j ≠ i₀}) → A j) :=
  { Equiv.piSplitAt i₀ A with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The norm of an element of $\prod_i A_i$ supported at one coordinate. -/
lemma norm_mulSingle (i₀ : ι) (y : A i₀) :
    Algebra.norm K (Pi.mulSingle i₀ y : (i : ι) → A i) = Algebra.norm K y := by
  classical
  rw [Algebra.norm_apply, Algebra.norm_apply]
  let e := piSplitAtLinear (K := K) A i₀
  rw [← LinearMap.det_conj _ e]
  have : (e : ((i : ι) → A i) →ₗ[K] A i₀ × ((j : {j // j ≠ i₀}) → A j)) ∘ₗ
      Algebra.lmul K ((i : ι) → A i) (Pi.mulSingle i₀ y) ∘ₗ
      (e.symm : A i₀ × ((j : {j // j ≠ i₀}) → A j) →ₗ[K] ((i : ι) → A i)) =
      LinearMap.prodMap (Algebra.lmul K (A i₀) y) LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_
    · simp [e, piSplitAtLinear, Equiv.piSplitAt]
    · funext j
      simp [e, piSplitAtLinear, Equiv.piSplitAt, j.2]
  rw [this, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

/-- **The norm on a finite product of fields** is the product of the norms of the coordinates. -/
theorem norm_pi (x : (i : ι) → A i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  conv_lhs => rw [← Finset.univ_prod_mulSingle x]
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => norm_mulSingle A i (x i)

open scoped TensorProduct

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra F K]
  [∀ i, Algebra E (A i)] [∀ i, Algebra F (A i)] [∀ i, IsScalarTower F K (A i)]
  [∀ i, IsScalarTower F E (A i)]

/-- The natural map $K \otimes_F E \to \prod_i A_i$, $c \otimes y \mapsto (c y)_i$. -/
def tensorToPi : K ⊗[F] E →ₐ[K] ((i : ι) → A i) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) (IsScalarTower.toAlgHom F E _)
    (fun _ _ => Commute.all _ _)

lemma tensorToPi_one_tmul (y : E) : tensorToPi A (F := F) ((1 : K) ⊗ₜ y) = algebraMap E _ y := by
  simp [tensorToPi]

/-- $N_{K \otimes_F E / K}(1 \otimes y) = N_{E/F}(y)$. -/
lemma norm_one_tmul (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply TensorProduct.AlgebraTensorModule.curry_injective
  ext c
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- **Norms through a decomposition $K \otimes_F E \cong \prod_i A_i$** (abstract form of O'Meara's 15:3): if the
natural map $K \otimes_F E \to \prod_i A_i$ is onto and $\sum_i [A_i : K] = [E : F]$, then $\prod_i N_{A_i/K}(y) =
N_{E/F}(y)$ for every $y \in E$. -/
theorem prod_norm_eq_of_surjective (hsurj : Function.Surjective (tensorToPi A (K := K) (F := F) (E := E)))
    (hdim : ∑ i, Module.finrank K (A i) = Module.finrank F E) (y : E) :
    ∏ i, Algebra.norm K (algebraMap E (A i) y) = algebraMap F K (Algebra.norm F y) := by
  have hinj : Function.Injective (tensorToPi A (K := K) (F := F) (E := E)) := by
    have hfr : Module.finrank K (K ⊗[F] E) = Module.finrank K ((i : ι) → A i) := by
      rw [Module.finrank_baseChange, Module.finrank_pi_fintype, hdim]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
      (f := (tensorToPi A (K := K) (F := F) (E := E)).toLinearMap)).2 hsurj
  let Φ := AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩
  rw [← norm_one_tmul, ← Algebra.norm_eq_of_algEquiv Φ]
  show _ = Algebra.norm K (tensorToPi A ((1 : K) ⊗ₜ y))
  rw [tensorToPi_one_tmul, norm_pi]
  rfl

end ProductNorm

/-! ### The finite spots over $\mathfrak p$: $[E_\mathfrak P : F_\mathfrak p] = ef$ and Theorem 15:3 -/

section SpotsOver

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

/-- The finite spots $\mathfrak P$ of $E$ with $\mathfrak P \mid \mathfrak p$. -/
abbrev SpotsOver : Type _ := {w : HeightOneSpectrum (𝓞 E) // w.asIdeal.LiesOver v.asIdeal}

instance (w : SpotsOver E v) : w.1.asIdeal.LiesOver v.asIdeal := w.2

lemma mem_primesOverFinset_of_spotsOver (w : SpotsOver E v) :
    w.1.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) :=
  (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).2 ⟨w.1.isPrime, w.2⟩

/-- The spots $\mathfrak P \mid \mathfrak p$ correspond to the primes of `primesOverFinset`. -/
def spotsOverEquiv : SpotsOver E v ≃ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) where
  toFun w := ⟨w.1.asIdeal, mem_primesOverFinset_of_spotsOver E v w⟩
  invFun P := by
    have h := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).1 P.2
    haveI := h.1
    exact ⟨⟨P.1, h.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1⟩, h.2⟩
  left_inv w := rfl
  right_inv P := rfl

noncomputable instance : Fintype (SpotsOver E v) := Fintype.ofEquiv _ (spotsOverEquiv E v).symm

noncomputable instance : DecidableEq (SpotsOver E v) := Classical.decEq _

/-- $\sum_{\mathfrak P \mid \mathfrak p} e(\mathfrak P|\mathfrak p) f(\mathfrak P|\mathfrak p) = [E : F]$. -/
lemma sum_ef_spotsOver :
    ∑ w : SpotsOver E v, w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F) =
      Module.finrank F E := by
  have := v.isMaximal
  rw [← Ideal.sum_ramification_inertia (p := v.asIdeal) (𝓞 E) F E v.ne_bot, ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E))]
  refine Fintype.sum_equiv (spotsOverEquiv E v) _
    (fun P => v.asIdeal.ramificationIdx' P.1 * v.asIdeal.inertiaDeg' P.1) fun w => ?_
  have := w.1.isMaximal
  simp only [spotsOverEquiv, Equiv.coe_fn_mk]
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, Ideal.inertiaDeg'_eq_inertiaDeg]

/-- Distinct finite spots of $E$ give inequivalent absolute values. -/
lemma not_isEquiv_adicAbv {w₁ w₂ : HeightOneSpectrum (𝓞 E)} (h : w₁ ≠ w₂) :
    ¬ (HeightOneSpectrum.adicAbv E w₁).IsEquiv (HeightOneSpectrum.adicAbv E w₂) := by
  intro heq
  have hle : ¬ w₁.asIdeal ≤ w₂.asIdeal := fun hle =>
    h (HeightOneSpectrum.ext (w₁.isMaximal.eq_of_le w₂.isPrime.ne_top hle))
  obtain ⟨x, hx1, hx2⟩ := Set.not_subset.1 hle
  have h1 : HeightOneSpectrum.adicAbv E w₁ (x : E) < 1 := by
    rw [← FinitePlace.norm_embedding]; exact (FinitePlace.norm_lt_one_iff_mem E w₁ x).2 hx1
  have h2 : HeightOneSpectrum.adicAbv E w₂ (x : E) = 1 := by
    rw [← FinitePlace.norm_embedding]; exact (FinitePlace.norm_eq_one_iff_notMem E w₂ x).2 hx2
  have := (heq 1 (x : E)).2 (by rw [map_one, h2])
  rw [map_one] at this
  exact absurd h1 (not_lt.2 this)

lemma isNontrivial_adicAbv (w : HeightOneSpectrum (𝓞 E)) : (HeightOneSpectrum.adicAbv E w).IsNontrivial := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  refine ⟨π, fun h0 => ?_, fun h1 => ?_⟩
  · rw [h0, map_zero] at hπ; exact exp_ne_zero hπ.symm
  · rw [← FinitePlace.norm_embedding, FinitePlace.norm_def, FinitePlace.embedding_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at h1
    have := (toNNReal_eq_one_iff (exp (-1 : ℤ)) (HeightOneSpectrum.absNorm_ne_zero w)
      (HeightOneSpectrum.one_lt_absNorm_nnreal w).ne').1 (by exact_mod_cast h1)
    exact absurd (exp_injective this) (by norm_num)

/-- **Weak approximation at the spots over $\mathfrak p$:** $E$ is dense in $\prod_{\mathfrak P|\mathfrak p}
E_\mathfrak P$. -/
theorem denseRange_algebraMap_spotsOver :
    DenseRange (algebraMap E ((w : SpotsOver E v) → w.1.adicCompletion E)) := by
  have h1 := AbsoluteValue.denseRange_algebraMap_pi (F := E) (ι := SpotsOver E v)
    (v := fun w => HeightOneSpectrum.adicAbv E w.1) (fun w => isNontrivial_adicAbv E w.1)
    (fun w₁ w₂ hne => not_isEquiv_adicAbv E (fun h => hne (Subtype.ext h)))
  let φ : (w : SpotsOver E v) → WithAbs (HeightOneSpectrum.adicAbv E w.1) → w.1.adicCompletion E :=
    fun w x => ((x.ofAbs : E) : w.1.adicCompletion E)
  have hφc : ∀ w, Continuous (φ w) := fun w => by
    have : Isometry (φ w) := by
      refine AddMonoidHomClass.isometry_of_norm
        ((algebraMap E (w.1.adicCompletion E)).toAddMonoidHom.comp
          (WithAbs.equiv (HeightOneSpectrum.adicAbv E w.1)).toAddMonoidHom) fun x => ?_
      rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
      rfl
    exact this.continuous
  have hφd : ∀ w, DenseRange (φ w) := fun w => by
    have := HeightOneSpectrum.denseRange_algebraMap E w.1
    refine this.mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨WithAbs.toAbs _ y, rfl⟩
  have h2 := (DenseRange.piMap hφd).comp h1 (continuous_pi fun w => (hφc w).comp (continuous_apply w))
  refine h2.mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨y, rfl⟩

open scoped TensorProduct

/-- **$F_\mathfrak p \otimes_F E \to \prod_{\mathfrak P|\mathfrak p} E_\mathfrak P$ is onto** (its image is a
finite-dimensional, hence closed, subspace containing the dense image of $E$). -/
theorem tensorToPi_spotsOver_surjective :
    Function.Surjective (tensorToPi (K := v.adicCompletion F) (F := F) (E := E)
      (fun w : SpotsOver E v => w.1.adicCompletion E)) := by
  let Φ := (tensorToPi (K := v.adicCompletion F) (F := F) (E := E)
      (fun w : SpotsOver E v => w.1.adicCompletion E)).toLinearMap
  change Function.Surjective Φ
  have hc : IsClosed (Φ.range : Set ((w : SpotsOver E v) → w.1.adicCompletion E)) :=
    Submodule.closed_of_finiteDimensional Φ.range
  have hd : DenseRange Φ := by
    refine (denseRange_algebraMap_spotsOver E v).mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨(1 : v.adicCompletion F) ⊗ₜ y, tensorToPi_one_tmul _ y⟩
  rw [← Set.range_eq_univ, ← Φ.coe_range, ← hc.closure_eq]
  exact hd.closure_range

/-- **The local degree at a finite spot** (O'Meara §15C/§33A): $[E_\mathfrak P : F_\mathfrak p] = e f$, and
$\sum_{\mathfrak P|\mathfrak p} [E_\mathfrak P : F_\mathfrak p] = [E : F]$. -/
theorem finrank_eq_ef_and_sum :
    (∀ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) =
      w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F)) ∧
    ∑ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
  have hle : ∑ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) ≤
      Module.finrank F E := by
    have := LinearMap.finrank_range_le (tensorToPi (K := v.adicCompletion F) (F := F) (E := E)
      (fun w : SpotsOver E v => w.1.adicCompletion E)).toLinearMap
    have hs : (tensorToPi (K := v.adicCompletion F) (F := F) (E := E)
        (fun w : SpotsOver E v => w.1.adicCompletion E)).toLinearMap.range = ⊤ :=
      LinearMap.range_eq_top.2 (tensorToPi_spotsOver_surjective E v)
    rw [hs, finrank_top, Module.finrank_pi_fintype, Module.finrank_baseChange] at this
    exact this
  have hge : ∀ w : SpotsOver E v, w.1.asIdeal.ramificationIdx (𝓞 F) * w.1.asIdeal.inertiaDeg (𝓞 F) ≤
      Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) := fun w => ef_le_finrank v w.1
  have hsum := sum_ef_spotsOver E v
  have heq : ∑ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) =
      Module.finrank F E :=
    le_antisymm hle (hsum ▸ Finset.sum_le_sum fun w _ => hge w)
  refine ⟨fun w => ?_, heq⟩
  have := (Finset.sum_eq_sum_iff_of_le (fun w _ => hge w)).1 (hsum.trans heq.symm)
  exact (this w (Finset.mem_univ _)).symm

/-- **O'Meara 15:3 at a finite spot:** $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}(y) = N_{E/F}(y)$
for $y \in E$ (equality in $F_\mathfrak p$). -/
@[kb "omeara1963" "§15B, 15:3 (2), p. 32 (at a finite spot, for the adic completions)"]
theorem prod_localNormFin_eq_norm (y : E) :
    ∏ w : SpotsOver E v, localNormFin v w.1 (algebraMap E (w.1.adicCompletion E) y) =
      algebraMap F (v.adicCompletion F) (Algebra.norm F y) :=
  prod_norm_eq_of_surjective (fun w : SpotsOver E v => w.1.adicCompletion E)
    (tensorToPi_spotsOver_surjective E v) (finrank_eq_ef_and_sum E v).2 y

end SpotsOver

/-! ### The valuation of a local norm (O'Meara §64, p. 173) -/

section NormValuation

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- $[E_\mathfrak P : F_\mathfrak p] = e f$ for a single spot $\mathfrak P \mid \mathfrak p$. -/
theorem finrank_adicCompletion_eq_ef :
    Module.finrank (v.adicCompletion F) (w.adicCompletion E) =
      w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) :=
  (finrank_eq_ef_and_sum E v).1 ⟨w, inferInstance⟩

lemma norm_localNormFin_inv (y : w.adicCompletion E) :
    ‖localNormFin v w y⁻¹‖ = ‖localNormFin v w y‖⁻¹ := by
  by_cases hy : y = 0
  · subst hy; simp [localNormFin_apply, Algebra.norm_zero]
  · have hm : localNormFin v w y * localNormFin v w y⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hy, map_one]
    apply eq_inv_of_mul_eq_one_left
    rw [← norm_mul, mul_comm, hm, norm_one]

/-- **O'Meara §64, p. 173 (by §33A):** $\lvert N_{\mathfrak P|\mathfrak p}\,y\rvert_\mathfrak p = \lvert y\rvert_\mathfrak P$
for $y \in E_\mathfrak P$ (normalized valuations, Mathlib's norms). -/
@[kb "omeara1963" "§64, p. 173 (|N_{𝔓|𝔭} 𝔍_𝔓|_𝔭 = |𝔍_𝔓|_𝔓, normalized valuations, by §33A)"]
theorem norm_localNormFin (y : w.adicCompletion E) : ‖localNormFin v w y‖ = ‖y‖ := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer F
  set πw : w.adicCompletion E := (π : w.adicCompletion E)
  set c : v.adicCompletion F := algebraMap F _ ϖ
  have hvπ : Valued.v πw = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hπ
  have hvc : Valued.v c = exp (-1 : ℤ) := by
    show Valued.v ((ϖ : F) : v.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hϖ
  have hπ0 : πw ≠ 0 := by intro h; rw [h, map_zero] at hvπ; exact exp_ne_zero hvπ.symm
  have hc0 : c ≠ 0 := by intro h; rw [h, map_zero] at hvc; exact exp_ne_zero hvc.symm
  have he := ramificationIdx_pos v w
  -- `‖πw‖ = ‖c‖ ^ f`
  have hnπ : ‖πw‖ = ‖c‖ ^ w.asIdeal.inertiaDeg (𝓞 F) := by
    rw [FinitePlace.norm_def, FinitePlace.norm_def, hvπ, hvc, toNNReal_liesOver v w]
    push_cast; rfl
  -- `ι c = πw ^ e * u` with `u` a unit
  set u := localMap v w c / πw ^ w.asIdeal.ramificationIdx (𝓞 F)
  have hu : ‖u‖ = 1 := by
    have : Valued.v u = 1 := by
      rw [map_div₀, valued_localMap, hvc, map_pow, hvπ, div_self (pow_ne_zero _ (exp_ne_zero))]
    rw [FinitePlace.norm_def, this, map_one, NNReal.coe_one]
  have hcu : localMap v w c = πw ^ w.asIdeal.ramificationIdx (𝓞 F) * u := by
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]
  -- `‖N πw‖ = ‖πw‖`
  have hNπ : ‖localNormFin v w πw‖ = ‖πw‖ := by
    have h1 : localNormFin v w (localMap v w c) = c ^ (w.asIdeal.ramificationIdx (𝓞 F) *
        w.asIdeal.inertiaDeg (𝓞 F)) := by
      rw [localNormFin_apply, ← algebraMap_adicCompletion_liesOver, Algebra.norm_algebraMap,
        finrank_adicCompletion_eq_ef]
    rw [hcu, map_mul, map_pow] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_pow, norm_localNormFin_eq_one v w hu, mul_one, norm_pow, pow_mul'] at h2
    rw [hnπ]
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) he.ne').1 h2
  -- general `y = πw ^ m * unit`
  by_cases hy : y = 0
  · subst hy; simp [localNormFin_apply, Algebra.norm_zero]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = exp m := ⟨log _, (exp_log ((Valuation.ne_zero_iff _).2 hy)).symm⟩
  set z := y * πw ^ m
  have hz : ‖z‖ = 1 := by
    have : Valued.v z = 1 := by
      rw [map_mul, map_zpow₀, hvπ, hm, ← exp_zsmul, smul_neg, smul_eq_mul, mul_one, ← exp_add,
        add_neg_cancel, exp_zero]
    rw [FinitePlace.norm_def, this, map_one, NNReal.coe_one]
  have hyz : y = πw ^ (-m) * z := by
    rw [mul_comm, mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, mul_one]
  have hzpow : ∀ k : ℤ, ‖localNormFin v w (πw ^ k)‖ = ‖πw‖ ^ k := fun k => by
    rcases k with k | k
    · simp only [Int.ofNat_eq_natCast, zpow_natCast, map_pow, norm_pow, hNπ]
    · rw [zpow_negSucc, norm_localNormFin_inv, map_pow, norm_pow, hNπ, zpow_negSucc]
  rw [hyz, map_mul, norm_mul, norm_localNormFin_eq_one v w hz, mul_one, hzpow, norm_mul, hz, mul_one,
    norm_zpow]

end NormValuation

end QuadFormsKB.OMeara
