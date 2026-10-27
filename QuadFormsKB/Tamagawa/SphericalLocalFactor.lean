import QuadFormsKB.Tamagawa.SphericalLocal
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.Weil.ProductFormulas

/-!
# Weil's local spherical factor as a series of local densities

**Layer:** local, at every finite place $v$ of a number field $F$, **dyadic places included**.

**Setting.** $F_v$, $\mathcal O_v$, uniformizer $\pi$ = `NF.π v`, $q = N\mathfrak p_v$, $e = \operatorname{ord}_v 2$, $U = \mathcal O_v^\times$,
$dx$ = `haarV` ($\operatorname{vol}\mathcal O_v = 1$), $Q$ over $\mathcal O_F$ nondegenerate in $n \ge 1$ variables, $L_v = \mathcal O_v^n$,
$\beta_v(t)$ = `DVR.localDensity (NF.Qp v Q) π t` for $t \in \mathcal O_v\setminus0$.

**Results.**
* `haarV_unitSq`: $\operatorname{vol}(U^2) = (1 - q^{-1})/[U : U^2] = (1-q^{-1})\,|2|_v/2$ ($[U:U^2] = 2q^e$, `HN.index_sq_U0`).
* `volume_shell`: for $t \in \mathcal O_v\setminus0$, $\operatorname{vol}\{x\in L_v : Q(x)\in tU^2\} = \beta_v(t)\operatorname{vol}(tU^2)$ — the pushforward of $dx$
  along $Q$ has density $\beta_v$ on the square-class shells (exact counting mod $\mathfrak p^k$, $k \ge \operatorname{ord}t + 2e + 1$, and
  $r_{\mathfrak p^k}(tu^2) = r_{\mathfrak p^k}(t)$).
* **`sphLocal_eq_tsum`** (Weil 1982, §4.5, (3), p. 102, and p. 107: "$T(\rho)$ covers twice the set $F(x)\in\rho k_v^{*2}$"):
  $$Z_\mathfrak p(s,\rho) = \frac{2}{1-q^{-1}}\int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|_v^s\,dx = |2|_v\sum_{j\in\mathbb Z}|\rho\pi^{2j}|_v^{1+s}\,\beta_v(\rho\pi^{2j}),$$
  terms with $\rho\pi^{2j}\notin\mathcal O_v$ being $0$. This is the local half of the bookkeeping in the spherical fibration:
  the $2$ and $(1 - q^{-1})^{-1}$ of `sphLocal` against $\operatorname{vol}(U^2)$.
-/

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology Set
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalLocalFactor

open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.SphericalZeta QuadFormsKB.Analysis

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-! ### The unit squares and their volume -/

/-- **The unit squares** $U^2 = \{u^2 : u \in \mathcal O_v^\times\} \subset F_v$. -/
def unitSq : Set Fv := {z | ∃ u : Fvˣ, u ∈ HN.U0 v ∧ z = (u : Fv) ^ 2}

/-- **The units** $U = \{z : |z|_v = 1\} \subset F_v$. -/
def unitSet : Set Fv := {z | Valued.v z = 1}

lemma unitSq_subset : unitSq v ⊆ unitSet v := by
  rintro z ⟨u, hu, rfl⟩
  simp only [unitSet, Set.mem_ofPred_eq, map_pow, (HN.mem_U0 v).mp hu, one_pow]

/-- $U^2$ is open: by the local square theorem, $z' \in U^2$ whenever $|z' - z| < |4|$ for some $z \in U^2$. -/
lemma unitSq_mem_of_close {z z' : Fv} (hz : z ∈ unitSq v) (h : Valued.v (z' - z) < Valued.v (4 : Fv)) :
    z' ∈ unitSq v := by
  obtain ⟨u, hu, rfl⟩ := hz
  have hu1 : Valued.v (u : Fv) = 1 := (HN.mem_U0 v).mp hu
  have hu0 : (u : Fv) ≠ 0 := u.ne_zero
  set w := z' / (u : Fv) ^ 2
  have hw : Valued.v (w - 1) < Valued.v (4 : Fv) := by
    have : w - 1 = (z' - (u : Fv) ^ 2) / (u : Fv) ^ 2 := by simp only [w]; field_simp
    rw [this, map_div₀, map_pow, hu1, one_pow, div_one]
    exact h
  obtain ⟨y, hy⟩ := HN.isSquare_of_valued_sub_one_lt v w hw
  have h4 : Valued.v (4 : Fv) ≤ 1 := by
    have : (4 : Fv) = ((4 : ℕ) : Fv) := by norm_num
    rw [this]
    exact (Valued.toNormedField.norm_le_one_iff).mp (IsUltrametricDist.norm_natCast_le_one _ _)
  have hw1 : Valued.v w = 1 := by
    have h1 : Valued.v (w - 1) < Valued.v (1 : Fv) := by rw [map_one]; exact lt_of_lt_of_le hw h4
    have : w = (w - 1) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ h1, map_one]
  have hy0 : y ≠ 0 := by rintro rfl; rw [mul_zero] at hy; rw [hy, map_zero] at hw1; exact zero_ne_one hw1
  have hy1 : Valued.v y = 1 := by
    have hvy : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.mpr hy0
    have h2 : Valued.v y * Valued.v y = 1 := by rw [← map_mul, ← hy, hw1]
    have hl : WithZero.log (Valued.v y) + WithZero.log (Valued.v y) = 0 := by
      rw [← WithZero.log_mul hvy hvy, h2, WithZero.log_one]
    have hl0 : WithZero.log (Valued.v y) = 0 := by omega
    rw [← WithZero.exp_log hvy, hl0, WithZero.exp_zero]
  refine ⟨Units.mk0 ((u : Fv) * y) (mul_ne_zero hu0 hy0), ?_, ?_⟩
  · rw [HN.mem_U0]; simp [hu1, hy1]
  · simp only [Units.val_mk0]
    rw [mul_pow, show y ^ 2 = w by rw [hy]; ring]
    simp only [w]; field_simp

/-- **The shell** $tU^2 = \{z \in tF_v^{\times2} : |z|_v = |t|_v\}$ of $t \in F_v$. -/
def shell (t : Fv) : Set Fv := sqClass t ∩ {z | Valued.v z = Valued.v t}

lemma valued_eq_iff_norm_eq {z t : Fv} : Valued.v z = Valued.v t ↔ ‖z‖ = ‖t‖ := by
  constructor
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_iff.mpr h.le) (Valued.toNormedField.norm_le_iff.mpr h.ge)
  · intro h
    exact le_antisymm (Valued.toNormedField.norm_le_iff.mp h.le) (Valued.toNormedField.norm_le_iff.mp h.ge)

lemma measurableSet_shell {t : Fv} (ht : t ≠ 0) : MeasurableSet (shell v t) := by
  refine (isOpen_sqClass v ht).measurableSet.inter ?_
  have : {z : Fv | Valued.v z = Valued.v t} = {z | ‖z‖ = ‖t‖} := by
    ext z; exact valued_eq_iff_norm_eq v
  rw [this]
  exact measurableSet_eq_fun continuous_norm.measurable measurable_const

lemma mem_shell_one {z : Fv} : z ∈ shell v 1 ↔ z ∈ unitSq v := by
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    simp only [Set.mem_ofPred_eq, one_mul, map_pow, map_one] at hz
    have hvy : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.mpr hy
    have hl : WithZero.log (Valued.v y) + WithZero.log (Valued.v y) = 0 := by
      rw [← WithZero.log_mul hvy hvy, ← pow_two, hz, WithZero.log_one]
    have hy1 : Valued.v y = 1 := by
      rw [← WithZero.exp_log hvy, show WithZero.log (Valued.v y) = 0 by omega, WithZero.exp_zero]
    exact ⟨Units.mk0 y hy, (HN.mem_U0 v).mpr (by simpa using hy1), by simp⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, u.ne_zero, by ring⟩, ?_⟩
    simp [(HN.mem_U0 v).mp hu]

/-- $tU^2 = t\cdot U^2$ for $t \ne 0$. -/
lemma shell_eq_image {t : Fv} (ht : t ≠ 0) : shell v t = (fun z => t * z) '' shell v 1 := by
  ext z
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    refine ⟨y ^ 2, ⟨⟨y, hy, by ring⟩, ?_⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, map_mul, map_pow] at hz ⊢
    have hvt : Valued.v t ≠ 0 := (Valued.v).ne_zero_iff.mpr ht
    rw [map_one]
    calc Valued.v y ^ 2 = Valued.v t * Valued.v y ^ 2 / Valued.v t := by field_simp
      _ = 1 := by rw [hz, div_self hvt]
  · rintro ⟨w, ⟨⟨y, hy, rfl⟩, hw⟩, rfl⟩
    refine ⟨⟨y, hy, by ring⟩, ?_⟩
    simp only [Set.mem_ofPred_eq, map_mul, map_one, one_mul] at hw ⊢
    rw [hw, mul_one]

/-! ### $\operatorname{vol}(U^2) = (1 - q^{-1})/[U:U^2]$ -/

/-- The subgroup $U^2$ of $U$ (squares of units). -/
abbrev sqSub : Subgroup (HN.U0 v) := (powMonoidHom 2 : HN.U0 v →* HN.U0 v).range

lemma index_sq_ne_zero : (sqSub v).index ≠ 0 := by
  rw [HN.index_sq_U0]
  exact mul_ne_zero two_ne_zero (pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
    (mem_nonZeroDivisors_of_ne_zero v.ne_bot)))

instance : (sqSub v).FiniteIndex := ⟨index_sq_ne_zero v⟩

noncomputable instance : Fintype ((HN.U0 v) ⧸ sqSub v) := Fintype.ofFinite _

/-- The representative unit of a coset of $U^2$ in $U$, as an element of $F_v$. -/
abbrev cosetRep (c : (HN.U0 v) ⧸ sqSub v) : Fv := (((Quotient.out c : HN.U0 v) : Fvˣ) : Fv)

lemma valued_cosetRep (c : (HN.U0 v) ⧸ sqSub v) : Valued.v (cosetRep v c) = 1 :=
  (HN.mem_U0 v).mp (Quotient.out c).2

lemma cosetRep_ne_zero (c : (HN.U0 v) ⧸ sqSub v) : cosetRep v c ≠ 0 := Units.ne_zero _

lemma unitSet_eq_iUnion : unitSet v = ⋃ c : (HN.U0 v) ⧸ sqSub v, (fun z => cosetRep v c * z) '' shell v 1 := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · intro hz
    simp only [unitSet, Set.mem_ofPred_eq] at hz
    have hz0 : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    set u : HN.U0 v := ⟨Units.mk0 z hz0, (HN.mem_U0 v).mpr (by simpa using hz)⟩
    set c : (HN.U0 v) ⧸ sqSub v := QuotientGroup.mk u
    refine ⟨c, ?_⟩
    have hc : (QuotientGroup.mk (Quotient.out c) : (HN.U0 v) ⧸ sqSub v) = QuotientGroup.mk u := QuotientGroup.out_eq' c
    obtain ⟨w, hw⟩ := QuotientGroup.eq.mp hc
    refine ⟨(((w : HN.U0 v) : Fvˣ) : Fv) ^ 2, (mem_shell_one v).mpr ⟨(w : HN.U0 v), (w : HN.U0 v).2, rfl⟩, ?_⟩
    have := congrArg (fun g : HN.U0 v => (((g : HN.U0 v) : Fvˣ) : Fv)) hw
    simp only [powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul,
      Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val] at this
    rw [this]
    have h0 := cosetRep_ne_zero v c
    simp only [cosetRep, u, Units.val_mk0] at h0 ⊢
    field_simp
  · rintro ⟨c, w, hw, rfl⟩
    rw [mem_shell_one] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    simp [unitSet, valued_cosetRep, (HN.mem_U0 v).mp hu]

lemma pairwise_disjoint_cosets :
    Pairwise (Function.onFun Disjoint fun c : (HN.U0 v) ⧸ sqSub v => (fun z => cosetRep v c * z) '' shell v 1) := by
  intro c c' hcc'
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  apply hcc'
  rw [mem_shell_one] at ha hb
  obtain ⟨u, hu, rfl⟩ := ha
  obtain ⟨u', hu', rfl⟩ := hb
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq]
  refine ⟨⟨u * u'⁻¹, Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hu')⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp only [powMonoidHom_apply, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul,
    Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  have hu0 : (u' : Fv) ≠ 0 := u'.ne_zero
  have hc0 := cosetRep_ne_zero v c
  have hc'0 := cosetRep_ne_zero v c'
  simp only [cosetRep] at hab hc0 hc'0
  field_simp
  linear_combination (-1 : Fv) * hab

lemma measurableSet_image_mul {a : Fv} (ha : a ≠ 0) {S : Set Fv} (hS : MeasurableSet S) :
    MeasurableSet ((fun z => a * z) '' S) := by
  have : (fun z => a * z) '' S = (fun z => a⁻¹ * z) ⁻¹' S := by
    ext z; simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    · intro h; exact ⟨a⁻¹ * z, h, by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
  rw [this]; exact hS.preimage (measurable_const_mul _)

/-- **Scaling**: $\operatorname{vol}(aS) = |a|_v\operatorname{vol}(S)$ (`measure_smul_eq`, `modK_eq_norm`). -/
lemma haarV_image_mul {a : Fv} (ha : a ≠ 0) (S : Set Fv) :
    haarV v ((fun z => a * z) '' S) = ENNReal.ofReal ‖a‖ * haarV v S := by
  rw [Analysis.Weil.measure_smul_eq (haarV v) ha, WeilRep.modK_eq_norm v ha]

lemma haarV_unitSet : haarV v (unitSet v) = ENNReal.ofReal (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
  have hset : unitSet v = (latticeV v 0 : Set Fv) \ (latticeV v 1 : Set Fv) := by
    ext z
    simp only [unitSet, Set.mem_ofPred_eq, Set.mem_sdiff, SetLike.mem_coe, mem_latticeV]
    constructor
    · intro h; rw [h]; refine ⟨by simp, ?_⟩
      intro h'
      have hlt : exp (-1 : ℤ) < 1 := by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
      exact absurd h' (not_le.mpr (by simp))
    · rintro ⟨h0, h1⟩
      simp only [neg_zero, WithZero.exp_zero] at h0
      have hz0 : z ≠ 0 := by rintro rfl; exact h1 (by simp)
      have hvz : Valued.v z ≠ 0 := (Valued.v).ne_zero_iff.mpr hz0
      rw [← WithZero.exp_log hvz] at h0 h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h0
      rw [WithZero.exp_le_exp] at h1
      rw [WithZero.exp_eq_one]
      omega
  rw [hset, measure_sdiff (by
      intro z hz; simp only [SetLike.mem_coe, mem_latticeV] at hz ⊢
      exact hz.trans (WithZero.exp_le_exp.mpr (by norm_num)))
    (measurableSet_latticeV v 1).nullMeasurableSet (measure_ne_top_of_subset (fun z hz => hz)
      ((isCompact_latticeV v 1).measure_lt_top.ne))]
  have h0 := haarV_real_latticeV v 0
  have h1 := haarV_real_latticeV v 1
  rw [zpow_zero] at h0
  rw [zpow_one, modV_eq] at h1
  rw [← ENNReal.ofReal_toReal ((isCompact_latticeV v 0).measure_lt_top.ne),
    ← ENNReal.ofReal_toReal ((isCompact_latticeV v 1).measure_lt_top.ne),
    ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
  rw [← Measure.real, ← Measure.real, h0, h1]

/-- **The volume of the unit squares** (every finite place): $\operatorname{vol}(U^2) = \dfrac{1 - q^{-1}}{[U : U^2]} = \dfrac{1-q^{-1}}{2q^e}$,
$e = \operatorname{ord}_v2$ (`HN.index_sq_U0`). The $[U:U^2]$ cosets $cU^2$ partition $U$ and have equal volume ($|c|_v = 1$). -/
@[kb "weil1982" "§4.5, p. 107 (T(ρ) covers twice F(x) ∈ ρk_v*²); O'Meara 63:9, p. 163 ((u : u²) = 2(Np)^{ord 2})"]
theorem haarV_shell_one : haarV v (shell v 1) =
    ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) / (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v)) := by
  have hm : MeasurableSet (shell v 1) := measurableSet_shell v one_ne_zero
  have h := haarV_unitSet v
  rw [unitSet_eq_iUnion, measure_iUnion (pairwise_disjoint_cosets v)
    (fun c => measurableSet_image_mul v (cosetRep_ne_zero v c) hm)] at h
  have hc : ∀ c : (HN.U0 v) ⧸ sqSub v, haarV v ((fun z => cosetRep v c * z) '' shell v 1) = haarV v (shell v 1) := by
    intro c
    rw [haarV_image_mul v (cosetRep_ne_zero v c), Valued.toNormedField.norm_eq_one_iff.mpr (valued_cosetRep v c),
      ENNReal.ofReal_one, one_mul]
  simp_rw [hc, ENNReal.tsum_const, ENat.card_eq_coe_natCard] at h
  have hcard : Nat.card ((HN.U0 v) ⧸ sqSub v) = 2 * Ideal.absNorm v.asIdeal ^ HN.ordTwo v := by
    rw [← Subgroup.index, HN.index_sq_U0]
  rw [hcard] at h
  have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  have hpos : (0 : ℝ) < 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v := by positivity
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.eq_div_iff (by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hpos) ENNReal.ofReal_ne_top, ← h]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  push_cast
  ring

/-- $\operatorname{vol}(tU^2) = |t|_v\operatorname{vol}(U^2)$. -/
theorem haarV_shell {t : Fv} (ht : t ≠ 0) : haarV v (shell v t) = ENNReal.ofReal ‖t‖ * haarV v (shell v 1) := by
  rw [shell_eq_image v ht, haarV_image_mul v ht]

/-! ### Counting on shells -/

variable {n : ℕ}

lemma evalIn_smul {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (Q : QuadForm R n) (c : K)
    (x : Fin n → K) : Q.evalIn K (c • x) = c ^ 2 * Q.evalIn K x := by
  simp only [QuadForm.evalIn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **$r_{\mathfrak p^k}(tu^2) = r_{\mathfrak p^k}(t)$** for a unit $u$ ($x \mapsto ux$ permutes the solutions). -/
theorem repCount_mul_unit_sq (Q : QuadForm 𝔬 n) (k : ℕ) (t : 𝔬) {u : 𝔬} (hu : IsUnit u) :
    DVR.repCount Q πv k (t * u ^ 2) = DVR.repCount Q πv k t := by
  unfold DVR.repCount
  set I := Ideal.span {πv ^ k}
  obtain ⟨w, rfl⟩ := hu
  set ū : (𝔬 ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom w
  let e : (Fin n → 𝔬 ⧸ I) ≃ (Fin n → 𝔬 ⧸ I) :=
    { toFun := fun x => ((ū⁻¹ : (𝔬 ⧸ I)ˣ) : 𝔬 ⧸ I) • x, invFun := fun x => (ū : 𝔬 ⧸ I) • x,
      left_inv := fun x => by simp [smul_smul], right_inv := fun x => by simp [smul_smul] }
  refine Nat.card_congr (e.subtypeEquiv fun x => ?_)
  simp only [e, Equiv.coe_fn_mk, evalIn_smul, map_mul, map_pow]
  have h1 : (Ideal.Quotient.mk I) (w : 𝔬) = (ū : 𝔬 ⧸ I) := rfl
  rw [h1]
  have key : ((ū⁻¹ : (𝔬 ⧸ I)ˣ) : 𝔬 ⧸ I) * (ū : 𝔬 ⧸ I) = 1 := Units.inv_mul ū
  constructor
  · intro h; rw [h]
    linear_combination (Ideal.Quotient.mk I t * (((ū⁻¹ : (𝔬 ⧸ I)ˣ) : 𝔬 ⧸ I) * (ū : 𝔬 ⧸ I) + 1)) * key
  · intro h
    linear_combination ((ū : 𝔬 ⧸ I) ^ 2) * h -
      (Q.evalIn (𝔬 ⧸ I) x * (((ū⁻¹ : (𝔬 ⧸ I)ˣ) : 𝔬 ⧸ I) * (ū : 𝔬 ⧸ I) + 1)) * key

/-- $v(4) = \exp(-2e)$. -/
lemma valued_four : Valued.v (4 : Fv) = exp (-(2 * HN.ordTwo v : ℤ)) := by
  rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, HN.valued_two, ← WithZero.exp_add]
  congr 1; ring

/-- **Saturation**: $tU^2$ is a union of cosets of $\mathfrak p^k$ for $k \ge \operatorname{ord}t + 2e + 1$. -/
theorem mem_shell_of_close {t z z' : Fv} (ht : t ≠ 0) {k : ℕ} (hk : -WithZero.log (Valued.v t) + 2 * HN.ordTwo v + 1 ≤ k)
    (hz : z ∈ shell v t) (h : Valued.v (z' - z) ≤ exp (-(k : ℤ))) : z' ∈ shell v t := by
  rw [shell_eq_image v ht] at hz ⊢
  obtain ⟨w, hw, rfl⟩ := hz
  have hvt : Valued.v t ≠ 0 := (Valued.v).ne_zero_iff.mpr ht
  refine ⟨z' / t, ?_, by field_simp⟩
  rw [mem_shell_one] at hw ⊢
  refine unitSq_mem_of_close v hw ?_
  have : z' / t - w = (z' - t * w) / t := by field_simp
  rw [this, map_div₀, valued_four]
  rw [← WithZero.exp_log hvt]
  calc Valued.v (z' - t * w) / exp (WithZero.log (Valued.v t))
      ≤ exp (-(k : ℤ)) / exp (WithZero.log (Valued.v t)) := by
        exact div_le_div_of_nonneg_right h (WithZero.exp_ne_zero).bot_lt.le
    _ = exp (-(k : ℤ) - WithZero.log (Valued.v t)) := by rw [← WithZero.exp_sub]
    _ < exp (-(2 * HN.ordTwo v : ℤ)) := WithZero.exp_lt_exp.mpr (by omega)

/-! ### The pushforward of $dx$ along $Q$ on a shell -/

/-- The closed ball $c + \mathfrak p^k$. -/
def ballK (k : ℕ) (c : Fv) : Set Fv := {z | Valued.v (z - c) ≤ exp (-(k : ℤ))}

lemma ballK_eq_preimage (k : ℕ) (c : Fv) : ballK v k c = (fun z => z + -c) ⁻¹' (latticeV v k : Set Fv) := by
  ext z; simp [ballK, mem_latticeV, sub_eq_add_neg]

lemma measurableSet_ballK (k : ℕ) (c : Fv) : MeasurableSet (ballK v k c) := by
  rw [ballK_eq_preimage]; exact (measurableSet_latticeV v k).preimage (measurable_add_const _)

lemma haarV_ballK (k : ℕ) (c : Fv) : haarV v (ballK v k c) = haarV v (latticeV v k) := by
  rw [ballK_eq_preimage]; exact measure_preimage_add_right _ _ _

/-- An element of a shell of $t \in \mathcal O_v$ is $tu^2$ with $u \in \mathcal O_v^\times$. -/
lemma exists_unit_of_mem_shell {t z : 𝔬} (ht : (t : Fv) ≠ 0) (hz : (z : Fv) ∈ shell v (t : Fv)) :
    ∃ u : 𝔬, IsUnit u ∧ z = t * u ^ 2 := by
  rw [shell_eq_image v ht] at hz
  obtain ⟨w, hw, hzw⟩ := hz
  rw [mem_shell_one] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  have hu1 : Valued.v (u : Fv) = 1 := (HN.mem_U0 v).mp hu
  refine ⟨⟨u, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hu1.le⟩,
    LocalZeta.isUnit_of_valued_eq_one v hu1, ?_⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  exact hzw.symm

open Classical in
/-- **The pushforward of $dx|_{L_v}$ along $Q$ has density $\beta_v$ on the shells** (every finite place): for $t \in \mathcal O_v$, $t \ne 0$,
$$\operatorname{vol}\{x\in L_v : Q(x)\in tU^2\} = \beta_v(t)\cdot\operatorname{vol}(tU^2).$$
*Proof:* for $k \ge \operatorname{ord}t + 2e + 1$ the shell is a union of cosets $c + \mathfrak p^k$ (`mem_shell_of_close`), the preimage is the
union of the congruence sets $\{Q(x)\equiv c\}$, each of volume $r_{\mathfrak p^k}(c)q^{-kn} = r_{\mathfrak p^k}(t)q^{-kn}$
(`volume_congSet`, `repCount_mul_unit_sq`), and $r_{\mathfrak p^k}(t)q^{-k(n-1)} = \beta_v(t)$ for large $k$. -/
theorem volume_shell (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {t : 𝔬} (ht : t ≠ 0) :
    (Measure.pi fun _ : Fin n => haarV v) (latL v n ∩ Q.evalIn Fv ⁻¹' shell v (t : Fv)) =
      ENNReal.ofReal (DVR.localDensity Q πv t) * haarV v (shell v (t : Fv)) := by
  have htF : (t : Fv) ≠ 0 := fun h => ht (Subtype.ext h)
  have hvt : Valued.v (t : Fv) ≠ 0 := (Valued.v).ne_zero_iff.mpr htF
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp
    (DVR.localDensity_eventually_eq Q hQ πv (NF.irreducible_π v) t ht (two_ne_zero_O v))
  set k : ℕ := max K₁ (Int.toNat (-WithZero.log (Valued.v (t : Fv)) + 2 * HN.ordTwo v + 1))
  have hk : -WithZero.log (Valued.v (t : Fv)) + 2 * HN.ordTwo v + 1 ≤ k := by
    have := le_max_right K₁ (Int.toNat (-WithZero.log (Valued.v (t : Fv)) + 2 * HN.ordTwo v + 1))
    omega
  have hβ := hK₁ k (le_max_left _ _)
  have := DVR.finite_quot_pow πv (NF.irreducible_π v) k
  haveI : Fintype (RQ v k) := Fintype.ofFinite _
  set R : Finset (RQ v k) := Finset.univ.filter fun y => (((Quotient.out y : 𝔬)) : Fv) ∈ shell v (t : Fv)
  -- the shell is saturated mod 𝔭^k
  have hsat : ∀ {z z' : Fv}, z ∈ shell v (t : Fv) → Valued.v (z' - z) ≤ exp (-(k : ℤ)) → z' ∈ shell v (t : Fv) :=
    fun hz h => mem_shell_of_close v htF hk hz h
  have hshell_le : ∀ {z : Fv}, z ∈ shell v (t : Fv) → Valued.v z ≤ 1 := by
    rintro z ⟨-, hz⟩
    rw [Set.mem_ofPred_eq] at hz
    rw [hz]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp t.2
  -- reduction: z ∈ 𝔬 is congruent to the lift of its residue
  have hred : ∀ z : 𝔬, Valued.v ((z : Fv) - ((Quotient.out (Ideal.Quotient.mk (Ideal.span {πv ^ k}) z) : 𝔬) : Fv))
      ≤ exp (-(k : ℤ)) := by
    intro z
    rw [← valued_sub_le_iff_mk_eq, Ideal.Quotient.mk_out]
  have hsame : ∀ {y y' : RQ v k}, Valued.v (((Quotient.out y : 𝔬) : Fv) - ((Quotient.out y' : 𝔬) : Fv))
      ≤ exp (-(k : ℤ)) → y = y' := by
    intro y y' h
    rw [← valued_sub_le_iff_mk_eq, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h
    exact h
  -- the preimage as a disjoint union of congruence sets
  have hU : latL v n ∩ Q.evalIn Fv ⁻¹' shell v (t : Fv) = ⋃ y ∈ R, congSet v Q ((Quotient.out y : 𝔬) : Fv) k := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, R, congSet]
    constructor
    · rintro ⟨hx, hQx⟩
      set z : 𝔬 := ⟨Q.evalIn Fv x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr
        (valued_evalIn_le_one v Q hx)⟩
      refine ⟨Ideal.Quotient.mk _ z, ?_, hx, hred z⟩
      refine hsat hQx ?_
      rw [← Valuation.map_neg, neg_sub]; exact hred z
    · rintro ⟨y, hy, hx, hxy⟩
      exact ⟨hx, hsat hy hxy⟩
  have hUs : shell v (t : Fv) = ⋃ y ∈ R, ballK v k ((Quotient.out y : 𝔬) : Fv) := by
    ext z
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop, R, ballK,
      Set.mem_ofPred_eq]
    constructor
    · intro hz
      set z' : 𝔬 := ⟨z, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hshell_le hz)⟩
      refine ⟨Ideal.Quotient.mk _ z', hsat hz ?_, hred z'⟩
      rw [← Valuation.map_neg, neg_sub]; exact hred z'
    · rintro ⟨y, hy, hzy⟩
      exact hsat hy hzy
  have hdisj1 : Set.PairwiseDisjoint (R : Set (RQ v k)) fun y => congSet v Q ((Quotient.out y : 𝔬) : Fv) k := by
    intro y _ y' _ hyy'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨-, h1⟩ ⟨-, h2⟩
    apply hyy'
    apply hsame
    have : ((Quotient.out y : 𝔬) : Fv) - ((Quotient.out y' : 𝔬) : Fv) =
        (Q.evalIn Fv x - ((Quotient.out y' : 𝔬) : Fv)) - (Q.evalIn Fv x - ((Quotient.out y : 𝔬) : Fv)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  have hdisj2 : Set.PairwiseDisjoint (R : Set (RQ v k)) fun y => ballK v k ((Quotient.out y : 𝔬) : Fv) := by
    intro y _ y' _ hyy'
    rw [Function.onFun, Set.disjoint_left]
    rintro z h1 h2
    apply hyy'
    apply hsame
    have : ((Quotient.out y : 𝔬) : Fv) - ((Quotient.out y' : 𝔬) : Fv) =
        (z - ((Quotient.out y' : 𝔬) : Fv)) - (z - ((Quotient.out y : 𝔬) : Fv)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  rw [hU, measure_biUnion_finset hdisj1 (fun y _ => measurableSet_congSet v Q _ k)]
  rw [hUs, measure_biUnion_finset hdisj2 (fun y _ => measurableSet_ballK v k _)]
  have hc : ∀ y ∈ R, (Measure.pi fun _ : Fin n => haarV v) (congSet v Q ((Quotient.out y : 𝔬) : Fv) k) =
      (DVR.repCount Q πv k t : ENNReal) * haarV v (latticeV v k) ^ n := by
    intro y hy
    rw [volume_congSet]
    obtain ⟨u, hu, hyu⟩ := exists_unit_of_mem_shell v htF (Finset.mem_filter.mp hy).2
    rw [hyu, repCount_mul_unit_sq v Q k t hu]
  simp_rw [Finset.sum_congr rfl hc, Finset.sum_congr rfl fun y (_ : y ∈ R) => haarV_ballK v k _]
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  -- the volume of 𝔭^k is q^{-k}
  have hq : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have hh : haarV v (latticeV v k) = ENNReal.ofReal (((DVR.q 𝔬 : ℝ) ^ k)⁻¹) := by
    rw [← ENNReal.ofReal_toReal ((isCompact_latticeV v k).measure_lt_top.ne), ← Measure.real,
      real_latticeV_eq v (haarV v) k, haarV_real_O, one_mul]
  rw [hh]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega] at hβ
  set c : ℝ := (R.card : ℝ)
  set r : ℝ := (DVR.repCount Q πv k t : ℝ)
  set h : ℝ := ((DVR.q 𝔬 : ℝ) ^ k)⁻¹
  have hh0 : 0 ≤ h := by positivity
  have e1 : (R.card : ENNReal) = ENNReal.ofReal c := (ENNReal.ofReal_natCast _).symm
  have e2 : (DVR.repCount Q πv k t : ENNReal) = ENNReal.ofReal r := (ENNReal.ofReal_natCast _).symm
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hβ0 : 0 ≤ DVR.localDensity Q πv t := by rw [← hβ]; positivity
  have lhs : ENNReal.ofReal c * (ENNReal.ofReal r * ENNReal.ofReal h ^ (m + 1)) =
      ENNReal.ofReal (c * (r * h ^ (m + 1))) := by
    rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hr0, ENNReal.ofReal_pow hh0]
  have rhs : ENNReal.ofReal (DVR.localDensity Q πv t) * (ENNReal.ofReal c * ENNReal.ofReal h) =
      ENNReal.ofReal (DVR.localDensity Q πv t * (c * h)) := by
    rw [ENNReal.ofReal_mul hβ0, ENNReal.ofReal_mul hc0]
  rw [e1, e2, lhs, rhs, ← hβ]
  congr 1
  simp only [h]
  rw [pow_succ, pow_mul]
  have hqk : ((DVR.q 𝔬 : ℝ) ^ k) ≠ 0 := by positivity
  rw [inv_pow, div_eq_mul_inv]
  ring

/-! ### The spherical local factor as a series of local densities -/

lemma eq_exp_iff_le_not_le {a : ℤᵐ⁰} (j : ℕ) :
    (a ≤ exp (-(j : ℤ)) ∧ ¬ a ≤ exp (-((j + 1 : ℕ) : ℤ))) ↔ a = exp (-(j : ℤ)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have ha : a ≠ 0 := by rintro rfl; exact h2 zero_le'
    rw [← WithZero.exp_log ha] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    rw [WithZero.exp_inj]; push_cast at h2; omega
  · rintro rfl
    refine ⟨le_rfl, fun h => ?_⟩
    rw [WithZero.exp_le_exp] at h; push_cast at h; omega

/-- $\operatorname{ord}_v\rho$ as an integer ($v(\rho) = \exp(-\operatorname{ord}\rho)$). -/
def ordF (ρ : Fv) : ℤ := -WithZero.log (Valued.v ρ)

/-- The point $t_j = \rho\pi^{j - \operatorname{ord}\rho}$ of valuation $\exp(-j)$ (in the square class of $\rho$ when $j \equiv \operatorname{ord}\rho$). -/
def tLev (ρ : Fv) (j : ℕ) : Fv := ρ * (πv : Fv) ^ ((j : ℤ) - ordF v ρ)

lemma valued_tLev {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) : Valued.v (tLev v ρ j) = exp (-(j : ℤ)) := by
  have hvρ : Valued.v ρ ≠ 0 := (Valued.v).ne_zero_iff.mpr hρ
  rw [tLev, map_mul, LocalZeta.valued_π_zpow, ← WithZero.exp_log hvρ, ← WithZero.exp_add, ordF]
  congr 1; ring

lemma tLev_ne_zero {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) : tLev v ρ j ≠ 0 := by
  intro h
  have := valued_tLev v hρ j
  rw [h, map_zero] at this
  exact WithZero.exp_ne_zero this.symm

/-- $t_j$ as an element of $\mathcal O_v$. -/
def tLevO {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) : 𝔬 :=
  ⟨tLev v ρ j, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
    rw [valued_tLev v hρ j, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)⟩

lemma coe_tLevO {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) : ((tLevO v hρ j : 𝔬) : Fv) = tLev v ρ j := rfl

lemma sqClass_tLev {ρ : Fv} (hρ : ρ ≠ 0) {j : ℕ} (hj : Even ((j : ℤ) - ordF v ρ)) :
    sqClass (tLev v ρ j) = sqClass ρ := by
  obtain ⟨m, hm⟩ := hj
  have hπ0 : (πv : Fv) ≠ 0 := by
    intro h; have := NF.valued_π v; rw [h, map_zero] at this; exact WithZero.zero_ne_coe this
  rw [tLev, hm, show m + m = 2 * m by ring, zpow_mul, show ((πv : Fv) ^ (2 : ℤ)) ^ m = ((πv : Fv) ^ m) ^ 2 by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]; norm_num]
  exact sqClass_mul_sq ρ (zpow_ne_zero _ hπ0)

/-- **The level series term**: $|t_j|^{1+s}\beta_v(t_j)$ if $j \equiv \operatorname{ord}\rho \pmod 2$, else $0$. -/
def levelTerm (Q : QuadForm 𝔬 n) {ρ : Fv} (hρ : ρ ≠ 0) (s : ℝ) (j : ℕ) : ℝ :=
  if Even ((j : ℤ) - ordF v ρ) then ‖tLev v ρ j‖ ^ (1 + s) * DVR.localDensity Q πv (tLevO v hρ j) else 0

/-- The level set $\{\operatorname{ord}Q = j\}$ meets $\{Q\in\rho F_v^{\times2}\}$ exactly in the shell of $t_j$ (if $j \equiv \operatorname{ord}\rho$), else not at all. -/
lemma levelSet_inter_sqClass_eq (Q : QuadForm 𝔬 n) {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) :
    levelSet v Q j ∩ Q.evalIn Fv ⁻¹' sqClass ρ =
      if Even ((j : ℤ) - ordF v ρ) then latL v n ∩ Q.evalIn Fv ⁻¹' shell v (tLev v ρ j) else ∅ := by
  have hlev : ∀ x, x ∈ levelSet v Q j ↔ x ∈ latL v n ∧ Valued.v (Q.evalIn Fv x) = exp (-(j : ℤ)) := by
    intro x
    simp only [levelSet, congSet, Set.mem_sdiff, Set.mem_ofPred_eq, ZeroMemClass.coe_zero, sub_zero]
    constructor
    · rintro ⟨⟨hx, h1⟩, h2⟩
      exact ⟨hx, (eq_exp_iff_le_not_le j).mp ⟨h1, fun h => h2 ⟨hx, h⟩⟩⟩
    · rintro ⟨hx, h⟩
      have := (eq_exp_iff_le_not_le j).mpr h
      exact ⟨⟨hx, this.1⟩, fun h' => this.2 h'.2⟩
  have hvρ : Valued.v ρ ≠ 0 := (Valued.v).ne_zero_iff.mpr hρ
  split_ifs with hj
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hlev, shell, sqClass_tLev v hρ hj, Set.mem_ofPred_eq,
      valued_tLev v hρ j]
    tauto
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hlev, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hv⟩, ⟨y, hy, hxy⟩⟩
    apply hj
    have hvy : Valued.v y ≠ 0 := (Valued.v).ne_zero_iff.mpr hy
    rw [hxy, map_mul, map_pow, ← WithZero.exp_log hvρ, ← WithZero.exp_log hvy, ← WithZero.exp_nsmul,
      ← WithZero.exp_add, WithZero.exp_inj] at hv
    refine ⟨-WithZero.log (Valued.v y), ?_⟩
    simp only [ordF]
    simp at hv
    omega

lemma norm_two_eq : ‖(2 : Fv)‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v)⁻¹ := by
  rw [LocalZeta.norm_eq_absNorm_pow v two_ne_zero, HN.valued_two, WithZero.log_exp, zpow_neg, zpow_natCast]

lemma norm_tLev {ρ : Fv} (hρ : ρ ≠ 0) (j : ℕ) : ‖tLev v ρ j‖ = ((DVR.q 𝔬 : ℝ) ^ j)⁻¹ := by
  rw [LocalZeta.norm_eq_absNorm_pow v (tLev_ne_zero v hρ j), valued_tLev v hρ j, WithZero.log_exp,
    NF.q_completion, zpow_neg, zpow_natCast]

lemma real_shell_one : (haarV v).real (shell v 1) =
    (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) / (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v) := by
  rw [Measure.real, haarV_shell_one, ENNReal.toReal_ofReal]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot))
  have : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have : (0 : ℝ) < 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v := by positivity
  exact div_nonneg (by linarith) this.le

/-- **Weil's local spherical factor as a series of local densities** (Weil 1982, §4.5, (3), p. 102; p. 107): at every finite
place $v$, for $Q$ over $\mathcal O_F$ nondegenerate, $n \ge 1$, $\rho \in F_v^\times$ and $s \ge 0$,
$$Z_\mathfrak p(s,\rho) = \frac{2}{1-q^{-1}}\int_{x\in L_v,\ Q(x)\in\rho F_v^{\times2}}|Q(x)|_v^s\,dx
  = |2|_v\sum_{j\ge0,\ j\equiv\operatorname{ord}\rho\ (2)}|t_j|_v^{1+s}\,\beta_v(t_j),\qquad t_j = \rho\pi^{j-\operatorname{ord}\rho},$$
i.e. `HasSum (levelTerm …) (|2|_v⁻¹ · sphLocal Q v ρ s)`. The $2$ and $(1-q^{-1})^{-1}$ of `sphLocal` cancel against
$\operatorname{vol}(U^2) = (1-q^{-1})|2|_v/2$; this is where $[U:U^2] = 2/|2|_v$ (dyadic places included) enters Weil's bookkeeping. -/
@[kb "weil1982" "§4.5, (3), p. 102 and p. 107 (T(ρ)_v covers twice {F(x) ∈ ρk_v*²}); §4.3, p. 89"]
theorem hasSum_levelTerm (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {ρ : Fv} (hρ : ρ ≠ 0)
    {s : ℝ} (hs : 0 ≤ s) :
    HasSum (levelTerm v (NF.Qp v Q) hρ s) (‖(2 : Fv)‖⁻¹ * sphLocal Q v ρ s) := by
  set Qv := NF.Qp v Q
  have hQv : Qv.Nondegenerate := NF.nondegenerate_Qp v hQ
  have hA := measurableSet_preimage_sqClass v Qv hρ
  have h := hasSum_setIntegral_level v (haarV v) Qv hQv hn hA hs
  set c := (haarV v).real (shell v 1)
  have hcdef : c = (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) / (2 * (Ideal.absNorm v.asIdeal : ℝ) ^ HN.ordTwo v) :=
    real_shell_one v
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [← NF.q_completion]; exact_mod_cast GlobalZeta.one_lt_qv v
  have hc : 0 < c := by
    rw [hcdef]
    have : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
    exact div_pos (by linarith) (by positivity)
  have hq0 : (0 : ℝ) < DVR.q 𝔬 := by exact_mod_cast q_pos v
  have hterm : ∀ j : ℕ, ((DVR.q 𝔬 : ℝ) ^ (-s)) ^ j *
      (Measure.pi fun _ : Fin n => haarV v).real (levelSet v Qv j ∩ Qv.evalIn Fv ⁻¹' sqClass ρ) =
      c * levelTerm v Qv hρ s j := by
    intro j
    rw [levelSet_inter_sqClass_eq v Qv hρ j, levelTerm]
    split_ifs with hj
    · have ht0 : tLevO v hρ j ≠ 0 := fun h0 => tLev_ne_zero v hρ j (congrArg Subtype.val h0)
      have hv := volume_shell v Qv hQv hn ht0
      rw [coe_tLevO] at hv
      have hβ0 : 0 ≤ DVR.localDensity Qv πv (tLevO v hρ j) := by
        obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (DVR.localDensity_eventually_eq Qv hQv πv
          (NF.irreducible_π v) _ ht0 (two_ne_zero_O v))
        rw [← hK K le_rfl]; positivity
      rw [Measure.real, hv, haarV_shell v (tLev_ne_zero v hρ j), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal hβ0, ← Measure.real,
        norm_tLev v hρ j]
      have hqj : (0 : ℝ) < (DVR.q 𝔬 : ℝ) ^ j := by positivity
      rw [Real.rpow_add (inv_pos.mpr hqj), Real.rpow_one, LocalZeta.rpow_inv_pow _ hq0]
      ring
    · simp
  have h' : HasSum (fun j => c * levelTerm v Qv hρ s j) (sphInt Q v ρ s) := by
    have := h.congr_fun fun j => (hterm j).symm
    exact this
  have h'' := h'.div_const c
  simp_rw [mul_div_cancel_left₀ _ hc.ne'] at h''
  convert h'' using 1
  rw [sphLocal, hcdef, norm_two_eq, NF.q_completion]
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have h1 : (1 : ℝ) - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≠ 0 := by
    have : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hN
    linarith
  field_simp

end QuadFormsKB.SphericalLocalFactor
