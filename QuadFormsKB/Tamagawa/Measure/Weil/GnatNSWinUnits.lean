/-
# $[\mathcal O_v^\times : \mathcal O_v^{\times2}] = 2q^{s}$

**Layer:** a number field $F$ and a finite place $v$ (dyadic places included), $|2|_v = q^{-s}$.

* `unitsSub v` $=\mathcal O_v^\times$ (compact open, `isCompact_unitsVSub`), `oneSub v k` $= 1+\mathfrak p^k$, `sqSub F v`
  $=\mathcal O_v^{\times2}$ (from `GnatNSWinScalar`).
* **`relIndex_sqSub`**: $[\mathcal O_v^\times : \mathcal O_v^{\times2}] = 2q^s$ (squaring maps $\pm(1+\mathfrak p^k)$ onto
  $1+\mathfrak p^{k+s}$ for $k > s$, `exists_sq_eq_near_one`; $[1+\mathfrak p^k : 1+\mathfrak p^{k+s}] = q^s$ by
  `omegaV_oneAdd`).
* **`omegaV_unitsVSub_eq_sq`**: $\omega_v(\mathcal O_v^\times) = 2q^s\,\omega_v(\mathcal O_v^{\times2})$.

Source: standard (e.g. Neukirch, *Algebraic Number Theory*, II.5.7 [unverified]).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinScalar

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa LerayPadic LocalDensity

section UnitIndex

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $\mathcal O_v^\times$ as a subgroup of $F_v^\times$. -/
def unitsSub : Subgroup Fvˣ where
  carrier := unitsVSub v
  mul_mem' := mul_mem_unitsVSub
  one_mem' := one_mem_unitsVSub v
  inv_mem' := inv_mem_unitsVSub

theorem unitsVSub_eq : unitsVSub v = {u : Fvˣ | (u : Fv) ∈ v.adicCompletionIntegers F ∧
    ((u⁻¹ : Fvˣ) : Fv) ∈ v.adicCompletionIntegers F} := by
  ext u
  simp only [unitsVSub, mem_ofPred_eq, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val,
    map_inv₀]
  constructor
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have h0 : Valued.v (u : Fv) ≠ 0 := by simp
    have := mul_le_mul' (le_refl (Valued.v (u : Fv))) h2
    rw [mul_inv_cancel₀ h0, mul_one] at this
    exact le_antisymm h1 this

theorem isCompact_unitsVSub : IsCompact (unitsVSub v) := by
  have hO : IsCompact (v.adicCompletionIntegers F : Set Fv) := by
    have := QuadFormsKB.Analysis.isCompact_latticeV v 0
    convert this using 1
    ext x; simp [QuadFormsKB.Analysis.mem_latticeV, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [unitsVSub_eq, Units.isEmbedding_embedProduct.isCompact_iff]
  have hK : IsCompact ((v.adicCompletionIntegers F : Set Fv) ×ˢ
      (MulOpposite.op '' (v.adicCompletionIntegers F : Set Fv))) :=
    hO.prod (hO.image MulOpposite.continuous_op)
  have hC : IsClosed {p : Fv × Fvᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} :=
    (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
      (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  have hset : Units.embedProduct Fv '' {u : Fvˣ | (u : Fv) ∈ v.adicCompletionIntegers F ∧
      ((u⁻¹ : Fvˣ) : Fv) ∈ v.adicCompletionIntegers F} =
      ((v.adicCompletionIntegers F : Set Fv) ×ˢ (MulOpposite.op '' (v.adicCompletionIntegers F : Set Fv))) ∩
        {p : Fv × Fvᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨u, ⟨hu, hu'⟩, h⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨⟨hu, ⟨_, hu', rfl⟩⟩, u.mul_inv, u.inv_mul⟩
    · rintro ⟨⟨hx, ⟨y', hy', rfl⟩⟩, h1, h2⟩
      exact ⟨⟨x, y', h1, h2⟩, ⟨hx, hy'⟩, rfl⟩
  rw [hset]
  exact hK.inter_right hC

/-- $1+\mathfrak p^k$ ($k\ge1$) as a subgroup of $F_v^\times$. -/
def oneSub (k : ℕ) (hk : 1 ≤ k) : Subgroup Fvˣ where
  carrier := {r : Fvˣ | Valued.v ((r : Fv) - 1) ≤ exp (-(k : ℤ))}
  mul_mem' {r s} hr hs := by
    change Valued.v ((r : Fv) * s - 1) ≤ _
    have hs1 : Valued.v (s : Fv) = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v hk hs)
    rw [show (r : Fv) * s - 1 = ((r : Fv) - 1) * s + ((s : Fv) - 1) by ring]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ hs)
    rw [map_mul, hs1, mul_one]; exact hr
  one_mem' := by change Valued.v ((1 : Fv) - 1) ≤ _; rw [sub_self, map_zero]; exact zero_le
  inv_mem' {r} hr := by
    change Valued.v (((r⁻¹ : Fvˣ) : Fv) - 1) ≤ _
    have hr1 : Valued.v (r : Fv) = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v hk hr)
    rw [Units.val_inv_eq_inv_val, show ((r : Fv))⁻¹ - 1 = -(((r : Fv) - 1) * (r : Fv)⁻¹) by
      field_simp; ring, Valuation.map_neg, map_mul, map_inv₀, hr1, inv_one, mul_one]
    exact hr

theorem isOpen_oneSub (k : ℕ) (hk : 1 ≤ k) : IsOpen (oneSub v k hk : Set Fvˣ) := by
  have hL : IsOpen (QuadFormsKB.Analysis.latticeV v (k : ℤ) : Set Fv) := by
    rw [QuadFormsKB.Analysis.coe_latticeV]
    refine IsUltrametricDist.isOpen_closedBall _ ?_
    rw [Ne, norm_eq_zero]; exact zpow_ne_zero _ (QuadFormsKB.HN.ϖ_ne_zero v)
  have : (oneSub v k hk : Set Fvˣ) = Units.val ⁻¹' ((fun x => x - 1) ⁻¹'
      (QuadFormsKB.Analysis.latticeV v (k : ℤ) : Set Fv)) := by
    ext r; simp [oneSub, QuadFormsKB.Analysis.mem_latticeV]
  rw [this]
  exact (hL.preimage (continuous_id.sub continuous_const)).preimage Units.continuous_val

theorem oneSub_le_unitsSub (k : ℕ) (hk : 1 ≤ k) : oneSub v k hk ≤ unitsSub v := fun r hr =>
  valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v hk hr)

theorem oneSub_anti {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k') :
    oneSub v k' (hk.trans hkk) ≤ oneSub v k hk := fun r hr =>
  (show Valued.v ((r : Fv) - 1) ≤ _ from hr).trans (exp_le_exp.2 (by omega))

theorem sqSub_le_unitsSub : sqSub F v ≤ unitsSub v := by
  rintro _ ⟨r, hr, rfl⟩
  change Valued.v ((r ^ 2 : Fvˣ) : Fv) = 1
  rw [Units.val_pow_eq_pow_val, map_pow, hr, one_pow]

theorem oneSub_le_sqSub {k : ℕ} (hk : sExp v < k) :
    oneSub v (k + sExp v) (by omega) ≤ sqSub F v := by
  intro r hr
  obtain ⟨t, ht, ht1⟩ := exists_sq_eq_near_one v (valued_two_eq v) hk (t := (r : Fv)) hr
  have htv : Valued.v t = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v (by omega) ht1)
  have ht0 : t ≠ 0 := by intro h; rw [h, map_zero] at htv; exact zero_ne_one htv
  exact ⟨Units.mk0 t ht0, htv, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, ht])⟩

theorem mem_zpowers_neg_one {z : Fvˣ} (hz : z ∈ Subgroup.zpowers (-1 : Fvˣ)) : z = 1 ∨ z = -1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rcases Int.even_or_odd k with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

theorem card_zpowers_neg_one : Nat.card (Subgroup.zpowers (-1 : Fvˣ)) = 2 := by
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one]
  have : ringChar Fv ≠ 2 := by rw [ringChar.eq_zero]; norm_num
  simp [this]

theorem neg_one_not_mem_oneSub {k : ℕ} (hk : sExp v < k) : (-1 : Fvˣ) ∉ oneSub v k (by omega) := by
  intro h
  change Valued.v (((-1 : Fvˣ) : Fv) - 1) ≤ _ at h
  rw [Units.val_neg, Units.val_one, show (-1 : Fv) - 1 = -2 by ring, Valuation.map_neg, valued_two_eq v,
    exp_le_exp] at h
  omega

/-- $[\pm(1+\mathfrak p^k) : 1+\mathfrak p^k] = 2$ for $k > s$. -/
theorem relIndex_oneSub_sup {k : ℕ} (hk : sExp v < k) :
    (oneSub v k (by omega)).relIndex (oneSub v k (by omega) ⊔ Subgroup.zpowers (-1)) = 2 := by
  rw [Subgroup.relIndex_sup_left]
  have h := Subgroup.relIndex_mul_card (H := oneSub v k (by omega)) (K := Subgroup.zpowers (-1 : Fvˣ))
  have hbot : oneSub v k (by omega) ⊓ Subgroup.zpowers (-1 : Fvˣ) = ⊥ := by
    rw [eq_bot_iff]; intro z hz
    rcases mem_zpowers_neg_one v (Subgroup.mem_inf.1 hz).2 with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exact absurd (h1 ▸ (Subgroup.mem_inf.1 hz).1) (neg_one_not_mem_oneSub v hk)
  rw [hbot, Subgroup.card_bot, mul_one, card_zpowers_neg_one] at h
  exact h

/-- The squaring map. -/
abbrev sqHom : Fvˣ →* Fvˣ := powMonoidHom 2

theorem map_sqHom_unitsSub : (unitsSub v).map (sqHom v) = sqSub F v := by
  ext c; constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩

theorem comap_sqHom_inf {k : ℕ} (hk : sExp v < k) :
    (oneSub v (k + sExp v) (by omega)).comap (sqHom v) ⊓ unitsSub v =
      (oneSub v k (by omega) ⊔ Subgroup.zpowers (-1)) ⊓ unitsSub v := by
  ext r
  simp only [Subgroup.mem_inf, Subgroup.mem_comap]
  constructor
  · rintro ⟨h2, hr⟩
    have h2' : Valued.v (((r ^ 2 : Fvˣ) : Fv) - 1) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := h2
    obtain ⟨t, ht, ht1⟩ := exists_sq_eq_near_one v (valued_two_eq v) hk h2'
    have htv : Valued.v t = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v (by omega) ht1)
    have ht0 : t ≠ 0 := by intro h; rw [h, map_zero] at htv; exact zero_ne_one htv
    set u := Units.mk0 t ht0
    have hu : u ∈ oneSub v k (by omega) := ht1
    have hsq : (r * u⁻¹) ^ 2 = 1 := by
      apply Units.ext
      rw [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_mk0, inv_pow, ht, Units.val_one, Units.val_pow_eq_pow_val, mul_inv_cancel₀ (pow_ne_zero _ (by simp))]
    have hpm : r * u⁻¹ = 1 ∨ r * u⁻¹ = -1 := by
      have hv := congrArg Units.val hsq
      rw [Units.val_pow_eq_pow_val, Units.val_one] at hv
      have : (((r * u⁻¹ : Fvˣ) : Fv) - 1) * (((r * u⁻¹ : Fvˣ) : Fv) + 1) = 0 := by linear_combination hv
      rcases mul_eq_zero.1 this with h | h
      · left; apply Units.ext; rw [Units.val_one]; linear_combination h
      · right; apply Units.ext; rw [Units.val_neg, Units.val_one]; linear_combination h
    refine ⟨Subgroup.mem_sup.2 ⟨u, hu, r * u⁻¹, ?_, by rw [mul_left_comm, mul_inv_cancel, mul_one]⟩, hr⟩
    rcases hpm with h | h <;> rw [h]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rintro ⟨hs, hr⟩
    refine ⟨?_, hr⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.1 hs
    have hz2 : z ^ 2 = 1 := by
      rcases mem_zpowers_neg_one v hz with h | h <;> rw [h] <;> simp
    suffices H : Valued.v ((((u * z) ^ 2 : Fvˣ) : Fv) - 1) ≤ exp (-((k + sExp v : ℕ) : ℤ)) from H
    rw [mul_pow, hz2, mul_one, Units.val_pow_eq_pow_val]
    have hu' : Valued.v ((u : Fv) - 1) ≤ exp (-(k : ℤ)) := hu
    rw [show (u : Fv) ^ 2 - 1 = 2 * ((u : Fv) - 1) + ((u : Fv) - 1) ^ 2 by ring]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul, valued_two_eq v, show (-((k + sExp v : ℕ) : ℤ)) = -(sExp v : ℤ) + -(k : ℤ) by push_cast; ring,
        exp_add]
      exact mul_le_mul' le_rfl hu'
    · rw [map_pow]
      calc Valued.v ((u : Fv) - 1) ^ 2 ≤ exp (-(k : ℤ)) ^ 2 := pow_le_pow_left₀ zero_le hu' 2
        _ ≤ _ := by rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]; push_cast; omega

theorem isOpen_sqSub : IsOpen (sqSub F v : Set Fvˣ) :=
  Subgroup.isOpen_mono (oneSub_le_sqSub v (k := sExp v + 1) (by omega)) (isOpen_oneSub v _ _)

theorem relIndex_ne_zero_unitsSub {H : Subgroup Fvˣ} (hH : IsOpen (H : Set Fvˣ)) : H.relIndex (unitsSub v) ≠ 0 :=
  relIndex_ne_zero_of_isOpen (isCompact_unitsVSub v) hH

theorem selfDualV_latticeV_ne_zero (k : ℤ) : Analysis.selfDualV v (Analysis.latticeV v k) ≠ 0 := by
  have hL : IsOpen (QuadFormsKB.Analysis.latticeV v k : Set Fv) := by
    rw [QuadFormsKB.Analysis.coe_latticeV]
    refine IsUltrametricDist.isOpen_closedBall _ ?_
    rw [Ne, norm_eq_zero]; exact zpow_ne_zero _ (QuadFormsKB.HN.ϖ_ne_zero v)
  exact (hL.measure_pos _ ⟨0, (QuadFormsKB.Analysis.latticeV v k).zero_mem⟩).ne'

theorem selfDualV_latticeV_ne_top (k : ℤ) : Analysis.selfDualV v (Analysis.latticeV v k) ≠ ⊤ :=
  (QuadFormsKB.Analysis.isCompact_latticeV v k).measure_lt_top.ne

/-- $[1+\mathfrak p^k : 1+\mathfrak p^{k+j}] = q^j$. -/
theorem relIndex_oneSub (k j : ℕ) (hk : 1 ≤ k) :
    ((oneSub v (k + j) (by omega)).relIndex (oneSub v k hk) : ℝ≥0∞) = (DVR.q 𝔬 : ℝ≥0∞) ^ j := by
  have hfin : (oneSub v (k + j) (by omega)).relIndex (oneSub v k hk) ≠ 0 :=
    relIndex_ne_zero_of_isOpen ((isCompact_unitsVSub v).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_oneSub v k hk)) (oneSub_le_unitsSub v k hk))
      (isOpen_oneSub v _ _)
  have e := measure_subgroup_eq_relIndex_mul (omegaV v) (isOpen_oneSub v (k + j) (by omega))
    (oneSub_anti v hk (by omega)) hfin
  have h1 : omegaV v (oneSub v k hk : Set Fvˣ) = Analysis.selfDualV v (Analysis.latticeV v (k : ℤ)) :=
    omegaV_oneAdd v hk
  have h2 : omegaV v (oneSub v (k + j) (by omega) : Set Fvˣ) =
      Analysis.selfDualV v (Analysis.latticeV v ((k + j : ℕ) : ℤ)) := omegaV_oneAdd v (by omega)
  rw [h1, h2, selfDualV_latticeV_nat, selfDualV_latticeV_nat] at e
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (DVR.q_pos (R := 𝔬)).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h0 := selfDualV_latticeV_ne_zero v 0
  have ht := selfDualV_latticeV_ne_top v 0
  set V := Analysis.selfDualV v (Analysis.latticeV v 0)
  set R := ((oneSub v (k + j) (by omega)).relIndex (oneSub v k hk) : ℝ≥0∞)
  rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))] at e
  have hk' : ((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ * V ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top hqt)) h0
  have hkt : ((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ * V ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (pow_ne_zero _ hq0)) ht
  have e2 : 1 * (((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ * V) = (R * ((DVR.q 𝔬 : ℝ≥0∞) ^ j)⁻¹) * (((DVR.q 𝔬 : ℝ≥0∞) ^ k)⁻¹ * V) := by
    rw [one_mul]; convert e using 1; ring
  have e3 := (ENNReal.mul_left_inj hk' hkt).1 e2
  calc R = R * (((DVR.q 𝔬 : ℝ≥0∞) ^ j)⁻¹ * (DVR.q 𝔬 : ℝ≥0∞) ^ j) := by
        rw [ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one]
    _ = (R * ((DVR.q 𝔬 : ℝ≥0∞) ^ j)⁻¹) * (DVR.q 𝔬 : ℝ≥0∞) ^ j := by ring
    _ = _ := by rw [← e3, one_mul]

/-- **$[\mathcal O_v^\times : \mathcal O_v^{\times2}] = 2q^{s}$.** -/
theorem relIndex_sqSub : (sqSub F v).relIndex (unitsSub v) = 2 * DVR.q 𝔬 ^ sExp v := by
  set k := sExp v + 1
  have hk : sExp v < k := by omega
  set U := oneSub v k (by omega)
  set U' := oneSub v (k + sExp v) (by omega)
  set μ₂ := Subgroup.zpowers (-1 : Fvˣ)
  set O := unitsSub v
  set Q := sqSub F v
  have hUO : U ≤ O := oneSub_le_unitsSub v k _
  have hμO : μ₂ ≤ O := by
    rw [Subgroup.zpowers_le]
    change Valued.v (((-1 : Fvˣ) : Fv)) = 1
    rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one]
  have hU'U : U' ≤ U := oneSub_anti v _ (by omega)
  have hU'Q : U' ≤ Q := oneSub_le_sqSub v hk
  have ha := Subgroup.relIndex_mul_relIndex U' Q O hU'Q (sqSub_le_unitsSub v)
  have hb := Subgroup.relIndex_mul_relIndex U' U O hU'U hUO
  have hc := Subgroup.relIndex_mul_relIndex U (U ⊔ μ₂) O le_sup_left (sup_le hUO hμO)
  rw [relIndex_oneSub_sup v hk] at hc
  have hd : U'.relIndex Q = (U ⊔ μ₂).relIndex O := by
    rw [show Q = (unitsSub v).map (sqHom v) from (map_sqHom_unitsSub v).symm, ← Subgroup.relIndex_comap,
      ← Subgroup.inf_relIndex_right, comap_sqHom_inf v hk, Subgroup.inf_relIndex_right]
  have he : U'.relIndex U = DVR.q 𝔬 ^ sExp v := by
    have := relIndex_oneSub v k (sExp v) (by omega)
    exact_mod_cast this
  have hX : (U ⊔ μ₂).relIndex O ≠ 0 := by
    intro h0
    have : U.relIndex O = 0 := by rw [← hc, h0, mul_zero]
    exact relIndex_ne_zero_unitsSub v (isOpen_oneSub v k _) this
  rw [hd] at ha
  rw [he, ← hc] at hb
  have : (U ⊔ μ₂).relIndex O * Q.relIndex O = (U ⊔ μ₂).relIndex O * (2 * DVR.q 𝔬 ^ sExp v) := by
    rw [ha, ← hb]; ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hX) this

/-- **$\omega_v(\mathcal O_v^\times) = 2q^s\,\omega_v(\mathcal O_v^{\times2})$.** -/
theorem omegaV_unitsVSub_eq_sq :
    omegaV v (unitsVSub v) = (2 * (DVR.q 𝔬 : ℝ≥0∞) ^ sExp v) * omegaV v (sqUnits F v) := by
  have e := measure_subgroup_eq_relIndex_mul (omegaV v) (A := unitsSub v) (B := sqSub F v) (isOpen_sqSub v)
    (sqSub_le_unitsSub v) (relIndex_ne_zero_unitsSub v (isOpen_sqSub v))
  rw [relIndex_sqSub] at e
  exact_mod_cast e

end UnitIndex

end QuadFormsKB.Tamagawa.Measure.Weil
