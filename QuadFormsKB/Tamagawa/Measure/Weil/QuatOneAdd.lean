/-
# The principal congruence subgroup $1+\pi^m\Lambda_v$ of $\Lambda_v^\times$ and its reduced norms

**Layer:** a number field $F$, a finite place $v$ (dyadic places included), $\Lambda_v = \mathfrak o_v\langle1,i,j,k\rangle\subset
\mathbb H[F_v,a,b]$ for integral $a, b$.

* `QSmall r x`: all four coordinates of $x$ have valuation $\le r$; products with integral quaternions stay small
  (`QSmall.mul_left`, `QSmall.mul_right`).
* **`oneAddCong v a b m`** $= \{u\in\Lambda_v^\times : u - 1\in\pi^m\Lambda_v\}$, a subgroup (`mem_oneAddCong_iff`).
* **`omegaQuatV_oneAddCong`**: $\omega_v(1+\pi^m\Lambda_v) = \mathrm{vol}(\pi^m\mathfrak o_v)^4$ (the norm is a unit there).
* **`nrd_oneAddCong`**: $\operatorname{nrd}(1+\pi^m\Lambda_v)\subseteq 1+\pi^{m+s}\mathfrak o_v$ ($|2|_v = q^{-s}$, $m\ge s$), and
  **`exists_oneAddCong_nrd_eq`**: equality for $m > s$ (square roots, `isSquare_of_valued_sub_one_lt`).
* **`omegaV_oneAddUnits`**: $\omega_v(1+\pi^k\mathfrak o_v) = \mathrm{vol}(\pi^k\mathfrak o_v)$.

Source: Weil 1982, §2.2 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqCount
import QuadFormsKB.Literature.HasseNorm.SquareClasses

open MeasureTheory Measure Set Function NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices

noncomputable section

section Small

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] {A B : K}

/-- All coordinates of $x\in\mathbb H[K,A,B]$ have valuation $\le r$. -/
def QSmall (r : ℤᵐ⁰) (x : ℍ[K,A,0,B]) : Prop :=
  Valued.v x.re ≤ r ∧ Valued.v x.imI ≤ r ∧ Valued.v x.imJ ≤ r ∧ Valued.v x.imK ≤ r

theorem valued_mul_le {r : ℤᵐ⁰} {x y : K} (hx : Valued.v x ≤ r) (hy : Valued.v y ≤ 1) : Valued.v (x * y) ≤ r := by
  rw [map_mul]; calc Valued.v x * Valued.v y ≤ r * 1 := mul_le_mul' hx hy
    _ = r := mul_one r

theorem valued_mul_le' {r : ℤᵐ⁰} {x y : K} (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ r) : Valued.v (x * y) ≤ r := by
  rw [mul_comm]; exact valued_mul_le hy hx

theorem valued_add_le {r : ℤᵐ⁰} {x y : K} (hx : Valued.v x ≤ r) (hy : Valued.v y ≤ r) : Valued.v (x + y) ≤ r :=
  (Valuation.map_add _ _ _).trans (max_le hx hy)

theorem valued_sub_le {r : ℤᵐ⁰} {x y : K} (hx : Valued.v x ≤ r) (hy : Valued.v y ≤ r) : Valued.v (x - y) ≤ r :=
  (Valuation.map_sub _ _ _).trans (max_le hx hy)

theorem valued_neg_le {r : ℤᵐ⁰} {x : K} (hx : Valued.v x ≤ r) : Valued.v (-x) ≤ r := by rwa [Valuation.map_neg]

/-- Leaves $P\cdot y$ with $P\in\{x_i, cx_i, ABx_i\}$. -/
theorem leaf_le {r s : ℤᵐ⁰} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) (hrs : r * s = r) {x y : K}
    (hx : Valued.v x ≤ r) (hy : Valued.v y ≤ s) :
    Valued.v (x * y) ≤ r ∧ Valued.v (A * x * y) ≤ r ∧ Valued.v (B * x * y) ≤ r ∧
      Valued.v (A * B * x * y) ≤ r := by
  have key : ∀ c : K, Valued.v c ≤ 1 → Valued.v (c * x * y) ≤ r := fun c hc => by
    rw [map_mul, map_mul]
    calc Valued.v c * Valued.v x * Valued.v y ≤ 1 * r * s := mul_le_mul' (mul_le_mul' hc hx) hy
      _ = r := by rw [one_mul, hrs]
  have hAB : Valued.v (A * B) ≤ 1 := by rw [map_mul]; exact mul_le_one' hA hB
  refine ⟨?_, key A hA, key B hB, key (A * B) hAB⟩
  have := key 1 (by simp); rwa [one_mul] at this

theorem leaf_le' {r : ℤᵐ⁰} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {x y : K}
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ r) :
    Valued.v (x * y) ≤ r ∧ Valued.v (A * x * y) ≤ r ∧ Valued.v (B * x * y) ≤ r ∧
      Valued.v (A * B * x * y) ≤ r := by
  have key : ∀ c : K, Valued.v c ≤ 1 → Valued.v (c * x * y) ≤ r := fun c hc => by
    rw [map_mul, map_mul]
    calc Valued.v c * Valued.v x * Valued.v y ≤ 1 * 1 * r := mul_le_mul' (mul_le_mul' hc hx) hy
      _ = r := by rw [one_mul, one_mul]
  have hAB : Valued.v (A * B) ≤ 1 := by rw [map_mul]; exact mul_le_one' hA hB
  refine ⟨?_, key A hA, key B hB, key (A * B) hAB⟩
  have := key 1 (by simp); rwa [one_mul] at this

theorem QSmall.mul_right {r : ℤᵐ⁰} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {x y : ℍ[K,A,0,B]}
    (hx : QSmall r x) (hy : QSmall 1 y) : QSmall r (x * y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  obtain ⟨k0, k1, k2, k3⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, zero_mul, mul_zero, add_zero, zero_add, sub_zero] <;>
  repeat (first | apply valued_add_le | apply valued_sub_le | apply valued_neg_le)
  all_goals first
    | exact (leaf_le hA hB (mul_one r) (by assumption) (by assumption)).1
    | exact (leaf_le hA hB (mul_one r) (by assumption) (by assumption)).2.1
    | exact (leaf_le hA hB (mul_one r) (by assumption) (by assumption)).2.2.1
    | exact (leaf_le hA hB (mul_one r) (by assumption) (by assumption)).2.2.2

theorem QSmall.mul_left {r : ℤᵐ⁰} (hA : Valued.v A ≤ 1) (hB : Valued.v B ≤ 1) {x y : ℍ[K,A,0,B]}
    (hx : QSmall 1 x) (hy : QSmall r y) : QSmall r (x * y) := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  obtain ⟨k0, k1, k2, k3⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, zero_mul, mul_zero, add_zero, zero_add, sub_zero] <;>
  repeat (first | apply valued_add_le | apply valued_sub_le | apply valued_neg_le)
  all_goals first
    | exact (leaf_le' hA hB (by assumption) (by assumption)).1
    | exact (leaf_le' hA hB (by assumption) (by assumption)).2.1
    | exact (leaf_le' hA hB (by assumption) (by assumption)).2.2.1
    | exact (leaf_le' hA hB (by assumption) (by assumption)).2.2.2

theorem QSmall.add {r : ℤᵐ⁰} {x y : ℍ[K,A,0,B]} (hx : QSmall r x) (hy : QSmall r y) : QSmall r (x + y) :=
  ⟨valued_add_le hx.1 hy.1, valued_add_le hx.2.1 hy.2.1, valued_add_le hx.2.2.1 hy.2.2.1,
    valued_add_le hx.2.2.2 hy.2.2.2⟩

theorem QSmall.neg {r : ℤᵐ⁰} {x : ℍ[K,A,0,B]} (hx : QSmall r x) : QSmall r (-x) :=
  ⟨valued_neg_le hx.1, valued_neg_le hx.2.1, valued_neg_le hx.2.2.1, valued_neg_le hx.2.2.2⟩

theorem QSmall.mono {r r' : ℤᵐ⁰} (h : r ≤ r') {x : ℍ[K,A,0,B]} (hx : QSmall r x) : QSmall r' x :=
  ⟨hx.1.trans h, hx.2.1.trans h, hx.2.2.1.trans h, hx.2.2.2.trans h⟩

theorem qSmall_one : QSmall (1 : ℤᵐ⁰) (1 : ℍ[K,A,0,B]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

end Small

section OneAdd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (a b : 𝓞 F)

local notation "Fv" => v.adicCompletion F

theorem qSmall_one_iff_mem_lamLoc (x : QuatV (a : F) (b : F) v) :
    QSmall (1 : ℤᵐ⁰) x ↔ x ∈ lamLoc (a : F) (b : F) v := by
  simp only [QSmall, lamLoc, mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem valuedA : Valued.v (algebraMap F Fv (a : F)) ≤ 1 := valued_algebraMap_le_one a v
theorem valuedB : Valued.v (algebraMap F Fv (b : F)) ≤ 1 := valued_algebraMap_le_one b v

/-- **$1+\pi^m\Lambda_v$** as a subgroup of $(D\otimes F_v)^\times$ ($m\ge1$). -/
def oneAddCong (m : ℕ) : Subgroup (QuatV (a : F) (b : F) v)ˣ where
  carrier := {u | u ∈ lamLocUnits (a : F) (b : F) v ∧
    QSmall (exp (-(m : ℤ))) ((u : QuatV (a : F) (b : F) v) - 1)}
  one_mem' := ⟨one_mem_lamLocUnits _ _ v, by simp only [Units.val_one, sub_self]; refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩
  mul_mem' {x y} hx hy := by
    refine ⟨lamLocUnits_mul_mem (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w) hx.1 hy.1, ?_⟩
    rw [Units.val_mul, show (x : QuatV (a : F) (b : F) v) * y - 1 =
      ((x : QuatV (a : F) (b : F) v) - 1) * y + ((y : QuatV (a : F) (b : F) v) - 1) by noncomm_ring]
    exact (hx.2.mul_right (valuedA v a) (valuedB v b) ((qSmall_one_iff_mem_lamLoc v a b _).2 hy.1.1)).add hy.2
  inv_mem' {x} hx := by
    refine ⟨⟨hx.1.2, by rw [inv_inv]; exact hx.1.1⟩, ?_⟩
    rw [show ((x⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) - 1 =
      -(((x⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) * ((x : QuatV (a : F) (b : F) v) - 1)) by
        rw [mul_sub, Units.inv_mul, mul_one, neg_sub]]
    exact (QSmall.mul_left (valuedA v a) (valuedB v b) ((qSmall_one_iff_mem_lamLoc v a b _).2 hx.1.2) hx.2).neg

theorem mem_oneAddCong {m : ℕ} {u : (QuatV (a : F) (b : F) v)ˣ} :
    u ∈ oneAddCong v a b m ↔ u ∈ lamLocUnits (a : F) (b : F) v ∧
      QSmall (exp (-(m : ℤ))) ((u : QuatV (a : F) (b : F) v) - 1) := Iff.rfl

theorem oneAddCong_le_lamLoc (m : ℕ) : oneAddCong v a b m ≤ lamLocUnitsSub v a b := fun _ hu => hu.1

theorem valued_lt_one_of_le_exp {m : ℕ} (hm : 1 ≤ m) {x : Fv} (h : Valued.v x ≤ exp (-(m : ℤ))) :
    Valued.v x < 1 :=
  lt_of_le_of_lt h (by rw [← exp_zero, exp_lt_exp]; omega)

theorem valued_eq_one_of_sub_one_lt {x : Fv} (h : Valued.v (x - 1) < 1) : Valued.v x = 1 := by
  have h1 : x = (x - 1) + 1 := by ring
  rw [h1, Valuation.map_add_eq_of_lt_right]
  · exact map_one _
  · rwa [map_one]

/-- On $1+\pi^m\Lambda_v$ ($m\ge1$) the reduced norm is a unit. -/
theorem valued_nrdLoc_eq_one {m : ℕ} (hm : 1 ≤ m) {x : QuatV (a : F) (b : F) v}
    (hx : QSmall (exp (-(m : ℤ))) (x - 1)) : Valued.v (nrdLoc _ _ x) = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  simp only [QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
    QuaternionAlgebra.imK_one, sub_zero] at h0 h1 h2 h3
  have hx0 : Valued.v x.re = 1 := valued_eq_one_of_sub_one_lt v (valued_lt_one_of_le_exp v hm h0)
  have hA := valuedA v a
  have hB := valuedB v b
  have hsmall : ∀ y : Fv, Valued.v y ≤ exp (-(m : ℤ)) → ∀ c : Fv, Valued.v c ≤ 1 → Valued.v (c * y ^ 2) < 1 :=
    fun y hy c hc => by
      rw [map_mul, map_pow]
      calc Valued.v c * Valued.v y ^ 2 ≤ 1 * Valued.v y ^ 2 := mul_le_mul' hc le_rfl
        _ = Valued.v y ^ 2 := one_mul _
        _ < 1 := pow_lt_one₀ zero_le' (valued_lt_one_of_le_exp v hm hy) two_ne_zero
  have hnrd : nrdLoc _ _ x = x.re ^ 2 + (-(algebraMap F Fv (a : F)) * x.imI ^ 2 +
      (-(algebraMap F Fv (b : F)) * x.imJ ^ 2 + (algebraMap F Fv (a : F) * algebraMap F Fv (b : F)) * x.imK ^ 2)) := by
    have hc : quatLocCoord _ _ x = ![x.re, x.imI, x.imJ, x.imK] := by ext i; fin_cases i <;> rfl
    rw [nrdLoc_eq_nrdForm, hc, nrdForm]; simp; ring
  have hrest : Valued.v (-(algebraMap F Fv (a : F)) * x.imI ^ 2 +
      (-(algebraMap F Fv (b : F)) * x.imJ ^ 2 + (algebraMap F Fv (a : F) * algebraMap F Fv (b : F)) * x.imK ^ 2)) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hsmall _ h1 _ (by rwa [Valuation.map_neg]))
      (lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hsmall _ h2 _ (by rwa [Valuation.map_neg]))
        (hsmall _ h3 _ (by rw [map_mul]; exact mul_le_one' hA hB)))))
  rw [hnrd, Valuation.map_add_eq_of_lt_left, map_pow, hx0, one_pow]
  rwa [map_pow, hx0, one_pow]

/-- $u\in1+\pi^m\Lambda_v$ iff $u - 1\in\pi^m\Lambda_v$ ($m\ge1$; integrality of $u^{\pm1}$ is then automatic). -/
theorem mem_oneAddCong_iff {m : ℕ} (hm : 1 ≤ m) {u : (QuatV (a : F) (b : F) v)ˣ} :
    u ∈ oneAddCong v a b m ↔ QSmall (exp (-(m : ℤ))) ((u : QuatV (a : F) (b : F) v) - 1) := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [mem_lamLocUnits_iff (fun w => valued_algebraMap_le_one a w) (fun w => valued_algebraMap_le_one b w),
    ← qSmall_one_iff_mem_lamLoc]
  refine ⟨?_, valued_nrdLoc_eq_one v a b hm h⟩
  have h1 : (u : QuatV (a : F) (b : F) v) = ((u : QuatV (a : F) (b : F) v) - 1) + 1 := by abel
  rw [h1]
  exact (h.mono (by rw [← exp_zero, exp_le_exp]; omega)).add qSmall_one

/-- **$\omega_v(1+\pi^m\Lambda_v) = \mathrm{vol}(\pi^m\mathfrak o_v)^4$** ($m\ge1$). -/
theorem omegaQuatV_oneAddCong {m : ℕ} (hm : 1 ≤ m) :
    omegaQuatV v (a : F) (b : F) (oneAddCong v a b m) =
      Analysis.selfDualV v (Analysis.latticeV v (m : ℤ)) ^ 4 := by
  set L : Set Fv := (Analysis.latticeV v (m : ℤ) : Set Fv)
  set L1 : Set Fv := (fun x => x - 1) ⁻¹' L
  have hLm : MeasurableSet L := Analysis.measurableSet_latticeV v m
  have hL1m : MeasurableSet L1 := hLm.preimage (measurable_id.sub_const 1)
  set T : Set (Fin 4 → Fv) := Set.univ.pi ![L1, L, L, L]
  have hT : ∀ x : QuatV (a : F) (b : F) v, quatLocCoord _ _ x ∈ T ↔ QSmall (exp (-(m : ℤ))) (x - 1) := by
    intro x
    simp only [T, Set.mem_univ_pi, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true]
    simp [QuaternionAlgebra.linearEquivTuple, QSmall, L1, L, Analysis.mem_latticeV]
    tauto
  have hset : (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ) =
      Units.val ⁻¹' (quatLocCoord _ _ ⁻¹' T) := by
    ext u; simp only [SetLike.mem_coe, Set.mem_preimage, hT, mem_oneAddCong_iff v a b hm]
  have hTm : MeasurableSet T := MeasurableSet.univ_pi fun i => by
    fin_cases i
    · exact hL1m
    · exact hLm
    · exact hLm
    · exact hLm
  have hOm : MeasurableSet (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ) := by
    rw [hset]
    exact (hTm.preimage (continuous_quatLocCoord _ _).measurable).preimage Units.continuous_val.measurable
  have h1 : ∀ u ∈ (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ),
      distribHaarChar (QuatV (a : F) (b : F) v) u = 1 := by
    intro u hu
    have hu' : nrdLocUnit _ _ u ∈ unitsVSub v := valued_nrdLoc_eq_one v a b hm hu.2
    rw [distribHaarChar_quatLoc, distribHaarChar_eq_one_of_mem_unitsVSub hu', one_pow]
  rw [omegaQuatV, omegaQuatLoc, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_quatLoc _ _)
    (continuous_distribHaarChar_quatLoc _ _ (continuous_distribHaarChar_adic v)) _ hOm h1]
  have himg : Units.val '' (oneAddCong v a b m : Set (QuatV (a : F) (b : F) v)ˣ) = quatLocCoord _ _ ⁻¹' T := by
    rw [hset]
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hx
      have hn : nrdLoc _ _ x ≠ 0 := by
        intro h0
        have := valued_nrdLoc_eq_one v a b hm ((hT x).1 hx)
        rw [h0, map_zero] at this; exact zero_ne_one this
      obtain ⟨u, rfl⟩ := (isUnit_iff_nrdLoc_ne_zero _ _ x).mpr hn
      exact ⟨u, hx, rfl⟩
  rw [himg, quatLocVol, Measure.map_apply (quatLocCLE _ _).symm.continuous.measurable
    (hTm.preimage (continuous_quatLocCoord _ _).measurable)]
  have hpre : (quatLocCLE _ _).symm ⁻¹' (quatLocCoord (algebraMap F Fv (a : F)) (algebraMap F Fv (b : F)) ⁻¹' T) =
      T := by
    ext c
    simp only [Set.mem_preimage]
    change (quatLocCoord _ _) ((quatLocCoord _ _).symm c) ∈ T ↔ c ∈ T
    rw [LinearEquiv.apply_symm_apply]
  have hL1 : Analysis.selfDualV v L1 = Analysis.selfDualV v L := by
    rw [show L1 = (fun x => (-1 : Fv) + x) ⁻¹' L by ext x; simp [L1, neg_add_eq_sub],
      measure_preimage_add]
  rw [hpre, Measure.pi_pi, Fin.prod_univ_four]
  simp [hL1, Matrix.vecHead, Matrix.vecTail]
  ring

/-! ### Reduced norms of $1+\pi^m\Lambda_v$ -/

theorem nrdLoc_one_add (y : QuatV (a : F) (b : F) v) :
    nrdLoc _ _ (1 + y) = 1 + 2 * y.re + nrdLoc _ _ y := by
  have hc : ∀ z : QuatV (a : F) (b : F) v, quatLocCoord _ _ z = ![z.re, z.imI, z.imJ, z.imK] := fun z => by
    ext i; fin_cases i <;> rfl
  rw [nrdLoc_eq_nrdForm, nrdLoc_eq_nrdForm, hc, hc, nrdForm, nrdForm]
  simp; ring

theorem valued_nrdLoc_le {r : ℤᵐ⁰} {y : QuatV (a : F) (b : F) v} (hy : QSmall r y) (hr : r ≤ 1) :
    Valued.v (nrdLoc _ _ y) ≤ r ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := hy
  have hc : quatLocCoord _ _ y = ![y.re, y.imI, y.imJ, y.imK] := by ext i; fin_cases i <;> rfl
  rw [nrdLoc_eq_nrdForm, hc, nrdForm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons]
  have hA := valuedA v a
  have hB := valuedB v b
  have hsq : ∀ z : Fv, Valued.v z ≤ r → ∀ c : Fv, Valued.v c ≤ 1 → Valued.v (c * z ^ 2) ≤ r ^ 2 := fun z hz c hc => by
    rw [map_mul, map_pow]
    calc Valued.v c * Valued.v z ^ 2 ≤ 1 * r ^ 2 := mul_le_mul' hc (pow_le_pow_left₀ zero_le' hz 2)
      _ = r ^ 2 := one_mul _
  refine valued_add_le (valued_sub_le (valued_sub_le ?_ (hsq _ h1 _ hA)) (hsq _ h2 _ hB))
    (hsq _ h3 _ (by rw [map_mul]; exact mul_le_one' hA hB))
  have := hsq _ h0 1 (by simp); rwa [one_mul] at this

/-- **$\operatorname{nrd}(1+\pi^m\Lambda_v)\subseteq1+\pi^{m+s}\mathfrak o_v$** for $|2|_v = q^{-s}$, $s\le m$. -/
theorem valued_nrdLoc_sub_one_le {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s ≤ m)
    {u : (QuatV (a : F) (b : F) v)ˣ} (hu : u ∈ oneAddCong v a b m) :
    Valued.v (nrdLoc _ _ (u : QuatV (a : F) (b : F) v) - 1) ≤ exp (-((m + s : ℕ) : ℤ)) := by
  set y : QuatV (a : F) (b : F) v := (u : QuatV (a : F) (b : F) v) - 1
  have hy : QSmall (exp (-(m : ℤ))) y := hu.2
  have hu' : (u : QuatV (a : F) (b : F) v) = 1 + y := by simp [y]
  rw [hu', nrdLoc_one_add, show 1 + 2 * y.re + nrdLoc _ _ y - 1 = 2 * y.re + nrdLoc _ _ y by ring]
  refine valued_add_le ?_ ?_
  · rw [map_mul, hs, show ((m + s : ℕ) : ℤ) = s + m by push_cast; ring, neg_add, exp_add]
    exact mul_le_mul' le_rfl hy.1
  · refine (valued_nrdLoc_le v a b hy (by rw [← exp_zero, exp_le_exp]; omega)).trans ?_
    rw [← exp_nsmul, exp_le_exp, nsmul_eq_mul]; push_cast; omega

/-- **Square roots near $1$**: for $m > s$ and $|t - 1|\le q^{-(m+s)}$ there is $r$ with $r^2 = t$ and $|r-1|\le q^{-m}$. -/
theorem exists_sq_eq_near_one {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) {t : Fv}
    (ht : Valued.v (t - 1) ≤ exp (-((m + s : ℕ) : ℤ))) :
    ∃ r : Fv, r ^ 2 = t ∧ Valued.v (r - 1) ≤ exp (-(m : ℤ)) := by
  have h4 : Valued.v (4 : Fv) = exp (-((2 * s : ℕ) : ℤ)) := by
    rw [show (4 : Fv) = 2 * 2 by norm_num, map_mul, hs, ← exp_add]; push_cast; ring_nf
  obtain ⟨r, hr⟩ := QuadFormsKB.HN.isSquare_of_valued_sub_one_lt v t (by
    rw [h4]; exact lt_of_le_of_lt ht (by rw [exp_lt_exp]; push_cast; omega))
  -- `(r - 1)(r + 1) = t - 1`
  have hprod : (r - 1) * (r + 1) = t - 1 := by rw [hr]; ring
  have hdiff : (r + 1) - (r - 1) = 2 := by ring
  by_cases h : Valued.v (r - 1) < exp (-(s : ℤ))
  · -- then `|r + 1| = |2|`
    have hp1 : Valued.v (r + 1) = exp (-(s : ℤ)) := by
      rw [show r + 1 = 2 + (r - 1) by ring, Valuation.map_add_eq_of_lt_left, hs]
      rwa [hs]
    refine ⟨r, by rw [hr]; ring, ?_⟩
    have := congrArg Valued.v hprod
    rw [map_mul, hp1] at this
    have h2 : Valued.v (r - 1) * exp (-(s : ℤ)) ≤ exp (-(m : ℤ)) * exp (-(s : ℤ)) := by
      rw [this, ← exp_add]; refine ht.trans (le_of_eq ?_); congr 1; push_cast; ring
    exact (mul_le_mul_iff_left₀ exp_pos).1 h2
  · -- otherwise `|r + 1| ≤ q^{-m}`: use `-r`
    rw [not_lt] at h
    have hm1 : Valued.v (r + 1) * exp (-(s : ℤ)) ≤ exp (-(m : ℤ)) * exp (-(s : ℤ)) := by
      calc Valued.v (r + 1) * exp (-(s : ℤ)) ≤ Valued.v (r + 1) * Valued.v (r - 1) := mul_le_mul' le_rfl h
        _ = Valued.v (t - 1) := by rw [← map_mul, mul_comm, hprod]
        _ ≤ exp (-((m + s : ℕ) : ℤ)) := ht
        _ = exp (-(m : ℤ)) * exp (-(s : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
    refine ⟨-r, by rw [neg_sq, hr]; ring, ?_⟩
    rw [show -r - 1 = -(r + 1) by ring, Valuation.map_neg]
    exact (mul_le_mul_iff_left₀ exp_pos).1 hm1

end OneAdd

end

end QuadFormsKB.Tamagawa.Measure.Weil
