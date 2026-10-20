/-
# The scalars, $[T : T\cap Z_N] = 2^{g-1}[N_v : \mathcal O_v^{\times2}]$

**Layer:** as in `GnatNSWinIndex`: a number field $F$, $K = F(\delta)$, a finite place $v$ with $g$ places $w\mid v$ of $K$,
$T\le Y^{(M)}$ the scalars ($t\in E^\times$, a unit at every $w\mid v$, $t^2\in F_v$), $T_0 = T\cap Z_N = T\cap F_v^\times$.

* **`card_sqOne`**: $\#\{z\in E : z^2 = 1\} = 2^g$ ($E\cong\prod_{w\mid v}K_w$).
* **`sqT`**: $T\to F_v^\times$, $t\mapsto t^2$, with range $N_v = \{c : \varphi_w(c)\in\mathcal O_w^{\times2}\ \forall w\mid v\}$
  (`NvSub`, square roots glue), image of $T_0$ equal to $\mathcal O_v^{\times2}$ (`sqSub`) and kernel $\mu_2(E)$.
* **`relIndex_TY`**: $[T : T\cap Z_N]\cdot2 = [N_v : \mathcal O_v^{\times2}]\cdot2^g$.

The naive count $[T:\mathcal O_v^\times] = [N_v:\mathcal O_v^{\times2}]$ misses the factor $2^{g-1}$ at the split places
($t = (1,-1)$); it cancels against $\prod_{w\mid v}[\mathcal O_w^\times:\mathcal O_w^{\times2}]$ in the final identity.

Source: Weil 1982, §2.2-2.3 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSWinIndex

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section SqOne

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

theorem card_sqOne_field {L : Type*} [Field L] [CharZero L] : Nat.card {x : L // x ^ 2 = 1} = 2 := by
  classical
  have e : {x : L // x ^ 2 = 1} ≃ Fin 2 :=
    { toFun := fun x => if (x : L) = 1 then 0 else 1
      invFun := fun i => if i = 0 then ⟨1, one_pow 2⟩ else ⟨-1, by ring⟩
      left_inv := fun x => by
        have hx := x.2
        have : (x : L) = 1 ∨ (x : L) = -1 := by
          have : ((x : L) - 1) * ((x : L) + 1) = 0 := by linear_combination hx
          rcases mul_eq_zero.1 this with h | h
          · left; linear_combination h
          · right; linear_combination h
        rcases this with h | h
        · simp [h]; exact Subtype.ext h.symm
        · have hne : (-1 : L) ≠ 1 := by
            intro h1; have : (2 : L) = 0 := by linear_combination -h1
            exact two_ne_zero this
          simp only [h, hne, ite_false]
          exact Subtype.ext h.symm
      right_inv := fun i => by
        fin_cases i
        · simp
        · have hne : (-1 : L) ≠ 1 := by
            intro h1; have : (2 : L) = 0 := by linear_combination -h1
            exact two_ne_zero this
          simp [hne] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

include hb₀ hb₁ in
/-- **$\#\mu_2(E) = 2^g$.** -/
theorem card_sqOne : Nat.card {z : E // z ^ 2 = 1} = 2 ^ Fintype.card (PlaceSet (K := K) v) := by
  classical
  have hglue := fun (t : PlaceProd (K := K) v) => exists_qlh_eq hb₀ hb₁ t
  let e : {z : E // z ^ 2 = 1} ≃ ∀ w : PlaceSet (K := K) v, {x : w.1.adicCompletion K // x ^ 2 = 1} :=
    { toFun := fun z w => ⟨qlh hb₁ v w z, by rw [← map_pow, z.2, map_one]⟩
      invFun := fun f => ⟨(hglue fun w => (f w : w.1.adicCompletion K)).choose, by
        apply qlh_injective hb₀ hb₁; intro w
        rw [map_pow, (hglue fun w => (f w : w.1.adicCompletion K)).choose_spec w, map_one]; exact (f w).2⟩
      left_inv := fun z => Subtype.ext (qlh_injective hb₀ hb₁ fun w =>
        (hglue fun w => qlh hb₁ v w (z : E)).choose_spec w)
      right_inv := fun f => funext fun w => Subtype.ext ((hglue fun w => (f w : w.1.adicCompletion K)).choose_spec w) }
  rw [Nat.card_congr e, Nat.card_pi]
  simp only [card_sqOne_field, Finset.prod_const, Finset.card_univ]

end SqOne

end QuadFormsKB.Tamagawa.Measure.Weil

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat LerayPadic

section Scalars

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F))
  (M : HeightOneSpectrum (𝓞 K) → ℕ) (hM1 : ∀ w, 1 ≤ M w)

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

variable (F) in
/-- $\mathcal O_v^{\times2}$ as a subgroup of $F_v^\times$. -/
def sqSub : Subgroup Fvˣ where
  carrier := sqUnits F v
  mul_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨r', hr', rfl⟩
    exact ⟨r * r', by rw [Units.val_mul, map_mul, hr, hr', one_mul], by rw [mul_pow]⟩
  one_mem' := ⟨1, by simp, by simp⟩
  inv_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r⁻¹, by rw [Units.val_inv_eq_inv_val, map_inv₀, hr, inv_one], by rw [inv_pow]⟩

variable (K) in
/-- **$N_v = \{c\in F_v^\times : \varphi_w(c)\in\mathcal O_w^{\times2}\ \forall w\mid v\}$** as a subgroup. -/
def NvSub : Subgroup Fvˣ where
  carrier := {c | ∀ w : PlaceSet (K := K) v, ∃ u : w.1.adicCompletion K, Valued.v u = 1 ∧
    localRingHom v w.1 w.2 (c : Fv) = u ^ 2}
  mul_mem' {c c'} hc hc' w := by
    obtain ⟨u, hu, hcu⟩ := hc w
    obtain ⟨u', hu', hcu'⟩ := hc' w
    exact ⟨u * u', by rw [map_mul, hu, hu', one_mul], by rw [Units.val_mul, map_mul, hcu, hcu', mul_pow]⟩
  one_mem' w := ⟨1, by simp, by simp⟩
  inv_mem' {c} hc w := by
    obtain ⟨u, hu, hcu⟩ := hc w
    exact ⟨u⁻¹, by rw [map_inv₀, hu, inv_one], by rw [Units.val_inv_eq_inv_val, map_inv₀, hcu, inv_pow]⟩

variable {v M hM1} {c₀ n N : ℕ}

theorem eq_coe_re_of_mem_TY {t : nsLocSub hb₁ hα hβ v M hM1} (ht : t ∈ TY hb₁ hα hβ v M hM1) :
    yv (t : GnK Fv a b d) = ((yv (t : GnK Fv a b d)).re : DEr Fv a b d) := by
  have ht' : imvE (yv (t : GnK Fv a b d)) = 0 := ht
  conv_lhs => rw [eq_re_add_pureE (yv (t : GnK Fv a b d)), ht']
  have : (pureE (0 : Fin 3 → E) : DEr Fv a b d) = 0 := by ext <;> rfl
  rw [this, add_zero]

/-- **$t\mapsto t^2$**, $T\to F_v^\times$ (the reduced norm). -/
def sqT : TY hb₁ hα hβ v M hM1 →* Fvˣ where
  toFun t := Units.mk0 (nrdK (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)))
    (nrdK_ne_zero ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d).2)
  map_one' := by
    apply Units.ext
    change nrdK (1 : DEr Fv a b d) = 1
    simp [nrdK, nrdE]; rfl
  map_mul' t t' := by
    apply Units.ext
    change nrdK ((((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d) : DEK Fv a b d) *
      (((t' : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d) : DEK Fv a b d) : DEr Fv a b d) = _
    rw [← Units.val_mul, nrdK_mul ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d).2]
    rfl

theorem algebraMap_sqT (t : TY hb₁ hα hβ v M hM1) :
    algebraMap Fv E (sqT hb₁ hα hβ t : Fv) =
      (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re ^ 2 := by
  change algebraMap Fv E (nrdK (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d))) = _
  rw [← nrdE_eq_nrdK ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d).2]
  change nrdE (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)) = _
  nth_rewrite 1 [eq_coe_re_of_mem_TY hb₁ hα hβ t.2]
  rw [nrdE_coe]

include hb₀ in
/-- **Scalars of $Y^{(M)}$**: a unit $z$ of $E$ at every $w\mid v$ with $z^2\in F_v$ is the real part of an element of $T$. -/
theorem exists_mem_TY (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {z : E}
    (hz : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) = 1) {c : Fv} (hc : z ^ 2 = algebraMap Fv E c) :
    ∃ t : nsLocSub hb₁ hα hβ v M hM1, t ∈ TY hb₁ hα hβ v M hM1 ∧ (yv (t : GnK Fv a b d)).re = z := by
  have hzu : IsUnit z := isUnit_of_qlh_ne_zero hb₀ hb₁ fun w h0 => by
    have := hz w; rw [h0, map_zero] at this; exact zero_ne_one this
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc
    exact (hzu.pow 2).ne_zero hc
  have hn : nrdE (z : DEr Fv a b d) = algebraMap Fv E c := by rw [nrdE_coe, hc]
  set y : GnK Fv a b d := ⟨QuadFormsKB.Quat.Gnat.unitOfNrd (z : DEr Fv a b d) c hc0 hn,
    QuadFormsKB.Quat.Gnat.unitOfNrd_mem _ _ hc0 hn⟩
  have hyv : yv y = (z : DEr Fv a b d) := rfl
  have him : imvE (yv y) = 0 := by rw [hyv]; funext l; fin_cases l <;> rfl
  have hyY : y ∈ nsLocSub hb₁ hα hβ v M hM1 := by
    refine (mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep y).2 fun w => ⟨by rw [hyv]; exact hz w, ?_⟩
    rw [him]
    convert latP_zero (u := w.1) (m := M w.1) using 1
    funext l; exact map_zero _
  exact ⟨⟨y, hyY⟩, him, by rw [hyv]; rfl⟩

include hb₀ in
/-- **The range of $t\mapsto t^2$ is $N_v$.** -/
theorem range_sqT (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) :
    (sqT hb₁ hα hβ (v := v) (M := M) (hM1 := hM1)).range = NvSub K v := by
  ext c
  constructor
  · rintro ⟨t, rfl⟩ w
    have hval := ((mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hMdeep _).1 (t : nsLocSub hb₁ hα hβ v M hM1).2 w).1
    refine ⟨qlh hb₁ v w (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re, hval, ?_⟩
    rw [← qlh_algebraMap hb₁ w, algebraMap_sqT, map_pow]
  · intro hc
    choose u hu hcu using hc
    obtain ⟨z, hz⟩ := exists_qlh_eq hb₀ hb₁ u
    have hz2 : z ^ 2 = algebraMap Fv E (c : Fv) := qlh_injective hb₀ hb₁ fun w => by
      rw [map_pow, hz w, qlh_algebraMap, hcu w]
    obtain ⟨t, htT, htz⟩ := exists_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 (hM1 := hM1) hMdeep
      (fun w => by rw [hz w]; exact hu w) hz2
    refine ⟨⟨t, htT⟩, Units.ext (FaithfulSMul.algebraMap_injective Fv E ?_)⟩
    rw [algebraMap_sqT]; change (yv (t : GnK Fv a b d)).re ^ 2 = _; rw [htz, hz2]

theorem re_mul_im_eq_zero_of_mem_TY {t : nsLocSub hb₁ hα hβ v M hM1} (ht : t ∈ TY hb₁ hα hβ v M hM1) :
    (yv (t : GnK Fv a b d)).re.re * (yv (t : GnK Fv a b d)).re.im = 0 := by
  have h1 : (nrdE (yv (t : GnK Fv a b d))).im = 0 := (t : GnK Fv a b d).2
  rw [eq_coe_re_of_mem_TY hb₁ hα hβ ht, nrdE_coe, pow_two, QuadraticAlgebra.im_mul] at h1
  have : (2 : Fv) * ((yv (t : GnK Fv a b d)).re.re * (yv (t : GnK Fv a b d)).re.im) = 0 := by
    linear_combination h1
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

include hb₀ in
/-- **$T\cap Z_N = T\cap F_v^\times$**: a scalar $t\in T$ has $\varphi_t = \pm1$, with $+1$ iff $t\in F_v$. -/
theorem mem_ZN_iff_of_mem_TY (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) {t : nsLocSub hb₁ hα hβ v M hM1}
    (ht : t ∈ TY hb₁ hα hβ v M hM1) :
    t ∈ ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW) ↔
      (yv (t : GnK Fv a b d)).re.im = 0 := by
  set r := (yv (t : GnK Fv a b d)).re
  have hyt := eq_coe_re_of_mem_TY hb₁ hα hβ ht
  have hr2 : (r ^ 2).im = 0 := by
    have h1 : (nrdE (yv (t : GnK Fv a b d))).im = 0 := (t : GnK Fv a b d).2
    rwa [hyt, nrdE_coe] at h1
  have hphi : phiLin (yv (t : GnK Fv a b d)) = ((r ^ 2).re⁻¹ * QuadraticAlgebra.norm r) • LinearMap.id := by
    rw [hyt, show ((r : DEr Fv a b d)) = (r : DEr Fv a b d) * 1 from (mul_one _).symm, phiLin_coe_mul r 1 hr2,
      phiLin_one]
  have hru : IsUnit r := isUnit_re_of_mem hb₀ hb₁ hα hβ hα0 hβ0 hW.deep t.2
  rw [mem_ZN_iff, mem_congSub, toMatrix_nsSOK, hphi, map_smul, LinearMap.toMatrix'_id]
  have hcase := re_mul_im_eq_zero_of_mem_TY hb₁ hα hβ ht
  rcases mul_eq_zero.1 hcase with h0 | h0
  · -- `r = im(r) δ`: `φ_t = -1`
    have him : r.im ≠ 0 := by
      intro h1; apply hru.ne_zero; exact QuadraticAlgebra.ext h0 h1
    have hf : (r ^ 2).re⁻¹ * QuadraticAlgebra.norm r = -1 := by
      have e1 : (r ^ 2).re = algebraMap F Fv (d : F) * r.im ^ 2 := by
        rw [pow_two, QuadraticAlgebra.re_mul, h0]; ring
      have e2 : QuadraticAlgebra.norm r = -(algebraMap F Fv (d : F) * r.im ^ 2) := by
        rw [QuadraticAlgebra.norm_def, h0]; ring
      rw [e1, e2, mul_neg, inv_mul_cancel₀ (mul_ne_zero ((map_ne_zero _).2 hd0) (pow_ne_zero _ him))]
    rw [hf]
    refine ⟨fun hb => ?_, fun h1 => absurd h1 him⟩
    exfalso
    have := hb 0 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    rw [show (-1 : Fv) - 1 = -2 by ring, Valuation.map_neg, valued_two_eq v, exp_le_exp] at this
    have := hW.Ns; omega
  · -- `r ∈ F_v`: `φ_t = 1`
    have hf : (r ^ 2).re⁻¹ * QuadraticAlgebra.norm r = 1 := by
      have hre : r.re ≠ 0 := by
        intro h1; apply hru.ne_zero; exact QuadraticAlgebra.ext h1 h0
      have e1 : (r ^ 2).re = r.re ^ 2 := by rw [pow_two, QuadraticAlgebra.re_mul, h0]; ring
      have e2 : QuadraticAlgebra.norm r = r.re ^ 2 := by rw [QuadraticAlgebra.norm_def, h0]; ring
      rw [e1, e2, inv_mul_cancel₀ (pow_ne_zero _ hre)]
    rw [hf, one_smul]
    exact ⟨fun _ => h0, fun _ => one_mem_ballOne v N⟩

theorem yv_injective_TY {t t' : nsLocSub hb₁ hα hβ v M hM1} (ht : t ∈ TY hb₁ hα hβ v M hM1)
    (ht' : t' ∈ TY hb₁ hα hβ v M hM1) (h : (yv (t : GnK Fv a b d)).re = (yv (t' : GnK Fv a b d)).re) : t = t' := by
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  change yv (t : GnK Fv a b d) = yv (t' : GnK Fv a b d)
  rw [eq_coe_re_of_mem_TY hb₁ hα hβ ht, eq_coe_re_of_mem_TY hb₁ hα hβ ht', h]

theorem sqT_eq_one_iff (t : TY hb₁ hα hβ v M hM1) :
    sqT hb₁ hα hβ t = 1 ↔ (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re ^ 2 = 1 := by
  rw [← algebraMap_sqT]
  constructor
  · intro h; rw [h, Units.val_one, map_one]
  · intro h; apply Units.ext; apply FaithfulSMul.algebraMap_injective Fv E; rw [h, Units.val_one, map_one]

include hb₀ in
theorem valued_qlh_of_sq_eq_one {z : E} (hz : z ^ 2 = 1) (w : PlaceSet (K := K) v) :
    Valued.v (qlh hb₁ v w z) = 1 := by
  have h1 : Valued.v (qlh hb₁ v w z) ^ 2 = 1 := by rw [← map_pow, ← map_pow, hz, map_one, map_one]
  have h0 : qlh hb₁ v w z ≠ 0 := by intro h; rw [h, map_zero] at h1; norm_num at h1
  obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp w.1 h0
  rw [hk, ← exp_nsmul, ← exp_zero, exp_inj] at h1; rw [hk, ← exp_zero, exp_inj]; simp at h1; omega

set_option maxHeartbeats 1000000 in
include hb₀ in
/-- **$\#\ker(t\mapsto t^2) = 2^g$.** -/
theorem card_ker_sqT (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) :
    Nat.card (sqT hb₁ hα hβ (v := v) (M := M) (hM1 := hM1)).ker = 2 ^ Fintype.card (PlaceSet (K := K) v) := by
  rw [← card_sqOne hb₀ hb₁ v]
  refine Nat.card_congr (Equiv.ofBijective (fun t => ⟨(yv (((t : TY hb₁ hα hβ v M hM1) :
    nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re, (sqT_eq_one_iff hb₁ hα hβ _).1 t.2⟩) ⟨?_, ?_⟩)
  · intro t t' h
    exact Subtype.ext (Subtype.ext (yv_injective_TY hb₁ hα hβ (t : TY hb₁ hα hβ v M hM1).2
      (t' : TY hb₁ hα hβ v M hM1).2 (congrArg Subtype.val h)))
  · rintro ⟨z, hz⟩
    have hzw : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) = 1 := valued_qlh_of_sq_eq_one hb₀ hb₁ hz
    have hz1 : z ^ 2 = algebraMap Fv E 1 := by rw [hz, map_one]
    obtain ⟨t, htT, htz⟩ := exists_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 (v := v) (M := M) (hM1 := hM1) hMdeep
      (z := z) hzw (c := 1) hz1
    exact ⟨⟨⟨t, htT⟩, (sqT_eq_one_iff hb₁ hα hβ _).2 (by change (yv (t : GnK Fv a b d)).re ^ 2 = 1; rw [htz, hz])⟩,
      Subtype.ext htz⟩

include hb₀ in
theorem valued_eq_one_of_qlh (hMdeep : ∀ w, nsLevK hα0 hβ0 w ≤ M w) {x : Fv}
    (hx : ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w (algebraMap Fv E x)) = 1) : Valued.v x = 1 := by
  obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v (K := K)
  have := hx ⟨w, hw⟩
  rw [qlh_algebraMap] at this
  exact (valued_localRingHom_eq_one_iff w hw x).1 this

theorem qlh_algebraMap_of_valued {x : Fv} (hx : Valued.v x = 1) (w : PlaceSet (K := K) v) :
    Valued.v (qlh hb₁ v w (algebraMap Fv E x)) = 1 := by
  rw [qlh_algebraMap]; exact (valued_localRingHom_eq_one_iff w.1 w.2 x).2 hx

set_option maxHeartbeats 1000000 in
include hb₀ in
/-- **The image of $T\cap Z_N$ under $t\mapsto t^2$ is $\mathcal O_v^{\times2}$.** -/
theorem map_sqT_H₀ (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    ((ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).subgroupOf
      (TY hb₁ hα hβ v M hM1)).map (sqT hb₁ hα hβ) = sqSub F v := by
  ext c
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_ZN_iff_of_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW t.2] at ht
    set r := (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re
    have hr : r = algebraMap Fv E r.re := QuadraticAlgebra.ext rfl ht
    have hval := fun w => ((mem_nsLocSub_iff hb₁ hα hβ hα0 hβ0 v M hM1 hW.deep _).1
      (t : nsLocSub hb₁ hα hβ v M hM1).2 w).1
    have hr1 : Valued.v r.re = 1 := valued_eq_one_of_qlh hb₀ hb₁ hα0 hβ0 (M := M) hW.deep
      (fun w => by rw [← hr]; exact hval w)
    have hr0 : r.re ≠ 0 := by intro h; rw [h, map_zero] at hr1; exact zero_ne_one hr1
    refine ⟨Units.mk0 r.re hr0, hr1, Units.ext (FaithfulSMul.algebraMap_injective Fv E ?_)⟩
    rw [algebraMap_sqT]
    change r ^ 2 = _
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, ← hr]
  · rintro ⟨r₀, hr₀, rfl⟩
    have hzw := qlh_algebraMap_of_valued hb₁ (K := K) hr₀
    have hz2 : (algebraMap Fv E (r₀ : Fv)) ^ 2 = algebraMap Fv E ((r₀ ^ 2 : Fvˣ) : Fv) := by
      rw [Units.val_pow_eq_pow_val, map_pow]
    obtain ⟨t, htT, htz⟩ := exists_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 (v := v) (M := M) (hM1 := hM1) hW.deep
      hzw hz2
    refine ⟨⟨t, htT⟩, ?_, Units.ext (FaithfulSMul.algebraMap_injective Fv E ?_)⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_ZN_iff_of_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW htT]
      change (yv (t : GnK Fv a b d)).re.im = 0
      rw [htz]; rfl
    · rw [algebraMap_sqT]; change (yv (t : GnK Fv a b d)).re ^ 2 = _; rw [htz, hz2]

/-- The real part of a scalar $t\in T$. -/
abbrev reT (t : TY hb₁ hα hβ v M hM1) : E := (yv ((t : nsLocSub hb₁ hα hβ v M hM1) : GnK Fv a b d)).re

theorem re_sq_of_im_eq_zero {z : E} (h1 : z ^ 2 = 1) (h2 : z.im = 0) : z.re ^ 2 = 1 := by
  have := congrArg QuadraticAlgebra.re h1
  rw [pow_two, QuadraticAlgebra.re_mul, h2, QuadraticAlgebra.re_one] at this
  rw [pow_two]; linear_combination this

set_option maxHeartbeats 1000000 in
include hb₀ in
theorem card_H₀_ker (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    Nat.card ↥((ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).subgroupOf
      (TY hb₁ hα hβ v M hM1) ⊓ (sqT hb₁ hα hβ (v := v) (M := M) (hM1 := hM1)).ker) = 2 := by
  rw [← card_sqOne_field (L := Fv)]
  set H := (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).subgroupOf
      (TY hb₁ hα hβ v M hM1) ⊓ (sqT hb₁ hα hβ (v := v) (M := M) (hM1 := hM1)).ker
  have hmem : ∀ t : TY hb₁ hα hβ v M hM1, t ∈ H → (reT hb₁ hα hβ t).im = 0 ∧ reT hb₁ hα hβ t ^ 2 = 1 := by
    intro t ht
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 ht
    rw [Subgroup.mem_subgroupOf, mem_ZN_iff_of_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW t.2] at h1
    exact ⟨h1, (sqT_eq_one_iff hb₁ hα hβ t).1 h2⟩
  refine Nat.card_congr (Equiv.ofBijective (fun s : H => ⟨(reT hb₁ hα hβ (s : TY hb₁ hα hβ v M hM1)).re,
    re_sq_of_im_eq_zero (hmem _ s.2).2 (hmem _ s.2).1⟩) ⟨?_, ?_⟩)
  · intro s s' h
    have h' : reT hb₁ hα hβ (s : TY hb₁ hα hβ v M hM1) = reT hb₁ hα hβ (s' : TY hb₁ hα hβ v M hM1) :=
      QuadraticAlgebra.ext (congrArg Subtype.val h) ((hmem _ s.2).1.trans (hmem _ s'.2).1.symm)
    exact Subtype.ext (Subtype.ext (yv_injective_TY hb₁ hα hβ (s : TY hb₁ hα hβ v M hM1).2
      (s' : TY hb₁ hα hβ v M hM1).2 h'))
  · rintro ⟨x, hx⟩
    have hx1 : Valued.v x = 1 := by
      have h1 : Valued.v x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
      have h0 : x ≠ 0 := by intro h; rw [h, map_zero] at h1; norm_num at h1
      obtain ⟨k, hk⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v h0
      rw [hk, ← exp_nsmul, ← exp_zero, exp_inj] at h1; rw [hk, ← exp_zero, exp_inj]; simp at h1; omega
    have hzw := qlh_algebraMap_of_valued hb₁ (K := K) hx1
    have hz2 : (algebraMap Fv E x) ^ 2 = algebraMap Fv E 1 := by rw [← map_pow, hx]
    obtain ⟨t, htT, htz⟩ := exists_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 (v := v) (M := M) (hM1 := hM1) hW.deep
      hzw hz2
    let t' : TY hb₁ hα hβ v M hM1 := ⟨t, htT⟩
    have hre : reT hb₁ hα hβ t' = algebraMap Fv E x := htz
    have hin : t' ∈ H := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf, mem_ZN_iff_of_mem_TY hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW t'.2]
        change (reT hb₁ hα hβ t').im = 0
        rw [hre]; rfl
      · rw [MonoidHom.mem_ker, sqT_eq_one_iff]
        change reT hb₁ hα hβ t' ^ 2 = 1
        rw [hre, ← map_pow, hx, map_one]
    exact ⟨⟨t', hin⟩, Subtype.ext (by change (reT hb₁ hα hβ t').re = x; rw [hre]; rfl)⟩

theorem TY_comm (t t' : TY hb₁ hα hβ v M hM1) : t' * t = t * t' :=
  Subtype.ext (TY_central hb₁ hα hβ (t : nsLocSub hb₁ hα hβ v M hM1) t.2 t')

set_option maxHeartbeats 1000000 in
include hb₀ in
/-- **$[T : T\cap Z_N]\cdot2 = [N_v : \mathcal O_v^{\times2}]\cdot2^g$.** -/
theorem relIndex_ZN_TY (hW : WinHyp hb₁ hα0 hβ0 ha0 v M c₀ n N) :
    (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).relIndex (TY hb₁ hα hβ v M hM1) * 2 =
      (sqSub F v).relIndex (NvSub K v) * 2 ^ Fintype.card (PlaceSet (K := K) v) := by
  set H₀ := (ZN hb₁ hα hβ ha0 hd0 v M hM1 (one_le_of_winHyp hb₁ hα0 hβ0 ha0 hW)).subgroupOf (TY hb₁ hα hβ v M hM1)
  set f := sqT hb₁ hα hβ (v := v) (M := M) (hM1 := hM1)
  have h1 := Subgroup.relIndex_mul_index (H := H₀) (K := H₀ ⊔ f.ker) le_sup_left
  have hX : (H₀ ⊔ f.ker).index = (sqSub F v).relIndex (NvSub K v) := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap, map_sqT_H₀ hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW,
      range_sqT hb₀ hb₁ hα hβ hα0 hβ0 hW.deep]
  have hY : H₀.relIndex (H₀ ⊔ f.ker) = H₀.relIndex f.ker := by
    rw [sup_comm]; exact relIndex_sup_of_central H₀ f.ker (fun t _ g => TY_comm hb₁ hα hβ t g)
  rw [hX, hY] at h1
  have h2 := Subgroup.relIndex_mul_card (H := H₀) (K := f.ker)
  rw [card_H₀_ker hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 hW, card_ker_sqT hb₀ hb₁ hα hβ hα0 hβ0 hW.deep] at h2
  change H₀.index * 2 = _
  rw [← h1, ← h2]; ring

end Scalars
