/-
# Local–global gluing of left ideals up to central scalars ($h_F = 1$)

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$, $\mathcal O$ an order.

**Proves**
* `exists_global_scalar`: a family $(r_v)$ of $r_v \in F_v^\times$ with $|r_v|_v = 1$ for almost all $v$ is
  $|c|_v = |r_v|_v$ for one $c \in F^\times$ ($h_F = 1$: $c = \prod_v\varpi_v^{-k_v}$);
* `idealSet_localIdeal_rTrans`: completion commutes with right translation, $(J\beta)_v = J_v\iota_v(\beta)$;
* `exists_unit_of_rTrans_eq`: principal left ideals $\mathcal O_vx = \mathcal O_vx'$ have generators differing by a unit;
* `exists_scalar_of_local` (**the gluing lemma**): if $J'_v = J_v\,r_v\iota_v(\delta)$ with $r_v \in F_v^\times$ at every $v$, then
  $J' = J\,c\delta$ for some $c \in F^\times$.

Source: Voight 2021, §§9.4–9.5 (local–global for lattices), 17.4 (classes and $h_F$), (26.5.?) [unverified locators].
-/
import QuadFormsKB.Tamagawa.TernaryLocalStab

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

section Scalars

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)]

theorem genP_not_mem {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) : genP v ∉ w.asIdeal := by
  intro hmem
  apply h
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [span_genP, Ideal.span_le, Set.singleton_subset_iff]; exact hmem
  exact HeightOneSpectrum.ext ((v.isMaximal).eq_of_le w.isPrime.ne_top hle)

theorem valued_genP_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) :
    Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F (genP v))) = 1 := by
  rw [← IsScalarTower.algebraMap_apply, valued_algebraMap_int, HeightOneSpectrum.intValuation_eq_one_iff]
  exact genP_not_mem h

theorem valued_genP_self (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (genP v))) = exp (-1 : ℤ) := by
  rw [← IsScalarTower.algebraMap_apply, valued_algebraMap_int, intValuation_genP]

theorem genP_F_ne_zero (v : HeightOneSpectrum (𝓞 F)) : algebraMap (𝓞 F) F (genP v) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 genP_ne_zero

/-- **A global scalar with prescribed valuations** ($h_F = 1$): given integers $k_v$, zero outside a finite set $S$, there is
$c \in F^\times$ with $|c|_v = e^{k_v}$ at every finite $v$. -/
theorem exists_global_scalar (S : Finset (HeightOneSpectrum (𝓞 F))) (k : HeightOneSpectrum (𝓞 F) → ℤ)
    (hk : ∀ v ∉ S, k v = 0) :
    ∃ c : F, c ≠ 0 ∧ ∀ v, Valued.v (algebraMap F (v.adicCompletion F) c) = exp (k v) := by
  classical
  refine ⟨∏ v ∈ S, algebraMap (𝓞 F) F (genP v) ^ (-k v), Finset.prod_ne_zero_iff.2 fun v _ =>
    zpow_ne_zero _ (genP_F_ne_zero v), fun w => ?_⟩
  rw [map_prod, map_prod]
  simp only [map_zpow₀]
  by_cases hw : w ∈ S
  · rw [← Finset.mul_prod_erase S _ hw, valued_genP_self, Finset.prod_eq_one, mul_one, ← WithZero.exp_zsmul]
    · simp
    · intro v hv
      rw [valued_genP_ne (Finset.ne_of_mem_erase hv), _root_.one_zpow]
  · rw [hk w hw, Finset.prod_eq_one, WithZero.exp_zero]
    intro v hv
    rw [valued_genP_ne (by rintro rfl; exact hw hv), _root_.one_zpow]

end Scalars

section Ideals

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **Completion commutes with right translation:** if $J' = J\beta$ then $J'_v = J_v\,\iota_v(\beta)$. -/
theorem idealSet_localIdeal_rTrans (v : HeightOneSpectrum (𝓞 F)) {J J' : Ideal O} {β : QuatF F a b}
    (h : idealSet J' = rTrans (idealSet J) β) :
    idealSet (localIdeal (v := v) J') = rTrans (idealSet (localIdeal (v := v) J)) (complHom v a b β) := by
  -- the span of the image, translated
  have hspan : ∀ (J : Ideal O), idealSet (localIdeal (v := v) J) =
      (Submodule.span (v.adicCompletionIntegers F) (idealImage (v := v) J) : Set (QuatV v a b)) := by
    intro J
    ext y
    constructor
    · rintro ⟨_, hy⟩; exact (mem_localIdeal_iff).1 hy
    · intro hy
      refine ⟨?_, (mem_localIdeal_iff).2 hy⟩
      refine (Submodule.span_le.2 ?_ : Submodule.span _ (idealImage (v := v) J) ≤
        Subalgebra.toSubmodule (localOrder (v := v) a b O)) hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_localOrder_of_mem a b x.2
  have himg : idealImage (v := v) J' = (· * complHom v a b β) '' idealImage (v := v) J := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (x : QuatF F a b) ∈ rTrans (idealSet J) β := h ▸ coe_mem_idealSet.2 hx
      obtain ⟨z, hz, hzx⟩ := this
      refine ⟨complHom v a b z, ⟨⟨z, hz.1⟩, hz.2, rfl⟩, ?_⟩
      simp only [← hzx, map_mul]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have : (x : QuatF F a b) * β ∈ idealSet J' := by rw [h]; exact ⟨x, coe_mem_idealSet.2 hx, rfl⟩
      exact ⟨⟨_, this.1⟩, this.2, map_mul _ _ _⟩
  rw [hspan, hspan, himg]
  -- span of image under the 𝔬-linear map (· * β)
  set f : QuatV v a b →ₗ[v.adicCompletionIntegers F] QuatV v a b :=
    (LinearMap.mulRight (v.adicCompletion F) (complHom v a b β)).restrictScalars (v.adicCompletionIntegers F)
  have hf : ∀ y, f y = y * complHom v a b β := fun y => rfl
  have : (· * complHom v a b β) '' idealImage (v := v) J = f '' idealImage (v := v) J := rfl
  rw [this, ← Submodule.map_span, Submodule.map_coe]
  rfl

theorem idealSet_top_local (v : HeightOneSpectrum (𝓞 F)) :
    idealSet (⊤ : Ideal (localOrder (v := v) a b O)) = (localOrder (v := v) a b O : Set (QuatV v a b)) := by
  ext y; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Submodule.mem_top⟩⟩

/-- **Generators of a principal left ideal differ by a unit:** $\mathcal O_vx = \mathcal O_vx'$ ($x, x' \in D_v^\times$) gives
$x' = ux$ with $u \in \mathcal O_v^\times$. -/
theorem exists_unit_of_rTrans_eq (v : HeightOneSpectrum (𝓞 F)) {x x' : (QuatV v a b)ˣ}
    (h : rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) x' =
      rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) x) :
    ∃ u ∈ unitsOv (O := O) v, x' = u * x := by
  have h1 : (x' : QuatV v a b) ∈ rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) x := by
    rw [← h]; exact ⟨1, Subalgebra.one_mem _, one_mul _⟩
  have h2 : (x : QuatV v a b) ∈ rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) x' := by
    rw [h]; exact ⟨1, Subalgebra.one_mem _, one_mul _⟩
  obtain ⟨p, hp, hpx⟩ := h1
  obtain ⟨q, hq, hqx⟩ := h2
  refine ⟨x' * x⁻¹, ⟨?_, ?_⟩, by group⟩
  · rw [Units.val_mul, ← hpx, mul_assoc, Units.mul_inv, mul_one]; exact hp
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← hqx, mul_assoc, Units.mul_inv, mul_one]; exact hq

theorem algebraMap_Fv_mem_localOrder (v : HeightOneSpectrum (𝓞 F)) {c : v.adicCompletion F}
    (hc : Valued.v c ≤ 1) : algebraMap (v.adicCompletion F) (QuatV v a b) c ∈ localOrder (v := v) a b O := by
  have := algebraMap_mem_localOrder (O := O) v ⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc⟩
  exact this

/-- Right translation by a central unit $c \in \mathfrak o_v^\times$ fixes a left ideal: $J_vc = J_v$. -/
theorem rTrans_scalar_local (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (localOrder (v := v) a b O))
    {c : v.adicCompletion F} (hc : Valued.v c = 1) :
    rTrans (idealSet I) (algebraMap (v.adicCompletion F) (QuatV v a b) c) = idealSet I := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have key : ∀ {d : v.adicCompletion F}, Valued.v d ≤ 1 →
      rTrans (idealSet I) (algebraMap (v.adicCompletion F) (QuatV v a b) d) ⊆ idealSet I := by
    intro d hd
    rintro _ ⟨y, ⟨hyO, hyI⟩, rfl⟩
    have hdO := algebraMap_Fv_mem_localOrder (O := O) v hd
    have hcomm : y * algebraMap (v.adicCompletion F) (QuatV v a b) d =
        algebraMap (v.adicCompletion F) (QuatV v a b) d * y := (Algebra.commutes _ _).symm
    show y * _ ∈ idealSet I
    rw [hcomm]
    exact mul_mem_idealSet hdO ⟨hyO, hyI⟩
  refine le_antisymm (key hc.le) fun y hy => ?_
  refine ⟨y * algebraMap (v.adicCompletion F) (QuatV v a b) c⁻¹, key (by rw [map_inv₀, hc, inv_one]) ⟨y, hy, rfl⟩, ?_⟩
  simp only
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, mul_one]

theorem valued_eq_one_of_scalar_unit (v : HeightOneSpectrum (𝓞 F)) (hO : IsOrder (𝓞 F) F O) {r : v.adicCompletion F}
    (hr : r ≠ 0) (h1 : algebraMap (v.adicCompletion F) (QuatV v a b) r ∈ localOrder (v := v) a b O)
    (h2 : algebraMap (v.adicCompletion F) (QuatV v a b) r⁻¹ ∈ localOrder (v := v) a b O) : Valued.v r = 1 := by
  have hOv := isOrder_localOrder (v := v) hO
  have hn : ∀ {d : v.adicCompletion F}, algebraMap (v.adicCompletion F) (QuatV v a b) d ∈ localOrder (v := v) a b O →
      Valued.v d ≤ 1 := by
    intro d hd
    obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hd).2
    have : nrd (algebraMap (v.adicCompletion F) (QuatV v a b) d) = d ^ 2 := by
      simp [nrd, QuaternionAlgebra.algebraMap_eq]; try ring
    rw [this] at ht
    have hle : Valued.v (d ^ 2) ≤ 1 := by
      rw [← ht]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 t.2
    rw [map_pow] at hle
    exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 hle
  have a1 := hn h1
  have a2 := hn h2
  rw [map_inv₀] at a2
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hr))).1 a2)

theorem inv_eq_mul_of_mul_eq_one {M : Type*} [Monoid M] {y R Ri d di : M} (e1 : y * R * d = 1) (hRRi : R * Ri = 1)
    (hdd : d * di = 1) : Ri = d * y := by
  have e2 : y * R = di := by
    calc y * R = y * R * (d * di) := by rw [hdd, mul_one]
      _ = (y * R * d) * di := by simp only [mul_assoc]
      _ = di := by rw [e1, one_mul]
  have e3 : y = di * Ri := by
    calc y = y * (R * Ri) := by rw [hRRi, mul_one]
      _ = (y * R) * Ri := by rw [mul_assoc]
      _ = di * Ri := by rw [e2]
  rw [e3, ← mul_assoc, hdd, one_mul]

set_option maxHeartbeats 1000000 in
/-- **The gluing lemma** ($h_F = 1$): let $J, J'$ be left ideals of $\mathcal O$ containing $n, n' \ne 0$, and $\delta \in D^\times$. If at
every finite place $J'_v = J_v\,r_v\iota_v(\delta)$ for some $r_v \in F_v^\times$, then $J' = J\,c\delta$ for some $c \in F^\times$. -/
theorem exists_scalar_of_local (hO : IsOrder (𝓞 F) F O) {J J' : Ideal O} {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hnJ : algebraMap (𝓞 F) O n ∈ J) (hnJ' : algebraMap (𝓞 F) O n' ∈ J') (δ : (QuatF F a b)ˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : v.adicCompletion F, r ≠ 0 ∧
      idealSet (localIdeal (v := v) J') = rTrans (idealSet (localIdeal (v := v) J))
        (algebraMap (v.adicCompletion F) (QuatV v a b) r * complHom v a b (δ : QuatF F a b))) :
    ∃ c : F, c ≠ 0 ∧ idealSet J' = rTrans (idealSet J) (algebraMap F (QuatF F a b) c * δ) := by
  classical
  choose r hr0 hr using h
  obtain ⟨m, hm0, hmδ⟩ := exists_smul_mem_order hO (δ : QuatF F a b)
  obtain ⟨m', hm0', hmδ'⟩ := exists_smul_mem_order hO ((δ⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)
  set N := n * n' * m * m'
  have hN : N ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hn hn') hm0) hm0'
  set S := primeSupport hN
  -- away from S the scalars are units
  have hunit : ∀ v ∉ S, Valued.v (r v) = 1 := by
    intro v hv
    have hvN : N ∉ v.asIdeal := fun h => hv ((mem_primeSupport hN).2 h)
    have hvn : n ∉ v.asIdeal := fun h => hvN (by
      simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h)))
    have hvn' : n' ∉ v.asIdeal := fun h => hvN (by
      simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h)))
    have hvm : m ∉ v.asIdeal := fun h => hvN (by simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
    have hvm' : m' ∉ v.asIdeal := fun h => hvN (by simp only [N]; exact v.asIdeal.mul_mem_left _ h)
    have hJ := localIdeal_eq_top v hnJ hvn
    have hJ' := localIdeal_eq_top v hnJ' hvn'
    have hrv := hr v
    rw [hJ, hJ', idealSet_top_local] at hrv
    -- δ_v and δ_v⁻¹ lie in O_v
    have hδO : ∀ {k : 𝓞 F} {z : QuatF F a b}, k ∉ v.asIdeal → algebraMap (𝓞 F) F k • z ∈ O →
        complHom v a b z ∈ localOrder (v := v) a b O := by
      intro k z hk hkz
      obtain ⟨u, hu⟩ := isUnit_ι_of_not_mem hk
      have h1 := mem_localOrder_of_mem (v := v) a b hkz
      rw [complHom_smul_int] at h1
      have : complHom v a b z = ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) •
          (ι v k • complHom v a b z) := by
        rw [smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [this]; exact Subalgebra.smul_mem _ h1 _
    have hd1 := hδO hvm hmδ
    have hd2 := hδO hvm' hmδ'
    have hmul : complHom v a b (δ : QuatF F a b) * complHom v a b ((δ⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    -- r_v δ_v ∈ O_v and 1 ∈ O_v r_v δ_v
    have h1 : algebraMap (v.adicCompletion F) (QuatV v a b) (r v) * complHom v a b (δ : QuatF F a b) ∈
        localOrder (v := v) a b O := by
      have : (1 : QuatV v a b) * (algebraMap (v.adicCompletion F) (QuatV v a b) (r v) *
          complHom v a b (δ : QuatF F a b)) ∈ rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) _ :=
        ⟨1, Subalgebra.one_mem _, rfl⟩
      rw [one_mul, ← hrv] at this; exact this
    have h2 : (1 : QuatV v a b) ∈ rTrans (localOrder (v := v) a b O : Set (QuatV v a b))
        (algebraMap (v.adicCompletion F) (QuatV v a b) (r v) * complHom v a b (δ : QuatF F a b)) := by
      rw [← hrv]; exact Subalgebra.one_mem _
    obtain ⟨y, hy, hy1⟩ := h2
    refine valued_eq_one_of_scalar_unit v hO (hr0 v) ?_ ?_
    · have := Subalgebra.mul_mem _ h1 hd2
      rwa [mul_assoc, hmul, mul_one] at this
    · have : algebraMap (v.adicCompletion F) (QuatV v a b) (r v)⁻¹ = complHom v a b (δ : QuatF F a b) * y := by
        have e1 : y * algebraMap (v.adicCompletion F) (QuatV v a b) (r v) * complHom v a b (δ : QuatF F a b) = 1 := by
          rw [mul_assoc]; exact hy1
        exact inv_eq_mul_of_mul_eq_one e1 (by rw [← map_mul, mul_inv_cancel₀ (hr0 v), map_one]) hmul
      rw [this]; exact Subalgebra.mul_mem _ hd1 hy
  -- the exponents
  have hex : ∀ v, ∃ k : ℤ, Valued.v (r v) = exp k := fun v => exists_valued_eq_exp v (hr0 v)
  choose k hk using hex
  have hk0 : ∀ v ∉ S, k v = 0 := by
    intro v hv
    have := hunit v hv
    rw [hk v] at this
    exact WithZero.exp_eq_one.1 this
  obtain ⟨c, hc0, hc⟩ := exists_global_scalar S k hk0
  refine ⟨c, hc0, ?_⟩
  -- local equalities with c
  have hloc : ∀ v, idealSet (localIdeal (v := v) J') =
      rTrans (idealSet (localIdeal (v := v) J)) (complHom v a b (algebraMap F (QuatF F a b) c * δ)) := by
    intro v
    have hcv : algebraMap F (v.adicCompletion F) c ≠ 0 := (map_ne_zero _).2 hc0
    set u := r v / algebraMap F (v.adicCompletion F) c
    have hu : Valued.v u = 1 := by
      rw [map_div₀, hk v, hc v, div_self (WithZero.exp_ne_zero)]
    have hsplit : algebraMap (v.adicCompletion F) (QuatV v a b) (r v) * complHom v a b (δ : QuatF F a b) =
        algebraMap (v.adicCompletion F) (QuatV v a b) u * complHom v a b (algebraMap F (QuatF F a b) c * δ) := by
      rw [map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply F (v.adicCompletion F) (QuatV v a b),
        ← mul_assoc, ← map_mul]
      congr 2
      simp only [u]; field_simp
    rw [hr v, hsplit, ← rTrans_rTrans, rTrans_scalar_local v _ hu]
  have hcδ : IsUnit (algebraMap F (QuatF F a b) c * δ) :=
    (IsUnit.map _ (isUnit_iff_ne_zero.2 hc0)).mul δ.isUnit
  set w := hcδ.unit
  ext z
  constructor
  · intro hz
    set y := z * ((w⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)
    have hyloc : ∀ v, complHom v a b y ∈ idealSet (localIdeal (v := v) J) := by
      intro v
      have h1 : complHom v a b z ∈ idealSet (localIdeal (v := v) J') := complHom_mem_idealSet_localIdeal v hz
      rw [hloc v] at h1
      obtain ⟨t, ht, hzt⟩ := h1
      have : complHom v a b y = t := by
        have hw1 : (algebraMap F (QuatF F a b) c * (δ : QuatF F a b)) * ((w⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) = 1 := by
          rw [show (algebraMap F (QuatF F a b) c * (δ : QuatF F a b)) = (w : QuatF F a b) from rfl, Units.mul_inv]
        have hzt' : complHom v a b z = t * complHom v a b (algebraMap F (QuatF F a b) c * δ) := hzt.symm
        calc complHom v a b y = complHom v a b z * complHom v a b ((w⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) :=
              map_mul _ _ _
          _ = t * complHom v a b ((algebraMap F (QuatF F a b) c * δ) * ((w⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) := by
              rw [hzt', mul_assoc, ← map_mul]
          _ = t := by rw [hw1, map_one, mul_one]
      rw [this]; exact ht
    have hyO : y ∈ O := mem_order_of_forall_complHom_mem hO fun v => idealSet_subset _ (hyloc v)
    have hyJ : (⟨y, hyO⟩ : O) ∈ J := mem_of_forall_toLocal_mem hO hn hnJ fun v => (hyloc v).2
    refine ⟨y, ⟨hyO, hyJ⟩, ?_⟩
    simp only [y, mul_assoc]
    rw [show ((w⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) * (algebraMap F (QuatF F a b) c * (δ : QuatF F a b)) = 1 from by
      rw [show (algebraMap F (QuatF F a b) c * (δ : QuatF F a b)) = (w : QuatF F a b) from rfl, Units.inv_mul], mul_one]
  · rintro ⟨y, hy, rfl⟩
    have hzloc : ∀ v, complHom v a b (y * (algebraMap F (QuatF F a b) c * δ)) ∈ idealSet (localIdeal (v := v) J') := by
      intro v
      rw [hloc v]
      exact ⟨_, complHom_mem_idealSet_localIdeal v hy, (map_mul _ _ _).symm⟩
    have hzO := mem_order_of_forall_complHom_mem hO fun v => idealSet_subset _ (hzloc v)
    exact ⟨hzO, mem_of_forall_toLocal_mem hO hn' hnJ' fun v => (hzloc v).2⟩

end Ideals

end QuadFormsKB.QuatOrder
