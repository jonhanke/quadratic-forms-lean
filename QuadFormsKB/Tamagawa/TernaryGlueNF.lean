/-
# Gluing left ideals up to a fractional ideal of $F$, every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ an order of $D$, $v$ the finite places.

The gluing lemma (`exists_scalar_of_local`) turns local scalars $r_v \in F_v^\times$ (almost all units) into one
global scalar $c \in F^\times$, which needs $h_F = 1$. In general the $r_v$ glue to the **fractional ideal**
$\prod_v\mathfrak p_v^{v(r_v)}$, written
$\mathfrak a\mathfrak b^{-1}$ with $\mathfrak a, \mathfrak b$ integral ($\mathfrak a = \prod\mathfrak p_v^{\max(-k_v,0)}$, $\mathfrak b = \prod\mathfrak p_v^{\max(k_v,0)}$,
$|r_v|_v = e^{k_v}$):

* `localIdeal_scaleIdeal`: $(\mathfrak aJ)_v = J_v\,t$ when $\mathfrak a\,\mathfrak o_v = (t)$;
* `map_ι_prod_pow`: $\big(\prod_{w\in S}\mathfrak p_w^{e_w}\big)\mathfrak o_v = (\varpi_v^{e_v})$ ($v \in S$), $= \mathfrak o_v$ ($v \notin S$);
* **`exists_scale_of_local`** (the gluing lemma): if $J'_v = J_v\,r_v\iota_v(\delta)$ ($r_v \in F_v^\times$) at every $v$, then
  $\mathfrak bJ' = \mathfrak aJ\delta$ for nonzero integral ideals $\mathfrak a, \mathfrak b$.

No basis of $\mathcal O$ or of an ideal and no generator of an ideal of $\mathcal O_F$ is chosen.

Source: Voight 2021, §§9.4–9.5 (local–global for lattices), §17.4 (classes), §26.5 (the action of $\mathrm{Cl}(F)$) [unverified locators].
-/
import QuadFormsKB.Tamagawa.TernaryIndexNF
import QuadFormsKB.Tamagawa.QuatIdealScaleNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

/-! ### Local helpers (PID-free copies of the lemmas in `TernaryGlue.lean`) -/

section LocalHelpers

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem idealSet_top_local_nf :
    idealSet (⊤ : Ideal (localOrder (v := v) a b O)) = (localOrder (v := v) a b O : Set (QuatV v a b)) := by
  ext y; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Submodule.mem_top⟩⟩

theorem algebraMap_Fv_mem_localOrder_nf {c : Fv} (hc : Valued.v c ≤ 1) :
    algebraMap Fv (QuatV v a b) c ∈ localOrder (v := v) a b O := by
  have : algebraMap Fv (QuatV v a b) c =
      algebraMap 𝔬 (QuatV v a b) ⟨c, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hc⟩ := rfl
  rw [this]; exact Subalgebra.algebraMap_mem _ _

/-- Right translation by a central unit $c \in \mathfrak o_v^\times$ fixes a left ideal. -/
theorem rTrans_scalar_local_nf (I : Ideal (localOrder (v := v) a b O)) {c : Fv} (hc : Valued.v c = 1) :
    rTrans (idealSet I) (algebraMap Fv (QuatV v a b) c) = idealSet I := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have key : ∀ {d : Fv}, Valued.v d ≤ 1 → rTrans (idealSet I) (algebraMap Fv (QuatV v a b) d) ⊆ idealSet I := by
    intro d hd
    rintro _ ⟨y, ⟨hyO, hyI⟩, rfl⟩
    have hdO := algebraMap_Fv_mem_localOrder_nf (O := O) v hd
    have hcomm : y * algebraMap Fv (QuatV v a b) d = algebraMap Fv (QuatV v a b) d * y := (Algebra.commutes _ _).symm
    show y * _ ∈ idealSet I
    rw [hcomm]
    exact mul_mem_idealSet hdO ⟨hyO, hyI⟩
  refine le_antisymm (key hc.le) fun y hy => ?_
  refine ⟨y * algebraMap Fv (QuatV v a b) c⁻¹, key (by rw [map_inv₀, hc, inv_one]) ⟨y, hy, rfl⟩, ?_⟩
  simp only
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, mul_one]

theorem valued_eq_one_of_scalar_unit_nf (hO : IsOrder (𝓞 F) F O) {r : Fv} (hr : r ≠ 0)
    (h1 : algebraMap Fv (QuatV v a b) r ∈ localOrder (v := v) a b O)
    (h2 : algebraMap Fv (QuatV v a b) r⁻¹ ∈ localOrder (v := v) a b O) : Valued.v r = 1 := by
  have hOv := Gen.isOrder_localOrder_gen v hO
  have hn : ∀ {d : Fv}, algebraMap Fv (QuatV v a b) d ∈ localOrder (v := v) a b O → Valued.v d ≤ 1 := by
    intro d hd
    obtain ⟨t, ht⟩ := (isInteger_trd_nrd hOv hd).2
    have : nrd (algebraMap Fv (QuatV v a b) d) = d ^ 2 := by
      simp [nrd, QuaternionAlgebra.algebraMap_eq]
    rw [this] at ht
    have hle : Valued.v (d ^ 2) ≤ 1 := by
      rw [← ht]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 t.2
    rw [map_pow] at hle
    exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 hle
  have a1 := hn h1
  have a2 := hn h2
  rw [map_inv₀] at a2
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hr))).1 a2)

/-- Generators of a principal left ideal differ by a unit. -/
theorem exists_unit_of_rTrans_eq_nf {x x' : (QuatV v a b)ˣ}
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

theorem rTrans_localOrder_unit_nf {u : (QuatV v a b)ˣ} (hu : u ∈ unitsOv (O := O) v) :
    rTrans (localOrder (v := v) a b O : Set (QuatV v a b)) (u : QuatV v a b) =
      (localOrder (v := v) a b O : Set (QuatV v a b)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩; exact Subalgebra.mul_mem _ hz hu.1
  · intro hy
    refine ⟨y * ((u⁻¹ : (QuatV v a b)ˣ) : QuatV v a b), Subalgebra.mul_mem _ hy hu.2, ?_⟩
    simp only [mul_assoc, Units.inv_mul, mul_one]

/-- The idealSet of the completion is the $\mathfrak o_v$-span of the image. -/
theorem idealSet_localIdeal_eq_span (J : Ideal O) :
    idealSet (localIdeal (v := v) J) = (Submodule.span 𝔬 (idealImage (v := v) J) : Set (QuatV v a b)) := by
  ext y
  constructor
  · rintro ⟨_, hy⟩; exact (Gen.mem_localIdeal_iff).1 hy
  · intro hy
    refine ⟨?_, (Gen.mem_localIdeal_iff).2 hy⟩
    refine (Submodule.span_le.2 ?_ : Submodule.span _ (idealImage (v := v) J) ≤
      Subalgebra.toSubmodule (localOrder (v := v) a b O)) hy
    rintro _ ⟨x, -, rfl⟩
    exact mem_localOrder_of_mem a b x.2

/-- **Completion commutes with right translation:** if $J' = J\beta$ then $J'_v = J_v\,\iota_v(\beta)$. -/
theorem idealSet_localIdeal_rTrans_nf {J J' : Ideal O} {β : QuatF F a b}
    (h : idealSet J' = rTrans (idealSet J) β) :
    idealSet (localIdeal (v := v) J') = rTrans (idealSet (localIdeal (v := v) J)) (complHom v a b β) := by
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
  rw [idealSet_localIdeal_eq_span, idealSet_localIdeal_eq_span, himg]
  set f : QuatV v a b →ₗ[𝔬] QuatV v a b :=
    (LinearMap.mulRight Fv (complHom v a b β)).restrictScalars 𝔬
  have : (· * complHom v a b β) '' idealImage (v := v) J = f '' idealImage (v := v) J := rfl
  rw [this, ← Submodule.map_span, Submodule.map_coe]
  rfl

end LocalHelpers

/-! ### Completion of $\mathfrak aJ$ -/

section Scale

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$(\mathfrak aJ)_v = J_v\,t$** when $\mathfrak a\,\mathfrak o_v = (t)$. -/
theorem localIdeal_scaleIdeal {𝔞 : Ideal (𝓞 F)} {t : 𝔬} (ht : Ideal.map (ι v) 𝔞 = Ideal.span {t}) (J : Ideal O) :
    idealSet (localIdeal (v := v) (Gen.scaleIdeal 𝔞 J)) =
      rTrans (idealSet (localIdeal (v := v) J)) (algebraMap Fv (QuatV v a b) (t : Fv)) := by
  set T := algebraMap Fv (QuatV v a b) (t : Fv)
  have hcomm : ∀ y : QuatV v a b, y * T = t • y := fun y => by
    rw [Algebra.smul_def]; exact (Algebra.commutes _ _).symm
  set N := Submodule.span 𝔬 (idealImage (v := v) J)
  have hN : (N.map ((LinearMap.mulRight Fv T).restrictScalars 𝔬) : Set (QuatV v a b)) =
      rTrans (N : Set (QuatV v a b)) T := by rw [Submodule.map_coe]; rfl
  rw [idealSet_localIdeal_eq_span, idealSet_localIdeal_eq_span, ← hN]
  congr 1
  apply le_antisymm
  · have key : ∀ z ∈ Gen.scaleSet 𝔞 (idealSet J),
        complHom v a b z ∈ N.map ((LinearMap.mulRight Fv T).restrictScalars 𝔬) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨r, hr, y, hy, rfl⟩ := hz
        have hrt : ι v r ∈ Ideal.span {t} := ht ▸ Ideal.mem_map_of_mem _ hr
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hrt
        refine ⟨c • complHom v a b y, N.smul_mem c (Submodule.subset_span ⟨⟨y, hy.1⟩, hy.2, rfl⟩), ?_⟩
        change c • complHom v a b y * T = complHom v a b (r • y)
        rw [hcomm, smul_smul, mul_comm, hc, complHom_int_smul]
      | zero => exact ⟨0, N.zero_mem, by rw [LinearMap.map_zero, map_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨x', hx', e1⟩ := hx; obtain ⟨y', hy', e2⟩ := hy
        exact ⟨x' + y', N.add_mem hx' hy', by
          rw [map_add, e1, e2, map_add]⟩
      | smul c x _ hx =>
        obtain ⟨x', hx', e1⟩ := hx
        exact ⟨ι v c • x', N.smul_mem _ hx', by rw [map_smul, e1, complHom_int_smul]⟩
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact key _ hx
  · rintro _ ⟨y, hy, rfl⟩
    change y * T ∈ _
    rw [hcomm]
    -- `t ∈ 𝔞𝔬_v`
    have htm : t ∈ Ideal.map (ι v) 𝔞 := ht ▸ Ideal.mem_span_singleton_self t
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      -- `t = ∑ c_k ι(r_k)`
      refine Submodule.span_induction (p := fun s _ => s • complHom v a b (x : QuatF F a b) ∈
        Submodule.span 𝔬 (idealImage (v := v) (Gen.scaleIdeal 𝔞 J))) ?_ ?_ ?_ ?_ htm
      · rintro _ ⟨r, hr, rfl⟩
        have hmem : (r • x : O) ∈ Gen.scaleIdeal 𝔞 J := by
          show ((r • x : O) : QuatF F a b) ∈ Gen.scaleSet 𝔞 (idealSet J)
          exact Gen.smul_mem_scaleSet hr (coe_mem_idealSet.2 hx)
        refine Submodule.subset_span ⟨r • x, hmem, ?_⟩
        show complHom v a b (r • (x : QuatF F a b)) = _
        rw [complHom_int_smul]
      · rw [zero_smul]; exact Submodule.zero_mem _
      · intro s s' _ _ hs hs'; rw [add_smul]; exact Submodule.add_mem _ hs hs'
      · intro c s _ hs; rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hs
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem map_ι_asIdeal_self : Ideal.map (ι v) v.asIdeal = Ideal.span {π v} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have := (ι_mem_span_π_pow v 1 x).2 (by rwa [pow_one])
    rwa [pow_one] at this
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨u, hu⟩ := v.intValuation_exists_uniformizer
    have hu0 : u ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, hu]; exact WithZero.exp_lt_one_iff.2 (by norm_num)
    have hval : Valued.v ((ι v u : 𝔬) : Fv) = exp (-1 : ℤ) := by rw [valued_ι, hu]
    have hassoc : Associated (ι v u) (π v) := by
      have h1 := irreducible_of_valued v hval
      exact (irreducible_π v).associated_of_dvd h1 (by
        rw [← pow_one (π v), π_pow_dvd_ι_iff, pow_one]; exact hu0) |>.symm
    obtain ⟨w, hw⟩ := hassoc.symm
    have : π v = ι v u * ((w⁻¹ : 𝔬ˣ) : 𝔬) := by rw [← hw, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hu0)

theorem map_ι_asIdeal_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : Ideal.map (ι v) w.asIdeal = ⊤ := by
  have hle : ¬ w.asIdeal ≤ v.asIdeal := fun h => hw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top h))
  obtain ⟨s, hs, hsv⟩ := IsConcreteLE.not_le_iff_exists.1 hle
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hs) (Gen.isUnit_ι_of_not_mem hsv)

open Classical in
/-- **The completion of $\prod_{w\in S}\mathfrak p_w^{e_w}$.** -/
theorem map_ι_prod_pow (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ) :
    Ideal.map (ι v) (∏ w ∈ S, w.asIdeal ^ e w) = Ideal.span {π v ^ (if v ∈ S then e v else 0)} := by
  rw [show Ideal.map (ι v) (∏ w ∈ S, w.asIdeal ^ e w) = Ideal.mapHom (ι v) (∏ w ∈ S, w.asIdeal ^ e w) from rfl,
    map_prod]
  simp_rw [map_pow, Ideal.mapHom_apply]
  split_ifs with hv
  · rw [← Finset.mul_prod_erase S _ hv, map_ι_asIdeal_self, Ideal.span_singleton_pow, Finset.prod_eq_one, mul_one]
    intro w hw
    rw [map_ι_asIdeal_ne v (Finset.ne_of_mem_erase hw), Ideal.top_pow, Ideal.one_eq_top]
  · rw [Finset.prod_eq_one, pow_zero, Ideal.span_singleton_one, Ideal.one_eq_top]
    intro w hw
    rw [map_ι_asIdeal_ne v (by rintro rfl; exact hv hw), Ideal.top_pow, Ideal.one_eq_top]

end Scale

/-! ### The gluing lemma -/

section Glue

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-- **Membership in a left ideal is local.** -/
theorem mem_idealSet_iff_local (hO : IsOrder (𝓞 F) F O) {I : Ideal O} {n : 𝓞 F} (hn : n ≠ 0)
    (hnI : algebraMap (𝓞 F) O n ∈ I) (x : QuatF F a b) :
    x ∈ idealSet I ↔ ∀ v : HeightOneSpectrum (𝓞 F), complHom v a b x ∈ idealSet (localIdeal (v := v) I) := by
  refine ⟨fun hx v => Gen.complHom_mem_idealSet_localIdeal v hx, fun h => ?_⟩
  have hxO : x ∈ O := Gen.mem_order_of_forall_complHom_mem hO fun v => idealSet_subset _ (h v)
  exact ⟨hxO, Gen.mem_of_forall_toLocal_mem hO hn hnI fun v => (h v).2⟩

theorem algebraMap_mem_scaleIdeal {𝔞 : Ideal (𝓞 F)} {m : 𝓞 F} (hm : m ∈ 𝔞) {J : Ideal O} {n : 𝓞 F}
    (hnJ : algebraMap (𝓞 F) O n ∈ J) : algebraMap (𝓞 F) O (m * n) ∈ Gen.scaleIdeal 𝔞 J := by
  show ((algebraMap (𝓞 F) O (m * n) : O) : QuatF F a b) ∈ Gen.scaleSet 𝔞 (idealSet J)
  have : ((algebraMap (𝓞 F) O (m * n) : O) : QuatF F a b) = m • ((algebraMap (𝓞 F) O n : O) : QuatF F a b) := by
    simp only [map_mul, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Algebra.smul_def]
  rw [this]
  exact Gen.smul_mem_scaleSet hm (coe_mem_idealSet.2 hnJ)

theorem prod_pow_ne_bot (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ) :
    (∏ w ∈ S, w.asIdeal ^ e w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  intro w _
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem toNat_sub_toNat_neg' (k : ℤ) : ((k.toNat : ℕ) : ℤ) - ((-k).toNat : ℕ) = k := Int.toNat_sub_toNat_neg k

set_option maxHeartbeats 1600000 in
/-- **The gluing lemma for every class number:** let $J, J'$ be left ideals of $\mathcal O$ containing $n, n' \ne 0$ and
$\delta \in D^\times$. If at every finite place $J'_v = J_v\,r_v\iota_v(\delta)$ for some $r_v \in F_v^\times$, then
$\mathfrak bJ' = \mathfrak aJ\delta$ for some nonzero integral ideals $\mathfrak a, \mathfrak b$ of $\mathcal O_F$
($\mathfrak a\mathfrak b^{-1}$ = the fractional ideal with local generators $r_v$). -/
@[kb "voight2021" "§§9.4–9.5, 17.4; Lemma 26.5.? (the class group acting on left classes) [unverified]"]
theorem exists_scale_of_local (hO : IsOrder (𝓞 F) F O) {J J' : Ideal O} {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hnJ : algebraMap (𝓞 F) O n ∈ J) (hnJ' : algebraMap (𝓞 F) O n' ∈ J') (δ : (QuatF F a b)ˣ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : v.adicCompletion F, r ≠ 0 ∧
      idealSet (localIdeal (v := v) J') = rTrans (idealSet (localIdeal (v := v) J))
        (algebraMap (v.adicCompletion F) (QuatV v a b) r * complHom v a b (δ : QuatF F a b))) :
    ∃ 𝔞 𝔟 : Ideal (𝓞 F), 𝔞 ≠ ⊥ ∧ 𝔟 ≠ ⊥ ∧
      idealSet (Gen.scaleIdeal 𝔟 J') = rTrans (idealSet (Gen.scaleIdeal 𝔞 J)) (δ : QuatF F a b) := by
  classical
  choose r hr0 hr using h
  obtain ⟨m, hm0, hmδ⟩ := exists_smul_mem_order_nf hO (δ : QuatF F a b)
  obtain ⟨m', hm0', hmδ'⟩ := exists_smul_mem_order_nf hO ((δ⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)
  set N := n * n' * m * m'
  have hN : N ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hn hn') hm0) hm0'
  set S := Gen.primeSupport hN
  -- away from S the scalars are units
  have hunit : ∀ v ∉ S, Valued.v (r v) = 1 := by
    intro v hv
    have hvN : N ∉ v.asIdeal := fun h => hv ((Gen.mem_primeSupport hN).2 h)
    have hvn : n ∉ v.asIdeal := fun h => hvN (by
      simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ h)))
    have hvn' : n' ∉ v.asIdeal := fun h => hvN (by
      simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h)))
    have hvm : m ∉ v.asIdeal := fun h => hvN (by simp only [N]; exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ h))
    have hvm' : m' ∉ v.asIdeal := fun h => hvN (by simp only [N]; exact v.asIdeal.mul_mem_left _ h)
    have hJ := Gen.localIdeal_eq_top v hnJ hvn
    have hJ' := Gen.localIdeal_eq_top v hnJ' hvn'
    have hrv := hr v
    rw [hJ, hJ', idealSet_top_local_nf] at hrv
    have hδO : ∀ {k : 𝓞 F} {z : QuatF F a b}, k ∉ v.asIdeal → k • z ∈ O →
        complHom v a b z ∈ localOrder (v := v) a b O := by
      intro k z hk hkz
      obtain ⟨u, hu⟩ := Gen.isUnit_ι_of_not_mem hk
      have h1 := mem_localOrder_of_mem (v := v) a b hkz
      rw [complHom_int_smul] at h1
      have : complHom v a b z = ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) •
          (ι v k • complHom v a b z) := by
        rw [smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [this]; exact Subalgebra.smul_mem _ h1 _
    have hd1 := hδO hvm hmδ
    have hd2 := hδO hvm' hmδ'
    have hmul : complHom v a b (δ : QuatF F a b) * complHom v a b ((δ⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
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
    refine valued_eq_one_of_scalar_unit_nf v hO (hr0 v) ?_ ?_
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
  set ea : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (-k v).toNat
  set eb : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (k v).toNat
  set 𝔞 := ∏ w ∈ S, w.asIdeal ^ ea w
  set 𝔟 := ∏ w ∈ S, w.asIdeal ^ eb w
  have h𝔞 : 𝔞 ≠ ⊥ := prod_pow_ne_bot S ea
  have h𝔟 : 𝔟 ≠ ⊥ := prod_pow_ne_bot S eb
  have hea : ∀ v, (if v ∈ S then ea v else 0) = ea v := fun v => by
    split_ifs with hv
    · rfl
    · simp [ea, hk0 v hv]
  have heb : ∀ v, (if v ∈ S then eb v else 0) = eb v := fun v => by
    split_ifs with hv
    · rfl
    · simp [eb, hk0 v hv]
  refine ⟨𝔞, 𝔟, h𝔞, h𝔟, ?_⟩
  -- the local identities
  have hloc : ∀ v, idealSet (localIdeal (v := v) (Gen.scaleIdeal 𝔟 J')) =
      rTrans (idealSet (localIdeal (v := v) (Gen.scaleIdeal 𝔞 J))) (complHom v a b (δ : QuatF F a b)) := by
    intro v
    have hπ0 : ((π v : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
      intro h0; have := valued_π v; rw [h0, map_zero] at this; exact WithZero.exp_ne_zero this.symm
    set P := ((π v : v.adicCompletionIntegers F) : v.adicCompletion F)
    have hA := localIdeal_scaleIdeal (O := O) v (map_ι_prod_pow v S ea) J
    have hB := localIdeal_scaleIdeal (O := O) v (map_ι_prod_pow v S eb) J'
    rw [hea] at hA; rw [heb] at hB
    rw [hB, hA, hr v, rTrans_rTrans, rTrans_rTrans]
    set u := r v * P ^ eb v / P ^ ea v
    have hu : Valued.v u = 1 := by
      have hP : Valued.v P = exp (-1 : ℤ) := valued_π v
      simp only [u, map_div₀, map_mul, map_pow, hk v, hP]
      rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_sub, WithZero.exp_eq_one]
      have := toNat_sub_toNat_neg' (k v)
      simp only [nsmul_eq_mul, ea, eb]
      linarith
    have hsplit : algebraMap (v.adicCompletion F) (QuatV v a b) (r v) * complHom v a b (δ : QuatF F a b) *
        algebraMap (v.adicCompletion F) (QuatV v a b) ((P : v.adicCompletion F) ^ eb v) =
        algebraMap (v.adicCompletion F) (QuatV v a b) u *
          (algebraMap (v.adicCompletion F) (QuatV v a b) ((P : v.adicCompletion F) ^ ea v) *
            complHom v a b (δ : QuatF F a b)) := by
      rw [mul_assoc, ← Algebra.commutes ((P : v.adicCompletion F) ^ eb v), ← mul_assoc, ← map_mul, ← mul_assoc,
        ← map_mul]
      congr 2
      simp only [u]; field_simp
    have hPpow : ∀ e : ℕ, (((π v ^ e : v.adicCompletionIntegers F)) : v.adicCompletion F) = P ^ e := fun e => by
      push_cast; rfl
    rw [hPpow, hPpow, hsplit, ← rTrans_rTrans, rTrans_scalar_local_nf v _ hu]
  -- globalize
  obtain ⟨μa, hμa, hμa0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  obtain ⟨μb, hμb, hμb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔟
  have hA := algebraMap_mem_scaleIdeal hμa hnJ
  have hB := algebraMap_mem_scaleIdeal hμb hnJ'
  have hAn : μa * n ≠ 0 := mul_ne_zero hμa0 hn
  have hBn : μb * n' ≠ 0 := mul_ne_zero hμb0 hn'
  ext z
  rw [mem_idealSet_iff_local hO hBn hB]
  constructor
  · intro hz
    set y := z * ((δ⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)
    have hy : y ∈ idealSet (Gen.scaleIdeal 𝔞 J) := by
      rw [mem_idealSet_iff_local hO hAn hA]
      intro v
      have h1 := hz v
      rw [hloc v] at h1
      obtain ⟨t, ht, hzt⟩ := h1
      have : complHom v a b y = t := by
        rw [map_mul, ← hzt, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
      rw [this]; exact ht
    refine ⟨y, hy, ?_⟩
    simp only [y, mul_assoc, Units.inv_mul, mul_one]
  · rintro ⟨y, hy, rfl⟩ v
    rw [hloc v]
    exact ⟨_, Gen.complHom_mem_idealSet_localIdeal v hy, (map_mul _ _ _).symm⟩

end Glue

end QuadFormsKB.QuatOrder
