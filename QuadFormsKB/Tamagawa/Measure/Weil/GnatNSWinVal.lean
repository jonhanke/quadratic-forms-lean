/-
# Valuations at $w\mid v$ and coordinate levels on $E = F_v[\delta]$

**Layer:** a number field $F$, a finite place $v$, a finite extension $K/F$ of number fields and the places $w\mid v$ of $K$;
for the quadratic case $K = F(\delta)$, $\delta^2 = d$, with basis $(1,\delta)$, the algebra $E = F_v[\delta]$ = `QE` and its
local maps $E\to K_w$ (`quadLocalHom`).

* `unifF v` $\in\mathcal O_F$ with $|{\tt unifF}|_v = q^{-1}$ (a global uniformizer at $v$), and the ramification exponent
  `ramE v w` $= e_w$ with $|\varphi_w(\varpi)|_w = q_w^{-e_w}$; **`valued_localRingHom_exp`**: $|x|_v = q^{-k}$ implies
  $|\varphi_w(x)|_w = q_w^{-e_wk}$ ($k\in\mathbb Z$), so $s_w = e_ws_v$, $e_\alpha(w) = e_we_a(v)$ (`sExp_over`, `eExp_over`).
* `CL k z` (coordinate level: $z = x + y\delta$ with $|x|_v, |y|_v\le q^{-k}$) and `PL k z` (place level:
  $|\varphi_w(z)|_w\le q_w^{-e_wk}$ for every $w\mid v$). **`CL.pl`**: `CL k z → PL k z`; **`exists_pl_cl`**: there is
  $c_0$ with `PL k z → CL (k - c₀) z` for all $k$, $z$ (compactness of $\prod_w\mathcal O_w$ in the coordinates of $(1,\delta)$).

These are the bookkeeping tools of the window argument that compares $\varphi(Y^{(M)})$ with $K_N$.

Source: Weil 1982, §2.2-2.3 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSDeep

open MeasureTheory Set Function Topology NumberField IsDedekindDomain WithZero
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Quat QuadFormsKB.Quat.Gnat

section RamE

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- A global uniformizer at $v$: $\varpi\in\mathcal O_F$ with $v(\varpi) = 1$. -/
def unifF : 𝓞 F := v.intValuation_exists_uniformizer.choose

theorem valued_unifF : Valued.v (algebraMap F Fv (unifF v : F)) = exp (-1 : ℤ) := by
  rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_exists_uniformizer.choose_spec

theorem unifF_coe_ne_zero : (unifF v : F) ≠ 0 := by
  intro h; have := valued_unifF v; rw [h, map_zero, map_zero] at this; exact exp_ne_zero this.symm

theorem unifF_ne_zero : unifF v ≠ 0 := fun h => unifF_coe_ne_zero v (by rw [h]; rfl)

theorem algebraMap_unifF_ne_zero : algebraMap (𝓞 F) (𝓞 K) (unifF v) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  exact unifF_ne_zero v

/-- **The ramification exponent** $e_w$ of $w$ over $v$: $|\varpi|_w = q_w^{-e_w}$. -/
def ramE (w : HeightOneSpectrum (𝓞 K)) : ℕ :=
  eExp (algebraMap (𝓞 F) (𝓞 K) (unifF v)) (algebraMap_unifF_ne_zero v) w

theorem localRingHom_unifF (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    localRingHom v w h (algebraMap F Fv (unifF v : F)) =
      algebraMap K (w.adicCompletion K) ((algebraMap (𝓞 F) (𝓞 K) (unifF v) : 𝓞 K) : K) := by
  rw [show algebraMap F Fv (unifF v : F) = ((unifF v : F) : Fv) from rfl, localRingHom_algebraMap]
  congr 1

theorem valued_localRingHom_unifF (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    Valued.v (localRingHom v w h (algebraMap F Fv (unifF v : F))) = exp (-(ramE v w : ℤ)) := by
  rw [localRingHom_unifF]
  exact valued_eExp _ _ w

/-- **Valuations at $w\mid v$**: $|x|_v = q^{-k}$ implies $|\varphi_w(x)|_w = q_w^{-e_wk}$. -/
theorem valued_localRingHom_exp (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) {x : Fv} {k : ℤ}
    (hx : Valued.v x = exp (-k)) : Valued.v (localRingHom v w h x) = exp (-((ramE v w : ℤ) * k)) := by
  set s := algebraMap F Fv (unifF v : F)
  have hs0 : s ≠ 0 := by
    intro h0; have := valued_unifF v; rw [show algebraMap F Fv (unifF v : F) = s from rfl, h0, map_zero] at this
    exact exp_ne_zero this.symm
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact exp_ne_zero hx.symm
  set y := x * s ^ (-k) with hy
  have hyv : Valued.v y = 1 := by
    rw [hy, map_mul, map_zpow₀, hx, valued_unifF, ← exp_zsmul, ← exp_add]; simp
  have hφy : Valued.v (localRingHom v w h y) = 1 := (valued_localRingHom_eq_one_iff w h y).2 hyv
  have hxy : x = y * s ^ k := by
    rw [hy, mul_assoc, ← zpow_add₀ hs0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxy, map_mul, map_zpow₀, map_mul, map_zpow₀, hφy, one_mul, valued_localRingHom_unifF, ← exp_zsmul]
  congr 1; simp; ring

theorem one_le_ramE (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) : 1 ≤ ramE v w := by
  by_contra h0
  push Not at h0
  have h1 := valued_localRingHom_unifF v w h
  rw [Nat.lt_one_iff.1 h0, Nat.cast_zero, neg_zero, exp_zero] at h1
  have h2 := (valued_localRingHom_eq_one_iff w h _).1 h1
  rw [valued_unifF] at h2
  rw [← exp_zero, exp_inj] at h2
  norm_num at h2

/-- $|x|_v\le q^{-k}$ implies $|\varphi_w(x)|_w\le q_w^{-e_wk}$. -/
theorem valued_localRingHom_le (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) {x : Fv} {k : ℤ}
    (hx : Valued.v x ≤ exp (-k)) : Valued.v (localRingHom v w h x) ≤ exp (-((ramE v w : ℤ) * k)) := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero, map_zero]; exact zero_le
  obtain ⟨j, hj⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hx0
  have hj' : Valued.v x = exp (-(-j)) := by rw [neg_neg]; exact hj
  rw [valued_localRingHom_exp v w h hj', exp_le_exp]
  rw [hj, exp_le_exp] at hx
  have he : (0 : ℤ) ≤ ramE v w := Nat.cast_nonneg _
  nlinarith

/-- $|\varphi_w(x)|_w\le q_w^{-e_wk}$ implies $|x|_v\le q^{-k}$ (the converse of `valued_localRingHom_le`). -/
theorem valued_le_of_localRingHom (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) {x : Fv} {k : ℤ}
    (hx : Valued.v (localRingHom v w h x) ≤ exp (-((ramE v w : ℤ) * k))) : Valued.v x ≤ exp (-k) := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]; exact zero_le
  obtain ⟨j, hj⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v hx0
  have hj' : Valued.v x = exp (-(-j)) := by rw [neg_neg]; exact hj
  rw [valued_localRingHom_exp v w h hj', exp_le_exp] at hx
  rw [hj, exp_le_exp]
  have he : (1 : ℤ) ≤ ramE v w := by exact_mod_cast one_le_ramE v w h
  nlinarith

theorem sExp_over (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    sExp w = ramE v w * sExp v := by
  have h1 := valued_localRingHom_exp v w h (valued_two_eq v)
  rw [map_ofNat, valued_two_eq, exp_inj, neg_inj] at h1
  exact_mod_cast h1

theorem eExp_over {a : 𝓞 F} {α : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (ha : a ≠ 0) (hα0 : α ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (h : underPlace (k := F) w = v) :
    eExp α hα0 w = ramE v w * eExp a ha v := by
  have h1 := valued_localRingHom_exp v w h (valued_eExp a ha v)
  rw [show algebraMap F Fv (a : F) = ((a : F) : Fv) from rfl, localRingHom_algebraMap, ← hα] at h1
  have h2 := valued_eExp α hα0 w
  change Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = _ at h1
  rw [h1, exp_inj, neg_inj] at h2
  exact_mod_cast h2.symm

end RamE

/-! ### Coordinate and place levels on $E = F_v[\delta]$ -/

section Levels

variable {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "E" => QE (algebraMap F (v.adicCompletion F) (d : F))

/-- **Coordinate level**: $z = x + y\delta$ with $|x|_v, |y|_v\le q^{-k}$. -/
def CL (k : ℤ) (z : E) : Prop := Valued.v z.re ≤ exp (-k) ∧ Valued.v z.im ≤ exp (-k)

/-- The local map $E\to K_w$ (`quadLocalHom`), with $E$ written as `QE (algebraMap F Fv d)`. -/
def qlh (w : PlaceSet (K := K) v) : E →+* w.1.adicCompletion K := quadLocalHom hb₁ v w.1 w.2

theorem qlh_apply (w : PlaceSet (K := K) v) (z : E) : qlh hb₁ v w z = quadLocalHom hb₁ v w.1 w.2 z := rfl

/-- **Place level**: $|\varphi_w(z)|_w\le q_w^{-e_wk}$ for every $w\mid v$. -/
def PL (k : ℤ) (z : E) : Prop :=
  ∀ w : PlaceSet (K := K) v, Valued.v (qlh hb₁ v w z) ≤ exp (-((ramE v w.1 : ℤ) * k))

variable {v}

theorem qlh_mul (w : PlaceSet (K := K) v) (z z' : E) :
    qlh hb₁ v w (z * z') = qlh hb₁ v w z * qlh hb₁ v w z' :=
  map_mul (qlh hb₁ v w) z z'

theorem qlh_add (w : PlaceSet (K := K) v) (z z' : E) :
    qlh hb₁ v w (z + z') = qlh hb₁ v w z + qlh hb₁ v w z' :=
  map_add (qlh hb₁ v w) z z'

theorem qlh_sub (w : PlaceSet (K := K) v) (z z' : E) :
    qlh hb₁ v w (z - z') = qlh hb₁ v w z - qlh hb₁ v w z' :=
  map_sub (qlh hb₁ v w) z z'

theorem qlh_one (w : PlaceSet (K := K) v) : qlh hb₁ v w (1 : E) = 1 :=
  map_one (qlh hb₁ v w)

theorem qlh_algebraMap (w : PlaceSet (K := K) v) (c : Fv) :
    qlh hb₁ v w (algebraMap Fv E c) = localRingHom v w.1 w.2 c :=
  quadLocalHom_algebraMap hb₁ v w.1 w.2 c

theorem valued_d_le_one : Valued.v (algebraMap F Fv (d : F)) ≤ 1 := valued_algebraMap_le_one d v

theorem CL.mono {k k' : ℤ} {z : E} (h : CL v k z) (hk : k' ≤ k) : CL v k' z :=
  ⟨h.1.trans (exp_le_exp.2 (by omega)), h.2.trans (exp_le_exp.2 (by omega))⟩

theorem CL.add {k : ℤ} {z z' : E} (h : CL v k z) (h' : CL v k z') : CL v k (z + z') :=
  ⟨(Valuation.map_add _ _ _).trans (max_le h.1 h'.1), (Valuation.map_add _ _ _).trans (max_le h.2 h'.2)⟩

theorem CL.neg {k : ℤ} {z : E} (h : CL v k z) : CL v k (-z) := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_neg, Valuation.map_neg]; exact h.1
  · rw [QuadraticAlgebra.im_neg, Valuation.map_neg]; exact h.2

theorem CL.sub {k : ℤ} {z z' : E} (h : CL v k z) (h' : CL v k z') : CL v k (z - z') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem CL.zero (k : ℤ) : CL v k (0 : E) := by
  refine ⟨?_, ?_⟩ <;> simp

theorem CL.mul {k k' : ℤ} {z z' : E} (h : CL v k z) (h' : CL v k' z') : CL v (k + k') (z * z') := by
  have hd := valued_d_le_one (d := d) (v := v)
  have e : exp (-(k + k')) = exp (-k) * exp (-k') := by rw [← exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_mul]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul, e]; exact mul_le_mul' h.1 h'.1
    · rw [map_mul, map_mul, e]
      calc Valued.v (algebraMap F Fv (d : F)) * Valued.v z.im * Valued.v z'.im ≤ 1 * exp (-k) * exp (-k') :=
            mul_le_mul' (mul_le_mul' hd h.2) h'.2
        _ = _ := by rw [one_mul]
  · rw [QuadraticAlgebra.im_mul]
    simp only [zero_mul, add_zero]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul, e]; exact mul_le_mul' h.1 h'.2
    · rw [map_mul, e]; exact mul_le_mul' h.2 h'.1

theorem CL.smul {k j : ℤ} {c : Fv} (hc : Valued.v c ≤ exp (-j)) {z : E} (h : CL v k z) :
    CL v (j + k) (algebraMap Fv E c * z) := by
  have e : exp (-(j + k)) = exp (-j) * exp (-k) := by rw [← exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_mul]; simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      zero_mul, mul_zero, add_zero]
    rw [map_mul, e]; exact mul_le_mul' hc h.1
  · rw [QuadraticAlgebra.im_mul]; simp only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
      zero_mul, add_zero]
    rw [map_mul, e]; exact mul_le_mul' hc h.2

theorem CL.algebraMap {k : ℤ} {c : Fv} (hc : Valued.v c ≤ exp (-k)) : CL v k (algebraMap Fv E c) := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.algebraMap_re]; exact hc
  · rw [QuadraticAlgebra.algebraMap_im, map_zero]; exact zero_le

theorem CL_one : CL v 0 (1 : E) := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_one, map_one, neg_zero, exp_zero]
  · rw [QuadraticAlgebra.im_one, map_zero]; exact zero_le

theorem CL.star {k : ℤ} {z : E} (h : CL v k z) : CL v k (star z) := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticAlgebra.re_star, zero_mul, add_zero]; exact h.1
  · rw [QuadraticAlgebra.im_star, Valuation.map_neg]; exact h.2

include hb₀ in
/-- **Coordinate level gives place level.** -/
theorem pl_of_cl {k : ℤ} {z : E} (h : CL v k z) : PL hb₁ v k z := by
  intro w
  have hint := isIntegral_basis hb₀ hb₁
  have hδ := valued_basis_le_one bK hint w.1 1
  change Valued.v (localRingHom v w.1 w.2 z.re + ((bK 1 : K) : w.1.adicCompletion K) *
    localRingHom v w.1 w.2 z.im) ≤ _
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · exact valued_localRingHom_le v w.1 w.2 h.1
  · rw [map_mul]
    calc _ ≤ 1 * exp (-((ramE v w.1 : ℤ) * k)) := mul_le_mul' hδ (valued_localRingHom_le v w.1 w.2 h.2)
      _ = _ := one_mul _

/-- Scaling by the uniformizer shifts the place level. -/
theorem PL.unif_mul {k : ℤ} {z : E} (h : PL hb₁ v k z) (j : ℤ) :
    PL hb₁ v (k + j) (algebraMap Fv E (algebraMap F Fv (unifF v : F) ^ j) * z) := by
  intro w
  rw [qlh_mul, qlh_algebraMap, Valuation.map_mul, map_zpow₀, map_zpow₀,
    valued_localRingHom_unifF, ← exp_zsmul]
  calc exp (j • -(ramE v w.1 : ℤ)) * Valued.v (qlh hb₁ v w z) ≤
        exp (j • -(ramE v w.1 : ℤ)) * exp (-((ramE v w.1 : ℤ) * k)) := mul_le_mul' le_rfl (h w)
    _ = _ := by rw [← exp_add]; congr 1; simp; ring

include hb₀ in
/-- **Place level gives coordinate level up to a fixed loss $c_0$** (compactness of $\prod_{w\mid v}\mathcal O_w$). -/
theorem exists_pl_cl : ∃ c₀ : ℕ, ∀ (k : ℤ) (z : E), PL hb₁ v k z → CL v (k - c₀) z := by
  -- the coordinates of the preimage of `∏ 𝒪_w` are bounded
  set B : Set (Fin 2 → Fv) := (localPiCLE bK v).symm '' intPlace (K := K) v
  have hB : IsCompact B := by
    refine IsCompact.image ?_ (localPiCLE bK v).symm.continuous
    rw [intPlace_eq_pi]
    exact isCompact_univ_pi fun w => QuadFormsKB.Analysis.isCompact_latticeV w.1 0
  have hopen : ∀ j : ℤ, IsOpen (QuadFormsKB.Analysis.latticeV v j : Set Fv) := fun j => by
    rw [QuadFormsKB.Analysis.coe_latticeV]
    refine IsUltrametricDist.isOpen_closedBall _ ?_
    rw [Ne, norm_eq_zero]
    exact zpow_ne_zero _ (QuadFormsKB.HN.ϖ_ne_zero v)
  obtain ⟨j, hj⟩ := hB.elim_directed_cover
    (fun j : ℕ => Set.pi Set.univ fun _ : Fin 2 => (QuadFormsKB.Analysis.latticeV v (-(j : ℤ)) : Set Fv))
    (fun j => isOpen_set_pi Set.finite_univ fun _ _ => hopen _)
    (by
      intro c _
      have : ∀ i : Fin 2, ∃ j : ℕ, Valued.v (c i) ≤ exp (j : ℤ) := by
        intro i
        by_cases h0 : c i = 0
        · exact ⟨0, by rw [h0, map_zero]; exact zero_le⟩
        obtain ⟨m, hm⟩ := QuadFormsKB.Lattices.exists_valued_eq_exp v h0
        exact ⟨m.toNat, by rw [hm, exp_le_exp]; omega⟩
      choose J hJ using this
      refine Set.mem_iUnion.2 ⟨J 0 + J 1, fun i _ => ?_⟩
      rw [SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV, neg_neg]
      refine (hJ i).trans (exp_le_exp.2 ?_)
      fin_cases i <;> simp <;> omega)
    (by
      intro i j
      refine ⟨max i j, fun c hc l _ => ?_, fun c hc l _ => ?_⟩
      · have := hc l (Set.mem_univ _)
        rw [SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV] at this ⊢
        exact this.trans (exp_le_exp.2 (by omega))
      · have := hc l (Set.mem_univ _)
        rw [SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV] at this ⊢
        exact this.trans (exp_le_exp.2 (by omega)))
  refine ⟨j, fun k z hz => ?_⟩
  set s := algebraMap F Fv (unifF v : F)
  have hs0 : s ≠ 0 := by
    intro h0; have := valued_unifF v; rw [show algebraMap F Fv (unifF v : F) = s from rfl, h0, map_zero] at this
    exact exp_ne_zero this.symm
  set z' := algebraMap Fv E (s ^ (-k)) * z with hz'
  have h0 : PL hb₁ v 0 z' := by
    have := hz.unif_mul hb₁ (-k)
    rwa [add_neg_cancel] at this
  have hmem : (![z'.re, z'.im] : Fin 2 → Fv) ∈ B := by
    refine ⟨localPiCLE bK v ![z'.re, z'.im], fun w => ?_, (localPiCLE bK v).symm_apply_apply _⟩
    rw [localPiCLE_apply, ← quadLocalHom_eq_localPi hb₀ hb₁, ← qlh_apply]
    have := h0 w
    rwa [mul_zero, neg_zero, exp_zero] at this
  have hb := hj hmem
  have hre := hb 0 (Set.mem_univ _)
  have him := hb 1 (Set.mem_univ _)
  rw [SetLike.mem_coe, QuadFormsKB.Analysis.mem_latticeV, neg_neg] at hre him
  have hcl : CL v (-(j : ℤ)) z' := ⟨by simpa using hre, by simpa using him⟩
  have hsk : Valued.v (s ^ k) ≤ exp (-k) := by
    rw [map_zpow₀, valued_unifF, ← exp_zsmul]; simp
  have := hcl.smul hsk
  have e : algebraMap Fv E (s ^ k) * z' = z := by
    rw [hz', ← mul_assoc, ← map_mul, ← zpow_add₀ hs0, add_neg_cancel, zpow_zero, map_one, one_mul]
  rw [e] at this
  convert this using 1; ring

end Levels

end QuadFormsKB.Tamagawa.Measure.Weil
