/-
# The covolume of a presented maximal order as a product of local volumes

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$, $\mathcal O$ an order of $D$.

* **`exists_integral_presentation`**: $\mathcal O = \bigoplus_i\mathfrak b_if_i$ with $f$ an $F$-basis of $D$ and $\mathfrak b_i$ nonzero **integral** ideals
  (rescale any Steinitz presentation, `exists_presentation_sub`; no basis of $\mathcal O$);
* **`mem_localOrder_iff_pres`**: then $\mathcal O_v = \bigoplus_i\mathfrak o_v\,\varpi^{c_v(\mathfrak b_i)}\iota_v(f_i)$ (`presBasisV`);
* **`tprod_norm_det_presBasisV`**: $\prod_v\|\det(\text{coordinates of }\varpi^{c_v(\mathfrak b_i)}f_i)\|_v = \big(|N\det(f)|\prod_iN\mathfrak b_i\big)^{-1}
  = \operatorname{covol}(f, \mathfrak b)^{-1}$ (product formula).

With `norm_det_coordQ_eq` this computes $\prod_v\|\det(\text{coordinates of }E_v)\|$ for local adapted bases $E_v$.

Source: Voight 2021, §§9.4–9.5 (local–global for lattices) [unverified locators]; the product formula
(`NumberField.FinitePlace.prod_eq_inv_abs_norm`).
-/
import QuadFormsKB.Tamagawa.TernaryLocalBasisNF
import QuadFormsKB.Tamagawa.TernaryGlueNF
import QuadFormsKB.Tamagawa.TernaryAssembly
import QuadFormsKB.Tamagawa.EichlerMassNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization
  QuadFormsKB.SphericalUnfold QuadFormsKB.IdeleClass

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-! ### An integral presentation -/

theorem exists_integral_scaling (𝔞 : FracIdeal F) :
    ∃ (d : 𝓞 F) (𝔟 : Ideal (𝓞 F)), d ≠ 0 ∧ 𝔟 ≠ ⊥ ∧
      ∀ x : F, x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) : Set F) ↔ ∃ r ∈ 𝔟, algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x := by
  obtain ⟨d, hd, hdx⟩ := (𝔞 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  set 𝔟 : Ideal (𝓞 F) := Submodule.comap (Algebra.linearMap (𝓞 F) F)
    (((𝔞 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).map (LinearMap.mulLeft (𝓞 F) (algebraMap (𝓞 F) F d)))
  have hmem : ∀ x : F, x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) : Set F) ↔
      ∃ r ∈ 𝔟, algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr⟩ := hdx x hx
      have hr' : algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x := by rw [hr, Algebra.smul_def]
      exact ⟨r, ⟨x, hx, hr'.symm⟩, hr'⟩
    · rintro ⟨r, ⟨y, hy, hyr⟩, hrx⟩
      have : y = x := by
        have h1 : algebraMap (𝓞 F) F d * y = algebraMap (𝓞 F) F d * x := by
          rw [← hrx]; exact hyr
        exact mul_left_cancel₀ hdF h1
      rw [← this]; exact hy
  refine ⟨d, 𝔟, hd0, ?_, hmem⟩
  have hne : ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ≠ ⊥ := by
    rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]; exact 𝔞.ne_zero
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨r, hr, hrx⟩ := (hmem x).1 hx
  intro hbot
  rw [hbot] at hr
  rw [(Submodule.mem_bot _).1 hr, map_zero] at hrx
  exact mul_ne_zero hdF hx0 hrx.symm

/-- **An integral presentation of an order**: $\mathcal O = \bigoplus_i\mathfrak b_if_i$ with $\mathfrak b_i$ nonzero integral ideals. -/
theorem exists_integral_presentation [IsTotallyReal F] (hO : IsOrder (𝓞 F) F O) :
    ∃ (f : Fin 4 → QuatF F a b) (𝔟 : Fin 4 → Ideal (𝓞 F)) (h𝔟 : ∀ i, 𝔟 i ≠ ⊥), LinearIndependent F f ∧
      ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i)) ξ ∧
        x = ∑ i, ξ i • f i := by
  obtain ⟨f₀, 𝔞, hli, hmem⟩ := Gen.exists_presentation_sub (M := Subalgebra.toSubmodule O) (isLattice_orderSub hO)
  choose d 𝔟 hd0 h𝔟 hsc using fun i => exists_integral_scaling (𝔞 i)
  have hdF : ∀ i, algebraMap (𝓞 F) F (d i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (hd0 i)
  refine ⟨fun i => (algebraMap (𝓞 F) F (d i))⁻¹ • f₀ i, 𝔟, h𝔟, ?_, fun x => ?_⟩
  · exact hli.units_smul (fun i => Units.mk0 _ (inv_ne_zero (hdF i)))
  · rw [show x ∈ (O : Set (QuatF F a b)) ↔ x ∈ Subalgebra.toSubmodule O from Iff.rfl, hmem]
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      refine ⟨fun i => algebraMap (𝓞 F) F (d i) * ξ i, fun i => ?_, ?_⟩
      · obtain ⟨r, hr, hrx⟩ := (hsc i (ξ i)).1 (hξ i)
        show _ ∈ (((𝔟 i : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : Set F)
        rw [SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
        exact ⟨r, hr, hrx⟩
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]
        congr 1
        show ξ i = (algebraMap (𝓞 F) F (d i) * ξ i) * (algebraMap (𝓞 F) F (d i))⁻¹
        rw [mul_comm (algebraMap (𝓞 F) F (d i)), mul_assoc, mul_inv_cancel₀ (hdF i), mul_one]
    · rintro ⟨ξ, hξ, rfl⟩
      refine ⟨fun i => (algebraMap (𝓞 F) F (d i))⁻¹ * ξ i, fun i => ?_, ?_⟩
      · have h1 := hξ i
        change ξ i ∈ (((𝔟 i : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : Set F) at h1
        rw [SetLike.mem_coe, FractionalIdeal.mem_coeIdeal] at h1
        obtain ⟨r, hr, hrx⟩ := h1
        refine (hsc i _).2 ⟨r, hr, ?_⟩
        rw [hrx, ← mul_assoc, mul_inv_cancel₀ (hdF i), one_mul]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]

/-! ### The local basis of a presentation -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The local basis of a presented order**: $\varpi^{c_v(\mathfrak b_i)}\iota_v(f_i)$. -/
def presBasisV (f : Fin 4 → QuatF F a b) (𝔟 : Fin 4 → Ideal (𝓞 F)) (i : Fin 4) : QuatV v a b :=
  (algebraMap 𝔬 Fv (π v) ^ cI v (𝔟 i)) • complHom v a b (f i)

variable {v}

theorem complHom_sum_smul (f : Fin 4 → QuatF F a b) (ξ : Fin 4 → F) :
    complHom v a b (∑ i, ξ i • f i) = ∑ i, algebraMap F Fv (ξ i) • complHom v a b (f i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, algebraMap_smul]

/-- **$\mathcal O_v = \bigoplus_i\mathfrak o_v\varpi^{c_v(\mathfrak b_i)}\iota_v(f_i)$** for an integral presentation. -/
theorem mem_localOrder_iff_pres {f : Fin 4 → QuatF F a b} {𝔟 : Fin 4 → Ideal (𝓞 F)} (h𝔟 : ∀ i, 𝔟 i ≠ ⊥)
    (hmem : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i)) ξ ∧
      x = ∑ i, ξ i • f i) (y : QuatV v a b) :
    y ∈ localOrder (v := v) a b O ↔ ∃ c : Fin 4 → 𝔬, y = ∑ i, (c i : Fv) • presBasisV v f 𝔟 i := by
  have hlat : ∀ (ξ : Fin 4 → F) (i : Fin 4), LatMem (fun i => Gen.idealUnit (𝔟 i) (h𝔟 i)) ξ →
      ∃ r ∈ 𝔟 i, algebraMap (𝓞 F) F r = ξ i := fun ξ i h => by
    have h1 := h i
    change ξ i ∈ (((𝔟 i : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : Set F) at h1
    rw [SetLike.mem_coe, FractionalIdeal.mem_coeIdeal] at h1
    exact h1
  constructor
  · intro hy
    change y ∈ Submodule.span 𝔬 (complHom v a b '' (O : Set (QuatF F a b))) at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨ξ, hξ, rfl⟩ := (hmem x).1 hx
      choose r hr hrξ using fun i => hlat ξ i hξ
      have hπ : ∀ i, ι v (r i) ∈ Ideal.span {π v ^ cI v (𝔟 i)} := fun i =>
        (map_ι_eq_span v (h𝔟 i)) ▸ Ideal.mem_map_of_mem _ (hr i)
      choose t ht using fun i => Ideal.mem_span_singleton'.1 (hπ i)
      refine ⟨t, ?_⟩
      rw [complHom_sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [presBasisV, smul_smul, ← hrξ i]
      congr 1
      rw [show algebraMap F Fv (algebraMap (𝓞 F) F (r i)) = algebraMap 𝔬 Fv (ι v (r i)) from rfl, ← ht i,
        map_mul, map_pow]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hz
      refine ⟨c + d, ?_⟩
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Subring.coe_add, add_smul]
    | smul s x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      refine ⟨s • c, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← algebraMap_smul Fv s, smul_smul, Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
      rfl
  · rintro ⟨c, rfl⟩
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ ?_ (c i)
    have hgen : π v ^ cI v (𝔟 i) ∈ Ideal.map (ι v) (𝔟 i) :=
      (map_ι_eq_span v (h𝔟 i)) ▸ Ideal.mem_span_singleton_self _
    unfold presBasisV
    rw [← map_pow]
    refine Submodule.span_induction (p := fun s _ => (algebraMap 𝔬 Fv s) • complHom v a b (f i) ∈
      localOrder (v := v) a b O) ?_ ?_ ?_ ?_ hgen
    · rintro _ ⟨r, hr, rfl⟩
      have hrf : algebraMap (𝓞 F) F r • f i ∈ (O : Set (QuatF F a b)) := by
        refine (hmem _).2 ⟨Pi.single i (algebraMap (𝓞 F) F r), fun j => ?_, ?_⟩
        · change (Pi.single i (algebraMap (𝓞 F) F r) : Fin 4 → F) j ∈
            (((𝔟 j : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) : Set F)
          by_cases hj : j = i
          · subst hj
            rw [Pi.single_eq_same, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
            exact ⟨r, hr, rfl⟩
          · rw [Pi.single_eq_of_ne hj]
            exact Submodule.zero_mem ((((𝔟 j : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)) : Submodule (𝓞 F) F)
        · rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
            Pi.single_eq_same]
      have h1 := mem_localOrder_of_mem (v := v) a b hrf
      rw [map_smul, ← algebraMap_smul Fv] at h1
      exact h1
    · simp only [map_zero, zero_smul]; exact Subalgebra.zero_mem _
    · intro x z _ _ hx hz
      rw [map_add, add_smul]; exact Subalgebra.add_mem _ hx hz
    · intro s x _ hx
      rw [smul_eq_mul, map_mul, mul_smul]
      exact Subalgebra.smul_mem _ hx s

theorem coordQ_presBasisV (f : Fin 4 → QuatF F a b) (𝔟 : Fin 4 → Ideal (𝓞 F)) :
    coordQ (presBasisV v f 𝔟) = (coordMat f).map (algebraMap F Fv) *
      Matrix.diagonal (fun i => algebraMap 𝔬 Fv (π v) ^ cI v (𝔟 i)) :=
  coordQ_smul_complHom f _

theorem det_coordQ_presBasisV (f : Fin 4 → QuatF F a b) (𝔟 : Fin 4 → Ideal (𝓞 F)) :
    (coordQ (presBasisV v f 𝔟)).det =
      algebraMap F Fv (coordMat f).det * ∏ i, algebraMap 𝔬 Fv (π v) ^ cI v (𝔟 i) := by
  rw [coordQ_presBasisV, det_mul, det_diagonal, RingHom.map_det, RingHom.mapMatrix_apply]

theorem norm_algebraMap_pi : ‖algebraMap 𝔬 Fv (π v)‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have hπ := irreducible_π v
  have := norm_coe_of_pow_dvd v (x := π v) (e := 1) (by simp)
    (by rw [pow_succ, pow_one]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one
      ((mul_dvd_mul_iff_left hπ.ne_zero).1 (by simpa using h))))
  rw [pow_one, q_completion] at this; exact this

theorem norm_det_coordQ_presBasisV (f : Fin 4 → QuatF F a b) (𝔟 : Fin 4 → Ideal (𝓞 F)) :
    ‖(coordQ (presBasisV v f 𝔟)).det‖ =
      absV v (coordMat f).det * ∏ i, (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ cI v (𝔟 i))⁻¹ := by
  rw [det_coordQ_presBasisV, norm_mul, norm_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_pow, norm_algebraMap_pi, inv_pow]

end Local

/-- **The product formula for the covolume of a presented order:**
$\prod_v\|\det(\text{coordinates of }\varpi^{c_v(\mathfrak b_i)}f_i)\|_v = (|N\det f|\prod_iN\mathfrak b_i)^{-1}$. -/
theorem tprod_norm_det_presBasisV {f : Fin 4 → QuatF F a b} {𝔟 : Fin 4 → Ideal (𝓞 F)} (h𝔟 : ∀ i, 𝔟 i ≠ ⊥)
    (hli : LinearIndependent F f) :
    ∏' v, ‖(coordQ (presBasisV v f 𝔟)).det‖ =
      (|((Algebra.norm ℚ (coordMat f).det : ℚ) : ℝ)| * ∏ i, (Ideal.absNorm (𝔟 i) : ℝ))⁻¹ := by
  classical
  have hdet0 : (coordMat f).det ≠ 0 := det_coordMat_ne_zero hli
  choose n hn hn0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (h𝔟 i)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (absV_hasFiniteMulSupport hdet0).toFinset ∪
    Finset.univ.biUnion fun i => Gen.primeSupport (hn0 i)
  have hS1 : ∀ v, absV v (coordMat f).det ≠ 1 → v ∈ S := fun v hv =>
    Finset.mem_union_left _ ((absV_hasFiniteMulSupport hdet0).mem_toFinset.2 hv)
  have hS2 : ∀ v i, v ∉ S → cI v (𝔟 i) = 0 := fun v i hv =>
    Gen.cI_eq_zero_of_mem_not_mem (h𝔟 i) (hn i) fun h => hv (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (Gen.mem_primeSupport (hn0 i)).2 h⟩))
  have hone : ∀ v ∉ S, ‖(coordQ (presBasisV v f 𝔟)).det‖ = 1 := fun v hv => by
    rw [norm_det_coordQ_presBasisV]
    have h1 : absV v (coordMat f).det = 1 := by by_contra h; exact hv (hS1 v h)
    rw [h1, one_mul]
    exact Finset.prod_eq_one fun i _ => by rw [hS2 v i hv, pow_zero, inv_one]
  rw [tprod_eq_prod hone]
  simp_rw [norm_det_coordQ_presBasisV]
  rw [Finset.prod_mul_distrib, Finset.prod_comm, prod_absV_of_subset hdet0 hS1, mul_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_inv_distrib, Gen.absNorm_eq_prod (h𝔟 i) (hn0 i) (hn i)]
  congr 1
  push_cast
  refine (Finset.prod_subset (fun v hv => Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hv⟩)) fun v _ hv => ?_).symm
  rw [Gen.cI_eq_zero_of_mem_not_mem (h𝔟 i) (hn i) fun h => hv ((Gen.mem_primeSupport (hn0 i)).2 h), pow_zero]

end QuadFormsKB.QuatOrder
