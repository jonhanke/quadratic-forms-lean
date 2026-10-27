/-
# Square discriminant: the adelic isomorphism $\Phi : P\cong SO(D,\operatorname{nrd})(\mathbb A)$ and the global points


**Layer:** as `GnatSqAdelic`: $F$ a number field, $a, b\in\mathcal O_F\setminus0$, $G^\natural$ = `gnatSqO`, any signature.

**Defines/proves**
* `mkFinUnit`, `mkInfUnit`, `mkAdeleUnit`: units of $D\otimes\mathbb A$ from local units (integral at almost all places);
  `nrdUnit_eq_of_local`, `quatUnits_eq_of_local`: an idele / a unit of $D\otimes\mathbb A$ is determined by its components;
* **`sqAdele_surjective`**: $G^\natural(\mathbb A)\to SO(V)(\mathbb A)$ is onto;
* **`ker_sqAdele`**: its kernel is the centre $Z = \{(u,u,u^2)\}$ (via the kernel of $D_{\mathbb A}^\times\to SO(D^0)(\mathbb A)$,
  `conjAdele_eq_one_iff`);
* **`sqPEquiv : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele (qSq a b)`** (open mapping theorem);
* global points: `sqF`, **`sqAdele_diag`**, **`map_gamP_sqPEquiv`**: $\Phi(\pi(\Gamma)) = $ `GammaSOAdele (qSq a b)`.

Source: Weil 1982, §3.7, p. 65 [unverified page]; §2.4, p. 23.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqAdelic

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology
  Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F]

/-! ### Assembling units of $D\otimes\mathbb A$ from local units -/

section Assemble

variable (A B : F)

/-- A unit of $D\otimes\mathbb A_f$ with prescribed components, integral at almost all places. -/
def mkFinUnit (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV A B v)ˣ)
    (hev : ∀ᶠ v in cofinite, β v ∈ lamLocUnits A B v) : (QuatFin A B)ˣ :=
  let x : QuatFin A B :=
    ⟨mkAF (fun v => (β v : QuatV A B v).re) (by filter_upwards [hev] with v hv; exact hv.1.1),
     mkAF (fun v => (β v : QuatV A B v).imI) (by filter_upwards [hev] with v hv; exact hv.1.2.1),
     mkAF (fun v => (β v : QuatV A B v).imJ) (by filter_upwards [hev] with v hv; exact hv.1.2.2.1),
     mkAF (fun v => (β v : QuatV A B v).imK) (by filter_upwards [hev] with v hv; exact hv.1.2.2.2)⟩
  let y : QuatFin A B :=
    ⟨mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).re) (by filter_upwards [hev] with v hv; exact hv.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imI) (by filter_upwards [hev] with v hv; exact hv.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imJ)
       (by filter_upwards [hev] with v hv; exact hv.2.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imK)
       (by filter_upwards [hev] with v hv; exact hv.2.2.2.2)⟩
  have hx : ∀ v, projQ _ _ v x = β v := fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hy : ∀ v, projQ _ _ v y = (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v) :=
    fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  ⟨x, y, projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.mul_inv],
    projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.inv_mul]⟩

theorem unitAtQ_mkFinUnit (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV A B v)ˣ)
    (hev : ∀ᶠ v in cofinite, β v ∈ lamLocUnits A B v) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtQ A B v (mkFinUnit A B β hev) = β v :=
  Units.ext (QuaternionAlgebra.ext rfl rfl rfl rfl)

/-- A unit of $D\otimes F_\infty$ with prescribed components. -/
def mkInfUnit (βR : ∀ w : {w : InfinitePlace F // w.IsReal}, (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ)
    (βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ) :
    (QuatInf A B)ˣ :=
  let x : QuatInf A B :=
    ⟨((fun w => (βR w).val.re), (fun w => (βC w).val.re)),
     ((fun w => (βR w).val.imI), (fun w => (βC w).val.imI)),
     ((fun w => (βR w).val.imJ), (fun w => (βC w).val.imJ)),
     ((fun w => (βR w).val.imK), (fun w => (βC w).val.imK))⟩
  let y : QuatInf A B :=
    ⟨((fun w => ((βR w)⁻¹).val.re), (fun w => ((βC w)⁻¹).val.re)),
     ((fun w => ((βR w)⁻¹).val.imI), (fun w => ((βC w)⁻¹).val.imI)),
     ((fun w => ((βR w)⁻¹).val.imJ), (fun w => ((βC w)⁻¹).val.imJ)),
     ((fun w => ((βR w)⁻¹).val.imK), (fun w => ((βC w)⁻¹).val.imK))⟩
  have hxR : ∀ w, projR _ _ w x = βR w := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hxC : ∀ w, projC _ _ w x = βC w := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hyR : ∀ w, projR _ _ w y = ((βR w)⁻¹).val := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hyC : ∀ w, projC _ _ w y = ((βC w)⁻¹).val := fun w => QuaternionAlgebra.ext rfl rfl rfl rfl
  ⟨x, y, quatInf_ext _ _ (fun w => by rw [map_mul, map_one, hxR, hyR, Units.mul_inv])
      (fun w => by rw [map_mul, map_one, hxC, hyC, Units.mul_inv]),
    quatInf_ext _ _ (fun w => by rw [map_mul, map_one, hxR, hyR, Units.inv_mul])
      (fun w => by rw [map_mul, map_one, hxC, hyC, Units.inv_mul])⟩

/-- A unit of $D\otimes\mathbb A$ with prescribed local components. -/
def mkAdeleUnit
    (βR : ∀ w : {w : InfinitePlace F // w.IsReal}, (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ)
    (βC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ)
    (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV A B v)ˣ) (hev : ∀ᶠ v in cofinite, β v ∈ lamLocUnits A B v) :
    (QuatAdele A B)ˣ :=
  (quatUnitsEquiv A B).symm (mkInfUnit A B βR βC, mkFinUnit A B β hev)

variable {A B}

theorem unitAtA_mkAdeleUnit (βR βC β hev) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtA A B v (mkAdeleUnit A B βR βC β hev) = β v := by
  rw [unitAtA_eq, mkAdeleUnit, ContinuousMulEquiv.apply_symm_apply, unitAtQ_mkFinUnit]

theorem unitAtR_mkAdeleUnit (βR βC β hev) (w : {w : InfinitePlace F // w.IsReal}) :
    unitAtR A B w (mkAdeleUnit A B βR βC β hev) = βR w := by
  apply Units.ext
  change projR A B w ((quatUnitsEquiv A B ((quatUnitsEquiv A B).symm _)).1 : QuatInf A B) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact QuaternionAlgebra.ext rfl rfl rfl rfl

theorem unitAtC_mkAdeleUnit (βR βC β hev) (w : {w : InfinitePlace F // w.IsComplex}) :
    unitAtC A B w (mkAdeleUnit A B βR βC β hev) = βC w := by
  apply Units.ext
  change projC A B w ((quatUnitsEquiv A B ((quatUnitsEquiv A B).symm _)).1 : QuatInf A B) = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact QuaternionAlgebra.ext rfl rfl rfl rfl

/-- **An idele norm is determined by the local reduced norms.** -/
theorem nrdUnit_eq_of_local {x y : (QuatAdele A B)ˣ}
    (hv : ∀ v, nrd ((unitAtA A B v x : (QuatV A B v)ˣ) : QuatV A B v) =
      nrd ((unitAtA A B v y : (QuatV A B v)ˣ) : QuatV A B v))
    (hR : ∀ w : {w : InfinitePlace F // w.IsReal},
      nrd ((unitAtR A B w x : (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ) :
        ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B]) =
      nrd ((unitAtR A B w y : (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ) :
        ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B]))
    (hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      nrd ((unitAtC A B w x : (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ) : ℍ[ℂ, w.1.embedding A, w.1.embedding B]) =
      nrd ((unitAtC A B w y : (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ) : ℍ[ℂ, w.1.embedding A, w.1.embedding B])) :
    nrdUnit x = nrdUnit y := by
  apply Units.ext
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) (Subtype.ext (funext fun v => ?_))
  · rw [← nrd_unitAtR, ← nrd_unitAtR, hR]
  · rw [← nrd_unitAtC, ← nrd_unitAtC, hC]
  · change ((nrdUnit x : (Adeles F)ˣ) : Adeles F).2 v = ((nrdUnit y : (Adeles F)ˣ) : Adeles F).2 v
    rw [← nrd_unitAtA, ← nrd_unitAtA, hv]

/-- **A unit of $D\otimes\mathbb A$ is determined by its local components.** -/
theorem quatUnits_eq_of_local {x y : (QuatAdele A B)ˣ} (hv : ∀ v, unitAtA A B v x = unitAtA A B v y)
    (hR : ∀ w, unitAtR A B w x = unitAtR A B w y) (hC : ∀ w, unitAtC A B w x = unitAtC A B w y) : x = y := by
  apply (quatUnitsEquiv A B).injective
  refine Prod.ext (Units.ext (quatInf_ext _ _ (fun w => congrArg Units.val (hR w)) fun w => congrArg Units.val (hC w)))
    (Units.ext (projQ_injective _ _ fun v => congrArg Units.val (hv v)))

end Assemble

/-! ### Scalars and the kernel -/

section Kernel

/-- The diagonal scalar pair $(r, r)$. -/
def scalarPair {K : Type*} [Field K] {A B : K} (r : Kˣ) : sqPair A B :=
  ⟨(Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r, Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r), rfl⟩

theorem scalarPair_mul_fst {K : Type*} [Field K] {A B : K} (r : Kˣ) (p : sqPair A B) :
    ((scalarPair r * p : sqPair A B) : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1 =
      Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).1 := rfl

theorem scalarPair_mul_snd {K : Type*} [Field K] {A B : K} (r : Kˣ) (p : sqPair A B) :
    ((scalarPair r * p : sqPair A B) : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2 =
      Units.map (algebraMap K ℍ[K,A,B]).toMonoidHom r * (p : (ℍ[K,A,B])ˣ × (ℍ[K,A,B])ˣ).2 := rfl

variable {a b : 𝓞 F}

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

theorem sqSOK_scalarPair_mul {K : Type*} [Field K] [Algebra F K] (ha : (a : F) ≠ 0) (r : Kˣ)
    (p : sqPair (algebraMap F K (a : F)) (algebraMap F K (b : F))) :
    sqSOK K ha (scalarPair r * p) = sqSOK K ha p := by
  rw [map_mul, (sqSOK_eq_one_iff ha (scalarPair r)).2 ⟨r, rfl, rfl⟩, one_mul]

/-- **A unit of $D\otimes\mathbb A$ that is central at every place is an idele** (via the kernel computation for
$D^\times_{\mathbb A}\to SO(D^0)(\mathbb A)$). -/
theorem mem_range_quatScalar_of_local (ha : a ≠ 0) {x : (QuatAdele (a : F) (b : F))ˣ}
    (hv : ∀ v, unitAtA (a : F) (b : F) v x ∈ centerUnits (algebraMap F (v.adicCompletion F) (a : F))
      (algebraMap F (v.adicCompletion F) (b : F)))
    (hR : ∀ w : {w : InfinitePlace F // w.IsReal}, unitAtR (a : F) (b : F) w x ∈
      centerUnits (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)))
    (hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, unitAtC (a : F) (b : F) w x ∈
      centerUnits (w.1.embedding (a : F)) (w.1.embedding (b : F))) :
    x ∈ (quatScalar (a : F) (b : F)).range := by
  have hA : (a : F) ≠ 0 := coe_ne_zero' ha
  refine (conjAdele_eq_one_iff a b ha x).1 ?_
  rw [conjAdele_apply]
  refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext ?_)) ?_
  · change conjGL (unitAtR (a : F) (b : F) w x) = 1
    exact (conjGL_eq_one_iff (embedding_of_isReal w.2) hA _).2 (hR w)
  · change conjGL (unitAtC (a : F) (b : F) w x) = 1
    exact (conjGL_eq_one_iff w.1.embedding hA _).2 (hC w)
  · ext v : 2
    rw [conjFin_apply]
    exact (conjOrth_eq_one_iff _ (hQF a b) hA _).2 (hv v)

theorem unitAtA_quatScalar_mem (c : (Adeles F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtA (a : F) (b : F) v (quatScalar (a : F) (b : F) c) ∈
      centerUnits (algebraMap F (v.adicCompletion F) (a : F)) (algebraMap F (v.adicCompletion F) (b : F)) := by
  rw [unitAtA_eq, quatUnitsEquiv_quatScalar]
  exact unitAtQ_finScalar _ _ _ v

theorem unitAtR_quatScalar_mem (c : (Adeles F)ˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    unitAtR (a : F) (b : F) w (quatScalar (a : F) (b : F) c) ∈
      centerUnits (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) :=
  mem_centerUnits.2 ⟨(c : Adeles F).1.1 w, QuaternionAlgebra.ext rfl rfl rfl rfl⟩

theorem unitAtC_quatScalar_mem (c : (Adeles F)ˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    unitAtC (a : F) (b : F) w (quatScalar (a : F) (b : F) c) ∈
      centerUnits (w.1.embedding (a : F)) (w.1.embedding (b : F)) :=
  mem_centerUnits.2 ⟨(c : Adeles F).1.2 w, QuaternionAlgebra.ext rfl rfl rfl rfl⟩

end Kernel

/-! ### The global map: surjectivity, kernel, the isomorphism -/

section Global

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

/-- **$G^\natural(\mathbb A)\to SO(V)(\mathbb A)$**, $(\alpha,\beta,u)\mapsto(x\mapsto\alpha_wx\beta_w^{-1})_{w\le\infty}$. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
def sqAdele : (gnatSqO ha0 hb0).G →* SOAdele Q₀ := (sqInf ha0 hb0).prod (sqFin ha0 hb0)

theorem continuous_sqAdele : Continuous (sqAdele ha0 hb0) :=
  (continuous_sqInf ha0 hb0).prodMk (continuous_sqFin ha0 hb0)

include hb0 in
/-- Local lifts at a finite place, integral at good places. -/
theorem exists_pairV_lift (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : sqPair (algebraMap F (v.adicCompletion F) (a : F)) (algebraMap F (v.adicCompletion F) (b : F)),
      (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) p : orthGroup QF (v.adicCompletion F)) = (g : OAf QF) v ∧
      ((Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v) →
        (p : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).1 ∈ lamLocUnits (a : F) (b : F) v ∧
        (p : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).2 ∈ lamLocUnits (a : F) (b : F) v) := by
  obtain ⟨p, hp⟩ := sqSOK_surjective (K := v.adicCompletion F) (coe_ne_zero' ha0) (coe_ne_zero' hb0)
    (⟨(g : OAf QF) v, g.2 v⟩ : soSub QF (v.adicCompletion F))
  have hp' : (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) p : orthGroup QF (v.adicCompletion F)) =
      (g : OAf QF) v := congrArg Subtype.val hp
  by_cases hS : Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v
  · obtain ⟨h2, hav, hbv, hst⟩ := hS
    obtain ⟨r, hr1, hr2⟩ := exists_smul_mem_lamLocUnits_sq v (fun w => valued_algebraMap_int_le_one w a)
      (fun w => valued_algebraMap_int_le_one w b) (coe_ne_zero' ha0) h2 hav hbv p (by rw [hp']; exact hst)
    refine ⟨scalarPair r * p, ?_, fun _ => ⟨by rw [scalarPair_mul_fst]; exact hr1, by rw [scalarPair_mul_snd]; exact hr2⟩⟩
    rw [sqSOK_scalarPair_mul, hp']
  · exact ⟨p, hp', fun h => absurd h hS⟩

include ha0 hb0 in
theorem eventually_good (g : SOAf Q₀) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧ (g : OAf QF) v ∈ stdStab QF v := by
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 := by
    filter_upwards [eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hv
    rwa [map_ofNat] at hv
  filter_upwards [h2, eventually_valued_eq_one (coe_ne_zero' ha0), eventually_valued_eq_one (coe_ne_zero' hb0),
    (g : OAf QF).2] with v h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

include hb0 in
/-- Local lifts at a real place. -/
theorem exists_pairR_lift (w : {w : InfinitePlace F // w.IsReal}) (g : ArchSO (QRe Q₀ w)) :
    ∃ p : sqPair (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)),
      (sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 (coe_ne_zero' ha0)) p :
        GL (Fin 4) ℝ) = ArchSO.incl _ g := by
  have hm := (mem_soReal_iff _ _).1 (show ArchSO.incl _ g ∈ soReal (QRe Q₀ w) from g.2)
  rw [show (QRe Q₀ w).hessian = (QF).hessian.map (embedding_of_isReal w.2) from hessian_map_NF _ _] at hm
  exact exists_sqSO_eq (embedding_of_isReal w.2) a b (coe_ne_zero' ha0) (coe_ne_zero' hb0) _
    (by convert hm.1 using 3) (by convert hm.2 using 2)

include hb0 in
/-- Local lifts at a complex place. -/
theorem exists_pairC_lift (w : {w : InfinitePlace F // w.IsComplex}) (g : ArchSOC (QCx Q₀ w)) :
    ∃ p : sqPair (w.1.embedding (a : F)) (w.1.embedding (b : F)),
      (sqSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 (coe_ne_zero' ha0)) p :
        GL (Fin 4) ℂ) = ArchSOC.incl _ g := by
  have hm := (mem_soC_iff _ _).1 (ArchSOC.incl_mem _ g)
  rw [gramC] at hm
  have h1 : ((ArchSOC.incl _ g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ)ᵀ * (QCx Q₀ w).hessian *
      ((ArchSOC.incl _ g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = (QCx Q₀ w).hessian := by
    have := congrArg ((2 : ℂ) • ·) hm.1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul] at this
    norm_num at this
    exact this
  rw [show (QCx Q₀ w).hessian = (QF).hessian.map w.1.embedding from hessian_map_NF _ _] at h1
  exact exists_sqSO_eq w.1.embedding a b (coe_ne_zero' ha0) (coe_ne_zero' hb0) _
    (by convert h1 using 3) (by convert hm.2 using 2)

/-- **$G^\natural(\mathbb A)\to SO(V)(\mathbb A)$ is surjective** ($a, b\ne0$): lift every local component (over $F_v$,
$\mathbb R$, $\mathbb C$); at the cofinitely many good places with integral component the lift can be taken in
$(\Lambda_v^\times)^2$ (`exists_smul_mem_lamLocUnits_sq`), so the lifts form two units of $D\otimes\mathbb A$ with equal norms. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
theorem sqAdele_surjective : Function.Surjective (sqAdele ha0 hb0) := by
  rintro ⟨gI, gf⟩
  choose pF hpF hpFS using fun v => exists_pairV_lift ha0 hb0 gf v
  choose pR hpR using fun w => exists_pairR_lift ha0 hb0 w (gI.1 w)
  choose pC hpC using fun w => exists_pairC_lift ha0 hb0 w (gI.2 w)
  have hev1 : ∀ᶠ v in cofinite,
      (pF v : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).1 ∈ lamLocUnits (a : F) (b : F) v := by
    filter_upwards [eventually_good ha0 hb0 gf] with v hv
    exact (hpFS v hv).1
  have hev2 : ∀ᶠ v in cofinite,
      (pF v : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).2 ∈ lamLocUnits (a : F) (b : F) v := by
    filter_upwards [eventually_good ha0 hb0 gf] with v hv
    exact (hpFS v hv).2
  set α := mkAdeleUnit (a : F) (b : F) (fun w => (pR w : (HRe a b w)ˣ × (HRe a b w)ˣ).1)
    (fun w => (pC w : (HCx a b w)ˣ × (HCx a b w)ˣ).1)
    (fun v => (pF v : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).1) hev1 with hα
  set β := mkAdeleUnit (a : F) (b : F) (fun w => (pR w : (HRe a b w)ˣ × (HRe a b w)ˣ).2)
    (fun w => (pC w : (HCx a b w)ˣ × (HCx a b w)ˣ).2)
    (fun v => (pF v : HK (v.adicCompletion F) a b × HK (v.adicCompletion F) a b).2) hev2 with hβ
  have hnrd : nrdUnit β = nrdUnit α := by
    refine nrdUnit_eq_of_local (fun v => ?_) (fun w => ?_) (fun w => ?_)
    · rw [hα, hβ, unitAtA_mkAdeleUnit, unitAtA_mkAdeleUnit]; exact (pF v).2.symm
    · rw [hα, hβ, unitAtR_mkAdeleUnit, unitAtR_mkAdeleUnit]; exact (pR w).2.symm
    · rw [hα, hβ, unitAtC_mkAdeleUnit, unitAtC_mkAdeleUnit]; exact (pC w).2.symm
  let g : (gnatSqO ha0 hb0).G := ⟨((α, β), nrdUnit α), Prod.ext rfl hnrd⟩
  have hgF : gFst ha0 hb0 g = α := rfl
  have hgS : gSnd ha0 hb0 g = β := rfl
  refine ⟨g, Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_⟩
  · have hp : pairR ha0 hb0 w g = pR w := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rw [pairR_fst, hgF, hα, unitAtR_mkAdeleUnit]
      · rw [pairR_snd, hgS, hβ, unitAtR_mkAdeleUnit]
    change ArchSO.incl _ (sqR ha0 hb0 w g) = _
    rw [sqR_incl, sqGLR_apply, hp, hpR w]
  · have hp : pairC ha0 hb0 w g = pC w := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rw [pairC_fst, hgF, hα, unitAtC_mkAdeleUnit]
      · rw [pairC_snd, hgS, hβ, unitAtC_mkAdeleUnit]
    change ArchSOC.incl _ (sqC ha0 hb0 w g) = _
    rw [sqC_incl, sqGLC_apply, hp, hpC w]
  · have hp : ∀ v, pairV ha0 hb0 v g = pF v := fun v => by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rw [pairV_fst, hgF, hα, unitAtA_mkAdeleUnit]
      · rw [pairV_snd, hgS, hβ, unitAtA_mkAdeleUnit]
    ext v : 2
    change ((sqFin ha0 hb0 g : SOAf Q₀) : OAf QF) v = _
    rw [sqFin_apply, hp v, hpF v]

theorem sqF_coe_central {K : Type*} [Field K] {A B : K} {x y : (ℍ[K,A,B])ˣ} {r : K} (hx : (x : ℍ[K,A,B]) = r)
    (hy : (y : ℍ[K,A,B]) = r) : x ∈ centerUnits A B ∧ x = y :=
  ⟨mem_centerUnits.2 ⟨r, hx⟩, Units.ext (hx.trans hy.symm)⟩

/-- **The kernel of $G^\natural(\mathbb A)\to SO(V)(\mathbb A)$ is the centre $Z$.** -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
theorem sqAdele_eq_one_iff (g : (gnatSqO ha0 hb0).G) :
    sqAdele ha0 hb0 g = 1 ↔ g ∈ (gnatSqO ha0 hb0).zHom.range := by
  constructor
  · intro h
    have hv : ∀ v, unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) ∈ centerUnits _ _ ∧
        unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) = unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) := fun v => by
      have h1 : sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) = 1 := by
        apply Subtype.ext
        have := congrArg (fun x : SOAdele Q₀ => ((x.2 : SOAf Q₀) : OAf QF) v) h
        exact this
      obtain ⟨r, hr1, hr2⟩ := (sqSOK_eq_one_iff _ _).1 h1
      exact sqF_coe_central hr1 hr2
    have hR : ∀ w, unitAtR (a : F) (b : F) w (gFst ha0 hb0 g) ∈ centerUnits _ _ ∧
        unitAtR (a : F) (b : F) w (gFst ha0 hb0 g) = unitAtR (a : F) (b : F) w (gSnd ha0 hb0 g) := fun w => by
      have h1 : (sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 (coe_ne_zero' ha0))
          (pairR ha0 hb0 w g) : GL (Fin 4) ℝ) = 1 := by
        rw [← sqGLR_apply, ← sqR_incl]
        have := congrArg (fun x : SOAdele Q₀ => ArchSO.incl _ (x.1.1 w)) h
        exact this
      obtain ⟨r, hr1, hr2⟩ := (sqSO_val_eq_one_iff _ a _ (coe_ne_zero' ha0) _).1 h1
      exact sqF_coe_central hr1 hr2
    have hC : ∀ w, unitAtC (a : F) (b : F) w (gFst ha0 hb0 g) ∈ centerUnits _ _ ∧
        unitAtC (a : F) (b : F) w (gFst ha0 hb0 g) = unitAtC (a : F) (b : F) w (gSnd ha0 hb0 g) := fun w => by
      have h1 : (sqSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 (coe_ne_zero' ha0))
          (pairC ha0 hb0 w g) : GL (Fin 4) ℂ) = 1 := by
        rw [← sqGLC_apply, ← sqC_incl]
        have := congrArg (fun x : SOAdele Q₀ => ArchSOC.incl _ (x.1.2 w)) h
        exact this
      obtain ⟨r, hr1, hr2⟩ := (sqSO_val_eq_one_iff _ a _ (coe_ne_zero' ha0) _).1 h1
      exact sqF_coe_central hr1 hr2
    obtain ⟨c, hc⟩ := mem_range_quatScalar_of_local ha0 (fun v => (hv v).1) (fun w => (hR w).1) (fun w => (hC w).1)
    have hαβ : gFst ha0 hb0 g = gSnd ha0 hb0 g :=
      quatUnits_eq_of_local (fun v => (hv v).2) (fun w => (hR w).2) (fun w => (hC w).2)
    refine ⟨c, (gnatSqO ha0 hb0).fst_injective ?_⟩
    change ((gnatSqO ha0 hb0).s c) = _
    refine Prod.ext ?_ ?_
    · exact hc.trans rfl
    · exact hc.trans hαβ
  · rintro ⟨c, rfl⟩
    have hF : gFst ha0 hb0 ((gnatSqO ha0 hb0).zHom c) = quatScalar (a : F) (b : F) c := rfl
    have hS : gSnd ha0 hb0 ((gnatSqO ha0 hb0).zHom c) = quatScalar (a : F) (b : F) c := rfl
    refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
    · change ArchSO.incl _ (sqR ha0 hb0 w _) = ArchSO.incl _ 1
      rw [sqR_incl, sqGLR_apply, map_one]
      obtain ⟨r, hr⟩ := mem_centerUnits.1 (unitAtR_quatScalar_mem (a := a) (b := b) c w)
      refine (sqSO_val_eq_one_iff _ a _ (coe_ne_zero' ha0) _).2 ⟨r, ?_, ?_⟩
      · rw [pairR_fst, hF]; exact hr
      · rw [pairR_snd, hS]; exact hr
    · change ArchSOC.incl _ (sqC ha0 hb0 w _) = ArchSOC.incl _ 1
      rw [sqC_incl, sqGLC_apply, map_one]
      obtain ⟨r, hr⟩ := mem_centerUnits.1 (unitAtC_quatScalar_mem (a := a) (b := b) c w)
      refine (sqSO_val_eq_one_iff _ a _ (coe_ne_zero' ha0) _).2 ⟨r, ?_, ?_⟩
      · rw [pairC_fst, hF]; exact hr
      · rw [pairC_snd, hS]; exact hr
    · ext v : 2
      change ((sqFin ha0 hb0 _ : SOAf Q₀) : OAf QF) v = ((1 : SOAf Q₀) : OAf QF) v
      rw [sqFin_apply]
      obtain ⟨r, hr⟩ := mem_centerUnits.1 (unitAtA_quatScalar_mem (a := a) (b := b) c v)
      have h1 : sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v ((gnatSqO ha0 hb0).zHom c)) = 1 :=
        (sqSOK_eq_one_iff _ _).2 ⟨r, by rw [pairV_fst, hF]; exact hr, by rw [pairV_snd, hS]; exact hr⟩
      rw [h1]
      rfl

theorem ker_sqAdele : (sqAdele ha0 hb0).ker = (gnatSqO ha0 hb0).zHom.range := by
  ext g; exact (MonoidHom.mem_ker).trans (sqAdele_eq_one_iff ha0 hb0 g)

instance locallyCompactSpace_SOAf {n : ℕ} (Q : QuadForm (𝓞 F) n) : LocallyCompactSpace (SOAf Q) :=
  (isClosed_soAf (Q.map (algebraMap (𝓞 F) F))).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- **`sqAdele` is open** (open mapping theorem: $G^\natural(\mathbb A)$ is $\sigma$-compact, $SO(V)(\mathbb A)$ locally compact). -/
theorem isOpenMap_sqAdele : IsOpenMap (sqAdele ha0 hb0) :=
  MonoidHom.isOpenMap_of_sigmaCompact _ (sqAdele_surjective ha0 hb0) (continuous_sqAdele ha0 hb0)

/-- The group isomorphism $P = G^\natural(\mathbb A)/Z\cong SO(V)(\mathbb A)$. -/
def sqPMulEquiv : (gnatSqO ha0 hb0).P ≃* SOAdele Q₀ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_sqAdele ha0 hb0).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (sqAdele_surjective ha0 hb0))

theorem sqPMulEquiv_mk (g : (gnatSqO ha0 hb0).G) :
    sqPMulEquiv ha0 hb0 (QuotientGroup.mk g) = sqAdele ha0 hb0 g := rfl

theorem continuous_sqPMulEquiv : Continuous (sqPMulEquiv ha0 hb0) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_sqAdele ha0 hb0)

theorem isOpenMap_sqPMulEquiv : IsOpenMap (sqPMulEquiv ha0 hb0) := by
  intro U hU
  have hpre : IsOpen ((QuotientGroup.mk : (gnatSqO ha0 hb0).G → (gnatSqO ha0 hb0).P) ⁻¹' U) :=
    hU.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have himg : (sqPMulEquiv ha0 hb0) '' U =
      (sqAdele ha0 hb0) '' ((QuotientGroup.mk : (gnatSqO ha0 hb0).G → (gnatSqO ha0 hb0).P) ⁻¹' U) := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective u
      exact ⟨α, hu, rfl⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨_, hα, rfl⟩
  rw [himg]
  exact isOpenMap_sqAdele ha0 hb0 _ hpre

/-- **The adelic isomorphism $\Phi : P = G^\natural(\mathbb A)/\mathbb A^\times\cong SO(\langle1,-a,-b,ab\rangle)(\mathbb A)$** as topological
groups ($a, b\in\mathcal O_F\setminus0$, any number field, any signature). Placewise it is the $G^\natural(F_v)/F_v^\times\cong SO(V)(F_v)$ for $d = 1$, i.e. $(\alpha,\beta)\mapsto(x\mapsto\alpha x\beta^{-1})$. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
def sqPEquiv : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele Q₀ :=
  { sqPMulEquiv ha0 hb0 with
    continuous_toFun := continuous_sqPMulEquiv ha0 hb0
    continuous_invFun := ((sqPMulEquiv ha0 hb0).toEquiv.toHomeomorphOfContinuousOpen
      (continuous_sqPMulEquiv ha0 hb0) (isOpenMap_sqPMulEquiv ha0 hb0)).symm.continuous }

theorem sqPEquiv_mk (g : (gnatSqO ha0 hb0).G) :
    sqPEquiv ha0 hb0 ((gnatSqO ha0 hb0).π g) = sqAdele ha0 hb0 g := rfl

end Global

/-! ### Global points: $G^\natural(F)/F^\times\cong SO(V)(F)$, compatibly with the diagonal embeddings -/

section GlobalPoints

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

theorem qSq_map_self : QF = V0Form (a : F) (b : F) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qSq, V0Form, QuadForm.diag, QuadForm.map]

/-- $(\xi_1,\xi_2)\mapsto(x\mapsto\xi_1x\xi_2^{-1})$ over $F$, as a matrix. -/
def sqGLF : sqPair (a : F) (b : F) →* GL (Fin 4) F :=
  (SO (V0Form (a : F) (b : F) 1)).subtype.comp (sqSO (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0))

theorem sqGLF_apply (p : sqPair (a : F) (b : F)) :
    sqGLF ha0 p = sqSO (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0) p := by
  simp only [sqGLF, MonoidHom.comp_apply, Subgroup.coe_subtype]

theorem sqGLF_mem (p : sqPair (a : F) (b : F)) : sqGLF ha0 p ∈ orthGroup QF F := by
  rw [mem_orthGroup, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, sqGLF_apply]
  have := ((mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0)).1 (sqSO two_ne_zero (coe_ne_zero' ha0) p).2).2
  rw [qSq_map_self]
  exact this

theorem sqGLF_det (p : sqPair (a : F) (b : F)) : (sqGLF ha0 p).val.det = 1 := by
  rw [sqGLF_apply]
  exact (sqSO two_ne_zero (coe_ne_zero' ha0) p).2.1

/-- **$G^\natural(F)\to SO(V)(F)$** ($d = 1$). -/
def sqF : sqPair (a : F) (b : F) →* soSub QF F :=
  ((sqGLF ha0).codRestrict (orthGroup QF F) (sqGLF_mem ha0)).codRestrict (soSub QF F) (sqGLF_det ha0)

theorem sqF_coe (p : sqPair (a : F) (b : F)) :
    (((sqF ha0 p : soSub QF F) : orthGroup QF F) : GL (Fin 4) F) = sqGLF ha0 p := rfl

include hb0 in
theorem sqF_surjective : Function.Surjective (sqF (b := b) ha0) := by
  intro γ
  have hmem : ((γ : orthGroup QF F) : GL (Fin 4) F) ∈ SO (V0Form (a : F) (b : F) 1) := by
    rw [mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0)]
    have h1 := (mem_orthGroup QF).1 (γ : orthGroup QF F).2
    rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id,
      show (QF).hessian = (V0Form (a : F) (b : F) 1).hessian by rw [qSq_map_self]] at h1
    exact ⟨mem_soSub.1 γ.2, h1⟩
  obtain ⟨p, hp⟩ := sqSO_surjective (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0) (coe_ne_zero' hb0) ⟨_, hmem⟩
  refine ⟨p, Subtype.ext (Subtype.ext ?_)⟩
  rw [sqF_coe, sqGLF_apply, hp]

/-- **Compatibility with the global points**: if $\alpha = \xi_1$, $\beta = \xi_2$ diagonally, then
$\Phi(\alpha,\beta,u) = (x\mapsto\xi_1x\xi_2^{-1})_{\mathrm{diag}}$. -/
theorem sqAdele_diag (p : sqPair (a : F) (b : F)) (g : (gnatSqO ha0 hb0).G)
    (h1 : gFst ha0 hb0 g = quatDiagUnit a b (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).1)
    (h2 : gSnd ha0 hb0 g = quatDiagUnit a b (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).2) :
    sqAdele ha0 hb0 g = diagSOAdele Q₀ (sqF ha0 p) := by
  set ξ₁ := (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).1
  set ξ₂ := (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).2
  have h2' : (gSnd ha0 hb0 g)⁻¹ = quatDiagUnit a b ξ₂⁻¹ := by rw [h2, map_inv]
  refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
  · change sqGLR ha0 hb0 w g = Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (sqGLF ha0 p)
    apply Units.ext
    rw [sqGLR_apply, sqGLF_apply, sqSO_val, pairR_fst, pairR_snd, ← map_inv]
    change _ = (((sqSO (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0) p : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map (embedding_of_isReal w.2)
    rw [sqSO_val, h1, h2']
    refine sqMat_map (embedding_of_isReal w.2) _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact mixedEmbedding_apply_isReal F _ w
  · change sqGLC ha0 hb0 w g = Matrix.GeneralLinearGroup.map w.1.embedding (sqGLF ha0 p)
    apply Units.ext
    rw [sqGLC_apply, sqGLF_apply, sqSO_val, pairC_fst, pairC_snd, ← map_inv]
    change _ = (((sqSO (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0) p : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map w.1.embedding
    rw [sqSO_val, h1, h2']
    refine sqMat_map w.1.embedding _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    exact mixedEmbedding_apply_isComplex F _ w
  · ext v : 3
    change ((sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF (v.adicCompletion F)) :
      GL (Fin 4) (v.adicCompletion F)) = Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (sqGLF ha0 p)
    apply Units.ext
    rw [sqSOK_coe, sqGLF_apply, sqSO_val, pairV_fst, pairV_snd, ← map_inv]
    change _ = (((sqSO (two_ne_zero : (2 : F) ≠ 0) (coe_ne_zero' ha0) p : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map (algebraMap F (v.adicCompletion F))
    rw [sqSO_val, h1, h2']
    exact sqMat_map (algebraMap F (v.adicCompletion F)) _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl

theorem nrdUnit_quatDiagUnit_eq {ξ η : (ℍ[F, (a : F), (b : F)])ˣ} :
    nrdUnit (quatDiagUnit a b ξ) = nrdUnit (quatDiagUnit a b η) ↔
      nrd (ξ : ℍ[F, (a : F), (b : F)]) = nrd (η : ℍ[F, (a : F), (b : F)]) := by
  constructor
  · intro h
    have := congrArg Units.val h
    rw [nrdUnit_map_quatDiagRing, nrdUnit_map_quatDiagRing] at this
    exact diag_injective this
  · intro h
    apply Units.ext
    rw [nrdUnit_map_quatDiagRing, nrdUnit_map_quatDiagRing, h]

/-- **$\Phi(\pi(\Gamma)) = SO(V)(F)$**: the isomorphism carries the image of $G^\natural(F)$ onto `GammaSOAdele`. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]; §2.4, p. 23"]
theorem map_gam_sqAdele : (gnatSqO ha0 hb0).gam.map (sqAdele ha0 hb0) = GammaSOAdele Q₀ := by
  ext x
  constructor
  · rintro ⟨g, ⟨⟨⟨ξ₁, hξ₁⟩, ⟨ξ₂, hξ₂⟩⟩, -⟩, rfl⟩
    have hn : nrd (ξ₁ : ℍ[F, (a : F), (b : F)]) = nrd (ξ₂ : ℍ[F, (a : F), (b : F)]) := by
      rw [← nrdUnit_quatDiagUnit_eq]
      change nrdUnit (Units.map (quatDiagRing (a : F) (b : F)).toMonoidHom ξ₁) =
        nrdUnit (Units.map (quatDiagRing (a : F) (b : F)).toMonoidHom ξ₂)
      rw [hξ₁, hξ₂]
      exact nrdUnit_gFst_eq_gSnd ha0 hb0 g
    exact ⟨sqF ha0 ⟨(ξ₁, ξ₂), hn⟩, (sqAdele_diag ha0 hb0 ⟨(ξ₁, ξ₂), hn⟩ g hξ₁.symm hξ₂.symm).symm⟩
  · rintro ⟨γ, rfl⟩
    obtain ⟨p, rfl⟩ := sqF_surjective ha0 hb0 γ
    set ξ₁ := (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).1
    set ξ₂ := (p : (ℍ[F, (a : F), (b : F)])ˣ × (ℍ[F, (a : F), (b : F)])ˣ).2
    have hn : nrdUnit (quatDiagUnit a b ξ₂) = nrdUnit (quatDiagUnit a b ξ₁) :=
      nrdUnit_quatDiagUnit_eq.2 p.2.symm
    let g : (gnatSqO ha0 hb0).G :=
      ⟨((quatDiagUnit a b ξ₁, quatDiagUnit a b ξ₂), nrdUnit (quatDiagUnit a b ξ₁)), Prod.ext rfl hn⟩
    refine ⟨g, ⟨⟨⟨ξ₁, rfl⟩, ⟨ξ₂, rfl⟩⟩, ⟨Units.mk0 _ (nrd_units_ne_zero ξ₁), ?_⟩⟩,
      sqAdele_diag ha0 hb0 p g rfl rfl⟩
    apply Units.ext
    rw [diagUnits_val]
    exact (nrdUnit_map_quatDiagRing ξ₁).symm

/-- **$\Phi(\pi(\Gamma)) = SO(V)(F)$** on the quotient $P$. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]; §2.4, p. 23"]
theorem map_gamP_sqPEquiv :
    (gnatSqO ha0 hb0).gamP.map (sqPEquiv ha0 hb0).toMulEquiv.toMonoidHom = GammaSOAdele Q₀ := by
  rw [← map_gam_sqAdele ha0 hb0]
  change ((gnatSqO ha0 hb0).gam.map (gnatSqO ha0 hb0).π).map _ = _
  rw [Subgroup.map_map]
  rfl

end GlobalPoints

end QuadFormsKB.Tamagawa.Measure.Weil
