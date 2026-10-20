/-
# Square discriminant, adelically: $P = G^\natural(\mathbb A)/\mathbb A^\times\cong SO(D,\operatorname{nrd})(\mathbb A)$


**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus0$, $D = (a,b)_F$, $Q_0 = q_{\mathrm{sq}}(a,b) = \langle1,-a,-b,ab\rangle$ over
$\mathcal O_F$ (`qSq`), any signature. $G^\natural$ is `gnatSqO a b` (`GnatData` with
$M = (D\otimes\mathbb A)^\times\times(D\otimes\mathbb A)^\times$), $P = G^\natural/Z$ its quotient by the centre $Z\cong\mathbb A^\times$.

**Defines/proves** (mirroring `PDAdelic`/`PDArch`/`PDGlobal` for $m = 3$)
* `unitAtA`, `nrd_unitAtA`, `projRA`, `projCA`: the local components of a unit of $D\otimes\mathbb A$ and their reduced norms;
* `sqFin`: $G^\natural(\mathbb A)\to SO(V)(\mathbb A_f)$, $(\alpha,\beta,u)\mapsto(x\mapsto\alpha_vx\beta_v^{-1})_v$ (it lands in the restricted
  product because $\alpha_v,\beta_v\in\Lambda_v^\times$ for almost all $v$, `sqSOK_mem_stdStab`); `continuous_sqFin`;
* `sqInf`: the archimedean map into $G_\infty$ (real and complex places); `continuous_sqInf`;
* **`sqAdele`** $= (\mathrm{sqInf},\mathrm{sqFin})$, **`sqAdele_surjective`** (local surjectivity, integral lifts at almost all places
  `exists_smul_mem_lamLocUnits_sq`), **`ker_sqAdele`** (kernel = the centre $Z$), open (Mathlib's open mapping theorem);
* **`sqPEquiv : (gnatSqO ha0 hb0).P ≃ₜ* SOAdele (qSq a b)`**;
* global points: `sqF` ($G^\natural(F)\to SO(V)(F)$), **`sqAdele_diag`**, **`map_gamP_sqPEquiv`**: $\Phi(\pi(\Gamma)) = SO(V)(F)$
  (`GammaSOAdele`).

Source: Weil 1982, §3.7, p. 65 [unverified page]; §2.4, p. 23 ($G_k\subset G_{\mathbb A}$).
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqLocal

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

/-! ### Local components of units of $D\otimes\mathbb A$ -/

section Components

variable (A B : F)

/-- The finite component at `v` of a unit of $D\otimes\mathbb A$. -/
def unitAtA (v : HeightOneSpectrum (𝓞 F)) : (QuatAdele A B)ˣ →* (QuatV A B v)ˣ :=
  (unitAtQ A B v).comp ((MonoidHom.snd _ _).comp (quatUnitsEquiv A B).toMulEquiv.toMonoidHom)

theorem unitAtA_val (v : HeightOneSpectrum (𝓞 F)) (x : (QuatAdele A B)ˣ) :
    ((unitAtA A B v x : (QuatV A B v)ˣ) : QuatV A B v) =
      ⟨(x : QuatAdele A B).re.2 v, (x : QuatAdele A B).imI.2 v, (x : QuatAdele A B).imJ.2 v,
        (x : QuatAdele A B).imK.2 v⟩ := rfl

theorem unitAtA_eq (v : HeightOneSpectrum (𝓞 F)) (x : (QuatAdele A B)ˣ) :
    unitAtA A B v x = unitAtQ A B v (quatUnitsEquiv A B x).2 := rfl

/-- **The local reduced norm is the component of the global one.** -/
theorem nrd_unitAtA (v : HeightOneSpectrum (𝓞 F)) (x : (QuatAdele A B)ˣ) :
    nrd ((unitAtA A B v x : (QuatV A B v)ˣ) : QuatV A B v) = ((nrdUnit x : (Adeles F)ˣ) : Adeles F).2 v := by
  rw [unitAtA_val, nrdUnit_val, nrd_mk]
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Prod.snd_add, Prod.snd_mul, Prod.snd_sub, Prod.snd_neg]
  have hev : ∀ y : FiniteAdeleRing (𝓞 F) F, y v = evalAt v y := fun _ => rfl
  rw [hev ((↑x : QuatAdele A B).re.2 * _ + _ + _ + _ - _)]
  simp only [map_add, map_mul, map_neg, map_zero, map_sub, diag_snd, evalAt_algebraMap, Prod.snd_zero]
  simp only [← hev]
  ring

theorem continuous_unitAtA (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitAtA A B v) :=
  (continuous_unitAtQ A B v).comp (continuous_snd.comp (quatUnitsEquiv A B).continuous)

/-- The real component at `w` of a unit of $D\otimes\mathbb A$. -/
def unitAtR (w : {w : InfinitePlace F // w.IsReal}) :
    (QuatAdele A B)ˣ →* (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ :=
  (Units.map (projR A B w).toMonoidHom).comp ((MonoidHom.fst _ _).comp (quatUnitsEquiv A B).toMulEquiv.toMonoidHom)

/-- The complex component at `w` of a unit of $D\otimes\mathbb A$. -/
def unitAtC (w : {w : InfinitePlace F // w.IsComplex}) :
    (QuatAdele A B)ˣ →* (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ :=
  (Units.map (projC A B w).toMonoidHom).comp ((MonoidHom.fst _ _).comp (quatUnitsEquiv A B).toMulEquiv.toMonoidHom)

theorem unitAtR_val (w : {w : InfinitePlace F // w.IsReal}) (x : (QuatAdele A B)ˣ) :
    ((unitAtR A B w x : (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ) :
      ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B]) =
      ⟨(x : QuatAdele A B).re.1.1 w, (x : QuatAdele A B).imI.1.1 w, (x : QuatAdele A B).imJ.1.1 w,
        (x : QuatAdele A B).imK.1.1 w⟩ := rfl

theorem unitAtC_val (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatAdele A B)ˣ) :
    ((unitAtC A B w x : (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ) : ℍ[ℂ, w.1.embedding A, w.1.embedding B]) =
      ⟨(x : QuatAdele A B).re.1.2 w, (x : QuatAdele A B).imI.1.2 w, (x : QuatAdele A B).imJ.1.2 w,
        (x : QuatAdele A B).imK.1.2 w⟩ := rfl

theorem nrd_unitAtR (w : {w : InfinitePlace F // w.IsReal}) (x : (QuatAdele A B)ˣ) :
    nrd ((unitAtR A B w x : (ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B])ˣ) :
      ℍ[ℝ, embedding_of_isReal w.2 A, embedding_of_isReal w.2 B]) =
      ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.1 w := by
  rw [unitAtR_val, nrdUnit_val, nrd_mk]
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Prod.fst_add, Prod.fst_mul, Prod.fst_sub, Prod.fst_neg,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Prod.fst_zero, Pi.zero_apply, diag_fst,
    mixedEmbedding_apply_isReal]
  ring

theorem nrd_unitAtC (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatAdele A B)ˣ) :
    nrd ((unitAtC A B w x : (ℍ[ℂ, w.1.embedding A, w.1.embedding B])ˣ) : ℍ[ℂ, w.1.embedding A, w.1.embedding B]) =
      ((nrdUnit x : (Adeles F)ˣ) : Adeles F).1.2 w := by
  rw [unitAtC_val, nrdUnit_val, nrd_mk]
  simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Prod.fst_add, Prod.fst_mul, Prod.fst_sub, Prod.fst_neg,
    Prod.snd_add, Prod.snd_mul, Prod.snd_sub, Prod.snd_neg,
    Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, diag_fst,
    mixedEmbedding_apply_isComplex]
  ring

end Components

/-! ### The two components of $G^\natural$ and the local pairs -/

section Pairs

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)
local notation "MD" => (QuatAdele ((a : 𝓞 F) : F) ((b : 𝓞 F) : F))ˣ

/-- The first component $\alpha$ of $(\alpha,\beta,u)\in G^\natural$. -/
def gFst : (gnatSqO ha0 hb0).G →* MD :=
  (MonoidHom.fst _ _).comp ((MonoidHom.fst _ _).comp (gnatSqO ha0 hb0).gnat.subtype)

/-- The second component $\beta$ of $(\alpha,\beta,u)\in G^\natural$. -/
def gSnd : (gnatSqO ha0 hb0).G →* MD :=
  (MonoidHom.snd _ _).comp ((MonoidHom.fst _ _).comp (gnatSqO ha0 hb0).gnat.subtype)

theorem gFst_apply (g : (gnatSqO ha0 hb0).G) : gFst ha0 hb0 g = (g : (MD × MD) × (Adeles F)ˣ).1.1 := rfl
theorem gSnd_apply (g : (gnatSqO ha0 hb0).G) : gSnd ha0 hb0 g = (g : (MD × MD) × (Adeles F)ˣ).1.2 := rfl

theorem continuous_gFst : Continuous (gFst ha0 hb0) :=
  continuous_fst.comp (continuous_fst.comp continuous_subtype_val)
theorem continuous_gSnd : Continuous (gSnd ha0 hb0) :=
  continuous_snd.comp (continuous_fst.comp continuous_subtype_val)

/-- $\operatorname{nrd}\alpha = \operatorname{nrd}\beta\ (= u)$ on $G^\natural$. -/
theorem nrdUnit_gFst (g : (gnatSqO ha0 hb0).G) :
    nrdUnit (gFst ha0 hb0 g) = (g : (MD × MD) × (Adeles F)ˣ).2 :=
  congrArg Prod.fst ((gnatSqO ha0 hb0).ν_fst g)

theorem nrdUnit_gSnd (g : (gnatSqO ha0 hb0).G) :
    nrdUnit (gSnd ha0 hb0 g) = (g : (MD × MD) × (Adeles F)ˣ).2 :=
  congrArg Prod.snd ((gnatSqO ha0 hb0).ν_fst g)

theorem nrdUnit_gFst_eq_gSnd (g : (gnatSqO ha0 hb0).G) : nrdUnit (gFst ha0 hb0 g) = nrdUnit (gSnd ha0 hb0 g) :=
  (nrdUnit_gFst ha0 hb0 g).trans (nrdUnit_gSnd ha0 hb0 g).symm

/-- The local pair $(\alpha_v,\beta_v)$ at a finite place. -/
def pairV (v : HeightOneSpectrum (𝓞 F)) :
    (gnatSqO ha0 hb0).G →* sqPair (algebraMap F (v.adicCompletion F) (a : F)) (algebraMap F (v.adicCompletion F) (b : F)) :=
  (((unitAtA (a : F) (b : F) v).comp (gFst ha0 hb0)).prod ((unitAtA (a : F) (b : F) v).comp (gSnd ha0 hb0))).codRestrict _
    fun g => by
      rw [mem_sqPair]
      change nrd ((unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) =
        nrd ((unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v)
      rw [nrd_unitAtA, nrd_unitAtA, nrdUnit_gFst_eq_gSnd]

theorem pairV_fst (v : HeightOneSpectrum (𝓞 F)) (g : (gnatSqO ha0 hb0).G) :
    ((pairV ha0 hb0 v g : sqPair _ _) : (QuatV (a : F) (b : F) v)ˣ × (QuatV (a : F) (b : F) v)ˣ).1 =
      unitAtA (a : F) (b : F) v (gFst ha0 hb0 g) := rfl

theorem pairV_snd (v : HeightOneSpectrum (𝓞 F)) (g : (gnatSqO ha0 hb0).G) :
    ((pairV ha0 hb0 v g : sqPair _ _) : (QuatV (a : F) (b : F) v)ˣ × (QuatV (a : F) (b : F) v)ˣ).2 =
      unitAtA (a : F) (b : F) v (gSnd ha0 hb0 g) := rfl

end Pairs

/-! ### The finite adelic map -/

section Fin

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

theorem coe_ne_zero' {x : 𝓞 F} (h : x ≠ 0) : (x : F) ≠ 0 := by exact_mod_cast h

/-- The local components of `sqFin`. -/
def sqFinFun (g : (gnatSqO ha0 hb0).G) : OAf QF :=
  ⟨fun v => (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF _), by
    filter_upwards [eventually_unitAtQ_mem_lamLocUnits _ _ (quatUnitsEquiv _ _ (gFst ha0 hb0 g)).2,
      eventually_unitAtQ_mem_lamLocUnits _ _ (quatUnitsEquiv _ _ (gSnd ha0 hb0 g)).2] with v h1 h2
    exact sqSOK_mem_stdStab v (fun w => valued_algebraMap_int_le_one w a) (fun w => valued_algebraMap_int_le_one w b)
      (coe_ne_zero' ha0) _ h1 h2⟩

@[simp] theorem sqFinFun_apply (g : (gnatSqO ha0 hb0).G) (v : HeightOneSpectrum (𝓞 F)) :
    sqFinFun ha0 hb0 g v = (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF _) :=
  rfl

/-- **$G^\natural(\mathbb A)\to SO(V)(\mathbb A_f)$**, $(\alpha,\beta,u)\mapsto(x\mapsto\alpha_vx\beta_v^{-1})_v$. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
def sqFin : (gnatSqO ha0 hb0).G →* SOAf Q₀ where
  toFun g := ⟨sqFinFun ha0 hb0 g, fun v => (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g)).2⟩
  map_one' := by
    ext v : 2
    simp only [sqFinFun_apply, map_one]
    simp
  map_mul' g h := by
    ext v : 2
    simp only [sqFinFun_apply, map_mul]
    simp

@[simp] theorem sqFin_apply (g : (gnatSqO ha0 hb0).G) (v : HeightOneSpectrum (𝓞 F)) :
    ((sqFin ha0 hb0 g : SOAf Q₀) : OAf QF) v =
      (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF _) := rfl

/-- Continuity of one local component. -/
theorem continuous_sqSOK_pairV (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun g : (gnatSqO ha0 hb0).G =>
      (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF (v.adicCompletion F)) := by
  set A : F := (a : F)
  set B : F := (b : F)
  have hc1 : Continuous fun g : (gnatSqO ha0 hb0).G =>
      ((unitAtA A B v (gFst ha0 hb0 g) : (QuatV A B v)ˣ) : QuatV A B v) :=
    Units.continuous_val.comp ((continuous_unitAtA A B v).comp (continuous_gFst ha0 hb0))
  have hc1' : Continuous fun g : (gnatSqO ha0 hb0).G =>
      (((unitAtA A B v (gFst ha0 hb0 g))⁻¹ : (QuatV A B v)ˣ) : QuatV A B v) :=
    Units.continuous_coe_inv.comp ((continuous_unitAtA A B v).comp (continuous_gFst ha0 hb0))
  have hc2 : Continuous fun g : (gnatSqO ha0 hb0).G =>
      ((unitAtA A B v (gSnd ha0 hb0 g) : (QuatV A B v)ˣ) : QuatV A B v) :=
    Units.continuous_val.comp ((continuous_unitAtA A B v).comp (continuous_gSnd ha0 hb0))
  have hc2' : Continuous fun g : (gnatSqO ha0 hb0).G =>
      (((unitAtA A B v (gSnd ha0 hb0 g))⁻¹ : (QuatV A B v)ˣ) : QuatV A B v) :=
    Units.continuous_coe_inv.comp ((continuous_unitAtA A B v).comp (continuous_gSnd ha0 hb0))
  refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
  · have e : ∀ g : (gnatSqO ha0 hb0).G,
        (((sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF (v.adicCompletion F)) :
          GL (Fin 4) (v.adicCompletion F)) : Matrix (Fin 4) (Fin 4) (v.adicCompletion F)) =
        sqMat ((unitAtA A B v (gFst ha0 hb0 g) : (QuatV A B v)ˣ) : QuatV A B v)
          (((unitAtA A B v (gSnd ha0 hb0 g))⁻¹ : (QuatV A B v)ˣ) : QuatV A B v) := fun g => by
      rw [sqSOK_coe, sqSO_val]; rfl
    refine (continuous_congr e).2 ?_
    exact continuous_sqMat_comp _ _ (continuous_re_loc _ _ |>.comp hc1) (continuous_imI_loc _ _ |>.comp hc1)
      (continuous_imJ_loc _ _ |>.comp hc1) (continuous_imK_loc _ _ |>.comp hc1)
      (continuous_re_loc _ _ |>.comp hc2') (continuous_imI_loc _ _ |>.comp hc2')
      (continuous_imJ_loc _ _ |>.comp hc2') (continuous_imK_loc _ _ |>.comp hc2')
  · have e : ∀ g : (gnatSqO ha0 hb0).G,
        ((((sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF (v.adicCompletion F)) :
          GL (Fin 4) (v.adicCompletion F))⁻¹ : GL (Fin 4) (v.adicCompletion F)) :
            Matrix (Fin 4) (Fin 4) (v.adicCompletion F)) =
        sqMat (((unitAtA A B v (gFst ha0 hb0 g))⁻¹ : (QuatV A B v)ˣ) : QuatV A B v)
          ((unitAtA A B v (gSnd ha0 hb0 g) : (QuatV A B v)ˣ) : QuatV A B v) := fun g => by
      rw [sqSOK_coe, ← Subgroup.coe_inv, sqSO_inv_val]; rfl
    refine (continuous_congr e).2 ?_
    exact continuous_sqMat_comp _ _ (continuous_re_loc _ _ |>.comp hc1') (continuous_imI_loc _ _ |>.comp hc1')
      (continuous_imJ_loc _ _ |>.comp hc1') (continuous_imK_loc _ _ |>.comp hc1')
      (continuous_re_loc _ _ |>.comp hc2) (continuous_imI_loc _ _ |>.comp hc2)
      (continuous_imJ_loc _ _ |>.comp hc2) (continuous_imK_loc _ _ |>.comp hc2)

/-- **`sqFin` is continuous**: on the open subgroup where $\alpha_f,\beta_f\in\hat\Lambda^\times$ it factors through
$\prod_vO(\mathfrak o_v^4)$ (as `continuous_conjFin`). -/
theorem continuous_sqFin : Continuous (sqFin ha0 hb0) := by
  refine continuous_of_continuousAt_one _ ?_
  set U : Set (gnatSqO ha0 hb0).G := {g | (quatUnitsEquiv _ _ (gFst ha0 hb0 g)).2 ∈ lamHatUnits (a : F) (b : F) ∧
    (quatUnitsEquiv _ _ (gSnd ha0 hb0 g)).2 ∈ lamHatUnits (a : F) (b : F)}
  have hUo : IsOpen U :=
    ((isOpen_lamHatUnits _ _).preimage (continuous_snd.comp ((quatUnitsEquiv _ _).continuous.comp
      (continuous_gFst ha0 hb0)))).inter
    ((isOpen_lamHatUnits _ _).preimage (continuous_snd.comp ((quatUnitsEquiv _ _).continuous.comp
      (continuous_gSnd ha0 hb0))))
  have hU : U ∈ 𝓝 (1 : (gnatSqO ha0 hb0).G) := hUo.mem_nhds (by
    refine ⟨?_, ?_⟩ <;> simp only [map_one, Prod.snd_one] <;> exact one_mem_lamHatUnits _ _)
  have hmem : ∀ g ∈ U, ∀ v, (sqSOK (v.adicCompletion F) (coe_ne_zero' ha0) (pairV ha0 hb0 v g) : orthGroup QF _) ∈
      stdStab QF v := fun g hg v =>
    sqSOK_mem_stdStab v (fun w => valued_algebraMap_int_le_one w a) (fun w => valued_algebraMap_int_le_one w b)
      (coe_ne_zero' ha0) _ ((mem_lamHatUnits_iff _ _ _).1 hg.1 v) ((mem_lamHatUnits_iff _ _ _).1 hg.2 v)
  let φ : U → ∀ v, (stdStab QF v : Set (orthGroup QF (v.adicCompletion F))) :=
    fun g v => ⟨_, hmem g.1 g.2 v⟩
  have hφ : Continuous φ := continuous_pi fun v =>
    ((continuous_sqSOK_pairV ha0 hb0 v).comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous fun g : U => ((sqFin ha0 hb0 g.1 : SOAf Q₀) : OAf QF) := by
    have := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup QF (v.adicCompletion F))
      (A := fun v => (stdStab QF v : Set (orthGroup QF (v.adicCompletion F)))) (𝓕 := cofinite)).continuous.comp hφ
    refine this.congr fun g => ?_
    ext v : 1
    rfl
  have hon : ContinuousOn (fun g => ((sqFin ha0 hb0 g : SOAf Q₀) : OAf QF)) U :=
    continuousOn_iff_continuous_domRestrict.2 hcomp
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff).2 (hon.continuousAt hU)

end Fin

/-! ### The archimedean map -/

section Inf

/-- $D\otimes_{F,\sigma_w}\mathbb R$. -/
abbrev HRe (a b : 𝓞 F) (w : {w : InfinitePlace F // w.IsReal}) : Type :=
  ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)]

/-- $D\otimes_{F,\tau_w}\mathbb C$. -/
abbrev HCx (a b : 𝓞 F) (w : {w : InfinitePlace F // w.IsComplex}) : Type :=
  ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)]

theorem archSOC_ext' {n : ℕ} {Q : QuadForm ℂ n} {g h : ArchSOC Q} (e : ArchSOC.incl Q g = ArchSOC.incl Q h) :
    g = h := Subtype.ext e

variable {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "Q₀" => qSq a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qSq a b)

/-- The local pair at a real place. -/
def pairR (w : {w : InfinitePlace F // w.IsReal}) :
    (gnatSqO ha0 hb0).G →* sqPair (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) :=
  (((unitAtR (a : F) (b : F) w).comp (gFst ha0 hb0)).prod ((unitAtR (a : F) (b : F) w).comp (gSnd ha0 hb0))).codRestrict _
    fun g => by
      rw [mem_sqPair]
      change nrd ((unitAtR (a : F) (b : F) w (gFst ha0 hb0 g) :
          (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ) :
          ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)]) =
        nrd ((unitAtR (a : F) (b : F) w (gSnd ha0 hb0 g) :
          (ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])ˣ) :
          ℍ[ℝ, embedding_of_isReal w.2 (a : F), embedding_of_isReal w.2 (b : F)])
      rw [nrd_unitAtR, nrd_unitAtR, nrdUnit_gFst_eq_gSnd]

/-- The local pair at a complex place. -/
def pairC (w : {w : InfinitePlace F // w.IsComplex}) :
    (gnatSqO ha0 hb0).G →* sqPair (w.1.embedding (a : F)) (w.1.embedding (b : F)) :=
  (((unitAtC (a : F) (b : F) w).comp (gFst ha0 hb0)).prod ((unitAtC (a : F) (b : F) w).comp (gSnd ha0 hb0))).codRestrict _
    fun g => by
      rw [mem_sqPair]
      change nrd ((unitAtC (a : F) (b : F) w (gFst ha0 hb0 g) :
          (ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)])ˣ) : ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)]) =
        nrd ((unitAtC (a : F) (b : F) w (gSnd ha0 hb0 g) :
          (ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)])ˣ) : ℍ[ℂ, w.1.embedding (a : F), w.1.embedding (b : F)])
      rw [nrd_unitAtC, nrd_unitAtC, nrdUnit_gFst_eq_gSnd]

theorem pairR_fst (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatSqO ha0 hb0).G) :
    ((pairR ha0 hb0 w g : sqPair _ _) : (HRe a b w)ˣ × (HRe a b w)ˣ).1 = unitAtR (a : F) (b : F) w (gFst ha0 hb0 g) :=
  rfl
theorem pairR_snd (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatSqO ha0 hb0).G) :
    ((pairR ha0 hb0 w g : sqPair _ _) : (HRe a b w)ˣ × (HRe a b w)ˣ).2 = unitAtR (a : F) (b : F) w (gSnd ha0 hb0 g) :=
  rfl
theorem pairC_fst (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatSqO ha0 hb0).G) :
    ((pairC ha0 hb0 w g : sqPair _ _) : (HCx a b w)ˣ × (HCx a b w)ˣ).1 = unitAtC (a : F) (b : F) w (gFst ha0 hb0 g) :=
  rfl
theorem pairC_snd (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatSqO ha0 hb0).G) :
    ((pairC ha0 hb0 w g : sqPair _ _) : (HCx a b w)ˣ × (HCx a b w)ˣ).2 = unitAtC (a : F) (b : F) w (gSnd ha0 hb0 g) :=
  rfl

theorem sqSO_mem_soReal (w : {w : InfinitePlace F // w.IsReal})
    (p : sqPair (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F))) :
    (sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 (coe_ne_zero' ha0)) p :
      GL (Fin 4) ℝ) ∈ soReal (QRe Q₀ w) := by
  have h := sqSO_hessian (embedding_of_isReal w.2) a b (coe_ne_zero' ha0) p
  rw [mem_soReal_iff, QRe, hessian_map_NF]
  exact ⟨by convert h.1 using 3, by convert h.2 using 2⟩

theorem sqSO_mem_soC (w : {w : InfinitePlace F // w.IsComplex})
    (p : sqPair (w.1.embedding (a : F)) (w.1.embedding (b : F))) :
    (sqSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 (coe_ne_zero' ha0)) p :
      GL (Fin 4) ℂ) ∈ soC (QCx Q₀ w) := by
  obtain ⟨h1, h2⟩ := sqSO_hessian w.1.embedding a b (coe_ne_zero' ha0) p
  rw [mem_soC_iff, gramC, QCx, hessian_map_NF]
  refine ⟨?_, by convert h2 using 2⟩
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1

/-- The real component as a matrix: $g\mapsto(x\mapsto\alpha_wx\beta_w^{-1})\in\mathrm{GL}_4(\mathbb R)$. -/
def sqGLR (w : {w : InfinitePlace F // w.IsReal}) : (gnatSqO ha0 hb0).G →* GL (Fin 4) ℝ :=
  (SO (V0Form (embedding_of_isReal w.2 (a : F)) (embedding_of_isReal w.2 (b : F)) 1)).subtype.comp
    ((sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2)) ((map_ne_zero _).2 (coe_ne_zero' ha0))).comp
      (pairR ha0 hb0 w))

/-- The complex component as a matrix. -/
def sqGLC (w : {w : InfinitePlace F // w.IsComplex}) : (gnatSqO ha0 hb0).G →* GL (Fin 4) ℂ :=
  (SO (V0Form (w.1.embedding (a : F)) (w.1.embedding (b : F)) 1)).subtype.comp
    ((sqSO (two_ne_zero_of_ringHom w.1.embedding) ((map_ne_zero _).2 (coe_ne_zero' ha0))).comp (pairC ha0 hb0 w))

theorem sqGLR_apply (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatSqO ha0 hb0).G) :
    sqGLR ha0 hb0 w g = sqSO (two_ne_zero_of_ringHom (embedding_of_isReal w.2))
      ((map_ne_zero _).2 (coe_ne_zero' ha0)) (pairR ha0 hb0 w g) := by
  simp only [sqGLR, MonoidHom.comp_apply, Subgroup.coe_subtype]

theorem sqGLC_apply (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatSqO ha0 hb0).G) :
    sqGLC ha0 hb0 w g = sqSO (two_ne_zero_of_ringHom w.1.embedding)
      ((map_ne_zero _).2 (coe_ne_zero' ha0)) (pairC ha0 hb0 w g) := by
  simp only [sqGLC, MonoidHom.comp_apply, Subgroup.coe_subtype]

/-- The real component $G^\natural(\mathbb A)\to SO(Q^{\sigma_w})(\mathbb R)$. -/
def sqR (w : {w : InfinitePlace F // w.IsReal}) : (gnatSqO ha0 hb0).G →* ArchSO (QRe Q₀ w) :=
  ((sqGLR ha0 hb0 w).codRestrict (soReal (QRe Q₀ w)) fun g => by
    rw [sqGLR_apply]; exact sqSO_mem_soReal ha0 w (pairR ha0 hb0 w g) :)

/-- The complex component $G^\natural(\mathbb A)\to SO(Q^{\tau_w})(\mathbb C)$. -/
def sqC (w : {w : InfinitePlace F // w.IsComplex}) : (gnatSqO ha0 hb0).G →* ArchSOC (QCx Q₀ w) :=
  ((sqGLC ha0 hb0 w).codRestrict (soC (QCx Q₀ w)) fun g => by
    rw [sqGLC_apply]; exact sqSO_mem_soC ha0 w (pairC ha0 hb0 w g) :)

theorem sqR_incl (w : {w : InfinitePlace F // w.IsReal}) (g : (gnatSqO ha0 hb0).G) :
    ArchSO.incl _ (sqR ha0 hb0 w g) = sqGLR ha0 hb0 w g := rfl

theorem sqC_incl (w : {w : InfinitePlace F // w.IsComplex}) (g : (gnatSqO ha0 hb0).G) :
    ArchSOC.incl _ (sqC ha0 hb0 w g) = sqGLC ha0 hb0 w g := rfl

/-- **$G^\natural(\mathbb A)\to G_\infty$**, $(\alpha,\beta,u)\mapsto(x\mapsto\alpha_wx\beta_w^{-1})_{w\mid\infty}$. -/
@[kb "weil1982" "§3.7, p. 65 [unverified page]"]
def sqInf : (gnatSqO ha0 hb0).G →* GInfSO Q₀ :=
  (MonoidHom.pi fun w => sqR ha0 hb0 w).prod (MonoidHom.pi fun w => sqC ha0 hb0 w)

set_option maxHeartbeats 1000000 in
theorem continuous_sqInf : Continuous (sqInf ha0 hb0) := by
  set A : F := (a : F)
  set B : F := (b : F)
  have hcR : ∀ (c : QuatAdele A B → Adeles F), Continuous c → ∀ f : (gnatSqO ha0 hb0).G → (QuatAdele A B)ˣ,
      Continuous f → ∀ w : {w : InfinitePlace F // w.IsReal}, Continuous fun g => (c (f g : QuatAdele A B)).1.1 w :=
    fun c hc f hf w => (continuous_apply w).comp (continuous_fst.comp (continuous_fst.comp
      (hc.comp (Units.continuous_val.comp hf))))
  have hcC : ∀ (c : QuatAdele A B → Adeles F), Continuous c → ∀ f : (gnatSqO ha0 hb0).G → (QuatAdele A B)ˣ,
      Continuous f → ∀ w : {w : InfinitePlace F // w.IsComplex}, Continuous fun g => (c (f g : QuatAdele A B)).1.2 w :=
    fun c hc f hf w => (continuous_apply w).comp (continuous_snd.comp (continuous_fst.comp
      (hc.comp (Units.continuous_val.comp hf))))
  have h1 := continuous_gFst ha0 hb0
  have h2 := continuous_gSnd ha0 hb0
  have h1' : Continuous fun g => (gFst ha0 hb0 g)⁻¹ := h1.inv
  have h2' : Continuous fun g => (gSnd ha0 hb0 g)⁻¹ := h2.inv
  have r0 := continuous_re A B; have r1 := continuous_imI A B
  have r2 := continuous_imJ A B; have r3 := continuous_imK A B
  refine Continuous.prodMk (continuous_pi fun w => ?_) (continuous_pi fun w => ?_)
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · have e : ∀ g : (gnatSqO ha0 hb0).G, ((ArchSO.incl _ (sqR ha0 hb0 w g) : GL (Fin 4) ℝ) :
          Matrix (Fin 4) (Fin 4) ℝ) = sqMat ((unitAtR A B w (gFst ha0 hb0 g) : (HRe a b w)ˣ) : HRe a b w)
            ((unitAtR A B w (gSnd ha0 hb0 g)⁻¹ : (HRe a b w)ˣ) : HRe a b w) := fun g => by
        rw [sqR_incl, sqGLR_apply, sqSO_val, pairR_fst, pairR_snd, map_inv]
      refine (continuous_congr e).2 ?_
      exact continuous_sqMat_comp _ _ (hcR _ r0 _ h1 w) (hcR _ r1 _ h1 w) (hcR _ r2 _ h1 w) (hcR _ r3 _ h1 w)
        (hcR _ r0 _ h2' w) (hcR _ r1 _ h2' w) (hcR _ r2 _ h2' w) (hcR _ r3 _ h2' w)
    · have e : ∀ g : (gnatSqO ha0 hb0).G, ((((ArchSO.incl _ (sqR ha0 hb0 w g) : GL (Fin 4) ℝ))⁻¹ : GL (Fin 4) ℝ) :
          Matrix (Fin 4) (Fin 4) ℝ) = sqMat ((unitAtR A B w (gFst ha0 hb0 g)⁻¹ : (HRe a b w)ˣ) : HRe a b w)
            ((unitAtR A B w (gSnd ha0 hb0 g) : (HRe a b w)ˣ) : HRe a b w) := fun g => by
        rw [sqR_incl, sqGLR_apply, ← Subgroup.coe_inv, sqSO_inv_val, pairR_fst, pairR_snd, map_inv]
      refine (continuous_congr e).2 ?_
      exact continuous_sqMat_comp _ _ (hcR _ r0 _ h1' w) (hcR _ r1 _ h1' w) (hcR _ r2 _ h1' w) (hcR _ r3 _ h1' w)
        (hcR _ r0 _ h2 w) (hcR _ r1 _ h2 w) (hcR _ r2 _ h2 w) (hcR _ r3 _ h2 w)
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · have e : ∀ g : (gnatSqO ha0 hb0).G, ((ArchSOC.incl _ (sqC ha0 hb0 w g) : GL (Fin 4) ℂ) :
          Matrix (Fin 4) (Fin 4) ℂ) = sqMat ((unitAtC A B w (gFst ha0 hb0 g) : (HCx a b w)ˣ) : HCx a b w)
            ((unitAtC A B w (gSnd ha0 hb0 g)⁻¹ : (HCx a b w)ˣ) : HCx a b w) := fun g => by
        rw [sqC_incl, sqGLC_apply, sqSO_val, pairC_fst, pairC_snd, map_inv]
      refine (continuous_congr e).2 ?_
      exact continuous_sqMat_comp _ _ (hcC _ r0 _ h1 w) (hcC _ r1 _ h1 w) (hcC _ r2 _ h1 w) (hcC _ r3 _ h1 w)
        (hcC _ r0 _ h2' w) (hcC _ r1 _ h2' w) (hcC _ r2 _ h2' w) (hcC _ r3 _ h2' w)
    · have e : ∀ g : (gnatSqO ha0 hb0).G, ((((ArchSOC.incl _ (sqC ha0 hb0 w g) : GL (Fin 4) ℂ))⁻¹ : GL (Fin 4) ℂ) :
          Matrix (Fin 4) (Fin 4) ℂ) = sqMat ((unitAtC A B w (gFst ha0 hb0 g)⁻¹ : (HCx a b w)ˣ) : HCx a b w)
            ((unitAtC A B w (gSnd ha0 hb0 g) : (HCx a b w)ˣ) : HCx a b w) := fun g => by
        rw [sqC_incl, sqGLC_apply, ← Subgroup.coe_inv, sqSO_inv_val, pairC_fst, pairC_snd, map_inv]
      refine (continuous_congr e).2 ?_
      exact continuous_sqMat_comp (fun t => ((unitAtC A B w (gFst ha0 hb0 t)⁻¹ : (HCx a b w)ˣ) : HCx a b w))
        (fun t => ((unitAtC A B w (gSnd ha0 hb0 t) : (HCx a b w)ˣ) : HCx a b w))
        (hcC _ r0 _ h1' w) (hcC _ r1 _ h1' w) (hcC _ r2 _ h1' w) (hcC _ r3 _ h1' w)
        (hcC _ r0 _ h2 w) (hcC _ r1 _ h2 w) (hcC _ r2 _ h2 w) (hcC _ r3 _ h2 w)

end Inf

end QuadFormsKB.Tamagawa.Measure.Weil
