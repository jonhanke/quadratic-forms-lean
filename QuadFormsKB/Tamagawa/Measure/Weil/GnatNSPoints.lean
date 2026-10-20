/-
# Non-square discriminant: the global points $\Phi(\pi(\Gamma)) = SO(V)(F)$

**Layer:** as `GnatNSGlobal`.

**Defines/proves**
* `nsF : Gnat a b d →* soSub QF F`, `nsF_surjective`;
* `bcRing_quatDiagRing`: $\Theta^{-1}$ of a global point of $D'$ is a global point of $D_E$ (`quatBaseChange_quatQuadDiag`);
* **`nsAdele_diag`**, **`map_gam_nsAdele`**, **`map_gamP_nsPEquiv`**: $\Phi(\pi(\Gamma)) = $ `GammaSOAdele (qNS a b d)`.

Source: Weil 1982, §3.7, pp. 64–65 [unverified]; §2.4, p. 23.
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSGlobal

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain Topology
  Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Lattices QuadFormsKB.Siegel
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F} (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F)) (hA0 : A' ≠ 0) (hB0 : B' ≠ 0)
  (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)

local notation "Q₀" => qNS a b d
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (qNS a b d)
local notation "MQ" => (QuatQuadAdele F (d : F) (a : F) (b : F))ˣ

/-! ### $G^\natural(F)\to SO(V)(F)$ -/

theorem qNS_map_self : QF = V0Form (a : F) (b : F) (d : F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qNS, V0Form, QuadForm.diag, QuadForm.map]

/-- $\varphi$ over $F$ as a matrix. -/
def nsGLF : Gnat (a : F) (b : F) (d : F) →* GL (Fin 4) F :=
  (SO (V0Form (a : F) (b : F) (d : F))).subtype.comp (phiSO (two_ne_zero : (2 : F) ≠ 0) ha0 hd0)

theorem nsGLF_apply (ξ : Gnat (a : F) (b : F) (d : F)) :
    nsGLF ha0 hd0 ξ = phiSO (two_ne_zero : (2 : F) ≠ 0) ha0 hd0 ξ := by
  simp only [nsGLF, MonoidHom.comp_apply, Subgroup.coe_subtype]

theorem nsGLF_mem (ξ : Gnat (a : F) (b : F) (d : F)) : nsGLF ha0 hd0 ξ ∈ orthGroup QF F := by
  rw [mem_orthGroup, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, nsGLF_apply]
  have := ((mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0)).1 (phiSO two_ne_zero ha0 hd0 ξ).2).2
  rw [qNS_map_self]
  exact this

theorem nsGLF_det (ξ : Gnat (a : F) (b : F) (d : F)) : (nsGLF ha0 hd0 ξ).val.det = 1 := by
  rw [nsGLF_apply]
  exact (phiSO two_ne_zero ha0 hd0 ξ).2.1

/-- **$G^\natural(F)\to SO(V)(F)$**. -/
def nsF : Gnat (a : F) (b : F) (d : F) →* soSub QF F :=
  ((nsGLF ha0 hd0).codRestrict (orthGroup QF F) (nsGLF_mem ha0 hd0)).codRestrict (soSub QF F) (nsGLF_det ha0 hd0)

theorem nsF_coe (ξ : Gnat (a : F) (b : F) (d : F)) :
    (((nsF ha0 hd0 ξ : soSub QF F) : orthGroup QF F) : GL (Fin 4) F) = nsGLF ha0 hd0 ξ := rfl

include hb0 in
theorem nsF_surjective : Function.Surjective (nsF (a := a) (b := b) (d := d) ha0 hd0) := by
  intro γ
  have hmem : ((γ : orthGroup QF F) : GL (Fin 4) F) ∈ SO (V0Form (a : F) (b : F) (d : F)) := by
    rw [mem_SO_iff_hessian (two_ne_zero : (2 : F) ≠ 0)]
    have h1 := (mem_orthGroup QF).1 (γ : orthGroup QF F).2
    rw [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id,
      show (QF).hessian = (V0Form (a : F) (b : F) (d : F)).hessian by rw [qNS_map_self]] at h1
    exact ⟨mem_soSub.1 γ.2, h1⟩
  obtain ⟨ξ, hξ⟩ := phiSO_surjective (two_ne_zero : (2 : F) ≠ 0) ha0 hb0 hd0 ⟨_, hmem⟩
  refine ⟨ξ, Subtype.ext (Subtype.ext ?_)⟩
  rw [nsF_coe, nsGLF_apply, hξ]

/-! ### Global points of $D'$ and of $D_E$ -/

variable (a b d) in
/-- The diagonal $D_E\to D_E\otimes\mathbb A_F$ (source written as `DE a b d`). -/
def deDiag : DE (a : F) (b : F) (d : F) →+* QuatQuadAdele F (d : F) (a : F) (b : F) :=
  QuaternionAlgebra.mapRingHom (quadDiag (d : F)) (QuadraticAlgebra.ext rfl (map_zero _)) (map_zero _)
    (QuadraticAlgebra.ext rfl (map_zero _))

@[simp] theorem deDiag_re (x : DE (a : F) (b : F) (d : F)) : (deDiag a b d x).re = quadDiag (d : F) x.re := rfl
@[simp] theorem deDiag_imI (x : DE (a : F) (b : F) (d : F)) : (deDiag a b d x).imI = quadDiag (d : F) x.imI := rfl
@[simp] theorem deDiag_imJ (x : DE (a : F) (b : F) (d : F)) : (deDiag a b d x).imJ = quadDiag (d : F) x.imJ := rfl
@[simp] theorem deDiag_imK (x : DE (a : F) (b : F) (d : F)) : (deDiag a b d x).imK = quadDiag (d : F) x.imK := rfl

/-- The diagonal on units. -/
abbrev deDiagUnit : (DE (a : F) (b : F) (d : F))ˣ →* MQ := Units.map (deDiag a b d).toMonoidHom

/-- $D_E\to D'$, coordinatewise `quadField` (source written as `DE a b d`). -/
def deFieldK : DE (a : F) (b : F) (d : F) →+* ℍ[K, algebraMap F K (a : F), algebraMap F K (b : F)] :=
  QuaternionAlgebra.mapRingHom (quadField hb₁) (by simp [quadField]) (map_zero _) (by simp [quadField])

include hb₀ in
theorem deFieldK_bijective : Function.Bijective (deFieldK hb₁ (a := a) (b := b)) := by
  have hq := quadField_bijective (d := (d : F)) hb₀ hb₁
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · exact QuaternionAlgebra.ext (hq.1 (congrArg QuaternionAlgebra.re h)) (hq.1 (congrArg QuaternionAlgebra.imI h))
      (hq.1 (congrArg QuaternionAlgebra.imJ h)) (hq.1 (congrArg QuaternionAlgebra.imK h))
  · obtain ⟨x0, h0⟩ := hq.2 y.re
    obtain ⟨x1, h1⟩ := hq.2 y.imI
    obtain ⟨x2, h2⟩ := hq.2 y.imJ
    obtain ⟨x3, h3⟩ := hq.2 y.imK
    exact ⟨⟨x0, x1, x2, x3⟩, QuaternionAlgebra.ext h0 h1 h2 h3⟩

theorem quatBaseChange_deDiag (x : DE (a : F) (b : F) (d : F)) :
    quatBaseChange hb₀ hb₁ (a : F) (b : F) (deDiag a b d x) = quatDiagRing _ _ (deFieldK hb₁ x) :=
  QuaternionAlgebra.ext (quadBaseChange_quadDiag hb₀ hb₁ _) (quadBaseChange_quadDiag hb₀ hb₁ _)
    (quadBaseChange_quadDiag hb₀ hb₁ _) (quadBaseChange_quadDiag hb₀ hb₁ _)

theorem dV_deDiag (v : HeightOneSpectrum (𝓞 F)) (ξ : DE (a : F) (b : F) (d : F)) :
    dV (a := a) (b := b) (d := d) v (deDiag a b d ξ) = deField (algebraMap F (v.adicCompletion F)) ξ :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl) (QuadraticAlgebra.ext rfl rfl)
    (QuadraticAlgebra.ext rfl rfl)

theorem dR_deDiag (w : {w : InfinitePlace F // w.IsReal}) (ξ : DE (a : F) (b : F) (d : F)) :
    dR (a := a) (b := b) (d := d) w (deDiag a b d ξ) = deField (embedding_of_isReal w.2) ξ :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext (fAtR_diag w _) (fAtR_diag w _))
    (QuadraticAlgebra.ext (fAtR_diag w _) (fAtR_diag w _)) (QuadraticAlgebra.ext (fAtR_diag w _) (fAtR_diag w _))
    (QuadraticAlgebra.ext (fAtR_diag w _) (fAtR_diag w _))

theorem dC_deDiag (w : {w : InfinitePlace F // w.IsComplex}) (ξ : DE (a : F) (b : F) (d : F)) :
    dC (a := a) (b := b) (d := d) w (deDiag a b d ξ) = deField w.1.embedding ξ :=
  QuaternionAlgebra.ext (QuadraticAlgebra.ext (fAtC_diag w _) (fAtC_diag w _))
    (QuadraticAlgebra.ext (fAtC_diag w _) (fAtC_diag w _)) (QuadraticAlgebra.ext (fAtC_diag w _) (fAtC_diag w _))
    (QuadraticAlgebra.ext (fAtC_diag w _) (fAtC_diag w _))

/-- $\Theta^{-1}$ maps the global point $\xi'\in D'$ to the global point $x\in D_E$ with $\mathrm{quatField}(x) = \xi'$. -/
theorem bcRing_quatDiagRing (x : DE (a : F) (b : F) (d : F)) (ξ' : ℍ[K, A', B'])
    (hξ : quatParamEquiv hA' hB' ξ' = deFieldK hb₁ x) :
    bcRing hb₀ hb₁ hA' hB' (quatDiagRing (F := K) A' B' ξ') = deDiag a b d x := by
  apply (quatBaseChange hb₀ hb₁ (a : F) (b : F)).injective
  rw [quatBaseChange_deDiag]
  change quatBaseChange hb₀ hb₁ (a : F) (b : F) ((quatBaseChange hb₀ hb₁ (a : F) (b : F)).symm
    (quatParamEquiv (diag_eq_of_eq hA') (diag_eq_of_eq hB') (quatDiagRing (F := K) A' B' ξ'))) = _
  rw [RingEquiv.apply_symm_apply, ← hξ]
  rfl

theorem deDiag_star (x : DE (a : F) (b : F) (d : F)) : deDiag a b d (star x) = star (deDiag a b d x) := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;>
    simp [QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
      QuaternionAlgebra.imK_star, map_neg]

/-- The $F$-points of $G^\natural$ have $\operatorname{nrd}_E$ = an idele of $F$. -/
theorem deDiag_nrd (ξ : Gnat (a : F) (b : F) (d : F)) :
    (((deDiagUnit ((ξ : (DE (a : F) (b : F) (d : F))ˣ)) : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) *
      star ((deDiagUnit ((ξ : (DE (a : F) (b : F) (d : F))ˣ)) : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F))).re =
      (⟨diagRing F (nrdK (((ξ : (DE (a : F) (b : F) (d : F))ˣ)) : DE (a : F) (b : F) (d : F))), 0⟩ :
        QuadAdele F (d : F)) := by
  change (deDiag a b d (((ξ : (DE (a : F) (b : F) (d : F))ˣ)) : DE (a : F) (b : F) (d : F)) *
    star (deDiag a b d (((ξ : (DE (a : F) (b : F) (d : F))ˣ)) : DE (a : F) (b : F) (d : F)))).re = _
  rw [← deDiag_star, ← map_mul, mul_star_eq_nrdE, nrdE_eq_nrdK ξ.2]
  exact QuadraticAlgebra.ext rfl (map_zero _)

/-- **Compatibility with the global points** (non-square model): if $\Theta^{-1}(g_1)$ is the $F$-point $\xi\in G^\natural(F)$ then
$\Phi(g) = \varphi_\xi$ diagonally. -/
theorem nsAdele_diag (ξ : Gnat (a : F) (b : F) (d : F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G)
    (h : nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g = deDiagUnit ((ξ : (DE (a : F) (b : F) (d : F))ˣ))) :
    nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 g = diagSOAdele Q₀ (nsF ha0 hd0 ξ) := by
  set x : DE (a : F) (b : F) (d : F) := ((ξ : (DE (a : F) (b : F) (d : F))ˣ) : DE (a : F) (b : F) (d : F))
  set y : DE (a : F) (b : F) (d : F) := (((ξ : (DE (a : F) (b : F) (d : F))ˣ)⁻¹ : (DE (a : F) (b : F) (d : F))ˣ) :
    DE (a : F) (b : F) (d : F))
  have h1 : ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) = deDiag a b d x := by
    rw [h]; rfl
  have h2 : (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) : QuatQuadAdele F (d : F) (a : F) (b : F)) = deDiag a b d y := by
    rw [h, ← map_inv]; rfl
  refine Prod.ext (Prod.ext (funext fun w => archSO_ext ?_) (funext fun w => archSOC_ext' ?_)) ?_
  · change nsGLR hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g =
      Matrix.GeneralLinearGroup.map (embedding_of_isReal w.2) (nsGLF ha0 hd0 ξ)
    apply Units.ext
    rw [nsGLR_apply, nsGLF_apply, phiSO_val]
    change _ = (((phiSO (two_ne_zero : (2 : F) ≠ 0) ha0 hd0 ξ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map (embedding_of_isReal w.2)
    rw [phiSO_val, ← nsMat_map]
    have e1 : (((nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEre a b d w)ˣ) : DEre a b d w) =
        deField (embedding_of_isReal w.2) x := by rw [nsPairR_val, h1, dR_deDiag]
    have e2 : ((((nsPairR hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEre a b d w)ˣ))⁻¹ : (DEre a b d w)ˣ) =
        Units.map (dR (a := a) (b := b) (d := d) w).toMonoidHom ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹) := by
      rw [map_inv]; rfl
    rw [e1, e2]
    change nsMat _ (dR (a := a) (b := b) (d := d) w (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F))) = _
    rw [h2, dR_deDiag]
  · change nsGLC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 w g = Matrix.GeneralLinearGroup.map w.1.embedding (nsGLF ha0 hd0 ξ)
    apply Units.ext
    rw [nsGLC_apply, nsGLF_apply, phiSO_val]
    change _ = (((phiSO (two_ne_zero : (2 : F) ≠ 0) ha0 hd0 ξ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map w.1.embedding
    rw [phiSO_val, ← nsMat_map]
    have e1 : (((nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEcx a b d w)ˣ) : DEcx a b d w) =
        deField w.1.embedding x := by rw [nsPairC_val, h1, dC_deDiag]
    have e2 : ((((nsPairC hb₀ hb₁ hA' hB' hA0 hB0 w g : Gnat _ _ _) : (DEcx a b d w)ˣ))⁻¹ : (DEcx a b d w)ˣ) =
        Units.map (dC (a := a) (b := b) (d := d) w).toMonoidHom ((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹) := by
      rw [map_inv]; rfl
    rw [e1, e2]
    change nsMat _ (dC (a := a) (b := b) (d := d) w (((nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g)⁻¹ : MQ) :
      QuatQuadAdele F (d : F) (a : F) (b : F))) = _
    rw [h2, dC_deDiag]
  · ext v : 3
    change ((nsSOK (v.adicCompletion F) a b d ha0 hd0 (nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g) :
      orthGroup QF (v.adicCompletion F)) : GL (Fin 4) (v.adicCompletion F)) =
        Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) (nsGLF ha0 hd0 ξ)
    have e1 : (((nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g : GnK (v.adicCompletion F) a b d) : DEK (v.adicCompletion F) a b d) :
        DEr (v.adicCompletion F) a b d) = deField (algebraMap F (v.adicCompletion F)) x := by
      rw [nsPairV_val, h1, dV_deDiag]
    have e2 : ((((nsPairV hb₀ hb₁ hA' hB' hA0 hB0 v g : GnK (v.adicCompletion F) a b d) :
        DEK (v.adicCompletion F) a b d)⁻¹ : DEK (v.adicCompletion F) a b d) : DEr (v.adicCompletion F) a b d) =
        deField (algebraMap F (v.adicCompletion F)) y := by
      rw [nsPairV_inv_val, h2, dV_deDiag]
    apply Units.ext
    rw [nsSOK_coe, nsGL_apply, nsGLF_apply, phiSO_val, e1, e2, nsMat_map]
    change _ = (((phiSO (two_ne_zero : (2 : F) ≠ 0) ha0 hd0 ξ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)).map (algebraMap F (v.adicCompletion F))
    rw [phiSO_val]

include hb0 in
/-- **$\Phi(\pi(\Gamma)) = SO(V)(F)$** (non-square model): the image of $G^\natural(F)$ is `GammaSOAdele`. -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]; §2.4, p. 23"]
theorem map_gam_nsAdele :
    (gnatBC bK 0 hb₀ hA0 hB0).gam.map (nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0) = GammaSOAdele Q₀ := by
  set eK := RingEquiv.ofBijective _ (deFieldK_bijective hb₀ hb₁ (a := a) (b := b))
  set pK := quatParamEquiv hA' hB'
  ext γ
  constructor
  · rintro ⟨g, ⟨⟨ξ', hξ'⟩, -⟩, rfl⟩
    set x : (DE (a : F) (b : F) (d : F))ˣ := Units.map eK.symm.toRingHom.toMonoidHom (Units.map pK.toRingHom.toMonoidHom ξ')
    have hx : pK (ξ' : ℍ[K, A', B']) = deFieldK hb₁ (x : DE (a : F) (b : F) (d : F)) := by
      change pK (ξ' : ℍ[K, A', B']) = eK (eK.symm (pK (ξ' : ℍ[K, A', B'])))
      rw [RingEquiv.apply_symm_apply]
    have hU : nsUnit hb₀ hb₁ hA' hB' hA0 hB0 g = deDiagUnit x := by
      apply Units.ext
      change bcRing hb₀ hb₁ hA' hB' ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1 : QuatAdele (F := K) A' B') = _
      rw [← hξ']
      exact bcRing_quatDiagRing hb₀ hb₁ hA' hB' _ _ hx
    have hxG : x ∈ Gnat (a : F) (b : F) (d : F) := by
      rw [mem_Gnat]
      have h1 := nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g
      rw [hU] at h1
      change (deDiag a b d (x : DE (a : F) (b : F) (d : F)) * star (deDiag a b d (x : DE (a : F) (b : F) (d : F)))).re = _
        at h1
      rw [← deDiag_star, ← map_mul, mul_star_eq_nrdE] at h1
      have h2 := congrArg QuadraticAlgebra.im h1
      change diagRing F (nrdE (x : DE (a : F) (b : F) (d : F))).im = 0 at h2
      exact diag_injective (h2.trans (map_zero (diagRing F)).symm)
    exact ⟨nsF ha0 hd0 ⟨x, hxG⟩, (nsAdele_diag hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 ⟨x, hxG⟩ g hU).symm⟩
  · rintro ⟨γ0, rfl⟩
    obtain ⟨ξ, rfl⟩ := nsF_surjective ha0 hb0 hd0 γ0
    set x : (DE (a : F) (b : F) (d : F))ˣ := (ξ : (DE (a : F) (b : F) (d : F))ˣ)
    set ξ' : (ℍ[K, A', B'])ˣ := Units.map pK.symm.toRingHom.toMonoidHom (Units.map eK.toRingHom.toMonoidHom x)
    have hx : pK (ξ' : ℍ[K, A', B']) = deFieldK hb₁ (x : DE (a : F) (b : F) (d : F)) := by
      change pK (pK.symm (eK (x : DE (a : F) (b : F) (d : F)))) = _
      rw [RingEquiv.apply_symm_apply]; rfl
    set g1 : (QuatAdele (F := K) A' B')ˣ := Units.map (quatDiagRing (F := K) A' B').toMonoidHom ξ'
    have hb : bcHom hb₀ hb₁ hA' hB' g1 = deDiagUnit x :=
      Units.ext (bcRing_quatDiagRing hb₀ hb₁ hA' hB' _ _ hx)
    set u : (Adeles F)ˣ := diagUnits F (Units.mk0 (nrdK (x : DE (a : F) (b : F) (d : F))) (nrdK_ne_zero ξ.2))
    have hnrd : nrdUnit g1 = adeleUnitsMap F K u := nrdUnit_eq_of_bcHom hb₀ hb₁ hA' hB' g1 u (by
      rw [hb]; exact deDiag_nrd ξ)
    let g : (gnatBC bK 0 hb₀ hA0 hB0).G := ⟨(g1, u), hnrd⟩
    refine ⟨g, ⟨⟨ξ', rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
    exact nsAdele_diag hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 ξ g hb

include hb0 in
/-- **$\Phi(\pi(\Gamma)) = SO(V)(F)$** on the quotient (non-square model). -/
@[kb "weil1982" "§3.7, pp. 64–65 [unverified]; §2.4, p. 23"]
theorem map_gamP_nsPEquiv :
    (gnatBC bK 0 hb₀ hA0 hB0).gamP.map (nsPEquiv hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0).toMulEquiv.toMonoidHom =
      GammaSOAdele Q₀ := by
  rw [← map_gam_nsAdele hb₀ hb₁ hA' hB' hA0 hB0 ha0 hb0 hd0]
  change ((gnatBC bK 0 hb₀ hA0 hB0).gam.map (gnatBC bK 0 hb₀ hA0 hB0).π).map _ = _
  rw [Subgroup.map_map]
  rfl

end QuadFormsKB.Tamagawa.Measure.Weil
