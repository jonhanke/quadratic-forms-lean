import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereLocalFin
import QuadFormsKB.Weil.ProductFormulas

/-!
# Good finite places for the adelic sphere

At every finite place $v$ where $\xi, w, G, G^{-1}$ are integral and $d$, $\det G$, $2m_0$, $4q(\xi)$, $q(w)$ are units
(`GoodFin`, true for almost all $v$: `eventually_goodFin`):

* **`secMulImage_good`**: $s_v(T_v\cap L_v)\,\iota_v(SO(L'_v)) = SO(L_v)$;
* **`cFin_good`**: the local constant $c_v$ is $1$;
* hence (`muLocSO_soStab_good`) $\mu_v(SO(L_v)) = \sigma_v(T_v\cap L_v)\,\mu'_v(SO(L'_v))$, the local orbital identity on
  the standard lattices (the local density identity in measure form, with weight $1$).
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.FibreDecomp QuadFormsKB.Tamagawa.Measure.FibreConst

variable {F : Type} [Field F] [NumberField F] {k : ℕ} {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

theorem distribHaarChar_adic_norm (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    (distribHaarChar (v.adicCompletion F) u : ℝ) = ‖(u : v.adicCompletion F)‖ := by
  have h := QuadFormsKB.WeilRep.modK_eq_norm v (Units.ne_zero u)
  rw [Analysis.Weil.modK_of_ne (Units.ne_zero u), Units.mk0_val] at h
  exact h

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

theorem eventually_notMem {x : 𝓞 F} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, x ∉ v.asIdeal := by
  have h0 : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
    have h_span_nezero : Ideal.span {x} ≠ 0 := by simp [hx]
    simp only [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  exact Filter.eventually_cofinite.mpr (by simpa using h0)

theorem norm_σV_eq_one {x : 𝓞 F} (hx : x ∉ v.asIdeal) : ‖σV v (algebraMap (𝓞 F) F x)‖ = 1 :=
  (NumberField.FinitePlace.norm_eq_one_iff_notMem F v x).mpr hx

/-- **Good finite places.** -/
def GoodFin : Prop :=
  S.GoodV v ∧ S.PAt (σV v) ∈ glInt v ∧ S.C.d ∉ v.asIdeal ∧ S.C.G.det ∉ v.asIdeal ∧ 2 * S.C.m₀ ∉ v.asIdeal

theorem eventually_goodFin (hρ : ρ ≠ 0) : ∀ᶠ v in Filter.cofinite, S.GoodFin v := by
  filter_upwards [S.eventually_goodV hρ, S.eventually_PAt_glInt, eventually_notMem S.C.hd,
    eventually_notMem S.C.hG, eventually_notMem (mul_ne_zero two_ne_zero S.C.hm)] with v h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The local constant is $1$ at good places.** -/
theorem cFin_good (hv : S.GoodFin v) : S.cFin v = 1 := by
  obtain ⟨-, -, hd, hG, hm⟩ := hv
  have h1 : ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac 1 S.C.G))‖ = 1 := by
    rw [show simJac 1 S.C.G = 1 ^ ((k + 1) * (k + 1 + 1) / 2) * S.C.G.det ^ (k + 1 + 1) from rfl, one_pow, one_mul]
    exact (NumberField.FinitePlace.norm_eq_one_iff_notMem F v _).mpr
      (fun h => hG ((Ideal.IsPrime.mem_of_pow_mem inferInstance _ h)))
  have hdn : ‖S.dV v‖ = 1 := norm_σV_eq_one v hd
  have hb : S.bPsi v = 1 := by
    rw [bPsi]
    have e1 : (distribHaarChar Fv (S.cPsi v) : ℝ) = 1 := by
      rw [distribHaarChar_adic_norm, cPsi, Units.val_mk0, norm_pow, norm_inv, hdn]; simp
    have e2 : (distribHaarChar Fv (Matrix.GeneralLinearGroup.det (S.psiGL v)) : ℝ) = 1 := by
      rw [distribHaarChar_adic_norm, Matrix.GeneralLinearGroup.val_det_apply, psiGL_val, Matrix.det_smul,
        norm_mul, norm_pow, norm_inv, hdn, PAt_val, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rw [norm_σV_eq_one v hG]; simp
    have e1' : (distribHaarChar Fv (S.cPsi v) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_one]; congr 1; exact NNReal.coe_eq_one.mp e1
    have e2' : (distribHaarChar Fv (Matrix.GeneralLinearGroup.det (S.psiGL v)) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_one]; congr 1; exact NNReal.coe_eq_one.mp e2
    rw [e1', e2', div_one]
  have hm' : absTwoM v S.C.m₀ = 1 := absTwoM_eq_one v hm
  rw [cFin, h1, hb, hm', ENNReal.ofReal_one, one_pow, inv_one, ENNReal.ofReal_one, one_mul, mul_one]

variable (Q₀ ρ) in
/-- The integral points of the local sphere. -/
def intSph : Set (sphV Q₀ ρ v) := {x | IntVec v x.1}

theorem glInt_mul {n : ℕ} {a b : GL (Fin n) Fv} (ha : a ∈ glInt v) (hb : b ∈ glInt v) : a * b ∈ glInt v := by
  rw [mem_glInt_iff] at ha hb ⊢
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact mul_mem_intMat v ha.1 hb.1
  · rw [_root_.mul_inv_rev, Units.val_mul]; exact mul_mem_intMat v hb.2 ha.2

theorem glInt_inv {n : ℕ} {a : GL (Fin n) Fv} (ha : a ∈ glInt v) : a⁻¹ ∈ glInt v := by
  rw [mem_glInt_iff] at ha ⊢; rw [inv_inv]; exact ⟨ha.2, ha.1⟩

theorem secSO_glInt (hv : S.GoodFin v) (y : sphV Q₀ ρ v) (hy : IntVec v y.1) :
    (((S.secSO hρ v y : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv) ∈ glInt v :=
  S.secFinGL_mem_glInt hρ hv.1 hy ((mem_sphV_iff Q₀ ρ v y.1).mp y.2)

/-- **At a good place, $s_v(T_v\cap L_v)\,\iota_v(SO(L'_v)) = SO(L_v)$.** -/
theorem secMulImage_good (hv : S.GoodFin v) :
    secMulImage (S.secSO hρ v) (S.iotaSO v) (intSph Q₀ ρ v) (soStabSO v S.C.Q' : Set (SOv v S.C.Q')) =
      (soStabSO v Q₀ : Set (SOv v Q₀)) := by
  ext g
  constructor
  · rintro ⟨y, hy, h, hh, rfl⟩
    show (((S.secSO hρ v y * S.iotaSO v h : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv) ∈ glInt v
    exact glInt_mul v (S.secSO_glInt hρ v hv y hy) (S.iotaV_mem_stdStab hv.2.1 hh)
  · intro hg
    have hg' : (((g : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv) ∈ glInt v := hg
    set x₀ := (S.sphereDataAt hρ (σV v)).x₀
    set G' : GL (Fin (k + 1)) Fv := (((g : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv)
    have hiso : G'.valᵀ * hesAt Q₀ (σV v) * G'.val = hesAt Q₀ (σV v) := (mem_orthGroup _).mp (g : orthGroup QF Fv).2
    have hy1 : G'.val *ᵥ x₀ ∈ sphV Q₀ ρ v := by
      rw [mem_sphV_iff, qH_mulVec_of_orth hiso, S.qH_sphereDataAt]
    set y : sphV Q₀ ρ v := ⟨G'.val *ᵥ x₀, hy1⟩
    have hyi : IntVec v y.1 := IntVec.mulVec v ((mem_glInt_iff v).mp hg').1 hv.1.2.2.1
    set M : SOv v Q₀ := (S.secSO hρ v y)⁻¹ * g
    set MG : GL (Fin (k + 1)) Fv := (((M : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv)
    have hMiso : MG.valᵀ * hesAt Q₀ (σV v) * MG.val = hesAt Q₀ (σV v) := (mem_orthGroup _).mp (M : orthGroup QF Fv).2
    have hMfix : MG.val *ᵥ x₀ = x₀ := by
      have hs := S.secFinGL_mulVec hρ v y.1 ((mem_sphV_iff Q₀ ρ v y.1).mp y.2)
      have e : MG = (((S.secSO hρ v y : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv)⁻¹ * G' := rfl
      rw [e, Units.val_mul, ← mulVec_mulVec]
      show _ *ᵥ y.1 = x₀
      conv_lhs => rw [← hs]
      rw [mulVec_mulVec, show (S.secFinGL hρ v y.1 _).val =
        (((S.secSO hρ v y : SOv v Q₀) : orthGroup QF Fv) : GL (Fin (k + 1)) Fv).val from rfl,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have hMint : MG ∈ glInt v := glInt_mul v (glInt_inv v (S.secSO_glInt hρ v hv y hyi)) hg'
    obtain ⟨h, e1, e2, e3, e4, e5⟩ := S.exists_conjBlockGL_eq hρ (σV v) hMiso hMfix
    have hhint : h ∈ glInt v := by
      rw [mem_glInt_iff] at hMint ⊢
      rw [e4, e5]
      exact ⟨S.blockOf_mem_intMat hv.2.1 hMint.1, S.blockOf_mem_intMat hv.2.1 hMint.2⟩
    have hdet : h.val.det = 1 := by rw [e3]; exact (M : SOv v Q₀).2
    let h' : SOv v S.C.Q' := ⟨⟨h, (mem_orthGroup _).mpr e2⟩, hdet⟩
    refine ⟨y, hyi, h', hhint, ?_⟩
    have hι : S.iotaSO v h' = M := Subtype.ext (Subtype.ext e1)
    rw [hι, mul_inv_cancel_left]

include hρ hQ in
/-- **The local orbital identity on the standard lattices at a good place**:
$\mu_v(SO(L_v)) = \sigma_v(T_v\cap L_v)\,\mu'_v(SO(L'_v))$. -/
theorem muLocSO_soStab_good (hk : 1 ≤ k) (hv : S.GoodFin v) :
    muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) =
      sigV Q₀ ρ hQ v (intSph Q₀ ρ v) * muLocSO v S.C.Q' 1 (soStabSO v S.C.Q' : Set (SOv v S.C.Q')) := by
  have hA : MeasurableSet (intSph Q₀ ρ v) := by
    have : intSph Q₀ ρ v = Subtype.val ⁻¹' {x : Fin (k + 1) → Fv | IntVec v x} := rfl
    rw [this]
    refine measurableSet_preimage measurable_subtype_coe ?_
    have : {x : Fin (k + 1) → Fv | IntVec v x} = ⋂ i, (fun x => x i) ⁻¹' {a | Valued.v a ≤ 1} := by
      ext x; simp [IntVec]
    rw [this]
    have h1 : MeasurableSet {a : Fv | Valued.v a ≤ 1} := by
      have := (measurable_id.prodMk (measurable_const (a := (1 : Fv)))) (measurableSet_valued_le v)
      simpa using this
    exact MeasurableSet.iInter fun i => (measurable_pi_apply i) h1
  have hB : MeasurableSet (soStabSO v S.C.Q' : Set (SOv v S.C.Q')) := (isOpen_soStabSO v S.C.Q').measurableSet
  rw [← S.secMulImage_good hρ v hv, S.localFib_fin' hρ hQ v hk hA hB, S.cFin_good v hv, one_mul]

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
