import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphere

/-!
# The stabilizer of $\xi$ in $SO(V)(\mathbb A)$ and in $SO(V)(F)$

For the setup of `AdelicSphere.lean` ($G = [d\xi\mid G']$, $Q_0\circ G = \langle m_0\rangle\perp Q'$):

* **`exists_conjBlockGL_eq`** (every place): an isometry $g$ of $H_\sigma$ fixing $\xi$ is $G\,\mathrm{diag}(1, h)\,G^{-1}$ for an
  isometry $h$ of $H'_\sigma$ with $\det h = \det g$, and $h = $ `blockOf`$(g)$;
* **`iota_smul_ξA`**: $\iota(h)\xi = \xi$; **`iota_injective`**;
* **`exists_iota_eq`**: every $g\in SO(V)(\mathbb A)$ with $g\xi = \xi$ is $\iota(h)$ for some $h\in SO(Q')(\mathbb A)$ (at almost every
  place $h_v$ is integral because $G$, $G^{-1}$ and $g_v$ are);
* **`exists_iota_diag_eq`**: the same over $F$, compatibly with the diagonal embeddings.
-/

open MeasureTheory Set Matrix
open scoped ENNReal RestrictedProduct

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

section Generic

variable {R : Type*} [Field R] {P : Matrix (Fin (k + 1)) (Fin (k + 1)) R}

theorem blockOf_conjBlock (hP : IsUnit P.det) (h : Matrix (Fin k) (Fin k) R) : blockOf P (conjBlock P h) = h := by
  unfold blockOf conjBlock
  have : P⁻¹ * (P * cornerMat 1 h * P⁻¹) * P = cornerMat 1 h := by
    simp only [← Matrix.mul_assoc]
    rw [nonsing_inv_mul P hP, Matrix.one_mul, Matrix.mul_assoc, nonsing_inv_mul P hP, Matrix.mul_one]
  rw [this, cornerMat_submatrix_succ]

theorem conjBlock_injective (hP : IsUnit P.det) : Function.Injective (conjBlock P (k := k)) := fun h h' e => by
  rw [← blockOf_conjBlock hP h, e, blockOf_conjBlock hP]

end Generic

theorem map_blockGL {K L : Type*} [Field K] [Field L] (τ : K →+* L) (h : GL (Fin k) K) :
    Matrix.GeneralLinearGroup.map τ (blockGL h) = blockGL (Matrix.GeneralLinearGroup.map τ h) :=
  Units.ext (by
    show (cornerMat 1 h.val).map τ = cornerMat 1 (h.val.map τ)
    rw [cornerMat_map, map_one])

theorem map_conjBlockGL {K L : Type*} [Field K] [Field L] (τ : K →+* L) (P : GL (Fin (k + 1)) K)
    (h : GL (Fin k) K) :
    Matrix.GeneralLinearGroup.map τ (conjBlockGL P h) =
      conjBlockGL (Matrix.GeneralLinearGroup.map τ P) (Matrix.GeneralLinearGroup.map τ h) := by
  simp only [conjBlockGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply,
    map_mul, map_inv, map_blockGL]

variable {Q₀ : QuadForm (𝓞 F) (k + 1)} {ρ : F}

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "AF" => FiniteAdeleRing (𝓞 F) F

namespace AdelicSphereSetup

variable (S : AdelicSphereSetup Q₀ ρ) (hρ : ρ ≠ 0)

theorem two_m₀_ne_zero {K : Type*} [Field K] [CharZero K] (σ : F →+* K) :
    σ (algebraMap (𝓞 F) F (2 * S.C.m₀)) ≠ 0 := by
  rw [map_ne_zero, map_ne_zero_iff _ RingOfIntegers.coe_injective]
  exact mul_ne_zero two_ne_zero S.C.hm

theorem d_ne_zero {K : Type*} [Field K] (σ : F →+* K) : σ (algebraMap (𝓞 F) F S.C.d) ≠ 0 := by
  rw [map_ne_zero, map_ne_zero_iff _ RingOfIntegers.coe_injective]; exact S.C.hd

/-- $g$ fixes $Ge_0$ iff it fixes $\xi$. -/
theorem fix_Pe0_iff {K : Type*} [Field K] (σ : F →+* K) (g : Matrix (Fin (k + 1)) (Fin (k + 1)) K) :
    g *ᵥ ((S.PAt σ).val *ᵥ e0) = (S.PAt σ).val *ᵥ e0 ↔
      g *ᵥ (S.sphereDataAt hρ σ).x₀ = (S.sphereDataAt hρ σ).x₀ := by
  rw [S.PAt_mulVec_e0, mulVec_smul]
  exact ⟨fun h => smul_right_injective _ (S.d_ne_zero σ) h, fun h => congrArg _ h⟩

/-- **$\iota$ fixes $\xi$** at every place. -/
theorem conjBlockGL_fix {K : Type*} [Field K] (σ : F →+* K) (h : GL (Fin k) K) :
    (conjBlockGL (S.PAt σ) h).val *ᵥ (S.sphereDataAt hρ σ).x₀ = (S.sphereDataAt hρ σ).x₀ := by
  rw [← S.fix_Pe0_iff hρ, conjBlockGL_val]
  exact conjBlock_mulVec (S.isUnit_det_PAt σ) _

/-- **The stabilizer at a place.** -/
theorem exists_conjBlockGL_eq {K : Type*} [Field K] [CharZero K] (σ : F →+* K) {g : GL (Fin (k + 1)) K}
    (hg : g.valᵀ * hesAt Q₀ σ * g.val = hesAt Q₀ σ)
    (hgx : g.val *ᵥ (S.sphereDataAt hρ σ).x₀ = (S.sphereDataAt hρ σ).x₀) :
    ∃ h : GL (Fin k) K, conjBlockGL (S.PAt σ) h = g ∧ h.valᵀ * hesAt S.C.Q' σ * h.val = hesAt S.C.Q' σ ∧
      h.val.det = g.val.det ∧ h.val = blockOf (S.PAt σ).val g.val ∧
      (h⁻¹ : GL (Fin k) K).val = blockOf (S.PAt σ).val (g⁻¹ : GL (Fin (k + 1)) K).val := by
  have hP := S.isUnit_det_PAt σ
  have ha := S.two_m₀_ne_zero σ
  have hPH := S.PAt_hes σ
  have hgi : (g⁻¹ : GL (Fin (k + 1)) K).valᵀ * hesAt Q₀ σ * (g⁻¹ : GL (Fin (k + 1)) K).val = hesAt Q₀ σ := by
    have e : (g⁻¹ : GL (Fin (k + 1)) K).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹ : GL (Fin (k + 1)) K).valᵀ * hesAt Q₀ σ * (g⁻¹ : GL (Fin (k + 1)) K).val
        = (g⁻¹ : GL (Fin (k + 1)) K).valᵀ * (g.valᵀ * hesAt Q₀ σ * g.val) * (g⁻¹ : GL (Fin (k + 1)) K).val := by
          rw [hg]
      _ = (g.val * (g⁻¹ : GL (Fin (k + 1)) K).val)ᵀ * hesAt Q₀ σ * (g.val * (g⁻¹ : GL (Fin (k + 1)) K).val) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = hesAt Q₀ σ := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; simp
  have hgxi : (g⁻¹ : GL (Fin (k + 1)) K).val *ᵥ (S.sphereDataAt hρ σ).x₀ = (S.sphereDataAt hρ σ).x₀ := by
    conv_lhs => rw [← hgx]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  obtain ⟨e1, e2, e3⟩ := exists_conjBlock_eq hP ha hPH hg ((S.fix_Pe0_iff hρ σ _).mpr hgx)
  obtain ⟨f1, -, -⟩ := exists_conjBlock_eq hP ha hPH hgi ((S.fix_Pe0_iff hρ σ _).mpr hgxi)
  set h1 := blockOf (S.PAt σ).val g.val
  set h2 := blockOf (S.PAt σ).val (g⁻¹ : GL (Fin (k + 1)) K).val
  have m12 : h1 * h2 = 1 := conjBlock_injective hP (by
    rw [conjBlock_mul hP, e1, f1, ← Units.val_mul, mul_inv_cancel, Units.val_one, conjBlock_one hP])
  have m21 : h2 * h1 = 1 := conjBlock_injective hP (by
    rw [conjBlock_mul hP, e1, f1, ← Units.val_mul, inv_mul_cancel, Units.val_one, conjBlock_one hP])
  refine ⟨⟨h1, h2, m12, m21⟩, Units.ext ?_, e2, e3, rfl, rfl⟩
  rw [conjBlockGL_val]; exact e1

/-! ### The adelic stabilizer -/

theorem iota_fst_fst (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsReal}) :
    ((ArchSO.incl _ ((S.iota h).1.1 w) : GL (Fin (k + 1)) ℝ)) =
      conjBlockGL (S.PAt (σR w)) (ArchSO.incl _ (h.1.1 w)) := rfl

theorem iota_fst_snd (h : SOAdele S.C.Q') (w : {w : InfinitePlace F // w.IsComplex}) :
    ((ArchSOC.incl _ ((S.iota h).1.2 w) : GL (Fin (k + 1)) ℂ)) =
      conjBlockGL (S.PAt (σC w)) (ArchSOC.incl _ (h.1.2 w)) := rfl

theorem iota_snd (h : SOAdele S.C.Q') (v : HeightOneSpectrum (𝓞 F)) :
    (((S.iota h).2 : OAf QF) v : orthGroup QF (v.adicCompletion F)) = S.iotaV v (((h.2 : SOAf S.C.Q') : OAf _) v) :=
  rfl

include hρ in
/-- **$\iota(h)\,\xi = \xi$.** -/
theorem iota_smul_ξA (h : SOAdele S.C.Q') : S.iota h • S.ξA = S.ξA := by
  funext i
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · exact congrFun (S.conjBlockGL_fix hρ (σR w) (ArchSO.incl _ (h.1.1 w))) i
  · exact congrFun (S.conjBlockGL_fix hρ (σC w) (ArchSOC.incl _ (h.1.2 w))) i
  · apply Subtype.ext; funext v
    exact congrFun (S.conjBlockGL_fix hρ (σV v) _) i

/-- **$\iota$ is injective.** -/
theorem iota_injective : Function.Injective S.iota := by
  intro h h' e
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · have := congrArg (fun g : SOAdele Q₀ => (ArchSO.incl _ (g.1.1 w) : GL (Fin (k + 1)) ℝ)) e
    exact Subtype.ext (conjBlockGL_injective _ this)
  · have := congrArg (fun g : SOAdele Q₀ => (ArchSOC.incl _ (g.1.2 w) : GL (Fin (k + 1)) ℂ)) e
    exact Subtype.ext (conjBlockGL_injective _ this)
  · apply Subtype.ext; apply RestrictedProduct.ext; intro v
    have := congrArg (fun g : SOAdele Q₀ => (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F))) e
    exact Subtype.ext (conjBlockGL_injective _ this)

theorem submatrix_mem_intMat {v : HeightOneSpectrum (𝓞 F)} {M : Matrix (Fin (k + 1)) (Fin (k + 1)) (v.adicCompletion F)}
    (hM : M ∈ intMat v) : M.submatrix Fin.succ Fin.succ ∈ intMat v := fun i j => hM _ _

theorem blockOf_mem_intMat {v : HeightOneSpectrum (𝓞 F)} (hP : S.PAt (σV v) ∈ glInt v)
    {g : Matrix (Fin (k + 1)) (Fin (k + 1)) (v.adicCompletion F)} (hg : g ∈ intMat v) :
    blockOf (S.PAt (σV v)).val g ∈ intMat v := by
  rw [mem_glInt_iff] at hP
  unfold blockOf
  rw [← Matrix.coe_units_inv]
  exact submatrix_mem_intMat (mul_mem_intMat v (mul_mem_intMat v hP.2 hg) hP.1)

include hρ in
/-- **The stabilizer of $\xi$ in $SO(V)(\mathbb A)$ is $\iota(SO(Q')(\mathbb A))$.** -/
theorem exists_iota_eq {g : SOAdele Q₀} (hg : g • S.ξA = S.ξA) : ∃ h, S.iota h = g := by
  classical
  -- real places
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, ∃ h : ArchSO (QRe S.C.Q' w),
      S.iotaR w h = g.1.1 w := by
    intro w
    have hm := hes_of_mem_soReal Q₀ (σR w) (g.1.1 w).2
    have hx : (ArchSO.incl _ (g.1.1 w) : GL (Fin (k + 1)) ℝ).val *ᵥ (S.sphereDataAt hρ (σR w)).x₀ =
        (S.sphereDataAt hρ (σR w)).x₀ := funext fun i => congrArg (fun y => (y i).1.1 w) hg
    obtain ⟨h, e1, e2, e3, -⟩ := S.exists_conjBlockGL_eq hρ (σR w) hm.1 hx
    exact ⟨⟨h, mem_soReal_of S.C.Q' (σR w) e2 (e3.trans hm.2)⟩, Subtype.ext e1⟩
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, ∃ h : ArchSOC (QCx S.C.Q' w),
      S.iotaC w h = g.1.2 w := by
    intro w
    have hm := hes_of_mem_soC Q₀ (σC w) (g.1.2 w).2
    have hx : (ArchSOC.incl _ (g.1.2 w) : GL (Fin (k + 1)) ℂ).val *ᵥ (S.sphereDataAt hρ (σC w)).x₀ =
        (S.sphereDataAt hρ (σC w)).x₀ := funext fun i => congrArg (fun y => (y i).1.2 w) hg
    obtain ⟨h, e1, e2, e3, -⟩ := S.exists_conjBlockGL_eq hρ (σC w) hm.1 hx
    exact ⟨⟨h, mem_soC_of S.C.Q' (σC w) e2 (e3.trans hm.2)⟩, Subtype.ext e1⟩
  -- finite places
  have hV : ∀ v : HeightOneSpectrum (𝓞 F), ∃ h : orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F),
      S.iotaV v h = ((g.2 : OAf QF) v) ∧
      ((h : GL (Fin k) (v.adicCompletion F)).val = blockOf (S.PAt (σV v)).val
        (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)).val) ∧
      (((h⁻¹ : orthGroup _ _) : GL (Fin k) (v.adicCompletion F)).val = blockOf (S.PAt (σV v)).val
        ((((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F))⁻¹ : GL (Fin (k + 1)) (v.adicCompletion F)).val) := by
    intro v
    have hm : (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)).valᵀ *
        hesAt Q₀ (σV v) * (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)).val = hesAt Q₀ (σV v) :=
      (mem_orthGroup _).mp ((g.2 : OAf QF) v).2
    have hx : (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)).val *ᵥ
        (S.sphereDataAt hρ (σV v)).x₀ = (S.sphereDataAt hρ (σV v)).x₀ :=
      funext fun i => congrArg (fun y => ((y i).2 : AF) v) hg
    obtain ⟨h, e1, e2, -, e4, e5⟩ := S.exists_conjBlockGL_eq hρ (σV v) hm hx
    exact ⟨⟨h, (mem_orthGroup _).mpr e2⟩, Subtype.ext e1, e4, e5⟩
  choose hr hr' using hR
  choose hc hc' using hC
  choose hv hv1 hv2 hv3 using hV
  have hfin : ∀ᶠ v in Filter.cofinite, hv v ∈ stdStab (S.C.Q'.map (algebraMap (𝓞 F) F)) v := by
    filter_upwards [S.eventually_PAt_glInt, (g.2 : OAf QF).2] with v hP hgv
    have hgv' : (((g.2 : OAf QF) v : orthGroup QF _) : GL (Fin (k + 1)) (v.adicCompletion F)) ∈ glInt v := hgv
    rw [mem_glInt_iff] at hgv'
    show ((hv v : orthGroup _ _) : GL (Fin k) (v.adicCompletion F)) ∈ glInt v
    rw [mem_glInt_iff]
    refine ⟨?_, ?_⟩
    · rw [hv2]; exact S.blockOf_mem_intMat hP hgv'.1
    · have : ((((hv v : orthGroup _ _) : GL (Fin k) (v.adicCompletion F))⁻¹ : GL (Fin k) (v.adicCompletion F))) =
          (((hv v)⁻¹ : orthGroup _ _) : GL (Fin k) (v.adicCompletion F)) := rfl
      rw [this, hv3]; exact S.blockOf_mem_intMat hP hgv'.2
  let hf : OAf (S.C.Q'.map (algebraMap (𝓞 F) F)) := ⟨hv, hfin⟩
  have hdet : hf ∈ soAf (S.C.Q'.map (algebraMap (𝓞 F) F)) := fun v => by
    show ((hv v : orthGroup _ _) : GL (Fin k) (v.adicCompletion F)).val.det = 1
    have := congrArg (fun x : orthGroup QF (v.adicCompletion F) => (x : GL (Fin (k + 1)) (v.adicCompletion F)).val.det) (hv1 v)
    rw [det_iotaV] at this
    rw [this]; exact (g.2.2 v)
  refine ⟨((hr, hc), ⟨hf, hdet⟩), ?_⟩
  refine Prod.ext (Prod.ext (funext fun w => hr' w) (funext fun w => hc' w)) ?_
  apply Subtype.ext; apply RestrictedProduct.ext; intro v
  exact hv1 v

/-! ### Rational points -/

theorem PAt_map {K : Type*} [Field K] (σ : F →+* K) :
    Matrix.GeneralLinearGroup.map σ (S.PAt (RingHom.id F)) = S.PAt σ :=
  Units.ext (by simp [PAt_val, Matrix.map_map])

theorem iotaRat_mem (hG : GL (Fin k) F) (hh : hG ∈ orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) F) :
    conjBlockGL (S.PAt (RingHom.id F)) hG ∈ orthGroup QF F := by
  rw [mem_orthGroup, Algebra.algebraMap_self] at hh ⊢
  exact (S.conj_mem (RingHom.id F) hh).1

theorem iotaRat_det (hG : GL (Fin k) F) :
    (conjBlockGL (S.PAt (RingHom.id F)) hG).val.det = hG.val.det := by
  rw [conjBlockGL_val, det_conjBlock (S.isUnit_det_PAt _)]

/-- The rational isometry $G\,\mathrm{diag}(1, h)\,G^{-1}$ of $Q_0$ for a rational isometry $h$ of $Q'$. -/
def iotaRat (h : soSub (S.C.Q'.map (algebraMap (𝓞 F) F)) F) : soSub QF F :=
  ⟨⟨conjBlockGL (S.PAt (RingHom.id F)) (h.1 : GL (Fin k) F), S.iotaRat_mem _ h.1.2⟩, by
    show (conjBlockGL (S.PAt (RingHom.id F)) (h.1 : GL (Fin k) F)).val.det = 1
    rw [S.iotaRat_det]; exact mem_soSub.mp h.2⟩

/-- **$\iota$ commutes with the diagonal embeddings.** -/
theorem iota_diag (h : soSub (S.C.Q'.map (algebraMap (𝓞 F) F)) F) :
    S.iota (diagSOAdele S.C.Q' h) = diagSOAdele Q₀ (S.iotaRat h) := by
  refine Prod.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_)) ?_
  · apply Subtype.ext
    show conjBlockGL (S.PAt (σR w)) (Matrix.GeneralLinearGroup.map (σR w) (h.1 : GL (Fin k) F)) =
      Matrix.GeneralLinearGroup.map (σR w) (conjBlockGL (S.PAt (RingHom.id F)) (h.1 : GL (Fin k) F))
    rw [map_conjBlockGL, S.PAt_map]
  · apply Subtype.ext
    show conjBlockGL (S.PAt (σC w)) (Matrix.GeneralLinearGroup.map (σC w) (h.1 : GL (Fin k) F)) =
      Matrix.GeneralLinearGroup.map (σC w) (conjBlockGL (S.PAt (RingHom.id F)) (h.1 : GL (Fin k) F))
    rw [map_conjBlockGL, S.PAt_map]
  · apply Subtype.ext; apply RestrictedProduct.ext; intro v
    apply Subtype.ext
    show conjBlockGL (S.PAt (σV v)) (Matrix.GeneralLinearGroup.map (σV v) (h.1 : GL (Fin k) F)) =
      Matrix.GeneralLinearGroup.map (σV v) (conjBlockGL (S.PAt (RingHom.id F)) (h.1 : GL (Fin k) F))
    rw [map_conjBlockGL, S.PAt_map]

/-- **$\iota(SO(Q')(F))\subseteq SO(V)(F)$.** -/
theorem iota_mem_gamma {h : SOAdele S.C.Q'} (hh : h ∈ GammaSOAdele S.C.Q') : S.iota h ∈ GammaSOAdele Q₀ := by
  obtain ⟨h₀, rfl⟩ := hh
  exact ⟨S.iotaRat h₀, (S.iota_diag h₀).symm⟩

include hρ in
/-- **The stabilizer of $\xi$ in $SO(V)(F)$ is $\iota(SO(Q')(F))$.** -/
theorem exists_iota_gamma {γ : SOAdele Q₀} (hγ : γ ∈ GammaSOAdele Q₀) (hfix : γ • S.ξA = S.ξA) :
    ∃ h ∈ GammaSOAdele S.C.Q', S.iota h = γ := by
  obtain ⟨γ₀, rfl⟩ := hγ
  set M := ((γ₀ : orthGroup QF F) : GL (Fin (k + 1)) F)
  have hfix' : M.val *ᵥ S.ξ.1 = S.ξ.1 := by
    rw [ξA, diagSOAdele_smul_diagVec] at hfix
    funext i
    have := congrFun hfix i
    exact diag_injective this
  have hm : M.valᵀ * hesAt Q₀ (RingHom.id F) * M.val = hesAt Q₀ (RingHom.id F) := by
    have := (mem_orthGroup _).mp (γ₀ : orthGroup QF F).2
    rwa [Algebra.algebraMap_self] at this
  obtain ⟨h, e1, e2, e3, -⟩ := S.exists_conjBlockGL_eq hρ (RingHom.id F) hm hfix'
  have hh : h ∈ orthGroup (S.C.Q'.map (algebraMap (𝓞 F) F)) F := by
    rw [mem_orthGroup, Algebra.algebraMap_self]; exact e2
  let h₀ : soSub (S.C.Q'.map (algebraMap (𝓞 F) F)) F := ⟨⟨h, hh⟩, by
    show h.val.det = 1; rw [e3]; exact mem_soSub.mp γ₀.2⟩
  refine ⟨diagSOAdele S.C.Q' h₀, ⟨h₀, rfl⟩, ?_⟩
  rw [S.iota_diag]
  congr 1
  exact Subtype.ext (Subtype.ext e1)

end AdelicSphereSetup

end QuadFormsKB.Tamagawa.Measure.Weil

end
