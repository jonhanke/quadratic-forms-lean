/-
# The local identity for embeddings of lattices, at every prime

**Layer:** the completion $F_\mathfrak p$ of a totally real number field at a finite prime $\mathfrak p$ (dyadic included); $V = (F^N, Q_0)$,
$N = r + n'$, an arbitrary lattice $L$ on $V$ and a quadratic lattice $T = (T_\ell, T_0)$ of rank $r$ (`FrameLatDefs.lean`).

**Proves**
* `latBetaT_eq_of_loc`: $\beta_\mathfrak p(L, T)$ computed with any local free models $A$, $B$ (two models differ by
  $\mathrm{GL}(\mathfrak o_\mathfrak p)$, which changes neither $\|\det\|$ nor the density, `localDensityForm_congr_left/right`);
* `latBetaT_of_std`: $\beta_\mathfrak p(L, T) = \beta_\mathfrak p(Q_0, T_0)$ where $L_\mathfrak p = \mathfrak o_\mathfrak p^N$ and $T_{\ell,\mathfrak p} = \mathfrak o_\mathfrak p^r$;
* `latBetaT_eq_zero_of_not_rep`: $\beta_\mathfrak p(L, T) = 0$ if $Q_0$ does not represent $T_0$ over $F_\mathfrak p$;
* **`latFrameLocalIdentity`** (Weil 1982, §3.4 and §4.5 [unverified]): for an adapted frame $Q_0\circ g = T_0\perp Q'$,
  $$W_\mathfrak p(g^{-1}L_\mathfrak p, T_{\ell,\mathfrak p})\,\beta_\mathfrak p(Q_0,Q_0)\,r_\mathfrak p(L)\,\|\det H_{T_0}\|_\mathfrak p^{\,n'} =
    \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(L, T)\,\|\det g\|_\mathfrak p^{\,n'+1},$$
  $r_\mathfrak p(L)$ = `locRatio`. *Proof:* local free models $L_\mathfrak p = A\mathfrak o_\mathfrak p^N$, $T_{\ell,\mathfrak p} = B\mathfrak o_\mathfrak p^r$ ($A$, $B$
  global, `exists_isLocModel`); $g' = A^{-1}g\,\mathrm{diag}(B, 1_{n'})$ is a frame of the global form $Q_0\circ A$ adapted to $T_0\circ B$
  with the same complement $Q'$, and $\mathrm{diag}(B^{-1}, 1)$ maps
  $Y_\mathfrak p(g^{-1}L_\mathfrak p, B\mathfrak o_\mathfrak p^r)$ onto
  $Y_\mathfrak p(g'^{-1}\mathfrak o_\mathfrak p^N)$ for $T_0\circ B\perp Q'$, commuting with $O(Q')(F_\mathfrak p)$
  (so the type sums agree); then
  `frameLocalIdentityGen` for $(Q_0\circ A, T_0\circ B, g')$, the $\alpha$ law $\tfrac12\beta(Q_0\circ A)\|\det A\|^{N+1} = \alpha_\mathfrak p(Q_0)r_\mathfrak p(L)$
  (`alpha_mul_normDet_eq`), $\det H_{T_0\circ B} = (\det B)^2\det H_{T_0}$ and $\det g' = \det g\det B/\det A$.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLatGlobal

open NumberField IsDedekindDomain Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.FramesLat

open QuadFormsKB.Tamagawa Lattices LocalDensity Frames SiegelLat QuadFormsKB.HilbertModular QuadFormsKB.QuadForm

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- Two local free models of the same local lattice give isometric integral Gram forms over $\mathfrak o_\mathfrak p$ and
the same $\|\det\|$. -/
theorem model_iso {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) {A₁ A₂ : GL (Fin N) F}
    (h₁ : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A₁)) (h₂ : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A₂))
    (he : loc v (Lattices.latOf A₁) = loc v (Lattices.latOf A₂)) :
    Siegel.IsometricGL (NF.Qp v (gramZ (formF Q₀) A₁ h₁)) (NF.Qp v (gramZ (formF Q₀) A₂ h₂)) ∧
      ‖algebraMap F Fv A₁.val.det‖ = ‖algebraMap F Fv A₂.val.det‖ := by
  set g₁ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₁
  set g₂ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₂
  have hstd : locAct v (g₁⁻¹ * g₂) (std v) = std v := by
    have h := he
    rw [Lattices.latOf, Lattices.latOf, loc_glImage, loc_glImage, loc_intVec] at h
    rw [locAct_mul, ← h, locAct_inv_locAct]
  obtain ⟨U, hU⟩ := exists_GL_o_of_locAct_std v _ hstd
  have hUv : U.val.map (algebraMap (v.adicCompletionIntegers F) Fv) = (g₁⁻¹ * g₂).val := congrArg Units.val hU
  have hform : NF.Qp v (gramZ (formF Q₀) A₂ h₂) = (NF.Qp v (gramZ (formF Q₀) A₁ h₁)).compMat U.val := by
    apply NF.map_injective (IsFractionRing.injective (v.adicCompletionIntegers F) Fv)
    rw [← map_compMat, map_Qp_gramZ, map_Qp_gramZ, compMat_mul, hUv, ← Units.val_mul, mul_inv_cancel_left]
  refine ⟨⟨U, fun x => by rw [hform, eval_compMat]⟩, ?_⟩
  have hdet : algebraMap F Fv A₂.val.det = algebraMap F Fv A₁.val.det *
      ((U.val.det : v.adicCompletionIntegers F) : Fv) := by
    have e1 : algebraMap F Fv A₂.val.det = g₂.val.det := by
      rw [RingHom.map_det]; rfl
    have e2 : algebraMap F Fv A₁.val.det = g₁.val.det := by
      rw [RingHom.map_det]; rfl
    have e3 : ((U.val.det : v.adicCompletionIntegers F) : Fv) = (g₁⁻¹ * g₂).val.det := by
      rw [← hUv, show ((U.val.det : v.adicCompletionIntegers F) : Fv) =
        algebraMap (v.adicCompletionIntegers F) Fv U.val.det from rfl, RingHom.map_det]; rfl
    rw [e1, e2, e3, ← det_mul, ← Units.val_mul, mul_inv_cancel_left]
  have hU1 : ‖((U.val.det : v.adicCompletionIntegers F) : Fv)‖ = 1 := norm_coe_unit v (U.isUnit.map Matrix.detMonoidHom)
  rw [hdet, norm_mul, hU1, mul_one]

/-- **$\beta_\mathfrak p(L, T)$ with any local free models** (independence of the models). -/
theorem latBetaT_eq_of_loc {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r)
    (hTi : Lattices.IsIntegral (formF T₀) Tl.1) {A : GL (Fin N) F} (hA : loc v (Lattices.latOf A) = loc v L.1)
    (hAi : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) {B : GL (Fin r) F}
    (hB : loc v (Lattices.latOf B) = loc v Tl.1) (hBi : Lattices.IsIntegral (formF T₀) (Lattices.latOf B)) :
    latBetaT v Q₀ L T₀ Tl = ‖algebraMap F Fv A.val.det‖ ^ r *
      (‖algebraMap F Fv B.val.det‖ ^ (r + 1) / ‖algebraMap F Fv B.val.det‖ ^ N) *
      NF.localDensityForm v (gramZ (formF Q₀) A hAi) (gramZ (formF T₀) B hBi) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨A₀, hA₀⟩ := exists_isLocModel v L
  obtain ⟨B₀, hB₀⟩ := exists_isLocModel v Tl
  have hA₀i := hA₀.isIntegral v hLi
  have hB₀i := hB₀.isIntegral v hTi
  have h : (∃ A, IsLocModel v L A ∧ Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) ∧
      (∃ B, IsLocModel v Tl B ∧ Lattices.IsIntegral (formF T₀) (Lattices.latOf B)) :=
    ⟨⟨A₀, hA₀, hA₀i⟩, ⟨B₀, hB₀, hB₀i⟩⟩
  unfold latBetaT
  rw [dif_pos h]
  have hA' := h.1.choose_spec
  have hB' := h.2.choose_spec
  obtain ⟨hisoA, hnA⟩ := model_iso v Q₀ hA'.2 hAi (hA'.1.2.trans hA.symm)
  obtain ⟨hisoB, hnB⟩ := model_iso v T₀ hB'.2 hBi (hB'.1.2.trans hB.symm)
  rw [hnA, hnB, NF.localDensityForm_eq_completion, NF.localDensityForm_eq_completion,
    DVR.localDensityForm_congr_left hisoA, DVR.localDensityForm_congr_right _ hisoB]

theorem isIntegral_latOf_one' {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) :
    Lattices.IsIntegral (formF Q₀) (Lattices.latOf (1 : GL (Fin n) F)) := by
  intro x hx
  rw [Lattices.latOf, glImage_one] at hx
  obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp hx
  exact ⟨Q₀.eval y, by rw [← eval_map_comp]⟩

theorem gramZ_one' {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) : gramZ (formF Q₀) 1 (isIntegral_latOf_one' Q₀) = Q₀ := by
  refine QuadForm.ext_eval fun x => IsFractionRing.injective (𝓞 F) F ?_
  rw [algebraMap_eval_gramZ, Units.val_one, one_mulVec, ← eval_map_comp]

theorem nondegenerate_gramZ' {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} (hQ₀ : Q₀.Nondegenerate) (A : GL (Fin n) F)
    (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) : (gramZ (formF Q₀) A h).Nondegenerate := by
  apply nondegenerate_of_map
  have hQF : (formF Q₀).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ₀
  rw [show (gramZ (formF Q₀) A h).map (algebraMap (𝓞 F) F) = formF (gramZ (formF Q₀) A h) from rfl, formF_gramZ,
    QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
  have hA : A.val.det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
  exact mul_ne_zero (mul_ne_zero hA hQF) hA

/-- **At a prime where $L_\mathfrak p$ and $T_{\ell,\mathfrak p}$ are standard, $\beta_\mathfrak p(L, T) = \beta_\mathfrak p(Q_0, T_0)$.** -/
theorem latBetaT_of_std {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) (T₀ : QuadForm (𝓞 F) r) (Tl : Lat F r)
    (hTi : Lattices.IsIntegral (formF T₀) Tl.1) (hL : loc v L.1 = std v) (hT : loc v Tl.1 = std v) :
    latBetaT v Q₀ L T₀ Tl = NF.localDensityForm v Q₀ T₀ := by
  have hA : loc v (Lattices.latOf (1 : GL (Fin N) F)) = loc v L.1 := by
    rw [Lattices.latOf, glImage_one, loc_intVec, hL]
  have hB : loc v (Lattices.latOf (1 : GL (Fin r) F)) = loc v Tl.1 := by
    rw [Lattices.latOf, glImage_one, loc_intVec, hT]
  rw [latBetaT_eq_of_loc v hN hr Q₀ L hLi T₀ Tl hTi hA (isIntegral_latOf_one' Q₀) hB (isIntegral_latOf_one' T₀),
    gramZ_one', gramZ_one']
  simp

/-- **No local representation, no local density:** if $Q_0$ does not represent $T_0$ over $F_\mathfrak p$ then $\beta_\mathfrak p(L, T) = 0$. -/
theorem latBetaT_eq_zero_of_not_rep {N r : ℕ} (hrN : r ≤ N) (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N)
    (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) (Tl : Lat F r)
    (h : ¬ ∃ X : Matrix (Fin N) (Fin r) Fv,
      ((formF Q₀).map (algebraMap F Fv)).compMat X = (formF T₀).map (algebraMap F Fv)) :
    latBetaT v Q₀ L T₀ Tl = 0 := by
  unfold latBetaT
  split_ifs with hex
  swap
  · rfl
  set A := hex.1.choose
  set B := hex.2.choose
  have hAi := hex.1.choose_spec.2
  have hBi := hex.2.choose_spec.2
  rw [show NF.localDensityForm v (gramZ (formF Q₀) A hAi) (gramZ (formF T₀) B hBi) = 0 by
    refine Frames.localDensityForm_eq_zero_of_not_rep v _ _ (nondegenerate_gramZ' hT B hBi) hrN ?_
    rintro ⟨X, hX⟩
    apply h
    set gB := Matrix.GeneralLinearGroup.map (algebraMap F Fv) B
    refine ⟨(A.val.map (algebraMap F Fv)) * X * gB⁻¹.val, ?_⟩
    rw [show (gramZ (formF Q₀) A hAi).map (algebraMap (𝓞 F) F) = formF (gramZ (formF Q₀) A hAi) from rfl,
      show (gramZ (formF T₀) B hBi).map (algebraMap (𝓞 F) F) = formF (gramZ (formF T₀) B hBi) from rfl,
      formF_gramZ, formF_gramZ] at hX
    rw [← map_compMat, ← map_compMat] at hX
    have e : ((formF Q₀).map (algebraMap F Fv)).compMat (A.val.map (algebraMap F Fv) * X * gB⁻¹.val) =
        ((((formF Q₀).map (algebraMap F Fv)).compMat (A.val.map (algebraMap F Fv))).compMat X).compMat gB⁻¹.val := by
      simp only [compMat_mul]
    have hBB : B.val.map (algebraMap F Fv) * gB⁻¹.val = 1 := Units.mul_inv gB
    rw [e, hX, compMat_mul, hBB, compMat_one]]
  simp

theorem exists_isLocModel' {N : ℕ} (hN : 1 ≤ N) (L : Lat F N) : ∃ A, IsLocModel v L A := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact exists_isLocModel v L

/-! ### The block matrix $\mathrm{diag}(B, 1_{n'})$ and transport of local types -/

section BlockDiag

/-- $\mathrm{diag}(B, 1_{n'}) \in \mathrm{GL}_{r+n'}(K)$. -/
def blockDiagGL {K : Type*} [CommRing K] {r n' : ℕ} (B : GL (Fin r) K) : GL (Fin (r + n')) K where
  val := blockMat B.val 0 0 1
  inv := blockMat B⁻¹.val 0 0 1
  val_inv := by
    rw [blockMat_mul]; simp [blockMat_one]
  inv_val := by
    rw [blockMat_mul]; simp [blockMat_one]

theorem blockDiagGL_val {K : Type*} [CommRing K] {r n' : ℕ} (B : GL (Fin r) K) :
    (blockDiagGL (n' := n') B).val = blockMat B.val 0 0 1 := rfl

/-- $\mathrm{diag}(P, 1)\,E = E\,P$ for the standard frame $E$. -/
theorem blockMat_mul_stdFrameMat {K : Type*} [CommRing K] {r n' : ℕ} (P : Matrix (Fin r) (Fin r) K) :
    blockMat P 0 0 (1 : Matrix (Fin n') (Fin n') K) * stdFrameMat = stdFrameMat * P := by
  ext i j
  refine (Matrix.mul_apply (M := blockMat P 0 0 1) (N := stdFrameMat)).trans ?_
  refine Eq.trans ?_ (Matrix.mul_apply (M := stdFrameMat) (N := P)).symm
  simp only [Fin.sum_univ_add]
  induction i using Fin.addCases with
  | left i => simp [stdFrameMat, Fin.castAdd_inj]
  | right i =>
    have h : ∀ (a : Fin n') (b : Fin r), Fin.natAdd r a ≠ Fin.castAdd n' b := fun a b => (castAdd_ne_natAdd b a).symm
    simp [stdFrameMat, h]

end BlockDiag

section Transport

variable {r n' : ℕ}

local notation "𝔬" => v.adicCompletionIntegers F

/-- $\mathrm{diag}(B, 1_{n'})$ over $F_\mathfrak p$, for a global $B$. -/
def Dloc (B : GL (Fin r) F) : GL (Fin (r + n')) Fv :=
  Matrix.GeneralLinearGroup.map (algebraMap F Fv) (blockDiagGL (n' := n') B)

theorem Dloc_val (B : GL (Fin r) F) :
    (Dloc v B : GL (Fin (r + n')) Fv).val = blockMat (B.val.map (algebraMap F Fv)) 0 0 1 := by
  show (blockMat B.val 0 0 1).map (algebraMap F Fv) = _
  rw [blockMat_map]; simp

theorem locAct_locAct_inv (g : GL (Fin (r + n')) Fv) (M : Submodule 𝔬 (Fin (r + n') → Fv)) :
    locAct v g (locAct v g⁻¹ M) = M := by
  rw [← locAct_mul, mul_inv_cancel, locAct_one]

theorem blockForm_compMat_diag (T₁ : QuadForm F r) (Q' : QuadForm F n') (B : GL (Fin r) F) :
    blockForm (T₁.compMat B.val) Q' = (blockForm T₁ Q').compMat (blockDiagGL (n' := n') B).val := by
  rw [blockDiagGL_val, compMat_blockMat_diag, compMat_one]

theorem mem_orth_Dloc (T₁ : QuadForm F r) (Q' : QuadForm F n') (B : GL (Fin r) F) (k : GL (Fin (r + n')) Fv) :
    k ∈ orthGroup (blockForm T₁ Q') Fv ↔
      (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * k * Dloc v B ∈ orthGroup (blockForm (T₁.compMat B.val) Q') Fv := by
  have := LatChange.mem_orthGroup_smul_compMat (blockForm T₁ Q') (c := 1) one_ne_zero
    (blockDiagGL (n' := n') B) Fv (h := (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * k * Dloc v B)
  rw [show ∀ X : QuadForm F (r + n'), (1 : F) • X = X from fun X => by ext1; simp, ← blockForm_compMat_diag] at this
  rw [this]
  have e : LatChange.gR (blockDiagGL (n' := n') B) Fv = Dloc v B := rfl
  rw [e, show (Dloc v B : GL (Fin (r + n')) Fv) * ((Dloc v B)⁻¹ * k * Dloc v B) * (Dloc v B)⁻¹ = k by group]

theorem orthEmbB_conj_Dloc (T₁ : QuadForm F r) (Q' : QuadForm F n') (B : GL (Fin r) F) (h : orthGroup Q' Fv) :
    (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * (orthEmbB T₁ Q' Fv h : GL (Fin (r + n')) Fv) * Dloc v B =
      (orthEmbB (T₁.compMat B.val) Q' Fv h : GL (Fin (r + n')) Fv) := by
  have hc : (orthEmbB T₁ Q' Fv h : GL (Fin (r + n')) Fv) * Dloc v B =
      Dloc v B * (orthEmbB (T₁.compMat B.val) Q' Fv h : GL (Fin (r + n')) Fv) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Dloc_val, orthEmbB_val, orthEmbB_val, blockMat_mul, blockMat_mul]
    simp
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **The transport bijection** $M \mapsto D^{-1}M$ between the local type sets. -/
def transportEquiv (T₁ : QuadForm F r) (Q' : QuadForm F n') (B : GL (Fin r) F)
    (Λ : Submodule 𝔬 (Fin (r + n') → Fv)) (Θ₁ Θ₂ : Submodule 𝔬 (Fin r → Fv))
    (hΘ : ∀ M : Submodule 𝔬 (Fin (r + n') → Fv),
      (∀ t ∈ Θ₁, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M) ↔
        (∀ t ∈ Θ₂, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈
          locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M)) :
    LocFrameSetL v T₁ Q' Λ Θ₁ ≃
      LocFrameSetL v (T₁.compMat B.val) Q' (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) Θ₂ where
  toFun M := ⟨locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M.1, by
      obtain ⟨k, hk⟩ := M.2.1
      refine ⟨⟨(Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * (k : GL (Fin (r + n')) Fv) * Dloc v B, (mem_orth_Dloc v T₁ Q' B k).mp k.2⟩, ?_⟩
      show locAct v ((Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * (k : GL (Fin (r + n')) Fv) * Dloc v B)
        (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) = _
      rw [← hk, ← locAct_mul, ← locAct_mul,
        show (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * (k : GL (Fin (r + n')) Fv) * Dloc v B * (Dloc v B)⁻¹ = (Dloc v B)⁻¹ * (k : GL (Fin (r + n')) Fv) by group],
    (hΘ M.1).mp M.2.2⟩
  invFun M := ⟨locAct v (Dloc v B : GL (Fin (r + n')) Fv) M.1, by
      obtain ⟨k, hk⟩ := M.2.1
      refine ⟨⟨(Dloc v B : GL (Fin (r + n')) Fv) * (k : GL (Fin (r + n')) Fv) * (Dloc v B)⁻¹, ?_⟩, ?_⟩
      · rw [mem_orth_Dloc v T₁ Q' B, show (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ * ((Dloc v B) * (k : GL (Fin (r + n')) Fv) * (Dloc v B)⁻¹) *
          Dloc v B = (k : GL (Fin (r + n')) Fv) by group]
        exact k.2
      · show locAct v ((Dloc v B : GL (Fin (r + n')) Fv) * (k : GL (Fin (r + n')) Fv) * (Dloc v B)⁻¹) Λ = _
        rw [← hk, ← locAct_mul, ← locAct_mul],
    (hΘ _).mpr (by rw [locAct_inv_locAct]; exact M.2.2)⟩
  left_inv M := Subtype.ext (locAct_locAct_inv v _ _)
  right_inv M := Subtype.ext (locAct_inv_locAct _ _)

theorem transportEquiv_smul (T₁ : QuadForm F r) (Q' : QuadForm F n') (B : GL (Fin r) F)
    (Λ : Submodule 𝔬 (Fin (r + n') → Fv)) (Θ₁ Θ₂ : Submodule 𝔬 (Fin r → Fv))
    (hΘ : ∀ M : Submodule 𝔬 (Fin (r + n') → Fv),
      (∀ t ∈ Θ₁, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M) ↔
        (∀ t ∈ Θ₂, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈
          locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M))
    (h : orthGroup Q' Fv) (M : LocFrameSetL v T₁ Q' Λ Θ₁) :
    transportEquiv v T₁ Q' B Λ Θ₁ Θ₂ hΘ (h • M) = h • transportEquiv v T₁ Q' B Λ Θ₁ Θ₂ hΘ M := by
  apply Subtype.ext
  show locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ (locAct v (orthEmbB T₁ Q' Fv h : GL (Fin (r + n')) Fv) M.1) =
    locAct v (orthEmbB (T₁.compMat B.val) Q' Fv h : GL (Fin (r + n')) Fv)
      (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M.1)
  rw [← locAct_mul, ← locAct_mul, ← orthEmbB_conj_Dloc v T₁ Q' B h]
  congr 1
  group

/-- **The local type sums are invariant under the transport** $M \mapsto D^{-1}M$. -/
theorem locFrameTypeSumL_transport (T₁ : QuadForm F r) (Q' : QuadForm F n') (hQ' : Q'.Nondegenerate)
    (B : GL (Fin r) F) {Λ : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ.IsLattice Fv)
    (Θ₁ Θ₂ : Submodule 𝔬 (Fin r → Fv))
    (hΘ : ∀ M : Submodule 𝔬 (Fin (r + n') → Fv),
      (∀ t ∈ Θ₁, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M) ↔
        (∀ t ∈ Θ₂, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈
          locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M)) :
    locFrameTypeSumL v T₁ Q' Λ Θ₁ =
      locFrameTypeSumL v (T₁.compMat B.val) Q' (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) Θ₂ := by
  classical
  have hΛ₂ := locAct_isLattice (v := v) (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ hΛ
  set φ := transportEquiv v T₁ Q' B Λ Θ₁ Θ₂ hΘ with hφ
  have hstab : ∀ M, MulAction.stabilizer (orthGroup Q' Fv) (φ M) = MulAction.stabilizer (orthGroup Q' Fv) M := by
    intro M; ext h
    simp only [MulAction.mem_stabilizer_iff]
    rw [← transportEquiv_smul v T₁ Q' B Λ Θ₁ Θ₂ hΘ h M]
    exact φ.injective.eq_iff
  have hw : ∀ M, locFrameWeightL v (T₁.compMat B.val) Q' (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) Θ₂ (φ M) =
      locFrameWeightL v T₁ Q' Λ Θ₁ M := by
    intro M; unfold locFrameWeightL; rw [hstab]
  let e : LocFrameTypesL v T₁ Q' Λ Θ₁ ≃
      LocFrameTypesL v (T₁.compMat B.val) Q' (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) Θ₂ :=
    Quotient.congr φ (fun a b => by
      show a ∈ MulAction.orbit (orthGroup Q' Fv) b ↔ φ a ∈ MulAction.orbit (orthGroup Q' Fv) (φ b)
      rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨h, (transportEquiv_smul v T₁ Q' B Λ Θ₁ Θ₂ hΘ h b).symm⟩
      · rintro ⟨h, hh⟩
        refine ⟨h, φ.injective ?_⟩
        rw [transportEquiv_smul]; exact hh)
  unfold locFrameTypeSumL
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun t => ?_
  have h1 : e t = Quotient.mk'' (φ t.out) := by
    calc e t = e (Quotient.mk'' t.out) := by rw [Quotient.out_eq']
      _ = _ := rfl
  have h2 : (Quotient.mk'' (e t).out : LocFrameTypesL v (T₁.compMat B.val) Q'
      (locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ Λ) Θ₂) = Quotient.mk'' (φ t.out) := by
    rw [Quotient.out_eq', h1]
  have h3 := Quotient.exact' h2
  change (e t).out ∈ MulAction.orbit (orthGroup Q' Fv) (φ t.out) at h3
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp h3
  rw [← hh, locFrameWeightL_smul v _ Q' hQ' hΛ₂ Θ₂ h, hw]

end Transport

/-- The final field algebra of `latFrameLocalIdentity`. -/
theorem latLocal_alg (a b G h0 W DQA DQ' DAT D0 ρ : ℝ) (r n' : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG : W * DQA * (b ^ 2 * h0) ^ n' = DQ' * DAT * (a⁻¹ * G * b) ^ (n' + 1))
    (hα : DQA * a ^ (r + n' + 1) = D0 * ρ) :
    W * D0 * ρ * h0 ^ n' = DQ' * (a ^ r * (b ^ (r + 1) / b ^ (r + n')) * DAT) * G ^ (n' + 1) := by
  have hp : b ^ n' ≠ 0 := pow_ne_zero _ hb
  have hq : a ^ n' ≠ 0 := pow_ne_zero _ ha
  have e1 : (b ^ 2 * h0) ^ n' = (b ^ n') ^ 2 * h0 ^ n' := by ring
  have e2 : (a⁻¹ * G * b) ^ (n' + 1) = (a ^ n' * a)⁻¹ * G ^ (n' + 1) * (b ^ n' * b) := by ring
  have e3 : b ^ (r + 1) / b ^ (r + n') = b / b ^ n' := by
    rw [pow_add, pow_add, pow_one]; field_simp
  have e4 : a ^ (r + n' + 1) = a ^ r * a ^ n' * a := by ring
  rw [e1, e2] at hG
  rw [e3]
  rw [e4] at hα
  generalize a ^ n' = q at *
  generalize b ^ n' = p at *
  generalize h0 ^ n' = H at *
  generalize G ^ (n' + 1) = GG at *
  generalize a ^ r = ar at *
  rw [mul_assoc W D0 ρ, mul_assoc, ← hα]
  field_simp at hG ⊢
  linear_combination ar * hG

/-- **The local identity for embeddings of lattices** (Weil 1982, §3.4 and §4.5 [unverified]; module docstring): for an adapted frame
$Q_0\circ g = T_0\perp Q'$,
$$W_\mathfrak p(g^{-1}L_\mathfrak p, T_{\ell,\mathfrak p})\,\beta_\mathfrak p(Q_0,Q_0)\,r_\mathfrak p(L)\,\|\det H_{T_0}\|^{n'} =
  \beta_\mathfrak p(Q',Q')\,\beta_\mathfrak p(L, T)\,\|\det g\|^{n'+1}.$$
Every prime, dyadic included; every $n' \ge 0$. For $L = \mathcal O_F^N$, $T_\ell = \mathcal O_F^r$ it is `frameLocalIdentityGen`. -/
@[kb "weil1982" "§3.4 and §4.5 (local identity for lattices, every prime) [unverified]"]
theorem latFrameLocalIdentity [IsTotallyReal F] {r n' : ℕ} (hr : 1 ≤ r) (Q₀ : QuadForm (𝓞 F) (r + n'))
    (hQ₀ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate)
    (fr : AdaptedFrameT (formF Q₀) (formF T₀)) (L : Lat F (r + n')) (hLi : Lattices.IsIntegral (formF Q₀) L.1)
    (Tl : Lat F r) (hTi : Lattices.IsIntegral (formF T₀) Tl.1) :
    locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1) *
        NF.localDensityForm v Q₀ Q₀ * locRatio v Q₀ L *
        ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * latBetaT v Q₀ L T₀ Tl *
        ‖algebraMap F Fv fr.g.val.det‖ ^ (n' + 1) := by
  obtain ⟨A, hA⟩ := exists_isLocModel' v (by omega : 1 ≤ r + n') L
  obtain ⟨B, hB⟩ := exists_isLocModel' v hr Tl
  have hAi := hA.isIntegral v hLi
  have hBi := hB.isIntegral v hTi
  set QA := gramZ (formF Q₀) A hAi with hQAdef
  set TB := gramZ (formF T₀) B hBi with hTBdef
  have hQA : QA.Nondegenerate := nondegenerate_gramZ hQ₀ A hAi
  have hTB : TB.Nondegenerate := nondegenerate_gramZ' hT B hBi
  let fr' : AdaptedFrameT (formF QA) (formF TB) :=
    { g := A⁻¹ * fr.g * blockDiagGL B
      Q' := fr.Q'
      compMat_eq := by
        rw [hQAdef, hTBdef, formF_gramZ, formF_gramZ, blockForm_compMat_diag, ← fr.compMat_eq, compMat_mul,
          Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
        rw [Units.mul_inv, Matrix.one_mul, compMat_mul] }
  have hG := Frames.frameLocalIdentityGen v QA hQA TB hTB fr'
  have hQ'nd : fr.Q'.Nondegenerate := Frames.adapted_nondegenerate Q₀ T₀ fr hQ₀
  have hQ'F : (formF fr.Q').Nondegenerate := formF_nondegenerate hQ'nd
  have hstdlat : (std v : Submodule (v.adicCompletionIntegers F) (Fin (r + n') → Fv)).IsLattice Fv := by
    have := loc_isLattice (v := v) (intVec_isLattice (F := F) (n := r + n'))
    rwa [loc_intVec] at this
  have hLloc : loc v L.1 = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) := by
    rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]
  have hTloc : loc v Tl.1 = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) B) (std v) := by
    rw [← hB.2, Lattices.latOf, loc_glImage, loc_intVec]
  have hΛ1 : loc v (Lat.image fr.g⁻¹ L).1 = locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr.g⁻¹)
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v)) := by
    show loc v (glImage fr.g⁻¹ L.1) = _
    rw [loc_glImage, hLloc]
  have hΛ1lat : (loc v (Lat.image fr.g⁻¹ L).1).IsLattice Fv := loc_isLattice v (Lat.image fr.g⁻¹ L).2
  have hDE : ∀ t : Fin r → Fv, (Dloc v B : GL (Fin (r + n')) Fv).val *ᵥ
      ((stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t) =
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ
        ((Matrix.GeneralLinearGroup.map (algebraMap F Fv) B).val *ᵥ t) := by
    intro t
    rw [mulVec_mulVec, mulVec_mulVec, Dloc_val]
    exact congrArg (fun M => M *ᵥ t) (blockMat_mul_stdFrameMat _)
  have hΘ : ∀ M : Submodule (v.adicCompletionIntegers F) (Fin (r + n') → Fv),
      (∀ t ∈ loc v Tl.1, (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈ M) ↔
        (∀ t ∈ (std v : Submodule (v.adicCompletionIntegers F) (Fin r → Fv)),
          (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) *ᵥ t ∈
            locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ M) := by
    intro M
    rw [hTloc]
    constructor
    · intro h t ht
      refine mem_locAct.mpr ⟨(Dloc v B : GL (Fin (r + n')) Fv).val *ᵥ (stdFrameMat *ᵥ t), ?_, ?_⟩
      · rw [hDE]; exact h _ (mem_locAct.mpr ⟨t, ht, rfl⟩)
      · rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    · intro h t ht
      obtain ⟨s, hs, rfl⟩ := mem_locAct.mp ht
      obtain ⟨y, hy, hyE⟩ := mem_locAct.mp (h s hs)
      have : y = (Dloc v B : GL (Fin (r + n')) Fv).val *ᵥ (stdFrameMat *ᵥ s) := by
        rw [← hyE, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      rw [this, hDE] at hy
      exact hy
  have hΛeq : locAct v (Dloc v B : GL (Fin (r + n')) Fv)⁻¹ (loc v (Lat.image fr.g⁻¹ L).1) =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr'.g)⁻¹ (std v) := by
    rw [hΛ1, ← locAct_mul, ← locAct_mul]
    congr 1
    show _ = (Matrix.GeneralLinearGroup.map (algebraMap F Fv) (A⁻¹ * fr.g * blockDiagGL B))⁻¹
    simp only [Dloc, map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  have hTBF : formF TB = (formF T₀).compMat B.val := formF_gramZ _ B hBi
  have hΛ'lat : (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr'.g)⁻¹ (std v) :
      Submodule (v.adicCompletionIntegers F) (Fin (r + n') → Fv)).IsLattice Fv := locAct_isLattice _ hstdlat
  have hsum : locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1) =
      locFrameTypeSumG v (TB.map (algebraMap (𝓞 F) F)) (fr.Q'.map (algebraMap (𝓞 F) F))
        (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) fr'.g)⁻¹ (std v)) := by
    rw [locFrameTypeSumL_transport v (formF T₀) (formF fr.Q') hQ'F B hΛ1lat (loc v Tl.1) (std v) hΘ, hΛeq,
      ← hTBF]
    exact locFrameTypeSumL_std v (formF TB) (formF fr.Q') hQ'F hΛ'lat
  -- the α law for the model
  have hα := alpha_mul_normDet_eq v Q₀ hQ₀ (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (NF.Qp v QA)
    (map_Qp_gramZ v Q₀ A hAi)
  rw [← hLloc] at hα
  have hdetA : (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A).val.det = algebraMap F Fv A.val.det := by
    rw [RingHom.map_det]; rfl
  rw [hdetA, ← NF.localDensityForm_eq_completion] at hα
  have hsd : NF.siegelDensity v Q₀ Q₀ = (1 / 2 : ℝ) * NF.localDensityForm v Q₀ Q₀ := by
    simp [NF.siegelDensity]
  rw [hsd] at hα
  have hα' : NF.localDensityForm v QA QA * ‖algebraMap F Fv A.val.det‖ ^ (r + n' + 1) =
      NF.localDensityForm v Q₀ Q₀ * locRatio v Q₀ L := by
    unfold locRatio; linarith
  have hβ := latBetaT_eq_of_loc v (by omega : 1 ≤ r + n') hr Q₀ L hLi T₀ Tl hTi hA.2 hAi hB.2 hBi
  have hdetT : ‖algebraMap F Fv (algebraMap (𝓞 F) F TB.hessian.det)‖ =
      ‖algebraMap F Fv B.val.det‖ ^ 2 * ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖ := by
    have e1 : ∀ {n : ℕ} (Q : QuadForm (𝓞 F) n), algebraMap (𝓞 F) F Q.hessian.det = (formF Q).hessian.det :=
      fun Q => by rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e1, e1, hTBF, hessian_compMat, det_mul, det_mul, det_transpose, map_mul, map_mul, norm_mul, norm_mul]
    ring
  have hdetg : ‖algebraMap F Fv fr'.g.val.det‖ =
      ‖algebraMap F Fv A.val.det‖⁻¹ * ‖algebraMap F Fv fr.g.val.det‖ * ‖algebraMap F Fv B.val.det‖ := by
    have h1 : (A⁻¹ : GL (Fin (r + n')) F).val.det * A.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    have h2 : fr'.g.val.det = A.val.det⁻¹ * fr.g.val.det * B.val.det := by
      show (A⁻¹ * fr.g * blockDiagGL B).val.det = _
      rw [Units.val_mul, Units.val_mul, det_mul, det_mul, blockDiagGL_val, det_blockMat_diag, det_one, mul_one,
        eq_inv_of_mul_eq_one_left h1]
    rw [h2, map_mul, map_mul, map_inv₀, norm_mul, norm_mul, norm_inv]
  have hG2 : locFrameTypeSumL v (formF T₀) (formF fr.Q') (loc v (Lat.image fr.g⁻¹ L).1) (loc v Tl.1) *
      NF.localDensityForm v QA QA *
        (‖algebraMap F Fv B.val.det‖ ^ 2 * ‖algebraMap F Fv (algebraMap (𝓞 F) F T₀.hessian.det)‖) ^ n' =
      NF.localDensityForm v fr.Q' fr.Q' * NF.localDensityForm v QA TB *
        (‖algebraMap F Fv A.val.det‖⁻¹ * ‖algebraMap F Fv fr.g.val.det‖ * ‖algebraMap F Fv B.val.det‖) ^ (n' + 1) := by
    rw [hsum, ← hdetT, ← hdetg]; exact hG
  have ha : ‖algebraMap F Fv A.val.det‖ ≠ 0 :=
    (norm_pos_iff.mpr ((map_ne_zero _).mpr (A.isUnit.map Matrix.detMonoidHom).ne_zero)).ne'
  have hb : ‖algebraMap F Fv B.val.det‖ ≠ 0 :=
    (norm_pos_iff.mpr ((map_ne_zero _).mpr (B.isUnit.map Matrix.detMonoidHom).ne_zero)).ne'
  rw [hβ]
  exact latLocal_alg _ _ _ _ _ _ _ _ _ _ r n' ha hb hG2 hα'

end QuadFormsKB.Tamagawa.FramesLat
