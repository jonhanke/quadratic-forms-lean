/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.LatticeLocalGenNF
import QuadFormsKB.Tamagawa.NonPIDEuler
import QuadFormsKB.Lattices.Steinitz

/-!
# Local densities of an arbitrary lattice, and the local orbital identity for it

**Layer:** a number field $F$ (any class number); a form $Q_0$ over $\mathcal O_F$ (the space $V = (F^N, Q_0)$); an **arbitrary**
$\mathcal O_F$-lattice $L$ on $V$ with $Q_0$ integral on $L$ (`Lat F N`, any Steinitz class: $L$ need not be free).

Every genus of integral lattices on a quadratic space over $F$ is of this form: choose an $F$-basis of $V$ inside $L$; then
$\mathcal O_F^N \subseteq L$ and $Q_0$ (the form in that basis) is integral on $\mathcal O_F^N$, i.e. a form over $\mathcal O_F$.

**Local models.** At a prime $\mathfrak p$ a *local free model* of $L$ is $A \in \mathrm{GL}_N(F)$ with $A\mathcal O_F^N \subseteq L$ and
$(A\mathcal O_F^N)_\mathfrak p = L_\mathfrak p$ (`IsLocModel`). It exists for every lattice (`exists_isLocModel`): Steinitz's normal form
$L = \gamma(\mathcal O_F^{N-1}\oplus\mathfrak c)$ (`Steinitz.exists_eq_glImage_steinitzLat`) and $a \in \mathfrak c$ with
$\mathrm{ord}_\mathfrak p a = \mathrm{ord}_\mathfrak p\mathfrak c$ give $A = \gamma\,\mathrm{diag}(1, \dots, 1, a)$. The Gram form $Q_A = Q_0\circ A$ of $A\mathcal O_F^N$
is a form over $\mathcal O_F$ (`gramZ`), and its completion is the Gram matrix of $L_\mathfrak p$ in a basis.

**Definition.** $\beta_\mathfrak p(L, m) = \|\det A\|_\mathfrak p\,\beta_\mathfrak p(Q_A, m)$ (`latBeta`): the local density of $m$ in $L_\mathfrak p$,
for the Haar measure of $F_\mathfrak p^N$ giving $\mathfrak o_\mathfrak p^N$ volume $1$ (the measure of the ambient coordinates in which the real
densities $\beta_\sigma(m)$ of `siegelProduct` are computed). It does not depend on the model (`latBeta_eq`: two models differ by
$\mathrm{GL}_N(\mathfrak o_\mathfrak p)$, `repCount_congr_isometricGL`), and for $L = \mathcal O_F^N$ it is the $\beta_\mathfrak p(L, m)$
(`latBeta_std`). `siegelProductLat Q₀ L m` is `siegelProduct` with these local factors, and `SiegelFormulaAtLat Q₀ L m` is
Siegel's formula for the genus of $L$.

**The local orbital identity for $L$ .** For an adapted frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$ and a local model
$A$ at $\mathfrak p$, $Q_A\circ(A^{-1}g) = \langle\rho\rangle\perp Q_0'$ is an adapted frame of the **global** form $Q_A$ whose frame lattice is
$g^{-1}A\mathfrak o_\mathfrak p^N = g^{-1}L_\mathfrak p$; the unconditional `orbitalLocalIdentities` for $Q_A$ and the
$\alpha$ law with non-integral local bases (`alpha_mul_normDet_eq`, from `LatticeLocalGenNF`) give
$$W_\mathfrak p(g^{-1}L_\mathfrak p, 1)\,\alpha_\mathfrak p(Q_0)\,r_\mathfrak p(L)\,|2\rho|_\mathfrak p^n\,|\det g|_\mathfrak p^{-(n+1)} =
  \alpha_\mathfrak p(Q_0')\,\beta_\mathfrak p(L, \rho)$$
(`latOrbitalIdentity`), $r_\mathfrak p(L) = r(K(L_\mathfrak p), K(\mathfrak o_\mathfrak p^N))$ the local index ratio of `tamagawaKLat`.

Sources: Weil 1982, §3.4 and §4.5, p. 109 [unverified]; Kitaoka 1993, §5.6 (local densities of lattices)
[unverified]; O'Meara 1963, 81:5, §82 [unverified].
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelLat

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
open QuadFormsKB.HilbertModular LatChange

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/-! ### Local free models -/

section Model

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **A local free model of $L$ at $\mathfrak p$**: $A \in \mathrm{GL}_N(F)$ with $A\mathcal O_F^N \subseteq L$ and $(A\mathcal O_F^N)_\mathfrak p = L_\mathfrak p$. -/
def IsLocModel (L : Lat F N) (A : GL (Fin N) F) : Prop :=
  Lattices.latOf A ≤ L.1 ∧ loc v (Lattices.latOf A) = loc v L.1

/-- The diagonal matrix $\mathrm{diag}(1, \dots, 1, a)$. -/
def lastDiag {m : ℕ} (a : F) : Fin (m + 1) → F := fun i => if i = Fin.last m then a else 1

theorem lastDiag_ne_zero {m : ℕ} {a : F} (ha : a ≠ 0) (i : Fin (m + 1)) : lastDiag a i ≠ 0 := by
  unfold lastDiag; split_ifs <;> simp [ha]

/-- $\mathrm{diag}(1, \dots, 1, a) \in \mathrm{GL}_{m+1}(F)$. -/
def lastDiagGL {m : ℕ} {a : F} (ha : a ≠ 0) : GL (Fin (m + 1)) F :=
  Matrix.nonsingInvUnit (diagonal (lastDiag a)) (isUnit_iff_ne_zero.mpr (by
    rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => lastDiag_ne_zero ha i))

theorem lastDiagGL_val {m : ℕ} {a : F} (ha : a ≠ 0) :
    (lastDiagGL (m := m) ha).val = diagonal (lastDiag a) := rfl

/-- A nonzero finitely generated $\mathcal O_F$-submodule of $F$ has an element of maximal valuation. -/
theorem exists_max_valuation {𝔠 : Submodule (𝓞 F) F} (hfg : 𝔠.FG) (hne : 𝔠 ≠ ⊥) :
    ∃ a ∈ 𝔠, a ≠ 0 ∧ ∀ c ∈ 𝔠, v.valuation F c ≤ v.valuation F a := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hne' : (s.filter (· ≠ 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    apply hne
    rw [← hs, Submodule.span_eq_bot]
    intro x hx; simpa using h hx
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image _ (fun c => v.valuation F c) hne'
  rw [Finset.mem_filter] at ha
  refine ⟨a, hs ▸ Submodule.subset_span ha.1, ha.2, fun c hc => ?_⟩
  rw [← hs] at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]; exact zero_le
    · exact hmax x (Finset.mem_filter.mpr ⟨hx, hx0⟩)
  | zero => rw [map_zero]; exact zero_le
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    calc v.valuation F (algebraMap (𝓞 F) F r) * v.valuation F x ≤ 1 * v.valuation F x :=
          mul_le_mul_left (v.valuation_le_one r) _
      _ = _ := one_mul _
      _ ≤ _ := hx

/-- **Every lattice has a local free model at every prime** (Steinitz's normal form, O'Meara 81:5 [unverified]). -/
@[kb "omeara1963" "81:5 (Steinitz normal form; local freeness) [unverified]"]
theorem exists_isLocModel {m : ℕ} (L : Lat F (m + 1)) : ∃ A, IsLocModel v L A := by
  classical
  obtain ⟨γ, 𝔠, hL⟩ := Steinitz.exists_eq_glImage_steinitzLat L.2
  set prj : (Fin (m + 1) → F) →ₗ[𝓞 F] F :=
    (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F)
  -- `𝔠` is the image of `γ⁻¹ L` under the last coordinate
  have hγinv : glImage γ⁻¹ L.1 = Steinitz.steinitzLat 𝔠 := by
    rw [hL, ← glImage_mul, inv_mul_cancel, glImage_one]
  have h𝔠 : 𝔠 = (Steinitz.steinitzLat (m := m) 𝔠).map prj := by
    ext c
    constructor
    · intro hc
      refine ⟨Pi.single (Fin.last m) c, ⟨fun i => ⟨0, ?_⟩, by simpa using hc⟩, by simp [prj]⟩
      simp [Fin.castSucc_ne_last]
    · rintro ⟨x, hx, rfl⟩; exact hx.2
  have hfg : 𝔠.FG := by
    rw [h𝔠, ← hγinv]
    exact (L.2.fg.map _).map _
  -- `𝔠 ≠ 0`: otherwise `L` lies in a hyperplane
  have hne : 𝔠 ≠ ⊥ := by
    intro h0
    set f : (Fin (m + 1) → F) →ₗ[F] F :=
      (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).comp (Matrix.mulVecLin γ⁻¹.val)
    have hsub : (L.1 : Set (Fin (m + 1) → F)) ⊆ LinearMap.ker f := by
      intro x hx
      have hx' : γ⁻¹.val *ᵥ x ∈ Steinitz.steinitzLat 𝔠 := hγinv ▸ mulVec_mem_glImage hx
      have := hx'.2
      rw [h0, Submodule.mem_bot] at this
      simpa [f] using this
    have htop := Submodule.span_le.mpr hsub
    rw [L.2.span_eq_top] at htop
    have h1 := htop (Submodule.mem_top (x := γ.val *ᵥ Pi.single (Fin.last m) 1))
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Matrix.mulVecLin_apply, mulVec_mulVec,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, LinearMap.proj_apply] at h1
    simp at h1
  obtain ⟨a, ha𝔠, ha0, hmax⟩ := exists_max_valuation v hfg hne
  set D := lastDiagGL (m := m) ha0
  refine ⟨γ * D, ?_, ?_⟩
  · -- `γ D 𝓞^N ⊆ γ (𝓞^m ⊕ 𝔠)`
    rw [hL, Lattices.latOf, glImage_mul]
    refine Submodule.map_mono fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
    obtain ⟨z, rfl⟩ := mem_intVec_iff_exists.mp hy
    refine ⟨fun i => ⟨z i.castSucc, ?_⟩, ?_⟩
    · simp [D, lastDiagGL_val, mulVec_diagonal, lastDiag, Fin.castSucc_ne_last, intCoe]
    · simp only [D, lastDiagGL_val, mulVec_diagonal, lastDiag, if_true]
      rw [show a * intCoe z (Fin.last m) = z (Fin.last m) • a by
        rw [Algebra.smul_def, mul_comm]]
      exact 𝔠.smul_mem _ ha𝔠
  · rw [Lattices.latOf, glImage_mul, hL, loc_glImage v γ, loc_glImage v γ]
    congr 1
    refine le_antisymm (loc_mono v ?_) ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
      obtain ⟨z, rfl⟩ := mem_intVec_iff_exists.mp hy
      refine ⟨fun i => ⟨z i.castSucc, ?_⟩, ?_⟩
      · simp [D, lastDiagGL_val, mulVec_diagonal, lastDiag, Fin.castSucc_ne_last, intCoe]
      · simp only [D, lastDiagGL_val, mulVec_diagonal, lastDiag, if_true]
        rw [show a * intCoe z (Fin.last m) = z (Fin.last m) • a by
          rw [Algebra.smul_def, mul_comm]]
        exact 𝔠.smul_mem _ ha𝔠
    · rw [loc, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      -- the coefficients `x_i / d_i ∈ 𝔬`
      have hcoef : ∀ i, Valued.v (algebraMap F Fv (x i / lastDiag a i)) ≤ 1 := by
        intro i
        rw [valued_algebraMap]
        by_cases hi : i = Fin.last m
        · subst hi
          simp only [lastDiag, if_true, map_div₀]
          have hva : v.valuation F a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
          rw [div_le_one₀ (zero_lt_iff.mpr hva)]
          exact hmax _ hx.2
        · simp only [lastDiag, hi, if_false, div_one]
          obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.mpr hi
          obtain ⟨b, hb⟩ := hx.1 i'
          rw [← hb]; exact v.valuation_le_one b
      have hsum : locVec v x = ∑ i, toO v _ (hcoef i) • locVec v (D.val *ᵥ Pi.single i 1) := by
        funext k
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_apply_coe, locVec_apply, toO, D, lastDiagGL_val, mulVec_diagonal,
          Pi.single_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
        simp only [if_true]
        show _ = algebraMap F Fv (x k / lastDiag a k) * algebraMap F Fv (lastDiag a k)
        rw [← map_mul, div_mul_cancel₀ _ (lastDiag_ne_zero ha0 k)]
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (locVec_mem_loc v (mulVec_mem_glImage (single_one_mem_intVec i)))

theorem IsLocModel.isIntegral {L : Lat F N} {A : GL (Fin N) F} (h : IsLocModel v L A) {Q : QuadForm F N}
    (hL : Lattices.IsIntegral Q L.1) : Lattices.IsIntegral Q (Lattices.latOf A) := fun x hx => hL x (h.1 hx)

end Model

/-! ### The local density of a lattice -/

section Beta

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The Gram form of $A\mathcal O_F^N$ over $F$ is $Q_0\circ A$. -/
theorem formF_gramZ (Q₀ : QuadForm (𝓞 F) N) (A : GL (Fin N) F)
    (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) :
    formF (gramZ (formF Q₀) A h) = (formF Q₀).compMat A.val :=
  QuadForm.ext_eval fun y => by
    show ((gramZ (formF Q₀) A h).map (algebraMap (𝓞 F) F)).eval y = _
    rw [gramZ_map, eval_gramFormF_col, eval_compMat]

/-- The completion of the Gram form of $A\mathcal O_F^N$ is $Q_0\circ A$ over $F_\mathfrak p$. -/
theorem map_Qp_gramZ (Q₀ : QuadForm (𝓞 F) N) (A : GL (Fin N) F)
    (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) :
    (NF.Qp v (gramZ (formF Q₀) A h)).map (algebraMap 𝔬 Fv) =
      ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)).compMat (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A).val := by
  rw [map_Qp_eq, map_Qp_eq, show (gramZ (formF Q₀) A h).map (algebraMap (𝓞 F) F) = formF (gramZ (formF Q₀) A h) from rfl,
    formF_gramZ, ← map_compMat]
  rfl

/-- **The local density of $m$ in $L_\mathfrak p$ does not depend on the local free model**: if $(A_1\mathcal O_F^N)_\mathfrak p = (A_2\mathcal O_F^N)_\mathfrak p$
then $\|\det A_1\|\beta_\mathfrak p(Q_{A_1}, m) = \|\det A_2\|\beta_\mathfrak p(Q_{A_2}, m)$ ($A_1^{-1}A_2 \in \mathrm{GL}_N(\mathfrak o_\mathfrak p)$). -/
theorem normDet_mul_localDensity_eq (Q₀ : QuadForm (𝓞 F) N) {A₁ A₂ : GL (Fin N) F}
    (h₁ : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A₁)) (h₂ : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A₂))
    (he : loc v (Lattices.latOf A₁) = loc v (Lattices.latOf A₂)) (m : 𝓞 F) :
    ‖algebraMap F Fv A₁.val.det‖ * NF.localDensity v (gramZ (formF Q₀) A₁ h₁) m =
      ‖algebraMap F Fv A₂.val.det‖ * NF.localDensity v (gramZ (formF Q₀) A₂ h₂) m := by
  set g₁ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₁
  set g₂ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₂
  have hstd : locAct v (g₁⁻¹ * g₂) (std v) = std v := by
    have h := he
    rw [Lattices.latOf, Lattices.latOf, loc_glImage, loc_glImage, loc_intVec] at h
    rw [locAct_mul, ← h, locAct_inv_locAct]
  obtain ⟨U, hU⟩ := exists_GL_o_of_locAct_std v _ hstd
  have hUv : U.val.map (algebraMap 𝔬 Fv) = (g₁⁻¹ * g₂).val := congrArg Units.val hU
  have hform : NF.Qp v (gramZ (formF Q₀) A₂ h₂) = (NF.Qp v (gramZ (formF Q₀) A₁ h₁)).compMat U.val := by
    apply NF.map_injective (IsFractionRing.injective 𝔬 Fv)
    rw [← map_compMat, map_Qp_gramZ, map_Qp_gramZ, compMat_mul, hUv, ← Units.val_mul, mul_inv_cancel_left]
  have hiso : Siegel.IsometricGL (NF.Qp v (gramZ (formF Q₀) A₁ h₁)) (NF.Qp v (gramZ (formF Q₀) A₂ h₂)) :=
    ⟨U, fun x => by rw [hform, eval_compMat]⟩
  have hβ : NF.localDensity v (gramZ (formF Q₀) A₁ h₁) m = NF.localDensity v (gramZ (formF Q₀) A₂ h₂) m := by
    rw [NF.localDensity_eq_completion, NF.localDensity_eq_completion]
    unfold DVR.localDensity
    simp_rw [repCount_congr_isometricGL hiso]
  have hdet : algebraMap F Fv A₂.val.det = algebraMap F Fv A₁.val.det * ((U.val.det : 𝔬) : Fv) := by
    have e1 : algebraMap F Fv A₂.val.det = g₂.val.det := by
      rw [RingHom.map_det]; rfl
    have e2 : algebraMap F Fv A₁.val.det = g₁.val.det := by
      rw [RingHom.map_det]; rfl
    have e3 : ((U.val.det : 𝔬) : Fv) = (g₁⁻¹ * g₂).val.det := by
      rw [← hUv, show ((U.val.det : 𝔬) : Fv) = algebraMap 𝔬 Fv U.val.det from rfl, RingHom.map_det]; rfl
    rw [e1, e2, e3, ← det_mul, ← Units.val_mul, mul_inv_cancel_left]
  have hU1 : ‖((U.val.det : 𝔬) : Fv)‖ = 1 := norm_coe_unit v (U.isUnit.map Matrix.detMonoidHom)
  rw [hdet, norm_mul, hU1, mul_one, hβ]

open Classical in
/-- **$\beta_\mathfrak p(L, m)$, the local density of $m$ in the lattice $L_\mathfrak p$** (Kitaoka 1993, §5.6 [unverified]; for the Haar measure of
$F_\mathfrak p^N$ with $\mathrm{vol}(\mathfrak o_\mathfrak p^N) = 1$): $\|\det A\|_\mathfrak p\,\beta_\mathfrak p(Q_0\circ A, m)$ for a local free model $A$ of $L$ at
$\mathfrak p$ (`IsLocModel`), $0$ if $L$ is not integral (no model with an integral Gram form). Independent of $A$ (`latBeta_eq`). -/
@[kb "kitaoka1993" "§5.6 (local densities of lattices) [unverified]"]
def latBeta (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  if h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral (formF Q₀) (Lattices.latOf A) then
    ‖algebraMap F Fv h.choose.val.det‖ * NF.localDensity v (gramZ (formF Q₀) h.choose h.choose_spec.2) m
  else 0

/-- `latBeta` computed with any local free model. -/
theorem latBeta_eq (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) {A : GL (Fin N) F} (hA : IsLocModel v L A)
    (hint : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) (m : 𝓞 F) :
    latBeta v Q₀ L m = ‖algebraMap F Fv A.val.det‖ * NF.localDensity v (gramZ (formF Q₀) A hint) m := by
  have h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral (formF Q₀) (Lattices.latOf A) := ⟨A, hA, hint⟩
  rw [latBeta, dif_pos h]
  exact normDet_mul_localDensity_eq v Q₀ _ _ (h.choose_spec.1.2.trans hA.2.symm) m

/-- **For $L = \mathcal O_F^N$, $\beta_\mathfrak p(L, m)$ is the local density** (the model $A = 1$). -/
theorem latBeta_std [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    latBeta v Q₀ (stdLat F N) m = NF.localDensity v Q₀ m := by
  have hA : IsLocModel v (stdLat F N) 1 := ⟨by rw [HilbertModular.latOf_one], by rw [HilbertModular.latOf_one]⟩
  rw [latBeta_eq v Q₀ _ hA (isIntegral_latOf_one Q₀), gramZ_one, Units.val_one, det_one, map_one, norm_one, one_mul]

end Beta

/-! ### The $\alpha$ law for arbitrary local bases -/

section AlphaGen

variable (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **The $\alpha$ law for a local basis $P \in \mathrm{GL}_n(F_\mathfrak p)$ with an integral Gram form** $T = Q_0\circ P$ (the local step of
`tamagawaKLat_eq_local_gen`, stated for one prime): $\tfrac12\beta_\mathfrak p(T, T)\,\|\det P\|^{n+1} = \alpha_\mathfrak p(Q_0)\cdot
r(K(P\mathfrak o_\mathfrak p^n), K(\mathfrak o_\mathfrak p^n))$. *Proof:* $\varpi^kP$ is integral; `latLocalFactor_eq` (the $\alpha$ law at every prime),
$\beta(\varpi^{2k}T) = q^{kn(n+1)}\beta(T)$ and the invariance of the stabilizer under scalars. -/
@[kb "weil1982" "§2.4 and §3.4 (Haar measures of lattice stabilizers) [unverified]"]
theorem alpha_mul_normDet_eq (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (P : GL (Fin n) Fv)
    (T : QuadForm 𝔬 n)
    (hT : T.map (algebraMap _ (v.adicCompletion F)) =
      ((NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).compMat P.val) :
    (1 / 2 : ℝ) * DVR.localDensityForm T T (NF.π v) * ‖P.val.det‖ ^ (n + 1) =
      NF.siegelDensity v Q₀ Q₀ *
        relRatio (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype (locAct v P (std v)))
          (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) := by
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set r := relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (locAct v P (std v))) (stdStab QF v)
  have hπ := NF.irreducible_π v
  obtain ⟨k, hk⟩ := exists_pi_pow_integral v P.val
  choose c hc using hk
  set P' : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) := Matrix.of c
  have hP'map : P'.map (algebraMap _ (v.adicCompletion F)) =
      (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ k • P.val := by
    ext i j; simp [P', hc]
  have hdetP' : (algebraMap _ (v.adicCompletion F) P'.det) =
      (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ (k * n) * P.val.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hP'map, det_smul, Fintype.card_fin, ← pow_mul]
  have hπF : algebraMap _ (v.adicCompletion F) (NF.π v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hπ.ne_zero
  have hPd : P.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
  have hP'0 : P'.det ≠ 0 := fun h0 => by
    have := hdetP'
    rw [h0, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero _ hπF) hPd) this.symm
  -- the form of `P'`
  have hform : (NF.Qp v Q₀).compMat P' = NF.π v ^ (2 * k) • T := by
    apply NF.map_injective (IsFractionRing.injective _ (v.adicCompletion F))
    rw [← map_compMat, hP'map, compMat_smul_mat, map_smul_form, ← hT, ← pow_mul, map_pow, mul_comm]
  have hTnd : T.Nondegenerate := by
    intro h0
    have h1 := congrArg (fun S : QuadForm (v.adicCompletion F) n => S.hessian.det) (hT)
    simp only [hessian_compMat, det_mul, det_transpose] at h1
    rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
    have hQnd : ((NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).hessian.det ≠ 0 := by
      rw [QuadForm.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, NF.det_hessian_Qp]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (NF.ι_ne_zero v hQ₀)
    exact mul_ne_zero (mul_ne_zero hPd hQnd) hPd h1.symm
  -- the local factor of `P'`
  have hlf := latLocalFactor_eq v Q₀ hQ₀ P' hP'0
  unfold latLocalFactor at hlf
  rw [hform, localDensityForm_smul_pi_pow v T hTnd] at hlf
  -- the stabilizers
  have hsc : ((NF.π v ^ k) • (1 : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))).map
      (algebraMap _ (v.adicCompletion F)) = (algebraMap _ (v.adicCompletion F) (NF.π v)) ^ k • 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hglOf : glOf v P' hP'0 = glOf v ((NF.π v ^ k) • (1 : Matrix (Fin n) (Fin n) _))
      (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ (pow_ne_zero _ hπ.ne_zero)) * P := by
    apply Units.ext
    rw [Units.val_mul, glOf_val, glOf_val, hP'map, hsc, Matrix.smul_mul, Matrix.one_mul]
  have hstab : stabLat v (orthGroup QF (v.adicCompletion F)).subtype (locAct v (glOf v P' hP'0) (std v)) =
      stabLat v (orthGroup QF (v.adicCompletion F)).subtype (locAct v P (std v)) := by
    rw [hglOf, locAct_mul]
    exact stabLat_locAct_scalar v _ _ _ (by rw [glOf_val, hsc]) _
  have hr : r = relRatio (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))
        (locAct v (glOf v P' hP'0) (std v)))
      (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) (std v)) := by
    rw [show r = relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (locAct v P (std v)))
      (stdStab QF v) from rfl, ← hstab, relRatio_stab_eq_KL]
  rw [hr, ← hlf]
  -- `‖det P'‖ = q^{-kn} ‖det P‖`
  have hnorm : ‖((P'.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ((DVR.q (v.adicCompletionIntegers F) : ℝ)⁻¹) ^ (k * n) * ‖P.val.det‖ := by
    rw [show ((P'.det : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap _ (v.adicCompletion F) P'.det from rfl, hdetP', norm_mul, norm_pow]
    congr 2
    have := norm_coe_of_pow_dvd v (x := NF.π v) (e := 1) (by simp)
      (by rw [pow_succ, pow_one]; exact fun h => hπ.not_isUnit (isUnit_of_dvd_one
        ((mul_dvd_mul_iff_left hπ.ne_zero).1 (by simpa using h))))
    rw [pow_one] at this; exact this
  rw [hnorm]
  have hq : (0 : ℝ) < DVR.q (v.adicCompletionIntegers F) := by exact_mod_cast DVR.q_pos
  have hexp : n * (n + 1) / 2 * (2 * k) = k * n * (n + 1) := by
    have : n * (n + 1) % 2 = 0 := Nat.even_iff.1 (Nat.even_mul_succ_self n)
    have h2 : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero this)
    calc n * (n + 1) / 2 * (2 * k) = (n * (n + 1) / 2 * 2) * k := by ring
      _ = k * n * (n + 1) := by rw [h2]; ring
  have e1 : ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (n * (n + 1) / 2)) ^ (2 * k) =
      (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * n * (n + 1)) := by rw [← pow_mul, hexp]
  have e2 : ((((DVR.q (v.adicCompletionIntegers F) : ℝ))⁻¹) ^ (k * n) * ‖P.val.det‖) ^ (n + 1) =
      ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * n * (n + 1)))⁻¹ * ‖P.val.det‖ ^ (n + 1) := by
    rw [mul_pow, ← pow_mul, inv_pow]
  rw [e1, e2]
  field_simp

end AlphaGen

/-! ### The local orbital identity for an arbitrary lattice -/

section Orbital

variable [IsTotallyReal F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- $r_\mathfrak p(L) = r(K(L_\mathfrak p), K(\mathfrak o_\mathfrak p^N))$, the local index ratio of the stabilizers in $O(V)(F_\mathfrak p)$
(the local factor of `tamagawaKLat` over `tamagawaK`). -/
def locRatio (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) : ℝ :=
  relRatio (stabLat v (orthGroup (formF Q₀) Fv).subtype (loc v L.1)) (stdStab (formF Q₀) v)

theorem formF_nondegenerate {Q₀ : QuadForm (𝓞 F) N} (hQ₀ : Q₀.Nondegenerate) : (formF Q₀).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ₀

theorem nondegenerate_gramZ {Q₀ : QuadForm (𝓞 F) N} (hQ₀ : Q₀.Nondegenerate) (A : GL (Fin N) F)
    (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) : (gramZ (formF Q₀) A h).Nondegenerate := by
  apply nondegenerate_of_map
  rw [show (gramZ (formF Q₀) A h).map (algebraMap (𝓞 F) F) = formF (gramZ (formF Q₀) A h) from rfl, formF_gramZ,
    QuadForm.Nondegenerate, hessian_compMat, det_mul, det_mul, det_transpose]
  have hA : A.val.det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
  exact mul_ne_zero (mul_ne_zero hA (formF_nondegenerate hQ₀)) hA

/-- **The frame of the model form**: $Q_A\circ(A^{-1}g) = Q_0\circ g = \langle\rho\rangle\perp Q_0'$. -/
def modelFrame (Q₀ : QuadForm (𝓞 F) (n + 1)) {ρ : F} (fr : AdaptedFrame (formF Q₀) ρ) (A : GL (Fin (n + 1)) F)
    (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) : AdaptedFrame (formF (gramZ (formF Q₀) A h)) ρ where
  g := A⁻¹ * fr.g
  Q' := fr.Q'
  compMat_eq := by rw [formF_gramZ, compMat_mul, ← Units.val_mul, mul_inv_cancel_left, fr.compMat_eq]

/-- The frame lattice of the model frame is $g^{-1}L_\mathfrak p$. -/
theorem frameLat_modelFrame (Q₀ : QuadForm (𝓞 F) (n + 1)) {ρ : F} (fr : AdaptedFrame (formF Q₀) ρ) (L : Lat F (n + 1))
    {A : GL (Fin (n + 1)) F} (hA : IsLocModel v L A) (h : Lattices.IsIntegral (formF Q₀) (Lattices.latOf A)) :
    frameLat v (modelFrame Q₀ fr A h).g = loc v (glImage fr.g⁻¹ L.1) := by
  show loc v (glImage (A⁻¹ * fr.g)⁻¹ intVec) = _
  rw [_root_.mul_inv_rev, inv_inv, glImage_mul, loc_glImage v fr.g⁻¹, loc_glImage v fr.g⁻¹]
  congr 1
  exact hA.2

/-- **The local orbital identity for the genus of an arbitrary lattice $L$** (Weil 1982, §3.4 and §4.5, p. 109 [unverified]): for an adapted
frame $Q_0\circ g = \langle\rho\rangle\perp Q_0'$, $\rho = m \ne 0$,
$$W_\mathfrak p(g^{-1}L_\mathfrak p, 1)\,\alpha_\mathfrak p(Q_0)\,r_\mathfrak p(L)\,|2\rho|_\mathfrak p^n\,|\det g|_\mathfrak p^{-(n+1)} = \alpha_\mathfrak p(Q_0')\,\beta_\mathfrak p(L, m).$$
*Proof:* for a local free model $A$, the unconditional `orbitalLocalIdentities` of the global form $Q_A$ at its frame
$A^{-1}g$ (frame lattice $g^{-1}L_\mathfrak p$, `frameLat_modelFrame`), and the $\alpha$ law $\alpha_\mathfrak p(Q_A)\|\det A\|^{n+2} = \alpha_\mathfrak p(Q_0)\,r_\mathfrak p(L)$
(`alpha_mul_normDet_eq`). -/
@[kb "weil1982" "§3.4 and §4.5, p. 109 (local fibration for the lattice L) [unverified]"]
theorem latOrbitalIdentity (Q₀ : QuadForm (𝓞 F) (n + 1)) (hQ₀ : Q₀.Nondegenerate) (hn : 1 ≤ n) (L : Lat F (n + 1))
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F} {ρ : F} (hmρ : algebraMap (𝓞 F) F m = ρ) (hρ : ρ ≠ 0)
    (fr : AdaptedFrame (formF Q₀) ρ) :
    locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F Fv 1) *
        NF.siegelDensity v Q₀ Q₀ * locRatio v Q₀ L * ‖(2 : Fv) * algebraMap F Fv ρ‖ ^ n *
        (‖algebraMap F Fv fr.g.val.det‖ ^ (n + 1))⁻¹ =
      NF.siegelDensity v fr.Q' fr.Q' * latBeta v Q₀ L m := by
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  set Q₁ := gramZ (formF Q₀) A hint
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_gramZ hQ₀ A hint
  set fr₁ := modelFrame Q₀ fr A hint
  have hj := (orbitalLocalIdentityAt_all (orbitalLocalIdentities Q₁ hQ₁) hQ₁ hn hρ fr₁ v).eq 0
  simp only [zero_mul, zpow_zero, mul_zero, mul_one] at hj
  rw [show locW v fr₁ 0 = locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v (glImage fr.g⁻¹ L.1))
      (algebraMap F Fv 1) by
    unfold locW; rw [frameLat_modelFrame v Q₀ fr L hA hint, zpow_zero, map_one]; rfl] at hj
  rw [show betaZ v Q₁ (algebraMap F Fv ρ) = NF.localDensity v Q₁ m by rw [← hmρ]; exact betaZ_algebraMap v Q₁ m] at hj
  -- the α law for the model
  have hα := alpha_mul_normDet_eq v Q₀ hQ₀ (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (NF.Qp v Q₁)
    (map_Qp_gramZ v Q₀ A hint)
  have hloc : locAct v (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A) (std v) = loc v L.1 := by
    rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]
  rw [hloc] at hα
  have hα₁ : NF.siegelDensity v Q₁ Q₁ = (1 / 2 : ℝ) * DVR.localDensityForm (NF.Qp v Q₁) (NF.Qp v Q₁) (NF.π v) := by
    simp only [NF.siegelDensity, ite_true, NF.localDensityForm_eq_completion]
  rw [← hα₁] at hα
  have hdetA : (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A).val.det = algebraMap F Fv A.val.det := by
    rw [RingHom.map_det]; rfl
  rw [hdetA] at hα
  have hdet₁ : algebraMap F Fv fr₁.g.val.det = (algebraMap F Fv A.val.det)⁻¹ * algebraMap F Fv fr.g.val.det := by
    show algebraMap F Fv (A⁻¹ * fr.g).val.det = _
    have h1 : (A⁻¹ : GL (Fin (n + 1)) F).val.det * A.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
    rw [Units.val_mul, det_mul, map_mul, eq_inv_of_mul_eq_one_left h1, map_inv₀]
  rw [hdet₁] at hj
  rw [latBeta_eq v Q₀ L hA hint]
  -- algebra
  simp only [norm_mul, norm_inv] at hj ⊢
  set a := ‖algebraMap F Fv A.val.det‖
  have ha : 0 < a := norm_pos_iff.mpr ((map_ne_zero _).mpr (A.isUnit.map Matrix.detMonoidHom).ne_zero)
  set G := ‖algebraMap F Fv fr.g.val.det‖
  have hG : 0 < G := norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)
  unfold locRatio
  generalize locTypeSumG v ρ (fr.Q'.map (algebraMap (𝓞 F) F)) (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F Fv 1) = W at hj ⊢
  generalize (‖(2 : Fv)‖ * ‖algebraMap F Fv ρ‖) ^ n = B at hj ⊢
  rw [mul_pow, inv_pow, mul_inv, inv_inv, show fr₁.Q' = fr.Q' from rfl] at hj
  linear_combination a * hj - W * B * (G ^ (n + 1))⁻¹ * hα

end Orbital

/-! ### Siegel's product and Siegel's formula for the genus of a lattice -/

section Product

/-- **The local positivity of $r_\mathfrak p(L)$**: $\alpha_\mathfrak p(Q_A)\|\det A\|^{N+1} = \alpha_\mathfrak p(Q_0)\,r_\mathfrak p(L)$ with both $\alpha$'s positive. -/
theorem locRatio_pos [IsTotallyReal F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {Q₀ : QuadForm (𝓞 F) (n + 1)}
    (hQ₀ : Q₀.Nondegenerate) (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) : 0 < locRatio v Q₀ L := by
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  set Q₁ := gramZ (formF Q₀) A hint
  have hQ₁ : Q₁.Nondegenerate := nondegenerate_gramZ hQ₀ A hint
  have hα := alpha_mul_normDet_eq v Q₀ hQ₀ (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A)
    (NF.Qp v Q₁) (map_Qp_gramZ v Q₀ A hint)
  have hloc : locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A) (std v) = loc v L.1 := by
    rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]
  rw [hloc] at hα
  have hα₁ : NF.siegelDensity v Q₁ Q₁ = (1 / 2 : ℝ) * DVR.localDensityForm (NF.Qp v Q₁) (NF.Qp v Q₁) (NF.π v) := by
    simp only [NF.siegelDensity, ite_true, NF.localDensityForm_eq_completion]
  rw [← hα₁] at hα
  have h1 : 0 < NF.siegelDensity v Q₁ Q₁ * ‖(Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A).val.det‖ ^
      (n + 1 + 1) := by
    refine mul_pos (siegelDensity_pos v Q₁ hQ₁) (pow_pos (norm_pos_iff.mpr ?_) _)
    exact ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A).isUnit.map
      Matrix.detMonoidHom).ne_zero
  rw [hα] at h1
  exact pos_of_mul_pos_right h1 (siegelDensity_pos v Q₀ hQ₀).le

/-- $r_\mathfrak p(L) = 1$ where $L_\mathfrak p = \mathfrak o_\mathfrak p^N$. -/
theorem locRatio_eq_one [IsTotallyReal F] (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N)
    (h : loc v L.1 = std v) : locRatio v Q₀ L = 1 := by
  unfold locRatio; rw [h, ← stdStab_eq_stabLat, relRatio_self]

/-- **$\mu_{\mathrm{Tam}}(K_{SO}(L)) = \mu_{\mathrm{Tam}}(K_{SO}(\mathcal O_F^N))\prod_\mathfrak pr_\mathfrak p(L)$** (the restricted product of the local index ratios). -/
theorem tamagawaKLat_eq_finprod [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) :
    tamagawaKLat Q₀ L = tamagawaK Q₀ * ∏ᶠ v, locRatio v Q₀ L := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v L.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  have hR : relRatio (locStab QF L) (locStab QF (stdLat F N)) = ∏ v ∈ S, locRatio v Q₀ L := by
    rw [relRatio_symm', relRatio_locStab_eq_prod QF L S hS, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (relRatio_symm' _ _).symm
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by
    by_contra h; exact hv (locRatio_eq_one v Q₀ L (hS v h))]
  unfold tamagawaKLat; rw [hR]

/-- **Siegel's product for the genus of an arbitrary lattice $L$** (Siegel 1935, Hauptsatz; over $F$ [unverified]):
$$S(L, m) = |d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(m)\prod_\mathfrak p\beta_\mathfrak p(L, m),$$
`siegelProduct` with the local densities $\beta_\mathfrak p(L, m)$ of `latBeta` (the real densities $\beta_\sigma(m)$ are those of the ambient
coordinates of $V = F^N$, matching the normalization of $\beta_\mathfrak p(L, m)$). For $L = \mathcal O_F^N$ it is `siegelProduct`
(`siegelProductLat_std`). Use only for $N \ge 4$ (rank $3$ needs the regularized product, rank $\le 2$ Siegel's $\varepsilon = \tfrac12$). -/
@[kb "siegel1935" "Hauptsatz (local side, arbitrary lattice; over F [unverified])"]
def siegelProductLat (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) *
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity N ‖σ (algebraMap (𝓞 F) F m)‖ (detGram Q₀ σ)) *
    ∏' v : HeightOneSpectrum (𝓞 F), latBeta v Q₀ L m

theorem siegelProductLat_std [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    siegelProductLat Q₀ (stdLat F N) m = siegelProduct Q₀ m := by
  unfold siegelProductLat siegelProduct; simp_rw [latBeta_std]

/-- **Siegel's formula for the number $m$ and the genus of an arbitrary lattice $L$** on $V = (F^N, Q_0)$ (Siegel 1935, Hauptsatz
[unverified]; any Steinitz class):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot S(L, m).$$

Field:
- `repMass_eq`: `repMass (formF Q₀) L m = mass (formF Q₀) L * siegelProductLat Q₀ L m`.

For $L = \mathcal O_F^N$ it is `SiegelFormulaAt Q₀ m` (`siegelFormulaAtLat_std_iff`). A statement (the conclusion of this file's
theorems), never assumed. -/
@[kb "siegel1935" "Hauptsatz (arbitrary lattice; over F [unverified])"]
structure SiegelFormulaAtLat (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (m : 𝓞 F) : Prop where
  repMass_eq : repMass (formF Q₀) L (algebraMap (𝓞 F) F m) = mass (formF Q₀) L * siegelProductLat Q₀ L m

/-- For $L = \mathcal O_F^N$ the lattice statement is `SiegelFormulaAt`. -/
theorem siegelFormulaAtLat_std_iff [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (m : 𝓞 F) :
    SiegelFormulaAtLat Q₀ (stdLat F N) m ↔ SiegelFormulaAt Q₀ m := by
  constructor
  · intro h; exact ⟨by rw [← siegelProductLat_std]; exact h.repMass_eq⟩
  · intro h; exact ⟨by rw [siegelProductLat_std]; exact h.repMass_eq⟩

end Product

end QuadFormsKB.Tamagawa.SiegelLat
