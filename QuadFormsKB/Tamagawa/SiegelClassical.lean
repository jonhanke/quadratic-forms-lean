/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelGenusV

/-!
# Siegel's formula with the classical, basis-free local densities

**Layer:** $F$ a number field; $(F^N, Q)$ a quadratic space over $F$ and $L$ an $\mathcal O_F$-lattice (`Lat F N`, any Steinitz
class) with $Q$ integral on $L$; then (headlines) an abstract quadratic space $(V, q)$ over a totally real number field.

**The classical local density** (Siegel 1935; Kitaoka 1993, §5.6; Hanke 2004, (5.1)–(5.2) [unverified for lattices]).
For a finite place $\mathfrak p$, choose any $\mathfrak o_\mathfrak p$-basis of $L_\mathfrak p$; with $T$ the Gram form of $Q$ in that
basis ($T(x) = Q(\sum_i x_ie_i)$, a form over $\mathfrak o_\mathfrak p$),
$$\beta_\mathfrak p(L, m) = \lim_{k\to\infty}\frac{\#\{x \in (\mathfrak o_\mathfrak p/\mathfrak p^k)^N : T(x) \equiv m \bmod \mathfrak p^k\}}
  {N\mathfrak p^{k(N-1)}} = \lim_k\frac{\#\{x \in L_\mathfrak p/\mathfrak p^kL_\mathfrak p : Q(x) \equiv m \bmod \mathfrak p^k\}}{N\mathfrak p^{k(N-1)}}$$
(`intrinsicBeta`; the library's `DVR.localDensity T`, the second count being the first one read through the basis).
It does
**not depend on the basis** (`intrinsicBeta_eq_of_localBasis`: any $P \in \mathrm{GL}_N(F_\mathfrak p)$ with $P\mathfrak o_\mathfrak p^N = L_\mathfrak p$;
two such differ by $\mathrm{GL}_N(\mathfrak o_\mathfrak p)$, an isometry of the Gram forms), nor on the coordinates of $V$
(`intrinsicBeta_compMat`). This is the density for the Haar measure of $F_\mathfrak p\otimes V$ giving $L_\mathfrak p$ volume $1$.

**Comparison with the coordinate densities.** `latBeta`/`spaceBeta` use the Haar measure giving the coordinate
lattice $\mathfrak o_\mathfrak p^N$ volume $1$: `spaceBeta v Q L m = locIndex v L * intrinsicBeta v Q L m` with
$\mathrm{locIndex}_\mathfrak p(L) = \|\det A\|_\mathfrak p$ for any local basis $A$ of $L_\mathfrak p$ (exponent $1$:
$\mathrm{vol}(L_\mathfrak p) = \|\det A\|_\mathfrak p\mathrm{vol}(\mathfrak o_\mathfrak p^N)$). Their product
$\mathrm{latIndex}(L) = \prod_\mathfrak p\|\det A_\mathfrak p\|_\mathfrak p = N(\mathfrak a_L)^{-1}$, $\mathfrak a_L = \prod_\mathfrak p\mathfrak p^{\mathrm{ord}_\mathfrak p\det A_\mathfrak p}$
the index ideal of $L$ relative to $\mathcal O_F^N$ (for $L \subseteq \mathcal O_F^N$: $[\mathcal O_F^N : L]^{-1}$).

**The discriminant.** $\mathfrak d(L) = \prod_\mathfrak p\mathfrak p^{\mathrm{ord}_\mathfrak p\det B_\mathfrak p}$, $B_\mathfrak p = \tfrac12H(Q\circ A_\mathfrak p)$ the Gram
matrix ($T(x) = x^{\mathsf T}B_\mathfrak px$) of a local basis — the discriminant (volume) ideal of $L$, a fractional ideal;
`discNorm Q L` $= N\mathfrak d(L) = \prod_\mathfrak p\|\det B_\mathfrak p\|_\mathfrak p^{-1}$, basis-free. By the product formula
(`discNorm_eq`) $N\mathfrak d(L) = \mathrm{latIndex}(L)^{-2}\prod_\sigma|\sigma\det B_Q|$, $B_Q = \tfrac12H(Q)$.

**The classical formula** (`siegelFormula_quadraticSpace_classical`, $\dim V = N \ge 4$):
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|}
  = \mathrm{Mass}(L)\cdot|d_F|^{-\frac{N-1}2}\,N\mathfrak d(L)^{-\frac12}\prod_{\sigma:F\to\mathbb R}\frac{\pi^{N/2}}{\Gamma(N/2)}\sigma(m)^{\frac{N-2}2}
  \prod_\mathfrak p\beta_\mathfrak p(L, m),$$
the real densities taken with Gram determinant $1$ (`archRepDensity N ‖σ m‖ 1`) and all of $\mathrm{vol}(L)$ collected in
$N\mathfrak d(L)^{-1/2}$. It is proved **equal to** gi's headline (`siegelProductClassicalV_eq`): the factor
$\prod_\sigma\det_\sigma(Q)^{-1/2}\cdot\mathrm{latIndex}(L) = N\mathfrak d(L)^{-1/2}$ (`prod_archRepDensity_mul_latIndex`). Ranks $3$, $2$
(regularized, $\varepsilon = \tfrac12$ in rank $2$) and $1$ ($\varepsilon = \tfrac12$, halved factors) likewise.

Sources: Siegel 1935, Hauptsatz [unverified]; Kitaoka 1993, §5.6 (local densities of lattices) [unverified]; O'Meara 1963,
§82 (discriminant of a lattice) [unverified]; Hanke 2004, (5.1)–(5.5), pp. 368–369 (density conventions).
-/

open NumberField IsDedekindDomain Module Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd QuadFormsKB.Tamagawa.SiegelLat LatChange

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/-! ### The local index and the classical local density -/

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- Two global matrices with the same local lattice at $\mathfrak p$ differ by $\mathrm{GL}_N(\mathfrak o_\mathfrak p)$. -/
theorem exists_GL_o_of_loc_eq {A₁ A₂ : GL (Fin N) F}
    (he : loc v (Lattices.latOf A₁) = loc v (Lattices.latOf A₂)) :
    ∃ U : GL (Fin N) 𝔬, U.val.map (algebraMap 𝔬 Fv) =
      ((Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₁)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₂).val := by
  have hstd : locAct v ((Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₁)⁻¹ *
      Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₂) (std v) = std v := by
    have h := he
    rw [Lattices.latOf, Lattices.latOf, loc_glImage, loc_glImage, loc_intVec] at h
    rw [locAct_mul, ← h, locAct_inv_locAct]
  obtain ⟨U, hU⟩ := exists_GL_o_of_locAct_std v _ hstd
  exact ⟨U, congrArg Units.val hU⟩

/-- **$\|\det A\|_\mathfrak p$ depends only on the local lattice $(A\mathcal O_F^N)_\mathfrak p$.** -/
theorem norm_det_eq_of_loc_eq {A₁ A₂ : GL (Fin N) F}
    (he : loc v (Lattices.latOf A₁) = loc v (Lattices.latOf A₂)) :
    ‖algebraMap F Fv A₁.val.det‖ = ‖algebraMap F Fv A₂.val.det‖ := by
  obtain ⟨U, hUv⟩ := exists_GL_o_of_loc_eq v he
  set g₁ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₁
  set g₂ := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A₂
  have hdet : algebraMap F Fv A₂.val.det = algebraMap F Fv A₁.val.det * ((U.val.det : 𝔬) : Fv) := by
    have e1 : algebraMap F Fv A₂.val.det = g₂.val.det := by rw [RingHom.map_det]; rfl
    have e2 : algebraMap F Fv A₁.val.det = g₁.val.det := by rw [RingHom.map_det]; rfl
    have e3 : ((U.val.det : 𝔬) : Fv) = (g₁⁻¹ * g₂).val.det := by
      rw [← hUv, show ((U.val.det : 𝔬) : Fv) = algebraMap 𝔬 Fv U.val.det from rfl, RingHom.map_det]; rfl
    rw [e1, e2, e3, ← det_mul, ← Units.val_mul, mul_inv_cancel_left]
  have hU1 : ‖((U.val.det : 𝔬) : Fv)‖ = 1 := norm_coe_unit v (U.isUnit.map Matrix.detMonoidHom)
  rw [hdet, norm_mul, hU1, mul_one]

/-- The completion of the Gram form of $A\mathcal O_F^N$ is $Q\circ A$ over $F_\mathfrak p$ (any form $Q$ over $F$). -/
theorem map_Qp_gramZ' (Q : QuadForm F N) (A : GL (Fin N) F) (h : Lattices.IsIntegral Q (Lattices.latOf A)) :
    (NF.Qp v (gramZ Q A h)).map (algebraMap 𝔬 Fv) =
      (Q.map (algebraMap F Fv)).compMat (Matrix.GeneralLinearGroup.map (algebraMap F Fv) A).val := by
  rw [map_Qp_eq, show (gramZ Q A h).map (algebraMap (𝓞 F) F) = formF (gramZ Q A h) from rfl,
    formF_gramZ', ← map_compMat]
  rfl

/-- **The local density of a Gram form of $L_\mathfrak p$ does not depend on the local basis** (global bases). -/
theorem localDensity_gramZ_eq (Q : QuadForm F N) {A₁ A₂ : GL (Fin N) F}
    (h₁ : Lattices.IsIntegral Q (Lattices.latOf A₁)) (h₂ : Lattices.IsIntegral Q (Lattices.latOf A₂))
    (he : loc v (Lattices.latOf A₁) = loc v (Lattices.latOf A₂)) (m : 𝓞 F) :
    NF.localDensity v (gramZ Q A₁ h₁) m = NF.localDensity v (gramZ Q A₂ h₂) m := by
  obtain ⟨U, hUv⟩ := exists_GL_o_of_loc_eq v he
  have hform : NF.Qp v (gramZ Q A₂ h₂) = (NF.Qp v (gramZ Q A₁ h₁)).compMat U.val := by
    apply NF.map_injective (IsFractionRing.injective 𝔬 Fv)
    rw [← map_compMat, map_Qp_gramZ', map_Qp_gramZ', compMat_mul, hUv, ← Units.val_mul, mul_inv_cancel_left]
  have hiso : Siegel.IsometricGL (NF.Qp v (gramZ Q A₁ h₁)) (NF.Qp v (gramZ Q A₂ h₂)) :=
    ⟨U, fun x => by rw [hform, eval_compMat]⟩
  rw [NF.localDensity_eq_completion, NF.localDensity_eq_completion]
  unfold DVR.localDensity
  simp_rw [repCount_congr_isometricGL hiso]

/-- Local free models exist in every rank (`exists_isLocModel`; rank $0$ is trivial). -/
theorem exists_isLocModel' (L : Lat F N) : ∃ A, IsLocModel v L A := by
  rcases N with _ | n
  · refine ⟨1, fun x _ => ?_, ?_⟩
    · rw [show x = 0 from Subsingleton.elim _ _]; exact L.1.zero_mem
    · ext x
      simp only [show x = 0 from Subsingleton.elim _ _, Submodule.zero_mem]
  · exact exists_isLocModel v L

open Classical in
/-- **The local index of $L$ at $\mathfrak p$**: $\|\det A\|_\mathfrak p$ for a local basis $A$ of $L_\mathfrak p$ (`IsLocModel`), i.e.
$\mathrm{vol}(L_\mathfrak p)/\mathrm{vol}(\mathfrak o_\mathfrak p^N) = N\mathfrak p^{-\mathrm{ord}_\mathfrak p\det A}$; independent of $A$
(`locIndex_eq`). -/
def locIndex (L : Lat F N) : ℝ :=
  if h : ∃ A, IsLocModel v L A then ‖algebraMap F Fv h.choose.val.det‖ else 0

theorem locIndex_eq {L : Lat F N} {A : GL (Fin N) F} (hA : loc v (Lattices.latOf A) = loc v L.1) :
    locIndex v L = ‖algebraMap F Fv A.val.det‖ := by
  classical
  have h : ∃ A, IsLocModel v L A := exists_isLocModel' v L
  rw [locIndex, dif_pos h]
  exact norm_det_eq_of_loc_eq v (h.choose_spec.2.trans hA.symm)

theorem locIndex_pos (L : Lat F N) : 0 < locIndex v L := by
  have h : ∃ A, IsLocModel v L A := exists_isLocModel' v L
  obtain ⟨A, hA⟩ := h
  rw [locIndex_eq v hA.2]
  exact norm_pos_iff.mpr ((map_ne_zero _).mpr (A.isUnit.map Matrix.detMonoidHom).ne_zero)

/-- $\mathrm{locIndex}_\mathfrak p(L) = 1$ where $L_\mathfrak p = \mathfrak o_\mathfrak p^N$. -/
theorem locIndex_eq_one {L : Lat F N} (h : loc v L.1 = std v) : locIndex v L = 1 := by
  rw [locIndex_eq v (A := 1) (by rw [Lattices.latOf, glImage_one, loc_intVec, h]), Units.val_one, det_one, map_one,
    norm_one]

open Classical in
/-- **The classical local density $\beta_\mathfrak p(L, m)$ of $m$ in the lattice $L_\mathfrak p$** (Siegel 1935; Kitaoka 1993, §5.6
[unverified]): `NF.localDensity` $= \lim_k \#\{x \bmod \mathfrak p^k : T(x) \equiv m\}/N\mathfrak p^{k(N-1)}$ of the Gram form
$T = Q\circ A$ of a local basis $A$ of $L_\mathfrak p$ on which $Q$ is integral; $0$ if there is none ($L$ not integral). The
density for the Haar measure giving $L_\mathfrak p$ volume $1$; independent of the local basis (`intrinsicBeta_eq`,
`intrinsicBeta_eq_of_localBasis`) and of the coordinates of $V$ (`intrinsicBeta_compMat`). -/
@[kb "kitaoka1993" "§5.6 (local density of a lattice, basis-free) [unverified]"]
def intrinsicBeta (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  if h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A) then
    NF.localDensity v (gramZ Q h.choose h.choose_spec.2) m
  else 0

/-- `intrinsicBeta` computed with any local free model. -/
theorem intrinsicBeta_eq (Q : QuadForm F N) (L : Lat F N) {A : GL (Fin N) F} (hA : IsLocModel v L A)
    (hint : Lattices.IsIntegral Q (Lattices.latOf A)) (m : 𝓞 F) :
    intrinsicBeta v Q L m = NF.localDensity v (gramZ Q A hint) m := by
  have h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A) := ⟨A, hA, hint⟩
  rw [intrinsicBeta, dif_pos h]
  exact localDensity_gramZ_eq v Q _ _ (h.choose_spec.1.2.trans hA.2.symm) m

/-- **The coordinate density is the local index times the classical one** (task 2): $\beta^{\mathrm{coord}}_\mathfrak p(L, m) =
\|\det A\|_\mathfrak p\,\beta_\mathfrak p(L_\mathfrak p, m)$. -/
theorem spaceBeta_eq_locIndex_mul (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) :
    spaceBeta v Q L m = locIndex v L * intrinsicBeta v Q L m := by
  classical
  by_cases h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A)
  · rw [spaceBeta, intrinsicBeta, dif_pos h, dif_pos h, locIndex_eq v h.choose_spec.1.2]
  · rw [spaceBeta, intrinsicBeta, dif_neg h, dif_neg h, mul_zero]

/-- **`latBeta` in terms of the classical density**: `latBeta v Q₀ L m = ‖det A‖_𝔭 · β_𝔭(L_𝔭, m)` for any local
model $A$. -/
theorem latBeta_eq_normDet_mul_intrinsicBeta (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) {A : GL (Fin N) F}
    (hA : IsLocModel v L A) (m : 𝓞 F) :
    latBeta v Q₀ L m = ‖algebraMap F Fv A.val.det‖ * intrinsicBeta v (formF Q₀) L m := by
  rw [← spaceBeta_formF, spaceBeta_eq_locIndex_mul, locIndex_eq v hA.2]

/-- **$\beta_\mathfrak p(L_\mathfrak p, m)$ from ANY local basis**: if $P \in \mathrm{GL}_N(F_\mathfrak p)$ with $P\mathfrak o_\mathfrak p^N = L_\mathfrak p$ and
$T$ is the Gram form of $Q$ in the basis $P$ (a form over $\mathfrak o_\mathfrak p$), then $\beta_\mathfrak p(L, m) = \beta(T, m)$, the
density of `DVR.localDensity` (the count of $x \in (\mathfrak o_\mathfrak p/\mathfrak p^k)^N \cong L_\mathfrak p/\mathfrak p^kL_\mathfrak p$ with
$T(x) \equiv m$). -/
theorem intrinsicBeta_eq_of_localBasis {n : ℕ} (Q : QuadForm F (n + 1)) (L : Lat F (n + 1))
    (hLi : Lattices.IsIntegral Q L.1) (P : GL (Fin (n + 1)) Fv) (hP : locAct v P (std v) = loc v L.1)
    (T : QuadForm 𝔬 (n + 1)) (hT : T.map (algebraMap 𝔬 Fv) = (Q.map (algebraMap F Fv)).compMat P.val) (m : 𝓞 F) :
    intrinsicBeta v Q L m = DVR.localDensity T (NF.π v) (NF.ι v m) := by
  obtain ⟨A, hA⟩ := exists_isLocModel v L
  have hint := hA.isIntegral v hLi
  set g := Matrix.GeneralLinearGroup.map (algebraMap F Fv) A
  have hstd : locAct v (g⁻¹ * P) (std v) = std v := by
    have h := hA.2
    rw [Lattices.latOf, loc_glImage, loc_intVec] at h
    rw [locAct_mul, hP, ← h, locAct_inv_locAct]
  obtain ⟨U, hU⟩ := exists_GL_o_of_locAct_std v _ hstd
  have hUv : U.val.map (algebraMap 𝔬 Fv) = (g⁻¹ * P).val := congrArg Units.val hU
  have hform : T = (NF.Qp v (gramZ Q A hint)).compMat U.val := by
    apply NF.map_injective (IsFractionRing.injective 𝔬 Fv)
    rw [← map_compMat, map_Qp_gramZ', compMat_mul, hUv, ← Units.val_mul, mul_inv_cancel_left, hT]
  have hiso : Siegel.IsometricGL (NF.Qp v (gramZ Q A hint)) T := ⟨U, fun x => by rw [hform, eval_compMat]⟩
  rw [intrinsicBeta_eq v Q L hA hint, NF.localDensity_eq_completion]
  unfold DVR.localDensity
  simp_rw [repCount_congr_isometricGL hiso]

/-- **Coordinate independence of $\beta_\mathfrak p(L_\mathfrak p, m)$**: for $g \in \mathrm{GL}_N(F)$, the lattice $g^{-1}L$ for the form
$Q\circ g$ has the same classical local densities (pointwise, no hypotheses). -/
theorem intrinsicBeta_compMat (Q : QuadForm F N) (L : Lat F N) (g : GL (Fin N) F) (m : 𝓞 F) :
    intrinsicBeta v (Q.compMat g.val) (Lat.image g⁻¹ L) m = intrinsicBeta v Q L m := by
  classical
  have hmod : ∀ A, IsLocModel v L A ↔ IsLocModel v (Lat.image g⁻¹ L) (g⁻¹ * A) := fun A => by
    refine ⟨fun h => isLocModel_image v h g, fun h => ?_⟩
    have := isLocModel_image v h g⁻¹
    rwa [inv_inv, mul_inv_cancel_left, lat_image_image_inv'] at this
  have hint : ∀ A, Lattices.IsIntegral Q (Lattices.latOf A) ↔
      Lattices.IsIntegral (Q.compMat g.val) (Lattices.latOf (g⁻¹ * A)) := fun A => by
    rw [latOf_mul]
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
      rw [evalIn_self_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
      exact h y hy
    · have := h ((g⁻¹).val *ᵥ x) (mulVec_mem_glImage hx)
      rwa [evalIn_self_compMat, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
  by_cases h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A)
  · obtain ⟨A, hA, hAi⟩ := h
    have hB := (hmod A).mp hA
    have hBi := (hint A).mp hAi
    rw [intrinsicBeta_eq v _ _ hB hBi, intrinsicBeta_eq v _ _ hA hAi]
    congr 1
    apply NF.map_injective RingOfIntegers.coe_injective
    show formF (gramZ _ _ hBi) = formF (gramZ _ _ hAi)
    rw [formF_gramZ', formF_gramZ', compMat_mul, ← Units.val_mul, mul_inv_cancel_left]
  · have h' : ¬ ∃ B, IsLocModel v (Lat.image g⁻¹ L) B ∧ Lattices.IsIntegral (Q.compMat g.val) (Lattices.latOf B) := by
      rintro ⟨B, hB, hBi⟩
      refine h ⟨g * B, (hmod _).mpr (by rwa [inv_mul_cancel_left]), (hint _).mpr (by rwa [inv_mul_cancel_left])⟩
    rw [intrinsicBeta, intrinsicBeta, dif_neg h, dif_neg h']

end Local

/-! ### The index and the discriminant of $L$ -/

section Global

theorem locIndex_hasFiniteMulSupport (L : Lat F N) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => locIndex v L :=
  (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv h => hv (locIndex_eq_one v h)

/-- **The index of $L$ relative to $\mathcal O_F^N$**: $\mathrm{latIndex}(L) = \prod_\mathfrak p\|\det A_\mathfrak p\|_\mathfrak p = N(\mathfrak a_L)^{-1}$,
$\mathfrak a_L = \prod_\mathfrak p\mathfrak p^{\mathrm{ord}_\mathfrak p\det A_\mathfrak p}$ ($A_\mathfrak p$ a local basis of $L_\mathfrak p$; a finite product,
`locIndex_hasFiniteMulSupport`). For $L \subseteq \mathcal O_F^N$ it is $[\mathcal O_F^N : L]^{-1}$ (cf. O'Meara 1963, §81D, 81:11–81:12, pp. 214–216: invariant factors and the index $(L : K)$). -/
@[kb "omeara1963" "§81D, p. 216 (the index (L:K) = ∏(𝔬:𝔯_i) via invariant factors, 81:11–81:12)"]
def latIndex (L : Lat F N) : ℝ := ∏ᶠ v, locIndex v L

theorem latIndex_eq_prod (L : Lat F N) :
    latIndex L = ∏ v ∈ (locIndex_hasFiniteMulSupport L).toFinset, locIndex v L :=
  finprod_eq_prod_of_mulSupport_subset _ fun _ hv => (locIndex_hasFiniteMulSupport L).mem_toFinset.mpr hv

theorem locIndex_eq_one_of_notMem (L : Lat F N) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ (locIndex_hasFiniteMulSupport L).toFinset) : locIndex v L = 1 := by
  by_contra h; exact hv ((locIndex_hasFiniteMulSupport L).mem_toFinset.mpr h)

/-- For the coordinate lattice, $\mathrm{latIndex}(\mathcal O_F^N) = 1$. -/
theorem latIndex_std : latIndex (stdLat F N) = 1 := by
  unfold latIndex
  rw [finprod_congr fun v => locIndex_eq_one v (L := stdLat F N) (loc_intVec v), finprod_one]

theorem latIndex_pos (L : Lat F N) : 0 < latIndex L := by
  rw [latIndex_eq_prod]; exact Finset.prod_pos fun v _ => locIndex_pos v L

open Classical in
/-- **The local discriminant** $\|\det B_\mathfrak p\|_\mathfrak p$, $B_\mathfrak p = \tfrac12H(Q\circ A)$ the Gram matrix ($T(x) = x^{\mathsf T}B_\mathfrak px$)
of $Q$ in a local basis $A$ of $L_\mathfrak p$; independent of $A$ (`locDisc_eq_of_locBasis`). -/
def locDisc (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N) (L : Lat F N) : ℝ :=
  if h : ∃ A, IsLocModel v L A then
    ‖algebraMap F (v.adicCompletion F) ((Q.compMat h.choose.val).hessian.det / 2 ^ N)‖
  else 0

theorem norm_det_compMat (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N) (A : GL (Fin N) F) :
    ‖algebraMap F (v.adicCompletion F) ((Q.compMat A.val).hessian.det / 2 ^ N)‖ =
      ‖algebraMap F (v.adicCompletion F) A.val.det‖ ^ 2 * ‖algebraMap F (v.adicCompletion F) (Q.hessian.det / 2 ^ N)‖ := by
  rw [hessian_det_compMat', mul_div_assoc, map_mul, norm_mul, map_pow, norm_pow]

theorem locDisc_eq (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N) (L : Lat F N) :
    locDisc v Q L = locIndex v L ^ 2 * ‖algebraMap F (v.adicCompletion F) (Q.hessian.det / 2 ^ N)‖ := by
  classical
  have h := exists_isLocModel' v L
  rw [locDisc, dif_pos h, locIndex_eq v h.choose_spec.2, norm_det_compMat]

/-- `locDisc` from any local basis. -/
theorem locDisc_eq_of_locBasis (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F N) {L : Lat F N} {A : GL (Fin N) F}
    (hA : loc v (Lattices.latOf A) = loc v L.1) :
    locDisc v Q L = ‖algebraMap F (v.adicCompletion F) ((Q.compMat A.val).hessian.det / 2 ^ N)‖ := by
  rw [locDisc_eq, locIndex_eq v hA, norm_det_compMat]

/-- **The absolute norm of the discriminant ideal of $L$** (O'Meara 1963, §82E, p. 228, where it is called the volume $\mathfrak vL$):
$N\mathfrak d(L) = \prod_\mathfrak p\|\det B_\mathfrak p\|_\mathfrak p^{-1}$, $\mathfrak d(L) = \prod_\mathfrak p\mathfrak p^{\mathrm{ord}_\mathfrak p\det B_\mathfrak p}$ with $B_\mathfrak p$ the
Gram matrix ($\tfrac12$Hessian) of $Q$ in a local basis of $L_\mathfrak p$. Basis-free (`locDisc_eq_of_locBasis`, `discNorm_compMat`);
`discNorm_eq` evaluates it by the product formula. -/
@[kb "omeara1963" "§82E, p. 229 (volume 𝔳L); §82B, p. 222 (discriminant of a free lattice)"]
def discNorm (Q : QuadForm F N) (L : Lat F N) : ℝ := ∏ᶠ v, (locDisc v Q L)⁻¹

variable [IsTotallyReal F] in
/-- **$N\mathfrak d(L) = \mathrm{latIndex}(L)^{-2}\prod_\sigma|\sigma\det B_Q|$** (the product formula; $B_Q = \tfrac12H(Q)$,
`detGramF Q σ` $= |\sigma\det B_Q|$). -/
theorem discNorm_eq (Q : QuadForm F N) (hQ : Q.Nondegenerate) (L : Lat F N) :
    discNorm Q L = (latIndex L ^ 2)⁻¹ * ∏ σ : F →ₐ[ℚ] ℂ, detGramF Q σ := by
  set x := Q.hessian.det / 2 ^ N
  have hx : x ≠ 0 := div_ne_zero hQ (pow_ne_zero _ two_ne_zero)
  have h1 := locIndex_hasFiniteMulSupport L
  have h2 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) x‖ :=
    (finite_valuation_ne_one hx).subset fun v hv => by
      by_contra h; exact hv (norm_algebraMap_eq_one (by simpa using h))
  have h1' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => (locIndex v L ^ 2)⁻¹ :=
    h1.subset fun v hv h => hv (by simp only [h]; norm_num)
  have h2' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) x‖⁻¹ :=
    h2.subset fun v hv h => hv (by simp only [h]; norm_num)
  unfold discNorm
  simp_rw [locDisc_eq, mul_inv]
  rw [finprod_mul_distrib h1' h2', finprod_inv_distrib, finprod_inv_distrib, ← finprod_pow h1, finprod_norm_eq x hx,
    inv_inv]
  rfl

/-- `discNorm` does not see a change of coordinates of $V$. -/
theorem discNorm_compMat (Q : QuadForm F N) (L : Lat F N) (g : GL (Fin N) F) :
    discNorm (Q.compMat g.val) (Lat.image g⁻¹ L) = discNorm Q L := by
  unfold discNorm
  refine finprod_congr fun v => ?_
  obtain ⟨A, hA⟩ := exists_isLocModel' v L
  rw [locDisc_eq_of_locBasis v _ (isLocModel_image v hA g).2, locDisc_eq_of_locBasis v _ hA.2, compMat_mul,
    ← Units.val_mul, mul_inv_cancel_left]

/-- $\beta_\infty$ with Gram determinant $d$ is $\beta_\infty$ with Gram determinant $1$ times $d^{-1/2}$. -/
theorem archRepDensity_eq_one_mul (M : ℕ) (a d : ℝ) :
    archRepDensity M a d = archRepDensity M a 1 * d ^ (-(1 / 2 : ℝ)) := by
  unfold archRepDensity; rw [Real.one_rpow, mul_one]

variable [IsTotallyReal F] in
/-- **The volume factor:** $\prod_\sigma\beta_\sigma(Q; a_\sigma)\cdot\mathrm{latIndex}(L) = \prod_\sigma\beta_\sigma(1; a_\sigma)\cdot N\mathfrak d(L)^{-1/2}$. -/
theorem prod_archRepDensity_mul_latIndex (Q : QuadForm F N) (hQ : Q.Nondegenerate) (L : Lat F N)
    (a : (F →ₐ[ℚ] ℂ) → ℝ) (M : ℕ) :
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) (detGramF Q σ)) * latIndex L =
      (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) 1) * discNorm Q L ^ (-(1 / 2 : ℝ)) := by
  have hD : 0 ≤ ∏ σ : F →ₐ[ℚ] ℂ, detGramF Q σ := Finset.prod_nonneg fun σ _ => by unfold detGramF; exact norm_nonneg _
  have e : ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) (detGramF Q σ) =
      (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) 1) * (∏ σ : F →ₐ[ℚ] ℂ, detGramF Q σ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.finsetProd_rpow _ _ (fun σ _ => by unfold detGramF; exact norm_nonneg _), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun σ _ => archRepDensity_eq_one_mul _ _ _
  have hI := latIndex_pos L
  have hc : ((latIndex L ^ 2)⁻¹) ^ (-(1 / 2 : ℝ)) = latIndex L := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv, ← Real.sqrt_eq_rpow, Real.sqrt_sq hI.le]
  rw [e, discNorm_eq Q hQ L, Real.mul_rpow (by positivity) hD, hc]
  ring

/-- A product with the finitely supported factor $\mathrm{locIndex}$ splits off $\mathrm{latIndex}(L)$. -/
theorem tprod_locIndex_mul (L : Lat F N) {f : HeightOneSpectrum (𝓞 F) → ℝ}
    (hf : Multipliable fun v => locIndex v L * f v) : ∏' v, locIndex v L * f v = latIndex L * ∏' v, f v := by
  have hg : Multipliable fun v => (locIndex v L)⁻¹ :=
    multipliable_of_ne_finset_one fun v hv => by rw [locIndex_eq_one_of_notMem L hv, inv_one]
  have hf' : Multipliable f := (hf.mul hg).congr fun v => by
    field_simp [(locIndex_pos v L).ne']
  have hS : ∀ v ∉ (locIndex_hasFiniteMulSupport L).toFinset, locIndex v L = 1 := fun v hv => locIndex_eq_one_of_notMem L hv
  rw [(multipliable_of_ne_finset_one hS).tprod_mul hf', tprod_eq_prod hS, latIndex_eq_prod]

/-- The same for `regProd`. -/
theorem regProd_locIndex_mul (L : Lat F N) (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ) {f : HeightOneSpectrum (𝓞 F) → ℝ}
    (hf : Multipliable fun v => locIndex v L * f v * (1 - χ v / (normP v : ℝ)) ^ e) :
    regProd χ e (fun v => locIndex v L * f v) = latIndex L * regProd χ e f := by
  have hg : Multipliable fun v => (locIndex v L)⁻¹ :=
    multipliable_of_ne_finset_one fun v hv => by rw [locIndex_eq_one_of_notMem L hv, inv_one]
  have hf' : Multipliable fun v => f v * (1 - χ v / (normP v : ℝ)) ^ e := (hf.mul hg).congr fun v => by
    field_simp [(locIndex_pos v L).ne']
  have h := regProd_mul_fin χ e _ (fun v hv => locIndex_eq_one_of_notMem L hv) hf'
  rw [show (fun v => locIndex v L * f v) = fun v => f v * locIndex v L from funext fun v => mul_comm _ _, h,
    ← latIndex_eq_prod]
  ring

end Global

/-! ### The classical Siegel products of $(Q, L)$ -/

section Products

/-- **The classical local side with a given value $P$ of the finite product**:
$|d_F|^{-\frac{N-1}2}\,N\mathfrak d(L)^{-\frac12}\prod_\sigma\beta_\sigma(1; \sigma m)\cdot P$, with $\beta_\sigma(1; a) = \frac{\pi^{N/2}}{\Gamma(N/2)}a^{\frac{N-2}2}$
(`archRepDensity N a 1`, Gram determinant $1$). -/
def siegelProductWithClassical (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) (P : ℝ) : ℝ :=
  |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) * discNorm Q L ^ (-(1 / 2 : ℝ)) *
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity N ‖σ (algebraMap (𝓞 F) F m)‖ 1) * P

/-- **Siegel's product with the classical normalization** ($N \ge 4$; Siegel 1935, Hauptsatz [unverified]):
$$S^{\mathrm{cl}}(L, m) = |d_F|^{-\frac{N-1}2}\,N\mathfrak d(L)^{-\frac12}\prod_{\sigma}\frac{\pi^{N/2}}{\Gamma(N/2)}\sigma(m)^{\frac{N-2}2}
  \prod_\mathfrak p\beta_\mathfrak p(L_\mathfrak p, m),$$
$\beta_\mathfrak p(L_\mathfrak p, m)$ the classical basis-free densities (`intrinsicBeta`), $N\mathfrak d(L)$ the norm of the discriminant ideal
(`discNorm`). -/
@[kb "siegel1935" "Hauptsatz (local side, classical normalization) [unverified]"]
def siegelProductClassical (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  siegelProductWithClassical Q L m (∏' v, intrinsicBeta v Q L m)

/-- **The rank-3 classical Siegel product** (regularized with the character `spaceChar3 Q m`, as `siegelProduct3Space`). -/
@[kb "siegel1935" "Hauptsatz, n = 3 (local side, regularized, classical normalization) [unverified]"]
def siegelProduct3Classical (Q : QuadForm F 3) (L : Lat F 3) (m : 𝓞 F) : ℝ :=
  siegelProductWithClassical Q L m (regProd (spaceChar3 Q m) 1 fun v => intrinsicBeta v Q L m)

/-- **The rank-2 classical Siegel product** (regularized with exponent $-1$ and the character `spaceChar2 Q`). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (local side, regularized, classical normalization) [unverified]"]
def siegelProduct2RegClassical (Q : QuadForm F 2) (L : Lat F 2) (m : 𝓞 F) : ℝ :=
  siegelProductWithClassical Q L m (regProd (spaceChar2 Q) (-1) fun v => intrinsicBeta v Q L m)

/-- **The rank-1 classical Siegel product** (the halved factors of `siegelProductOneSpace`):
$N\mathfrak d(L)^{-\frac12}\prod_\sigma\tfrac12\beta_\sigma(1; \sigma m)\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L_\mathfrak p, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (local side, classical normalization) [unverified]"]
def siegelProductOneClassical (Q : QuadForm F 1) (L : Lat F 1) (m : 𝓞 F) : ℝ :=
  discNorm Q L ^ (-(1 / 2 : ℝ)) * (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
    ∏' v : HeightOneSpectrum (𝓞 F), intrinsicBeta v Q L m / 2

variable [IsTotallyReal F]

theorem siegelProductWithF_latIndex_mul (Q : QuadForm F N) (hQ : Q.Nondegenerate) (L : Lat F N) (m : 𝓞 F) (P : ℝ) :
    siegelProductWithF Q m (latIndex L * P) = siegelProductWithClassical Q L m P := by
  unfold siegelProductWithF siegelProductWithClassical
  have h := prod_archRepDensity_mul_latIndex Q hQ L (fun σ => ‖σ (algebraMap (𝓞 F) F m)‖) N
  linear_combination (|(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) * P) * h

/-- Multipliability of the coordinate densities with a correction factor, from coordinates $(\gamma, Q_0)$. -/
theorem multipliable_spaceBeta_corr {n : ℕ} (Q : QuadForm F (n + 1)) (L : Lat F (n + 1))
    (hLi : Lattices.IsIntegral Q L.1) (γ : GL (Fin (n + 1)) F) (Q₀ : QuadForm (𝓞 F) (n + 1))
    (hγ : formF Q₀ = Q.compMat γ.val) (m : 𝓞 F) {χ χ' : HeightOneSpectrum (𝓞 F) → ℝ} (hχ' : ∀ v, |χ' v| ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, χ v = χ' v) (e : ℤ)
    (hβ : Multipliable fun v => latBeta v Q₀ (Lat.image γ⁻¹ L) m * (1 - χ' v / (normP v : ℝ)) ^ e) :
    Multipliable fun v => spaceBeta v Q L m * (1 - χ v / (normP v : ℝ)) ^ e := by
  have hr : Multipliable fun v => ((1 - χ v / (normP v : ℝ)) / (1 - χ' v / (normP v : ℝ))) ^ e :=
    multipliable_of_ne_finset_one fun v hv => by
      rw [hS v hv, div_self (one_sub_div_pos (hχ' v) v).ne', _root_.one_zpow]
  refine ((hβ.mul (hasProd_norm_det γ).multipliable).mul hr).congr fun v => ?_
  have h0 := zpow_ne_zero e (one_sub_div_pos (hχ' v) v).ne'
  rw [spaceBeta_eq v Q L hLi γ Q₀ hγ, div_zpow]
  field_simp

/-- **$S(Q, L, m) = S^{\mathrm{cl}}(Q, L, m)$, rank $N \ge 4$**: gcf's coordinate Siegel product equals the classical one. -/
theorem siegelProductSpace_eq_classical {N : ℕ} (hN : 4 ≤ N) (Q : QuadForm F N) (hpd : IsTotallyPosDef Q) (L : Lat F N)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductSpace Q L m = siegelProductClassical Q L m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords Q hpd L hLi
  have hβ := multipliable_latBeta (by omega) Q₀ hpd₀ _ hLi' hm
  have hmul : Multipliable fun v => spaceBeta v Q L m := by
    rw [spaceBeta_fun_eq Q L hLi γ Q₀ hγ]; exact hβ.mul (hasProd_norm_det γ).multipliable
  unfold siegelProductSpace siegelProductClassical
  simp_rw [spaceBeta_eq_locIndex_mul] at hmul ⊢
  rw [tprod_locIndex_mul L hmul, siegelProductWithF_latIndex_mul Q hpd.nondegenerate]

/-- The corrected rank-3 coordinate densities converge (unconditionally). -/
theorem multipliable_spaceBeta_chiTern (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => spaceBeta v Q L m * (1 - spaceChar3 Q m v / (normP v : ℝ)) ^ (1 : ℤ) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 2) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hm0 : m ≠ 0 := ne_zero_of_totallyPos hm
  have hβ := multipliable_latBeta_mul_chiTern hQ₀ _ hLi' hm0
  have hχ := Filter.eventually_cofinite.mp (eventually_chiTern_eq Q γ Q₀ hγ hQ₀ hm0)
  exact multipliable_spaceBeta_corr Q L hLi γ Q₀ hγ m (χ := spaceChar3 Q m) (fun v => abs_chiTern_le v Q₀ m)
    hχ.toFinset (fun v hv => by by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm))) 1 hβ

/-- The corrected rank-2 coordinate densities converge (unconditionally). -/
theorem multipliable_spaceBeta_chiP (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => spaceBeta v Q L m * (1 - spaceChar2 Q v / (normP v : ℝ)) ^ (-1 : ℤ) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 1) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  obtain ⟨P, hP⟩ := exists_hasProd_latBeta_mul_chiP Q₀ hpd₀ _ hLi' hm
  have hχ := Filter.eventually_cofinite.mp (eventually_chiP_eq Q γ Q₀ hγ hQ₀)
  exact multipliable_spaceBeta_corr Q L hLi γ Q₀ hγ m (χ := spaceChar2 Q) (fun v => abs_chiP_le Q₀ v)
    hχ.toFinset (fun v hv => by by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm))) (-1) hP.multipliable

/-- `regProd` of the coordinate densities is $\mathrm{latIndex}(L)$ times `regProd` of the classical ones. -/
theorem regProd_spaceBeta_eq (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) (χ : HeightOneSpectrum (𝓞 F) → ℝ) (e : ℤ)
    (hmul : Multipliable fun v => spaceBeta v Q L m * (1 - χ v / (normP v : ℝ)) ^ e) :
    regProd χ e (fun v => spaceBeta v Q L m) = latIndex L * regProd χ e fun v => intrinsicBeta v Q L m := by
  simp_rw [spaceBeta_eq_locIndex_mul] at hmul ⊢
  exact regProd_locIndex_mul L χ e hmul

/-- **$S_3(Q, L, m) = S_3^{\mathrm{cl}}(Q, L, m)$.** -/
theorem siegelProduct3Space_eq_classical (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3Space Q L m = siegelProduct3Classical Q L m := by
  unfold siegelProduct3Space siegelProduct3Classical
  rw [regProd_spaceBeta_eq Q L m _ _ (multipliable_spaceBeta_chiTern Q hpd L hLi hm),
    siegelProductWithF_latIndex_mul Q hpd.nondegenerate]

/-- **$S^{\mathrm{reg}}_2(Q, L, m) = S^{\mathrm{reg,cl}}_2(Q, L, m)$.** -/
theorem siegelProduct2RegSpace_eq_classical (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegSpace Q L m = siegelProduct2RegClassical Q L m := by
  unfold siegelProduct2RegSpace siegelProduct2RegClassical
  rw [regProd_spaceBeta_eq Q L m _ _ (multipliable_spaceBeta_chiP Q hpd L hLi hm),
    siegelProductWithF_latIndex_mul Q hpd.nondegenerate]

/-- **Natural order passes to the classical densities**: if the coordinate densities have the natural-order product
`regProd χ e`, so do the classical ones (they differ by the finitely supported `locIndex`). -/
theorem hasProd_intrinsicBeta_of_spaceBeta (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) (χ : HeightOneSpectrum (𝓞 F) → ℝ)
    (e : ℤ) (hmul : Multipliable fun v => spaceBeta v Q L m * (1 - χ v / (normP v : ℝ)) ^ e)
    (hP : HasProd (fun v => spaceBeta v Q L m) (regProd χ e fun v => spaceBeta v Q L m) (normOrder F)) :
    HasProd (fun v => intrinsicBeta v Q L m) (regProd χ e fun v => intrinsicBeta v Q L m) (normOrder F) := by
  have hg : HasProd (fun v => (locIndex v L)⁻¹) (∏ v ∈ (locIndex_hasFiniteMulSupport L).toFinset, (locIndex v L)⁻¹)
      (normOrder F) :=
    hasProd_prod_of_ne_finset_one fun v hv => by rw [locIndex_eq_one_of_notMem L hv, inv_one]
  have h := hP.mul hg
  rw [regProd_spaceBeta_eq Q L m χ e hmul, Finset.prod_inv_distrib, ← latIndex_eq_prod] at h
  convert h using 1
  · funext v; rw [spaceBeta_eq_locIndex_mul]; field_simp [(locIndex_pos v L).ne']
  · field_simp [(latIndex_pos L).ne']

/-- **$\mathcal S_1(Q, L, m) = \mathcal S_1^{\mathrm{cl}}(Q, L, m)$.** -/
theorem siegelProductOneSpace_eq_classical (Q : QuadForm F 1) (hpd : IsTotallyPosDef Q) (L : Lat F 1)
    (hLi : Lattices.IsIntegral Q L.1) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneSpace Q L m = siegelProductOneClassical Q L m := by
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi'⟩ := exists_coords (n := 0) Q hpd L hLi
  have hβ := multipliable_latBeta_rankOne Q₀ hpd₀ _ hLi' hm
  have hmul : Multipliable fun v => locIndex v L * (intrinsicBeta v Q L m / 2) :=
    (hβ.mul (hasProd_norm_det γ).multipliable).congr fun v => by
      rw [← mul_div_assoc, ← spaceBeta_eq_locIndex_mul, spaceBeta_eq v Q L hLi γ Q₀ hγ]; ring
  have e : (fun v => spaceBeta v Q L m / 2) = fun v => locIndex v L * (intrinsicBeta v Q L m / 2) := by
    funext v; rw [spaceBeta_eq_locIndex_mul]; ring
  have ha := prod_archRepDensity_mul_latIndex Q hpd.nondegenerate L (fun σ => ‖σ (algebraMap (𝓞 F) F m)‖) 1
  unfold siegelProductOneSpace siegelProductOneClassical
  rw [e, tprod_locIndex_mul L hmul, Finset.prod_div_distrib, Finset.prod_div_distrib]
  linear_combination ((∏' v, intrinsicBeta v Q L m / 2) / ∏ σ : F →ₐ[ℚ] ℂ, (2 : ℝ)) * ha

end Products

/-! ### The abstract quadratic space: basis-free densities and discriminant -/

section AbstractSpace

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]

theorem intrinsicBeta_coord_indep (v : HeightOneSpectrum (𝓞 F)) (q : QuadraticForm F V) (L : Submodule (𝓞 F) V)
    [L.IsLattice F] {n n' : ℕ} (e : Basis (Fin n) F V) (e' : Basis (Fin n') F V) (m : 𝓞 F) :
    intrinsicBeta v (coordForm q e) (coordLat e L) m = intrinsicBeta v (coordForm q e') (coordLat e' L) m := by
  obtain rfl := basis_card_eq e e'
  rw [coordForm_basis_change q e e', coordLat_basis_change e e', intrinsicBeta_compMat]

theorem discNorm_coord_indep (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] {n n' : ℕ}
    (e : Basis (Fin n) F V) (e' : Basis (Fin n') F V) :
    discNorm (coordForm q e) (coordLat e L) = discNorm (coordForm q e') (coordLat e' L) := by
  obtain rfl := basis_card_eq e e'
  rw [coordForm_basis_change q e e', coordLat_basis_change e e', discNorm_compMat]

variable [FiniteDimensional F V]

/-- **The classical local density $\beta_\mathfrak p(L_\mathfrak p, m)$ of a lattice $L$ in an abstract quadratic space $(V, q)$**
(Siegel 1935; Kitaoka 1993, §5.6 [unverified]): $\lim_k\#\{x \in L_\mathfrak p/\mathfrak p^kL_\mathfrak p : q(x) \equiv m \bmod \mathfrak p^k\}/N\mathfrak p^{k(N-1)}$,
computed from the Gram form of a local basis of $L_\mathfrak p$ (`intrinsicBeta`) in the coordinates of `Module.finBasis`; equal in
every basis (`intrinsicBetaV_eq_basis`, pointwise, no hypotheses) and for every local basis (`intrinsicBeta_eq_of_localBasis`). -/
@[kb "kitaoka1993" "§5.6 (local density of a lattice in a quadratic space) [unverified]"]
def intrinsicBetaV (v : HeightOneSpectrum (𝓞 F)) (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F]
    (m : 𝓞 F) : ℝ :=
  intrinsicBeta v (coordForm q (finBasis F V)) (coordLat (finBasis F V) L) m

/-- **The norm $N\mathfrak d(L)$ of the discriminant ideal of $L$ in $(V, q)$** (O'Meara 1963, §82E, p. 228, the volume $\mathfrak vL$),
$\mathfrak d(L) = \prod_\mathfrak p\mathfrak p^{\mathrm{ord}_\mathfrak p\det(B_q(e_i, e_j))}$ for local bases $(e_i)$ of $L_\mathfrak p$, $B_q(x, x) = q(x)$;
equal in every basis (`discNormV_eq_basis`). -/
@[kb "omeara1963" "§82E, p. 229 (volume 𝔳L); §82B, p. 222"]
def discNormV (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] : ℝ :=
  discNorm (coordForm q (finBasis F V)) (coordLat (finBasis F V) L)

theorem intrinsicBetaV_eq_basis (v : HeightOneSpectrum (𝓞 F)) (q : QuadraticForm F V) (L : Submodule (𝓞 F) V)
    [L.IsLattice F] {n : ℕ} (e : Basis (Fin n) F V) (m : 𝓞 F) :
    intrinsicBetaV v q L m = intrinsicBeta v (coordForm q e) (coordLat e L) m :=
  intrinsicBeta_coord_indep v q L _ e m

theorem discNormV_eq_basis (q : QuadraticForm F V) (L : Submodule (𝓞 F) V) [L.IsLattice F] {n : ℕ}
    (e : Basis (Fin n) F V) : discNormV q L = discNorm (coordForm q e) (coordLat e L) :=
  discNorm_coord_indep q L _ e

end AbstractSpace

/-! ### The headlines: Siegel's formula with the classical normalization -/

section Headlines

variable [IsTotallyReal F] {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
  [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Siegel's formula with the classical local densities, $\dim V = N \ge 4$** (unconditional; Siegel 1935, Hauptsatz;
Kitaoka 1993, §5.6 (densities) [unverified]): for a totally positive definite quadratic space $(V, q)$ over a totally
real number field $F$, an $\mathcal O_F$-lattice $L$ with $q$ integral on $L$, and $m \in \mathcal O_F$ totally positive,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(m)}{|O(M)|} = \mathrm{Mass}(L)\cdot|d_F|^{-\frac{N-1}2}\,N\mathfrak d(L)^{-\frac12}
  \prod_{\sigma:F\to\mathbb R}\frac{\pi^{N/2}}{\Gamma(N/2)}\sigma(m)^{\frac{N-2}2}\prod_\mathfrak p\beta_\mathfrak p(L_\mathfrak p, m),$$
every term basis-free: the intrinsic genus (gi), $N\mathfrak d(L)$ = `discNormV q L` (discriminant ideal, Gram matrix
$B_q(x, x) = q(x)$), $\beta_\mathfrak p(L_\mathfrak p, m)$ = `intrinsicBetaV` (Haar measure with $\mathrm{vol}(L_\mathfrak p) = 1$), real densities
with Gram determinant $1$ (`archRepDensity N a 1`). Proved equal to `siegelFormula_quadraticSpace_intrinsic`. -/
@[kb "siegel1935" "Hauptsatz, classical normalization (discriminant, basis-free local densities) [unverified for F]"]
theorem siegelFormula_quadraticSpace_classical (hN : 4 ≤ finrank F V) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
      (|(discr F : ℝ)| ^ (-((finrank F V : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity (finrank F V) ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        ∏' v, intrinsicBetaV v q L m) := by
  rw [siegelFormula_quadraticSpace_intrinsic hN hq hLi hm]
  congr 1
  exact siegelProductSpace_eq_classical hN _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm

/-- **Ternary, classical normalization** (unconditional; regularized with the character $\chi_m$ = `spaceChar3` of
$F(\sqrt{-2m\det H_q})/F$, in any basis — here `finBasisOfFinrankEq`):
$\mathrm{repMass} = \mathrm{Mass}\cdot|d_F|^{-1}N\mathfrak d(L)^{-1/2}\prod_\sigma\beta_\sigma(1; \sigma m)\cdot\mathrm{regProd}_{\chi_m}(1, \beta_\mathfrak p(L_\mathfrak p, m))$. -/
@[kb "siegel1935" "Hauptsatz, n = 3, classical normalization [unverified for F]"]
theorem siegelFormula3_quadraticSpace_classical (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
      (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar3 (coordForm q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v q L m) := by
  rw [siegelFormula3_quadraticSpace_intrinsic h hq hLi hm, siegelProduct3V,
    siegelProduct3Space_eq_classical _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm,
    siegelProduct3Classical, siegelProductWithClassical, discNormV_eq_basis q L (finBasisOfFinrankEq F V h)]
  simp only [intrinsicBetaV_eq_basis _ q L (finBasisOfFinrankEq F V h), Nat.cast_ofNat]

/-- **Binary, classical normalization** (unconditional; $\varepsilon = \tfrac12$, regularized with $\chi_q$ = `spaceChar2`):
$\mathrm{repMass} = \tfrac12\mathrm{Mass}\cdot|d_F|^{-1/2}N\mathfrak d(L)^{-1/2}\prod_\sigma\beta_\sigma(1; \sigma m)\cdot
\mathrm{regProd}_{\chi_q}(-1, \beta_\mathfrak p(L_\mathfrak p, m))$. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (ε = 1/2), classical normalization [unverified for F]"]
theorem siegelFormula2_quadraticSpace_classical (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L *
      (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
        (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
        regProd (spaceChar2 (coordForm q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v q L m) := by
  rw [siegelFormula2_quadraticSpace_intrinsic h hq hLi hm, siegelProduct2RegV,
    siegelProduct2RegSpace_eq_classical _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm,
    siegelProduct2RegClassical, siegelProductWithClassical, discNormV_eq_basis q L (finBasisOfFinrankEq F V h)]
  simp only [intrinsicBetaV_eq_basis _ q L (finBasisOfFinrankEq F V h), Nat.cast_ofNat]

/-- **Unary, classical normalization** (unconditional; $\varepsilon = \tfrac12$):
$\mathrm{repMass} = \mathrm{Mass}\cdot 2\,N\mathfrak d(L)^{-1/2}\prod_\sigma\tfrac12\beta_\sigma(1; \sigma m)\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L_\mathfrak p, m)$. -/
@[kb "siegel1935" "Hauptsatz, n = 1 (ε = 1/2), classical normalization [unverified for F]"]
theorem siegelFormula1_quadraticSpace_classical (h : finrank F V = 1) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
      (2 * (discNormV q L ^ (-(1 / 2 : ℝ)) * (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ 1 / 2) *
        ∏' v, intrinsicBetaV v q L m / 2)) := by
  rw [siegelFormula1_quadraticSpace_intrinsic h hq hLi hm, siegelProductOneV,
    siegelProductOneSpace_eq_classical _ (isTotallyPosDef_coordForm hq _) _ (isIntegral_coordLat hLi _) hm,
    siegelProductOneClassical, discNormV_eq_basis q L (finBasisOfFinrankEq F V h)]
  simp only [intrinsicBetaV_eq_basis _ q L (finBasisOfFinrankEq F V h)]

/-- **Ternary, natural order, classical normalization**: in any basis $e$ of $V$, given `NaturalOrderEulerOne` of $\chi_m$
(convention input), the natural-order Euler product of the classical densities $\beta_\mathfrak p(L_\mathfrak p, m)$ converges to the
regularized value, and Siegel's formula holds in the classical form. -/
@[kb "hanke2004" "(5.3), p. 368 (n = 3, natural order), classical normalization"]
theorem siegelFormula3_quadraticSpace_natural_classical (h : finrank F V = 3) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 3) F V) (hN : NaturalOrderEulerOne (spaceChar3 (coordForm q e) m)) :
    HasProd (fun v => intrinsicBetaV v q L m)
        (regProd (spaceChar3 (coordForm q e) m) 1 fun v => intrinsicBetaV v q L m) (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = massGenV q L *
        (|(discr F : ℝ)| ^ (-((3 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 3 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
          regProd (spaceChar3 (coordForm q (finBasisOfFinrankEq F V h)) m) 1 fun v => intrinsicBetaV v q L m) := by
  refine ⟨?_, siegelFormula3_quadraticSpace_classical h hq hLi hm⟩
  have hP := (siegelFormula3_quadraticSpace_natural_intrinsic h hq hLi hm e hN).1
  have hmul := multipliable_spaceBeta_chiTern _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) hm
  have := hasProd_intrinsicBeta_of_spaceBeta _ _ m _ 1 hmul hP
  simpa only [intrinsicBetaV_eq_basis _ q L e] using this

/-- **Binary, natural order, classical normalization**: in any basis $e$ of $V$, given `NaturalOrderEulerOne` of $\chi_q$, the
natural-order Euler product of the classical densities converges to the regularized value, and Siegel's formula holds in the
classical form. -/
@[kb "siegel1935" "Hauptsatz, n = 2 (natural order), classical normalization [unverified]"]
theorem siegelFormula2_quadraticSpace_natural_classical (h : finrank F V = 2) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m))
    (e : Basis (Fin 2) F V) (hN : NaturalOrderEulerOne (spaceChar2 (coordForm q e))) :
    HasProd (fun v => intrinsicBetaV v q L m)
        (regProd (spaceChar2 (coordForm q e)) (-1) fun v => intrinsicBetaV v q L m) (normOrder F) ∧
      repMassGenV q L (algebraMap (𝓞 F) F m) = (1 / 2 : ℝ) * massGenV q L *
        (|(discr F : ℝ)| ^ (-((2 : ℝ) - 1) / 2) * discNormV q L ^ (-(1 / 2 : ℝ)) *
          (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 2 ‖σ (algebraMap (𝓞 F) F m)‖ 1) *
          regProd (spaceChar2 (coordForm q (finBasisOfFinrankEq F V h))) (-1) fun v => intrinsicBetaV v q L m) := by
  refine ⟨?_, siegelFormula2_quadraticSpace_classical h hq hLi hm⟩
  have hP := (siegelFormula2_quadraticSpace_natural_intrinsic h hq hLi hm e hN).1
  have hmul := multipliable_spaceBeta_chiP _ (isTotallyPosDef_coordForm hq e) _ (isIntegral_coordLat hLi e) hm
  have := hasProd_intrinsicBeta_of_spaceBeta _ _ m _ (-1) hmul hP
  simpa only [intrinsicBetaV_eq_basis _ q L e] using this

end Headlines

end QuadFormsKB.Tamagawa.SiegelSpace

