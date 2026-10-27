/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelLatNatural
import QuadFormsKB.Siegel.NFDyadicGood

/-!
# The local side of Siegel's formula for a quadratic space over $F$, without coordinates over $\mathcal O_F$

**Layer:** $F$ a totally real number field (any class number); $V = F^N$ with an **arbitrary** quadratic form $Q$ over $F$
(`QuadForm F N`, coefficients in $F$, not necessarily over $\mathcal O_F$), totally positive definite; $L$ an arbitrary
$\mathcal O_F$-lattice on $V$ (`Lat F N`, any Steinitz class) with $Q$ integral on $L$.

The genus objects `mass Q L`, `repMass Q L m` (Lattices/, Tamagawa/RepMass) are already defined for forms over $F$ and lattices on
$F^N$. This file defines the local side with every term attached to $(Q, L)$, with no choice of an $\mathcal O_F$-integral
coordinate system:

* `spaceBeta v Q L m`: the local density $\beta_\mathfrak p(L, m)$ of $m$ in $L_\mathfrak p$ (`latBeta` with the form over $F$;
  `spaceBeta_formF`), for the Haar measure of $F_\mathfrak p^N$ with $\mathrm{vol}(\mathfrak o_\mathfrak p^N) = 1$.
* `detGramF Q σ` $= |\sigma(\det(H_Q/2))|$: the Gram determinant of $Q$ at the real place $\sigma$ (G's `detGram` for forms over $F$).
* `sqChar v d`: the quadratic symbol of $d \in F^\times$ at $\mathfrak p$ ($\pm1$ according as $d$ is a square in $F_\mathfrak p$, for
  $\mathfrak p \nmid 2$ with $d$ a $\mathfrak p$-unit; $0$ otherwise), i.e. the character of $F(\sqrt d)/F$ at the unramified odd primes;
  `spaceChar2 Q` ($d = -\det H_Q$) and `spaceChar3 Q m` ($d = -2m\det H_Q$) are Siegel's characters $\chi_Q$, $\chi_m$.

The transport lemmas (`spaceBeta_eq`, `detGram_eq_detGramF`, `prod_archRepDensity_eq`) compare these with G's terms for any
coordinates $Q\circ\gamma = Q_0$ over $\mathcal O_F$ (`exists_coords_of_isIntegral`); the product formula cancels the factors
$|\det\gamma|$.

-/

open NumberField IsDedekindDomain Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open Matrix
open QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm QuadFormsKB.HilbertModular QuadFormsKB.NFEuler
open QuadFormsKB.RegProd QuadFormsKB.Tamagawa.SiegelLat LatChange

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

/-! ### The intrinsic terms -/

section Defs

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

open Classical in
/-- **$\beta_\mathfrak p(L, m)$ for a form $Q$ over $F$** (Kitaoka 1993, §5.6 [unverified]): $\|\det A\|_\mathfrak p\,\beta_\mathfrak p(Q\circ A, m)$
for a local free model $A$ of $L$ at $\mathfrak p$ (`IsLocModel`: $A\mathcal O_F^N \subseteq L$, $(A\mathcal O_F^N)_\mathfrak p = L_\mathfrak p$) on which
$Q$ is integral; $0$ if there is none. The local density of $m$ in $L_\mathfrak p$ for the Haar measure of $F_\mathfrak p^N$ with
$\mathrm{vol}(\mathfrak o_\mathfrak p^N) = 1$. For $Q = Q_0$ over $\mathcal O_F$ it is `latBeta` (`spaceBeta_formF`). -/
@[kb "kitaoka1993" "§5.6 (local densities of lattices, form over F) [unverified]"]
def spaceBeta (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  if h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A) then
    ‖algebraMap F Fv h.choose.val.det‖ * NF.localDensity v (gramZ Q h.choose h.choose_spec.2) m
  else 0

theorem spaceBeta_formF (Q₀ : QuadForm (𝓞 F) N) (L : Lat F N) (m : 𝓞 F) :
    spaceBeta v (formF Q₀) L m = latBeta v Q₀ L m := rfl

/-- **The quadratic symbol of $d \in F$ at $\mathfrak p$**: for $\mathfrak p \nmid 2$ and $\mathrm{ord}_\mathfrak p d = 0$, $1$ if $d$ is a square
in $F_\mathfrak p$ and $-1$ otherwise; $0$ at $\mathfrak p \mid 2$ and where $d$ is not a $\mathfrak p$-unit. At those primes it is the
Frobenius sign of $F(\sqrt d)/F$ (Neukirch 1999, Ch. I §8 [unverified]); it depends only on the square class of $d$
(`sqChar_mul_sq`). -/
@[kb "neukirch1999" "Ch. I §8 (decomposition of primes in F(√d)) [unverified]"]
def sqChar (d : F) : ℝ :=
  open Classical in
  if (2 : 𝓞 F) ∈ v.asIdeal ∨ v.valuation F d ≠ 1 then 0
  else if IsSquare (algebraMap F Fv d) then 1 else -1

theorem abs_sqChar_le (d : F) : |sqChar v d| ≤ 1 := by
  unfold sqChar; split_ifs <;> simp

end Defs

/-- **The Gram determinant of a form over $F$ at a real place**: $|\sigma(\det H_Q/2^N)| = |\sigma(\det(\tfrac12 H_Q))|$
(G's `detGram`, for forms over $F$: `detGramF_formF`). -/
@[kb "siegel1935" "Hauptsatz (archimedean factor: det of the Gram matrix at σ) [unverified]"]
def detGramF (Q : QuadForm F N) (σ : F →ₐ[ℚ] ℂ) : ℝ := ‖σ (Q.hessian.det / 2 ^ N)‖

/-- **Siegel's character $\chi_Q$ of a binary form over $F$** ($F(\sqrt{-\det H_Q})/F$; rank $2$). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (the character χ of F(√-det)) [unverified]"]
def spaceChar2 (Q : QuadForm F 2) (v : HeightOneSpectrum (𝓞 F)) : ℝ := sqChar v (-Q.hessian.det)

/-- **Siegel's character $\chi_m$ of a ternary form over $F$** ($F(\sqrt{-2m\det H_Q})/F$; rank $3$, Hanke 2004, p. 357). -/
@[kb "hanke2004" "Φ₃(𝔭) = χ(-2 det H · m), p. 357"]
def spaceChar3 (Q : QuadForm F 3) (m : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  sqChar v (-(2 * Q.hessian.det * algebraMap (𝓞 F) F m))

theorem detGramF_aux (Q₀ : QuadForm (𝓞 F) N) :
    algebraMap (𝓞 F) F Q₀.hessian.det = (formF Q₀).hessian.det := by
  rw [show (formF Q₀).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) from hessian_map _ _,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem detGramF_formF (Q₀ : QuadForm (𝓞 F) N) (σ : F →ₐ[ℚ] ℂ) : detGramF (formF Q₀) σ = detGram Q₀ σ := by
  unfold detGramF detGram
  rw [show (formF Q₀).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) from hessian_map _ _,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]

/-! ### Transport along coordinates -/

section Transport

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- The Gram form of $A\mathcal O_F^N$ over $F$ is $Q\circ A$ (any form $Q$ over $F$). -/
theorem formF_gramZ' (Q : QuadForm F N) (A : GL (Fin N) F) (h : Lattices.IsIntegral Q (Lattices.latOf A)) :
    formF (gramZ Q A h) = Q.compMat A.val :=
  QuadForm.ext_eval fun y => by
    show ((gramZ Q A h).map (algebraMap (𝓞 F) F)).eval y = _
    rw [gramZ_map, eval_gramFormF_col, eval_compMat]

theorem latOf_mul (γ A : GL (Fin N) F) : Lattices.latOf (γ * A) = glImage γ (Lattices.latOf A) := by
  rw [Lattices.latOf, Lattices.latOf, glImage_mul]

/-- **Local models move with the coordinates:** if $A$ is a local model of $L$ at $\mathfrak p$, then $\gamma^{-1}A$ is one of $\gamma^{-1}L$. -/
theorem isLocModel_image {L : Lat F N} {A : GL (Fin N) F} (h : IsLocModel v L A) (γ : GL (Fin N) F) :
    IsLocModel v (Lat.image γ⁻¹ L) (γ⁻¹ * A) := by
  refine ⟨?_, ?_⟩
  · rw [latOf_mul]
    exact Submodule.map_mono h.1
  · show loc v (Lattices.latOf (γ⁻¹ * A)) = loc v (glImage γ⁻¹ L.1)
    rw [latOf_mul, loc_glImage, loc_glImage, h.2]

/-- **$\beta_\mathfrak p$ under a change of coordinates:** if $Q\circ\gamma = Q_0$ over $\mathcal O_F$ and $Q$ is integral on $L$, then
$\beta_\mathfrak p(Q; L, m) = \|\det\gamma\|_\mathfrak p\,\beta_\mathfrak p(Q_0; \gamma^{-1}L, m)$. -/
theorem spaceBeta_eq {n : ℕ} (Q : QuadForm F (n + 1)) (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral Q L.1)
    (γ : GL (Fin (n + 1)) F) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hγ : formF Q₀ = Q.compMat γ.val) (m : 𝓞 F) :
    spaceBeta v Q L m = ‖algebraMap F Fv γ.val.det‖ * latBeta v Q₀ (Lat.image γ⁻¹ L) m := by
  classical
  obtain ⟨A₀, hA₀⟩ := exists_isLocModel v L
  have h : ∃ A, IsLocModel v L A ∧ Lattices.IsIntegral Q (Lattices.latOf A) := ⟨A₀, hA₀, hA₀.isIntegral v hLi⟩
  set A := h.choose
  have hA : IsLocModel v L A := h.choose_spec.1
  have hAi : Lattices.IsIntegral Q (Lattices.latOf A) := h.choose_spec.2
  have hLi' : Lattices.IsIntegral (formF Q₀) (Lat.image γ⁻¹ L).1 := by rw [hγ]; exact isIntegral_compMat Q γ hLi
  have hB := isLocModel_image v hA γ
  have hBi := hB.isIntegral v hLi'
  rw [spaceBeta, dif_pos h, latBeta_eq v Q₀ _ hB hBi m]
  have hg : gramZ (formF Q₀) (γ⁻¹ * A) hBi = gramZ Q A hAi := by
    apply NF.map_injective RingOfIntegers.coe_injective
    show formF (gramZ (formF Q₀) (γ⁻¹ * A) hBi) = formF (gramZ Q A hAi)
    rw [formF_gramZ', formF_gramZ', hγ, compMat_mul, ← Units.val_mul, mul_inv_cancel_left]
  rw [hg, Units.val_mul, det_mul, map_mul, norm_mul, ← mul_assoc, ← mul_assoc, ← norm_mul, ← map_mul,
    ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, map_one, norm_one, one_mul]

/-- $\det H_{Q\circ\gamma} = (\det\gamma)^2\det H_Q$. -/
theorem hessian_det_compMat' (Q : QuadForm F N) (G : Matrix (Fin N) (Fin N) F) :
    (Q.compMat G).hessian.det = G.det ^ 2 * Q.hessian.det := by
  rw [hessian_compMat, det_mul, det_mul, det_transpose]; ring

/-- **The archimedean Gram determinants under a change of coordinates:** $\det_\sigma(Q_0) = |\sigma\det\gamma|^2\det_\sigma(Q)$. -/
theorem detGram_eq_detGramF (Q : QuadForm F N) (γ : GL (Fin N) F) (Q₀ : QuadForm (𝓞 F) N)
    (hγ : formF Q₀ = Q.compMat γ.val) (σ : F →ₐ[ℚ] ℂ) :
    detGram Q₀ σ = ‖σ γ.val.det‖ ^ 2 * detGramF Q σ := by
  rw [← detGramF_formF, hγ]
  unfold detGramF
  rw [hessian_det_compMat', mul_div_assoc, map_mul, norm_mul, map_pow, norm_pow]

/-- $\beta_\sigma$ scales as $\det^{-1/2}$: `archRepDensity N a (c² d) = archRepDensity N a d / c` for $c > 0$, $d \ge 0$. -/
theorem archRepDensity_sq_mul (N : ℕ) (a : ℝ) {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) :
    archRepDensity N a (c ^ 2 * d) = archRepDensity N a d * c⁻¹ := by
  unfold archRepDensity
  rw [Real.mul_rpow (by positivity) hd]
  have : (c ^ 2) ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le]
  rw [this]; ring

/-- **The archimedean factor under a change of coordinates:**
$\prod_\sigma\beta_\sigma(Q_0; m) = \prod_\sigma\beta_\sigma(Q; m)\cdot\prod_\sigma|\sigma\det\gamma|^{-1}$. -/
theorem prod_archRepDensity_eq (Q : QuadForm F N) (γ : GL (Fin N) F) (Q₀ : QuadForm (𝓞 F) N)
    (hγ : formF Q₀ = Q.compMat γ.val) (a : (F →ₐ[ℚ] ℂ) → ℝ) (M : ℕ) :
    ∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) (detGram Q₀ σ) =
      (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity M (a σ) (detGramF Q σ)) * (∏ σ : F →ₐ[ℚ] ℂ, ‖σ γ.val.det‖)⁻¹ := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  have hdet : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
  have hc : 0 < ‖σ γ.val.det‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hdet)
  rw [detGram_eq_detGramF Q γ Q₀ hγ, archRepDensity_sq_mul M _ hc (by unfold detGramF; exact norm_nonneg _)]

variable [IsTotallyReal F] in
/-- The factors $\|\det\gamma\|_\mathfrak p$ have finite support and product $\prod_\sigma|\sigma\det\gamma|^{-1}$ (the product formula). -/
theorem hasProd_norm_det (γ : GL (Fin N) F) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) γ.val.det‖)
      (∏ σ : F →ₐ[ℚ] ℂ, ‖σ γ.val.det‖)⁻¹ := by
  have hdet : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
  have hfin : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) γ.val.det‖ := by
    refine (finite_valuation_ne_one hdet).subset fun v hv => ?_
    by_contra h
    exact hv (norm_algebraMap_eq_one (by simpa using h))
  have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hfin).hasProd
  rwa [tprod_eq_finprod hfin, finprod_norm_eq _ hdet] at this

theorem norm_det_ne_zero (γ : GL (Fin N) F) (v : HeightOneSpectrum (𝓞 F)) :
    ‖algebraMap F (v.adicCompletion F) γ.val.det‖ ≠ 0 :=
  norm_ne_zero_iff.mpr ((map_ne_zero _).mpr (γ.isUnit.map Matrix.detMonoidHom).ne_zero)

end Transport

/-! ### The characters -/

section Char

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **`sqChar` is the residue symbol** at $\mathfrak p \nmid 2$ for a $\mathfrak p$-unit $x \in \mathcal O_F$ (Hensel). -/
theorem sqChar_algebraMap (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {x : 𝓞 F} (hx : x ∉ v.asIdeal)
    (hval : v.valuation F (algebraMap (𝓞 F) F x) = 1) :
    sqChar v (algebraMap (𝓞 F) F x) = (Siegel.charNF v x : ℝ) := by
  classical
  rw [← Siegel.quadSymbolNF_eq_charNF v h2 x]
  unfold sqChar Siegel.quadSymbolNF
  rw [if_neg (by simp [h2, hval]), if_neg hx]
  have e : algebraMap (v.adicCompletionIntegers F) Fv (NF.ι v x) = algebraMap F Fv (algebraMap (𝓞 F) F x) := by
    show ((NF.ι v x : v.adicCompletionIntegers F) : Fv) = _
    rw [← IsScalarTower.algebraMap_apply]; rfl
  rw [e]
  split_ifs <;> simp

/-- **`sqChar` sees only the square class** away from the primes of $u$: $\chi(u^2d) = \chi(d)$ if $\mathrm{ord}_\mathfrak p u = 0$. -/
theorem sqChar_mul_sq {u : F} (hu : u ≠ 0) (hval : v.valuation F u = 1) (d : F) :
    sqChar v (u ^ 2 * d) = sqChar v d := by
  classical
  unfold sqChar
  have hv : v.valuation F (u ^ 2 * d) = v.valuation F d := by rw [map_mul, map_pow, hval, one_pow, one_mul]
  have hsq : IsSquare (algebraMap F Fv (u ^ 2 * d)) ↔ IsSquare (algebraMap F Fv d) := by
    have hu' : algebraMap F Fv u ≠ 0 := (map_ne_zero _).mpr hu
    rw [map_mul, map_pow]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r / algebraMap F Fv u, ?_⟩
      field_simp
      linear_combination hr
    · rintro ⟨r, hr⟩
      exact ⟨algebraMap F Fv u * r, by rw [hr]; ring⟩
  simp only [hv, hsq]

variable [IsTotallyReal F]

/-- **The binary character of $Q$ is that of any $\mathcal O_F$-model**, off a finite set: if $Q\circ\gamma = Q_0$, then
`chiP v Q₀ = spaceChar2 Q v` for all but finitely many $\mathfrak p$. -/
theorem eventually_chiP_eq (Q : QuadForm F 2) (γ : GL (Fin 2) F) (Q₀ : QuadForm (𝓞 F) 2)
    (hγ : formF Q₀ = Q.compMat γ.val) (hQ₀ : Q₀.Nondegenerate) :
    ∀ᶠ v in cofinite, chiP v Q₀ = spaceChar2 Q v := by
  have hdet : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
  have hneg : -Q₀.hessian.det ≠ 0 := neg_ne_zero.mpr hQ₀
  have hnegF : algebraMap (𝓞 F) F (-Q₀.hessian.det) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hneg
  filter_upwards [(Siegel.finite_mem_asIdeal (two_ne_zero (α := 𝓞 F))).eventually_cofinite_notMem,
    (Siegel.finite_mem_asIdeal hQ₀).eventually_cofinite_notMem,
    (finite_valuation_ne_one hnegF).eventually_cofinite_notMem,
    (finite_valuation_ne_one hdet).eventually_cofinite_notMem] with v h2 hd hval hγv
  simp only [not_not] at h2 hd hval hγv
  rw [chiP_binary_eq_charNF v Q₀ h2 hd, ← sqChar_algebraMap v h2 (fun h => hd (neg_mem_iff.mp h)) hval]
  have e : algebraMap (𝓞 F) F (-Q₀.hessian.det) = γ.val.det ^ 2 * -Q.hessian.det := by
    rw [map_neg, detGramF_aux Q₀, hγ, hessian_det_compMat']; ring
  rw [e, sqChar_mul_sq v hdet hγv]
  rfl

/-- **The ternary character of $(Q, m)$ is that of any $\mathcal O_F$-model**, off a finite set. -/
theorem eventually_chiTern_eq (Q : QuadForm F 3) (γ : GL (Fin 3) F) (Q₀ : QuadForm (𝓞 F) 3)
    (hγ : formF Q₀ = Q.compMat γ.val) (hQ₀ : Q₀.Nondegenerate) {m : 𝓞 F} (hm : m ≠ 0) :
    ∀ᶠ v in cofinite, chiTern Q₀ m v = spaceChar3 Q m v := by
  have hdet : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
  set x : 𝓞 F := (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m
  have hx : x ≠ 0 := by
    simp only [x]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (mul_ne_zero two_ne_zero hQ₀)) hm
  have hxF : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hx
  filter_upwards [(Siegel.finite_mem_asIdeal (two_ne_zero (α := 𝓞 F))).eventually_cofinite_notMem,
    (Siegel.finite_mem_asIdeal hQ₀).eventually_cofinite_notMem,
    (Siegel.finite_mem_asIdeal hx).eventually_cofinite_notMem,
    (finite_valuation_ne_one hxF).eventually_cofinite_notMem,
    (finite_valuation_ne_one hdet).eventually_cofinite_notMem] with v h2 hd hxv hval hγv
  simp only [not_not] at h2 hd hxv hval hγv
  have hG : Siegel.IsGoodPrimeNF Q₀ v := ⟨h2, hd⟩
  show Siegel.psiNF Q₀ m v = _
  unfold Siegel.psiNF
  rw [if_pos hG, ← sqChar_algebraMap v h2 hxv hval]
  have e : algebraMap (𝓞 F) F x = γ.val.det ^ 2 * -(2 * Q.hessian.det * algebraMap (𝓞 F) F m) := by
    simp only [x, map_mul, map_pow, map_neg, map_one, map_ofNat]
    rw [detGramF_aux Q₀, hγ, hessian_det_compMat']; norm_num; ring
  rw [e, sqChar_mul_sq v hdet hγv]
  rfl

end Char

/-! ### Convergence of the lattice products (ranks $\ge 4$ and $1$) -/

section Conv

variable [IsTotallyReal F]

/-- **$\prod_\mathfrak p\beta_\mathfrak p(L, m)$ converges unconditionally in rank $N \ge 4$** for every integral lattice $L$ and totally
positive $m$: if $m$ is represented over $F$, the factors are $W_\mathfrak p\,\alpha_\mathfrak p\,r_\mathfrak p/(\alpha'_\mathfrak p E_\mathfrak p)$
(`latOrbitalIdentity`, the computation of `two_mul_tamagawaKLat_mul_repMass_frame`); otherwise one factor vanishes. -/
theorem multipliable_latBeta {n : ℕ} (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hpd : IsTotallyPosDef (formF Q₀))
    (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => latBeta v Q₀ L m := by
  classical
  set ρ := algebraMap (𝓞 F) F m with hmρ
  have hρ : ρ ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  by_cases hrep : ∃ ξ, (formF Q₀).eval ξ = ρ
  swap
  · obtain ⟨v, hv⟩ := exists_latBeta_eq_zero_of_not_rep Q₀ hpd L hLi hm hrep
    exact (hasProd_zero_of_exists_eq_zero ⟨v, hv⟩).multipliable
  obtain ⟨ξ, hξ⟩ := hrep
  obtain ⟨fr⟩ := exists_adaptedFrame (formF Q₀) hξ hρ
  have hQF : (formF Q₀).Nondegenerate := hpd.nondegenerate
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_map hQF
  have hQ'nd : fr.Q'.Nondegenerate := fr.nondegenerate hQF hρ
  set QF' := fr.Q'.map (algebraMap (𝓞 F) F)
  set W0 : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    locTypeSumG v ρ QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => locRatio v Q₀ L
  set α : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀
  set α' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v fr.Q' fr.Q'
  set E : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) / ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => latBeta v Q₀ L m
  have hEpos : ∀ v, 0 < E v := fun v => by
    have h1 : algebraMap F (v.adicCompletion F) fr.g.val.det ≠ 0 :=
      (map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    have h2 : algebraMap F (v.adicCompletion F) (2 * ρ) ≠ 0 := (map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ)
    exact div_pos (pow_pos (norm_pos_iff.mpr h1) _) (pow_pos (norm_pos_iff.mpr h2) _)
  have hαpos : ∀ v, 0 < α v := fun v => siegelDensity_pos v Q₀ hQ₀
  have hα'pos : ∀ v, 0 < α' v := fun v => siegelDensity_pos v fr.Q' hQ'nd
  have hrpos : ∀ v, 0 < r v := fun v => locRatio_pos v hQ₀ L hLi
  have hW : ∀ v, W0 v = α' v * E v * β v / (α v * r v) := by
    intro v
    have hj := latOrbitalIdentity v Q₀ hQ₀ (by omega) L hLi hmρ.symm hρ fr
    rw [show (2 : v.adicCompletion F) * algebraMap F (v.adicCompletion F) ρ =
      algebraMap F (v.adicCompletion F) (2 * ρ) by rw [map_mul, map_ofNat]] at hj
    have hdet : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero)) _
    have h2ρ : 0 < ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n :=
      pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (mul_ne_zero two_ne_zero hρ))) _
    have hα := hαpos v
    have hr := hrpos v
    simp only [W0, E, α, α', β, r] at hj ⊢
    generalize ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n + 1) = D at hj hdet ⊢
    generalize ‖algebraMap F (v.adicCompletion F) (2 * ρ)‖ ^ n = B2 at hj h2ρ ⊢
    rw [eq_div_iff (mul_pos hα hr).ne']
    field_simp at hj ⊢
    linear_combination hj
  have hglat : (glImage fr.g⁻¹ L.1).IsLattice F := glImage_isLattice fr.g⁻¹ L.2
  have hfin₀ : {v : HeightOneSpectrum (𝓞 F) | loc v (glImage fr.g⁻¹ L.1) ≠ std v ∨ v.valuation F ρ ≠ 1 ∨
      v.valuation F 2 ≠ 1}.Finite :=
    ((Filter.eventually_cofinite.mp (loc_eventually_std hglat)).union
      ((finite_valuation_ne_one hρ).union (finite_valuation_ne_one (two_ne_zero (α := F))))).subset fun v hv => by
        simpa [or_assoc] using hv
  have hW0fin : Function.HasFiniteMulSupport W0 := by
    refine hfin₀.subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show locTypeSumG v ρ QF' (loc v (glImage fr.g⁻¹ L.1)) (algebraMap F (v.adicCompletion F) 1) = 1
    rw [h.1, map_one]
    exact locTypeSumG_std_one_of_units v fr.Q' hQ'nd h.2.1 h.2.2
  have hrfin : Function.HasFiniteMulSupport r := by
    refine (Filter.eventually_cofinite.mp (loc_eventually_std L.2)).subset fun v hv => ?_
    by_contra h
    exact hv (locRatio_eq_one v Q₀ L (by simpa using h))
  have hEfin : Function.HasFiniteMulSupport E := by
    have hdet : fr.g.val.det ≠ 0 := (fr.g.isUnit.map Matrix.detMonoidHom).ne_zero
    refine ((finite_valuation_ne_one hdet).union (finite_valuation_ne_one (mul_ne_zero two_ne_zero hρ))).subset
      fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    apply hv
    show E v = 1
    simp only [E, norm_algebraMap_eq_one h.1, norm_algebraMap_eq_one h.2, one_pow, div_one]
  have hαm : Multipliable α := multipliable_siegelDensity (N := n + 1) (by omega) (by omega) Q₀ hQ₀
  have hα'm : Multipliable α' := multipliable_siegelDensity (N := n) (by omega) (by omega) fr.Q' hQ'nd
  have hA' : 0 < ∏' v, α' v := tprod_siegelDensity_pos (N := n) (by omega) fr.Q' hQ'nd
  have hfp : ∀ {f : HeightOneSpectrum (𝓞 F) → ℝ}, Function.HasFiniteMulSupport f → HasProd f (∏ᶠ v, f v) :=
    fun {f} hf => by
      have := (multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hf).hasProd
      rwa [tprod_eq_finprod hf] at this
  have hEprod : 0 < ∏ᶠ v, E v := by
    rw [finprod_eq_prod_of_mulSupport_subset E (s := hEfin.toFinset) fun v hv => (Set.Finite.mem_toFinset _).mpr hv]
    exact Finset.prod_pos fun v _ => hEpos v
  have hβeq : β = fun v => W0 v * α v * r v / (α' v * E v) := by
    funext v
    rw [hW v]
    have := hα'pos v; have := hEpos v; have := hαpos v; have := hrpos v
    field_simp
  have hβp : HasProd β ((∏ᶠ v, W0 v) * (∏' v, α v) * (∏ᶠ v, r v) / ((∏' v, α' v) * ∏ᶠ v, E v)) := by
    rw [hβeq]
    exact (((hfp hW0fin).mul hαm.hasProd).mul (hfp hrfin)).div₀ (hα'm.hasProd.mul (hfp hEfin))
      (mul_pos hA' hEprod).ne'
  exact hβp.multipliable

/-- **$\prod_\mathfrak p\beta_\mathfrak p(L, m)/2$ converges unconditionally in rank $1$**: finite support if $m = ct^2$ with $t \in L$,
a vanishing factor otherwise (the cases of `siegelFormulaOneLat_totallyReal`). -/
theorem multipliable_latBeta_rankOne (Q₀ : QuadForm (𝓞 F) 1) (hpd : IsTotallyPosDef (formF Q₀)) (L : Lat F 1)
    (hLi : Lattices.IsIntegral (formF Q₀) L.1) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => latBeta v Q₀ L m / 2 := by
  classical
  have hQ : Q₀.Nondegenerate := nondegenerate_of_map hpd.nondegenerate
  have hc0 : Q₀.coeff 0 0 ≠ 0 := by
    intro h0; apply hQ; rw [TauSOOne.hessian_det_rankOne, h0, mul_zero]
  have hm0 : algebraMap (𝓞 F) F m ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (ne_zero_of_totallyPos hm)
  by_cases hrep : ∃ t : F, algebraMap (𝓞 F) F m = algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t ^ 2
  · obtain ⟨t, hmt⟩ := hrep
    have ht : t ≠ 0 := by rintro rfl; apply hm0; rw [hmt]; ring
    by_cases hmem : (fun _ => t) ∈ L.1
    · set x : F := 2 * algebraMap (𝓞 F) F (Q₀.coeff 0 0) * t
      have hcF : algebraMap (𝓞 F) F (Q₀.coeff 0 0) ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc0
      have hx : x ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hcF) ht
      have hloc : ∀ v : HeightOneSpectrum (𝓞 F), latBeta v Q₀ L m / 2 = ‖algebraMap F (v.adicCompletion F) x‖⁻¹ := by
        intro v
        rw [latBeta_rankOne_of_mem v hQ hLi ht hmt (locVec_mem_loc v hmem)]
        ring
      have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) x‖⁻¹ := by
        refine (finite_valuation_ne_one hx).subset fun v hv => ?_
        by_contra h
        apply hv
        show ‖algebraMap F (v.adicCompletion F) x‖⁻¹ = 1
        rw [norm_algebraMap_eq_one (by simpa using h), inv_one]
      rw [show (fun v => latBeta v Q₀ L m / 2) = fun v => ‖algebraMap F (v.adicCompletion F) x‖⁻¹ from funext hloc]
      exact multipliable_of_hasFiniteMulSupport (L := SummationFilter.unconditional _) hfin
    · obtain ⟨v, hv⟩ : ∃ v, locVec v (fun _ => t) ∉ loc v L.1 := by
        by_contra hall
        push Not at hall
        exact hmem ((mem_iff_forall_loc L.2 _).mpr hall)
      have h0 : latBeta v Q₀ L m / 2 = 0 := by
        rw [latBeta_rankOne_of_not_mem v hQ hLi ht hmt hv, zero_div]
      exact (hasProd_zero_of_exists_eq_zero ⟨v, h0⟩).multipliable
  · have hnr : ¬ ∃ ξ, (formF Q₀).eval ξ = algebraMap (𝓞 F) F m := by
      rintro ⟨ξ, hξ⟩
      exact hrep ⟨ξ 0, by rw [← hξ, SiegelRankOne.eval_rankOne]⟩
    obtain ⟨v, hv⟩ := exists_latBeta_eq_zero_of_not_rep (n := 0) Q₀ hpd L hLi hm hnr
    have h0 : latBeta v Q₀ L m / 2 = 0 := by rw [hv, zero_div]
    exact (hasProd_zero_of_exists_eq_zero ⟨v, h0⟩).multipliable

end Conv

/-! ### The Siegel products of $(Q, L)$ -/

section Products

/-- **The local side with a given value $P$ of the finite product**, for a form $Q$ over $F$:
$|d_F|^{-(N-1)/2}\prod_{\sigma : F\to\mathbb R}\beta_\sigma(Q; m)\cdot P$, with $\beta_\sigma$ = `archRepDensity` at `detGramF Q σ`. -/
def siegelProductWithF (Q : QuadForm F N) (m : 𝓞 F) (P : ℝ) : ℝ :=
  |(discr F : ℝ)| ^ (-((N : ℝ) - 1) / 2) *
    (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity N ‖σ (algebraMap (𝓞 F) F m)‖ (detGramF Q σ)) * P

/-- **Siegel's product of $(V, Q) = (F^N, Q)$ and $L$** ($N \ge 4$; Siegel 1935, Hauptsatz, over $F$ [unverified]):
$$S(Q, L, m) = |d_F|^{-\frac{N-1}2}\prod_\sigma\beta_\sigma(Q; m)\prod_\mathfrak p\beta_\mathfrak p(L, m),$$
every term attached to the form $Q$ over $F$ and the lattice $L$ (`detGramF`, `spaceBeta`). -/
@[kb "siegel1935" "Hauptsatz (local side, quadratic space over F, arbitrary lattice) [unverified]"]
def siegelProductSpace (Q : QuadForm F N) (L : Lat F N) (m : 𝓞 F) : ℝ :=
  siegelProductWithF Q m (∏' v, spaceBeta v Q L m)

/-- **The rank-3 Siegel product of $(Q, L)$** (regularized, with the character `spaceChar3 Q m` of
$F(\sqrt{-2m\det H_Q})/F$). -/
@[kb "siegel1935" "Hauptsatz, n = 3 (local side, regularized; quadratic space over F) [unverified]"]
def siegelProduct3Space (Q : QuadForm F 3) (L : Lat F 3) (m : 𝓞 F) : ℝ :=
  siegelProductWithF Q m (regProd (spaceChar3 Q m) 1 fun v => spaceBeta v Q L m)

/-- **The rank-2 Siegel product of $(Q, L)$** (regularized with exponent $-1$ and the character `spaceChar2 Q` of
$F(\sqrt{-\det H_Q})/F$). -/
@[kb "siegel1935" "Hauptsatz, n = 2 (local side, regularized; quadratic space over F) [unverified]"]
def siegelProduct2RegSpace (Q : QuadForm F 2) (L : Lat F 2) (m : 𝓞 F) : ℝ :=
  siegelProductWithF Q m (regProd (spaceChar2 Q) (-1) fun v => spaceBeta v Q L m)

/-- **The rank-1 Siegel product of $(Q, L)$** (the halved factors of `siegelProductOneLat`). -/
@[kb "siegel1935" "Hauptsatz, n = 1 (local side; quadratic space over F) [unverified]"]
def siegelProductOneSpace (Q : QuadForm F 1) (L : Lat F 1) (m : 𝓞 F) : ℝ :=
  (∏ σ : F →ₐ[ℚ] ℂ, archRepDensity 1 ‖σ (algebraMap (𝓞 F) F m)‖ (detGramF Q σ) / 2) *
    ∏' v : HeightOneSpectrum (𝓞 F), spaceBeta v Q L m / 2

theorem siegelProductWithF_eq (Q : QuadForm F N) (γ : GL (Fin N) F) (Q₀ : QuadForm (𝓞 F) N)
    (hγ : formF Q₀ = Q.compMat γ.val) (m : 𝓞 F) (P : ℝ) :
    siegelProductWithF Q m ((∏ σ : F →ₐ[ℚ] ℂ, ‖σ γ.val.det‖)⁻¹ * P) = siegelProductWith Q₀ m P := by
  unfold siegelProductWithF siegelProductWith
  rw [prod_archRepDensity_eq Q γ Q₀ hγ]
  ring

variable [IsTotallyReal F]

theorem exists_finset_norm_det (γ : GL (Fin N) F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      (∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) γ.val.det‖ = 1) ∧
        ∏ v ∈ S, ‖algebraMap F (v.adicCompletion F) γ.val.det‖ = (∏ σ : F →ₐ[ℚ] ℂ, ‖σ γ.val.det‖)⁻¹ := by
  have h := hasProd_norm_det γ
  have hfin : Function.HasFiniteMulSupport
      fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) γ.val.det‖ := by
    have hdet : γ.val.det ≠ 0 := (γ.isUnit.map Matrix.detMonoidHom).ne_zero
    refine (finite_valuation_ne_one hdet).subset fun v hv => ?_
    by_contra hc
    exact hv (norm_algebraMap_eq_one (by simpa using hc))
  refine ⟨hfin.toFinset, fun v hv => ?_, ?_⟩
  · by_contra hc; exact hv (hfin.mem_toFinset.mpr hc)
  · refine h.unique (hasProd_prod_of_ne_finset_one fun v hv => ?_) |>.symm
    by_contra hc; exact hv (hfin.mem_toFinset.mpr hc)

section Setting

variable {n : ℕ} (Q : QuadForm F (n + 1)) (L : Lat F (n + 1)) (hLi : Lattices.IsIntegral Q L.1)
  (γ : GL (Fin (n + 1)) F) (Q₀ : QuadForm (𝓞 F) (n + 1)) (hγ : formF Q₀ = Q.compMat γ.val)

include hLi hγ

theorem isIntegral_image_of_coords : Lattices.IsIntegral (formF Q₀) (Lat.image γ⁻¹ L).1 := by
  rw [hγ]; exact isIntegral_compMat Q γ hLi

theorem spaceBeta_fun_eq (m : 𝓞 F) :
    (fun v => spaceBeta v Q L m) =
      fun v => latBeta v Q₀ (Lat.image γ⁻¹ L) m * ‖algebraMap F (v.adicCompletion F) γ.val.det‖ := by
  funext v; rw [spaceBeta_eq v Q L hLi γ Q₀ hγ, mul_comm]

/-- **$S(Q, L) = S(Q_0, \gamma^{-1}L)$, rank $N \ge 4$.** -/
theorem siegelProductSpace_eq (hn : 3 ≤ n) (hpd₀ : IsTotallyPosDef (formF Q₀)) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductSpace Q L m = siegelProductLat Q₀ (Lat.image γ⁻¹ L) m := by
  have hβ := multipliable_latBeta hn Q₀ hpd₀ _ (isIntegral_image_of_coords Q L hLi γ Q₀ hγ) hm
  have hg := (hasProd_norm_det γ)
  unfold siegelProductSpace
  rw [spaceBeta_fun_eq Q L hLi γ Q₀ hγ, hβ.tprod_mul hg.multipliable, hg.tprod_eq, mul_comm,
    siegelProductWithF_eq Q γ Q₀ hγ]
  rfl

end Setting

/-- **$S_3(Q, L) = S_3(Q_0, \gamma^{-1}L)$.** -/
theorem siegelProduct3Space_eq (Q : QuadForm F 3) (L : Lat F 3) (hLi : Lattices.IsIntegral Q L.1)
    (γ : GL (Fin 3) F) (Q₀ : QuadForm (𝓞 F) 3) (hγ : formF Q₀ = Q.compMat γ.val) (hpd₀ : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct3Space Q L m = siegelProduct3Lat Q₀ (Lat.image γ⁻¹ L) m := by
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hm0 : m ≠ 0 := ne_zero_of_totallyPos hm
  set L' := Lat.image γ⁻¹ L
  have hβ := multipliable_latBeta_mul_chiTern hQ₀ L' (isIntegral_image_of_coords Q L hLi γ Q₀ hγ) hm0
  obtain ⟨S, hS1, hSprod⟩ := exists_finset_norm_det γ
  have hχ := Filter.eventually_cofinite.mp (eventually_chiTern_eq Q γ Q₀ hγ hQ₀ hm0)
  have hf : Multipliable fun v => (latBeta v Q₀ L' m * ‖algebraMap F (v.adicCompletion F) γ.val.det‖) * (1 - chiTern Q₀ m v / (normP v : ℝ)) ^ (1 : ℤ) := by
    have := hβ.mul (hasProd_norm_det γ).multipliable
    refine this.congr fun v => ?_
    ring
  unfold siegelProduct3Space siegelProduct3Lat
  rw [spaceBeta_fun_eq Q L hLi γ Q₀ hγ,
    regProd_congr_finite (χ := spaceChar3 Q m) (fun v => abs_sqChar_le v _) (fun v => abs_chiTern_le v Q₀ m) hχ.toFinset
      (fun v hv => by
        by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm)))
      (lOne_chiTern_pos hpd₀ hm).2 1 _ hf,
    regProd_mul_fin _ 1 S hS1 hβ, hSprod, mul_comm, siegelProductWithF_eq Q γ Q₀ hγ]

/-- **$S^{\mathrm{reg}}_2(Q, L) = S^{\mathrm{reg}}_2(Q_0, \gamma^{-1}L)$.** -/
theorem siegelProduct2RegSpace_eq (Q : QuadForm F 2) (L : Lat F 2) (hLi : Lattices.IsIntegral Q L.1)
    (γ : GL (Fin 2) F) (Q₀ : QuadForm (𝓞 F) 2) (hγ : formF Q₀ = Q.compMat γ.val) (hpd₀ : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProduct2RegSpace Q L m = siegelProduct2RegLat Q₀ (Lat.image γ⁻¹ L) m := by
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  set L' := Lat.image γ⁻¹ L
  obtain ⟨P, hP⟩ := exists_hasProd_latBeta_mul_chiP Q₀ hpd₀ L' (isIntegral_image_of_coords Q L hLi γ Q₀ hγ) hm
  have hβ := hP.multipliable
  obtain ⟨S, hS1, hSprod⟩ := exists_finset_norm_det γ
  have hχ := Filter.eventually_cofinite.mp (eventually_chiP_eq Q γ Q₀ hγ hQ₀)
  have hf : Multipliable fun v => (latBeta v Q₀ L' m * ‖algebraMap F (v.adicCompletion F) γ.val.det‖) * (1 - chiP v Q₀ / (normP v : ℝ)) ^ (-1 : ℤ) := by
    have := hβ.mul (hasProd_norm_det γ).multipliable
    refine this.congr fun v => ?_
    ring
  unfold siegelProduct2RegSpace siegelProduct2RegLat
  rw [spaceBeta_fun_eq Q L hLi γ Q₀ hγ,
    regProd_congr_finite (χ := spaceChar2 Q) (fun v => abs_sqChar_le v _) (fun v => abs_chiP_le Q₀ v) hχ.toFinset
      (fun v hv => by
        by_contra hc; exact hv (hχ.mem_toFinset.mpr (fun h => hc h.symm)))
      (lOne_chiP_binary hpd₀).2 (-1) _ hf,
    regProd_mul_fin _ (-1) S hS1 hβ, hSprod, mul_comm, siegelProductWithF_eq Q γ Q₀ hγ]

/-- **$\mathcal S_1(Q, L) = \mathcal S_1(Q_0, \gamma^{-1}L)$.** -/
theorem siegelProductOneSpace_eq (Q : QuadForm F 1) (L : Lat F 1) (hLi : Lattices.IsIntegral Q L.1)
    (γ : GL (Fin 1) F) (Q₀ : QuadForm (𝓞 F) 1) (hγ : formF Q₀ = Q.compMat γ.val) (hpd₀ : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    siegelProductOneSpace Q L m = siegelProductOneLat Q₀ (Lat.image γ⁻¹ L) m := by
  set L' := Lat.image γ⁻¹ L
  have hβ := multipliable_latBeta_rankOne Q₀ hpd₀ L' (isIntegral_image_of_coords Q L hLi γ Q₀ hγ) hm
  have hg := hasProd_norm_det γ
  have e : (fun v => spaceBeta v Q L m / 2) =
      fun v => latBeta v Q₀ L' m / 2 * ‖algebraMap F (v.adicCompletion F) γ.val.det‖ := by
    funext v; rw [spaceBeta_eq v Q L hLi γ Q₀ hγ]; ring
  unfold siegelProductOneSpace siegelProductOneLat
  rw [e, hβ.tprod_mul hg.multipliable, hg.tprod_eq, Finset.prod_div_distrib, Finset.prod_div_distrib,
    prod_archRepDensity_eq Q γ Q₀ hγ]
  ring

end Products

end QuadFormsKB.Tamagawa.SiegelSpace
