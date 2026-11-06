/-
# Hanke 2011, Theorem 6.2 summed over the genera, every signature (indefinite included)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Def. 6.1 and Theorem 6.2, pp. 25–26.

The paper's proper mass $\mathrm{Mass}^+(L)$ (Def. 6.1) is Hanke 2005's $\mathrm{Mass}(\Lambda,\varphi)$ [(5.4)]; in the library it is
`massPlus Q₀ hQ` (= `Hanke2005.hankeMass`), defined for the lattice $L = \mathcal O_F^n$ of a form $Q_0$ over $\mathcal O_F$.
Here, for any signature vector $\vec\sigma_\infty$ ($n \ge 3$, every number field $F$):

* `IsFreeRealization S σ 𝕊 c t Q₀`: $(Q_0\otimes F, \mathcal O_F^n)$ realizes the tuple $t$ of local genera
  ($t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$, `IsRealization`).
* `massPlus_of_freeRealization` (**Thm. 6.2 for one genus, in the paper's normalization**): then
  $$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
  {N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1},$$
  with $C_{\vec\sigma_\infty,n}$ = `sigConst σ`; in particular $\mathrm{Mass}^+$ depends only on the genus (the tuple $t$).
* `massPlusOfTuple` (**$\mathrm{Mass}^+(G)$ of a genus**, Def. 6.1): $\mathrm{Mass}^+$ of a chosen free realization.
* `theorem_6_2_summed`: **Theorem 6.2 summed over the genera**, when every genus in $\mathrm{Gen}^*$ has a member on
  $\mathcal O_F^n$ (hypothesis `hfree`):
  $$\sum_{G\in\mathrm{Gen}^*}\mathrm{Mass}^+(G) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot
  \frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S);$$
  `theorem_6_2_summed_M`: the same with $M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$ (Lemma 3.7), i.e. the paper's (15).
* `theorem_6_2_summed_pid`: if $\mathcal O_F$ is a principal ideal domain (e.g. $F = \mathbb Q$), `hfree` always holds
  (every lattice is free, Steinitz), so Theorem 6.2 holds **unconditionally for every signature**.

*General number field:* a genus whose lattices have a non-trivial Steinitz class has no member on $\mathcal O_F^n$; the
hypothesis `hfree` is removed in `GlobalMassLatSummed.lean` (`theorem_6_2_summed_all`, `theorem_6_2_all`), which
extends $\mathrm{Mass}^+$ to every lattice (`massPlusLat`).

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSigConst
import QuadFormsKB.Lattices.SpinorGlobal
import QuadFormsKB.Lattices.Steinitz
import QuadFormsKB.Tamagawa.OrbitalEuler
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal
import QuadFormsKB.Literature.Hanke2011Structure.RationalLocalTuples

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField NumberField.InfinitePlace Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular
  QuadFormsKB.Siegel QuadFormsKB.Hanke2005
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Helpers -/

open Classical in
/-- $(\prod'_v\beta_v)^{-1}$ equals `invDensityTuple`'s convention for a multipliable family of nonzero reals. -/
theorem inv_tprod_eq_ite {ι : Type*} {β : ι → ℝ} (h0 : ∀ i, β i ≠ 0) (hm : Multipliable β) :
    (∏' i, β i)⁻¹ = if Multipliable (fun i => (β i)⁻¹) then ∏' i, (β i)⁻¹ else 0 := by
  by_cases hz : ∏' i, β i = 0
  · rw [hz, _root_.inv_zero, if_neg]
    intro hm'
    have := hm.tprod_mul hm'
    simp only [fun i => mul_inv_cancel₀ (h0 i), tprod_one, hz, zero_mul] at this
    exact one_ne_zero this
  · rw [if_pos (hm.inv₀ hz), hm.tprod_inv₀ hz]

theorem localBeta_pos (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) :
    0 < localBeta v Q₀ := by
  have hgform : localBeta v Q₀ = ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) *
      LocalDensity.NF.siegelDensity v Q₀ Q₀ := Hanke2005.hankeBeta_gramV v Q₀ hQ₀
  rw [hgform]
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  exact mul_pos (pow_pos h2 _) (Tamagawa.siegelDensity_pos v Q₀ hQ₀)

/-- $\prod_{\mathfrak p}\beta_{\psi_\mathfrak p,\mathfrak p}(\psi_\mathfrak p)$ is multipliable ($n \ge 3$, every number field). -/
theorem multipliable_localBeta (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => localBeta v Q₀ := by
  have hm2 : Multipliable fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) :=
    multipliable_of_hasFiniteMulSupport (Hanke2005.hasFiniteMulSupport_norm_two.pow _)
  have hms := Tamagawa.multipliable_siegelDensity (by omega) (by omega) Q₀ hQ₀
  have e : (fun v : HeightOneSpectrum (𝓞 F) => localBeta v Q₀) = fun v =>
      ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) * LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
    funext fun v => Hanke2005.hankeBeta_gramV v Q₀ hQ₀
  rw [e]
  exact hm2.mul hms

theorem loc_stdLat (v : HeightOneSpectrum (𝓞 F)) : loc v (Lattices.stdLat : Lat F n).1 = std v := loc_intVec v

/-- The local genus of $\mathcal O_F^n$ at $\mathfrak p$ has density `localBeta`. -/
theorem beta_locGenusOf_stdLat (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)
    (hL : IsIntegral (formF Q₀) (Lattices.stdLat : Lat F n).1) :
    (locGenusOf v (formF Q₀) Lattices.stdLat hL).beta = localBeta v Q₀ :=
  beta_locGenusOf_of_std v Q₀ Lattices.stdLat hL (loc_stdLat v)

/-- **The product formula** $\prod_\mathfrak p|x|_\mathfrak p = (\prod_\sigma|\sigma x|)^{-1}$ (every number field). -/
theorem finprod_norm_eq' (x : F) (hx : x ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ =
      (∏ σ : F →ₐ[ℚ] ℂ, ‖σ x‖)⁻¹ := by
  have h := WeilRep.prod_modulus_eq_one (F := F) hx
  have hm : ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) x) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) x‖ :=
    finprod_congr fun v => WeilRep.modK_eq_norm v ((map_ne_zero _).mpr hx)
  rw [hm, mixedEmbedding.norm_eq_norm] at h
  rw [Tamagawa.prod_norm_embeddings]
  push_cast at h
  exact eq_inv_of_mul_eq_one_right h

/-- **$N_{F/\mathbb Q}(I(\det_H\mathcal O_F^n)) = |N_{F/\mathbb Q}(\det H_{Q_0})|$.** -/
theorem normAssoc_detH_stdLat (Q₀ : QuadForm (𝓞 F) n) (hQ : (formF Q₀).hessian.det ≠ 0) :
    normAssoc (detH (formF Q₀) hQ Lattices.stdLat) = |((Algebra.norm ℚ (formF Q₀).hessian.det : ℚ) : ℝ)| := by
  set D : F := (formF Q₀).hessian.det
  have hcomp : ∀ v : HeightOneSpectrum (𝓞 F), AdelicSqCl.comp v (detH (formF Q₀) hQ Lattices.stdLat) =
      SqCl.mk (localHessDet (formF Q₀) hQ v 1) := fun v =>
    detH_comp (formF Q₀) hQ Lattices.stdLat v (by rw [locAct_one]; exact loc_stdLat v)
  have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
      (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v (detH (formF Q₀) hQ Lattices.stdLat) =
        ‖algebraMap F (v.adicCompletion F) D‖⁻¹ := by
    intro v
    have h := norm_eq_of_comp v _ (hcomp v)
    have e : ((localHessDet (formF Q₀) hQ v 1 : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) D := by
      simp [localHessDet]
      try rfl
    rw [e] at h
    rw [h, inv_inv]
  unfold normAssoc
  rw [finprod_congr hterm, finprod_inv_distrib, finprod_norm_eq' D hQ, inv_inv,
    Tamagawa.prod_norm_embeddings]

/-! ### Free realizations and the proper mass of a genus -/

variable (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
  (c : HeightOneSpectrum (𝓞 F) → ℤ)

/-- **$(Q_0 \otimes F, \mathcal O_F^n)$ realizes the tuple $t$** of $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$. -/
def IsFreeRealization (t : LocTuple F n) (Q₀ : QuadForm (𝓞 F) n) : Prop :=
  IsRealization S σ 𝕊 c t (formF Q₀) Lattices.stdLat

variable {S σ 𝕊 c}

theorem IsFreeRealization.nondegenerate {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n}
    (h : IsFreeRealization S σ 𝕊 c t Q₀) : Q₀.Nondegenerate :=
  Tamagawa.nondegenerate_of_map h.1

/-- **The paper's constant in Theorem 6.2**: $\dfrac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot
\dfrac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{(2^{[F:\mathbb Q]})^{n(n+1)/2}}$ ($N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$). -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (the constant)"]
def massPlusConst (σ : SignatureVector F n) (S : AdelicSqCl F) : ℝ :=
  2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / sigConst σ * normAssoc S ^ (((n : ℝ) + 1) / 2) /
    ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2)

theorem massPlusConst_pos (σ : SignatureVector F n) (S : AdelicSqCl F) : 0 < massPlusConst σ S := by
  have hNS : 0 < normAssoc S := by
    unfold normAssoc
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun a b ha hb => mul_pos ha hb) fun v => ?_
    exact zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))) _
  have hΔ : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have := sigConst_pos σ
  have := Real.rpow_pos_of_pos hNS (((n : ℝ) + 1) / 2)
  have := Real.rpow_pos_of_pos hΔ ((n : ℝ) * (n - 1) / 4)
  unfold massPlusConst
  positivity

/-- **Theorem 6.2 for one genus, in terms of the tuple of local genera** (any signature, $n \ge 3$, every number field):
if $(Q_0\otimes F,\mathcal O_F^n)$ realizes $t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$, then
$\mathrm{Mass}^+(\mathcal O_F^n) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\frac{N(I(S))^{(n+1)/2}}{N(2\mathcal O_F)^{n(n+1)/2}}
\prod_{\mathfrak p}\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$. -/
@[kb "hanke2011structure" "Thm. 6.2, pp. 25–26 (one genus, any signature, tuple of local genera)"]
theorem massPlus_of_freeRealization (hn : 3 ≤ n) {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n}
    (h : IsFreeRealization S σ 𝕊 c t Q₀) :
    massPlus Q₀ h.nondegenerate = ENNReal.ofReal (massPlusConst σ S * invDensityTuple t) := by
  have hQ₀ := h.nondegenerate
  obtain ⟨hQ, hL, hσ, hS, -, -, ht⟩ := h
  have hN : |((Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℚ) : ℝ)| = normAssoc S := by
    rw [← hS]; exact (normAssoc_detH_stdLat Q₀ hQ).symm
  have hβ : (∏' v, localBeta v Q₀)⁻¹ = invDensityTuple t := by
    have hb : ∀ v, (locGenusOf v (formF Q₀) Lattices.stdLat hL).beta = localBeta v Q₀ := fun v =>
      beta_locGenusOf_stdLat v Q₀ hL
    have hm : Multipliable fun v => localBeta v Q₀ := multipliable_localBeta hn Q₀ hQ₀
    rw [← ht]
    classical
    show _ = if Multipliable (fun v => ((locGenusOf v (formF Q₀) Lattices.stdLat hL).beta)⁻¹) then
      ∏' v, ((locGenusOf v (formF Q₀) Lattices.stdLat hL).beta)⁻¹ else 0
    simp only [hb]
    exact inv_tprod_eq_ite (fun v => (localBeta_pos v Q₀ hQ₀).ne') hm
  have hC := constC_eq_sigConst Q₀ hQ₀ hσ
  have hpos : 0 ≤ 2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / constC Q₀ *
      |((Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℚ) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) := by
    have := constC_pos Q₀
    positivity
  have key : 2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / constC Q₀ *
      |((Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℚ) : ℝ)| ^ (((n : ℝ) + 1) / 2) /
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) * (∏' v, localBeta v Q₀)⁻¹ =
      massPlusConst σ S * invDensityTuple t := by
    rw [hN, hβ, hC]
    rfl
  have h62 := theorem_6_2_genus hn Q₀ hQ₀
  rw [← ENNReal.ofReal_mul hpos, key] at h62
  exact h62

open Classical in
/-- **The proper mass $\mathrm{Mass}^+(G)$ of a genus** (Def. 6.1, p. 25), for a tuple $t$ of local genera: $\mathrm{Mass}^+$ of a
chosen realization on $\mathcal O_F^n$ (`IsFreeRealization`); $0$ if there is none. By `massPlus_of_freeRealization` it
does not depend on the choice. -/
@[kb "hanke2011structure" "Def. 6.1, p. 25 (Mass⁺(G))"]
def massPlusOfTuple (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) (t : LocTuple F n) : ℝ≥0∞ :=
  if h : ∃ Q₀, IsFreeRealization S σ 𝕊 c t Q₀ then massPlus h.choose h.choose_spec.nondegenerate else 0

theorem massPlusOfTuple_eq (hn : 3 ≤ n) {t : LocTuple F n} (h : ∃ Q₀, IsFreeRealization S σ 𝕊 c t Q₀) :
    massPlusOfTuple S σ 𝕊 c t = ENNReal.ofReal (massPlusConst σ S * invDensityTuple t) := by
  unfold massPlusOfTuple
  rw [dif_pos h]
  exact massPlus_of_freeRealization hn h.choose_spec

/-- `massPlusOfTuple t` is $\mathrm{Mass}^+$ of any free realization of $t$. -/
theorem massPlusOfTuple_eq_massPlus (hn : 3 ≤ n) {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n}
    (h : IsFreeRealization S σ 𝕊 c t Q₀) : massPlusOfTuple S σ 𝕊 c t = massPlus Q₀ h.nondegenerate := by
  rw [massPlusOfTuple_eq hn ⟨Q₀, h⟩, massPlus_of_freeRealization hn h]

theorem invDensityTuple_nonneg (t : LocTuple F n) (ht : ∀ v, 0 ≤ (t v).beta) : 0 ≤ invDensityTuple t := by
  unfold invDensityTuple
  split_ifs
  · exact tprod_nonneg fun v => inv_nonneg.mpr (ht v)
  · exact le_rfl

/-- **Theorem 6.2 summed over the genera** (every signature vector $\vec\sigma_\infty$, $n \ge 3$, every number field),
provided every genus of $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ has a member on $\mathcal O_F^n$ (`hfree`):
$$\sum_{t\in\mathrm{Gen}^*}\mathrm{Mass}^+(t) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot
\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S)$$
(the masses as real numbers). No finiteness of $\mathrm{Gen}^*$ is needed (termwise identity). -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (summed over the genera, every signature)"]
theorem theorem_6_2_summed (hn : 3 ≤ n)
    (hfree : ∀ t ∈ GenStar S σ 𝕊 c, ∃ Q₀, IsFreeRealization S σ 𝕊 c t Q₀) :
    ∑ᶠ t ∈ GenStar S σ 𝕊 c, (massPlusOfTuple S σ 𝕊 c t).toReal = massPlusConst σ S * totalMassT S σ 𝕊 c := by
  unfold totalMassT
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun t ht => ?_
  obtain ⟨Q₀, hQ₀⟩ := hfree t ht
  have hnd := hQ₀.nondegenerate
  rw [massPlusOfTuple_eq hn ⟨Q₀, hQ₀⟩, ENNReal.toReal_ofReal]
  refine mul_nonneg (massPlusConst_pos σ S).le (invDensityTuple_nonneg t fun v => ?_)
  obtain ⟨-, hL, -, -, -, -, ht'⟩ := hQ₀
  rw [← ht', beta_locGenusOf_stdLat]
  exact (localBeta_pos v Q₀ hnd).le

/-! ### Lattices over a principal ideal domain are free -/

section PID

open Lattices.Steinitz
open scoped nonZeroDivisors

variable [IsPrincipalIdealRing (𝓞 F)]

/-- **Over a principal ideal domain every lattice in $F^{m+1}$ is free**: $M = \gamma\,\mathcal O_F^{m+1}$ (Steinitz's normal
form $M = \gamma(\mathcal O_F^m \oplus \mathfrak c)$, `exists_eq_glImage_steinitzLat`, with $\mathfrak c = c\,\mathcal O_F$ principal). -/
@[kb "omeara1963" "§81B, 81:5, p. 212 (Steinitz class trivial over a PID)"]
theorem exists_latOf_of_pid {m : ℕ} {M : Submodule (𝓞 F) (Fin (m + 1) → F)} (hM : M.IsLattice F) :
    ∃ γ : GL (Fin (m + 1)) F, M = latOf γ := by
  classical
  obtain ⟨γ, 𝔠, hM'⟩ := exists_eq_glImage_steinitzLat hM
  have hN : glImage γ⁻¹ M = steinitzLat 𝔠 := by rw [hM', ← glImage_mul, inv_mul_cancel, glImage_one]
  have hNlat : (steinitzLat (m := m) 𝔠).IsLattice F := hN ▸ glImage_isLattice γ⁻¹ hM
  set pr : (Fin (m + 1) → F) →ₗ[𝓞 F] F :=
    (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)).restrictScalars (𝓞 F)
  have hc : 𝔠 = (steinitzLat (m := m) 𝔠).map pr := by
    ext x
    constructor
    · intro hx
      refine ⟨Pi.single (Fin.last m) x, ⟨fun i => ⟨0, ?_⟩, ?_⟩, ?_⟩
      · simp [Pi.single_apply, (Fin.castSucc_lt_last i).ne]
      · simpa using hx
      · simp [pr]
    · rintro ⟨y, ⟨-, hy⟩, rfl⟩
      exact hy
  have hfg : 𝔠.FG := by rw [hc]; exact hNlat.fg.map _
  obtain ⟨c, hcs⟩ := (FractionalIdeal.isPrincipal
    (⟨𝔠, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (𝓞 F)⁰ F)).principal
  change 𝔠 = Submodule.span (𝓞 F) {c} at hcs
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hle : Submodule.span F (steinitzLat (m := m) 𝔠 : Set (Fin (m + 1) → F)) ≤
        LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : Fin (m + 1) => F) (Fin.last m)) := by
      refine Submodule.span_le.mpr fun y hy => ?_
      have h2 : y (Fin.last m) ∈ 𝔠 := hy.2
      rw [hcs, Submodule.span_singleton_eq_bot.mpr rfl] at h2
      simpa using h2
    rw [hNlat.span_eq_top] at hle
    have := hle (Submodule.mem_top (x := Pi.single (Fin.last m) (1 : F)))
    simp at this
  set d : Fin (m + 1) → F := fun i => if i = Fin.last m then c else 1
  have hd : (Matrix.diagonal d).det ≠ 0 := by
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by simp only [d]; split_ifs <;> simp [hc0]
  set D : GL (Fin (m + 1)) F := ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)).unit
  have hD : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d := rfl
  have hst : steinitzLat (m := m) 𝔠 = glImage D intVec := by
    ext y
    rw [mem_glImage, hD]
    constructor
    · rintro ⟨hy, hy'⟩
      rw [hcs] at hy'
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy'
      refine ⟨fun i => if i = Fin.last m then algebraMap (𝓞 F) F a else y i, fun i => ?_, ?_⟩
      · by_cases hi : i = Fin.last m
        · simp [hi]
        · simp only [hi, if_false]
          obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
          exact hy j
      · funext i
        rw [mulVec_diagonal]
        by_cases hi : i = Fin.last m
        · subst hi; simp only [d, if_true]; rw [← ha, Algebra.smul_def]; ring
        · simp [d, hi]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · rw [mulVec_diagonal]; simp only [d, (Fin.castSucc_lt_last i).ne, if_false, one_mul]; exact hx _
      · rw [mulVec_diagonal, hcs]; simp only [d, if_true]
        obtain ⟨a, ha⟩ := hx (Fin.last m)
        exact Submodule.mem_span_singleton.mpr ⟨a, by rw [Algebra.smul_def, ha, mul_comm]⟩
  exact ⟨γ * D, by rw [hM', hst, latOf, glImage_mul]⟩

/-- **Over a principal ideal domain every genus has a member on $\mathcal O_F^n$**: every realization $(Q, L)$ of
$t \in \mathrm{Gen}^*$ transports to a free one, $(Q\circ\gamma, \mathcal O_F^n)$ with $L = \gamma\,\mathcal O_F^n$. -/
theorem exists_freeRealization_of_pid {t : LocTuple F n} (ht : t ∈ GenStar S σ 𝕊 c) :
    ∃ Q₀, IsFreeRealization S σ 𝕊 c t Q₀ := by
  obtain ⟨⟨Q, L⟩, hQ, hL, hσ, hS, hprim, hc, ht⟩ := (mem_genStar_iff S σ 𝕊 c t).mp ht
  dsimp only at hQ hL hσ hS hprim hc ht
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin n) F, L.1 = latOf g := by
    cases n with
    | zero =>
      refine ⟨1, ?_⟩
      ext x
      rw [latOf, glImage_one, Subsingleton.elim x 0]
      simp only [Submodule.zero_mem]
    | succ m => exact exists_latOf_of_pid L.2
  have himg : Lat.image g⁻¹ L = Lattices.stdLat := by
    apply Lattices.Lat.ext
    show glImage g⁻¹ L.1 = intVec
    rw [hg, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
  have hint : IsIntegral Q (latOf g) := hg ▸ hL
  refine ⟨gramZ Q g hint, ?_⟩
  have hform : formF (gramZ Q g hint) = Q.compMat g.val :=
    QuadForm.ext_eval fun y => by
      show ((gramZ Q g hint).map (algebraMap (𝓞 F) F)).eval y = _
      rw [gramZ_map, eval_gramFormF_col, QuadForm.eval_compMat]
  unfold IsFreeRealization
  rw [hform, ← himg]
  refine ⟨hessian_det_compMat_ne Q g hQ, isIntegral_transport Q g hL, hasSignature_compMat Q g hσ, ?_, ?_, ?_, ?_⟩
  · rw [detH_transport Q g hQ L]; exact hS
  · intro v; rw [locGenusOf_transport Q g v L hL]; exact hprim v
  · intro v hv; rw [locGenusOf_transport Q g v L hL]; exact hc v hv
  · funext v; rw [locGenusOf_transport Q g v L hL]; exact congrFun ht v

/-- **Theorem 6.2 summed over the genera, every signature, $\mathcal O_F$ a principal ideal domain** (e.g. $F = \mathbb Q$),
unconditional: $\sum_{t\in\mathrm{Gen}^*}\mathrm{Mass}^+(t) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}
\frac{N(I(S))^{(n+1)/2}}{N(2\mathcal O_F)^{n(n+1)/2}}T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S)$. -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (summed over the genera, every signature, O_F a PID)"]
theorem theorem_6_2_summed_pid (hn : 3 ≤ n) :
    ∑ᶠ t ∈ GenStar S σ 𝕊 c, (massPlusOfTuple S σ 𝕊 c t).toReal = massPlusConst σ S * totalMassT S σ 𝕊 c :=
  theorem_6_2_summed hn fun _ ht => exists_freeRealization_of_pid ht

/-- **Theorem 6.2, (15), the paper's form** ($\mathcal O_F$ a principal ideal domain, every signature; $S$ globally
rational with the sign condition of Lemma 3.7):
$$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \frac{C_{\vec\sigma_\infty,n}}{2|\Delta_F|^{n(n-1)/4}}\cdot
\frac{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}\sum_{G\in\mathrm{Gen}^*}\mathrm{Mass}^+(G).$$ -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (M* form, every signature, O_F a PID)"]
theorem theorem_6_2_pid (hn : 3 ≤ n) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    totalMassM n S (epsInf σ) 𝕊 c =
      (massPlusConst σ S)⁻¹ * ∑ᶠ t ∈ GenStar S σ 𝕊 c, (massPlusOfTuple S σ 𝕊 c t).toReal := by
  rw [theorem_6_2_summed_pid hn, ← mul_assoc, inv_mul_cancel₀ (massPlusConst_pos σ S).ne', one_mul,
    (lemma_3_7 (by omega) S σ 𝕊 c α hα hsign).2]

end PID

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.massPlus_of_freeRealization
#print axioms QuadFormsKB.Hanke2011Structure.theorem_6_2_summed
#print axioms QuadFormsKB.Hanke2011Structure.theorem_6_2_summed_pid
#print axioms QuadFormsKB.Hanke2011Structure.theorem_6_2_pid
