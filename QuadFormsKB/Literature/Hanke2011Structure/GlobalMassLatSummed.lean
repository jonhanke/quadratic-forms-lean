/-
# Hanke 2011, Theorem 6.2 summed over all genera, every number field, every signature

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Def. 6.1 and Theorem 6.2, (15), pp. 25–26.

**Setting.** $F$ any number field, $n\ge3$, $S\in\mathrm{SqCl}(\mathbb A_{F,f}^\times,U_f)$, $\vec\sigma_\infty$ any signature vector,
$\mathbb S$ a set of primes with prescribed Hasse invariants $\vec c_{\mathbb S}$, and $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$
(`GenStar`) the genera of primitive $\mathcal O_F$-valued lattices, represented by their tuples $t$ of local genera.

`GlobalMassSummedIndef.lean` proved the summed Theorem 6.2 only when every genus has a member on $\mathcal O_F^n$ (`hfree`,
automatic when $\mathcal O_F$ is a PID), because the library's $\mathrm{Mass}^+$ was defined only for $\mathcal O_F^n$. With
$\mathrm{Mass}^+(L)$ for **every** lattice (`massPlusLat`, `GlobalMassLat.lean`) the hypothesis disappears:

* `IsLatRealization S σ 𝕊 c t Q₀ L`: $(Q_0\otimes F, L)$ realizes $t\in\mathrm{Gen}^*$, with $Q_0$ over $\mathcal O_F$ and $L$ any lattice
  (any Steinitz class); `exists_latRealization`: **every** $t\in\mathrm{Gen}^*$ has one (clear the denominators of a realizing
  form, `exists_integral_model`, and transport the lattice).
* **`massPlusLat_of_realization`** (Theorem 6.2 for one genus, every lattice): $\mathrm{Mass}^+(L) =
  \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}
  \prod_{\mathfrak p}\beta_{t_{\mathfrak p},\mathfrak p}(t_{\mathfrak p})^{-1}$.
* `massPlusOfGenus` (**$\mathrm{Mass}^+(G)$ of a genus**, Def. 6.1): $\mathrm{Mass}^+$ of a chosen realization; independent of the
  choice (`massPlusOfGenus_eq_massPlusLat`), and equal to the library's `massPlusOfTuple` when a free realization exists
  (`massPlusOfGenus_eq_massPlusOfTuple`).
* **`theorem_6_2_summed_all`** (Theorem 6.2 summed over the genera; every number field, every signature, $n\ge3$,
  **unconditional**):
  $$\sum_{G\in\mathrm{Gen}^*}\mathrm{Mass}^+(G) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot
  \frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S).$$
* **`theorem_6_2_all`** (the paper's (15), with $M^*$ via Lemma 3.7; $S$ globally rational with the sign condition of
  Lemma 3.7, as in `theorem_6_2_pid`):
  $$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \frac{C_{\vec\sigma_\infty,n}}{2|\Delta_F|^{n(n-1)/4}}\cdot
  \frac{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}\sum_{G\in\mathrm{Gen}^*}\mathrm{Mass}^+(G).$$

Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassLat
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummedIndef
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummedTransport

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField NumberField.InfinitePlace Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular
  QuadFormsKB.Siegel QuadFormsKB.Hanke2005
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The local density of a nondegenerate local genus (any rank) is positive (`LocGenus.beta_pos_rank`). -/
theorem LocGenus.beta_pos_any (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) (hG : G.Nondeg) :
    0 < G.beta := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep G
  have e : G = LocGenus.mk Q := hQ.symm
  subst e
  have hne : Q.hessian.det ≠ 0 := (LocGenus.nondeg_mk Q).mp hG
  have hpos := Tamagawa.localDensityForm_self_pos' v Q hne
  rw [LocGenus.beta_mk]
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v Q hne]
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  unfold LocalDensity.DVR.siegelDensity
  simp only [ite_true]
  exact mul_pos (pow_pos h2 _) (mul_pos (by norm_num) hpos)

/-- The local densities of the local genera of an $\mathcal O_F$-valued lattice are positive. -/
theorem beta_locGenusOf_pos (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0)
    (L : Lat F n) (hL : IsIntegral Q L.1) : 0 < (locGenusOf v Q L hL).beta :=
  LocGenus.beta_pos_any v _ (det_locGenusOf v Q hQ L hL).1

variable (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
  (c : HeightOneSpectrum (𝓞 F) → ℤ)

/-! ### Realizations on arbitrary lattices -/

/-- **$(Q_0\otimes F, L)$ realizes the tuple $t$** of $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$, for a form $Q_0$ over
$\mathcal O_F$ and an arbitrary lattice $L$ on $F^n$ (any Steinitz class). -/
def IsLatRealization (t : LocTuple F n) (Q₀ : QuadForm (𝓞 F) n) (L : Lat F n) : Prop :=
  IsRealization S σ 𝕊 c t (formF Q₀) L

variable {S σ 𝕊 c}

theorem IsLatRealization.nondegenerate {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n} {L : Lat F n}
    (h : IsLatRealization S σ 𝕊 c t Q₀ L) : Q₀.Nondegenerate :=
  Tamagawa.nondegenerate_of_map h.1

/-- A free realization is a realization on the lattice $\mathcal O_F^n$. -/
theorem IsFreeRealization.isLatRealization {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n}
    (h : IsFreeRealization S σ 𝕊 c t Q₀) : IsLatRealization S σ 𝕊 c t Q₀ Lattices.stdLat := h

/-- **Every genus of $\mathrm{Gen}^*$ has a realization $(Q_0\otimes F, L)$ with $Q_0$ over $\mathcal O_F$** (every number field):
for a realization $(Q, L)$ choose $g\in\mathrm{GL}_n(F)$ and $Q_0$ with $Q_0\otimes F = Q\circ g$ (`exists_integral_model`); then
$(Q\circ g, g^{-1}L)$ realizes the same tuple (`locGenusOf_transport`, `detH_transport`). -/
theorem exists_latRealization {t : LocTuple F n} (ht : t ∈ GenStar S σ 𝕊 c) :
    ∃ p : QuadForm (𝓞 F) n × Lat F n, IsLatRealization S σ 𝕊 c t p.1 p.2 := by
  obtain ⟨⟨Q, L⟩, hQ, hL, hσ, hS, hprim, hc, ht⟩ := (mem_genStar_iff S σ 𝕊 c t).mp ht
  dsimp only at hQ hL hσ hS hprim hc ht
  obtain ⟨g, Q₀, hform⟩ := exists_integral_model Q
  refine ⟨(Q₀, Lat.image g⁻¹ L), ?_⟩
  unfold IsLatRealization
  dsimp only
  rw [hform]
  refine ⟨hessian_det_compMat_ne Q g hQ, isIntegral_transport Q g hL, hasSignature_compMat Q g hσ, ?_, ?_, ?_, ?_⟩
  · rw [detH_transport Q g hQ L]; exact hS
  · intro v; rw [locGenusOf_transport Q g v L hL]; exact hprim v
  · intro v hv; rw [locGenusOf_transport Q g v L hL]; exact hc v hv
  · funext v; rw [locGenusOf_transport Q g v L hL]; exact congrFun ht v

/-! ### Theorem 6.2 for one genus, every lattice -/

/-- **Theorem 6.2 for one genus, every lattice** (any signature, $n\ge3$, every number field): if $(Q_0\otimes F, L)$ realizes
$t\in\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$, with $L$ any lattice (any Steinitz class), then
$$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{t_{\mathfrak p},\mathfrak p}(t_{\mathfrak p})^{-1};$$
in particular $\mathrm{Mass}^+(L)$ depends only on the genus $t$. -/
@[kb "hanke2011structure" "Thm. 6.2, pp. 25–26 (one genus, every lattice, any signature, tuple of local genera)"]
theorem massPlusLat_of_realization (hn : 3 ≤ n) {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n} {L : Lat F n}
    (h : IsLatRealization S σ 𝕊 c t Q₀ L) :
    massPlusLat Q₀ h.nondegenerate L = ENNReal.ofReal (massPlusConst σ S * invDensityTuple t) := by
  have hQ₀ := h.nondegenerate
  obtain ⟨hQ, hL, hσ, hS, -, -, ht⟩ := h
  rw [massPlusLat_eq_local hn Q₀ hQ₀ hQ L hL]
  congr 1
  have hβ : (∏' v, (locGenusOf v (formF Q₀) L hL).beta)⁻¹ = invDensityTuple t := by
    rw [← ht]
    classical
    show _ = if Multipliable (fun v => ((locGenusOf v (formF Q₀) L hL).beta)⁻¹) then
      ∏' v, ((locGenusOf v (formF Q₀) L hL).beta)⁻¹ else 0
    exact inv_tprod_eq_ite (fun v => (beta_locGenusOf_pos v (formF Q₀) hQ L hL).ne')
      (multipliable_beta_locGenusOf' hn Q₀ hQ₀ L hL)
  rw [hβ, hS, constC_eq_sigConst Q₀ hQ₀ hσ]
  rfl

/-! ### The proper mass of a genus -/

open Classical in
/-- **The proper mass $\mathrm{Mass}^+(G)$ of a genus** (Def. 6.1, p. 25), for a tuple $t$ of local genera: $\mathrm{Mass}^+(L)$
(`massPlusLat`) of a chosen realization $(Q_0\otimes F, L)$ of $t$, $Q_0$ over $\mathcal O_F$, $L$ any lattice; $0$ if there is
none. By `massPlusOfGenus_eq_massPlusLat` it does not depend on the choice, and every $t\in\mathrm{Gen}^*$ has a realization
(`exists_latRealization`). -/
@[kb "hanke2011structure" "Def. 6.1, p. 25 (Mass⁺(G), every genus)"]
def massPlusOfGenus (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) (t : LocTuple F n) : ℝ≥0∞ :=
  if h : ∃ p : QuadForm (𝓞 F) n × Lat F n, IsLatRealization S σ 𝕊 c t p.1 p.2 then
    massPlusLat h.choose.1 h.choose_spec.nondegenerate h.choose.2
  else 0

theorem massPlusOfGenus_eq (hn : 3 ≤ n) {t : LocTuple F n}
    (h : ∃ p : QuadForm (𝓞 F) n × Lat F n, IsLatRealization S σ 𝕊 c t p.1 p.2) :
    massPlusOfGenus S σ 𝕊 c t = ENNReal.ofReal (massPlusConst σ S * invDensityTuple t) := by
  unfold massPlusOfGenus
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact massPlusLat_of_realization hn h.choose_spec

/-- **$\mathrm{Mass}^+(G)$ is $\mathrm{Mass}^+(L)$ of any realization** $(Q_0\otimes F, L)$ of the genus. -/
theorem massPlusOfGenus_eq_massPlusLat (hn : 3 ≤ n) {t : LocTuple F n} {Q₀ : QuadForm (𝓞 F) n} {L : Lat F n}
    (h : IsLatRealization S σ 𝕊 c t Q₀ L) : massPlusOfGenus S σ 𝕊 c t = massPlusLat Q₀ h.nondegenerate L := by
  rw [massPlusOfGenus_eq hn ⟨(Q₀, L), h⟩, massPlusLat_of_realization hn h]

/-- **Comparison with the free definition**: when $t$ has a realization on $\mathcal O_F^n$, `massPlusOfGenus` is the library's
`massPlusOfTuple`. -/
theorem massPlusOfGenus_eq_massPlusOfTuple (hn : 3 ≤ n) {t : LocTuple F n}
    (h : ∃ Q₀, IsFreeRealization S σ 𝕊 c t Q₀) : massPlusOfGenus S σ 𝕊 c t = massPlusOfTuple S σ 𝕊 c t := by
  obtain ⟨Q₀, hQ₀⟩ := h
  rw [massPlusOfGenus_eq hn ⟨(Q₀, Lattices.stdLat), hQ₀.isLatRealization⟩, massPlusOfTuple_eq hn ⟨Q₀, hQ₀⟩]

/-! ### Theorem 6.2 summed over all genera -/

/-- **Theorem 6.2 summed over the genera** (every number field $F$, every signature vector $\vec\sigma_\infty$, $n\ge3$;
unconditional, no hypothesis on the Steinitz classes):
$$\sum_{G\in\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)}\mathrm{Mass}^+(G) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot
\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S)$$
(the masses as real numbers; no finiteness of $\mathrm{Gen}^*$ is needed, the identity is termwise). -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (summed over the genera, every signature, every number field)"]
theorem theorem_6_2_summed_all (hn : 3 ≤ n) :
    ∑ᶠ t ∈ GenStar S σ 𝕊 c, (massPlusOfGenus S σ 𝕊 c t).toReal = massPlusConst σ S * totalMassT S σ 𝕊 c := by
  unfold totalMassT
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun t ht => ?_
  obtain ⟨p, hp⟩ := exists_latRealization ht
  rw [massPlusOfGenus_eq hn ⟨p, hp⟩, ENNReal.toReal_ofReal]
  refine mul_nonneg (massPlusConst_pos σ S).le (invDensityTuple_nonneg t fun v => ?_)
  obtain ⟨hQ, hL, -, -, -, -, ht'⟩ := hp
  rw [← ht']
  exact (beta_locGenusOf_pos v _ hQ _ hL).le

/-- **Theorem 6.2, (15), the paper's form** (every number field, every signature, $n\ge3$; $S$ globally rational with the
sign condition of Lemma 3.7, hypotheses `hα`, `hsign` as in `theorem_6_2_pid`):
$$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \frac{C_{\vec\sigma_\infty,n}}{2|\Delta_F|^{n(n-1)/4}}\cdot
\frac{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}\sum_{G\in\mathrm{Gen}^*}\mathrm{Mass}^+(G).$$ -/
@[kb "hanke2011structure" "Thm. 6.2, (15), p. 25 (M* form, every signature, every number field)"]
theorem theorem_6_2_all (hn : 3 ≤ n) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    totalMassM n S (epsInf σ) 𝕊 c =
      (massPlusConst σ S)⁻¹ * ∑ᶠ t ∈ GenStar S σ 𝕊 c, (massPlusOfGenus S σ 𝕊 c t).toReal := by
  rw [theorem_6_2_summed_all hn, ← mul_assoc, inv_mul_cancel₀ (massPlusConst_pos σ S).ne', one_mul,
    (lemma_3_7 (by omega) S σ 𝕊 c α hα hsign).2]

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.exists_latRealization
#print axioms QuadFormsKB.Hanke2011Structure.massPlusLat_of_realization
#print axioms QuadFormsKB.Hanke2011Structure.massPlusOfGenus_eq_massPlusLat
#print axioms QuadFormsKB.Hanke2011Structure.massPlusOfGenus_eq_massPlusOfTuple
#print axioms QuadFormsKB.Hanke2011Structure.theorem_6_2_summed_all
#print axioms QuadFormsKB.Hanke2011Structure.theorem_6_2_all
