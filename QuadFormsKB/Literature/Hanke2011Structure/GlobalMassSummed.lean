/-
# Hanke 2011, Corollary 6.3 (and 6.4, coefficientwise) summed over the genera, totally real $F$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, Theorem 6.2, Corollaries 6.3 and 6.4, pp. 25–27.

For $F$ totally real, $n \ge 3$, $S \in \mathrm{SqCl}(\mathbb A_{F,f}^\times, U_f)$, the totally positive definite signature
vector $\vec\sigma_\infty = ((n,0))_v$ (`totPosSig`), a set $\mathbb S$ of primes and Hasse invariants $\vec c_{\mathbb S}$:

* `massOfTuple` assigns to a tuple $t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ of local genera the mass
  `Lattices.mass Q L` of a chosen realization $(Q, L)$ ($Q$ a form over $F$, $L$ a lattice; $0$ outside $\mathrm{Gen}^*$).
* `massOfTuple_eq`: for $t \in \mathrm{Gen}^*$, `massOfTuple t` $= C(S)\cdot\prod_{\mathfrak p}\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$,
  in particular it does not depend on the chosen realization (`mass_eq_of_rep`, `massOfTuple_eq_mass`).
* **`sum_massOfTuple_eq`**: $\sum_{t \in \mathrm{Gen}^*}\mathrm{Mass}(t) = C(S)\,T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S)$ with
  $C(S) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot\frac{N(I(S))^{(n+1)/2}}{(2^{[F:\mathbb Q]})^{n(n+1)/2}}$.
* **`cor_6_3_summed`**: the same with $M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$ (Lemma 3.7, globally rational $S$), and the
  paper's form $M^* = C(S)^{-1}\sum\mathrm{Mass}$ (Cor. 6.3).

No finiteness of $\mathrm{Gen}^*$ is needed: the identity is termwise, so it holds for the `finsum`s as defined (a
`finsum` over an infinite support is $0$ on both sides). (In fact $\mathrm{Gen}^*$ is finite, but this is not used.)

The key step is the transport lemma of `GlobalMassSummedTransport.lean`: a realization $(Q, L)$ over $F$ is replaced by
$(Q\circ g, g^{-1}L)$ with $Q\circ g = Q_0 \otimes F$, $Q_0$ over $\mathcal O_F$, so that `mass_eq_local` applies.
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummedTransport

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **The constant of Corollary 6.3:**
$C(S) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{(2^{[F:\mathbb Q]})^{n(n+1)/2}}$
($N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$). -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (the constant)"]
def massConst (F : Type) [Field F] [NumberField F] (n : ℕ) (S : AdelicSqCl F) : ℝ :=
  |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
    normAssoc S ^ (((n : ℝ) + 1) / 2) / ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2)

theorem massConst_pos (S : AdelicSqCl F) : 0 < massConst F n S := by
  have hNS : 0 < normAssoc S := by
    unfold normAssoc
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun a b ha hb => mul_pos ha hb) fun v => ?_
    exact zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))) _
  have hV : 0 < volV n := by rw [volV_eq_tauR]; exact Hanke2005.tauR_pos n
  have hΔ : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  unfold massConst
  have := Real.rpow_pos_of_pos hNS (((n : ℝ) + 1) / 2)
  have := Real.rpow_pos_of_pos hΔ ((n : ℝ) * (n - 1) / 4)
  positivity

/-! ### The mass of one realization -/

section Core

variable [IsTotallyReal F]

/-- **Cor. 6.3 for a form over $\mathcal O_F$, in terms of the tuple of local genera.** -/
theorem mass_core (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hpd : IsTotallyPosDef (formF Q₀))
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral (formF Q₀) L.1) :
    Lattices.mass (formF Q₀) L = massConst F n (detH (formF Q₀) hQ L) *
      invDensityTuple (fun v => locGenusOf v (formF Q₀) L hL) := by
  have h := mass_eq_local hn Q₀ hpd hQ L hL
  have hQ₀ : Q₀.Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  have hmult := multipliable_beta_locGenusOf hn Q₀ hQ₀ L hL
  have hpos := mass_pos hpd L hL
  have hne : ∏' v, (locGenusOf v (formF Q₀) L hL).beta ≠ 0 := by
    intro h0
    rw [h0, _root_.inv_zero, mul_zero] at h
    exact hpos.ne' h
  have e : invDensityTuple (fun v => locGenusOf v (formF Q₀) L hL) =
      (∏' v, (locGenusOf v (formF Q₀) L hL).beta)⁻¹ := by
    unfold invDensityTuple
    dsimp only
    rw [if_pos (hmult.inv₀ hne), hmult.tprod_inv₀ hne]
  rw [e]
  exact h

/-- **The mass of any realization $(Q, L)$ over $F$** of a totally positive definite space with the totally positive
signature: $\mathrm{Mass}(Q, L) = C(\det_H L)\cdot\prod_{\mathfrak p}\beta_{G_\mathfrak p,\mathfrak p}(G_\mathfrak p)^{-1}$,
$G_\mathfrak p$ the local genera of $L$ (`invDensityTuple`). Proof: transport to an $\mathcal O_F$-model
(`GlobalMassSummedTransport.lean`) and `mass_core`. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (one genus, any realization over F)"]
theorem mass_of_rep (hn : 3 ≤ n) {Q : QuadForm F n} (hQ : Q.hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral Q L.1)
    (hσ : HasSignature Q (totPosSig F n)) :
    Lattices.mass Q L = massConst F n (detH Q hQ L) * invDensityTuple (fun v => locGenusOf v Q L hL) := by
  obtain ⟨g, Q₀, hQ₀⟩ := exists_integral_model Q
  have step : ∀ Q' : QuadForm F n, formF Q₀ = Q' → ∀ (hQ' : Q'.hessian.det ≠ 0) (L' : Lat F n)
      (hL' : IsIntegral Q' L'.1), IsTotallyPosDef Q' →
      Lattices.mass Q' L' = massConst F n (detH Q' hQ' L') * invDensityTuple (fun v => locGenusOf v Q' L' hL') := by
    intro Q' h
    subst h
    intro hQ' L' hL' hpd
    exact mass_core hn Q₀ hpd hQ' L' hL'
  have hpd : IsTotallyPosDef (Q.compMat g.val) :=
    isTotallyPosDef_of_hasSignature (hasSignature_compMat Q g hσ)
  have := step (Q.compMat g.val) hQ₀ (hessian_det_compMat_ne Q g hQ) (Lat.image g⁻¹ L)
    (isIntegral_transport Q g hL) hpd
  rw [mass_transport, detH_transport Q g hQ L] at this
  rw [this]
  congr 2
  funext v
  exact locGenusOf_transport Q g v L hL

end Core

/-! ### The mass of a tuple of local genera -/

variable (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
  (c : HeightOneSpectrum (𝓞 F) → ℤ)

/-- **$(Q, L)$ realizes the tuple $t$ of $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$:** $Q$ nondegenerate of
signature $\vec\sigma_\infty$, $L$ an integral lattice with $\det_H(L) = S$, primitive local genera with Hasse invariants
$c_\mathfrak p$ ($\mathfrak p \in \mathbb S$), and tuple of local genera $t$. -/
def IsRealization (t : LocTuple F n) (Q : QuadForm F n) (L : Lat F n) : Prop :=
  ∃ (hQ : Q.hessian.det ≠ 0) (hL : IsIntegral Q L.1), HasSignature Q σ ∧ detH Q hQ L = S ∧
    (∀ v, (locGenusOf v Q L hL).Prim) ∧ (∀ v ∈ 𝕊, (locGenusOf v Q L hL).hasse = c v) ∧
      (fun v => locGenusOf v Q L hL) = t

theorem mem_genStar_iff (t : LocTuple F n) :
    t ∈ GenStar S σ 𝕊 c ↔ ∃ p : QuadForm F n × Lat F n, IsRealization S σ 𝕊 c t p.1 p.2 := by
  constructor
  · rintro ⟨Q, hQ, L, hL, h⟩
    exact ⟨(Q, L), hQ, hL, h⟩
  · rintro ⟨⟨Q, L⟩, hQ, hL, h⟩
    exact ⟨Q, hQ, L, hL, h⟩

open Classical in
/-- **The mass of a tuple of local genera** $t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$: the mass
`Lattices.mass Q L` of a chosen realization $(Q, L)$ of $t$ (a form over $F$ and a lattice, `IsRealization`); $0$ if
$t \notin \mathrm{Gen}^*$. It does not depend on the choice (`mass_eq_of_realization`). -/
def massOfTuple (t : LocTuple F n) : ℝ :=
  if h : ∃ p : QuadForm F n × Lat F n, IsRealization S σ 𝕊 c t p.1 p.2 then
    Lattices.mass h.choose.1 h.choose.2
  else 0

section Sum

variable [IsTotallyReal F]

/-- **The mass of any realization of a tuple $t \in \mathrm{Gen}^*$** (totally positive signature) is
$C(S)\prod_\mathfrak p\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$: in particular any two realizations of $t$ have the same mass. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (independent of the realization)"]
theorem mass_eq_of_realization (hn : 3 ≤ n) {t : LocTuple F n} {Q : QuadForm F n} {L : Lat F n}
    (h : IsRealization S (totPosSig F n) 𝕊 c t Q L) :
    Lattices.mass Q L = massConst F n S * invDensityTuple t := by
  obtain ⟨hQ, hL, hσ, hS, -, -, rfl⟩ := h
  rw [mass_of_rep hn hQ L hL hσ, hS]

/-- **The mass of a tuple of local genera:** for $t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ with $\vec\sigma_\infty$
totally positive, `massOfTuple t` $= C(S)\prod_\mathfrak p\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$ (Cor. 6.3 for one genus). -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (one genus, tuple of local genera)"]
theorem massOfTuple_eq (hn : 3 ≤ n) {t : LocTuple F n} (ht : t ∈ GenStar S (totPosSig F n) 𝕊 c) :
    massOfTuple S (totPosSig F n) 𝕊 c t = massConst F n S * invDensityTuple t := by
  have h := (mem_genStar_iff S (totPosSig F n) 𝕊 c t).mp ht
  unfold massOfTuple
  rw [dif_pos h]
  exact mass_eq_of_realization S 𝕊 c hn h.choose_spec

/-- `massOfTuple t` is the mass of any realization of $t$. -/
theorem massOfTuple_eq_mass (hn : 3 ≤ n) {t : LocTuple F n} {Q : QuadForm F n} {L : Lat F n}
    (h : IsRealization S (totPosSig F n) 𝕊 c t Q L) :
    massOfTuple S (totPosSig F n) 𝕊 c t = Lattices.mass Q L := by
  rw [mass_eq_of_realization S 𝕊 c hn h,
    massOfTuple_eq S 𝕊 c hn ((mem_genStar_iff S _ 𝕊 c t).mpr ⟨(Q, L), h⟩)]

/-- **Corollary 6.3 summed over the genera** (totally real $F$, $n \ge 3$, totally positive definite signature
$\vec\sigma_\infty = ((n,0))_v$):
$$\sum_{t \in \mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)}\mathrm{Mass}(t) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}
\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{(2^{[F:\mathbb Q]})^{n(n+1)/2}}\cdot T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S).$$
No finiteness of $\mathrm{Gen}^*$ is assumed or needed (the summands are proportional termwise). -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (summed over the genera, totally real F)"]
theorem sum_massOfTuple_eq (hn : 3 ≤ n) :
    ∑ᶠ t ∈ GenStar S (totPosSig F n) 𝕊 c, massOfTuple S (totPosSig F n) 𝕊 c t =
      |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
        normAssoc S ^ (((n : ℝ) + 1) / 2) / ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) *
          totalMassT S (totPosSig F n) 𝕊 c := by
  show _ = massConst F n S * _
  unfold totalMassT
  rw [mul_finsum_mem]
  exact finsum_mem_congr rfl fun t ht => massOfTuple_eq S 𝕊 c hn ht

/-- **Corollary 6.3 summed over the genera, with $M^*$** (Lemma 3.7: $S$ globally rational,
$\rho_\mathfrak p(S_\mathfrak p) = \alpha$ at every prime, $\alpha$ a square at every real place):
$$\sum_{t \in \mathrm{Gen}^*}\mathrm{Mass}(t) = \frac{|\Delta_F|^{n(n-1)/4}}{V(n)^{[F:\mathbb Q]}}
\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}{(2^{[F:\mathbb Q]})^{n(n+1)/2}}\cdot M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S),\qquad
\varepsilon_\infty = \prod_{v\mid\infty}c_v((n,0)).$$ -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (summed over the genera, totally real F; M* form)"]
theorem sum_massOfTuple_eq_totalMassM (hn : 3 ≤ n) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenStar S (totPosSig F n) 𝕊 c, massOfTuple S (totPosSig F n) 𝕊 c t =
      |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / volV n ^ Module.finrank ℚ F *
        normAssoc S ^ (((n : ℝ) + 1) / 2) / ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) *
          totalMassM n S (epsInf (totPosSig F n)) 𝕊 c := by
  have h := lemma_3_7 (by omega) S (totPosSig F n) 𝕊 c α hα (fun w => by
    simpa [totPosSig] using hsign w)
  rw [← h.2]
  exact sum_massOfTuple_eq S 𝕊 c hn

/-- **Corollary 6.3, the paper's form** ($\vec\sigma_\infty$ totally definite, $S$ globally rational):
$$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \frac{V(n)^{[F:\mathbb Q]}}{|\Delta_F|^{n(n-1)/4}}\cdot
\frac{(2^{[F:\mathbb Q]})^{n(n+1)/2}}{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}\cdot\sum_{t \in \mathrm{Gen}^*}\mathrm{Mass}(t),$$
where $\sum_{t}\mathrm{Mass}(t) = \sum_{L \in \mathrm{Cls}^*}1/|\mathrm{Aut}(L)|$ (the mass of a genus is the sum of
$1/|O(M)|$ over its classes, `Lattices.mass`; $N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$). -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (M* in terms of the class sum)"]
theorem cor_6_3_summed (hn : 3 ≤ n) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    totalMassM n S (epsInf (totPosSig F n)) 𝕊 c =
      volV n ^ Module.finrank ℚ F / |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) / normAssoc S ^ (((n : ℝ) + 1) / 2) *
          ∑ᶠ t ∈ GenStar S (totPosSig F n) 𝕊 c, massOfTuple S (totPosSig F n) 𝕊 c t := by
  have h := sum_massOfTuple_eq_totalMassM S 𝕊 c hn α hα hsign
  have hC := massConst_pos (n := n) S
  have hC' : massConst F n S ≠ 0 := hC.ne'
  have e : volV n ^ Module.finrank ℚ F / |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) *
        ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) / normAssoc S ^ (((n : ℝ) + 1) / 2) =
      (massConst F n S)⁻¹ := by
    unfold massConst
    rw [inv_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_div]
    field_simp
  rw [e, h]
  unfold massConst at hC' ⊢
  rw [← mul_assoc, inv_mul_cancel₀ hC', one_mul]

end Sum

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.mass_of_rep
#print axioms QuadFormsKB.Hanke2011Structure.sum_massOfTuple_eq
#print axioms QuadFormsKB.Hanke2011Structure.sum_massOfTuple_eq_totalMassM
#print axioms QuadFormsKB.Hanke2011Structure.cor_6_3_summed
