/-
# The global Siegel Eisenstein series of degree $r$
**Layer:** local at each finite place $v$ of a number field $F$ (dyadic places included), then global over $F$.

**Setting.** $Q = \sum_{i<n}a_ix_i^2$, $n = 2m$ (0-based indices), $a_i \in F^\times$; the degree $r$;
$s_0 = m - \frac{r+1}2$ (`sZero`) and $\rho_r = \frac{r+1}2$ (`rhoR`). A *finite datum* is a family $\Phi = (\Phi_v)_v$,
$\Phi_v \in S(V_v^r) = S(M_{n\times r}(F_v))$, with $\Phi_v = \mathbf 1_{M_{n\times r}(\mathcal O_v)}$ (`oneSG`) for all but finitely many $v$.

**Results (local).**
* `secSR` (**the standard section**): $f_v(g, s) = f_{\Phi_v}(g)\,\|g\|_v^{-(s - s_0)}$, with $f_{\Phi_v}(g) = (\omega_v(g)\Phi_v)(0)$ (`secRV`) and
  the height $\|g\|_v$ of `htR`.
* `secSR_parabolic` (**$f_v(\cdot, s) \in I(s, \chi_V)$**): $f_v(n(B)m(A)g, s) = \chi_V(\det A)\,|\det A|_v^{s+\rho_r}f_v(g, s)$.
* `secSR_oneSG_of_good`: at a good place, $f_v(k, s) = 1$ for $\Phi_v = \mathbf 1_{L_v^r}$ and $k \in \mathrm{Sp}_{2r}(\mathcal O_v)$, every $s$.

**Results (global).**
* `finSecR` (**the finite section**): $f_f(\gamma, s) = \prod_{v<\infty}f_v(\gamma_v, s)$ for $\gamma \in \mathrm{Sp}_{2r}(F)$, a finite
  product (`hasFiniteMulSupport_secSR`), and its parabolic law `finSecR_parabolic`.
* `IsArchSectionR`: the parabolic law $f_\infty(n(B)m(A)\gamma) = \chi_{V,\infty}(\det A)\,|N(\det A)|^{s+\rho_r}f_\infty(\gamma)$ required of
  an archimedean section.
* `globalSecR_parabolic` (**left $P(F)$-invariance of the global section** $f(\gamma, s) = f_\infty(\gamma)f_f(\gamma, s)$; Hilbert reciprocity
  and the product formula, through `borelFactor_prod_eq_one` applied to $t = \det A$).
* `eisensteinR` (**the Siegel Eisenstein series of degree $r$**):
  $$E(g, s, \Phi) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f_\infty(\gamma, s)\prod_{v<\infty}f_v(\gamma_v, s).$$
For $r = 1$ these are `secS`, `finSecA`, `globalSecA`, `eisensteinA` (`SiegelWeil/EisensteinAdelic.lean`, at $g_f = 1$).

Sources: Kudla, *Some extensions of the Siegel–Weil formula* (2008), §1 [unverified]; Weil, *Sur la formule de Siegel dans la
théorie des groupes classiques*, Acta Math. 113 (1965), Ch. II [unverified]; Kudla–Rallis, J. reine angew. Math. 387 (1988), §1
[unverified].
-/
import QuadFormsKB.SiegelWeil.Eisenstein
import QuadFormsKB.SiegelWeil.Forms.EisensteinSpherical

open IsDedekindDomain NumberField MeasureTheory Filter Matrix
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

/-- $s_0 = m - \frac{r+1}2$, the point where the section $f_\Phi$ lies in $I(s_0, \chi_V)$ ($n = 2m$). -/
def sZero (m r : ℕ) : ℂ := (m : ℂ) - ((r : ℂ) + 1) / 2

/-- $\rho_r = \frac{r+1}2$. -/
def rhoR (r : ℕ) : ℂ := ((r : ℂ) + 1) / 2

lemma blockA_spN_spM {k : Type*} [Field k] {r : ℕ} (B : Matrix (Fin r) (Fin r) k) (hB : Bᵀ = B) (A : GL (Fin r) k) :
    blockA (spN B hB * spM A) = (A : Matrix (Fin r) (Fin r) k) := by
  simp [blockA, spN_coe, spM_coe, fromBlocks_multiply]

/-! ### The local standard section -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F
variable (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-- **The standard section at a finite place**: $f_v(g, s) = f_{\Phi}(g)\,\|g\|_v^{-(s - s_0)}$, $f_\Phi = $ `secRV`, $\|g\|_v = $ `htR`. -/
@[kb "kudla2008" "§1 (the standard section $\\Phi(g, s) = \\Phi(g)|a(g)|^{s-s_0}$) [unverified]"]
def secSR (Φ : Sg (localDataV v) m r) (g : Sp r Fv) (s : ℂ) : ℂ :=
  secRV v a Φ g * ((htR v g : ℝ) : ℂ) ^ (-(s - sZero m r))

lemma htR_spN_spM_mul (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) (A : GL (Fin r) Fv) (g : Sp r Fv) :
    htR v (spN B hB * spM A * g) = ‖(A : Matrix (Fin r) (Fin r) Fv).det‖⁻¹ * htR v g := by
  rw [htR_mul_of_mem_siegelP' v (spN_spM_mem_siegelP B hB A), blockA_spN_spM]

lemma ofReal_inv_cpow {x : ℝ} (hx : 0 < x) (e : ℂ) : (((x⁻¹ : ℝ)) : ℂ) ^ e = (x : ℂ) ^ (-e) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

/-- **$f_v(\cdot, s) \in I(s, \chi_V)$**: $f_v(n(B)m(A)g, s) = \chi_V(\det A)\,|\det A|_v^{s+\rho_r}f_v(g, s)$. -/
@[kb "kudla2008" "§1 ($\\Phi(s) \\in I(s, \\chi_V)$) [unverified]"]
theorem secSR_parabolic (Φ : Sg (localDataV v) m r) (B : Matrix (Fin r) (Fin r) Fv) (hB : Bᵀ = B) (A : GL (Fin r) Fv)
    (g : Sp r Fv) (s : ℂ) :
    secSR v a Φ (spN B hB * spM A * g) s =
      (localDataV v).chiV a (A : Matrix (Fin r) (Fin r) Fv).det *
        ((‖(A : Matrix (Fin r) (Fin r) Fv).det‖ : ℝ) : ℂ) ^ (s + rhoR r) * secSR v a Φ g s := by
  have hd : (A : Matrix (Fin r) (Fin r) Fv).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have hpos : 0 < ‖(A : Matrix (Fin r) (Fin r) Fv).det‖ := norm_pos_iff.mpr hd
  unfold secSR
  rw [secRV_parabolic, htR_spN_spM_mul, md_eq_norm' v hd, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hpos.le) (htR_nonneg v g), ofReal_inv_cpow hpos]
  have hne : ((‖(A : Matrix (Fin r) (Fin r) Fv).det‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have e : ((‖(A : Matrix (Fin r) (Fin r) Fv).det‖ : ℝ) : ℂ) ^ (s + rhoR r) =
      ((‖(A : Matrix (Fin r) (Fin r) Fv).det‖ : ℝ) : ℂ) ^ m *
        ((‖(A : Matrix (Fin r) (Fin r) Fv).det‖ : ℝ) : ℂ) ^ (-(-(s - sZero m r))) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hne]
    congr 1; unfold sZero rhoR; ring
  rw [e]; ring

/-- **The unramified section is $1$ on $\mathrm{Sp}_{2r}(\mathcal O_v)$** at a good place, for every $s$. -/
theorem secSR_oneSG_of_good (hg : IsGoodV v a) (k : Sp r Fv) (hk : IsIntSp v k) (s : ℂ) :
    secSR v a (oneSG v m r) k s = 1 := by
  unfold secSR
  rw [secRV_eq, weilRepSpV_oneSG_of_good v a hg k hk, htR_eq_one_of_int v hk]
  simp [coe_oneSG, oneG, ptG, ballIndV]

end Local

/-! ### The finite section and the Eisenstein series -/

section Global

variable {F : Type} [Field F] [NumberField F] {m r : ℕ} (a : Fin (2 * m) → Fˣ)
  (Φ : ∀ v : HeightOneSpectrum (𝓞 F), Sg (localDataV v) m r) (hΦ : ∀ᶠ v in cofinite, Φ v = oneSG v m r)

/-- The image $\gamma_v$ of $\gamma \in \mathrm{Sp}_{2r}(F)$ in $\mathrm{Sp}_{2r}(F_v)$. -/
abbrev locSpV (v : HeightOneSpectrum (𝓞 F)) : Sp r F →* Sp r (v.adicCompletion F) :=
  locSp (algebraMap F (v.adicCompletion F))

/-- **The finite part of the global section**: $f_f(\gamma, s) = \prod_{v<\infty}f_v(\gamma_v, s)$, $f_v = $ `secSR` of $\Phi_v$. -/
@[kb "kudla2008" "§1 (the standard section $\\Phi(s) = \\otimes_v\\Phi_v(s)$) [unverified]"]
def finSecR (γ : Sp r F) (s : ℂ) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), secSR v (aV a v) (Φ v) (locSpV v γ) s

/-- The finite places where $V$ is not good, $\Phi_v \ne \mathbf 1_{L_v^r}$, or an entry of $\gamma$ is not $v$-integral. -/
def badR (γ : Sp r F) : Set (HeightOneSpectrum (𝓞 F)) :=
  badPlaces a 1 ∪ {v | Φ v ≠ oneSG v m r} ∪
    ⋃ x, ⋃ y, HeightOneSpectrum.Support (𝓞 F) (K := F) ((γ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) x y)

include hΦ in
lemma badR_finite (γ : Sp r F) : (badR a Φ γ).Finite :=
  ((badPlaces_finite a 1).union hΦ).union (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ =>
    HeightOneSpectrum.Support.finite (𝓞 F) _)

lemma isIntSp_of_not_badR {γ : Sp r F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badR a Φ γ) :
    IsIntSp v (locSpV v γ) := by
  intro x y
  simp only [badR, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hv
  rw [locSp_coe, map_apply]
  exact (norm_le_one_iff_valued v).mpr (valued_le_one_of_not_mem_support (hv.2 x y))

include hΦ in
lemma hasFiniteMulSupport_secSR (γ : Sp r F) (s : ℂ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => secSR v (aV a v) (Φ v) (locSpV v γ) s :=
  (badR_finite a Φ hΦ γ).subset fun v hv => by
    by_contra h
    apply hv
    have hgood := isGoodV_of_not_bad (γ := 1) a (fun h' => h (Or.inl (Or.inl h')))
    have hΦv : Φ v = oneSG v m r := by
      by_contra h'; exact h (Or.inl (Or.inr h'))
    simp only
    rw [hΦv]
    exact secSR_oneSG_of_good v _ hgood _ (isIntSp_of_not_badR a Φ h) s

lemma locSpV_spN_spM (v : HeightOneSpectrum (𝓞 F)) (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) :
    locSpV v (spN B hB * spM A) = spN (B.map (algebraMap F (v.adicCompletion F))) (by rw [← transpose_map, hB]) *
      spM (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A) := by
  rw [map_mul, locSp_spN, locSp_spM]

/-- $\det A \in F^\times$ for $A \in \mathrm{GL}_r(F)$. -/
def detU (A : GL (Fin r) F) : Fˣ := Matrix.GeneralLinearGroup.det A

lemma detU_coe (A : GL (Fin r) F) : ((detU A : Fˣ) : F) = (A : Matrix (Fin r) (Fin r) F).det := rfl

lemma det_map_GL (v : HeightOneSpectrum (𝓞 F)) (A : GL (Fin r) F) :
    ((Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) A : GL (Fin r) (v.adicCompletion F)) :
      Matrix (Fin r) (Fin r) (v.adicCompletion F)).det = algebraMap F _ (A : Matrix (Fin r) (Fin r) F).det := by
  rw [RingHom.map_det]; rfl

include hΦ in
/-- **The parabolic law of the finite section**: $f_f(n(B)m(A)\gamma, s) = \big(\prod_v\chi_{V,v}(\det A)|\det A|_v^{s+\rho_r}\big)f_f(\gamma, s)$
(place by place, `secSR_parabolic`; `borelFactorV` at $t = \det A$ and $s + \rho_r - 1$). -/
theorem finSecR_parabolic (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) (γ : Sp r F) (s : ℂ) :
    finSecR a Φ (spN B hB * spM A * γ) s =
      (∏ᶠ v, borelFactorV a (detU A) (s + rhoR r - 1) v) * finSecR a Φ γ s := by
  unfold finSecR
  rw [← finprod_mul_distrib (hasFiniteMulSupport_borelFactorV a (detU A) _)
    (hasFiniteMulSupport_secSR a Φ hΦ γ s)]
  congr 1; funext v
  rw [map_mul, locSpV_spN_spM, secSR_parabolic, det_map_GL, borelFactorV, detU_coe,
    show s + rhoR r - 1 + 1 = s + rhoR r by ring]

/-- **An archimedean section of degree $r$ at $s$**: $f_\infty : \mathrm{Sp}_{2r}(F) \to \mathbb C$ (standing for
$\gamma \mapsto f_\infty(\gamma g_\infty, s)$) with $f_\infty(n(B)m(A)\gamma) = \chi_{V,\infty}(\det A)\,|N(\det A)|^{s+\rho_r}f_\infty(\gamma)$. -/
def IsArchSectionR (fInf : Sp r F → ℂ) (s : ℂ) : Prop :=
  ∀ (B : Matrix (Fin r) (Fin r) F) (hB : Bᵀ = B) (A : GL (Fin r) F) (γ : Sp r F),
    fInf (spN B hB * spM A * γ) =
      (localDataInf (F := F)).chiV (aInf a) (mixedEmbedding F (A : Matrix (Fin r) (Fin r) F).det) *
        ((mixedEmbedding.norm (mixedEmbedding F (A : Matrix (Fin r) (Fin r) F).det) : ℝ) : ℂ) ^ (s + rhoR r) * fInf γ

/-- **The global section** $f(\gamma, s) = f_\infty(\gamma)\,f_f(\gamma, s)$ on $\mathrm{Sp}_{2r}(F)$. -/
def globalSecR (fInf : Sp r F → ℂ) (s : ℂ) (γ : Sp r F) : ℂ := fInf γ * finSecR a Φ γ s

include hΦ in
/-- **Left $P(F)$-invariance of the global section** (Hilbert reciprocity and the product formula, `borelFactor_prod_eq_one`
at $t = \det A$). -/
@[kb "kudla2008" "§1 ($\\Phi(\\gamma g, s) = \\Phi(g, s)$ for $\\gamma \\in P(F)$) [unverified]"]
theorem globalSecR_parabolic {fInf : Sp r F → ℂ} {s : ℂ} (hInf : IsArchSectionR a fInf s) {p : Sp r F}
    (hp : p ∈ siegelP r F) (γ : Sp r F) : globalSecR a Φ fInf s (p * γ) = globalSecR a Φ fInf s γ := by
  obtain ⟨B, hB, hpe⟩ := exists_spN_spM_of_mem_siegelP hp
  set A := levi hp
  unfold globalSecR
  rw [hpe, hInf, finSecR_parabolic a Φ hΦ]
  have := borelFactor_prod_eq_one a (detU A) (s + rhoR r - 1)
  rw [show s + rhoR r - 1 + 1 = s + rhoR r by ring, detU_coe] at this
  linear_combination (fInf γ * finSecR a Φ γ s) * this

include hΦ in
lemma globalSecR_lift {fInf : Sp r F → ℂ} {s : ℂ} (hInf : IsArchSectionR a fInf s) (g g' : Sp r F)
    (h : QuotientGroup.rightRel (siegelP r F) g g') : globalSecR a Φ fInf s g = globalSecR a Φ fInf s g' := by
  rw [QuotientGroup.rightRel_apply] at h
  have := globalSecR_parabolic a Φ hΦ hInf h g
  rw [inv_mul_cancel_right] at this
  exact this.symm

include hΦ in
/-- **The Siegel Eisenstein series of degree $r$**:
$$E(g, s, \Phi) = \sum_{\gamma\in P(F)\backslash\mathrm{Sp}_{2r}(F)}f_\infty(\gamma, s)\prod_{v<\infty}f_v(\gamma_v, s)$$
(`tsum`; $0$ if the series does not converge), for the finite datum $\Phi_f = \bigotimes_v\Phi_v$ and an archimedean section
$f_\infty$ (`IsArchSectionR`). -/
@[kb "kudla2008" "§1 ($E(g, s, \\Phi) = \\sum_{\\gamma\\in P(F)\\backslash G(F)}\\Phi(\\gamma g, s)$) [unverified]; weil1965 Ch. II [unverified]"]
def eisensteinR {fInf : Sp r F → ℂ} {s : ℂ} (hInf : IsArchSectionR a fInf s) : ℂ :=
  ∑' q : PQuot r F, Quotient.lift (globalSecR a Φ fInf s) (globalSecR_lift a Φ hΦ hInf) q

end Global

end QuadFormsKB.SiegelWeil.Forms
