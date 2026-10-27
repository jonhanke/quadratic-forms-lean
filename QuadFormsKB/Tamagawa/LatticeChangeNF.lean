/-
# $\tau(SO)$ for an arbitrary lattice, over every number field

**Layer:** a number field $F$ (any class number); a form $Q_0$ over $\mathcal O_F$ (the space $V = (F^n, Q_0)$); an **arbitrary**
$\mathcal O_F$-lattice $L$ on $V$ (`Lat F n`: any Steinitz class, not necessarily free, not necessarily of the form
$\mathfrak b\,\mathcal O_F^n$).

`LatChange.tauSO_smul_compMat` proved that the $\tau$ does not depend on the lattice, but only for free lattices
$g\,\mathcal O_F^n$ and only for $\mathcal O_F$ a PID (Smith normal form over $\mathcal O_F$). This file removes both restrictions.
The local ingredient is the $\alpha$ law at every prime (`alphaLaw_global`: local Smith normal form over
$\mathfrak o_\mathfrak p$, no global Smith form needed); the global ingredient is `mass_eq_mass_mul_relRatio`, which already holds for
any two lattices.

**Definitions.**
* `tamagawaKLat Q₀ L` $= \mu_{\mathrm{Tam}}(K_{SO}(L))$: the measure $\mu_{\mathrm{Tam}}(K_{SO}(\mathcal O_F^n))$ (`tamagawaK`) transported to the
  stabilizer of $L$ by the Haar property, $\mu(K(L)) = \mu(K(\mathcal O_F^n))\cdot r(K(L), K(\mathcal O_F^n))$,
  $r(A, B) = [A : A\cap B]/[B : A\cap B]$ (`relRatio`).
* `tauSOLat Q₀ L` $= \mu_{\mathrm{Tam}}(K_{SO}(L))\cdot 2\,\mathrm{Mass}(L)$, the $\tau$ computed with $L$ ($2\,\mathrm{Mass} = \mathrm{mass}_{SO}$,
  `mass_SO_eq_two_mul_mass`).

**Proves** (all without `IsPrincipalIdealRing`):
* **`tamagawaKLat_eq_local`**: $\mu_{\mathrm{Tam}}(K_{SO}(L))$ is the product of the local gauge-form volumes **of $L$**:
  $$\mu(K_{SO}(L)) = |d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0\circ P_\mathfrak p)\,
    \|\det P_\mathfrak p\|_\mathfrak p^{n+1}$$
  for any local bases $L_\mathfrak p = P_\mathfrak p\,\mathfrak o_\mathfrak p^n$, $P_\mathfrak p \in M_n(\mathfrak o_\mathfrak p)$ (i.e. $L \subseteq \mathcal O_F^n$), i.e. Weil's
  $\mu(O(L_\mathfrak p)) \propto \alpha_\mathfrak p(L_\mathfrak p)\,|\det L_\mathfrak p|^{(n+1)/2}$ with the ambient real volumes;
* **`tauSOLat_eq_tauSO`**: $\tau$ computed with any integral lattice $L$ is $\tau(Q_0)$;
* **`tauSO_compMat_nf`**, **`tauSO_smul_compMat_nf`**: $\tau(c\,(Q_0\circ G)) = \tau(Q_0)$ for every $G \in M_n(\mathcal O_F)$, $\det G \ne 0$,
  any number field (the theorem without the PID);
* `tamagawaNumberTwo_compMat_iff_nf`, `tamagawaNumberTwo_iff_of_similar_nf`: $\tau = 2$ is a property of the similarity class of
  the $F$-space $V$;
* **`massFormula_lat_nf`**, `massFormula_lat_local_nf`: the mass formula for the genus of an arbitrary integral lattice $L$,
  $\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}$, given $\tau(Q_0) = 2$.

Sources: Weil 1982, §2.2.1, p. 14 (local measures are independent of the coordinates), Thm. 2.3.1, pp. 21–22 (product formula),
§2.4, p. 22, §3.4 [unverified] (Haar measures of lattice stabilizers); O'Meara 1963, §81B–C, 81:5–81:8, pp. 212–213 (81:5 is the Steinitz form $L = \mathfrak o x_1 + \dots + \mathfrak a x_n$).
-/
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Tamagawa.TernaryReduction

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.LatChange

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The measure and $\tau$ of an arbitrary lattice -/

/-- **$\mu_{\mathrm{Tam}}(K_{SO}(L))$ for an arbitrary lattice $L$ on $V = (F^n, Q_0)$**: the $\mu_{\mathrm{Tam}}(K_{SO}(\mathcal O_F^n))$ times
$r(K(L), K(\mathcal O_F^n)) = \mu(K(L))/\mu(K(\mathcal O_F^n))$ (the Haar property of the combinatorial measure). That this is the
product of the local volumes of $L$ is `tamagawaKLat_eq_local`. -/
def tamagawaKLat (Q₀ : QuadForm (𝓞 F) n) (L : Lat F n) : ℝ :=
  tamagawaK Q₀ * relRatio (locStab (Q₀.map (algebraMap (𝓞 F) F)) L)
    (locStab (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n))

/-- **The $\tau(SO(V))$ computed with an arbitrary lattice $L$**:
$\mu_{\mathrm{Tam}}(K_{SO}(L))\cdot\mathrm{mass}_{SO}(L)$ with
$\mathrm{mass}_{SO}(L) = 2\,\mathrm{Mass}(L)$ (each $O$-class is two $SO$-classes or one with an improper automorphism; the
`mass_SO_eq_two_mul_mass`, written out here in the $O$-form). -/
def tauSOLat (Q₀ : QuadForm (𝓞 F) n) (L : Lat F n) : ℝ :=
  tamagawaKLat Q₀ L * (2 * mass (Q₀.map (algebraMap (𝓞 F) F)) L)

theorem relRatio_symm' {G : Type*} [Group G] (A B : Subgroup G) : relRatio B A = (relRatio A B)⁻¹ := by
  simp [relRatio, inv_div]

theorem tamagawaKLat_std (Q₀ : QuadForm (𝓞 F) n) : tamagawaKLat Q₀ (stdLat F n) = tamagawaK Q₀ := by
  simp [tamagawaKLat, relRatio_self]

theorem tauSOLat_std (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : tauSOLat Q₀ (stdLat F n) = tauSO Q₀ := by
  unfold tauSOLat tauSO
  rw [tamagawaKLat_std, mass_SO_eq_two_mul_mass Q₀ hQ₀ hn hpd (isIntegral_std Q₀)]

/-- **$\tau$ does not depend on the lattice** (any number field, any lattice $L$ on $V$, integral for $Q_0$; in particular any
Steinitz class): $\tau(SO(V))$ computed with $L$ equals $\tau(Q_0)$ (computed with $\mathcal O_F^n$).
*Proof:* $\mathrm{Mass}(L) = \mathrm{Mass}(\mathcal O_F^n)\,r(K(\mathcal O_F^n), K(L))$ (`mass_eq_mass_mul_relRatio`, any two
lattices) and $r(K(L), K(\mathcal O_F^n))\,r(K(\mathcal O_F^n), K(L)) = 1$. -/
@[kb "weil1982" "§2.4, p. 22 (the Tamagawa measure does not depend on choices); §3.4 [unverified]"]
theorem tauSOLat_eq_tauSO (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (L : Lat F n)
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) L.1) : tauSOLat Q₀ L = tauSO Q₀ := by
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  rw [← tauSOLat_std Q₀ hQ₀ hn hpd]
  unfold tauSOLat tamagawaKLat
  rw [mass_eq_mass_mul_relRatio hpd (stdLat F n) L (isIntegral_std Q₀) hLi, relRatio_self]
  have hc := commensurable_locStab QF (stdLat F n) L
  have h1 : relRatio (locStab QF L) (locStab QF (stdLat F n)) *
      relRatio (locStab QF (stdLat F n)) (locStab QF L) = 1 :=
    relRatio_mul_relRatio_symm ⟨hc.2.relIndex_ne_zero, hc.1.relIndex_ne_zero⟩
  linear_combination (tamagawaK Q₀ * 2 * mass QF (stdLat F n)) * h1

/-! ### The measure of $K(L)$ from the local densities of $L$ -/

section Local


/-- The local factor of $\mu(K_{SO}(L))$ at $\mathfrak p$, for a local basis $L_\mathfrak p = P\,\mathfrak o_\mathfrak p^n$:
$\tfrac12\beta_\mathfrak p(Q_0\circ P, Q_0\circ P)\,\|\det P\|_\mathfrak p^{n+1}$ ($= \mathrm{vol}(SO(L_\mathfrak p))$ for the gauge form of $Q_0$ in the
coordinates of $\mathcal O_F^n$). -/
def latLocalFactor (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)
    (P : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) : ℝ :=
  (1 / 2 : ℝ) * DVR.localDensityForm ((NF.Qp v Q₀).compMat P) ((NF.Qp v Q₀).compMat P) (NF.π v) *
    ‖((P.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ ^ (n + 1)

/-- **The local factor is $\alpha_\mathfrak p(\mathcal O_F^n)$ times the local index ratio** (the $\alpha$ law at every prime,
`alphaLaw_global`): $\tfrac12\beta(Q_0\circ P)\|\det P\|^{n+1} = \alpha_\mathfrak p(Q_0)\cdot r(K(P\mathfrak o^n), K(\mathfrak o^n))$. -/
theorem latLocalFactor_eq (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (P : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) (hP : P.det ≠ 0) :
    latLocalFactor v Q₀ P = NF.siegelDensity v Q₀ Q₀ *
      relRatio (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)))
          (locAct v (glOf v P hP) (std v)))
        (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) (std v)) := by
  have h := alphaLaw_global v Q₀ hQ₀ P hP
  unfold AlphaLawAt at h
  unfold latLocalFactor
  simp only [NF.siegelDensity, ite_true, NF.localDensityForm_eq_completion]
  linear_combination (-(1 / 2 : ℝ)) * h

/-- The local index ratio in the global notation. -/
theorem relRatio_stab_eq_KL (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)
    (Λ : Submodule (v.adicCompletionIntegers F) (Fin n → v.adicCompletion F)) :
    relRatio (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype Λ)
        (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) =
      relRatio (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) Λ)
        (KL v ((NF.Qp v Q₀).map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) (std v)) := by
  rw [map_Qp_eq, ← stabLat_map_subtype_eq_KL, ← stdStab_map_subtype_eq_KL,
    relRatio_map (Subgroup.subtype_injective _)]

/-- **$\mu_{\mathrm{Tam}}(K_{SO}(L))$ is the product of the local volumes of $L$** (any number field, any lattice $L \subseteq \mathcal O_F^n$
given by local bases $L_\mathfrak p = P_\mathfrak p\,\mathfrak o_\mathfrak p^n$, $n \ne 0, 2$):
$$\mu(K_{SO}(L)) = |d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0\circ P_\mathfrak p)\,\|\det P_\mathfrak p\|^{n+1}.$$
*Proof:* the local factor is $\alpha_\mathfrak p(Q_0)\,r_\mathfrak p$ (`latLocalFactor_eq`), $r_\mathfrak p = 1$ where $L_\mathfrak p = \mathfrak o_\mathfrak p^n$, and
$\prod_\mathfrak p r_\mathfrak p = r(K(L), K(\mathcal O_F^n))$ (`relRatio_locStab_eq_prod`, the restricted product). -/
@[kb "weil1982" "§2.2.1, p. 14; §2.3, p. 21; §3.4 (μ(O(L_p)) ∝ α_p(L_p)|det L_p|^((n+1)/2)) [unverified]"]
theorem tamagawaKLat_eq_local (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (L : Lat F n) (P : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))
    (hP : ∀ v, (P v).det ≠ 0) (hL : ∀ v, loc v L.1 = locAct v (glOf v (P v) (hP v)) (std v)) :
    tamagawaKLat Q₀ L = (|(discr F : ℝ)|) ^ (-((n : ℝ) * (n - 1) / 4)) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) * ∏' v, latLocalFactor v Q₀ (P v) := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    relRatio (stabLat v (orthGroup QF (v.adicCompletion F)).subtype (loc v L.1)) (stdStab QF v)
  have hSfin : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  set S := hSfin.toFinset
  have hS : ∀ v ∉ S, loc v L.1 = std v := fun v hv => by
    by_contra h; exact hv (hSfin.mem_toFinset.mpr h)
  have hr1 : ∀ v ∉ S, r v = 1 := fun v hv => by
    simp only [r]; rw [hS v hv, ← stdStab_eq_stabLat, relRatio_self]
  -- the global ratio is the finite product of the local ones
  have hR : relRatio (locStab QF L) (locStab QF (stdLat F n)) = ∏ v ∈ S, r v := by
    rw [relRatio_symm', relRatio_locStab_eq_prod QF L S hS, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun v _ => (relRatio_symm' _ _).symm
  -- the local factors
  have hfac : ∀ v, latLocalFactor v Q₀ (P v) = NF.siegelDensity v Q₀ Q₀ * r v := fun v => by
    rw [latLocalFactor_eq v Q₀ hQ₀ (P v) (hP v), ← hL v]
    simp only [r]; rw [relRatio_stab_eq_KL]
  have hrm : Multipliable r := multipliable_of_ne_finset_one hr1
  have hsm := multipliable_siegelDensity hn0 hn2 Q₀ hQ₀
  rw [show (fun v => latLocalFactor v Q₀ (P v)) = fun v => NF.siegelDensity v Q₀ Q₀ * r v from funext hfac,
    hsm.tprod_mul hrm, tprod_eq_prod hr1]
  unfold tamagawaKLat tamagawaK
  rw [hR]; ring

end Local

/-! ### $\tau(c\,(Q_0\circ G)) = \tau(Q_0)$ without the PID -/

section Change

/-- $G$ as an element of $\mathrm{GL}_n(F)$. -/
def glF (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0) : GL (Fin n) F :=
  Matrix.nonsingInvUnit (G.map (algebraMap (𝓞 F) F)) (isUnit_iff_ne_zero.mpr (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG))

theorem glF_val (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0) :
    (glF G hG).val = G.map (algebraMap (𝓞 F) F) := rfl

theorem det_map_ι_ne_zero (v : HeightOneSpectrum (𝓞 F)) {G : Matrix (Fin n) (Fin n) (𝓞 F)} (hG : G.det ≠ 0) :
    (G.map (NF.ι v)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  intro h
  apply hG
  have hinj : Function.Injective (NF.ι v) := by
    intro x y hxy
    apply RingOfIntegers.coe_injective
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hxy
    simpa using this
  exact hinj (by rw [h, map_zero])

theorem loc_image_glF (v : HeightOneSpectrum (𝓞 F)) (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0) :
    loc v (Lat.image (glF G hG) (stdLat F n)).1 = locAct v (glOf v (G.map (NF.ι v)) (det_map_ι_ne_zero v hG)) (std v) := by
  show loc v (glImage _ intVec) = _
  rw [loc_glImage, loc_intVec]
  congr 1
  ext a b
  rfl

theorem detGram_compMat (Q₀ : QuadForm (𝓞 F) n) (G : Matrix (Fin n) (Fin n) (𝓞 F)) (σ : F →ₐ[ℚ] ℂ) :
    detGram (Q₀.compMat G) σ = ‖σ (algebraMap (𝓞 F) F G.det)‖ ^ 2 * detGram Q₀ σ := by
  simp only [detGram, hessian_compMat, det_mul, det_transpose, map_mul, map_div₀, norm_mul, norm_div]
  ring

/-- **$\mu_{\mathrm{Tam}}(K_{SO})$ of the form $Q_0\circ G$ is $\mu_{\mathrm{Tam}}(K_{SO}(G\mathcal O_F^n))$ for $Q_0$**: the local factors are those of
the local bases $P_\mathfrak p = G$ (`tamagawaKLat_eq_local`), and the Jacobians $\|\det G\|_\mathfrak p^{n+1}$ cancel the archimedean
change $\prod_\sigma|\sigma(\det G)|^{-(n+1)}$ by the product formula. -/
theorem tamagawaK_compMat_eq (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0) :
    tamagawaK (Q₀.compMat G) = tamagawaKLat Q₀ (Lat.image (glF G hG) (stdLat F n)) := by
  classical
  have hQG : (Q₀.compMat G).Nondegenerate := nondegenerate_compMat_of_det hQ₀ hG
  rw [tamagawaKLat_eq_local hn0 hn2 Q₀ hQ₀ _ (fun v => G.map (NF.ι v)) (fun v => det_map_ι_ne_zero v hG)
    (fun v => loc_image_glF v G hG)]
  set x : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F G.det)‖
  have hfac : ∀ v, latLocalFactor v Q₀ (G.map (NF.ι v)) = NF.siegelDensity v (Q₀.compMat G) (Q₀.compMat G) *
      x v ^ (n + 1) := fun v => by
    unfold latLocalFactor
    have e1 : (NF.Qp v Q₀).compMat (G.map (NF.ι v)) = NF.Qp v (Q₀.compMat G) := map_compMat _ _ _
    have e2 : ‖(((G.map (NF.ι v)).det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = x v := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e1, e2]
    simp only [NF.siegelDensity, ite_true, NF.localDensityForm_eq_completion]
  -- the Jacobians: `x v = 1` off a finite set, `∏ x v⁻¹ = ∏ σ |σ det G|`
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | G.det ∈ v.asIdeal}.Finite := by
    have h_span_nezero : Ideal.span {G.det} ≠ 0 := by simp [hG]
    simp only [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  set T := hTfin.toFinset
  have hx1 : ∀ v ∉ T, x v = 1 := fun v hv =>
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v G.det).mpr (fun h => hv (hTfin.mem_toFinset.mpr h))
  have hxpow1 : ∀ v ∉ T, x v ^ (n + 1) = 1 := fun v hv => by rw [hx1 v hv, one_pow]
  have hxinv1 : ∀ v ∉ T, (x v)⁻¹ = 1 := fun v hv => by rw [hx1 v hv, inv_one]
  have hN := tprod_norm_inv hG
  rw [tprod_eq_prod hxinv1] at hN
  set Nd := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ (algebraMap (𝓞 F) F G.det)‖
  have hsm := multipliable_siegelDensity hn0 hn2 _ hQG
  rw [show (fun v => latLocalFactor v Q₀ (G.map (NF.ι v))) = fun v =>
      NF.siegelDensity v (Q₀.compMat G) (Q₀.compMat G) * x v ^ (n + 1) from funext hfac,
    hsm.tprod_mul (multipliable_of_ne_finset_one hxpow1), tprod_eq_prod hxpow1]
  have hxT : ∏ v ∈ T, x v ^ (n + 1) = (Nd ^ (n + 1))⁻¹ := by
    rw [← hN, Finset.prod_inv_distrib, inv_pow, inv_inv, Finset.prod_pow]
  rw [hxT]
  -- the archimedean factors
  have hpos : ∀ σ : F →ₐ[ℚ] ℂ, 0 < ‖σ (algebraMap (𝓞 F) F G.det)‖ := fun σ =>
    norm_pos_iff.mpr ((map_ne_zero σ).mpr (coe_ne_zero hG))
  have hσ : ∀ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram (Q₀.compMat G) σ) =
      (‖σ (algebraMap (𝓞 F) F G.det)‖ ^ (n + 1))⁻¹ * archVolSO n (detGram Q₀ σ) := fun σ => by
    rw [detGram_compMat, archVolSO_mul n (d := detGram Q₀ σ) (by positivity) (norm_nonneg _)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos σ).le, ← Real.rpow_natCast, ← Real.rpow_neg (hpos σ).le]
    congr 1; push_cast; ring
  unfold tamagawaK
  rw [Finset.prod_congr rfl fun σ _ => hσ σ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow]
  ring

/-- **The $\tau(SO)$ is invariant under every integral change of lattice, over every number field** (the
`tauSO_smul_compMat` without `IsPrincipalIdealRing`, $c = 1$): $\tau(Q_0\circ G) = \tau(Q_0)$ for $G \in M_n(\mathcal O_F)$, $\det G \ne 0$
($n \ne 0, 2$, $Q_0$ totally positive definite).
*Proof:* $\mathrm{Mass}(Q_0\circ G, \mathcal O_F^n) = \mathrm{Mass}(Q_0, G\mathcal O_F^n)$ (`mass_similar`), $\mu(K_{SO})$ of $Q_0\circ G$ is
$\mu(K_{SO}(G\mathcal O_F^n))$ for $Q_0$ (`tamagawaK_compMat_eq`: the $\alpha$ law at every prime and the product formula), and
`tauSOLat_eq_tauSO`. No global Smith normal form is used. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), any class number"]
theorem tauSO_compMat_nf (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0) :
    tauSO (Q₀.compMat G) = tauSO Q₀ := by
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  set M : Lat F n := Lat.image (glF G hG) (stdLat F n)
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hQG : (Q₀.compMat G).Nondegenerate := nondegenerate_compMat_of_det hQ₀ hG
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdG : IsTotallyPosDef ((Q₀.compMat G).map (algebraMap (𝓞 F) F)) := by
    rw [← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF
  have hτG : tauSO (Q₀.compMat G) = tamagawaK (Q₀.compMat G) *
      (2 * mass ((Q₀.compMat G).map (algebraMap (𝓞 F) F)) (stdLat F n)) := by
    unfold tauSO; rw [mass_SO_eq_two_mul_mass _ hQG hn hpdG (isIntegral_std _)]
  have hmass : mass ((Q₀.compMat G).map (algebraMap (𝓞 F) F)) (stdLat F n) = mass QF M := by
    have e : (Q₀.compMat G).map (algebraMap (𝓞 F) F) = (1 : F) • QF.compMat (glF G hG).val := by
      rw [one_smul_form, glF_val, map_compMat]
    rw [e]; exact mass_similar QF one_ne_zero (glF G hG) _
  rw [hτG, hmass, tamagawaK_compMat_eq hn0 hn2 Q₀ hQ₀ G hG,
    ← tauSOLat_eq_tauSO Q₀ hQ₀ hn hpd M (isIntegral_image Q₀ G _ (glF_val G hG))]
  rfl

/-- **$\tau(c\,(Q_0\circ G)) = \tau(Q_0)$ over every number field** (`tauSO_smul_compMat` without the PID): for
$G \in M_n(\mathcal O_F)$, $\det G \ne 0$, and $c \in \mathcal O_F\setminus0$ with $c\,(Q_0\circ G)$ totally positive definite. -/
@[kb "weil1982" "§2.2.1, p. 14; Thm. 2.3.1, pp. 21-22; §2.4, p. 22 (independent of choices), any class number"]
theorem tauSO_smul_compMat_nf (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) {c : 𝓞 F} (hc : c ≠ 0)
    (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0)
    (hpd₁ : IsTotallyPosDef ((c • Q₀.compMat G).map (algebraMap (𝓞 F) F))) :
    tauSO (c • Q₀.compMat G) = tauSO Q₀ := by
  have hQG : (Q₀.compMat G).Nondegenerate := nondegenerate_compMat_of_det hQ₀ hG
  have hGF : (G.map (algebraMap (𝓞 F) F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hG
  have hpdG : IsTotallyPosDef ((Q₀.compMat G).map (algebraMap (𝓞 F) F)) := by
    rw [← map_compMat]; exact isTotallyPosDef_compMat_of_det hpd hGF
  have e : c • Q₀.compMat G = c • (Q₀.compMat G).compMat (diagonal fun _ => (1 : 𝓞 F)) := by
    rw [diagonal_one, compMat_one]
  rw [e] at hpd₁ ⊢
  rw [tauSO_smul_compMat_diagonal hn0 hn2 _ hQG hpdG hc _ (fun _ => one_ne_zero) hpd₁,
    tauSO_compMat_nf hn0 hn2 Q₀ hQ₀ hpd G hG]

/-- **$\tau = 2$ is invariant under integral change of lattice and rescaling**, any number field. -/
theorem tamagawaNumberTwo_smul_compMat_iff_nf (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n)
    (hQ₀ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) {c : 𝓞 F} (hc : c ≠ 0)
    (G : Matrix (Fin n) (Fin n) (𝓞 F)) (hG : G.det ≠ 0)
    (hpd₁ : IsTotallyPosDef ((c • Q₀.compMat G).map (algebraMap (𝓞 F) F))) :
    TamagawaNumberTwo (c • Q₀.compMat G) ↔ TamagawaNumberTwo Q₀ := by
  unfold TamagawaNumberTwo; rw [tauSO_smul_compMat_nf hn0 hn2 Q₀ hQ₀ hpd hc G hG hpd₁]

/-- **$\tau$ is an invariant of the similarity class of the $F$-space** (any number field): if
$c_1\,(Q_1\circ G_1) = c_0\,(Q_0\circ G_0)$ for integral $G_i$ with $\det G_i \ne 0$ and $c_i \ne 0$ (i.e. $(F^n, Q_0)$ and
$(F^n, Q_1)$ are similar: every similarity $Q_1 \sim t\,(Q_0\circ g)$, $g \in \mathrm{GL}_n(F)$, $t \in F^\times$, has this form after
clearing denominators), then $\tau(Q_1) = \tau(Q_0)$. -/
theorem tauSO_eq_of_similar_nf (hn0 : n ≠ 0) (hn2 : n ≠ 2) {Q₀ Q₁ : QuadForm (𝓞 F) n} (hQ₀ : Q₀.Nondegenerate)
    (hQ₁ : Q₁.Nondegenerate) (hpd₀ : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpd₁ : IsTotallyPosDef (Q₁.map (algebraMap (𝓞 F) F))) {c₀ c₁ : 𝓞 F} (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0)
    {G₀ G₁ : Matrix (Fin n) (Fin n) (𝓞 F)} (hG₀ : G₀.det ≠ 0) (hG₁ : G₁.det ≠ 0)
    (hpd : IsTotallyPosDef ((c₀ • Q₀.compMat G₀).map (algebraMap (𝓞 F) F)))
    (he : c₁ • Q₁.compMat G₁ = c₀ • Q₀.compMat G₀) : tauSO Q₁ = tauSO Q₀ := by
  rw [← tauSO_smul_compMat_nf hn0 hn2 Q₀ hQ₀ hpd₀ hc₀ G₀ hG₀ hpd,
    ← tauSO_smul_compMat_nf hn0 hn2 Q₁ hQ₁ hpd₁ hc₁ G₁ hG₁ (by rw [he]; exact hpd), he]

end Change

/-! ### The mass formula for an arbitrary lattice -/

section MassLat

/-- **The mass formula for the genus of an arbitrary lattice** (any number field, any Steinitz class): if $\tau(Q_0) = 2$ then
for every lattice $L$ on $V = (F^n, Q_0)$ integral for $Q_0$,
$$\mathrm{Mass}(L) = \sum_{\mathrm{cls}M\subseteq\mathrm{gen}L}\frac1{|O(M)|} = \mu_{\mathrm{Tam}}(K_{SO}(L))^{-1}.$$ -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice [unverified]"]
theorem massFormula_lat_nf (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hτ : TamagawaNumberTwo Q₀) (L : Lat F n)
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) L.1) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L = (tamagawaKLat Q₀ L)⁻¹ := by
  have h := tauSOLat_eq_tauSO Q₀ hQ₀ hn hpd L hLi
  unfold TamagawaNumberTwo at hτ
  rw [hτ] at h
  unfold tauSOLat at h
  have h1 : tamagawaKLat Q₀ L * mass (Q₀.map (algebraMap (𝓞 F) F)) L = 1 := by linarith
  exact eq_inv_of_mul_eq_one_right h1

/-- **The mass formula for an arbitrary lattice, with the local densities of $L$**: for $L \subseteq \mathcal O_F^n$ integral with local
bases $L_\mathfrak p = P_\mathfrak p\,\mathfrak o_\mathfrak p^n$ and $\tau(Q_0) = 2$ ($n \ne 0, 2$),
$$\mathrm{Mass}(L) = |d_F|^{n(n-1)/4}\Big(\prod_\sigma\mathrm{vol}(SO(V_\sigma))\Big)^{-1}\Big(\prod_\mathfrak p\tfrac12\beta_\mathfrak p(Q_0\circ P_\mathfrak p)\|\det P_\mathfrak p\|^{n+1}\Big)^{-1}.$$ -/
@[kb "kitaoka1993" "Thm 6.8.1 (mass formula), arbitrary lattice [unverified]"]
theorem massFormula_lat_local_nf (hn0 : n ≠ 0) (hn2 : n ≠ 2) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hτ : TamagawaNumberTwo Q₀) (L : Lat F n)
    (hLi : IsIntegral (Q₀.map (algebraMap (𝓞 F) F)) L.1)
    (P : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F))
    (hP : ∀ v, (P v).det ≠ 0) (hL : ∀ v, loc v L.1 = locAct v (glOf v (P v) (hP v)) (std v)) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L = ((|(discr F : ℝ)|) ^ (-((n : ℝ) * (n - 1) / 4)) *
      (∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ)) * ∏' v, latLocalFactor v Q₀ (P v))⁻¹ := by
  rw [massFormula_lat_nf Q₀ hQ₀ (Nat.pos_of_ne_zero hn0) hpd hτ L hLi,
    tamagawaKLat_eq_local hn0 hn2 Q₀ hQ₀ L P hP hL]

end MassLat

end QuadFormsKB.Tamagawa.LatChange

