/-
# Hanke 2011, Definition 6.1 and Theorem 6.2 for one genus, for every lattice (any Steinitz class, any signature)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Def. 6.1 and Theorem 6.2, pp. 25–26; Hanke 2005's mass
$\mathrm{Mass}(\Lambda,\varphi)$ [(5.4)–(5.6), Theorem 2.1] (bib key `hanke2005crelle`).

**Setting.** $F$ a number field of degree $d$, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $n$ variables of
**any signature**, $V = (F^n, Q)$ with $Q = Q_0\otimes F$ (`formF Q₀`), $L$ an **arbitrary** lattice on $V$ (`Lat F n`, any
Steinitz class; for the formulas $L$ is $\mathcal O_F$-valued, `IsIntegral`), $S = \det_H(L)$ (`detH`), $G_{\mathfrak p}$ the local
genus of $L_{\mathfrak p}$ (`locGenusOf`) with Hanke's local density $\beta_{G_\mathfrak p,\mathfrak p}(G_{\mathfrak p})$ (`LocGenus.beta`).

* **Definition 6.1 for $L$** (`massPlusLat Q₀ hQ L`): the proper mass $\mathrm{Mass}^+(L)$ is Hanke 2005's
  $\mathrm{Mass}(\Lambda,\varphi)$ [(5.4), in the form (5.6)] with $\Lambda = L$:
  $$\mathrm{Mass}^+(L) = \sum_{a\in SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)}\frac{\tau_a(\Gamma_a\backslash G_a)}{\mathrm{vol}_C(C_a)},$$
  $\Gamma_a = SO(M_a)$ the unit group of the class $a$ (`unitGroupLat`), $\tau_a$ Hanke's archimedean measure (`muArchHanke`)
  and $\mathrm{vol}_C(C_a) = \prod_w\mathrm{vol}_C(C_w)$ (`volCAt`); the archimedean data depend only on the space $V$. For
  $L = \mathcal O_F^n$ this is the library's `massPlus Q₀ hQ` (`massPlusLat_std`, by definition).
* **`massPlusLat_eq_relRatio_mul`** ($n\ge3$): $\mathrm{Mass}^+(L) = r(O(\hat{\mathcal O}_F^n), O(\hat L))\cdot\mathrm{Mass}^+(\mathcal O_F^n)$,
  $r(A,B) = [A:A\cap B]/[B:A\cap B]$, from $\operatorname{covol}(SO(V)(F)\backslash SO(V)(\mathbb A)) = \mu_f(SO(\hat L))\sum_a v(M_a)$
  for both lattices (`covolume_eq_muFin_KSOLat_mul_tsum`) and $\mu_f(SO(\hat L)) = r(O(\hat L), O(\hat{\mathcal O}_F^n))\,
  \mu_f(SO(\hat{\mathcal O}_F^n))$ (`muFin_KSOLat`).
* **`massPlusLat_eq_local`** (**Theorem 6.2 for one genus, every lattice**; $n\ge3$, every number field, every signature):
  $$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
  {N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1},$$
  $C_{\vec\sigma_\infty,n}$ = `constC Q₀`, $N_{F/\mathbb Q}(I(S))$ = `normAssoc S`, $N_{F/\mathbb Q}(2\mathcal O_F) = 2^d$.
  From Theorem 6.2 for $\mathcal O_F^n$ (`theorem_6_2_genus`) and the lattice-change identity
  $\mu_{\mathrm{Tam}}(K(L)) = |d_F|^{-n(n-1)/4}\prod_\sigma\mathrm{vol}(SO(V_\sigma))\prod_{\mathfrak p}\tfrac12\beta_{\mathfrak p}(Q\circ P_{\mathfrak p})
  \|\det P_{\mathfrak p}\|^{n+1}$ (`LatChange.tamagawaKLat_eq_local_gen`, $L_{\mathfrak p} = P_{\mathfrak p}\mathfrak o_{\mathfrak p}^n$).

All unconditional (standard axioms only; $\tau(SO(V)) = 2$ enters through `theorem_6_2_genus`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassLatIndex

namespace QuadFormsKB.Hanke2011Structure

open MeasureTheory Measure MulAction Set NumberField IsDedekindDomain Matrix
open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005 QuadFormsKB.HilbertModular QuadFormsKB.Siegel
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Definition 6.1 for every lattice -/

section Def

variable (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Definition 6.1 for an arbitrary lattice** (p. 25): the proper mass $\mathrm{Mass}^+(L)$ of a lattice $L$ on
$V = (F^n, Q_0\otimes F)$ (any Steinitz class) is Hanke's $\mathrm{Mass}(\Lambda,\varphi)$ [Hanke 2005, (5.4), in the form (5.6)]
with $\Lambda = L$:
$$\mathrm{Mass}^+(L) = \frac{\sum_a\tau_a(\Gamma_a\backslash G_a)}{\mathrm{vol}_C(C_a)},$$
the sum over the proper classes $a\in SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$ (`DCLat`), $\Gamma_a = SO(M_a)$
(`unitGroupLat`), $\tau_a$ = `muArchHanke Q₀ hQ` (Hanke §2, p. 5) and $\mathrm{vol}_C(C_a) = \prod_w\mathrm{vol}_C(C_w)$
(`volCAt`; these depend only on $V$). For $L = \mathcal O_F^n$ it is `massPlus Q₀ hQ` (`massPlusLat_std`). -/
@[kb "hanke2011structure" "Def. 6.1, p. 25 (Mass⁺(L) for every lattice L, via Hanke 2005 (5.4)–(5.6))"]
def massPlusLat (L : Lat F n) : ℝ≥0∞ :=
  (∑' i, covolume (unitGroupLat Q₀ L i) (GInfSO Q₀) (muArchHanke Q₀ hQ)) / ENNReal.ofReal (∏ w, volCAt Q₀ w)

/-- **For $L = \mathcal O_F^n$, `massPlusLat` is the library's `massPlus`** (definitionally: $SO(\hat L)$ is `KSO Q₀`). -/
theorem massPlusLat_std : massPlusLat Q₀ hQ (Tamagawa.stdLat F n) = massPlus Q₀ hQ := rfl

/-- $\tau_a(\Gamma_a\backslash G_a) = 2^{d\,n(n-1)/2}|d_F|^{n(n-1)/4}\,\mathrm{vol}(\Gamma_a\backslash G_a, \mu_\infty)$. -/
theorem covolume_unitGroupLat_muArchHanke (L : Lat F n) (i : DCLat Q₀ L) :
    covolume (unitGroupLat Q₀ L i) (GInfSO Q₀) (muArchHanke Q₀ hQ) =
      ENNReal.ofReal (archHankeConst F n) * covolume (unitGroupLat Q₀ L i) (GInfSO Q₀) (muArchTamSO Q₀ hQ) := by
  have := countable_GammaSOAdele Q₀
  have := countable_levelGroup (Γ := GammaSOAdele Q₀) (KSOLat Q₀ L) (dcRepLat Q₀ L i)
  unfold muArchHanke
  exact covolume_smul _ _ (by simpa using archHankeConst_pos (F := F) (n := n))

/-- **The unit volumes of the genus of $L$ and of $\mathcal O_F^n$** ($n \ge 3$, $L$ $\mathcal O_F$-valued):
$\sum_a v(M_a) = r(O(\hat{\mathcal O}_F^n), O(\hat L))\sum_i v(M_i)$, since both sums times $\mu_f$ of the stabilizer are the
covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$. -/
theorem tsum_covolume_unitGroupLat (hn : 3 ≤ n) (L : Lat F n) (hL : IsIntegral QF L.1) :
    ∑' i, covolume (unitGroupLat Q₀ L i) (GInfSO Q₀) (muArchTamSO Q₀ hQ) =
      ENNReal.ofReal (relRatio (locStab QF (Tamagawa.stdLat F n)) (locStab QF L)) * ∑' i, unitVolume Q₀ hQ i := by
  have h1 := covolume_eq_muFin_KSOLat_mul_tsum Q₀ hQ L
  rw [covolume_eq_muFin_mul_tsum_unitVolume Q₀ hQ, muFin_KSOLat Q₀ hQ (by omega) L hL, muFin_KSO] at h1
  set r := relRatio (locStab QF L) (locStab QF (Tamagawa.stdLat F n)) with hrdef
  have hf : 0 < finFactor Q₀ (fun _ => 1) := by
    rw [finFactor_one Q₀ hQ]; exact tprod_siegelDensity_pos hn Q₀ hQ
  have hr : 0 < r := relRatio_pos ⟨relIndex_locStab_ne_zero QF L (Tamagawa.stdLat F n),
    relIndex_locStab_ne_zero QF (Tamagawa.stdLat F n) L⟩
  rw [ENNReal.ofReal_mul hr.le, mul_comm (ENNReal.ofReal r), mul_assoc] at h1
  have h3 := (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hf).ne' ENNReal.ofReal_ne_top).mp h1
  rw [LatChange.relRatio_symm', ← hrdef, h3, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
    inv_mul_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul]

/-- **$\mathrm{Mass}^+(L) = r(O(\hat{\mathcal O}_F^n), O(\hat L))\cdot\mathrm{Mass}^+(\mathcal O_F^n)$** ($n\ge3$, $L$ an
$\mathcal O_F$-valued lattice on $V$, any signature): Hanke 2005's Lemma 6.1 in the indefinite setting. -/
@[kb "hanke2005crelle" "Lemma 6.1, p. 20 (Mass(Λ)/Mass(Λ') = vol(D'_h)/vol(D_h)), any signature"]
theorem massPlusLat_eq_relRatio_mul (hn : 3 ≤ n) (L : Lat F n) (hL : IsIntegral QF L.1) :
    massPlusLat Q₀ hQ L =
      ENNReal.ofReal (relRatio (locStab QF (Tamagawa.stdLat F n)) (locStab QF L)) * massPlus Q₀ hQ := by
  unfold massPlusLat massPlus hankeMass
  simp only [covolume_unitGroupLat_muArchHanke, ENNReal.tsum_mul_left, tsum_covolume_muArchHanke,
    tsum_covolume_unitGroupLat Q₀ hQ hn L hL]
  simp only [div_eq_mul_inv]
  ring

end Def

/-! ### Theorem 6.2 for one genus, every lattice -/

section Main

/-- $\|x\|_{\mathfrak p} = 1$ when $v_{\mathfrak p}(x) = 1$ (every number field). -/
theorem norm_algebraMap_eq_one_nf {v : HeightOneSpectrum (𝓞 F)} {x : F} (hx : v.valuation F x = 1) :
    ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  have hx0 : algebraMap F (v.adicCompletion F) x ≠ 0 := by
    intro h; rw [map_eq_zero_iff _ (algebraMap F _).injective] at h; rw [h, map_zero] at hx; exact zero_ne_one hx
  rw [LocalZeta.norm_eq_absNorm_pow v hx0, valued_algebraMap, hx, WithZero.log_one, zpow_zero]

/-- **The product formula** $\prod_{\mathfrak p}|x|_{\mathfrak p} = (\prod_\sigma|\sigma x|)^{-1}$ (every number field). -/
theorem finprod_norm_eq_nf (x : F) (hx : x ≠ 0) :
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

theorem localBeta_pos' (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) :
    0 < localBeta v Q₀ := by
  have hgform : localBeta v Q₀ = ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) *
      LocalDensity.NF.siegelDensity v Q₀ Q₀ := Hanke2005.hankeBeta_gramV v Q₀ hQ₀
  rw [hgform]
  have h2 : (0 : ℝ) < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  exact mul_pos (pow_pos h2 _) (Tamagawa.siegelDensity_pos v Q₀ hQ₀)

theorem multipliable_localBeta' (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) => localBeta v Q₀ := by
  have hm2 : Multipliable fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) :=
    multipliable_of_hasFiniteMulSupport (Hanke2005.hasFiniteMulSupport_norm_two.pow _)
  have hms := Tamagawa.multipliable_siegelDensity (by omega) (by omega) Q₀ hQ₀
  have e : (fun v : HeightOneSpectrum (𝓞 F) => localBeta v Q₀) = fun v =>
      ‖(2 : v.adicCompletion F)‖ ^ (n * (n - 1) / 2) * LocalDensity.NF.siegelDensity v Q₀ Q₀ :=
    funext fun v => Hanke2005.hankeBeta_gramV v Q₀ hQ₀
  rw [e]
  exact hm2.mul hms

/-- The local factor $\|2\|_{\mathfrak p}^{-k}\|\det P_{\mathfrak p}\|^{n+1}$ is $1$ at almost every prime (`finite_mulSupport_detFactor`,
without the totally real hypothesis). -/
theorem finite_mulSupport_detFactor' (L : Lat F n) (k : ℕ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(locBasis v L).val.det‖ ^ (n + 1)).Finite := by
  have h2 := (Hanke2005.hasFiniteMulSupport_norm_two (F := F))
  have hL : {v : HeightOneSpectrum (𝓞 F) | ¬ loc v L.1 = std v}.Finite :=
    Filter.eventually_cofinite.mp (loc_eventually_std L.2)
  refine (h2.union hL).subset fun v hv => ?_
  by_contra hn
  simp only [Set.mem_union, Function.mem_mulSupport, Set.mem_ofPred_eq, not_or, not_not] at hn
  apply hv
  have hstd : locAct v (locBasis v L) (std v) = std v := by rw [← locBasis_spec]; exact hn.2
  obtain ⟨P₀, hP₀⟩ := exists_gl_o_of_locAct_eq v hstd
  have hdet : ‖(locBasis v L).val.det‖ = 1 := by
    rw [← hP₀]
    show ‖(P₀.val.map (algebraMap _ (v.adicCompletion F))).det‖ = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Tamagawa.norm_coe_unit v (P₀.isUnit.map Matrix.detMonoidHom)
  show (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(locBasis v L).val.det‖ ^ (n + 1) = 1
  rw [hn.1, hdet, one_pow, one_pow, inv_one, one_mul]

/-- The local densities of the local genera of $L$ are multipliable ($n \ge 3$, every number field;
`multipliable_beta_locGenusOf` without the totally real hypothesis). -/
theorem multipliable_beta_locGenusOf' (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate) (L : Lat F n)
    (hL : IsIntegral (formF Q₀) L.1) : Multipliable fun v => (locGenusOf v (formF Q₀) L hL).beta := by
  classical
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => localBeta v Q₀ with hg
  have hgpos : ∀ v, 0 < g v := fun v => localBeta_pos' v Q₀ hQ₀
  have hgm : Multipliable g := multipliable_localBeta' hn Q₀ hQ₀
  have hev : ∀ᶠ v in Filter.cofinite, (locGenusOf v (formF Q₀) L hL).beta = g v := by
    filter_upwards [loc_eventually_std L.2] with v hv
    exact beta_locGenusOf_of_std v Q₀ L hL hv
  have hratio : Multipliable fun v => (locGenusOf v (formF Q₀) L hL).beta / g v := by
    refine multipliable_of_hasFiniteMulSupport ?_
    refine (Filter.eventually_cofinite.mp hev).subset fun v hv => ?_
    intro he
    apply hv
    show (locGenusOf v (formF Q₀) L hL).beta / g v = 1
    rw [he, div_self (hgpos v).ne']
  have e : (fun v => (locGenusOf v (formF Q₀) L hL).beta) =
      fun v => g v * ((locGenusOf v (formF Q₀) L hL).beta / g v) := by
    funext v; field_simp [(hgpos v).ne']
  rw [e]
  exact hgm.mul hratio

/-- **Theorem 6.2 for one genus, every lattice** (pp. 25–26; $n\ge3$, every number field $F$, every signature): for $Q_0$
nondegenerate over $\mathcal O_F$ and **any** $\mathcal O_F$-valued lattice $L$ on $V = (F^n, Q_0\otimes F)$ (any Steinitz class),
with $S = \det_H(L)$ and $G_{\mathfrak p}$ the local genus of $L_{\mathfrak p}$,
$$\mathrm{Mass}^+(L) = \frac{2|\Delta_F|^{n(n-1)/4}}{C_{\vec\sigma_\infty,n}}\cdot\frac{N_{F/\mathbb Q}(I(S))^{(n+1)/2}}
{N_{F/\mathbb Q}(2\mathcal O_F)^{n(n+1)/2}}\cdot\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$$
($\mathrm{Mass}^+(L)$ = `massPlusLat`, $C_{\vec\sigma_\infty,n}$ = `constC Q₀`, $N_{F/\mathbb Q}(I(S))$ = `normAssoc S`,
$N_{F/\mathbb Q}(2\mathcal O_F) = 2^{[F:\mathbb Q]}$). -/
@[kb "hanke2011structure" "Thm. 6.2, pp. 25–26 (one genus, every lattice, any signature; the last display of the proof)"]
theorem massPlusLat_eq_local (hn : 3 ≤ n) (Q₀ : QuadForm (𝓞 F) n) (hQ₀ : Q₀.Nondegenerate)
    (hQ : (formF Q₀).hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral (formF Q₀) L.1) :
    massPlusLat Q₀ hQ₀ L = ENNReal.ofReal (2 * |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) / constC Q₀ *
      normAssoc (detH (formF Q₀) hQ L) ^ (((n : ℝ) + 1) / 2) /
      ((2 : ℝ) ^ Module.finrank ℚ F) ^ ((n : ℝ) * (n + 1) / 2) *
      (∏' v, (locGenusOf v (formF Q₀) L hL).beta)⁻¹) := by
  classical
  set d := Module.finrank ℚ F with hd
  set k := n * (n - 1) / 2 with hk
  set S := detH (formF Q₀) hQ L with hSdef
  set D : F := (formF Q₀).hessian.det with hD
  set P : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F) := fun v => locBasis v L with hP
  set T : ∀ v : HeightOneSpectrum (𝓞 F), QuadForm (v.adicCompletionIntegers F) n := fun v =>
    QuadForm.toO v (localForm (formF Q₀) v (P v)) (localForm_coeff_integral v _ L hL (locBasis_spec v L)) with hTdef
  have hT : ∀ v, (T v).map (algebraMap _ (v.adicCompletion F)) =
      ((LocalDensity.NF.Qp v Q₀).map (algebraMap _ (v.adicCompletion F))).compMat (P v).val := by
    intro v; simp only [hTdef]; rw [QuadForm.map_toO, Tamagawa.map_Qp_eq]; rfl
  have h1 := LatChange.tamagawaKLat_eq_local_gen (by omega) (by omega) Q₀ hQ₀ L P T hT
    (fun v => locBasis_spec v L)
  -- the local factors in the paper's normalization
  set β : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (locGenusOf v (formF Q₀) L hL).beta with hβ
  set a : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (‖(2 : v.adicCompletion F)‖ ^ k)⁻¹ * ‖(P v).val.det‖ ^ (n + 1)
    with ha
  have hfac : ∀ v, (1 / 2 : ℝ) * LocalDensity.DVR.localDensityForm (T v) (T v) (LocalDensity.NF.π v) *
      ‖(P v).val.det‖ ^ (n + 1) = β v * a v := by
    intro v
    have hb := beta_locGenusOf_eq v (formF Q₀) hQ L hL
    have h2v : (‖(2 : v.adicCompletion F)‖ ^ k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr two_ne_zero)
    simp only [hβ, ha, hb]
    field_simp
    ring
  simp_rw [hfac] at h1
  have hβm := multipliable_beta_locGenusOf' hn Q₀ hQ₀ L hL
  have ham : Multipliable a := multipliable_of_hasFiniteMulSupport (finite_mulSupport_detFactor' L k)
  rw [hβm.tprod_mul ham] at h1
  -- the index ratio `r(O(Ô_F^n), O(L̂))` from the lattice change
  set α := ∏' v, LocalDensity.NF.siegelDensity v Q₀ Q₀ with hα
  have hαpos : 0 < α := tprod_siegelDensity_pos hn Q₀ hQ₀
  set A0 := |(discr F : ℝ)| ^ (-((n : ℝ) * (n - 1) / 4)) * ∏ σ : F →ₐ[ℚ] ℂ, archVolSO n (detGram Q₀ σ) with hA0
  have hA0pos : 0 < A0 := mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero F)) _)
    (Finset.prod_pos fun σ _ => ArchSOMeasure.archVolSO_pos n (detGram_pos hQ₀ σ))
  set r := relRatio (locStab (formF Q₀) L) (locStab (formF Q₀) (Tamagawa.stdLat F n)) with hr
  have hrpos : 0 < r := relRatio_pos ⟨relIndex_locStab_ne_zero (formF Q₀) L (Tamagawa.stdLat F n),
    relIndex_locStab_ne_zero (formF Q₀) (Tamagawa.stdLat F n) L⟩
  have hKL : LatChange.tamagawaKLat Q₀ L = A0 * (α * r) := by
    rw [← mul_assoc]; rfl
  rw [hKL] at h1
  have hαr : α * r = (∏' v, β v) * ∏' v, a v := mul_left_cancel₀ hA0pos.ne' h1
  have hPpos : 0 < (∏' v, β v) * ∏' v, a v := by rw [← hαr]; exact mul_pos hαpos hrpos
  have hr' : relRatio (locStab (formF Q₀) (Tamagawa.stdLat F n)) (locStab (formF Q₀) L) =
      α / ((∏' v, β v) * ∏' v, a v) := by
    rw [LatChange.relRatio_symm', ← hr, ← hαr]
    field_simp
  -- the finite product `∏ a`
  have hX : 0 < ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ := Finset.prod_pos fun σ _ =>
    norm_pos_iff.mpr ((map_ne_zero_iff _ σ.toRingHom.injective).mpr hQ)
  set X := ∏ σ : F →ₐ[ℚ] ℂ, ‖σ D‖ with hXdef
  have hnormD : ∀ v : HeightOneSpectrum (𝓞 F), 0 < ‖algebraMap F (v.adicCompletion F) D‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hQ)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) D‖ * ‖(P v).val.det‖ ^ 2 =
      ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ := by
    intro v
    have hc := detH_comp (formF Q₀) hQ L v (locBasis_spec v L)
    rw [← norm_eq_of_comp v S hc, localHessDet, Units.val_mk0, norm_mul, norm_pow]
  have hfinD : {v : HeightOneSpectrum (𝓞 F) | ‖algebraMap F (v.adicCompletion F) D‖ ≠ 1}.Finite := by
    have := (Tamagawa.finite_valuation_ne_one hQ)
    refine this.subset fun v hv => ?_
    intro h
    apply hv
    exact norm_algebraMap_eq_one_nf h
  have hfin2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖).Finite :=
    Hanke2005.hasFiniteMulSupport_norm_two (F := F)
  set T₀ : Finset (HeightOneSpectrum (𝓞 F)) :=
    (finite_mulSupport_detFactor' L k).toFinset ∪ hfinD.toFinset ∪ (supp_finite S).toFinset ∪ hfin2.toFinset
    with hT₀
  have hout : ∀ v ∉ T₀, a v = 1 ∧ ‖algebraMap F (v.adicCompletion F) D‖ = 1 ∧ adelicOrd v S = 0 ∧
      ‖(2 : v.adicCompletion F)‖ = 1 := by
    intro v hv
    simp only [hT₀, Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h1
    · simpa using h2
    · simpa [supp] using h3
    · simpa using h4
  have hA : ∏' v, a v = ∏ v ∈ T₀, a v := by
    rw [tprod_eq_finprod (L := SummationFilter.unconditional _) (finite_mulSupport_detFactor' L k)]
    exact Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).1
  have hNS : normAssoc S = ∏ v ∈ T₀, (Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S := by
    unfold normAssoc
    exact Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => by rw [(hout v hv).2.2.1, zpow_zero]
  have hXT : ∏ v ∈ T₀, ‖algebraMap F (v.adicCompletion F) D‖ = X⁻¹ := by
    rw [← finprod_norm_eq_nf D hQ]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.1).symm
  have h2T : ∏ v ∈ T₀, ‖(2 : v.adicCompletion F)‖ = ((2 : ℝ) ^ d)⁻¹ := by
    rw [← Hanke2005.tprod_norm_two, tprod_eq_finprod (L := SummationFilter.unconditional _) hfin2]
    exact (Tamagawa.finprod_eq_prod_of_one T₀ fun v hv => (hout v hv).2.2.2).symm
  have hdetP : ∀ v : HeightOneSpectrum (𝓞 F), ‖(P v).val.det‖ ^ (n + 1) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖) ^
        (((n : ℝ) + 1) / 2) := by
    intro v
    have h := hloc v
    have hsq : ‖(P v).val.det‖ ^ 2 =
        ((Ideal.absNorm v.asIdeal : ℝ) ^ adelicOrd v S)⁻¹ / ‖algebraMap F (v.adicCompletion F) D‖ := by
      rw [← h]; field_simp [(hnormD v).ne']
    rw [← hsq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1; push_cast; ring
  have hprodA : ∏ v ∈ T₀, a v = (2 : ℝ) ^ (d * k) * (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) := by
    simp only [ha, Finset.prod_mul_distrib, hdetP]
    rw [Finset.prod_inv_distrib, Finset.prod_pow, h2T, Real.finsetProd_rpow _ _ (fun v _ =>
        div_nonneg (inv_nonneg.mpr (zpow_nonneg (Nat.cast_nonneg _) _)) (norm_nonneg _)),
      Finset.prod_div_distrib, Finset.prod_inv_distrib, ← hNS, hXT, inv_pow, inv_inv, ← pow_mul]
    congr 1
    rw [div_inv_eq_mul, inv_mul_eq_div]
  have hNSpos : 0 < normAssoc S := by
    rw [hNS]
    exact Finset.prod_pos fun v _ =>
      zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot))) _
  -- Theorem 6.2 for `𝒪_F^n` and `∏ β_v(𝒪_F^n) = 2^{-dk} ∏ α_v`
  have hΛ : ∏' v, localBeta v Q₀ = ((2 : ℝ) ^ (d * k))⁻¹ * α := tprod_hankeBeta Q₀ hQ₀ (by omega) (by omega)
  have hXN : |((Algebra.norm ℚ ((Q₀.map (algebraMap (𝓞 F) F)).hessian.det) : ℚ) : ℝ)| = X :=
    (Tamagawa.prod_norm_embeddings D).symm
  have hC := constC_pos Q₀
  rw [massPlusLat_eq_relRatio_mul Q₀ hQ₀ hn L hL, theorem_6_2_genus hn Q₀ hQ₀, hr', hΛ, hXN, hA, hprodA]
  have hΔ : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hXp : 0 < X ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hX _
  have hNp : 0 < normAssoc S ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos hNSpos _
  have h2p : 0 < ((2 : ℝ) ^ d) ^ ((n : ℝ) * (n + 1) / 2) := by positivity
  have hΔp : 0 < |(discr F : ℝ)| ^ ((n : ℝ) * (n - 1) / 4) := Real.rpow_pos_of_pos hΔ _
  have hPA : 0 < (2 : ℝ) ^ (d * k) * (X / normAssoc S) ^ (((n : ℝ) + 1) / 2) := by
    have := Real.rpow_pos_of_pos (div_pos hX hNSpos) (((n : ℝ) + 1) / 2)
    positivity
  have hPβ : 0 < ∏' v, β v := by
    rw [hA, hprodA] at hPpos
    exact pos_of_mul_pos_left hPpos hPA.le
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.div_rpow hX.le hNSpos.le]
  field_simp
  ring

end Main

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.massPlusLat_std
#print axioms QuadFormsKB.Hanke2011Structure.massPlusLat_eq_relRatio_mul
#print axioms QuadFormsKB.Hanke2011Structure.massPlusLat_eq_local
