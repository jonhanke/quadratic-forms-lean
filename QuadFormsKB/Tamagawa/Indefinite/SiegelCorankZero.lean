/-
# Siegel's formula for frames of corank zero: representations of a form by forms of the same rank

**Layer:** number fields. $F$ **any** number field, $Q_0$ a nondegenerate quadratic form over $\mathcal O_F$ in $N$ variables of
**any signature** (definite or indefinite: nothing here uses indefiniteness), $L = \mathcal O_F^N$, $T_0$ a nondegenerate form
over $\mathcal O_F$ in the same number $N$ of variables with a rational frame $\Xi$ ($Q_0\circ\Xi = T_0$; equivalently
$T_0\cong Q_0$ over $F$). A representation of $T_0$ by a class $M_i$ of the genus of $L$ is an isometry of $T_0$ into $M_i$
(an $\mathcal O_F$-basis of a sublattice of $M_i$ of full rank with Gram form $T_0$). Notation as in `SiegelCorankOne.lean`:
$n(M_i,T_0)$ = `repCount`, $v(M_i)$ = `unitVolume`, $\beta_\mathfrak p(L,T_0)$ = `NF.localDensityForm`, normalized absolute values
$|x|_w$ at the infinite places ($|\sigma_wx|$ real, $|\sigma_wx|^2$ complex).

**Headlines (unconditional):**
* **`siegelIndefiniteForms_corank0_uncond`** ($N\ge3$):
  $$\sum_in(M_i,T_0) = \prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
  and $\prod_w|\det\Xi|_w^{-1} = \prod_w(|\det H_{Q_0}|_w/|\det H_{T_0}|_w)^{1/2}$ does not depend on $\Xi$;
* **`siegelIndefinite_binary_corank0_uncond`** ($N = 2$, $V$ anisotropic, $E$ its discriminant field): the same with the
  regularized product $L(1,\chi_E)^{-1}\prod_\mathfrak pL_\mathfrak p(1,\chi_E)\tfrac12\beta_\mathfrak p(L,T_0)$ (finite support);
* `tsum_repCount_self` ($N\ge1$): $\sum_in(M_i,L) = 2$ (elementary: one class of representations in each of the two
  $SO(V)(F)$-orbits of frames), so the corank-zero formula for $T_0 = Q_0$ **is** $\tau(SO(V)) = 2$, i.e. the mass formula
  $\sum_iv(M_i) = 2\prod_\mathfrak p\alpha_\mathfrak p(L,L)^{-1}$ (`siegelCorank0_self_iff_tau`).

**Siegel's $\varepsilon = \tfrac12$ and the two orbits.** For $n' = N - r = 0$ the stabilizer $SO(W)$ of a frame is
$SO_0 = 1$, $\tau(SO_0) = 1$, and Weil's factor $\tau(SO(W))/\tau(SO(V))$ is $\tfrac12$, as for $n' = 1$. Here the $\tfrac12$
appears in each local factor, $\tfrac12\beta_\mathfrak p(L,T_0) = \alpha_\mathfrak p(L,T_0)$ (Siegel's normalization `siegelDensity`,
$\varepsilon_\mathfrak p = \tfrac12$ for $n = m$), and the global $\tfrac12$ is cancelled by the **two** $SO(V)(F)$-orbits of
rational frames ($\det X = \pm\det\Xi$, an $O(V)(F)$-torsor): $\sum_in(M_i,T_0) = 2\cdot\#\{SO(\hat L)\text{-orbits of integral
adelic frames}\}$ and $\tau(SO(V)) = 2$. Equivalently, counting with $O$ instead of $SO$: the classes modulo $O(M_i)$ are
half as many when $M_i$ has an improper automorph, and $[O(L_\mathfrak p):SO(L_\mathfrak p)] = 2$ at every $\mathfrak p$.

**Proof.** The split $n = n^+_\Xi + n^+_{\Xi'}$ (`repCount_eq_add`), the global counts
$\sum_in^+_\Xi(M_i,T_0) = \#\mathrm{FinOrbit}(\Xi)$ (`tsum_repCountP_eq`), the local counts $n_v\,\mu_v(SO(L_v)) =
\tfrac12\beta_v(L,T_0)|\det\Xi|_v$ (`locCountZero_mul_aSO`, `tsum_one_finOrbit_zero`), $\tau(SO(V)) = 2$ in the form
$\mu_f(SO(\hat L))\sum_iv(M_i) = 2$, and the product formula for $\det\Xi$.
-/
import QuadFormsKB.Tamagawa.Indefinite.CorankZeroLocal
import QuadFormsKB.Tamagawa.Indefinite.CorankZeroCount

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

section Count

variable (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate)

open Classical in
include hQ hT in
/-- **One orbit against the local factors**: for a rational frame $X$ of $T_0$ and positive convergence factors
$(\lambda_v)$ with $\prod_va_v/\lambda_v$ convergent,
$$\#\mathrm{FinOrbit}(X)\cdot\prod_v\frac{a_v}{\lambda_v} = \prod_{w\mid\infty}|\det X|_w^{-1}\prod_v\frac{\beta_v(L,T_0)}{2\lambda_v}$$
(`locCountZero_mul_aSO`, `tsum_one_finOrbit_zero` and the product formula for $\det X$). -/
theorem finOrbit_mul_tprod_zero (hN : 0 < N) (X : RatFrame Q₀ T₀) (lam : HeightOneSpectrum (𝓞 F) → ℝ)
    (ha : Multipliable fun v => aSO Q₀ v / lam v) :
    Multipliable (fun v => NF.localDensityForm v Q₀ T₀ / 2 / lam v) ∧
      (∑' _O : FinOrbit (n' := 0) Q₀ T₀ X, (1 : ℝ≥0∞)) * ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) =
        ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w X.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w X.1.det‖ ^ 2)⁻¹) *
            ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lam v) := by
  set n : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (locCountZero Q₀ T₀ hT X v : ℝ) with hn
  have hnfin : (Function.mulSupport n).Finite :=
    (badZero Q₀ T₀ hT X).finite_toSet.subset fun v hv => by
      by_contra hb
      exact hv (by simp [hn, locCountZero_eq_one Q₀ hQ T₀ hT X hN v hb])
  have hnm : Multipliable n := multipliable_of_hasFiniteMulSupport hnfin
  set G := X.1.det with hGdef
  have hG : G ≠ 0 := det_ratFrame_ne_zero Q₀ T₀ hT X
  have hGfin := mulSupport_finite_norm (F := F) hG
  have hGv : ∀ v : HeightOneSpectrum (𝓞 F), ‖σV v G‖ ≠ 0 := fun v => norm_ne_zero_iff.2 ((map_ne_zero _).2 hG)
  have hf : ∀ v, n v * (aSO Q₀ v / lam v) = NF.localDensityForm v Q₀ T₀ / 2 / lam v * ‖σV v G‖ := by
    intro v
    have h := locCountZero_mul_aSO Q₀ hQ T₀ hT X hN v
    rw [← mul_div_assoc, h]; ring
  have hinvfin : (Function.mulSupport fun v => ‖σV v G‖⁻¹).Finite := hGfin.subset fun v hv => by
    intro h1; apply hv; show ‖σV v G‖⁻¹ = 1; rw [show ‖σV v G‖ = 1 from h1, inv_one]
  have hβ : (fun v => NF.localDensityForm v Q₀ T₀ / 2 / lam v) =
      fun v => n v * (aSO Q₀ v / lam v) * ‖σV v G‖⁻¹ := by
    funext v; rw [hf, mul_assoc, mul_inv_cancel₀ (hGv v), mul_one]
  have hmβ : Multipliable fun v => NF.localDensityForm v Q₀ T₀ / 2 / lam v := by
    rw [hβ]; exact (hnm.mul ha).mul (multipliable_of_hasFiniteMulSupport hinvfin)
  refine ⟨hmβ, ?_⟩
  rw [tsum_one_finOrbit_zero Q₀ hQ T₀ hT X hN, ← ENNReal.ofReal_mul (tprod_nonneg fun v => Nat.cast_nonneg _)]
  congr 1
  rw [← hnm.tprod_mul ha, tprod_congr hf, hmβ.tprod_mul (multipliable_of_hasFiniteMulSupport hGfin)]
  have hP := prod_places_mul_tprod (F := F) hG
  set Gs := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w G|) *
    ∏ w : {w : InfinitePlace F // w.IsComplex}, ‖σC w G‖ ^ 2 with hGs
  have hA : ∏' v, ‖σV v G‖ = Gs⁻¹ := eq_inv_of_mul_eq_one_right hP
  have hinv : (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w G|⁻¹) *
      ∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w G‖ ^ 2)⁻¹ = Gs⁻¹ := by
    rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib, hGs, mul_inv]
  rw [hA, hinv, mul_comm]

open Classical in
include hQ hT in
/-- **The count against the local factors** (corank zero), for convergence factors $(\lambda_v)$ with
$\prod_va_v/\lambda_v$ convergent:
$$\sum_in(M_i,T_0)\cdot\prod_v\frac{a_v}{\lambda_v} = 2\prod_{w\mid\infty}|\det\Xi|_w^{-1}\prod_v\frac{\beta_v(L,T_0)}{2\lambda_v},$$
and the product on the right converges. -/
theorem count_mul_tprod_zero (hN : 0 < N) (Ξ : RatFrame Q₀ T₀) (lam : HeightOneSpectrum (𝓞 F) → ℝ)
    (ha : Multipliable fun v => aSO Q₀ v / lam v) :
    Multipliable (fun v => NF.localDensityForm v Q₀ T₀ / 2 / lam v) ∧
      (∑' i, repCount Q₀ T₀ i) * ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) =
        2 * ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
            ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lam v) := by
  obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_det_neg Q₀ hQ T₀ Ξ hN
  obtain ⟨hm, h1⟩ := finOrbit_mul_tprod_zero Q₀ hQ T₀ hT hN Ξ lam ha
  obtain ⟨-, h2⟩ := finOrbit_mul_tprod_zero Q₀ hQ T₀ hT hN Ξ' lam ha
  refine ⟨hm, ?_⟩
  have hsplit : ∑' i, repCount Q₀ T₀ i = ∑' i, repCountP Q₀ T₀ Ξ i + ∑' i, repCountP Q₀ T₀ Ξ' i := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun i => repCount_eq_add Q₀ hQ T₀ hT Ξ Ξ' hΞ' i
  have hR : ∀ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ'.1.det|⁻¹ = |σR w Ξ.1.det|⁻¹ := fun w => by
    rw [hΞ', map_neg, abs_neg]
  have hC : ∀ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ'.1.det‖ ^ 2)⁻¹ = (‖σC w Ξ.1.det‖ ^ 2)⁻¹ :=
    fun w => by rw [hΞ', map_neg, norm_neg]
  rw [hsplit, tsum_repCountP_eq Q₀ hQ T₀ hT Ξ, tsum_repCountP_eq Q₀ hQ T₀ hT Ξ', add_mul, h1, h2,
    Finset.prod_congr rfl fun w _ => hR w, Finset.prod_congr rfl fun w _ => hC w, two_mul]

end Count

/-! ### Headline: corank zero, $N\ge3$ -/

open Classical in
/-- **Siegel's formula for frames of corank zero, every number field — unconditional** (Siegel 1935, 1936, Hauptsatz for
$n = m$, $\varepsilon = \frac12$; Weil 1965): for $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N\ge3$
variables of any signature, $T_0$ nondegenerate over $\mathcal O_F$ in $N$ variables with a rational frame $\Xi$
($Q_0\circ\Xi = T_0$),
$$\sum_in(M_i,T_0) = \prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\prod_\mathfrak p\tfrac12\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^N$; $n(M_i,T_0)$ = `repCount` (the number of classes of
representations of $T_0$ by $M_i$, i.e. of isometric embeddings of $(\mathcal O_F^N, T_0)$ into $M_i$, modulo the unit group
$\Gamma_i = SO(M_i)$), $v(M_i)$ = `unitVolume`, $|\cdot|_w$ normalized ($|\sigma_w\det\Xi|$ at a real place,
$|\sigma_w\det\Xi|^2$ at a complex place), $\beta_\mathfrak p$ = `NF.localDensityForm`; $\tfrac12\beta_\mathfrak p(L,T_0)$ is Siegel's
$\alpha_\mathfrak p(L,T_0)$ (`NF.siegelDensity`). For definite $Q_0$ over $\mathbb Q$: $n(M_i,T_0) = r(M_i,T_0)/|SO(M_i)|$ and
$v(M_i) = \mathrm{vol}(SO(V)(\mathbb R))/|SO(M_i)|$. For $T_0 = Q_0$, $\Xi = 1$ the left side is $2$ (`tsum_repCount_self`) and the
statement is $\tau(SO(V)) = 2$. No hypotheses beyond these. -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz, n = m (ε = 1/2; corank zero; every number field) [unverified]"]
theorem siegelIndefiniteForms_corank0_uncond (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)
    (T₀ : QuadForm (𝓞 F) N) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) (hN : 3 ≤ N) :
    ∑' i, repCount Q₀ T₀ i =
      ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2) * ∑' i, unitVolume Q₀ hQ i := by
  have hN0 : 0 < N := by omega
  -- the local product of `SO(V)` and `τ(SO(V)) = 2`
  have hApos : 0 < ∏' v, aSO Q₀ v := tprod_aSO_pos hN Q₀ hQ
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  have hτ : A * V = 2 := by
    have h := tauTwoAll_release_uncond N hN Q₀ hQ
    unfold TamagawaNumberTwoAdelic at h
    rw [covolume_muTam_eq_muFin_mul, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ (fun _ => one_pos)] at h
    simp only [div_one] at h
    exact h
  obtain ⟨-, hcount⟩ := count_mul_tprod_zero Q₀ hQ T₀ hT hN0 Ξ (fun _ => 1)
    (by simpa only [div_one] using multipliable_aSO hN Q₀ hQ)
  simp only [div_one] at hcount
  refine (ENNReal.mul_left_inj hA0 hAt).mp (hcount.trans ?_)
  rw [← hτ]; ring

/-! ### Binary forms ($N = 2$), $V$ anisotropic -/

open Classical in
/-- **Siegel's formula for isometries of anisotropic binary forms, every number field — unconditional** (Siegel 1935,
Hauptsatz for $n = m = 2$, $\varepsilon = \frac12$; Weil 1965 with convergence factors): for $F$ a number field, $Q_0$ a
nondegenerate binary form over $\mathcal O_F$ of any signature, **anisotropic** over $F$, $E$ its discriminant field
(`IsDiscField`), $T_0$ a nondegenerate binary form over $\mathcal O_F$ with a rational frame $\Xi$ ($Q_0\circ\Xi = T_0$),
$$\sum_in(M_i,T_0) = \prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot L(1,\chi_E)^{-1}\prod_\mathfrak pL_\mathfrak p(1,\chi_E)\,
\tfrac12\beta_\mathfrak p(L,T_0)\cdot\sum_iv(M_i),$$
$L_\mathfrak p(1,\chi_E)^{-1}$ = `lamL (chiE F E) 𝔭`, $L(1,\chi_E)$ = `LOne (chiE F E)`; the $L$-value is Weil's global
convergence factor of $\tau(SO(V)) = 2$ (`tauTwoBinaryAll_uncond`). Isotropic binary $V$ is excluded. -/
@[kb "siegel1935" "Hauptsatz for n = m = 2 (ε = 1/2), isometries of binary forms; convergence factors L(1, χ) [unverified]"]
theorem siegelIndefinite_binary_corank0_uncond (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra F E] (hE : IsDiscField Q₀ E)
    (T₀ : QuadForm (𝓞 F) 2) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    ∑' i, repCount Q₀ T₀ i =
      ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) * (LOne (chiE F E))⁻¹ *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lamL (chiE F E) v) * ∑' i, unitVolume Q₀ hQ i := by
  set lam := lamL (chiE F E) with hlamdef
  have hlam : ∀ v, 0 < lam v := lamL_pos (abs_chiE_le hE.finrank_eq_two)
  obtain ⟨hL, -⟩ := lOne_chiE (F := F) (E := E) hE.finrank_eq_two
  -- the convergence factors make the local product of `SO(V)` finite
  obtain ⟨S, hS⟩ := eventually_muLocSO_lamL_chiE Q₀ hQ hE
  have haS : ∀ v ∉ S, aSO Q₀ v / lam v = 1 := by
    intro v hv
    have h := hS v hv
    have h0 : 0 ≤ NF.siegelDensity v Q₀ Q₀ / lam v :=
      div_nonneg (siegelDensity_self_pos' Q₀ hQ v).le (hlam v).le
    rw [muLocSO_soStabSO, ← ENNReal.ofReal_one] at h
    rw [aSO_eq_siegelDensity Q₀ hQ v]
    exact (ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one).mp h
  have hafin : (Function.mulSupport fun v => aSO Q₀ v / lam v).Finite :=
    S.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (haS v h)
  have ha : Multipliable fun v => aSO Q₀ v / lam v := multipliable_of_hasFiniteMulSupport hafin
  have hApos : 0 < ∏' v, aSO Q₀ v / lam v := by
    rw [tprod_eq_prod (s := hafin.toFinset) (fun v hv => by
      by_contra hne; exact hv (hafin.mem_toFinset.2 hne))]
    exact Finset.prod_pos fun v _ => div_pos (aSO_pos Q₀ hQ v) (hlam v)
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v / lam v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolume Q₀ hQ i with hV
  -- `τ(SO(V)) = 2` for the binary measure
  have hτ : ENNReal.ofReal (LOne (chiE F E))⁻¹ * (A * V) = 2 := by
    have h := tauTwoBinaryAll_uncond F Q₀ hQ hA E hE
    rw [muTamBin, muTamChi, covolume_smul_muTam, covolume_muTam_eq_muFin_mul, muFin_KSO,
      finFactor_eq_tprod_aSO Q₀ hQ hlam] at h
    exact h
  obtain ⟨-, hcount⟩ := count_mul_tprod_zero Q₀ hQ T₀ hT two_pos Ξ lam ha
  refine (ENNReal.mul_left_inj hA0 hAt).mp (hcount.trans ?_)
  set P := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
    (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) with hP
  set B := ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lam v with hB
  have hP0 : 0 ≤ P := mul_nonneg (Finset.prod_nonneg fun w _ => by positivity)
    (Finset.prod_nonneg fun w _ => by positivity)
  have hLi : 0 ≤ (LOne (chiE F E))⁻¹ := (inv_pos.2 hL).le
  rw [← hτ]
  have e : ENNReal.ofReal (P * (LOne (chiE F E))⁻¹ * B) =
      ENNReal.ofReal (LOne (chiE F E))⁻¹ * ENNReal.ofReal (P * B) := by
    rw [← ENNReal.ofReal_mul hLi]
    congr 1
    ring
  rw [e]
  ring

/-! ### $T_0 = Q_0$: the count is $2$, and the formula is $\tau(SO(V)) = 2$ -/

section Self

variable (Q₀ : QuadForm (𝓞 F) N) (hQ : Q₀.Nondegenerate)

/-- The identity frame of $Q_0$ ($Q_0\circ1 = Q_0$). -/
def ratFrameOne : RatFrame Q₀ Q₀ := ⟨1, QuadForm.compMat_one _⟩

include hQ in
/-- A rational frame $X$ of $Q_0$ with $\det X = \pm1$ has one local orbit at every place: $n_v = 1$. -/
theorem locCountZero_self (hN : 0 < N) (X : RatFrame Q₀ Q₀) (hX : X.1.det = 1 ∨ X.1.det = -1)
    (v : HeightOneSpectrum (𝓞 F)) : locCountZero Q₀ Q₀ hQ X v = 1 := by
  have h := locCountZero_mul_aSO Q₀ hQ Q₀ hQ X hN v
  have hn : ‖σV v X.1.det‖ = 1 := by
    rcases hX with h1 | h1 <;> simp [h1]
  have ha : aSO Q₀ v = 2⁻¹ * NF.localDensityForm v Q₀ Q₀ := by
    rw [aSO_eq_siegelDensity Q₀ hQ v]; simp only [NF.siegelDensity, ↓reduceIte]; norm_num
  rw [hn, mul_one, ← ha] at h
  have hpos := aSO_pos Q₀ hQ v
  have : (locCountZero Q₀ Q₀ hQ X v : ℝ) = 1 := by
    have := (mul_left_inj' hpos.ne').mp (h.trans (one_mul _).symm)
    exact this
  exact_mod_cast this

include hQ in
/-- **One class of representations of $L$ in each orbit**: $\sum_in(M_i,L) = 2$ ($N\ge1$). The two $SO(V)(F)$-orbits of
frames of $Q_0$ are those of $1$ and of a rational reflection $s$; each meets the genus in exactly one class of
representations modulo units (all local orbit counts are $1$). Elementary: no Tamagawa number is used. -/
@[kb "siegel1935" "n = m = rank: the representations of L by its genus, classes modulo units [unverified]"]
theorem tsum_repCount_self (hN : 0 < N) : ∑' i, repCount Q₀ Q₀ i = 2 := by
  classical
  obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_det_neg Q₀ hQ Q₀ (ratFrameOne Q₀) hN
  have h1 : (ratFrameOne Q₀).1.det = 1 := Matrix.det_one
  have hc : ∀ X : RatFrame Q₀ Q₀, (X.1.det = 1 ∨ X.1.det = -1) →
      ∑' _O : FinOrbit (n' := 0) Q₀ Q₀ X, (1 : ℝ≥0∞) = 1 := by
    intro X hX
    rw [tsum_one_finOrbit_zero Q₀ hQ Q₀ hQ X hN]
    simp only [locCountZero_self Q₀ hQ hN X hX, Nat.cast_one, tprod_one, ENNReal.ofReal_one]
  have hsplit : ∑' i, repCount Q₀ Q₀ i =
      ∑' i, repCountP Q₀ Q₀ (ratFrameOne Q₀) i + ∑' i, repCountP Q₀ Q₀ Ξ' i := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun i => repCount_eq_add Q₀ hQ Q₀ hQ (ratFrameOne Q₀) Ξ' hΞ' i
  rw [hsplit, tsum_repCountP_eq Q₀ hQ Q₀ hQ, tsum_repCountP_eq Q₀ hQ Q₀ hQ, hc _ (Or.inl h1),
    hc _ (Or.inr (by rw [hΞ', h1]))]
  norm_num

include hQ in
/-- **The corank-zero formula for $T_0 = Q_0$ is $\tau(SO(V)) = 2$** ($N\ge1$): with $\Xi = 1$,
$$\sum_in(M_i,L) = \prod_\mathfrak p\tfrac12\beta_\mathfrak p(L,L)\cdot\sum_iv(M_i)\iff\operatorname{covol}(SO(V)(F)\backslash
SO(V)(\mathbb A),\mu_{\mathrm{Tam}}) = 2,$$
since the left side is $2$ (`tsum_repCount_self`) and $\mu_f(SO(\hat L)) = \prod_\mathfrak p\alpha_\mathfrak p(L,L)$,
$\alpha_\mathfrak p = \frac12\beta_\mathfrak p$. So `siegelIndefiniteForms_corank0_uncond` contains the mass formula
$\sum_iv(M_i) = 2\prod_\mathfrak p\alpha_\mathfrak p(L,L)^{-1}$, and conversely the count plus $\tau = 2$ gives it for $T_0 = Q_0$. -/
theorem siegelCorank0_self_iff_tau (hN : 0 < N) :
    ∑' i, repCount Q₀ Q₀ i =
        ENNReal.ofReal (∏' v, NF.localDensityForm v Q₀ Q₀ / 2) * ∑' i, unitVolume Q₀ hQ i ↔
      TamagawaNumberTwoAdelic Q₀ hQ := by
  have ha : ∏' v, NF.localDensityForm v Q₀ Q₀ / 2 = ∏' v, aSO Q₀ v / 1 := tprod_congr fun v => by
    rw [aSO_eq_siegelDensity Q₀ hQ v]; simp only [NF.siegelDensity, ↓reduceIte]; ring
  unfold TamagawaNumberTwoAdelic
  rw [covolume_muTam_eq_muFin_mul, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ (fun _ => one_pos),
    tsum_repCount_self Q₀ hQ hN, ha]
  exact eq_comm

end Self

end QuadFormsKB.Tamagawa.Indefinite
