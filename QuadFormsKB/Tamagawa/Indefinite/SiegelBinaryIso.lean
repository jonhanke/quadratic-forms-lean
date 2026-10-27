/-
# Siegel's formula for isotropic binary forms: corank one (numbers) and corank zero (isometries)

**Layer:** number fields, adeles. $F$ **any** number field, $Q_0$ a nondegenerate binary form over $\mathcal O_F$ that is
**isotropic** over $F$ (e.g. $xy$, `hypForm`), $e$ an isotropic vector, $\chi = \chi_e$ the eigenvalue on the line $Fe$
(`isoChar`), so $SO(V)\cong\mathbb G_m$. Notation as in `SiegelCorankOne.lean`: $n(M_i,T_0)$ = `repCount`, $\beta_\mathfrak p$ =
`NF.localDensityForm`, $\lambda_\mathfrak p = 1 - N\mathfrak p^{-1}$ (`lamV`), $\rho_F = \operatorname{Res}_{s=1}\zeta_F(s)$
(`dedekindZeta_residue`).

**Why a different normalization.** The unit group $\Gamma_i = SO(M_i)\cong\mathcal O_F^\times$ has rank $r_1 + r_2 - 1$ (finite
only for $F = \mathbb Q$ and $F$ imaginary quadratic), while $SO(V)(F_\infty)\cong\prod_{w\mid\infty}F_w^\times$ has dimension
$r_1 + r_2$; so the unit volumes $v(M_i)$ (`unitVolume`) are all infinite and $\tau(SO(V)) = \infty$. The counts
$n(M_i,T_0)$ stay finite (the stabilizer of a frame is trivial). Replace $v(M_i)$ by the **norm-one unit volume**
$$v^1(M_i) = \operatorname{covol}\bigl(\Gamma_i\backslash SO(V)(F_\infty),\ \mu_\infty|_{\{0\le\log|\chi|_\infty<1\}}\bigr)
  = \operatorname{vol}(\Gamma_i\backslash SO(V)(F_\infty)^1)\qquad(\texttt{unitVolumeIso})$$
($\Gamma_i\subseteq\ker|\chi|_\infty$; $\mu_\infty = \mu^1_\infty\times dt/t$, $\int_1^e dt/t = 1$) and $\tau(SO(V)) = 2$ by Weil's
$\tau^1(SO(V)) = 1$ for $\rho_F^{-1}\prod_v\lambda_v^{-1}\omega_v$ (`tauOne_binary_isotropic_uncond`).

**Statements (unconditional):**
* `tauIso_eq_tsum_unitVolumeIso` and **`massIso_uncond`** (the norm-one mass formula):
  $\mu^\lambda_f(SO(\hat L))\sum_iv^1(M_i) = \rho_F$, $\mu^\lambda_f(SO(\hat L)) = \prod_\mathfrak p\alpha_\mathfrak p(L,L)/\lambda_\mathfrak p$;
* **`siegelIndefinite_binary_isotropic_uncond`** (corank one, $T_0 = \langle m\rangle$):
  $$c^{(1)}_\infty(Q_0)\sum_in(M_i,m) = |d_F|^{-1/2}\rho_F^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(L,m)}{1 - N\mathfrak p^{-1}}\cdot\sum_iv^1(M_i);$$
* **`siegelIndefinite_binary_isotropic_corank0_uncond`** (corank zero, $T_0$ binary with a rational frame $\Xi$):
  $$\sum_in(M_i,T_0) = 2\prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\rho_F^{-1}\prod_\mathfrak p\frac{\tfrac12\beta_\mathfrak p(L,T_0)}{1 - N\mathfrak p^{-1}}
    \cdot\sum_iv^1(M_i);$$
* **`tsum_repCount_hypForm`** ($Q_0 = xy$): $\sum_in(M_i,m) = \prod_\mathfrak p\beta_\mathfrak p(xy,m)/(1 - N\mathfrak p^{-1})$, no measures
  (classically $\beta_\mathfrak p(xy,m) = (1 - N\mathfrak p^{-1})(v_\mathfrak p(m) + 1)$, so this is the number $d_F(m)$ of integral ideals
  dividing $m$; over $\mathbb Q$, $n(\mathbb Z^2,m) = \#\{(x,y) : xy = m\}/\{\pm1\} = d(m)$).

**The factors.** Weil's factor is $\tau(SO_1)/\tau^1(SO(V)) = 1$ (corank one: no $\tfrac12$, unlike the anisotropic
`siegelIndefinite_binary_uncond`) and $\tau(SO_0)/\tau^1(SO(V)) = 1$ (corank zero: the two $SO(V)(F)$-orbits of rational frames
give the factor $2$).

**Proof:** The counts (`count_mul_tprod`, `count_mul_tprod_zero`, valid for every nondegenerate binary $Q_0$ and
every $\lambda$ with $\prod_va_v/\lambda_v$ convergent), the torus lemma (`tauIso_eq_tsum_DCq`) with $U = SO(\hat L)$,
and
$\tau^1 = 1$.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankZero
import QuadFormsKB.Tamagawa.Indefinite.SiegelCorankOne
import QuadFormsKB.Tamagawa.Indefinite.IsoTorus
import QuadFormsKB.Tamagawa.Indefinite.IsoHyps
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteChecks
import QuadFormsKB.LocalDensity.HyperbolicNumbers

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.RegProd

variable {F : Type} [Field F] [NumberField F]

section Iso

variable (Q₀ : QuadForm (𝓞 F) 2) (hQ : Q₀.Nondegenerate) {e : Fin 2 → F} (he : IsIsoVec Q₀ e)

/-- **The norm-one unit volume** $v^1(M_i)$ of the class $i$ of an isotropic binary lattice: the covolume of the unit group
$\Gamma_i$ in $SO(V)(F_\infty)$ for Weil's archimedean measure `muArchTamSO` restricted to the shell
$\{0\le\log|\chi_e|_\infty<1\}$ (`isoShellInf`). Since $\Gamma_i\subseteq\ker|\chi_e|_\infty$ and $\mu_\infty = \mu^1_\infty\times dt/t$,
it is $\operatorname{vol}(\Gamma_i\backslash SO(V)(F_\infty)^1)$; the unrestricted `unitVolume` is infinite here. Parameters: `Q₀`,
`hQ`, `he`, `i`. -/
@[kb "weil1982" "§3.2 (norm-one part G(𝔸)¹ for a split torus; unit volumes of SO(V) ≅ G_m) [unverified page]"]
def unitVolumeIso (i : DC Q₀) : ℝ≥0∞ :=
  covolume (unitGroup Q₀ i) (GInfSO Q₀) ((muArchTamSO Q₀ hQ).restrict (isoShellInf Q₀ hQ he))

/-- **$|\chi_e(u)|_f = 1$ on $SO(\hat L)$**: an eigenvalue of a matrix in $GL_2(\mathfrak o_v)$ is a unit. -/
theorem isoNormFin_KSO (u : SOAf Q₀) (hu : u ∈ KSO Q₀) : isoNormFin Q₀ hQ he u = 1 := by
  refine isoNormFin_eq_one_of_units Q₀ hQ he u fun v => ?_
  have hst := (mem_KSO_iff Q₀ u).1 hu v
  set gv := evalSO Q₀ v u with hgv
  have hstd : ((gv : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) ∈
      stdStab (Q₀.map (algebraMap (𝓞 F) F)) v := hst
  have hstd' : (((gv⁻¹ : SOv v Q₀)) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) ∈
      stdStab (Q₀.map (algebraMap (𝓞 F) F)) v := (soStabSO v Q₀).inv_mem hst
  have hMM : omat ((gv⁻¹ : SOv v Q₀) : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) *
      omat (gv : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) = 1 := by
    rw [← omat_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hspec := isoCharV_spec hQ he v (finComp u v)
  have hx : (algebraMap F (v.adicCompletion F) ∘ e) ≠ 0 := by
    intro h0
    apply he.1
    funext j
    have := congrFun h0 j
    simpa using this
  exact valuation_eigen_eq_one Valued.v _ _ (fun i j => entry_le_one_of_mem_stdStab v hstd i j)
    (fun i j => entry_le_one_of_mem_stdStab v hstd' i j) hMM _ hx _ hspec

/-- The double cosets of the torus lemma for $U = SO(\hat L)$ are the proper classes in the genus. -/
theorem tsum_DCq_KSO_eq (f : SOAf Q₀ → ℝ≥0∞) (hf : ∀ b, f b = f 1) :
    ∑' c : DCq Q₀ (KSO Q₀), f (dcqRep Q₀ (KSO Q₀) c) = ∑' i : DC Q₀, f (dcRep Q₀ i) := by
  let eqv : DCq Q₀ (KSO Q₀) ≃ DC Q₀ := Quotient.congr (Equiv.refl _) (fun _ _ => Iff.rfl)
  rw [tsum_congr fun c => hf (dcqRep Q₀ (KSO Q₀) c), tsum_congr fun i => hf (dcRep Q₀ i)]
  exact eqv.tsum_eq (fun _ => f 1)

/-- **The torus lemma for $U = SO(\hat L)$**: $\tau^1(SO(V)) = \rho_F^{-1}\mu^\lambda_f(SO(\hat L))\sum_iv^1(M_i)$. -/
theorem tauIso_eq_tsum_unitVolumeIso :
    tauIso Q₀ hQ he = ENNReal.ofReal (dedekindZeta_residue F)⁻¹ * muFin Q₀ lamV (KSO Q₀) *
      ∑' i, unitVolumeIso Q₀ hQ he i := by
  have := countable_DCq Q₀ (KSO Q₀) (isOpen_KSO Q₀)
  rw [tauIso_eq_tsum_DCq Q₀ hQ he (KSO Q₀) (isOpen_KSO Q₀).measurableSet (isoNormFin_KSO Q₀ hQ he)
    (discreteTopology_levelGroup Q₀)]
  congr 1

include hQ he in
/-- $\prod_\mathfrak p a_\mathfrak p/\lambda_\mathfrak p$ converges for isotropic binary forms ($a_\mathfrak p = \lambda_\mathfrak p$ off a finite set). -/
theorem multipliable_aSO_lamV_iso : Multipliable fun v => aSO Q₀ v / lamV v := by
  have h := multipliable_siegelDensity_div_lamV hQ ((isotropicF_iff_isSquare Q₀).1 ⟨e, he⟩)
  exact h.congr fun v => by rw [aSO_eq_siegelDensity Q₀ hQ v]

include hQ in
/-- $\prod_\mathfrak p a_\mathfrak p/\lambda_\mathfrak p > 0$. -/
theorem tprod_aSO_lamV_pos : 0 < ∏' v, aSO Q₀ v / lamV v := by
  rw [← finFactor_eq_tprod_aSO Q₀ hQ lamV_pos]
  exact finFactor_lamV_pos_gen Q₀ hQ

/-- **The norm-one mass formula for an isotropic binary lattice, every number field — unconditional** (Weil's
$\tau^1(\mathbb G_m) = 1$; Dirichlet's class number formula): for $F$ a number field and $Q_0$ a nondegenerate binary form over
$\mathcal O_F$, isotropic over $F$ with isotropic vector $e$,
$$\prod_\mathfrak p\frac{\alpha_\mathfrak p(L,L)}{1 - N\mathfrak p^{-1}}\cdot\sum_iv^1(M_i) = \rho_F,$$
$\alpha_\mathfrak p(L,L) = \mu_\mathfrak p(SO(L_\mathfrak p))$ (`aSO`, Siegel's density), $v^1(M_i)$ = `unitVolumeIso`, $\rho_F$ the residue
of $\zeta_F$ at $s = 1$. For $xy$ the product is $1$ and $\sum_iv^1(M_i) = \rho_F$. -/
@[kb "weil1982" "§3.2 and Thm 3.2.1 (τ(G_m) = 1), mass formula for the norm-one unit groups [unverified page]"]
theorem massIso_uncond :
    ENNReal.ofReal (∏' v, aSO Q₀ v / lamV v) * ∑' i, unitVolumeIso Q₀ hQ he i =
      ENNReal.ofReal (dedekindZeta_residue F) := by
  have h := tauOne_binary_isotropic_uncond F Q₀ hQ ⟨e, he⟩ e he
  rw [tauIso_eq_tsum_unitVolumeIso, muFin_KSO, finFactor_eq_tprod_aSO Q₀ hQ lamV_pos, mul_assoc] at h
  have hρ := dedekindZeta_residue_pos F
  rw [ENNReal.ofReal_inv_of_pos hρ] at h
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := (ENNReal.ofReal_pos.2 hρ).ne'
  calc _ = ENNReal.ofReal (dedekindZeta_residue F) * ((ENNReal.ofReal (dedekindZeta_residue F))⁻¹ *
        (ENNReal.ofReal (∏' v, aSO Q₀ v / lamV v) * ∑' i, unitVolumeIso Q₀ hQ he i)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hρ0 ENNReal.ofReal_ne_top, one_mul]
    _ = _ := by rw [h, mul_one]

/-- **The regularized product of the local densities of an isotropic binary form**:
$$|d_F|^{-1/2}\,\rho_F^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(L,T_0)}{1 - N\mathfrak p^{-1}},$$
$\rho_F$ = `dedekindZeta_residue F` (Weil's global factor of $\mathbb G_m$), $1 - N\mathfrak p^{-1}$ = `lamV` (the convergence
factors $\zeta_{F,\mathfrak p}(1)^{-1}$). The factors $\beta_\mathfrak p/\lambda_\mathfrak p$ are $1$ for almost all $\mathfrak p$ when $V$ is
isotropic. Parameters: `Q₀`, `T₀`. -/
@[kb "siegel1935" "local densities of isotropic binary forms, regularized by ζ_F (convergence factors 1 - Np⁻¹) [unverified]"]
def isoBinDensityProduct (Q₀ : QuadForm (𝓞 F) 2) (T₀ : QuadForm (𝓞 F) 1) : ℝ :=
  |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * (dedekindZeta_residue F)⁻¹ * ∏' v, NF.localDensityForm v Q₀ T₀ / lamV v

open Classical in
/-- **Siegel's formula for the numbers represented by an isotropic binary form, every number field — unconditional**
(corank one, $N = 2$, $r = 1$, with Weil's $\tau^1(SO(V)) = 1$ for $SO(V)\cong\mathbb G_m$): for $F$ a number field, $Q_0$ a
nondegenerate binary form over $\mathcal O_F$, **isotropic** over $F$ with isotropic vector $e$, $T_0 = \langle m\rangle$ a
nondegenerate form in one variable with a rational point $\Xi$ ($Q_0(\Xi) = m$),
$$c^{(1)}_\infty(Q_0)\sum_in(M_i,m) = |d_F|^{-1/2}\rho_F^{-1}\prod_\mathfrak p\frac{\beta_\mathfrak p(L,m)}{1 - N\mathfrak p^{-1}}\cdot\sum_iv^1(M_i),$$
the sums over the proper classes $M_i$ in the genus of $L = \mathcal O_F^2$; $n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with
$Q_0(x) = m$ modulo the unit group $SO(M_i)\cong\mathcal O_F^\times$; finite), $v^1(M_i)$ = `unitVolumeIso` (norm-one unit
volumes; the unit volumes themselves are infinite), $c^{(1)}_\infty(Q_0) = c_F(2)\prod_w|\det H_{Q_0}|_w^{-1}$ (`cInfCorankOne`),
$\rho_F$ = `dedekindZeta_residue F`. No factor $\tfrac12$: Weil's factor is $\tau(SO_1)/\tau^1(SO(V)) = 1$. Over $\mathbb Q$ for
$xy$: $\sum_in(M_i,m) = d(m)$, $v^1(\mathbb Z^2) = 1$. -/
@[kb "siegel1935" "Hauptsatz for n = 2, m = 1, isotropic binary forms (Siegel's excluded case), with Weil's τ¹(G_m) = 1 [unverified]"]
theorem siegelIndefinite_binary_isotropic_uncond (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame Q₀ T₀) :
    cInfCorankOne Q₀ * ∑' i, repCount Q₀ T₀ i =
      ENNReal.ofReal (isoBinDensityProduct Q₀ T₀) * ∑' i, unitVolumeIso Q₀ hQ he i := by
  have ha := multipliable_aSO_lamV_iso Q₀ hQ he
  have hApos := tprod_aSO_lamV_pos Q₀ hQ
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v / lamV v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolumeIso Q₀ hQ he i with hV
  have hτ : A * V = ENNReal.ofReal (dedekindZeta_residue F) := massIso_uncond Q₀ hQ he
  have hρ := dedekindZeta_residue_pos F
  obtain ⟨hmf, hcount⟩ := count_mul_tprod (r := 1) Q₀ hQ T₀ hT Ξ lamV lamV_pos ha
  have hid := densityIdentity_corankOne (r := 1) Q₀ hQ T₀ Ξ (towerCorankOne (r := 1) Q₀ hQ T₀ hT Ξ) hT lamV
    (fun v => (lamV_pos v).ne') hmf
  have key1 : cInfCorankOne Q₀ * (∑' i, repCount Q₀ T₀ i) * A =
      ENNReal.ofReal (isoBinDensityProduct Q₀ T₀ * dedekindZeta_residue F) := by
    rw [mul_assoc, hcount, cInfCorankOne_eq, ← ENNReal.ofReal_mul (mul_nonneg (cF_pos' (F := F) _).le (mul_nonneg
      (Finset.prod_nonneg fun w _ => by positivity) (Finset.prod_nonneg fun w _ => by positivity)))]
    congr 1
    rw [isoBinDensityProduct, ← hid, cF_two]
    field_simp
  have key2 : ENNReal.ofReal (isoBinDensityProduct Q₀ T₀) * V * A =
      ENNReal.ofReal (isoBinDensityProduct Q₀ T₀ * dedekindZeta_residue F) := by
    rw [mul_assoc, mul_comm V A, hτ, ← ENNReal.ofReal_mul' hρ.le]
  exact (ENNReal.mul_left_inj hA0 hAt).mp (key1.trans key2.symm)

open Classical in
/-- **Siegel's formula for isometries of isotropic binary forms, every number field — unconditional** (corank zero,
$N = r = 2$, with Weil's $\tau^1(SO(V)) = 1$): for $F$ a number field, $Q_0$ a nondegenerate binary form over $\mathcal O_F$,
**isotropic** over $F$ with isotropic vector $e$, $T_0$ a nondegenerate binary form over $\mathcal O_F$ with a rational frame
$\Xi$ ($Q_0\circ\Xi = T_0$),
$$\sum_in(M_i,T_0) = 2\prod_{w\mid\infty}|\det\Xi|_w^{-1}\cdot\rho_F^{-1}\prod_\mathfrak p\frac{\tfrac12\beta_\mathfrak p(L,T_0)}{1 - N\mathfrak p^{-1}}
\cdot\sum_iv^1(M_i),$$
$n(M_i,T_0)$ = `repCount` (isometric embeddings of $(\mathcal O_F^2,T_0)$ into $M_i$ modulo units), $v^1(M_i)$ = `unitVolumeIso`,
$|\cdot|_w$ normalized, $\rho_F$ = `dedekindZeta_residue F`, $1 - N\mathfrak p^{-1}$ = `lamV`. The factor $2$: two
$SO(V)(F)$-orbits of rational frames, and Weil's factor $\tau(SO_0)/\tau^1(SO(V)) = 1$. For $T_0 = Q_0$, $\Xi = 1$ the left side
is $2$ (`tsum_repCount_self`) and the statement is the norm-one mass formula `massIso_uncond`. -/
@[kb "siegel1935" "Hauptsatz for n = m = 2, isotropic binary forms, with Weil's τ¹(G_m) = 1 [unverified]"]
theorem siegelIndefinite_binary_isotropic_corank0_uncond (T₀ : QuadForm (𝓞 F) 2) (hT : T₀.Nondegenerate)
    (Ξ : RatFrame Q₀ T₀) :
    ∑' i, repCount Q₀ T₀ i =
      2 * ENNReal.ofReal ((∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
          (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) * (dedekindZeta_residue F)⁻¹ *
        ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lamV v) * ∑' i, unitVolumeIso Q₀ hQ he i := by
  have ha := multipliable_aSO_lamV_iso Q₀ hQ he
  have hApos := tprod_aSO_lamV_pos Q₀ hQ
  set A := ENNReal.ofReal (∏' v, aSO Q₀ v / lamV v) with hAdef
  have hA0 : A ≠ 0 := (ENNReal.ofReal_pos.2 hApos).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set V := ∑' i, unitVolumeIso Q₀ hQ he i with hV
  have hτ : A * V = ENNReal.ofReal (dedekindZeta_residue F) := massIso_uncond Q₀ hQ he
  have hρ := dedekindZeta_residue_pos F
  obtain ⟨-, hcount⟩ := count_mul_tprod_zero Q₀ hQ T₀ hT two_pos Ξ lamV ha
  refine (ENNReal.mul_left_inj hA0 hAt).mp (hcount.trans ?_)
  set P := (∏ w : {w : InfinitePlace F // w.IsReal}, |σR w Ξ.1.det|⁻¹) *
    (∏ w : {w : InfinitePlace F // w.IsComplex}, (‖σC w Ξ.1.det‖ ^ 2)⁻¹) with hP
  set B := ∏' v, NF.localDensityForm v Q₀ T₀ / 2 / lamV v with hB
  have e1 : ENNReal.ofReal (P * (dedekindZeta_residue F)⁻¹ * B) * ENNReal.ofReal (dedekindZeta_residue F) =
      ENNReal.ofReal (P * B) := by
    rw [← ENNReal.ofReal_mul' hρ.le]
    congr 1
    field_simp
  calc 2 * ENNReal.ofReal (P * B)
      = 2 * (ENNReal.ofReal (P * (dedekindZeta_residue F)⁻¹ * B) * (A * V)) := by rw [hτ, e1]
    _ = _ := by ring

/-! ### The hyperbolic plane $xy$: the count without measures -/

/-- For $xy$ the regularized local masses are $1$: $\prod_\mathfrak p\alpha_\mathfrak p/\lambda_\mathfrak p = 1$. -/
theorem tprod_aSO_lamV_hypForm :
    ∏' v, aSO (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) v / lamV v = 1 := by
  rw [← finFactor_eq_tprod_aSO _ nondegenerate_hypForm lamV_pos]
  exact finFactor_hypForm

/-- **The numbers represented by the genus of $xy$, every number field — unconditional**: for $F$ a number field,
$Q_0 = x_0x_1$ (`hypForm`) and $T_0 = \langle m\rangle$ nondegenerate with a rational point $\Xi$ ($\Xi_0\Xi_1 = m$),
$$\sum_in(M_i,m) = \prod_\mathfrak p\frac{\beta_\mathfrak p(xy,m)}{1 - N\mathfrak p^{-1}},$$
the sum over the proper classes $M_i$ in the genus of $\mathcal O_F^2$ ($h_F$ of them), $n(M_i,m)$ = `repCount` (the number of
$x\in M_i$ with $x_0x_1 = m$ modulo units). No measures: $\sum_iv^1(M_i) = \rho_F$ (`massIso_uncond`) cancels.
Classically $\beta_\mathfrak p(xy,m) = (1 - N\mathfrak p^{-1})(v_\mathfrak p(m) + 1)$ and the product is the number of integral ideals
dividing $m$ (over $\mathbb Q$: the divisor count $d(m)$). -/
@[kb "siegel1935" "divisor count as the number of representations by the genus of xy (Siegel's formula for xy) [unverified]"]
theorem tsum_repCount_hypForm (T₀ : QuadForm (𝓞 F) 1) (hT : T₀.Nondegenerate)
    (Ξ : RatFrame (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) T₀) :
    ∑' i, repCount (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) T₀ i =
      ENNReal.ofReal (∏' v, NF.localDensityForm v (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) T₀ / lamV v) := by
  classical
  set H := QuadFormsKB.Tamagawa.Measure.Weil.hypForm F with hHdef
  have hH : H.Nondegenerate := nondegenerate_hypForm
  have he : IsIsoVec H (hypE F) := isIsoVec_hypE
  have h := siegelIndefinite_binary_isotropic_uncond H hH he T₀ hT Ξ
  have hm := massIso_uncond H hH he
  rw [tprod_aSO_lamV_hypForm, ENNReal.ofReal_one, one_mul] at hm
  rw [hm, isoBinDensityProduct, ← ENNReal.ofReal_mul' (dedekindZeta_residue_pos F).le] at h
  have hρ := (dedekindZeta_residue_pos F).ne'
  have hc : cInfCorankOne H = ENNReal.ofReal (cF F 2) := by
    rw [cInfCorankOne_eq, hessian_hypForm_det]
    congr 1
    simp
  rw [hc] at h
  set P := ∏' v, NF.localDensityForm v H T₀ / lamV v with hP
  have e1 : |(discr F : ℝ)| ^ (-(1 / 2 : ℝ)) * (dedekindZeta_residue F)⁻¹ * P * dedekindZeta_residue F =
      cF F 2 * P := by
    rw [cF_two]; field_simp
  rw [e1, ENNReal.ofReal_mul (cF_pos' (F := F) 2).le] at h
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 (cF_pos' (F := F) 2)).ne' ENNReal.ofReal_ne_top).mp h

/-- **The divisor count: the numbers represented by the genus of $xy$, every number field — unconditional**: for $F$ a
number field and $m\in\mathcal O_F\setminus0$ represented by $x_0x_1$ over $F$ (a rational point $\Xi$; every $m\ne0$ is, e.g.
$(m,1)$),
$$\sum_in(M_i,m) = \prod_\mathfrak p\bigl(v_\mathfrak p(m) + 1\bigr),$$
the number of integral ideals of $\mathcal O_F$ dividing $m$; the sum is over the proper classes $M_i$ in the genus of
$\mathcal O_F^2$ with the form $x_0x_1$, $n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with $x_0x_1 = m$ modulo the units of
$M_i$), $v_\mathfrak p(m)$ the exponent of $\mathfrak p$ in $m\mathcal O_F$. From `tsum_repCount_hypForm` and
$\beta_\mathfrak p(xy,m) = (v_\mathfrak p(m) + 1)(1 - N\mathfrak p^{-1})$ (`NF.localDensityForm_hyperbolic_unary`, every $\mathfrak p$, dyadic
included). Over $\mathbb Q$: $\#\{(x,y)\in\mathbb Z^2 : xy = m\}/\{\pm1\} = d(m)$, Dirichlet's divisor count. -/
@[kb "siegel1935" "Siegel's formula for xy: the divisor count (Siegel's excluded isotropic binary case) [unverified]"]
theorem tsum_repCount_hypForm_divisors (m : 𝓞 F) (hm : m ≠ 0)
    (Ξ : RatFrame (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) (DVR.unary m)) :
    ∑' i, repCount (QuadFormsKB.Tamagawa.Measure.Weil.hypForm F) (DVR.unary m) i =
      ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F),
        (((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors : ℕ) + 1 : ℝ)) := by
  have hT : (DVR.unary m).Nondegenerate :=
    unary_nondegenerate (by exact_mod_cast (show (m : 𝓞 F) ≠ 0 from hm))
  rw [tsum_repCount_hypForm (DVR.unary m) hT Ξ]
  congr 1
  refine tprod_congr fun v => ?_
  rw [NF.localDensityForm_hyperbolic_unary v m hm, lamV]
  have hl : (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) ≠ 0 := (lamV_pos v).ne'
  rw [mul_div_assoc, div_self hl, mul_one]

end Iso

end QuadFormsKB.Tamagawa.Indefinite
