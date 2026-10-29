/-
# The hyperbolic plane $xy$ over $\mathbb Q$: one class, $v^1(\mathbb Z^2) = 1$, and the divisor count

**Layer:** number fields with class number one, then $\mathbb Q$. Notation as in
`Indefinite/SiegelBinaryIso.lean`: $H = x_0x_1$ (`hypForm`), $L = \mathcal O_F^2$, the proper classes $M_i$ in the genus of $L$
(`DC`), $n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with $x_0x_1 = m$ modulo the unit group of $M_i$), $v^1(M_i)$ =
`unitVolumeIso` (the norm-one unit volume).

**Statements (unconditional):**
* `dc_hypForm_eq_one`, `subsingleton_DC_hypForm`: if $\mathcal O_F$ is a principal ideal domain, the genus of $L$ for $H$ has
  **one proper class**. Through $\mathbb A_f^\times\cong SO(H)(\mathbb A_f)$ (`hypFinEquiv`, $t\mapsto\mathrm{diag}(t,t^{-1})$), which
  carries $\hat{\mathcal O}^\times$ onto $SO(\hat L)$ and $F^\times$ onto $SO(H)(F)$, the proper classes are
  $F^\times\backslash\mathbb A_f^\times/\hat{\mathcal O}^\times$, the ideal class group (`ideleIdeal`).
* `unitVolumeIso_hypForm_of_isPrincipalIdealRing`: then $v^1(L) = \rho_F$ (from the norm-one mass formula `massIso_uncond`),
  and **`unitVolumeIso_hypForm_rat`**: $v^1(\mathbb Z^2) = 1$ over $\mathbb Q$ ($\rho_\mathbb Q = 1$).
* **`tprod_count_add_one_rat`**: for $m\in\mathcal O_\mathbb Q\setminus0$, $\prod_p(v_p(m)+1) = d(|m|)$, the number of positive
  divisors (Mathlib's `Nat.card_divisors`; the primes of $\mathcal O_\mathbb Q$ are reindexed by the rational primes,
  `Rat.HeightOneSpectrum.primesEquiv`).
* **`tsum_repCount_hypForm_rat`**, **`repCount_hypForm_rat`**: for $m\in\mathbb Z\setminus0$,
  $n(\mathbb Z^2,m) = \#\{(x,y)\in\mathbb Z^2 : xy = m\}/\{\pm1\} = d(|m|)$, Dirichlet's divisor count, as the corank-one
  Siegel formula for $xy$ (`tsum_repCount_hypForm_divisors`) with one class.
* **`siegel_hypForm_rat_explicit`**: Siegel's formula for $xy$ over $\mathbb Q$ with $v^1(\mathbb Z^2) = 1$ inserted.
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelBinaryIso
import QuadFormsKB.Tamagawa.Classical.Helpers

open MeasureTheory Set Matrix MulAction
open scoped ENNReal nonZeroDivisors

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Indefinite LocalDensity

/-! ### One proper class for $xy$ when $\mathcal O_F$ is a principal ideal domain -/

section OneClass

variable {F : Type} [Field F] [NumberField F]

/-- The finite part of $\Phi(\xi) = \mathrm{diag}(\xi,\xi^{-1})$, $\xi\in F^\times$, is `hypFinEquiv` of the principal idele. -/
theorem hypFinEquiv_finDiag (γ : Fˣ) :
    hypFinEquiv F (finDiag γ) = (diagSOAdele (hypForm F) (hypSOF γ)).2 := by
  rw [← hypEquiv_diagUnits, ← finPart_diagUnits]
  rfl

/-- **One proper class for $xy$ if $\mathcal O_F$ is a principal ideal domain**: every $b\in SO(H)(\mathbb A_f)$ is in the
double coset of $1$. Write $b = \mathrm{diag}(t,t^{-1})$, $t\in\mathbb A_f^\times$; the ideal of $t$ is $(\gamma)$,
$\gamma\in F^\times$, so $t = \gamma u$ with $u\in\hat{\mathcal O}^\times$, and $b = \mathrm{diag}(\gamma,\gamma^{-1})\cdot1\cdot
\mathrm{diag}(u,u^{-1})$ with the last factor in $SO(\hat L)$. -/
theorem dc_hypForm_eq_one [IsPrincipalIdealRing (𝓞 F)] (b : SOAf (hypForm F)) :
    (⟦b⟧ : DC (hypForm F)) = ⟦1⟧ := by
  set t := (hypFinEquiv F).symm b with ht
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff
    ((ideleIdeal F t : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)).1 inferInstance
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact Units.ne_zero _ hx
  set γ : Fˣ := Units.mk0 x hx0 with hγ
  have hprin : ideleIdeal F (finDiag γ) = ideleIdeal F t := by
    rw [ideleIdeal_finDiag]
    exact Units.ext (by rw [coe_toPrincipalIdeal, hγ, Units.val_mk0, hx])
  set u := (finDiag γ)⁻¹ * t with hu
  have huO : u ∈ OHatUnits F := by
    rw [← ideleIdeal_eq_one_iff, hu, map_mul, map_inv, hprin, inv_mul_cancel]
  have hk : hypFinEquiv F u ∈ KSO (hypForm F) := by
    have : u ∈ hypFinEquiv F ⁻¹' (KSO (hypForm F) : Set (SOAf (hypForm F))) := by
      rw [hypFinEquiv_preimage_KSO]; exact huO
    exact this
  have hb : b = (diagSOAdele (hypForm F) (hypSOF γ)).2 * 1 * hypFinEquiv F u := by
    rw [mul_one, ← hypFinEquiv_finDiag, ← map_mul, hu, mul_inv_cancel_left, ht]
    exact ((hypFinEquiv F).apply_symm_apply b).symm
  exact (Quotient.sound (s := dcSetoid (hypForm F)) (a := 1) (b := b)
    ⟨_, ⟨hypSOF γ, rfl⟩, _, hk, hb⟩).symm

/-- **One proper class in the genus of $xy$** when $\mathcal O_F$ is a principal ideal domain. -/
theorem subsingleton_DC_hypForm [IsPrincipalIdealRing (𝓞 F)] : Subsingleton (DC (hypForm F)) := by
  refine ⟨fun i j => ?_⟩
  induction i using Quotient.inductionOn with | h b => ?_
  induction j using Quotient.inductionOn with | h b' => ?_
  rw [dc_hypForm_eq_one b, dc_hypForm_eq_one b']

/-- A sum over the proper classes of $xy$ with one class is the value at the class of $1$. -/
theorem tsum_DC_hypForm [IsPrincipalIdealRing (𝓞 F)] (f : DC (hypForm F) → ℝ≥0∞) (i : DC (hypForm F)) :
    ∑' j, f j = f i := by
  have := subsingleton_DC_hypForm (F := F)
  exact tsum_eq_single i fun j hj => absurd (Subsingleton.elim j i) hj

/-- **The norm-one unit volume of $xy$ with class number one**: $v^1(L) = \rho_F$ for the single class ($\rho_F$ the residue
of $\zeta_F$ at $s = 1$), by the norm-one mass formula `massIso_uncond` ($\prod_\mathfrak p\alpha_\mathfrak p/\lambda_\mathfrak p = 1$ for $xy$). -/
theorem unitVolumeIso_hypForm_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 F)] (i : DC (hypForm F)) :
    unitVolumeIso (hypForm F) nondegenerate_hypForm isIsoVec_hypE i = ENNReal.ofReal (dedekindZeta_residue F) := by
  have hm := massIso_uncond (hypForm F) nondegenerate_hypForm (isIsoVec_hypE (F := F))
  rw [tprod_aSO_lamV_hypForm, ENNReal.ofReal_one, one_mul, tsum_DC_hypForm _ i] at hm
  exact hm

end OneClass

/-! ### Over $\mathbb Q$ -/

section Rat

/-- $\mathcal O_\mathbb Q$ is a principal ideal domain ($\mathcal O_\mathbb Q\cong\mathbb Z$, Mathlib's `Rat.ringOfIntegersEquiv`); the
same instance as in `Tamagawa/SiegelAllRanks.lean`, which this file does not import. -/
instance isPrincipalIdealRing_ringOfIntegers_rat' : IsPrincipalIdealRing (𝓞 ℚ) :=
  IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective

/-- **$v^1(\mathbb Z^2) = 1$ for $xy$ over $\mathbb Q$ — unconditional**: the genus of $\mathbb Z^2$ for $x_0x_1$ has one proper class
(`subsingleton_DC_hypForm`), and its norm-one unit volume, the covolume of the unit group $\{\pm1\}$ in
$SO(H)(\mathbb R)\cong\mathbb R^\times$ for Weil's archimedean measure restricted to the shell $\{1\le|t|<e\}$
(`unitVolumeIso`), is $1$. From the norm-one mass formula `massIso_uncond` and $\rho_\mathbb Q = 1$. -/
@[kb "weil1982" "§3.2 and Thm 3.2.1 (τ(G_m) = 1): the norm-one unit volume of xy over ℚ [unverified page]"]
theorem unitVolumeIso_hypForm_rat (i : DC (hypForm ℚ)) :
    unitVolumeIso (hypForm ℚ) nondegenerate_hypForm isIsoVec_hypE i = 1 := by
  rw [unitVolumeIso_hypForm_of_isPrincipalIdealRing, dedekindZeta_residue_rat, ENNReal.ofReal_one]

/-- **$\operatorname{ord}_p(m)$ over $\mathcal O_\mathbb Q$ is the exponent of $p$ in $|m|$**: the multiplicity of the prime
$\mathfrak p$ of $\mathcal O_\mathbb Q$ in $(m)$ is the exponent of $p$ = `natGenerator 𝔭` in the factorization of
$|m|\in\mathbb N$ ($m$ read in $\mathbb Z$ by `Rat.ringOfIntegersEquiv`). -/
theorem count_factors_span_rat {m : 𝓞 ℚ} (hm : m ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors =
      (Rat.ringOfIntegersEquiv m).natAbs.factorization (Rat.HeightOneSpectrum.natGenerator v) := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  set p := Rat.HeightOneSpectrum.natGenerator v with hp
  set n := (Rat.ringOfIntegersEquiv m).natAbs with hn
  have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hn0 : n ≠ 0 := by
    rw [hn, Int.natAbs_ne_zero]
    exact (map_ne_zero_iff _ Rat.ringOfIntegersEquiv.injective).2 hm
  have key : ∀ k, m ∈ v.asIdeal ^ k ↔ p ^ k ∣ n := fun k => by
    rw [← Ideal.apply_mem_of_equiv_iff (f := e), Ideal.map_pow, ← Rat.HeightOneSpectrum.span_natGenerator,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← Nat.cast_pow, Int.natCast_dvd,
      Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  obtain ⟨h1, h2⟩ := NF.mem_pow_count v hm
  rw [key, hpp.pow_dvd_iff_le_factorization hn0] at h1
  rw [key, hpp.pow_dvd_iff_le_factorization hn0] at h2
  omega

/-- **$\prod_p(v_p(m)+1) = d(|m|)$ over $\mathbb Q$**: for $m\in\mathcal O_\mathbb Q\setminus0$, the product over the primes
$\mathfrak p$ of $\mathcal O_\mathbb Q$ of $\operatorname{ord}_\mathfrak p(m) + 1$ is the number of positive divisors of $|m|$ ($m$ read in
$\mathbb Z$ by `Rat.ringOfIntegersEquiv`; Mathlib's `Nat.card_divisors`). -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie: the number of divisors d(n) = ∏(a_p + 1) [unverified locator]"]
theorem tprod_count_add_one_rat {m : 𝓞 ℚ} (hm : m ≠ 0) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ),
        (((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors : ℕ) + 1 : ℝ) =
      ((Rat.ringOfIntegersEquiv m).natAbs.divisors.card : ℝ) := by
  classical
  set n := (Rat.ringOfIntegersEquiv m).natAbs with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Int.natAbs_ne_zero]
    exact (map_ne_zero_iff _ Rat.ringOfIntegersEquiv.injective).2 hm
  set f : Nat.Primes → ℝ := fun p => ((n.factorization p : ℕ) : ℝ) + 1 with hf
  have h1 : ∏' v : HeightOneSpectrum (𝓞 ℚ),
      (((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {m})).factors : ℕ) + 1 : ℝ) =
      ∏' v : HeightOneSpectrum (𝓞 ℚ), f (Rat.HeightOneSpectrum.primesEquiv v) :=
    tprod_congr fun v => by rw [count_factors_span_rat hm v]; rfl
  have hS : ∀ p ∉ (n.primeFactors.subtype Nat.Prime : Finset Nat.Primes), f p = 1 := fun p hp => by
    have : (p : ℕ) ∉ n.primeFactors := fun h => hp (Finset.mem_subtype.2 h)
    rw [hf]
    simp only
    rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization]), Nat.cast_zero, zero_add]
  have h2 : ∏' p : Nat.Primes, f p = ∏ p ∈ (n.primeFactors.subtype Nat.Prime : Finset Nat.Primes), f p :=
    tprod_eq_prod hS
  rw [h1, (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tprod_eq f, h2, Nat.card_divisors hn0]
  push_cast
  exact Finset.prod_subtype_of_mem (fun p : ℕ => ((n.factorization p : ℕ) : ℝ) + 1)
    fun p hp => Nat.prime_of_mem_primeFactors hp

end Rat

/-! ### The divisor count -/

section Frame

variable {F : Type} [Field F] [NumberField F]

/-- **The rational point $\Xi = (m,1)$ of $x_0x_1 = m$**, a rational frame of $\langle m\rangle$ in $H$. Parameter: `m`. -/
def ratFrameHypUnary (m : 𝓞 F) : RatFrame (hypForm F) (DVR.unary m) :=
  ⟨Matrix.of ![![algebraMap (𝓞 F) F m], ![1]], by
    ext i j
    fin_cases i; fin_cases j
    simp [QuadForm.compMat, QuadForm.ofUpper, QuadForm.map, QuadForm.diag, QuadForm.evalIn, DVR.unary,
      DVR.hyperbolic, Fin.sum_univ_two]⟩

end Frame

/-- **The number of representations of $m$ by $xy$ over $\mathbb Q$, summed over the genus — unconditional**: for
$m\in\mathbb Z\setminus0$,
$$\sum_in(M_i,m) = d(|m|),$$
the number of positive divisors of $|m|$; the sum is over the proper classes $M_i$ in the genus of $\mathbb Z^2$ for
$x_0x_1$ (one class, `subsingleton_DC_hypForm`), $n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with $x_0x_1 = m$ modulo the
unit group of $M_i$). From `tsum_repCount_hypForm_divisors` and `tprod_count_add_one_rat`. -/
@[kb "siegel1935" "Siegel's formula for xy over ℚ: the divisor count d(|m|) (Siegel's excluded isotropic binary case) [unverified]"]
theorem tsum_repCount_hypForm_rat {m : ℤ} (hm : m ≠ 0) :
    ∑' i, Indefinite.repCount (hypForm ℚ) (DVR.unary (m : 𝓞 ℚ)) i = (m.natAbs.divisors.card : ℝ≥0∞) := by
  have hm' : (m : 𝓞 ℚ) ≠ 0 := by
    intro h
    apply hm
    have := congrArg Rat.ringOfIntegersEquiv h
    simpa using this
  rw [tsum_repCount_hypForm_divisors (m : 𝓞 ℚ) hm' (ratFrameHypUnary _), tprod_count_add_one_rat hm',
    map_intCast, ENNReal.ofReal_natCast]
  simp

/-- **Dirichlet's divisor count as the number of representations by $xy$ — unconditional**: for $m\in\mathbb Z\setminus0$ and
the (single) proper class $M_i$ in the genus of $\mathbb Z^2$ for $x_0x_1$,
$$n(M_i,m) = \#\{(x,y)\in\mathbb Z^2 : xy = m\}/\{\pm1\} = d(|m|),$$
$n(M_i,m)$ = `repCount` (the number of $x\in M_i$ with $x_0x_1 = m$ modulo the unit group of $M_i$), $d(|m|)$ the number of
positive divisors of $|m|$. Siegel's formula for $xy$ (corank one) with one class and $v^1(\mathbb Z^2) = 1$. -/
@[kb "siegel1935" "Siegel's formula for xy over ℚ, one class: n(ℤ², m) = d(|m|) [unverified]"]
theorem repCount_hypForm_rat {m : ℤ} (hm : m ≠ 0) (i : DC (hypForm ℚ)) :
    Indefinite.repCount (hypForm ℚ) (DVR.unary (m : 𝓞 ℚ)) i = (m.natAbs.divisors.card : ℝ≥0∞) := by
  rw [← tsum_repCount_hypForm_rat hm, tsum_DC_hypForm _ i]

/-- **Siegel's formula for $xy$ over $\mathbb Q$ with $v^1(\mathbb Z^2) = 1$ — unconditional**: for $T_0 = \langle m\rangle$ a
nondegenerate form in one variable over $\mathcal O_\mathbb Q$ with a rational point $\Xi$ of $x_0x_1 = m$,
$$c^{(1)}_\infty(xy)\sum_in(M_i,m) = \prod_p\frac{\beta_p(xy,m)}{1 - p^{-1}},$$
$c^{(1)}_\infty$ = `cInfCorankOne`, the right side `isoBinDensityProduct` ($|d_\mathbb Q| = 1$, $\rho_\mathbb Q = 1$). This is
`siegelIndefinite_binary_isotropic_uncond` with $\sum_iv^1(M_i) = 1$ (`unitVolumeIso_hypForm_rat`). -/
@[kb "siegel1935" "Hauptsatz for n = 2, m = 1, isotropic binary forms, xy over ℚ [unverified]"]
theorem siegel_hypForm_rat_explicit (T₀ : QuadForm (𝓞 ℚ) 1) (hT : T₀.Nondegenerate) (Ξ : RatFrame (hypForm ℚ) T₀) :
    cInfCorankOne (hypForm ℚ) * ∑' i, Indefinite.repCount (hypForm ℚ) T₀ i =
      ENNReal.ofReal (isoBinDensityProduct (hypForm ℚ) T₀) := by
  have h := siegelIndefinite_binary_isotropic_uncond (hypForm ℚ) nondegenerate_hypForm isIsoVec_hypE T₀ hT Ξ
  simp only [tsum_DC_hypForm _ (⟦1⟧ : DC (hypForm ℚ)), unitVolumeIso_hypForm_rat, mul_one] at h ⊢
  exact h

end QuadFormsKB.Tamagawa.Classical
