/-
# The Gan–Hanke–Yu mass formula for special orthogonal groups, odd rank (Gan–Hanke–Yu 2001, Proposition 7.4)

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), §2 (Prop. 2.13), §7
((7.1)–(7.3), Prop. 7.4); J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math.
584 (2005), Theorem 5.1.

Let $k$ be a totally real number field of degree $d$, $V$ a totally definite quadratic space of odd rank $m = 2n+1\ge3$ over
$k$, $G = SO(V)$ and $\Lambda$ a maximal lattice (here $\Lambda = \mathcal O_F^m$ with the form $Q_0$; `F` is Gan–Hanke–Yu's $k$, and the
rank is called `n` in Lean with Gan–Hanke–Yu's $n$ = `n / 2`). Gan–Hanke–Yu's Proposition 7.4:
$$\mathrm{Mass}(\Lambda) = \Big(\frac1{2^{nd}}\,L(M)\,\tau(G)\Big)\prod_{v\in S}\lambda_v,\qquad
L(M) = \prod_{r=1}^n\zeta_k(1-2r)\ \ (7.2),\qquad \tau(G) = 2\ \ (7.3),$$
$$\lambda_v = \frac{q_v^{2n}-1}{2(q_v+1)}\ \ (V_v\cong V_{\delta,-1},\ \delta\in A_v^\times),\qquad
\lambda_v = \frac{q_v^{n}+w}{2}\ \ (V_v\cong V_{\delta,w},\ \delta\notin A_v^\times),$$
and $\lambda_v = 1$ for $v\notin S$ ($V_v\cong V_{\delta,1}$, $\delta\in A_v^\times$). Here $\mathrm{Mass}(\Lambda) = \mathrm{Mass}(K)$ (7.1)
$=\sum_i 1/|\Gamma_i|$, the sum over the $SO$-classes in the genus, i.e. the left side of `theorem51_definite_general`.

**Formalized** as `ghy_prop74` (unconditional), with these readings:
* *$\delta\in A_v^\times$* is `DetUnitSqAt` ($\det\varphi$ a unit times a square; Gan–Hanke–Yu's discriminant is that of the bilinear
  form $\langle x,x\rangle = Q(x)$, i.e. $\det H/2^m$ up to sign), and $w = 1$ iff $t_v = 1$ (the space $V_{\delta,1}$ is the one of
  larger Witt index); `lambdaGHYAt`.
* *Clarification:* $L(M)$ must be read as $|L(M)|$: $\zeta_k(1-2r)$ has sign $(-1)^{rd}$ (e.g. $k = \mathbb Q$, $m = 3$:
  $L(M) = \zeta(-1) = -1/12$, while $\mathrm{Mass}(x_0^2+x_1^2+x_2^2) = 1/24$ for $SO$).
* Mathlib's `dedekindZeta` is the Dirichlet series (no analytic continuation), so $|\zeta_k(1-2r)|$ is written through Hecke's
  functional equation for totally real $k$:
  $|\zeta_k(1-2r)| = |D_k|^{2r-1/2}\big(2(2r-1)!/(2\pi)^{2r}\big)^d\zeta_k(2r)$ (`absZetaNeg`).

*Proof.* `theorem51_definite_general` gives the mass as `theorem51RHSGen`. Placewise,
$\lambda^{\rm Gan–Hanke–Yu}_v = |2|_v^n\,[\widetilde\Lambda_v:\Lambda_v]^n\,\lambda'_v$ (`lambdaGHYAt_eq`, from the dual indices of
`GHYOddDual.lean`: $[\widetilde\Lambda_v:\Lambda_v] = |2|_v^{-1}q^c$, $c = 0, 2, 1$), and $\prod_v|2|_v = 2^{-d}$ (product formula).
-/
import QuadFormsKB.Literature.Hanke2005.GHYOddDual
import QuadFormsKB.Literature.Hanke2005.TheoremFiveOneGeneral

open NumberField IsDedekindDomain Real
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.Tamagawa.LatChange

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The dual index at every place (odd rank) -/

section Dual

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

open Classical in
/-- **The dual index of a maximal lattice of odd rank** (Gan–Hanke–Yu 2001, (6.6), (6.10), (6.13); Shimura 1999, (3.2.1)):
$t_v\in\{1,3\}$ and $[\widetilde\Lambda_v:\Lambda_v] = |2|_v^{-1}q^c$ with $c = 0$ ($\det\varphi$ a unit times a square, $t_v = 1$),
$c = 2$ (unit times a square, $t_v = 3$), $c = 1$ (not a unit times a square). -/
@[kb "ganhankeyu2001" "(6.6), (6.10), (6.13) (the dual index of the maximal lattice, odd rank)"]
theorem dualIndexAt_odd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) :
    (anisoDim v Q₀ = 1 ∨ anisoDim v Q₀ = 3) ∧
      dualIndexAt v Q₀ = ‖(2 : Fv)‖⁻¹ *
        (DVR.q 𝔬 : ℝ) ^ (if DetUnitSqAt v Q₀ then (if anisoDim v Q₀ = 1 then 0 else 2) else 1) := by
  obtain ⟨k, r, h, N, hN, hNM, hNa, hE⟩ :=
    exists_hypSum_shape v n (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ) (maxProp_Qp v Q₀ hQ hmax)
  subst h
  have ht := anisoDim_of_hypSum v Q₀ hQ N hNa hE
  have hr4 : r ≤ 4 := rank_le_four_of_aniso v _ hNa
  have hrodd : r = 1 ∨ r = 3 := by
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨U, hU, hUe⟩ := hE
  set DQ := (NF.Qp v Q₀).hessian.det with hDQ
  set DH := (hypSum N k).hessian.det with hDH
  have hHess := DVR.hessian_eq_of_eval hUe
  have hDHeq : DH = U.det * U.det * DQ := by
    rw [hDH, hHess, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hcoe : ((DH : 𝔬) : Fv) = ((U.det : 𝔬) : Fv) ^ 2 * ((DQ : 𝔬) : Fv) := by
    rw [hDHeq]; push_cast; ring
  have hnormU := norm_coe_unit v hU
  have hs0 : ((U.det : 𝔬) : Fv) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnormU
    exact zero_ne_one hnormU
  have hnormDH : ‖((DH : 𝔬) : Fv)‖ = ‖((DQ : 𝔬) : Fv)‖ := by
    rw [hcoe, norm_mul, norm_pow, hnormU, one_pow, one_mul]
  have hdual : dualIndexAt v Q₀ = ‖dN v N‖⁻¹ := by
    unfold dualIndexAt
    rw [← hDQ, ← hnormDH, hDH, norm_det_hypSum]
  have key := algebraMap_det_eq v Q₀
  rw [← hDQ] at key
  -- Shimura's condition for `Q₀` is Shimura's condition for the kernel
  have hiff : DetUnitSqAt v Q₀ ↔ ∃ c : Fv, c ≠ 0 ∧ ‖dN v N / 2 ^ r * c ^ 2‖ = 1 := by
    rw [← detHyp_hypSum v N k]
    constructor
    · rintro ⟨c, hc0, hc⟩
      refine ⟨c / ((U.det : 𝔬) : Fv), div_ne_zero hc0 hs0, ?_⟩
      rw [map_div₀, map_pow, map_ofNat, key] at hc
      rw [← hc, ← hDH, hcoe]
      congr 1
      field_simp
    · rintro ⟨c, hc0, hc⟩
      refine ⟨c * ((U.det : 𝔬) : Fv), mul_ne_zero hc0 hs0, ?_⟩
      rw [map_div₀, map_pow, map_ofNat, key, ← hc, ← hDH, hcoe]
      congr 1
      ring
  rw [hdual, ht]
  have hfin : ∀ ν : ℕ, ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ ν)⁻¹ →
      ‖dN v N‖⁻¹ = ‖(2 : Fv)‖⁻¹ * (DVR.q 𝔬 : ℝ) ^ ν := fun ν h => by rw [h, mul_inv, inv_inv]
  rcases hrodd with rfl | rfl
  · refine ⟨Or.inl rfl, ?_⟩
    obtain ⟨ν, hν, hnorm⟩ := norm_dN_one v N hN hNM
    have hpar := (detSq_iff_even v ⟨0, rfl⟩ N ν hnorm)
    rw [hfin ν hnorm, if_pos rfl]
    congr 1
    by_cases hd : DetUnitSqAt v Q₀
    · rw [if_pos hd]
      have := hpar.1 (hiff.1 hd)
      have : ν = 0 := by obtain ⟨i, hi⟩ := this; omega
      rw [this]
    · rw [if_neg hd]
      have : ¬ Even ν := fun he => hd (hiff.2 (hpar.2 he))
      have : ν = 1 := by
        rcases (by omega : ν = 0 ∨ ν = 1) with h0 | h1
        · exact absurd ⟨0, by omega⟩ this
        · exact h1
      rw [this]
  · refine ⟨Or.inr rfl, ?_⟩
    have h3 : ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 1)⁻¹ ∨
        ‖dN v N‖ = ‖(2 : Fv)‖ * ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹ := by
      by_cases h2 : IsUnit (2 : 𝔬)
      · exact norm_dN_three_odd v h2 N hN hNM hNa
      · exact norm_dN_three_dyadic v h2 N hNM hNa
    rw [if_neg (show (3 : ℕ) ≠ 1 by decide)]
    rcases h3 with h1 | h2'
    · have hpar := detSq_iff_even v ⟨1, rfl⟩ N 1 h1
      have hd : ¬ DetUnitSqAt v Q₀ := fun hd => by
        obtain ⟨i, hi⟩ := hpar.1 (hiff.1 hd); omega
      rw [hfin 1 h1]; simp only [hd, if_false]
    · have hpar := detSq_iff_even v ⟨1, rfl⟩ N 2 h2'
      have hd : DetUnitSqAt v Q₀ := hiff.2 (hpar.2 ⟨1, rfl⟩)
      rw [hfin 2 h2']; simp only [hd, if_true]

end Dual

/-! ### Gan–Hanke–Yu's local factor -/

open Classical in
/-- **Gan–Hanke–Yu's $\lambda_v$ for odd rank $m = 2n+1$** (Gan–Hanke–Yu 2001, Proposition 7.4, p. 119; Table 4), as a function of $q = q_v$, $n$,
$t = t_v$ and whether the discriminant is a unit ($\delta\in A_v^\times$): $1$ ($\delta$ a unit, $t = 1$, i.e. $v\notin S$);
$(q^{2n}-1)/(2(q+1))$ ($\delta$ a unit, $t = 3$, i.e. $w = -1$); $(q^n+w)/2$ with $w = 1$ for $t = 1$ and $w = -1$ for $t = 3$
($\delta$ not a unit). -/
@[kb "ganhankeyu2001" "Proposition 7.4, p. 119 (λ_v, odd rank)"]
def lambdaGHYOdd (q : ℝ) (k t : ℕ) (unitDisc : Prop) : ℝ :=
  if unitDisc then (if t = 1 then 1 else (q ^ (2 * k) - 1) / (2 * (q + 1)))
  else (if t = 1 then (q ^ k + 1) / 2 else (q ^ k - 1) / 2)

/-- Gan–Hanke–Yu's $\lambda_v$ at a finite place for $Q_0$ ($n$ odd; Gan–Hanke–Yu's $n$ is `n / 2`). -/
def lambdaGHYAt (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n) : ℝ :=
  lambdaGHYOdd (normQ v) (n / 2) (anisoDim v Q₀) (DetUnitSqAt v Q₀)

/-- **Gan–Hanke–Yu's $\lambda_v$ against Hanke's (generalized) $\lambda'_v$:** $\lambda^{\rm Gan–Hanke–Yu}_v = |2|_v^{\,n}\,
[\widetilde\Lambda_v:\Lambda_v]^n\,\lambda'_v$ ($n$ = Gan–Hanke–Yu's $n$ = `n / 2`). -/
theorem lambdaGHYAt_eq (v : HeightOneSpectrum (𝓞 F)) (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n)
    (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    lambdaGHYAt v Q₀ = ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) * lambdaGen v Q₀ := by
  classical
  obtain ⟨ht, hdual⟩ := dualIndexAt_odd v hn hodd Q₀ hQ hmax
  have hq := DensitySD.q_eq v
  have hq1 : 1 < normQ v := one_lt_normQ v
  have hq0 : 0 < normQ v := lt_trans zero_lt_one hq1
  have h2pos : 0 < ‖(2 : v.adicCompletion F)‖ := norm_pos_iff.mpr two_ne_zero
  have hmul : ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) =
      (normQ v) ^ ((if DetUnitSqAt v Q₀ then (if anisoDim v Q₀ = 1 then 0 else 2) else 1) * (n / 2)) := by
    rw [hdual, mul_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2pos.ne'), one_mul, hq, ← pow_mul]
  rw [hmul]
  unfold lambdaGHYAt lambdaGHYOdd lambdaGen
  have hk1 : 1 ≤ n / 2 := by omega
  have hrp : (normQ v) ^ (-((n / 2 : ℕ) : ℝ)) = ((normQ v) ^ (n / 2))⁻¹ := by
    rw [Real.rpow_neg hq0.le, Real.rpow_natCast]
  by_cases hd : DetUnitSqAt v Q₀
  · have hcond : ¬ (Odd n ∧ ¬ DetUnitSqAt v Q₀) := fun h => h.2 hd
    rw [if_pos hd, if_pos hd, if_neg hcond]
    rcases ht with h1 | h3
    · rw [if_pos h1, if_pos h1, zero_mul, pow_zero, one_mul]
      unfold lambdaAt lambdaHanke
      split_ifs <;> simp [h1]
    · have hne : anisoDim v Q₀ ≠ 1 := by omega
      rw [if_neg hne, if_neg hne]
      have hd1 : dualIndexAt v Q₀ ≠ 1 := by
        rw [hdual, if_pos hd, if_neg hne]
        have h2le : ‖(2 : v.adicCompletion F)‖ ≤ 1 := by
          have := norm_two_Fv v (e := 0)
          rw [← map_ofNat (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) 2]
          exact (Valued.toNormedField.norm_le_one_iff).mpr
            ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (2 : v.adicCompletionIntegers F).2)
        have : 1 < ‖(2 : v.adicCompletion F)‖⁻¹ * ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) ^ 2 := by
          rw [hq]
          have : 1 < (normQ v) ^ 2 := one_lt_pow₀ hq1 (by norm_num)
          have : 1 ≤ ‖(2 : v.adicCompletion F)‖⁻¹ := one_le_inv_iff₀.mpr ⟨h2pos, h2le⟩
          nlinarith
        exact this.ne'
      unfold lambdaAt lambdaHanke
      rw [if_neg hd1, h3]
      simp only
      have hrp2 : (normQ v) ^ (-(2 * ((n / 2 : ℕ) : ℝ))) = ((normQ v) ^ (2 * (n / 2)))⁻¹ := by
        rw [Real.rpow_neg hq0.le, show (2 * ((n / 2 : ℕ) : ℝ)) = ((2 * (n / 2) : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_natCast]
      rw [hrp2, mul_comm 2 (n / 2), pow_mul, ← pow_mul, mul_comm (n / 2) 2]
      have hqq : (normQ v) ^ (2 * (n / 2)) ≠ 0 := pow_ne_zero _ hq0.ne'
      field_simp
      ring
  · have hcond : Odd n ∧ ¬ DetUnitSqAt v Q₀ := ⟨hodd, hd⟩
    rw [if_neg hd, if_neg hd, if_pos hcond, one_mul]
    unfold lambdaOddNonUnit
    have hqk : (normQ v) ^ (n / 2) ≠ 0 := pow_ne_zero _ hq0.ne'
    rcases ht with h1 | h3
    · rw [if_pos h1, if_pos h1, hrp]; field_simp
    · have hne : anisoDim v Q₀ ≠ 1 := by omega
      rw [if_neg hne, if_neg hne, hrp]; field_simp

/-! ### $L(M)$ and the global formula -/

/-- **$|\zeta_F(1-2r)|$ through Hecke's functional equation** ($F$ totally real of degree $d$, $r\ge1$):
$|D_F|^{2r-1/2}\big(2\,(2r-1)!/(2\pi)^{2r}\big)^d\,\zeta_F(2r)$. Mathlib's `dedekindZeta` is the Dirichlet series, without
analytic continuation, so the value at the negative odd integer $1-2r$ is given by the functional equation. -/
@[kb "ganhankeyu2001" "(7.2) (ζ_k(1 − 2r), through Hecke's functional equation for totally real k)"]
def absZetaNeg (F : Type) [Field F] [NumberField F] (r : ℕ) : ℝ :=
  |(discr F : ℝ)| ^ (2 * (r : ℝ) - 1 / 2) *
    (2 * (Nat.factorial (2 * r - 1) : ℝ) / (2 * π) ^ (2 * r)) ^ Module.finrank ℚ F *
      NFEuler.dedekindZetaR F (2 * (r : ℝ))

/-- **Gan–Hanke–Yu's $|L(M)|$ for odd rank $2k+1$** (Gan–Hanke–Yu 2001, (7.2)): $\prod_{r=1}^k|\zeta_F(1-2r)|$. -/
@[kb "ganhankeyu2001" "(7.2) (L(M) for m = 2n + 1, in absolute value)"]
def lMotiveOdd (F : Type) [Field F] [NumberField F] (k : ℕ) : ℝ :=
  ∏ r ∈ Finset.range k, absZetaNeg F (r + 1)

theorem lMotiveOdd_eq (k : ℕ) :
    lMotiveOdd F k = (2 : ℝ) ^ (k * Module.finrank ℚ F) * |(discr F : ℝ)| ^ (k ^ 2) *
      ∏ j ∈ Finset.range k, (|(discr F : ℝ)| ^ (1 / 2 : ℝ) *
        ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1))) ^ Module.finrank ℚ F *
          NFEuler.dedekindZetaR F (2 * ((j : ℝ) + 1))) := by
  have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  induction k with
  | zero => simp [lMotiveOdd]
  | succ k ih =>
    unfold lMotiveOdd at ih ⊢
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
    unfold absZetaNeg
    have e1 : |(discr F : ℝ)| ^ (2 * ((k + 1 : ℕ) : ℝ) - 1 / 2) =
        |(discr F : ℝ)| ^ (2 * k + 1) * |(discr F : ℝ)| ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hD]
      congr 1; push_cast; ring
    have e2 : (2 * ((k + 1 : ℕ) : ℝ)) = 2 * ((k : ℝ) + 1) := by push_cast; ring
    rw [e1, e2, mul_div_assoc, mul_pow]
    rw [show (k + 1) * Module.finrank ℚ F = k * Module.finrank ℚ F + Module.finrank ℚ F by ring,
      show (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) by ring, pow_add, pow_add]
    ring

/-- **The product of Gan–Hanke–Yu's local factors:** $\prod_v\lambda^{\rm Gan–Hanke–Yu}_v = 2^{-nd}\,[\widetilde\Lambda:\Lambda]^n\prod_v\lambda'_v$. -/
theorem tprod_lambdaGHYAt (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) :
    ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYAt v Q₀ =
      ((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * (∏' v, dualIndexAt v Q₀) ^ (n / 2) *
        ∏' v, lambdaGen v Q₀ := by
  have h1 := hasFiniteMulSupport_norm_two (F := F)
  have h2 := hasFiniteMulSupport_dualIndexAt Q₀ hQ
  have h3 := hasFiniteMulSupport_lambdaGen Q₀ hQ
  have h1' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n / 2) :=
    h1.pow (n / 2)
  have h2' : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => dualIndexAt v Q₀ ^ (n / 2) :=
    h2.pow (n / 2)
  have hA : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) * lambdaGen v Q₀ := (h1'.mul h2').mul h3
  have hB : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) := h1'.mul h2'
  rw [tprod_congr fun v => lambdaGHYAt_eq v hn hodd Q₀ hQ hmax,
    tprod_eq_finprod (L := SummationFilter.unconditional _) hA,
    finprod_mul_distrib (f := fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2)) (g := fun v => lambdaGen v Q₀) hB h3,
    finprod_mul_distrib (f := fun v : HeightOneSpectrum (𝓞 F) => ‖(2 : v.adicCompletion F)‖ ^ (n / 2))
      (g := fun v => dualIndexAt v Q₀ ^ (n / 2)) h1' h2',
    ← finprod_pow h1, ← finprod_pow h2,
    ← tprod_eq_finprod (L := SummationFilter.unconditional _) h1,
    ← tprod_eq_finprod (L := SummationFilter.unconditional _) h2,
    ← tprod_eq_finprod (L := SummationFilter.unconditional _) h3, tprod_norm_two, inv_pow, ← pow_mul,
    mul_comm (Module.finrank ℚ F) (n / 2)]

/-- **Gan–Hanke–Yu 2001, Proposition 7.4** (odd rank $m = 2n+1\ge3$; totally real $k$ = `F` of degree $d$; $V$ totally definite;
$\Lambda = \mathcal O_F^m$ maximal): $\mathrm{Mass}(\Lambda) = \big(2^{-nd}\,|L(M)|\,\tau(G)\big)\prod_v\lambda_v$ with $\tau(G) = 2$
(7.3), $|L(M)| = \prod_{r=1}^n|\zeta_F(1-2r)|$ (`lMotiveOdd`, through the functional equation) and Gan–Hanke–Yu's $\lambda_v$
(`lambdaGHYAt`, equal to $1$ off $S$). The mass is $\sum_i1/|\Gamma_i|$ over the $SO$-classes of the genus. **Unconditional.** -/
@[kb "ganhankeyu2001" "Proposition 7.4, p. 119 (with (7.1)–(7.3))"]
theorem ghy_prop74 [IsTotallyReal F] (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((2 : ℝ) ^ ((n / 2) * Module.finrank ℚ F))⁻¹ * lMotiveOdd F (n / 2) * 2 *
        ∏' v : HeightOneSpectrum (𝓞 F), lambdaGHYAt v Q₀) := by
  classical
  rw [theorem51_definite_general hn Q₀ hQ hpd hmax, tprod_lambdaGHYAt hn hodd Q₀ hQ hmax]
  congr 1
  unfold theorem51RHSGen
  dsimp only
  have hB : (∏ w : {w : InfinitePlace F // w.IsReal}, bPhi n (rAt Q₀ w)) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [rAt_eq_zero Q₀ hQ hpd w.1, bPhi_zero]
  have hC : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [hB, hC, pow_zero, if_pos hodd]
  obtain ⟨k, rfl⟩ := hodd
  have e1 : (2 * k + 1 - 1) ^ 2 / 4 = k ^ 2 := by
    rw [show (2 * k + 1 - 1) ^ 2 = 4 * k ^ 2 by rw [Nat.add_sub_cancel]; ring]; omega
  have e2 : (2 * k + 1 - 1) / 2 = k := by omega
  have e3 : (2 * k + 1) / 2 = k := by omega
  have hI : 0 ≤ ∏' v, dualIndexAt v Q₀ := (tprod_dualIndexAt_pos Q₀ hQ).le
  have fI : (∏' v, dualIndexAt v Q₀) ^ ((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) = (∏' v, dualIndexAt v Q₀) ^ k := by
    rw [show (((2 * k + 1 : ℕ) : ℝ) - 1) / 2 = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
  have f2 : (2 : ℝ) ^ (-((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ)) =
      ((2 : ℝ) ^ (k * Module.finrank ℚ F))⁻¹ := by
    rw [show -((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) * (Module.finrank ℚ F : ℝ) = -((k * Module.finrank ℚ F : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp only [e1, e2, e3]
  rw [fI, f2, lMotiveOdd_eq]
  have h2 : (0 : ℝ) < 2 ^ (k * Module.finrank ℚ F) := by positivity
  field_simp

end QuadFormsKB.Hanke2005
