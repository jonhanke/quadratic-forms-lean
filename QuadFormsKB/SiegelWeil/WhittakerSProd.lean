/-
# The Euler product of the local Whittaker integrals at general $s$
**Layer:** local (one finite place) and global bookkeeping (Euler products over the finite places of a number field $F$).

**Setting.** $Q = \sum_{i<n}a_ix_i^2$, $n = 2m \ge 2$ (0-based indices), $\varphi_v = \mathbf 1_{\mathcal O_v^n}$, $s_0 = m - 1$, $s \in \mathbb C$,
$X = q_v^{-(s-s_0)}$, and $W_v(t, s)$ = `whittakerVS` the local Whittaker integral of the standard section at $s$
(`SiegelWeil/WhittakerS.lean`). A place is *good* (`IsGoodV`) if $d_v = 0$, $v \nmid 2$ and every $a_i$ is a unit.

**Results.**
* **`whittakerVS_eq_of_good`**: at a good place and for a unit $t \in \mathcal O_v^\times$, the truncations $T_0(t) = 1$ and
  $T_j(t) = \beta_v(t)$ ($j \ge 1$), so
  $$W_v(t, s) = 1 + X\,(\beta_v(t) - 1).$$
* **`whittakerVS_eq_lFactor_of_good`**: with $\beta_v(t) = 1 - \chi_vq_v^{-m}$ (Hanke 2004, Table 1; `localDensity_even_unit_of_unimodular`),
  $\chi_v = \chi((-1)^mD)$ the quadratic character of the residue field (`chiDisc`),
  $$W_v(t, s) = 1 - \chi_v\,q_v^{-(s+1)} = L_v(s+1, \chi_V)^{-1},$$
  the inverse Euler factor of the quadratic character of $V$ at $s + 1$.
* **`multipliable_whittakerVS`** (global): for $Q = \sum_ib_ix_i^2$ with $b_i \in \mathcal O_F\setminus 0$, $t \in \mathcal O_F\setminus 0$ and
  $\operatorname{Re}s > 0$, the Euler product $\prod_{v<\infty}W_v(t, s)$ converges absolutely (`Multipliable`; the factors are
  $1 + O(N\mathfrak p^{-(\operatorname{Re}s+1)})$), and **`hasProd_whittakerVS_s₀`**: at $s = s_0$ its value is
  $C_f\prod_v\beta_v(t)$ (`hasProd_whittakerV`).

This is the finite-place half of the Euler product of the Fourier coefficients off $s_0$; the archimedean Whittaker integral off
$s_0$ and the global unfolding remain open.

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Kudla (2008), §1 [unverified]; Yang, J. Number Theory 72 (1998)
[unverified]; Hanke (2004), Table 1, p. 363 (the counts mod $\mathfrak p$).
-/
import QuadFormsKB.SiegelWeil.WhittakerS
import QuadFormsKB.SiegelWeil.GlobalWhittaker
import QuadFormsKB.SiegelWeil.Eisenstein
import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.LocalDensity.DVRUnimodular

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

variable {F : Type} [Field F] [NumberField F]

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-! ### Elementary facts at a good place -/

lemma not_π_dvd_of_valued_eq_one {z : 𝔬} (h : Valued.v (z : Fv) = 1) : ¬ LocalDensity.NF.π v ∣ z := by
  intro hd
  have h1 := (LocalDensity.NF.mem_span_π_pow v 1 z).mp (by
    rw [pow_one]; exact Ideal.mem_span_singleton.mpr hd)
  rw [h, ← exp_zero, exp_le_exp] at h1
  omega

/-- $q_v = |\varpi_v|_v^{-1}$ is the absolute norm $N\mathfrak p_v$. -/
lemma qV_eq : qV v = (Ideal.absNorm v.asIdeal : ℝ) := by
  have hx : HN.ϖ v ≠ 0 := HN.ϖ_ne_zero v
  have hn : ‖HN.ϖ v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v (HN.ϖ v)) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valued.v).ne_zero_iff.mpr hx)]
    push_cast; rfl
  have hv : Valued.v (HN.ϖ v) = exp (-1 : ℤ) := by simpa using valued_ϖ_zpow v 1
  rw [qV, hn, hv, log_exp, zpow_neg, zpow_one, inv_inv]

lemma not_π_dvd_two_of_good (hg : IsGoodV v a) : ¬ LocalDensity.NF.π v ∣ 2 :=
  not_π_dvd_of_valued_eq_one v (by rw [show ((2 : 𝔬) : Fv) = 2 from rfl]; exact hg.2.1)

lemma not_π_dvd_aO_of_good (hg : IsGoodV v a) (i : Fin (2 * m)) :
    ¬ LocalDensity.NF.π v ∣ aO v a (fun i => (hg.2.2 i).le) i :=
  not_π_dvd_of_valued_eq_one v (show Valued.v ((aO v a (fun i => (hg.2.2 i).le) i : 𝔬) : Fv) = 1 from hg.2.2 i)

lemma cB_eq_one_of_good (hg : IsGoodV v a) : (localDataV v).cB a = 1 := by
  unfold LocalData.cB
  refine Finset.prod_eq_one fun i _ => ?_
  rw [md_eq_one v (by rw [map_mul, hg.2.1, hg.2.2 i, one_mul])]
  simp

lemma vol_eq_one_of_good (hg : IsGoodV v a) : (selfDualV v).real (latticeV v 0) = 1 := by
  rw [selfDualV_real_latticeV, hg.1]; simp

lemma repCount_level_zero {n : ℕ} (Q : QuadForm 𝔬 n) (π t : 𝔬) : LocalDensity.DVR.repCount Q π 0 t = 1 := by
  have : Subsingleton (𝔬 ⧸ Ideal.span {π ^ 0}) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
  unfold LocalDensity.DVR.repCount
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- **$T_0(t) = 1$ at a good place** (every $t \in \mathcal O_v$). -/
theorem whittakerTr_zero_of_good (hm : 0 < m) (hg : IsGoodV v a) (t : 𝔬) : whittakerTr v a (t : Fv) 0 = 1 := by
  rw [whittakerTr_eq v a hm (fun i => (hg.2.2 i).le) t 0 (by rw [hg.1]), gammaV_eq_one_of_good hg,
    cB_eq_one_of_good v a hg, vol_eq_one_of_good v a hg, Nat.zero_sub, repCount_level_zero]
  simp

/-- **$T_j(t) = \beta_v(t)$ for $j \ge 1$ at a good place and a unit $t$** (no Zero-type solutions; Good-type counts are
constant from level $1$, Hanke 2004, Lemma 3.2). -/
theorem whittakerTr_of_good_unit (hm : 0 < m) (hg : IsGoodV v a) (t : 𝔬) (ht : Valued.v (t : Fv) = 1) (j : ℕ)
    (hj : 1 ≤ j) :
    whittakerTr v a (t : Fv) j = (LocalDensity.DVR.localDensity (QO v a (fun i => (hg.2.2 i).le))
      (LocalDensity.NF.π v) t : ℂ) := by
  set ha : ∀ i, Valued.v (a i : Fv) ≤ 1 := fun i => (hg.2.2 i).le
  set π := LocalDensity.NF.π v
  have hπ : Irreducible π := LocalDensity.NF.irreducible_π v
  have h2 : ¬ π ∣ 2 := not_π_dvd_two_of_good v a hg
  have hai : ∀ i, ¬ π ∣ aO v a ha i := not_π_dvd_aO_of_good v a hg
  have htπ : ¬ π ∣ t := not_π_dvd_of_valued_eq_one v ht
  have htπ2 : ¬ π ^ 2 ∣ t := fun h => htπ (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  have hd : diffExp v = 0 := hg.1
  rw [whittakerTr_eq v a hm ha t j (by rw [hd]; omega), gammaV_eq_one_of_good hg,
    cB_eq_one_of_good v a hg, vol_eq_one_of_good v a hg]
  simp only [hd, Nat.sub_zero]
  have hrep : LocalDensity.DVR.repCount (QO v a ha) π j t =
      LocalDensity.DVR.repCountOf (QO v a ha) π j t (fun x => ¬ LocalDensity.DVR.IsZeroType π j x) := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      rw [LocalDensity.DVR.repCount_one_eq_nonZero_add _ π hπ t]
      simp [htπ]
    · rw [show QO v a ha = QuadForm.diag (aO v a ha) from rfl, LocalDensity.DVR.repCount_eq_zero_add_nonZero _ π hπ,
        LocalDensity.DVR.repCountOf_eq_zero_of_not_dvd _ π ∅ 0
          (LocalDensity.DVR.isJordanFormW_diag_unit (aO v a ha) hπ hai) t j 2 le_rfl hj2 htπ2
          (LocalDensity.DVR.IsZeroType π j) (fun x hx i _ => hx i), zero_add]
  have hβ := LocalDensity.DVR.localDensity_diag_of_not_sq_dvd (aO v a ha) π hπ h2 hai t htπ2
  rw [hrep, show QO v a ha = QuadForm.diag (aO v a ha) from rfl, hβ,
    ← LocalDensity.DVR.normalized_nonZero_diag (aO v a ha) π hπ h2 hai t j hj]
  simp

/-! ### The Whittaker integral at $s$ at a good place -/

/-- **$W_v(t, s) = 1 + X(\beta_v(t) - 1)$ at a good place**, $t \in \mathcal O_v^\times$, every $s \in \mathbb C$ ($X = q_v^{-(s-s_0)}$). -/
@[kb "kudla2008" "§1 (the unramified local Whittaker function) [unverified]; weil1965 Ch. II [unverified]"]
theorem whittakerVS_eq_of_good (hm : 0 < m) (hg : IsGoodV v a) (t : 𝔬) (ht : Valued.v (t : Fv) = 1) (s : ℂ) :
    whittakerVS v a (t : Fv) s = 1 + Xs (m := m) v s * ((LocalDensity.DVR.localDensity
      (QO v a (fun i => (hg.2.2 i).le)) (LocalDensity.NF.π v) t : ℂ) - 1) := by
  have hJ : ∀ j, 1 ≤ j → whittakerTr v a (t : Fv) j = whittakerTr v a (t : Fv) 1 := fun j hj => by
    rw [whittakerTr_of_good_unit v a hm hg t ht j hj, whittakerTr_of_good_unit v a hm hg t ht 1 le_rfl]
  have hev : ∀ k, 1 ≤ k → whittakerTrS v a (t : Fv) s k = 1 + Xs (m := m) v s * ((LocalDensity.DVR.localDensity
      (QO v a (fun i => (hg.2.2 i).le)) (LocalDensity.NF.π v) t : ℂ) - 1) := by
    intro k hk
    rw [whittakerTrS_eq_of_const v a _ s hJ k hk, Finset.sum_range_one, whittakerTr_zero_of_good v a hm hg,
      whittakerTr_of_good_unit v a hm hg t ht 1 le_rfl]
    ring
  exact (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨1, fun k hk => (hev k hk).symm⟩)).limUnder_eq

lemma not_π_dvd_det_QO (hg : IsGoodV v a) :
    ¬ LocalDensity.NF.π v ∣ (QO v a (fun i => (hg.2.2 i).le)).hessian.det := by
  set π := LocalDensity.NF.π v
  have hπ : Irreducible π := LocalDensity.NF.irreducible_π v
  have hp : Prime π := hπ.prime
  have h2 : ¬ π ∣ 2 := not_π_dvd_two_of_good v a hg
  rw [QO, LocalDensity.DVR.det_hessian_diag]
  intro h
  rcases hp.dvd_or_dvd h with h | h
  · exact h2 (hp.dvd_of_dvd_pow h)
  · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp _).mp h
    exact not_π_dvd_aO_of_good v a hg i hi

/-- **The unramified Whittaker integral is an inverse $L$-factor**: at a good place, for $t \in \mathcal O_v^\times$ and every
$s \in \mathbb C$,
$$W_v(t, s) = 1 - \chi_v\,q_v^{-(s+1)},\qquad \chi_v = \chi\big((-1)^mD\big)\ (\texttt{chiDisc}),$$
i.e. $L_v(s+1, \chi_V)^{-1}$. At $s = s_0 = m - 1$ it is $\beta_v(t) = 1 - \chi_vq_v^{-m}$. -/
@[kb "kudla2008" "§1 (the unramified local Whittaker function) [unverified]; Yang (1998) [unverified]; Hanke (2004), Table 1, p. 363"]
theorem whittakerVS_eq_lFactor_of_good (hm : 0 < m) (hg : IsGoodV v a) (t : 𝔬) (ht : Valued.v (t : Fv) = 1)
    (s : ℂ) :
    whittakerVS v a (t : Fv) s = 1 - (LocalDensity.DVR.chiDisc (QO v a (fun i => (hg.2.2 i).le)) : ℂ) *
      ((qV v : ℝ) : ℂ) ^ (-(s + 1)) := by
  set π := LocalDensity.NF.π v
  have hπ : Irreducible π := LocalDensity.NF.irreducible_π v
  have h2 : ¬ π ∣ 2 := not_π_dvd_two_of_good v a hg
  have hβ := LocalDensity.DVR.localDensity_even_unit_of_unimodular (QO v a (fun i => (hg.2.2 i).le)) π hπ h2
    (not_π_dvd_det_QO v a hg) (by omega) (even_two_mul m) t (not_π_dvd_of_valued_eq_one v ht)
  rw [whittakerVS_eq_of_good v a hm hg t ht s, hβ, show 2 * m / 2 = m by omega]
  have hq : (LocalDensity.DVR.q 𝔬 : ℝ) = qV v := by rw [LocalDensity.NF.q_completion, qV_eq]
  have hq0 : (((qV v : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (qV_pos v).ne'
  rw [hq]
  have e : Xs (m := m) v s * (((qV v : ℝ) : ℂ) ^ m)⁻¹ = ((qV v : ℝ) : ℂ) ^ (-(s + 1)) := by
    rw [Xs, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hq0]
    congr 1; ring
  rw [← e]
  push_cast
  ring

end Local

/-! ### The Euler product over the finite places -/

section Global

variable {m : ℕ}

lemma valued_ι_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : 𝓞 F} (hx : x ∉ v.asIdeal) :
    Valued.v ((LocalDensity.NF.ι v x : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
  rw [LocalDensity.NF.valued_ι]
  exact le_antisymm (v.intValuation_le_one x) (not_lt.mp fun h => hx ((v.intValuation_lt_one_iff_mem x).mp h))

lemma finite_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {x}) (by simpa using hx)).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv ⊢
  exact Ideal.dvd_span_singleton.mpr hv

/-- **The Euler product of the local Whittaker integrals at $s$ converges for $\operatorname{Re}s > 0$** (absolutely, `Multipliable`):
for $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus 0$, $n = 2m \ge 2$, and $t \in \mathcal O_F\setminus 0$,
$\prod_{v<\infty}W_v(t, s)$ converges; outside the finitely many places dividing $2\,\mathfrak d_F\,t\prod_ib_i$ the factor is
$1 - \chi_vN\mathfrak p_v^{-(s+1)}$ (`whittakerVS_eq_lFactor_of_good`). -/
@[kb "weil1965" "Ch. II–IV [unverified]; Kudla (2008), §1 [unverified]"]
theorem multipliable_whittakerVS (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (t : 𝓞 F) (ht : t ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    Multipliable fun v : HeightOneSpectrum (𝓞 F) =>
      whittakerVS v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F) s := by
  set W : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    whittakerVS v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F) s
  have hbad : (badPlaces (unitsOfInt b hb) 1 ∪ {v : HeightOneSpectrum (𝓞 F) | t ∈ v.asIdeal}).Finite :=
    (badPlaces_finite _ 1).union (finite_mem_asIdeal ht)
  have key : ∀ v, v ∉ badPlaces (unitsOfInt b hb) 1 ∪ {v : HeightOneSpectrum (𝓞 F) | t ∈ v.asIdeal} →
      ‖W v - 1‖ ≤ 1 * (NFEuler.normP v : ℝ) ^ (-(s.re + 1)) := by
    intro v hv
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hv
    have hg : IsGoodV v (aOfInt v b hb) := by
      rw [aOfInt_eq_aV]; exact isGoodV_of_not_bad _ hv.1
    simp only [W]
    rw [whittakerVS_eq_lFactor_of_good v _ hm hg _ (valued_ι_eq_one hv.2), sub_sub_cancel_left, norm_neg,
      norm_mul, qV_eq, one_mul]
    have hN : 0 < Ideal.absNorm v.asIdeal := by
      exact lt_of_lt_of_le two_pos (NFEuler.two_le_normP v)
    rw [show (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast_cpow_of_pos hN]
    have hχ : ‖(LocalDensity.DVR.chiDisc (QO v (aOfInt v b hb) (fun i => (hg.2.2 i).le)) : ℂ)‖ ≤ 1 := by
      unfold LocalDensity.DVR.chiDisc
      rw [Complex.norm_intCast]
      generalize (-1 : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) ^ (2 * m / 2) *
        LocalDensity.DVR.resGramDet (QO v (aOfInt v b hb) (fun i => (hg.2.2 i).le)) = x
      by_cases hx : x = 0
      · simp [hx]
      · rcases quadraticChar_dichotomy hx with h | h <;> simp [h]
    calc _ ≤ 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(s + 1)).re :=
          mul_le_mul_of_nonneg_right hχ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by simp [NFEuler.normP]
  have hbound : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ‖W v - 1‖ ≤ 1 * (NFEuler.normP v : ℝ) ^ (-(s.re + 1)) :=
    Filter.eventually_cofinite.mpr (hbad.subset fun v hv => by by_contra h; exact hv (key v h))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => ‖W v - 1‖ :=
    Summable.of_norm_bounded_eventually ((NFEuler.summable_normP_rpow (by linarith : 1 < s.re + 1)).mul_left 1)
      (hbound.mono fun v h => by rwa [norm_norm])
  simpa using multipliable_one_add_of_summable hsum

/-- **Value of the Euler product at $s = s_0$**: if $\prod_v\beta_v(t) = P$ then $\prod_vW_v(t, s_0) = C_f\cdot P$ (`hasProd_whittakerV`,
`whittakerVS_s₀`). -/
theorem hasProd_whittakerVS_s₀ (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) (t : 𝓞 F) (ht : t ≠ 0)
    {P : ℝ} (hP : HasProd (fun v : HeightOneSpectrum (𝓞 F) => LocalDensity.NF.localDensity v (QuadForm.diag b) t) P) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) =>
        whittakerVS v (aOfInt v b hb) ((LocalDensity.NF.ι v t : v.adicCompletionIntegers F) : v.adicCompletion F)
          ((m : ℂ) - 1))
      (constFin (unitsOfInt b hb) * P) := by
  refine (hasProd_whittakerV hm b hb t ht hP).congr_fun fun v => ?_
  have ht' : LocalDensity.NF.ι v t ≠ 0 := LocalDensity.NF.ι_ne_zero v ht
  exact whittakerVS_s₀ v _ hm (aOfInt_le_one v b hb) _ ht'

end Global

end QuadFormsKB.SiegelWeil
