/-
# The local Whittaker integral at a finite place for general $s$
**Layer:** local, at one finite place $v$ of a number field $F$ (dyadic places included).

**Setting.** $Q = \sum_{i<n}a_ix_i^2$, $n = 2m$ (0-based indices), $|a_i|_v \le 1$, $\varphi_v = \mathbf 1_{\mathcal O_v^n}$, $s_0 = m - 1$, $s \in \mathbb C$.
The standard section is $f_v(g, s) = f_v(g)\|g\|_v^{-(s-s_0)}$ (`secS`), and on the big cell $\|wn(b)\|_v = \max(1, |b|_v)$. With
$T_j(t) = \int_{\mathfrak p_v^{-j}}f_v(wn(b))\psi_v(-tb)\,db$ (the truncated integral at $s_0$, `whittakerTr`; it equals
$\gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}r_{\mathfrak p^{j-d_v}}(t)/q_v^{(j-d_v)(n-1)}$ for $j \ge d_v$, `whittakerTr_eq`) and
$X = q_v^{-(s-s_0)}$:

**Results.**
* `whittakerTrS`, `whittakerVS`: the truncated and the regularized Whittaker integral at $s$,
  $W_v(t, s) = \lim_k\int_{\mathfrak p_v^{-k}}f_v(wn(b), s)\psi_v(-tb)\,db$.
* **`whittakerTrS_eq`** (Abel summation over the shells $|b|_v = q_v^j$): for every $k$ and every $t \in F_v$,
  $$\int_{\mathfrak p_v^{-k}}f_v(wn(b), s)\psi_v(-tb)\,db = \sum_{j<k}(X^j - X^{j+1})\,T_j(t) + X^kT_k(t).$$
* **`whittakerVS_eq`**: for $t \in \mathcal O_v\setminus0$ there is $J$ such that for **every** $s \in \mathbb C$
  $$W_v(t, s) = \sum_{j<J}(X^j - X^{j+1})\,T_j(t) + X^JT_J(t),$$
  a polynomial in $X = q_v^{-(s-s_0)}$ (the integral is a finite sum; no convergence condition on $s$), and
  `whittakerVS_s₀`: at $s = s_0$ ($X = 1$) it is the earlier $W_v(t) = \gamma_Vc_B N(\mathfrak d_v)^{-(n-1)/2}\beta_v(t)$ (`whittakerV_eq_localDensity`).

This is the finite-place half of the factorization of the Fourier coefficients off $s_0$; the archimedean
Whittaker integral off $s_0$ and the global unfolding are not formalized in this file.

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Kudla (2008), §1 ($W_{T,v}(g, s, \Phi_v)$) [unverified]; Yang,
J. Number Theory 72 (1998) (local Whittaker functions as polynomials in $q^{-s}$) [unverified].
-/
import QuadFormsKB.SiegelWeil.LocalWhittaker

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-! ### Abel summation over the shells -/

/-- The finite Abel identity behind the shell decomposition:
$[j_0 \le k]\,X^{j_0} = \sum_{j<k}(X^j - X^{j+1})[j_0 \le j] + X^k[j_0 \le k]$. -/
lemma abel_shell (X : ℂ) (j₀ : ℕ) : ∀ k : ℕ, (if j₀ ≤ k then X ^ j₀ else 0) =
    ∑ j ∈ Finset.range k, (X ^ j - X ^ (j + 1)) * (if j₀ ≤ j then 1 else 0) + X ^ k * (if j₀ ≤ k then 1 else 0)
  | 0 => by
    rcases Nat.eq_zero_or_pos j₀ with h | h
    · subst h; simp
    · simp [show ¬ j₀ ≤ 0 by omega]
  | k + 1 => by
    rw [Finset.sum_range_succ]
    have ih := abel_shell X j₀ k
    rcases lt_trichotomy j₀ (k + 1) with h | h | h
    · have h1 : j₀ ≤ k := by omega
      simp only [h1, h.le, ite_true, mul_one] at ih ⊢
      linear_combination ih
    · subst h
      have h1 : ¬ k + 1 ≤ k := by omega
      simp only [h1, le_refl, ite_true, ite_false, mul_one, mul_zero] at ih ⊢
      linear_combination ih
    · have h1 : ¬ j₀ ≤ k := by omega
      have h2 : ¬ j₀ ≤ k + 1 := by omega
      simp only [h1, h2, ite_false, mul_zero] at ih ⊢
      linear_combination ih

/-- **The shell index** of $b \in F_v$: $0$ if $|b|_v \le 1$, and $j$ if $|b|_v = q_v^j$, $j \ge 1$. -/
def shellIdx (b : Fv) : ℕ := if Valued.v b ≤ 1 then 0 else (log (Valued.v b)).toNat

lemma valued_le_exp_iff_shellIdx (b : Fv) (j : ℕ) : Valued.v b ≤ exp (j : ℤ) ↔ shellIdx v b ≤ j := by
  unfold shellIdx
  split_ifs with h
  · exact ⟨fun _ => Nat.zero_le _, fun _ => h.trans (by rw [← exp_zero, exp_le_exp]; omega)⟩
  · push Not at h
    have h0 : Valued.v b ≠ 0 := (zero_lt_one.trans h).ne'
    obtain ⟨e, he⟩ : ∃ e, Valued.v b = exp e := ⟨_, (exp_log h0).symm⟩
    rw [he, ← exp_zero, exp_lt_exp] at h
    rw [he, log_exp, exp_le_exp]
    omega

lemma ballIndV_neg_eq_ite (b : Fv) (j : ℕ) :
    ballIndV v 0 (-(j : ℤ)) b = if shellIdx v b ≤ j then 1 else 0 := by
  unfold ballIndV
  by_cases h : shellIdx v b ≤ j
  · rw [ite_eq_left h]
    exact Set.indicator_of_mem (by
      show Valued.v (b - 0) ≤ exp (-(-(j : ℤ)))
      rw [sub_zero, neg_neg]; exact (valued_le_exp_iff_shellIdx v b j).mpr h) _
  · rw [ite_eq_right h]
    exact Set.indicator_of_notMem (by
      show ¬ Valued.v (b - 0) ≤ exp (-(-(j : ℤ)))
      rw [sub_zero, neg_neg]; exact fun h' => h ((valued_le_exp_iff_shellIdx v b j).mp h')) _

/-- $q' = |\varpi_v|_v^{-1} > 1$ (it is $q_v$). -/
abbrev qV : ℝ := ‖HN.ϖ v‖⁻¹

lemma qV_pos : 0 < qV v := inv_pos.mpr (norm_pos_iff.mpr (HN.ϖ_ne_zero v))

lemma norm_eq_of_valued_eq {x y : Fv} (h : Valued.v x = Valued.v y) : ‖x‖ = ‖y‖ :=
  le_antisymm ((Valued.toNormedField.norm_le_iff).mpr h.le) ((Valued.toNormedField.norm_le_iff).mpr h.ge)

/-- $\max(1, |b|_v) = q_v^{j}$, $j$ the shell index. -/
lemma max_one_norm_eq (b : Fv) : max 1 ‖b‖ = qV v ^ shellIdx v b := by
  unfold shellIdx
  split_ifs with h
  · rw [pow_zero]; exact max_eq_left ((Valued.toNormedField.norm_le_one_iff).mpr h)
  · push Not at h
    have h0 : Valued.v b ≠ 0 := (zero_lt_one.trans h).ne'
    have hpos : 0 < log (Valued.v b) := by
      rw [← exp_lt_exp, exp_log h0, exp_zero]; exact h
    have hv : Valued.v b = Valued.v (HN.ϖ v ^ (-(log (Valued.v b)))) := by
      rw [valued_ϖ_zpow, neg_neg, exp_log h0]
    have hn : ‖b‖ = qV v ^ (log (Valued.v b)).toNat := by
      rw [norm_eq_of_valued_eq v hv, norm_zpow, qV, inv_pow, ← zpow_natCast, ← zpow_neg,
        Int.toNat_of_nonneg hpos.le]
    rw [hn]
    refine max_eq_right (one_le_pow₀ ?_)
    rw [qV]
    exact (one_le_inv₀ (norm_pos_iff.mpr (HN.ϖ_ne_zero v))).mpr (norm_ϖ_lt_one v).le

/-- $\|wn(b)\|_v = \max(1, |b|_v)$. -/
lemma htV_wMat_nMat (b : Fv) : htV v (wMat * nMat b : SL(2, Fv)) = max 1 ‖b‖ := by
  rw [htV]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two, wMat, nMat]

/-! ### The Whittaker integral at $s$ -/

/-- **The function $b \mapsto f_v(wn(b), s)$** of the standard section of $\mathbf 1_{\mathcal O_v^n}$. -/
def wfunS (b : Fv) (s : ℂ) : ℂ := secS v a (oneS v m) (wMat * nMat b) s

/-- **The truncated local Whittaker integral at $s$**: $\int_{\mathfrak p_v^{-k}}f_v(wn(b), s)\,\psi_v(-tb)\,db$ (self-dual $db$). -/
@[kb "kudla2008" "§1 (the local Whittaker function $W_{T,v}(g, s, \\Phi_v)$) [unverified]; weil1965 Ch. II [unverified]"]
def whittakerTrS (t : Fv) (s : ℂ) (k : ℕ) : ℂ :=
  ∫ b, ballIndV v 0 (-(k : ℤ)) b * (wfunS v a b s * (psiV v (-(t * b)) : ℂ)) ∂selfDualV v

/-- **The local Whittaker integral at $s$**: $W_v(t, s) = \lim_k\int_{\mathfrak p_v^{-k}}f_v(wn(b), s)\psi_v(-tb)\,db$ (`limUnder`; the limit is
attained for $t \in \mathcal O_v\setminus0$, `whittakerVS_eq`). At $s = s_0$ it is `whittakerV` (`whittakerVS_s₀`). -/
@[kb "kudla2008" "§1 ($W_{T,v}(e, s, \\Phi_v)$) [unverified]; weil1965 Ch. II [unverified]"]
def whittakerVS (t : Fv) (s : ℂ) : ℂ := limUnder atTop (whittakerTrS v a t s)

/-- $X = q_v^{-(s-s_0)}$. -/
abbrev Xs (s : ℂ) : ℂ := ((qV v : ℝ) : ℂ) ^ (-(s - ((m : ℂ) - 1)))

lemma ofReal_pow_cpow (q : ℝ) (hq : 0 < q) (j : ℕ) (w : ℂ) : (((q ^ j : ℝ) : ℂ)) ^ w = ((q : ℂ) ^ w) ^ j := by
  rw [← Complex.cpow_nat_mul]
  have h1 : (((q ^ j : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (pow_pos hq j).ne'
  have h2 : ((q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2, ← Complex.ofReal_log (pow_pos hq j).le,
    Real.log_pow, ← Complex.ofReal_log hq.le]
  push_cast
  ring_nf

/-- $f_v(wn(b), s) = X^{j(b)}f_v(wn(b))$, $j(b)$ the shell index. -/
lemma wfunS_eq (b : Fv) (s : ℂ) : wfunS v a b s = (Xs (m := m) v s) ^ shellIdx v b * wfun v a b := by
  unfold wfunS secS
  rw [htV_wMat_nMat, max_one_norm_eq, ofReal_pow_cpow _ (qV_pos v), mul_comm]
  rfl

/-- The integrand of the truncated Whittaker integral at $s_0$ is integrable (Fubini, as in `whittakerTr_eq_vol`). -/
lemma integrable_whittakerTr (t : Fv) (k : ℕ) :
    Integrable (fun b => ballIndV v 0 (-(k : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ))) (selfDualV v) := by
  set γc := (localDataV v).gammaV a * (localDataV v).cB a
  have : SigmaFinite (localDataV v).μ := (isOps_V v).sigmaFinite
  have : SFinite ((localDataV v).muN (2 * m)) := by unfold muN; infer_instance
  have hW : ∀ b : Fv, ballIndV v 0 (-(k : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ)) =
      γc * ∫ x, ballIndV v 0 (-(k : ℤ)) b * (oneV v (2 * m) x * (psiV v (b * (Qform a x - t)) : ℂ))
        ∂(localDataV v).muN (2 * m) := by
    intro b
    rw [wfun_eq]
    simp only [← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : (psiV v (b * (Qform a x - t)) : ℂ) = (psiV v (b * Qform a x) : ℂ) * (psiV v (-(t * b)) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
    dsimp only
    rw [this]; ring
  have hint : Integrable (Function.uncurry fun (b : Fv) (x : Fin (2 * m) → Fv) =>
      ballIndV v 0 (-(k : ℤ)) b * (oneV v (2 * m) x * (psiV v (b * (Qform a x - t)) : ℂ)))
      ((selfDualV v).prod ((localDataV v).muN (2 * m))) := by
    refine Integrable.mono' ((integrable_ballIndV_zero v (-(k : ℤ))).norm.mul_prod
      (integrable_oneV v (m := m)).norm) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine ((continuous_ballIndV_zero v _).comp continuous_fst).mul
        (((continuous_oneV v).comp continuous_snd).mul ?_)
      refine continuous_subtype_val.comp ((continuous_psiV v).comp ?_)
      refine continuous_fst.mul ((?_ : Continuous fun x : Fin (2 * m) → Fv => Qform a x).comp continuous_snd
        |>.sub continuous_const)
      unfold Qform
      exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).pow 2)
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      exact le_rfl
  have h := hint.integral_prod_left.const_mul γc
  refine h.congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [Function.uncurry]
  exact (hW b).symm

/-- **The truncated Whittaker integral at $s$ by Abel summation over the shells** (every finite place, dyadic included; every
$t \in F_v$, $k \in \mathbb N$, $s \in \mathbb C$): with $X = q_v^{-(s-s_0)}$ and $T_j(t)$ the truncated integral at $s_0$ (`whittakerTr`),
$$\int_{\mathfrak p_v^{-k}}f_v(wn(b), s)\psi_v(-tb)\,db = \sum_{j<k}(X^j - X^{j+1})\,T_j(t) + X^kT_k(t).$$
*Proof:* $f_v(wn(b), s) = X^{j(b)}f_v(wn(b))$ on the shell $|b|_v = q_v^{j(b)}$, and $[j(b) \le k]X^{j(b)} = \sum_{j<k}(X^j - X^{j+1})[j(b) \le j] + X^k[j(b) \le k]$. -/
@[kb "kudla2008" "§1 (the local Whittaker function) [unverified]; Yang (1998) [unverified]"]
theorem whittakerTrS_eq (t : Fv) (s : ℂ) (k : ℕ) :
    whittakerTrS v a t s k = ∑ j ∈ Finset.range k, ((Xs (m := m) v s) ^ j - (Xs (m := m) v s) ^ (j + 1)) *
      whittakerTr v a t j + (Xs (m := m) v s) ^ k * whittakerTr v a t k := by
  set X := Xs (m := m) v s
  have hpt : ∀ b : Fv, ballIndV v 0 (-(k : ℤ)) b * (wfunS v a b s * (psiV v (-(t * b)) : ℂ)) =
      ∑ j ∈ Finset.range k, (X ^ j - X ^ (j + 1)) *
        (ballIndV v 0 (-(j : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ))) +
      X ^ k * (ballIndV v 0 (-(k : ℤ)) b * (wfun v a b * (psiV v (-(t * b)) : ℂ))) := by
    intro b
    have hab := abel_shell X (shellIdx v b) k
    rw [wfunS_eq]
    simp only [ballIndV_neg_eq_ite]
    have e : ∀ j, (X ^ j - X ^ (j + 1)) * ((if shellIdx v b ≤ j then (1 : ℂ) else 0) *
        (wfun v a b * (psiV v (-(t * b)) : ℂ))) =
        ((X ^ j - X ^ (j + 1)) * (if shellIdx v b ≤ j then 1 else 0)) * (wfun v a b * (psiV v (-(t * b)) : ℂ)) :=
      fun j => by ring
    simp_rw [e, ← Finset.sum_mul]
    have e2 : (if shellIdx v b ≤ k then (1 : ℂ) else 0) * (X ^ shellIdx v b * wfun v a b * (psiV v (-(t * b)) : ℂ)) =
        (if shellIdx v b ≤ k then X ^ shellIdx v b else 0) * (wfun v a b * (psiV v (-(t * b)) : ℂ)) := by
      split_ifs <;> ring
    rw [e2, hab]
    ring
  unfold whittakerTrS
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add, integral_finsetSum]
  · simp only [integral_const_mul]
    rfl
  · exact fun j _ => (integrable_whittakerTr v a t j).const_mul _
  · exact integrable_finsetSum _ fun j _ => (integrable_whittakerTr v a t j).const_mul _
  · exact (integrable_whittakerTr v a t k).const_mul _

/-- If the $T_j$ are constant from $J$ on, so is the truncated integral at $s$. -/
lemma whittakerTrS_eq_of_const (t : Fv) (s : ℂ) {J : ℕ} (hJ : ∀ j, J ≤ j → whittakerTr v a t j = whittakerTr v a t J)
    (k : ℕ) (hk : J ≤ k) :
    whittakerTrS v a t s k = ∑ j ∈ Finset.range J, ((Xs (m := m) v s) ^ j - (Xs (m := m) v s) ^ (j + 1)) *
      whittakerTr v a t j + (Xs (m := m) v s) ^ J * whittakerTr v a t J := by
  rw [whittakerTrS_eq]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [← add_assoc, Finset.sum_range_succ, hJ (J + r) (by omega), hJ (J + r + 1) (by omega)]
    rw [hJ (J + r) (by omega)] at ih
    rw [← ih]
    ring

/-- **The local Whittaker integral at $s$ is a polynomial in $X = q_v^{-(s-s_0)}$** (every finite place, dyadic included;
$|a_i|_v \le 1$, $m > 0$, $t \in \mathcal O_v\setminus0$): there is $J$ such that for every $s \in \mathbb C$ the truncations are eventually
constant and
$$W_v(t, s) = \sum_{j<J}(X^j - X^{j+1})\,T_j(t) + X^JT_J(t),$$
with $T_j(t)$ = `whittakerTr` ($= \gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}r_{\mathfrak p^{j-d_v}}(t)/q_v^{(j-d_v)(n-1)}$ for $j \ge d_v$, `whittakerTr_eq`). -/
@[kb "kudla2008" "§1 (the local Whittaker function $W_{T,v}(e, s, \\Phi_v)$) [unverified]; Yang (1998) [unverified]"]
theorem whittakerVS_eq (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬) (ht : t ≠ 0) :
    ∃ J : ℕ, ∀ s : ℂ, (∀ k, J ≤ k → whittakerTrS v a (t : Fv) s k = whittakerVS v a (t : Fv) s) ∧
      whittakerVS v a (t : Fv) s = ∑ j ∈ Finset.range J, ((Xs (m := m) v s) ^ j - (Xs (m := m) v s) ^ (j + 1)) *
        whittakerTr v a (t : Fv) j + (Xs (m := m) v s) ^ J * whittakerTr v a (t : Fv) J := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (whittakerTr_eventually_eq v a hm ha t ht)
  have hJ' : ∀ j, J ≤ j → whittakerTr v a (t : Fv) j = whittakerTr v a (t : Fv) J := fun j hj => by
    rw [hJ j hj, hJ J le_rfl]
  refine ⟨J, fun s => ?_⟩
  have hev : ∀ k, J ≤ k → whittakerTrS v a (t : Fv) s k = ∑ j ∈ Finset.range J,
      ((Xs (m := m) v s) ^ j - (Xs (m := m) v s) ^ (j + 1)) * whittakerTr v a (t : Fv) j +
        (Xs (m := m) v s) ^ J * whittakerTr v a (t : Fv) J := whittakerTrS_eq_of_const v a _ s hJ'
  have hlim : whittakerVS v a (t : Fv) s = ∑ j ∈ Finset.range J,
      ((Xs (m := m) v s) ^ j - (Xs (m := m) v s) ^ (j + 1)) * whittakerTr v a (t : Fv) j +
        (Xs (m := m) v s) ^ J * whittakerTr v a (t : Fv) J :=
    (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨J, fun k hk => (hev k hk).symm⟩)).limUnder_eq
  exact ⟨fun k hk => (hev k hk).trans hlim.symm, hlim⟩

/-- **At $s = s_0$ the Whittaker integral at $s$ is the earlier $W_v(t)$**($X = 1$, the sum telescopes), hence
$W_v(t, s_0) = \gamma_Vc_B\operatorname{vol}(\mathcal O_v)^{n-1}\beta_v(t)$ (`whittakerV_eq_localDensity`). -/
theorem whittakerVS_s₀ (hm : 0 < m) (ha : ∀ i, Valued.v (a i : v.adicCompletion F) ≤ 1) (t : 𝔬) (ht : t ≠ 0) :
    whittakerVS v a (t : Fv) ((m : ℂ) - 1) = whittakerV v a (t : Fv) := by
  have hX : Xs (m := m) v ((m : ℂ) - 1) = 1 := by simp [Xs]
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (whittakerTr_eventually_eq v a hm ha t ht)
  have hJ' : ∀ j, J ≤ j → whittakerTr v a (t : Fv) j = whittakerTr v a (t : Fv) J := fun j hj => by
    rw [hJ j hj, hJ J le_rfl]
  have hev : ∀ k, J ≤ k → whittakerTrS v a (t : Fv) ((m : ℂ) - 1) k = whittakerConst v a *
      (LocalDensity.DVR.localDensity (QO v a ha) (LocalDensity.NF.π v) t : ℂ) := by
    intro k hk
    rw [whittakerTrS_eq_of_const v a _ _ hJ' k hk, hX]
    simp only [one_pow, sub_self, zero_mul, Finset.sum_const_zero, zero_add, one_mul]
    exact hJ J le_rfl
  rw [whittakerVS, (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨J, fun k hk => (hev k hk).symm⟩)).limUnder_eq,
    whittakerV_eq_localDensity v a hm ha t ht, whittakerConst]

end QuadFormsKB.SiegelWeil
