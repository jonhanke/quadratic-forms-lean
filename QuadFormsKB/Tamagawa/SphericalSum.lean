/-
# The summation behind Weil's comparison

**Layer:** pure analysis and finite combinatorics; no number fields. This file isolates the two summation steps of
Weil's comparison of the spherical sum with the plain zeta integral (A. Weil, *Adeles and Algebraic Groups*, 1982,
§4.5, pp. 106–108):

* `hasSum_poisson` (**the Euler expansion of the restricted sum**, Weil's (4)–(6), p. 106): a sum over pairs
  $(T, d)$, $T$ a finite set of primes and $d$ in a finite group $D$, of $a(T,d)\prod_{p\in T}r_p$, where the $d$-sums obey a
  Poisson (orthogonality) identity $\sum_d a(T,d) = |D|^{-1}\sum_d\chi_d(T)\hat a(d)$, equals
  $|D|^{-1}\sum_d\hat a(d)\prod_p(1 + \chi_d(p)r_p)$. In the application $T$ is the set of primes outside $S$ at which the class
  $\rho$ has odd order, $d$ runs over $E_S/E_S^2$ ($S$-units), $r_p$ is the ratio of the odd- and even-parity local integrals,
  and $\chi_d$ is the quadratic character of $F(\sqrt d)/F$.
* `tendsto_mul_of_sandwich` (**the limit $S \to \infty$**, Weil's (8), p. 108): if for every $\varepsilon > 0$ the function is
  eventually between $\mu Y$ and $\mu'Y$ with $1 - \varepsilon \le \mu$, $\mu' \le 1 + \varepsilon$ and $sY(s) \to L$, then $sZ(s) \to L$.
-/
import Mathlib
import QuadFormsKB.Citation

open Filter Topology

noncomputable section

namespace QuadFormsKB.SphericalSum

/-- **The Euler expansion** $\sum_{T}\prod_{p\in T}f(p) = \prod_p(1 + f(p))$ (sum over the finite subsets $T$), for
$\sum_p|f(p)| < \infty$ (Mathlib's `tprod_one_add`). -/
theorem hasSum_finset_prod {P : Type*} {f : P → ℝ} (hf : Summable fun p => |f p|) :
    HasSum (fun T : Finset P => ∏ p ∈ T, f p) (∏' p, (1 + f p)) := by
  have hs : Summable fun T : Finset P => ∏ p ∈ T, f p :=
    summable_finsetProd_of_summable_norm (f := f) (by simpa [Real.norm_eq_abs] using hf)
  rw [tprod_one_add hs]; exact hs.hasSum

/-- **The Poisson–Euler identity** (Weil 1982, §4.5, (4)–(6), p. 106, in multiplicative form). Let $D$ be finite, $r_p \ge 0$
summable, $|\chi_d(p)| \le 1$, $a(T,d) \ge 0$, and suppose that for every finite $T$
$$\sum_{d\in D}a(T,d) = |D|^{-1}\sum_{d\in D}\Big(\prod_{p\in T}\chi_d(p)\Big)\hat a(d).$$
Then $\displaystyle\sum_{(T,d)}a(T,d)\prod_{p\in T}r_p = |D|^{-1}\sum_{d\in D}\hat a(d)\prod_p\big(1 + \chi_d(p)\,r_p\big)$. -/
@[kb "weil1982" "§4.5, (4)–(6), p. 106 (Z_S as 2^{-|S|} Σ_λ of Euler products)"]
theorem hasSum_poisson {P D : Type*} [Fintype D] (r : P → ℝ) (hr : ∀ p, 0 ≤ r p) (hrs : Summable r)
    (χ : D → P → ℝ) (hχ : ∀ d p, |χ d p| ≤ 1) (a : Finset P → D → ℝ) (ha : ∀ T d, 0 ≤ a T d)
    (ahat : D → ℝ) (hpois : ∀ T, ∑ d, a T d = (Fintype.card D : ℝ)⁻¹ * ∑ d, (∏ p ∈ T, χ d p) * ahat d) :
    HasSum (fun x : Finset P × D => a x.1 x.2 * ∏ p ∈ x.1, r p)
      ((Fintype.card D : ℝ)⁻¹ * ∑ d, ahat d * ∏' p, (1 + χ d p * r p)) := by
  have hT : ∀ d, HasSum (fun T : Finset P => ∏ p ∈ T, (χ d p * r p)) (∏' p, (1 + χ d p * r p)) := by
    intro d
    refine hasSum_finset_prod (hrs.of_nonneg_of_le (fun p => abs_nonneg _) fun p => ?_)
    rw [abs_mul, abs_of_nonneg (hr p)]
    exact mul_le_of_le_one_left (hr p) (hχ d p)
  have hsumT : HasSum (fun T : Finset P => ∑ d, a T d * ∏ p ∈ T, r p)
      ((Fintype.card D : ℝ)⁻¹ * ∑ d, ahat d * ∏' p, (1 + χ d p * r p)) := by
    have h := (hasSum_sum fun d (_ : d ∈ Finset.univ) => (hT d).mul_left (ahat d)).mul_left
      (Fintype.card D : ℝ)⁻¹
    convert h using 1
    funext T
    rw [← Finset.sum_mul, hpois T, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  have hf0 : ∀ x : Finset P × D, 0 ≤ a x.1 x.2 * ∏ p ∈ x.1, r p := fun x =>
    mul_nonneg (ha _ _) (Finset.prod_nonneg fun p _ => hr p)
  have hsf : Summable fun x : Finset P × D => a x.1 x.2 * ∏ p ∈ x.1, r p := by
    refine (summable_prod_of_nonneg hf0).mpr ⟨fun T => (hasSum_fintype _).summable, ?_⟩
    simpa [tsum_fintype] using hsumT.summable
  convert hsf.hasSum using 1
  rw [hsf.tsum_prod' (fun T => (hasSum_fintype _).summable)]
  simp only [tsum_fintype]
  exact hsumT.tsum_eq.symm

/-- **The limit along the sandwich** (Weil 1982, §4.5, p. 108: "lim. inf. $sZ(s)$ and lim. sup. $sZ(s)$ ... are between
$\mu(S)$ and $\mu'(S)$; since we may here take $S$ as large as we please"): if $L \ge 0$ and for every $\varepsilon > 0$ there are
$0 \le \mu$, $\mu'$ with $1 - \varepsilon \le \mu$, $\mu' \le 1 + \varepsilon$ and a function $Y$ with $sY(s) \to L$ and eventually
$\mu Y(s) \le Z(s) \le \mu'Y(s)$, then $sZ(s) \to L$ as $s \to 0^+$. -/
@[kb "weil1982" "§4.5, p. 108 (μ(S) < 2^{-|S|} Z(s) Z_S(s)^{-1} < μ'(S), S → ∞)"]
theorem tendsto_mul_of_sandwich {Z : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ ε > 0, ∃ μ μ' : ℝ, ∃ Y : ℝ → ℝ, 0 ≤ μ ∧ 1 - ε ≤ μ ∧ μ' ≤ 1 + ε ∧
      (∀ᶠ s in 𝓝[>] 0, μ * Y s ≤ Z s ∧ Z s ≤ μ' * Y s) ∧
      Tendsto (fun s => s * Y s) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun s => s * Z s) (𝓝[>] 0) (𝓝 L) := by
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_nhdsWithin_of_forall fun s hs => hs
  rw [tendsto_order]
  constructor
  · intro a ha
    -- choose ε with (1 - ε) L > a
    obtain ⟨ε, hε, hεa⟩ : ∃ ε > 0, a < (1 - ε) * L := by
      by_cases h0 : L = 0
      · exact ⟨1, one_pos, by rw [h0]; linarith⟩
      · have hL0 : 0 < L := lt_of_le_of_ne hL (Ne.symm h0)
        refine ⟨(L - a) / (2 * L), div_pos (by linarith) (by linarith), ?_⟩
        have e : (1 - (L - a) / (2 * L)) * L = (L + a) / 2 := by field_simp; ring
        rw [e]; linarith
    obtain ⟨μ, μ', Y, hμ0, hμ, -, hev, hY⟩ := h ε hε
    have hlim := hY.const_mul μ
    have hμL : a < μ * L := lt_of_lt_of_le hεa (mul_le_mul_of_nonneg_right hμ hL)
    filter_upwards [(tendsto_order.1 hlim).1 a hμL, hev, hpos] with s h1 h2 hs
    calc a < μ * (s * Y s) := h1
      _ = s * (μ * Y s) := by ring
      _ ≤ s * Z s := mul_le_mul_of_nonneg_left h2.1 hs.le
  · intro b hb
    obtain ⟨ε, hε, hεb⟩ : ∃ ε > 0, (1 + ε) * L < b := by
      by_cases h0 : L = 0
      · exact ⟨1, one_pos, by rw [h0]; linarith⟩
      · have hL0 : 0 < L := lt_of_le_of_ne hL (Ne.symm h0)
        refine ⟨(b - L) / (2 * L), div_pos (by linarith) (by linarith), ?_⟩
        have e : (1 + (b - L) / (2 * L)) * L = (L + b) / 2 := by field_simp; ring
        rw [e]; linarith
    obtain ⟨μ, μ', Y, -, -, hμ', hev, hY⟩ := h ε hε
    have hlim := hY.const_mul μ'
    have hμL : μ' * L < b := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hμ' hL) hεb
    filter_upwards [(tendsto_order.1 hlim).2 b hμL, hev, hpos] with s h1 h2 hs
    calc s * Z s ≤ s * (μ' * Y s) := mul_le_mul_of_nonneg_left h2.2 hs.le
      _ = μ' * (s * Y s) := by ring
      _ < b := h1

/-! ### Comparing infinite products factor by factor -/

lemma prod_one_add_le_exp {ι : Type*} (A : Finset ι) (θ : ι → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    ∏ i ∈ A, (1 + θ i) ≤ Real.exp (∑ i ∈ A, θ i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => by linarith [hθ i]) fun i _ => by
    linarith [Real.add_one_le_exp (θ i)]

lemma one_sub_sum_le_prod {ι : Type*} (A : Finset ι) (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) :
    1 - ∑ i ∈ A, θ i ≤ ∏ i ∈ A, (1 - θ i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hP : 0 ≤ ∏ i ∈ A, (1 - θ i) := Finset.prod_nonneg fun i _ => by linarith [hθ1 i]
    have hS : 0 ≤ ∑ i ∈ A, θ i := Finset.sum_nonneg fun i _ => hθ0 i
    nlinarith [hθ0 a, hθ1 a]

/-- **Factorwise sandwich for infinite products** (the step "$\mu(S) < 2^{-|S|}Z(s,\rho)Z_S(s,\rho)^{-1} < \mu'(S)$", Weil 1982, p. 108):
if $(1-\theta_i)P_i \le z_i \le (1+\theta_i)P_i$ with $P_i \ge 0$, $0 \le \theta_i \le 1$, $\sum\theta_i \le \delta$, then
$(1-\delta)\prod P \le \prod z \le e^\delta\prod P$. -/
theorem tprod_sandwich {ι : Type*} (z P θ : ι → ℝ) {Z B δ : ℝ} (hz : HasProd z Z) (hP : HasProd P B)
    (hP0 : ∀ i, 0 ≤ P i) (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) (hθs : Summable θ) (hδ : ∑' i, θ i ≤ δ)
    (hlow : ∀ i, (1 - θ i) * P i ≤ z i) (hup : ∀ i, z i ≤ (1 + θ i) * P i) :
    (1 - δ) * B ≤ Z ∧ Z ≤ Real.exp δ * B := by
  have hsumA : ∀ A : Finset ι, ∑ i ∈ A, θ i ≤ δ := fun A =>
    (hθs.sum_le_tsum A (fun i _ => hθ0 i)).trans hδ
  have hPA : ∀ A : Finset ι, 0 ≤ ∏ i ∈ A, P i := fun A => Finset.prod_nonneg fun i _ => hP0 i
  constructor
  · refine le_of_tendsto_of_tendsto' (Filter.Tendsto.const_mul (1 - δ) hP) hz fun A => ?_
    calc (1 - δ) * ∏ i ∈ A, P i ≤ (1 - ∑ i ∈ A, θ i) * ∏ i ∈ A, P i :=
          mul_le_mul_of_nonneg_right (by linarith [hsumA A]) (hPA A)
      _ ≤ (∏ i ∈ A, (1 - θ i)) * ∏ i ∈ A, P i :=
          mul_le_mul_of_nonneg_right (one_sub_sum_le_prod A θ hθ0 hθ1) (hPA A)
      _ = ∏ i ∈ A, ((1 - θ i) * P i) := (Finset.prod_mul_distrib).symm
      _ ≤ ∏ i ∈ A, z i := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (by linarith [hθ1 i]) (hP0 i))
          fun i _ => hlow i
  · refine le_of_tendsto_of_tendsto' hz (Filter.Tendsto.const_mul (Real.exp δ) hP) fun A => ?_
    have hz0 : ∀ i, 0 ≤ z i := fun i => le_trans (mul_nonneg (by linarith [hθ1 i]) (hP0 i)) (hlow i)
    calc ∏ i ∈ A, z i ≤ ∏ i ∈ A, ((1 + θ i) * P i) := Finset.prod_le_prod₀ (fun i _ => hz0 i) fun i _ => hup i
      _ = (∏ i ∈ A, (1 + θ i)) * ∏ i ∈ A, P i := Finset.prod_mul_distrib
      _ ≤ Real.exp (∑ i ∈ A, θ i) * ∏ i ∈ A, P i :=
          mul_le_mul_of_nonneg_right (prod_one_add_le_exp A θ hθ0) (hPA A)
      _ ≤ Real.exp δ * ∏ i ∈ A, P i :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hsumA A)) (hPA A)

open Classical in
/-- **Tails of a summable family are small:** for $\theta \ge 0$ summable and $\delta > 0$ there is a finite $A$ with
$\sum_{i\notin S}\theta_i \le \delta$ for every finite $S \supseteq A$. -/
theorem exists_tail_le {ι : Type*} (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθs : Summable θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : Finset ι, ∀ S : Finset ι, A ⊆ S → ∑' i, (if i ∈ S then 0 else θ i) ≤ δ := by
  classical
  have ht : Tendsto (fun A : Finset ι => ∑ i ∈ A, θ i) atTop (𝓝 (∑' i, θ i)) := hθs.hasSum
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 ht).1 (∑' i, θ i - δ) (by linarith))
  refine ⟨A, fun S hS => ?_⟩
  have h1 : ∑' i, (if i ∈ S then 0 else θ i) = ∑' i, θ i - ∑ i ∈ S, θ i := by
    have hsplit : ∀ i, θ i = (if i ∈ S then θ i else 0) + (if i ∈ S then 0 else θ i) := fun i => by
      split_ifs <;> simp
    have hfin : ∑' i, (if i ∈ S then θ i else 0) = ∑ i ∈ S, θ i := by
      rw [tsum_eq_sum (s := S) (fun i hi => by simp [hi])]
      exact Finset.sum_congr rfl fun i hi => by simp [hi]
    have hs1 : Summable fun i => (if i ∈ S then θ i else 0) :=
      summable_of_ne_finset_zero (s := S) fun i hi => by simp [hi]
    have hs2 : Summable fun i => (if i ∈ S then 0 else θ i) :=
      hθs.of_nonneg_of_le (fun i => by split_ifs <;> simp [hθ0 i]) fun i => by split_ifs <;> simp [hθ0 i]
    have := hs1.tsum_add hs2
    rw [← tsum_congr hsplit] at this
    linarith
  rw [h1]
  have := hA S hS
  linarith

end QuadFormsKB.SphericalSum
