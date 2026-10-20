/-
# Quadratic-character $L$-functions over a number field and Hanke's $E_n(X)$

Let $F$ be a number field, $d = [F:\mathbb{Q}]$, and let $\chi$ be a real function on the nonzero primes of $\mathcal O_F$
with $|\chi(\mathfrak p)| \le 1$ (`hχ`). The intended case is the quadratic residue symbol of a discriminant: $\chi(\mathfrak p) = \pm1$
for $\mathfrak p \nmid \mathfrak N$ and $\chi(\mathfrak p) = 0$ for $\mathfrak p \mid \mathfrak N$ (`charOff 𝔑 χ` makes a $\pm1$-valued $\chi$ vanish on
$\mathfrak p \mid \mathfrak N$, so the factors there are $1$). For real $s > 1$,
$$L_F(s,\chi) = \prod_{\mathfrak p}\big(1 - \chi(\mathfrak p)N\mathfrak p^{-s}\big)^{-1}\qquad(\texttt{LFunctionNF}),$$
an absolutely convergent product (`hasProd_LFunctionNF`, via the Euler product convergence lemmas). This file proves
$$\zeta_F(s)^{-1} \le L_F(s,\chi) \le \zeta_F(s),\qquad L_F(s,\chi)^{-1} \ge \zeta_F(s)^{-1} \ge \zeta(s)^{-d},$$
and the lower bound behind Hanke 2004 Thm 5.7(c)'s constant $E_n(X)$ (with $s = (n-1)/2$, $n \ge 5$ odd):
$$L_F(s,\chi) \ge \prod_{\mathfrak p}(1 + N\mathfrak p^{-s})^{-1} \ge E(X) =
  \frac{\prod_{p^d \le X}(1 + p^{-s})^d}{\prod_{N\mathfrak p \le X}(1 + N\mathfrak p^{-s})}\Big(\frac{\zeta(2s)}{\zeta(s)}\Big)^d
  \qquad(\texttt{hankeEX\_le\_LFunctionNF}),$$
and the X-free bound $L_F(s,\chi) \ge (\zeta(2s)/\zeta(s))^d$ (`zeta_ratio_pow_le_LFunctionNF`).

*Update (Hanke 2004, proof of Thm 5.7(c), pp. 375–376):* the step
$\prod_{N\mathfrak p > X}(1 + N\mathfrak p^{-s}) \le \prod_{p > X}(1 + p^{-s})^d$ ("taking all primes $\mathfrak p \mid p$ to split
completely") is not valid as stated: a prime over $p \le X$ can have $N\mathfrak p > X$ (e.g. $F = \mathbb{Q}(\sqrt5)$, $X = 3$,
$s = 3$: the inert primes $2, 3$ have norms $4, 9$, and the left side exceeds the right by a factor $\approx 1.0015$). It holds
with $\prod_{p^d > X}$ in place of $\prod_{p > X}$ (`hankeE_le_LFunctionNF` with $B = \{p : p^d \le X\}$). *Erratum:* the
printed $E_n(X)$ has $\prod_{p<X}(1/(1 + 1/p^s))^d$ in the numerator; the argument gives $\prod_{p<X}(1 + 1/p^s)^d$
(only this makes the bound "optimal as $X \to \infty$"). The printed constant is still a valid (weaker) lower bound,
since it is $\le (\zeta(2s)/\zeta(s))^d$ (`hankeEPrinted_le_LFunctionNF`).

Sources: Neukirch, *Algebraic Number Theory*, Ch. VII §8 (Hecke $L$-series, Euler products) [unverified locator];
Hanke 2004, Thm 5.7 and its proof, pp. 372–376.
-/
import QuadFormsKB.Analysis.NFEulerProduct

open NumberField IsDedekindDomain Filter Topology

set_option linter.unusedSectionVars false

namespace QuadFormsKB.NFEuler

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ### Definitions -/

open Classical in
/-- **$\chi$ with the primes dividing $\mathfrak N$ removed:** $\chi(\mathfrak p)$ if $\mathfrak p \nmid \mathfrak N$ and $0$ if
$\mathfrak p \mid \mathfrak N$ (i.e. $\mathfrak N \subseteq \mathfrak p$). -/
@[kb "hanke2004" "Thm 5.7 proof, p. 374 (χ on 𝔭 ∤ N)"]
def charOff (𝔑 : Ideal (𝓞 F)) (χ : HeightOneSpectrum (𝓞 F) → ℝ) (𝔭 : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if 𝔑 ≤ 𝔭.asIdeal then 0 else χ 𝔭

theorem abs_charOff_le {𝔑 : Ideal (𝓞 F)} {χ : HeightOneSpectrum (𝓞 F) → ℝ}
    (hχ : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), ¬ 𝔑 ≤ 𝔭.asIdeal → |χ 𝔭| ≤ 1) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    |charOff 𝔑 χ 𝔭| ≤ 1 := by
  unfold charOff
  split_ifs with h
  · simp
  · exact hχ 𝔭 h

/-- **The local $L$-factor** $(1 - \chi(\mathfrak p)N\mathfrak p^{-s})^{-1}$. -/
def lFactor (χ : HeightOneSpectrum (𝓞 F) → ℝ) (s : ℝ) (𝔭 : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (1 - χ 𝔭 * (normP 𝔭 : ℝ) ^ (-s))⁻¹

/-- **The $L$-function $L_F(s,\chi) = \prod_{\mathfrak p}(1 - \chi(\mathfrak p)N\mathfrak p^{-s})^{-1}$** (Mathlib's unconditional
product `tprod`). *Use for real $s > 1$ and $|\chi| \le 1$*, where it converges (`hasProd_LFunctionNF`); at $s = 1$ the
product converges only conditionally and Hanke's $L_F(1,\psi)$ is kept as a hypothesis (use `IsEulerProductValueNF`). -/
@[kb "hanke2004" "Thm 5.7, p. 372 (L_F(s, χ))"]
def LFunctionNF (χ : HeightOneSpectrum (𝓞 F) → ℝ) (s : ℝ) : ℝ :=
  ∏' 𝔭, lFactor χ s 𝔭

/-! ### Pointwise bounds for the factors -/

section factor

variable {c x : ℝ}

theorem one_sub_mul_pos (hc : |c| ≤ 1) (hx0 : 0 < x) (hx : x ≤ 1 / 2) : 0 < 1 - c * x := by
  have : |c * x| ≤ x := by
    rw [abs_mul, abs_of_pos hx0]; exact mul_le_of_le_one_left hx0.le hc
  have := (abs_le.mp this).2; linarith

theorem abs_inv_one_sub_mul_sub_one_le (hc : |c| ≤ 1) (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |(1 - c * x)⁻¹ - 1| ≤ 2 * x := by
  have hpos := one_sub_mul_pos hc hx0 hx
  have hcx : |c * x| ≤ x := by
    rw [abs_mul, abs_of_pos hx0]; exact mul_le_of_le_one_left hx0.le hc
  have hge : 1 / 2 ≤ 1 - c * x := by have := (abs_le.mp hcx).2; linarith
  rw [show (1 - c * x)⁻¹ - 1 = c * x / (1 - c * x) by field_simp; ring, abs_div,
    abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith

theorem inv_one_add_le_inv_one_sub_mul (hc : |c| ≤ 1) (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    (1 + x)⁻¹ ≤ (1 - c * x)⁻¹ := by
  have hpos := one_sub_mul_pos hc hx0 hx
  have hcx : |c * x| ≤ x := by
    rw [abs_mul, abs_of_pos hx0]; exact mul_le_of_le_one_left hx0.le hc
  exact inv_anti₀ hpos (by have := (abs_le.mp hcx).1; linarith)

theorem inv_one_sub_mul_le_inv_one_sub (hc : |c| ≤ 1) (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    (1 - c * x)⁻¹ ≤ (1 - x)⁻¹ := by
  have hcx : |c * x| ≤ x := by
    rw [abs_mul, abs_of_pos hx0]; exact mul_le_of_le_one_left hx0.le hc
  exact inv_anti₀ (by linarith) (by have := (abs_le.mp hcx).2; linarith)

theorem one_sub_le_inv_one_add (hx0 : 0 < x) : 1 - x ≤ (1 + x)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
  nlinarith

end factor

/-! ### Convergence and the bounds $\zeta_F^{-1} \le L_F \le \zeta_F$ -/

variable {χ : HeightOneSpectrum (𝓞 F) → ℝ} {s : ℝ}

theorem lFactor_bounds (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹ ≤ lFactor χ s 𝔭 ∧ lFactor χ s 𝔭 ≤ (1 - (normP 𝔭 : ℝ) ^ (-s))⁻¹ := by
  obtain ⟨h0, h1⟩ := rpow_neg_mem (two_le_normP 𝔭) hs.le
  exact ⟨inv_one_add_le_inv_one_sub_mul (hχ 𝔭) h0 h1, inv_one_sub_mul_le_inv_one_sub (hχ 𝔭) h0 h1⟩

theorem lFactor_pos (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    0 < lFactor χ s 𝔭 := by
  obtain ⟨h0, h1⟩ := rpow_neg_mem (two_le_normP 𝔭) hs.le
  exact inv_pos.mpr (one_sub_mul_pos (hχ 𝔭) h0 h1)

/-- **$L_F(s,\chi)$ converges absolutely for real $s > 1$** (by the Euler product convergence criterion with $|\ell_{\mathfrak p} - 1| \le 2N\mathfrak p^{-s}$). -/
theorem hasProd_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) :
    HasProd (lFactor χ s) (LFunctionNF χ s) := by
  refine (multipliable_of_abs_sub_one_le (lFactor χ s) (C := 2) hs
    (Eventually.of_forall fun 𝔭 => ?_)).hasProd
  obtain ⟨h0, h1⟩ := rpow_neg_mem (two_le_normP 𝔭) hs.le
  exact abs_inv_one_sub_mul_sub_one_le (hχ 𝔭) h0 h1

/-- **$L_F(s,\chi) \le \zeta_F(s)$** for real $s > 1$ and $|\chi| \le 1$. -/
@[kb "hanke2004" "Thm 5.7 proof, p. 375 (L_F(s, χ) ≤ ζ_F(s)) [unverified]"]
theorem LFunctionNF_le_dedekindZetaR (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) :
    LFunctionNF χ s ≤ dedekindZetaR F s :=
  le_of_tendsto_of_tendsto' (hasProd_LFunctionNF hχ hs) (hasProd_dedekindZeta hs) fun _ =>
    Finset.prod_le_prod₀ (fun 𝔭 _ => (lFactor_pos hχ hs 𝔭).le) fun 𝔭 _ => (lFactor_bounds hχ hs 𝔭).2

/-- Every finite partial product of $\prod_{\mathfrak p}(1 + N\mathfrak p^{-s})^{-1}$ bounds $L_F(s,\chi)$ from below
in the limit: if $c \le \prod_{\mathfrak p \in T}(1 + N\mathfrak p^{-s})^{-1}$ for all finite $T$, then $c \le L_F(s,\chi)$. -/
theorem le_LFunctionNF_of_forall (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) {c : ℝ}
    (hc : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), c ≤ ∏ 𝔭 ∈ T, (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹) :
    c ≤ LFunctionNF χ s :=
  ge_of_tendsto' (hasProd_LFunctionNF hχ hs) fun T => (hc T).trans
    (Finset.prod_le_prod₀ (fun 𝔭 _ => inv_nonneg.mpr (by
      have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).1; linarith)) fun 𝔭 _ =>
      (lFactor_bounds hχ hs 𝔭).1)

/-- **$\zeta_F(s)^{-1} \le L_F(s,\chi)$** for real $s > 1$ and $|\chi| \le 1$. -/
@[kb "hanke2004" "Thm 5.7 proof, p. 375 (L_F(s, χ) ≥ ζ_F(s)⁻¹) [unverified]"]
theorem inv_dedekindZetaR_le_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) :
    (dedekindZetaR F s)⁻¹ ≤ LFunctionNF χ s :=
  le_of_tendsto_of_tendsto' (hasProd_one_sub_rpow hs) (hasProd_LFunctionNF hχ hs) fun _ =>
    Finset.prod_le_prod₀ (fun 𝔭 _ => by
      have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).2; linarith) fun 𝔭 _ =>
      (one_sub_le_inv_one_add (rpow_neg_mem (two_le_normP 𝔭) hs.le).1).trans (lFactor_bounds hχ hs 𝔭).1

theorem LFunctionNF_pos (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) : 0 < LFunctionNF χ s :=
  lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le one_pos (one_le_dedekindZetaR hs)))
    (inv_dedekindZetaR_le_LFunctionNF hχ hs)

/-- **$1/L_F(s,\chi) \ge \zeta_F(s)^{-1} \ge \zeta(s)^{-d}$** for real $s > 1$ and $|\chi| \le 1$ (Hanke 2004
Thm 5.7(b) over $F$ uses $s = 2$). -/
@[kb "hanke2004" "Thm 5.7(b), p. 373 (1/L_F(2, χ) ≥ ζ(2)^{-d}) [unverified]"]
theorem zetaR_pow_inv_le_inv_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) :
    (zetaR s ^ Module.finrank ℚ F)⁻¹ ≤ (dedekindZetaR F s)⁻¹ ∧
      (dedekindZetaR F s)⁻¹ ≤ (LFunctionNF χ s)⁻¹ := by
  have hz : 0 < dedekindZetaR F s := lt_of_lt_of_le one_pos (one_le_dedekindZetaR hs)
  exact ⟨inv_anti₀ hz (dedekindZetaR_le_zetaR_pow hs),
    inv_anti₀ (LFunctionNF_pos hχ hs) (LFunctionNF_le_dedekindZetaR hχ hs)⟩

/-! ### $\prod_p(1 + p^{-s}) = \zeta(s)/\zeta(2s)$ and Hanke's $E_n(X)$ -/

/-- $\prod_p (1 + p^{-s}) = \zeta(s)/\zeta(2s)$ for real $s > 1$. -/
theorem hasProd_one_add_rpow_primes (hs : 1 < s) :
    HasProd (fun p : Nat.Primes => 1 + ((p : ℕ) : ℝ) ^ (-s)) (zetaR s / zetaR (2 * s)) := by
  have h2s : 1 < 2 * s := by linarith
  have hz2 : 0 < zetaR (2 * s) := lt_of_lt_of_le one_pos (one_le_zetaR h2s)
  have hinv := (hasProd_zetaR h2s).inv₀ hz2.ne'
  have h := (hasProd_zetaR hs).mul hinv
  rw [← div_eq_mul_inv] at h
  refine h.congr_fun fun p => ?_
  obtain ⟨h0, h1⟩ := rpow_neg_mem p.2.two_le hs.le
  rw [show -(2 * s) = (-s) * 2 by ring, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two, inv_inv]
  have hx : 1 - ((p : ℕ) : ℝ) ^ (-s) ≠ 0 := by linarith
  field_simp
  ring


/-- **Grouping bound for $\prod(1 + N\mathfrak p^{-s})$:** if no $\mathfrak p \in T$ lies over a prime of $B$, then
$\prod_{\mathfrak p \in T}(1 + N\mathfrak p^{-s})\cdot\prod_{p \in B}(1 + p^{-s})^d \le (\zeta(s)/\zeta(2s))^d$. -/
theorem prod_one_add_mul_le (hs : 1 < s) (T : Finset (HeightOneSpectrum (𝓞 F))) (B : Finset Nat.Primes)
    (hTB : ∀ 𝔭 ∈ T, primeBelow 𝔭 ∉ B) :
    (∏ 𝔭 ∈ T, (1 + (normP 𝔭 : ℝ) ^ (-s))) * (∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F
      ≤ (zetaR s / zetaR (2 * s)) ^ Module.finrank ℚ F := by
  classical
  have hu1 : ∀ n : ℕ, 2 ≤ n → 1 ≤ 1 + (n : ℝ) ^ (-s) := fun n hn => by
    have := (rpow_neg_mem hn hs.le).1; linarith
  have hanti : ∀ m n : ℕ, 2 ≤ m → m ≤ n → 1 + (n : ℝ) ^ (-s) ≤ 1 + (m : ℝ) ^ (-s) :=
    fun m n hm hmn => by linarith [rpow_neg_anti hm hmn (by linarith : (0 : ℝ) < s)]
  have h1 := prod_le_prod_primeBelow_pow (fun n : ℕ => 1 + (n : ℝ) ^ (-s)) hu1 hanti T
  rw [Finset.prod_pow] at h1
  have hdisj : Disjoint (T.image primeBelow) B := by
    rw [Finset.disjoint_left]
    intro p hp hpB
    obtain ⟨𝔭, h𝔭, rfl⟩ := Finset.mem_image.mp hp
    exact hTB 𝔭 h𝔭 hpB
  have h2 : (∏ p ∈ T.image primeBelow, (1 + ((p : ℕ) : ℝ) ^ (-s))) *
      ∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s)) ≤ zetaR s / zetaR (2 * s) := by
    rw [← Finset.prod_union hdisj]
    exact prod_le_of_hasProd (hasProd_one_add_rpow_primes hs) (fun p => hu1 _ p.2.two_le) _
  have hnn : ∀ S : Finset Nat.Primes, 0 ≤ ∏ p ∈ S, (1 + ((p : ℕ) : ℝ) ^ (-s)) := fun S =>
    Finset.prod_nonneg fun p _ => zero_le_one.trans (hu1 _ p.2.two_le)
  calc (∏ 𝔭 ∈ T, (1 + (normP 𝔭 : ℝ) ^ (-s))) * (∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F
      ≤ (∏ p ∈ T.image primeBelow, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F *
          (∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (hnn B) _)
    _ = ((∏ p ∈ T.image primeBelow, (1 + ((p : ℕ) : ℝ) ^ (-s))) *
          ∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (hnn _) (hnn B)) h2 _

theorem one_add_rpow_normP_pos (hs : 1 < s) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    0 < 1 + (normP 𝔭 : ℝ) ^ (-s) := by
  have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).1; linarith

/-- **The X-free lower bound $L_F(s,\chi) \ge (\zeta(2s)/\zeta(s))^d$** for real $s > 1$ and $|\chi| \le 1$
($L_F(s,\chi) \ge \prod_{\mathfrak p}(1 + N\mathfrak p^{-s})^{-1} \ge \prod_p(1 + p^{-s})^{-d}$). -/
@[kb "hanke2004" "Thm 5.7 proof, p. 375 (L_F(s, χ) ≥ (ζ(2s)/ζ(s))^d) [unverified]"]
theorem zeta_ratio_pow_le_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) :
    (zetaR (2 * s) / zetaR s) ^ Module.finrank ℚ F ≤ LFunctionNF χ s := by
  refine le_LFunctionNF_of_forall hχ hs fun T => ?_
  have h := prod_one_add_mul_le hs T ∅ (by simp)
  simp only [Finset.prod_empty, one_pow, mul_one] at h
  rw [Finset.prod_inv_distrib, ← inv_div, inv_pow]
  exact inv_anti₀ (Finset.prod_pos fun 𝔭 _ => one_add_rpow_normP_pos hs 𝔭) h

/-- **Hanke's constant $E(A, B)$, corrected:** for a finite set $A$ of primes of $F$ and a finite set $B$ of rational
primes,
$$E_s(A, B) = \frac{\prod_{p \in B}(1 + p^{-s})^d}{\prod_{\mathfrak p \in A}(1 + N\mathfrak p^{-s})}
  \Big(\frac{\zeta(2s)}{\zeta(s)}\Big)^d .$$
With $A = \{N\mathfrak p \le X\}$ and $B = \{p : p^d \le X\}$ this is `hankeEX` (Hanke 2004 Thm 5.7(c)'s $E_n(X)$ with
$s = (n-1)/2$, corrected: see the module docstring). -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (E_n(X), corrected)"]
def hankeE (F : Type) [Field F] [NumberField F] (s : ℝ) (A : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Finset Nat.Primes) : ℝ :=
  (∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F / (∏ 𝔭 ∈ A, (1 + (normP 𝔭 : ℝ) ^ (-s))) *
    (zetaR (2 * s) / zetaR s) ^ Module.finrank ℚ F

/-- **$L_F(s,\chi) \ge E_s(A, B)$** whenever every prime of $F$ over a prime of $B$ lies in $A$
(Hanke 2004, proof of Thm 5.7(c), pp. 375–376, with the threshold corrected). -/
@[kb "hanke2004" "Thm 5.7(c) proof, pp. 375–376 (L_F(s, Φ) ≥ E_n(X), corrected)"]
theorem hankeE_le_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s)
    (A : Finset (HeightOneSpectrum (𝓞 F))) (B : Finset Nat.Primes)
    (hAB : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), primeBelow 𝔭 ∈ B → 𝔭 ∈ A) :
    hankeE F s A B ≤ LFunctionNF χ s := by
  classical
  refine le_LFunctionNF_of_forall hχ hs fun T => ?_
  have hv0 := one_add_rpow_normP_pos (F := F) hs
  have hv1 : ∀ 𝔭 : HeightOneSpectrum (𝓞 F), (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹ ≤ 1 := fun 𝔭 =>
    inv_le_one_of_one_le₀ (by have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).1; linarith)
  rw [← Finset.prod_filter_mul_prod_filter_not T (· ∈ A)]
  have hA : ∏ 𝔭 ∈ A, (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹ ≤
      ∏ 𝔭 ∈ T with 𝔭 ∈ A, (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹ :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (fun 𝔭 h => (Finset.mem_filter.mp h).2)
      (fun 𝔭 _ => (inv_pos.mpr (hv0 𝔭)).le) fun 𝔭 _ _ => hv1 𝔭
  set Q := (∏ p ∈ B, (1 + ((p : ℕ) : ℝ) ^ (-s))) ^ Module.finrank ℚ F with hQ
  set Z := (zetaR s / zetaR (2 * s)) ^ Module.finrank ℚ F with hZ
  set P := ∏ 𝔭 ∈ T with 𝔭 ∉ A, (1 + (normP 𝔭 : ℝ) ^ (-s)) with hP
  have hPpos : 0 < P := Finset.prod_pos fun 𝔭 _ => hv0 𝔭
  have hZpos : 0 < Z := pow_pos (div_pos (lt_of_lt_of_le one_pos (one_le_zetaR hs))
    (lt_of_lt_of_le one_pos (one_le_zetaR (by linarith)))) _
  have hQnn : 0 ≤ Q := pow_nonneg (Finset.prod_nonneg fun p _ => by
    have := (rpow_neg_mem p.2.two_le hs.le).1; linarith) _
  have hPQ : P * Q ≤ Z := prod_one_add_mul_le hs _ B fun 𝔭 h hB =>
    (Finset.mem_filter.mp h).2 (hAB 𝔭 hB)
  have hR : Q * Z⁻¹ ≤ ∏ 𝔭 ∈ T with 𝔭 ∉ A, (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹ := by
    rw [Finset.prod_inv_distrib, ← hP, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hZpos hPpos]
    linarith
  have hE : hankeE F s A B = (∏ 𝔭 ∈ A, (1 + (normP 𝔭 : ℝ) ^ (-s))⁻¹) * (Q * Z⁻¹) := by
    rw [hankeE, Finset.prod_inv_distrib, hQ, hZ, ← inv_div (zetaR s), inv_pow]
    ring
  rw [hE]
  exact mul_le_mul hA hR (mul_nonneg hQnn (inv_nonneg.mpr hZpos.le))
    (Finset.prod_nonneg fun 𝔭 _ => (inv_pos.mpr (hv0 𝔭)).le)

/-- The rational primes $p$ with $p^d \le X$. -/
def primesPowLe (F : Type) [Field F] [NumberField F] (X : ℕ) : Finset Nat.Primes :=
  (((Finset.range (X + 1)).filter fun n => n ^ Module.finrank ℚ F ≤ X).subtype Nat.Prime :
    Finset Nat.Primes)

/-- **Hanke's $E_n(X)$, corrected** (Thm 5.7(c), p. 373, with $s = (n-1)/2$):
$$E(X) = \frac{\prod_{p^d \le X}(1 + p^{-s})^d}{\prod_{N\mathfrak p \le X}(1 + N\mathfrak p^{-s})}
  \Big(\frac{\zeta(2s)}{\zeta(s)}\Big)^d .$$
*Erratum/Update:* printed with $\prod_{p<X}(1/(1 + 1/p^s))^{[F:\mathbb{Q}]}$ in the numerator (`hankeEPrinted`); see the
module docstring. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (E_n(X), corrected)"]
def hankeEX (F : Type) [Field F] [NumberField F] (s : ℝ) (X : ℕ) : ℝ :=
  hankeE F s (primesNormLe F X) (primesPowLe F X)

/-- **$L_F(s,\chi) \ge E(X)$ for every $X$** (corrected Hanke 2004, proof of Thm 5.7(c), p. 376): a prime $\mathfrak p$ over
$p$ with $p^d \le X$ has $N\mathfrak p \le p^d \le X$. -/
@[kb "hanke2004" "Thm 5.7(c) proof, p. 376 (L_F(s, Φ) ≥ E_n(X), corrected)"]
theorem hankeEX_le_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) (X : ℕ) :
    hankeEX F s X ≤ LFunctionNF χ s := by
  refine hankeE_le_LFunctionNF hχ hs _ _ fun 𝔭 h => ?_
  have h' : ((primeBelow 𝔭 : ℕ)) ∈ (Finset.range (X + 1)).filter
      fun n => n ^ Module.finrank ℚ F ≤ X :=
    (Finset.mem_subtype (p := Nat.Prime) (a := (primeBelow 𝔭 : {n : ℕ // Nat.Prime n}))).mp h
  rw [Finset.mem_filter] at h'
  exact mem_primesNormLe.mpr ((normP_le_pow_finrank 𝔭).trans h'.2)

/-- **Hanke's $E_n(X)$ as printed** (Thm 5.7(c), p. 373):
$$\frac{\prod_{p<X}(1/(1 + 1/p^s))^{[F:\mathbb{Q}]}}{\prod_{N\mathfrak p \le X}(1 + 1/N\mathfrak p^s)}
  \Big(\frac{\zeta_{\mathbb{Q}}(2s)}{\zeta_{\mathbb{Q}}(s)}\Big)^{[F:\mathbb{Q}]} .$$ -/
def hankeEPrinted (F : Type) [Field F] [NumberField F] (s : ℝ) (X : ℕ) : ℝ :=
  (∏ p ∈ ((Finset.range X).subtype Nat.Prime : Finset Nat.Primes), (1 + ((p : ℕ) : ℝ) ^ (-s))⁻¹) ^
      Module.finrank ℚ F / (∏ 𝔭 ∈ primesNormLe F X, (1 + (normP 𝔭 : ℝ) ^ (-s))) *
    (zetaR (2 * s) / zetaR s) ^ Module.finrank ℚ F

/-- **The printed $E_n(X)$ is still a valid lower bound** (weaker than the X-free one):
$E_n^{\mathrm{printed}}(X) \le (\zeta(2s)/\zeta(s))^d \le L_F(s,\chi)$. -/
@[kb "hanke2004" "Thm 5.7(c), p. 373 (E_n(X) as printed)"]
theorem hankeEPrinted_le_LFunctionNF (hχ : ∀ 𝔭, |χ 𝔭| ≤ 1) (hs : 1 < s) (X : ℕ) :
    hankeEPrinted F s X ≤ LFunctionNF χ s := by
  refine le_trans ?_ (zeta_ratio_pow_le_LFunctionNF hχ hs)
  have hnum : (∏ p ∈ ((Finset.range X).subtype Nat.Prime : Finset Nat.Primes),
      (1 + ((p : ℕ) : ℝ) ^ (-s))⁻¹) ^ Module.finrank ℚ F ≤ 1 := by
    refine pow_le_one₀ (Finset.prod_nonneg fun p _ => ?_) (Finset.prod_le_one₀ (fun p _ => ?_) fun p _ => ?_)
    all_goals have := (rpow_neg_mem p.2.two_le hs.le).1
    · exact (inv_pos.mpr (by linarith)).le
    · exact (inv_pos.mpr (by linarith)).le
    · exact inv_le_one_of_one_le₀ (by linarith)
  have hden : 1 ≤ ∏ 𝔭 ∈ primesNormLe F X, (1 + (normP 𝔭 : ℝ) ^ (-s)) :=
    Finset.one_le_prod₀ fun 𝔭 _ => by have := (rpow_neg_mem (two_le_normP 𝔭) hs.le).1; linarith
  have hratio : 0 ≤ (zetaR (2 * s) / zetaR s) ^ Module.finrank ℚ F :=
    pow_nonneg (div_nonneg (zero_le_one.trans (one_le_zetaR (by linarith)))
      (zero_le_one.trans (one_le_zetaR hs))) _
  rw [hankeEPrinted]
  exact mul_le_of_le_one_left hratio (div_le_one_of_le₀ (hnum.trans hden) (zero_le_one.trans hden))

end

end QuadFormsKB.NFEuler
