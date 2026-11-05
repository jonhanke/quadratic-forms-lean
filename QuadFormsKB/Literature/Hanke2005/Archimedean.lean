/-
# Hanke 2005, §4 and Theorem 5.1: the archimedean constants

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Defines** the closed forms computed in §4:
* `tauR n` $=\tfrac12\pi^{n(n+1)/4}\prod_{l=1}^n\Gamma(l/2)^{-1}$, the volume $\tau_{\mathbb R}(SO_n(\mathbb R))$ for Hanke's
  $\widetilde\omega_G$ ((4.1.1), p. 10);
* `volCReal q r` $= 2\cdot2^{-rn/2}\,\tau_{\mathbb R}(SO_q)\,\tau_{\mathbb R}(SO_r)$, $n = q + r$, the volume of the stabilizer
  $C_{\mathbb R}$ of the base point of $Z_{\mathbb R}$ for $\omega_C$ (§4.2, pp. 12–13);
* `volCComplex n` $= 2^{n(n-3)/2}\,\tau_{\mathbb R}(SO_n)$, the volume of $C_{\mathbb C}\cong SO_n(\mathbb R)$ (§4.3, p. 15);
* Shimura's multivariate gamma function `gammaMulti i s` $=\Gamma_i(s) = \pi^{i(i-1)/4}\prod_{j=0}^{i-1}\Gamma(s - j/2)$ and
  `bPhi n r` $= b^\varphi_v = 2^{rn/2}\pi^{(n-r)r/2}\Gamma_r(r/2)\Gamma_r(n/2)^{-1}$ (Theorem 5.1, p. 17).

**Proves**
* `tauR_eq_two_pow_mul_archVolSO`: Hanke's $\tau_{\mathbb R}(SO_n(\mathbb R))$ is $2^{n(n-1)/2}$ times the repository's
  `archVolSO n 1` (the gauge-form volume in coefficient coordinates, `ArchVol.archVolSO_eq_volume`); the factor converts
  the coefficient coordinates $c_{ij} = 2t_{ij}$ ($i<j$) to Hanke's Gram coordinates $t_{ij}$;
* `volCReal_zero`: for $r = 0$ (definite) $\mathrm{vol}_C(C_{\mathbb R}) = \tau_{\mathbb R}(SO_n(\mathbb R))$;
* `inv_volCReal` (proof of Theorem 5.1, Part 2, p. 18): $\mathrm{vol}_C(C_v)^{-1} = \tau_{\mathbb R}(SO_n)^{-1}\,b^\varphi_v$;
* `inv_volCComplex` (Part 3, p. 19): $\mathrm{vol}_C(C_v)^{-1} = \tau_{\mathbb R}(SO_n)^{-2}\cdot
  2^{-(n-1)(n-2)/2}\pi^{n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)^{-1}$;
* `inv_tauR_odd`, `inv_tauR_even` (Part 1, p. 18, Legendre's duplication formula):
  $\tau_{\mathbb R}(SO_{2m+1})^{-1} = 2^{m+1}\prod_{j=1}^m\frac{(2j-1)!}{(2\pi)^{2j}}$ and
  $\tau_{\mathbb R}(SO_{2m})^{-1} = 2^{2m}\prod_{j=1}^{m-1}\frac{(2j-1)!}{(2\pi)^{2j}}\cdot(m-1)!\,(2\pi)^{-m}$.

Indices: Hanke's products $\prod_{l=1}^n$ are `∏ l ∈ Finset.range n` with $l+1$ in place of $l$.
-/
import QuadFormsKB.Tamagawa.MassFormula

open Real Finset

noncomputable section

namespace QuadFormsKB.Hanke2005

/-- **(4.1.1)** (Hanke thesis, §4.1, p. 10): the volume of $SO_n(\mathbb R)$ for Hanke's form $\widetilde\omega_G$,
$\tau_{\mathbb R}(SO_n(\mathbb R)) = \tfrac12\pi^{n(n+1)/4}\prod_{l=1}^n\Gamma(l/2)^{-1}$ (from Voskresenskiĭ, (14.6), p. 85). -/
@[kb "hanke2005crelle" "(4.1.1), p. 10"]
def tauR (n : ℕ) : ℝ :=
  (1 / 2) * π ^ ((n : ℝ) * (n + 1) / 4) * ∏ l ∈ range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹

/-- **$\mathrm{vol}_C(C_{\mathbb R})$** (Hanke thesis, §4.2, pp. 12–13): for $\varphi_v = \mathrm{diag}[1_q,-1_r]$, $q\ge r$,
$n = q + r$, the stabilizer $C_{\mathbb R}$ of $p_{\mathbb R}\in Z_{\mathbb R}$ has volume
$2\cdot2^{-rn/2}\,\tau_{\mathbb R}(SO_q(\mathbb R))\,\tau_{\mathbb R}(SO_r(\mathbb R))$ for the fibre form $\omega_C$. -/
@[kb "hanke2005crelle" "§4.2, pp. 12–13 (vol_C(C_R))"]
def volCReal (q r : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ (-((r : ℝ) * (q + r)) / 2) * tauR q * tauR r

/-- **$\mathrm{vol}_C(C_{\mathbb C})$** (Hanke thesis, §4.3, p. 15): $C_{\mathbb C}\cong SO_n(\mathbb R)$ has volume
$2^{n(n-3)/2}\cdot\tfrac12\pi^{n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)^{-1}$ for $\omega_C$. -/
@[kb "hanke2005crelle" "§4.3, p. 15 (vol_C(C_C))"]
def volCComplex (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((n : ℝ) * (n - 3) / 2) * tauR n

/-- **Shimura's multivariate gamma function** (Hanke thesis, Theorem 5.1, p. 17):
$\Gamma_i(s) = \pi^{i(i-1)/4}\prod_{j=0}^{i-1}\Gamma(s - j/2)$. -/
@[kb "hanke2005crelle" "Theorem 5.1, p. 17 (Γ_i(s))"]
def gammaMulti (i : ℕ) (s : ℝ) : ℝ :=
  π ^ ((i : ℝ) * (i - 1) / 4) * ∏ j ∈ range i, Gamma (s - j / 2)

/-- **$b^\varphi_v$** (Hanke thesis, Theorem 5.1, p. 17): for a real place with $r_v = r$ (the normalization (2.9),
$\varphi_v = \mathrm{diag}[1_q,-1_r]$, $q\ge r$), $b^\varphi_v = 2^{rn/2}\pi^{(n-r)r/2}\Gamma_r(r/2)\Gamma_r(n/2)^{-1}$; for a
definite place ($r = 0$) it is $1$ (`bPhi_zero`). -/
@[kb "hanke2005crelle" "Theorem 5.1, p. 17 (b^φ_v)"]
def bPhi (n r : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r : ℝ) * n / 2) * π ^ (((n : ℝ) - r) * r / 2) * gammaMulti r ((r : ℝ) / 2) *
    (gammaMulti r ((n : ℝ) / 2))⁻¹

theorem bPhi_zero (n : ℕ) : bPhi n 0 = 1 := by
  simp [bPhi, gammaMulti]

theorem tauR_pos (n : ℕ) : 0 < tauR n := by
  unfold tauR
  refine mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _)) ?_
  exact Finset.prod_pos fun l _ => inv_pos.2 (Real.Gamma_pos_of_pos (by positivity))

theorem prod_range_pi_rpow (n : ℕ) :
    ∏ j ∈ range n, π ^ (((j : ℝ) + 1) / 2) = π ^ ((n : ℝ) * (n + 1) / 4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, ← Real.rpow_add Real.pi_pos]
    congr 1; push_cast; ring

theorem tauR_zero : tauR 0 = 1 / 2 := by simp [tauR]

theorem tauR_succ_inv (n : ℕ) :
    (tauR (n + 1))⁻¹ = (tauR n)⁻¹ * Gamma (((n : ℝ) + 1) / 2) * π ^ (-(((n : ℝ) + 1) / 2)) := by
  have h : π ^ (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) / 4) =
      π ^ ((n : ℝ) * (n + 1) / 4) * π ^(((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; push_cast; ring
  have hg : 0 < Gamma (((n : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp1 : 0 < π ^ ((n : ℝ) * (n + 1) / 4) := Real.rpow_pos_of_pos Real.pi_pos _
  have hp2 : 0 < π ^ (((n : ℝ) + 1) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hP : 0 < ∏ l ∈ range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹ :=
    Finset.prod_pos fun l _ => inv_pos.2 (Real.Gamma_pos_of_pos (by positivity))
  unfold tauR
  rw [Finset.prod_range_succ, h, Real.rpow_neg Real.pi_pos.le]
  field_simp

/-- **(4.1.1) versus the repository's archimedean volume**: $\tau_{\mathbb R}(SO_n(\mathbb R)) = 2^{n(n-1)/2}\,$`archVolSO n 1`
(every $n$; for $n = 0$ both sides are $\tfrac12$). `archVolSO n 1` is the gauge-form volume $\mathrm{vol}(SO_n(\mathbb R), dX/dS)$ in the coefficient coordinates of the
form $x_0^2+\dots+x_{n-1}^2$ (proved: `ArchVol.archVolSO_eq_volume`); Hanke's $dT = \prod_{i\le j}dt_{ij}$ uses the Gram
entries, $dS = 2^{n(n-1)/2}dT$. -/
@[kb "hanke2005crelle" "(4.1.1), p. 10 (comparison with the coefficient normalization)"]
theorem tauR_eq_two_pow_mul_archVolSO (n : ℕ) :
    tauR n = (2 : ℝ) ^ (n * (n - 1) / 2) * Tamagawa.archVolSO n 1 := by
  unfold tauR Tamagawa.archVolSO
  rw [Finset.prod_div_distrib, prod_range_pi_rpow, Finset.prod_inv_distrib, Real.one_rpow]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n * (n - 1) / 2) := by positivity
  field_simp

/-- For a definite real place ($r = 0$): $\mathrm{vol}_C(C_{\mathbb R}) = \tau_{\mathbb R}(SO_n(\mathbb R))$ (Hanke thesis, §4,
p. 9: "when $v$ is real and $\varphi$ is definite … $C_v = G_v$"). -/
theorem volCReal_zero (q : ℕ) : volCReal q 0 = tauR q := by
  have : tauR 0 = 1 / 2 := tauR_zero
  simp [volCReal, this]
  ring

theorem gammaMulti_shift (q r : ℕ) :
    gammaMulti r (((q : ℝ) + r) / 2) =
      π ^ ((r : ℝ) * (r - 1) / 4) * ∏ l ∈ range r, Gamma ((((q : ℝ) + l) + 1) / 2) := by
  unfold gammaMulti
  congr 1
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem prod_gamma_add (q r : ℕ) :
    ∏ l ∈ range (q + r), Gamma (((l : ℝ) + 1) / 2) =
      (∏ l ∈ range q, Gamma (((l : ℝ) + 1) / 2)) *
        ∏ l ∈ range r, Gamma ((((q : ℝ) + l) + 1) / 2) := by
  rw [Finset.prod_range_add]
  push_cast
  rfl

/-- **Part 2 of the proof of Theorem 5.1** (Hanke thesis, p. 18): at a real place with $\varphi_v = \mathrm{diag}[1_q,-1_r]$,
$n = q+r$, $\mathrm{vol}_C(C_v)^{-1} = 2\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2)\cdot b^\varphi_v = \tau_{\mathbb R}(SO_n)^{-1}b^\varphi_v$. -/
@[kb "hanke2005crelle" "proof of Theorem 5.1, Part 2, p. 18"]
theorem inv_volCReal (q r : ℕ) : (volCReal q r)⁻¹ = (tauR (q + r))⁻¹ * bPhi (q + r) r := by
  have hl : gammaMulti r ((r : ℝ) / 2) =
      π ^ ((r : ℝ) * (r - 1) / 4) * ∏ l ∈ range r, Gamma (((l : ℝ) + 1) / 2) := by
    have := gammaMulti_shift 0 r
    simpa using this
  have hr : gammaMulti r (((q + r : ℕ) : ℝ) / 2) =
      π ^ ((r : ℝ) * (r - 1) / 4) * ∏ l ∈ range r, Gamma ((((q : ℝ) + l) + 1) / 2) := by
    rw [← gammaMulti_shift]; push_cast; rfl
  have hP := prod_gamma_add q r
  have hx : 0 < ∏ l ∈ range q, Gamma (((l : ℝ) + 1) / 2) :=
    Finset.prod_pos fun l _ => Real.Gamma_pos_of_pos (by positivity)
  have hy : 0 < ∏ l ∈ range r, Gamma (((l : ℝ) + 1) / 2) :=
    Finset.prod_pos fun l _ => Real.Gamma_pos_of_pos (by positivity)
  have hQ : 0 < ∏ l ∈ range r, Gamma ((((q : ℝ) + l) + 1) / 2) :=
    Finset.prod_pos fun l _ => Real.Gamma_pos_of_pos (by positivity)
  have hπ : π ^ (((q + r : ℕ) : ℝ) * (((q + r : ℕ) : ℝ) + 1) / 4) =
      π ^ ((q : ℝ) * (q + 1) / 4) * π ^ ((r : ℝ) * (r + 1) / 4) * π ^ ((q : ℝ) * r / 2) := by
    rw [← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos]; congr 1; push_cast; ring
  have hπ2 : π ^ ((((q + r : ℕ) : ℝ) - r) * r / 2) = π ^ ((q : ℝ) * r / 2) := by
    congr 1; push_cast; ring
  have h2 : (2 : ℝ) ^ (-((r : ℝ) * (q + r)) / 2) * (2 : ℝ) ^ (((r : ℝ) * ((q + r : ℕ) : ℝ)) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; push_cast; rw [show -((r : ℝ) * (q + r)) / 2 + (r : ℝ) * (q + r) / 2 = 0 by ring]; simp
  have hA := Real.rpow_pos_of_pos Real.pi_pos ((q : ℝ) * (q + 1) / 4)
  have hB := Real.rpow_pos_of_pos Real.pi_pos ((r : ℝ) * (r + 1) / 4)
  have hC := Real.rpow_pos_of_pos Real.pi_pos ((q : ℝ) * r / 2)
  have hD := Real.rpow_pos_of_pos Real.pi_pos ((r : ℝ) * (r - 1) / 4)
  have hE : 0 < (2 : ℝ) ^ (-((r : ℝ) * (q + r)) / 2) := by positivity
  have hF : 0 < (2 : ℝ) ^ (((r : ℝ) * ((q + r : ℕ) : ℝ)) / 2) := by positivity
  unfold volCReal tauR bPhi
  rw [hl, hr, hπ, hπ2]
  simp only [Finset.prod_inv_distrib]
  rw [hP]
  simp only [mul_inv]
  generalize (2 : ℝ) ^ (-((r : ℝ) * (q + r)) / 2) = e at *
  generalize (2 : ℝ) ^ (((r : ℝ) * ((q + r : ℕ) : ℝ)) / 2) = f at *
  generalize π ^ ((q : ℝ) * (q + 1) / 4) = a at *
  generalize π ^ ((r : ℝ) * (r + 1) / 4) = b at *
  generalize π ^ ((q : ℝ) * r / 2) = c at *
  generalize π ^ ((r : ℝ) * (r - 1) / 4) = d at *
  generalize (∏ l ∈ range q, Gamma (((l : ℝ) + 1) / 2)) = x at *
  generalize (∏ l ∈ range r, Gamma (((l : ℝ) + 1) / 2)) = y at *
  generalize (∏ l ∈ range r, Gamma ((((q : ℝ) + l) + 1) / 2)) = Q at *
  have hef : f = e⁻¹ := by field_simp; linarith
  subst hef
  field_simp

/-- **Part 3 of the proof of Theorem 5.1** (Hanke thesis, p. 19): at a complex place,
$\mathrm{vol}_C(C_v)^{-1} = \big(2\pi^{-n(n+1)/4}\prod_j\Gamma(j/2)\big)^2\cdot2^{-(n-1)(n-2)/2}\pi^{n(n+1)/4}\prod_j\Gamma(j/2)^{-1}$
(with $b^\varphi_v = 1$): each complex place replaces two real places of the totally definite formula, with a correction. -/
@[kb "hanke2005crelle" "proof of Theorem 5.1, Part 3, p. 19"]
theorem inv_volCComplex (n : ℕ) :
    (volCComplex n)⁻¹ = (tauR n)⁻¹ ^ 2 * ((2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) *
      π ^ ((n : ℝ) * (n + 1) / 4) * ∏ l ∈ range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹) := by
  have hT : π ^ ((n : ℝ) * (n + 1) / 4) * ∏ l ∈ range n, (Gamma (((l : ℝ) + 1) / 2))⁻¹ =
      2 * tauR n := by unfold tauR; ring
  have hpos := tauR_pos n
  have h2 : (2 : ℝ) ^ ((n : ℝ) * (n - 3) / 2) * (2 : ℝ) ^ (-((n : ℝ) * (n - 3) / 2) - 1) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num)]
    have : (n : ℝ) * (n - 3) / 2 + (-((n : ℝ) * (n - 3) / 2) - 1) = -1 := by ring
    rw [this, Real.rpow_neg_one]; norm_num
  have h3 : (2 : ℝ) ^ (-(((n : ℝ) - 1) * (n - 2)) / 2) = (2 : ℝ) ^ (-((n : ℝ) * (n - 3) / 2) - 1) := by
    congr 1; ring
  rw [mul_assoc _ (π ^ _) _, hT, h3]
  unfold volCComplex
  have h4 : 0 < (2 : ℝ) ^ ((n : ℝ) * (n - 3) / 2) := by positivity
  have h5 : 0 < (2 : ℝ) ^ (-((n : ℝ) * (n - 3) / 2) - 1) := by positivity
  generalize (2 : ℝ) ^ ((n : ℝ) * (n - 3) / 2) = a at *
  generalize (2 : ℝ) ^ (-((n : ℝ) * (n - 3) / 2) - 1) = b at *
  generalize tauR n = t at *
  field_simp
  nlinarith [h2]

/-- **Part 1 of the proof of Theorem 5.1, odd $n = 2m+1$** (Hanke thesis, p. 18, "by rearranging terms"; Legendre's
duplication formula): $\tau_{\mathbb R}(SO_{2m+1})^{-1} = 2\pi^{-n(n+1)/4}\prod_{j=1}^n\Gamma(j/2) =
2^{m+1}\prod_{j=1}^m\frac{(2j-1)!}{(2\pi)^{2j}}$. -/
@[kb "hanke2005crelle" "proof of Theorem 5.1, Part 1, p. 18"]
theorem inv_tauR_odd (m : ℕ) :
    (tauR (2 * m + 1))⁻¹ = (2 : ℝ) ^ (m + 1) *
      ∏ j ∈ range m, ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1))) := by
  induction m with
  | zero =>
    have h := tauR_succ_inv 0
    rw [tauR_zero] at h
    simp only [Nat.cast_zero, zero_add] at h
    have hs : Gamma (1 / 2) = √π := Real.Gamma_one_half_eq
    have hp : √π * π ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]; norm_num
    simp only [Nat.mul_zero, zero_add, Finset.range_zero, Finset.prod_empty]
    rw [h, hs, mul_assoc, hp]; norm_num
  | succ m ih =>
    have e1 : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    rw [e1, tauR_succ_inv (2 * m + 1 + 1), tauR_succ_inv (2 * m + 1)]
    have hg1 : Gamma ((((2 * m + 1 : ℕ) : ℝ) + 1) / 2) = Gamma ((m : ℝ) + 1) := by
      congr 1; push_cast; ring
    have hg2 : Gamma ((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2) = Gamma ((m : ℝ) + 1 + 1 / 2) := by
      congr 1; push_cast; ring
    have hdup := Real.Gamma_mul_Gamma_add_half ((m : ℝ) + 1)
    have hfac : Gamma (2 * ((m : ℝ) + 1)) = (Nat.factorial (2 * m + 1) : ℝ) := by
      rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
    have h2p : (2 : ℝ) ^ (1 - 2 * ((m : ℝ) + 1)) = ((2 : ℝ) ^ (2 * m + 1))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]; congr 1; push_cast; ring
    have hpp : π ^ (-((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) * π ^ (-((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2)) *
        √π = (π ^ (2 * m + 2))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos, ← Real.rpow_add Real.pi_pos,
        ← Real.rpow_natCast, ← Real.rpow_neg Real.pi_pos.le]
      congr 1; push_cast; ring
    rw [hg1, hg2]
    have key : (tauR (2 * m + 1))⁻¹ * Gamma ((m : ℝ) + 1) *
        π ^ (-((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) *
        Gamma ((m : ℝ) + 1 + 1 / 2) * π ^ (-((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2)) =
        (tauR (2 * m + 1))⁻¹ * (Gamma ((m : ℝ) + 1) * Gamma ((m : ℝ) + 1 + 1 / 2)) *
        (π ^ (-((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) * π ^ (-((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2))) := by
      ring
    rw [key, hdup, hfac, h2p]
    have key2 : (tauR (2 * m + 1))⁻¹ * ((Nat.factorial (2 * m + 1) : ℝ) * ((2 : ℝ) ^ (2 * m + 1))⁻¹ * √π) *
        (π ^ (-((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) * π ^ (-((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2))) =
        (tauR (2 * m + 1))⁻¹ * ((Nat.factorial (2 * m + 1) : ℝ) * ((2 : ℝ) ^ (2 * m + 1))⁻¹) *
        (π ^ (-((((2 * m + 1 : ℕ) : ℝ) + 1) / 2)) * π ^ (-((((2 * m + 1 + 1 : ℕ) : ℝ) + 1) / 2)) * √π) := by
      ring
    rw [key2, hpp, ih, Finset.prod_range_succ,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega, mul_pow, show 2 * (m + 1) = 2 * m + 2 by ring]
    have : (0 : ℝ) < π := Real.pi_pos
    field_simp
    ring

/-- **Part 1 of the proof of Theorem 5.1, even $n = 2m$, $m\ge1$** (Hanke thesis, p. 18):
$\tau_{\mathbb R}(SO_{2m})^{-1} = 2^{2m}\prod_{j=1}^{m-1}\frac{(2j-1)!}{(2\pi)^{2j}}\cdot(m-1)!\,(2\pi)^{-m}$. -/
@[kb "hanke2005crelle" "proof of Theorem 5.1, Part 1, p. 18"]
theorem inv_tauR_even {m : ℕ} (hm : 1 ≤ m) :
    (tauR (2 * m))⁻¹ = (2 : ℝ) ^ (2 * m) *
      (∏ j ∈ range (m - 1), ((Nat.factorial (2 * (j + 1) - 1) : ℝ) / (2 * π) ^ (2 * (j + 1)))) *
      ((Nat.factorial (m - 1) : ℝ) * (2 * π) ^ (-(m : ℝ))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, tauR_succ_inv, inv_tauR_odd,
    Nat.add_sub_cancel]
  have hg : Gamma ((((2 * k + 1 : ℕ) : ℝ) + 1) / 2) = (Nat.factorial k : ℝ) := by
    rw [← Real.Gamma_nat_eq_factorial]; congr 1; push_cast; ring
  have hp : π ^ (-((((2 * k + 1 : ℕ) : ℝ) + 1) / 2)) = (π ^ (k + 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg Real.pi_pos.le]; congr 1; push_cast; ring
  have h2π : (2 * π) ^ (-((k + 1 : ℕ) : ℝ)) = ((2 * π) ^ (k + 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
  rw [hg, hp, h2π, mul_pow, show 2 * k + 1 + 1 = (k + 1) + (k + 1) by ring, pow_add]
  have : (0 : ℝ) < π := Real.pi_pos
  field_simp
  ring

end QuadFormsKB.Hanke2005
