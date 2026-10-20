/-
# Theta series on $\Gamma_0(N)$: characteristics, cusps, quadratic Gauss sums

For a real symmetric positive definite matrix $S$ with $\vec{x}^{\mathsf T}S\vec{x} \in \mathbb{Z}$ for all
$\vec{x} \in \mathbb{Z}^n$ (for an integral form $Q$ this is the Gram matrix $A = H/2$), write
$S[\vec{x}] = \vec{x}^{\mathsf T}S\vec{x}$, $S^* = \tfrac14 S^{-1}$ and $e(t) = e^{2\pi i t}$.

* `thetaChar S h z` $= \sum_{\vec{x} \in \mathbb{Z}^n} e\big(z\, S[\vec{x} + \vec{h}]\big)$, the theta series with characteristic
  $\vec{h} \in \mathbb{R}^n$, and its inversion law `thetaChar_S`
  $$\vartheta_{S,\vec{h}}(-1/z) = (\det S)^{-1/2}\Big(\frac{-iz}{2}\Big)^{n/2}
    \sum_{\vec{y} \in \mathbb{Z}^n} e\big(z\,S^*[\vec{y}]\big)\, e(\vec{y}\cdot\vec{h}).$$
* `gaussSum S a c m` $= G_S(a, \vec{m}, c) = \sum_{\vec{r} \in (\mathbb{Z}/c)^n} e\Big(\frac{a\,S[\vec{r}] + \vec{m}\cdot\vec{r}}{c}\Big)$,
  the $n$-ary quadratic Gauss sum with a linear term.
* `thetaGram_cusp`: the expansion of $\Theta_S$ at the cusp $a/c$: for $c \ge 1$, $a \in \mathbb{Z}$, $\operatorname{Im} w > 0$,
  $$\Theta_S\Big(\frac{a}{c} - \frac{1}{cw}\Big) = (\det S)^{-1/2}\Big(\frac{-iw}{2c}\Big)^{n/2}
    \sum_{\vec{m} \in \mathbb{Z}^n} G_S(a, \vec{m}, c)\, e\Big(\frac{w}{c}\, S^*[\vec{m}]\Big).$$

For an integral positive definite form $Q$ in $n = 2k$ variables with level $N$ (`IsThetaLevel`), Hessian $H$, Gram
matrix $A = H/2$ and $\Delta_Q = (-1)^k\det H$ (`thetaDisc`):

* `theta_gamma0`: for $\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$, $c \ge 1$, $N \mid c$:
  $\Theta_Q(\gamma z) = M_A(a, c)(cz+d)^k\Theta_Q(z)$, $M_A(a,c) = (\tfrac{-i}{2c})^k(\det A)^{-1/2}G_A(a, \vec 0, c)$ (`thetaMult`).
* `thetaMult_reciprocity`: $M_A(a, Nc_0) = a^{-k}\,G_{NA^*}(-c_0, \vec 0, a)$.
* `gaussSum_prime` (via `sum_addChar_quadForm`): Gauss sums modulo a good odd prime are $\left(\frac{(-1)^k\det H}{p}\right)p^k$.
* `thetaMult_eq_jacobiSym`, `thetaMult_eq_thetaChi`: $M_A(a, c) = (\Delta_Q/a) = \chi_Q(d)$ (Dirichlet's theorem).
* `theta_gamma0_chi`, `theta_gamma0_quaternary`: $\Theta_Q(\gamma z) = \chi_Q(d)(cz+d)^k\Theta_Q(z)$ on $\Gamma_0(N)$.
* `isBoundedAtImInfty_thetaH_slash`, `thetaMFGamma1`, `thetaMFGamma0`: $\Theta_Q \in M_k(\Gamma_1(N))$; in $M_k(\Gamma_0(N))$ for
  trivial $\chi_Q$; `thetaMF_sumSq_four`: $\Theta_{I_4} \in M_2(\Gamma_0(4))$.

Sources: Iwaniec, *Topics in Classical Automorphic Forms*, §10.3–10.4 [unverified]; Miyake, *Modular Forms*,
§4.9 [unverified]; Schoeneberg, *Elliptic Modular Functions*, Ch. IX [unverified].
-/
import QuadFormsKB.Siegel.ThetaModular
import QuadFormsKB.Siegel.QuadGaussSum

open Complex Matrix Filter Topology
open QuadFormsKB.Analysis (quadAt quadAtR)
open ModularForm
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-! ### Theta series with characteristics -/

/-- **Theta series with characteristic** $\vec{h} \in \mathbb{R}^n$ of a real matrix $S$:
$$\vartheta_{S,\vec{h}}(z) = \sum_{\vec{x} \in \mathbb{Z}^n} e\big(z\,(\vec{x}+\vec{h})^{\mathsf T} S (\vec{x}+\vec{h})\big),$$
$e(t) = e^{2\pi i t}$ (a `tsum`; absolutely convergent for $S$ positive definite and $\operatorname{Im} z > 0$). For
$\vec{h} = \vec{\mu}$ in the dual lattice of an integral form this is $\theta_{L+\vec{\mu}}$. -/
def thetaChar (S : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (z : ℂ) : ℂ :=
  ∑' x : Fin n → ℤ, cexp (2 * Real.pi * I * z * (quadAtR S (fun i => (x i : ℝ) + h i) : ℂ))

/-- **Inversion law for theta series with characteristics.** For $S$ real positive definite, $\vec{h} \in \mathbb{R}^n$
and $\operatorname{Im} z > 0$,
$$\vartheta_{S,\vec{h}}(-1/z) = (\det S)^{-1/2}\Big(\frac{-iz}{2}\Big)^{n/2}
  \sum_{\vec{y} \in \mathbb{Z}^n} e\big(z\, \vec{y}^{\mathsf T} S^* \vec{y}\big)\, e(\vec{y}\cdot\vec{h}),
  \qquad S^* = \tfrac14 S^{-1},$$
with the principal branch of the power. *Proof:* `Analysis.tsum_gaussian_quadratic_shift` at $w = 2i/z$. -/
@[kb "serre1973" "Ch. VII §6.2, theta of a lattice [unverified]"]
theorem thetaChar_S {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef) (h : Fin n → ℝ) {z : ℂ}
    (hz : 0 < z.im) :
    thetaChar S h (-1 / z) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * (-I * z / 2) ^ ((n : ℂ) / 2) *
        ∑' y : Fin n → ℤ, cexp (2 * Real.pi * I * z * (quadAt ((1 / 4 : ℝ) • S⁻¹) y : ℂ)) *
          cexp (2 * Real.pi * I * ((∑ i, (y i : ℝ) * h i : ℝ) : ℂ)) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  set w : ℂ := 2 * I / z with hw
  have hwre : 0 < w.re := by
    have : w = (2 / Complex.normSq z : ℝ) * (I * (starRingEnd ℂ) z) := by
      rw [hw, div_eq_mul_inv, Complex.inv_def]; push_cast; ring
    rw [this, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    simp only [mul_re, I_re, conj_re, zero_mul, I_im, conj_im, one_mul, zero_sub, neg_neg]
    positivity
  have hwinv : w⁻¹ = -I * z / 2 := by
    rw [hw]; field_simp; rw [I_sq]; ring
  have h1 := Analysis.tsum_gaussian_quadratic_shift hS hwre h
  rw [hwinv] at h1
  unfold thetaChar
  have hl : ∀ x : Fin n → ℤ,
      cexp (2 * Real.pi * I * (-1 / z) * (quadAtR S (fun i => (x i : ℝ) + h i) : ℂ)) =
      cexp (-Real.pi * w * (quadAtR S (fun i => (x i : ℝ) + h i) : ℂ)) := by
    intro x; congr 1; rw [hw]; field_simp
  have hr : ∀ y : Fin n → ℤ, cexp (-Real.pi * (-I * z / 2) * (quadAt S⁻¹ y : ℂ)) =
      cexp (2 * Real.pi * I * z * (quadAt ((1 / 4 : ℝ) • S⁻¹) y : ℂ)) := by
    intro y; congr 1
    simp only [quadAt, smul_mulVec, dotProduct_smul, smul_eq_mul]
    push_cast; ring
  simp_rw [hl, h1, hr]

/-! ### Quadratic Gauss sums -/

/-- The standard lift $\mathbb{Z}/c \to \{0, \dots, c-1\} \subset \mathbb{Z}$, coordinatewise. -/
def liftZ {c : ℕ} (r : Fin n → ZMod c) : Fin n → ℤ := fun i => ((r i).val : ℤ)

/-- **The $n$-ary quadratic Gauss sum with linear term:** for a real matrix $S$, $a \in \mathbb{Z}$, $c \ge 1$ and
$\vec{m} \in \mathbb{Z}^n$,
$$G_S(a, \vec{m}, c) = \sum_{\vec{r} \in \{0,\dots,c-1\}^n} e\Big(\frac{a\, \vec{r}^{\mathsf T} S \vec{r} + \vec{m}\cdot\vec{r}}{c}\Big),$$
the sum over $\vec{r} \in (\mathbb{Z}/c)^n$ through the standard lift (`liftZ`). When $\vec{x}^{\mathsf T}S\vec{x}$ is integral on
$\mathbb{Z}^n$ the summand depends only on $\vec{r} \bmod c$. $G_S(a, c) = G_S(a, \vec{0}, c)$ is the classical quadratic
Gauss sum $\sum_{\vec{r} \bmod c} e(a\,Q(\vec{r})/c)$ of $Q(\vec{x}) = \vec{x}^{\mathsf T}S\vec{x}$. -/
@[kb "iwaniec1997" "§10.4, quadratic Gauss sums [unverified]"]
def gaussSum (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) [NeZero c] (m : Fin n → ℤ) : ℂ :=
  ∑ r : Fin n → ZMod c, cexp (2 * Real.pi * I *
    (((a : ℂ) * (quadAt S (liftZ r) : ℂ) + ∑ i, (m i : ℂ) * (liftZ r i : ℂ)) / c))

/-- Splitting $\mathbb{Z}^n$ by residues mod $c$: $\vec{x} \leftrightarrow (\vec{x} \bmod c, \lfloor \vec{x}/c \rfloor)$, with
inverse $(\vec{r}, \vec{y}) \mapsto \operatorname{lift}(\vec{r}) + c\vec{y}$. -/
def splitEquiv (c : ℕ) [NeZero c] : (Fin n → ℤ) ≃ (Fin n → ZMod c) × (Fin n → ℤ) where
  toFun x := (fun i => (x i : ZMod c), fun i => x i / c)
  invFun p := fun i => liftZ p.1 i + c * p.2 i
  left_inv x := by
    funext i
    simp only [liftZ, ZMod.val_intCast]
    exact Int.emod_add_mul_ediv (x i) c
  right_inv p := by
    obtain ⟨r, y⟩ := p
    have hc : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [liftZ]
    · simp only [liftZ]
      rw [add_comm, Int.mul_add_ediv_left _ _ hc.ne', Int.ediv_eq_zero_of_lt (by positivity)
        (by exact_mod_cast ZMod.val_lt (r i)), add_zero]

/-- Polarization: for symmetric $S$, $S[\vec{u} + \vec{v}] = S[\vec{u}] + 2\,\vec{u}^{\mathsf T}S\vec{v} + S[\vec{v}]$. -/
lemma quadAtR_add {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S) (u v : Fin n → ℝ) :
    quadAtR S (u + v) = quadAtR S u + 2 * (u ⬝ᵥ S *ᵥ v) + quadAtR S v := by
  have : v ⬝ᵥ S *ᵥ u = u ⬝ᵥ S *ᵥ v := by
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hSt]
  simp only [quadAtR, mulVec_add, dotProduct_add, add_dotProduct, this]
  ring

lemma quadAtR_smul (S : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (v : Fin n → ℝ) :
    quadAtR S (t • v) = t ^ 2 * quadAtR S v := by
  simp only [quadAtR, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring

/-- If $S[\vec{x}] \in \mathbb{Z}$ on $\mathbb{Z}^n$ and $S$ is symmetric, then $2\,\vec{x}^{\mathsf T}S\vec{y} \in \mathbb{Z}$ on $\mathbb{Z}^n$. -/
lemma two_bil_int {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (x y : Fin n → ℤ) :
    ∃ q : ℤ, 2 * ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (y i : ℝ))) = q := by
  obtain ⟨q1, h1⟩ := hint (x + y)
  obtain ⟨q2, h2⟩ := hint x
  obtain ⟨q3, h3⟩ := hint y
  refine ⟨q1 - q2 - q3, ?_⟩
  have := quadAtR_add hSt (fun i => (x i : ℝ)) (fun i => (y i : ℝ))
  have e : (fun i => (x i : ℝ)) + (fun i => (y i : ℝ)) = fun i => ((x + y) i : ℝ) := by
    funext i; simp
  rw [e] at this
  push_cast
  change quadAtR S _ = _ at h1 h2 h3
  linarith

/-- $e(t + k) = e(t)$ for $k \in \mathbb{Z}$. -/
lemma cexp_add_int (t : ℂ) (k : ℤ) :
    cexp (2 * Real.pi * I * (t + k)) = cexp (2 * Real.pi * I * t) := by
  rw [mul_add, Complex.exp_add, show 2 * Real.pi * I * (k : ℂ) = k * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Expansion of $\Theta_S$ at the cusp $a/c$.** Let $S$ be real symmetric positive definite with
$S[\vec{x}] = \vec{x}^{\mathsf T}S\vec{x} \in \mathbb{Z}$ for all $\vec{x} \in \mathbb{Z}^n$, $a \in \mathbb{Z}$, $c \ge 1$, and
$\operatorname{Im} w > 0$. Then
$$\Theta_S\Big(\frac{a}{c} - \frac{1}{cw}\Big) = (\det S)^{-1/2}\Big(\frac{-iw}{2c}\Big)^{n/2}
  \sum_{\vec{m} \in \mathbb{Z}^n} G_S(a, \vec{m}, c)\, e\Big(\frac{w}{c}\, S^*[\vec{m}]\Big), \qquad S^* = \tfrac14 S^{-1},$$
with $G_S$ the Gauss sum `gaussSum` and the principal branch of the power. No relation between $a$ and $c$ is
needed. *Proof:* split $\vec{x} = \vec{r} + c\vec{y}$ by residues mod $c$; then
$e\big(\tfrac{a}{c}S[\vec{x}]\big) = e\big(\tfrac{a}{c}S[\vec{r}]\big)$ and the sum over $\vec{y}$ is the theta series with
characteristic $\vec{r}/c$ at $-c/w$, to which `thetaChar_S` applies. -/
@[kb "iwaniec1997" "§10.3, theta at a cusp [unverified]"]
theorem thetaGram_cusp {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (a : ℤ) (c : ℕ) [NeZero c] {w : ℂ}
    (hw : 0 < w.im) :
    thetaGram S (a / c - 1 / (c * w)) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * (-I * w / (2 * c)) ^ ((n : ℂ) / 2) *
        ∑' m : Fin n → ℤ, gaussSum S a c m *
          cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) := by
  have hSt : Sᵀ = S := by
    have := hS.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  set z : ℂ := a / c - 1 / (c * w) with hzdef
  set w' : ℂ := w / c with hw'
  have hwc : 0 < w'.im := by
    have : w'.im = w.im / c := by rw [hw']; simp
    rw [this]; positivity
  have hz : 0 < z.im := by
    have : z = a / c + ((c : ℝ)⁻¹ ^ 2 : ℝ) * (-1 / w') := by
      rw [hzdef, hw']; push_cast; field_simp; ring
    have h2 : 0 < (-1 / w').im := by
      have hw'0 : w' ≠ 0 := by rintro h; rw [h] at hwc; simp at hwc
      rw [div_eq_mul_inv, neg_one_mul, neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hwc (Complex.normSq_pos.mpr hw'0)
    rw [this, add_im, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    have : ((a : ℂ) / c).im = 0 := by
      rw [show (a : ℂ) / c = ((a / c : ℝ) : ℂ) by push_cast; ring, ofReal_im]
    rw [this, zero_add]
    positivity
  set F : (Fin n → ℤ) → ℂ := fun x => cexp (2 * Real.pi * I * z * (quadAt S x : ℂ)) with hF
  have hsum : Summable F := by
    have := summable_thetaGram_term hS hz
    exact this.of_norm
  -- Step 1: split `x = lift r + c y`.
  have hsplit : thetaGram S z = ∑ r : Fin n → ZMod c, ∑' y : Fin n → ℤ,
      F (fun i => liftZ r i + c * y i) := by
    have h1 : thetaGram S z = ∑' p : (Fin n → ZMod c) × (Fin n → ℤ), F ((splitEquiv c).symm p) := by
      rw [(splitEquiv c).symm.tsum_eq]; rfl
    have hs2 : Summable fun p : (Fin n → ZMod c) × (Fin n → ℤ) => F ((splitEquiv c).symm p) :=
      (splitEquiv c).symm.summable_iff.mpr hsum
    rw [h1, hs2.tsum_prod, tsum_fintype]
    rfl
  -- Step 2: each residue class is a theta series with characteristic.
  have hclass : ∀ r : Fin n → ZMod c, ∀ y : Fin n → ℤ, F (fun i => liftZ r i + c * y i) =
      cexp (2 * Real.pi * I * ((a : ℂ) * (quadAt S (liftZ r) : ℂ) / c)) *
        cexp (2 * Real.pi * I * (-1 / w') *
          (quadAtR S (fun i => (y i : ℝ) + (liftZ r i : ℝ) / c) : ℂ)) := by
    intro r y
    set u : Fin n → ℝ := fun i => (liftZ r i : ℝ) with hu
    set v : Fin n → ℝ := fun i => (y i : ℝ) with hv
    have e1 : quadAt S (fun i => liftZ r i + c * y i) = quadAtR S (u + (c : ℝ) • v) := by
      have hvec : (fun i => ((liftZ r i + c * y i : ℤ) : ℝ)) = u + (c : ℝ) • v := by
        funext i; simp [hu, hv]
      change quadAtR S (fun i => ((liftZ r i + c * y i : ℤ) : ℝ)) = _
      rw [hvec]
    have e2 : quadAtR S (u + (c : ℝ) • v) =
        quadAt S (liftZ r) + c * (2 * (u ⬝ᵥ S *ᵥ v)) + c ^ 2 * quadAtR S v := by
      rw [quadAtR_add hSt, quadAtR_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]; ring
    have e3 : (fun i => (y i : ℝ) + (liftZ r i : ℝ) / c) = (c : ℝ)⁻¹ • (u + (c : ℝ) • v) := by
      funext i; simp [hu, hv]; field_simp; ring
    have e4 : quadAtR S (fun i => (y i : ℝ) + (liftZ r i : ℝ) / c) =
        (c : ℝ)⁻¹ ^ 2 * quadAtR S (u + (c : ℝ) • v) := by rw [e3, quadAtR_smul]
    obtain ⟨k, hk⟩ := two_bil_int hSt hint (liftZ r) y
    obtain ⟨q, hq⟩ := hint y
    simp only [hF]
    rw [e1, e4, e2]
    rw [← Complex.exp_add]
    have hk' : ((u ⬝ᵥ S *ᵥ v : ℝ) : ℂ) = (k : ℂ) / 2 := by
      rw [eq_div_iff two_ne_zero]; exact_mod_cast (by rw [← hk]; ring : (u ⬝ᵥ S *ᵥ v) * 2 = (k : ℝ))
    have hq' : ((quadAtR S v : ℝ) : ℂ) = (q : ℂ) := by exact_mod_cast hq
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨a * k + a * c * q, ?_⟩
    push_cast
    rw [hk', hq', hzdef, hw']
    field_simp
    ring
  -- Step 3: invert each class.
  have hinv : ∀ r : Fin n → ZMod c, ∑' y : Fin n → ℤ, F (fun i => liftZ r i + c * y i) =
      cexp (2 * Real.pi * I * ((a : ℂ) * (quadAt S (liftZ r) : ℂ) / c)) *
        (((Real.sqrt S.det)⁻¹ : ℝ) * (-I * w' / 2) ^ ((n : ℂ) / 2) *
          ∑' m : Fin n → ℤ, cexp (2 * Real.pi * I * w' * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) *
            cexp (2 * Real.pi * I * ((∑ i, (m i : ℝ) * ((liftZ r i : ℝ) / c) : ℝ) : ℂ))) := by
    intro r
    simp_rw [hclass]
    rw [tsum_mul_left, ← thetaChar_S hS _ hwc]
    rfl
  rw [hsplit]
  simp_rw [hinv]
  -- Step 4: exchange the finite sum over residues with the sum over `m`.
  have hsm : ∀ r : Fin n → ZMod c, Summable fun m : Fin n → ℤ =>
      cexp (2 * Real.pi * I * ((a : ℂ) * (quadAt S (liftZ r) : ℂ) / c)) *
        (cexp (2 * Real.pi * I * w' * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) *
          cexp (2 * Real.pi * I * ((∑ i, (m i : ℝ) * ((liftZ r i : ℝ) / c) : ℝ) : ℂ))) := by
    intro r
    refine Summable.mul_left _ ?_
    have hP : ((1 / 4 : ℝ) • S⁻¹).PosDef := hS.inv.smul (by norm_num)
    refine Summable.of_norm_bounded (summable_thetaGram_term hP hwc) fun m => ?_
    rw [norm_mul]
    have : ‖cexp (2 * Real.pi * I * ((∑ i, (m i : ℝ) * ((liftZ r i : ℝ) / c) : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, mul_one]
  have hrw : ∀ r : Fin n → ZMod c,
      cexp (2 * Real.pi * I * ((a : ℂ) * (quadAt S (liftZ r) : ℂ) / c)) *
        (((Real.sqrt S.det)⁻¹ : ℝ) * (-I * w' / 2) ^ ((n : ℂ) / 2) *
          ∑' m : Fin n → ℤ, cexp (2 * Real.pi * I * w' * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) *
            cexp (2 * Real.pi * I * ((∑ i, (m i : ℝ) * ((liftZ r i : ℝ) / c) : ℝ) : ℂ))) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * (-I * w' / 2) ^ ((n : ℂ) / 2) *
        ∑' m : Fin n → ℤ, cexp (2 * Real.pi * I * ((a : ℂ) * (quadAt S (liftZ r) : ℂ) / c)) *
          (cexp (2 * Real.pi * I * w' * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) *
            cexp (2 * Real.pi * I * ((∑ i, (m i : ℝ) * ((liftZ r i : ℝ) / c) : ℝ) : ℂ))) := by
    intro r; rw [tsum_mul_left]; ring
  simp_rw [hrw]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun r _ => hsm r]
  rw [show -I * w / (2 * c) = -I * w' / 2 by rw [hw']; ring]
  congr 1
  congr 1; funext m
  rw [gaussSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show 2 * Real.pi * I * (w / c) = 2 * Real.pi * I * w' by rw [hw'], ← mul_assoc,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  have : ∑ i, 2 * (Real.pi : ℂ) * I * ((m i : ℂ) * ((liftZ r i : ℂ) / c)) =
      2 * Real.pi * I * ((∑ i, (m i : ℂ) * (liftZ r i : ℂ)) / c) := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.mul_sum, this]
  ring

/-! ### Gauss sums under a level: vanishing and completing the square -/

/-- The summand of `gaussSum` as a function on $\mathbb{Z}^n$:
$\vec{x} \mapsto e\big((a\,S[\vec{x}] + \vec{m}\cdot\vec{x})/c\big)$. -/
def gsTerm (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) (m x : Fin n → ℤ) : ℂ :=
  cexp (2 * Real.pi * I * (((a : ℂ) * (quadAt S x : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ)) / c))

lemma gaussSum_eq_sum_gsTerm (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) [NeZero c]
    (m : Fin n → ℤ) : gaussSum S a c m = ∑ r : Fin n → ZMod c, gsTerm S a c m (liftZ r) := rfl

/-- $S[\vec{x} + c\vec{y}] = S[\vec{x}] + c\,(2\vec{x}^{\mathsf T}S\vec{y}) + c^2 S[\vec{y}]$ on integer vectors. -/
lemma quadAt_add_mul {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S) (x y : Fin n → ℤ) (c : ℤ) :
    quadAt S (fun i => x i + c * y i) = quadAt S x +
      c * (2 * ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (y i : ℝ)))) + c ^ 2 * quadAt S y := by
  have hvec : (fun i => ((x i + c * y i : ℤ) : ℝ)) =
      (fun i => (x i : ℝ)) + (c : ℝ) • (fun i => (y i : ℝ)) := by
    funext i; simp
  change quadAtR S (fun i => ((x i + c * y i : ℤ) : ℝ)) = _
  rw [hvec, quadAtR_add hSt, quadAtR_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- **Periodicity mod $c$** of the Gauss-sum summand (for $S[\cdot]$ integral on $\mathbb{Z}^n$). -/
lemma gsTerm_add_mul {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (a : ℤ) {c : ℕ} (hc : c ≠ 0)
    (m x y : Fin n → ℤ) :
    gsTerm S a c m (fun i => x i + c * y i) = gsTerm S a c m x := by
  obtain ⟨k, hk⟩ := two_bil_int hSt hint x y
  obtain ⟨q, hq⟩ := hint y
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold gsTerm
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * k + a * c * q + ∑ i, m i * y i, ?_⟩
  rw [quadAt_add_mul hSt x y c]
  have hk' : ((((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (y i : ℝ))) : ℝ) : ℂ) = (k : ℂ) / 2 := by
    rw [eq_div_iff two_ne_zero]
    exact_mod_cast (by rw [← hk]; ring :
      ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (y i : ℝ))) * 2 = (k : ℝ))
  have hq' : ((quadAt S y : ℝ) : ℂ) = (q : ℂ) := by exact_mod_cast hq
  push_cast
  rw [hk', hq']
  simp only [mul_add, Finset.sum_add_distrib]
  field_simp
  have : ∑ i, (c : ℂ) * (m i : ℂ) * (y i : ℂ) = c * ∑ i, (m i : ℂ) * (y i : ℂ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

/-- Every $\vec{x} \in \mathbb{Z}^n$ is $\operatorname{lift}(\vec{x} \bmod c) + c\lfloor\vec{x}/c\rfloor$. -/
lemma liftZ_cast_add (c : ℕ) [NeZero c] (x : Fin n → ℤ) :
    x = fun i => liftZ (fun j => (x j : ZMod c)) i + c * (x i / c) :=
  ((splitEquiv c).left_inv x).symm

/-- **Shift invariance:** $\sum_{\vec{r} \bmod c} \Phi(\vec{r} + \vec{t}) = \sum_{\vec{r} \bmod c}\Phi(\vec{r})$ for the Gauss-sum summand
$\Phi$ and any $\vec{t} \in \mathbb{Z}^n$. -/
lemma gaussSum_shift {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (a : ℤ) (c : ℕ) [NeZero c]
    (m t : Fin n → ℤ) :
    ∑ r : Fin n → ZMod c, gsTerm S a c m (liftZ r + t) = gaussSum S a c m := by
  have h1 : ∀ r : Fin n → ZMod c, gsTerm S a c m (liftZ r + t) =
      gsTerm S a c m (liftZ (r + fun i => (t i : ZMod c))) := by
    intro r
    rw [liftZ_cast_add c (liftZ r + t), gsTerm_add_mul hSt hint a (NeZero.ne c)]
    congr 2
    funext i
    simp [liftZ]
  simp_rw [h1]
  rw [gaussSum_eq_sum_gsTerm]
  exact Fintype.sum_equiv (Equiv.addRight fun i => (t i : ZMod c)) _ _ (fun _ => rfl)

/-- An integer matrix $H$ with $H = 2S$ ("the Hessian"), when $S$ is symmetric and $S[\cdot]$ is integral on $\mathbb{Z}^n$. -/
lemma exists_int_hessian {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) :
    ∃ H : Matrix (Fin n) (Fin n) ℤ, ∀ i j, (H i j : ℝ) = 2 * S i j := by
  have h : ∀ i j, ∃ q : ℤ, (q : ℝ) = 2 * S i j := by
    intro i j
    obtain ⟨q, hq⟩ := two_bil_int hSt hint (Pi.single i 1) (Pi.single j 1)
    refine ⟨q, ?_⟩
    rw [← hq]
    have e1 : (fun k => ((Pi.single i (1 : ℤ) : Fin n → ℤ) k : ℝ)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i <;> simp [hk]
    have e2 : (fun k => ((Pi.single j (1 : ℤ) : Fin n → ℤ) k : ℝ)) = Pi.single j 1 := by
      funext k; by_cases hk : k = j <;> simp [hk]
    rw [e1, e2, mulVec_single_one, single_one_dotProduct]
    simp
  choose H hH using h
  exact ⟨Matrix.of H, fun i j => hH i j⟩

/-- $\sum_i (H\vec{u})_i x_i = 2\,\vec{x}^{\mathsf T}S\vec{u}$ when $H = 2S$. -/
lemma sum_hessian_mulVec {S : Matrix (Fin n) (Fin n) ℝ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : ∀ i j, (H i j : ℝ) = 2 * S i j) (u x : Fin n → ℤ) :
    (∑ i, ((H *ᵥ u) i : ℝ) * (x i : ℝ)) =
      2 * ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (u i : ℝ))) := by
  simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hH, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Completing the square in a Gauss sum.** Let $S$ be symmetric with $S[\cdot]$ integral on $\mathbb{Z}^n$,
$H = 2S$ integral, and $ad - bc = 1$ with $c \ge 1$. For $\vec{u} \in \mathbb{Z}^n$,
$$G_S(a, H\vec{u}, c) = e\Big(-\frac{a d^2\, S[\vec{u}]}{c}\Big)\, G_S(a, \vec{0}, c).$$
*Proof:* shift $\vec{r} \mapsto \vec{r} + d\vec{u}$; $a\,S[\vec{r} + d\vec{u}] = a\,S[\vec{r}] + (1 + bc)\,(H\vec{u})\cdot\vec{r} + ad^2 S[\vec{u}]$. -/
theorem gaussSum_hessian {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : ∀ i j, (H i j : ℝ) = 2 * S i j) {a b d : ℤ} {c : ℕ} [NeZero c]
    (hdet : a * d - b * c = 1) (u : Fin n → ℤ) :
    gaussSum S a c (H *ᵥ u) =
      cexp (2 * Real.pi * I * (-(a * d ^ 2 * (quadAt S u : ℂ)) / c)) * gaussSum S a c 0 := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [← gaussSum_shift hSt hint a c 0 (d • u), Finset.mul_sum, gaussSum_eq_sum_gsTerm]
  refine Finset.sum_congr rfl fun r _ => ?_
  set x := liftZ r
  have hxd : x + d • u = fun i => x i + d * u i := by funext i; simp
  rw [hxd]
  unfold gsTerm
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(b * ∑ i, (H *ᵥ u) i * x i), ?_⟩
  rw [quadAt_add_mul hSt x u d]
  have hB := sum_hessian_mulVec hH u x
  have hB' : ((((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (u i : ℝ))) : ℝ) : ℂ) =
      (∑ i, ((H *ᵥ u) i : ℂ) * (x i : ℂ)) / 2 := by
    rw [eq_div_iff two_ne_zero]
    exact_mod_cast (by rw [hB]; ring :
      ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => (u i : ℝ))) * 2 = ∑ i, ((H *ᵥ u) i : ℝ) * (x i : ℝ))
  have hdet' : (a : ℂ) * d = 1 + b * c := by
    have : ((a * d - b * c : ℤ) : ℂ) = 1 := by rw [hdet]; simp
    push_cast at this; linear_combination this
  push_cast
  rw [hB']
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
  linear_combination (norm := skip) (-(2 * Real.pi * I * (∑ i, ((H *ᵥ u) i : ℂ) * (x i : ℂ))) / c) * hdet'
  field_simp
  ring

/-- **Vanishing of Gauss sums off $H\mathbb{Z}^n$.** Let $S$ be real symmetric positive definite with $S[\cdot]$ integral on
$\mathbb{Z}^n$, and let $N \ge 1$ be a level: $N\, S^*[\vec{y}] \in \mathbb{Z}$ for all $\vec{y} \in \mathbb{Z}^n$,
$S^* = \tfrac14 S^{-1}$. If $N \mid c$ and $G_S(a, \vec{m}, c) \ne 0$, then $\vec{m} = 2S\vec{u}$ for some
$\vec{u} \in \mathbb{Z}^n$ (i.e. $\vec{m} \in H\mathbb{Z}^n$). *Proof:* for $\vec{s} \in \mathbb{Z}^n$ the shift
$\vec{t} = c\,(2S)^{-1}\vec{s} \in \mathbb{Z}^n$ multiplies the sum by $e\big(\vec{m}^{\mathsf T}(2S)^{-1}\vec{s}\big)$. -/
theorem exists_eq_hessian_of_gaussSum_ne_zero {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) {N : ℕ} (hN0 : 0 < N)
    (hlev : ∀ y : Fin n → ℤ, ∃ q : ℤ, (N : ℝ) * quadAt ((1 / 4 : ℝ) • S⁻¹) y = q)
    (a : ℤ) {c : ℕ} [NeZero c] (hNc : N ∣ c) (m : Fin n → ℤ) (hG : gaussSum S a c m ≠ 0) :
    ∃ u : Fin n → ℤ, ∀ i, (m i : ℝ) = 2 * (S *ᵥ fun j => (u j : ℝ)) i := by
  have hSt : Sᵀ = S := by
    have := hS.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdetS : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hSit : (S⁻¹)ᵀ = S⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSt]
  set S' : Matrix (Fin n) (Fin n) ℝ := (N : ℝ) • ((1 / 4 : ℝ) • S⁻¹) with hS'
  have hS't : S'ᵀ = S' := by rw [hS', transpose_smul, transpose_smul, hSit]
  have hquadS' : ∀ y, quadAt S' y = (N : ℝ) * quadAt ((1 / 4 : ℝ) • S⁻¹) y := by
    intro y; simp only [quadAt, hS', smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hintS' : ∀ y : Fin n → ℤ, ∃ q : ℤ, quadAt S' y = q := fun y => by
    rw [hquadS']; exact hlev y
  obtain ⟨K, hK⟩ := exists_int_hessian hS't hintS'
  obtain ⟨c0, hc0⟩ := hNc
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
  -- real form of `K s`
  have hKs : ∀ s : Fin n → ℤ, (fun i => ((K *ᵥ s) i : ℝ)) =
      ((N : ℝ) / 2) • (S⁻¹ *ᵥ fun i => (s i : ℝ)) := by
    intro s; funext i
    simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hK, hS', Pi.smul_apply,
      smul_eq_mul, Matrix.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hSKs : ∀ s : Fin n → ℤ, S *ᵥ (fun i => ((K *ᵥ s) i : ℝ)) = ((N : ℝ) / 2) • fun i => (s i : ℝ) := by
    intro s
    rw [hKs, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hdetS, one_mulVec]
  -- the shift
  have hshift : ∀ s x : Fin n → ℤ, gsTerm S a c m (x + fun i => c0 * (K *ᵥ s) i) =
      gsTerm S a c m x * cexp (2 * Real.pi * I * ((∑ i, (m i : ℂ) * ((K *ᵥ s) i : ℂ)) / N)) := by
    intro s x
    have hxt : x + (fun i => c0 * (K *ᵥ s) i) = fun i => x i + c0 * (K *ᵥ s) i := rfl
    rw [hxt]
    unfold gsTerm
    rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    obtain ⟨q, hq⟩ := hintS' s
    refine ⟨a * ∑ i, x i * s i + a * c0 * q, ?_⟩
    rw [quadAt_add_mul hSt x (K *ᵥ s) c0]
    have h2 : 2 * ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => ((K *ᵥ s) i : ℝ))) =
        N * ∑ i, (x i : ℝ) * (s i : ℝ) := by
      rw [hSKs, dotProduct_smul, smul_eq_mul, dotProduct]; ring
    have h3 : quadAt S (K *ᵥ s) = N * q := by
      rw [← hq]
      change (fun i => ((K *ᵥ s) i : ℝ)) ⬝ᵥ S *ᵥ (fun i => ((K *ᵥ s) i : ℝ)) = _
      rw [hSKs, dotProduct_smul, hKs, smul_dotProduct, smul_eq_mul, smul_eq_mul, hquadS']
      simp only [quadAt, smul_mulVec, dotProduct_smul, smul_eq_mul]
      rw [dotProduct_comm (S⁻¹ *ᵥ fun i => (s i : ℝ)) (fun i => (s i : ℝ))]
      ring
    have h2' : ((2 * ((fun i => (x i : ℝ)) ⬝ᵥ S *ᵥ (fun i => ((K *ᵥ s) i : ℝ))) : ℝ) : ℂ) =
        N * ∑ i, (x i : ℂ) * (s i : ℂ) := by rw [h2]; push_cast; rfl
    have h3' : ((quadAt S (K *ᵥ s) : ℝ) : ℂ) = N * q := by rw [h3]; push_cast; rfl
    have hcN : (c : ℂ) = N * c0 := by rw [hc0]; push_cast; rfl
    have hNc' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hc0n : c0 ≠ 0 := by rintro rfl; exact NeZero.ne c (by rw [hc0, mul_zero])
    have hc0' : (c0 : ℂ) ≠ 0 := by exact_mod_cast hc0n
    rw [h2, h3]
    rw [hcN]
    push_cast
    simp only [mul_add, Finset.sum_add_distrib]
    field_simp
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  -- the phase must be trivial
  have hphase : ∀ s : Fin n → ℤ,
      cexp (2 * Real.pi * I * ((∑ i, (m i : ℂ) * ((K *ᵥ s) i : ℂ)) / N)) = 1 := by
    intro s
    have h := gaussSum_shift hSt hint a c m (fun i => c0 * (K *ᵥ s) i)
    simp_rw [hshift] at h
    rw [← Finset.sum_mul, ← gaussSum_eq_sum_gsTerm] at h
    have : gaussSum S a c m * (cexp (2 * Real.pi * I * ((∑ i, (m i : ℂ) * ((K *ᵥ s) i : ℂ)) / N)) - 1)
        = 0 := by rw [mul_sub, h, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hG
    · exact sub_eq_zero.mp h0
  have hu : ∀ j, ∃ u : ℤ, (u : ℝ) = (1 / 2 : ℝ) * (S⁻¹ *ᵥ fun i => (m i : ℝ)) j := by
    intro j
    obtain ⟨u, hu⟩ := Complex.exp_eq_one_iff.mp (hphase (Pi.single j 1))
    refine ⟨u, ?_⟩
    have hNc' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have e : (u : ℂ) = (∑ i, (m i : ℂ) * ((K *ᵥ Pi.single j 1) i : ℂ)) / N := by
      have := hu; rw [show (u : ℂ) * (2 * Real.pi * I) = 2 * Real.pi * I * u by ring] at this
      exact (mul_left_cancel₀ hpi this).symm
    have e2 : (∑ i, (m i : ℂ) * ((K *ᵥ Pi.single j 1) i : ℂ)) / N =
        (((1 / 2 : ℝ) * (S⁻¹ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) := by
      have hcol : ∀ i, ((K *ᵥ Pi.single j 1) i : ℂ) = ((K i j : ℝ) : ℂ) := by
        intro i; rw [mulVec_single_one]; simp
      simp_rw [hcol, hK, hS']
      simp only [Matrix.smul_apply, smul_eq_mul, mulVec, dotProduct]
      push_cast
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : S⁻¹ i j = S⁻¹ j i := by
        conv_lhs => rw [← hSit]
        rfl
      rw [this]
      field_simp
      ring
    exact_mod_cast e.trans e2
  choose u hu using hu
  refine ⟨u, fun i => ?_⟩
  have hvec : (fun j => (u j : ℝ)) = (1 / 2 : ℝ) • (S⁻¹ *ᵥ fun i => (m i : ℝ)) := by
    funext j; rw [hu j]; rfl
  rw [hvec, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hdetS, one_mulVec]
  simp

/-- $(H\vec{u})$ as a real vector is $2S\vec{u}$. -/
lemma cast_hessian_mulVec {S : Matrix (Fin n) (Fin n) ℝ} {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : ∀ i j, (H i j : ℝ) = 2 * S i j) (u : Fin n → ℤ) :
    (fun i => ((H *ᵥ u) i : ℝ)) = (2 : ℝ) • (S *ᵥ fun j => (u j : ℝ)) := by
  funext i
  simp only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, hH, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- $S^*[H\vec{u}] = S[\vec{u}]$ for $S^* = \tfrac14 S^{-1}$ and $H = 2S$. -/
lemma quadAt_dual_hessian {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    {H : Matrix (Fin n) (Fin n) ℤ} (hH : ∀ i j, (H i j : ℝ) = 2 * S i j) (u : Fin n → ℤ) :
    quadAt ((1 / 4 : ℝ) • S⁻¹) (H *ᵥ u) = quadAt S u := by
  have hSt : Sᵀ = S := by
    have := hS.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdetS : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  change quadAtR _ (fun i => ((H *ᵥ u) i : ℝ)) = _
  rw [cast_hessian_mulVec hH]
  simp only [quadAtR, smul_mulVec, mulVec_smul, mulVec_mulVec, Matrix.smul_mul,
    nonsing_inv_mul _ hdetS, one_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring_nf
  exact dotProduct_comm _ _

/-- **Theta transformation under $\Gamma_0(N)$, with a Gauss-sum multiplier.** Let $S$ be real symmetric positive
definite with $S[\cdot]$ integral on $\mathbb{Z}^n$, and $N \ge 1$ a level ($N S^*[\cdot]$ integral). For
$\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ with $c \ge 1$, $N \mid c$, and $\operatorname{Im} z > 0$,
$$\Theta_S\Big(\frac{az+b}{cz+d}\Big) = (\det S)^{-1/2}\Big(\frac{-i(cz+d)}{2c}\Big)^{n/2} G_S(a, c)\, \Theta_S(z),
  \qquad G_S(a, c) = \sum_{\vec{r} \bmod c} e\Big(\frac{a\, S[\vec{r}]}{c}\Big),$$
principal branch. *Proof:* `thetaGram_cusp` at $w = cz + d$; only $\vec{m} = H\vec{u}$ contribute
(`exists_eq_hessian_of_gaussSum_ne_zero`), and for those
$G_S(a, H\vec{u}, c)\, e\big(\tfrac{w}{c}S[\vec{u}]\big) = G_S(a,c)\, e(z\,S[\vec{u}])$ (`gaussSum_hessian`, $ad - bc = 1$). -/
@[kb "iwaniec1997" "§10.4, Thm. 10.9 (proof) [unverified]"]
theorem thetaGram_gamma0 {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) {N : ℕ} (hN0 : 0 < N)
    (hlev : ∀ y : Fin n → ℤ, ∃ q : ℤ, (N : ℝ) * quadAt ((1 / 4 : ℝ) • S⁻¹) y = q)
    {a b d : ℤ} {c : ℕ} [NeZero c] (hNc : N ∣ c) (hdet : a * d - b * c = 1) {z : ℂ}
    (hz : 0 < z.im) :
    thetaGram S ((a * z + b) / (c * z + d)) =
      ((Real.sqrt S.det)⁻¹ : ℝ) * (-I * (c * z + d) / (2 * c)) ^ ((n : ℂ) / 2) *
        gaussSum S a c 0 * thetaGram S z := by
  have hSt : Sᵀ = S := by
    have := hS.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdetS : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  set w : ℂ := c * z + d with hwdef
  have hw : 0 < w.im := by
    rw [hwdef]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
    positivity
  have hw0 : w ≠ 0 := by rintro h; rw [h] at hw; simp at hw
  have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have hz' : (a * z + b) / (c * z + d) = a / c - 1 / (c * w) := by
    rw [← hwdef]; field_simp; linear_combination (-1 : ℂ) * hdet'
  rw [hz', thetaGram_cusp hS hint a c hw]
  obtain ⟨H, hH⟩ := exists_int_hessian hSt hint
  have hinj : Function.Injective fun u : Fin n → ℤ => H *ᵥ u := by
    intro u v huv
    have h1 := congrArg (fun m : Fin n → ℤ => fun i => ((m i : ℤ) : ℝ)) huv
    simp only at h1
    rw [cast_hessian_mulVec hH, cast_hessian_mulVec hH] at h1
    have h2 := congrArg (fun v => ((1 / 2 : ℝ) • S⁻¹) *ᵥ v) h1
    simp only [mulVec_smul, smul_mulVec, mulVec_mulVec, Matrix.smul_mul, nonsing_inv_mul _ hdetS,
      one_mulVec, smul_smul] at h2
    norm_num at h2
    funext i; exact_mod_cast congrFun h2 i
  set f : (Fin n → ℤ) → ℂ := fun m => gaussSum S a c m *
    cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ)) with hf
  have hsupp : Function.support f ⊆ Set.range fun u : Fin n → ℤ => H *ᵥ u := by
    intro m hm
    have hG : gaussSum S a c m ≠ 0 := by
      intro h0; apply hm; simp [hf, h0]
    obtain ⟨u, hu⟩ := exists_eq_hessian_of_gaussSum_ne_zero hS hint hN0 hlev a hNc m hG
    refine ⟨u, funext fun i => ?_⟩
    have := congrFun (cast_hessian_mulVec hH u) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact_mod_cast this.trans (hu i).symm
  rw [← hinj.tsum_eq hsupp]
  have hterm : ∀ u : Fin n → ℤ, f (H *ᵥ u) =
      gaussSum S a c 0 * cexp (2 * Real.pi * I * z * (quadAt S u : ℂ)) := by
    intro u
    rw [hf]
    simp only
    rw [gaussSum_hessian hSt hint hH hdet u, quadAt_dual_hessian hS hH u, mul_comm (cexp _) _,
      mul_assoc, ← Complex.exp_add]
    congr 1
    obtain ⟨q, hq⟩ := hint u
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-(b * d * q), ?_⟩
    rw [hq, hwdef]
    push_cast
    linear_combination (norm := skip) (-(2 * Real.pi * I * d * q) / c) * hdet'
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  unfold thetaGram
  ring

/-! ### Integral forms of even rank -/

/-- **The theta multiplier** for even rank $n = 2k$: for $c \ge 1$ and $a \in \mathbb{Z}$,
$$M_S(a, c) = \Big(\frac{-i}{2c}\Big)^{k} (\det S)^{-1/2}\, G_S(a, c), \qquad
  G_S(a, c) = \sum_{\vec{r} \bmod c} e\Big(\frac{a\,S[\vec{r}]}{c}\Big).$$
For $S = A = H/2$ the Gram matrix of $Q$ and $\gamma \in \Gamma_0(N)$ with $c > 0$,
$\Theta_Q(\gamma z) = M_A(a, c)\,(cz+d)^k\,\Theta_Q(z)$ (`theta_gamma0`); `thetaMult_eq_jacobiSym` evaluates it. -/
def thetaMult (S : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (a : ℤ) (c : ℕ) [NeZero c] : ℂ :=
  (-I / (2 * c)) ^ k * ((Real.sqrt S.det)⁻¹ : ℝ) * gaussSum S a c 0

/-- $Q(\vec{x}) = A[\vec{x}]$ is integral. -/
lemma quadAt_gramMatrix_int (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    ∃ q : ℤ, quadAt (gramMatrix Q) x = q := ⟨Q.eval x, quadAt_gramMatrix Q x⟩

/-- `IsThetaLevel` in the form used by `thetaGram_gamma0`. -/
lemma isThetaLevel_iff_gram (Q : QuadForm ℤ n) (N : ℕ) :
    IsThetaLevel Q N ↔
      ∀ y : Fin n → ℤ, ∃ q : ℤ, (N : ℝ) * quadAt ((1 / 4 : ℝ) • (gramMatrix Q)⁻¹) y = q := Iff.rfl

/-- **Theta transformation under $\Gamma_0(N)$ (even rank, Gauss-sum multiplier).** Let $Q$ be a positive definite
integral form in $n = 2k$ variables and $N \ge 1$ a level (`IsThetaLevel`). For
$\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ with $c \ge 1$, $N \mid c$, and $\operatorname{Im} z > 0$,
$$\Theta_Q\Big(\frac{az+b}{cz+d}\Big) = M(a, c)\,(cz+d)^k\,\Theta_Q(z),$$
with $M(a, c)$ = `thetaMult (gramMatrix Q) k a c` (an explicit normalized Gauss sum). -/
@[kb "hanke2004" "§4, p. 364 [unverified]"]
theorem theta_gamma0 {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {a b d : ℤ} {c : ℕ} [NeZero c] (hNc : N ∣ c)
    (hdet : a * d - b * c = 1) {z : ℂ} (hz : 0 < z.im) :
    theta Q ((a * z + b) / (c * z + d)) = thetaMult (gramMatrix Q) k a c * (c * z + d) ^ k * theta Q z := by
  rw [theta_eq_thetaGram, theta_eq_thetaGram,
    thetaGram_gamma0 (gramMatrix_posDef hQ) (quadAt_gramMatrix_int Q) hN0 hN hNc hdet hz,
    show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, cpow_natCast, thetaMult]
  rw [show -I * (c * z + d) / (2 * c) = (-I / (2 * c)) * (c * z + d) by ring, mul_pow]
  ring

/-! ### Boundedness at every cusp -/

/-- The Gauss-sum summand has absolute value $1$. -/
lemma norm_gsTerm (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) (m x : Fin n → ℤ) :
    ‖gsTerm S a c m x‖ = 1 := by
  unfold gsTerm
  have : ((a : ℂ) * (quadAt S x : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ)) / c =
      (((a * quadAt S x + ∑ i, (m i : ℝ) * (x i : ℝ)) / c : ℝ) : ℂ) := by push_cast; rfl
  rw [this, show 2 * (Real.pi : ℂ) * I * (((a * quadAt S x + ∑ i, (m i : ℝ) * (x i : ℝ)) / c : ℝ) : ℂ)
      = ((2 * Real.pi * ((a * quadAt S x + ∑ i, (m i : ℝ) * (x i : ℝ)) / c) : ℝ) : ℂ) * I by
        push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- $|G_S(a, \vec{m}, c)| \le c^n$. -/
lemma norm_gaussSum_le (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) [NeZero c] (m : Fin n → ℤ) :
    ‖gaussSum S a c m‖ ≤ (c : ℝ) ^ n := by
  rw [gaussSum_eq_sum_gsTerm]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_gsTerm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  push_cast; rfl

/-- $|e(z\,P[\vec{m}])| \le |e(i\,P[\vec{m}])|$ for $P$ positive definite and $\operatorname{Im} z \ge 1$. -/
lemma norm_cexp_quad_le {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) {z : ℂ} (hz : 1 ≤ z.im)
    (m : Fin n → ℤ) :
    ‖cexp (2 * Real.pi * I * z * (quadAt P m : ℂ))‖ ≤ ‖cexp (2 * Real.pi * I * I * (quadAt P m : ℂ))‖ := by
  rw [Complex.norm_exp, Complex.norm_exp, Real.exp_le_exp]
  have hq := quadAt_nonneg hP m
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
  have := mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.2 hz)) hq
  nlinarith

/-- **Uniform bound for $\Theta_S \mid_k \gamma$** ($n = 2k$, $c \ge 1$): for $\operatorname{Im}\tau \ge 1$,
$|\Theta_S(\gamma\tau)|\,|c\tau + d|^{-k} \le (\det S)^{-1/2}(2c)^{-k} c^n \sum_{\vec{m}} |e(i\,S^*[\vec{m}])|$. -/
theorem norm_thetaGram_slash_le {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosDef)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) {k : ℕ} (hn : n = 2 * k)
    {a b d : ℤ} {c : ℕ} [NeZero c] (hdet : a * d - b * c = 1) {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖thetaGram S ((a * τ + b) / (c * τ + d))‖ * ‖(c * τ + d : ℂ)‖⁻¹ ^ k ≤
      (Real.sqrt S.det)⁻¹ * (1 / (2 * c)) ^ k * ((c : ℝ) ^ n *
        ∑' m : Fin n → ℤ, ‖cexp (2 * Real.pi * I * I * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  set w : ℂ := c * τ + d with hwdef
  have hτ0 : 0 < τ.im := by linarith
  have hw : 0 < w.im := by
    rw [hwdef]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
    positivity
  have hw0 : w ≠ 0 := by rintro h; rw [h] at hw; simp at hw
  have hdet' : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  have hz' : (a * τ + b) / (c * τ + d) = a / c - 1 / (c * w) := by
    rw [← hwdef]; field_simp; linear_combination (-1 : ℂ) * hdet'
  have hP : ((1 / 4 : ℝ) • S⁻¹).PosDef := hS.inv.smul (by norm_num)
  have hwc : 1 ≤ (w / c).im := by
    have : (w / c).im = τ.im := by
      rw [hwdef, add_div, mul_div_cancel_left₀ _ hc0]
      simp [Complex.div_im]
    rw [this]; exact hτ
  have hsumI := (summable_thetaGram_term hP (z := I) (by simp))
  have hbound : ∀ m : Fin n → ℤ, ‖gaussSum S a c m *
      cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ ≤
      (c : ℝ) ^ n * ‖cexp (2 * Real.pi * I * I * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ := by
    intro m
    rw [norm_mul]
    exact mul_le_mul (norm_gaussSum_le S a c m) (norm_cexp_quad_le hP hwc m) (norm_nonneg _)
      (by positivity)
  have hsum2 : Summable fun m : Fin n → ℤ => ‖gaussSum S a c m *
      cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hsumI.mul_left _)
  rw [hz', thetaGram_cusp hS hint a c hw,
    show ((n : ℂ) / 2) = ((k : ℕ) : ℂ) by rw [hn]; push_cast; ring, cpow_natCast]
  rw [norm_mul, norm_mul, norm_pow]
  have hnorm1 : ‖(-I * w / (2 * c) : ℂ)‖ = ‖w‖ * (1 / (2 * c)) := by
    rw [norm_div, norm_mul, norm_neg, norm_I, one_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_natCast]
    field_simp
  rw [hnorm1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htsum : ‖∑' m : Fin n → ℤ, gaussSum S a c m *
      cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ ≤
      (c : ℝ) ^ n * ∑' m : Fin n → ℤ,
        ‖cexp (2 * Real.pi * I * I * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ := by
    refine (norm_tsum_le_tsum_norm hsum2).trans ?_
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum hbound hsum2 (hsumI.mul_left _)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  calc (Real.sqrt S.det)⁻¹ * (‖w‖ * (1 / (2 * c))) ^ k * ‖∑' m : Fin n → ℤ, gaussSum S a c m *
      cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ * ‖w‖⁻¹ ^ k
      = (Real.sqrt S.det)⁻¹ * (1 / (2 * c)) ^ k * ‖∑' m : Fin n → ℤ, gaussSum S a c m *
      cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • S⁻¹) m : ℂ))‖ := by
        rw [mul_pow, inv_pow]; field_simp
    _ ≤ _ := by gcongr

/-- $\Theta_Q(z + j) = \Theta_Q(z)$ for $j \in \mathbb{Z}$. -/
theorem theta_add_int (Q : QuadForm ℤ n) (z : ℂ) (j : ℤ) : theta Q (z + j) = theta Q z := by
  unfold theta
  congr 1; funext x
  rw [show 2 * Real.pi * I * (z + j) * (Q.eval x : ℂ) =
      2 * Real.pi * I * z * (Q.eval x : ℂ) + (j * Q.eval x : ℤ) * (2 * Real.pi * I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Uniform bound for $\Theta_Q \mid_k \gamma$, every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$** ($Q$ positive definite,
$n = 2k$): there is $M$ with $|\Theta_Q(\gamma\tau)|\,|c\tau+d|^{-k} \le M$ for $\operatorname{Im}\tau \ge 1$. -/
theorem exists_bound_theta_slash {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    {a b c d : ℤ} (hdet : a * d - b * c = 1) :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im →
      ‖theta Q ((a * τ + b) / (c * τ + d))‖ * ‖(c * τ + d : ℂ)‖⁻¹ ^ k ≤ M := by
  have hA := gramMatrix_posDef hQ
  have hint := quadAt_gramMatrix_int Q
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- `c < 0`: use `-γ`
    set c' : ℕ := (-c).toNat with hc'
    have hc'c : (c' : ℤ) = -c := by rw [hc']; omega
    have : NeZero c' := ⟨by omega⟩
    refine ⟨(Real.sqrt (gramMatrix Q).det)⁻¹ * (1 / (2 * c')) ^ k * ((c' : ℝ) ^ n *
      ∑' m : Fin n → ℤ, ‖cexp (2 * Real.pi * I * I * (quadAt ((1 / 4 : ℝ) • (gramMatrix Q)⁻¹) m : ℂ))‖), fun τ hτ => ?_⟩
    have hdet' : (-a) * (-d) - (-b) * (c' : ℤ) = 1 := by rw [hc'c]; linarith
    have h := norm_thetaGram_slash_le hA hint hn hdet' hτ
    have e1 : (((-a : ℤ) : ℂ) * τ + ((-b : ℤ) : ℂ)) / ((c' : ℂ) * τ + ((-d : ℤ) : ℂ)) =
        (a * τ + b) / (c * τ + d) := by
      have : (c' : ℂ) = -(c : ℂ) := by exact_mod_cast hc'c
      rw [this]; push_cast
      rw [show -(a : ℂ) * τ + -b = -(a * τ + b) by ring, show -(c : ℂ) * τ + -d = -(c * τ + d) by ring,
        neg_div_neg_eq]
    have e2 : ‖((c' : ℂ) * τ + ((-d : ℤ) : ℂ))‖ = ‖(c * τ + d : ℂ)‖ := by
      have : (c' : ℂ) = -(c : ℂ) := by exact_mod_cast hc'c
      rw [this]; push_cast
      rw [show -(c : ℂ) * τ + -d = -(c * τ + d) by ring, norm_neg]
    rw [e1, e2, ← theta_eq_thetaGram] at h
    exact h
  · -- `c = 0`: `γ = ±T^b`
    subst hc
    have had : a * d = 1 := by linarith
    have hd : d = 1 ∨ d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    refine ⟨∑' x : Fin n → ℤ, ‖cexp (2 * Real.pi * I * I * (Q.eval x : ℂ))‖, fun τ hτ => ?_⟩
    have ha : a = d := by rcases hd with rfl | rfl <;> omega
    subst ha
    have hτ' : ((a : ℂ) * τ + b) / ((0 : ℤ) * τ + a) = τ + (a * b : ℤ) := by
      rcases hd with rfl | rfl <;> push_cast <;> field_simp <;> ring
    have hn1 : ‖((0 : ℤ) * τ + a : ℂ)‖ = 1 := by
      rcases hd with rfl | rfl <;> simp
    rw [hτ', theta_add_int, hn1, inv_one, one_pow, mul_one]
    exact norm_theta_le hQ hτ
  · set c' : ℕ := c.toNat with hc'
    have hc'c : (c' : ℤ) = c := by rw [hc']; omega
    have : NeZero c' := ⟨by omega⟩
    refine ⟨(Real.sqrt (gramMatrix Q).det)⁻¹ * (1 / (2 * c')) ^ k * ((c' : ℝ) ^ n *
      ∑' m : Fin n → ℤ, ‖cexp (2 * Real.pi * I * I * (quadAt ((1 / 4 : ℝ) • (gramMatrix Q)⁻¹) m : ℂ))‖), fun τ hτ => ?_⟩
    have hdet' : a * d - b * (c' : ℤ) = 1 := by rw [hc'c]; exact hdet
    have h := norm_thetaGram_slash_le hA hint hn hdet' hτ
    have : (c' : ℂ) = (c : ℂ) := by exact_mod_cast hc'c
    rw [this, ← theta_eq_thetaGram] at h
    exact h

/-- **$\Theta_Q$ is bounded at every cusp:** for $Q$ positive definite, $n = 2k$, and every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$, $\Theta_Q \mid_k \gamma$ is bounded as $\operatorname{Im}\tau \to \infty$. No level is needed. -/
@[kb "iwaniec1997" "§10.4 (theta at the cusps) [unverified]"]
theorem isBoundedAtImInfty_thetaH_slash {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    (γ : SL(2, ℤ)) : UpperHalfPlane.IsBoundedAtImInfty (thetaH Q ∣[(k : ℤ)] γ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  obtain ⟨M, hM⟩ := exists_bound_theta_slash hQ hn hdet
  refine ⟨M, 1, fun τ hτ => ?_⟩
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, thetaH,
    UpperHalfPlane.coe_specialLinearGroup_apply, norm_mul, norm_zpow, _root_.zpow_neg, zpow_natCast,
    ← inv_pow]
  simpa using hM τ hτ

/-! ### Reciprocity for the theta multiplier -/

/-- **Constant term of a theta-type series at $i\infty$.** For $P$ positive definite, $g$ bounded on $\mathbb{Z}^n$ and
$W(t)$ with $\operatorname{Im} W(t) \to \infty$:
$\sum_{\vec{m}} g(\vec{m})\, e\big(W(t)\,P[\vec{m}]\big) \to g(\vec{0})$ (dominated convergence). -/
lemma tendsto_tsum_cexp_quad {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (g : (Fin n → ℤ) → ℂ) {B : ℝ} (hg : ∀ m, ‖g m‖ ≤ B) {W : ℝ → ℂ}
    (hW : Tendsto (fun t => (W t).im) atTop atTop) :
    Tendsto (fun t => ∑' m : Fin n → ℤ, g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ)))
      atTop (𝓝 (g 0)) := by
  have hsumI := (summable_thetaGram_term hP (z := I) (by simp))
  have hlim : ∀ m : Fin n → ℤ, Tendsto (fun t => g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ)))
      atTop (𝓝 (if m = 0 then g 0 else 0)) := by
    intro m
    by_cases hm : m = 0
    · subst hm
      have : quadAt P (0 : Fin n → ℤ) = 0 := by simp [quadAt]
      simp [this]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hm)]
      have hpos : 0 < quadAt P m := by
        have hv : (fun i => (m i : ℝ)) ≠ 0 := by
          intro h; apply hm; funext i; have := congrFun h i; simpa using this
        simpa using hP.dotProduct_mulVec_pos hv
      rw [show (0 : ℂ) = g m * 0 by ring]
      refine Tendsto.const_mul _ ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ t, ‖cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ))‖ =
          Real.exp (-(2 * Real.pi * quadAt P m) * (W t).im) := by
        intro t; rw [Complex.norm_exp]; congr 1; simp [mul_re, mul_im]; ring
      simp_rw [hnorm]
      exact Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by have := Real.pi_pos; nlinarith) hW)
  have hbound : ∀ᶠ t in atTop, ∀ m : Fin n → ℤ,
      ‖g m * cexp (2 * Real.pi * I * W t * (quadAt P m : ℂ))‖ ≤
        B * ‖cexp (2 * Real.pi * I * I * (quadAt P m : ℂ))‖ := by
    filter_upwards [hW.eventually_ge_atTop 1] with t ht m
    rw [norm_mul]
    exact mul_le_mul (hg m) (norm_cexp_quad_le hP ht m) (norm_nonneg _)
      ((norm_nonneg _).trans (hg 0))
  have h := tendsto_tsum_of_dominated_convergence (hsumI.mul_left B) hlim hbound
  rwa [tsum_ite_eq] at h

/-- **The dual form of level $N$:** $A' = N A^* = \tfrac{N}{4}A^{-1}$ (`dualGram` scaled by $N$), the Gram matrix of the
integral form $N Q^*$ when $N$ is a level. -/
def levelDualGram (Q : QuadForm ℤ n) (N : ℕ) : Matrix (Fin n) (Fin n) ℝ := (N : ℝ) • dualGram Q

lemma levelDualGram_posDef {Q : IntQF n} (hQ : Q.PosDef) {N : ℕ} (hN0 : 0 < N) :
    (levelDualGram Q N).PosDef :=
  ((gramMatrix_posDef hQ).inv.smul (by norm_num : (0 : ℝ) < 1 / 4)).smul (by exact_mod_cast hN0)

lemma levelDualGram_int {Q : QuadForm ℤ n} {N : ℕ} (hN : IsThetaLevel Q N) (y : Fin n → ℤ) :
    ∃ q : ℤ, quadAt (levelDualGram Q N) y = q := by
  obtain ⟨q, hq⟩ := hN y
  refine ⟨q, ?_⟩
  rw [← hq]
  simp only [quadAt, levelDualGram, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Reciprocity for the theta multiplier** ($n = 2k$, $N$ a level, $c = Nc_0 \ge 1$, $a \ge 1$):
$$M_A(a, c) = \Big(\frac{-i}{2c}\Big)^{k}(\det A)^{-1/2}\,G_A(a, c) = a^{-k}\, G_{A'}(-c_0, a),$$
where $A'$ = `levelDualGram Q N` is the Gram matrix of the integral form $NQ^*$. So the Gauss sum modulo $c$ (all of whose
prime factors may divide $N$) is traded for one modulo $a$. *Proof:* expand $\Theta_Q$ at the cusp $a/c$
(`thetaGram_cusp`), and alternatively apply the inversion $\Theta_A(-1/\tau) \propto \Theta_{A^*}(\tau)$ and expand $\Theta_{A'}$ at the cusp
$-c_0/a$; compare the constant terms as $w = it \to i\infty$ (`tendsto_tsum_cexp_quad`). -/
@[kb "iwaniec1997" "§10.4, reciprocity of Gauss sums [unverified]"]
theorem thetaMult_reciprocity {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) (a : ℕ) [NeZero a] {c c0 : ℕ} [NeZero c]
    (hc : c = N * c0) :
    thetaMult (gramMatrix Q) k a c = ((a : ℂ) ^ k)⁻¹ * gaussSum (levelDualGram Q N) (-c0) a 0 := by
  set A := gramMatrix Q with hAdef
  have hA : A.PosDef := gramMatrix_posDef hQ
  set A' := levelDualGram Q N with hA'def
  have hA' : A'.PosDef := levelDualGram_posDef hQ hN0
  have hP : ((1 / 4 : ℝ) • A⁻¹).PosDef := hA.inv.smul (by norm_num)
  have hP' : ((1 / 4 : ℝ) • A'⁻¹).PosDef := hA'.inv.smul (by norm_num)
  have hnk : ((n : ℂ) / 2) = ((k : ℕ) : ℂ) := by rw [hn]; push_cast; ring
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne a
  have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  -- the two expansions agree for every `w = i t`, `t > 0`
  set L : ℂ → ℂ := fun w => ∑' m : Fin n → ℤ, gaussSum A a c m *
    cexp (2 * Real.pi * I * (w / c) * (quadAt ((1 / 4 : ℝ) • A⁻¹) m : ℂ)) with hL
  set W' : ℂ → ℂ := fun w => N * (a * w - 1) / c with hW'
  set R : ℂ → ℂ := fun w => ∑' m : Fin n → ℤ, gaussSum A' (-c0) a m *
    cexp (2 * Real.pi * I * (W' w / a) * (quadAt ((1 / 4 : ℝ) • A'⁻¹) m : ℂ)) with hR
  have key : ∀ t : ℝ, 0 < t → (-I / (2 * c)) ^ k * L (I * t) =
      ((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k * R (I * t) := by
    intro t ht
    set w : ℂ := I * t with hwdef
    have hw : 0 < w.im := by simp [hwdef, ht]
    have hw0 : w ≠ 0 := by rintro h; rw [h] at hw; simp at hw
    have haw : a * w - 1 ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp [hwdef] at this
      rcases this with h1 | h1
      · exact (NeZero.ne a) (by exact_mod_cast h1)
      · exact ht.ne' h1
    have haw' : (-1 + w * a : ℂ) ≠ 0 := by intro h; apply haw; linear_combination h
    have hinv : (-1 + w * (a : ℂ))⁻¹ * (-1 + w * a) = 1 := inv_mul_cancel₀ haw'
    set z : ℂ := ((a : ℤ) : ℂ) / c - 1 / (c * w) with hzdef
    have hz0 : z ≠ 0 := by
      rw [hzdef, show ((a : ℤ) : ℂ) / c - 1 / (c * w) = (a * w - 1) / (c * w) by push_cast; field_simp]
      exact div_ne_zero haw (mul_ne_zero hc0' hw0)
    set τ : ℂ := -1 / z with hτdef
    have hτ : τ = -(c * w) / (a * w - 1) := by
      rw [hτdef, hzdef, show ((a : ℤ) : ℂ) / c - 1 / (c * w) = (a * w - 1) / (c * w) by
        push_cast; field_simp]
      field_simp
    have hτim : 0 < τ.im := by
      have hzim : 0 < z.im := by
        have : z = (a / c : ℂ) + ((c : ℝ)⁻¹ ^ 2 : ℝ) * (-1 / (w / c)) := by
          rw [hzdef]; push_cast; field_simp; ring
        have hwc : 0 < (w / c).im := by
          have : (w / c).im = w.im / c := by simp
          rw [this]; positivity
        have h2 : 0 < (-1 / (w / c)).im := by
          have hw'0 : w / c ≠ 0 := div_ne_zero hw0 hc0'
          rw [div_eq_mul_inv, neg_one_mul, neg_im, inv_im, neg_div, neg_neg]
          exact div_pos hwc (Complex.normSq_pos.mpr hw'0)
        rw [this, add_im, mul_im]
        simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
        have : ((a : ℂ) / c).im = 0 := by
          rw [show (a : ℂ) / c = ((a / c : ℝ) : ℂ) by push_cast; ring, ofReal_im]
        rw [this, zero_add]
        positivity
      rw [hτdef, div_eq_mul_inv, neg_one_mul, neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hzim (Complex.normSq_pos.mpr hz0)
    have hzτ : z = -1 / τ := by rw [hτdef]; field_simp
    -- expansion 1
    have e1 := thetaGram_cusp hA (quadAt_gramMatrix_int Q) a c hw
    -- expansion 2: inversion, rescaling, cusp `-c0/a`
    have e2 := thetaGram_S hA hτim
    rw [← hzτ] at e2
    have e3 : thetaGram ((1 / 4 : ℝ) • A⁻¹) τ = thetaGram A' (τ / N) := by
      rw [hA'def, levelDualGram, thetaGram_smul (N : ℝ) (dualGram Q)]
      show thetaGram (dualGram Q) τ = _
      congr 1; push_cast; field_simp
    have hW'im : 0 < (W' w).im := by
      rw [show W' w = ((N / c * a * t : ℝ) : ℂ) * I + ((-(N / c) : ℝ) : ℂ) by
        simp only [hW', hwdef]; push_cast; field_simp; ring]
      simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, add_zero]
      positivity
    have hτN : τ / N = ((-c0 : ℤ) : ℂ) / a - 1 / (a * W' w) := by
      rw [hτ, hW', hc]; push_cast
      field_simp
      ring_nf
      linear_combination (-(c0 : ℂ)) * hinv
    have e4 := thetaGram_cusp hA' (levelDualGram_int hN) (-c0) a hW'im
    rw [← hτN] at e4
    rw [e1, e3, e4, hnk, cpow_natCast, cpow_natCast, cpow_natCast] at e2
    -- cancel
    have hsA : ((Real.sqrt A.det)⁻¹ : ℝ) ≠ 0 := by
      have := hA.det_pos; positivity
    have hprod : (-I * τ / 2) * (-I * W' w / (2 * a)) = N * w / (4 * a) := by
      rw [hτ, hW']; field_simp; rw [I_sq]; ring_nf
      linear_combination 4 * hinv
    have e5 : (-I / (2 * c)) ^ k * w ^ k * L w =
        ((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k * w ^ k * R w := by
      have hsA' : (((Real.sqrt A.det)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsA
      have h' : (-I * w / (2 * c)) ^ k * L w = (-I * τ / 2) ^ k *
          (((Real.sqrt A'.det)⁻¹ : ℝ) * (-I * W' w / (2 * a)) ^ k * R w) := by
        apply mul_left_cancel₀ hsA'
        linear_combination e2
      calc (-I / (2 * c)) ^ k * w ^ k * L w = (-I * w / (2 * c)) ^ k * L w := by
            rw [← mul_pow]; ring_nf
        _ = ((Real.sqrt A'.det)⁻¹ : ℝ) * ((-I * τ / 2) * (-I * W' w / (2 * a))) ^ k * R w := by
            rw [h', mul_pow]; ring
        _ = _ := by rw [hprod, mul_div_right_comm, mul_pow]; ring
    have hwk : w ^ k ≠ 0 := pow_ne_zero _ hw0
    have := e5
    rw [show (-I / (2 * c)) ^ k * w ^ k * L w = w ^ k * ((-I / (2 * c)) ^ k * L w) by ring,
      show ((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k * w ^ k * R w =
        w ^ k * (((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k * R w) by ring] at this
    exact mul_left_cancel₀ hwk this
  -- limits as `t → ∞`
  have hlimL : Tendsto (fun t : ℝ => L (I * t)) atTop (𝓝 (gaussSum A a c 0)) := by
    have := tendsto_tsum_cexp_quad hP (gaussSum A a c) (norm_gaussSum_le A a c)
      (W := fun t : ℝ => I * t / c) (by
        have : (fun t : ℝ => (I * t / c : ℂ).im) = fun t : ℝ => t / (c : ℝ) := by funext t; simp
        rw [this]; exact Tendsto.atTop_div_const hcpos tendsto_id)
    simpa [hL] using this
  have hlimR : Tendsto (fun t : ℝ => R (I * t)) atTop (𝓝 (gaussSum A' (-c0) a 0)) := by
    have := tendsto_tsum_cexp_quad hP' (gaussSum A' (-c0) a) (norm_gaussSum_le A' (-c0) a)
      (W := fun t : ℝ => W' (I * t) / a) (by
        have : (fun t : ℝ => (W' (I * t) / a : ℂ).im) = fun t : ℝ => ((N : ℝ) / c) * t := by
          funext t; simp only [hW']
          rw [show (N : ℂ) * (a * (I * t) - 1) / c / a = ((N / c : ℝ) : ℂ) * (I * t - 1 / a) by
            push_cast; field_simp]
          simp
        rw [this]; exact Tendsto.const_mul_atTop (by positivity) tendsto_id)
    simpa [hR] using this
  have h1 := hlimL.const_mul ((-I / (2 * c)) ^ k)
  have h2 := hlimR.const_mul (((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k)
  have heq : (fun t : ℝ => (-I / (2 * c)) ^ k * L (I * t)) =ᶠ[atTop]
      fun t => ((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k * R (I * t) := by
    filter_upwards [eventually_gt_atTop 0] with t ht using key t ht
  have hlim := tendsto_nhds_unique (h1.congr' heq) h2
  -- `det A' = (N/4)^n / det A`
  have hdetA' : Real.sqrt A'.det = ((N : ℝ) / 4) ^ k / Real.sqrt A.det := by
    have hd : A'.det = ((N : ℝ) / 4) ^ n * (A.det)⁻¹ := by
      rw [hA'def, levelDualGram, dualGram, smul_smul, det_smul, det_nonsing_inv,
        Ring.inverse_eq_inv', Fintype.card_fin]
      ring
    rw [hd, show ((N : ℝ) / 4) ^ n = (((N : ℝ) / 4) ^ k) ^ 2 by rw [← pow_mul, hn, mul_comm],
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_inv]
    ring
  have hsqA : 0 < Real.sqrt A.det := Real.sqrt_pos.mpr hA.det_pos
  calc thetaMult A k a c = ((Real.sqrt A.det)⁻¹ : ℝ) * ((-I / (2 * c)) ^ k * gaussSum A a c 0) := by
        rw [thetaMult]; ring
    _ = ((Real.sqrt A.det)⁻¹ : ℝ) * (((Real.sqrt A'.det)⁻¹ : ℝ) * ((N : ℂ) / (4 * a)) ^ k *
          gaussSum A' (-c0) a 0) := by rw [hlim]
    _ = _ := by
        rw [hdetA']
        have hsq : (Real.sqrt A.det : ℂ) ≠ 0 := by exact_mod_cast hsqA.ne'
        push_cast
        field_simp
        rw [div_pow, div_pow, mul_pow]
        field_simp

/-! ### Gauss sums modulo an odd prime not dividing the determinant -/

/-- **Gauss sums modulo a good odd prime.** Let $S$ be symmetric with $S[\cdot]$ integral on $\mathbb{Z}^n$, $H = 2S$ an
integer matrix, $n = 2k$, $p$ an odd prime with $p \nmid \det H$, and $p \nmid b$. Then
$$G_S(b, p) = \sum_{\vec{r} \bmod p} e\Big(\frac{b\,S[\vec{r}]}{p}\Big) = \Big(\frac{(-1)^k\det H}{p}\Big)\, p^k$$
(Legendre symbol). *Proof:* reduce mod $p$ and apply `sum_addChar_quadForm` to $M = \tfrac12 H \bmod p$. -/
@[kb "iwaniec1997" "§10.4, Gauss sums at good primes [unverified]"]
theorem gaussSum_prime {S : Matrix (Fin n) (Fin n) ℝ} (hSt : Sᵀ = S)
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) {H : Matrix (Fin n) (Fin n) ℤ}
    (hH : ∀ i j, (H i j : ℝ) = 2 * S i j) {k : ℕ} (hn : n = 2 * k) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpH : ¬ (p : ℤ) ∣ H.det) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    gaussSum S b p 0 = (legendreSym p ((-1) ^ k * H.det) : ℂ) * (p : ℂ) ^ k := by
  have hK : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hK
  set Hp : Matrix (Fin n) (Fin n) (ZMod p) := H.map (Int.cast : ℤ → ZMod p) with hHp
  set M : Matrix (Fin n) (Fin n) (ZMod p) := (2 : ZMod p)⁻¹ • Hp with hMdef
  have hHt : Hᵀ = H := by
    ext i j
    have h1 := hH i j; have h2' := hH j i
    have : S j i = S i j := by rw [← Matrix.transpose_apply S i j, hSt]
    exact_mod_cast (show (H j i : ℝ) = H i j by rw [h1, h2', this])
  have hMt : Mᵀ = M := by rw [hMdef, transpose_smul, hHp, ← transpose_map, hHt]
  have hdetHp : Hp.det = (H.det : ZMod p) := by
    rw [hHp]; exact (RingHom.map_det (Int.castRingHom (ZMod p)) H).symm
  have hdetH0 : (H.det : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hdetM : M.det = ((2 : ZMod p)⁻¹ ^ k) ^ 2 * (H.det : ZMod p) := by
    rw [hMdef, det_smul, Fintype.card_fin, hdetHp, ← pow_mul, mul_comm k 2, ← hn]
  have hdetM0 : M.det ≠ 0 := by
    rw [hdetM]; exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero h2))) hdetH0
  have hb0 : (b : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  -- each summand is `ψ(b · r^T M r)`
  have hterm : ∀ r : Fin n → ZMod p,
      cexp (2 * Real.pi * I * (((b : ℂ) * (quadAt S (liftZ r) : ℂ) +
        ∑ i, ((0 : Fin n → ℤ) i : ℂ) * (liftZ r i : ℂ)) / p)) =
      ZMod.stdAddChar ((b : ZMod p) * (r ⬝ᵥ M *ᵥ r)) := by
    intro r
    obtain ⟨q, hq⟩ := hint (liftZ r)
    have h2q : 2 * q = liftZ r ⬝ᵥ H *ᵥ liftZ r := by
      have : ((2 * q : ℤ) : ℝ) = ((liftZ r ⬝ᵥ H *ᵥ liftZ r : ℤ) : ℝ) := by
        rw [Int.cast_mul, ← hq]
        simp only [quadAt, dotProduct, mulVec, Int.cast_sum, Int.cast_mul, hH, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      exact_mod_cast this
    have hcast : (fun i => ((liftZ r i : ℤ) : ZMod p)) = r := by
      funext i; simp [liftZ]
    have hqp : (q : ZMod p) = r ⬝ᵥ M *ᵥ r := by
      have : (2 : ZMod p) * q = r ⬝ᵥ Hp *ᵥ r := by
        have := congrArg (Int.cast : ℤ → ZMod p) h2q
        push_cast at this
        rw [this]
        conv_rhs => rw [← hcast]
        simp only [dotProduct, mulVec, hHp, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
      rw [hMdef, smul_mulVec, dotProduct_smul, smul_eq_mul, ← this, ← mul_assoc,
        inv_mul_cancel₀ h2, one_mul]
    rw [show ((b : ZMod p) * (r ⬝ᵥ M *ᵥ r)) = ((b * q : ℤ) : ZMod p) by push_cast; rw [hqp],
      ZMod.stdAddChar_coe, hq]
    congr 1
    simp
    ring
  rw [gaussSum]
  simp_rw [hterm]
  rw [sum_addChar_quadForm hK (ZMod.isPrimitive_stdAddChar p) hn M hMt hdetM0 hb0, ZMod.card,
    hdetM]
  have hsq : ((2 : ZMod p)⁻¹ ^ k) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero h2))
  rw [show ((-1) ^ k * (((2 : ZMod p)⁻¹ ^ k) ^ 2 * (H.det : ZMod p))) =
      ((2 : ZMod p)⁻¹ ^ k) ^ 2 * (((-1) ^ k * H.det : ℤ) : ZMod p) by push_cast; ring, map_mul]
  simp only [quadCharC, MulChar.ringHomComp_apply, quadraticChar_sq_one' (pow_ne_zero _ (inv_ne_zero h2)),
    legendreSym]
  push_cast
  simp only [map_one, one_mul, eq_intCast]

/-! ### Evaluation of the multiplier: the character $\chi_Q$ -/

/-- $G_S(a, \vec{m}, c)$ depends only on $a \bmod c$ (for $S[\cdot]$ integral). -/
lemma gaussSum_add_mul {S : Matrix (Fin n) (Fin n) ℝ}
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (a j : ℤ) (c : ℕ) [NeZero c]
    (m : Fin n → ℤ) : gaussSum S (a + j * c) c m = gaussSum S a c m := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  refine Finset.sum_congr rfl fun r _ => ?_
  obtain ⟨q, hq⟩ := hint (liftZ r)
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨j * q, ?_⟩
  rw [hq]; push_cast; field_simp; ring

lemma thetaMult_add_mul {S : Matrix (Fin n) (Fin n) ℝ}
    (hint : ∀ x : Fin n → ℤ, ∃ q : ℤ, quadAt S x = q) (k : ℕ) (a j : ℤ) (c : ℕ) [NeZero c] :
    thetaMult S k (a + j * c) c = thetaMult S k a c := by
  rw [thetaMult, thetaMult, gaussSum_add_mul hint]

/-- The real matrix $H$ (Hessian of $Q$) is $2A$. -/
lemma hessian_cast_eq (Q : QuadForm ℤ n) (i j : Fin n) :
    ((Q.hessian i j : ℤ) : ℝ) = 2 * gramMatrix Q i j := by
  simp [gramMatrix, Matrix.smul_apply]

/-- $\det H' \cdot \det H = N^n$ for the Hessian $H'$ of $NQ^*$ (any integer matrix with $H' = 2A'$). -/
lemma det_levelDual_mul_det {Q : IntQF n} (hQ : Q.PosDef) {N : ℕ}
    {H' : Matrix (Fin n) (Fin n) ℤ} (hH' : ∀ i j, (H' i j : ℝ) = 2 * levelDualGram Q N i j) :
    H'.det * Q.hessian.det = (N : ℤ) ^ n := by
  have hA := gramMatrix_posDef hQ
  have hdetA : IsUnit (gramMatrix Q).det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hr1 : H'.map (Int.cast : ℤ → ℝ) = (2 * (N : ℝ) / 4) • (gramMatrix Q)⁻¹ := by
    ext i j; simp only [Matrix.map_apply, hH', levelDualGram, dualGram, Matrix.smul_apply, smul_eq_mul]
    ring
  have hr2 : Q.hessian.map (Int.cast : ℤ → ℝ) = (2 : ℝ) • gramMatrix Q := by
    ext i j; simp [hessian_cast_eq, Matrix.smul_apply]
  have hprod : H'.map (Int.cast : ℤ → ℝ) * Q.hessian.map (Int.cast : ℤ → ℝ) = (N : ℝ) • 1 := by
    rw [hr1, hr2, smul_mul_smul_comm, nonsing_inv_mul _ hdetA]
    congr 1; ring
  have := congrArg Matrix.det hprod
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_fin] at this
  have e1 : (H'.map (Int.cast : ℤ → ℝ)).det = (H'.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) H').symm
  have e2 : (Q.hessian.map (Int.cast : ℤ → ℝ)).det = (Q.hessian.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) Q.hessian).symm
  rw [e1, e2] at this
  exact_mod_cast this

/-- **The multiplier at a good prime.** For $Q$ positive definite, $n = 2k$, $N$ a level, $c = Nc_0 \ge 1$ and $p$ an odd
prime with $p \nmid N$, $p \nmid c_0$:
$$M_A(p, c) = \Big(\frac{(-1)^k \det H}{p}\Big)$$
(Legendre symbol). *Proof:* `thetaMult_reciprocity`, then `gaussSum_prime` for $NQ^*$, whose Hessian $H'$ has
$\det H' \det H = N^n$. -/
theorem thetaMult_prime {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hpN : ¬ p ∣ N) {c c0 : ℕ} [NeZero c] (hc : c = N * c0) (hpc0 : ¬ p ∣ c0) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    thetaMult (gramMatrix Q) k p c = (legendreSym p ((-1) ^ k * Q.hessian.det) : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [thetaMult_reciprocity hQ hn hN0 hN p hc]
  have hA' := levelDualGram_posDef hQ hN0
  have hSt' : (levelDualGram Q N)ᵀ = levelDualGram Q N := by
    have := hA'.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨H', hH'⟩ := exists_int_hessian hSt' (levelDualGram_int hN)
  have hdet := det_levelDual_mul_det hQ hH'
  have hpN' : ¬ (p : ℤ) ∣ N := by exact_mod_cast hpN
  have hpH' : ¬ (p : ℤ) ∣ H'.det := by
    intro h; apply hpN'
    exact Int.Prime.dvd_pow' hp.out (hdet ▸ dvd_mul_of_dvd_left h _)
  have hpH : ¬ (p : ℤ) ∣ Q.hessian.det := by
    intro h; apply hpN'
    exact Int.Prime.dvd_pow' hp.out (hdet ▸ dvd_mul_of_dvd_right h _)
  have hb : ¬ (p : ℤ) ∣ -(c0 : ℤ) := by
    rw [Int.dvd_neg]; exact_mod_cast hpc0
  rw [gaussSum_prime hSt' (levelDualGram_int hN) hH' hn hp2 hpH' hb]
  have hpk : ((p : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [← mul_assoc, mul_comm _ (legendreSym p _ : ℂ), mul_assoc, inv_mul_cancel₀ hpk, mul_one]
  -- the two Legendre symbols agree: their product is `(N^k / p)^2 = 1`
  have hsq1 : ((-1 : ℤ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hprod : legendreSym p ((-1) ^ k * H'.det) * legendreSym p ((-1) ^ k * Q.hessian.det) = 1 := by
    rw [← legendreSym.mul]
    have : (-1) ^ k * H'.det * ((-1) ^ k * Q.hessian.det) = ((N : ℤ) ^ k) ^ 2 := by
      calc (-1) ^ k * H'.det * ((-1) ^ k * Q.hessian.det)
          = ((-1 : ℤ) ^ k) ^ 2 * (H'.det * Q.hessian.det) := by ring
        _ = (N : ℤ) ^ (2 * k) := by rw [hsq1, one_mul, hdet, hn]
        _ = ((N : ℤ) ^ k) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [this]
    exact legendreSym.sq_one' p (by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      intro h; exact hpN' (Int.Prime.dvd_pow' hp.out h))
  have hΔ0 : (((-1) ^ k * Q.hessian.det : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h; apply hpH
    have : Q.hessian.det = (-1) ^ k * ((-1) ^ k * Q.hessian.det) := by
      rw [← mul_assoc, ← pow_two, hsq1, one_mul]
    rw [this]; exact dvd_mul_of_dvd_right h _
  have hL2 := legendreSym.sq_one p hΔ0
  have : legendreSym p ((-1) ^ k * H'.det) = legendreSym p ((-1) ^ k * Q.hessian.det) := by
    calc legendreSym p ((-1) ^ k * H'.det)
        = legendreSym p ((-1) ^ k * H'.det) * legendreSym p ((-1) ^ k * Q.hessian.det) ^ 2 := by
          rw [hL2, mul_one]
      _ = legendreSym p ((-1) ^ k * Q.hessian.det) := by rw [pow_two, ← mul_assoc, hprod, one_mul]
  rw [this]

/-- **The discriminant** $\Delta_Q = (-1)^k \det H$ of an even-rank form ($n = 2k$, $H$ the Hessian). The character of
$\Theta_Q$ is $d \mapsto \left(\frac{\Delta_Q}{d}\right)$. For $n = 4$, $\Delta_Q = \det H$. -/
def thetaDisc (Q : QuadForm ℤ n) (k : ℕ) : ℤ := (-1) ^ k * Q.hessian.det

/-- $|\Delta_Q|$ divides $N^n$ for a level $N$. -/
lemma thetaDisc_dvd {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} {N : ℕ} (hN0 : 0 < N)
    (hN : IsThetaLevel Q N) : (thetaDisc Q k).natAbs ∣ N ^ n := by
  have hA' := levelDualGram_posDef hQ hN0
  have hSt' : (levelDualGram Q N)ᵀ = levelDualGram Q N := by
    have := hA'.1; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨H', hH'⟩ := exists_int_hessian hSt' (levelDualGram_int hN)
  have hdet := det_levelDual_mul_det hQ hH'
  rw [thetaDisc, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
  have : (Q.hessian.det).natAbs ∣ ((N : ℤ) ^ n).natAbs := by
    rw [← hdet, Int.natAbs_mul]; exact Dvd.intro_left _ rfl
  simpa [Int.natAbs_pow] using this

/-- $\Delta_Q \ne 0$. -/
lemma thetaDisc_ne_zero {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} {N : ℕ} (hN0 : 0 < N)
    (hN : IsThetaLevel Q N) : thetaDisc Q k ≠ 0 := by
  intro h
  have := thetaDisc_dvd hQ (k := k) hN0 hN
  rw [h, Int.natAbs_zero, zero_dvd_iff] at this
  exact (pow_ne_zero _ hN0.ne') this

/-- **The multiplier at an odd positive $a$.** For $Q$ positive definite, $n = 2k$, $N$ a level, $c = Nc_0 \ge 1$, and
$a \ge 1$ odd with $\gcd(a, c) = 1$:
$$M_A(a, c) = \Big(\frac{\Delta_Q}{a}\Big) \quad\text{(Jacobi symbol)}, \qquad \Delta_Q = (-1)^k \det H.$$
*Proof:* by reciprocity $M_A(a, c)$ depends only on $c_0 \bmod a$, so we may replace $c_0$ by $c_0' \equiv 0 \bmod 4|\Delta_Q|$; by
Dirichlet's theorem (Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod`) pick a large prime $p \equiv a \bmod Nc_0'$; then
$M_A(a, c) = M_A(p, Nc_0') = (\Delta_Q/p)$ (`thetaMult_prime`) $= (\Delta_Q/a)$ since $p \equiv a \bmod 4|\Delta_Q|$. -/
theorem thetaMult_eq_jacobiSym {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {a : ℕ} (ha : Odd a) {c c0 : ℕ} [NeZero c]
    (hc : c = N * c0) (hac : Nat.Coprime a c) :
    thetaMult (gramMatrix Q) k a c = (jacobiSym (thetaDisc Q k) a : ℂ) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have : NeZero a := ⟨ha0⟩
  have hc00 : c0 ≠ 0 := by rintro rfl; exact NeZero.ne c (by rw [hc, mul_zero])
  set Δ := thetaDisc Q k with hΔ
  have hΔ0 : Δ ≠ 0 := thetaDisc_ne_zero hQ hN0 hN
  set L : ℕ := 4 * Δ.natAbs with hL
  have hL0 : 0 < L := by rw [hL]; have := Int.natAbs_pos.mpr hΔ0; omega
  have : NeZero L := ⟨hL0.ne'⟩
  have haN : Nat.Coprime a N := Nat.Coprime.coprime_dvd_right ⟨c0, hc⟩ hac
  have haΔ : Nat.Coprime a Δ.natAbs :=
    Nat.Coprime.coprime_dvd_right (thetaDisc_dvd hQ hN0 hN) (Nat.Coprime.pow_right _ haN)
  have ha4 : Nat.Coprime a 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr ha)
  have haL : Nat.Coprime a L := Nat.Coprime.mul_right ha4 haΔ
  -- choose `j` with `L ∣ c0 + a j`
  obtain ⟨u, hu⟩ : IsUnit (a : ZMod L) := (ZMod.isUnit_iff_coprime a L).mpr haL
  set j : ℕ := ((-(c0 : ZMod L)) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)).val with hj
  set c0' : ℕ := c0 + a * j with hc0'
  have hLc0' : L ∣ c0' := by
    rw [← ZMod.natCast_eq_zero_iff, hc0']
    push_cast
    rw [hj, ZMod.natCast_zmod_val, ← hu]
    rw [show ((u : ZMod L)) * (-(c0 : ZMod L) * ((u⁻¹ : (ZMod L)ˣ) : ZMod L)) =
      -(c0 : ZMod L) * (((u⁻¹ : (ZMod L)ˣ) : ZMod L) * u) by ring, Units.inv_mul]
    ring
  set c' : ℕ := N * c0' with hc'
  have hc'0 : c' ≠ 0 := by rw [hc']; exact mul_ne_zero hN0.ne' (by omega)
  have : NeZero c' := ⟨hc'0⟩
  -- step 1: replace `c` by `c'`
  have h1 : thetaMult (gramMatrix Q) k a c = thetaMult (gramMatrix Q) k a c' := by
    rw [thetaMult_reciprocity hQ hn hN0 hN a hc, thetaMult_reciprocity hQ hn hN0 hN a hc']
    congr 1
    rw [show (-(c0' : ℤ)) = -(c0 : ℤ) + (-(j : ℤ)) * a by rw [hc0']; push_cast; ring]
    rw [gaussSum_add_mul (levelDualGram_int hN)]
  -- step 2: a prime `p ≡ a mod c'`
  have hac' : Nat.Coprime a c' := by
    rw [hc']
    refine Nat.Coprime.mul_right haN ?_
    rw [hc0', Nat.coprime_add_mul_left_right]
    exact Nat.Coprime.coprime_dvd_right ⟨N, by rw [hc, mul_comm]⟩ hac
  obtain ⟨p, hpgt, hpp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime a c').mpr hac') (N + L + a)
  have : Fact p.Prime := ⟨hpp⟩
  have hdvd : (c' : ℤ) ∣ (p : ℤ) - a := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (p : ℤ) c').mp (by exact_mod_cast hpa.symm)
    exact this
  obtain ⟨t, ht⟩ := hdvd
  have h2 : thetaMult (gramMatrix Q) k a c' = thetaMult (gramMatrix Q) k p c' := by
    rw [show ((p : ℕ) : ℤ) = (a : ℤ) + t * c' by linarith, thetaMult_add_mul (quadAt_gramMatrix_int Q)]
  -- step 3: evaluate at the prime
  have hp2 : p ≠ 2 := by omega
  have hpN : ¬ p ∣ N := fun h => by have := Nat.le_of_dvd hN0 h; omega
  have hpc' : Nat.Coprime p c' := by
    have : (p : ZMod c') = (a : ZMod c') := hpa
    have hu' := (ZMod.isUnit_iff_coprime a c').mpr hac'
    rw [← this] at hu'
    exact (ZMod.isUnit_iff_coprime p c').mp hu'
  have hpc0' : ¬ p ∣ c0' := by
    intro h
    have : p ∣ c' := by rw [hc']; exact Dvd.dvd.mul_left h _
    have := Nat.Coprime.eq_one_of_dvd hpc' this
    exact hpp.one_lt.ne' this
  have h3 := thetaMult_prime hQ hn hN0 hN hp2 hpN hc' hpc0'
  rw [h1, h2, h3, jacobiSym.legendreSym.to_jacobiSym]
  -- step 4: `p ≡ a mod 4|Δ|`
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  congr 1
  rw [jacobiSym.mod_right _ hpo, jacobiSym.mod_right _ ha]
  change jacobiSym Δ (p % (4 * Δ.natAbs)) = jacobiSym Δ (a % (4 * Δ.natAbs))
  congr 1
  have hLc' : (L : ℤ) ∣ c' := by
    rw [hc']; exact_mod_cast Dvd.dvd.mul_left hLc0' _
  have : (p : ℤ) % L = (a : ℤ) % L := by
    rw [show (p : ℤ) = a + t * c' by linarith]
    obtain ⟨s, hs⟩ := hLc'
    rw [hs, show (a : ℤ) + t * (L * s) = a + (t * s) * L by ring, Int.add_mul_emod_self_right]
  rw [← hL]
  exact_mod_cast this

/-- **Periodicity of the Jacobi symbol $(\Delta_Q/\cdot)$ modulo the level** on odd positive integers prime to $N$
(a consequence of the theta transformation law: both values are $M_A(\cdot, N)$). -/
theorem jacobiSym_thetaDisc_periodic {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    {N : ℕ} (hN0 : 0 < N) (hN : IsThetaLevel Q N) {x y : ℕ} (hx : Odd x) (hy : Odd y)
    (hxN : Nat.Coprime x N) (hxy : (x : ℤ) % N = (y : ℤ) % N) :
    jacobiSym (thetaDisc Q k) x = jacobiSym (thetaDisc Q k) y := by
  have : NeZero N := ⟨hN0.ne'⟩
  have hyN : Nat.Coprime y N := by
    have : (x : ZMod N) = (y : ZMod N) := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) N).mpr (Int.ModEq.dvd hxy)
      exact_mod_cast this
    rw [← ZMod.isUnit_iff_coprime] at hxN ⊢
    rwa [← this]
  have h1 := thetaMult_eq_jacobiSym hQ hn hN0 hN hx (c0 := 1) (by ring) hxN
  have h2 := thetaMult_eq_jacobiSym hQ hn hN0 hN hy (c0 := 1) (by ring) hyN
  obtain ⟨t, ht⟩ : (N : ℤ) ∣ (y : ℤ) - x := Int.ModEq.dvd hxy
  have h3 : thetaMult (gramMatrix Q) k (y : ℤ) N = thetaMult (gramMatrix Q) k (x : ℤ) N := by
    rw [show (y : ℤ) = x + t * N by linarith, thetaMult_add_mul (quadAt_gramMatrix_int Q)]
  rw [h1, h2] at h3
  exact_mod_cast h3.symm

/-- An odd positive representative of $d \bmod N$: $r = d \bmod N \in [0, N)$ if $r$ is odd, else $r + N$. For
$\gcd(d, N) = 1$ it is odd, positive, prime to $N$ and $\equiv d \pmod N$ (`oddRep_spec`). -/
def oddRep (N : ℕ) (d : ℤ) : ℕ :=
  if Odd (d % N).toNat then (d % N).toNat else (d % N).toNat + N

lemma oddRep_spec {N : ℕ} (hN0 : 0 < N) {d : ℤ} (hd : IsCoprime d N) :
    Odd (oddRep N d) ∧ ((oddRep N d : ℕ) : ℤ) % N = d % N ∧ Nat.Coprime (oddRep N d) N := by
  have hN0' : (0 : ℤ) < N := by exact_mod_cast hN0
  have hr0 : 0 ≤ d % N := Int.emod_nonneg _ hN0'.ne'
  have hrt : (((d % N).toNat : ℕ) : ℤ) = d % N := Int.toNat_of_nonneg hr0
  -- coprimality of anything `≡ d mod N`
  have hcop : ∀ x : ℕ, (x : ℤ) % N = d % N → Nat.Coprime x N := by
    intro x hx
    have : IsCoprime (x : ℤ) N := by
      obtain ⟨u, v, huv⟩ := hd
      obtain ⟨t, ht⟩ : (N : ℤ) ∣ (x : ℤ) - d := Int.ModEq.dvd hx.symm
      exact ⟨u, v - u * t, by rw [show (x : ℤ) = d + N * t by linarith]; linear_combination huv⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp this |> fun h => by simpa [Int.gcd] using h
  unfold oddRep
  split_ifs with ho
  · refine ⟨ho, ?_, ?_⟩
    · rw [hrt, Int.emod_emod_of_dvd _ (dvd_refl _)]
    · exact hcop _ (by rw [hrt, Int.emod_emod_of_dvd _ (dvd_refl _)])
  · have hmod : ((((d % N).toNat + N : ℕ)) : ℤ) % N = d % N := by
      push_cast; rw [hrt, Int.add_emod_right, Int.emod_emod_of_dvd _ (dvd_refl _)]
    refine ⟨?_, hmod, hcop _ hmod⟩
    rw [Nat.not_odd_iff_even] at ho
    rcases Nat.even_or_odd N with hNe | hNo
    · exfalso
      -- `2 ∣ d` and `2 ∣ N`
      have h2N : (2 : ℤ) ∣ N := by exact_mod_cast even_iff_two_dvd.mp hNe
      have h2r : (2 : ℤ) ∣ d % N := by
        rw [← hrt]; exact_mod_cast even_iff_two_dvd.mp ho
      have h2d : (2 : ℤ) ∣ d := by
        have := Int.emod_add_mul_ediv d N
        rw [← this]; exact dvd_add h2r (dvd_mul_of_dvd_left h2N _)
      have := IsCoprime.isUnit_of_dvd' hd h2d h2N
      rcases Int.isUnit_iff.mp this with h | h <;> norm_num at h
    · exact Even.add_odd ho hNo

/-- **The character of $\Theta_Q$:** for $d \in \mathbb{Z}$, $\chi_Q(d) = \left(\frac{\Delta_Q}{\tilde d}\right)$ (Jacobi symbol), where
$\Delta_Q = (-1)^k\det H$ and $\tilde d$ = `oddRep N d` is an odd positive integer $\equiv d \pmod N$. For $\gcd(d, N) = 1$ this
does not depend on the choice of $\tilde d$ (`thetaChi_eq_jacobiSym`): $\chi_Q(d) = (\Delta_Q/x)$ for every odd $x \ge 1$,
$x \equiv d \pmod N$. So $\chi_Q$ is a quadratic character mod $N$; it is the Kronecker symbol
$\left(\frac{\Delta_Q}{\cdot}\right)$ (at even $d$, for odd $N_Q$: `chiCharLevel_natCast_eq_kroneckerSym`). The canonical
Dirichlet character is `chiCharLevel` (modulo `level Q`); `thetaChi_eq_chiCharLevel` and `thetaChi_eq_chi` relate them.
For $n = 4$: $\chi_Q(d) = \left(\frac{\det H}{d}\right)$. -/
@[kb "hanke2004" "§4, p. 364 (the character χ) [unverified]"]
def thetaChi (Q : QuadForm ℤ n) (k N : ℕ) (d : ℤ) : ℤ := jacobiSym (thetaDisc Q k) (oddRep N d)

/-- $\chi_Q(d) = (\Delta_Q/x)$ for every odd positive $x \equiv d \pmod N$, $\gcd(d, N) = 1$. -/
theorem thetaChi_eq_jacobiSym {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {d : ℤ} (hd : IsCoprime d N) {x : ℕ} (hx : Odd x)
    (hxd : (x : ℤ) % N = d % N) : thetaChi Q k N d = jacobiSym (thetaDisc Q k) x := by
  obtain ⟨h1, h2, h3⟩ := oddRep_spec hN0 hd
  exact jacobiSym_thetaDisc_periodic hQ hn hN0 hN h1 hx h3 (h2.trans hxd.symm)

lemma exists_odd_pos_add_mul {a b d : ℤ} {c : ℕ} (hc : 0 < c) (hdet : a * d - b * c = 1) :
    ∃ j : ℕ, 0 < a + j * c ∧ Odd (a + j * c) := by
  have hc' : (1 : ℤ) ≤ c := by exact_mod_cast hc
  set j0 : ℕ := a.natAbs + 1 with hj0
  have hpos : ∀ j : ℕ, j0 ≤ j → 0 < a + j * c := by
    intro j hj
    have : (j0 : ℤ) ≤ j := by exact_mod_cast hj
    have h1 : |a| + 1 ≤ (j : ℤ) := by rw [hj0] at this; push_cast at this; exact this
    have h2 : -a ≤ |a| := neg_le_abs a
    nlinarith
  by_cases ho : Odd (a + j0 * c)
  · exact ⟨j0, hpos j0 le_rfl, ho⟩
  · refine ⟨j0 + 1, hpos _ (by omega), ?_⟩
    rw [Int.not_odd_iff_even] at ho
    push_cast
    rw [show a + ((j0 : ℤ) + 1) * c = (a + j0 * c) + c by ring]
    rcases Int.even_or_odd (c : ℤ) with hce | hco
    · exfalso
      -- `a` even and `c` even contradict `ad - bc = 1`
      have hae : Even a := by
        have := ho.sub (hce.mul_left (j0 : ℤ)); simpa using this
      have : Even (a * d - b * c) := (hae.mul_right d).sub (hce.mul_left b)
      rw [hdet] at this; exact (Int.not_even_one) this
    · exact ho.add_odd hco

/-- **The theta multiplier is $\chi_Q(d)$.** For $Q$ positive definite, $n = 2k$, $N$ a level, and
$\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ with $c = Nc_0 \ge 1$: $M_A(a, c) = \chi_Q(d)$. -/
theorem thetaMult_eq_thetaChi {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {a b d : ℤ} {c c0 : ℕ} [NeZero c] (hc : c = N * c0)
    (hdet : a * d - b * c = 1) :
    thetaMult (gramMatrix Q) k a c = (thetaChi Q k N d : ℂ) := by
  have hcpos : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hcN : (c : ℤ) = N * c0 := by exact_mod_cast hc
  have hdN : IsCoprime d N := ⟨a, -b * c0, by rw [← hdet, hcN]; ring⟩
  obtain ⟨j, hjpos, hjodd⟩ := exists_odd_pos_add_mul hcpos hdet
  set at' : ℕ := (a + j * c).toNat with hat
  have hat' : (at' : ℤ) = a + j * c := Int.toNat_of_nonneg hjpos.le
  have h1 : thetaMult (gramMatrix Q) k a c = thetaMult (gramMatrix Q) k at' c := by
    rw [hat', thetaMult_add_mul (quadAt_gramMatrix_int Q)]
  have hato : Odd at' := by
    rw [← Int.odd_coe_nat, hat']; exact hjodd
  have hatc : Nat.Coprime at' c := by
    have : IsCoprime (at' : ℤ) c := ⟨d, -b - j * d, by rw [hat', ← hdet]; ring⟩
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast] at this
    exact this
  rw [h1, thetaMult_eq_jacobiSym hQ hn hN0 hN hato hc hatc]
  -- compare `J(Δ | at')` with `J(Δ | oddRep N d)`
  obtain ⟨hxo, hxd, hxN⟩ := oddRep_spec hN0 hdN
  set x := oddRep N d
  have hatN : Nat.Coprime at' N := Nat.Coprime.coprime_dvd_right ⟨c0, hc⟩ hatc
  have hprod : jacobiSym (thetaDisc Q k) (at' * x) = 1 := by
    rw [jacobiSym_thetaDisc_periodic hQ hn hN0 hN (hato.mul hxo) odd_one
      (Nat.coprime_mul_iff_left.mpr ⟨hatN, hxN⟩) (y := 1) ?_, jacobiSym.one_right]
    -- `at' x ≡ a d ≡ 1 mod N`
    have e1 : ((at' * x : ℕ) : ℤ) = (a * d) + (j * c * d + (a + j * c) * (x - d)) := by
      push_cast; rw [hat']; ring
    obtain ⟨t, ht⟩ : (N : ℤ) ∣ (x : ℤ) - d := Int.ModEq.dvd hxd.symm
    rw [e1, show a * d = 1 + b * c by linarith, hcN, ht]
    rw [show 1 + b * (N * c0) + (j * (N * c0) * d + (a + j * (N * c0)) * (N * t)) =
      1 + (b * c0 + j * c0 * d + (a + j * (N * c0)) * t) * N by ring, Int.add_mul_emod_self_right]
    simp
  have hgcd : (thetaDisc Q k).gcd at' = 1 := by
    have := Nat.Coprime.coprime_dvd_right (thetaDisc_dvd hQ (k := k) hN0 hN)
      (Nat.Coprime.pow_right n hatN)
    rw [Int.gcd, Int.natAbs_natCast]; exact Nat.Coprime.symm this
  have hsq := jacobiSym.sq_one hgcd
  rw [jacobiSym.mul_right' _ (by rintro h; rw [h] at hato; simp at hato)
    (by rintro h; rw [h] at hxo; simp at hxo)] at hprod
  have : jacobiSym (thetaDisc Q k) x = jacobiSym (thetaDisc Q k) at' := by
    calc jacobiSym (thetaDisc Q k) x = jacobiSym (thetaDisc Q k) at' ^ 2 * jacobiSym (thetaDisc Q k) x := by
          rw [hsq, one_mul]
      _ = jacobiSym (thetaDisc Q k) at' := by rw [pow_two, mul_assoc, hprod, mul_one]
  rw [thetaChi, ← this]

/-- $G_S(-a, c) = \overline{G_S(a, c)}$. -/
lemma gaussSum_neg (S : Matrix (Fin n) (Fin n) ℝ) (a : ℤ) (c : ℕ) [NeZero c] :
    gaussSum S (-a) c 0 = starRingEnd ℂ (gaussSum S a c 0) := by
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_conj]
  congr 1
  simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero, map_mul,
    map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast, map_natCast, Int.cast_neg]
  ring

/-- $M_S(-a, c) = (-1)^k\,\overline{M_S(a, c)}$. -/
lemma thetaMult_neg (S : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (a : ℤ) (c : ℕ) [NeZero c] :
    thetaMult S k (-a) c = (-1) ^ k * starRingEnd ℂ (thetaMult S k a c) := by
  rw [thetaMult, thetaMult, gaussSum_neg, map_mul, map_mul, map_pow, Complex.conj_ofReal]
  simp only [map_div₀, map_neg, Complex.conj_I, map_mul, map_ofNat, map_natCast]
  rw [show -(-I) / (2 * (c : ℂ)) = (-1) * (-I / (2 * c)) by ring, mul_pow]
  ring_nf
  rw [pow_mul']
  norm_num

/-- $\chi_Q(-d) = (-1)^k \chi_Q(d)$ for $\gcd(d, N) = 1$. -/
theorem thetaChi_neg {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {d : ℤ} (hd : IsCoprime d N) :
    thetaChi Q k N (-d) = (-1) ^ k * thetaChi Q k N d := by
  have : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨u, v, huv⟩ := hd
  have h1 := thetaMult_eq_thetaChi hQ hn hN0 hN (a := u) (b := -v) (d := d) (c0 := 1) (by ring)
    (by linear_combination huv)
  have h2 := thetaMult_eq_thetaChi hQ hn hN0 hN (a := -u) (b := -v) (d := -d) (c0 := 1) (by ring)
    (by linear_combination huv)
  rw [thetaMult_neg, h1, map_intCast] at h2
  exact_mod_cast h2.symm

/-- **The theta transformation law on $\Gamma_0(N)$ with character $\chi_Q$** (Hanke 2004, §4; even rank $n = 2k$).
Let $Q$ be a positive definite integral form in $n = 2k$ variables, $N \ge 1$ a level (`IsThetaLevel`), and
$\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$ with $N \mid c$. For $\operatorname{Im} z > 0$,
$$\Theta_Q\Big(\frac{az+b}{cz+d}\Big) = \chi_Q(d)\,(cz+d)^k\,\Theta_Q(z),$$
where $\chi_Q(d) = \left(\frac{(-1)^k\det H}{\tilde d}\right)$ (`thetaChi`; Jacobi symbol at an odd positive $\tilde d \equiv d \bmod N$). Restated with the canonical character
`chiCharLevel` as `theta_gamma0_chiCharLevel`. -/
@[kb "hanke2004" "§4, p. 364 (Θ_Q ∈ M_{n/2}(Γ₀(N), χ)) [unverified]"]
theorem theta_gamma0_chi {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {a b c d : ℤ} (hdet : a * d - b * c = 1)
    (hNc : (N : ℤ) ∣ c) {z : ℂ} (hz : 0 < z.im) :
    theta Q ((a * z + b) / (c * z + d)) = (thetaChi Q k N d : ℂ) * (c * z + d) ^ k * theta Q z := by
  obtain ⟨c0, hc0⟩ := hNc
  have hdN : IsCoprime d N := ⟨a, -b * c0, by rw [← hdet, hc0]; ring⟩
  -- the case `c > 0`
  have pos : ∀ {a b c d : ℤ}, a * d - b * c = 1 → 0 < c → (N : ℤ) ∣ c →
      theta Q ((a * z + b) / (c * z + d)) = (thetaChi Q k N d : ℂ) * (c * z + d) ^ k * theta Q z := by
    intro a b c d hdet hc hNc
    obtain ⟨c0, hc0⟩ := hNc
    set c' : ℕ := c.toNat with hc'
    have hc'c : (c' : ℤ) = c := Int.toNat_of_nonneg hc.le
    have : NeZero c' := ⟨by omega⟩
    have hc0pos : 0 ≤ c0 := by
      by_contra h; push Not at h
      have : (N : ℤ) * c0 < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hN0) h
      omega
    have hc'N : c' = N * c0.toNat := by
      have : ((N * c0.toNat : ℕ) : ℤ) = c := by push_cast; rw [Int.toNat_of_nonneg hc0pos, hc0]
      omega
    have hdet' : a * d - b * (c' : ℤ) = 1 := by rw [hc'c]; exact hdet
    have h := theta_gamma0 hQ hn hN0 hN (Nat.dvd_of_mod_eq_zero (by rw [hc'N]; simp)) hdet' hz
    rw [thetaMult_eq_thetaChi hQ hn hN0 hN hc'N hdet'] at h
    have : ((c' : ℕ) : ℂ) = (c : ℂ) := by exact_mod_cast hc'c
    rw [this] at h
    exact h
  rcases lt_trichotomy c 0 with hc | hc | hc
  · -- `c < 0`: use `-γ`
    have h := pos (a := -a) (b := -b) (c := -c) (d := -d) (by linarith) (by linarith)
      ⟨-c0, by rw [hc0]; ring⟩
    have e1 : (((-a : ℤ) : ℂ) * z + ((-b : ℤ) : ℂ)) / (((-c : ℤ) : ℂ) * z + ((-d : ℤ) : ℂ)) =
        (a * z + b) / (c * z + d) := by
      push_cast
      rw [show -(a : ℂ) * z + -b = -(a * z + b) by ring, show -(c : ℂ) * z + -d = -(c * z + d) by ring,
        neg_div_neg_eq]
    rw [e1, thetaChi_neg hQ hn hN0 hN hdN] at h
    rw [h]
    push_cast
    rw [show -(c : ℂ) * z + -d = (-1) * (c * z + d) by ring, mul_pow]
    have : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (thetaChi Q k N d * (c * z + d) ^ k * theta Q z) * this
  · -- `c = 0`: `γ = ±T^b`
    subst hc
    have had : a * d = 1 := by linarith
    have hd : d = 1 ∨ d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have ha : a = d := by rcases hd with rfl | rfl <;> omega
    subst ha
    have hz' : ((a : ℂ) * z + b) / ((0 : ℤ) * z + a) = z + (a * b : ℤ) := by
      rcases hd with rfl | rfl <;> push_cast <;> field_simp <;> ring
    rw [hz', theta_add_int]
    have h1 : thetaChi Q k N 1 = 1 := by
      rw [thetaChi_eq_jacobiSym hQ hn hN0 hN isCoprime_one_left odd_one (by simp),
        jacobiSym.one_right]
    rcases hd with rfl | rfl
    · rw [h1]; simp
    · rw [thetaChi_neg hQ hn hN0 hN isCoprime_one_left, h1]
      push_cast
      ring_nf
      rw [pow_mul']
      norm_num
  · exact pos hdet hc ⟨c0, hc0⟩

/-! ### Modular forms: $M_k(\Gamma_1(N))$, and $M_k(\Gamma_0(N))$ when $\chi_Q$ is trivial -/

/-- $\chi_Q(d)$ depends only on $d \bmod N$. -/
lemma thetaChi_congr (Q : QuadForm ℤ n) (k N : ℕ) {d d' : ℤ} (h : d % N = d' % N) :
    thetaChi Q k N d = thetaChi Q k N d' := by
  simp only [thetaChi, oddRep, h]

/-- **Slash form of the $\Gamma_0(N)$ law:** $\Theta_Q \mid_k \gamma = \chi_Q(d)\,\Theta_Q$ for every $\gamma \in \Gamma_0(N)$,
$d = \gamma_{11}$ (0-based entries: $\gamma = \begin{pmatrix}\gamma_{00}&\gamma_{01}\\\gamma_{10}&\gamma_{11}\end{pmatrix}$). -/
theorem thetaH_slash_gamma0 {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    thetaH Q ∣[(k : ℤ)] γ = (thetaChi Q k N (γ 1 1) : ℂ) • thetaH Q := by
  have hNc : (N : ℤ) ∣ γ 1 0 := by
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ; exact hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  ext τ
  have h := theta_gamma0_chi hQ hn hN0 hN hdet hNc τ.im_pos
  have hd : ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
    simpa [UpperHalfPlane.denom] using this
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [thetaH]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, ofReal_intCast]
  rw [h, _root_.zpow_neg, zpow_natCast]
  field_simp

/-- **$\Theta_Q$ is a modular form of weight $k$ for $\Gamma_1(N)$** (even rank $n = 2k$, $Q$ positive definite, $N$ a
level): Mathlib's `ModularForm Γ₁(N) k`. Invariance: $\chi_Q(d) = \chi_Q(1) = 1$ for $d \equiv 1 \bmod N$ (`thetaH_slash_gamma0`);
holomorphy: `differentiableOn_theta`; cusps: `isBoundedAtImInfty_thetaH_slash`. Together with `thetaH_slash_gamma0`
this is $\Theta_Q \in M_k(\Gamma_0(N), \chi_Q)$ (Mathlib has no spaces of modular forms with character). -/
@[kb "hanke2004" "§4, p. 364 [unverified]"]
def thetaMFGamma1 {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) : ModularForm (CongruenceSubgroup.Gamma1 N) k where
  toFun := thetaH Q
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change thetaH Q ∣[(k : ℤ)] γ = thetaH Q
    obtain ⟨_, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N γ).mp hγ
    have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := (CongruenceSubgroup.Gamma0_mem).mpr h10
    rw [thetaH_slash_gamma0 hQ hn hN0 hN hγ0]
    have h1 : thetaChi Q k N (γ 1 1) = 1 := by
      have : (γ 1 1) % N = (1 : ℤ) % N := by
        have h' : ((γ 1 1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using h11
        exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h'
      rw [thetaChi_congr Q k N this, thetaChi_eq_jacobiSym hQ hn hN0 hN isCoprime_one_left odd_one
        (by simp), jacobiSym.one_right]
    rw [h1]; simp
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_theta hQ).congr fun z hz => ?_
    simp [thetaH, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  bdd_at_cusps' hc := by
    have : NeZero N := ⟨hN0.ne'⟩
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => isBoundedAtImInfty_thetaH_slash hQ hn γ

@[simp] theorem thetaMFGamma1_apply {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) (τ : UpperHalfPlane) :
    thetaMFGamma1 hQ hn hN0 hN τ = theta Q τ := rfl

/-- **$\Theta_Q \in M_k(\Gamma_0(N))$ when the character is trivial** ($\chi_Q(d) = 1$ for all $d$ prime to $N$). -/
def thetaMFGamma0 {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) {N : ℕ}
    (hN0 : 0 < N) (hN : IsThetaLevel Q N) (hχ : ∀ d : ℤ, IsCoprime d N → thetaChi Q k N d = 1) :
    ModularForm (CongruenceSubgroup.Gamma0 N) k where
  toFun := thetaH Q
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    change thetaH Q ∣[(k : ℤ)] γ = thetaH Q
    rw [thetaH_slash_gamma0 hQ hn hN0 hN hγ]
    have hγ' : γ ∈ CongruenceSubgroup.Gamma0 N := hγ
    have hNc : (N : ℤ) ∣ γ 1 0 := by
      rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ'; exact hγ'
    obtain ⟨c0, hc0⟩ := hNc
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    rw [hχ _ ⟨γ 0 0, -γ 0 1 * c0, by linear_combination hdet + γ 0 1 * hc0⟩]; simp
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_theta hQ).congr fun z hz => ?_
    simp [thetaH, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  bdd_at_cusps' hc := by
    have : NeZero N := ⟨hN0.ne'⟩
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => isBoundedAtImInfty_thetaH_slash hQ hn γ

/-! ### Quaternary forms (Hanke 2004) and the four-squares check -/

/-- For $n = 4$ the discriminant is $\Delta_Q = \det H$. -/
lemma thetaDisc_four (Q : QuadForm ℤ 4) : thetaDisc Q 2 = Q.hessian.det := by
  simp [thetaDisc]

/-- **Quaternary forms: $\Theta_Q \in M_2(\Gamma_0(N), \chi_Q)$** (Hanke 2004, §4, $n = 4$). For $Q$ a positive definite
integral quaternary form with level $N$ (`IsThetaLevel`) and $\begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$,
$N \mid c$, $\operatorname{Im} z > 0$:
$$\Theta_Q\Big(\frac{az+b}{cz+d}\Big) = \Big(\frac{\det H}{\tilde d}\Big)(cz+d)^2\,\Theta_Q(z),$$
where $\tilde d$ = `oddRep N d` is an odd positive integer $\equiv d \pmod N$ and $(\cdot/\cdot)$ is the Jacobi symbol; by
`thetaChi_eq_jacobiSym` any odd positive $\tilde d \equiv d \pmod N$ gives the same value. In Hanke's notation
($D_Q = \det(\text{Gram}) = \det H/16$) the character is $\left(\frac{16 D_Q}{\cdot}\right)$, which equals
$\left(\frac{D_Q}{\cdot}\right)$ at odd arguments when $D_Q \in \mathbb{Z}$. -/
@[kb "hanke2004" "§4, p. 364 (n = 4) [unverified]"]
theorem theta_gamma0_quaternary {Q : IntQF 4} (hQ : Q.PosDef) {N : ℕ} (hN0 : 0 < N)
    (hN : IsThetaLevel Q N) {a b c d : ℤ} (hdet : a * d - b * c = 1) (hNc : (N : ℤ) ∣ c)
    {z : ℂ} (hz : 0 < z.im) :
    theta Q ((a * z + b) / (c * z + d)) =
      (jacobiSym Q.hessian.det (oddRep N d) : ℂ) * (c * z + d) ^ 2 * theta Q z := by
  have h := theta_gamma0_chi hQ (k := 2) rfl hN0 hN hdet hNc hz
  rwa [thetaChi, thetaDisc_four] at h

/-- $\Theta_{I_4}$, $I_4 = x_0^2 + x_1^2 + x_2^2 + x_3^2$: $\det H = 16$ and $\chi_{I_4}$ is trivial
($(16/x) = (4^2/x) = 1$ for odd $x$). -/
lemma thetaChi_sumSq_four (d : ℤ) (hd : IsCoprime d (4 : ℕ)) : thetaChi (sumSq 4) 2 4 d = 1 := by
  obtain ⟨ho, -, -⟩ := oddRep_spec (by norm_num : 0 < 4) hd
  have hdet : (sumSq 4).hessian.det = 4 ^ 2 := by
    rw [hessian_sumSq, det_smul, det_one]; norm_num
  rw [thetaChi, thetaDisc_four, hdet]
  refine jacobiSym.sq_one' ?_
  rw [Int.gcd, Int.natAbs_natCast]
  have : Nat.Coprime 4 (oddRep 4 d) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
  simpa using this

/-- **Sanity check: $\Theta_{I_4} = \vartheta^4 \in M_2(\Gamma_0(4))$** (trivial character), recovering the classical
fact used for Jacobi's four-squares theorem. Here $H = 2I_4$, $\det H = 16$, level $N = 4$. -/
@[kb "iwaniec1997" "§10.4 / Ch. 11, four squares [unverified]"]
def thetaMF_sumSq_four : ModularForm (CongruenceSubgroup.Gamma0 4) 2 :=
  thetaMFGamma0 posDef_sumSq (n := 4) (k := 2) rfl (by norm_num) isThetaLevel_sumSq
    thetaChi_sumSq_four

@[simp] theorem thetaMF_sumSq_four_apply (τ : UpperHalfPlane) :
    thetaMF_sumSq_four τ = theta (sumSq 4) τ := rfl

end

end QuadFormsKB.Siegel