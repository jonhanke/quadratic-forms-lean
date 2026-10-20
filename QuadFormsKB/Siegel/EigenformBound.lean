/-
# The cusp-form coefficient bound (4.8) from the eigenform decomposition and Deligne's bound

Hanke 2004, p. 367: a cusp form $g(z) = \sum_{m \ge 1}b(m)e(mz)$ of integral weight $k$ on $\Gamma_0(N)$ with character
$\chi$ is written as
$$g = \sum_{i=1}^r\gamma_ig_i \qquad (4.7)$$
with $g_i = \sum_{m \ge 1}b_i(m)e(mz)$ Hecke eigenforms normalized so that their first nonzero coefficient is $1$; by
the theory of newforms (Atkin–Lehner [`atkinlehner1970`]; with character, Li 1975 [unverified]) and Deligne's bound
[`deligne1974`], $|b_i(m)| \le \tau(m)m^{(k-1)/2}$, hence
$$|b(m)| \le \tau(m)\,m^{(k-1)/2}\sum_{i=1}^r|\gamma_i| \qquad (4.8).$$

**Cited input** (`EigenformDecompDeligne N χ`, weight $k = 2$, the case of quaternary theta series): every
$g \in S_2(\Gamma_0(N), \chi)$ has such a decomposition with $|b_i(m)| \le \tau(m)\,m^{1/2}$. Mathlib has neither Hecke
operators nor newforms, so "Hecke eigenform" is not part of the Lean statement; what is stated is what (4.8) uses: the
$g_i$ are in $S_2(\Gamma_0(N), \chi)$, normalized, and satisfy Deligne's bound.

**Proved** (`eq_4_8`, `cuspBound_of_eigenformDecomp`): (4.8), and the repo's `CuspBound c (1/2) C` with
$C = \sum_i|\gamma_i|$ for any real sequence $c$ with $|c(m)| \le |b(m)|$ (e.g. $c(m) = b(m)$ when the coefficients
are real, as for $\theta_Q - \theta_{\mathrm{Gen}(Q)}$).

**Representation of $S_2(\Gamma_0(N), \chi)$** (as for $\Theta_Q$ in `Siegel/ThetaGamma0.lean`, `thetaMFGamma1`,
`thetaH_slash_gamma0`): a Mathlib `CuspForm (Gamma1 N) 2` $g$ with $g\,|_2\,\gamma = \chi(d)\,g$ for every
$\gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \Gamma_0(N)$ (`IsCuspFormWithChar`), and $b(m)$ = the $m$-th coefficient of
Mathlib's $q$-expansion with period $1$ (`qCoeff`).
-/
import QuadFormsKB.Siegel.Inputs
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open ModularForm
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

/-- **$g \in S_k(\Gamma_0(N), \chi)$** for a cusp form $g$ on $\Gamma_1(N)$: $g\,|_k\,\gamma = \chi(d)\,g$ for every
$\gamma = \begin{pmatrix}\gamma_{00}&\gamma_{01}\\\gamma_{10}&\gamma_{11}\end{pmatrix} \in \Gamma_0(N)$, $d = \gamma_{11}$ (0-based
entries; Mathlib has no spaces of modular forms with character, cf. `thetaH_slash_gamma0`).

Parameters: `χ`, a Dirichlet character modulo $N$ with values in $\mathbb{C}$; `g`, a Mathlib cusp form of weight $k$ for
$\Gamma_1(N)$. -/
@[kb "hanke2004" "§4, p. 364 (S_k(Γ₀(N), χ))"]
def IsCuspFormWithChar {N : ℕ} (χ : DirichletCharacter ℂ N) {k : ℤ}
    (g : CuspForm (CongruenceSubgroup.Gamma1 N) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
    (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = χ ((γ 1 1 : ℤ) : ZMod N) • (⇑g : UpperHalfPlane → ℂ)

/-- **The $m$-th Fourier coefficient** $b(m)$ of $g(z) = \sum_{m \ge 0}b(m)e(mz)$: the coefficient of $q^m$ in Mathlib's
$q$-expansion with period $1$, $q = e^{2\pi iz}$ (`UpperHalfPlane.qExpansion 1`). -/
noncomputable def qCoeff {N : ℕ} {k : ℤ} (g : CuspForm (CongruenceSubgroup.Gamma1 N) k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 (⇑g : UpperHalfPlane → ℂ)).coeff m

/-- **Normalized $q$-expansion** (Hanke 2004, p. 367, normalization of the $g_i$ in (4.7)): the first nonzero coefficient
$b(m_0)$, $m_0 \ge 1$, is $1$.

Field: `exists_first`: there is $m_0 \ge 1$ with $b(m_0) = 1$ and $b(m) = 0$ for $1 \le m < m_0$. -/
structure IsNormalizedQExp (b : ℕ → ℂ) : Prop where
  exists_first : ∃ m₀ : ℕ, 1 ≤ m₀ ∧ b m₀ = 1 ∧ ∀ m, 1 ≤ m → m < m₀ → b m = 0

/-- **Input: the eigenform decomposition (4.7) with Deligne's bound, weight 2** (Hanke 2004, (4.7)–(4.8), p. 367;
Atkin–Lehner 1970 [`atkinlehner1970`], newforms; Deligne 1974 [`deligne1974`], $|b_i(m)| \le \tau(m)m^{(k-1)/2}$).

For $N \ge 1$ and a Dirichlet character $\chi$ modulo $N$: every $g \in S_2(\Gamma_0(N), \chi)$
(`IsCuspFormWithChar`) can be written, on the coefficients $b(m)$, $m \ge 1$, as $g = \sum_{i < r}\gamma_ig_i$ with finitely
many $g_i \in S_2(\Gamma_0(N), \chi)$ whose $q$-expansions $\sum_m b_i(m)q^m$ are normalized (`IsNormalizedQExp`) and
satisfy Deligne's bound $|b_i(m)| \le \tau(m)\,m^{1/2}$ ($m^{(k-1)/2}$ with $k = 2$; $\tau$ = `divCount`).

Field:
- `decomp`: for every $g$ with `IsCuspFormWithChar χ g` there are $r \in \mathbb{N}$, cusp forms $g_0, \dots, g_{r-1}$ and
  $\gamma_0, \dots, \gamma_{r-1} \in \mathbb{C}$ with (i) each $g_i \in S_2(\Gamma_0(N), \chi)$, (ii) each $g_i$ normalized,
  (iii) $b(m) = \sum_i\gamma_ib_i(m)$ for all $m \ge 1$ ((4.7) on coefficients), (iv)
  $|b_i(m)| \le \tau(m)m^{1/2}$ for all $i$ and $m \ge 1$ (Deligne).

*Why true:* $S_2(\Gamma_0(N), \chi)$ has a basis of forms $f(dz)$, $f$ a normalized newform of level $M$, $dM \mid N$
(Atkin–Lehner for trivial $\chi$; Li 1975 [unverified] with character); $f(dz)$ is normalized (first coefficient
$b(d) = 1$) and $|a_f(m/d)| \le \tau(m/d)(m/d)^{1/2} \le \tau(m)m^{1/2}$ by Deligne (for weight 2 already Eichler–Shimura–Igusa).
Hanke calls the $g_i$ "eigenforms for all $T_p$"; Mathlib has no Hecke operators, so that property is not stated (it is
not used in (4.8)). The identity (4.7) is stated on the coefficients $m \ge 1$ (the constant terms vanish for cusp
forms), which is what (4.8) uses. Not proved here (cited). -/
@[kb "hanke2004" "(4.7)–(4.8), p. 367"]
structure EigenformDecompDeligne (N : ℕ) (χ : DirichletCharacter ℂ N) : Prop where
  decomp : ∀ g : CuspForm (CongruenceSubgroup.Gamma1 N) 2, IsCuspFormWithChar χ g →
    ∃ (r : ℕ) (gs : Fin r → CuspForm (CongruenceSubgroup.Gamma1 N) 2) (γ : Fin r → ℂ),
      (∀ i, IsCuspFormWithChar χ (gs i)) ∧
      (∀ i, IsNormalizedQExp (qCoeff (gs i))) ∧
      (∀ m : ℕ, 1 ≤ m → qCoeff g m = ∑ i, γ i * qCoeff (gs i) m) ∧
      (∀ i, ∀ m : ℕ, 1 ≤ m → ‖qCoeff (gs i) m‖ ≤ divCount m * (m : ℝ) ^ (1 / 2 : ℝ))

/-- **(4.8)** (Hanke 2004, p. 367), the coefficient bound from a decomposition (4.7) with Deligne's bound: if
$b(m) = \sum_{i < r}\gamma_ib_i(m)$ and $|b_i(m)| \le \tau(m)m^{\alpha}$ for $m \ge 1$, then
$$|b(m)| \le \tau(m)\,m^{\alpha}\sum_{i < r}|\gamma_i| \qquad (m \ge 1).$$
(Hanke: $\alpha = (k-1)/2$.) -/
@[kb "hanke2004" "(4.8), p. 367"]
theorem eq_4_8 {r : ℕ} (b : ℕ → ℂ) (bs : Fin r → ℕ → ℂ) (γ : Fin r → ℂ) (α : ℝ)
    (hdec : ∀ m : ℕ, 1 ≤ m → b m = ∑ i, γ i * bs i m)
    (hD : ∀ i, ∀ m : ℕ, 1 ≤ m → ‖bs i m‖ ≤ divCount m * (m : ℝ) ^ α) {m : ℕ} (hm : 1 ≤ m) :
    ‖b m‖ ≤ divCount m * (m : ℝ) ^ α * ∑ i, ‖γ i‖ := by
  rw [hdec m hm, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hD i m hm) (norm_nonneg _)

/-- **(4.8) as the repo's `CuspBound`, weight 2** (Hanke 2004, (4.8), p. 367, with $k = n/2 = 2$, $\alpha = (k-1)/2 = 1/2$):
under `EigenformDecompDeligne N χ`, for $g \in S_2(\Gamma_0(N), \chi)$ and any real sequence $c$ with
$|c(m)| \le |b(m)|$ for $m \ge 1$ ($b$ the coefficients of $g$; e.g. $c(m) = b(m)$ for real coefficients), there are
$\gamma_0, \dots, \gamma_{r-1}$ (those of (4.7)) with
$$|c(m)| \le \Big(\sum_{i < r}|\gamma_i|\Big)\tau(m)\,m^{1/2} \qquad (m \ge 1),$$
i.e. `CuspBound c (1/2) (∑ i, ‖γ i‖)`. -/
@[kb "hanke2004" "(4.8), p. 367 (k = 2)"]
theorem cuspBound_of_eigenformDecomp {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hED : EigenformDecompDeligne N χ) {g : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hg : IsCuspFormWithChar χ g) {c : ℕ → ℝ} (hc : ∀ m : ℕ, 1 ≤ m → |c m| ≤ ‖qCoeff g m‖) :
    ∃ (r : ℕ) (γ : Fin r → ℂ), CuspBound c (1 / 2) (∑ i, ‖γ i‖) := by
  obtain ⟨r, gs, γ, -, -, hdec, hD⟩ := hED.decomp g hg
  refine ⟨r, γ, ⟨fun m hm => ?_⟩⟩
  have h := eq_4_8 (qCoeff g) (fun i => qCoeff (gs i)) γ (1 / 2) hdec hD hm
  calc |c m| ≤ ‖qCoeff g m‖ := hc m hm
    _ ≤ divCount m * (m : ℝ) ^ (1 / 2 : ℝ) * ∑ i, ‖γ i‖ := h
    _ = (∑ i, ‖γ i‖) * divCount m * (m : ℝ) ^ (1 / 2 : ℝ) := by ring

/-- Under `EigenformDecompDeligne N χ`, every $g \in S_2(\Gamma_0(N), \chi)$ with real coefficients $c(m) = b(m)$
($m \ge 1$) satisfies `CuspBound c (1/2) C` for some $C \ge 0$. -/
theorem exists_cuspBound_of_eigenformDecomp {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hED : EigenformDecompDeligne N χ) {g : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hg : IsCuspFormWithChar χ g) {c : ℕ → ℝ} (hc : ∀ m : ℕ, 1 ≤ m → (c m : ℂ) = qCoeff g m) :
    ∃ C : ℝ, 0 ≤ C ∧ CuspBound c (1 / 2) C := by
  obtain ⟨r, γ, h⟩ := cuspBound_of_eigenformDecomp hED hg (c := c) fun m hm => by
    rw [← hc m hm, Complex.norm_real, Real.norm_eq_abs]
  exact ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, h⟩

end QuadFormsKB.Siegel
