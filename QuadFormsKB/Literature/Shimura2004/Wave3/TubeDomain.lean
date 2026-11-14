/-
# Shimura 2004, §15.1–15.2 and Lemma 15.4: the tube domain $U + iD$ is stable under $z \mapsto -z^{-1}$

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), Chapter IV, §15.1 (the cone $D$,
(15.2)), §15.2 ((15.4a–c), the domain $\mathfrak h$) and Lemma 15.4 (printed pp. 146–148). Page numbers are printed
pages.

**Setting and dictionary.** $U$ is a real vector space with a nondegenerate form `Q : QuadraticForm ℝ U` of signature
$(1, m-1)$, $m = \dim U$: there is a vector with $\varphi[x] > 0$ and every subspace on which $\varphi$ is positive
definite has dimension at most $1$ (`IsLorentzian`). Fix $\varepsilon \in U$ with $\varphi[\varepsilon] > 0$. In
$A(U)$, $x\varepsilon + \varepsilon x = 2\varphi(x, \varepsilon)$, so Shimura's cone (15.2)
$D = \{x \in U : x^2 > 0,\ x\varepsilon + \varepsilon x > 0\}$ is `lorentzCone Q ε`
$= \{x : \varphi[x] > 0,\ \varphi(x, \varepsilon) > 0\}$.

**Complexification.** An element $z = x + iy$ of $U_{\mathbb C}$ is the pair $(x, y) \in U \times U$; it lies in
$\mathfrak h = U + iD$ (15.4a) iff $y \in D$. In $A(U_{\mathbb C})$, $z^2 = \varphi_{\mathbb C}[z]$ with
$\varphi_{\mathbb C}[x + iy] = \varphi[x] - \varphi[y] + 2i\,\varphi(x, y)$ (`complexValue Q x y`), so $z$ is
invertible exactly when $\varphi_{\mathbb C}[z] \ne 0$, and then $-z^{-1} = -z/\varphi_{\mathbb C}[z]$ is again a
vector of $U_{\mathbb C}$. Writing $\varphi_{\mathbb C}[z] = \alpha + i\beta$, $N = \alpha^2 + \beta^2$:
$$-z^{-1} = \frac{-(\alpha x + \beta y)}{N} + i\,\frac{\beta x - \alpha y}{N}.$$
Lemma 15.4 therefore says: for $y \in D$, $\varphi_{\mathbb C}[x + iy] \ne 0$ and $(\beta x - \alpha y)/N \in D$.
This vector form is what is formalized (`Lemma15_4`); the Clifford algebra $A(U_{\mathbb C})$ itself is not used.

**Proves.** `lemma_15_4 : Lemma15_4` (unconditional, no named inputs), via: negative semidefiniteness of
$y^\perp$ for $\varphi[y] > 0$ (`Q_nonpos_of_orth`), the reverse Cauchy–Schwarz inequality `reverse_cs`
($\varphi[x]\varphi[y] \le \varphi(x,y)^2$), and transitivity of "same time cone" (`bil_pos_trans`).
-/
import QuadFormsKB.Literature.OMeara.Sec82
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import QuadFormsKB.Citation

open Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.OMeara

/-- $2$ is invertible in $\mathbb R$ (local instance, needed by `OMeara.bil`). -/
@[instance_reducible] def invertibleTwoReal : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

attribute [local instance] invertibleTwoReal

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- **Signature $(1, m-1)$** (Shimura 2004, §15.1, p. 146): $\varphi$ takes a positive value, and every subspace on
which $\varphi$ is positive definite has dimension at most $1$. (For nondegenerate $\varphi$ on an $m$-dimensional
space this is signature $(1, m-1)$.) -/
def IsLorentzian (Q : QuadraticForm ℝ U) : Prop :=
  (∃ x : U, 0 < Q x) ∧ ∀ W : Submodule ℝ U, (∀ w ∈ W, w ≠ 0 → 0 < Q w) → finrank ℝ W ≤ 1

/-- **The cone $D$** (Shimura 2004, (15.2), p. 146): $D = \{x \in U : x^2 > 0,\ x\varepsilon + \varepsilon x > 0\}$,
i.e. $\varphi[x] > 0$ and $\varphi(x, \varepsilon) > 0$. -/
@[kb "shimura2004" "(15.2), p. 146 (the cone D = {x ∈ U : x² > 0, xε + εx > 0})"]
def lorentzCone (Q : QuadraticForm ℝ U) (ε : U) : Set U := {x | 0 < Q x ∧ 0 < bil Q x ε}

/-- $\varphi_{\mathbb C}[x + iy] = \varphi[x] - \varphi[y] + 2i\,\varphi(x, y)$, the value of the complexified form
(so $z^2 = \varphi_{\mathbb C}[z]$ in $A(U_{\mathbb C})$, Shimura 2004, §15.2, p. 147). -/
def complexValue (Q : QuadraticForm ℝ U) (x y : U) : ℂ := ⟨Q x - Q y, 2 * bil Q x y⟩

/-- The imaginary part of $-z^{-1} = -z/\varphi_{\mathbb C}[z]$ for $z = x + iy$:
$(\beta x - \alpha y)/(\alpha^2 + \beta^2)$ with $\alpha + i\beta = \varphi_{\mathbb C}[z]$. -/
def negInvIm (Q : QuadraticForm ℝ U) (x y : U) : U :=
  (Complex.normSq (complexValue Q x y))⁻¹ •
    ((complexValue Q x y).im • x - (complexValue Q x y).re • y)

/-- **Lemma 15.4** (Shimura 2004, p. 148), vector form: for $U$ of signature $(1, m-1)$, $\varphi[\varepsilon] > 0$
and $z = x + iy \in \mathfrak h = U + iD$ ($y \in D$): $\varphi_{\mathbb C}[z] \ne 0$ (so $z$ is invertible in
$A(U_{\mathbb C})$), and $-z^{-1} \in \mathfrak h$, i.e. its imaginary part `negInvIm Q x y` lies in $D$. -/
@[kb "shimura2004" "Lemma 15.4, p. 148 (z ∈ 𝔥 ⇒ z invertible and -z⁻¹ ∈ 𝔥)"]
def Lemma15_4 : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℝ U] [FiniteDimensional ℝ U] (Q : QuadraticForm ℝ U),
    (QuadraticMap.associated Q).Nondegenerate → IsLorentzian Q →
    ∀ ε : U, 0 < Q ε → ∀ x y : U, y ∈ lorentzCone Q ε →
      complexValue Q x y ≠ 0 ∧ negInvIm Q x y ∈ lorentzCone Q ε

/-! ### Proof of Lemma 15.4 -/

/-- Expansion of $\varphi[s x + t y] = s^2 \varphi[x] + 2 s t\,\varphi(x, y) + t^2 \varphi[y]$ for real
scalars $s, t$ and vectors $x, y$. -/
theorem Q_comb (Q : QuadraticForm ℝ U) (s t : ℝ) (x y : U) :
    Q (s • x + t • y) = s * s * Q x + 2 * (s * t) * bil Q x y + t * t * Q y := by
  rw [Q_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, bil_smul_left, bil_smul_right]
  ring

/-- Expansion $\varphi(s x + t y, z) = s\,\varphi(x, z) + t\,\varphi(y, z)$ for real scalars $s, t$. -/
theorem bil_comb_left (Q : QuadraticForm ℝ U) (s t : ℝ) (x y z : U) :
    bil Q (s • x + t • y) z = s * bil Q x z + t * bil Q y z := by
  rw [bil_add_left Q, bil_smul_left, bil_smul_left]

/-- Decomposition along a vector $y$ with $\varphi[y] > 0$: every $x$ is $t y + w$ with $t\,\varphi[y] = \varphi(x, y)$
and $w$ orthogonal to $y$, i.e. $\varphi(w, y) = 0$. -/
theorem decomp_along (Q : QuadraticForm ℝ U) (x y : U) (hy : 0 < Q y) :
    ∃ (t : ℝ) (w : U), x = t • y + w ∧ bil Q w y = 0 ∧ t * Q y = bil Q x y := by
  have hne : Q y ≠ 0 := hy.ne'
  refine ⟨bil Q x y / Q y, x - (bil Q x y / Q y) • y, by simp, ?_, by field_simp⟩
  rw [bil_sub_left Q, bil_smul_left, bil_self Q]
  field_simp
  ring

/-- The orthogonal complement of a vector $y$ with $\varphi[y] > 0$ is negative semidefinite when $\varphi$ has
signature $(1, m-1)$: if $\varphi(w, y) = 0$ then $\varphi[w] \le 0$. -/
theorem Q_nonpos_of_orth {Q : QuadraticForm ℝ U} (hL : IsLorentzian Q) {y w : U} (hy : 0 < Q y)
    (h : bil Q w y = 0) : Q w ≤ 0 := by
  by_contra hw
  push Not at hw
  have hyw : bil Q y w = 0 := by rw [bil_comm Q]; exact h
  have key : ∀ s t : ℝ, Q (s • y + t • w) = s * s * Q y + t * t * Q w := by
    intro s t
    rw [Q_comb, hyw]; ring
  have hli : LinearIndependent ℝ ![y, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t h0
    have h1 := key s t
    rw [h0, map_zero] at h1
    have h2 : s * s * Q y = 0 := by
      nlinarith [mul_nonneg (mul_self_nonneg s) hy.le, mul_nonneg (mul_self_nonneg t) hw.le]
    have h3 : t * t * Q w = 0 := by
      nlinarith [mul_nonneg (mul_self_nonneg s) hy.le, mul_nonneg (mul_self_nonneg t) hw.le]
    simp [hy.ne', hw.ne'] at h2 h3
    exact ⟨h2, h3⟩
  have hfin := finrank_span_eq_card hli
  simp only [Fintype.card_fin] at hfin
  have hle := hL.2 (Submodule.span ℝ (Set.range ![y, w])) (by
    intro u hu hne
    rw [Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨c, rfl⟩ := hu
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hne ⊢
    rw [key]
    have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
      by_contra hcc
      push Not at hcc
      apply hne
      rw [hcc.1, hcc.2]; simp
    rcases hc with hc | hc
    · nlinarith [mul_pos (mul_self_pos.2 hc) hy, mul_nonneg (mul_self_nonneg (c 1)) hw.le]
    · nlinarith [mul_pos (mul_self_pos.2 hc) hw, mul_nonneg (mul_self_nonneg (c 0)) hy.le])
  omega

/-- **Reverse Cauchy–Schwarz inequality**: if $\varphi[y] > 0$ (signature $(1, m-1)$) then
$\varphi[x]\,\varphi[y] \le \varphi(x, y)^2$ for all $x$. -/
theorem reverse_cs {Q : QuadraticForm ℝ U} (hL : IsLorentzian Q) {y : U} (hy : 0 < Q y) (x : U) :
    Q x * Q y ≤ bil Q x y ^ 2 := by
  obtain ⟨t, w, hx, hw0, ht⟩ := decomp_along Q x y hy
  have hQx : Q x = t * t * Q y + Q w := by
    rw [hx, Q_add Q, QuadraticMap.map_smul, bil_smul_left, bil_comm Q y w, hw0]
    ring
  have hwle := Q_nonpos_of_orth hL hy hw0
  rw [hQx, ← ht]
  nlinarith [mul_nonneg (neg_nonneg.2 hwle) hy.le]

/-- Real Cauchy–Schwarz for a positive semidefinite quadratic polynomial: if $R \ge 0$ and
$P - 2 l B + l^2 R \ge 0$ for all real $l$, then $B^2 \le P R$. -/
theorem cs_real {P R B : ℝ} (hR : 0 ≤ R) (h : ∀ l : ℝ, 0 ≤ P - 2 * l * B + l * l * R) :
    B ^ 2 ≤ P * R := by
  rcases hR.eq_or_lt with h0 | hpos
  · subst h0
    by_contra hlt
    push Not at hlt
    have hB : B ≠ 0 := by
      rintro rfl
      simp at hlt
    have e : 2 * ((P + 1) / (2 * B)) * B = P + 1 := by field_simp
    have := h ((P + 1) / (2 * B))
    nlinarith [e]
  · have := h (B / R)
    have e : P - 2 * (B / R) * B + B / R * (B / R) * R = P - B ^ 2 / R := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ hpos] at this
    exact this

/-- **Same time cone is transitive**: for $\varphi$ of signature $(1, m-1)$, if $\varphi[a], \varphi[b], \varphi[c] > 0$,
$\varphi(a, b) > 0$ and $\varphi(b, c) > 0$, then $\varphi(a, c) > 0$. -/
theorem bil_pos_trans {Q : QuadraticForm ℝ U} (hL : IsLorentzian Q) {a b c : U}
    (ha : 0 < Q a) (hb : 0 < Q b) (hc : 0 < Q c) (hab : 0 < bil Q a b) (hbc : 0 < bil Q b c) :
    0 < bil Q a c := by
  obtain ⟨s, a', ha', ha0, hs⟩ := decomp_along Q a b hb
  have hcb : 0 < bil Q c b := by rw [bil_comm Q]; exact hbc
  obtain ⟨t, c', hc', hc0, ht⟩ := decomp_along Q c b hb
  have hs0 : 0 < s := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hb.le]
  have ht0 : 0 < t := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (neg_nonneg.2 h) hb.le]
  have hQa : Q a = s * s * Q b + Q a' := by
    rw [ha', Q_add Q, QuadraticMap.map_smul, bil_smul_left, bil_comm Q b a', ha0]
    ring
  have hQc : Q c = t * t * Q b + Q c' := by
    rw [hc', Q_add Q, QuadraticMap.map_smul, bil_smul_left, bil_comm Q b c', hc0]
    ring
  have hac : bil Q a c = s * t * Q b + bil Q a' c' := by
    rw [ha', hc']
    simp only [bil_add_left Q, bil_add_right Q, bil_smul_left, bil_smul_right,
      bil_self Q]
    rw [bil_comm Q b c', hc0, ha0]
    ring
  have ha'le := Q_nonpos_of_orth hL hb ha0
  have hc'le := Q_nonpos_of_orth hL hb hc0
  have hcs : bil Q a' c' ^ 2 ≤ (-Q a') * (-Q c') := by
    apply cs_real (neg_nonneg.2 hc'le)
    intro l
    have horth : bil Q (a' + l • c') b = 0 := by
      rw [bil_add_left Q, bil_smul_left, ha0, hc0]; ring
    have hle := Q_nonpos_of_orth hL hb horth
    rw [Q_add Q, QuadraticMap.map_smul, bil_smul_right, smul_eq_mul] at hle
    nlinarith
  have hP : -Q a' < s * s * Q b := by linarith
  have hR : -Q c' < t * t * Q b := by linarith
  have hS : 0 < s * s * Q b := by positivity
  have hT : 0 < t * t * Q b := by positivity
  have hlt : bil Q a' c' ^ 2 < (s * t * Q b) ^ 2 := by
    have : (-Q a') * (-Q c') < (s * s * Q b) * (t * t * Q b) := by
      nlinarith [mul_nonneg (neg_nonneg.2 ha'le) (neg_nonneg.2 hc'le)]
    nlinarith
  have habs := abs_lt_of_sq_lt_sq hlt (by positivity)
  rw [hac]
  linarith [(abs_lt.1 habs).1]

/-- **Lemma 15.4** (Shimura 2004, p. 148), vector form, proved unconditionally: for $U$ finite-dimensional with
nondegenerate $\varphi$ of signature $(1, m-1)$, $\varphi[\varepsilon] > 0$ and $y \in D$, one has
$\varphi_{\mathbb C}[x + iy] \ne 0$ and $(\beta x - \alpha y)/(\alpha^2+\beta^2) \in D$ where
$\alpha + i\beta = \varphi_{\mathbb C}[x + iy]$. -/
@[kb "shimura2004" "Lemma 15.4, p. 148 (proof)"]
theorem lemma_15_4 : Lemma15_4 := by
  intro U _ _ _ Q _ hL ε hε x y hy
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Q x - Q y := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = 2 * bil Q x y := ⟨_, rfl⟩
  have hrcs := reverse_cs hL hy1 x
  have hN : 0 < α * α + β * β := by
    by_contra hle
    push Not at hle
    have h1 : α = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    have h2 : β = 0 := by nlinarith [mul_self_nonneg α, mul_self_nonneg β]
    have h3 : Q x = Q y := by linarith
    have h4 : bil Q x y = 0 := by linarith
    rw [h4, h3] at hrcs
    nlinarith [mul_pos hy1 hy1]
  have hns : Complex.normSq (complexValue Q x y) = α * α + β * β := by
    rw [Complex.normSq_apply]
    simp only [complexValue, hα, hβ]
  constructor
  · intro h0
    have := congrArg Complex.normSq h0
    rw [hns, map_zero] at this
    linarith
  · have himg : negInvIm Q x y = (α * α + β * β)⁻¹ • (β • x + (-α) • y) := by
      unfold negInvIm
      rw [hns]
      simp only [complexValue, hα, hβ, sub_eq_add_neg, neg_smul]
    have hw : Q (β • x + (-α) • y) = (α * α + β * β) * Q y := by
      rw [Q_comb, hα, hβ]; ring
    have hb : bil Q (β • x + (-α) • y) y = β * bil Q x y - α * Q y := by
      rw [bil_comb_left, bil_self Q]; ring
    have hpos : 0 < β * bil Q x y - α * Q y := by
      rw [hα, hβ]
      nlinarith [mul_pos hy1 hy1]
    have key : ∀ N : ℝ, 0 < N → 0 < N⁻¹ * N⁻¹ * (N * Q y) := by
      intro N hN; positivity
    have hQ' : 0 < Q ((α * α + β * β)⁻¹ • (β • x + (-α) • y)) := by
      rw [QuadraticMap.map_smul, hw]
      exact key _ hN
    have hb' : 0 < bil Q ((α * α + β * β)⁻¹ • (β • x + (-α) • y)) y := by
      rw [bil_smul_left, hb]
      positivity
    rw [himg]
    exact ⟨hQ', bil_pos_trans hL hQ' hy1 hε hb' hy2⟩

end QuadFormsKB.Shimura2004
