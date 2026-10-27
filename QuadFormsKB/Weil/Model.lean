/-
# The Weil representation from one-dimensional harmonic analysis

**Layer:** abstract harmonic analysis over a commutative ring $K$ (instantiated at the finite places in
`Weil/NonArch.lean`).

**Data** (`LocalData K`): an additive character $\psi : K \to \mathbb C^1$, a measure $\mu$ on $K$, a "modulus"
$|\cdot| = $ `md` (used on units), a "Weil constant" $\gamma = $ `γ` (used on units), a "Hilbert symbol"
$(\cdot,\cdot) = $ `hilb`, a space $S \subseteq \{K \to \mathbb C\}$ of test functions, and the unit $2 \in K^\times$. Notation:
$$\mathcal F f(y) = \int_K f(x)\,\psi(xy)\,d\mu(x)\ (\texttt{four}),\qquad
  e_s f(x) = \psi(sx^2)f(x)\ (\texttt{chirp}),\qquad D_t f(x) = f(tx)\ (\texttt{dil}).$$

**Axioms.** `IsOps` (enough to *define* the operators): $\mu$ is $\sigma$-finite, `md` is positive and multiplicative
on units, $f\psi(\cdot\,y)$ is integrable for $f \in S$, $S$ is stable under $e_s$, $D_t$ and $\mathcal F$, and `hilb` is
a symmetric bimultiplicative $\pm1$-valued symbol on units with $(b, -b) = 1$. `IsModel` (enough to prove the relations)
adds, for $f \in S$ and $t, b \in K^\times$:
* (I) Fourier inversion $\mathcal F\mathcal F f(x) = f(-x)$;
* (D) $\mathcal F(D_tf) = |t|^{-1}D_{t^{-1}}\mathcal Ff$;
* (W) **the Weil identity** $\mathcal F(e_b\,\mathcal Ff)(y) = \gamma(b)\,\psi(cy^2)\,\mathcal F(e_cf)(2cy)$, $c = -(4b)^{-1}$;
* (S) $\gamma(ts^2) = |s|^{-1}\gamma(t)$;
* (H) $\gamma(st)\gamma(1) = (s,t)\,\gamma(s)\gamma(t)$ (Weil's index and the Hilbert symbol);
* $S \ne 0$.

These are exactly what the repo proves at a finite place (`Analysis/WeilIndex*.lean`, `LocalFourierNF.lean`).

**Consequences in dimension one.** With the normalized constant $g(t) = \gamma(t)|2t|^{1/2}$ (`gN`):
`gN_mul_gN_neg`: $g(b)g(-b) = 1$, derived from (I), (D), (W) by composing the Weil identity for $b$ and $-b$ (no
evaluation of a Gauss sum); `gN_one_pow_four`: $g(1)^4 = (-1,-1)$; `gN_mul_sq`: $g(ts^2) = g(t)$.

**The quadratic space** (`a : Fin (2m) → Kˣ`): $V = K^{2m}$, $Q(x) = \sum_i a_ix_i^2$, $B(x,y) = \sum_i 2a_ix_iy_i$,
$n = 2m$ (0-based indices). The **quadratic character** $\chi_V(t) = (t, (-1)^m\det V)$, $\det V = \prod_i a_i$
(`chiV`), and the **Weil index** (`gammaV`)
$$\gamma_V = \chi_V(-1)\prod_{i<n} g(a_i)^{-1}.$$

**The operators** on functions $\Phi : K^n \to \mathbb C$ (Kudla, *Notes*, §I.1, Prop. 1.3 [unverified]; Weil 1964,
§14 [unverified]):
$$\omega(n(b))\Phi(x) = \psi(bQ(x))\Phi(x),\quad \omega(m(t))\Phi(x) = \chi_V(t)|t|^{m}\Phi(tx),\quad
  \omega(w)\Phi(y) = \gamma_V\int_{K^n}\Phi(x)\psi(B(x,y))\,d\mu_B(x),$$
with $d\mu_B = \prod_i|2a_i|^{1/2}d\mu(x_i)$ the measure self-dual for $\psi(B(x,y))$ (`opNf`, `opMf`, `opWf`).
They preserve $S(V) = \operatorname{span}\{x \mapsto \prod_if_i(x_i) : f_i \in S\}$ (`Sn`), satisfy the relations
(R1)–(R6) of `SL2Cells.lean` there (`sl2Relations`), and so define a representation
$$\omega : \mathrm{SL}_2(k) \to \operatorname{End}_{\mathbb C}S(V)$$
for every field $k$ with a ring map $k \to K$ (`weilRep`), with $\omega(n(b)), \omega(m(t)), \omega(w)$ as above
(`weilRep_nMat`, `weilRep_mMat`, `weilRep_wMat`).

The constant $\gamma_V$ is forced: (R5) $w^2 = m(-1)$ needs $\gamma_V^2 = \chi_V(-1)$ (`gammaV_sq`) and (R6) needs
$\gamma_V\prod_ig(a_ib) = \chi_V(-b)$ (`gammaV_mul_prod_gN`); both follow from (H), $g(b)g(-b) = 1$ and $g(1)^4 = (-1,-1)$.
In fact $\gamma_V = \prod_ig(a_i)$, **the Weil index of $V$** (`gammaV_eq_prod_gN`), so $\omega(w)\Phi = \gamma(\psi\circ Q)\hat\Phi$
with the kernel $\psi(+B(x,y))$; with the kernel $\psi(-B(x,y))$ (Kudla) the constants change accordingly.

Sources: Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), §§14, 26–28 [unverified];
Kudla, *Notes on the local theta correspondence* (1996), §I.1–I.3 [unverified]; Rao (1993), Thm. 3.6 [unverified];
Bump (1997), §4.8 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.SL2Cells

open MeasureTheory
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

/-- Equalities in a commutative group of units, via `Additive` and `abel`. -/
macro "units_eq" : tactic =>
  `(tactic| (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow, ofMul_zpow]; abel))

/-! ### Local data -/

/-- The dilation $D_tf(x) = f(tx)$. -/
def dil {K : Type*} [Mul K] (t : K) (f : K → ℂ) (x : K) : ℂ := f (t * x)

/-- **Local data for the Weil representation** over a commutative ring $K$ (one variable):
* `ψ`: an additive character $K \to \mathbb C^1$;
* `μ`: a measure on $K$ (the self-dual Haar measure, in the instances);
* `md`: the modulus $|t|$ (only its values on units are used);
* `γ`: the Weil constant $\gamma(t)$, i.e. the (regularized) Gauss integral $\int\psi(tx^2)\,d\mu(x)$ (units only);
* `hilb`: the Hilbert symbol $(s,t)$ (units only);
* `S`: the space of test functions (Schwartz–Bruhat functions, in the instances);
* `two`: $2$ as a unit of $K$ (`two_eq`). -/
@[kb "weil1964" "§14 (local data: $\\psi$, self-dual measure, $\\mathcal S$) [unverified]"]
structure LocalData (K : Type*) [CommRing K] [MeasurableSpace K] where
  ψ : AddChar K Circle
  μ : Measure K
  md : K → ℝ
  γ : K → ℂ
  hilb : K → K → ℤ
  S : Submodule ℂ (K → ℂ)
  two : Kˣ
  two_eq : (two : K) = 2

namespace LocalData

variable {K : Type*} [CommRing K] [MeasurableSpace K] (D : LocalData K)

/-- The Fourier transform $\mathcal Ff(y) = \int_K f(x)\psi(xy)\,d\mu(x)$. -/
def four (f : K → ℂ) (y : K) : ℂ := ∫ x, f x * (D.ψ (x * y) : ℂ) ∂D.μ

/-- The chirp $e_sf(x) = \psi(sx^2)f(x)$. -/
def chirp (s : K) (f : K → ℂ) (x : K) : ℂ := (D.ψ (s * x ^ 2) : ℂ) * f x

/-- The constant $c = -(4b)^{-1}$ of the Weil identity. -/
def cW (b : Kˣ) : Kˣ := -(D.two * D.two * b)⁻¹

/-- **Axioms that define the operators** (closure of $S$; Hilbert symbol on units):
* `sigmaFinite`: $\mu$ is $\sigma$-finite;
* `md_pos`, `md_mul`: $|t| > 0$ and $|st| = |s||t|$ on units;
* `integrable_char`: $x \mapsto f(x)\psi(xy)$ is $\mu$-integrable for $f \in S$;
* `chirp_mem`, `dil_mem`, `four_mem`: $S$ is stable under $e_s$, $D_t$ ($t$ a unit) and $\mathcal F$;
* `hilb_pm`, `hilb_comm`, `hilb_mul_left`, `hilb_neg`: $(s,t) = \pm1$, $(s,t) = (t,s)$, $(ss',t) = (s,t)(s',t)$,
  $(s,-s) = 1$ on units. -/
structure IsOps : Prop where
  sigmaFinite : SigmaFinite D.μ
  md_pos : ∀ t : Kˣ, 0 < D.md t
  md_mul : ∀ s t : Kˣ, D.md ((s : K) * t) = D.md s * D.md t
  integrable_char : ∀ f ∈ D.S, ∀ y : K, Integrable (fun x => f x * (D.ψ (x * y) : ℂ)) D.μ
  chirp_mem : ∀ f ∈ D.S, ∀ s : K, D.chirp s f ∈ D.S
  dil_mem : ∀ f ∈ D.S, ∀ t : Kˣ, dil (t : K) f ∈ D.S
  four_mem : ∀ f ∈ D.S, D.four f ∈ D.S
  hilb_pm : ∀ s t : Kˣ, D.hilb s t = 1 ∨ D.hilb s t = -1
  hilb_comm : ∀ s t : Kˣ, D.hilb s t = D.hilb t s
  hilb_mul_left : ∀ s s' t : Kˣ, D.hilb ((s : K) * s') t = D.hilb s t * D.hilb s' t
  hilb_neg : ∀ s : Kˣ, D.hilb s (-(s : K)) = 1

/-- **Axioms that give the relations** (on top of `IsOps`), for $f \in S$ and units $t, b, s$:
* `inversion`: $\mathcal F\mathcal Ff(x) = f(-x)$;
* `four_dil`: $\mathcal F(D_tf)(y) = |t|^{-1}\mathcal Ff(t^{-1}y)$;
* `weil`: $\mathcal F(e_b\mathcal Ff)(y) = \gamma(b)\psi(cy^2)\mathcal F(e_cf)(2cy)$ with $c = -(4b)^{-1}$ (`cW`);
* `γ_sq`: $\gamma(ts^2) = |s|^{-1}\gamma(t)$;
* `weil_hilb`: $\gamma(st)\gamma(1) = (s,t)\gamma(s)\gamma(t)$;
* `nontrivial`: $S \ne 0$. -/
structure IsModel : Prop extends IsOps D where
  inversion : ∀ f ∈ D.S, ∀ x : K, D.four (D.four f) x = f (-x)
  four_dil : ∀ f ∈ D.S, ∀ (t : Kˣ) (y : K), D.four (dil (t : K) f) y = (D.md t : ℂ)⁻¹ * D.four f (↑t⁻¹ * y)
  weil : ∀ f ∈ D.S, ∀ (b : Kˣ) (y : K), D.four (D.chirp b (D.four f)) y =
    D.γ b * (D.ψ (D.cW b * y ^ 2) : ℂ) * D.four (D.chirp (D.cW b) f) (2 * D.cW b * y)
  γ_sq : ∀ t s : Kˣ, D.γ ((t : K) * (s : K) ^ 2) = (D.md s : ℂ)⁻¹ * D.γ t
  weil_hilb : ∀ s t : Kˣ, D.γ ((s : K) * t) * D.γ 1 = (D.hilb s t : ℂ) * D.γ s * D.γ t
  nontrivial : ∃ f ∈ D.S, f ≠ 0

variable {D}

/-! ### Elementary identities for $e_s$, $D_t$, $\mathcal F$ -/

lemma four_smul (c : ℂ) (f : K → ℂ) : D.four (c • f) = c • D.four f := by
  ext y; simp only [four, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

lemma chirp_smul (s : K) (c : ℂ) (f : K → ℂ) : D.chirp s (c • f) = c • D.chirp s f := by
  ext x; simp only [chirp, Pi.smul_apply, smul_eq_mul]; ring

lemma dil_smul (t : K) (c : ℂ) (f : K → ℂ) : dil t (c • f) = c • dil t f := rfl

lemma chirp_chirp (s s' : K) (f : K → ℂ) : D.chirp s (D.chirp s' f) = D.chirp (s + s') f := by
  ext x; simp only [chirp, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]; ring

lemma chirp_zero (f : K → ℂ) : D.chirp 0 f = f := by
  ext x; simp [chirp]

lemma dil_dil (s t : K) (f : K → ℂ) : dil s (dil t f) = dil (t * s) f := by
  ext x; simp only [dil, mul_assoc]

lemma dil_one (f : K → ℂ) : dil 1 f = f := by ext x; simp [dil]

/-- $e_{s}D_t = D_te_{s'}$ when $s = s't^2$. -/
lemma chirp_dil {s s' t : K} (h : s = s' * t ^ 2) (f : K → ℂ) :
    D.chirp s (dil t f) = dil t (D.chirp s' f) := by
  ext x; simp only [chirp, dil, h]; congr 3; ring

lemma chirp_dil_neg_one (s : K) (f : K → ℂ) : D.chirp s (dil (-1) f) = dil (-1) (D.chirp s f) :=
  chirp_dil (by ring) f

/-! ### Consequences of the axioms in one variable -/

section OneDim

variable (hD : D.IsModel)
include hD

lemma md_one : D.md 1 = 1 := by
  have h := hD.md_mul 1 1
  have hp := hD.md_pos 1
  simp only [Units.val_one, mul_one] at h hp
  have : D.md 1 * (D.md 1 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0 <;> [linarith; linarith]

lemma md_inv (t : Kˣ) : D.md (↑t⁻¹ : K) = (D.md t)⁻¹ := by
  have h := hD.md_mul t t⁻¹
  rw [Units.mul_inv, md_one hD] at h
  have := hD.md_pos t
  field_simp
  linarith

lemma md_neg_one : D.md (-1 : K) = 1 := by
  have h := hD.md_mul (-1) (-1)
  have hp := hD.md_pos (-1)
  simp only [Units.val_neg, Units.val_one, neg_mul_neg, mul_one, md_one hD] at h hp
  nlinarith

lemma md_neg (t : Kˣ) : D.md (-(t : K)) = D.md t := by
  have h := hD.md_mul (-1) t
  simp only [Units.val_neg, Units.val_one, neg_one_mul, md_neg_one hD, one_mul] at h
  exact h

lemma four_dil_fun {f : K → ℂ} (hf : f ∈ D.S) (t : Kˣ) :
    D.four (dil (t : K) f) = ((D.md t : ℂ)⁻¹) • dil (↑t⁻¹) (D.four f) := by
  ext y; rw [hD.four_dil f hf t y]; rfl

/-- $\mathcal F\mathcal F = D_{-1}$ on $S$. -/
lemma four_four_fun {f : K → ℂ} (hf : f ∈ D.S) : D.four (D.four f) = dil (-1) f := by
  ext x; rw [hD.inversion f hf x]; simp [dil]

lemma four_dil_neg_one {f : K → ℂ} (hf : f ∈ D.S) : D.four (dil (-1) f) = dil (-1) (D.four f) := by
  have := four_dil_fun hD hf (-1)
  rw [show ((-1 : Kˣ) : K) = -1 by simp] at this
  rw [this, md_neg_one hD]
  simp

/-- **$g(b)g(-b) = 1$, unnormalized form:** $\gamma(b)\gamma(-b)|2b| = 1$. *Proof:* compose the Weil identities for
$b$ and $-b$ on a nonzero $f \in S$: $\mathcal Fe_b\mathcal F\,\mathcal Fe_{-b}\mathcal F = \mathcal Fe_bD_{-1}e_{-b}\mathcal F
= D_{-1}\mathcal F\mathcal F = \mathrm{id}$ by (I), while the Weil identity (twice) and (D) give
$\gamma(b)\gamma(-b)|2c|^{-1}\,\mathrm{id}$ with $|2c| = |2b|^{-1}$. -/
theorem γ_mul_γ_neg_mul_md (b : Kˣ) : D.γ b * D.γ (-(b : K)) * D.md ((D.two : K) * b) = 1 := by
  obtain ⟨f, hf, hf0⟩ := hD.nontrivial
  have hc' : ((D.cW (-b) : Kˣ) : K) = -((D.cW b : Kˣ) : K) := by
    simp only [cW, mul_neg, inv_neg, neg_neg, Units.val_neg]
  have hnegb : (((-b : Kˣ)) : K) = -(b : K) := by simp
  have h4 : D.four f ∈ D.S := hD.four_mem f hf
  have hh : D.chirp (-(b : K)) (D.four f) ∈ D.S := hD.chirp_mem _ h4 _
  have hg : D.four (D.chirp (-(b : K)) (D.four f)) ∈ D.S := hD.four_mem _ hh
  set g := D.four (D.chirp (-(b : K)) (D.four f)) with hg_def
  -- way A: the composite is the identity
  have hA : D.four (D.chirp b (D.four g)) = f := by
    rw [hg_def, four_four_fun hD hh, chirp_dil_neg_one, chirp_chirp, add_neg_cancel, chirp_zero,
      four_dil_neg_one hD h4, four_four_fun hD hf, dil_dil]
    norm_num [dil_one]
  -- way B: two Weil identities
  have hW : ∀ (u : Kˣ) {φ : K → ℂ}, φ ∈ D.S → D.four (D.chirp u (D.four φ)) =
      (D.γ u) • D.chirp (D.cW u) (dil (2 * (D.cW u : K)) (D.four (D.chirp (D.cW u) φ))) := by
    intro u φ hφ
    ext y; rw [hD.weil φ hφ u y]; simp only [Pi.smul_apply, smul_eq_mul, chirp, dil]; ring
  have hg' : g = (D.γ (-(b : K))) • D.chirp (-(D.cW b : K))
      (dil (2 * -(D.cW b : K)) (D.four (D.chirp (-(D.cW b : K)) f))) := by
    rw [hg_def, ← hnegb, hW (-b) hf, hc', hnegb]
  have hF₁ : D.four (D.chirp (-(D.cW b : K)) f) ∈ D.S := hD.four_mem _ (hD.chirp_mem _ hf _)
  set u : Kˣ := D.two * (-(D.cW b)) with hu
  have hu' : (u : K) = 2 * -(D.cW b : K) := by rw [hu, Units.val_mul, D.two_eq, Units.val_neg]
  have hB : D.four (D.chirp b (D.four g)) =
      (D.γ b * D.γ (-(b : K)) * (D.md u : ℂ)⁻¹) • f := by
    rw [hW b hg, hg', chirp_smul, chirp_chirp, add_neg_cancel, chirp_zero, four_smul, ← hu',
      four_dil_fun hD hF₁ u, four_four_fun hD (hD.chirp_mem _ hf _)]
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, chirp, dil]
    have hy : -1 * ((↑u⁻¹ : K) * (2 * (D.cW b : K) * y)) = y := by
      have : (u : K) * ↑u⁻¹ = 1 := by simp
      rw [hu'] at this
      linear_combination y * this
    rw [hy]
    have hψ : (D.ψ ((D.cW b : K) * y ^ 2) : ℂ) * (D.ψ (-(D.cW b : K) * y ^ 2) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_mul, add_neg_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one]
    linear_combination (D.γ b * D.γ (-(b : K)) * (D.md u : ℂ)⁻¹ * f y) * hψ
  -- compare
  have hC : D.γ b * D.γ (-(b : K)) * (D.md u : ℂ)⁻¹ = 1 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hf0
    have := congrFun (hA.symm.trans hB) x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hx
    have h' : (D.γ b * D.γ (-(b : K)) * (D.md u : ℂ)⁻¹ - 1) * f x = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h0 | h0
    · linear_combination h0
    · exact absurd h0 hx
  have hu2 : u = (D.two * b)⁻¹ := by
    rw [hu, cW, neg_neg]; simp only [mul_inv]; group
  have hmd : D.md u = (D.md ((D.two : K) * b))⁻¹ := by
    rw [hu2, md_inv hD, Units.val_mul]
  rw [hmd] at hC
  have hpos := hD.md_pos (D.two * b)
  rw [Units.val_mul] at hpos
  have hne : (D.md ((D.two : K) * b) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [Complex.ofReal_inv, inv_inv] at hC
  exact_mod_cast hC


/-! ### The normalized Weil constant $g(t) = \gamma(t)|2t|^{1/2}$ -/

lemma sqrt_md_mul (s t : Kˣ) :
    (Real.sqrt (D.md ((s : K) * t)) : ℂ) = Real.sqrt (D.md s) * Real.sqrt (D.md t) := by
  rw [hD.md_mul, Real.sqrt_mul (hD.md_pos s).le]; push_cast; ring

lemma sqrt_md_unit_mul (s t : Kˣ) :
    (Real.sqrt (D.md ((s * t : Kˣ) : K)) : ℂ) = Real.sqrt (D.md s) * Real.sqrt (D.md t) := by
  rw [Units.val_mul, sqrt_md_mul hD]

lemma md_two_mul (t : Kˣ) : D.md (2 * (t : K)) = D.md D.two * D.md t := by
  rw [← D.two_eq, hD.md_mul]

end OneDim

/-- **The normalized Weil constant** $g(t) = \gamma(t)\,|2t|^{1/2}$ (of unit modulus in the instances; here only
$g(b)g(-b) = 1$ is used, `gN_mul_gN_neg`). -/
def gN (t : K) : ℂ := D.γ t * (Real.sqrt (D.md (2 * t)) : ℂ)

/-- The Hilbert symbol as a complex number. -/
def hC (s t : K) : ℂ := (D.hilb s t : ℂ)

section OneDim'

variable (hD : D.IsModel)
include hD

lemma hC_sq (s t : Kˣ) : D.hC s t * D.hC s t = 1 := by
  rcases hD.hilb_pm s t with h | h <;> simp [hC, h]

lemma hC_mul_left (s s' t : Kˣ) : D.hC ((s : K) * s') t = D.hC s t * D.hC s' t := by
  simp [hC, hD.hilb_mul_left]

lemma hC_comm (s t : Kˣ) : D.hC s t = D.hC t s := by simp [hC, hD.hilb_comm]

lemma hC_mul_right (s t t' : Kˣ) : D.hC s ((t : K) * t') = D.hC s t * D.hC s t' := by
  rw [show ((t : K) * t') = ((t * t' : Kˣ) : K) by simp, hC_comm hD, Units.val_mul,
    hC_mul_left hD, hC_comm hD t, hC_comm hD t']

lemma hC_one_left (t : Kˣ) : D.hC 1 t = 1 := by
  have h := hC_mul_left hD 1 1 t
  simp only [Units.val_one, mul_one] at h
  have h2 := hC_sq hD 1 t
  simp only [Units.val_one] at h2
  calc D.hC 1 t = D.hC 1 t * (D.hC 1 t * D.hC 1 t) := by rw [h2, mul_one]
    _ = 1 := by rw [← h, h2]

lemma hC_self (t : Kˣ) : D.hC t t = D.hC t (-1) := by
  have h := hC_mul_right hD t (-1) (-t)
  have hn := hD.hilb_neg t
  simp only [Units.val_neg, Units.val_one, neg_one_mul, neg_neg] at h
  rw [h, show D.hC t (-(t : K)) = 1 by simp [hC, hn], mul_one]

lemma hC_prod_left {ι : Type*} (s : Finset ι) (u : ι → Kˣ) (t : Kˣ) :
    D.hC ((∏ i ∈ s, u i : Kˣ) : K) t = ∏ i ∈ s, D.hC (u i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hC_one_left hD]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, Units.val_mul, hC_mul_left hD, ih]

lemma hC_pow_left (u t : Kˣ) (m : ℕ) : D.hC ((u ^ m : Kˣ) : K) t = D.hC u t ^ m := by
  have := hC_prod_left hD (Finset.range m) (fun _ => u) t
  simpa [Finset.prod_const] using this

lemma gN_mul_gN_neg (b : Kˣ) : D.gN b * D.gN (-(b : K)) = 1 := by
  have h := γ_mul_γ_neg_mul_md hD b
  have hpos := hD.md_pos (D.two * b)
  rw [Units.val_mul, D.two_eq] at hpos
  have hneg : D.md (2 * -(b : K)) = D.md (2 * (b : K)) := by
    rw [mul_neg, show (2 : K) * b = ((D.two * b : Kˣ) : K) by simp [D.two_eq], md_neg hD]
  unfold gN
  rw [hneg, D.two_eq] at *
  have hs : (Real.sqrt (D.md (2 * (b : K))) : ℂ) * Real.sqrt (D.md (2 * (b : K))) = D.md (2 * (b : K)) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
  linear_combination h + (D.γ b * D.γ (-(b : K))) * hs

lemma gN_ne_zero (b : Kˣ) : D.gN b ≠ 0 := by
  intro h; have := gN_mul_gN_neg hD b; rw [h, zero_mul] at this; exact zero_ne_one this

lemma gN_mul (s t : Kˣ) : D.gN ((s : K) * t) * D.gN 1 = D.hC s t * D.gN s * D.gN t := by
  unfold gN hC
  have h := hD.weil_hilb s t
  have e1 : (Real.sqrt (D.md (2 * ((s : K) * t))) : ℂ) * Real.sqrt (D.md (2 * 1)) =
      Real.sqrt (D.md (2 * (s : K))) * Real.sqrt (D.md (2 * (t : K))) := by
    have a1 : (2 : K) * ((s : K) * t) = ((D.two * s * t : Kˣ) : K) := by simp [D.two_eq, mul_assoc]
    have a2 : (2 : K) * 1 = ((D.two : Kˣ) : K) := by simp [D.two_eq]
    have a3 : (2 : K) * s = ((D.two * s : Kˣ) : K) := by simp [D.two_eq]
    have a4 : (2 : K) * t = ((D.two * t : Kˣ) : K) := by simp [D.two_eq]
    rw [a1, a2, a3, a4]
    simp only [sqrt_md_unit_mul hD]
    ring
  calc D.γ ((s : K) * t) * (Real.sqrt (D.md (2 * ((s : K) * t))) : ℂ) * (D.γ 1 * Real.sqrt (D.md (2 * 1)))
      = (D.γ ((s : K) * t) * D.γ 1) * ((Real.sqrt (D.md (2 * ((s : K) * t))) : ℂ) *
          Real.sqrt (D.md (2 * 1))) := by ring
    _ = _ := by rw [h, e1]; ring

lemma gN_mul_sq (t s : Kˣ) : D.gN ((t : K) * (s : K) ^ 2) = D.gN t := by
  unfold gN
  rw [hD.γ_sq]
  have hs := hD.md_pos s
  have e : (Real.sqrt (D.md (2 * ((t : K) * (s : K) ^ 2))) : ℂ) =
      Real.sqrt (D.md (2 * (t : K))) * D.md s := by
    have a1 : (2 : K) * ((t : K) * (s : K) ^ 2) = ((D.two * t * (s * s) : Kˣ) : K) := by
      simp [D.two_eq, mul_assoc, sq]
    have a2 : (2 : K) * t = ((D.two * t : Kˣ) : K) := by simp [D.two_eq]
    rw [a1, a2]
    simp only [sqrt_md_unit_mul hD]
    have : (Real.sqrt (D.md s) : ℂ) * Real.sqrt (D.md s) = D.md s := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hs.le]
    linear_combination (↑√(D.md ↑D.two) * ↑√(D.md ↑t) : ℂ) * this
  rw [e]
  have : (D.md s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

lemma gN_one_mul_neg_one : D.gN 1 * D.gN (-1) = 1 := by
  simpa using gN_mul_gN_neg hD 1

lemma gN_one_pow_four : D.gN 1 ^ 4 = D.hC (-1) (-1) := by
  have h := gN_mul hD (-1) (-1)
  simp only [Units.val_neg, Units.val_one, neg_mul_neg, mul_one] at h
  have h1 := gN_one_mul_neg_one hD
  have hs := hC_sq hD (-1) (-1)
  simp only [Units.val_neg, Units.val_one] at hs
  -- `g(1)^2 = h g(-1)^2` and `g(1) g(-1) = 1`
  linear_combination (D.gN 1 ^ 2) * h + (D.hC (-1) (-1) * (D.gN 1 * D.gN (-1) + 1)) * h1

lemma gN_sq (t : Kˣ) : D.gN t * D.gN t = D.hC t (-1) * (D.gN 1 * D.gN 1) := by
  have h := gN_mul hD t t
  have h1 := gN_mul_sq hD 1 t
  simp only [Units.val_one, one_mul] at h1
  rw [← sq, h1, hC_self hD] at h
  have hs := hC_sq hD t (-1)
  simp only [Units.val_neg, Units.val_one] at hs
  linear_combination (-D.hC t (-1)) * h - (D.gN t * D.gN t) * hs

end OneDim'



/-! ### The one-variable transforms $F_\alpha = |2\alpha|^{1/2}D_{2\alpha}\mathcal F$ -/

/-- The Fourier transform for the pairing $\psi(2\alpha xy)$ of the form $\langle\alpha\rangle$, with the self-dual
measure $|2\alpha|^{1/2}d\mu$: $F_\alpha f(y) = |2\alpha|^{1/2}\,\mathcal Ff(2\alpha y)$. -/
def Fa (α : K) (f : K → ℂ) : K → ℂ := (Real.sqrt (D.md (2 * α)) : ℂ) • dil (2 * α) (D.four f)

lemma Fa_smul (α : K) (c : ℂ) (f : K → ℂ) : D.Fa α (c • f) = c • D.Fa α f := by
  unfold Fa; rw [four_smul, dil_smul, smul_comm]

lemma Fa_mem (hD : D.IsOps) {f : K → ℂ} (hf : f ∈ D.S) (α : Kˣ) : D.Fa α f ∈ D.S := by
  unfold Fa
  have : dil (2 * (α : K)) (D.four f) ∈ D.S := by
    have h := hD.dil_mem _ (hD.four_mem f hf) (D.two * α)
    rwa [Units.val_mul, D.two_eq] at h
  exact D.S.smul_mem _ this

section OneDimFa

variable (hD : D.IsModel)
include hD

/-- $F_\alpha D_t = |t|^{-1}D_{t^{-1}}F_\alpha$ on $S$. -/
lemma Fa_dil {f : K → ℂ} (hf : f ∈ D.S) (α t : Kˣ) :
    D.Fa α (dil (t : K) f) = ((D.md t : ℂ)⁻¹) • dil (↑t⁻¹ : K) (D.Fa α f) := by
  unfold Fa
  rw [four_dil_fun hD hf, dil_smul, dil_smul, dil_dil, dil_dil, smul_smul, smul_smul, mul_comm (2 * (α : K)),
    mul_comm (Real.sqrt _ : ℂ)]

/-- $F_\alpha F_\alpha = D_{-1}$ on $S$ (Fourier inversion for the self-dual measure of $\langle\alpha\rangle$). -/
lemma Fa_Fa {f : K → ℂ} (hf : f ∈ D.S) (α : Kˣ) : D.Fa α (D.Fa α f) = dil (-1) f := by
  have h2α : (2 * (α : K)) = ((D.two * α : Kˣ) : K) := by simp [D.two_eq]
  have hpos := hD.md_pos (D.two * α)
  conv_lhs => rw [Fa, Fa, four_smul, dil_smul, h2α, four_dil_fun hD (hD.four_mem f hf),
    four_four_fun hD hf, dil_smul, dil_dil, dil_dil, smul_smul, smul_smul]
  rw [← h2α] at hpos ⊢
  have hx : (-1 : K) * (↑(D.two * α)⁻¹ * (2 * (α : K))) = -1 := by
    rw [h2α, Units.inv_mul, mul_one]
  rw [hx]
  have : (Real.sqrt (D.md (2 * (α : K))) : ℂ) * Real.sqrt (D.md (2 * (α : K))) * (D.md (2 * (α : K)) : ℂ)⁻¹
      = 1 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
    have : (D.md (2 * (α : K)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp
  rw [this, one_smul]

/-- **The Bruhat relation in one variable:** for $f \in S$ and units $\alpha, b$,
$$F_\alpha\big(e_{\alpha b}F_\alpha f\big) = \frac{g(\alpha b)}{|b|^{1/2}}\;e_{c}\,D_{-b^{-1}}F_\alpha(e_cf),\qquad c = -\alpha b^{-1}.$$
This is the Weil identity (W) for $\beta = b/(4\alpha)$, transported by $D_{2\alpha}$, with
$\gamma(\beta) = g(\alpha b)\,|2\alpha|^{1/2}|b|^{-1/2}$ from (S). -/
lemma Fa_chirp_Fa {f : K → ℂ} (hf : f ∈ D.S) (α b : Kˣ) :
    D.Fa α (D.chirp ((α : K) * b) (D.Fa α f)) =
      (D.gN ((α : K) * b) * ((Real.sqrt (D.md b) : ℂ))⁻¹) •
        D.chirp (-((α : K) * ↑b⁻¹)) (dil (-(↑b⁻¹ : K)) (D.Fa α (D.chirp (-((α : K) * ↑b⁻¹)) f))) := by
  set u : Kˣ := D.two * α with hu
  have h2α : (2 * (α : K)) = (u : K) := by simp [hu, D.two_eq]
  set β : Kˣ := b * (D.two * D.two * α)⁻¹ with hβ
  have hcβ : ((D.cW β : Kˣ) : K) = -((α : K) * ↑b⁻¹) := by
    have : D.cW β = -(α * b⁻¹) := by
      rw [cW, hβ]; congr 1; units_eq
    rw [this]; simp
  have hupos := hD.md_pos u
  -- the left side is `𝓕 e_β 𝓕 f`
  have hL : D.Fa α (D.chirp ((α : K) * b) (D.Fa α f)) = D.four (D.chirp β (D.four f)) := by
    have hcd : D.chirp ((α : K) * b) (dil (u : K) (D.four f)) = dil (u : K) (D.chirp β (D.four f)) := by
      refine chirp_dil ?_ _
      rw [hβ, hu]
      simp only [Units.val_mul, D.two_eq]
      have h2 : (2 : K) * 2 * (α : K) * ↑(D.two * D.two * α)⁻¹ = 1 := by
        rw [show (2 : K) * 2 * (α : K) = ((D.two * D.two * α : Kˣ) : K) by simp [D.two_eq], Units.mul_inv]
      linear_combination (-(α : K) * b) * h2
    unfold Fa
    rw [h2α, chirp_smul, hcd, four_smul, dil_smul,
      four_dil_fun hD (hD.chirp_mem _ (hD.four_mem f hf) _), dil_smul, dil_dil, smul_smul, smul_smul]
    have hx : (↑u⁻¹ : K) * (u : K) = 1 := by simp
    rw [hx, dil_one]
    have : (Real.sqrt (D.md u) : ℂ) * Real.sqrt (D.md u) * (D.md u : ℂ)⁻¹ = 1 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hupos.le]
      have : (D.md u : ℂ) ≠ 0 := by exact_mod_cast hupos.ne'
      field_simp
    rw [this, one_smul]
  rw [hL]
  ext y
  rw [hD.weil f hf β y, hcβ]
  simp only [Pi.smul_apply, smul_eq_mul, chirp, dil, Fa]
  -- constants: `γ(β) = g(αb) |2α|^{1/2} |b|^{-1/2}`
  have hg : D.gN β = D.gN ((α : K) * b) := by
    have := gN_mul_sq hD (α * b) (D.two * α)⁻¹
    rw [← Units.val_mul, ← this, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 2
    rw [hβ]; units_eq
  have hmd : D.md (2 * (β : K)) * D.md (u : K) = D.md b := by
    rw [show (2 * (β : K)) = ((D.two * β : Kˣ) : K) by simp [D.two_eq], ← hD.md_mul, ← Units.val_mul]
    congr 2
    rw [hβ, hu]; units_eq
  have hβpos := hD.md_pos (D.two * β)
  rw [Units.val_mul, D.two_eq] at hβpos
  have hbpos := hD.md_pos b
  have hγ : D.γ β = D.gN ((α : K) * b) * Real.sqrt (D.md u) * ((Real.sqrt (D.md b) : ℂ))⁻¹ := by
    rw [← hg, gN]
    have hs : (Real.sqrt (D.md b) : ℂ) = Real.sqrt (D.md (2 * (β : K))) * Real.sqrt (D.md u) := by
      rw [← hmd, Real.sqrt_mul hβpos.le]; push_cast; ring
    rw [hs]
    have h1 : (Real.sqrt (D.md (2 * (β : K))) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hβpos).ne'
    have h2 : (Real.sqrt (D.md u) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hupos).ne'
    field_simp
  rw [hγ, h2α]
  have hy : (2 : K) * -((α : K) * ↑b⁻¹) * y = (u : K) * (-(↑b⁻¹ : K) * y) := by rw [← h2α]; ring
  rw [hy]
  have h3 : (Real.sqrt (D.md b) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hbpos).ne'
  field_simp

end OneDimFa

/-! ### Pure tensors -/

/-- **Pure tensors** $\bigotimes_if_i : x \mapsto \prod_{i<n}f_i(x_i)$ on $K^n$. -/
def ptensor {n : ℕ} (f : Fin n → K → ℂ) (x : Fin n → K) : ℂ := ∏ i, f i (x i)

lemma ptensor_smul_fun {n : ℕ} (c : Fin n → ℂ) (f : Fin n → K → ℂ) :
    ptensor (fun i => c i • f i) = (∏ i, c i) • ptensor f := by
  ext x; simp only [ptensor, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- **The Schwartz space of $V = K^n$** spanned by pure tensors of test functions:
$S(V) = \operatorname{span}_{\mathbb C}\{\bigotimes_if_i : f_i \in S\}$. (At a finite place this is every locally constant
compactly supported function; at the archimedean places it is the algebraic tensor product, dense in the Schwartz
space.) -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$) [unverified]"]
def Sn (n : ℕ) : Submodule ℂ ((Fin n → K) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f : Fin n → K → ℂ, (∀ i, f i ∈ D.S) ∧ Φ = ptensor f}

lemma ptensor_mem_Sn {n : ℕ} {f : Fin n → K → ℂ} (hf : ∀ i, f i ∈ D.S) : ptensor f ∈ D.Sn n :=
  Submodule.subset_span ⟨f, hf, rfl⟩

end LocalData

/-! ### The quadratic space $V = K^{2m}$, $Q = \sum_ia_ix_i^2$ -/

/-- The diagonal quadratic form $Q(x) = \sum_{i<n}a_ix_i^2$. -/
def Qform {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → Kˣ) (x : Fin n → K) : K := ∑ i, (a i : K) * x i ^ 2

/-- Its bilinear form $B(x,y) = Q(x+y) - Q(x) - Q(y) = \sum_{i<n}2a_ix_iy_i$. -/
def Bform {K : Type*} [CommRing K] {n : ℕ} (a : Fin n → Kˣ) (x y : Fin n → K) : K :=
  ∑ i, 2 * (a i : K) * x i * y i

/-- The discriminant $(-1)^m\det V = (-1)^m\prod_{i<2m}a_i$ of $V = \langle a_0, \dots, a_{2m-1}\rangle$. -/
def discV {K : Type*} [CommRing K] {m : ℕ} (a : Fin (2 * m) → Kˣ) : Kˣ := (-1) ^ m * ∏ i, a i

namespace LocalData

variable {K : Type*} [CommRing K] [MeasurableSpace K] (D : LocalData K) {m : ℕ} (a : Fin (2 * m) → Kˣ)

/-- **The quadratic character of $V$:** $\chi_V(t) = (t, (-1)^m\det V)$. -/
@[kb "kudla1996" "§I.1, (1.4) ($\\chi_V(x) = (x, (-1)^m\\det V)$) [unverified]"]
def chiV (t : K) : ℂ := D.hC t (discV a)

/-- **The Weil index of $V$:** $\gamma_V = \chi_V(-1)\prod_{i<2m}g(a_i)^{-1}$, $g(t) = \gamma(t)|2t|^{1/2}$ the normalized
Weil constant of $x \mapsto \psi(tx^2)$. It is forced by the relations (`gammaV_sq`, `gammaV_mul_prod_gN`). -/
@[kb "weil1964" "§14, Thm. 2 and §26 (the index $\\gamma(f)$ of a character of second degree) [unverified]"]
def gammaV : ℂ := D.chiV a (-1) * (∏ i, D.gN (a i))⁻¹

/-- The normalizing constant $\prod_i|2a_i|^{1/2}$ of the measure on $V$ self-dual for $\psi(B(x,y))$. -/
def cB : ℂ := ∏ i, (Real.sqrt (D.md (2 * (a i : K))) : ℂ)

/-- The product measure $\mu^{\otimes n}$ on $K^n$. -/
def muN (n : ℕ) : Measure (Fin n → K) := Measure.pi fun _ => D.μ

/-- **$\omega(n(b))$:** $\Phi(x) \mapsto \psi(bQ(x))\Phi(x)$. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(n(b))$) [unverified]"]
def opNf (b : K) (Φ : (Fin (2 * m) → K) → ℂ) (x : Fin (2 * m) → K) : ℂ :=
  (D.ψ (b * Qform a x) : ℂ) * Φ x

/-- **$\omega(m(t))$:** $\Phi(x) \mapsto \chi_V(t)|t|^{m}\Phi(tx)$ ($|t|^{n/2}$ with $n = 2m$). -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(m(a))$) [unverified]"]
def opMf (t : K) (Φ : (Fin (2 * m) → K) → ℂ) (x : Fin (2 * m) → K) : ℂ :=
  D.chiV a t * (D.md t : ℂ) ^ m * Φ (fun i => t * x i)

/-- **$\omega(w)$:** $\Phi \mapsto \gamma_V\hat\Phi$, $\hat\Phi(y) = \int_V\Phi(x)\psi(B(x,y))\,d\mu_B(x)$,
$d\mu_B = \prod_i|2a_i|^{1/2}\,d\mu(x_i)$. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(w)$) [unverified]"]
def opWf (Φ : (Fin (2 * m) → K) → ℂ) (y : Fin (2 * m) → K) : ℂ :=
  D.gammaV a * D.cB a * ∫ x, Φ x * (D.ψ (Bform a x y) : ℂ) ∂D.muN (2 * m)

variable {D a}

lemma coe_prod_circle {ι : Type*} (s : Finset ι) (f : ι → Circle) :
    ((∏ i ∈ s, f i : Circle) : ℂ) = ∏ i ∈ s, (f i : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.prod_insert hj, Circle.coe_mul, ih]

lemma addChar_sum {ι : Type*} (ψ : AddChar K Circle) (s : Finset ι) (f : ι → K) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

lemma psi_Qform (b : K) (x : Fin (2 * m) → K) :
    (D.ψ (b * Qform a x) : ℂ) = ∏ i, (D.ψ (b * (a i : K) * x i ^ 2) : ℂ) := by
  rw [Qform, Finset.mul_sum, addChar_sum, coe_prod_circle]
  simp only [mul_assoc]

lemma psi_Bform (x y : Fin (2 * m) → K) :
    (D.ψ (Bform a x y) : ℂ) = ∏ i, (D.ψ (x i * (2 * (a i : K) * y i)) : ℂ) := by
  rw [Bform, addChar_sum, coe_prod_circle]
  congr 1; ext i; congr 2; ring

lemma opNf_ptensor (b : K) (f : Fin (2 * m) → K → ℂ) :
    D.opNf a b (ptensor f) = ptensor (fun i => D.chirp (b * a i) (f i)) := by
  ext x; simp only [opNf, ptensor, chirp, psi_Qform, ← Finset.prod_mul_distrib]

lemma opMf_ptensor (t : K) (f : Fin (2 * m) → K → ℂ) :
    D.opMf a t (ptensor f) = (D.chiV a t * (D.md t : ℂ) ^ m) • ptensor (fun i => dil t (f i)) := by
  ext x; simp only [opMf, ptensor, dil, Pi.smul_apply, smul_eq_mul]

lemma opWf_ptensor' [SigmaFinite D.μ] (f : Fin (2 * m) → K → ℂ) :
    D.opWf a (ptensor f) = D.gammaV a • ptensor (fun i => D.Fa (a i) (f i)) := by
  ext y
  simp only [opWf, ptensor, Pi.smul_apply, smul_eq_mul, psi_Bform, ← Finset.prod_mul_distrib, muN]
  rw [integral_fintype_prod_eq_prod (fun i x => f i x * (D.ψ (x * (2 * (a i : K) * y i)) : ℂ)), cB,
    mul_assoc, ← Finset.prod_mul_distrib]
  rfl

lemma opWf_ptensor (hD : D.IsOps) (f : Fin (2 * m) → K → ℂ) :
    D.opWf a (ptensor f) = D.gammaV a • ptensor (fun i => D.Fa (a i) (f i)) := by
  haveI := hD.sigmaFinite
  exact opWf_ptensor' f

lemma opWf_smul (c : ℂ) (Φ : (Fin (2 * m) → K) → ℂ) : D.opWf a (c • Φ) = c • D.opWf a Φ := by
  ext y; simp only [opWf, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]; ring

lemma opNf_smul (b : K) (c : ℂ) (Φ : (Fin (2 * m) → K) → ℂ) : D.opNf a b (c • Φ) = c • D.opNf a b Φ := by
  ext x; simp only [opNf, Pi.smul_apply, smul_eq_mul]; ring

lemma opMf_smul (t : K) (c : ℂ) (Φ : (Fin (2 * m) → K) → ℂ) : D.opMf a t (c • Φ) = c • D.opMf a t Φ := by
  ext x; simp only [opMf, Pi.smul_apply, smul_eq_mul]; ring


/-! ### The constants $\chi_V$ and $\gamma_V$ -/

section Constants

variable (hD : D.IsModel)
include hD

lemma chiV_mul (s t : Kˣ) : D.chiV a ((s : K) * t) = D.chiV a s * D.chiV a t := hC_mul_left hD _ _ _

lemma chiV_sq (t : Kˣ) : D.chiV a t * D.chiV a t = 1 := hC_sq hD _ _

lemma chiV_one : D.chiV a 1 = 1 := by unfold chiV; exact hC_one_left hD (discV a)

lemma chiV_inv (t : Kˣ) : D.chiV a (↑t⁻¹ : K) = D.chiV a t := by
  have h := chiV_mul hD (a := a) t t⁻¹
  rw [Units.mul_inv, chiV_one hD] at h
  have hs := chiV_sq hD (a := a) t
  linear_combination (-D.chiV a t) * h - (D.chiV a ↑t⁻¹) * hs

lemma chiV_neg_one_eq : D.chiV a (-1) = D.hC (-1) (-1) ^ m * D.hC ((∏ i, a i : Kˣ) : K) (-1) := by
  have h1 : D.chiV a (-1) = D.hC ((-1 : Kˣ) : K) (((-1 : Kˣ) ^ m : Kˣ) : K) *
      D.hC ((-1 : Kˣ) : K) ((∏ i, a i : Kˣ) : K) := by
    rw [chiV, discV, Units.val_mul, ← hC_mul_right hD]; simp
  rw [h1, hC_comm hD _ ((-1) ^ m), hC_pow_left hD, hC_comm hD _ (∏ i, a i)]
  simp

lemma chiV_eq (b : Kˣ) : D.chiV a b = D.hC b (-1) ^ m * D.hC ((∏ i, a i : Kˣ) : K) b := by
  have h1 : D.chiV a b = D.hC (b : K) (((-1 : Kˣ) ^ m : Kˣ) : K) * D.hC (b : K) ((∏ i, a i : Kˣ) : K) := by
    rw [chiV, discV, Units.val_mul, ← hC_mul_right hD]
  rw [h1, hC_comm hD _ ((-1) ^ m), hC_pow_left hD, hC_comm hD _ (∏ i, a i), hC_comm hD (-1) b]
  simp

lemma prod_gN_ne_zero : (∏ i, D.gN (a i)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => gN_ne_zero hD (a i)

/-- $\prod_ig(a_ib) = \chi_V(b)\prod_ig(a_i)$ (from (H) and $g(b)^2 = (b,-1)g(1)^2$). -/
lemma prod_gN_mul (b : Kˣ) : ∏ i, D.gN ((a i : K) * b) = D.chiV a b * ∏ i, D.gN (a i) := by
  have hg1 : D.gN 1 ≠ 0 := by simpa using gN_ne_zero hD 1
  have key : (∏ i, D.gN ((a i : K) * b)) * D.gN 1 ^ (2 * m) =
      (∏ i, D.hC (a i) b) * (∏ i, D.gN (a i)) * D.gN b ^ (2 * m) := by
    have h := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => gN_mul hD (a i) b)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hb : D.gN b ^ (2 * m) = D.hC b (-1) ^ m * D.gN 1 ^ (2 * m) := by
    rw [pow_mul, pow_mul, sq, gN_sq hD, ← sq, mul_pow]
  rw [hb, ← hC_prod_left hD] at key
  have hchi := chiV_eq hD (a := a) b
  have h1 : D.gN 1 ^ (2 * m) ≠ 0 := pow_ne_zero _ hg1
  have : (∏ i, D.gN ((a i : K) * b) - D.chiV a b * ∏ i, D.gN (a i)) * D.gN 1 ^ (2 * m) = 0 := by
    rw [hchi]; linear_combination key
  rcases mul_eq_zero.mp this with h | h
  · linear_combination h
  · exact absurd h h1

/-- $\big(\prod_ig(a_i)\big)^2 = \chi_V(-1)$ (from $g(a)^2 = (a,-1)g(1)^2$ and $g(1)^4 = (-1,-1)$). -/
lemma prod_gN_sq : (∏ i, D.gN (a i)) * (∏ i, D.gN (a i)) = D.chiV a (-1) := by
  rw [← Finset.prod_mul_distrib]
  have h := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => gN_sq hD (a i))
  rw [h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    chiV_neg_one_eq hD, ← gN_one_pow_four hD]
  have hprod : ∏ i, D.hC (a i) (-1) = D.hC ((∏ i, a i : Kˣ) : K) (-1) := by
    have := hC_prod_left hD Finset.univ a (-1)
    simpa using this.symm
  rw [hprod]
  ring

/-- **$\gamma_V^2 = \chi_V(-1)$**, which is relation (R5) $w^2 = m(-1)$ at the level of constants. -/
@[kb "weil1964" "§14 and §26 (the index of a quadratic form; $\\gamma^2$) [unverified]"]
theorem gammaV_sq : D.gammaV a * D.gammaV a = D.chiV a (-1) := by
  have h := prod_gN_sq hD (a := a)
  have hs := chiV_sq hD (a := a) (-1)
  simp only [Units.val_neg, Units.val_one] at hs
  have hc : D.chiV a (-1) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact zero_ne_one hs
  calc D.gammaV a * D.gammaV a
      = (D.chiV a (-1) * D.chiV a (-1)) * ((∏ i, D.gN (a i)) * (∏ i, D.gN (a i)))⁻¹ := by
        unfold gammaV; rw [mul_inv]; ring
    _ = (D.chiV a (-1))⁻¹ := by rw [h, hs, one_mul]
    _ = D.chiV a (-1) := by field_simp; linear_combination -hs

/-- **$\gamma_V\prod_ig(a_ib) = \chi_V(-b)$**, which is relation (R6) at the level of constants. -/
@[kb "weil1964" "§14 and §26 [unverified]"]
theorem gammaV_mul_prod_gN (b : Kˣ) :
    D.gammaV a * ∏ i, D.gN ((a i : K) * b) = D.chiV a (-(b : K)) := by
  rw [prod_gN_mul hD, gammaV, show -(b : K) = ((-1 : Kˣ) : K) * b by simp, chiV_mul hD]
  have hne := prod_gN_ne_zero hD (a := a)
  field_simp
  simp only [Units.val_neg, Units.val_one]
  ring

/-- **$\gamma_V$ is the Weil index of $V$:** $\gamma_V = \prod_ig(a_i)$, the product of the normalized Weil indices
$g(a_i) = \gamma(a_i)|2a_i|^{1/2}$ of the characters of second degree $x \mapsto \psi(a_ix^2)$ (Weil's normalization).
(From $\gamma_V = \chi_V(-1)\prod_ig(a_i)^{-1}$ and $\big(\prod_ig(a_i)\big)^2 = \chi_V(-1)$.) -/
@[kb "weil1964" "§14, Thm. 2; §26 (the index of $\\langle a_0,\\dots,a_{n-1}\\rangle$ is the product) [unverified]"]
theorem gammaV_eq_prod_gN : D.gammaV a = ∏ i, D.gN (a i) := by
  have h := prod_gN_sq hD (a := a)
  have hne := prod_gN_ne_zero hD (a := a)
  rw [gammaV, ← h]
  field_simp

end Constants

/-! ### The operators on $S(V)$ -/

lemma opNf_add (b : K) (Φ Ψ : (Fin (2 * m) → K) → ℂ) : D.opNf a b (Φ + Ψ) = D.opNf a b Φ + D.opNf a b Ψ := by
  ext x; simp only [opNf, Pi.add_apply]; ring

lemma opMf_add (t : K) (Φ Ψ : (Fin (2 * m) → K) → ℂ) : D.opMf a t (Φ + Ψ) = D.opMf a t Φ + D.opMf a t Ψ := by
  ext x; simp only [opMf, Pi.add_apply]; ring

section Operators

variable (hD : D.IsOps)
include hD

lemma integrable_ptensor_char {f : Fin (2 * m) → K → ℂ} (hf : ∀ i, f i ∈ D.S) (y : Fin (2 * m) → K) :
    Integrable (fun x => ptensor f x * (D.ψ (Bform a x y) : ℂ)) (D.muN (2 * m)) := by
  haveI := hD.sigmaFinite
  have : (fun x => ptensor f x * (D.ψ (Bform a x y) : ℂ)) =
      fun x => ∏ i, (f i (x i) * (D.ψ (x i * (2 * (a i : K) * y i)) : ℂ)) := by
    ext x; simp only [ptensor, psi_Bform, ← Finset.prod_mul_distrib]
  rw [this]
  exact Integrable.fintype_prod (f := fun i z => f i z * (D.ψ (z * (2 * (a i : K) * y i)) : ℂ))
    (fun i => hD.integrable_char _ (hf i) _)

lemma integrable_Sn_char {Φ : (Fin (2 * m) → K) → ℂ} (hΦ : Φ ∈ D.Sn (2 * m)) (y : Fin (2 * m) → K) :
    Integrable (fun x => Φ x * (D.ψ (Bform a x y) : ℂ)) (D.muN (2 * m)) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx => obtain ⟨f, hf, rfl⟩ := hx; exact integrable_ptensor_char hD hf y
  | zero => simp
  | add x z _ _ hx hz =>
    refine (hx.add hz).congr (Filter.Eventually.of_forall fun x => ?_); simp [add_mul]
  | smul c x _ hx =>
    refine (hx.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_); simp [mul_assoc]

lemma opWf_add {Φ Ψ : (Fin (2 * m) → K) → ℂ} (hΦ : Φ ∈ D.Sn (2 * m)) (hΨ : Ψ ∈ D.Sn (2 * m)) :
    D.opWf a (Φ + Ψ) = D.opWf a Φ + D.opWf a Ψ := by
  ext y
  simp only [opWf, Pi.add_apply, add_mul]
  rw [integral_add (integrable_Sn_char hD hΦ y) (integrable_Sn_char hD hΨ y)]
  ring

lemma opNf_mem (b : K) {Φ : (Fin (2 * m) → K) → ℂ} (hΦ : Φ ∈ D.Sn (2 * m)) : D.opNf a b Φ ∈ D.Sn (2 * m) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opNf_ptensor]; exact ptensor_mem_Sn (fun i => hD.chirp_mem _ (hf i) _)
  | zero => rw [show D.opNf a b 0 = 0 by ext; simp [opNf]]; exact zero_mem _
  | add x z _ _ hx hz => rw [opNf_add]; exact add_mem hx hz
  | smul c x _ hx => rw [opNf_smul]; exact Submodule.smul_mem _ c hx

lemma opMf_mem (t : Kˣ) {Φ : (Fin (2 * m) → K) → ℂ} (hΦ : Φ ∈ D.Sn (2 * m)) :
    D.opMf a t Φ ∈ D.Sn (2 * m) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opMf_ptensor]; exact Submodule.smul_mem _ _ (ptensor_mem_Sn (fun i => hD.dil_mem _ (hf i) _))
  | zero => rw [show D.opMf a t 0 = 0 by ext; simp [opMf]]; exact zero_mem _
  | add x z _ _ hx hz => rw [opMf_add]; exact add_mem hx hz
  | smul c x _ hx => rw [opMf_smul]; exact Submodule.smul_mem _ c hx

lemma opWf_mem {Φ : (Fin (2 * m) → K) → ℂ} (hΦ : Φ ∈ D.Sn (2 * m)) : D.opWf a Φ ∈ D.Sn (2 * m) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opWf_ptensor hD]; exact Submodule.smul_mem _ _ (ptensor_mem_Sn (fun i => Fa_mem hD (hf i) _))
  | zero => rw [show D.opWf a 0 = 0 by ext; simp [opWf]]; exact zero_mem _
  | add x z hx' hz' hx hz => rw [opWf_add hD hx' hz']; exact add_mem hx hz
  | smul c x _ hx => rw [opWf_smul]; exact Submodule.smul_mem _ c hx

variable (a) in
/-- $\omega(n(b))$ as a linear endomorphism of $S(V)$. -/
def opN (b : K) : Module.End ℂ (D.Sn (2 * m)) where
  toFun Φ := ⟨D.opNf a b Φ, opNf_mem hD b Φ.2⟩
  map_add' Φ Ψ := Subtype.ext (by simp only [Submodule.coe_add]; exact opNf_add b Φ.1 Ψ.1)
  map_smul' c Φ := Subtype.ext (by simp only [Submodule.coe_smul, RingHom.id_apply]; exact opNf_smul b c Φ.1)

variable (a) in
/-- $\omega(m(t))$ as a linear endomorphism of $S(V)$. -/
def opM (t : Kˣ) : Module.End ℂ (D.Sn (2 * m)) where
  toFun Φ := ⟨D.opMf a t Φ, opMf_mem hD t Φ.2⟩
  map_add' Φ Ψ := Subtype.ext (by simp only [Submodule.coe_add]; exact opMf_add (t : K) Φ.1 Ψ.1)
  map_smul' c Φ := Subtype.ext (by
    simp only [Submodule.coe_smul, RingHom.id_apply]; exact opMf_smul (t : K) c Φ.1)

variable (a) in
/-- $\omega(w)$ as a linear endomorphism of $S(V)$. -/
def opW : Module.End ℂ (D.Sn (2 * m)) where
  toFun Φ := ⟨D.opWf a Φ, opWf_mem hD Φ.2⟩
  map_add' Φ Ψ := Subtype.ext (by simp only [Submodule.coe_add]; exact opWf_add hD Φ.2 Ψ.2)
  map_smul' c Φ := Subtype.ext (by simp only [Submodule.coe_smul, RingHom.id_apply]; exact opWf_smul c Φ.1)

@[simp] lemma opN_apply (b : K) (Φ : D.Sn (2 * m)) : (opN a hD b Φ : (Fin (2 * m) → K) → ℂ) =
    D.opNf a b Φ := rfl
@[simp] lemma opM_apply (t : Kˣ) (Φ : D.Sn (2 * m)) : (opM a hD t Φ : (Fin (2 * m) → K) → ℂ) =
    D.opMf a t Φ := rfl
@[simp] lemma opW_apply (Φ : D.Sn (2 * m)) : (opW a hD Φ : (Fin (2 * m) → K) → ℂ) = D.opWf a Φ := rfl

end Operators

/-- Two endomorphisms of $S(V)$ agreeing on pure tensors are equal. -/
lemma End_ext_ptensor {n : ℕ} {L₁ L₂ : Module.End ℂ (D.Sn n)}
    (h : ∀ (f : Fin n → K → ℂ) (hf : ∀ i, f i ∈ D.S),
      (L₁ ⟨ptensor f, ptensor_mem_Sn hf⟩ : (Fin n → K) → ℂ) = L₂ ⟨ptensor f, ptensor_mem_Sn hf⟩) :
    L₁ = L₂ := by
  refine LinearMap.ext_on Submodule.span_span_coe_preimage ?_
  rintro ⟨Φ, hΦ⟩ hmem
  obtain ⟨f, hf, rfl⟩ := hmem
  exact Subtype.ext (h f hf)

/-! ### The relations -/

section Relations

variable (hD : D.IsModel)
include hD

lemma ptensor_const_smul (c : ℂ) (g : Fin (2 * m) → K → ℂ) :
    ptensor (fun i => c • g i) = (c ^ (2 * m)) • ptensor g := by
  rw [ptensor_smul_fun, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- (R1) -/
lemma opN_zero : opN a hD.toIsOps 0 = 1 := by
  ext Φ x; simp [opNf]

lemma opN_add (b b' : K) : opN a hD.toIsOps (b + b') = opN a hD.toIsOps b * opN a hD.toIsOps b' := by
  ext Φ x
  simp only [opN_apply, Module.End.mul_apply, opNf, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- (R2) -/
lemma opM_one : opM a hD.toIsOps 1 = 1 := by
  ext Φ x; simp [opMf, chiV_one hD, md_one hD]

lemma opM_mul (s t : Kˣ) : opM a hD.toIsOps (s * t) = opM a hD.toIsOps s * opM a hD.toIsOps t := by
  ext Φ x
  simp only [opM_apply, Module.End.mul_apply, opMf, Units.val_mul, chiV_mul hD, hD.md_mul]
  push_cast
  rw [mul_pow]
  have : (fun i => (s : K) * t * x i) = fun i => (t : K) * ((s : K) * x i) := by ext i; ring
  rw [this]; ring

/-- (R3) -/
lemma opM_opN (t : Kˣ) (b : K) :
    opM a hD.toIsOps t * opN a hD.toIsOps b = opN a hD.toIsOps ((t : K) ^ 2 * b) * opM a hD.toIsOps t := by
  ext Φ x
  simp only [opM_apply, opN_apply, Module.End.mul_apply, opMf, opNf]
  have : b * Qform a (fun i => (t : K) * x i) = (t : K) ^ 2 * b * Qform a x := by
    simp only [Qform, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [this]; ring

/-- (R4) $\omega(w)\omega(m(t)) = \omega(m(t^{-1}))\omega(w)$. -/
lemma opW_opM (t : Kˣ) :
    opW a hD.toIsOps * opM a hD.toIsOps t = opM a hD.toIsOps t⁻¹ * opW a hD.toIsOps := by
  refine End_ext_ptensor fun f hf => ?_
  show D.opWf a (D.opMf a t (ptensor f)) = D.opMf a ↑t⁻¹ (D.opWf a (ptensor f))
  rw [opMf_ptensor, opWf_smul, opWf_ptensor hD.toIsOps, opWf_ptensor hD.toIsOps, opMf_smul, opMf_ptensor]
  have hF : (fun i => D.Fa (a i) (dil (t : K) (f i))) =
      fun i => ((D.md t : ℂ)⁻¹) • dil (↑t⁻¹ : K) (D.Fa (a i) (f i)) :=
    funext fun i => Fa_dil hD (hf i) (a i) t
  rw [hF, ptensor_const_smul hD, smul_smul, smul_smul, smul_smul]
  congr 1
  rw [chiV_inv hD, md_inv hD]
  have := hD.md_pos t
  have : (D.md t : ℂ) ≠ 0 := by exact_mod_cast this.ne'
  push_cast
  rw [inv_pow, inv_pow]
  field_simp
  ring

/-- (R5) $\omega(w)^2 = \omega(m(-1))$, using $\gamma_V^2 = \chi_V(-1)$. -/
lemma opW_opW : opW a hD.toIsOps * opW a hD.toIsOps = opM a hD.toIsOps (-1) := by
  refine End_ext_ptensor fun f hf => ?_
  show D.opWf a (D.opWf a (ptensor f)) = D.opMf a ↑(-1 : Kˣ) (ptensor f)
  rw [opWf_ptensor hD.toIsOps, opWf_smul, opWf_ptensor hD.toIsOps, opMf_ptensor, smul_smul,
    gammaV_sq hD]
  have hF : (fun i => D.Fa (a i) (D.Fa (a i) (f i))) = fun i => dil (-1 : K) (f i) :=
    funext fun i => Fa_Fa hD (hf i) (a i)
  rw [hF]
  simp [md_neg_one hD]

/-- (R6) $\omega(w)\omega(n(b))\omega(w) = \omega(n(-b^{-1}))\omega(m(-b^{-1}))\omega(w)\omega(n(-b^{-1}))$, using
$\gamma_V\prod_ig(a_ib) = \chi_V(-b)$. -/
lemma opW_opN_opW (b : Kˣ) :
    opW a hD.toIsOps * opN a hD.toIsOps (b : K) * opW a hD.toIsOps =
      opN a hD.toIsOps (-(↑b⁻¹ : K)) * opM a hD.toIsOps (-b⁻¹) * opW a hD.toIsOps *
        opN a hD.toIsOps (-(↑b⁻¹ : K)) := by
  refine End_ext_ptensor fun f hf => ?_
  show D.opWf a (D.opNf a b (D.opWf a (ptensor f))) =
    D.opNf a (-(↑b⁻¹ : K)) (D.opMf a ↑(-b⁻¹) (D.opWf a (D.opNf a (-(↑b⁻¹ : K)) (ptensor f))))
  rw [opWf_ptensor hD.toIsOps, opNf_smul, opNf_ptensor, opWf_smul, opWf_ptensor hD.toIsOps, smul_smul]
  rw [opNf_ptensor, opWf_ptensor hD.toIsOps, opMf_smul, opMf_ptensor, opNf_smul, opNf_smul, opNf_ptensor,
    smul_smul]
  have hF : (fun i => D.Fa (a i) (D.chirp ((b : K) * a i) (D.Fa (a i) (f i)))) =
      fun i => (D.gN ((a i : K) * b) * ((Real.sqrt (D.md b) : ℂ))⁻¹) •
        D.chirp (-(↑b⁻¹ : K) * a i) (dil ((-b⁻¹ : Kˣ) : K)
          (D.Fa (a i) (D.chirp (-(↑b⁻¹ : K) * a i) (f i)))) := by
    funext i
    rw [mul_comm (b : K), Fa_chirp_Fa hD (hf i) (a i) b]
    congr 2 <;> simp [mul_comm]
  rw [hF, ptensor_smul_fun, smul_smul]
  congr 1
  -- constants
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hγ := gammaV_mul_prod_gN hD (a := a) b
  have hb := hD.md_pos b
  have hs : (Real.sqrt (D.md b) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have hs2 : ((Real.sqrt (D.md b) : ℂ)) ^ 2 = D.md b := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  have hchi : D.chiV a ((-b⁻¹ : Kˣ) : K) = D.chiV a (-(b : K)) := by
    rw [show (-b⁻¹ : Kˣ) = (-b)⁻¹ by simp, chiV_inv hD]; simp
  have hmd : D.md ((-b⁻¹ : Kˣ) : K) = (D.md b)⁻¹ := by
    rw [Units.val_neg, md_neg hD, md_inv hD]
  rw [hchi, hmd, ← hγ, pow_mul, inv_pow, inv_pow, hs2]
  push_cast
  have : (D.md b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [inv_pow]
  field_simp

/-- **The relations (R1)–(R6)** for $\omega(n(\iota b))$, $\omega(m(\iota t))$, $\omega(w)$ on $S(V)$, for a ring map
$\iota : k \to K$ from a field. -/
theorem sl2Relations {k : Type*} [Field k] (ι : k →+* K) :
    SL2Relations (fun b : k => opN a hD.toIsOps (ι b)) (fun t : kˣ => opM a hD.toIsOps (Units.map ι t))
      (opW a hD.toIsOps) where
  N_zero := by simp only [map_zero]; exact opN_zero hD
  N_add b b' := by simp only [map_add]; exact opN_add hD _ _
  A_one := by simp only [map_one]; exact opM_one hD
  A_mul t t' := by simp only [map_mul]; exact opM_mul hD _ _
  A_N t b := by
    have := opM_opN hD (a := a) (Units.map ι t) (ι b)
    simpa [map_mul, map_pow] using this
  W_A t := by simpa [map_inv] using opW_opM hD (a := a) (Units.map ι t)
  W_W := by simpa using opW_opW hD (a := a)
  W_N_W b hb := by
    have := opW_opN_opW hD (a := a) (Units.map ι (Units.mk0 b hb))
    have e1 : (((Units.map ι (Units.mk0 b hb))⁻¹ : Kˣ) : K) = ι b⁻¹ := by simp
    have e2 : (-(Units.map ι (Units.mk0 b hb))⁻¹ : Kˣ) = Units.map ι (Units.mk0 (-b⁻¹) (unit_ne_zero_aux hb)) := by
      ext; simp
    rw [e1, e2] at this
    simpa [map_neg] using this

end Relations

/-! ### The Weil representation -/

/-- **The Weil representation** $\omega = \omega_{V,\psi} : \mathrm{SL}_2(k) \to \operatorname{End}_{\mathbb C}S(V)$ of a diagonal
quadratic space $V = \langle a_0, \dots, a_{2m-1}\rangle$ of even dimension $n = 2m$ over $K$, for a field $k$ with a
ring map $\iota : k \to K$ (e.g. $k = K = F_v$, or $k = F \to F_v$), in the Schrödinger model:
$$\omega(n(b))\Phi(x) = \psi(bQ(x))\Phi(x),\quad \omega(m(t))\Phi(x) = \chi_V(t)|t|^{n/2}\Phi(tx),\quad
  \omega(w)\Phi = \gamma_V\hat\Phi$$
(`weilRep_nMat`, `weilRep_mMat`, `weilRep_wMat`), $\hat\Phi(y) = \int\Phi(x)\psi(B(x,y))d\mu_B(x)$. It is a monoid
homomorphism: no cocycle, since $n$ is even. On a general $g$ it is the Bruhat-cell formula (`cellRep`). -/
@[kb "weil1964" "§14, Thm. 2 (the representation of $\\mathrm{Sp}$ for even $n$; for $\\mathrm{SL}_2$) [unverified]"]
def weilRep (hD : D.IsModel) {k : Type*} [Field k] (ι : k →+* K) :
    SL(2, k) →* Module.End ℂ (D.Sn (2 * m)) :=
  cellHom (sl2Relations hD (a := a) ι)

variable (hD : D.IsModel) {k : Type*} [Field k] (ι : k →+* K)

@[simp] theorem weilRep_nMat (b : k) : weilRep hD (a := a) ι (nMat b) = opN a hD.toIsOps (ι b) :=
  cellHom_nMat _ b

@[simp] theorem weilRep_mMat (t : kˣ) : weilRep hD (a := a) ι (mMat t) = opM a hD.toIsOps (Units.map ι t) :=
  cellHom_mMat _ t

@[simp] theorem weilRep_wMat : weilRep hD (a := a) ι wMat = opW a hD.toIsOps := cellHom_wMat _

theorem weilRep_apply (g : SL(2, k)) :
    weilRep hD (a := a) ι g = cellRep (fun b : k => opN a hD.toIsOps (ι b))
      (fun t : kˣ => opM a hD.toIsOps (Units.map ι t)) (opW a hD.toIsOps) g := rfl

end LocalData

end QuadFormsKB.WeilRep
