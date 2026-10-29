/-
# The Schrödinger model of the Weil representation of $\mathrm{Sp}_{2g}$

**Layer:** abstract local harmonic analysis over a commutative ring $K$, from the one-variable data `LocalData K` of
`Weil/Model.lean` (instantiated at every finite place, `isModel_V`, and at the archimedean block, `isModel_inf`).

**Setting.** $V = K^{n}$, $n = 2m$, $Q(x) = \sum_{i<n}a_ix_i^2$ with $a_i \in K^\times$ (0-based indices), the genus $g$, and
$V^g = M_{n\times g}(K)$ (`PtG`): column $j$ of $X$ is $x_j \in V$. Put
$$Q[X] = X^{\mathsf T}\operatorname{diag}(a)X = \big(\tfrac12B(x_j, x_k)\big)_{jk}\ (\texttt{QX}),\qquad
  \langle X, Y\rangle = \sum_{i,j}2a_iX_{ij}Y_{ij} = \sum_jB(x_j, y_j)\ (\texttt{BX}).$$

**The operators** (Kudla, *Notes*, §I.1, Prop. 1.3 [unverified]; Weil 1964, §14 [unverified]) on functions
$\Phi : V^g \to \mathbb C$:
$$\omega(n(B))\Phi(X) = \psi(\operatorname{tr}(B\,Q[X]))\Phi(X),\qquad
  \omega(m(A))\Phi(X) = \chi_V(\det A)\,|\det A|^{m}\,\Phi(XA),$$
$$\omega(w)\Phi(Y) = \gamma_V^{\,g}\int_{V^g}\Phi(X)\,\psi(\langle X, Y\rangle)\,d\mu_B(X)\qquad(\texttt{opNg},\ \texttt{opMg},\ \texttt{opWg}),$$
with $d\mu_B$ the self-dual measure ($g$ copies of the one of `Weil/Model.lean`), $|\det A|^m = |\det A|^{n/2}$.

**The test space** $S(V^g) = \operatorname{span}\{X \mapsto \prod_{i,j}f_{ij}(X_{ij}) : f_{ij} \in S\}$ (`Sg`).

**Agreement with $g = 1$** (`opNg_genusOne`, `opMg_genusOne`, `opWg_genusOne`, `weilRepSp_genusOne`): along $M_{n\times1}(K) \cong K^n$ the three operators are
`opNf`, `opMf`, `opWf` of `Weil/Model.lean`. More generally, on pure tensors the diagonal elements act coordinatewise
by the one-variable operators (`opNg_diag_ptG`, `opMg_diag_ptG`, `opWg_ptG`), i.e. $n(\operatorname{diag}d)$,
$m(\operatorname{diag}t)$, $w$ act on $S(V)^{\otimes g}$ as $\bigotimes_j$ of the genus-one operators for $d_j$, $t_j$, $w$.

**Relations proved for every model** (`LocalData.IsModel`; no further hypothesis):
* on all functions: $\omega(n(B+B')) = \omega(n(B))\omega(n(B'))$, $\omega(m(AA')) = \omega(m(A))\omega(m(A'))$,
  $\omega(m(A))\omega(n(B)) = \omega(n(AB\,{}^tA))\omega(m(A))$ (`opNg_add`, `opMg_mul`, `opMg_opNg`);
* on $S(V^g)$: $\omega(w)^2 = \omega(m(-1))$ (`opWg_opWg`) and the Weil relation for invertible diagonal $D$
  $$\omega(w)\omega(n(D))\omega(w) = \omega(n(-D^{-1}))\,\omega(m(-D^{-1}))\,\omega(w)\,\omega(n(-D^{-1}))\qquad(\texttt{opWg\_opNg\_opWg\_diag}),$$
  from the one-variable identities of `Weil/Model.lean` coordinate by coordinate, and the constants
  $\gamma_V^2 = \chi_V(-1)$, $\gamma_V\prod_ig(a_id) = \chi_V(-d)$ once per column.

**The interface `IsGLModel`** (stability of $S(V^g)$ under $\omega(m(A))$, $\omega(n(B))$ for all $A$, symmetric $B$, and the
change of variables $\int\Phi(XA)\psi(\langle X, Y\rangle)\,dX = |\det A|^{-n}\int\Phi(X)\psi(\langle X, Y\,{}^tA^{-1}\rangle)\,dX$ on
$S(V^g)$). It holds for $g = 1$ in every model (`isGLModel_one`). Under it: $\omega(w)\omega(m(A)) = \omega(m({}^tA^{-1}))\omega(w)$
(`opWg_opMg`), all relations `SiegelRelations` for $k \to K$ (`siegelRelations_omega`, by `siegelRelations_of_diag`),
and, **conditional on the named input `SiegelPresentation`**, the Weil representation
$$\omega : \mathrm{Sp}_{2g}(k) \to \operatorname{End}_{\mathbb C}S(V^g)\qquad(\texttt{weilRepSp})$$
with the Schrödinger formulas on $n(B)$, $m(A)$, $w$ (`weilRepSp_spN`, `weilRepSp_spM`, `weilRepSp_spW`).

Sources: Weil, Acta Math. 111 (1964), §14 [unverified]; Kudla, *Notes on the local theta correspondence* (1996), §I.1,
Prop. 1.3 [unverified]; Rao, Pacific J. Math. 157 (1993), §3 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Model
import QuadFormsKB.Weil.Genus.Relations

open MeasureTheory Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

variable {K : Type*} [CommRing K] [MeasurableSpace K]

/-- **Points of $V^g$**: $n\times g$ matrices, $n = 2m$; column $j$ is $x_j \in V = K^n$. -/
abbrev PtG (m g : ℕ) (K : Type*) := Matrix (Fin (2 * m)) (Fin g) K

variable {m g : ℕ}

/-- $Q[X] = X^{\mathsf T}\operatorname{diag}(a)X$, i.e. $Q[X]_{jk} = \sum_ia_iX_{ij}X_{ik} = \tfrac12B(x_j, x_k)$. -/
def QX (a : Fin (2 * m) → Kˣ) (X : PtG m g K) : Matrix (Fin g) (Fin g) K :=
  Xᵀ * diagonal (fun i => (a i : K)) * X

/-- The pairing $\langle X, Y\rangle = \sum_{i,j}2a_iX_{ij}Y_{ij} = \sum_jB(x_j, y_j)$ on $V^g$. -/
def BX (a : Fin (2 * m) → Kˣ) (X Y : PtG m g K) : K := ∑ i, ∑ j, 2 * (a i : K) * X i j * Y i j

/-- The product measure $\mu^{\otimes(n\times g)}$ on $V^g$. -/
def muG (D : LocalData K) (m g : ℕ) : Measure (PtG m g K) := Measure.pi fun _ => Measure.pi fun _ => D.μ

/-- **$\omega(n(B))$:** $\Phi(X) \mapsto \psi(\operatorname{tr}(B\,Q[X]))\Phi(X)$. -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(n(b))\\varphi(x) = \\psi(\\operatorname{tr}(b\\,Q(x)))\\varphi(x)$) [unverified]"]
def opNg (D : LocalData K) (a : Fin (2 * m) → Kˣ) (B : Matrix (Fin g) (Fin g) K) (Φ : PtG m g K → ℂ)
    (X : PtG m g K) : ℂ :=
  (D.ψ (trace (B * QX a X)) : ℂ) * Φ X

/-- **$\omega(m(A))$:** $\Phi(X) \mapsto \chi_V(\det A)|\det A|^{m}\Phi(XA)$ ($|\det A|^{n/2}$, $n = 2m$). -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(m(a))\\varphi(x) = \\chi_V(\\det a)|\\det a|^{m/2}\\varphi(xa)$) [unverified]"]
def opMg (D : LocalData K) (a : Fin (2 * m) → Kˣ) (A : GL (Fin g) K) (Φ : PtG m g K → ℂ) (X : PtG m g K) : ℂ :=
  D.chiV a (A : Matrix (Fin g) (Fin g) K).det * (D.md (A : Matrix (Fin g) (Fin g) K).det : ℂ) ^ m *
    Φ (X * (A : Matrix (Fin g) (Fin g) K))

/-- **$\omega(w)$:** $\Phi \mapsto \gamma_V^g\hat\Phi$, $\hat\Phi(Y) = \int\Phi(X)\psi(\langle X, Y\rangle)\,d\mu_B(X)$, with
$d\mu_B = c_B^{\,g}\,d\mu^{\otimes(n\times g)}$ self-dual ($c_B = \prod_i|2a_i|^{1/2}$, `cB`). -/
@[kb "kudla1996" "§I.1, Prop. 1.3 (Schrödinger model, $\\omega(w)\\varphi = \\gamma\\,\\hat\\varphi$) [unverified]"]
def opWg (D : LocalData K) (a : Fin (2 * m) → Kˣ) (Φ : PtG m g K → ℂ) (Y : PtG m g K) : ℂ :=
  D.gammaV a ^ g * D.cB a ^ g * ∫ X, Φ X * (D.ψ (BX a X Y) : ℂ) ∂muG D m g

/-- **Pure tensors** $X \mapsto \prod_{i,j}f_{ij}(X_{ij})$ on $V^g$. -/
def ptG (f : Fin (2 * m) → Fin g → K → ℂ) (X : PtG m g K) : ℂ := ∏ i, ∏ j, f i j (X i j)

/-- **The Schwartz space of $V^g$**, spanned by pure tensors of test functions. -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ for a finite-dimensional $X$; here $X = V^g$) [unverified]"]
def Sg (D : LocalData K) (m g : ℕ) : Submodule ℂ (PtG m g K → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f : Fin (2 * m) → Fin g → K → ℂ, (∀ i j, f i j ∈ D.S) ∧ Φ = ptG f}

variable {D : LocalData K} {a : Fin (2 * m) → Kˣ}

lemma ptG_mem_Sg {f : Fin (2 * m) → Fin g → K → ℂ} (hf : ∀ i j, f i j ∈ D.S) : ptG f ∈ Sg D m g :=
  Submodule.subset_span ⟨f, hf, rfl⟩

/-! ### Pure tensors and the diagonal elements -/

lemma psi_trace_diag_QX (d : Fin g → K) (X : PtG m g K) :
    (D.ψ (trace (diagonal d * QX a X)) : ℂ) = ∏ i, ∏ j, (D.ψ (d j * (a i : K) * X i j ^ 2) : ℂ) := by
  have h : trace (diagonal d * QX a X) = ∑ i, ∑ j, d j * (a i : K) * X i j ^ 2 := by
    have hY : ∀ j i, (Xᵀ * diagonal fun i => (a i : K)) j i = X i j * a i := fun j i => by
      rw [mul_diagonal, transpose_apply]
    have hdiag : ∀ j, (QX a X) j j = ∑ i, a i * X i j ^ 2 := by
      intro j
      rw [QX, mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hY]; ring
    simp only [trace, diag, diagonal_mul, hdiag, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h, addChar_sum, coe_prod_circle]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [addChar_sum, coe_prod_circle]

lemma psi_BX (X Y : PtG m g K) :
    (D.ψ (BX a X Y) : ℂ) = ∏ i, ∏ j, (D.ψ (X i j * (2 * (a i : K) * Y i j)) : ℂ) := by
  rw [BX, addChar_sum, coe_prod_circle]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [addChar_sum, coe_prod_circle]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2; ring

lemma opNg_diag_ptG (d : Fin g → K) (f : Fin (2 * m) → Fin g → K → ℂ) :
    opNg D a (diagonal d) (ptG f) = ptG (fun i j => D.chirp (d j * a i) (f i j)) := by
  ext X
  simp only [opNg, ptG, chirp, psi_trace_diag_QX, ← Finset.prod_mul_distrib]

lemma opMg_diag_ptG (t : Fin g → Kˣ) (f : Fin (2 * m) → Fin g → K → ℂ) :
    opMg D a (diagGL t) (ptG f) =
      (D.chiV a (∏ j, (t j : K)) * (D.md (∏ j, (t j : K)) : ℂ) ^ m) • ptG (fun i j => dil (t j : K) (f i j)) := by
  ext X
  simp only [opMg, ptG, dil, diagGL_coe, det_diagonal, Pi.smul_apply, smul_eq_mul, mul_diagonal]
  congr 1
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma opWg_ptG (hD : D.IsOps) (f : Fin (2 * m) → Fin g → K → ℂ) :
    opWg D a (ptG f) = (D.gammaV a ^ g) • ptG (fun i j => D.Fa (a i) (f i j)) := by
  haveI := hD.sigmaFinite
  ext Y
  simp only [opWg, ptG, Pi.smul_apply, smul_eq_mul, psi_BX, ← Finset.prod_mul_distrib]
  have h0 : ∫ X : PtG m g K, ∏ i, ∏ j, (f i j (X i j) * (D.ψ (X i j * (2 * (a i : K) * Y i j)) : ℂ))
      ∂(muG D m g) =
      ∏ i, ∫ x : Fin g → K, ∏ j, (f i j (x j) * (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ))
        ∂(Measure.pi fun _ => D.μ) :=
    integral_fintype_prod_eq_prod (fun i (x : Fin g → K) => ∏ j, (f i j (x j) *
      (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ)))
  rw [h0]
  have h1 : ∀ i, ∫ x : Fin g → K, ∏ j, (f i j (x j) * (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ))
      ∂(Measure.pi fun _ => D.μ) = ∏ j, ∫ x, f i j x * (D.ψ (x * (2 * (a i : K) * Y i j)) : ℂ) ∂D.μ :=
    fun i => integral_fintype_prod_eq_prod (fun j x => f i j x * (D.ψ (x * (2 * (a i : K) * Y i j)) : ℂ))
  simp only [h1]
  have hc : D.cB a ^ g = ∏ i, ∏ _j : Fin g, (Real.sqrt (D.md (2 * (a i : K))) : ℂ) := by
    rw [cB, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [mul_assoc, hc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Fa, Pi.smul_apply, smul_eq_mul, dil, four]

/-! ### Linearity and stability -/

lemma opNg_add_fun (B : Matrix (Fin g) (Fin g) K) (Φ Ψ : PtG m g K → ℂ) :
    opNg D a B (Φ + Ψ) = opNg D a B Φ + opNg D a B Ψ := by
  ext X; simp only [opNg, Pi.add_apply]; ring

lemma opNg_smul (B : Matrix (Fin g) (Fin g) K) (c : ℂ) (Φ : PtG m g K → ℂ) :
    opNg D a B (c • Φ) = c • opNg D a B Φ := by
  ext X; simp only [opNg, Pi.smul_apply, smul_eq_mul]; ring

lemma opMg_add_fun (A : GL (Fin g) K) (Φ Ψ : PtG m g K → ℂ) :
    opMg D a A (Φ + Ψ) = opMg D a A Φ + opMg D a A Ψ := by
  ext X; simp only [opMg, Pi.add_apply]; ring

lemma opMg_smul (A : GL (Fin g) K) (c : ℂ) (Φ : PtG m g K → ℂ) :
    opMg D a A (c • Φ) = c • opMg D a A Φ := by
  ext X; simp only [opMg, Pi.smul_apply, smul_eq_mul]; ring

lemma opWg_smul (c : ℂ) (Φ : PtG m g K → ℂ) : opWg D a (c • Φ) = c • opWg D a Φ := by
  ext Y; simp only [opWg, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]; ring

lemma integrable_Sg (hD : D.IsOps) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) (Y : PtG m g K) :
    Integrable (fun X => Φ X * (D.ψ (BX a X Y) : ℂ)) (muG D m g) := by
  haveI := hD.sigmaFinite
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have : (fun X => ptG f X * (D.ψ (BX a X Y) : ℂ)) = fun X : PtG m g K =>
        ∏ i, ∏ j, (f i j (X i j) * (D.ψ (X i j * (2 * (a i : K) * Y i j)) : ℂ)) := by
      ext X; simp only [ptG, psi_BX, ← Finset.prod_mul_distrib]
    rw [this]
    exact Integrable.fintype_prod (μ := fun _ => Measure.pi fun _ => D.μ)
      (f := fun i (x : Fin g → K) => ∏ j, (f i j (x j) * (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ)))
      fun i => Integrable.fintype_prod (f := fun j z => f i j z * (D.ψ (z * (2 * (a i : K) * Y i j)) : ℂ))
        fun j => hD.integrable_char _ (hf i j) _
  | zero => simp
  | add x z _ _ hx hz =>
    refine (hx.add hz).congr (Filter.Eventually.of_forall fun x => ?_); simp [add_mul]
  | smul c x _ hx =>
    refine (hx.const_mul c).congr (Filter.Eventually.of_forall fun x => ?_); simp [mul_assoc]

lemma opWg_add (hD : D.IsOps) {Φ Ψ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) (hΨ : Ψ ∈ Sg D m g) :
    opWg D a (Φ + Ψ) = opWg D a Φ + opWg D a Ψ := by
  ext Y
  simp only [opWg, Pi.add_apply, add_mul]
  rw [integral_add (integrable_Sg hD hΦ Y) (integrable_Sg hD hΨ Y)]
  ring

lemma opWg_mem (hD : D.IsOps) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) : opWg D a Φ ∈ Sg D m g := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opWg_ptG hD]
    exact Submodule.smul_mem _ _ (ptG_mem_Sg (fun i j => Fa_mem hD (hf i j) _))
  | zero => rw [show opWg D a (0 : PtG m g K → ℂ) = 0 by ext; simp [opWg]]; exact zero_mem _
  | add x z hx' hz' hx hz => rw [opWg_add hD hx' hz']; exact add_mem hx hz
  | smul c x _ hx => rw [opWg_smul]; exact Submodule.smul_mem _ c hx

lemma opNg_diag_mem (hD : D.IsOps) (d : Fin g → K) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    opNg D a (diagonal d) Φ ∈ Sg D m g := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opNg_diag_ptG]; exact ptG_mem_Sg (fun i j => hD.chirp_mem _ (hf i j) _)
  | zero => rw [show opNg D a (diagonal d) (0 : PtG m g K → ℂ) = 0 by ext; simp [opNg]]; exact zero_mem _
  | add x z _ _ hx hz => rw [opNg_add_fun]; exact add_mem hx hz
  | smul c x _ hx => rw [opNg_smul]; exact Submodule.smul_mem _ c hx

lemma opMg_diag_mem (hD : D.IsOps) (t : Fin g → Kˣ) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    opMg D a (diagGL t) Φ ∈ Sg D m g := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opMg_diag_ptG]
    exact Submodule.smul_mem _ _ (ptG_mem_Sg (fun i j => hD.dil_mem _ (hf i j) _))
  | zero => rw [show opMg D a (diagGL t) (0 : PtG m g K → ℂ) = 0 by ext; simp [opMg]]; exact zero_mem _
  | add x z _ _ hx hz => rw [opMg_add_fun]; exact add_mem hx hz
  | smul c x _ hx => rw [opMg_smul]; exact Submodule.smul_mem _ c hx

/-! ### Relations on all functions -/

/-- $\omega(n(0)) = 1$. -/
lemma opNg_zero (Φ : PtG m g K → ℂ) : opNg D a 0 Φ = Φ := by
  ext X; simp [opNg]

/-- $\omega(n(B + B')) = \omega(n(B))\omega(n(B'))$. -/
@[kb "kudla1996" "§I.1 (the Schrödinger model is a representation of the Siegel parabolic) [unverified]"]
theorem opNg_add (B B' : Matrix (Fin g) (Fin g) K) (Φ : PtG m g K → ℂ) :
    opNg D a (B + B') Φ = opNg D a B (opNg D a B' Φ) := by
  ext X
  simp only [opNg, add_mul, trace_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

/-- $\omega(m(1)) = 1$. -/
lemma opMg_one (hD : D.IsModel) (Φ : PtG m g K → ℂ) : opMg D a 1 Φ = Φ := by
  ext X
  simp [opMg, chiV_one hD, md_one hD]

/-- $\omega(m(AA')) = \omega(m(A))\omega(m(A'))$. -/
@[kb "kudla1996" "§I.1 (the Schrödinger model is a representation of the Siegel parabolic) [unverified]"]
theorem opMg_mul (hD : D.IsModel) (A A' : GL (Fin g) K) (Φ : PtG m g K → ℂ) :
    opMg D a (A * A') Φ = opMg D a A (opMg D a A' Φ) := by
  obtain ⟨u, hu⟩ := Matrix.isUnits_det_units A
  obtain ⟨u', hu'⟩ := Matrix.isUnits_det_units A'
  ext X
  simp only [opMg, Units.val_mul, det_mul, ← hu, ← hu', chiV_mul hD, hD.md_mul, Matrix.mul_assoc]
  push_cast
  rw [mul_pow]
  ring

/-- $\omega(m(A))\omega(n(B)) = \omega(n(AB\,{}^tA))\omega(m(A))$. -/
@[kb "kudla1996" "§I.1 (the Schrödinger model is a representation of the Siegel parabolic) [unverified]"]
theorem opMg_opNg (A : GL (Fin g) K) (B : Matrix (Fin g) (Fin g) K) (Φ : PtG m g K → ℂ) :
    opMg D a A (opNg D a B Φ) =
      opNg D a ((A : Matrix (Fin g) (Fin g) K) * B * (A : Matrix (Fin g) (Fin g) K)ᵀ) (opMg D a A Φ) := by
  ext X
  have h : trace (B * QX a (X * (A : Matrix (Fin g) (Fin g) K))) =
      trace ((A : Matrix (Fin g) (Fin g) K) * B * (A : Matrix (Fin g) (Fin g) K)ᵀ * QX a X) := by
    have e : QX a (X * (A : Matrix (Fin g) (Fin g) K)) =
        (A : Matrix (Fin g) (Fin g) K)ᵀ * QX a X * (A : Matrix (Fin g) (Fin g) K) := by
      simp only [QX, transpose_mul, Matrix.mul_assoc]
    rw [e, ← Matrix.mul_assoc B, trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [opMg, opNg, h]
  ring

/-! ### Relations on $S(V^g)$ -/

/-! ### Helper lemmas for the relations on $S(V^g)$ -/

lemma ptG_smul_fun (c : Fin (2 * m) → Fin g → ℂ) (f : Fin (2 * m) → Fin g → K → ℂ) :
    ptG (fun i j => c i j • f i j) = (∏ i, ∏ j, c i j) • ptG f := by
  ext X; simp only [ptG, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

lemma chiV_prod_units (hD : D.IsModel) (t : Fin g → Kˣ) :
    D.chiV a (∏ j, (t j : K)) = ∏ j, D.chiV a (t j : K) := by
  let φ : Kˣ →* ℂ :=
    { toFun := fun u => D.chiV a (u : K)
      map_one' := by simpa using chiV_one hD (a := a)
      map_mul' := fun s t => by simpa using chiV_mul hD (a := a) s t }
  have h : D.chiV a (((∏ j, t j : Kˣ)) : K) = ∏ j, D.chiV a (t j : K) := map_prod φ t Finset.univ
  rwa [Units.coe_prod] at h

lemma md_prod_units (hD : D.IsModel) (t : Fin g → Kˣ) :
    D.md (∏ j, (t j : K)) = ∏ j, D.md (t j : K) := by
  let φ : Kˣ →* ℝ :=
    { toFun := fun u => D.md (u : K)
      map_one' := by simpa using md_one hD
      map_mul' := fun s t => by simpa using hD.md_mul s t }
  have h : D.md (((∏ j, t j : Kˣ)) : K) = ∏ j, D.md (t j : K) := map_prod φ t Finset.univ
  rwa [Units.coe_prod] at h

lemma chiV_neg_one_pow (hD : D.IsModel) (n : ℕ) : D.chiV a ((-1 : K) ^ n) = D.chiV a (-1) ^ n := by
  induction n with
  | zero => simpa using chiV_one hD (a := a)
  | succ n ih =>
    have h := chiV_mul hD (a := a) (-1) ((-1 : Kˣ) ^ n)
    simp only [Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val] at h
    rw [pow_succ', pow_succ', h, ih]

lemma md_neg_one_pow (hD : D.IsModel) (n : ℕ) : D.md ((-1 : K) ^ n) = 1 := by
  rcases neg_one_pow_eq_or K n with h | h
  · rw [h]; simpa using md_one hD
  · rw [h]; exact md_neg_one hD

lemma neg_one_eq_diagGL : (-1 : GL (Fin g) K) = diagGL (fun _ => (-1 : Kˣ)) := by
  ext i j
  by_cases h : i = j <;> simp [diagGL_coe, diagonal_apply, Matrix.one_apply, h]

lemma const_col (hD : D.IsModel) (d : Kˣ) :
    D.gammaV a * ∏ i, (D.gN ((a i : K) * d) * ((Real.sqrt (D.md d) : ℂ))⁻¹) =
      D.chiV a (-(d : K)) * ((D.md d : ℂ)⁻¹) ^ m := by
  rw [Finset.prod_mul_distrib, ← mul_assoc, gammaV_mul_prod_gN hD, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hb := hD.md_pos d
  have hs2 : ((Real.sqrt (D.md d) : ℂ)) ^ 2 = D.md d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  rw [pow_mul, inv_pow, hs2, inv_pow]


/-- **$\omega(w)^2 = \omega(m(-1))$ on $S(V^g)$** (Fourier inversion and $\gamma_V^2 = \chi_V(-1)$, once per column). -/
@[kb "weil1964" "§14 (the relation $w^2 = m(-1)$ in the Schrödinger model) [unverified]"]
theorem opWg_opWg (hD : D.IsModel) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    opWg D a (opWg D a Φ) = opMg D a (-1) Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [opWg_ptG hD.toIsOps, opWg_smul, opWg_ptG hD.toIsOps, smul_smul, neg_one_eq_diagGL, opMg_diag_ptG]
    have hF : (fun i j => D.Fa (a i) (D.Fa (a i) (f i j))) = fun i j => dil (((-1 : Kˣ)) : K) (f i j) :=
      funext fun i => funext fun j => by simpa using Fa_Fa hD (hf i j) (a i)
    rw [hF]
    congr 1
    simp only [Units.val_neg, Units.val_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [chiV_neg_one_pow hD, md_neg_one_pow hD, ← pow_add, ← two_mul, pow_mul, ← gammaV_sq hD (a := a)]
    simp [pow_two]
  | zero =>
    rw [show opWg D a (0 : PtG m g K → ℂ) = 0 by ext; simp [opWg],
      show opWg D a (0 : PtG m g K → ℂ) = 0 by ext; simp [opWg]]
    ext; simp [opMg]
  | add x z hx' hz' hx hz =>
    rw [opWg_add hD.toIsOps hx' hz', opWg_add hD.toIsOps (opWg_mem hD.toIsOps hx') (opWg_mem hD.toIsOps hz'),
      opMg_add_fun, hx, hz]
  | smul c x hx' hx => rw [opWg_smul, opWg_smul, opMg_smul, hx]

/-- **The Weil relation for invertible diagonal $D = \operatorname{diag}(d)$ on $S(V^g)$:**
$\omega(w)\omega(n(D))\omega(w) = \omega(n(-D^{-1}))\,\omega(m(-D^{-1}))\,\omega(w)\,\omega(n(-D^{-1}))$
(the one-variable relation (R6) in every coordinate, `Fa_chirp_Fa`, and $\gamma_V\prod_ig(a_id_j) = \chi_V(-d_j)$ per column). -/
@[kb "weil1964" "§14 (the relation $w\\,n(b)\\,w = n(-b^{-1})m(-b^{-1})w\\,n(-b^{-1})$ in the Schrödinger model) [unverified]"]
theorem opWg_opNg_opWg_diag (hD : D.IsModel) (d : Fin g → Kˣ) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    opWg D a (opNg D a (diagonal fun j => (d j : K)) (opWg D a Φ)) =
      opNg D a (-diagonal fun j => (((d j)⁻¹ : Kˣ) : K))
        (opMg D a (-(diagGL d)⁻¹)
          (opWg D a (opNg D a (-diagonal fun j => (((d j)⁻¹ : Kˣ) : K)) Φ))) := by
  have hE : (-diagonal fun j => (((d j)⁻¹ : Kˣ) : K)) = diagonal fun j => (((-(d j)⁻¹ : Kˣ)) : K) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h]
  have hG : (-(diagGL d)⁻¹ : GL (Fin g) K) = diagGL (fun j => -(d j)⁻¹) := by
    ext i j
    rw [Units.val_neg, diagGL_inv_coe]
    by_cases h : i = j <;> simp [diagonal_apply, h]
  rw [hE, hG]
  have hDm := hD.toIsOps
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    simp only [opWg_ptG hDm, opNg_smul, opNg_diag_ptG, opWg_smul, smul_smul, opMg_smul, opMg_diag_ptG]
    have hF : (fun i j => D.Fa (a i) (D.chirp ((d j : K) * a i) (D.Fa (a i) (f i j)))) =
        fun i j => (D.gN ((a i : K) * d j) * ((Real.sqrt (D.md (d j)) : ℂ))⁻¹) •
          D.chirp (-((a i : K) * ((d j)⁻¹ : Kˣ))) (dil (-(((d j)⁻¹ : Kˣ) : K))
            (D.Fa (a i) (D.chirp (-((a i : K) * ((d j)⁻¹ : Kˣ))) (f i j)))) := by
      funext i j
      rw [mul_comm (d j : K), Fa_chirp_Fa hD (hf i j) (a i) (d j)]
    have hF2 : (fun i j => D.chirp (((-(d j)⁻¹ : Kˣ) : K) * a i)
        (dil (((-(d j)⁻¹ : Kˣ)) : K) (D.Fa (a i) (D.chirp (((-(d j)⁻¹ : Kˣ) : K) * a i) (f i j))))) =
        fun i j => D.chirp (-((a i : K) * ((d j)⁻¹ : Kˣ))) (dil (-(((d j)⁻¹ : Kˣ) : K))
            (D.Fa (a i) (D.chirp (-((a i : K) * ((d j)⁻¹ : Kˣ))) (f i j)))) := by
      funext i j
      simp only [Units.val_neg, neg_mul]
      rw [mul_comm (((d j)⁻¹ : Kˣ) : K) (a i)]
    rw [hF, ptG_smul_fun, smul_smul, hF2]
    congr 1
    have hchi : ∀ j, D.chiV a (((-(d j)⁻¹ : Kˣ)) : K) = D.chiV a (-(d j : K)) := fun j => by
      rw [show (-(d j)⁻¹ : Kˣ) = (-d j)⁻¹ by simp, chiV_inv hD]; simp
    have hmd : ∀ j, D.md (((-(d j)⁻¹ : Kˣ)) : K) = (D.md (d j))⁻¹ := fun j => by
      rw [Units.val_neg, md_neg hD, md_inv hD]
    rw [chiV_prod_units hD, md_prod_units hD]
    simp only [hchi, hmd]
    have hL : D.gammaV a ^ g * D.gammaV a ^ g * ∏ i, ∏ j, (D.gN ((a i : K) * d j) * ((Real.sqrt (D.md (d j)) : ℂ))⁻¹)
        = D.gammaV a ^ g * ∏ j, (D.gammaV a * ∏ i, (D.gN ((a i : K) * d j) * ((Real.sqrt (D.md (d j)) : ℂ))⁻¹)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_comm]
      ring
    rw [hL, Finset.prod_congr rfl fun j _ => const_col hD (d j), Finset.prod_mul_distrib]
    push_cast
    rw [Finset.prod_inv_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
  | zero =>
    have h0 : opWg D a (0 : PtG m g K → ℂ) = 0 := by ext; simp [opWg]
    have h1 : ∀ (B : Matrix (Fin g) (Fin g) K), opNg D a B (0 : PtG m g K → ℂ) = 0 := by
      intro B; ext; simp [opNg]
    have h2 : ∀ (A : GL (Fin g) K), opMg D a A (0 : PtG m g K → ℂ) = 0 := by
      intro A; ext; simp [opMg]
    simp only [h0, h1, h2]
  | add x z hx' hz' hx hz =>
    rw [opWg_add hDm hx' hz', opNg_add_fun, opWg_add hDm (opNg_diag_mem hDm _ (opWg_mem hDm hx'))
      (opNg_diag_mem hDm _ (opWg_mem hDm hz')), hx, hz, opNg_add_fun,
      opWg_add hDm (opNg_diag_mem hDm _ hx') (opNg_diag_mem hDm _ hz'), opMg_add_fun, opNg_add_fun]
  | smul c x hx' hx =>
    rw [opWg_smul, opNg_smul, opWg_smul, hx, opNg_smul, opWg_smul, opMg_smul, opNg_smul]


lemma integral_ptG (hD : D.IsOps) (f : Fin (2 * m) → Fin g → K → ℂ) (Y : PtG m g K) :
    ∫ X, ptG f X * (D.ψ (BX a X Y) : ℂ) ∂muG D m g = ∏ i, ∏ j, D.four (f i j) (2 * (a i : K) * Y i j) := by
  haveI := hD.sigmaFinite
  have h : (fun X => ptG f X * (D.ψ (BX a X Y) : ℂ)) = fun X : PtG m g K =>
      ∏ i, ∏ j, (f i j (X i j) * (D.ψ (X i j * (2 * (a i : K) * Y i j)) : ℂ)) := by
    ext X; simp only [ptG, psi_BX, ← Finset.prod_mul_distrib]
  rw [h]
  have h0 : ∫ X : PtG m g K, ∏ i, ∏ j, (f i j (X i j) * (D.ψ (X i j * (2 * (a i : K) * Y i j)) : ℂ))
      ∂(muG D m g) =
      ∏ i, ∫ x : Fin g → K, ∏ j, (f i j (x j) * (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ))
        ∂(Measure.pi fun _ => D.μ) :=
    integral_fintype_prod_eq_prod (fun i (x : Fin g → K) => ∏ j, (f i j (x j) *
      (D.ψ (x j * (2 * (a i : K) * Y i j)) : ℂ)))
  rw [h0]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact integral_fintype_prod_eq_prod (fun j x => f i j x * (D.ψ (x * (2 * (a i : K) * Y i j)) : ℂ))

lemma ptG_mul_diagGL (d : Fin g → Kˣ) (f : Fin (2 * m) → Fin g → K → ℂ) :
    (fun X => ptG f (X * ((diagGL d : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))) =
      ptG (fun i j => dil (d j : K) (f i j)) := by
  ext X
  simp only [ptG, dil, diagGL_coe, mul_diagonal]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma comp_diagGL_mem (hD : D.IsOps) (d : Fin g → Kˣ) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g) :
    (fun X => Φ (X * ((diagGL d : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))) ∈ Sg D m g := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    rw [ptG_mul_diagGL]
    exact ptG_mem_Sg (fun i j => hD.dil_mem _ (hf i j) _)
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

lemma invT_diagGL_coe (d : Fin g → Kˣ) :
    ((invT (diagGL d) : GL (Fin g) K) : Matrix (Fin g) (Fin g) K) = diagonal fun j => (((d j)⁻¹ : Kˣ) : K) := by
  rw [invT_coe, diagGL_inv_coe, diagonal_transpose]

lemma four_comp_diagGL (hD : D.IsModel) (d : Fin g → Kˣ) {Φ : PtG m g K → ℂ} (hΦ : Φ ∈ Sg D m g)
    (Y : PtG m g K) :
    ∫ X, Φ (X * ((diagGL d : GL (Fin g) K) : Matrix (Fin g) (Fin g) K)) * (D.ψ (BX a X Y) : ℂ) ∂muG D m g =
      ((D.md ((diagGL d : GL (Fin g) K) : Matrix (Fin g) (Fin g) K).det : ℂ)⁻¹) ^ (2 * m) *
        ∫ X, Φ X * (D.ψ (BX a X (Y * ((invT (diagGL d) : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))) : ℂ)
          ∂muG D m g := by
  have hDm := hD.toIsOps
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have e := congrFun (ptG_mul_diagGL (m := m) d f)
    simp only [e]
    rw [integral_ptG hDm, integral_ptG hDm, invT_diagGL_coe]
    have hc : ∀ i j, D.four (dil (d j : K) (f i j)) (2 * (a i : K) * Y i j) =
        (D.md (d j : K) : ℂ)⁻¹ * D.four (f i j) (2 * (a i : K) * (Y * diagonal fun j => (((d j)⁻¹ : Kˣ) : K)) i j) := by
      intro i j
      rw [hD.four_dil _ (hf i j), mul_diagonal]
      congr 2
      ring
    simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [diagGL_coe, det_diagonal, md_prod_units hD, ← Finset.prod_pow]
    push_cast
    rw [Finset.prod_pow, Finset.prod_inv_distrib]
  | zero => simp
  | add x z hx' hz' hx hz =>
    have h1 := integrable_Sg (a := a) hDm (comp_diagGL_mem hDm d hx') Y
    have h2 := integrable_Sg (a := a) hDm (comp_diagGL_mem hDm d hz') Y
    have h3 := integrable_Sg (a := a) hDm hx'
      (Y * ((invT (diagGL d) : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))
    have h4 := integrable_Sg (a := a) hDm hz'
      (Y * ((invT (diagGL d) : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))
    simp only [Pi.add_apply, add_mul] at *
    rw [integral_add h1 h2, integral_add h3 h4, hx, hz, mul_add]
  | smul c x hx' hx =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul] at *
    rw [hx]; ring

lemma exists_diagGL_one (A : GL (Fin 1) K) : ∃ t : Kˣ, A = diagGL (fun _ => t) := by
  refine ⟨Matrix.GeneralLinearGroup.det A, ?_⟩
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [diagGL_coe, Matrix.GeneralLinearGroup.det, det_unique]

/-! ### The interface `IsGLModel` and the relation $w\,m(A) = m({}^tA^{-1})\,w$ -/

/-- **$S(V^g)$ is a $\mathrm{GL}_g$-model** (interface): $S(V^g)$ is stable under $\omega(n(B))$ (symmetric $B$) and
$\omega(m(A))$ (all $A \in \mathrm{GL}_g(K)$), and the Fourier transform satisfies the change of variables
$$\int\Phi(XA)\,\psi(\langle X, Y\rangle)\,d\mu(X) = |\det A|^{-n}\int\Phi(X)\,\psi(\langle X, Y\,{}^tA^{-1}\rangle)\,d\mu(X)
  \qquad(\Phi \in S(V^g)),$$
$n = 2m$ (the map $X \mapsto XA$ has modulus $|\det A|^n$ on $V^g = (K^g)^n$). Fields:
* `opN_mem`: $\omega(n(B))S(V^g) \subseteq S(V^g)$ for symmetric $B$;
* `opM_mem`: $\omega(m(A))S(V^g) \subseteq S(V^g)$;
* `four_comp`: the change of variables above.
It holds for $g = 1$ in every model (`isGLModel_one`); at a finite place it holds for every $g$ because $S(V^g)$ is
then all locally constant compactly supported functions. -/
@[kb "weil1964" "§14 ($\\mathcal S(X)$ is stable under $\\mathrm{GL}(X)$; the modulus of $X \\mapsto XA$) [unverified]"]
structure IsGLModel (D : LocalData K) (a : Fin (2 * m) → Kˣ) (g : ℕ) : Prop where
  opN_mem : ∀ B : Matrix (Fin g) (Fin g) K, Bᵀ = B → ∀ Φ ∈ Sg D m g, opNg D a B Φ ∈ Sg D m g
  opM_mem : ∀ A : GL (Fin g) K, ∀ Φ ∈ Sg D m g, opMg D a A Φ ∈ Sg D m g
  four_comp : ∀ (A : GL (Fin g) K), ∀ Φ ∈ Sg D m g, ∀ Y : PtG m g K,
    ∫ X, Φ (X * (A : Matrix (Fin g) (Fin g) K)) * (D.ψ (BX a X Y) : ℂ) ∂muG D m g =
      ((D.md (A : Matrix (Fin g) (Fin g) K).det : ℂ)⁻¹) ^ (2 * m) *
        ∫ X, Φ X * (D.ψ (BX a X (Y * (invT A : Matrix (Fin g) (Fin g) K))) : ℂ) ∂muG D m g

/-- **$\omega(w)\omega(m(A)) = \omega(m({}^tA^{-1}))\omega(w)$ on $S(V^g)$** (change of variables and $\chi_V(t^{-1}) = \chi_V(t)$). -/
@[kb "weil1964" "§14 (the relation $w\\,m(a) = m({}^ta^{-1})\\,w$ in the Schrödinger model) [unverified]"]
theorem opWg_opMg (hD : D.IsModel) (hGL : IsGLModel D a g) (A : GL (Fin g) K) {Φ : PtG m g K → ℂ}
    (hΦ : Φ ∈ Sg D m g) :
    opWg D a (opMg D a A Φ) = opMg D a (invT A) (opWg D a Φ) := by
  obtain ⟨u, hu⟩ := Matrix.isUnits_det_units A
  have h1 : Matrix.det ((A⁻¹ : GL (Fin g) K) : Matrix (Fin g) (Fin g) K) *
      Matrix.det (A : Matrix (Fin g) (Fin g) K) = 1 := by
    rw [← det_mul, Units.inv_mul, det_one]
  have hdet : Matrix.det ((invT A : GL (Fin g) K) : Matrix (Fin g) (Fin g) K) = ((u⁻¹ : Kˣ) : K) := by
    rw [invT_coe, det_transpose]
    have huv : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
    rw [← hu] at h1
    linear_combination (-(Matrix.det ((A⁻¹ : GL (Fin g) K) : Matrix (Fin g) (Fin g) K))) * huv
      + ((u⁻¹ : Kˣ) : K) * h1
  ext Y
  have hmd : (D.md (u : K) : ℂ) ≠ 0 := by exact_mod_cast (hD.md_pos u).ne'
  have hI := hGL.four_comp A Φ hΦ Y
  simp only [opWg, opMg, hdet, mul_assoc, integral_const_mul]
  rw [hI, ← hu, chiV_inv hD, md_inv hD]
  push_cast
  generalize (∫ X : PtG m g K, Φ X * ((D.ψ (BX a X (Y * ((invT A : GL (Fin g) K) :
    Matrix (Fin g) (Fin g) K))) : Circle) : ℂ) ∂muG D m g) = J
  rw [show 2 * m = m + m by ring, pow_add]
  field_simp
  simp only [one_div, inv_pow]
  field_simp

/-- **The interface holds in genus one** (stability under $D_t$ and chirps; $\mathcal F(D_tf) = |t|^{-1}D_{t^{-1}}\mathcal Ff$). -/
@[kb "weil1964" "§14 (genus one) [unverified]"]
theorem isGLModel_one (hD : D.IsModel) : IsGLModel D a 1 where
  opN_mem B _ Φ hΦ := by
    have : B = diagonal fun _ => B 0 0 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj; simp
    rw [this]; exact opNg_diag_mem hD.toIsOps _ hΦ
  opM_mem A Φ hΦ := by
    obtain ⟨t, rfl⟩ := exists_diagGL_one A
    exact opMg_diag_mem hD.toIsOps _ hΦ
  four_comp A Φ hΦ Y := by
    obtain ⟨t, rfl⟩ := exists_diagGL_one A
    exact four_comp_diagGL hD _ hΦ Y

/-! ### The operators as endomorphisms of $S(V^g)$ and the relations of $\mathrm{Sp}_{2g}(k)$ -/

section Endo

variable (hD : D.IsModel) (hGL : IsGLModel D a g) {k : Type*} [Field k] (ι : k →+* K)

open Classical in
/-- $\omega(n(\iota B))$ on $S(V^g)$ for symmetric $B \in M_g(k)$ (the identity for non-symmetric $B$, a junk value). -/
def endN (B : Matrix (Fin g) (Fin g) k) : Module.End ℂ (Sg D m g) :=
  if hB : Bᵀ = B then
    { toFun := fun Φ => ⟨opNg D a (B.map ι) Φ, hGL.opN_mem _ (by rw [← transpose_map, hB]) Φ Φ.2⟩
      map_add' := fun Φ Ψ => Subtype.ext (opNg_add_fun _ Φ.1 Ψ.1)
      map_smul' := fun c Φ => Subtype.ext (opNg_smul _ c Φ.1) }
  else 1

/-- $\omega(m(\iota A))$ on $S(V^g)$ for $A \in \mathrm{GL}_g(k)$. -/
def endM (A : GL (Fin g) k) : Module.End ℂ (Sg D m g) where
  toFun Φ := ⟨opMg D a (Matrix.GeneralLinearGroup.map ι A) Φ, hGL.opM_mem _ Φ Φ.2⟩
  map_add' Φ Ψ := Subtype.ext (opMg_add_fun _ Φ.1 Ψ.1)
  map_smul' c Φ := Subtype.ext (opMg_smul _ c Φ.1)

/-- $\omega(w)$ on $S(V^g)$. -/
def endW : Module.End ℂ (Sg D m g) where
  toFun Φ := ⟨opWg D a Φ, opWg_mem hD.toIsOps Φ.2⟩
  map_add' Φ Ψ := Subtype.ext (opWg_add hD.toIsOps Φ.2 Ψ.2)
  map_smul' c Φ := Subtype.ext (opWg_smul c Φ.1)

lemma endN_apply {B : Matrix (Fin g) (Fin g) k} (hB : Bᵀ = B) (Φ : Sg D m g) :
    ((endN hGL ι B Φ : Sg D m g) : PtG m g K → ℂ) = opNg D a (B.map ι) Φ := by
  simp [endN, hB]

@[simp] lemma endM_apply (A : GL (Fin g) k) (Φ : Sg D m g) :
    ((endM hGL ι A Φ : Sg D m g) : PtG m g K → ℂ) = opMg D a (Matrix.GeneralLinearGroup.map ι A) Φ := rfl

@[simp] lemma endW_apply (Φ : Sg D m g) : ((endW (a := a) hD Φ : Sg D m g) : PtG m g K → ℂ) = opWg D a Φ := rfl

/-- **The Schrödinger operators satisfy the relations of $\mathrm{Sp}_{2g}(k)$** (`SiegelRelations`), for a field $k$
with $2 \ne 0$ and a ring map $\iota : k \to K$: the parabolic relations pointwise, $w\,m(A) = m({}^tA^{-1})w$ by the change
of variables, $w^2 = m(-1)$ by Fourier inversion, and the Weil relation for every invertible symmetric $B$ by
diagonalizing $B$ over $k$ and the diagonal case (`siegelRelations_of_diag`). -/
@[kb "weil1964" "§14, Thm. 2 (the operators $r(s)$ for $s$ in the generators satisfy the relations of $\\mathrm{Sp}$) [unverified]"]
theorem siegelRelations_omega (h2 : (2 : k) ≠ 0) :
    SiegelRelations (endN hGL ι) (endM hGL ι) (endW (a := a) (g := g) hD) := by
  have hdsymm : ∀ d : Fin g → kˣ, (diagonal fun j => (d j : k))ᵀ = diagonal fun j => (d j : k) :=
    fun d => diagonal_transpose _
  have hdsymm' : ∀ d : Fin g → kˣ, (-diagonal fun j => (((d j)⁻¹ : kˣ) : k))ᵀ =
      -diagonal fun j => (((d j)⁻¹ : kˣ) : k) := fun d => by rw [transpose_neg, diagonal_transpose]
  have hmapGL : ∀ A : GL (Fin g) k, ((Matrix.GeneralLinearGroup.map ι A : GL (Fin g) K) : Matrix (Fin g) (Fin g) K) =
      (A : Matrix (Fin g) (Fin g) k).map ι := fun A => rfl
  refine siegelRelations_of_diag h2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [endN_apply hGL ι (by simp), Matrix.map_zero _ (map_zero ι)]
    exact opNg_zero _
  · intro B B' hB hB'
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, endN_apply hGL ι (by rw [transpose_add, hB, hB']), endN_apply hGL ι hB,
      endN_apply hGL ι hB', Matrix.map_add _ (map_add ι)]
    exact opNg_add _ _ _
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [endM_apply, map_one]
    exact opMg_one hD _
  · intro A A'
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, endM_apply, endM_apply, endM_apply, map_mul]
    exact opMg_mul hD _ _ _
  · intro A B hB
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    have hs : ((A : Matrix (Fin g) (Fin g) k) * B * (A : Matrix (Fin g) (Fin g) k)ᵀ)ᵀ =
        (A : Matrix (Fin g) (Fin g) k) * B * (A : Matrix (Fin g) (Fin g) k)ᵀ := by
      simp [transpose_mul, hB, Matrix.mul_assoc]
    simp only [Module.End.mul_apply, endM_apply, endN_apply hGL ι hB, endN_apply hGL ι hs]
    rw [opMg_opNg, hmapGL, Matrix.map_mul, Matrix.map_mul, transpose_map]
  · intro A
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, endW_apply, endM_apply, endM_apply, endW_apply,
      opWg_opMg hD hGL _ (Φ.2)]
    congr 2
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    have h1 : Matrix.GeneralLinearGroup.map ι (-1 : GL (Fin g) k) = -1 := by
      ext i j; simp [Matrix.GeneralLinearGroup.map]
    rw [Module.End.mul_apply, endW_apply, endW_apply, endM_apply, h1]
    exact opWg_opWg hD Φ.2
  · intro d
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    simp only [Module.End.mul_apply, endW_apply, endM_apply, endN_apply hGL ι (hdsymm d),
      endN_apply hGL ι (hdsymm' d)]
    have e1 : (diagonal fun j => (d j : k)).map ι = diagonal fun j => ((Units.map (ι : k →* K) (d j) : Kˣ) : K) := by
      rw [diagonal_map (map_zero ι)]; rfl
    have e2 : (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)).map ι =
        -diagonal fun j => ((((Units.map (ι : k →* K) (d j))⁻¹ : Kˣ)) : K) := by
      rw [Matrix.map_neg _ (map_neg ι), diagonal_map (map_zero ι)]; simp
    have e3 : Matrix.GeneralLinearGroup.map ι (-(diagGL d)⁻¹) = -(diagGL fun j => Units.map (ι : k →* K) (d j))⁻¹ := by
      ext i j
      simp [Matrix.GeneralLinearGroup.map, diagGL, diagonal_apply]
    rw [e1, e2, e3]
    exact opWg_opNg_opWg_diag hD (fun j => Units.map (ι : k →* K) (d j)) Φ.2

/-- **The Weil representation of $\mathrm{Sp}_{2g}(k)$ on $S(V^g)$** (Schrödinger model), conditional on the named input
`SiegelPresentation` (proved for $g = 1$, `siegelPresentation_one`): the monoid homomorphism with
$\omega(n(B)) = $ `opNg`, $\omega(m(A)) = $ `opMg`, $\omega(w) = $ `opWg` on the generators. No cocycle: $n = 2m$ is even. -/
@[kb "weil1964" "§14, Thm. 2 and §43 (for even $\\dim V$ the Weil representation is a representation of $\\mathrm{Sp}$) [unverified]"]
def weilRepSp (hP : SiegelPresentation.{u_1} g k) (h2 : (2 : k) ≠ 0) :
    Sp g k →* Module.End ℂ (Sg D m g) :=
  Classical.choose (hP.extend _ _ _ _ (siegelRelations_omega hD hGL ι h2))

theorem weilRepSp_spN (hP : SiegelPresentation.{u_1} g k) (h2 : (2 : k) ≠ 0) (B : Matrix (Fin g) (Fin g) k)
    (hB : Bᵀ = B) : weilRepSp hD hGL ι hP h2 (spN B hB) = endN hGL ι B :=
  (Classical.choose_spec (hP.extend _ _ _ _ (siegelRelations_omega hD hGL ι h2))).1 B hB

theorem weilRepSp_spM (hP : SiegelPresentation.{u_1} g k) (h2 : (2 : k) ≠ 0) (A : GL (Fin g) k) :
    weilRepSp hD hGL ι hP h2 (spM A) = endM hGL ι A :=
  (Classical.choose_spec (hP.extend _ _ _ _ (siegelRelations_omega hD hGL ι h2))).2.1 A

theorem weilRepSp_spW (hP : SiegelPresentation.{u_1} g k) (h2 : (2 : k) ≠ 0) :
    weilRepSp hD hGL ι hP h2 spW = endW (a := a) hD :=
  (Classical.choose_spec (hP.extend _ _ _ _ (siegelRelations_omega hD hGL ι h2))).2.2

end Endo

end QuadFormsKB.WeilRep.Genus
