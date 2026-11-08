/-
# Hanke 2013, §2.1: dual lattices and modular lattices

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`).

**Setting.** The paper works over a number field $F$ with ring of integers $\mathcal O_F$. Here $R$ is a Dedekind
domain with fraction field $F$ in which $2$ is invertible (for a number field, $R = \mathcal O_F$). The paper's
bilinear space $(V, B)$ is encoded, as in O'Meara's book, by the quadratic form $Q = Q_B$, $Q_B(x) = B(x, x)$, on the
finite-dimensional $F$-vector space $V$: then O'Meara's bilinear form `OMeara.bil Q` is $B$ (since $2 \in F^\times$).
A *lattice in $V$* is a finitely generated $R$-submodule $L$ with $FL = V$ (Mathlib's `Submodule.IsLattice F L`); a
(non-zero) *fractional ideal* $\mathfrak a$ is a non-zero finitely generated $R$-submodule of $F$; $\mathfrak aL$ is
`a • L` and $\mathfrak a^{-1}$ is `1 / a`. The space is *non-degenerate* when
`(QuadraticMap.associated Q).Nondegenerate`.

**Defines** a-valued bilinear lattices (`IsAValued`: $B(L, L) \subseteq \mathfrak a$, i.e. O'Meara's scale
$\mathfrak sL \subseteq \mathfrak a$), the $\mathfrak a$-dual $L^{\#\mathfrak a}$ (`aDual`, **Definition 2.1**) and
$\mathfrak a$-modular lattices (`IsAModular`, **Definition 2.5**).

**Proves** Lemmas **2.2**, **2.3**, **2.4**, **2.6**, **2.7**, Remark **2.8** (comparison with O'Meara's
$\mathfrak a$-modular lattices, `OMeara.IsModular`) and the polarization identity **Lemma 2.9** (over any commutative
ring).
-/
import QuadFormsKB.Literature.OMeara.Sec82Max
import QuadFormsKB.Citation

open QuadraticMap Submodule Module
open scoped Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$\mathfrak a$-valued bilinear lattice** (Hanke 2013, §2, p. 4, used in Lemma 2.2): $B(L, L) \subseteq \mathfrak a$,
where $B$ = `bil Q` is the bilinear form with $B(x, x) = Q(x)$. Equivalently O'Meara's scale satisfies
$\mathfrak sL \subseteq \mathfrak a$ (`scale`; Remark 2.8). -/
@[kb "hanke2013algorithms" "§2.1, p. 4 (a-valued bilinear lattice B(L, L) ⊆ a)"]
def IsAValued (a : Submodule R F) (L : Submodule R V) : Prop :=
  scale Q L ≤ a

/-- **The $\mathfrak a$-dual lattice** (Hanke 2013, Definition 2.1, p. 4):
$L^{\#\mathfrak a} := \{v \in V : B(v, L) \subseteq \mathfrak a\}$, for an $R$-submodule $L$ of $V$ and an
$R$-submodule $\mathfrak a$ of $F$ (in the paper $L$ is a lattice and $\mathfrak a$ a non-zero fractional ideal). For
$\mathfrak a = \mathcal O_F$ it is the dual lattice $L^\#$ (`OMeara.dual`, see `aDual_one`). -/
@[kb "hanke2013algorithms" "Definition 2.1, p. 4"]
def aDual (a : Submodule R F) (L : Submodule R V) : Submodule R V where
  carrier := {v | ∀ y ∈ L, bil Q v y ∈ a}
  add_mem' := by
    intro x x' hx hx' y hy
    rw [bil_add_left]; exact add_mem (hx y hy) (hx' y hy)
  zero_mem' := by intro y _; simp [bil]
  smul_mem' := by
    intro c x hx y hy
    rw [bil_rsmul_left, ← Algebra.smul_def]; exact a.smul_mem c (hx y hy)

theorem mem_aDual {a : Submodule R F} {L : Submodule R V} {v : V} :
    v ∈ aDual Q a L ↔ ∀ y ∈ L, bil Q v y ∈ a := Iff.rfl

/-- **$\mathfrak a$-modular lattice** (Hanke 2013, Definition 2.5, p. 5): $L^{\#\mathfrak a} = L$ (the paper's
equivalent form of $L^\# = \mathfrak a^{-1}L$, see `isAModular_iff_dual_eq`). -/
@[kb "hanke2013algorithms" "Definition 2.5, p. 5"]
def IsAModular (a : Submodule R F) (L : Submodule R V) : Prop :=
  aDual Q a L = L

/-- **Lemma 2.2** (Hanke 2013, p. 4): $L$ is $\mathfrak a$-valued if and only if $L \subseteq L^{\#\mathfrak a}$.
(The paper's hypotheses that $V$ is non-degenerate and $L$ a lattice are not needed.) -/
@[kb "hanke2013algorithms" "Lemma 2.2, p. 4"]
theorem lemma_2_2 {a : Submodule R F} {L : Submodule R V} :
    IsAValued Q a L ↔ L ≤ aDual Q a L := by
  constructor
  · intro h x hx y hy; exact h (bil_mem_scale Q hx hy)
  · intro h
    rw [IsAValued, scale, span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact h hx y hy

theorem aDual_anti {a : Submodule R F} {K L : Submodule R V} (h : K ≤ L) : aDual Q a L ≤ aDual Q a K :=
  fun _ hv y hy => hv y (h hy)

theorem aDual_mono_ideal {a b : Submodule R F} (h : a ≤ b) (L : Submodule R V) : aDual Q a L ≤ aDual Q b L :=
  fun _ hv y hy => h (hv y hy)

/-- $B(v, w) \in \mathfrak a$ for $v \in L^{\#\mathfrak a}$ and $w \in L$, in either order. -/
theorem bil_mem_of_mem_aDual_left {a : Submodule R F} {L : Submodule R V} {v w : V} (hv : v ∈ aDual Q a L)
    (hw : w ∈ L) : bil Q w v ∈ a := by
  rw [bil_comm]; exact hv w hw

end Defs

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- For a lattice $L$ in $V$, the $\mathcal O_F$-dual is O'Meara's dual $L^\#$ (`OMeara.dual`). -/
theorem aDual_one {L : Submodule R V} (hL : L.IsLattice F) : aDual Q 1 L = dual Q L := by
  ext v
  exact ⟨fun h => ⟨by rw [hL.span_eq_top]; trivial, h⟩, fun h => h.2⟩

/-- **Lemma 2.3, first part** (Hanke 2013, p. 5): $L^{\#\mathfrak a} = \mathfrak aL^\#$ for a lattice $L$ in $V$ and a
non-zero fractional ideal $\mathfrak a$ (non-degeneracy is not needed). -/
@[kb "hanke2013algorithms" "Lemma 2.3, p. 5 (L^{#a} = aL^#)"]
theorem aDual_eq_smul_dual {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V}
    (hL : L.IsLattice F) : aDual Q a L = a • dual Q L := by
  apply le_antisymm
  · have h1 : (1 / a) • aDual Q a L ≤ dual Q L := by
      rw [Submodule.smul_le]
      intro β hβ v hv
      refine ⟨by rw [hL.span_eq_top]; trivial, fun y hy => ?_⟩
      rw [bil_smul_left]
      have := mul_mem_mul hβ (hv y hy)
      rwa [mul_comm (1 / a) a, mul_one_div_cancel_of_fg ha ha0] at this
    calc aDual Q a L = a • (1 / a) • aDual Q a L := (smul_inv_smul_max ha ha0 _).symm
      _ ≤ a • dual Q L := Submodule.smul_mono le_rfl h1
  · rw [Submodule.smul_le]
    intro α hα m hm y hy
    rw [bil_smul_left]
    have := mul_mem_mul hα (hm.2 y hy)
    rwa [mul_one] at this

/-- The dual of a lattice in a non-degenerate space is a lattice. -/
theorem isLattice_dual (hV : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V}
    (hL : L.IsLattice F) : (dual Q L).IsLattice F := by
  have hreg := isRegular_of_lattice_max Q hV hL
  exact ⟨dual_fg Q hL.fg hreg, by rw [span_dual Q hL.fg hreg, hL.span_eq_top]⟩

/-- The $\mathfrak a$-dual of a lattice in a non-degenerate space is a lattice (Hanke 2013, Definition 2.1: "the
$\mathcal O_F$-lattice $L^{\#\mathfrak a}$"). -/
theorem isLattice_aDual (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) : (aDual Q a L).IsLattice F := by
  rw [aDual_eq_smul_dual Q ha ha0 hL]
  exact isLattice_smul_max ha ha0 (isLattice_dual Q hV hL)

/-- **Lemma 2.3, second part** (Hanke 2013, p. 5): $(\mathfrak bL)^\# = L^{\#\mathfrak b^{-1}}$ for a lattice $L$ in a
non-degenerate space and a non-zero fractional ideal $\mathfrak b$. -/
@[kb "hanke2013algorithms" "Lemma 2.3, p. 5 ((bL)^# = L^{#b⁻¹})"]
theorem dual_smul_eq_aDual (hV : (QuadraticMap.associated Q).Nondegenerate) {b : Submodule R F} (hb : b.FG)
    (hb0 : b ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) : dual Q (b • L) = aDual Q (1 / b) L := by
  obtain ⟨hif, hin⟩ := one_div_fg hb hb0
  rw [dual_smul Q hb hb0 hL.fg (isRegular_of_lattice_max Q hV hL), aDual_eq_smul_dual Q hif hin hL]

/-- **Lemma 2.4** (Hanke 2013, p. 5): $(L^{\#\mathfrak a})^{\#\mathfrak a} = L$ for a lattice $L$ in a non-degenerate
space and a non-zero fractional ideal $\mathfrak a$. -/
@[kb "hanke2013algorithms" "Lemma 2.4, p. 5"]
theorem lemma_2_4 (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) : aDual Q a (aDual Q a L) = L := by
  have hreg := isRegular_of_lattice_max Q hV hL
  have hD := isLattice_dual Q hV hL
  rw [aDual_eq_smul_dual Q ha ha0 (isLattice_aDual Q hV ha ha0 hL), aDual_eq_smul_dual Q ha ha0 hL,
    dual_smul Q ha ha0 hD.fg (isRegular_dual Q hL.fg hreg), dual_dual Q hL.fg hreg, smul_inv_smul_max ha ha0]

/-- A lattice in a non-zero space is non-zero. -/
theorem ne_bot_of_isLattice [Nontrivial V] {L : Submodule R V} (hL : L.IsLattice F) : L ≠ ⊥ := by
  intro h
  have h1 := hL.span_eq_top
  rw [h] at h1
  simp at h1

/-- **Definition 2.5, the equivalence** (Hanke 2013, p. 5): $L^\# = \mathfrak a^{-1}L$ if and only if
$L^{\#\mathfrak a} = L$. -/
@[kb "hanke2013algorithms" "Definition 2.5, p. 5 (L^# = a⁻¹L ⇔ L^{#a} = L)"]
theorem isAModular_iff_dual_eq {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V}
    (hL : L.IsLattice F) : IsAModular Q a L ↔ dual Q L = (1 / a) • L := by
  rw [IsAModular, aDual_eq_smul_dual Q ha ha0 hL]
  constructor
  · intro h; conv_rhs => rw [← h]
    rw [inv_smul_smul_max ha ha0]
  · intro h; rw [h, smul_inv_smul_max ha ha0]

/-- **Remark 2.8, modular lattices** (Hanke 2013, p. 5): the paper's $\mathfrak a$-modular lattices are O'Meara's
(`OMeara.IsModular`: $\mathfrak sL = \mathfrak a$ and $\mathfrak vL = \mathfrak a^n$), by O'Meara 82:14. Here $L$ is a
lattice in a non-degenerate space $V \ne 0$. *Update:* for $V = 0$ the paper's definition makes the zero lattice
$\mathfrak a$-modular for every $\mathfrak a$, and Lemma 2.6 fails ($B(L, L) = 0 \ne \mathfrak a$); O'Meara's
definition excludes it. -/
@[kb "hanke2013algorithms" "Remark 2.8, p. 5 (a-modular coincides with O'Meara's, 82:14)"]
theorem isAModular_iff_isModular [Nontrivial V] (hV : (QuadraticMap.associated Q).Nondegenerate)
    {a : Submodule R F} (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) :
    IsAModular Q a L ↔ IsModular Q a L := by
  rw [isModular_iff_smul_dual Q hL.fg (ne_bot_of_isLattice hL) (isRegular_of_lattice_max Q hV hL) ha ha0,
    IsAModular, aDual_eq_smul_dual Q ha ha0 hL]

/-- **Remark 2.8, value ideals** (Hanke 2013, p. 5): the bilinear value ideal $B(L, L)$, i.e. the $R$-module generated
by the values $B(x, y)$, $x, y \in L$, is O'Meara's scale $\mathfrak sL$ (by definition of `OMeara.scale`). (The
remark's last point, that O'Meara's scaling $L^\alpha$ rescales the form while the paper scales the lattice, has no
formal content.) -/
@[kb "hanke2013algorithms" "Remark 2.8, p. 5 (B(L, L) is O'Meara's scale)"]
theorem remark_2_8_scale (L : Submodule R V) :
    scale Q L = span R (Set.image2 (bil Q) (L : Set V) (L : Set V)) := rfl

/-- **Lemma 2.6** (Hanke 2013, p. 5): an $\mathfrak a$-modular lattice $L$ in a non-degenerate space $V \ne 0$ has
bilinear value ideal $B(L, L) = \mathfrak a$. (The hypothesis $V \ne 0$ is needed, see `isAModular_iff_isModular`.) -/
@[kb "hanke2013algorithms" "Lemma 2.6, p. 5"]
theorem lemma_2_6 [Nontrivial V] (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F}
    (ha : a.FG) (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hmod : IsAModular Q a L) :
    scale Q L = a :=
  ((isAModular_iff_isModular Q hV ha ha0 hL).1 hmod).2.1

/-- **Lemma 2.7** (Hanke 2013, p. 5): if $L$ is $\mathfrak a$-modular then $\mathfrak bL$ is
$\mathfrak b^2\mathfrak a$-modular, for a lattice $L$ in a non-degenerate space and non-zero fractional ideals
$\mathfrak a$, $\mathfrak b$. -/
@[kb "hanke2013algorithms" "Lemma 2.7, p. 5"]
theorem lemma_2_7 (hV : (QuadraticMap.associated Q).Nondegenerate) {a b : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) (hb : b.FG) (hb0 : b ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F)
    (hmod : IsAModular Q a L) : IsAModular Q (b ^ 2 * a) (b • L) := by
  have hreg := isRegular_of_lattice_max Q hV hL
  have hba : (b ^ 2 * a).FG := (hb.pow 2).mul ha
  have hba0 : b ^ 2 * a ≠ ⊥ := mul_ne_bot' (pow_fg_ne_bot hb hb0 2).2 ha0
  have hbL := isLattice_smul_max hb hb0 hL
  rw [IsAModular, aDual_eq_smul_dual Q hba hba0 hbL, dual_smul Q hb hb0 hL.fg hreg, ← mul_smul_submodule]
  have : b ^ 2 * a * (1 / b) = b * a := by
    calc b ^ 2 * a * (1 / b) = b * a * (b * (1 / b)) := by ring
      _ = b * a := by rw [mul_one_div_cancel_of_fg hb hb0, mul_one]
  rw [this, mul_smul_submodule, ← aDual_eq_smul_dual Q ha ha0 hL, hmod]

end Dedekind

section Polarization

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Lemma 2.9, polarization identity** (Hanke 2013, p. 6). For a quadratic form $Q$ in $n$ variables over a
commutative ring $R$, the Hessian bilinear form $H(x, y) := Q(x + y) - Q(x) - Q(y)$ (Mathlib's `QuadraticMap.polar`)
satisfies $Q(x + y) = Q(x) + H(x, y) + Q(y)$, $H(x, x) = 2Q(x)$, and $H(x, y) = x^tAy$ for the symmetric matrix
$A = (H(e_i, e_j))_{i,j}$, $e_i$ the standard basis vectors (indices $0, \dots, n-1$); $A$ is the matrix of second
partial derivatives of $Q$, see `lemma_2_9_hessian`. -/
@[kb "hanke2013algorithms" "Lemma 2.9, p. 6"]
theorem lemma_2_9 (Q : QuadraticMap R (Fin n → R) R) (x y : Fin n → R) :
    Q (x + y) = Q x + polar Q x y + Q y ∧ polar Q x x = 2 * Q x ∧
    polar Q x y = x ⬝ᵥ (Matrix.of (fun i j => polar Q (Pi.single i 1) (Pi.single j 1)) *ᵥ y) ∧
    (Matrix.of (fun i j => polar Q (Pi.single i 1) (Pi.single j 1))).IsSymm := by
  refine ⟨by simp only [polar]; ring, by rw [polar_self, nsmul_eq_mul, Nat.cast_ofNat], ?_, ?_⟩
  · have h2 := congrArg (fun f => f x y) (Matrix.toLinearMap₂'_toMatrix' (R := R) (polarBilin Q))
    simp only [Matrix.toLinearMap₂'_apply'] at h2
    rw [← polarBilin_apply_apply, ← h2]
    congr 2
  · ext i j
    simp [polar_comm]

open MvPolynomial in
theorem pderiv_X_eq_C (a b : Fin n) : pderiv a (X b : MvPolynomial (Fin n) R) = C (if a = b then 1 else 0) := by
  by_cases h : a = b
  · subst h; simp
  · rw [pderiv_X_of_ne (Ne.symm h)]; simp [h]

open MvPolynomial in
theorem pderiv_pderiv_X_mul_X (i j k l : Fin n) :
    pderiv i (pderiv j (X k * X l : MvPolynomial (Fin n) R)) =
      C ((if j = l then 1 else 0) * (if i = k then 1 else 0) +
        (if j = k then 1 else 0) * (if i = l then 1 else 0)) := by
  simp only [Derivation.leibniz, pderiv_X_eq_C, smul_eq_mul, pderiv_C, mul_zero, zero_add, map_add, map_mul]

theorem sum_sum_mul_delta (c : Fin n → Fin n → R) (i j : Fin n) :
    ∑ k, ∑ l, c k l * (((if j = l then (1 : R) else 0) * if i = k then 1 else 0) +
      (if j = k then 1 else 0) * if i = l then 1 else 0) = c i j + c j i := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]

/-- **Lemma 2.9, the Hessian matrix** (Hanke 2013, p. 6): for the polynomial
$P = \sum_{k,l} c_{kl}X_kX_l$ in $n$ variables over a commutative ring $R$ (every quadratic form is of this shape),
$\partial^2P/\partial X_i\partial X_j$ is the constant $c_{ij} + c_{ji}$, which is
$H(e_i, e_j) = P(e_i + e_j) - P(e_i) - P(e_j)$. -/
@[kb "hanke2013algorithms" "Lemma 2.9, p. 6 (A is the matrix of second partials)"]
theorem lemma_2_9_hessian (c : Fin n → Fin n → R) (i j : Fin n) :
    let P : MvPolynomial (Fin n) R := ∑ k, ∑ l, MvPolynomial.C (c k l) * MvPolynomial.X k * MvPolynomial.X l
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.C (c i j + c j i) ∧
    MvPolynomial.eval (Pi.single i 1 + Pi.single j 1) P - MvPolynomial.eval (Pi.single i 1) P -
      MvPolynomial.eval (Pi.single j 1) P = c i j + c j i := by
  intro P
  constructor
  · have hP : P = ∑ k, ∑ l, MvPolynomial.C (c k l) * (MvPolynomial.X k * MvPolynomial.X l) := by
      simp only [P, mul_assoc]
    rw [hP, map_sum]
    simp only [map_sum, MvPolynomial.pderiv_C_mul, pderiv_pderiv_X_mul_X, ← map_mul]
    rw [← sum_sum_mul_delta c i j]
    simp only [map_sum]
  · simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.add_apply, Pi.single_apply]
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_add_distrib]
    ring

end Polarization

end QuadFormsKB.Hanke2013Algorithms
