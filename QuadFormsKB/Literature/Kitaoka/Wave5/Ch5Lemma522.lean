/-
# Kitaoka 1993, Lemma 5.2.2: lattices on the hyperbolic plane

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §5.2, Lemma 5.2.2, p. 74 (printed page).

**Book statement.** For $c \in F^\times$ and a lattice $L$ on the hyperbolic plane $H$, the following three conditions
are equivalent: (i) $L \cong \begin{pmatrix} 0 & c \\ c & 0 \end{pmatrix}$; (ii) $L$ is $(c)$-modular and
$\mathfrak n(L) \subseteq (2c)$; (iii) $L$ is $(2c)$-maximal.

**Encoding.** $F = \mathbb Q_p$, $R = \mathbb Z_p$ (any prime $p$, including $p = 2$). The hyperbolic plane is a
quadratic space $(V, Q)$ over $\mathbb Q_p$ of dimension $2$, regular and isotropic. Kitaoka's bilinear form with
$B(x, x) = Q(x)$ is O'Meara's `OMeara.bil`. A lattice on $V$ is a finitely generated $\mathbb Z_p$-submodule spanning
$V$ (`Submodule.IsLattice`). (i) is: $L$ has a basis $e_1, e_2$ (here: $L = \mathbb Z_pe_1 + \mathbb Z_pe_2$) with
$Q(e_1) = Q(e_2) = 0$ and $B(e_1, e_2) = c$, i.e. Gram matrix $\begin{pmatrix} 0 & c \\ c & 0 \end{pmatrix}$.
(ii) uses `OMeara.IsModular` and `OMeara.normIdeal`; (iii) is `OMeara.IsMaximal` for the ideal $(2c)$.

**Proves** (unconditional): `lemma522` (the three conditions as a `List.TFAE`), from the general version
`lemma522_gen` over any discrete valuation ring whose fraction field has $2 \ne 0$.

**Proof.** (i) $\Rightarrow$ (ii): the Gram matrix is $c\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ with a unit
determinant (O'Meara 82:13, `OMeara.isModular_iff_gram`), and $Q(re_1 + se_2) = 2rsc$. (ii) $\Leftrightarrow$ (iii) is
O'Meara 82:21 (`OMeara.isMaximal_iff_isModular_of_hyperbolic`); Kitaoka derives (ii) $\Rightarrow$ (iii) from his
Lemma 5.2.1. (iii) $\Rightarrow$ (i): by O'Meara 82:21a (`OMeara.exists_eq_of_isMaximal_hyperbolic`)
$L = \mathfrak bx + c\mathfrak b^{-1}y$ for a hyperbolic pair $x, y$ and a fractional ideal $\mathfrak b = \beta R$;
take $e_1 = \beta x$, $e_2 = c\beta^{-1}y$. (Kitaoka's own proof of (iii) $\Rightarrow$ (i) is a direct maximality
argument.)
-/
import QuadFormsKB.Literature.OMeara.Sec82Max
import Mathlib.NumberTheory.Padics.PadicIntegers

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Lemma522

open OMeara

section General

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Condition (i) of Lemma 5.2.2: $L = Re_1 + Re_2$ with $Q(e_1) = Q(e_2) = 0$ and $B(e_1, e_2) = c$. -/
def HypBasis (c : F) (L : Submodule R V) : Prop :=
  ∃ e₁ e₂ : V, L = span R {e₁, e₂} ∧ Q e₁ = 0 ∧ Q e₂ = 0 ∧ bil Q e₁ e₂ = c

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem span_mul_singleton (a b : F) : (R ∙ a) * (R ∙ b) = R ∙ (a * b) := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem span_two_mul (c : F) : span R {(2 : F)} * (R ∙ c) = R ∙ (2 * c) := span_mul_singleton 2 c

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [Invertible (2 : F)] in
theorem one_div_span_singleton {β : F} (hβ : β ≠ 0) : 1 / (R ∙ β) = R ∙ β⁻¹ := by
  ext x
  rw [Submodule.mem_div_iff_forall_mul_mem, Submodule.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (h β (Submodule.mem_span_singleton_self β))
    refine ⟨r, ?_⟩
    rw [Algebra.smul_def, hr]
    field_simp
  · rintro ⟨r, rfl⟩ y hy
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [Submodule.mem_one]
    refine ⟨r * s, ?_⟩
    simp only [Algebra.smul_def, map_mul]
    field_simp

/-- (i) $\Rightarrow$ (ii). -/
theorem modular_of_hypBasis {c : F} (hc : c ≠ 0) {L : Submodule R V} (h : HypBasis Q c L) :
    IsModular Q (R ∙ c) L ∧ normIdeal Q L ≤ R ∙ (2 * c) := by
  classical
  obtain ⟨e₁, e₂, hL, h1, h2, h12⟩ := h
  have hinjR : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hsm : ∀ (r : R) (v : V), r • v = algebraMap R F r • v := fun r v => (algebraMap_smul F r v).symm
  have h21 : bil Q e₂ e₁ = c := by rw [bil_comm]; exact h12
  have hli : LinearIndependent R ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [hsm, hsm] at hst
    have hb1 := congrArg (bil Q e₁) hst
    have hb2 := congrArg (bil Q e₂) hst
    rw [bil_add_right, bil_smul_right, bil_smul_right, bil_self, h1, h12] at hb1
    rw [bil_add_right, bil_smul_right, bil_smul_right, bil_self, h2, h21] at hb2
    simp only [mul_zero, zero_add, add_zero] at hb1 hb2
    have ht : algebraMap R F t = 0 := by
      rcases mul_eq_zero.mp (show algebraMap R F t * c = 0 by simpa [bil] using hb1) with h0 | h0
      · exact h0
      · exact absurd h0 hc
    have hs : algebraMap R F s = 0 := by
      rcases mul_eq_zero.mp (show algebraMap R F s * c = 0 by simpa [bil] using hb2) with h0 | h0
      · exact h0
      · exact absurd h0 hc
    exact ⟨hinjR (by rw [hs, map_zero]), hinjR (by rw [ht, map_zero])⟩
  have hrange : Set.range ![e₁, e₂] = {e₁, e₂} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  have hspan : span R (Set.range ![e₁, e₂]) = L := by rw [hrange, hL]
  let b : Basis (Fin 2) R L := (Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hb : ∀ i, (b i : V) = ![e₁, e₂] i := fun i => by
    simp [b, Basis.span_apply]
  constructor
  · rw [isModular_iff_gram Q b hc]
    refine ⟨⟨0⟩, !![0, 1; 1, 0], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]; simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [gram, hb, h1, h2, h12, h21]
  · rw [normIdeal, span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, hL] at hz
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨s * t, ?_⟩
    rw [hsm, hsm, Q_add, Q_smul, Q_smul, h1, h2, bil_smul_left, bil_smul_right, h12, Algebra.smul_def, map_mul]
    ring

/-- (iii) $\Rightarrow$ (i). -/
theorem hypBasis_of_isMaximal (hV : (QuadraticMap.associated Q).Nondegenerate) (hdim : finrank F V = 2)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {c : F} (hc : c ≠ 0) {L : Submodule R V}
    (h : IsMaximal Q (R ∙ (2 * c)) L) : HypBasis Q c L := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_hyp_pair_max Q hV hiso
  have hc' : (R ∙ c).FG := fg_span_singleton c
  have hc0 : (R ∙ c) ≠ ⊥ := by simpa using hc
  rw [← span_two_mul] at h
  obtain ⟨b, hbfg, hb0, hL⟩ := exists_eq_of_isMaximal_hyperbolic Q hx hy hxy hdim hc' hc0 h
  obtain ⟨β, hβ, rfl⟩ := exists_eq_span_singleton hbfg hb0
  refine ⟨β • x, (c * β⁻¹) • y, ?_, by rw [Q_smul, hx, mul_zero], by rw [Q_smul, hy, mul_zero], ?_⟩
  · rw [hL, one_div_span_singleton hβ, span_mul_singleton, span_smul_span_singleton_max,
      span_smul_span_singleton_max, ← span_union, Set.union_singleton, Set.pair_comm]
  · rw [bil_smul_left, bil_smul_right, hxy]
    field_simp

/-- **Kitaoka 1993, Lemma 5.2.2** (p. 74), over a discrete valuation ring $R$ with fraction field $F$, $2 \ne 0$
in $F$. -/
theorem lemma522_gen (hV : (QuadraticMap.associated Q).Nondegenerate) (hdim : finrank F V = 2)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {c : F} (hc : c ≠ 0) {L : Submodule R V} (hL : L.IsLattice F) :
    List.TFAE [HypBasis Q c L, IsModular Q (R ∙ c) L ∧ normIdeal Q L ≤ R ∙ (2 * c),
      IsMaximal Q (R ∙ (2 * c)) L] := by
  have hc' : (R ∙ c).FG := fg_span_singleton c
  have hc0 : (R ∙ c) ≠ ⊥ := by simpa using hc
  have h23 := isMaximal_iff_isModular_of_hyperbolic Q hV hdim hiso hc' hc0 hL
  rw [span_two_mul] at h23
  tfae_have 1 → 2 := modular_of_hypBasis Q hc
  tfae_have 2 → 3 := h23.2
  tfae_have 3 → 1 := hypBasis_of_isMaximal Q hV hdim hiso hc
  tfae_finish

end General

/-- **Kitaoka 1993, Lemma 5.2.2** (p. 74). Let $p$ be a prime, $c \in \mathbb Q_p^\times$, $(V, Q)$ the hyperbolic
plane over $\mathbb Q_p$ (a regular isotropic quadratic space of dimension $2$) and $L$ a lattice on $V$. The following
are equivalent:
(i) $L \cong \begin{pmatrix} 0 & c \\ c & 0 \end{pmatrix}$, i.e. $L = \mathbb Z_pe_1 + \mathbb Z_pe_2$ with
$Q(e_1) = Q(e_2) = 0$, $B(e_1, e_2) = c$;
(ii) $L$ is $(c)$-modular and $\mathfrak n(L) \subseteq (2c)$;
(iii) $L$ is $(2c)$-maximal.
Unconditional. -/
@[kb "kitaoka1993" "§5.2, Lemma 5.2.2, p. 74"]
theorem lemma522 (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    [IsScalarTower ℤ_[p] ℚ_[p] V] [FiniteDimensional ℚ_[p] V] (Q : QuadraticForm ℚ_[p] V)
    (hV : (QuadraticMap.associated Q).Nondegenerate) (hdim : finrank ℚ_[p] V = 2)
    (hiso : ∃ v : V, v ≠ 0 ∧ Q v = 0) {c : ℚ_[p]} (hc : c ≠ 0) {L : Submodule ℤ_[p] V}
    (hL : L.IsLattice ℚ_[p]) :
    letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
    List.TFAE [∃ e₁ e₂ : V, L = span ℤ_[p] {e₁, e₂} ∧ Q e₁ = 0 ∧ Q e₂ = 0 ∧ bil Q e₁ e₂ = c,
      IsModular Q (ℤ_[p] ∙ c) L ∧ normIdeal Q L ≤ ℤ_[p] ∙ (2 * c),
      IsMaximal Q (ℤ_[p] ∙ (2 * c)) L] :=
  letI : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero
  lemma522_gen Q hV hdim hiso hc hL

end QuadFormsKB.Kitaoka.Lemma522
