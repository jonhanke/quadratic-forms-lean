/-
# Cassels, Chapter 2: Examples 4, 13, 14 (pp. 29, 31-32)

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 2, *Examples*, pp. 29, 31-32.

**Setting.** As in `Ch2/Exercises.lean`: $k$ = `F` is a field of characteristic $\ne 2$ (`[Invertible (2 : F)]`),
a quadratic space is `Q : QuadraticForm F V` with $V$ finite-dimensional, autometries are `OMeara.orth Q`, proper
ones `OMeara.orthPlus Q`, and *regular* means that `OMeara.bil Q` (`QuadraticMap.associated Q`) is nondegenerate.
Indices are $0$-based. Explicit forms in $n$ variables are written as polynomial expressions in
$x_0, \dots, x_{n-1}$.

**Proves.**
* Ex. 4 (p. 29): $a x_0^{2} + b x_1^{2} - ab x_2^{2}$ is isotropic iff $x_0^{2} - a x_1^{2} - b x_2^{2} + ab x_3^{2}$
  is isotropic (`ex4`).
* Ex. 14 (p. 32), (i) and (ii): the coordinate topology on $O(V)$ does not depend on the basis (`ex14_i`), and
  $O^{+}(V)$ is open and closed in $O(V)$ (`ex14_ii`).

* Ex. 13 (pp. 31-32), (i) and (ii): isometric forms have equal numbers of zeros, of representations of $1$ and
  equal orders of the proper orthogonal groups (`ex13_i`); the number of zeros of a regular binary form over a
  finite field of odd order (`ex13_ii`, `ex13_ii_zmod` over $\mathbb F_p$).

**Not formalized here**: Ex. 13 (iii)-(vi) (the recursions and closed formulas for $N_n$, $R_n$, $A_n$); the
classification step of Ex. 13 (i); Ex. 14 (iii). *Erratum candidate for Ex. 14 (iii):* as printed the claim fails
when the form is indefinite (for the form $x_0^{2} - x_1^{2}$ the group $O^{+}$ has two connected components, the
hint's path from $b$ to $a$ must stay among anisotropic vectors of the same sign); it holds for definite forms.
-/
import QuadFormsKB.Literature.OMeara.Sec91Units
import QuadFormsKB.Literature.Cassels.Ch2.Exercises
import Mathlib.Topology.Instances.Matrix

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch2Ex

open QuadFormsKB.OMeara

section Ex4

variable {F : Type*} [Field F] [Invertible (2 : F)]

/-- **Cassels, Ch. 2, Ex. 4 (p. 29).** Let $a, b \in k^{\times}$. Then the form
$a x_0^{2} + b x_1^{2} - ab x_2^{2}$ is isotropic if and only if the form
$x_0^{2} - a x_1^{2} - b x_2^{2} + ab x_3^{2}$ is isotropic. (Hint: the previous example, `ex3`.)
The page image shows that the book's pair is $\langle 1, a, b\rangle$-type
and $\langle 1, a, b, ab\rangle$, see `ex4_book`; this theorem is the equivalent form with $a, b$ replaced by
$-a, -b$ (and the first form scaled by $-1$). -/
@[kb "cassels1978" "Ch. 2, Ex. 4, p. 29"]
theorem ex4 (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x : Fin 3 → F, x ≠ 0 ∧ a * x 0 ^ 2 + b * x 1 ^ 2 - a * b * x 2 ^ 2 = 0) ↔
    (∃ x : Fin 4 → F, x ≠ 0 ∧ x 0 ^ 2 - a * x 1 ^ 2 - b * x 2 ^ 2 + a * b * x 3 ^ 2 = 0) := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨![0, x 0, x 1, x 2], ?_, by simp; linear_combination (-1 : F) * h⟩
    intro h0
    apply hx
    ext i
    fin_cases i
    · simpa using congrFun h0 1
    · simpa using congrFun h0 2
    · simpa using congrFun h0 3
  · rintro ⟨x, hx, h⟩
    -- the case where `a` is a square
    have hsq : (∃ c : F, a = c ^ 2) → ∃ x : Fin 3 → F, x ≠ 0 ∧ a * x 0 ^ 2 + b * x 1 ^ 2 - a * b * x 2 ^ 2 = 0 := by
      rintro ⟨c, rfl⟩
      refine ⟨![0, c, 1], ?_, by simp; ring⟩
      intro h0
      simpa using congrFun h0 2
    by_cases hN : x 2 ^ 2 - a * x 3 ^ 2 = 0
    · apply hsq
      have hN' : x 0 ^ 2 - a * x 1 ^ 2 = 0 := by linear_combination h + b * hN
      by_cases h3 : x 3 = 0
      · have h2 : x 2 = 0 := by simpa [h3] using hN
        by_cases h1 : x 1 = 0
        · have h0 : x 0 = 0 := by simpa [h1] using hN'
          exact absurd (by ext i; fin_cases i <;> simp [h0, h1, h2, h3]) hx
        · exact ⟨x 0 / x 1, by field_simp; linear_combination -hN'⟩
      · exact ⟨x 2 / x 3, by field_simp; linear_combination -hN⟩
    · obtain ⟨A, hA⟩ := ex3 (F := F) (-a) (neg_ne_zero.mpr ha)
      have hN0 : (x 2 ^ 2 - a * x 3 ^ 2) ≠ 0 := hN
      have hmem : ∀ (u v : F) (hne : u ^ 2 - a * v ^ 2 ≠ 0), Units.mk0 _ hne ∈ A := by
        intro u v hne
        rw [hA]
        exact ⟨u, v, by simp [Units.val_mk0]; ring⟩
      by_cases hN1 : x 0 ^ 2 - a * x 1 ^ 2 = 0
      · -- then `b (x₂² - a x₃²) = 0`, impossible
        exfalso
        have : b * (x 2 ^ 2 - a * x 3 ^ 2) = 0 := by linear_combination -h + hN1
        exact (mul_ne_zero hb hN0) this
      · have hbA : Units.mk0 b hb ∈ A := by
          have e : Units.mk0 b hb = Units.mk0 _ hN1 * (Units.mk0 _ hN0)⁻¹ := by
            ext
            simp only [Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
            field_simp
            linear_combination -h
          rw [e]
          exact A.mul_mem (hmem _ _ hN1) (A.inv_mem (hmem _ _ hN0))
        obtain ⟨p, q, hpq⟩ := (hA _).mp hbA
        simp only [Units.val_mk0] at hpq
        refine ⟨![b, -(a * q), p], ?_, ?_⟩
        · intro h0
          exact hb (by simpa using congrFun h0 0)
        · simp
          linear_combination (-(a * b)) * hpq

/-- **Cassels, Ch. 2, Ex. 4 (p. 29), the book's forms.** Let $a, b \in k^{\times}$. Then the form
$x_0^{2} + a x_1^{2} + b x_2^{2}$ is isotropic if and only if the form
$x_0^{2} + a x_1^{2} + b x_2^{2} + ab\, x_3^{2}$ is isotropic. *Erratum:* the second form is printed with
"$a x_1^{2}$" (the first variable twice); the correct term is $a x_2^{2}$ in the book's 1-based indexing, i.e.
$a x_1^{2}$ in the 0-based indexing used here. Derived from `ex4` applied to $(-a, -b)$:
$\langle a, b, ab\rangle$ scaled by $ab$ is $\langle b, a, 1\rangle$ up to squares. -/
@[kb "cassels1978" "Ch. 2, Ex. 4, p. 29 (the book's forms)"]
theorem ex4_book (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x : Fin 3 → F, x ≠ 0 ∧ x 0 ^ 2 + a * x 1 ^ 2 + b * x 2 ^ 2 = 0) ↔
    (∃ x : Fin 4 → F, x ≠ 0 ∧ x 0 ^ 2 + a * x 1 ^ 2 + b * x 2 ^ 2 + a * b * x 3 ^ 2 = 0) := by
  have h := ex4 (-a) (-b) (neg_ne_zero.mpr ha) (neg_ne_zero.mpr hb)
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h4 : (∃ x : Fin 4 → F, x ≠ 0 ∧ x 0 ^ 2 - -a * x 1 ^ 2 - -b * x 2 ^ 2 + -a * -b * x 3 ^ 2 = 0) ↔
      (∃ x : Fin 4 → F, x ≠ 0 ∧ x 0 ^ 2 + a * x 1 ^ 2 + b * x 2 ^ 2 + a * b * x 3 ^ 2 = 0) := by
    constructor <;> rintro ⟨x, hx, h⟩ <;> exact ⟨x, hx, by linear_combination h⟩
  rw [← h4, ← h]
  constructor
  · rintro ⟨y, hy, hq⟩
    refine ⟨![y 2 / a, y 1 / b, y 0 / (a * b)], ?_, ?_⟩
    · intro h0
      apply hy
      ext i
      fin_cases i
      · have := congrFun h0 2
        simpa [ha, hb] using this
      · have := congrFun h0 1
        simpa [hb] using this
      · have := congrFun h0 0
        simpa [ha] using this
    · simp
      field_simp
      linear_combination (-1 : F) * hq
  · rintro ⟨x, hx, hq⟩
    refine ⟨![a * b * x 2, b * x 1, a * x 0], ?_, ?_⟩
    · intro h0
      apply hx
      ext i
      fin_cases i
      · simpa [ha] using congrFun h0 2
      · simpa [hb] using congrFun h0 1
      · simpa [hab] using congrFun h0 0
    · simp
      linear_combination (-(a * b)) * hq

end Ex4

section Ex14

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)

/-- **The coordinate topology on $O(V)$** (Cassels, Ch. 2, Ex. 14, p. 32), for a basis $b$ of $V$: the topology
induced by the map sending $\sigma \in O(V)$ to its matrix $(s_{ij})$ in the basis $b$ (so
$\sigma b_j = \sum_i s_{ij} b_i$), with values in the space of $n \times n$ real matrices. -/
@[reducible] def coordTopology{ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) : TopologicalSpace (orth Q) :=
  TopologicalSpace.induced (fun σ => LinearMap.toMatrix b b (σ.1 : V →ₗ[ℝ] V)) inferInstance

/-- Change of basis: the matrix in `b'` is the conjugate of the matrix in `b`. -/
lemma toMatrix_change {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι ℝ V) (b' : Basis ι' ℝ V) (f : V →ₗ[ℝ] V) :
    LinearMap.toMatrix b' b' f = LinearMap.toMatrix b b' LinearMap.id *
      LinearMap.toMatrix b b f * LinearMap.toMatrix b' b LinearMap.id := by
  rw [← LinearMap.toMatrix_comp b b b', ← LinearMap.toMatrix_comp b' b b']
  congr 1

/-- One inclusion of topologies for `ex14_i`. -/
lemma coordTopology_le {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι ℝ V) (b' : Basis ι' ℝ V) : coordTopology Q b ≤ coordTopology Q b' := by
  unfold coordTopology
  set P := LinearMap.toMatrix b b' (LinearMap.id : V →ₗ[ℝ] V)
  set P' := LinearMap.toMatrix b' b (LinearMap.id : V →ₗ[ℝ] V)
  have hg : Continuous fun M : Matrix ι ι ℝ => P * M * P' := by fun_prop
  have hf : (fun σ : orth Q => LinearMap.toMatrix b' b' (σ.1 : V →ₗ[ℝ] V)) =
      (fun M : Matrix ι ι ℝ => P * M * P') ∘ fun σ => LinearMap.toMatrix b b (σ.1 : V →ₗ[ℝ] V) := by
    funext σ
    exact toMatrix_change b b' _
  rw [hf, ← induced_compose]
  exact induced_mono (continuous_iff_le_induced.mp hg)

/-- **Cassels, Ch. 2, Ex. 14 (i) (p. 32).** The coordinate topology on $O(V)$ is independent of the choice of the
basis: for two bases $b$, $b'$ of $V$ the topologies `coordTopology Q b` and `coordTopology Q b'` coincide. -/
@[kb "cassels1978" "Ch. 2, Ex. 14 (i), p. 32"]
theorem ex14_i {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Basis ι ℝ V) (b' : Basis ι' ℝ V) : coordTopology Q b = coordTopology Q b' :=
  le_antisymm (coordTopology_le Q b b') (coordTopology_le Q b' b)

/-- **Cassels, Ch. 2, Ex. 14 (ii) (p. 32).** For a regular real quadratic space, $O^{+}(V)$ is both open and
closed in $O(V)$ (in the coordinate topology, for any basis $b$). -/
@[kb "cassels1978" "Ch. 2, Ex. 14 (ii), p. 32"]
theorem ex14_ii (hQ : (associated Q).Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ V) :
    @IsClopen (orth Q) (coordTopology Q b) {σ | σ.1 ∈ orthPlus Q} := by
  let _ := coordTopology Q b
  let g : orth Q → ℝ := fun σ => (LinearMap.toMatrix b b (σ.1 : V →ₗ[ℝ] V)).det
  have hg : Continuous g :=
    (Continuous.matrix_det continuous_induced_dom : Continuous fun σ : orth Q =>
      (LinearMap.toMatrix b b (σ.1 : V →ₗ[ℝ] V)).det)
  have hgd : ∀ σ : orth Q, g σ = ((LinearEquiv.det σ.1 : ℝˣ) : ℝ) := fun σ => by
    simp [g, LinearMap.det_toMatrix]
  have hset1 : {σ : orth Q | σ.1 ∈ orthPlus Q} = g ⁻¹' {1} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, hgd, orthPlus,
      Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, h⟩; simp [h]
    · intro h; exact ⟨σ.2, Units.ext h⟩
  have hset2 : {σ : orth Q | σ.1 ∈ orthPlus Q} = g ⁻¹' Set.Ioi 0 := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi, hgd, orthPlus,
      Subgroup.mem_inf, MonoidHom.mem_ker]
    rcases det_orth_eq Q hQ σ.2 with h | h
    · simp [h, σ.2]
    · simp [h, σ.2]
  exact ⟨hset1 ▸ isClosed_singleton.preimage hg, hset2 ▸ isOpen_Ioi.preimage hg⟩

end Ex14

section Ex13

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/-- Conjugation by an isometry carries proper autometries to proper autometries. -/
lemma conj_mem_orthPlus {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (e : Q₁.IsometryEquiv Q₂)
    {σ : V₁ ≃ₗ[F] V₁} (hσ : σ ∈ orthPlus Q₁) :
    (e.toLinearEquiv.symm.trans σ).trans e.toLinearEquiv ∈ orthPlus Q₂ := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hσ
  refine Subgroup.mem_inf.mpr ⟨fun y => ?_, ?_⟩
  · have h := e.map_app (σ (e.toLinearEquiv.symm y))
    have h' : (Q₁ (σ (e.toLinearEquiv.symm y))) = Q₁ (e.toLinearEquiv.symm y) := h1 _
    have h'' := e.map_app (e.toLinearEquiv.symm y)
    refine h.trans (h'.trans ?_)
    simp
  · rw [MonoidHom.mem_ker] at h2 ⊢
    rw [LinearEquiv.det_conj, h2]

/-- **Cassels, Ch. 2, Ex. 13 (i) (p. 31).** (Invariance part.) If two quadratic forms are isometric, then they
have the same number $N$ of zeros (including $0$), the same number $R$ of representations of $1$, and proper
orthogonal groups of the same order $A$. For forms over $\mathbb F_p$ this is the first step of the statement that
$N$, $R$, $A$ depend only on the dimension and the determinant class (the second step, that forms of equal dimension
and determinant class are isometric, is the classification of forms over finite fields and is not reproved here).
(Any field; `Nat.card` is $0$ for an infinite set.) -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (i), p. 31"]
theorem ex13_i {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (e : Q₁.IsometryEquiv Q₂) :
    Nat.card {x // Q₁ x = 0} = Nat.card {y // Q₂ y = 0} ∧
    Nat.card {x // Q₁ x = 1} = Nat.card {y // Q₂ y = 1} ∧
    Nat.card (orthPlus Q₁) = Nat.card (orthPlus Q₂) := by
  refine ⟨Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun x => ?_),
    Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun x => ?_), Nat.card_congr ?_⟩
  · simp [e.map_app]
  · simp [e.map_app]
  · refine
      { toFun := fun σ => ⟨(e.toLinearEquiv.symm.trans σ.1).trans e.toLinearEquiv,
          conj_mem_orthPlus e σ.2⟩
        invFun := fun τ => ⟨(e.toLinearEquiv.trans τ.1).trans e.toLinearEquiv.symm,
          conj_mem_orthPlus e.symm τ.2⟩
        left_inv := fun σ => ?_
        right_inv := fun τ => ?_ }
    · apply Subtype.ext; ext x; simp
    · apply Subtype.ext; ext x; simp

/-- **Cassels, Ch. 2, Ex. 13 (ii) (p. 31).** Let $k$ be a finite field of odd order $q$ (for $q = p$ a prime,
$k = \mathbb F_p$, see `ex13_ii_zmod`) and $f = a x_0^{2} + b x_1^{2}$ a regular binary form
($a, b \in k^{\times}$, determinant $d = ab$). The number $N_2(d)$ of zeros of $f$ in $k^{2}$, including $(0,0)$, is
$2q - 1$ if $-d$ is a square in $k$ and $1$ otherwise. *Erratum:* the page prints the condition as
$d \in (k^{\times})^{2}$; the correct condition is $-d \in (k^{\times})^{2}$ (checked against the page image; e.g.
$x^{2} - y^{2}$ over $\mathbb F_3$ has $d = -1$, a non-square, and $5$ zeros). Every binary form is equivalent to a diagonal one, so this is no loss of generality. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (ii), p. 31"]
theorem ex13_ii [Fintype F] [DecidableEq F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card {z : F × F // a * z.1 ^ 2 + b * z.2 ^ 2 = 0} =
      if IsSquare (-(a * b)) then 2 * Nat.card F - 1 else 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  have h2 : (2 : F) ≠ 0 := Invertible.ne_zero (2 : F)
  split_ifs with hsq
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact mul_ne_zero ha hb (by simpa using hr)
    let L : F → Finset (F × F) := fun ε => Finset.univ.image fun x : F => (x, ε * r * b⁻¹ * x)
    have hLc : ∀ ε, (L ε).card = Fintype.card F := fun ε =>
      (Finset.card_image_of_injective _ fun x y h => (Prod.mk.inj h).1).trans Finset.card_univ
    have hS : Finset.univ.filter (fun z : F × F => a * z.1 ^ 2 + b * z.2 ^ 2 = 0) = L 1 ∪ L (-1) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, L, Finset.mem_image,
        Prod.mk.injEq]
      constructor
      · intro h
        have h1 : (b * y - r * x) * (b * y + r * x) = 0 := by
          linear_combination b * h + x ^ 2 * hr
        rcases mul_eq_zero.mp h1 with h3 | h3
        · left
          exact ⟨x, rfl, by field_simp; linear_combination -h3⟩
        · right
          exact ⟨x, rfl, by field_simp; linear_combination -h3⟩
      · rintro (⟨x', rfl, rfl⟩ | ⟨x', rfl, rfl⟩) <;> (field_simp; linear_combination (-x' ^ 2) * hr)
    have hI : L 1 ∩ L (-1) = {(0, 0)} := by
      ext ⟨x, y⟩
      simp only [Finset.mem_inter, L, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨x1, rfl, h1⟩, ⟨x2, h2', h3⟩⟩
        have hx : x2 = x1 := h2'
        subst hx
        have : (2 : F) * r * b⁻¹ * x2 = 0 := by linear_combination h1 - h3
        have hx0 : x2 = 0 := by
          simpa [h2, hr0, hb] using this
        subst hx0
        simp only [mul_zero] at h1
        exact ⟨rfl, h1.symm⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨⟨0, rfl, by simp⟩, ⟨0, rfl, by simp⟩⟩
    rw [hS]
    have := Finset.card_union_add_card_inter (L 1) (L (-1))
    rw [hI, hLc, hLc, Finset.card_singleton] at this
    omega
  · rw [Finset.card_eq_one]
    refine ⟨(0, 0), ?_⟩
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      have hy : y = 0 := by
        by_contra hy
        apply hsq
        refine ⟨a * x / y, ?_⟩
        rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hy hy)]
        linear_combination (-a) * h
      subst hy
      refine ⟨?_, rfl⟩
      simpa [ha] using h
    · rintro ⟨rfl, rfl⟩
      simp

/-- **Cassels, Ch. 2, Ex. 13 (ii) (p. 31), over $\mathbb F_p$.** For an odd prime $p$ and $a, b \in \mathbb F_p^{\times}$
the number of zeros of $a x_0^{2} + b x_1^{2}$ in $\mathbb F_p^{2}$ is $2p - 1$ if $-ab$ is a square and $1$
otherwise. -/
@[kb "cassels1978" "Ch. 2, Ex. 13 (ii), p. 31"]
theorem ex13_ii_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card {z : ZMod p × ZMod p // a * z.1 ^ 2 + b * z.2 ^ 2 = 0} =
      if IsSquare (-(a * b)) then 2 * p - 1 else 1 := by
  have : Invertible (2 : ZMod p) := invertibleOfNonzero (by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this
    exact hp this)
  classical
  rw [ex13_ii a b ha hb, Nat.card_zmod]

end Ex13

section Ex14iii

/-- The indefinite binary form $x_0^{2} - x_1^{2}$ on $\mathbb R^{2}$ (Mathlib's weighted sum of squares with
weights $1, -1$; a local abbreviation, not a new notion). -/
abbrev diffSqForm : QuadraticForm ℝ (Fin 2 → ℝ) := QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), -1]

lemma diffSqForm_apply (x : Fin 2 → ℝ) : diffSqForm x = x 0 ^ 2 - x 1 ^ 2 := by
  simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two]
  ring

/-- **Cassels, Ch. 2, Ex. 14 (iii) (p. 32), counterexample for an indefinite form.** For
$Q = x_0^{2} - x_1^{2}$ on $\mathbb R^{2}$ the group $O^{+}(V)$ is not connected in the coordinate topology (for
the standard basis; by `ex14_i` for any basis).
*Erratum:* as printed, Ex. 14 (iii) claims that $O^{+}(V)$ is connected for every real quadratic space. This fails for
indefinite forms: for $\sigma \in O(Q)$ the matrix entry $s_{00}$ satisfies $s_{00}^{2} - s_{10}^{2} = 1$, so
$s_{00} \ne 0$, and $O^{+}$ is split by the sign of $s_{00}$ into two non-empty open pieces (containing $1$ and
$-1$). The hint's path from $b$ to $a$ must stay within anisotropic vectors, which is impossible when $Q(a)$ and
$Q(b)$ have opposite signs. The statement is true for definite forms. -/
@[kb "cassels1978" "Ch. 2, Ex. 14 (iii), p. 32 (erratum: fails for indefinite forms)"]
theorem ex14_iii_counterexample :
    ¬ @IsPreconnected (orth diffSqForm) (coordTopology diffSqForm (Pi.basisFun ℝ (Fin 2)))
      {σ | σ.1 ∈ orthPlus diffSqForm} := by
  let _ := coordTopology diffSqForm (Pi.basisFun ℝ (Fin 2))
  let g : orth diffSqForm → ℝ := fun σ =>
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin 2)) (Pi.basisFun ℝ (Fin 2)) (σ.1 : (Fin 2 → ℝ) →ₗ[ℝ] _)) 0 0
  have hg : Continuous g :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_induced_dom)
  have hge : ∀ σ : orth diffSqForm, g σ = σ.1 (Pi.single 0 1) 0 := fun σ => by
    simp [g]
  have hne : ∀ σ : orth diffSqForm, g σ ≠ 0 := by
    intro σ h0
    have h1 := σ.2 (Pi.single 0 1)
    rw [diffSqForm_apply, diffSqForm_apply] at h1
    rw [hge] at h0
    simp [h0] at h1
    nlinarith [sq_nonneg (σ.1 (Pi.single 0 1) 1)]
  let one : orth diffSqForm := ⟨1, (orth diffSqForm).one_mem⟩
  have hnegmem : (LinearEquiv.neg ℝ : (Fin 2 → ℝ) ≃ₗ[ℝ] _) ∈ orth diffSqForm := fun x => by
    simp
  let m1 : orth diffSqForm := ⟨LinearEquiv.neg ℝ, hnegmem⟩
  have hone : one.1 ∈ orthPlus diffSqForm := (orthPlus diffSqForm).one_mem
  have hm1 : m1.1 ∈ orthPlus diffSqForm := by
    refine Subgroup.mem_inf.mpr ⟨hnegmem, ?_⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [LinearEquiv.coe_det]
    have : ((LinearEquiv.neg ℝ : (Fin 2 → ℝ) ≃ₗ[ℝ] _) : (Fin 2 → ℝ) →ₗ[ℝ] _) = (-1 : ℝ) • LinearMap.id := by
      ext x; simp
    rw [this, LinearMap.det_smul]
    simp
  intro hconn
  have := hconn {σ | 0 < g σ} {σ | g σ < 0} (isOpen_lt continuous_const hg)
    (isOpen_lt hg continuous_const)
    (fun σ _ => by
      rcases lt_or_gt_of_ne (hne σ) with h | h
      · exact Or.inr h
      · exact Or.inl h)
    ⟨one, hone, by simp [one, hge]⟩ ⟨m1, hm1, by simp [m1, hge]⟩
  obtain ⟨σ, -, h1, h2⟩ := this
  exact absurd (show 0 < g σ from h1) (not_lt.mpr (show g σ < 0 from h2).le)

end Ex14iii

end QuadFormsKB.Cassels.Ch2Ex

