/-
# Cassels, Chapter 12, Notes (continued): Venkov's domain, Voronoi's perfect and extreme forms, the Soviet reduction

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, Notes, pp. 281–282. These passages report results of other authors
(Venkov 1940, Voronoi 1908) without proof. Conventions as in `Ch12/Notes.lean` (the pairing
$\{f, h\} = \operatorname{Trace} FH$ is `venkovPairing`; $\mathrm{GL}_n(\mathbb{Z})$ acts by `act T F`
$= T^{\mathsf T}FT$, i.e. $f \mapsto f(T\vec{x})$); indices are 0-based; $N = \tfrac12 n(n+1)$ is the dimension of the space
of real forms.

**Formalized and proved**
* the definition of Venkov's domain $V(h_0)$ (`venkovDomain`) and its description by pairwise inequalities
  (`mem_venkovDomain_iff`);
* the face condition for perfect forms (`IsFaceHyperplane`, the hyperplane $\{h, \cdot\} = 1$ cuts the convex hull of
  the squares $M$ (`venkovSquares`) in a face spanning the hyperplane) and its equivalence with conditions (i)–(ii),
  i.e. with the library's definition `IsPerfect` (`isPerfect_iff_isFaceHyperplane`);
* the definition of Voronoi's domains $W(h)$ (`voronoiDomain`), of eutactic forms (`IsEutactic`) and of
  the best constant (`hermiteQuotient`);
* the consequence of "one need consider only extreme forms" (`ExtremeFormsSuffice.le_of_hermiteConstantBound`);
* the Soviet "Hermite-reduced" read literally (`IsDiagMinimal`): it forces all diagonal entries to be equal
  (`IsDiagMinimal.diag_eq`), so $x^2 + 2y^2$, which is Minkowski-reduced, fails it
  (`not_isDiagMinimal_diag_one_two`). This documents an erratum of the printed definition.

**Named statements** (cited deep theorems, assumed rather than proved, as `structure ... : Prop`):
`VenkovTheorem` (finite hyperplane description and fundamental domain), `VoronoiAlgorithm` (finite hyperplane
description of $W(h)$ and finiteness of perfect forms up to equivalence), `ExtremeFormsSuffice` (the best Hermite
constant is attained at an extreme form; proved for $n \ge 1$ in `Ch12/ExtremeForms.lean`),
`VoronoiExtremeCharacterization` (extreme $=$ perfect and eutactic),
`MinkowskiNotLexReduced` ("not necessarily vice versa").

**Reconstructed.** Cassels' "$SL^{\pm}_n$" is read as $\mathrm{GL}_n(\mathbb{Z})$ (all integral unimodular matrices). The
"proper integral automorphs" of $h_0$ are read as the integral unimodular automorphs *modulo $\pm 1$* (the matrix $-1$
acts trivially on forms; for odd $n$ this is the same as automorphs of determinant $1$).
"Fundamental domain" is made precise in `IsFundamentalDomain` (covering, and no two distinct points of the
interior, taken inside the space of symmetric matrices, are equivalent).
-/
import QuadFormsKB.Literature.Cassels.Ch12.Notes
import QuadFormsKB.Literature.Cassels.Ch12.Sec6
import QuadFormsKB.Literature.Cassels.Ch12.Sec7

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-! ### Venkov's domain (12.r51, 12.r52) -/

/-- **Venkov's domain $V(h_0)$** (Cassels, Ch. 12, Notes, p. 281): the set of strictly positive definite forms $f$ (with
matrix `F`) such that
$$\{f, h_0\} = \inf_{S} \{f, S h_0\},$$
where $S$ runs through the integral unimodular matrices `S : GL (Fin n) ℤ` and $Sh_0(\vec{x}) = h_0(S\vec{x})$ has matrix
`act S.val H0` $= S^{\mathsf T}H_0S$. Here `H0` is the matrix of the fixed form $h_0$ (strictly positive definite in the
book) and `venkovPairing` is the pairing $\{\cdot,\cdot\}$. The infimum is a greatest lower bound (`IsGLB`) of the
set of values over all $S$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (Venkov's domain V(h₀))"]
def venkovDomain (H0 : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {F | F.PosDef ∧
    IsGLB (Set.range fun S : GL (Fin n) ℤ => venkovPairing F (act S.val H0)) (venkovPairing F H0)}

/-- **$V(h_0)$ by inequalities**: `F` lies in Venkov's domain iff `F` is strictly positive definite and
$\{f, h_0\} \le \{f, Sh_0\}$ for every integral unimodular $S$ (the infimum is attained at $S = 1$). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (Venkov's domain V(h₀))"]
theorem mem_venkovDomain_iff (H0 F : Matrix (Fin n) (Fin n) ℝ) :
    F ∈ venkovDomain H0 ↔
      F.PosDef ∧ ∀ S : GL (Fin n) ℤ, venkovPairing F H0 ≤ venkovPairing F (act S.val H0) := by
  unfold venkovDomain
  refine and_congr_right fun _ => ⟨fun h S => h.1 ⟨S, rfl⟩, fun h => ⟨?_, ?_⟩⟩
  · rintro _ ⟨S, rfl⟩
    exact h S
  · intro b hb
    refine hb ⟨1, ?_⟩
    simp [act_one]

/-- **Bounded by finitely many hyperplanes** (Cassels, Ch. 12, Notes, p. 281; made precise): a set `D` of real
forms is the part, inside the cone of strictly positive definite forms, of a finite intersection of closed half-spaces
$\{f : \{f, a\} \ge 0\}$, $a$ running through a finite set `s` of real matrices (forms). -/
def IsBoundedByHyperplanes (D : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  ∃ s : Finset (Matrix (Fin n) (Fin n) ℝ), D = {F | F.PosDef ∧ ∀ A ∈ s, 0 ≤ venkovPairing F A}

/-- **Fundamental domain for the action of $\mathrm{GL}_n(\mathbb{Z})$ on strictly positive definite forms** (made
precise): a set `D` of strictly positive definite forms such that (a) every strictly positive definite form is
integrally equivalent to one in `D` (there is `T` with `act T F ∈ D`), and (b) two equivalent points of the
interior of `D` relative to the symmetric matrices (`symInterior`, Sec. 7) coincide: if `F` and `act T F` both lie in the interior then `act T F = F`. (The
matrix $-1$ acts trivially, so equivalent interior points need only agree as forms.) -/
def IsFundamentalDomain (D : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  (∀ F ∈ D, F.PosDef) ∧ (∀ F : Matrix (Fin n) (Fin n) ℝ, F.PosDef → ∃ T : GL (Fin n) ℤ, act T.val F ∈ D) ∧
    ∀ F ∈ symInterior D, ∀ T : GL (Fin n) ℤ, act T.val F ∈ symInterior D → act T.val F = F

/-- **The proper integral automorphs, modulo $\pm 1$**: the classes $\{T, -T\}$ of the integral matrices $T$ of
determinant $\pm 1$ with $h_0(T\vec{x}) = h_0(\vec{x})$ (`act T H0 = H0`). The order $g$ of this group is
`(automorphClasses H0).ncard`. -/
def automorphClasses (H0 : Matrix (Fin n) (Fin n) ℝ) : Set (Set (Matrix (Fin n) (Fin n) ℤ)) :=
  (fun T => ({T, -T} : Set (Matrix (Fin n) (Fin n) ℤ))) ''
    {T | (T.det = 1 ∨ T.det = -1) ∧ act T H0 = H0}

/-- **Venkov's theorem** (Cassels, Ch. 12, Notes, p. 281; Venkov 1940), *named statement* (cited, not proved) in
dimension `n`. For every strictly positive definite $h_0$ with matrix `H0`:
(a) $V(h_0)$ is bounded by finitely many hyperplanes (`IsBoundedByHyperplanes`);
(b) with $g$ the order of the group of automorphs modulo $\pm 1$ (`automorphClasses`), $V(h_0)$ is the union of $g$
fundamental domains `D 0, …, D (g-1)` with pairwise disjoint interiors. For $g = 1$ ($h_0$ has no nontrivial
automorph) this says $V(h_0)$ is itself a fundamental domain (`VenkovTheorem.isFundamentalDomain_of_ncard_eq_one`).
A full proof requires Venkov's theory (Voronoi-type finiteness of the set of $S$ that matter). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (Venkov: V(h₀) bounded by finitely many hyperplanes; fundamental domain)"]
structure VenkovTheorem (n : ℕ) : Prop where
  /-- $V(h_0)$ is bounded by finitely many hyperplanes. -/
  bounded : ∀ H0 : Matrix (Fin n) (Fin n) ℝ, H0.PosDef → IsBoundedByHyperplanes (venkovDomain H0)
  /-- $V(h_0)$ is a union of $g$ fundamental domains with disjoint interiors. -/
  tiling : ∀ H0 : Matrix (Fin n) (Fin n) ℝ, H0.PosDef →
    ∃ D : Fin (automorphClasses H0).ncard → Set (Matrix (Fin n) (Fin n) ℝ),
      (∀ i, IsFundamentalDomain (D i)) ∧ venkovDomain H0 = ⋃ i, D i ∧
        Pairwise fun i j => symInterior (D i) ∩ symInterior (D j) = ∅

/-- **Venkov's theorem, case without nontrivial automorphs** (Cassels, Ch. 12, Notes, p. 281): if $h_0$ is strictly
positive definite and has no automorph other than $\pm 1$ ($g = 1$), then $V(h_0)$ is a fundamental domain. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (V(h₀) is a fundamental domain if h₀ has no proper integral automorphs)"]
theorem VenkovTheorem.isFundamentalDomain_of_ncard_eq_one (hV : VenkovTheorem n)
    {H0 : Matrix (Fin n) (Fin n) ℝ} (hH0 : H0.PosDef) (hg : (automorphClasses H0).ncard = 1) :
    IsFundamentalDomain (venkovDomain H0) := by
  obtain ⟨D, hD, hU, -⟩ := hV.tiling H0 hH0
  have key : ∀ x : Fin (automorphClasses H0).ncard, x = ⟨0, by omega⟩ := fun x => by
    ext; have := x.2; omega
  have hU' : venkovDomain H0 = D ⟨0, by omega⟩ := by
    rw [hU]
    ext F
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => by rwa [key i] at hi, fun h => ⟨_, h⟩⟩
  rw [hU']
  exact hD _

/-! ### The face condition for perfect forms (12.r54) -/

/-- **The set $M$ of squares** (Cassels, Ch. 12, Notes, p. 281): the forms $(\vec{m}\cdot\vec{x})^2$, matrix
$\vec{m}\vec{m}^{\mathsf T}$, with $\vec{m}$ running through the nonzero integral vectors. -/
def venkovSquares (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∃ m : Fin n → ℤ, m ≠ 0 ∧ A = vecMulVec (cast m) (cast m)}

/-- **The hyperplane $\{h, \cdot\} = 1$ is a face of the convex cover of $M$** (Cassels, Ch. 12, Notes, p. 281; made
precise): `H` is symmetric, the convex hull of $M$ lies in the half-space $\{h, \cdot\} \ge 1$ (so the hyperplane is
a supporting hyperplane and its intersection with the hull is a face), and that face spans the hyperplane: the affine span
of the hull $\cap \{\{h, \cdot\} = 1\}$ is the whole hyperplane $\{f \text{ symmetric} : \{h, f\} = 1\}$ in the
$N$-dimensional space of forms (so the face has the full dimension $N - 1$). -/
def IsFaceHyperplane (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.IsSymm ∧ convexHull ℝ (venkovSquares n) ⊆ {A | 1 ≤ venkovPairing H A} ∧
    (affineSpan ℝ (convexHull ℝ (venkovSquares n) ∩ {A | venkovPairing H A = 1}) :
        Set (Matrix (Fin n) (Fin n) ℝ)) = {A | A.IsSymm ∧ venkovPairing H A = 1}

/-- Helper: the Venkov pairing with a fixed matrix, as a linear functional. -/
noncomputable def faceAux_pairingL (F : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A := venkovPairing F A
  map_add' A B := by simp [venkovPairing, Matrix.mul_add, Matrix.trace_add]
  map_smul' c A := by simp [venkovPairing, Matrix.trace_smul]

/-- Helper: the Venkov pairing is affine in the second argument. -/
theorem faceAux_pairing_affine (F p q r : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    venkovPairing F (c • (p - q) + r) =
      c * (venkovPairing F p - venkovPairing F q) + venkovPairing F r := by
  simp [venkovPairing, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_sub]

/-- Helper: the Venkov pairing is linear in the first argument. -/
theorem faceAux_pairing_sub_left (F G A : Matrix (Fin n) (Fin n) ℝ) :
    venkovPairing (F - G) A = venkovPairing F A - venkovPairing G A := by
  simp [venkovPairing, Matrix.sub_mul, Matrix.trace_sub]

/-- Helper: a set of matrices closed under $c(p - q) + r$ as an affine subspace. -/
def faceAux_aff (X : Set (Matrix (Fin n) (Fin n) ℝ))
    (h : ∀ (c : ℝ) (p q r : Matrix (Fin n) (Fin n) ℝ), p ∈ X → q ∈ X → r ∈ X →
      c • (p - q) + r ∈ X) : AffineSubspace ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := X
  smul_vsub_vadd_mem' c p q r hp hq hr := h c p q r hp hq hr

/-- Helper: the affine span of a subset of an affine-closed set stays in it. -/
theorem faceAux_affineSpan_subset (X T : Set (Matrix (Fin n) (Fin n) ℝ))
    (h : ∀ (c : ℝ) (p q r : Matrix (Fin n) (Fin n) ℝ), p ∈ X → q ∈ X → r ∈ X →
      c • (p - q) + r ∈ X) (hT : T ⊆ X) : (affineSpan ℝ T : Set (Matrix (Fin n) (Fin n) ℝ)) ⊆ X :=
  affineSpan_le (Q := faceAux_aff X h) |>.2 hT

/-- Helper: the outer products $m m^{\mathsf T}$ are symmetric. -/
theorem faceAux_vecMulVec_symm (a : Fin n → ℝ) : (vecMulVec a a).IsSymm := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- Helper: the convex hull of the squares consists of symmetric matrices. -/
theorem faceAux_hull_symm : convexHull ℝ (venkovSquares n) ⊆ {A | A.IsSymm} := by
  apply convexHull_min
  · rintro _ ⟨m, -, rfl⟩
    exact faceAux_vecMulVec_symm _
  · intro x hx y hy a b _ _ _
    exact (hx.smul a).add (hy.smul b)

/-- Helper: the half-space $\{A : 1 \le \{H, A\}\}$ is convex. -/
theorem faceAux_convex_half (H : Matrix (Fin n) (Fin n) ℝ) :
    Convex ℝ {A : Matrix (Fin n) (Fin n) ℝ | 1 ≤ venkovPairing H A} := by
  intro x hx y hy a b ha hb hab
  have key : venkovPairing H (a • x + b • y) = a * venkovPairing H x + b * venkovPairing H y := by
    simp [venkovPairing, Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]
  show 1 ≤ venkovPairing H (a • x + b • y)
  rw [key]
  have hx' : 1 ≤ venkovPairing H x := hx
  have hy' : 1 ≤ venkovPairing H y := hy
  nlinarith

/-- Helper: every linear functional on matrices is the pairing with a symmetric matrix, on symmetric
matrices. -/
theorem faceAux_dual (φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    ∃ G : Matrix (Fin n) (Fin n) ℝ, G.IsSymm ∧ ∀ X, X.IsSymm → φ X = venkovPairing G X := by
  refine ⟨Matrix.of fun i j => (φ (Matrix.single i j 1) + φ (Matrix.single j i 1)) / 2, ?_, ?_⟩
  · ext i j
    simp [add_comm]
  · intro X hX
    have hX' : ∀ i j, X j i = X i j := fun i j => by
      have := congrFun (congrFun hX i) j
      simpa using this
    have h1 : φ X = ∑ i, ∑ j, X i j * φ (Matrix.single i j 1) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have : (Matrix.single i j (X i j) : Matrix (Fin n) (Fin n) ℝ) = X i j • Matrix.single i j 1 := by
        simp [Matrix.smul_single]
      rw [this, map_smul, smul_eq_mul]
    rw [h1]
    unfold venkovPairing
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
    have hswap : ∑ i, ∑ j, φ (Matrix.single j i 1) * X j i
        = ∑ i, ∑ j, φ (Matrix.single i j 1) * X i j := Finset.sum_comm
    have hrw : ∀ i j, (φ (Matrix.single i j 1) + φ (Matrix.single j i 1)) / 2 * X j i =
        (φ (Matrix.single i j 1) * X i j + φ (Matrix.single j i 1) * X j i) / 2 := by
      intro i j; rw [hX' i j]; ring
    simp only [hrw, ← Finset.sum_div, Finset.sum_add_distrib, hswap]
    simp only [mul_comm (X _ _)]
    ring

/-- Helper: a set `S₁` of matrices on which the pairing with `H` is $1$; a matrix of pairing $1$ in its
linear span lies in its affine span. -/
theorem faceAux_mem_affineSpan (H : Matrix (Fin n) (Fin n) ℝ) (S₁ : Set (Matrix (Fin n) (Fin n) ℝ))
    (hS : ∀ s ∈ S₁, venkovPairing H s = 1) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Submodule.span ℝ S₁) (hP : venkovPairing H A = 1) : A ∈ affineSpan ℝ S₁ := by
  obtain ⟨s₀, hs₀⟩ : S₁.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [Submodule.span_empty, Submodule.mem_bot] at hA
    subst hA
    simp [venkovPairing] at hP
  have key : ∀ x ∈ Submodule.span ℝ S₁,
      x - venkovPairing H x • s₀ ∈ vectorSpan ℝ S₁ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      rw [hS x hx, one_smul]
      exact vsub_mem_vectorSpan ℝ hx hs₀
    | zero => simp [venkovPairing]
    | add x y _ _ hx hy =>
      have : venkovPairing H (x + y) = venkovPairing H x + venkovPairing H y := by
        simp [venkovPairing, Matrix.mul_add, Matrix.trace_add]
      rw [this, add_smul]
      have := Submodule.add_mem _ hx hy
      convert this using 1
      abel
    | smul a x _ hx =>
      have : venkovPairing H (a • x) = a * venkovPairing H x := by
        simp [venkovPairing, Matrix.trace_smul]
      rw [this, mul_smul, ← smul_sub]
      exact Submodule.smul_mem _ a hx
  have h1 := key A hA
  rw [hP, one_smul] at h1
  have h2 : A -ᵥ s₀ ∈ (affineSpan ℝ S₁).direction := by
    rw [direction_affineSpan]; exact h1
  exact (AffineSubspace.vsub_right_mem_direction_iff_mem (subset_affineSpan ℝ S₁ hs₀) A).1 h2

/-- Helper: for a perfect form the matrices $m m^{\mathsf T}$ with $h(m) = 1$ span all symmetric
matrices (linearly). -/
theorem faceAux_span {H : Matrix (Fin n) (Fin n) ℝ} (hsym : H.IsSymm)
    (hii : ∀ F : Matrix (Fin n) (Fin n) ℝ, F.IsSymm →
      (∀ m : Fin n → ℤ, val H (cast m) = 1 → val F (cast m) = 1) → F = H)
    (A : Matrix (Fin n) (Fin n) ℝ) (hAs : A.IsSymm) :
    A ∈ Submodule.span ℝ {B : Matrix (Fin n) (Fin n) ℝ |
      ∃ m : Fin n → ℤ, val H (cast m) = 1 ∧ B = vecMulVec (cast m) (cast m)} := by
  by_contra hnot
  obtain ⟨φ, hφA, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  obtain ⟨G, hG, hGφ⟩ := faceAux_dual φ
  have hvanish : ∀ m : Fin n → ℤ, val H (cast m) = 1 → val G (cast m) = 0 := by
    intro m hm
    have hmem : vecMulVec (cast m) (cast m) ∈ Submodule.span ℝ {B : Matrix (Fin n) (Fin n) ℝ |
      ∃ m : Fin n → ℤ, val H (cast m) = 1 ∧ B = vecMulVec (cast m) (cast m)} :=
      Submodule.subset_span ⟨m, hm, rfl⟩
    have h0 : φ (vecMulVec (cast m) (cast m)) ∈ (Submodule.span ℝ {B : Matrix (Fin n) (Fin n) ℝ |
      ∃ m : Fin n → ℤ, val H (cast m) = 1 ∧ B = vecMulVec (cast m) (cast m)}).map φ :=
      Submodule.mem_map_of_mem hmem
    rw [hφ, Submodule.mem_bot] at h0
    rw [hGφ _ (faceAux_vecMulVec_symm _), venkovPairing_vecMulVec] at h0
    exact h0
  have hFH := hii (H + G) (hsym.add hG) (fun m hm => by
    have : val (H + G) (cast m) = val H (cast m) + val G (cast m) := by
      simp [val, Matrix.add_mulVec, dotProduct_add]
    rw [this, hm, hvanish m hm, add_zero])
  have hG0 : G = 0 := by
    have := congrArg (fun M => M - H) hFH
    simpa using this
  apply hφA
  rw [hGφ A hAs, hG0]
  simp [venkovPairing]

/-- Helper: a perfect form gives a face hyperplane. -/
theorem faceAux_isFaceHyperplane_of_isPerfect {H : Matrix (Fin n) (Fin n) ℝ} (hP : IsPerfect H) :
    IsFaceHyperplane H := by
  obtain ⟨hsym, hi, hii⟩ := hP
  refine ⟨hsym, ?_, ?_⟩
  · apply convexHull_min
    · rintro _ ⟨m, hm, rfl⟩
      show 1 ≤ venkovPairing H _
      rw [venkovPairing_vecMulVec]; exact hi m hm
    · exact faceAux_convex_half H
  · apply Set.Subset.antisymm
    · refine faceAux_affineSpan_subset _ _ ?_ ?_
      · rintro c p q r ⟨hp1, hp2⟩ ⟨hq1, hq2⟩ ⟨hr1, hr2⟩
        refine ⟨((hp1.sub hq1).smul c).add hr1, ?_⟩
        show venkovPairing H _ = 1
        rw [faceAux_pairing_affine, hp2, hq2, hr2]; ring
      · rintro A ⟨hA1, hA2⟩
        exact ⟨faceAux_hull_symm hA1, hA2⟩
    · rintro A ⟨hAs, hA1⟩
      have hsub : {B : Matrix (Fin n) (Fin n) ℝ |
          ∃ m : Fin n → ℤ, val H (cast m) = 1 ∧ B = vecMulVec (cast m) (cast m)} ⊆
          convexHull ℝ (venkovSquares n) ∩ {A | venkovPairing H A = 1} := by
        rintro _ ⟨m, hm, rfl⟩
        have hm0 : m ≠ 0 := by
          rintro rfl
          simp [val, cast, dotProduct] at hm
        refine ⟨subset_convexHull ℝ _ ⟨m, hm0, rfl⟩, ?_⟩
        show venkovPairing H _ = 1
        rw [venkovPairing_vecMulVec]; exact hm
      refine affineSpan_mono ℝ hsub ?_
      refine faceAux_mem_affineSpan H _ ?_ A (faceAux_span hsym hii A hAs) hA1
      rintro _ ⟨m, hm, rfl⟩
      rw [venkovPairing_vecMulVec]; exact hm

/-- Helper: the pairing with $E_{ij}$ picks out the entry $(j, i)$. -/
theorem faceAux_pairing_single (F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    venkovPairing F (Matrix.single i j (1 : ℝ)) = F j i := by
  simp [venkovPairing, Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- Helper: a face hyperplane gives a perfect form. -/
theorem faceAux_isPerfect_of_isFaceHyperplane {H : Matrix (Fin n) (Fin n) ℝ}
    (h : IsFaceHyperplane H) : IsPerfect H := by
  obtain ⟨hsym, hhull, hspan⟩ := h
  have hi : ∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val H (cast m) := by
    intro m hm
    have h1 : vecMulVec (cast m) (cast m) ∈ convexHull ℝ (venkovSquares n) :=
      subset_convexHull ℝ _ ⟨m, hm, rfl⟩
    have h2 := hhull h1
    rwa [Set.mem_ofPred_eq, venkovPairing_vecMulVec] at h2
  refine ⟨hsym, hi, ?_⟩
  intro F hF hFm
  have hT : ∀ A ∈ convexHull ℝ (venkovSquares n) ∩ {A | venkovPairing H A = 1},
      venkovPairing F A = 1 := by
    rintro A ⟨hA, hA1⟩
    rw [convexHull_eq] at hA
    obtain ⟨ι, t, w, z, hw0, hw1, hz, rfl⟩ := hA
    rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hA1 ⊢
    have hlin : ∀ G : Matrix (Fin n) (Fin n) ℝ, venkovPairing G (∑ i ∈ t, w i • z i) =
        ∑ i ∈ t, w i * venkovPairing G (z i) := by
      intro G
      have := map_sum (faceAux_pairingL G) (fun i => w i • z i) t
      simp only [map_smul, smul_eq_mul] at this
      exact this
    have hA1' := hA1
    rw [Set.mem_ofPred_eq, hlin] at hA1'
    rw [hlin]
    have hz1 : ∀ i ∈ t, 1 ≤ venkovPairing H (z i) := fun i hi =>
      hhull (subset_convexHull ℝ _ (hz i hi))
    have hzero : ∀ i ∈ t, w i * (venkovPairing H (z i) - 1) = 0 := by
      have hsum : ∑ i ∈ t, w i * (venkovPairing H (z i) - 1) = 0 := by
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib, hA1', hw1]; ring
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => mul_nonneg (hw0 i hi) (sub_nonneg.2 (hz1 i hi)))).1 hsum
    have : ∑ i ∈ t, w i * venkovPairing F (z i) = ∑ i ∈ t, w i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rcases mul_eq_zero.1 (hzero i hi) with h0 | h1
      · rw [h0]; simp
      · obtain ⟨m, hm, hzm⟩ := hz i hi
        have hHm : val H (cast m) = 1 := by
          rw [← venkovPairing_vecMulVec, ← hzm]; linarith
        rw [hzm, venkovPairing_vecMulVec, hFm m hHm, mul_one]
    rw [this, hw1]
  have hclosed : ∀ (c : ℝ) (p q r : Matrix (Fin n) (Fin n) ℝ),
      p ∈ {A | venkovPairing F A = 1} → q ∈ {A | venkovPairing F A = 1} →
      r ∈ {A | venkovPairing F A = 1} → c • (p - q) + r ∈ {A | venkovPairing F A = 1} := by
    intro c p q r hp hq hr
    show venkovPairing F _ = 1
    rw [faceAux_pairing_affine, show venkovPairing F p = 1 from hp, show venkovPairing F q = 1 from hq,
      show venkovPairing F r = 1 from hr]
    ring
  have hX : ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → venkovPairing H A = 1 →
      venkovPairing F A = 1 := by
    intro A hAs hA1
    have hmem : A ∈ (affineSpan ℝ (convexHull ℝ (venkovSquares n) ∩
        {A | venkovPairing H A = 1}) : Set (Matrix (Fin n) (Fin n) ℝ)) := by
      rw [hspan]; exact ⟨hAs, hA1⟩
    exact faceAux_affineSpan_subset _ _ hclosed hT hmem
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hm₀ : (Pi.single ⟨0, hn⟩ (1 : ℤ) : Fin n → ℤ) ≠ 0 := fun h => by
    simpa using congrFun h ⟨0, hn⟩
  set m₀ : Fin n → ℤ := Pi.single ⟨0, hn⟩ (1 : ℤ) with hm₀def
  set c : ℝ := val H (cast m₀) with hc
  have hc1 : 1 ≤ c := hi m₀ hm₀
  have hcpos : 0 < c := by linarith
  set X₀ : Matrix (Fin n) (Fin n) ℝ := c⁻¹ • vecMulVec (cast m₀) (cast m₀) with hX₀
  have hX₀s : X₀.IsSymm := (faceAux_vecMulVec_symm _).smul _
  have hX₀P : venkovPairing H X₀ = 1 := by
    have : venkovPairing H X₀ = c⁻¹ * venkovPairing H (vecMulVec (cast m₀) (cast m₀)) := by
      simp [hX₀, venkovPairing, Matrix.trace_smul]
    rw [this, venkovPairing_vecMulVec, ← hc]
    field_simp
  have hX₀F : venkovPairing F X₀ = 1 := hX X₀ hX₀s hX₀P
  have hall : ∀ X : Matrix (Fin n) (Fin n) ℝ, X.IsSymm →
      venkovPairing F X = venkovPairing H X := by
    intro X hXs
    set t := venkovPairing H X with ht
    have hYs : (X - t • X₀ + X₀).IsSymm := ((hXs.sub (hX₀s.smul t)).add hX₀s)
    have hYP : venkovPairing H (X - t • X₀ + X₀) = 1 := by
      have e1 : venkovPairing H (X - t • X₀ + X₀) = venkovPairing H X - t * 1 + 1 := by
        have h1 : X - t • X₀ + X₀ = (1 : ℝ) • (X - t • X₀) + X₀ := by rw [one_smul]
        have h2 : venkovPairing H (X - t • X₀) = venkovPairing H X - t * venkovPairing H X₀ := by
          simp [venkovPairing, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul]
        have h3 : venkovPairing H (X - t • X₀ + X₀) = venkovPairing H (X - t • X₀) + venkovPairing H X₀ := by
          simp [venkovPairing, Matrix.mul_add, Matrix.trace_add]
        rw [h3, h2, hX₀P]
      rw [e1]; ring
    have h4 := hX _ hYs hYP
    have h2 : venkovPairing F (X - t • X₀) = venkovPairing F X - t * venkovPairing F X₀ := by
      simp [venkovPairing, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_smul]
    have h3 : venkovPairing F (X - t • X₀ + X₀) = venkovPairing F (X - t • X₀) + venkovPairing F X₀ := by
      simp [venkovPairing, Matrix.mul_add, Matrix.trace_add]
    rw [h3, h2, hX₀F] at h4
    linarith
  ext i j
  have hs : (Matrix.single i j (1 : ℝ) + Matrix.single j i 1).IsSymm := by
    show (_ : Matrix (Fin n) (Fin n) ℝ)ᵀ = _
    rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]
  have h5 := hall _ hs
  have e : ∀ G : Matrix (Fin n) (Fin n) ℝ, venkovPairing G (Matrix.single i j (1 : ℝ) + Matrix.single j i 1)
      = G j i + G i j := by
    intro G
    have : venkovPairing G (Matrix.single i j (1 : ℝ) + Matrix.single j i 1) =
        venkovPairing G (Matrix.single i j 1) + venkovPairing G (Matrix.single j i 1) := by
      simp [venkovPairing, Matrix.mul_add, Matrix.trace_add]
    rw [this, faceAux_pairing_single, faceAux_pairing_single]
  rw [e, e] at h5
  have hFs : ∀ a b, F b a = F a b := fun a b => by simpa using congrFun (congrFun hF a) b
  have hHs : ∀ a b, H b a = H a b := fun a b => by simpa using congrFun (congrFun hsym a) b
  have h6 := hFs i j
  have h7 := hHs i j
  linarith

/-- **Perfect forms and the face condition** (Cassels, Ch. 12, Notes, p. 281): for a real matrix $H$ (the form
$h$), $h$ is perfect (`IsPerfect`: symmetric, $h(\vec{m}) \ge 1$ for all nonzero integral $\vec{m}$, and $h$ is the
only symmetric form taking the value $1$ at every $\vec{m}$ with $h(\vec{m}) = 1$) if and only if the hyperplane
$\{h, \cdot\} = 1$ is a face of the convex hull of the squares spanning that hyperplane (`IsFaceHyperplane`).
The key identity is $\{h, \vec{m}\vec{m}^{\mathsf T}\} = h(\vec{m})$ (`venkovPairing_vecMulVec`). Valid for all
$n$, including $n = 0$ (both sides hold). Proof: (perfect $\Rightarrow$ face) the span of the squares
$\vec{m}\vec{m}^{\mathsf T}$ with $h(\vec{m}) = 1$ contains every symmetric matrix, by a separating linear functional
and condition (ii); (face $\Rightarrow$ perfect) a convex combination of squares with pairing $1$ uses only squares
with $h(\vec{m}) = 1$, so any $F$ as in (ii) has $\{f, \cdot\} = 1$ on the face, hence on its affine span. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (face condition equivalent to (i)–(ii))"]
theorem isPerfect_iff_isFaceHyperplane (H : Matrix (Fin n) (Fin n) ℝ) :
    IsPerfect H ↔ IsFaceHyperplane H :=
  ⟨faceAux_isFaceHyperplane_of_isPerfect, faceAux_isPerfect_of_isFaceHyperplane⟩

/-! ### Voronoi's domains and Voronoi's algorithm (12.r55) -/

/-- **Voronoi's domain $W(h)$** (Cassels, Ch. 12, Notes, p. 281): for a perfect form $h$ (matrix `H`), the set of
strictly positive definite forms $f$ with $\{f, h\} = \inf_g \{f, g\}$, $g$ running through the perfect forms
(`IsPerfect`; the infimum is a greatest lower bound). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (Voronoi's domain W(h))"]
def voronoiDomain (H : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {F | F.PosDef ∧ IsGLB ((fun G => venkovPairing F G) '' {G | IsPerfect G}) (venkovPairing F H)}

/-- **Voronoi's algorithm** (Cassels, Ch. 12, Notes, p. 281; Voronoi 1908), *named statement* (cited, not proved) in
dimension `n`: (a) for every perfect form $h$ the domain $W(h)$ is bounded by finitely many hyperplanes; (b) there are
only finitely many perfect forms up to integral equivalence: a finite set `s` of perfect forms such that every perfect
form is `act T g` for some `g ∈ s` and unimodular `T`. (The algorithm walks from one $W(h)$ across its facets to the
neighbouring ones; a full proof is Voronoi's theory of perfect forms.) -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (Voronoi: each W(h) bounded by finitely many hyperplanes; algorithm for perfect forms)"]
structure VoronoiAlgorithm (n : ℕ) : Prop where
  /-- Each $W(h)$ is bounded by finitely many hyperplanes. -/
  bounded : ∀ H : Matrix (Fin n) (Fin n) ℝ, IsPerfect H → IsBoundedByHyperplanes (voronoiDomain H)
  /-- Finitely many perfect forms up to integral equivalence. -/
  finite_classes : ∃ s : Finset (Matrix (Fin n) (Fin n) ℝ), (∀ g ∈ s, IsPerfect g) ∧
    ∀ H, IsPerfect H → ∃ g ∈ s, ∃ T : GL (Fin n) ℤ, act T.val g = H

/-! ### Extreme forms and the best constant (12.r56, 12.r58) -/

/-- **The Hermite quotient** $\min f / d(f)^{1/n}$ (Cassels, Ch. 12, Thm. 2.1, p. 260, and Notes, p. 281): for a real form
with matrix `F`, the infimum of $f(\vec{m})$ over nonzero integral $\vec{m}$ divided by $(\det F)^{1/n}$. The best
possible constant $\gamma_n$ of Theorem 2.1 is the supremum of this over strictly positive definite forms. -/
noncomputable def hermiteQuotient (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf ((fun m : Fin n → ℤ => val F (cast m)) '' {m | m ≠ 0}) / F.det ^ ((1 : ℝ) / n)

/-- **Only extreme forms matter for $\gamma_n$** (Cassels, Ch. 12, Notes, p. 281, "to obtain the best possible value of
$\gamma_n$ one need consider only extreme forms"), *named statement* (cited, not proved) in dimension `n`: the
supremum of the Hermite quotient over strictly positive definite forms is attained at an extreme form
(`IsExtreme`). **Proved** for every $n \ge 1$ by Mahler's compactness argument: `extremeFormsSuffice_holds`
(`Ch12/ExtremeForms.lean`). For $n = 0$ it is false (no form has minimum $1$, there being no nonzero integral vector). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (best γ_n: only extreme forms need be considered)"]
structure ExtremeFormsSuffice (n : ℕ) : Prop where
  /-- Some extreme form has the largest Hermite quotient. -/
  exists_extreme : ∃ H : Matrix (Fin n) (Fin n) ℝ, IsExtreme H ∧
    ∀ F : Matrix (Fin n) (Fin n) ℝ, F.PosDef → hermiteQuotient F ≤ hermiteQuotient H

/-- **Consequence**: if only extreme forms matter (`ExtremeFormsSuffice`) and `γ` satisfies Theorem 2.1 in dimension
$n > 0$ (`HermiteConstantBound`), then the Hermite quotient of that extreme form is at most `γ`; so this quotient is
a lower bound for every admissible constant, and the maximal quotient over all forms is attained there. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (best γ_n: only extreme forms need be considered)"]
theorem ExtremeFormsSuffice.le_of_hermiteConstantBound (hE : ExtremeFormsSuffice n) (hn : 0 < n) {γ : ℝ}
    (hγ : HermiteConstantBound n γ) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, IsExtreme H ∧ (∀ F : Matrix (Fin n) (Fin n) ℝ, F.PosDef → hermiteQuotient F ≤ hermiteQuotient H) ∧
      hermiteQuotient H ≤ γ := by
  obtain ⟨H, hH, hmax⟩ := hE.exists_extreme
  refine ⟨H, hH, hmax, ?_⟩
  obtain ⟨hpd, hglb, -⟩ := hH
  have hne : ((fun m : Fin n → ℤ => val H (cast m)) '' {m | m ≠ 0}).Nonempty :=
    ⟨_, Pi.single ⟨0, hn⟩ 1, fun h => by simpa using congrFun h ⟨0, hn⟩, rfl⟩
  have hinf : sInf ((fun m : Fin n → ℤ => val H (cast m)) '' {m | m ≠ 0}) = 1 := hglb.csInf_eq hne
  unfold hermiteQuotient
  rw [hinf]
  have hdet : 0 < H.det := hpd.det_pos
  have hp : 0 < H.det ^ ((1 : ℝ) / n) := Real.rpow_pos_of_pos hdet _
  rw [div_le_iff₀ hp]
  obtain ⟨m, hm, hle⟩ := hγ H hpd
  exact (hglb.1 ⟨m, hm, rfl⟩).trans hle

/-- **Eutactic form** (Cassels, Ch. 12, Notes, p. 282, "a further property ('eutactic')"; Voronoi): a strictly positive
definite form $h$ with matrix `H` and minimum $1$ (`IsGLB` of its values at nonzero integral vectors is $1$) is
eutactic if its set $M_1(h) = \{\vec{m} : h(\vec{m}) = 1\}$ of minimal vectors is finite and the inverse matrix is a
positive combination of the squares of the minimal vectors:
$$H^{-1} = \sum_{\vec{m} \in M_1(h)} \lambda_{\vec{m}}\,\vec{m}\vec{m}^{\mathsf T}, \qquad \lambda_{\vec{m}} > 0 \text{ for all }
\vec{m} \in M_1(h)$$
(`c m` is $\lambda_{\vec{m}}$; $\pm\vec{m}$ are counted separately, which changes nothing). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (eutactic forms)"]
def IsEutactic (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.PosDef ∧ IsGLB ((fun m : Fin n → ℤ => val H (cast m)) '' {m | m ≠ 0}) 1 ∧
    {m : Fin n → ℤ | val H (cast m) = 1}.Finite ∧
    ∃ c : (Fin n → ℤ) → ℝ, (∀ m, val H (cast m) = 1 → 0 < c m) ∧
      H⁻¹ = ∑ᶠ m ∈ {m : Fin n → ℤ | val H (cast m) = 1}, c m • vecMulVec (cast m) (cast m)

/-- **Voronoi's characterization of extreme forms** (Cassels, Ch. 12, Notes, p. 282; Voronoi 1908), *named statement*
(cited, not proved) in dimension `n`: a form is extreme iff it is perfect and eutactic. A full proof is Voronoi's
second-order analysis of $\det$ on the set of forms with minimum $1$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Voronoi: extreme = perfect and eutactic)"]
structure VoronoiExtremeCharacterization (n : ℕ) : Prop where
  /-- Extreme forms are exactly the perfect, eutactic forms. -/
  extreme_iff : ∀ H : Matrix (Fin n) (Fin n) ℝ, IsExtreme H ↔ IsPerfect H ∧ IsEutactic H

/-! ### The Soviet "Hermite-reduced" (12.r62) -/

/-- **The Soviet definition read literally** (Cassels, Ch. 12, Notes, p. 282): a strictly positive definite $F$ with
$f_{ii} \le f^*_{ii}$ for each $i = 0, \dots, n-1$ separately and for every form $f^*$ integrally equivalent to $f$
(`act T F`, $T$ unimodular). *Erratum:* read this way the condition forces all $f_{ii}$ to be equal
(`IsDiagMinimal.diag_eq`), so the library's `IsLexReduced` (lexicographic order, Ryškov) is the intended notion. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Soviet Hermite reduction, literal reading; erratum)"]
def IsDiagMinimal (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  F.PosDef ∧ ∀ T : GL (Fin n) ℤ, ∀ i, F i i ≤ act T.val F i i

/-- Helper: the unimodular matrix exchanging the variables $x_i$ and $x_j$. -/
def swapGL (i j : Fin n) : GL (Fin n) ℤ :=
  ⟨(Equiv.swap i j).permMatrix ℤ, (Equiv.swap i j).permMatrix ℤ, by
    rw [← Matrix.permMatrix_mul]; simp, by rw [← Matrix.permMatrix_mul]; simp⟩

/-- Helper: exchanging the variables $x_i, x_j$ moves the diagonal entry $f_{jj}$ to position $i$:
$(\mathrm{swap}^{\mathsf T}F\,\mathrm{swap})_{ii} = f_{jj}$. -/
theorem swapGL_diag (F : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    act (swapGL i j).val F i i = F j j := by
  rw [act_diag, ← val_single F j]
  congr 1
  ext k
  simp only [swapGL, Matrix.permMatrix_mulVec, Function.comp_apply, Pi.single_apply, cast]
  by_cases hk : k = j
  · simp [hk]
  · have : (Equiv.swap i j) k ≠ i := by
      intro h
      apply hk
      have := (Equiv.swap_apply_eq_iff.1 h)
      simpa using this
    simp [hk, this]

/-- **The literal reading forces equal diagonal entries** (Cassels, Ch. 12, Notes, p. 282): if $f_{ii} \le f^*_{ii}$ for
all $i$ and all equivalent $f^*$, then $f_{ii} = f_{jj}$ for all $i, j$ (exchange the variables $x_i, x_j$ and use the
inequality twice). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Soviet Hermite reduction, literal reading forces equal diagonal)"]
theorem IsDiagMinimal.diag_eq {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsDiagMinimal F) (i j : Fin n) :
    F i i = F j j := by
  have h1 := hF.2 (swapGL i j) i
  have h2 := hF.2 (swapGL j i) j
  rw [swapGL_diag] at h1 h2
  exact le_antisymm h1 h2

/-- **A Minkowski-reduced form failing the literal condition** (Cassels, Ch. 12, Notes, p. 282): $x^2 + 2y^2$ (matrix
`!![1, 0; 0, 2]`) is Minkowski-reduced but not `IsDiagMinimal`, so the literal reading of the printed definition
is strictly stronger than Minkowski reduction and cannot be what is meant. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (x² + 2y² is Minkowski-reduced but fails the literal Soviet condition)"]
theorem not_isDiagMinimal_diag_one_two :
    IsMinkowskiReduced (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) ∧
      ¬ IsDiagMinimal (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hs : (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  refine ⟨(binary_isMinkowskiReduced_iff hs).2 ?_, fun h => ?_⟩
  · norm_num
  · have := h.diag_eq 0 1
    norm_num at this

/-- **"But not necessarily vice versa"** (Cassels, Ch. 12, Notes, p. 282), *named statement* (cited, not proved): the
converse of `IsLexReduced.isMinkowskiReduced` fails: for some dimension $n$ there is a Minkowski-reduced form that is
not lexicographically reduced. (Cassels refers to Ryškov 1971–73. A different choice of first basis vector of the
same minimal length can allow a smaller later diagonal entry; the dimension is presumably $n \ge 5$. An explicit
example would require verifying infinitely many Minkowski conditions.) -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Minkowski-reduced does not imply Soviet Hermite-reduced)"]
structure MinkowskiNotLexReduced : Prop where
  /-- Some Minkowski-reduced form is not lexicographically reduced. -/
  exists_form : ∃ (n : ℕ) (F : Matrix (Fin n) (Fin n) ℝ), IsMinkowskiReduced F ∧ ¬ IsLexReduced F

end QuadFormsKB.Reduction
