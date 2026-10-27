/-
# Cassels, Chapter 12: the Notes (Venkov, Voronoi, extreme forms, lexicographic reduction)

Cassels, *Rational Quadratic Forms* (1978), Ch. 12, Notes, pp. 280–282. The Notes survey the literature without
proofs; the definitions and the two short arguments they contain are formalized here:

* Venkov's pairing $\{f, h\} = \sum_{i,j} f_{ij}h_{ij} = \operatorname{Trace} FH$ (`venkovPairing`, p. 280), its value at a
  square of a linear form (`venkovPairing_vecMulVec`), $\{f, h\} \ge 0$ on $\mathcal P$ (`venkovPairing_nonneg`) and
  the bracketed claim "$f \in \mathcal P$ iff $\{f, h\} \ge 0$ for all $h \in \mathcal P$" (`posSemidef_iff_venkovPairing`,
  p. 281);
* perfect forms (`IsPerfect`, Voronoi, p. 281) and extreme forms (`IsExtreme`, p. 281, 12.d2);
* the "Soviet" Hermite reduction (`IsLexReduced`, p. 282) and "such a form is clearly Minkowski-reduced"
  (`IsLexReduced.isMinkowskiReduced`).

**Not formalized** (stated in the Notes without proof): Minkowski's conditions for $n = 5, 6$ (Ryškov, Tammela) and
$n = 7$ (Tammela); Venkov's theorem that $V(h_0)$ is bounded by finitely many hyperplanes and is a fundamental domain;
Voronoi's algorithm and the characterization of extreme forms as perfect and eutactic; the tables of reduced forms.
-/
import QuadFormsKB.Literature.Cassels.Ch12.Sec5

open Matrix

namespace QuadFormsKB.Reduction

variable {n : ℕ}

/-- **Venkov's pairing** (Cassels, Ch. 12, Notes, p. 280): for real forms $f, h$ with matrices $F, H$,
$$\{f, h\} = \sum_{i,j} f_{ij}h_{ij} = \operatorname{Trace} FH$$
(for symmetric $H$; the trace form is used for all matrices). A symmetric bilinear form on the space of forms, of
dimension $N = \tfrac12 n(n+1)$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 280 (Venkov: {f, h} = Trace FH)"]
def venkovPairing (F H : Matrix (Fin n) (Fin n) ℝ) : ℝ := (F * H).trace

/-- **The pairing with a square** (Cassels, Ch. 12, p. 280, the forms $(*)$): for $h(\vec{x}) = (a_0x_0 + \dots +
a_{n-1}x_{n-1})^2$, with matrix $\vec{a}\vec{a}^{\mathsf T}$, $\{f, h\} = f(\vec{a})$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 280 (the pairing with a square (*))"]
theorem venkovPairing_vecMulVec (F : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) :
    venkovPairing F (vecMulVec a a) = val F a := by
  unfold venkovPairing val
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **$\{f, h\} \ge 0$ on $\mathcal P$** (Cassels, Ch. 12, Notes, p. 280, "it readily follows by bilinearity"): for positive
semi-definite $F$ and $H$, $\operatorname{Trace} FH \ge 0$ ($H$ is a sum of squares of linear forms). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 280 ({f, h} ≥ 0 on 𝒫)"]
theorem venkovPairing_nonneg {F H : Matrix (Fin n) (Fin n) ℝ} (hF : F.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ venkovPairing F H := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.1 hH
  unfold venkovPairing
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  have := venkovPairing_vecMulVec F (v k)
  unfold venkovPairing at this
  have hs : star (v k) = v k := by ext; simp
  rw [hs, this]
  exact ((posSemidef_iff F).1 hF).2 _

/-- **$\mathcal P$ is self-dual for Venkov's pairing** (Cassels, Ch. 12, Notes, p. 281, the bracketed remark): a real
symmetric $F$ is positive semi-definite iff $\{f, h\} \ge 0$ for every positive semi-definite $h$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (f ∈ 𝒫 iff {f, h} ≥ 0 for all h ∈ 𝒫)"]
theorem posSemidef_iff_venkovPairing {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsSymm) :
    F.PosSemidef ↔ ∀ H : Matrix (Fin n) (Fin n) ℝ, H.PosSemidef → 0 ≤ venkovPairing F H := by
  constructor
  · exact fun hP H hH => venkovPairing_nonneg hP hH
  · intro h
    rw [posSemidef_iff]
    refine ⟨hF, fun a => ?_⟩
    rw [← venkovPairing_vecMulVec]
    apply h
    rw [posSemidef_iff]
    constructor
    · ext i j
      simp [Matrix.vecMulVec_apply, mul_comm]
    · intro x
      have : val (vecMulVec a a) x = (a ⬝ᵥ x) ^ 2 := by
        unfold val
        simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]; positivity

/-- **Perfect form (of minimum $1$)** (Voronoi; Cassels, Ch. 12, Notes, p. 281): a real symmetric $H$ such that
(i) $h(\vec{m}) \ge 1$ for every nonzero integral $\vec{m}$ ($\{h, m\} \ge 1$ for the squares $m = (\vec{m}\cdot\vec{x})^2$),
and (ii) the only real symmetric $F$ with $f(\vec{m}) = 1$ for all $\vec{m}$ in $M_1(h) = \{\vec{m} : h(\vec{m}) = 1\}$ is
$F = H$. Equivalently the hyperplane $\{f, \cdot\} = 1$ meets the convex hull of the squares in a face. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (perfect forms, Voronoi)"]
def IsPerfect (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.IsSymm ∧ (∀ m : Fin n → ℤ, m ≠ 0 → 1 ≤ val H (cast m)) ∧
    ∀ F : Matrix (Fin n) (Fin n) ℝ, F.IsSymm → (∀ m : Fin n → ℤ, val H (cast m) = 1 → val F (cast m) = 1) → F = H

/-- **Extreme form (of minimum $1$)** (Cassels, Ch. 12, Notes, p. 281; item 12.d2): a strictly positive definite $H$ with
(i) $\inf_{\vec{m} \ne 0} h(\vec{m}) = 1$ and (ii) $d(h) = \det H$ a local maximum among the forms satisfying (i): some
neighbourhood $U$ of $H$ in $M_n(\mathbb{R})$ has $\det G \le \det H$ for every strictly positive definite $G \in U$ whose
minimum over nonzero integral vectors is $1$. -/
@[kb "cassels1978" "Ch. 12, Notes, p. 281 (extreme forms)"]
def IsExtreme (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  H.PosDef ∧ IsGLB ((fun m : Fin n → ℤ => val H (cast m)) '' {m | m ≠ 0}) 1 ∧
    ∃ U ∈ nhds H, ∀ G ∈ U, G.PosDef → IsGLB ((fun m : Fin n → ℤ => val G (cast m)) '' {m | m ≠ 0}) 1 →
      G.det ≤ H.det

/-- **Reduction by the lexicographic order of the diagonal** (Cassels, Ch. 12, Notes, p. 282, the "Hermite-reduced" of
some writers of the Soviet school): a strictly positive definite $F$ such that
$(f_{00}, f_{11}, \dots, f_{n-1,n-1}) \le (f^*_{00}, \dots, f^*_{n-1,n-1})$ in the lexicographic order for every form $f^*$
integrally equivalent to $f$ (Mathlib's `Pi.Lex` order via `toLex`). Not Hermite's reduction of p. 259
(`IsHermiteReduced`). -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Hermite-reduced in the sense of the Soviet school)"]
def IsLexReduced (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  F.PosDef ∧ ∀ T : GL (Fin n) ℤ, toLex (fun i => F i i) ≤ toLex (fun i => act T.val F i i)

/-- **A lexicographically reduced form is Minkowski-reduced** (Cassels, Ch. 12, Notes, p. 282, "such a form is clearly
Minkowski-reduced"): for $\vec{e}^{\,*}$ extending $e_0, \dots, e_{j-1}$, the completed basis gives an equivalent form with the
same first $j$ diagonal entries and $j$-th entry $f(\vec{e}^{\,*})$. (The converse fails, as Cassels says; not
formalized.) -/
@[kb "cassels1978" "Ch. 12, Notes, p. 282 (Soviet Hermite reduction implies Minkowski reduction)"]
theorem IsLexReduced.isMinkowskiReduced {F : Matrix (Fin n) (Fin n) ℝ} (hF : IsLexReduced F) :
    IsMinkowskiReduced F := by
  obtain ⟨hpd, hmin⟩ := hF
  refine ⟨hpd, fun j e he => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨T, h1, h2⟩ := he
  have hcol : ∀ i, act T.val F i i = val F (fun k => (T.val k i : ℝ)) := by
    intro i
    rw [← val_single (act T.val F) i, val_act]
    congr 1
    ext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, castM]
  have hlow : ∀ i < j, act T.val F i i = F i i := by
    intro i hi
    rw [hcol, ← val_single F i]
    congr 1
    ext k
    simp [h1 i hi k, Pi.single_apply]
  have hj : act T.val F j j = val F (cast e) := by
    rw [hcol]
    congr 1
    ext k
    simp [h2 k]
  have hle := hmin T
  have hlt' : toLex (fun i => act T.val F i i) < toLex (fun i => F i i) := by
    refine ⟨j, fun i hi => hlow i hi, ?_⟩
    show act T.val F j j < F j j
    rw [hj]
    exact hlt
  exact absurd hle (not_le.2 hlt')

end QuadFormsKB.Reduction
