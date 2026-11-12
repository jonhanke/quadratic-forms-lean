/-
# Kitaoka 1993, Sections 6.5–6.6: representations by genera and proper spinor genera

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.5, p. 157 (Theorem 6.5.1, due to Kneser, Hsia and
Schulze-Pillot), §6.6, pp. 164–165 (Theorems 6.6.1, 6.6.2, Lemma 6.6.1). Printed page numbers.

**Setting.** Quadratic spaces $(F^n, Q)$ over a number field $F$ and $\mathcal O_F$-lattices in them, as in
`Literature/Kitaoka/Ch6Fundamentals.lean`; Kitaoka's results are over $F = \mathbb Q$ and are stated so here.
Kitaoka's bilinear form is $B(x, y) = \tfrac12(Q(x + y) - Q(x) - Q(y))$, so $B(x, x) = Q(x)$ (`kbil`).

**Defines**
* `RepByGenus QW QV K L`: $K$ is represented by $\mathrm{gen}(L)$, i.e. by some lattice of the genus of $L$
  (§6.5, p. 157);
* `RepByProperSpinorGenus QW QV K L`: $K$ is represented by $\mathrm{spn}^+(L)$ (§6.5, p. 157);
* `repProperSpinorGenera Q K L`: the proper spinor genera in $\mathrm{gen}(L)$ that represent $K$;
* `Theorem651`, `Theorem661`, `Theorem662`: the statements of Theorems 6.5.1, 6.6.1, 6.6.2 (stated).

**Proves**
* `lemma661` (Lemma 6.6.1, Dickson's lemma): every subset of $\mathbb N^k$ (componentwise order) has only finitely many
  minimal elements. *Proof:* the minimal elements form an antichain, and $\mathbb N^k$ is well quasi-ordered (Mathlib
  `Pi.wellQuasiOrderedLE`, `WellQuasiOrderedLE.finite_of_isAntichain`).
-/
import QuadFormsKB.Literature.Kitaoka.Ch6Fundamentals
import QuadFormsKB.Literature.OMeara.Sec102Spn

open NumberField IsDedekindDomain QuadFormsKB.Lattices

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka

section Defs

variable {F : Type} [Field F] [NumberField F] {m n : ℕ}

/-- **$K$ is represented by $\mathrm{gen}(L)$** (Kitaoka 1993, §6.5, p. 157): some lattice $M$ in the genus of $L$
represents $K$, $K \rightarrowtail M$ (`LatRep`). Here $K$ is an $\mathcal O_F$-module in $(F^m, Q_W)$ and $L$ a
lattice on $(F^n, Q_V)$. -/
@[kb "kitaoka1993" "§6.5, p. 157 (K is represented by gen(L))"]
def RepByGenus (QW : QuadForm F m) (QV : QuadForm F n) (K : Submodule (𝓞 F) (Fin m → F)) (L : Lat F n) :
    Prop :=
  ∃ M : Lat F n, SameGenus QV L.1 M.1 ∧ LatRep QW QV K M.1

/-- **$K$ is represented by $\mathrm{spn}^+(L)$** (Kitaoka 1993, §6.5, p. 157): some lattice $M$ in the proper spinor
genus of $L$ (`Lattices.SameProperSpinorGenus`) represents $K$, $K \rightarrowtail M$. -/
@[kb "kitaoka1993" "§6.5, p. 157 (K is represented by spn⁺(L))"]
def RepByProperSpinorGenus (QW : QuadForm F m) (QV : QuadForm F n) (K : Submodule (𝓞 F) (Fin m → F))
    (L : Lat F n) : Prop :=
  ∃ M : Lat F n, SameProperSpinorGenus QV L M ∧ LatRep QW QV K M.1

/-- **The proper spinor genera in $\mathrm{gen}(L)$ that represent $K$** (Kitaoka 1993, §6.5, p. 157): the classes
$c$ in `Lattices.genusProperSpinorGenera Q L` (the proper spinor genera contained in $\mathrm{gen}(L)$) containing a
lattice $M$ with $K \rightarrowtail M$. Here $K$ lies in the same space $(F^n, Q)$ as $L$. -/
@[kb "kitaoka1993" "§6.5, Thm. 6.5.1, p. 157 (the spn⁺ in gen(L) representing K)"]
def repProperSpinorGenera (Q : QuadForm F n) (K : Submodule (𝓞 F) (Fin n → F)) (L : Lat F n) :
    Set (Quotient (properSpnSetoid Q)) :=
  {c | c ∈ genusProperSpinorGenera Q L ∧ ∃ M : Lat F n, Quotient.mk _ M = c ∧ LatRep Q Q K M.1}

theorem repProperSpinorGenera_subset (Q : QuadForm F n) (K : Submodule (𝓞 F) (Fin n → F)) (L : Lat F n) :
    repProperSpinorGenera Q K L ⊆ genusProperSpinorGenera Q L := fun _ h => h.1

/-- **Kitaoka's bilinear form** $B(x, y) = \tfrac12\bigl(Q(x + y) - Q(x) - Q(y)\bigr)$ of $Q$ over an extension field
$K$ of $F$ (Kitaoka 1993, §1.1: $B(x, x) = Q(x)$). -/
def kbil (Q : QuadForm F n) (K : Type*) [Field K] [Algebra F K] (x y : Fin n → K) : K :=
  (Q.evalIn K (x + y) - Q.evalIn K x - Q.evalIn K y) / 2

end Defs

/-! ### Theorem 6.5.1 (Kneser, Hsia, Schulze-Pillot): representation in codimension 2 -/

/-- The completion of a number field at an infinite place has characteristic zero. -/
theorem charZero_completion {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) : CharZero w.Completion :=
  charZero_of_injective_algebraMap (algebraMap F _).injective

attribute [local instance] charZero_completion

/-- **The spinor norm condition at a place** (condition (ii) of Kitaoka's Theorem 6.5.1, one component): every
spinor norm $\theta(\varphi) \in K^\times/(K^\times)^2$ of an element $\varphi$ of the subgroup `G` of $O^+(V_K)$ lies
in $N_K = \{x \in K^\times \mid (x, -\delta)_K = 1\}$, where $(\cdot,\cdot)_K$ is the Hilbert symbol of the local field
$K$ (`hilbertSymbol`). Written with representatives: every $x \in K^\times$ whose square class is $\theta(\varphi)$
has $(x, -\delta)_K = 1$. -/
def SpinorNormsInNorms {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n) (K : Type*) [Field K]
    [Algebra F K] [CharZero K] (G : Set (orthGroup Q K)) (δ : F) : Prop :=
  ∀ φ ∈ G, ∀ x : K, x ≠ 0 → sqClassOf x = spinorNorm Q K φ → hilbertSymbol K x (-(algebraMap F K δ)) = 1

/-- **Kitaoka 1993, Theorem 6.5.1** (Kneser, Hsia, Schulze-Pillot; p. 157), *stated*. Let $V = W \perp U$ be a regular
quadratic space over $\mathbb Q$ with $\dim U = 2$, $L$ a lattice on $V$ and $K \subseteq L$ a lattice on $W$. Then $K$
is represented by either every $\mathrm{spn}^+$ or exactly half of the $\mathrm{spn}^+$ in $\mathrm{gen}(L)$, and the
latter case occurs if and only if
1. $-dU \notin (\mathbb Q^\times)^2$;
2. $\theta(O^+_{\mathbb A}(L)) \subseteq \tilde N := \prod_v N_v \cap \mathbb Q_{\mathbb A}^\times$, where
   $N_v = \{x \in \mathbb Q_v^\times \mid (x, -dU)_{\mathbb Q_v} = 1\}$;
3. $\theta(L_p; K_p) := \{\theta(\varphi) \mid \varphi \in O^+(V_p),\ K_p \subseteq \varphi(L_p)\} \subseteq N_p$ for
   every prime $p$.

*Encoding.* $V = (\mathbb Q^n, Q)$ with $Q$ nondegenerate; $U$ is given by a basis $u_0, u_1$: $B(u_i, K) = 0$, $K$ and
$u_0, u_1$ span $V$ over $\mathbb Q$, and $\delta = \det(B(u_i, u_j)) \ne 0$ (so $U = \mathbb Q u_0 + \mathbb Q u_1$ is
regular, $W = \mathbb QK = U^\perp$ and $dU = \delta$ modulo squares). Condition 2 is written place by place
(`SpinorNormsInNorms`): $O^+_{\mathbb A}(L)$ is the product of the stabilizers $O^+(L_p)$ and of $O^+(V_\infty)$, so
$\theta(O^+_{\mathbb A}(L)) \subseteq \tilde N$ means $\theta(O^+(L_p)) \subseteq N_p$ for every prime $p$ and
$\theta(O^+(V_\infty)) \subseteq N_\infty$. The proper spinor genera in $\mathrm{gen}(L)$ are
`Lattices.genusProperSpinorGenera Q L`, those representing $K$ are `repProperSpinorGenera Q K L`, and "exactly half"
is $2\,|\text{representing}| = |\text{all}|$ (both finite, O'Meara 102:8). -/
@[kb "kitaoka1993" "§6.5, Thm. 6.5.1, p. 157"]
def Theorem651 : Prop :=
  ∀ {n : ℕ} (Q : QuadForm ℚ n), Q.Nondegenerate →
  ∀ (L : Lat ℚ n) (K : Submodule (𝓞 ℚ) (Fin n → ℚ)) (u : Fin 2 → Fin n → ℚ),
    K ≤ L.1 →
    (∀ i, ∀ x ∈ K, kbil Q ℚ (u i) x = 0) →
    Submodule.span ℚ ((K : Set (Fin n → ℚ)) ∪ Set.range u) = ⊤ →
    let δ : ℚ := Matrix.det (Matrix.of fun i j => kbil Q ℚ (u i) (u j))
    δ ≠ 0 →
    let all := genusProperSpinorGenera Q L
    let rep := repProperSpinorGenera Q K L
    (rep = all ∨ 2 * rep.ncard = all.ncard) ∧
    (2 * rep.ncard = all.ncard ↔
      (¬ IsSquare (-δ) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ),
          SpinorNormsInNorms Q (v.adicCompletion ℚ)
            {φ | φ ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
              locAct v (φ : GL (Fin n) (v.adicCompletion ℚ)) (loc v L.1) = loc v L.1} δ) ∧
        (∀ w : InfinitePlace ℚ, SpinorNormsInNorms Q w.Completion {φ | φ ∈ Tamagawa.soSub Q w.Completion} δ) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ),
          SpinorNormsInNorms Q (v.adicCompletion ℚ)
            {φ | φ ∈ Tamagawa.soSub Q (v.adicCompletion ℚ) ∧
              loc v K ≤ locAct v (φ : GL (Fin n) (v.adicCompletion ℚ)) (loc v L.1)} δ)))

/-! ### Section 6.6: representation in codimension at least 3 -/

/-- **Kitaoka 1993, Theorem 6.6.1** (p. 164), *stated*: let $V = (\mathbb Q^m, Q_V)$ and $W = (\mathbb Q^n, Q_W)$ be
regular quadratic spaces over $\mathbb Q$ with $\dim V + 3 \le \dim W$, and $L$, $M$ lattices on $V$, $W$. If $L_p$ is
represented by $M_p$ for every prime $p$, $V_\infty$ is represented by $W_\infty$, and $W$ is indefinite
($W_\infty$ isotropic, `Lattices.IsIndefinite`), then $L$ is represented by $M$. Kitaoka's proof uses strong
approximation for the spinor kernel (his Theorem 6.2.2). -/
@[kb "kitaoka1993" "§6.6, Thm. 6.6.1, p. 164"]
def Theorem661 : Prop :=
  ∀ {m n : ℕ} (QV : QuadForm ℚ m) (QW : QuadForm ℚ n), QV.Nondegenerate → QW.Nondegenerate → m + 3 ≤ n →
  ∀ (L : Lat ℚ m) (M : Lat ℚ n),
    (∀ v : HeightOneSpectrum (𝓞 ℚ), LocLatRep v QV QW L.1 M.1) →
    (∀ w : InfinitePlace ℚ, SpaceRepAt w QV QW) →
    IsIndefinite QW →
    LatRep QV QW L.1 M.1

/-- **Kitaoka 1993, Theorem 6.6.2** (p. 165), *stated*: let $W = (\mathbb Q^n, Q_W)$ be a positive definite quadratic
space over $\mathbb Q$ and $N$ a lattice on it. Then there is a constant $c(N) > 0$ such that a lattice $M$ on a
positive definite quadratic space $V = (\mathbb Q^m, Q_V)$ over $\mathbb Q$ is represented by $N$ provided that
$\dim W \ge 2 \dim V + 3$, $\min(M) := \min\{Q(x) \mid x \in M,\ x \ne 0\} > c(N)$, and $M_p$ is represented by $N_p$
for every prime $p$. Positive definiteness is `Lattices.IsTotallyPosDef` (over $\mathbb Q$: $Q(x) > 0$ for $x \ne 0$);
$\min(M) > c$ is written as $Q_V(x) > c$ for every nonzero $x \in M$ (the minimum is attained). -/
@[kb "kitaoka1993" "§6.6, Thm. 6.6.2, p. 165"]
def Theorem662 : Prop :=
  ∀ {n : ℕ} (QW : QuadForm ℚ n), IsTotallyPosDef QW → ∀ N : Lat ℚ n,
    ∃ c : ℝ, 0 < c ∧
      ∀ {m : ℕ} (QV : QuadForm ℚ m), IsTotallyPosDef QV → ∀ M : Lat ℚ m,
        2 * m + 3 ≤ n →
        (∀ x ∈ M.1, x ≠ 0 → c < (QV.evalIn ℚ x : ℝ)) →
        (∀ v : HeightOneSpectrum (𝓞 ℚ), LocLatRep v QV QW M.1 N.1) →
        LatRep QV QW M.1 N.1

/-- **Kitaoka 1993, Lemma 6.6.1** (p. 165; Dickson's lemma): with the partial order on $\mathbb N^k$ given by
$(x_1, \dots, x_k) \le (y_1, \dots, y_k)$ iff $x_i \le y_i$ for all $i$, every subset $S \subseteq \mathbb N^k$ contains
only finitely many minimal elements. ($\mathbb N^k$ is `Fin k → ℕ` with the componentwise order; an element is minimal
in $S$ when it is `Minimal (· ∈ S)`.)

*Proof.* The minimal elements of $S$ are pairwise incomparable, and an antichain in the well quasi-order
$\mathbb N^k$ is finite (Mathlib `Pi.wellQuasiOrderedLE`, `WellQuasiOrderedLE.finite_of_isAntichain`). Kitaoka argues
by induction on $k$. -/
@[kb "kitaoka1993" "§6.6, Lemma 6.6.1, p. 165"]
theorem lemma661 (k : ℕ) (S : Set (Fin k → ℕ)) : {x | Minimal (· ∈ S) x}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro x hx y hy hxy hle
  exact hxy (le_antisymm hle (hy.2 hx.1 hle))

end QuadFormsKB.Kitaoka
