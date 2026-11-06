/-
# Hanke 2011, §4: the sign-sum identity (Lemma 4.17) and the A/B decomposition (5)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

The algebraic heart of the structure theorem (Theorem 4.8): for a nonempty finite set $T$, indeterminates
$X_i, Y_i$ ($i \in T$) and an $N$-th root of unity $c$,
$$\sum_{\substack{(\varepsilon_i)_{i\in T} \in \mu_N^{T} \\ \prod_i \varepsilon_i = c}}\ \prod_{i\in T}(X_i + \varepsilon_i Y_i)
  = N^{|T|-1}\Bigl[\prod_{i\in T} X_i + c\prod_{i\in T} Y_i\Bigr]. \tag{14}$$

* `sum_prod_add_of_prod_eq`: the identity for an arbitrary finite abelian group $G$ in place of $\mu_N$, with a
  multiplicative map $\iota : G \to A$ into a commutative ring whose values sum to $0$ (proved by induction on $|T|$).
* `lemma_4_17`: Lemma 4.17 itself, for $\mu_N \subset \mathbb{C}$, $N \ge 2$, and $X_i, Y_i$ in any commutative
  $\mathbb{C}$-algebra (taking the algebra of polynomials gives the polynomial identity).
* `lemma_4_17_false_N_one`: *Update*: the lemma needs
  $N \ge 2$. For $N = 1$ the proof's step $\sum_{\varepsilon\in\mu_N}\varepsilon = 0$ fails, and so does the
  identity: with $|T| = 2$ and $X_i = Y_i = 1$ the left side is $4$ and the right side is $2$. The paper only uses
  $N = 2$ (`sum_sign_prod_eq`), where the lemma holds.
* `sum_sign_prod_eq`: the case $G = \{\pm 1\}$ used in the step (11)–(12) of the proof of Theorem 4.8.
* `massSum_eq_half`: formula (5) of Definition 4.6, $\widetilde M^{*,\varepsilon} = (A^* + \varepsilon B^*)/2$ for
  $A^* = \widetilde M^{*,+} + \widetilde M^{*,-}$ and $B^* = \widetilde M^{*,+} - \widetilde M^{*,-}$.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2011Structure

open Finset

section General

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] {A : Type*} [CommRing A]

omit [DecidableEq G] in
/-- Sum of `ι` over a finite group is unchanged by inversion. -/
private theorem sum_inv_eq (ι : G →* A) : ∑ g : G, ι g⁻¹ = ∑ g : G, ι g :=
  Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl

/-- The identity (14) for tuples indexed by `Fin (k + 1)`, by induction on `k`. -/
private theorem sum_prod_add_fin (ι : G →* A) (hι : ∑ g : G, ι g = 0) :
    ∀ (k : ℕ) (X Y : Fin (k + 1) → A) (c : G),
      ∑ ε : Fin (k + 1) → G, (if ∏ i, ε i = c then ∏ i, (X i + ι (ε i) * Y i) else 0) =
        (Fintype.card G : A) ^ k * (∏ i, X i + ι c * ∏ i, Y i) := by
  intro k
  induction k with
  | zero =>
    intro X Y c
    rw [← (Equiv.funUnique (Fin 1) G).symm.sum_comp]
    simp
  | succ k ih =>
    intro X Y c
    rw [← (Fin.consEquiv fun _ : Fin (k + 2) => G).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ (n := k + 1), Fin.cons_zero, Fin.cons_succ]
    have key : ∀ g : G, ∑ ε' : Fin (k + 1) → G,
        (if g * ∏ i, ε' i = c then (X 0 + ι g * Y 0) *
          ∏ i : Fin (k + 1), (X i.succ + ι (ε' i) * Y i.succ) else 0) =
        (X 0 + ι g * Y 0) * ((Fintype.card G : A) ^ k *
          (∏ i : Fin (k + 1), X i.succ + ι (g⁻¹ * c) * ∏ i : Fin (k + 1), Y i.succ)) := by
      intro g
      rw [← ih (fun i => X i.succ) (fun i => Y i.succ) (g⁻¹ * c), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ε' _ => ?_
      have : (g * ∏ i, ε' i = c) ↔ (∏ i, ε' i = g⁻¹ * c) := by
        constructor <;> intro h
        · rw [← h]; group
        · rw [h]; group
      by_cases h : ∏ i, ε' i = g⁻¹ * c
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (this.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
      · have h' : ¬ (g * ∏ i, ε' i = c) := fun h' => h (this.mp h')
        rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false h), mul_zero]
    rw [Finset.sum_congr rfl fun g _ => key g]
    set PX := ∏ i : Fin (k + 1), X i.succ
    set PY := ∏ i : Fin (k + 1), Y i.succ
    have expand : ∀ g : G, (X 0 + ι g * Y 0) * ((Fintype.card G : A) ^ k * (PX + ι (g⁻¹ * c) * PY)) =
        (Fintype.card G : A) ^ k * (X 0 * PX + ι c * (Y 0 * PY)) +
        (Fintype.card G : A) ^ k * (X 0 * ι c * PY) * ι g⁻¹ +
        (Fintype.card G : A) ^ k * (Y 0 * PX) * ι g := by
      intro g
      have h1 : ι g * ι g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [map_mul ι g⁻¹ c]
      linear_combination ((Fintype.card G : A) ^ k * Y 0 * PY * ι c) * h1
    rw [Finset.sum_congr rfl fun g _ => expand g, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_inv_eq, hι, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_zero, add_zero, ← Finset.mul_sum, hι, mul_zero, add_zero]
    ring

/-- **The sign-sum identity for an arbitrary finite abelian group.** Let $G$ be a finite abelian group,
$\iota : G \to A$ a multiplicative map into a commutative ring $A$ with $\sum_{g\in G}\iota(g) = 0$, $T$ a nonempty
finite set, $X, Y : T \to A$ and $c \in G$. Then
$$\sum_{\substack{\varepsilon : T \to G\\ \prod_i \varepsilon_i = c}} \prod_{i\in T}\bigl(X_i + \iota(\varepsilon_i)Y_i\bigr)
  = |G|^{|T|-1}\Bigl[\prod_{i} X_i + \iota(c)\prod_i Y_i\Bigr].$$
Lemma 4.17 is the case $G = \mu_N \subset \mathbb{C}$ (`lemma_4_17`). -/
theorem sum_prod_add_of_prod_eq (ι : G →* A) (hι : ∑ g : G, ι g = 0)
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T] (X Y : T → A) (c : G) :
    ∑ ε ∈ (univ : Finset (T → G)).filter (fun ε => ∏ i, ε i = c), ∏ i, (X i + ι (ε i) * Y i) =
      (Fintype.card G : A) ^ (Fintype.card T - 1) * (∏ i, X i + ι c * ∏ i, Y i) := by
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card T = k + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  let e : T ≃ Fin (k + 1) := Fintype.equivFinOfCardEq hk
  rw [Finset.sum_filter, hk, Nat.add_sub_cancel]
  have h := sum_prod_add_fin ι hι k (fun i => X (e.symm i)) (fun i => Y (e.symm i)) c
  rw [e.symm.prod_comp X, e.symm.prod_comp Y] at h
  rw [← h]
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl G)) _ _ fun ε => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [e.symm.prod_comp (fun i => ε i), e.symm.prod_comp (fun i => X i + ι (ε i) * Y i)]

end General

section RootsOfUnity

/-- The $N$-th roots of unity in $\mathbb{C}$ as a finite type (Mathlib provides `Finite`). -/
noncomputable scoped instance fintypeRootsOfUnity (N : ℕ) [NeZero N] : Fintype (rootsOfUnity N ℂ) :=
  Fintype.ofFinite _

/-- The sum of the $N$-th roots of unity in $\mathbb{C}$ is $0$ for $N \ge 2$. -/
theorem sum_rootsOfUnity_eq_zero {N : ℕ} [NeZero N] (hN : 2 ≤ N) {A : Type*} [CommRing A] [Algebra ℂ A] :
    ∑ g : rootsOfUnity N ℂ, algebraMap ℂ A ((g : ℂˣ) : ℂ) = 0 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hζ := Complex.isPrimitiveRoot_exp N hN0
  set ζ := hζ.toRootsOfUnity
  have hζ1 : ((ζ : ℂˣ) : ℂ) ≠ 1 := by
    rw [IsPrimitiveRoot.val_toRootsOfUnity_coe]
    exact hζ.ne_one (by omega)
  set S := ∑ g : rootsOfUnity N ℂ, ((g : ℂˣ) : ℂ)
  have hS : ((ζ : ℂˣ) : ℂ) * S = S := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft ζ) (fun g => ((ζ : ℂˣ) : ℂ) * ((g : ℂˣ) : ℂ))
      (fun g => ((g : ℂˣ) : ℂ)) fun g => by simp
  have : S = 0 := by
    have : (((ζ : ℂˣ) : ℂ) - 1) * S = 0 := by rw [sub_mul, hS, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hζ1)
  rw [← map_sum]
  change algebraMap ℂ A S = 0
  rw [this, map_zero]

/-- **Lemma 4.17** (Hanke). Let $T$ be a nonempty finite set, $X_i, Y_i$ ($i\in T$) elements of a commutative
$\mathbb{C}$-algebra $A$ (for indeterminates: $A$ a polynomial ring), $N \ge 2$, and $c \in \mu_N$ an $N$-th root of
unity in $\mathbb{C}$. Then
$$\sum_{\substack{(\varepsilon_i)_{i\in T} \in \mu_N^{T} \\ \prod_i \varepsilon_i = c}}\ \prod_{i\in T}(X_i + \varepsilon_i Y_i)
  = N^{|T|-1}\Bigl[\prod_{i\in T} X_i + c\prod_{i\in T} Y_i\Bigr].$$
*Update*: the hypothesis $N \ge 2$ is needed and missing from
the printed statement; for $N = 1$ the identity is false (`lemma_4_17_false_N_one`). Also, the printed condition
$\prod_{i\in T}\varepsilon_p = c$ should read $\prod_{i\in T}\varepsilon_i = c$, and in the last line of the proof
$a_T$ should read $a_U$ (typographical). -/
@[kb "hanke2011structure" "Lemma 4.17, p. 21"]
theorem lemma_4_17 {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T] {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    {A : Type*} [CommRing A] [Algebra ℂ A] (X Y : T → A) (c : rootsOfUnity N ℂ) :
    ∑ ε ∈ (univ : Finset (T → rootsOfUnity N ℂ)).filter (fun ε => ∏ i, ε i = c),
        ∏ i, (X i + algebraMap ℂ A ((ε i : ℂˣ) : ℂ) * Y i) =
      (N : A) ^ (Fintype.card T - 1) *
        (∏ i, X i + algebraMap ℂ A ((c : ℂˣ) : ℂ) * ∏ i, Y i) := by
  let ι : rootsOfUnity N ℂ →* A :=
    ((algebraMap ℂ A : ℂ →* A).comp (Units.coeHom ℂ)).comp (rootsOfUnity N ℂ).subtype
  have hcard : Fintype.card (rootsOfUnity N ℂ) = N := by
    rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]
  have h := sum_prod_add_of_prod_eq ι (sum_rootsOfUnity_eq_zero hN) X Y c
  rw [hcard] at h
  exact h

/-- **Lemma 4.17 needs $N \ge 2$** (proposed correction). For $N = 1$, $T = \{0, 1\}$ and $X_i = Y_i = 1$ in
$\mathbb{C}$, the left side of (14) is $(1+1)^2 = 4$ while the right side is $1^{1}\,(1 + 1) = 2$. -/
@[kb "hanke2011structure" "Lemma 4.17, p. 21 (fails for N = 1)"]
theorem lemma_4_17_false_N_one :
    ¬ ∀ (c : rootsOfUnity 1 ℂ),
      ∑ ε ∈ (univ : Finset (Fin 2 → rootsOfUnity 1 ℂ)).filter (fun ε => ∏ i, ε i = c),
          ∏ i : Fin 2, ((1 : ℂ) + ((ε i : ℂˣ) : ℂ) * 1) =
        ((1 : ℕ) : ℂ) ^ (Fintype.card (Fin 2) - 1) *
          (∏ _i : Fin 2, (1 : ℂ) + ((c : ℂˣ) : ℂ) * ∏ _i : Fin 2, (1 : ℂ)) := by
  intro h
  have hsub : ∀ x : rootsOfUnity 1 ℂ, x = 1 := fun x => by
    have := x.2; rw [mem_rootsOfUnity, pow_one] at this; exact Subtype.ext this
  have h1 := h 1
  have hf : (univ : Finset (Fin 2 → rootsOfUnity 1 ℂ)).filter (fun ε => ∏ i, ε i = 1) = univ :=
    Finset.filter_true_of_mem fun ε _ => hsub _
  have hu : (univ : Finset (Fin 2 → rootsOfUnity 1 ℂ)) = {fun _ => 1} := by
    ext ε; simp only [mem_univ, mem_singleton, true_iff]; funext i; exact hsub _
  rw [hf, hu, Finset.sum_singleton] at h1
  norm_num at h1

end RootsOfUnity

section Signs

/-- **The sign sum in the proof of Theorem 4.8, step (11)–(12).** For a nonempty finite set $T$ of primes, local
quantities $A_{\mathfrak p}, B_{\mathfrak p}$ in a field $K$ of characteristic $\ne 2$ (here: $\mathbb{R}$ or
$\mathbb{C}$), and a sign $C \in \{\pm1\}$,
$$\sum_{\substack{(\varepsilon_{\mathfrak p}) \in \{\pm1\}^{T}\\ \prod_{\mathfrak p}\varepsilon_{\mathfrak p} = C}}
  \prod_{\mathfrak p\in T}\frac{A_{\mathfrak p} + \varepsilon_{\mathfrak p}B_{\mathfrak p}}{2}
  = \frac{2^{|T|-1}}{2^{|T|}}\Bigl[\prod_{\mathfrak p\in T}A_{\mathfrak p} + C\prod_{\mathfrak p\in T}B_{\mathfrak p}\Bigr].$$
This is Lemma 4.17 with $N = 2$ (the signs $\{\pm1\} = \mathbb{Z}^\times$). -/
@[kb "hanke2011structure" "Thm. 4.8, proof, eqs. (11)-(12), p. 18"]
theorem sum_sign_prod_eq {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T] (a b : T → K) (C : ℤˣ) :
    ∑ ε ∈ (univ : Finset (T → ℤˣ)).filter (fun ε => ∏ i, ε i = C),
        ∏ i, (a i + ((ε i : ℤ) : K) * b i) / 2 =
      (2 : K) ^ (Fintype.card T - 1) / 2 ^ Fintype.card T *
        (∏ i, a i + ((C : ℤ) : K) * ∏ i, b i) := by
  let ι : ℤˣ →* K := (Int.castRingHom K : ℤ →* K).comp (Units.coeHom ℤ)
  have hι : ∑ g : ℤˣ, ι g = 0 := by
    rw [show (univ : Finset ℤˣ) = {1, -1} by decide, Finset.sum_pair (by decide)]
    simp [ι]
  have h := sum_prod_add_of_prod_eq ι hι a b C
  have hcard : Fintype.card ℤˣ = 2 := by decide
  rw [hcard] at h
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← Finset.sum_div]
  have hι' : ∀ g : ℤˣ, ι g = ((g : ℤ) : K) := fun _ => rfl
  simp only [hι'] at h
  rw [h]
  push_cast
  field_simp

end Signs

section AB

/-- **Formula (5) of Definition 4.6.** For the normalized local mass sums $\widetilde M^{*,\pm}$ (any values in a
field of characteristic $\ne 2$), with $A^* := \widetilde M^{*,+} + \widetilde M^{*,-}$ and
$B^* := \widetilde M^{*,+} - \widetilde M^{*,-}$, for each sign $\varepsilon \in \{\pm1\}$,
$$\widetilde M^{*,\varepsilon} = \frac{A^* + \varepsilon B^*}{2}.$$
Here `M true` is $\widetilde M^{*,+}$ and `M false` is $\widetilde M^{*,-}$. -/
@[kb "hanke2011structure" "Def. 4.6, eq. (5), p. 16"]
theorem massSum_eq_half {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (M : Bool → K) (ε : Bool) :
    M ε = ((M true + M false) + (if ε then 1 else -1) * (M true - M false)) / 2 := by
  cases ε <;> simp <;> field_simp <;> ring

end AB

end QuadFormsKB.Hanke2011Structure
