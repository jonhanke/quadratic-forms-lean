/-
# Kitaoka 1993, Section 6.7: Watson's theorem on decomposable lattices

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §6.7, Theorem 6.7.2 (Watson), p. 169, and
Lemmas 6.7.1–6.7.3, pp. 170–171 (printed pages).

A quadratic module $L$ is *decomposable* if $L = L_1 \perp L_2$ with $L_1, L_2 \ne 0$, and *indecomposable* otherwise
(p. 169). For lattices over $\mathbb Z$ this is `Lattices.IsDecomposable` / `Lattices.IsIndecomposable` (O'Meara §105,
`Literature/OMeara/Sec105.lean`), over the number field $F = \mathbb Q$. Theorem 6.7.1 (Eichler) is
`Lattices.indecomposable_splitting_unique` (O'Meara 105:1).

**Proves**
* `lemma672` (Lemma 6.7.2, unconditional): let $W \cong \langle 1\rangle^{\perp s} \perp \langle -1\rangle^{\perp t}$ be
  a regular real quadratic space with $s \ge t$ and $s + t \ge 11$, and $r \in \{2, 4, 6, 8\}$. Then $W$ has a subspace
  $W_0$ of dimension $r$ with $dW_0 = 1$ and Hasse invariant $S(W_0) = 1$. $W_0$ is given by an orthogonal basis
  $v_0, \dots, v_{r-1}$ (standard basis vectors of $W$) with $Q(v_k) = a_k$; $dW_0 = \prod_k a_k$ modulo squares and
  $S(W_0) = \prod_{k<l}(a_k, a_l)_{\mathbb R}$ (Kitaoka's Theorem 3.4.1; `hasseInvariant`). Kitaoka assumes $W$ isotropic
  ($t \ge 1$); the proof does not use it.

**States** (named propositions, not proved)
* `Lemma671`: a regular lattice $K$ over $\mathbb Z_p$ of rank $n$ splits as $K = K_1 \perp K_2$ with
  $dK_1 \in (\mathbb Q_p^\times)^2$ and $\operatorname{rank} K_1 = 2$ if $p \ne 2$, $n \ge 5$, and
  $\operatorname{rank} K_1 \in \{2, 4\}$ if $p = 2$, $n \ge 8$;
* `Lemma673`: a lattice $L$ on an indefinite regular quadratic space $V$ over $\mathbb Q$ with $\dim V \ge 12$ has a
  decomposable lattice in its genus;
* `Theorem672` (Watson): there is no indecomposable lattice on an indefinite regular quadratic space $V$ over
  $\mathbb Q$ with $\dim V \ge 12$.
Kitaoka's proofs need: for Lemma 6.7.1, the Jordan splitting of $\mathbb Z_p$-lattices into rank-one and binary
components and the square classes of $\mathbb Q_p^\times$; for Lemma 6.7.3, the existence of a rational space with
prescribed local spaces (his Theorem 4.4.2) and lattices with prescribed localizations; for Theorem 6.7.2, in addition,
the equality $\mathrm{spn}^+(L) = \mathrm{cls}^+(L)$ for indefinite $L$ of rank $\ge 3$ and the local modification of
a lattice inside its proper spinor genus. These are not combined here.
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Lattice
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Lattices.SpinorKernel
import QuadFormsKB.Literature.OMeara.Sec105
import QuadFormsKB.Literature.Kitaoka.Ch5Extension

open QuadraticMap NumberField

noncomputable section

namespace QuadFormsKB.Kitaoka.Watson

/-! ### Lemma 6.7.2 (real spaces) -/

/-- The signature vector $(1, \dots, 1, -1, \dots, -1)$ ($s$ entries $1$, then $t$ entries $-1$). -/
def sigVec (s t : ℕ) : Fin (s + t) → ℚ := Fin.append (fun _ => (1 : ℚ)) (fun _ => (-1 : ℚ))

/-- The real quadratic space $\langle 1\rangle^{\perp s} \perp \langle -1\rangle^{\perp t}$ on $\mathbb R^{s+t}$. -/
def sigForm (s t : ℕ) : QuadraticForm ℝ (Fin (s + t) → ℝ) :=
  weightedSumSquares ℝ (fun i => ((sigVec s t i : ℚ) : ℝ))

theorem sigForm_single (s t : ℕ) (i : Fin (s + t)) :
    sigForm s t (Pi.single i 1) = ((sigVec s t i : ℚ) : ℝ) := by
  classical
  simp [sigForm, weightedSumSquares_apply, Pi.single_apply]

theorem polar_sigForm_single (s t : ℕ) {i j : Fin (s + t)} (h : i ≠ j) :
    polar (sigForm s t) (Pi.single i 1) (Pi.single j 1) = 0 := by
  classical
  simp only [polar, sigForm, weightedSumSquares_apply, Pi.add_apply, Pi.single_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

theorem hilbertSymbol_real_eq' (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    hilbertSymbol ℝ x y = if x < 0 ∧ y < 0 then -1 else 1 := by
  have H := hilbertSymbol_real x y hx hy
  split_ifs with hc
  · exact H.mpr hc
  · have h01 : hilbertSymbol ℝ x y = 1 ∨ hilbertSymbol ℝ x y = -1 := by
      unfold hilbertSymbol; split_ifs <;> simp
    rcases h01 with h | h
    · exact h
    · exact absurd (H.mp h) hc

/-- The witness of Lemma 6.7.2: standard basis vectors $e_{f(k)}$ of $W$ for an injective $f$. -/
theorem witness (s t r : ℕ) (f : Fin r → Fin (s + t)) (hf : Function.Injective f) :
    let v : Fin r → Fin (s + t) → ℝ := fun k => Pi.single (f k) 1
    LinearIndependent ℝ v ∧ (∀ k, sigForm s t (v k) = ((sigVec s t (f k) : ℚ) : ℝ)) ∧
      (∀ k l, k ≠ l → polar (sigForm s t) (v k) (v l) = 0) := by
  refine ⟨?_, fun k => sigForm_single s t (f k), fun k l hkl => polar_sigForm_single s t (hf.ne hkl)⟩
  have := (Pi.basisFun ℝ (Fin (s + t))).linearIndependent.comp f hf
  convert this using 1
  funext k
  simp [Pi.basisFun_apply]

/-- **Kitaoka 1993, Lemma 6.7.2** (p. 171). Let $W \cong \langle 1\rangle^{\perp s} \perp \langle -1\rangle^{\perp t}$ be a
regular quadratic space over $\mathbb R$ with $\dim W = s + t \ge 11$ and $s \ge t$, and let $r \in \{2,4,6,8\}$. Then
there is a subspace $W_0 \subseteq W$ with $\dim W_0 = r$, $dW_0 = 1$ and Hasse invariant $S(W_0) = 1$.

*Encoding.* $W_0$ is the span of linearly independent, pairwise orthogonal vectors $v_0, \dots, v_{r-1}$ with
$Q(v_k) = a_k \ne 0$, so $W_0 \cong \langle a_0, \dots, a_{r-1}\rangle$, $dW_0 = \prod_k a_k$ modulo squares (here a
positive real, i.e. a square) and $S(W_0) = \prod_{k < l}(a_k, a_l)_{\mathbb R}$ (`hasseInvariant ℝ a`). Kitaoka also
assumes $W$ isotropic ($t \ge 1$). *Update:* isotropy is not needed.

*Proof* (Kitaoka's): $s \ge 6$; for $r \le 6$, or $r = 8 \le s$, take $W_0 = \langle 1\rangle^{\perp r}$; for $r = 8$
and $s \in \{6, 7\}$, $t \ge 4$ and $W_0 = \langle 1\rangle^{\perp 4} \perp \langle -1\rangle^{\perp 4}$, with
$S(W_0) = (-1,-1)_{\mathbb R}^6 = 1$. -/
@[kb "kitaoka1993" "§6.7, Lemma 6.7.2, p. 171"]
theorem lemma672 (s t r : ℕ) (hst : t ≤ s) (h11 : 11 ≤ s + t) (hr : r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 8) :
    ∃ (v : Fin r → Fin (s + t) → ℝ) (a : Fin r → ℚ),
      LinearIndependent ℝ v ∧ (∀ k, sigForm s t (v k) = a k) ∧
      (∀ k l, k ≠ l → polar (sigForm s t) (v k) (v l) = 0) ∧ (∀ k, a k ≠ 0) ∧
      0 < ∏ k, a k ∧ hasseInvariant ℝ a = 1 := by
  classical
  have hs6 : 6 ≤ s := by omega
  -- the case `W₀ = ⟨1⟩^r` with `r ≤ s`
  have hall : ∀ r, r ≤ s → ∃ (v : Fin r → Fin (s + t) → ℝ) (a : Fin r → ℚ),
      LinearIndependent ℝ v ∧ (∀ k, sigForm s t (v k) = a k) ∧
      (∀ k l, k ≠ l → polar (sigForm s t) (v k) (v l) = 0) ∧ (∀ k, a k ≠ 0) ∧
      0 < ∏ k, a k ∧ hasseInvariant ℝ a = 1 := by
    intro r hr
    let f : Fin r → Fin (s + t) := fun k => Fin.castAdd t (Fin.castLE hr k)
    have hf : Function.Injective f := fun k l h => by
      simpa [f, Fin.ext_iff] using h
    obtain ⟨h1, h2, h3⟩ := witness s t r f hf
    have ha : ∀ k, sigVec s t (f k) = 1 := fun k => by simp [f, sigVec]
    refine ⟨_, fun _ => 1, h1, fun k => by rw [h2 k, ha k], h3, fun _ => one_ne_zero, by simp, ?_⟩
    have hp' : hilbertSymbol ℝ 1 1 = 1 :=
      (hilbertSymbol_real_eq' 1 1 one_ne_zero one_ne_zero).trans (by norm_num)
    simp only [hasseInvariant, map_one, hp', ite_self, Finset.prod_const_one]
  rcases hr with rfl | rfl | rfl | rfl
  · exact hall 2 (by omega)
  · exact hall 4 (by omega)
  · exact hall 6 hs6
  · by_cases h8 : 8 ≤ s
    · exact hall 8 h8
    · -- `s ∈ {6, 7}`, so `t ≥ 4`: `W₀ = ⟨1⟩^4 ⊥ ⟨-1⟩^4`
      have ht4 : 4 ≤ t := by omega
      let f : Fin 8 → Fin (s + t) := fun k =>
        if h : k.val < 4 then Fin.castAdd t ⟨k.val, by omega⟩ else Fin.natAdd s ⟨k.val - 4, by omega⟩
      have hf : Function.Injective f := by
        intro k l h
        simp only [f] at h
        split_ifs at h with hk hl hl <;> simp [Fin.ext_iff] at h <;> ext <;> omega
      obtain ⟨h1, h2, h3⟩ := witness s t 8 f hf
      set a : Fin 8 → ℚ := fun k => if k.val < 4 then 1 else -1 with hadef
      have ha : ∀ k, sigVec s t (f k) = a k := by
        intro k
        by_cases hk : k.val < 4
        · have : f k = Fin.castAdd t ⟨k.val, by omega⟩ := dif_pos hk
          rw [this, sigVec, Fin.append_left, hadef]; simp [hk]
        · have : f k = Fin.natAdd s ⟨k.val - 4, by omega⟩ := dif_neg hk
          rw [this, sigVec, Fin.append_right, hadef]; simp [hk]
      refine ⟨_, a, h1, fun k => by rw [h2 k, ha k], h3, ?_, ?_, ?_⟩
      · intro k; simp only [hadef]; split_ifs <;> norm_num
      · simp only [hadef, Fin.prod_univ_succ, Fin.prod_univ_zero]; norm_num
      · have hm : hilbertSymbol ℝ (-1) (-1) = -1 :=
          (hilbertSymbol_real_eq' (-1) (-1) (by norm_num) (by norm_num)).trans (by norm_num)
        have hp : hilbertSymbol ℝ 1 (-1) = 1 :=
          (hilbertSymbol_real_eq' 1 (-1) (by norm_num) (by norm_num)).trans (by norm_num)
        have hp2 : hilbertSymbol ℝ (-1) 1 = 1 :=
          (hilbertSymbol_real_eq' (-1) 1 (by norm_num) (by norm_num)).trans (by norm_num)
        have hp' : hilbertSymbol ℝ 1 1 = 1 :=
          (hilbertSymbol_real_eq' 1 1 (by norm_num) (by norm_num)).trans (by norm_num)
        have hval : ∀ i j : Fin 8, hilbertSymbol ℝ (algebraMap ℚ ℝ (a i)) (algebraMap ℚ ℝ (a j)) =
            if 4 ≤ i.val ∧ 4 ≤ j.val then -1 else 1 := by
          intro i j
          simp only [hadef]
          by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4 <;>
            simp [hi, hj, hm, hp, hp2, hp', show ¬ (4 ≤ i.val) ↔ i.val < 4 from not_le]
        simp only [hasseInvariant, hval]
        decide

/-! ### Lemma 6.7.1, Lemma 6.7.3, Theorem 6.7.2 (stated) -/

/-- **A splitting $K = K_1 \perp K_2$ with $\operatorname{rank} K_1 = r$ and $dK_1 \in (\mathbb Q_p^\times)^2$** of a
$\mathbb Z_p$-lattice $K$ on $(\mathbb Q_p^n, Q)$ (Kitaoka 1993, Lemma 6.7.1): $K = K_1 \oplus K_2$ with
$B(K_1, K_2) = 0$, $K_1$ has a basis $b_0, \dots, b_{r-1}$ (linearly independent over $\mathbb Z_p$, spanning $K_1$),
and $\det(B(b_i, b_j))$ is a nonzero square in $\mathbb Q_p$ ($B$ = `Padic.pbil`, $B(x,x) = Q(x)$). -/
def HasSquareDiscSplitting {p : ℕ} [Fact p.Prime] {n : ℕ} (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (K : Submodule ℤ_[p] (Fin n → ℚ_[p])) (r : ℕ) : Prop :=
  ∃ (K₁ K₂ : Submodule ℤ_[p] (Fin n → ℚ_[p])) (b : Fin r → Fin n → ℚ_[p]),
    K₁ ⊔ K₂ = K ∧ Disjoint K₁ K₂ ∧ (∀ x ∈ K₁, ∀ y ∈ K₂, Padic.pbil Q x y = 0) ∧
    LinearIndependent ℤ_[p] b ∧ Submodule.span ℤ_[p] (Set.range b) = K₁ ∧
    (Matrix.of fun i j => Padic.pbil Q (b i) (b j)).det ≠ 0 ∧
    IsSquare (Matrix.of fun i j => Padic.pbil Q (b i) (b j)).det

/-- **Kitaoka 1993, Lemma 6.7.1** (p. 170), *stated*. Let $K$ be a regular quadratic lattice over $\mathbb Z_p$ with
$n = \operatorname{rank} K$. Then there is a splitting $K = K_1 \perp K_2$ with $dK_1 \in (\mathbb Q_p^\times)^2$ and
moreover $\operatorname{rank} K_1 = 2$ if $p \ne 2$ and $n \ge 5$, $\operatorname{rank} K_1 = 2$ or $4$ if $p = 2$ and
$n \ge 8$. ($K$ is a lattice on the regular space $(\mathbb Q_p^n, Q)$, so $\operatorname{rank} K = n$.) -/
@[kb "kitaoka1993" "§6.7, Lemma 6.7.1, p. 170"]
def Lemma671 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (Q : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]))
    (K : Submodule ℤ_[p] (Fin n → ℚ_[p])),
    (polarBilin Q).Nondegenerate → K.IsLattice ℚ_[p] →
    (p ≠ 2 → 5 ≤ n → HasSquareDiscSplitting Q K 2) ∧
    (p = 2 → 8 ≤ n → HasSquareDiscSplitting Q K 2 ∨ HasSquareDiscSplitting Q K 4)

open Lattices in
/-- **Kitaoka 1993, Lemma 6.7.3** (p. 171), *stated*. Let $L$ be a lattice on a regular quadratic space $V$ over
$\mathbb Q$ which is indefinite with $\dim V \ge 12$ (the space of Theorem 6.7.2). Then there is a decomposable lattice
$M \in \mathrm{gen}(L)$. ($V = (\mathbb Q^n, Q)$, `Lattices.IsIndefinite`, `Lattices.SameGenus`,
`Lattices.IsDecomposable`.) -/
@[kb "kitaoka1993" "§6.7, Lemma 6.7.3, p. 171"]
def Lemma673 : Prop :=
  ∀ (n : ℕ) (Q : QuadForm ℚ n), Q.Nondegenerate → IsIndefinite Q → 12 ≤ n →
    ∀ L : Lat ℚ n, ∃ M : Lat ℚ n, SameGenus Q L.1 M.1 ∧ IsDecomposable Q M.1

open Lattices in
/-- **Kitaoka 1993, Theorem 6.7.2** (Watson; p. 169), *stated*. Let $V$ be an indefinite quadratic space over
$\mathbb Q$. Then there is no indecomposable lattice on $V$ if $\dim V \ge 12$. ($V = (\mathbb Q^n, Q)$ regular,
`Lattices.IsIndefinite`; a lattice is `Lattices.Lat ℚ n`; indecomposable is `Lattices.IsIndecomposable`.) -/
@[kb "kitaoka1993" "§6.7, Thm. 6.7.2, p. 169"]
def Theorem672 : Prop :=
  ∀ (n : ℕ) (Q : QuadForm ℚ n), Q.Nondegenerate → IsIndefinite Q → 12 ≤ n →
    ∀ L : Lat ℚ n, ¬ IsIndecomposable Q L.1

end QuadFormsKB.Kitaoka.Watson
