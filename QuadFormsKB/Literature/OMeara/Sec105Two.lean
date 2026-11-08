/-
# O'Meara §105: Example 105:2, the dyadic spots cannot be dropped from 105:1

**Layer:** $F = \mathbb Q$; $V = \mathbb Q^4$ with $Q = x_0^2 + x_1^2 + x_2^2 + x_3^2$ (`QuadForm.diag ![1, 1, 1, 1]`)
and the bilinear form `bil Q x y` $= x^{\mathsf T}H_Qy$ (twice O'Meara's $B$; the factor does not change orthogonality).
Spots of $\mathbb Q$: finite spots `HeightOneSpectrum (𝓞 ℚ)` and the infinite spot (`InfinitePlace ℚ`).

**Defines**
* `nonDyadicSpots`: O'Meara's set $S$ of all non-dyadic finite spots ($2 \notin \mathfrak p$).
* `zHalf`: the ring $\mathfrak o = \mathfrak o(S)$ of elements integral at every spot of $S$, i.e.
  $\mathbb Z[\tfrac12]$; Mathlib's $S$-integers `Set.integer`, which is indexed by the *exceptional* set, here
  $S^c$ = the dyadic spot.
* `latL`: the lattice $L = \mathfrak o e_0 \perp \dots \perp \mathfrak o e_3$, $e_i$ the standard basis (`Pi.single i 1`).
* `baseY`: O'Meara's four vectors $y_0 = \tfrac12(1,1,1,1)$, $y_1 = \tfrac12(1,-1,1,-1)$, $y_2 = \tfrac12(1,1,-1,-1)$,
  $y_3 = \tfrac12(1,-1,-1,1)$ (his $\tfrac12(x_1 \pm x_2 + x_3 \pm x_4)$ and $\tfrac12(x_1 \pm x_2 - x_3 \mp x_4)$).
* `baseTwo`: the base $e_0 + e_1, e_0 - e_1, e_2, e_3$.

**Proves** (O'Meara 1973, §105, 105:2, p. 323)
* `omeara105_2_definite`: $S$ is a definite set of spots for $V$: $V$ is anisotropic at the dyadic spot and at the
  infinite spot. Proof: an isotropic $\langle1,1,1,1\rangle$ over a field $K$ gives $(-1,-1)_K = 1$
  (`hilbert_neg_one_of_isotropic`, by Euler's two-square identity); $(-1,-1) = -1$ at the infinite spot, $= 1$ at the
  odd spots, so by Hilbert reciprocity $(-1,-1) = -1$ at the (unique) dyadic spot.
* `omeara105_2_base`: the $y_j$ are a base of $L$ with $Q(y_j) = 1$ and $B(y_i,y_j) = 0$ for $i \ne j$:
  $L \cong \langle1\rangle\perp\langle1\rangle\perp\langle1\rangle\perp\langle1\rangle$ in the base $y$.
* `omeara105_2_components_ne`: the component $\mathfrak o y_0$ is none of the components $\mathfrak o e_i$, so $L$ has
  two indecomposable splittings into rank-one lattices with different components: the uniqueness of Theorem 105:1
  (`indecomposable_splitting_unique`) fails when $S$ does not contain the dyadic spots.
* `omeara105_2_base_two`: $L \cong \langle2\rangle\perp\langle2\rangle\perp\langle1\rangle\perp\langle1\rangle$ in the
  base $e_0 + e_1, e_0 - e_1, e_2, e_3$ (O'Meara: "the reader may easily verify").

*Convention:* indices are 0-based; O'Meara's $x_1, \dots, x_4$ are $e_0, \dots, e_3$.
*Deviation:* the library's splitting predicates (`IsOrthSplitting`, `Sec105.lean`) are for $\mathcal O_F$-lattices;
here the lattice is over $\mathfrak o(S) = \mathbb Z[\tfrac12]$ and the splittings are given by explicit orthogonal
bases (rank-one lattices are indecomposable).
-/
import QuadFormsKB.Literature.OMeara.Sec105Example
import QuadFormsKB.Literature.LocalGlobal.NumberFieldMain
import QuadFormsKB.Tamagawa.SquareClassDuality

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- The form $x_0^2 + x_1^2 + x_2^2 + x_3^2$ over $\mathbb Q$. -/
abbrev sumFour : QuadForm ℚ 4 := QuadForm.diag ![1, 1, 1, 1]

/-! ### Anisotropy at the spots outside $S$ -/

/-- **An isotropic $\langle1,1,1,1\rangle$ forces $(-1,-1)_K = 1$** over a field $K \supseteq \mathbb Q$: from
$x_0^2 + x_1^2 + x_2^2 + x_3^2 = 0$ with $c = x_0^2 + x_1^2 \ne 0$, Euler's identity
$(x_0^2+x_1^2)(x_2^2+x_3^2) = (x_0x_2 - x_1x_3)^2 + (x_0x_3 + x_1x_2)^2$ writes $-1 = u^2 + v^2$; if $c = 0$, already
$x_0^2 + x_1^2 = 0$ or $x_2^2 + x_3^2 = 0$ non-trivially. -/
theorem hilbert_neg_one_of_isotropic {K : Type*} [Field K] [Algebra ℚ K] (h : sumFour.IsotropicIn K) :
    hilbertSymbol K (-1) (-1) = 1 := by
  obtain ⟨x, hx0, hx⟩ := h
  replace hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 0 := by
    simpa [QuadForm.evalIn_diag, Fin.sum_univ_four] using hx
  unfold hilbertSymbol
  rw [if_pos]
  by_cases hc : x 0 ^ 2 + x 1 ^ 2 = 0
  · by_cases h01 : x 0 = 0 ∧ x 1 = 0
    · refine ⟨x 2, x 3, 0, ?_, ?_⟩
      · intro h
        simp only [Prod.mk_eq_zero] at h
        apply hx0
        ext i; fin_cases i
        · exact h01.1
        · exact h01.2
        · exact h.1
        · exact h.2.1
      · rw [h01.1, h01.2] at hx; linear_combination hx
    · refine ⟨x 0, x 1, 0, ?_, ?_⟩
      · intro h
        simp only [Prod.mk_eq_zero] at h
        exact h01 ⟨h.1, h.2.1⟩
      · linear_combination hc
  · refine ⟨(x 0 * x 2 - x 1 * x 3) / (x 0 ^ 2 + x 1 ^ 2), (x 0 * x 3 + x 1 * x 2) / (x 0 ^ 2 + x 1 ^ 2), 1,
      by simp, ?_⟩
    field_simp
    linear_combination (x 0 ^ 2 + x 1 ^ 2) * hx

/-- $(-1,-1) = -1$ over the completion of $\mathbb Q$ at its infinite spot (which is real, so the completion is
$\mathbb R$): $z^2 = -x^2 - y^2$ has only the trivial solution. -/
theorem hilbert_neg_one_neg_one_infinite (w : InfinitePlace ℚ) : hilbertSymbol w.Completion (-1) (-1) = -1 := by
  unfold hilbertSymbol
  split_ifs with hex
  swap
  · rfl
  exfalso
  obtain ⟨x, y, z, hne, h⟩ := hex
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  have h' : φ x ^ 2 + φ y ^ 2 + φ z ^ 2 = 0 := by
    have := congrArg φ h
    simp only [map_pow, map_add, map_mul, map_neg, map_one] at this
    linarith
  have hx : φ x = 0 := by nlinarith [sq_nonneg (φ x), sq_nonneg (φ y), sq_nonneg (φ z)]
  have hy : φ y = 0 := by nlinarith [sq_nonneg (φ x), sq_nonneg (φ y), sq_nonneg (φ z)]
  have hz : φ z = 0 := by nlinarith [sq_nonneg (φ x), sq_nonneg (φ y), sq_nonneg (φ z)]
  apply hne
  simp only [Prod.mk_eq_zero]
  exact ⟨φ.injective (by rw [hx, map_zero]), φ.injective (by rw [hy, map_zero]),
    φ.injective (by rw [hz, map_zero])⟩

/-- $2$ is a prime of $\mathcal O_{\mathbb Q} \cong \mathbb Z$. -/
theorem prime_two_ratInt : Prime (2 : 𝓞 ℚ) := by
  have : Rat.ringOfIntegersEquiv (2 : 𝓞 ℚ) = 2 := map_ofNat _ 2
  rw [← MulEquiv.prime_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃* ℤ)]
  simpa [this] using Int.prime_two

/-- **$\mathbb Q$ has only one dyadic spot**: two finite spots containing $2$ are equal ($(2)$ is maximal). -/
theorem dyadic_unique {v v' : HeightOneSpectrum (𝓞 ℚ)} (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hv' : (2 : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have h0 : (2 : 𝓞 ℚ) ≠ 0 := prime_two_ratInt.ne_zero
  have hmax : (Ideal.span {(2 : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime h0).mpr prime_two_ratInt).isMaximal (by simpa using h0)
  have e1 := hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)
  have e2 := hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')
  exact HeightOneSpectrum.ext (e1.symm.trans e2)

/-- $(-1,-1) = -1$ at the dyadic spot of $\mathbb Q$, by Hilbert reciprocity: the places with $(-1,-1)_v = -1$ are
even in number, the infinite spot is one of them and no odd spot is (`SqDual.hilbert_units_nondyadic`). -/
theorem hilbert_neg_one_neg_one_dyadic {v : HeightOneSpectrum (𝓞 ℚ)} (hv : (2 : 𝓞 ℚ) ∈ v.asIdeal) :
    (NFPlace.finite v).hilbert (-1) (-1) = -1 := by
  have hm1 : v.valuation ℚ (-1 : ℚ) = 1 := by rw [Valuation.map_neg, map_one]
  by_contra hne
  · obtain ⟨-, heven⟩ := hilbert_reciprocity_nf (F := ℚ) (-1) (-1) (by norm_num) (by norm_num)
    have hset : {p : NFPlace ℚ | p.hilbert (-1) (-1) = -1} = {NFPlace.infinite Rat.infinitePlace} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      cases p with
      | infinite w =>
        rw [Subsingleton.elim w Rat.infinitePlace]
        simp only [NFPlace.hilbert, map_neg, map_one]
        exact iff_of_true (hilbert_neg_one_neg_one_infinite _) (by simp)
      | finite u =>
        refine ⟨fun hu => ?_, fun h' => by cases h'⟩
        by_cases h2 : (2 : 𝓞 ℚ) ∈ u.asIdeal
        · rw [dyadic_unique h2 hv] at hu; exact absurd hu hne
        · rw [SqDual.hilbert_units_nondyadic u h2 (-1) (-1)
            (by rw [Valuation.map_neg, map_one]) (by rw [Valuation.map_neg, map_one])] at hu
          norm_num at hu
    rw [hset, Set.ncard_singleton] at heven
    exact Nat.not_even_one heven

/-! ### O'Meara's ring $\mathfrak o(S)$ and the lattice $L$ -/

/-- **O'Meara's $S$ for Example 105:2:** the non-dyadic finite spots of $\mathbb Q$ ($2 \notin \mathfrak p$). -/
@[kb "omeara1963" "§105, 105:2, p. 323 (S = the non-dyadic spots of ℚ)"]
def nonDyadicSpots : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | (2 : 𝓞 ℚ) ∉ v.asIdeal}

/-- **Example 105:2, $S$ is definite for $V$** (O'Meara 1973, §105, p. 323): $V = \langle1,1,1,1\rangle$ is
anisotropic at every spot outside $S$, the dyadic spot and the infinite spot. -/
@[kb "omeara1963" "§105, 105:2, p. 323 (S is definite for V)"]
theorem omeara105_2_definite :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ nonDyadicSpots → ¬ sumFour.IsotropicIn (v.adicCompletion ℚ)) ∧
      ∀ w : InfinitePlace ℚ, ¬ sumFour.IsotropicIn w.Completion := by
  refine ⟨fun v hv hiso => ?_, fun w hiso => ?_⟩
  · have hv2 : (2 : 𝓞 ℚ) ∈ v.asIdeal := by simpa [nonDyadicSpots] using hv
    have h1 := hilbert_neg_one_of_isotropic hiso
    have h2 := hilbert_neg_one_neg_one_dyadic hv2
    simp only [NFPlace.hilbert, map_neg, map_one] at h2
    rw [h1] at h2; norm_num at h2
  · have h1 := hilbert_neg_one_of_isotropic hiso
    rw [hilbert_neg_one_neg_one_infinite] at h1; norm_num at h1

/-- **O'Meara's ring $\mathfrak o = \mathfrak o(S)$ for Example 105:2**: the $x \in \mathbb Q$ with $|x|_\mathfrak p
\le 1$ at every $\mathfrak p \in S$, i.e. $\mathbb Z[\tfrac12]$ (Mathlib's `Set.integer`, indexed by the exceptional
set $S^c$). -/
@[kb "omeara1963" "§105, 105:2, p. 323 (𝔬 = 𝔬(S), S the non-dyadic spots)"]
abbrev zHalf : Subalgebra (𝓞 ℚ) ℚ := (nonDyadicSpotsᶜ).integer ℚ

theorem half_mem_zHalf : (1 / 2 : ℚ) ∈ zHalf := by
  intro v hv
  have hv2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := by simpa [nonDyadicSpots] using hv
  have h2 : v.valuation ℚ (2 : ℚ) = 1 := by
    have := (HeightOneSpectrum.intValuation_eq_one_iff (v := v)).mpr hv2
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)] at this
    exact_mod_cast this
  rw [one_div, map_inv₀, h2, inv_one]

/-- The entries $0, \pm\tfrac12, \pm1$ lie in $\mathfrak o$. -/
theorem mem_zHalf_of {q : ℚ} (h : q = 0 ∨ q = 1 / 2 ∨ q = -(1 / 2) ∨ q = 1 ∨ q = -1) : q ∈ zHalf := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact zero_mem _
  · exact half_mem_zHalf
  · exact neg_mem half_mem_zHalf
  · exact one_mem _
  · exact neg_mem (one_mem _)

/-- The standard basis vector $e_i$ of $\mathbb Q^4$. -/
abbrev stdE (i : Fin 4) : Fin 4 → ℚ := Pi.single i 1

/-- **The lattice $L = \mathfrak o e_0 \perp \dots \perp \mathfrak o e_3$ of Example 105:2.** -/
@[kb "omeara1963" "§105, 105:2, p. 323 (L = 𝔬x₁ ⊥ ⋯ ⊥ 𝔬x₄)"]
def latL : Submodule zHalf (Fin 4 → ℚ) := Submodule.span zHalf (Set.range stdE)

theorem sum_smul_stdE (c : Fin 4 → zHalf) : ∑ i, c i • stdE i = fun k => (c k : ℚ) := by
  ext k
  fin_cases k <;> simp [Fin.sum_univ_four, Subalgebra.smul_def]

/-- A family $b$ with entries in $\mathfrak o$ such that every $e_i$ is an $\mathfrak o$-combination of the $b_j$ spans
$L$. -/
theorem span_eq_latL {b : Fin 4 → Fin 4 → ℚ} (hb : ∀ j k, b j k ∈ zHalf) (D : Fin 4 → Fin 4 → ℚ)
    (hD : ∀ i j, D i j ∈ zHalf) (hDb : ∀ i, ∑ j, D i j • b j = stdE i) :
    Submodule.span zHalf (Set.range b) = latL := by
  apply le_antisymm
  · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
    refine (Submodule.mem_span_range_iff_exists_fun zHalf).mpr ⟨fun k => ⟨b j k, hb j k⟩, ?_⟩
    rw [sum_smul_stdE]
  · refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i => ?_)
    refine (Submodule.mem_span_range_iff_exists_fun zHalf).mpr ⟨fun j => ⟨D i j, hD i j⟩, ?_⟩
    rw [← hDb i]
    rfl

/-- Linear independence over $\mathfrak o$ of four vectors of $\mathbb Q^4$ from linear independence over $\mathbb Q$. -/
theorem linearIndependent_zHalf {b : Fin 4 → Fin 4 → ℚ} (h : LinearIndependent ℚ b) : LinearIndependent zHalf b := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have := h (fun j => (g j : ℚ)) (by rw [← hg]; rfl) i
  exact Subtype.ext this

/-- $B(x, y) = 2\sum_k x_k y_k$ for the sum of four squares. -/
theorem bil_sumFour (x y : Fin 4 → ℚ) : bil sumFour x y = 2 * ∑ k, x k * y k := by
  simp only [bil, QuadForm.hessian, QuadForm.diag, dotProduct, Matrix.mulVec, Fin.sum_univ_four,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  simp
  ring

/-! ### The base $y$ -/

/-- **O'Meara's base $y_0, \dots, y_3$ of Example 105:2**: $\tfrac12(1,1,1,1)$, $\tfrac12(1,-1,1,-1)$,
$\tfrac12(1,1,-1,-1)$, $\tfrac12(1,-1,-1,1)$. -/
def baseY : Fin 4 → Fin 4 → ℚ :=
  ![![1 / 2, 1 / 2, 1 / 2, 1 / 2], ![1 / 2, -(1 / 2), 1 / 2, -(1 / 2)], ![1 / 2, 1 / 2, -(1 / 2), -(1 / 2)],
    ![1 / 2, -(1 / 2), -(1 / 2), 1 / 2]]

/-- **Example 105:2, the base $y$** (O'Meara 1973, §105, p. 323): $y_0, \dots, y_3$ is a base of $L$ (they span $L$
over $\mathfrak o$ and are linearly independent), with $Q(y_j) = 1$ and $B(y_i, y_j) = 0$ for $i \ne j$; so
$L \cong \langle1\rangle\perp\langle1\rangle\perp\langle1\rangle\perp\langle1\rangle$ in this base. -/
@[kb "omeara1963" "§105, 105:2, p. 323 (L ≅ ⟨1⟩⊥⟨1⟩⊥⟨1⟩⊥⟨1⟩ in the base y)"]
theorem omeara105_2_base :
    Submodule.span zHalf (Set.range baseY) = latL ∧ LinearIndependent zHalf baseY ∧
      (∀ j, sumFour.eval (baseY j) = 1) ∧ ∀ i j, i ≠ j → bil sumFour (baseY i) (baseY j) = 0 := by
  refine ⟨span_eq_latL (fun j k => mem_zHalf_of ?_) baseY (fun i j => mem_zHalf_of ?_) fun i => ?_, ?_, ?_, ?_⟩
  · fin_cases j <;> fin_cases k <;> simp [baseY]
  · fin_cases i <;> fin_cases j <;> simp [baseY]
  · ext k; fin_cases i <;> fin_cases k <;> simp [baseY, Fin.sum_univ_four] <;> norm_num
  · refine linearIndependent_zHalf (Fintype.linearIndependent_iff.mpr fun g hg i => ?_)
    have h0 := congrFun hg 0; have h1 := congrFun hg 1; have h2 := congrFun hg 2; have h3 := congrFun hg 3
    simp [Fin.sum_univ_four, baseY] at h0 h1 h2 h3
    fin_cases i <;> simp <;> linarith
  · intro j; fin_cases j <;> simp [QuadForm.evalIn_diag, Fin.sum_univ_four, baseY] <;> norm_num
  · intro i j hij
    rw [bil_sumFour]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, baseY] at hij ⊢ <;> norm_num

/-- **Example 105:2, two different splittings** (O'Meara 1973, §105, p. 323): $L = \mathfrak oe_0 \perp \dots \perp
\mathfrak oe_3 = \mathfrak oy_0 \perp \dots \perp \mathfrak oy_3$ (`omeara105_2_base`), and the component
$\mathfrak oy_0$ is none of the $\mathfrak oe_i$. So the indecomposable components of $L$ (rank one) are not unique:
Theorem 105:1 needs $S$ to contain the dyadic spots, although $S$ is definite for $V$ (`omeara105_2_definite`). -/
@[kb "omeara1963" "§105, 105:2, p. 323 (two different splittings: S must contain the dyadic spots)"]
theorem omeara105_2_components_ne (i : Fin 4) :
    Submodule.span zHalf {baseY 0} ≠ Submodule.span zHalf {stdE i} := by
  intro h
  have hy : baseY 0 ∈ Submodule.span zHalf {stdE i} := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨k, hk⟩ := exists_ne i
  have := congrFun ha k
  rw [Pi.smul_apply, stdE, Pi.single_eq_of_ne hk, smul_zero] at this
  fin_cases k <;> simp [baseY] at this

/-! ### The base $e_0 + e_1, e_0 - e_1, e_2, e_3$ -/

/-- The base $e_0 + e_1, e_0 - e_1, e_2, e_3$ of $L$. -/
def baseTwo : Fin 4 → Fin 4 → ℚ := ![![1, 1, 0, 0], ![1, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]

/-- **Example 105:2, a third splitting** (O'Meara 1973, §105, p. 323): $e_0 + e_1, e_0 - e_1, e_2, e_3$ is a base of
$L$ with values $2, 2, 1, 1$ and pairwise orthogonal, so
$L \cong \langle2\rangle\perp\langle2\rangle\perp\langle1\rangle\perp\langle1\rangle$. -/
@[kb "omeara1963" "§105, 105:2, p. 323 (L ≅ ⟨2⟩⊥⟨2⟩⊥⟨1⟩⊥⟨1⟩)"]
theorem omeara105_2_base_two :
    Submodule.span zHalf (Set.range baseTwo) = latL ∧ LinearIndependent zHalf baseTwo ∧
      sumFour.eval (baseTwo 0) = 2 ∧ sumFour.eval (baseTwo 1) = 2 ∧ sumFour.eval (baseTwo 2) = 1 ∧
      sumFour.eval (baseTwo 3) = 1 ∧ ∀ i j, i ≠ j → bil sumFour (baseTwo i) (baseTwo j) = 0 := by
  refine ⟨span_eq_latL (fun j k => mem_zHalf_of ?_)
    ![![1 / 2, 1 / 2, 0, 0], ![1 / 2, -(1 / 2), 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
    (fun i j => mem_zHalf_of ?_) fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases j <;> fin_cases k <;> simp [baseTwo]
  · fin_cases i <;> fin_cases j <;> simp
  · ext k; fin_cases i <;> fin_cases k <;> simp [baseTwo, Fin.sum_univ_four] <;> norm_num
  · refine linearIndependent_zHalf (Fintype.linearIndependent_iff.mpr fun g hg i => ?_)
    have h0 := congrFun hg 0; have h1 := congrFun hg 1; have h2 := congrFun hg 2; have h3 := congrFun hg 3
    simp [Fin.sum_univ_four, baseTwo] at h0 h1 h2 h3
    fin_cases i <;> simp <;> linarith
  all_goals try (simp [QuadForm.evalIn_diag, Fin.sum_univ_four, baseTwo] <;> norm_num; done)
  intro i j hij
  rw [bil_sumFour]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, baseTwo] at hij ⊢

end QuadFormsKB.Lattices
