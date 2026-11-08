/-
# Conway–Sloane, Ch. 15, §9.5: Theorem 18 at $p = 2$ with at most one even Jordan constituent

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`), Theorem 18, the "only if" direction at $p = 2$.

**Layer.** As in `Section9Theorem18DyadicTwoSided.lean`: over $\mathbb Q$ at the prime $v$ over $2$, a basis
$b_k = \gamma e_k$ of $L_2$ with Gram matrix $G$ = `locGram Q v γ` of $B$ ($G_{kk} = 2Q(b_k)$), and the Gram matrix
$N = G^{-1}$ of the dual basis. Indices are $0$-based.

**The shape** (`IsDiagBlock`, a **condition**): a set $B$ of indices (the *block*, possibly empty) such that every
$b_d$, $d \notin B$, is orthogonal to all other basis vectors, and the block is a scaled even unimodular lattice:
for a scalar $c \ne 0$ the entries $cG_{ij}$ and $cG_{ii}/2$ ($i, j \in B$) are integral, some $cG_{i_0j}$ is a unit,
the entries $N_{ij}$ ($i, j \in B$) satisfy $\lvert N_{ij}\rvert \le \lvert c\rvert$ (the dual block is scaled by
$c^{-1}$), and either $B$ has at most two elements or the block is `IsBlockEvenUnimodular`. In Conway–Sloane's
notation: $L_2 = \langle 2^{e_1}u_1, \dots, 2^{e_r}u_r\rangle \perp 2^sU$ with $U$ even unimodular (or no $U$), the
$1$-dimensional constituents at any scales, in any order; i.e. **every $2$-adic lattice whose Jordan decomposition
has at most one even (type II) constituent** (odd constituents have orthogonal bases).

**Proof** (`twoSidedChain_or_top_of_diagBlock`, a greedy construction). While some $b_d$, $d \notin B$, is not
peeled, let $k$ be such an index with $\lvert G_{kk}\rvert$ largest and $k'$ one with $\lvert G_{k'k'}\rvert$
smallest.
* If the block lies below $b_k$ ($\lvert G_{ii'}\rvert \le \lvert 2G_{kk}\rvert$ on $B$), peel $b_k$ from the bottom:
  alone, with a partner $b_j$ of the same norm order, or, if three unpeeled $b_d$ share that order, the root group is
  everything (`rootGroup_eq_top_of_three`).
* Otherwise, if the dual block lies below $b_{k'}^\#$ ($\lvert N_{ii'}\rvert \le \lvert 2N_{k'k'}\rvert$ on $B$),
  peel $b_{k'}$ from the top (a step in $N$; same trichotomy).
* Otherwise $\lvert cG_{kk}\rvert = 1$: $b_k$ lies at the scale of the block, and the root vectors of the block (of
  every unit norm times $c^{-1}$, `exists_rootVector_block`) together with $b_k$ give the root group everything.
When every $b_d$ is peeled, the remainder is the block, a base case of `PeelChainPair`.

**Proves** `rootGroup_eq_top_of_sum`, `rootGroup_eq_top_of_three`, `rootGroup_eq_top_of_block_single`, the
abstract greedy construction `twoSidedChain_or_top_greedy`, `twoSidedChain_or_top_of_diagBlock`,
**`theorem18OnlyIf_of_diagBlock`** and **`theorem18OnlyIf_of_diag`** (Theorem 18, "only if", at $p = 2$ for every
lattice whose $2$-adic completion has an orthogonal basis, any rank and any scales; unconditional).

**A second shape** (`IsDiagCore`, a **condition**): a *core* $B$ of any shape, with every $1$-dimensional
constituent outside its scale range (below the core, or above it in the dual). The same greedy construction never
gets stuck, so if the core is a terminal case of `PeelChainPair` (of $\gamma$ or of the dual basis), Theorem 18
("only if") holds (`twoSidedChain_or_top_of_diagCore`, **`theorem18OnlyIf_of_diagCore`**); e.g.
$\langle a\rangle \perp 4(E \perp \langle 2u\rangle) \perp 64\langle d\rangle$ for any binary even unimodular $E$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18DyadicTwoSided

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

section DiagBlock

variable {n : ℕ} {Q : QuadForm ℚ n} {L : Lat ℚ n} {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- **Two orthogonal basis vectors with $\lvert G_{aa} + G_{bb}\rvert = \lvert 2G_{aa}\rvert$ and every unit class
in the root group give the root group everything**: $x = b_a + b_b$ is a root vector of norm $(G_{aa} + G_{bb})/2$,
of the same absolute value as $G_{aa}$, so $Q(x)Q(b_a)$ has odd order. -/
theorem rootGroup_eq_top_of_sum (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v))
    (hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v) {a b : Fin n} (hab : a ≠ b)
    (ha : ∀ m, m ≠ a → locGram Q v γ m a = 0) (hb : ∀ m, m ≠ b → locGram Q v γ m b = 0)
    (hvab : Valued.v (locGram Q v γ b b) = Valued.v (locGram Q v γ a a))
    (hsum : Valued.v (locGram Q v γ a a + locGram Q v γ b b) = Valued.v (2 * locGram Q v γ a a)) :
    rootGroup Q L v = ⊤ := by
  set G := locGram Q v γ with hG
  have hGa : G a a ≠ 0 := locGram_diag_ne_zero hQ γ ha
  have hvGa : Valued.v (G a a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hGa
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  have hv20 : Valued.v (2 : Fv) ≠ 0 := by rw [hv2]; exact exp_ne_zero
  set c : Fin n → Fv := Pi.single a 1 + Pi.single b 1 with hc_def
  have hc : c ∈ std v := (std v).add_mem (single_mem_std a (by simp)) (single_mem_std b (by simp))
  have hca : c a = 1 := by simp [hc_def, hab]
  have hcb : c b = 1 := by simp [hc_def, hab.symm]
  have hcm : ∀ m, m ≠ a → m ≠ b → c m = 0 := fun m h1 h2' => by simp [hc_def, h1, h2']
  have hdiag : ∀ m, (G *ᵥ c) m = G m m * c m := fun m =>
    gram_mulVec_diag_of γ fun l hl hcl => by
      have : l = a ∨ l = b := by
        by_contra h
        push Not at h
        exact hcl (hcm l h.1 h.2)
      rcases this with rfl | rfl
      · exact ha m (Ne.symm hl)
      · exact hb m (Ne.symm hl)
  have hdot : c ⬝ᵥ (G *ᵥ c) = G a a + G b b := by
    rw [hc_def, add_dotProduct, single_dotProduct, single_dotProduct, ← hc_def, hdiag a, hdiag b, hca, hcb]
    ring
  have hQx : Q.evalIn Fv (γ.val *ᵥ c) = (G a a + G b b) / 2 := by
    have h2Q := two_mul_evalIn_locGram (Q := Q) (v := v) γ c
    rw [← hG, hdot] at h2Q
    rw [eq_div_iff two_ne_zero]
    linear_combination h2Q
  have hvQ : Valued.v (Q.evalIn Fv (γ.val *ᵥ c)) = Valued.v (G a a) := by
    rw [hQx, map_div₀, hsum, map_mul, mul_div_cancel_left₀ _ hv20]
  have hx0 : Q.evalIn Fv (γ.val *ᵥ c) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvQ; exact hvGa hvQ.symm
  have hroot : IsRootVector Q L v (γ.val *ᵥ c) := by
    refine ⟨hx0, symm_mem_of_gram L γ hγ hc hx0 fun m => ?_⟩
    rw [← hG, hdiag m, hvQ]
    by_cases hma : m = a
    · subst hma; rw [hca, mul_one]
    by_cases hmb : m = b
    · subst hmb; rw [hcb, mul_one, hvab]
    rw [hcm m hma hmb, mul_zero, map_zero]
    exact zero_le
  have hba := isRootVector_basis_of_orth γ hγ a ha hGa
  have hmem := sqClassOf_mul_mem_rootGroup hroot hba
  rw [evalIn_basis_eq] at hmem
  refine rootGroup_eq_top_of_units_of_odd h2 hunits (log (Valued.v (G a a))) ?_ hmem
  rw [map_mul, hvQ, map_div₀, hv2]
  conv_lhs => rw [← exp_log hvGa]
  rw [← exp_sub, ← exp_add]
  congr 1
  ring

/-- **Three orthogonal basis vectors with diagonal entries of the same absolute value give the root group
everything** (Conway–Sloane's $2^e\langle a, b, c\rangle$; Cassels' Lemma 3.8 (ii), first pattern, gives every unit
class; among $G_{ii}, G_{jj}, G_{kk}$ two have a sum of absolute value $\lvert 2G_{ii}\rvert$, which gives a class of
odd order, `rootGroup_eq_top_of_sum`). -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic root vectors of an odd Jordan constituent of rank at least 3)"]
theorem rootGroup_eq_top_of_three (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hQ : Q.Nondegenerate) (γ : GL (Fin n) Fv)
    (hγ : loc v L.1 = locAct v γ (std v)) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : ∀ m, m ≠ i → locGram Q v γ m i = 0) (hj : ∀ m, m ≠ j → locGram Q v γ m j = 0)
    (hk : ∀ m, m ≠ k → locGram Q v γ m k = 0)
    (hvj : Valued.v (locGram Q v γ j j) = Valued.v (locGram Q v γ i i))
    (hvk : Valued.v (locGram Q v γ k k) = Valued.v (locGram Q v γ i i)) : rootGroup Q L v = ⊤ := by
  set G := locGram Q v γ with hG
  have hGi : G i i ≠ 0 := locGram_diag_ne_zero hQ γ hi
  have hGj : G j j ≠ 0 := locGram_diag_ne_zero hQ γ hj
  have hvGi : Valued.v (G i i) ≠ 0 := (Valuation.ne_zero_iff _).mpr hGi
  have hq1 : Valued.v (G j j / G i i) = 1 := by rw [map_div₀, hvj, div_self hvGi]
  have hr1 : Valued.v (G k k / G i i) = 1 := by rw [map_div₀, hvk, div_self hvGi]
  have horth3 : ∀ l m, l ≠ m → (l = i ∨ l = j ∨ l = k) → G l m = 0 := by
    intro l m hlm hl
    rw [hG, locGram_symm' γ l m]
    rcases hl with rfl | rfl | rfl
    exacts [hi m (Ne.symm hlm), hj m (Ne.symm hlm), hk m (Ne.symm hlm)]
  have hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v :=
    units_le_rootGroup_of_ternary h2 γ hγ hij hik hjk horth3 hGi (p := 1) (q := toO v _ hq1.le)
      (r := toO v _ hr1.le)
      (Or.inl ⟨isUnit_one, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hq1,
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hr1⟩)
      (by simp [hG]) (by show G j j = G i i * (G j j / G i i); field_simp)
      (by show G k k = G i i * (G k k / G i i); field_simp)
  have hij' : Valued.v (G i i + G j j) ≤ Valued.v (2 * G i i) := valued_add_le_two_mul h2 hGi hvj.symm
  have hik' : Valued.v (G i i + G k k) ≤ Valued.v (2 * G i i) := valued_add_le_two_mul h2 hGi hvk.symm
  by_cases e1 : Valued.v (G i i + G j j) = Valued.v (2 * G i i)
  · exact rootGroup_eq_top_of_sum h2 hQ γ hγ hunits hij hi hj hvj e1
  by_cases e2 : Valued.v (G i i + G k k) = Valued.v (2 * G i i)
  · exact rootGroup_eq_top_of_sum h2 hQ γ hγ hunits hik hi hk hvk e2
  have l1 := lt_of_le_of_ne hij' e1
  have l2 := lt_of_le_of_ne hik' e2
  refine rootGroup_eq_top_of_sum h2 hQ γ hγ hunits hjk hj hk (hvk.trans hvj.symm) ?_
  have e : G j j + G k k = ((G i i + G j j) + (G i i + G k k)) + -(2 * G i i) := by ring
  have hv2j : Valued.v (2 * G j j) = Valued.v (2 * G i i) := by rw [map_mul, map_mul, hvj]
  rw [e, hv2j, Valuation.map_add_eq_of_lt_right _ (by rw [Valuation.map_neg]; exact Valuation.map_add_lt _ l1 l2),
    Valuation.map_neg]

/-- **A basis vector at the scale of an even block gives the root group everything**: if the $b_t$ ($t \in T$) are
orthogonal to all other basis vectors, $cG_{ij}$ and $cG_{ii}/2$ are integral off $T$ with some $cG_{i_0j}$ a unit,
and $b_k$ ($k \in T$) has $\lvert cG_{kk}\rvert = 1$, then the block's root vectors of norm $c^{-1}u$ (every unit
$u$, `exists_rootVector_block`) and $b_k$ (norm $G_{kk}/2$, of absolute value $\lvert c^{-1}\rvert/\lvert 2\rvert$)
give every unit class and a class of odd order. -/
theorem rootGroup_eq_top_of_block_single (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (hQ : Q.Nondegenerate)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) {T : Finset (Fin n)}
    (hT : ∀ t ∈ T, ∀ m, m ≠ t → locGram Q v γ m t = 0) {c : Fv} (hc : c ≠ 0)
    (hint : ∀ i j, i ∉ T → j ∉ T → Valued.v (c * locGram Q v γ i j) ≤ 1)
    (heven : ∀ i, i ∉ T → Valued.v (c * locGram Q v γ i i / 2) ≤ 1) (i0 j : Fin n) (hi0 : i0 ∉ T)
    (hjT : j ∉ T) (hj : Valued.v (c * locGram Q v γ i0 j) = 1) {k : Fin n} (hkT : k ∈ T)
    (hk : Valued.v (c * locGram Q v γ k k) = 1) : rootGroup Q L v = ⊤ := by
  have hunits : ∀ u : Fv, Valued.v u = 1 → sqClassOf u ∈ rootGroup Q L v :=
    units_of_unitRootsBlock h2 γ hγ ⟨T, c, i0, j, hT, hc, hint, heven, hi0, hjT, hj⟩
  obtain ⟨x, hxr, hx, -⟩ := exists_rootVector_block h2 γ hγ hT hc hint heven i0 j hi0 hjT hj (map_one Valued.v)
  have hGk : locGram Q v γ k k ≠ 0 := locGram_diag_ne_zero hQ γ (hT k hkT)
  have hbk := isRootVector_basis_of_orth γ hγ k (hT k hkT) hGk
  have hmem := sqClassOf_mul_mem_rootGroup hxr hbk
  rw [evalIn_basis_eq, hx] at hmem
  have hv2 : Valued.v (2 : Fv) = exp (-1 : ℤ) := valued_two_dyadic v h2
  have hvc : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  refine rootGroup_eq_top_of_units_of_odd h2 hunits (-log (Valued.v c)) ?_ hmem
  have hGv : Valued.v (locGram Q v γ k k) = (Valued.v c)⁻¹ := by
    rw [map_mul] at hk; exact eq_inv_of_mul_eq_one_right hk
  rw [map_mul, map_mul, map_inv₀, map_one, mul_one, map_div₀, hGv, hv2]
  conv_lhs => rw [← exp_log hvc]
  rw [← WithZero.exp_neg, ← exp_sub, ← exp_add]
  congr 1
  ring

variable (v) in
/-- **Diagonal plus one scaled even unimodular block** (a **condition** on the Gram matrix $G$ of a basis, the Gram
matrix $N$ of the dual basis, a set $B$ of indices and a scalar $c$): every $b_d$, $d \notin B$, is orthogonal to the
other basis vectors; $c \ne 0$; $cG_{ij}$ and $cG_{ii}/2$ are integral on $B$; $\lvert N_{ij}\rvert \le
\lvert c\rvert$ on $B$; if $B$ is nonempty some $cG_{i_0j}$ ($i_0, j \in B$) is a unit; and $B$ has at most two
elements or is a scaled even unimodular block (`IsBlockEvenUnimodular`). See the module docstring. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic Jordan forms with at most one even constituent)"]
def IsDiagBlock (G N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) (B : Finset (Fin n))
    (c : v.adicCompletion ℚ) : Prop :=
  (∀ d, d ∉ B → ∀ m, m ≠ d → G m d = 0) ∧ c ≠ 0 ∧
    (∀ i j, i ∈ B → j ∈ B → Valued.v (c * G i j) ≤ 1) ∧ (∀ i, i ∈ B → Valued.v (c * G i i / 2) ≤ 1) ∧
    (∀ i j, i ∈ B → j ∈ B → Valued.v (N i j) ≤ Valued.v c) ∧
    (B.Nonempty → ∃ i0 j, i0 ∈ B ∧ j ∈ B ∧ Valued.v (c * G i0 j) = 1) ∧
    (B.card ≤ 2 ∨ IsBlockEvenUnimodular G Bᶜ c)

/-- If every basis vector outside $B$ is orthogonal to the others, an off-diagonal entry $G_{ii'}$ with $i \notin B$
or $i' \notin B$ vanishes (for a symmetric $G$). -/
theorem off_eq_zero_of_orth {G : Matrix (Fin n) (Fin n) Fv} (hGs : ∀ a b, G a b = G b a) {B : Finset (Fin n)}
    (hD : ∀ d, d ∉ B → ∀ m, m ≠ d → G m d = 0) {i i' : Fin n} (hii : i ≠ i') (h : i ∉ B ∨ i' ∉ B) :
    G i i' = 0 := by
  rcases h with h | h
  · rw [hGs]; exact hD i h i' (Ne.symm hii)
  · exact hD i' h i hii

/-- **The greedy two-sided chain** (see the module docstring), abstractly: if the $b_d$, $d \notin B$, are orthogonal
to all other basis vectors, the block $B$ is a terminal case (`hterm`), and the root group is everything whenever a
largest diagonal entry $G_{kk}$ outside $B$ is not above the block and a smallest one $G_{k'k'}$ is not below the
dual block (`hneither`), then either the root group is everything or a two-sided peeling chain exists. -/
theorem twoSidedChain_or_top_greedy (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {B : Finset (Fin n)}
    (hD : ∀ d, d ∉ B → ∀ m, m ≠ d → locGram Q v γ m d = 0)
    (hterm : TwoSidedChain Q v γ N hN Bᶜ [])
    (hneither : ∀ k k', k ∉ B → k' ∉ B → Valued.v (locGram Q v γ k' k') ≤ Valued.v (locGram Q v γ k k) →
      (∃ b₁ b₂, b₁ ∈ B ∧ b₂ ∈ B ∧ Valued.v (2 * locGram Q v γ k k) < Valued.v (locGram Q v γ b₁ b₂)) →
      (∃ b₃ b₄, b₃ ∈ B ∧ b₄ ∈ B ∧ Valued.v (2 * N k' k') < Valued.v (N b₃ b₄)) → rootGroup Q L v = ⊤) :
    rootGroup Q L v = ⊤ ∨ ∃ ks, TwoSidedChain Q v γ N hN ∅ ks := by
  set G := locGram Q v γ with hG
  have hNG : N * G = 1 := mul_eq_one_comm.mp hN
  have hGs : ∀ a b, G a b = G b a := fun a b => locGram_symm' γ a b
  have hNs : ∀ a b, N a b = N b a := fun a b => by
    have := locGram_symm' (Q := Q) (v := v) (dualGam Q v γ N hN) a b
    rwa [locGram_dualGam] at this
  have hND : ∀ d, d ∉ B → ∀ m, m ≠ d → N m d = 0 := fun d hd => (col_orth_of_mul_eq_one hNG (hD d hd)).1
  have hNdd : ∀ d, d ∉ B → N d d = (G d d)⁻¹ := fun d hd =>
    eq_inv_of_mul_eq_one_left (col_orth_of_mul_eq_one hNG (hD d hd)).2
  have hGd0 : ∀ d, d ∉ B → Valued.v (G d d) ≠ 0 := fun d hd =>
    (Valuation.ne_zero_iff _).mpr (locGram_diag_ne_zero hQ γ (hD d hd))
  have hvN : ∀ d, d ∉ B → Valued.v (N d d) = (Valued.v (G d d))⁻¹ := fun d hd => by
    rw [hNdd d hd, map_inv₀]
  have hNle : ∀ a b, a ∉ B → b ∉ B → Valued.v (G b b) ≤ Valued.v (G a a) →
      Valued.v (N a a) ≤ Valued.v (N b b) := fun a b ha hb hle => by
    rw [hvN a ha, hvN b hb]; exact inv_anti₀ (zero_lt_iff.mpr (hGd0 b hb)) hle
  have hNeq : ∀ a b, a ∉ B → b ∉ B → (Valued.v (N a a) = Valued.v (N b b) ↔
      Valued.v (G a a) = Valued.v (G b b)) := fun a b ha hb => by
    rw [hvN a ha, hvN b hb]; exact ⟨fun h => inv_injective h, fun h => by rw [h]⟩
  suffices key : ∀ m (T : Finset (Fin n)), T ⊆ Bᶜ → (Bᶜ \ T).card = m →
      rootGroup Q L v = ⊤ ∨ ∃ ks, TwoSidedChain Q v γ N hN T ks from
    key _ ∅ (Finset.empty_subset _) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T hTB hm
  by_cases hS : (Bᶜ \ T).Nonempty
  swap
  · have hTeq : T = Bᶜ := by
      refine Finset.Subset.antisymm hTB fun x hx => ?_
      by_contra hxT
      exact hS ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxT⟩⟩
    subst hTeq
    exact Or.inr ⟨[], hterm⟩
  set S := Bᶜ \ T with hS_def
  have hmemS : ∀ i, i ∈ S ↔ i ∉ B ∧ i ∉ T := fun i => by simp [hS_def]
  have hIH : ∀ k, k ∈ S → rootGroup Q L v = ⊤ ∨ ∃ ks, TwoSidedChain Q v γ N hN (insert k T) ks := by
    intro k hk
    have hk' := (hmemS k).mp hk
    refine ih ((Bᶜ \ insert k T).card) ?_ (insert k T) ?_ rfl
    · rw [← hm]
      apply Finset.card_lt_card
      refine (Finset.ssubset_iff_of_subset fun x hx => ?_).mpr ⟨k, hk, by simp⟩
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or, Finset.mem_compl] at hx
      exact (hmemS x).mpr ⟨hx.1, hx.2.2⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simpa using hk'.1
      · exact hTB hx
  obtain ⟨k, hkS, hkmax⟩ := S.exists_max_image (fun i => Valued.v (G i i)) hS
  obtain ⟨k', hk'S, hk'min⟩ := S.exists_min_image (fun i => Valued.v (G i i)) hS
  obtain ⟨hkB, hkT⟩ := (hmemS k).mp hkS
  obtain ⟨hk'B, hk'T⟩ := (hmemS k').mp hk'S
  by_cases hbot : ∀ i i', i ∈ B → i' ∈ B → Valued.v (G i i') ≤ Valued.v (2 * G k k)
  · -- peel from the bottom
    have hrest : ∀ (U : Finset (Fin n)), (∀ i, i ∉ U → i ∉ B → i ∈ S ∧ i ≠ k) →
        (∀ i, i ∈ S → i ≠ k → i ∉ U → Valued.v (G i i) ≠ Valued.v (G k k)) →
        ∀ i i', i ∉ U → i' ∉ U → Valued.v (G i i') ≤ Valued.v (2 * G k k) := by
      intro U hU hne i i' hi hi'
      by_cases hii : i = i'
      · subst hii
        by_cases hiB : i ∈ B
        · exact hbot i i hiB hiB
        · obtain ⟨hiS, hik⟩ := hU i hi hiB
          exact valued_le_two_mul_of_lt h2 (lt_of_le_of_ne (hkmax i hiS) (hne i hiS hik hi))
      · by_cases hiB : i ∈ B
        · by_cases hi'B : i' ∈ B
          · exact hbot i i' hiB hi'B
          · rw [off_eq_zero_of_orth hGs hD hii (Or.inr hi'B), map_zero]; exact zero_le
        · rw [off_eq_zero_of_orth hGs hD hii (Or.inl hiB), map_zero]; exact zero_le
    by_cases hjx : ∃ j ∈ S, j ≠ k ∧ Valued.v (G j j) = Valued.v (G k k)
    · obtain ⟨j, hjS, hjk, hjv⟩ := hjx
      obtain ⟨hjB, hjT⟩ := (hmemS j).mp hjS
      by_cases hix : ∃ i ∈ S, i ≠ k ∧ i ≠ j ∧ Valued.v (G i i) = Valued.v (G k k)
      · obtain ⟨i, hiS, hik, hij, hiv⟩ := hix
        exact Or.inl (rootGroup_eq_top_of_three h2 hQ γ hγ (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij)
          (hD k hkB) (hD j hjB) (hD i ((hmemS i).mp hiS).1) hjv hiv)
      · rcases hIH k hkS with htop | ⟨ks, hks⟩
        · exact Or.inl htop
        refine Or.inr ⟨(k, some j, false) :: ks, ⟨hkT, hjT, hjk, hD k hkB, hD j hjB, hjv, ?_⟩, hks⟩
        refine hrest _ (fun i hi hiB => ?_) (fun i hiS hik hiU he => ?_)
        · simp only [Finset.mem_insert, not_or] at hi
          exact ⟨(hmemS i).mpr ⟨hiB, hi.2.2⟩, hi.1⟩
        · simp only [Finset.mem_insert, not_or] at hiU
          exact hix ⟨i, hiS, hik, hiU.2.1, he⟩
    · rcases hIH k hkS with htop | ⟨ks, hks⟩
      · exact Or.inl htop
      refine Or.inr ⟨(k, none, false) :: ks, ⟨hkT, hD k hkB, ?_⟩, hks⟩
      refine hrest _ (fun i hi hiB => ?_) (fun i hiS hik _ he => hjx ⟨i, hiS, hik, he⟩)
      simp only [Finset.mem_insert, not_or] at hi
      exact ⟨(hmemS i).mpr ⟨hiB, hi.2⟩, hi.1⟩
  by_cases htop : ∀ i i', i ∈ B → i' ∈ B → Valued.v (N i i') ≤ Valued.v (2 * N k' k')
  · -- peel from the top (a step in the dual Gram matrix)
    have hNmax : ∀ i, i ∈ S → Valued.v (N i i) ≤ Valued.v (N k' k') := fun i hi =>
      hNle i k' ((hmemS i).mp hi).1 hk'B (hk'min i hi)
    have hrest : ∀ (U : Finset (Fin n)), (∀ i, i ∉ U → i ∉ B → i ∈ S ∧ i ≠ k') →
        (∀ i, i ∈ S → i ≠ k' → i ∉ U → Valued.v (N i i) ≠ Valued.v (N k' k')) →
        ∀ i i', i ∉ U → i' ∉ U → Valued.v (N i i') ≤ Valued.v (2 * N k' k') := by
      intro U hU hne i i' hi hi'
      by_cases hii : i = i'
      · subst hii
        by_cases hiB : i ∈ B
        · exact htop i i hiB hiB
        · obtain ⟨hiS, hik⟩ := hU i hi hiB
          exact valued_le_two_mul_of_lt h2 (lt_of_le_of_ne (hNmax i hiS) (hne i hiS hik hi))
      · by_cases hiB : i ∈ B
        · by_cases hi'B : i' ∈ B
          · exact htop i i' hiB hi'B
          · rw [off_eq_zero_of_orth hNs hND hii (Or.inr hi'B), map_zero]; exact zero_le
        · rw [off_eq_zero_of_orth hNs hND hii (Or.inl hiB), map_zero]; exact zero_le
    by_cases hjx : ∃ j ∈ S, j ≠ k' ∧ Valued.v (G j j) = Valued.v (G k' k')
    · obtain ⟨j, hjS, hjk, hjv⟩ := hjx
      obtain ⟨hjB, hjT⟩ := (hmemS j).mp hjS
      by_cases hix : ∃ i ∈ S, i ≠ k' ∧ i ≠ j ∧ Valued.v (G i i) = Valued.v (G k' k')
      · obtain ⟨i, hiS, hik, hij, hiv⟩ := hix
        exact Or.inl (rootGroup_eq_top_of_three h2 hQ γ hγ (Ne.symm hjk) (Ne.symm hik) (Ne.symm hij)
          (hD k' hk'B) (hD j hjB) (hD i ((hmemS i).mp hiS).1) hjv hiv)
      · rcases hIH k' hk'S with htop' | ⟨ks, hks⟩
        · exact Or.inl htop'
        refine Or.inr ⟨(k', some j, true) :: ks, ⟨hk'T, hjT, hjk, hND k' hk'B, hND j hjB,
          (hNeq j k' hjB hk'B).mpr hjv, ?_⟩, hks⟩
        refine hrest _ (fun i hi hiB => ?_) (fun i hiS hik hiU he => ?_)
        · simp only [Finset.mem_insert, not_or] at hi
          exact ⟨(hmemS i).mpr ⟨hiB, hi.2.2⟩, hi.1⟩
        · simp only [Finset.mem_insert, not_or] at hiU
          exact hix ⟨i, hiS, hik, hiU.2.1, (hNeq i k' ((hmemS i).mp hiS).1 hk'B).mp he⟩
    · rcases hIH k' hk'S with htop' | ⟨ks, hks⟩
      · exact Or.inl htop'
      refine Or.inr ⟨(k', none, true) :: ks, ⟨hk'T, hND k' hk'B, ?_⟩, hks⟩
      refine hrest _ (fun i hi hiB => ?_) (fun i hiS hik _ he =>
        hjx ⟨i, hiS, hik, (hNeq i k' ((hmemS i).mp hiS).1 hk'B).mp he⟩)
      simp only [Finset.mem_insert, not_or] at hi
      exact ⟨(hmemS i).mpr ⟨hiB, hi.2⟩, hi.1⟩
  left
  push Not at hbot htop
  obtain ⟨b₁, b₂, hb₁, hb₂, hlt₁⟩ := hbot
  obtain ⟨b₃, b₄, hb₃, hb₄, hlt₂⟩ := htop
  exact hneither k k' hkB hk'B (hk'min k hkS) ⟨b₁, b₂, hb₁, hb₂, hlt₁⟩ ⟨b₃, b₄, hb₃, hb₄, hlt₂⟩


/-- **The greedy two-sided chain for `IsDiagBlock`** (see the module docstring): either the root group is everything
or a two-sided peeling chain exists. -/
theorem twoSidedChain_or_top_of_diagBlock (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {B : Finset (Fin n)} {c : Fv}
    (h : IsDiagBlock v (locGram Q v γ) N B c) :
    rootGroup Q L v = ⊤ ∨ ∃ ks, TwoSidedChain Q v γ N hN ∅ ks := by
  obtain ⟨hD, hc, hBint, hBeven, hBdual, hBunit, hBterm⟩ := h
  refine twoSidedChain_or_top_greedy hQ h2 γ hγ N hN hD (Or.inl ⟨[], ?_⟩) ?_
  · have hc' : Finset.univ \ Bᶜ = B := by ext x; simp
    show (Finset.univ \ Bᶜ).card ≤ 2 ∨ _
    rcases hBterm with hB2 | hBu
    · exact Or.inl (by rw [hc']; exact hB2)
    · exact Or.inr (Or.inl ⟨c, hBu⟩)
  intro k k' hkB hk'B hle ⟨b₁, b₂, hb₁, hb₂, hlt₁⟩ ⟨b₃, b₄, hb₃, hb₄, hlt₂⟩
  set G := locGram Q v γ with hG
  have hNG : N * G = 1 := mul_eq_one_comm.mp hN
  have hGd0 : ∀ d, d ∉ B → Valued.v (G d d) ≠ 0 := fun d hd =>
    (Valuation.ne_zero_iff _).mpr (locGram_diag_ne_zero hQ γ (hD d hd))
  have hvN : ∀ d, d ∉ B → Valued.v (N d d) = (Valued.v (G d d))⁻¹ := fun d hd => by
    rw [eq_inv_of_mul_eq_one_left (col_orth_of_mul_eq_one hNG (hD d hd)).2, map_inv₀]
  have hv20 : 0 < Valued.v (2 : Fv) := zero_lt_iff.mpr (by rw [valued_two_dyadic v h2]; exact exp_ne_zero)
  have hvc0 : 0 < Valued.v c := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc)
  -- $\lvert 2cG_{kk}\rvert < \lvert cG_{b_1b_2}\rvert \le 1$, so $\lvert cG_{kk}\rvert \le 1$
  have hA : Valued.v (c * G k k) ≤ 1 := by
    have h1 : Valued.v (c * (2 * G k k)) < Valued.v (1 : Fv) := by
      rw [map_one, map_mul]
      calc Valued.v c * Valued.v (2 * G k k) < Valued.v c * Valued.v (G b₁ b₂) :=
            mul_lt_mul_of_pos_left hlt₁ hvc0
        _ = Valued.v (c * G b₁ b₂) := (map_mul _ _ _).symm
        _ ≤ 1 := hBint b₁ b₂ hb₁ hb₂
    have h3 := valued_le_two_mul_of_lt h2 h1
    rw [show c * (2 * G k k) = 2 * (c * G k k) by ring, mul_one, map_mul] at h3
    exact le_of_mul_le_mul_left (by rwa [mul_one]) hv20
  -- $\lvert 2N_{k'k'}\rvert < \lvert N_{b_3b_4}\rvert \le \lvert c\rvert$, so $\lvert cG_{k'k'}\rvert \ge 1$
  have hB : 1 ≤ Valued.v (c * G k' k') := by
    have hGk'0 := hGd0 k' hk'B
    have h1 : Valued.v (2 * N k' k') < Valued.v c := lt_of_lt_of_le hlt₂ (hBdual b₃ b₄ hb₃ hb₄)
    have h3 := valued_le_two_mul_of_lt h2 h1
    rw [map_mul, map_mul, hvN k' hk'B] at h3
    have h4 : (Valued.v (G k' k'))⁻¹ ≤ Valued.v c := le_of_mul_le_mul_left h3 hv20
    rw [map_mul]
    calc (1 : ℤᵐ⁰) = (Valued.v (G k' k'))⁻¹ * Valued.v (G k' k') := (inv_mul_cancel₀ hGk'0).symm
      _ ≤ Valued.v c * Valued.v (G k' k') := by gcongr
  have hC : Valued.v (c * G k' k') ≤ Valued.v (c * G k k) := by
    have := hle
    rw [map_mul, map_mul]; gcongr
  have hk1 : Valued.v (c * G k k) = 1 := le_antisymm hA (hB.trans hC)
  obtain ⟨i0, j, hi0, hj, hu⟩ := hBunit ⟨b₁, hb₁⟩
  exact rootGroup_eq_top_of_block_single h2 hQ γ hγ (T := Bᶜ)
    (fun t ht m hm => hD t (by simpa using ht) m hm) hc
    (fun i j hi hj => hBint i j (by simpa using hi) (by simpa using hj))
    (fun i hi => hBeven i (by simpa using hi)) i0 j (by simpa using hi0) (by simpa using hj) hu
    (by simpa using hkB) hk1

/-- **Theorem 18, "only if", at $p = 2$ for diagonal-plus-block bases** (Conway–Sloane §9.5, p. 391; unconditional):
if $L_2$ has a basis $\gamma$ satisfying `IsDiagBlock` (every $2$-adic lattice with at most one even Jordan
constituent, written in a Jordan basis), Theorem 18 ("only if") holds for $L$ at $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': 2-adic Jordan forms with at most one even constituent)"]
theorem theorem18OnlyIf_of_diagBlock (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {B : Finset (Fin n)} {c : Fv} (h : IsDiagBlock v (locGram Q v γ) N B c) :
    Theorem18OnlyIf Q L v hQ := by
  rcases twoSidedChain_or_top_of_diagBlock hQ h2 γ hγ N hN h with htop | ⟨ks, hks⟩
  · exact theorem18OnlyIf_of_eq_top hQ htop
  · exact theorem18OnlyIf_of_twoSidedChain hQ h2 γ hγ N hN ks hks

/-- **Theorem 18, "only if", at $p = 2$ for every lattice whose $2$-adic completion has an orthogonal basis**
(Conway–Sloane §9.5, p. 391; any rank, any scales; unconditional): if the Gram matrix of a basis of $L_2$ is
diagonal, every element of $\theta(O^+(L_2))$ is, up to squares, the product of the norms of an even number of
$2$-adic root vectors. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': 2-adic lattices with an orthogonal basis)"]
theorem theorem18OnlyIf_of_diag (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v))
    (hdiag : ∀ i j, i ≠ j → locGram Q v γ i j = 0) : Theorem18OnlyIf Q L v hQ := by
  have hdet : IsUnit (locGram Q v γ).det := isUnit_iff_ne_zero.mpr (locGram_det_ne_zero hQ γ)
  refine theorem18OnlyIf_of_diagBlock hQ h2 γ hγ (locGram Q v γ)⁻¹ (Matrix.mul_nonsing_inv _ hdet)
    (B := ∅) (c := 1) ⟨fun d _ m hm => hdiag m d hm, one_ne_zero, by simp, by simp, by simp, by simp,
      Or.inl (by simp)⟩

variable (v) in
/-- **A diagonal part outside the scale range of a core** (a **condition** on the Gram matrix $G$ of a basis, the
Gram matrix $N$ of the dual basis and a set $B$ of indices, the *core*): every $b_d$, $d \notin B$, is orthogonal to
the other basis vectors, and lies either below the core ($\lvert G_{ii'}\rvert \le \lvert 2G_{dd}\rvert$ for
$i, i' \in B$) or above it in the dual ($\lvert N_{ii'}\rvert \le \lvert 2N_{dd}\rvert$ for $i, i' \in B$). In
Conway–Sloane's notation: $L_2 = \langle 2^{e_1}u_1, \dots\rangle \perp M \perp \langle 2^{f_1}w_1, \dots\rangle$
with the first $1$-dimensional constituents at scales below the scale of $M$ and the others above the scale of
$M^\#$'s dual. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, p. 391 (2-adic Jordan forms: a core with 1-dimensional constituents outside its scale range)"]
def IsDiagCore (G N : Matrix (Fin n) (Fin n) (v.adicCompletion ℚ)) (B : Finset (Fin n)) : Prop :=
  (∀ d, d ∉ B → ∀ m, m ≠ d → G m d = 0) ∧
    ∀ d, d ∉ B → (∀ i i', i ∈ B → i' ∈ B → Valued.v (G i i') ≤ Valued.v (2 * G d d)) ∨
      (∀ i i', i ∈ B → i' ∈ B → Valued.v (N i i') ≤ Valued.v (2 * N d d))

/-- **The greedy two-sided chain for `IsDiagCore`**: if the core is a terminal case (a peeling chain with partners
of $\gamma$ or of the dual basis, starting with the $1$-dimensional constituents peeled), either the root group is
everything or a two-sided peeling chain exists. -/
theorem twoSidedChain_or_top_of_diagCore (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {B : Finset (Fin n)} (h : IsDiagCore v (locGram Q v γ) N B)
    (hterm : TwoSidedChain Q v γ N hN Bᶜ []) :
    rootGroup Q L v = ⊤ ∨ ∃ ks, TwoSidedChain Q v γ N hN ∅ ks := by
  obtain ⟨hD, hside⟩ := h
  refine twoSidedChain_or_top_greedy hQ h2 γ hγ N hN hD hterm ?_
  intro k k' hkB hk'B hle ⟨b₁, b₂, hb₁, hb₂, hlt₁⟩ ⟨b₃, b₄, hb₃, hb₄, hlt₂⟩
  exfalso
  rcases hside k hkB with hk | hk
  · exact (not_le.mpr hlt₁) (hk b₁ b₂ hb₁ hb₂)
  · have hNG : N * locGram Q v γ = 1 := mul_eq_one_comm.mp hN
    have hvN : ∀ d, d ∉ B → Valued.v (N d d) = (Valued.v (locGram Q v γ d d))⁻¹ := fun d hd => by
      rw [eq_inv_of_mul_eq_one_left (col_orth_of_mul_eq_one hNG (hD d hd)).2, map_inv₀]
    have hG0 : Valued.v (locGram Q v γ k' k') ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (locGram_diag_ne_zero hQ γ (hD k' hk'B))
    have hNle : Valued.v (N k k) ≤ Valued.v (N k' k') := by
      rw [hvN k hkB, hvN k' hk'B]; exact inv_anti₀ (zero_lt_iff.mpr hG0) hle
    have h2le : Valued.v (2 * N k k) ≤ Valued.v (2 * N k' k') := by
      rw [map_mul, map_mul]; gcongr
    exact (not_le.mpr hlt₂) ((hk b₃ b₄ hb₃ hb₄).trans h2le)

/-- **Theorem 18, "only if", at $p = 2$ for a core with $1$-dimensional constituents outside its scale range**
(Conway–Sloane §9.5, p. 391; unconditional): if $L_2$ has a basis with `IsDiagCore` whose core is a terminal case of
a peeling chain with partners (of $\gamma$ or of the dual basis), Theorem 18 ("only if") holds for $L$ at $2$. -/
@[kb "conwaysloane1999" "Ch. 15, §9.5, Thm. 18, p. 391 (p = 2, 'only if': a core with 1-dimensional constituents outside its scale range)"]
theorem theorem18OnlyIf_of_diagCore (hQ : Q.Nondegenerate) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : GL (Fin n) Fv) (hγ : loc v L.1 = locAct v γ (std v)) (N : Matrix (Fin n) (Fin n) Fv)
    (hN : locGram Q v γ * N = 1) {B : Finset (Fin n)} (h : IsDiagCore v (locGram Q v γ) N B)
    (hterm : TwoSidedChain Q v γ N hN Bᶜ []) : Theorem18OnlyIf Q L v hQ := by
  rcases twoSidedChain_or_top_of_diagCore hQ h2 γ hγ N hN h hterm with htop | ⟨ks, hks⟩
  · exact theorem18OnlyIf_of_eq_top hQ htop
  · exact theorem18OnlyIf_of_twoSidedChain hQ h2 γ hγ N hN ks hks

end DiagBlock

end QuadFormsKB.ConwaySloane
