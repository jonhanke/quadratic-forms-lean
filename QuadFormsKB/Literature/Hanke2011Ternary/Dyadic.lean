/-
# Hanke 2011 (ternary masses), §4: local ternary computations at $\mathfrak p \mid 2$, $F_{\mathfrak p} = \mathbb{Q}_2$

J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §4, pp. 9–15.

Since $F_{\mathfrak p} = \mathbb{Q}_2$, everything here is stated over $\mathbb{Q}_2$ (`ℚ_[2]`), with the
repository's Hilbert symbol `hilbertSymbol ℚ_[2]` and the explicit formula `hilbertSymbol_two_formula`
(Serre III.1.2): for $u, v \in \mathbb{Z}_2^\times$, $(2^\alpha u, 2^\beta v)_2 =
(-1)^{\varepsilon(u)\varepsilon(v) + \alpha\omega(v) + \beta\omega(u)}$ with $\varepsilon$ = `twoEps`,
$\omega$ = `twoOmega` read off $u \bmod 8$.

* `PartialLocalGenusSymbol` (**Definition 4.1**, = paper 6, Def. 5.1) and `lemma_4_2`: there are exactly $20$ partial
  local genus symbols of size $3$. *(Integration note: the definition is copied from paper 6's
  `Hanke2011Structure.PartialLocalGenusSymbol`, branch `paper06`, not yet on main; replace it by that one when both
  are merged.)*
* `remark_4_3_Q1`, `remark_4_3_Q2` (**Remark 4.3**): the $\mathbb{Q}$-diagonalizations of the two unimodular type
  $\mathrm{II}_2$ forms and their signs.
* `lemma_4_6` (**Lemma 4.6**, with **Definition 4.7**): the Hasse invariant of $ax^2 + 2^\beta by^2 + 2^\gamma cz^2$
  splits as the unit Hasse invariant times the valuation adjustment; `c2unit_mod_four`: the unit Hasse invariant
  depends only on $a, b, c \bmod 4$.
* `lemma_4_9` (**Lemma 4.9**): $u \in (\mathbb{Z}/8)^\times$ is determined by $u \bmod 4$ and the Kronecker symbol
  $\left(\frac{u}{2}\right)$ (`ZMod.χ₈`).
* `block_I3_table`, `block_I2_table`, `lemma_4_10` (**Lemma 4.10**): the representative tables and the
  multiplicities of the unit Hasse invariant.
* `remark_6_3_hilbert` (**Remark 6.3**): $(u, u)_2 = (-1, u)_2$ for $u \in \mathbb{Z}_2^\times$.
* `typeII_hasse` (**proof of Lemma 4.10**, Block $\mathrm{II}_2$ table): *Erratum (proposed by the formalization):*
  the paper says "$c_2 = c_{2,\mathrm{unit}} = -1$ for both of these blocks"; in fact
  $c_2(\langle -2, 2\rangle) = (-2,2)_2 = +1$ and $c_2(\langle 2, 6\rangle) = (2,6)_2 = -1$ (Serre's convention
  $\prod_{i<j}$, used throughout the paper, Lemma 2.2); the remark is not used in the tables.
-/
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Equiv.Hilbert
import QuadFormsKB.Citation

namespace QuadFormsKB.Hanke2011Ternary

open QuadFormsKB.HilbertLocal Matrix

/-! ## Definition 4.1 and Lemma 4.2: partial local genus symbols -/

/-- A **separator** between two adjacent blocks of a partial local genus symbol (paper 6, Def. 5.1(1)):
a comma `,`, a semicolon `;`, or a pair of colons `::`. -/
inductive Separator
  /-- The comma `,`. -/
  | comma
  /-- The semicolon `;` (allowed only between two unbarred blocks). -/
  | semicolon
  /-- The pair of colons `::`. -/
  | doubleColon
  deriving DecidableEq, Repr

instance : Fintype Separator :=
  ⟨{Separator.comma, Separator.semicolon, Separator.doubleColon}, by intro x; cases x <;> simp⟩

/-- **Partial local genus symbol of size $n$** (Definition 4.1, recalling paper 6, Def. 5.1 and Rem. 5.2, p. 22):
a tuple $(n_1, \dots, n_r)$ of positive integers with $n_1 + \dots + n_r = n$ ($r$ not specified), in which
1. each of the $r - 1$ separators between adjacent blocks is `,`, `;` or `::`;
2. each even $n_i$ may carry a bar $\bar n_i$ (odd blocks may not);
3. the separator `;` may appear only between two adjacent unbarred numbers.
They correspond to the Conway–Sloane 2-adic genus symbols without signs and oddities: `::` separates trains, barred
numbers are type II blocks, `;` separates compartments.

Fields (0-based): `blocks` is $(n_1,\dots,n_r)$ (a `Composition n`); `seps[i]` is the separator between blocks $i$
and $i+1$; `bars[i] = true` means block $i$ is barred. -/
@[kb "hanke2011ternary" "§4, Def. 4.1, p. 9"]
structure PartialLocalGenusSymbol (n : ℕ) where
  /-- The underlying Jordan block structure $(n_1,\dots,n_r)$. -/
  blocks : Composition n
  /-- The separators between adjacent blocks. -/
  seps : List Separator
  /-- Which blocks carry a bar. -/
  bars : List Bool
  /-- There is one separator between each pair of adjacent blocks: $r-1$ in total. -/
  seps_length : seps.length = blocks.length - 1
  /-- There is one bar flag per block. -/
  bars_length : bars.length = blocks.length
  /-- Condition (2): only even blocks may be barred. -/
  bar_even : ∀ i : ℕ, bars[i]? = some true → ∃ b ∈ blocks.blocks[i]?, Even b
  /-- Condition (3): a semicolon at position $i$ requires blocks $i$ and $i+1$ both unbarred. -/
  semicolon_unbarred : ∀ i : ℕ, seps[i]? = some Separator.semicolon →
    bars[i]? = some false ∧ bars[i + 1]? = some false

namespace PartialLocalGenusSymbol

/-- A computable enumeration of the compositions of `n` as lists, with fuel `f` (Mathlib's `Composition` is not
kernel-reducible, so the finiteness is established through this list). -/
def compsF : ℕ → ℕ → List (List ℕ)
  | f, n =>
    if n = 0 then [[]] else
      match f with
      | 0 => []
      | f + 1 => (List.range n).flatMap fun j => (compsF f (n - (j + 1))).map (List.cons (j + 1))

theorem compsF_sound : ∀ (f n : ℕ) (l : List ℕ), l ∈ compsF f n → (∀ x ∈ l, 0 < x) ∧ l.sum = n := by
  intro f
  induction f with
  | zero =>
    intro n l hl
    unfold compsF at hl
    split_ifs at hl with h
    · simp at hl; subst hl; simp [h]
    · simp at hl
  | succ f ih =>
    intro n l hl
    unfold compsF at hl
    split_ifs at hl with h
    · simp at hl; subst hl; simp [h]
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hl
      obtain ⟨j, hj, t, ht, rfl⟩ := hl
      obtain ⟨h1, h2⟩ := ih _ t ht
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact h1 x hx
      · simp [h2]; omega

theorem compsF_complete : ∀ (l : List ℕ) (f n : ℕ), l.length ≤ f → (∀ x ∈ l, 0 < x) → l.sum = n →
    l ∈ compsF f n := by
  intro l
  induction l with
  | nil =>
    intro f n _ _ hs
    simp at hs; subst hs
    unfold compsF; simp
  | cons x t ih =>
    intro f n hf hp hs
    have hx : 0 < x := hp x (by simp)
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    unfold compsF
    have hn : n ≠ 0 := by simp at hs; omega
    rw [if_neg hn]
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    have e : x - 1 + 1 = x := by omega
    refine ⟨x - 1, by simp at hs; omega, t, ?_, by simp [e]⟩
    rw [e]
    exact ih f' (n - x) (by simp at hf; omega)
      (fun y hy => hp y (by simp [hy])) (by simp at hs; omega)

/-- Compositions of `n` as lists. -/
abbrev Cl (n : ℕ) : Type := ↥(compsF n n).toFinset

/-- Raw data of a symbol, before imposing conditions (2) and (3). -/
abbrev Data (n : ℕ) : Type :=
  Σ c : Cl n, List.Vector Separator (c.1.length - 1) × List.Vector Bool c.1.length

/-- Conditions (2) and (3) on raw data. -/
def Valid {n : ℕ} (d : Data n) : Prop :=
  (∀ i : ℕ, d.2.2.1[i]? = some true → ∃ b ∈ d.1.1[i]?, Even b) ∧
  (∀ i : ℕ, d.2.1.1[i]? = some Separator.semicolon →
    d.2.2.1[i]? = some false ∧ d.2.2.1[i + 1]? = some false)

instance {n : ℕ} (d : Data n) : Decidable (Valid d) := by
  have hs : d.2.1.1.length ≤ d.1.1.length := by rw [d.2.1.2]; omega
  have hb : d.2.2.1.length = d.1.1.length := d.2.2.2
  have hex : ∀ i : ℕ, (∃ b ∈ d.1.1[i]?, Even b) ↔
      (d.1.1[i]?.any (fun b => decide (Even b))) = true := by
    intro i
    cases d.1.1[i]? <;> simp
  refine decidable_of_iff
    ((∀ i < d.1.1.length + 1, d.2.2.1[i]? = some true → (d.1.1[i]?.any (fun b => decide (Even b))) = true) ∧
     (∀ i < d.1.1.length + 1, d.2.1.1[i]? = some Separator.semicolon →
       d.2.2.1[i]? = some false ∧ d.2.2.1[i + 1]? = some false)) ?_
  unfold Valid
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · by_cases hlt : i < d.1.1.length + 1
      · exact (hex i).2 (h1 i hlt hi)
      · rw [List.getElem?_eq_none (by omega)] at hi
        simp at hi
    · by_cases hlt : i < d.1.1.length + 1
      · exact h2 i hlt hi
      · rw [List.getElem?_eq_none (by omega)] at hi
        simp at hi
  · rintro ⟨h1, h2⟩
    exact ⟨fun i _ hi => (hex i).1 (h1 i hi), fun i _ hi => h2 i hi⟩

/-- Symbols of size $n$ are exactly the valid raw data. -/
def equivValid {n : ℕ} : PartialLocalGenusSymbol n ≃ {d : Data n // Valid d} where
  toFun s := ⟨⟨⟨s.blocks.blocks, List.mem_toFinset.mpr (compsF_complete _ n n
      (by simpa [Composition.length] using s.blocks.length_le)
      (fun x hx => s.blocks.blocks_pos hx) s.blocks.blocks_sum)⟩,
      ⟨s.seps, s.seps_length⟩, ⟨s.bars, s.bars_length⟩⟩, s.bar_even, s.semicolon_unbarred⟩
  invFun d := ⟨⟨d.1.1.1, fun {i} hi => (compsF_sound _ _ _ (List.mem_toFinset.mp d.1.1.2)).1 i hi,
      (compsF_sound _ _ _ (List.mem_toFinset.mp d.1.1.2)).2⟩,
      d.1.2.1.1, d.1.2.2.1, d.1.2.1.2, d.1.2.2.2, d.2.1, d.2.2⟩
  left_inv s := rfl
  right_inv := by
    rintro ⟨⟨⟨c, hc⟩, ⟨s, hs⟩, ⟨b, hb⟩⟩, hv⟩
    rfl

end PartialLocalGenusSymbol

instance (n : ℕ) : Fintype (PartialLocalGenusSymbol n) :=
  Fintype.ofEquiv _ PartialLocalGenusSymbol.equivValid.symm

/-- **Lemma 4.2** (Hanke 2011, p. 10): there are exactly $20$ partial local genus symbols of size $3$:
$(3)$, $(2,1)$, $(2;1)$, $(2::1)$, $(\bar2,1)$, $(\bar2::1)$, $(1,2)$, $(1;2)$, $(1::2)$, $(1,\bar2)$,
$(1::\bar2)$, $(1,1,1)$, $(1,1;1)$, $(1;1,1)$, $(1;1;1)$, $(1,1::1)$, $(1::1,1)$, $(1::1;1)$, $(1;1::1)$,
$(1::1::1)$. -/
@[kb "hanke2011ternary" "§4, Lemma 4.2, p. 10"]
theorem lemma_4_2 : Fintype.card (PartialLocalGenusSymbol 3) = 20 := by
  rw [Fintype.card_congr PartialLocalGenusSymbol.equivValid]
  decide +kernel

/-! ## Remark 4.3: type $\mathrm{II}_2$ diagonalization -/

/-- **Remark 4.3**, first form (Hanke 2011, p. 10): $Q_1 = \begin{pmatrix}0&1\\1&0\end{pmatrix}
\sim_{\mathbb{Q}_2} \begin{pmatrix}-2&0\\0&2\end{pmatrix}$, via $P^{\mathsf T}Q_1P$ with
$P = \begin{pmatrix}1&1\\-1&1\end{pmatrix}$ ($\det P = 2 \ne 0$; the congruence holds over $\mathbb{Q}$), and
$\det_G(Q_1) = -1 \equiv 7 \pmod 8$, so its sign $\left(\frac{\det}{2}\right) = \chi_8(7) = +1$. -/
@[kb "hanke2011ternary" "§4, Remark 4.3, p. 10"]
theorem remark_4_3_Q1 :
    (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ * !![0, 1; 1, 0] * !![1, 1; -1, 1] = !![-2, 0; 0, 2] ∧
    (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 ∧
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = -1 ∧ ((-1 : ℤ) : ZMod 8) = 7 ∧ ZMod.χ₈ (7 : ZMod 8) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [Matrix.det_fin_two_of]; norm_num
  · rw [Matrix.det_fin_two_of]; norm_num
  · decide
  · decide

/-- **Remark 4.3**, second form (Hanke 2011, p. 10): $Q_2 = \begin{pmatrix}2&1\\1&2\end{pmatrix}
\sim_{\mathbb{Q}_2} \begin{pmatrix}2&0\\0&6\end{pmatrix}$, via $P = \begin{pmatrix}1&-1\\0&2\end{pmatrix}$, and
$\det_G(Q_2) = 3$, so its sign is $\chi_8(3) = -1$. -/
@[kb "hanke2011ternary" "§4, Remark 4.3, p. 10"]
theorem remark_4_3_Q2 :
    (!![1, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ * !![2, 1; 1, 2] * !![1, -1; 0, 2] = !![2, 0; 0, 6] ∧
    (!![1, -1; 0, 2] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 ∧
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ).det = 3 ∧ ZMod.χ₈ (3 : ZMod 8) = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [Matrix.det_fin_two_of]; norm_num
  · rw [Matrix.det_fin_two_of]; norm_num
  · decide

/-! ## Lemma 4.6 and Definition 4.7: structure of the Hasse invariant -/

/-- **The unit Hasse invariant** $c_{2,\mathrm{unit}} := (a,b)_2(a,c)_2(b,c)_2$ (Definition 4.7, p. 11), for units
$a, b, c$ of $\mathbb{Z}_2$. -/
@[kb "hanke2011ternary" "§4, Def. 4.7, p. 11"]
noncomputable def c2unit (a b c : ℤ_[2]ˣ) : ℤ :=
  hilbertSymbol ℚ_[2] ((a : ℤ_[2]) : ℚ_[2]) ((b : ℤ_[2]) : ℚ_[2]) *
    hilbertSymbol ℚ_[2] ((a : ℤ_[2]) : ℚ_[2]) ((c : ℤ_[2]) : ℚ_[2]) *
    hilbertSymbol ℚ_[2] ((b : ℤ_[2]) : ℚ_[2]) ((c : ℤ_[2]) : ℚ_[2])

/-- **The valuation adjustment** $(2^\beta, ac)_2(2^\gamma, ab)_2$ (Definition 4.7, p. 11). -/
@[kb "hanke2011ternary" "§4, Def. 4.7, p. 11"]
noncomputable def valuationAdjustment (β γ : ℤ) (a b c : ℤ_[2]ˣ) : ℤ :=
  hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ β) ((a : ℤ_[2]) * (c : ℤ_[2]) : ℚ_[2]) *
    hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ γ) ((a : ℤ_[2]) * (b : ℤ_[2]) : ℚ_[2])

/-! ### Helper lemmas for the Hilbert symbol over $\mathbb{Q}_2$ -/

private lemma hsqL {K : Type*} [Field K] (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K (c ^ 2 * a) b = hilbertSymbol K a b := by
  unfold hilbertSymbol
  congr 1
  apply propext
  constructor
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨c * x, y, z, ?_, by rw [heq]; ring⟩
    intro h
    apply hne
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, mul_eq_zero, hc, false_or] at h ⊢
    exact h
  · rintro ⟨x, y, z, hne, heq⟩
    refine ⟨x / c, y, z, ?_, by rw [heq]; field_simp⟩
    intro h
    apply hne
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hc, or_false] at h ⊢
    exact h

private lemma hsqR {K : Type*} [Field K] (a b c : K) (hc : c ≠ 0) :
    hilbertSymbol K a (c ^ 2 * b) = hilbertSymbol K a b := by
  rw [hilbertSymbol_comm, hsqL _ _ _ hc, hilbertSymbol_comm]

private lemma hmulL (a a' b : ℚ_[2]) (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) :
    hilbertSymbol ℚ_[2] (a * a') b = hilbertSymbol ℚ_[2] a b * hilbertSymbol ℚ_[2] a' b :=
  hilbertSymbol_padic_mul_left (p := 2) a a' b ha ha' hb

private lemma hmulR (a b b' : ℚ_[2]) (ha : a ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    hilbertSymbol ℚ_[2] a (b * b') = hilbertSymbol ℚ_[2] a b * hilbertSymbol ℚ_[2] a b' := by
  rw [hilbertSymbol_comm, hmulL _ _ _ hb hb' ha, hilbertSymbol_comm _ b a, hilbertSymbol_comm _ b' a]

private lemma unit_coe_ne (u : ℤ_[2]ˣ) : ((u : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
  intro h0
  exact u.ne_zero (PadicInt.ext (by simpa using h0))

private lemma two_zpow_split (β : ℤ) :
    (2 : ℚ_[2]) ^ β = ((2 : ℚ_[2]) ^ (β / 2)) ^ 2 * (2 : ℚ_[2]) ^ (β % 2) := by
  rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ two_ne_zero]
  congr 1
  push_cast
  omega

private lemma hilbert_two_pow_two_pow (β γ : ℤ) :
    hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ β) ((2 : ℚ_[2]) ^ γ) = 1 := by
  rw [two_zpow_split β, two_zpow_split γ,
    hsqL _ _ _ (zpow_ne_zero _ two_ne_zero), hsqR _ _ _ (zpow_ne_zero _ two_ne_zero)]
  have h22 : hilbertSymbol ℚ_[2] 2 2 = 1 := by
    unfold hilbertSymbol
    rw [if_pos]
    refine ⟨1, 1, 2, by simp, by norm_num⟩
  rcases (by omega : β % 2 = 0 ∨ β % 2 = 1) with h | h <;>
  rcases (by omega : γ % 2 = 0 ∨ γ % 2 = 1) with h' | h' <;> rw [h, h'] <;>
  simp [h22, hilbertSymbol_one_right] <;> rw [hilbertSymbol_comm] <;> simp [hilbertSymbol_one_right]

private lemma hilbert_units_eq (u v : ℤ_[2]ˣ) :
    hilbertSymbol ℚ_[2] ((u : ℤ_[2]) : ℚ_[2]) ((v : ℤ_[2]) : ℚ_[2]) =
      (-1) ^ (twoEps (PadicInt.toZModPow 3 (u : ℤ_[2])) * twoEps (PadicInt.toZModPow 3 (v : ℤ_[2]))) := by
  have := hilbertSymbol_two_formula 0 0 u v
  simpa using this

/-- **Lemma 4.6** (Hanke 2011, p. 11): for units $a, b, c \in \mathbb{Z}_2^\times$ and $\beta, \gamma \in \mathbb{Z}$,
the Hasse invariant $c_2 = \prod_{i<j}(a_i, a_j)_2$ of $ax^2 + 2^\beta by^2 + 2^\gamma cz^2$ is
$$c_2 = \underbrace{(a,b)_2(a,c)_2(b,c)_2}_{c_{2,\mathrm{unit}}}\cdot
\underbrace{(2^\beta, ac)_2(2^\gamma, ab)_2}_{\text{valuation adjustment}}.$$ -/
@[kb "hanke2011ternary" "§4, Lemma 4.6, p. 11"]
theorem lemma_4_6 (a b c : ℤ_[2]ˣ) (β γ : ℤ) :
    hilbertSymbol ℚ_[2] ((a : ℤ_[2]) : ℚ_[2]) ((2 : ℚ_[2]) ^ β * ((b : ℤ_[2]) : ℚ_[2])) *
      hilbertSymbol ℚ_[2] ((a : ℤ_[2]) : ℚ_[2]) ((2 : ℚ_[2]) ^ γ * ((c : ℤ_[2]) : ℚ_[2])) *
      hilbertSymbol ℚ_[2] ((2 : ℚ_[2]) ^ β * ((b : ℤ_[2]) : ℚ_[2])) ((2 : ℚ_[2]) ^ γ * ((c : ℤ_[2]) : ℚ_[2])) =
    c2unit a b c * valuationAdjustment β γ a b c := by
  have hA := unit_coe_ne a
  have hB := unit_coe_ne b
  have hC := unit_coe_ne c
  have hP : (2 : ℚ_[2]) ^ β ≠ 0 := zpow_ne_zero _ two_ne_zero
  have hQ : (2 : ℚ_[2]) ^ γ ≠ 0 := zpow_ne_zero _ two_ne_zero
  unfold c2unit valuationAdjustment
  push_cast
  rw [hmulR _ _ _ hA hP hB, hmulR _ _ _ hA hQ hC, hmulL _ _ _ hP hB (mul_ne_zero hQ hC),
    hmulR _ _ _ hP hQ hC, hmulR _ _ _ hB hQ hC, hmulR _ _ _ hP hA hC, hmulR _ _ _ hQ hA hB,
    hilbertSymbol_comm _ _ ((2 : ℚ_[2]) ^ β), hilbertSymbol_comm _ _ ((2 : ℚ_[2]) ^ γ) ,
    hilbertSymbol_comm _ ((2 : ℚ_[2]) ^ γ) ((b : ℤ_[2]) : ℚ_[2]), hilbert_two_pow_two_pow]
  ring

/-- **Lemma 4.6**, last claim (p. 11): $c_{2,\mathrm{unit}}$ depends only on $a, b, c \bmod 4\mathbb{Z}_2$. -/
@[kb "hanke2011ternary" "§4, Lemma 4.6, p. 11"]
theorem c2unit_mod_four (a b c a' b' c' : ℤ_[2]ˣ)
    (ha : PadicInt.toZModPow 2 (a : ℤ_[2]) = PadicInt.toZModPow 2 (a' : ℤ_[2]))
    (hb : PadicInt.toZModPow 2 (b : ℤ_[2]) = PadicInt.toZModPow 2 (b' : ℤ_[2]))
    (hc : PadicInt.toZModPow 2 (c : ℤ_[2]) = PadicInt.toZModPow 2 (c' : ℤ_[2])) :
    c2unit a b c = c2unit a' b' c' := by
  have hcomp := PadicInt.zmod_cast_comp_toZModPow (p := 2) 2 3 (by norm_num)
  have key : ∀ x y : ℤ_[2], PadicInt.toZModPow 2 x = PadicInt.toZModPow 2 y →
      ZMod.castHom (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)) (ZMod (2 ^ 2)) (PadicInt.toZModPow 3 x) =
        ZMod.castHom (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)) (ZMod (2 ^ 2)) (PadicInt.toZModPow 3 y) := by
    intro x y h
    have h1 := RingHom.congr_fun hcomp x
    have h2 := RingHom.congr_fun hcomp y
    simp only [RingHom.comp_apply] at h1 h2
    rw [h1, h2, h]
  have eps : ∀ r r' : ZMod (2 ^ 3),
      ZMod.castHom (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)) (ZMod (2 ^ 2)) r =
        ZMod.castHom (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)) (ZMod (2 ^ 2)) r' → twoEps r = twoEps r' := by
    decide
  unfold c2unit
  rw [hilbert_units_eq a b, hilbert_units_eq a c, hilbert_units_eq b c, hilbert_units_eq a' b',
    hilbert_units_eq a' c', hilbert_units_eq b' c']
  rw [eps _ _ (key _ _ ha), eps _ _ (key _ _ hb), eps _ _ (key _ _ hc)]

/-! ## Lemma 4.9: sign decorations -/

/-- **Lemma 4.9** (Hanke 2011, p. 12): a unit $u \in (\mathbb{Z}/8\mathbb{Z})^\times$ is determined by its reduction
$u \bmod 4$ and the value of the Kronecker symbol $\left(\frac{u}{2}\right) = \chi_8(u)$ ($+1$ if
$u \equiv \pm1 \pmod 8$, $-1$ if $u \equiv \pm 3 \pmod 8$); every pair (unit mod $4$, sign) occurs. -/
@[kb "hanke2011ternary" "§4, Lemma 4.9, p. 12"]
theorem lemma_4_9 (r : ZMod 4) (hr : IsUnit r) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∃! u : ZMod 8, IsUnit u ∧ ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) u = r ∧ ZMod.χ₈ u = s := by
  have h4 : ∀ r : ZMod 4, IsUnit r ↔ ∃ v, r * v = 1 := fun r => isUnit_iff_exists_inv
  have h8 : ∀ r : ZMod 8, IsUnit r ↔ ∃ v, r * v = 1 := fun r => isUnit_iff_exists_inv
  simp only [ExistsUnique, h8]
  rw [h4] at hr
  rcases hs with rfl | rfl <;> revert r <;> decide

/-! ## Lemma 4.10: fixed sign $c_2$-distributions -/

/-- **The unit Hilbert symbol on residues mod 8**: $(u, v)_2 = (-1)^{\varepsilon(u)\varepsilon(v)}$ for odd $u, v$
(`hilbertSymbol_two_formula` with $\alpha = \beta = 0$; `hilbert2_eq`). -/
def hilbert2 (u v : ZMod 8) : ℤ := (-1) ^ (twoEps u * twoEps v)

/-- The repository's Hilbert symbol on $\mathbb{Z}_2$-units agrees with `hilbert2` on their residues mod $8$. -/
theorem hilbert2_eq (u v : ℤ_[2]ˣ) :
    hilbertSymbol ℚ_[2] ((u : ℤ_[2]) : ℚ_[2]) ((v : ℤ_[2]) : ℚ_[2]) =
      hilbert2 (PadicInt.toZModPow 3 (u : ℤ_[2])) (PadicInt.toZModPow 3 (v : ℤ_[2])) := by
  have := hilbertSymbol_two_formula 0 0 u v
  simpa [hilbert2] using this

/-- The unit Hasse invariant $\prod_{i<j}(a_i, a_j)_2$ of a diagonal form with odd entries, on residues mod 8. -/
def c2unitList : List (ZMod 8) → ℤ
  | [] => 1
  | a :: l => (l.map (hilbert2 a)).prod * c2unitList l

/-- **Block $I_3$ table** (proof of Lemma 4.10, p. 13): the representatives $\operatorname{diag}[\dots]$ of the
unimodular type $I_3$ blocks with given sign and oddity (`(rep, sign, oddity, c₂,unit, det mod 8)`): the sign is
$\chi_8(\det)$, the oddity is the trace mod $8$. -/
@[kb "hanke2011ternary" "§4, proof of Lemma 4.10, Block I3 tables, p. 13"]
def blockI3 : List (List (ZMod 8) × ℤ × ZMod 8 × ℤ × ZMod 8) :=
  [([1, 1, -1], 1, 1, 1, 7), ([1, 1, 1], 1, 3, 1, 1), ([-1, -1, -1], 1, 5, -1, 7), ([1, -1, -1], 1, 7, -1, 1),
   ([-1, -1, 3], -1, 1, -1, 3), ([1, -1, 3], -1, 3, -1, 5), ([1, 1, 3], -1, 5, 1, 3), ([1, 1, -3], -1, 7, 1, 5)]

/-- **Block $I_3$ table is correct** (p. 13): each listed representative has the listed sign, oddity, unit Hasse
invariant and determinant. -/
@[kb "hanke2011ternary" "§4, proof of Lemma 4.10, Block I3 tables, p. 13"]
theorem block_I3_table : ∀ e ∈ blockI3,
    ZMod.χ₈ e.1.prod = e.2.1 ∧ e.1.sum = e.2.2.1 ∧ c2unitList e.1 = e.2.2.2.1 ∧ e.1.prod = e.2.2.2.2 := by
  decide +kernel

/-- **Block $I_2$ table** (proof of Lemma 4.10, p. 13): `(rep, sign, oddity, (a,b)₂, det mod 8)`. -/
@[kb "hanke2011ternary" "§4, proof of Lemma 4.10, Block I2 tables, p. 13"]
def blockI2 : List (List (ZMod 8) × ℤ × ZMod 8 × ℤ × ZMod 8) :=
  [([1, 1], 1, 2, 1, 1), ([-1, -1], 1, -2, -1, 1), ([1, -1], 1, 0, 1, 7),
   ([-1, 3], -1, 2, -1, 5), ([1, -3], -1, -2, 1, 5), ([-1, -3], -1, 4, 1, 3)]

/-- **Block $I_2$ table is correct** (p. 13). -/
@[kb "hanke2011ternary" "§4, proof of Lemma 4.10, Block I2 tables, p. 13"]
theorem block_I2_table : ∀ e ∈ blockI2,
    ZMod.χ₈ e.1.prod = e.2.1 ∧ e.1.sum = e.2.2.1 ∧ c2unitList e.1 = e.2.2.2.1 ∧ e.1.prod = e.2.2.2.2 := by
  decide +kernel

/-- The number of decorations in the list `L` (unit parts of a diagonalization, mod 8) with unit determinant
$\equiv u' \pmod 4$ and unit Hasse invariant `c`. -/
def c2count (L : List (List (ZMod 8))) (u' : ZMod 4) (c : ℤ) : ℕ :=
  (L.filter fun d => decide (ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) d.prod = u') && decide (c2unitList d = c)).length

/-- Unsigned (sign $+$) $I_1 \oplus I_1 \oplus I_1$ decorations: each $I_1$ block is $\operatorname{diag}[1]$ or
$\operatorname{diag}[-1]$. -/
def decI111 : List (List (ZMod 8)) :=
  [[1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1], [-1, 1, 1], [-1, 1, -1], [-1, -1, 1], [-1, -1, -1]]

/-- Unsigned $I_2 \oplus I_1$ decorations: $I_2 \in \{[1,1], [-1,-1], [1,-1]\}$, $I_1 \in \{[1], [-1]\}$. -/
def decI21 : List (List (ZMod 8)) :=
  [[1, 1, 1], [1, 1, -1], [-1, -1, 1], [-1, -1, -1], [1, -1, 1], [1, -1, -1]]

/-- Unsigned $I_3$ decorations: the four sign-$+$ representatives of `blockI3`. -/
def decI3 : List (List (ZMod 8)) := [[1, 1, -1], [1, 1, 1], [-1, -1, -1], [1, -1, -1]]

/-- Unsigned $\mathrm{II}_2 \oplus I_1$ decorations, as unit parts $[a; b, c]$ of $\operatorname{diag}[a, -2, 2]$
($a = \pm1$ the $I_1$ block, $\langle -2, 2\rangle = 2\langle -1, 1\rangle$ the sign-$+$ $\mathrm{II}_2$ block). -/
def decII21 : List (List (ZMod 8)) := [[1, -1, 1], [-1, -1, 1]]

/-- **Lemma 4.10** (Hanke 2011, p. 12): the multiplicities of the unit Hasse invariant $c_{2,\mathrm{unit}} = +1, -1$
over the unsigned decorations with unit determinant $u \equiv u' \pmod 4$:

| | $I_1\oplus I_1\oplus I_1$ | $I_2\oplus I_1$ | $I_3$ | $\mathrm{II}_2\oplus I_1$ |
|---|---|---|---|---|
| $u' \equiv 1$ | $1, 3$ | $1, 2$ | $1, 1$ | $0, 1$ |
| $u' \equiv -1$ | $3, 1$ | $2, 1$ | $1, 1$ | $1, 0$ | -/
@[kb "hanke2011ternary" "§4, Lemma 4.10, p. 12"]
theorem lemma_4_10 :
    (c2count decI111 1 1, c2count decI111 1 (-1), c2count decI111 (-1) 1, c2count decI111 (-1) (-1)) =
      (1, 3, 3, 1) ∧
    (c2count decI21 1 1, c2count decI21 1 (-1), c2count decI21 (-1) 1, c2count decI21 (-1) (-1)) = (1, 2, 2, 1) ∧
    (c2count decI3 1 1, c2count decI3 1 (-1), c2count decI3 (-1) 1, c2count decI3 (-1) (-1)) = (1, 1, 1, 1) ∧
    (c2count decII21 1 1, c2count decII21 1 (-1), c2count decII21 (-1) 1, c2count decII21 (-1) (-1)) =
      (0, 1, 1, 0) := by
  decide +kernel

/-- **The Hasse invariants of the two type $\mathrm{II}_2$ blocks** (proof of Lemma 4.10, Block $\mathrm{II}_2$ table,
p. 13), via their diagonalizations of Remark 4.3: $c_2(\langle -2, 2\rangle) = (-2, 2)_2 = 1$ and
$c_2(\langle 2, 6\rangle) = (2, 6)_2 = -1$. *Erratum (proposed by the formalization):* the paper
states $c_2 = -1$ for both. -/
@[kb "hanke2011ternary" "§4, proof of Lemma 4.10, Block II2 table, p. 13"]
theorem typeII_hasse :
    hilbertSymbol ℚ_[2] (-2) 2 = 1 ∧ hilbertSymbol ℚ_[2] 2 6 = -1 := by
  refine ⟨?_, ?_⟩
  · have h := hilbertSymbol_self_neg ℚ_[2] 2
    rw [hilbertSymbol_comm]
    exact h
  · have h1 : ‖((3 : ℤ) : ℤ_[2])‖ = 1 := by
      have h2 : ¬ ‖((3 : ℤ) : ℤ_[2])‖ < 1 := fun h => by
        have := (PadicInt.norm_int_lt_one_iff_dvd 3).1 h
        omega
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h2)
    have hu : IsUnit ((3 : ℤ) : ℤ_[2]) := PadicInt.isUnit_iff.2 h1
    have := hilbertSymbol_two_formula 1 1 1 hu.unit
    have e3 : ((hu.unit : ℤ_[2]) : ℚ_[2]) = 3 := by
      rw [IsUnit.unit_spec]; push_cast; rfl
    have e3' : PadicInt.toZModPow 3 (hu.unit : ℤ_[2]) = 3 := by
      rw [IsUnit.unit_spec, map_intCast]; norm_num
    rw [e3'] at this
    simp only [pow_one, Units.val_one, PadicInt.coe_one, map_one, one_mul, mul_one] at this
    rw [e3] at this
    have e6 : (2 : ℚ_[2]) * 3 = 6 := by norm_num
    rw [e6] at this
    rw [this]
    decide

/-- **Remark 6.3** (Hanke 2011, p. 24): $(u, u)_2 = (-1, u)_2$ for $u \in \mathbb{Z}_2^\times$ (used to compare the
$u$-dependence of Lemma 6.2 with paper 6, Thm. 5.7). -/
@[kb "hanke2011ternary" "§6, Remark 6.3, p. 24"]
theorem remark_6_3_hilbert (u : ℤ_[2]ˣ) :
    hilbertSymbol ℚ_[2] ((u : ℤ_[2]) : ℚ_[2]) ((u : ℤ_[2]) : ℚ_[2]) =
      hilbertSymbol ℚ_[2] (-1) ((u : ℤ_[2]) : ℚ_[2]) := by
  have h1 := hilbert2_eq u u
  have h2 := hilbert2_eq (-1) u
  have e : (((-1 : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = -1 := by simp
  rw [e] at h2
  rw [h1, h2]
  have e' : PadicInt.toZModPow 3 (((-1 : ℤ_[2]ˣ) : ℤ_[2])) = -1 := by simp
  rw [e']
  unfold hilbert2
  generalize PadicInt.toZModPow 3 (u : ℤ_[2]) = r
  revert r
  decide

end QuadFormsKB.Hanke2011Ternary
