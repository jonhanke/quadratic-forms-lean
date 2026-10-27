/-
# O'Meara §58: orthogonal bases and quaternary spaces (58:1, 58:7)

**Setting.** $F$ is a field with $2$ invertible (O'Meara's Chapter V: characteristic $\ne 2$), $(V, Q)$ a
finite-dimensional quadratic space over $F$ (Mathlib `QuadraticForm F V`), and $B$ is O'Meara's symmetric bilinear
form `OMeara.bil Q` (Mathlib's `QuadraticMap.associated Q`, so $B(x,x) = Q(x)$). *Regular* means
`(QuadraticMap.associated Q).Nondegenerate`. An *orthogonal basis* of $V$ is a basis $X = (X_i)_{i < n}$ with
$B(X_i, X_j) = 0$ for $i \ne j$. Indices are 0-based, as in Lean's `Fin n` (O'Meara's $x_1, \dots, x_n$ are
$x_0, \dots, x_{n-1}$ here); the "adjacent positions $i, i+1$" of a chain step are 0-based.
The discriminant is $d = \det(B(b_i, b_j))$ in a basis $b$ (`gram Q b`), defined only modulo squares as in the book.

**Proves**
* `exists_adjacent_chain_of_orthogonal_bases` (**58:1**, p. 150): any two orthogonal bases $X, Y$ of a regular space
  are joined by a chain of orthogonal bases $X = \mathcal X_0, \dots, \mathcal X_k = Y$ in which each
  $\mathcal X_{m+1}$ arises from $\mathcal X_m$ by altering at most two adjacent basis vectors. The printed
  proof's garbled formulas are reconstructed in `key_reduce`/`exists_chain_first`.
* `isotropic_iff_baseChange_isotropic` (**58:7**, p. 153): for a regular quaternary space $V$ with discriminant $d$
  and $E = F(\sqrt d)$, $V$ is isotropic iff $E \otimes_F V$ (Mathlib's `QuadraticForm.baseChange`) is isotropic.
  The case of a square $d$ (where $E = F$) is trivial and is treated separately.

Helper declarations live in the sub-namespace `QuadFormsKB.OMeara.Sp58`.
-/
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Citation

open QuadraticMap Module

set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

namespace QuadFormsKB.OMeara
namespace Sp58

section Basic

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) {n : ℕ}

/-- A family $x_0, \dots, x_{n-1}$ of vectors that are pairwise orthogonal and have $Q(x_i) \ne 0$. In a regular
space of dimension $n$ these are exactly the orthogonal bases (`isOrthAniso_basis`, `basis_of_isOrthAniso`). -/
structure IsOrthAniso (x : Fin n → V) : Prop where
  orth : ∀ i j, i ≠ j → bil Q (x i) (x j) = 0
  aniso : ∀ i, Q (x i) ≠ 0

variable {Q}

theorem IsOrthAniso.comp {x : Fin n → V} (hx : IsOrthAniso Q x) (σ : Fin n ≃ Fin n) :
    IsOrthAniso Q (x ∘ σ) :=
  ⟨fun _ _ h => hx.orth _ _ (σ.injective.ne h), fun _ => hx.aniso _⟩

theorem IsOrthAniso.linearIndependent {x : Fin n → V} (hx : IsOrthAniso Q x) :
    LinearIndependent F x := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun v => bil Q v (x j)) hg
  simp only [bil_sum_left, bil_smul_left] at h
  rw [show bil Q 0 (x j) = 0 by simp [bil]] at h
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hx.orth i j hij, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), bil_self] at h
  exact (mul_eq_zero.mp h).resolve_right (hx.aniso j)

variable [FiniteDimensional F V]

/-- An orthogonal anisotropic family of length $\dim V$ is a basis. -/
def basisOfIsOrthAniso {x : Fin n → V} (hx : IsOrthAniso Q x) (hn : n = finrank F V) :
    Basis (Fin n) F V :=
  basisOfLinearIndependentOfCardEqFinrank' x hx.linearIndependent (by simpa using hn)

@[simp] theorem coe_basisOfIsOrthAniso {x : Fin n → V} (hx : IsOrthAniso Q x) (hn : n = finrank F V) :
    ⇑(basisOfIsOrthAniso hx hn) = x := by
  simp [basisOfIsOrthAniso]

/-- In a regular space an orthogonal basis consists of anisotropic vectors. -/
theorem isOrthAniso_basis (hQ : (QuadraticMap.associated Q).Nondegenerate) (X : Basis (Fin n) F V)
    (hX : ∀ i j, i ≠ j → bil Q (X i) (X j) = 0) : IsOrthAniso Q X := by
  refine ⟨hX, fun i h0 => ?_⟩
  have hy : (QuadraticMap.associated Q : LinearMap.BilinForm F V) (X i) = 0 := by
    refine X.ext fun j => ?_
    by_cases hij : i = j
    · subst hij
      simpa using h0
    · simpa using hX i j hij
  exact X.ne_zero i (hQ.1 _ fun y => congrArg (fun f => f y) hy)

/-- In a regular space, a vector orthogonal to every member of an orthogonal anisotropic family of length
$\dim V$ is $0$. -/
theorem eq_zero_of_orth (hQ : (QuadraticMap.associated Q).Nondegenerate) {x : Fin n → V}
    (hx : IsOrthAniso Q x) (hn : n = finrank F V) {v : V} (h : ∀ j, bil Q v (x j) = 0) : v = 0 := by
  refine hQ.1 v fun w => ?_
  have hy : (QuadraticMap.associated Q : LinearMap.BilinForm F V) v = 0 :=
    (basisOfIsOrthAniso hx hn).ext fun j => by simpa using h j
  exact congrArg (fun f => f w) hy

end Basic

section Steps

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V) {n : ℕ}

/-- **One step of a chain, acting only on positions $\ge s$:** $x$ and $x'$ are orthogonal anisotropic families
and $x'$ differs from $x$ at most in two adjacent positions $i, i+1$ (0-based) with $i \ge s$. -/
def Step (s : ℕ) (x x' : Fin n → V) : Prop :=
  IsOrthAniso Q x ∧ IsOrthAniso Q x' ∧
    ∃ i : ℕ, s ≤ i ∧ ∀ j : Fin n, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → x' j = x j

variable {Q}

theorem Step.mono {s s' : ℕ} {x x' : Fin n → V} (h : s' ≤ s) (hs : Step Q s x x') : Step Q s' x x' :=
  ⟨hs.1, hs.2.1, by
    obtain ⟨i, hi, hh⟩ := hs.2.2
    exact ⟨i, h.trans hi, hh⟩⟩

theorem Step.orth_left {s : ℕ} {x x' : Fin n → V} (hs : Step Q s x x') : IsOrthAniso Q x := hs.1

theorem Step.orth_right {s : ℕ} {x x' : Fin n → V} (hs : Step Q s x x') : IsOrthAniso Q x' := hs.2.1

/-- A chain of steps at positions $\ge s$ does not change the first $s$ vectors. -/
theorem prefix_of_chain {s : ℕ} {x z : Fin n → V} (h : Relation.ReflTransGen (Step Q s) x z) :
    ∀ j : Fin n, (j : ℕ) < s → z j = x j := by
  induction h with
  | refl => intro j _; rfl
  | tail _ hst ih =>
    intro j hj
    obtain ⟨_, _, i, hi, hh⟩ := hst
    rw [hh j (by omega) (by omega), ih j hj]

/-- Swapping two adjacent vectors is a step. -/
theorem step_swap {x : Fin n → V} (hx : IsOrthAniso Q x) (s i : ℕ) (hsi : s ≤ i) (hi : i + 1 < n) :
    Step Q s x (x ∘ Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩) := by
  refine ⟨hx, hx.comp _, i, hsi, fun j h1 h2 => ?_⟩
  have hj1 : j ≠ (⟨i, by omega⟩ : Fin n) := fun h => h1 (by rw [h])
  have hj2 : j ≠ (⟨i + 1, hi⟩ : Fin n) := fun h => h2 (by rw [h])
  simp [Equiv.swap_apply_of_ne_of_ne hj1 hj2]

/-- The set of positions $j$ with $B(y, x_j) \ne 0$ (the nonzero coordinates of $y$ in the orthogonal basis $x$,
up to the nonzero factors $Q(x_j)$). -/
def supp (Q : QuadraticForm F V) (y : V) (x : Fin n → V) : Finset (Fin n) :=
  Finset.univ.filter fun j => bil Q y (x j) ≠ 0

theorem mem_supp {y : V} {x : Fin n → V} {j : Fin n} : j ∈ supp Q y x ↔ bil Q y (x j) ≠ 0 := by
  simp [supp]

/-- The sum of the positions in a set (the measure decreased by the reduction in the proof of 58:1). -/
def muSum (S : Finset (Fin n)) : ℕ := ∑ j ∈ S, (j : ℕ)

theorem muSum_erase_lt {S : Finset (Fin n)} {w : Fin n} (hw : w ∈ S) (h0 : 0 < (w : ℕ)) :
    muSum (S.erase w) < muSum S := by
  unfold muSum
  rw [← Finset.add_sum_erase S _ hw]
  omega

theorem muSum_swap_lt {x : Fin n → V} {y : V} {i : ℕ} (hi : i + 1 < n)
    (hu : (⟨i, by omega⟩ : Fin n) ∉ supp Q y x) (hw : (⟨i + 1, hi⟩ : Fin n) ∈ supp Q y x) :
    muSum (supp Q y (x ∘ Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩)) < muSum (supp Q y x) := by
  set u : Fin n := ⟨i, by omega⟩ with hu_def
  set w : Fin n := ⟨i + 1, hi⟩ with hw_def
  have huw : u ≠ w := by simp [hu_def, hw_def, Fin.ext_iff]
  have hS : supp Q y (x ∘ Equiv.swap u w) = insert u ((supp Q y x).erase w) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_erase, mem_supp, Function.comp_apply]
    by_cases h1 : j = u
    · subst h1
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => Or.inl rfl, fun _ => mem_supp.mp hw⟩
    · by_cases h2 : j = w
      · subst h2
        rw [Equiv.swap_apply_right]
        refine ⟨fun h => absurd (mem_supp.mpr h) hu, ?_⟩
        rintro (h | ⟨h, _⟩)
        · exact absurd h.symm huw
        · exact absurd rfl h
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ⟨fun h => Or.inr ⟨h2, h⟩, fun h => h.elim (fun h => absurd h h1) fun h => h.2⟩
  have hnot : u ∉ (supp Q y x).erase w := fun h => hu (Finset.mem_of_mem_erase h)
  rw [hS]
  unfold muSum
  rw [Finset.sum_insert hnot, ← Finset.add_sum_erase (supp Q y x) _ hw]
  simp [hu_def, hw_def]

/-- **The reduction step of 58:1** (O'Meara 1973, p. 150, the displayed substitution, whose OCR text is garbled; this is a
reconstruction). Let $x$ be an orthogonal anisotropic family and $y$ a vector with $b_u = B(y, x_u) \ne 0$,
$b_w = B(y, x_w) \ne 0$ for two positions $u \ne w$ and
$Q(a_u x_u) + Q(a_w x_w) = b_u^2/Q(x_u) + b_w^2/Q(x_w) \ne 0$, where $a_j = b_j/Q(x_j)$ are the coordinates of $y$.
Replace $x_u, x_w$ by $x_u' = a_u x_u + a_w x_w$ and $x_w' = b_w x_u - b_u x_w$ (a vector of the plane
$F x_u + F x_w$ orthogonal to $x_u'$). Then the new family is orthogonal and anisotropic, $B(y, x_w') = 0$,
$B(y, x_u') = Q(x_u') \ne 0$, and the other coordinates are unchanged. -/
theorem key_reduce {x : Fin n → V} (hx : IsOrthAniso Q x) (y : V) (u w : Fin n) (huw : u ≠ w)
    (hu : bil Q y (x u) ≠ 0)
    (hq : bil Q y (x u) ^ 2 / Q (x u) + bil Q y (x w) ^ 2 / Q (x w) ≠ 0) :
    ∃ x' : Fin n → V, IsOrthAniso Q x' ∧ (∀ j, j ≠ u → j ≠ w → x' j = x j) ∧ bil Q y (x' w) = 0 ∧
      ∀ j, j ≠ w → (bil Q y (x' j) ≠ 0 ↔ bil Q y (x j) ≠ 0) := by
  obtain ⟨bu, hbu⟩ : ∃ b, b = bil Q y (x u) := ⟨_, rfl⟩
  obtain ⟨bw, hbw⟩ : ∃ b, b = bil Q y (x w) := ⟨_, rfl⟩
  obtain ⟨cu, hcu⟩ : ∃ c, c = Q (x u) := ⟨_, rfl⟩
  obtain ⟨cw, hcw⟩ : ∃ c, c = Q (x w) := ⟨_, rfl⟩
  rw [← hbu] at hu hq
  rw [← hbw] at hq
  rw [← hcu] at hq
  rw [← hcw] at hq
  have hcu0 : cu ≠ 0 := hcu ▸ hx.aniso u
  have hcw0 : cw ≠ 0 := hcw ▸ hx.aniso w
  have hxuw : bil Q (x u) (x w) = 0 := hx.orth u w huw
  have hxwu : bil Q (x w) (x u) = 0 := hx.orth w u huw.symm
  have hxu : bil Q (x u) (x u) = cu := by rw [bil_self, hcu]
  have hxw : bil Q (x w) (x w) = cw := by rw [bil_self, hcw]
  obtain ⟨t, ht⟩ : ∃ t : V, t = (bu / cu) • x u + (bw / cw) • x w := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t' : V, t' = bw • x u + (-bu) • x w := ⟨_, rfl⟩
  have hQt : Q t = bu ^ 2 / cu + bw ^ 2 / cw := by
    rw [ht, Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxuw, ← hcu, ← hcw]
    field_simp
    ring
  have hQt' : Q t' = cu * cw * (bu ^ 2 / cu + bw ^ 2 / cw) := by
    rw [ht', Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxuw, ← hcu, ← hcw]
    field_simp
    ring
  have hbt : bil Q y t = bu ^ 2 / cu + bw ^ 2 / cw := by
    rw [ht, bil_add_right, bil_smul_right, bil_smul_right, ← hbu, ← hbw]
    ring
  have hbt' : bil Q y t' = 0 := by
    rw [ht', bil_add_right, bil_smul_right, bil_smul_right, ← hbu, ← hbw]
    ring
  have htt' : bil Q t t' = 0 := by
    rw [ht, ht']
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, hxuw, hxwu, hxu, hxw]
    field_simp
    ring
  have hto : ∀ b, b ≠ u → b ≠ w → bil Q t (x b) = 0 ∧ bil Q t' (x b) = 0 := by
    intro b h1 h2
    have e1 := hx.orth u b (Ne.symm h1)
    have e2 := hx.orth w b (Ne.symm h2)
    constructor
    · rw [ht, bil_add_left, bil_smul_left, bil_smul_left, e1, e2]; ring
    · rw [ht', bil_add_left, bil_smul_left, bil_smul_left, e1, e2]; ring
  have hQt0 : Q t ≠ 0 := by rw [hQt]; exact hq
  have hQt'0 : Q t' ≠ 0 := by rw [hQt']; exact mul_ne_zero (mul_ne_zero hcu0 hcw0) hq
  obtain ⟨x', hx'⟩ : ∃ x' : Fin n → V, x' = fun j => if j = u then t else if j = w then t' else x j :=
    ⟨_, rfl⟩
  have hxu' : x' u = t := by rw [hx']; simp
  have hxw' : x' w = t' := by rw [hx']; simp [Ne.symm huw]
  have hxo : ∀ j, j ≠ u → j ≠ w → x' j = x j := by
    intro j h1 h2
    rw [hx']; simp [h1, h2]
  have hcls : ∀ j : Fin n, j = u ∨ j = w ∨ (j ≠ u ∧ j ≠ w) := by
    intro j
    by_cases h1 : j = u
    · exact Or.inl h1
    · by_cases h2 : j = w
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
  refine ⟨x', ⟨?_, ?_⟩, hxo, by rw [hxw']; exact hbt', ?_⟩
  · intro a b hab
    rcases hcls a with ha | ha | ⟨ha1, ha2⟩ <;> rcases hcls b with hb | hb | ⟨hb1, hb2⟩
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha, hb, hxu', hxw']; exact htt'
    · rw [ha, hxu', hxo b hb1 hb2]; exact (hto b hb1 hb2).1
    · rw [ha, hb, hxu', hxw', bil_comm]; exact htt'
    · exact absurd (ha.trans hb.symm) hab
    · rw [ha, hxw', hxo b hb1 hb2]; exact (hto b hb1 hb2).2
    · rw [hb, hxu', hxo a ha1 ha2, bil_comm]; exact (hto a ha1 ha2).1
    · rw [hb, hxw', hxo a ha1 ha2, bil_comm]; exact (hto a ha1 ha2).2
    · rw [hxo a ha1 ha2, hxo b hb1 hb2]; exact hx.orth a b hab
  · intro a
    rcases hcls a with ha | ha | ⟨ha1, ha2⟩
    · rw [ha, hxu']; exact hQt0
    · rw [ha, hxw']; exact hQt'0
    · rw [hxo a ha1 ha2]; exact hx.aniso a
  · intro j hj
    by_cases ha1 : j = u
    · rw [ha1, hxu', hbt, ← hbu]
      exact ⟨fun _ => hu, fun _ => hq⟩
    · rw [hxo j ha1 hj]

/-- The reduction of `key_reduce` at the adjacent positions $i, i+1$, as a step: the new family's support is the
old one with the position $i+1$ removed. -/
theorem key_step {x : Fin n → V} (hx : IsOrthAniso Q x) (y : V) (s i : ℕ) (hsi : s ≤ i) (hi : i + 1 < n)
    (hu : bil Q y (x ⟨i, by omega⟩) ≠ 0)
    (hq : bil Q y (x ⟨i, by omega⟩) ^ 2 / Q (x ⟨i, by omega⟩) +
      bil Q y (x ⟨i + 1, hi⟩) ^ 2 / Q (x ⟨i + 1, hi⟩) ≠ 0) :
    ∃ x' : Fin n → V, Step Q s x x' ∧ supp Q y x' = (supp Q y x).erase ⟨i + 1, hi⟩ := by
  have huw : (⟨i, by omega⟩ : Fin n) ≠ ⟨i + 1, hi⟩ := by simp [Fin.ext_iff]
  obtain ⟨x', hx', hxo, hw0, hiff⟩ := key_reduce hx y _ _ huw hu hq
  refine ⟨x', ⟨hx, hx', i, hsi, fun j h1 h2 =>
    hxo j (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))⟩, ?_⟩
  ext j
  rw [mem_supp, Finset.mem_erase, mem_supp]
  by_cases hj : j = ⟨i + 1, hi⟩
  · rw [hj]
    exact ⟨fun h => absurd hw0 h, fun h => absurd rfl h.1⟩
  · exact ⟨fun h => ⟨hj, (hiff j hj).mp h⟩, fun h => (hiff j hj).mpr h.2⟩

/-- Swapping two positions of the support does not change the support. -/
theorem supp_swap {x : Fin n → V} {y : V} {u w : Fin n} (hu : u ∈ supp Q y x) (hw : w ∈ supp Q y x) :
    supp Q y (x ∘ Equiv.swap u w) = supp Q y x := by
  ext j
  rw [mem_supp, Function.comp_apply]
  by_cases h1 : j = u
  · rw [h1, Equiv.swap_apply_left]
    exact ⟨fun _ => hu, fun _ => mem_supp.mp hw⟩
  · by_cases h2 : j = w
    · rw [h2, Equiv.swap_apply_right]
      exact ⟨fun _ => hw, fun _ => mem_supp.mp hu⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, ← mem_supp]

end Steps

section Chain

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V} {n : ℕ}

/-- **Step 1 of the proof of 58:1** (O'Meara 1973, p. 150): if $x$ is an orthogonal basis (family) and $y$ an
anisotropic vector orthogonal to $x_0, \dots, x_{s-1}$, then a chain of steps at positions $\ge s$ leads from $x$ to
an orthogonal basis $z$ with $z_s = y$. Proof by strong induction on the sum of the positions of the support of $y$
(the positions $j$ with $B(y, x_j) \ne 0$): adjacent swaps push the support to the front; then either the support is
$\{s\}$ (and $x_s$ is replaced by $y$) or the reduction `key_reduce` removes one position from the support. -/
theorem exists_chain_first (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : n = finrank F V) (s : ℕ)
    (hs : s < n) (y : V) (hy : Q y ≠ 0) :
    ∀ (m : ℕ) (x : Fin n → V), IsOrthAniso Q x → (∀ j : Fin n, (j : ℕ) < s → bil Q y (x j) = 0) →
      muSum (supp Q y x) = m →
      ∃ z : Fin n → V, Relation.ReflTransGen (Step Q s) x z ∧ IsOrthAniso Q z ∧ z ⟨s, hs⟩ = y := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x hx hpre hm
  have reduce : (∃ x' : Fin n → V, Relation.ReflTransGen (Step Q s) x x' ∧ IsOrthAniso Q x' ∧
      muSum (supp Q y x') < muSum (supp Q y x)) →
      ∃ z : Fin n → V, Relation.ReflTransGen (Step Q s) x z ∧ IsOrthAniso Q z ∧ z ⟨s, hs⟩ = y := by
    rintro ⟨x', hch, hx', hlt⟩
    have hpre' : ∀ j : Fin n, (j : ℕ) < s → bil Q y (x' j) = 0 := fun j hj => by
      rw [prefix_of_chain hch j hj]; exact hpre j hj
    obtain ⟨z, hz1, hz2, hz3⟩ := ih _ (hm ▸ hlt) x' hx' hpre' rfl
    exact ⟨z, hch.trans hz1, hz2, hz3⟩
  have hS_ge : ∀ j ∈ supp Q y x, s ≤ (j : ℕ) := by
    intro j hj
    by_contra h
    exact (mem_supp.mp hj) (hpre j (by omega))
  have hne : ∃ j, j ∈ supp Q y x := by
    by_contra h
    push Not at h
    have h0 : y = 0 := eq_zero_of_orth hQ hx hn fun j => by
      have := h j
      rw [mem_supp, not_not] at this
      exact this
    exact hy (by rw [h0]; exact map_zero Q)
  by_cases hA : ∃ (i : ℕ) (hi : i + 1 < n), s ≤ i ∧ (⟨i, by omega⟩ : Fin n) ∉ supp Q y x ∧
      (⟨i + 1, hi⟩ : Fin n) ∈ supp Q y x
  · obtain ⟨i, hi, hsi, h1, h2⟩ := hA
    exact reduce ⟨_, Relation.ReflTransGen.single (step_swap hx s i hsi hi), hx.comp _,
      muSum_swap_lt hi h1 h2⟩
  push Not at hA
  have hdown : ∀ (i : ℕ) (hi : i + 1 < n), s ≤ i → (⟨i + 1, hi⟩ : Fin n) ∈ supp Q y x →
      (⟨i, by omega⟩ : Fin n) ∈ supp Q y x := by
    intro i hi hsi h
    by_contra h'
    exact hA i hi hsi h' h
  have hclosed : ∀ (d : ℕ) (j j' : Fin n), (j : ℕ) = j' + d → j ∈ supp Q y x → s ≤ (j' : ℕ) →
      j' ∈ supp Q y x := by
    intro d
    induction d with
    | zero =>
      intro j j' h hj _
      have : j = j' := Fin.ext (by omega)
      rwa [← this]
    | succ d ihd =>
      intro j j' h hj hsj
      have hlt : (j' : ℕ) + 1 < n := by have := j.2; omega
      have h1 : (⟨(j' : ℕ) + 1, hlt⟩ : Fin n) ∈ supp Q y x :=
        ihd j ⟨(j' : ℕ) + 1, hlt⟩ (by simp only; omega) hj (by simp only; omega)
      exact hdown j' hlt hsj h1
  have hs_mem : (⟨s, hs⟩ : Fin n) ∈ supp Q y x := by
    obtain ⟨j, hj⟩ := hne
    have := hS_ge j hj
    exact hclosed ((j : ℕ) - s) j ⟨s, hs⟩ (by simp only; omega) hj le_rfl
  have hu0 : bil Q y (x ⟨s, hs⟩) ≠ 0 := mem_supp.mp hs_mem
  by_cases h1 : ∃ hlt : s + 1 < n, (⟨s + 1, hlt⟩ : Fin n) ∈ supp Q y x
  swap
  · -- the support is {s}: replace x_s by y
    have hother : ∀ j : Fin n, j ≠ ⟨s, hs⟩ → bil Q y (x j) = 0 := by
      intro j hj
      by_contra hb
      have hjs := hS_ge j (mem_supp.mpr hb)
      have hlt : s + 1 < n := by have := j.2; have : (j : ℕ) ≠ s := fun h => hj (Fin.ext h); omega
      exact h1 ⟨hlt, hclosed ((j : ℕ) - (s + 1)) j ⟨s + 1, hlt⟩
        (by simp only; have : (j : ℕ) ≠ s := fun h => hj (Fin.ext h); omega) (mem_supp.mpr hb) (by simp only; omega)⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin n → V, z = Function.update x ⟨s, hs⟩ y := ⟨_, rfl⟩
    have hzu : z ⟨s, hs⟩ = y := by rw [hz]; exact Function.update_self ..
    have hzo : ∀ j, j ≠ (⟨s, hs⟩ : Fin n) → z j = x j := by
      intro j hj; rw [hz]; exact Function.update_of_ne hj ..
    have hz' : IsOrthAniso Q z := by
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · by_cases ha : a = ⟨s, hs⟩
        · have hb : b ≠ ⟨s, hs⟩ := fun h => hab (ha.trans h.symm)
          rw [ha, hzu, hzo b hb]; exact hother b hb
        · by_cases hb : b = ⟨s, hs⟩
          · rw [hb, hzu, hzo a ha, bil_comm]; exact hother a ha
          · rw [hzo a ha, hzo b hb]; exact hx.orth a b hab
      · by_cases ha : a = ⟨s, hs⟩
        · rw [ha, hzu]; exact hy
        · rw [hzo a ha]; exact hx.aniso a
    refine ⟨z, Relation.ReflTransGen.single ⟨hx, hz', s, le_rfl, fun j h1 _ => hzo j ?_⟩, hz', hzu⟩
    intro h; exact h1 (by rw [h])
  · obtain ⟨hlt, hw1⟩ := h1
    have hw0 : bil Q y (x ⟨s + 1, hlt⟩) ≠ 0 := mem_supp.mp hw1
    have hcu : Q (x ⟨s, hs⟩) ≠ 0 := hx.aniso _
    have hcw : Q (x ⟨s + 1, hlt⟩) ≠ 0 := hx.aniso _
    have fin1 : ∀ (i : ℕ) (hsi : s ≤ i) (hi : i + 1 < n)
        (hui : bil Q y (x ⟨i, by omega⟩) ≠ 0)
        (hqi : bil Q y (x ⟨i, by omega⟩) ^ 2 / Q (x ⟨i, by omega⟩) +
          bil Q y (x ⟨i + 1, hi⟩) ^ 2 / Q (x ⟨i + 1, hi⟩) ≠ 0)
        (hwS : (⟨i + 1, hi⟩ : Fin n) ∈ supp Q y x),
        ∃ z : Fin n → V, Relation.ReflTransGen (Step Q s) x z ∧ IsOrthAniso Q z ∧
          z ⟨s, hs⟩ = y := by
      intro i hsi hi hui hqi hwS
      obtain ⟨x', hst, hsupp⟩ := key_step hx y s i hsi hi hui hqi
      refine reduce ⟨x', Relation.ReflTransGen.single hst, hst.2.1, ?_⟩
      rw [hsupp]
      exact muSum_erase_lt hwS (Nat.succ_pos i)
    by_cases h2 : ∃ hlt2 : s + 1 + 1 < n, (⟨s + 1 + 1, hlt2⟩ : Fin n) ∈ supp Q y x
    · obtain ⟨hlt2, hw2⟩ := h2
      by_cases hqa : bil Q y (x ⟨s, hs⟩) ^ 2 / Q (x ⟨s, hs⟩) +
          bil Q y (x ⟨s + 1, hlt⟩) ^ 2 / Q (x ⟨s + 1, hlt⟩) = 0
      swap
      · exact fin1 s le_rfl hlt hu0 hqa hw1
      by_cases hqb : bil Q y (x ⟨s + 1, hlt⟩) ^ 2 / Q (x ⟨s + 1, hlt⟩) +
          bil Q y (x ⟨s + 1 + 1, hlt2⟩) ^ 2 / Q (x ⟨s + 1 + 1, hlt2⟩) = 0
      swap
      · exact fin1 (s + 1) (by omega) hlt2 hw0 hqb hw2
      -- both sums vanish: swap the positions s+1, s+2, then reduce at s, s+1
      have hc2 : Q (x ⟨s + 1 + 1, hlt2⟩) ≠ 0 := hx.aniso _
      have hqu : bil Q y (x ⟨s, hs⟩) ^ 2 / Q (x ⟨s, hs⟩) ≠ 0 :=
        div_ne_zero (pow_ne_zero 2 hu0) hcu
      have hsw := supp_swap hw1 hw2
      have e0 : (x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s, hs⟩ = x ⟨s, hs⟩ := by
        refine congrArg x (Equiv.swap_apply_of_ne_of_ne ?_ ?_) <;> (simp [Fin.ext_iff]; try omega)
      have e1 : (x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s + 1, hlt⟩ =
          x ⟨s + 1 + 1, hlt2⟩ := by
        rw [Function.comp_apply, Equiv.swap_apply_left]
      have hstep1 := step_swap hx s (s + 1) (by omega) hlt2
      have hx'' := hx.comp (Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩)
      have hu1 : bil Q y ((x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s, hs⟩) ≠ 0 := by
        rw [e0]; exact hu0
      have hq1 : bil Q y ((x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s, hs⟩) ^ 2 /
          Q ((x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s, hs⟩) +
          bil Q y ((x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s + 1, hlt⟩) ^ 2 /
          Q ((x ∘ Equiv.swap (⟨s + 1, hlt⟩ : Fin n) ⟨s + 1 + 1, hlt2⟩) ⟨s + 1, hlt⟩) ≠ 0 := by
        rw [e0, e1]
        have : bil Q y (x ⟨s, hs⟩) ^ 2 / Q (x ⟨s, hs⟩) +
            bil Q y (x ⟨s + 1 + 1, hlt2⟩) ^ 2 / Q (x ⟨s + 1 + 1, hlt2⟩) =
            2 * (bil Q y (x ⟨s, hs⟩) ^ 2 / Q (x ⟨s, hs⟩)) := by linear_combination hqb - hqa
        rw [this]
        exact mul_ne_zero two_ne_zero hqu
      obtain ⟨x', hst, hsupp⟩ := key_step hx'' y s s le_rfl hlt hu1 hq1
      refine reduce ⟨x', (Relation.ReflTransGen.single hstep1).tail hst, hst.2.1, ?_⟩
      rw [hsupp, hsw]
      exact muSum_erase_lt hw1 (Nat.succ_pos s)
    · -- the support is {s, s+1}: then Q(y) = Q(a_s x_s) + Q(a_{s+1} x_{s+1})
      have hother : ∀ j : Fin n, j ≠ ⟨s, hs⟩ → j ≠ ⟨s + 1, hlt⟩ → bil Q y (x j) = 0 := by
        intro j hj1 hj2
        by_contra hb
        have hjs := hS_ge j (mem_supp.mpr hb)
        have hne1 : (j : ℕ) ≠ s := fun h => hj1 (Fin.ext h)
        have hne2 : (j : ℕ) ≠ s + 1 := fun h => hj2 (Fin.ext h)
        have hlt2 : s + 1 + 1 < n := by have := j.2; omega
        exact h2 ⟨hlt2, hclosed ((j : ℕ) - (s + 1 + 1)) j ⟨s + 1 + 1, hlt2⟩
          (by simp only; omega) (mem_supp.mpr hb) (by simp only; omega)⟩
      have huw : (⟨s, hs⟩ : Fin n) ≠ ⟨s + 1, hlt⟩ := by simp [Fin.ext_iff]
      have hxuw : bil Q (x ⟨s, hs⟩) (x ⟨s + 1, hlt⟩) = 0 := hx.orth _ _ huw
      have hxwu : bil Q (x ⟨s + 1, hlt⟩) (x ⟨s, hs⟩) = 0 := hx.orth _ _ huw.symm
      have hv : y - (bil Q y (x ⟨s, hs⟩) / Q (x ⟨s, hs⟩)) • x ⟨s, hs⟩ -
          (bil Q y (x ⟨s + 1, hlt⟩) / Q (x ⟨s + 1, hlt⟩)) • x ⟨s + 1, hlt⟩ = 0 := by
        refine eq_zero_of_orth hQ hx hn fun j => ?_
        simp only [bil_sub_left, bil_smul_left]
        by_cases hj1 : j = ⟨s, hs⟩
        · rw [hj1, hxwu, bil_self]
          field_simp
          ring
        · by_cases hj2 : j = ⟨s + 1, hlt⟩
          · rw [hj2, hxuw, bil_self]
            field_simp
            ring
          · rw [hother j hj1 hj2, hx.orth _ _ (Ne.symm hj1), hx.orth _ _ (Ne.symm hj2)]
            ring
      have hyexp : y = (bil Q y (x ⟨s, hs⟩) / Q (x ⟨s, hs⟩)) • x ⟨s, hs⟩ +
          (bil Q y (x ⟨s + 1, hlt⟩) / Q (x ⟨s + 1, hlt⟩)) • x ⟨s + 1, hlt⟩ := by
        rw [sub_sub, sub_eq_zero] at hv
        exact hv
      have hQy : Q y = bil Q y (x ⟨s, hs⟩) ^ 2 / Q (x ⟨s, hs⟩) +
          bil Q y (x ⟨s + 1, hlt⟩) ^ 2 / Q (x ⟨s + 1, hlt⟩) := by
        conv_lhs => rw [hyexp]
        rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, hxuw]
        field_simp
        ring
      exact fin1 s le_rfl hlt hu0 (by rw [← hQy]; exact hy) hw1

/-- **Step 2 of the proof of 58:1** (O'Meara 1973, p. 150): induction on the length of the common prefix. Two
orthogonal bases (as families) of a regular space that agree before position $s$ are joined by a chain of steps at
positions $\ge s$. (O'Meara inducts on $n$, passing to the orthogonal complement of $y_1$; here the complement is
replaced by the bookkeeping `s`, which avoids bases of subspaces.) -/
theorem chain_of_isOrthAniso (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : n = finrank F V) :
    ∀ (d s : ℕ), s + d = n → ∀ x y : Fin n → V, IsOrthAniso Q x → IsOrthAniso Q y →
      (∀ j : Fin n, (j : ℕ) < s → x j = y j) → Relation.ReflTransGen (Step Q s) x y := by
  intro d
  induction d with
  | zero =>
    intro s hsd x y _ _ h
    have : x = y := funext fun j => h j (by omega)
    rw [this]
  | succ d ih =>
    intro s hsd x y hx hy hpre
    have hs : s < n := by omega
    obtain ⟨z, hz1, hz2, hz3⟩ := exists_chain_first hQ hn s hs (y ⟨s, hs⟩) (hy.aniso _) _ x hx
      (fun j hj => by
        rw [hpre j hj]
        exact hy.orth _ _ (Fin.ne_of_val_ne (show s ≠ (j : ℕ) by omega))) rfl
    have hzpre : ∀ j : Fin n, (j : ℕ) < s + 1 → z j = y j := by
      intro j hj
      by_cases h : (j : ℕ) < s
      · rw [prefix_of_chain hz1 j h]; exact hpre j h
      · have : j = ⟨s, hs⟩ := Fin.ext (by show (j : ℕ) = s; omega)
        rw [this]; exact hz3
    have hmono : ∀ a b : Fin n → V, Relation.ReflTransGen (Step Q (s + 1)) a b →
        Relation.ReflTransGen (Step Q s) a b := by
      intro a b h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hst ih' => exact ih'.tail (hst.mono (Nat.le_succ s))
    exact hz1.trans (hmono _ _ (ih (s + 1) (by omega) z y hz2 hy hzpre))

end Chain

end Sp58

section Main

open Sp58

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V) {n : ℕ}

/-- $X$ is an **orthogonal basis** of $(V, Q)$: $B(X_i, X_j) = 0$ for $i \ne j$. -/
def IsOrthogonalBasis (X : Basis (Fin n) F V) : Prop :=
  ∀ i j, i ≠ j → bil Q (X i) (X j) = 0

/-- $X'$ is obtained from $X$ by **altering at most two adjacent basis vectors**: there is a (0-based) position $i$
such that $X'_j = X_j$ for all positions $j \notin \{i, i+1\}$. (The position $i$ is a natural number so that
altering only the last vector, $i = n-1$, is allowed.) -/
def AdjacentChange (X X' : Basis (Fin n) F V) : Prop :=
  ∃ i : ℕ, ∀ j : Fin n, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → X' j = X j

variable {Q}

/-- A chain of single steps, as a function chain. -/
theorem exists_chain_of_reflTransGen {X Y : Basis (Fin n) F V}
    (h : Relation.ReflTransGen (fun B C : Basis (Fin n) F V =>
      IsOrthogonalBasis Q B ∧ IsOrthogonalBasis Q C ∧ AdjacentChange B C) X Y)
    (hX : IsOrthogonalBasis Q X) :
    ∃ (k : ℕ) (Z : Fin (k + 1) → Basis (Fin n) F V), Z 0 = X ∧ Z (Fin.last k) = Y ∧
      (∀ m, IsOrthogonalBasis Q (Z m)) ∧
      ∀ m : Fin k, AdjacentChange (Z m.castSucc) (Z m.succ) := by
  induction h with
  | refl => exact ⟨0, fun _ => X, rfl, rfl, fun _ => hX, fun m => m.elim0⟩
  | tail _ hst ih =>
    rename_i B C _
    obtain ⟨k, Z, h0, hl, hZ, hadj⟩ := ih
    refine ⟨k + 1, Fin.snoc Z C, ?_, by simp, ?_, ?_⟩
    · have : (0 : Fin (k + 1 + 1)) = Fin.castSucc 0 := rfl
      rw [this, Fin.snoc_castSucc, h0]
    · intro m
      induction m using Fin.lastCases with
      | last => simpa using hst.2.1
      | cast i => simpa using hZ i
    · intro m
      induction m using Fin.lastCases with
      | last =>
        have e : (Fin.last k).castSucc = Fin.castSucc (Fin.last k) := rfl
        simpa [hl] using hst.2.2
      | cast i =>
        rw [Fin.succ_castSucc]
        simp only [Fin.snoc_castSucc]
        exact hadj i

/-- **Lemma 58:1** (O'Meara 1963, §58, p. 150): *Let $\mathcal X_0$ and $\mathcal X_k$ be two orthogonal bases of a
regular quadratic space $V$. Then there is a chain of orthogonal bases
$\mathcal X_0, \mathcal X_1, \dots, \mathcal X_k$ in which $\mathcal X_m$ is obtained by altering at most two adjacent
basis vectors of $\mathcal X_{m-1}$.*

Formalization: `X Y` are orthogonal bases (`Basis (Fin n) F V` with $B(X_i, X_j) = 0$ for $i \ne j$) of the regular
space $V$ ($n = \dim V$), and `Z : Fin (k + 1) → Basis (Fin n) F V` is the chain, with `Z 0 = X`, `Z (Fin.last k) = Y`,
every `Z m` an orthogonal basis, and each `Z (m+1)` obtained from `Z m` by altering at most the two adjacent
vectors in positions $i, i+1$ (`AdjacentChange`, 0-based: O'Meara's positions $i, i+1$ with $1 \le i < n$ are
positions $i-1, i$ here). A chain of length $k = 0$ is allowed.

*Proof* (as in the book, with the garbled displayed formulas of step 1 reconstructed): `exists_chain_first` moves a
prescribed vector $y_s$ to position $s$ by a chain, choosing among the bases reachable the one whose "support" is
smallest (here: with smallest sum of positions, which also lets adjacent transpositions normalize the support to an
initial segment); if the support is $\{s\}$ one replaces $x_s$ by $y_s$; otherwise `key_reduce` replaces two adjacent
vectors $x_i, x_{i+1}$ of the support by $a_i x_i + a_{i+1} x_{i+1}$ and a vector of their span orthogonal to it,
which lowers the support (when three vectors are in the support, not all of the sums $Q(a_ix_i)+Q(a_jx_j)$ of pairs
vanish, else $Q(a_ix_i) = 0$). Step 2 (`chain_of_isOrthAniso`) is the induction on the number of fixed leading
vectors. Regularity is used to see that every vector of an orthogonal basis is anisotropic. -/
@[kb "omeara1963" "§58, 58:1, p. 150"]
theorem exists_adjacent_chain_of_orthogonal_bases (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (X Y : Basis (Fin n) F V) (hX : IsOrthogonalBasis Q X) (hY : IsOrthogonalBasis Q Y) :
    ∃ (k : ℕ) (Z : Fin (k + 1) → Basis (Fin n) F V), Z 0 = X ∧ Z (Fin.last k) = Y ∧
      (∀ m, IsOrthogonalBasis Q (Z m)) ∧
      ∀ m : Fin k, AdjacentChange (Z m.castSucc) (Z m.succ) := by
  have hn : n = finrank F V := by rw [finrank_eq_card_basis X, Fintype.card_fin]
  have hXa := isOrthAniso_basis hQ X hX
  have hYa := isOrthAniso_basis hQ Y hY
  have hch := chain_of_isOrthAniso hQ hn n 0 (by omega) X Y hXa hYa (fun j hj => by omega)
  have key : ∀ f : Fin n → V, Relation.ReflTransGen (Step Q 0) (⇑X) f →
      ∃ B : Basis (Fin n) F V, ⇑B = f ∧ Relation.ReflTransGen (fun B C : Basis (Fin n) F V =>
        IsOrthogonalBasis Q B ∧ IsOrthogonalBasis Q C ∧ AdjacentChange B C) X B := by
    intro f hf
    induction hf with
    | refl => exact ⟨X, rfl, Relation.ReflTransGen.refl⟩
    | tail _ hst ih =>
      rename_i g f'
      obtain ⟨B, hB, hBch⟩ := ih
      obtain ⟨hg, hf', i, _, hi⟩ := hst
      refine ⟨basisOfIsOrthAniso hf' hn, coe_basisOfIsOrthAniso hf' hn, hBch.tail ⟨?_, ?_, i, ?_⟩⟩
      · intro a b hab
        have := hg.orth a b hab
        rwa [← hB] at this
      · intro a b hab
        have := hf'.orth a b hab
        rwa [← coe_basisOfIsOrthAniso hf' hn] at this
      · intro j h1 h2
        rw [congrFun (coe_basisOfIsOrthAniso hf' hn) j, hi j h1 h2, ← hB]
  obtain ⟨B, hB, hBch⟩ := key _ hch
  have hBY : B = Y := DFunLike.coe_injective hB
  subst hBY
  exact exists_chain_of_reflTransGen hBch hX

end Main

namespace Sp58

section Quaternary

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V}

theorem gram_eq_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι F V) :
    gram Q b = LinearMap.BilinForm.toMatrix b (QuadraticMap.associated Q) := by
  ext i j
  simp [gram, LinearMap.BilinForm.toMatrix_apply]

/-- **The discriminant of a regular space is nonzero** (the determinant of the matrix of $B$ in a basis). -/
theorem det_gram_ne_zero (hQ : (QuadraticMap.associated Q).Nondegenerate) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι F V) : (gram Q b).det ≠ 0 := by
  rw [gram_eq_toMatrix]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ

/-- Change of basis: $d(c) = (\det T)^2\, d(b)$ for the change of basis matrix $T$. -/
theorem det_gram_eq_sq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (b c : Basis ι F V) :
    (gram Q c).det = (b.toMatrix c).det ^ 2 * (gram Q b).det := by
  rw [gram_eq_toMatrix, gram_eq_toMatrix,
    ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c (QuadraticMap.associated Q)]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- For an orthogonal anisotropic basis the matrix of $B$ is diagonal, so the discriminant is $\prod_i Q(x_i)$. -/
theorem det_gram_of_isOrthAniso {n : ℕ} {x : Fin n → V} (hx : IsOrthAniso Q x) :
    (gram Q x).det = ∏ i, Q (x i) := by
  have : gram Q x = Matrix.diagonal fun i => Q (x i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [gram]
    · simp [gram, hij, hx.orth i j hij]
  rw [this, Matrix.det_diagonal]

/-- **A regular plane orthogonal to two orthogonal anisotropic vectors.** In a regular quaternary space, two
orthogonal anisotropic vectors $x, y$ extend to an orthogonal anisotropic basis $(x, y, p_0, p_1)$: the orthogonal
complement $P = \langle x, y\rangle^\perp$ is a regular plane (the restriction of $B$ to the regular subspace
$\langle x, y\rangle$ is nondegenerate, so $V = \langle x, y\rangle \perp P$), and a regular space has an orthogonal
basis of anisotropic vectors. -/
theorem exists_orthogonal_plane (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hdim : finrank F V = 4) {x y : V} (hf2 : IsOrthAniso Q (![x, y] : Fin 2 → V)) :
    ∃ p : Fin 2 → V, IsOrthAniso Q (![x, y, p 0, p 1] : Fin 4 → V) := by
  set B : LinearMap.BilinForm F V := QuadraticMap.associated Q with hB
  have hBs : B.IsSymm := ⟨fun u v => bil_comm Q u v⟩
  have hBr : B.IsRefl := hBs.isRefl
  set U : Submodule F V := Submodule.span F (Set.range (![x, y] : Fin 2 → V)) with hU
  have hUdim : finrank F U = 2 := by
    rw [hU, finrank_span_eq_card hf2.linearIndependent]; simp
  have hUnd : (B.restrict U).Nondegenerate := by
    let bU : Basis (Fin 2) F U := Basis.span hf2.linearIndependent
    have hbU : ∀ i, (bU i : V) = ![x, y] i := fun i =>
      congrArg Subtype.val (Basis.span_apply hf2.linearIndependent i)
    have hO : (B.restrict U).iIsOrtho bU := by
      intro i j hij
      show B (bU i) (bU j) = 0
      rw [hbU, hbU]
      exact hf2.orth i j hij
    refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self _ bU hO).mpr
      fun i => ?_
    show B (bU i) (bU i) ≠ 0
    rw [hbU]
    show bil Q _ _ ≠ 0
    rw [bil_self]
    exact hf2.aniso i
  have hcompl : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hBr hUnd
  set P : Submodule F V := B.orthogonal U with hP
  have hPnd : (B.restrict P).Nondegenerate := by
    rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBr,
      LinearMap.BilinForm.orthogonal_orthogonal hQ hBr U]
    exact hcompl.symm
  have hPdim : finrank F P = 2 := by
    have := LinearMap.BilinForm.finrank_orthogonal hQ U
    rw [hdim, hUdim] at this
    exact this
  obtain ⟨pb, hpb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp (hBs.restrict P))
  obtain ⟨p, hp⟩ : ∃ p : Fin 2 → V, ∀ i, p i = (pb (Fin.cast hPdim.symm i) : V) :=
    ⟨fun i => (pb (Fin.cast hPdim.symm i) : V), fun _ => rfl⟩
  have hpP : ∀ i, p i ∈ P := fun i => by rw [hp]; exact (pb _).2
  have hxp : ∀ i, bil Q x (p i) = 0 := fun i =>
    (hpP i) x (Submodule.subset_span ⟨0, rfl⟩)
  have hyp : ∀ i, bil Q y (p i) = 0 := fun i =>
    (hpP i) y (Submodule.subset_span ⟨1, rfl⟩)
  have hpx : ∀ i, bil Q (p i) x = 0 := fun i => (bil_comm Q _ _).trans (hxp i)
  have hpy : ∀ i, bil Q (p i) y = 0 := fun i => (bil_comm Q _ _).trans (hyp i)
  have hpp : ∀ i j, i ≠ j → bil Q (p i) (p j) = 0 := by
    intro i j hij
    have := hpb (fun h => hij (Fin.cast_injective _ h) : Fin.cast hPdim.symm i ≠ Fin.cast hPdim.symm j)
    rw [hp, hp]
    exact this
  have hpa : ∀ i, Q (p i) ≠ 0 := by
    intro i
    have := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hpb hPnd
      (Fin.cast hPdim.symm i)
    rw [hp]
    intro h
    apply this
    show bil Q _ _ = 0
    rw [bil_self]
    exact h
  have hxy : bil Q x y = 0 := hf2.orth 0 1 (by decide)
  have hyx : bil Q y x = 0 := hf2.orth 1 0 (by decide)
  have hxne : Q x ≠ 0 := hf2.aniso 0
  have hyne : Q y ≠ 0 := hf2.aniso 1
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine ⟨p, ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hxy
    · exact hxp 0
    · exact hxp 1
    · exact hyx
    · exact absurd rfl hij
    · exact hyp 0
    · exact hyp 1
    · exact hpx 0
    · exact hpy 0
    · exact absurd rfl hij
    · exact hpp 0 1 h01
    · exact hpx 1
    · exact hpy 1
    · exact hpp 1 0 h10
    · exact absurd rfl hij
  · fin_cases i
    · exact hxne
    · exact hyne
    · exact hpa 0
    · exact hpa 1

/-- **The core of the proof of 58:7** (O'Meara 1963, p. 153). Let $V$ be a regular quaternary space with
discriminant $d = d(b)$ (the determinant of $(B(b_i, b_j))$ in a basis $b$). If $x, y \in V$ are orthogonal with
$Q(y) = e \ne 0$ and $Q(x) = -de$, then $V$ is isotropic. (The book: $V = \langle e\rangle \perp \langle -de\rangle
\perp P$ for a plane $P$; comparing discriminants, $P$ has discriminant $-1$ modulo squares, so $P$ is a hyperbolic
plane.) Here: the orthogonal anisotropic basis $(x, y, p_0, p_1)$ of `exists_orthogonal_plane` has
$\delta^2 d = (-de)\,e\,c_0c_1$ with $c_i = Q(p_i)$ and $\delta$ the determinant of the change of basis from $b$
(`det_gram_eq_sq_mul`), whence $c_0c_1 = -(\delta/e)^2$ ($d \ne 0$ since $V$ is regular), and
$(\delta/e)\,p_0 + c_0\,p_1$ is isotropic: its value is $c_0\big((\delta/e)^2 + c_0c_1\big) = 0$. -/
theorem exists_isotropic_of_orthogonal_pair (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hdim : finrank F V = 4) (b : Basis (Fin 4) F V) {d : F} (hd : d = (gram Q b).det)
    {x y : V} {e : F} (he : e ≠ 0) (hy : Q y = e) (hx : Q x = -(d * e)) (hxy : bil Q x y = 0) :
    ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  have hd0 : d ≠ 0 := hd ▸ det_gram_ne_zero hQ b
  have hxne : Q x ≠ 0 := by rw [hx]; exact neg_ne_zero.mpr (mul_ne_zero hd0 he)
  have hf2 : IsOrthAniso Q (![x, y] : Fin 2 → V) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hxy
      · exact (bil_comm Q y x).trans hxy
      · exact absurd rfl hij
    · fin_cases i
      · exact hxne
      · show Q y ≠ 0
        rw [hy]; exact he
  obtain ⟨p, hf4⟩ := exists_orthogonal_plane hQ hdim hf2
  have hc0 : Q (p 0) ≠ 0 := hf4.aniso 2
  have hc1 : Q (p 1) ≠ 0 := hf4.aniso 3
  have h01 : bil Q (p 0) (p 1) = 0 := hf4.orth 2 3 (by decide)
  have hn4 : 4 = finrank F V := hdim.symm
  have hdet := det_gram_eq_sq_mul (Q := Q) b (basisOfIsOrthAniso hf4 hn4)
  rw [coe_basisOfIsOrthAniso, det_gram_of_isOrthAniso hf4, ← hd] at hdet
  simp only [Fin.prod_univ_four] at hdet
  have e0 : (![x, y, p 0, p 1] : Fin 4 → V) 0 = x := rfl
  have e1 : (![x, y, p 0, p 1] : Fin 4 → V) 1 = y := rfl
  have e2 : (![x, y, p 0, p 1] : Fin 4 → V) 2 = p 0 := rfl
  have e3 : (![x, y, p 0, p 1] : Fin 4 → V) 3 = p 1 := rfl
  rw [e0, e1, e2, e3, hx, hy] at hdet
  set δ := (b.toMatrix (![x, y, p 0, p 1] : Fin 4 → V)).det with hδ
  have hkey : Q (p 0) * Q (p 1) * (-(e ^ 2)) = δ ^ 2 := by
    apply mul_right_cancel₀ hd0
    linear_combination hdet
  refine ⟨(δ / e) • p 0 + Q (p 0) • p 1, ?_, ?_⟩
  · intro hv
    have h := congrArg (fun v => bil Q v (p 1)) hv
    simp only [bil_add_left, bil_smul_left, h01, bil_self] at h
    rw [show bil Q 0 (p 1) = 0 by simp [bil]] at h
    simp only [mul_zero, zero_add] at h
    exact mul_ne_zero hc0 hc1 h
  · rw [Q_add, Q_smul, Q_smul, bil_smul_left, bil_smul_right, h01]
    field_simp
    linear_combination (-Q (p 0)) * hkey

end Quaternary

section BaseChange

open TensorProduct

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V}
variable {E : Type*} [Field E] [Algebra F E]

/-- The map $V \to E \otimes_F V$, $v \mapsto 1 \otimes v$, is injective (a field extension has an $F$-linear
retraction $E \to F$ of $F \to E$). -/
theorem one_tmul_injective : Function.Injective (fun v : V => (1 : E) ⊗ₜ[F] v) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hg1 : g 1 = 1 := by simpa using LinearMap.congr_fun hg 1
  intro v w h
  have := congrArg (fun z => TensorProduct.lid F V (LinearMap.rTensor V g z)) h
  simpa [hg1] using this

/-- **Every element of $E \otimes_F V$ is $1 \otimes x + r \otimes y$** when $E = F(r)$ is generated by a square root
$r$ of an element $d \in F$: then $E = F + Fr$. -/
theorem exists_eq_tmul_add_tmul {r : E} {d : F} (hr : r ^ 2 = algebraMap F E d)
    (hgen : Algebra.adjoin F {r} = ⊤) (z : E ⊗[F] V) :
    ∃ x y : V, z = (1 : E) ⊗ₜ[F] x + r ⊗ₜ[F] y := by
  have hE : ∀ e : E, ∃ f g : F, e = algebraMap F E f + algebraMap F E g * r := by
    intro e
    have he : e ∈ Algebra.adjoin F {r} := by rw [hgen]; trivial
    induction he using Algebra.adjoin_induction with
    | mem a ha =>
      rw [Set.mem_singleton_iff] at ha
      exact ⟨0, 1, by simp [ha]⟩
    | algebraMap f => exact ⟨f, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨f1, g1, h1⟩ := ha
      obtain ⟨f2, g2, h2⟩ := hb
      exact ⟨f1 + f2, g1 + g2, by rw [h1, h2, map_add, map_add]; ring⟩
    | mul a b _ _ ha hb =>
      obtain ⟨f1, g1, h1⟩ := ha
      obtain ⟨f2, g2, h2⟩ := hb
      refine ⟨f1 * f2 + g1 * g2 * d, f1 * g2 + g1 * f2, ?_⟩
      rw [h1, h2]
      simp only [map_add, map_mul]
      linear_combination (algebraMap F E g1 * algebraMap F E g2) * hr
  refine TensorProduct.inductionOn z (fun e v => ?_) (fun z w hz hw => ?_)
  · obtain ⟨f, g, rfl⟩ := hE e
    refine ⟨f • v, g • v, ?_⟩
    rw [add_tmul, Algebra.algebraMap_eq_smul_one, smul_tmul, ← Algebra.smul_def, smul_tmul]
  · obtain ⟨x1, y1, h1⟩ := hz
    obtain ⟨x2, y2, h2⟩ := hw
    exact ⟨x1 + x2, y1 + y2, by rw [h1, h2, tmul_add, tmul_add]; abel⟩

/-- **The value of the base change on $1 \otimes x + r \otimes y$:**
$Q_E(1 \otimes x + r \otimes y) = Q(x) + 2B(x,y)\,r + Q(y)\,r^2$ (with $F$ embedded in $E$). -/
theorem baseChange_tmul_add (x y : V) (r : E) :
    Q.baseChange E ((1 : E) ⊗ₜ[F] x + r ⊗ₜ[F] y) =
      algebraMap F E (Q x) + algebraMap F E (2 * bil Q x y) * r + algebraMap F E (Q y) * r ^ 2 := by
  have : Invertible (2 : E) := (Invertible.map (algebraMap F E) 2).copy 2 (map_ofNat _ _).symm
  have hpol := congrArg (fun B => B ((1 : E) ⊗ₜ[F] x) (r ⊗ₜ[F] y))
    (QuadraticForm.polarBilin_baseChange (A := E) Q)
  simp only [QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.baseChange_tmul] at hpol
  rw [QuadraticMap.map_add (Q.baseChange E), hpol]
  simp only [QuadraticForm.baseChange_tmul, Algebra.smul_def, QuadraticMap.polar]
  rw [Q_add Q x y]
  have : Q x + 2 * bil Q x y + Q y - Q x - Q y = 2 * bil Q x y := by ring
  rw [this]
  ring

end BaseChange

end Sp58

section Quaternary58

open Sp58 TensorProduct

variable {F : Type*} [Field F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable {Q : QuadraticForm F V}
variable {E : Type*} [Field E] [Algebra F E]

/-- **Proposition 58:7** (O'Meara 1963, §58, p. 153): *$V$ is a regular quaternary space with discriminant $d$, and
$E$ is the field $E = F(\sqrt d)$. Then $V$ is isotropic if and only if $EV$ is isotropic.*

**Formalization.**
* $V$ is regular (`hQ`: the bilinear form $B$ of $Q$ is nondegenerate) and quaternary (`hdim`: $\dim V = 4$).
* The discriminant is $d = \det\big(B(b_i, b_j)\big)$ for a basis $b$ of $V$ (`hd`, with `gram Q b` the matrix of
  $B$ in $b$). O'Meara's $dV$ is only defined modulo squares of $F^\times$; the theorem is stated for every basis
  $b$, and the field $E = F(\sqrt d)$ does not depend on the choice of the representative $d$.
* $E$ is a field extension of $F$ (`[Field E] [Algebra F E]`) generated by a square root $r$ of $d$
  (`hr : r ^ 2 = algebraMap F E d`, `hgen : Algebra.adjoin F {r} = ⊤`), i.e. $E = F(\sqrt d)$ (this includes the case
  that $d$ is a square, where $E = F$).
* $EV$ is the extension of scalars of the quadratic space: $E \otimes_F V$ with the quadratic form
  `Q.baseChange E` (Mathlib), the unique $E$-quadratic form with $Q_E(a \otimes v) = a^2\,Q(v)$; its bilinear form is
  the $E$-linear extension of $B$.
* *Isotropic* means: there is a nonzero vector $v$ with $Q(v) = 0$.

*Proof* (as in the book, with the last step made explicit): $\Rightarrow$ is clear, as $v \mapsto 1 \otimes v$ is
injective. For $\Leftarrow$ suppose $V$ is anisotropic and $x + r y$ (that is, $1 \otimes x + r \otimes y$; every
element of $EV$ has this form, as $E = F + Fr$) is isotropic. If $r \in F$ this gives an isotropic vector of $V$
directly. Otherwise $1, r$ are linearly independent over $F$ and $Q(x) + d\,Q(y) = 0$, $B(x,y) = 0$; anisotropy forces
$e = Q(y) \ne 0$ and $Q(x) = -de$, and `exists_isotropic_of_orthogonal_pair` shows that $V$ is isotropic after all
($V = \langle e\rangle \perp \langle -de\rangle \perp P$, and the discriminant forces $P$ to be a hyperbolic plane).

In the book "$d$ must be a non-square" uses both assumptions, $V$ anisotropic and $EV$ isotropic (if $d$ were a
square, $EV = V$); the formalization makes this explicit by treating the case `r` in the image of $F$ first. -/
@[kb "omeara1963" "§58, 58:7, p. 153"]
theorem isotropic_iff_baseChange_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (hdim : finrank F V = 4) (b : Basis (Fin 4) F V) {d : F} (hd : d = (gram Q b).det)
    (r : E) (hr : r ^ 2 = algebraMap F E d) (hgen : Algebra.adjoin F {r} = ⊤) :
    (∃ v : V, v ≠ 0 ∧ Q v = 0) ↔ ∃ z : E ⊗[F] V, z ≠ 0 ∧ Q.baseChange E z = 0 := by
  constructor
  · rintro ⟨v, hv, hQv⟩
    refine ⟨(1 : E) ⊗ₜ[F] v, fun h => hv (one_tmul_injective (E := E)
      (show (1 : E) ⊗ₜ[F] v = (1 : E) ⊗ₜ[F] (0 : V) by rw [h, tmul_zero])), ?_⟩
    rw [QuadraticForm.baseChange_tmul, hQv]
    simp
  · rintro ⟨z, hz, hQz⟩
    by_contra hV
    push Not at hV
    obtain ⟨x, y, rfl⟩ := exists_eq_tmul_add_tmul hr hgen z
    by_cases hrange : ∃ c : F, algebraMap F E c = r
    · obtain ⟨c, rfl⟩ := hrange
      have hz1 : (1 : E) ⊗ₜ[F] x + algebraMap F E c ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (x + c • y) := by
        rw [Algebra.algebraMap_eq_smul_one, smul_tmul, tmul_add]
      rw [hz1] at hz hQz
      refine hV (x + c • y) (fun h => hz (by rw [h, tmul_zero])) ?_
      rw [QuadraticForm.baseChange_tmul] at hQz
      simpa using hQz
    · push Not at hrange
      rw [baseChange_tmul_add, hr] at hQz
      have h2 : algebraMap F E (Q x + d * Q y) + algebraMap F E (2 * bil Q x y) * r = 0 := by
        rw [map_add, map_mul]
        linear_combination hQz
      have hv : 2 * bil Q x y = 0 := by
        by_contra hv
        have hv' : algebraMap F E (2 * bil Q x y) ≠ 0 := (map_ne_zero _).mpr hv
        apply hrange (-(Q x + d * Q y) / (2 * bil Q x y))
        rw [map_div₀, map_neg, div_eq_iff hv']
        linear_combination -h2
      have hxy : bil Q x y = 0 := (mul_eq_zero.mp hv).resolve_left two_ne_zero
      rw [hv, map_zero, zero_mul, add_zero] at h2
      have hu : Q x + d * Q y = 0 := (map_eq_zero _).mp h2
      by_cases hy0 : Q y = 0
      · have hy : y = 0 := by
          by_contra h
          exact hV y h hy0
        have hx : Q x = 0 := by rw [hy0] at hu; simpa using hu
        have hx0 : x = 0 := by
          by_contra h
          exact hV x h hx
        exact hz (by rw [hx0, hy]; simp)
      · obtain ⟨v, hv0, hQv⟩ := exists_isotropic_of_orthogonal_pair hQ hdim b hd hy0 rfl
          (by linear_combination hu) hxy
        exact hV v hv0 hQv

end Quaternary58
end QuadFormsKB.OMeara
