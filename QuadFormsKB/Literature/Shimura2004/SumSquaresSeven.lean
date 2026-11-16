/-
# $\mathbb Z$-maximal lattices over $\mathbb Z^7$ for the sum of seven squares

Proof of `SumSqMaxOverIntVec 7`: the code of a $\mathbb Z$-maximal lattice $M \supseteq \mathbb Z^7$ (the odd sets of
its vectors, `InCode`) is a maximal doubly even binary code of length $7$, and after a permutation of coordinates it
contains the words $a_0 = \{0,1,2,3\}$, $b_0 = \{0,1,4,5\}$, $c_0 = \{0,2,4,6\}$, hence the code $S_0$ they span (the
$[7,3]$ simplex code). $S_0$ is self-maximal (`S0_selfMax`), so two such lattices are equal (`eq_of_code_ge`).

The normalization is in three steps, each a permutation found from equal fibre sizes of labellings
(`exists_perm_of_fiber`); the finite facts about subsets of $\{0, \dots, 6\}$ are checked by `decide`.
-/
import QuadFormsKB.Literature.Shimura2004.SumSquaresCodes

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices

/-! ### Transport -/

/-- Moving a $\mathbb Z$-maximal lattice over $\mathbb Z^n$ by a permutation of coordinates. -/
theorem transport_perm {n : ℕ} {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1) (σ : Equiv.Perm (Fin n)) :
    IsGMaximal (sosQ n) (Lat.image (permGL σ) M) ∧
      (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ (Lat.image (permGL σ) M).1 ∧
      IsIsometric (sosQ n) M.1 (Lat.image (permGL σ) M).1 ∧
      ∀ T, InCode M.1 (T.map σ.toEmbedding) → InCode (Lat.image (permGL σ) M).1 T :=
  ⟨isGMaximal_image hM (permGL_mem_orth σ), intVec_le_image_perm hZ σ, ⟨permGL σ, permGL_mem_orth σ, rfl⟩,
    fun _ hT => inCode_image_perm σ hT⟩

/-- Fibre condition of `exists_perm_of_fiber` for the labels `lab l` and `lab l0`. -/
def FibOK {n : ℕ} (l l0 : List (Finset (Fin n))) : Prop :=
  (∀ x, (Finset.univ.filter fun y => lab l y = lab l x).card =
      (Finset.univ.filter fun y => lab l0 y = lab l x).card) ∧
    ∀ x, (Finset.univ.filter fun y => lab l y = lab l0 x).card =
      (Finset.univ.filter fun y => lab l0 y = lab l0 x).card

instance {n : ℕ} (l l0 : List (Finset (Fin n))) : Decidable (FibOK l l0) := by
  unfold FibOK; infer_instance

theorem exists_perm_of_fibOK {n : ℕ} {l l0 : List (Finset (Fin n))} (h : FibOK l l0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ x, lab l (σ x) = lab l0 x :=
  exists_perm_of_fiber _ _ h.1 h.2

namespace Seven

/-- $a_0 = \{0,1,2,3\}$. -/
def a0 : Finset (Fin 7) := {0, 1, 2, 3}
/-- $b_0 = \{0,1,4,5\}$. -/
def b0 : Finset (Fin 7) := {0, 1, 4, 5}
/-- $c_0 = \{0,2,4,6\}$. -/
def c0 : Finset (Fin 7) := {0, 2, 4, 6}

/-- **The simplex code** $S_0 = \langle a_0, b_0, c_0\rangle$ (eight words). -/
def S0 : Finset (Finset (Fin 7)) :=
  {∅, a0, b0, c0, symmDiff a0 b0, symmDiff a0 c0, symmDiff b0 c0, symmDiff (symmDiff a0 b0) c0}

set_option maxRecDepth 100000 in
/-- $S_0$ is a maximal doubly even code. -/
theorem S0_selfMax : ∀ T : Finset (Fin 7), 4 ∣ T.card → (∀ U ∈ S0, 4 ∣ (symmDiff T U).card) → T ∈ S0 := by
  decide

set_option maxRecDepth 100000 in
theorem card_cases : ∀ T : Finset (Fin 7), 4 ∣ T.card → T = ∅ ∨ T.card = 4 := by decide

set_option maxRecDepth 100000 in
theorem fib1 : ∀ A : Finset (Fin 7), A.card = 4 → FibOK [A] [a0] := by decide

set_option maxRecDepth 100000 in
theorem step2_cases : ∀ U : Finset (Fin 7), 4 ∣ U.card → 4 ∣ (symmDiff U a0).card →
    U = ∅ ∨ U = a0 ∨ (U.card = 4 ∧ (U ∩ a0).card = 2) := by decide

set_option maxRecDepth 100000 in
theorem fib2 : ∀ B : Finset (Fin 7), B.card = 4 → (B ∩ a0).card = 2 → FibOK [a0, B] [a0, b0] := by decide

set_option maxRecDepth 100000 in
theorem fib3 : ∀ C : Finset (Fin 7), 4 ∣ C.card → 4 ∣ (symmDiff C a0).card → 4 ∣ (symmDiff C b0).card →
    4 ∣ (symmDiff C (symmDiff a0 b0)).card → C ≠ ∅ → C ≠ a0 → C ≠ b0 → C ≠ symmDiff a0 b0 →
    FibOK [a0, b0, C] [a0, b0, c0] := by decide

set_option maxRecDepth 100000 in
theorem a0_card : a0.card = 4 := by decide
set_option maxRecDepth 100000 in
theorem b0_facts : b0.card = 4 ∧ (b0 ∩ a0).card = 2 ∧ 4 ∣ (symmDiff b0 a0).card := by decide
set_option maxRecDepth 100000 in
theorem c0_facts : 4 ∣ c0.card ∧ 4 ∣ (symmDiff c0 a0).card ∧ 4 ∣ (symmDiff c0 b0).card ∧
    4 ∣ (symmDiff c0 (symmDiff a0 b0)).card ∧ c0 ≠ ∅ ∧ c0 ≠ a0 ∧ c0 ≠ b0 ∧ c0 ≠ symmDiff a0 b0 := by decide

/-- **Normal form**: a $\mathbb Z$-maximal lattice over $\mathbb Z^7$ is isometric (by a permutation of
coordinates) to one whose code contains $S_0$. -/
theorem normal_form {M : Lat ℚ 7} (hM : IsGMaximal (sosQ 7) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 7 → ℚ)) ≤ M.1) :
    ∃ M₃ : Lat ℚ 7, IsGMaximal (sosQ 7) M₃ ∧ (intVec : Submodule (𝓞 ℚ) (Fin 7 → ℚ)) ≤ M₃.1 ∧
      IsIsometric (sosQ 7) M.1 M₃.1 ∧ ∀ U ∈ S0, InCode M₃.1 U := by
  -- step 1: a word of weight 4, moved to `a0`
  have hN := intNorm_of_isGMaximal hM
  obtain ⟨A, hA, hA4⟩ : ∃ A, InCode M.1 A ∧ A.card = 4 := by
    by_contra hno
    push Not at hno
    have hall : ∀ U, InCode M.1 U → U = ∅ := fun U hU =>
      (card_cases U (hU.four_dvd hN hZ)).resolve_right (hno U hU)
    have ha := inCode_of_isGMaximal hM hZ (T := a0) fun U hU => by
      rw [hall U hU]; decide
    exact hno a0 ha a0_card
  obtain ⟨σ₁, hσ₁⟩ := exists_perm_of_fibOK (fib1 A hA4)
  obtain ⟨hM₁, hZ₁, hi₁, ht₁⟩ := transport_perm hM hZ σ₁
  set M₁ := Lat.image (permGL σ₁) M
  have hN₁ := intNorm_of_isGMaximal hM₁
  have ha₁ : InCode M₁.1 a0 := ht₁ a0 (by rw [show a0.map σ₁.toEmbedding = A from map_eq_of_lab hσ₁ 0 (by simp) (by simp)]; exact hA)
  -- step 2: a second word `B` meeting `a0` in two points, moved to `b0`
  obtain ⟨B, hB, hB4, hBa⟩ : ∃ B, InCode M₁.1 B ∧ B.card = 4 ∧ (B ∩ a0).card = 2 := by
    by_contra hno
    push Not at hno
    have hall : ∀ U, InCode M₁.1 U → U = ∅ ∨ U = a0 := by
      intro U hU
      rcases step2_cases U (hU.four_dvd hN₁ hZ₁) ((hU.symmDiff hN₁ hZ₁ ha₁).four_dvd hN₁ hZ₁) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h.2 (hno U hU h.1)
    have hb := inCode_of_isGMaximal hM₁ hZ₁ (T := b0) fun U hU => by
      rcases hall U hU with rfl | rfl
      · decide
      · decide
    exact hno b0 hb b0_facts.1 b0_facts.2.1
  obtain ⟨σ₂, hσ₂⟩ := exists_perm_of_fibOK (fib2 B hB4 hBa)
  obtain ⟨hM₂, hZ₂, hi₂, ht₂⟩ := transport_perm hM₁ hZ₁ σ₂
  set M₂ := Lat.image (permGL σ₂) M₁
  have hN₂ := intNorm_of_isGMaximal hM₂
  have ha₂ : InCode M₂.1 a0 := ht₂ a0 (by rw [show a0.map σ₂.toEmbedding = a0 from map_eq_of_lab hσ₂ 0 (by simp) (by simp)]; exact ha₁)
  have hb₂ : InCode M₂.1 b0 := ht₂ b0 (by rw [show b0.map σ₂.toEmbedding = B from map_eq_of_lab hσ₂ 1 (by simp) (by simp)]; exact hB)
  -- step 3: a word `C` outside ⟨a0, b0⟩, moved to `c0`
  obtain ⟨C, hC, hC0, hCa, hCb, hCab⟩ :
      ∃ C, InCode M₂.1 C ∧ C ≠ ∅ ∧ C ≠ a0 ∧ C ≠ b0 ∧ C ≠ symmDiff a0 b0 := by
    by_contra hno
    push Not at hno
    have hc := inCode_of_isGMaximal hM₂ hZ₂ (T := c0) fun U hU => by
      by_cases h0 : U = ∅
      · subst h0; decide
      by_cases h1 : U = a0
      · subst h1; decide
      by_cases h2 : U = b0
      · subst h2; decide
      rw [hno U hU (Finset.nonempty_iff_ne_empty.mpr h0) h1 h2]; decide
    exact c0_facts.2.2.2.2.2.2.2 (hno c0 hc (Finset.nonempty_iff_ne_empty.mpr c0_facts.2.2.2.2.1) c0_facts.2.2.2.2.2.1 c0_facts.2.2.2.2.2.2.1)
  have hab₂ := hb₂.symmDiff hN₂ hZ₂ ha₂ |> fun h => by rwa [symmDiff_comm] at h
  obtain ⟨σ₃, hσ₃⟩ := exists_perm_of_fibOK (fib3 C (hC.four_dvd hN₂ hZ₂)
    ((hC.symmDiff hN₂ hZ₂ ha₂).four_dvd hN₂ hZ₂) ((hC.symmDiff hN₂ hZ₂ hb₂).four_dvd hN₂ hZ₂)
    ((hC.symmDiff hN₂ hZ₂ hab₂).four_dvd hN₂ hZ₂) hC0 hCa hCb hCab)
  obtain ⟨hM₃, hZ₃, hi₃, ht₃⟩ := transport_perm hM₂ hZ₂ σ₃
  set M₃ := Lat.image (permGL σ₃) M₂
  have hN₃ := intNorm_of_isGMaximal hM₃
  have ha₃ : InCode M₃.1 a0 := ht₃ a0 (by rw [show a0.map σ₃.toEmbedding = a0 from map_eq_of_lab hσ₃ 0 (by simp) (by simp)]; exact ha₂)
  have hb₃ : InCode M₃.1 b0 := ht₃ b0 (by rw [show b0.map σ₃.toEmbedding = b0 from map_eq_of_lab hσ₃ 1 (by simp) (by simp)]; exact hb₂)
  have hc₃ : InCode M₃.1 c0 := ht₃ c0 (by rw [show c0.map σ₃.toEmbedding = C from map_eq_of_lab hσ₃ 2 (by simp) (by simp)]; exact hC)
  refine ⟨M₃, hM₃, hZ₃, IsIsometric.trans _ (IsIsometric.trans _ hi₁ hi₂) hi₃, ?_⟩
  have hab := ha₃.symmDiff hN₃ hZ₃ hb₃
  intro U hU
  simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hU
  rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inCode_empty hZ₃
  · exact ha₃
  · exact hb₃
  · exact hc₃
  · exact hab
  · exact ha₃.symmDiff hN₃ hZ₃ hc₃
  · exact hb₃.symmDiff hN₃ hZ₃ hc₃
  · exact hab.symmDiff hN₃ hZ₃ hc₃

end Seven

/-- **`SumSqMaxOverIntVec 7`**: two $\mathbb Z$-maximal lattices over $\mathbb Z^7$ for the sum of seven squares are
isometric (each is $\mathbb Z^7 + \tfrac12 C$ for a $[7,3]$ simplex code $C$, and these codes differ by a permutation
of coordinates). -/
theorem sumSqMaxOverIntVec_seven : SumSqMaxOverIntVec 7 := by
  refine ⟨fun M M' hM hM' hZ hZ' => ?_⟩
  obtain ⟨M₃, hM₃, hZ₃, hi, hS⟩ := Seven.normal_form hM hZ
  obtain ⟨M₃', hM₃', hZ₃', hi', hS'⟩ := Seven.normal_form hM' hZ'
  have h := eq_of_code_ge hM₃ hM₃' hZ₃ hZ₃' Seven.S0 Seven.S0_selfMax hS hS'
  exact IsIsometric.trans _ (IsIsometric.trans _ hi h) hi'.symm

end QuadFormsKB.Shimura2004
