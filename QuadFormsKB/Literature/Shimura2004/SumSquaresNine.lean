/-
# $\mathbb Z$-maximal lattices over $\mathbb Z^9$ for the sum of nine squares

Proof of `SumSqMaxOverIntVec 9`: after a permutation of coordinates, the code of a $\mathbb Z$-maximal lattice
$M \supseteq \mathbb Z^9$ (the odd sets of its vectors, `InCode`) contains $a_0 = \{0,1,2,3\}$, $b_0 = \{0,1,4,5\}$,
$c_0 = \{0,2,4,6\}$ and $d_0 = \{0, \dots, 7\}$, hence the extended Hamming code $S_0$ of length $8$ on the coordinates
$0, \dots, 7$ (sixteen words); $S_0$ is a maximal doubly even code of length $9$ (`S0_selfMax`), so two such lattices
are equal (`eq_of_code_ge`).

Each normalization step finds a code word of a prescribed type by maximality (if every code word lay in a small
explicit set $W$, a word compatible with all of $W$ would be a code word, a contradiction) and moves it into place by a
permutation found from equal fibre sizes (`exists_perm_of_fibOK`). The finite facts about subsets of
$\{0, \dots, 8\}$ are checked by `decide`.
-/
import QuadFormsKB.Literature.Shimura2004.SumSquaresSeven

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices

/-- If every code word of a $\mathbb Z$-maximal $M \supseteq \mathbb Z^n$ lies in $W$, then every $T$ with
$4 \mid \#(U \mathbin\triangle T)$ for all $U \in W$ is a code word. -/
theorem inCode_of_subset {n : ℕ} {M : Lat ℚ n} (hM : IsGMaximal (sosQ n) M)
    (hZ : (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ≤ M.1) (W : Finset (Finset (Fin n)))
    (hW : ∀ U, InCode M.1 U → U ∈ W) {T : Finset (Fin n)} (hT : ∀ U ∈ W, 4 ∣ (symmDiff U T).card) :
    InCode M.1 T :=
  inCode_of_isGMaximal hM hZ fun U hU => hT U (hW U hU)

namespace Nine

/-- $a_0 = \{0,1,2,3\}$. -/
def a0 : Finset (Fin 9) := {0, 1, 2, 3}
/-- $b_0 = \{0,1,4,5\}$. -/
def b0 : Finset (Fin 9) := {0, 1, 4, 5}
/-- $c_0 = \{0,2,4,6\}$. -/
def c0 : Finset (Fin 9) := {0, 2, 4, 6}
/-- $d_0 = \{0, \dots, 7\}$. -/
def d0 : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 6, 7}

/-- $\langle a_0, b_0\rangle$. -/
def W2 : Finset (Finset (Fin 9)) := {∅, a0, b0, symmDiff a0 b0}

/-- $\langle a_0, b_0, c_0\rangle$. -/
def W3 : Finset (Finset (Fin 9)) :=
  {∅, a0, b0, c0, symmDiff a0 b0, symmDiff a0 c0, symmDiff b0 c0, symmDiff (symmDiff a0 b0) c0}

/-- **The extended Hamming code** on the coordinates $0, \dots, 7$ (sixteen words). -/
def S0 : Finset (Finset (Fin 9)) :=
  {∅, {0, 1, 2, 3}, {0, 1, 4, 5}, {0, 1, 6, 7}, {0, 2, 4, 6}, {0, 2, 5, 7}, {0, 3, 4, 7}, {0, 3, 5, 6},
    {1, 2, 4, 7}, {1, 2, 5, 6}, {1, 3, 4, 6}, {1, 3, 5, 7}, {2, 3, 4, 5}, {2, 3, 6, 7}, {4, 5, 6, 7},
    {0, 1, 2, 3, 4, 5, 6, 7}}

/-- Words of type $\alpha$: four points, two of them in $a_0$. -/
abbrev IsA (B : Finset (Fin 9)) : Prop := B.card = 4 ∧ (B ∩ a0).card = 2

/-- Words of type $\beta$: four points outside $a_0$. -/
abbrev IsB (D : Finset (Fin 9)) : Prop := D.card = 4 ∧ D ∩ a0 = ∅

/-- Words of type $\gamma$ (the target of step 3): one point in each of $a_0 \cap b_0$, $a_0 \setminus b_0$,
$b_0 \setminus a_0$ and the rest. -/
abbrev IsC (C : Finset (Fin 9)) : Prop :=
  C.card = 4 ∧ (C ∩ a0).card = 2 ∧ (C ∩ b0).card = 2 ∧ (C ∩ (a0 ∩ b0)).card = 1

/-- Words of type $\delta$: four points, two of them in $\{6, 7, 8\}$, compatible with $a_0$ and $b_0$. -/
abbrev IsD (D : Finset (Fin 9)) : Prop :=
  D.card = 4 ∧ (D ∩ {6, 7, 8}).card = 2 ∧ 4 ∣ (symmDiff D a0).card ∧ 4 ∣ (symmDiff D b0).card

/-- $\langle a_0, b_0, D\rangle$. -/
def W2D (D : Finset (Fin 9)) : Finset (Finset (Fin 9)) :=
  {∅, a0, b0, symmDiff a0 b0, D, symmDiff D a0, symmDiff D b0, symmDiff D (symmDiff a0 b0)}

/-! ### Finite facts -/

set_option maxRecDepth 100000

/-- $S_0$ is a maximal doubly even code of length $9$. -/
theorem S0_selfMax : ∀ T : Finset (Fin 9), 4 ∣ T.card → (∀ U ∈ S0, 4 ∣ (symmDiff T U).card) → T ∈ S0 := by
  decide

theorem L1a : ∀ U : Finset (Fin 9), 4 ∣ U.card → U.card ≠ 4 → U = ∅ ∨ U.card = 8 := by decide

theorem L1b : ∀ E : Finset (Fin 9), E.card = 8 → ∀ E' : Finset (Fin 9), E'.card = 8 →
    4 ∣ (symmDiff E E').card → E = E' := by decide

theorem L1c : ∀ E : Finset (Fin 9), E.card = 8 → ∃ F : Finset (Fin 9), F.card = 4 ∧ 4 ∣ (symmDiff E F).card := by
  decide

theorem fib1 : ∀ A : Finset (Fin 9), A.card = 4 → FibOK [A] [a0] := by decide

theorem L2a : ∀ U : Finset (Fin 9), 4 ∣ U.card → 4 ∣ (symmDiff U a0).card → ¬ IsA U →
    U = ∅ ∨ U = a0 ∨ IsB U ∨ IsB (symmDiff U a0) := by decide

theorem L2b : ∀ D : Finset (Fin 9), IsB D → ∀ U : Finset (Fin 9), 4 ∣ U.card → 4 ∣ (symmDiff U a0).card →
    4 ∣ (symmDiff U D).card → ¬ IsA U → U ∈ ({∅, a0, D, symmDiff D a0} : Finset (Finset (Fin 9))) := by
  decide

theorem L2c : ∀ D : Finset (Fin 9), IsB D → ∃ T : Finset (Fin 9), IsA T ∧
    ∀ U ∈ ({∅, a0, D, symmDiff D a0} : Finset (Finset (Fin 9))), 4 ∣ (symmDiff U T).card := by
  decide

theorem fib2 : ∀ B : Finset (Fin 9), IsA B → FibOK [a0, B] [a0, b0] := by decide

theorem L3a : ∀ U : Finset (Fin 9), 4 ∣ U.card → 4 ∣ (symmDiff U a0).card → 4 ∣ (symmDiff U b0).card →
    ¬ IsC U → U ∈ W2 ∨ IsD U ∨ IsD (symmDiff U a0) := by decide

theorem L3b : ∀ D : Finset (Fin 9), IsD D → ∀ U : Finset (Fin 9), 4 ∣ U.card → 4 ∣ (symmDiff U a0).card →
    4 ∣ (symmDiff U b0).card → 4 ∣ (symmDiff U D).card → ¬ IsC U → U ∈ W2D D := by decide

theorem L3c : ∀ D : Finset (Fin 9), IsD D → ∃ T : Finset (Fin 9), IsC T ∧
    ∀ U ∈ W2D D, 4 ∣ (symmDiff U T).card := by decide

theorem fib3 : ∀ C : Finset (Fin 9), IsC C → FibOK [a0, b0, C] [a0, b0, c0] := by decide

theorem L4a : ∀ U : Finset (Fin 9), (∀ w ∈ W3, 4 ∣ (symmDiff U w).card) → U ∉ W3 →
    (7 ∈ U ∧ 8 ∉ U) ∨ (8 ∈ U ∧ 7 ∉ U) := by decide

theorem L4b : ∀ U : Finset (Fin 9), (∀ w ∈ W3, 4 ∣ (symmDiff U w).card) → U ∉ W3 → 7 ∈ U →
    ∃ w ∈ W3, symmDiff U w = d0 := by decide

theorem facts : a0.card = 4 ∧ IsA b0 ∧ 4 ∣ (symmDiff a0 b0).card ∧ IsC c0 ∧ (∀ U ∈ W2, 4 ∣ (symmDiff U c0).card) ∧
    (∀ U ∈ W3, 4 ∣ (symmDiff U d0).card) ∧ d0 ∉ W3 := by decide

/-- The transposition of the coordinates $7$ and $8$ fixes $a_0$, $b_0$, $c_0$. -/
theorem swap78 : a0.map (Equiv.swap (7 : Fin 9) 8).toEmbedding = a0 ∧
    b0.map (Equiv.swap (7 : Fin 9) 8).toEmbedding = b0 ∧ c0.map (Equiv.swap (7 : Fin 9) 8).toEmbedding = c0 ∧
    ∀ U : Finset (Fin 9), 8 ∈ U → 7 ∉ U → 7 ∈ U.map (Equiv.swap (7 : Fin 9) 8).toEmbedding := by decide


theorem map_swap78_twice (U : Finset (Fin 9)) :
    (U.map (Equiv.swap (7 : Fin 9) 8).toEmbedding).map (Equiv.swap (7 : Fin 9) 8).toEmbedding = U := by
  ext x; simp

/-! ### Normalization -/

variable {M : Lat ℚ 9}

/-- Code words of a lattice over $\mathbb Z^9$ with integral norm are compatible. -/
theorem compat (hN : IntNorm M.1) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1) {U V : Finset (Fin 9)}
    (hU : InCode M.1 U) (hV : InCode M.1 V) : 4 ∣ (symmDiff U V).card :=
  (hU.symmDiff hN hZ hV).four_dvd hN hZ

/-- **Step 1**: a code word of weight $4$. -/
theorem step1 (hM : IsGMaximal (sosQ 9) M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1) :
    ∃ A, InCode M.1 A ∧ A.card = 4 := by
  have hN := intNorm_of_isGMaximal hM
  by_contra hno
  push Not at hno
  have h08 : ∀ U, InCode M.1 U → U = ∅ ∨ U.card = 8 := fun U hU =>
    L1a U (hU.four_dvd hN hZ) (hno U hU)
  by_cases hE : ∃ E, InCode M.1 E ∧ E.card = 8
  · obtain ⟨E, hE, hE8⟩ := hE
    have hW : ∀ U, InCode M.1 U → U ∈ ({∅, E} : Finset (Finset (Fin 9))) := by
      intro U hU
      rcases h08 U hU with h | h
      · simp [h]
      · simp [L1b E hE8 U h (compat hN hZ hE hU)]
    obtain ⟨F, hF4, hEF⟩ := L1c E hE8
    have hF := inCode_of_subset hM hZ _ hW (T := F) (by
      intro U hU
      simp only [Finset.mem_insert, Finset.mem_singleton] at hU
      rcases hU with rfl | rfl
      · have e : symmDiff (∅ : Finset (Fin 9)) F = F := by ext; simp [Finset.mem_symmDiff]
        rw [e, hF4]
      · exact hEF)
    exact hno F hF hF4
  · push Not at hE
    have hW : ∀ U, InCode M.1 U → U ∈ ({∅} : Finset (Finset (Fin 9))) := fun U hU => by
      rcases h08 U hU with h | h
      · simp [h]
      · exact absurd h (hE U hU)
    have ha := inCode_of_subset hM hZ _ hW (T := a0) (by
      intro U hU
      rw [Finset.mem_singleton] at hU
      subst hU
      decide)
    exact hno a0 ha facts.1

/-- **Step 2**: if $a_0$ is a code word, there is a code word of type $\alpha$. -/
theorem step2 (hM : IsGMaximal (sosQ 9) M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1)
    (ha : InCode M.1 a0) : ∃ B, InCode M.1 B ∧ IsA B := by
  have hN := intNorm_of_isGMaximal hM
  by_contra hno
  push Not at hno
  by_cases hsub : ∀ U, InCode M.1 U → U = ∅ ∨ U = a0
  · have hb := inCode_of_subset hM hZ {∅, a0} (fun U hU => by
      rcases hsub U hU with rfl | rfl <;> simp) (T := b0) (by
        intro U hU
        simp only [Finset.mem_insert, Finset.mem_singleton] at hU
        rcases hU with rfl | rfl
        · decide
        · exact facts.2.2.1)
    exact hno b0 hb facts.2.1
  push Not at hsub
  obtain ⟨U, hU, hU0, hUa⟩ := hsub
  obtain ⟨D, hD, hDB⟩ : ∃ D, InCode M.1 D ∧ IsB D := by
    rcases L2a U (hU.four_dvd hN hZ) (compat hN hZ hU ha) (hno U hU) with h | h | h | h
    · exact absurd h (Finset.nonempty_iff_ne_empty.mp hU0)
    · exact absurd h hUa
    · exact ⟨U, hU, h⟩
    · exact ⟨_, hU.symmDiff hN hZ ha, h⟩
  have hW : ∀ V, InCode M.1 V → V ∈ ({∅, a0, D, symmDiff D a0} : Finset (Finset (Fin 9))) := fun V hV =>
    L2b D hDB V (hV.four_dvd hN hZ) (compat hN hZ hV ha) (compat hN hZ hV hD) (hno V hV)
  obtain ⟨T, hTA, hT⟩ := L2c D hDB
  exact hno T (inCode_of_subset hM hZ _ hW hT) hTA

/-- **Step 3**: if $a_0$, $b_0$ are code words, there is a code word of type $\gamma$. -/
theorem step3 (hM : IsGMaximal (sosQ 9) M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1)
    (ha : InCode M.1 a0) (hb : InCode M.1 b0) : ∃ C, InCode M.1 C ∧ IsC C := by
  have hN := intNorm_of_isGMaximal hM
  have hab := ha.symmDiff hN hZ hb
  by_contra hno
  push Not at hno
  by_cases hsub : ∀ U, InCode M.1 U → U ∈ W2
  · have hc := inCode_of_subset hM hZ W2 hsub (T := c0) facts.2.2.2.2.1
    exact hno c0 hc facts.2.2.2.1
  push Not at hsub
  obtain ⟨U, hU, hUW⟩ := hsub
  obtain ⟨D, hD, hDD⟩ : ∃ D, InCode M.1 D ∧ IsD D := by
    rcases L3a U (hU.four_dvd hN hZ) (compat hN hZ hU ha) (compat hN hZ hU hb) (hno U hU) with h | h | h
    · exact absurd h hUW
    · exact ⟨U, hU, h⟩
    · exact ⟨_, hU.symmDiff hN hZ ha, h⟩
  have hW : ∀ V, InCode M.1 V → V ∈ W2D D := fun V hV =>
    L3b D hDD V (hV.four_dvd hN hZ) (compat hN hZ hV ha) (compat hN hZ hV hb) (compat hN hZ hV hD) (hno V hV)
  obtain ⟨T, hTC, hT⟩ := L3c D hDD
  exact hno T (inCode_of_subset hM hZ _ hW hT) hTC

/-- The words of $W_3 = \langle a_0, b_0, c_0\rangle$ are code words when $a_0, b_0, c_0$ are. -/
theorem W3_inCode (hN : IntNorm M.1) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1)
    (ha : InCode M.1 a0) (hb : InCode M.1 b0) (hc : InCode M.1 c0) : ∀ w ∈ W3, InCode M.1 w := by
  have hab := ha.symmDiff hN hZ hb
  intro w hw
  simp only [W3, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inCode_empty hZ
  · exact ha
  · exact hb
  · exact hc
  · exact hab
  · exact ha.symmDiff hN hZ hc
  · exact hb.symmDiff hN hZ hc
  · exact hab.symmDiff hN hZ hc

/-- **Step 4**: if $a_0, b_0, c_0$ are code words, there is a code word outside $W_3$, containing $7$ or $8$. -/
theorem step4 (hM : IsGMaximal (sosQ 9) M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1)
    (ha : InCode M.1 a0) (hb : InCode M.1 b0) (hc : InCode M.1 c0) :
    ∃ U, InCode M.1 U ∧ (∀ w ∈ W3, 4 ∣ (symmDiff U w).card) ∧ U ∉ W3 := by
  have hN := intNorm_of_isGMaximal hM
  have hW3 := W3_inCode hN hZ ha hb hc
  by_contra hno
  push Not at hno
  have hsub : ∀ U, InCode M.1 U → U ∈ W3 := fun U hU =>
    hno U hU fun w hw => compat hN hZ hU (hW3 w hw)
  exact facts.2.2.2.2.2.2 (hsub d0 (inCode_of_subset hM hZ W3 hsub facts.2.2.2.2.2.1))

/-- **Normal form**: a $\mathbb Z$-maximal lattice over $\mathbb Z^9$ is isometric (by a permutation of
coordinates) to one whose code contains $S_0$. -/
theorem normal_form (hM : IsGMaximal (sosQ 9) M) (hZ : (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M.1) :
    ∃ M₄ : Lat ℚ 9, IsGMaximal (sosQ 9) M₄ ∧ (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M₄.1 ∧
      IsIsometric (sosQ 9) M.1 M₄.1 ∧ ∀ U ∈ S0, InCode M₄.1 U := by
  -- step 1
  obtain ⟨A, hA, hA4⟩ := step1 hM hZ
  obtain ⟨σ₁, hσ₁⟩ := exists_perm_of_fibOK (fib1 A hA4)
  obtain ⟨hM₁, hZ₁, hi₁, ht₁⟩ := transport_perm hM hZ σ₁
  set M₁ := Lat.image (permGL σ₁) M
  have ha₁ : InCode M₁.1 a0 :=
    ht₁ a0 (by rw [show a0.map σ₁.toEmbedding = A from map_eq_of_lab hσ₁ 0 (by simp) (by simp)]; exact hA)
  -- step 2
  obtain ⟨B, hB, hBA⟩ := step2 hM₁ hZ₁ ha₁
  obtain ⟨σ₂, hσ₂⟩ := exists_perm_of_fibOK (fib2 B hBA)
  obtain ⟨hM₂, hZ₂, hi₂, ht₂⟩ := transport_perm hM₁ hZ₁ σ₂
  set M₂ := Lat.image (permGL σ₂) M₁
  have ha₂ : InCode M₂.1 a0 :=
    ht₂ a0 (by rw [show a0.map σ₂.toEmbedding = a0 from map_eq_of_lab hσ₂ 0 (by simp) (by simp)]; exact ha₁)
  have hb₂ : InCode M₂.1 b0 :=
    ht₂ b0 (by rw [show b0.map σ₂.toEmbedding = B from map_eq_of_lab hσ₂ 1 (by simp) (by simp)]; exact hB)
  -- step 3
  obtain ⟨C, hC, hCC⟩ := step3 hM₂ hZ₂ ha₂ hb₂
  obtain ⟨σ₃, hσ₃⟩ := exists_perm_of_fibOK (fib3 C hCC)
  obtain ⟨hM₃, hZ₃, hi₃, ht₃⟩ := transport_perm hM₂ hZ₂ σ₃
  set M₃ := Lat.image (permGL σ₃) M₂
  have ha₃ : InCode M₃.1 a0 :=
    ht₃ a0 (by rw [show a0.map σ₃.toEmbedding = a0 from map_eq_of_lab hσ₃ 0 (by simp) (by simp)]; exact ha₂)
  have hb₃ : InCode M₃.1 b0 :=
    ht₃ b0 (by rw [show b0.map σ₃.toEmbedding = b0 from map_eq_of_lab hσ₃ 1 (by simp) (by simp)]; exact hb₂)
  have hc₃ : InCode M₃.1 c0 :=
    ht₃ c0 (by rw [show c0.map σ₃.toEmbedding = C from map_eq_of_lab hσ₃ 2 (by simp) (by simp)]; exact hC)
  -- step 4: a word containing `7` (after possibly swapping `7` and `8`), then `d0`
  obtain ⟨U, hU, hUc, hUW⟩ := step4 hM₃ hZ₃ ha₃ hb₃ hc₃
  have key : ∀ (M₄ : Lat ℚ 9), IsGMaximal (sosQ 9) M₄ → (intVec : Submodule (𝓞 ℚ) (Fin 9 → ℚ)) ≤ M₄.1 →
      InCode M₄.1 a0 → InCode M₄.1 b0 → InCode M₄.1 c0 → ∀ U', InCode M₄.1 U' → U' ∉ W3 → 7 ∈ U' →
      ∀ V ∈ S0, InCode M₄.1 V := by
    intro M₄ hM₄ hZ₄ ha hb hc U' hU' hU'W h7
    have hN₄ := intNorm_of_isGMaximal hM₄
    have hW3 := W3_inCode hN₄ hZ₄ ha hb hc
    obtain ⟨w, hw, hwd⟩ := L4b U' (fun w hw => compat hN₄ hZ₄ hU' (hW3 w hw)) hU'W h7
    have hd : InCode M₄.1 d0 := hwd ▸ hU'.symmDiff hN₄ hZ₄ (hW3 w hw)
    intro V hV
    -- every word of `S0` is a word of `W3` or `d0` plus one
    have hS0 : ∀ V ∈ S0, V ∈ W3 ∨ ∃ w ∈ W3, V = symmDiff d0 w := by decide
    rcases hS0 V hV with h | ⟨w', hw', rfl⟩
    · exact hW3 V h
    · exact hd.symmDiff hN₄ hZ₄ (hW3 w' hw')
  rcases L4a U hUc hUW with ⟨h7, -⟩ | ⟨h8, h7⟩
  · exact ⟨M₃, hM₃, hZ₃, IsIsometric.trans _ (IsIsometric.trans _ hi₁ hi₂) hi₃,
      key M₃ hM₃ hZ₃ ha₃ hb₃ hc₃ U hU hUW h7⟩
  · let τ : Equiv.Perm (Fin 9) := Equiv.swap 7 8
    obtain ⟨hM₄, hZ₄, hi₄, ht₄⟩ := transport_perm hM₃ hZ₃ τ
    obtain ⟨sa, sb, sc, s7⟩ := swap78
    refine ⟨_, hM₄, hZ₄, IsIsometric.trans _ (IsIsometric.trans _ (IsIsometric.trans _ hi₁ hi₂) hi₃) hi₄,
      key _ hM₄ hZ₄ (ht₄ a0 (by rw [sa]; exact ha₃)) (ht₄ b0 (by rw [sb]; exact hb₃))
        (ht₄ c0 (by rw [sc]; exact hc₃)) (U.map τ.toEmbedding) (ht₄ _ (by rw [map_swap78_twice]; exact hU))
        ?_ (s7 U h8 h7)⟩
    intro hmem
    apply hUW
    have hW3τ : ∀ w ∈ W3, w.map τ.toEmbedding = w := by decide
    have := hW3τ _ hmem
    rw [map_swap78_twice] at this
    rw [this]; exact hmem

end Nine

/-- **`SumSqMaxOverIntVec 9`**: two $\mathbb Z$-maximal lattices over $\mathbb Z^9$ for the sum of nine squares are
isometric (each is $\mathbb Z^9 + \tfrac12 C$ with $C$ an extended Hamming code of length $8$ on eight of the nine
coordinates, and these codes differ by a permutation of coordinates). -/
theorem sumSqMaxOverIntVec_nine : SumSqMaxOverIntVec 9 := by
  refine ⟨fun M M' hM hM' hZ hZ' => ?_⟩
  obtain ⟨M₄, hM₄, hZ₄, hi, hS⟩ := Nine.normal_form hM hZ
  obtain ⟨M₄', hM₄', hZ₄', hi', hS'⟩ := Nine.normal_form hM' hZ'
  have h := eq_of_code_ge hM₄ hM₄' hZ₄ hZ₄' Nine.S0 Nine.S0_selfMax hS hS'
  exact IsIsometric.trans _ (IsIsometric.trans _ hi h) hi'.symm

end QuadFormsKB.Shimura2004
