/-
# Cassels, Chapter 7, Lemma 3.2: triangular bases of a sublattice

**Setting.** $I$ is a principal ideal domain; the lattice $\Lambda$ with basis $b_0, \dots, b_{n-1}$ is an $I$-module
`Λ` with a basis `b : Basis (Fin n) I Λ`, and a sublattice $\Gamma$ is a submodule `Γ : Submodule I Λ` containing
$d\Lambda$ for some $d \ne 0$ (for lattices $\Gamma \subseteq \Lambda$ spanning the same $k$-space this holds by
Lemma 3.1, `exists_det_mem_and_smul_mem`). Coordinates are `b.repr x i`; indices are $0, \dots, n-1$.

**Proves** Lemma 3.2 (p. 104): $\Gamma$ has a basis $c_0, \dots, c_{n-1}$ of the triangular shape
$c_j = t_{j0}b_0 + \cdots + t_{jj}b_j$ with $t_{jj} \ne 0$ (`exists_triangular_basis`).

**Proof** (Cassels'): $S_j$ = the $j$-th coordinates of the elements of $\Gamma$ whose coordinates after $j$ vanish is an
ideal (`triIdeal`) containing $d$; choose $c_j$ realizing a generator $t_{jj}$. Every element of $\Gamma$ is then reduced
to $0$ by subtracting multiples of $c_{n-1}, c_{n-2}, \dots$; independence comes from the nonzero diagonal.
-/
import Mathlib
import QuadFormsKB.Citation

namespace QuadFormsKB.Cassels

open Module Submodule

variable {n : ℕ} {I Λ : Type*} [CommRing I] [IsDomain I] [IsPrincipalIdealRing I] [AddCommGroup Λ] [Module I Λ]

/-- The ideal $S_j$ (Cassels' (3.8)): of $j$-th coordinates of the elements of $\Gamma$ whose coordinates after $j$ vanish. -/
def triIdeal (b : Basis (Fin n) I Λ) (Γ : Submodule I Λ) (j : Fin n) : Ideal I where
  carrier := {s | ∃ a ∈ Γ, b.repr a j = s ∧ ∀ i, j < i → b.repr a i = 0}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl, ha'⟩ ⟨a', ha2, rfl, ha2'⟩
    exact ⟨a + a', Γ.add_mem ha ha2, by simp, fun i hi => by simp [ha' i hi, ha2' i hi]⟩
  zero_mem' := ⟨0, Γ.zero_mem, by simp, fun i _ => by simp⟩
  smul_mem' := by
    rintro r _ ⟨a, ha, rfl, ha'⟩
    exact ⟨r • a, Γ.smul_mem r ha, by simp, fun i hi => by simp [ha' i hi]⟩

/-- **Cassels, Ch. 7, Lemma 3.2**: *suppose that $I$ is a principal ideal domain, let $\Gamma \subseteq \Lambda$ be
lattices and $b_0, \dots, b_{n-1}$ any basis of $\Lambda$; then there is a basis $c_0, \dots, c_{n-1}$ of $\Gamma$ of the
shape $c_j = t_{j0}b_0 + \cdots + t_{jj}b_j$ with $t_{ji} \in I$, $t_{jj} \ne 0$.* That $\Gamma$ is a lattice in the same
space is expressed by $d\vec x \in \Gamma$ for all $\vec x \in \Lambda$, for some $d \ne 0$; the conclusion says
that the $b$-coordinates of $c_j$ after the $j$-th vanish and the $j$-th is nonzero. -/
@[kb "cassels1978" "Ch. 7, Lemma 3.2, p. 104"]
theorem exists_triangular_basis (b : Basis (Fin n) I Λ) (Γ : Submodule I Λ) {d : I} (hd : d ≠ 0)
    (hdΓ : ∀ x : Λ, d • x ∈ Γ) :
    ∃ c : Basis (Fin n) I Γ, ∀ j, b.repr (c j) j ≠ 0 ∧ ∀ i, j < i → b.repr (c j) i = 0 := by
  classical
  set t : Fin n → I := fun j => Submodule.IsPrincipal.generator (triIdeal b Γ j) with ht
  have hmem : ∀ j, t j ∈ triIdeal b Γ j := fun j => Submodule.IsPrincipal.generator_mem _
  choose c hcΓ hcj hci using hmem
  have hdj : ∀ j, d ∈ triIdeal b Γ j := fun j =>
    ⟨d • b j, hdΓ _, by simp, fun i hi => by simp [hi.ne]⟩
  have ht0 : ∀ j, t j ≠ 0 := by
    intro j h0
    have : triIdeal b Γ j = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).2 h0
    have := hdj j
    rw [‹triIdeal b Γ j = ⊥›, Ideal.mem_bot] at this
    exact hd this
  -- spanning
  have hspan : ∀ k : ℕ, ∀ a ∈ Γ, (∀ i : Fin n, k ≤ i.val → b.repr a i = 0) →
      a ∈ span I (Set.range c) := by
    intro k
    induction k with
    | zero =>
      intro a _ ha
      have : a = 0 := b.repr.injective (Finsupp.ext fun i => by simpa using ha i (Nat.zero_le _))
      rw [this]; exact zero_mem _
    | succ k ih =>
      intro a haΓ ha
      by_cases hk : k < n
      · set j : Fin n := ⟨k, hk⟩
        have hS : b.repr a j ∈ triIdeal b Γ j :=
          ⟨a, haΓ, rfl, fun i hi => ha i (by simp [j, Fin.lt_def] at hi; omega)⟩
        obtain ⟨v, hv⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator _).1 hS
        have h' : a - v • c j ∈ span I (Set.range c) := by
          refine ih _ (Γ.sub_mem haΓ (Γ.smul_mem _ (hcΓ j))) fun i hi => ?_
          rcases (Nat.lt_or_eq_of_le hi) with hlt | heq
          · have hji : j < i := by simp [j, Fin.lt_def]; omega
            simp [ha i (by omega), hci j i hji]
          · have : i = j := Fin.ext (by simp [j]; omega)
            subst this
            simp [hcj, hv, smul_eq_mul, ht]
        have := add_mem h' (smul_mem (span I (Set.range c)) v (subset_span ⟨j, rfl⟩))
        simpa using this
      · exact ih a haΓ fun i hi => ha i (by omega)
  set v : Fin n → Γ := fun j => ⟨c j, hcΓ j⟩ with hv
  have hli : LinearIndependent I v := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have hg' : ∑ j, g j • c j = 0 := by
      have := congrArg Subtype.val hg
      simpa [hv] using this
    have hcoord : ∀ i, ∑ l, g l * b.repr (c l) i = 0 := by
      intro i
      have := congrArg (fun x => b.repr x i) hg'
      simpa [map_sum] using this
    have key : ∀ m : ℕ, ∀ j : Fin n, n - m ≤ j.val → g j = 0 := by
      intro m
      induction m with
      | zero => intro j hj; omega
      | succ m ih =>
        intro j hj
        by_cases hjm : n - m ≤ j.val
        · exact ih j hjm
        · have hsum := hcoord j
          rw [Finset.sum_eq_single j] at hsum
          · rw [hcj] at hsum
            exact (mul_eq_zero.1 hsum).resolve_right (ht0 j)
          · intro l _ hl
            rcases lt_or_gt_of_ne hl with hlt | hgt
            · rw [hci l j hlt, mul_zero]
            · rw [ih l (by rw [Fin.lt_def] at hgt; omega), zero_mul]
          · simp
    intro j
    exact key n j (by omega)
  have hsp : ⊤ ≤ span I (Set.range v) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun I).1
      (hspan n x hx fun i hi => absurd i.2 (by omega))
    have : (⟨x, hx⟩ : Γ) = ∑ j, w j • v j := Subtype.ext (by simp [hv, ← hw])
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)
  refine ⟨Basis.mk hli hsp, fun j => ?_⟩
  rw [Basis.mk_apply]
  exact ⟨by rw [hcj]; exact ht0 j, hci j⟩

end QuadFormsKB.Cassels
