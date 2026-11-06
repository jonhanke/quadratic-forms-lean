/-
# O'Meara §71D: step 1 of the proof of Hilbert's reciprocity law

O'Meara's Theorem 71:18 (Hilbert's reciprocity law) is in the library as `HN.hilbert_product_formula_nf` (proved by
the Weil index), and Theorem 71:19 with Corollary 71:19a as `PresNF.exists_prescribed_hilbert`. This file has the
first step of O'Meara's proof of 71:18 (p. 201), obtained here from 71:19 (which the library proves from the
reciprocity law, the reverse of O'Meara's order).

**Proves**
* Step 1 of the proof of 71:18 (pp. 201–202): `exists_hilbert_neg_one_at_two_of_three`, and the stronger
  `exists_hilbert_neg_one_pair` (any two distinct spots at which $\beta$ is not a square).
-/
import QuadFormsKB.Literature.OMeara.Sec71BNorm

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
/-- **Elements with symbol $-1$ at exactly two prescribed spots:** if $\beta \in \dot F$ is not a square at the
distinct spots $\mathfrak p_1$, $\mathfrak p_2$ (discrete or infinite), there is $\gamma \in \dot F$ with
$(\gamma, \beta)_\mathfrak p = -1$ for $\mathfrak p \in \{\mathfrak p_1, \mathfrak p_2\}$ and $+1$ at all other spots.
This is Theorem 71:19 for $T = \{\mathfrak p_1, \mathfrak p_2\}$ with the given $\beta$ (Corollary 71:19a). -/
@[kb "omeara1963" "§71D, 71:19 and 71:19a, p. 203 (T a pair of spots)"]
theorem exists_hilbert_neg_one_pair {β : F} (hβ : β ≠ 0) {p₁ p₂ : NFPlace F} (h12 : p₁ ≠ p₂)
    (hns₁ : p₁.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K β))
    (hns₂ : p₂.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K β)) :
    ∃ γ : F, γ ≠ 0 ∧ ∀ p : NFPlace F, p.hilbert γ β = if p = p₁ ∨ p = p₂ then -1 else 1 := by
  set ε : NFPlace F → ℤ := fun p => if p = p₁ ∨ p = p₂ then -1 else 1 with hε
  have hset : {v : NFPlace F | ∃ _ : Unit, ε v = -1} = {p₁, p₂} := by
    ext v
    simp only [hε, Set.mem_ofPred_eq, exists_const, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs with h
    · simpa using h
    · simp only [not_or] at h
      simp [h.1, h.2]
  have hset' : {v : NFPlace F | ε v = -1} = {p₁, p₂} := by
    rw [← hset]; simp
  obtain ⟨γ, hγ, hγv⟩ := PresNF.exists_prescribed_hilbert (ι := Unit) (fun _ => β) (fun _ => hβ)
    (fun _ v => ε v) (fun _ v => by simp only [hε]; split_ifs <;> simp)
    (by rw [hset]; exact Set.toFinite _) (fun _ => by rw [hset', Set.ncard_pair h12]; exact even_two)
    (by
      intro v
      by_cases hv : v = p₁ ∨ v = p₂
      · have hnsv : v.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K β) := by
          rcases hv with rfl | rfl
          · exact hns₁
          · exact hns₂
        have := exists_hilbertSymbol_neg_one v hβ hnsv
        cases v with
        | finite v =>
          obtain ⟨x, hx0, hx⟩ := this
          exact ⟨x, hx0, fun _ => by simp only [hε, if_pos hv]; exact hx⟩
        | infinite w =>
          obtain ⟨x, hx0, hx⟩ := this
          exact ⟨x, hx0, fun _ => by simp only [hε, if_pos hv]; exact hx⟩
      · cases v with
        | finite v =>
          exact ⟨1, one_ne_zero, fun _ => by simp only [hε, if_neg hv]; exact hilbertSymbol_one_right _ _⟩
        | infinite w =>
          exact ⟨1, one_ne_zero, fun _ => by simp only [hε, if_neg hv]; exact hilbertSymbol_one_right _ _⟩)
  exact ⟨γ, hγ, fun p => by rw [NFPlace_hilbert_comm]; exact hγv () p⟩

open scoped Classical in
/-- **Step 1 of the proof of Theorem 71:18** (O'Meara 1963, pp. 201–202): given three distinct spots
$\mathfrak p_1, \mathfrak p_2, \mathfrak p_3$ at which $\beta \in \dot F$ is not a square, there is $\gamma \in F$ such
that $(\gamma, \beta)_\mathfrak p$ is $-1$ at two of these spots and $+1$ at all remaining spots of $F$. O'Meara obtains
this from the index $(J_F : P_F N_{E/F} J_E) = 2$ for $E = F(\sqrt\beta)$; here it is Theorem 71:19
(`exists_hilbert_neg_one_pair`, which needs only two of the spots). -/
@[kb "omeara1963" "§71D, proof of 71:18, step 1, pp. 201–202"]
theorem exists_hilbert_neg_one_at_two_of_three {β : F} (hβ : β ≠ 0) {p₁ p₂ p₃ : NFPlace F} (h12 : p₁ ≠ p₂)
    (_h13 : p₁ ≠ p₃) (_h23 : p₂ ≠ p₃)
    (hns : ∀ p ∈ ({p₁, p₂, p₃} : Set (NFPlace F)), p.atPlace fun K _ _ => ¬ IsSquare (algebraMap F K β)) :
    ∃ γ : F, γ ≠ 0 ∧ ∃ q₁ ∈ ({p₁, p₂, p₃} : Set (NFPlace F)), ∃ q₂ ∈ ({p₁, p₂, p₃} : Set (NFPlace F)), q₁ ≠ q₂ ∧
      ∀ p : NFPlace F, p.hilbert γ β = if p = q₁ ∨ p = q₂ then -1 else 1 := by
  obtain ⟨γ, hγ, h⟩ := exists_hilbert_neg_one_pair hβ h12 (hns p₁ (by simp)) (hns p₂ (by simp))
  exact ⟨γ, hγ, p₁, by simp, p₂, by simp, h12, h⟩

end QuadFormsKB.OMeara
