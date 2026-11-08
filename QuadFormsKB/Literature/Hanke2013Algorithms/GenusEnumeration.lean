/-
# Hanke 2013, Algorithm 5.8: the halting test of the genus enumeration

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), Algorithm 5.8, p. 20.

**Setting** (the library's, `Lattices/Finite.lean`): $F$ a number field, $Q$ a totally positive definite quadratic form
on $F^n$, lattices `Lat F n`, classes `LatClass Q`, the classes in the genus of $L$ `genusClasses Q L`,
$|O(M)|$ = `LatClass.autCard`, and $\mathrm{Mass}(L) = \sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}1/|O(M)|$ = `mass Q L`. $L$ is
integral (`IsIntegral Q L`; the paper's $\mathfrak a$-valued lattices reduce to this by scaling, not formalized here).

**Proves** the halting test of Algorithm 5.8: for a finite set $S$ of classes in the genus of $L$, the partial mass
$\mathrm{Mass}(S) = \sum_{c\in S}1/|O(c)|$ is at most $\mathrm{Mass}(L)$, with equality exactly when $S$ contains every class
of the genus (`algorithm_5_8_halting`, `partialMass_le`).

**Named input** `BenhamHsia F` (Benham–Hsia [2, Proposition 1, (1.1), Theorem 2], as used by the paper: "the
$\mathfrak p$-power neighbors at the primes $\mathfrak p$ of bounded norm exhaust all classes in the genus of $L$"): for
$n\ge3$, a totally positive definite $Q$ and an integral lattice $L$, there are a finite set $E$ of excluded primes and a
bound $B$ such that the lattices reached from $L$ by chains of $\mathfrak p$-neighbours (Definition 5.1, `IsPNeighbor`, for
$\mathfrak a = \mathcal O_F$, up to isometry) at primes $\mathfrak p\notin E$ with $N(\mathfrak p)\le B$ are exactly the
lattices in the genus of $L$. (Benham–Hsia specify the excluded primes, those dividing $2\,dL$; only their finiteness
is used here, so the input assumed is weaker than their theorem.) From it: `algorithm_5_8_complete`, the classes found
by the neighbour search are those of the genus, and the halting test $\mathrm{Mass}(S) = \mathrm{Mass}(L)$ is reached.
-/
import QuadFormsKB.Lattices.Finite
import QuadFormsKB.Literature.Hanke2013Algorithms.Even
import QuadFormsKB.Equiv.Mathlib
import QuadFormsKB.Citation

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-- **The partial mass** $\mathrm{Mass}(S) = \sum_{L'\in S}1/\#\mathrm{Aut}(L')$ of a finite set $S$ of classes (Hanke 2013,
Algorithm 5.8, p. 20). -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (the partial mass Mass(S))"]
def partialMass (Q : QuadForm F n) (S : Finset (LatClass Q)) : ℝ :=
  ∑ c ∈ S, ((LatClass.autCard Q c : ℝ))⁻¹

/-- Every class in the genus of an integral lattice of a totally positive definite space has a positive weight. -/
theorem autCard_inv_pos {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {L : Lat F n} (hLi : IsIntegral Q L.1)
    {c : LatClass Q} (hc : c ∈ genusClasses Q L) : 0 < ((LatClass.autCard Q c : ℝ))⁻¹ := by
  obtain ⟨M, rfl, hgen⟩ := hc
  have := finite_autLat hQ M.2 (SameGenus.isIntegral Q hLi hgen)
  have hpos : 0 < Nat.card (autLat Q M.1) := Nat.card_pos
  change (0 : ℝ) < ((Nat.card (autLat Q M.1) : ℕ) : ℝ)⁻¹
  positivity

/-- **The partial mass is at most the mass** (Hanke 2013, Algorithm 5.8, p. 20: "If the partial mass ... satisfies
$\mathrm{Mass}(S) < \mathrm{Mass}(L)$, then repeat"). -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (Mass(S) ≤ Mass(L))"]
theorem partialMass_le {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {L : Lat F n} (hLi : IsIntegral Q L.1)
    {S : Finset (LatClass Q)} (hS : (S : Set (LatClass Q)) ⊆ genusClasses Q L) : partialMass Q S ≤ mass Q L := by
  rw [mass_eq_sum hQ L hLi, partialMass]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => (Set.Finite.mem_toFinset _).2 (hS hc)) ?_
  intro c _ _
  positivity

/-- **The halting test of Algorithm 5.8** (Hanke 2013, p. 20: "repeat the procedure for the next smallest prime until
$\mathrm{Mass}(S) = \mathrm{Mass}(L)$"): for a finite set $S$ of classes in the genus of an integral lattice $L$ of a totally
positive definite space, $\mathrm{Mass}(S) = \mathrm{Mass}(L)$ if and only if $S$ is the set of all classes in the genus. -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (halting: Mass(S) = Mass(L) iff S is all of the genus)"]
theorem algorithm_5_8_halting {Q : QuadForm F n} (hQ : IsTotallyPosDef Q) {L : Lat F n} (hLi : IsIntegral Q L.1)
    {S : Finset (LatClass Q)} (hS : (S : Set (LatClass Q)) ⊆ genusClasses Q L) :
    partialMass Q S = mass Q L ↔ (S : Set (LatClass Q)) = genusClasses Q L := by
  classical
  set T := (genusClasses_finite hQ L hLi).toFinset with hTdef
  have hST : S ⊆ T := fun c hc => (Set.Finite.mem_toFinset _).2 (hS hc)
  rw [mass_eq_sum hQ L hLi, partialMass]
  constructor
  · intro h
    have hsplit := Finset.sum_sdiff hST (f := fun c => ((LatClass.autCard Q c : ℝ))⁻¹)
    have hzero : ∑ c ∈ T \ S, ((LatClass.autCard Q c : ℝ))⁻¹ = 0 := by linarith
    have hempty : T \ S = ∅ := by
      by_contra hne
      obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.2 hne
      have hpos : 0 < ∑ c ∈ T \ S, ((LatClass.autCard Q c : ℝ))⁻¹ :=
        Finset.sum_pos (fun c hc => autCard_inv_pos hQ hLi ((Set.Finite.mem_toFinset _).1
          (Finset.mem_sdiff.1 hc).1)) ⟨c, hc⟩
      linarith
    have hTS : T ⊆ S := fun c hc => by
      by_contra h'
      have : c ∈ T \ S := Finset.mem_sdiff.2 ⟨hc, h'⟩
      rw [hempty] at this; simp at this
    apply Set.Subset.antisymm hS
    intro c hc
    exact Finset.mem_coe.2 (hTS ((Set.Finite.mem_toFinset _).2 hc))
  · intro h
    have : S = T := by
      ext c
      rw [hTdef, Set.Finite.mem_toFinset, ← h, Finset.mem_coe]
    rw [this]

/-- **One step of the neighbour search** of Algorithm 5.8: $Y$ is isometric to a $\mathfrak p$-neighbour of $X$
(Definition 5.1 with $\mathfrak a = \mathcal O_F$, `IsPNeighbor`) for some maximal ideal $\mathfrak p$ with the property $P$. -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (p-neighbours of the lattices found so far)"]
def NbStep (Q : QuadForm F n) (P : Ideal (𝓞 F) → Prop) (X Y : Lat F n) : Prop :=
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  ∃ p : Ideal (𝓞 F), p.IsMaximal ∧ P p ∧ ∃ Y' : Lat F n,
    IsPNeighbor (QuadForm.toQuadraticForm Q) (1 : Submodule (𝓞 F) F) p X.1 Y'.1 ∧ IsIsometric Q Y'.1 Y.1

/-- **Benham–Hsia** ([2, Proposition 1, (1.1), Theorem 2], as cited in Hanke 2013, Algorithm 5.8, p. 20), a **named
input** (not proved here): for $n\ge3$, a totally positive definite $Q$ on $F^n$ and an integral lattice $L$, there are a
finite set $E$ of primes and a bound $B$ such that a lattice $M$ is in the genus of $L$ if and only if it is reached from
$L$ by a chain of neighbour steps (`NbStep`) at primes $\mathfrak p\notin E$ with $N(\mathfrak p)\le B$. Field: `exhaust`. -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (citing Benham–Hsia [2, Proposition 1, (1.1), Theorem 2])"]
structure BenhamHsia (F : Type*) [Field F] [NumberField F] : Prop where
  exhaust : ∀ n : ℕ, 3 ≤ n → ∀ Q : QuadForm F n, IsTotallyPosDef Q → ∀ L : Lat F n, IsIntegral Q L.1 →
    ∃ E : Set (Ideal (𝓞 F)), E.Finite ∧ ∃ B : ℕ, ∀ M : Lat F n,
      SameGenus Q L.1 M.1 ↔ Relation.ReflTransGen (NbStep Q fun p => p ∉ E ∧ Nat.card (𝓞 F ⧸ p) ≤ B) L M

/-- **Algorithm 5.8 is complete and halts** (Hanke 2013, p. 20), conditional on the named input `BenhamHsia F`: for
$n\ge3$, $Q$ totally positive definite and $L$ integral, there are a finite set $E$ of primes and a bound $B$ such that the
set $S$ of classes of the lattices found by the neighbour search from $L$ (chains of $\mathfrak p$-neighbours, $\mathfrak p\notin E$,
$N(\mathfrak p)\le B$) is finite, is the set of all classes in the genus of $L$, and has partial mass $\mathrm{Mass}(S) = \mathrm{Mass}(L)$
(so the halting test of the algorithm is met). -/
@[kb "hanke2013algorithms" "Algorithm 5.8, p. 20 (correctness and termination, given Benham–Hsia)"]
theorem algorithm_5_8_complete (hBH : BenhamHsia F) (hn : 3 ≤ n) {Q : QuadForm F n} (hQ : IsTotallyPosDef Q)
    (L : Lat F n) (hLi : IsIntegral Q L.1) :
    ∃ E : Set (Ideal (𝓞 F)), E.Finite ∧ ∃ B : ℕ,
      ∃ hS : {c : LatClass Q | ∃ M : Lat F n, Quotient.mk _ M = c ∧
          Relation.ReflTransGen (NbStep Q fun p => p ∉ E ∧ Nat.card (𝓞 F ⧸ p) ≤ B) L M}.Finite,
        (hS.toFinset : Set (LatClass Q)) = genusClasses Q L ∧ partialMass Q hS.toFinset = mass Q L := by
  obtain ⟨E, hE, B, hiff⟩ := hBH.exhaust n hn Q hQ L hLi
  have heq : {c : LatClass Q | ∃ M : Lat F n, Quotient.mk _ M = c ∧
      Relation.ReflTransGen (NbStep Q fun p => p ∉ E ∧ Nat.card (𝓞 F ⧸ p) ≤ B) L M} = genusClasses Q L := by
    ext c
    simp only [Set.mem_ofPred_eq, genusClasses]
    exact exists_congr fun M => and_congr Iff.rfl (hiff M).symm
  have hfin : {c : LatClass Q | ∃ M : Lat F n, Quotient.mk _ M = c ∧
      Relation.ReflTransGen (NbStep Q fun p => p ∉ E ∧ Nat.card (𝓞 F ⧸ p) ≤ B) L M}.Finite := by
    rw [heq]; exact genusClasses_finite hQ L hLi
  refine ⟨E, hE, B, hfin, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset, heq]
  · rw [algorithm_5_8_halting hQ hLi (by rw [Set.Finite.coe_toFinset, heq]), Set.Finite.coe_toFinset, heq]

end QuadFormsKB.Hanke2013Algorithms
