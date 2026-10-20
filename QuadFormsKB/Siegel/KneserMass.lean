/-
# Kneser neighbours, part 5: the mass completeness criterion

**Layer:** integral forms (`QuadForm ℤ n`), their $\mathrm{GL}_n(\mathbb{Z})$-classes (`QClass`) and the mass
$\mathrm{Mass}(Q) = \sum_{[Q'] \in \mathrm{Gen}(Q)} 1/|\mathrm{Aut}(Q')|$ (`Siegel/Mass.lean`; the convention of this repository: $\mathrm{GL}$-classes,
$\mathrm{Aut} \subseteq \mathrm{GL}_n(\mathbb{Z})$ including improper automorphisms).

**Proves** the stopping rule of the neighbour method (Schulze-Pillot 1991, §2; Scharlau–Hemkemeier 1998, §2; Conway–Sloane 1988,
§1): for a positive definite $Q$ and pairwise non-equivalent forms $Q_1, \dots, Q_k$ in its genus,
- `sum_inv_card_aut_le_mass`: $\sum_i 1/|\mathrm{Aut}(Q_i)| \le \mathrm{Mass}(Q)$;
- `genusClasses_eq_of_sum_eq_mass` (**completeness criterion**): if equality holds, then $Q_1, \dots, Q_k$ represent **every** class
  in the genus, $\mathrm{Gen}(Q) = \{[Q_1], \dots, [Q_k]\}$; `exists_intEquiv_of_sum_eq_mass` is the same statement for forms.

*Proof:* the genus has finitely many classes (`genusFinite`, Hermite reduction) and every class has
$|\mathrm{Aut}| \ge 1$ (`autCard_pos_of_mem`); the classes $[Q_i]$ are distinct, so their weights are part of the finite sum
defining the mass, and a missing class would contribute a positive term.

The criterion is unconditional; the value of $\mathrm{Mass}(Q)$ it is compared with must come from elsewhere (the
Smith–Minkowski–Siegel mass formula, `Tamagawa/MassFormula.lean`, or a proved class-number result, `KneserExample.lean`).
-/
import QuadFormsKB.Siegel.FourSquaresClassNumber

open Matrix

namespace QuadFormsKB.Siegel.Kneser

open QuadFormsKB.Siegel

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **The classes of a pairwise non-equivalent family** $(Q_i)_{i \in \iota}$, as a `Finset` of classes. -/
noncomputable def classFinset (R : ι → QuadForm ℤ n) : Finset (QClass n) :=
  by classical exact Finset.univ.image fun i => classOf (R i)

theorem mem_classFinset {R : ι → QuadForm ℤ n} {c : QClass n} :
    c ∈ classFinset R ↔ ∃ i, classOf (R i) = c := by
  classical
  simp [classFinset]

/-- With pairwise non-equivalent $Q_i$, $\sum_{c \in \{[Q_i]\}} 1/|\mathrm{Aut}(c)| = \sum_i 1/|\mathrm{Aut}(Q_i)|$. -/
theorem sum_classFinset {R : ι → QuadForm ℤ n} (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j) :
    ∑ c ∈ classFinset R, ((c.autCard : ℝ))⁻¹ = ∑ i, ((Nat.card (Aut (R i)) : ℝ))⁻¹ := by
  classical
  unfold classFinset
  rw [Finset.sum_image]
  · rfl
  · intro i _ j _ h
    exact hdist i j (classOf_eq_classOf_iff.mp h)

/-- **Lower bound:** for a positive definite $Q$ and pairwise non-equivalent forms $Q_i$ in its genus,
$$\sum_i \frac{1}{|\mathrm{Aut}(Q_i)|} \le \mathrm{Mass}(Q).$$ -/
@[kb "schulzepillot1991" "§2 (mass check)"]
theorem sum_inv_card_aut_le_mass {Q : IntQF n} (hQ : Q.PosDef) (R : ι → QuadForm ℤ n)
    (hgen : ∀ i, SameGenus Q (R i)) (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j) :
    ∑ i, ((Nat.card (Aut (R i)) : ℝ))⁻¹ ≤ mass Q := by
  classical
  have hF := genusFinite hQ
  rw [mass_eq_sum hF, ← sum_classFinset hdist]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro c hc
  obtain ⟨i, rfl⟩ := mem_classFinset.mp hc
  exact (Set.Finite.mem_toFinset _).mpr (classOf_mem_genusClasses_iff.mpr (hgen i))

/-- **The mass completeness criterion** (the stopping rule of Kneser's neighbour method; Schulze-Pillot 1991, §2;
Scharlau–Hemkemeier 1998, §2). Let $Q$ be positive definite and $Q_1, \dots, Q_k$ (`R : ι → QuadForm ℤ n`) forms with
- `hgen`: each $Q_i$ in the genus of $Q$;
- `hdist`: the $Q_i$ pairwise not $\mathrm{GL}_n(\mathbb{Z})$-equivalent;
- `hmass`: $\sum_i 1/|\mathrm{Aut}(Q_i)| = \mathrm{Mass}(Q)$.

Then $\mathrm{Gen}(Q) = \{[Q_1], \dots, [Q_k]\}$: the list is the whole genus. -/
@[kb "schulzepillot1991" "§2 (mass check)"]
theorem genusClasses_eq_of_sum_eq_mass {Q : IntQF n} (hQ : Q.PosDef) (R : ι → QuadForm ℤ n)
    (hgen : ∀ i, SameGenus Q (R i)) (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j)
    (hmass : ∑ i, ((Nat.card (Aut (R i)) : ℝ))⁻¹ = mass Q) :
    genusClasses Q = Set.range fun i => classOf (R i) := by
  classical
  have hF := genusFinite hQ
  set T := hF.finite_classes.toFinset
  have hsub : classFinset R ⊆ T := by
    intro c hc
    obtain ⟨i, rfl⟩ := mem_classFinset.mp hc
    exact (Set.Finite.mem_toFinset _).mpr (classOf_mem_genusClasses_iff.mpr (hgen i))
  have heq : classFinset R = T := by
    by_contra hne
    obtain ⟨c, hcT, hcR⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
    have hpos : (0 : ℝ) < (c.autCard : ℝ)⁻¹ := by
      have := autCard_pos_of_mem hQ ((Set.Finite.mem_toFinset _).mp hcT)
      positivity
    have h1 : ∑ d ∈ insert c (classFinset R), ((d.autCard : ℝ))⁻¹ ≤ ∑ d ∈ T, ((d.autCard : ℝ))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_subset hcT hsub) fun _ _ _ => by positivity
    rw [Finset.sum_insert hcR, sum_classFinset hdist, hmass, mass_eq_sum hF] at h1
    linarith
  ext c
  constructor
  · intro hc
    have : c ∈ classFinset R := heq ▸ (Set.Finite.mem_toFinset _).mpr hc
    obtain ⟨i, rfl⟩ := mem_classFinset.mp this
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact classOf_mem_genusClasses_iff.mpr (hgen i)

/-- **The completeness criterion for forms:** under the hypotheses of `genusClasses_eq_of_sum_eq_mass`, every form $Q'$ in
the genus of $Q$ is $\mathrm{GL}_n(\mathbb{Z})$-equivalent to one of the $Q_i$. -/
@[kb "schulzepillot1991" "§2 (mass check)"]
theorem exists_intEquiv_of_sum_eq_mass {Q : IntQF n} (hQ : Q.PosDef) (R : ι → QuadForm ℤ n)
    (hgen : ∀ i, SameGenus Q (R i)) (hdist : ∀ i j, IntEquiv (R i) (R j) → i = j)
    (hmass : ∑ i, ((Nat.card (Aut (R i)) : ℝ))⁻¹ = mass Q) {Q' : QuadForm ℤ n} (h : SameGenus Q Q') :
    ∃ i, IntEquiv (R i) Q' := by
  have hc := classOf_mem_genusClasses_iff.mpr h
  rw [genusClasses_eq_of_sum_eq_mass hQ R hgen hdist hmass] at hc
  obtain ⟨i, hi⟩ := hc
  exact ⟨i, classOf_eq_classOf_iff.mp hi⟩

end QuadFormsKB.Siegel.Kneser
