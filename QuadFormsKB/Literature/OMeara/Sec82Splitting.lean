/-
# O'Meara §82D: direct sums of lattices, the notation $X_1 \perp \cdots \perp X_r$, adjunction

**Setting.** $R$ is a Dedekind domain with fraction field $F$, $2 \in F^\times$, and $(V, Q)$ a finite-dimensional
quadratic space over $F$ with O'Meara's bilinear form $B$ = `bil Q`; lattices are `Submodule R V`. A direct sum
$L = L_1 \oplus \cdots \oplus L_r$ of sublattices is an independent family (`iSupIndep`) with supremum $L$; an
orthogonal splitting is `IsOrthSplit` (`Sec82.lean`).

**Defines** `IsOrthSplitInto Q L Qs Xs`: $L = X_1 \perp \cdots \perp X_r$ for lattices $X_i$ in other quadratic spaces
(O'Meara 1963, §82D, p. 224).

**Proves** (O'Meara 1963, §82D, pp. 224–225):
* `span_iSup`, `iSupIndep_span`, `finrank_iSup_of_iSupIndep`, `IsOrthSplit.span_eq`, `IsOrthSplit.iSupIndep_span`,
  `IsOrthSplit.finrank_eq_sum`: a direct (or orthogonal) sum of lattices $L = L_1 \oplus \cdots \oplus L_r$ gives the
  direct sum of spaces $FL = FL_1 \oplus \cdots \oplus FL_r$ and $\operatorname{rank} L = \sum \operatorname{rank} L_i$
  (p. 225);
* `adjunction_space`, `adjunction_lattice`: *adjunction* (p. 225): for quadratic spaces $U$, $V$ the space
  $W = U \times V$ with the form $Q_U \oplus Q$ (Mathlib's `QuadraticMap.prod`) contains $V$ (as $0 \times V$) and is
  $W = U' \perp V$ with $U' = U \times 0 \cong U$; for lattices $K \subseteq U$ and $L \subseteq V$ the lattice
  $J = K' \perp L$ with $K' = K \times 0 \cong K$ lies in $W$.
-/
import QuadFormsKB.Literature.OMeara.Sec82Modular
import QuadFormsKB.Literature.OMeara.Sec82Free

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The notation $L = X_1 \perp \cdots \perp X_r$** (O'Meara 1963, §82D, p. 224): for lattices $X_i$ in quadratic
spaces $(V_i, Q_i)$, not necessarily contained in $V$, $L$ has an orthogonal splitting $L = L_1 \perp \cdots \perp L_r$
in which each $L_i$ is isometric to $X_i$. -/
@[kb "omeara1963" "§82D, p. 224 (L = X₁ ⊥ ⋯ ⊥ X_r for lattices in other spaces)"]
def IsOrthSplitInto (L : Submodule R V) {ι : Type*} {Vs : ι → Type*} [∀ i, AddCommGroup (Vs i)]
    [∀ i, Module F (Vs i)] [∀ i, Module R (Vs i)] [∀ i, IsScalarTower R F (Vs i)]
    (Qs : ∀ i, QuadraticForm F (Vs i)) (Xs : ∀ i, Submodule R (Vs i)) : Prop :=
  ∃ Ls : ι → Submodule R V, IsOrthSplit Q L Ls ∧ ∀ i, IsometricLat Q (Qs i) (Ls i) (Xs i)

omit [IsDedekindDomain R] [IsFractionRing R F] [Invertible (2 : F)] [FiniteDimensional F V] in
/-- $F(\sum_i L_i) = \sum_i FL_i$. -/
theorem span_iSup {ι : Sort*} (Ls : ι → Submodule R V) :
    span F ((⨆ i, Ls i : Submodule R V) : Set V) = ⨆ i, span F (Ls i : Set V) := by
  rw [Submodule.iSup_eq_span, Submodule.span_span_of_tower, Submodule.span_iUnion]

/-- **A direct sum of lattices spans a direct sum of spaces** (O'Meara 1963, §82D, p. 225): if the sublattices $L_i$
are independent ($L = L_1 \oplus \cdots \oplus L_r$), the spaces $FL_i$ are independent, so
$FL = FL_1 \oplus \cdots \oplus FL_r$ (with `span_iSup`). -/
@[kb "omeara1963" "§82D, p. 225 (L = L₁ ⊕ ⋯ ⊕ L_r implies FL = FL₁ ⊕ ⋯ ⊕ FL_r)"]
theorem iSupIndep_span {ι : Type*} {Ls : ι → Submodule R V} (h : iSupIndep Ls) :
    iSupIndep fun i => span F (Ls i : Set V) := by
  intro i
  have hd := disjoint_span_of_disjoint (F := F) (h i)
  simp only [span_iSup] at hd
  exact hd

include F in
/-- $\operatorname{rank}(\sum_{i \in s} L_i) = \sum_{i \in s} \operatorname{rank} L_i$ for independent $L_i$. -/
theorem finrank_biSup_of_iSupIndep {ι : Type*} {Ls : ι → Submodule R V} (h : iSupIndep Ls) (s : Finset ι) :
    finrank R ↥(⨆ i ∈ s, Ls i) = ∑ i ∈ s, finrank R (Ls i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [iSup₂_eq_bot.2 fun i hi => absurd hi (Finset.notMem_empty i)]
    simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, ← ih, Finset.iSup_insert, finrank_sup_of_disjoint' (F := F)]
    exact h.disjoint_biSup (y := (s : Set ι)) (by simpa using hj)

include F in
/-- **The rank of a direct sum** (O'Meara 1963, §82D, p. 225): for independent sublattices $L_1, \dots, L_r$,
$\operatorname{rank}(L_1 \oplus \cdots \oplus L_r) = \operatorname{rank} L_1 + \cdots + \operatorname{rank} L_r$. -/
@[kb "omeara1963" "§82D, p. 225 (rank L = rank L₁ + ⋯ + rank L_r)"]
theorem finrank_iSup_of_iSupIndep {ι : Type*} [Fintype ι] {Ls : ι → Submodule R V} (h : iSupIndep Ls) :
    finrank R ↥(⨆ i, Ls i) = ∑ i, finrank R (Ls i) := by
  have h1 : (⨆ i ∈ (Finset.univ : Finset ι), Ls i) = ⨆ i, Ls i := by
    simp only [Finset.mem_univ, iSup_pos]
  rw [← h1, finrank_biSup_of_iSupIndep (F := F) h Finset.univ]

/-- **An orthogonal splitting of a lattice gives one of its space** (O'Meara 1963, §82D, p. 225): if
$L = L_1 \perp \cdots \perp L_r$ then $FL = FL_1 + \cdots + FL_r$, the sum being direct
(`IsOrthSplit.iSupIndep_span`) and orthogonal. -/
@[kb "omeara1963" "§82D, p. 225 (L = L₁ ⊥ ⋯ ⊥ L_r implies FL = FL₁ ⊥ ⋯ ⊥ FL_r)"]
theorem IsOrthSplit.span_eq {L : Submodule R V} {ι : Type*} {Ls : ι → Submodule R V} (h : IsOrthSplit Q L Ls) :
    span F (L : Set V) = ⨆ i, span F (Ls i : Set V) := by
  rw [← h.iSup_eq, span_iSup]

/-- The spaces $FL_i$ of an orthogonal splitting are independent (O'Meara 1963, §82D, p. 225). -/
@[kb "omeara1963" "§82D, p. 225 (the FL_i of a splitting are independent)"]
theorem IsOrthSplit.iSupIndep_span {L : Submodule R V} {ι : Type*} {Ls : ι → Submodule R V}
    (h : IsOrthSplit Q L Ls) : iSupIndep fun i => span F (Ls i : Set V) :=
  OMeara.iSupIndep_span (F := F) h.indep

/-- **The rank of an orthogonal sum** (O'Meara 1963, §82D, p. 225): if $L = L_1 \perp \cdots \perp L_r$ then
$\operatorname{rank} L = \operatorname{rank} L_1 + \cdots + \operatorname{rank} L_r$. -/
@[kb "omeara1963" "§82D, p. 225 (rank of an orthogonal sum)"]
theorem IsOrthSplit.finrank_eq_sum {L : Submodule R V} {ι : Type*} [Fintype ι] {Ls : ι → Submodule R V}
    (h : IsOrthSplit Q L Ls) : finrank R L = ∑ i, finrank R (Ls i) := by
  rw [← finrank_iSup_of_iSupIndep (F := F) h.indep, h.iSup_eq]

section Adjunction

variable {U : Type*} [AddCommGroup U] [Module F U] [Module R U] [IsScalarTower R F U]
variable (QU : QuadraticForm F U)

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- $B_W((u, 0), (0, v)) = 0$ in $W = U \times V$ with the form $Q_U \oplus Q$. -/
theorem bil_prod_inl_inr (u : U) (v : V) : bil (QU.prod Q) (u, 0) (0, v) = 0 := by
  rw [bil_eq_half]
  simp [QuadraticMap.prod_apply]

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **Adjunction of a space** (O'Meara 1963, §82D, p. 225): for quadratic spaces $(U, Q_U)$ and $(V, Q)$, the space
$W = U \times V$ with the form $Q_U \oplus Q$ contains $V$ as $0 \times V$ (with its form $Q$) and
$W = U' \perp V$ with $U' = U \times 0$ isometric to $U$: $B_W(U', V) = 0$, $Q_W(u, 0) = Q_U(u)$,
$Q_W(0, v) = Q(v)$, and $U'$, $V$ are complementary subspaces of $W$. -/
@[kb "omeara1963" "§82D, p. 225 (adjunction: W = U' ⊥ V with U' ≅ U)"]
theorem adjunction_space :
    (∀ (u : U) (v : V), bil (QU.prod Q) (u, 0) (0, v) = 0) ∧ (∀ u : U, (QU.prod Q) (u, 0) = QU u) ∧
      (∀ v : V, (QU.prod Q) (0, v) = Q v) ∧
      IsCompl (LinearMap.range (LinearMap.inl F U V)) (LinearMap.range (LinearMap.inr F U V)) :=
  ⟨bil_prod_inl_inr Q QU, fun u => by simp [QuadraticMap.prod_apply],
    fun v => by simp [QuadraticMap.prod_apply], LinearMap.isCompl_range_inl_inr⟩

omit [IsDedekindDomain R] [IsFractionRing R F] [FiniteDimensional F V] in
/-- **Adjunction of a lattice** (O'Meara 1963, §82D, p. 225): for lattices $K$ in $U$ and $L$ in $V$, the lattice
$J = K \times L$ in $W = U \times V$ (form $Q_U \oplus Q$) is $J = K' \perp L'$ with $K' = K \times 0 \cong K$ and
$L' = 0 \times L \cong L$ (the copy of $L$ in the copy $0 \times V$ of $V$). -/
@[kb "omeara1963" "§82D, p. 225 (adjunction: J = K' ⊥ L with K' ≅ K)"]
theorem adjunction_lattice (K : Submodule R U) (L : Submodule R V) :
    IsOrthSum (QU.prod Q) (K.prod L) (K.map (LinearMap.inl R U V)) (L.map (LinearMap.inr R U V)) ∧
      IsometricLat QU (QU.prod Q) K (K.map (LinearMap.inl R U V)) ∧
      IsometricLat Q (QU.prod Q) L (L.map (LinearMap.inr R U V)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩
    exact bil_prod_inl_inr Q QU u v
  · rw [Submodule.disjoint_def]
    rintro _ ⟨u, -, rfl⟩ ⟨v, -, hv⟩
    simp only [LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk.injEq] at hv
    simp [← hv.1]
  · apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩; exact ⟨hu, L.zero_mem⟩
      · rintro _ ⟨v, hv, rfl⟩; exact ⟨K.zero_mem, hv⟩
    · rintro ⟨u, v⟩ ⟨hu, hv⟩
      have : ((u, v) : U × V) = (u, 0) + (0, v) := by simp
      rw [this]
      exact Submodule.add_mem_sup ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  · exact ⟨Submodule.equivMapOfInjective _ LinearMap.inl_injective K, fun x => by
      simp [Submodule.coe_equivMapOfInjective_apply, QuadraticMap.prod_apply]⟩
  · exact ⟨Submodule.equivMapOfInjective _ LinearMap.inr_injective L, fun x => by
      simp [Submodule.coe_equivMapOfInjective_apply, QuadraticMap.prod_apply]⟩

end Adjunction

end QuadFormsKB.OMeara
