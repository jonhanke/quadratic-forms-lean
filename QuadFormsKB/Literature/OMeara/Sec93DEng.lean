/-
# O'Meara §93D: from the norm group to a matrix (tools for 93:17 and 93:18)

**Setting**: $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$; $(V, Q)$ a quadratic space over
$F$, O'Meara's $B$ = `bil Q`; lattices are `Submodule R V`.

O'Meara proves the normal forms of 93:17 and 93:18 by the same pattern: write down a lattice $K$ on $FL$ with the
wanted matrix, check $\mathfrak gK = \mathfrak gL$, and conclude $L \cong K$ by Theorem 93:16. This file packages
that pattern:

* `exists_basis_of_isometricLat`: an isometry $L \cong M$ carries a base of $M$ to a base of $L$ with the same matrix;
* `span_basis_props`: an $F$-base $e$ of $V$ whose matrix $(B(e_i, e_j))$ has entries in $\mathfrak o$ and unit
  determinant spans a unimodular lattice $\mathfrak oe_1 + \dots + \mathfrak oe_n$ on $V$;
* `exists_basis_gram_of_normGroup_eq`: if moreover this lattice has the same norm group as a unimodular lattice $L$
  on $V$, then $L$ has a base with the same matrix (93:16);
* `basisF_of_lattice`, `isUnit_det_of_isUnimodular`, `span_eq_top_of_basis`: a base of a unimodular lattice $L$ with
  $\operatorname{rank} L = \dim V$ is a base of $V$, so $FL = V$.
-/
import QuadFormsKB.Literature.OMeara.Sec93DUni
import QuadFormsKB.Literature.OMeara.Sec93D18

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Eng93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- An isometry of lattices $L \cong M$ carries a base of $M$ to a base of $L$ with the same matrix. -/
theorem exists_basis_of_isometricLat {L M : Submodule R V} (h : IsometricLat Q Q L M) {ι : Type*}
    (e : Basis ι R M) :
    ∃ e' : Basis ι R L, gram Q (fun i => (e' i : V)) = gram Q (fun i => (e i : V)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.map f.symm, ?_⟩
  have hf' : ∀ x : M, Q (f.symm x : V) = Q (x : V) := fun x => by
    simpa using (hf (f.symm x)).symm
  ext i j
  simp only [gram, Matrix.of_apply, Basis.map_apply]
  exact Uni93.bil_eq_of_isometry Q f.symm hf' (e i) (e j)

/-- **A unimodular lattice from a base of $V$**: if the matrix of an $F$-base $e$ of $V$ is $G$ with entries in
$\mathfrak o$ and $\det G$ a unit, then $M = \mathfrak oe_1 + \dots + \mathfrak oe_n$ is a unimodular lattice on $V$
($FM = V$) with base $e$. -/
theorem span_basis_props {n : ℕ} [NeZero n] (e : Basis (Fin n) F V) {G : Matrix (Fin n) (Fin n) R}
    (hG : IsUnit G.det) (hgram : gram Q (fun i => e i) = G.map (algebraMap R F)) :
    IsUnimodular Q (span R (Set.range e)) ∧ (span R (Set.range e)).FG ∧
      span F ((span R (Set.range e) : Submodule R V) : Set V) = ⊤ ∧
      ∃ b : Basis (Fin n) R (span R (Set.range e)), ∀ i, (b i : V) = e i := by
  have hG' : gram Q (fun i => e i) = (1 : F) • G.map (algebraMap R F) := by rw [one_smul]; exact hgram
  obtain ⟨hmod, -⟩ := isModular_span_of_gram Q one_ne_zero hG hG'
  have hdet : (gram Q (fun i => e i)).det ≠ 0 := by
    rw [hgram, show (G.map (algebraMap R F)).det = algebraMap R F G.det from (RingHom.map_det _ _).symm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hG.ne_zero
  have hli : LinearIndependent R (fun i => e i) := linearIndependent_of_det_gram_ne_zero Q hdet
  refine ⟨?_, fg_span (Set.finite_range _), ?_, Basis.span hli, fun i => by simp [Basis.span_apply]⟩
  · rw [← Submodule.one_eq_span] at hmod
    exact hmod
  · rw [Submodule.span_span_of_tower, e.span_eq]

/-- **Theorem 93:16 in matrix form**: let $L$ be a unimodular lattice on $V$ ($FL = V$) and $e$ an $F$-base of $V$
whose matrix $G$ has entries in $\mathfrak o$ and unit determinant. If $\mathfrak oe_1 + \dots + \mathfrak oe_n$ has
the same norm group as $L$, then $L$ has a base with matrix $G$. -/
theorem exists_basis_gram_of_normGroup_eq {L : Submodule R V} (hfg : L.FG) (hU : IsUnimodular Q L)
    (hspan : span F (L : Set V) = ⊤) {n : ℕ} [NeZero n] (e : Basis (Fin n) F V)
    {G : Matrix (Fin n) (Fin n) R} (hG : IsUnit G.det) (hgram : gram Q (fun i => e i) = G.map (algebraMap R F))
    (hg : normGroup Q L = normGroup Q (span R (Set.range e))) :
    ∃ b : Basis (Fin n) R L, gram Q (fun i => (b i : V)) = G.map (algebraMap R F) := by
  obtain ⟨hMU, hMfg, hMspan, b, hb⟩ := span_basis_props Q e hG hgram
  have hiso := Uni93.isometricLat_of_normGroup_eq_of_span Q hfg hMfg (by rw [hMspan, hspan]) hU hMU hg
  obtain ⟨b', hb'⟩ := exists_basis_of_isometricLat Q hiso b
  refine ⟨b', ?_⟩
  rw [hb', ← hgram]
  congr 1
  funext i
  exact hb i

/-- The discriminant of a base of a unimodular lattice is a unit of $\mathfrak o$. -/
theorem isUnit_det_of_isUnimodular {L : Submodule R V} (hU : IsUnimodular Q L) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R L) :
    ∃ u : R, IsUnit u ∧ (gram Q fun i => (b i : V)).det = algebraMap R F u := by
  have hv := volume_eq_span_det Q b
  rw [hU.2.2, one_pow] at hv
  have h1 : (gram Q fun i => (b i : V)).det ∈ (1 : Submodule R F) := by
    rw [hv]; exact mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_one.mp h1
  have h2 : (1 : F) ∈ span R {(gram Q fun i => (b i : V)).det} := by
    rw [← hv]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨r, hr⟩ := mem_span_singleton.mp h2
  rw [← hu, Algebra.smul_def, ← map_mul] at hr
  have hru : r * u = 1 := IsFractionRing.injective R F (by rw [hr, map_one])
  exact ⟨u, IsUnit.of_mul_eq_one_right (a := r) hru, hu.symm⟩

/-- A base of a lattice with non-zero discriminant and rank $\dim V$ is an $F$-base of $V$. -/
theorem basisF_of_lattice [FiniteDimensional F V] {L : Submodule R V} {n : ℕ} [NeZero n] (b : Basis (Fin n) R L)
    (hdet : (gram Q fun i => (b i : V)).det ≠ 0) (hn : finrank F V = n) :
    ∃ e : Basis (Fin n) F V, ∀ i, e i = b i := by
  have hli : LinearIndependent F (fun i => (b i : V)) := linearIndependent_of_det_gram_ne_zero (R := F) Q hdet
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hn]), fun i => by simp⟩

/-- A lattice with a base that is an $F$-base of $V$ is a lattice on $V$: $FL = V$. -/
theorem span_eq_top_of_basis {L : Submodule R V} {n : ℕ} (b : Basis (Fin n) R L) (e : Basis (Fin n) F V)
    (he : ∀ i, e i = b i) : span F (L : Set V) = ⊤ := by
  rw [eq_top_iff, ← e.span_eq]
  refine span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [he]
  exact subset_span (b i).2

end Eng93

end QuadFormsKB.OMeara
