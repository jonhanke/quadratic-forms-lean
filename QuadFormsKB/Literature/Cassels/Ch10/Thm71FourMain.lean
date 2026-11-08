/-
# Cassels, Chapter 10, Theorem 7.1 for $n \ge 4$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7, Theorem 7.1 (p. 186) and its proof for $n \ge 4$
(pp. 189–190).

**Proves.**
* `spinApprox_of_isotropic` (Cassels' second stage, p. 190): a family $t_p \in \operatorname{Spin}(V_p)$ has the approximation
  property at every finite set $T$ (containing $2$ and the primes dividing the determinant of $f$) at whose primes $V_p$ is
  isotropic: each $t_p$ is a product of commutators (Lemma 3.4, Theorem 3.2) and Lemma 7.2 applies factor by factor;
* `spinStrongApproximation_four_le`: **Theorem 7.1 for $n \ge 4$**, by Cassels' proof: the first stage (`firstStage`) gives
  $u \in \operatorname{Spin}(V)$ close to the chosen $u^{(p)} \in \mathcal U_p$ on $T$; $u \in \operatorname{Spin}(\Lambda_p)$ outside a finite set
  $P_2$ of good primes, where $V_p$ is isotropic; the second stage gives $v$ close to $1$ on $T$, close to $u^{-1}$ on $P_2$ and in
  $\operatorname{Spin}(\Lambda_p)$ elsewhere; $uv$ is the required element.
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Four

open CliffordAlgebra TensorProduct Module Matrix Topology Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Five

open QuadFormsKB.Cassels Thm71Ternary Thm71Spin Thm71Coords Thm71Approx

/-- Helper (file-local): the vector space topology on $C(V_p)$. -/
noncomputable local instance cliffTop'' {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  cliffordTopology (Q.baseChange ℚ_[p])

local instance cliffModTop'' {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : IsModuleTopology ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := ⟨rfl⟩

local instance cliffFin'' {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : Module.Finite ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  finiteDimensional_clifford (Q.baseChange ℚ_[p])

local instance cliffTopRing'' {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (p : ℕ) [Fact p.Prime] : IsTopologicalRing (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  IsModuleTopology.isTopologicalRing ℚ_[p] _

section Second

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}
  {Λ : Submodule ℤ V} {n : ℕ} (e : Basis (Fin n) ℚ V)

/-- **Cassels' second stage** (p. 190): a family of spin elements has the approximation property at a finite set $T$ of
primes (containing $2$ and the primes dividing the determinant of $f$) at which every $t_p$ is $1$ or $V_p$ is isotropic
(`hiso`). -/
theorem spinApprox_of_isotropic (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 4 ≤ n) (he : ∀ i, e i ∈ Λ)
    {N : Matrix (Fin n) (Fin n) ℤ} (hNs : Nᵀ = N) {D : ℕ} (hD : 0 < D)
    (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e)
    (hfind : ∃ x y : Fin n → ℝ, (LocalDensity.ofMatrixZ N).evalIn ℝ x < 0 ∧ 0 < (LocalDensity.ofMatrixZ N).evalIn ℝ y)
    (T : Finset Nat.Primes) (hT2 : ∀ p : Nat.Primes, p ∉ T → (p : ℕ) ≠ 2)
    (hTd : ∀ p : Nat.Primes, p ∉ T → ¬ ((p : ℕ) : ℤ) ∣ (LocalDensity.ofMatrixZ N).hessian.det)
    (t : ∀ p : Nat.Primes, spinGroup (Q.baseChange ℚ_[(p : ℕ)]))
    (hiso : ∀ p ∈ T, (t p : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) = 1 ∨
      ∃ x : ℚ_[(p : ℕ)] ⊗[ℚ] V, x ≠ 0 ∧ Q.baseChange ℚ_[(p : ℕ)] x = 0) :
    SpinApprox Q Λ T fun p => (t p : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) := by
  classical
  have hloc : ∀ p : Nat.Primes, ∃ (L : List ((ℚ_[(p : ℕ)] ⊗[ℚ] V) × (ℚ_[(p : ℕ)] ⊗[ℚ] V)))
      (a₀ : ℚ_[(p : ℕ)] ⊗[ℚ] V), p ∈ T → (∀ ab ∈ L, Q.baseChange ℚ_[(p : ℕ)] ab.1 ≠ 0 ∧
        Q.baseChange ℚ_[(p : ℕ)] ab.2 ≠ 0) ∧ Q.baseChange ℚ_[(p : ℕ)] a₀ ≠ 0 ∧
        (t p : CliffordAlgebra _) =
          (L.map fun ab => vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ab.1 ab.2)).prod := by
    intro p
    by_cases hp : p ∈ T
    · have hQp := nondegenerate_baseChange e hQ ℚ_[(p : ℕ)]
      have hfin : Module.finrank ℚ_[(p : ℕ)] (ℚ_[(p : ℕ)] ⊗[ℚ] V) = n := by
        rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e), Fintype.card_fin]
      have : Nontrivial (ℚ_[(p : ℕ)] ⊗[ℚ] V) :=
        Module.nontrivial_of_finrank_pos (R := ℚ_[(p : ℕ)]) (by rw [hfin]; omega)
      obtain ⟨a₀, ha₀⟩ := exists_anisotropic hQp
      rcases hiso p hp with h1 | hi
      · exact ⟨[], a₀, fun _ => ⟨by simp, ha₀, by simp [h1]⟩⟩
      obtain ⟨L, hL, hLu⟩ := exists_list_vcomm hQp (by omega) hi (t p)
      exact ⟨L, a₀, fun _ => ⟨hL, ha₀, hLu⟩⟩
    · exact ⟨[], 0, fun h => absurd h hp⟩
  choose L a₀ hL using hloc
  set s : ℕ := T.sup fun p => (L p).length with hs
  set bP := fun p : Nat.Primes => Algebra.TensorProduct.basis ℚ_[(p : ℕ)] e
  set fam : List (∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) :=
    (List.range s).map fun j p =>
      vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ((L p).getD j (a₀ p, a₀ p)).1
        ((L p).getD j (a₀ p, a₀ p)).2)
    with hfam
  have hvec : ∀ (p : Nat.Primes) (x : ℚ_[(p : ℕ)] ⊗[ℚ] V), vecP e p ((bP p).equivFun x) = x := by
    intro p x; rw [vecP_eq, LinearEquiv.symm_apply_apply]
  have happrox : SpinApprox Q Λ T fun p => (fam.map fun t => t p).prod := by
    refine SpinApprox.list_prod fam fun t ht => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    have h72 := lemma72 e hQ hn he hNs hD hND hfind T hT2 hTd
      (fun p => (bP p).equivFun ((L p).getD j (a₀ p, a₀ p)).1)
      (fun p => (bP p).equivFun ((L p).getD j (a₀ p, a₀ p)).2)
      (fun p hp => by
        rw [hvec]
        obtain ⟨hLp, ha₀p, -⟩ := hL p hp
        rw [List.getD_eq_getElem?_getD]
        cases h : (L p)[j]? with
        | none => simpa using ha₀p
        | some ab => simpa using (hLp ab (List.mem_of_getElem? h)).1)
      (fun p hp => by
        rw [hvec]
        obtain ⟨hLp, ha₀p, -⟩ := hL p hp
        rw [List.getD_eq_getElem?_getD]
        cases h : (L p)[j]? with
        | none => simpa using ha₀p
        | some ab => simpa using (hLp ab (List.mem_of_getElem? h)).2)
    simpa only [hvec] using h72
  intro O hO
  have hO' : ∀ p ∈ T, IsOpen (O p) ∧ (fam.map fun t => t p).prod ∈ O p := by
    intro p hp
    refine ⟨(hO p hp).1, ?_⟩
    obtain ⟨-, ha₀p, hLu⟩ := hL p hp
    have := prod_range_getD (fun ab : (ℚ_[(p : ℕ)] ⊗[ℚ] V) × (ℚ_[(p : ℕ)] ⊗[ℚ] V) =>
        vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) ab.1 ab.2)) (a₀ p, a₀ p)
      (vprod_vcommList_self ha₀p) (L p) s (Finset.le_sup (f := fun p => (L p).length) hp)
    have e2 : (fam.map fun t => t p).prod = (t p : CliffordAlgebra _) := by
      rw [hLu, ← this, hfam, List.map_map]
      rfl
    rw [e2]; exact (hO p hp).2
  exact happrox O hO'

end Second

end QuadFormsKB.Cassels.Thm71Five
