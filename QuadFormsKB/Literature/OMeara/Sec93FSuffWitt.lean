/-
# Witt's theorem for regular sublattices

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a regular
finite-dimensional quadratic space $(V, Q)$, lattices `Submodule R V`.

**Proves** (O'Meara 1963, 42:17, Witt's theorem, applied to lattices, as used in the proof of 93:28, p. 273:
"we can assume that $L_1 = K_1$ by Witt's theorem")
* `exists_orth_latMap_eq`: an isometry $A \cong B$ of regular sublattices of $V$ is induced by some $\sigma \in O(V)$:
  $\sigma A = B$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffRed
import QuadFormsKB.Witt.Extension

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffWitt

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Witt's theorem for lattices** (O'Meara 1963, 42:17, p. 98): if $A$, $B$ are regular finitely generated
sublattices of a regular quadratic space $V$ and $A \cong B$, then $\sigma A = B$ for some $\sigma \in O(V)$. -/
@[kb "omeara1963" "§42F, 42:17, p. 98 (Witt's theorem), for lattices; used in §93F, p. 273"]
theorem exists_orth_latMap_eq (hQ : (QuadraticMap.associated Q).Nondegenerate) {A B : Submodule R V}
    (hAfg : A.FG) (hAreg : IsRegular Q A) (h : IsometricLat Q Q A B) :
    ∃ σ ∈ orth Q, latMap σ A = B := by
  classical
  obtain ⟨f, hf⟩ := h
  obtain ⟨b⟩ := exists_basis (R := R) (F := F) hAfg
  obtain ⟨bF, hbF⟩ := exists_basis_span (F := F) b
  set σ₀ : span F (A : Set V) →ₗ[F] V := bF.constr F (fun i => (f (b i) : V)) with hσ₀
  have hσb : ∀ i, σ₀ (bF i) = (f (b i) : V) := fun i => by simp [hσ₀, Basis.constr_basis]
  have hbil := bil_eq_of_isometricLat Q Q f hf
  -- `σ₀` preserves `B`
  have hB : ∀ x y : span F (A : Set V), bil Q (σ₀ x) (σ₀ y) = bil Q (x : V) (y : V) := by
    intro x y
    have hx := bF.sum_repr x
    have hy := bF.sum_repr y
    rw [← hx, ← hy, map_sum, map_sum, Submodule.coe_sum, Submodule.coe_sum, bil_sum_left, bil_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bil_sum_right, bil_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, Submodule.coe_smul, Submodule.coe_smul, bil_smul_left, bil_smul_left, bil_smul_right,
      bil_smul_right, hσb, hσb, hbF, hbF, hbil]
  have hQσ : ∀ x : span F (A : Set V), Q (σ₀ x) = Q (x : V) := fun x => by
    rw [← bil_self, hB, bil_self]
  -- `σ₀` is injective
  have hinj : Function.Injective σ₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    obtain ⟨d, hd0, hd⟩ := exists_smul_mem_of_mem_span (F := F) (S := A) w.2
    have h0 : d • (w : V) = 0 := hAreg _ hd fun z hz => by
      obtain ⟨c, -, hc⟩ := exists_smul_mem_of_mem_span (F := F) (S := A) (subset_span hz : z ∈ span F (A : Set V))
      have := hB w ⟨z, subset_span hz⟩
      rw [hw, show bil Q 0 (σ₀ ⟨z, subset_span hz⟩) = 0 by simp [bil]] at this
      rw [bil_rsmul_left, ← this, mul_zero]
    have hdF : algebraMap R F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hd0
    have : (w : V) = 0 := by
      rw [← algebraMap_smul F d (w : V)] at h0
      exact (smul_eq_zero.mp h0).resolve_left hdF
    exact (Submodule.mem_bot F).mpr (Subtype.ext this)
  obtain ⟨ρ, hρ⟩ := QuadraticForm.exists_isometryEquiv_extend_of_associated Q hQ σ₀ hinj hQσ
  refine ⟨ρ.toLinearEquiv, fun v => ρ.map_app v, ?_⟩
  -- `ρ` agrees with `f` on `A`
  have hρA : ∀ a : A, ρ (a : V) = (f a : V) := by
    intro a
    have ha := b.sum_repr a
    have hav : (a : V) = ∑ i, (b.repr a i) • (b i : V) := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      rw [← this]; simp
    have hfa : (f a : V) = ∑ i, (b.repr a i) • (f (b i) : V) := by
      conv_lhs => rw [← ha]
      rw [map_sum, Submodule.coe_sum]; simp
    have hmem : (a : V) ∈ span F (A : Set V) := subset_span a.2
    have h1 := hρ ⟨a, hmem⟩
    simp only at h1
    rw [h1]
    have : (⟨(a : V), hmem⟩ : span F (A : Set V)) = ∑ i, (algebraMap R F (b.repr a i)) • bF i := by
      apply Subtype.ext
      rw [Submodule.coe_sum, hav]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, hbF, algebraMap_smul]
    rw [this, map_sum, hfa]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hσb, algebraMap_smul]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    have := hρA ⟨a, ha⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, QuadraticMap.IsometryEquiv.coe_toLinearEquiv]
      at this ⊢
    rw [this]; exact (f ⟨a, ha⟩).2
  · intro y hy
    obtain ⟨a, hay⟩ := f.surjective ⟨y, hy⟩
    have hy' : y = (f a : V) := by rw [hay]
    refine ⟨a, a.2, ?_⟩
    have := hρA a
    rw [hy']; simpa using this

end QuadFormsKB.OMeara.SuffWitt
