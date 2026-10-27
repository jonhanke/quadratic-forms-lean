/-
# O'Meara §91B: the index of the rotations in the group of units (91:4a)

**Setting** (as in `Sec82.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, a
finite-dimensional regular quadratic space $(V, Q)$ over $F$, O'Meara's bilinear form $B$ = `bil Q`, lattices =
`Submodule R V`.

**Defines** the rotations $O^+(V)$ (`orthPlus`), $O^+(L) = O(L) \cap O^+(V)$ (`orthLatPlus`) and the proper class
$\operatorname{cls}^+ L$ (`clsPlus`) (O'Meara 1963, §82C, pp. 222–223).

**Proves**
* `det_symmetry`: $\det \tau_u = -1$ (O'Meara 1963, §43A, p. 100);
* `relIndex_orthLatPlus` (**91:4a**, p. 241): $(O(L) : O^+(L)) = 2$ for a lattice $L$ on a regular non-zero space;
* `clsPlus_eq_cls` (**91:4a**, second part, with 82:3): $\operatorname{cls}^+ L = \operatorname{cls} L$.
-/
import QuadFormsKB.Literature.OMeara.Sec91Type

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The rotations** $O^+(V)$ (O'Meara 1963, §43A, p. 100): the isometries of determinant $1$. -/
@[kb "omeara1963" "§43A, p. 100 (rotations O⁺(V))"]
def orthPlus : Subgroup (V ≃ₗ[F] V) := orth Q ⊓ (LinearEquiv.det).ker

/-- **$O^+(L) = O(L) \cap O^+(V)$** (O'Meara 1963, §82C, p. 223). -/
@[kb "omeara1963" "§82C, p. 223 (O⁺(L) = O(L) ∩ O⁺(V))"]
def orthLatPlus (L : Submodule R V) : Subgroup (V ≃ₗ[F] V) := orthLat Q L ⊓ orthPlus Q

/-- **The proper class** $\operatorname{cls}^+ L$ (O'Meara 1963, §82C, p. 222): the lattices $\sigma L$ with
$\sigma \in O^+(V)$. -/
@[kb "omeara1963" "§82C, p. 222 (the proper class cls⁺ L)"]
def clsPlus (L : Submodule R V) : Set (Submodule R V) :=
  {K | ∃ σ ∈ orthPlus Q, K = latMap σ L}

end Defs

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
  [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- Determinant of `id - f ⊗ u` when `f u = 2`. -/
theorem det_refl_aux (f : Dual F V) (u : V) (hf : f u = 2) :
    LinearMap.det (LinearMap.id - f.smulRight u) = -1 := by
  classical
  let b := Module.finBasis F V
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (LinearMap.id - f.smulRight u) =
      1 - Matrix.replicateCol Unit (fun i => b.repr u i) *
        Matrix.replicateRow Unit (fun j => f (b j)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol,
      Matrix.replicateRow, sub_eq_add_neg, Finsupp.single_apply, eq_comm, mul_comm]
  rw [this, Matrix.det_one_sub_mul_comm]
  have hu : f u = ∑ j, f (b j) * b.repr u j := by
    conv_lhs => rw [← b.sum_repr u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  simp [Matrix.mul_apply, ← hu, hf]
  norm_num

/-- On a regular space, every isometry has determinant $\pm 1$. -/
theorem det_orth_eq (hV : (QuadraticMap.associated Q).Nondegenerate) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ orth Q) : LinearEquiv.det σ = 1 ∨ LinearEquiv.det σ = -1 := by
  classical
  let b := Module.finBasis F V
  set B := QuadraticMap.associated (R := F) Q with hB
  have hcomp : LinearMap.BilinForm.comp B (σ : V →ₗ[F] V) (σ : V →ₗ[F] V) = B := by
    ext x y
    have h1 := hσ (x + y)
    have h2 := hσ x
    have h3 := hσ y
    rw [map_add, Q_add, Q_add, h2, h3] at h1
    have h4 : (2 : F) * bil Q (σ x) (σ y) = 2 * bil Q x y := by linear_combination h1
    have h5 := mul_left_cancel₀ (two_ne_zero (α := F)) h4
    simpa [LinearMap.BilinForm.comp_apply] using h5
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B (σ : V →ₗ[F] V) (σ : V →ₗ[F] V)
  rw [hcomp] at hmat
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  have hG : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hV
  have hsq : (LinearMap.det (σ : V →ₗ[F] V)) ^ 2 = 1 := by
    apply mul_right_cancel₀ hG
    linear_combination -hdet
  have hu : ((LinearEquiv.det σ : Fˣ) : F) ^ 2 = 1 := by
    rw [LinearEquiv.coe_det]; exact hsq
  have : ((LinearEquiv.det σ : Fˣ) : F) = 1 ∨ ((LinearEquiv.det σ : Fˣ) : F) = -1 :=
    by
      set a : F := ((LinearEquiv.det σ : Fˣ) : F)
      rcases mul_eq_zero.mp (show (a - 1) * (a + 1) = 0 by linear_combination hu) with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases this with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by simpa using h))

/-- For a unit of $L$, membership in $O^+(L)$ means determinant $1$. -/
theorem mem_orthLatPlus_iff {L : Submodule R V} {σ : V ≃ₗ[F] V} (h : σ ∈ orthLat Q L) :
    σ ∈ orthLatPlus Q L ↔ LinearEquiv.det σ = 1 :=
  ⟨fun H => H.2.2, fun H => ⟨h, h.1, H⟩⟩

/-- **A symmetry has determinant $-1$** (O'Meara 1963, §43A, p. 100). -/
@[kb "omeara1963" "§43A, p. 100 (det τ_u = −1)"]
theorem det_symmetry {u : V} (hu : Q u ≠ 0) : LinearEquiv.det (symmetry Q u hu) = -1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have h := det_refl_aux (symmForm Q u) u (symmForm_self Q hu)
  convert h using 2
  ext x
  simp [symmetry, Module.reflection_apply]

/-- **91:4a** (O'Meara 1963, p. 241): for a lattice $L$ on a regular non-zero quadratic space $V$ over a local field,
$(O(L) : O^+(L)) = 2$. (Only the discrete valuation ring is used.) -/
@[kb "omeara1963" "§91B, 91:4a, p. 241"]
theorem relIndex_orthLatPlus (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    {L : Submodule R V} (hL : L.IsLattice F) : (orthLatPlus Q L).relIndex (orthLat Q L) = 2 := by
  obtain ⟨u, -, hu, hτ⟩ := exists_symmetry_mem_orthLat Q hV hL
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    have h2 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h2
    have : (2 : F) = 0 := by linear_combination -h2
    exact two_ne_zero this
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨_, hτ⟩, fun b => ?_⟩
  have hb := det_orth_eq Q hV b.2.1
  have hmem : ∀ c : orthLat Q L, c ∈ (orthLatPlus Q L).subgroupOf (orthLat Q L) ↔
      LinearEquiv.det (c : V ≃ₗ[F] V) = 1 := fun c => mem_orthLatPlus_iff Q c.2
  rw [hmem, hmem]
  have hd : LinearEquiv.det ((b * ⟨_, hτ⟩ : orthLat Q L) : V ≃ₗ[F] V) =
      LinearEquiv.det (b : V ≃ₗ[F] V) * -1 := by
    rw [← det_symmetry Q hu, ← map_mul]; rfl
  rw [hd]
  rcases hb with h | h
  · rw [h]; simp [hne]
  · rw [h]; simp [hne]

/-- **91:4a, second part** (O'Meara 1963, p. 241, with 82:3): $\operatorname{cls}^+ L = \operatorname{cls} L$ for a
lattice $L$ on a regular non-zero quadratic space over a local field. -/
@[kb "omeara1963" "§91B, 91:4a, p. 241 (cls L = cls⁺ L)"]
theorem clsPlus_eq_cls (hV : (QuadraticMap.associated Q).Nondegenerate) [Nontrivial V]
    {L : Submodule R V} (hL : L.IsLattice F) : clsPlus Q L = cls Q L := by
  ext K
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ.1, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    rcases det_orth_eq Q hV hσ with h | h
    · exact ⟨σ, ⟨hσ, h⟩, rfl⟩
    · obtain ⟨u, -, hu, hτ⟩ := exists_symmetry_mem_orthLat Q hV hL
      refine ⟨σ * symmetry Q u hu, ⟨(orth Q).mul_mem hσ hτ.1, ?_⟩, ?_⟩
      · show LinearEquiv.det (σ * symmetry Q u hu) = 1
        rw [map_mul, h, det_symmetry Q hu]; simp
      · have : ((σ * symmetry Q u hu : V ≃ₗ[F] V) : V →ₗ[F] V).restrictScalars R =
            ((σ : V →ₗ[F] V).restrictScalars R).comp
              ((symmetry Q u hu : V →ₗ[F] V).restrictScalars R) := rfl
        have h2 := hτ.2
        simp only [latMap] at h2 ⊢
        rw [this, Submodule.map_comp, h2]

end Main

end QuadFormsKB.OMeara
