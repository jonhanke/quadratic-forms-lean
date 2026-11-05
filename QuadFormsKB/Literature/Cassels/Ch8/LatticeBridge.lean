/-
# Cassels, Chapter 8: bridge from Cassels' matrices over $\mathbb Q_p$ to O'Meara's lattices

Cassels works with a form $f(\vec x) = \vec x^{t}F\vec x$, $F \in M_n(\mathbb Q_p)$ symmetric, and with
$\mathbb Z_p$-equivalence; the library's O'Meara files (`Literature/OMeara/Sec82.lean` …) work with a quadratic space
$(V, Q)$ over a local field and lattices `Submodule R V`. This file identifies the two settings for
$V = \mathbb Q_p^n$, $Q = f$ (`qfForm F`, Mathlib's `Matrix.toQuadraticForm'`), $R = \mathbb Z_p$ and the lattice
$\mathbb Z_p^n$ (`zpLat n`, the $\mathbb Z_p$-span of the standard basis):
* `qfForm_apply`, `bil_qfForm`: $Q(\vec x) = f(\vec x)$ and O'Meara's $B(\vec x, \vec y) = \vec x^{t}F\vec y$;
* `mem_zpLat`: $\vec x \in \mathbb Z_p^n$ iff `IsIntVec x`; `zpLat_isLattice`: it is a lattice on $\mathbb Q_p^n$;
* `isIntAut_iff_mem_orthLat`: Cassels' integral automorphs are O'Meara's units $O(\mathbb Z_p^n)$;
* `symmetry_eq_tauFun`: O'Meara's symmetry $\tau_u$ is Cassels' $\tau_u$ ((3.7), p. 113).

No `kb` tags: these are notational identifications.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Bases
import QuadFormsKB.Literature.OMeara.Sec92Cancel
import QuadFormsKB.Literature.OMeara.Sec91Type

namespace QuadFormsKB.Cassels

open Matrix Submodule

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- $2$ is invertible in $\mathbb Q_p$ (needed by O'Meara's bilinear form $B = \frac12$ polar form). -/
noncomputable instance invertibleTwoPadic : Invertible (2 : ℚ_[p]) := invertibleOfNonzero two_ne_zero

/-- Cassels' form $f(\vec x) = \vec x^{t}F\vec x$ as a Mathlib quadratic form on $\mathbb Q_p^n$. -/
noncomputable abbrev qfForm (F : Matrix (Fin n) (Fin n) ℚ_[p]) : QuadraticForm ℚ_[p] (Fin n → ℚ_[p]) :=
  Matrix.toQuadraticForm' F

theorem qfForm_apply (F : Matrix (Fin n) (Fin n) ℚ_[p]) (x : Fin n → ℚ_[p]) : qfForm F x = qf F x := by
  simp [qfForm, qf, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- O'Meara's $B(\vec x, \vec y)$ for $Q = f$ with $F$ symmetric is $\vec x^{t}F\vec y$ (half of `bil F`). -/
theorem bil_qfForm {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) (x y : Fin n → ℚ_[p]) :
    OMeara.bil (qfForm F) x y = x ⬝ᵥ (F *ᵥ y) := by
  have hs : y ⬝ᵥ F *ᵥ x = x ⬝ᵥ F *ᵥ y := by
    have : y ᵥ* F = F *ᵥ y := by rw [← Matrix.vecMul_transpose, hF]
    rw [Matrix.dotProduct_mulVec, this, dotProduct_comm]
  have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated (S := ℚ_[p]) (qfForm F))
  simp only [LinearMap.smul_apply, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    qfForm_apply, qf_add, bil, hs] at h
  rw [two_nsmul] at h
  change QuadraticMap.associated (qfForm F) x y = _
  linear_combination (1 / 2 : ℚ_[p]) * h

variable (p) in
/-- The lattice $\mathbb Z_p^n \subset \mathbb Q_p^n$: the $\mathbb Z_p$-span of the standard basis. -/
noncomputable abbrev zpLat (n : ℕ) : Submodule ℤ_[p] (Fin n → ℚ_[p]) :=
  span ℤ_[p] (Set.range (Pi.basisFun ℚ_[p] (Fin n)))

theorem mem_zpLat {x : Fin n → ℚ_[p]} : x ∈ zpLat p n ↔ IsIntVec x := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ i
    simpa [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, Algebra.smul_def, PadicInt.algebraMap_apply]
      using (c i).2
  · intro h
    refine ⟨fun i => ⟨x i, h i⟩, ?_⟩
    ext i
    simp only [Finset.sum_apply, Pi.basisFun_apply]
    rw [Finset.sum_eq_single i]
    · change ((⟨x i, h i⟩ : ℤ_[p]) • (Pi.single i (1 : ℚ_[p]) : Fin n → ℚ_[p]) i) = x i
      rw [Pi.single_eq_same, Algebra.smul_def, mul_one]
      rfl
    · intro j _ hj
      change ((⟨x j, h j⟩ : ℤ_[p]) • (Pi.single j (1 : ℚ_[p]) : Fin n → ℚ_[p]) i) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
    · simp

theorem zpLat_isLattice : (zpLat p n).IsLattice ℚ_[p] := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [Submodule.span_span_of_tower]
  exact (Pi.basisFun ℚ_[p] (Fin n)).span_eq

/-- Cassels' integral automorphs (`IsIntAut`) are O'Meara's units $O(L)$ of $L = \mathbb Z_p^n$. -/
theorem isIntAut_iff_mem_orthLat (F : Matrix (Fin n) (Fin n) ℚ_[p])
    (σ : (Fin n → ℚ_[p]) ≃ₗ[ℚ_[p]] (Fin n → ℚ_[p])) :
    IsIntAut F σ ↔ σ ∈ OMeara.orthLat (qfForm F) (zpLat p n) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun x => by rw [qfForm_apply, qfForm_apply]; exact h1 x, ?_⟩
    ext x
    simp only [OMeara.latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_zpLat.2 (h2 y (mem_zpLat.1 hy))
    · intro hx
      exact ⟨σ.symm x, mem_zpLat.2 (h3 x (mem_zpLat.1 hx)), by simp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x => by rw [← qfForm_apply, ← qfForm_apply]; exact h1 x, fun x hx => ?_, fun x hx => ?_⟩
    · have : σ x ∈ OMeara.latMap σ (zpLat p n) := ⟨x, mem_zpLat.2 hx, rfl⟩
      rw [h2] at this
      exact mem_zpLat.1 this
    · have hx' : x ∈ OMeara.latMap σ (zpLat p n) := by rw [h2]; exact mem_zpLat.2 hx
      obtain ⟨y, hy, rfl⟩ := hx'
      simpa using mem_zpLat.1 hy

/-- O'Meara's symmetry $\tau_u$ (`OMeara.symmetry`) is Cassels' $\tau_u$ (`tauFun`, (3.7)). -/
theorem symmetry_eq_tauFun {F : Matrix (Fin n) (Fin n) ℚ_[p]} (hF : Fᵀ = F) {u : Fin n → ℚ_[p]}
    (hu : qfForm F u ≠ 0) (x : Fin n → ℚ_[p]) : OMeara.symmetry (qfForm F) u hu x = tauFun F u x := by
  have hs : u ⬝ᵥ F *ᵥ x = x ⬝ᵥ F *ᵥ u := by
    have : u ᵥ* F = F *ᵥ u := by rw [← Matrix.vecMul_transpose, hF]
    rw [Matrix.dotProduct_mulVec, this, dotProduct_comm]
  rw [OMeara.symmetry_apply, tauFun_apply, bil_qfForm hF, qfForm_apply]
  simp only [bil, hs]
  congr 2
  ring

end QuadFormsKB.Cassels
