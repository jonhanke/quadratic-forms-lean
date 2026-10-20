/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.FormClassNF

/-!
# Isometry is preserved by base change; isometry is local–global in both directions

* `QuadForm.isometricIn_baseChange`: over a field $F$ in which $2 \ne 0$, an isometry of forms over $F$
  stays an isometry over every field extension $K$ of $F$ (the same matrix, mapped into $K$).
* `isometricIn_everywhere_of_isometricIn_nf`: forms isometric over a number field $F$ are
  isometric over every completion $F_v$.
* `isometricIn_iff_everywhere_nf`: together with `Tamagawa.FormClassNF.isometricIn_of_everywhere_nf`,
  nondegenerate forms over $F$ are isometric over $F$ if and only if they are isometric over every $F_v$.
-/

namespace QuadFormsKB

open Matrix

namespace QuadForm

variable {F : Type*} [Field F] {n : ℕ}

/-- A bilinear identity on all vectors determines the matrix. -/
private theorem matrix_eq_of_dotProduct {A B : Matrix (Fin n) (Fin n) F}
    (h : ∀ x y : Fin n → F, x ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ (B *ᵥ y)) : A = B := by
  ext i j
  simpa [mulVec_single, dotProduct_single, single_dotProduct] using h (Pi.single i 1) (Pi.single j 1)

/-- Twice the value: $2\,Q(x) = x^{\mathsf T} H x$, $H$ the Hessian, over any $F$-algebra. -/
private theorem two_mul_evalIn (K : Type*) [CommRing K] [Algebra F K] (Q : QuadForm F n) (x : Fin n → K) :
    2 * Q.evalIn K x = x ⬝ᵥ (Q.hessian.map (algebraMap F K) *ᵥ x) := by
  rw [hessian, Matrix.map_add _ (map_add _), Matrix.transpose_map, add_mulVec, dotProduct_add,
    ← evalIn_eq_dotProduct, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec,
    ← evalIn_eq_dotProduct, two_mul]

/-- The Hessian form of $Q(P x)$: $(Px)^{\mathsf T} H (P y) = x^{\mathsf T} (P^{\mathsf T} H P) y$. -/
private theorem dotProduct_conj {S : Type*} [CommRing S] (A P : Matrix (Fin n) (Fin n) S) (x y : Fin n → S) :
    (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ y)) = x ⬝ᵥ ((Pᵀ * A * P) *ᵥ y) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec, ← vecMul_vecMul, ← vecMul_vecMul,
    vecMul_transpose]

/-- **Isometry is preserved by base change.** Over a field $F$ with $2 \ne 0$, if $Q(P x) = R(x)$ for some
$P \in \mathrm{GL}_n(F)$, then the same $P$ (mapped into $K$) is an isometry of $Q$ and $R$ over every field
$K \supseteq F$: the relation $P^{\mathsf T} H_Q P = H_R$ of Hessians, which determines the forms when $2 \ne 0$,
is preserved by the ring map $F \to K$. -/
@[kb "omeara1963" "§42 [unverified]"]
theorem isometricIn_baseChange (h2 : (2 : F) ≠ 0) {Q R : QuadForm F n} (K : Type*) [Field K] [Algebra F K]
    (h : Q.IsometricIn F R) : Q.IsometricIn K R := by
  obtain ⟨P, hP, hPQ⟩ := h
  -- The Hessian relation over F.
  have hH : Pᵀ * Q.hessian * P = R.hessian := by
    refine (matrix_eq_of_dotProduct fun x y => ?_).symm
    have h1 := polar_eq_hessian F Q (P *ᵥ x) (P *ᵥ y)
    have h2' := polar_eq_hessian F R x y
    rw [← mulVec_add, hPQ, hPQ, hPQ] at h1
    simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h1 h2'
    rw [← h2', h1, dotProduct_conj]
  refine ⟨P.map (algebraMap F K), ?_, fun x => ?_⟩
  · rw [show (P.map (algebraMap F K)).det = algebraMap F K P.det from (RingHom.map_det _ _).symm]
    exact hP.map _
  · have h2K : (2 : K) ≠ 0 := by
      rw [← map_ofNat (algebraMap F K) 2]; exact (map_ne_zero _).mpr h2
    refine mul_left_cancel₀ h2K ?_
    rw [two_mul_evalIn, two_mul_evalIn, dotProduct_conj, ← hH, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map]

end QuadForm

open NumberField

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- **Isometry over $F$ gives isometry everywhere locally.** If two quadratic forms over a number field $F$ are
isometric over $F$, they are isometric over every completion $F_v$ (by base change,
`QuadForm.isometricIn_baseChange`). -/
@[kb "omeara1963" "§66:4 [unverified]"]
theorem isometricIn_everywhere_of_isometricIn_nf (Q R : QuadForm F n) (h : Q.IsometricIn F R) :
    NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  rintro (w | v)
  · exact QuadForm.isometricIn_baseChange h2 _ h
  · exact QuadForm.isometricIn_baseChange h2 _ h

/-- **Isometry is local–global (both directions).** Nondegenerate quadratic forms $Q, R$ over a number field $F$
are isometric over $F$ if and only if they are isometric over every completion $F_v$. -/
@[kb "omeara1963" "§66:4 [unverified]"]
theorem isometricIn_iff_everywhere_nf (Q R : QuadForm F n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn F R ↔ NFPlace.Everywhere (F := F) fun K _ _ => Q.IsometricIn K R :=
  ⟨isometricIn_everywhere_of_isometricIn_nf Q R, Tamagawa.FormClassNF.isometricIn_of_everywhere_nf Q R hQ hR⟩

end QuadFormsKB
