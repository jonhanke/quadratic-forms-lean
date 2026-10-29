/-
# The Weil relation for every symmetric $B$ from the diagonal case

**Layer:** pure algebra over a field $k$ with $2 \ne 0$.

**Diagonalization** (`exists_eq_mul_diagonal_mul_transpose`): every invertible symmetric $B \in M_g(k)$ is congruent to
a diagonal matrix, $B = P\operatorname{diag}(d_0, \dots, d_{g-1})P^{\mathsf T}$ with $P \in \mathrm{GL}_g(k)$, $d_j \in k^\times$.

**Reduction** (`siegelRelations_of_diag`): let $N, A, W$ be maps into a monoid satisfying the parabolic relations
(`N_zero`, `N_add`, `A_one`, `A_mul`, `A_N`), $WA(a) = A({}^ta^{-1})W$ and $W^2 = A(-1)$. If the Weil relation
$$WN(D)W = N(-D^{-1})\,A(-D^{-1})\,W\,N(-D^{-1})$$
holds for every invertible **diagonal** $D$, then it holds for every invertible symmetric $B$, i.e. `SiegelRelations`
holds. *Proof:* $N(B) = A(P)N(D)A(P)^{-1}$ by `A_N`; move $A(P^{\pm1})$ through $W$ by `W_A`, apply the diagonal case,
and move the Levi factors back, using $B^{-1} = {}^tP^{-1}D^{-1}P^{-1}$.

This is how the genus-$g$ Weil relation is reduced to $g$ copies of the one-variable relation (R6) in
`Weil/Genus/Model.lean`.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Lam, *Introduction to quadratic
forms over fields* (2005), Ch. I, Cor. 2.4 (diagonalization) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Symplectic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

variable {g : ℕ} {k : Type*} [Field k]

/-- The invertible diagonal matrix $\operatorname{diag}(d_0, \dots, d_{g-1})$ as an element of $\mathrm{GL}_g(k)$. -/
def diagGL {R : Type*} [CommRing R] (d : Fin g → Rˣ) : GL (Fin g) R where
  val := diagonal fun j => (d j : R)
  inv := diagonal fun j => (((d j)⁻¹ : Rˣ) : R)
  val_inv := by rw [diagonal_mul_diagonal]; simp
  inv_val := by rw [diagonal_mul_diagonal]; simp

@[simp] lemma diagGL_coe {R : Type*} [CommRing R] (d : Fin g → Rˣ) :
    ((diagGL d : GL (Fin g) R) : Matrix (Fin g) (Fin g) R) = diagonal fun j => (d j : R) := rfl

lemma diagGL_inv_coe {R : Type*} [CommRing R] (d : Fin g → Rˣ) :
    (((diagGL d)⁻¹ : GL (Fin g) R) : Matrix (Fin g) (Fin g) R) = diagonal fun j => (((d j)⁻¹ : Rˣ) : R) := rfl

/-- **Diagonalization of an invertible symmetric matrix** over a field with $2 \ne 0$:
$B = P\operatorname{diag}(d)P^{\mathsf T}$, $P \in \mathrm{GL}_g(k)$, $d_j \in k^\times$. -/
@[kb "lam2005" "Ch. I, Cor. 2.4 (every quadratic space has an orthogonal basis) [unverified]"]
theorem exists_eq_mul_diagonal_mul_transpose (h2 : (2 : k) ≠ 0) (B : GL (Fin g) k)
    (hB : (B : Matrix (Fin g) (Fin g) k)ᵀ = B) :
    ∃ (P : GL (Fin g) k) (d : Fin g → kˣ),
      (B : Matrix (Fin g) (Fin g) k) = (P : Matrix (Fin g) (Fin g) k) * diagonal (fun j => (d j : k)) *
        (P : Matrix (Fin g) (Fin g) k)ᵀ := by
  classical
  have : Invertible (2 : k) := invertibleOfNonzero h2
  set Bm : Matrix (Fin g) (Fin g) k := (B : Matrix (Fin g) (Fin g) k) with hBm
  have hsymm : (Matrix.toBilin' Bm).IsSymm := by
    rw [Matrix.isSymm_toBilin'_iff_isSymm]
    exact hB
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := Matrix.toBilin' Bm)
    (LinearMap.BilinForm.isSymm_iff.1 hsymm)
  have hr : Module.finrank k (Fin g → k) = g := by simp
  let v' : Module.Basis (Fin g) k (Fin g → k) := v.reindex (finCongr hr)
  have hv' : ∀ i j, i ≠ j → Matrix.toBilin' Bm (v' i) (v' j) = 0 := by
    intro i j hij
    simp only [v', Module.Basis.reindex_apply]
    exact hv (i := (finCongr hr).symm i) (j := (finCongr hr).symm j) (by simpa using hij)
  let Q : Matrix (Fin g) (Fin g) k := fun i j => v' j i
  have hQdet : IsUnit Q.det := by
    have := (Pi.basisFun k (Fin g)).isUnit_det v'
    rw [Module.Basis.det_apply] at this
    convert this using 2
    ext i j
    simp [Q, Module.Basis.toMatrix_apply]
  have hQD : Qᵀ * Bm * Q = diagonal (fun j => Matrix.toBilin' Bm (v' j) (v' j)) := by
    ext i j
    have h1 : (Qᵀ * Bm * Q) i j = Matrix.toBilin' Bm (v' i) (v' j) := by
      rw [Matrix.toBilin'_apply]
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_apply, Finset.sum_mul, Q]
      rw [Finset.sum_comm]
      rfl
    rw [h1]
    by_cases hij : i = j
    · subst hij; simp
    · rw [hv' i j hij]; simp [hij]
  have hQu : IsUnit Q := (isUnit_iff_isUnit_det Q).2 hQdet
  have hDu : IsUnit (diagonal (fun j => Matrix.toBilin' Bm (v' j) (v' j))) := by
    rw [← hQD, isUnit_iff_isUnit_det, det_mul, det_mul, det_transpose]
    have hBu : IsUnit Bm.det := (isUnit_iff_isUnit_det Bm).1 B.isUnit
    exact (hQdet.mul hBu).mul hQdet
  rw [isUnit_diagonal, Pi.isUnit_iff] at hDu
  let Qg : GL (Fin g) k := hQu.unit
  refine ⟨invT Qg, fun j => (hDu j).unit, ?_⟩
  have hQgi : Q * ((Qg⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) = 1 := Units.mul_inv Qg
  have hQgi' : ((Qg⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) * Q = 1 := Units.inv_mul Qg
  have hD : diagonal (fun j => (((hDu j).unit : kˣ) : k)) =
      diagonal (fun j => Matrix.toBilin' Bm (v' j) (v' j)) := by
    simp
  rw [hD, invT_coe, transpose_transpose, ← hQD]
  set Qi := ((Qg⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) with hQi
  calc Bm = (Qiᵀ * Qᵀ) * Bm * (Q * Qi) := by
        rw [← transpose_mul, hQgi, transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma invT_invT (a : GL (Fin g) k) : invT (invT a) = a := Units.ext (transpose_transpose _)

lemma inv_invT (a : GL (Fin g) k) : (invT a)⁻¹ = invT a⁻¹ := Units.ext rfl

/-- **The Weil relation for every invertible symmetric $B$ from the diagonal case** (see the module docstring). -/
@[kb "kudla1996" "§I.1 (relations among $m(a)$, $n(b)$, $w$; reduction to diagonal $b$) [unverified]"]
theorem siegelRelations_of_diag (h2 : (2 : k) ≠ 0) {M : Type*} [Monoid M]
    {N : Matrix (Fin g) (Fin g) k → M} {A : GL (Fin g) k → M} {W : M}
    (N_zero : N 0 = 1)
    (N_add : ∀ B B' : Matrix (Fin g) (Fin g) k, Bᵀ = B → B'ᵀ = B' → N (B + B') = N B * N B')
    (A_one : A 1 = 1) (A_mul : ∀ a a' : GL (Fin g) k, A (a * a') = A a * A a')
    (A_N : ∀ (a : GL (Fin g) k) (B : Matrix (Fin g) (Fin g) k), Bᵀ = B →
      A a * N B = N ((a : Matrix (Fin g) (Fin g) k) * B * (a : Matrix (Fin g) (Fin g) k)ᵀ) * A a)
    (W_A : ∀ a : GL (Fin g) k, W * A a = A (invT a) * W)
    (W_W : W * W = A (-1))
    (W_N_W_diag : ∀ d : Fin g → kˣ,
      W * N (diagonal fun j => (d j : k)) * W =
        N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)) * A (-(diagGL d)⁻¹) * W * N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k))) :
    SiegelRelations N A W := by
  refine
    { N_zero := N_zero, N_add := N_add, A_one := A_one, A_mul := A_mul, A_N := A_N, W_A := W_A, W_W := W_W,
      W_N_W := ?_ }
  intro B hB
  obtain ⟨P, d, hPd⟩ := exists_eq_mul_diagonal_mul_transpose h2 B hB
  set Pt : GL (Fin g) k := invT P⁻¹ with hPt
  have hPtc : (Pt : Matrix (Fin g) (Fin g) k) = (P : Matrix (Fin g) (Fin g) k)ᵀ := by simp [Pt]
  have hBG : B = P * diagGL d * Pt :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, hPtc, diagGL_coe]; exact hPd)
  have hBi : B⁻¹ = invT P * (diagGL d)⁻¹ * P⁻¹ := by
    rw [hBG, _root_.mul_inv_rev, _root_.mul_inv_rev, hPt, inv_invT, inv_inv]
    simp [mul_assoc]
  set Gm : GL (Fin g) k := -(diagGL d)⁻¹ with hGm
  have hneg : -B⁻¹ = invT P * Gm * P⁻¹ := by
    rw [hBi]
    apply Units.ext
    simp [Gm, Units.val_neg]
  have hE : -diagonal (fun j => (((d j)⁻¹ : kˣ) : k)) = (Gm : Matrix (Fin g) (Fin g) k) := by
    rw [hGm, Units.val_neg, diagGL_inv_coe]
  have hEs : ((Gm : Matrix (Fin g) (Fin g) k))ᵀ = Gm := by
    rw [← hE, transpose_neg, diagonal_transpose]
  have hDs : (diagonal (fun j => (d j : k)))ᵀ = diagonal (fun j => (d j : k)) := diagonal_transpose _
  have hFs := symm_neg_inv hB
  have hFc : (((-B⁻¹ : GL (Fin g) k)) : Matrix (Fin g) (Fin g) k) =
      -((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k) := Units.val_neg _
  have hAinv : A P * A P⁻¹ = 1 := by rw [← A_mul, mul_inv_cancel, A_one]
  have hNB : N (B : Matrix (Fin g) (Fin g) k) = A P * N (diagonal fun j => (d j : k)) * A P⁻¹ := by
    have h := A_N P _ hDs
    rw [← hPd] at h
    calc N (B : Matrix (Fin g) (Fin g) k)
        = (N (B : Matrix (Fin g) (Fin g) k) * A P) * A P⁻¹ := by
          rw [Monoid.mul_assoc, ← A_mul, mul_inv_cancel, A_one, mul_one]
      _ = _ := by rw [← h]
  have hW1 : W * A P = A (invT P) * W := W_A P
  have hW2 : W * A Pt = A P⁻¹ * W := by rw [W_A Pt, hPt, invT_invT]
  have h1 : A (invT P) * N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)) =
      N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) * A (invT P) := by
    have h := A_N (invT P) (Gm : Matrix (Fin g) (Fin g) k) hEs
    rw [hE]
    convert h using 3
    rw [← hFc, hneg]
    simp [invT_coe, Matrix.mul_assoc]
  have h2' : N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)) * A Pt =
      A Pt * N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) := by
    have h := A_N Pt _ hFs
    rw [hE]
    rw [h]
    congr 2
    rw [← hFc, hneg, hPtc]
    simp only [Units.val_mul, invT_coe, transpose_transpose, Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one,
      Matrix.one_mul]
  have h4 : A (invT P) * A Gm * A P⁻¹ = A (-B⁻¹) := by
    rw [← A_mul, ← A_mul, hneg]
  rw [hNB]
  calc W * (A P * N (diagonal fun j => (d j : k)) * A P⁻¹) * W
      = (W * A P) * N (diagonal fun j => (d j : k)) * (A P⁻¹ * W) := by simp only [Monoid.mul_assoc]
    _ = A (invT P) * (W * N (diagonal fun j => (d j : k)) * W) * A Pt := by
        rw [hW1, ← hW2]; simp only [Monoid.mul_assoc]
    _ = A (invT P) * (N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)) * A Gm * W *
          N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k))) * A Pt := by rw [W_N_W_diag d]
    _ = (A (invT P) * N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k))) * A Gm * W *
          (N (-diagonal fun j => (((d j)⁻¹ : kˣ) : k)) * A Pt) := by simp only [Monoid.mul_assoc]
    _ = _ := by
        rw [h1, h2', ← h4]
        calc _ = N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) * (A (invT P) * A Gm) * (W * A Pt) * N (-((B⁻¹ : GL (Fin g) k) : Matrix (Fin g) (Fin g) k)) := by
              simp only [Monoid.mul_assoc]
          _ = _ := by rw [hW2]; simp only [Monoid.mul_assoc]

end QuadFormsKB.WeilRep.Genus
