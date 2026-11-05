/-
# Even unimodular forms over $\mathbb{Z}_2$: classification by the determinant

**Layer:** forms over $\mathbb{Z}_2$ (`QuadForm ℤ_[2] n`).

**Proves** the $2$-adic analogue of `Siegel.Kneser.isometricGL_of_unimodular`
(`isometricGL_two_of_unimodular`): if the Hessian $H = C + C^{\mathsf T}$ of $Q$ (the Gram matrix of the polar
bilinear form; its diagonal is even) has unit determinant, and $Q'$ is a form over $\mathbb{Z}_2$ with
$\det H' = \det H$, then $Q$ and $Q'$ are $\mathrm{GL}_n(\mathbb{Z}_2)$-equivalent.

*Route.* Cassels, *Rational Quadratic Forms*, Ch. 8, Corollary to Lemma 4.1 (p. 119), in the form
`Cassels.dyadic_EU_equiv`: two symmetric $\mathbb{Z}_2$-integral matrices with even diagonal and unit determinant
(`dyadicEU`) whose determinants agree up to a unit square are $\mathbb{Z}_2$-equivalent (the proof splits off the
binary blocks $H = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $A = \begin{pmatrix}2&1\\1&2\end{pmatrix}$, uses
$A \perp A \cong H \perp H$, and separates $H^k$ from $H^{k-1} \perp A$ by the non-square $-3$). Here we transport the
Hessians to $\mathbb{Q}_2$ (`hessian_dyadicEU`), obtain $T \in \mathrm{GL}_n(\mathbb{Z}_2)$ with $T^{\mathsf T} H T = H'$,
descend this to $\mathbb{Z}_2$ by injectivity of $\mathbb{Z}_2 \to \mathbb{Q}_2$, and recover $Q'(x) = Q(Tx)$ from
$2Q(y) = y^{\mathsf T}Hy$ (`two_mul_eval`) since $2 \ne 0$ in the domain $\mathbb{Z}_2$.
-/
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic

open Matrix QuadFormsKB

namespace QuadFormsKB.Cassels.Ch9EvenUnimodularTwo

variable {n : ℕ}

/-- The identity $2\,Q(\vec y) = \vec y^{\mathsf T} H \vec y$ over $\mathbb{Z}_2$, where $H$ is the Hessian of $Q$. -/
theorem two_mul_eval (Q : QuadForm ℤ_[2] n) (y : Fin n → ℤ_[2]) :
    2 * Q.eval y = y ⬝ᵥ (Q.hessian *ᵥ y) := by
  have h := QuadForm.polar_eq_hessian ℤ_[2] Q y y
  have e : Q.hessian.map (algebraMap ℤ_[2] ℤ_[2]) = Q.hessian := by ext; simp
  rw [e] at h
  rw [← h]
  have : Q.evalIn ℤ_[2] (y + y) = 4 * Q.evalIn ℤ_[2] y := by
    simp only [QuadForm.evalIn, Pi.add_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp; ring
  rw [this]; ring

/-- The determinant commutes with the inclusion $\mathbb{Z}_2 \to \mathbb{Q}_2$ applied entrywise. -/
theorem map_det_coe (M : Matrix (Fin n) (Fin n) ℤ_[2]) :
    (M.map PadicInt.Coe.ringHom).det = PadicInt.Coe.ringHom M.det :=
  (RingHom.map_det _ M).symm

/-- The Hessian of a form over $\mathbb{Z}_2$ with unit Hessian determinant, viewed over $\mathbb{Q}_2$, is an even
unimodular matrix (`dyadicEU`): symmetric, integral, with diagonal in $2\mathbb{Z}_2$ and determinant of norm $1$. -/
theorem hessian_dyadicEU (Q : QuadForm ℤ_[2] n) (hQ : IsUnit Q.hessian.det) :
    dyadicEU (Q.hessian.map PadicInt.Coe.ringHom) := by
  have hsymm : Q.hessianᵀ = Q.hessian := by
    simp [QuadForm.hessian, Matrix.transpose_add, add_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Matrix.transpose_map, hsymm]
  · intro i j
    exact PadicInt.norm_le_one (Q.hessian i j)
  · intro i
    have hd : Q.hessian i i = 2 * Q.coeff i i := by simp [QuadForm.hessian]; ring
    have h1 : (Q.hessian.map PadicInt.Coe.ringHom) i i = (2 : ℚ_[2]) * (Q.coeff i i : ℚ_[2]) := by
      rw [Matrix.map_apply, hd, map_mul, map_ofNat]; rfl
    rw [h1, norm_mul, dyadic_norm_two_q]
    have h2 : ‖((Q.coeff i i : ℤ_[2]) : ℚ_[2])‖ ≤ 1 := PadicInt.norm_le_one (Q.coeff i i)
    calc (2 : ℝ)⁻¹ * ‖((Q.coeff i i : ℤ_[2]) : ℚ_[2])‖ ≤ 2⁻¹ * 1 := by gcongr
      _ < 1 := by norm_num
  · rw [map_det_coe]
    exact (PadicInt.isUnit_iff.1 hQ)

/-- **Even unimodular forms over $\mathbb{Z}_2$ are classified by the determinant.**
Let $Q, Q'$ be quadratic forms in $n$ variables over $\mathbb{Z}_2$ whose Hessians (the Gram matrices
$H = C + C^{\mathsf T}$ of the polar bilinear forms, with even diagonal) satisfy $\det H \in \mathbb{Z}_2^{\times}$ and
$\det H' = \det H$. Then there is $g \in \mathrm{GL}_n(\mathbb{Z}_2)$ with $Q(g\vec x) = Q'(\vec x)$ for all
$\vec x \in \mathbb{Z}_2^n$. (Then $n$ is necessarily even.) Unconditional.

*Route:* Cassels, Ch. 8, Corollary to Lemma 4.1 (`dyadic_EU_equiv`); this is the even unimodular case of
O'Meara 93:16. -/
@[kb "cassels1978" "Ch. 8, Cor. to Lemma 4.1, p. 119 (even unimodular forms over ℤ₂)"]
theorem isometricGL_two_of_unimodular (Q Q' : QuadForm ℤ_[2] n)
    (hQ : IsUnit Q.hessian.det) (hdet : Q'.hessian.det = Q.hessian.det) :
    Siegel.IsometricGL Q Q' := by
  have hQ' : IsUnit Q'.hessian.det := hdet ▸ hQ
  have hrel : dyadicRel (Q.hessian.map PadicInt.Coe.ringHom) (Q'.hessian.map PadicInt.Coe.ringHom) :=
    ⟨1, by simp, by rw [map_det_coe, map_det_coe, hdet]; simp⟩
  obtain ⟨T, hT⟩ := dyadic_EU_equiv n _ _ (hessian_dyadicEU Q hQ) (hessian_dyadicEU Q' hQ') hrel
  have hT' : T.val.transpose * Q.hessian * T.val = Q'.hessian := by
    apply Matrix.map_injective (f := PadicInt.Coe.ringHom) (fun a b h => PadicInt.ext h)
    calc (T.val.transpose * Q.hessian * T.val).map PadicInt.Coe.ringHom
        = (T.val.map PadicInt.Coe.ringHom)ᵀ * Q.hessian.map PadicInt.Coe.ringHom *
            T.val.map PadicInt.Coe.ringHom := by
          rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      _ = _ := hT
  refine ⟨T, fun x => ?_⟩
  have h2 : (2 : ℤ_[2]) * Q.eval (T.val *ᵥ x) = 2 * Q'.eval x := by
    rw [two_mul_eval, two_mul_eval, ← hT', Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    have key : ∀ v : Fin n → ℤ_[2], x ⬝ᵥ (T.val.transpose *ᵥ v) = (T.val *ᵥ x) ⬝ᵥ v := fun v => by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact (key _).symm
  exact mul_left_cancel₀ (by norm_num) h2

end QuadFormsKB.Cassels.Ch9EvenUnimodularTwo
