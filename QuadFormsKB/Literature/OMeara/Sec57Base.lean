/-
# O'Meara §57: extension of scalars of a quaternion algebra, and 57:11 (similarity forms of 57:10)

**Setting.** Fields $F \subseteq E$ (an `Algebra F E`) of characteristic $\ne 2$; O'Meara's quaternion algebra
$\left(\frac{\alpha,\beta}{F}\right)$ is Mathlib's `ℍ[F,α,β]` (`QuaternionAlgebra F α 0 β`, defining base
$1, i, j, k$ with $i^2 = \alpha$, $j^2 = \beta$, $ij = k = -ji$). O'Meara's $E$-ification $EA$ of an $F$-algebra $A$
is the $E$-algebra `E ⊗[F] A`. Bundled central simple algebras and similarity as in `Sec52F.lean`.

**Proves**
* **57.r4** (§57A, p. 142): `defining_base_mul`, $x_ix_j = -x_jx_i \in Fx_k$;
* **57.r3** (§57A, p. 142): `algEquiv_baseChange`, $E\left(\frac{\alpha,\beta}{F}\right) \cong
  \left(\frac{\alpha,\beta}{E}\right)$ as $E$-algebras (same multiplication table);
* **57:11, first sentence** (p. 148): `isBrauerEquivalent_57_10`, the four parts of 57:10 with the isomorphism symbol
  replaced by the similarity symbol $\sim$.
-/
import QuadFormsKB.Literature.OMeara.Sec58Hasse

open scoped TensorProduct
open Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.QuatBase57

universe u

section BaseChange

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] (α β : F)

/-- The defining base of $\left(\frac{\alpha,\beta}{E}\right)$ as a quaternion basis over $F$ (with the images of
$\alpha, \beta$ in $E$). -/
def basisE : QuaternionAlgebra.Basis ℍ[E,algebraMap F E α,algebraMap F E β] α 0 β where
  i := ⟨0, 1, 0, 0⟩
  i_mul_i := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
  j := ⟨0, 0, 1, 0⟩
  j_mul_j := by ext <;> simp [Algebra.algebraMap_eq_smul_one]
  k := ⟨0, 0, 0, 1⟩
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- The natural $E$-algebra homomorphism $E \otimes_F \left(\frac{\alpha,\beta}{F}\right) \to
\left(\frac{\alpha,\beta}{E}\right)$, $e \otimes x \mapsto e\,x$. -/
def toBaseChange : E ⊗[F] ℍ[F,α,β] →ₐ[E] ℍ[E,algebraMap F E α,algebraMap F E β] :=
  Algebra.TensorProduct.lift (Algebra.ofId E _) (QuaternionAlgebra.lift (basisE α β))
    (fun _ _ => Algebra.commute_algebraMap_left _ _)

theorem toBaseChange_tmul (e : E) (x : ℍ[F,α,β]) :
    toBaseChange α β (e ⊗ₜ x) = algebraMap E _ e * QuaternionAlgebra.lift (basisE α β) x :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem toBaseChange_surjective : Function.Surjective (toBaseChange (E := E) α β) := by
  intro q
  refine ⟨q.re ⊗ₜ 1 + q.imI ⊗ₜ ⟨0, 1, 0, 0⟩ + q.imJ ⊗ₜ ⟨0, 0, 1, 0⟩ + q.imK ⊗ₜ ⟨0, 0, 0, 1⟩, ?_⟩
  have hI : QuaternionAlgebra.lift (basisE (E := E) α β) (⟨0, 1, 0, 0⟩ : ℍ[F,α,β]) = ⟨0, 1, 0, 0⟩ := by
    simp [QuaternionAlgebra.Basis.lift, basisE]
  have hJ : QuaternionAlgebra.lift (basisE (E := E) α β) (⟨0, 0, 1, 0⟩ : ℍ[F,α,β]) = ⟨0, 0, 1, 0⟩ := by
    simp [QuaternionAlgebra.Basis.lift, basisE]
  have hK : QuaternionAlgebra.lift (basisE (E := E) α β) (⟨0, 0, 0, 1⟩ : ℍ[F,α,β]) = ⟨0, 0, 0, 1⟩ := by
    simp [QuaternionAlgebra.Basis.lift, basisE]
  simp only [map_add, toBaseChange_tmul, map_one, mul_one, hI, hJ, hK]
  ext <;> simp [QuaternionAlgebra.algebraMap_eq]

/-- **57.r3: extension of scalars of a quaternion algebra** (O'Meara 1963, §57A, p. 142): for a field extension
$E/F$ and $\alpha,\beta \in F$, $E\left(\frac{\alpha,\beta}{F}\right) \cong \left(\frac{\alpha,\beta}{E}\right)$ as
$E$-algebras, by $e \otimes x \mapsto e\,x$ (the defining base of the first is a base of the second with the same
multiplication table). Here $E\left(\frac{\alpha,\beta}{F}\right)$ is `E ⊗[F] ℍ[F,α,β]`; no hypothesis on
$\alpha, \beta$ or the characteristic is needed. -/
@[kb "omeara1963" "§57A, p. 142 (E((α,β)/F) ≅ (α,β)/E)"]
def algEquiv_baseChange : E ⊗[F] ℍ[F,α,β] ≃ₐ[E] ℍ[E,algebraMap F E α,algebraMap F E β] :=
  AlgEquiv.ofBijective (toBaseChange α β) (by
    refine ⟨?_, toBaseChange_surjective α β⟩
    have h : Module.finrank E (E ⊗[F] ℍ[F,α,β]) = Module.finrank E ℍ[E,algebraMap F E α,algebraMap F E β] := by
      rw [Module.finrank_baseChange, QuaternionAlgebra.finrank_eq_four, QuaternionAlgebra.finrank_eq_four]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
      (f := (toBaseChange (E := E) α β).toLinearMap)).2 (toBaseChange_surjective α β))

@[simp]
theorem algEquiv_baseChange_tmul (e : E) (x : ℍ[F,α,β]) :
    algEquiv_baseChange α β (e ⊗ₜ x) = algebraMap E _ e * QuaternionAlgebra.lift (basisE α β) x :=
  toBaseChange_tmul α β e x

end BaseChange

/-- **57.r4** (O'Meara 1963, §57A, p. 142): in the defining base $1, x_1, x_2, x_3$ of $(\alpha,\beta)$,
$x_ix_j = -x_jx_i \in Fx_k$ for every permutation $i,j,k$ of $1,2,3$:
$x_1x_2 = x_3 = -x_2x_1$, $x_2x_3 = -\beta x_1 = -x_3x_2$, $x_3x_1 = -\alpha x_2 = -x_1x_3$. -/
@[kb "omeara1963" "§57A, p. 142 (x_i x_j = -x_j x_i ∈ F x_k)"]
theorem defining_base_mul {F : Type*} [Field F] (α β : F) :
    let x₁ : ℍ[F,α,β] := ⟨0, 1, 0, 0⟩
    let x₂ : ℍ[F,α,β] := ⟨0, 0, 1, 0⟩
    let x₃ : ℍ[F,α,β] := ⟨0, 0, 0, 1⟩
    (x₁ * x₂ = x₃ ∧ x₂ * x₁ = -x₃) ∧ (x₂ * x₃ = -β • x₁ ∧ x₃ * x₂ = β • x₁) ∧
      (x₃ * x₁ = -α • x₂ ∧ x₁ * x₃ = α • x₂) := by
  intro x₁ x₂ x₃
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> ext <;> simp [x₁, x₂, x₃]

/-! ### 57:11: 57:10 with similarity in place of isomorphism -/

section Similar

open CSA52

variable {F : Type u} [Field F] [Invertible (2 : F)]

/-- **57:11, first sentence** (O'Meara 1963, 57:11, p. 148): "for trivial reasons we can replace the isomorphism
symbol $\cong$ by the similarity symbol $\sim$ throughout the statement of 57:10". For nonzero
$\alpha,\beta,\gamma,\lambda,\mu$:
1. $(1,\alpha)\sim(1,-1)\sim(\alpha,-\alpha)$, and $(\alpha,-\alpha)\sim(\alpha,1-\alpha)$ if $\alpha \ne 1$;
2. $(\beta,\alpha)\sim(\alpha,\beta)\sim(\alpha\lambda^2,\beta\mu^2)$;
3. $(\alpha,\alpha\beta)\sim(\alpha,-\beta)$;
4. $(\alpha,\beta)\otimes(\alpha,\gamma)\sim(\alpha,\beta\gamma)\otimes(1,-1)$.
(The hypothesis $\alpha \ne 1$ in (1) is implicit in the book: $(\alpha, 1-\alpha)$ needs $1-\alpha \ne 0$.) -/
@[kb "omeara1963" "§57B, 57:11, p. 148 (57:10 with ∼ in place of ≅)"]
theorem isBrauerEquivalent_57_10 {α β γ l m : F} (hα : α ≠ 0) (hβ : β ≠ 0) (hγ : γ ≠ 0) (hl : l ≠ 0)
    (hm : m ≠ 0) :
    (IsBrauerEquivalent (quaternion 1 α one_ne_zero hα) (quaternion 1 (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero)) ∧
      IsBrauerEquivalent (quaternion 1 (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero))
        (quaternion α (-α) hα (neg_ne_zero.2 hα)) ∧
      ∀ h1 : α ≠ 1, IsBrauerEquivalent (quaternion α (-α) hα (neg_ne_zero.2 hα))
        (quaternion α (1 - α) hα (sub_ne_zero.2 (Ne.symm h1)))) ∧
    (IsBrauerEquivalent (quaternion β α hβ hα) (quaternion α β hα hβ) ∧
      IsBrauerEquivalent (quaternion α β hα hβ)
        (quaternion (α * l ^ 2) (β * m ^ 2) (mul_ne_zero hα (pow_ne_zero 2 hl)) (mul_ne_zero hβ (pow_ne_zero 2 hm)))) ∧
    IsBrauerEquivalent (quaternion α (α * β) hα (mul_ne_zero hα hβ)) (quaternion α (-β) hα (neg_ne_zero.2 hβ)) ∧
    IsBrauerEquivalent (tensor (quaternion α β hα hβ) (quaternion α γ hα hγ))
      (tensor (quaternion α (β * γ) hα (mul_ne_zero hβ hγ))
        (quaternion 1 (-1) one_ne_zero (neg_ne_zero.2 one_ne_zero))) := by
  obtain ⟨⟨e1⟩, ⟨e2⟩, e3⟩ := QuatIso57.algEquiv_one_chain (F := F) hα
  obtain ⟨e4⟩ := QuatIso57.algEquiv_swap (F := F) hα hβ
  obtain ⟨e5⟩ := QuatIso57.algEquiv_scale (F := F) hα hβ hl hm
  obtain ⟨e6⟩ := QuatIso57.algEquiv_mul_neg (F := F) hα hβ
  obtain ⟨e7⟩ := QuatIso57.nonempty_algEquiv_tensor (F := F) hα hβ hγ
  refine ⟨⟨isBrauerEquivalent_of_algEquiv e1, isBrauerEquivalent_of_algEquiv e2, fun h1 => ?_⟩,
    ⟨isBrauerEquivalent_of_algEquiv e4, (isBrauerEquivalent_of_algEquiv e5).symm⟩,
    isBrauerEquivalent_of_algEquiv e6, isBrauerEquivalent_of_algEquiv e7⟩
  obtain ⟨e⟩ := e3 h1
  exact isBrauerEquivalent_of_algEquiv e

end Similar

end QuadFormsKB.OMeara.QuatBase57
