/-
# Main Theorem 22.4.1 over a principal ideal domain with $2$ invertible in the fraction field (Voight)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021, Main Theorems 22.1.1 and 22.4.1 (p. 364),
Proposition 22.4.4, Proposition 22.4.12 (key `voight2021`).

**Statement** (`evenCliffordCorrespondence_of_two_ne_zero`). For every principal ideal domain $R$ whose fraction field
$F$ has $2 \ne 0$, `EvenCliffordCorrespondence R F` holds: $Q \mapsto \operatorname{Clf}^0(Q)$ is a bijection from
similarity classes of nondegenerate ternary quadratic forms over $R$ to isomorphism classes of quaternion $R$-orders.
This is Voight's Main Theorem 22.4.1 (`MainTheorem22_4_1`) under the extra hypothesis $\operatorname{char} F \ne 2$
(`mainTheorem_22_4_1_of_two_ne_zero`).

**Proof.** By `evenCliffordCorrespondence_iff_exists_clf0` it remains to show that every quaternion $R$-order $O$
(an abstract $R$-algebra, finitely generated and torsion-free, with $F \otimes_R O$ a quaternion algebra) is an even
Clifford algebra. Write $F \otimes_R O \cong (F[i], c_3 \mid F)$ with $i^2 = c_1 + c_2 i$; completing the square
($i \mapsto i - c_2/2$, `quatCompleteSquare`) gives $F \otimes_R O \cong (a, b \mid F)$ with $a = c_1 + c_2^2/4$,
$b = c_3$ nonzero. The map $O \to F \otimes_R O$, $x \mapsto 1 \otimes x$, is injective ($O$ is free, being finitely
generated and torsion-free over a principal ideal domain), and its image is an $R$-order in $(a, b \mid F)$. So
$O$ is isomorphic to an order in $(a, b \mid F)$, which is an even Clifford algebra by `OrderClf0.exists_clf0`.
-/
import QuadFormsKB.Literature.Voight.Wave2.OrderClf0

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion

universe u

namespace QuadFormsKB.Voight

/-- **Completing the square** (Voight 6.1.3): $(F[i], c_3 \mid F)$ with $i^2 = c_1 + 2m\,i$ is isomorphic to
$(c_1 + m^2, c_3 \mid F)$, via $i \mapsto i + m$. -/
def quatCompleteSquare {F : Type*} [CommRing F] (c₁ m c₃ : F) :
    ℍ[F, c₁ + m ^ 2, 0, c₃] ≃ₐ[F] ℍ[F, c₁, 2 * m, c₃] where
  toFun x := ⟨x.re - m * x.imI, x.imI, x.imJ - m * x.imK, x.imK⟩
  invFun x := ⟨x.re + m * x.imI, x.imI, x.imJ + m * x.imK, x.imK⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring
  map_add' x y := by ext <;> simp <;> ring
  commutes' r := by ext <;> simp [QuaternionAlgebra.algebraMap_eq]

section Abstract

variable {R : Type u} {F : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]

/-- **Every quaternion order over a principal ideal domain is an even Clifford algebra** (Voight 2021,
Proposition 22.4.4), when $2 \ne 0$ in the fraction field: the clause `exists_clf0` of Main Theorem 22.4.1. -/
@[kb "voight2021" "Proposition 22.4.4, p. 364"]
theorem exists_clf0_of_isQuaternionOrder (h2 : (2 : F) ≠ 0) (O : Type u) [Ring O] [Algebra R O]
    (hO : IsQuaternionOrder R F O) :
    ∃ Q : QuadForm R 3, ternaryDisc Q ≠ 0 ∧ Nonempty (O ≃ₐ[R] Clf0 Q) := by
  classical
  haveI := hO.finite
  haveI := hO.torsionFree
  obtain ⟨c₁, c₂, c₃, hsep, hc₃, ⟨ψ⟩⟩ := hO.quaternion
  obtain ⟨m, rfl⟩ : ∃ m, c₂ = 2 * m := ⟨c₂ / 2, by field_simp⟩
  have ha : c₁ + m ^ 2 ≠ 0 := by
    intro h; apply hsep; linear_combination 4 * h
  -- the isomorphism F ⊗ O ≃ (a, b | F)
  let χ : F ⊗[R] O ≃ₐ[F] ℍ[F, c₁ + m ^ 2, 0, c₃] := ψ.trans (quatCompleteSquare c₁ m c₃).symm
  let θ : O →ₐ[R] ℍ[F, c₁ + m ^ 2, 0, c₃] :=
    (χ.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight
  -- injectivity via a basis of O
  let b := Module.Free.chooseBasis R O
  have hθ : Function.Injective θ := by
    intro x y hxy
    have h1 : (1 : F) ⊗ₜ[R] x = 1 ⊗ₜ[R] y := χ.injective hxy
    have h2' := congrArg (Algebra.TensorProduct.basis F b).repr h1
    rw [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul, one_smul,
      one_smul] at h2'
    apply b.repr.injective
    ext i
    have := congrArg (fun f => f i) h2'
    simp only [Finsupp.mapRange_apply] at this
    exact IsFractionRing.injective R F this
  let O' : Subalgebra R ℍ[F, c₁ + m ^ 2, 0, c₃] := θ.range
  have hO' : QuatOrder.IsOrder R F O' := by
    constructor
    · have : Subalgebra.toSubmodule O' = Submodule.map θ.toLinearMap ⊤ := by
        ext z; simp [O']
      rw [this]
      exact (Module.Finite.fg_top).map _
    · rw [eq_top_iff]
      intro z _
      obtain ⟨y, rfl⟩ := χ.surjective z
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        have : χ (f ⊗ₜ[R] x) = f • θ x := by
          rw [show f ⊗ₜ[R] x = f • ((1 : F) ⊗ₜ[R] x) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
            map_smul]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
      | add y y' hy hy' => rw [map_add]; exact Submodule.add_mem _ (hy trivial) (hy' trivial)
  obtain ⟨Q, hQ, ⟨φ⟩⟩ := OrderClf0.exists_clf0 hO' h2 ha hc₃
  exact ⟨Q, hQ, ⟨(AlgEquiv.ofInjective θ hθ).trans φ⟩⟩

/-- **Main Theorem 22.4.1 (Voight 2021) when $2 \ne 0$**: for a principal ideal domain $R$ with fraction field $F$
in which $2 \ne 0$, the even Clifford algebra gives a bijection between similarity classes of nondegenerate ternary
quadratic forms over $R$ and isomorphism classes of quaternion $R$-orders (`EvenCliffordCorrespondence R F`).
Proved. -/
@[kb "voight2021" "Main Theorem 22.1.1, p. 353; Main Theorem 22.4.1, p. 364"]
theorem evenCliffordCorrespondence_of_two_ne_zero (h2 : (2 : F) ≠ 0) : EvenCliffordCorrespondence R F :=
  (evenCliffordCorrespondence_iff_exists_clf0 h2).2 fun O _ _ hO => exists_clf0_of_isQuaternionOrder h2 O hO

end Abstract

/-- **Main Theorem 22.4.1 (Voight 2021) for principal ideal domains whose fraction field has characteristic
$\ne 2$**: the statement `MainTheorem22_4_1` restricted to $2 \ne 0$ in $F$. Proved. -/
@[kb "voight2021" "Main Theorem 22.4.1, p. 364"]
theorem mainTheorem_22_4_1_of_two_ne_zero :
    ∀ (R F : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F]
      [IsFractionRing R F], (2 : F) ≠ 0 → EvenCliffordCorrespondence R F :=
  fun _ _ _ _ _ _ _ _ h2 => evenCliffordCorrespondence_of_two_ne_zero h2

end QuadFormsKB.Voight
