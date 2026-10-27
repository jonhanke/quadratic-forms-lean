/-
# O'Meara §52F: similarity of central simple algebras (running text, pp. 127-129)

**Setting.** $F$ a field.  O'Meara's central simple algebras over $F$ are Mathlib's bundled `CSA F`
(finite-dimensional, central, simple); his *similarity* $A \sim A'$ is Mathlib's `IsBrauerEquivalent`
(Sec52B proves that the two agree: `isBrauerEquivalent_iff_nonempty_algEquiv`).  The tensor product and
the reciprocal algebra are bundled here, in the sub-namespace `QuadFormsKB.OMeara.CSA52`, so that
similarity can be stated for them.

**Definitions** (all in `QuadFormsKB.OMeara.CSA52`)
* `ofAlg`: the bundled algebra of a central simple algebra given by instances;
* `tensor A B`: the bundled $A \otimes_F B$ (central simple by 52:1);
* `one`: the bundled $F$ (O'Meara's $1$ in "$A \sim 1$");
* `op A`: the bundled reciprocal algebra $A^*$ (the opposite algebra).

**Proves** (book page 128 unless stated)
* `isBrauerEquivalent_of_algEquiv`: isomorphic algebras are similar;
* `isBrauerEquivalent_tensor`: $A \sim A'$ and $B \sim B'$ imply $A \otimes B \sim A' \otimes B'$ (the case
  of two factors of the remark on $A_1 \otimes \cdots \otimes A_t$);
* `nonempty_algEquiv_tensor_comm`, `nonempty_algEquiv_tensor_assoc`, `nonempty_algEquiv_tensor_one` and their
  similarity forms: $A \otimes B \cong B \otimes A$, $(A \otimes B) \otimes C \cong A \otimes (B \otimes C)$,
  $A \otimes F \cong A$;
* `isBrauerEquivalent_one_iff`: $A \sim 1$ iff $A$ splits ($A \cong M_k(F)$, $k \ge 1$);
* `isBrauerEquivalent_tensor_of_left_one`: $A \sim 1$ implies $A \otimes B \sim B$;
* `isBrauerEquivalent_tensor_op` (**52:10** consequence, p. 128-129): $A \otimes A^* \sim 1$;
* `isBrauerEquivalent_of_tensor` (the cancellation law, p. 129): $A \otimes B \sim A' \otimes B$ implies
  $A \sim A'$;
* `isBrauerEquivalent_quaternion_tensor_self` (**57:11**, second assertion, p. 148):
  $(\alpha,\beta) \otimes (\alpha,\beta) \sim 1$.

*Not formalized:* the first assertion of 57:11, $(\alpha,\beta) \otimes (\alpha,\gamma) \sim (\alpha,\beta\gamma)$,
which needs 57:10 (4), proved elsewhere; and the $t$-fold statement $A_1 \otimes \cdots \otimes A_t \sim
A_1' \otimes \cdots \otimes A_t'$ (it follows from the two-factor case by induction).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec52A
import QuadFormsKB.Literature.OMeara.Sec52B
import QuadFormsKB.Literature.OMeara.Sec57

open scoped TensorProduct
open Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CSA52

universe u

variable {F : Type u} [Field F]

/-! ### The bundled algebras -/

/-- The bundled central simple algebra of an $F$-algebra $A$ that is central, simple and finite
dimensional over $F$ (Mathlib's `CSA`). -/
def ofAlg (A : Type u) [Ring A] [Algebra F A] [Algebra.IsCentral F A] [IsSimpleRing A]
    [FiniteDimensional F A] : CSA.{u, u} F where
  toAlgCat := AlgCat.of F A
  isCentral := show Algebra.IsCentral F A from inferInstance
  isSimple := show IsSimpleRing A from inferInstance
  fin_dim := show FiniteDimensional F A from inferInstance

/-- The bundled tensor product $A \otimes_F B$ of two central simple algebras, central simple by
O'Meara 52:1 (`isCentralSimple_tensorProduct`). -/
def tensor (A B : CSA.{u, u} F) : CSA.{u, u} F :=
  haveI : Algebra.IsCentral F (A ⊗[F] B) := isCentral_tensorProduct
  haveI : IsSimpleRing (A ⊗[F] B) := isSimpleRing_tensorProduct_of_isCentral
  ofAlg (A ⊗[F] B)

/-- The bundled algebra $F$ itself, O'Meara's $1$ in "$A \sim 1$" (§52F, p. 128). -/
def one : CSA.{u, u} F :=
  ofAlg F

/-- The bundled reciprocal algebra $A^*$ of §52F (p. 128), the opposite algebra `Aᵐᵒᵖ` (same vector space,
twisted product $a \times b = ba$). -/
def op (A : CSA.{u, u} F) : CSA.{u, u} F :=
  ofAlg (Aᵐᵒᵖ)

/-! ### Similarity: basic properties -/

/-- **O'Meara §52F, p. 128**: isomorphic central simple algebras are similar. -/
@[kb "omeara1963" "§52F, p. 128 (isomorphic algebras are similar)"]
theorem isBrauerEquivalent_of_algEquiv {A B : CSA.{u, u} F} (e : A ≃ₐ[F] B) :
    IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

/-- Similarity as in the remark of §52F (p. 128) with the matrix algebras written as tensor factors:
$A \sim A'$ iff $A \otimes M_r(F) \cong A' \otimes M_s(F)$ for some $r, s \ge 1$ (Sec52B,
`isBrauerEquivalent_iff_tensor`, restated on the bundled algebras). -/
theorem isBrauerEquivalent_iff_tensor_matrix (A A' : CSA.{u, u} F) :
    IsBrauerEquivalent A A' ↔ ∃ r s : ℕ, r ≠ 0 ∧ s ≠ 0 ∧
      Nonempty (A ⊗[F] Matrix (Fin r) (Fin r) F ≃ₐ[F] A' ⊗[F] Matrix (Fin s) (Fin s) F) :=
  isBrauerEquivalent_iff_tensor (A := A) (A' := A')

/-- $M_r(F) \otimes_F M_s(F) \cong M_{rs}(F)$ (Kronecker product, reindexed by `Fin (r * s)`). -/
def matrixTensorEquiv (r s : ℕ) :
    Matrix (Fin r) (Fin r) F ⊗[F] Matrix (Fin s) (Fin s) F ≃ₐ[F] Matrix (Fin (r * s)) (Fin (r * s)) F :=
  (Matrix.kroneckerAlgEquiv (Fin r) (Fin s) F).trans (Matrix.reindexAlgEquiv F F finProdFinEquiv)

/-- **O'Meara §52F, p. 128**: if $A \sim A'$ and $B \sim B'$ then $A \otimes B \sim A' \otimes B'$.
(O'Meara states the $t$-fold version; the case of two factors is the same argument and gives the $t$-fold
one by induction.)  Proof: write the similarities as $A \otimes M_r \cong A' \otimes M_s$ and
$B \otimes M_p \cong B' \otimes M_q$, and regroup the four tensor factors. -/
@[kb "omeara1963" "§52F, p. 128 (tensor products of similar algebras)"]
theorem isBrauerEquivalent_tensor {A A' B B' : CSA.{u, u} F} (h : IsBrauerEquivalent A A')
    (h' : IsBrauerEquivalent B B') : IsBrauerEquivalent (tensor A B) (tensor A' B') := by
  rw [isBrauerEquivalent_iff_tensor_matrix] at h h' ⊢
  obtain ⟨r, s, hr, hs, ⟨e⟩⟩ := h
  obtain ⟨p, q, hp, hq, ⟨e'⟩⟩ := h'
  refine ⟨r * p, s * q, mul_ne_zero hr hp, mul_ne_zero hs hq, ⟨?_⟩⟩
  exact ((Algebra.TensorProduct.congr AlgEquiv.refl (matrixTensorEquiv (F := F) r p).symm).trans
    ((Algebra.TensorProduct.tensorTensorTensorComm F F F F _ _ _ _).trans
      ((Algebra.TensorProduct.congr e e').trans
        ((Algebra.TensorProduct.tensorTensorTensorComm F F F F _ _ _ _).symm.trans
          (Algebra.TensorProduct.congr AlgEquiv.refl (matrixTensorEquiv (F := F) s q))))))

/-! ### Commutativity, associativity, unit -/

/-- **O'Meara §52F, p. 128**: $A \otimes B \cong B \otimes A$. -/
@[kb "omeara1963" "§52F, p. 128 (A ⊗ B ≅ B ⊗ A)"]
theorem nonempty_algEquiv_tensor_comm (A B : CSA.{u, u} F) :
    Nonempty (tensor A B ≃ₐ[F] tensor B A) :=
  ⟨Algebra.TensorProduct.comm F A B⟩

/-- **O'Meara §52F, p. 128**: $(A \otimes B) \otimes C \cong A \otimes (B \otimes C)$. -/
@[kb "omeara1963" "§52F, p. 128 (associativity of ⊗)"]
theorem nonempty_algEquiv_tensor_assoc (A B C : CSA.{u, u} F) :
    Nonempty (tensor (tensor A B) C ≃ₐ[F] tensor A (tensor B C)) :=
  ⟨Algebra.TensorProduct.assoc F F F A B C⟩

/-- **O'Meara §52F, p. 128**: $A \otimes F \cong A$. -/
@[kb "omeara1963" "§52F, p. 128 (A ⊗ F ≅ A)"]
theorem nonempty_algEquiv_tensor_one (A : CSA.{u, u} F) : Nonempty (tensor A one ≃ₐ[F] A) :=
  ⟨Algebra.TensorProduct.rid F F A⟩

/-- Similarity form of `nonempty_algEquiv_tensor_comm`: $A \otimes B \sim B \otimes A$. -/
theorem isBrauerEquivalent_tensor_comm (A B : CSA.{u, u} F) :
    IsBrauerEquivalent (tensor A B) (tensor B A) :=
  isBrauerEquivalent_of_algEquiv (nonempty_algEquiv_tensor_comm A B).some

/-- Similarity form of `nonempty_algEquiv_tensor_assoc`. -/
theorem isBrauerEquivalent_tensor_assoc (A B C : CSA.{u, u} F) :
    IsBrauerEquivalent (tensor (tensor A B) C) (tensor A (tensor B C)) :=
  isBrauerEquivalent_of_algEquiv (nonempty_algEquiv_tensor_assoc A B C).some

/-- Similarity form of `nonempty_algEquiv_tensor_one`: $A \otimes F \sim A$. -/
theorem isBrauerEquivalent_tensor_one (A : CSA.{u, u} F) : IsBrauerEquivalent (tensor A one) A :=
  isBrauerEquivalent_of_algEquiv (nonempty_algEquiv_tensor_one A).some

/-! ### Splitting -/

/-- **O'Meara §52F, p. 128**: a central simple algebra $A$ splits ($A \cong M_k(F)$ for some $k \ge 1$) iff
$A \sim 1$, where $1$ is the algebra `one` $= F$.  (Via Wedderburn, 52:9, and Sec52B's
`splits_iff_nonempty_algEquiv_base`: both say that the division algebra component is $F$.) -/
@[kb "omeara1963" "§52F, p. 128 (A ~ 1 iff A splits)"]
theorem isBrauerEquivalent_one_iff (A : CSA.{u, u} F) :
    IsBrauerEquivalent A one ↔ ∃ k : ℕ, k ≠ 0 ∧ Nonempty (A ≃ₐ[F] Matrix (Fin k) (Fin k) F) := by
  have e₀ : F ≃ₐ[F] Matrix (Fin 1) (Fin 1) F :=
    AlgEquiv.ofBijective (Algebra.ofId F (Matrix (Fin 1) (Fin 1) F))
      ⟨fun a b h => by
        simpa [Algebra.ofId_apply, Matrix.algebraMap_matrix_apply] using congrFun (congrFun h 0) 0,
        fun M => ⟨M 0 0, by
          ext i j
          simp [Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, Fin.fin_one_eq_zero i,
            Fin.fin_one_eq_zero j]⟩⟩
  have e₁ : (one : CSA.{u, u} F) ≃ₐ[F] Matrix (Fin 1) (Fin 1) F := e₀
  constructor
  · intro h
    have : IsArtinianRing A := IsArtinianRing.of_finite F A
    obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F A
    have h2 := (isBrauerEquivalent_iff_nonempty_algEquiv (A := A) (A' := (one : CSA.{u, u} F))
      (D' := F) e e₁).mp h
    obtain ⟨ε⟩ := h2
    exact ⟨n, NeZero.ne n, ⟨e.trans ε.mapMatrix⟩⟩
  · rintro ⟨k, hk, ⟨e⟩⟩
    have : NeZero k := ⟨hk⟩
    exact (isBrauerEquivalent_iff_nonempty_algEquiv (A := A) (A' := (one : CSA.{u, u} F))
      (D := F) (D' := F) e e₁).mpr ⟨AlgEquiv.refl⟩

/-- **O'Meara §52F, p. 128**: if $A \sim 1$ then $A \otimes B \sim B$. -/
@[kb "omeara1963" "§52F, p. 128 (A ~ 1 implies A ⊗ B ~ B)"]
theorem isBrauerEquivalent_tensor_of_left_one {A : CSA.{u, u} F} (h : IsBrauerEquivalent A one)
    (B : CSA.{u, u} F) : IsBrauerEquivalent (tensor A B) B :=
  ((isBrauerEquivalent_tensor h (IsBrauerEquivalent.refl B)).trans
    (isBrauerEquivalent_tensor_comm one B)).trans (isBrauerEquivalent_tensor_one B)

/-! ### Reciprocal algebra and cancellation -/

/-- **O'Meara 52:10, consequence** (§52F, p. 128-129): $A \otimes A^* \sim 1$ (indeed
$A \otimes A^* \cong M_m(F)$ with $m = \dim_F A \ge 1$, `tensorProduct_mulOpposite_equiv_matrix`). -/
@[kb "omeara1963" "§52F, 52:10, p. 128 (A ⊗ A* ~ 1)"]
theorem isBrauerEquivalent_tensor_op (A : CSA.{u, u} F) : IsBrauerEquivalent (tensor A (op A)) one := by
  rw [isBrauerEquivalent_one_iff]
  obtain ⟨e⟩ := tensorProduct_mulOpposite_equiv_matrix (F := F) (A := A)
  exact ⟨Module.finrank F A, (Module.finrank_pos (R := F) (M := A)).ne', ⟨e⟩⟩

/-- **O'Meara §52F, cancellation law** (p. 129): if $A \otimes B \sim A' \otimes B$ then $A \sim A'$.
Following the book: tensor with $B^*$ and use $B \otimes B^* \sim 1$. -/
@[kb "omeara1963" "§52F, p. 129 (cancellation law)"]
theorem isBrauerEquivalent_of_tensor {A A' B : CSA.{u, u} F}
    (h : IsBrauerEquivalent (tensor A B) (tensor A' B)) : IsBrauerEquivalent A A' := by
  have key : ∀ X : CSA.{u, u} F, IsBrauerEquivalent (tensor (tensor X B) (op B)) X := fun X =>
    ((isBrauerEquivalent_tensor_assoc X B (op B)).trans
      ((isBrauerEquivalent_tensor (IsBrauerEquivalent.refl X)
        (isBrauerEquivalent_tensor_op B)).trans (isBrauerEquivalent_tensor_one X)))
  exact ((key A).symm.trans
    ((isBrauerEquivalent_tensor h (IsBrauerEquivalent.refl (op B))).trans (key A')))

/-! ### 57:11, second assertion -/

section Quaternion

variable [Invertible (2 : F)]

/-- The quaternion algebra $(\alpha,\beta) = $ `ℍ[F,α,β]`, bundled as a central simple algebra (O'Meara 57:2,
`Quaternions57.isCentral`, `Quaternions57.isSimpleRing`) for $\alpha, \beta \ne 0$. -/
def quaternion (α β : F) (hα : α ≠ 0) (hβ : β ≠ 0) : CSA.{u, u} F :=
  haveI := Quaternions57.isCentral (F := F) hα hβ
  haveI := Quaternions57.isSimpleRing (F := F) hα hβ
  ofAlg ℍ[F,α,β]

/-- Conjugation $x \mapsto \bar x$ is an algebra isomorphism from $(\alpha,\beta)$ to its reciprocal algebra
$(\alpha,\beta)^*$ (it reverses products). -/
def quaternionOpEquiv (α β : F) : ℍ[F,α,β] ≃ₐ[F] ℍ[F,α,β]ᵐᵒᵖ :=
  AlgEquiv.ofRingEquiv (f := starRingEquiv (R := ℍ[F,α,β]))
    (fun r => by
      apply MulOpposite.unop_injective
      simp [starRingEquiv])

/-- **O'Meara 57:11, second assertion** (§57C, p. 148): for $\alpha, \beta \ne 0$ (characteristic $\ne 2$),
$(\alpha,\beta) \otimes (\alpha,\beta) \sim 1$.  Proof: conjugation is an isomorphism
$(\alpha,\beta) \cong (\alpha,\beta)^*$, so $(\alpha,\beta) \otimes (\alpha,\beta) \cong
(\alpha,\beta) \otimes (\alpha,\beta)^* \sim 1$ by 52:10. -/
@[kb "omeara1963" "§57C, 57:11, p. 148 (second assertion)"]
theorem isBrauerEquivalent_quaternion_tensor_self (α β : F) (hα : α ≠ 0) (hβ : β ≠ 0) :
    IsBrauerEquivalent (tensor (quaternion α β hα hβ) (quaternion α β hα hβ)) one := by
  have e0 : (quaternion α β hα hβ) ⊗[F] ℍ[F,α,β] ≃ₐ[F] (quaternion α β hα hβ) ⊗[F] ℍ[F,α,β]ᵐᵒᵖ :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := F) (A₁ := quaternion α β hα hβ))
      (quaternionOpEquiv α β)
  have e : tensor (quaternion α β hα hβ) (quaternion α β hα hβ) ≃ₐ[F]
      tensor (quaternion α β hα hβ) (op (quaternion α β hα hβ)) := e0
  exact (isBrauerEquivalent_of_algEquiv e).trans (isBrauerEquivalent_tensor_op _)

end Quaternion

end QuadFormsKB.OMeara.CSA52
