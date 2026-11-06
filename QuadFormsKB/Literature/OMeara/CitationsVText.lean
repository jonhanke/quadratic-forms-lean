/-
# O'Meara Chapter V: tagged restatements of facts the library takes from Mathlib

Items of §51–§58 that had no citation tag yet: the fact is used through Mathlib or
inside a proof, and nothing carried an O'Meara tag. Each declaration here is a short comparison lemma that states the
book's claim and proves it from the named Mathlib declaration (or directly). Only `IsCompatible` (54.r1) is a new
definition: O'Meara's notion of an algebra *compatible* with $V$, which the library had only as an inline hypothesis.

Notation: $B$ is `QuadFormsKB.OMeara.bil Q` $=$ `QuadraticMap.associated Q`; the quaternion algebra $(\alpha,\beta)$
is `ℍ[F,α,0,β]`; indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Literature.OMeara.Sec52B

noncomputable section

namespace QuadFormsKB.OMeara.TextV

universe u

open scoped TensorProduct

section Sec51

variable {F : Type*} [Field F]

/-- **51.r1** (O'Meara 1963, §51, p. 113): a map $\omega : U \times V \to W$ that is additive and homogeneous in each
variable is a bilinear map (Mathlib `LinearMap.mk₂`). -/
@[kb "omeara1963" "§51, p. 113 (bilinear mapping: additive and homogeneous in each variable)"]
theorem exists_bilinear_of_laws {U V W : Type*} [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : U → V → W)
    (h1 : ∀ u u' v, f (u + u') v = f u v + f u' v) (h2 : ∀ (α : F) u v, f (α • u) v = α • f u v)
    (h3 : ∀ u v v', f u (v + v') = f u v + f u v') (h4 : ∀ (α : F) u v, f u (α • v) = α • f u v) :
    ∃ B : U →ₗ[F] V →ₗ[F] W, ∀ u v, B u v = f u v :=
  ⟨LinearMap.mk₂ F f h1 h2 h3 h4, fun _ _ => rfl⟩

/-- **51.r3** (O'Meara 1963, §51, p. 113): a tensor product of $U$ and $V$ exists: the canonical bilinear map
$U \times V \to U \otimes V$ is a tensor product (Mathlib `IsTensorProduct`, `TensorProduct.mk`). -/
@[kb "omeara1963" "§51, p. 113 (existence of a tensor product)"]
theorem isTensorProduct_mk (U V : Type*) [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V] :
    IsTensorProduct (TensorProduct.mk F U V) := by
  have : TensorProduct.lift (TensorProduct.mk F U V) = LinearMap.id := TensorProduct.lift_mk
  unfold IsTensorProduct
  rw [this]
  exact Function.bijective_id

/-- **51.r5** (O'Meara 1963, §51, p. 114): the linear map induced by a bilinear map $\omega$ satisfies
$\varphi(u \otimes v) = \omega(u, v)$ (Mathlib `TensorProduct.lift_tmul`). -/
@[kb "omeara1963" "§51, p. 114 (φ(u ⊗ v) = ω(u, v))"]
theorem lift_tmul_eq {U V W : Type*} [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (ω : U →ₗ[F] V →ₗ[F] W) (u : U) (v : V) :
    TensorProduct.lift ω (u ⊗ₜ[F] v) = ω u v :=
  TensorProduct.lift.tmul u v

/-- **51.r6** (O'Meara 1963, §51, p. 114): $\dim(U \otimes V) = \dim U \cdot \dim V$ for finite-dimensional $U, V$
(Mathlib `Module.finrank_tensorProduct`). -/
@[kb "omeara1963" "§51, p. 114 (dim U⊗V = dim U · dim V)"]
theorem finrank_tensor_eq_mul (U V : Type*) [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    [Module.Finite F U] [Module.Finite F V] :
    Module.finrank F (U ⊗[F] V) = Module.finrank F U * Module.finrank F V :=
  Module.finrank_tensorProduct

/-- **51.r9** (O'Meara 1963, §51, p. 114–115): in an $F$-algebra $A$, $\alpha(xy) = (\alpha x)y = x(\alpha y)$
(Mathlib `smul_mul_assoc`, `mul_smul_comm`). -/
@[kb "omeara1963" "§51, p. 115 (algebra: α(xy) = (αx)y = x(αy))"]
theorem smul_mul_eq_smul_mul_eq_mul_smul {A : Type*} [Ring A] [Algebra F A] (α : F) (x y : A) :
    α • (x * y) = (α • x) * y ∧ α • (x * y) = x * (α • y) :=
  ⟨(smul_mul_assoc α x y).symm, (mul_smul_comm α x y).symm⟩

/-- **51.r10** (O'Meara 1963, §51, p. 115): in a division algebra every nonzero element has a two-sided inverse
(Mathlib `DivisionRing`). -/
@[kb "omeara1963" "§51, p. 115 (division algebra: every nonzero element is invertible)"]
theorem divisionAlgebra_inv {D : Type*} [DivisionRing D] [Algebra F D] (x : D) (hx : x ≠ 0) :
    ∃ y : D, x * y = 1 ∧ y * x = 1 :=
  ⟨x⁻¹, mul_inv_cancel₀ hx, inv_mul_cancel₀ hx⟩

/-- **51.r11** (O'Meara 1963, §51, p. 115): $(\alpha 1_A)x = \alpha x = x(\alpha 1_A)$ in an $F$-algebra $A$
(Mathlib `Algebra.smul_def`, `Algebra.commutes`). -/
@[kb "omeara1963" "§51, p. 115 ((α1_A)x = αx = x(α1_A))"]
theorem smul_one_mul_eq {A : Type*} [Ring A] [Algebra F A] (α : F) (x : A) :
    (α • (1 : A)) * x = α • x ∧ α • x = x * (α • (1 : A)) := by
  refine ⟨by rw [smul_mul_assoc, one_mul], ?_⟩
  rw [mul_smul_comm, mul_one]

/-- **51:1** (O'Meara 1963, §51, p. 115): $L_F(V)$, the linear maps $V \to V$, is an algebra over $F$, with
$\alpha \mapsto \alpha\,\mathrm{id}_V$ (Mathlib `Module.End`, `Module.algebraMap_end_apply`). -/
@[kb "omeara1963" "§51, p. 115 (L_F(V) is an algebra over F)"]
theorem algebraMap_end_eq_smul_id (V : Type*) [AddCommGroup V] [Module F V] (α : F) :
    algebraMap F (Module.End F V) α = α • LinearMap.id := by
  ext v
  simp [Module.algebraMap_end_apply]

/-- **51.r13** (O'Meara 1963, §51, p. 115): an $F$-linear, multiplicative map with $\varphi(1) = 1$ between
$F$-algebras is an algebra homomorphism (Mathlib `AlgHom.ofLinearMap`). -/
@[kb "omeara1963" "§51, p. 115 (algebra homomorphism: F-linear, multiplicative, φ(1) = 1)"]
theorem exists_algHom_of_linear_mul_one {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
    (φ : A →ₗ[F] B) (hone : φ 1 = 1) (hmul : ∀ x y, φ (x * y) = φ x * φ y) :
    ∃ ψ : A →ₐ[F] B, ⇑ψ = ⇑φ :=
  ⟨AlgHom.ofLinearMap φ hone hmul, rfl⟩

/-- **51.r17** (O'Meara 1963, §51, p. 116): in $A \otimes B$, $(x \otimes y)(x' \otimes y') = xx' \otimes yy'$ and
$1 \otimes 1$ is the identity (Mathlib `Algebra.TensorProduct.tmul_mul_tmul`, `Algebra.TensorProduct.one_def`). -/
@[kb "omeara1963" "§51, p. 116 ((x⊗y)(x'⊗y') = xx'⊗yy', identity 1⊗1)"]
theorem tensor_algebra_mul_one {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B] :
    (∀ (x x' : A) (y y' : B), (x ⊗ₜ[F] y) * (x' ⊗ₜ[F] y') = (x * x') ⊗ₜ[F] (y * y')) ∧
      (1 : A ⊗[F] B) = (1 : A) ⊗ₜ[F] (1 : B) :=
  ⟨fun x x' y y' => Algebra.TensorProduct.tmul_mul_tmul x x' y y', Algebra.TensorProduct.one_def⟩

/-- **51.r19** (O'Meara 1963, §51, p. 117): if $A \cong A'$ and $B \cong B'$ as $F$-algebras, then
$A \otimes B \cong A' \otimes B'$ (Mathlib `Algebra.TensorProduct.congr`). -/
@[kb "omeara1963" "§51, p. 117 (A ≅ A', B ≅ B' implies A⊗B ≅ A'⊗B')"]
theorem tensor_algEquiv_congr {A A' B B' : Type*} [Ring A] [Algebra F A] [Ring A'] [Algebra F A']
    [Ring B] [Algebra F B] [Ring B'] [Algebra F B'] (hA : Nonempty (A ≃ₐ[F] A'))
    (hB : Nonempty (B ≃ₐ[F] B')) : Nonempty ((A ⊗[F] B) ≃ₐ[F] (A' ⊗[F] B')) :=
  ⟨Algebra.TensorProduct.congr hA.some hB.some⟩

end Sec51

section Sec52

variable {F : Type*} [Field F]

/-- **52.r1** (O'Meara 1963, §52, p. 118): for a nonzero $F$-algebra $A$ the map $\alpha \mapsto \alpha 1_A$ is
injective, and each $\alpha 1_A$ is central in $A$ (Mathlib `RingHom.injective`, `Algebra.commutes`). -/
@[kb "omeara1963" "§52, p. 118 (α ↦ α1_A injective; α1_A central)"]
theorem algebraMap_injective_central {A : Type*} [Ring A] [Nontrivial A] [Algebra F A] :
    Function.Injective (algebraMap F A) ∧ ∀ (α : F) (x : A), algebraMap F A α * x = x * algebraMap F A α :=
  ⟨(algebraMap F A).injective, fun α x => Algebra.commutes α x⟩

/-- **52.r2** (O'Meara 1963, §52, p. 119): $A$ is central iff its centre is $F1_A$ (Mathlib `Algebra.IsCentral`). -/
@[kb "omeara1963" "§52, p. 119 (central algebra: centre = F1_A)"]
theorem isCentral_iff_center {A : Type*} [Ring A] [Algebra F A] :
    Algebra.IsCentral F A ↔
      ∀ z : A, (∀ x, z * x = x * z) → ∃ α : F, z = algebraMap F A α := by
  constructor
  · intro h z hz
    have hz' : z ∈ Subalgebra.center F A := by
      rw [Subalgebra.mem_center_iff]
      exact fun x => (hz x).symm
    have := Algebra.IsCentral.out (K := F) (D := A) hz'
    obtain ⟨α, hα⟩ := Algebra.mem_bot.mp this
    exact ⟨α, hα.symm⟩
  · intro h
    refine ⟨fun z hz => ?_⟩
    have hz' : ∀ x : A, z * x = x * z := fun x => (Subalgebra.mem_center_iff.mp hz x).symm
    obtain ⟨α, hα⟩ := h z hz'
    exact Algebra.mem_bot.mpr ⟨α, hα.symm⟩

/-- **52.r4** (O'Meara 1963, §52, p. 119): a simple algebra has no two-sided ideals other than $0$ and $A$.
(Mathlib's `IsSimpleRing` additionally requires $A \ne 0$.) -/
@[kb "omeara1963" "§52, p. 119 (simple: only two-sided ideals 0 and A)"]
theorem simple_two_sided_ideals {A : Type*} [Ring A] [IsSimpleRing A] (I : TwoSidedIdeal A) :
    I = ⊥ ∨ I = ⊤ :=
  IsSimpleOrder.eq_bot_or_eq_top I

/-- **52.r5** (O'Meara 1963, §52, p. 119): a division algebra is simple (Mathlib instance
`DivisionRing.isSimpleRing`). -/
@[kb "omeara1963" "§52, p. 119 (a division algebra is simple)"]
theorem divisionAlgebra_isSimple {D : Type*} [DivisionRing D] [Algebra F D] : IsSimpleRing D :=
  inferInstance

/-- **52.r6** (O'Meara 1963, §52, p. 119): a central simple algebra (Mathlib `CSA F`) is central and simple (and
finite-dimensional). -/
@[kb "omeara1963" "§52, p. 119 (central simple algebra = central and simple)"]
theorem csa_central_simple (A : CSA F) :
    Algebra.IsCentral F A ∧ IsSimpleRing A ∧ FiniteDimensional F A :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **52.r7, 52.r8** (O'Meara 1963, §52, p. 120): an $A$-linear map between left ideals (more generally left
$A$-modules) of an $F$-algebra $A$ is $F$-linear (Mathlib `LinearMap.restrictScalars`; maps are written on the left
in the library). -/
@[kb "omeara1963" "§52, p. 120 (an A-linear map of left ideals is F-linear)"]
theorem exists_fLinear_of_aLinear {A : Type*} [Ring A] [Algebra F A] {M N : Type*} [AddCommGroup M]
    [Module A M] [Module F M] [IsScalarTower F A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower F A N] (f : M →ₗ[A] N) :
    ∃ g : M →ₗ[F] N, ∀ x, g x = f x :=
  ⟨f.restrictScalars F, fun _ => rfl⟩

/-- **52.r10** (O'Meara 1963, §52, p. 121): a nonzero finite-dimensional $F$-algebra has a minimal (nonzero) left
ideal (Mathlib `IsArtinianRing.of_finite`, `IsAtomic`). -/
@[kb "omeara1963" "§52, p. 121 (a nonzero finite-dimensional algebra has a minimal left ideal)"]
theorem exists_minimal_leftIdeal {A : Type*} [Ring A] [Nontrivial A] [Algebra F A] [FiniteDimensional F A] :
    ∃ I : Submodule A A, IsAtom I := by
  have : IsArtinianRing A := IsArtinianRing.of_finite F A
  rcases eq_bot_or_exists_atom_le (⊤ : Submodule A A) with h | ⟨I, hI, _⟩
  · exact absurd h top_ne_bot
  · exact ⟨I, hI⟩

/-- **52.r11** (O'Meara 1963, §52, p. 122): $M_n(D)$ is a finite-dimensional $F$-algebra when $D$ is
(Mathlib `Matrix` module instances). -/
@[kb "omeara1963" "§52, p. 122 (M_n(D) is a finite-dimensional F-algebra)"]
theorem matrix_finiteDimensional (n : ℕ) (D : Type*) [Ring D] [Algebra F D] [FiniteDimensional F D] :
    FiniteDimensional F (Matrix (Fin n) (Fin n) D) :=
  inferInstance

/-- **52.r14** (O'Meara 1963, §52, p. 125, footnote): a simple ring with the minimum condition on left ideals
(Artinian) is a matrix ring $M_n(D)$, $n \ge 1$, over a division ring $D$ (Mathlib
`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`). -/
@[kb "omeara1963" "§52, p. 125 (Wedderburn–Artin: simple Artinian ring is M_n(D))"]
theorem simple_artinian_matrix (R : Type u) [Ring R] [IsSimpleRing R] [IsArtinianRing R] :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing R

/-- **52.r16** (O'Meara 1963, §52, p. 128): similarity of central simple algebras ($M_n(A) \cong M_m(B)$, $n, m \ge 1$)
is an equivalence relation (Mathlib `IsBrauerEquivalent.is_eqv`). -/
@[kb "omeara1963" "§52, p. 128 (similarity of central simple algebras is an equivalence relation)"]
theorem similarity_equivalence : Equivalence (IsBrauerEquivalent (K := F)) :=
  IsBrauerEquivalent.is_eqv

end Sec52

section Sec53

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {V : Type*} [AddCommGroup V] [Module F V]

/-- **53.r14** (O'Meara 1963, §53, p. 131): the $E$-ification $E \otimes V$ of a quadratic space $(V, Q)$ carries the
quadratic form $Q_E$ with $Q_E(1 \otimes x) = Q(x)$ (Mathlib `QuadraticForm.baseChange_tmul`); it is the only
quadratic form with this property (`baseChange_ext`, no hypothesis on $2$ needed); and when $2$ is
invertible in $E$ its bilinear form restricts to $B$ on $V$ (`QuadraticForm.associated_baseChange`):
$B_E(1 \otimes x, 1 \otimes y) = B(x, y)$. -/
@[kb "omeara1963" "§53, p. 131 (the E-ification of a quadratic space: Q_E(1⊗x) = Q x, unique)"]
theorem eification_unique_and_restricts [Invertible (2 : F)] [Invertible (2 : E)] (Q : QuadraticForm F V) :
    (∀ x, Q.baseChange E ((1 : E) ⊗ₜ[F] x) = algebraMap F E (Q x)) ∧
      (∀ Q' : QuadraticForm E (E ⊗[F] V), (∀ x, Q' ((1 : E) ⊗ₜ[F] x) = algebraMap F E (Q x)) →
        Q' = Q.baseChange E) ∧
      ∀ x y : V, QuadraticMap.associated (R := E) (Q.baseChange E)
          ((1 : E) ⊗ₜ[F] x) ((1 : E) ⊗ₜ[F] y) = algebraMap F E (QuadraticMap.associated (R := F) Q x y) := by
  have h1 : ∀ x, Q.baseChange E ((1 : E) ⊗ₜ[F] x) = algebraMap F E (Q x) := by
    intro x
    rw [QuadraticForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one]
  refine ⟨h1, fun Q' hQ' => baseChange_ext fun x => by rw [hQ', h1], ?_⟩
  intro x y
  rw [QuadraticForm.associated_baseChange]
  simp [Algebra.algebraMap_eq_smul_one]

end Sec53

section Sec54

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {A : Type*} [Ring A] [Algebra F A]

/-- **54.r1** (O'Meara 1963, §54, p. 131): an $F$-algebra $A$ is *compatible* with the quadratic space $(V, Q)$ if
$V \subseteq A$ (here an $F$-linear map $j : V \to A$; injectivity is not required) and $x^2 = Q(x)1_A$ for all
$x \in V$. -/
@[kb "omeara1963" "§54, p. 131 (algebra compatible with V: x² = Q(x)1_A)"]
def IsCompatible (Q : QuadraticForm F V) (j : V →ₗ[F] A) : Prop :=
  ∀ x, j x * j x = algebraMap F A (Q x)

/-- **54.r2** (O'Meara 1963, §54, p. 132): in an algebra compatible with $V$ (with $2$ invertible in $F$),
$xy + yx = 2B(x,y)1_A$ for $x, y \in V$. -/
@[kb "omeara1963" "§54, p. 132 (compatible algebra: xy + yx = 2B(x,y)1_A)"]
theorem IsCompatible.mul_add_mul [Invertible (2 : F)] {Q : QuadraticForm F V} {j : V →ₗ[F] A}
    (h : IsCompatible Q j) (x y : V) :
    j x * j y + j y * j x = algebraMap F A (2 * QuadFormsKB.OMeara.bil Q x y) := by
  have hxy := h (x + y)
  have h2 : 2 * QuadFormsKB.OMeara.bil Q x y = QuadraticMap.polar Q x y := by
    rw [QuadFormsKB.OMeara.bil, QuadraticMap.associated_apply]
    change 2 * (⅟(2 : F) * _) = _
    rw [← mul_assoc, mul_invOf_self, one_mul]
    rfl
  rw [h2]
  rw [map_add, add_mul, mul_add, mul_add, h x, h y, QuadraticMap.map_add Q x y, map_add, map_add] at hxy
  apply add_left_cancel (a := algebraMap F A (Q x) + algebraMap F A (Q y))
  rw [← hxy]
  abel

/-- **54:2 (i)** (O'Meara 1963, §54, p. 132): let $A$ be compatible with $V$ and $x \in V$ anisotropic (the book's
$V$ is regular with an orthogonal base, so $x = x_1$ exists when $V \ne 0$). Then the subring generated by $V$ in $A$
(Mathlib `Subring.closure (Set.range j)`) is closed under scalars and contains $1_A = Q(x)^{-1}x^2$, i.e. it is
the subalgebra `Algebra.adjoin F (Set.range j)`, and $1_A$ lies in it. -/
@[kb "omeara1963" "§54, p. 132 (subring generated by V is a subalgebra containing 1_A)"]
theorem adjoin_toSubring_eq_closure {Q : QuadraticForm F V} {j : V →ₗ[F] A} (h : IsCompatible Q j)
    {x : V} (hx : Q x ≠ 0) :
    (1 : A) ∈ Subring.closure (Set.range j) ∧
      (Algebra.adjoin F (Set.range j)).toSubring = Subring.closure (Set.range j) := by
  have h1 : (1 : A) ∈ Subring.closure (Set.range j) := by
    have e : (1 : A) = ((Q x)⁻¹ • j x) * j x := by
      rw [smul_mul_assoc, h x, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hx, map_one]
    rw [e]
    exact Subring.mul_mem _ (Subring.subset_closure ⟨(Q x)⁻¹ • x, by simp⟩)
      (Subring.subset_closure ⟨x, rfl⟩)
  refine ⟨h1, le_antisymm ?_ ?_⟩
  · let S : Subalgebra F A :=
      { Subring.closure (Set.range j) with
        algebraMap_mem' := fun α => by
          have e : algebraMap F A α = (j ((α * (Q x)⁻¹) • x)) * j x := by
            rw [map_smul, smul_mul_assoc, h x, Algebra.smul_def, ← map_mul, mul_assoc,
              inv_mul_cancel₀ hx, mul_one]
          rw [e]
          exact Subring.mul_mem _ (Subring.subset_closure ⟨_, rfl⟩) (Subring.subset_closure ⟨x, rfl⟩) }
    intro a ha
    exact Algebra.adjoin_le (S := S) (fun b hb => Subring.subset_closure hb) ha
  · exact Subring.closure_le.mpr fun a ha => Algebra.subset_adjoin ha


/-- **54.r7** (O'Meara 1963, §54, p. 135): the even elements $C^+$ of the Clifford algebra $C$ of $(V, Q)$ (Mathlib
`CliffordAlgebra.even`) form a subalgebra: $1_C \in C^+$, $C^+$ is closed under products, and $C^+$ contains the
product $xy$ of two vectors. -/
@[kb "omeara1963" "§54, p. 135 (even elements C⁺ form a subalgebra containing 1 and xy)"]
theorem even_subalgebra (Q : QuadraticForm F V) :
    (1 : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q ∧
      (∀ a b : CliffordAlgebra Q, a ∈ CliffordAlgebra.even Q → b ∈ CliffordAlgebra.even Q →
        a * b ∈ CliffordAlgebra.even Q) ∧
      ∀ x y : V, CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q y ∈ CliffordAlgebra.even Q :=
  ⟨Subalgebra.one_mem _, fun _ _ ha hb => Subalgebra.mul_mem _ ha hb,
    fun x y => CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q x y⟩

end Sec54

section Sec57

variable {F : Type*} [Field F] {α β : F}

/-- **57.r1** (O'Meara 1963, §57, p. 142): $(\alpha,\beta)$ (`ℍ[F,α,0,β]`) has the base $1, x_1, x_2, x_3$ (0-based:
`basisOneIJK` indexes $0,1,2,3$) with $x_1^2 = \alpha$, $x_2^2 = \beta$, $x_1x_2 = x_3 = -x_2x_1$,
$x_3^2 = -\alpha\beta$. -/
@[kb "omeara1963" "§57, p. 142 ((α,β): base 1, x₁, x₂, x₃ and multiplication table)"]
theorem quaternion_base_table (α β : F) :
    (QuaternionAlgebra.basisOneIJK α 0 β 0 = (1 : (QuaternionAlgebra F α 0 β)) ∧ QuaternionAlgebra.basisOneIJK α 0 β 1 = ⟨0, 1, 0, 0⟩ ∧
      QuaternionAlgebra.basisOneIJK α 0 β 2 = ⟨0, 0, 1, 0⟩ ∧ QuaternionAlgebra.basisOneIJK α 0 β 3 = ⟨0, 0, 0, 1⟩) ∧
    (⟨0, 1, 0, 0⟩ * ⟨0, 1, 0, 0⟩ : (QuaternionAlgebra F α 0 β)) = algebraMap F (QuaternionAlgebra F α 0 β) α ∧
    (⟨0, 0, 1, 0⟩ * ⟨0, 0, 1, 0⟩ : (QuaternionAlgebra F α 0 β)) = algebraMap F (QuaternionAlgebra F α 0 β) β ∧
    (⟨0, 1, 0, 0⟩ * ⟨0, 0, 1, 0⟩ : (QuaternionAlgebra F α 0 β)) = ⟨0, 0, 0, 1⟩ ∧
    (⟨0, 0, 1, 0⟩ * ⟨0, 1, 0, 0⟩ : (QuaternionAlgebra F α 0 β)) = -⟨0, 0, 0, 1⟩ ∧
    (⟨0, 0, 0, 1⟩ * ⟨0, 0, 0, 1⟩ : (QuaternionAlgebra F α 0 β)) = algebraMap F (QuaternionAlgebra F α 0 β) (-(α * β)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> ext <;> simp [QuaternionAlgebra.basisOneIJK]

/-- **57.r5** (O'Meara 1963, §57, p. 143): the conjugate of $x = \xi_0 1 + \xi_1x_1 + \xi_2x_2 + \xi_3x_3$ is
$\bar x = \xi_0 1 - \xi_1x_1 - \xi_2x_2 - \xi_3x_3$ (Mathlib `QuaternionAlgebra.star_mk`, `re_star`, `imI_star`). -/
@[kb "omeara1963" "§57, p. 143 (conjugate x̄ = ξ₀1 − ξ₁x₁ − ξ₂x₂ − ξ₃x₃)"]
theorem star_components (x : (QuaternionAlgebra F α 0 β)) :
    (star x).re = x.re ∧ (star x).imI = -x.imI ∧ (star x).imJ = -x.imJ ∧ (star x).imK = -x.imK := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- **57.r6** (O'Meara 1963, §57, p. 143): conjugation is an involution, additive, $F$-linear, and
anti-multiplicative: $\bar{\bar x} = x$, $\overline{x+y} = \bar x + \bar y$, $\overline{\eta x} = \eta\bar x$,
$\overline{xy} = \bar y\bar x$ (Mathlib `star_star`, `star_add`, `QuaternionAlgebra.star_smul`, `star_mul`). -/
@[kb "omeara1963" "§57, p. 143 (conjugation: involutive, additive, η-linear, anti-multiplicative)"]
theorem conjugation_laws :
    (∀ x : (QuaternionAlgebra F α 0 β), star (star x) = x) ∧ (∀ x y : (QuaternionAlgebra F α 0 β), star (x + y) = star x + star y) ∧
      (∀ (η : F) (x : (QuaternionAlgebra F α 0 β)), star (η • x) = η • star x) ∧ ∀ x y : (QuaternionAlgebra F α 0 β), star (x * y) = star y * star x :=
  ⟨fun x => star_star x, fun x y => star_add x y, fun η x => QuaternionAlgebra.star_smul η x,
    fun x y => star_mul x y⟩

/-- **57.r8** (O'Meara 1963, §57, p. 143): the trace $Tx = x + \bar x$ equals $2\xi_0 1$, satisfies
$T\bar x = Tx$ and is additive (Mathlib `QuaternionAlgebra.star_eq_two_re_sub`, `star_add`). -/
@[kb "omeara1963" "§57, p. 143 (trace Tx = x + x̄ = 2ξ₀1, Tx̄ = Tx, additive)"]
theorem trace_laws :
    (∀ x : (QuaternionAlgebra F α 0 β), x + star x = algebraMap F (QuaternionAlgebra F α 0 β) (2 * x.re)) ∧ (∀ x : (QuaternionAlgebra F α 0 β), star x + star (star x) = x + star x) ∧
      ∀ x y : (QuaternionAlgebra F α 0 β), (x + y) + star (x + y) = (x + star x) + (y + star y) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_⟩
  · ext <;> simp [QuaternionAlgebra.algebraMap_eq]
    ring
  · rw [star_star, add_comm]
  · rw [star_add]; abel

/-- **57.r10** (O'Meara 1963, §57, p. 143), $2$ invertible: $x$ is pure ($\xi_0 = 0$) iff $\bar x = -x$, and
$x$ is a scalar ($x = \xi_01$) iff $\bar x = x$ (Mathlib `QuaternionAlgebra.star_eq_neg`, which needs `CharZero`;
here only `Invertible (2 : F)`). -/
@[kb "omeara1963" "§57, p. 143 (x pure iff x̄ = −x; x scalar iff x̄ = x)"]
theorem pure_scalar_iff_star [Invertible (2 : F)] (x : (QuaternionAlgebra F α 0 β)) :
    (x.re = 0 ↔ star x = -x) ∧ (x = algebraMap F (QuaternionAlgebra F α 0 β) x.re ↔ star x = x) := by
  have h2 : (2 : F) ≠ 0 := Invertible.ne_zero (2 : F)
  have key : ∀ c : F, c = -c ↔ c = 0 := fun c => by
    constructor
    · intro h
      have : (2 : F) * c = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
      exact (mul_eq_zero.mp this).resolve_left h2
    · intro h; rw [h]; simp
  constructor
  · constructor
    · intro h; ext <;> simp [h]
    · intro h
      have := congrArg QuaternionAlgebra.re h
      simp only [QuaternionAlgebra.re_star, QuaternionAlgebra.re_neg, zero_mul, add_zero] at this
      exact (key x.re).mp this
  · constructor
    · intro h
      have e1 : x.imI = 0 := by simpa [QuaternionAlgebra.algebraMap_eq] using congrArg QuaternionAlgebra.imI h
      have e2 : x.imJ = 0 := by simpa [QuaternionAlgebra.algebraMap_eq] using congrArg QuaternionAlgebra.imJ h
      have e3 : x.imK = 0 := by simpa [QuaternionAlgebra.algebraMap_eq] using congrArg QuaternionAlgebra.imK h
      ext <;> simp [e1, e2, e3]
    · intro h
      have h1 := congrArg QuaternionAlgebra.imI h
      have h2' := congrArg QuaternionAlgebra.imJ h
      have h3 := congrArg QuaternionAlgebra.imK h
      simp only [QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star] at h1 h2' h3
      have e1 := (key x.imI).mp h1.symm
      have e2 := (key x.imJ).mp h2'.symm
      have e3 := (key x.imK).mp h3.symm
      ext <;> simp [QuaternionAlgebra.algebraMap_eq, e1, e2, e3]

end Sec57

end QuadFormsKB.OMeara.TextV

/-! 52.r9 (O'Meara 1963, §52B, pp. 120–121): $R_A(\mathfrak a)$, the $F$-algebra of $A$-linear maps of a left ideal
$\mathfrak a$ with the multiplication twisted by writing maps on the right, is `(Module.End A a)ᵐᵒᵖ` in the library
(maps written on the left, opposite algebra); it carries a second tag here. -/
attribute [kb "omeara1963" "§52B, pp. 120–121 (R_A(a), the A-linear maps of a with twisted product, as (End_A a)ᵒᵖ)"]
  QuadFormsKB.OMeara.finiteDimensional_endMulOpposite
