/-
# O'Meara §54: uniqueness of the Clifford algebra (54:1)

**Setting.** $F$ a field, $(V, Q)$ a quadratic space over $F$. O'Meara (§54, p. 132) calls an $F$-algebra $A$ (with
identity) *compatible with* $V$ if $V$ sits in $A$ with $x^2 = Q(x)$ for $x \in V$; here this is an $F$-linear map
$\iota : V \to A$ with $\iota(x)^2 = Q(x) \cdot 1$ (O'Meara regards $V$ as a subset of $A$; we keep the map explicit).
A compatible algebra $(C, \iota)$ is a *Clifford algebra* of $V$ (`IsCliffordAlgebraOf`) if for every compatible
algebra $(A, f)$ there is exactly one algebra homomorphism $\varphi : C \to A$ with $\varphi \circ \iota = f$.
The universal property quantifies over algebras $A$ in a fixed universe (the universe of $C$).

**Proves**
* `IsCliffordAlgebraOf` (definition, §54, p. 132);
* `isCliffordAlgebraOf_cliffordAlgebra`: Mathlib's `CliffordAlgebra Q` is a Clifford algebra in this sense (existence,
  which O'Meara proves later in §54);
* `existsUnique_algEquiv_of_isCliffordAlgebraOf` (**54:1**): two Clifford algebras $C$, $C'$ of $V$ are related by
  exactly one algebra isomorphism that is the identity on $V$ (i.e. commutes with the embeddings of $V$).

**Proof notes.** O'Meara's argument: the two universal maps $C \to C'$, $C' \to C$ compose to homomorphisms that are
the identity on $V$, hence (by uniqueness) the identity. Regularity of $V$, assumed in the book, is not used.
-/
import Mathlib
import QuadFormsKB.Citation

noncomputable section

namespace QuadFormsKB.OMeara

universe u v

variable {F : Type v} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- **Clifford algebra of a quadratic space** (O'Meara 1963, §54, p. 132): an $F$-algebra $C$ with an $F$-linear map
$\iota : V \to C$ which is *compatible with* $V$, $\iota(x)^2 = Q(x)\cdot 1$ for all $\vec{x} \in V$, and universal: for
every $F$-algebra $A$ (in the universe of $C$) and every linear $f : V \to A$ with $f(x)^2 = Q(x)\cdot 1$ there is
exactly one algebra homomorphism $\varphi : C \to A$ with $\varphi(\iota(x)) = f(x)$ for all $\vec x \in V$. -/
@[kb "omeara1963" "§54, p. 132 (Clifford algebra: universal compatible algebra)"]
def IsCliffordAlgebraOf (C : Type u) [Ring C] [Algebra F C] (ι : V →ₗ[F] C) : Prop :=
  (∀ x : V, ι x * ι x = algebraMap F C (Q x)) ∧
    ∀ (A : Type u) [Ring A] [Algebra F A] (f : V →ₗ[F] A),
      (∀ x : V, f x * f x = algebraMap F A (Q x)) →
        ∃! φ : C →ₐ[F] A, ∀ x : V, φ (ι x) = f x

/-- Mathlib's `CliffordAlgebra Q`, with its canonical map `CliffordAlgebra.ι Q`, is a Clifford algebra of $V$ in
O'Meara's sense (§54, p. 132): it is compatible with $V$ and has the universal mapping property. -/
@[kb "omeara1963" "§54, p. 132 (existence of the Clifford algebra)"]
theorem isCliffordAlgebraOf_cliffordAlgebra
    (C : Type u) [Ring C] [Algebra F C] (e : CliffordAlgebra Q ≃ₐ[F] C) :
    IsCliffordAlgebraOf Q C (e.toLinearMap ∘ₗ CliffordAlgebra.ι Q) := by
  refine ⟨fun x => ?_, fun A _ _ f hf => ?_⟩
  · simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, ← map_mul, CliffordAlgebra.ι_sq_scalar,
      AlgEquiv.commutes]
  · refine ⟨(CliffordAlgebra.lift Q ⟨f, hf⟩).comp e.symm.toAlgHom, fun x => by simp, ?_⟩
    intro ψ hψ
    have h : ψ.comp e.toAlgHom = CliffordAlgebra.lift Q ⟨f, hf⟩ := by
      apply CliffordAlgebra.hom_ext
      ext x; simpa using hψ x
    rw [← h]; ext c; simp

/-- **Proposition 54:1** (O'Meara 1963, p. 132): if $(C, \iota)$ and $(C', \iota')$ are Clifford algebras of the
quadratic space $V$, there is exactly one algebra isomorphism $\varphi : C \to C'$ which is the identity on $V$, i.e.
$\varphi(\iota(x)) = \iota'(x)$ for all $\vec x \in V$. (The book assumes $V$ regular; this is not needed.) -/
@[kb "omeara1963" "§54, 54:1, p. 132"]
theorem existsUnique_algEquiv_of_isCliffordAlgebraOf {C C' : Type u} [Ring C] [Algebra F C] [Ring C']
    [Algebra F C'] {ι : V →ₗ[F] C} {ι' : V →ₗ[F] C'} (hC : IsCliffordAlgebraOf Q C ι)
    (hC' : IsCliffordAlgebraOf Q C' ι') :
    ∃! φ : C ≃ₐ[F] C', ∀ x : V, φ (ι x) = ι' x := by
  obtain ⟨φ, hφ, hφu⟩ := hC.2 C' ι' hC'.1
  obtain ⟨ψ, hψ, -⟩ := hC'.2 C ι hC.1
  have hid : ∀ x : V, (AlgHom.id F C) (ι x) = ι x := fun _ => rfl
  have h1 : ψ.comp φ = AlgHom.id F C := by
    obtain ⟨_, -, hu⟩ := hC.2 C ι hC.1
    exact (hu _ fun x => by simp [hφ, hψ]).trans (hu _ hid).symm
  have h2 : φ.comp ψ = AlgHom.id F C' := by
    obtain ⟨_, -, hu⟩ := hC'.2 C' ι' hC'.1
    exact (hu _ fun x => by simp [hφ, hψ]).trans (hu _ fun _ => rfl).symm
  refine ⟨AlgEquiv.ofAlgHom φ ψ h2 h1, hφ, fun χ hχ => ?_⟩
  have : χ.toAlgHom = φ := hφu _ hχ
  ext c
  exact congrArg (fun g : C →ₐ[F] C' => g c) this

end QuadFormsKB.OMeara
