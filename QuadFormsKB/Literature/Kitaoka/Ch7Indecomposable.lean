/-
# Kitaoka 1993, Theorem 7.5.3: indecomposability under scalar extension

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.5, Theorem 7.5.3, p. 244 (printed page).

**Setting.** As in the lattice layer of the repository: a quadratic space over a number field $F$ is $(F^n, Q)$ with
`Q : QuadForm F n`, and a lattice is an $\mathcal O_F$-submodule $L$ of $F^n$ (`Lattices.Lat F n`: finitely generated
and spanning). For a number field $E \supseteq F$ the scalar extension is $V_E = (E^n, Q)$ (`Q.map (algebraMap F E)`)
and $R_E L$ is the $\mathcal O_E$-span of $L \subseteq F^n \subseteq E^n$ (`scalarExt E L`). Decomposability is the
O'Meara-file notion `Lattices.IsIndecomposable` ($L \ne 0$ and $L$ is not $L_1 \perp L_2$ with $L_1, L_2 \ne 0$).

"$V_v$ is positive definite at every infinite place $v$ of $F$" is `Lattices.IsTotallyPosDef Q` ($Q(x)$ totally
positive for every $x \ne 0$ in $F^n$; for totally real $F$ this is positive definiteness at every real place).

"$K$ is unramified over $F$" is written `Algebra.Unramified (𝓞 F) (𝓞 K)` (Mathlib: $\mathcal O_K$ is formally
unramified and of finite type over $\mathcal O_F$, i.e. every prime of $\mathcal O_F$ is unramified in $K$); the
infinite places are unramified automatically since $E$, hence every intermediate field, is totally real. An
intermediate field $F \subseteq K \subseteq E$ is described by a number field $K$ with a scalar tower
$F \to K \to E$; $K = F$ means $[K : F] = 1$.

**Defines** `scalarExt E L` ($R_E L$) and the statement `Theorem753` (stated).
-/
import QuadFormsKB.Literature.OMeara.Sec105
import QuadFormsKB.Lattices.Finite
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.FieldTheory.Galois.Basic

open NumberField QuadFormsKB.Lattices

noncomputable section

namespace QuadFormsKB.Kitaoka

/-- **The scalar extension $R_E L$** (Kitaoka 1993, §7.5, p. 244) of an $\mathcal O_F$-lattice $L \subseteq F^n$ to a
number field $E \supseteq F$: the $\mathcal O_E$-submodule of $E^n$ spanned by $L$ (coordinates mapped by
$F \to E$). -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.3, p. 244 (R_E L)"]
def scalarExt {F : Type*} [Field F] [NumberField F] (E : Type*) [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 F) (Fin n → F)) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) ((fun x i => algebraMap F E (x i)) '' (L : Set (Fin n → F)))

/-- **Kitaoka 1993, Theorem 7.5.3** (p. 244), *stated*: let $E/F$ be a Galois extension of totally real number fields
such that $F$ is the unique intermediate field of $E/F$ unramified over $F$. Let $V = (F^n, Q)$ be a quadratic space
over $F$ which is positive definite at every infinite place of $F$, and $L$ a lattice on $V$. If $L$ is
indecomposable, then $R_E L$ is indecomposable (on $V_E = (E^n, Q)$). -/
@[kb "kitaoka1993" "§7.5, Thm. 7.5.3, p. 244"]
def Theorem753 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E],
    IsTotallyReal F → IsTotallyReal E →
    (∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K E] [IsScalarTower F K E],
      Algebra.Unramified (𝓞 F) (𝓞 K) → Module.finrank F K = 1) →
    ∀ (n : ℕ) (Q : QuadForm F n), IsTotallyPosDef Q →
      ∀ L : Lat F n, IsIndecomposable Q L.1 → IsIndecomposable (Q.map (algebraMap F E)) (scalarExt E L.1)

end QuadFormsKB.Kitaoka
