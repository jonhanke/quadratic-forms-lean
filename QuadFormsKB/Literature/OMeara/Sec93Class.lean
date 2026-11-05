/-
# O'Meara §93E: the same set of fundamental invariants

**Setting** (as in `Sec93EBasic.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$,
lattices `Submodule R V` and `Submodule R V'` in quadratic spaces over $F$, Jordan splittings `Ls`, `Ks` indexed by
the same `Fin t` ($0$-based).

**Proves** (O'Meara 1963, §93E, p. 264): if $L$ and $L'$ have the same fundamental type, then fundamental norm
generators $a_1, \dots, a_t$ of $L$ are also fundamental norm generators of $L'$
(`IsFundNormGenerators.of_sameFundamentalType`), so that "$L$ and $L'$ have the same set of fundamental invariants"
(`sameFundamentalInvariants_of_sameFundamentalType`).
-/
import QuadFormsKB.Literature.OMeara.Sec93EBasic

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section SameSet

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **Fundamental norm generators are shared by lattices of the same fundamental type** (O'Meara 1963, §93E, p. 264):
"Suppose $L$ has the same fundamental type as $L'$. Then the fundamental norm generators satisfy
$a_i \cong a_i' \bmod \mathfrak w_i'$ and so $\{a_1, \dots, a_t\}$ can be regarded as a set of fundamental norm
generators of $L'$." (A norm generator of $L^{\mathfrak s_i}$ depends only on its norm group $\mathfrak g_i$, and
$\mathfrak g_i = \mathfrak g_i'$.) -/
@[kb "omeara1963" "§93E, p. 264 (the a_i of L are fundamental norm generators of L' of the same fundamental type)"]
theorem IsFundNormGenerators.of_sameFundamentalType {L : Submodule R V} {L' : Submodule R V'} {t : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hs : SameFundamentalType Q Q' L L' Ls Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) : IsFundNormGenerators Q' L' Ks a := by
  intro i
  obtain ⟨h, hs⟩ := hs
  have hi : Fin.cast h i = i := Fin.ext rfl
  have hg := (hs i).2.2
  rw [hi] at hg
  refine ⟨?_, ?_⟩
  · have : a i ∈ fundNormGroup Q L Ls i := (ha i).1
    exact (show a i ∈ fundNormGroup Q' L' Ks i from hg ▸ this)
  · rw [(ha i).2, fundSub, normIdeal_eq_span_normGroup Q, normIdeal_eq_span_normGroup Q']
    exact congrArg (fun g : AddSubgroup F => span R (g : Set F)) hg

/-- **The same set of fundamental invariants** (O'Meara 1963, §93E, p. 264): "When this is done we say that we have
chosen the same set of fundamental invariants for $L$ and $L'$": lattices of the same fundamental type, with
fundamental norm generators $a$ of $L$, have the same set of fundamental invariants with the scalars $a$. -/
@[kb "omeara1963" "§93E, p. 264 (the same set of fundamental invariants)"]
theorem sameFundamentalInvariants_of_sameFundamentalType {L : Submodule R V} {L' : Submodule R V'} {t : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hs : SameFundamentalType Q Q' L L' Ls Ks)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) : SameFundamentalInvariants Q Q' L L' Ls Ks a :=
  ⟨hs, ha, ha.of_sameFundamentalType Q Q' hs⟩

end SameSet

end QuadFormsKB.OMeara
