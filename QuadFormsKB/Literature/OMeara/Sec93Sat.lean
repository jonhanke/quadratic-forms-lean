/-
# O'Meara 93:21–93:22: saturated Jordan splittings

**Setting** (as in `Sec93E.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$, $2$ not a unit of $R$ (O'Meara's dyadic local field), $(V, Q)$ a regular quadratic space over $F$,
lattices `Submodule R V`; a Jordan splitting is `IsJordanSplitting Q L Ls`, and it is saturated (`IsSaturated`,
§93E, p. 264) when $\mathfrak gL_i = \mathfrak g_i$ for every $i$. Indices are $0$-based.

**States** Proposition 93:21 (p. 265) as the named statement `SaturatedSplittingExistence` (assumed, not proved
here: O'Meara's proof uses 93:18, whose classification of unimodular lattices of dimension $\ge 3$ is not
formalized).

**Proves**
* `IsSaturated.normGroup_le` (93:22, the direction that needs no hypothesis): a saturated Jordan splitting maximizes
  every $\mathfrak gL_i$ among the Jordan splittings of $L$;
* `isSaturated_iff_forall_normGroup_le` (**Example 93:22**, p. 266), conditional on the named statement 93:21: when
  all $\dim L_i \ge 3$, a Jordan splitting is saturated if and only if it maximizes all the groups $\mathfrak gL_i$.
-/
import QuadFormsKB.Literature.OMeara.Sec93EBasic

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Saturated

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Proposition 93:21** (O'Meara 1963, §93E, p. 265), *named statement* (assumed, not proved here): "Suppose $L$ has
a Jordan splitting $L = L_1 \perp \cdots \perp L_t$ in which $\dim L_i \ge 3$ for $1 \le i \le t$. Then $L$ has a
saturated Jordan splitting." Here $L$ is a lattice on the regular quadratic space $V$ over the dyadic local field $F$
(Henselian discrete valuation ring with finite residue field, $2$ not a unit). (The machine-read text reads
"$\dim L_i = 3$"; the page image reads "$\dim L_i \ge 3$".) -/
@[kb "omeara1963" "§93E, 93:21, p. 265"]
structure SaturatedSplittingExistence : Prop where
  exists_saturated : ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L : Submodule R V) [L.IsLattice F] {t : ℕ} (Ls : Fin t → Submodule R V),
      IsJordanSplitting Q L Ls → (∀ i, 3 ≤ finrank R (Ls i)) →
      ∃ Ks : Fin t → Submodule R V, IsSaturated Q L Ks

variable {R Q}

omit [HenselianLocalRing R] [Finite (ResidueField R)] [FiniteDimensional F V] in
/-- The fundamental norm groups of two Jordan splittings of the same lattice agree index by index: they depend only
on $L$ and the scale $\mathfrak s_i$, which is the same for both splittings by 91:9. -/
theorem fundNormGroup_eq_of_isJordanSplitting {L : Submodule R V} (hfg : L.FG) {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q L Ks) (i : Fin t) (j : Fin t') (hij : (i : ℕ) = j) :
    fundNormGroup Q L Ks j = fundNormGroup Q L Ls i := by
  obtain ⟨h, hs⟩ := hL.sameJordanType Q hfg hK
  have hj : Fin.cast h i = j := Fin.ext (by simp [hij])
  have hsc : scale Q (Ks j) = scale Q (Ls i) := by rw [← hj]; exact (hs i).1.symm
  simp only [fundNormGroup, fundSub, hsc]

omit [HenselianLocalRing R] [Finite (ResidueField R)] [FiniteDimensional F V] in
/-- **Example 93:22, first half** (O'Meara 1963, §93E, p. 266): a saturated Jordan splitting
$L = L_1 \perp \cdots \perp L_t$ maximizes all the groups $\mathfrak gL_i$: for every Jordan splitting
$L = L_1' \perp \cdots \perp L_t'$, $\mathfrak gL_i' \subseteq \mathfrak gL_i$. (No dimension hypothesis is needed for
this direction: $\mathfrak gL_i' \subseteq \mathfrak g_i = \mathfrak gL_i$.) -/
@[kb "omeara1963" "§93E, 93:22, p. 266"]
theorem IsSaturated.normGroup_le {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hsat : IsSaturated Q L Ls) {t' : ℕ} (Ks : Fin t' → Submodule R V) (hK : IsJordanSplitting Q L Ks)
    (i : Fin t) (j : Fin t') (hij : (i : ℕ) = j) : normGroup Q (Ks j) ≤ normGroup Q (Ls i) := by
  rw [hsat.2 i, ← fundNormGroup_eq_of_isJordanSplitting hfg hsat.1 hK i j hij]
  exact normGroup_le_fundNormGroup Q hfg hK j

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- **Example 93:22** (O'Meara 1963, §93E, p. 266), conditional on Proposition 93:21 (`SaturatedSplittingExistence`):
"Suppose the Jordan splitting $L = L_1 \perp \cdots \perp L_t$ has $\dim L_i \ge 3$ for $1 \le i \le t$. Then [...] the
given Jordan splitting is saturated if and only if it has the following property: if $L = L_1' \perp \cdots \perp
L_t'$ is any Jordan splitting of $L$, then $\mathfrak gL_i \supseteq \mathfrak gL_i'$ for $1 \le i \le t$. So in this
case a saturated splitting is one that maximizes all the groups $\mathfrak gL_i$." (Another Jordan splitting may be
indexed by any `Fin t'`; by 91:9, $t' = t$, and the condition compares components with the same index.) -/
@[kb "omeara1963" "§93E, 93:22, p. 266"]
theorem isSaturated_iff_forall_normGroup_le (hS : SaturatedSplittingExistence R Q) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hdim : ∀ i, 3 ≤ finrank R (Ls i)) :
    IsSaturated Q L Ls ↔ ∀ {t' : ℕ} (Ks : Fin t' → Submodule R V), IsJordanSplitting Q L Ks →
      ∀ (i : Fin t) (j : Fin t'), (i : ℕ) = j → normGroup Q (Ks j) ≤ normGroup Q (Ls i) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  refine ⟨fun hsat _ Ks hK i j hij => hsat.normGroup_le hfg Ks hK i j hij, fun hmax => ?_⟩
  obtain ⟨Ks, hKs⟩ := hS.exists_saturated h2p hQ L Ls hL hdim
  refine ⟨hL, fun i => le_antisymm (normGroup_le_fundNormGroup Q hfg hL i) ?_⟩
  rw [← fundNormGroup_eq_of_isJordanSplitting hfg hL hKs.1 i i rfl, ← hKs.2 i]
  exact hmax Ks hKs.1 i i rfl

end Saturated

end QuadFormsKB.OMeara
