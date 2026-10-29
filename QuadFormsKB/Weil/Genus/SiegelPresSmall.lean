/-
# The presentation of $\mathrm{Sp}_{2g}(k)$ for every field, conditional on the small finite fields

**Layer:** pure algebra over a field $k$.

**Result** (`siegelPresentation_of_smallField`). For every genus $g$ and every field $k$, the named input
`SiegelPresentation g k` (the presentation of $\mathrm{Sp}_{2g}(k)$ by the Siegel parabolic and $w$) follows from the
smaller named input `SiegelPresentationSmallField g k`, which asserts it only when $k$ is a finite field with at most
$3g$ elements. Every other field is covered by `siegelPresentation_of_card` (`SiegelPresFinite.lean`; the infinite
fields also by `siegelPresentation`). For $g = 1$ the small-field input is proved (`siegelPresentationSmallField_one`,
from `siegelPresentation_one`).

**What remains** (the input `SiegelPresentationSmallField`, $g \ge 2$): for a fixed $g$ only the finitely many
finite fields $\mathbb F_q$ with $q \le 3g$ (e.g. $q = 2, 3, 4, 5$ for $g = 2$). There the big-cell method fails (over
$\mathbb F_2$, $g = 2$ no common $n(T)w$ moves the needed elements into the big cell), and the proof needs the Bruhat
decomposition $\mathrm{Sp}_{2g}(k) = \bigsqcup_{r \le g} P w_r P$.
The statement has been confirmed by a computer coset enumeration (outside Lean) for
$(g, q) = (2, 2), (2, 3), (3, 2)$.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 [unverified]; Rao, Pacific J. Math. 157
(1993), §2 (Bruhat decomposition relative to the Siegel parabolic) [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.SiegelPresFinite

open Matrix

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

universe u v

variable {g : ℕ} {k : Type v} [Field k]

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ over the small finite fields** (a named input; Kudla 1996, §I.1;
Rao 1993, §2): field `small`: if $k$ is finite (`Finite k`) with at most $3g$ elements ($\#k \le 3g$), then
`SiegelPresentation g k` holds. Vacuous for infinite fields and for finite fields with more than $3g$ elements, where
the presentation is proved (`siegelPresentation_of_card`). -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations; finite fields with at most $3g$ elements) [unverified]"]
structure SiegelPresentationSmallField (g : ℕ) (k : Type v) [Field k] : Prop where
  small : Finite k → Nat.card k ≤ 3 * g → SiegelPresentation.{u} g k

/-- **The presentation of $\mathrm{Sp}_{2g}(k)$ for every field $k$, conditional on the small finite fields**
(every genus $g$): the named input `SiegelPresentation g k` follows from `SiegelPresentationSmallField g k`
(hypothesis `h`), i.e. it is proved except for the finite fields with at most $3g$ elements. -/
@[kb "kudla1996" "§I.1 (generators $m(a)$, $n(b)$, $w$ of $\\mathrm{Sp}(W)$ and their relations) [unverified]"]
theorem siegelPresentation_of_smallField (h : SiegelPresentationSmallField.{u} g k) :
    SiegelPresentation.{u} g k := by
  by_cases hk : ((3 * g : ℕ) : Cardinal) < Cardinal.mk k
  · exact siegelPresentation_of_card hk
  · have hle : Cardinal.mk k ≤ ((3 * g : ℕ) : Cardinal) := le_of_not_gt hk
    have hfin : Finite k := Cardinal.lt_aleph0_iff_finite.1 (lt_of_le_of_lt hle (Cardinal.natCast_lt_aleph0))
    refine h.small hfin ?_
    have := Fintype.ofFinite k
    rw [Cardinal.mk_fintype] at hle
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast hle

/-- **Genus one:** the small-field input holds for $g = 1$ (from `siegelPresentation_one`). -/
@[kb "kudla1996" "§I.1 ($\\mathrm{Sp}_2 = \\mathrm{SL}_2$ and its Bruhat cells) [unverified]"]
theorem siegelPresentationSmallField_one : SiegelPresentationSmallField.{u} 1 k :=
  ⟨fun _ _ => siegelPresentation_one⟩

end QuadFormsKB.WeilRep.Genus
