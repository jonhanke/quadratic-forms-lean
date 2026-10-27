/-
# O'Meara, Chapter VI: notions for quadratic spaces used throughout the chapter

**Setting.** $F$ is a field and $(V, Q)$, $(U, Q_U)$ are quadratic spaces over $F$ (Mathlib `QuadraticForm F V`).
O'Meara's standing assumptions of Part Three are that the characteristic of $F$ is not $2$ and that spaces are
finite dimensional; they are added as hypotheses where they are used. A space is *regular* when its quadratic radical
is zero, written `Q.radical = ⊥` (in characteristic $\ne 2$ this is the nondegeneracy of O'Meara's bilinear form $B$,
Mathlib `QuadraticMap.radical_eq_ker_associated`).

**Defines**
* `IsRepresentedBy Q_U Q`: $U$ is *represented by* $V$, written $U \to V$ (O'Meara 1963, §41A, p. 84): there is an
  isometry of $U$ into $V$, i.e. an injective linear map $\sigma \colon U \to V$ with $Q(\sigma x) = Q_U(x)$;
* `IsUniversal Q`: $V$ is *universal* (O'Meara 1963, §41A, p. 83, row 41.d3 of the coverage audit): $Q(V) = F$, i.e.
  every element of $F$ is a value $Q(x)$.

**Proves** the basic facts used in the chapter: representation is reflexive and transitive and is implied by
isometry (`IsRepresentedBy.refl`, `IsRepresentedBy.trans`, `IsRepresentedBy.of_equivalent`), an isometry from a
regular space is automatically injective (`isRepresentedBy_of_isometry`), and representation preserves the
represented values (`IsRepresentedBy.exists_eq`).
-/
import Mathlib
import QuadFormsKB.Citation

open QuadraticMap

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type*} [Field F]
variable {U V W : Type*} [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- **$U$ is represented by $V$** (O'Meara 1963, §41A, p. 84): there is a *representation* (O'Meara's "isometry of
$U$ into $V$") $\sigma \colon U \to V$, an injective $F$-linear map with $Q(\sigma x) = Q_U(x)$ for all $x \in U$.

Mathlib's `QuadraticMap.Isometry` (notation `Q_U →qᵢ Q`) does not require injectivity; for a regular $U$ every such
map is injective (`isRepresentedBy_of_isometry`). -/
@[kb "omeara1963" "§41A, p. 84 (U is represented by V: an isometry of U into V)"]
def IsRepresentedBy (QU : QuadraticForm F U) (Q : QuadraticForm F V) : Prop :=
  ∃ σ : QU →qᵢ Q, Function.Injective σ

/-- **$V$ is universal** (O'Meara 1963, §41A, p. 83): $Q(V) = F$, i.e. every $\alpha \in F$ is $Q(x)$ for some
$x \in V$. -/
@[kb "omeara1963" "§41A, p. 83 (universal space, Q(V) = F)"]
def IsUniversal (Q : QuadraticForm F V) : Prop :=
  ∀ a : F, ∃ x : V, Q x = a

namespace IsRepresentedBy

theorem refl (Q : QuadraticForm F V) : IsRepresentedBy Q Q :=
  ⟨Isometry.id Q, Function.injective_id⟩

theorem trans {QU : QuadraticForm F U} {QV : QuadraticForm F V} {QW : QuadraticForm F W}
    (h₁ : IsRepresentedBy QU QV) (h₂ : IsRepresentedBy QV QW) : IsRepresentedBy QU QW := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ.comp σ, hτ.comp hσ⟩

theorem of_equivalent {QU : QuadraticForm F U} {QV : QuadraticForm F V} (h : QU.Equivalent QV) :
    IsRepresentedBy QU QV := by
  obtain ⟨e⟩ := h
  exact ⟨e.toIsometry, e.injective⟩

/-- A represented space has its values among the values of the representing space. -/
theorem exists_eq {QU : QuadraticForm F U} {QV : QuadraticForm F V} (h : IsRepresentedBy QU QV) (x : U) :
    ∃ y : V, QV y = QU x := by
  obtain ⟨σ, -⟩ := h
  exact ⟨σ x, σ.map_app x⟩

end IsRepresentedBy

/-- **An isometry of a regular space is a representation** (O'Meara 1963, 42:7, p. 93, in the case of a regular
source): if $\operatorname{rad} U = 0$ and $2 \ne 0$ in $F$, a linear map preserving $Q$ is injective. -/
theorem isRepresentedBy_of_isometry [Invertible (2 : F)] {QU : QuadraticForm F U} {QV : QuadraticForm F V}
    (hU : QU.radical = ⊥) (σ : QU →qᵢ QV) : IsRepresentedBy QU QV := by
  refine ⟨σ, ?_⟩
  change Function.Injective σ.toLinearMap
  rw [← LinearMap.ker_eq_bot (f := σ.toLinearMap), eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [← hU, QuadraticMap.radical_eq_ker_associated, LinearMap.mem_ker]
  ext y
  have h := σ.map_app (x + y)
  have h1 := σ.map_app x
  have h2 := σ.map_app y
  simp only [Isometry.coe_toLinearMap] at hx
  rw [map_add, hx, zero_add] at h
  rw [hx, QuadraticMap.map_zero] at h1
  rw [LinearMap.zero_apply, QuadraticMap.associated_apply]
  rw [← h, ← h1, h2]
  simp

end QuadFormsKB.OMeara
