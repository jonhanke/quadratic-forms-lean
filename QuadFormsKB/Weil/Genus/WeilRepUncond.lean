/-
# The Weil representation of $\mathrm{Sp}_{2g}$, unconditionally

**Layer:** local harmonic analysis; combines `Weil/Genus/Model.lean` (the Schrödinger operators and `weilRepSp`,
conditional on the named input `SiegelPresentation` and the interface `IsGLModel`) with their discharges
`siegelPresentation` (every infinite field, `Weil/Genus/SiegelPres.lean`) and `isGLModel_V` (every finite place and every
genus, `Weil/Genus/HaarGL.lean`).

**Results.**
* `weilRepSpInf`: for a model $D$ over $K$, an infinite field $k$ with $2 \ne 0$ and a ring map $\iota : k \to K$, under
  the interface `IsGLModel D a g`, the Weil representation
  $\omega : \mathrm{Sp}_{2g}(k) \to \operatorname{End}_{\mathbb C}S(V^g)$ with the Schrödinger formulas on $n(B)$, $m(A)$, $w$
  (`weilRepSpInf_spN`, `weilRepSpInf_spM`, `weilRepSpInf_spW`); no presentation input.
* `weilRepSpV`: at a finite place $v$ of a number field $F$, for every genus $g$ and every diagonal
  $Q = \langle a_0, \dots, a_{n-1}\rangle$ over $F_v$, $n = 2m$, the Weil representation of $\mathrm{Sp}_{2g}(F_v)$ on
  $S(V_v^g)$ (all locally constant compactly supported functions on $M_{n\times g}(F_v)$, `mem_Sg_iff`), with the
  Schrödinger formulas on the generators (`weilRepSpV_spN`, `weilRepSpV_spM`, `weilRepSpV_spW`). Unconditional.

Sources: Weil, Acta Math. 111 (1964), §14 [unverified]; Kudla, *Notes on the local theta correspondence* (1996),
§I.1, Prop. 1.3 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.Genus.Model
import QuadFormsKB.Weil.Genus.SiegelPres
import QuadFormsKB.Weil.Genus.HaarGL

open Matrix

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

section Abstract

variable {K : Type*} [CommRing K] [MeasurableSpace K] {m g : ℕ} {D : LocalData K} {a : Fin (2 * m) → Kˣ}
variable (hD : D.IsModel) (hGL : IsGLModel D a g) {k : Type*} [Field k] [Infinite k] (ι : k →+* K)

/-- **The Weil representation of $\mathrm{Sp}_{2g}(k)$ on $S(V^g)$ for an infinite field $k$** (Schrödinger model):
`weilRepSp` with the named input `SiegelPresentation` discharged by `siegelPresentation`. Hypotheses: `hD` (a model),
`hGL` (the interface `IsGLModel`), `ι : k → K` a ring map, `h2 : (2 : k) ≠ 0`. -/
@[kb "weil1964" "§14, Thm. 2 and §43 (for even $\\dim V$ the Weil representation is a representation of $\\mathrm{Sp}$) [unverified]"]
def weilRepSpInf (h2 : (2 : k) ≠ 0) : Sp g k →* Module.End ℂ (Sg D m g) :=
  weilRepSp hD hGL ι siegelPresentation h2

theorem weilRepSpInf_spN (h2 : (2 : k) ≠ 0) (B : Matrix (Fin g) (Fin g) k) (hB : Bᵀ = B) :
    weilRepSpInf hD hGL ι h2 (spN B hB) = endN hGL ι B :=
  weilRepSp_spN hD hGL ι siegelPresentation h2 B hB

theorem weilRepSpInf_spM (h2 : (2 : k) ≠ 0) (A : GL (Fin g) k) :
    weilRepSpInf hD hGL ι h2 (spM A) = endM hGL ι A :=
  weilRepSp_spM hD hGL ι siegelPresentation h2 A

theorem weilRepSpInf_spW (h2 : (2 : k) ≠ 0) :
    weilRepSpInf hD hGL ι h2 spW = endW (a := a) hD :=
  weilRepSp_spW hD hGL ι siegelPresentation h2

end Abstract

section Place

open IsDedekindDomain NumberField

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

variable {m : ℕ}

/-- **The local Weil representation of $\mathrm{Sp}_{2g}(F_v)$ at a finite place $v$** (every genus $g$, dyadic places
included) on $S(V_v^g)$, $V_v = F_v^{n}$ with $Q = \langle a_0, \dots, a_{n-1}\rangle$, $n = 2m$. Unconditional:
`weilRepSpInf` with $k = F_v$, $\iota = \mathrm{id}$, the model `isModel_V v` and the interface `isGLModel_V v a g`. -/
@[kb "weil1964" "§14, Thm. 2 and §43 (the Weil representation of $\\mathrm{Sp}$ over a $\\mathfrak p$-adic field, $\\dim V$ even) [unverified]"]
def weilRepSpV (a : Fin (2 * m) → (Fv)ˣ) (g : ℕ) : Sp g Fv →* Module.End ℂ (Sg (localDataV v) m g) :=
  weilRepSpInf (isModel_V v) (isGLModel_V v a g) (RingHom.id Fv) two_ne_zero

theorem weilRepSpV_spN (a : Fin (2 * m) → (Fv)ˣ) (g : ℕ) (B : Matrix (Fin g) (Fin g) Fv) (hB : Bᵀ = B) :
    weilRepSpV v a g (spN B hB) = endN (isGLModel_V v a g) (RingHom.id Fv) B :=
  weilRepSpInf_spN _ _ _ _ B hB

theorem weilRepSpV_spM (a : Fin (2 * m) → (Fv)ˣ) (g : ℕ) (A : GL (Fin g) Fv) :
    weilRepSpV v a g (spM A) = endM (isGLModel_V v a g) (RingHom.id Fv) A :=
  weilRepSpInf_spM _ _ _ _ A

theorem weilRepSpV_spW (a : Fin (2 * m) → (Fv)ˣ) (g : ℕ) : weilRepSpV v a g spW = endW (a := a) (isModel_V v) :=
  weilRepSpInf_spW _ _ _ _

end Place

end QuadFormsKB.WeilRep.Genus
