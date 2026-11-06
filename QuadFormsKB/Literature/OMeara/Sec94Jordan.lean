/-
# O'Meara §94: the lattices $L^{\mathfrak s_i}$ from a Jordan splitting

**Setting** (as in `Sec91Jordan.lean`): $R$ a discrete valuation ring (O'Meara's $\mathfrak o$) with fraction field
$F$, $2 \ne 0$ in $F$, a quadratic space $(V, Q)$ over $F$, lattices = `Submodule R V`. A Jordan splitting
$L = L_1 \perp \cdots \perp L_t$ is `IsJordanSplitting Q L Ls` with `Ls : Fin t → Submodule R V` (0-based: O'Meara's
$L_1, \dots, L_t$ are `Ls 0, …, Ls (t-1)`), $\mathfrak s_i = \mathfrak sL_i$ strictly decreasing. $L^{\mathfrak a}$ is
`subA Q 𝔞 L` (§82I: $\{x \in L : B(x, L) \subseteq \mathfrak a\}$).

**Proves** the last formula of §94 (O'Meara 1973 printing, p. 280; the machine-read text garbled it, the page image
reads)
$$L^{\mathfrak s_i} = (\pi^{s_i - s_1}L_1) \perp \cdots \perp (\pi^{s_i - s_{i-1}}L_{i-1}) \perp L_i \perp \cdots
\perp L_t,$$
where $\mathfrak s_j = \mathfrak p^{s_j}$; here $\pi^{s_i - s_j}L_j$ is written $\mathfrak s_i\mathfrak s_j^{-1}L_j$
(the same lattice): `subA_scale_isOrthSplit`.
-/
import QuadFormsKB.Literature.OMeara.Sec91Type
import QuadFormsKB.Literature.OMeara.Sec82Sub

open QuadraticMap Submodule Module
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- The component $L_j^{\mathfrak s_i}$ of a Jordan splitting: $\mathfrak s_i\mathfrak s_j^{-1}L_j$ for $j < i$ and
$L_j$ for $j \ge i$. -/
theorem subA_scale_component {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) (hfg : ∀ j, (Ls j).FG) (i j : Fin t) :
    subA Q (scale Q (Ls i)) (Ls j) =
      if j < i then (scale Q (Ls i) * (1 / scale Q (Ls j))) • Ls j else Ls j := by
  split_ifs with hji
  · have hlt : scale Q (Ls i) < scale Q (Ls j) := hJ.scale_strictAnti hji
    exact subA_of_isModular_of_ge Q (scale_fg Q (hfg i)) (hJ.modular i).1 (hJ.modular j) (hfg j) hlt.le
  · have hle : scale Q (Ls j) ≤ scale Q (Ls i) := hJ.scale_strictAnti.antitone (not_lt.mp hji)
    exact subA_of_isModular_of_le Q (hJ.modular j) hle

/-- **$L^{\mathfrak s_i}$ from a Jordan splitting** (O'Meara 1973, §94, p. 280): for a Jordan splitting
$L = L_1 \perp \cdots \perp L_t$ with scales $\mathfrak s_1 \supsetneq \cdots \supsetneq \mathfrak s_t$,
$$L^{\mathfrak s_i} = \mathfrak s_i\mathfrak s_1^{-1}L_1 \perp \cdots \perp \mathfrak s_i\mathfrak s_{i-1}^{-1}L_{i-1}
\perp L_i \perp \cdots \perp L_t,$$
O'Meara's $(\pi^{s_i - s_1}L_1) \perp \cdots \perp (\pi^{s_i - s_{i-1}}L_{i-1}) \perp L_i \perp \cdots \perp L_t$. -/
@[kb "omeara1963" "§94, p. 280 (L^{s_i} = π^{s_i−s_1}L_1 ⊥ ⋯ ⊥ π^{s_i−s_{i−1}}L_{i−1} ⊥ L_i ⊥ ⋯ ⊥ L_t)"]
theorem subA_scale_isOrthSplit {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) (hfg : ∀ j, (Ls j).FG) (i : Fin t) :
    IsOrthSplit Q (subA Q (scale Q (Ls i)) L)
      (fun j => if j < i then (scale Q (Ls i) * (1 / scale Q (Ls j))) • Ls j else Ls j) := by
  have hcomp := subA_scale_component Q hJ hfg i
  have hle : ∀ j, (if j < i then (scale Q (Ls i) * (1 / scale Q (Ls j))) • Ls j else Ls j) ≤ Ls j := by
    intro j
    rw [← hcomp j]
    exact fun x hx => hx.1
  refine ⟨fun j k hjk x hx y hy => hJ.split.orth j k hjk x (hle j hx) y (hle k hy),
    hJ.split.indep.mono hle, ?_⟩
  rw [subA_eq_iSup Q hJ.split]
  exact iSup_congr fun j => (hcomp j).symm

end QuadFormsKB.OMeara
