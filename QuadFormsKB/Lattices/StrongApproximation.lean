/-
# Strong approximation for the spin group: the named input `StrongApproximationSpin`

**Layer:** lattices in $(V, Q) = (F^n, Q)$ over a number field $F$ (`Lattices/ClassSet.lean`), the spinor kernels
$O'(V) \le O(V)(F)$ and $O'(V_{\mathbb A_f}) \le O(V)(\mathbb A_f)$ (`Lattices/SpinorKernel.lean`).

**Defines** the named input `StrongApproximationSpin F`: for every nondegenerate, indefinite (`IsIndefinite`)
form $Q$ over $F$ in $n \ge 3$ variables and every lattice $L$ in $V$,
$$O'(V_{\mathbb A_f}) \subseteq O'(V)\cdot O(\hat L), \qquad O(\hat L) = \{h : h_\mathfrak p L_\mathfrak p = L_\mathfrak p\ \forall\mathfrak p\},$$
i.e. every $h \in O'(V_{\mathbb A_f})$ is $h = \gamma k$ with $\gamma \in O'(V)$ rational (embedded diagonally) and
$k \in O(\hat L)$ (`locStab Q L`).

**Status: cited input, not proved here.** This is the strong approximation theorem for rotations, Kneser 1956 and
Eichler 1952 (O'Meara 1963, 104:3 [unverified]; Cassels 1978, Ch. 10 Thm 7.1 [unverified]): if $\dim V \ge 3$ and
$V_w$ is isotropic at some infinite place $w$, then $O'(V)$ is dense in $O'(V_{\mathbb A_f})$ (the adelic group away
from the infinite places). The statement here is the density statement tested against the open subgroups
$O(\hat L) \cap O'(V_{\mathbb A_f})$: if $O'(V)$ is dense then $h\,O(\hat L)^{-1}$ (an open neighbourhood of $h$) meets
$O'(V)$, which is the field `approx`. It follows from strong approximation for $\mathrm{Spin}(V)$ (simply connected,
$F_w$-isotropic; Kneser 1966, Platonov 1969) and $\theta(\text{local spinor kernels})$; neither is formalized.

*Not equivalent to its main consequence.* Eichler's theorem (`Lattices/Eichler.lean`: spinor genus = class) only
needs some $\gamma \in O(V)$ with $\gamma L = hL$; the input gives $\gamma$ in the smaller group $O'(V)$ and for every
$h \in O'(V_{\mathbb A_f})$, a statement about the group, not about the lattice $hL$ alone.

**Interface (stable; consumed by the Kneser-connectivity work, branch `kneser-connectivity`).** Do not change the
signature of `StrongApproximationSpin` or of its field `approx` without updating `docs/handoff/spinor-genera.md`.
-/
import QuadFormsKB.Lattices.SpinorKernel

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB

open Lattices

/-- **Strong approximation for the spin group (rotations) — a named, cited input.**
For every $n \ge 3$ and every form `Q : QuadForm F n` that is nondegenerate (`Q.Nondegenerate`) and indefinite
(`IsIndefinite Q`: isotropic at some infinite place of $F$), every lattice $L$ in $V = F^n$ and every
$h \in O'(V_{\mathbb A_f})$ (`spinorKernelAf Q`), there is a rational $\gamma \in O'(V)$ (`spinorKernel Q F`) with
$\gamma^{-1}h \in O(\hat L)$ (`locStab Q L`), i.e. $h \in O'(V)\,O(\hat L)$.

Kneser 1956 / Eichler 1952; O'Meara 1963, 104:3 [unverified]; Cassels 1978, Ch. 10 [unverified]. **Not proved in
this repository**: every theorem using it is conditional on it (classified as an input in `docs/inputs.toml`). -/
@[kb "omeara1963" "104:3, strong approximation for rotations [unverified]"]
structure StrongApproximationSpin (F : Type*) [Field F] [NumberField F] : Prop where
  /-- $O'(V_{\mathbb A_f}) \subseteq O'(V) \cdot O(\hat L)$ for nondegenerate indefinite $V$ of dimension $n \ge 3$. -/
  approx : ∀ {n : ℕ} (Q : QuadForm F n), 3 ≤ n → Q.Nondegenerate → IsIndefinite Q →
    ∀ (L : Lat F n) (h : OAf Q), h ∈ spinorKernelAf Q →
      ∃ γ : orthGroup Q F, γ ∈ spinorKernel Q F ∧ (diagF Q γ)⁻¹ * h ∈ locStab Q L

end QuadFormsKB
