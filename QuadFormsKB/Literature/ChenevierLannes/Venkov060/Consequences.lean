/-
# Chenevier–Lannes: unconditional consequences of Venkov's identity

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition 2.3.2, Proposition-Definition 2.3.3 (a) and
Scholium 2.3.4, pp. 35–36. Printed page numbers.

Venkov's identity `VenkovRootSum n` is now proved for $n = 8, 16, 24$ (`venkovRootSum_eight`, `venkovRootSum_sixteen`,
`venkovRootSum_twentyFour`, `Venkov060/HarmonicTheta.lean`). This file removes the hypothesis from the results of
`Wave2/Venkov.lean` and `Wave2/VenkovRoots.lean` that the book states for these ranks. (Every other theorem of the
library with hypothesis `VenkovRootSum 24`, `VenkovRootSum 16` or `VenkovRootSum 8` is discharged by the same three
theorems; `scripts/input_audit.py` records them as discharged.)

**Proves** (all unconditional):
- `eq_zero_of_orthogonal_roots_uncond` (Proposition-Definition 2.3.3 (a), rank part): for an even unimodular lattice of
  dimension $n \in \{8, 16, 24\}$ with a root, a vector orthogonal to every root is $0$, i.e. $R(L)$ has rank $n$;
- `scholium_2_3_4_uncond` (Scholium 2.3.4): for $n = 24$, $\sum_{\alpha \in R(L)}(\alpha \cdot x)^2 = 2\,h(L)\;x \cdot x$;
- `card_root_dot_pm_one_twentyFour_uncond`: for $n = 24$ and a root $\alpha$, the number of roots $\beta$ with
  $\beta \cdot \alpha = \pm 1$ is $4h(L) - 8$;
- `venkov_eight_uncond`, `venkov_sixteen_uncond`: for $n = 8, 16$ the constant in Venkov's identity is $60$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Venkov060.HarmonicTheta
import QuadFormsKB.Literature.ChenevierLannes.Wave2.VenkovRoots

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

/-- `VenkovRootSum n` for $n \in \{8, 16, 24\}$. -/
theorem venkovRootSum_of_mem {n : ℕ} (hn : n = 8 ∨ n = 16 ∨ n = 24) : VenkovRootSum n := by
  rcases hn with rfl | rfl | rfl
  · exact venkovRootSum_eight
  · exact venkovRootSum_sixteen
  · exact venkovRootSum_twentyFour

/-- **The roots span (rank part of Proposition-Definition 2.3.3 (a))** (Chenevier–Lannes, p. 35). Unconditional: for an
even unimodular lattice $L$ of dimension $n \in \{8, 16, 24\}$ with $R(L) \ne \emptyset$, a vector $x \in \mathbb{R}^n$
with $\alpha \cdot x = 0$ for every root $\alpha$ is $0$. -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3 (a), p. 35 (R(L) has rank n, n = 8, 16, 24)"]
theorem eq_zero_of_orthogonal_roots_uncond {n : ℕ} (hn : n = 8 ∨ n = 16 ∨ n = 24) {Q : QuadForm ℤ n}
    (hQ : IsEvenUnimodular Q) (hR : (rootSet Q).Nonempty) {x : Fin n → ℝ}
    (hx : ∀ α ∈ rootSet Q, latDot Q α x = 0) : x = 0 :=
  eq_zero_of_orthogonal_roots (venkovRootSum_of_mem hn) (by omega) hQ hR hx

/-- **Scholium 2.3.4** (Chenevier–Lannes, p. 36). Unconditional: for a Niemeier lattice $L$ (even unimodular of
dimension $24$) and $x \in \mathbb{R}^{24}$, $\sum_{\alpha \in R(L)}(\alpha \cdot x)^2 = 2\,h(L)\;x \cdot x$. -/
@[kb "chenevierlannes2019" "Scholium 2.3.4, p. 36"]
theorem scholium_2_3_4_uncond {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) (x : Fin 24 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 2 * (coxeterNumber Q : ℝ) * (2 * Q.evalIn ℝ x) :=
  scholium_2_3_4 venkovRootSum_twentyFour hQ x

/-- **Roots with scalar product $\pm 1$ against a root** (Chenevier–Lannes, proof of Scholium 2.3.4, p. 36).
Unconditional: for $n = 24$ and $\alpha \in R(L)$, $\#\{\beta \in R(L) : \beta \cdot \alpha = \pm 1\} = 4h(L) - 8$. -/
@[kb "chenevierlannes2019" "Scholium 2.3.4, p. 36 (roots with β·α = ±1)"]
theorem card_root_dot_pm_one_twentyFour_uncond {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q)
    {α : Fin 24 → ℤ} (hα : α ∈ rootSet Q) :
    ((((rootSet_finite hQ.posDef).toFinset.filter (fun β => bZ Q β α = 1 ∨ bZ Q β α = -1)).card : ℕ) : ℝ) =
      4 * (coxeterNumber Q : ℝ) - 8 :=
  card_root_dot_pm_one_twentyFour venkovRootSum_twentyFour hQ hα

/-- **Venkov's identity for $n = 8$** with constant $60$. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35 (n = 8, constant 60)"]
theorem venkov_eight_uncond {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) (x : Fin 8 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 60 * (2 * Q.evalIn ℝ x) :=
  venkov_eight venkovRootSum_eight hQ x

/-- **Venkov's identity for $n = 16$** with constant $60$. Unconditional. -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35 (n = 16, constant 60)"]
theorem venkov_sixteen_uncond {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) (x : Fin 16 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 60 * (2 * Q.evalIn ℝ x) :=
  venkov_sixteen venkovRootSum_sixteen hQ x

end QuadFormsKB.ChenevierLannes
