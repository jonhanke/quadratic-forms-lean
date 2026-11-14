/-
# Chenevier–Lannes: Venkov's identity for the roots (Proposition 2.3.2, Scholium 2.3.4)

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §2.3, Proposition 2.3.2, Proposition-Definition 2.3.3 (a) and
Scholium 2.3.4, pp. 35–36. Printed page numbers.

**Layer.** Even unimodular lattices as integral forms $Q = q_L$ (`EvenUnimodular.lean`): for $x, y \in \mathbb{R}^n =
\mathbb{R} \otimes L$ the book's inner product is $x \cdot y = x^{\mathsf T}Hy$ ($H$ the Hessian, the Gram matrix of $L$),
so $x \cdot x = 2\,Q(x)$; a root $\alpha \in R(L)$ (`rootSet`) is a vector of $\mathbb{Z}^n$ with $Q(\alpha) = 1$.

**States** (named input):
- `VenkovRootSum n` (Proposition 2.3.2): for every even unimodular $L$ of dimension $n$ and every $x \in \mathbb{R}^n$,
  $$\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = \frac{2\,|R(L)|}{n}\; x \cdot x.$$
  The book proves it for $n = 8, 16, 24$ with Venkov's theta series with harmonic coefficients of degree $2$ (a cusp
  form of weight $n/2 + 2 \le 14$ vanishes); harmonic theta series are not formalized here.

**Proves** (conditional on `VenkovRootSum n` where stated):
- `eq_zero_of_orthogonal_roots` (conditional; the rank part of Proposition-Definition 2.3.3 (a)): if $R(L) \ne \emptyset$,
  the only vector orthogonal to all roots is $0$, i.e. $R(L)$ spans $\mathbb{R} \otimes L$ (rank $n$);
- `scholium_2_3_4` (conditional; Scholium 2.3.4): for $n = 24$ and $R(L) \ne \emptyset$,
  $\sum_{\alpha}(\alpha \cdot x)^2 = 2\,h(L)\,x \cdot x$;
- `venkov_eight`, `venkov_sixteen` (conditional): for $n = 8, 16$ the constant is $2|R(L)|/n = 60$ (unconditionally
  $|R(L)| = 240, 480$, `card_rootSet_eight`, `card_rootSet_sixteen`).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.ThetaSeries

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel

variable {n : ℕ}

/-- **The inner product $\alpha \cdot x = \alpha^{\mathsf T}Hx$** of an integral vector $\alpha$ with a real vector $x$,
for the lattice $L$ with Gram matrix $H$ = `Q.hessian`. -/
noncomputable def latDot (Q : QuadForm ℤ n) (α : Fin n → ℤ) (x : Fin n → ℝ) : ℝ :=
  (fun i => (α i : ℝ)) ⬝ᵥ (Q.hessian.map (Int.cast : ℤ → ℝ) *ᵥ x)

/-- **Proposition 2.3.2 (Venkov)** (Chenevier–Lannes, p. 35; named input): for every even unimodular lattice $L$ of
dimension $n$ and every $x \in \mathbb{R} \otimes L = \mathbb{R}^n$,
$$\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = \frac{2\,|R(L)|}{n}\; x \cdot x, \qquad x \cdot x = 2\,Q(x).$$
The book states and proves it for $n = 8, 16, 24$ (theta series with harmonic coefficients of degree $2$: the
corresponding modular form of weight $n/2 + 2$ is a cusp form, hence $0$ for $n/2 + 2 < 12$ and $n/2 + 2 = 14$). Assumed
here, not proved; the sum is a finite sum (`finsum`; $R(L)$ is finite). -/
@[kb "chenevierlannes2019" "Prop. 2.3.2, p. 35"]
structure VenkovRootSum (n : ℕ) : Prop where
  /-- $\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = \frac{2|R(L)|}{n}\,(2Q(x))$ for every even unimodular $Q$ and real
  $x$. -/
  root_sum : ∀ Q : QuadForm ℤ n, IsEvenUnimodular Q → ∀ x : Fin n → ℝ,
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 2 * ((rootSet Q).ncard : ℝ) / n * (2 * Q.evalIn ℝ x)

/-- The root set of a positive definite form is finite. -/
theorem rootSet_finite {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : (rootSet Q).Finite :=
  IntQF.PosDef.repSet_finite hQ 1

/-- **The roots span (rank part of Proposition-Definition 2.3.3 (a))** (Chenevier–Lannes, p. 35): **conditional** on
`VenkovRootSum n`. If an even unimodular lattice $L$ of dimension $n \ge 1$ has a root, then a vector
$x \in \mathbb{R}^n$ orthogonal to every root is $0$; that is, $R(L)$ has rank $n$. *Proof* (the book's): the left side
of Venkov's identity vanishes, the constant $2|R(L)|/n$ is positive, so $x \cdot x = 0$. -/
@[kb "chenevierlannes2019" "Prop.-Def. 2.3.3 (a), p. 35 (R(L) has rank n; conditional)"]
theorem eq_zero_of_orthogonal_roots (hV : VenkovRootSum n) (hn : 0 < n) {Q : QuadForm ℤ n}
    (hQ : IsEvenUnimodular Q) (hR : (rootSet Q).Nonempty) {x : Fin n → ℝ}
    (hx : ∀ α ∈ rootSet Q, latDot Q α x = 0) : x = 0 := by
  by_contra hne
  have h := hV.root_sum Q hQ x
  rw [finsum_mem_of_eqOn_zero (fun α hα => by simp [hx α hα])] at h
  have hc : (0 : ℝ) < (rootSet Q).ncard := by
    exact_mod_cast (Set.ncard_pos (rootSet_finite hQ.posDef)).mpr hR
  have hq := hQ.posDef.evalIn_real_pos x hne
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have : (0 : ℝ) < 2 * ((rootSet Q).ncard : ℝ) / n * (2 * Q.evalIn ℝ x) := by positivity
  linarith

/-- **Scholium 2.3.4** (Chenevier–Lannes, p. 36): **conditional** on `VenkovRootSum 24`. For a Niemeier lattice $L$ and
$x \in \mathbb{R}^{24}$, $\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = 2\,h(L)\; x \cdot x$, with $h(L) = |R(L)|/24$
(`coxeterNumber`, Proposition-Definition 2.3.3 (c)). (The book assumes $R(L) \ne \emptyset$; with $h = 0$ the identity
also holds for the Leech lattice.) -/
@[kb "chenevierlannes2019" "Scholium 2.3.4, p. 36 (conditional)"]
theorem scholium_2_3_4 (hV : VenkovRootSum 24) {Q : QuadForm ℤ 24} (hQ : IsEvenUnimodular Q) (x : Fin 24 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 2 * (coxeterNumber Q : ℝ) * (2 * Q.evalIn ℝ x) := by
  rw [hV.root_sum Q hQ x, coxeterNumber, ← ncard_rootSet]
  push_cast
  ring

/-- **Venkov's identity for $n = 8$** (Chenevier–Lannes, Proposition 2.3.2 with $|R(L)| = 240$): **conditional** on
`VenkovRootSum 8`, $\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = 60\; x \cdot x$. -/
theorem venkov_eight (hV : VenkovRootSum 8) {Q : QuadForm ℤ 8} (hQ : IsEvenUnimodular Q) (x : Fin 8 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 60 * (2 * Q.evalIn ℝ x) := by
  rw [hV.root_sum Q hQ x, card_rootSet_eight hQ]
  norm_num

/-- **Venkov's identity for $n = 16$** (Chenevier–Lannes, Proposition 2.3.2 with $|R(L)| = 480$): **conditional** on
`VenkovRootSum 16`, $\sum_{\alpha \in R(L)} (\alpha \cdot x)^2 = 60\; x \cdot x$. -/
theorem venkov_sixteen (hV : VenkovRootSum 16) {Q : QuadForm ℤ 16} (hQ : IsEvenUnimodular Q) (x : Fin 16 → ℝ) :
    ∑ᶠ α ∈ rootSet Q, latDot Q α x ^ 2 = 60 * (2 * Q.evalIn ℝ x) := by
  rw [hV.root_sum Q hQ x, card_rootSet_sixteen hQ]
  norm_num

end QuadFormsKB.ChenevierLannes
