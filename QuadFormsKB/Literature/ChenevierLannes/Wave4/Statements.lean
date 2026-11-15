/-
# Chenevier–Lannes, §3.4 and §5.1: statements of: further results

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §3.4.1, Proposition 3.4.1.2, p. 62; §3.4.2, Proposition 3.4.2.5
(Venkov), p. 66, and Theorem 3.4.2.10 (a), p. 69; §3.4.4, Propositions 3.4.4.2, 3.4.4.3, 3.4.4.4 (Borcherds) and the
properties of $\iota$, pp. 81–83; §5.1, the Siegel operator and the filtration of $\mathbb{C}[X_n]$ by the kernels of
the theta maps, pp. 123–124. Printed page numbers.

**Layer.** As in `Wave3/Statements.lean`: Niemeier lattices as integral forms on $\mathbb{Z}^{24}$, the
inner product `bQ`, Weyl vectors `IsWeylVector`, neighbours `voisLat`, root types `HasRootType` (via the root lattice),
Table 1.1 (`niemeierRootTable`); Siegel theta series `siegelTheta`, `thetaMap`, `thetaKer` (wave 1, `Theta.lean`).

**States** (named propositions, not proved; the reason is given in each docstring):
- `WeylVectorNorm` (Proposition 3.4.2.5, Venkov): $q(\rho) = h(h + 1)$;
- `RootDivisibility` (Proposition 3.4.1.2, in the form used for Niemeier lattices);
- `EvenHeightRoots` (Proposition 3.4.4.3): $\#\{\alpha \in R : 2 \mid \rho \cdot \alpha\} = 12h - \iota(R)$;
- `BorcherdsTwoNeighbors` (Proposition 3.4.4.4, Borcherds): $r_2(L_1) + r_2(L_2) = 3r_2(B) - 24r_1(B) + 48$;
- `CoxeterOfTwoNeighbor` (Proposition 3.4.4.2): $h(\mathrm{vois}_2(L; \rho)) = h/2 - \iota(R)/8 + 2$;
- `SiegelPhiTheta` (§5.1, p. 123): $\Phi\,\vartheta_{g+1}(L) = \vartheta_g(L)$;
- `ThetaFiltration` (§5.1, p. 123): $\mathrm{Ker}\,\vartheta_{g+1} \subset \mathrm{Ker}\,\vartheta_g$.

**Proves:**
- `ADEType.iota`, `adeIota` (§3.4.4, p. 81: the number $\iota(R)$ of odd exponents) and `iota_table` (unconditional,
  by computation over Table 1.1): $24 \le 2\iota(R)$ with equality exactly when $h$ is odd (p. 82, where the book
  prints the reversed inequality: an erratum), and the value
  $h/2 - \iota(R)/8 + 2$ predicted by Proposition 3.4.4.2 is, for each of the $23$ root systems, the Coxeter number of a
  Niemeier lattice ($0$, the Leech lattice, exactly for $24A_1$);
- `coxeter_dvd_weylVector_norm` (**conditional** on `VenkovRootSum 24` and `WeylVectorNorm`): the divisibility part of
  Theorem 3.4.2.10 (a): $h \mid q(\rho)$ and $h + 1 \mid q(\rho)$ for the Weyl vector $\rho \in L$.
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave4.WeylVectors
import QuadFormsKB.Literature.ChenevierLannes.Theta

open Matrix Filter

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser ADEType

variable {n : ℕ}

/-! ### Proposition 3.4.2.5 (Venkov) and the divisibility in the holy constructions -/

/-- **Proposition 3.4.2.5 (Venkov)** (Chenevier–Lannes, p. 66; named statement): for a Niemeier lattice $L$ with roots,
Coxeter number $h$, and a Weyl vector $\rho$, $q(\rho) = h(h + 1)$. The book's proof uses $\rho \cdot \rho =
\frac{n}{12}h(h + 1)$ for an irreducible root system of type ADE of rank $n$ (the "strange formula" of Freudenthal and
de Vries, checked on the classification) and Proposition-Definition 2.3.3 (b); neither the classification of root
systems nor that formula is in the library, so this is stated, not proved. -/
@[kb "chenevierlannes2019" "Prop. 3.4.2.5, p. 66"]
def WeylVectorNorm : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ ρ : Fin 24 → ℚ, IsWeylVector Q ρ →
    Q.evalIn ℚ ρ = coxeterNumber Q * (coxeterNumber Q + 1)

/-- **Theorem 3.4.2.10 (a), divisibility** (Chenevier–Lannes, p. 69): **conditional** on `VenkovRootSum 24` and
`WeylVectorNorm`. For a Niemeier lattice $L$ with roots and a Weyl vector $\rho$, $\rho \in L$ (Proposition 3.4.2.1,
`weylVector_mem_lattice`), $h$ is an integer (`coxeterNumber_eq_nat`) and $q(\rho) = h(h + 1)$, so both $h$ and $h + 1$
divide $q(\rho)$: the class of $\rho$ is isotropic in $L/hL$ and in $L/(h + 1)L$. (The $d$-primitivity of $\rho$,
the other half of (a), uses a simple root $\alpha$ with $\rho \cdot \alpha = 1$ and is not formalized.) -/
@[kb "chenevierlannes2019" "Thm. 3.4.2.10 (a), p. 69 (q(ρ) ≡ 0 mod h, h + 1; conditional)"]
theorem coxeter_dvd_weylVector_norm (hV : VenkovRootSum 24) (hN : WeylVectorNorm) {Q : QuadForm ℤ 24}
    (hQ : IsNiemeier Q) (hR : (rootSet Q).Nonempty) {ρ : Fin 24 → ℚ} (hρ : IsWeylVector Q ρ) :
    ∃ (r : Fin 24 → ℤ) (h : ℕ), ρ = cv r ∧ coxeterNumber Q = h ∧ (h : ℤ) ∣ Q.eval r ∧ ((h : ℤ) + 1) ∣ Q.eval r := by
  obtain ⟨r, rfl⟩ := weylVector_mem_lattice hV hQ hR hρ
  obtain ⟨h, hh⟩ := coxeterNumber_eq_nat hV hQ hR
  have hn := hN Q hQ hR (cv r) hρ
  rw [evalIn_cv, hh] at hn
  have he : Q.eval r = (h : ℤ) * ((h : ℤ) + 1) := by exact_mod_cast hn
  exact ⟨r, h, rfl, hh, ⟨(h : ℤ) + 1, he⟩, ⟨h, by rw [he]; ring⟩⟩

/-! ### Proposition 3.4.1.2 -/

/-- **Proposition 3.4.1.2** (Chenevier–Lannes, p. 62; named statement, in the form used for Niemeier lattices in the
proof of Proposition 3.4.1.1): for a Niemeier lattice $L$ with roots and Coxeter number $h$, an element $x \in V$ with
$\alpha \cdot x \in \mathbb{Z}$ for every root (a linear form integral on $R$), and an integer $d$ with
$2 \le d < h$, some root $\alpha$ has $d \mid \alpha \cdot x$. *Deviation:* the book states it for an irreducible
reduced root system; the Niemeier form applies it to one irreducible component of $R(L)$ (all have Coxeter number $h$,
Proposition-Definition 2.3.3 (b)). The book's proof uses the highest root and Bourbaki, Chap. VI, §1, Prop. 31 (heights
of roots); not formalized. -/
@[kb "chenevierlannes2019" "Prop. 3.4.1.2, p. 62 (Niemeier form)"]
def RootDivisibility : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ x : Fin 24 → ℚ,
    (∀ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) x = k) → ∀ d : ℕ, 2 ≤ d → (d : ℚ) < coxeterNumber Q →
      ∃ α ∈ rootSet Q, ∃ k : ℤ, bQ Q (cv α) x = d * k

/-! ### The number $\iota(R)$ of odd exponents and Propositions 3.4.4.2–3.4.4.4 -/

/-- **$\iota$ of an irreducible type** (Chenevier–Lannes, §3.4.4, p. 81): the number of odd exponents of the Weyl group,
$\iota(A_l) = \lfloor (l + 1)/2 \rfloor$, $\iota(D_l) = 2\lfloor l/2 \rfloor$, $\iota(E_6) = 4$, $\iota(E_7) = 7$,
$\iota(E_8) = 8$ (from the exponents in Bourbaki, Chap. VI, Planches I–VII). -/
@[kb "chenevierlannes2019" "§3.4.4, p. 81 (ι, number of odd exponents)"]
def ADEType.iota : ADEType → ℕ
  | A l => (l + 1) / 2
  | D l => 2 * (l / 2)
  | E6 => 4
  | E7 => 7
  | E8 => 8

/-- $\iota$ is additive: $\iota(R) = \sum_i \iota(R_i)$ over the irreducible components (p. 81). -/
def adeIota (R : Multiset ADEType) : ℕ := (R.map ADEType.iota).sum

/-- **The numerology of §3.4.4 on Table 1.1** (Chenevier–Lannes, pp. 81–82): unconditional, by computation. For each of
the $23$ root systems $R$ of Table 1.1 with Coxeter number $h$: (1) $24 = \operatorname{rank} R \le 2\iota(R)$, with
equality exactly when $h$ is odd (the book: exactly when every component is $A_d$ with $d$ even); (2) $8$ divides
$4h - \iota(R) + 16$, and the value $h' = h/2 - \iota(R)/8 + 2$ of Proposition 3.4.4.2 is $\le (h + 1)/2$
(Proposition 3.4.4.1) and is either $0$ (the Leech lattice, for $R = 24A_1$) or the Coxeter number of an entry of
Table 1.1.
*Erratum:* p. 82 prints "the inequality $l \ge 2\iota(R)$" for a root system of type ADE of rank $l$; the correct
inequality is $l \le 2\iota(R)$ ($\iota(D_{24}) = 24$; $\iota(A_d) = (d + 1)/2$ for $d$ odd), which is also what
Proposition 3.4.4.1 needs ($h' \le (h + 1)/2 \iff 2\iota(R) \ge 24$). -/
@[kb "chenevierlannes2019" "§3.4.4, pp. 81–82 (ι on Table 1.1)"]
theorem iota_table : ∀ e ∈ niemeierRootTable,
    24 ≤ 2 * adeIota e.1 ∧ (2 * adeIota e.1 = 24 ↔ e.2 % 2 = 1) ∧ 8 ∣ 4 * e.2 + 16 - adeIota e.1 ∧
      2 * ((4 * e.2 + 16 - adeIota e.1) / 8) ≤ e.2 + 1 ∧
      ((4 * e.2 + 16 - adeIota e.1) / 8 = 0 ∨ (4 * e.2 + 16 - adeIota e.1) / 8 ∈ niemeierRootTable.map Prod.snd) := by
  intro e he
  simp only [niemeierRootTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  decide

/-- **The number $r_k(\Lambda)$ of vectors of norm $k$** (Chenevier–Lannes, §3.4.4, p. 83) of a lattice
$\Lambda \subset \mathbb{Q}^n$ for the inner product of $Q$: $\#\{x \in \Lambda : x \cdot x = k\}$. -/
noncomputable def latRepNum (Q : QuadForm ℤ n) (Λ : Submodule ℤ (Fin n → ℚ)) (k : ℚ) : ℕ :=
  {x | x ∈ Λ ∧ bQ Q x x = k}.ncard

/-- **Proposition 3.4.4.3** (Chenevier–Lannes, p. 82; named statement): for a Niemeier lattice $L$ with roots of type
$R$ and a Weyl vector $\rho$, the number of roots $\alpha$ with $\rho \cdot \alpha$ even is $12h(L) - \iota(R)$. The
book's proof uses Kostant's theorem relating the heights of the positive roots to the exponents of the Weyl group; not
in the library. -/
@[kb "chenevierlannes2019" "Prop. 3.4.4.3, p. 82"]
def EvenHeightRoots : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ R : Multiset ADEType, HasRootType Q R →
    ∀ ρ : Fin 24 → ℚ, IsWeylVector Q ρ →
      ({α | α ∈ rootSet Q ∧ ∃ k : ℤ, bQ Q (cv α) ρ = 2 * k}.ncard : ℚ) = 12 * coxeterNumber Q - adeIota R

/-- **Proposition 3.4.4.4 (Borcherds)** (Chenevier–Lannes, p. 83; named statement): let $B$ be an odd unimodular lattice
of dimension $24$ and $L_1, L_2$ its two even $2$-neighbours; then
$$r_2(L_1) + r_2(L_2) = 3\,r_2(B) - 24\,r_1(B) + 48.$$
*Formulation.* By Borcherds' dictionary (§3.1, p. 51), $B$ and its even neighbours are described from $L_1 =
\mathbb{Z}^{24}$ (`stdLat 24`, an even unimodular lattice) and one $2$-neighbour $L_2$ of it: with $M = L_1 \cap L_2$,
$M^\sharp / M = \{0, a, b, a + b\}$ with $L_1/M = \langle a \rangle$, $L_2/M = \langle b\rangle$, and $B$ is the
preimage of $\langle a + b \rangle$, i.e. $B = M + \mathbb{Z}(x_1 + x_2)$ for any $x_1 \in L_1 \setminus L_2$,
$x_2 \in L_2 \setminus L_1$. The book's proof uses modular forms for the theta group $\Gamma_\theta$ and the transfer to
$\mathrm{SL}_2(\mathbb{Z})$ (Lemma 3.4.4.5, $\vartheta_{L_1} + \vartheta_{L_2} = \mathrm{tr}\,\vartheta_B$); modular
forms for $\Gamma_\theta$ are not in the library. -/
@[kb "chenevierlannes2019" "Prop. 3.4.4.4, p. 83"]
def BorcherdsTwoNeighbors : Prop :=
  ∀ Q : QuadForm ℤ 24, IsEvenUnimodular Q →
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    ∀ L₂ ∈ neighbors Q 2, ∀ x₁ x₂ : Fin 24 → ℚ, x₁ ∈ stdLat 24 → x₁ ∉ L₂ → x₂ ∈ L₂ → x₂ ∉ stdLat 24 →
      ((latRepNum Q (stdLat 24) 2 + latRepNum Q L₂ 2 : ℕ) : ℤ) =
        3 * latRepNum Q (stdLat 24 ⊓ L₂ ⊔ Submodule.span ℤ {x₁ + x₂}) 2
          - 24 * latRepNum Q (stdLat 24 ⊓ L₂ ⊔ Submodule.span ℤ {x₁ + x₂}) 1 + 48

/-- **Proposition 3.4.4.2** (Chenevier–Lannes, p. 81; named statement): for a Niemeier lattice $L$ with roots of type
$R$, a Weyl vector $\rho = $ `cv r` $\in L$ and $v \in L$ with $\rho \cdot v$ odd (so $\rho$ is $2$-primitive;
$q(\rho) = h(h + 1)$ is even), the $2$-neighbour $\mathrm{vois}_2(L; \rho)$ (`voisLat`) has Coxeter number
$$h(\mathrm{vois}_2(L; \rho)) = \frac{h(L)}{2} - \frac{\iota(R)}{8} + 2,$$
where the Coxeter number of the $2$-neighbour is $r_2/24$ (`latRepNum`). The book derives it from Propositions 3.4.4.3,
3.4.4.4 and Corollary 3.1.16 (two of which are stated here, not proved). -/
@[kb "chenevierlannes2019" "Prop. 3.4.4.2, p. 81"]
def CoxeterOfTwoNeighbor : Prop :=
  ∀ Q : QuadForm ℤ 24, IsNiemeier Q → (rootSet Q).Nonempty → ∀ R : Multiset ADEType, HasRootType Q R →
    ∀ r v : Fin 24 → ℤ, IsWeylVector Q (cv r) → (2 : ℤ) ∣ bZ Q r v - 1 →
      (latRepNum Q (voisLat Q 2 r v) 2 : ℚ) / 24 = coxeterNumber Q / 2 - adeIota R / 8 + 2

/-! ### The Siegel operator and the theta filtration (§5.1) -/

/-- **Siegel's operator on theta series** (Chenevier–Lannes, §5.1, p. 123; named statement): for an even unimodular
lattice $L$ and $Z' \in \mathbb{H}_g$,
$$\Phi\,\vartheta_{g+1}(L)(Z') = \lim_{t \to +\infty} \vartheta_{g+1}(L)\begin{pmatrix}Z'&0\\0&it\end{pmatrix}
= \vartheta_g(L)(Z')$$
(`phiEmbed`): only the $X$ with last column $0$ survive the limit. Not proved here (a limit of an infinite sum,
dominated convergence on $\mathbb{Z}^{n \times (g + 1)}$). -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (Φ ϑ_{g+1} = ϑ_g)"]
def SiegelPhiTheta : Prop :=
  ∀ (n : ℕ) (Q : QuadForm ℤ n), IsEvenUnimodular Q → ∀ (g : ℕ), ∀ Z' ∈ siegelUpper g,
    Tendsto (fun t : ℝ => siegelTheta (g + 1) Q (phiEmbed Z' t)) atTop (nhds (siegelTheta g Q Z'))

/-- **The theta filtration** (Chenevier–Lannes, §5.1, p. 123; named statement): $\mathrm{Ker}\,\vartheta_{g+1} \subset
\mathrm{Ker}\,\vartheta_g$ on $\mathbb{C}[X_n]$, so the kernels form a decreasing filtration (from $\Phi \circ
\vartheta_{g+1} = \vartheta_g$, `SiegelPhiTheta`, and $\begin{pmatrix}Z'&0\\0&it\end{pmatrix} \in \mathbb{H}_{g+1}$ for
$t > 0$). -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (Ker ϑ_{g+1} ⊂ Ker ϑ_g)"]
def ThetaFiltration : Prop := ∀ n g : ℕ, thetaKer n (g + 1) ⊆ thetaKer n g

end QuadFormsKB.ChenevierLannes
