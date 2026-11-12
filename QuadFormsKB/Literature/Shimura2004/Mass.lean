/-
# Shimura 2004, §13.11 and §13.14: the mass of a genus, and the exact mass formula it uses

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §13.11 (printed pp. 133–134) and
the proof of Theorem 13.14 (p. 135). Page numbers are printed pages.

**What the book says.** Shimura (§13.11) recalls the mass $m(G,U) = \sum_{a\in B}[\Gamma^a:1]^{-1}$ of a reductive
group $G$ relative to an open subgroup $U$ of $G_{\mathbb A}$ when $G_{\mathbf a}$ is compact ((13.12c); $B$ a set of
representatives of $G\backslash G_{\mathbb A}/U$, $\Gamma^a = G\cap aUa^{-1}$), puts $m(G,\Lambda) = m(G,U)$ for the
stabilizer $U$ of a lattice $\Lambda$ (13.12d), and quotes from his earlier papers
* (13.13b) $m(SO^\varphi(V),\Lambda) = 2\,m(O^\varphi(V),\Lambda)$ for every $\mathfrak g$-lattice $\Lambda$
  ([S97, Lemma 24.2 (1)], [S99a, Lemma 5.6 (1)]);
* the exact mass formula for the genus of maximal lattices, [S99a, Theorem 5.8] (= Shimura 1999, *An exact mass
  formula for orthogonal groups*, Duke Math. J. 97), used in the proof of Theorem 13.14 to evaluate $m(H, D)$.

The book does not restate the exact mass formula; the library proves it (Hanke 2005, Theorem 5.1, which is Shimura's
formula for $\Lambda = \mathcal O_F^n$ maximal, extended by Gan–Hanke–Yu 2001 to the places excluded by Shimura's
hypothesis). This file records the library's proofs under the book's labels; nothing is reproved.

**Dictionary.** A number field $F$ with ring of integers $\mathfrak g = \mathcal O_F$; the form is
`Q₀ : QuadForm (𝓞 F) n` on $V = F^n$ and $\Lambda = \mathcal O_F^n$ (`stdLat F n`), or any lattice `L : Lat F n`.
The double coset mass `dcMass Γ K` is $\sum_{\Gamma\alpha K}|\Gamma\cap\alpha K\alpha^{-1}|^{-1}$ (`Tamagawa.dcMass`);
with $\Gamma = SO(V)(F)$, $K = SO(\hat\Lambda)$ inside $SO(V)(\mathbb A_f)$ it is Shimura's $m(SO^\varphi(V),\Lambda)$
for totally definite $\varphi$ (where $G_{\mathbf a}$ is compact and $D\supseteq G_{\mathbf a}$, so
$G\backslash G_{\mathbb A}/D = G\backslash G_{\mathbf h}/D_{\mathbf h}$). `Tamagawa.mass` is the $O$-mass
$\sum_{\mathrm{cls}\,M\subseteq\mathrm{gen}\,L}|O(M)|^{-1}$, Shimura's $m(O^\varphi(V),\Lambda)$.

**Proves** (all unconditional, by the library's theorems; standard axioms only)
* `mass_SO_eq_two_mul_mass_O` and `mass_SO_eq_two_mul_mass_O_lat`: (13.13b) for totally positive definite $\varphi$,
  for $\Lambda = \mathcal O_F^n$ ($n \ge 1$) and for every integral lattice when $n$ is odd.
* `exact_mass_maximal_definite`, `exact_mass_maximal`: the exact mass formula [S99a, Thm. 5.8] for the genus of the
  maximal lattice $\mathcal O_F^n$, $n \ge 3$, in the totally definite case (as a sum over the $SO$-classes) and for
  every signature (through Hanke's archimedean normalization), with no hypothesis on $\det\varphi$.

*Not covered here:* (13.13a) (the index formula $m(U') = [U:U']\,m(U)$) for general open $U'$, and the general
non-compact definition (13.12a) with volumes of $\Gamma\backslash S$ on the symmetric space.
-/
import QuadFormsKB.Tamagawa.MassSOLatNF
import QuadFormsKB.Literature.Hanke2005.TheoremFiveOneGeneral
import QuadFormsKB.Citation

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **(13.13b)** (Shimura 2004, §13.11, p. 133, quoting [S97, Lemma 24.2 (1)] and [S99a, Lemma 5.6 (1)]):
$m(SO^\varphi(V), \Lambda) = 2\,m(O^\varphi(V), \Lambda)$, here for $\Lambda = \mathcal O_F^n$, $n \ge 1$, $\varphi$
nondegenerate and totally positive definite, and $\Lambda$ integral. Library: `Tamagawa.mass_SO_eq_two_mul_mass`. -/
@[kb "shimura2004" "(13.13b), p. 133 (m(SO^φ(V), Λ) = 2 m(O^φ(V), Λ); totally definite, Λ = 𝔤ⁿ)"]
theorem mass_SO_eq_two_mul_mass_O (hQ : Q₀.Nondegenerate) (hn : 0 < n) (hpd : IsTotallyPosDef QF)
    (hLi : IsIntegral QF (stdLat F n).1) :
    dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF (stdLat F n)).subgroupOf (soAf QF)) =
      2 * mass QF (stdLat F n) :=
  mass_SO_eq_two_mul_mass Q₀ hQ hn hpd hLi

/-- **(13.13b)** (Shimura 2004, §13.11, p. 133) for every integral lattice $\Lambda$ when $n$ is odd ($\varphi$
nondegenerate, totally positive definite). Library: `Tamagawa.mass_SO_eq_two_mul_mass_lat`. -/
@[kb "shimura2004" "(13.13b), p. 133 (m(SO^φ(V), Λ) = 2 m(O^φ(V), Λ); totally definite, n odd, any lattice)"]
theorem mass_SO_eq_two_mul_mass_O_lat (hQ : Q₀.Nondegenerate) (hn : Odd n) (hpd : IsTotallyPosDef QF)
    (L : Lat F n) (hLi : IsIntegral QF L.1) :
    dcMass ((ratPoints QF).subgroupOf (soAf QF)) ((locStab QF L).subgroupOf (soAf QF)) = 2 * mass QF L :=
  mass_SO_eq_two_mul_mass_lat Q₀ hQ hn hpd L hLi

/-- **The exact mass of the genus of maximal lattices, totally definite case** ([S99a, Theorem 5.8], used by
Shimura 2004 in the proof of Theorem 13.14, p. 135, and in (13.12c), p. 133): for $F$ totally real, $n \ge 3$,
$\varphi$ nondegenerate and totally positive definite and $\Lambda = \mathcal O_F^n$ maximal,
$m(SO^\varphi(V), \Lambda) = \sum_{a}[\Gamma^a : 1]^{-1}$ (sum over $SO(V)\backslash SO(V)_{\mathbb A}/D$) equals the
explicit product `theorem51RHSGen Q₀` (Euler factors, $\zeta_F$ values, local factors $\lambda_v$). No hypothesis on
$\det\varphi$. Library: `Hanke2005.theorem51_definite_general`. -/
@[kb "shimura2004" "§13.11 (13.12c), p. 133, and proof of Thm. 13.14, p. 135 (exact mass, citing [S99a, Thm. 5.8])"]
theorem exact_mass_maximal_definite [IsTotallyReal F] (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) (hmax : StdIsMaximal Q₀) :
    ∑' i : DC Q₀, ((Nat.card (unitGroup Q₀ i) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (theorem51RHSGen Q₀) :=
  theorem51_definite_general hn Q₀ hQ hpd hmax

/-- **The exact mass of the genus of maximal lattices, any signature** ([S99a, Theorem 5.8]; Shimura 2004, §13.11,
p. 133, (13.12a) with volumes on the symmetric space): for $n \ge 3$, $\varphi$ nondegenerate and $\mathcal O_F^n$
maximal, Hanke's mass (sum of the archimedean covolumes of the $\Gamma^a$, normalized by the volumes of the compact
forms) equals `theorem51RHSGen Q₀`. Library: `Hanke2005.theorem51_general`. -/
@[kb "shimura2004" "§13.11 (13.12a), p. 133 (exact mass, citing [S99a, Thm. 5.8])"]
theorem exact_mass_maximal (hn : 3 ≤ n) (hQ : Q₀.Nondegenerate) (hmax : StdIsMaximal Q₀) :
    hankeMass Q₀ hQ = ENNReal.ofReal (theorem51RHSGen Q₀) :=
  theorem51_general hn Q₀ hQ hmax

end QuadFormsKB.Shimura2004
