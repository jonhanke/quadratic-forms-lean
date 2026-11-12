/-
# Shimura 2004, §9: genera and classes over a number field, the spinor norm count

**Source.** G. Shimura, *Arithmetic and Analytic Theories of Quadratic Forms and Clifford Groups*, Mathematical
Surveys and Monographs 109, American Mathematical Society, 2004 (key `shimura2004`), §9, printed pp. 79–92. Page
numbers are printed pages.

**What the book says.** For a number field $F$, $(V,\varphi)$ nondegenerate of dimension $n$, $G = SO^\varphi(V)$
and an open subgroup $D$ of $G_{\mathbb A}$ containing $G_{\mathbf a}$ (e.g. the stabilizer of a lattice), the
$G$-classes in the $G$-genus of a lattice correspond to $G\backslash G_{\mathbb A}/D$ (§9.3). With the spinor norm
$\sigma : G_{\mathbb A} \to F_{\mathbb A}^\times/F_{\mathbb A}^{\times 2}$ (9.12) and $\sigma(D)\subseteq
F_{\mathbb A}^\times$ the preimage of its image:
* **Theorem 9.18** (Eichler): if $n \ge 3$ and $SO^\varphi_{\mathbf a}$ is not compact, $S_{\mathbb A}\subseteq S^0D$,
  where $S_{\mathbb A}$ is the adelic spinor kernel and $S^0 = \{\alpha\in SO^\varphi\mid\sigma(\alpha)=1\}$.
* **Lemma 9.19 (iii)**: under the same hypotheses, $x\mapsto\sigma(x)$ is a bijection
  $SO^\varphi\backslash SO^\varphi_{\mathbb A}/D \to F_{\mathbb A}^\times/F^\times\sigma(D)$.

**In the library** (from the proof of Shimura 1999, Lemma 2.4, which is the same statement): `Hanke2005.SpinorIdele`
proves Lemma 9.19 (iii) for $D$ the stabilizer $SO(\hat L)\times G_{\mathbf a}$ of $L = \mathcal O_F^n$ and
$\varphi$ given by a form `Q₀ : QuadForm (𝓞 F) n` (so $L$ is free; the double cosets are over the finite adeles,
which is the same since $D\supseteq G_{\mathbf a}$); "not compact at some archimedean place" is `IsIndefinite`.
This file records those proofs under the book's labels.

**Proves** (unconditional; standard axioms only)
* `lemma_9_19_iii`: the bijection $SO\backslash SO_{\mathbb A}/D \simeq F_{\mathbb A}^\times/F^\times\sigma(D)$ and
  the class number $\#(SO\backslash SO_{\mathbb A}/D) = [F_{\mathbb A}^\times : F^\times\sigma(D)]$, for
  $D = $ the stabilizer of $\mathcal O_F^n$.
* `theorem_9_18_weak`: $S_{\mathbb A}\subseteq SO^\varphi(F)\,D$ for the same $D$. This is weaker than Theorem 9.18
  ($SO^\varphi(F)$ in place of $S^0$) and is what the library's Lemma 2.4 (1) of Shimura 1999 gives.

*Not covered here:* Theorem 9.20 (Kneser's strong approximation for $G^1(V)$, the library has it in the form of
O'Meara 104:4, `Lattices.strongApproximationSpin`, for the spinor kernel), Lemma 9.23, Theorem 9.26 (the class number
of the genus of maximal lattices as an index of ideal groups $[\mathfrak I:\mathfrak I_1]$; needs the exceptional
primes of §9.7), and general open $D$.
-/
import QuadFormsKB.Literature.Hanke2005.SpinorIdeleMain
import QuadFormsKB.Literature.Hanke2005.ClassIndex
import QuadFormsKB.Citation

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Shimura2004

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005 QuadFormsKB.Hanke2005.SpinorIdele QuadFormsKB.Hanke2005.EqualMasses

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)

/-- **Lemma 9.19 (iii)** (Shimura 2004, p. 87), for $D$ the stabilizer of $L = \mathcal O_F^n$: if $n \ge 3$ and
$\varphi$ is nondegenerate and indefinite at some archimedean place ($SO^\varphi_{\mathbf a}$ not compact), the
spinor norm gives a bijection $SO^\varphi\backslash SO^\varphi_{\mathbb A}/D \simeq F_{\mathbb A}^\times/F^\times
\sigma(D)$ (`dcEquivIdele`, with `dcEquivIdele_mk`: the class of $b$ goes to the class of any idèle representing
$\sigma(b)$), and therefore the number of $SO$-classes in the genus of $L$ is $[F_{\mathbb A}^\times :
F^\times\sigma(D)]$. Library: `Hanke2005.SpinorIdele.dcEquivIdele`, `card_DC_eq_index_idele`. -/
@[kb "shimura2004" "Lemma 9.19 (iii), p. 87 (SO\\SO_A/D ≅ F_A^×/F^×σ(D); D the stabilizer of 𝔤ⁿ)"]
theorem lemma_9_19_iii (hn : 3 ≤ n) (hind : IsIndefinite QF) :
    Nonempty (DC Q₀ ≃ IdeleGroup (𝓞 F) F ⧸ classIdeleSub QF (nondegenerate_map Q₀ hQ)) ∧
      Nat.card (DC Q₀) = (classIdeleSub QF (nondegenerate_map Q₀ hQ)).index :=
  ⟨⟨dcEquivIdele Q₀ hQ hn hind⟩, card_DC_eq_index_idele Q₀ hQ hn hind⟩

/-- **Theorem 9.18, weak form** (Shimura 2004, p. 87; Eichler): for $n \ge 3$ and $\varphi$ nondegenerate and
indefinite at some archimedean place, every rotation in the adelic spinor kernel $S_{\mathbb A}$ (finite part) lies in
$SO^\varphi(F)\,D$ for $D$ the stabilizer of $\mathcal O_F^n$. Shimura's statement has the smaller group $S^0$ (the
global spinor kernel) in place of $SO^\varphi(F)$ and an arbitrary open $D \supseteq SO^\varphi_{\mathbf a}$.
Library: `Hanke2005.spinorKernel_le_classSub`. -/
@[kb "shimura2004" "Thm. 9.18, p. 87 (weak form: S_A ⊆ SO^φ D for D the stabilizer of 𝔤ⁿ)"]
theorem theorem_9_18_weak (hn : 3 ≤ n) (hind : IsIndefinite QF) (h : SOAf Q₀)
    (hh : (h : OAf QF) ∈ spinorKernelAf QF) : h ∈ classSub Q₀ hn hQ hind :=
  spinorKernel_le_classSub Q₀ hn hQ hind h hh

end QuadFormsKB.Shimura2004
