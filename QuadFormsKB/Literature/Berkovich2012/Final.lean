import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.LocalTwo

/-!
# Berkovich–Hanke–Jagy: the statement of Lemma 3.3, and Theorem 6.1, Corollary 6.2 from it

Source: A. Berkovich, J. Hanke and W. Jagy, *A proof of the S-genus identities for ternary quadratic
forms*, arXiv:1010.1926v2 (bib key `berkovich2012`), §3, Lemma 3.3, p. 3; §6, Theorem 6.1 and
Corollary 6.2, p. 7.

* `SGenusParam S B`: the statement of Lemma 3.3 (proved: `lemma_3_3`), the parametrization of the genera of the S-genus by
  sign vectors, as binary forms $B_\sigma$ of discriminant $-8S$ with $\varepsilon_p(B_\sigma + 2Sz^2) = \sigma_p$.
* `SGenusParam.toStructure`: Lemma 3.3 implies the former input `SGenusStructure` (whose local fields,
  Lemma 3.1 at $p \mid S$ and at $p = 2$, are now proved: `local_odd_of_disc`, `local_two_of_disc`).
* `theorem_6_1_of_param`, `corollary_6_2_of_param`: the S-genus identities from `SGenusParam`. Lemma 3.3 is
  proved in `Lemma33.lean` (`lemma_3_3`), which also states the unconditional `theorem_6_1`, `corollary_6_2`.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel

/-- **Lemma 3.3, the statement** (proved: `lemma_3_3` in `Lemma33.lean`) (the genera of the S-genus are parametrized by the sign vectors).
`B σ`, for each sign vector $\sigma = (\sigma_p)_{p \mid S}$, is a positive definite integral binary form of
discriminant $-8S$, such that the genera of the ternary forms $B_\sigma(x, y) + 2Sz^2$ exhaust the S-genus
and are pairwise distinct, and $B_\sigma(x,y) + 2Sz^2$ has the signs $\varepsilon_p = \sigma_p$
(Definition 3.2, in the form of Remark 3.4: `epsP`).

Fields:
- `posDef`: each $B_\sigma$ is positive definite;
- `disc`: each $B_\sigma$ has discriminant $-8S$;
- `cover`: every class of the S-genus lies in the genus of some $B_\sigma(x,y) + 2Sz^2$;
- `sign`: $\varepsilon_p(B_\sigma(x,y) + 2Sz^2) = \sigma_p$ for every $p \mid S$.

The remaining part of Lemma 3.3, that the genera for distinct $\sigma \ne \tau$ are distinct, follows from `sign`
(`SGenusParam.disjoint`). -/
@[kb "berkovich2012" "§3, Lemma 3.3, p. 3 (statement)"]
structure SGenusParam (S : ℕ) (B : Signs S → BinQF) : Prop where
  posDef : ∀ σ, (B σ).PosDef'
  disc : ∀ σ, (B σ).disc = -8 * S
  cover : SGenus S ⊆ ⋃ σ, genusClasses (sForm S (B σ))
  sign : ∀ σ (p : {p // p ∈ S.primeFactors}),
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    epsP p (sForm S (B σ)) = sgnB (σ p)

/-- Every class in the genus of $B_\sigma(x,y) + 2Sz^2$ has $\varepsilon_p = \sigma_p$. -/
theorem SGenusParam.epsP_class {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (h : SGenusParam S B) (σ : Signs S) (p : {p // p ∈ S.primeFactors}) {c : QClass 3}
    (hc : c ∈ genusClasses (sForm S (B σ))) :
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    QClass.epsP p c = sgnB (σ p) := by
  haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  obtain ⟨α, hα, hiso⟩ := local_odd_of_disc hSodd hSsf (h.disc σ) (Nat.dvd_of_mem_primeFactors p.2)
  rw [QClass.epsP_eq_legendre (p : ℕ) hα hiso hc, ← epsP_eq_legendre (p : ℕ) (SameGenus.refl _) hα hiso]
  exact h.sign σ p

/-- **Lemma 3.3, injectivity** (the genera of $B_\sigma(x,y) + 2Sz^2$ for distinct sign vectors are distinct):
a consequence of the signs. -/
@[kb "berkovich2012" "§3, Lemma 3.3 and its proof, p. 3 (injectivity)"]
theorem SGenusParam.disjoint {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (h : SGenusParam S B) (σ τ : Signs S) (hne : σ ≠ τ) :
    Disjoint (genusClasses (sForm S (B σ))) (genusClasses (sForm S (B τ))) := by
  rw [Set.disjoint_left]
  intro c hσ hτ
  apply hne
  funext p
  have e1 := h.epsP_class hSodd hSsf σ p hσ
  have e2 := h.epsP_class hSodd hSsf τ p hτ
  rw [e1] at e2
  cases hs : σ p <;> cases ht : τ p <;> simp_all [sgnB]

/-- **Lemma 3.3 gives the local structure** (with Lemma 3.1, proved): for $S$ odd squarefree, `SGenusParam`
implies `SGenusStructure`. The local fields come from `local_odd_of_disc` (with
$\left(\frac{-\alpha}{p}\right) = \varepsilon_p = \sigma_p$ by `epsP_eq_legendre`) and `local_two_of_disc`. -/
theorem SGenusParam.toStructure {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (h : SGenusParam S B) : SGenusStructure S B where
  posDef := h.posDef
  disc := h.disc
  cover := h.cover
  disjoint := h.disjoint hSodd hSsf
  local_odd := fun σ p => by
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    obtain ⟨α, hα, hiso⟩ := local_odd_of_disc hSodd hSsf (h.disc σ) (Nat.dvd_of_mem_primeFactors p.2)
    refine ⟨α, hα, ?_, hiso⟩
    rw [← epsP_eq_legendre (p : ℕ) (SameGenus.refl _) hα hiso]
    exact h.sign σ p
  local_two := fun σ => local_two_of_disc hSodd (h.disc σ)

/-- **Theorem 6.1 (the twisted S-genus identity).** Let $S$ be an odd squarefree natural number,
$W \mid S$, and $m \in \mathbb{N}$ with $W \mid m$ and $m \equiv 1, 2 \pmod 4$. Then
$$\sum_{Q \in S\text{-genus}} \epsilon_W(Q)\, \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} =
W\, \frac{r_{x^2+y^2+z^2}(m/W^2)}{48},$$
where the right side is $0$ if $W^2 \nmid m$. The sum is over the classes of the S-genus
(`SGenus`), $\epsilon_W = \prod_{p \mid W} \varepsilon_p$ (`QClass.epsW`).

From `SGenusParam S B` (Lemma 3.3, proved: `lemma_3_3`); the unconditional form is `theorem_6_1`. Siegel's formula and Lemmas 3.1,
4.1–4.3, 5.1 and 6.3 are proved. -/
theorem theorem_6_1_of_param {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (hP : SGenusParam S B) {W : ℕ} (hW : W ∣ S)
    {m : ℕ} (hWm : W ∣ m) (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (QClass.epsW W c : ℝ) * c.repNum m / c.autCard =
      W * (if W ^ 2 ∣ m then (repNum (sumSq 3) ((m / W ^ 2 : ℕ) : ℤ) : ℝ) else 0) / 48 :=
  have hS := hP.toStructure hSodd hSsf
  theorem_6_1_of_mass hSodd hSsf hS (lemma_5_1 hSodd hS) hW hWm hm4

/-- **Corollary 6.2 (the S-genus identity).** For $S$ odd squarefree and $m \equiv 1, 2 \pmod 4$,
$$\sum_{Q \in S\text{-genus}} \frac{r_Q(m)}{|\mathrm{Aut}(Q)|} = \frac{r_{x^2+y^2+z^2}(m)}{48}.$$
Theorem 6.1 with $W = 1$, from `SGenusParam S B`; the unconditional form is `corollary_6_2`. -/
theorem corollary_6_2_of_param {S : ℕ} (hSodd : Odd S) (hSsf : Squarefree S) {B : Signs S → BinQF}
    (hP : SGenusParam S B) {m : ℕ} (hm4 : m % 4 = 1 ∨ m % 4 = 2) :
    ∑ᶠ c ∈ SGenus S, (c.repNum m : ℝ) / c.autCard = (repNum (sumSq 3) (m : ℤ) : ℝ) / 48 :=
  have hS := hP.toStructure hSodd hSsf
  corollary_6_2_of_mass hSodd hSsf hS (lemma_5_1 hSodd hS) hm4

end QuadFormsKB.Berkovich2012
