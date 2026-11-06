import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.Lemma63
import QuadFormsKB.Siegel.LocalProduct
import QuadFormsKB.Siegel.Mass
import QuadFormsKB.Defs.Binary

/-!
# Berkovich–Hanke–Jagy: the S-genus, the signs $\varepsilon_p$, and comparison of Euler products

Source: A. Berkovich, J. Hanke and W. Jagy, arXiv:1010.1926v2 (bib key `berkovich2012`), §1 (definition
of the S-genus), Definition 3.2 (the signs $\varepsilon_p$), Theorem 6.1 ($\epsilon_W$).

* `sForm S B`: the ternary form $B(x, y) + 2S z^2$ for a binary form $B$.
* `SGenus S`: the S-genus, the set of classes of ternary forms locally equivalent (at every place) to
  some $B(x,y) + 2Sz^2$ with $B$ a positive definite integral binary form of discriminant $-8S$.
* `epsP p Q`: the sign $\varepsilon_p$ of Definition 3.2. The source defines it as
  $\left(\frac{-\alpha}{p}\right)$ where $Q \sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$
  (Lemma 3.1); equivalently (Remark 3.4) $\varepsilon_p = \left(\frac{-n}{p}\right)$ for any $n$
  represented by $Q$ with $p \nmid n$ (such $n$ are $\equiv \alpha \cdot \square \pmod p$). The Lean
  definition uses the represented values: $\varepsilon_p(Q) = 1$ if $Q$ represents some $n$ with
  $p \nmid n$ and $\left(\frac{-n}{p}\right) = 1$, and $-1$ otherwise. For classes in the S-genus the
  two agree (this is part of the named input `SGenusStructure`).
* `eulerProductValue_ratio`: if two forms have the same local densities outside a finite set $T$ of
  primes, their natural-order Euler products differ by the finite product over $T$ (used in the proof
  of Theorem 6.1, (6)–(8)).
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel Filter Topology Matrix

/-- **The ternary form $B(x, y) + 2S z^2$** for a binary form $B = a x^2 + b x y + c y^2$. -/
def sForm (S : ℕ) (B : BinQF) : QuadForm ℤ 3 :=
  QuadForm.ofUpper ![![B.a, B.b, 0], ![0, B.c, 0], ![0, 0, 2 * S]]

/-- **The S-genus** (§1): the classes of ternary forms $Q$ locally equivalent (over $\mathbb{Z}_p$ for
every prime $p$ and over $\mathbb{R}$, i.e. in the same genus) to some $B(x, y) + 2S z^2$, with $B$ a
positive definite integral binary form of discriminant $b^2 - 4ac = -8S$. -/
@[kb "berkovich2012" "§1, p. 1 (the S-genus)"]
def SGenus (S : ℕ) : Set (QClass 3) :=
  {c | ∃ B : BinQF, B.PosDef' ∧ B.disc = -8 * S ∧ c ∈ genusClasses (sForm S B)}

/-- **The sign $\varepsilon_p(Q)$** (Definition 3.2, via Remark 3.4): $1$ if $Q$ represents an
integer $n$ with $p \nmid n$ and $\left(\frac{-n}{p}\right) = 1$, and $-1$ otherwise. -/
@[kb "berkovich2012" "§3, Definition 3.2 and Remark 3.4, pp. 3–4"]
noncomputable def epsP (p : ℕ) [Fact p.Prime] (Q : QuadForm ℤ 3) : ℤ := by
  classical
  exact if ∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ Q.eval v ∧ legendreSym p (-Q.eval v) = 1 then 1 else -1

/-- $\varepsilon_p$ is a class invariant (equivalent forms represent the same integers). -/
theorem epsP_eq_of_intEquiv (p : ℕ) [Fact p.Prime] {Q Q' : QuadForm ℤ 3} (h : IntEquiv Q Q') :
    epsP p Q = epsP p Q' := by
  classical
  obtain ⟨g, hg⟩ := h
  have key : (∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ Q.eval v ∧ legendreSym p (-Q.eval v) = 1) ↔
      (∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ Q'.eval v ∧ legendreSym p (-Q'.eval v) = 1) := by
    constructor
    · rintro ⟨v, h1, h2⟩
      refine ⟨(g⁻¹).val *ᵥ v, ?_⟩
      rw [← hg, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
      exact ⟨h1, h2⟩
    · rintro ⟨v, h1, h2⟩
      exact ⟨g.val *ᵥ v, by rw [hg]; exact ⟨h1, h2⟩⟩
  unfold epsP
  simp only [key]

/-- $\varepsilon_p$ of a class. -/
noncomputable def QClass.epsP (p : ℕ) [Fact p.Prime] (c : QClass 3) : ℤ :=
  Quotient.lift (s := intSetoid 3) (fun Q => Berkovich2012.epsP p Q)
    (fun _ _ h => epsP_eq_of_intEquiv p h) c

/-- **$\epsilon_W(Q) = \prod_{p \mid W} \varepsilon_p(\mathrm{Gen}(Q))$** (Theorem 6.1). -/
@[kb "berkovich2012" "§6, Theorem 6.1, p. 7"]
noncomputable def QClass.epsW (W : ℕ) (c : QClass 3) : ℤ :=
  ∏ p ∈ W.primeFactors.attach,
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    QClass.epsP p c

/-- **Comparison of natural-order Euler products.** If $\beta_p(Q; m) = \beta_p(Q'; m)$ for all
primes $p \notin T$ ($T$ finite) and $\beta_p(Q'; m) \ne 0$ for $p \in T$, and $P$, $P'$ are the
natural-order Euler products of $Q$, $Q'$ at $m$, then
$P = P' \prod_{p \in T} \beta_p(Q; m) / \beta_p(Q'; m)$. -/
theorem eulerProductValue_ratio {n : ℕ} {Q Q' : QuadForm ℤ n} {m : ℤ} {P P' : ℝ}
    (hP : IsEulerProductValue Q m P) (hP' : IsEulerProductValue Q' m P')
    (T : Finset AWS.PrimeIdx) (hout : ∀ p ∉ T, eulerFactor Q m p = eulerFactor Q' m p)
    (hne : ∀ p ∈ T, eulerFactor Q' m p ≠ 0) :
    P = P' * ∏ p ∈ T, eulerFactor Q m p / eulerFactor Q' m p := by
  set c := ∏ p ∈ T, eulerFactor Q m p / eulerFactor Q' m p
  have hev : ∀ᶠ X in atTop, eulerPartialProd Q m X = c * eulerPartialProd Q' m X := by
    have := tendsto_primesUpTo.eventually (eventually_ge_atTop T)
    filter_upwards [this] with X hX
    unfold eulerPartialProd
    rw [← Finset.prod_sdiff hX, ← Finset.prod_sdiff (s₁ := T) hX]
    rw [Finset.prod_congr rfl fun p hp => hout p (Finset.mem_sdiff.1 hp).2]
    have : ∏ p ∈ T, eulerFactor Q m p = c * ∏ p ∈ T, eulerFactor Q' m p := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => by field_simp [hne p hp]
    rw [this]; ring
  have h2 : Tendsto (eulerPartialProd Q m) atTop (𝓝 (c * P')) :=
    (hP'.const_mul c).congr' (hev.mono fun X hX => hX.symm)
  have := tendsto_nhds_unique hP h2
  rw [this]; ring

end QuadFormsKB.Berkovich2012
