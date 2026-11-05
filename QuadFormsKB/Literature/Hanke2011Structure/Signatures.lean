/-
# Hanke 2011, signature vectors and the sign $\varepsilon_\infty$ (Def. 3.1, Rem. 4.16, Def. 8.2, Rem. 8.7)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`).

* `SignatureVector F n` (Definition 3.1, p. 12): a vector $\vec\sigma_\infty = ((\sigma_{v,+},\sigma_{v,-}))_{v\mid\infty_{\mathbb R}}$
  of pairs of nonnegative integers with $\sigma_{v,+} + \sigma_{v,-} = n$, one for each real place $v$ of the number field $F$.
* `card_signatureVector` (Remark 4.16, p. 20): there are $(n+1)^r$ of them, $r$ the number of real places.
* `epsInf` (Lemma 3.7, p. 13; Theorem 6.2, p. 26): $\varepsilon_\infty := \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v)$, where for a
  real quadratic space of signature $(\sigma_+,\sigma_-)$ the Hasse invariant (Serre's convention
  $\prod_{i<j}(a_i,a_j)_\infty$, as in the paper's proof of Lemma 5.10) is $(-1)^{\sigma_-(\sigma_--1)/2}$
  (`hasseLocal_real_signature`; complex places contribute $1$). `epsInf_mem` ($\varepsilon_\infty = \pm1$): of the $(n+1)^r$
  signature vectors only the sign $\varepsilon_\infty$ enters $M^*$ (Remark 4.16).
* `epsInf_definite_two` (Lemma 7.8, p. 32): for $n = 2$ and a totally definite signature vector, $\varepsilon_\infty = (-1)^\alpha$
  with $\alpha$ the number of real places where $\vec\sigma_\infty$ is negative definite.
* `LocallySimilar` (Definition 8.2, p. 34): $\sigma_v$ equals $\sigma'_v$ or its swap at every real place.
* `sum_epsInf_eq_zero` (proof of Theorem 8.6, p. 36; Remark 8.7, p. 37): summing $\varepsilon_\infty$ over all choices of
  $(2,0)$ or $(0,2)$ at a nonempty set of real places gives $0$; this is why the $B^*$-terms cancel in the proof of
  Theorem 8.6 (and, by Lemma 8.3, whenever the signature is definite somewhere).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.HasseScaling

namespace QuadFormsKB.Hanke2011Structure

open NumberField Finset Classical

variable (F : Type*) [Field F] [NumberField F]

/-- The possible signatures $(\sigma_+,\sigma_-) \in \mathbb Z_{\ge0}^2$ of a real quadratic space of dimension $n$:
$\sigma_+ + \sigma_- = n$. -/
def SigPair (n : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = n}

instance (n : ℕ) : Fintype (SigPair n) :=
  Fintype.subtype (Finset.HasAntidiagonal.antidiagonal n) (fun _ => Finset.HasAntidiagonal.mem_antidiagonal)

theorem card_sigPair (n : ℕ) : Fintype.card (SigPair n) = n + 1 := by
  unfold SigPair
  rw [Fintype.subtype_card, Finset.Nat.card_antidiagonal]

/-- **A vector of signatures of rank $n$** (Hanke 2011, Def. 3.1, p. 12): for each real place $v$ of the number field $F$,
a pair $(\sigma_{v,+},\sigma_{v,-}) \in \mathbb Z_{\ge0}^2$ with $\sigma_{v,+} + \sigma_{v,-} = n$. -/
@[kb "hanke2011structure" "Def. 3.1, p. 12"]
def SignatureVector (n : ℕ) : Type _ := {w : InfinitePlace F // w.IsReal} → SigPair n

noncomputable instance (n : ℕ) : Fintype (SignatureVector F n) :=
  inferInstanceAs (Fintype ({w : InfinitePlace F // w.IsReal} → SigPair n))

/-- **Remark 4.16** (Hanke 2011, p. 20): there are $(n+1)^r$ signature vectors of rank $n$, $r$ the number of real places
of $F$ (`InfinitePlace.nrRealPlaces`). -/
@[kb "hanke2011structure" "Rem. 4.16, p. 20"]
theorem card_signatureVector (n : ℕ) :
    Fintype.card (SignatureVector F n) = (n + 1) ^ InfinitePlace.nrRealPlaces F := by
  classical
  calc Fintype.card (SignatureVector F n)
      = Fintype.card ({w : InfinitePlace F // w.IsReal} → SigPair n) := Fintype.card_congr (Equiv.refl _)
    _ = (n + 1) ^ InfinitePlace.nrRealPlaces F := by
      rw [Fintype.card_fun, card_sigPair]

variable {F}

/-- The Hasse invariant (Serre's convention) of a real quadratic space of signature $(\sigma_+,\sigma_-)$:
$(-1)^{\sigma_-(\sigma_--1)/2}$, the number of pairs $i<j$ of negative diagonal entries. -/
def hasseReal (σneg : ℕ) : ℤ := (-1) ^ (σneg * (σneg - 1) / 2)

/-- **$\varepsilon_\infty$** (Hanke 2011, Lemma 3.7, p. 13; Theorem 6.2, p. 26): $\varepsilon_\infty := \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v)$,
the product over the real places of the Hasse invariants $(-1)^{\sigma_{v,-}(\sigma_{v,-}-1)/2}$ (complex places
contribute $1$). -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (ε∞)"]
noncomputable def epsInf {n : ℕ} (σ : SignatureVector F n) : ℤ := ∏ v, hasseReal (σ v).1.2

/-- **$\varepsilon_\infty = \pm1$** (Remark 4.16: of the $(n+1)^r$ signature vectors only this sign enters $M^*$). -/
@[kb "hanke2011structure" "Rem. 4.16, p. 20 (ε∞ = ±1)"]
theorem epsInf_mem {n : ℕ} (σ : SignatureVector F n) : epsInf σ = 1 ∨ epsInf σ = -1 := by
  unfold epsInf hasseReal
  rw [Finset.prod_pow_eq_pow_sum]
  exact neg_one_pow_eq_or ℤ _

/-- **The real Hasse invariant of a definite binary form** (Serre's convention, `hasseLocal`): for $a, b \in \mathbb R$ both
positive ($\sigma_- = 0$) or both negative ($\sigma_- = 2$), $(a,b)_{\mathbb R} = (-1)^{\sigma_-(\sigma_--1)/2}$ (`hasseReal`). -/
theorem hasseLocal_real_definite_two {a b : ℝ} (hab : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) :
    hasseLocal ℝ ![a, b] = hasseReal (if a < 0 then 2 else 0) := by
  have h2 : hasseLocal ℝ ![a, b] = hilbertSymbol ℝ a b := by simp [hasseLocal, Fin.prod_univ_two]
  have hpm : hilbertSymbol ℝ a b = 1 ∨ hilbertSymbol ℝ a b = -1 := by
    unfold hilbertSymbol; split_ifs <;> simp
  rw [h2]
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hn : ¬ hilbertSymbol ℝ a b = -1 := fun h =>
      absurd ((hilbertSymbol_real a b ha.ne' hb.ne').mp h).1 (not_lt.mpr ha.le)
    simp [hasseReal, not_lt.mpr ha.le, hpm.resolve_right hn]
  · rw [(hilbertSymbol_real a b ha.ne hb.ne).mpr ⟨ha, hb⟩]
    simp [hasseReal, ha]

/-- **Lemma 7.8's sign** (Hanke 2011, p. 32): for $n = 2$ and a totally definite signature vector ($\sigma_v = (2,0)$ or
$(0,2)$ at every real place), $\varepsilon_\infty = (-1)^\alpha$, $\alpha$ the number of real places where $\sigma_v = (0,2)$. -/
@[kb "hanke2011structure" "Lemma 7.8, p. 32 (ε∞ = (-1)^α)"]
theorem epsInf_definite_two (σ : SignatureVector F 2) (hσ : ∀ v, (σ v).1.2 = 0 ∨ (σ v).1.2 = 2) :
    epsInf σ = (-1) ^ (univ.filter fun v => (σ v).1.2 = 2).card := by
  classical
  unfold epsInf
  rw [Finset.card_filter, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rcases hσ v with h | h <;> simp [hasseReal, h]

variable (F) in
/-- **Locally similar signature vectors** (Hanke 2011, Def. 8.2, p. 34): at every real place $v$,
$\sigma_v = \sigma'_v$ or $\sigma_v = (\sigma'_{v,-}, \sigma'_{v,+})$ (the local quadratic spaces are similar). -/
@[kb "hanke2011structure" "Def. 8.2, p. 34"]
def LocallySimilar {n : ℕ} (σ σ' : SignatureVector F n) : Prop :=
  ∀ v, (σ v).1 = (σ' v).1 ∨ (σ v).1 = ((σ' v).1.2, (σ' v).1.1)

/-- **The cancellation of the $B^*$-terms** (Hanke 2011, proof of Theorem 8.6, p. 36; Remark 8.7, p. 37). Summing
$\varepsilon_\infty$ over the $2^{|D|}$ choices of the definite signature $(2,0)$ or $(0,2)$ at each place of a nonempty finite
set $D$ (here: any nonempty finite type `D`, sign vectors `s : D → ℤˣ`, $\varepsilon_\infty = \prod_v s_v$ by
`epsInf_definite_two`) gives $0$. So in $\sum_{\vec\sigma'}\bigl[A^* + \varepsilon_\infty(\vec\sigma')B^*\bigr]$ over the signature vectors
locally similar to a definite one, the $B^*$-terms cancel. -/
@[kb "hanke2011structure" "Thm. 8.6, proof, p. 36; Rem. 8.7, p. 37 (cancellation)"]
theorem sum_epsInf_eq_zero (D : Type*) [Fintype D] [DecidableEq D] [Nonempty D] :
    ∑ s : D → ℤˣ, ∏ v, ((s v : ℤˣ) : ℤ) = 0 := by
  rw [← Fintype.prod_sum (fun _ (x : ℤˣ) => (x : ℤ))]
  have h : ∑ x : ℤˣ, (x : ℤ) = 0 := by
    rw [show (univ : Finset ℤˣ) = {1, -1} by decide]
    simp
  rw [h]
  exact Finset.prod_eq_zero (mem_univ (Classical.arbitrary D)) rfl

end QuadFormsKB.Hanke2011Structure
