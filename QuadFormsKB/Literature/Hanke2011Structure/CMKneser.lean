/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Structure.CMUnitIndex

/-!
# Paper 6, Lemma 8.4 (generalized Dedekind correspondence), from Kneser's exact sequence

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Lemma 8.4 and its proof, p. 35.

**Lemma 8.4.** For a CM extension $K/F$ ($F = K^+$ the maximal real subfield),
$$|G(\mathcal O_K)| = \frac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\frac{2^{[F:\mathbb Q]}}{Q_{K/F}},\qquad
  Q_{K/F} = [\mathcal O_K^\times : \mathcal O_F^\times(\mathcal O_K^\times\cap\mu_\infty)],$$
where $G(\mathcal O_K)$ is Kneser's group of primitive binary $\mathcal O_F$-lattices that are rank-one $\mathcal O_K$-modules
with the norm-compatibility condition (Lemma 8.3).

*The paper's proof*: Kneser [17, p. 412] gives the exact sequence
$$\mathcal O_K^\times \xrightarrow{N} \mathcal O_F^\times \to G(\mathcal O_K) \to \mathrm{Pic}(\mathcal O_K)
  \xrightarrow{N} \mathrm{Pic}(\mathcal O_F) \to 1$$
(surjectivity at the end: Washington, Thm. 10.1), so $|G(\mathcal O_K)| = \frac{h_K}{h_F}[\mathcal O_F^\times :
N\mathcal O_K^\times]$, and $[\mathcal O_F^\times : N\mathcal O_K^\times]\,Q_{K/F} = 2^{[F:\mathbb Q]}$ (proved unconditionally in
`CMUnitIndex.lean`, `CMUnits.lemma_8_4_unit_index`).

Kneser's group $G(\mathcal O_K)$ is not defined in the library. The exact sequence is therefore the **named input**
`KneserSequence K G`: a group $G$ with homomorphisms $\delta : \mathcal O_F^\times \to G$, $\rho : G \to
\mathrm{Cl}(\mathcal O_K)$ and $\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$ with $\ker\delta = N\mathcal O_K^\times$,
$\operatorname{im}\delta = \ker\rho$, $\operatorname{im}\rho = \ker\nu$ and $\nu$ surjective (Kneser's sequence for
$G = G(\mathcal O_K)$, with Washington's surjectivity). From it, `lemma_8_4` proves the formula
$|G|\cdot h_F\cdot Q_{K/F} = h_K\cdot 2^{[F:\mathbb Q]}$, i.e. Lemma 8.4 (`lemma_8_4_div`). Here $\mathcal O_F^\times$ is
`realUnits K` (the units of $K$ coming from $K^+$), $N$ = `CMUnits.unitsNorm` ($u \mapsto u\bar u$), $Q_{K/F}$ =
`indexRealUnits K`, $h$ = `classNumber`.
-/

open NumberField NumberField.Units NumberField.IsCMField Module

namespace QuadFormsKB.Hanke2011Structure.CMUnits

noncomputable section

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- **Kneser's exact sequence for $G(\mathcal O_K)$** (Kneser 1982, §6, p. 412, top; with the surjectivity of the norm on
class groups, Washington, *Introduction to cyclotomic fields*, Thm. 10.1, p. 184), as used in the proof of Hanke 2011,
Lemma 8.4, p. 35. For a CM field $K$ with $F = K^+$ and a group $G$: there are homomorphisms
$\delta : \mathcal O_F^\times \to G$ (`delta`), $\rho : G \to \mathrm{Cl}(\mathcal O_K)$ (`rho`) and
$\nu : \mathrm{Cl}(\mathcal O_K) \to \mathrm{Cl}(\mathcal O_F)$ (`nu`, the norm) such that
$$\mathcal O_K^\times \xrightarrow{N} \mathcal O_F^\times \xrightarrow{\delta} G \xrightarrow{\rho} \mathrm{Cl}(\mathcal O_K)
  \xrightarrow{\nu} \mathrm{Cl}(\mathcal O_F) \to 1$$
is exact: `ker_delta` ($\ker\delta = N_{K/F}\mathcal O_K^\times$), `range_delta` ($\operatorname{im}\delta = \ker\rho$),
`range_rho` ($\operatorname{im}\rho = \ker\nu$), `nu_surj`. The input for $G = G(\mathcal O_K)$ (Lemma 8.3) is
Kneser's theorem; $G(\mathcal O_K)$ itself is not defined in the library. -/
@[kb "hanke2011structure" "Lemma 8.4, proof, p. 35 (Kneser's exact sequence [17, p. 412]; Washington Thm. 10.1)"]
structure KneserSequence (G : Type*) [Group G] : Prop where
  exists_seq : ∃ (delta : realUnits K →* G) (rho : G →* ClassGroup (𝓞 K))
    (nu : ClassGroup (𝓞 K) →* ClassGroup (𝓞 (maximalRealSubfield K))),
    delta.ker = (unitsNorm K).range.subgroupOf (realUnits K) ∧ delta.range = rho.ker ∧ rho.range = nu.ker ∧
      Function.Surjective nu

/-- $|H| = |\ker f|\cdot|\operatorname{im} f|$ for a group homomorphism $f$ (Nat.card form, no finiteness needed). -/
theorem card_eq_card_ker_mul_card_range {H H' : Type*} [Group H] [Group H'] (f : H →* H') :
    Nat.card H = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

/-- **Lemma 8.4** (Hanke 2011, p. 35), from Kneser's exact sequence: for a CM field $K$, $F = K^+$, and a group $G$
fitting into Kneser's exact sequence (`KneserSequence K G`; for $G = G(\mathcal O_K)$ this is Kneser's theorem),
$$|G|\cdot h(\mathcal O_F)\cdot Q_{K/F} = h(\mathcal O_K)\cdot 2^{[F:\mathbb Q]},$$
with $Q_{K/F}$ = `indexRealUnits K` and $h$ = `classNumber`. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4 {G : Type*} [Group G] (H : KneserSequence K G) :
    Nat.card G * classNumber (maximalRealSubfield K) * indexRealUnits K =
      classNumber K * 2 ^ finrank ℚ (maximalRealSubfield K) := by
  obtain ⟨delta, rho, nu, hker, hδ, hρ, hν⟩ := H.exists_seq
  -- $|G| = |\ker\rho|\cdot|\operatorname{im}\rho| = |\operatorname{im}\delta|\cdot|\ker\nu|$
  have h1 : Nat.card G = Nat.card delta.range * Nat.card nu.ker := by
    rw [card_eq_card_ker_mul_card_range rho, ← hδ, hρ]
  -- $|\operatorname{im}\delta| = [\mathcal O_F^\times : N\mathcal O_K^\times]$
  have h2 : Nat.card delta.range = (unitsNorm K).range.relIndex (realUnits K) := by
    rw [Subgroup.relIndex, ← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange delta).toEquiv,
      Subgroup.index]
  -- $h_K = |\ker\nu|\cdot h_F$
  have h3 : classNumber K = Nat.card nu.ker * classNumber (maximalRealSubfield K) := by
    rw [classNumber, classNumber, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      card_eq_card_ker_mul_card_range nu, MonoidHom.range_eq_top.2 hν, Subgroup.card_top]
  rw [h1, h2, h3, ← lemma_8_4_unit_index K]
  ring

/-- **Lemma 8.4** in the paper's form: $|G| = \dfrac{h(\mathcal O_K)}{h(\mathcal O_F)}\cdot\dfrac{2^{[F:\mathbb Q]}}{Q_{K/F}}$. -/
@[kb "hanke2011structure" "Lemma 8.4, p. 35"]
theorem lemma_8_4_div {G : Type*} [Group G] (H : KneserSequence K G) :
    (Nat.card G : ℚ) = (classNumber K : ℚ) / classNumber (maximalRealSubfield K) *
      (2 ^ finrank ℚ (maximalRealSubfield K) / indexRealUnits K) := by
  have hF : (classNumber (maximalRealSubfield K) : ℚ) ≠ 0 := by exact_mod_cast classNumber_ne_zero _
  have hQ : (indexRealUnits K : ℚ) ≠ 0 := by
    rcases indexRealUnits_eq_one_or_two K with h | h <;> rw [h] <;> norm_num
  have := lemma_8_4 K H
  field_simp
  exact_mod_cast this

end

end QuadFormsKB.Hanke2011Structure.CMUnits
