/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Literature.Hanke2011Ternary.GlobalNF
import QuadFormsKB.Literature.OMeara.Sec72Local

/-!
# Hanke 2011 (ternary masses), Theorem 7.1: the global sign of $D_{B^*,\lambda;3}$

J. Hanke, arXiv:1109.1054 (`hanke2011ternary`), §7, proof of Theorem 7.1, p. 26.

The signed form `theorem_7_1_B_signed` has the sign
$\sigma(\mathfrak a) = \prod_{\mathfrak p\nmid2}\left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}
\prod_{\mathfrak p\mid2}(-\varepsilon_{\mathfrak p})$. When $\lambda(\mathfrak a)$ is globally rational, i.e. the square class of
some $\alpha \in F^\times$ at every prime, the factors are local Hilbert symbols $(-1,\alpha)_{\mathfrak p}$ (up to the sign
$-1$ at each $\mathfrak p \mid 2$), and Hilbert reciprocity (`NFPlace.finprod_hilbert`) gives
$$\sigma(\mathfrak a) = (-1)^{\#\{\mathfrak p\mid 2\}}\prod_{w\ \mathrm{real}}(-1,\alpha)_w$$
(`prod_sgnAt_eq`; complex places contribute $1$). With $2$ split completely, $\#\{\mathfrak p \mid 2\} = [F:\mathbb Q]$.

* `theorem_7_1_B` (**Theorem 7.1, $B^*$ part, corrected**): coefficientwise,
  $D_{B^*,\lambda;3}(s) = (-1)^{[F:\mathbb Q]}\prod_{w\ \mathrm{real}}(-1,\alpha_{\mathfrak a})_w\cdot
  \dfrac{\zeta_F(2s+2)\zeta_F(s+2)}{N(2\mathcal O_F)^{s}\zeta_F(3s+6)}$.

*Erratum:* the paper's sign
$(-1)^{[F:\mathbb Q]+\sigma_{v,-}}$ is this when $\alpha_{\mathfrak a}$ has sign $(-1)^{\sigma_{v,-}}$ at every real place $v$;
in general it is $(-1)^{[F:\mathbb Q]}\prod_{w}(-1,\alpha_{\mathfrak a})_w$, which does not depend on the signature.
-/

namespace QuadFormsKB.Hanke2011Ternary.NF

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

noncomputable section

variable {F : Type} [Field F] [NumberField F]

theorem finite_dyadic : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite :=
  (finite_bad (1 : (Ideal (𝓞 F))⁰)).subset fun _ hv => Or.inl hv

/-- The number of primes of $F$ above $2$. -/
def numDyadic (F : Type) [Field F] [NumberField F] : ℕ := (finite_dyadic (F := F)).toFinset.card

open Classical in
/-- **The sign of Theorem 7.1 by Hilbert reciprocity** (proof of Thm. 7.1, p. 26): if
$(-1,\alpha)_{\mathfrak p} = \left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_{\mathfrak p}\mathfrak a}$ at $\mathfrak p\nmid 2$ and
$\varepsilon_{\mathfrak p} = (-1,\alpha)_{\mathfrak p}$ at $\mathfrak p \mid 2$ (i.e. $\lambda(\mathfrak a)$ is the square class of $\alpha$
at every prime), then $\prod_{\mathfrak p}\mathrm{sgn}_{\mathfrak p} = (-1)^{\#\{\mathfrak p\mid2\}}\prod_{w}(-1,\alpha)_w$, the last
product over the infinite places. -/
@[kb "hanke2011ternary" "§7, proof of Thm. 7.1, p. 26 (product formula for the sign)"]
theorem prod_sgnAt_eq (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hodd : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal →
      (NFPlace.finite v).hilbert (-1 : F) (α : F) = ((epsOdd v ^ ordI v a : ℤˣ) : ℤ))
    (hdy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal →
      ((ε a v : ℤˣ) : ℤ) = (NFPlace.finite v).hilbert (-1 : F) (α : F)) :
    ∏ᶠ v, ((sgnAt ε a v : ℤˣ) : ℤ) =
      (-1) ^ numDyadic F * ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) := by
  set h : HeightOneSpectrum (𝓞 F) → ℤ := fun v => (NFPlace.finite v).hilbert (-1 : F) (α : F)
  set d : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if (2 : 𝓞 F) ∈ v.asIdeal then -1 else 1
  have hsplit : ∀ v, ((sgnAt ε a v : ℤˣ) : ℤ) = d v * h v := by
    intro v
    simp only [sgnAt, d, h]
    split_ifs with hv
    · rw [Units.val_neg, hdy v hv]; ring
    · rw [hodd v hv, one_mul]
  have hrec := NFPlace.finprod_hilbert (-1 : F) (α : F) (by norm_num) α.ne_zero
  have hfh : Function.HasFiniteMulSupport h := by
    have : Function.mulSupport h ⊆ NFPlace.finite ⁻¹' Function.mulSupport
        (fun v : NFPlace F => v.hilbert (-1 : F) (α : F)) := fun v hv => hv
    exact (hrec.1.preimage (fun _ _ _ _ e => NFPlace.finite.inj e)).subset this
  have hfd : Function.HasFiniteMulSupport d := finite_dyadic.subset fun v hv => by
    by_contra hn
    exact hv (by simp only [d]; exact if_neg hn)
  have hd : ∏ᶠ v, d v = (-1) ^ numDyadic F := by
    rw [finprod_eq_prod_of_mulSupport_subset d (s := finite_dyadic.toFinset) fun v hv => by
      rw [Finset.mem_coe, Set.Finite.mem_toFinset]; by_contra hn; exact hv (by simp only [d]; exact if_neg hn)]
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℤ)) fun v hv => by
      rw [Set.Finite.mem_toFinset] at hv; exact if_pos hv]
    rw [Finset.prod_const]; rfl
  have hpm : ∀ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) *
      (NFPlace.infinite w).hilbert (-1 : F) (α : F) = 1 := fun w => by
    rcases NFPlace.hilbert_eq_one_or (NFPlace.infinite w) (-1 : F) (α : F) with e | e <;> rw [e] <;> norm_num
  have hh : ∏ᶠ v, h v = ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) := by
    have h1 := OMeara.finprod_nfPlace (fun v : NFPlace F => v.hilbert (-1 : F) (α : F)) hrec.1
    rw [hrec.2] at h1
    have h2 : (∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F)) *
        ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) = 1 := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun w _ => hpm w
    calc ∏ᶠ v, h v = (∏ᶠ v, h v) * ((∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F)) *
          ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F)) := by rw [h2, mul_one]
      _ = _ := by rw [← mul_assoc, ← h1, one_mul]
  rw [finprod_congr hsplit, finprod_mul_distrib hfd hfh, hd, hh]

/-- **Theorem 7.1, $B^*$ part, corrected** (Hanke 2011, p. 26): for a number field $F$ whose primes above $2$ have norm
$2$, a nonzero ideal $\mathfrak a$ with $\lambda(\mathfrak a)$ the square class of $\alpha \in F^\times$ at every prime (as in
`prod_sgnAt_eq`), coefficientwise
$$[\mathfrak a^{-s}]\,D_{B^*,\lambda;3} = (-1)^{\#\{\mathfrak p\mid2\}}\prod_{w}(-1,\alpha)_w\cdot
[\mathfrak a^{-s}]\,\frac{\zeta_F(2s+2)\,\zeta_F(s+2)}{N(2\mathcal O_F)^{s}\,\zeta_F(3s+6)}.$$
When $2$ splits completely, $\#\{\mathfrak p\mid2\} = [F:\mathbb Q]$ (`theorem_7_1_B_split`). *Erratum:* the printed sign is $(-1)^{[F:\mathbb Q]+\sigma_{v,-}}$ (module docstring). -/
@[kb "hanke2011ternary" "§7, Thm. 7.1, p. 26 (D_{B*,λ;3}; sign corrected)"]
theorem theorem_7_1_B (h2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → qv v = 2)
    (ε : (Ideal (𝓞 F))⁰ → HeightOneSpectrum (𝓞 F) → ℤˣ) (a : (Ideal (𝓞 F))⁰) (α : Fˣ)
    (hodd : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∉ v.asIdeal →
      (NFPlace.finite v).hilbert (-1 : F) (α : F) = ((epsOdd v ^ ordI v a : ℤˣ) : ℤ))
    (hdy : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal →
      ((ε a v : ℤˣ) : ℤ) = (NFPlace.finite v).hilbert (-1 : F) (α : F)) :
    coeffB ε a = (((-1) ^ numDyadic F * ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1 : F) (α : F) : ℤ) : ℚ) *
      eulerCoeff EB a := by
  rw [theorem_7_1_B_signed h2 ε a, ← prod_sgnAt_eq ε a α hodd hdy]
  congr 1
  have hf : Function.HasFiniteMulSupport fun v => ((sgnAt ε a v : ℤˣ) : ℤ) := (finite_bad a).subset fun v hv => by
    by_contra hb
    simp only [Set.mem_ofPred_eq, not_or, not_not] at hb
    exact hv (by simp [sgnAt, hb.1, hb.2])
  exact (map_finprod (Int.castRingHom ℚ) hf).symm

end

end QuadFormsKB.Hanke2011Ternary.NF

#print axioms QuadFormsKB.Hanke2011Ternary.NF.prod_sgnAt_eq
#print axioms QuadFormsKB.Hanke2011Ternary.NF.theorem_7_1_B
