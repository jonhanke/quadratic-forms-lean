/-
# Hanke 2011 (enumerating maximal definite forms): the explicit bounds of §7 (Lemmas 7.3, 7.4, Theorem 7.8)

J. Hanke, *Enumerating maximal definite quadratic forms of bounded class number over $\mathbb Z$ in $n\ge3$ variables*,
arXiv:1110.1876v1 (`hanke2011enumerating`), §7, pp. 10–14.

**Setting.** $Q_0$ is a $\mathbb Z$-valued (i.e. $\mathcal O_{\mathbb Q}$-valued, `QuadForm (𝓞 ℚ) n`) form in $n\ge3$
variables, nondegenerate and positive definite, with $L = \mathbb Z^n$ maximal (`StdIsMaximal`), and $h(L)$ =
`Lattices.classNumber` (classes for the full orthogonal group). The local factors $\lambda_p$ are `lambdaOdd` /
`lambdaEven` of the Gan–Hanke–Yu mass-type of $(V_p, Q_p)$ (`oddTypeAt`, `evenTypeAt`, see `Comparison.lean`); $p$ runs over the
maximal ideals $v$ of $\mathcal O_{\mathbb Q}$, with $p = q_v$ = `normQ v`. The zeta values are
$|\zeta(1-2k)|$ = `absZetaNeg ℚ k` and $|L(1-\frac n2,\chi)|$ = `absLNeg Q₀ (n/2)` (through the functional equations).

**Proves.**
* the products $\prod_p\lambda_p$ are finite products (`hasFiniteMulSupport_lambdaOdd`, `hasFiniteMulSupport_lambdaEven`);
* **Lemma 7.4** (`lemma_7_4_prod_odd`, `lemma_7_4_prod_even`: (8); `lemma_7_4_odd`, `lemma_7_4_even`: (7)), from (2), (5)
  and Lemma 7.2, with the corrections listed below;
* **Lemma 7.3** (`lemma_7_3`): $|L(1-\frac n2,\chi)|/2^t \le B\,2^{\frac{n-2}2}\big/\prod_{k=1}^{\frac{n-2}2}|\zeta(1-2k)|\cdot
  (2\text{ if }n = 4,\ 1\text{ if }n\ge6)$, $t$ the number of primes of type III (the primes dividing $\mathrm{Cond}(\chi)$);
* $\zeta_{\mathbb Q} = \zeta$ for $s > 1$ (`dedekindZetaR_rat`) and $|\zeta(-1)| = 1/12$ (`absZetaNeg_rat_one`);
* **Theorem 7.8, corrected** (`theorem_7_8_corrected`): for $n = 3$ and $h(L) = 1$, every odd prime $p$ at which the Gan–Hanke–Yu
  mass-type is not generic satisfies $p\le47$.

*Erratum (Lemma 7.4):* the printed $B''$ lacks the factor $B$: from $\mathrm{Mass}^+\le h\le B$ one gets
$\prod_p\lambda_p\le B\cdot B''$ and $\lambda_p\le\epsilon\,B\,B''$ (for $B = 1$, the case of Thm 7.8, both readings agree).
*Erratum (Lemma 7.4, (7), $n$ even):* the other factors include the $t$ factors $\lambda_q = \frac12$ of type III, so the
argument gives $\lambda_p\le\epsilon\,2^{t}B\,B''$ (equivalently, $|L(1-\frac n2,\chi)|$ replaced by
$|L(1-\frac n2,\chi)|/2^t$ in $B''$, as in (3) and (6)); (7) as printed holds when $t = 0$.
*Erratum (Theorem 7.8, proof):* $\lambda_2\in\{1,\frac12,\frac32\}$ (types I and II$^-$ at $p = 2$ give $\frac12$, Lemma 7.2),
so the divisibility argument gives $\frac{p\pm1}2\mid24$, i.e. $p\le47$; the printed $p\le23$ is not reached by it
(it is consistent with the tables of §8, i.e. with the enumeration of Thm 7.5). `theorem_7_8_corrected` is the corrected
conclusion, phrased with "the mass-type at $p$ is not generic" (for odd $p$ and a maximal lattice this is $p\mid\det_H(Q)$;
that comparison is not formalized here).
-/
import QuadFormsKB.Literature.Hanke2011Enumerating.Comparison
import QuadFormsKB.Literature.Hanke2011Enumerating.MassBounds
import QuadFormsKB.LocalDensity.NFLocal

open NumberField IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2011Enumerating

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005

/-! ### Finite products with factors $\ge c$ on a finite set and $\ge 1$ elsewhere -/

section Products

variable {ι : Type*}

theorem pow_card_le_prod {f : ι → ℝ} {c : ℝ} (hc0 : 0 ≤ c) {S E : Finset ι} (hES : E ⊆ S)
    (hE : ∀ i ∈ E, c ≤ f i) (hnE : ∀ i ∈ S, i ∉ E → 1 ≤ f i) : c ^ E.card ≤ ∏ i ∈ S, f i := by
  classical
  rw [← Finset.prod_sdiff hES]
  have h1 : (1 : ℝ) ≤ ∏ i ∈ S \ E, f i := by
    have := Finset.prod_le_prod₀ (s := S \ E) (f := fun _ => (1 : ℝ)) (g := f) (fun _ _ => zero_le_one)
      (fun i hi => hnE i (Finset.mem_sdiff.1 hi).1 (Finset.mem_sdiff.1 hi).2)
    simpa using this
  have h2 : c ^ E.card ≤ ∏ i ∈ E, f i := by
    have := Finset.prod_le_prod₀ (s := E) (f := fun _ => c) (g := f) (fun _ _ => hc0) hE
    simpa using this
  have h3 : 0 ≤ c ^ E.card := pow_nonneg hc0 _
  nlinarith

/-- If $f$ has finite multiplicative support, $f\ge c$ on the finite set $E$ ($0\le c$) and $f\ge1$ off $E$, then
$c^{|E|}\le\prod_i f(i)$. -/
theorem pow_card_le_tprod {f : ι → ℝ} (hf : f.HasFiniteMulSupport) {c : ℝ} (hc0 : 0 ≤ c) (E : Finset ι)
    (hE : ∀ i ∈ E, c ≤ f i) (hnE : ∀ i, i ∉ E → 1 ≤ f i) : c ^ E.card ≤ ∏' i, f i := by
  classical
  set S := hf.toFinset ∪ E
  have hoff : ∀ i ∉ S, f i = 1 := fun i hi => by
    by_contra h
    exact hi (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
  rw [tprod_eq_prod (L := SummationFilter.unconditional _) hoff]
  exact pow_card_le_prod hc0 Finset.subset_union_right hE fun i _ hi => hnE i hi

/-- One factor against the product: $f(p)\,c^{|E\setminus\{p\}|}\le\prod_if(i)$ under the hypotheses of
`pow_card_le_tprod` and $f\ge0$. -/
theorem mul_pow_card_le_tprod [DecidableEq ι] {f : ι → ℝ} (hf : f.HasFiniteMulSupport) {c : ℝ} (hc0 : 0 ≤ c) (E : Finset ι)
    (hE : ∀ i ∈ E, c ≤ f i) (hnE : ∀ i, i ∉ E → 1 ≤ f i) (hpos : ∀ i, 0 ≤ f i) (p : ι) :
    f p * c ^ (E.erase p).card ≤ ∏' i, f i := by
  classical
  set S := insert p (hf.toFinset ∪ E)
  have hoff : ∀ i ∉ S, f i = 1 := fun i hi => by
    by_contra h
    exact hi (Finset.mem_insert_of_mem (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h)))
  rw [tprod_eq_prod (L := SummationFilter.unconditional _) hoff, ← Finset.mul_prod_erase S f (Finset.mem_insert_self _ _)]
  have hsub : E.erase p ⊆ S.erase p := Finset.erase_subset_erase _ (fun i hi =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ hi))
  have h := pow_card_le_prod hc0 hsub (fun i hi => hE i (Finset.mem_of_mem_erase hi)) (fun i hi hiE => by
    by_cases hE' : i ∈ E
    · exact absurd (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hi, hE'⟩) hiE
    · exact hnE i hE')
  exact mul_le_mul_of_nonneg_left h (hpos p)

end Products

/-! ### The local factors have finite multiplicative support -/

section Support

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $\lambda_{\mathrm{odd},v} = 1$ for all but finitely many $v$ ($n\ge3$ odd, $\mathcal O_F^n$ maximal). -/
theorem hasFiniteMulSupport_lambdaOdd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaOdd (normQ v) n (oddTypeAt v Q₀) := by
  have h1 := (hasFiniteMulSupport_norm_two (F := F)).pow (n / 2)
  have h2 := (hasFiniteMulSupport_dualIndexAt Q₀ hQ).pow (n / 2)
  have h3 := hasFiniteMulSupport_lambdaGen Q₀ hQ
  have hA := (h1.mul h2).mul h3
  have e : (fun v : HeightOneSpectrum (𝓞 F) => lambdaOdd (normQ v) n (oddTypeAt v Q₀)) =
      fun v => ‖(2 : v.adicCompletion F)‖ ^ (n / 2) * dualIndexAt v Q₀ ^ (n / 2) * lambdaGen v Q₀ := by
    funext v
    rw [← lambdaGHYAt_eq_lambdaOdd hodd v Q₀, lambdaGHYAt_eq v hn hodd Q₀ hQ hmax]
  rw [e]
  exact hA

/-- $\lambda_{\mathrm{even},v} = 1$ for all but finitely many $v$ ($n\ge4$ even, $\mathcal O_F^n$ maximal): off the finite set
where the dual index is $\ne1$. -/
theorem hasFiniteMulSupport_lambdaEven (hn : 4 ≤ n) (heven : Even n) (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (hmax : StdIsMaximal Q₀) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => lambdaEven (normQ v) n (evenTypeAt v Q₀) := by
  have hS := hasFiniteMulSupport_dualIndexAt Q₀ hQ
  refine Set.Finite.subset hS fun v hv => ?_
  simp only [Function.mem_mulSupport] at hv ⊢
  intro hd
  apply hv
  rw [← lambdaGHYEvenAt_eq_lambdaEven heven v Q₀]
  have h := lambdaGHYEvenAt_mul ramifiedDualIndexConductor_proved v hn heven Q₀ hQ hmax
  have hc : condFactor v Q₀ = 1 := by
    unfold condFactor
    rw [if_neg (not_isRamifiedAt_of_dualIndexAt_eq_one v Q₀ heven hd)]
  rw [hc, hd, lambdaAt_eq_one_of Q₀ v hd] at h
  simpa using h

end Support

/-! ### $\zeta_{\mathbb Q} = \zeta$ and $|\zeta(-1)| = 1/12$ -/

/-- $N v$ is the prime $p$ under $v$ for $v$ a maximal ideal of $\mathcal O_{\mathbb Q}$. -/
theorem normQ_rat (v : HeightOneSpectrum (𝓞 ℚ)) : normQ v = (Rat.HeightOneSpectrum.natGenerator v : ℝ) := by
  unfold normQ
  exact_mod_cast LocalDensity.NF.absNorm_rat v

/-- At most one maximal ideal of $\mathcal O_{\mathbb Q}$ has a given norm. -/
theorem eq_of_normQ_eq {v w : HeightOneSpectrum (𝓞 ℚ)} (h : normQ v = normQ w) : v = w := by
  rw [normQ_rat, normQ_rat] at h
  have h' : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w := by exact_mod_cast h
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h')

/-- **$\zeta_{\mathbb Q}(s) = \zeta(s)$** for real $s > 1$ (the two Euler products, matched by
`Rat.HeightOneSpectrum.primesEquiv`). -/
theorem dedekindZetaR_rat {s : ℝ} (hs : 1 < s) : NFEuler.dedekindZetaR ℚ s = NFEuler.zetaR s := by
  have h1 := NFEuler.hasProd_dedekindZeta (F := ℚ) hs
  have h2 := NFEuler.hasProd_zetaR hs
  have h3 := (Equiv.hasProd_iff (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))).2 h2
  refine h1.unique ?_
  convert h3 using 2 with v
  simp only [Function.comp_apply]
  congr 3
  exact_mod_cast LocalDensity.NF.absNorm_rat v

/-- **$|\zeta(-1)| = 1/12$**: `absZetaNeg ℚ 1` $= \frac{2\cdot1!}{(2\pi)^2}\zeta(2) = \frac1{12}$. -/
theorem absZetaNeg_rat_one : absZetaNeg ℚ 1 = 1 / 12 := by
  unfold absZetaNeg
  rw [dedekindZetaR_rat (by norm_num), show (2 * ((1 : ℕ) : ℝ)) = 2 by norm_num, NFEuler.zetaR_two,
    Module.finrank_self, pow_one, Rat.numberField_discr, Int.cast_one, abs_one, Real.one_rpow]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  norm_num
  field_simp
  ring

theorem absZetaNeg_pos {F : Type} [Field F] [NumberField F] (r : ℕ) (hr : 1 ≤ r) : 0 < absZetaNeg F r := by
  unfold absZetaNeg
  have hD : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero F)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h2r : (1 : ℝ) < 2 * (r : ℝ) := by linarith
  have hz : 0 < NFEuler.dedekindZetaR F (2 * (r : ℝ)) :=
    lt_of_lt_of_le one_pos (NFEuler.one_le_dedekindZetaR h2r)
  have hπ : 0 < Real.pi := Real.pi_pos
  positivity

/-- The product $\prod_{k=1}^m|\zeta(1-2k)|$ (`absZetaNeg ℚ k`). -/
def zetaProd (m : ℕ) : ℝ := ∏ k ∈ Finset.range m, absZetaNeg ℚ (k + 1)

theorem zetaProd_pos (m : ℕ) : 0 < zetaProd m :=
  Finset.prod_pos fun k _ => absZetaNeg_pos (k + 1) (by omega)

/-! ### Lemma 7.4 -/

section Lemma74

variable {n : ℕ}

/-- **$B''$ for odd $n$** (Hanke 2011, Lemma 7.4, p. 12): $2^{\frac{n-3}2}\big/\prod_{k=1}^{\frac{n-1}2}|\zeta(1-2k)|$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, p. 12 (B'' for n odd)"]
def bOdd (n : ℕ) : ℝ := (2 : ℝ) ^ (((n : ℝ) - 3) / 2) / zetaProd ((n - 1) / 2)

/-- **$B''$ for even $n$** (Hanke 2011, Lemma 7.4, p. 12):
$2^{\frac{n-2}2}\big/\big(|L(1-\frac n2,\chi)|\prod_{k=1}^{\frac{n-2}2}|\zeta(1-2k)|\big)$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, p. 12 (B'' for n even)"]
def bEven (Q₀ : QuadForm (𝓞 ℚ) n) : ℝ :=
  (2 : ℝ) ^ (((n : ℝ) - 2) / 2) / (absLNeg Q₀ (n / 2) * zetaProd ((n - 2) / 2))

/-- **$\epsilon$** (Hanke 2011, Lemma 7.4, p. 12): $2$ for $3\le n\le4$, $1$ for $n\ge5$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, p. 12 (ε)"]
def epsilon (n : ℕ) : ℝ := if n ≤ 4 then 2 else 1

/-- From $\mathrm{Mass}^+ = \mathrm{ofReal}(X)$ and $\mathrm{Mass}^+\le h\le B$: $X\le B$. -/
theorem le_of_massPlus {X : ℝ} {h : ℕ} {B : ℝ} (hM : ENNReal.ofReal X ≤ (h : ℝ≥0∞)) (hB : (h : ℝ) ≤ B) : X ≤ B := by
  rw [← ENNReal.ofReal_natCast] at hM
  exact ((ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hM).trans hB

theorem rpow_neg_half (a : ℝ) : (2 : ℝ) ^ ((3 - a) / 2) = ((2 : ℝ) ^ ((a - 3) / 2))⁻¹ := by
  rw [← Real.rpow_neg (by norm_num)]; ring_nf

/-- **Lemma 7.4, (8), $n$ odd** (Hanke 2011, p. 13), with $B''$ multiplied by $B$ (*Erratum*, see the module docstring):
if $h(L)\le B$ then $\prod_p\lambda_{\mathrm{odd},p}\le B\cdot B''$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, (8), p. 13 (n odd)"]
theorem lemma_7_4_prod_odd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B) :
    ∏' v : HeightOneSpectrum (𝓞 ℚ), lambdaOdd (normQ v) n (oddTypeAt v Q₀) ≤ B * bOdd n := by
  have hM := massPlus_le_classNumber (by omega) Q₀ hQ hpd
  rw [mass_formula_odd hn hodd Q₀ hQ hpd hmax] at hM
  have hX := le_of_massPlus hM hB
  rw [rpow_neg_half] at hX
  have h2 : 0 < (2 : ℝ) ^ (((n : ℝ) - 3) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hZ := zetaProd_pos ((n - 1) / 2)
  unfold bOdd
  unfold zetaProd at hZ ⊢
  rw [mul_div_assoc', le_div_iff₀ hZ]
  have := mul_le_mul_of_nonneg_left hX h2.le
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul] at this
  linarith

/-- **Lemma 7.4, (7), $n$ odd** (Hanke 2011, pp. 12–13), with $B''$ multiplied by $B$ (*Erratum*): if $h(L)\le B$ then
$\lambda_{\mathrm{odd},p}\le\epsilon\,B\,B''$ for every $p$. *Proof* (the paper's: (2) and Lemma 7.2): all other factors are
$\ge1$, except (for $n = 3$) the one at $p = 2$, which is $\ge\frac12$. -/
@[kb "hanke2011enumerating" "Lemma 7.4, (7), pp. 12–13 (n odd)"]
theorem lemma_7_4_odd (hn : 3 ≤ n) (hodd : Odd n) (Q₀ : QuadForm (𝓞 ℚ) n) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀) {B : ℝ}
    (hB : (Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ n) : ℝ) ≤ B)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    lambdaOdd (normQ p) n (oddTypeAt p Q₀) ≤ epsilon n * B * bOdd n := by
  classical
  set f := fun v : HeightOneSpectrum (𝓞 ℚ) => lambdaOdd (normQ v) n (oddTypeAt v Q₀) with hfdef
  have hf := hasFiniteMulSupport_lambdaOdd hn hodd Q₀ hQ hmax
  have hP := lemma_7_4_prod_odd hn hodd Q₀ hQ hpd hmax hB
  have h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), 2 ≤ NFEuler.normP v := fun v => NFEuler.two_le_normP v
  set E := hf.toFinset.filter fun v => f v < 1
  have hE : ∀ v ∈ E, 1 / 2 ≤ f v := fun v _ => half_le_lambdaOdd (h2 v) hn hodd _
  have hnE : ∀ v, v ∉ E → 1 ≤ f v := fun v hv => by
    by_contra hlt
    push_neg at hlt
    apply hv
    refine Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ?_, hlt⟩
    exact ne_of_lt hlt
  have hpos : ∀ v, 0 ≤ f v := fun v =>
    le_trans (by norm_num) (half_le_lambdaOdd (NFEuler.two_le_normP v) hn hodd (oddTypeAt v Q₀))
  have hmain := mul_pow_card_le_tprod hf (by norm_num : (0 : ℝ) ≤ 1 / 2) E hE hnE hpos p
  -- the exceptional set has at most one element (the place over 2), and is empty for n ≥ 5
  have hEsub : ∀ v ∈ E, n = 3 ∧ normQ v = 2 := fun v hv => by
    obtain ⟨h3, h2', -⟩ := lemma_7_2_odd (h2 v) hn hodd _ (Finset.mem_filter.1 hv).2
    exact ⟨h3, by unfold normQ; exact_mod_cast h2'⟩
  have hcard : (E.erase p).card ≤ (if n ≤ 4 then 1 else 0) := by
    split_ifs with h4
    · refine Finset.card_le_one.2 fun a ha b hb => ?_
      exact eq_of_normQ_eq (((hEsub a (Finset.mem_of_mem_erase ha)).2).trans
        ((hEsub b (Finset.mem_of_mem_erase hb)).2).symm)
    · refine le_of_eq (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a ha => ?_))
      have := (hEsub a (Finset.mem_of_mem_erase ha)).1
      omega
  have hpow : (if n ≤ 4 then (1 / 2 : ℝ) else 1) ≤ (1 / 2 : ℝ) ^ (E.erase p).card := by
    split_ifs with h4
    · have : (E.erase p).card ≤ 1 := by simpa [h4] using hcard
      calc (1 / 2 : ℝ) = (1 / 2) ^ 1 := (pow_one _).symm
        _ ≤ (1 / 2) ^ (E.erase p).card := pow_le_pow_of_le_one (by norm_num) (by norm_num) this
    · have : (E.erase p).card = 0 := by simpa [h4] using hcard
      rw [this, pow_zero]
  have hfp := hpos p
  have hm := mul_le_mul_of_nonneg_left hpow hfp
  unfold epsilon
  split_ifs with h4
  · rw [if_pos h4] at hm
    linarith
  · rw [if_neg h4] at hm
    linarith

end Lemma74

/-! ### Theorem 7.8, corrected -/

/-- **Theorem 7.8, corrected** (Hanke 2011, p. 13; *Erratum*, see the module docstring): for a $\mathbb Z$-valued
positive definite form $Q_0$ in $3$ variables with $\mathbb Z^3$ maximal and class number $h(L) = 1$, every odd prime $p$
(a maximal ideal $v$ with $q_v = p$ odd) at which the Gan–Hanke–Yu mass-type is not generic satisfies $p\le47$. *Proof*: Lemma
7.4 with $B = 1$ gives $\lambda_p\le2\cdot12 = 24$ ($|\zeta(-1)| = 1/12$), and $\lambda_p\ge\frac{p-1}2$ for the
non-generic types I, II$^\pm$ at odd $p$; so $p\le49$, and $49$ is not prime. -/
@[kb "hanke2011enumerating" "Theorem 7.8, p. 13 (corrected bound p ≤ 47)"]
theorem theorem_7_8_corrected (Q₀ : QuadForm (𝓞 ℚ) 3) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ))) (hmax : StdIsMaximal Q₀)
    (h1 : Lattices.classNumber (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (stdLat ℚ 3) = 1)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : normQ v ≠ 2) (hgen : oddTypeAt v Q₀ ≠ .gen) :
    normQ v ≤ 47 := by
  have h := lemma_7_4_odd (by norm_num) (by decide) Q₀ hQ hpd hmax (B := 1) (by rw [h1]; norm_num) v
  have hb : bOdd 3 = 12 := by
    unfold bOdd zetaProd
    norm_num [absZetaNeg_rat_one]
  rw [hb] at h
  simp only [epsilon, show (3 : ℕ) ≤ 4 by norm_num, if_true] at h
  set p := Rat.HeightOneSpectrum.natGenerator v
  have hpv : normQ v = (p : ℝ) := normQ_rat v
  have hp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hp2 : p ≠ 2 := fun h2 => hv (by rw [hpv, h2]; norm_num)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  -- λ_p ≥ (p-1)/2 for the non-generic types
  have hlow : ((p : ℝ) - 1) / 2 ≤ lambdaOdd (normQ v) 3 (oddTypeAt v Q₀) := by
    rw [hpv]
    cases hT : oddTypeAt v Q₀ with
    | gen => exact absurd hT hgen
    | I =>
      simp only [lambdaOdd]
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      norm_num
      nlinarith
    | IIplus => simp only [lambdaOdd]; norm_num; linarith
    | IIminus => simp only [lambdaOdd]; norm_num
  have hle : (p : ℝ) ≤ 49 := by linarith
  have hle' : p ≤ 49 := by exact_mod_cast hle
  have hne : p ≠ 49 := fun h49 => by rw [h49] at hp; norm_num at hp
  rw [hpv]
  have : p ≤ 47 := by
    rcases Nat.lt_or_ge p 48 with h | h
    · omega
    · interval_cases p <;> simp_all <;> norm_num at hp
  exact_mod_cast this

end QuadFormsKB.Hanke2011Enumerating
