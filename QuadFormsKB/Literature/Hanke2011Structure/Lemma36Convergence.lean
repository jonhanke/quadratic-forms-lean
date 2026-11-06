/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.GeneraFiniteHensel
import QuadFormsKB.Literature.Hanke2011Structure.TheoremOneOne
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist
import QuadFormsKB.Analysis.NFEulerProduct

/-!
# Hanke 2011, Lemma 3.6: convergence of $M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$ for $n \ne 2$

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §3, Lemma 3.6, p. 13: "$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$
converges for all $S$ when $n \ne 2$."

In the library $M^*$ is `totalMassM n S ε 𝕊 c` $= \sum_{t \in \mathrm{Gen}^*_f(S,\varepsilon,\mathbb S,\vec c)}
\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$, a `finsum` of `invDensityTuple t` (the Euler product when it converges, $0$
otherwise). "Converges" is formalized as **both** of the following, for every number field $F$:

* **(a) finiteness of the index set** (`genStarF_finite`, every $n \in \mathbb N$): $\mathrm{Gen}^*_f(S,\varepsilon,\mathbb S,\vec c;n)$
  is a finite set. *Proof* (the paper's): let $T = \{\mathfrak p \mid 2\} \cup \mathrm{Supp}(S)$ (finite). Outside $T$ there is exactly
  one admissible local genus (Thm. 2.6 for $\mathfrak p \nmid 2$, `admLoc_good`), and at each $\mathfrak p \in T$ there are finitely
  many (`genera_finite`, Hensel's lemma, every prime). So restriction to $T$ is an injection of $\mathrm{Gen}^*_f$ into a finite
  product of finite sets.
* **(b) convergence of each Euler product** (`multipliable_invDensity`, `tprod_invDensity_ne_zero`, $n \ge 1$, $n \ne 2$): for
  every $t \in \mathrm{Gen}^*_f$, the family $(\beta(t_{\mathfrak p})^{-1})_{\mathfrak p}$ is `Multipliable` (unconditionally
  convergent) with nonzero product. *Proof*: for $\mathfrak p \notin T$ the density is the generic one (Lemma 3.6, proof;
  `lemma_3_6_density_odd`/`lemma_3_6_density_even`), namely $\prod_{i=1}^{r}(1 - q^{-2i})$ for $n = 2r+1$ and
  $(1 - \chi_{\mathfrak p}q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})$ for $n = 2r$, $\chi_{\mathfrak p} = \pm1$, $q = N\mathfrak p$.
  Each factor is $1 + O(N\mathfrak p^{-2})$ when $n \ne 2$ ($r \ge 2$), hence multipliable with nonzero product by the summability of
  $\sum_{\mathfrak p} N\mathfrak p^{-2}$ (`NFEuler.multipliable_of_abs_sub_one_le`); the finitely many factors at $T$ are positive
  (`LocGenus.beta_pos_rank`). (For $n = 2$ the factor $1 - \chi q^{-1}$ is only conditionally convergent, which is why the paper
  excludes $n = 2$.)

**Headline.** `lemma_3_6_converges`: for $n \ge 1$, $n \ne 2$, $\mathrm{Gen}^*_f$ is finite and for each of its elements the Euler
product converges to a nonzero number, so that $M^*$ is a finite sum of nonzero Euler products
(`totalMassM_eq_sum`). The result is **unconditional** (no named inputs).

Indices are 0-based.
-/

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField QuadFormsKB.NFEuler

noncomputable section

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Part A: finiteness of $\mathrm{Gen}^*_f$ -/

/-- **The bad primes for $S$**: the primes $\mathfrak p \mid 2$ together with the support $\{\mathfrak p \mid \mathrm{ord}_{\mathfrak p}(S)
\ne 0\}$ of $S$. -/
def badPrimes (S : AdelicSqCl F) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | (2 : 𝓞 F) ∈ v.asIdeal} ∪ supp S

/-- The set of bad primes is finite. -/
theorem badPrimes_finite (S : AdelicSqCl F) : (badPrimes S).Finite :=
  finite_dyadic_two.union (supp_finite S)

/-- Outside the bad primes, $\mathfrak p \nmid 2$ and $S_{\mathfrak p}$ is a unit squareclass. -/
theorem good_of_not_mem_badPrimes {S : AdelicSqCl F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPrimes S) :
    (2 : 𝓞 F) ∉ v.asIdeal ∧ AdelicSqCl.comp v S ∈ localUnitSqCl F v := by
  simp only [badPrimes, Set.mem_union, Set.mem_ofPred_eq, not_or] at hv
  refine ⟨hv.1, mem_localUnitSqCl_of_ordZ v ?_⟩
  have h : ¬ adelicOrd v S ≠ 0 := hv.2
  exact (show adelicOrd v S = 0 from not_not.mp h)

section Gen

variable {S : AdelicSqCl F} {ε : ℤ} {𝕊 : Set (HeightOneSpectrum (𝓞 F))} {c : HeightOneSpectrum (𝓞 F) → ℤ}

/-- **Uniqueness outside the bad primes** (Thm. 2.6 for $\mathfrak p \nmid 2$): two tuples of $\mathrm{Gen}^*_f$ agree at every prime
outside `badPrimes S` ($n \ge 1$). -/
theorem tuple_eq_of_not_bad (hn : 1 ≤ n) {t t' : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c)
    (ht' : t' ∈ GenStarF S ε 𝕊 c) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPrimes S) : t v = t' v := by
  obtain ⟨h2, hs⟩ := good_of_not_mem_badPrimes hv
  obtain ⟨Q, -, hQ, -⟩ := admLoc_good hn v h2 hs
  have h1 : t v ∈ admLoc n v (AdelicSqCl.comp v S) := ht.1 v
  have h1' : t' v ∈ admLoc n v (AdelicSqCl.comp v S) := ht'.1 v
  rw [hQ] at h1 h1'
  exact (Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h1').symm

/-- In rank $0$ there is a single local genus at each prime. -/
instance locGenus_zero_subsingleton (v : HeightOneSpectrum (𝓞 F)) : Subsingleton (LocGenus v 0) :=
  ⟨fun a b => Quotient.inductionOn₂ a b fun _ _ => congrArg (Quotient.mk _) (QuadForm.ext (Subsingleton.elim _ _))⟩

/-- **Lemma 3.6 (convergence of $M^*$), part (a): $\mathrm{Gen}^*_f(S,\varepsilon,\mathbb S,\vec c;n)$ is finite**, for every number
field $F$, every $n \in \mathbb N$, every $S$, $\varepsilon$, $\mathbb S$, $\vec c$. -/
@[kb "hanke2011structure" "Lemma 3.6, p. 13 (Gen*_f finite, part of convergence of M*)"]
theorem genStarF_finite (S : AdelicSqCl F) (ε : ℤ) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) : (GenStarF (n := n) S ε 𝕊 c).Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (LocTuple F 0) := inferInstanceAs (Subsingleton (∀ v, LocGenus v 0))
    have : Finite (LocTuple F 0) := Finite.of_subsingleton
    exact Set.toFinite _
  · have : Finite (badPrimes S) := (badPrimes_finite S).to_subtype
    let r : LocTuple F n → ∀ v : badPrimes S, LocGenus v.1 n := fun t v => t v.1
    have himg : r '' GenStarF S ε 𝕊 c ⊆ Set.pi Set.univ
        (fun v : badPrimes S => {G : LocGenus v.1 n | G.Nondeg ∧ G.det = AdelicSqCl.comp v.1 S}) := by
      rintro _ ⟨t, ht, rfl⟩ v _
      exact ⟨(ht.1 v.1).1, (ht.1 v.1).2.2⟩
    have hfin : (r '' GenStarF S ε 𝕊 c).Finite :=
      (Set.Finite.pi (fun v : badPrimes S => genera_finite v.1 n _)).subset himg
    refine Set.Finite.of_finite_image hfin ?_
    intro t ht t' ht' htt
    funext v
    by_cases hv : v ∈ badPrimes S
    · exact congrFun htt ⟨v, hv⟩
    · exact tuple_eq_of_not_bad hn ht ht' hv

end Gen

/-! ### Part B: the generic density at a good prime -/

section Density

variable (v : HeightOneSpectrum (𝓞 F))

/-- $|2|_{\mathfrak p} = 1$ for $\mathfrak p \nmid 2$. -/
theorem norm_two_eq_one_of_not_mem (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ‖(2 : v.adicCompletion F)‖ = 1 := by
  have := (FinitePlace.norm_eq_one_iff_notMem F v (2 : 𝓞 F)).mpr h2
  simpa [map_ofNat] using this

/-- **Lemma 3.6, density of a unimodular genus, $n = 2r+1$** (any number field, $\mathfrak p \nmid 2$):
$\beta(Q) = \prod_{i=1}^r(1 - N\mathfrak p^{-2i})$ for $Q$ with unit Hessian determinant. -/
theorem beta_good_odd_nf (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (r : ℕ)
    (Q : QuadForm (v.adicCompletionIntegers F) (2 * r + 1)) (hQ : IsUnit Q.hessian.det) :
    (LocGenus.mk Q).beta = gOdd r (normP v : ℝ) := by
  have hne : Q.hessian.det ≠ 0 := hQ.ne_zero
  have hπ := LocalDensity.NF.irreducible_π v
  have h2' := not_dvd_two_of_not_mem v h2
  have hd := lemma_3_6_density_odd hπ h2' r Q (LocalDensity.DVR.dvr_not_dvd_of_isUnit hπ hQ)
  rw [LocGenus.beta_mk]
  unfold betaForm
  rw [Hanke2005.hankeBeta_std_hessian v Q hne, norm_two_eq_one_of_not_mem v h2, one_pow, one_mul]
  unfold LocalDensity.DVR.siegelDensity
  simp only [ite_true]
  have hq : (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) = (normP v : ℝ) := by
    rw [LocalDensity.NF.q_completion]
  rw [gOdd, ← hq, ← hd]
  ring

/-- **Lemma 3.6, density of a unimodular genus, $n = 2r$** ($r \ge 1$, $\mathfrak p \nmid 2$):
$\beta(Q) = (1 - \chi\,N\mathfrak p^{-r})\prod_{i=1}^{r-1}(1 - N\mathfrak p^{-2i})$ with $\chi = \pm 1$. -/
theorem beta_good_even_nf (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (r : ℕ) (hr : 1 ≤ r)
    (Q : QuadForm (v.adicCompletionIntegers F) (2 * r)) (hQ : IsUnit Q.hessian.det) :
    ∃ x : ℝ, |x| ≤ 1 ∧
      (LocGenus.mk Q).beta = (1 - x * ((normP v : ℝ) ^ r)⁻¹) * gOdd (r - 1) (normP v : ℝ) := by
  have hne : Q.hessian.det ≠ 0 := hQ.ne_zero
  have hπ := LocalDensity.NF.irreducible_π v
  have h2' := not_dvd_two_of_not_mem v h2
  have hdet := LocalDensity.DVR.dvr_not_dvd_of_isUnit hπ hQ
  have hd := lemma_3_6_density_even hπ h2' r hr Q hdet
  refine ⟨(LocalDensity.DVR.chiDisc Q : ℝ), ?_, ?_⟩
  · rcases Hanke2005.chiDisc_pm hπ h2' Q hdet with h | h <;> simp [h]
  · rw [LocGenus.beta_mk]
    unfold betaForm
    rw [Hanke2005.hankeBeta_std_hessian v Q hne, norm_two_eq_one_of_not_mem v h2, one_pow, one_mul]
    unfold LocalDensity.DVR.siegelDensity
    simp only [ite_true]
    have hq : (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) = (normP v : ℝ) := by
      rw [LocalDensity.NF.q_completion]
    rw [gOdd, ← hq]
    rw [← mul_one_div, show (1 : ℝ) / 2 = 2⁻¹ by norm_num] at *
    linarith [hd]

end Density

section Tuple

variable {S : AdelicSqCl F} {ε : ℤ} {𝕊 : Set (HeightOneSpectrum (𝓞 F))} {c : HeightOneSpectrum (𝓞 F) → ℤ}

/-- **The density of every genus of $\mathrm{Gen}^*_f$ outside the bad primes, $n = 2r+1$.** -/
theorem tuple_beta_odd (r : ℕ) {t : LocTuple F (2 * r + 1)} (ht : t ∈ GenStarF S ε 𝕊 c)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ badPrimes S) : (t v).beta = gOdd r (normP v : ℝ) := by
  obtain ⟨h2, hs⟩ := good_of_not_mem_badPrimes hv
  obtain ⟨Q, hQu, hQ, -⟩ := admLoc_good (n := 2 * r + 1) (by omega) v h2 hs
  have h1 : t v ∈ admLoc (2 * r + 1) v (AdelicSqCl.comp v S) := ht.1 v
  rw [hQ] at h1
  rw [Set.mem_singleton_iff.mp h1]
  exact beta_good_odd_nf v h2 r Q hQu

/-- **The density of every genus of $\mathrm{Gen}^*_f$ outside the bad primes, $n = 2r$**, with a sign $\chi_{\mathfrak p}$,
$|\chi_{\mathfrak p}| \le 1$ (it is $\pm1$ at the good primes, and $0$ is used at the bad ones). -/
theorem exists_chi_even (r : ℕ) (hr : 1 ≤ r) {t : LocTuple F (2 * r)} (ht : t ∈ GenStarF S ε 𝕊 c) :
    ∃ χ : HeightOneSpectrum (𝓞 F) → ℝ, (∀ v, |χ v| ≤ 1) ∧ ∀ v, v ∉ badPrimes S →
      (t v).beta = (1 - χ v * ((normP v : ℝ) ^ r)⁻¹) * gOdd (r - 1) (normP v : ℝ) := by
  classical
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ x : ℝ, |x| ≤ 1 ∧ (v ∉ badPrimes S →
      (t v).beta = (1 - x * ((normP v : ℝ) ^ r)⁻¹) * gOdd (r - 1) (normP v : ℝ)) := by
    intro v
    by_cases hv : v ∈ badPrimes S
    · exact ⟨0, by simp, fun h => absurd hv h⟩
    · obtain ⟨h2, hs⟩ := good_of_not_mem_badPrimes hv
      obtain ⟨Q, hQu, hQ, -⟩ := admLoc_good (n := 2 * r) (by omega) v h2 hs
      have h1 : t v ∈ admLoc (2 * r) v (AdelicSqCl.comp v S) := ht.1 v
      rw [hQ] at h1
      obtain ⟨x, hx, hb⟩ := beta_good_even_nf v h2 r hr Q hQu
      exact ⟨x, hx, fun _ => by rw [Set.mem_singleton_iff.mp h1]; exact hb⟩
  choose χ hχ hb using hex
  exact ⟨χ, hχ, hb⟩

end Tuple

/-! ### Part C: Euler products -/

section Euler

variable {X : Type*}

theorem two_le_normP_real (v : HeightOneSpectrum (𝓞 F)) : (2 : ℝ) ≤ (normP v : ℝ) := by
  exact_mod_cast two_le_normP v

/-- **One Euler factor $1 - c(\mathfrak p)N\mathfrak p^{-e}$, $|c| \le 1$, $e \ge 2$**: multipliable, with nonzero product, and each
factor positive. -/
theorem family_factor (c : HeightOneSpectrum (𝓞 F) → ℝ) (hc : ∀ v, |c v| ≤ 1) {e : ℕ} (he : 2 ≤ e) :
    (∀ v, 0 < 1 - c v * ((normP v : ℝ) ^ e)⁻¹) ∧
      Multipliable (fun v => 1 - c v * ((normP v : ℝ) ^ e)⁻¹) ∧
        ∏' v, (1 - c v * ((normP v : ℝ) ^ e)⁻¹) ≠ 0 := by
  have hq2 : ∀ v : HeightOneSpectrum (𝓞 F), (2 : ℝ) ≤ (normP v : ℝ) := two_le_normP_real
  have hx : ∀ v : HeightOneSpectrum (𝓞 F), ((normP v : ℝ) ^ e)⁻¹ ≤ ((normP v : ℝ) ^ 2)⁻¹ := fun v =>
    inv_anti₀ (by have := hq2 v; positivity) (pow_le_pow_right₀ (by linarith [hq2 v]) he)
  have hx4 : ∀ v : HeightOneSpectrum (𝓞 F), ((normP v : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := fun v => by
    have h4 : (4 : ℝ) ≤ (normP v : ℝ) ^ 2 := by nlinarith [hq2 v]
    calc ((normP v : ℝ) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
      _ = 1 / 4 := by norm_num
  have hxnn : ∀ v : HeightOneSpectrum (𝓞 F), 0 ≤ ((normP v : ℝ) ^ e)⁻¹ := fun v => by
    have := hq2 v; positivity
  have hpos : ∀ v, 0 < 1 - c v * ((normP v : ℝ) ^ e)⁻¹ := fun v => by
    have h1 : c v * ((normP v : ℝ) ^ e)⁻¹ ≤ |c v * ((normP v : ℝ) ^ e)⁻¹| := le_abs_self _
    have h2 : |c v * ((normP v : ℝ) ^ e)⁻¹| ≤ ((normP v : ℝ) ^ e)⁻¹ := by
      rw [abs_mul, abs_of_nonneg (hxnn v)]
      exact mul_le_of_le_one_left (hxnn v) (hc v)
    linarith [hx v, hx4 v]
  have hb : ∀ v : HeightOneSpectrum (𝓞 F),
      |(1 - c v * ((normP v : ℝ) ^ e)⁻¹) - 1| ≤ 1 * (normP v : ℝ) ^ (-(2 : ℝ)) := fun v => by
    rw [show (1 - c v * ((normP v : ℝ) ^ e)⁻¹) - 1 = -(c v * ((normP v : ℝ) ^ e)⁻¹) by ring, abs_neg, abs_mul,
      abs_of_nonneg (hxnn v), Real.rpow_neg (by have := hq2 v; positivity), Real.rpow_two, one_mul]
    exact (mul_le_of_le_one_left (hxnn v) (hc v)).trans (hx v)
  have hev : ∀ᶠ v in Filter.cofinite, |(1 - c v * ((normP v : ℝ) ^ e)⁻¹) - 1| ≤
      1 * (normP v : ℝ) ^ (-(2 : ℝ)) := Filter.Eventually.of_forall hb
  exact ⟨hpos, multipliable_of_abs_sub_one_le _ (C := 1) (σ := 2) (by norm_num) hev,
    tprod_ne_zero_of_abs_sub_one_le _ (C := 1) (σ := 2) (by norm_num) hev fun v => (hpos v).ne'⟩

/-- A finite product of multipliable families with nonzero products is multipliable with nonzero product. -/
theorem multipliable_prod_ne_zero {ι : Type*} (s : Finset ℕ) (f : ℕ → ι → ℝ)
    (h : ∀ i ∈ s, Multipliable (f i) ∧ ∏' x, f i x ≠ 0) :
    Multipliable (fun x => ∏ i ∈ s, f i x) ∧ ∏' x, ∏ i ∈ s, f i x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨multipliable_one, by simp⟩
  | insert a s ha ih =>
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hh := h a (Finset.mem_insert_self a s)
    simp only [Finset.prod_insert ha]
    exact ⟨hh.1.mul ih'.1, by rw [hh.1.tprod_mul ih'.1]; exact mul_ne_zero hh.2 ih'.2⟩

/-- **The generic density for $n = 2r+1$ is multipliable over the primes of $F$**, with nonzero product. -/
theorem gOdd_family (r : ℕ) :
    Multipliable (fun v : HeightOneSpectrum (𝓞 F) => gOdd r (normP v : ℝ)) ∧
      ∏' v : HeightOneSpectrum (𝓞 F), gOdd r (normP v : ℝ) ≠ 0 := by
  have h := multipliable_prod_ne_zero (Finset.range r)
    (fun i (v : HeightOneSpectrum (𝓞 F)) => 1 - (fun _ => (1 : ℝ)) v * ((normP v : ℝ) ^ (2 * (i + 1)))⁻¹)
    fun i _ => let h := family_factor (fun _ => (1 : ℝ)) (fun _ => by simp) (e := 2 * (i + 1)) (by omega)
      ⟨h.2.1, h.2.2⟩
  simpa [gOdd] using h

end Euler

/-- If $f \ne 0$ everywhere agrees cofinitely with a multipliable $g \ne 0$ with nonzero product, then $f$ is multipliable with
nonzero product. -/
theorem multipliable_ne_zero_of_eventually {ι : Type*} (f g : ι → ℝ) (hf : ∀ v, f v ≠ 0) (hg : ∀ v, g v ≠ 0)
    (hgm : Multipliable g) (hg0 : ∏' v, g v ≠ 0) (hev : ∀ᶠ v in Filter.cofinite, f v = g v) :
    Multipliable f ∧ ∏' v, f v ≠ 0 := by
  classical
  set h : ι → ℝ := fun v => f v / g v with hh
  have hfin : (Function.mulSupport h).Finite := by
    have : {v | ¬ f v = g v}.Finite := Filter.eventually_cofinite.mp hev
    refine this.subset fun v hv => ?_
    intro hfg
    apply hv
    simp [hh, hfg, hg v]
  have hhm : Multipliable h := multipliable_of_hasFiniteMulSupport hfin
  have hh0 : ∏' v, h v ≠ 0 := by
    rw [tprod_eq_prod (s := hfin.toFinset) (fun b hb => by
      simpa using hb)]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => div_ne_zero (hf v) (hg v)
  have e : f = fun v => g v * h v := funext fun v => by
    simp only [hh]; field_simp [hg v]
  rw [e]
  exact ⟨hgm.mul hhm, by rw [hgm.tprod_mul hhm]; exact mul_ne_zero hg0 hh0⟩

section Main

variable {S : AdelicSqCl F} {ε : ℤ} {𝕊 : Set (HeightOneSpectrum (𝓞 F))} {c : HeightOneSpectrum (𝓞 F) → ℤ}

theorem eventually_not_bad (S : AdelicSqCl F) : ∀ᶠ v in Filter.cofinite, v ∉ badPrimes (F := F) S :=
  Filter.eventually_cofinite.mpr (by simpa using badPrimes_finite S)

/-- **The densities of a tuple of $\mathrm{Gen}^*_f$ are multipliable with nonzero product** ($n \ge 1$, $n \ne 2$). -/
theorem multipliable_beta (hn : 1 ≤ n) (hn2 : n ≠ 2) {t : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c) :
    Multipliable (fun v => (t v).beta) ∧ ∏' v, (t v).beta ≠ 0 := by
  have hf : ∀ v, (t v).beta ≠ 0 := fun v => (LocGenus.beta_pos_rank v (t v) (ht.1 v).1).ne'
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hk : 2 ≤ k := by omega
    obtain ⟨χ, hχ, hb⟩ := exists_chi_even k (by omega) ht
    obtain ⟨hpos, hm, h0⟩ := family_factor χ hχ hk
    obtain ⟨gm, g0⟩ := gOdd_family (F := F) (k - 1)
    have hgpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < gOdd (k - 1) (normP v : ℝ) := fun v =>
      gOdd_pos _ (by have := two_le_normP_real v; linarith)
    refine multipliable_ne_zero_of_eventually _
      (fun v => (1 - χ v * ((normP v : ℝ) ^ k)⁻¹) * gOdd (k - 1) (normP v : ℝ)) hf
      (fun v => (mul_pos (hpos v) (hgpos v)).ne') (hm.mul gm) ?_ ?_
    · rw [hm.tprod_mul gm]; exact mul_ne_zero h0 g0
    · filter_upwards [eventually_not_bad S] with v hv using hb v hv
  · refine multipliable_ne_zero_of_eventually _ (fun v => gOdd k (normP v : ℝ)) hf
      (fun v => (gOdd_pos _ (by have := two_le_normP_real v; linarith)).ne')
      (gOdd_family k).1 (gOdd_family k).2 ?_
    filter_upwards [eventually_not_bad S] with v hv using tuple_beta_odd k ht hv

/-- **Lemma 3.6 (convergence of $M^*$), part (b): each Euler product $\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$ converges**
(is `Multipliable`, i.e. unconditionally convergent) for $t \in \mathrm{Gen}^*_f(S,\varepsilon,\mathbb S,\vec c;n)$, $n \ge 1$, $n \ne 2$,
every number field. -/
@[kb "hanke2011structure" "Lemma 3.6, p. 13 (Euler product of M* converges, n ≠ 2)"]
theorem multipliable_invDensity (hn : 1 ≤ n) (hn2 : n ≠ 2) {t : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c) :
    Multipliable fun v => ((t v).beta)⁻¹ :=
  (multipliable_beta hn hn2 ht).1.inv₀ (multipliable_beta hn hn2 ht).2

/-- **The Euler product of Lemma 3.6 is nonzero** (same hypotheses as `multipliable_invDensity`). -/
theorem tprod_invDensity_ne_zero (hn : 1 ≤ n) (hn2 : n ≠ 2) {t : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c) :
    ∏' v, ((t v).beta)⁻¹ ≠ 0 := by
  have h := multipliable_beta hn hn2 ht
  rw [h.1.tprod_inv₀ h.2]
  exact inv_ne_zero h.2

/-- On $\mathrm{Gen}^*_f$ ($n \ge 1$, $n \ne 2$) `invDensityTuple` is the (nonzero) Euler product itself, not the junk value
$0$. -/
theorem invDensityTuple_eq_tprod (hn : 1 ≤ n) (hn2 : n ≠ 2) {t : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c) :
    invDensityTuple t = ∏' v, ((t v).beta)⁻¹ := by
  classical
  unfold invDensityTuple
  exact if_pos (multipliable_invDensity hn hn2 ht)

/-- **$M^*$ is a finite sum of nonzero Euler products** ($n \ge 1$, $n \ne 2$). -/
theorem totalMassM_eq_sum (hn : 1 ≤ n) (hn2 : n ≠ 2) (S : AdelicSqCl F) (ε : ℤ)
    (𝕊 : Set (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℤ) :
    totalMassM n S ε 𝕊 c = ∑ t ∈ (genStarF_finite (n := n) S ε 𝕊 c).toFinset, ∏' v, ((t v).beta)⁻¹ := by
  unfold totalMassM
  rw [finsum_mem_eq_finite_toFinset_sum _ (genStarF_finite (n := n) S ε 𝕊 c)]
  refine Finset.sum_congr rfl fun t ht => ?_
  exact invDensityTuple_eq_tprod hn hn2 ((genStarF_finite (n := n) S ε 𝕊 c).mem_toFinset.mp ht)

/-- **Lemma 3.6** (Hanke 2011, p. 13): *$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S)$ converges for all $S$ when $n \ne 2$.*
Formalized as: for every number field $F$, $n \ge 1$, $n \ne 2$, $S$, $\varepsilon$, $\mathbb S$, $\vec c$, the index set
$\mathrm{Gen}^*_f(S,\varepsilon,\mathbb S,\vec c;n)$ is finite, and for every $t$ in it the Euler product
$\prod_{\mathfrak p}\beta(t_{\mathfrak p})^{-1}$ converges (`Multipliable`) to a nonzero number, which is the value of
`invDensityTuple t`. Unconditional. -/
@[kb "hanke2011structure" "Lemma 3.6, p. 13 (convergence of M*, n ≠ 2)"]
theorem lemma_3_6_converges (hn : 1 ≤ n) (hn2 : n ≠ 2) (S : AdelicSqCl F) (ε : ℤ)
    (𝕊 : Set (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℤ) :
    (GenStarF (n := n) S ε 𝕊 c).Finite ∧
      ∀ t ∈ GenStarF (n := n) S ε 𝕊 c, Multipliable (fun v => ((t v).beta)⁻¹) ∧
        ∏' v, ((t v).beta)⁻¹ ≠ 0 ∧ invDensityTuple t = ∏' v, ((t v).beta)⁻¹ :=
  ⟨genStarF_finite S ε 𝕊 c, fun _ ht => ⟨multipliable_invDensity hn hn2 ht, tprod_invDensity_ne_zero hn hn2 ht,
    invDensityTuple_eq_tprod hn hn2 ht⟩⟩

end Main

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.genStarF_finite
#print axioms QuadFormsKB.Hanke2011Structure.multipliable_invDensity
#print axioms QuadFormsKB.Hanke2011Structure.tprod_invDensity_ne_zero
#print axioms QuadFormsKB.Hanke2011Structure.totalMassM_eq_sum
#print axioms QuadFormsKB.Hanke2011Structure.lemma_3_6_converges
