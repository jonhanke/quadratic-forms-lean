/-
# Cassels, Appendix B, §3, p. 377: the weight of the genus of a sum of squares

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §3, p. 377, on the genus $\mathcal F_0$ of the
form $f_0 = x_1^2 + \dots + x_n^2$ (here `sumSq n`, in the variables $x_0, \dots, x_{n-1}$; Cassels' $x_1, \dots, x_n$ are
shifted by one).

**Proved.**
* `card_autPlus_sumSq`: for $n \ge 1$, $I_n$ has $2^{n-1}\,n!$ proper integral automorphs (an improper one is the sign
  change of $x_0$, so $O^{+}$ has index $2$ in $O$, `card_aut_sumSq`);
* `pweight_sumSq_of_le_five`: for $1 \le n \le 5$ the weight is $W(\mathcal F_0) = 1/(2^{n-1}\,n!)$ (the genus has one
  class, `genusClasses_sumSq`, and $W = 2\,\mathrm{mass}$, `pweight_eq_two_mul_mass`);
* `pgenusClasses_sumSq_of_le_five`: for $n \le 5$ the genus has one proper class;
* `pgenusClasses_sumSq_eq_singleton_of_magnus` and `pgenusClasses_sumSq_ne_singleton_of_magnus`: from
  `MagnusSumSquares`, Cassels' deduction that $\mathcal F_0$ is one proper class for $n \le 8$ and has further classes for
  $n > 8$. Finiteness of the set of proper classes of a genus is proved unconditionally in the library
  (`pgenusClasses_finite`, from `genusFinite`), so it is not a hypothesis.

**Named statements.**
* `MagnusSumSquares`: Magnus' evaluation of Siegel's formula (1937) for the weight of $\mathcal F_0$, namely
  $W(\mathcal F_0) = 1/(2^{n-1}\,n!)$ for $1 \le n \le 8$ and $W(\mathcal F_0) > 1/(2^{n-1}\,n!)$ for $n > 8$. It is
  **proved** in `AppB/Magnus.lean` (`magnusSumSquares_holds`) from the class lists of `AppB/SumSquaresGenus.lean` (one class
  for $n \le 8$, the class of $E_8 \perp I_{n-8}$ besides that of $f_0$ for $n > 8$);
* `MagnusAsymptotic`: (3.9), $\log W(\mathcal F_0) = (n^2/4)(\log n - 3/2 - \log 2\pi) + O(n \log n)$, with the implied
  constant made explicit as an existential. Needs the same formula plus Stirling-type estimates.

*Erratum (candidate; not stated in Lean).* Cassels prints the values $W = \frac{1}{2^8\,9!}\cdot\frac{3^2\cdot17}{137}$
($n = 9$) and $\frac{1}{2^9\,10!}\cdot\frac{3^2 5^2}{137}$ ($n = 10$). The denominator $137$ should be $135$: for $n = 9$
the genus contains the classes of $I_9$ and $E_8 \perp I_1$, with $o^{+} = 2^8\,9!$ and $|W(E_8)| = 696729600$, which
gives $W = (1 + 2/15)/(2^8\,9!) = \frac{3^2 \cdot 17}{135}\cdot\frac{1}{2^8\,9!}$; for $n = 10$,
$W = (1 + 2/3)/(2^9\,10!) = \frac{3^2 5^2}{135}\cdot\frac{1}{2^9\,10!}$. These values are deliberately not formalized here.
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Siegel.FourSquaresClassNumber

open Matrix

noncomputable section

namespace QuadFormsKB.Siegel

/-- Helper: for $n \ge 1$ the sign change $\mathrm{diag}(-1, 1, \dots, 1)$ of $x_0$ is an improper automorph of $I_n$. -/
theorem hasImproperAut_sumSq_succ (m : ℕ) : HasImproperAut (sumSq (m + 1)) := by
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ := Matrix.diagonal (Fin.cons (-1) fun _ => 1) with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  refine ⟨⟨D, D, hDD, hDD⟩, ?_, ?_⟩
  · rw [mem_aut_sumSq_iff]
    show Dᵀ * D = 1
    rw [hD, Matrix.diagonal_transpose]
    exact hDD
  · show D.det = -1
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp

/-- **$f_0 = x_0^2 + \dots + x_{n-1}^2$ has $2^{n-1}\,n!$ proper integral automorphs** (Cassels, App. B, §3, p. 377),
for $n \ge 1$: $\lvert O^{+}(I_n)\rvert = 2^{n-1}\,n!$. Here `n` is the number of variables and `AutPlus (sumSq n)` is
the group of proper automorphs in $\mathrm{GL}_n(\mathbb Z)$. -/
@[kb "cassels1978" "App. B, §3, p. 377 (f₀ has 2^{n−1} n! proper automorphs)"]
theorem card_autPlus_sumSq {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (AutPlus (sumSq n)) = 2 ^ (n - 1) * n.factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := card_aut_eq_mul (sumSq (m + 1))
  simp only [card_aut_sumSq, hasImproperAut_sumSq_succ m, ite_true] at h
  have h2 : 2 ^ (m + 1) * (m + 1).factorial = 2 * (2 ^ m * (m + 1).factorial) := by ring
  rw [h2] at h
  simp only [Nat.add_sub_cancel]
  omega

/-- **The weight of the genus of $x_0^2 + \dots + x_{n-1}^2$ for $1 \le n \le 5$:**
$W(\mathcal F_0) = 1/(2^{n-1}\,n!)$ (Cassels, App. B, §3, p. 377, the cases of $n \le 5$ of Magnus' result; the genus
has one class). -/
@[kb "cassels1978" "App. B, §3, p. 377 (W(𝓕₀) = 1/(2^{n−1} n!), here n ≤ 5)"]
theorem pweight_sumSq_of_le_five {n : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) :
    pweight (sumSq n) = 1 / (2 ^ (n - 1) * (n.factorial : ℝ)) := by
  rw [pweight_eq_two_mul_mass hn posDef_sumSq, mass, genusClasses_sumSq hn5, finsum_mem_singleton,
    QClass.autCard_classOf, card_aut_sumSq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : (0 : ℝ) < (m + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  push_cast [Nat.add_sub_cancel]
  field_simp
  ring

/-- **One proper class for $n \le 5$:** the genus of $I_n$ is the single proper class of $I_n$, for $1 \le n \le 5$
(unconditional; for $n = 3, 4$ see also `pgenusClasses_sumSq_three`, `pgenusClasses_sumSq_four`). -/
theorem pgenusClasses_sumSq_of_le_five {n : ℕ} (hn : 1 ≤ n) (hn5 : n ≤ 5) :
    pgenusClasses (sumSq n) = {pclassOf (sumSq n)} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ext D
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', hf', hg⟩
    rw [← hf']
    have h1 := sameGenus_sumSq_intEquiv hn5 hg
    have h2 := (intEquiv_iff_properIntEquiv_of_hasImproperAut (hasImproperAut_sumSq_succ m) f').mp h1
    exact (pclassOf_eq_pclassOf_iff.mpr h2).symm
  · rintro rfl
    exact ⟨sumSq (m + 1), rfl, SameGenus.refl _⟩

/-- **Magnus' evaluation of the weight of the genus of $x_1^2 + \dots + x_n^2$** (Cassels, App. B, §3, p. 377; Magnus
1937, from Siegel's formula). Fields: `le_eight` — for $1 \le n \le 8$, $W(\mathcal F_0) = 1/(2^{n-1}\,n!)$; `gt_eight` —
for $n > 8$, $W(\mathcal F_0) > 1/(2^{n-1}\,n!)$. Here $W$ is `pweight (sumSq n)`. Assumed, not proved: it needs
Siegel's mass formula for $n \ge 6$ (the case $n \le 5$ is `pweight_sumSq_of_le_five`). The particular values at
$n = 9, 10$ printed by Cassels are not stated (see the module docstring for the erratum). -/
@[kb "cassels1978" "App. B, §3, p. 377 (Magnus: the weight of the genus of x₁²+⋯+xₙ²)"]
structure MagnusSumSquares : Prop where
  /-- For $1 \le n \le 8$ the weight is exactly $1/(2^{n-1}\,n!)$. -/
  le_eight : ∀ n : ℕ, 1 ≤ n → n ≤ 8 → pweight (sumSq n) = 1 / (2 ^ (n - 1) * (n.factorial : ℝ))
  /-- For $n > 8$ the weight exceeds $1/(2^{n-1}\,n!)$. -/
  gt_eight : ∀ n : ℕ, 8 < n → 1 / (2 ^ (n - 1) * (n.factorial : ℝ)) < pweight (sumSq n)

/-- **The asymptotic (3.9) for the weight of the genus of $x_1^2 + \dots + x_n^2$** (Cassels, App. B, §3, (3.9),
p. 377): $\log W(\mathcal F_0) = \tfrac{n^2}{4}\bigl(\log n - \tfrac32 - \log 2\pi\bigr) + O(n \log n)$ as
$n \to \infty$, with the $O$-constant made explicit. Field `bound`: there is a real $C$ such that for all $n \ge 2$,
$\bigl|\log W - \tfrac{n^2}{4}(\log n - \tfrac32 - \log 2\pi)\bigr| \le C\, n \log n$, where $W$ is
`pweight (sumSq n)`. Assumed, not proved. -/
@[kb "cassels1978" "App. B, §3, (3.9), p. 377"]
structure MagnusAsymptotic : Prop where
  /-- The explicit form of the $O(n\log n)$ error term. -/
  bound : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    |Real.log (pweight (sumSq n)) -
        ((n : ℝ) ^ 2 / 4) * (Real.log n - 3 / 2 - Real.log (2 * Real.pi))| ≤ C * n * Real.log n

/-- Helper: for $n \ge 1$, the weight of the genus of $I_n$ is the sum over the finite set of proper classes, and the
proper class of $I_n$ contributes $1/o^{+}(I_n)$. -/
theorem pweight_sumSq_eq_sum {n : ℕ} (hn : 1 ≤ n) :
    pweight (sumSq n) = ∑ C ∈ (pgenusClasses_finite hn posDef_sumSq.nondegenerate).toFinset,
      ((Nat.card (AutPlus C.out) : ℝ))⁻¹ := by
  rw [pweight, finsum_mem_eq_finite_toFinset_sum]

/-- **Cassels' deduction, $n \le 8$** (App. B, §3, p. 377): assuming Magnus' evaluation `MagnusSumSquares`, the genus of
$f_0$ consists only of the proper class of $f_0$ for $1 \le n \le 8$. The finiteness of the set of proper classes of the
genus is proved (`pgenusClasses_finite`), not assumed; the argument is that $f_0$ alone already contributes
$1/o^{+}(f_0) = 1/(2^{n-1}\,n!)$ (`card_autPlus_sumSq`) to $W$, and every further class would add a positive amount. -/
@[kb "cassels1978" "App. B, §3, p. 377 (𝓕₀ has one class for n ≤ 8, more for n > 8)"]
theorem pgenusClasses_sumSq_eq_singleton_of_magnus (hM : MagnusSumSquares) {n : ℕ} (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    pgenusClasses (sumSq n) = {pclassOf (sumSq n)} := by
  classical
  have hfin := pgenusClasses_finite hn posDef_sumSq.nondegenerate
  have hmem : pclassOf (sumSq n) ∈ pgenusClasses (sumSq n) := ⟨sumSq n, rfl, SameGenus.refl _⟩
  by_contra hne
  obtain ⟨C, hC, hCne⟩ : ∃ C ∈ pgenusClasses (sumSq n), C ≠ pclassOf (sumSq n) := by
    by_contra h
    push Not at h
    exact hne (Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, h⟩)
  have hterm : ((Nat.card (AutPlus (pclassOf (sumSq n)).out) : ℝ))⁻¹ = 1 / (2 ^ (n - 1) * (n.factorial : ℝ)) := by
    have h1 : ProperIntEquiv (pclassOf (sumSq n)).out (sumSq n) :=
      pclassOf_eq_pclassOf_iff.mp (pclassOf_out _)
    rw [card_autPlus_eq_of_intEquiv h1.intEquiv, card_autPlus_sumSq hn]
    push_cast
    rw [one_div]
  have hCpos : 0 < ((Nat.card (AutPlus C.out) : ℝ))⁻¹ := by
    have hpd : IntQF.PosDef C.out := (mem_pgenusClasses_iff_out.mp hC).posDef posDef_sumSq
    have := card_autPlus_pos hpd
    positivity
  have hlt : ∑ D ∈ ({pclassOf (sumSq n)} : Finset (PClass n)), ((Nat.card (AutPlus D.out) : ℝ))⁻¹ <
      ∑ D ∈ hfin.toFinset, ((Nat.card (AutPlus D.out) : ℝ))⁻¹ := by
    refine Finset.sum_lt_sum_of_subset (i := C) ?_ ?_ ?_ ?_ ?_
    · intro D hD
      rw [Finset.mem_singleton] at hD
      rw [Set.Finite.mem_toFinset, hD]; exact hmem
    · exact (Set.Finite.mem_toFinset hfin).mpr hC
    · simpa using hCne
    · exact hCpos
    · intro D _ _; positivity
  rw [Finset.sum_singleton, hterm, ← pweight_sumSq_eq_sum hn, hM.le_eight n hn hn8] at hlt
  exact lt_irrefl _ hlt

/-- **Cassels' deduction, $n > 8$** (App. B, §3, p. 377): assuming Magnus' evaluation `MagnusSumSquares`, for $n > 8$ the
genus of $f_0$ contains further proper classes besides that of $f_0$. (Here, as in the one-class statement, finiteness
is not needed: if the genus were the single class of $f_0$, then $W = 1/o^{+}(f_0) = 1/(2^{n-1}\,n!)$, against the strict
inequality.) -/
@[kb "cassels1978" "App. B, §3, p. 377 (𝓕₀ has one class for n ≤ 8, more for n > 8)"]
theorem pgenusClasses_sumSq_ne_singleton_of_magnus (hM : MagnusSumSquares) {n : ℕ} (hn : 8 < n) :
    pgenusClasses (sumSq n) ≠ {pclassOf (sumSq n)} := by
  intro h
  have hn1 : 1 ≤ n := by omega
  have h1 : ProperIntEquiv (pclassOf (sumSq n)).out (sumSq n) :=
    pclassOf_eq_pclassOf_iff.mp (pclassOf_out _)
  have := hM.gt_eight n hn
  rw [pweight, h, finsum_mem_singleton, card_autPlus_eq_of_intEquiv h1.intEquiv, card_autPlus_sumSq hn1] at this
  push_cast at this
  rw [one_div] at this
  exact lt_irrefl _ this

end QuadFormsKB.Siegel
