/-
# Cassels, Appendix B, §3, p. 377: Magnus' evaluation of the weight of the genus of a sum of squares, proved

Cassels, *Rational Quadratic Forms* (1978), Appendix B, §3, p. 377. The named statement `MagnusSumSquares`
(`SumSquares.lean`) is proved here unconditionally, without Siegel's mass formula, from the classification results
already in the library: the genus of $I_n = x_0^2 + \dots + x_{n-1}^2$ has one class for $n \le 8$
(`genusClasses_sumSq_of_le_eight`, `intEquiv_of_sameGenus_sumSq`) and a second class $E_8 \perp I_{n-8}$ for $n > 8$
(`pgenusClasses_sumSq_ne_singleton`). Indices are 0-based (Cassels' $x_1, \dots, x_n$ are $x_0, \dots, x_{n-1}$).

**Proved.**
* `pweight_sumSq_of_le_eight`: $W(\mathcal F_0) = 1/(2^{n-1}\,n!)$ for $1 \le n \le 8$;
* `pgenusClasses_sumSq_of_le_eight`: the genus has one proper class for $1 \le n \le 8$;
* `pweight_sumSq_gt`: $W(\mathcal F_0) > 1/(2^{n-1}\,n!)$ for $n > 8$;
* `magnusSumSquares_holds`: the named statement `MagnusSumSquares`.
-/
import QuadFormsKB.Literature.Cassels.AppB.SumSquares
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus

open Matrix

noncomputable section

namespace QuadFormsKB.Siegel

/-- **The weight of the genus of $x_0^2 + \dots + x_{n-1}^2$ for $1 \le n \le 8$:**
$W(\mathcal F_0) = 1/(2^{n-1}\,n!)$ (Cassels, App. B, §3, p. 377), unconditionally: the genus has one class
(`genusClasses_sumSq_of_le_eight`) and $W = 2\,\mathrm{mass}$. Here `n` is the number of variables. -/
@[kb "cassels1978" "App. B, §3, p. 377 (W(𝓕₀) = 1/(2^{n−1} n!), n ≤ 8, proved)"]
theorem pweight_sumSq_of_le_eight {n : ℕ} (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    pweight (sumSq n) = 1 / (2 ^ (n - 1) * (n.factorial : ℝ)) := by
  rw [pweight_eq_two_mul_mass hn posDef_sumSq, mass, genusClasses_sumSq_of_le_eight hn8, finsum_mem_singleton,
    QClass.autCard_classOf, card_aut_sumSq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : (0 : ℝ) < (m + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  push_cast [Nat.add_sub_cancel]
  field_simp
  ring

/-- **One proper class for $n \le 8$:** the genus of $I_n$ is the single proper class of $I_n$, for $1 \le n \le 8$
(unconditional). Here `n` is the number of variables. -/
@[kb "cassels1978" "App. B, §3, p. 377 (𝓕₀ is one proper class for n ≤ 8, proved)"]
theorem pgenusClasses_sumSq_of_le_eight {n : ℕ} (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    pgenusClasses (sumSq n) = {pclassOf (sumSq n)} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  ext D
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', hf', hg⟩
    rw [← hf']
    have h1 := intEquiv_of_sameGenus_sumSq hn hn8 hg
    have h2 := (intEquiv_iff_properIntEquiv_of_hasImproperAut (hasImproperAut_sumSq_succ m) f').mp h1
    exact (pclassOf_eq_pclassOf_iff.mpr h2).symm
  · rintro rfl
    exact ⟨sumSq (m + 1), rfl, SameGenus.refl _⟩

/-- **The weight of the genus of $x_0^2 + \dots + x_{n-1}^2$ for $n > 8$ exceeds $1/(2^{n-1}\,n!)$** (Cassels, App. B,
§3, p. 377), unconditionally: $W$ is the finite sum of $1/o^{+}$ over the proper classes of the genus
(`pweight_sumSq_eq_sum`); the class of $I_n$ contributes $1/(2^{n-1}\,n!)$ and a second class
(`pgenusClasses_sumSq_ne_singleton`) contributes a positive amount. Here `n` is the number of variables. -/
@[kb "cassels1978" "App. B, §3, p. 377 (W(𝓕₀) > 1/(2^{n−1} n!) for n > 8, proved)"]
theorem pweight_sumSq_gt {n : ℕ} (hn : 8 < n) :
    1 / (2 ^ (n - 1) * (n.factorial : ℝ)) < pweight (sumSq n) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hfin := pgenusClasses_finite hn1 posDef_sumSq.nondegenerate
  have hmem : pclassOf (sumSq n) ∈ pgenusClasses (sumSq n) := ⟨sumSq n, rfl, SameGenus.refl _⟩
  obtain ⟨C, hC, hCne⟩ : ∃ C ∈ pgenusClasses (sumSq n), C ≠ pclassOf (sumSq n) := by
    by_contra h
    push Not at h
    exact pgenusClasses_sumSq_ne_singleton hn (Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, h⟩)
  have hterm : ((Nat.card (AutPlus (pclassOf (sumSq n)).out) : ℝ))⁻¹ = 1 / (2 ^ (n - 1) * (n.factorial : ℝ)) := by
    have h1 : ProperIntEquiv (pclassOf (sumSq n)).out (sumSq n) :=
      pclassOf_eq_pclassOf_iff.mp (pclassOf_out _)
    rw [card_autPlus_eq_of_intEquiv h1.intEquiv, card_autPlus_sumSq hn1]
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
  rwa [Finset.sum_singleton, hterm, ← pweight_sumSq_eq_sum hn1] at hlt

/-- **Magnus' evaluation of the weight of the genus of $x_1^2 + \dots + x_n^2$, proved** (Cassels, App. B, §3, p. 377):
the named statement `MagnusSumSquares` holds, with no assumption. Field `le_eight` is `pweight_sumSq_of_le_eight`
and field `gt_eight` is `pweight_sumSq_gt`. -/
@[kb "cassels1978" "App. B, §3, p. 377 (Magnus: the weight of the genus of x₁²+⋯+xₙ², proved)"]
theorem magnusSumSquares_holds : MagnusSumSquares :=
  ⟨fun _ h1 h8 => pweight_sumSq_of_le_eight h1 h8, fun _ hn => pweight_sumSq_gt hn⟩

end QuadFormsKB.Siegel
