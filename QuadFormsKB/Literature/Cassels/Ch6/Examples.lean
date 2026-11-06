/-
# Cassels, Chapter 6, Examples

**Setting.** Rational forms `Q R : RatQF n`, regular = `Nondegenerate`, equivalence over $K \supseteq \mathbb Q$ =
`IsometricIn K`, the places of $\mathbb Q$ = `RatPlace`.

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6, Examples, pp. 99–101)
* Example 2 (ii): $x_0^2 - 82x_1^2$ and $2x_0^2 - 41x_1^2$ are equivalent over $\mathbb Q$, with an explicit
  equivalence (`ex2_ii`);
* Example 9: regular rational forms equivalent over $\mathbb R$ and over $\mathbb Q_p$ for all primes $p$ except
  possibly one are equivalent over $\mathbb Q$ (`ex9`).

**Proof notes.** Example 2 (ii): the substitution $x_0 \mapsto (10x_0 + 41x_1)/3$, $x_1 \mapsto (x_0 + 5x_1)/3$ (of
determinant $1$) takes $x_0^2 - 82x_1^2$ to $2x_0^2 - 41x_1^2$. Example 9: diagonalize; the quotient of the
determinants is a square in $\mathbb Q_p$ for $p \ne p_0$, hence (product formula for the Hilbert symbol and its
nondegeneracy at $p_0$) also in $\mathbb Q_{p_0}$; the Hasse invariants agree at all $v \ne p_0$, hence at $p_0$ by the
product formula (Ch. 6, Lemma 1.1); so the forms are equivalent over $\mathbb Q_{p_0}$ by the local classification
(Ch. 4, Thm. 1.1), and over $\mathbb Q$ by the Weak Hasse Principle (Theorem 1.2).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseConventions

namespace QuadFormsKB.Cassels.Ch6

open Matrix

variable {n : ℕ}

/-- **Cassels, Ch. 6, Example 2 (ii)**: *$x_0^2 - 82x_1^2$ and $2x_0^2 - 41x_1^2$ are equivalent over $\mathbb Q$*:
the matrix $P = \frac13\begin{pmatrix} 10 & 41 \\ 1 & 5\end{pmatrix}$ ($\det P = 1$) satisfies
$(P\vec x)_0^2 - 82(P\vec x)_1^2 = 2x_0^2 - 41x_1^2$. -/
@[kb "cassels1978" "Ch. 6, Ex. 2 (ii), p. 100"]
theorem ex2_ii : (QuadForm.diag ![(1 : ℚ), -82]).IsometricIn ℚ (QuadForm.diag ![(2 : ℚ), -41]) ∧
    ∀ x : Fin 2 → ℚ, (QuadForm.diag ![(1 : ℚ), -82]).eval (!![10 / 3, 41 / 3; 1 / 3, 5 / 3] *ᵥ x) =
      (QuadForm.diag ![(2 : ℚ), -41]).eval x := by
  have key : ∀ x : Fin 2 → ℚ, (QuadForm.diag ![(1 : ℚ), -82]).eval (!![10 / 3, 41 / 3; 1 / 3, 5 / 3] *ᵥ x) =
      (QuadForm.diag ![(2 : ℚ), -41]).eval x := by
    intro x
    simp only [QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Matrix.mulVec, dotProduct, Fin.isValue]
    simp
    ring
  refine ⟨⟨!![10 / 3, 41 / 3; 1 / 3, 5 / 3], ?_, key⟩, key⟩
  rw [Matrix.det_fin_two_of]
  norm_num

open QuadFormsKB RatPlace in
/-- Cassels' $c_v$ takes values $\pm 1$. -/
theorem ex9_hasse_pm (v : RatPlace) (a : Fin n → ℚ) : v.hasseCassels a = 1 ∨ v.hasseCassels a = -1 := by
  have : IsUnit (v.hasseCassels a) := by
    unfold RatPlace.hasseCassels
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j _ => ?_
    split_ifs
    · rcases hilbert_pm v (a i) (a j) with h | h <;> rw [h] <;> simp
    · exact isUnit_one
  exact Int.isUnit_iff.mp this

open QuadFormsKB RatPlace in
/-- Transfer of a local property along an implication valid over all fields. -/
theorem ex9_atPlace_mono {P P' : (K : Type) → [Field K] → [CharZero K] → Prop}
    (H : ∀ (K : Type) [Field K] [CharZero K], P K → P' K) {v : RatPlace} (h : v.atPlace P) :
    v.atPlace P' := by
  cases v with
  | infinite => exact H ℝ h
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    exact H ℚ_[p.1] h

open QuadFormsKB RatPlace in
/-- If `d₁, d₂` are in the same square class at all places but `p₀`, also at `p₀`. -/
theorem ex9_sameSq (p₀ : Nat.Primes) [Fact p₀.1.Prime] (da db : ℚ) (hda : da ≠ 0) (hdb : db ≠ 0)
    (h : ∀ v : RatPlace, v ≠ RatPlace.finite p₀ → SameSqAt v da db) :
    ∃ t : ℚ_[p₀.1], t ≠ 0 ∧ (db : ℚ_[p₀.1]) = t ^ 2 * (da : ℚ_[p₀.1]) := by
  have he : da * db ≠ 0 := mul_ne_zero hda hdb
  have key : ∀ c : ℚ, c ≠ 0 → (RatPlace.finite p₀).hilbert c (da * db) = 1 := by
    intro c hc
    obtain ⟨-, hev⟩ := hilbert_product_formula c (da * db) hc he
    have hsub : {v : RatPlace | v.hilbert c (da * db) = -1} ⊆ {RatPlace.finite p₀} := by
      intro v hv
      by_contra hne
      have h1 := (h v hne).hilbert_right c
      have h2 := hilbert_mul_right v c da db hc hda hdb
      have hv' : v.hilbert c (da * db) = -1 := hv
      rw [h2, h1] at hv'
      rcases hilbert_pm v c da with h3 | h3 <;> rw [h3] at hv' <;> simp at hv'
    by_contra hne1
    have hm1 : (RatPlace.finite p₀).hilbert c (da * db) = -1 := by
      rcases hilbert_pm (RatPlace.finite p₀) c (da * db) with h3 | h3
      · exact absurd h3 hne1
      · exact h3
    have : {v : RatPlace | v.hilbert c (da * db) = -1} = {RatPlace.finite p₀} :=
      Set.Subset.antisymm hsub (by simpa using hm1)
    rw [this, Set.ncard_singleton] at hev
    exact absurd hev (by decide)
  have hsq : IsSquare ((da * db : ℚ) : ℚ_[p₀.1]) := by
    by_contra hns
    have he0 : ((da * db : ℚ) : ℚ_[p₀.1]) ≠ 0 := by exact_mod_cast he
    obtain ⟨x, hx0, hx⟩ := (PadicClass.localHilbertField_padic p₀.1).exists_neg_one _ he0 hns
    obtain ⟨q, hq, s, hs⟩ := Prescribed.exists_rat_sq_class p₀.1 x hx0
    have hq0 : (q : ℚ_[p₀.1]) ≠ 0 := by exact_mod_cast hq
    have hxs : x = s ^ 2 * (q : ℚ_[p₀.1]) := by
      rw [div_eq_iff hq0] at hs; rw [hs]; ring
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hx0
      rw [hxs]; simp
    rw [hxs, PadicClass.hs_sq_right _ _ _ hs0, hilbertSymbol_comm] at hx
    have := key q hq
    simp only [RatPlace.hilbert] at this
    rw [hx] at this
    norm_num at this
  obtain ⟨s, hs⟩ := hsq
  have hdb0 : (db : ℚ_[p₀.1]) ≠ 0 := by exact_mod_cast hdb
  have hda0 : (da : ℚ_[p₀.1]) ≠ 0 := by exact_mod_cast hda
  have hs' : (da : ℚ_[p₀.1]) * db = s * s := by exact_mod_cast hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hda0 hdb0 (by rw [hs']; ring)
  refine ⟨s / da, div_ne_zero hs0 hda0, ?_⟩
  rw [show (s / (da : ℚ_[p₀.1])) ^ 2 * da = (s * s) * (da : ℚ_[p₀.1])⁻¹ * ((da : ℚ_[p₀.1])⁻¹ * da) by ring,
    inv_mul_cancel₀ hda0, mul_one, ← hs']
  field_simp

/-- **Cassels, Ch. 6, Example 9**: *let $f, g$ be regular rational forms in $n$ variables which are equivalent over
$\mathbb R$ and over $\mathbb Q_p$ for all finite primes $p$ except possibly a single prime $p_0$; then they are
equivalent over $\mathbb Q$.* -/
@[kb "cassels1978" "Ch. 6, Ex. 9, p. 101"]
theorem ex9 (Q R : RatQF n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) (p₀ : Nat.Primes)
    (h : ∀ v : RatPlace, v ≠ RatPlace.finite p₀ → v.atPlace fun K _ _ => Q.IsometricIn K R) :
    Q.IsometricIn ℚ R := by
  obtain ⟨a, ha, hQa⟩ := HM3.exists_isometric_diag Q hQ
  obtain ⟨b, hb, hRb⟩ := HM3.exists_isometric_diag R hR
  have hda : diagDet a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hdb : diagDet b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  have hloc : ∀ v : RatPlace, v ≠ RatPlace.finite p₀ →
      v.atPlace fun K _ _ => (QuadForm.diag a).IsometricIn K (QuadForm.diag b) := by
    intro v hv
    refine ex9_atPlace_mono (fun K _ _ hK => ?_) (h v hv)
    exact QuadForm.isometricIn_trans K (QuadForm.isometricIn_symm K (HM3.isometricIn_of_rat K hQa))
      (QuadForm.isometricIn_trans K hK (HM3.isometricIn_of_rat K hRb))
  have hfin : (QuadForm.diag a).IsometricIn ℚ (QuadForm.diag b) := by
    rw [isometric_iff_everywhere _ _ (QuadForm.nondegenerate_diag ha) (QuadForm.nondegenerate_diag hb)]
    intro v
    by_cases hv : v = RatPlace.finite p₀
    · subst hv
      have : Fact p₀.1.Prime := ⟨p₀.2⟩
      show (QuadForm.diag a).IsometricIn ℚ_[p₀.1] (QuadForm.diag b)
      rw [isometric_padic_iff p₀.1 a b ha hb]
      refine ⟨?_, ?_⟩
      · obtain ⟨t, ht, e⟩ := ex9_sameSq p₀ (diagDet a) (diagDet b) hda hdb
          fun v hv => sameSq_of_isometric v a b (hloc v hv)
        -- db = t² da, so da = (t⁻¹)² db
        refine ⟨t⁻¹, inv_ne_zero ht, ?_⟩
        have e' : algebraMap ℚ ℚ_[p₀.1] (∏ i, b i) = t ^ 2 * algebraMap ℚ ℚ_[p₀.1] (∏ i, a i) := by
          simpa [diagDet] using e
        rw [e']
        field_simp
      · have hpm := hasseCassels_product_formula a ha
        have hpm' := hasseCassels_product_formula b hb
        have hmul : ∏ᶠ v : RatPlace, (v.hasseCassels a * v.hasseCassels b) = 1 := by
          rw [finprod_mul_distrib hpm.1 hpm'.1, hpm.2, hpm'.2]; rfl
        have hsingle : ∏ᶠ v : RatPlace, (v.hasseCassels a * v.hasseCassels b) =
            (RatPlace.finite p₀).hasseCassels a * (RatPlace.finite p₀).hasseCassels b := by
          refine finprod_eq_single _ (RatPlace.finite p₀) fun v hv => ?_
          rw [RatPlace.hasseCassels_isometric v a b ha hb (hloc v hv)]
          rcases ex9_hasse_pm v b with h | h <;> rw [h] <;> norm_num
        rw [hsingle] at hmul
        have e1 := RatPlace.hasseSerre_finite p₀ a
        have e2 := RatPlace.hasseSerre_finite p₀ b
        rw [← e1, ← e2]
        show (RatPlace.finite p₀).hasseCassels a = (RatPlace.finite p₀).hasseCassels b
        rcases ex9_hasse_pm (RatPlace.finite p₀) a with h | h <;>
          rcases ex9_hasse_pm (RatPlace.finite p₀) b with h' | h' <;> rw [h, h'] at hmul ⊢ <;> simp_all
    · exact hloc v hv
  exact QuadForm.isometricIn_trans ℚ hQa
    (QuadForm.isometricIn_trans ℚ hfin (QuadForm.isometricIn_symm ℚ hRb))

end QuadFormsKB.Cassels.Ch6
