/-
# Conway–Sloane, Ch. 15, §9.5: upper bounds for the $2$-adically automorphous numbers

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §9.5, p. 391
(`conwaysloane1999`).

**Layer.** As in `Section9Theorem18.lean`, over $\mathbb Q$ at the prime $v$ over $2$; the $\mathbb Q$-algebra structure
on $\mathbb Q_2$ is the completion's (`instAlgebraAdicCompletion`, as in `Section9Kernel.lean`).

The book's examples (§9.6, (44), §11) need to know that certain numbers are *not* $2$-adically automorphous. At odd
primes this follows from Theorem 18 (`theorem18_odd`, proved); at $p = 2$ the "only if" direction of Theorem 18 is the
named statement `Theorem18Dyadic`. This file derives from it general bounds. (The examples themselves no longer use
it: their $2$-adic bounds are proved directly in `Section9DyadicEven.lean`, `Section9DyadicGlue.lean` and
`Section11TwoClasses.lean`, with Wall's formula.)

**Proves**
* `Theorem18Dyadic.exists_rootVectors'`: the statement with the completion's algebra structure;
* `even_log_of_theorem18Dyadic`: assuming `Theorem18Dyadic`, if every $2$-adic root vector $x$ has
  $\lvert Q(x)\rvert_2 = 2^{-(2k+1)}$ for some $k$ (odd order, as for root vectors of norm $2\cdot$unit), then every
  $2$-adically automorphous number has even order.
-/
import QuadFormsKB.Literature.ConwaySloane.Section9Theorem18Odd

open NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.ConwaySloane

open Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- `Theorem18Dyadic` with the completion's $\mathbb Q$-algebra structure on $\mathbb Q_2$. -/
theorem Theorem18Dyadic.exists_rootVectors' (hT : Theorem18Dyadic) {n : ℕ} (Q : QuadForm ℚ n)
    (hQ : Q.Nondegenerate) (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup Q hQ v L) :
    ∃ xs : List (Fin n → v.adicCompletion ℚ), Even xs.length ∧ (∀ x ∈ xs, IsRootVector Q L v x) ∧
      SqClass.mk A = sqClassOf (valProd Q (v.adicCompletion ℚ) xs) := by
  have h := hT.exists_rootVectors n Q hQ L v h2 A
  rw [← instAlgebraAdicCompletion_rat_eq v] at h
  exact h hA

/-- Products of an even number of elements of odd order have even order. -/
theorem exists_even_of_list {n : ℕ} {v : HeightOneSpectrum (𝓞 ℚ)} (xs : List (Fin n → v.adicCompletion ℚ)) (Q : QuadForm ℚ n)
    (hodd : ∀ x ∈ xs, ∃ k : ℤ, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) = exp (2 * k + 1))
    (m : ℕ) (hm : xs.length = 2 * m) :
    ∃ k : ℤ, Valued.v (valProd Q (v.adicCompletion ℚ) xs) = exp (2 * k) := by
  induction m generalizing xs with
  | zero =>
    obtain rfl : xs = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨0, by simp [valProd]⟩
  | succ m ih =>
    match xs, hm with
    | x :: y :: rest, hm =>
      obtain ⟨a, ha⟩ := hodd x (by simp)
      obtain ⟨b, hb⟩ := hodd y (by simp)
      obtain ⟨c, hc⟩ := ih rest (fun z hz => hodd z (by simp [hz])) (by simp at hm; omega)
      refine ⟨a + b + 1 + c, ?_⟩
      have e : valProd Q (v.adicCompletion ℚ) (x :: y :: rest) =
          Q.evalIn (v.adicCompletion ℚ) x * (Q.evalIn (v.adicCompletion ℚ) y * valProd Q _ rest) := by
        simp only [valProd, List.map_cons, List.prod_cons]
      rw [e, map_mul, map_mul, ha, hb, hc, ← exp_add, ← exp_add]
      congr 1; ring

/-- **The $2$-adically automorphous numbers have even order** when every $2$-adic root vector has a norm of odd
order (for instance $2\cdot$unit), assuming the $p = 2$ case of Theorem 18 (`Theorem18Dyadic`). -/
theorem even_log_of_theorem18Dyadic (hT : Theorem18Dyadic) {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate)
    (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (hodd : ∀ x, IsRootVector Q L v x → ∃ k : ℤ, Valued.v (Q.evalIn (v.adicCompletion ℚ) x) = exp (2 * k + 1))
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup Q hQ v L) :
    ∃ k : ℤ, Valued.v (A : v.adicCompletion ℚ) = exp (2 * k) := by
  obtain ⟨xs, ⟨m, hm⟩, hr, hAx⟩ := hT.exists_rootVectors' Q hQ L v h2 A hA
  have hv0 : valProd Q (v.adicCompletion ℚ) xs ≠ 0 := valProd_ne_zero Q _ (fun z hz => (hr z hz).1)
  obtain ⟨k, hk⟩ := exists_even_of_list xs Q (fun x hx => hodd x (hr x hx)) m (by omega)
  rw [sqClassOf_of_ne_zero hv0] at hAx
  set B : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hv0 with hB
  have h1 : SqClass.mk (A⁻¹ * B) = 1 := by
    rw [SqClass.mk_mul, ← hAx]
    exact inv_mul_cancel (SqClass.mk A)
  obtain ⟨y, hy⟩ := (SqClass.mk_eq_one_iff (A⁻¹ * B)).mp h1
  have hAe : A = B * (y ^ 2)⁻¹ := by rw [hy]; group
  have hAv : (A : v.adicCompletion ℚ) = valProd Q _ xs * ((y : v.adicCompletion ℚ) ^ 2)⁻¹ := by
    conv_lhs => rw [hAe]
    simp [hB]
  have hsv : Valued.v (y : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  refine ⟨k - WithZero.log (Valued.v (y : v.adicCompletion ℚ)), ?_⟩
  rw [hAv, map_mul, map_inv₀, map_pow, hk, ← exp_log hsv, ← exp_nsmul, ← exp_neg, ← exp_add, log_exp]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The $2$-adically automorphous numbers lie in $H$** when every product $Q(x)Q(y)$ of two $2$-adic root vectors has
its square class in the subgroup $H$, assuming the $p = 2$ case of Theorem 18 (`Theorem18Dyadic`). -/
theorem mem_of_theorem18Dyadic (hT : Theorem18Dyadic) {n : ℕ} (Q : QuadForm ℚ n) (hQ : Q.Nondegenerate)
    (L : Lat ℚ n) (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (H : Subgroup (SqClass (v.adicCompletion ℚ)))
    (hpair : ∀ x y, IsRootVector Q L v x → IsRootVector Q L v y →
      sqClassOf (Q.evalIn (v.adicCompletion ℚ) x * Q.evalIn (v.adicCompletion ℚ) y) ∈ H)
    (A : (v.adicCompletion ℚ)ˣ) (hA : A ∈ localSpinorNormGroup Q hQ v L) : SqClass.mk A ∈ H := by
  obtain ⟨xs, ⟨m, hm⟩, hr, hAx⟩ := hT.exists_rootVectors' Q hQ L v h2 A hA
  rw [hAx]
  suffices key : ∀ m (xs : List (Fin n → v.adicCompletion ℚ)), xs.length = 2 * m →
      (∀ x ∈ xs, IsRootVector Q L v x) → sqClassOf (valProd Q (v.adicCompletion ℚ) xs) ∈ H from
    key m xs (by omega) hr
  intro m
  induction m with
  | zero =>
    intro xs hl _
    obtain rfl : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp only [valProd, List.map_nil, List.prod_nil, sqClassOf_one]
    exact H.one_mem
  | succ m ih =>
    intro xs hl hr
    match xs, hl with
    | x :: y :: rest, hl =>
      have hrx := hr x (by simp)
      have hry := hr y (by simp)
      have hrest : ∀ z ∈ rest, IsRootVector Q L v z := fun z hz => hr z (by simp [hz])
      have hv0 : valProd Q (v.adicCompletion ℚ) rest ≠ 0 := valProd_ne_zero Q _ (fun z hz => (hrest z hz).1)
      have hxy := mul_ne_zero hrx.1 hry.1
      have e : valProd Q (v.adicCompletion ℚ) (x :: y :: rest) =
          (Q.evalIn (v.adicCompletion ℚ) x * Q.evalIn (v.adicCompletion ℚ) y) * valProd Q _ rest := by
        simp only [valProd, List.map_cons, List.prod_cons]; ring
      rw [e, sqClassOf_mul hxy hv0]
      exact H.mul_mem (hpair x y hrx hry) (ih rest (by simp at hl; omega) hrest)

end QuadFormsKB.ConwaySloane
