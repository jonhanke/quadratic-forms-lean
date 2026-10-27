/-
# Classical special cases over $\mathbb Q$: Dirichlet's formula for $x_0^2+x_1^2$ and $x_0^2-2x_1^2$

**Layer:** $\mathbb Q$.

From `siegelIndefinite_binary_uncond` (Siegel's formula for an anisotropic binary form, every number field), applied at
$\langle m\rangle$ and at $\langle1\rangle$ (`tsum_repCount_eq_ratio`), with one class of representations of $1$ modulo
units (`tsum_repCount_one_sumTwoSq`, `tsum_repCount_one_pell2`) and the explicit local densities
$\beta_p(m) = \beta_p(1)\sum_{j\le v_p(m)}\chi_D(p)^j$ at odd $p$, $\beta_2(m)\in\{0,\beta_2(1)\}$ (`BinaryDensities.lean`):

* **Dirichlet's formula for $x_0^2+x_1^2$** ($D = -4$, positive definite; `dirichlet_sumTwoSq`): for every $m\ge1$,
  $$\sum_in(M_i,m) = \sum_{d\mid m}\chi_{-4}(d),$$
  the sum over the proper classes $M_i$ of the genus of $\mathbb Z^2$, $n(M_i,m)$ = `repCount` the number of $x\in M_i$ with
  $x_0^2+x_1^2 = m$ **modulo the unit group** $SO(M_i)$ (for $M_i = \mathbb Z^2$: the four rotations by multiples of
  $\pi/2$, acting freely, so $n = r_2(m)/4$ and this is Jacobi's $r_2(m) = 4\sum_{d\mid m}\chi_{-4}(d)$ once the genus is
  known to have one class, which is not formalized here);
* **the same for $x_0^2-2x_1^2$** ($D = 8$, indefinite; `dirichlet_pell2`): $\sum_in(M_i,m) = \sum_{d\mid m}\chi_8(d)$ for every
  $m\ge1$ represented by $x_0^2-2x_1^2$ over $\mathbb Q$; here $SO(M_i)$ is infinite (for $\mathbb Z^2$: $\pm(3+2\sqrt2)^k$, the
  norm-one units of $\mathbb Z[\sqrt2]$), and the regulator enters only the unit volumes $v(M_i)$, which cancel.
-/
import QuadFormsKB.Tamagawa.Classical.BinaryRatio
import QuadFormsKB.Tamagawa.Classical.BinaryDensities
import QuadFormsKB.Tamagawa.Classical.BinaryOrbit

open NumberField IsDedekindDomain
open scoped ENNReal

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB.Binary QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure.Weil RatBridge LocalDensity

/-- **The genus sum against the local product.** -/
theorem tsum_repCount_eq_tprod (Q₀ : QuadForm (𝓞 ℚ) 2) (hQ : Q₀.Nondegenerate) (hA : AnisotropicF Q₀)
    (E : Type) [Field E] [NumberField E] [Algebra ℚ E] (hE : IsDiscField Q₀ E)
    (Ξ₁ : RatFrame Q₀ (DVR.unary 1)) (h1 : ∑' i, Indefinite.repCount Q₀ (DVR.unary (1 : 𝓞 ℚ)) i = 1)
    {m : 𝓞 ℚ} (hm : (m : ℚ) ≠ 0) (Ξ : RatFrame Q₀ (DVR.unary m)) (r : HeightOneSpectrum (𝓞 ℚ) → ℝ)
    (hr : (Function.mulSupport r).Finite) (hβ : ∀ v, NF.localDensity v Q₀ m = NF.localDensity v Q₀ 1 * r v) :
    ∑' i, Indefinite.repCount Q₀ (DVR.unary m) i = ENNReal.ofReal (∏' v, r v) := by
  obtain ⟨hB1, h⟩ := tsum_repCount_eq_ratio Q₀ hQ hA E hE Ξ₁ h1 hm Ξ
  rw [h, binDensityProduct_div Q₀ hQ E hE Ξ₁ r hr hβ hB1]

/-! ### The two forms -/

theorem hessian_det_up_diag (a b : ℤ) : (up (QuadForm.diag ![a, b])).hessian.det = ((4 * a * b : ℤ) : 𝓞 ℚ) := by
  simp [up, Siegel.toOQ, QuadForm.hessian, QuadForm.map, QuadForm.diag]
  ring

theorem nondegenerate_up_sumTwoSq : (up sumTwoSqZ).Nondegenerate := by
  rw [QuadForm.Nondegenerate, sumTwoSqZ, hessian_det_up_diag]; norm_num

theorem nondegenerate_up_pell2 : (up pell2Z).Nondegenerate := by
  rw [QuadForm.Nondegenerate, pell2Z, hessian_det_up_diag]; norm_num

theorem qF_up_diag (a b : ℤ) (ξ : Fin 2 → ℚ) :
    ((up (QuadForm.diag ![a, b])).map (algebraMap (𝓞 ℚ) ℚ)).eval ξ = a * ξ 0 ^ 2 + b * ξ 1 ^ 2 := by
  simp [up, Siegel.toOQ, QuadForm.eval, QuadForm.evalIn, QuadForm.map, QuadForm.diag, Fin.sum_univ_two,
    Matrix.diagonal]
  ring

theorem anisotropicF_up_sumTwoSq : AnisotropicF (up sumTwoSqZ) := by
  intro ξ h
  simp only [sumTwoSqZ, qF_up_diag] at h
  push_cast at h
  have h0 : ξ 0 = 0 := by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]
  have h1 : ξ 1 = 0 := by nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1)]
  funext i; fin_cases i <;> simp [h0, h1]

theorem anisotropicF_up_pell2 : AnisotropicF (up pell2Z) := by
  intro ξ h
  simp only [pell2Z, qF_up_diag] at h
  push_cast at h
  have h1 : ξ 1 = 0 := by
    by_contra hne
    have hsq : (ξ 0 / ξ 1) ^ 2 = 2 := by field_simp; linarith
    have hr : ((ξ 0 / ξ 1 : ℚ) : ℝ) ^ 2 = 2 := by exact_mod_cast hsq
    have habs : |((ξ 0 / ξ 1 : ℚ) : ℝ)| = Real.sqrt 2 := by
      rw [← Real.sqrt_sq_eq_abs, hr]
    exact irrational_sqrt_two (by
      rcases abs_choice ((ξ 0 / ξ 1 : ℚ) : ℝ) with e | e
      · exact ⟨ξ 0 / ξ 1, by rw [← habs, e]⟩
      · exact ⟨-(ξ 0 / ξ 1), by rw [← habs, e]; push_cast; ring⟩)
  have h0 : ξ 0 = 0 := by rw [h1] at h; nlinarith [sq_nonneg (ξ 0)]
  funext i; fin_cases i <;> simp [h0, h1]

/-- $E = \mathbb Q(\sqrt{-4}) = \mathbb Q(i)$ is the discriminant field of $x_0^2 + x_1^2$ ($-\det H = -4 = (2\omega)^2$). -/
theorem isDiscField_sumTwoSq : IsDiscField (up sumTwoSqZ) (QField (-4)) := by
  refine ⟨?_, ⟨QuadraticAlgebra.mk 0 2, ?_, ?_⟩⟩
  · exact QuadraticAlgebra.finrank_eq_two _ _
  · rw [sumTwoSqZ, hessian_det_up_diag]
    ext
    · rw [sq, QuadraticAlgebra.re_mul]; simp; norm_num; exact (map_ofNat _ 4).symm
    · rw [sq, QuadraticAlgebra.im_mul]; simp
  · rintro ⟨q, hq⟩
    have := congrArg QuadraticAlgebra.im hq
    simp at this

/-- $E = \mathbb Q(\sqrt 8) = \mathbb Q(\sqrt 2)$ is the discriminant field of $x_0^2 - 2x_1^2$ ($-\det H = 8 = (2\omega)^2$). -/
theorem isDiscField_pell2 : IsDiscField (up pell2Z) (QField 8) := by
  refine ⟨?_, ⟨QuadraticAlgebra.mk 0 2, ?_, ?_⟩⟩
  · exact QuadraticAlgebra.finrank_eq_two _ _
  · rw [pell2Z, hessian_det_up_diag]
    ext
    · rw [sq, QuadraticAlgebra.re_mul]; simp; norm_num; exact (map_ofNat _ 8).symm
    · rw [sq, QuadraticAlgebra.im_mul]; simp
  · rintro ⟨q, hq⟩
    have := congrArg QuadraticAlgebra.im hq
    simp at this

/-- A rational frame of $\langle m\rangle$ from an integer representation $a x_0^2 + b x_1^2 = m$ at $(x_0, x_1)$. -/
def ratFrameOfInt (a b : ℤ) {m x y : ℤ} (h : a * x ^ 2 + b * y ^ 2 = m) :
    RatFrame (up (QuadForm.diag ![a, b])) (DVR.unary ((m : ℤ) : 𝓞 ℚ)) :=
  (ratFrameEquivRatSphere (up (QuadForm.diag ![a, b])) ((m : ℤ) : 𝓞 ℚ)).symm
    ⟨![(x : ℚ), (y : ℚ)], by
      show ((up (QuadForm.diag ![a, b])).map (algebraMap (𝓞 ℚ) ℚ)).eval ![(x : ℚ), (y : ℚ)] =
        algebraMap (𝓞 ℚ) ℚ ((m : ℤ) : 𝓞 ℚ)
      rw [qF_up_diag, map_intCast]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact_mod_cast h⟩


/-! ### No rational point -/

/-- With no rational frame there are no representations: $\sum_in(M_i,T_0) = 0$. -/
theorem tsum_repCount_eq_zero_of_isEmpty {N r : ℕ} (Q₀ : QuadForm (𝓞 ℚ) N) (T₀ : QuadForm (𝓞 ℚ) r)
    (h : IsEmpty (RatFrame Q₀ T₀)) : ∑' i, Indefinite.repCount Q₀ T₀ i = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun i => ?_
  unfold Indefinite.repCount
  have : IsEmpty (MulAction.orbitRel.Quotient (unitGroup Q₀ i) (repsT Q₀ T₀ i)) := by
    refine ⟨fun q => ?_⟩
    induction q using Quotient.inductionOn with
    | h y =>
      obtain ⟨X, -, -⟩ := y.2
      exact h.false X
  exact tsum_empty

theorem sum_range_neg_one_pow (n : ℕ) : ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd n with he | ho
    · rw [if_pos he, if_neg (Nat.not_even_iff_odd.2 he.add_one), he.neg_one_pow]; ring
    · rw [if_neg (Nat.not_even_iff_odd.2 ho), if_pos ho.add_one, ho.neg_one_pow]; ring

/-- **If $\sum_{d\mid m}\chi_{-4}(d)\ne0$, every prime $q\equiv3\pmod 4$ divides $m$ to an even power.** -/
theorem even_padicValNat_of_sum_chi4_ne_zero {m : ℕ} (hm : m ≠ 0)
    (h : ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) ≠ 0) {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) :
    Even (padicValNat q m) := by
  by_cases hqm : q ∣ m
  · rw [← prod_locRatio₄ hm, Finset.prod_ne_zero_iff] at h
    have hmem : q ∈ (2 * m).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hq, Dvd.dvd.mul_left hqm 2, by omega⟩
    have hloc := h q hmem
    have hq2 : q ≠ 2 := by omega
    have hχ : (ZMod.χ₄ (q : ZMod 4) : ℝ) = -1 := by
      rw [ZMod.χ₄_nat_three_mod_four hq3]; norm_num
    rw [locRatio₄, if_neg hq2, hχ, sum_range_neg_one_pow] at hloc
    rw [← Nat.factorization_def m hq]
    by_contra hodd
    exact hloc (if_pos (Nat.not_even_iff_odd.1 hodd).add_one)
  · rw [padicValNat.eq_zero_of_not_dvd hqm]; exact ⟨0, rfl⟩

/-! ### Dirichlet's formula -/

/-- **Dirichlet's formula for $x_0^2-2x_1^2$** (Dirichlet, *Vorlesungen über Zahlentheorie*, §§ 89–93 [unverified locator];
Siegel 1935, Hauptsatz for $n = 2$, $m = 1$): for $m\ge1$ represented by $x_0^2-2x_1^2$ over $\mathbb Q$, the number of
representations of $m$ by the genus of $\mathbb Z^2$ with $x_0^2 - 2x_1^2$, each class counted modulo its (infinite) unit
group, is $\sum_{d\mid m}\chi_8(d)$, $\chi_8 = \left(\frac 8\cdot\right)$. Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93 (number of representations by a genus) [unverified locator]"]
theorem dirichlet_pell2 (m : ℕ) (hm : 1 ≤ m) (Ξ : RatFrame (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ)))) :
    ∑' i, Indefinite.repCount (up pell2Z) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₈ (d : ZMod 8) : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have Ξ₁ : RatFrame (up pell2Z) (DVR.unary ((1 : ℤ) : 𝓞 ℚ)) := ratFrameOfInt 1 (-2) (x := 1) (y := 0) (by norm_num)
  rw [tsum_repCount_eq_tprod (up pell2Z) nondegenerate_up_pell2 anisotropicF_up_pell2 (QField 8) isDiscField_pell2
    (by simpa using Ξ₁) tsum_repCount_one_pell2 (by exact_mod_cast hm0) Ξ _ (mulSupport_locRatio₈_finite hm0)
    (fun v => by simpa using nfLocalDensity_pell2_eq v hm0), tprod_locRatio₈ hm0]

/-- **Dirichlet's formula for $x_0^2+x_1^2$** (Dirichlet, *Vorlesungen über Zahlentheorie*, §§ 89–93 [unverified locator];
Jacobi's two-squares theorem): for every $m\ge1$, the number of representations of $m$ by the genus of $x_0^2+x_1^2$, each
class counted modulo its unit group, is $\sum_{d\mid m}\chi_{-4}(d)$. If $m$ is not a sum of two squares both sides vanish
(Fermat's criterion, `Nat.eq_sq_add_sq_iff`). Unconditional. -/
@[kb "dirichlet1863" "Vorlesungen über Zahlentheorie, §§ 89–93; Jacobi's r_2 [unverified locator]"]
theorem dirichlet_sumTwoSq (m : ℕ) (hm : 1 ≤ m) :
    ∑' i, Indefinite.repCount (up sumTwoSqZ) (DVR.unary (((m : ℤ) : 𝓞 ℚ))) i =
      ENNReal.ofReal (∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ)) := by
  have hm0 : m ≠ 0 := by omega
  have Ξ₁ : RatFrame (up sumTwoSqZ) (DVR.unary ((1 : ℤ) : 𝓞 ℚ)) := ratFrameOfInt 1 1 (x := 1) (y := 0) (by norm_num)
  by_cases hne : Nonempty (RatFrame (up sumTwoSqZ) (DVR.unary (((m : ℤ) : 𝓞 ℚ))))
  · obtain ⟨Ξ⟩ := hne
    rw [tsum_repCount_eq_tprod (up sumTwoSqZ) nondegenerate_up_sumTwoSq anisotropicF_up_sumTwoSq (QField (-4))
      isDiscField_sumTwoSq (by simpa using Ξ₁) tsum_repCount_one_sumTwoSq (by exact_mod_cast hm0) Ξ _
      (mulSupport_locRatio₄_finite hm0) (fun v => by simpa using nfLocalDensity_sumTwoSq_eq v hm0),
      tprod_locRatio₄ hm0]
  · rw [tsum_repCount_eq_zero_of_isEmpty _ _ (not_nonempty_iff.1 hne)]
    by_cases hs : ∑ d ∈ m.divisors, (ZMod.χ₄ (d : ZMod 4) : ℝ) = 0
    · rw [hs, ENNReal.ofReal_zero]
    · exfalso
      obtain ⟨x, y, hxy⟩ := Nat.eq_sq_add_sq_iff.2 fun q hq hq3 =>
        even_padicValNat_of_sum_chi4_ne_zero hm0 hs (Nat.prime_of_mem_primeFactors hq) hq3
      exact hne ⟨ratFrameOfInt 1 1 (x := x) (y := y) (by rw [hxy]; push_cast; ring)⟩

end QuadFormsKB.Tamagawa.Classical
