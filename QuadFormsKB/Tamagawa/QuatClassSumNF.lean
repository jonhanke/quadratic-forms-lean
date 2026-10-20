/-
# The class decomposition of $\zeta_{\mathcal O}$ for every class number

**Layer:** $F$ a number field (any class number), $D = (a,b)_F$ ($ab \ne 0$), $\mathcal O \subset D$ a maximal $\mathcal O_F$-order.
`QuatClassSum` proves the class sum formula $[\Gamma_J:\mathcal O_F^\times]\sum_{J'\sim J}N(\operatorname{nrd}J')^{-s} = N(\operatorname{nrd}J)^{-s}E_J(s)$
(`index_mul_tsum_class_nrd`) without any hypothesis on the class number; only the passage from $\sum_JN(\operatorname{nrd}J)^{-s}$ to the Dirichlet series
$\sum_{\mathfrak n}c(\mathfrak n)N\mathfrak n^{-s}$ used principal reduced norms $(n)$. Here (`Gen.tsum_nrdTerm_eq`, `Gen.zetaO_eq_tsum_class`) it is done with
`card_ideal_nrd_eq_N` for an arbitrary ideal $\mathfrak n$:
$$\zeta_{\mathcal O}(s) = \sum_{[J]}[\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}E_J(s)\qquad(s>2).$$

Source: Voight, *Quaternion Algebras* (2021), (26.5.8)–(26.5.9).
-/
import QuadFormsKB.Tamagawa.QuatClassSum
import QuadFormsKB.Tamagawa.QuatZetaEulerNF

open NumberField Quaternion IsDedekindDomain
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.LocalDensity.NF

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

namespace Gen

section ZetaClasses

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- Every nonzero ideal has only finitely many left ideals of a maximal order with that reduced norm, and at least one
(the count `card_ideal_nrd_eq_N` is a positive product). -/
theorem finite_and_pos_card (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {𝔫 : Ideal (𝓞 F)} (h𝔫 : 𝔫 ≠ ⊥) :
    Finite {J : Ideal O // leftNrdIdeal J = 𝔫} ∧ Nat.card {J : Ideal O // leftNrdIdeal J = 𝔫} ≠ 0 := by
  obtain ⟨n, hn𝔫, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔫
  have hcard : Nat.card {J : Ideal O // leftNrdIdeal J = 𝔫} = _ := card_ideal_nrd_eq_N ha hb hO h𝔫 hn hn𝔫
  have hpos : Nat.card {J : Ideal O // leftNrdIdeal J = 𝔫} ≠ 0 := by
    rw [hcard, Finset.prod_ne_zero_iff]
    intro v _
    split_ifs
    · exact one_ne_zero
    · exact (Finset.sum_pos (fun i _ => pow_pos (Nat.pos_of_ne_zero (by
          rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)) i) ⟨0, by simp⟩).ne'
  exact ⟨Nat.finite_of_card_ne_zero hpos, hpos⟩

/-- **$\zeta_{\mathcal O}(s)$ as a sum over left ideals** ($\mathcal O$ maximal, $s > 2$, every class number). -/
theorem tsum_nrdTerm_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {s : ℝ} (hs : 2 < s) :
    ∑' J : Ideal O, nrdTerm J s =
      ENNReal.ofReal (∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)) := by
  have hs0 : -s ≠ 0 := by linarith
  have hnn : ∀ 𝔫 : Ideal (𝓞 F), 0 ≤ (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s) := fun 𝔫 =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [ENNReal.ofReal_tsum_of_nonneg hnn (hasSum_zetaO ha hb hO hs).summable,
    ← (Equiv.sigmaFiberEquiv (leftNrdIdeal (O := O))).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun 𝔫 => ?_
  have e : ∀ J : {J : Ideal O // leftNrdIdeal J = 𝔫},
      nrdTerm ((Equiv.sigmaFiberEquiv (leftNrdIdeal (O := O))) ⟨𝔫, J⟩) s =
        ENNReal.ofReal ((Ideal.absNorm 𝔫 : ℝ) ^ (-s)) := fun J => by
    rw [Equiv.sigmaFiberEquiv_apply, nrdTerm, J.2]
  rw [tsum_congr e, ENNReal.tsum_const]
  by_cases h𝔫 : 𝔫 = ⊥
  · subst h𝔫
    simp [Real.zero_rpow hs0]
  · obtain ⟨hfin, -⟩ := finite_and_pos_card ha hb hO h𝔫
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rfl

/-- **The class decomposition of $\zeta_{\mathcal O}$ for every class number** (Voight 2021, (26.5.9)): for a maximal order with
$[\Gamma_J:\mathcal O_F^\times] < \infty$ for every class, and $s > 2$,
$$\zeta_{\mathcal O}(s) = \sum_{[J]}[\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}E_J(s).$$ -/
@[kb "voight2021" "(26.5.9)"]
theorem zetaO_eq_tsum_class (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O)
    (hfin : ∀ J : Ideal O, (centralUnitsIn (R := 𝓞 F) J).FiniteIndex) {s : ℝ} (hs : 2 < s) :
    ENNReal.ofReal (∑' 𝔫 : Ideal (𝓞 F), (idealCountO O 𝔫 : ℝ) * (Ideal.absNorm 𝔫 : ℝ) ^ (-s)) =
      ∑' c : Quotient (idealSetoid O),
        ((centralUnitsIn (R := 𝓞 F) c.out).index : ℝ≥0∞)⁻¹ * (nrdTerm c.out s * epsteinSum c.out s) := by
  rw [← tsum_nrdTerm_eq ha hb hO hs, tsum_ideal_eq_tsum_class]
  refine tsum_congr fun c => ?_
  have := hfin c.out
  rw [← index_mul_tsum_class_nrd hO.1 c.out s, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _

end ZetaClasses

end Gen

end QuadFormsKB.QuatOrder
