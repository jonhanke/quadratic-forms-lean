/-
# The class decomposition of $\zeta_{\mathcal O}$

**Layer:** $F$ a number field with $\mathcal O_F$ a PID, $D = (a,b)_F$, $\mathcal O \subset D$ an $\mathcal O_F$-order.

For a left ideal $J$ and $\beta \in (\mathcal O : J)\cap D^\times$ the reduced norm is multiplicative (`absNorm_leftNrdIdeal_rmulIdeal`):
$$N(\operatorname{nrd}(J\beta)) = N(\operatorname{nrd}J)\cdot|N_{F/\mathbb Q}(\operatorname{nrd}\beta)|.$$
With the unfolding of `QuatIdealClasses` this gives, for every left ideal class with $[\Gamma_J : \mathcal O_F^\times] < \infty$
(`index_mul_tsum_class_nrd`),
$$[\Gamma_J : \mathcal O_F^\times]\sum_{J'\sim J}N(\operatorname{nrd}J')^{-s} = N(\operatorname{nrd}J)^{-s}\,E_J(s),\qquad
  E_J(s) = \sum_{\beta \in \mathcal O_F^\times\backslash((\mathcal O:J)\cap D^\times)}|N_{F/\mathbb Q}(\operatorname{nrd}\beta)|^{-s}$$
(`epsteinSum`, the Epstein zeta function of the lattice $(\mathcal O : J)$ with the form $\operatorname{nrd}$, summed over $\mathcal O_F^\times$-orbits).

Source: Voight, *Quaternion Algebras* (2021), Prop. 16.3.2 / Lemma 16.3.7 (multiplicativity of nrd), proof of Thm. 26.5.4,
(26.5.8)–(26.5.9); locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatIdealClasses

open NumberField Quaternion
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat

-- Orders are typed `Subalgebra (𝓞 F) ℍ[F, a, b]` (with `QuaternionAlgebra.instAlgebra`, the instance of the generic
-- `leftNrdIdeal`), not `Subalgebra (𝓞 F) (QuatF F a b)` (where instance search finds `RingOfIntegers.instAlgebra`);
-- the two are definitionally but not reducibly equal. We switch the latter off in this file.
attribute [-instance] NumberField.RingOfIntegers.instAlgebra

section NrdMul

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- The $\mathcal O_F$-span of the reduced norms of a set. -/
def nrdSpan (S : Set (QuatF F a b)) : Submodule (𝓞 F) F := Submodule.span (𝓞 F) (nrd '' S)

/-- **$\operatorname{nrd}(J)$ as a submodule of $F$** is the span of the reduced norms of the elements of $J$ (they are integral). -/
theorem coe_leftNrdIdeal (hO : IsOrder (𝓞 F) F O) (J : Ideal O) :
    IsLocalization.coeSubmodule F (leftNrdIdeal J) = nrdSpan (idealSet J) := by
  rw [IsLocalization.coeSubmodule]; unfold leftNrdIdeal; rw [Submodule.map_span, nrdSpan]
  congr 1
  ext t
  constructor
  · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
    exact ⟨x, coe_mem_idealSet.2 hx, hr.symm⟩
  · rintro ⟨x, ⟨hxO, hxJ⟩, rfl⟩
    obtain ⟨r, hr⟩ := (isInteger_trd_nrd hO hxO).2
    exact ⟨r, ⟨⟨x, hxO⟩, hxJ, hr⟩, hr⟩

theorem nrdSpan_rTrans (S : Set (QuatF F a b)) (β : QuatF F a b) :
    nrdSpan (rTrans S β) = nrdSpan S * Submodule.span (𝓞 F) {nrd β} := by
  rw [nrdSpan, nrdSpan, Submodule.span_mul_span]
  congr 1
  ext t
  simp only [rTrans, Set.mem_image, Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨nrd x, ⟨x, hx, rfl⟩, nrd β, rfl, (nrd_mul x β).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, rfl, rfl⟩
    exact ⟨x * β, ⟨x, hx, rfl⟩, nrd_mul x β⟩

/-- **Multiplicativity of the reduced norm under right translation**, as fractional ideals:
$\operatorname{nrd}(J\beta) = \operatorname{nrd}(J)\cdot(\operatorname{nrd}\beta)$. -/
theorem coeIdeal_leftNrdIdeal_rmulIdeal (hO : IsOrder (𝓞 F) F O) {J : Ideal O} {β : QuatF F a b}
    (hβ : β ∈ colon J) :
    ((leftNrdIdeal (rmulIdeal J β) : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      (leftNrdIdeal J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) *
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (nrd β) := by
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_spanSingleton]
  rw [coe_leftNrdIdeal hO, coe_leftNrdIdeal hO, idealSet_rmulIdeal hβ, nrdSpan_rTrans]

/-- **$N(\operatorname{nrd}(J\beta)) = N(\operatorname{nrd}J)\,|N_{F/\mathbb Q}(\operatorname{nrd}\beta)|$** for $\beta \in (\mathcal O : J)$. -/
theorem absNorm_leftNrdIdeal_rmulIdeal (hO : IsOrder (𝓞 F) F O) {J : Ideal O} {β : QuatF F a b}
    (hβ : β ∈ colon J) :
    (Ideal.absNorm (leftNrdIdeal (rmulIdeal J β)) : ℝ) =
      (Ideal.absNorm (leftNrdIdeal J) : ℝ) * |(Algebra.norm ℚ (nrd β) : ℝ)| := by
  have h := congrArg FractionalIdeal.absNorm (coeIdeal_leftNrdIdeal_rmulIdeal hO hβ)
  rw [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.absNorm_span_singleton (𝓞 F)] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h']

/-- **The Epstein sum of the class of $J$**:
$E_J(s) = \sum_{\beta\in\mathcal O_F^\times\backslash((\mathcal O:J)\cap D^\times)}|N_{F/\mathbb Q}(\operatorname{nrd}\beta)|^{-s} \in [0,\infty]$. -/
def epsteinSum (J : Ideal O) (s : ℝ) : ℝ≥0∞ :=
  ∑' q : MulAction.orbitRel.Quotient (centralUnitsIn (R := 𝓞 F) J) (ColonUnits J),
    ENNReal.ofReal (|(Algebra.norm ℚ (nrd (q.out.1 : QuatF F a b)) : ℝ)| ^ (-s))

/-- The zeta term $N(\operatorname{nrd}J)^{-s}$ of a left ideal, in $[0,\infty)$. -/
def nrdTerm (J : Ideal O) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((Ideal.absNorm (leftNrdIdeal J) : ℝ) ^ (-s))

/-- **The class sum** (Voight 2021, (26.5.8)): $[\Gamma_J:\mathcal O_F^\times]\sum_{J'\sim J}N(\operatorname{nrd}J')^{-s} =
N(\operatorname{nrd}J)^{-s}E_J(s)$. -/
theorem index_mul_tsum_class_nrd (hO : IsOrder (𝓞 F) F O) (J : Ideal O)
    [(centralUnitsIn (R := 𝓞 F) J).FiniteIndex] (s : ℝ) :
    (centralUnitsIn (R := 𝓞 F) J).index * ∑' J' : {J' : Ideal O // IdealRel J J'}, nrdTerm J'.1 s =
      nrdTerm J s * epsteinSum J s := by
  rw [index_mul_tsum_class' J (fun J' => nrdTerm J' s), epsteinSum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [nrdTerm, nrdTerm, absNorm_leftNrdIdeal_rmulIdeal hO q.out.2,
    Real.mul_rpow (Nat.cast_nonneg _) (abs_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

end NrdMul

section ZetaClasses

variable {F : Type} [Field F] [NumberField F] [IsPrincipalIdealRing (𝓞 F)] {a b : 𝓞 F}
  {O : Subalgebra (𝓞 F) ℍ[F,algebraMap (𝓞 F) F a,algebraMap (𝓞 F) F b]}

/-- **$\zeta_{\mathcal O}(s)$ as a sum over left ideals** ($\mathcal O$ maximal, $s > 2$):
$\sum_J N(\operatorname{nrd}J)^{-s} = \sum_{\mathfrak n}c(\mathfrak n)N\mathfrak n^{-s}$ (the Dirichlet series). -/
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
  · obtain ⟨n, rfl⟩ := (IsPrincipalIdealRing.principal 𝔫).principal
    have hn : n ≠ 0 := by rintro rfl; exact h𝔫 (by simp)
    have hcard : Nat.card {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} = _ := card_ideal_nrd_eq ha hb hO hn
    have hpos : Nat.card {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} ≠ 0 := by
      rw [hcard, Finset.prod_ne_zero_iff]
      intro v _
      split_ifs
      · exact one_ne_zero
      · exact (Finset.sum_pos (fun i _ => pow_pos (Nat.pos_of_ne_zero (by
            rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)) i) ⟨0, by simp⟩).ne'
    have hfin : Finite {J : Ideal O // leftNrdIdeal J = Ideal.span {n}} := Nat.finite_of_card_ne_zero hpos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rfl

/-- **The class decomposition of $\zeta_{\mathcal O}$** (Voight 2021, (26.5.9)): for a maximal order with
$[\Gamma_J:\mathcal O_F^\times] < \infty$ for every class, and $s > 2$,
$$\zeta_{\mathcal O}(s) = \sum_{[J]}[\Gamma_J:\mathcal O_F^\times]^{-1}N(\operatorname{nrd}J)^{-s}E_J(s).$$ -/
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

end QuadFormsKB.QuatOrder
