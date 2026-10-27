/-
# The $SO$-mass of the trace-zero lattice for every class number: $h_F$ cancels

**Layer:** $F$ totally real (any class number), $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ maximal,
$L = \mathcal O^0$ (`pureLat`), $Q = \langle -a,-b,ab\rangle$, $\Gamma = SO(Q)(F)$, $K_0 = SO(\hat L)$, $K' = \prod_vc_v(\mathcal O_v^\times)$.

* `finite_orbits_KpNF`, `finite_stab_KpNF`: $\Gamma\backslash G/K'$ is finite with finite stabilizers;
* `dcMass_KpNF_eq_mul`: $\mathrm{dcMass}(\Gamma, K') = 2^{\#\mathrm{Ram}_f}\,\mathrm{dcMass}(\Gamma, K_0)$ (`relIndex_KpNF_K0NF`);
* **`dcMass_K0NF_eq`**: with Eichler's mass formula for every class number (`eichler_mass_formula_nf'`) and the double coset mass
  (`classNumber_mul_dcMass_KpNF`), **$h_F$ cancels**:
  $$\mathrm{dcMass}(SO(Q)(F), SO(\hat L)) = 2^{-\#\mathrm{Ram}_f}\cdot\frac{2\,\zeta_F(2)\prod_{\mathfrak p\in\mathrm{Ram}_f}(1-N\mathfrak p^{-1})}
    {c_{\mathcal O}\,d_F^{1/2}\,\pi^{2[F:\mathbb Q]}},$$
  $c_{\mathcal O}$ = the lattice constant of any presentation $\mathcal O = \bigoplus_i\mathfrak a_if_i$.

Source: Voight 2021, Thm. 26.5.4 (Eichler's mass formula, with $h_F$); Weil 1982, §3.7(a), §2.4, p. 23 and Lemma 2.4.2, p. 26.
-/
import QuadFormsKB.Tamagawa.TernaryDcMassNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction Real
open scoped RestrictedProduct nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization
  QuadFormsKB.QuatZeta QuadFormsKB.HilbertModular QuadFormsKB.NFEuler QuadFormsKB.SphericalUnfold
  QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

set_option maxHeartbeats 4000000 in
theorem finite_orbits_KpNF (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O) :
    Finite (orbitRel.Quotient (GamNF a b) (soAf (QP a b) ⧸ KpNF O)) := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := Gen.finite_classes ha hb hO hdiv
  set Y := orbitRel.Quotient (GamNF a b) (soAf (QP a b) ⧸ KpNF O)
  have hJ : ∀ ω : Y, ∃ J : Ideal O, leftNrdIdeal J ≠ ⊥ ∧ IsGenNF J ((Quotient.out ω.out : soAf (QP a b)) : OAf (QP a b)) :=
    fun ω => exists_isGenNF_of_mem ha hb hO hdiv (Quotient.out ω.out : soAf (QP a b)).2
  choose J hJ0 hJg using hJ
  refine Finite.of_injective (fun ω => Quotient.mk (idealSetoid O) (J ω)) fun ω ω' h => ?_
  obtain ⟨δ, hδ⟩ := Quotient.exact h
  have hδ' : idealSet (Gen.scaleIdeal ⊤ (J ω')) = rTrans (idealSet (Gen.scaleIdeal ⊤ (J ω))) (δ : QuatF F a b) := by
    rw [Gen.idealSet_scaleIdeal_top, Gen.idealSet_scaleIdeal_top]; exact hδ
  have hmem := mem_KANF_of_scale ha (hJg ω) (hJg ω') top_ne_bot top_ne_bot δ hδ'
  have horb := (mem_orbit_iff_NF (O := O) ha hb (isGenNF_mem_soAf (hJg ω)) (isGenNF_mem_soAf (hJg ω'))).2 ⟨_, hmem⟩
  have e : ∀ ω : Y, (QuotientGroup.mk (⟨((Quotient.out ω.out : soAf (QP a b)) : OAf (QP a b)),
      isGenNF_mem_soAf (hJg ω)⟩ : soAf (QP a b)) : soAf (QP a b) ⧸ KpNF O) = ω.out := fun ω => by
    conv_rhs => rw [← Quotient.out_eq' ω.out]
  rw [e, e] at horb
  rw [← Quotient.out_eq' ω, ← Quotient.out_eq' ω']
  exact (Quotient.sound' (orbitRel_apply.2 horb)).symm

set_option maxHeartbeats 4000000 in
theorem finite_stab_KpNF (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) (x : soAf (QP a b) ⧸ KpNF O) : Finite (stabilizer (GamNF a b) x) := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  induction x using QuotientGroup.induction_on with | H h => ?_
  obtain ⟨J, hJ, hJh⟩ := exists_isGenNF_of_mem ha hb hO hdiv h.2
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    apply hJ
    refine Ideal.span_eq_bot.2 fun r ⟨x, hx, hr⟩ => ?_
    have h0 : nrd (x : QuatF F a b) = 0 := by rw [show x = 0 from hx]; simp [nrd]
    rw [h0] at hr
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 hr
  have hcard := card_stab_eq ha hb hO hJ hJh
  have hfi : (centralUnitsIn (R := 𝓞 F) J).FiniteIndex := finiteIndex_centralUnitsIn (O := O) hdef hO.1 hstd hJ0
  have hpos : 0 < Nat.card (stabilizer (ClassGroup (𝓞 F)) (Quotient.mk (idealSetoid O) J)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  change Nat.card (stabilizer (GamNF a b) (cosetJ hJh)) ≠ 0
  rw [hcard]
  exact mul_ne_zero hfi.index_ne_zero hpos.ne'

/-- $\mathrm{dcMass}(\Gamma, K') = 2^{\#\mathrm{Ram}_f}\cdot\mathrm{dcMass}(\Gamma, K_0)$. -/
theorem dcMass_KpNF_eq_mul (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) :
    dcMass (GamNF a b) (KpNF O) = (2 : ℝ) ^ (ramFin ha hb).card * dcMass (GamNF a b) (K0NF hO.1) := by
  have hle := KpNF_le_K0NF (O := O) hO.1
  have hrel := relIndex_KpNF_K0NF hO ha hb
  have hrel0 : (KpNF O).relIndex (K0NF hO.1) ≠ 0 := by rw [hrel]; positivity
  have hK : (K0NF hO.1).Commensurable (KpNF O) :=
    ⟨⟨by rw [Subgroup.relIndex_eq_one.2 hle]; exact one_ne_zero⟩, ⟨hrel0⟩⟩
  have := finite_orbits_KpNF ha hb hdef hO
  have : Finite (orbitRel.Quotient (GamNF a b) (soAf (QP a b) ⧸ K0NF hO.1)) :=
    finite_orbits_of_commensurable _ _ _ hK
  have hstab0 := finite_stabilizer_of_commensurable (GamNF a b) (KpNF O) (K0NF hO.1) hK
    (finite_stab_KpNF ha hb hdef hO hstd)
  rw [dcMass_of_le (GamNF a b) hle hrel0 hstab0, hrel]
  push_cast; ring

/-- **The $SO$-mass of the trace-zero lattice of a maximal order, every class number ($h_F$ cancels):**
$$\mathrm{dcMass}(SO(Q)(F), SO(\hat L)) = 2^{-\#\mathrm{Ram}_f}\,\frac{2\zeta_F(2)\prod_{\mathrm{Ram}_f}(1-N\mathfrak p^{-1})}{c_{\mathcal O}\,d_F^{1/2}\,\pi^{2[F:\mathbb Q]}}.$$ -/
@[kb "voight2021" "Thm. 26.5.4 (Eichler's mass formula with h_F); Weil 1982, §3.7(a)"]
theorem dcMass_K0NF_eq (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) (hO : IsMaximalOrder (𝓞 F) F O)
    (hstd : stdOrder F a b ≤ O) {fO : Fin 4 → QuatF F a b} {𝔞O : Fin 4 → FracIdeal F}
    (hliO : LinearIndependent F fO)
    (hmemO : ∀ x, x ∈ (O : Set (QuatF F a b)) ↔ ∃ ξ : Fin 4 → F, LatMem 𝔞O ξ ∧ x = ∑ i, ξ i • fO i) :
    dcMass (GamNF a b) (K0NF hO.1) = ((2 : ℝ) ^ (ramFin ha hb).card)⁻¹ *
      (2 * dedekindZetaR F 2 * (∏ v ∈ ramFin ha hb, (1 - (normP v : ℝ) ^ (-(1 : ℝ)))) /
        (latConst (gramMat fO) 𝔞O * (NumberField.discr F : ℝ) ^ (1 / 2 : ℝ) *
          π ^ (2 * Fintype.card (InfinitePlace F)))) := by
  have h1 := classNumber_mul_dcMass_KpNF ha hb hdef hO hstd
  rw [Gen.eichler_mass_formula_nf' ha hb hdef hO hstd hliO hmemO, dcMass_KpNF_eq_mul ha hb hdef hO hstd] at h1
  have hh : (NumberField.classNumber F : ℝ) ≠ 0 := by exact_mod_cast NumberField.classNumber_ne_zero F
  have h2 : (0 : ℝ) < 2 ^ (ramFin ha hb).card := by positivity
  generalize dcMass (GamNF a b) (K0NF hO.1) = X at h1 ⊢
  field_simp at h1 ⊢
  linear_combination h1

end QuadFormsKB.QuatOrder
