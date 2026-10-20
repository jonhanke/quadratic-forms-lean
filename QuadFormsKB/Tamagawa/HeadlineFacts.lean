/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.SiegelSpaceChars
import QuadFormsKB.Tamagawa.SiegelRank3Frame
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

/-!
# The side conditions of the headline statements

The headline formulas (`Challenge.lean`) are written with `∑ᶠ` (zero over an infinite set), `Nat.card` (zero for an
infinite type), `∏'` (one for a non-multipliable product) and `LOne` (a `limUnder`, junk if the limit does not exist).
This file collects, in the form used by the headlines, the facts that rule out these default values:

* `finite_autLatV_and_repSet`: every lattice $M$ in the genus of $L$ has finite $O(M)$ and finitely many
  $x \in M$ with $q(x) = t$;
* `multipliable_intrinsicBetaV` (rank $\ge 4$), `multipliable_intrinsicBetaV_rankOne` (rank $1$): the Euler products of
  the classical densities converge unconditionally;
* `regFacts_spaceChar3`, `regFacts_spaceChar3V`, `regFacts_spaceChar2`, `regFacts_spaceChar2V` (ranks $3$, $2$):
  $L_F(1, \chi) = \lim_{s \to 1^+} L_F(s, \chi)$ exists and is positive, and the corrected product inside `regProd`
  converges unconditionally;
* `finite_orbits_SO`, `finite_stabilizer_SO`: the $SO$ double coset space in `tauSO` is finite, with finite stabilizers.
-/

open NumberField IsDedekindDomain Module Filter MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.SiegelSpace

open QuadFormsKB.Lattices QuadFormsKB.NFEuler QuadFormsKB.RegProd QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F]

/-! ### Finite automorphism groups and representation sets in the genus -/

section Genus

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
  [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **Every lattice in the genus has finite $O(M)$ and finite representation sets** (totally positive definite $q$,
$L$ integral): transported from `finite_autLat` and `finite_repSet` in the coordinates of `finBasis`. -/
theorem finite_autLatV_and_repSet (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) (t : F)
    (M : Submodule (𝓞 F) V) [M.IsLattice F] (hM : SameGenusV q L M) :
    Finite (autLatV q M) ∧ Finite {x : V // x ∈ M ∧ q x = t} := by
  set e := finBasis F V
  have hpd := isTotallyPosDef_coordForm hq e
  have hMi : IsIntegral (coordForm q e) (coordLat e M).1 :=
    SameGenus.isIntegral _ (isIntegral_coordLat hLi e) ((sameGenusV_iff_coord e L M).mp hM)
  constructor
  · have : Finite (autLat (coordForm q e) (coordLatSub e M)) := finite_autLat hpd (coordLat e M).2 hMi
    apply Nat.finite_of_card_ne_zero
    rw [card_autLatV_eq_coord e M]
    exact Nat.card_pos.ne'
  · have := finite_repSet hpd (coordLat e M).2 hMi t
    refine Finite.of_injective (β := {v : Fin _ → F // v ∈ (coordLat e M).1 ∧ (coordForm q e).eval v = t})
      (fun x => ⟨e.equivFun x.1, ⟨x.1, x.2.1, rfl⟩, (coordForm_hφ q e x.1).symm.trans x.2.2⟩) ?_
    intro x y h
    exact Subtype.ext (e.equivFun.injective (congrArg Subtype.val h))

end Genus

/-! ### Convergence of the Euler products -/

section Products

variable [IsTotallyReal F] {N : ℕ}

/-- Splitting off the finitely supported factor `locIndex` preserves multipliability. -/
theorem multipliable_of_locIndex_mul (L : Lat F N) {g : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : Multipliable fun v => locIndex v L * g v) : Multipliable g := by
  have hg : Multipliable fun v => (locIndex v L)⁻¹ :=
    multipliable_of_ne_finset_one fun v hv => by rw [locIndex_eq_one_of_notMem L hv, inv_one]
  exact (h.mul hg).congr fun v => by field_simp [(locIndex_pos v L).ne']

variable {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
  [FiniteDimensional F V] {q : QuadraticForm F V} {L : Submodule (𝓞 F) V} [L.IsLattice F]

/-- **$\prod_\mathfrak p \beta_\mathfrak p(L, m)$ converges unconditionally, $\dim V \ge 4$.** -/
theorem multipliable_intrinsicBetaV (hN : 4 ≤ finrank F V) (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => intrinsicBetaV v q L m := by
  obtain ⟨n, hn⟩ : ∃ n, finrank F V = n + 1 := ⟨finrank F V - 1, by omega⟩
  set e := finBasisOfFinrankEq F V hn
  have hLi' := isIntegral_coordLat hLi e
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi₀⟩ := exists_coords _ (isTotallyPosDef_coordForm hq e) _ hLi'
  have hβ := multipliable_latBeta (by omega) Q₀ hpd₀ _ hLi₀ hm
  have hmul : Multipliable fun v => spaceBeta v (coordForm q e) (coordLat e L) m := by
    rw [spaceBeta_fun_eq _ _ hLi' γ Q₀ hγ]; exact hβ.mul (hasProd_norm_det γ).multipliable
  simp_rw [spaceBeta_eq_locIndex_mul] at hmul
  simpa only [intrinsicBetaV_eq_basis _ q L e] using multipliable_of_locIndex_mul _ hmul

/-- **$\prod_\mathfrak p \beta_\mathfrak p(L, m)/2$ converges unconditionally, $\dim V = 1$.** -/
theorem multipliable_intrinsicBetaV_rankOne (h : finrank F V = 1) (hq : IsTotallyPosDefV q)
    (hLi : IsIntegralLattice q L) {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    Multipliable fun v => intrinsicBetaV v q L m / 2 := by
  set e := finBasisOfFinrankEq F V h
  have hLi' := isIntegral_coordLat hLi e
  obtain ⟨γ, Q₀, hγ, hpd₀, hLi₀⟩ := exists_coords (n := 0) _ (isTotallyPosDef_coordForm hq e) _ hLi'
  have hβ := multipliable_latBeta_rankOne Q₀ hpd₀ _ hLi₀ hm
  have hmul : Multipliable fun v => locIndex v (coordLat e L) * (intrinsicBeta v (coordForm q e) (coordLat e L) m / 2) :=
    (hβ.mul (hasProd_norm_det γ).multipliable).congr fun v => by
      rw [← mul_div_assoc, ← spaceBeta_eq_locIndex_mul, spaceBeta_eq v _ _ hLi' γ Q₀ hγ]; ring
  simpa only [intrinsicBetaV_eq_basis _ q L e] using multipliable_of_locIndex_mul _ hmul

/-! ### The regularized products: $L_F(1, \chi)$ exists and is positive, the corrected product converges -/

/-- **The three facts behind `regProd χ e f`** pass along a change of $\chi$ off a finite set. -/
theorem regFacts_congr {χ χ₀ f : HeightOneSpectrum (𝓞 F) → ℝ} (hχ : ∀ v, |χ v| ≤ 1) (hχ₀ : ∀ v, |χ₀ v| ≤ 1)
    (h : ∀ᶠ v in cofinite, χ₀ v = χ v) (e : ℤ)
    (H : HasLOne χ₀ (LOne χ₀) ∧ 0 < LOne χ₀ ∧ Multipliable fun v => f v * (1 - χ₀ v / (normP v : ℝ)) ^ e) :
    HasLOne χ (LOne χ) ∧ 0 < LOne χ ∧ Multipliable fun v => f v * (1 - χ v / (normP v : ℝ)) ^ e := by
  have hfin := eventually_cofinite.mp h
  have hS : ∀ v ∉ hfin.toFinset, χ v = χ₀ v := fun v hv => by
    by_contra hc; exact hv (hfin.mem_toFinset.mpr fun h' => hc h'.symm)
  have h' := H.1.congr_finite hχ hχ₀ hfin.toFinset hS
  refine ⟨by rw [h'.lOne_eq]; exact h', lOne_pos_of_congr hχ hχ₀ _ hS H.2.1 H.1, ?_⟩
  exact (multipliable_corr_transfer hχ₀ _ hS e H.2.2 multipliable_one).congr fun v => by rw [mul_one]

/-- $L_F(1, \chi_m) > 0$ for the coordinate ternary character. -/
theorem lOne_spaceChar3_pos (Q : QuadForm F 3) (hpd : IsTotallyPosDef Q) (L : Lat F 3) (hLi : IsIntegral Q L.1)
    {m : 𝓞 F} (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    0 < LOne (spaceChar3 Q m) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 2) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hfin := eventually_cofinite.mp (eventually_chiTern_eq Q γ Q₀ hγ hQ₀ (ne_zero_of_totallyPos hm))
  exact lOne_pos_of_congr (fun v => abs_sqChar_le v _) (fun v => abs_chiTern_le v Q₀ m) hfin.toFinset
    (fun v hv => by by_contra hc; exact hv (hfin.mem_toFinset.mpr fun h => hc h.symm))
    (lOne_chiTern_pos hpd₀ hm).1 (lOne_chiTern_pos hpd₀ hm).2

/-- $L_F(1, \chi_Q) > 0$ for the coordinate binary character. -/
theorem lOne_spaceChar2_pos (Q : QuadForm F 2) (hpd : IsTotallyPosDef Q) (L : Lat F 2) (hLi : IsIntegral Q L.1) :
    0 < LOne (spaceChar2 Q) := by
  obtain ⟨γ, Q₀, hγ, hpd₀, -⟩ := exists_coords (n := 1) Q hpd L hLi
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_of_isTotallyPosDef hpd₀
  have hfin := eventually_cofinite.mp (eventually_chiP_eq Q γ Q₀ hγ hQ₀)
  exact lOne_pos_of_congr (fun v => abs_sqChar_le v _) (fun v => abs_chiP_le Q₀ v) hfin.toFinset
    (fun v hv => by by_contra hc; exact hv (hfin.mem_toFinset.mpr fun h => hc h.symm))
    (lOne_chiP_binary hpd₀).1 (lOne_chiP_binary hpd₀).2

/-- **Rank 3, character in a basis $e$:** $L_F(1, \chi_m)$ exists and is positive, and
$\prod_\mathfrak p \beta_\mathfrak p(L, m)(1 - \chi_m(\mathfrak p)/N\mathfrak p)$ converges unconditionally. -/
theorem regFacts_spaceChar3 (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) (e : Basis (Fin 3) F V) :
    HasLOne (spaceChar3 (coordForm q e) m) (LOne (spaceChar3 (coordForm q e) m)) ∧
      0 < LOne (spaceChar3 (coordForm q e) m) ∧
      Multipliable fun v => intrinsicBetaV v q L m * (1 - spaceChar3 (coordForm q e) m v / (normP v : ℝ)) ^ (1 : ℤ) := by
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  refine ⟨hasLOne_spaceChar3 _ hpd _ hLi' hm, lOne_spaceChar3_pos _ hpd _ hLi' hm, ?_⟩
  simp only [intrinsicBetaV_eq_basis _ q L e]
  exact multipliable_intrinsicBeta_of_spaceBeta _ _ _ _ _ (multipliable_spaceBeta_chiTern _ hpd _ hLi' hm)

/-- **Rank 3, basis-free character** (as `regFacts_spaceChar3`). -/
theorem regFacts_spaceChar3V (h : finrank F V = 3) (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    HasLOne (spaceChar3V q m) (LOne (spaceChar3V q m)) ∧ 0 < LOne (spaceChar3V q m) ∧
      Multipliable fun v => intrinsicBetaV v q L m * (1 - spaceChar3V q m v / (normP v : ℝ)) ^ (1 : ℤ) :=
  regFacts_congr (abs_spaceChar3V_le q m) (fun v => abs_sqChar_le v _)
    (eventually_spaceChar3_eq_V q (finBasisOfFinrankEq F V h) m) 1
    (regFacts_spaceChar3 hq hLi hm (finBasisOfFinrankEq F V h))

/-- **Rank 2, character in a basis $e$:** $L_F(1, \chi_Q)$ exists and is positive, and
$\prod_\mathfrak p \beta_\mathfrak p(L, m)(1 - \chi_Q(\mathfrak p)/N\mathfrak p)^{-1}$ converges unconditionally. -/
theorem regFacts_spaceChar2 (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) (e : Basis (Fin 2) F V) :
    HasLOne (spaceChar2 (coordForm q e)) (LOne (spaceChar2 (coordForm q e))) ∧
      0 < LOne (spaceChar2 (coordForm q e)) ∧
      Multipliable fun v => intrinsicBetaV v q L m * (1 - spaceChar2 (coordForm q e) v / (normP v : ℝ)) ^ (-1 : ℤ) := by
  have hpd := isTotallyPosDef_coordForm hq e
  have hLi' := isIntegral_coordLat hLi e
  refine ⟨hasLOne_spaceChar2 _ hpd _ hLi', lOne_spaceChar2_pos _ hpd _ hLi', ?_⟩
  simp only [intrinsicBetaV_eq_basis _ q L e]
  exact multipliable_intrinsicBeta_of_spaceBeta _ _ _ _ _ (multipliable_spaceBeta_chiP _ hpd _ hLi' hm)

/-- **Rank 2, basis-free character** (as `regFacts_spaceChar2`). -/
theorem regFacts_spaceChar2V (h : finrank F V = 2) (hq : IsTotallyPosDefV q) (hLi : IsIntegralLattice q L) {m : 𝓞 F}
    (hm : ∀ v : InfinitePlace F, 0 < realEmb F v (algebraMap (𝓞 F) F m)) :
    HasLOne (spaceChar2V q) (LOne (spaceChar2V q)) ∧ 0 < LOne (spaceChar2V q) ∧
      Multipliable fun v => intrinsicBetaV v q L m * (1 - spaceChar2V q v / (normP v : ℝ)) ^ (-1 : ℤ) :=
  regFacts_congr (abs_spaceChar2V_le q) (fun v => abs_sqChar_le v _)
    (eventually_spaceChar2_eq_V q (finBasisOfFinrankEq F V h)) (-1)
    (regFacts_spaceChar2 hq hLi hm (finBasisOfFinrankEq F V h))

end Products

end QuadFormsKB.Tamagawa.SiegelSpace

namespace QuadFormsKB.Tamagawa

open QuadFormsKB.Lattices

/-! ### The $SO$ double coset space in `tauSO` is finite, with finite stabilizers -/

section Orbits

/-- **A subgroup of finite index has finitely many orbits** when the group does: the orbits of $H'$ inside the orbit
of $x$ are the classes of $h^{-1}x$, $h$ running over $H/H'$. -/
theorem finite_orbits_of_finiteIndex {H X : Type*} [Group H] [MulAction H X] (H' : Subgroup H) [H'.FiniteIndex]
    [Finite (orbitRel.Quotient H X)] : Finite (orbitRel.Quotient H' X) := by
  let f : orbitRel.Quotient H X × (H ⧸ H') → orbitRel.Quotient H' X := fun p =>
    Quotient.liftOn' p.2 (fun h => (Quotient.mk'' (h⁻¹ • p.1.out) : orbitRel.Quotient H' X)) fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab
      refine Quotient.sound' (orbitRel_apply.mpr ⟨⟨a⁻¹ * b, hab⟩, ?_⟩)
      show (a⁻¹ * b) • b⁻¹ • p.1.out = a⁻¹ • p.1.out
      rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one]
  refine Finite.of_surjective f fun ω' => ?_
  induction ω' using Quotient.inductionOn' with | h x => ?_
  obtain ⟨g, hg⟩ := orbitRel_apply.mp
    (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' x : orbitRel.Quotient H X)))
  refine ⟨(Quotient.mk'' x, QuotientGroup.mk g), ?_⟩
  show (Quotient.mk'' (g⁻¹ • (Quotient.mk'' x : orbitRel.Quotient H X).out) : orbitRel.Quotient H' X) = _
  rw [← hg, inv_smul_smul]

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- The inclusion $SO(V)(\mathbb A_f)/K^0 \to O(V)(\mathbb A_f)/K$. -/
def soQuotMap (Q : QuadForm F n) (L : Lat F n) :
    soAf Q ⧸ (locStab Q L).subgroupOf (soAf Q) → OAf Q ⧸ locStab Q L :=
  Quotient.map' (fun g : soAf Q => (g : OAf Q)) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact Subgroup.mem_subgroupOf.mp hab

theorem soQuotMap_injective (Q : QuadForm F n) (L : Lat F n) : Function.Injective (soQuotMap Q L) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  change (QuotientGroup.mk (a : OAf Q) : OAf Q ⧸ locStab Q L) = QuotientGroup.mk (b : OAf Q) at hab
  rw [QuotientGroup.eq] at hab
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simpa using hab

theorem soQuotMap_smul (Q : QuadForm F n) (L : Lat F n) (γ : (ratPoints Q).subgroupOf (soAf Q))
    (y : soAf Q ⧸ (locStab Q L).subgroupOf (soAf Q)) :
    soQuotMap Q L (γ • y) = ((γ : soAf Q) : OAf Q) • soQuotMap Q L y := by
  induction y using QuotientGroup.induction_on with | H a => rfl

/-- **Finitely many $SO$ double cosets** $SO(V)(F)\backslash SO(V)(\mathbb A_f)/SO(\hat L)$, $L = \mathcal O_F^n$
(nondegenerate $Q_0$, totally positive definite over $F$, $n \ge 1$). -/
theorem finite_orbits_SO (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hn : 0 < n)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) :
    Finite (orbitRel.Quotient ((ratPoints (Q₀.map (algebraMap (𝓞 F) F))).subgroupOf (soAf (Q₀.map (algebraMap (𝓞 F) F))))
      (soAf (Q₀.map (algebraMap (𝓞 F) F)) ⧸
        (locStab (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F n)).subgroupOf (soAf (Q₀.map (algebraMap (𝓞 F) F))))) := by
  set Q := Q₀.map (algebraMap (𝓞 F) F)
  set Γ' := (soAf Q).subgroupOf (ratPoints Q)
  have : Γ'.FiniteIndex := ⟨by rw [index_soAf_ratPoints Q₀ hQ hn]; norm_num⟩
  have := finite_orbits hpd (stdLat F n) (LatChange.isIntegral_std Q₀)
  have : Finite (orbitRel.Quotient Γ' (OAf Q ⧸ locStab Q (stdLat F n))) := finite_orbits_of_finiteIndex Γ'
  refine finite_orbits_of_map (H₂ := Γ') (soQuotMap Q (stdLat F n)) fun a b ⟨γ, hγ⟩ => ?_
  refine ⟨⟨⟨((γ : ratPoints Q) : OAf Q), Subgroup.mem_subgroupOf.mp γ.2⟩, by simp [Subgroup.mem_subgroupOf]⟩, ?_⟩
  apply soQuotMap_injective
  rw [soQuotMap_smul]
  exact hγ

/-- **Finite $SO$ stabilizers** $SO(V)(F) \cap \alpha K^0\alpha^{-1}$, inside the finite $O$ stabilizers. -/
theorem finite_stabilizer_SO {Q : QuadForm F n} (hpd : IsTotallyPosDef Q) (L : Lat F n) (hLi : IsIntegral Q L.1)
    (x : soAf Q ⧸ (locStab Q L).subgroupOf (soAf Q)) :
    Finite (stabilizer ((ratPoints Q).subgroupOf (soAf Q)) x) := by
  have hfin := finite_stabilizer hpd L hLi (soQuotMap Q L x)
  refine Finite.of_injective (β := stabilizer (ratPoints Q) (soQuotMap Q L x))
    (fun γ => ⟨⟨((γ.1 : soAf Q) : OAf Q), Subgroup.mem_subgroupOf.mp γ.1.2⟩, ?_⟩) ?_
  · rw [mem_stabilizer_iff]
    have h := congrArg (soQuotMap Q L) (mem_stabilizer_iff.mp γ.2)
    rw [soQuotMap_smul] at h
    exact h
  · intro γ γ' h
    have h' := congrArg (fun g => ((g.1 : ratPoints Q) : OAf Q)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext h'))

end Orbits

end QuadFormsKB.Tamagawa
