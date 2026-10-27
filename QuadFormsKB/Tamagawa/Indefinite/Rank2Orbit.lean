/-
# Weil's measure of the integral adelic frames with convergence factors on the stabilizer

**Layer:** number fields, adeles. Frame coordinates `D : FrameTower Q₀ hQ n' (cols Ξ.1)`, $N = r + n'\ge3$, $n'\ge1$, and
convergence factors $\lambda_v>0$ for the stabilizer $H = SO(Q'')$ such that $\prod_v\lambda_v^{-1}\alpha_v(L'')$ converges
absolutely to a nonzero value (for binary anisotropic $Q''$: $\lambda_v = L_v(1,\chi)^{-1}$). This is `frameOrbitSum_eq`
(`FrameDensities.lean`, $\lambda = 1$, $n'\ge3$) with the stabilizer measure `muFin Q'' λ`:
$$\sum_O\frac{\mu_f(SO(\hat L))}{\mu^\lambda_{H,f}(K_O)} = \prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,
  \frac{|\det g|_\mathfrak p^{\,n'+1}}{|\det H_{T_0}|_\mathfrak p^{\,n'}}\,\lambda_\mathfrak p\qquad(\texttt{frameOrbitSum\_lam}),$$
the product converging absolutely (`hasProd_frameLocFactor_lam`).
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameDensities

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.Tamagawa.Measure.ConeFinite

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)
  (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hlam : ∀ v, 0 < lam v)
  (hmult : Multipliable fun v => (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal)
  (hpos : 0 < ∏' v, (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal)

/-- **The orbit sum with the stabilizer measure `muFin Q'' λ`**:
$\sum_O\mu_f(SO(\hat L))/\mu^\lambda_{H,f}(K_O)$. -/
def frameOrbitSumLam : ℝ≥0∞ :=
  ∑' O : FinOrbit Q₀ T₀ Ξ, muFin Q₀ (fun _ => 1) (KSO Q₀) /
    muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O))

section LamHelpers

local notation "fr" => towerAdapted Q₀ hQ T₀ Ξ D hT
local notation "Bad" => towerBad Q₀ hQ T₀ Ξ D hT
set_option quotPrecheck false in
local notation "aL " v:max => (muLocSO v D.Q'' (lam v) (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal

theorem muLocSO_eq_ofReal_smul {m : ℕ} (Q : QuadForm (𝓞 F) m) (v : HeightOneSpectrum (𝓞 F)) {l : ℝ}
    (hl : 0 < l) : muLocSO v Q l = ENNReal.ofReal l⁻¹ • muLocSO v Q 1 := by
  have h : Real.toNNReal (NF.siegelDensity v Q Q / l) =
      Real.toNNReal l⁻¹ * Real.toNNReal (NF.siegelDensity v Q Q / 1) := by
    rw [← Real.toNNReal_mul (inv_nonneg.2 hl.le), div_one, inv_mul_eq_div]
  unfold muLocSO haarNorm
  rw [h, mul_smul]
  rfl

theorem muLocSO_apply_lam {m : ℕ} (Q : QuadForm (𝓞 F) m) (v : HeightOneSpectrum (𝓞 F)) {l : ℝ}
    (hl : 0 < l) (S : Set (SOv v Q)) : muLocSO v Q l S = ENNReal.ofReal l⁻¹ * muLocSO v Q 1 S := by
  rw [muLocSO_eq_ofReal_smul Q v hl, Measure.smul_apply, smul_eq_mul]

theorem ennreal_div_ofReal_inv_mul (A M : ℝ≥0∞) {l : ℝ} (hl : 0 < l) :
    A / (ENNReal.ofReal l⁻¹ * M) = ENNReal.ofReal l * (A / M) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hl,
    ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top))
      (Or.inl (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hl).ne')), inv_inv]
  ring

theorem toReal_muLocSO_soStab_lam {m : ℕ} (Q : QuadForm (𝓞 F) m) (hQ : Q.Nondegenerate)
    (v : HeightOneSpectrum (𝓞 F)) {l : ℝ} (hl : 0 < l) :
    (muLocSO v Q l (soStabSO v Q : Set (SOv v Q))).toReal = aSO Q v / l := by
  have hd := siegelDensity_self_pos' Q hQ v
  rw [aSO, muLocSO_soStabSO, muLocSO_soStabSO, ENNReal.toReal_ofReal (div_pos hd hl).le,
    ENNReal.toReal_ofReal (by rw [div_one]; exact hd.le), div_one]

/-- Right invariance of `muFin Q lam` for arbitrary convergence factors. -/
theorem isMulRightInvariant_muFin_lam {m : ℕ} (Q : QuadForm (𝓞 F) m)
    (lam : HeightOneSpectrum (𝓞 F) → ℝ) (hQ : Q.Nondegenerate) (hn : 0 < m) :
    (QuadFormsKB.Tamagawa.Measure.muFin Q lam).IsMulRightInvariant := by
  classical
  by_cases hc : Real.toNNReal (finFactor Q lam) = 0
  · have h0 : QuadFormsKB.Tamagawa.Measure.muFin Q lam = 0 := by
      unfold QuadFormsKB.Tamagawa.Measure.muFin haarNorm; rw [hc]; simp
    rw [h0]
    exact ⟨fun g => MeasureTheory.Measure.map_zero _⟩
  · have : (QuadFormsKB.Tamagawa.Measure.muFin Q lam).IsHaarMeasure := by
      unfold QuadFormsKB.Tamagawa.Measure.muFin haarNorm; exact MeasureTheory.Measure.IsHaarMeasure.nnreal_smul _ hc
    refine Weil.isMulRightInvariant_of_conj _ (KSO Q : Set (SOAf Q)) (isCompact_KSO Q) ⟨1, ?_⟩ ?_
    · rw [(isOpen_KSO Q).interior_eq]; exact (KSO Q).one_mem
    intro g
    have hev : ∀ᶠ v in Filter.cofinite, evalSO Q v g ∈ soStabSO v Q := by
      have := (g : OAf (Q.map (algebraMap (𝓞 F) F))).2
      filter_upwards [this] with v hv
      exact hv
    set S := (Filter.eventually_cofinite.mp hev).toFinset with hS
    have hgK : ∀ v, v ∉ S → evalSO Q v g ∈ soStabSO v Q := by
      intro v hv
      have : v ∉ {v | ¬ evalSO Q v g ∈ soStabSO v Q} := by
        simpa [hS] using hv
      simpa using this
    set U : ∀ v, Set (SOv v Q) := fun v => {y | evalSO Q v g * y * (evalSO Q v g)⁻¹ ∈ soStabSO v Q} with hU
    have key : ∀ x : SOAf Q, (g * x * g⁻¹ ∈ KSO Q) ↔
        ∀ v, evalSO Q v g * evalSO Q v x * (evalSO Q v g)⁻¹ ∈ soStabSO v Q := by
      intro x
      rw [mem_KSO_iff]
      simp only [map_mul, map_inv, SetLike.mem_coe]
    have hbox : {x | g * x * g⁻¹ ∈ (KSO Q : Set (SOAf Q))} = boxSO Q S U := by
      ext x
      show g * x * g⁻¹ ∈ KSO Q ↔ _
      rw [key]
      simp only [boxSO, hU, Set.mem_ofPred_eq, SetLike.mem_coe]
      constructor
      · intro hx
        refine ⟨fun v _ => hx v, fun v hv => ?_⟩
        have hg := hgK v hv
        have := (soStabSO v Q).mul_mem ((soStabSO v Q).mul_mem ((soStabSO v Q).inv_mem hg) (hx v)) hg
        simpa [mul_assoc] using this
      · rintro ⟨h1, h2⟩ v
        by_cases hv : v ∈ S
        · exact h1 v hv
        · have hg := hgK v hv
          exact (soStabSO v Q).mul_mem ((soStabSO v Q).mul_mem hg (h2 v hv)) ((soStabSO v Q).inv_mem hg)
    have hUm : ∀ v ∈ S, MeasurableSet (U v) := by
      intro v _
      refine IsOpen.measurableSet ?_
      exact (isOpen_soStabSO v Q).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    have hone : ∀ v ∈ S, haarSO Q v (U v) = 1 := by
      intro v _
      haveI := Weil.isMulRightInvariant_muLocSO v Q hQ hn
      haveI : (muLocSO v Q 1).IsMulLeftInvariant := by unfold muLocSO; infer_instance
      rw [haarSO_eq_div Q hQ v one_pos]
      have hconj := Weil.measure_conj_set_eq (muLocSO v Q 1) (evalSO Q v g) (soStabSO v Q : Set (SOv v Q))
      have : muLocSO v Q 1 (U v) = muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q)) := hconj
      rw [this]
      exact ENNReal.div_self (muLocSO_soStabSO_pos Q hQ v one_pos)
        (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
    rw [hbox, QuadFormsKB.Tamagawa.Measure.muFin_boxSO_haar Q _ S U hUm, Finset.prod_eq_one hone, mul_one,
      muFin_KSO]

include hlam hmult hpos in
theorem muFin_orbitStab_congr_lam (hn' : 1 ≤ n') (b b' : IntFr Q₀ T₀ Ξ)
    (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b'.1) = muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) b.1) := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := stab_iotaB (stabIn_frameCprod Q₀ hQ T₀ Ξ D) _ hfix
  have hb' : b'.1 = k * b.1 * D.ιFin a := by rw [ha]; group
  have := isMulRightInvariant_muFin_lam D.Q'' lam D.hQ'' (by omega)
  rw [hb', orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]

open Classical in
include hlam hmult hpos in
theorem tprod_ite_aL_pos : 0 < ∏' v, if v ∈ Bad then 1 else aL v := by
  classical
  have ha0 : ∀ v, 0 < aL v := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos D.Q'' D.hQ'' v (hlam v))
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have h := tprod_eq_prod_mul_tprod_ite (fun v => aL v) hmult Bad (fun v _ => (ha0 v).ne')
  have hp := hpos
  rw [show (∏' v, aL v) = _ from h] at hp
  convert pos_of_mul_pos_right hp (Finset.prod_nonneg fun v _ => (ha0 v).le)

open Classical in
include hlam hmult hpos in
/-- **One orbit term with the convergence factors**. -/
theorem orbit_term_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') (O : FinOrbit Q₀ T₀ Ξ) :
    muFin Q₀ (fun _ => 1) (KSO Q₀) /
        muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) =
      (∏ v ∈ Bad, ENNReal.ofReal (lam v) * (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
          muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q')))) *
        ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v) := by
  obtain ⟨b', hrel, hgood⟩ := exists_goodRep Q₀ hQ T₀ Ξ D hT hn' (Quotient.out O)
  have hO : O = Quotient.mk _ b' := by
    conv_lhs => rw [← Quotient.out_eq O]
    exact Quotient.sound hrel
  show _ / muFin D.Q'' lam (orbitStab D.ιFin (KSO Q₀) (Quotient.out O).1) = _
  rw [← muFin_orbitStab_congr_lam Q₀ hQ T₀ Ξ D lam hlam hmult hpos hn' _ _ hrel,
    orbitStab_eq_boxSO Q₀ hQ T₀ Ξ D hT b'.1 hgood]
  have hU : ∀ v ∈ Bad, MeasurableSet
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) :=
    fun v _ => (isOpen_orbitStab_loc v Q₀ T₀ fr _).measurableSet
  rw [muFin_boxSO_split D.Q'' D.hQ'' hlam hmult Bad _ hU]
  rw [muFin_KSO, finFactor_one Q₀ hQ, ← finFactor_one Q₀ hQ]
  have hKa : ENNReal.ofReal (finFactor Q₀ fun _ => 1) =
      (∏ v ∈ Bad, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀))) *
        ENNReal.ofReal (∏' v, if v ∈ Bad then 1 else aSO Q₀ v) := by
    rw [finFactor, show (fun v => (muLocSO v Q₀ ((fun _ => (1 : ℝ)) v) (soStabSO v Q₀ : Set (SOv v Q₀))).toReal) =
      aSO Q₀ from rfl, tprod_eq_prod_mul_tprod_ite (aSO Q₀) (multipliable_aSO hN Q₀ hQ) Bad
        (fun v _ => (aSO_pos Q₀ hQ v).ne'),
      ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => (aSO_pos Q₀ hQ v).le),
      ENNReal.ofReal_prod_of_nonneg fun v _ => (aSO_pos Q₀ hQ v).le]
    simp only [ofReal_aSO]
  rw [hKa]
  have hposL := tprod_ite_aL_pos Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos
  have hloc : ∀ v ∈ Bad, muLocSO v D.Q'' 1
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) =
      muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q')) := by
    intro v _
    rw [hO, finToLoc_eq]
    exact muLocSO_orbitStab_eq v Q₀ T₀ fr hT D.hQ'' hn' _ _ rfl
  have hU0 : ∀ v ∈ Bad, muLocSO v D.Q'' (lam v)
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) ≠ 0 := by
    intro v _
    have := isHaarMeasure_muLocSO v (fr).Q' D.hQ''
    rw [muLocSO_apply_lam D.Q'' v (hlam v)]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (inv_pos.2 (hlam v))).ne'
      ((isOpen_orbitStab_loc v Q₀ T₀ fr _).measure_pos _ ⟨1, Subgroup.one_mem _⟩).ne'
  rw [ennreal_prod_div _ _ _ hU0 _ _ hposL]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun v hv => ?_) rfl
  rw [muLocSO_apply_lam D.Q'' v (hlam v), ennreal_div_ofReal_inv_mul _ _ (hlam v), hloc v hv]

open Classical in
theorem tsum_prod_finToLoc (hn' : 1 ≤ n') :
    ∑' O : FinOrbit Q₀ T₀ Ξ, ∏ v ∈ Bad, (muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
          muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q'))) =
      ∏ v ∈ Bad, locOrbitSum v Q₀ T₀ fr := by
  set e := Equiv.ofBijective _ (finOrbitMap_bijective Q₀ hQ T₀ Ξ D hT hn')
  have : ∀ v : Bad, Fintype (LocOrbit v.1 Q₀ T₀ fr) := fun v =>
    @Fintype.ofFinite _ (finite_locOrbit v.1 Q₀ T₀ fr hQ hT hn')
  set w : ∀ v : HeightOneSpectrum (𝓞 F), LocOrbit v Q₀ T₀ fr → ℝ≥0∞ := fun v o =>
    muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) / muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v (fr).Q'))
    with hw
  have h1 : ∀ O : FinOrbit Q₀ T₀ Ξ, (∏ v ∈ Bad, w v (finToLoc Q₀ hQ T₀ Ξ D hT O v)) =
      ∏ v : Bad, w v.1 (e O v) := fun O => (Finset.prod_coe_sort Bad _).symm
  rw [tsum_congr h1, e.tsum_eq (f := fun x => ∏ v : Bad, w v.1 (x v)), tsum_fintype, ← Fintype.prod_sum,
    ← Finset.prod_coe_sort Bad]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [locOrbitSum, tsum_fintype]

open Classical in
include hlam hmult hpos in
theorem frameOrbitSumLam_eq_prod (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    frameOrbitSumLam Q₀ hQ T₀ Ξ D lam = (∏ v ∈ Bad, ENNReal.ofReal (lam v) * locOrbitSum v Q₀ T₀ fr) *
      ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v) := by
  unfold frameOrbitSumLam
  rw [tsum_congr (orbit_term_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN), ENNReal.tsum_mul_right]
  congr 1
  simp_rw [Finset.prod_mul_distrib]
  rw [ENNReal.tsum_mul_left, tsum_prod_finToLoc Q₀ hQ T₀ Ξ D hT hn']

open Classical in
include hlam hmult hpos in
theorem hasProd_frameLocFactor_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    HasProd (fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v)
      ((∏ v ∈ Bad, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) *
        ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aL v)) := by
  have ha0 : ∀ v, 0 < aL v := fun v =>
    ENNReal.toReal_pos (muLocSO_soStabSO_pos D.Q'' D.hQ'' v (hlam v))
      (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)
  have hA := multipliable_ite_one (aSO Q₀) (multipliable_aSO hN Q₀ hQ) Bad (fun v _ => (aSO_pos Q₀ hQ v).ne')
  have hB := multipliable_ite_one (fun v => aL v) hmult Bad (fun v _ => (ha0 v).ne')
  have hdiv := hA.hasProd.div₀ hB.hasProd (tprod_ite_aL_pos Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos).ne'
  have hg : (fun v => (if v ∈ Bad then 1 else aSO Q₀ v) / (if v ∈ Bad then 1 else aL v)) =
      fun v => if v ∈ Bad then 1 else frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v := by
    funext v
    by_cases hv : v ∈ Bad
    · simp [hv]
    · simp only [hv, ite_false]
      rw [frameLocFactor_good Q₀ hQ T₀ Ξ D hT hn' v hv, toReal_muLocSO_soStab_lam D.Q'' D.hQ'' v (hlam v)]
      have h1 := aSO_pos D.Q'' D.hQ'' v
      have h2 := hlam v
      field_simp
  rw [hg] at hdiv
  rw [← hdiv.tprod_eq]
  exact hasProd_prod_mul_tprod_ite _ Bad hdiv.multipliable

end LamHelpers

include hlam hmult hpos in
/-- The local factors with the convergence factors converge absolutely:
$\prod_\mathfrak p\beta_\mathfrak p|\det g|_\mathfrak p^{n'+1}|\det H_{T_0}|_\mathfrak p^{-n'}\lambda_\mathfrak p$. -/
theorem multipliable_frameLocFactor_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    Multipliable fun v => frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v :=
  (hasProd_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN).multipliable

include hlam hmult hpos in
/-- **Weil's measure of the integral adelic frames with convergence factors on the stabilizer.** -/
theorem frameOrbitSum_lam (hn' : 1 ≤ n') (hN : 3 ≤ r + n') :
    frameOrbitSumLam Q₀ hQ T₀ Ξ D lam = ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v * lam v) := by
  classical
  rw [(hasProd_frameLocFactor_lam Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN).tprod_eq,
    frameOrbitSumLam_eq_prod Q₀ hQ T₀ Ξ D hT lam hlam hmult hpos hn' hN,
    ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      mul_nonneg (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v) (hlam v).le),
    ENNReal.ofReal_prod_of_nonneg fun v _ =>
      mul_nonneg (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v) (hlam v).le]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ENNReal.ofReal_mul (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v),
    ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT hn' v, mul_comm]

end QuadFormsKB.Tamagawa.Indefinite
