/-
# Weil's measure of the integral adelic frames as a product of local densities

**Layer:** number fields, adeles. Frame coordinates `D : FrameTower Q₀ hQ n' Ξ` of a rational frame $\Xi$ of $T_0$ give the
adapted frame $g = [\Xi\mid C]$ (`towerAdapted`, $Q_0\circ g = T_0\perp Q''$) and $\iota(h) = g\,\mathrm{diag}(1_r,h)\,g^{-1}$ at every
finite place. This file proves
$$\texttt{frameOrbitSum} = \sum_O\frac{\mu_f(SO(\hat L))}{\mu_{H,f}(K_O)} = \prod_\mathfrak p\beta_\mathfrak p(L, T_0)\,
  \frac{|\det g|_\mathfrak p^{\,n'+1}}{|\det H_{T_0}|_\mathfrak p^{\,n'}}\qquad(\texttt{frameOrbitSum\_eq}):$$
* the $SO(\hat L)$-orbits $O$ of integral adelic frames are the families of local orbits at the finitely many exceptional places
  $B$ (`towerBad`; one orbit at every other place, `good_subsingleton`), `finOrbitEquiv`;
* every orbit has a representative $b$ with $b_v = 1$ for $v\notin B$ (`exists_goodRep`), the measure of $K_O$ does not depend
  on the representative (`muFin_orbitStab_congr`), and for such $b$ the group $K_O$ is the box with factors
  $K_{O,v}$ at $v\in B$ and $SO(L''_v)$ elsewhere (`orbitStab_eq_boxSO`), whose measure is a product (`muFin_boxSO_split`);
* each local factor is `locOrbitSum_eq`, and at $v\notin B$ the factor is $\mu_v(SO(L_v))/\mu''_v(SO(L''_v))$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameDensitiesAux
import QuadFormsKB.Tamagawa.Measure.ConeFiniteGroup

open MeasureTheory Set Matrix MulAction
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Frames LocalDensity
  QuadFormsKB.Tamagawa.Measure.ConeFinite

/-! ### Generic lemmas -/

section Generic

theorem mem_orbitStab' {B B' : Type*} [Group B] [Group B'] {ιB : B' →* B} {K : Subgroup B} {gO : B} {h : B'} :
    h ∈ orbitStab ιB K gO ↔ gO * ιB h * gO⁻¹ ∈ K := by
  simp [orbitStab, MulAut.conj_apply]

theorem orbitStab_mul_mul {B B' : Type*} [Group B] [Group B'] (ιB : B' →* B) (K : Subgroup B) (b k : B)
    (hk : k ∈ K) (a : B') :
    orbitStab ιB K (k * b * ιB a) = (orbitStab ιB K b).comap (MulAut.conj a).toMonoidHom := by
  ext h
  rw [Subgroup.mem_comap, mem_orbitStab', mem_orbitStab']
  have e : k * b * ιB a * ιB h * (k * b * ιB a)⁻¹ =
      k * (b * ιB ((MulAut.conj a).toMonoidHom h) * b⁻¹) * k⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    group
  rw [e]
  constructor
  · intro H
    have := K.mul_mem (K.mul_mem (K.inv_mem hk) H) hk
    simpa [mul_assoc] using this
  · intro H
    exact K.mul_mem (K.mul_mem hk H) (K.inv_mem hk)

theorem measure_comap_conj {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (U : Subgroup G) (a : G) :
    μ ((U.comap (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) = μ U := by
  have e : ((U.comap (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) =
      (fun h => h * a⁻¹) ⁻¹' ((fun h => a * h) ⁻¹' (U : Set G)) := by
    ext h
    simp [MulAut.conj_apply, mul_assoc]
  rw [e, measure_preimage_mul_right, measure_preimage_mul]

theorem multipliable_ite_one {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (ha : Multipliable a) (S : Finset ι)
    (hS : ∀ v ∈ S, a v ≠ 0) : Multipliable fun v => if v ∈ S then 1 else a v := by
  set c : ι → ℝ := fun v => if v ∈ S then (a v)⁻¹ else 1 with hc
  have hcm : Multipliable c :=
    (hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional ι) (s := S) (f := c) fun v hv => by simp [c, hv]).multipliable
  convert ha.mul hcm using 1
  ext v
  by_cases hv : v ∈ S
  · simp [c, hv, mul_inv_cancel₀ (hS v hv)]
  · simp [c, hv]

theorem hasProd_prod_mul_tprod_ite {ι : Type*} [DecidableEq ι] (a : ι → ℝ) (S : Finset ι)
    (h : Multipliable fun v => if v ∈ S then 1 else a v) :
    HasProd a ((∏ v ∈ S, a v) * ∏' v, if v ∈ S then 1 else a v) := by
  have h1 : HasProd (fun v => if v ∈ S then a v else 1) (∏ v ∈ S, a v) := by
    have := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional ι) (s := S) (f := fun v => if v ∈ S then a v else 1)
      (fun v hv => by simp [hv])
    rwa [Finset.prod_congr rfl fun v hv => (show (if v ∈ S then a v else 1) = a v by simp [hv])] at this
  convert h1.mul h.hasProd using 1
  ext v
  by_cases hv : v ∈ S <;> simp [hv]

theorem ennreal_prod_div {ι : Type*} (s : Finset ι) (A U : ι → ℝ≥0∞) (hU : ∀ i ∈ s, U i ≠ 0) (x y : ℝ)
    (hy : 0 < y) :
    ((∏ i ∈ s, A i) * ENNReal.ofReal x) / ((∏ i ∈ s, U i) * ENNReal.ofReal y) =
      (∏ i ∈ s, A i / U i) * ENNReal.ofReal (x / y) := by
  rw [ENNReal.ofReal_div_of_pos hy]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (ENNReal.ofReal_pos.2 hy).ne'),
    ENNReal.prod_inv_distrib (fun i hi j _ _ => Or.inl (hU i hi)), Finset.prod_mul_distrib]
  ring

end Generic

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

/-! ### Local lemmas -/

section Local

variable (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) (r + n')) (T₀ : QuadForm (𝓞 F) r)
  (fr : AdaptedFrameT (Q₀.map (algebraMap (𝓞 F) F)) (T₀.map (algebraMap (𝓞 F) F)))

theorem continuous_locIota : Continuous (locIota v Q₀ T₀ fr) :=
  Continuous.subtype_mk (Continuous.subtype_mk ((continuous_const.mul ((continuous_blockGLB v).comp
    (continuous_subtype_val.comp continuous_subtype_val))).mul continuous_const) _) _

theorem isOpen_orbitStab_loc (φ : SOv v Q₀) :
    IsOpen (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) := by
  have e : (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) =
      (fun h => φ * locIota v Q₀ T₀ fr h * φ⁻¹) ⁻¹' (soStabSO v Q₀ : Set (SOv v Q₀)) := by
    ext h
    exact mem_orbitStab'
  rw [e]
  exact (isOpen_soStabSO v Q₀).preimage
    ((continuous_const.mul (continuous_locIota v Q₀ T₀ fr)).mul continuous_const)

/-- The measure of $K_\varphi = \{h : \varphi\,\iota(h)\,\varphi^{-1}\in SO(L_v)\}$ depends only on the local orbit of
$\varphi\,\Xi$. -/
theorem muLocSO_orbitStab_eq (hT : T₀.Nondegenerate) (hQ' : (fr).Q'.Nondegenerate) (hn' : 1 ≤ n') (φ : SOv v Q₀)
    (y : locFrameSet v Q₀ T₀ fr) (hy : y.1 = soMat v φ * locBase v Q₀ T₀ fr) :
    muLocSO v (fr).Q' 1 (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) φ : Set (SOv v (fr).Q')) =
      muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (Quotient.mk _ y) : Set (SOv v (fr).Q')) := by
  set o : LocOrbit v Q₀ T₀ fr := Quotient.mk _ y
  obtain ⟨k, hk, hky⟩ := Quotient.mk_out (s := locOrbitSetoid v Q₀ T₀ fr) y
  have hrep : (Quotient.out o : locFrameSet v Q₀ T₀ fr).1 =
      soMat v (locOrbitRep v Q₀ T₀ fr o) * locBase v Q₀ T₀ fr := by
    rw [locOrbitRep_eq]; exact frPhi_spec v Q₀ T₀ fr _
  have hφ : soMat v φ * locBase v Q₀ T₀ fr = soMat v (k * locOrbitRep v Q₀ T₀ fr o) * locBase v Q₀ T₀ fr := by
    rw [← hy, hky, hrep, soMat_mul, Matrix.mul_assoc]
  obtain ⟨a, ha⟩ := Xi_stab v Q₀ T₀ fr hT _ _ hφ
  have := isHaarMeasure_muLocSO v (fr).Q' hQ'
  have := Weil.isMulRightInvariant_muLocSO v (fr).Q' hQ' hn'
  rw [ha, orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]
  rfl

theorem finite_locOrbit (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) (hn' : 1 ≤ n') :
    Finite (LocOrbit v Q₀ T₀ fr) := by
  have hQ' : (fr).Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  obtain ⟨ρ, -, hρdet⟩ := exists_stdStab_det_neg_one v (fr).Q' hQ' (by omega)
  have hQF' := nondegenerate_QF (fr).Q' hQ'
  have hH2 : (soSub ((fr).Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).index = 2 := by
    have := relIndex_soSub_eq_two _ hQF' ⊤ ρ (Subgroup.mem_top _) hρdet
    rwa [Subgroup.relIndex_top_right, inf_top_eq] at this
  have := finite_types v Q₀ T₀ fr hQ₀ hT
  have := Subgroup.finite_quotient_of_finite_quotient_of_index_ne_zero
    (X := LocFrameSetG v (T₀.map (algebraMap (𝓞 F) F)) ((fr).Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)))
    (H := soSub ((fr).Q'.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) (by rw [hH2]; norm_num)
  exact Finite.of_injective _ (ThQ_bijective v Q₀ T₀ fr hQ₀ hT (by omega)).1

include fr in
theorem localDensityForm_nonneg_of_frame (hQ₀ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate) :
    0 ≤ NF.localDensityForm v Q₀ T₀ := by
  have hQ' : (fr).Q'.Nondegenerate := adapted_nondegenerate Q₀ T₀ fr hQ₀
  have hid := frameLocalIdentityGen v Q₀ hQ₀ T₀ hT fr
  have hW : 0 ≤ locFrameTypeSumG v (T₀.map (algebraMap (𝓞 F) F)) ((fr).Q'.map (algebraMap (𝓞 F) F))
      (locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) fr.g)⁻¹ (std v)) :=
    finsum_nonneg fun t => locFrameWeightG_nonneg v Q₀ T₀ fr _
  have hβ₀ := LatChange.localDensityForm_self_pos v Q₀ hQ₀
  have hβ' := LatChange.localDensityForm_self_pos v (fr).Q' hQ'
  have hg : 0 < ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) := by
    have : fr.g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero
    exact pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 this)) _
  have hL : 0 ≤ NF.localDensityForm v (fr).Q' (fr).Q' * NF.localDensityForm v Q₀ T₀ *
      ‖algebraMap F (v.adicCompletion F) fr.g.val.det‖ ^ (n' + 1) := by
    rw [← hid]; positivity
  have h2 : 0 ≤ NF.localDensityForm v (fr).Q' (fr).Q' * NF.localDensityForm v Q₀ T₀ :=
    nonneg_of_mul_nonneg_left hL hg
  exact nonneg_of_mul_nonneg_right h2 hβ'

end Local

/-! ### The global objects -/

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1)) (hT : T₀.Nondegenerate)

local notation "fr" => towerAdapted Q₀ hQ T₀ Ξ D hT
local notation "Bad" => towerBad Q₀ hQ T₀ Ξ D hT

/-- The integral adelic frames in the orbit of $\Xi$. -/
abbrev IntFr : Type := {b : SOAf Q₀ // b • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r}

/-- Every orbit has a representative $b$ with $b_v = 1$ outside the exceptional places. -/
theorem exists_goodRep (hn' : 1 ≤ n') (b : IntFr Q₀ T₀ Ξ) :
    ∃ b' : IntFr Q₀ T₀ Ξ, (finOrbitSetoid Q₀ T₀ Ξ).r b b' ∧ ∀ v ∉ Bad, evalSO Q₀ v b'.1 = 1 := by
  classical
  obtain ⟨c, hcS, hcn⟩ := exists_SOAf_of_fam Q₀ Bad (fun v => evalSO Q₀ v b.1)
  have hS : ∀ v ∈ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locFr Q₀ hQ T₀ Ξ D hT v b.1 := fun v hv => by
    simp only [locFr, hcS v hv]
  have hN : ∀ v ∉ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locBase v Q₀ T₀ fr := fun v hv => by
    simp only [locFr, hcn v hv, soMat_one, Matrix.one_mul]
  have hint : c • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := by
    rw [mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT]
    intro v i j
    by_cases hv : v ∈ Bad
    · rw [hS v hv]; exact (mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT b.1).mp b.2 v i j
    · rw [hN v hv]; exact good_base_int Q₀ hQ T₀ Ξ D hT v hv i j
  refine ⟨⟨c, hint⟩, ?_, hcn⟩
  rw [finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT]
  intro v
  by_cases hv : v ∈ Bad
  · refine ⟨1, (soStabSO v Q₀).one_mem, ?_⟩
    show locFr Q₀ hQ T₀ Ξ D hT v c = soMat v 1 * locFr Q₀ hQ T₀ Ξ D hT v b.1
    rw [soMat_one, Matrix.one_mul, hS v hv]
  · have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
    exact Quotient.exact (Subsingleton.elim (Quotient.mk _ _) (Quotient.mk _ _))

/-- **The measure of $K_O$ does not depend on the representative of $O$.** -/
theorem muFin_orbitStab_congr (hn' : 1 ≤ n') (b b' : IntFr Q₀ T₀ Ξ) (h : (finOrbitSetoid Q₀ T₀ Ξ).r b b') :
    muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) b'.1) =
      muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) b.1) := by
  obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 h
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hfix : ((k * b.1)⁻¹ * b'.1) • ratFT Q₀ T₀ Ξ = ratFT Q₀ T₀ Ξ := by
    rw [mul_smul, ← hky, ← mul_smul k, inv_smul_smul]
  obtain ⟨a, ha⟩ := stab_iotaB (stabIn_frameCprod Q₀ hQ T₀ Ξ D) _ hfix
  have hb' : b'.1 = k * b.1 * D.ιFin a := by rw [ha]; group
  have := isMulRightInvariant_muFin D.Q'' D.hQ'' (by omega)
  rw [hb', orbitStab_mul_mul _ _ _ _ hk, measure_comap_conj]

/-- For a representative with $b_v = 1$ outside $B$, the orbit stabilizer $K_O$ is a box. -/
theorem orbitStab_eq_boxSO (b : SOAf Q₀) (hb : ∀ v ∉ Bad, evalSO Q₀ v b = 1) :
    (orbitStab D.ιFin (KSO Q₀) b : Set (SOAf D.Q'')) = boxSO D.Q'' Bad
      (fun v => ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q''))) := by
  ext h
  have e : ∀ v, evalSO Q₀ v (b * D.ιFin h * b⁻¹) =
      evalSO Q₀ v b * locIota v Q₀ T₀ fr (evalSO D.Q'' v h) * (evalSO Q₀ v b)⁻¹ := fun v => by
    rw [map_mul, map_mul, map_inv, evalSO_ιFin Q₀ hQ T₀ Ξ D hT]
  simp only [SetLike.mem_coe, mem_orbitStab', mem_KSO_iff, boxSO, Set.mem_ofPred_eq, e]
  constructor
  · intro H
    refine ⟨fun v _ => H v, fun v hv => ?_⟩
    have := H v
    rw [hb v hv, one_mul, inv_one, mul_one] at this
    exact (locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv _).mp this
  · rintro ⟨H1, H2⟩ v
    by_cases hv : v ∈ Bad
    · exact H1 v hv
    · rw [hb v hv, one_mul, inv_one, mul_one]
      exact (locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv _).mpr (H2 v hv)

/-- The local orbit at $v$ of an orbit $O$ of integral adelic frames. -/
def finToLoc (O : FinOrbit Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) : LocOrbit v Q₀ T₀ fr :=
  Quotient.mk _ (locFrAt Q₀ hQ T₀ Ξ D hT (Quotient.out O).1 (Quotient.out O).2 v)

theorem finToLoc_eq (b : IntFr Q₀ T₀ Ξ) (v : HeightOneSpectrum (𝓞 F)) :
    finToLoc Q₀ hQ T₀ Ξ D hT (Quotient.mk _ b) v = Quotient.mk _ (locFrAt Q₀ hQ T₀ Ξ D hT b.1 b.2 v) := by
  apply Quotient.sound
  have h : (finOrbitSetoid Q₀ T₀ Ξ).r (Quotient.out (Quotient.mk (finOrbitSetoid Q₀ T₀ Ξ) b)) b :=
    Quotient.mk_out (s := finOrbitSetoid Q₀ T₀ Ξ) b
  exact (finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT _ _).mp h v

/-- The real local measures $\mu_v(SO(L_v))$. -/
def aSO {N : ℕ} (Q : QuadForm (𝓞 F) N) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q))).toReal

theorem ofReal_aSO {N : ℕ} (Q : QuadForm (𝓞 F) N) (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (aSO Q v) = muLocSO v Q 1 (soStabSO v Q : Set (SOv v Q)) := by
  rw [aSO, ENNReal.ofReal_toReal]; rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top

theorem aSO_pos {N : ℕ} (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) :
    0 < aSO Q v :=
  ENNReal.toReal_pos (muLocSO_soStabSO_pos Q hQ v one_pos) (by rw [muLocSO_soStabSO]; exact ENNReal.ofReal_ne_top)

theorem tprod_aSO_pos {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) : 0 < ∏' v, aSO Q v := by
  have := tprod_siegelDensity_pos hN Q hQ
  rwa [← finFactor_one Q hQ] at this

theorem multipliable_aSO {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) :
    Multipliable (aSO Q) :=
  multipliable_muLocSO_one Q hQ (by omega) (by omega)

open Classical in
/-- **One orbit term**: $\frac{\mu_f(SO(\hat L))}{\mu''_f(K_O)} = \prod_{v\in B}\frac{\mu_v(SO(L_v))}{\mu''_v(K_{O,v})}\cdot
\frac{\prod_{v\notin B}\mu_v(SO(L_v))}{\prod_{v\notin B}\mu''_v(SO(L''_v))}$. -/
theorem orbit_term_eq (hn' : 3 ≤ n') (O : FinOrbit Q₀ T₀ Ξ) :
    muFin Q₀ (fun _ => 1) (KSO Q₀) /
        muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (finOrbitRep Q₀ T₀ Ξ O)) =
      (∏ v ∈ Bad, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) /
          muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q'))) *
        ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aSO D.Q'' v) := by
  have hN : 3 ≤ r + n' := by omega
  obtain ⟨b', hrel, hgood⟩ := exists_goodRep Q₀ hQ T₀ Ξ D hT (by omega) (Quotient.out O)
  have hO : O = Quotient.mk _ b' := by
    conv_lhs => rw [← Quotient.out_eq O]
    exact Quotient.sound hrel
  show _ / muFin D.Q'' (fun _ => 1) (orbitStab D.ιFin (KSO Q₀) (Quotient.out O).1) = _
  rw [← muFin_orbitStab_congr Q₀ hQ T₀ Ξ D (by omega) _ _ hrel, orbitStab_eq_boxSO Q₀ hQ T₀ Ξ D hT b'.1 hgood]
  have hQ'' := D.hQ''
  have hU : ∀ v ∈ Bad, MeasurableSet
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) :=
    fun v _ => (isOpen_orbitStab_loc v Q₀ T₀ fr _).measurableSet
  rw [muFin_boxSO_split D.Q'' D.hQ'' (fun _ => one_pos) (multipliable_aSO hn' D.Q'' D.hQ'') Bad _ hU]
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
  have hpos : 0 < ∏' v, if v ∈ Bad then 1 else aSO D.Q'' v := by
    have h := tprod_eq_prod_mul_tprod_ite (aSO D.Q'') (multipliable_aSO hn' D.Q'' D.hQ'') Bad
      (fun v _ => (aSO_pos D.Q'' D.hQ'' v).ne')
    have hp := tprod_aSO_pos hn' D.Q'' D.hQ''
    rw [h] at hp
    exact pos_of_mul_pos_right hp (Finset.prod_nonneg fun v _ => (aSO_pos D.Q'' D.hQ'' v).le)
  have hloc : ∀ v ∈ Bad, muLocSO v D.Q'' 1
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) =
      muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr (finToLoc Q₀ hQ T₀ Ξ D hT O v) : Set (SOv v (fr).Q')) := by
    intro v _
    rw [hO, finToLoc_eq]
    exact muLocSO_orbitStab_eq v Q₀ T₀ fr hT D.hQ'' (by omega) _ _ rfl
  have hU0 : ∀ v ∈ Bad, muLocSO v D.Q'' 1
      ((orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) (evalSO Q₀ v b'.1) : Subgroup (SOv v D.Q'')) :
        Set (SOv v D.Q'')) ≠ 0 := by
    intro v _
    have := isHaarMeasure_muLocSO v (fr).Q' D.hQ''
    exact ((isOpen_orbitStab_loc v Q₀ T₀ fr _).measure_pos _ ⟨1, Subgroup.one_mem _⟩).ne'
  have hsplit : (∏' v, if v ∈ Bad then 1 else
      (muLocSO v D.Q'' 1 (soStabSO v D.Q'' : Set (SOv v D.Q''))).toReal) =
      ∏' v, if v ∈ Bad then 1 else aSO D.Q'' v := rfl
  rw [hsplit, ennreal_prod_div _ _ _ hU0 _ _ hpos]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun v hv => by rw [hloc v hv]) rfl

theorem tprod_ite_aSO_pos {N : ℕ} (hN : 3 ≤ N) (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate)
    (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidablePred (· ∈ S)] :
    0 < ∏' v, if v ∈ S then 1 else aSO Q v := by
  classical
  have h := tprod_eq_prod_mul_tprod_ite (aSO Q) (multipliable_aSO hN Q hQ) S (fun v _ => (aSO_pos Q hQ v).ne')
  have hp := tprod_aSO_pos hN Q hQ
  rw [h] at hp
  convert pos_of_mul_pos_right hp (Finset.prod_nonneg fun v _ => (aSO_pos Q hQ v).le)

/-- The local orbits at the exceptional places of an orbit of integral adelic frames. -/
def finOrbitMap (O : FinOrbit Q₀ T₀ Ξ) : ∀ v : Bad, LocOrbit v.1 Q₀ T₀ fr :=
  fun v => finToLoc Q₀ hQ T₀ Ξ D hT O v.1

/-- **The orbits of integral adelic frames are the families of local orbits at the exceptional places.** -/
theorem finOrbitMap_bijective (hn' : 1 ≤ n') : Function.Bijective (finOrbitMap Q₀ hQ T₀ Ξ D hT) := by
  classical
  constructor
  · intro O O' h
    rw [← Quotient.out_eq O, ← Quotient.out_eq O']
    apply Quotient.sound
    refine (finOrbit_rel_iff Q₀ hQ T₀ Ξ D hT _ _).mpr fun v => ?_
    by_cases hv : v ∈ Bad
    · exact Quotient.exact (congrFun h ⟨v, hv⟩)
    · have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
      exact Quotient.exact (Subsingleton.elim (Quotient.mk _ _) (Quotient.mk _ _))
  · intro x
    set φ : ∀ v, SOv v Q₀ := fun v => if hv : v ∈ Bad then locOrbitRep v Q₀ T₀ fr (x ⟨v, hv⟩) else 1 with hφ
    obtain ⟨c, hcS, hcn⟩ := exists_SOAf_of_fam Q₀ Bad φ
    have hS : ∀ (v) (hv : v ∈ Bad), locFr Q₀ hQ T₀ Ξ D hT v c =
        (Quotient.out (x ⟨v, hv⟩) : locFrameSet v Q₀ T₀ fr).1 := by
      intro v hv
      show soMat v (evalSO Q₀ v c) * locBase v Q₀ T₀ fr = _
      rw [hcS v hv, frPhi_spec v Q₀ T₀ fr (Quotient.out (x ⟨v, hv⟩))]
      simp only [hφ, hv, ↓reduceDIte, locOrbitRep_eq]
    have hN : ∀ v ∉ Bad, locFr Q₀ hQ T₀ Ξ D hT v c = locBase v Q₀ T₀ fr := fun v hv => by
      simp only [locFr, hcn v hv, soMat_one, Matrix.one_mul]
    have hint : c • ratFT Q₀ T₀ Ξ ∈ latHatT F (r + n') r := by
      rw [mem_latHatT_smul_iff Q₀ hQ T₀ Ξ D hT]
      intro v i j
      by_cases hv : v ∈ Bad
      · rw [hS v hv]; exact (Quotient.out (x ⟨v, hv⟩)).2.2 i j
      · rw [hN v hv]; exact good_base_int Q₀ hQ T₀ Ξ D hT v hv i j
    refine ⟨Quotient.mk _ ⟨c, hint⟩, funext fun v => ?_⟩
    show finToLoc Q₀ hQ T₀ Ξ D hT (Quotient.mk _ ⟨c, hint⟩) v.1 = x v
    rw [finToLoc_eq]
    conv_rhs => rw [← Quotient.out_eq (x v)]
    exact congrArg _ (Subtype.ext (hS v.1 v.2))

open Classical in
/-- **Weil's measure of the integral frames as a product over the exceptional places.** -/
theorem frameOrbitSum_eq_prod (hn' : 3 ≤ n') :
    frameOrbitSum Q₀ hQ T₀ Ξ D = (∏ v ∈ Bad, locOrbitSum v Q₀ T₀ fr) *
      ENNReal.ofReal ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aSO D.Q'' v) := by
  unfold frameOrbitSum
  rw [tsum_congr (orbit_term_eq Q₀ hQ T₀ Ξ D hT hn'), ENNReal.tsum_mul_right]
  congr 1
  set e := Equiv.ofBijective _ (finOrbitMap_bijective Q₀ hQ T₀ Ξ D hT (by omega))
  have : ∀ v : Bad, Fintype (LocOrbit v.1 Q₀ T₀ fr) := fun v =>
    @Fintype.ofFinite _ (finite_locOrbit v.1 Q₀ T₀ fr hQ hT (by omega))
  set w : ∀ v : HeightOneSpectrum (𝓞 F), LocOrbit v Q₀ T₀ fr → ℝ≥0∞ := fun v o =>
    muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) / muLocSO v (fr).Q' 1 (locOrbitStab v Q₀ T₀ fr o : Set (SOv v (fr).Q'))
    with hw
  have h1 : ∀ O : FinOrbit Q₀ T₀ Ξ, (∏ v ∈ Bad, w v (finToLoc Q₀ hQ T₀ Ξ D hT O v)) =
      ∏ v : Bad, w v.1 (e O v) := fun O => (Finset.prod_coe_sort Bad _).symm
  rw [tsum_congr h1, e.tsum_eq (f := fun x => ∏ v : Bad, w v.1 (x v)), tsum_fintype, ← Fintype.prod_sum,
    ← Finset.prod_coe_sort Bad]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [locOrbitSum, tsum_fintype]

theorem frameLocFactor_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ frameLocFactor Q₀ hQ T₀ Ξ D hT v := by
  unfold frameLocFactor
  have := localDensityForm_nonneg_of_frame v Q₀ T₀ fr hQ hT
  positivity

theorem ofReal_frameLocFactor (hn' : 1 ≤ n') (v : HeightOneSpectrum (𝓞 F)) :
    ENNReal.ofReal (frameLocFactor Q₀ hQ T₀ Ξ D hT v) = locOrbitSum v Q₀ T₀ fr :=
  (locOrbitSum_eq v Q₀ T₀ fr hQ hT hn').symm

/-- At a good place the local factor is $\mu_v(SO(L_v))/\mu''_v(SO(L''_v))$. -/
theorem frameLocFactor_good (hn' : 1 ≤ n') (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ Bad) :
    frameLocFactor Q₀ hQ T₀ Ξ D hT v = aSO Q₀ v / aSO D.Q'' v := by
  have := good_subsingleton Q₀ hQ T₀ Ξ D hT v hv hn'
  set y : locFrameSet v Q₀ T₀ fr := ⟨locBase v Q₀ T₀ fr, ⟨1, by rw [soMat_one, Matrix.one_mul]⟩,
    good_base_int Q₀ hQ T₀ Ξ D hT v hv⟩
  have hstab : (orbitStab (locIota v Q₀ T₀ fr) (soStabSO v Q₀) 1 : Set (SOv v (fr).Q')) =
      (soStabSO v D.Q'' : Set (SOv v D.Q'')) := by
    ext h
    simp only [SetLike.mem_coe, mem_orbitStab', one_mul, inv_one, mul_one]
    exact locIota_mem_iff Q₀ hQ T₀ Ξ D hT v hv h
  have hK := muLocSO_orbitStab_eq v Q₀ T₀ fr hT D.hQ'' hn' 1 y (by rw [soMat_one, Matrix.one_mul])
  rw [hstab] at hK
  have hsum : locOrbitSum v Q₀ T₀ fr = ENNReal.ofReal (aSO Q₀ v) / ENNReal.ofReal (aSO D.Q'' v) := by
    rw [locOrbitSum, tsum_eq_single (Quotient.mk _ y) (fun o ho => absurd (Subsingleton.elim o _) ho),
      ofReal_aSO, ofReal_aSO, ← hK]
  rw [← ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT (by omega) v, ← ENNReal.ofReal_div_of_pos (aSO_pos D.Q'' D.hQ'' v)]
    at hsum
  exact (ENNReal.ofReal_eq_ofReal_iff (frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v)
    (div_nonneg (aSO_pos Q₀ hQ v).le (aSO_pos D.Q'' D.hQ'' v).le)).mp hsum

open Classical in
theorem hasProd_frameLocFactor (hn' : 3 ≤ n') :
    HasProd (frameLocFactor Q₀ hQ T₀ Ξ D hT) ((∏ v ∈ Bad, frameLocFactor Q₀ hQ T₀ Ξ D hT v) *
      ((∏' v, if v ∈ Bad then 1 else aSO Q₀ v) / ∏' v, if v ∈ Bad then 1 else aSO D.Q'' v)) := by
  have hN : 3 ≤ r + n' := by omega
  have hA := multipliable_ite_one (aSO Q₀) (multipliable_aSO hN Q₀ hQ) Bad (fun v _ => (aSO_pos Q₀ hQ v).ne')
  have hB := multipliable_ite_one (aSO D.Q'') (multipliable_aSO hn' D.Q'' D.hQ'') Bad
    (fun v _ => (aSO_pos D.Q'' D.hQ'' v).ne')
  have hdiv := hA.hasProd.div₀ hB.hasProd (tprod_ite_aSO_pos hn' D.Q'' D.hQ'' Bad).ne'
  have hg : (fun v => (if v ∈ Bad then 1 else aSO Q₀ v) / (if v ∈ Bad then 1 else aSO D.Q'' v)) =
      fun v => if v ∈ Bad then 1 else frameLocFactor Q₀ hQ T₀ Ξ D hT v := by
    funext v
    by_cases hv : v ∈ Bad
    · simp [hv]
    · simp only [hv, ite_false]
      exact (frameLocFactor_good Q₀ hQ T₀ Ξ D hT (by omega) v hv).symm
  rw [hg] at hdiv
  rw [← hdiv.tprod_eq]
  exact hasProd_prod_mul_tprod_ite _ Bad hdiv.multipliable

theorem multipliable_frameLocFactor (hn' : 3 ≤ n') : Multipliable (frameLocFactor Q₀ hQ T₀ Ξ D hT) :=
  (hasProd_frameLocFactor Q₀ hQ T₀ Ξ D hT hn').multipliable

/-- **Weil's measure of the integral adelic frames is the product of the local densities**:
$$\sum_O\frac{\mu_f(SO(\hat L))}{\mu_{H,f}(K_O)} = \prod_\mathfrak p\beta_\mathfrak p(L,T_0)\,|\det g|_\mathfrak p^{\,n'+1}\,
  |\det H_{T_0}|_\mathfrak p^{-n'}.$$ -/
theorem frameOrbitSum_eq (hn' : 3 ≤ n') :
    frameOrbitSum Q₀ hQ T₀ Ξ D = ENNReal.ofReal (∏' v, frameLocFactor Q₀ hQ T₀ Ξ D hT v) := by
  classical
  rw [(hasProd_frameLocFactor Q₀ hQ T₀ Ξ D hT hn').tprod_eq, frameOrbitSum_eq_prod Q₀ hQ T₀ Ξ D hT hn',
    ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v),
    ENNReal.ofReal_prod_of_nonneg fun v _ => frameLocFactor_nonneg Q₀ hQ T₀ Ξ D hT v]
  congr 1
  exact Finset.prod_congr rfl fun v _ => (ofReal_frameLocFactor Q₀ hQ T₀ Ξ D hT (by omega) v).symm

end QuadFormsKB.Tamagawa.Indefinite
