/-
# The archimedean identity and the product formula for the non-square model

**Layer:** $F$ totally real, $K/F$ quadratic and totally real, $-a,-b,d\gg0$.

* **`prod_abs_sigW_algebraMap`**: $\prod_{w\mid\infty}|\sigma_w(y)| = (\prod_{v\mid\infty}|\sigma_v(y)|)^2$ for $y\in F$ (norm transitivity).
* **`muArchTamSO_qNS_univ_toReal`**: $\mu^{\mathrm{Tam}}_\infty(G_\infty) = c_F(4)\prod_v\pi^4/(64D_v^2\sqrt{D_v})$, $D_v = \sigma_v(a^2b^2d^3)$.
* **`nsArchRatio`** and **`arch_identity_ns`**: $\mu^{(3)}_{K,\infty}(G_\infty)\cdot\prod_{v\in S}r_v = \mu^{(4)}_{F,\infty}(G_\infty)$ with
  $r_v = R_v^{-3}\|ab\|_v^{-3}\|d\|_v^{15/2}$, $R_v = \prod_{w\mid v}\mathrm{vol}(\mathfrak o_w)/\mathrm{vol}(\mathfrak o_v)^2$ (the product formula
  for $ab$, $d$ and for the discriminants $|d_K|^{1/2} = |d_F|\prod_vR_v^{-1}$).

Source: Weil 1982, §2.3 (product formula), Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSAssembly

open MeasureTheory Set Function NumberField NumberField.InfinitePlace IsDedekindDomain Module
open scoped ENNReal ComplexOrder Classical

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayArch

noncomputable section

/-! ### Real places of $K$ over $F$ -/

section RealPlaces

variable {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [Algebra F K]
  [IsTotallyReal K]

theorem card_real_places_eq (hK : finrank F K = 2) :
    Fintype.card {w : InfinitePlace K // w.IsReal} = 2 * Fintype.card {v : InfinitePlace F // v.IsReal} := by
  have h1 := IsTotallyReal.finrank (K := K)
  have h2 := IsTotallyReal.finrank (K := F)
  have h3 : finrank ℚ K = finrank ℚ F * finrank F K := (Module.finrank_mul_finrank ℚ F K).symm
  unfold nrRealPlaces at h1 h2
  rw [← h1, ← h2, h3, hK, mul_comm]

theorem prod_norm_embeddings_eq_abs_norm {L : Type} [Field L] [NumberField L] (x : L) :
    ∏ σ : L →ₐ[ℚ] ℂ, ‖σ x‖ = |(Algebra.norm ℚ x : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← norm_prod, ← h]
  simp [Complex.norm_ratCast]

/-- **$\prod_{w\mid\infty}|\sigma_w(y)| = (\prod_{v\mid\infty}|\sigma_v(y)|)^2$** for $y\in F$, $[K:F] = 2$. -/
theorem prod_abs_sigW_algebraMap (hK : finrank F K = 2) (y : F) :
    ∏ w : {w : InfinitePlace K // w.IsReal}, |sigW w (algebraMap F K y)| =
      (∏ v : {v : InfinitePlace F // v.IsReal}, |sigW v y|) ^ 2 := by
  rw [← prod_norm_embeddings_eq_prod_sigW, ← prod_norm_embeddings_eq_prod_sigW,
    prod_norm_embeddings_eq_abs_norm, prod_norm_embeddings_eq_abs_norm, ← Algebra.norm_norm (S := F),
    Algebra.norm_algebraMap, hK, map_pow, Rat.cast_pow, abs_pow]

end RealPlaces

/-! ### The archimedean mass of $SO(\langle1,-ad,-bd,abd\rangle)$ -/

section ArchNS

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F}

theorem hessian_qNS (a b d : 𝓞 F) :
    (qNS a b d).hessian = Matrix.diagonal ![2, -2 * (a * d), -2 * (b * d), 2 * (a * b * d)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuadForm.hessian, qNS, QuadForm.diag, Matrix.diagonal, map_ofNat] <;> ring

theorem gramDetR_QRe_qNS (w : {w : InfinitePlace F // w.IsReal}) :
    gramDetR (QRe (qNS a b d) w) = (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 * (sigW w (d : F)) ^ 3 := by
  rw [gramDetR, QRe, QuadForm.hessian_map, QuadForm.hessian_map, hessian_qNS, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_map (map_zero _), Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, map_mul, map_neg, map_ofNat]
  norm_num [Matrix.vecHead, Matrix.vecTail]
  simp only [map_ofNat]
  ring

variable [IsTotallyReal F]

theorem muArchTamSO_qNS_univ (hQ : (qNS a b d).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qNS a b d))) :
    muArchTamSO (qNS a b d) hQ Set.univ =
      ENNReal.ofReal (cF F 4) * ∏ w : {w : InfinitePlace F // w.IsReal},
        ENNReal.ofReal (QuadFormsKB.Tamagawa.archVolSO 4 (gramDetR (QRe (qNS a b d) w))) := by
  have : ∀ w, Fact (IsPosDefR (QRe (qNS a b d) w)) := fun w => ⟨isPosDefR_QRe (qNS a b d) hQ hpd w⟩
  have hC : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => (not_isComplex_iff_isReal.mpr (IsTotallyReal.isReal w.1)) w.2⟩
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe (qNS a b d) w) (gramDetR_QRe_ne_zero (qNS a b d) hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero (qNS a b d) hQ w); infer_instance
  have hsfC : ∀ i : {w : InfinitePlace F // w.IsComplex},
      SigmaFinite (LerayComplex.lerayMeasureC (QCx (qNS a b d) i) (gramDetC_QCx_ne_zero (qNS a b d) hQ i)) :=
    fun i => isEmptyElim i
  rw [muArchTamSO_of_isTotallyReal, Measure.smul_apply, smul_eq_mul, muArchNF, muArchLeray, ← Set.univ_prod_univ,
    Measure.prod_prod, Measure.pi_univ, Measure.pi_univ,
    Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty, mul_one]
  congr 1
  exact Finset.prod_congr rfl fun w _ => lerayMeasure_univ _ (by norm_num)

theorem ohatVol_pow_six : ohatVol F ^ 6 = cF F 4 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero (K := F))
  rw [ohatVol, cF, Real.sqrt_eq_rpow, ← Real.rpow_neg hd.le, ← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num

/-- **The archimedean mass in closed form** ($-a,-b,d\gg0$). -/
theorem muArchTamSO_qNS_univ_toReal (hQ : (qNS a b d).Nondegenerate)
    (hpd : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qNS a b d))) (hd : IsTotallyPos (d : F)) :
    (muArchTamSO (qNS a b d) hQ Set.univ).toReal = ohatVol F ^ 6 * ∏ w : {w : InfinitePlace F // w.IsReal},
      Real.pi ^ 4 / (64 * (|sigW w (a : F)| ^ 5 * |sigW w (b : F)| ^ 5 *
        ((sigW w (d : F)) ^ 7 * Real.sqrt (sigW w (d : F))))) := by
  rw [muArchTamSO_qNS_univ hQ hpd, ENNReal.toReal_mul, ENNReal.toReal_ofReal cF_nonneg, ENNReal.toReal_prod,
    ← ohatVol_pow_six]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hdw : 0 < sigW w (d : F) := emb_pos_of_isTotallyPos hd w.1 w.2
  have hD : 0 < (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 * (sigW w (d : F)) ^ 3 := by
    have ha : 0 < (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 ∨ (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 = 0 :=
      (eq_or_lt_of_le (by positivity)).elim (fun h => Or.inr h.symm) Or.inl
    rcases ha with ha | ha
    · positivity
    · exfalso
      have hQ' := gramDetR_QRe_ne_zero (qNS a b d) hQ w
      rw [gramDetR_QRe_qNS, ha, zero_mul] at hQ'
      exact hQ' rfl
  rw [gramDetR_QRe_qNS, ENNReal.toReal_ofReal (by rw [archVolSO_four hD]; positivity), archVolSO_four hD]
  congr 2
  have h2 : (sigW w (a : F)) ^ 2 * (sigW w (b : F)) ^ 2 * (sigW w (d : F)) ^ 3 =
      ((|sigW w (a : F)| * |sigW w (b : F)| * sigW w (d : F)) ^ 2) * sigW w (d : F) := by
    rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
  rw [h2, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

end ArchNS

/-! ### The local relative discriminant factor $R_v$ -/

section RelDisc

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- $\mathrm{vol}(\mathfrak o_v)$ for the self-dual measure. -/
abbrev vo {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : ℝ :=
  (Analysis.selfDualV v).real (Analysis.latticeV v 0)

variable (K) in
/-- **$R_v = \prod_{w\mid v}\mathrm{vol}(\mathfrak o_w)/\mathrm{vol}(\mathfrak o_v)^2$** (the local factor of $|d_K|^{-1/2}/|d_F|^{-1}$). -/
def relDisc (v : HeightOneSpectrum (𝓞 F)) : ℝ := (∏ w ∈ placesOver (K := K) v, vo w) / vo v ^ 2

theorem vo_pos {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : 0 < vo v := selfDualV_real_pos v

theorem relDisc_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < relDisc K v :=
  div_pos (Finset.prod_pos fun w _ => vo_pos w) (pow_pos (vo_pos v) 2)

open scoped Classical in
theorem prod_placeSet_eq (v : HeightOneSpectrum (𝓞 F)) (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∏ w : PlaceSet (K := K) v, f w.1 = ∏ w ∈ placesOver (K := K) v, f w := by
  refine (Finset.prod_subtype (placesOver (K := K) v) (fun w => ?_) f).symm
  exact mem_placesOver v

/-- **$R_v = 1$ where $\operatorname{disc}(b)$ is a $v$-unit** (`localConst_eq_one`). -/
theorem relDisc_eq_one {bK : Module.Basis (Fin 2) F K} (hint : ∀ i, IsIntegral ℤ (bK i))
    {v : HeightOneSpectrum (𝓞 F)} (hd : v.valuation F (Algebra.discr F bK) = 1) : relDisc K v = 1 := by
  have hmap := map_volVN_localPi bK v
  rw [localConst_eq_one bK v hint hd, ENNReal.coe_one, one_smul] at hmap
  have e1 : ((volVN (ι := Fin 2) v).map (localPiCLE bK v)) (intPlace (K := K) v) = volVN (ι := Fin 2) v (intLat v) := by
    rw [← localPi_image_integers bK v hint hd]
    exact map_localPi_apply bK v _
  rw [hmap] at e1
  have h1 := congrArg ENNReal.toReal e1
  change (placeMeasure (K := K) v).real (intPlace v) = (volVN (ι := Fin 2) v).real (intLat v) at h1
  rw [intPlace_eq_pi, intLat_eq_pi] at h1
  unfold placeMeasure at h1
  rw [real_pi_selfDual, real_pi_selfDual (J := Fin 2) (fun _ => v)] at h1
  rw [relDisc, ← prod_placeSet_eq v vo]
  rw [h1, Fin.prod_univ_two, sq, div_self (mul_pos (vo_pos v) (vo_pos v)).ne']

open scoped Classical in
/-- **$\prod_{v\in S}R_v = \mathrm{vol}(\hat{\mathcal O}_K)/\mathrm{vol}(\hat{\mathcal O}_F)^2$** when $R_v = 1$ off $S$. -/
theorem prod_relDisc_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, relDisc K v = 1) :
    ∏ v ∈ S, relDisc K v = ohatVol K / ohatVol F ^ 2 := by
  have hTK := mulSupport_volO_real_finite (F := K)
  have hTF := mulSupport_volO_real_finite (F := F)
  set V : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hTF.toFinset ∪ hTK.toFinset.image underPlace
  have hSV : S ⊆ V := Finset.subset_union_left.trans Finset.subset_union_left
  have h1 : ∏ v ∈ S, relDisc K v = ∏ v ∈ V, relDisc K v :=
    Finset.prod_subset hSV fun v _ hv => hS v hv
  have hK : ohatVol K = ∏ v ∈ V, ∏ w ∈ placesOver (K := K) v, vo w := by
    rw [ohatVol_eq_finprod, ← Finset.prod_biUnion (pairwiseDisjoint_placesOver V)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨underPlace w, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hTK.mem_toFinset.2 hw)), ?_⟩
    exact (mem_placesOver _).2 rfl
  have hF : ohatVol F = ∏ v ∈ V, vo v := by
    rw [ohatVol_eq_finprod]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (hTF.mem_toFinset.2 hv))
  rw [h1, hK, hF, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  rfl

end RelDisc

/-! ### The archimedean identity -/

section ArchIdentity

variable {F K : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [Algebra F K]
  [IsTotallyReal K] {a b d : 𝓞 F}

variable (K a b d) in
/-- **The local ratio $r_v = R_v^{-3}\|ab\|_v^{-3}\|d\|_v^{15/2}$** at a finite place $v$ of $F$. -/
def nsRatio (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (relDisc K v)⁻¹ ^ 3 * (‖algebraMap F (v.adicCompletion F) ((a : F) * (b : F))‖⁻¹) ^ 3 *
    ‖algebraMap F (v.adicCompletion F) (d : F)‖ ^ ((15 : ℝ) / 2)

theorem nsRatio_pos (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    0 < nsRatio K a b d v := by
  have hab : algebraMap F (v.adicCompletion F) ((a : F) * (b : F)) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F _).injective]; exact mul_ne_zero ha0 hb0
  have hd : algebraMap F (v.adicCompletion F) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap F _).injective]; exact hd0
  unfold nsRatio
  have := relDisc_pos (K := K) v
  have := norm_pos_iff.2 hab
  have := norm_pos_iff.2 hd
  positivity

/-- $\prod_{v\in S}\|x\|_v = (\prod_{v\mid\infty}|\sigma_v(x)|)^{-1}$ when $|x|_v = 1$ off $S$ (product formula). -/
theorem prod_norm_eq_of_good (S : Finset (HeightOneSpectrum (𝓞 F))) {x : F} (hx : x ≠ 0)
    (hS : ∀ v ∉ S, v.valuation F x = 1) :
    ∏ v ∈ S, ‖algebraMap F (v.adicCompletion F) x‖ = (∏ w : {w : InfinitePlace F // w.IsReal}, |sigW w x|)⁻¹ := by
  rw [← prod_norm_embeddings_eq_prod_sigW, ← QuadFormsKB.Tamagawa.finprod_norm_eq x hx]
  exact (QuadFormsKB.Tamagawa.finprod_eq_prod_of_one S fun v hv =>
    QuadFormsKB.Tamagawa.norm_algebraMap_eq_one (hS v hv)).symm

theorem pow_mul_sqrt_eq_rpow {x : ℝ} (hx : 0 < x) : x ^ 7 * Real.sqrt x = x ^ ((15 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hx]; norm_num

set_option maxHeartbeats 1600000 in
/-- **The archimedean identity** $\mu^{(3)}_{K,\infty}(G_\infty)\prod_{v\in S}r_v = \mu^{(4)}_{F,\infty}(G_\infty)$ (Weil's product
formula for the non-square model). -/
@[kb "weil1982" "§2.3 (product formula), Thm 2.3.1 [unverified page]"]
theorem arch_identity_ns (hK2 : finrank F K = 2) {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F))
    (hβ : (β : K) = algebraMap F K (b : F)) (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0)
    (hd0 : (d : F) ≠ 0) (hna : IsTotallyPos (-(a : F))) (hnb : IsTotallyPos (-(b : F))) (hd : IsTotallyPos (d : F))
    (hQ : (qNS a b d).Nondegenerate) (hpd4 : IsTotallyPosDef (QuadFormsKB.HilbertModular.formF (qNS a b d)))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hSg : ∀ v ∉ S, relDisc K v = 1 ∧ v.valuation F ((a : F) * (b : F)) = 1 ∧ v.valuation F (d : F) = 1) :
    (muArchTamSO (QuatZeta.pureFormO α β) (nondegenerate_pureFormO α β hα0 hβ0) univ).toReal *
        ∏ v ∈ S, nsRatio K a b d v = (muArchTamSO (qNS a b d) hQ univ).toReal := by
  have hna' : IsTotallyPos (-(α : K)) := by rw [hα, ← map_neg]; exact isTotallyPos_algebraMap hna
  have hnb' : IsTotallyPos (-(β : K)) := by rw [hβ, ← map_neg]; exact isTotallyPos_algebraMap hnb
  have hpd3 := hpd_pureFormO (F := K) hna' hnb'
  rw [muArchTamSO_univ_toReal (F := K) hα0 hβ0 hpd3, muArchTamSO_qNS_univ_toReal hQ hpd4 hd,
    ← ohatVol_pow_three]
  set n := Fintype.card {v : InfinitePlace F // v.IsReal}
  set A := ∏ v : {v : InfinitePlace F // v.IsReal}, |sigW v (a : F)|
  set B := ∏ v : {v : InfinitePlace F // v.IsReal}, |sigW v (b : F)|
  set D := ∏ v : {v : InfinitePlace F // v.IsReal}, sigW v (d : F)
  have hA : 0 < A := Finset.prod_pos fun v _ => abs_pos.2 ((map_ne_zero _).2 ha0)
  have hB : 0 < B := Finset.prod_pos fun v _ => abs_pos.2 ((map_ne_zero _).2 hb0)
  have hDv : ∀ v : {v : InfinitePlace F // v.IsReal}, 0 < sigW v (d : F) := fun v => emb_pos_of_isTotallyPos hd v.1 v.2
  have hD : 0 < D := Finset.prod_pos fun v _ => hDv v
  -- the K-product
  have hK : ∏ w : {w : InfinitePlace K // w.IsReal},
      Real.pi ^ 2 / (8 * ((sigW w (α : K)) ^ 2 * (sigW w (β : K)) ^ 2) ^ 2) =
      (Real.pi ^ 2 / 8) ^ (2 * n) * (A ^ 8 * B ^ 8)⁻¹ := by
    have e : ∀ w : {w : InfinitePlace K // w.IsReal},
        Real.pi ^ 2 / (8 * ((sigW w (α : K)) ^ 2 * (sigW w (β : K)) ^ 2) ^ 2) =
          (Real.pi ^ 2 / 8) * ((|sigW w (α : K)| ^ 4 * |sigW w (β : K)| ^ 4))⁻¹ := by
      intro w
      rw [show ((sigW w (α : K)) ^ 2 * (sigW w (β : K)) ^ 2) ^ 2 = |sigW w (α : K)| ^ 4 * |sigW w (β : K)| ^ 4 by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs, sq_abs]; ring]
      field_simp
    rw [Finset.prod_congr rfl fun w _ => e w, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      card_real_places_eq hK2, Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, hα, hβ,
      prod_abs_sigW_algebraMap hK2, prod_abs_sigW_algebraMap hK2, ← pow_mul, ← pow_mul]
  -- the F-product
  have hF : ∏ w : {w : InfinitePlace F // w.IsReal},
      Real.pi ^ 4 / (64 * (|sigW w (a : F)| ^ 5 * |sigW w (b : F)| ^ 5 *
        ((sigW w (d : F)) ^ 7 * Real.sqrt (sigW w (d : F))))) =
      (Real.pi ^ 4 / 64) ^ n * (A ^ 5 * B ^ 5 * D ^ ((15 : ℝ) / 2))⁻¹ := by
    have e : ∀ w : {w : InfinitePlace F // w.IsReal},
        Real.pi ^ 4 / (64 * (|sigW w (a : F)| ^ 5 * |sigW w (b : F)| ^ 5 *
          ((sigW w (d : F)) ^ 7 * Real.sqrt (sigW w (d : F))))) =
          (Real.pi ^ 4 / 64) * (|sigW w (a : F)| ^ 5 * |sigW w (b : F)| ^ 5 * (sigW w (d : F)) ^ ((15 : ℝ) / 2))⁻¹ := by
      intro w
      rw [pow_mul_sqrt_eq_rpow (hDv w)]
      field_simp
    rw [Finset.prod_congr rfl fun w _ => e w, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_inv_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
      Real.finset_prod_rpow _ _ fun w _ => (hDv w).le]
  -- the finite product
  have hab : (a : F) * (b : F) ≠ 0 := mul_ne_zero ha0 hb0
  have hSprod : ∏ v ∈ S, nsRatio K a b d v =
      (ohatVol K / ohatVol F ^ 2)⁻¹ ^ 3 * (A * B) ^ 3 * (D⁻¹) ^ ((15 : ℝ) / 2) := by
    unfold nsRatio
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow, Finset.prod_inv_distrib,
      Finset.prod_inv_distrib, Real.finset_prod_rpow S _ (fun v _ => norm_nonneg _),
      prod_relDisc_eq S (fun v hv => (hSg v hv).1), prod_norm_eq_of_good S hab (fun v hv => (hSg v hv).2.1),
      prod_norm_eq_of_good S hd0 (fun v hv => (hSg v hv).2.2)]
    congr 2
    · rw [inv_inv]
      simp only [A, B, map_mul, abs_mul, Finset.prod_mul_distrib]
    · congr 1
      exact Finset.prod_congr rfl fun v _ => abs_of_pos (hDv v)
  rw [hK, hF, hSprod, Real.inv_rpow hD.le]
  have hoK := ohatVol_pos (F := K)
  have hoF := ohatVol_pos (F := F)
  have hDr : 0 < D ^ ((15 : ℝ) / 2) := Real.rpow_pos_of_pos hD _
  rw [show (Real.pi ^ 4 / 64) ^ n = (Real.pi ^ 2 / 8) ^ (2 * n) by rw [pow_mul]; ring_nf]
  field_simp

end ArchIdentity

end

end QuadFormsKB.Tamagawa.Measure.Weil
