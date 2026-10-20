/-
# The good places of the non-square model

**Layer:** $F$ totally real (only for the regrouping), $K = F(\delta)$, $\delta^2 = d$; a finite place $v$ of $F$ with
$|2abd|_v = 1$ and $v\nmid\operatorname{disc}(1,\delta)$.

* **`siegelDensity_qNS_good`**: $\alpha_v(\langle1,-ad,-bd,abd\rangle) = (1-\chi(\bar d)q^{-2})(1-q^{-2})$
  (`localDensityForm_self_even`; $\chi(\bar d) = -1$ is the $SO^-(4,q)$ case, Kitaoka §5.6).
* **`prod_siegelDensity_good`**: $\prod_{w\mid v}\alpha_w(\langle-\alpha,-\beta,\alpha\beta\rangle) = \alpha_v(\langle1,-ad,-bd,abd\rangle)$ — split
  case: two places with $Nw = Nv$; inert case: one place with $Nw = Nv^2$ ($f = 1$ would make $d$ a square in $F_v$).
* **`finFactor_regroup`**: $\prod'_w\alpha^{(3)}_w = \prod'_v\alpha^{(4)}_v\cdot\prod_{v\in S}\prod_{w\mid v}\alpha^{(3)}_w/\alpha^{(4)}_v$.

Source: Kitaoka 1993, §5.6 [unverified]; Weil 1982, §2.3 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSArch
import QuadFormsKB.Literature.LocalGlobal.SquaresLocalGlobal
import QuadFormsKB.Literature.LocalGlobal.PrescribedNF

open Matrix NumberField IsDedekindDomain WithZero MeasureTheory Set Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LerayPadic LocalDensity

/-! ### The density of $\langle1,-ad,-bd,abd\rangle$ at a good place -/

section Density

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a b d : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

theorem hessian_Qp_qNS (a b d : 𝓞 F) : (NF.Qp v (qNS a b d)).hessian =
    Matrix.diagonal (fun i => NF.ι v (![2, -2 * (a * d), -2 * (b * d), 2 * (a * b * d)] i)) := by
  rw [NF.Qp, QuadForm.hessian_map, hessian_qNS, Matrix.diagonal_map (map_zero _)]

/-- **The good-place density of $\langle1,-ad,-bd,abd\rangle$**: $(1-\chi(\bar d)q^{-2})(1-q^{-2})$. -/
theorem siegelDensity_qNS_good (h2 : Valued.v (2 : Fv) = 1) (ha : Valued.v (algebraMap F Fv (a : F)) = 1)
    (hb : Valued.v (algebraMap F Fv (b : F)) = 1) (hd : Valued.v (algebraMap F Fv (d : F)) = 1) :
    letI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
    NF.siegelDensity v (qNS a b d) (qNS a b d) =
      (1 - (quadraticChar (IsLocalRing.ResidueField 𝔬) (IsLocalRing.residue 𝔬 (NF.ι v d)) : ℝ) *
        ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹) * (1 - ((DVR.q 𝔬 : ℝ) ^ 2)⁻¹) := by
  classical
  letI : Fintype (IsLocalRing.ResidueField 𝔬) := Fintype.ofFinite _
  have h2' : ¬ πv ∣ (2 : 𝔬) := not_dvd_of_valued_eq_one v (by rw [show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl]; exact h2)
  have hι : ∀ x : 𝓞 F, ((NF.ι v x : 𝔬) : Fv) = algebraMap F Fv (x : F) := coe_ι
  have hres : ∀ z : 𝔬, ¬ πv ∣ z → IsLocalRing.residue 𝔬 z ≠ 0 := by
    intro z hz h0
    rw [IsLocalRing.residue_eq_zero_iff, (NF.irreducible_π v).maximalIdeal_eq, Ideal.mem_span_singleton] at h0
    exact hz h0
  have habd : ¬ πv ∣ (NF.ι v a * NF.ι v b * NF.ι v d) := by
    refine not_dvd_of_valued_eq_one v ?_
    push_cast; rw [hι, hι, hι, map_mul, map_mul, ha, hb, hd, mul_one, mul_one]
  have hdd : ¬ πv ∣ NF.ι v d := not_dvd_of_valued_eq_one v (by rw [hι, hd])
  have e : (NF.Qp v (qNS a b d)).hessian.det = 2 ^ 4 * (NF.ι v a * NF.ι v b * NF.ι v d) ^ 2 * NF.ι v d := by
    rw [hessian_Qp_qNS, Matrix.det_diagonal, Fin.prod_univ_four]
    norm_num [Matrix.vecHead, Matrix.vecTail]
    rw [map_ofNat]; ring
  have hdet : ¬ πv ∣ (NF.Qp v (qNS a b d)).hessian.det := by
    rw [e]
    refine not_dvd_of_valued_eq_one v ?_
    push_cast
    rw [map_mul, map_mul, map_pow, map_pow, show ((2 : 𝔬) : Fv) = 2 by push_cast; rfl, h2, hι, hι, hι, map_mul,
      map_mul, ha, hb, hd]
    norm_num
  have h2r : (2 : IsLocalRing.ResidueField 𝔬) ≠ 0 := by
    have := hres 2 h2'; rwa [map_ofNat] at this
  have hχ : DVR.chiDisc (NF.Qp v (qNS a b d)) =
      quadraticChar (IsLocalRing.ResidueField 𝔬) (IsLocalRing.residue 𝔬 (NF.ι v d)) := by
    unfold DVR.chiDisc DVR.resGramDet
    have hr : IsLocalRing.residue 𝔬 (2 ^ 4 * (NF.ι v a * NF.ι v b * NF.ι v d) ^ 2 * NF.ι v d) / 2 ^ 4 =
        (IsLocalRing.residue 𝔬 (NF.ι v a * NF.ι v b * NF.ι v d)) ^ 2 * IsLocalRing.residue 𝔬 (NF.ι v d) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_ofNat]
      field_simp
    rw [e, hr, show (4 : ℕ) / 2 = 2 by rfl, neg_one_sq, one_mul, map_mul,
      quadraticChar_sq_one' (hres _ habd), one_mul]
  rw [NF.siegelDensity, if_pos rfl, NF.localDensityForm_eq_completion,
    DVR.localDensityForm_self_even πv 2 (by norm_num) _ (NF.irreducible_π v) h2' hdet, hχ]
  simp only [show 2 - 1 = 1 by rfl, Finset.range_one, Finset.prod_singleton]
  ring

end Density

/-! ### The places over a good place and their norms -/

section Places

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

theorem underPlace_eq_of_comap {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 K)}
    (hP : P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = v.asIdeal) : underPlace (k := F) P = v :=
  HeightOneSpectrum.ext hP

include hb₀ hb₁ in
theorem finrank_eq_two_of_basis : Module.finrank F K = 2 := by
  rw [Module.finrank_eq_card_basis bK]; simp

include hb₀ hb₁ in
theorem not_isSquare_d : ¬ IsSquare (d : F) := by
  have key : ∀ e : F, bK 1 ≠ algebraMap F K e := fun e he => by
    have h1 : bK.repr (bK 1) 1 = 1 := by simp
    have h2 : bK.repr (algebraMap F K e) 1 = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, ← hb₀, bK.repr_self]; simp
    rw [he] at h1; rw [h1] at h2; exact one_ne_zero h2
  rintro ⟨c, hc⟩
  have h1 : (bK 1 - algebraMap F K c) * (bK 1 + algebraMap F K c) = 0 := by
    rw [show (bK 1 - algebraMap F K c) * (bK 1 + algebraMap F K c) = bK 1 * bK 1 - algebraMap F K (c * c) by
      rw [map_mul]; ring, hb₁, hc, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact key c (sub_eq_zero.1 h)
  · exact key (-c) (by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h)

include hb₀ in
theorem span_basis (y : K) : ∃ b₀ b₁ : F, y = algebraMap F K b₀ + algebraMap F K b₁ * bK 1 := by
  refine ⟨bK.repr y 0, bK.repr y 1, ?_⟩
  conv_lhs => rw [← bK.sum_repr y]
  rw [Fin.sum_univ_two, hb₀, Algebra.smul_def, Algebra.smul_def, mul_one]

open scoped Classical in
include hb₀ hb₁ in
/-- **Split good place**: two places over $v$, both of norm $Nv$. -/
theorem placesOver_split {v : HeightOneSpectrum (𝓞 F)} (h2d : 2 * d ∉ v.asIdeal)
    (hsq : IsSquare (algebraMap F (v.adicCompletion F) (d : F))) :
    ∃ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q ∧ placesOver (K := K) v = {P, Q} ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  obtain ⟨P, Q, hPQ, hP, hQ, hnP, hnQ⟩ := QuadFormsKB.SqLG.exists_two_primes_of_isSquare d (not_isSquare_d hb₀ hb₁)
    (bK 1) (by rw [sq]; exact hb₁) (span_basis hb₀) v h2d hsq
  refine ⟨P, Q, hPQ, ?_, hnP, hnQ⟩
  have hPm : P ∈ placesOver (K := K) v := (mem_placesOver v).2 (underPlace_eq_of_comap hP)
  have hQm : Q ∈ placesOver (K := K) v := (mem_placesOver v).2 (underPlace_eq_of_comap hQ)
  have hcard : (placesOver (K := K) v).card ≤ 2 := by
    have := card_places_le_two (K := K) v (finrank_eq_two_of_basis hb₀ hb₁)
    rwa [Fintype.card_congr (Equiv.subtypeEquivRight (fun w => (mem_placesOver (K := K) v (w := w)).symm)),
      Fintype.card_coe] at this
  symm
  refine Finset.eq_of_subset_of_card_le (fun w hw => ?_) ?_
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  · rw [Finset.card_pair hPQ]; exact hcard

open scoped Classical in
include hb₀ hb₁ in
/-- **Inert good place**: one place over $v$, of norm $Nv^2$. -/
theorem placesOver_inert {v : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hdv : v.valuation F (d : F) = 1) (hnsq : ¬ IsSquare (algebraMap F (v.adicCompletion F) (d : F))) :
    ∃ w : HeightOneSpectrum (𝓞 K), placesOver (K := K) v = {w} ∧
      Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
  obtain ⟨w, hw⟩ := exists_place_over hb₀ hb₁ v
  have hns : ∀ c : v.adicCompletion F, ((d : F) : v.adicCompletion F) ≠ c * c := fun c h => hnsq ⟨c, h⟩
  refine ⟨w, ?_, ?_⟩
  · ext u
    simp only [mem_placesOver, Finset.mem_singleton]
    exact ⟨fun hu => place_unique_of_nonsq hb₀ hb₁ v hns u w hu hw, fun hu => hu ▸ hw⟩
  · have hK2 := finrank_eq_two_of_basis hb₀ hb₁
    haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hK2 }
    have hcomap : w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hw
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [Ideal.under_def, hcomap]⟩
    haveI := v.isMaximal
    haveI := w.isMaximal
    have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) := by
      rw [← Ideal.absNorm_relNorm (𝓞 F) (𝓞 K), Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal, map_pow]
    have hle := QuadFormsKB.QTwist.absNorm_le_sq_of_comap hK2 v w hcomap
    have hunder : QuadFormsKB.HN.under (F := F) w = v := HeightOneSpectrum.ext hcomap
    have hf1 : w.asIdeal.inertiaDeg (𝓞 F) ≠ 1 := by
      intro hf
      have hf' : (QuadFormsKB.HN.under (F := F) w).asIdeal.inertiaDeg' w.asIdeal = 1 := by
        rw [hunder, Ideal.inertiaDeg'_eq_inertiaDeg]; exact hf
      have hsqK : IsSquare (algebraMap K (w.adicCompletion K) (algebraMap F K (d : F))) :=
        ⟨algebraMap K (w.adicCompletion K) (bK 1), by rw [← map_mul, hb₁]⟩
      have := QuadFormsKB.PresNF.isSquare_down w hf' (by rw [hunder]; exact h2) (d : F) (by rw [hunder]; exact hdv) hsqK
      rw [hunder] at this
      exact hnsq this
    have hf0 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos w.asIdeal (𝓞 F)
    have hp : 2 ≤ Ideal.absNorm v.asIdeal := QuadFormsKB.NFEuler.two_le_normP v
    have hf2 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 2 := by
      by_contra h
      push_neg at h
      rw [hnorm] at hle
      have h3 : Ideal.absNorm v.asIdeal ^ 2 < Ideal.absNorm v.asIdeal ^ w.asIdeal.inertiaDeg (𝓞 F) :=
        Nat.pow_lt_pow_right (by omega) h
      omega
    rw [hnorm, show w.asIdeal.inertiaDeg (𝓞 F) = 2 by omega]

end Places

/-! ### The good-place identity and the regrouping -/

section Good

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {a b d : 𝓞 F}
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))

theorem not_mem_of_valued_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : 𝓞 F}
    (h : Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1) : x ∉ v.asIdeal := by
  intro hx
  have := (v.valuation_lt_one_iff_mem (K := F) x).2 hx
  rw [← valued_algebraMap] at this
  exact absurd h (ne_of_lt (by simpa using this))

include hb₀ hb₁ hα hβ in
/-- **The good-place identity** $\prod_{w\mid v}\alpha_w(\langle-\alpha,-\beta,\alpha\beta\rangle) = \alpha_v(\langle1,-ad,-bd,abd\rangle)$. -/
@[kb "kitaoka1993" "§5.6 (local densities at good places; SO^±(4,q)) [unverified]"]
theorem prod_siegelDensity_good {v : HeightOneSpectrum (𝓞 F)}
    (hv : NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) :
    ∏ w ∈ placesOver (K := K) v, NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β) =
      NF.siegelDensity v (qNS a b d) (qNS a b d) := by
  classical
  have hw : ∀ w ∈ placesOver (K := K) v, NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β) =
      1 - ((Ideal.absNorm w.asIdeal : ℝ) ^ 2)⁻¹ := by
    intro w hw
    obtain ⟨h2w, haw, hbw⟩ := nsGoodK hα hβ hv w ((mem_placesOver v).1 hw)
    rw [siegelDensity_pureFormO_good w h2w haw hbw, LocalDensity.NF.q_completion]
  obtain ⟨h2, ha, hb, hd, -⟩ := hv
  rw [Finset.prod_congr rfl hw, siegelDensity_qNS_good v h2 ha hb hd, LocalDensity.NF.q_completion]
  letI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
  have h2v : (2 : 𝓞 F) ∉ v.asIdeal := not_mem_of_valued_eq_one (by rw [show ((2 : 𝓞 F) : F) = (2 : F) from map_ofNat (algebraMap (𝓞 F) F) 2, map_ofNat]; exact h2)
  have hdv : v.valuation F (d : F) = 1 := by rw [← valued_algebraMap]; exact hd
  have h2d : 2 * d ∉ v.asIdeal := by
    refine not_mem_of_valued_eq_one ?_
    rw [show ((2 * d : 𝓞 F) : F) = 2 * (d : F) by rw [show ((2 * d : 𝓞 F) : F) = algebraMap (𝓞 F) F (2 * d) from rfl, map_mul, map_ofNat], map_mul, map_ofNat, map_mul, h2, hd, one_mul]
  have hι : ((LocalDensity.NF.ι v d : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (d : F) := coe_ι d
  have hdd : ¬ LocalDensity.NF.π v ∣ LocalDensity.NF.ι v d := not_dvd_of_valued_eq_one v (by rw [hι]; exact hd)
  have hres0 : IsLocalRing.residue (v.adicCompletionIntegers F) (LocalDensity.NF.ι v d) ≠ 0 := by
    intro h0
    rw [IsLocalRing.residue_eq_zero_iff, (LocalDensity.NF.irreducible_π v).maximalIdeal_eq,
      Ideal.mem_span_singleton] at h0
    exact hdd h0
  by_cases hsq : IsSquare (algebraMap F (v.adicCompletion F) (d : F))
  · have hissq : IsSquare (IsLocalRing.residue (v.adicCompletionIntegers F) (LocalDensity.NF.ι v d)) := by
      obtain ⟨z, hz⟩ := hsq
      have hzv : Valued.v z ≤ 1 := by
        have h1 : Valued.v z * Valued.v z = 1 := by rw [← map_mul, ← hz, hd]
        by_contra hc
        push_neg at hc
        have := one_lt_mul_of_lt_of_le hc hc.le
        rw [h1] at this; exact lt_irrefl _ this
      set zO : v.adicCompletionIntegers F := ⟨z, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hzv⟩
      have hzO : LocalDensity.NF.ι v d = zO * zO := Subtype.ext (by rw [hι, hz]; rfl)
      exact ⟨IsLocalRing.residue _ zO, by rw [hzO, map_mul]⟩
    rw [(quadraticChar_one_iff_isSquare hres0).2 hissq]
    obtain ⟨P, Q, hPQ, hPQs, hnP, hnQ⟩ := placesOver_split hb₀ hb₁ h2d hsq
    rw [hPQs, Finset.prod_pair hPQ, hnP, hnQ]
    push_cast; ring
  · have hnres : ¬ IsSquare (IsLocalRing.residue (v.adicCompletionIntegers F) (LocalDensity.NF.ι v d)) := by
      intro hr
      have e2 : ((2 : v.adicCompletionIntegers F) : v.adicCompletion F) = 2 := by push_cast; rfl
      have h2' : ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) :=
        not_dvd_of_valued_eq_one v (by rw [e2]; exact h2)
      obtain ⟨c, -, hc⟩ := QuadFormsKB.LocalZeta.exists_sq_of_residue_isSquare v h2'
        (LocalDensity.DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) hdd) hr
      exact hsq ⟨(c : v.adicCompletion F), by rw [← hι, hc]; push_cast; ring⟩
    rw [quadraticChar_neg_one_iff_not_isSquare.2 hnres]
    obtain ⟨w, hws, hnw⟩ := placesOver_inert hb₀ hb₁ h2v hdv hsq
    rw [hws, Finset.prod_singleton, hnw]
    push_cast; ring

/-- **The regrouping of the regularized products** $\prod'_w\alpha^{(3)}_w = \prod'_v\alpha^{(4)}_v\cdot\prod_{v\in S}\prod_{w\mid v}
\alpha^{(3)}_w/\alpha^{(4)}_v$ when the good-place identity holds off $S$. -/
theorem finFactor_regroup (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hQ : (qNS a b d).Nondegenerate)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, ∏ w ∈ placesOver (K := K) v,
      NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β) = NF.siegelDensity v (qNS a b d) (qNS a b d)) :
    finFactor (QuatZeta.pureFormO α β) (fun _ => 1) = finFactor (qNS a b d) (fun _ => 1) *
      ∏ v ∈ S, (∏ w ∈ placesOver (K := K) v,
        NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β)) /
          NF.siegelDensity v (qNS a b d) (qNS a b d) := by
  classical
  have hQ3 := nondegenerate_pureFormO α β hα0 hβ0
  rw [finFactor_one _ hQ3, finFactor_one _ hQ]
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun w => NF.siegelDensity w (QuatZeta.pureFormO α β) (QuatZeta.pureFormO α β)
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v => ∏ w ∈ placesOver (K := K) v, f w
  set h : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v (qNS a b d) (qNS a b d)
  have hf : Multipliable f := multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ3
  have hh : Multipliable h := multipliable_siegelDensity (by norm_num) (by norm_num) _ hQ
  let e : HeightOneSpectrum (𝓞 K) ≃ Σ v : HeightOneSpectrum (𝓞 F), PlaceSet (K := K) v :=
    { toFun := fun w => ⟨underPlace w, w, rfl⟩
      invFun := fun p => p.2.1
      left_inv := fun w => rfl
      right_inv := fun ⟨v, w, hw⟩ => by subst hw; rfl }
  have hg : HasProd g (∏' w, f w) := by
    have h1 : HasProd (f ∘ e.symm) (∏' w, f w) := (e.symm.hasProd_iff).2 hf.hasProd
    refine h1.sigma fun v => ?_
    have := hasProd_fintype (fun c : PlaceSet (K := K) v => f c.1)
    rw [prod_placeSet_eq v f] at this
    exact this
  rw [← hg.tprod_eq]
  have hne : ∀ v, h v ≠ 0 := fun v => (siegelDensity_self_pos' _ hQ v).ne'
  have hr : ∀ v ∉ S, g v / h v = 1 := fun v hv => by
    show (∏ w ∈ placesOver (K := K) v, f w) / h v = 1
    rw [hS v hv, div_self (hne v)]
  calc ∏' v, g v = ∏' v, (h v * (g v / h v)) := tprod_congr fun v => (mul_div_cancel₀ _ (hne v)).symm
    _ = (∏' v, h v) * ∏' v, (g v / h v) := hh.tprod_mul (multipliable_of_ne_finset_one hr)
    _ = _ := by rw [tprod_eq_prod hr]

end Good

end QuadFormsKB.Tamagawa.Measure.Weil
