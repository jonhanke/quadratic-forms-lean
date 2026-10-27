/-
# Weil's measure comparison for the non-square model over every number field

**Layer:** $F$ any number field, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$; $G^\natural$ = `gnatBCO`,
$P = G^\natural/\mathbb A_F^\times$, $\Phi$ = `nsPEquiv` : $P\cong SO(Q_0)(\mathbb A_F)$, $Q_0 = \langle1,-ad,-bd,abd\rangle$ (`qNS`).

* **`sigmaK_eq`**: the sphere measure $\sigma_K(A) = \prod_{w}\sigma_w(A_w)$ of the test set over $K$, regrouped over the
  places of $F$.
* **`nsAdele_image_nsS0U`**: $\Phi(\pi(S_0^U)) = U\times K''$ (image identity).
* **`map_muP_nsPEquiv_eq_muTam_any`**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for every model (no signature hypothesis).
* **`gnatMeasureComparisonNSIndef`**: the named input `GnatMeasureComparisonNSIndef F` holds for every number field $F$;
  hence `gnatMeasureComparison` and `gnatTamagawaComparison` (the structures `GnatMeasureComparison F`,
  `GnatTamagawaComparison F`).

*Proof* (Weil 1982, Thm 2.3.1). Haar uniqueness on the measurable test set
$E = U\times K''$ (`eq_of_eq_on_measurable`). $P$ side: the fibrations along $\pi$ and $p$ (`muP_nsS0U_mul_of_meas`), the sign
decomposition of the norm-one part (`muSL1N_X1set`), the cone over $K$ (`muSL1N_Hcone_mul`, `omegaQuatInf_archCone_eq`), the
finite factor (`rF_eq_div_quatCongS`, `rF_toReal_eq_kInf`). $SO$ side: `muArchTamSO_pi` and the local ratios
(`leray_URset_split`, `leray_URset_ns`, `leray_UCset`). The finite identity `fin_identity_ns`, the shells
(`omegaInf_BinfPos`) and the constant identity `const_identity_ns_any` close the computation.

Source: Weil 1982, §2.3, Thm 2.3.1, §3.7, pp. 64-65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSSignDecomp
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSShellRatio
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSConstAny
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFiniteAny
import QuadFormsKB.Tamagawa.Measure.Weil.GnatComparisonAny

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  IsDedekindDomain
open scoped ENNReal NNReal Quaternion ComplexConjugate

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex
  SphereLeray SphereLerayC

/-! ### The sphere measure of the test set over $K$, regrouped over $F$ -/

section Sigma

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))

variable (a b) in
/-- $\sigma(Y)$ at a real place with $d_v>0$ (one factor). -/
def sRv (v : {v : InfinitePlace F // v.IsReal}) : ℝ≥0∞ :=
  sig (NSArch.normForm (embedding_of_isReal v.2 (a : F)) (embedding_of_isReal v.2 (b : F))) 1 (NSArch.posR _ _)

variable (a b) in
/-- $\sigma_{\mathbb C}(Y)$ at a real place with $d_v<0$. -/
def sCv (v : {v : InfinitePlace F // v.IsReal}) : ℝ≥0∞ :=
  sigC (NSArch.normForm ((embedding_of_isReal v.2 (a : F) : ℝ) : ℂ) ((embedding_of_isReal v.2 (b : F) : ℝ) : ℂ)) 1
    (NSArch.posC _ _)

variable (a b) in
/-- $\sigma_{\mathbb C}(Y)$ at a complex place (one factor). -/
def sCCv (v : {v : InfinitePlace F // v.IsComplex}) : ℝ≥0∞ :=
  sigC (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))) 1 (NSArch.posC _ _)

variable (a b d) in
open Classical in
/-- The local sphere measure as a function on all infinite places of $F$. -/
def sPlace (v : InfinitePlace F) : ℝ≥0∞ :=
  if h : v.IsReal then (if 0 < embedding_of_isReal h (d : F) then sRv a b ⟨v, h⟩ else sCv a b ⟨v, h⟩)
  else sCCv a b ⟨v, not_isReal_iff_isComplex.1 h⟩

theorem embedding_real_algebraMap (w : {w : InfinitePlace K // w.IsReal}) (x : F) :
    embedding_of_isReal w.2 (algebraMap F K x) =
      embedding_of_isReal (IsReal.comap (algebraMap F K) w.2) x := by
  apply Complex.ofReal_injective
  rw [embedding_of_isReal_apply, embedding_of_isReal_apply, comap_embedding_of_isReal _ (IsReal.comap _ w.2)]
  rfl

theorem embedding_cx_algebraMap_of_real (w : InfinitePlace K) (hv : (w.comap (algebraMap F K)).IsReal) (x : F) :
    w.embedding (algebraMap F K x) = ((embedding_of_isReal hv x : ℝ) : ℂ) := by
  rw [embedding_of_isReal_apply, comap_embedding_of_isReal _ hv]
  rfl

include hα hβ in
theorem sig_ARK_eq (w : {w : InfinitePlace K // w.IsReal}) :
    sig (QRe (qSq α β) w) 1 (ARK α β w) = sRv a b ⟨_, IsReal.comap (algebraMap F K) w.2⟩ := by
  have e : NSArch.normForm (embedding_of_isReal w.2 (α : K)) (embedding_of_isReal w.2 (β : K)) =
      NSArch.normForm (embedding_of_isReal (IsReal.comap (algebraMap F K) w.2) (a : F))
        (embedding_of_isReal (IsReal.comap (algebraMap F K) w.2) (b : F)) := by
    rw [hα, hβ, embedding_real_algebraMap, embedding_real_algebraMap]
  rw [ARK, sig_congr_val (QRe_qSq α β w), sig_congr_val e, sRv, posR_eq]

include hα hβ in
theorem sigC_ACK_eq_of_real (w : {w : InfinitePlace K // w.IsComplex}) (hv : (w.1.comap (algebraMap F K)).IsReal) :
    sigC (QCx (qSq α β) w) 1 (ACK α β w) = sCv a b ⟨_, hv⟩ := by
  have e : NSArch.normForm (w.1.embedding (α : K)) (w.1.embedding (β : K)) =
      NSArch.normForm ((embedding_of_isReal hv (a : F) : ℝ) : ℂ) ((embedding_of_isReal hv (b : F) : ℝ) : ℂ) := by
    rw [hα, hβ, embedding_cx_algebraMap_of_real, embedding_cx_algebraMap_of_real]
  rw [ACK, sigC_congr_val (QCx_qSq α β w), sigC_congr_val e, sCv, posC_eq]

include hα hβ in
theorem sigC_ACK_eq_of_cx (w : {w : InfinitePlace K // w.IsComplex}) (hv : (w.1.comap (algebraMap F K)).IsComplex) :
    sigC (QCx (qSq α β) w) 1 (ACK α β w) = sCCv a b ⟨_, hv⟩ := by
  rcases (embedding_comp_eq_or_conj w.1 hv).1 with h | h
  · have e : NSArch.normForm (w.1.embedding (α : K)) (w.1.embedding (β : K)) =
        NSArch.normForm ((w.1.comap (algebraMap F K)).embedding (a : F))
          ((w.1.comap (algebraMap F K)).embedding (b : F)) := by
      rw [hα, hβ]; exact congrArg₂ NSArch.normForm (RingHom.congr_fun h _) (RingHom.congr_fun h _)
    rw [ACK, sigC_congr_val (QCx_qSq α β w), sigC_congr_val e, sCCv, posC_eq]
  · have e : NSArch.normForm (w.1.embedding (α : K)) (w.1.embedding (β : K)) =
        NSArch.normForm (conj ((w.1.comap (algebraMap F K)).embedding (a : F)))
          (conj ((w.1.comap (algebraMap F K)).embedding (b : F))) := by
      rw [hα, hβ]; exact congrArg₂ NSArch.normForm (RingHom.congr_fun h _) (RingHom.congr_fun h _)
    rw [ACK, sigC_congr_val (QCx_qSq α β w), sigC_congr_val e, ← posC_eq, sigC_posC_conj, sCCv]

open scoped Classical in
include hb₀ hb₁ hα hβ in
/-- **$\sigma_K(A)$ regrouped over the places of $F$.** -/
theorem sigmaK_eq :
    (∏ w : {w : InfinitePlace K // w.IsReal}, sig (QRe (qSq α β) w) 1 (ARK α β w)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, sigC (QCx (qSq α β) w) 1 (ACK α β w) =
      (∏ v : {v : InfinitePlace F // v.IsReal},
        (if 0 < embedding_of_isReal v.2 (d : F) then sRv a b v ^ 2 else sCv a b v)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, sCCv a b v ^ 2 := by
  classical
  have hR : ∀ w : {w : InfinitePlace K // w.IsReal}, sig (QRe (qSq α β) w) 1 (ARK α β w) =
      sPlace a b d (w.1.comap (algebraMap F K)) := fun w => by
    have hv := IsReal.comap (algebraMap F K) w.2
    have hpos : 0 < embedding_of_isReal hv (d : F) := by
      rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne (d_ne_zero bK hb₁) ⟨_, hv⟩) with h | h
      · exact (not_real_over_ns hb₀ hb₁ ⟨_, hv⟩ h w rfl).elim
      · exact h
    rw [sig_ARK_eq hα hβ, sPlace, dif_pos hv, if_pos hpos]
  have hC : ∀ w : {w : InfinitePlace K // w.IsComplex}, sigC (QCx (qSq α β) w) 1 (ACK α β w) =
      sPlace a b d (w.1.comap (algebraMap F K)) := fun w => by
    by_cases hv : (w.1.comap (algebraMap F K)).IsReal
    · have hneg : ¬ 0 < embedding_of_isReal hv (d : F) := fun h =>
        not_complex_over_split hb₀ hb₁ ⟨_, hv⟩ h w rfl
      rw [sigC_ACK_eq_of_real hα hβ w hv, sPlace, dif_pos hv, if_neg hneg]
    · have hv' := not_isReal_iff_isComplex.1 hv
      rw [sigC_ACK_eq_of_cx hα hβ w hv', sPlace, dif_neg hv]
  rw [Finset.prod_congr rfl fun w _ => hR w, Finset.prod_congr rfl fun w _ => hC w,
    prod_real_comap bK hb₀ hb₁, prod_complex_comap bK hb₀ hb₁, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    by_cases h : 0 < embedding_of_isReal v.2 (d : F)
    · rw [if_pos h, if_pos h, if_pos h, mul_one, sPlace, dif_pos v.2, if_pos h]
    · rw [if_neg h, if_neg h, if_neg h, one_mul, sPlace, dif_pos v.2, if_neg h]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [sPlace, dif_neg (not_isReal_iff_isComplex.2 v.2)]

end Sigma

/-! ### The image identity -/

section Image

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (S : Finset (HeightOneSpectrum (𝓞 F)))
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0

/-- **The image identity** $\Phi(\pi(S_0^U)) = U\times K''$. -/
theorem nsAdele_image_nsS0U (hb0 : (b : F) ≠ 0) (hint : ∀ i, IsIntegral ℤ (bK i))
    (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) (U : Set (GInfSO (qNS a b d))) :
    nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 ''
        nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 U =
      U ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := by
  have himg := nsAdele_image_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK mK hmK1 hb0 hint hSK hgood
  ext X
  constructor
  · rintro ⟨g, ⟨hg, hgU⟩, rfl⟩
    have h2 : nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 g ∈
        univ ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := by
      rw [← himg]; exact ⟨g, hg, rfl⟩
    exact ⟨hgU, h2.2⟩
  · rintro ⟨hX1, hX2⟩
    have : X ∈ univ ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := ⟨mem_univ _, hX2⟩
    rw [← himg] at this
    obtain ⟨g, hg, rfl⟩ := this
    exact ⟨g, ⟨hg, hX1⟩, rfl⟩

include hb₀ hα0 hβ0 in
theorem isOpen_boxSO_ns (hb0 : (b : F) ≠ 0) (hint : ∀ i, IsIntegral ℤ (bK i))
    (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) :
    IsOpen (Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)) := by
  have himg := nsAdele_image_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK mK hmK1 hb0 hint hSK hgood
  have ho : IsOpen ((univ : Set (GInfSO (qNS a b d))) ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)) := by
    rw [← himg]
    exact isOpenMap_nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hb0 hd0 _
      (isOpen_nsS0 hb₀ hα0 hβ0 ((isOpen_quatCongS SK mK hmK1).preimage (continuous_quatFinPart α β)))
  have := isOpenMap_snd _ ho
  rwa [Set.snd_image_prod Set.univ_nonempty] at this

include hb₀ hα0 hβ0 in
theorem boxSO_ns_nonempty (hb0 : (b : F) ≠ 0) (hint : ∀ i, IsIntegral ℤ (bK i))
    (hSK : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S)
    (hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v) :
    (Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1)).Nonempty := by
  have himg := nsAdele_image_nsS0 hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK mK hmK1 hb0 hint hSK hgood
  have h1 : nsAdele hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 1 ∈
      univ ×ˢ Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 mK hmK1) := by
    rw [← himg]; exact ⟨1, (nsS0 hb₀ hα0 hβ0 (HS α β SK mK hmK1)).one_mem, rfl⟩
  exact ⟨_, h1.2⟩

end Image

/-! ### The local Leray measures in the shape of the constant identity -/

section LerayShape

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))

open Classical in
theorem leray_URset_eq (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (v : {v : InfinitePlace F // v.IsReal}) :
    lerayMeasure (QRe (qNS a b d) v) (gramDetR_QRe_ne_zero _ hQ v) (URset (a := a) (b := b) hb₀ hb₁ v) =
      ENNReal.ofReal (nsKappaR (a : F) (b : F) (d : F) v) *
        (if 0 < embedding_of_isReal v.2 (d : F) then sRv a b v ^ 2 else sCv a b v) := by
  by_cases h : 0 < embedding_of_isReal v.2 (d : F)
  · rw [leray_URset_split hb₀ hb₁ ha0 hb0 hd0 hQ v h, nsKappaR, if_pos h, if_pos h, sRv]
  · have h' : embedding_of_isReal v.2 (d : F) < 0 :=
      lt_of_le_of_ne (not_lt.1 h) (ne_zero_of_algebraMap_ne hd0 v)
    rw [leray_URset_ns hb₀ hb₁ ha0 hb0 hd0 hQ v h', nsKappaR, if_neg h, if_neg h, sCv]

theorem leray_UCset_eq (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (hQ : (qNS a b d).Nondegenerate) (v : {v : InfinitePlace F // v.IsComplex}) :
    lerayMeasureC (QCx (qNS a b d) v) (gramDetC_QCx_ne_zero _ hQ v) (UCset (a := a) (b := b) hb₀ hb₁ v) =
      ENNReal.ofReal (nsKappaC (a : F) (b : F) (d : F) v) * sCCv a b v ^ 2 := by
  rw [leray_UCset hb₀ hb₁ ha0 hb0 hd0 hQ v, nsKappaC, sCCv]

theorem sRv_ne_top (v : {v : InfinitePlace F // v.IsReal}) : sRv a b v ≠ ⊤ := NSArch.sig_posR_ne_top
theorem sCv_ne_top (v : {v : InfinitePlace F // v.IsReal}) : sCv a b v ≠ ⊤ := NSArch.sigC_posC_ne_top
theorem sCCv_ne_top (v : {v : InfinitePlace F // v.IsComplex}) : sCCv a b v ≠ ⊤ := NSArch.sigC_posC_ne_top
theorem sRv_ne_zero (v : {v : InfinitePlace F // v.IsReal}) : sRv a b v ≠ 0 := NSArch.sig_posR_pos.ne'
theorem sCv_ne_zero (v : {v : InfinitePlace F // v.IsReal}) : sCv a b v ≠ 0 := NSArch.sigC_posC_pos.ne'
theorem sCCv_ne_zero (v : {v : InfinitePlace F // v.IsComplex}) : sCCv a b v ≠ 0 := NSArch.sigC_posC_pos.ne'

theorem nsKappaR_pos (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (v : {v : InfinitePlace F // v.IsReal}) : 0 < nsKappaR (a : F) (b : F) (d : F) v := by
  have hA := abs_pos.2 (ne_zero_of_algebraMap_ne ha0 v)
  have hB := abs_pos.2 (ne_zero_of_algebraMap_ne hb0 v)
  have hD := Real.rpow_pos_of_pos (abs_pos.2 (ne_zero_of_algebraMap_ne hd0 v)) ((15 : ℝ) / 2)
  unfold nsKappaR
  split_ifs <;> positivity

theorem nsKappaC_pos (ha0 : (a : F) ≠ 0) (hb0 : (b : F) ≠ 0) (hd0 : (d : F) ≠ 0)
    (v : {v : InfinitePlace F // v.IsComplex}) : 0 < nsKappaC (a : F) (b : F) (d : F) v := by
  have hA := norm_pos_iff.2 ((map_ne_zero v.1.embedding).2 ha0)
  have hB := norm_pos_iff.2 ((map_ne_zero v.1.embedding).2 hb0)
  have hD := Real.rpow_pos_of_pos (norm_pos_iff.2 ((map_ne_zero v.1.embedding).2 hd0)) (15 : ℝ)
  unfold nsKappaC
  positivity

end LerayShape


/-- The real-number bookkeeping of the assembly. -/
theorem ns_final_algebra {p wv uf n2 slc wb nf wk nh e8 sk qh kI uk m3 R m4 c2 : ℝ}
    (hwv : 0 < wv) (huf : 0 < uf) (hnh : 0 < nh) (hwk : 0 < wk)
    (E1 : p * (wv * uf) = n2 * slc * (wb * nf)) (E2 : slc * (wk * nh) = e8 * sk * wk * qh)
    (E3 : qh = kI * (uk * m3)) (E4 : m3 * nf * uk = R * m4 * nh * uf) (E5 : wb = c2 * wv) :
    p = n2 * e8 * kI * R * c2 * sk * m4 := by
  have E2' : slc * nh = e8 * sk * qh := by
    have h : (slc * nh - e8 * sk * qh) * wk = 0 := by linear_combination E2
    have := (mul_eq_zero.1 h).resolve_right hwk.ne'
    linarith
  have key : (p - n2 * e8 * kI * R * c2 * sk * m4) * (wv * uf * nh) = 0 := by
    linear_combination nh * E1 + (n2 * wb * nf) * E2' + (n2 * wb * nf * e8 * sk) * E3 +
      (n2 * nf * e8 * sk * kI * uk * m3) * E5 + (n2 * c2 * wv * e8 * sk * kI) * E4
  have hpos : wv * uf * nh ≠ 0 := by positivity
  have := (mul_eq_zero.1 key).resolve_right hpos
  linarith

/-! ### The comparison -/

section Main

variable {F : Type} [Field F] [NumberField F]

set_option maxHeartbeats 16000000 in
open scoped Classical in
/-- **Weil's measure comparison $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the non-square model, every number field, every model**
(no signature hypothesis). -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, product formula); §3.7, pp. 64-65 [unverified page]"]
theorem map_muP_nsPEquiv_eq_muTam_any (a b d : 𝓞 F) (K : Type) [Field K] [NumberField K] [Algebra F K]
    (bK : Module.Basis (Fin 2) F K) (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
    (α β : 𝓞 K) (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (hQ : (qNS a b d).Nondegenerate) :
    ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map
      (nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) (ne_zero_of_algebraMap_eq hα hα0)
        (ne_zero_of_algebraMap_eq hβ hβ0) (d_ne_zero_of_basis hb₁)) = muTam (qNS a b d) hQ (fun _ => 1) := by
  have ha0 : (a : F) ≠ 0 := ne_zero_of_algebraMap_eq hα hα0
  have hb0 : (b : F) ≠ 0 := ne_zero_of_algebraMap_eq hβ hβ0
  have hd0 : (d : F) ≠ 0 := d_ne_zero_of_basis hb₁
  have hint := isIntegral_basis hb₀ hb₁
  set S := nsBad (bK := bK) ha0 hb0 hd0 with hSdef
  set SK := nsBadK (K := K) S with hSKdef
  set m := nsLevK hα0 hβ0
  have hm1 : ∀ w, 1 ≤ m w := one_le_nsLevK hα0 hβ0
  have hSKiff : ∀ w, w ∈ SK ↔ underPlace (k := F) w ∈ S := fun w => mem_nsBadK
  have hgood : ∀ v ∉ S, NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := fun v hv => nsGood_of_not_mem bK hv
  have hSKg : ∀ w ∉ SK, Valued.v (2 : w.adicCompletion K) = 1 ∧
      Valued.v (algebraMap K (w.adicCompletion K) (α : K)) = 1 ∧
        Valued.v (algebraMap K (w.adicCompletion K) (β : K)) = 1 := fun w hw =>
    nsGoodK hα hβ (hgood _ (fun h => hw ((hSKiff w).2 h))) w rfl
  have hmS : ∀ w ∈ SK, 2 * sExp w < m w ∧ sExp w + eExp α hα0 w ≤ m w := fun w _ => nsLevK_cond hα0 hβ0 w
  set Φ := nsPEquiv hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hb0 hd0 with hΦdef
  set U := Uarch a b hb₀ hb₁ with hUdef
  have hUm : MeasurableSet U := measurableSet_Uarch hb₀ hb₁ ha0 hd0
  set S₀ := nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK m hm1 U with hS₀def
  set box := Measure.boxSO (qNS a b d) S (nsU hb₁ hα hβ ha0 hd0 m hm1) with hboxdef
  have hboxo : IsOpen box := isOpen_boxSO_ns hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood
  have hEm : MeasurableSet (U ×ˢ box) := hUm.prod hboxo.measurableSet
  -- the image identity
  have hΦE : Φ '' ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀) = U ×ˢ box := by
    rw [Set.image_image]
    exact nsAdele_image_nsS0U hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood U
  have hpre : Φ ⁻¹' (U ×ˢ box) = (gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀ := by
    rw [← hΦE]; exact Φ.injective.preimage_image _
  have hπm : MeasurableSet ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀) := by
    rw [← hpre]; exact hEm.preimage Φ.continuous.measurable
  -- positivity at the real places
  have hpos : ∀ g : (gnatBCO bK 0 hb₀ hα0 hβ0).G, g ∈ S₀ →
      ∀ v : {v : InfinitePlace F // v.IsReal},
        0 < ((g : (QuatAdele (α : K) (β : K))ˣ × (Adeles F)ˣ).2 : Adeles F).1.1 v := fun g hg v => by
    have hU := (mem_Uarch_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 g).1 hg.2
    exact pos_of_nsR_mem_URset hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 v g (hU.1 v)
  -- the P side
  have e1 := muP_nsS0U_mul_of_meas hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK m hm1 U hUm hπm hpos S hSKiff hSKg
  change _ = muSL1N hα0 hβ0 (X1set hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK m hm1) * _ at e1
  rw [muSL1N_X1set hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK m hm1] at e1
  have hTRm : ∀ w, MeasurableSet (TRd (F := K) w) := fun _ => measurableSet_Ioo
  have hTCm : ∀ w, MeasurableSet (TCd (F := K) w) := fun w => (isOpen_TCd w).measurableSet
  have h0 : ∀ w, (0 : ℝ) ∈ TRd (F := K) w := fun _ => ⟨by norm_num, by norm_num⟩
  have e2 := muSL1N_Hcone_mul SK m hm1 (TRd (F := K)) (ARK α β) (TCd (F := K)) (ACK α β) hα0 hβ0 hSKg hTRm
    measurableSet_ARK hTCm TCd_subset measurableSet_ACK h0 one_mem_TCd
  rw [omegaQuatInf_archCone_eq (fun w => QRe (qSq α β) w) (fun w => QCx (qSq α β) w) eval_quatCoordR eval_quatCoordC
    (TRd (F := K)) (ARK α β) (TCd (F := K)) (ACK α β) hTRm measurableSet_ARK hTCm TCd_subset measurableSet_ACK] at e2
  change muSL1N hα0 hβ0 (HconeSL SK m hm1) * _ = _ at e2
  have e3 := rF_eq_div_quatCongS SK m hm1 hα0 hβ0 hSKg hmS
  have e4 := fin_identity_ns hb₀ hb₁ hα hβ hα0 hβ0 ha0 hb0 hd0 hQ hint
  have e5 := omegaInf_BinfPos (F := F)
  have e6 := const_identity_ns_any bK hb₀ hb₁ hα hβ ha0 hb0 hd0
  have e7 := rF_toReal_eq_kInf α β hα0 hβ0
  have e8 := sigmaK_eq hb₀ hb₁ hα hβ
  -- finiteness and positivity
  have hωV0 : omegaInf F (Vone (F := F)) ≠ 0 := omegaInf_Vone_ne_zero
  have hωVt : omegaInf F (Vone (F := F)) ≠ ⊤ := omegaInf_Vone_ne_top
  have hUF0 : muFinUnits F (OHatUnits F) ≠ 0 := muFinUnits_OHatUnits_ne_zero
  have hUFt : muFinUnits F (OHatUnits F) ≠ ⊤ := muFinUnits_OHatUnits_ne_top
  have hUK0 : muFinUnits K (OHatUnits K) ≠ 0 := muFinUnits_OHatUnits_ne_zero
  have hUKt : muFinUnits K (OHatUnits K) ≠ ⊤ := muFinUnits_OHatUnits_ne_top
  have hωBt : omegaInf F (BinfPos (F := F)) ≠ ⊤ := omegaInf_BinfPos_ne_top
  have hωK0 : omegaInf K (nrdShell K (TRd (F := K)) TCd) ≠ 0 := omegaInf_nrdShell_d_ne_zero
  have hωKt : omegaInf K (nrdShell K (TRd (F := K)) TCd) ≠ ⊤ := omegaInf_nrdShell_d_ne_top
  have hbox_sub : ideleBox S (nsN α β m hm1) ⊆ (OHatUnits F : Set (FiniteAdeleRing (𝓞 F) F)ˣ) := by
    intro g hg
    rw [← ideleBox_empty (nsN α β m hm1)]
    intro v
    have := hg v
    simp only [Finset.notMem_empty, ite_false]
    split_ifs at this with hv
    · exact nsN_subset' hb₀ hb₁ m hm1 v this
    · exact this
  have hNFt : muFinUnits F (ideleBox S (nsN α β m hm1)) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hbox_sub) (lt_of_le_of_ne le_top hUFt))
  have hNHt : muFinUnits K (NH α β SK m hm1) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (measure_mono (NH_subset_OHatUnits SK m hm1))
    (lt_of_le_of_ne le_top hUKt))
  have hNH0 : muFinUnits K (NH α β SK m hm1) ≠ 0 := by
    rw [show muFinUnits K (NH α β SK m hm1) = muFinUnits K (OHatUnits K) *
        ∏ w ∈ SK, omegaV w (nL α β m hm1 w) / omegaV w (unitsVSub w) from
      muFinUnits_ideleBox_of_measurable SK _ fun w _ => measurableSet_nL m hm1 w]
    refine mul_ne_zero hUK0 (Finset.prod_ne_zero_iff.2 fun w _ => ?_)
    exact (ENNReal.div_pos (omegaV_nL_ne_zero m hm1 hα0 w) (omegaV_unitsVSub_ne_top w)).ne'
  have hqH0 := muFinQuat_quatCongS_ne_zero SK m hm1 hα0 hβ0
  have hqHt := muFinQuat_quatCongS_ne_top (a := α) (b := β) SK m hm1
  have hM3t := muFin_box_ne_top SK m hm1 (QuatZeta.pureFormO α β)
  have hk := kInf_pos α β hα0 hβ0
  have hrFt : rF α β ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at e7; linarith
  have hM30 : QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO α β) (fun _ => 1)
      (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO α β) SK (congSO3S (a := α) (b := β) m hm1)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, ENNReal.div_zero hqH0] at e3
    exact hrFt e3
  have e3' : muFinQuat (α : K) (β : K) (quatCongS α β SK m hm1) = rF α β * (muFinUnits K (OHatUnits K) *
      QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO α β) (fun _ => 1)
        (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO α β) SK (congSO3S (a := α) (b := β) m hm1))) := by
    rw [e3, ENNReal.div_mul_cancel (mul_ne_zero hUK0 hM30) (ENNReal.mul_ne_top hUKt hM3t)]
  -- the sphere measures
  rw [e8] at e2
  set σF : ℝ≥0∞ := (∏ v : {v : InfinitePlace F // v.IsReal},
      (if 0 < embedding_of_isReal v.2 (d : F) then sRv a b v ^ 2 else sCv a b v)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, sCCv a b v ^ 2 with hσF
  have hσt : σF ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun v _ => ?_) (ENNReal.prod_ne_top fun v _ =>
      ENNReal.pow_ne_top (sCCv_ne_top v))
    split_ifs
    · exact ENNReal.pow_ne_top (sRv_ne_top v)
    · exact sCv_ne_top v
  have hσ0 : σF ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ => ?_) (Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero 2 (sCCv_ne_zero v))
    split_ifs
    · exact pow_ne_zero 2 (sRv_ne_zero v)
    · exact sCv_ne_zero v
  have hFF : 0 < QuadFormsKB.Tamagawa.Measure.finFactor (qNS a b d) (fun _ => 1) := by
    rw [QuadFormsKB.Tamagawa.Measure.finFactor_one (qNS a b d) hQ]
    exact tprod_siegelDensity_pos (by norm_num) (qNS a b d) hQ
  have hM40 : QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1) box ≠ 0 := by
    have hc : Real.toNNReal (QuadFormsKB.Tamagawa.Measure.finFactor (qNS a b d) (fun _ => 1)) ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hFF
    have : IsHaarMeasure (QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1)) := by
      unfold QuadFormsKB.Tamagawa.Measure.muFin haarNorm; exact IsHaarMeasure.nnreal_smul _ hc
    exact (hboxo.measure_pos _ (boxSO_ns_nonempty hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood)).ne'
  have hL3t : ∀ w, Measure.muLocSO w (QuatZeta.pureFormO α β) 1 (congSO3S (a := α) (b := β) m hm1 w) ≠ ∞ := by
    intro w
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun x hx => ?_)) (by
      rw [Measure.muLocSO_soStabSO]; exact ENNReal.ofReal_lt_top))
    exact LerayPadic.congSub_le_stdStab w _ (m w) (hm1 w) hx
  have hUvt : ∀ v ∈ S, Measure.muLocSO v (qNS a b d) 1 (nsU hb₁ hα hβ ha0 hd0 m hm1 v) ≠ ∞ := by
    intro v hv
    have hv' : ¬ NSGoodPlace (bK := bK) (a := a) (b := b) (d := d) v := (Set.Finite.mem_toFinset _).1 hv
    have h := nsBadPlaceRatio_any a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 v hv'
    have hl : (∏ w ∈ placesOver (K := K) v, Measure.muLocSO w (QuatZeta.pureFormO α β) 1
        (congSO3S (a := α) (b := β) m hm1 w) * omegaV w (unitsVSub w) / omegaV w (nL α β m hm1 w)) *
          (omegaV v (nsN α β m hm1 v) / omegaV v (unitsVSub v)) ≠ ∞ := by
      refine ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => ENNReal.div_ne_top
        (ENNReal.mul_ne_top (hL3t w) (omegaV_unitsVSub_ne_top w)) (omegaV_nL_ne_zero m hm1 hα0 w))
        (ENNReal.div_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono (nsN_subset' hb₀ hb₁ m hm1 v))
          (lt_of_le_of_ne le_top (omegaV_unitsVSub_ne_top v)))) (omegaV_unitsVSub_ne_zero v))
    rw [h] at hl
    intro htop
    exact hl (by rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (nsRatio_pos_any ha0 hb0 hd0 v)).ne'])
  have hUo : ∀ v ∈ S, MeasurableSet (nsU hb₁ hα hβ ha0 hd0 m hm1 v) := fun v hv =>
    (isOpen_nsU hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 S SK m hm1 hb0 hint hSKiff hgood hv).measurableSet
  have hM4t : QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1) box ≠ ⊤ := by
    rw [hboxdef, QuadFormsKB.Tamagawa.Measure.muFin_boxSO (qNS a b d) hQ (fun _ => one_pos) S _ hUo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun v hv =>
      ENNReal.div_ne_top (hUvt v hv) (Measure.muLocSO_soStabSO_pos (qNS a b d) hQ v one_pos))
  -- the SO side
  have hSO : muTam (qNS a b d) hQ (fun _ => 1) (U ×ˢ box) =
      ENNReal.ofReal (cF F 4 * cxWeil F 4) *
        ((∏ v : {v : InfinitePlace F // v.IsReal}, ENNReal.ofReal (nsKappaR (a : F) (b : F) (d : F) v) *
          (if 0 < embedding_of_isReal v.2 (d : F) then sRv a b v ^ 2 else sCv a b v)) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, ENNReal.ofReal (nsKappaC (a : F) (b : F) (d : F) v) *
          sCCv a b v ^ 2) * QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1) box := by
    rw [muTam, Measure.prod_prod, hUdef]
    unfold Uarch
    rw [muArchTamSO_pi]
    congr 3
    · exact Finset.prod_congr rfl fun v _ => leray_URset_eq hb₀ hb₁ ha0 hb0 hd0 hQ v
    · exact Finset.prod_congr rfl fun v _ => leray_UCset_eq hb₀ hb₁ ha0 hb0 hd0 hQ v
  have hκR : ∀ v, 0 ≤ nsKappaR (a : F) (b : F) (d : F) v := fun v => (nsKappaR_pos ha0 hb0 hd0 v).le
  have hκC : ∀ v, 0 ≤ nsKappaC (a : F) (b : F) (d : F) v := fun v => (nsKappaC_pos ha0 hb0 hd0 v).le
  have hcc : 0 < cF F 4 * cxWeil F 4 :=
    mul_pos (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))) _) cxWeil_pos
  have hSO' : muTam (qNS a b d) hQ (fun _ => 1) (U ×ˢ box) =
      ENNReal.ofReal (cF F 4 * cxWeil F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal}, nsKappaR (a : F) (b : F) (d : F) v) *
        ∏ v : {v : InfinitePlace F // v.IsComplex}, nsKappaC (a : F) (b : F) (d : F) v)) * σF *
        QuadFormsKB.Tamagawa.Measure.muFin (qNS a b d) (fun _ => 1) box := by
    rw [hSO, Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun v _ => hκR v),
      ← ENNReal.ofReal_prod_of_nonneg (fun v _ => hκC v), ENNReal.ofReal_mul hcc.le,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ => hκR v), hσF]
    ring
  have hCpos : 0 < cF F 4 * cxWeil F 4 * ((∏ v : {v : InfinitePlace F // v.IsReal}, nsKappaR (a : F) (b : F) (d : F) v) *
      ∏ v : {v : InfinitePlace F // v.IsComplex}, nsKappaC (a : F) (b : F) (d : F) v) :=
    mul_pos hcc (mul_pos (Finset.prod_pos fun v _ => nsKappaR_pos ha0 hb0 hd0 v)
      (Finset.prod_pos fun v _ => nsKappaC_pos ha0 hb0 hd0 v))
  have hSOt : muTam (qNS a b d) hQ (fun _ => 1) (U ×ˢ box) ≠ ⊤ := by
    rw [hSO']; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσt) hM4t
  have hSO0 : muTam (qNS a b d) hQ (fun _ => 1) (U ×ˢ box) ≠ 0 := by
    rw [hSO']; exact mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.2 hCpos).ne' hσ0) hM40
  -- finiteness of the P side
  have hSLt : muSL1N hα0 hβ0 (HconeSL SK m hm1) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_mul (mul_ne_zero hωK0 hNH0)] at e2
    exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hσt)
      hωKt) hqHt) e2.symm
  have hPt : (gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0) ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_mul (mul_ne_zero hωV0 hUF0)] at e1
    exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hSLt)
      (ENNReal.mul_ne_top hωBt hNFt)) e1.symm
  -- the real identity
  have E1 := congrArg ENNReal.toReal e1
  have E2 := congrArg ENNReal.toReal e2
  have E3 := congrArg ENNReal.toReal e3'
  have E5 := congrArg ENNReal.toReal e5
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at E1 E2 E3 E5
  rw [e7] at E3
  have hPr : ((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0) ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀)).toReal =
      (muTam (qNS a b d) hQ (fun _ => 1) (U ×ˢ box)).toReal := by
    rw [hSO', ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le, ← e6]
    exact ns_final_algebra (ENNReal.toReal_pos hωV0 hωVt) (ENNReal.toReal_pos hUF0 hUFt)
      (ENNReal.toReal_pos hNH0 hNHt) (ENNReal.toReal_pos hωK0 hωKt) E1 E2 E3 e4 E5
  have hPeq := (ENNReal.toReal_eq_toReal_iff' hPt hSOt).1 hPr
  -- Haar uniqueness on the test set
  have hmap : (((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ) (U ×ˢ box) =
      (gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0) ((gnatBCO bK 0 hb₀ hα0 hβ0).π '' S₀) := by
    rw [Measure.map_apply (map_continuous Φ).measurable hEm, hpre]
  have := (gnatBCO bK 0 hb₀ hα0 hβ0).isHaarMeasure_muP (muBC bK 0 hb₀ hα0 hβ0)
  have : (((gnatBCO bK 0 hb₀ hα0 hβ0).muP (muBC bK 0 hb₀ hα0 hβ0)).map Φ).IsHaarMeasure := Φ.isHaarMeasure_map _
  refine eq_of_eq_on_measurable _ _ (U := U ×ˢ box) ?_ ?_ ?_
  · rw [hmap, hPeq]; exact hSO0
  · rw [hmap]; exact hPt
  · rw [hmap, hPeq]

/-- **The named input `GnatMeasureComparisonNSIndef F` holds for every number field $F$** (Weil's measure comparison
$\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the non-square models that are not totally definite; the theorem
`map_muP_nsPEquiv_eq_muTam_any` needs no signature hypothesis at all). -/
@[kb "weil1982" "Thm 2.3.1; §3.7, pp. 64-65 [unverified page]"]
theorem gnatMeasureComparisonNSIndef : GnatMeasureComparisonNSIndef F :=
  ⟨fun a b d K _ _ _ bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ _ =>
    map_muP_nsPEquiv_eq_muTam_any a b d K bK hb₀ hb₁ α β hα hβ hα0 hβ0 hQ⟩

/-- **`GnatMeasureComparison F` for every number field** (both discriminant cases of Weil's measure comparison). -/
@[kb "weil1982" "Thm 2.3.1; §3.7, pp. 64-65 [unverified page]"]
theorem gnatMeasureComparison : GnatMeasureComparison F :=
  gnatMeasureComparison_of_nsIndef gnatMeasureComparisonNSIndef

/-- **`GnatTamagawaComparison F` for every number field.** -/
@[kb "weil1982" "Thm 2.3.1; §3.7, pp. 64-65 [unverified page]"]
theorem gnatTamagawaComparison : GnatTamagawaComparison F :=
  gnatTamagawaComparison_of_nsIndef gnatMeasureComparisonNSIndef

end Main

end QuadFormsKB.Tamagawa.Measure.Weil

end
