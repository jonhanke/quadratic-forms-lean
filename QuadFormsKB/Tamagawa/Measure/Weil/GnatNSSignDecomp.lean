/-
# The norm-one part of the test set as a union of sign translates

**Layer:** $F$ any number field, $K = F(\delta)$, $\delta^2 = d$, $\alpha = a$, $\beta = b$; $G^\natural$ = `gnatBCO`; $Q_0 = $ `qNS a b d`.

* **`Uarch`** $= \prod_{v\text{ real}}U_v\times\prod_{v\text{ complex}}U_v\subseteq G_\infty$ (`URset`, `UCset`).
* **`signIdele ε`** for $\varepsilon : \{\text{infinite places of }F\}\to\{\pm1\}$: the idele with archimedean components $\varepsilon_v$ and
  finite part $1$; it squares to $1$, so $z(\varepsilon) = (\varepsilon, 1)\in G^\natural$ and $\mathrm{nsInf}$ does not see it.
* **`setSL1U_eq_iUnion`**: $\{x\in\mathrm{SL}_1(D\otimes\mathbb A_K) : x\in H_S,\ \mathrm{nsInf}(x,1)\in U\} = \bigsqcup_\varepsilon\varepsilon\cdot H$, with
  $H = \{x\in\mathrm{SL}_1 : x\in H_{\mathrm{cone}}\}$ (coordinates at every place of $K$ in the test sets);
  **`muSL1N_setSL1U`**: its measure is $2^{\#\{\text{infinite places of }F\}}\,\mu_{\mathrm{SL}_1}(H)$.

Source: Weil 1982, §2.3, Thm 2.3.1 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSArchSetsC
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSFibAny
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSConeK

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

/-! ### Sign ideles -/

section Sign

variable {F : Type} [Field F] [NumberField F]

/-- **The sign idele** with archimedean components $\varepsilon_v\in\{\pm1\}$ and finite part $1$. -/
def signIdele (ε : InfinitePlace F → ℤˣ) : (Adeles F)ˣ :=
  (idelesEquiv F).symm (mkInfUnitRC (fun w => ((ε w.1 : ℤ) : ℝ)) (fun w => (((ε w.1 : ℤ) : ℝ) : ℂ))
    (fun w => by rcases Int.units_eq_one_or (ε w.1) with h | h <;> simp [h])
    (fun w => by rcases Int.units_eq_one_or (ε w.1) with h | h <;> simp [h]), 1)

theorem infPart_signIdele (ε : InfinitePlace F → ℤˣ) :
    infPart (signIdele ε) = mkInfUnitRC (fun w => ((ε w.1 : ℤ) : ℝ)) (fun w => (((ε w.1 : ℤ) : ℝ) : ℂ))
      (fun w => by rcases Int.units_eq_one_or (ε w.1) with h | h <;> simp [h])
      (fun w => by rcases Int.units_eq_one_or (ε w.1) with h | h <;> simp [h]) :=
  congrArg Prod.fst ((idelesEquiv F).apply_symm_apply _)

theorem finPart_signIdele (ε : InfinitePlace F → ℤˣ) : finPart (signIdele ε) = 1 :=
  congrArg Prod.snd ((idelesEquiv F).apply_symm_apply _)

theorem signIdele_fst_fst (ε : InfinitePlace F → ℤˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    ((signIdele ε : (Adeles F)ˣ) : Adeles F).1.1 w = ((ε w.1 : ℤ) : ℝ) := by
  have := congrArg (fun u : (mixedSpace F)ˣ => (u : mixedSpace F).1 w) (infPart_signIdele ε)
  exact this

theorem signIdele_fst_snd (ε : InfinitePlace F → ℤˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    ((signIdele ε : (Adeles F)ˣ) : Adeles F).1.2 w = (((ε w.1 : ℤ) : ℝ) : ℂ) := by
  have := congrArg (fun u : (mixedSpace F)ˣ => (u : mixedSpace F).2 w) (infPart_signIdele ε)
  exact this

theorem int_unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem signIdele_sq (ε : InfinitePlace F → ℤˣ) : signIdele ε ^ 2 = 1 := by
  apply (idelesEquiv F).injective
  rw [map_pow, map_one, idelesEquiv_apply, infPart_signIdele, finPart_signIdele, Prod.pow_mk, one_pow]
  refine Prod.ext (Units.ext (Prod.ext (funext fun w => ?_) (funext fun w => ?_))) rfl
  · rw [Units.val_pow_eq_pow_val]
    show ((ε w.1 : ℤ) : ℝ) ^ 2 = 1
    exact int_unit_sq _
  · rw [Units.val_pow_eq_pow_val]
    show ((((ε w.1 : ℤ) : ℝ) : ℂ)) ^ 2 = 1
    rw [← Complex.ofReal_pow, int_unit_sq, Complex.ofReal_one]

end Sign

section SignK

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

theorem adeleMap_signIdele_real (ε : InfinitePlace F → ℤˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    (adeleMap F K ((signIdele ε : (Adeles F)ˣ) : Adeles F)).1.1 w =
      ((ε (w.1.comap (algebraMap F K)) : ℤ) : ℝ) := by
  rw [adeleMap_fst_fst, signIdele_fst_fst]

theorem adeleMap_signIdele_cx (ε : InfinitePlace F → ℤˣ) (w : {w : InfinitePlace K // w.IsComplex}) :
    (adeleMap F K ((signIdele ε : (Adeles F)ˣ) : Adeles F)).1.2 w =
      (((ε (w.1.comap (algebraMap F K)) : ℤ) : ℝ) : ℂ) := by
  by_cases hv : (w.1.comap (algebraMap F K)).IsReal
  · rw [adeleMap_fst_snd_of_isReal_comap _ w hv, signIdele_fst_fst]
  · have hv' : (w.1.comap (algebraMap F K)).IsComplex := not_isReal_iff_isComplex.1 hv
    rcases (embedding_comp_eq_or_conj w.1 hv').1 with h | h
    · rw [adeleMap_fst_snd_of_comp_eq _ w hv' h, signIdele_fst_snd]
    · rw [adeleMap_fst_snd_of_comp_eq_conj _ w hv' h, signIdele_fst_snd, Complex.conj_ofReal]

variable {A' B' : K}

theorem qVec_unitAtR_quatScalar_mul (c : (Adeles K)ˣ) (x : (QuatAdele A' B')ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    qVec ((unitAtR A' B' w (quatScalar A' B' c * x) : (ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'])ˣ) :
        ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B']) =
      ((c : Adeles K).1.1 w) • qVec ((unitAtR A' B' w x : (ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'])ˣ) :
        ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B']) := by
  rw [map_mul, Units.val_mul]
  have e : ((unitAtR A' B' w (quatScalar A' B' c) : (ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B'])ˣ) :
      ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B']) = (((c : Adeles K).1.1 w : ℝ) :
        ℍ[ℝ, embedding_of_isReal w.2 A', embedding_of_isReal w.2 B']) := QuaternionAlgebra.ext rfl rfl rfl rfl
  rw [e, QuaternionAlgebra.coe_mul_eq_smul, qVec_smul]

theorem qVec_unitAtC_quatScalar_mul (c : (Adeles K)ˣ) (x : (QuatAdele A' B')ˣ)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    qVec ((unitAtC A' B' w (quatScalar A' B' c * x) : (ℍ[ℂ, w.1.embedding A', w.1.embedding B'])ˣ) :
        ℍ[ℂ, w.1.embedding A', w.1.embedding B']) =
      ((c : Adeles K).1.2 w) • qVec ((unitAtC A' B' w x : (ℍ[ℂ, w.1.embedding A', w.1.embedding B'])ˣ) :
        ℍ[ℂ, w.1.embedding A', w.1.embedding B']) := by
  rw [map_mul, Units.val_mul]
  have e : ((unitAtC A' B' w (quatScalar A' B' c) : (ℍ[ℂ, w.1.embedding A', w.1.embedding B'])ˣ) :
      ℍ[ℂ, w.1.embedding A', w.1.embedding B']) = (((c : Adeles K).1.2 w : ℂ) :
        ℍ[ℂ, w.1.embedding A', w.1.embedding B']) := QuaternionAlgebra.ext rfl rfl rfl rfl
  rw [e, QuaternionAlgebra.coe_mul_eq_smul, qVec_smul]

end SignK

/-! ### The decomposition -/

section Decomp

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ
local notation "nsI" => nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0

variable (a b) in
/-- **The archimedean test set** $U = \prod_vU_v\subseteq G_\infty$. -/
def Uarch : Set (GInfSO (qNS a b d)) :=
  (univ.pi fun v => URset (a := a) (b := b) hb₀ hb₁ v) ×ˢ (univ.pi fun v => UCset (a := a) (b := b) hb₀ hb₁ v)

theorem measurableSet_Uarch (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0) :
    MeasurableSet (Uarch a b hb₀ hb₁) :=
  (MeasurableSet.univ_pi fun v => measurableSet_URset hb₀ hb₁ ha0 hd0 v).prod
    (MeasurableSet.univ_pi fun v => measurableSet_UCset hb₀ hb₁ ha0 hd0 v)

variable (α β) in
/-- The real test sets over $K$: the points of $S_1$ with coordinates in `posVecR`. -/
def ARK (w : {w : InfinitePlace K // w.IsReal}) : Set (Sph (QRe (qSq α β) w) 1) := {x | (x : Fin 4 → ℝ) ∈ posVecR}

variable (α β) in
/-- The complex test sets over $K$: the points of $S_1$ with coordinates in `posVecC`. -/
def ACK (w : {w : InfinitePlace K // w.IsComplex}) : Set (SphC (QCx (qSq α β) w) 1) :=
  {x | (x : Fin 4 → ℂ) ∈ posVecC}

theorem isOpen_posVecR : IsOpen posVecR :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_posVecC : IsOpen posVecC :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply 0))).inter
    (isOpen_lt continuous_norm continuous_const)

theorem measurableSet_ARK (w : {w : InfinitePlace K // w.IsReal}) : MeasurableSet (ARK α β w) :=
  (isOpen_posVecR.preimage continuous_subtype_val).measurableSet

theorem measurableSet_ACK (w : {w : InfinitePlace K // w.IsComplex}) : MeasurableSet (ACK α β w) :=
  (isOpen_posVecC.preimage continuous_subtype_val).measurableSet

/-- **The cone test set** $H$: the elements of $\mathrm{SL}_1$ in $H_{\mathrm{cone}}$. -/
def HconeSL : Set (nrdHom (α : K) (β : K)).ker :=
  {x | (x : MK) ∈ Hcone SK mK hmK1 (TRd (F := K)) (ARK α β) (TCd (F := K)) (ACK α β)}

theorem measurableSet_HconeSL : MeasurableSet (HconeSL SK mK hmK1 (α := α) (β := β)) :=
  (measurableSet_Hcone SK mK hmK1 _ _ _ _ (fun _ => measurableSet_Ioo) measurableSet_ARK
    (fun w => (isOpen_TCd w).measurableSet) TCd_subset measurableSet_ACK).preimage measurable_subtype_coe

theorem mem_HconeSL_iff (x : (nrdHom (α : K) (β : K)).ker) :
    x ∈ HconeSL SK mK hmK1 ↔
      (∀ w : {w : InfinitePlace K // w.IsReal},
        qVec ((unitAtR (α : K) (β : K) w (x : MK) : (HRe α β w)ˣ) : HRe α β w) ∈ posVecR) ∧
      (∀ w : {w : InfinitePlace K // w.IsComplex},
        qVec ((unitAtC (α : K) (β : K) w (x : MK) : (HCx α β w)ˣ) : HCx α β w) ∈ posVecC) ∧
      (x : MK) ∈ HS α β SK mK hmK1 := by
  have hx : nrdUnit (x : MK) = 1 := x.2
  rw [HconeSL, mem_setOf_eq, mem_Hcone]
  simp only [qVec_mem_coneR_iff _ (ARK α β) (fun w => show (0 : ℝ) ∈ TRd (F := K) w from ⟨by norm_num, by norm_num⟩) _ _ hx,
    qVec_mem_coneC_iff _ (ACK α β) one_mem_TCd TCd_subset _ _ hx]
  rfl

/-- The sign element $\varepsilon\in\mathrm{SL}_1(D\otimes\mathbb A_K)$. -/
def sK (ε : InfinitePlace F → ℤˣ) : (nrdHom (α : K) (β : K)).ker :=
  ⟨quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)), by
    rw [MonoidHom.mem_ker]
    change nrdUnit _ = 1
    rw [nrdUnit_quatScalar, ← map_pow, signIdele_sq, map_one]⟩

theorem sK_mul_self (ε : InfinitePlace F → ℤˣ) : sK (α := α) (β := β) ε * sK ε = 1 := by
  apply Subtype.ext
  change quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)) *
    quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)) = 1
  rw [← map_mul, ← map_mul, ← sq, signIdele_sq, map_one, map_one]

end Decomp

section Decomp2

variable {F : Type} [Field F] [NumberField F] {a b d : 𝓞 F} {K : Type} [Field K] [NumberField K]
  [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {α β : 𝓞 K} (hα : (α : K) = algebraMap F K (a : F)) (hβ : (β : K) = algebraMap F K (b : F))
  (hα0 : α ≠ 0) (hβ0 : β ≠ 0) (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)
  (SK : Finset (HeightOneSpectrum (𝓞 K))) (mK : HeightOneSpectrum (𝓞 K) → ℕ) (hmK1 : ∀ w, 1 ≤ mK w)

local notation "dN" => gnatBCO bK 0 hb₀ hα0 hβ0
local notation "MK" => (QuatAdele (α : K) (β : K))ˣ
local notation "nsI" => nsInf hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0

/-- **The norm-one part of the test set**: $\{x\in\mathrm{SL}_1 : x\in H_S,\ \mathrm{nsInf}(x,1)\in U\}$. -/
def X1set : Set (nrdHom (α : K) (β : K)).ker :=
  {x | (x : MK) ∈ HS α β SK mK hmK1 ∧ nsI ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ ∈ Uarch a b hb₀ hb₁}

include hb₀ hb₁ hα0 in
theorem sK_mem_HS (ε : InfinitePlace F → ℤˣ) : (sK (α := α) (β := β) ε : MK) ∈ HS α β SK mK hmK1 := by
  change quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)) ∈ HS α β SK mK hmK1
  rw [quatScalar_mem_HS_iff SK mK hmK1 hα0, finPart_adeleUnitsMap_mem_iff hb₀ hb₁, finPart_signIdele]
  exact (OHatUnits F).one_mem

theorem qVec_unitAtR_sK_mul (ε : InfinitePlace F → ℤˣ) (x : (nrdHom (α : K) (β : K)).ker)
    (w : {w : InfinitePlace K // w.IsReal}) :
    qVec ((unitAtR (α : K) (β : K) w ((sK ε * x : (nrdHom (α : K) (β : K)).ker) : MK) : (HRe α β w)ˣ) : HRe α β w) =
      ((ε (w.1.comap (algebraMap F K)) : ℤ) : ℝ) • qVec ((unitAtR (α : K) (β : K) w (x : MK) : (HRe α β w)ˣ) : HRe α β w) := by
  rw [Subgroup.coe_mul]
  change qVec ((unitAtR (α : K) (β : K) w (quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)) * (x : MK)) :
    (HRe α β w)ˣ) : HRe α β w) = _
  rw [qVec_unitAtR_quatScalar_mul, coe_adeleUnitsMap, adeleMap_signIdele_real]

theorem qVec_unitAtC_sK_mul (ε : InfinitePlace F → ℤˣ) (x : (nrdHom (α : K) (β : K)).ker)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    qVec ((unitAtC (α : K) (β : K) w ((sK ε * x : (nrdHom (α : K) (β : K)).ker) : MK) : (HCx α β w)ˣ) : HCx α β w) =
      (((ε (w.1.comap (algebraMap F K)) : ℤ) : ℝ) : ℂ) •
        qVec ((unitAtC (α : K) (β : K) w (x : MK) : (HCx α β w)ˣ) : HCx α β w) := by
  rw [Subgroup.coe_mul]
  change qVec ((unitAtC (α : K) (β : K) w (quatScalar (α : K) (β : K) (adeleUnitsMap F K (signIdele ε)) * (x : MK)) :
    (HCx α β w)ˣ) : HCx α β w) = _
  rw [qVec_unitAtC_quatScalar_mul, coe_adeleUnitsMap, adeleMap_signIdele_cx]

theorem mem_Uarch_iff (g : (dN).G) :
    nsI g ∈ Uarch a b hb₀ hb₁ ↔
      (∀ v, nsR hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 v g ∈ URset (a := a) (b := b) hb₀ hb₁ v) ∧
      (∀ v, nsC hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 v g ∈ UCset (a := a) (b := b) hb₀ hb₁ v) := by
  simp only [Uarch, mem_prod, mem_univ_pi]
  rfl

theorem unit_sign_eq (r : ℝ) (hr : r ^ 2 = 1) : ∃ u : ℤˣ, ((u : ℤ) : ℝ) = r := by
  rcases NSArch.eq_one_or_neg_one_of_sq hr with h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨-1, by simp [h]⟩

include hα hβ in
/-- **The decomposition** $\{x\in\mathrm{SL}_1 : x\in H_S,\ \mathrm{nsInf}(x,1)\in U\} = \bigcup_\varepsilon\varepsilon\cdot H$. -/
theorem X1set_eq_iUnion :
    X1set hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1 =
      ⋃ ε : InfinitePlace F → ℤˣ, (fun y => sK ε * y) '' HconeSL SK mK hmK1 := by
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨hxS, hxU⟩
    rw [mem_Uarch_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0] at hxU
    have hsign : ∀ v : InfinitePlace F, ∃ u : ℤˣ,
        (∀ w : {w : InfinitePlace K // w.IsReal}, w.1.comap (algebraMap F K) = v →
          ((u : ℤ) : ℝ) • qVec ((unitAtR (α : K) (β : K) w (x : MK) : (HRe α β w)ˣ) : HRe α β w) ∈ posVecR) ∧
        (∀ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v →
          (((u : ℤ) : ℝ) : ℂ) • qVec ((unitAtC (α : K) (β : K) w (x : MK) : (HCx α β w)ˣ) : HCx α β w) ∈ posVecC) := by
      intro v
      by_cases hv : v.IsReal
      · obtain ⟨r, hr, hR, hC⟩ := exists_sign_of_nsR_mem_URset hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0)
          ha0 hd0 ⟨v, hv⟩ ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ rfl (hxU.1 ⟨v, hv⟩)
        obtain ⟨u, hu⟩ := unit_sign_eq r hr
        exact ⟨u, fun w hw => by rw [hu]; exact hR w hw, fun w hw => by rw [hu]; exact hC w hw⟩
      · have hv' : v.IsComplex := not_isReal_iff_isComplex.1 hv
        obtain ⟨r, hr, hC⟩ := exists_sign_of_nsC_mem_UCset hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0)
          ha0 hd0 ⟨v, hv'⟩ ⟨((x : MK), 1), (dN).pair_mem_gnat x⟩ rfl (hxU.2 ⟨v, hv'⟩)
        obtain ⟨u, hu⟩ := unit_sign_eq r hr
        exact ⟨u, fun w hw => (not_real_over_complex ⟨v, hv'⟩ w hw).elim, fun w hw => by rw [hu]; exact hC w hw⟩
    choose ε hεR hεC using hsign
    refine ⟨ε, sK ε * x, ?_, by rw [← mul_assoc, sK_mul_self, one_mul]⟩
    rw [mem_HconeSL_iff]
    refine ⟨fun w => ?_, fun w => ?_, ?_⟩
    · rw [qVec_unitAtR_sK_mul]; exact hεR _ w rfl
    · rw [qVec_unitAtC_sK_mul]; exact hεC _ w rfl
    · exact (HS α β SK mK hmK1).mul_mem (sK_mem_HS hb₀ hb₁ hα0 SK mK hmK1 ε) hxS
  · rintro ⟨ε, y, hy, rfl⟩
    obtain ⟨hyR, hyC, hyS⟩ := (mem_HconeSL_iff SK mK hmK1 y).1 hy
    refine ⟨(HS α β SK mK hmK1).mul_mem (sK_mem_HS hb₀ hb₁ hα0 SK mK hmK1 ε) hyS, ?_⟩
    have hz : (⟨(((sK ε * y : (nrdHom (α : K) (β : K)).ker) : MK), 1), (dN).pair_mem_gnat (sK ε * y)⟩ : (dN).G) =
        (dN).zHom (signIdele ε) * ⟨((y : MK), 1), (dN).pair_mem_gnat y⟩ := by
      apply Subtype.ext
      refine Prod.ext rfl ?_
      change (1 : (Adeles F)ˣ) = signIdele ε ^ 2 * 1
      rw [signIdele_sq, one_mul]
    rw [hz, nsInf_zHom_mul hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0, mem_Uarch_iff hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0]
    exact ⟨fun v => nsR_mem_URset_of_coords hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 v _ rfl
        (fun w _ => hyR w) (fun w _ => hyC w),
      fun v => nsC_mem_UCset_of_coords hb₀ hb₁ hα hβ (coeK_ne_zero hα0) (coeK_ne_zero hβ0) ha0 hd0 v _ rfl
        (fun w _ => hyC w)⟩

include hb₀ hb₁ hd0 in
theorem exists_place_over_inf (v : InfinitePlace F) :
    (∃ w : {w : InfinitePlace K // w.IsReal}, w.1.comap (algebraMap F K) = v) ∨
      (∃ w : {w : InfinitePlace K // w.IsComplex}, w.1.comap (algebraMap F K) = v) := by
  by_cases hv : v.IsReal
  · rcases lt_or_gt_of_ne (ne_zero_of_algebraMap_ne hd0 ⟨v, hv⟩) with h | h
    · exact Or.inr ⟨_, (nsPlace_spec hb₀ hb₁ ⟨v, hv⟩ h).1⟩
    · exact Or.inl ⟨_, (splitPlaces_spec hb₀ hb₁ ⟨v, hv⟩ h).1⟩
  · exact Or.inr ⟨_, (cxPlaces_spec hb₀ hb₁ ⟨v, not_isReal_iff_isComplex.1 hv⟩).2.1⟩

theorem int_units_ne (u u' : ℤˣ) (h : u ≠ u') : ((u : ℤ) : ℝ) = - ((u' : ℤ) : ℝ) := by
  rcases Int.units_eq_one_or u with hu | hu <;> rcases Int.units_eq_one_or u' with hu' | hu' <;>
    simp_all

include hb₀ hb₁ hd0 in
theorem pairwise_disjoint_sK :
    Pairwise (Disjoint on fun ε : InfinitePlace F → ℤˣ => (fun y => sK (α := α) (β := β) ε * y) '' HconeSL SK mK hmK1) := by
  intro ε ε' hne
  obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
  have hs := int_units_ne _ _ hv
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', heq⟩
  obtain ⟨hyR, hyC, -⟩ := (mem_HconeSL_iff SK mK hmK1 y).1 hy
  obtain ⟨hyR', hyC', -⟩ := (mem_HconeSL_iff SK mK hmK1 y').1 hy'
  rcases exists_place_over_inf hb₀ hb₁ hd0 (K := K) v with ⟨w, hw⟩ | ⟨w, hw⟩
  · have e := congrArg (fun z : (nrdHom (α : K) (β : K)).ker =>
      qVec ((unitAtR (α : K) (β : K) w (z : MK) : (HRe α β w)ˣ) : HRe α β w) 0) heq
    simp only [qVec_unitAtR_sK_mul, hw, Pi.smul_apply, smul_eq_mul] at e
    have h1 := (hyR w).1
    have h2 := (hyR' w).1
    rw [hs] at e
    rcases Int.units_eq_one_or (ε v) with hu | hu <;> simp [hu] at hs e <;> nlinarith
  · have e := congrArg (fun z : (nrdHom (α : K) (β : K)).ker =>
      (qVec ((unitAtC (α : K) (β : K) w (z : MK) : (HCx α β w)ˣ) : HCx α β w) 0).re) heq
    simp only [qVec_unitAtC_sK_mul, hw, Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul] at e
    have h1 := (hyC w).1
    have h2 := (hyC' w).1
    rw [hs] at e
    rcases Int.units_eq_one_or (ε v) with hu | hu <;> simp [hu] at hs e <;> nlinarith

include hα hβ in
/-- **$\mu_{\mathrm{SL}_1}(X^1) = 2^{\#\{\text{infinite places of }F\}}\,\mu_{\mathrm{SL}_1}(H)$.** -/
theorem muSL1N_X1set :
    muSL1N hα0 hβ0 (X1set hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1) =
      2 ^ Fintype.card (InfinitePlace F) * muSL1N hα0 hβ0 (HconeSL SK mK hmK1) := by
  classical
  rw [X1set_eq_iUnion hb₀ hb₁ hα hβ hα0 hβ0 ha0 hd0 SK mK hmK1,
    measure_iUnion (pairwise_disjoint_sK hb₀ hb₁ hd0 SK mK hmK1) (fun ε => by
      rw [Set.image_mul_left]; exact measurable_const_mul _ (measurableSet_HconeSL SK mK hmK1)), tsum_fintype]
  have h : ∀ ε : InfinitePlace F → ℤˣ, muSL1N hα0 hβ0 ((fun y => sK (α := α) (β := β) ε * y) '' HconeSL SK mK hmK1) =
      muSL1N hα0 hβ0 (HconeSL SK mK hmK1) := fun ε => by
    rw [Set.image_mul_left, measure_preimage_mul]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_units_int, nsmul_eq_mul]
  push_cast
  ring

end Decomp2

end QuadFormsKB.Tamagawa.Measure.Weil

end
