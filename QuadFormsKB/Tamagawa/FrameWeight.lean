/-
# The weight of a local type of frames as a ratio of orbit counts

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (dyadic included).

**Proves** `frameNear_type`: for $g \in O(V)(F_\mathfrak p)$ with $x = g^{-1}E$ integral, $N_{k,s}(Kx) = w(gL)\,N_{k,s}(KE)$ for $k \gg s \gg 0$
(Weil 1982, §3.4 [unverified]; the finite form of $\nu(Kx)/\nu(KE) = \mu(K_0')/\mu(K_{gL})$). See the docstring of the theorem for the proof.

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameLocal
import QuadFormsKB.Tamagawa.FrameDiag
import QuadFormsKB.Tamagawa.AlphaLawSplit

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! #### A universe-polymorphic diagonalization -/

section PolyDiag

variable {F : Type*} [Field F] [NumberField F] {r : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem fw_hessian_map_alg (T₀ : QuadForm (𝓞 F) r) :
    (T₀.map (algebraMap (𝓞 F) F)).hessian = T₀.hessian.map (algebraMap (𝓞 F) F) := by
  ext i j; simp [QuadForm.hessian, QuadForm.map]

theorem fw_hessian_diag (dg : Fin r → 𝓞 F) :
    (QuadForm.diag dg).hessian = Matrix.diagonal (fun i => 2 * dg i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [QuadForm.hessian, QuadForm.diag, two_mul]
  · simp [QuadForm.hessian, QuadForm.diag, h]

/-- Universe-polymorphic copy of `exists_diag_global`. -/
theorem fw_exists_diag_global (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    ∃ (P : Matrix (Fin r) (Fin r) (𝓞 F)) (dg : Fin r → 𝓞 F), P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧
      T₀.compMat P = QuadForm.diag dg := by
  classical
  set T := T₀.map (algebraMap (𝓞 F) F) with hTdef
  have hTF : T.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hTdef, fw_hessian_map_alg, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hT
  obtain ⟨e, hort, hne⟩ := exists_orthogonal_basis T F hTF
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    (Finset.univ.image fun p : Fin r × Fin r => e p.2 p.1)
  choose a ha using fun p : Fin r × Fin r => hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  let P : Matrix (Fin r) (Fin r) (𝓞 F) := Matrix.of fun i j => a (i, j)
  have hPe : ∀ i j, algebraMap (𝓞 F) F (P i j) = (b : 𝓞 F) • e j i := fun i j => ha (i, j)
  have hcol : ∀ j, (fun l => algebraMap (𝓞 F) F (P l j)) = (algebraMap (𝓞 F) F (b : 𝓞 F)) • e j := by
    intro j; funext l
    rw [hPe, Algebra.smul_def]; rfl
  have hbne : algebraMap (𝓞 F) F (b : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr (nonZeroDivisors.coe_ne_zero b)
  have hdiag : ∀ i, algebraMap (𝓞 F) F (T₀.eval fun l => P l i) =
      algebraMap (𝓞 F) F (b : 𝓞 F) ^ 2 * T.evalIn F (e i) := by
    intro i
    rw [← eval_map_comp (algebraMap (𝓞 F) F) T₀ (fun l => P l i)]
    show T.evalIn F _ = _
    rw [hcol i, evalIn_smul']
  have hoff : ∀ i j, i < j →
      (fun l => P l i) ⬝ᵥ (T₀.hessian *ᵥ fun l => P l j) = 0 := by
    intro i j hij
    apply (map_eq_zero_iff _ RingOfIntegers.coe_injective).mp
    have e1 : algebraMap (𝓞 F) F ((fun l => P l i) ⬝ᵥ (T₀.hessian *ᵥ fun l => P l j)) =
        (fun l => algebraMap (𝓞 F) F (P l i)) ⬝ᵥ
          (T₀.hessian.map (algebraMap (𝓞 F) F) *ᵥ fun l => algebraMap (𝓞 F) F (P l j)) := by
      simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
    rw [e1, hcol i, hcol j, ← fw_hessian_map_alg, ← hTdef, smul_dotProduct, mulVec_smul, dotProduct_smul]
    have hq := hort i j hij.ne
    unfold qbil at hq
    simp only [Algebra.algebraMap_self] at hq
    have hm : T.hessian.map (RingHom.id F) = T.hessian := by ext; simp
    rw [hm] at hq
    simp [hq]
  have hdg : ∀ i, T₀.eval (fun l => P l i) ≠ 0 := by
    intro i h0
    have := hdiag i
    rw [h0, map_zero] at this
    exact (mul_ne_zero (pow_ne_zero 2 hbne) (hne i)) this.symm
  have heq : T₀.compMat P = QuadForm.diag (fun i => T₀.eval fun l => P l i) := by
    refine QuadForm.ext_upper fun i j hij => ?_
    rw [QuadForm.compMat_coeff, if_pos hij]
    simp only [QuadForm.diag, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg h]
      exact hoff i j (lt_of_le_of_ne hij h)
  refine ⟨P, fun i => T₀.eval fun l => P l i, ?_, hdg, heq⟩
  intro hP0
  have h1 := congrArg QuadForm.hessian heq
  rw [QuadForm.hessian_compMat, fw_hessian_diag] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hP0, mul_zero] at h2
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero two_ne_zero (hdg i)) h2.symm

/-- Universe-polymorphic copy of `exists_diag_local`. -/
theorem fw_exists_diag_local (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    ∃ (P : Matrix (Fin r) (Fin r) (v.adicCompletionIntegers F)) (dg : Fin r → v.adicCompletionIntegers F),
      P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧ (NF.Qp v T₀).compMat P = QuadForm.diag dg := by
  obtain ⟨P, dg, hP, hdg, h⟩ := fw_exists_diag_global T₀ hT
  refine ⟨P.map (NF.ι v), fun i => NF.ι v (dg i), ?_, fun i => NF.ι_ne_zero v (hdg i), ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact NF.ι_ne_zero v hP
  · rw [NF.Qp, QuadForm.map_compMat, h]
    ext i j
    simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]

end PolyDiag

section Weight

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r)
  (Q₀' : QuadForm (𝓞 F) n')

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "QB" => blockForm TF QF'
local notation "Qo" => NF.Qp v (blockForm T₀ Q₀')
local notation "To" => NF.Qp v T₀

/-! #### Coordinates -/

theorem fw_coeFrame_eq (y : Fin (r + n') × Fin r → 𝔬) :
    coeFrame v y = (toMat y).map (algebraMap 𝔬 Fv) := rfl

theorem fw_coeFrame_frameMat (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (a : Fin (r + n') × Fin r → 𝔬) :
    coeFrame v (frameMat r P *ᵥ a) = P.map (algebraMap 𝔬 Fv) * coeFrame v a := by
  rw [fw_coeFrame_eq, fw_coeFrame_eq, toMat_frameMat_mulVec, Matrix.map_mul]

theorem fw_coeFrame_inj {y z : Fin (r + n') × Fin r → 𝔬} (h : coeFrame v y = coeFrame v z) : y = z := by
  funext p
  exact Subtype.ext (congrFun (congrFun h p.1) p.2)

theorem fw_coeFrame_rho (κ : stdStab QB v) (y : Fin (r + n') × Fin r → 𝔬) :
    coeFrame v (frameRepK v T₀ Q₀' κ *ᵥ y) =
      ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * coeFrame v y := by
  have : frameRepK v T₀ Q₀' κ = frameMat r (intRep v QB κ) := rfl
  rw [this, fw_coeFrame_frameMat, intRep_map]

theorem fw_formF_rho (κ : stdStab QB v) (y : Fin (r + n') × Fin r → 𝔬) :
    formF Qo (frameRepK v T₀ Q₀' κ *ᵥ y) = formF Qo y := by
  have : frameRepK v T₀ Q₀' κ = frameMat r (intRep v QB κ) := rfl
  rw [this]
  exact formF_frameMat_of_compMat Qo (compMat_intRep v (isIntModel_blockForm v T₀ Q₀') κ) y

theorem fw_nondeg (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) : (Qo).Nondegenerate := by
  apply NF.nondegenerate_Qp
  show (blockForm T₀ Q₀').hessian.det ≠ 0
  rw [det_hessian_blockForm]
  exact mul_ne_zero hT hQ'

theorem fw_nondegF (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) : (QB).Nondegenerate := by
  show (QB).hessian.det ≠ 0
  rw [det_hessian_blockForm]
  exact mul_ne_zero (fl_hess_ne T₀ hT) (fl_hess_ne Q₀' hQ')

theorem fw_formF_std : formF Qo (stdFrame (A := 𝔬) (r := r) (n' := n')) = tc To := by
  show formF ((blockForm T₀ Q₀').map (NF.ι v)) _ = tc (T₀.map (NF.ι v))
  rw [map_blockForm]
  exact formF_stdFrame _ _

/-! #### Stabilizers of lattices are open -/

theorem fw_mulVec_mem_of_congr {N : ℕ} {Λ' : Submodule 𝔬 (Fin N → Fv)} {c : ℕ}
    (hb : ball v (c : ℤ) ≤ Λ') (hb' : Λ' ≤ ball v (-(c : ℤ)))
    (X : Matrix (Fin N) (Fin N) 𝔬) (hX : ∀ i j, NF.π v ^ (2 * c) ∣ X i j - (1 : Matrix (Fin N) (Fin N) 𝔬) i j)
    {y : Fin N → Fv} (hy : y ∈ Λ') : X.map (algebraMap 𝔬 Fv) *ᵥ y ∈ Λ' := by
  choose E hE using hX
  set ϖ : Fv := ((NF.π v : 𝔬) : Fv)
  set w : Fin N → Fv := fun i => ∑ j, (E i j : Fv) * y j with hw
  have key : X.map (algebraMap 𝔬 Fv) *ᵥ y = y + ϖ ^ (2 * c) • w := by
    funext i
    have h1 : ∀ j, (X i j : Fv) = (((1 : Matrix (Fin N) (Fin N) 𝔬) i j : 𝔬) : Fv) + ϖ ^ (2 * c) * (E i j : Fv) := by
      intro j
      have := congrArg (fun z : 𝔬 => (z : Fv)) (hE i j)
      push_cast at this ⊢
      simp only [ϖ]
      linear_combination this
    have e : ∀ j, (X.map (algebraMap 𝔬 Fv)) i j = (X i j : Fv) := fun j => rfl
    simp only [Matrix.mulVec, dotProduct, e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
    simp_rw [h1, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single i]
      · simp [Matrix.one_apply]
      · intro j _ hj; simp [Matrix.one_apply, Ne.symm hj]
      · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [key]
  refine Λ'.add_mem hy (hb ?_)
  intro i
  have hyv : ∀ j, Valued.v (y j) ≤ WithZero.exp (c : ℤ) := by
    intro j
    have := hb' hy j
    simpa using this
  have hwv : Valued.v (w i) ≤ WithZero.exp (c : ℤ) := by
    refine Valuation.map_sum_le _ fun j _ => ?_
    rw [map_mul]
    calc Valued.v ((E i j : 𝔬) : Fv) * Valued.v (y j) ≤ 1 * WithZero.exp (c : ℤ) :=
          mul_le_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (E i j).2) (hyv j)
      _ = _ := one_mul _
  show Valued.v (ϖ ^ (2 * c) * w i) ≤ _
  rw [map_mul, map_pow, NF.valued_π, ← WithZero.exp_nsmul]
  calc WithZero.exp ((2 * c) • (-1 : ℤ)) * Valued.v (w i)
      ≤ WithZero.exp ((2 * c) • (-1 : ℤ)) * WithZero.exp (c : ℤ) := mul_le_mul_right hwv _
    _ = _ := by
      rw [← WithZero.exp_add]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring

theorem fw_locAct_eq_of_le {N : ℕ} (g : GL (Fin N) Fv) {Λ' : Submodule 𝔬 (Fin N → Fv)}
    (h1 : locAct v g Λ' ≤ Λ') (h2 : locAct v g⁻¹ Λ' ≤ Λ') : locAct v g Λ' = Λ' := by
  rw [locAct_eq_iff]
  refine le_antisymm ?_ h2
  calc Λ' = locAct v g⁻¹ (locAct v g Λ') := (locAct_inv_locAct g Λ').symm
    _ ≤ locAct v g⁻¹ Λ' := Submodule.map_mono h1

theorem fw_congr_inv (κ : stdStab QB v) {s : ℕ}
    (h : ∀ i j, NF.π v ^ s ∣ intRep v QB κ i j - (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) i j) :
    ∀ i j, NF.π v ^ s ∣ intRep v QB κ⁻¹ i j - (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) i j := by
  intro i j
  have h1 : intRep v QB κ⁻¹ * intRep v QB κ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : intRep v QB κ⁻¹ i j - (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) i j =
      -∑ l, intRep v QB κ⁻¹ i l * (intRep v QB κ l j - (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) l j) := by
    have := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply] at this
    simp only [mul_sub, Finset.sum_sub_distrib, this]
    have h3 : ∑ l, intRep v QB κ⁻¹ i l * (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) l j =
        intRep v QB κ⁻¹ i j := by simp [Matrix.one_apply]
    rw [h3]; ring
  rw [h2, dvd_neg]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (h l j) _

/-- The subgroup of $K$ stabilizing a lattice $\Lambda'$. -/
def fwJ (Λ' : Submodule 𝔬 (Fin (r + n') → Fv)) : Subgroup (stdStab QB v) :=
  (stabLat v (orthGroup QB Fv).subtype Λ').subgroupOf (stdStab QB v)

theorem mem_fwJ {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)} (κ : stdStab QB v) :
    κ ∈ fwJ v T₀ Q₀' Λ' ↔ locAct v ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) Λ' = Λ' := Iff.rfl

/-- **Elements of $K$ congruent to $1$ modulo a high power of $\pi$ stabilize a given lattice.** -/
theorem fw_exists_congr {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ'.IsLattice Fv) :
    ∃ t : ℕ, ∀ κ : stdStab QB v, (∀ i j, NF.π v ^ t ∣ intRep v QB κ i j -
      (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) i j) → κ ∈ fwJ v T₀ Q₀' Λ' := by
  obtain ⟨c, hb, hb'⟩ := exists_local_bounds v hΛ
  refine ⟨2 * c, fun κ hκ => ?_⟩
  rw [mem_fwJ]
  have hle : ∀ κ : stdStab QB v, (∀ i j, NF.π v ^ (2 * c) ∣ intRep v QB κ i j -
      (1 : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) i j) →
      locAct v ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) Λ' ≤ Λ' := by
    rintro κ hκ _ ⟨y, hy, rfl⟩
    show ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ y ∈ Λ'
    rw [← intRep_map v QB κ]
    exact fw_mulVec_mem_of_congr v hb hb' _ hκ hy
  refine fw_locAct_eq_of_le v _ (hle κ hκ) ?_
  have := hle κ⁻¹ (fw_congr_inv v T₀ Q₀' κ hκ)
  simpa using this

/-- **Openness of orbits relative to $J(\Lambda')$.** -/
theorem fw_exists_J_of_near (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate)
    {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ'.IsLattice Fv) :
    ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s → ∀ y z : Fin (r + n') × Fin r → 𝔬, formF Qo y = tc To → formF Qo z = tc To →
      (∀ i, NF.π v ^ s ∣ z i - y i) → ∃ γ ∈ fwJ v T₀ Q₀' Λ', frameRepK v T₀ Q₀' γ *ᵥ y = z := by
  obtain ⟨t, ht⟩ := fw_exists_congr v T₀ Q₀' hΛ
  obtain ⟨P, dg, hPdet, hdg, hP⟩ := fw_exists_diag_local v T₀ hT
  have hπ := NF.irreducible_π v
  have hf : ∃ f : ℕ, ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i := by
    choose f hf using fun i => exists_pow_dvd_not_dvd (NF.π v) hπ
      (show 4 * dg i ≠ 0 from mul_ne_zero (by
        have := NF.two_ne_zero' v
        intro h
        apply this
        have h4 : (4 : 𝔬) = 2 * 2 := by norm_num
        rw [h4] at h
        rcases mul_eq_zero.mp h with h | h <;> exact h) (hdg i))
    refine ⟨Finset.univ.sup f, fun i hdiv => (hf i).2 ?_⟩
    exact (pow_dvd_pow _ (by have := Finset.le_sup (f := f) (Finset.mem_univ i); omega)).trans hdiv
  obtain ⟨f, hf⟩ := hf
  refine ⟨t + r * f + 1, fun s hs y z hy hz hyz => ?_⟩
  obtain ⟨M, hM, hMy, hM1⟩ := exists_frame_openMat hπ Qo To hPdet hP hdg hf (s := s) (by omega) hy hz hyz
  obtain ⟨κ, hκ⟩ := exists_intRep_eq v (isIntModel_blockForm v T₀ Q₀') (fw_nondeg v T₀ Q₀' hT hQ') M hM
  refine ⟨κ, ht κ fun i j => ?_, ?_⟩
  · rw [hκ]; exact (pow_dvd_pow _ (by omega)).trans (hM1 i j)
  · show frameMat r (intRep v QB κ) *ᵥ y = z
    rw [hκ]; exact hMy

/-- **The orbit of $J(\Lambda')$ is saturated.** -/
theorem fw_orbit_sat (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate)
    {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ'.IsLattice Fv) :
    ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s → ∀ y0 : Fin (r + n') × Fin r → 𝔬, formF Qo y0 = tc To →
      ∀ a ∈ gOrbit (frameRepK v T₀ Q₀') (fwJ v T₀ Q₀' Λ') y0, ∀ z, formF Qo z = tc To →
        (∀ i, NF.π v ^ s ∣ z i - a i) → z ∈ gOrbit (frameRepK v T₀ Q₀') (fwJ v T₀ Q₀' Λ') y0 := by
  obtain ⟨s₁, hs₁⟩ := fw_exists_J_of_near v T₀ Q₀' hT hQ' hΛ
  refine ⟨s₁, fun s hs y0 hy0 a ⟨κ, hκ, ha⟩ z hz hza => ?_⟩
  have ha' : formF Qo a = tc To := by rw [← ha, fw_formF_rho, hy0]
  obtain ⟨γ, hγ, hγa⟩ := hs₁ s hs a z ha' hz hza
  refine ⟨γ * κ, mul_mem hγ hκ, ?_⟩
  rw [map_mul, ← Matrix.mulVec_mulVec, ha, hγa]

/-- **The orbit comparison for $J(\Lambda')$ at a genuine frame.** -/
theorem fw_gNear_J (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate)
    {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)} (hΛ : Λ'.IsLattice Fv) :
    ∃ s₁ : ℕ, ∀ s k : ℕ, s₁ ≤ s → s ≤ k → ∀ y : Fin (r + n') × Fin r → 𝔬, formF Qo y = tc To →
      gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') ⊤ y) *
          (fwJ v T₀ Q₀' Λ').relIndex (gStab (frameRepK v T₀ Q₀') y) =
        (fwJ v T₀ Q₀' Λ').index *
          gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') (fwJ v T₀ Q₀' Λ') y) := by
  obtain ⟨s₁, hs₁⟩ := fw_exists_J_of_near v T₀ Q₀' hT hQ' hΛ
  refine ⟨s₁, fun s k hs hsk y hy => ?_⟩
  refine gNear_mul_relIndex (frameRepK v T₀ Q₀') (isCongr_formF Qo _) (fun κ x => fw_formF_rho v T₀ Q₀' κ x)
    (tc To) hsk (NF.irreducible_π v) _ y (fun κ hκ => ?_)
  exact hs₁ s hs y _ hy (by rw [fw_formF_rho, hy]) (fun i => hκ i)

/-! #### Stabilizers -/

theorem fw_conj_iff' {N : ℕ} (h a : GL (Fin N) Fv) (Λ : Submodule 𝔬 (Fin N → Fv)) :
    locAct v (h * a * h⁻¹) (locAct v h Λ) = locAct v h Λ ↔ locAct v a Λ = Λ := by
  rw [locAct_mul, locAct_mul, locAct_inv_locAct, locAct_eq_iff, locAct_inv_locAct]

theorem fw_conj_iff {N : ℕ} (h a : GL (Fin N) Fv) (Λ : Submodule 𝔬 (Fin N → Fv)) :
    locAct v (h⁻¹ * a * h) Λ = Λ ↔ locAct v a (locAct v h Λ) = locAct v h Λ := by
  rw [locAct_mul, locAct_mul, locAct_eq_iff, inv_inv]

theorem fw_relIndex_E (hT : T₀.Nondegenerate) (M' : LocFrameSet v TF QF') :
    (fwJ v T₀ Q₀' M'.1).relIndex (gStab (frameRepK v T₀ Q₀') (stdFrame (A := 𝔬) (r := r) (n' := n'))) =
      (stabilizer (orthGroup QF' Fv) M').relIndex (stdStab QF' v) := by
  have hTF := fl_hess_ne_v v T₀ hT
  refine relIndex_stab_eq (stdStab QB v) (stabLat v (orthGroup QB Fv).subtype M'.1) _
    (orthEmbB TF QF' Fv) (stdStab QF' v) (stabilizer (orthGroup QF' Fv) M') ?_ ?_
  · ext k
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      have hκE : ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
          stdFrameMat := by
        have := congrArg (coeFrame v) (show frameRepK v T₀ Q₀' κ *ᵥ (stdFrame (A := 𝔬) (r := r) (n' := n')) =
          stdFrame from hκ)
        rwa [fw_coeFrame_rho, coeFrame_stdFrame] at this
      obtain ⟨h, hh⟩ := exists_orthEmbB_eq TF QF' Fv hTF (κ : orthGroup QB Fv) hκE
      exact ⟨h, (mem_stdStab_orthEmbB_iff TF QF' v h).mp (by rw [hh]; exact κ.2), hh⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨orthEmbB TF QF' Fv h, (mem_stdStab_orthEmbB_iff TF QF' v h).mpr hh⟩, ?_, rfl⟩
      show frameRepK v T₀ Q₀' _ *ᵥ (stdFrame (A := 𝔬) (r := r) (n' := n')) = stdFrame
      apply fw_coeFrame_inj v
      rw [fw_coeFrame_rho, coeFrame_stdFrame]
      exact orthEmbB_mul_stdFrameMat TF QF' Fv h
  · intro h' _
    rw [mem_stabilizer_iff]
    constructor
    · intro h1; exact Subtype.ext h1
    · intro h1; exact congrArg Subtype.val h1

theorem fw_relIndex_x (hT : T₀.Nondegenerate) (g : orthGroup QB Fv) (x : Fin (r + n') × Fin r → 𝔬)
    (hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x)
    (M' : LocFrameSet v TF QF') (hM' : M'.1 = locAct v (g : GL (Fin (r + n')) Fv) (std v)) :
    (fwJ v T₀ Q₀' (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))).relIndex
        (gStab (frameRepK v T₀ Q₀') x) = (stdStab QF' v).relIndex (stabilizer (orthGroup QF' Fv) M') := by
  have hTF := fl_hess_ne_v v T₀ hT
  have hgx' : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
      coeFrame v x := hgx
  clear hgx
  have hgg : (g : GL (Fin (r + n')) Fv).val * ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hgE : (g : GL (Fin (r + n')) Fv).val * coeFrame v x = stdFrameMat := by
    rw [← hgx', ← Matrix.mul_assoc, hgg, Matrix.one_mul]
  refine relIndex_stab_eq (stdStab QB v)
    (stabLat v (orthGroup QB Fv).subtype (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))) _
    ((MulAut.conj g⁻¹).toMonoidHom.comp (orthEmbB TF QF' Fv)) (stabilizer (orthGroup QF' Fv) M')
    (stdStab QF' v) ?_ ?_
  · ext k
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ, rfl⟩
      have hκx : ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * coeFrame v x = coeFrame v x := by
        have := congrArg (coeFrame v) (show frameRepK v T₀ Q₀' κ *ᵥ x = x from hκ)
        rwa [fw_coeFrame_rho] at this
      set μ : orthGroup QB Fv := g * (κ : orthGroup QB Fv) * g⁻¹ with hμ
      have hμE : (μ : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
          stdFrameMat := by
        simp only [hμ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
        rw [hgx', hκx, hgE]
      obtain ⟨h, hh⟩ := exists_orthEmbB_eq TF QF' Fv hTF μ hμE
      refine ⟨h, ?_, ?_⟩
      · rw [mem_stabilizer_iff]
        apply Subtype.ext
        rw [LocFrameSet.smul_val, hh, hM']
        have := (fw_conj_iff v (g : GL (Fin (r + n')) Fv) (μ : GL (Fin (r + n')) Fv) (std v)).mp (by
          have e : (g : GL (Fin (r + n')) Fv)⁻¹ * (μ : GL (Fin (r + n')) Fv) * (g : GL (Fin (r + n')) Fv) =
              ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) := by
            simp only [hμ, Subgroup.coe_mul, Subgroup.coe_inv]; group
          rw [e]; exact κ.2)
        exact this
      · show g⁻¹ * orthEmbB TF QF' Fv h * g⁻¹⁻¹ = (κ : orthGroup QB Fv)
        rw [hh]; simp only [hμ]; group
    · rintro ⟨h', hh', rfl⟩
      have hK : g⁻¹ * orthEmbB TF QF' Fv h' * g ∈ stdStab QB v := by
        show locAct v ((g⁻¹ * orthEmbB TF QF' Fv h' * g : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) = std v
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [fw_conj_iff]
        have h1' : h' • M' = M' := mem_stabilizer_iff.mp hh'
        have h1 : locAct v ((orthEmbB TF QF' Fv h' : orthGroup QB Fv) : GL (Fin (r + n')) Fv) M'.1 = M'.1 :=
          congrArg Subtype.val h1'
        rwa [hM'] at h1
      refine ⟨⟨_, hK⟩, ?_, ?_⟩
      · show frameRepK v T₀ Q₀' _ *ᵥ x = x
        apply fw_coeFrame_inj v
        rw [fw_coeFrame_rho]
        show (g⁻¹ * orthEmbB TF QF' Fv h' * g : orthGroup QB Fv).1.val * coeFrame v x = coeFrame v x
        have hφE : ((orthEmbB TF QF' Fv h' : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
            (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := orthEmbB_mul_stdFrameMat TF QF' Fv h'
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
        rw [hgE, hφE, hgx']
      · show g⁻¹ * orthEmbB TF QF' Fv h' * g = g⁻¹ * orthEmbB TF QF' Fv h' * g⁻¹⁻¹
        rw [inv_inv]
  · intro h' _
    show locAct v ((g⁻¹ * orthEmbB TF QF' Fv h' * g⁻¹⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv)
      (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)) =
        locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) ↔ _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [fw_conj_iff']
    exact (mem_stdStab_orthEmbB_iff TF QF' v h')

/-- **$[K : J_1] = [K : J_0]$** (the modular ratio of $O(V)(F_\mathfrak p)$ is $1$). -/
theorem fw_index_eq (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (g : orthGroup QB Fv) :
    (fwJ v T₀ Q₀' (locAct v (g : GL (Fin (r + n')) Fv) (std v))).index =
      (fwJ v T₀ Q₀' (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))).index := by
  set ψ := (orthGroup QB Fv).subtype
  set K := stdStab QB v
  set S0 := stabLat v ψ (locAct v (g : GL (Fin (r + n')) Fv) (std v))
  set S1 := stabLat v ψ (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))
  have hmod := modRatio_eq_one v (QB) (fw_nondegF T₀ Q₀' hT hQ') g⁻¹
  have hc2 : K.map (MulAut.conj g⁻¹).toMonoidHom = S1 := stdStab_map_conj v (QB) g⁻¹
  have hc1 : S0.map (MulAut.conj g⁻¹).toMonoidHom = K := by
    rw [stabLat_map_conj]
    have : locAct v (ψ g⁻¹) (locAct v (g : GL (Fin (r + n')) Fv) (std v)) = std v :=
      locAct_inv_locAct (g : GL (Fin (r + n')) Fv) (std v)
    rw [this]
    exact (stdStab_eq_stabLat v QB).symm
  have e := Subgroup.relIndex_map_map_of_injective S0 K (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective
  rw [hc1, hc2] at e
  have hne : K.relIndex S1 ≠ 0 := by
    have := relIndex_stabLat_ne_zero v ψ (Λ₁ := locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))
      (Λ₂ := std v) (locAct_isLattice _ (std_isLattice v)) (std_isLattice v)
    rwa [← stdStab_eq_stabLat] at this
  unfold modRatio relRatio at hmod
  rw [hc2] at hmod
  have h1 : (S1.relIndex K : ℝ) = (K.relIndex S1 : ℝ) := by
    have hne' : (K.relIndex S1 : ℝ) ≠ 0 := by exact_mod_cast hne
    exact (div_eq_one_iff_eq hne').mp hmod
  have h2 : S1.relIndex K = K.relIndex S1 := by exact_mod_cast h1
  show S0.relIndex K = S1.relIndex K
  rw [h2]; exact e.symm

theorem fw_relIndex_ne_zero (M' : LocFrameSet v TF QF') (hM' : M'.1.IsLattice Fv) :
    (stdStab QF' v).relIndex (stabilizer (orthGroup QF' Fv) M') ≠ 0 := by
  set ψ'' : orthGroup QF' Fv →* GL (Fin (r + n')) Fv := (orthGroup QB Fv).subtype.comp (orthEmbB TF QF' Fv)
  have h1 : stabilizer (orthGroup QF' Fv) M' = stabLat v ψ'' M'.1 := by
    ext h'; rw [mem_stabilizer_iff]; constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have h2 : stdStab QF' v = stabLat v ψ'' (std v) := by
    ext h'; exact (mem_stdStab_orthEmbB_iff TF QF' v h').symm
  rw [h1, h2]
  exact relIndex_stabLat_ne_zero v ψ'' hM' (std_isLattice v)

/-! #### Bases of sublattices of $\mathfrak o^N$ -/

theorem fw_exists_basisMat {N : ℕ} {Λ : Submodule 𝔬 (Fin N → Fv)} (hle : Λ ≤ std v) (hΛ : Λ.IsLattice Fv) :
    ∃ P : Matrix (Fin N) (Fin N) 𝔬, P.det ≠ 0 ∧
      ∀ y, y ∈ Λ ↔ ∃ c : Fin N → 𝔬, P.map (algebraMap 𝔬 Fv) *ᵥ (fun i => (c i : Fv)) = y := by
  classical
  obtain ⟨k, hk, -⟩ := exists_local_bounds v hΛ
  let emb : (Fin N → 𝔬) →ₗ[𝔬] (Fin N → Fv) :=
    LinearMap.pi fun i => (Algebra.linearMap 𝔬 Fv).comp (LinearMap.proj i)
  have hemb : ∀ z, emb z = fun i => (z i : Fv) := fun z => rfl
  let Λ₀ : Submodule 𝔬 (Fin N → 𝔬) := Λ.comap emb
  have hΛ₀ : ∀ z, z ∈ Λ₀ ↔ (fun i => (z i : Fv)) ∈ Λ := fun z => Iff.rfl
  obtain ⟨n₀, b⟩ := Submodule.basisOfPid (Pi.basisFun 𝔬 (Fin N)) Λ₀
  -- the rank of `Λ₀` is `N`
  have hπ0 : (NF.π v ^ k : 𝔬) ≠ 0 := pow_ne_zero _ (NF.irreducible_π v).ne_zero
  let f : (Fin N → 𝔬) →ₗ[𝔬] (Fin N → 𝔬) := (NF.π v ^ k : 𝔬) • LinearMap.id
  have hfinj : Function.Injective f := by
    intro a b hab
    funext i
    have := congrFun hab i
    simp only [f, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hπ0 this
  have hrange : LinearMap.range f ≤ Λ₀ := by
    rintro _ ⟨u, rfl⟩
    rw [hΛ₀]
    apply hk
    intro i
    simp only [f, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [map_mul, map_pow, NF.valued_π, ← WithZero.exp_nsmul]
    calc WithZero.exp (k • (-1 : ℤ)) * Valued.v ((u i : 𝔬) : Fv) ≤ WithZero.exp (k • (-1 : ℤ)) * 1 :=
          mul_le_mul_right ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u i).2) _
      _ = WithZero.exp (-(k : ℤ)) := by rw [mul_one]; congr 1; simp
  have hrk : Module.finrank 𝔬 Λ₀ = N := by
    apply le_antisymm
    · simpa using Submodule.finrank_le Λ₀
    · have h1 := Submodule.finrank_mono hrange
      rw [LinearMap.finrank_range_of_inj hfinj] at h1
      simpa using h1
  have hn₀ : n₀ = N := by
    have := Module.finrank_eq_card_basis b
    rw [hrk] at this
    simpa using this.symm
  subst hn₀
  let P : Matrix (Fin n₀) (Fin n₀) 𝔬 := Matrix.of fun i j => ((b j : Λ₀) : Fin n₀ → 𝔬) i
  have hP : ∀ y, P *ᵥ y = ((b.equivFun.symm y : Λ₀) : Fin n₀ → 𝔬) := by
    intro y
    funext i
    rw [Module.Basis.equivFun_symm_apply]
    simp [P, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨P, ?_, fun y => ?_⟩
  · intro hdet
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hw0
    have h1 : b.equivFun.symm w = 0 := Subtype.ext (by rw [← hP, hw]; rfl)
    have := congrArg b.equivFun h1
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at this
    exact this
  · constructor
    · intro hy
      obtain ⟨z, hz⟩ := integral_of_mem_std' v (hle hy)
      have hzΛ : z ∈ Λ₀ := by rw [hΛ₀, hz]; exact hy
      refine ⟨b.equivFun ⟨z, hzΛ⟩, ?_⟩
      rw [← hz, ← coe_mulVec_o, hP, LinearEquiv.symm_apply_apply]
    · rintro ⟨c, rfl⟩
      rw [← coe_mulVec_o, hP]
      exact (hΛ₀ _).mp (b.equivFun.symm c).2

/-- **Lattices contain a box**: the lattice generated by the columns of $P$ contains $\pi^k\mathfrak o^N$. -/
theorem fw_hc {N : ℕ} {k : ℕ} (P : Matrix (Fin N) (Fin N) 𝔬) {X : Submodule 𝔬 (Fin N → Fv)}
    (hb : ball v (k : ℤ) ≤ X)
    (hX : ∀ y ∈ X, ∃ c : Fin N → 𝔬, P.map (algebraMap 𝔬 Fv) *ᵥ (fun i => (c i : Fv)) = y)
    (u : Fin N → 𝔬) : ∃ w, P *ᵥ w = NF.π v ^ k • u := by
  have hy : (fun i => ((NF.π v ^ k • u) i : Fv)) ∈ X := by
    apply hb
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [map_mul, map_pow, NF.valued_π, ← WithZero.exp_nsmul]
    calc WithZero.exp (k • (-1 : ℤ)) * Valued.v ((u i : 𝔬) : Fv) ≤ WithZero.exp (k • (-1 : ℤ)) * 1 :=
          mul_le_mul_right ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u i).2) _
      _ = WithZero.exp (-(k : ℤ)) := by rw [mul_one]; congr 1; simp
  obtain ⟨c, hc⟩ := hX _ hy
  refine ⟨c, coe_o_injective v ?_⟩
  show (fun i => ((P *ᵥ c) i : Fv)) = _
  rw [coe_mulVec_o, hc]

/-- **A frame whose columns lie in the lattice of $P$ is $P$ times an integral frame.** -/
theorem fw_exists_frame_preimage (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬)
    {X : Submodule 𝔬 (Fin (r + n') → Fv)}
    (hX : ∀ y ∈ X, ∃ c : Fin (r + n') → 𝔬, P.map (algebraMap 𝔬 Fv) *ᵥ (fun i => (c i : Fv)) = y)
    (y : Fin (r + n') × Fin r → 𝔬) (hy : ∀ j, (fun i => (y (i, j) : Fv)) ∈ X) :
    ∃ a, frameMat r P *ᵥ a = y := by
  choose c hc using fun j => hX _ (hy j)
  refine ⟨fun p => c p.2 p.1, funext fun ⟨i, j⟩ => ?_⟩
  rw [frameMat_mulVec_col]
  apply Subtype.ext
  have h1 := congrFun (hc j) i
  have h2 := congrFun (coe_mulVec_o v P (c j)) i
  show (((P *ᵥ fun l => c j l) i : 𝔬) : Fv) = (y (i, j) : Fv)
  rw [h2]; exact h1

theorem fw_det_pm (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (a : orthGroup QB Fv) :
    ((a : GL (Fin (r + n')) Fv).val).det = 1 ∨ ((a : GL (Fin (r + n')) Fv).val).det = -1 := by
  have hH := (mem_orthGroup_iff' QB).mp a.2
  have hdet : ((QB).hessian.map (algebraMap F Fv)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).mpr (fw_nondegF T₀ Q₀' hT hQ')
  have h := congrArg Matrix.det hH
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have h2 : (((a : GL (Fin (r + n')) Fv).val).det - 1) * (((a : GL (Fin (r + n')) Fv).val).det + 1) *
      ((QB).hessian.map (algebraMap F Fv)).det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left; linear_combination h4
    · right; linear_combination h4
  · exact absurd h3 hdet

theorem fw_exists_P2 {N : ℕ} (g : GL (Fin N) Fv) (P₁ : Matrix (Fin N) (Fin N) 𝔬)
    (hP₁ : ∀ j, (fun l => (P₁ l j : Fv)) ∈ locAct v g (std v)) :
    ∃ P₂ : Matrix (Fin N) (Fin N) 𝔬, P₂.map (algebraMap 𝔬 Fv) = g⁻¹.val * P₁.map (algebraMap 𝔬 Fv) := by
  have hb : ∀ i j, Valued.v ((g⁻¹.val * P₁.map (algebraMap 𝔬 Fv)) i j) ≤ 1 := by
    intro i j
    obtain ⟨z, hz, hgz⟩ := hP₁ j
    have hz' : g⁻¹.val *ᵥ (fun l => (P₁ l j : Fv)) = z := by
      rw [← hgz]
      show g⁻¹.val *ᵥ (g.val *ᵥ z) = z
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have := congrFun hz' i
    have e : (g⁻¹.val * P₁.map (algebraMap 𝔬 Fv)) i j = (g⁻¹.val *ᵥ (fun l => (P₁ l j : Fv))) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e, this]
    simpa using hz i
  exact ⟨Matrix.of fun i j => toO v _ (hb i j), Matrix.ext fun i j => rfl⟩

theorem fw_col_mem {N : ℕ} (P : Matrix (Fin N) (Fin N) 𝔬) {X : Submodule 𝔬 (Fin N → Fv)}
    (hX : ∀ c : Fin N → 𝔬, P.map (algebraMap 𝔬 Fv) *ᵥ (fun i => (c i : Fv)) ∈ X) (j : Fin N) :
    (fun l => (P l j : Fv)) ∈ X := by
  have := hX (Pi.single j 1)
  convert this using 1
  funext l
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem fw_hc_mono {N : ℕ} {k c : ℕ} (P : Matrix (Fin N) (Fin N) 𝔬)
    (h : ∀ u : Fin N → 𝔬, ∃ w, P *ᵥ w = NF.π v ^ k • u) (hkc : k ≤ c) :
    ∀ u : Fin N → 𝔬, ∃ w, P *ᵥ w = NF.π v ^ c • u := by
  intro u
  obtain ⟨w, hw⟩ := h (NF.π v ^ (c - k) • u)
  refine ⟨w, ?_⟩
  rw [hw, smul_smul, ← pow_add, Nat.add_sub_cancel' hkc]

theorem fw_mulVec_mem (κ : stdStab QB v) {Λ' : Submodule 𝔬 (Fin (r + n') → Fv)}
    (h : locAct v ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) Λ' = Λ') {y : Fin (r + n') → Fv}
    (hy : y ∈ Λ') : ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ y ∈ Λ' := by
  have : ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ y ∈
      locAct v ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) Λ' := ⟨y, hy, rfl⟩
  rwa [h] at this

theorem fw_conj_J0 (g : orthGroup QB Fv) (κ : stdStab QB v)
    (hκ : κ ∈ fwJ v T₀ Q₀' (locAct v (g : GL (Fin (r + n')) Fv) (std v))) :
    ∃ l : stdStab QB v,
      l ∈ fwJ v T₀ Q₀' (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)) ∧
      ((l : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val =
        ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
          (g : GL (Fin (r + n')) Fv).val := by
  have hmem : g⁻¹ * (κ : orthGroup QB Fv) * g ∈ stdStab QB v := by
    show locAct v ((g⁻¹ * (κ : orthGroup QB Fv) * g : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) = std v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [fw_conj_iff]
    exact (mem_fwJ v T₀ Q₀' κ).mp hκ
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [mem_fwJ]
    show locAct v ((g⁻¹ * (κ : orthGroup QB Fv) * g : orthGroup QB Fv) : GL (Fin (r + n')) Fv)
      (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)) =
        locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have e : (g : GL (Fin (r + n')) Fv)⁻¹ * ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) *
        (g : GL (Fin (r + n')) Fv) = (g : GL (Fin (r + n')) Fv)⁻¹ *
          ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) * ((g : GL (Fin (r + n')) Fv)⁻¹)⁻¹ := by
      rw [inv_inv]
    rw [e, fw_conj_iff']
    exact κ.2
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]

theorem fw_conj_J1 (g : orthGroup QB Fv) (l : stdStab QB v)
    (hl : l ∈ fwJ v T₀ Q₀' (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))) :
    ∃ κ : stdStab QB v, κ ∈ fwJ v T₀ Q₀' (locAct v (g : GL (Fin (r + n')) Fv) (std v)) ∧
      ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val =
        (g : GL (Fin (r + n')) Fv).val * ((l : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
          ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val := by
  have hl' := (mem_fwJ v T₀ Q₀' l).mp hl
  have e : locAct v (g : GL (Fin (r + n')) Fv)
      (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)) = std v := by
    rw [← locAct_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one, locAct_one]
  have hmem : g * (l : orthGroup QB Fv) * g⁻¹ ∈ stdStab QB v := by
    show locAct v ((g * (l : orthGroup QB Fv) * g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) = std v
    have := (fw_conj_iff' v (g : GL (Fin (r + n')) Fv) ((l : orthGroup QB Fv) : GL (Fin (r + n')) Fv)
      (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))).mpr hl'
    rw [e] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [mem_fwJ]
    show locAct v ((g * (l : orthGroup QB Fv) * g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv)
      (locAct v (g : GL (Fin (r + n')) Fv) (std v)) = locAct v (g : GL (Fin (r + n')) Fv) (std v)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [fw_conj_iff']
    exact l.2
  · simp only [Subgroup.coe_mul, Units.val_mul]

/-- **Transport of near counts by $h = g^{-1}$:** $N_{k,s}(J_1x) = N_{k,s}(J_0E)$ for $k \gg s \gg 0$. -/
theorem fw_orbit_transport (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (g : orthGroup QB Fv)
    (x : Fin (r + n') × Fin r → 𝔬) (hx : formF Qo x = tc To)
    (hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) =
      coeFrame v x) :
    ∃ s₀ k₀ : ℕ, ∀ s k : ℕ, s₀ ≤ s → s + k₀ ≤ k →
      gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀')
        (fwJ v T₀ Q₀' (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v))) x) =
      gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀')
        (fwJ v T₀ Q₀' (locAct v (g : GL (Fin (r + n')) Fv) (std v))) (stdFrame (A := 𝔬) (r := r) (n' := n'))) := by
  classical
  have hπ := NF.irreducible_π v
  set Gm := (g : GL (Fin (r + n')) Fv).val with hGm
  set Hm := ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val with hHm
  have hGH : Gm * Hm = 1 := by
    rw [hGm, hHm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hHG : Hm * Gm = 1 := by
    rw [hGm, hHm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hgE : Gm * coeFrame v x = (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
    rw [← hgx, ← Matrix.mul_assoc, hGH, Matrix.one_mul]
  set Λ0 := locAct v (g : GL (Fin (r + n')) Fv) (std v) with hΛ0def
  set Λ1 := locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) with hΛ1def
  have hΛ0 : Λ0.IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  have hΛ1 : Λ1.IsLattice Fv := locAct_isLattice _ (std_isLattice v)
  obtain ⟨k0, hk0, -⟩ := exists_local_bounds v hΛ0
  have hball : ball v (k0 : ℤ) ≤ (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)) :=
    le_inf (ball_anti v (by omega)) hk0
  have hΛ : (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)).IsLattice Fv :=
    isLattice_of_bounds v (k := (k0 : ℤ)) (k' := 0) hball inf_le_left
  obtain ⟨P₁, hdet₁, hP₁⟩ := fw_exists_basisMat v (inf_le_left : (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)) ≤ std v) hΛ
  have hcolΛ : ∀ j, (fun l => (P₁ l j : Fv)) ∈ (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)) :=
    fun j => fw_col_mem v P₁ (fun c => (hP₁ _).mpr ⟨c, rfl⟩) j
  obtain ⟨P₂, hP₂⟩ := fw_exists_P2 v (g : GL (Fin (r + n')) Fv) P₁ (fun j => (inf_le_right : _ ≤ Λ0) (hcolΛ j))
  have hP₂' : P₂.map (algebraMap 𝔬 Fv) = Hm * P₁.map (algebraMap 𝔬 Fv) := hP₂
  -- determinants
  have hdm : ∀ P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬, (P.map (algebraMap 𝔬 Fv)).det = ((P.det : 𝔬) : Fv) := by
    intro P
    have := RingHom.map_det (algebraMap 𝔬 Fv) P
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  have hdetrel : ((P₂.det : 𝔬) : Fv) = Hm.det * ((P₁.det : 𝔬) : Fv) := by
    rw [← hdm, ← hdm, hP₂', Matrix.det_mul]
  have hassoc : Associated P₁.det P₂.det ∧ P₂.det ≠ 0 := by
    have hne1 : ((P₁.det : 𝔬) : Fv) ≠ 0 := fun h => hdet₁ (Subtype.ext h)
    rcases fw_det_pm v T₀ Q₀' hT hQ' (g⁻¹) with h | h
    · have h' : Hm.det = 1 := h
      have : P₂.det = P₁.det := Subtype.ext (by rw [hdetrel, h']; simp)
      exact ⟨⟨1, by simp [this]⟩, this ▸ hdet₁⟩
    · have h' : Hm.det = -1 := h
      have : P₂.det = -P₁.det := Subtype.ext (by rw [hdetrel, h']; simp)
      exact ⟨⟨-1, by simp [this]⟩, by rw [this]; exact neg_ne_zero.mpr hdet₁⟩
  -- the Gram forms agree
  have hQ : (Qo).compMat P₁ = (Qo).compMat P₂ := by
    refine NF.map_injective (f := algebraMap 𝔬 Fv) Subtype.val_injective ?_
    rw [← QuadForm.map_compMat, ← QuadForm.map_compMat, ← fl_QB_map, hP₂']
    exact (fl_compMat_orth v QB (g⁻¹ : orthGroup QB Fv).2 (P₁.map (algebraMap 𝔬 Fv))).symm
  -- the lattices contain a box
  have hc₁ : ∀ u : Fin (r + n') → 𝔬, ∃ w, P₁ *ᵥ w = NF.π v ^ k0 • u :=
    fw_hc v P₁ (X := std v ⊓ Λ0) hball (fun y hy => (hP₁ y).mp hy)
  have hΛ' : (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv))).IsLattice Fv :=
    locAct_isLattice _ hΛ
  obtain ⟨k2, hk2, -⟩ := exists_local_bounds v hΛ'
  have hc₂ : ∀ u : Fin (r + n') → 𝔬, ∃ w, P₂ *ᵥ w = NF.π v ^ k2 • u := by
    refine fw_hc v P₂ hk2 (fun y hy => ?_)
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨c, hc⟩ := (hP₁ y').mp hy'
    refine ⟨c, ?_⟩
    show P₂.map (algebraMap 𝔬 Fv) *ᵥ (fun i => (c i : Fv)) = Hm *ᵥ y'
    rw [hP₂', ← hc, Matrix.mulVec_mulVec]
  set c := max k0 k2 with hc
  have hc₁' := fw_hc_mono v P₁ hc₁ (le_max_left k0 k2)
  have hc₂' := fw_hc_mono v P₂ hc₂ (le_max_right k0 k2)
  -- the orbits
  set ρ := frameRepK v T₀ Q₀' with hρ
  set J0 := fwJ v T₀ Q₀' Λ0 with hJ0
  set J1 := fwJ v T₀ Q₀' Λ1 with hJ1
  have hE : formF Qo (stdFrame (A := 𝔬) (r := r) (n' := n')) = tc To := fw_formF_std v T₀ Q₀'
  have hEcol : ∀ j, (fun i => (((stdFrame (A := 𝔬) (r := r) (n' := n')) (i, j) : 𝔬) : Fv)) =
      fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) i j := by
    intro j; funext i
    have := congrFun (congrFun (coeFrame_stdFrame (v := v) (r := r) (n' := n')) i) j
    exact this
  -- columns of `E` lie in `Λ = L ∩ gL`
  have hEΛ : ∀ j, (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) i j) ∈
      (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)) := by
    intro j
    refine ⟨stdCol_mem_std v j, ?_⟩
    refine ⟨fun i => (x (i, j) : Fv), coe_mem_std' v (fun i => x (i, j)), ?_⟩
    show Gm *ᵥ (fun i => (x (i, j) : Fv)) = _
    funext i
    have := congrFun (congrFun hgE i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, coeFrame] using this
  have hcolK : ∀ (κ : stdStab QB v), κ ∈ J0 → ∀ j,
      (fun i => (((ρ κ *ᵥ (stdFrame (A := 𝔬) (r := r) (n' := n'))) (i, j) : 𝔬) : Fv)) ∈
        (std v ⊓ Λ0 : Submodule 𝔬 (Fin (r + n') → Fv)) := by
    intro κ hκ j
    have hκ' := (mem_fwJ v T₀ Q₀' κ).mp hκ
    have e : (fun i => (((ρ κ *ᵥ (stdFrame (A := 𝔬) (r := r) (n' := n'))) (i, j) : 𝔬) : Fv)) =
        ((κ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *ᵥ
          (fun i => (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) i j) := by
      funext i
      have := congrFun (congrFun (fw_coeFrame_rho v T₀ Q₀' κ (stdFrame (A := 𝔬) (r := r) (n' := n')))  i) j
      rw [coeFrame_stdFrame] at this
      exact this
    rw [e]
    exact ⟨fw_mulVec_mem v T₀ Q₀' κ κ.2 (hEΛ j).1, fw_mulVec_mem v T₀ Q₀' κ hκ' (hEΛ j).2⟩
  -- the set `A` of integral preimages
  set B0 := gOrbit ρ J0 (stdFrame (A := 𝔬) (r := r) (n' := n')) with hB0
  set B1 := gOrbit ρ J1 x with hB1
  have hC0 : ∀ y ∈ B0, ∃ a, frameMat r P₁ *ᵥ a = y ∧ frameMat r P₁ *ᵥ a ∈ B0 := by
    rintro y ⟨κ, hκ, rfl⟩
    obtain ⟨a, ha⟩ := fw_exists_frame_preimage v P₁ (X := std v ⊓ Λ0) (fun y hy => (hP₁ y).mp hy)
      (ρ κ *ᵥ stdFrame) (hcolK κ hκ)
    exact ⟨a, ha, by rw [ha]; exact ⟨κ, hκ, rfl⟩⟩
  set A : Set (Fin (r + n') × Fin r → 𝔬) := {a | frameMat r P₁ *ᵥ a ∈ B0} with hA
  have himg1 : (frameMat r P₁ *ᵥ ·) '' A = B0 := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hy
      obtain ⟨a, ha, ha'⟩ := hC0 y hy
      exact ⟨a, ha', ha⟩
  have e1 : ∀ a : Fin (r + n') × Fin r → 𝔬,
      coeFrame v (frameMat r P₂ *ᵥ a) = Hm * coeFrame v (frameMat r P₁ *ᵥ a) := by
    intro a
    rw [fw_coeFrame_frameMat, fw_coeFrame_frameMat, hP₂', Matrix.mul_assoc]
  have hHGY : ∀ Y : Matrix (Fin (r + n')) (Fin r) Fv, Hm * (Gm * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hHG, Matrix.one_mul]
  have hC1a : ∀ a ∈ A, frameMat r P₂ *ᵥ a ∈ B1 := by
    intro a ha
    obtain ⟨κ, hκ, hκa⟩ := ha
    obtain ⟨l, hl, hlv⟩ := fw_conj_J0 v T₀ Q₀' g κ hκ
    refine ⟨l, hl, ?_⟩
    apply fw_coeFrame_inj v
    rw [e1, ← hκa, fw_coeFrame_rho, fw_coeFrame_rho, hlv, coeFrame_stdFrame, ← hgE]
    simp only [hGm, hHm, Matrix.mul_assoc]
  have himg2 : (frameMat r P₂ *ᵥ ·) '' A = B1 := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩; exact hC1a a ha
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨κ, hκ, hκv⟩ := fw_conj_J1 v T₀ Q₀' g l hl
      obtain ⟨a, ha, haB⟩ := hC0 (ρ κ *ᵥ stdFrame) ⟨κ, hκ, rfl⟩
      refine ⟨a, haB, ?_⟩
      apply fw_coeFrame_inj v
      rw [e1, ha, fw_coeFrame_rho, fw_coeFrame_rho, hκv, coeFrame_stdFrame, ← hgx]
      simp only [Matrix.mul_assoc]
      exact hHGY _
  -- saturation and the conclusion
  obtain ⟨sa, hsa⟩ := fw_orbit_sat v T₀ Q₀' hT hQ' hΛ0
  obtain ⟨sb, hsb⟩ := fw_orbit_sat v T₀ Q₀' hT hQ' hΛ1
  have hTo : (To).hessian.det ≠ 0 := NF.nondegenerate_Qp v hT
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hTo
  have hsat₁ : ∀ a ∈ A, ∀ z, formF Qo z = tc To →
      (∀ i, NF.π v ^ (max sa sb) ∣ z i - (frameMat r P₁ *ᵥ a) i) → ∃ a' ∈ A, z = frameMat r P₁ *ᵥ a' := by
    intro a ha z hz hza
    have hzB : z ∈ B0 := hsa (max sa sb) (le_max_left _ _) stdFrame hE (frameMat r P₁ *ᵥ a) ha z hz hza
    obtain ⟨a', ha'eq, ha'B⟩ := hC0 z hzB
    exact ⟨a', ha'B, ha'eq.symm⟩
  have hsat₂ : ∀ a ∈ A, ∀ z, formF Qo z = tc To →
      (∀ i, NF.π v ^ (max sa sb) ∣ z i - (frameMat r P₂ *ᵥ a) i) → ∃ a' ∈ A, z = frameMat r P₂ *ᵥ a' := by
    intro a ha z hz hza
    have hzB : z ∈ B1 := hsb (max sa sb) (le_max_right _ _) x hx (frameMat r P₂ *ᵥ a) (hC1a a ha) z hz hza
    rw [← himg2] at hzB
    obtain ⟨a', ha', rfl⟩ := hzB
    exact ⟨a', ha', rfl⟩
  refine ⟨max sa sb, c + d + (2 * d + 1), fun s k hs hk => ?_⟩
  have key := frameNear_eq_of_compMat_eq hπ Qo To hd hd' hdet₁ hassoc.2 hassoc.1 hQ hc₁' hc₂' hsat₁ hsat₂
    (k := k) (s := s) hs (by omega) (by omega)
  rw [himg1, himg2] at key
  exact key.symm

/-- **The orbit of a type against the orbit of $E$** (the heart of Weil's argument, finite form): for $g \in O(V)(F_\mathfrak p)$ with
$x = g^{-1}E$ integral, $N_{k,s}(Kx) = w(gL)\,N_{k,s}(KE)$ for $k \gg s \gg 0$. *Proof:* with $h = g^{-1}$, $J_0 = K\cap h^{-1}Kh$ (the
elements of $K$ stabilizing $gL$) and $J_1 = K\cap hKh^{-1}$: the orbit comparison `gNear_mul_relIndex` at $E$ with $J_0$ and at $x$ with
$J_1$ (openness from `exists_frame_openMat`: an integral isometry $\equiv 1 \bmod \pi^{2c}$ stabilizes every lattice between
$\pi^c L$ and $\pi^{-c}L$); $J_1x = h\,J_0E$ and $N(hB) = N(B)$ for $B = J_0E$ (`frameNear_eq_of_compMat_eq` with a basis $P_1$ of
$L\cap gL$ and $P_2 = hP_1$, a basis of $hL\cap L$); $[K : J_1] = [K : J_0]$ (`modRatio_eq_one`); and the stabilizers of $E$ and
$x$ in $K$, cut by $J_0$, $J_1$, are $\mathrm{diag}(1_r, \cdot)$ of $K_0'$, $K_{gL}$, cut by $K_0'\cap K_{gL}$ (`exists_orthEmbB_eq`,
`relIndex_stab_eq`). -/
@[kb "weil1982" "§3.4 (orbit measures and lattice stabilizers) [unverified]"]
theorem frameNear_type (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (g : orthGroup QB Fv)
    (x : Fin (r + n') × Fin r → 𝔬) (hx : formF Qo x = tc To)
    (hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x) :
    ∃ s₀ k₀ : ℕ, ∀ s k : ℕ, s₀ ≤ s → s + k₀ ≤ k →
      (gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') ⊤ x) : ℝ) =
        locFrameWeight v TF QF' (framePt v T₀ Q₀' g x hgx) *
          gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') ⊤ stdFrame) := by
  have hgx' : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = coeFrame v x := hgx
  obtain ⟨s₀, k₀, htr⟩ := fw_orbit_transport v T₀ Q₀' hT hQ' g x hx hgx'
  have hΛ0 : (locAct v (g : GL (Fin (r + n')) Fv) (std v)).IsLattice Fv :=
    locAct_isLattice _ (std_isLattice v)
  have hΛ1 : (locAct v ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v)).IsLattice Fv :=
    locAct_isLattice _ (std_isLattice v)
  obtain ⟨sa, hA⟩ := fw_gNear_J v T₀ Q₀' hT hQ' hΛ0
  obtain ⟨sb, hB⟩ := fw_gNear_J v T₀ Q₀' hT hQ' hΛ1
  refine ⟨max (max s₀ sa) sb, k₀, fun s k hs hk => ?_⟩
  have hsk : s ≤ k := by omega
  have hE := hA s k (by omega) hsk (stdFrame (A := 𝔬) (r := r) (n' := n')) (fw_formF_std v T₀ Q₀')
  have hX := hB s k (by omega) hsk x hx
  have h2 := htr s k (by omega) hk
  have hidx := fw_index_eq v T₀ Q₀' hT hQ' g
  have ha : (fwJ v T₀ Q₀' (locAct v (g : GL (Fin (r + n')) Fv) (std v))).relIndex
      (gStab (frameRepK v T₀ Q₀') (stdFrame (A := 𝔬) (r := r) (n' := n'))) =
      (stabilizer (orthGroup QF' Fv) (framePt v T₀ Q₀' g x hgx)).relIndex (stdStab QF' v) :=
    fw_relIndex_E v T₀ Q₀' hT (framePt v T₀ Q₀' g x hgx)
  have hb := fw_relIndex_x v T₀ Q₀' hT g x hgx' (framePt v T₀ Q₀' g x hgx) rfl
  have hne := fw_relIndex_ne_zero v T₀ Q₀' (framePt v T₀ Q₀' g x hgx) hΛ0
  rw [ha] at hE
  rw [hb] at hX
  have hnat : gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') ⊤ x) *
        (stdStab QF' v).relIndex (stabilizer (orthGroup QF' Fv) (framePt v T₀ Q₀' g x hgx)) =
      (stabilizer (orthGroup QF' Fv) (framePt v T₀ Q₀' g x hgx)).relIndex (stdStab QF' v) *
        gNear (formF Qo) (tc To) (NF.π v) k s (gOrbit (frameRepK v T₀ Q₀') ⊤ stdFrame) := by
    rw [hX, h2, ← hidx, Nat.mul_comm ((stabilizer (orthGroup QF' Fv) (framePt v T₀ Q₀' g x hgx)).relIndex
      (stdStab QF' v)), hE]
  unfold locFrameWeight
  rw [div_mul_eq_mul_div, eq_div_iff (by exact_mod_cast hne)]
  exact_mod_cast hnat

end Weight

end QuadFormsKB.Tamagawa.Frames
