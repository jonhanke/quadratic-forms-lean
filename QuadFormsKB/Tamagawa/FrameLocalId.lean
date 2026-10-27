/-
# Weil's local orbital identity for frames, every prime

**Layer:** the completion $\mathfrak o_\mathfrak p \subset F_\mathfrak p$ of a number field at a finite prime (dyadic included).

**Proves** **`frameLocalIdentity`**: $W_\mathfrak p\,\beta_\mathfrak p(Q, Q)\,|\det H_T|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q', Q')\,\beta_\mathfrak p(Q, T)$ for
$Q = T_0\perp Q_0'$ (Weil 1982, §3.4 [unverified]; Kitaoka 1993, §5.6 [unverified]). *Proof:* for $k \gg s \gg 0$ the frames of $T$ mod
$\pi^k$ are the disjoint union of the near sets of the $K$-orbits of the integral frames (`card_sol_eq_sum_gNear`; Hensel for frames, openness
`exists_frame_openMat`); these orbits are the local types (`exists_frameType_data`, `exists_frame_eq_inv_mul`, `mem_orbit_of_frame`), finitely
many; each orbit has $w$ times the points of the orbit of $E$ (`frameNear_type`), which has $|O(Q\bmod\pi^k)|/(q^{dn'}|O(Q'\bmod\pi^k)|)$
points (`frameNear_stdFrame`); normalize (`localDensityForm_eventually_eq`, `localDensityForm_self_eq_card`).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameWeight
import QuadFormsKB.Lattices.CartanDieudonne

open Matrix MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa Lattices NumberField IsDedekindDomain

/-! ### Universe-polymorphic copies of the diagonalization and the norm lemma -/

section Poly

variable {F : Type*} [Field F] [NumberField F] {r : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem lid_hessian_map_alg (T₀ : QuadForm (𝓞 F) r) :
    (T₀.map (algebraMap (𝓞 F) F)).hessian = T₀.hessian.map (algebraMap (𝓞 F) F) := by
  ext i j; simp [QuadForm.hessian, QuadForm.map]

theorem lid_hessian_diag (dg : Fin r → 𝓞 F) :
    (QuadForm.diag dg).hessian = Matrix.diagonal (fun i => 2 * dg i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [QuadForm.hessian, QuadForm.diag, two_mul]
  · simp [QuadForm.hessian, QuadForm.diag, h]

/-- Universe-polymorphic copy of `exists_diag_global`. -/
theorem lid_exists_diag_global (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    ∃ (P : Matrix (Fin r) (Fin r) (𝓞 F)) (dg : Fin r → 𝓞 F), P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧
      T₀.compMat P = QuadForm.diag dg := by
  classical
  set T := T₀.map (algebraMap (𝓞 F) F) with hTdef
  have hTF : T.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hTdef, lid_hessian_map_alg, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
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
    rw [e1, hcol i, hcol j, ← lid_hessian_map_alg, ← hTdef, smul_dotProduct, mulVec_smul, dotProduct_smul]
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
  rw [QuadForm.hessian_compMat, lid_hessian_diag] at h1
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hP0, mul_zero] at h2
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero two_ne_zero (hdg i)) h2.symm

/-- Universe-polymorphic copy of `exists_diag_local`. -/
theorem lid_exists_diag_local (T₀ : QuadForm (𝓞 F) r) (hT : T₀.Nondegenerate) :
    ∃ (P : Matrix (Fin r) (Fin r) (v.adicCompletionIntegers F)) (dg : Fin r → v.adicCompletionIntegers F),
      P.det ≠ 0 ∧ (∀ i, dg i ≠ 0) ∧ (NF.Qp v T₀).compMat P = QuadForm.diag dg := by
  obtain ⟨P, dg, hP, hdg, h⟩ := lid_exists_diag_global T₀ hT
  refine ⟨P.map (NF.ι v), fun i => NF.ι v (dg i), ?_, fun i => NF.ι_ne_zero v (hdg i), ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact NF.ι_ne_zero v hP
  · rw [NF.Qp, QuadForm.map_compMat, h]
    ext i j
    simp [QuadForm.map, QuadForm.diag, Matrix.diagonal_apply]

theorem lid_norm_eq_absNorm_pow {x : v.adicCompletion F} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v x) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valued.v).ne_zero_iff.mpr hx)]
  push_cast; rfl

theorem lid_norm_coe_of_pow_dvd {x : v.adicCompletionIntegers F} {e : ℕ} (he : NF.π v ^ e ∣ x)
    (he' : ¬ NF.π v ^ (e + 1) ∣ x) :
    ‖((x : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ e)⁻¹ := by
  obtain ⟨u, rfl⟩ := he
  have hu : IsUnit u := by
    refine DVR.dvr_isUnit_of_not_dvd (NF.irreducible_π v) fun h => he' ?_
    rw [pow_succ]; exact mul_dvd_mul_left _ h
  have hv : Valued.v (((NF.π v ^ e * u : v.adicCompletionIntegers F)) : v.adicCompletion F) =
      WithZero.exp (-(e : ℤ)) := by
    push_cast
    rw [map_mul, map_pow, NF.valued_π, (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu,
      mul_one, ← WithZero.exp_nsmul]
    congr 1; simp
  have hx0 : ((NF.π v ^ e * u : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  rw [lid_norm_eq_absNorm_pow v hx0, hv, WithZero.log_exp, NF.q_completion, _root_.zpow_neg, zpow_natCast]

end Poly

/-! ### Orbits, disjointness and covering -/

section Counting

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F)) (T₀ : QuadForm (𝓞 F) r)
  (Q₀' : QuadForm (𝓞 F) n')

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "TF" => T₀.map (algebraMap (𝓞 F) F)
local notation "QF'" => Q₀'.map (algebraMap (𝓞 F) F)
local notation "QB" => blockForm TF QF'
local notation "Qo" => NF.Qp v (blockForm T₀ Q₀')
local notation "To" => NF.Qp v T₀

theorem lid_coeFrame_frameMat (P : Matrix (Fin (r + n')) (Fin (r + n')) 𝔬) (x : Fin (r + n') × Fin r → 𝔬) :
    coeFrame v (frameMat r P *ᵥ x) = P.map (algebraMap 𝔬 Fv) * coeFrame v x := by
  have e : ∀ y : Fin (r + n') × Fin r → 𝔬, coeFrame v y = (toMat y).map (algebraMap 𝔬 Fv) := fun y => rfl
  rw [e, e, toMat_frameMat_mulVec, Matrix.map_mul]

theorem lid_coeFrame_injective {x y : Fin (r + n') × Fin r → 𝔬} (h : coeFrame v x = coeFrame v y) : x = y := by
  funext p
  exact Subtype.ext (congrFun (congrFun h p.1) p.2)

theorem lid_nondeg_block (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) :
    (blockForm T₀ Q₀').Nondegenerate := by
  rw [QuadForm.Nondegenerate, det_hessian_blockForm]
  exact mul_ne_zero hT hQ'

theorem lid_Qo_nondeg (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) : (Qo).Nondegenerate :=
  NF.nondegenerate_Qp v (lid_nondeg_block T₀ Q₀' hT hQ')

/-- The orbits of $K$ (via `intRep`) and of all integral isometries coincide. -/
theorem lid_gOrbit_eq (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate) (y : Fin (r + n') × Fin r → 𝔬) :
    gOrbit (frameRepK v T₀ Q₀') ⊤ y = gOrbit (frameRep (Qo) r) ⊤ y := by
  have hQo := isIntModel_blockForm v T₀ Q₀'
  have hnd := lid_Qo_nondeg v T₀ Q₀' hT hQ'
  ext z
  constructor
  · rintro ⟨κ, -, rfl⟩
    refine ⟨isomOf hnd (intRep v QB κ) (compMat_intRep v hQo κ), Subgroup.mem_top _, ?_⟩
    rfl
  · rintro ⟨κ, -, rfl⟩
    obtain ⟨κ', hκ'⟩ := exists_intRep_eq v hQo hnd (κ : GL (Fin (r + n')) 𝔬).val (compMat_frameRep _ κ)
    refine ⟨κ', Subgroup.mem_top _, ?_⟩
    show frameMat r (intRep v QB κ') *ᵥ y = _
    rw [hκ']
    rfl

/-- **Disjointness:** frames in the $K$-orbits of $x$, $x'$ that are congruent mod $\pi^s$ give the same local type. -/
theorem lid_disj (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate)
    {P : Matrix (Fin r) (Fin r) 𝔬} (hPdet : P.det ≠ 0) {dg : Fin r → 𝔬}
    (hP : (To).compMat P = QuadForm.diag dg) (hdg : ∀ i, dg i ≠ 0) {f : ℕ}
    (hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i) {s : ℕ} (hs : r * f + 1 ≤ s)
    (M M' : LocFrameSet v TF QF') (x x' : Fin (r + n') × Fin r → 𝔬)
    (hx : formF (Qo) x = tc To) (hx' : formF (Qo) x' = tc To) (g g' : orthGroup QB Fv)
    (hg : locAct v (g : GL (Fin (r + n')) Fv) (std v) = M.1)
    (hg' : locAct v (g' : GL (Fin (r + n')) Fv) (std v) = M'.1)
    (hgx : ((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x)
    (hgx' : ((g'⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v x')
    (a a' : Fin (r + n') × Fin r → 𝔬) (ha : a ∈ gOrbit (frameRepK v T₀ Q₀') ⊤ x)
    (ha' : a' ∈ gOrbit (frameRepK v T₀ Q₀') ⊤ x') (haa' : ∀ i, NF.π v ^ s ∣ a i - a' i) :
    (Quotient.mk'' M : LocFrameTypes v TF QF') = Quotient.mk'' M' := by
  have hQo := isIntModel_blockForm v T₀ Q₀'
  have hnd := lid_Qo_nondeg v T₀ Q₀' hT hQ'
  have hπ := NF.irreducible_π v
  obtain ⟨κ, -, rfl⟩ := ha
  obtain ⟨κ', -, rfl⟩ := ha'
  have hρ : ∀ κ : stdStab QB v, frameRepK v T₀ Q₀' κ = frameMat r (intRep v QB κ) := fun κ => rfl
  have hxa : ∀ (κ : stdStab QB v) (z : Fin (r + n') × Fin r → 𝔬), formF (Qo) z = tc To →
      formF (Qo) (frameRepK v T₀ Q₀' κ *ᵥ z) = tc To := by
    intro κ z hz
    rw [hρ, formF_frameMat_of_compMat _ (compMat_intRep v hQo κ), hz]
  obtain ⟨M₀, hM₀, hM₀x, -⟩ := exists_frame_openMat hπ (Qo) To hPdet hP hdg hf hs (hxa κ x hx) (hxa κ' x' hx')
    (fun i => by rw [← dvd_neg, neg_sub]; exact haa' i)
  obtain ⟨τ, hτ⟩ := exists_intRep_eq v hQo hnd M₀ hM₀
  have hτ' : frameRepK v T₀ Q₀' τ = frameMat r M₀ := by rw [hρ, hτ]
  set κ'' : stdStab QB v := κ'⁻¹ * τ * κ with hκ''
  have key : frameRepK v T₀ Q₀' κ'' *ᵥ x = x' := by
    rw [hκ'', map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hτ', hM₀x, mulVec_inv_mulVec_g]
  have hκ : ((κ'' : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (((g⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv)) =
        ((g'⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) := by
    have h0 : ((κ'' : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * coeFrame v x = coeFrame v x' := by
      rw [← intRep_map v QB κ'', ← lid_coeFrame_frameMat]
      exact congrArg (coeFrame v) key
    rw [← hgx, ← hgx'] at h0
    exact h0
  exact (Quotient.sound' (mem_orbit_of_frame v T₀ Q₀' hT M M' g g' hg hg' κ'' hκ)).symm

theorem lid_mat_aux (A B C C' : Matrix (Fin (r + n')) (Fin (r + n')) Fv)
    (E : Matrix (Fin (r + n')) (Fin r) Fv) (h1 : C * C' = 1) (h2 : B * E = E) :
    A * B * C * (C' * E) = A * E := by
  rw [Matrix.mul_assoc (A * B) C (C' * E), ← Matrix.mul_assoc C C', h1, Matrix.one_mul, Matrix.mul_assoc, h2]

/-- **Covering:** every integral frame of $T$ lies in the $K$-orbit of $x_t$ for some local type $t$. -/
theorem lid_cover (hT : T₀.Nondegenerate) (hQ' : Q₀'.Nondegenerate)
    (x : LocFrameTypes v TF QF' → Fin (r + n') × Fin r → 𝔬) (g : LocFrameTypes v TF QF' → orthGroup QB Fv)
    (hloc : ∀ t, locAct v ((g t : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) = (locFrameRep v TF QF' t).1)
    (hgx : ∀ t, (((g t)⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val * stdFrameMat = coeFrame v (x t))
    (y : Fin (r + n') × Fin r → 𝔬) (hy : formF (Qo) y = tc To) :
    ∃ t, y ∈ gOrbit (frameRepK v T₀ Q₀') ⊤ (x t) := by
  obtain ⟨gy, hgy⟩ := exists_frame_eq_inv_mul v T₀ Q₀' hT hQ' y hy
  set M := framePt v T₀ Q₀' gy y hgy with hM
  set t : LocFrameTypes v TF QF' := Quotient.mk'' M with ht
  obtain ⟨h', hh'⟩ : locFrameRep v TF QF' t ∈ orbit (orthGroup QF' Fv) M :=
    Quotient.exact' (locFrameRep_mk v TF QF' t)
  set φ := orthEmbB TF QF' Fv
  set κo : orthGroup QB Fv := gy⁻¹ * (φ h')⁻¹ * g t with hκo
  have h1 : locAct v ((g t : orthGroup QB Fv) : GL (Fin (r + n')) Fv) (std v) =
      locAct v ((φ h' : orthGroup QB Fv) : GL (Fin (r + n')) Fv)
        (locAct v (gy : GL (Fin (r + n')) Fv) (std v)) := by
    rw [hloc t, ← hh']; rfl
  have hκK : κo ∈ stdStab QB v := by
    show locAct v (κo : GL (Fin (r + n')) Fv) (std v) = std v
    simp only [hκo, Subgroup.coe_mul, Subgroup.coe_inv, locAct_mul]
    rw [h1, locAct_inv_locAct, locAct_inv_locAct]
  refine ⟨t, ⟨⟨κo, hκK⟩, Subgroup.mem_top _, ?_⟩⟩
  apply lid_coeFrame_injective v
  have e1 : frameRepK v T₀ Q₀' ⟨κo, hκK⟩ = frameMat r (intRep v QB ⟨κo, hκK⟩) := rfl
  rw [e1, lid_coeFrame_frameMat, intRep_map, ← hgx t, ← hgy]
  have hcc : ((g t : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (((g t)⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hφ : (((φ h')⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val *
      (stdFrameMat : Matrix (Fin (r + n')) (Fin r) Fv) = stdFrameMat := by
    rw [← map_inv]; exact orthEmbB_mul_stdFrameMat TF QF' Fv h'⁻¹
  simp only [hκo, Subgroup.coe_mul, Units.val_mul]
  exact lid_mat_aux v (((gy⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val)
    ((((φ h')⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val) (((g t : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val)
    ((((g t)⁻¹ : orthGroup QB Fv) : GL (Fin (r + n')) Fv).val) stdFrameMat hcc hφ

end Counting

/-- Triangular numbers: $\binom{r+n'}{2} = (n'r + r^2 - \binom{r+1}{2}) + \binom{n'}{2}$ (the exponents of the densities). -/
theorem lid_tri (r n' : ℕ) :
    (r + n') * (r + n' - 1) / 2 = ((r + n') * r - r * (r + 1) / 2) + n' * (n' - 1) / 2 := by
  have e1 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self r)
  have e2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n')
  have e3 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (r + n'))
  generalize r * (r + 1) / 2 = a at *
  generalize n' * (n' - 1) / 2 = b at *
  generalize (r + n') * (r + n' - 1) / 2 = c at *
  rcases Nat.eq_zero_or_pos n' with rfl | hn
  · simp only [add_zero, Nat.zero_sub, mul_zero] at *
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · omega
    · have e4 : r * r = r * (r - 1) + r := by
        obtain ⟨u, rfl⟩ : ∃ u, r = u + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      have : r * (r + 1) = r * r + r := by ring
      omega
  · obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    have h1 : (r + (m + 1)) * (r + (m + 1) - 1) = r * r + 2 * r * m + m * m + r + m := by
      have : r + (m + 1) - 1 = r + m := by omega
      rw [this]; ring
    have h2 : r * (r + 1) = r * r + r := by ring
    have h3 : (m + 1) * m = m * m + m := by ring
    have h4 : (r + (m + 1)) * r = r * r + r * m + r := by ring
    have h5 : r * m = m * r := mul_comm _ _
    have h6 : 2 * r * m = 2 * (r * m) := by ring
    omega

/-! ### The local identity -/

section Main

variable {F : Type*} [Field F] [NumberField F] {r n' : ℕ} (v : HeightOneSpectrum (𝓞 F))

/-- **Weil's local orbital identity for frames** at every finite prime (dyadic included): for $T_0$, $Q_0'$ nondegenerate over $\mathcal O_F$
and $Q = T_0\perp Q_0'$,
$$W_\mathfrak p\cdot\beta_\mathfrak p(Q, Q)\cdot|\det H_{T_0}|_\mathfrak p^{\,n'} = \beta_\mathfrak p(Q_0', Q_0')\cdot\beta_\mathfrak p(Q, T_0),$$
$W_\mathfrak p$ = `locFrameTypeSum`, $\beta_\mathfrak p$ = `NF.localDensityForm` (no factor $\tfrac12$), $|\cdot|_\mathfrak p$ the normalized absolute
value. For $r = 1$, $T_0 = \langle m\rangle$ it is the `LocalOrbitalIdentityAt` ($\det H_T = 2m$). -/
@[kb "weil1982" "§3.4 (the local fibration O(V) → frames) [unverified]"]
theorem frameLocalIdentity (T₀ : QuadForm (𝓞 F) r) (Q₀' : QuadForm (𝓞 F) n') (hT : T₀.Nondegenerate)
    (hQ' : Q₀'.Nondegenerate) :
    locFrameTypeSum v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) *
        NF.localDensityForm v (blockForm T₀ Q₀') (blockForm T₀ Q₀') *
        ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ ^ n' =
      NF.localDensityForm v Q₀' Q₀' * NF.localDensityForm v (blockForm T₀ Q₀') T₀ := by
  classical
  have hπ := NF.irreducible_π v
  have hQbl : NF.Qp v (blockForm T₀ Q₀') = blockForm (NF.Qp v T₀) (NF.Qp v Q₀') :=
    map_blockForm (NF.ι v) T₀ Q₀'
  have hTo : (NF.Qp v T₀).Nondegenerate := NF.nondegenerate_Qp v hT
  have hQ'o : (NF.Qp v Q₀').Nondegenerate := NF.nondegenerate_Qp v hQ'
  have h2 : (2 : v.adicCompletionIntegers F) ≠ 0 := NF.two_ne_zero' v
  have h4 : (4 : v.adicCompletionIntegers F) ≠ 0 := by
    rw [show (4 : v.adicCompletionIntegers F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  -- a diagonalization of `T`
  obtain ⟨P, dg, hPdet, hdg, hP⟩ := lid_exists_diag_local v T₀ hT
  choose fi hfi hfi' using fun i => DVR.exists_pow_dvd_not_dvd (NF.π v) hπ (mul_ne_zero h4 (hdg i))
  set f := Finset.univ.sup fi with hfdef
  have hf : ∀ i, ¬ NF.π v ^ (f + 1) ∣ 4 * dg i := fun i h =>
    hfi' i ((pow_dvd_pow _ (by have := Finset.le_sup (f := fi) (Finset.mem_univ i); omega)).trans h)
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hTo
  obtain ⟨d', he, he'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hQ'o
  obtain ⟨hdD, hdD'⟩ := det_blockForm_exact hπ (NF.Qp v T₀) (NF.Qp v Q₀') hd hd' he he'
  rw [← hQbl] at hdD hdD'
  -- the data of the local types
  choose x g hx hloc hgx using fun t : LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F))
    (Q₀'.map (algebraMap (𝓞 F) F)) => exists_frameType_data v T₀ Q₀' (locFrameRep v _ _ t)
  have hdisjAll : ∀ s, r * f + 1 ≤ s → ∀ t t', ∀ a ∈ gOrbit (frameRepK v T₀ Q₀') ⊤ (x t),
      ∀ a' ∈ gOrbit (frameRepK v T₀ Q₀') ⊤ (x t'), (∀ i, NF.π v ^ s ∣ a i - a' i) → t = t' := by
    intro s hs t t' a ha a' ha' haa'
    have := lid_disj v T₀ Q₀' hT hQ' hPdet hP hdg hf hs _ _ (x t) (x t') (hx t) (hx t') (g t) (g t')
      (hloc t) (hloc t') (hgx t) (hgx t') a a' ha ha' haa'
    rw [locFrameRep_mk, locFrameRep_mk] at this
    exact this
  have hfinT : Finite (LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))) := by
    have := DVR.finite_vec (ι := Fin (r + n') × Fin r) (NF.π v) hπ (r * f + 1)
    refine Finite.of_injective (fun t => DVR.redI (NF.π v) (r * f + 1) (x t)) fun t t' htt => ?_
    refine hdisjAll (r * f + 1) le_rfl t t' (x t) ⟨1, Subgroup.mem_top 1, by simp [frameRepK]⟩ (x t')
      ⟨1, Subgroup.mem_top 1, by simp [frameRepK]⟩ ((DVR.redI_eq_iff _ _ _ _).mp htt)
  let _ : Fintype (LocFrameTypes v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F))) :=
    Fintype.ofFinite _
  -- the radii
  choose s₀ k₀ hnear using fun t => frameNear_type v T₀ Q₀' hT hQ' (g t) (x t) (hx t) (hgx t)
  obtain ⟨s, hs1, hs2⟩ : ∃ s, r * f + 1 ≤ s ∧ ∀ t, s₀ t ≤ s :=
    ⟨max (r * f + 1) (Finset.univ.sup s₀), le_max_left _ _, fun t =>
      (Finset.le_sup (f := s₀) (Finset.mem_univ t)).trans (le_max_right _ _)⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k, s + 4 * (d + d') + 2 * d + 2 * d' + 1 ≤ k ∧ ∀ t, s + k₀ t ≤ k :=
    ⟨s + Finset.univ.sup k₀ + 4 * (d + d') + 2 * d + 2 * d' + 1, by omega, fun t => by
      have := Finset.le_sup (f := k₀) (Finset.mem_univ t); omega⟩
  -- the level set is the union of the near sets
  have hhensel : ∀ z : Fin (r + n') × Fin r → v.adicCompletionIntegers F,
      (∀ p, NF.π v ^ k ∣ formF (NF.Qp v (blockForm T₀ Q₀')) z p - tc (NF.Qp v T₀) p) →
      ∃ y, formF (NF.Qp v (blockForm T₀ Q₀')) y = tc (NF.Qp v T₀) ∧ ∀ i, NF.π v ^ (k - d) ∣ y i - z i :=
    fun z hz => exists_formF_eq_of_dvd hπ (NF.Qp v (blockForm T₀ Q₀')) (NF.Qp v T₀) hd hd' (by omega) z hz
  have hpart := card_sol_eq_sum_gNear hπ (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀))
    (fun t => gOrbit (frameRepK v T₀ Q₀') ⊤ (x t)) (lid_cover v T₀ Q₀' hT hQ' x g hloc hgx)
    (hdisjAll s hs1) (k := k) (e := d) (by omega) hhensel
  have hrepN : DVR.repCountForm (NF.Qp v (blockForm T₀ Q₀')) (NF.Qp v T₀) (NF.π v) k =
      ∑ t, gNear (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀)) (NF.π v) k s
        (gOrbit (frameRepK v T₀ Q₀') ⊤ (x t)) := by
    rw [DVR.repCountForm_eq_card_sol]; exact hpart
  have hpt : ∀ t, framePt v T₀ Q₀' (g t) (x t) (hgx t) = locFrameRep v _ _ t := fun t => Subtype.ext (hloc t)
  have hper : ∀ t, (gNear (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀)) (NF.π v) k s
        (gOrbit (frameRepK v T₀ Q₀') ⊤ (x t)) : ℝ) =
      locFrameWeight v _ _ (locFrameRep v _ _ t) *
        (gNear (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀)) (NF.π v) k s
          (gOrbit (frameRepK v T₀ Q₀') ⊤ stdFrame) : ℝ) := by
    intro t
    have := hnear t s k (hs2 t) (hk2 t)
    rwa [hpt t] at this
  have hA : (DVR.repCountForm (NF.Qp v (blockForm T₀ Q₀')) (NF.Qp v T₀) (NF.π v) k : ℝ) =
      locFrameTypeSum v (T₀.map (algebraMap (𝓞 F) F)) (Q₀'.map (algebraMap (𝓞 F) F)) *
        (gNear (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀)) (NF.π v) k s
          (gOrbit (frameRepK v T₀ Q₀') ⊤ stdFrame) : ℝ) := by
    rw [hrepN, Nat.cast_sum, Finset.sum_congr rfl (fun t _ => hper t), ← Finset.sum_mul, locFrameTypeSum,
      finsum_eq_sum_of_fintype]
  -- the orbit of the standard frame
  have hE := frameNear_stdFrame hπ (NF.Qp v T₀) (NF.Qp v Q₀') hd hd' he he' hPdet hP hdg hf (s := s) (k := k)
    hs1 (by omega)
  rw [← hQbl, ← lid_gOrbit_eq v T₀ Q₀' hT hQ' stdFrame] at hE
  have hEr : (gNear (formF (NF.Qp v (blockForm T₀ Q₀'))) (tc (NF.Qp v T₀)) (NF.π v) k s
          (gOrbit (frameRepK v T₀ Q₀') ⊤ stdFrame) : ℝ) *
        ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (d * n') * (Nat.card (orthMod (NF.Qp v Q₀') (NF.π v) k) : ℝ)) =
      (Nat.card (orthMod (NF.Qp v (blockForm T₀ Q₀')) (NF.π v) k) : ℝ) := by
    exact_mod_cast hE
  -- the densities
  have hβ1 : NF.localDensityForm v (blockForm T₀ Q₀') T₀ =
      (DVR.repCountForm (NF.Qp v (blockForm T₀ Q₀')) (NF.Qp v T₀) (NF.π v) k : ℝ) /
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * ((r + n') * r - r * (r + 1) / 2)) := by
    rw [NF.localDensityForm_eq_completion]
    exact DVR.localDensityForm_eq _ _ _ hπ d hd hd' (by omega) k (by omega)
  have hβ2 : NF.localDensityForm v (blockForm T₀ Q₀') (blockForm T₀ Q₀') =
      (Nat.card (orthMod (NF.Qp v (blockForm T₀ Q₀')) (NF.π v) k) : ℝ) /
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * ((r + n') * (r + n' - 1) / 2)) := by
    rw [NF.localDensityForm_eq_completion]
    exact DVR.localDensityForm_self_eq_card _ _ hπ (d + d') hdD hdD' k (by omega)
  have hβ3 : NF.localDensityForm v Q₀' Q₀' =
      (Nat.card (orthMod (NF.Qp v Q₀') (NF.π v) k) : ℝ) /
        (DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (k * (n' * (n' - 1) / 2)) := by
    rw [NF.localDensityForm_eq_completion]
    exact DVR.localDensityForm_self_eq_card _ _ hπ d' he he' k (by omega)
  have hnorm : ‖algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F T₀.hessian.det)‖ =
      ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ d)⁻¹ := by
    have := lid_norm_coe_of_pow_dvd v (x := (NF.Qp v T₀).hessian.det) hd hd'
    rw [NF.det_hessian_Qp] at this
    exact this
  have hq : (0 : ℝ) < (DVR.q (v.adicCompletionIntegers F) : ℝ) := by exact_mod_cast DVR.q_pos
  rw [hβ1, hβ2, hβ3, hnorm, hA, lid_tri r n', ← hEr]
  rw [mul_add, pow_add, inv_pow, ← pow_mul]
  field_simp

end Main

end QuadFormsKB.Tamagawa.Frames
