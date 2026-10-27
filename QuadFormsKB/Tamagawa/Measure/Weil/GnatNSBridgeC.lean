import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSBridgeR
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchSplitC
import QuadFormsKB.Tamagawa.Measure.Weil.NSArchTestSets
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSPlaces

/-!
# The bridge at a complex place of $F$: the global archimedean map of the non-square model versus `phiSplitC`


**Layer.** `nsC v g` $=\varphi(\Theta^{-1}g_1)_v$ (`GnatNSMaps`) is the matrix of $\varphi_x$, $x=(\Theta^{-1}g_1)_v\in D_E\otimes F_v$,
$F_v=\mathbb C$. Complex analogue of `GnatNSBridgeR`.

**Step 1 (forms).** The quadratic forms of the non-square and square models at a complex place are `nsFormC` and `normForm`
(`QCx_qNS`, `QCx_qSq`).

**Step 2 (global).** For the two places $w_1\ne w_2$ of $K$ over the complex place $v$ of $F$, the coordinates of
$m=g_1\in(D'\otimes\mathbb A_K)^\times$ at $w_i$ are $\psi_{\pm t}(x)$ (`psi`) or the complex conjugate of that, according to whether
$w_i\circ\mathrm{alg}$ is $\sigma_v$ or $\bar\sigma_v$ (`twC`). Hence `nsC v g` is $\operatorname{nrd}^{-1}$ times
$T^{-1}\,\mathrm{sq}(X_1,\overline{X_2})\,T$ (`mat_nsC_cx`), and for $c^2=g_{2,v}$ it is `phiSplitC` of the normalized sphere
points (`mat_nsC_eq_phiSplitC`).

**Step 3 (conjugation).** Coordinatewise complex conjugation $S_1(\bar A,\bar B)\to S_1(A,B)$ is a homeomorphism that preserves the
Leray measure and carries `posC` onto `posC` (`conjSph`, `conjSph_measurePreserving`, `sigC_posC_conj`).
-/

open Matrix Quaternion NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Measure Set
open scoped Quaternion ComplexConjugate ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Quat.Gnat

/-! ### Step 1: the specialization homomorphism over $\mathbb C$ -/

section PsiId

variable {A B D t : ℂ}

/-- $\psi_t : D_E\to\mathbb H[\mathbb C,A,B]$, $r+s\delta\mapsto r+ts$ ($t^2=D$), for $D_E$ over $\mathbb C$. -/
def psiId (t : ℂ) (ht : t ^ 2 = D) : DE A B D →+* ℍ[ℂ, A, B] := psi (RingHom.id ℂ) t ht rfl rfl

theorem psiId_re (ht : t ^ 2 = D) (x : DE A B D) : (psiId t ht x).re = x.re.re + t * x.re.im := rfl
theorem psiId_imI (ht : t ^ 2 = D) (x : DE A B D) : (psiId t ht x).imI = x.imI.re + t * x.imI.im := rfl
theorem psiId_imJ (ht : t ^ 2 = D) (x : DE A B D) : (psiId t ht x).imJ = x.imJ.re + t * x.imJ.im := rfl
theorem psiId_imK (ht : t ^ 2 = D) (x : DE A B D) : (psiId t ht x).imK = x.imK.re + t * x.imK.im := rfl

theorem neg_sq_C (ht : t ^ 2 = D) : (-t) ^ 2 = D := (neg_sq t).trans ht

theorem psiId_star (ht : t ^ 2 = D) (x : DE A B D) : psiId t ht (star x) = star (psiId t ht x) :=
  psi_star _ _ _ _ _ x

theorem psiId_sig (ht : t ^ 2 = D) (y : DE A B D) : psiId t ht (sig y) = psiId (-t) (neg_sq_C ht) y :=
  psi_sig _ _ _ (neg_sq_C ht) _ _ y

theorem psiId_emb (ht : t ^ 2 = D) (v : Fin 4 → ℂ) :
    psiId t ht (emb v : DE A B D) = vecQ (NSArch.tMatC t *ᵥ v) := by
  rw [NSArch.tMatC_mulVec]
  ext <;> simp [psiId_re, psiId_imI, psiId_imJ, psiId_imK, emb, vecQ]

theorem coords_eq_psiId (ht0 : t ≠ 0) (ht : t ^ 2 = D) {y : DE A B D} (hy : InV0 y) :
    coords y = NSArch.tInvC t *ᵥ qVec (psiId t ht y) := by
  have e := emb_coords (two_ne_zero (α := ℂ)) hy
  conv_rhs => rw [← e]
  rw [psiId_emb, qVec_vecQ, Matrix.mulVec_mulVec, NSArch.tInvC_mul_tMatC ht0, Matrix.one_mulVec]

/-- **Key identity ($E_w=\mathbb C\times\mathbb C$).**
$\varphi_x=\operatorname{nrd}(x)^{-1}\,T^{-1}\,\mathrm{sq}(\psi_t x,\overline{\psi_{-t}x})\,T$ as matrices. -/
theorem toMatrix'_phiLin_C (ht0 : t ≠ 0) (ht : t ^ 2 = D) (x : DE A B D) :
    LinearMap.toMatrix' (phiLin x) =
      (nrdK x)⁻¹ • (NSArch.tInvC t * sqMat (psiId t ht x) (star (psiId (-t) (neg_sq_C ht) x)) * NSArch.tMatC t) := by
  have key : ∀ v : Fin 4 → ℂ, phiLin x v = ((nrdK x)⁻¹ • (NSArch.tInvC t *
      sqMat (psiId t ht x) (star (psiId (-t) (neg_sq_C ht) x)) * NSArch.tMatC t)) *ᵥ v := by
    intro v
    rw [phiLin_apply, coords_eq_psiId ht0 ht (inV0_conj x _ (inV0_emb v)), map_mul, map_mul, psiId_emb,
      psiId_sig, psiId_star, Matrix.smul_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, sqMat_mulVec]
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [LinearMap.toMatrix'_mulVec, key]

end PsiId

/-! ### The forms -/

section Forms

variable {F : Type} [Field F] [NumberField F]

/-- $Q_{\mathrm{ns}}(a,b,d)^{\tau_v}=\langle1,-a_vd_v,-b_vd_v,a_vb_vd_v\rangle$ = `NSArch.nsFormC` at a complex place. -/
theorem QCx_qNS (a b d : 𝓞 F) (v : {v : InfinitePlace F // v.IsComplex}) :
    QCx (qNS a b d) v = NSArch.nsFormC (v.1.embedding (a : F)) (v.1.embedding (b : F)) (v.1.embedding (d : F)) := by
  rw [NSArch.nsFormC_eq_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qNS, QuadForm.diag, QuadForm.map]

/-- $Q_{\mathrm{sq}}(\alpha,\beta)^{\tau_w}=\langle1,-\alpha_w,-\beta_w,\alpha_w\beta_w\rangle$ = `NSArch.normForm`. -/
theorem QCx_qSq (α β : 𝓞 F) (w : {w : InfinitePlace F // w.IsComplex}) :
    QCx (qSq α β) w = NSArch.normForm (w.1.embedding (α : F)) (w.1.embedding (β : F)) := by
  rw [NSArch.normForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qSq, QuadForm.diag, QuadForm.map]

end Forms

/-! ### Conjugation of the complex sphere $S_1(\bar A,\bar B)\to S_1(A,B)$ -/

section Conj

open QuadFormsKB.Tamagawa.Measure.SphereLerayC

variable (A B : ℂ)

/-- Coordinatewise complex conjugation of vectors in $\mathbb C^4$. -/
def conjV (x : Fin 4 → ℂ) : Fin 4 → ℂ := fun i => conj (x i)

theorem conjV_conjV (x : Fin 4 → ℂ) : conjV (conjV x) = x := by
  funext i; simp [conjV]

theorem conjV_smul (r : ℂ) (x : Fin 4 → ℂ) : conjV (r • x) = conj r • conjV x := by
  funext i; simp [conjV]

theorem eval_normForm_conjV (x : Fin 4 → ℂ) :
    (NSArch.normForm A B).eval (conjV x) = conj ((NSArch.normForm (conj A) (conj B)).eval x) := by
  rw [NSArch.eval_normForm, NSArch.eval_normForm]
  simp [nrd, vecQ, conjV]

theorem continuous_conjV : Continuous conjV :=
  continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

/-- **Conjugation of the sphere**: $x\mapsto\bar x$ coordinatewise, $S_1(\bar A,\bar B)\to S_1(A,B)$. -/
def conjSph (x : SphC (NSArch.normForm (conj A) (conj B)) 1) : SphC (NSArch.normForm A B) 1 :=
  ⟨conjV (x : Fin 4 → ℂ), by
    show (NSArch.normForm A B).eval _ = 1
    rw [eval_normForm_conjV, x.2, map_one]⟩

theorem conjSph_val (x : SphC (NSArch.normForm (conj A) (conj B)) 1) :
    ((conjSph A B x : SphC (NSArch.normForm A B) 1) : Fin 4 → ℂ) = conjV (x : Fin 4 → ℂ) := rfl

theorem continuous_conjSph : Continuous (conjSph A B) :=
  (continuous_conjV.comp continuous_subtype_val).subtype_mk _

/-- The inverse of `conjSph`: $S_1(A,B)\to S_1(\bar A,\bar B)$. -/
def conjSph' (x : SphC (NSArch.normForm A B) 1) : SphC (NSArch.normForm (conj A) (conj B)) 1 :=
  ⟨conjV (x : Fin 4 → ℂ), by
    show (NSArch.normForm (conj A) (conj B)).eval _ = 1
    have h := eval_normForm_conjV (conj A) (conj B) (x : Fin 4 → ℂ)
    simp only [Complex.conj_conj] at h
    rw [h, x.2, map_one]⟩

theorem continuous_conjSph' : Continuous (conjSph' A B) :=
  (continuous_conjV.comp continuous_subtype_val).subtype_mk _

/-- `conjSph` is a homeomorphism. -/
def conjSphHomeo : SphC (NSArch.normForm (conj A) (conj B)) 1 ≃ₜ SphC (NSArch.normForm A B) 1 where
  toFun := conjSph A B
  invFun := conjSph' A B
  left_inv _ := Subtype.ext (conjV_conjV _)
  right_inv _ := Subtype.ext (conjV_conjV _)
  continuous_toFun := continuous_conjSph A B
  continuous_invFun := continuous_conjSph' A B

/-- `conjV` as a homeomorphism. -/
def conjVHomeo : (Fin 4 → ℂ) ≃ₜ (Fin 4 → ℂ) where
  toFun := conjV
  invFun := conjV
  left_inv := conjV_conjV
  right_inv := conjV_conjV
  continuous_toFun := continuous_conjV
  continuous_invFun := continuous_conjV

theorem conjV_measurePreserving : MeasurePreserving conjV (volume : Measure (Fin 4 → ℂ)) volume :=
  volume_preserving_pi (fun _ => Complex.conjLIE.measurePreserving)

/-- $\bar{\ }$ on $\mathbb C^\times$. -/
def conjU (β : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ).toMonoidHom β

theorem conjU_val (β : ℂˣ) : ((conjU β : ℂˣ) : ℂ) = conj (β : ℂ) := rfl

theorem conjU_conjU (β : ℂˣ) : conjU (conjU β) = β := Units.ext (by simp [conjU_val])

theorem conjU_mem_R0 {β : ℂˣ} (h : β ∈ R0) : conjU β ∈ R0 := by
  refine ⟨?_, ?_⟩
  · rw [conjU_val, Complex.conj_re]; exact h.1
  · rw [conjU_val, Complex.norm_conj]; exact h.2

theorem conjV_polC (β : ℂˣ) (x : SphC (NSArch.normForm (conj A) (conj B)) 1) :
    conjV (polC (NSArch.normForm (conj A) (conj B)) 1 (β, x)) =
      polC (NSArch.normForm A B) 1 (conjU β, conjSph A B x) :=
  by simp only [polC, conjSph_val, conjU_val]; exact conjV_smul (β : ℂ) (x : Fin 4 → ℂ)

theorem conjV_polC' (β : ℂˣ) (x : SphC (NSArch.normForm A B) 1) :
    conjV (polC (NSArch.normForm A B) 1 (β, x)) =
      polC (NSArch.normForm (conj A) (conj B)) 1 (conjU β, conjSph' A B x) :=
  by simp only [polC, conjSph', conjU_val]; exact conjV_smul (β : ℂ) (x : Fin 4 → ℂ)

theorem conjSph_preimage_polC (S : Set (SphC (NSArch.normForm A B) 1)) :
    polC (NSArch.normForm (conj A) (conj B)) 1 '' (R0 ×ˢ (conjSph A B ⁻¹' S)) =
      conjV ⁻¹' (polC (NSArch.normForm A B) 1 '' (R0 ×ˢ S)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨⟨β, x⟩, hbx, hy⟩
    have hx2 : conjSph A B x ∈ S := Set.mem_preimage.1 (Set.mem_prod.1 hbx).2
    have hmem : (conjU β, conjSph A B x) ∈ R0 ×ˢ S := Set.mem_prod.2 ⟨conjU_mem_R0 (Set.mem_prod.1 hbx).1, hx2⟩
    refine Set.mem_preimage.2 ⟨(conjU β, conjSph A B x), hmem, ?_⟩
    have h1 := conjV_polC A B β x
    rw [hy] at h1
    exact h1.symm
  · intro y hy
    obtain ⟨⟨β, x⟩, hbx, hy⟩ := Set.mem_preimage.1 hy
    have hx' : conjSph A B (conjSph' A B x) = x := Subtype.ext (conjV_conjV _)
    have hx2 : conjSph A B (conjSph' A B x) ∈ S := by
      rw [hx']; exact (Set.mem_prod.1 hbx).2
    have hmem : (conjU β, conjSph' A B x) ∈ R0 ×ˢ (conjSph A B ⁻¹' S) :=
      Set.mem_prod.2 ⟨conjU_mem_R0 (Set.mem_prod.1 hbx).1, Set.mem_preimage.2 hx2⟩
    refine ⟨(conjU β, conjSph' A B x), hmem, ?_⟩
    have h1 := conjV_polC' A B β x
    have h2 : conjV (polC (NSArch.normForm A B) 1 (β, x)) = conjV (conjV y) := congrArg conjV hy
    rw [conjV_conjV] at h2
    exact h1.symm.trans h2

theorem nuC_conjSph_preimage {S : Set (SphC (NSArch.normForm A B) 1)} (hS : MeasurableSet S) :
    nuC (NSArch.normForm (conj A) (conj B)) 1 (conjSph A B ⁻¹' S) = nuC (NSArch.normForm A B) 1 S := by
  have hm := (continuous_conjSph A B).measurable
  rw [nuC_apply_volume one_ne_zero (hm hS), nuC_apply_volume one_ne_zero hS, conjSph_preimage_polC]
  congr 1
  exact conjV_measurePreserving.measure_preimage_emb conjVHomeo.measurableEmbedding _

theorem sigC_conjSph_preimage {S : Set (SphC (NSArch.normForm A B) 1)} (hS : MeasurableSet S) :
    sigC (NSArch.normForm (conj A) (conj B)) 1 (conjSph A B ⁻¹' S) = sigC (NSArch.normForm A B) 1 S := by
  rw [sigC, sigC, Measure.smul_apply, Measure.smul_apply, nuC_conjSph_preimage A B hS]

/-- **Conjugation preserves the Leray measure of the sphere:** $S_1(\bar A,\bar B)\to S_1(A,B)$, $x\mapsto\bar x$. -/
theorem conjSph_measurePreserving :
    MeasurePreserving (conjSph A B) (sigC (NSArch.normForm (conj A) (conj B)) 1) (sigC (NSArch.normForm A B) 1) :=
  ⟨(continuous_conjSph A B).measurable, Measure.ext fun S hS => by
    rw [Measure.map_apply (continuous_conjSph A B).measurable hS, sigC_conjSph_preimage A B hS]⟩

theorem norm_conjV (x : Fin 4 → ℂ) : ‖conjV x‖ = ‖x‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · rw [conjV, Complex.norm_conj]; exact norm_le_pi_norm x i
  · have := norm_le_pi_norm (conjV x) i
    rwa [conjV, Complex.norm_conj] at this

theorem conjSph_preimage_posC :
    conjSph A B ⁻¹' NSArch.posC A B = NSArch.posC (conj A) (conj B) := by
  ext x
  show (0 < ((conjV (x : Fin 4 → ℂ)) 0).re ∧ ‖conjV (x : Fin 4 → ℂ)‖ < 2) ↔ _
  rw [norm_conjV]
  simp [conjV, NSArch.posC]

/-- Conjugation maps `posC (conj A) (conj B)` onto `posC A B`. -/
theorem conjSph_image_posC : conjSph A B '' NSArch.posC (conj A) (conj B) = NSArch.posC A B := by
  rw [← conjSph_preimage_posC A B]
  exact Set.image_preimage_eq _ (conjSphHomeo A B).surjective

/-- **The Leray measure of the test set is conjugation invariant.** -/
theorem sigC_posC_conj :
    sigC (NSArch.normForm (conj A) (conj B)) 1 (NSArch.posC (conj A) (conj B)) =
      sigC (NSArch.normForm A B) 1 (NSArch.posC A B) := by
  rw [← conjSph_preimage_posC A B]
  exact sigC_conjSph_preimage A B NSArch.measurableSet_posC

end Conj

/-! ### Step 2a: orientation of a complex place of $K$ over a complex place of $F$ -/

section Twist

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- **Same orientation:** the embedding $w:K\to\mathbb C$ restricts to the embedding of $F$ chosen for $w|_F$
(rather than to its complex conjugate). -/
def SameOr (F : Type) [Field F] [Algebra F K] (w : {w : InfinitePlace K // w.IsComplex}) : Prop :=
  w.1.embedding.comp (algebraMap F K) = (w.1.comap (algebraMap F K)).embedding

open Classical in
/-- **The twist** at $w$: the identity if $w$ has the same orientation as $w|_F$, coordinatewise complex conjugation otherwise. -/
def twC (F : Type) [Field F] [Algebra F K] (w : {w : InfinitePlace K // w.IsComplex}) (y : Fin 4 → ℂ) :
    Fin 4 → ℂ :=
  if SameOr F w then y else conjV y

open Classical in
/-- **The embedding of $K$ extending the chosen embedding of $F$ at $w|_F$ that $w$ represents:**
$w$ itself if the orientation is the same, $\bar w$ otherwise. -/
def extEmb (_bK : Module.Basis (Fin 2) F K) (w : {w : InfinitePlace K // w.IsComplex}) : K →+* ℂ :=
  if SameOr F w then w.1.embedding else (starRingEnd ℂ).comp w.1.embedding

/-- **The value of $\delta$** under `extEmb`: $w(\delta)$ if the orientation is the same, $\overline{w(\delta)}$ otherwise. -/
def twt (bK : Module.Basis (Fin 2) F K) (w : {w : InfinitePlace K // w.IsComplex}) : ℂ := extEmb bK w (bK 1)

open Classical in
theorem twt_eq_ite (bK : Module.Basis (Fin 2) F K) (w : {w : InfinitePlace K // w.IsComplex}) :
    twt bK w = if SameOr F w then w.1.embedding (bK 1) else conj (w.1.embedding (bK 1)) := by
  unfold twt extEmb
  split_ifs <;> rfl

theorem extEmb_comp (bK : Module.Basis (Fin 2) F K) (w : {w : InfinitePlace K // w.IsComplex})
    (hv : (w.1.comap (algebraMap F K)).IsComplex) :
    (extEmb bK w).comp (algebraMap F K) = (w.1.comap (algebraMap F K)).embedding := by
  unfold extEmb
  split_ifs with h
  · exact h
  · rcases (embedding_comp_eq_or_conj w.1 hv).1 with h' | h'
    · exact absurd h' h
    · ext x
      have := congrArg (fun f : F →+* ℂ => f x) h'
      simp only [RingHom.comp_apply] at this ⊢
      rw [this]; exact Complex.conj_conj _

theorem mk_extEmb (bK : Module.Basis (Fin 2) F K) (w : {w : InfinitePlace K // w.IsComplex}) :
    InfinitePlace.mk (extEmb bK w) = w.1 := by
  unfold extEmb
  split_ifs
  · exact InfinitePlace.mk_embedding w.1
  · exact (InfinitePlace.mk_conjugate_eq w.1.embedding).trans (InfinitePlace.mk_embedding w.1)

variable {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {d : F} (hb₁ : bK 1 * bK 1 = algebraMap F K d)

include hb₁ in
/-- $t^2=d_v$ for $t=\delta$ as seen by `extEmb`. -/
theorem twt_sq (v : {v : InfinitePlace F // v.IsComplex}) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) : twt bK w ^ 2 = v.1.embedding d := by
  have hv : (w.1.comap (algebraMap F K)).IsComplex := hw ▸ v.2
  have h := congrArg (fun f : F →+* ℂ => f d) (extEmb_comp bK w hv)
  simp only [RingHom.comp_apply, hw] at h
  rw [twt, sq_delta_emb bK hb₁, h]

include hb₁ in
theorem twt_ne_zero (hd0 : d ≠ 0) (v : {v : InfinitePlace F // v.IsComplex})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) : twt bK w ≠ 0 := by
  intro h0
  have h := twt_sq hb₁ v w hw
  rw [h0, zero_pow two_ne_zero] at h
  exact hd0 ((map_eq_zero _).1 h.symm)

include hb₀ hb₁ in
/-- **The two places over $v$ have opposite values of $\delta$:** $t_{w_2}=-t_{w_1}$. -/
theorem twt_neg (v : {v : InfinitePlace F // v.IsComplex}) (w₁ w₂ : {w : InfinitePlace K // w.IsComplex})
    (h₁ : w₁.1.comap (algebraMap F K) = v.1) (h₂ : w₂.1.comap (algebraMap F K) = v.1) (hne : w₁ ≠ w₂) :
    twt bK w₂ = - twt bK w₁ := by
  have hv₁ : (w₁.1.comap (algebraMap F K)).IsComplex := h₁ ▸ v.2
  have hv₂ : (w₂.1.comap (algebraMap F K)).IsComplex := h₂ ▸ v.2
  have c1 := extEmb_comp bK w₁ hv₁
  have c2 := extEmb_comp bK w₂ hv₂
  rw [h₁] at c1
  rw [h₂] at c2
  rcases eq_or_comp_deltaConj bK hb₀ hb₁ (extEmb bK w₂) (extEmb bK w₁)
      (fun x => congrArg (fun f : F →+* ℂ => f x) (c2.trans c1.symm)) with h | h
  · exfalso
    apply hne
    have := mk_extEmb bK w₂
    rw [h, mk_extEmb bK w₁] at this
    exact Subtype.ext this
  · rw [twt, twt, h, comp_deltaConj_delta bK hb₀ hb₁]

end Twist

/-! ### Step 2b: the global map at a complex place -/

section Global

open IsDedekindDomain QuadFormsKB.Tamagawa.ArchSOMeasure QuadFormsKB.Tamagawa.Measure.LerayReal
  QuadFormsKB.Tamagawa.Measure.LerayComplex

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  {bK : Module.Basis (Fin 2) F K} (hb₀ : bK 0 = 1) {a b d : 𝓞 F}
  (hb₁ : bK 1 * bK 1 = algebraMap F K (d : F))
  {A' B' : K} (hA' : A' = algebraMap F K (a : F)) (hB' : B' = algebraMap F K (b : F))
  (hA0 : A' ≠ 0) (hB0 : B' ≠ 0)

open Classical in
/-- Components of `adeleMap F K t` at a complex place $w$ of $K$ over a complex place $v$ of $F$:
$t_v$ if $w$ has the same orientation as $v$, $\overline{t_v}$ otherwise. -/
theorem fAtC_adeleMap_cc (t : Adeles F) (v : {v : InfinitePlace F // v.IsComplex})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    (if SameOr F w then fAtC w (adeleMap F K t) else conj (fAtC w (adeleMap F K t))) = fAtC v t := by
  have hv : (w.1.comap (algebraMap F K)).IsComplex := hw ▸ v.2
  have hsub : (⟨w.1.comap (algebraMap F K), hv⟩ : {v : InfinitePlace F // v.IsComplex}) = v := Subtype.ext hw
  split_ifs with h
  · rw [fAtC_apply, adeleMap_fst_snd_of_comp_eq t w hv h, hsub]; rfl
  · rcases (embedding_comp_eq_or_conj w.1 hv).1 with h' | h'
    · exact absurd h' h
    · rw [fAtC_apply, adeleMap_fst_snd_of_comp_eq_conj t w hv h', hsub, Complex.conj_conj]; rfl

open Classical in
/-- **The twisted coordinate of $\Theta z$ at $w$:** $z_v+\delta_w z'_v$ with $\delta_w$ = `twt`. -/
theorem twist_quadBaseChange (z : QuadAdele F (d : F)) (v : {v : InfinitePlace F // v.IsComplex})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    (if SameOr F w then fAtC w (quadBaseChange hb₀ hb₁ z) else conj (fAtC w (quadBaseChange hb₀ hb₁ z))) =
      fAtC v z.re + twt bK w * fAtC v z.im := by
  have e1 := fAtC_adeleMap_cc z.re v w hw
  have e2 := fAtC_adeleMap_cc z.im v w hw
  rw [quadBaseChange_apply, map_add, map_mul, fAtC_diag, twt_eq_ite]
  by_cases h : SameOr F w
  · simp only [h, ↓reduceIte] at e1 e2 ⊢
    rw [e1, e2]
  · simp only [h, ↓reduceIte] at e1 e2 ⊢
    rw [map_add, map_mul, e1, e2]

open Classical in
/-- **Coordinates at a complex place $w$ of $K$ over the complex place $v$ of $F$:** the (twisted) coordinates of $m$ at $w$
are $z_v+\delta\,z'_v$ for the components $z+z'\delta$ of $\Theta^{-1}m$. -/
theorem coord_cc (m : QuatAdele (F := K) A' B') (v : {v : InfinitePlace F // v.IsComplex})
    (w : {w : InfinitePlace K // w.IsComplex}) (hw : w.1.comap (algebraMap F K) = v.1) :
    (if SameOr F w then m.re.1.2 w else conj (m.re.1.2 w)) =
        fAtC v (bcRing hb₀ hb₁ hA' hB' m).re.re + twt bK w * fAtC v (bcRing hb₀ hb₁ hA' hB' m).re.im ∧
    (if SameOr F w then m.imI.1.2 w else conj (m.imI.1.2 w)) =
        fAtC v (bcRing hb₀ hb₁ hA' hB' m).imI.re + twt bK w * fAtC v (bcRing hb₀ hb₁ hA' hB' m).imI.im ∧
    (if SameOr F w then m.imJ.1.2 w else conj (m.imJ.1.2 w)) =
        fAtC v (bcRing hb₀ hb₁ hA' hB' m).imJ.re + twt bK w * fAtC v (bcRing hb₀ hb₁ hA' hB' m).imJ.im ∧
    (if SameOr F w then m.imK.1.2 w else conj (m.imK.1.2 w)) =
        fAtC v (bcRing hb₀ hb₁ hA' hB' m).imK.re + twt bK w * fAtC v (bcRing hb₀ hb₁ hA' hB' m).imK.im := by
  obtain ⟨h1, h2, h3, h4⟩ := quadBaseChange_bcRing hb₀ hb₁ hA' hB' m
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := twist_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).re v w hw
    rwa [h1] at this
  · have := twist_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imI v w hw
    rwa [h2] at this
  · have := twist_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imJ v w hw
    rwa [h3] at this
  · have := twist_quadBaseChange hb₀ hb₁ (bcRing hb₀ hb₁ hA' hB' m).imK v w hw
    rwa [h4] at this

/-- **The transported element at a complex place of $F$:** $x=(\Theta^{-1}g_1)_v\in D_E\otimes F_v$. -/
def nsXC (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) : DEcx a b d v :=
  (((nsPairC hb₀ hb₁ hA' hB' hA0 hB0 v g : Gnat _ _ _) : (DEcx a b d v)ˣ) : DEcx a b d v)

/-- **Complex places $w$ over $v$:** $\psi_{s}(x)$ has the twisted coordinates of $g_1$ at $w$ (`unitAtC`), where
$x=(\Theta^{-1}g_1)_v$, $s$ = `twt` and $\psi_s$ is `psiId`. -/
theorem qVec_psiId_nsXC (v : {v : InfinitePlace F // v.IsComplex}) (w : {w : InfinitePlace K // w.IsComplex})
    (hw : w.1.comap (algebraMap F K) = v.1) {s : ℂ} (hs : twt bK w = s)
    (ht : s ^ 2 = v.1.embedding (d : F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    twC F w (qVec (mUnitC w (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) =
      qVec (psiId s ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)) := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := coord_cc hb₀ hb₁ hA' hB'
    (((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1 : (QuatAdele (F := K) A' B')ˣ) : QuatAdele (F := K) A' B')
    v w hw
  subst hs
  unfold twC
  by_cases hc : SameOr F w
  · simp only [hc, ↓reduceIte] at h1 h2 h3 h4 ⊢
    funext i
    fin_cases i
    · show (mUnitC w _).re = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).re
      rw [psiId_re, mUnitC, unitAtC_val]; exact h1
    · show (mUnitC w _).imI = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imI
      rw [psiId_imI, mUnitC, unitAtC_val]; exact h2
    · show (mUnitC w _).imJ = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imJ
      rw [psiId_imJ, mUnitC, unitAtC_val]; exact h3
    · show (mUnitC w _).imK = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imK
      rw [psiId_imK, mUnitC, unitAtC_val]; exact h4
  · simp only [hc, ↓reduceIte] at h1 h2 h3 h4 ⊢
    funext i
    fin_cases i
    · show conj (mUnitC w _).re = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).re
      rw [psiId_re, mUnitC, unitAtC_val]; exact h1
    · show conj (mUnitC w _).imI = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imI
      rw [psiId_imI, mUnitC, unitAtC_val]; exact h2
    · show conj (mUnitC w _).imJ = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imJ
      rw [psiId_imJ, mUnitC, unitAtC_val]; exact h3
    · show conj (mUnitC w _).imK = (psiId _ ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)).imK
      rw [psiId_imK, mUnitC, unitAtC_val]; exact h4

/-! #### The matrix of `nsC` -/

variable (ha0 : (a : F) ≠ 0) (hd0 : (d : F) ≠ 0)

/-- $\operatorname{nrd}_K(x)=g_{2,v}$ for $x=(\Theta^{-1}g_1)_v$. -/
theorem nrdK_nsXC (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nrdK (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g) =
      fAtC v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F) :=
  nrdK_deMap (fAtC v) (fAtC_diag v (d : F)) (fAtC_diag v (a : F)) (fAtC_diag v (b : F))
    (nsUnit_nrd hb₀ hb₁ hA' hB' hA0 hB0 g)

theorem nrdE_nsXC (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    nrdE (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g) =
      algebraMap ℂ (QE (v.1.embedding (d : F))) (nrdK (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)) :=
  nrdE_eq_nrdK (nsPairC hb₀ hb₁ hA' hB' hA0 hB0 v g).2

/-- `mat (nsC v g)` is the matrix of $\varphi_x$, $x=(\Theta^{-1}g_1)_v$. -/
theorem mat_nsC_eq_toMatrix (v : {v : InfinitePlace F // v.IsComplex}) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOC.mat _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
      LinearMap.toMatrix' (phiLin (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)) := by
  change ((nsGLC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = _
  rw [nsGLC_apply, coe_phiSO, nsXC]

/-- **A complex place $v$ of $F$: `nsC` in terms of the coordinates of $g_1$ at the two places of $K$ over $v$.**
With $t=\delta$ as seen by $w_1$ (`twt bK w₁`; $\delta$ is $-t$ for $w_2$), $r=g_{2,v}$, $X_i$ the $w_i$-coordinates of $g_1$
(`mUnitC`) twisted by `twC` (conjugated if $w_i$ and $w_i|_F$ have opposite orientation):
$\varphi_v(g)=r^{-1}\,T^{-1}\,(y\mapsto X_1\,y\,\overline{X_2})\,T$. -/
theorem mat_nsC_cx (v : {v : InfinitePlace F // v.IsComplex})
    (w₁ w₂ : {w : InfinitePlace K // w.IsComplex}) (h₁ : w₁.1.comap (algebraMap F K) = v.1)
    (h₂ : w₂.1.comap (algebraMap F K) = v.1) (hne : w₁ ≠ w₂) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) :
    ArchSOC.mat _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
      (fAtC v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F))⁻¹ •
        (NSArch.tInvC (twt bK w₁) *
          sqMat (vecQ (twC F w₁ (qVec (mUnitC w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1))) :
              ℍ[ℂ, v.1.embedding (a : F), v.1.embedding (b : F)])
            (star (vecQ (twC F w₂ (qVec (mUnitC w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)))  :
              ℍ[ℂ, v.1.embedding (a : F), v.1.embedding (b : F)])) *
          NSArch.tMatC (twt bK w₁)) := by
  have ht := twt_sq hb₁ v w₁ h₁
  have ht0 := twt_ne_zero hb₁ hd0 v w₁ h₁
  rw [qVec_psiId_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v w₁ h₁ rfl ht g,
    qVec_psiId_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v w₂ h₂ (twt_neg hb₀ hb₁ v w₁ w₂ h₁ h₂ hne) (neg_sq_C ht) g,
    vecQ_qVec, vecQ_qVec, mat_nsC_eq_toMatrix hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0, toMatrix'_phiLin_C ht0 ht,
    nrdK_nsXC hb₀ hb₁ hA' hB' hA0 hB0]

open SphereLerayC in
/-- **A complex place $v$ of $F$: `nsC` is `phiSplitC` of the normalized sphere points.** For $c^2=r=g_{2,v}$, $c\ne0$ (the case needed
downstream is $r=c=1$), the matrix of `nsC v g` equals that of `phiSplitC` at $(x_1,x_2)$,
$x_i=c^{-1}\,\mathrm{tw}_i(\mathrm{qVec}(X_i))$, $X_i$ the $w_i$-coordinates of $g_1$ (`mUnitC`, twisted by `twC`). -/
theorem mat_nsC_eq_phiSplitC (v : {v : InfinitePlace F // v.IsComplex})
    (w₁ w₂ : {w : InfinitePlace K // w.IsComplex}) (h₁ : w₁.1.comap (algebraMap F K) = v.1)
    (h₂ : w₂.1.comap (algebraMap F K) = v.1) (hne : w₁ ≠ w₂) {t : ℂ} (ht1 : twt bK w₁ = t) (ht0 : t ≠ 0)
    (ht : t ^ 2 = v.1.embedding (d : F)) (g : (gnatBC bK 0 hb₀ hA0 hB0).G) {c : ℂ}
    (hc : c ^ 2 = fAtC v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F)) (hc0 : c ≠ 0) :
    ∃ x₁ x₂ : SphC (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))) 1,
      (x₁ : Fin 4 → ℂ) = c⁻¹ • twC F w₁ (qVec (mUnitC w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) ∧
      (x₂ : Fin 4 → ℂ) = c⁻¹ • twC F w₂ (qVec (mUnitC w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) ∧
      ArchSOC.mat _ (nsC hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v g) =
        ArchSOC.mat _ (NSArch.phiSplitC ht0 ht (x₁, x₂)) := by
  set u := fAtC v ((g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).2 : Adeles F) with hu
  have ht2 : twt bK w₂ = -t := by rw [twt_neg hb₀ hb₁ v w₁ w₂ h₁ h₂ hne, ht1]
  have e1 := qVec_psiId_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v w₁ h₁ ht1 ht g
  have e2 := qVec_psiId_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v w₂ h₂ ht2 (neg_sq_C ht) g
  have hn1 : nrd (psiId t ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)) = u := by
    have := nrd_psi (RingHom.id ℂ) t ht rfl rfl (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g) _
      (nrdE_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)
    rw [nrdK_nsXC] at this
    exact this
  have hn2 : nrd (psiId (-t) (neg_sq_C ht) (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)) = u := by
    have := nrd_psi (RingHom.id ℂ) (-t) (neg_sq_C ht) rfl rfl (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g) _
      (nrdE_nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)
    rw [nrdK_nsXC] at this
    exact this
  have hsph : ∀ Y : ℍ[ℂ, v.1.embedding (a : F), v.1.embedding (b : F)], nrd Y = u →
      (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))).eval (c⁻¹ • qVec Y) = 1 := by
    intro Y hY
    rw [NSArch.eval_normForm_smulC, NSArch.eval_normForm_qVec, hY, ← hc, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hc0)]
  let x₁ : SphC (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))) 1 :=
    ⟨c⁻¹ • qVec (psiId t ht (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)), hsph _ hn1⟩
  let x₂ : SphC (NSArch.normForm (v.1.embedding (a : F)) (v.1.embedding (b : F))) 1 :=
    ⟨c⁻¹ • qVec (psiId (-t) (neg_sq_C ht) (nsXC hb₀ hb₁ hA' hB' hA0 hB0 v g)), hsph _ hn2⟩
  have hx₁ : (x₁ : Fin 4 → ℂ) =
      c⁻¹ • twC F w₁ (qVec (mUnitC w₁ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) :=
    congrArg (c⁻¹ • ·) e1.symm
  have hx₂ : (x₂ : Fin 4 → ℂ) =
      c⁻¹ • twC F w₂ (qVec (mUnitC w₂ (g : (QuatAdele (F := K) A' B')ˣ × (Adeles F)ˣ).1)) :=
    congrArg (c⁻¹ • ·) e2.symm
  refine ⟨x₁, x₂, hx₁, hx₂, ?_⟩
  have hcc : c⁻¹ * c⁻¹ = u⁻¹ := by rw [← mul_inv, ← sq, hc]
  have key := mat_nsC_cx hb₀ hb₁ hA' hB' hA0 hB0 ha0 hd0 v w₁ w₂ h₁ h₂ hne g
  rw [ht1] at key
  rw [key, NSArch.mat_phiSplitC, hx₁, hx₂,
    vecQ_smul, vecQ_smul, star_smul_quat, sqMat_smul_smul, Matrix.mul_smul, Matrix.smul_mul, hcc]

end Global

end QuadFormsKB.Tamagawa.Measure.Weil

end
