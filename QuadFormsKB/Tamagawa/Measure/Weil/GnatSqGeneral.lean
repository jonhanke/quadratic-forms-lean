import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqArchP
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqPDArch
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqFinite
import QuadFormsKB.Tamagawa.Measure.Weil.GnatMeasureHaar
import QuadFormsKB.Tamagawa.Measure.Weil.GnatNSHaar

/-!
# Weil's local-ratio identity for the square model over every number field

**Layer:** $F$ any number field ($r_1$ real, $r_2$ complex places), $a, b\in\mathcal O_F\setminus0$, $D = \mathbb H[F,a,b]$ any quaternion
algebra (division or $M_2(F)$), every signature, $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`), $\Phi$ = `sqPEquiv`.

**`map_muP_sqPEquiv_eq_muTam_any`**: $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$, i.e. the `square` field of `GnatTamagawaComparison F`.

*Proof* (Weil 1982, Thm 2.3.1). Haar uniqueness reduces to one open test set
$\Phi(\pi(S_0)) = U_\infty\times K''$ (`sqPEquiv_preimage_box_gen`), with
$S_0 = \{(\alpha,\beta,u) : \beta\in H,\ \alpha\beta^{-1}\in E\}$, $H$ = `Hset` (conjugation in $W$ at $\infty$, the congruence box at
the finite places), $E$ = `Eset` (a cone over $A = \prod_wA_w\subseteq\prod_w\{Q_w = 1\}$ at $\infty$), and
$U_\infty = \prod_w\{L_x\,\mathrm{diag}(1,h) : x\in A_w,\ h\in W_w\}$ (the archimedean component of $\Phi$ is
$x\mapsto\alpha x\beta^{-1} = L_{\alpha\beta^{-1}}\circ c_\beta$, `sqR_eq_decomp`). Then
* $\mu_P(\pi S_0) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mu_{PD}(\operatorname{pd}H)$ (`muP_sqS0Set`);
* $\mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\,N = 8^{r_2}\sigma(A)\,q_E$ (`muSL1N_Eset_mul`, `omegaQuatInf_archCone_eq`);
* $\mu_{PD}(\operatorname{pd}H) = \mu^{(3)}_\infty(W)\,M_3$ (`muPD_pdMk_Hset`);
* $\mu_{\mathrm{Tam}}(U_\infty\times K'') = c_F(4)2^{6r_2}\prod_w|2|_w^{-3}\sigma_w(A_w)\mu^{(3)}_w(W_w)\cdot M_4$ (`lerayMeasure_boxR`, `lerayMeasureC_boxC`);
* $q_EM_3 = c_F(3)\,8^{-r_1}64^{-r_2}\,NM_4$ (`fin_identity_sq_E`, the finite places and the product formula).
-/

open MeasureTheory Measure Set Function NumberField NumberField.InfinitePlace NumberField.mixedEmbedding IsDedekindDomain
  WithZero
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.ArchPolar LerayPadic
open QuadFormsKB.Tamagawa.Measure.LerayReal QuadFormsKB.Tamagawa.Measure.LerayComplex QuadFormsKB.Tamagawa.ArchSOMeasure

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)

local notation "dSq" => gnatSqO ha hb

/-! ### The archimedean component of $\Phi$ -/

theorem nrdUnit_gα_mul_inv (g : (dSq).G) : nrdUnit (gα ha hb g * (gβ ha hb g)⁻¹) = 1 := by
  have : nrdHom (a : F) (b : F) (gα ha hb g * (gβ ha hb g)⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change nrdUnit (gα ha hb g) * (nrdUnit (gβ ha hb g))⁻¹ = 1
    rw [nrd_gα, nrd_gβ, mul_inv_cancel]
  exact this

/-- **$x\mapsto\alpha_wx\beta_w^{-1} = L_{\alpha_w\beta_w^{-1}}\circ\mathrm{diag}(1, c_{\beta_w})$** at a real place. -/
theorem sqR_eq_decomp (w : {w : InfinitePlace F // w.IsReal}) (g : (dSq).G) :
    sqR ha hb w g = lmulSecR ha w (sphPtOfR w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g)) *
      iotaR' w (conjRloc w (unitAtR (a : F) (b : F) w (gβ ha hb g))) := by
  apply Subtype.ext; apply Units.ext
  change ArchSOInst.mat _ (sqR ha hb w g) = ArchSOInst.mat _ (lmulSecR ha w _) * ArchSOInst.mat _ (iotaR' w _)
  rw [mat_lmulSecR, mat_iotaR']
  change ((sqGLR ha hb w g : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ) = _
  rw [sqGLR_apply, sqSO_val, pairR_fst, pairR_snd]
  change sqMat _ _ = sqMat (vecQ (qVec ((unitAtR (a : F) (b : F) w (gα ha hb g * (gβ ha hb g)⁻¹) : (HRe a b w)ˣ) :
    HRe a b w))) 1 * _
  rw [vecQ_qVec, map_mul, map_inv]
  exact sqMat_eq_sec_mul_iota _ _

/-- The same at a complex place. -/
theorem sqC_eq_decomp (w : {w : InfinitePlace F // w.IsComplex}) (g : (dSq).G) :
    sqC ha hb w g = lmulSecC ha w (sphPtOfC w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g)) *
      iotaC' w (conjCloc w (unitAtC (a : F) (b : F) w (gβ ha hb g))) := by
  apply Subtype.ext; apply Units.ext
  change ArchSOC.mat _ (sqC ha hb w g) = ArchSOC.mat _ (lmulSecC ha w _) * ArchSOC.mat _ (iotaC' w _)
  rw [mat_lmulSecC, mat_iotaC']
  change ((sqGLC ha hb w g : GL (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) = _
  rw [sqGLC_apply, sqSO_val, pairC_fst, pairC_snd]
  change sqMat _ _ = sqMat (vecQ (qVec ((unitAtC (a : F) (b : F) w (gα ha hb g * (gβ ha hb g)⁻¹) : (HCx a b w)ˣ) :
    HCx a b w))) 1 * _
  rw [vecQ_qVec, map_mul, map_inv]
  exact sqMat_eq_sec_mul_iota _ _

/-! ### The archimedean boxes -/

section Boxes

variable (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
  (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QRe (qSq a b) w) 1))
  (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
  (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QCx (qSq a b) w) 1))
  (WR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe (QuatZeta.pureFormO a b) w)))
  (WC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx (QuatZeta.pureFormO a b) w)))

/-- $W = \prod_wW_w\subseteq G^{(3)}_\infty$. -/
def WInf : Set (GInfSO (QuatZeta.pureFormO a b)) := (univ.pi WR) ×ˢ (univ.pi WC)

/-- **$U_\infty = \prod_w\{L_x\,\mathrm{diag}(1,h) : x\in A_w,\ h\in W_w\}\subseteq G^{(4)}_\infty$.** -/
def UInf : Set (GInfSO (qSq a b)) :=
  (univ.pi fun w => boxR ha w (AR w) (WR w)) ×ˢ (univ.pi fun w => boxC ha w (AC w) (WC w))

set_option maxHeartbeats 800000 in
theorem sqR_mem_boxR_iff (w : {w : InfinitePlace F // w.IsReal}) (g : (dSq).G) :
    sqR ha hb w g ∈ boxR ha w (AR w) (WR w) ↔
      sphPtOfR w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g) ∈ AR w ∧
        conjRloc w (unitAtR (a : F) (b : F) w (gβ ha hb g)) ∈ WR w := by
  rw [sqR_eq_decomp, boxR, Set.mem_image]
  constructor
  · rintro ⟨⟨x, h⟩, hxh, heq⟩
    have key : (fun p : _ × _ => lmulSecR ha w p.1 * iotaR' w p.2) (x, h) =
        (fun p : _ × _ => lmulSecR ha w p.1 * iotaR' w p.2)
          (sphPtOfR w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g),
            conjRloc w (unitAtR (a : F) (b : F) w (gβ ha hb g))) := heq
    have := lmulSecR_mul_iotaR'_injective ha w key
    rw [Prod.mk.injEq] at this
    rw [← this.1, ← this.2]; exact hxh
  · intro hxh
    exact ⟨(sphPtOfR w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g),
      conjRloc w (unitAtR (a : F) (b : F) w (gβ ha hb g))), hxh, rfl⟩

set_option maxHeartbeats 800000 in
theorem sqC_mem_boxC_iff (w : {w : InfinitePlace F // w.IsComplex}) (g : (dSq).G) :
    sqC ha hb w g ∈ boxC ha w (AC w) (WC w) ↔
      sphPtOfC w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g) ∈ AC w ∧
        conjCloc w (unitAtC (a : F) (b : F) w (gβ ha hb g)) ∈ WC w := by
  rw [sqC_eq_decomp, boxC, Set.mem_image]
  constructor
  · rintro ⟨⟨x, h⟩, hxh, heq⟩
    have key : (fun p : _ × _ => lmulSecC ha w p.1 * iotaC' w p.2) (x, h) =
        (fun p : _ × _ => lmulSecC ha w p.1 * iotaC' w p.2)
          (sphPtOfC w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g),
            conjCloc w (unitAtC (a : F) (b : F) w (gβ ha hb g))) := heq
    have := lmulSecC_mul_iotaC'_injective ha w key
    rw [Prod.mk.injEq] at this
    rw [← this.1, ← this.2]; exact hxh
  · intro hxh
    exact ⟨(sphPtOfC w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g),
      conjCloc w (unitAtC (a : F) (b : F) w (gβ ha hb g))), hxh, rfl⟩

theorem sqInf_mem_UInf_iff (g : (dSq).G) :
    sqInf ha hb g ∈ UInf ha AR AC WR WC ↔
      (∀ w, sphPtOfR w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g) ∈ AR w ∧
        conjRloc w (unitAtR (a : F) (b : F) w (gβ ha hb g)) ∈ WR w) ∧
      (∀ w, sphPtOfC w (gα ha hb g * (gβ ha hb g)⁻¹) (nrdUnit_gα_mul_inv ha hb g) ∈ AC w ∧
        conjCloc w (unitAtC (a : F) (b : F) w (gβ ha hb g)) ∈ WC w) := by
  change (∀ w ∈ univ, sqR ha hb w g ∈ boxR ha w (AR w) (WR w)) ∧ (∀ w ∈ univ, sqC ha hb w g ∈ boxC ha w (AC w) (WC w)) ↔ _
  simp only [mem_univ, true_imp_iff, sqR_mem_boxR_iff, sqC_mem_boxC_iff]

theorem conjInf_mem_WInf_iff (β : (QuatAdele (a : F) (b : F))ˣ) :
    conjInf a b ((quatUnitsEquiv (a : F) (b : F) β).1) ∈ WInf WR WC ↔
      (∀ w, conjRloc w (unitAtR (a : F) (b : F) w β) ∈ WR w) ∧ (∀ w, conjCloc w (unitAtC (a : F) (b : F) w β) ∈ WC w) := by
  change (∀ w ∈ univ, conjR a b w _ ∈ WR w) ∧ (∀ w ∈ univ, conjC a b w _ ∈ WC w) ↔ _
  simp only [mem_univ, true_imp_iff, conjR_eq_conjRloc, conjC_eq_conjCloc]
  rfl

theorem qVec_mem_coneR_iff (h0 : ∀ w, (0 : ℝ) ∈ TR w) (w : {w : InfinitePlace F // w.IsReal})
    (x : (QuatAdele (a : F) (b : F))ˣ) (hx : nrdUnit x = 1) :
    qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w) ∈ coneR (QRe (qSq a b) w) (TR w) (AR w) ↔
      sphPtOfR w x hx ∈ AR w := by
  have e : qVec ((unitAtR (a : F) (b : F) w x : (HRe a b w)ˣ) : HRe a b w) =
      Real.exp 0 • ((sphPtOfR w x hx : SphereLeray.Sph (QRe (qSq a b) w) 1) : Fin 4 → ℝ) := by
    rw [Real.exp_zero, one_smul]; rfl
  rw [e]
  exact mem_coneR_smul_iff (h0 w) _

theorem qVec_mem_coneC_iff (h1 : ∀ w, (1 : ℂˣ) ∈ TC w) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU)
    (w : {w : InfinitePlace F // w.IsComplex}) (x : (QuatAdele (a : F) (b : F))ˣ) (hx : nrdUnit x = 1) :
    qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w) ∈ coneC (QCx (qSq a b) w) (TC w) (AC w) ↔
      sphPtOfC w x hx ∈ AC w := by
  have e : qVec ((unitAtC (a : F) (b : F) w x : (HCx a b w)ˣ) : HCx a b w) =
      ((1 : ℂˣ) : ℂ) • ((sphPtOfC w x hx : SphereLerayC.SphC (QCx (qSq a b) w) 1) : Fin 4 → ℂ) := by
    rw [Units.val_one, one_smul]; rfl
  rw [e, mem_coneC_iff _ (hTh w) (hTh w (h1 w))]
  exact and_iff_right (h1 w)

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (m : HeightOneSpectrum (𝓞 F) → ℕ) (hm1 : ∀ v, 1 ≤ m v)

/-- **Membership in $S_0$**: $g\in S_0$ iff its archimedean image lies in $U_\infty$ and $g$ lies in the subgroup
$S_0(H_S, E_S)$ of the definite proof. -/
theorem mem_sqS0Set_iff (h0 : ∀ w, (0 : ℝ) ∈ TR w) (h1 : ∀ w, (1 : ℂˣ) ∈ TC w)
    (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (g : (dSq).G) :
    g ∈ sqS0Set ha hb (Hset a b S m hm1 (WInf WR WC)) (Eset S m TR AR TC AC) ↔
      sqInf ha hb g ∈ UInf ha AR AC WR WC ∧
        g ∈ sqS0 ha hb (HS a b S m hm1) (ES a b S m) (HS_normalizes_ES a b S m hm1) := by
  rw [sqInf_mem_UInf_iff, mem_sqS0]
  change (conjInf a b ((quatUnitsEquiv (a : F) (b : F) (gβ ha hb g)).1) ∈ WInf WR WC ∧
      quatFinPart a b (gβ ha hb g) ∈ quatCongS a b S m hm1) ∧ gα ha hb g * (gβ ha hb g)⁻¹ ∈ Eset S m TR AR TC AC ↔ _
  rw [conjInf_mem_WInf_iff, mem_Eset]
  simp only [qVec_mem_coneR_iff TR AR h0 _ _ (nrdUnit_gα_mul_inv ha hb g),
    qVec_mem_coneC_iff TC AC h1 hTh _ _ (nrdUnit_gα_mul_inv ha hb g), forall_and]
  change _ ↔ _ ∧ (quatFinPart a b (gβ ha hb g) ∈ quatCongS a b S m hm1 ∧
    quatFinPart a b (gα ha hb g * (gβ ha hb g)⁻¹) ∈ econgS a b S m)
  tauto

theorem sqInf_eq_of_π_eq {g g' : (dSq).G} (h : (dSq).π g = (dSq).π g') : sqInf ha hb g = sqInf ha hb g' := by
  have := congrArg (sqPEquiv ha hb) h
  rw [sqPEquiv_mk, sqPEquiv_mk] at this
  exact congrArg Prod.fst this

/-- **$\Phi^{-1}(U_\infty\times K'') = \pi(S_0)$** for every number field. -/
theorem sqPEquiv_preimage_box_gen
    (hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1)
    (hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v)
    (h0 : ∀ w, (0 : ℝ) ∈ TR w) (h1 : ∀ w, (1 : ℂˣ) ∈ TC w) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) :
    sqPEquiv ha hb ⁻¹' (UInf ha AR AC WR WC ×ˢ QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) S (congSOS m hm1)) =
      (dSq).π '' sqS0Set ha hb (Hset a b S m hm1 (WInf WR WC)) (Eset S m TR AR TC AC) := by
  ext x
  obtain ⟨g, rfl⟩ := (dSq).π_surjective x
  rw [mem_preimage, sqPEquiv_mk]
  change sqInf ha hb g ∈ UInf ha AR AC WR WC ∧ sqFin ha hb g ∈ _ ↔ _
  constructor
  · rintro ⟨hU, hbox⟩
    obtain ⟨g', hg', hgg'⟩ := exists_mem_sqS0_of_box ha hb S m hm1 hS hmS g hbox
    refine ⟨g', (mem_sqS0Set_iff ha hb TR AR TC AC WR WC S m hm1 h0 h1 hTh g').2 ⟨?_, hg'⟩, hgg'⟩
    rw [sqInf_eq_of_π_eq ha hb hgg']; exact hU
  · rintro ⟨g', hg', hgg'⟩
    obtain ⟨hU, hdef⟩ := (mem_sqS0Set_iff ha hb TR AR TC AC WR WC S m hm1 h0 h1 hTh g').1 hg'
    have hbox := sqAdele_mem_boxK ha hb S m hm1 g' hdef
    have e : sqAdele ha hb g' = sqAdele ha hb g := by
      rw [← sqPEquiv_mk, ← sqPEquiv_mk, hgg']
    rw [e] at hbox
    refine ⟨?_, (mem_prod.1 hbox).2⟩
    rw [← sqInf_eq_of_π_eq ha hb hgg']; exact hU

/-! ### The archimedean measures of the boxes -/

open scoped Classical in
/-- **$\mu^{(4)}_\infty(U_\infty) = c_F(4)\,2^{6r_2}\prod_{w\text{ real}}\tfrac18\sigma_w(A_w)\mu_w(W_w)
\prod_{w\text{ complex}}\tfrac1{64}\sigma_w(A_w)\mu_w(W_w)$.** -/
theorem muArchTamSO_UInf (hQ : (qSq a b).Nondegenerate) (hAR : ∀ w, MeasurableSet (AR w))
    (hAC : ∀ w, MeasurableSet (AC w)) (hWR : ∀ w, MeasurableSet (WR w)) (hWC : ∀ w, MeasurableSet (WC w)) :
    muArchTamSO (qSq a b) hQ (UInf ha AR AC WR WC) =
      ENNReal.ofReal (cF F 4 * cxWeil F 4) *
        ((∏ w, ENNReal.ofReal (1 / 8) * (SphereLeray.sig (QRe (qSq a b) w) 1 (AR w) *
          lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
            (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w))) *
        ∏ w, ENNReal.ofReal (1 / 64) * (SphereLerayC.sigC (QCx (qSq a b) w) 1 (AC w) *
          lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
            (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w))) := by
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe (qSq a b) w) (gramDetR_QRe_ne_zero _ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero _ hQ w); infer_instance
  have hsfC : ∀ w, SigmaFinite (lerayMeasureC (QCx (qSq a b) w) (gramDetC_QCx_ne_zero _ hQ w)) := fun w => by
    have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero _ hQ w); infer_instance
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, LerayArch.muArchNF, LerayArch.muArchLeray, UInf,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
  congr 2
  · exact Finset.prod_congr rfl fun w _ => lerayMeasure_boxR ha w _ _ (hAR w) (hWR w)
  · exact Finset.prod_congr rfl fun w _ => lerayMeasureC_boxC ha w _ _ (hAC w) (hWC w)

open scoped Classical in
theorem muArchTamSO_WInf :
    muArchTamSO (QuatZeta.pureFormO a b) (nondegenerate_pureFormO a b ha hb) (WInf WR WC) =
      ENNReal.ofReal (cF F 3 * cxWeil F 3) *
        ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
            (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
        ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
            (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w)) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  have hsf : ∀ w, SigmaFinite (lerayMeasure (QRe (QuatZeta.pureFormO a b) w) (gramDetR_QRe_ne_zero _ hQ w)) :=
    fun w => by have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero _ hQ w); infer_instance
  have hsfC : ∀ w, SigmaFinite (lerayMeasureC (QCx (QuatZeta.pureFormO a b) w) (gramDetC_QCx_ne_zero _ hQ w)) :=
    fun w => by have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero _ hQ w); infer_instance
  rw [muArchTamSO, Measure.smul_apply, smul_eq_mul, LerayArch.muArchNF, LerayArch.muArchLeray, WInf,
    Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]

theorem isOpen_Eset (hm1 : ∀ v, 1 ≤ m v) (hTRo : ∀ w, IsOpen (TR w)) (hARo : ∀ w, IsOpen (AR w))
    (hTCo : ∀ w, IsOpen (TC w)) (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (hACo : ∀ w, IsOpen (AC w)) :
    IsOpen (Eset S m TR AR TC AC) := by
  have hR : ∀ w, Continuous (quatCoordR (a : F) (b : F) w) := fun w => continuous_pi fun i =>
    (continuous_apply w).comp (continuous_fst.comp ((continuous_apply i).comp (quatInfCLE (a : F) (b : F)).continuous))
  have hC : ∀ w, Continuous (quatCoordC (a : F) (b : F) w) := fun w => continuous_pi fun i =>
    (continuous_apply w).comp (continuous_snd.comp ((continuous_apply i).comp (quatInfCLE (a : F) (b : F)).continuous))
  have hcone : IsOpen (archConeSet (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w)
      (fun w => QCx (qSq a b) w) TR AR TC AC) := by
    have e : archConeSet (a := (a : F)) (b := (b : F)) (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w)
        TR AR TC AC = (⋂ w, quatCoordR (a : F) (b : F) w ⁻¹' coneR (QRe (qSq a b) w) (TR w) (AR w)) ∩
          ⋂ w, quatCoordC (a : F) (b : F) w ⁻¹' coneC (QCx (qSq a b) w) (TC w) (AC w) := by
      ext x; simp [archConeSet]
    rw [e]
    exact (isOpen_iInter_of_finite fun w => (isOpen_coneR _ (hTRo w) (hARo w)).preimage (hR w)).inter
      (isOpen_iInter_of_finite fun w => (isOpen_coneC _ (hTCo w) (hTh w) (hACo w)).preimage (hC w))
  exact ((hcone.preimage Units.continuous_val).prod (isOpen_econgS S m hm1)).preimage
    (quatUnitsEquiv (a : F) (b : F)).continuous

end Boxes

/-! ### The comparison on the test set -/

section Main

variable (TR : {w : InfinitePlace F // w.IsReal} → Set ℝ)
  (AR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (SphereLeray.Sph (QRe (qSq a b) w) 1))
  (TC : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ)
  (AC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (SphereLerayC.SphC (QCx (qSq a b) w) 1))
  (WR : ∀ w : {w : InfinitePlace F // w.IsReal}, Set (ArchSO (QRe (QuatZeta.pureFormO a b) w)))
  (WC : ∀ w : {w : InfinitePlace F // w.IsComplex}, Set (ArchSOC (QCx (QuatZeta.pureFormO a b) w)))

open scoped Classical in
/-- The constant $c_F(4)2^{6r_2}8^{-r_1}64^{-r_2} = 8^{r_2}\,c_F(3)2^{3r_2}\cdot c_F(3)8^{-r_1}64^{-r_2}$. -/
theorem arch_const_eq :
    ENNReal.ofReal (cF F 4 * cxWeil F 4) * ((∏ _w : {w : InfinitePlace F // w.IsReal}, ENNReal.ofReal (1 / 8)) *
        ∏ _w : {w : InfinitePlace F // w.IsComplex}, ENNReal.ofReal (1 / 64)) =
      (8 : ℝ≥0∞) ^ nrComplexPlaces F * ENNReal.ofReal (cF F 3 * cxWeil F 3) *
        ENNReal.ofReal (cF F 3 * (∏ _w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ)) *
          ∏ _w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ)) := by
  have hc3 : 0 ≤ cF F 3 := Real.rpow_nonneg (abs_nonneg _) _
  have hx3 : 0 ≤ cxWeil F 3 := cxWeil_pos.le
  have hc4 : 0 ≤ cF F 4 * cxWeil F 4 := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) cxWeil_pos.le
  have hp1 : 0 ≤ ∏ _w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ) := Finset.prod_nonneg fun _ _ => by norm_num
  have h8 : (0 : ℝ) ≤ 8 ^ nrComplexPlaces F := by positivity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by norm_num), ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by norm_num),
    ← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hc4,
    show (8 : ℝ≥0∞) ^ nrComplexPlaces F = ENNReal.ofReal ((8 : ℝ) ^ nrComplexPlaces F) by
      rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_mul h8, ← ENNReal.ofReal_mul (mul_nonneg h8 (mul_nonneg hc3 hx3))]
  congr 1
  rw [← cF_three_sq, cxWeil, cxWeil, show (4 * (4 - 1) / 2 : ℕ) = 6 from rfl, show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl,
    pow_mul, pow_mul]
  have e : (2 : ℝ) ^ 6 = (2 ^ 3) ^ 2 := by norm_num
  rw [e, ← pow_mul, mul_comm 2, pow_mul, show (8 : ℝ) = 2 ^ 3 by norm_num]
  ring

/-- The test set $S_0$ of the square model. -/
abbrev testS0 : Set (dSq).G :=
  sqS0Set ha hb (Hset a b (sqBad ha hb) (sqLev ha hb) (one_le_sqLev ha hb) (WInf WR WC))
    (Eset (sqBad ha hb) (sqLev ha hb) TR AR TC AC)

set_option maxHeartbeats 4000000 in
open scoped Classical in
/-- **The comparison on the test set**: $\mu_P(\pi(S_0)) = \mu_{\mathrm{Tam}}(U_\infty\times K'')$, every number field. -/
theorem muP_testS0_eq (hQ : (qSq a b).Nondegenerate)
    (hTRo : ∀ w, IsOpen (TR w)) (hARo : ∀ w, IsOpen (AR w)) (hTCo : ∀ w, IsOpen (TC w))
    (hACo : ∀ w, IsOpen (AC w)) (hWRo : ∀ w, IsOpen (WR w)) (hWCo : ∀ w, IsOpen (WC w))
    (hTh : ∀ w, TC w ⊆ SphereLerayC.halfU) (h0 : ∀ w, (0 : ℝ) ∈ TR w) (h1 : ∀ w, (1 : ℂˣ) ∈ TC w)
    (hω0 : omegaInf F (nrdShell F TR TC) ≠ 0) (hωt : omegaInf F (nrdShell F TR TC) ≠ ∞) :
    (dSq).muP (muSq ha hb) ((dSq).π '' testS0 ha hb TR AR TC AC WR WC) =
      muTam (qSq a b) hQ (fun _ => 1)
        (UInf ha AR AC WR WC ×ˢ QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) (sqBad ha hb)
          (congSOS (sqLev ha hb) (one_le_sqLev ha hb))) := by
  set S := sqBad ha hb
  set m := sqLev ha hb
  have hm1 := one_le_sqLev ha hb
  have hS : ∀ v ∉ S, Valued.v (2 : v.adicCompletion F) = 1 ∧
      Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
        Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 := fun v hv => good_of_not_mem_sqBad ha hb hv
  have hmS : ∀ v ∈ S, 2 * sExp v < m v ∧ sExp v + eExp a ha v ≤ m v := fun v _ => sqLev_cond ha hb v
  have hsm : ∀ v ∈ S, sExp v < m v := fun v hv => by have := (hmS v hv).1; omega
  have hTRm : ∀ w, MeasurableSet (TR w) := fun w => (hTRo w).measurableSet
  have hARm : ∀ w, MeasurableSet (AR w) := fun w => (hARo w).measurableSet
  have hTCm : ∀ w, MeasurableSet (TC w) := fun w => (hTCo w).measurableSet
  have hACm : ∀ w, MeasurableSet (AC w) := fun w => (hACo w).measurableSet
  have hWRm : ∀ w, MeasurableSet (WR w) := fun w => (hWRo w).measurableSet
  have hWCm : ∀ w, MeasurableSet (WC w) := fun w => (hWCo w).measurableSet
  have hWo : IsOpen (WInf WR WC) := (isOpen_set_pi finite_univ fun w _ => hWRo w).prod
    (isOpen_set_pi finite_univ fun w _ => hWCo w)
  have hWm : MeasurableSet (WInf WR WC) := hWo.measurableSet
  -- the P side
  have hP := muP_sqS0Set ha hb (Hset a b S m hm1 (WInf WR WC)) (Eset S m TR AR TC AC)
    (isOpen_Hset a b S m hm1 hWo) (isOpen_Eset TR AR TC AC S m hm1 hTRo hARo hTCo hTh hACo)
    measurableSet_Bset' (mul_ne_zero omegaInf_Vone_ne_zero muFinUnits_OHatUnits_ne_zero)
    (ENNReal.mul_ne_top omegaInf_Vone_ne_top muFinUnits_OHatUnits_ne_top)
    (fun β hβ => tamIdeles_center_fibre a b S m hm1 ha (WInf WR WC) β hβ)
  set M := muSL1N ha hb {x : (nrdHom (a : F) (b : F)).ker |
    (x : (QuatAdele (a : F) (b : F))ˣ) ∈ Eset S m TR AR TC AC}
  have hD := muPD_pdMk_Hset a b S m hm1 ha hb hS hmS hWm
  -- the SL₁ factor
  have hM := muSL1N_Eset_mul S m TR AR TC AC ha hb hm1 hS hsm hTRm hARm hTCm hTh hACm h0 h1
  rw [omegaQuatInf_archCone_eq (fun w => QRe (qSq a b) w) (fun w => QCx (qSq a b) w) eval_quatCoordR
    eval_quatCoordC TR AR TC AC hTRm hARm hTCm hTh hACm] at hM
  set ω := omegaInf F (nrdShell F TR TC)
  set N := muFinUnits F (NE S m)
  set qE := muFinQuat (a : F) (b : F) (econgS a b S m)
  set σ := (∏ w, SphereLeray.sig (QRe (qSq a b) w) 1 (AR w)) * ∏ w, SphereLerayC.sigC (QCx (qSq a b) w) 1 (AC w)
  have hMN : M * N = (8 : ℝ≥0∞) ^ nrComplexPlaces F * σ * qE := by
    refine (ENNReal.mul_left_inj hω0 hωt).1 ?_
    calc M * N * ω = M * (ω * N) := by ring
      _ = _ := hM
      _ = _ := by ring
  -- the finite identity
  set M3 := QuadFormsKB.Tamagawa.Measure.muFin (QuatZeta.pureFormO a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (QuatZeta.pureFormO a b) S (congSO3S m hm1))
  set M4 := QuadFormsKB.Tamagawa.Measure.muFin (qSq a b) (fun _ => 1)
    (QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) S (congSOS m hm1))
  have hN0 : N ≠ 0 := muFinUnits_NE_ne_zero S m hm1
  have hNt : N ≠ ⊤ := muFinUnits_NE_ne_top S m hm1
  have hqEt : qE ≠ ⊤ := muFinQuat_econgS_ne_top S m
  have hM3t : M3 ≠ ⊤ := muFin_box_ne_top S m hm1 _
  have hM4t : M4 ≠ ⊤ := muFin_box_ne_top S m hm1 _
  set K : ℝ := cF F 3 * (∏ _w : {w : InfinitePlace F // w.IsReal}, (1 / 8 : ℝ)) *
    ∏ _w : {w : InfinitePlace F // w.IsComplex}, (1 / 64 : ℝ)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (Finset.prod_nonneg fun _ _ => by norm_num)) (Finset.prod_nonneg fun _ _ => by norm_num)
  have hfin : qE * M3 = ENNReal.ofReal K * (N * M4) := by
    have h := fin_identity_sq_E ha hb hQ
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top hqEt hM3t)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hNt hM4t))]
    conv_rhs => rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]
    exact h
  -- the SO side
  rw [hP, hD, muTam, Measure.prod_prod, muArchTamSO_UInf ha hb AR AC WR WC hQ hARm hACm hWRm hWCm,
    muArchTamSO_WInf ha hb WR WC]
  refine (ENNReal.mul_left_inj hN0 hNt).1 ?_
  simp only [Finset.prod_mul_distrib]
  calc M * (ENNReal.ofReal (cF F 3 * cxWeil F 3) * ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
          (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
        ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
          (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w)) * M3) * N
      = (M * N) * (ENNReal.ofReal (cF F 3 * cxWeil F 3) * ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
          (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
        ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
          (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w))) * M3 := by ring
    _ = (8 : ℝ≥0∞) ^ nrComplexPlaces F * σ * (ENNReal.ofReal (cF F 3 * cxWeil F 3) *
        ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
          (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
        ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
          (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w))) * (qE * M3) := by
        rw [hMN]; ring
    _ = _ := by
        rw [hfin, show (8 : ℝ≥0∞) ^ nrComplexPlaces F * σ * (ENNReal.ofReal (cF F 3 * cxWeil F 3) *
          ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
            (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
          ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
            (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w))) * (ENNReal.ofReal K * (N * M4)) =
          ((8 : ℝ≥0∞) ^ nrComplexPlaces F * ENNReal.ofReal (cF F 3 * cxWeil F 3) * ENNReal.ofReal K) * σ *
          ((∏ w, lerayMeasure (QRe (QuatZeta.pureFormO a b) w)
            (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WR w)) *
          ∏ w, lerayMeasureC (QCx (QuatZeta.pureFormO a b) w)
            (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) (WC w)) * M4 * N by ring,
          ← arch_const_eq]
        simp only [σ]
        ring

end Main

/-! ### Concrete archimedean data -/

section Data

/-- $\log$-radii $(-1,1)$ at the real places. -/
def TRd : {w : InfinitePlace F // w.IsReal} → Set ℝ := fun _ => Ioo (-1) 1

/-- Radii $\{|\beta - 1| < 1/2\}$ at the complex places. -/
def TCd : {w : InfinitePlace F // w.IsComplex} → Set ℂˣ := fun _ => {β | ‖(β : ℂ) - 1‖ < 1 / 2}

/-- $A_w = \{x\in S_1 : \|x\| < 2\}$ at a real place. -/
def ARd (w : {w : InfinitePlace F // w.IsReal}) : Set (SphereLeray.Sph (QRe (qSq a b) w) 1) :=
  {x | ‖(x : Fin 4 → ℝ)‖ < 2}

/-- $A_w = \{x\in S_1 : \|x\| < 2\}$ at a complex place. -/
def ACd (w : {w : InfinitePlace F // w.IsComplex}) : Set (SphereLerayC.SphC (QCx (qSq a b) w) 1) :=
  {x | ‖(x : Fin 4 → ℂ)‖ < 2}

theorem exists_nbhd_lerayR (w : {w : InfinitePlace F // w.IsReal}) :
    ∃ s : Set (ArchSO (QRe (QuatZeta.pureFormO a b) w)), 1 ∈ s ∧ IsOpen s ∧
      lerayMeasure _ (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) s < ⊤ := by
  have := isHaarMeasure_lerayMeasure (gramDetR_QRe_ne_zero _ (nondegenerate_pureFormO a b ha hb) w)
  exact Measure.exists_isOpen_measure_lt_top _ 1

theorem exists_nbhd_lerayC (w : {w : InfinitePlace F // w.IsComplex}) :
    ∃ s : Set (ArchSOC (QCx (QuatZeta.pureFormO a b) w)), 1 ∈ s ∧ IsOpen s ∧
      lerayMeasureC _ (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w) s < ⊤ := by
  have := isHaarMeasure_lerayMeasureC (gramDetC_QCx_ne_zero _ (nondegenerate_pureFormO a b ha hb) w)
  exact Measure.exists_isOpen_measure_lt_top _ 1

/-- An open neighbourhood $W_w$ of $1$ of finite measure in $SO(Q')(\mathbb R)$. -/
def WRd (w : {w : InfinitePlace F // w.IsReal}) : Set (ArchSO (QRe (QuatZeta.pureFormO a b) w)) :=
  Classical.choose (exists_nbhd_lerayR ha hb w)

/-- An open neighbourhood $W_w$ of $1$ of finite measure in $SO(Q')(\mathbb C)$. -/
def WCd (w : {w : InfinitePlace F // w.IsComplex}) : Set (ArchSOC (QCx (QuatZeta.pureFormO a b) w)) :=
  Classical.choose (exists_nbhd_lerayC ha hb w)

theorem TCd_subset (w : {w : InfinitePlace F // w.IsComplex}) : TCd w ⊆ SphereLerayC.halfU := fun β hβ => by
  have h : ‖(β : ℂ) - 1‖ < 1 / 2 := hβ
  have h2 := Complex.abs_re_le_norm ((β : ℂ) - 1)
  rw [Complex.sub_re, Complex.one_re] at h2
  change 0 < (β : ℂ).re
  have := abs_lt.1 (lt_of_le_of_lt h2 h)
  linarith [this.1]

theorem isOpen_TCd (w : {w : InfinitePlace F // w.IsComplex}) : IsOpen (TCd w) :=
  isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const

theorem one_mem_TCd (w : {w : InfinitePlace F // w.IsComplex}) : (1 : ℂˣ) ∈ TCd w := by
  change ‖((1 : ℂˣ) : ℂ) - 1‖ < 1 / 2
  simp

theorem lintegral_TCd_lt_top (w : {w : InfinitePlace F // w.IsComplex}) :
    ∫⁻ β in TCd w, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂SphereLerayC.volU ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono (g := fun _ => ENNReal.ofReal 4) measurable_const
    fun β hβ => ?_) ?_)
  · have h : ‖(β : ℂ) - 1‖ < 1 / 2 := hβ
    have h1 : 1 / 2 < ‖(β : ℂ)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (β : ℂ)
      rw [norm_one, norm_sub_rev] at this; linarith
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [setLIntegral_const, SphereLerayC.volU_apply (isOpen_TCd w).measurableSet]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (measure_mono ?_)
      (measure_ball_lt_top (x := (1 : ℂ)) (r := 1 / 2)))
    rintro _ ⟨β, hβ, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact hβ

theorem lintegral_TCd_ne_zero (w : {w : InfinitePlace F // w.IsComplex}) :
    ∫⁻ β in TCd w, ENNReal.ofReal (‖(β : ℂ)‖ ^ 2)⁻¹ ∂SphereLerayC.volU ≠ 0 := by
  refine (lt_of_lt_of_le ?_ (setLIntegral_mono
    (Measurable.ennreal_ofReal (((continuous_norm.comp Units.continuous_val).measurable.pow_const 2).inv))
    (fun β hβ => ?_) : ∫⁻ _ in TCd w, ENNReal.ofReal (4 / 9) ∂SphereLerayC.volU ≤ _)).ne'
  · rw [setLIntegral_const, SphereLerayC.volU_apply (isOpen_TCd w).measurableSet]
    refine ENNReal.mul_pos (by norm_num) (lt_of_lt_of_le (Metric.measure_ball_pos volume (1 : ℂ)
      (by norm_num : (0 : ℝ) < 1 / 2)) (measure_mono fun z hz => ?_)).ne'
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, norm_one] at hz; norm_num at hz
    refine ⟨Units.mk0 z hz0, ?_, rfl⟩
    change ‖((Units.mk0 z hz0 : ℂˣ) : ℂ) - 1‖ < 1 / 2
    rw [Units.val_mk0, ← dist_eq_norm]; exact hz
  · have h : ‖(β : ℂ) - 1‖ < 1 / 2 := hβ
    have h1 : ‖(β : ℂ)‖ < 3 / 2 := by
      have := norm_sub_norm_le (β : ℂ) 1
      rw [norm_one] at this; linarith
    have h0 : 0 < ‖(β : ℂ)‖ := norm_pos_iff.2 β.ne_zero
    refine ENNReal.ofReal_le_ofReal ?_
    show (4 : ℝ) / 9 ≤ (‖(β : ℂ)‖ ^ 2)⁻¹
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    nlinarith

theorem omegaInf_nrdShell_d_ne_zero : omegaInf F (nrdShell F (TRd (F := F)) TCd) ≠ 0 := by
  rw [omegaInf_nrdShell (TR := TRd) (TC := TCd) (fun _ => measurableSet_Ioo) (fun w => (isOpen_TCd w).measurableSet)
    TCd_subset]
  refine mul_ne_zero (pow_ne_zero _ two_ne_zero) (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => ?_)
    (Finset.prod_ne_zero_iff.2 fun w _ => mul_ne_zero (by norm_num) (lintegral_TCd_ne_zero w)))
  rw [TRd, Real.volume_Ioo]; norm_num

theorem omegaInf_nrdShell_d_ne_top : omegaInf F (nrdShell F (TRd (F := F)) TCd) ≠ ⊤ := by
  rw [omegaInf_nrdShell (TR := TRd) (TC := TCd) (fun _ => measurableSet_Ioo) (fun w => (isOpen_TCd w).measurableSet)
    TCd_subset]
  refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun w _ => ?_) (ENNReal.prod_ne_top fun w _ =>
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (lintegral_TCd_lt_top w)))
  rw [TRd, Real.volume_Ioo]; exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top

theorem isOpen_ARd (w : {w : InfinitePlace F // w.IsReal}) : IsOpen (ARd (a := a) (b := b) w) :=
  isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem isOpen_ACd (w : {w : InfinitePlace F // w.IsComplex}) : IsOpen (ACd (a := a) (b := b) w) :=
  isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem sig_ARd_ne_top (w : {w : InfinitePlace F // w.IsReal}) :
    SphereLeray.sig (QRe (qSq a b) w) 1 (ARd w) ≠ ⊤ := by
  rw [SphereLeray.sig, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => ?_)
    (SphereLeray.nu_bounded_lt_top one_ne_zero 2)))
  exact le_of_lt (show ‖(x : Fin 4 → ℝ)‖ < 2 from hx)

theorem sigC_ACd_ne_top (w : {w : InfinitePlace F // w.IsComplex}) :
    SphereLerayC.sigC (QCx (qSq a b) w) 1 (ACd w) ≠ ⊤ := by
  rw [SphereLerayC.sigC, Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_ne_top ENNReal.coe_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => ?_)
    (SphereLerayC.nuC_ballS_lt_top one_ne_zero (by norm_num) 2)))
  exact le_of_lt (show ‖(x : Fin 4 → ℂ)‖ < 2 from hx)

theorem norm_qVec_one {K : Type*} [NormedField K] {A B : K} : ‖qVec (1 : ℍ[K,A,B])‖ = 1 := by
  have : qVec (1 : ℍ[K,A,B]) = Pi.single 0 1 := by
    funext i; fin_cases i <;> simp [qVec]
  rw [this, Pi.norm_single, norm_one]

/-- $1\in S_0$. -/
theorem one_mem_testS0 :
    (1 : (dSq).G) ∈ testS0 ha hb TRd ARd TCd ACd (WRd ha hb) (WCd ha hb) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change conjInf a b 1 ∈ WInf (WRd ha hb) (WCd ha hb)
    rw [map_one]
    exact ⟨fun w _ => (Classical.choose_spec (exists_nbhd_lerayR ha hb w)).1,
      fun w _ => (Classical.choose_spec (exists_nbhd_lerayC ha hb w)).1⟩
  · exact (quatCongS a b _ _ _).one_mem
  · rw [mem_Eset]
    refine ⟨fun w => ?_, fun w => ?_, ?_⟩
    · have e : qVec ((unitAtR (a : F) (b : F) w (gα ha hb 1 * (gβ ha hb 1)⁻¹) : (HRe a b w)ˣ) : HRe a b w) =
          Real.exp 0 • ((⟨qVec (1 : HRe a b w), by
            show (QRe (qSq a b) w).eval _ = 1
            rw [eval_qRe_qSq, vecQ_qVec, nrd_one]⟩ : SphereLeray.Sph (QRe (qSq a b) w) 1) : Fin 4 → ℝ) := by
        rw [Real.exp_zero, one_smul]
        change qVec ((unitAtR (a : F) (b : F) w (1 * 1⁻¹) : (HRe a b w)ˣ) : HRe a b w) = _
        rw [inv_one, mul_one, map_one, Units.val_one]
      rw [e, mem_coneR_smul_iff (show (0 : ℝ) ∈ TRd w from ⟨by norm_num, by norm_num⟩)]
      change ‖qVec (1 : HRe a b w)‖ < 2
      rw [norm_qVec_one]; norm_num
    · have e : qVec ((unitAtC (a : F) (b : F) w (gα ha hb 1 * (gβ ha hb 1)⁻¹) : (HCx a b w)ˣ) : HCx a b w) =
          ((1 : ℂˣ) : ℂ) • ((⟨qVec (1 : HCx a b w), by
            show (QCx (qSq a b) w).eval _ = 1
            rw [eval_qCx_qSq, vecQ_qVec, nrd_one]⟩ : SphereLerayC.SphC (QCx (qSq a b) w) 1) : Fin 4 → ℂ) := by
        rw [Units.val_one, one_smul]
        change qVec ((unitAtC (a : F) (b : F) w (1 * 1⁻¹) : (HCx a b w)ˣ) : HCx a b w) = _
        rw [inv_one, mul_one, map_one, Units.val_one]
      rw [e, mem_coneC_iff _ (TCd_subset w) (TCd_subset w (one_mem_TCd w))]
      refine ⟨one_mem_TCd w, ?_⟩
      change ‖qVec (1 : HCx a b w)‖ < 2
      rw [norm_qVec_one]; norm_num
    · change quatFinPart a b (1 * 1⁻¹) ∈ _
      rw [inv_one, mul_one, map_one]; exact (econgS a b _ _).one_mem

end Data

/-! ### The theorem -/

/-- **Weil's local-ratio identity for the square model over every number field** ($m = 4$, every quaternion algebra
$D = \mathbb H[F,a,b]$, every signature, complex places allowed): $\Phi_*\mu_P = \mu_{\mathrm{Tam}}$ for the $\Phi$ =
`sqPEquiv`. This removes the totally real and totally definite hypotheses of `map_muP_sqPEquiv_eq_muTam`. -/
@[kb "weil1982" "Thm 2.3.1 (local ratios, ∏_v r_v = 1); §3.7, p. 65 [unverified page]"]
theorem map_muP_sqPEquiv_eq_muTam_any (hQ : (qSq a b).Nondegenerate) :
    ((gnatSqO ha hb).muP (muSq ha hb)).map (sqPEquiv ha hb) = muTam (qSq a b) hQ (fun _ => 1) := by
  classical
  set S₀ := testS0 ha hb TRd ARd TCd ACd (WRd ha hb) (WCd ha hb)
  set U := UInf ha ARd ACd (WRd ha hb) (WCd ha hb) ×ˢ
    QuadFormsKB.Tamagawa.Measure.boxSO (qSq a b) (sqBad ha hb) (congSOS (sqLev ha hb) (one_le_sqLev ha hb))
  have hWRo : ∀ w, IsOpen (WRd ha hb w) := fun w => (Classical.choose_spec (exists_nbhd_lerayR ha hb w)).2.1
  have hWCo : ∀ w, IsOpen (WCd ha hb w) := fun w => (Classical.choose_spec (exists_nbhd_lerayC ha hb w)).2.1
  have hTRo : ∀ w, IsOpen (TRd (F := F) w) := fun _ => isOpen_Ioo
  have h0 : ∀ w, (0 : ℝ) ∈ TRd (F := F) w := fun _ => ⟨by norm_num, by norm_num⟩
  have hpre : sqPEquiv ha hb ⁻¹' U = (dSq).π '' S₀ :=
    sqPEquiv_preimage_box_gen ha hb TRd ARd TCd ACd (WRd ha hb) (WCd ha hb) (sqBad ha hb) (sqLev ha hb)
      (one_le_sqLev ha hb) (fun v hv => good_of_not_mem_sqBad ha hb hv) (fun v _ => sqLev_cond ha hb v) h0
      one_mem_TCd TCd_subset
  have heq := muP_testS0_eq ha hb TRd ARd TCd ACd (WRd ha hb) (WCd ha hb) hQ hTRo isOpen_ARd isOpen_TCd isOpen_ACd
    hWRo hWCo TCd_subset h0 one_mem_TCd omegaInf_nrdShell_d_ne_zero omegaInf_nrdShell_d_ne_top
  have hS₀o : IsOpen S₀ := isOpen_sqS0Set ha hb _ _
    (isOpen_Hset a b _ _ _ ((isOpen_set_pi finite_univ fun w _ => hWRo w).prod
      (isOpen_set_pi finite_univ fun w _ => hWCo w)))
    (isOpen_Eset TRd ARd TCd ACd _ _ (one_le_sqLev ha hb) hTRo isOpen_ARd isOpen_TCd TCd_subset isOpen_ACd)
  have hUeq : U = sqPEquiv ha hb '' ((dSq).π '' S₀) := by
    rw [← hpre, Set.image_preimage_eq _ (sqPEquiv ha hb).surjective]
  have hUo : IsOpen U := by
    rw [hUeq]
    exact (sqPEquiv ha hb).isOpenMap _ (QuotientGroup.isOpenMap_coe _ hS₀o)
  have hUne : U.Nonempty := by
    refine ⟨sqPEquiv ha hb ((dSq).π 1), ?_⟩
    rw [← mem_preimage, hpre]; exact ⟨1, one_mem_testS0 ha hb, rfl⟩
  have hmap : ((gnatSqO ha hb).muP (muSq ha hb)).map (sqPEquiv ha hb) U =
      (dSq).muP (muSq ha hb) ((dSq).π '' S₀) := by
    rw [Measure.map_apply (map_continuous (sqPEquiv ha hb)).measurable hUo.measurableSet, hpre]
  have := (gnatSqO ha hb).isHaarMeasure_muP (muSq ha hb)
  have : (((gnatSqO ha hb).muP (muSq ha hb)).map (sqPEquiv ha hb)).IsHaarMeasure :=
    (sqPEquiv ha hb).isHaarMeasure_map _
  -- finiteness of the test value
  have hfin : muTam (qSq a b) hQ (fun _ => 1) U ≠ ⊤ := by
    rw [muTam, Measure.prod_prod, muArchTamSO_UInf ha hb ARd ACd (WRd ha hb) (WCd ha hb) hQ
      (fun w => (isOpen_ARd w).measurableSet) (fun w => (isOpen_ACd w).measurableSet)
      (fun w => (hWRo w).measurableSet) (fun w => (hWCo w).measurableSet)]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top
      (ENNReal.prod_ne_top fun w _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (sig_ARd_ne_top w) (Classical.choose_spec (exists_nbhd_lerayR ha hb w)).2.2.ne))
      (ENNReal.prod_ne_top fun w _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (sigC_ACd_ne_top w) (Classical.choose_spec (exists_nbhd_lerayC ha hb w)).2.2.ne))))
      (muFin_box_ne_top (sqBad ha hb) (sqLev ha hb) (one_le_sqLev ha hb) _)
  refine eq_of_eq_on_open _ _ hUo hUne (by rw [hmap, heq]; exact hfin) ?_
  rw [hmap, heq]

end QuadFormsKB.Tamagawa.Measure.Weil

end
