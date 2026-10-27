import QuadFormsKB.Tamagawa.Measure.LocalSO
import QuadFormsKB.Tamagawa.Measure.Weil.CovolumeTransport
import QuadFormsKB.Tamagawa.AlphaLawOdd
import QuadFormsKB.Tamagawa.OrbitalEuler

/-!
# Similar forms: the local Tamagawa measures at a finite place

**Layer:** a number field $F$, a finite place $v$. $Q_0$ is a nondegenerate form over $\mathcal O_F$ in $n$ variables,
$G \in M_n(\mathcal O_F)$ with $\det G \ne 0$, $c \in \mathcal O_F\setminus 0$, and $Q_1 = c\,(Q_0\circ G)$ (`compMat`).

**Defines**
* `simConjOrth QF₀ QF₁ G c hH K`: $g\mapsto G^{-1}gG$, $O(Q_0)(K)\cong O(Q_1)(K)$ for every field $K \supseteq F$, whenever the
  Hessians satisfy $H_1 = c\,G^{\mathsf T}H_0G$; `simConjSO` its restriction to $SO$.

**Proves**
* **`map_muLoc_conj`**: $(g\mapsto G^{-1}gG)_*\mu_v^{Q_0} = \|c\|_v^{N}\,\|\det G\|_v^{n+1}\,\mu_v^{Q_1}$ on
  $O(Q_1)(F_v)$, $N = n(n+1)/2$, for the local measures `muLoc` ($\lambda_v = 1$);
* **`map_muLocSO_conj`**: the same on $SO(Q_1)(F_v)$ for `muLocSO`.

*Proof.* Both sides are Haar measures (`map_eq_smul_of_compact_open`); evaluate on $O(\mathfrak o_v^n)$ for $Q_1$, whose
preimage is the stabilizer of the lattice $G\mathfrak o_v^n$ for $Q_0$, of measure
$\beta_v(Q_0\circ G)\,\|\det G\|_v^{n+1}$ (`muLoc_eq_haarNorm_latOf`), while $\beta_v(c\,Q) = \|c\|_v^{-N}\beta_v(Q)$
(`localDensityForm_smul`).

Source: Weil 1982, §2.2.1, p. 14 (local measures and coordinate changes), §2.3, Thm 2.3.1, pp. 21–22.
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm

section Algebra

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (QF₀ QF₁ : QuadForm F n) (G : GL (Fin n) F) (c : F)
  (hH : QF₁.hessian = c • ((G : Matrix (Fin n) (Fin n) F)ᵀ * QF₀.hessian * (G : Matrix (Fin n) (Fin n) F)))
  (K : Type*) [Field K] [Algebra F K]

/-- $G$ in $\mathrm{GL}_n(K)$. -/
abbrev glK : GL (Fin n) K := Matrix.GeneralLinearGroup.map (algebraMap F K) G

theorem glK_val : (glK G K : Matrix (Fin n) (Fin n) K) = (G : Matrix (Fin n) (Fin n) F).map (algebraMap F K) := rfl

include hH in
theorem hessian_map_sim :
    QF₁.hessian.map (algebraMap F K) =
      algebraMap F K c • ((glK G K : Matrix (Fin n) (Fin n) K)ᵀ * QF₀.hessian.map (algebraMap F K) *
        (glK G K : Matrix (Fin n) (Fin n) K)) := by
  rw [hH, glK_val, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem conj_aux {R : Type*} [CommRing R] {P Pi H X : Matrix (Fin n) (Fin n) R} (h1 : P * Pi = 1)
    (hX : Xᵀ * H * X = H) : (Pi * X * P)ᵀ * (Pᵀ * H * P) * (Pi * X * P) = Pᵀ * H * P := by
  have h1' : Piᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  calc (Pi * X * P)ᵀ * (Pᵀ * H * P) * (Pi * X * P)
      = Pᵀ * (Xᵀ * (Piᵀ * Pᵀ) * H * (P * Pi) * X) * P := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Pᵀ * H * P := by rw [h1', h1, Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_assoc]

theorem glK_mul_inv : (glK G K).val * ((glK G K)⁻¹ : GL (Fin n) K).val = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem glK_inv_mul : ((glK G K)⁻¹ : GL (Fin n) K).val * (glK G K).val = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

include hH in
theorem conj_mem_orthGroup {g : GL (Fin n) K} (hg : g ∈ orthGroup QF₀ K) :
    (glK G K)⁻¹ * g * glK G K ∈ orthGroup QF₁ K := by
  rw [mem_orthGroup] at hg ⊢
  rw [hessian_map_sim QF₀ QF₁ G c hH K]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [conj_aux (glK_mul_inv G K) hg]

include hH in
theorem conj_inv_mem_orthGroup (hc : c ≠ 0) {g : GL (Fin n) K} (hg : g ∈ orthGroup QF₁ K) :
    glK G K * g * (glK G K)⁻¹ ∈ orthGroup QF₀ K := by
  rw [mem_orthGroup] at hg ⊢
  rw [hessian_map_sim QF₀ QF₁ G c hH K] at hg
  have hc' : algebraMap F K c ≠ 0 := (map_ne_zero _).mpr hc
  set H := QF₀.hessian.map (algebraMap F K)
  set P := (glK G K).val
  set Pi := ((glK G K)⁻¹ : GL (Fin n) K).val
  have hg' : (g.val)ᵀ * (Pᵀ * H * P) * g.val = Pᵀ * H * P := by
    have := congrArg (fun M => (algebraMap F K c)⁻¹ • M) hg
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc', one_smul] at this
    exact this
  have key := conj_aux (P := Pi) (Pi := P) (glK_inv_mul G K) hg'
  have hPT : Piᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, glK_mul_inv, Matrix.transpose_one]
  have e : Piᵀ * (Pᵀ * H * P) * Pi = H := by
    rw [show Piᵀ * (Pᵀ * H * P) * Pi = (Piᵀ * Pᵀ) * H * (P * Pi) by simp only [Matrix.mul_assoc], hPT,
      glK_mul_inv, Matrix.one_mul, Matrix.mul_one]
  simp only [Units.val_mul]
  rw [e] at key
  exact key

/-- **Conjugation by $G$**: $O(Q_0)(K)\cong O(Q_1)(K)$, $g\mapsto G^{-1}gG$, when $H_1 = c\,G^{\mathsf T}H_0G$, $c\ne0$. -/
def simConjOrth (hc : c ≠ 0) : orthGroup QF₀ K ≃* orthGroup QF₁ K where
  toFun g := ⟨(glK G K)⁻¹ * (g : GL (Fin n) K) * glK G K, conj_mem_orthGroup QF₀ QF₁ G c hH K g.2⟩
  invFun g := ⟨glK G K * (g : GL (Fin n) K) * (glK G K)⁻¹, conj_inv_mem_orthGroup QF₀ QF₁ G c hH K hc g.2⟩
  left_inv g := by ext1; simp [mul_assoc]
  right_inv g := by ext1; simp [mul_assoc]
  map_mul' g h := by ext1; simp [mul_assoc]

theorem simConjOrth_val (hc : c ≠ 0) (g : orthGroup QF₀ K) :
    ((simConjOrth QF₀ QF₁ G c hH K hc g : orthGroup QF₁ K) : GL (Fin n) K) =
      (glK G K)⁻¹ * (g : GL (Fin n) K) * glK G K := rfl

theorem simConjOrth_symm_val (hc : c ≠ 0) (g : orthGroup QF₁ K) :
    (((simConjOrth QF₀ QF₁ G c hH K hc).symm g : orthGroup QF₀ K) : GL (Fin n) K) =
      glK G K * (g : GL (Fin n) K) * (glK G K)⁻¹ := rfl

theorem simConjOrth_mem_soSub_iff (hc : c ≠ 0) (g : orthGroup QF₀ K) :
    simConjOrth QF₀ QF₁ G c hH K hc g ∈ soSub QF₁ K ↔ g ∈ soSub QF₀ K := by
  simp only [mem_soSub, simConjOrth_val, Units.val_mul, det_mul]
  rw [mul_comm, ← mul_assoc, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul]

/-- **Conjugation by $G$ on $SO$**: $SO(Q_0)(K)\cong SO(Q_1)(K)$. -/
def simConjSO (hc : c ≠ 0) : soSub QF₀ K ≃* soSub QF₁ K where
  toFun g := ⟨simConjOrth QF₀ QF₁ G c hH K hc g, (simConjOrth_mem_soSub_iff QF₀ QF₁ G c hH K hc g).mpr g.2⟩
  invFun g := ⟨(simConjOrth QF₀ QF₁ G c hH K hc).symm g, by
    rw [← simConjOrth_mem_soSub_iff QF₀ QF₁ G c hH K hc, MulEquiv.apply_symm_apply]; exact g.2⟩
  left_inv g := by ext1; simp
  right_inv g := by ext1; simp
  map_mul' g h := by ext1; simp

theorem simConjSO_val (hc : c ≠ 0) (g : soSub QF₀ K) :
    ((simConjSO QF₀ QF₁ G c hH K hc g : soSub QF₁ K) : orthGroup QF₁ K) = simConjOrth QF₀ QF₁ G c hH K hc g := rfl

end Algebra


section Place

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Q₀ : QuadForm (𝓞 F) n)

/-- **The similar form** $Q_1 = c\,(Q_0\circ G)$ over $\mathcal O_F$. -/
abbrev simForm (c : 𝓞 F) (G : Matrix (Fin n) (Fin n) (𝓞 F)) : QuadForm (𝓞 F) n := c • Q₀.compMat G

/-- **The Jacobian of the similarity** $\delta = c^{n(n+1)/2}\det(G)^{n+1} \in \mathcal O_F$: the determinant of the
coefficient map $q \mapsto c\,(q\circ G)$. -/
abbrev simJac (c : 𝓞 F) (G : Matrix (Fin n) (Fin n) (𝓞 F)) : 𝓞 F := c ^ (n * (n + 1) / 2) * G.det ^ (n + 1)

variable {Q₀} {c : 𝓞 F} {G : Matrix (Fin n) (Fin n) (𝓞 F)}

theorem simJac_ne_zero (hc : c ≠ 0) (hG : G.det ≠ 0) : simJac c G ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hG)

theorem hessian_simForm (hG : G.det ≠ 0) :
    ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)).hessian = (c : F) •
      (((LatChange.glF G hG : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * (Q₀.map (algebraMap (𝓞 F) F)).hessian *
        ((LatChange.glF G hG : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
  rw [Siegel.hessian_map_NF, Siegel.hessian_map_NF, LatChange.glF_val, LatChange.hessian_smul, hessian_compMat]
  have h1 : (Gᵀ * Q₀.hessian * G).map (algebraMap (𝓞 F) F) =
      (G.map (algebraMap (𝓞 F) F))ᵀ * Q₀.hessian.map (algebraMap (𝓞 F) F) * G.map (algebraMap (𝓞 F) F) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [← h1]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem coe_ne_zero_of_ne_zero (hc : c ≠ 0) : (c : F) ≠ 0 :=
  (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hc

/-- **The local conjugation** $g\mapsto G^{-1}gG$, $O(Q_0)(F_v)\cong O(Q_1)(F_v)$, as an isomorphism of topological
groups. -/
def simConjV (hc : c ≠ 0) (hG : G.det ≠ 0) :
    orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) ≃ₜ*
      orthGroup ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) (v.adicCompletion F) :=
  { simConjOrth _ _ (LatChange.glF G hG) (c : F) (hessian_simForm hG) (v.adicCompletion F)
      (coe_ne_zero_of_ne_zero hc) with
    continuous_toFun := Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
    continuous_invFun := Continuous.subtype_mk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const) _ }

theorem simConjV_val (hc : c ≠ 0) (hG : G.det ≠ 0) (g : orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)) :
    ((simConjV v hc hG g : orthGroup _ _) : GL (Fin n) (v.adicCompletion F)) =
      (glK (LatChange.glF G hG) (v.adicCompletion F))⁻¹ * (g : GL (Fin n) (v.adicCompletion F)) *
        glK (LatChange.glF G hG) (v.adicCompletion F) := rfl

theorem glOf_eq_glK (hG : G.det ≠ 0) :
    glOf v (G.map (NF.ι v)) (LatChange.det_map_ι_ne_zero v hG) =
      glK (LatChange.glF G hG) (v.adicCompletion F) := by
  ext i j
  rfl

/-- **The preimage of $O(\mathfrak o_v^n)$ for $Q_1$ is the stabilizer of $G\mathfrak o_v^n$ for $Q_0$.** -/
theorem simConjV_preimage_stdStab (hc : c ≠ 0) (hG : G.det ≠ 0) :
    simConjV v hc hG ⁻¹' ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v :
        Subgroup (orthGroup _ (v.adicCompletion F))) : Set (orthGroup _ (v.adicCompletion F))) =
      ((stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype
        (latOf v (G.map (NF.ι v))) : Subgroup (orthGroup _ (v.adicCompletion F))) :
          Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))) := by
  ext g
  rw [latOf_eq v _ (LatChange.det_map_ι_ne_zero v hG), glOf_eq_glK v hG]
  set P := glK (LatChange.glF G hG) (v.adicCompletion F)
  change locAct v ((simConjV v hc hG g : orthGroup _ _) : GL (Fin n) (v.adicCompletion F)) (std v) = std v ↔
    locAct v (g : GL (Fin n) (v.adicCompletion F)) (locAct v P (std v)) = locAct v P (std v)
  rw [simConjV_val, locAct_mul, locAct_mul, locAct_eq_iff, inv_inv]

/-- The norm of an integer at $v$ through the completion of the integers. -/
theorem norm_ι_eq (x : 𝓞 F) :
    ‖((NF.ι v x : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖ := rfl

/-- $2\cdot$`latLocalFactor` of the local basis $G$: $\beta_v(Q_0\circ G)\,\|\det G\|_v^{n+1}$. -/
theorem two_mul_latLocalFactor (G : Matrix (Fin n) (Fin n) (𝓞 F)) :
    2 * LatChange.latLocalFactor v Q₀ (G.map (NF.ι v)) =
      NF.localDensityForm v (Q₀.compMat G) (Q₀.compMat G) *
        ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F G.det)‖ ^ (n + 1) := by
  unfold LatChange.latLocalFactor
  have e1 : (NF.Qp v Q₀).compMat (G.map (NF.ι v)) = NF.Qp v (Q₀.compMat G) := map_compMat _ _ _
  have e2 : ‖(((G.map (NF.ι v)).det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ =
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F G.det)‖ := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [e1, e2, NF.localDensityForm_eq_completion]
  ring

/-- **Scaling the self-density at $v$:** $\beta_v(cQ) = \|c\|_v^{-n(n+1)/2}\beta_v(Q)$. -/
theorem localDensityForm_smul_norm {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hc : c ≠ 0) :
    NF.localDensityForm v (c • Q) (c • Q) * ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F c)‖ ^
      (n * (n + 1) / 2) = NF.localDensityForm v Q Q := by
  have hinj : Function.Injective (NF.ι v) := by
    intro x y hxy
    apply RingOfIntegers.coe_injective
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) hxy
    simpa using this
  have hc' : NF.ι v c ≠ 0 := fun h => hc (hinj (by rw [h, map_zero]))
  obtain ⟨o, ho, ho'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) (NF.irreducible_π v) hc'
  have hQp : (NF.Qp v Q).Nondegenerate := by
    rw [QuadForm.Nondegenerate, NF.det_hessian_Qp]
    exact fun h => hQ (hinj (by rw [h, map_zero]))
  have hsmul : NF.Qp v (c • Q) = NF.ι v c • NF.Qp v Q := Tamagawa.map_smul_form _ _ _
  rw [NF.localDensityForm_eq_completion, NF.localDensityForm_eq_completion, hsmul,
    Tamagawa.localDensityForm_smul (NF.Qp v Q) hQp (NF.irreducible_π v) ho ho', ← norm_ι_eq,
    norm_coe_of_pow_dvd v ho ho']
  have hq : (0 : ℝ) < (DVR.q (v.adicCompletionIntegers F) : ℝ) := Nat.cast_pos.mpr DVR.q_pos
  rw [inv_pow, ← pow_mul]
  field_simp

theorem nondegenerate_simForm (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (simForm Q₀ c G).Nondegenerate := by
  have h := LatChange.nondegenerate_compMat_of_det hQ hG
  rw [QuadForm.Nondegenerate] at h ⊢
  rw [simForm, LatChange.hessian_smul, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) h

/-- **The local ratio at a finite place:** $(g\mapsto G^{-1}gG)_*\mu_v^{Q_0} = \|\delta\|_v\,\mu_v^{Q_1}$ on
$O(Q_1)(F_v)$, $\delta = c^{n(n+1)/2}\det(G)^{n+1}$ (`simJac`), for the local measures ($\lambda_v = 1$). -/
@[kb "weil1982" "§2.2.1, p. 14 (local measures under a change of coordinates)"]
theorem map_muLoc_simConjV (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (Measure.muLoc v Q₀ 1).map (simConjV v hc hG) =
      ENNReal.ofReal ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ •
        Measure.muLoc v (simForm Q₀ c G) 1 := by
  have hQ₁ := nondegenerate_simForm hQ hc hG
  have hQG : (Q₀.compMat G).Nondegenerate := LatChange.nondegenerate_compMat_of_det hQ hG
  have := Measure.isHaarMeasure_muLoc v Q₀ hQ one_pos
  have := Measure.isHaarMeasure_muLoc v (simForm Q₀ c G) hQ₁ one_pos
  rw [map_eq_smul_of_compact_open (simConjV v hc hG) (Measure.muLoc v Q₀ 1) (Measure.muLoc v (simForm Q₀ c G) 1)
    (Measure.isCompact_stdStab v _)
    (Measure.isOpen_stdStab v _) ⟨1, (stdStab _ v).one_mem⟩]
  congr 1
  have hA : Measure.muLoc v Q₀ 1 ((stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype
      (latOf v (G.map (NF.ι v))) : Subgroup _) : Set (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F))) =
      ENNReal.ofReal (2 * LatChange.latLocalFactor v Q₀ (G.map (NF.ι v))) := by
    rw [Measure.muLoc_eq_haarNorm_latOf v Q₀ hQ one_pos _ (LatChange.det_map_ι_ne_zero v hG)]
    refine (Measure.haarNorm_self _ _ _).trans ?_
    rw [div_one]; rfl
  rw [simConjV_preimage_stdStab, hA, Measure.muLoc_stdStab, div_one, two_mul_latLocalFactor]
  have hβ := LatChange.localDensityForm_self_pos v (Q₀.compMat G) hQG
  have hs := localDensityForm_smul_norm v hQG hc
  set β := NF.localDensityForm v (Q₀.compMat G) (Q₀.compMat G)
  set β₁ := NF.localDensityForm v (simForm Q₀ c G) (simForm Q₀ c G)
  set x := ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F G.det)‖
  set y := ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F c)‖
  have hy : 0 < y := norm_pos_iff.mpr ((map_ne_zero _).mpr (coe_ne_zero_of_ne_zero hc))
  have hβ₁ : 0 < β₁ := by
    have : 0 < β₁ * y ^ (n * (n + 1) / 2) := hs ▸ hβ
    exact pos_of_mul_pos_left this (pow_nonneg hy.le _)
  have hδ : ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ =
      y ^ (n * (n + 1) / 2) * x ^ (n + 1) := by
    simp only [simJac, map_mul, map_pow, norm_mul, norm_pow, x, y]
  rw [hδ, ← ENNReal.ofReal_div_of_pos hβ₁, ← hs]
  congr 1
  field_simp

theorem simConjV_mem_soSub (hc : c ≠ 0) (hG : G.det ≠ 0) (g : Measure.SOv v Q₀) :
    simConjV v hc hG g.1 ∈ soSub ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) (v.adicCompletion F) :=
  (simConjOrth_mem_soSub_iff _ _ (LatChange.glF G hG) (c : F) (hessian_simForm hG) (v.adicCompletion F)
    (coe_ne_zero_of_ne_zero hc) g.1).mpr g.2

theorem simConjV_symm_mem_soSub (hc : c ≠ 0) (hG : G.det ≠ 0) (g : Measure.SOv v (simForm Q₀ c G)) :
    (simConjV v hc hG).symm g.1 ∈ soSub (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F) := by
  rw [← simConjOrth_mem_soSub_iff _ _ (LatChange.glF G hG) (c : F) (hessian_simForm hG) (v.adicCompletion F)
    (coe_ne_zero_of_ne_zero hc)]
  convert g.2 using 1
  exact (simConjV v hc hG).apply_symm_apply g.1

/-- **The local conjugation on $SO$**: $SO(Q_0)(F_v)\cong SO(Q_1)(F_v)$, $g\mapsto G^{-1}gG$. -/
def simConjSOV (hc : c ≠ 0) (hG : G.det ≠ 0) : Measure.SOv v Q₀ ≃ₜ* Measure.SOv v (simForm Q₀ c G) where
  toFun g := ⟨simConjV v hc hG g.1, simConjV_mem_soSub v hc hG g⟩
  invFun g := ⟨(simConjV v hc hG).symm g.1, simConjV_symm_mem_soSub v hc hG g⟩
  left_inv g := Subtype.ext ((simConjV v hc hG).symm_apply_apply g.1)
  right_inv g := Subtype.ext ((simConjV v hc hG).apply_symm_apply g.1)
  map_mul' g h := Subtype.ext (map_mul (simConjV v hc hG) g.1 h.1)
  continuous_toFun := Continuous.subtype_mk ((simConjV v hc hG).continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk ((simConjV v hc hG).symm.continuous.comp continuous_subtype_val) _

theorem simConjSOV_val (hc : c ≠ 0) (hG : G.det ≠ 0) (g : Measure.SOv v Q₀) :
    ((simConjSOV v hc hG g : Measure.SOv v (simForm Q₀ c G)) : orthGroup _ (v.adicCompletion F)) =
      simConjV v hc hG g.1 := rfl

theorem image_val_preimage_simConjSOV (hc : c ≠ 0) (hG : G.det ≠ 0) (S : Set (Measure.SOv v (simForm Q₀ c G))) :
    Subtype.val '' (simConjSOV v hc hG ⁻¹' S) = simConjV v hc hG ⁻¹' (Subtype.val '' S) := by
  ext g
  constructor
  · rintro ⟨h, hh, hg⟩
    rw [Set.mem_preimage, ← hg]
    exact ⟨simConjSOV v hc hG h, Set.mem_preimage.mp hh, simConjSOV_val v hc hG h⟩
  · rintro ⟨k, hk, hgk⟩
    have hg : g = (simConjV v hc hG).symm k.1 := by rw [hgk, ContinuousMulEquiv.symm_apply_apply]
    refine ⟨⟨_, simConjV_symm_mem_soSub v hc hG k⟩, ?_, hg.symm⟩
    have : simConjSOV v hc hG ⟨_, simConjV_symm_mem_soSub v hc hG k⟩ = k :=
      (simConjSOV v hc hG).apply_symm_apply k
    rw [Set.mem_preimage, this]; exact hk

/-- **The local ratio on $SO$:** $(g\mapsto G^{-1}gG)_*\mu_v^{SO,Q_0} = \|\delta\|_v\,\mu_v^{SO,Q_1}$ for `muLocSO`
($\lambda_v = 1$, $n > 0$). -/
@[kb "weil1982" "§2.2.1, p. 14 (local measures under a change of coordinates)"]
theorem map_muLocSO_simConjSOV (hn : 0 < n) (hQ : Q₀.Nondegenerate) (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (Measure.muLocSO v Q₀ 1).map (simConjSOV v hc hG) =
      ENNReal.ofReal ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ •
        Measure.muLocSO v (simForm Q₀ c G) 1 := by
  have hQ₁ := nondegenerate_simForm hQ hc hG
  have hE₀ := Measure.measurableEmbedding_soSub v Q₀ hQ
  have hE₁ := Measure.measurableEmbedding_soSub v (simForm Q₀ c G) hQ₁
  ext S hS
  have hm₁ : Measurable (simConjSOV (Q₀ := Q₀) v hc hG) := (simConjSOV v hc hG).continuous.measurable
  have hm₀ : Measurable (simConjV (Q₀ := Q₀) v hc hG) := (simConjV v hc hG).continuous.measurable
  rw [Measure.map_apply hm₁ hS, Measure.smul_apply,
    Measure.muLocSO_eq_comap v Q₀ hQ hn one_pos, Measure.muLocSO_eq_comap v _ hQ₁ hn one_pos,
    hE₀.comap_apply, hE₁.comap_apply, image_val_preimage_simConjSOV,
    ← Measure.map_apply hm₀ (hE₁.measurableSet_image.mpr hS),
    map_muLoc_simConjV v hQ hc hG, Measure.smul_apply]

end Place


end QuadFormsKB.Tamagawa.Measure.Weil
