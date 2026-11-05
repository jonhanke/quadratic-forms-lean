/-
# Hanke 2005, Lemma 6.2: conjugation by a similitude preserves volumes in $O(V_\mathfrak p)$

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $Q_0$ nondegenerate over $\mathcal O_F$ (Hanke's $\varphi$; $\varphi_\mathfrak p$ its localization), $H_\mathfrak p$ = `hessV v Q₀`
its Gram matrix over $F_\mathfrak p$, a similitude $\alpha\in\mathrm{GL}_n(F_\mathfrak p)$, ${}^t\alpha H_\mathfrak p\alpha = \xi H_\mathfrak p$.

**Proves**
* `relRatio_stabLat_similitude`: $r(O(\alpha\Lambda), O(\Lambda)) = 1$ for every lattice $\Lambda = L_\mathfrak p$, i.e.
  $\mathrm{vol}(\alpha O(\Lambda)\alpha^{-1}) = \mathrm{vol}(O(\Lambda))$;
* `relRatio_conj_similitude` (**Lemma 6.2**): $r(\alpha D\alpha^{-1}, D) = 1$ for every open compact subgroup $D$ of $O(V_\mathfrak p)$.
-/
import QuadFormsKB.Literature.Hanke2005.Sec6Defs
import QuadFormsKB.Tamagawa.LatticeChangeNF
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Literature.Hanke2005.LocalDensity
import QuadFormsKB.Tamagawa.SiegelClassical

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Local

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

section Aux

theorem hessV_eq (Q₀ : QuadForm (𝓞 F) n) :
    hessV v Q₀ = (NF.Qp v Q₀).hessian.map (algebraMap 𝔬 Fv) := by
  unfold hessV
  rw [← QuadForm.hessian_map (algebraMap 𝔬 Fv) (NF.Qp v Q₀), Tamagawa.map_Qp_eq,
    QuadForm.hessian_map (algebraMap F Fv) (Q₀.map (algebraMap (𝓞 F) F))]

theorem gramOf_eq_hessV (Q₀ : QuadForm (𝓞 F) n) :
    gramOf v (NF.Qp v Q₀) = (1 / 2 : Fv) • hessV v Q₀ := by
  rw [hessV_eq]; rfl

theorem det_hessV_ne_zero (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) : (hessV v Q₀).det ≠ 0 := by
  rw [hessV_eq]
  exact Tamagawa.det_map_ne_zero v (NF.nondegenerate_Qp v hQ)

theorem gramOf_transpose (Q : QuadForm 𝔬 n) : (gramOf v Q)ᵀ = gramOf v Q := by
  ext i j
  simp [gramOf, QuadForm.hessian, add_comm]

theorem gramOf_det_ne_zero (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) : (gramOf v Q).det ≠ 0 := by
  unfold gramOf
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by simp)) (Tamagawa.det_map_ne_zero v hQ)

theorem gramOf_compMat (Qo : QuadForm 𝔬 n) (P : Matrix (Fin n) (Fin n) 𝔬) :
    gramOf v (Qo.compMat P) = (P.map (algebraMap 𝔬 Fv))ᵀ * gramOf v Qo * P.map (algebraMap 𝔬 Fv) := by
  unfold gramOf
  rw [QuadForm.hessian_compMat, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_smul,
    Matrix.smul_mul]

theorem det_sq_of_similitude (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (A : Matrix (Fin n) (Fin n) Fv)
    {ξ : Fv} (hA : Aᵀ * hessV v Q₀ * A = ξ • hessV v Q₀) : A.det ^ 2 = ξ ^ n := by
  have h := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at h
  have h0 := det_hessV_ne_zero v Q₀ hQ
  apply mul_right_cancel₀ h0
  linear_combination h

theorem norm_det_pow_of_similitude (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (A : Matrix (Fin n) (Fin n) Fv) {ξ : Fv} (hA : Aᵀ * hessV v Q₀ * A = ξ • hessV v Q₀) :
    ‖A.det‖ ^ (n + 1) = ‖ξ‖ ^ (n * (n + 1) / 2) := by
  have h := det_sq_of_similitude v Q₀ hQ A hA
  have h2 : ‖A.det‖ ^ 2 = ‖ξ‖ ^ n := by rw [← norm_pow, h, norm_pow]
  have h3 := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
  have h4 : n * (n + 1) / 2 * 2 = n * (n + 1) := by rw [mul_comm]; exact h3
  rw [← pow_mul, mul_comm, pow_mul, h2, ← pow_mul, ← pow_mul, h4]

theorem relRatio_KL_similitude (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (A : Matrix (Fin n) (Fin n) Fv)
    {ξ : Fv} (hξ : ξ ≠ 0) (hA : Aᵀ * hessV v Q₀ * A = ξ • hessV v Q₀)
    (P P' : Matrix (Fin n) (Fin n) 𝔬) (hP : P.det ≠ 0) (hP' : P'.det ≠ 0)
    (hPP : P'.map (algebraMap 𝔬 Fv) = A * P.map (algebraMap 𝔬 Fv)) :
    relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (locAct v (glOf v P' hP') (std v)))
        (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v)) =
      relRatio (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (locAct v (glOf v P hP) (std v)))
        (KL v ((NF.Qp v Q₀).map (algebraMap 𝔬 Fv)) (std v)) := by
  classical
  have hQo : (NF.Qp v Q₀).Nondegenerate := NF.nondegenerate_Qp v hQ
  have h1 := Tamagawa.alphaLaw_global v Q₀ hQ P hP
  have h2 := Tamagawa.alphaLaw_global v Q₀ hQ P' hP'
  unfold Tamagawa.AlphaLawAt at h1 h2
  have hpos := Tamagawa.localDensityForm_self_pos' v (NF.Qp v Q₀) hQo
  have hnP := Tamagawa.nondegenerate_compMat v hQo hP
  have hnP' := Tamagawa.nondegenerate_compMat v hQo hP'
  -- the Gram matrices
  have hφA : (A)ᵀ * gramOf v (NF.Qp v Q₀) * A = ξ • gramOf v (NF.Qp v Q₀) := by
    rw [gramOf_eq_hessV, Matrix.mul_smul, Matrix.smul_mul, hA, smul_comm]
  have hφ : gramOf v ((NF.Qp v Q₀).compMat P') = ξ • gramOf v ((NF.Qp v Q₀).compMat P) := by
    rw [gramOf_compMat, gramOf_compMat, hPP, Matrix.transpose_mul]
    calc (P.map (algebraMap 𝔬 Fv))ᵀ * Aᵀ * gramOf v (NF.Qp v Q₀) * (A * P.map (algebraMap 𝔬 Fv))
        = (P.map (algebraMap 𝔬 Fv))ᵀ * (Aᵀ * gramOf v (NF.Qp v Q₀) * A) * P.map (algebraMap 𝔬 Fv) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hφA, Matrix.mul_smul, Matrix.smul_mul]
  have hsm := hankeBeta_std_smul v (gramOf_transpose v ((NF.Qp v Q₀).compMat P))
    (gramOf_det_ne_zero v _ hnP) hξ
  rw [← hφ, hankeBeta_std_hessian v _ hnP, hankeBeta_std_hessian v _ hnP'] at hsm
  have hc : ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) ≠ 0 := pow_ne_zero _ (by simp)
  have hS : DVR.localDensityForm ((NF.Qp v Q₀).compMat P) ((NF.Qp v Q₀).compMat P) (NF.π v) =
      ‖ξ‖ ^ (n * (n + 1) / 2) * DVR.localDensityForm ((NF.Qp v Q₀).compMat P') ((NF.Qp v Q₀).compMat P')
        (NF.π v) := by
    unfold DVR.siegelDensity at hsm
    simp only [ite_true] at hsm
    apply mul_left_cancel₀ hc
    linear_combination 2 * hsm
  -- determinants
  have hdet : ∀ R : Matrix (Fin n) (Fin n) 𝔬, ((R.det : 𝔬) : Fv) = (R.map (algebraMap 𝔬 Fv)).det :=
    fun R => RingHom.map_det (algebraMap 𝔬 Fv) R
  have hd' : ‖((P'.det : 𝔬) : Fv)‖ ^ (n + 1) = ‖ξ‖ ^ (n * (n + 1) / 2) * ‖((P.det : 𝔬) : Fv)‖ ^ (n + 1) := by
    rw [hdet, hdet, hPP, Matrix.det_mul, norm_mul, mul_pow, norm_det_pow_of_similitude v Q₀ hQ A hA]
  refine mul_right_cancel₀ hpos.ne' ?_
  rw [h2, h1, hd', hS]
  ring

theorem exists_locAct_std_model' (M : Lat F n) : ∃ γ : GL (Fin n) Fv, loc v M.1 = locAct v γ (std v) := by
  obtain ⟨A, hA⟩ := Tamagawa.SiegelSpace.exists_isLocModel' v M
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap F Fv) A, ?_⟩
  rw [← hA.2, Lattices.latOf, loc_glImage, loc_intVec]

theorem stabLat_scalGL {G : Type*} [Group G] (ψ : G →* GL (Fin n) Fv) (k : ℤ)
    (Λ : Submodule 𝔬 (Fin n → Fv)) : stabLat v ψ (locAct v (scalGL v k) Λ) = stabLat v ψ Λ := by
  ext x
  show locAct v (ψ x) (locAct v (scalGL v k) Λ) = locAct v (scalGL v k) Λ ↔ locAct v (ψ x) Λ = Λ
  rw [← locAct_mul, ← scalGL_comm, locAct_mul, locAct_eq_iff, locAct_inv_locAct]

theorem exists_glOf_eq (g : GL (Fin n) Fv) (k : ℕ) (h : locAct v g (std v) ≤ ball v (-(k : ℤ))) :
    ∃ (P : Matrix (Fin n) (Fin n) 𝔬) (hP : P.det ≠ 0), glOf v P hP = scalGL v k * g := by
  have hle : ∀ i j, Valued.v ((scalGL v (k : ℤ) * g).val i j) ≤ 1 := by
    intro i j
    have hm : g.val *ᵥ Pi.single j 1 ∈ locAct v g (std v) := ⟨_, single_one_mem_std v j, rfl⟩
    have h1 := h hm i
    rw [mulVec_single_one] at h1
    have e : (scalGL v (k : ℤ) * g).val i j = unifV v ^ (k : ℤ) * g.val i j := by
      rw [Units.val_mul, scalGL_val]
      simp [Matrix.scalar_apply, Matrix.diagonal_mul]
    rw [e, map_mul, valued_unifV_zpow]
    calc WithZero.exp (-(k : ℤ)) * Valued.v (g.val i j) ≤ WithZero.exp (-(k : ℤ)) * WithZero.exp (-(-(k : ℤ))) :=
          mul_le_mul_right h1 _
      _ = 1 := by rw [← WithZero.exp_add]; simp
  set P : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun i j => toO v _ (hle i j)
  have hPm : P.map (algebraMap 𝔬 Fv) = (scalGL v (k : ℤ) * g).val := by ext i j; rfl
  have hP : P.det ≠ 0 := by
    intro h0
    have h1 : (P.map (algebraMap 𝔬 Fv)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hPm] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (scalGL v (k : ℤ) * g).isUnit).ne_zero h1
  exact ⟨P, hP, Units.ext (by rw [glOf_val, hPm])⟩

theorem mem_map_stabLat (G : Subgroup (GL (Fin n) Fv)) (Λ : Submodule 𝔬 (Fin n → Fv)) (g : GL (Fin n) Fv) :
    g ∈ (stabLat v G.subtype Λ).map G.subtype ↔ g ∈ G ∧ locAct v g Λ = Λ := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨g, h1⟩, h2, rfl⟩

theorem commens_trans' {G : Type*} [Group G] {A B C : Subgroup G} (h1 : Tamagawa.Commens A B)
    (h2 : Tamagawa.Commens B C) : Tamagawa.Commens A C := by
  have key : ∀ {A B : Subgroup G}, Tamagawa.Commens A B → A.Commensurable B := fun h =>
    ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr h.2, Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr h.1⟩
  have := Subgroup.Commensurable.trans (key h1) (key h2)
  exact ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp this.2,
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp this.1⟩

/-- A similitude normalizes the orthogonal group. -/
theorem orth_conj_iff (Q₀ : QuadForm (𝓞 F) n) (α : GL (Fin n) Fv) {ξ : Fv} (hξ : ξ ≠ 0)
    (hα : α.valᵀ * hessV v Q₀ * α.val = ξ • hessV v Q₀) (g : GL (Fin n) Fv) :
    g ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv ↔
      α⁻¹ * g * α ∈ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv := by
  show g.valᵀ * hessV v Q₀ * g.val = hessV v Q₀ ↔
    (α⁻¹ * g * α).valᵀ * hessV v Q₀ * (α⁻¹ * g * α).val = hessV v Q₀
  have h1 : α.val * (α⁻¹).val = 1 := Units.mul_inv α
  have h2 : (α⁻¹).val * α.val = 1 := Units.inv_mul α
  have e1 : (α⁻¹).valᵀ * α.valᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : ∀ M : Matrix (Fin n) (Fin n) Fv, (α⁻¹).valᵀ * (α.valᵀ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  have h4 : ∀ M : Matrix (Fin n) (Fin n) Fv, α.val * ((α⁻¹).val * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have K : ξ • ((α⁻¹ * g * α).valᵀ * hessV v Q₀ * (α⁻¹ * g * α).val) =
      α.valᵀ * (g.valᵀ * hessV v Q₀ * g.val) * α.val := by
    have e : ξ • ((α⁻¹ * g * α).valᵀ * hessV v Q₀ * (α⁻¹ * g * α).val) =
        (α⁻¹ * g * α).valᵀ * (ξ • hessV v Q₀) * (α⁻¹ * g * α).val := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e, ← hα]
    simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, h3, h4]
  constructor
  · intro h
    rw [h, hα] at K
    exact smul_right_injective _ hξ K
  · intro h
    rw [h, ← hα] at K
    have := congrArg (fun M => (α⁻¹).valᵀ * M * (α⁻¹).val) K
    simp only [Matrix.mul_assoc, h3, h1, Matrix.mul_one] at this
    simpa [Matrix.mul_assoc] using this.symm

theorem map_conj_stabLat (Q₀ : QuadForm (𝓞 F) n) (α : GL (Fin n) Fv) {ξ : Fv} (hξ : ξ ≠ 0)
    (hα : α.valᵀ * hessV v Q₀ * α.val = ξ • hessV v Q₀) (Λ : Submodule 𝔬 (Fin n → Fv)) :
    ((stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype Λ).map
        (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype).map (MulAut.conj α).toMonoidHom =
      (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype (locAct v α Λ)).map
        (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype := by
  ext g
  rw [Subgroup.mem_map_equiv (f := MulAut.conj α), MulAut.conj_symm_apply, mem_map_stabLat, mem_map_stabLat,
    ← orth_conj_iff v Q₀ α hξ hα g]
  refine and_congr_right fun _ => ?_
  rw [locAct_mul, locAct_mul, locAct_eq_iff, inv_inv]

end Aux

/-- **Lemma 6.2 for lattice stabilizers**: $r(O(\alpha L_\mathfrak p), O(L_\mathfrak p)) = 1$ for a similitude $\alpha$ of $\varphi_\mathfrak p$
(stabilizers in $O(V_\mathfrak p)$ = `orthGroup`). -/
theorem relRatio_stabLat_similitude (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (α : GL (Fin n) Fv) {ξ : Fv}
    (hξ : ξ ≠ 0) (hα : α.valᵀ * hessV v Q₀ * α.val = ξ • hessV v Q₀) (M : Lat F n) :
    relRatio
      (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype (locAct v α (loc v M.1)))
      (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype (loc v M.1)) = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := exists_locAct_std_model' v M
  have hΛ : (loc v M.1).IsLattice Fv := loc_isLattice v M.2
  have hαΛ : (locAct v α (loc v M.1)).IsLattice Fv := locAct_isLattice _ hΛ
  obtain ⟨k₁, -, hk₁⟩ := exists_local_bounds v hΛ
  obtain ⟨k₂, -, hk₂⟩ := exists_local_bounds v hαΛ
  have b1 : locAct v γ (std v) ≤ ball v (-((max k₁ k₂ : ℕ) : ℤ)) := by
    rw [← hγ]; exact hk₁.trans (ball_anti v (by simp))
  have b2 : locAct v (α * γ) (std v) ≤ ball v (-((max k₁ k₂ : ℕ) : ℤ)) := by
    rw [locAct_mul, ← hγ]; exact hk₂.trans (ball_anti v (by simp))
  obtain ⟨P, hP, hPe⟩ := exists_glOf_eq v γ (max k₁ k₂) b1
  obtain ⟨P', hP', hPe'⟩ := exists_glOf_eq v (α * γ) (max k₁ k₂) b2
  have hPP : P'.map (algebraMap 𝔬 Fv) = α.val * P.map (algebraMap 𝔬 Fv) := by
    rw [← glOf_val v P' hP', ← glOf_val v P hP, hPe, hPe', ← Units.val_mul, ← mul_assoc, ← mul_assoc,
      scalGL_comm v ((max k₁ k₂ : ℕ) : ℤ) α]
  have key := relRatio_KL_similitude v Q₀ hQ α.val hξ hα P P' hP hP' hPP
  set ψ := (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype with hψ
  have hSP : stabLat v ψ (locAct v (glOf v P hP) (std v)) = stabLat v ψ (loc v M.1) := by
    rw [hPe, locAct_mul, ← hγ, stabLat_scalGL]
  have hSP' : stabLat v ψ (locAct v (glOf v P' hP') (std v)) = stabLat v ψ (locAct v α (loc v M.1)) := by
    rw [hPe', locAct_mul, locAct_mul, ← hγ, stabLat_scalGL]
  have e1 : relRatio (stabLat v ψ (locAct v α (loc v M.1))) (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) =
      relRatio (stabLat v ψ (loc v M.1)) (stdStab (Q₀.map (algebraMap (𝓞 F) F)) v) := by
    rw [← hSP', ← hSP, Tamagawa.LatChange.relRatio_stab_eq_KL, Tamagawa.LatChange.relRatio_stab_eq_KL]
    exact key
  rw [Tamagawa.stdStab_eq_stabLat] at e1
  have hc1 := commens_stabLat v ψ hαΛ hΛ
  have hc2 := commens_stabLat v ψ hΛ (std_isLattice v)
  have hc3 := commens_stabLat v ψ hαΛ (std_isLattice v)
  have hm := relRatio_mul hc1 hc2 hc3
  have hpos := relRatio_pos hc2
  rw [e1] at hm
  have : relRatio (stabLat v ψ (locAct v α (loc v M.1))) (stabLat v ψ (loc v M.1)) *
      relRatio (stabLat v ψ (loc v M.1)) (stabLat v ψ (std v)) = 1 *
      relRatio (stabLat v ψ (loc v M.1)) (stabLat v ψ (std v)) := by rw [hm, one_mul]
  exact mul_right_cancel₀ hpos.ne' this

/-- **Lemma 6.2** (Hanke thesis, p. 20): for a similitude $\alpha$ of $\varphi_\mathfrak p$ and an open compact subgroup $D$ of
$O(V_\mathfrak p)$ (here: a subgroup of `orthGroup` commensurable with $O(\mathfrak o_\mathfrak p^n)$),
$\mathrm{vol}(\alpha D\alpha^{-1}) = \mathrm{vol}(D)$, i.e. $r(\alpha D\alpha^{-1}, D) = 1$ (conjugation computed in
$\mathrm{GL}_n(F_\mathfrak p)$). -/
@[kb "hanke2005crelle" "Lemma 6.2, p. 20"]
theorem relRatio_conj_similitude (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (α : GL (Fin n) Fv) {ξ : Fv}
    (hξ : ξ ≠ 0) (hα : α.valᵀ * hessV v Q₀ * α.val = ξ • hessV v Q₀) (D : Subgroup (GL (Fin n) Fv))
    (hD : D ≤ orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv)
    (hcomm : D.Commensurable
      ((stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype (std v)).map
        (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv).subtype)) :
    relRatio (D.map (MulAut.conj α).toMonoidHom) D = 1 := by
  classical
  set G := orthGroup (Q₀.map (algebraMap (𝓞 F) F)) Fv with hG
  set K := (stabLat v G.subtype (std v)).map G.subtype with hK
  set c := (MulAut.conj α).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj α).injective
  have hC1 : K.map c = (stabLat v G.subtype (locAct v α (std v))).map G.subtype :=
    map_conj_stabLat v Q₀ α hξ hα (std v)
  have hDK : Tamagawa.Commens D K := ⟨Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hcomm.2,
    Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hcomm.1⟩
  have hKaK : Tamagawa.Commens (K.map c) K := by
    rw [hC1]
    exact Tamagawa.Commens.map (Subgroup.subtype_injective G)
      (commens_stabLat v G.subtype (locAct_isLattice _ (std_isLattice v)) (std_isLattice v))
  have hDaKa : Tamagawa.Commens (D.map c) (K.map c) := hDK.map hcinj
  have hKaD : Tamagawa.Commens (K.map c) D := commens_trans' hKaK hDK.symm
  have hDaD : Tamagawa.Commens (D.map c) D := commens_trans' hDaKa hKaD
  have e1 := relRatio_mul hDaKa hKaD hDaD
  have e2 := relRatio_mul hKaK hDK.symm hKaD
  have e3 : relRatio (D.map c) (K.map c) = relRatio D K := relRatio_map hcinj D K
  have e4 : relRatio (K.map c) K = 1 := by
    rw [hC1, hK, relRatio_map (Subgroup.subtype_injective G)]
    have := relRatio_stabLat_similitude v Q₀ hQ α hξ hα (stdLat F n)
    rwa [Tamagawa.loc_stdLat] at this
  have e5 : relRatio D K = (relRatio K D)⁻¹ := Tamagawa.LatChange.relRatio_symm' K D
  have hpos : 0 < relRatio K D := relRatio_pos hDK.symm
  rw [← e1, e3, ← e2, e4, e5, one_mul, inv_mul_cancel₀ hpos.ne']

end Local

end QuadFormsKB.Hanke2005
