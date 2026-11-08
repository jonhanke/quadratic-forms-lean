/-
# Watson (1963), Lemma 14 at $q = 2$: the named input `WatsonPhi4SplitTwo` is proved

See `Phi4Two.lean` for the argument. `phi4_split_two`, `watsonPhi4SplitTwo_holds`.
-/
import QuadFormsKB.Literature.Watson1963.Phi4Two

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms QuadFormsKB.Hanke2011Structure

/-- Helper: entries of $M^{\mathsf T} A$ as pairings. -/
theorem transpose_mul_apply' {n v : ℕ} (M : Matrix (Fin n) (Fin v) ℤ_[2]) (A : Matrix (Fin n) (Fin n) ℤ_[2])
    (i : Fin v) (r : Fin n) : (Mᵀ * A) i r = (M *ᵥ Pi.single i 1) ⬝ᵥ (A *ᵥ Pi.single r 1) := by
  rw [mulVec_single_one, mulVec_single_one]
  simp [Matrix.mul_apply, dotProduct, Matrix.transpose_apply, Matrix.col]

/-- Helper: $(X^{\mathsf T} C W)_{ab} = (Xe_a)^{\mathsf T} C (We_b)$. -/
theorem transpose_mul_mul_apply' {n a b : ℕ} (C : Matrix (Fin n) (Fin n) ℤ_[2]) (X : Matrix (Fin n) (Fin a) ℤ_[2])
    (W : Matrix (Fin n) (Fin b) ℤ_[2]) (i : Fin a) (j : Fin b) :
    (Xᵀ * C * W) i j = (X *ᵥ Pi.single i 1) ⬝ᵥ (C *ᵥ (W *ᵥ Pi.single j 1)) := by
  have hX : X *ᵥ Pi.single i 1 = fun l => X l i := by ext l; simp [mulVec, dotProduct, Pi.single_apply]
  have hW : W *ᵥ Pi.single j 1 = fun l => W l j := by ext l; simp [mulVec, dotProduct, Pi.single_apply]
  rw [hX, hW]
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **$D_4$ as $A_2 \perp 2A_2$ over $\mathbb Z_2$, as an isometry of base changes.** -/
theorem isometricGL_phiD3 :
    IsometricGL (n := 2 + 2) ((phiD 3).map (Int.castRingHom ℤ_[2]))
      (QuadForm.orthSum ((phiA 2).map (Int.castRingHom ℤ_[2])) ((2 : ℤ_[2]) • (quadA : QuadForm ℤ_[2] 2))) := by
  obtain ⟨T, hT, hdec⟩ := phiD3_decomp
  set Tq := T.map (Int.castRingHom ℤ_[2])
  have hTq : IsUnit Tq.det := by
    have : Tq.det = ((T.det : ℤ) : ℤ_[2]) := (RingHom.map_det (Int.castRingHom ℤ_[2]) T).symm
    rw [this]; exact isUnit_of_odd hT
  refine ⟨Matrix.nonsingInvUnit Tq hTq, fun z => ?_⟩
  show ((phiD 3).map _).eval (Tq *ᵥ z) = _
  rw [← QuadForm.eval_compMat, QuadForm.map_compMat, hdec, eval_map_orthSum]
  show (QuadForm.orthSum _ _).evalIn ℤ_[2] z = (QuadForm.orthSum _ _).evalIn ℤ_[2] z
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum]
  congr 1
  show (((2 : ℤ) • (quadA : QuadForm ℤ 2)).map _).eval _ = ((2 : ℤ_[2]) • quadA).eval _
  rw [eval_map_padic, evalIn_smul_form, eval_smul_form', ← eval_map_padic, quadA_map]
  push_cast; rfl

/-- **Watson 1963, Lemma 14 at $q = 2$** (see `Phi4Two.lean`): a Watson-minimal positive definite form $f$ in
$4 + m$ variables, $m \ge 8$, with $r_2(f) \le 9$, splits off $\Phi_4$ over $\mathbb Z_2$. -/
@[kb "watson1963" "§9, Lemma 14 with q = 2 (Φ₄ splits off over ℤ₂), pp. 560, 565"]
theorem phi4_split_two {m : ℕ} {f : QuadForm ℤ (4 + m)} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hm : 8 ≤ m) (hr : rankModP 2 f ≤ 9) :
    ∃ ψp : QuadForm ℤ_[2] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[2])) (QuadForm.orthSum ((phiD 3).map (Int.castRingHom ℤ_[2])) ψp) := by
  classical
  obtain ⟨k, m', hm', H, K, hH, horth, hspan, huniq, hpsi, h2k, hr1, hrev⟩ := exists_decomp_two f
  have h6 := IsWatsonMinimal.le_two_mul_rankModP 2 hf hmin
  set F := f.map (Int.castRingHom ℤ_[2]) with hF
  set U := F.compMat H with hUdef
  set ψ := F.compMat K with hψdef
  have hU : IsUnit U.hessian.det := by rw [hUdef, QuadForm.hessian_compMat]; exact hH
  have hSF : SqFreePsi ψ :=
    sqFreePsi_of_decomp F (IsWatsonMinimal.sqFree2 hf hmin) H K hH horth hspan huniq hpsi
  have hψ : ∀ c, F.eval (K *ᵥ c) = ψ.eval c := fun c => (QuadForm.eval_compMat F K c).symm
  -- A₂ in U
  obtain ⟨H₁, hH₁⟩ := exists_rep_unimod' U ((phiA 2).map (Int.castRingHom ℤ_[2])) hU
    (isUnit_map_det _ (not_two_dvd_phiA_det 2 (by decide))) ⟨k, by ring⟩ (by decide) (by omega)
  set MA := H * H₁
  have hMA : ∀ y, F.eval (MA *ᵥ y) = ((phiA 2).map (Int.castRingHom ℤ_[2])).eval y := fun y => by
    rw [← mulVec_mulVec, ← hH₁, hUdef, QuadForm.eval_compMat]
  -- 2A in ψ
  obtain ⟨x, y, ⟨a, hxa, ha⟩, ⟨a', hya, ha'⟩, ⟨b, hxyb, hb⟩⟩ := psi_exists_anisotropic_pair ψ hpsi hSF (by omega)
  obtain ⟨g, hg⟩ := (isometricGL_bq_hypA ha hb ha').trans isometricGL_quadA_hypA.symm
  set X : Matrix (Fin m') (Fin 2) ℤ_[2] := Matrix.of fun r i => (![x, y] i) r
  have hX : ∀ w, X *ᵥ w = w 0 • x + w 1 • y := fun w => by
    ext r; simp [X, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  set M2 := K * X * g.val
  have hM2 : ∀ z, F.eval (M2 *ᵥ z) = ((2 : ℤ_[2]) • (quadA : QuadForm ℤ_[2] 2)).eval z := fun z => by
    rw [eval_smul_form', ← hg z, ← mulVec_mulVec, ← mulVec_mulVec, hψ, hX]
    set w := g.val *ᵥ z
    have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    rw [hw, Composition.bq_eval]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hp := QuadForm.eval_polar ψ (w 0 • x) (w 1 • y)
    rw [eval_smul_sq, eval_smul_sq, mulVec_smul, dotProduct_smul, smul_dotProduct, hxyb, hxa, hya] at hp
    simp only [smul_eq_mul] at hp
    linear_combination hp
  have hM2K : ∀ z, ∃ c, M2 *ᵥ z = K *ᵥ c := fun z => ⟨X *ᵥ (g.val *ᵥ z), by
    rw [← mulVec_mulVec, ← mulVec_mulVec]⟩
  have horthA : ∀ y' z, (MA *ᵥ y') ⬝ᵥ (F.hessian *ᵥ (M2 *ᵥ z)) = 0 := fun y' z => by
    obtain ⟨c, hc⟩ := hM2K z
    rw [hc, ← mulVec_mulVec]; exact horth _ c
  -- pairings with M2 are even
  have hev2 : ∀ z w, (2 : ℤ_[2]) ∣ (M2 *ᵥ z) ⬝ᵥ (F.hessian *ᵥ w) := fun z w => by
    obtain ⟨c, hc⟩ := hM2K z
    obtain ⟨a₀, c₀, rfl⟩ := hspan w
    rw [hc, mulVec_add, dotProduct_add, dot_symm F (K *ᵥ c) (H *ᵥ a₀), horth, zero_add, dot_compMat]
    exact dot_even ψ hpsi c c₀
  -- the left inverse
  set GA := MAᵀ * F.hessian * MA with hGA
  have hGAu : IsUnit GA.det := by
    have : F.compMat MA = (phiA 2).map (Int.castRingHom ℤ_[2]) :=
      QuadForm.eq_of_eval_eq fun z => by rw [QuadForm.eval_compMat, hMA]
    rw [hGA, ← QuadForm.hessian_compMat, this]
    exact isUnit_map_det _ (not_two_dvd_phiA_det 2 (by decide))
  set LA := GA⁻¹ * (MAᵀ * F.hessian)
  have hP : ∀ i r, (2 : ℤ_[2]) ∣ (M2ᵀ * F.hessian) i r := fun i r => by
    rw [transpose_mul_apply']; exact hev2 _ _
  choose P' hP' using hP
  set Pm : Matrix (Fin 2) (Fin (4 + m)) ℤ_[2] := Matrix.of P'
  have hPm : M2ᵀ * F.hessian = (2 : ℤ_[2]) • Pm := Matrix.ext fun i r => by rw [hP' i r]; rfl
  set Hq := (quadA : QuadForm ℤ_[2] 2).hessian
  have hHq : IsUnit Hq.det := by rw [hessian_det_quadA]; exact QuadFormsKB.Cassels.dyadic_isUnit_three
  have hcancel : ∀ {A B : Matrix (Fin 2) (Fin 2) ℤ_[2]}, (2 : ℤ_[2]) • A = (2 : ℤ_[2]) • B → A = B := by
    intro A B h
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (show (2 : ℤ_[2]) ≠ 0 by norm_num) this
  have hG2 : Pm * M2 = Hq := by
    apply hcancel
    rw [← Matrix.smul_mul, ← hPm, ← QuadForm.hessian_compMat]
    have : F.compMat M2 = (2 : ℤ_[2]) • (quadA : QuadForm ℤ_[2] 2) :=
      QuadForm.eq_of_eval_eq fun z => by rw [QuadForm.eval_compMat, hM2]
    rw [this, hessian_smul']
  have hcross : MAᵀ * F.hessian * M2 = 0 := by
    refine Matrix.ext fun i j => ?_
    rw [transpose_mul_mul_apply', horthA]; rfl
  have hPA : Pm * MA = 0 := by
    have h2 : (2 : ℤ_[2]) • (Pm * MA) = 0 := by
      rw [← Matrix.smul_mul, ← hPm]
      have : M2ᵀ * F.hessian * MA = (MAᵀ * F.hessian * M2)ᵀ := by
        rw [Matrix.transpose_mul (MAᵀ * F.hessian) M2, Matrix.transpose_mul MAᵀ F.hessian,
          Matrix.transpose_transpose, hessian_isSymm', Matrix.mul_assoc]
      rw [this, hcross, Matrix.transpose_zero]
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this ⊢
    exact (mul_eq_zero.1 this).resolve_left (show (2 : ℤ_[2]) ≠ 0 by norm_num)
  set L2 := Hq⁻¹ * Pm
  set M := appendCols MA M2
  set L : Matrix (Fin (2 + 2)) (Fin (4 + m)) ℤ_[2] :=
    Matrix.of fun i r => Fin.append (fun a => LA a r) (fun b => L2 b r) i
  have hLAA : LA * MA = 1 := by
    simp only [LA, Matrix.mul_assoc]; rw [← Matrix.mul_assoc MAᵀ, ← hGA, Matrix.nonsing_inv_mul _ hGAu]
  have hLA2 : LA * M2 = 0 := by
    simp only [LA, Matrix.mul_assoc]; rw [← Matrix.mul_assoc MAᵀ, hcross, Matrix.mul_zero]
  have hL2A : L2 * MA = 0 := by simp only [L2, Matrix.mul_assoc]; rw [hPA, Matrix.mul_zero]
  have hL22 : L2 * M2 = 1 := by simp only [L2, Matrix.mul_assoc]; rw [hG2, Matrix.nonsing_inv_mul _ hHq]
  have hne : ∀ (a c : Fin 2), (Fin.castAdd 2 a : Fin (2 + 2)) ≠ Fin.natAdd 2 c := fun a c h => by
    have := congrArg Fin.val h; simp at this; omega
  have hLM : L * M = 1 := by
    refine Matrix.ext fun i j => ?_
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun c => ?_) (fun c => ?_) j
    · have := congrFun (congrFun hLAA a) c
      simp only [Matrix.mul_apply] at this ⊢
      simp only [L, M, appendCols, Matrix.of_apply, Fin.append_left, Matrix.one_apply, Fin.castAdd_inj]
      exact this
    · have := congrFun (congrFun hLA2 a) c
      simp only [Matrix.mul_apply] at this ⊢
      simp only [L, M, appendCols, Matrix.of_apply, Fin.append_left, Fin.append_right, Matrix.one_apply, hne a c,
        if_false]
      exact this
    · have := congrFun (congrFun hL2A a) c
      simp only [Matrix.mul_apply] at this ⊢
      simp only [L, M, appendCols, Matrix.of_apply, Fin.append_left, Fin.append_right, Matrix.one_apply,
        (hne c a).symm, if_false]
      exact this
    · have := congrFun (congrFun hL22 a) c
      simp only [Matrix.mul_apply] at this ⊢
      simp only [L, M, appendCols, Matrix.of_apply, Fin.append_right, Matrix.one_apply, Fin.natAdd_inj]
      exact this
  have horthL : ∀ k', L *ᵥ k' = 0 → Mᵀ *ᵥ (F.hessian *ᵥ k') = 0 := by
    intro k' hk'
    have hA : LA *ᵥ k' = 0 := funext fun a => by
      have := congrFun hk' (Fin.castAdd 2 a)
      simp only [L, mulVec, dotProduct, Matrix.of_apply, Fin.append_left, Pi.zero_apply] at this
      exact this
    have h2 : L2 *ᵥ k' = 0 := funext fun a => by
      have := congrFun hk' (Fin.natAdd 2 a)
      simp only [L, mulVec, dotProduct, Matrix.of_apply, Fin.append_right, Pi.zero_apply] at this
      exact this
    have hA' : MAᵀ *ᵥ (F.hessian *ᵥ k') = 0 := by
      have : MAᵀ * F.hessian = GA * LA := by
        simp only [LA]; rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGAu, Matrix.one_mul]
      rw [mulVec_mulVec, this, ← mulVec_mulVec, hA, mulVec_zero]
    have h2' : M2ᵀ *ᵥ (F.hessian *ᵥ k') = 0 := by
      have : M2ᵀ * F.hessian = (2 : ℤ_[2]) • (Hq * L2) := by
        simp only [L2]; rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hHq, Matrix.one_mul, hPm]
      rw [mulVec_mulVec, this, Matrix.smul_mulVec, ← mulVec_mulVec, h2, mulVec_zero, smul_zero]
    funext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · have := congrFun hA' a
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      simp only [M, appendCols, Matrix.of_apply, Fin.append_left]
      exact this
    · have := congrFun h2' a
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      simp only [M, appendCols, Matrix.of_apply, Fin.append_right]
      exact this
  obtain ⟨m'', hm'', K', horth', hspan', -⟩ := exists_complement_of_left_inverse F.hessian M L hLM horthL
  have hMeval : ∀ z, F.eval (M *ᵥ z) = (QuadForm.orthSum ((phiA 2).map (Int.castRingHom ℤ_[2]))
      ((2 : ℤ_[2]) • (quadA : QuadForm ℤ_[2] 2))).eval z := by
    intro z
    rw [appendCols_mulVec]
    have hp := QuadForm.eval_polar F (MA *ᵥ fun i => z (Fin.castAdd 2 i)) (M2 *ᵥ fun i => z (Fin.natAdd 2 i))
    rw [horthA, hMA, hM2] at hp
    show _ = (QuadForm.orthSum _ _).evalIn ℤ_[2] z
    rw [QuadForm.evalIn_orthSum]
    show _ = QuadForm.eval _ _ + QuadForm.eval _ _
    linear_combination hp
  have hiso := isometricGL_of_complement hm'' M hMeval K' horth' hspan'
  obtain rfl : m'' = m := by omega
  refine ⟨F.compMat K', hiso.trans ?_⟩
  exact isometricGL_orthSum_of isometricGL_phiD3.symm (IsometricGL.refl _)

/-- **The named input `WatsonPhi4SplitTwo` holds** (`phi4_split_two`). -/
@[kb "watson1963" "§9, Lemma 14 at q = 2 (proof of WatsonPhi4SplitTwo)"]
theorem watsonPhi4SplitTwo_holds : WatsonPhi4SplitTwo :=
  ⟨fun _ _ hf hmin hm hr => phi4_split_two hf hmin hm hr⟩

end QuadFormsKB.Watson1963
