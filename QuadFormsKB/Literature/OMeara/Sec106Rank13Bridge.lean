/-
# O'Meara §106F, toward 106.r38: lattices on $I_n$ and their Gram forms

**Layer:** $V = \mathbb Q^n$ with $Q = x_0^2 + \dots + x_{n-1}^2$ (`Lattices.sumSqForm n`), lattices `glImage B intVec`
($B \in \mathrm{GL}_n(\mathbb Q)$, the lattice with basis the columns of $B$), integral forms `QuadForm ℤ n` with
$\mathrm{GL}_n(\mathbb Z)$-equivalence `Siegel.IntEquiv` and genus `Siegel.SameGenus`. A matrix $B$ is a basis of a
lattice with *Gram form* $R$ when $\sum_i (Bx)_i^2 = R(x)$ for all $x \in \mathbb Q^n$. Indices are 0-based.

**Proves** (all unconditional)
* `isUnimodularZ_glImage_of_gram`: the lattice $B\mathbb Z^n$ is unimodular when its Gram form has an even Hessian of
  determinant $2^n$ (the argument of `Siegel.isUnimodularZ_glImage_of_sameGenus`, with the genus hypothesis replaced by
  these two properties).
* `intEquiv_of_isIsometric_glImage`: if $\sigma B\mathbb Z^n = g\mathbb Z^n$ for a rational isometry $\sigma$, then the
  Gram forms of $B$ and $g$ are integrally equivalent.
* `isIsometric_glImage_of_intEquiv`: conversely, integrally equivalent Gram forms give isometric lattices.
* `isProperIsometric_of_isIsometric_swap`: an isometry $L \to M$ may be taken proper when $L$ is stable under the
  transposition of the coordinates $x_0, x_1$ ($n \ge 2$).
-/
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel

variable {n : ℕ}

/-- $\sum_i (Bx)_i^2$ is the value of `sumSqForm n` at $Bx$. -/
theorem evalIn_sumSq_eq_sumSqForm (x : Fin n → ℚ) :
    (sumSq n).evalIn ℚ x = (sumSqForm n).evalIn ℚ x := by
  rw [evalIn_sumSq, evalIn_sumSqForm]

/-- **A lattice with an even unimodular Gram form is unimodular.** Let $B \in \mathrm{GL}_n(\mathbb Q)$ and let $R$ be an
integral form with $\sum_i (Bx)_i^2 = R(x)$ (`hB`), whose Hessian has even entries (`hev`) and determinant $2^n$
(`hdet`, stated as equality with the Hessian determinant of $I_n$). Then $B\mathbb Z^n$ is unimodular on $I_n$. -/
theorem isUnimodularZ_glImage_of_gram {R : QuadForm ℤ n} (B : GL (Fin n) ℚ)
    (hB : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (B.val *ᵥ x) = R.evalIn ℚ x)
    (hev : ∀ i j, 2 ∣ R.hessian i j) (hdet : (sumSq n).hessian.det = R.hessian.det) :
    IsUnimodularZ (sumSqForm n) (glImage B intVec) := by
  have hH := Kneser.hessian_eq_conj (Q := sumSq n) (g := B.val) (fun x => (hB x).symm)
  rw [hessian_sumSq] at hH
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => R.hessian i j / 2
  have hG2 : ∀ i j, 2 * G i j = R.hessian i j := fun i j => Int.mul_ediv_cancel' (hev i j)
  have e3 : (((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (algebraMap ℤ ℚ)) =
      (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hH
  have hGq : G.map (Int.castRingHom ℚ) = B.val.transpose * B.val := by
    ext i j
    have e1 := congrFun (congrFun hH i) j
    have e2 : (R.hessian i j : ℚ) = 2 * (G i j : ℚ) := by exact_mod_cast (hG2 i j).symm
    simp only [Matrix.map_apply, eq_intCast, Matrix.smul_apply, smul_eq_mul, algebraMap_int_eq] at e1 ⊢
    rw [e2] at e1
    linarith
  have hGH : R.hessian = (2 : ℤ) • G := by
    ext i j; simp [hG2]
  have hGdet : G.det = 1 := by
    have h1 := hdet
    rw [hessian_sumSq, hGH, Matrix.det_smul, Matrix.det_smul, Matrix.det_one] at h1
    have h2 : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    simpa [h2] using h1.symm
  have hdotQ : ∀ v v' : Fin n → ℚ,
      (B.val *ᵥ v) ⬝ᵥ (B.val *ᵥ v') = ((G.map (Int.castRingHom ℚ)) *ᵥ v) ⬝ᵥ v' := by
    intro v v'
    rw [hGq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hdot : ∀ y y' : Fin n → ℤ,
      (B.val *ᵥ (fun i => (y i : ℚ))) ⬝ᵥ (B.val *ᵥ (fun i => (y' i : ℚ))) = (((G *ᵥ y) ⬝ᵥ y' : ℤ) : ℚ) := by
    intro y y'
    rw [hdotQ]
    simp [dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hint : ∀ {v : Fin n → ℚ}, v ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) →
      ∃ z : Fin n → ℤ, v = fun i => (z i : ℚ) := by
    intro v hv
    choose z hz using mem_intVec_int.mp hv
    exact ⟨z, funext hz⟩
  unfold IsUnimodularZ
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ glImage B intVec, ∃ m : ℤ, bil (sumSqForm n) x y / 2 = m := hx
    set w : Fin n → ℚ := B⁻¹.val *ᵥ x with hw
    have hxw : B.val *ᵥ w = x := by
      rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcol : ∀ j, ∃ m : ℤ, ((G.map (Int.castRingHom ℚ)) *ᵥ w) j = m := by
      intro j
      have hej : (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
        rw [mem_intVec_int]
        intro i
        by_cases hij : i = j
        · exact ⟨1, by simp [hij]⟩
        · exact ⟨0, by simp [hij]⟩
      obtain ⟨m, hm⟩ := hx' _ (mulVec_mem_glImage (γ := B) hej)
      refine ⟨m, ?_⟩
      rw [DefiniteForms.bil_sumSq, ← hxw, hdotQ, dotProduct_single_one] at hm
      linarith
    choose m hm using hcol
    have hwint : ∀ i, ∃ k : ℤ, w i = k := by
      intro i
      have e : (G.adjugate.map (Int.castRingHom ℚ)) *ᵥ ((G.map (Int.castRingHom ℚ)) *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul, hGdet, one_smul,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
      refine ⟨∑ j, G.adjugate i j * m j, ?_⟩
      have hmv : (G.map (Int.castRingHom ℚ)) *ᵥ w = fun j => (m j : ℚ) := funext hm
      rw [hmv] at e
      rw [← congrFun e i]
      simp [Matrix.mulVec, dotProduct]
    exact ⟨w, mem_intVec_int.mpr hwint, hxw⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_glImage.mp hx
    obtain ⟨z, rfl⟩ := hint hy
    intro y' hy'
    obtain ⟨v, hv, rfl⟩ := mem_glImage.mp hy'
    obtain ⟨z', rfl⟩ := hint hv
    refine ⟨(G *ᵥ z) ⬝ᵥ z', ?_⟩
    rw [DefiniteForms.bil_sumSq, hdot]
    ring

/-- An element $V \in \mathrm{GL}_n(\mathbb Q)$ with $V\mathbb Z^n = \mathbb Z^n$ has integral entries. -/
theorem exists_int_of_glImage_intVec (V : GL (Fin n) ℚ) (hV : glImage V intVec = intVec) :
    ∃ A : Matrix (Fin n) (Fin n) ℤ, A.map (Int.castRingHom ℚ) = V.val := by
  have : ∀ i j, ∃ m : ℤ, V.val i j = m := by
    intro i j
    have hej : (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
      rw [mem_intVec_int]
      intro k
      by_cases hkj : k = j
      · exact ⟨1, by simp [hkj]⟩
      · exact ⟨0, by simp [hkj]⟩
    have := mem_intVec_int.mp (hV ▸ mulVec_mem_glImage (γ := V) hej) i
    simpa [Matrix.mulVec_single_one] using this
  choose A hA using this
  exact ⟨Matrix.of A, by ext i j; simp [hA]⟩

/-- An element $U \in \mathrm{GL}_n(\mathbb Q)$ with $U\mathbb Z^n = \mathbb Z^n$ comes from $\mathrm{GL}_n(\mathbb Z)$. -/
theorem exists_glZ_of_glImage_intVec (U : GL (Fin n) ℚ) (hU : glImage U intVec = intVec) :
    ∃ A : GL (Fin n) ℤ, A.val.map (Int.castRingHom ℚ) = U.val := by
  have hU2 : glImage U⁻¹ intVec = intVec := by
    conv_lhs => rw [← hU]
    rw [← glImage_mul, inv_mul_cancel, glImage_one]
  obtain ⟨A, hA⟩ := exists_int_of_glImage_intVec U hU
  obtain ⟨B, hB⟩ := exists_int_of_glImage_intVec U⁻¹ hU2
  have hAB : A * B = 1 := by
    have h : (A * B).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective h
  have hBA : B * A = 1 := by
    have h : (B * A).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_mul, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective h
  exact ⟨⟨A, B, hAB, hBA⟩, hA⟩

/-- **Isometric lattices have integrally equivalent Gram forms.** Let $B$, $g \in \mathrm{GL}_n(\mathbb Q)$ be bases with
Gram forms $R$ (`hB`) and $Q'$ (`hg`), and let $\sigma \in O(I_n)(\mathbb Q)$ (`hσ`) carry $B\mathbb Z^n$ onto $g\mathbb Z^n$
(`hL`). Then $R$ and $Q'$ are $\mathrm{GL}_n(\mathbb Z)$-equivalent (via $(\sigma B)^{-1}g$). -/
theorem intEquiv_of_isIsometric_glImage {R Q' : QuadForm ℤ n} (B g σ : GL (Fin n) ℚ)
    (hB : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (B.val *ᵥ x) = R.evalIn ℚ x)
    (hg : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x)
    (hσ : σ ∈ orthGroup (sumSqForm n) ℚ) (hL : glImage σ (glImage B intVec) = glImage g intVec) :
    IntEquiv R Q' := by
  set U : GL (Fin n) ℚ := (σ * B)⁻¹ * g with hU
  have hU1 : glImage U intVec = intVec := by
    rw [hU, glImage_mul, ← hL, ← glImage_mul, ← glImage_mul, mul_assoc, inv_mul_cancel, glImage_one]
  obtain ⟨A, hA⟩ := exists_glZ_of_glImage_intVec U hU1
  refine ⟨A, fun x => ?_⟩
  apply Int.cast_injective (α := ℚ)
  show ((R.eval (A.val *ᵥ x) : ℤ) : ℚ) = ((Q'.eval x : ℤ) : ℚ)
  rw [← evalIn_intCast, ← evalIn_intCast]
  have hv : (fun i => ((A.val *ᵥ x) i : ℚ)) = U.val *ᵥ (fun i => (x i : ℚ)) := by
    rw [← hA]
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [hv, ← hB, ← hg]
  have hBU : B.val *ᵥ (U.val *ᵥ fun i => (x i : ℚ)) = σ⁻¹.val *ᵥ (g.val *ᵥ fun i => (x i : ℚ)) := by
    rw [hU, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, _root_.mul_inv_rev,
      ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hBU]
  have hinv : σ⁻¹ ∈ orthGroup (sumSqForm n) ℚ := Subgroup.inv_mem _ hσ
  rw [evalIn_sumSq_eq_sumSqForm, evalIn_sumSq_eq_sumSqForm, evalIn_mulVec_of_mem (sumSqForm n) hinv]

/-- The Hessian of $I_n$ over $\mathbb Q$ is $2 \cdot 1$. -/
theorem hessian_sumSqForm : (sumSqForm n).hessian = (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [QuadForm.hessian, sumSqForm, QuadForm.diag]; norm_num
  · simp [QuadForm.hessian, sumSqForm, QuadForm.diag, hij]

/-- A rational matrix $\gamma$ with $\gamma^{\mathsf T}\gamma = 1$ is an isometry of $I_n$. -/
theorem mem_orthGroup_sumSqForm {γ : GL (Fin n) ℚ} (h : γ.valᵀ * γ.val = 1) :
    γ ∈ orthGroup (sumSqForm n) ℚ := by
  rw [mem_orthGroup]
  have hm : (sumSqForm n).hessian.map (algebraMap ℚ ℚ) = (2 : ℚ) • 1 := by
    rw [hessian_sumSqForm]; ext i j; simp [Matrix.one_apply]
  rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, h]

/-- The Gram matrix of a basis: if $\sum_i (Bx)_i^2 = R(x)$ then $H_R = 2B^{\mathsf T}B$ (over $\mathbb Q$). -/
theorem hessian_map_eq_of_gram {R : QuadForm ℤ n} (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (B *ᵥ x) = R.evalIn ℚ x) :
    R.hessian.map (algebraMap ℤ ℚ) = (2 : ℚ) • (Bᵀ * B) := by
  rw [Kneser.hessian_eq_conj (Q := sumSq n) (g := B) (fun x => (hB x).symm), hessian_sumSq]
  have e3 : (((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (algebraMap ℤ ℚ)) =
      (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **Integrally equivalent Gram forms give isometric lattices.** If $B$, $g$ are bases with Gram forms $R$, $Q'$ and
$R \sim_{\mathbb Z} Q'$, then $B\mathbb Z^n$ and $g\mathbb Z^n$ are isometric lattices on $I_n$. -/
theorem isIsometric_glImage_of_intEquiv {R Q' : QuadForm ℤ n} (B g : GL (Fin n) ℚ)
    (hB : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (B.val *ᵥ x) = R.evalIn ℚ x)
    (hg : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x) (h : IntEquiv R Q') :
    IsIsometric (sumSqForm n) (glImage B intVec) (glImage g intVec) := by
  obtain ⟨A, hA⟩ := h
  have hH := (Siegel.eval_mulVec_eq_iff_hessian R Q' A.val).mp hA
  let Aq : GL (Fin n) ℚ := Units.map (Int.castRingHom ℚ).mapMatrix.toMonoidHom A
  have hAq : Aq.val = A.val.map (Int.castRingHom ℚ) := rfl
  have hRB := hessian_map_eq_of_gram B.val hB
  have hQg := hessian_map_eq_of_gram g.val hg
  -- `(B A)ᵀ (B A) = gᵀ g`
  have hkey : (B * Aq).valᵀ * (B * Aq).val = g.valᵀ * g.val := by
    have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.map (algebraMap ℤ ℚ)) hH
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    rw [hRB, hQg] at h1
    have h2 : (2 : ℚ) • ((B * Aq).valᵀ * (B * Aq).val) = (2 : ℚ) • (g.valᵀ * g.val) := by
      rw [← h1, Units.val_mul, transpose_mul, hAq]
      simp only [algebraMap_int_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    exact smul_right_injective _ (two_ne_zero (α := ℚ)) h2
  set γ : GL (Fin n) ℚ := g * (B * Aq)⁻¹ with hγ
  have hγo : γ ∈ orthGroup (sumSqForm n) ℚ := by
    apply mem_orthGroup_sumSqForm
    have h1 : (B * Aq).val * ((B * Aq)⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc γ.valᵀ * γ.val = ((B * Aq)⁻¹).valᵀ * (g.valᵀ * g.val) * ((B * Aq)⁻¹).val := by
          rw [hγ, Units.val_mul, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = ((B * Aq).val * ((B * Aq)⁻¹).val)ᵀ * ((B * Aq).val * ((B * Aq)⁻¹).val) := by
          rw [← hkey, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, transpose_one, Matrix.one_mul]
  refine ⟨γ, hγo, ?_⟩
  have hAZ : glImage Aq⁻¹ intVec = intVec := by
    ext x
    rw [mem_glImage]
    have hAi : (Aq⁻¹).val = (A⁻¹ : GL (Fin n) ℤ).val.map (Int.castRingHom ℚ) := by
      rw [← map_inv]; rfl
    have hz : ∀ (M : GL (Fin n) ℤ) (z : Fin n → ℤ),
        M.val.map (Int.castRingHom ℚ) *ᵥ (fun i => (z i : ℚ)) = fun i => ((M.val *ᵥ z) i : ℚ) := by
      intro M z; funext i; simp [Matrix.mulVec, dotProduct]
    constructor
    · rintro ⟨y, hy, rfl⟩
      choose z hz' using mem_intVec_int.mp hy
      have hy' : y = fun i => (z i : ℚ) := funext hz'
      rw [hy', hAi, hz, mem_intVec_int]
      exact fun i => ⟨_, rfl⟩
    · intro hx
      choose z hz' using mem_intVec_int.mp hx
      refine ⟨fun i => ((A.val *ᵥ z) i : ℚ), mem_intVec_int.mpr fun i => ⟨_, rfl⟩, ?_⟩
      rw [hAi, hz, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact (funext hz').symm
  have e : γ * B = g * Aq⁻¹ := by rw [hγ, _root_.mul_inv_rev]; group
  rw [← glImage_mul, e, glImage_mul, hAZ]

/-- The transposition of the coordinates $x_0$ and $x_1$, as an element of $\mathrm{GL}_n(\mathbb Q)$ ($n \ge 2$). -/
def swapGL (hn : 2 ≤ n) : GL (Fin n) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).permMatrix ℚ) (by
    rw [Matrix.det_permutation, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
    norm_num)

theorem swapGL_val (hn : 2 ≤ n) :
    (swapGL hn).val = (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).permMatrix ℚ := rfl

theorem swapGL_det (hn : 2 ≤ n) : (swapGL hn).val.det = -1 := by
  rw [swapGL_val, Matrix.det_permutation, Equiv.Perm.sign_swap (by simp [Fin.ext_iff])]
  norm_num

theorem swapGL_mem (hn : 2 ≤ n) : swapGL hn ∈ orthGroup (sumSqForm n) ℚ := by
  apply mem_orthGroup_sumSqForm
  rw [swapGL_val, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, Equiv.swap_inv, Equiv.swap_mul_self,
    Matrix.permMatrix_one]

/-- An element of $O(I_n)(\mathbb Q)$ has determinant $\pm 1$. -/
theorem det_eq_one_or_neg_one_sumSqForm {γ : GL (Fin n) ℚ} (hγ : γ ∈ orthGroup (sumSqForm n) ℚ) :
    γ.val.det = 1 ∨ γ.val.det = -1 := by
  rw [mem_orthGroup] at hγ
  have h := congrArg Matrix.det hγ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have h0 : ((sumSqForm n).hessian.map (algebraMap ℚ ℚ)).det ≠ 0 := by
    have hm : (sumSqForm n).hessian.map (algebraMap ℚ ℚ) = (2 : ℚ) • 1 := by
      rw [hessian_sumSqForm]; ext i j; simp [Matrix.one_apply]
    rw [hm, Matrix.det_smul, Matrix.det_one]
    simp
  have h1 : γ.val.det * γ.val.det = 1 := by
    have := h
    field_simp at this
    nlinarith [this]
  have h2 : (γ.val.det - 1) * (γ.val.det + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; linarith
  · right; linarith

/-- **An isometry may be taken proper when the source lattice is stable under the swap of $x_0$, $x_1$** ($n \ge 2$). -/
theorem isProperIsometric_of_isIsometric_swap (hn : 2 ≤ n) {L M : Submodule (𝓞 ℚ) (Fin n → ℚ)}
    (hL : glImage (swapGL hn) L = L) (h : IsIsometric (sumSqForm n) L M) :
    IsProperIsometric (sumSqForm n) L M := by
  obtain ⟨γ, hγ, he⟩ := h
  rcases det_eq_one_or_neg_one_sumSqForm hγ with h1 | h1
  · exact ⟨⟨γ, hγ⟩, Tamagawa.mem_soSub.mpr h1, he⟩
  · refine ⟨⟨γ * swapGL hn, (orthGroup (sumSqForm n) ℚ).mul_mem hγ (swapGL_mem hn)⟩, ?_, ?_⟩
    · rw [Tamagawa.mem_soSub]
      change (γ * swapGL hn).val.det = 1
      rw [Units.val_mul, Matrix.det_mul, h1, swapGL_det]
      norm_num
    · change glImage (γ * swapGL hn) L = M
      rw [glImage_mul, hL, he]

end QuadFormsKB.Lattices

