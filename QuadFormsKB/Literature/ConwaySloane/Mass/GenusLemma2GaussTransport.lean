/-
# Conway–Sloane, LDL IV, §11, Lemma 2 at $p = 2$: from `DiscIso` to `Admissible`

Transport of an isomorphism of discriminant forms `DiscIso T A B` (integer matrices $A$, $B$) to the matrix data
`Admissible F F' T` (`GenusLemma2GaussBase.lean`) of the 2-adic block forms $F = $ `bmat D`, $F' = $ `bmat D'`, when
$A \sim_{\mathbb Z_2} F$ and $B \sim_{\mathbb Z_2} F'$ (`ZpEquiv`).

1. *Integer data* (`int_data`): $\Phi$, $\Phi'$, $W$, $W'$, $M$, $M'$ with $\Phi A = BW$, $\Phi'B = AW'$,
   $\Phi'\Phi = 1 + AM$, $\Phi\Phi' = 1 + BM'$, and $\mathrm{dualNorm}_B(\Phi y) - \mathrm{dualNorm}_A(y) \in T\mathbb Z$.
2. *Quadratic condition* (`quad_data`): $X = \Phi^{\mathsf T}B^{-1}\Phi - A^{-1}$ need not be 2-integral, but
   $y^{\mathsf T}Xy \in T\mathbb Z_2$ for all $y \in \mathbb Z_2^n$ (diagonal entries and twice the off-diagonal ones are
   in $T\mathbb Z_2$).
3. *Transport* along $\mathbb Z_2$-equivalences (`transport2`).
4. *Reindexing* from `Fin n` to `BIdx D` (`Admissible.submatrix_equiv`), and the final theorem `admissible_of_discIso`.

Indices are 0-based.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2GaussBase
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemma2Odd

set_option linter.unusedSectionVars false

open Matrix QuadFormsKB QuadFormsKB.Cassels QuadFormsKB.ConwaySloane.TwoAdic

namespace QuadFormsKB.ConwaySloane.Mass.Gauss2

open Lemma2Odd

variable {n : ℕ}

/-! ### Integer data -/

theorem exists_lift_aux {A B : Matrix (Fin n) (Fin n) ℤ} (φ : DiscGroup A →+ DiscGroup B) :
    ∃ Φ W : Matrix (Fin n) (Fin n) ℤ, Φ * A = B * W ∧
      ∀ y, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk (Φ *ᵥ y) := by
  set c : Fin n → (Fin n → ℤ) := fun j => Quotient.out (φ (QuotientAddGroup.mk (Pi.single j 1))) with hc
  set Φ : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => c j i with hΦ
  have hmk : ∀ y, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk (Φ *ᵥ y) := by
    have key : (φ.comp (QuotientAddGroup.mk' (gramLat A))) =
        (QuotientAddGroup.mk' (gramLat B)).comp Φ.mulVecLin.toAddMonoidHom := by
      refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
      have e : (Pi.single j x : Fin n → ℤ) = x • Pi.single j (1 : ℤ) := by
        ext r; by_cases h : r = j
        · subst h; simp
        · simp [h]
      rw [e, map_zsmul, map_zsmul]
      congr 1
      have hcol : Φ *ᵥ Pi.single j 1 = c j := by
        rw [Matrix.mulVec_single_one]; ext i; simp [hΦ, Matrix.col]
      change φ (QuotientAddGroup.mk (Pi.single j 1)) = QuotientAddGroup.mk (Φ *ᵥ Pi.single j 1)
      rw [hcol, hc]
      exact (QuotientAddGroup.out_eq' _).symm
    intro y
    exact DFunLike.congr_fun key y
  have hw : ∀ j, ∃ w, B *ᵥ w = Φ *ᵥ (A *ᵥ Pi.single j 1) := by
    intro j
    have h0 : (QuotientAddGroup.mk (A *ᵥ Pi.single j 1) : DiscGroup A) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (mem_gramLat.2 ⟨_, rfl⟩)
    have := hmk (A *ᵥ Pi.single j 1)
    rw [h0, map_zero] at this
    exact mem_gramLat.1 ((QuotientAddGroup.eq_zero_iff _).1 this.symm)
  choose w hw using hw
  refine ⟨Φ, Matrix.of fun i j => w j i, ?_, hmk⟩
  ext i j
  have e1 : (Φ * A) i j = ((Φ * A) *ᵥ Pi.single j 1) i := by simp
  have e2 : (B * Matrix.of fun i j => w j i) i j = (B *ᵥ w j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e1, e2, ← Matrix.mulVec_mulVec, hw j]

theorem exists_mat_of_cols {A P : Matrix (Fin n) (Fin n) ℤ}
    (h : ∀ y, ∃ z, P *ᵥ y = y + A *ᵥ z) : ∃ M, P = 1 + A * M := by
  choose z hz using fun j : Fin n => h (Pi.single j 1)
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have e1 : P i j = (P *ᵥ Pi.single j 1) i := by simp
  have e2 : (A * Matrix.of fun i j => z j i) i j = (A *ᵥ z j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [e1, hz j, Matrix.add_apply, e2, Matrix.one_apply]
  simp [Pi.single_apply, eq_comm]

/-- **Integer data of a `DiscIso`**: lifts of $\varphi$ and $\varphi^{-1}$, mutually inverse up to $A$, $B$. -/
theorem int_data {A B : Matrix (Fin n) (Fin n) ℤ} {T : ℕ} (h : DiscIso T A B) :
    ∃ Φ Φ' W W' M M' : Matrix (Fin n) (Fin n) ℤ, Φ * A = B * W ∧ Φ' * B = A * W' ∧
      Φ' * Φ = 1 + A * M ∧ Φ * Φ' = 1 + B * M' ∧
      ∀ y : Fin n → ℤ, ∃ k : ℤ, dualNorm B (Φ *ᵥ y) = dualNorm A y + (T : ℕ) * k := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨Φ, W, hW, hmk⟩ := exists_lift_aux (A := A) (B := B) φ.toAddMonoidHom
  obtain ⟨Φ', W', hW', hmk'⟩ := exists_lift_aux (A := B) (B := A) φ.symm.toAddMonoidHom
  have hmk1 : ∀ y, φ (QuotientAddGroup.mk y) = QuotientAddGroup.mk (Φ *ᵥ y) := hmk
  have hmk2 : ∀ z, φ.symm (QuotientAddGroup.mk z) = QuotientAddGroup.mk (Φ' *ᵥ z) := hmk'
  refine ⟨Φ, Φ', W, W', ?_⟩
  obtain ⟨M, hM⟩ := exists_mat_of_cols (A := A) (P := Φ' * Φ) (fun y => by
    have : (QuotientAddGroup.mk (Φ' *ᵥ (Φ *ᵥ y)) : DiscGroup A) = QuotientAddGroup.mk y := by
      rw [← hmk2, ← hmk1]; simp
    obtain ⟨z, hz⟩ := exists_eq_mulVec this.symm
    exact ⟨z, by rw [← Matrix.mulVec_mulVec]; exact hz⟩)
  obtain ⟨M', hM'⟩ := exists_mat_of_cols (A := B) (P := Φ * Φ') (fun y => by
    have : (QuotientAddGroup.mk (Φ *ᵥ (Φ' *ᵥ y)) : DiscGroup B) = QuotientAddGroup.mk y := by
      rw [← hmk1, ← hmk2]; simp
    obtain ⟨z, hz⟩ := exists_eq_mulVec this.symm
    exact ⟨z, by rw [← Matrix.mulVec_mulVec]; exact hz⟩)
  refine ⟨M, M', hW, hW', hM, hM', fun y => hφ y (Φ *ᵥ y) (hmk1 y)⟩

/-! ### The quadratic condition over $\mathbb Q_2$ -/

theorem sum_norm_le_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[2]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem IsInt.mulVec {M : Matrix (Fin n) (Fin n) ℚ_[2]} {y : Fin n → ℚ_[2]} (hM : IsInt M) (hy : IsIntV y) :
    IsIntV (M *ᵥ y) := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_norm_le_one _ _ fun j _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hM i j) (norm_nonneg _) (hy j)

theorem quad_data {A B : Matrix (Fin n) (Fin n) ℤ} (hdA : A.det ≠ 0) (hdB : B.det ≠ 0) {T : ℕ}
    {Φ : Matrix (Fin n) (Fin n) ℤ}
    (hm : ∀ y : Fin n → ℤ, ∃ k : ℤ, dualNorm B (Φ *ᵥ y) = dualNorm A y + (T : ℕ) * k) :
    ∀ y : Fin n → ℚ_[2], IsIntV y → ∃ z : ℚ_[2], ‖z‖ ≤ 1 ∧
      qv ((B.map (Int.castRingHom ℚ_[2]))⁻¹) ((Φ.map (Int.castRingHom ℚ_[2])) *ᵥ y) -
        qv ((A.map (Int.castRingHom ℚ_[2]))⁻¹) y = (T : ℚ_[2]) * z := by
  set f := Int.castRingHom ℚ_[2] with hf
  set X := (Φ.map f)ᵀ * (B.map f)⁻¹ * Φ.map f - (A.map f)⁻¹ with hX
  have hQ : ∀ y : Fin n → ℤ, ∃ m : ℤ,
      (fun i => (y i : ℚ_[2])) ⬝ᵥ (X *ᵥ fun i => (y i : ℚ_[2])) = (T : ℚ_[2]) * m := by
    intro y
    obtain ⟨m, hm⟩ := hm y
    refine ⟨m, ?_⟩
    have e1 := dualNorm_cast (p := 2) B hdB (Φ *ᵥ y)
    have e2 := dualNorm_cast (p := 2) A hdA y
    have e3 : (fun i => ((Φ *ᵥ y) i : ℚ_[2])) = Φ.map f *ᵥ fun i => (y i : ℚ_[2]) := by
      funext i; have := RingHom.map_mulVec f Φ y i; simpa [hf, Function.comp_def] using this
    rw [e3, conj_dot] at e1
    rw [hX, Matrix.sub_mulVec, dotProduct_sub, ← e1, ← e2, hm]; push_cast; ring
  have hd : ∀ i, ∃ m : ℤ, X i i = (T : ℚ_[2]) * m := fun i => by
    obtain ⟨m, h⟩ := hQ (Pi.single i 1)
    refine ⟨m, ?_⟩
    rw [cast_single] at h
    simpa using h
  have ho : ∀ i j, ∃ m : ℤ, X i j + X j i = (T : ℚ_[2]) * m := fun i j => by
    obtain ⟨m1, h1⟩ := hQ (Pi.single i 1 + Pi.single j 1)
    obtain ⟨m2, h2⟩ := hQ (Pi.single i 1)
    obtain ⟨m3, h3⟩ := hQ (Pi.single j 1)
    have ec : (fun r => (((Pi.single i 1 + Pi.single j 1 : Fin n → ℤ)) r : ℚ_[2])) =
        Pi.single i 1 + Pi.single j 1 := by
      rw [← cast_single i, ← cast_single j]; ext r; simp
    rw [ec] at h1
    rw [cast_single] at h2 h3
    have q1 : (Pi.single i 1 + Pi.single j 1) ⬝ᵥ (X *ᵥ (Pi.single i 1 + Pi.single j 1))
        = X i i + X i j + X j i + X j j := by
      simp [mulVec_add, dotProduct_add, add_dotProduct]; ring
    have q2 : ∀ r : Fin n, (Pi.single r 1) ⬝ᵥ (X *ᵥ (Pi.single r 1)) = X r r := fun r => by simp
    rw [q1] at h1
    rw [q2] at h2 h3
    refine ⟨m1 - m2 - m3, ?_⟩
    push_cast
    linear_combination h1 - h2 - h3
  choose e he using hd
  choose o ho using ho
  intro y hy
  have hconj : qv ((B.map f)⁻¹) ((Φ.map f) *ᵥ y) - qv ((A.map f)⁻¹) y = y ⬝ᵥ (X *ᵥ y) := by
    unfold qv
    rw [conj_dot, hX, Matrix.sub_mulVec, dotProduct_sub]
  rw [hconj]
  refine ⟨(∑ i, (e i : ℚ_[2]) * (y i * y i)) +
    ∑ i, ∑ j, (if i < j then (o i j : ℚ_[2]) * (y i * y j) else 0), ?_, ?_⟩
  · have hb : ∀ a b : ℚ_[2], ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun a b ha hb => by
      rw [norm_mul]; calc ‖a‖ * ‖b‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hyy : ∀ i j, ‖y i * y j‖ ≤ 1 := fun i j => hb _ _ (hy i) (hy j)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (sum_norm_le_one _ _ fun i _ => ?_)
      (sum_norm_le_one _ _ fun i _ => sum_norm_le_one _ _ fun j _ => ?_))
    · exact hb _ _ (Padic.norm_int_le_one _) (hyy i i)
    · split_ifs
      · exact hb _ _ (Padic.norm_int_le_one _) (hyy i j)
      · simp
  · set g : Fin n → Fin n → ℚ_[2] := fun i j => X i j * (y i * y j) with hg
    have h0 : y ⬝ᵥ (X *ᵥ y) = ∑ i, ∑ j, g i j := by
      simp only [dotProduct, Matrix.mulVec, hg, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h1 : ∑ i, ∑ j, g i j = ∑ i, ∑ j, ((if i = j then g i j else 0) + (if i < j then g i j else 0) +
        (if j < i then g i j else 0)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp
      · simp [h, h.ne', not_lt.2 h.le]
    have h2 : ∑ i, ∑ j, (if j < i then g i j else 0) = ∑ i, ∑ j, (if i < j then g j i else 0) :=
      Finset.sum_comm
    simp only [Finset.sum_add_distrib] at h1
    rw [h0, h1, h2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hs1' : ∑ i, g i i = (T : ℚ_[2]) * ∑ i, (e i : ℚ_[2]) * (y i * y i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg]; rw [he i]; ring
    have hp : ∀ i j, (if i < j then g i j else 0) + (if i < j then g j i else 0) =
        (T : ℚ_[2]) * (if i < j then (o i j : ℚ_[2]) * (y i * y j) else 0) := by
      intro i j
      by_cases hij : i < j
      · simp only [hij, ite_true, hg]
        have := ho i j
        linear_combination (y i * y j) * this
      · simp [hij]
    have hs3 : ∑ i, ∑ j, (if i < j then g i j else 0) + ∑ i, ∑ j, (if i < j then g j i else 0) =
        (T : ℚ_[2]) * ∑ i, ∑ j, (if i < j then (o i j : ℚ_[2]) * (y i * y j) else 0) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hp i j
    rw [mul_add, ← hs1', ← hs3]
    ring


/-! ### Transport along $\mathbb Z_2$-equivalences -/

section Transport

variable {S Si S' Si' F G D D' Φ Φ' W W' M M' : Matrix (Fin n) (Fin n) ℚ_[2]}

theorem rel_tr (h1 : S * Si = 1) (h1' : S' * Si' = 1) (hD : Sᵀ * F * S = D) (hD' : S'ᵀ * G * S' = D')
    (e : Φ * F = G * W) : (S'ᵀ * Φ * Siᵀ) * D = D' * (Si' * W * S) := by
  have t2 : ∀ X, Siᵀ * (Sᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  have c1' : ∀ X, S' * (Si' * X) = X := fun X => by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  subst hD hD'
  simp only [Matrix.mul_assoc, t2, c1']
  rw [← Matrix.mul_assoc Φ, e, Matrix.mul_assoc]

theorem mul_tr (h1 : S * Si = 1) (h2 : Si * S = 1) (h1' : S' * Si' = 1) (hD : Sᵀ * F * S = D)
    (e : Φ' * Φ = 1 + F * M) : (Sᵀ * Φ' * Si'ᵀ) * (S'ᵀ * Φ * Siᵀ) = 1 + D * (Si * M * Siᵀ) := by
  have a : Si'ᵀ * S'ᵀ = 1 := by rw [← Matrix.transpose_mul, h1', Matrix.transpose_one]
  have b : Sᵀ * Siᵀ = 1 := by rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  have c1 : ∀ X, S * (Si * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  subst hD
  calc (Sᵀ * Φ' * Si'ᵀ) * (S'ᵀ * Φ * Siᵀ) = Sᵀ * (Φ' * (Si'ᵀ * S'ᵀ) * Φ) * Siᵀ := by
        simp only [Matrix.mul_assoc]
    _ = Sᵀ * (Φ' * Φ) * Siᵀ := by rw [a, Matrix.mul_one]
    _ = 1 + Sᵀ * F * S * (Si * M * Siᵀ) := by
        rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, b]
        simp only [Matrix.mul_assoc, c1]

theorem inv_tr (hF : IsUnit F.det) (h1 : S * Si = 1) (h2 : Si * S = 1) (hD : Sᵀ * F * S = D) :
    D⁻¹ = Si * F⁻¹ * Siᵀ := by
  have c1 : ∀ X, S * (Si * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hFF : ∀ X, F * (F⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hF, Matrix.one_mul]
  apply inv_eq_right_inv
  rw [← hD]
  simp only [Matrix.mul_assoc, c1, hFF]
  rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]

theorem qv_conj (h1 : S * Si = 1) (Q : Matrix (Fin n) (Fin n) ℚ_[2]) (v : Fin n → ℚ_[2]) :
    qv (Si * Q * Siᵀ) (Sᵀ *ᵥ v) = qv Q v := by
  have a : Siᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  unfold qv
  have a' : Siᵀ *ᵥ (Sᵀ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, a, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, a',
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

/-- **Transport to the diagonal/block forms**: the data $(\Phi, \Phi', W, W', M, M')$ over $\mathbb Q_2$ for
$F$, $G$ gives `Admissible D D' T` for $\mathbb Z_2$-equivalent forms $D \sim F$, $D' \sim G$. -/
theorem transport2 {T : ℕ} (hF : IsUnit F.det) (hG : IsUnit G.det)
    (hFD : ZpEquiv F D) (hGD : ZpEquiv G D')
    (hΦ : IsInt Φ) (hΦ' : IsInt Φ') (hW : IsInt W) (hW' : IsInt W') (hM : IsInt M) (hM' : IsInt M')
    (e1 : Φ * F = G * W) (e2 : Φ' * G = F * W') (e3 : Φ' * Φ = 1 + F * M) (e4 : Φ * Φ' = 1 + G * M')
    (hq : ∀ y : Fin n → ℚ_[2], IsIntV y → ∃ z : ℚ_[2], ‖z‖ ≤ 1 ∧
      qv G⁻¹ (Φ *ᵥ y) - qv F⁻¹ y = (T : ℚ_[2]) * z) :
    Admissible D D' T := by
  obtain ⟨U, hU⟩ := hFD
  obtain ⟨U', hU'⟩ := hGD
  set S := U.val.map PadicInt.Coe.ringHom with hS
  set Si := (U⁻¹).val.map PadicInt.Coe.ringHom with hSi
  set S' := U'.val.map PadicInt.Coe.ringHom with hS'
  set Si' := (U'⁻¹).val.map PadicInt.Coe.ringHom with hSi'
  have one_map : (1 : Matrix (Fin n) (Fin n) ℤ_[2]).map PadicInt.Coe.ringHom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : S * Si = 1 := by
    rw [hS, hSi, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_map]
  have h2 : Si * S = 1 := by
    rw [hS, hSi, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_map]
  have h1' : S' * Si' = 1 := by
    rw [hS', hSi', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_map]
  have h2' : Si' * S' = 1 := by
    rw [hS', hSi', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_map]
  have iS : IsInt S := isInt_map _
  have iSi : IsInt Si := isInt_map _
  have iS' : IsInt S' := isInt_map _
  have iSi' : IsInt Si' := isInt_map _
  refine ⟨S'ᵀ * Φ * Siᵀ, Sᵀ * Φ' * Si'ᵀ, Si' * W * S, Si * W' * S', Si * M * Siᵀ, Si' * M' * Si'ᵀ,
    ((iS'.transpose.mul hΦ).mul iSi.transpose), ((iS.transpose.mul hΦ').mul iSi'.transpose),
    ((iSi'.mul hW).mul iS), ((iSi.mul hW').mul iS'), ((iSi.mul hM).mul iSi.transpose),
    ((iSi'.mul hM').mul iSi'.transpose),
    rel_tr h1 h1' hU hU' e1, rel_tr h1' h1 hU' hU e2, mul_tr h1 h2 h1' hU e3, mul_tr h1' h2' h1 hU' e4, ?_⟩
  intro y hy
  have hDi := inv_tr hF h1 h2 hU
  have hDi' := inv_tr hG h1' h2' hU'
  have hu : IsIntV (Siᵀ *ᵥ y) := IsInt.mulVec iSi.transpose hy
  have hy' : Sᵀ *ᵥ (Siᵀ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, h2, Matrix.transpose_one, Matrix.one_mulVec]
  obtain ⟨z, hz, hzeq⟩ := hq _ hu
  refine ⟨z, hz, ?_⟩
  have e5 : (S'ᵀ * Φ * Siᵀ) *ᵥ y = S'ᵀ *ᵥ (Φ *ᵥ (Siᵀ *ᵥ y)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e6 := qv_conj h1 F⁻¹ (Siᵀ *ᵥ y)
  rw [hy'] at e6
  rw [e5, hDi', hDi, qv_conj h1', e6, ← hzeq]

end Transport

/-! ### Reindexing -/

section Reindex

theorem qv_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] (F : Matrix ι ι ℚ_[2]) (e : κ ≃ ι) (y : κ → ℚ_[2]) :
    qv (F.submatrix e e) y = qv F (y ∘ e.symm) := by
  unfold qv
  rw [Matrix.submatrix_mulVec_equiv]
  unfold dotProduct
  rw [← Equiv.sum_comp e]
  simp

theorem Admissible.submatrix_equiv {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ']
    {F : Matrix ι ι ℚ_[2]} {F' : Matrix ι' ι' ℚ_[2]} {T : ℕ} (h : Admissible F F' T) (e : κ ≃ ι) (e' : κ' ≃ ι') :
    Admissible (F.submatrix e e) (F'.submatrix e' e') T := by
  obtain ⟨Ψ, Ψ', W, W', M, M', i1, i2, i3, i4, i5, i6, r1, r2, r3, r4, hq⟩ := h
  refine ⟨Ψ.submatrix e' e, Ψ'.submatrix e e', W.submatrix e' e, W'.submatrix e e', M.submatrix e e,
    M'.submatrix e' e', fun _ _ => i1 _ _, fun _ _ => i2 _ _, fun _ _ => i3 _ _, fun _ _ => i4 _ _,
    fun _ _ => i5 _ _, fun _ _ => i6 _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, r1]
  · rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, r2]
  · rw [Matrix.submatrix_mul_equiv, r3, Matrix.submatrix_mul_equiv F M e e e, ← Matrix.submatrix_one_equiv e]
    rfl
  · rw [Matrix.submatrix_mul_equiv, r4, Matrix.submatrix_mul_equiv F' M' e' e' e', ← Matrix.submatrix_one_equiv e']
    rfl
  · intro y hy
    obtain ⟨z, hz, hzeq⟩ := hq (y ∘ e.symm) (fun i => hy _)
    refine ⟨z, hz, ?_⟩
    have e7 : ((Ψ *ᵥ y ∘ e.symm) ∘ e') ∘ e'.symm = Ψ *ᵥ y ∘ e.symm := by ext; simp
    rw [Matrix.inv_submatrix_equiv, Matrix.inv_submatrix_equiv, qv_submatrix, qv_submatrix,
      Matrix.submatrix_mulVec_equiv, e7]
    exact hzeq

end Reindex

/-! ### The theorem -/

theorem bmat_eq_submatrix (D : List DyBlock) (h : dyDim D = n) :
    bmat D = (castMat D h).submatrix (bE D h).symm (bE D h).symm := by
  ext i j; rw [Matrix.submatrix_apply, castMat_apply]; simp

/-- **From an isomorphism of discriminant forms to admissible data.** If `DiscIso T A B` for symmetric integer
$A$, $B$ with nonzero determinant, $A \sim_{\mathbb Z_2}$ `castMat D h` and $B \sim_{\mathbb Z_2}$ `castMat D' h'`
(`ZpEquiv`), then `Admissible (bmat D) (bmat D') T`. Unconditional (standard axioms only). -/
theorem admissible_of_discIso {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hdA : A.det ≠ 0) (hdB : B.det ≠ 0) {T : ℕ} (hT : DiscIso T A B)
    {D D' : List DyBlock} (h : dyDim D = n) (h' : dyDim D' = n)
    (hAD : ZpEquiv (A.map (Int.castRingHom ℚ_[2])) (TwoAdic.castMat D h))
    (hBD : ZpEquiv (B.map (Int.castRingHom ℚ_[2])) (TwoAdic.castMat D' h')) :
    Admissible (bmat D) (bmat D') T := by
  obtain ⟨Φ, Φ', W, W', M, M', e1, e2, e3, e4, hm⟩ := int_data hT
  set f := Int.castRingHom ℚ_[2] with hf
  have hu : ∀ C : Matrix (Fin n) (Fin n) ℤ, C.det ≠ 0 → IsUnit (C.map f).det := fun C hC => by
    rw [isUnit_iff_ne_zero]
    have := RingHom.map_det f C
    intro h0
    apply hC
    have h2 : f C.det = 0 := this.trans h0
    have h3 : ((C.det : ℤ) : ℚ_[2]) = 0 := by simpa [hf] using h2
    exact_mod_cast h3
  have c1 : Φ.map f * A.map f = B.map f * W.map f := by
    have := congrArg f.mapMatrix e1; simp only [map_mul] at this; exact this
  have c2 : Φ'.map f * B.map f = A.map f * W'.map f := by
    have := congrArg f.mapMatrix e2; simp only [map_mul] at this; exact this
  have c3 : Φ'.map f * Φ.map f = 1 + A.map f * M.map f := by
    have := congrArg f.mapMatrix e3; simp only [map_mul, map_add, map_one] at this; exact this
  have c4 : Φ.map f * Φ'.map f = 1 + B.map f * M'.map f := by
    have := congrArg f.mapMatrix e4; simp only [map_mul, map_add, map_one] at this; exact this
  have key := transport2 (T := T) (hu A hdA) (hu B hdB) hAD hBD (isInt_intCast Φ) (isInt_intCast Φ')
    (isInt_intCast W) (isInt_intCast W') (isInt_intCast M) (isInt_intCast M') c1 c2 c3 c4
    (quad_data hdA hdB hm)
  rw [bmat_eq_submatrix D h, bmat_eq_submatrix D' h']
  exact key.submatrix_equiv _ _

end QuadFormsKB.ConwaySloane.Mass.Gauss2
