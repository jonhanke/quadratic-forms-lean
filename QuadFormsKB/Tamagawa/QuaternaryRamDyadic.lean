/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.TernaryRamDyadic
import QuadFormsKB.Witt.Bridge

/-!
# The self-density of $\pi T'\perp T$ at a dyadic prime (maximal order of a quaternion division algebra)

**Layer:** a complete discrete valuation ring $R$ with finite residue field, uniformizer $\pi$, $\pi \mid 2$ (dyadic).

Let $T, T'$ be binary forms with $\det H_T$, $\det H_{T'}$ units whose reductions are anisotropic. Put
$Q = \pi T'\perp T$ and $Q'' = T'\perp\pi T$, so that $Q\circ P = \pi Q''$ for $P = \mathrm{diag}(1,1,\pi,\pi)$.
We prove (repository normalization $\beta = 2\alpha$)
$$\beta_\pi(Q, Q) = 4q(q+1)^2 \qquad (\texttt{localDensityForm\_quaternary\_dyadic}),$$
Shimura's value for the maximal order of the quaternion division algebra.

*Proof.* Orbit--stabilizer for the frame $F = (e_0, e_1)$ (the $\pi T'$ block) in $O(Q \bmod \pi^k)$.
* The stabilizer is $\{(B, D)\}$ with $\pi B = 0$ and $D \in O(T \bmod \pi^k)$ (`qrStabEquiv`): it has $q^4\cdot|O(T \bmod \pi^k)|$ elements.
* The orbit is every representation of $\pi T'$ mod $\pi^k$ (`qr_orbit`): such a representation has bottom block divisible by $\pi$
  (`qr_bot_dvd`, $\bar T$ anisotropic), so it is $PZ$ with $Q''\circ Z \equiv T'$ mod $\pi^{k-1}$; Hensel ($T'$ unimodular) gives an
  exact $Z_t$. The exact representation $PZ_t$ of $\pi T'$ is the frame of an exact isometry of $Q$ (`qr_exact_isometry`): the
  orthogonal complement is $\{(-EN b; Nb)\}$ for an explicit integral $E$, and it carries the form $T_1 \equiv T$ mod $\pi$
  ($T_1 = T + \pi T'\circ E$), so a second Hensel step finds $N$ with $T_1\circ N = T$. Finally the frame may be moved by
  $\pi^{k-1}P(\cdot)$ without changing $Q\circ X$ mod $\pi^k$.
* Representations of $\pi T'$ by $Q$ mod $\pi^{k+1}$ correspond to representations of $T'$ by $Q''$ mod $\pi^k$:
  $A_{\pi^{k+1}}(Q, \pi T') = q^4A_{\pi^k}(Q'', T')$ (`repCountForm_quat_piT`).
* $\beta_\pi(Q'', T') = \beta_\pi(T, T) = 2(q+1)/q$ (count mod $\pi$ via `card_orth_binary_char2`), so
  $\beta_\pi(Q, Q) = q^3\cdot\frac{2(q+1)}{q}\cdot\frac{2(q+1)}{q} = 4q(q+1)^2$.

Sources: Shimura 1999 (Lemma 3.7(2), Prop. 3.9); the counting is elementary. Indices are 0-based.
-/

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

/-! ### Block vectors and matrices on $\mathrm{Fin}(2+2)$ -/

section Blocks

variable {A : Type*} [CommRing A] {r : ℕ}

/-- The matrix with top block `X` and bottom block `Y` (rows `Fin (2+2)`). -/
def qrStk (X Y : Matrix (Fin 2) (Fin r) A) : Matrix (Fin (2 + 2)) (Fin r) A :=
  Matrix.of fun i j => Fin.append (fun a => X a j) (fun b => Y b j) i

/-- The top block of `qrStk X Y` is `X`. -/
theorem qrStk_top (X Y : Matrix (Fin 2) (Fin r) A) (a : Fin 2) (j : Fin r) :
    qrStk X Y (Fin.castAdd 2 a) j = X a j := by simp only [qrStk, Matrix.of_apply, Fin.append_left]

/-- The bottom block of `qrStk X Y` is `Y`. -/
theorem qrStk_bot (X Y : Matrix (Fin 2) (Fin r) A) (a : Fin 2) (j : Fin r) :
    qrStk X Y (Fin.natAdd 2 a) j = Y a j := by simp only [qrStk, Matrix.of_apply, Fin.append_right]

/-- A matrix is the stack of its top and bottom blocks. -/
theorem qrStk_top_bot (Z : Matrix (Fin (2 + 2)) (Fin r) A) :
    qrStk (Matrix.of fun a j => Z (Fin.castAdd 2 a) j) (Matrix.of fun a j => Z (Fin.natAdd 2 a) j) = Z := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · rw [qrStk_top]; rfl
  · rw [qrStk_bot]; rfl

/-- $(\text{stack } X\, Y)\,w = (Xw, Yw)$. -/
theorem qrStk_mulVec (X Y : Matrix (Fin 2) (Fin r) A) (w : Fin r → A) :
    qrStk X Y *ᵥ w = Fin.append (X *ᵥ w) (Y *ᵥ w) := by
  ext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [mulVec, dotProduct, qrStk_top, Fin.append_left]
  · simp only [mulVec, dotProduct, qrStk_bot, Fin.append_right]

/-- $(\text{stack } X\, Y)\,M = \text{stack}(XM)(YM)$. -/
theorem qrStk_mul {s : ℕ} (X Y : Matrix (Fin 2) (Fin r) A) (M : Matrix (Fin r) (Fin s) A) :
    qrStk X Y * M = qrStk (X * M) (Y * M) := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [Matrix.mul_apply, qrStk_top]
  · simp only [Matrix.mul_apply, qrStk_bot]

/-- The value of a vector as a pair of blocks. -/
theorem qr_append_eta (v : Fin (2 + 2) → A) :
    Fin.append (fun a => v (Fin.castAdd 2 a)) (fun a => v (Fin.natAdd 2 a)) = v :=
  Fin.append_castAdd_natAdd

/-- $\mathrm{diag}(1, 1, p, p)$. -/
def qrPm (p : A) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A :=
  Matrix.diagonal (Fin.append (fun _ => (1 : A)) (fun _ => p))

/-- $\mathrm{diag}(1,1,p,p)\,v = (v_{\mathrm{top}}, p\,v_{\mathrm{bot}})$. -/
theorem qrPm_mulVec (p : A) (v : Fin (2 + 2) → A) :
    qrPm p *ᵥ v = Fin.append (fun a => v (Fin.castAdd 2 a)) (fun a => p * v (Fin.natAdd 2 a)) := by
  ext i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [qrPm, mulVec_diagonal, Fin.append_left, one_mul]
  · simp only [qrPm, mulVec_diagonal, Fin.append_right]

/-- $(\mathrm{diag}(1,1,p,p)Z)_{ij}$ is $Z_{ij}$ in the top rows and $pZ_{ij}$ in the bottom rows. -/
theorem qrPm_mul_apply (p : A) (Z : Matrix (Fin (2 + 2)) (Fin r) A) (i : Fin (2 + 2)) (j : Fin r) :
    (qrPm p * Z) i j = Fin.append (fun _ => (1 : A)) (fun _ => p) i * Z i j := by
  simp only [qrPm, Matrix.diagonal_mul]

/-- Base change commutes with $\mathrm{diag}(1,1,p,p)$. -/
theorem qrPm_map {B : Type*} [CommRing B] (f : A →+* B) (p : A) : (qrPm p).map f = qrPm (f p) := by
  ext i j
  simp only [Matrix.map_apply, qrPm, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [Fin.append_left, map_one]
    · simp only [Fin.append_right]
  · simp

/-- The frame $F = (e_0, e_1)$: top block $1$, bottom block $0$. -/
def qrFrame (A : Type*) [CommRing A] : Matrix (Fin (2 + 2)) (Fin 2) A :=
  qrStk (1 : Matrix (Fin 2) (Fin 2) A) 0

/-- Base change commutes with the frame. -/
theorem qrFrame_map {B : Type*} [CommRing B] (f : A →+* B) : (qrFrame A).map f = qrFrame B := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · simp only [Matrix.map_apply, qrFrame, qrStk_top, Matrix.one_apply, apply_ite f, map_one, map_zero]
  · simp only [Matrix.map_apply, qrFrame, qrStk_bot, Matrix.zero_apply, map_zero]

/-- $F\,w = (w, 0)$. -/
theorem qrFrame_mulVec (w : Fin 2 → A) : qrFrame A *ᵥ w = Fin.append w 0 := by
  rw [qrFrame, qrStk_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec]

/-- $(XF)_{ij} = X_{i,j}$ for the first two columns. -/
theorem mul_qrFrame_apply (X : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A) (i : Fin (2 + 2)) (j : Fin 2) :
    (X * qrFrame A) i j = X i (Fin.castAdd 2 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp only [qrFrame, qrStk_top, qrStk_bot, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, mul_ite, mul_one, mul_zero]
  fin_cases j <;> simp [Fin.castAdd]

end Blocks

/-! ### The orthogonal sum of two binary forms -/

section OrthSum

variable {A : Type*} [CommRing A]

/-- $(S\perp T)(x) = S(x_{\mathrm{top}}) + T(x_{\mathrm{bot}})$. -/
theorem eval_orthSum_gen {m n : ℕ} (S : QuadForm A m) (T : QuadForm A n) (x : Fin (m + n) → A) :
    (orthSum S T).eval x = S.eval (fun a => x (Fin.castAdd n a)) + T.eval (fun b => x (Fin.natAdd m b)) :=
  evalIn_orthSum A S T x

/-- $(S\perp T)(u, v) = S(u) + T(v)$. -/
theorem eval_orthSum_append {m n : ℕ} (S : QuadForm A m) (T : QuadForm A n) (u : Fin m → A) (v : Fin n → A) :
    (orthSum S T).eval (Fin.append u v) = S.eval u + T.eval v := by
  rw [eval_orthSum_gen]
  simp only [Fin.append_left, Fin.append_right]

/-- The polar form of an orthogonal sum is the sum of the polar forms. -/
theorem bil_orthSum_gen {m n : ℕ} (S : QuadForm A m) (T : QuadForm A n) (x y : Fin (m + n) → A) :
    x ⬝ᵥ ((orthSum S T).hessian *ᵥ y) =
      (fun a => x (Fin.castAdd n a)) ⬝ᵥ (S.hessian *ᵥ fun a => y (Fin.castAdd n a)) +
      (fun b => x (Fin.natAdd m b)) ⬝ᵥ (T.hessian *ᵥ fun b => y (Fin.natAdd m b)) := by
  rw [← eval_polar, ← eval_polar, ← eval_polar]
  have e1 : (fun a => (x + y) (Fin.castAdd n a)) =
      (fun a => x (Fin.castAdd n a)) + fun a => y (Fin.castAdd n a) := rfl
  have e2 : (fun b => (x + y) (Fin.natAdd m b)) =
      (fun b => x (Fin.natAdd m b)) + fun b => y (Fin.natAdd m b) := rfl
  rw [eval_orthSum_gen, eval_orthSum_gen, eval_orthSum_gen, e1, e2]
  ring

/-- $T(cx) = c^2\,T(x)$. -/
theorem eval_smul_vec {n : ℕ} (T : QuadForm A n) (c : A) (x : Fin n → A) : T.eval (c • x) = c * c * T.eval x := by
  rw [eval_eq_dotProduct', eval_eq_dotProduct', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]; ring

/-- $H_{pT} = p\,H_T$. -/
theorem hessian_smul_form {n : ℕ} (p : A) (T : QuadForm A n) : (p • T).hessian = p • T.hessian := by
  ext; simp [hessian, smul_coeff]; ring

/-- $T(0) = 0$. -/
theorem eval_zero_vec {n : ℕ} (T : QuadForm A n) : T.eval 0 = 0 := by
  simp [QuadForm.eval, QuadForm.evalIn]

/-- $(S\perp T)\circ F = S$ for the frame $F$ of the first block. -/
theorem compMat_orthSum_frame (S T : QuadForm A 2) : (orthSum S T).compMat (qrFrame A) = S :=
  eq_of_eval_eq fun w => by
    rw [eval_compMat, qrFrame_mulVec, eval_orthSum_append, eval_zero_vec, add_zero]

/-- $(\pi T'\perp T)\circ P = \pi(T'\perp\pi T)$ for $P = \mathrm{diag}(1,1,\pi,\pi)$. -/
theorem compMat_orthSum_Pm (p : A) (S T : QuadForm A 2) :
    (orthSum (p • S) T).compMat (qrPm p) = p • orthSum S (p • T) :=
  eq_of_eval_eq fun w => by
    rw [eval_compMat, qrPm_mulVec, eval_smul_form_rd, eval_orthSum_gen, eval_orthSum_gen]
    simp only [Fin.append_left, Fin.append_right]
    rw [eval_smul_form_rd p S, eval_smul_form_rd p T]
    rw [show (fun a => p * w (Fin.natAdd 2 a)) = p • fun a => w (Fin.natAdd 2 a) from rfl, eval_smul_vec]
    ring

/-- The $(a,b)$ entry of $X^{\mathsf T}CW$ is $X_a^{\mathsf T}CW_b$ (columns), for matrices of different widths. -/
theorem qr_tmm_apply {n r s : ℕ} (C : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A)
    (W : Matrix (Fin n) (Fin s) A) (a : Fin r) (b : Fin s) :
    (Xᵀ * C * W) a b = (fun l => X l a) ⬝ᵥ (C *ᵥ fun l => W l b) := by
  simp only [Matrix.mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The Gram matrix of stacked blocks in $S\perp T$. -/
theorem qr_gram {r s : ℕ} (S T : QuadForm A 2) (X Y : Matrix (Fin 2) (Fin r) A) (X' Y' : Matrix (Fin 2) (Fin s) A) :
    (qrStk X Y)ᵀ * (orthSum S T).hessian * qrStk X' Y' =
      Xᵀ * S.hessian * X' + Yᵀ * T.hessian * Y' := by
  ext a b
  rw [qr_tmm_apply, bil_orthSum_gen, Matrix.add_apply, qr_tmm_apply, qr_tmm_apply]
  congr 2 <;> ext l <;> first | exact qrStk_top _ _ _ _ | exact qrStk_bot _ _ _ _

end OrthSum

/-! ### Coefficients, Hessian and base change of $S\perp T$ -/

section OrthSumCoeff

variable {A : Type*} [CommRing A] {m n : ℕ}

/-- The coefficients of $S\perp T$ in the top-top block are those of $S$. -/
theorem orthSum_coeff_cc (S : QuadForm A m) (T : QuadForm A n) (a b : Fin m) :
    (orthSum S T).coeff (Fin.castAdd n a) (Fin.castAdd n b) = S.coeff a b := by
  simp only [orthSum, ofUpper, Matrix.of_apply, Fin.addCases_left]
  have h3 : Fin.castAdd n a ≤ Fin.castAdd n b ↔ a ≤ b :=
    Fin.le_iff_val_le_val.trans (Fin.le_iff_val_le_val (a := a) (b := b)).symm
  by_cases h : a ≤ b
  · rw [if_pos (h3.mpr h)]
  · rw [if_neg (fun h' => h (h3.mp h')), S.upper (show id b < id a from not_le.mp h)]

/-- The coefficients of $S\perp T$ in the bottom-bottom block are those of $T$. -/
theorem orthSum_coeff_nn (S : QuadForm A m) (T : QuadForm A n) (a b : Fin n) :
    (orthSum S T).coeff (Fin.natAdd m a) (Fin.natAdd m b) = T.coeff a b := by
  simp only [orthSum, ofUpper, Matrix.of_apply, Fin.addCases_right]
  have h4 : Fin.natAdd m a ≤ Fin.natAdd m b ↔ a ≤ b := by
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val (a := a)]
    change m + a.val ≤ m + b.val ↔ _
    omega
  by_cases h : a ≤ b
  · rw [if_pos (h4.mpr h)]
  · rw [if_neg (fun h' => h (h4.mp h')), T.upper (show id b < id a from not_le.mp h)]

/-- The top-bottom coefficients of $S\perp T$ vanish. -/
theorem orthSum_coeff_cn (S : QuadForm A m) (T : QuadForm A n) (a : Fin m) (b : Fin n) :
    (orthSum S T).coeff (Fin.castAdd n a) (Fin.natAdd m b) = 0 := by
  simp only [orthSum, ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

/-- The bottom-top coefficients of $S\perp T$ vanish. -/
theorem orthSum_coeff_nc (S : QuadForm A m) (T : QuadForm A n) (a : Fin n) (b : Fin m) :
    (orthSum S T).coeff (Fin.natAdd m a) (Fin.castAdd n b) = 0 := by
  simp only [orthSum, ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

/-- The Hessian of $S\perp T$ is block diagonal. -/
theorem det_hessian_orthSum (S : QuadForm A m) (T : QuadForm A n) :
    (orthSum S T).hessian.det = S.hessian.det * T.hessian.det := by
  have h : (orthSum S T).hessian = (Matrix.fromBlocks S.hessian 0 0 T.hessian).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm := by
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [hessian, orthSum_coeff_cc, orthSum_coeff_nn, orthSum_coeff_cn, orthSum_coeff_nc]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/-- Base change commutes with the orthogonal sum. -/
theorem map_orthSum {B : Type*} [CommRing B] (f : A →+* B) (S : QuadForm A m) (T : QuadForm A n) :
    (orthSum S T).map f = orthSum (S.map f) (T.map f) := by
  ext i j
  simp only [QuadForm.map, Matrix.map_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · rw [orthSum_coeff_cc, orthSum_coeff_cc]; simp
  · rw [orthSum_coeff_cn, orthSum_coeff_cn]; simp
  · rw [orthSum_coeff_nc, orthSum_coeff_nc]; simp
  · rw [orthSum_coeff_nn, orthSum_coeff_nn]; simp

end OrthSumCoeff

/-! ### Representations of $\pi T'$ by $\pi T'\perp T$ -/

section OrbitDVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A representation of $\pi T'$ by $\pi T'\perp T$ mod $\pi^k$ ($k \ge 1$, $\bar T$ anisotropic) has bottom block divisible
by $\pi$. -/
theorem qr_bot_dvd {π : R} (T T' : QuadForm R 2)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) {k : ℕ} (hk : 1 ≤ k)
    (Yh : Matrix (Fin (2 + 2)) (Fin 2) R)
    (hx : ∀ i j, π ^ k ∣ ((orthSum (π • T') T).compMat Yh).coeff i j - (π • T').coeff i j) :
    ∀ a j, π ∣ Yh (Fin.natAdd 2 a) j := by
  intro a j
  have h1 := hx j j
  have hv : (fun l => Yh l j) = Fin.append (fun b => Yh (Fin.castAdd 2 b) j) (fun b => Yh (Fin.natAdd 2 b) j) :=
    (qr_append_eta _).symm
  rw [compMat_coeff, if_pos le_rfl, if_pos rfl, hv, eval_orthSum_append, eval_smul_form_rd] at h1
  have h3 : π ∣ T.eval (fun b => Yh (Fin.natAdd 2 b) j) := by
    have h4 : π ∣ π ^ k := dvd_pow_self π (by omega)
    have h6 := h4.trans h1
    have h5 : T.eval (fun b => Yh (Fin.natAdd 2 b) j) =
        (π * T'.eval (fun b => Yh (Fin.castAdd 2 b) j) + T.eval (fun b => Yh (Fin.natAdd 2 b) j) -
          (π • T').coeff j j) - π * (T'.eval (fun b => Yh (Fin.castAdd 2 b) j) - T'.coeff j j) := by
      simp only [smul_coeff, Matrix.smul_apply, smul_eq_mul]; ring
    rw [h5]; exact dvd_sub h6 (dvd_mul_right _ _)
  exact haniso _ h3 a

/-- **Moving columns by $p^{k-1}P(\cdot)$ does not change $Q\circ X$ mod $p^k$** when $H_QP$ and $Q\circ P$ are
divisible by $p$. -/
theorem qr_pert_dvd {A : Type*} [CommRing A] {n r : ℕ} (Q : QuadForm A n) (p : A) (P : Matrix (Fin n) (Fin n) A)
    (hB : ∀ v w : Fin n → A, p ∣ v ⬝ᵥ (Q.hessian *ᵥ (P *ᵥ w))) (hE : ∀ w : Fin n → A, p ∣ Q.eval (P *ᵥ w))
    {k : ℕ} (hk : 1 ≤ k) (X N : Matrix (Fin n) (Fin r) A) (i j : Fin r) :
    p ^ k ∣ (Q.compMat (X + p ^ (k - 1) • (P * N))).coeff i j - (Q.compMat X).coeff i j := by
  obtain ⟨j', rfl⟩ : ∃ j', k = j' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hcol : ∀ m : Fin r, (fun l => (X + p ^ j' • (P * N)) l m) =
      (fun l => X l m) + p ^ j' • (P *ᵥ fun l => N l m) := fun m => by
    ext l; simp [Matrix.add_apply, Matrix.smul_apply]; rfl
  have hD : ∀ v w : Fin n → A, p ^ (j' + 1) ∣ v ⬝ᵥ (Q.hessian *ᵥ (p ^ j' • (P *ᵥ w))) := by
    intro v w
    obtain ⟨c, hc⟩ := hB v w
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul, hc]
    exact ⟨c, by ring⟩
  have hF3 : ∀ w : Fin n → A, p ^ (j' + 1) ∣ Q.eval (p ^ j' • (P *ᵥ w)) := by
    intro w
    obtain ⟨c, hc⟩ := hE w
    rw [eval_smul_vec, hc]
    exact ⟨p ^ j' * c, by ring⟩
  rw [compMat_coeff, compMat_coeff, hcol i, hcol j]
  split_ifs with h1 h2
  · subst h2
    have := eval_polar Q (fun l => X l i) (p ^ j' • (P *ᵥ fun l => N l i))
    rw [show Q.eval ((fun l => X l i) + p ^ j' • (P *ᵥ fun l => N l i)) - Q.eval (fun l => X l i) =
      (fun l => X l i) ⬝ᵥ (Q.hessian *ᵥ (p ^ j' • (P *ᵥ fun l => N l i))) +
        Q.eval (p ^ j' • (P *ᵥ fun l => N l i)) by linear_combination this]
    exact dvd_add (hD _ _) (hF3 _)
  · rw [add_dotProduct, mulVec_add, dotProduct_add, dotProduct_add,
      dot_hessian_comm Q (p ^ j' • (P *ᵥ fun l => N l i)) (fun l => X l j)]
    have e : ∀ a b c d : A, a + b + (c + d) - a = b + c + d := fun a b c d => by ring
    rw [e]
    exact dvd_add (dvd_add (hD _ _) (hD _ _)) (hD _ _)
  · simp

/-- **$A_{\pi^{k+1}}(\pi T'\perp T, \pi T') = q^4A_{\pi^k}(T'\perp\pi T, T')$** ($\bar T$ anisotropic): a representation is
$PZ$ with $P = \mathrm{diag}(1,1,\pi,\pi)$ (`qr_bot_dvd`), and $Q\circ PZ = \pi(Q''\circ Z)$. -/
theorem repCountForm_quat_piT [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π)
    (T T' : QuadForm R 2) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) (k : ℕ) :
    repCountForm (orthSum (π • T') T) (π • T') π (k + 1) =
      q R ^ 4 * repCountForm (orthSum T' (π • T)) T' π k := by
  classical
  have := finite_quot_pow π hπ (k + 1)
  have := finite_quot_pow π hπ k
  have hπ0 := hπ.ne_zero
  set Q := orthSum (π • T') T with hQdef
  set Q' := orthSum T' (π • T) with hQ'def
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) with hmk
  set mk' := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk'
  have hle : Ideal.span {π ^ (k + 1)} ≤ Ideal.span {π ^ k} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ k))
  set ρ := Ideal.Quotient.factor hle with hρ
  set ρM : Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) →+
      Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ k}) := ρ.toAddMonoidHom.mapMatrix with hρM
  set Pb : Matrix (Fin (2 + 2)) (Fin (2 + 2)) (R ⧸ Ideal.span {π ^ (k + 1)}) := qrPm (mk π) with hPb
  set P : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R := qrPm π with hPdef
  set φ : Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) →+
      Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)}) :=
    { toFun := fun Z => Pb * Z
      map_zero' := Matrix.mul_zero _
      map_add' := fun Z Z' => Matrix.mul_add _ _ _ } with hφ
  set S : Set (Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ (k + 1)})) :=
    {Y | (Q.map mk).compMat Y = (π • T').map mk} with hS
  set S' : Set (Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ k})) :=
    {W | (Q'.map mk').compMat W = T'.map mk'} with hS'
  have hPbmap : ∀ Z : Matrix (Fin (2 + 2)) (Fin 2) R, φ (Z.map mk) = (P * Z).map mk := fun Z => by
    show Pb * Z.map mk = _
    rw [Matrix.map_mul, hPb, hPdef, qrPm_map]
  have hcompP : ∀ Z : Matrix (Fin (2 + 2)) (Fin 2) R, Q.compMat (P * Z) = π • Q'.compMat Z := fun Z => by
    rw [← compMat_mul, hQdef, hPdef, compMat_orthSum_Pm, smul_compMat_rd]
  -- (a) every representation is in the image of `φ`
  have hrange : S ⊆ Set.range φ := by
    intro Y hY
    choose f hf using fun (i : Fin (2 + 2)) (j : Fin 2) => Ideal.Quotient.mk_surjective (Y i j)
    set Yh : Matrix (Fin (2 + 2)) (Fin 2) R := Matrix.of f with hYh
    have hYm : Yh.map mk = Y := by ext i j; exact hf i j
    have hx : ∀ i j, π ^ (k + 1) ∣ (Q.compMat Yh).coeff i j - (π • T').coeff i j := by
      rw [← map_mk_eq_iff, ← map_compMat, hYm]; exact hY
    choose c hc using qr_bot_dvd T T' haniso (by omega : 1 ≤ k + 1) Yh hx
    refine ⟨(qrStk (Matrix.of fun a j => Yh (Fin.castAdd 2 a) j) (Matrix.of c)).map mk, ?_⟩
    rw [hPbmap, ← hYm]
    congr 1
    ext i j
    rw [hPdef, qrPm_mul_apply]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [qrStk_top, Fin.append_left, one_mul]; rfl
    · rw [qrStk_bot, Fin.append_right]; exact (hc a j).symm
  -- (b) the preimages agree
  have hpre : φ ⁻¹' S = ρM ⁻¹' S' := by
    ext Z
    choose f hf using fun (i : Fin (2 + 2)) (j : Fin 2) => Ideal.Quotient.mk_surjective (Z i j)
    have hZ : Z = (Matrix.of f).map mk := by ext i j; exact (hf i j).symm
    have hρZ : ρM Z = (Matrix.of f).map mk' := by
      rw [hZ]; ext i j
      simp only [hρM, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, hρ, hmk, hmk']
      exact Ideal.Quotient.factor_mk hle (f i j)
    rw [Set.mem_preimage, Set.mem_preimage, hρZ, hZ, hPbmap, hS, hS', Set.mem_setOf_eq, Set.mem_setOf_eq,
      map_compMat, map_compMat, map_mk_eq_iff, map_mk_eq_iff, hcompP]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [smul_coeff, smul_coeff, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub,
      pow_succ', mul_dvd_mul_iff_left hπ0]
  -- (c) kernels
  have hsurj : Function.Surjective ρM := fun Y => by
    choose f hf using fun i j => Ideal.Quotient.factor_surjective hle (Y i j)
    exact ⟨Matrix.of f, by ext i j; exact hf i j⟩
  have hc : ∀ j, Nat.card (R ⧸ Ideal.span {π ^ j}) = q R ^ j := fun j => card_quot_pow π hπ j
  have hM : ∀ j, Nat.card (Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ j})) = q R ^ (j * 8) := by
    intro j
    rw [show Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ j}) = (Fin (2 + 2) → Fin 2 → R ⧸ Ideal.span {π ^ j})
      from rfl, Nat.card_fun, Nat.card_fun, hc, Nat.card_fin, Nat.card_fin, ← pow_mul, ← pow_mul]
  have hkerρ : Nat.card ρM.ker = q R ^ 8 := by
    have h2 := card_preimage_eq ρM Set.univ (fun Y _ => hsurj Y)
    simp only [Set.preimage_univ, Nat.card_univ] at h2
    rw [hM, hM] at h2
    have hq : 0 < q R ^ (k * 8) := pow_pos q_pos _
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [← pow_add, show 8 + k * 8 = (k + 1) * 8 by ring, h2]
  have hkerφ : Nat.card φ.ker = q R ^ 4 := by
    have e : φ.ker ≃ (Fin 2 → Fin 2 → {t : R ⧸ Ideal.span {π ^ (k + 1)} // mk π * t = 0}) :=
      { toFun := fun Z => fun a j => ⟨Z.1 (Fin.natAdd 2 a) j, by
          have h0 : (qrPm (mk π) * Z.1) (Fin.natAdd 2 a) j = 0 := congrFun (congrFun Z.2 _) j
          rw [qrPm_mul_apply, Fin.append_right] at h0
          exact h0⟩
        invFun := fun t => ⟨qrStk 0 (Matrix.of fun a j => (t a j).1), by
          rw [AddMonoidHom.mem_ker, hφ]
          simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          ext i j
          rw [hPb, qrPm_mul_apply]
          refine Fin.addCases (fun a => ?_) (fun a => ?_) i
          · rw [qrStk_top, Fin.append_left]; simp
          · rw [qrStk_bot, Fin.append_right]; simpa using (t a j).2⟩
        left_inv := fun Z => by
          apply Subtype.ext
          ext i j
          refine Fin.addCases (fun a => ?_) (fun a => ?_) i
          · have := congrFun (congrFun Z.2 (Fin.castAdd 2 a)) j
            simp only [hφ, hPb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, qrPm_mul_apply, Fin.append_left,
              one_mul] at this
            exact (qrStk_top _ _ a j).trans this.symm
          · exact qrStk_bot _ _ a j
        right_inv := fun t => by funext a j; exact Subtype.ext (qrStk_bot _ _ a j) }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_fun, card_ann_pi hπ (by omega), Nat.card_fin, ← pow_mul]
  have h1 := card_preimage_eq φ S hrange
  have h2 := card_preimage_eq ρM S' (fun Y _ => hsurj Y)
  rw [hpre, h2, hkerρ, hkerφ] at h1
  unfold repCountForm
  change Nat.card S = q R ^ 4 * Nat.card S'
  have hq : 0 < q R ^ 4 := pow_pos q_pos _
  apply Nat.eq_of_mul_eq_mul_left hq
  linarith [h1]

end OrbitDVR

/-! ### Column concatenation and the frame stabilizer -/

section Stab

variable {A : Type*} [CommRing A]

/-- The matrix with first two columns `Y` and last two columns `W`. -/
def qrColCat (Y W : Matrix (Fin (2 + 2)) (Fin 2) A) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A :=
  Matrix.of fun i j => Fin.append (fun c => Y i c) (fun c => W i c) j

/-- The first two columns of `qrColCat Y W` are `Y`. -/
theorem qrColCat_cast (Y W : Matrix (Fin (2 + 2)) (Fin 2) A) (i : Fin (2 + 2)) (c : Fin 2) :
    qrColCat Y W i (Fin.castAdd 2 c) = Y i c := by
  simp only [qrColCat, Matrix.of_apply, Fin.append_left]

/-- The last two columns of `qrColCat Y W` are `W`. -/
theorem qrColCat_nat (Y W : Matrix (Fin (2 + 2)) (Fin 2) A) (i : Fin (2 + 2)) (c : Fin 2) :
    qrColCat Y W i (Fin.natAdd 2 c) = W i c := by
  simp only [qrColCat, Matrix.of_apply, Fin.append_right]

/-- $[Y\,|\,W](w_1, w_2) = Yw_1 + Ww_2$. -/
theorem qrColCat_mulVec (Y W : Matrix (Fin (2 + 2)) (Fin 2) A) (w1 w2 : Fin 2 → A) :
    qrColCat Y W *ᵥ Fin.append w1 w2 = Y *ᵥ w1 + W *ᵥ w2 := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_add, qrColCat_cast, qrColCat_nat, Fin.append_left, Fin.append_right,
    Pi.add_apply]

/-- $[Y\,|\,W]\,F = Y$. -/
theorem qrColCat_mul_frame (Y W : Matrix (Fin (2 + 2)) (Fin 2) A) : qrColCat Y W * qrFrame A = Y := by
  ext i j
  rw [mul_qrFrame_apply, qrColCat_cast]

/-- A matrix fixing the frame is `qrColCat F (qrStk B D)`. -/
theorem qr_eq_colCat_of_frame (X : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A) (hF : X * qrFrame A = qrFrame A) :
    X = qrColCat (qrFrame A) (qrStk (Matrix.of fun a c => X (Fin.castAdd 2 a) (Fin.natAdd 2 c))
      (Matrix.of fun a c => X (Fin.natAdd 2 a) (Fin.natAdd 2 c))) := by
  ext i j
  refine Fin.addCases (fun c => ?_) (fun c => ?_) j
  · rw [qrColCat_cast, ← hF, mul_qrFrame_apply]
  · rw [qrColCat_nat]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [qrStk_top]; rfl
    · rw [qrStk_bot]; rfl

/-- The value of $pT'\perp T$ on $[F\,|\,(B;D)]\,(w_1,w_2)$. -/
theorem qr_eval_colCat (p : A) (T' T : QuadForm A 2) (B D : Matrix (Fin 2) (Fin 2) A) (w1 w2 : Fin 2 → A) :
    (orthSum (p • T') T).eval (qrColCat (qrFrame A) (qrStk B D) *ᵥ Fin.append w1 w2) =
      p * T'.eval (w1 + B *ᵥ w2) + T.eval (D *ᵥ w2) := by
  rw [qrColCat_mulVec, qrFrame_mulVec, qrStk_mulVec]
  have : (Fin.append w1 (0 : Fin 2 → A) : Fin (2 + 2) → A) + Fin.append (B *ᵥ w2) (D *ᵥ w2) =
      Fin.append (w1 + B *ᵥ w2) (D *ᵥ w2) := by
    ext i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · simp only [Pi.add_apply, Fin.append_left]
    · simp only [Pi.add_apply, Fin.append_right, Pi.zero_apply, zero_add]
  rw [this, eval_orthSum_append, eval_smul_form_rd]

/-- If $pB = 0$ entrywise then $p\,(Bw)_i = 0$. -/
theorem qr_mul_B_vec_zero (p : A) (B : Matrix (Fin 2) (Fin 2) A) (hB : ∀ a c, p * B a c = 0) (w : Fin 2 → A) (i : Fin 2) :
    p * (B *ᵥ w) i = 0 := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [← mul_assoc, hB, zero_mul]

/-- **The frame stabilizer condition:** with $\det H_{T'}$ a unit, the matrix `[F | (B; D)]` is an isometry of
$pT'\perp T$ iff $pB = 0$ and $D$ is an isometry of $T$. -/
theorem qr_stab_iff (p : A) (T' T : QuadForm A 2) (hT' : IsUnit T'.hessian.det) (B D : Matrix (Fin 2) (Fin 2) A) :
    (orthSum (p • T') T).compMat (qrColCat (qrFrame A) (qrStk B D)) = orthSum (p • T') T ↔
      (∀ a c, p * B a c = 0) ∧ T.compMat D = T := by
  constructor
  · intro h
    have key : ∀ w1 w2 : Fin 2 → A, p * T'.eval (w1 + B *ᵥ w2) + T.eval (D *ᵥ w2) = p * T'.eval w1 + T.eval w2 := by
      intro w1 w2
      have := congrArg (fun S => S.eval (Fin.append w1 w2)) h
      simp only [eval_compMat, qr_eval_colCat, eval_orthSum_append, eval_smul_form_rd] at this
      exact this
    have h0 : ∀ w2, p * T'.eval (B *ᵥ w2) + T.eval (D *ᵥ w2) = T.eval w2 := by
      intro w2
      have := key 0 w2
      rwa [zero_add, eval_zero_vec, mul_zero, zero_add] at this
    have hpair : ∀ w1 w2 : Fin 2 → A, p * (w1 ⬝ᵥ (T'.hessian *ᵥ (B *ᵥ w2))) = 0 := by
      intro w1 w2
      have e1 := eval_polar T' w1 (B *ᵥ w2)
      linear_combination (key w1 w2) - (h0 w2) - p * e1
    have hBzero : ∀ a c, p * B a c = 0 := by
      intro a c
      have hcol : (B *ᵥ Pi.single c (1 : A)) = fun a => B a c := by
        ext a; simp [mulVec, dotProduct, Pi.single_apply]
      have hu : T'.hessian *ᵥ (fun a => p * B a c) = 0 := by
        have e : (fun a => p * B a c) = p • (B *ᵥ Pi.single c (1 : A)) := by rw [hcol]; rfl
        rw [e, mulVec_smul]
        ext a'
        have h1 := hpair (Pi.single a' 1) (Pi.single c 1)
        rw [single_dotProduct, one_mul] at h1
        simpa using h1
      have hinv := congrArg (fun v => T'.hessian⁻¹ *ᵥ v) hu
      simp only [mulVec_mulVec, nonsing_inv_mul _ hT', Matrix.one_mulVec, mulVec_zero] at hinv
      exact congrFun hinv a
    refine ⟨hBzero, eq_of_eval_eq fun w2 => ?_⟩
    rw [eval_compMat, ← h0 w2, mul_eval_eq_zero p T' (qr_mul_B_vec_zero p B hBzero w2), zero_add]
  · rintro ⟨hB, hD⟩
    refine eq_of_eval_eq fun w => ?_
    obtain ⟨w1, w2, rfl⟩ : ∃ w1 w2, w = Fin.append w1 w2 := ⟨_, _, (qr_append_eta w).symm⟩
    rw [eval_compMat, qr_eval_colCat, eval_orthSum_append, eval_smul_form_rd]
    have hs := qr_mul_B_vec_zero p B hB
    have e1 := eval_polar T' w1 (B *ᵥ w2)
    have e2 : p * (w1 ⬝ᵥ (T'.hessian *ᵥ (B *ᵥ w2))) = 0 := by
      rw [dot_hessian_comm, dotProduct_comm]
      exact mul_bil_eq_zero p T'.hessian _ (hs w2)
    have e3 := mul_eval_eq_zero p T' (hs w2)
    have e4 : T.eval (D *ᵥ w2) = T.eval w2 := by
      rw [← eval_compMat, hD]
    rw [e4]
    linear_combination p * e1 + e2 + e3

/-- **The stabilizer of the frame $F$ of $pT'\perp T$** ($\det H_{T'}$ a unit): $(B, D)$ with $pB = 0$ and $D \in O(T)$. -/
def qrStabEquiv (p : A) (T' T : QuadForm A 2) (hT' : IsUnit T'.hessian.det) :
    {X : Matrix (Fin (2 + 2)) (Fin (2 + 2)) A // (orthSum (p • T') T).compMat X = orthSum (p • T') T ∧
        X * qrFrame A = qrFrame A} ≃
      (Fin 2 → Fin 2 → {t : A // p * t = 0}) × {D : Matrix (Fin 2) (Fin 2) A // T.compMat D = T} where
  toFun X := by
    have hX := qr_eq_colCat_of_frame X.1 X.2.2
    have h := (qr_stab_iff p T' T hT' _ _).1 (by rw [← hX]; exact X.2.1)
    exact (fun a c => ⟨X.1 (Fin.castAdd 2 a) (Fin.natAdd 2 c), h.1 a c⟩,
      ⟨Matrix.of fun a c => X.1 (Fin.natAdd 2 a) (Fin.natAdd 2 c), h.2⟩)
  invFun BD := ⟨qrColCat (qrFrame A) (qrStk (Matrix.of fun a c => (BD.1 a c).1) BD.2.1), by
    refine ⟨(qr_stab_iff p T' T hT' _ _).2 ⟨fun a c => (BD.1 a c).2, BD.2.2⟩, qrColCat_mul_frame _ _⟩⟩
  left_inv X := by
    apply Subtype.ext
    exact (qr_eq_colCat_of_frame X.1 X.2.2).symm
  right_inv BD := by
    apply Prod.ext
    · funext a c; exact Subtype.ext (by simp only [qrColCat_nat, qrStk_top]; rfl)
    · exact Subtype.ext (by ext a c; simp only [qrColCat_nat, qrStk_bot]; rfl)

end Stab

/-! ### Counts mod $\pi$ and the two densities -/

section Dens

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]

/-- **$|O(\bar T)| = 2(q+1)$** for a unimodular binary $T$ with $\bar T$ anisotropic at a dyadic prime. -/
theorem card_orth_mod_pi {π : R} (hπ : Irreducible π) (h2π : π ∣ 2) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    Nat.card {D : Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {π ^ 1}) //
      (T.map (Ideal.Quotient.mk _)).compMat D = T.map (Ideal.Quotient.mk _)} = 2 * (q R + 1) := by
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have hfin := finite_quot_pow π hπ 1
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have hmk0 : ∀ x : R, mk x = 0 ↔ π ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  have h2 : (2 : R ⧸ Ideal.span {π ^ 1}) = 0 := by rw [← map_ofNat mk 2, hmk0]; exact h2π
  have hanisoK : ∀ x : Fin 2 → R ⧸ Ideal.span {π ^ 1}, (T.map mk).eval x = 0 → x = 0 := by
    intro x hx
    choose f hf using fun i => Ideal.Quotient.mk_surjective (x i)
    have hxf : x = fun i => mk (f i) := funext fun i => (hf i).symm
    subst hxf
    have : mk (T.eval f) = 0 := by rw [← hx, eval_map_comp']
    have hd := haniso f ((hmk0 _).1 this)
    funext i; exact (hmk0 _).2 (hd i)
  have hb : (T.map mk).coeff 0 1 ≠ 0 := by
    intro h0
    have hdet : (T.map mk).hessian.det = mk T.hessian.det := by
      rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu := hT.map mk
    rw [← hdet] at hu
    have h10 : (T.map mk).coeff 1 0 = 0 := (T.map mk).upper (show (0 : Fin 2) < 1 by decide)
    have : (T.map mk).hessian.det = 0 := by
      simp only [hessian, det_fin_two, Matrix.add_apply, Matrix.transpose_apply, h0, h10]
      rw [show (T.map mk).coeff 0 0 + (T.map mk).coeff 0 0 = 2 * (T.map mk).coeff 0 0 by ring, h2]; ring
    rw [this] at hu; exact not_isUnit_zero hu
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  rw [card_orth_binary_char2 h2 _ hanisoK hb, hcard]

/-- **$\beta_\pi(T, T) = 2(q+1)/q$** for a unimodular binary $T$ with $\bar T$ anisotropic at a dyadic prime. -/
theorem localDensityForm_binary_aniso {π : R} (hπ : Irreducible π) (h2π : π ∣ 2) (T : QuadForm R 2)
    (hT : IsUnit T.hessian.det) (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) :
    localDensityForm T T π = 2 * ((q R : ℝ) + 1) / q R := by
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT le_rfl]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  unfold repCountForm
  rw [card_orth_mod_pi hπ h2π T hT haniso]
  push_cast
  norm_num

/-- Representations of $T'$ by $T'\perp Z$ with $Z$ identically zero are the representations of $T'$ by $T'$ in the top block. -/
theorem qr_compMat_orthSum_zero_iff {A : Type*} [CommRing A] (T' Z : QuadForm A 2) (hZ : ∀ x, Z.eval x = 0)
    (Y : Matrix (Fin (2 + 2)) (Fin 2) A) :
    (orthSum T' Z).compMat Y = T' ↔ T'.compMat (Matrix.of fun a j => Y (Fin.castAdd 2 a) j) = T' := by
  have ev : ∀ w, ((orthSum T' Z).compMat Y).eval w = (T'.compMat (Matrix.of fun a j => Y (Fin.castAdd 2 a) j)).eval w := by
    intro w
    rw [eval_compMat, eval_compMat]
    conv_lhs => rw [← qrStk_top_bot Y, qrStk_mulVec, eval_orthSum_append, hZ, add_zero]
  constructor
  · intro h; exact eq_of_eval_eq fun w => by rw [← ev, h]
  · intro h; exact eq_of_eval_eq fun w => by rw [ev, h]

/-- **$\beta_\pi(T'\perp\pi T, T') = 2(q+1)/q$** for a unimodular binary $T'$ with $\bar T'$ anisotropic at a dyadic prime:
the count mod $\pi$ is $q^4\cdot|O(\bar T')|$. -/
theorem localDensityForm_quat_piU {π : R} (hπ : Irreducible π) (h2π : π ∣ 2) (T T' : QuadForm R 2)
    (hT' : IsUnit T'.hessian.det) (haniso' : ∀ x : Fin 2 → R, π ∣ T'.eval x → ∀ i, π ∣ x i) :
    localDensityForm (orthSum T' (π • T)) T' π = 2 * ((q R : ℝ) + 1) / q R := by
  rw [localDensityForm_eq_of_isUnit _ _ π hπ hT' (by norm_num)]
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hmax : (Ideal.span {π ^ 1}).IsMaximal := by
    rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  let _ : Field (R ⧸ Ideal.span {π ^ 1}) := Ideal.Quotient.field _
  have hfin := finite_quot_pow π hπ 1
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ 1}) with hmk
  have hmk0 : ∀ x : R, mk x = 0 ↔ π ∣ x := fun x => by
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  have hπ0 : mk π = 0 := (hmk0 _).2 dvd_rfl
  have hcard : Nat.card (R ⧸ Ideal.span {π ^ 1}) = q R := by rw [card_quot_pow π hπ, pow_one]
  have hZ : ∀ x, ((π • T).map mk).eval x = 0 := by
    intro x; rw [map_smul_form_rd, hπ0, eval_smul_form_rd, zero_mul]
  have hcount : repCountForm (orthSum T' (π • T)) T' π 1 = q R ^ 4 * (2 * (q R + 1)) := by
    unfold repCountForm
    simp only [map_orthSum]
    have e : {Y : Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ 1}) //
        (orthSum (T'.map mk) ((π • T).map mk)).compMat Y = T'.map mk} ≃
        {D : Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {π ^ 1}) // (T'.map mk).compMat D = T'.map mk} ×
          Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {π ^ 1}) :=
      { toFun := fun Y => (⟨Matrix.of fun a j => Y.1 (Fin.castAdd 2 a) j,
          (qr_compMat_orthSum_zero_iff _ _ hZ Y.1).1 Y.2⟩, Matrix.of fun a j => Y.1 (Fin.natAdd 2 a) j)
        invFun := fun p => ⟨qrStk p.1.1 p.2, (qr_compMat_orthSum_zero_iff _ _ hZ _).2 (by
          have : (Matrix.of fun a j => (qrStk p.1.1 p.2) (Fin.castAdd 2 a) j) = p.1.1 := by
            ext a j; exact qrStk_top _ _ a j
          rw [this]; exact p.1.2)⟩
        left_inv := fun Y => Subtype.ext (qrStk_top_bot Y.1)
        right_inv := fun p => by
          apply Prod.ext
          · exact Subtype.ext (by ext a j; exact qrStk_top _ _ a j)
          · ext a j; exact qrStk_bot _ _ a j }
    have hmat : Nat.card (Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {π ^ 1})) = q R ^ 4 := by
      rw [show Matrix (Fin 2) (Fin 2) (R ⧸ Ideal.span {π ^ 1}) = (Fin 2 → Fin 2 → R ⧸ Ideal.span {π ^ 1}) from rfl,
        Nat.card_fun, Nat.card_fun, hcard, Nat.card_fin, ← pow_mul]
    rw [Nat.card_congr e, Nat.card_prod, card_orth_mod_pi hπ h2π T' hT' haniso', hmat]
    ring
  rw [hcount]
  have h5 : ((2 + 2) * 2 - 2 * (2 + 1) / 2 : ℕ) = 5 := by norm_num
  rw [h5]
  push_cast
  field_simp

end Dens

/-! ### The exact isometry with a prescribed frame -/

section Exact

variable {A : Type*} [CommRing A]

/-- $T(e_i) = c_{ii}$ for a binary form. -/
theorem qr_eval_one_col (T : QuadForm A 2) (i : Fin 2) :
    T.eval (fun b => (1 : Matrix (Fin 2) (Fin 2) A) b i) = T.coeff i i := by
  rw [eval_binary]; fin_cases i <;> simp [Matrix.one_apply]

/-- $e_i^{\mathsf T}He_j = H_{ij}$. -/
theorem qr_one_col_dot (H : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    (fun b => (1 : Matrix (Fin 2) (Fin 2) A) b i) ⬝ᵥ (H *ᵥ fun b => (1 : Matrix (Fin 2) (Fin 2) A) b j) = H i j := by
  fin_cases i <;> fin_cases j <;> simp [dotProduct, mulVec, Matrix.one_apply]

/-- $T_1 = (pT'\perp T)\circ(-E;\,1) \equiv T$ mod $p$. -/
theorem qr_T1_dvd (p : A) (T' T : QuadForm A 2) (E : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    p ∣ ((orthSum (p • T') T).compMat (qrStk (-E) 1)).coeff i j - T.coeff i j := by
  have hcol : ∀ i, (fun l => qrStk (-E) (1 : Matrix (Fin 2) (Fin 2) A) l i) =
      Fin.append (fun a => (-E) a i) (fun b => (1 : Matrix (Fin 2) (Fin 2) A) b i) := fun i => rfl
  rw [compMat_coeff]
  split_ifs with h1 h2
  · subst h2
    rw [hcol, eval_orthSum_append, eval_smul_form_rd, qr_eval_one_col]
    exact ⟨T'.eval _, by ring⟩
  · rw [hcol, hcol, bil_orthSum_gen]
    simp only [Fin.append_left, Fin.append_right]
    rw [hessian_smul_form, smul_mulVec, dotProduct_smul, qr_one_col_dot]
    have hlt : i < j := lt_of_le_of_ne h1 h2
    have h0 : T.coeff j i = 0 := T.upper (show id i < id j from hlt)
    have : T.hessian i j = T.coeff i j := by simp [hessian, h0]
    rw [this]
    exact ⟨(fun a => (-E) a i) ⬝ᵥ (T'.hessian *ᵥ fun a => (-E) a j), by rw [smul_eq_mul]; ring⟩
  · rw [T.upper (show id j < id i from not_le.mp h1)]; simp

/-- $(yw)\cdot(H E u) = w\cdot(y^{\mathsf T}HE\,u)$. -/
theorem qr_dot3 (y H E : Matrix (Fin 2) (Fin 2) A) (w u : Fin 2 → A) :
    (y *ᵥ w) ⬝ᵥ (H *ᵥ (E *ᵥ u)) = w ⬝ᵥ ((yᵀ * H * E) *ᵥ u) := by
  have key : ∀ v, w ⬝ᵥ (yᵀ *ᵥ v) = (y *ᵥ w) ⬝ᵥ v := fun v => by rw [dotProduct_mulVec, vecMul_transpose]
  rw [← mulVec_mulVec, ← mulVec_mulVec, key]

end Exact

section ExactR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- $y_1$ is invertible: $y_1^{\mathsf T}H_{T'}y_1 \equiv H_{T'}$ mod $\pi$. -/
theorem qr_det_y1 {π : R} (hπ : Irreducible π) (T T' : QuadForm R 2) (hT' : IsUnit T'.hessian.det)
    (y1 z : Matrix (Fin 2) (Fin 2) R)
    (hgram : y1ᵀ * T'.hessian * y1 + π • (zᵀ * T.hessian * z) = T'.hessian) : IsUnit y1.det := by
  apply dvr_isUnit_of_not_dvd hπ
  intro hdvd
  set mk := Ideal.Quotient.mk (Ideal.span {π}) with hmk
  have hmk0 : ∀ x : R, mk x = 0 ↔ π ∣ x := fun x => by
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hπ0 : mk π = 0 := (hmk0 _).2 dvd_rfl
  have h0 : (RingHom.mapMatrix mk) (π • (zᵀ * T.hessian * z)) = 0 := by
    ext i j; simp [RingHom.mapMatrix_apply, hπ0]
  have e := congrArg (RingHom.mapMatrix mk) hgram
  rw [map_add, h0, add_zero, map_mul, map_mul] at e
  have h1 := congrArg Matrix.det e
  simp only [RingHom.mapMatrix_apply, Matrix.transpose_map, det_mul, det_transpose] at h1
  have d1 : (y1.map mk).det = mk y1.det := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have d2 : (T'.hessian.map mk).det = mk T'.hessian.det := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [d1, d2, (hmk0 _).2 hdvd] at h1
  simp only [zero_mul, mul_zero] at h1
  exact dvr_not_dvd_of_isUnit hπ hT' ((hmk0 _).1 h1.symm)

/-- **Every exact representation $PZ_t$ of $\pi T'$ by $\pi T'\perp T$ (with $Q''\circ Z_t = T'$) is the frame of an exact
isometry.** The orthogonal complement is spanned by $(-EN; N)$ with $E = (y_1^{\mathsf T}H_{T'})^{-1}z^{\mathsf T}H_T$ and
$N$ found by Hensel's lemma from $T_1\circ N = T$, $T_1 = (\pi T'\perp T)\circ(-E; 1) \equiv T$ mod $\pi$. -/
theorem qr_exact_isometry [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (T T' : QuadForm R 2) (hT : IsUnit T.hessian.det) (hT' : IsUnit T'.hessian.det)
    (Zt : Matrix (Fin (2 + 2)) (Fin 2) R) (hZ : (orthSum T' (π • T)).compMat Zt = T') :
    ∃ X : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R,
      (orthSum (π • T') T).compMat X = orthSum (π • T') T ∧ X * qrFrame R = qrPm π * Zt := by
  classical
  obtain ⟨y1, z, rfl⟩ : ∃ y1 z, Zt = qrStk y1 z := ⟨_, _, (qrStk_top_bot Zt).symm⟩
  set Q := orthSum (π • T') T with hQ
  have hgram : y1ᵀ * T'.hessian * y1 + π • (zᵀ * T.hessian * z) = T'.hessian := by
    have h := hessian_compMat (orthSum T' (π • T)) (qrStk y1 z)
    rw [hZ, qr_gram, hessian_smul_form] at h
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact h.symm
  have hy : IsUnit y1.det := qr_det_y1 hπ T T' hT' y1 z hgram
  have hG : IsUnit (y1ᵀ * T'.hessian).det := by rw [det_mul, det_transpose]; exact hy.mul hT'
  set E : Matrix (Fin 2) (Fin 2) R := (y1ᵀ * T'.hessian)⁻¹ * (zᵀ * T.hessian) with hEdef
  have hE : y1ᵀ * T'.hessian * E = zᵀ * T.hessian := by
    rw [hEdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  -- Hensel for `T₁ ∘ N = T`
  set T₁ : QuadForm R 2 := Q.compMat (qrStk (-E) 1) with hT₁
  have hx0 : ∀ p : UpperIdx 2, π ^ 1 ∣ DVR.formF T₁ (fun p : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) R) p.1 p.2) p -
      T.coeff p.1.1 p.1.2 := by
    intro p
    have : toMat (fun p : Fin 2 × Fin 2 => (1 : Matrix (Fin 2) (Fin 2) R) p.1 p.2) = 1 := by ext i j; rfl
    rw [DVR.formF, this, compMat_one, pow_one]
    exact qr_T1_dvd π T' T E p.1.1 p.1.2
  obtain ⟨y, hy', -⟩ := newton_lift hπ (DVR.formF T₁) (DVR.formD T₁) (DVR.formF_add_smul T₁)
    (fun p => T.coeff p.1.1 p.1.2) 0 1 (by norm_num)
    (fun x hx c => DVR.formD_surj T₁ T π hπ 0 1 (by simp) (by simpa using dvr_not_dvd_of_isUnit hπ hT) (by omega) x hx c)
    _ hx0
  have hN : T₁.compMat (toMat y) = T := ext_upper fun i j hij => congrFun hy' ⟨(i, j), hij⟩
  set N : Matrix (Fin 2) (Fin 2) R := toMat y with hNdef
  -- the isometry
  have hY : Q.compMat (qrPm π * qrStk y1 z) = π • T' := by
    rw [← compMat_mul, hQ, compMat_orthSum_Pm, smul_compMat_rd, hZ]
  have hW : Q.compMat (qrStk (-E) 1 * N) = T := by rw [← compMat_mul]; exact hN
  refine ⟨qrColCat (qrPm π * qrStk y1 z) (qrStk (-E) 1 * N), ?_, qrColCat_mul_frame _ _⟩
  refine eq_of_eval_eq fun w => ?_
  obtain ⟨w1, w2, rfl⟩ : ∃ w1 w2, w = Fin.append w1 w2 := ⟨_, _, (qr_append_eta w).symm⟩
  rw [eval_compMat, qrColCat_mulVec, hQ, eval_orthSum_append]
  rw [← hQ]
  have e1 := eval_polar Q ((qrPm π * qrStk y1 z) *ᵥ w1) ((qrStk (-E) 1 * N) *ᵥ w2)
  have hYe : Q.eval ((qrPm π * qrStk y1 z) *ᵥ w1) = (π • T').eval w1 := by rw [← eval_compMat, hY]
  have hWe : Q.eval ((qrStk (-E) 1 * N) *ᵥ w2) = T.eval w2 := by rw [← eval_compMat, hW]
  have hcross : ((qrPm π * qrStk y1 z) *ᵥ w1) ⬝ᵥ (Q.hessian *ᵥ ((qrStk (-E) 1 * N) *ᵥ w2)) = 0 := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, qrStk_mulVec, qrStk_mulVec, qrPm_mulVec, hQ, bil_orthSum_gen]
    simp only [Fin.append_left, Fin.append_right, Matrix.one_mulVec]
    rw [hessian_smul_form, smul_mulVec, dotProduct_smul, Matrix.neg_mulVec, mulVec_neg, dotProduct_neg,
      qr_dot3, hE, show (fun a => π * (z *ᵥ w1) a) = π • (z *ᵥ w1) from rfl, smul_dotProduct]
    have h3 := qr_dot3 z T.hessian 1 w1 (N *ᵥ w2)
    simp only [Matrix.mul_one, Matrix.one_mulVec] at h3
    rw [h3, Matrix.mulVec_mulVec]
    simp only [smul_eq_mul]
    ring
  rw [hQ] at e1 hYe hWe hcross
  linear_combination e1 + hYe + hWe + hcross

end ExactR

/-! ### The frame orbit is every representation of $\pi T'$ -/

section Orbit

/-- $p$ divides $v^{\mathsf T}H_Q\,\mathrm{diag}(1,1,p,p)\,w$ for $Q = pT'\perp T$. -/
theorem qr_hB {A : Type*} [CommRing A] (p : A) (T' T : QuadForm A 2) (v w : Fin (2 + 2) → A) :
    p ∣ v ⬝ᵥ ((orthSum (p • T') T).hessian *ᵥ (qrPm p *ᵥ w)) := by
  rw [bil_orthSum_gen, qrPm_mulVec]
  simp only [Fin.append_left, Fin.append_right]
  rw [hessian_smul_form, smul_mulVec, dotProduct_smul,
    show (fun a => p * w (Fin.natAdd 2 a)) = p • (fun a => w (Fin.natAdd 2 a)) from rfl, mulVec_smul,
    dotProduct_smul]
  apply dvd_add <;> rw [smul_eq_mul] <;> exact dvd_mul_right _ _

/-- $p$ divides $Q(\mathrm{diag}(1,1,p,p)\,w)$ for $Q = pT'\perp T$. -/
theorem qr_hE {A : Type*} [CommRing A] (p : A) (T' T : QuadForm A 2) (w : Fin (2 + 2) → A) :
    p ∣ (orthSum (p • T') T).eval (qrPm p *ᵥ w) := by
  rw [eval_orthSum_gen, qrPm_mulVec]
  simp only [Fin.append_left, Fin.append_right]
  rw [eval_smul_form_rd, show (fun a => p * w (Fin.natAdd 2 a)) = p • (fun a => w (Fin.natAdd 2 a)) from rfl,
    eval_smul_vec]
  exact dvd_add (dvd_mul_right _ _) ⟨p * T.eval fun a => w (Fin.natAdd 2 a), by ring⟩

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The frame orbit of $\pi T'\perp T$ mod $\pi^k$ is every representation of $\pi T'$** ($k \ge 2$, $T, T'$ unimodular,
$\bar T$ anisotropic). -/
theorem qr_orbit [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (T T' : QuadForm R 2) (hT : IsUnit T.hessian.det) (hT' : IsUnit T'.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i) {k : ℕ} (hk : 2 ≤ k)
    (Y : Matrix (Fin (2 + 2)) (Fin 2) (R ⧸ Ideal.span {π ^ k}))
    (hY : ((orthSum (π • T') T).map (Ideal.Quotient.mk _)).compMat Y = (π • T').map (Ideal.Quotient.mk _)) :
    ∃ X, ((orthSum (π • T') T).map (Ideal.Quotient.mk _)).compMat X =
        (orthSum (π • T') T).map (Ideal.Quotient.mk _) ∧ X * qrFrame _ = Y := by
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k}) with hmk
  set Q := orthSum (π • T') T with hQdef
  set Q' := orthSum T' (π • T) with hQ'def
  set P : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R := qrPm π with hPdef
  have hπ0 := hπ.ne_zero
  -- lift `Y`
  choose f hf using fun (i : Fin (2 + 2)) (j : Fin 2) => Ideal.Quotient.mk_surjective (Y i j)
  set Yh : Matrix (Fin (2 + 2)) (Fin 2) R := Matrix.of f with hYh
  have hYm : Yh.map mk = Y := by ext i j; exact hf i j
  have hx : ∀ i j, π ^ k ∣ (Q.compMat Yh).coeff i j - (π • T').coeff i j := by
    rw [← map_mk_eq_iff, ← map_compMat, hYm]; exact hY
  choose c hc using qr_bot_dvd T T' haniso (by omega : 1 ≤ k) Yh hx
  set Zh : Matrix (Fin (2 + 2)) (Fin 2) R :=
    qrStk (Matrix.of fun a j => Yh (Fin.castAdd 2 a) j) (Matrix.of c) with hZh
  have hPZ : P * Zh = Yh := by
    ext i j
    rw [hPdef, qrPm_mul_apply]
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hZh, qrStk_top, Fin.append_left, one_mul]; rfl
    · rw [hZh, qrStk_bot, Fin.append_right]; exact (hc a j).symm
  have hcompP : ∀ Z : Matrix (Fin (2 + 2)) (Fin 2) R, Q.compMat (P * Z) = π • Q'.compMat Z := fun Z => by
    rw [← compMat_mul, hQdef, hPdef, compMat_orthSum_Pm, smul_compMat_rd]
  have hxZ : ∀ p : DVR.UpperIdx 2, π ^ (k - 1) ∣ DVR.formF Q' (fun li => Zh li.1 li.2) p - T'.coeff p.1.1 p.1.2 := by
    intro p
    have h1 := hx p.1.1 p.1.2
    rw [← hPZ, hcompP, smul_coeff, smul_coeff, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_sub, show k = k - 1 + 1 by omega, pow_succ', mul_dvd_mul_iff_left hπ0] at h1
    exact h1
  -- Hensel
  obtain ⟨y, hy, hyx⟩ := newton_lift hπ (DVR.formF Q') (DVR.formD Q') (DVR.formF_add_smul Q')
    (fun p => T'.coeff p.1.1 p.1.2) 0 (k - 1) (by omega)
    (fun x hx c => DVR.formD_surj Q' T' π hπ 0 (k - 1) (by simp)
      (by simpa using dvr_not_dvd_of_isUnit hπ hT') (by omega) x hx c) _ hxZ
  set Zt := DVR.toMat y with hZt
  have hQZt : Q'.compMat Zt = T' := ext_upper fun i j hij => congrFun hy ⟨(i, j), hij⟩
  -- the exact isometry
  obtain ⟨X, hX, hXF⟩ := qr_exact_isometry hπ T T' hT hT' Zt hQZt
  -- the correction
  have hdiff : ∀ i j, π ^ (k - 1) ∣ Zh i j - Zt i j := by
    intro i j
    have := hyx (i, j)
    rw [Nat.sub_zero] at this
    have e : Zh i j - Zt i j = -(y (i, j) - Zh i j) := by simp [hZt, DVR.toMat]
    rw [e]; exact (dvd_neg).mpr this
  choose M hM using hdiff
  set N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R := qrColCat (Matrix.of M) 0 with hNdef
  set Xc := X + π ^ (k - 1) • (P * N) with hXc
  have hXcF : Xc * qrFrame R = Yh := by
    have hNF : N * qrFrame R = Matrix.of M := qrColCat_mul_frame _ _
    rw [hXc, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hNF, hXF, ← hPZ, ← Matrix.mul_smul,
      ← Matrix.mul_add]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    linear_combination -(hM i j)
  refine ⟨Xc.map mk, ?_, ?_⟩
  · rw [map_compMat, map_mk_eq_iff]
    intro i j
    have := qr_pert_dvd Q π P (qr_hB π T' T) (qr_hE π T' T) (by omega : 1 ≤ k) X N i j
    rw [hX] at this
    exact this
  · calc Xc.map mk * qrFrame _ = (Xc * qrFrame R).map mk := by (rw [Matrix.map_mul, qrFrame_map]; rfl)
      _ = Y := by rw [hXcF, hYm]

end Orbit

/-! ### The self-density -/

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The self-density of $\pi T'\perp T$ at a dyadic prime** ($T, T'$ binary with $\det H_T$, $\det H_{T'}$ units and
$\bar T$, $\bar T'$ anisotropic):
$$\beta_\pi(\pi T'\perp T, \pi T'\perp T) = 4q(q+1)^2.$$
This is the quaternary lattice of the maximal order of a quaternion division algebra over a dyadic field (repository
normalization $\beta = 2\alpha$: Shimura's $\alpha_2 = 36$ for the Hurwitz order over $\mathbb Z_2$, $72 = 4\cdot2\cdot9$).
(The hypothesis `h20 : 2 ≠ 0` is not used by the argument; it is kept to match the interface of the ternary analogue.)
*Proof.* Orbit--stabilizer for the frame of the $\pi T'$ block: $\beta(Q,Q) = q^3\,\beta(Q'', T')\,\beta(T,T)$ with
$Q'' = T'\perp\pi T$ and $\beta(Q'', T') = \beta(T, T) = 2(q+1)/q$. -/
@[kb "shimura1999" "Lemma 3.7(2), Prop. 3.9 (t = 4: the maximal order of the quaternion division algebra)"]
theorem localDensityForm_quaternary_dyadic [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π) (h20 : (2 : R) ≠ 0) (h2π : π ∣ 2)
    (T T' : QuadForm R 2) (hT : IsUnit T.hessian.det) (hT' : IsUnit T'.hessian.det)
    (haniso : ∀ x : Fin 2 → R, π ∣ T.eval x → ∀ i, π ∣ x i)
    (haniso' : ∀ x : Fin 2 → R, π ∣ T'.eval x → ∀ i, π ∣ x i) :
    localDensityForm (orthSum (π • T') T) (orthSum (π • T') T) π = 4 * (q R : ℝ) * ((q R : ℝ) + 1) ^ 2 := by
  classical
  set Q := orthSum (π • T') T with hQdef
  set Q' := orthSum T' (π • T) with hQ'def
  have hQnd : Q.Nondegenerate := by
    rw [QuadForm.Nondegenerate, hQdef, det_hessian_orthSum, hessian_smul_form, det_smul]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hT'.ne_zero) hT.ne_zero
  have hTnd : T.Nondegenerate := hT.ne_zero
  have hT'nd : T'.Nondegenerate := hT'.ne_zero
  obtain ⟨d, hd, hd'⟩ := exists_pow_dvd_not_dvd π hπ hQnd
  have e1 := localDensityForm_eventually_eq Q Q hQnd π hπ le_rfl
  have e2 := localDensityForm_eventually_eq Q' T' hT'nd π hπ (by norm_num)
  have e3 := localDensityForm_eventually_eq T T hTnd π hπ le_rfl
  obtain ⟨m, h1, h2, h3, hm⟩ := (((Filter.tendsto_add_atTop_nat 1).eventually e1).and (e2.and
    (((Filter.tendsto_add_atTop_nat 1).eventually e3).and (Filter.eventually_gt_atTop (d + 1))))).exists
  have hβ' := localDensityForm_quat_piU hπ h2π T T' hT' haniso'
  have hβT := localDensityForm_binary_aniso hπ h2π T hT haniso
  rw [← h2] at hβ'
  rw [← h3] at hβT
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have h6 : ((2 + 2) * (2 + 2) - (2 + 2) * (2 + 2 + 1) / 2 : ℕ) = 6 := by norm_num
  have h5 : ((2 + 2) * 2 - 2 * (2 + 1) / 2 : ℕ) = 5 := by norm_num
  have h1' : (2 * 2 - 2 * (2 + 1) / 2 : ℕ) = 1 := by norm_num
  simp only [h6, h5, h1'] at h1 hβ' hβT
  have hA' : (repCountForm Q' T' π m : ℝ) = 2 * ((q R : ℝ) + 1) / q R * (q R : ℝ) ^ (m * 5) := by
    rw [← hβ']; field_simp
  have hAT : (repCountForm T T π (m + 1) : ℝ) = 2 * ((q R : ℝ) + 1) / q R * (q R : ℝ) ^ ((m + 1) * 1) := by
    rw [← hβT]; field_simp
  rw [← h1]
  -- the orbit–stabilizer count at level `m + 1`
  have := finite_quot_pow π hπ (m + 1)
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) with hmk
  have hQmap : Q.map mk = orthSum (mk π • T'.map mk) (T.map mk) := by
    rw [hQdef, map_orthSum, map_smul_form_rd]
  have hT'u : IsUnit (T'.map mk).hessian.det := by
    rw [hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hT'.map _
  have hcount : repCountForm Q Q π (m + 1) =
      (q R ^ 4 * repCountForm Q' T' π m) * (q R ^ 4 * repCountForm T T π (m + 1)) := by
    rw [← repCountForm_quat_piT hπ T T' haniso m]
    unfold repCountForm
    rw [card_compMat_eq_frameOrbit_mul _ (fun X hX => isUnit_det_of_compMat_eq _ π hπ d (m + 1) hd hd'
      (by omega) X hX) (qrFrame _)]
    congr 1
    · unfold frameOrbit
      refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
      constructor
      · rintro ⟨X, hX, rfl⟩
        rw [← compMat_mul, hX, hQmap, compMat_orthSum_frame, map_smul_form_rd]
      · intro hY
        exact qr_orbit hπ T T' hT hT' haniso (by omega) Y hY
    · rw [hQmap, Nat.card_congr (qrStabEquiv (mk π) (T'.map mk) (T.map mk) hT'u), Nat.card_prod,
        Nat.card_fun, Nat.card_fun, card_ann_pi hπ (by omega), Nat.card_fin, ← pow_mul]
  rw [hcount]
  push_cast
  rw [hA', hAT]
  field_simp
  ring

end Main

end QuadFormsKB.Tamagawa
