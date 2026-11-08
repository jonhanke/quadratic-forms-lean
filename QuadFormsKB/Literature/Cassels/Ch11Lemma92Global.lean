/-
# Cassels, Chapter 11, proof of Lemma 9.2: global linear algebra

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2 (pp. 246–248): the
space $V^{(2)}$ of vectors normal to $\mathbf u$ and the lattice $\mathbb Z^4 \cap V^{(2)}$ ((9.50), (9.59)).

**Proves.**
* `exists_kernel_basis`: for a primitive $r \in \mathbb Z^4$ there are a $4 \times 3$ integer matrix $W$ and a $3 \times 4$
  integer matrix $\tilde W$ with $\tilde WW = 1$, $r \cdot Wz = 0$, and $W\tilde Wx = x$ whenever $r \cdot x = 0$: the columns of
  $W$ are a basis of $\{x \in \mathbb Z^4 : r \cdot x = 0\}$ (Cassels, Ch. 9, Lemma 2.1, Corollary, for the row $r$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Shape

open Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-- **A basis of the integer vectors normal to a primitive row** (Cassels, Ch. 9, Lemma 2.1, Corollary): for $r \in \mathbb Z^4$
with coprime coordinates there are $W \in M_{4 \times 3}(\mathbb Z)$, $\tilde W \in M_{3 \times 4}(\mathbb Z)$ with $\tilde WW = 1$,
$r \cdot Wz = 0$ for all $z$, and $W\tilde Wx = x$ for every $x \in \mathbb Z^4$ with $r \cdot x = 0$. *Proof:* $r$ is the first
row of some $V \in \mathrm{GL}_4(\mathbb Z)$; $W$ is the last three columns of $V^{-1}$, $\tilde W$ the last three rows of $V$. -/
theorem exists_kernel_basis (r : Fin 4 → ℤ) (hr : Finset.univ.gcd r = 1) :
    ∃ (W : Matrix (Fin 4) (Fin 3) ℤ) (Wt : Matrix (Fin 3) (Fin 4) ℤ), Wt * W = 1 ∧
      (∀ z : Fin 3 → ℤ, r ⬝ᵥ (W *ᵥ z) = 0) ∧ (∀ x : Fin 4 → ℤ, r ⬝ᵥ x = 0 → W *ᵥ (Wt *ᵥ x) = x) ∧
      ∃ c0 : Fin 4 → ℤ, W * Wt + Matrix.vecMulVec c0 r = 1 := by
  obtain ⟨T, hT⟩ := (Siegel.exists_basis_first_iff_gcd (n := 4) (by norm_num) r).2 hr
  set V : Matrix (Fin 4) (Fin 4) ℤ := (T.val)ᵀ with hV
  set U : Matrix (Fin 4) (Fin 4) ℤ := ((T⁻¹ : GL (Fin 4) ℤ).val)ᵀ with hU
  have hVU : V * U = 1 := by
    rw [hV, hU, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  have hUV : U * V = 1 := by
    rw [hV, hU, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
  have hrow : ∀ i, V 0 i = r i := by
    intro i
    have := congrFun hT i
    simp only [mulVec, dotProduct, Pi.single_apply] at this
    rw [hV, Matrix.transpose_apply, ← this]
    simp
  set W : Matrix (Fin 4) (Fin 3) ℤ := Matrix.of fun i j => U i j.succ with hW
  set Wt : Matrix (Fin 3) (Fin 4) ℤ := Matrix.of fun j i => V j.succ i with hWt
  refine ⟨W, Wt, ?_, fun z => ?_, fun x hx => ?_, fun i => U i 0, ?_⟩
  · ext j k
    have := congrFun (congrFun hVU j.succ) k.succ
    simp only [Matrix.mul_apply, Matrix.one_apply, Fin.succ_inj] at this
    simpa [hW, hWt, Matrix.mul_apply, Matrix.one_apply] using this
  · have h0 : ∀ j : Fin 3, ∑ i, r i * U i j.succ = 0 := by
      intro j
      have := congrFun (congrFun hVU 0) j.succ
      rw [Matrix.mul_apply, Matrix.one_apply, if_neg (Fin.succ_ne_zero j).symm] at this
      rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [hrow]
    have e : r ⬝ᵥ (W *ᵥ z) = ∑ j, z j * ∑ i, r i * U i j.succ := by
      simp only [hW, mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]; simp [h0]
  · have hx0 : ∑ l, V 0 l * x l = 0 := by
      rw [← hx]; simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => by rw [hrow]
    have hUVx : U *ᵥ (V *ᵥ x) = x := by rw [mulVec_mulVec, hUV, one_mulVec]
    conv_rhs => rw [← hUVx]
    funext i
    simp only [hW, hWt, mulVec, dotProduct, Matrix.of_apply]
    rw [Fin.sum_univ_succ (f := fun k => U i k * ∑ l, V k l * x l), hx0, mul_zero, zero_add]
  · ext i j
    have := congrFun (congrFun hUV i) j
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hrow] at this
    rw [Matrix.add_apply, Matrix.vecMulVec_apply, ← this]
    simp only [hW, hWt, Matrix.mul_apply, Matrix.of_apply]
    ring

/-! ### The form $h = f \circ W$ and the splitting $f(b\mathbf u + Wz) = f(\mathbf u)b^2 + h(z)$ -/

section Split

variable {R : Type*} [CommRing R]

theorem bl_col_eq (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) (i j : Fin 3) :
    bl Q (Ch11L92.col B i) (Ch11L92.col B j) = (Bᵀ * Q.hessian * B) i j := by
  rw [Ch11L92.col, Ch11L92.col, mulVec_single_one, mulVec_single_one]
  simp only [bl, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    simp only [Matrix.col_apply]; ring

/-- **The Hessian of the Gram form** $y \mapsto Q(By)$ is $B^{\mathsf T}H_QB$. -/
theorem gramOf_hessian (Q : QuadForm R 4) (B : Matrix (Fin 4) (Fin 3) R) :
    (gramOf Q B).hessian = Bᵀ * Q.hessian * B := by
  ext i j
  rw [← bl_col_eq]
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [gramOf_coeff Q B i j h.le, (gramOf Q B).upper h, if_neg h.ne, add_zero]
  · rw [gramOf_coeff Q B i i le_rfl, if_pos rfl, bl_self]; ring
  · rw [gramOf_coeff Q B j i h.le, (gramOf Q B).upper h, if_neg h.ne, zero_add, bl_comm]

/-- **The splitting (9.5) for $n = 4$**: if $B(\mathbf u, Wz) = 0$ for all $z$ then
$f(b\mathbf u + Wz) = f(\mathbf u)b^2 + h(z)$ with $h = $ `gramOf f W`. -/
theorem eval_split (Q : QuadForm R 4) (u : Fin 4 → R) (W : Matrix (Fin 4) (Fin 3) R)
    (horth : ∀ z, bl Q u (W *ᵥ z) = 0) (b : R) (z : Fin 3 → R) :
    Q.eval (b • u + W *ᵥ z) = b ^ 2 * Q.eval u + (gramOf Q W).eval z := by
  rw [eval_add, eval_smul, bl_smul_left, horth, mul_zero, add_zero, gramOf_eval]

end Split

/-! ### The determinant identity -/

/-- Helper: the $4 \times 4$ matrix $[\mathbf u \mid W]$. -/
def uW (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i k => Fin.cases (u i) (fun j => W i j) k

/-- **The determinant identity** $\det([\mathbf u \mid W])^2\det H_f = 2f(\mathbf u)\det H_h$, from
$[\mathbf u \mid W]^{\mathsf T}H_f[\mathbf u \mid W] = \operatorname{diag}(2f(\mathbf u), H_h)$. -/
theorem det_uW_sq_mul (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (horth : ∀ z, bl f u (W *ᵥ z) = 0) :
    (uW u W).det ^ 2 * f.hessian.det = 2 * f.eval u * (gramOf f W).hessian.det := by
  have hblk : (uW u W)ᵀ * f.hessian * uW u W =
      Matrix.of fun k l => Fin.cases (Fin.cases (2 * f.eval u) (fun _ => 0) l)
        (fun i => Fin.cases 0 (fun j => (gramOf f W).hessian i j) l) k := by
    rw [gramOf_hessian]
    ext k l
    have hcolk : ∀ k : Fin 4, (fun i => uW u W i k) = Fin.cases u (fun j => Ch11L92.col W j) k := by
      intro k; refine Fin.cases ?_ (fun j => ?_) k
      · funext i; simp [uW]
      · funext i; simp [uW, Ch11L92.col, mulVec_single_one]
    have e : ((uW u W)ᵀ * f.hessian * uW u W) k l =
        bl f (fun i => uW u W i k) (fun i => uW u W i l) := by
      simp only [bl, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    rw [e, hcolk k, hcolk l]
    have hW : ∀ j, Ch11L92.col W j = W *ᵥ Pi.single j 1 := fun j => rfl
    refine Fin.cases ?_ (fun i => ?_) k <;> refine Fin.cases ?_ (fun j => ?_) l
    · simp [bl_self]
    · simp only [Fin.cases_zero, Fin.cases_succ, Matrix.of_apply]; rw [hW]; exact horth _
    · simp only [Fin.cases_zero, Fin.cases_succ, Matrix.of_apply]; rw [hW, bl_comm]; exact horth _
    · simp only [Fin.cases_succ, Matrix.of_apply]; rw [bl_col_eq]
  have hD : (Matrix.of fun k l => Fin.cases (Fin.cases (2 * f.eval u) (fun _ => 0) l)
      (fun i => Fin.cases 0 (fun j => (gramOf f W).hessian i j) l) k : Matrix (Fin 4) (Fin 4) ℤ).det =
      2 * f.eval u * (gramOf f W).hessian.det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul, mul_zero, Finset.sum_const_zero,
      add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    congr 2
  have hdet := congrArg Matrix.det hblk
  rw [hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  rw [← hdet]; ring

/-! ### Consequences at the primes not dividing $2f(\mathbf u)\det H_f$ -/

/-- **$\det[\mathbf u \mid W]$ divides $2f(\mathbf u)$:** with $N_0$ the matrix of rows $H\mathbf u$, $\tilde W$,
$N_0[\mathbf u \mid W]$ is block triangular with diagonal $2f(\mathbf u), 1, 1, 1$. -/
theorem det_uW_dvd (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1) (horth : ∀ z, bl f u (W *ᵥ z) = 0) :
    (uW u W).det ∣ 2 * f.eval u := by
  set N0 : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of fun k i =>
    Fin.cases ((f.hessian *ᵥ u) i) (fun j => Wt j i) k with hN0
  have hsymm : f.hessianᵀ = f.hessian := by simp [QuadForm.hessian, add_comm]
  have hHs : ∀ a c, f.hessian a c = f.hessian c a := fun a c => by
    rw [← Matrix.transpose_apply f.hessian c a, hsymm]
  have hNM : (N0 * uW u W).det = 2 * f.eval u := by
    have hlow : N0 * uW u W = Matrix.of fun k l => Fin.cases (Fin.cases (2 * f.eval u) (fun _ => 0) l)
        (fun j => Fin.cases ((Wt *ᵥ u) j) (fun k' => (1 : Matrix (Fin 3) (Fin 3) ℤ) j k') l) k := by
      ext k l
      refine Fin.cases ?_ (fun j => ?_) k <;> refine Fin.cases ?_ (fun j' => ?_) l
      · have := bl_self f u
        simp only [bl] at this
        simp only [hN0, Matrix.mul_apply, uW, Matrix.of_apply, Fin.cases_zero]
        rw [← this, dotProduct, ← hsymm]
        simp only [mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by
          rw [hHs c a]; ring
      · have := horth (Pi.single j' 1)
        simp only [bl, mulVec_single_one] at this
        simp only [hN0, Matrix.mul_apply, uW, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ]
        rw [← this, ← hsymm]
        simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.col_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by
          rw [hHs c a]; ring
      · simp [hN0, Matrix.mul_apply, uW, mulVec, dotProduct]
      · have := congrFun (congrFun hWt j) j'
        simp only [Matrix.mul_apply] at this
        simp [hN0, Matrix.mul_apply, uW, this]
    rw [hlow, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, Fin.cases_zero, Fin.cases_succ, zero_mul, mul_zero, Finset.sum_const_zero,
      add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have : ((Matrix.of fun k l => Fin.cases (Fin.cases (2 * f.eval u) (fun _ => 0) l)
        (fun j => Fin.cases ((Wt *ᵥ u) j) (fun k' => (1 : Matrix (Fin 3) (Fin 3) ℤ) j k') l) k :
          Matrix (Fin 4) (Fin 4) ℤ).submatrix Fin.succ Fin.succ) = 1 := by
      ext i j; simp
    rw [this, Matrix.det_one, mul_one]
  exact ⟨N0.det, by rw [← hNM, Matrix.det_mul, mul_comm]⟩

/-- **$h$ is unimodular at $p \nmid 2f(\mathbf u)\det H_f$** (Cassels' case (d), (9.59): $\Gamma_p = \mathbb Z_p^4 \cap V^{(2)}$
is unimodular). -/
theorem not_dvd_hessian_det (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1) (horth : ∀ z, bl f u (W *ᵥ z) = 0) {p : ℕ} (hp : p.Prime)
    (hpd : ¬ (p : ℤ) ∣ 2 * f.eval u * f.hessian.det) : ¬ (p : ℤ) ∣ 2 * (gramOf f W).hessian.det := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd := det_uW_dvd f u W Wt hWt horth
  have hid := det_uW_sq_mul f u W horth
  intro h2
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h => hpd (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hph : (p : ℤ) ∣ (gramOf f W).hessian.det := (hpp.dvd_or_dvd h2).resolve_left hp2
  have : (p : ℤ) ∣ (uW u W).det ^ 2 * f.hessian.det := by
    rw [hid]; exact Dvd.dvd.mul_left hph _
  rcases hpp.dvd_or_dvd this with h | h
  · exact hpd (dvd_mul_of_dvd_left ((hpp.dvd_of_dvd_pow h).trans hdvd) _)
  · exact hpd (dvd_mul_of_dvd_right h _)

/-- **Primitivity of $b\mathbf u + Wz$ at $p \nmid 2f(\mathbf u)$** (Cassels (9.44) in case (d)): if $z$ is primitive at $p$
then so is $b\mathbf u + Wz$. -/
theorem primAt_add_of_not_dvd (f : QuadForm ℤ 4) (u : Fin 4 → ℤ) (W : Matrix (Fin 4) (Fin 3) ℤ)
    (Wt : Matrix (Fin 3) (Fin 4) ℤ) (hWt : Wt * W = 1) (horth : ∀ z, bl f u (W *ᵥ z) = 0) {p : ℕ} (hp : p.Prime)
    (hpg : ¬ (p : ℤ) ∣ 2 * f.eval u) (b : ℤ) {z : Fin 3 → ℤ} (hz : PrimAt p z) : PrimAt p (b • u + W *ᵥ z) := by
  intro hall
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd_dot : ∀ c : Fin 4 → ℤ, (p : ℤ) ∣ c ⬝ᵥ (b • u + W *ᵥ z) := fun c =>
    Finset.dvd_sum fun i _ => Dvd.dvd.mul_left (hall i) _
  -- pairing with `H u`
  have h1 : bl f u (b • u + W *ᵥ z) = b * (2 * f.eval u) := by
    rw [bl_add_right, horth, add_zero, bl_smul_right, bl_self]
  have hb : (p : ℤ) ∣ b := by
    have : (p : ℤ) ∣ bl f u (b • u + W *ᵥ z) := by
      rw [bl, dotProduct_mulVec]; exact hdvd_dot _
    rw [h1] at this
    exact (hpp.dvd_or_dvd this).resolve_right hpg
  apply hz
  intro j
  have e : z j = (Wt *ᵥ (b • u + W *ᵥ z)) j - b * (Wt *ᵥ u) j := by
    rw [mulVec_add, mulVec_mulVec, hWt, one_mulVec, mulVec_smul]; simp
  rw [e]
  exact dvd_sub (hdvd_dot (fun i => Wt j i)) (Dvd.dvd.mul_right hb _)

end QuadFormsKB.Cassels.Ch11L92
