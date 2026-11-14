/-
# Hecke's bound for $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ in every rank

For $Q$ positive definite in $n$ variables, $c(m) = r_Q(m) - a_E(m)$ (`genusCuspCoeff`) are the Fourier coefficients of
$f = \Theta_Q - \Theta_{\mathrm{Gen}(Q)}$. For $n = 2k$ even, $f$ is a cusp form of weight $k$ and
`Siegel.exists_abs_genusCuspCoeff_le` gives $c(m) = O(m^{k/2})$ (Hecke's bound, Mathlib's
`CuspFormClass.qExpansion_isBigO`). For $n$ odd, $f$ has half-integral weight and Mathlib has no modular form to apply this to.
This file proves
$$|c(m)| \le C\,m^{n/4}\qquad(m \ge 1)$$
for **every** $n$ (`exists_abs_genusCuspCoeff_le_rpow`), unconditionally, by **squaring**:

1. `theta_orthSum`: $\Theta_{A \perp B} = \Theta_A \Theta_B$ for positive definite $A$, $B$ (product of absolutely convergent
   series over $\mathbb Z^{a} \times \mathbb Z^{b}$, `Fin.appendEquiv`); `posDef_orthSum`.
2. `sameGenus_orthSum`: $A \sim A'$, $B \sim B'$ in genus implies $A \perp B \sim A' \perp B'$ (block diagonal isometries over
   every $\mathbb Z_p$ and $\mathbb R$, `isometricGL_orthSum`; base change `map_orthSum`).
3. With $w_c = |\mathrm{Aut}(Q_c)|^{-1}/\mathrm{Mass}(Q)$ and `theta_sub_thetaGen`, $f = \sum_c w_c(\Theta_Q - \Theta_{Q_c})$, so
   $$f^2 = \sum_{c,d} w_c w_d\big[(\Theta_{Q\perp Q} - \Theta_{Q\perp Q_d}) + (\Theta_{Q\perp Q} - \Theta_{Q_c\perp Q})
   - (\Theta_{Q\perp Q} - \Theta_{Q_c\perp Q_d})\big],$$
   and every difference is $\Theta_A - \Theta_B$ for forms of even rank $2n$ in one genus: the cusp form `thetaCuspDiff` of weight
   $n$ for $\Gamma_1(N)$ (common level from `exists_isThetaLevel_genus`). Mathlib's `CuspFormClass.exists_bound` gives
   $\|F(\tau)\| \le C(\operatorname{Im}\tau)^{-n/2}$ for each, hence $\|f(\tau)\|^2 \le K(\operatorname{Im}\tau)^{-n/2}$ and
   $\|f(\tau)\| \le M(\operatorname{Im}\tau)^{-n/4}$ (`exists_norm_theta_sub_le`).
4. The $q$-expansion coefficients of $f$ are $c(m)$ (`hasSum_theta`, `hasSum_thetaGen`, Mathlib's
   `UpperHalfPlane.qExpansion_coeff_unique`), and Mathlib's `qExpansion_coeff_eq_intervalIntegral` on the horizontal line
   $\operatorname{Im}\tau = 1/m$ gives $|c(m)| \le e^{2\pi}M\,m^{n/4}$.

*Reused library results:* `exists_abs_genusCuspCoeff_le` (even case, same method), `thetaCuspDiff`, `exists_isThetaLevel_genus`,
`theta_sub_thetaGen`, `hasSum_theta`, `hasSum_thetaGen`, `genusFinite`, `QuadForm.evalIn_orthSum`; $E_8$-file helper
`posDef_orthSum` (Cassels Ch. 9, Ex. 11) and `blockLinR` (copied, generalized to $\mathrm{diag}(P, P')$).

Source: Iwaniec, *Topics in Classical Automorphic Forms*, Thm 5.1 (Hecke's bound) [unverified]; the squaring trick is the standard
way to treat half-integral weight (Moreno–Wagstaff, *Sums of Squares of Integers*).
-/
import QuadFormsKB.Siegel.HeckeBound
import QuadFormsKB.Witt.Bridge

open Complex Filter Asymptotics UpperHalfPlane Matrix
open scoped MatrixGroups Manifold

namespace QuadFormsKB.MorenoWagstaff

open QuadFormsKB.Siegel

noncomputable section

/-! ### Step 1: theta series of an orthogonal sum -/

/-- **Positive definiteness of $A \perp B$**: the orthogonal sum of two positive definite integral forms is positive definite. -/
theorem posDef_orthSum {a m : ℕ} {P : QuadForm ℤ a} {g : QuadForm ℤ m} (hP : IntQF.PosDef P)
    (hg : IntQF.PosDef g) : IntQF.PosDef (QuadForm.orthSum P g) := by
  intro x hx
  show 0 < (QuadForm.orthSum P g).evalIn ℤ x
  rw [QuadForm.evalIn_orthSum]
  by_cases h1 : (fun i => x (Fin.castAdd m i)) = 0
  · have h2 : (fun j => x (Fin.natAdd a j)) ≠ 0 := by
      intro h2
      apply hx
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · exact congrFun h1 i
      · exact congrFun h2 j
    have h3 := hP.eval_nonneg (fun i => x (Fin.castAdd m i))
    have h4 := hg _ h2
    show 0 < P.eval _ + g.eval _
    omega
  · have h3 := hP _ h1
    have h4 := hg.eval_nonneg (fun j => x (Fin.natAdd a j))
    show 0 < P.eval _ + g.eval _
    omega

/-- **Theta of an orthogonal sum**: for positive definite $A$, $B$ and $\operatorname{Im} z > 0$,
$$\Theta_{A \perp B}(z) = \Theta_A(z)\,\Theta_B(z).$$
The series over $\mathbb Z^{a+b} \simeq \mathbb Z^a \times \mathbb Z^b$ (`Fin.appendEquiv`) is the product of two absolutely
convergent series. -/
theorem theta_orthSum {a b : ℕ} {A : IntQF a} {B : IntQF b} (hA : A.PosDef) (hB : B.PosDef) {z : ℂ}
    (hz : 0 < z.im) : theta (QuadForm.orthSum A B) z = theta A z * theta B z := by
  unfold theta
  rw [tsum_mul_tsum_of_summable_norm (summable_theta_term hA hz).norm (summable_theta_term hB hz).norm,
    ← (Fin.appendEquiv a b).tsum_eq]
  refine tsum_congr fun p => ?_
  show cexp (2 * Real.pi * Complex.I * z * (((QuadForm.orthSum A B).evalIn ℤ (Fin.append p.1 p.2) : ℤ) : ℂ)) = _
  rw [QuadForm.evalIn_orthSum]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### Step 2: the genus of an orthogonal sum -/

section BlockDiag

variable {K : Type*} [CommRing K] {a b : ℕ}

/-- The block diagonal matrix $\mathrm{diag}(P, P')$ on `Fin (a + b)`. -/
def blockDiag (P : Matrix (Fin a) (Fin a) K) (P' : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin (a + b)) (Fin (a + b)) K :=
  (Matrix.fromBlocks P 0 0 P').submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- $\mathrm{diag}(P, P')$ acts by $P$ on the first $a$ coordinates. -/
theorem blockDiag_mulVec_castAdd (P : Matrix (Fin a) (Fin a) K) (P' : Matrix (Fin b) (Fin b) K)
    (x : Fin (a + b) → K) :
    (fun i => (blockDiag P P' *ᵥ x) (Fin.castAdd b i)) = P *ᵥ (fun i => x (Fin.castAdd b i)) := by
  ext i
  simp [blockDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]

/-- $\mathrm{diag}(P, P')$ acts by $P'$ on the last $b$ coordinates. -/
theorem blockDiag_mulVec_natAdd (P : Matrix (Fin a) (Fin a) K) (P' : Matrix (Fin b) (Fin b) K)
    (x : Fin (a + b) → K) :
    (fun j => (blockDiag P P' *ᵥ x) (Fin.natAdd a j)) = P' *ᵥ (fun j => x (Fin.natAdd a j)) := by
  ext j
  simp [blockDiag, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.fromBlocks]

/-- $\det \mathrm{diag}(P, P') = \det P \cdot \det P'$. -/
theorem det_blockDiag (P : Matrix (Fin a) (Fin a) K) (P' : Matrix (Fin b) (Fin b) K) :
    (blockDiag P P').det = P.det * P'.det := by
  rw [blockDiag, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]

/-- **Block diagonal isometries**: $Q \sim Q'$ and $P \sim P'$ over a commutative ring $K$ imply
$Q \perp P \sim Q' \perp P'$ (`IsometricGL`). -/
theorem isometricGL_orthSum {Q Q' : QuadForm K a} {P P' : QuadForm K b} (h : IsometricGL Q Q')
    (h' : IsometricGL P P') : IsometricGL (QuadForm.orthSum Q P) (QuadForm.orthSum Q' P') := by
  rw [isometricGL_iff_isometricIn] at h h' ⊢
  obtain ⟨g, hg, e⟩ := h
  obtain ⟨g', hg', e'⟩ := h'
  refine ⟨blockDiag g g', ?_, fun x => ?_⟩
  · rw [det_blockDiag]; exact hg.mul hg'
  · rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum, blockDiag_mulVec_castAdd,
      blockDiag_mulVec_natAdd, e, e']

end BlockDiag

section OrthSumCoeff

variable {R : Type*} [CommRing R] {m n : ℕ}

theorem orthSum_coeff_cc (S : QuadForm R m) (T : QuadForm R n) (a b : Fin m) :
    (QuadForm.orthSum S T).coeff (Fin.castAdd n a) (Fin.castAdd n b) = S.coeff a b := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left]
  have h3 : Fin.castAdd n a ≤ Fin.castAdd n b ↔ a ≤ b :=
    Fin.le_iff_val_le_val.trans (Fin.le_iff_val_le_val (a := a) (b := b)).symm
  by_cases h : a ≤ b
  · rw [if_pos (h3.mpr h)]
  · rw [if_neg (fun h' => h (h3.mp h')), S.upper (show id b < id a from not_le.mp h)]

theorem orthSum_coeff_nn (S : QuadForm R m) (T : QuadForm R n) (a b : Fin n) :
    (QuadForm.orthSum S T).coeff (Fin.natAdd m a) (Fin.natAdd m b) = T.coeff a b := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_right]
  have h4 : Fin.natAdd m a ≤ Fin.natAdd m b ↔ a ≤ b := by
    rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val (a := a)]
    change m + a.val ≤ m + b.val ↔ _
    omega
  by_cases h : a ≤ b
  · rw [if_pos (h4.mpr h)]
  · rw [if_neg (fun h' => h (h4.mp h')), T.upper (show id b < id a from not_le.mp h)]

theorem orthSum_coeff_cn (S : QuadForm R m) (T : QuadForm R n) (a : Fin m) (b : Fin n) :
    (QuadForm.orthSum S T).coeff (Fin.castAdd n a) (Fin.natAdd m b) = 0 := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

theorem orthSum_coeff_nc (S : QuadForm R m) (T : QuadForm R n) (a : Fin n) (b : Fin m) :
    (QuadForm.orthSum S T).coeff (Fin.natAdd m a) (Fin.castAdd n b) = 0 := by
  simp only [QuadForm.orthSum, QuadForm.ofUpper, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

/-- **Base change commutes with the orthogonal sum**: $(S \perp T)\otimes_f = S_f \perp T_f$. -/
theorem map_orthSum {B : Type*} [CommRing B] (f : R →+* B) (S : QuadForm R m) (T : QuadForm R n) :
    (QuadForm.orthSum S T).map f = QuadForm.orthSum (S.map f) (T.map f) := by
  ext i j
  simp only [QuadForm.map, Matrix.map_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j
  · rw [orthSum_coeff_cc, orthSum_coeff_cc]; simp
  · rw [orthSum_coeff_cn, orthSum_coeff_cn]; simp
  · rw [orthSum_coeff_nc, orthSum_coeff_nc]; simp
  · rw [orthSum_coeff_nn, orthSum_coeff_nn]; simp

end OrthSumCoeff

/-- **The genus of an orthogonal sum**: if $A, A'$ are in one genus and $B, B'$ are in one genus, then
$A \perp B$ and $A' \perp B'$ are in one genus (`SameGenus`: block diagonal local isometries at every $p$ and at $\infty$). -/
theorem sameGenus_orthSum {a b : ℕ} {A A' : IntQF a} {B B' : IntQF b} (hA : SameGenus A A')
    (hB : SameGenus B B') : SameGenus (QuadForm.orthSum A B) (QuadForm.orthSum A' B') := by
  refine ⟨fun p _ => ?_, ?_⟩
  · rw [map_orthSum, map_orthSum]
    exact isometricGL_orthSum (hA.1 p) (hB.1 p)
  · rw [map_orthSum, map_orthSum]
    exact isometricGL_orthSum hA.2 hB.2

/-! ### Step 3: the square of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ -/

/-- **A uniform bound for theta differences in one genus** ($G$ positive definite in $m = 2k$ variables): there is a function
$B$ on forms with $\|\Theta_G(\tau) - \Theta_A(\tau)\| \le B(A)\,(\operatorname{Im}\tau)^{-k/2}$ for every $\tau \in \mathbb H$ and
every $A$ in the genus of $G$. Each $\Theta_G - \Theta_A$ is a cusp form of weight $k$ for $\Gamma_1(N)$, $N$ a common level
(`thetaCuspDiff`), and Mathlib's `CuspFormClass.exists_bound` applies. -/
theorem exists_theta_sub_bound {m k : ℕ} {G : IntQF m} (hG : G.PosDef) (hm : m = 2 * k) :
    ∃ B : IntQF m → ℝ, ∀ A, SameGenus G A → ∀ τ : ℍ,
      ‖theta G τ - theta A τ‖ ≤ B A / τ.im ^ ((k : ℝ) / 2) := by
  obtain ⟨N, hN0, hN⟩ := exists_isThetaLevel_genus hG (genusFinite hG)
  haveI : NeZero N := ⟨hN0.ne'⟩
  have key : ∀ A : IntQF m, ∃ C : ℝ, SameGenus G A → ∀ τ : ℍ,
      ‖theta G τ - theta A τ‖ ≤ C / τ.im ^ ((k : ℝ) / 2) := by
    intro A
    by_cases h : SameGenus G A
    · obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (k := (k : ℤ))
        (thetaCuspDiff hG h hm hN0 (hN G (SameGenus.refl G)) (hN A h))
      refine ⟨C, fun _ τ => ?_⟩
      simpa using hC τ
    · exact ⟨0, fun h' => absurd h' h⟩
  choose B hB using key
  exact ⟨B, fun A h => hB A h⟩

/-- **The square of the cuspidal part is $O((\operatorname{Im}\tau)^{-n/2})$**: for $Q$ positive definite in $n$ variables there
is $K \ge 0$ with $\|\Theta_Q(\tau) - \Theta_{\mathrm{Gen}(Q)}(\tau)\|^2 \le K(\operatorname{Im}\tau)^{-n/2}$ on $\mathbb H$.
(Via $f^2 = \sum_{c,d} w_c w_d(\cdots)$, a combination of cusp forms of weight $n$ on the rank-$2n$ genus of $Q \perp Q$.) -/
theorem exists_sq_norm_theta_sub_le {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ : ℍ,
      ‖theta Q τ - thetaGen Q τ‖ ^ 2 ≤ K / τ.im ^ ((n : ℝ) / 2) := by
  classical
  have hG : IntQF.PosDef (QuadForm.orthSum Q Q) := posDef_orthSum hQ hQ
  obtain ⟨B, hB⟩ := exists_theta_sub_bound hG (show n + n = 2 * n by omega)
  have hF := genusFinite hQ
  set s := hF.finite_classes.toFinset with hs
  have hmem : ∀ c ∈ s, SameGenus Q c.out := fun c hc =>
    sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)
  have hpos : ∀ c ∈ s, IntQF.PosDef c.out := fun c hc => (hmem c hc).posDef hQ
  set T : QClass n → QClass n → ℝ := fun c d =>
    |B (QuadForm.orthSum Q d.out)| + |B (QuadForm.orthSum c.out Q)| + |B (QuadForm.orthSum c.out d.out)|
    with hT
  set a : QClass n → ℂ := fun c => ((c.autCard : ℂ))⁻¹ with ha
  refine ⟨‖((mass Q : ℝ) : ℂ)⁻¹‖ ^ 2 * ∑ c ∈ s, ∑ d ∈ s, ‖a c‖ * ‖a d‖ * T c d,
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ => by
      simp only [hT]; positivity), fun τ => ?_⟩
  have hy0 : 0 < τ.im ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  -- pairwise bound
  have hpair : ∀ c ∈ s, ∀ d ∈ s,
      ‖(theta Q τ - theta c.out τ) * (theta Q τ - theta d.out τ)‖ ≤ T c d / τ.im ^ ((n : ℝ) / 2) := by
    intro c hc d hd
    have hQQ : theta (QuadForm.orthSum Q Q) τ = theta Q τ * theta Q τ := theta_orthSum hQ hQ τ.im_pos
    have h1 : theta (QuadForm.orthSum Q d.out) τ = theta Q τ * theta d.out τ :=
      theta_orthSum hQ (hpos d hd) τ.im_pos
    have h2 : theta (QuadForm.orthSum c.out Q) τ = theta c.out τ * theta Q τ :=
      theta_orthSum (hpos c hc) hQ τ.im_pos
    have h3 : theta (QuadForm.orthSum c.out d.out) τ = theta c.out τ * theta d.out τ :=
      theta_orthSum (hpos c hc) (hpos d hd) τ.im_pos
    have e1 := (hB _ (sameGenus_orthSum (SameGenus.refl Q) (hmem d hd)) τ).trans
      (div_le_div_of_nonneg_right (le_abs_self _) hy0.le)
    have e2 := (hB _ (sameGenus_orthSum (hmem c hc) (SameGenus.refl Q)) τ).trans
      (div_le_div_of_nonneg_right (le_abs_self _) hy0.le)
    have e3 := (hB _ (sameGenus_orthSum (hmem c hc) (hmem d hd)) τ).trans
      (div_le_div_of_nonneg_right (le_abs_self _) hy0.le)
    have hid : (theta Q τ - theta c.out τ) * (theta Q τ - theta d.out τ) =
        (theta (QuadForm.orthSum Q Q) τ - theta (QuadForm.orthSum Q d.out) τ) +
        (theta (QuadForm.orthSum Q Q) τ - theta (QuadForm.orthSum c.out Q) τ) -
        (theta (QuadForm.orthSum Q Q) τ - theta (QuadForm.orthSum c.out d.out) τ) := by
      rw [hQQ, h1, h2, h3]; ring
    rw [hid]
    refine (norm_sub_le _ _).trans ?_
    refine le_trans (add_le_add_left (norm_add_le _ _) _) ?_
    simp only [hT, add_div]
    linarith
  have hf : theta Q τ - thetaGen Q τ = ((mass Q : ℝ) : ℂ)⁻¹ *
      ∑ c ∈ s, a c * (theta Q τ - theta c.out τ) := theta_sub_thetaGen hQ hF τ
  have hS : (∑ c ∈ s, a c * (theta Q τ - theta c.out τ)) ^ 2 =
      ∑ c ∈ s, ∑ d ∈ s, (a c * a d) *
        ((theta Q τ - theta c.out τ) * (theta Q τ - theta d.out τ)) := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have hbound : ‖∑ c ∈ s, a c * (theta Q τ - theta c.out τ)‖ ^ 2 ≤
      (∑ c ∈ s, ∑ d ∈ s, ‖a c‖ * ‖a d‖ * T c d) / τ.im ^ ((n : ℝ) / 2) := by
    rw [← norm_pow, hS]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ c ∈ s, ‖∑ d ∈ s, (a c * a d) *
          ((theta Q τ - theta c.out τ) * (theta Q τ - theta d.out τ))‖
        ≤ ∑ c ∈ s, ∑ d ∈ s, ‖a c‖ * ‖a d‖ * (T c d / τ.im ^ ((n : ℝ) / 2)) :=
          Finset.sum_le_sum fun c hc => (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => by
            rw [norm_mul, norm_mul]
            exact mul_le_mul_of_nonneg_left (hpair c hc d hd) (by positivity))
      _ = _ := by
          simp only [Finset.sum_div]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [hf, norm_mul, mul_pow, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- **Growth of the cuspidal part**: for $Q$ positive definite in $n$ variables there is $M \ge 0$ with
$\|\Theta_Q(\tau) - \Theta_{\mathrm{Gen}(Q)}(\tau)\| \le M(\operatorname{Im}\tau)^{-n/4}$ on $\mathbb H$ (square root of
`exists_sq_norm_theta_sub_le`). -/
theorem exists_norm_theta_sub_le {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℍ, ‖theta Q τ - thetaGen Q τ‖ ≤ M * τ.im ^ (-((n : ℝ) / 4)) := by
  obtain ⟨K, hK, h⟩ := exists_sq_norm_theta_sub_le hQ
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun τ => ?_⟩
  have hy : 0 < τ.im := τ.im_pos
  have e : (-((n : ℝ) / 4)) * ((2 : ℕ) : ℝ) = -((n : ℝ) / 2) := by push_cast; ring
  have hsq : (Real.sqrt K * τ.im ^ (-((n : ℝ) / 4))) ^ 2 = K / τ.im ^ ((n : ℝ) / 2) := by
    rw [mul_pow, Real.sq_sqrt hK, ← Real.rpow_natCast, ← Real.rpow_mul hy.le, e, Real.rpow_neg hy.le,
      div_eq_mul_inv K]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hy.le _)) two_ne_zero).1 (by rw [hsq]; exact h τ)

/-! ### Step 4: coefficient extraction -/

/-- Mathlib's `UpperHalfPlane.qExpansion_coeff_unique` for a plain function `f : ℍ → ℂ` (Mathlib states it for
`FunLike` types; same proof). -/
theorem qExpansion_coeff_unique_fun {f : ℍ → ℂ} {c : ℕ → ℂ} {h : ℝ} (hh : 0 < h)
    (hfanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam h τ ^ m) (f τ)) (m : ℕ) :
    c m = (UpperHalfPlane.qExpansion h f).coeff m := by
  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (UpperHalfPlane.cuspFunction h f)
      (FormalMultilinearSeries.ofScalars ℂ fun m => (UpperHalfPlane.qExpansion h f).coeff m) 0 := by
    simpa [UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm] using hfanalytic.hasFPowerSeriesAt
  simpa using congr(FormalMultilinearSeries.coeff $(h1.eq_formalMultilinearSeries h2) m)

/-- **Coefficients from a growth bound** (abstract form of Hecke's argument): if $F$ is holomorphic on $\mathbb H$ with
$F(\tau) = \sum_m a_m q^m$ ($q = e^{2\pi i\tau}$) and $\|F(\tau)\| \le M(\operatorname{Im}\tau)^{-e}$, then
$\|a_m\| \le e^{2\pi}M\,m^{e}$ for $m \ge 1$ (Mathlib's `qExpansion_coeff_eq_intervalIntegral` on $\operatorname{Im}\tau = 1/m$). -/
theorem norm_coeff_le_of_norm_le {F : ℍ → ℂ} {a : ℕ → ℂ} {M e : ℝ}
    (hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => a m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hM : ∀ τ : ℍ, ‖F τ‖ ≤ M * τ.im ^ (-e))
    {m : ℕ} (hm : 1 ≤ m) : ‖a m‖ ≤ Real.exp (2 * Real.pi) * (M * (m : ℝ) ^ e) := by
  have hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1 := by
    refine UpperHalfPlane.periodic_comp_ofComplex fun τ => ?_
    have hq : Function.Periodic.qParam 1 (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) := by
      simp [Function.Periodic.qParam, UpperHalfPlane.coe_vadd, mul_add, Complex.exp_add]
    exact (hsum ((1 : ℝ) +ᵥ τ)).unique (by rw [hq]; exact hsum τ)
  have hbdd := UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos hsum
  have hana := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hper hhol hbdd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set t : ℝ := 1 / m with ht
  have ht0 : 0 < t := by positivity
  have hco := qExpansion_coeff_unique_fun one_pos hana hsum m
  rw [UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral one_pos hper hhol hbdd m ht0] at hco
  have e1 : 1 / Real.exp (-2 * Real.pi * t / 1) ^ m = Real.exp (2 * Real.pi) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    rw [ht]
    field_simp
  have e2 : t ^ (-e) = (m : ℝ) ^ e := by
    rw [ht, one_div, Real.inv_rpow hm0.le, Real.rpow_neg hm0.le, inv_inv]
  have hpt : ∀ u : ℝ, ‖1 / Function.Periodic.qParam 1 ((u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ)) ^ m *
      F ⟨(u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ), by simpa using ht0⟩‖ ≤
      Real.exp (2 * Real.pi) * (M * (m : ℝ) ^ e) := by
    intro u
    rw [norm_mul, norm_div, norm_one, norm_pow, Function.Periodic.norm_qParam]
    have him : ((u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ)).im = t := by simp
    have e1' : 1 / Real.exp (-2 * Real.pi * ((u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ)).im / 1) ^ m =
        Real.exp (2 * Real.pi) := by rw [him]; exact e1
    rw [e1']
    have hFb := hM ⟨(u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ), by simpa using ht0⟩
    have him' : (⟨(u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : ℍ) : ℂ), by simpa using ht0⟩ : ℍ).im = t := him
    rw [him', e2] at hFb
    exact mul_le_mul_of_nonneg_left hFb (Real.exp_pos _).le
  rw [hco, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => hpt u)) (norm_nonneg _)).trans ?_
  simp

/-- The $q$-expansion of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ has coefficients `genusCuspCoeff Q m`. -/
theorem hasSum_theta_sub_thetaGen {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (τ : ℍ) :
    HasSum (fun m : ℕ => (genusCuspCoeff Q m : ℂ) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (theta Q τ - thetaGen Q τ) := by
  have h := (hasSum_theta hQ τ.im_pos).sub (hasSum_thetaGen hQ (genusFinite hQ) τ.im_pos)
  convert h using 2 with m
  simp only [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul, div_one, genusCuspCoeff]
  push_cast
  rw [mul_comm (m : ℂ)]
  ring

/-- $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ is holomorphic on $\mathbb H$. -/
theorem mdifferentiable_theta_sub_thetaGen {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => theta Q τ - thetaGen Q τ) := by
  have hF := genusFinite hQ
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 := differentiableOn_theta hQ
  have h2 : DifferentiableOn ℂ (thetaGen Q) {z : ℂ | 0 < z.im} := by
    have : thetaGen Q = fun z => (((mass Q)⁻¹ : ℝ) : ℂ) *
        ∑ c ∈ hF.finite_classes.toFinset, (((c.autCard : ℝ))⁻¹ : ℂ) * theta c.out z :=
      funext (thetaGen_eq_sum hF)
    rw [this]
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun c hc => ?_) _
    exact (differentiableOn_theta ((sameGenus_out_of_mem
      ((Set.Finite.mem_toFinset _).mp hc)).posDef hQ)).const_mul _
  refine (h1.sub h2).congr fun x hx => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < x.im from hx)]

/-- **Hecke's bound for $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ in every rank** (unconditional): for $Q$ positive definite in $n \ge 1$
variables there is $C \ge 0$ with
$$|r_Q(m) - a_E(m)| \le C\,m^{n/4}\qquad\text{for all } m \ge 1.$$
For $n = 2k$ this is `exists_abs_genusCuspCoeff_le` ($m^{k/2} = m^{n/4}$); for odd $n$ the form has half-integral weight and the
proof goes through the square $f^2$, a combination of weight-$n$ cusp forms of rank $2n$ (`exists_norm_theta_sub_le`), and the
coefficient formula on the line $\operatorname{Im}\tau = 1/m$ (`norm_coeff_le_of_norm_le`). $C$ is not explicit. -/
theorem exists_abs_genusCuspCoeff_le_rpow {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) (_hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → |genusCuspCoeff Q m| ≤ C * (m : ℝ) ^ ((n : ℝ) / 4) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_theta_sub_le hQ
  refine ⟨Real.exp (2 * Real.pi) * M, by positivity, fun m hm => ?_⟩
  have key := norm_coeff_le_of_norm_le (hasSum_theta_sub_thetaGen hQ)
    (mdifferentiable_theta_sub_thetaGen hQ) hM hm
  rw [Complex.norm_real, Real.norm_eq_abs] at key
  calc |genusCuspCoeff Q m| ≤ _ := key
    _ = _ := by ring

end

end QuadFormsKB.MorenoWagstaff
