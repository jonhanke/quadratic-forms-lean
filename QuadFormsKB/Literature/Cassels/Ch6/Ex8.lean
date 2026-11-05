/-
# Cassels, Chapter 6, Example 8: representations of forms over ℝ and over ℚ

**Setting.** Rational forms `f : RatQF n`, `g : RatQF m`; "$f$ represents $g$ over $K$" is
`Tamagawa.Frames.Rep K f g`: there is a matrix $X \in K^{n \times m}$ with $f(X\vec y) = g(\vec y)$ for all
$\vec y \in K^m$ (Cassels' representation of a form by a form, by a linear substitution).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6, Example 8, p. 101): if $f$ is regular, $n \ge m + 3$ and
$f$ represents $g$ over $\mathbb R$, then $f$ represents $g$ over $\mathbb Q$ (`ex8`).

**Proof notes.** Cassels' hint: without loss of generality $g$ is diagonal, $\langle b_0, \dots, b_{m-1}\rangle$
(diagonal entries $0$ are dropped: they are represented by the zero column), and induction on $m$. Since $n \ge 4$, $f$
represents $b_0 \ne 0$ over every $\mathbb Q_p$ (a regular form in at least four variables over $\mathbb Q_p$ is
universal) and over $\mathbb R$ by hypothesis, so over $\mathbb Q$ (Corollary 2 to Theorem 1.1,
`represents_iff_everywhere`); then $f \cong \langle b_0\rangle \perp f_1$ over $\mathbb Q$, and over $\mathbb R$ the form
$f_1$ represents $\langle b_1, \dots\rangle$ by Witt's theorem (`Tamagawa.Frames.rep_step`); $f_1$ has $n - 1 \ge
(m - 1) + 3$ variables. The second part of the example (no $m$ for which $n \ge m + 2$ suffices) is not formalized.
-/
import QuadFormsKB.Tamagawa.FrameHM
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.Classical.DavenportCassels
import QuadFormsKB.Literature.Classical.SumsOfSquares

namespace QuadFormsKB.Cassels.Ch6

open Tamagawa.Frames

/-- Diagonalization over `ℚ` of an arbitrary (possibly degenerate) rational form. -/
theorem exists_isometric_diag_any {n : ℕ} (Q : RatQF n) :
    ∃ a : Fin n → ℚ, Q.IsometricIn ℚ (QuadForm.diag a) := by
  set Q' : QuadraticForm ℚ (Fin n → ℚ) :=
    LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' ℚ Q.coeff) with hQ'
  have hev : ∀ x, QuadForm.evalIn ℚ Q x = Q' x := fun x => by
    rw [hQ', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']
    simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · ring
    · rw [Q.upper (not_le.mp h)]; ring
  clear_value Q'
  obtain ⟨v0, hv0⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm ℚ Q')
  let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr (Module.finrank_fin_fun ℚ)
  let v := v0.reindex e
  have hv : LinearMap.IsOrthoᵢ (QuadraticMap.associated Q') v := by
    intro i j hij
    show QuadraticMap.associated Q' (v i) (v j) = 0
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact hv0 (fun h => hij (e.symm.injective h))
  clear_value v
  refine ⟨fun i => Q' (v i), (Pi.basisFun ℚ (Fin n)).toMatrix v, ?_, ?_⟩
  · have := Module.Basis.invertibleToMatrix (Pi.basisFun ℚ (Fin n)) v
    exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)
  · intro y
    have hmul : ((Pi.basisFun ℚ (Fin n)).toMatrix v).mulVec y = ∑ i, y i • v i := by
      ext k
      simp [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_apply, mul_comm]
    rw [hmul, hev, ← QuadraticMap.basisRepr_apply, QuadraticMap.basisRepr_eq_of_iIsOrtho Q' v hv,
      QuadraticMap.weightedSumSquares_apply]
    simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply, Algebra.algebraMap_self,
      RingHom.id_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [mul_assoc]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

open Matrix in
/-- A zero first diagonal entry of the represented form costs nothing (forward direction). -/
theorem rep_zero_cons_of {K : Type} [Field K] [CharZero K] [Algebra ℚ K] {N r : ℕ} (Q : QuadForm ℚ N)
    (dt : Fin r → ℚ) (h : Rep K Q (QuadForm.diag (Fin.cons 0 dt : Fin (r + 1) → ℚ))) :
    Rep K Q (QuadForm.diag dt) := by
  obtain ⟨X, hX⟩ := h
  refine ⟨Matrix.of fun i j => X i j.succ, fun y => ?_⟩
  have hmv : (Matrix.of fun i j => X i j.succ) *ᵥ y = X *ᵥ (Fin.cons 0 y : Fin (r + 1) → K) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hmv, hX]
  have := evalIn_diag_cons (K := K) (algebraMap ℚ K 0) (fun i => algebraMap ℚ K (dt i))
    (Fin.cons 0 y : Fin (r + 1) → K)
  rw [evalIn_diag_base K dt y, evalIn_diag_base K (Fin.cons 0 dt : Fin (r + 1) → ℚ), alg_cons, this]
  simp

open Matrix in
/-- A zero first diagonal entry of the represented form costs nothing (backward direction). -/
theorem rep_zero_cons_to {K : Type} [Field K] [CharZero K] [Algebra ℚ K] {N r : ℕ} (Q : QuadForm ℚ N)
    (dt : Fin r → ℚ) (h : Rep K Q (QuadForm.diag dt)) :
    Rep K Q (QuadForm.diag (Fin.cons 0 dt : Fin (r + 1) → ℚ)) := by
  obtain ⟨Y, hY⟩ := h
  refine ⟨Matrix.of fun i j => Fin.cases 0 (fun j' => Y i j') j, fun y => ?_⟩
  have hmv : (Matrix.of fun i j => Fin.cases 0 (fun j' => Y i j') j) *ᵥ y = Y *ᵥ Fin.tail y := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]
  rw [hmv, hY]
  have := evalIn_diag_cons (K := K) (algebraMap ℚ K 0) (fun i => algebraMap ℚ K (dt i)) y
  rw [evalIn_diag_base K (Fin.cons 0 dt : Fin (r + 1) → ℚ), alg_cons, this, evalIn_diag_base K dt]
  simp

/-- The diagonal case of Example 8, by induction on `m` (entries of `d` may vanish). -/
theorem ex8_diag (m : ℕ) : ∀ (n : ℕ) (a : Fin n → ℚ), (∀ i, a i ≠ 0) → ∀ d : Fin m → ℚ, m + 3 ≤ n →
    Rep ℝ (QuadForm.diag a) (QuadForm.diag d) → Rep ℚ (QuadForm.diag a) (QuadForm.diag d) := by
  induction m with
  | zero =>
    intro n a _ d _ _
    exact ⟨0, fun y => by simp [QuadForm.evalIn_diag]⟩
  | succ m ih =>
    intro n a ha d hn hR
    obtain ⟨d0, dt, rfl⟩ : ∃ d0 dt, d = (Fin.cons d0 dt : Fin (m + 1) → ℚ) :=
      ⟨d 0, Fin.tail d, (Fin.cons_self_tail d).symm⟩
    by_cases h0 : d0 = 0
    · subst h0
      exact rep_zero_cons_to _ dt (ih n a ha dt (by omega) (rep_zero_cons_of _ dt hR))
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hnd := QuadForm.nondegenerate_diag ha
      have hRb : (QuadForm.diag a).RepresentsIn ℝ d0 := rep_represents a _ hR
      have hQ : (QuadForm.diag a).RepresentsIn ℚ d0 := by
        rw [represents_iff_everywhere _ hnd d0 h0]
        intro v
        rcases v with _ | p
        · exact hRb
        · have : Fact p.1.Prime := ⟨p.2⟩
          show (QuadForm.diag a).RepresentsIn ℚ_[p.1] d0
          exact represents_padic_of_four_le p.1 a ha (by omega) d0
      obtain ⟨α, hα, hiso⟩ := QuadForm.exists_isometric_diag_cons hnd h0 hQ
      have hloc : Rep ℝ (QuadForm.diag α) (QuadForm.diag dt) :=
        rep_local_step d0 h0 α hα dt a hiso hR
      exact rep_of_iso_left hiso (rep_cons d0 α dt (ih n' α hα dt (by omega) hloc))

/-- **Cassels, Ch. 6, Example 8**: *let $f(\vec x)$, $g(\vec y)$ be forms with rational coefficients in $n$, $m$
variables such that (i) $f$ is regular, (ii) $n \ge m + 3$, (iii) $f$ represents $g$ over $\mathbb R$. Then $f$
represents $g$ over $\mathbb Q$.* -/
@[kb "cassels1978" "Ch. 6, Ex. 8, p. 101 (first part)"]
theorem ex8 {n m : ℕ} (f : RatQF n) (g : RatQF m) (hf : f.Nondegenerate) (hnm : m + 3 ≤ n) (hR : Rep ℝ f g) :
    Rep ℚ f g := by
  obtain ⟨a, ha, hiso⟩ := HM3.exists_isometric_diag f hf
  obtain ⟨t, hit⟩ := exists_isometric_diag_any g
  rw [rep_iff_diag hiso hit] at hR ⊢
  exact ex8_diag m n a ha t hnm hR

/-- The diagonal `(1, …, 1, 7)` on `k + 1` entries. -/
def ex8T (k : ℕ) : Fin (k + 1) → ℚ := fun i => if (i : ℕ) = k then 7 else 1

/-- `ex8T (k + 1)` is `ex8T k` with a leading `1`. -/
theorem ex8T_succ (k : ℕ) : ex8T (k + 1) = (Fin.cons 1 (ex8T k) : Fin (k + 2) → ℚ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [ex8T]

/-- The all-ones diagonal with a leading `1` split off. -/
theorem ex8_ones_succ (k : ℕ) :
    (fun _ : Fin (k + 4) => (1 : ℚ)) = (Fin.cons 1 (fun _ : Fin (k + 3) => (1 : ℚ)) : Fin (k + 4) → ℚ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

open Matrix in
/-- Adding a common leading diagonal entry to a representation. -/
theorem rep_cons_base {K : Type} [Field K] [CharZero K] [Algebra ℚ K] {N r : ℕ} (b : ℚ)
    (α : Fin N → ℚ) (dt : Fin r → ℚ) (h : Rep K (QuadForm.diag α) (QuadForm.diag dt)) :
    Rep K (QuadForm.diag (Fin.cons b α : Fin (N + 1) → ℚ))
      (QuadForm.diag (Fin.cons b dt : Fin (r + 1) → ℚ)) := by
  obtain ⟨Y, hY⟩ := h
  refine ⟨Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i, fun y => ?_⟩
  have hX : (Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => Y i' j') j) i :
        Matrix (Fin (N + 1)) (Fin (r + 1)) K) *ᵥ y = (Fin.cons (y 0) (Y *ᵥ Fin.tail y) : Fin (N + 1) → K) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.tail]
  rw [hX, evalIn_diag_base K (Fin.cons b α : Fin (N + 1) → ℚ),
    evalIn_diag_base K (Fin.cons b dt : Fin (r + 1) → ℚ), alg_cons, alg_cons, evalIn_diag_cons,
    evalIn_diag_cons]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [← evalIn_diag_base K α, ← evalIn_diag_base K dt, hY]

open Matrix in
/-- Base case over `ℝ`: `⟨1,1,1⟩` represents `⟨7⟩`. -/
theorem ex8_real_base : Rep ℝ (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))) (QuadForm.diag (ex8T 0)) := by
  refine ⟨Matrix.of fun i _ => if i = 0 then Real.sqrt 7 else 0, fun y => ?_⟩
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
  simp [Matrix.mulVec, dotProduct, ex8T, mul_pow, Real.sq_sqrt, mul_comm]

/-- Real part of the induction: `⟨1^{k+3}⟩` represents `⟨1^k, 7⟩` over `ℝ`. -/
theorem ex8_real (k : ℕ) : Rep ℝ (QuadForm.diag (fun _ : Fin (k + 3) => (1 : ℚ))) (QuadForm.diag (ex8T k)) := by
  induction k with
  | zero => exact ex8_real_base
  | succ k ih =>
    rw [ex8T_succ, ex8_ones_succ]
    exact rep_cons_base 1 _ _ ih

/-- Rational part of the induction: cancel leading squares by Witt. -/
theorem ex8_cancel (k : ℕ) (h : Rep ℚ (QuadForm.diag (fun _ : Fin (k + 3) => (1 : ℚ))) (QuadForm.diag (ex8T k))) :
    Rep ℚ (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))) (QuadForm.diag (ex8T 0)) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [ex8T_succ, ex8_ones_succ] at h
    obtain ⟨X, hX⟩ := h
    obtain ⟨Y, hY⟩ := rep_step (K := ℚ) one_ne_zero (fun _ => one_ne_zero) X hX
    exact ih ⟨Y, hY⟩

open Matrix in
/-- Seven is not a sum of three rational squares. -/
theorem ex8_seven_not : ¬ Rep ℚ (QuadForm.diag (fun _ : Fin 3 => (1 : ℚ))) (QuadForm.diag (ex8T 0)) := by
  rintro ⟨X, hX⟩
  have h := hX (Pi.single 0 1)
  have e1 : (QuadForm.diag (ex8T 0)).evalIn ℚ (Pi.single 0 1) = 7 := by
    rw [QuadForm.evalIn_diag]; simp [ex8T]
  rw [e1, QuadForm.evalIn_diag] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply, one_mul] at h
  obtain ⟨y, hy⟩ := DavenportCassels.sum_sq_int_of_rat (m := 3) le_rfl 7
    ⟨fun i => (X *ᵥ Pi.single 0 1) i, by simpa using h⟩
  have hn : (∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = 7) :=
    ⟨(y 0).natAbs, (y 1).natAbs, (y 2).natAbs, by
      have := hy
      simp only [Fin.sum_univ_three] at this
      zify
      simpa [sq_abs] using this⟩
  exact (Grosswald.legendre_three_squares 7).mp hn ⟨0, 0, by norm_num⟩

/-- **Cassels, Ch. 6, Example 8**, second part: *there is no $m \ge 1$ for which the hypothesis $n \ge m + 3$ may be
replaced by $n \ge m + 2$*: the sum $f$ of $m + 2$ squares represents $g = x_0^2 + \cdots + x_{m-2}^2 + 7x_{m-1}^2$ over
$\mathbb R$ (both are positive definite) but not over $\mathbb Q$ (otherwise, cancelling $m - 1$ squares by Witt's
theorem, $7$ would be a sum of three rational squares, hence of three integral squares, which it is not). -/
@[kb "cassels1978" "Ch. 6, Ex. 8, p. 101 (second part: n ≥ m + 2 does not suffice)"]
theorem ex8_sharp (m : ℕ) (hm : 1 ≤ m) :
    Rep ℝ (QuadForm.diag (fun _ : Fin (m + 2) => (1 : ℚ)))
        (QuadForm.diag (fun i : Fin m => if (i : ℕ) = m - 1 then (7 : ℚ) else 1)) ∧
      ¬ Rep ℚ (QuadForm.diag (fun _ : Fin (m + 2) => (1 : ℚ)))
        (QuadForm.diag (fun i : Fin m => if (i : ℕ) = m - 1 then (7 : ℚ) else 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hT : (fun i : Fin (k + 1) => if (i : ℕ) = k + 1 - 1 then (7 : ℚ) else 1) = ex8T k := by
    funext i; simp [ex8T]
  rw [hT]
  exact ⟨ex8_real k, fun h => ex8_seven_not (ex8_cancel k h)⟩

end QuadFormsKB.Cassels.Ch6
