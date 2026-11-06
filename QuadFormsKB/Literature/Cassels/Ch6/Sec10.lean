/-
# Cassels, Chapter 6, §10: finite projective planes, the Bruck–Ryser theorem

**Setting.** A finite projective plane is Mathlib's `Configuration.ProjectivePlane P L` on finite types of points $P$
and lines $L$ (with incidence `p ∈ l`); it includes Cassels' exclusion of degenerate cases (four points in general
position). Its order $n$ is `Configuration.ProjectivePlane.order P L`: every line has $n + 1$ points, every point lies
on $n + 1$ lines, and there are $N = n^2 + n + 1$ points and $N$ lines (`card_points`, `card_lines`).

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6, §10)
* (10.3): with one variable $x_p$ per point and the linear form $L_l(\vec x) = \sum_{p \in l}x_p$ per line,
  $\sum_l L_l(\vec x)^2 = n\sum_p x_p^2 + \bigl(\sum_p x_p\bigr)^2$ (`sum_sq_lines`);
* Lemma 10.1 (Bruck and Ryser): if $n \equiv 1, 2 \pmod 4$, every odd prime dividing $n$ to an odd power is
  $\equiv 1 \pmod 4$ (`bruck_ryser`).

**Proof notes.** As Cassels': by (10.3) the form $g(\vec x) = n\sum x_p^2 + (\sum x_p)^2$ is rationally equivalent to
the sum of $N$ squares (the incidence matrix is invertible, its Gram matrix $nI + J$ having determinant
$n^{N-1}(n+1)^2 \ne 0$), so they have the same Hasse–Minkowski invariants. Instead of Cassels' variables (10.4) (garbled
in the machine-read text; read from the page image and formalized as `bruck_ryser_diag`, `Ch6/Sec10Diag.lean`) the
diagonalization here uses the orthogonal basis $\vec u = (1, \dots, 1)$,
$\vec v_k = \vec e_0 + \cdots + \vec e_k - (k+1)\vec e_{k+1}$ ($0 \le k \le N-2$) of both forms:
$\sum x_p^2 \cong \langle N\rangle \perp W$ and $g \cong \langle N(n+1)^2\rangle \perp nW$ with
$W = \langle 1\cdot2, 2\cdot3, \dots, (N-1)N\rangle$. Comparing $c_p$ (Cassels' Hasse–Minkowski invariant) and using
$N - 1 \equiv 2 \pmod 4$ gives $(n, -N)_p = 1$; for an odd $p$ dividing $n$ to an odd power, $N \equiv 1 \pmod p$, so
this says $(-1/p) = 1$, i.e. $p \equiv 1 \pmod 4$ (Cassels' (10.5)–(10.8) with $(n, -1)_p$).
-/
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import Mathlib.Combinatorics.Configuration
import QuadFormsKB.Witt.Represents
import QuadFormsKB.Literature.LocalGlobal.FieldGeneral
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.Cassels.Ch6.Sec7Steps

namespace QuadFormsKB.Cassels.Ch6

open Configuration Matrix QuadForm

variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L]

open scoped Classical in
/-- Helper: the number of lines through `p` and `q` is `n + 1` if `p = q` and `1` otherwise. -/
theorem card_lines_through [ProjectivePlane P L] (p q : P) :
    (Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card =
      if p = q then ProjectivePlane.order P L + 1 else 1 := by
  split_ifs with h
  · subst h
    have := ProjectivePlane.lineCount_eq L p
    rw [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    simpa using this
  · obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line (P := P) (L := L) p q h
    rw [Finset.card_eq_one]
    refine ⟨l, ?_⟩
    ext l'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h' => hu l' h', fun h' => h' ▸ hl⟩

open scoped Classical in
/-- Helper: expansion of the sum of squares over lines as a double sum over points. -/
theorem sum_sq_lines_expand (x : P → ℚ) :
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2 =
      ∑ p, ∑ q, x p * x q * ((Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card : ℚ) := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hp : p ∈ l <;> by_cases hq : q ∈ l <;> simp [hp, hq]

open scoped Classical in
/-- **Cassels, Ch. 6, §10, (10.3), p. 92**: for a finite projective plane of order $n$ and $x \in \mathbb Q^P$,
$\sum_{l}\bigl(\sum_{p \in l}x_p\bigr)^2 = n\sum_p x_p^2 + \bigl(\sum_p x_p\bigr)^2$ (each point lies on $n + 1$ lines,
two distinct points on exactly one). -/
@[kb "cassels1978" "Ch. 6, §10, (10.3), p. 92"]
theorem sum_sq_lines [ProjectivePlane P L] (x : P → ℚ) :
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2 =
      (ProjectivePlane.order P L : ℚ) * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2 := by
  rw [sum_sq_lines_expand]
  have h : ∀ p q : P, x p * x q * ((Finset.univ.filter fun l : L => p ∈ l ∧ q ∈ l).card : ℚ) =
      x p * x q + (ProjectivePlane.order P L : ℚ) * (if p = q then x p ^ 2 else 0) := by
    intro p q
    rw [card_lines_through]
    by_cases hpq : p = q
    · subst hpq; simp; ring
    · simp [hpq]
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, sq (∑ p, x p), Finset.sum_mul_sum]
  simp
  simp_rw [Finset.mul_sum]
  ring

open scoped Classical in
/-- Helper: the incidence matrix of a finite projective plane of order `n`, with respect to enumerations of the
points and lines by `Fin (n² + n + 1)`, satisfies the identity (10.3). -/
theorem exists_incidence_matrix [ProjectivePlane P L] :
    ∃ A : Matrix (Fin (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1))
        (Fin (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1)) ℚ,
      ∀ x, ∑ i, (A *ᵥ x) i ^ 2 =
        (ProjectivePlane.order P L : ℚ) * ∑ i, x i ^ 2 + (∑ i, x i) ^ 2 := by
  let eP : P ≃ Fin (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1) :=
    Fintype.equivFinOfCardEq (ProjectivePlane.card_points P L)
  let eL : L ≃ Fin (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1) :=
    Fintype.equivFinOfCardEq (ProjectivePlane.card_lines P L)
  refine ⟨Matrix.of fun i j => if eP.symm j ∈ eL.symm i then 1 else 0, fun x => ?_⟩
  have h := sum_sq_lines (P := P) (L := L) (fun p => x (eP p))
  have e1 : ∀ i, ((Matrix.of fun i j => if eP.symm j ∈ eL.symm i then (1 : ℚ) else 0) *ᵥ x) i =
      ∑ p : P, if p ∈ eL.symm i then x (eP p) else 0 := by
    intro i
    simp only [mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [← Equiv.sum_comp eP]
    simp
  simp_rw [e1]
  rw [Equiv.sum_comp eL.symm (fun l : L => (∑ p : P, if p ∈ l then x (eP p) else 0) ^ 2), h]
  simp only [Equiv.sum_comp eP (fun j => x j ^ 2), Equiv.sum_comp eP (fun j => x j)]

/-- Helper: the telescoping (Gram--Schmidt) identity for the sum of squares. -/
theorem parseval_nat (zz : ℕ → ℚ) (M : ℕ) :
    ∑ i ∈ Finset.range (M + 1), zz i ^ 2 =
      (∑ i ∈ Finset.range (M + 1), zz i) ^ 2 / (M + 1) +
        ∑ k ∈ Finset.range M, ((∑ i ∈ Finset.range (k + 1), zz i) - (k + 1) * zz (k + 1)) ^ 2 /
          ((k + 1) * (k + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ (fun i => zz i ^ 2) (M + 1),
      Finset.sum_range_succ (fun i => zz i) (M + 1),
      Finset.sum_range_succ (fun k : ℕ => ((∑ i ∈ Finset.range (k + 1), zz i) - (k + 1) * zz (k + 1)) ^ 2 /
          ((k + 1) * (k + 2))) M]
    have hT := ih
    generalize ∑ k ∈ Finset.range M, ((∑ i ∈ Finset.range (k + 1), zz i) - (k + 1) * zz (k + 1)) ^ 2 /
          ((k + 1) * (k + 2)) = T at hT ⊢
    generalize ∑ i ∈ Finset.range (M + 1), zz i = S at hT ⊢
    generalize ∑ i ∈ Finset.range (M + 1), zz i ^ 2 = Q at hT ⊢
    have h1 : (M : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (M : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h3 : (M : ℚ) + 2 ≠ 0 := by positivity
    have hT' : T = Q - S ^ 2 / (M + 1) := by linarith
    subst hT'
    push_cast
    field_simp
    ring

/-- Helper: the extension by zero of a vector on `Fin N` to `ℕ`. -/
def extNat {N : ℕ} (z : Fin N → ℚ) (i : ℕ) : ℚ := if h : i < N then z ⟨i, h⟩ else 0

/-- Helper: the change-of-basis matrix `Φ` to the orthogonal basis `u, v_0, …, v_{m-1}`. -/
noncomputable def phiMat (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  Matrix.of fun k i => if k = 0 then 1 / ((m : ℚ) + 1) else
    (if (i : ℕ) < k then 1 else if i = k then -((k : ℕ) : ℚ) else 0) / (((k : ℕ) : ℚ) * (((k : ℕ) : ℚ) + 1))

/-- Helper: a sum over `Fin (m + 1)` as a sum over `range (m + 1)` of the zero extension. -/
theorem sum_fin_extNat {m : ℕ} (z : Fin (m + 1) → ℚ) :
    ∑ i : Fin (m + 1), z i = ∑ i ∈ Finset.range (m + 1), extNat z i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => extNat z i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [extNat, i.is_lt, dite_true]

/-- Helper: the coordinate of `Φ z` along `u = (1, …, 1)` is `(∑ z) / N`. -/
theorem phiMat_zero (m : ℕ) (z : Fin (m + 1) → ℚ) :
    (phiMat m *ᵥ z) 0 = (∑ i, z i) / ((m : ℚ) + 1) := by
  simp [phiMat, mulVec, dotProduct, div_eq_mul_inv, Finset.sum_mul, mul_comm]

/-- Helper: the coordinate of `Φ z` along `v_j` is `(∑_{i ≤ j} z_i - (j+1) z_{j+1}) / ((j+1)(j+2))`. -/
theorem phiMat_succ (m : ℕ) (z : Fin (m + 1) → ℚ) (j : Fin m) :
    (phiMat m *ᵥ z) j.succ = ((∑ i ∈ Finset.range ((j : ℕ) + 1), extNat z i) -
        (((j : ℕ) : ℚ) + 1) * extNat z ((j : ℕ) + 1)) / ((((j : ℕ) : ℚ) + 1) * (((j : ℕ) : ℚ) + 2)) := by
  have hj : (j : ℕ) + 1 < m + 1 := by omega
  have e1 : ∀ i : Fin (m + 1), phiMat m j.succ i * z i =
      ((if (i : ℕ) < (j : ℕ) + 1 then extNat z i else 0) +
        (if (i : ℕ) = (j : ℕ) + 1 then -(((j : ℕ) : ℚ) + 1) * extNat z i else 0)) /
        ((((j : ℕ) : ℚ) + 1) * (((j : ℕ) : ℚ) + 2)) := by
    intro i
    have hz : z i = extNat z i := by simp only [extNat, i.is_lt, dite_true]
    simp only [phiMat, Matrix.of_apply, Fin.val_succ, Fin.ext_iff]
    push_cast
    rw [hz]
    by_cases h1 : (i : ℕ) < (j : ℕ) + 1
    · have : ¬ (i : ℕ) = (j : ℕ) + 1 := by omega
      have hp1 : ((j : ℕ) : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : ((j : ℕ) : ℚ) + 2 ≠ 0 := by positivity
      have hp3 : ((j : ℕ) : ℚ) + 1 + 1 ≠ 0 := by positivity
      simp [h1, this]
      field_simp
      ring
    · by_cases h2 : (i : ℕ) = (j : ℕ) + 1
      · simp [h2]
        ring
      · simp [h1, h2]
  simp only [mulVec, dotProduct, e1, ← Finset.sum_div, Finset.sum_add_distrib]
  have s1 : ∑ i : Fin (m + 1), (if (i : ℕ) < (j : ℕ) + 1 then extNat z i else 0) =
      ∑ i ∈ Finset.range ((j : ℕ) + 1), extNat z i := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) + 1 then extNat z i else 0) (m + 1),
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have s2 : ∑ i : Fin (m + 1), (if (i : ℕ) = (j : ℕ) + 1 then -(((j : ℕ) : ℚ) + 1) * extNat z i else 0) =
      -(((j : ℕ) : ℚ) + 1) * extNat z ((j : ℕ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i => if i = (j : ℕ) + 1 then -(((j : ℕ) : ℚ) + 1) * extNat z i else 0) (m + 1)]
    rw [Finset.sum_eq_single ((j : ℕ) + 1)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  rw [s1, s2]
  ring

/-- Helper: Parseval for the orthogonal basis, `∑ z_i² = N y_0² + ∑ (k+1)(k+2) y_{k+1}²` with `y = Φ z`. -/
theorem phiMat_sq (m : ℕ) (z : Fin (m + 1) → ℚ) :
    ∑ i, z i ^ 2 = ((m : ℚ) + 1) * (phiMat m *ᵥ z) 0 ^ 2 +
      ∑ k : Fin m, (((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2) * (phiMat m *ᵥ z) k.succ ^ 2 := by
  have h := parseval_nat (extNat z) m
  have hz : ∀ i : Fin (m + 1), z i = extNat z i := fun i => by simp only [extNat, i.is_lt, dite_true]
  have e1 : ∑ i, z i ^ 2 = ∑ i ∈ Finset.range (m + 1), extNat z i ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => extNat z i ^ 2)]
    exact Finset.sum_congr rfl fun i _ => by rw [← hz]
  rw [e1, h, phiMat_zero, ← sum_fin_extNat z]
  simp_rw [phiMat_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k => (((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2) *
    (((∑ i ∈ Finset.range (k + 1), extNat z i) - (((k : ℕ) : ℚ) + 1) * extNat z (k + 1)) /
      ((((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2))) ^ 2) m]
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ((k : ℕ) : ℚ) + 1 ≠ 0 := by positivity
    have h2 : ((k : ℕ) : ℚ) + 2 ≠ 0 := by positivity
    field_simp

/-- Helper: `∑ z_i = N · (Φ z)_0`. -/
theorem phiMat_sum (m : ℕ) (z : Fin (m + 1) → ℚ) : ∑ i, z i = ((m : ℚ) + 1) * (phiMat m *ᵥ z) 0 := by
  rw [phiMat_zero]
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp

/-- Helper: `Φ` is invertible. -/
theorem phiMat_det_ne_zero (m : ℕ) : (phiMat m).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv
  have h0 := phiMat_sq m v
  rw [hmv] at h0
  simp only [Pi.zero_apply] at h0
  have h1 : ∑ i, v i ^ 2 = 0 := by rw [h0]; simp
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h1
  funext i
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (h1 i (Finset.mem_univ i))

/-- Helper: the value of a diagonal form `⟨a, b_0, …, b_{m-1}⟩` over `ℚ`. -/
theorem evalIn_diag_cons_val {m : ℕ} (a : ℚ) (b : Fin m → ℚ) (x : Fin (m + 1) → ℚ) :
    (diag (Fin.cons a b : Fin (m + 1) → ℚ)).evalIn ℚ x = a * x 0 ^ 2 + ∑ k, b k * x k.succ ^ 2 := by
  rw [evalIn_diag, Fin.sum_univ_succ]
  simp

/-- Helper: a matrix satisfying the identity (10.3) with `n > 0` is invertible. -/
theorem det_ne_zero_of_sq {N n : ℕ} (hn : 0 < n) (A : Matrix (Fin N) (Fin N) ℚ)
    (hA : ∀ x, ∑ i, (A *ᵥ x) i ^ 2 = n * ∑ i, x i ^ 2 + (∑ i, x i) ^ 2) : A.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  apply hv
  have h0 := hA v
  rw [hmv] at h0
  simp only [Pi.zero_apply] at h0
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h0' : (n : ℚ) * ∑ i, v i ^ 2 + (∑ i, v i) ^ 2 = 0 := by rw [← h0]; simp
  have h1 : ∑ i, v i ^ 2 = 0 := by
    have : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [sq_nonneg (∑ i, v i)]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h1
  funext i
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (h1 i (Finset.mem_univ i))

/-- Helper: the two diagonalized forms are rationally isometric. -/
theorem diag_isometric_of_incidence (m n : ℕ) (hn : 0 < n) (hm : m = n ^ 2 + n)
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ x, ∑ i, (A *ᵥ x) i ^ 2 = n * ∑ i, x i ^ 2 + (∑ i, x i) ^ 2) :
    (diag (Fin.cons ((m : ℚ) + 1) (fun k : Fin m => (((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2)) :
        Fin (m + 1) → ℚ)).IsometricIn ℚ
      (diag (Fin.cons (((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2)
        (fun k : Fin m => (n : ℚ) * ((((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2))) : Fin (m + 1) → ℚ)) := by
  have hAd := det_ne_zero_of_sq hn A hA
  have hΦ := phiMat_det_ne_zero m
  have hmq : (m : ℚ) = (n : ℚ) ^ 2 + n := by exact_mod_cast hm
  refine ⟨phiMat m * A * (phiMat m)⁻¹, ?_, fun y => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv]
    refine IsUnit.mul (IsUnit.mul (isUnit_iff_ne_zero.mpr hΦ) (isUnit_iff_ne_zero.mpr hAd)) ?_
    simp [Ring.inverse_eq_inv', hΦ]
  · have hU : IsUnit (phiMat m).det := isUnit_iff_ne_zero.mpr hΦ
    obtain ⟨u, rfl⟩ : ∃ u, y = phiMat m *ᵥ u :=
      ⟨(phiMat m)⁻¹ *ᵥ y, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]⟩
    have e : (phiMat m * A * (phiMat m)⁻¹) *ᵥ (phiMat m *ᵥ u) = phiMat m *ᵥ (A *ᵥ u) := by
      rw [Matrix.mulVec_mulVec]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
      rw [← Matrix.mulVec_mulVec]
    rw [e, evalIn_diag_cons_val, evalIn_diag_cons_val]
    have h1 := phiMat_sq m (A *ᵥ u)
    have h2 := hA u
    have h3 := phiMat_sq m u
    have h4 := phiMat_sum m u
    have hW : ∑ k : Fin m, (n : ℚ) * ((((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2)) *
        (phiMat m *ᵥ u) k.succ ^ 2 = (n : ℚ) * ∑ k : Fin m, (((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2) *
        (phiMat m *ᵥ u) k.succ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    linear_combination (-1) * h1 + h2 + (n : ℚ) * h3 + ((∑ i, u i) + ((m : ℚ) + 1) * (phiMat m *ᵥ u) 0) * h4
      - hW + (((m : ℚ) + 1) * (phiMat m *ᵥ u) 0 ^ 2) * hmq

/-- Helper: a product of a constant over all pairs `i < j` is the constant to the power `C(k, 2)`. -/
theorem prod_pairs_const (c : ℤ) (k : ℕ) :
    ∏ i : Fin k, ∏ j : Fin k, (if i < j then c else 1) = c ^ k.choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ (n := k), Fin.succ_pos, Fin.succ_lt_succ_iff, ite_true,
      Fin.not_lt_zero, ite_false, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [ih, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- Helper: `∏_{i<j} f_i f_j = (∏ f)^(k-1)`. -/
theorem prod_pairs_mul {M : Type*} [CommMonoid M] (k : ℕ) (f : Fin k → M) :
    ∏ i : Fin k, ∏ j : Fin k, (if i < j then f i * f j else 1) = (∏ i, f i) ^ (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    simp only [Fin.prod_univ_succ (n := k), Fin.succ_pos, Fin.succ_lt_succ_iff, ite_true,
      Fin.not_lt_zero, ite_false, one_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    rw [ih (fun i => f i.succ)]
    rcases k with _ | k
    · simp
    · simp only [mul_pow, Nat.add_one_sub_one]
      rw [mul_assoc, ← pow_succ']

/-- Helper: bimultiplicativity of the Hilbert symbol in both arguments. -/
theorem hilbert_mul_mul (v : RatPlace) {a a' b b' : ℚ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hb : b ≠ 0) (hb' : b' ≠ 0) :
    v.hilbert (a * a') (b * b') = v.hilbert a b * v.hilbert a b' * (v.hilbert a' b * v.hilbert a' b') := by
  rw [HilbertLocal.RatPlace.hilbert_mul_left v a a' (b * b') ha ha' (mul_ne_zero hb hb'),
    RatPlace.hilbert_mul_right v a b b' ha hb hb', RatPlace.hilbert_mul_right v a' b b' ha' hb hb']

/-- Helper: Cassels' `c_v` of a scaled diagonal form. -/
theorem hasseCassels_smul (v : RatPlace) {n : ℚ} (hn : n ≠ 0) {k : ℕ} (β : Fin k → ℚ)
    (hβ : ∀ i, β i ≠ 0) :
    v.hasseCassels (fun i => n * β i) =
      v.hilbert n n ^ k.choose 2 * v.hilbert n (∏ i, β i) ^ (k - 1) * v.hasseCassels β := by
  unfold RatPlace.hasseCassels
  have pt : ∀ i j : Fin k, (if i < j then v.hilbert (n * β i) (n * β j) else 1) =
      (if i < j then v.hilbert n n else 1) *
        (if i < j then v.hilbert n (β i) * v.hilbert n (β j) else 1) *
        (if i < j then v.hilbert (β i) (β j) else 1) := by
    intro i j
    split_ifs with h
    · rw [hilbert_mul_mul v hn (hβ i) hn (hβ j), RatPlace.hilbert_comm v (β i) n]
      ring
    · simp
  simp only [pt, Finset.prod_mul_distrib]
  rw [prod_pairs_const, prod_pairs_mul k (fun i => v.hilbert n (β i)),
    ← hilbert_prod_right_aux v hn β hβ]

/-- Helper: a natural number prime to `p` is a `p`-adic unit. -/
theorem isUnit_natCast_padic {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (ha : ¬ p ∣ a) :
    IsUnit ((a : ℤ) : ℤ_[p]) := by
  refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ha ?_))
  have := (PadicInt.norm_int_lt_one_iff_dvd (p := p) (a : ℤ)).mp hlt
  exact_mod_cast this

/-- Helper: the local computation at an odd prime `p` dividing `n` to an odd power, when `N ≡ 1 (mod p)`. -/
theorem local_negOne_square {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (n N : ℕ) (hn0 : n ≠ 0)
    (hodd : Odd (padicValNat p n)) (hN : (N : ZMod p) = 1)
    (h : RatPlace.hilbert (.finite ⟨p, hp.out⟩) (n : ℚ) (-(N : ℚ)) = 1) : p % 4 = 1 := by
  obtain ⟨e, n', hn', hneq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  have hn'0 : n' ≠ 0 := by rintro rfl; simp at hneq; exact hn0 hneq
  have he : padicValNat p n = e := by
    rw [hneq, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hn'0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hn', add_zero]
  rw [he] at hodd
  have uN : IsUnit (((-(N : ℤ)) : ℤ) : ℤ_[p]) := by
    have hnd : ¬ p ∣ N := by
      intro hd
      have : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).mpr hd
      rw [hN] at this
      exact one_ne_zero this
    have := isUnit_natCast_padic (p := p) hnd
    have e2 : (((-(N : ℤ)) : ℤ) : ℤ_[p]) = -((N : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [e2]
    exact this.neg
  set u := (isUnit_natCast_padic (p := p) hn').unit with hu
  set v := uN.unit with hv
  have key := HilbertLocal.hilbertSymbol_odd_formula hp2 e 0 u v
  have e1 : (p : ℚ_[p]) ^ e * ((u : ℤ_[p]) : ℚ_[p]) = ((n : ℚ) : ℚ_[p]) := by
    rw [hu, hneq]
    simp
  have e2 : (p : ℚ_[p]) ^ 0 * ((v : ℤ_[p]) : ℚ_[p]) = ((-(N : ℚ) : ℚ) : ℚ_[p]) := by
    rw [hv]
    simp
  rw [e1, e2] at key
  have h' : hilbertSymbol ℚ_[p] ((n : ℚ) : ℚ_[p]) ((-(N : ℚ) : ℚ) : ℚ_[p]) = 1 := h
  rw [h'] at key
  have hc : HilbertLocal.unitChar v = quadraticChar (ZMod p) (-1) := by
    unfold HilbertLocal.unitChar
    rw [hv]
    simp [hN]
  rw [hc] at key
  simp only [mul_zero, zero_mul, pow_zero, one_mul] at key
  have hne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hq : quadraticChar (ZMod p) (-1) = 1 := by
    rcases quadraticChar_dichotomy hne with h1 | h1
    · exact h1
    · rw [h1, hodd.neg_one_pow] at key
      norm_num at key
  have hsq := (quadraticChar_one_iff_isSquare hne).mp hq
  have h4 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  rcases hp.out.eq_two_or_odd with h2 | h2
  · exact absurd h2 hp2
  · omega

/-- Helper: the sequence `w_k = (k + 1)(k + 2)` of diagonal entries of `W`. -/
def wSeq (m : ℕ) : Fin m → ℚ := fun k => (((k : ℕ) : ℚ) + 1) * (((k : ℕ) : ℚ) + 2)

/-- Helper: the entries `w_k` are nonzero. -/
theorem wSeq_ne_zero (m : ℕ) (k : Fin m) : wSeq m k ≠ 0 := by
  unfold wSeq; positivity

/-- Helper: `∏_{k<m} (k+1)(k+2) = (m+1)·(m!)²`. -/
theorem prod_wSeq (m : ℕ) : ∏ k : Fin m, wSeq m k = ((m : ℚ) + 1) * ((m.factorial : ℚ)) ^ 2 := by
  unfold wSeq
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => ((k : ℚ) + 1) * ((k : ℚ) + 2)) m]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- Helper: `n² + n ≡ 2 (mod 4)` when `n ≡ 1, 2 (mod 4)`. -/
theorem mod_four_of_order {n : ℕ} (h4 : n % 4 = 1 ∨ n % 4 = 2) : (n ^ 2 + n) % 4 = 2 := by
  rcases h4 with h | h <;> simp [pow_two, Nat.add_mod, Nat.mul_mod, h]

/-- Helper: an odd power of `±1` is itself. -/
theorem pow_pm_odd {x : ℤ} (hx : x = 1 ∨ x = -1) {k : ℕ} (hk : Odd k) : x ^ k = x := by
  rcases hx with rfl | rfl
  · simp
  · exact hk.neg_one_pow

/-- Helper: `C(m, 2)` is odd when `m ≡ 2 (mod 4)`. -/
theorem choose_two_odd {m : ℕ} (hm : m % 4 = 2) : Odd (m.choose 2) := by
  obtain ⟨q, rfl⟩ : ∃ q, m = 4 * q + 2 := ⟨m / 4, by omega⟩
  rw [Nat.choose_two_right]
  have h1 : (4 * q + 2) * (4 * q + 2 - 1) = 2 * ((2 * q + 1) * (4 * q + 1)) := by
    have : 4 * q + 2 - 1 = 4 * q + 1 := by omega
    rw [this]; ring
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num)]
  exact (odd_two_mul_add_one q).mul ⟨2 * q, by ring⟩

/-- Helper: the Hilbert symbol `(N(n+1)², ∏ n w_k)_v` equals `(N, ∏ w_k)_v` when `m` is even. -/
theorem hilbert_d2_const (v : RatPlace) (m n : ℕ) (hn : 0 < n) (hm2 : m % 2 = 0) :
    v.hilbert (((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2) (∏ k : Fin m, (n : ℚ) * wSeq m k) =
      v.hilbert ((m : ℚ) + 1) (∏ k : Fin m, wSeq m k) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hW : ∏ k : Fin m, wSeq m k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => wSeq_ne_zero m k
  have hprod : ∏ k : Fin m, (n : ℚ) * wSeq m k = (n : ℚ) ^ m * ∏ k : Fin m, wSeq m k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnm : (n : ℚ) ^ m = ((n : ℚ) ^ (m / 2)) ^ 2 := by
    rw [← pow_mul]; congr 1; omega
  have hnm0 : (n : ℚ) ^ m ≠ 0 := pow_ne_zero _ hnq
  rw [hprod, HilbertLocal.RatPlace.hilbert_mul_left v _ _ _ hN0 (pow_ne_zero 2 hn1) (mul_ne_zero hnm0 hW),
    RatPlace.hilbert_comm v (((n : ℚ) + 1) ^ 2), RatPlace.hilbert_sq_right v _ _ hn1,
    RatPlace.hilbert_mul_right v _ _ _ hN0 hnm0 hW, hnm,
    RatPlace.hilbert_sq_right v _ _ (pow_ne_zero _ hnq)]
  ring

/-- Helper: `(n, -N)_v = 1` at every place `v`, where `N = m + 1 = n² + n + 1`. -/
theorem hilbert_order_neg_eq_one (m n : ℕ) (hn : 0 < n) (hm : m = n ^ 2 + n)
    (h4 : n % 4 = 1 ∨ n % 4 = 2) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (hA : ∀ x, ∑ i, (A *ᵥ x) i ^ 2 = n * ∑ i, x i ^ 2 + (∑ i, x i) ^ 2) (v : RatPlace) :
    v.hilbert (n : ℚ) (-((m : ℚ) + 1)) = 1 := by
  have hiso : (diag (Fin.cons ((m : ℚ) + 1) (wSeq m) : Fin (m + 1) → ℚ)).IsometricIn ℚ
      (diag (Fin.cons (((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2) (fun k : Fin m => (n : ℚ) * wSeq m k) :
        Fin (m + 1) → ℚ)) := diag_isometric_of_incidence m n hn hm A hA
  have hm4 : m % 4 = 2 := by rw [hm]; exact mod_four_of_order h4
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hnw : ∀ k : Fin m, (n : ℚ) * wSeq m k ≠ 0 := fun k => mul_ne_zero hnq (wSeq_ne_zero m k)
  have hN2 : ((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
  have hd1 : ∀ i, (Fin.cons ((m : ℚ) + 1) (wSeq m) : Fin (m + 1) → ℚ) i ≠ 0 :=
    fun i => Fin.cases hN0 (fun j => wSeq_ne_zero m j) i
  have hd2 : ∀ i, (Fin.cons (((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2) (fun k : Fin m => (n : ℚ) * wSeq m k) :
      Fin (m + 1) → ℚ) i ≠ 0 := fun i => Fin.cases hN2 (fun j => hnw j) i
  have hiso' : RatPlace.atPlace (fun K _ _ => (diag (Fin.cons ((m : ℚ) + 1) (wSeq m) :
      Fin (m + 1) → ℚ)).IsometricIn K
      (diag (Fin.cons (((m : ℚ) + 1) * ((n : ℚ) + 1) ^ 2) (fun k : Fin m => (n : ℚ) * wSeq m k) :
        Fin (m + 1) → ℚ))) v := by
    cases v with
    | infinite => exact FieldGen.isometricIn_of_base ℝ hiso
    | finite p =>
      have : Fact p.1.Prime := ⟨p.2⟩
      exact FieldGen.isometricIn_of_base ℚ_[p.1] hiso
  have hc := RatPlace.hasseCassels_isometric v _ _ hd1 hd2 hiso'
  rw [hasseCassels_cons v hN0 (wSeq m) (wSeq_ne_zero m),
    hasseCassels_cons v hN2 (fun k : Fin m => (n : ℚ) * wSeq m k) hnw,
    hasseCassels_smul v hnq (wSeq m) (wSeq_ne_zero m),
    hilbert_d2_const v m n hn (by omega)] at hc
  have hW0 : ∏ k : Fin m, wSeq m k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => wSeq_ne_zero m k
  have ha0 : v.hilbert ((m : ℚ) + 1) (∏ k : Fin m, wSeq m k) ≠ 0 := by
    rcases RatPlace.hilbert_pm v ((m : ℚ) + 1) (∏ k : Fin m, wSeq m k) with h | h <;> simp [h]
  have hcw0 : v.hasseCassels (wSeq m) ≠ 0 := by
    rcases hasseCassels_pm v (wSeq m) with h | h <;> simp [h]
  have h1 := mul_left_cancel₀ ha0 hc
  have h2 : v.hilbert (n : ℚ) n ^ m.choose 2 * v.hilbert (n : ℚ) (∏ k : Fin m, wSeq m k) ^ (m - 1) = 1 := by
    have : (v.hilbert (n : ℚ) n ^ m.choose 2 * v.hilbert (n : ℚ) (∏ k : Fin m, wSeq m k) ^ (m - 1)) *
        v.hasseCassels (wSeq m) = 1 * v.hasseCassels (wSeq m) := by
      rw [one_mul]; exact h1.symm
    exact mul_right_cancel₀ hcw0 this
  rw [pow_pm_odd (RatPlace.hilbert_pm v (n : ℚ) n) (choose_two_odd hm4),
    pow_pm_odd (RatPlace.hilbert_pm v (n : ℚ) _) (⟨(m - 1) / 2, by omega⟩ : Odd (m - 1)),
    RatPlace.hilbert_self v n hnq,
    ← RatPlace.hilbert_mul_right v n (-1) _ hnq (by norm_num) hW0, prod_wSeq] at h2
  have e : (-1 : ℚ) * (((m : ℚ) + 1) * (m.factorial : ℚ) ^ 2) = (-((m : ℚ) + 1)) * (m.factorial : ℚ) ^ 2 := by
    ring
  have hf : (m.factorial : ℚ) ≠ 0 := by positivity
  rw [e, RatPlace.hilbert_mul_right v n _ _ hnq (neg_ne_zero.mpr hN0) (pow_ne_zero 2 hf),
    RatPlace.hilbert_sq_right v n _ hf, mul_one] at h2
  exact h2

/-- **Cassels, Ch. 6, Lemma 10.1** (Bruck and Ryser): *let $n$ be the order of a finite projective plane and suppose
that $n \equiv 1$ or $2 \pmod 4$. Then every odd prime $p$ which divides $n$ to an odd power satisfies
$p \equiv 1 \pmod 4$.* -/
@[kb "cassels1978" "Ch. 6, Lemma 10.1, pp. 91–93 (Bruck–Ryser)"]
theorem bruck_ryser [ProjectivePlane P L] (hn : ProjectivePlane.order P L % 4 = 1 ∨ ProjectivePlane.order P L % 4 = 2)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hodd : Odd (padicValNat p (ProjectivePlane.order P L))) :
    p % 4 = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hn1 := ProjectivePlane.one_lt_order P L
  obtain ⟨A, hA⟩ := exists_incidence_matrix (P := P) (L := L)
  generalize ProjectivePlane.order P L = n at *
  have hn0 : 0 < n := by omega
  have hpn : p ∣ n := dvd_of_one_le_padicValNat hodd.pos
  have hN : ((n ^ 2 + n + 1 : ℕ) : ZMod p) = 1 := by
    have : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).mpr hpn
    push_cast
    rw [this]; ring
  refine local_negOne_square hp2 n (n ^ 2 + n + 1) hn0.ne' hodd hN ?_
  have := hilbert_order_neg_eq_one (n ^ 2 + n) n hn0 rfl hn A hA (.finite ⟨p, hp⟩)
  push_cast at this ⊢
  exact this

end QuadFormsKB.Cassels.Ch6
