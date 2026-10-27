/-
# Cassels, Chapter 11, Theorem 6.3 and Corollary: rational substitutions between forms

**Layer:** integer forms $f$ = `QuadForm ℤ n` (classically integral, determinant $d$ with $\det H = 2^nd$); a rational
substitution $y = Tx$ with $f_2(y) = f_1(x)$, i.e. $f_1(x) = f_2(Tx)$; $m = [n/2]$; $p$-integrality of a rational
number: $p \nmid$ its denominator.

**Proves**
* Theorem 6.3 (p. 226) (`exists_special_bases_of_subst`): if $T$ is $p$-integral for $p \mid 2d$ and $\det T = \pm1$,
  there are positive integers $s_1, \dots, s_m$ with $s_{i+1} \mid s_i$ and integral substitutions $x = UX$,
  $y = VY$ ($\det U, \det V = \pm1$) such that $Y_i = s_iX_i$ ($i \le m$), $X_{n+1-i} = s_iY_{n+1-i}$ ($i \le m$) and
  $X_{m+1} = Y_{m+1}$ ($n$ odd); i.e. $V^{-1}TU = \mathrm{diag}(s_1, \dots, s_m, [1], s_m^{-1}, \dots, s_1^{-1})$.
  0-based: $D_{jj} = s_j$ for $j < m$, $D_{jj} = 1$ for $j = m$ ($n$ odd), $D_{jj} = s_{n-1-j}^{-1}$ for $j \ge n - m$.
  (The displays (6.7)–(6.11) are partly garbled in the scan and are read from the proof via Lemma 5.1.)
* Theorem 6.3, last part (`sameProperSpinorGenus_of_subst`): for $n \ge 3$, $\mathcal S_{f_2} = g(W)\mathcal S_{f_1}$
  with $W = s_1\cdots s_m = I(\Lambda, \Gamma)$ ((6.12)–(6.13), unfolded as in Theorem 4.1).
* Corollary (p. 227) (`casselsW_eq_lcm_minors`): $W$ is the least common multiple of the denominators of the
  $m \times m$ minors of $T$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec6Cor
import QuadFormsKB.Literature.Cassels.Ch11Sec5Lemma

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

variable {n : ℕ}

/-- Cassels' diagonal matrix of Theorem 6.3 (0-based): $s_j$ for $j < m$, $1$ in the middle ($n$ odd),
$s_{n-1-j}^{-1}$ for $j \ge n - m$, where $m = [n/2]$. -/
def casselsSDiag (s : Fin (n / 2) → ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun j =>
    if h : j.1 < n / 2 then (s ⟨j.1, h⟩ : ℚ)
    else if h' : n - n / 2 ≤ j.1 then ((s ⟨n - 1 - j.1, by omega⟩ : ℚ))⁻¹ else 1

/-! ### Minors: a rectangular Cauchy–Binet expansion and the denominators of the minors -/

section Minors

/-- Rectangular Cauchy–Binet, summing over all functions $p$: $\det(AB) = \sum_p (\prod_i A_{i,p(i)})
\det(B_{p,\cdot})$ for $A$ of size $m \times k$ and $B$ of size $k \times m$. -/
theorem det_mul_rect {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * (B.submatrix p id).det := by
  classical
  have key : ∀ M : Matrix (Fin m) (Fin m) R,
      M.det = ∑ σ : Equiv.Perm (Fin m), (Equiv.Perm.sign σ : ℤ) • ∏ i, M i (σ i) := by
    intro M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  rw [key (A * B)]
  have h1 : ∀ σ : Equiv.Perm (Fin m), ∏ i, (A * B) i (σ i) =
      ∑ p : Fin m → Fin k, (∏ i, A i (p i)) * ∏ i, B (p i) (σ i) := by
    intro σ
    simp_rw [Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib]
  simp_rw [h1, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [key (B.submatrix p id), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul, Matrix.submatrix_apply, id]
  ring

/-- The same, summing over the columns of $A$. -/
theorem det_mul_rect' {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ q : Fin m → Fin k, (A.submatrix id q).det * ∏ i, B (q i) i := by
  rw [← Matrix.det_transpose, Matrix.transpose_mul, det_mul_rect]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_comm]
  congr 1
  · rw [← Matrix.det_transpose]
    congr 1

theorem submatrix_mul_id {R : Type*} [CommRing R] {m k l : ℕ} (A : Matrix (Fin l) (Fin k) R)
    (B : Matrix (Fin k) (Fin l) R) (a b : Fin m → Fin l) :
    (A * B).submatrix a b = A.submatrix a id * B.submatrix id b := by
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply]

theorem det_submatrix_rows_eq_zero {R : Type*} [CommRing R] {m k : ℕ} {p : Fin m → Fin k}
    (hp : ¬ Function.Injective p) (M : Matrix (Fin k) (Fin m) R) : (M.submatrix p id).det = 0 := by
  unfold Function.Injective at hp
  push Not at hp
  obtain ⟨i, j, hij, hne⟩ := hp
  exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hij])

theorem det_submatrix_cols_eq_zero {R : Type*} [CommRing R] {m k : ℕ} {q : Fin m → Fin k}
    (hq : ¬ Function.Injective q) (M : Matrix (Fin m) (Fin k) R) : (M.submatrix id q).det = 0 := by
  unfold Function.Injective at hq
  push Not at hq
  obtain ⟨i, j, hij, hne⟩ := hq
  exact Matrix.det_zero_of_column_eq hne (by intro c; simp [hij])

theorem det_mem_subring {m : ℕ} (R0 : Subring ℚ) (M : Matrix (Fin m) (Fin m) ℚ)
    (h : ∀ i j, M i j ∈ R0) : M.det ∈ R0 := by
  rw [Matrix.det_apply]
  exact Subring.sum_mem _ fun σ _ => by
    rw [Units.smul_def]
    exact Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => h _ _) _

/-- Numerators of the diagonal of `casselsSDiag`. -/
def sNum (s : Fin (n / 2) → ℕ) (j : Fin n) : ℕ := if h : j.1 < n / 2 then s ⟨j.1, h⟩ else 1

/-- Denominators of the diagonal of `casselsSDiag`. -/
def sDen (s : Fin (n / 2) → ℕ) (j : Fin n) : ℕ :=
  if h : n - n / 2 ≤ j.1 then s ⟨n - 1 - j.1, by have := j.2; omega⟩ else 1

theorem casselsSDiag_apply_diag (s : Fin (n / 2) → ℕ) (j : Fin n) :
    casselsSDiag s j j = (sNum s j : ℚ) / (sDen s j : ℚ) := by
  unfold casselsSDiag sNum sDen
  rw [Matrix.diagonal_apply_eq]
  by_cases h : j.1 < n / 2
  · have h' : ¬ n - n / 2 ≤ j.1 := by omega
    simp [h, h']
  · by_cases h' : n - n / 2 ≤ j.1
    · simp [h, h']
    · simp [h, h']

theorem casselsSDiag_apply_ne (s : Fin (n / 2) → ℕ) {i j : Fin n} (h : i ≠ j) : casselsSDiag s i j = 0 := by
  unfold casselsSDiag
  rw [Matrix.diagonal_apply_ne _ h]

theorem sDen_prod_dvd (s : Fin (n / 2) → ℕ) (S : Finset (Fin n)) : ∏ j ∈ S, sDen s j ∣ ∏ i, s i := by
  classical
  let g : Fin (n / 2) → Fin n := fun i => ⟨n - 1 - i.1, by have := i.2; omega⟩
  have hg : Function.Injective g := by
    intro i j hij
    have := congrArg Fin.val hij
    simp only [g] at this
    have := i.2; have := j.2
    exact Fin.ext (by omega)
  set T : Finset (Fin n) := Finset.univ.image g with hT
  have hgT : ∀ i, sDen s (g i) = s i := by
    intro i
    have h1 : n - n / 2 ≤ (g i).1 := by have := i.2; simp only [g]; omega
    simp only [sDen, dif_pos h1]
    congr 1
    apply Fin.ext
    simp only [g]
    have := i.2
    omega
  have hout : ∀ x, x ∉ T → sDen s x = 1 := by
    intro x hx
    by_contra hne
    apply hx
    have h1 : n - n / 2 ≤ x.1 := by
      by_contra hc
      exact hne (by simp [sDen, hc])
    refine Finset.mem_image.2 ⟨⟨n - 1 - x.1, by have := x.2; omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [g]
    have := x.2
    omega
  have e1 : ∏ j ∈ S ∩ T, sDen s j = ∏ j ∈ S, sDen s j :=
    Finset.prod_subset Finset.inter_subset_left (fun x _ hx => hout x (fun h => hx (Finset.mem_inter.2 ⟨‹_›, h⟩)))
  have e2 : ∏ j ∈ T, sDen s j = ∏ i, s i := by
    rw [hT, Finset.prod_image (fun a _ b _ h => hg h)]
    exact Finset.prod_congr rfl fun i _ => hgT i
  rw [← e1, ← e2]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_right

theorem W_mul_prod_int (s : Fin (n / 2) → ℕ) (hs : ∀ i, 0 < s i) (S : Finset (Fin n)) :
    ((∏ i, s i : ℕ) : ℚ) * ∏ j ∈ S, casselsSDiag s j j ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨c, hc⟩ := sDen_prod_dvd s S
  have hden : ∀ j, (sDen s j : ℚ) ≠ 0 := by
    intro j
    have : 0 < sDen s j := by
      unfold sDen
      split_ifs
      · exact hs _
      · exact one_pos
    exact_mod_cast this.ne'
  have hD : (∏ j ∈ S, (sDen s j : ℚ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hden j
  simp_rw [casselsSDiag_apply_diag]
  rw [Finset.prod_div_distrib, hc]
  refine ⟨((c * ∏ j ∈ S, sNum s j : ℕ) : ℤ), ?_⟩
  simp only [eq_intCast]
  push_cast
  field_simp

theorem int_inv_of_det {k : ℕ} (U : Matrix (Fin k) (Fin k) ℤ) (hU : U.det = 1 ∨ U.det = -1) :
    ∃ W : Matrix (Fin k) (Fin k) ℤ, U * W = 1 ∧ W * U = 1 := by
  have hu : IsUnit U.det := by rcases hU with h | h <;> simp [h]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det U).2 hu
  subst hu'
  exact ⟨↑u⁻¹, u.mul_inv, u.inv_mul⟩

theorem intCast_map_mul {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℤ) :
    (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) :=
  (Int.castRingHom ℚ).mapMatrix.map_mul A B

theorem intCast_map_one {k : ℕ} : (1 : Matrix (Fin k) (Fin k) ℤ).map (Int.cast : ℤ → ℚ) = 1 :=
  (Int.castRingHom ℚ).mapMatrix.map_one

theorem intCast_mem_range (z : ℤ) : (z : ℚ) ∈ (Int.castRingHom ℚ).range := ⟨z, rfl⟩

theorem minor_W_mem (T : Matrix (Fin n) (Fin n) ℚ) (s : Fin (n / 2) → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ)
    (hs : ∀ i, 0 < s i) (hU : U.det = 1 ∨ U.det = -1)
    (hTUV : T * U.map (Int.cast : ℤ → ℚ) = V.map (Int.cast : ℤ → ℚ) * casselsSDiag s)
    (a b : Fin (n / 2) → Fin n) :
    ((∏ i, s i : ℕ) : ℚ) * (T.submatrix a b).det ∈ (Int.castRingHom ℚ).range := by
  classical
  obtain ⟨Ui, hUUi, hUiU⟩ := int_inv_of_det U hU
  set R0 := (Int.castRingHom ℚ).range with hR0
  set W : ℚ := ((∏ i, s i : ℕ) : ℚ) with hW
  set D := casselsSDiag s with hD
  have hT : T = V.map (Int.cast : ℤ → ℚ) * (D * Ui.map (Int.cast : ℤ → ℚ)) := by
    rw [← Matrix.mul_assoc, ← hTUV, Matrix.mul_assoc, ← intCast_map_mul, hUUi, intCast_map_one,
      Matrix.mul_one]
  have e1 : (T.submatrix a b).det = ∑ p : Fin (n / 2) → Fin n,
      (∏ i, (V.map (Int.cast : ℤ → ℚ)) (a i) (p i)) *
        ∑ r : Fin (n / 2) → Fin n, (∏ i, D (p i) (r i)) *
          (((Ui.map (Int.cast : ℤ → ℚ))).submatrix r b).det := by
    rw [hT, submatrix_mul_id, det_mul_rect]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h2 : ((D * Ui.map (Int.cast : ℤ → ℚ)).submatrix id b).submatrix p id =
        D.submatrix p id * (Ui.map (Int.cast : ℤ → ℚ)).submatrix id b := by
      rw [← submatrix_mul_id]; rfl
    rw [h2, det_mul_rect]
    rfl
  have term : ∀ p r : Fin (n / 2) → Fin n,
      (∏ i, (V.map (Int.cast : ℤ → ℚ)) (a i) (p i)) *
        ((W * ∏ i, D (p i) (r i)) * (((Ui.map (Int.cast : ℤ → ℚ))).submatrix r b).det) ∈ R0 := by
    intro p r
    refine Subring.mul_mem _ (Subring.prod_mem _ fun i _ => intCast_mem_range _) ?_
    by_cases hr : p = r
    · subst hr
      by_cases hp : Function.Injective p
      · refine Subring.mul_mem _ ?_ (det_mem_subring _ _ fun i j => intCast_mem_range _)
        have : ∏ i, D (p i) (p i) = ∏ j ∈ Finset.univ.image p, D j j := by
          rw [Finset.prod_image (fun a _ b _ h => hp h)]
        rw [this]
        exact W_mul_prod_int s hs _
      · have : (((Ui.map (Int.cast : ℤ → ℚ))).submatrix p b).det = 0 :=
          det_submatrix_rows_eq_zero hp ((Ui.map (Int.cast : ℤ → ℚ)).submatrix id b)
        rw [this, mul_zero]
        exact Subring.zero_mem _
    · have : ∃ i, p i ≠ r i := by
        by_contra hc
        push Not at hc
        exact hr (funext hc)
      obtain ⟨i, hi⟩ := this
      have : ∏ i, D (p i) (r i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (casselsSDiag_apply_ne s hi)
      rw [this, mul_zero, zero_mul]
      exact Subring.zero_mem _
  rw [e1, Finset.mul_sum]
  refine Subring.sum_mem _ fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun r _ => ?_
  have := term p r
  convert this using 1
  ring

theorem inv_W_mem (T : Matrix (Fin n) (Fin n) ℚ) (s : Fin (n / 2) → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ)
    (hs : ∀ i, 0 < s i) (hV : V.det = 1 ∨ V.det = -1)
    (hTUV : T * U.map (Int.cast : ℤ → ℚ) = V.map (Int.cast : ℤ → ℚ) * casselsSDiag s) (L : ℚ)
    (hL : ∀ a b : Fin (n / 2) → Fin n, L * (T.submatrix a b).det ∈ (Int.castRingHom ℚ).range) :
    L * ((∏ i, s i : ℕ) : ℚ)⁻¹ ∈ (Int.castRingHom ℚ).range := by
  classical
  obtain ⟨Vi, hVVi, hViV⟩ := int_inv_of_det V hV
  set R0 := (Int.castRingHom ℚ).range with hR0
  set D := casselsSDiag s with hD
  have hDe : D = (Vi.map (Int.cast : ℤ → ℚ)) * (T * U.map (Int.cast : ℤ → ℚ)) := by
    rw [hTUV, ← Matrix.mul_assoc, ← intCast_map_mul, hViV, intCast_map_one, Matrix.one_mul]
  let e : Fin (n / 2) → Fin n := fun i => ⟨n - 1 - i.1, by have := i.2; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have := congrArg Fin.val hij
    simp only [e] at this
    have := i.2; have := j.2
    exact Fin.ext (by omega)
  have hsub : D.submatrix e e = Matrix.diagonal fun i => D (e i) (e i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact casselsSDiag_apply_ne s (fun h => hij (he h))
  have hdiag : ∀ i, D (e i) (e i) = ((s i : ℕ) : ℚ)⁻¹ := by
    intro i
    rw [hD, casselsSDiag_apply_diag]
    have h1 : ¬ (e i).1 < n / 2 := by have := i.2; simp only [e]; omega
    have h2 : n - n / 2 ≤ (e i).1 := by have := i.2; simp only [e]; omega
    have h3 : sNum s (e i) = 1 := by simp [sNum, h1]
    have h4 : sDen s (e i) = s i := by
      simp only [sDen, dif_pos h2]
      congr 1
      apply Fin.ext
      have := i.2
      simp only [e]
      omega
    rw [h3, h4]
    simp
  have hdet : (D.submatrix e e).det = ((∏ i, s i : ℕ) : ℚ)⁻¹ := by
    rw [hsub, Matrix.det_diagonal]
    simp_rw [hdiag]
    rw [Finset.prod_inv_distrib, Nat.cast_prod]
  rw [← hdet, hDe, submatrix_mul_id, det_mul_rect, Finset.mul_sum]
  refine Subring.sum_mem _ fun p _ => ?_
  have h2 : ((T * U.map (Int.cast : ℤ → ℚ)).submatrix id e).submatrix p id =
      T.submatrix p id * (U.map (Int.cast : ℤ → ℚ)).submatrix id e := by
    rw [← submatrix_mul_id]; rfl
  rw [h2, det_mul_rect', Finset.mul_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun q _ => ?_
  have e3 : (T.submatrix p id).submatrix id q = T.submatrix p q := rfl
  rw [e3]
  have hm : (∏ i, (Vi.map (Int.cast : ℤ → ℚ)).submatrix e id i (p i)) *
      (∏ i, (U.map (Int.cast : ℤ → ℚ)).submatrix id e (q i) i) * (L * (T.submatrix p q).det) ∈ R0 :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.prod_mem _ fun i _ => intCast_mem_range _)
      (Subring.prod_mem _ fun i _ => intCast_mem_range _)) (hL p q)
  convert hm using 1
  ring

theorem den_dvd_of_mul_mem (x : ℚ) (W : ℕ) (hW : W ≠ 0) (h : (W : ℚ) * x ∈ (Int.castRingHom ℚ).range) :
    x.den ∣ W := by
  obtain ⟨z, hz⟩ := h
  have hW0 : (W : ℚ) ≠ 0 := by exact_mod_cast hW
  have hx : x = (z : ℚ) / (W : ℚ) := by
    rw [eq_div_iff hW0]
    simpa [mul_comm] using hz.symm
  have : x = Rat.divInt z (W : ℤ) := by
    rw [Rat.divInt_eq_div, hx]; push_cast; rfl
  have h3 := Rat.den_dvd z (W : ℤ)
  rw [← this] at h3
  exact_mod_cast h3

theorem mul_den_mem (x : ℚ) (L : ℕ) (h : x.den ∣ L) : (L : ℚ) * x ∈ (Int.castRingHom ℚ).range := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨x.num * c, ?_⟩
  have := Rat.mul_den_eq_num x
  simp only [eq_intCast]
  push_cast
  rw [← this]; ring

end Minors

/-! ### Local data of the lattices $\gamma\mathbb Z^n$ -/

section LocalData

theorem valued_intCast_le_one' (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) :
    Valued.v ((z : ℤ) : v.adicCompletion ℚ) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (K := ℚ) (v := v)).1
    (intCast_mem (v.adicCompletionIntegers ℚ) z)

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem valued_intCast_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ)
    (h : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ z) :
    Valued.v ((z : ℤ) : v.adicCompletion ℚ) = 1 := by
  refine le_antisymm (valued_intCast_le_one' v z) ?_
  by_contra hlt
  push Not at hlt
  refine h ?_
  have := (valued_intCast_le_iff v z 1).1 (by simpa using le_exp_neg_one_of_lt_one hlt)
  simpa using this

theorem valued_le_one_of_den (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ)
    (h : ¬ Rat.HeightOneSpectrum.natGenerator v ∣ q.den) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
  have hq : algebraMap ℚ (v.adicCompletion ℚ) q =
      (q.num : v.adicCompletion ℚ) / ((q.den : ℕ) : v.adicCompletion ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q]
    simp
  rw [hq, map_div₀]
  have hd : Valued.v (((q.den : ℕ) : v.adicCompletion ℚ)) = 1 := by
    have := valued_intCast_eq_one v (q.den : ℤ) (by exact_mod_cast h)
    simpa using this
  rw [hd, div_one]
  exact valued_intCast_le_one' v _

/-- The subring of rationals integral at $v$. -/
def locSub (v : HeightOneSpectrum (𝓞 ℚ)) : Subring ℚ :=
  (v.adicCompletionIntegers ℚ).toSubring.comap (algebraMap ℚ (v.adicCompletion ℚ))

theorem mem_locSub {v : HeightOneSpectrum (𝓞 ℚ)} {q : ℚ} :
    q ∈ locSub v ↔ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) ≤ 1 := by
  simp [locSub, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem inv_entries_mem (R1 : Subring ℚ) (T : GL (Fin n) ℚ) (hT : ∀ i j, T.val i j ∈ R1)
    (hdet : T.val.det = 1 ∨ T.val.det = -1) : ∀ i j, (T⁻¹).val i j ∈ R1 := by
  intro i j
  have h1 : (T⁻¹).val = (T.val.det)⁻¹ • T.val.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h1, Matrix.smul_apply, smul_eq_mul]
  refine Subring.mul_mem _ ?_ ?_
  · rcases hdet with h | h
    · rw [h]; simpa using Subring.one_mem R1
    · rw [h]; simpa using Subring.neg_mem _ (Subring.one_mem R1)
  · rw [Matrix.adjugate_apply]
    refine det_mem_subring R1 _ fun k l => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · exact hT _ _

theorem subst_mulVec_mem_std {v : HeightOneSpectrum (𝓞 ℚ)} {k : ℕ}
    (M : Matrix (Fin k) (Fin k) (v.adicCompletion ℚ)) (hM : ∀ i j, Valued.v (M i j) ≤ 1)
    {y : Fin k → v.adicCompletion ℚ} (hy : y ∈ std v) : M *ᵥ y ∈ std v := by
  rw [mem_std_iff] at hy ⊢
  intro i
  rw [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i j) (hy j)

theorem glMap_val (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin n) ℚ) :
    (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) g).val =
      g.val.map (algebraMap ℚ (v.adicCompletion ℚ)) := rfl

/-- If $T$ and $T^{-1}$ are $p$-integral then $T\mathbb Z^n$ and $\mathbb Z^n$ have the same localization at $p$. -/
theorem loc_latOf_eq_std (v : HeightOneSpectrum (𝓞 ℚ)) (T : GL (Fin n) ℚ)
    (hT : ∀ i j, T.val i j ∈ locSub v) (hdet : T.val.det = 1 ∨ T.val.det = -1) :
    loc v (latOf T) = std v := by
  have hinv := inv_entries_mem (locSub v) T hT hdet
  rw [latOf, loc_glImage, loc_intVec]
  ext x
  rw [mem_locAct]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact subst_mulVec_mem_std _ (fun i j => by
      rw [glMap_val, Matrix.map_apply]; exact mem_locSub.1 (hT i j)) hy
  · intro hx
    refine ⟨(GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) T)⁻¹.val *ᵥ x,
      subst_mulVec_mem_std _ ?_ hx, mulVec_inv_mulVec _ _⟩
    intro i j
    rw [← map_inv, glMap_val, Matrix.map_apply]
    exact mem_locSub.1 (hinv i j)

theorem locGram_map_eq (f F : QuadForm ℤ n) (γ : GL (Fin n) ℚ) (hF : FormOf f γ F)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    locGram (f.map (Int.castRingHom ℚ)) v
        (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) γ) =
      F.hessian.map (Int.castRingHom (v.adicCompletion ℚ)) := by
  have hH := Siegel.Kneser.hessian_eq_conj hF
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℤ, (M.map (algebraMap ℤ ℚ)).map (algebraMap ℚ (v.adicCompletion ℚ)) =
      M.map (Int.castRingHom (v.adicCompletion ℚ)) := fun M => by
    ext i j; simp
  calc _ = (γ.val ᵀ * f.hessian.map (algebraMap ℤ ℚ) * γ.val).map (algebraMap ℚ (v.adicCompletion ℚ)) := by
        unfold locGram
        rw [glMap_val, Siegel.Kneser.hessian_map, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
        simp only [algebraMap_int_eq, Matrix.map_map]
    _ = (F.hessian.map (algebraMap ℤ ℚ)).map (algebraMap ℚ (v.adicCompletion ℚ)) := by rw [hH]
    _ = _ := hc _

/-- Local data of $\gamma\mathbb Z^n$ at an odd prime $v$ not dividing the determinant of the form $F$
in the basis $\gamma$. -/
theorem locData (f F : QuadForm ℤ n) (γ : GL (Fin n) ℚ) (hF : FormOf f γ F)
    (hFc : IsClassicallyIntegral F) (v : HeightOneSpectrum (𝓞 ℚ)) (hodd : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (hH : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ F.hessian.det) :
    (∀ x ∈ loc v (latOf γ), ∀ y ∈ loc v (latOf γ),
      Valued.v (qbil (f.map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) ∧
    (∀ x ∈ loc v (latOf γ), Valued.v ((f.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
    (∃ γ' : GL (Fin n) (v.adicCompletion ℚ), loc v (latOf γ) = locAct v γ' (std v) ∧
      Valued.v (locGram (f.map (Int.castRingHom ℚ)) v γ').det = 1) := by
  have hGram := locGram_map_eq f F γ hF v
  have hdet : Valued.v (F.hessian.det : v.adicCompletion ℚ) = 1 := valued_intCast_eq_one v _ hH
  have hlocγ : loc v (latOf γ) = locAct v (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) γ) (std v) := by
    rw [latOf, loc_glImage, loc_intVec]
  refine ⟨(latCI_iff_loc _ _).1 (latCI_latOf f hF hFc) v, ?_, ⟨_, hlocγ, ?_⟩⟩
  · intro x hx
    rw [hlocγ, mem_locAct] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h2 := two_mul_evalIn_locGram (Q := f.map (Int.castRingHom ℚ)) (v := v)
      (GeneralLinearGroup.map (algebraMap ℚ (v.adicCompletion ℚ)) γ) y
    rw [hGram] at h2
    have h3 : Valued.v (y ⬝ᵥ (F.hessian.map (Int.castRingHom (v.adicCompletion ℚ)) *ᵥ y)) ≤ 1 := by
      rw [dotProduct]
      have hmem := subst_mulVec_mem_std (F.hessian.map (Int.castRingHom (v.adicCompletion ℚ)))
        (fun i j => valued_intCast_le_one' v _) hy
      rw [mem_std_iff] at hy hmem
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul]
      exact mul_le_one' (hy j) (hmem j)
    rw [← h2, map_mul, valued_two hodd, one_mul] at h3
    exact h3
  · rw [hGram, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet

theorem exists_int_of_latOf_eq {γ δ : GL (Fin n) ℚ} (h : latOf γ = latOf δ) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, (U.det = 1 ∨ U.det = -1) ∧
      U.map (Int.castRingHom ℚ) = (δ⁻¹ * γ).val := by
  have hP : glImage (δ⁻¹ * γ) intVec = intVec := by
    rw [glImage_mul]
    change glImage δ⁻¹ (latOf γ) = intVec
    rw [h, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
  obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
  have e : (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ) = (δ⁻¹ * γ).val :=
    congrArg Units.val hP₀
  set U : Matrix (Fin n) (Fin n) ℤ := (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map Rat.ringOfIntegersEquiv
  have hU : U.map (Int.castRingHom ℚ) = (δ⁻¹ * γ).val := by
    rw [← e]
    ext i j
    simp [U, Rat.ringOfIntegersEquiv_apply_coe]
  have hunit : IsUnit U.det := by
    have : IsUnit (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det := P₀.isUnit.map Matrix.detMonoidHom
    have h2 := this.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    have h3 : U.det = (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det :=
      (RingHom.map_det (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) _).symm
    rwa [h3]
  exact ⟨U, Int.isUnit_iff.mp hunit, hU⟩

end LocalData

/-- **Cassels, Theorem 6.3** (Ch. 11, p. 226): *let $f_1, f_2$ be classically integral forms in $n \ge 2$ variables
and of determinant $d \ne 0$. Let $y = Tx$ be a transformation such that identically $f_2(y) = f_1(x)$. Suppose
further that $t_{ij} \in \mathbb Z_p$ (all $p \mid 2d$) and $\det(t_{ij}) = \pm1$. Then there are positive integers
$s_1, \dots, s_m$, $m = [n/2]$, and transformations $x = UX$, $y = VY$ with $U, V$ integral of determinant $\pm1$ such
that $Y_i = s_iX_i$, $X_{n+1-i} = s_iY_{n+1-i}$ ($1 \le i \le m$) and $X_{m+1} = Y_{m+1}$ ($n$ odd). We can suppose,
further, that $s_{i+1} \mid s_i$.* 0-based, reconstructed (module docstring). -/
@[kb "cassels1978" "Ch. 11, Thm. 6.3, p. 226 ((6.7)–(6.11) reconstructed; 0-based)"]
theorem exists_special_bases_of_subst (hn : 2 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (T : Matrix (Fin n) (Fin n) ℚ)
    (hT : ∀ x : Fin n → ℚ, (f₁.map (Int.castRingHom ℚ)).evalIn ℚ x = (f₂.map (Int.castRingHom ℚ)).evalIn ℚ (T *ᵥ x))
    (hTp : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * f₁.hessian.det → ∀ i j, ¬ p ∣ (T i j).den)
    (hTdet : T.det = 1 ∨ T.det = -1) :
    ∃ (s : Fin (n / 2) → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ),
      (∀ i, 0 < s i) ∧ (∀ i : Fin (n / 2), ∀ h : i.1 + 1 < n / 2, s ⟨i.1 + 1, h⟩ ∣ s i) ∧
      (U.det = 1 ∨ U.det = -1) ∧ (V.det = 1 ∨ V.det = -1) ∧
      T * U.map (Int.cast : ℤ → ℚ) = V.map (Int.cast : ℤ → ℚ) * casselsSDiag s := by
  classical
  have hn0 : 0 < n := by omega
  have hTne : T.det ≠ 0 := by rcases hTdet with h | h <;> simp [h]
  set Tg : GL (Fin n) ℚ := Matrix.GeneralLinearGroup.mkOfDetNeZero T hTne with hTg
  have hTgv : (Tg : Matrix (Fin n) (Fin n) ℚ) = T := rfl
  set Q := f₂.map (Int.castRingHom ℚ) with hQ
  set Λ : Lat ℚ n := ⟨latOf 1, latOf_isLattice 1⟩ with hΛ
  set Γ : Lat ℚ n := ⟨latOf Tg, latOf_isLattice Tg⟩ with hΓ
  have hFT : FormOf f₂ Tg f₁ := fun x =>
    (map_evalIn_rat f₁ x).symm.trans ((hT x).trans (map_evalIn_rat f₂ _))
  have hF1 : FormOf f₂ 1 f₂ := fun x => by simp
  have hΛi : Tamagawa.SiegelSpace.latIndex Λ = 1 := by
    have := latIndex_latOf (1 : GL (Fin n) ℚ)
    simpa using this
  have hΓi : Tamagawa.SiegelSpace.latIndex Γ = 1 := by
    have := latIndex_latOf Tg
    rw [hTgv] at this
    rcases hTdet with h | h <;> simpa [h] using this
  have hidx : Tamagawa.SiegelSpace.latIndex Λ = Tamagawa.SiegelSpace.latIndex Γ := hΛi.trans hΓi.symm
  have hlocT : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ 2 * f₁.hessian.det → loc v Γ.1 = loc v Λ.1 := by
    intro v hv
    have hp := Rat.HeightOneSpectrum.prime_natGenerator v
    have hT' : ∀ i j, Tg.val i j ∈ locSub v := fun i j =>
      mem_locSub.2 (valued_le_one_of_den v _ (hTp _ hp hv i j))
    show loc v (latOf Tg) = loc v (latOf 1)
    rw [loc_latOf_eq_std v Tg hT' (by rw [hTgv]; exact hTdet), latOf, glImage_one, loc_intVec]
  have hloc : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Λ Γ →
      (∀ x ∈ loc v Λ.1, ∀ y ∈ loc v Λ.1,
        Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) ∧
      (∀ x ∈ loc v Γ.1, ∀ y ∈ loc v Γ.1,
        Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ)) ∧
      (∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v Λ.1 = locAct v γ (std v) ∧
        Valued.v (locGram Q v γ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n) ∧
      (∃ δ : GL (Fin n) (v.adicCompletion ℚ), loc v Γ.1 = locAct v δ (std v) ∧
        Valued.v (locGram Q v δ).det = Valued.v (2 : v.adicCompletion ℚ) ^ n) := by
    intro v hv
    have hnd : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ 2 * f₁.hessian.det := fun hc =>
      (loc_eq_iff_not_dvd_casselsI hidx v).1 (hlocT v hc).symm hv
    have hodd : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h2 => hnd (by
      rw [(two_mem_iff_natGenerator v).1 h2]; exact dvd_mul_right _ _)
    have hH1 : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ f₁.hessian.det :=
      fun h => hnd (Dvd.dvd.mul_left h _)
    have hH2 : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ f₂.hessian.det := by
      rw [← hd]; exact hH1
    obtain ⟨a1, a2, a3⟩ := locData f₂ f₂ 1 hF1 h₂ v hodd hH2
    obtain ⟨c1, c2, c3⟩ := locData f₂ f₁ Tg hFT h₁ v hodd hH1
    have v2 : Valued.v (2 : v.adicCompletion ℚ) ^ n = 1 := by rw [valued_two hodd, one_pow]
    refine ⟨a1, c1, ?_, ?_⟩
    · obtain ⟨γ, h1, h2⟩ := a3
      exact ⟨γ, h1, by rw [v2]; exact h2⟩
    · obtain ⟨γ, h1, h2⟩ := c3
      exact ⟨γ, h1, by rw [v2]; exact h2⟩
  obtain ⟨b, s, hb, hΛb, hΓb, hpos, hchain, hrev, hint⟩ := exists_basis_casselsForm Q hidx hloc
  have hb' : LinearIndependent ℚ (fun j => s j • b j) := linIndep_of_lat hΓb
  have hΛl : latOf (basisGL hb) = latOf 1 := (lat_eq_latOf hΛb).symm
  have hΓl : latOf (basisGL hb') = latOf Tg := (lat_eq_latOf hΓb).symm
  obtain ⟨V, hVdet, hVmap⟩ := exists_int_of_latOf_eq hΛl
  obtain ⟨U, hUdet, hUmap⟩ := exists_int_of_latOf_eq hΓl
  have hVm : V.map (Int.cast : ℤ → ℚ) = (basisGL hb).val := by
    rw [show V.map (Int.cast : ℤ → ℚ) = V.map (Int.castRingHom ℚ) from rfl, hVmap, inv_one, one_mul]
  have hTU : T * U.map (Int.cast : ℤ → ℚ) = (basisGL hb').val := by
    rw [show U.map (Int.cast : ℤ → ℚ) = U.map (Int.castRingHom ℚ) from rfl, hUmap, Units.val_mul,
      ← Matrix.mul_assoc, ← hTgv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hbd : (basisGL hb').val = (basisGL hb).val * Matrix.diagonal s := by
    ext i j
    simp [basisGL_val, Matrix.mul_diagonal, mul_comm]
  let e : Fin (n / 2) → Fin n := fun i => ⟨i.1, by have := i.2; omega⟩
  have hsint : ∀ i : Fin (n / 2), ∃ z : ℕ, (z : ℚ) = s (e i) := by
    intro i
    obtain ⟨z, hz⟩ := hint (e i) (by show i.1 < (n + 1) / 2; have := i.2; omega)
    have hp := hpos (e i)
    rw [hz] at hp
    have hz0 : 0 ≤ z := by exact_mod_cast hp.le
    exact ⟨z.toNat, by rw [hz]; exact_mod_cast Int.toNat_of_nonneg hz0⟩
  choose s' hs' using hsint
  have hdiag : Matrix.diagonal s = casselsSDiag s' := by
    unfold casselsSDiag
    congr 1
    funext j
    by_cases h1 : j.1 < n / 2
    · rw [dif_pos h1, hs']
    · rw [dif_neg h1]
      by_cases h2 : n - n / 2 ≤ j.1
      · rw [dif_pos h2, hs']
        have hr : e ⟨n - 1 - j.1, by have := j.2; omega⟩ = Fin.rev j := by
          apply Fin.ext
          simp only [e, Fin.val_rev]
          omega
        rw [hr]
        have := hrev j
        have hne : s (Fin.rev j) ≠ 0 := (hpos _).ne'
        field_simp
        linarith
      · rw [dif_neg h2]
        have hr : Fin.rev j = j := by
          apply Fin.ext
          simp only [Fin.val_rev]
          omega
        have h3 := hrev j
        rw [hr] at h3
        have h4 := hpos j
        nlinarith
  refine ⟨s', U, V, fun i => ?_, fun i h => ?_, hUdet, hVdet, ?_⟩
  · have := hpos (e i)
    rw [← hs' i] at this
    exact_mod_cast this
  · have hj : (e i).1 + 1 < n := by have := i.2; show i.1 + 1 < n; omega
    obtain ⟨z, hz⟩ := hchain (e i) hj
    have e2 : (⟨(e i).1 + 1, hj⟩ : Fin n) = e ⟨i.1 + 1, h⟩ := rfl
    rw [e2, ← hs', ← hs'] at hz
    have hne : ((s' ⟨i.1 + 1, h⟩ : ℕ) : ℚ) ≠ 0 := by
      have := hpos (e ⟨i.1 + 1, h⟩)
      rw [← hs'] at this
      exact this.ne'
    have h5 : ((s' i : ℕ) : ℚ) = z * (s' ⟨i.1 + 1, h⟩ : ℕ) := by
      field_simp at hz
      linarith
    have h6 : ((s' i : ℕ) : ℤ) = z * ((s' ⟨i.1 + 1, h⟩ : ℕ) : ℤ) := by exact_mod_cast h5
    exact Int.natCast_dvd_natCast.1 ⟨z, by rw [h6]; ring⟩
  · rw [← hdiag, hTU, hbd, hVm]

theorem casselsSDiag_eq_diagonal (s : Fin (n / 2) → ℕ) :
    casselsSDiag s = Matrix.diagonal fun j => (sNum s j : ℚ) / (sDen s j : ℚ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; rw [Matrix.diagonal_apply_eq]; exact casselsSDiag_apply_diag s i
  · rw [Matrix.diagonal_apply_ne _ hij]; exact casselsSDiag_apply_ne s hij

/-- The index $I(T^{-1}\mathbb Z^n, \mathbb Z^n) = s_1\cdots s_m$ when $TU = V\,\mathrm{diag}(s)$. -/
theorem casselsI_latOf_inv_subst (T : GL (Fin n) ℚ) (s : Fin (n / 2) → ℕ) (hs : ∀ i, 0 < s i)
    (U V : Matrix (Fin n) (Fin n) ℤ) (hU : U.det = 1 ∨ U.det = -1) (hV : V.det = 1 ∨ V.det = -1)
    (hTUV : (T : Matrix (Fin n) (Fin n) ℚ) * U.map (Int.cast : ℤ → ℚ) =
      V.map (Int.cast : ℤ → ℚ) * casselsSDiag s) :
    casselsI (⟨latOf T⁻¹, latOf_isLattice _⟩ : Lat ℚ n) stdLat = ∏ i, s i := by
  classical
  obtain ⟨Ui, hUUi, hUiU⟩ := int_inv_of_det U hU
  obtain ⟨Vi, hVVi, hViV⟩ := int_inv_of_det V hV
  set X : GL (Fin n) ℚ := T⁻¹ with hX
  set D := casselsSDiag s with hD
  have hDdiag : D = Matrix.diagonal fun j => (sNum s j : ℚ) / (sDen s j : ℚ) :=
    casselsSDiag_eq_diagonal s
  let e : Fin (n / 2) → Fin n := fun i => ⟨i.1, by have := i.2; omega⟩
  have hnum : ∀ i, sNum s (e i) = s i := by
    intro i
    have : (e i).1 < n / 2 := i.2
    simp only [sNum, dif_pos this]
    rfl
  have hden : ∀ i, sDen s (e i) = 1 := by
    intro i
    have h1 : ¬ n - n / 2 ≤ (e i).1 := by have := i.2; show ¬ n - n / 2 ≤ i.1; omega
    simp only [sDen, dif_neg h1]
  have hcv : ∀ (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ),
      A.map (Int.cast : ℤ → ℚ) *ᵥ Siegel.Kneser.cv x = Siegel.Kneser.cv (A *ᵥ x) := cast_mulVec_cv
  have hXT : X.val * T.val = 1 := by rw [hX, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hXTv : ∀ x : Fin n → ℚ, X.val *ᵥ (T.val *ᵥ x) = x := by
    intro x; rw [mulVec_mulVec, hXT, one_mulVec]
  have hTXv : ∀ x : Fin n → ℚ, T.val *ᵥ (X.val *ᵥ x) = x := fun x => mulVec_inv_mulVec T x
  have hT' : T.val = V.map (Int.cast : ℤ → ℚ) * (D * Ui.map (Int.cast : ℤ → ℚ)) := by
    rw [← Matrix.mul_assoc, ← hTUV, Matrix.mul_assoc, ← intCast_map_mul, hUUi, intCast_map_one,
      Matrix.mul_one]
  have hVD : Vi.map (Int.cast : ℤ → ℚ) * T.val = D * Ui.map (Int.cast : ℤ → ℚ) := by
    rw [hT', ← Matrix.mul_assoc, ← intCast_map_mul, hViV, intCast_map_one, Matrix.one_mul]
  have key : ∀ z : Fin n → ℤ, X.val *ᵥ Siegel.Kneser.cv z ∈ (stdLat : Lat ℚ n).1 ↔
      ∀ i : Fin (n / 2), (s i : ℤ) ∣ (Vi *ᵥ z) (e i) := by
    intro z
    show X.val *ᵥ Siegel.Kneser.cv z ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ _
    rw [mem_intVec_Q]
    constructor
    · rintro ⟨w, hw⟩ i
      have h1 : Siegel.Kneser.cv z = T.val *ᵥ Siegel.Kneser.cv w := by rw [← hw, hTXv]
      have h2 : Siegel.Kneser.cv (Vi *ᵥ z) = D *ᵥ Siegel.Kneser.cv (Ui *ᵥ w) := by
        rw [← hcv Vi z, h1, mulVec_mulVec, hVD, ← mulVec_mulVec, hcv]
      have h3 := congrFun h2 (e i)
      rw [hDdiag, mulVec_diagonal, hnum, hden] at h3
      simp only [Siegel.Kneser.cv_apply, Nat.cast_one, div_one] at h3
      exact ⟨(Ui *ᵥ w) (e i), by exact_mod_cast h3⟩
    · intro hdvd
      have hdvd' : ∀ j, ∃ c : ℤ, (Vi *ᵥ z) j = (sNum s j : ℤ) * c := by
        intro j
        by_cases hj : j.1 < n / 2
        · have := hdvd ⟨j.1, hj⟩
          have e1 : e ⟨j.1, hj⟩ = j := Fin.ext rfl
          rw [e1] at this
          have e2 : sNum s j = s ⟨j.1, hj⟩ := by simp only [sNum, dif_pos hj]
          rw [e2]
          exact this
        · exact ⟨(Vi *ᵥ z) j, by simp [sNum, hj]⟩
      choose c hc using hdvd'
      let u : Fin n → ℤ := fun j => c j * (sDen s j : ℤ)
      have hDu : Siegel.Kneser.cv (Vi *ᵥ z) = D *ᵥ Siegel.Kneser.cv u := by
        funext j
        rw [hDdiag, mulVec_diagonal]
        have hn0 : (sNum s j : ℚ) ≠ 0 := by
          have : 0 < sNum s j := by
            unfold sNum; split_ifs
            · exact hs _
            · exact one_pos
          exact_mod_cast this.ne'
        have hd0 : (sDen s j : ℚ) ≠ 0 := by
          have : 0 < sDen s j := by
            unfold sDen; split_ifs
            · exact hs _
            · exact one_pos
          exact_mod_cast this.ne'
        simp only [Siegel.Kneser.cv_apply, u]
        rw [hc j]
        push_cast
        field_simp
      refine ⟨U *ᵥ u, ?_⟩
      have h1 : Siegel.Kneser.cv z = T.val *ᵥ Siegel.Kneser.cv (U *ᵥ u) := by
        calc Siegel.Kneser.cv z = Siegel.Kneser.cv (V *ᵥ (Vi *ᵥ z)) := by
              rw [mulVec_mulVec, hVVi, one_mulVec]
          _ = V.map (Int.cast : ℤ → ℚ) *ᵥ Siegel.Kneser.cv (Vi *ᵥ z) := (hcv V _).symm
          _ = V.map (Int.cast : ℤ → ℚ) *ᵥ (D *ᵥ Siegel.Kneser.cv u) := by rw [hDu]
          _ = (V.map (Int.cast : ℤ → ℚ) * D) *ᵥ Siegel.Kneser.cv u := mulVec_mulVec _ _ _
          _ = (T.val * U.map (Int.cast : ℤ → ℚ)) *ᵥ Siegel.Kneser.cv u := by rw [hTUV]
          _ = T.val *ᵥ (U.map (Int.cast : ℤ → ℚ) *ᵥ Siegel.Kneser.cv u) := (mulVec_mulVec _ _ _).symm
          _ = T.val *ᵥ Siegel.Kneser.cv (U *ᵥ u) := by rw [hcv]
      rw [h1, hXTv]
  -- the index
  let Φ : (Fin n → ℤ) →+ (Fin n → ℚ) :=
    AddMonoidHom.mk' (fun z => X.val *ᵥ Siegel.Kneser.cv z)
      (fun a b => by rw [Siegel.Kneser.cv_add, mulVec_add])
  have hXinj : Function.Injective fun y : Fin n → ℚ => X.val *ᵥ y :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit X)
  have hΦinj : Function.Injective Φ := fun a b h => Siegel.Kneser.cv_injective (hXinj h)
  have hrange : Φ.range = (latOf X).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_range]
    show (∃ z, X.val *ᵥ Siegel.Kneser.cv z = x) ↔ x ∈ latOf X
    rw [mem_latOf_Q]
    constructor <;> rintro ⟨z, hz⟩ <;> exact ⟨z, hz.symm⟩
  have hH : ∀ z, z ∈ ((latOf X ⊓ (stdLat : Lat ℚ n).1).toAddSubgroup.comap Φ) ↔
      ∀ i : Fin (n / 2), (s i : ℤ) ∣ (Vi *ᵥ z) (e i) := by
    intro z
    rw [AddSubgroup.mem_comap]
    show X.val *ᵥ Siegel.Kneser.cv z ∈ latOf X ⊓ (stdLat : Lat ℚ n).1 ↔ _
    rw [Submodule.mem_inf, ← key]
    exact ⟨fun h => h.2, fun h => ⟨(mem_latOf_Q X _).mpr ⟨z, rfl⟩, h⟩⟩
  unfold casselsI
  show ((latOf X ⊓ (stdLat : Lat ℚ n).1).toAddSubgroup).relIndex (latOf X).toAddSubgroup = ∏ i, s i
  have hK : (latOf X ⊓ (stdLat : Lat ℚ n).1).toAddSubgroup =
      ((latOf X ⊓ (stdLat : Lat ℚ n).1).toAddSubgroup.comap Φ).map Φ := by
    rw [AddSubgroup.map_comap_eq, hrange]
    exact (inf_of_le_right (fun x hx => hx.1)).symm
  have hL : (latOf X).toAddSubgroup = (⊤ : AddSubgroup (Fin n → ℤ)).map Φ := by
    rw [← AddMonoidHom.range_eq_map, hrange]
  rw [hL, hK, AddSubgroup.relIndex_map_map_of_injective _ _ hΦinj, AddSubgroup.relIndex_top_right]
  let f : (Fin n → ℤ) →+ ((i : Fin (n / 2)) → ZMod (s i)) :=
    AddMonoidHom.mk' (fun z i => (((Vi *ᵥ z) (e i) : ℤ) : ZMod (s i)))
      (fun a b => by funext i; simp [Matrix.mulVec_add])
  have hker : ((latOf X ⊓ (stdLat : Lat ℚ n).1).toAddSubgroup.comap Φ) = f.ker := by
    ext z
    rw [hH, AddMonoidHom.mem_ker]
    show _ ↔ (fun i => (((Vi *ᵥ z) (e i) : ℤ) : ZMod (s i))) = 0
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    rw [Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective f := by
    intro c
    haveI : ∀ i, NeZero (s i) := fun i => ⟨(hs i).ne'⟩
    let u : Fin n → ℤ := fun j => if h : j.1 < n / 2 then (((c ⟨j.1, h⟩).val : ℕ) : ℤ) else 0
    refine ⟨V *ᵥ u, ?_⟩
    funext i
    show (((Vi *ᵥ (V *ᵥ u)) (e i) : ℤ) : ZMod (s i)) = c i
    rw [mulVec_mulVec, hViV, one_mulVec]
    have hi : (e i).1 < n / 2 := i.2
    simp only [u, dif_pos hi]
    have : (⟨(e i).1, hi⟩ : Fin (n / 2)) = i := Fin.ext rfl
    rw [this]
    simp
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top]
  simp [Nat.card_pi, Nat.card_zmod]

/-- **Cassels, Theorem 6.3**, last part (Ch. 11, p. 227, (6.12)–(6.13)): *finally, if $n \ge 3$, the spinor genera
$\mathcal S_1, \mathcal S_2$ of $f_1, f_2$ satisfy $\mathcal S_2 = g_W\mathcal S_1$, where $W = s_1 \cdots s_m$*
(in the notation of Theorems 3.1 and 4.1). Unfolded as in Theorem 4.1: in $V = (\mathbb Q^n, f_1)$ with
$\Lambda = \mathbb Z^n$, the lattice of $f_2$ is $\Gamma = T^{-1}\mathbb Z^n$ (for $\det T = 1$; for $\det T = -1$ its
proper class is that of the image under an improper automorph), and $\Gamma$ is in the spinor genus of $\alpha\Lambda$
whenever $\theta(\alpha_p) = W$ at $p \in P$ ($P$ = Cassels' $P^*$ for $\Lambda$). Here stated for $\det T = 1$ with
$W = s_1\cdots s_m$ for the $s$ of Theorem 6.3. -/
@[kb "cassels1978" "Ch. 11, Thm. 6.3, (6.12)–(6.13), p. 227 (det T = 1; g_W𝒮 unfolded)"]
theorem sameProperSpinorGenus_of_subst (hn : 3 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (T : GL (Fin n) ℚ)
    (hT : ∀ x : Fin n → ℚ, (f₁.map (Int.castRingHom ℚ)).evalIn ℚ x =
      (f₂.map (Int.castRingHom ℚ)).evalIn ℚ ((T : Matrix (Fin n) (Fin n) ℚ) *ᵥ x))
    (hTp : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * f₁.hessian.det → ∀ i j, ¬ p ∣ ((T : Matrix (Fin n) (Fin n) ℚ) i j).den)
    (hTdet : (T : Matrix (Fin n) (Fin n) ℚ).det = 1)
    (s : Fin (n / 2) → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ) (hs : ∀ i, 0 < s i)
    (hU : U.det = 1 ∨ U.det = -1) (hV : V.det = 1 ∨ V.det = -1)
    (hTUV : (T : Matrix (Fin n) (Fin n) ℚ) * U.map (Int.cast : ℤ → ℚ) = V.map (Int.cast : ℤ → ℚ) * casselsSDiag s)
    (P : Finset (HeightOneSpectrum (𝓞 ℚ))) (hP2 : ∀ v, (2 : 𝓞 ℚ) ∈ v.asIdeal → v ∈ P)
    (hPunim : ∀ v, v ∉ P →
      (∀ x ∈ loc v (stdLat : Lat ℚ n).1,
        Valued.v ((f₁.map (Int.castRingHom ℚ)).evalIn (v.adicCompletion ℚ) x) ≤ 1) ∧
      ∃ γ : GL (Fin n) (v.adicCompletion ℚ), loc v (stdLat : Lat ℚ n).1 = locAct v γ (std v) ∧
        Valued.v (locGram (f₁.map (Int.castRingHom ℚ)) v γ).det = 1)
    (hPd : ∀ v ∈ P, (Rat.HeightOneSpectrum.natGenerator v : ℤ) ∣ 2 * f₁.hessian.det)
    (α : OAf (f₁.map (Int.castRingHom ℚ)))
    (hα : ∀ v ∈ P, α v ∈ Tamagawa.soSub (f₁.map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) ∧
      spinorNorm (f₁.map (Int.castRingHom ℚ)) (v.adicCompletion ℚ) (α v) =
        sqClassOf (((∏ i, s i : ℕ) : ℚ) : v.adicCompletion ℚ))
    (hα1 : ∀ v, v ∉ P → α v = 1) :
    SameProperSpinorGenus (f₁.map (Int.castRingHom ℚ)) ⟨latOf T⁻¹, latOf_isLattice T⁻¹⟩
      (latSMul (f₁.map (Int.castRingHom ℚ)) α stdLat) := by
  classical
  have hn2 : 2 ≤ n := by omega
  revert α
  set Q := f₁.map (Int.castRingHom ℚ) with hQdef
  intro α hα hα1
  have hQ : Q.Nondegenerate := nondegenerate_map_of_det_ne_zero f₁ hd0
  have hTi : (T⁻¹ : GL (Fin n) ℚ).val.det = 1 := by
    have := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel T))
    rw [Units.val_mul, det_mul, hTdet, Units.val_one, det_one, one_mul] at this
    exact this
  have hFinv : FormOf f₁ T⁻¹ f₂ := fun x => by
    have := hT ((T⁻¹ : GL (Fin n) ℚ).val *ᵥ x)
    rw [mulVec_inv_mulVec] at this
    rw [hQdef] at this
    exact (map_evalIn_rat f₂ x).symm.trans (this.symm.trans (map_evalIn_rat f₁ _))
  have hF1 : FormOf f₁ 1 f₁ := fun x => by simp
  have e1 : latOf (1 : GL (Fin n) ℚ) = (stdLat : Lat ℚ n).1 := by rw [latOf, glImage_one]; rfl
  have hlocInv : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ 2 * f₁.hessian.det →
      loc v (latOf T⁻¹) = std v := by
    intro v hv
    have hp := Rat.HeightOneSpectrum.prime_natGenerator v
    have hT' : ∀ i j, (T : GL (Fin n) ℚ).val i j ∈ locSub v := fun i j =>
      mem_locSub.2 (valued_le_one_of_den v _ (hTp _ hp hv i j))
    exact loc_latOf_eq_std v T⁻¹ (inv_entries_mem (locSub v) T hT' (Or.inl hTdet)) (Or.inl hTi)
  set Γ : Lat ℚ n := ⟨latOf T⁻¹, latOf_isLattice T⁻¹⟩ with hΓ
  have hidx : Tamagawa.SiegelSpace.latIndex Γ = Tamagawa.SiegelSpace.latIndex (stdLat : Lat ℚ n) := by
    have h1 := latIndex_latOf T⁻¹
    have h2 := latIndex_latOf (1 : GL (Fin n) ℚ)
    have e : (⟨latOf (1 : GL (Fin n) ℚ), latOf_isLattice 1⟩ : Lat ℚ n) = stdLat := Subtype.ext e1
    rw [e] at h2
    rw [h2, show Tamagawa.SiegelSpace.latIndex Γ = _ from h1, hTi]
    simp
  have hSG : SameGenus Q (stdLat : Lat ℚ n).1 Γ.1 := by
    refine sameGenus_of_unimodular_of_loc_ne Q stdLat Γ fun v hv => ?_
    have hnd : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ 2 * f₁.hessian.det := fun hc =>
      hv (by
        show loc v (stdLat : Lat ℚ n).1 = loc v (latOf T⁻¹)
        rw [hlocInv v hc]; exact loc_intVec v)
    have hodd : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun h2 => hnd (by
      rw [(two_mem_iff_natGenerator v).1 h2]; exact dvd_mul_right _ _)
    have hH1 : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ f₁.hessian.det :=
      fun h => hnd (Dvd.dvd.mul_left h _)
    have hH2 : ¬ ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∣ f₂.hessian.det := by
      rw [← hd]; exact hH1
    obtain ⟨a1, a2, a3⟩ := locData f₁ f₁ 1 hF1 h₁ v hodd hH1
    obtain ⟨c1, c2, c3⟩ := locData f₁ f₂ T⁻¹ hFinv h₂ v hodd hH2
    rw [e1] at a2 a3
    exact ⟨hodd, a2, c2, a3, c3⟩
  have hIc : casselsI Γ (stdLat : Lat ℚ n) = ∏ i, s i :=
    casselsI_latOf_inv_subst T s hs U V hU hV hTUV
  have hI : ∀ v ∈ P, ¬ Rat.HeightOneSpectrum.natGenerator v ∣ casselsI Γ (stdLat : Lat ℚ n) := by
    intro v hv
    refine (loc_eq_iff_not_dvd_casselsI hidx v).1 ?_
    show loc v (latOf T⁻¹) = loc v (stdLat : Lat ℚ n).1
    rw [hlocInv v (hPd v hv)]; exact (loc_intVec v).symm
  exact sameProperSpinorGenus_latSMul_of_casselsI Q hQ hn stdLat P hP2 hPunim (Γ := Γ)
    (Δ := stdLat) hSG (SameGenus.refl Q _) hI α (fun v hv => by rw [hIc]; exact hα v hv) hα1

/-- **Cassels, Theorem 6.3, Corollary** (Ch. 11, p. 227): *$W$ is the least common multiple of the denominators of the
$m \times m$ minors of the matrix $(t_{ij})$, where $m = [n/2]$* (for any $s, U, V$ as in Theorem 6.3; proof:
Binet–Cauchy). -/
@[kb "cassels1978" "Ch. 11, Thm. 6.3, Cor., p. 227"]
theorem casselsW_eq_lcm_minors (T : Matrix (Fin n) (Fin n) ℚ)
    (s : Fin (n / 2) → ℕ) (U V : Matrix (Fin n) (Fin n) ℤ) (hs : ∀ i, 0 < s i)
    (hsd : ∀ i : Fin (n / 2), ∀ h : i.1 + 1 < n / 2, s ⟨i.1 + 1, h⟩ ∣ s i)
    (hU : U.det = 1 ∨ U.det = -1) (hV : V.det = 1 ∨ V.det = -1)
    (hTUV : T * U.map (Int.cast : ℤ → ℚ) = V.map (Int.cast : ℤ → ℚ) * casselsSDiag s) :
    (∏ i, s i : ℕ) = ((Finset.univ : Finset (Fin (n / 2) ↪ Fin n)) ×ˢ (Finset.univ : Finset (Fin (n / 2) ↪ Fin n))).lcm
      (fun e => ((T.submatrix e.1 e.2).det).den) := by
  classical
  have hW : (∏ i, s i : ℕ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (hs i).ne'
  apply Nat.dvd_antisymm
  · set L := ((Finset.univ : Finset (Fin (n / 2) ↪ Fin n)) ×ˢ (Finset.univ : Finset (Fin (n / 2) ↪ Fin n))).lcm
      (fun e => ((T.submatrix e.1 e.2).det).den) with hLdef
    have hL : ∀ a b : Fin (n / 2) → Fin n,
        (L : ℚ) * (T.submatrix a b).det ∈ (Int.castRingHom ℚ).range := by
      intro a b
      by_cases ha : Function.Injective a
      · by_cases hb : Function.Injective b
        · have hmem : ((⟨a, ha⟩ : Fin (n / 2) ↪ Fin n), (⟨b, hb⟩ : Fin (n / 2) ↪ Fin n)) ∈
              (Finset.univ : Finset (Fin (n / 2) ↪ Fin n)) ×ˢ (Finset.univ : Finset (Fin (n / 2) ↪ Fin n)) := by
            simp
          exact mul_den_mem _ _ (Finset.dvd_lcm (f := fun e : (Fin (n / 2) ↪ Fin n) × (Fin (n / 2) ↪ Fin n) =>
            ((T.submatrix e.1 e.2).det).den) hmem)
        · have : (T.submatrix a b).det = 0 := det_submatrix_cols_eq_zero hb (T.submatrix a id)
          rw [this, mul_zero]
          exact Subring.zero_mem _
      · have : (T.submatrix a b).det = 0 := det_submatrix_rows_eq_zero ha (T.submatrix id b)
        rw [this, mul_zero]
        exact Subring.zero_mem _
    obtain ⟨z, hz⟩ := inv_W_mem T s U V hs hV hTUV (L : ℚ) hL
    have hW0 : ((∏ i, s i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hW
    have h1 : (L : ℚ) = z * ((∏ i, s i : ℕ) : ℚ) := by
      simp only [eq_intCast] at hz
      rw [hz]; field_simp
    have h2 : (L : ℤ) = z * ((∏ i, s i : ℕ) : ℤ) := by exact_mod_cast h1
    exact Int.natCast_dvd_natCast.1 ⟨z, by rw [h2]; ring⟩
  · apply Finset.lcm_dvd
    intro e _
    exact den_dvd_of_mul_mem _ _ hW (minor_W_mem T s U V hs hU hTUV e.1 e.2)

end QuadFormsKB.Lattices
