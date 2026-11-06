/-
# Cassels, Chapter 8, Lemma 4.2 and Corollary: cancellation over $\mathbb Z_2$

**Setting** (as in `Ch8/Dyadic.lean`, $p = 2$): classically integral forms by their symmetric matrices over
$\mathbb Q_2$ (`IsClassIntegral`), proper primitivity (`IsProperlyPrimitive`), orthogonal sums `orthSumMat` (Cassels'
$f + g$ in distinct variables), $\langle u\rangle$ the form $ux^{2}$ (matrix `!![u]`), and $\mathbb Z_2$-equivalence
`ZpEquiv` ($\sim$).

**Proves**
* `zpEquiv_cancel_unit` (**Lemma 4.2**, pp. 120–122): a "Witt's lemma" over $\mathbb Z_2$: if
  $\langle u\rangle + g_1 \sim \langle u\rangle + g_2$ for a unit $u$, and $g_1, g_2$ are both properly primitive or both
  not, then $g_1 \sim g_2$. (Equivalence (4.7) shows that the condition is needed.)
* `zpEquiv_cancel_binary` (**Corollary to Lemma 4.2**, p. 122): if $g_1, g_2$ are integral but not properly primitive
  and $h + g_1 \sim h + g_2$ with $h = 2x_1x_2$ (4.20) or $h = 2x_1^{2} + 2x_1x_2 + 2x_2^{2}$ (4.21), then
  $g_1 \sim g_2$. (The formulas (4.20), (4.21) are lost in the scan; they are reconstructed from the proof, which adds
  $\langle 1\rangle$ and uses (4.7), (4.8).)

**Proof of Lemma 4.2** (Cassels' cases; the end of case (iii), lost in the scan, is completed as follows). In
$\Lambda = \mathbb Z_2^{1+m}$ with $\varphi = \langle u\rangle + g_1$, let $b = e_0$ and $c = Te_0$ ($\varphi(b) = \varphi(c) = u$);
an integral isometry $\sigma$ with $\sigma b = \pm c$ maps $b^{\perp}$ (form $g_1$) onto $c^{\perp}$ (form $g_2$).
(i) $\varphi(b, c)$ even: $\varphi(b - c) \equiv 2 \pmod 4$ and $\tau_{b-c}$ is integral. (ii) $\varphi(b,c)$ odd: after
$c \mapsto -c$, $\varphi(b - c) \equiv 4 \pmod 8$; if $\varphi(b - c, \Lambda) \subseteq 2\mathbb Z_2$, $\tau_{b-c}$ is
integral. (iii) Otherwise some $d$ has $\varphi(b - c, d)$ odd; $N = \langle b, b - c, d\rangle$ is unimodular, so
$\Lambda = N \perp K$, $g_1 \sim h_1 + k$, $g_2 \sim h_2 + k$ with $h_1 = b^{\perp} \cap N$, $h_2 = c^{\perp} \cap N$ binary
unimodular with $\langle u\rangle + h_1 \sim \langle u\rangle + h_2$ (both are $N$), and exactly one of $h_1, h_2$ is even
(the diagonal values of the projections of $d$ differ by $\varphi(d, b - c)$, odd). If $k$ is even, $g_1$ and $g_2$
differ in proper primitivity, excluded by hypothesis. Otherwise $k \sim \langle v\rangle + k_1$. The even one is $H$:
if it were $A$ ($\det \equiv 3$), the odd one would be $\langle a, 3a\rangle$ and $\langle u\rangle + A \sim
\langle u, a, 3a\rangle$ is impossible, the characteristic values (Example 4 (ii)) being $u$ and $u + 4a \pmod 8$. Then
the odd one has determinant $\equiv -1$, so it is $\langle a, -a\rangle \sim \langle v, -v\rangle$, and (4.7) gives
$h_1 + \langle v\rangle \sim h_2 + \langle v\rangle$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.DyadicCancelAux

namespace QuadFormsKB.Cassels.Lemma42

open QuadFormsKB.Cassels Matrix

/-- A diagonal ternary form `⟨a, b, c⟩` of unit entries with `ab ≡ -1 (mod 8)` is `H ⊥ ⟨c⟩`. -/
private theorem bi_diag3 {a b c : ℚ_[2]} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hab : ‖a * b + 1‖ ≤ 1 / 8) :
    ZpEquiv !![a, 0, 0; 0, b, 0; 0, 0, c] !![0, 1, 0; 1, 0, 0; 0, 0, c] := by
  obtain ⟨w1, r0, hw1, hu1, hr0, hd1⟩ := dyadic_exists_lift ha
  obtain ⟨w3, v0, hw3, hu3, hv0, hd3⟩ := dyadic_exists_lift hc
  set w2 : ℤ_[2] := ⟨b, hb.le⟩ with hw2def
  have hw2 : (w2 : ℚ_[2]) = b := rfl
  have hu2 : IsUnit w2 := PadicInt.isUnit_iff.2 (by rw [PadicInt.norm_def, hw2]; exact hb)
  have h8 : (2 : ℤ_[2]) ^ 3 ∣ w1 * w2 + 1 := by
    have hn : ‖((2 : ℤ_[2]) ^ 3 : ℤ_[2])‖ = 1 / 8 := by
      have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by simpa using PadicInt.norm_p (p := 2)
      rw [norm_pow, h2]; norm_num
    obtain ⟨z, hz⟩ := padicInt_dvd_of_norm_le (a := (2 : ℤ_[2]) ^ 3) (b := w1 * w2 + 1)
      (by norm_num) (by
        show ‖((w1 * w2 + 1 : ℤ_[2]) : ℚ_[2])‖ ≤ _
        rw [hn]; push_cast; rw [hw1, hw2]; exact hab)
    exact ⟨z, hz⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, r0 * r0 = 1 + 8 * k := by
    rcases hr0 with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨3, by norm_num⟩, ⟨6, by norm_num⟩]
  have hk' : (r0 : ℤ_[2]) * r0 = 1 + 8 * (k : ℤ_[2]) := by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[2]) hk
  have h2 : (2 : ℤ_[2]) ^ 3 ∣ w2 - (-(r0 : ℤ_[2])) := by
    obtain ⟨e1, he1⟩ := h8
    obtain ⟨e2, he2⟩ := hd1
    have hw : w1 = r0 + 2 ^ 3 * e2 := by linear_combination he2
    subst hw
    exact ⟨(r0 : ℤ_[2]) * (e1 - e2 * w2) - k * w2, by
      linear_combination (r0 : ℤ_[2]) * he1 + (-(w2)) * hk'⟩
  have hd : ∀ i j, (2 : ℤ_[2]) ^ 3 ∣ (!![w1, 0, 0; 0, w2, 0; 0, 0, w3] : Matrix (Fin 3) (Fin 3) ℤ_[2]) i j -
      (!![(r0 : ℤ_[2]), 0, 0; 0, -(r0 : ℤ_[2]), 0; 0, 0, (v0 : ℤ_[2])] : Matrix (Fin 3) (Fin 3) ℤ_[2]) i j := by
    intro i j
    have h2' : (2 : ℤ_[2]) ^ 3 ∣ w2 + r0 := by simpa using h2
    fin_cases i <;> fin_cases j <;> simp [hd1, hd3, h2']
  have hdet : IsUnit (!![w1, 0, 0; 0, w2, 0; 0, 0, w3] : Matrix (Fin 3) (Fin 3) ℤ_[2]).det := by
    simp [Matrix.det_fin_three]
    exact ⟨⟨hu1, hu2⟩, hu3⟩
  have := dyadic_zpEquiv_of_mod8 (!![w1, 0, 0; 0, w2, 0; 0, 0, w3] : Matrix (Fin 3) (Fin 3) ℤ_[2])
    !![(r0 : ℤ_[2]), 0, 0; 0, -(r0 : ℤ_[2]), 0; 0, 0, (v0 : ℤ_[2])]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp) hdet hd
  have hbi := bi_int r0 v0 hr0 hv0
  have e1 : ZpEquiv !![a, 0, 0; 0, b, 0; 0, 0, c] !![(r0 : ℚ_[2]), 0, 0; 0, -r0, 0; 0, 0, v0] := by
    convert this using 1
    · ext i j; fin_cases i <;> fin_cases j <;> simp [hw1, hw2, hw3]
    · ext i j; fin_cases i <;> fin_cases j <;> simp
  have this2 := dyadic_zpEquiv_of_mod8 (!![0, 1, 0; 1, 0, 0; 0, 0, w3] : Matrix (Fin 3) (Fin 3) ℤ_[2])
    !![0, 1, 0; 1, 0, 0; 0, 0, (v0 : ℤ_[2])]
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by ext i j; fin_cases i <;> fin_cases j <;> simp)
    (by simp [Matrix.det_fin_three]; exact hu3)
    (by intro i j; fin_cases i <;> fin_cases j <;> simp [hd3])
  have e2 : ZpEquiv !![(0 : ℚ_[2]), 1, 0; 1, 0, 0; 0, 0, c] !![0, 1, 0; 1, 0, 0; 0, 0, (v0 : ℚ_[2])] := by
    convert this2 using 1
    · ext i j; fin_cases i <;> fin_cases j <;> simp [hw3]
    · ext i j; fin_cases i <;> fin_cases j <;> simp
  exact e1.trans (hbi.trans e2.symm)

/-- The `3 × 3` matrix of `P ⊥ ⟨v⟩` for a binary `P`. -/
private theorem bi_orth21 (P : Matrix (Fin 2) (Fin 2) ℚ_[2]) (v : ℚ_[2]) :
    orthSumMat P !![v] = !![P 0 0, P 0 1, 0; P 1 0, P 1 1, 0; 0, 0, v] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact dyadic_orthSumMat_cc P _ 0 0
  · exact dyadic_orthSumMat_cc P _ 0 1
  · exact dyadic_orthSumMat_cn P _ 0 0
  · exact dyadic_orthSumMat_cc P _ 1 0
  · exact dyadic_orthSumMat_cc P _ 1 1
  · exact dyadic_orthSumMat_cn P _ 1 0
  · exact dyadic_orthSumMat_nc P _ 0 0
  · exact dyadic_orthSumMat_nc P _ 0 1
  · exact dyadic_orthSumMat_nn P _ 0 0

/-- A determinant `≡ -1 (mod 8)` is a unit. -/
private theorem bi_det_unit {d : ℚ_[2]} (hd : ‖d + 1‖ ≤ 1 / 8) : ‖d‖ = 1 := by
  have h1 : ‖d‖ ≤ 1 := by
    have := mn_sub_le (d + 1) 1
    rw [show d + 1 - 1 = d by ring, norm_one] at this
    exact this.trans (max_le (hd.trans (by norm_num)) le_rfl)
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have := mn_sub_le (d + 1) d
  rw [show d + 1 - d = 1 by ring, norm_one] at this
  have h2 : max ‖d + 1‖ ‖d‖ < 1 := max_lt (lt_of_le_of_lt hd (by norm_num)) hlt
  linarith

/-- An odd binary form whose first diagonal entry is a unit. -/
private theorem odd_core {h : Matrix (Fin 2) (Fin 2) ℚ_[2]} (hs : hᵀ = h) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (h0 : ‖h 0 0‖ = 1) (hdet : ‖h.det + 1‖ ≤ 1 / 8) {v : ℚ_[2]} (hv : ‖v‖ = 1) :
    ZpEquiv (orthSumMat h !![v]) (orthSumMat !![0, 1; 1, 0] !![v]) := by
  have h10 : h 1 0 = h 0 1 := by
    have := congrFun (congrFun hs 0) 1
    simpa [Matrix.transpose_apply] using this
  have hx : h 0 0 ≠ 0 := by intro h; rw [h, norm_zero] at h0; exact zero_ne_one h0
  have hdet2 : h.det = h 0 0 * h 1 1 - h 0 1 * h 0 1 := by
    rw [Matrix.det_fin_two, h10]
  set ρ' : ℚ_[2] := h 1 1 - h 0 1 * h 0 1 / h 0 0 with hρ'
  have hxρ : h 0 0 * ρ' = h.det := by
    rw [hdet2, hρ']; field_simp
  have hdu := bi_det_unit hdet
  have hρn : ‖ρ'‖ = 1 := by
    have : ‖h 0 0‖ * ‖ρ'‖ = 1 := by rw [← norm_mul, hxρ, hdu]
    rw [h0, one_mul] at this; exact this
  have hS : UM (!![1, -(h 0 1 / h 0 0); 0, 1] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
    refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two]⟩
    fin_cases i <;> fin_cases j <;> simp
    rw [h0, div_one]; exact hi 0 1
  have e1 : ZpEquiv h !![h 0 0, 0; 0, ρ'] := by
    refine zpEquiv_of_UM hS ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hρ', h10] <;> field_simp <;> ring
  have e2 := dyadic_zpEquiv_orthSum e1 (ZpEquiv.refl !![v])
  rw [bi_orth21, bi_orth21] at *
  have := bi_diag3 h0 hρn hv (by rw [hxρ]; exact hdet)
  refine e2.trans ?_
  convert this using 1 <;> simp

private theorem odd_bin_diag {h : Matrix (Fin 2) (Fin 2) ℚ_[2]} (hs : hᵀ = h) (hi : ∀ i j, ‖h i j‖ ≤ 1)
    (hodd : ∃ i, ‖h i i‖ = 1) (hdet : ‖h.det + 1‖ ≤ 1 / 8) {v : ℚ_[2]} (hv : ‖v‖ = 1) :
    ZpEquiv (orthSumMat h !![v]) (orthSumMat !![0, 1; 1, 0] !![v]) := by
  by_cases h0 : ‖h 0 0‖ = 1
  · exact odd_core hs hi h0 hdet hv
  · have h1 : ‖h 1 1‖ = 1 := by
      obtain ⟨i, hi'⟩ := hodd
      fin_cases i
      · exact absurd hi' h0
      · exact hi'
    set σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1 with hσ
    have hp := dyadic_zpEquiv_perm h σ
    have hs' : (h.submatrix σ σ)ᵀ = h.submatrix σ σ := by rw [Matrix.transpose_submatrix, hs]
    have hdet' : ‖(h.submatrix σ σ).det + 1‖ ≤ 1 / 8 := by
      rw [Matrix.det_submatrix_equiv_self]; exact hdet
    have hc := odd_core hs' (fun i j => hi _ _) (by simpa [hσ] using h1) hdet' hv
    exact (dyadic_zpEquiv_orthSum hp (ZpEquiv.refl _)).trans hc

/-- Integrality of an orthogonal sum. -/
private theorem bi_orth_int {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℚ_[2]} {B : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) : ∀ i j, ‖orthSumMat A B i j‖ ≤ 1 := by
  intro i j
  rw [dyadic_orthSumMat_eq, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [hA, hB]

/-- The case `h` even, `h'` odd of `fin_step`. -/
private theorem fin_half {m' : ℕ} {h h' : Matrix (Fin 2) (Fin 2) ℚ_[2]} {K : Matrix (Fin m') (Fin m') ℚ_[2]}
    (hs : hᵀ = h) (hs' : h'ᵀ = h') (hKs : Kᵀ = K) (hi : ∀ i j, ‖h i j‖ ≤ 1) (hi' : ∀ i j, ‖h' i j‖ ≤ 1)
    (hKi : IsClassIntegral K) (hdet : ‖h.det + 1‖ ≤ 1 / 8) (hdet' : ‖h'.det + 1‖ ≤ 1 / 8)
    (hE : ∀ i, ‖h i i‖ < 1) (hO : ∃ i, ‖h' i i‖ = 1)
    (hpp : IsProperlyPrimitive (orthSumMat h K) ↔ IsProperlyPrimitive (orthSumMat h' K)) :
    ZpEquiv (orthSumMat h K) (orthSumMat h' K) := by
  by_cases hK : ∃ i, ‖K i i‖ = 1
  · obtain ⟨i, hiK⟩ := hK
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = 1 + m'' := ⟨m' - 1, by have := i.pos; omega⟩
    obtain ⟨v, K1, hv, hKe⟩ := pivot_split hKs hKi i hiK
    have eH : ZpEquiv (orthSumMat h !![v]) (orthSumMat !![0, 1; 1, 0] !![v]) :=
      dyadic_zpEquiv_orthSum (even_bin_H hs hi hE hdet) (ZpEquiv.refl _)
    have eO := odd_bin_diag hs' hi' hO hdet' hv
    have e := eH.trans eO.symm
    have hh : 2 + (1 + m'') = 2 + 1 + m'' := by omega
    have e2 : ZpEquiv (orthSumMat h (orthSumMat !![v] K1)) (orthSumMat h' (orthSumMat !![v] K1)) := by
      rw [dyadic_orthSumMat_assoc h !![v] K1 hh, dyadic_orthSumMat_assoc h' !![v] K1 hh]
      exact dyadic_zpEquiv_cast hh (dyadic_zpEquiv_orthSum e (ZpEquiv.refl _))
    exact (dyadic_zpEquiv_orthSum (ZpEquiv.refl h) hKe).trans
      (e2.trans (dyadic_zpEquiv_orthSum (ZpEquiv.refl h') hKe).symm)
  · exfalso
    push Not at hK
    have hKlt : ∀ i, ‖K i i‖ < 1 := fun i => lt_of_le_of_ne (hKi i i) (hK i)
    have hP' : IsProperlyPrimitive (orthSumMat h' K) := by
      rw [pp_iff_diag]
      obtain ⟨i0, hi0⟩ := hO
      exact ⟨bi_orth_int hi' hKi, Fin.castAdd m' i0, by rw [dyadic_orthSumMat_cc]; exact hi0⟩
    obtain ⟨hI, j, hj⟩ := pp_iff_diag.1 (hpp.2 hP')
    induction j using Fin.addCases with
    | left i => rw [dyadic_orthSumMat_cc] at hj; exact absurd hj (hE i).ne
    | right i => rw [dyadic_orthSumMat_nn] at hj; exact absurd hj (hKlt i).ne

private theorem fin_step {m' : ℕ} {h h' : Matrix (Fin 2) (Fin 2) ℚ_[2]} {K : Matrix (Fin m') (Fin m') ℚ_[2]}
    (hs : hᵀ = h) (hs' : h'ᵀ = h') (hKs : Kᵀ = K) (hi : ∀ i j, ‖h i j‖ ≤ 1) (hi' : ∀ i j, ‖h' i j‖ ≤ 1)
    (hKi : IsClassIntegral K) (hdet : ‖h.det + 1‖ ≤ 1 / 8) (hdet' : ‖h'.det + 1‖ ≤ 1 / 8)
    (hpar : ((∀ i, ‖h i i‖ < 1) ∧ ∃ i, ‖h' i i‖ = 1) ∨ ((∃ i, ‖h i i‖ = 1) ∧ ∀ i, ‖h' i i‖ < 1))
    (hpp : IsProperlyPrimitive (orthSumMat h K) ↔ IsProperlyPrimitive (orthSumMat h' K)) :
    ZpEquiv (orthSumMat h K) (orthSumMat h' K) := by
  rcases hpar with ⟨hE, hO⟩ | ⟨hO, hE⟩
  · exact fin_half hs hs' hKs hi hi' hKi hdet hdet' hE hO hpp
  · exact (fin_half hs' hs hKs hi' hi hKi hdet' hdet hE hO hpp.symm).symm

/-- Conjugating the first summand of an orthogonal sum, transported along a cast. -/
private theorem cc_w_conj {n a c : ℕ} (h : n = a + c) (Q M N : Matrix (Fin a) (Fin a) ℚ_[2])
    (K : Matrix (Fin c) (Fin c) ℚ_[2]) (hQ : Qᵀ * M * Q = N) :
    ((orthSumMat Q (1 : Matrix (Fin c) (Fin c) ℚ_[2])).submatrix (Fin.cast h) (Fin.cast h))ᵀ *
      (orthSumMat M K).submatrix (Fin.cast h) (Fin.cast h) *
      (orthSumMat Q (1 : Matrix (Fin c) (Fin c) ℚ_[2])).submatrix (Fin.cast h) (Fin.cast h) =
    (orthSumMat N K).submatrix (Fin.cast h) (Fin.cast h) := by
  rw [cc_cast_conj, orthSumMat_transpose', orthSumMat_mul', orthSumMat_mul']
  simp [hQ]


/-- First column of the transported rotation. -/
private theorem cc_w_col {m' : ℕ} {t : ℚ_[2]} (Q : Matrix (Fin (1 + 2)) (Fin (1 + 2)) ℚ_[2])
    (hQ : ∀ x, Q x 0 = if x = 0 then t else if x = 2 then 1 else 0) (h : 1 + (2 + m') = 1 + 2 + m')
    (y : Fin (1 + (2 + m'))) :
    ((orthSumMat Q (1 : Matrix (Fin m') (Fin m') ℚ_[2])).submatrix (Fin.cast h) (Fin.cast h)) y
        (Fin.castAdd (2 + m') 0) =
      if y = Fin.castAdd (2 + m') 0 then t else if y = Fin.natAdd 1 (Fin.castAdd m' 1) then 1 else 0 := by
  have e0 : Fin.cast h (Fin.castAdd (2 + m') (0 : Fin 1)) = Fin.castAdd m' (0 : Fin (1 + 2)) := Fin.ext (by simp)
  rw [Matrix.submatrix_apply, e0]
  by_cases hy : y.val < 3
  · have ey : Fin.cast h y = Fin.castAdd m' (⟨y.val, hy⟩ : Fin (1 + 2)) := Fin.ext (by simp)
    rw [ey, dyadic_orthSumMat_cc, hQ]
    have c1 : (⟨y.val, hy⟩ : Fin (1 + 2)) = 0 ↔ y = Fin.castAdd (2 + m') 0 := by
      rw [Fin.ext_iff, Fin.ext_iff]
      simp
    have c2 : (⟨y.val, hy⟩ : Fin (1 + 2)) = 2 ↔ y = Fin.natAdd 1 (Fin.castAdd m' 1) := by
      rw [Fin.ext_iff, Fin.ext_iff]
      simp
    simp only [c1, c2]
  · have ey : Fin.cast h y = Fin.natAdd (1 + 2) (⟨y.val - 3, by omega⟩ : Fin m') := Fin.ext (by simp; omega)
    rw [ey, dyadic_orthSumMat_nc]
    have c1 : ¬ y = Fin.castAdd (2 + m') 0 := fun e => hy (by rw [e]; simp)
    have c2 : ¬ y = Fin.natAdd 1 (Fin.castAdd m' 1) := fun e => hy (by rw [e]; simp)
    simp [c1, c2]

/-- Column of a product when the right factor's column has two nonzero entries. -/
private theorem cc_mul_col {n : ℕ} (X W : Matrix (Fin n) (Fin n) ℚ_[2]) (j a b : Fin n) (hab : a ≠ b) (t : ℚ_[2])
    (hW : ∀ y, W y j = if y = a then t else if y = b then 1 else 0) (x : Fin n) :
    (X * W) x j = X x a * t + X x b := by
  rw [Matrix.mul_apply]
  have : ∀ y, X x y * W y j = (if y = a then X x a * t else 0) + (if y = b then X x b else 0) := by
    intro y
    rw [hW]
    by_cases h1 : y = a
    · subst h1; simp [hab]
    · by_cases h2 : y = b
      · subst h2; simp [h1]
      · simp [h1, h2]
  simp [this, Finset.sum_add_distrib]

/-- The columns `e_0` and `e_{tail 1}` are fixed by `1 ⊥ U` when `U` fixes the first two coordinates. -/
private theorem cc_X_col {m' : ℕ} (U : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2])
    (hU : ∀ (i : Fin 2) (x : Fin (2 + m')), U x (Fin.castAdd m' i) = if x = Fin.castAdd m' i then 1 else 0)
    (x : Fin (1 + (2 + m'))) :
    orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) U x (Fin.castAdd (2 + m') 0) =
        (if x = Fin.castAdd (2 + m') 0 then 1 else 0) ∧
      orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) U x (Fin.natAdd 1 (Fin.castAdd m' 1)) =
        (if x = Fin.natAdd 1 (Fin.castAdd m' 1) then 1 else 0) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [dyadic_orthSumMat_cc, dyadic_orthSumMat_cn]
    simp [cc_castAdd_ne_natAdd]
  · rw [dyadic_orthSumMat_nc, dyadic_orthSumMat_nn, hU]
    simp [(cc_castAdd_ne_natAdd _ _).symm]

/-- A unit plus a non-unit is a unit. -/
private theorem cc_unit_add_small {x y : ℚ_[2]} (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) : ‖x + y‖ = 1 := by
  refine le_antisymm ((IsUltrametricDist.norm_add_le_max x y).trans (max_le hx.le hy.le)) ?_
  by_contra hlt
  push_neg at hlt
  have : ‖x‖ ≤ max ‖x + y‖ ‖y‖ := by
    simpa using mn_sub_le (x + y) y
  rw [hx] at this
  rcases le_max_iff.1 this with h | h <;> linarith

private theorem cc_add_small {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 1 / 8) : ‖a + b‖ ≤ 1 / 8 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

/-- The numerical facts about the two binary blocks needed for `fin_step`. -/
private theorem cc_fin_inputs {u t r β γ : ℚ_[2]} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1) (hr : ‖r‖ ≤ 1) (hβ : ‖β‖ = 1)
    (hγ : u * t ^ 2 + γ = u) (h1 h2 : Matrix (Fin 2) (Fin 2) ℚ_[2]) (e1 : h1 = !![r, β; β, γ])
    (e2 : h2 = !![u * β ^ 2 + u ^ 2 * t ^ 2 * r, -(u * t) * (γ * r - β ^ 2);
          -(u * t) * (γ * r - β ^ 2), γ * (γ * r - β ^ 2)]) :
    ‖γ‖ ≤ 1 / 8 ∧ h1ᵀ = h1 ∧ h2ᵀ = h2 ∧ (∀ i j, ‖h1 i j‖ ≤ 1) ∧ (∀ i j, ‖h2 i j‖ ≤ 1) ∧
      ‖h1.det + 1‖ ≤ 1 / 8 ∧ ‖h2.det + 1‖ ≤ 1 / 8 ∧
      (((∀ i, ‖h1 i i‖ < 1) ∧ ∃ i, ‖h2 i i‖ = 1) ∨ ((∃ i, ‖h1 i i‖ = 1) ∧ ∀ i, ‖h2 i i‖ < 1)) := by
  have hγe : γ = u * (1 - t ^ 2) := by linear_combination hγ
  have hγs : ‖γ‖ ≤ 1 / 8 := by
    rw [hγe, norm_mul, hu, one_mul]; exact (cm_unit_norms t ht).2
  have hγ1 : ‖γ‖ ≤ 1 := hγs.trans (by norm_num)
  have hβ2 : ‖β ^ 2‖ = 1 := by rw [norm_pow, hβ]; simp
  have hD : ‖γ * r - β ^ 2‖ ≤ 1 := (mn_sub_le _ _).trans (max_le (cm_mul1 _ _ hγ1 hr) hβ2.le)
  have hd1 : ‖γ * r - β ^ 2 + 1‖ ≤ 1 / 8 := by
    have : γ * r - β ^ 2 + 1 = γ * r + (1 - β ^ 2) := by ring
    rw [this]
    refine cc_add_small ?_ ?_
    · rw [norm_mul]; nlinarith [norm_nonneg γ, norm_nonneg r]
    · rw [← norm_neg]; simpa using cc_sq_sub_one hβ
  have hut : ‖u * t‖ = 1 := by rw [norm_mul, hu, ht, one_mul]
  have hβu : ‖β * u‖ = 1 := by rw [norm_mul, hu, hβ, one_mul]
  have hdet2 : h2.det = (β * u) ^ 2 * (γ * r - β ^ 2) := by
    rw [e2, Matrix.det_fin_two_of]
    linear_combination ((γ * r - β ^ 2) * β ^ 2 * u) * hγ
  refine ⟨hγs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · rw [e2]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j; rw [e1]; fin_cases i <;> fin_cases j <;> simp [hr, hβ.le, hγ1]
  · intro i j
    rw [e2]
    have ha : ‖u * β ^ 2 + u ^ 2 * t ^ 2 * r‖ ≤ 1 := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, hu, hβ2]; simp
      · rw [norm_mul, norm_mul, norm_pow, norm_pow, hu, ht]; simpa using hr
    have hb : ‖-(u * t) * (γ * r - β ^ 2)‖ ≤ 1 := by
      rw [norm_mul, norm_neg, hut, one_mul]; exact hD
    have hc : ‖γ * (γ * r - β ^ 2)‖ ≤ 1 := cm_mul1 _ _ hγ1 hD
    fin_cases i <;> fin_cases j <;> first | exact ha | exact hb | exact hc
  · rw [e1, Matrix.det_fin_two_of]
    have : r * γ - β * β + 1 = γ * r + (1 - β ^ 2) := by ring
    rw [this]
    refine cc_add_small ?_ ?_
    · rw [norm_mul]; nlinarith [norm_nonneg γ, norm_nonneg r]
    · rw [← norm_neg]; simpa using cc_sq_sub_one hβ
  · have hdet1 : h1.det = γ * r - β ^ 2 := by rw [e1, Matrix.det_fin_two_of]; ring
    rw [hdet2]
    have : (β * u) ^ 2 * (γ * r - β ^ 2) + 1 = (β * u) ^ 2 * (γ * r - β ^ 2 + 1) + (1 - (β * u) ^ 2) := by ring
    rw [this]
    refine cc_add_small ?_ ?_
    · rw [norm_mul, norm_pow, hβu]; simpa using hd1
    · rw [← norm_neg]; simpa using cc_sq_sub_one hβu
  · have hd2 : ‖γ * (γ * r - β ^ 2)‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg γ, norm_nonneg (γ * r - β ^ 2)]
    have hT : u ^ 2 * t ^ 2 * r = u * (u * t ^ 2 * r) := by ring
    rcases lt_or_eq_of_le hr with hlt | heq
    · left
      refine ⟨fun i => ?_, 0, ?_⟩
      · rw [e1]; fin_cases i <;> simp [hlt]; linarith
      · rw [e2]
        simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_zero]
        refine cc_unit_add_small ?_ ?_
        · rw [norm_mul, hu, hβ2]; simp
        · rw [norm_mul, norm_mul, norm_pow, norm_pow, hu, ht]; simpa using hlt
    · right
      refine ⟨⟨0, ?_⟩, fun i => ?_⟩
      · rw [e1]; simpa using heq
      · rw [e2]
        fin_cases i
        · simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
            Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Fin.zero_eta]
          have : u * β ^ 2 + u ^ 2 * t ^ 2 * r = u * (β ^ 2 + u * t ^ 2 * r) := by ring
          rw [this, norm_mul, hu, one_mul]
          refine cc_unit_add_unit hβ2 ?_
          rw [norm_mul, norm_mul, norm_pow, hu, ht, heq]; simp
        · simpa using hd2

/-- Case (iii) in normal form: `c = T e_0 = t e_0 + e_{tail 1}` and `β = G₁(0,1)` a unit. -/
private theorem c3_core {m' : ℕ} {u t : ℚ_[2]} (hu : ‖u‖ = 1) (ht : ‖t‖ = 1)
    {G1 G2 : Matrix (Fin (2 + m')) (Fin (2 + m')) ℚ_[2]} (h₁ : G1ᵀ = G1) (h₂ : G2ᵀ = G2)
    (hi₁ : IsClassIntegral G1) (hi₂ : IsClassIntegral G2)
    (hpp : IsProperlyPrimitive G1 ↔ IsProperlyPrimitive G2)
    (hβ : ‖G1 (Fin.castAdd m' 0) (Fin.castAdd m' 1)‖ = 1)
    (T : Matrix (Fin (1 + (2 + m'))) (Fin (1 + (2 + m'))) ℚ_[2]) (hT : UM T)
    (hc : ∀ x, T x (Fin.castAdd (2 + m') 0) =
      if x = Fin.castAdd (2 + m') 0 then t else if x = Fin.natAdd 1 (Fin.castAdd m' 1) then 1 else 0)
    (heq : Tᵀ * orthSumMat !![u] G1 * T = orthSumMat !![u] G2) : ZpEquiv G1 G2 := by
  have hγ := cc_gamma T hc heq
  set r := G1 (Fin.castAdd m' 0) (Fin.castAdd m' 0) with hrdef
  set β := G1 (Fin.castAdd m' 0) (Fin.castAdd m' 1) with hβdef
  set γ := G1 (Fin.castAdd m' 1) (Fin.castAdd m' 1) with hγdef
  have hr : ‖r‖ ≤ 1 := hi₁ _ _
  have hβ10 : G1 (Fin.castAdd m' 1) (Fin.castAdd m' 0) = β := by
    have := congrFun (congrFun h₁ (Fin.castAdd m' 0)) (Fin.castAdd m' 1)
    simpa [Matrix.transpose_apply] using this
  have e1 : G1.submatrix (Fin.castAdd m') (Fin.castAdd m') = !![r, β; β, γ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hrdef, hβdef, hγdef, hβ10]
  obtain ⟨hγs, hs1, hs2, hin1, hin2, hdt1, hdt2, hpar⟩ := cc_fin_inputs hu ht hr hβ hγ
    (!![r, β; β, γ]) (!![u * β ^ 2 + u ^ 2 * t ^ 2 * r, -(u * t) * (γ * r - β ^ 2);
          -(u * t) * (γ * r - β ^ 2), γ * (γ * r - β ^ 2)]) rfl rfl
  have hdet1 : ‖(G1.submatrix (Fin.castAdd m') (Fin.castAdd m')).det‖ = 1 := by
    rw [e1]
    have h1 : ‖(-1 : ℚ_[2]) + ((!![r, β; β, γ] : Matrix (Fin 2) (Fin 2) ℚ_[2]).det + 1)‖ = 1 :=
      cc_unit_add_small (by simp) (lt_of_le_of_lt hdt1 (by norm_num))
    simpa using h1
  obtain ⟨U, K, hU, hUfix, hKs, hKi, hUeq⟩ := split_unimodular_block h₁ hi₁ hdet1
  rw [e1] at hUeq
  obtain ⟨Q, hQ0, hQdet, hQi, hQeq⟩ := q3 (r := r) hu.le ht.le hβ.le (hγs.trans (by norm_num)) hγ
  have hQU : UM Q := ⟨hQi, by rw [hQdet, norm_mul, hβ, hu, one_mul]⟩
  have hh : 1 + (2 + m') = 1 + 2 + m' := by omega
  set H2 : Matrix (Fin 2) (Fin 2) ℚ_[2] := !![u * β ^ 2 + u ^ 2 * t ^ 2 * r, -(u * t) * (γ * r - β ^ 2);
          -(u * t) * (γ * r - β ^ 2), γ * (γ * r - β ^ 2)] with hH2
  set X : Matrix (Fin (1 + (2 + m'))) (Fin (1 + (2 + m'))) ℚ_[2] := orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) U
    with hX
  set W : Matrix (Fin (1 + (2 + m'))) (Fin (1 + (2 + m'))) ℚ_[2] :=
    (orthSumMat Q (1 : Matrix (Fin m') (Fin m') ℚ_[2])).submatrix (Fin.cast hh) (Fin.cast hh) with hW
  have hXU : UM X := UM.orthSum UM.one hU
  have hWU : UM W := UM.cast hh (UM.orthSum hQU UM.one)
  have hXeq : Xᵀ * orthSumMat !![u] G1 * X = orthSumMat !![u] (orthSumMat !![r, β; β, γ] K) := by
    rw [hX, orthSumMat_transpose', orthSumMat_mul', orthSumMat_mul', hUeq]
    congr 1
    ext i j
    fin_cases i; fin_cases j; simp
  have hYeq : (X * W)ᵀ * orthSumMat !![u] G1 * (X * W) = orthSumMat !![u] (orthSumMat H2 K) := by
    have e : (X * W)ᵀ * orthSumMat !![u] G1 * (X * W) = Wᵀ * (Xᵀ * orthSumMat !![u] G1 * X) * W := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hA1 := dyadic_orthSumMat_assoc !![u] !![r, β; β, γ] K hh
    have hA2 := dyadic_orthSumMat_assoc !![u] H2 K hh
    rw [e, hXeq, hA1, hA2]
    exact cc_w_conj hh Q _ _ K hQeq
  have hne : Fin.castAdd (2 + m') (0 : Fin 1) ≠ Fin.natAdd 1 (Fin.castAdd m' (1 : Fin 2)) :=
    cc_castAdd_ne_natAdd _ _
  have hTY : ∀ x, (X * W) x (Fin.castAdd (2 + m') 0) = T x (Fin.castAdd (2 + m') 0) := by
    intro x
    have hx := cc_X_col U hUfix x
    rw [← hX] at hx
    rw [cc_mul_col X W _ _ _ hne t (cc_w_col Q hQ0 hh) x, hx.1, hx.2, hc]
    by_cases h1 : x = Fin.castAdd (2 + m') 0
    · simp [h1, hne]
    · by_cases h2 : x = Fin.natAdd 1 (Fin.castAdd m' 1)
      · simp [h2, hne.symm]
      · simp [h1, h2]
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have E1 : ZpEquiv G1 (orthSumMat !![r, β; β, γ] K) := zpEquiv_of_UM hU hUeq
  have E2 : ZpEquiv G2 (orthSumMat H2 K) := RL2 hu0 T (X * W) hT (hXU.mul hWU) hTY heq hYeq
  have hpp' : IsProperlyPrimitive (orthSumMat !![r, β; β, γ] K) ↔ IsProperlyPrimitive (orthSumMat H2 K) :=
    (pp_of_zpEquiv h₁ hi₁ E1).symm.trans (hpp.trans (pp_of_zpEquiv h₂ hi₂ E2))
  have E3 := fin_step hs1 hs2 hKs hin1 hin2 hKi hdt1 hdt2 hpar hpp'
  exact E1.trans (E3.trans E2.symm)

/-- Entry computations for case (iii): the norm identity for `c` and a unit entry of `G₁ s`, where `s` is the tail
of `c = T e_0`. -/
private theorem cm_setup {m : ℕ} {u : ℚ_[2]} (hu : ‖u‖ = 1) {G1 G2 : Matrix (Fin m) (Fin m) ℚ_[2]}
    (T : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2])
    (heq : Tᵀ * orthSumMat !![u] G1 * T = orthSumMat !![u] G2)
    (ht : ‖T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1)
    (hodd : ∃ y, ‖(orthSumMat !![u] G1 *ᵥ ((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
      fun x => T x (Fin.castAdd m 0))) y‖ = 1) :
    u * T (Fin.castAdd m 0) (Fin.castAdd m 0) ^ 2 + (fun i => T (Fin.natAdd 1 i) (Fin.castAdd m 0)) ⬝ᵥ
      (G1 *ᵥ fun i => T (Fin.natAdd 1 i) (Fin.castAdd m 0)) = u ∧
    ∃ j, ‖(G1 *ᵥ fun i => T (Fin.natAdd 1 i) (Fin.castAdd m 0)) j‖ = 1 := by
  obtain ⟨y, hy⟩ := hodd
  obtain ⟨hn1, hn8⟩ := cm_unit_norms _ ht
  constructor
  · have h := congrFun (congrFun heq (Fin.castAdd m 0)) (Fin.castAdd m 0)
    rw [cm_quad_entry, dyadic_orthSumMat_cc, cm_dot_split] at h
    simp only [cm_orth_mulVec_c, cm_orth_mulVec_n] at h
    simp [dotProduct, Matrix.mulVec] at h
    simp only [dotProduct, Matrix.mulVec]
    linear_combination h
  · induction y using Fin.addCases with
    | left i =>
      exfalso
      rw [cm_orth_mulVec_c] at hy
      fin_cases i
      simp [Matrix.mulVec, dotProduct, norm_mul, hu] at hy
      linarith
    | right j =>
      refine ⟨j, ?_⟩
      rw [cm_orth_mulVec_n] at hy
      have hv : (fun k => ((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
          fun x => T x (Fin.castAdd m 0)) (Fin.natAdd 1 k)) = -(fun i => T (Fin.natAdd 1 i) (Fin.castAdd m 0)) := by
        ext k
        simp [Pi.single_eq_of_ne (cc_castAdd_ne_natAdd (0 : Fin 1) k).symm]
      rw [hv, Matrix.mulVec_neg, Pi.neg_apply, norm_neg] at hy
      exact hy

/-- Choosing a unit entry `s k` and a unit entry `ν j'` of `ν = G₁ s` with `j' ≠ k`. -/
private theorem cm_find {m : ℕ} {G1 : Matrix (Fin m) (Fin m) ℚ_[2]} (hi₁ : IsClassIntegral G1)
    (s : Fin m → ℚ_[2]) (hs : ∀ i, ‖s i‖ ≤ 1) (hq : ‖s ⬝ᵥ (G1 *ᵥ s)‖ < 1)
    (hj : ∃ j, ‖(G1 *ᵥ s) j‖ = 1) : ∃ k j', j' ≠ k ∧ ‖s k‖ = 1 ∧ ‖(G1 *ᵥ s) j'‖ = 1 := by
  have hν : ∀ i, ‖(G1 *ᵥ s) i‖ ≤ 1 := cm_mulVec_le G1 s hi₁ hs
  obtain ⟨j, hj⟩ := hj
  have hk : ∃ k, ‖s k‖ = 1 := by
    by_contra hcon
    push_neg at hcon
    have : ‖(G1 *ᵥ s) j‖ < 1 := by
      simp only [Matrix.mulVec, dotProduct]
      refine cm_sum_lt _ _ fun l _ => ?_
      have h1 : ‖s l‖ < 1 := lt_of_le_of_ne (hs l) (hcon l)
      rw [norm_mul]
      nlinarith [norm_nonneg (G1 j l), norm_nonneg (s l), hi₁ j l]
    linarith
  obtain ⟨k, hk⟩ := hk
  refine ⟨k, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, i ≠ k → ‖(G1 *ᵥ s) i‖ < 1 := fun i hi =>
    lt_of_le_of_ne (hν i) (fun h => hcon i hi hk h)
  have hjk : j = k := by
    by_contra hne
    have := hlt j hne
    linarith
  subst hjk
  have hsum := Finset.add_sum_erase Finset.univ (fun i => s i * (G1 *ᵥ s) i) (Finset.mem_univ j)
  have hrest : ‖∑ i ∈ Finset.univ.erase j, s i * (G1 *ᵥ s) i‖ < 1 := by
    refine cm_sum_lt _ _ fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    rw [norm_mul]
    nlinarith [norm_nonneg (s i), norm_nonneg ((G1 *ᵥ s) i), hs i, hlt i hij]
  have heq : s j * (G1 *ᵥ s) j = s ⬝ᵥ (G1 *ᵥ s) - ∑ i ∈ Finset.univ.erase j, s i * (G1 *ᵥ s) i := by
    simp only [dotProduct]
    linear_combination hsum
  have h1 : ‖s j * (G1 *ᵥ s) j‖ < 1 := by
    rw [heq]
    exact lt_of_le_of_lt (mn_sub_le _ _) (max_lt hq hrest)
  rw [norm_mul, hk, hj] at h1
  norm_num at h1

/-- Case (iii) in general: some entry of `Φ₁ (e_0 - c)` is a unit. -/
private theorem c3_main {m : ℕ} {u : ℚ_[2]} (hu : ‖u‖ = 1) {G1 G2 : Matrix (Fin m) (Fin m) ℚ_[2]}
    (h₁ : G1ᵀ = G1) (h₂ : G2ᵀ = G2) (hi₁ : IsClassIntegral G1) (hi₂ : IsClassIntegral G2)
    (hpp : IsProperlyPrimitive G1 ↔ IsProperlyPrimitive G2)
    (T : Matrix (Fin (1 + m)) (Fin (1 + m)) ℚ_[2]) (hT : UM T)
    (heq : Tᵀ * orthSumMat !![u] G1 * T = orthSumMat !![u] G2)
    (ht : ‖T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1)
    (hodd : ∃ y, ‖(orthSumMat !![u] G1 *ᵥ ((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
      fun x => T x (Fin.castAdd m 0))) y‖ = 1) : ZpEquiv G1 G2 := by
  have hsetup := cm_setup hu T heq ht hodd
  obtain ⟨hq, hjex⟩ := hsetup
  set t0 := T (Fin.castAdd m 0) (Fin.castAdd m 0) with ht0
  set s : Fin m → ℚ_[2] := fun i => T (Fin.natAdd 1 i) (Fin.castAdd m 0) with hsdef
  have hs : ∀ i, ‖s i‖ ≤ 1 := fun i => hT.1 _ _
  have hq' : ‖s ⬝ᵥ (G1 *ᵥ s)‖ < 1 := by
    have h8 : s ⬝ᵥ (G1 *ᵥ s) = u * (1 - t0 ^ 2) := by linear_combination hq
    rw [h8, norm_mul, hu, one_mul]
    exact lt_of_le_of_lt (cm_unit_norms _ ht).2 (by norm_num)
  obtain ⟨k, j', hjk, hk, hj'⟩ := cm_find hi₁ s hs hq' hjex
  have hm2 : 2 ≤ m := by
    have h1 := j'.isLt
    have h2 := k.isLt
    have h3 : j'.val ≠ k.val := fun h => hjk (Fin.ext h)
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = 2 + m' := ⟨m - 2, by omega⟩
  obtain ⟨S, hS, hS0, hS1⟩ := norm_basis s hs hjk hk
  obtain ⟨hSinv, hSS, hSS'⟩ := UM.inv hS
  have hST : ∀ i j, ‖(Sᵀ) i j‖ ≤ 1 := fun i j => hS.1 j i
  have hG1S : Sᵀ * G1 * S * 1 = Sᵀ * G1 * S := Matrix.mul_one _
  set G1' := Sᵀ * G1 * S with hG1'
  have hequiv : ZpEquiv G1 G1' := zpEquiv_of_UM hS rfl
  have hsymm : G1'ᵀ = G1' := by
    rw [hG1', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h₁, Matrix.mul_assoc]
  have hint : IsClassIntegral G1' := fun i j =>
    cm_mul_le _ _ (cm_mul_le _ _ hST hi₁) hS.1 i j
  have hpp' : IsProperlyPrimitive G1' ↔ IsProperlyPrimitive G2 :=
    (pp_of_zpEquiv h₁ hi₁ hequiv).symm.trans hpp
  have hUT : UM (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ * T) :=
    UM.mul (UM.orthSum UM.one hSinv) hT
  have hTeq : (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ * T)ᵀ * orthSumMat !![u] G1' *
      (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ * T) = orthSumMat !![u] G2 := by
    rw [← heq, Matrix.transpose_mul, orthSumMat_transpose']
    have hX : orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2])ᵀ S⁻¹ᵀ * orthSumMat !![u] G1' *
        orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ = orthSumMat !![u] G1 := by
      rw [orthSumMat_mul', orthSumMat_mul']
      congr 1
      · ext a b; simp
      · rw [hG1']
        have e1 : S⁻¹ᵀ * (Sᵀ * G1 * S) * S⁻¹ = (S * S⁻¹)ᵀ * G1 * (S * S⁻¹) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
        rw [e1, hSS]; simp
    calc _ = Tᵀ * (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2])ᵀ S⁻¹ᵀ * orthSumMat !![u] G1' *
        orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹) * T := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hX]
  have hSs : S⁻¹ *ᵥ s = Pi.single (Fin.castAdd m' 1) 1 := by
    have : s = S *ᵥ (Pi.single (Fin.castAdd m' 1) 1) := by
      ext x; rw [Matrix.mulVec_single_one]; exact (hS1 x).symm
    rw [this, Matrix.mulVec_mulVec, hSS', Matrix.one_mulVec]
  have hcol : ∀ x, (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ * T) x (Fin.castAdd (2 + m') 0) =
      if x = Fin.castAdd (2 + m') 0 then t0 else if x = Fin.natAdd 1 (Fin.castAdd m' 1) then 1 else 0 := by
    intro x
    have hc : (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ * T) x (Fin.castAdd (2 + m') 0) =
        (orthSumMat (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) S⁻¹ *ᵥ fun y => T y (Fin.castAdd (2 + m') 0)) x := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hc]
    induction x using Fin.addCases with
    | left i =>
      rw [cm_orth_mulVec_c]
      have : i = 0 := Subsingleton.elim _ _
      subst this
      simp [ht0, Matrix.mulVec, dotProduct]
    | right i =>
      rw [cm_orth_mulVec_n]
      have h1 : (fun k => T (Fin.natAdd 1 k) (Fin.castAdd (2 + m') 0)) = s := rfl
      rw [h1, hSs]
      simp [Pi.single_apply, (cc_castAdd_ne_natAdd (0 : Fin 1) i).symm, Fin.natAdd_inj]
  have hβ : ‖G1' (Fin.castAdd m' 0) (Fin.castAdd m' 1)‖ = 1 := by
    rw [hG1', cm_quad_entry]
    have h0 : (fun a => S a (Fin.castAdd m' 0)) = Pi.single j' 1 := by
      ext x; rw [hS0 x, Pi.single_apply]
    have h1 : (fun b => S b (Fin.castAdd m' 1)) = s := funext hS1
    rw [h0, h1, single_dotProduct, one_mul]
    exact hj'
  exact hequiv.trans (c3_core hu ht hsymm h₂ hint hi₂ hpp' hβ _ hUT hcol hTeq)

/-- Lemma 4.2 (private copy used to build the Corollary). -/
private theorem cancel_unit_main {m : ℕ} {u : ℚ_[2]} (hu : ‖u‖ = 1) {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]}
    (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂) (hi₁ : IsClassIntegral G₁) (hi₂ : IsClassIntegral G₂)
    (hpp : IsProperlyPrimitive G₁ ↔ IsProperlyPrimitive G₂)
    (h : ZpEquiv (orthSumMat !![u] G₁) (orthSumMat !![u] G₂)) : ZpEquiv G₁ G₂ := by
  obtain ⟨T, hT, heq⟩ := exists_UM_of_zpEquiv h
  have hΦi := mn_Phi_int (u := u) hu.le hi₁
  by_cases hA : ‖T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ < 1
  · have h1 : ‖1 - T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1 := by
      have e : (1 : ℚ_[2]) = (1 - T (Fin.castAdd m 0) (Fin.castAdd m 0)) + T (Fin.castAdd m 0) (Fin.castAdd m 0) := by
        ring
      have hle : ‖(1 : ℚ_[2])‖ ≤ max ‖1 - T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ ‖T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ := by
        conv_lhs => rw [e]
        exact IsUltrametricDist.norm_add_le_max _ _
      rw [norm_one] at hle
      refine le_antisymm ((mn_sub_le _ _).trans ?_) ?_
      · simpa using hA.le
      · rcases le_max_iff.1 hle with h3 | h3
        · exact h3
        · exact absurd hA (not_lt.2 h3)
    have ha : ‖u - u * T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1 := by
      rw [show u - u * T (Fin.castAdd m 0) (Fin.castAdd m 0) = u * (1 - T (Fin.castAdd m 0) (Fin.castAdd m 0)) by ring,
        norm_mul, hu, h1, one_mul]
    refine refl_route hu h₁ hi₁ T hT heq (norm_ne_zero_iff.1 (by rw [ha]; exact one_ne_zero)) ?_
    intro x y
    rw [norm_div, ha, div_one, norm_mul]
    exact mul_le_one₀ (mn_w_int hT.1 x) (norm_nonneg _) (mn_mulVec_int hΦi (mn_w_int hT.1) y)
  · have ht1 : ‖T (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1 := le_antisymm (hT.1 _ _) (not_lt.1 hA)
    obtain ⟨ε, hε, hε2⟩ := mn_sign ht1
    obtain ⟨T', hT', heq', hc'⟩ := sign_norm T hT heq ε hε
    have ht' : T' (Fin.castAdd m 0) (Fin.castAdd m 0) = ε * T (Fin.castAdd m 0) (Fin.castAdd m 0) := hc' _
    have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
    have hnorm' : ‖T' (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1 := by
      rw [ht', norm_mul, hεn, ht1, one_mul]
    have ha : ‖u - u * T' (Fin.castAdd m 0) (Fin.castAdd m 0)‖ = 1 / 2 := by
      rw [show u - u * T' (Fin.castAdd m 0) (Fin.castAdd m 0) = u * (1 - ε * T (Fin.castAdd m 0) (Fin.castAdd m 0)) by
        rw [ht']; ring, norm_mul, hu, hε2, one_mul]
    by_cases hB : ∃ y, ‖(orthSumMat !![u] G₁ *ᵥ ((Pi.single (Fin.castAdd m 0) (1 : ℚ_[2]) : Fin (1 + m) → ℚ_[2]) -
        fun x => T' x (Fin.castAdd m 0))) y‖ = 1
    · exact c3_main hu h₁ h₂ hi₁ hi₂ hpp T' hT' heq' hnorm' hB
    · push_neg at hB
      refine refl_route hu h₁ hi₁ T' hT' heq' (norm_ne_zero_iff.1 (by rw [ha]; norm_num)) ?_
      intro x y
      have hy := mn_le_half (lt_of_le_of_ne (mn_mulVec_int hΦi (mn_w_int hT'.1) y) (hB y))
      rw [norm_div, norm_mul, ha, div_le_one (by norm_num)]
      calc _ ≤ (1 : ℝ) * (1 / 2) := mul_le_mul (mn_w_int hT'.1 x) hy (norm_nonneg _) zero_le_one
        _ = 1 / 2 := one_mul _

/-- Transport of `ℤ₂`-equivalence back along a dimension cast. -/
private theorem cb_uncast {n n' : ℕ} {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : n' = n)
    (hFG : ZpEquiv (F.submatrix (Fin.cast h) (Fin.cast h)) (G.submatrix (Fin.cast h) (Fin.cast h))) :
    ZpEquiv F G := by
  subst h
  simpa using hFG

/-- Reassociating an orthogonal sum of three blocks does not change `ℤ₂`-equivalence. -/
private theorem cb_assocE {a b c : ℕ} {P P' : Matrix (Fin a) (Fin a) ℚ_[2]} {Q Q' : Matrix (Fin b) (Fin b) ℚ_[2]}
    {R R' : Matrix (Fin c) (Fin c) ℚ_[2]} :
    ZpEquiv (orthSumMat (orthSumMat P Q) R) (orthSumMat (orthSumMat P' Q') R') ↔
      ZpEquiv (orthSumMat P (orthSumMat Q R)) (orthSumMat P' (orthSumMat Q' R')) := by
  have hh : a + (b + c) = a + b + c := by omega
  rw [dyadic_orthSumMat_assoc P Q R hh, dyadic_orthSumMat_assoc P' Q' R' hh]
  constructor
  · intro h
    exact dyadic_zpEquiv_cast hh h
  · intro h
    exact cb_uncast hh h

/-- An orthogonal sum of integral matrices is integral. -/
private theorem cb_integral {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℚ_[2]} {B : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hA : IsClassIntegral A) (hB : IsClassIntegral B) : IsClassIntegral (orthSumMat A B) := by
  intro i j
  induction i using Fin.addCases with
  | left i1 =>
    induction j using Fin.addCases with
    | left j1 => rw [dyadic_orthSumMat_cc]; exact hA _ _
    | right j2 => rw [dyadic_orthSumMat_cn]; simp
  | right i2 =>
    induction j using Fin.addCases with
    | left j1 => rw [dyadic_orthSumMat_nc]; simp
    | right j2 => rw [dyadic_orthSumMat_nn]; exact hB _ _

/-- An orthogonal sum of symmetric matrices is symmetric. -/
private theorem cb_symm {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℚ_[2]} {B : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hA : Aᵀ = A) (hB : Bᵀ = B) : (orthSumMat A B)ᵀ = orthSumMat A B := by
  rw [orthSumMat_transpose', hA, hB]

/-- A single unit entry is integral. -/
private theorem cb_integral_one {d : ℚ_[2]} (hd : ‖d‖ = 1) : IsClassIntegral !![d] := by
  intro i j
  fin_cases i
  fin_cases j
  simp [hd]

/-- `⟨d⟩ ⊥ G`-like sums with a unit diagonal entry in the first block are properly primitive. -/
private theorem cb_pp_left {a b : ℕ} {A : Matrix (Fin a) (Fin a) ℚ_[2]} {B : Matrix (Fin b) (Fin b) ℚ_[2]}
    (hA : IsClassIntegral A) (hB : IsClassIntegral B) (i : Fin a) (hi : ‖A i i‖ = 1) :
    IsProperlyPrimitive (orthSumMat A B) := by
  rw [pp_iff_diag]
  refine ⟨cb_integral hA hB, Fin.castAdd b i, ?_⟩
  rw [dyadic_orthSumMat_cc]
  exact hi

/-- Cancel three unit summands `⟨d₁⟩ ⊥ ⟨d₂⟩ ⊥ ⟨d₃⟩` from `ℤ₂`-equivalent forms, neither properly primitive. -/
private theorem cb_cancel3 {m : ℕ} {d₁ d₂ d₃ : ℚ_[2]} (h1 : ‖d₁‖ = 1) (h2 : ‖d₂‖ = 1) (h3 : ‖d₃‖ = 1)
    {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]} (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂) (hi₁ : IsClassIntegral G₁)
    (hi₂ : IsClassIntegral G₂) (hp₁ : ¬ IsProperlyPrimitive G₁) (hp₂ : ¬ IsProperlyPrimitive G₂)
    (h : ZpEquiv (orthSumMat (orthSumMat !![d₁] (orthSumMat !![d₂] !![d₃])) G₁)
      (orthSumMat (orthSumMat !![d₁] (orthSumMat !![d₂] !![d₃])) G₂)) : ZpEquiv G₁ G₂ := by
  have s1 : ∀ x : ℚ_[2], (!![x] : Matrix (Fin 1) (Fin 1) ℚ_[2])ᵀ = !![x] := by
    intro x; ext i j; fin_cases i; fin_cases j; rfl
  have i1 := cb_integral_one h1
  have i2 := cb_integral_one h2
  have i3 := cb_integral_one h3
  have hE : IsClassIntegral (orthSumMat !![d₂] !![d₃]) := cb_integral i2 i3
  have hEs : (orthSumMat !![d₂] !![d₃])ᵀ = orthSumMat !![d₂] !![d₃] := cb_symm (s1 _) (s1 _)
  -- reassociate
  have h' : ZpEquiv (orthSumMat !![d₁] (orthSumMat (orthSumMat !![d₂] !![d₃]) G₁))
      (orthSumMat !![d₁] (orthSumMat (orthSumMat !![d₂] !![d₃]) G₂)) :=
    cb_assocE.mp (by simpa using h)
  -- cancel d₁
  have c1 : ZpEquiv (orthSumMat (orthSumMat !![d₂] !![d₃]) G₁) (orthSumMat (orthSumMat !![d₂] !![d₃]) G₂) :=
    cancel_unit_main h1 (cb_symm hEs h₁) (cb_symm hEs h₂) (cb_integral hE hi₁) (cb_integral hE hi₂)
      (iff_of_true (cb_pp_left hE hi₁ (Fin.castAdd 1 0) (by rw [dyadic_orthSumMat_cc]; simpa using h2))
        (cb_pp_left hE hi₂ (Fin.castAdd 1 0) (by rw [dyadic_orthSumMat_cc]; simpa using h2))) h'
  have h'' : ZpEquiv (orthSumMat !![d₂] (orthSumMat !![d₃] G₁)) (orthSumMat !![d₂] (orthSumMat !![d₃] G₂)) :=
    cb_assocE.mp c1
  have c2 : ZpEquiv (orthSumMat !![d₃] G₁) (orthSumMat !![d₃] G₂) :=
    cancel_unit_main h2 (cb_symm (s1 _) h₁) (cb_symm (s1 _) h₂) (cb_integral i3 hi₁) (cb_integral i3 hi₂)
      (iff_of_true (cb_pp_left i3 hi₁ 0 (by simpa using h3)) (cb_pp_left i3 hi₂ 0 (by simpa using h3))) h''
  exact cancel_unit_main h3 h₁ h₂ hi₁ hi₂ (iff_of_false hp₁ hp₂) c2

/-- `⟨1⟩ ⊥ H` is the displayed `3 × 3` matrix (hyperbolic case). -/
private theorem cb_eq_H (a b c : ℚ_[2]) :
    orthSumMat !![a] !![0, b; c, 0] = !![a, 0, 0; 0, 0, b; 0, c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dyadic_orthSumMat_eq, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases]

/-- A diagonal `3 × 3` matrix as nested orthogonal sums. -/
private theorem cb_eq_diag (a b c : ℚ_[2]) :
    orthSumMat !![a] (orthSumMat !![b] !![c]) = !![a, 0, 0; 0, b, 0; 0, 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dyadic_orthSumMat_eq, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases]

private theorem cancel_binary_main {m : ℕ} {H : Matrix (Fin 2) (Fin 2) ℚ_[2]}
    (hH : H = !![0, 1; 1, 0] ∨ H = !![2, 1; 1, 2])
    {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]} (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂) (hi₁ : IsClassIntegral G₁)
    (hi₂ : IsClassIntegral G₂) (hp₁ : ¬ IsProperlyPrimitive G₁) (hp₂ : ¬ IsProperlyPrimitive G₂)
    (h : ZpEquiv (orthSumMat H G₁) (orthSumMat H G₂)) : ZpEquiv G₁ G₂ := by
  have h1 : ZpEquiv (orthSumMat !![(1 : ℚ_[2])] (orthSumMat H G₁)) (orthSumMat !![(1 : ℚ_[2])] (orthSumMat H G₂)) :=
    dyadic_zpEquiv_orthSum (ZpEquiv.refl _) h
  have h2 := cb_assocE.mpr h1
  have n1 : ‖(1 : ℚ_[2])‖ = 1 := norm_one
  have n3 : ‖(3 : ℚ_[2])‖ = 1 := by
    have := PadicInt.isUnit_iff.mp dyadic_isUnit_three
    rw [PadicInt.norm_def] at this
    exact this
  have nm : ‖(-1 : ℚ_[2])‖ = 1 := by simp
  have key : ∀ {d₁ d₂ d₃ : ℚ_[2]}, ‖d₁‖ = 1 → ‖d₂‖ = 1 → ‖d₃‖ = 1 →
      ZpEquiv (orthSumMat !![(1 : ℚ_[2])] H) (orthSumMat !![d₁] (orthSumMat !![d₂] !![d₃])) → ZpEquiv G₁ G₂ := by
    intro d₁ d₂ d₃ e1 e2 e3 hD
    have h3 : ZpEquiv (orthSumMat (orthSumMat !![d₁] (orthSumMat !![d₂] !![d₃])) G₁)
        (orthSumMat (orthSumMat !![d₁] (orthSumMat !![d₂] !![d₃])) G₂) :=
      (dyadic_zpEquiv_orthSum hD.symm (ZpEquiv.refl _)).trans
        (h2.trans (dyadic_zpEquiv_orthSum hD (ZpEquiv.refl _)))
    exact cb_cancel3 e1 e2 e3 h₁ h₂ hi₁ hi₂ hp₁ hp₂ h3
  rcases hH with rfl | rfl
  · refine key n1 n1 nm ?_
    rw [cb_eq_H, cb_eq_diag]
    simpa using equiv_4_7 n1
  · refine key n3 nm nm ?_
    have e : orthSumMat !![(1 : ℚ_[2])] !![2, 1; 1, 2] = !![1, 0, 0; 0, 2, 1; 0, 1, 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [dyadic_orthSumMat_eq, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases]
    rw [e, cb_eq_diag]
    simpa using equiv_4_8 n1

end QuadFormsKB.Cassels.Lemma42

namespace QuadFormsKB.Cassels

open Matrix

/-- **Cassels, Ch. 8, Lemma 4.2** ($p = 2$): *let $u$ be a $2$-adic unit and let $g_1(\vec x)$ and $g_2(\vec x)$ be
classically integral $2$-adic forms. Suppose that either (i) both $g_1$ and $g_2$ are properly primitive or (ii) neither
$g_1$ nor $g_2$ is properly primitive. If $\langle u\rangle + g_1 \sim \langle u\rangle + g_2$ (4.14) then
$g_1 \sim g_2$ (4.15).* Here $g_1, g_2$ are forms in $m$ variables with symmetric matrices $G_1, G_2$ over
$\mathbb Q_2$; the hypothesis "both or neither" is `IsProperlyPrimitive G₁ ↔ IsProperlyPrimitive G₂`. -/
@[kb "cassels1978" "Ch. 8, Lemma 4.2, pp. 120–122"]
theorem zpEquiv_cancel_unit {m : ℕ} {u : ℚ_[2]} (hu : ‖u‖ = 1) {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]}
    (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂) (hi₁ : IsClassIntegral G₁) (hi₂ : IsClassIntegral G₂)
    (hpp : IsProperlyPrimitive G₁ ↔ IsProperlyPrimitive G₂)
    (h : ZpEquiv (orthSumMat !![u] G₁) (orthSumMat !![u] G₂)) : ZpEquiv G₁ G₂ :=
  Lemma42.cancel_unit_main hu h₁ h₂ hi₁ hi₂ hpp h

/-- **Cassels, Ch. 8, Corollary to Lemma 4.2** ($p = 2$): *suppose that $g_1$ and $g_2$ are integral forms but not
properly primitive. If $h + g_1 \sim h + g_2$ (4.19) where $h = 2x_1x_2$ (4.20) or $h = 2x_1^{2} + 2x_1x_2 + 2x_2^{2}$
(4.21), then $g_1 \sim g_2$.* The matrix of $h$ is $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ or
$\begin{pmatrix} 2 & 1 \\ 1 & 2\end{pmatrix}$. -/
@[kb "cassels1978" "Ch. 8, Cor. to Lemma 4.2, p. 122 ((4.20), (4.21) reconstructed)"]
theorem zpEquiv_cancel_binary {m : ℕ} {H : Matrix (Fin 2) (Fin 2) ℚ_[2]} (hH : H = !![0, 1; 1, 0] ∨ H = !![2, 1; 1, 2])
    {G₁ G₂ : Matrix (Fin m) (Fin m) ℚ_[2]} (h₁ : G₁ᵀ = G₁) (h₂ : G₂ᵀ = G₂) (hi₁ : IsClassIntegral G₁)
    (hi₂ : IsClassIntegral G₂) (hp₁ : ¬ IsProperlyPrimitive G₁) (hp₂ : ¬ IsProperlyPrimitive G₂)
    (h : ZpEquiv (orthSumMat H G₁) (orthSumMat H G₂)) : ZpEquiv G₁ G₂ :=
  Lemma42.cancel_binary_main hH h₁ h₂ hi₁ hi₂ hp₁ hp₂ h

end QuadFormsKB.Cassels
