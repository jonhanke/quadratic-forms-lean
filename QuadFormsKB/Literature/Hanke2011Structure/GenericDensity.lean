/-
# Hanke 2011, Lemma 3.6: bounds for the generic Euler factors ($n$ even)

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §3.

In the proof of Lemma 3.6 (p. 13) the inverse generic local density at a prime $\mathfrak p \nmid 2$ outside the support of
$S$, for $n = 2r$ even, is
$$\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1} = \Bigl[(1 - \chi\,q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})\Bigr]^{-1},
  \qquad \chi \in \{\pm1\},$$
($q$ the size of the residue field; the sign is $\chi = \chi((-1)^r\det_H)$, see `lemma_3_6_density_even` and
`chiDisc_even`), and the paper states the bounds
$$1 \le \prod_{\mathfrak p\notin T}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}
  \le \zeta^T_F(2)\zeta^T_F(4)\cdots\zeta^T_F(n-2)\,\frac{\zeta^T_F(n/2)}{\zeta^T_F(n)}.$$

* `generic_even_one_le`: the lower bound holds factor by factor for $n \ge 4$ ($r \ge 2$). (For $n = 2$ it fails:
  $(1 + q^{-1})^{-1} < 1$; the paper treats $n = 2$ separately.)
* `generic_even_le`: the correct upper bound, factor by factor: $\beta^{-1} \le (1 - q^{-r})^{-1}\prod_{i=1}^{r-1}(1-q^{-2i})^{-1}$,
  the local factor of $\zeta(2)\cdots\zeta(n-2)\,\zeta(n/2)$.
* *Erratum* (proposed by the formalization), `lemma_3_6_upper_bound_false_local`,
  `lemma_3_6_upper_bound_false`: the printed upper bound is false. The local factor of $\zeta(n/2)/\zeta(n)$ is
  $(1 - q^{-n})/(1 - q^{-r}) = 1 + q^{-r}$, which is smaller than $(1 - q^{-r})^{-1}$, the value of the last factor of
  $\beta^{-1}$ when $\chi = +1$. Counterexample: $n = 4$ and $S$ the trivial squareclass (e.g. the form
  $Q = x_0^2+x_1^2+x_2^2+x_3^2$, $\det_H Q = 16$): at every $\mathfrak p \nmid 2$,
  $\beta^{-1} = (1 - q^{-2})^{-2} > (1-q^{-2})^{-1}(1 + q^{-2})$, so the product over the primes outside $T$ is
  $\zeta^T_F(2)^2 > \zeta^T_F(2)^2/\zeta^T_F(4)$. The correct bound is $\zeta^T_F(2)\cdots\zeta^T_F(n-2)\,\zeta^T_F(n/2)$,
  which still converges for $n \ge 4$, so the convergence conclusion of Lemma 3.6 is unaffected.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Hanke2011Structure.LocalGenera
import QuadFormsKB.Literature.Hanke2011Structure.BinarySeries

namespace QuadFormsKB.Hanke2011Structure

open Finset

/-- The generic local density for $n = 2r$ at a prime with residue field of size $q$ and sign $\chi$:
$(1 - \chi q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})$ (index shift: the product runs over `i ∈ range (r - 1)` with
exponent `2 * (i + 1)`). -/
noncomputable def genericEven (q : ℝ) (r : ℕ) (χ : ℝ) : ℝ :=
  (1 - χ * (q ^ r)⁻¹) * ∏ i ∈ range (r - 1), (1 - (q ^ (2 * (i + 1)))⁻¹)

private theorem inv_pow_lt_one {q : ℝ} (hq : 1 < q) {k : ℕ} (hk : 1 ≤ k) : (q ^ k)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))

private theorem inv_pow_pos {q : ℝ} (hq : 1 < q) (k : ℕ) : 0 < (q ^ k)⁻¹ :=
  inv_pos.mpr (pow_pos (by linarith) k)

private theorem prod_pos' {q : ℝ} (hq : 1 < q) (m : ℕ) :
    0 < ∏ i ∈ range m, (1 - (q ^ (2 * (i + 1)))⁻¹) :=
  prod_pos fun i _ => by have := inv_pow_lt_one hq (k := 2 * (i + 1)) (by omega); linarith

private theorem prod_le_one' {q : ℝ} (hq : 1 < q) (m : ℕ) :
    ∏ i ∈ range m, (1 - (q ^ (2 * (i + 1)))⁻¹) ≤ 1 :=
  prod_le_one₀ (fun i _ => by have := inv_pow_lt_one hq (k := 2 * (i + 1)) (by omega); linarith)
    (fun i _ => by have := inv_pow_pos hq (2 * (i + 1)); linarith)

theorem genericEven_pos {q : ℝ} (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1) :
    0 < genericEven q r χ := by
  unfold genericEven
  refine mul_pos ?_ (prod_pos' hq _)
  have := inv_pow_lt_one hq hr
  have := inv_pow_pos hq r
  rcases hχ with rfl | rfl <;> linarith

/-- **Lemma 3.6, lower bound, factor by factor** (Hanke 2011, p. 13; $n = 2r \ge 4$): for $q > 1$ and $\chi = \pm1$,
$1 \le \bigl[(1 - \chi q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})\bigr]^{-1}$. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (lower bound, n ≥ 4)"]
theorem generic_even_one_le {q : ℝ} (hq : 1 < q) {r : ℕ} (hr : 2 ≤ r) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1) :
    1 ≤ (genericEven q r χ)⁻¹ := by
  rw [one_le_inv₀ (genericEven_pos hq (by omega) hχ)]
  unfold genericEven
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, prod_range_succ']
  simp only [zero_add, mul_one]
  have hP := prod_le_one' hq m
  have hP0 := (prod_pos' (q := q) hq m).le
  have hP' : ∏ i ∈ range m, (1 - (q ^ (2 * (i + 1 + 1)))⁻¹) ≤ 1 := by
    refine prod_le_one₀ (fun i _ => ?_) (fun i _ => ?_)
    · have := inv_pow_lt_one hq (k := 2 * (i + 1 + 1)) (by omega); linarith
    · have := inv_pow_pos hq (2 * (i + 1 + 1)); linarith
  have hP0' : 0 ≤ ∏ i ∈ range m, (1 - (q ^ (2 * (i + 1 + 1)))⁻¹) := by
    refine prod_nonneg fun i _ => ?_
    have := inv_pow_lt_one hq (k := 2 * (i + 1 + 1)) (by omega); linarith
  -- `(1 - χ q^{-r})(1 - q^{-2}) ≤ (1 + q^{-2})(1 - q^{-2}) ≤ 1`, since `q^{-r} ≤ q^{-2}`
  have hq0 : 0 < q := by linarith
  have hr2 : (q ^ (m + 2))⁻¹ ≤ (q ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos hq0 _) (pow_le_pow_right₀ hq.le (by omega))
  have hx := inv_pow_pos hq (m + 2)
  have hy := inv_pow_lt_one hq (k := 2) (by omega)
  have hy0 := inv_pow_pos hq 2
  have h1 : (1 - χ * (q ^ (m + 2))⁻¹) * (1 - (q ^ (2 * (0 + 1)))⁻¹) ≤ 1 := by
    rw [show 2 * (0 + 1) = 2 by rfl]
    have hχx : -(q ^ (m + 2))⁻¹ ≤ -χ * (q ^ (m + 2))⁻¹ ∧ -χ * (q ^ (m + 2))⁻¹ ≤ (q ^ (m + 2))⁻¹ := by
      rcases hχ with rfl | rfl <;> constructor <;> linarith
    nlinarith [mul_nonneg hy0.le hy0.le]
  have h0 : 0 ≤ (1 - χ * (q ^ (m + 2))⁻¹) * (1 - (q ^ (2 * (0 + 1)))⁻¹) := by
    have : (q ^ (m + 2))⁻¹ < 1 := inv_pow_lt_one hq (by omega)
    rw [show 2 * (0 + 1) = 2 by rfl]
    apply mul_nonneg
    · rcases hχ with rfl | rfl <;> linarith
    · linarith
  calc _
      = ((1 - χ * (q ^ (m + 2))⁻¹) * (1 - (q ^ (2 * (0 + 1)))⁻¹)) *
          ∏ i ∈ range m, (1 - (q ^ (2 * (i + 1 + 1)))⁻¹) := by ring
    _ ≤ 1 * 1 := mul_le_mul h1 hP' hP0' zero_le_one
    _ = 1 := one_mul 1

/-- **Lemma 3.6, the correct upper bound, factor by factor** (Hanke 2011, p. 13; $n = 2r \ge 2$): for $q > 1$ and
$\chi = \pm1$,
$$\Bigl[(1 - \chi q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})\Bigr]^{-1} \le (1 - q^{-r})^{-1}\prod_{i=1}^{r-1}(1 - q^{-2i})^{-1},$$
the local factor of $\zeta(2)\zeta(4)\cdots\zeta(n-2)\,\zeta(n/2)$. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (upper bound, corrected)"]
theorem generic_even_le {q : ℝ} (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1) :
    (genericEven q r χ)⁻¹ ≤ (genericEven q r 1)⁻¹ := by
  rw [inv_le_inv₀ (genericEven_pos hq hr hχ) (genericEven_pos hq hr (Or.inl rfl))]
  unfold genericEven
  refine mul_le_mul_of_nonneg_right ?_ (prod_pos' hq _).le
  have := inv_pow_pos hq r
  rcases hχ with rfl | rfl <;> linarith

/-- **The printed upper bound of Lemma 3.6 fails at every prime, factor by factor** (*Erratum*, proposed by the
formalization). For $q > 1$ and $r \ge 1$, with $\chi = +1$ (the sign of every $\mathfrak p \nmid 2$ outside
$T$ when $(-1)^r S$ is the trivial squareclass), the inverse generic density exceeds the local factor of the paper's
bound $\zeta(2)\cdots\zeta(n-2)\,\zeta(n/2)/\zeta(n)$:
$$\prod_{i=1}^{r-1}(1 - q^{-2i})^{-1}\cdot\frac{1 - q^{-2r}}{1 - q^{-r}}
  < \Bigl[(1 - q^{-r})\prod_{i=1}^{r-1}(1 - q^{-2i})\Bigr]^{-1}.$$ -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (upper bound, printed, false)"]
theorem lemma_3_6_upper_bound_false_local {q : ℝ} (hq : 1 < q) {r : ℕ} (hr : 1 ≤ r) :
    (∏ i ∈ range (r - 1), (1 - (q ^ (2 * (i + 1)))⁻¹))⁻¹ * ((1 - (q ^ (2 * r))⁻¹) / (1 - (q ^ r)⁻¹)) <
      (genericEven q r 1)⁻¹ := by
  have hP := prod_pos' hq (r - 1)
  have hx := inv_pow_pos hq r
  have hx1 := inv_pow_lt_one hq hr
  have hsq : (q ^ (2 * r))⁻¹ = (q ^ r)⁻¹ ^ 2 := by rw [pow_mul', inv_pow]
  have hfac : (1 - (q ^ (2 * r))⁻¹) / (1 - (q ^ r)⁻¹) = 1 + (q ^ r)⁻¹ := by
    rw [hsq, div_eq_iff (by linarith)]; ring
  unfold genericEven
  rw [hfac, one_mul, mul_inv, mul_comm ((1 - (q ^ r)⁻¹)⁻¹)]
  refine mul_lt_mul_of_pos_left ?_ (inv_pos.mpr hP)
  set x := (q ^ r)⁻¹
  rw [lt_inv_comm₀ (by linarith) (by linarith), inv_eq_one_div, lt_div_iff₀ (by linarith)]
  nlinarith

/-- **The printed upper bound of Lemma 3.6 fails for products over primes** (*Erratum*, proposed by the formalization).
For $n = 4$ and a nonempty finite set $P$ of primes (residue field sizes $q_{\mathfrak p} > 1$) at which
the sign is $+1$ (e.g. $S$ trivial, every $\mathfrak p \nmid 2$), the product of the inverse generic densities
$\prod_{\mathfrak p\in P}(1 - q_{\mathfrak p}^{-2})^{-2}$ is strictly larger than the corresponding partial product of the paper's
bound $\zeta(2)\zeta(2)/\zeta(4)$, namely $\prod_{\mathfrak p\in P}(1 - q_{\mathfrak p}^{-2})^{-1}(1 - q_{\mathfrak p}^{-4})/(1 - q_{\mathfrak p}^{-2})$.
(Letting $P$ exhaust the primes outside $T$, the two sides tend to $\zeta^T_F(2)^2$ and $\zeta^T_F(2)^2/\zeta^T_F(4)$.) -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (upper bound, printed, false)"]
theorem lemma_3_6_upper_bound_false {ι : Type*} (P : Finset ι) (hP : P.Nonempty) (q : ι → ℝ)
    (hq : ∀ i ∈ P, 1 < q i) :
    ∏ i ∈ P, (1 - (q i ^ 2)⁻¹)⁻¹ * ((1 - (q i ^ 4)⁻¹) / (1 - (q i ^ 2)⁻¹)) <
      ∏ i ∈ P, (genericEven (q i) 2 1)⁻¹ := by
  refine prod_lt_prod_of_nonempty₀ (fun i hi => ?_) (fun i hi => ?_) hP
  · have hx := inv_pow_lt_one (hq i hi) (k := 2) (by omega)
    have hx4 := inv_pow_lt_one (hq i hi) (k := 4) (by omega)
    exact mul_pos (inv_pos.mpr (by linarith)) (div_pos (by linarith) (by linarith))
  · have h := lemma_3_6_upper_bound_false_local (hq i hi) (r := 2) (by omega)
    simpa using h

/-- **Lemma 3.6, the generic product for $n$ odd, over $\mathbb Q$** (Hanke 2011, p. 13). For $n = 2r+1$ the inverse generic
density at a prime $p \nmid 2$ outside the support of $S$ is $\prod_{i=1}^r(1-p^{-2i})^{-1}$ (`lemma_3_6_density_odd`), and
the product of these Euler factors over all primes converges to $\zeta(2)\zeta(4)\cdots\zeta(n-1)$ (Riemann zeta function;
index shift: `i ∈ range r` stands for $2(i+1)$). Removing the finitely many factors at the primes of $T$ gives the
paper's $\zeta^T(2)\cdots\zeta^T(n-1)$, so the generic product converges for $n$ odd. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (n odd, F = ℚ)"]
theorem lemma_3_6_generic_odd_rat (r : ℕ) :
    HasProd (fun p : Nat.Primes => ∏ i ∈ range r, (1 - (p : ℂ) ^ (-(2 * ((i : ℂ) + 1))))⁻¹)
      (∏ i ∈ range r, riemannZeta (2 * ((i : ℂ) + 1))) := by
  refine hasProd_prod fun i _ => riemannZeta_eulerProduct_hasProd ?_
  have : (2 * ((i : ℂ) + 1)).re = 2 * ((i : ℝ) + 1) := by simp
  rw [this]
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

section Form

open QuadFormsKB.LocalDensity

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (IsLocalRing.ResidueField R)] [DecidableEq (IsLocalRing.ResidueField R)]
  {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2)
include hπ h2

/-- **The counterexample form for the Lemma 3.6 upper bound** (*Erratum*, proposed by the formalization).
Over a DVR $R$ with finite residue field of size $q$ and $\pi \nmid 2$, the form
$Q = \langle 1,1,1,1\rangle = x_0^2+x_1^2+x_2^2+x_3^2$ (unimodular, $\det_H Q = 16$) has, in the paper's normalization
$\beta = \tfrac12\alpha_\pi(Q,Q)$, $\beta^{-1} = (1 - q^{-2})^{-2}$, which is strictly larger than
$(1 - q^{-2})^{-1}\,(1 - q^{-4})/(1 - q^{-2})$, the local factor at $\mathfrak p$ of the paper's bound
$\zeta(2)\,\zeta(2)/\zeta(4)$ for $n = 4$. -/
@[kb "hanke2011structure" "Lemma 3.6, proof, p. 13 (upper bound, printed, false)"]
theorem lemma_3_6_upper_bound_counterexample :
    (DVR.localDensityForm (QuadForm.diag (![1, 1, 1, 1] : Fin 4 → R))
        (QuadForm.diag (![1, 1, 1, 1] : Fin 4 → R)) π / 2)⁻¹ = (genericEven (DVR.q R) 2 1)⁻¹ ∧
      (1 - ((DVR.q R : ℝ) ^ 2)⁻¹)⁻¹ * ((1 - ((DVR.q R : ℝ) ^ 4)⁻¹) / (1 - ((DVR.q R : ℝ) ^ 2)⁻¹)) <
        (genericEven (DVR.q R) 2 1)⁻¹ := by
  have hq : (1 : ℝ) < DVR.q R := by exact_mod_cast DVR.one_lt_q
  refine ⟨?_, by simpa using lemma_3_6_upper_bound_false_local hq (r := 2) (by omega)⟩
  have h2F : (2 : IsLocalRing.ResidueField R) ≠ 0 := by
    have := (DVR.dvr_isUnit_of_not_dvd hπ h2).map (IsLocalRing.residue R)
    rw [map_ofNat] at this
    exact this.ne_zero
  have hdet : ¬ π ∣ (QuadForm.diag (![1, 1, 1, 1] : Fin 4 → R)).hessian.det := by
    rw [DVR.det_hessian_diag, show ∏ i, (![1, 1, 1, 1] : Fin 4 → R) i = 1 by simp [Fin.prod_univ_four], mul_one]
    exact DVR.dvr_not_dvd_of_isUnit hπ ((DVR.dvr_isUnit_of_not_dvd hπ h2).pow 4)
  have h := lemma_3_6_density_even hπ h2 2 (by omega) (QuadForm.diag (![1, 1, 1, 1] : Fin 4 → R)) hdet
  have hchi := chiDisc_even hπ h2 2 (QuadForm.diag (![1, 1, 1, 1] : Fin 4 → R))
  rw [DVR.det_hessian_diag] at hchi
  have hp : ∏ i, (![1, 1, 1, 1] : Fin 4 → R) i = 1 := by simp [Fin.prod_univ_four]
  simp only [hp, mul_one, map_pow, map_ofNat] at hchi
  have hsq : quadraticChar (IsLocalRing.ResidueField R) ((-1) ^ 2 * (2 : IsLocalRing.ResidueField R) ^ (2 * 2)) =
      1 := by
    rw [show ((-1) ^ 2 * (2 : IsLocalRing.ResidueField R) ^ (2 * 2)) = (2 ^ 2) ^ 2 by ring]
    exact quadraticChar_sq_one' (pow_ne_zero _ h2F)
  rw [hsq] at hchi
  rw [h, hchi]
  simp [genericEven]

/-- **The first row of the table in the proof of Theorem 7.6** (Hanke 2011, p. 30; $\mathfrak p \nmid 2$, $\nu = 0$, Jordan type
$I_2$). For a binary form $Q$ over $R$ ($\pi \nmid 2$) with unit Hessian determinant $u = \det_H Q$, the local density
in the paper's normalization is $\beta_{Q}(Q) = \tfrac12\alpha_\pi(Q,Q) = \gamma_{\mathfrak p}(u) = 1 - \chi_u(\mathfrak p)/q$, with
$\chi_u(\mathfrak p) = \left(\frac{-u}{\mathfrak p}\right)$ (`gammaP`); so the normalized density $\gamma_{\mathfrak p}(u)\,\beta^{-1}$ of the
table is $1$. This ties the table values used in `BinarySeries.lean` (and Lemma 7.10) to the repository's local
densities in this case. -/
@[kb "hanke2011structure" "Thm. 7.6, proof, table, p. 30 (p ∤ 2, ν = 0)"]
theorem theorem_7_6_table_unimodular (Q : QuadForm R 2) (hdet : ¬ π ∣ Q.hessian.det) :
    DVR.localDensityForm Q Q π / 2 =
      gammaP ((quadraticChar (IsLocalRing.ResidueField R) (-IsLocalRing.residue R Q.hessian.det) : ℤ) : ℝ)
        (DVR.q R) := by
  have h := lemma_3_6_density_even hπ h2 1 le_rfl Q hdet
  have hchi := chiDisc_even hπ h2 1 Q
  simp only [pow_one, neg_one_mul] at hchi
  rw [h, hchi, gammaP]
  simp [div_eq_mul_inv]

/-- **Remark 4.14, nondyadic part** (Hanke 2011, p. 20): for $n = 2r+1$ odd and $\mathfrak p \nmid 2$, the generic local density
$\beta_{n,\mathfrak p}(\widetilde S_{\mathfrak p})$ does not depend on the normalized squareclass $\widetilde S_{\mathfrak p}$: any two unimodular forms
$Q, Q'$ in $2r+1$ variables have the same local density ($\prod_{i=1}^r(1-q^{-2i})$ in the paper's normalization,
`lemma_3_6_density_odd`), "essentially because there is only one orthogonal group over each finite field". (At the
dyadic primes the remark rests on Gan–Hanke–Yu and is not formalized.) -/
@[kb "hanke2011structure" "Rem. 4.14, p. 20 (p ∤ 2)"]
theorem remark_4_14_nondyadic (r : ℕ) (Q Q' : QuadForm R (2 * r + 1)) (hQ : ¬ π ∣ Q.hessian.det)
    (hQ' : ¬ π ∣ Q'.hessian.det) : DVR.localDensityForm Q Q π = DVR.localDensityForm Q' Q' π := by
  have h := lemma_3_6_density_odd hπ h2 r Q hQ
  have h' := lemma_3_6_density_odd hπ h2 r Q' hQ'
  linarith

end Form

end QuadFormsKB.Hanke2011Structure
