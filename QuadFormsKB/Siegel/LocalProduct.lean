/-
# Siegel's formula: the local product $\beta_\infty(m)\prod_p\beta_p(m)$

**Defines** Hanke's determinant $D = \det H/2^n$ (`gramDet`), the archimedean density $\beta_\infty(m)$ of
Hanke 2004 (5.5), p. 369 (`betaInf`, with $\omega_n$ = `unitBallVol`), the Euler factors $\beta_p(m)$ (`eulerFactor`,
the repo's `LocalDensity.localDensity`), the Euler product (`eulerProduct`, partial products `eulerPartialProd`,
natural-order value `IsEulerProductValue`) and the local side of Siegel's formula
$a_E^{\mathrm{loc}}(m) = \beta_\infty(m)\prod_p\beta_p(m)$ for $n \ge 4$ (`aE`), with $n = 3$ parameterized (`aEWith`).

**Proves** the explicit good-prime factor ($p \nmid 2\det(H)\,m$: $\beta_p(m) = 1 \pm p^{-\lfloor n/2\rfloor}$,
`localDensity_good`), hence **absolute convergence of $\prod_p\beta_p(m)$ for $n \ge 4$** (`multipliable_eulerFactor`)
and agreement with the natural-order limit (`isEulerProductValue_eulerProduct`); and the four-squares sanity
checks $D = 1$, $\beta_\infty(m) = \pi^2 m$ (`gramDet_Q4`, `betaInf_Q4`).

**Normalization (checked):** Hanke writes $Q(\vec{x}) = \sum_{i,j} c_{ij}x_ix_j$ with $(c_{ij})$ symmetric, so his $D$ is
the determinant of the Gram matrix $A = H/2$, not of the Hessian $H$ (`gramDet`). With this $D$, (5.5) gives
$\beta_\infty(m) = \pi^2 m$ for the sum of four squares, matching the AWS notes' (2.9).

**$n = 3$ (open):** the Euler product converges only conditionally; its value is taken as a
parameter.
-/
import QuadFormsKB.Siegel.Mass

open Matrix Filter Topology

namespace QuadFormsKB.Siegel

variable {n : ℕ}

open LocalDensity in
/-- **Odd $p \nmid \det H$: a $p$-unimodular diagonal form with the same counts, and its determinant**
(Hanke 2004, Lemma 2.1, p. 355, case $p \nmid 2$, with the determinant tracked): for $p$ an odd prime with
$p \nmid \det H$ there are $a_0, \dots, a_{n-1}$ with $p \nmid a_i$,
$r_{p^k}(Q, m) = r_{p^k}(\langle a_0, \dots, a_{n-1}\rangle, m)$ for all $k, m$, and $2^n\prod_i a_i = u^2\det H$ with
$p \nmid u$ ($u = \det U$ for the change of variables $U$). So $\prod_i a_i$ and Hanke's $D = \det H/2^n$ have the same
square class at $p$. -/
theorem exists_diag_unimodular_same_counts_det (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    ∃ a : Fin n → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) ∧
      (∀ k m, repCount Q p k m = repCount (QuadForm.diag a) p k m) ∧
      ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧ 2 ^ n * ∏ i, a i = u ^ 2 * Q.hessian.det := by
  have hpp : (p : ℕ).Prime := Fact.out
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  have hp2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this)
  have hpv : ∀ a : ℤ, a ≠ 0 → ∃ v : ℕ, ∃ w, a = (p : ℤ) ^ v * w ∧ ¬ (p : ℤ) ∣ w := by
    intro a ha
    obtain ⟨w, hw⟩ := padicValInt_dvd (p := p) a
    refine ⟨padicValInt p a, w, hw, ?_⟩
    rintro ⟨w', rfl⟩
    have h1 : (p : ℤ) ^ (padicValInt p a + 1) ∣ a := ⟨w', hw.trans (by ring)⟩
    rcases (padicValInt_dvd_iff (p := p) (padicValInt p a + 1) a).1 h1 with h | h
    · exact ha h
    · omega
  obtain ⟨U, hU, D, hD⟩ := exists_conj_diagonal_aux hpZ hp2 hpv _ Q.hessian Finset.univ rfl
    (hessian_isSymm Q) (fun k l _ h => by simp at h)
  have hval : ∀ x : Fin n → ℤ, 2 * Q.eval (U *ᵥ x) = ∑ i, D i * x i * x i := by
    intro x
    have hc : (U *ᵥ x) ⬝ᵥ (Q.hessian *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ * Q.hessian * U) *ᵥ x) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Uᵀ, vecMul_transpose]
    rw [two_mul_eval_eq_hessian, hc, hD]
    simp [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  set a : Fin n → ℤ := fun i => Q.eval (U *ᵥ Pi.single i 1) with ha
  have hDa : ∀ i, D i = 2 * a i := by
    intro i
    rw [ha]; dsimp only
    rw [hval]
    simp [Pi.single_apply]
  have hdiag : ∀ x : Fin n → ℤ, (QuadForm.diag a).eval x = ∑ i, a i * x i * x i := by
    intro x
    simp only [QuadForm.diag, QuadForm.evalIn, diagonal_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  have hQ' : ∀ x : Fin n → ℤ, (QuadForm.diag a).eval x = Q.eval (U *ᵥ x) := by
    intro x
    have h2 := hval x
    rw [hdiag]
    have : (2 : ℤ) * ∑ i, a i * x i * x i = 2 * Q.eval (U *ᵥ x) := by
      rw [h2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hDa]; ring
    exact (mul_left_cancel₀ two_ne_zero this)
  have hdetD : (Uᵀ * Q.hessian * U).det = U.det * Q.hessian.det * U.det := by
    rw [det_mul, det_mul, det_transpose]
  rw [hD, det_diagonal] at hdetD
  refine ⟨a, fun i hai => ?_, fun k m => (repCount_eq_of_unimodular Q _ U p hU hQ' k m).symm,
    U.det, hU, ?_⟩
  swap
  · have : ∏ i, D i = 2 ^ n * ∏ i, a i := by
      rw [Finset.prod_congr rfl fun i _ => hDa i, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [← this, hdetD]; ring
  have hdvd : (p : ℤ) ∣ ∏ i, D i :=
    (hai.mul_left 2).trans ((hDa i).symm ▸ Finset.dvd_prod_of_mem D (Finset.mem_univ i))
  rw [hdetD] at hdvd
  rcases hpZ.dvd_or_dvd hdvd with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · exact hU h
    · exact hdet h
  · exact hU h

open LocalDensity in
/-- **Odd $p \nmid \det H$: a $p$-unimodular diagonal form with the same counts** (Hanke 2004, Lemma 2.1,
p. 355, case $p \nmid 2$, with the determinant tracked): for $p$ an odd prime with $p \nmid \det H$ there are
$a_0, \dots, a_{n-1}$ with $p \nmid a_i$ and $r_{p^k}(Q, m) = r_{p^k}(\langle a_0, \dots, a_{n-1}\rangle, m)$ for all $k, m$.
Same proof as `LocalDensity.exists_diag_same_counts`; the determinant relation is in
`exists_diag_unimodular_same_counts_det`. -/
@[kb "hanke2004" "Lemma 2.1, p. 355"]
theorem exists_diag_unimodular_same_counts (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) :
    ∃ a : Fin n → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) ∧
      ∀ k m, LocalDensity.repCount Q p k m = LocalDensity.repCount (QuadForm.diag a) p k m :=
  let ⟨a, h1, h2, _⟩ := exists_diag_unimodular_same_counts_det Q p hp hdet
  ⟨a, h1, h2⟩

open LocalDensity in
/-- **The local density at a good prime** (Hanke 2004, Table 1 / Remark 3.4.1(a), p. 361–363): for $p$ an odd
prime with $p \nmid \det H$ and $p \nmid m$, and $n \ge 1$,
$$\beta_p(m) = 1 - \frac{c}{p^{n/2}} \ (n \text{ even}), \qquad \beta_p(m) = 1 + \frac{c}{p^{(n-1)/2}} \ (n \text{ odd}),$$
for some sign $c = \pm 1$ (a Legendre symbol; `n / 2` is natural-number division, so it is $(n-1)/2$ for odd
$n$). Here $\beta_p$ is the repo's `LocalDensity.localDensity` ((5.1)–(5.2), p. 368). -/
@[kb "hanke2004" "Table 1, p. 363; Remark 3.4.1(a), p. 361"]
theorem localDensity_good (Q : QuadForm ℤ n) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    ∃ c : ℝ, c ^ 2 = 1 ∧
      localDensity Q p m = if Even n then 1 - c / (p : ℝ) ^ (n / 2) else 1 + c / (p : ℝ) ^ (n / 2) := by
  obtain ⟨a, ha, hcount⟩ := exists_diag_unimodular_same_counts Q p hp hdet
  have e1 : localDensity Q p m = localDensity (QuadForm.diag a) p m :=
    (localDensity_congr_of_repCount Q _ p hcount m).1
  rw [e1, localDensity_unit a p hp ha m hm]
  have hcd := card_diag_mod_p a p hp ha hn m hm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rcases Nat.even_or_odd n with he | ho
  · set L := legendreSym p ((-1) ^ (n / 2) * ∏ i, a i)
    have hL : ((L : ℤ) : ℝ) ^ 2 = 1 := by
      have : (((-1) ^ (n / 2) * ∏ i, a i : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        exact mul_ne_zero (by exact_mod_cast LocalDensity.neg_one_pow_ne_zero_zmod p _)
          (by exact_mod_cast LocalDensity.prod_ne_zero_zmod a p ha)
      exact_mod_cast legendreSym.sq_one p this
    refine ⟨L, hL, ?_⟩
    simp only [he, ↓reduceIte]
    have hr : (repCount (QuadForm.diag a) p 1 m : ℝ) = (p : ℝ) ^ (n - 1) - L * (p : ℝ) ^ (n / 2 - 1) := by
      exact_mod_cast (hcd.1 he).2
    rw [hr]
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 2 := ⟨n / 2 - 1, by obtain ⟨j, hj⟩ := he; omega⟩
    have e2 : (2 * k + 2) / 2 = k + 1 := by omega
    have e3 : 2 * k + 2 - 1 = (k + 1) + k := by omega
    rw [e2, e3, Nat.add_sub_cancel, pow_add]
    field_simp
  · set L := legendreSym p ((-1) ^ ((n - 1) / 2) * (∏ i, a i) * m)
    have hL : ((L : ℤ) : ℝ) ^ 2 = 1 := by
      have : (((-1) ^ ((n - 1) / 2) * (∏ i, a i) * m : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
        · exact_mod_cast LocalDensity.neg_one_pow_ne_zero_zmod p _
        · exact_mod_cast LocalDensity.prod_ne_zero_zmod a p ha
        · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hm
      exact_mod_cast legendreSym.sq_one p this
    refine ⟨L, hL, ?_⟩
    simp only [Nat.not_even_iff_odd.mpr ho, ↓reduceIte]
    have hr : (repCount (QuadForm.diag a) p 1 m : ℝ) = (p : ℝ) ^ (n - 1) + L * (p : ℝ) ^ ((n - 1) / 2) := by
      exact_mod_cast (hcd.2 ho).2
    rw [hr]
    obtain ⟨k, rfl⟩ := ho
    have e2 : (2 * k + 1) / 2 = k := by omega
    have e3 : (2 * k + 1 - 1) / 2 = k := by omega
    have e4 : 2 * k + 1 - 1 = k + k := by omega
    rw [e2, e3, e4, pow_add]
    field_simp

/-- **Good-prime bound:** $|\beta_p(m) - 1| \le p^{-\lfloor n/2 \rfloor}$ for odd $p \nmid \det H \cdot m$. For $n \ge 4$ this is
$\le p^{-2}$ (absolutely convergent Euler product); for $n = 3$ it is only $p^{-1}$. -/
theorem abs_localDensity_sub_one_le (Q : QuadForm ℤ n) (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) (m : ℤ) (hm : ¬ (p : ℤ) ∣ m) :
    |LocalDensity.localDensity Q p m - 1| ≤ 1 / (p : ℝ) ^ (n / 2) := by
  obtain ⟨c, hc, h⟩ := localDensity_good Q hn p hp hdet m hm
  have hc' : |c| = 1 := by
    have := abs_sq c ▸ congrArg abs hc
    nlinarith [abs_nonneg c, sq_abs c]
  have hp0 : (0 : ℝ) < (p : ℝ) ^ (n / 2) := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  rw [h]
  split_ifs
  · rw [show 1 - c / (p : ℝ) ^ (n / 2) - 1 = -(c / (p : ℝ) ^ (n / 2)) by ring, abs_neg, abs_div,
      hc', abs_of_pos hp0]
  · rw [show 1 + c / (p : ℝ) ^ (n / 2) - 1 = c / (p : ℝ) ^ (n / 2) by ring, abs_div, hc',
      abs_of_pos hp0]


/-! ### The Euler product -/

/-- **The Euler factor at $p$:** $\beta_p(m)$ (`LocalDensity.localDensity`, Hanke 2004 (5.1)–(5.2), p. 368, with the
corrected exponent; $\mathrm{Vol}(\mathbb{Z}_p) = 1$), indexed by the primes `AWS.PrimeIdx` $= \{p : p \text{ prime}\}$ as in
`AWS.FourSquaresInputs`. -/
noncomputable def eulerFactor (Q : QuadForm ℤ n) (m : ℤ) (p : AWS.PrimeIdx) : ℝ :=
  LocalDensity.localDensity Q p m

/-- Only finitely many primes divide a nonzero integer. -/
theorem finite_primes_dvd {N : ℤ} (hN : N ≠ 0) : {p : AWS.PrimeIdx | (p : ℤ) ∣ N}.Finite := by
  refine (Set.finite_le_nat N.natAbs).preimage Subtype.val_injective.injOn |>.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hp ⊢
  have : (p : ℕ) ∣ N.natAbs := Int.natCast_dvd.mp hp
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hN) this

/-- **All but finitely many Euler factors are $p^{-\lfloor n/2\rfloor}$-close to $1$:** for $Q$ nondegenerate, $n \ge 1$,
$m \ne 0$, the bound `abs_localDensity_sub_one_le` holds for every $p \nmid 2 \det(H)\, m$. -/
theorem eventually_abs_eulerFactor_sub_one_le (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    {m : ℤ} (hm : m ≠ 0) :
    ∀ᶠ p : AWS.PrimeIdx in cofinite, |eulerFactor Q m p - 1| ≤ 1 / ((p : ℕ) : ℝ) ^ (n / 2) := by
  have hN : 2 * Q.hessian.det * m ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hQ) hm
  refine Filter.eventually_cofinite.mpr ((finite_primes_dvd hN).subset fun p hp => ?_)
  simp only [Set.mem_ofPred_eq] at hp ⊢
  by_contra h
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  have hpZ : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
  have h2 : ¬ ((p : ℕ) : ℤ) ∣ 2 * Q.hessian.det := fun h' => h (h'.mul_right m)
  have hp2 : (p : ℕ) ≠ 2 := by
    intro e; apply h2; rw [e]; exact dvd_mul_right _ _
  have hdet : ¬ ((p : ℕ) : ℤ) ∣ Q.hessian.det := fun h' => h2 (h'.mul_left 2)
  have hpm : ¬ ((p : ℕ) : ℤ) ∣ m := fun h' => h (h'.mul_left _)
  exact hp (abs_localDensity_sub_one_le Q hn p hp2 hdet m hpm)

/-- $\sum_p p^{-2} < \infty$ (Mathlib's `Nat.Primes.summable_rpow`). -/
theorem summable_inv_sq_primes : Summable fun p : AWS.PrimeIdx => 1 / ((p : ℕ) : ℝ) ^ 2 := by
  have h := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
  refine h.congr fun p => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  norm_cast

/-- **The Euler product converges absolutely for $n \ge 4$** (Hanke 2004, (5.3), p. 368, $n \ge 4$): for $Q$
nondegenerate and $m \ne 0$, $\prod_p \beta_p(m)$ is unconditionally convergent in $\mathbb{R}$ (`Multipliable`), since
$\sum_p |\beta_p(m) - 1| < \infty$. -/
@[kb "hanke2004" "(5.3), p. 368 (n ≥ 4)"]
theorem multipliable_eulerFactor (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {m : ℤ}
    (hm : m ≠ 0) : Multipliable (eulerFactor Q m) := by
  have hs : Summable fun p => eulerFactor Q m p - 1 := by
    refine Summable.of_norm_bounded_eventually summable_inv_sq_primes ?_
    filter_upwards [eventually_abs_eulerFactor_sub_one_le Q hQ (by omega) hm] with p hp
    rw [Real.norm_eq_abs]
    refine hp.trans ?_
    have h1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    have : ((p : ℕ) : ℝ) ^ 2 ≤ ((p : ℕ) : ℝ) ^ (n / 2) := pow_le_pow_right₀ h1 (by omega)
    exact one_div_le_one_div_of_le (by positivity) this
  have := Real.multipliable_one_add_of_summable hs
  simpa using this

/-- The primes $p \le X$. -/
def primesUpTo (X : ℕ) : Finset AWS.PrimeIdx := (Finset.range (X + 1)).subtype Nat.Prime

/-- $\{p \le X\}$ exhausts the primes as $X \to \infty$. -/
theorem tendsto_primesUpTo : Tendsto primesUpTo atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun X Y hXY p hp => ?_) fun p => ⟨p, ?_⟩
  · simp only [primesUpTo, Finset.mem_subtype, Finset.mem_range] at hp ⊢; omega
  · simp [primesUpTo]

/-- **Partial Euler products** $\prod_{p \le X} \beta_p(m)$, in the natural order of the primes. -/
noncomputable def eulerPartialProd (Q : QuadForm ℤ n) (m : ℤ) (X : ℕ) : ℝ :=
  ∏ p ∈ primesUpTo X, eulerFactor Q m p

/-- **$P$ is the value of the Euler product in the natural order:** $\prod_{p \le X} \beta_p(m) \to P$ as $X \to \infty$.

*Role:* for $n \ge 4$ the product converges absolutely and its value `eulerProduct` satisfies this
(`isEulerProductValue_eulerProduct`). For $n = 3$ the product converges at best conditionally and **the
convention is undecided**; this predicate is one candidate (Siegel's own definition takes the
limit in the natural order [unverified]), the other is $L(1, \chi) \cdot (\text{finite product})$. Batch 1 leaves
$n = 3$ parameterized: see `aEWith`. -/
def IsEulerProductValue (Q : QuadForm ℤ n) (m : ℤ) (P : ℝ) : Prop :=
  Tendsto (eulerPartialProd Q m) atTop (𝓝 P)

/-- An unconditional product is also the limit of the partial products in the natural order. -/
theorem isEulerProductValue_of_hasProd {Q : QuadForm ℤ n} {m : ℤ} {P : ℝ}
    (h : HasProd (eulerFactor Q m) P) : IsEulerProductValue Q m P :=
  (show Tendsto (fun s : Finset AWS.PrimeIdx => ∏ p ∈ s, eulerFactor Q m p) atTop (𝓝 P) from h).comp
    tendsto_primesUpTo

/-- **The Euler product** $\prod_p \beta_p(m)$ as Mathlib's unconditional product `tprod`.

*Use only for $n \ge 4$* (then it converges, `hasProd_eulerProduct`). For $n = 3$ the product is in general not
unconditionally convergent and `tprod` returns its junk value $1$; use `aEWith` with an explicit value. -/
noncomputable def eulerProduct (Q : QuadForm ℤ n) (m : ℤ) : ℝ := ∏' p, eulerFactor Q m p

/-- For $n \ge 4$, $Q$ nondegenerate, $m \ne 0$: $\prod_p \beta_p(m)$ converges to `eulerProduct Q m`. -/
theorem hasProd_eulerProduct (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n) {m : ℤ}
    (hm : m ≠ 0) : HasProd (eulerFactor Q m) (eulerProduct Q m) :=
  (multipliable_eulerFactor Q hQ hn hm).hasProd

/-- For $n \ge 4$ the two candidate meanings of $\prod_p \beta_p(m)$ agree: `eulerProduct` is the natural-order limit. -/
theorem isEulerProductValue_eulerProduct (Q : QuadForm ℤ n) (hQ : Q.Nondegenerate) (hn : 4 ≤ n)
    {m : ℤ} (hm : m ≠ 0) : IsEulerProductValue Q m (eulerProduct Q m) :=
  isEulerProductValue_of_hasProd (hasProd_eulerProduct Q hQ hn hm)

/-! ### The archimedean density -/

/-- **$\omega_n$, the volume of the unit ball** $\{\vec{x} \in \mathbb{R}^n : \sum_i x_i^2 < 1\}$ (Lebesgue measure on
`EuclideanSpace ℝ (Fin n)`); Hanke's "volume of the $n$-sphere $\sum x_i^2 \le 1$" in (5.5). Equals
$\pi^{n/2}/\Gamma(n/2 + 1)$ (`unitBallVol_eq`). -/
noncomputable def unitBallVol (n : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- $\omega_n = \sqrt{\pi}^{\,n}/\Gamma(n/2 + 1)$ for $n \ge 1$ (Mathlib's `EuclideanSpace.volume_ball`). -/
theorem unitBallVol_eq (hn : 1 ≤ n) :
    unitBallVol n = Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [unitBallVol, EuclideanSpace.volume_ball, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal]
  positivity

/-- **Hanke's determinant $D$** (Hanke 2004, p. 355): the determinant of the symmetric **Gram** matrix
$A = (c_{ij})$ with $Q(\vec{x}) = \sum_{i,j} c_{ij} x_i x_j = \vec{x}^{\mathsf T}A\vec{x}$. In this repo's convention
($Q(\vec{x}) = \sum_{i \le j} c_{ij} x_i x_j$, Hessian $H = C + C^{\mathsf T}$, $Q(\vec{x}) = \tfrac12\vec{x}^{\mathsf T}H\vec{x}$) this is
$$D = \det(H/2) = \det H / 2^n \in \mathbb{Q}.$$
Example: $D = 1$ for $x_0^2 + \dots + x_3^2$ (`gramDet_Q4`). -/
@[kb "hanke2004" "§2, D_Q = det(Q_p), p. 355"]
noncomputable def gramDet (Q : QuadForm ℤ n) : ℝ := (Q.hessian.det : ℝ) / 2 ^ n

/-- **The archimedean local density $\beta_\infty(m)$** (Hanke 2004, (5.5), p. 369, citing Siegel, Hilfssatz 26):
$$\beta_\infty(m) = \frac{n\,\omega_n\,D^{-1/2}}{2}\, m^{(n-2)/2},$$
with $\omega_n$ = `unitBallVol n` and $D$ = `gramDet Q` $= \det H/2^n$ (see there for the normalization). For
positive definite $Q$ this is $\frac{d}{dt}\mathrm{Vol}\{\vec{x} \in \mathbb{R}^n : Q(\vec{x}) \le t\}$ at $t = m$, i.e. Siegel's
(5.1) at $v = \infty$: proved as `tendsto_volume_shell_div` (`Siegel/Archimedean.lean`).

*Edge cases:* real powers (`Real.rpow`); meaningful for $D > 0$, $m \ge 0$. Example: $\pi^2 m$ for the sum of four
squares (`betaInf_Q4`, the AWS notes' (2.9)). -/
@[kb "hanke2004" "(5.5), p. 369"]
noncomputable def betaInf (Q : QuadForm ℤ n) (m : ℝ) : ℝ :=
  n * unitBallVol n * gramDet Q ^ (-(1 / 2 : ℝ)) / 2 * m ^ (((n : ℝ) - 2) / 2)

/-- **The local product with a given Euler-product value $P$:** $\beta_\infty(m)\cdot P$.

*Role:* for $n = 3$ the meaning of $\prod_p \beta_p(m)$ is not fixed here, so statements for
$n = 3$ take the value $P$ as an explicit parameter (with a hypothesis such as `IsEulerProductValue Q m P`). For
$n \ge 4$, use `aE` $=$ `aEWith Q m (eulerProduct Q m)`. -/
noncomputable def aEWith (Q : QuadForm ℤ n) (m : ℤ) (P : ℝ) : ℝ := betaInf Q m * P

/-- **The local product (Siegel's right-hand side) for $n \ge 4$** (Hanke 2004, (5.3), p. 368):
$$a_E^{\mathrm{loc}}(m) = \beta_\infty(m) \prod_p \beta_p(m),$$
the product converging absolutely (`multipliable_eulerFactor`). Siegel's formula will state
`genusRepAvg Q m = aE Q m`. Not to be used for $n = 3$ (see `eulerProduct`, `aEWith`).

*Warning: meaningful only for $n \ge 4$.* For $n = 3$ the factors $\beta_p(m) = 1 + \chi_m(p)/p$ are not
unconditionally multipliable, so `tprod` returns its junk value $1$ (unless some $\beta_p(m) = 0$) and `aE Q m` is then
$\beta_\infty(m)$ alone. In rank $3$ use `aEWith Q m (eulerProductReg3 Q m)` (the regularized value,
`Tamagawa/RatBridge3.lean`). -/
@[kb "hanke2004" "(5.3), p. 368"]
noncomputable def aE (Q : QuadForm ℤ n) (m : ℤ) : ℝ := aEWith Q m (eulerProduct Q m)

/-! ### Sanity checks: the sum of four squares -/

/-- $D = 1$ for $x_0^2+x_1^2+x_2^2+x_3^2$ ($H = 2I_4$, $\det H = 16 = 2^4$). -/
theorem gramDet_Q4 : gramDet AWS.Q4 = 1 := by
  have : AWS.Q4.hessian = Matrix.diagonal fun _ => 2 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [AWS.Q4, QuadForm.diag, QuadForm.hessian]
    · simp [AWS.Q4, QuadForm.diag, QuadForm.hessian, Matrix.diagonal, h, Ne.symm h]
  rw [gramDet, this, det_diagonal]
  norm_num

/-- **The AWS notes' (2.9):** $\beta_\infty(m) = \pi^2 m$ for $x_0^2 + x_1^2 + x_2^2 + x_3^2$ ($n = 4$, $D = 1$,
$\omega_4 = \pi^2/2$). Checks the normalization of (5.5) against `AWS.betaInf_calc`. -/
@[kb "hanke2011aws" "§2.7.2, (2.9), p. 37"]
theorem betaInf_Q4 (m : ℝ) : betaInf AWS.Q4 m = Real.pi ^ 2 * m := by
  rw [betaInf, gramDet_Q4, Real.one_rpow, unitBallVol_eq (by norm_num)]
  have hG : Real.Gamma ((4 : ℕ) / 2 + 1 : ℝ) = 2 := by
    rw [show ((4 : ℕ) / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hG]
  have hs : Real.sqrt Real.pi ^ 4 = Real.pi ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt Real.pi_pos.le]
  rw [hs, show (((4 : ℕ) : ℝ) - 2) / 2 = 1 by norm_num, Real.rpow_one]
  push_cast
  ring

end QuadFormsKB.Siegel
