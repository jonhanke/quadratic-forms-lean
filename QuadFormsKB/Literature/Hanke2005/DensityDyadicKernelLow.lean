/-
# Hanke 2005, (3.3) at dyadic places: the density of $\mathbb H^k\perp N$ from its two lowest levels

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

The named input `DyadicKernelDensity F` (Shimura, Thm 8.6(3), Prop. 3.9: the self-density of $\mathbb H^k\perp N$ at a
dyadic place, $N$ a maximal lattice on an anisotropic space of dimension $r$, $n = r + 2k \ge 3$) is reduced to its
**two lowest levels** $n \le 6$ (`DyadicKernelDensityLow F`): for each $r$ these are $k_0$ and $k_0+1$, where $k_0$ is the
least $k$ with $r + 2k \ge 3$ ($n \in \{3,5\}$ for $r\in\{1,3\}$, $n\in\{4,6\}$ for $r\in\{2,4\}$).

*Proof of the reduction* (`dyadicKernelDensity_of_low`), purely local:
* `localDensityForm_hypSum_succ`: $\beta(\mathbb H^{k+1}\perp N) = \rho_k(Z)\,\beta(\mathbb H^k\perp N)$ with
  $\rho_k(Z) = (q^{k+1}-1)(q^{r+k}+Z)/q^{r+2k+1}$ and $Z$ the number of zeros of $N \bmod \pi$ (the frame lemma
  `localDensityForm_hypFrame`, the count of hyperbolic pairs `localDensityForm_hypExt_hyperbolic`, and, because $N$ is
  anisotropic, Hensel's lemma `resRadZero_eq_resZero_of_aniso`: every residue zero of $N$ lies in the radical).
* `xiShimura_succ`: Shimura's $\xi$ obeys the same recursion with $Z = Z^*$: $Z^* = 1$ ($r = 1$), $q$ ($r = 2$ ramified),
  $q^2$ ($r = 2$ unramified, $r = 3$, $r = 4$).
* The two lowest levels give $\rho_{k_0}(Z) = \rho_{k_0}(Z^*)$, so $Z = Z^*$ ($\rho_{k_0}$ is injective in $Z$), and the
  formula propagates to every $k \ge k_0$.
* $r = 0$ is excluded by $[\widetilde\Lambda:\Lambda]\ne1$, and $r \ge 5$ is impossible (every form of rank $5$ over $F_\mathfrak p$ is
  isotropic, O'Meara 63:19, `LocalRankFive.isotropic_five`).

So `ShimuraMaximalDensityRest F` (hence Theorem 5.1) rests on `DyadicKernelDensityLow F`
(`shimuraMaximalDensityRest_of_low`).
-/
import QuadFormsKB.Literature.Hanke2005.DensityDyadicKernelShape
import QuadFormsKB.Literature.Hanke2011Structure.DyadicExistence
import QuadFormsKB.LocalDensity.HypKernel
import QuadFormsKB.Tamagawa.LocalRankFive
import QuadFormsKB.Tamagawa.AlphaLawSplit

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.LocalDensity.DVR QuadFormsKB.LocalDensity.HypFrame QuadFormsKB.Tamagawa
  QuadFormsKB.Lattices QuadForm

/-! ### Iterating the hyperbolic step over a complete discrete valuation ring -/

section Iterate

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {r : ℕ}

theorem hypSum_succ (N : QuadForm R r) (k : ℕ) : hypSum N (k + 1) = hypExt (hypSum N k) := rfl

theorem hypSum_det (N : QuadForm R r) : ∀ k, (hypSum N k).hessian.det = (-1) ^ k * N.hessian.det
  | 0 => by simp [hypSum]
  | k + 1 => by
    rw [hypSum_succ, hypExt, Hanke2011Structure.hessian_orthSum_det, hypSum_det N k, hyperbolic_hessian_det]
    ring

theorem hypSum_nondegenerate {N : QuadForm R r} (hN : N.Nondegenerate) (k : ℕ) : (hypSum N k).Nondegenerate := by
  rw [QuadForm.Nondegenerate, hypSum_det]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hN

theorem resRadZero_hypSum [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (N : QuadForm R r) :
    ∀ k, resRadZero π (hypSum N k) = resRadZero π N
  | 0 => rfl
  | k + 1 => by rw [hypSum_succ, resRadZero_hypExt hπ, resRadZero_hypSum hπ N k]

/-- **The residue zeros of $\mathbb H^k\perp N$:** $qZ_k = q^{r+2k} + q^k(qZ_0 - q^r)$. -/
theorem resZero_hypSum [Finite (IsLocalRing.ResidueField R)] {π : R} (hπ : Irreducible π) (N : QuadForm R r) :
    ∀ k, (q R : ℝ) * resZero π (hypSum N k) =
      (q R : ℝ) ^ (r + 2 * k) + (q R : ℝ) ^ k * ((q R : ℝ) * resZero π N - (q R : ℝ) ^ r)
  | 0 => by simp [hypSum]
  | k + 1 => by
    have h := resZero_hypExt hπ (hypSum N k)
    rw [← hypSum_succ] at h
    have e := congrArg (Nat.cast (R := ℝ)) h
    push_cast at e
    have ih := resZero_hypSum hπ N k
    have hx : (q R : ℝ) ^ (r + 2 * (k + 1)) = (q R : ℝ) ^ (r + 2 * k) * (q R : ℝ) * (q R : ℝ) := by
      rw [show r + 2 * (k + 1) = r + 2 * k + 2 by ring, pow_add]; ring
    rw [hx, pow_succ]
    linear_combination (q R : ℝ) * e + (q R : ℝ) * ih

/-- $\rho_k(Z) = (q^{k+1}-1)(q^{r+k}+Z)/q^{r+2k+1}$, the ratio $\beta(\mathbb H^{k+1}\perp N)/\beta(\mathbb H^k\perp N)$. -/
def rho (q : ℝ) (r : ℕ) (Z : ℝ) (k : ℕ) : ℝ := (q ^ (k + 1) - 1) * (q ^ (r + k) + Z) / q ^ (r + 2 * k + 1)

/-- **The density recursion for $\mathbb H^k\perp N$, $N$ anisotropic:** $\beta(\mathbb H^{k+1}\perp N) = \rho_k(Z)\,\beta(\mathbb H^k\perp N)$,
$Z$ the number of zeros of $N \bmod \pi$. -/
@[kb "kitaoka1993" "§5.6 [unverified] (α(H^{k+1} ⊥ N) / α(H^k ⊥ N) for N anisotropic, from residue counts)"]
theorem localDensityForm_hypSum_succ [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π) (N : QuadForm R r)
    (hN : N.Nondegenerate) (han : ∀ x, N.eval x = 0 → x = 0) (k : ℕ) :
    localDensityForm (hypSum N (k + 1)) (hypSum N (k + 1)) π =
      rho (q R) r (resZero π N) k * localDensityForm (hypSum N k) (hypSum N k) π := by
  rw [hypSum_succ, localDensityForm_hypExt_step hπ _ (hypSum_nondegenerate hN k) (hypSum_nondegenerate hN (k + 1)),
    resRadZero_hypSum hπ, resRadZero_eq_resZero_of_aniso hπ N han]
  congr 1
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hZ := resZero_hypSum hπ N k
  unfold rho
  rw [div_eq_div_iff (pow_pos hq _).ne' (pow_pos hq _).ne']
  rw [show r + 2 * k + 1 = r + 2 * k + 1 from rfl]
  have e1 : (q R : ℝ) ^ (r + 2 * k) = (q R : ℝ) ^ r * (q R : ℝ) ^ k * (q R : ℝ) ^ k := by
    rw [← pow_add, ← pow_add]; ring_nf
  have e2 : (q R : ℝ) ^ (r + k) = (q R : ℝ) ^ r * (q R : ℝ) ^ k := pow_add _ _ _
  rw [e1] at hZ ⊢
  rw [e2, pow_succ, pow_succ]
  linear_combination ((q R : ℝ) ^ r * (q R : ℝ) ^ k * (q R : ℝ) ^ k * (q R : ℝ)) * hZ

end Iterate

/-! ### Shimura's $\xi$ obeys the same recursion -/

section Xi

theorem rpow_neg_nat' {q : ℝ} (hq : 0 < q) (n : ℕ) : q ^ (-(n : ℝ)) = (q ^ n)⁻¹ := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]

theorem ppow_succ' {q : ℝ} (hq : 0 < q) (k : ℕ) : ppow q (k + 1) = ppow q k * (1 - (q ^ (2 * k + 2))⁻¹) := by
  unfold ppow
  rw [Finset.prod_range_succ, show (-(2 * ((k : ℝ) + 1))) = -(((2 * k + 2 : ℕ) : ℝ)) by push_cast; ring,
    rpow_neg_nat' hq]

/-- Shimura's residue zero count $Z^*$ for the anisotropic kernel: $1$ for $r = 1$, $q$ for $r = 2$ ramified, $q^2$ otherwise. -/
def zStar (q : ℝ) (r : ℕ) (ram : Prop) : ℝ :=
  open Classical in if r = 1 then 1 else if r = 2 ∧ ram then q else q ^ 2

open Classical in
/-- **Shimura's $\xi$ obeys the density recursion:** for $1 \le r \le 4$ and $[\widetilde\Lambda:\Lambda]\ne1$,
$\xi(n + 2) = \rho_k(Z^*)\,\xi(n)$, $n = r + 2k$. -/
theorem xiShimura_succ {q : ℝ} (hq : 1 < q) {r : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (ram : Prop) (k : ℕ) :
    xiShimura q (r + 2 * (k + 1)) r ram False = rho q r (zStar q r ram) k * xiShimura q (r + 2 * k) r ram False := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqk : ∀ j : ℕ, 0 < q ^ j := fun j => pow_pos hq0 j
  have hlt : ∀ j : ℕ, 1 ≤ j → (q ^ j)⁻¹ < 1 := fun j hj => inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  interval_cases r
  · -- r = 1: ξ = ppow q m, m = k
    simp only [xiShimura, zStar, if_true]
    rw [show (1 + 2 * (k + 1)) / 2 = k + 1 by omega, show (1 + 2 * k) / 2 = k by omega, ppow_succ' hq0]
    unfold rho
    field_simp
    ring
  · -- r = 2
    by_cases hram : ram
    · simp only [xiShimura, zStar, hram, if_true, and_self, if_false, show (2 : ℕ) ≠ 1 by decide]
      rw [show (2 + 2 * (k + 1)) / 2 - 1 = k + 1 by omega, show (2 + 2 * k) / 2 - 1 = k by omega, ppow_succ' hq0]
      unfold rho
      field_simp
      ring
    · simp only [xiShimura, zStar, hram, if_false, and_false, show (2 : ℕ) ≠ 1 by decide]
      rw [show (2 + 2 * (k + 1)) / 2 - 1 = k + 1 by omega, show (2 + 2 * k) / 2 - 1 = k by omega, ppow_succ' hq0,
        show (1 - (((2 + 2 * (k + 1)) / 2 : ℕ) : ℝ)) = -((k + 1 : ℕ) : ℝ) by
          rw [show (2 + 2 * (k + 1)) / 2 = k + 2 by omega]; push_cast; ring,
        show (1 - (((2 + 2 * k) / 2 : ℕ) : ℝ)) = -((k : ℕ) : ℝ) by
          rw [show (2 + 2 * k) / 2 = k + 1 by omega]; push_cast; ring,
        rpow_neg_nat' hq0, rpow_neg_nat' hq0]
      have h1 : (1 : ℝ) + (q ^ (k + 1))⁻¹ ≠ 0 := by have := hqk (k + 1); positivity
      have h2 : (1 : ℝ) + (q ^ k)⁻¹ ≠ 0 := by have := hqk k; positivity
      unfold rho
      field_simp
      ring
  · -- r = 3: ξ = 2(1+q) ppow(m-1), m = k + 1
    simp only [xiShimura, zStar, show (3 : ℕ) ≠ 1 by decide, show ¬ ((3 : ℕ) = 2 ∧ ram) by simp, if_false]
    rw [show (3 + 2 * (k + 1)) / 2 - 1 = k + 1 by omega, show (3 + 2 * k) / 2 - 1 = k by omega, ppow_succ' hq0]
    unfold rho
    field_simp
    ring
  · -- r = 4: ξ = 2(1+q)(1-q^{1-m})⁻¹ ppow(m-1), m = k + 2
    simp only [xiShimura, zStar, show (4 : ℕ) ≠ 1 by decide, show ¬ ((4 : ℕ) = 2 ∧ ram) by simp, if_false]
    rw [show (4 + 2 * (k + 1)) / 2 - 1 = k + 2 by omega, show (4 + 2 * k) / 2 - 1 = k + 1 by omega, ppow_succ' hq0,
      show (1 - (((4 + 2 * (k + 1)) / 2 : ℕ) : ℝ)) = -((k + 2 : ℕ) : ℝ) by
        rw [show (4 + 2 * (k + 1)) / 2 = k + 3 by omega]; push_cast; ring,
      show (1 - (((4 + 2 * k) / 2 : ℕ) : ℝ)) = -((k + 1 : ℕ) : ℝ) by
        rw [show (4 + 2 * k) / 2 = k + 2 by omega]; push_cast; ring,
      rpow_neg_nat' hq0, rpow_neg_nat' hq0]
    have h1 : (1 : ℝ) - (q ^ (k + 2))⁻¹ ≠ 0 := (sub_pos.mpr (hlt _ (by omega))).ne'
    have h2 : (1 : ℝ) - (q ^ (k + 1))⁻¹ ≠ 0 := (sub_pos.mpr (hlt _ (by omega))).ne'
    have h3 : q ^ (k + 2) - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hq (by omega))).ne'
    have h4 : q ^ (k + 1) - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hq (by omega))).ne'
    unfold rho
    field_simp
    ring

/-- $\rho_k$ is injective in $Z$ ($q > 1$). -/
theorem rho_injective {q : ℝ} (hq : 1 < q) (r : ℕ) {Z Z' : ℝ} (k : ℕ) (h : rho q r Z k = rho q r Z' k) : Z = Z' := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have h1 : q ^ (k + 1) - 1 ≠ 0 := (sub_pos.mpr (one_lt_pow₀ hq (by omega))).ne'
  unfold rho at h
  rw [div_left_inj' (pow_pos hq0 _).ne', mul_right_inj' h1] at h
  linarith

/-- **Propagation:** two sequences with the same recursion from level $k_0$ on that agree at $k_0$ agree from $k_0$ on. -/
theorem eq_of_rec {β S ρ : ℕ → ℝ} (k₀ : ℕ) (hβ : ∀ k, β (k + 1) = ρ k * β k) (hS : ∀ k, S (k + 1) = ρ k * S k)
    (h0 : β k₀ = S k₀) : ∀ k, k₀ ≤ k → β k = S k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h0
  | succ k _ ih => rw [hβ, hS, ih]

end Xi

/-! ### Transport of the data of $\mathbb H^k\perp N$ to $N$ -/

section Transport

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- Multiplying by a nonzero square does not change `IsUnramSqrt`. -/
theorem isUnramSqrt_mul_sq (x d : v.adicCompletion F) (hd : d ≠ 0) :
    IsUnramSqrt v (x * d ^ 2) ↔ IsUnramSqrt v x := by
  constructor
  · rintro ⟨c, hc, y, hy, e⟩
    exact ⟨d * c, mul_ne_zero hd hc, y, hy, by rw [← e]; ring⟩
  · rintro ⟨c, hc, y, hy, e⟩
    exact ⟨c / d, div_ne_zero hc hd, y, hy, by rw [← e]; field_simp⟩

variable {r : ℕ} (N : QuadForm (v.adicCompletionIntegers F) r)

/-- $D_0 = \det H_N$ in $F_\mathfrak p$. -/
abbrev dN : v.adicCompletion F := ((N.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)

theorem det_hypSum_coe (k : ℕ) :
    (((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) = (-1) ^ k * dN v N := by
  rw [hypSum_det]; push_cast; rfl

theorem norm_det_hypSum (k : ℕ) :
    ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = ‖dN v N‖ := by
  rw [det_hypSum_coe, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem two_ne_zero_Fv : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero

theorem ram_hypSum (k : ℕ) :
    IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
        ((((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k))) ↔
      IsUnramSqrt v ((-1) ^ (r / 2) * (dN v N / 2 ^ r)) := by
  have h2 := two_ne_zero_Fv v
  have e : (-1 : v.adicCompletion F) ^ ((r + 2 * k) / 2) *
      ((((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k)) =
      ((-1) ^ (r / 2) * (dN v N / 2 ^ r)) * ((2 : v.adicCompletion F) ^ k)⁻¹ ^ 2 := by
    rw [det_hypSum_coe, show (r + 2 * k) / 2 = r / 2 + k by omega, pow_add, pow_add]
    field_simp
    rw [show ((-1 : v.adicCompletion F) ^ k) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; simp]
    ring
  rw [e, isUnramSqrt_mul_sq v _ _ (inv_ne_zero (pow_ne_zero _ h2))]

theorem detHyp_hypSum (k : ℕ) :
    (∃ c : v.adicCompletion F, c ≠ 0 ∧
      ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k) * c ^ 2‖ = 1) ↔
    (∃ c : v.adicCompletion F, c ≠ 0 ∧ ‖dN v N / 2 ^ r * c ^ 2‖ = 1) := by
  have h2 := two_ne_zero_Fv v
  have e : ∀ c : v.adicCompletion F,
      ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k) * c ^ 2‖ =
        ‖dN v N / 2 ^ r * (c / 2 ^ k) ^ 2‖ := by
    intro c
    rw [det_hypSum_coe]
    simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [pow_add, pow_mul]
    have : ‖(2 : v.adicCompletion F)‖ ≠ 0 := norm_ne_zero_iff.mpr h2
    field_simp
    ring
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c / 2 ^ k, div_ne_zero hc (pow_ne_zero _ h2), by rw [← e]; exact h⟩
  · rintro ⟨c, hc, h⟩
    refine ⟨c * 2 ^ k, mul_ne_zero hc (pow_ne_zero _ h2), ?_⟩
    rw [e, mul_div_assoc, div_self (pow_ne_zero _ h2), mul_one]; exact h

end Transport


/-! ### Anisotropic forms over $F_\mathfrak p$ have rank at most $4$ -/

section RankFour

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- **An anisotropic form over $F_\mathfrak p$ has rank $\le 4$** (O'Meara 63:19, via `LocalRankFive.isotropic_five` applied
to the restriction to the first five variables; an anisotropic form is nondegenerate). -/
@[kb "omeara1963" "§63C, 63:19, p. 170"]
theorem rank_le_four_of_aniso {r : ℕ} (P : QuadForm (v.adicCompletion F) r) (han : ∀ y, P.eval y = 0 → y = 0) :
    r ≤ 4 := by
  by_contra hr
  push_neg at hr
  set E : Matrix (Fin r) (Fin 5) (v.adicCompletion F) := Matrix.of fun i j => if i.val = j.val then 1 else 0 with hE
  have hEy : ∀ (y : Fin 5 → v.adicCompletion F) (j : Fin 5), (E *ᵥ y) ⟨j.val, by omega⟩ = y j := by
    intro y j
    simp only [hE, mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single j (fun b _ hb => if_neg (fun h => hb (Fin.ext h).symm)) (by simp)]
    simp
  set P5 := P.compMat E with hP5
  have han5 : ∀ y, P5.eval y = 0 → y = 0 := by
    intro y hy
    rw [hP5, eval_compMat] at hy
    have h0 := han _ hy
    funext j
    rw [← hEy y j, h0]; rfl
  have hnd : P5.Nondegenerate := by
    by_contra h
    rw [QuadForm.Nondegenerate, not_not] at h
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    apply hy0
    apply han5
    have h2 := dotProduct_hessian_self P5 y
    rw [hy, dotProduct_zero] at h2
    have : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
    exact (mul_eq_zero.mp h2.symm).resolve_left this
  obtain ⟨x, hx0, hx⟩ := LocalRankFive.isotropic_five v P5 hnd
  exact hx0 (han5 x (by simpa using hx))

end RankFour


/-! ### Kernels of rank one -/

section RankOne

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem diag_of_rank_one {A : Type*} [CommRing A] (N : QuadForm A 1) : N = QuadForm.diag fun _ => N.coeff 0 0 := by
  ext i j
  fin_cases i; fin_cases j
  simp [QuadForm.diag]

/-- **A rank-one kernel is a unit times $x^2$:** if $N = \langle\varepsilon\rangle$ has the extension property (so
$\mathrm{ord}\,\varepsilon\le1$, `nu_le_one`) and satisfies Shimura's determinant hypothesis (so $\mathrm{ord}\,\varepsilon$ is even),
then $\varepsilon$ is a unit. -/
theorem isUnit_of_rank_one (N : QuadForm (v.adicCompletionIntegers F) 1) (hN : N.Nondegenerate)
    (hmax : MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))))
    (hc : ∃ c : v.adicCompletion F, c ≠ 0 ∧ ‖dN v N / 2 ^ 1 * c ^ 2‖ = 1) : IsUnit (N.coeff 0 0) := by
  set ε := N.coeff 0 0 with hεdef
  have hdiag := diag_of_rank_one N
  have hdet : N.hessian.det = 2 * ε := by
    rw [hdiag]; simp [QuadForm.hessian, QuadForm.diag, Matrix.det_unique]; ring
  have hε0 : ε ≠ 0 := by
    intro h; apply hN; rw [hdet, h, mul_zero]
  have hπ := NF.irreducible_π v
  obtain ⟨a, ha, ha'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ hε0
  obtain ⟨w, hw⟩ := ha
  have hwu : IsUnit w := by
    refine DVR.dvr_isUnit_of_not_dvd hπ fun h => ha' ?_
    rw [hw, pow_succ]; exact mul_dvd_mul_left _ h
  have ha1 : a ≤ 1 := by
    refine nu_le_one v (fun _ => a) (fun _ => w) ?_ (0 : Fin 1)
    have e : (QuadForm.diag fun _ : Fin 1 => NF.π v ^ a * w) = N := by rw [hdiag, ← hw]
    rw [e]; exact hmax
  -- `a` is even
  obtain ⟨c, hc0, hc⟩ := hc
  have hεn : ‖((ε : v.adicCompletionIntegers F) : v.adicCompletion F)‖ = ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ a)⁻¹ :=
    Tamagawa.norm_coe_of_pow_dvd v ⟨w, hw⟩ ha'
  have h2 : (2 : v.adicCompletion F) ≠ 0 := two_ne_zero
  have hD : dN v N = 2 * ((ε : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [dN, hdet]; push_cast; rfl
  have hc' : ‖((ε : v.adicCompletionIntegers F) : v.adicCompletion F)‖ * ‖c‖ ^ 2 = 1 := by
    rw [← hc, hD, pow_one, show (2 : v.adicCompletion F) * ((ε : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 =
      ((ε : v.adicCompletionIntegers F) : v.adicCompletion F) by field_simp, norm_mul, norm_pow]
  have hQ : ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    rw [NF.q_completion]
  have hQ1 : 1 < (Ideal.absNorm v.asIdeal : ℝ) := by rw [← hQ, DensitySD.q_eq v]; exact one_lt_normQ v
  have hQ0 : 0 < (Ideal.absNorm v.asIdeal : ℝ) := lt_trans zero_lt_one hQ1
  rw [hεn, hQ, LocalZeta.norm_eq_absNorm_pow v hc0] at hc'
  set z := WithZero.log (Valued.v c)
  have hz : (Ideal.absNorm v.asIdeal : ℝ) ^ (2 * z) = (Ideal.absNorm v.asIdeal : ℝ) ^ (a : ℤ) := by
    rw [zpow_natCast, two_mul, zpow_add₀ hQ0.ne']
    have hpa : (Ideal.absNorm v.asIdeal : ℝ) ^ a ≠ 0 := pow_ne_zero _ hQ0.ne'
    field_simp at hc'
    linear_combination hc'
  have h2z := zpow_right_injective₀ hQ0 hQ1.ne' hz
  have ha0 : a = 0 := by omega
  rw [hw, ha0, pow_zero, one_mul]
  exact hwu

end RankOne

/-! ### The reduced named input and the reduction -/

section Reduction

variable {F : Type} [Field F] [NumberField F]

/-- **Shimura's local density of $\mathbb H^k\perp N$ at a dyadic place, at its two lowest levels $n = r+2k\le 6$** (a **named
input**, the special case $n \le 6$ of `DyadicKernelDensity`; Shimura, Thm 8.6(3), Prop. 3.9; Hanke thesis (3.3), p. 8). Same
data and conclusion as `DyadicKernelDensity` (see there), with the extra hypothesis $r + 2k \le 6$. Field: `density`.
For each kernel dimension $r\in\{2,3,4\}$ these are the two levels $k_0, k_0+1$ ($k_0$ least with $r+2k_0\ge3$); every other
level follows (`dyadicKernelDensity_of_low`). Not definitionally the conclusion of `DyadicKernelDensity`: it says nothing
about $n \ge 7$. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N with Λ̃_p ≠ Λ_p, n ≤ 6; quoting Shimura 1999, Thm 8.6(3), Prop. 3.9)"]
structure DyadicKernelDensityLow (F : Type) [Field F] [NumberField F] : Prop where
  /-- The local density of $\mathbb H^k\perp N$ for $3 \le r + 2k \le 6$ and $r \ge 2$. -/
  density : ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsUnit (2 : v.adicCompletionIntegers F) → ∀ {k r : ℕ}, 3 ≤ r + 2 * k →
    r + 2 * k ≤ 6 → 2 ≤ r →
    ∀ N : QuadForm (v.adicCompletionIntegers F) r, N.Nondegenerate →
      MaxProp v (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) →
      (∀ y : Fin r → v.adicCompletion F,
        (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) →
      ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 →
      (Odd (r + 2 * k) → ∃ c : v.adicCompletion F, c ≠ 0 ∧
        ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) /
          2 ^ (r + 2 * k) * c ^ 2‖ = 1) →
      DVR.localDensityForm (hypSum N k) (hypSum N k) (NF.π v) =
        2 * ‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ *
          xiShimura (normQ v) (r + 2 * k) r
            (¬ IsUnramSqrt v ((-1) ^ ((r + 2 * k) / 2) *
              ((((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * k))))
            (‖(((hypSum N k).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ = 1)

theorem aniso_integral (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (N : QuadForm (v.adicCompletionIntegers F) r)
    (han : ∀ y : Fin r → v.adicCompletion F,
      (N.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).eval y = 0 → y = 0) :
    ∀ x : Fin r → v.adicCompletionIntegers F, N.eval x = 0 → x = 0 := by
  intro x hx
  have h := han (fun i => algebraMap _ _ (x i)) (by rw [eval_map_gen, hx, map_zero])
  funext i
  have := congrFun h i
  exact (FaithfulSMul.algebraMap_injective (v.adicCompletionIntegers F) (v.adicCompletion F)) (by simpa using this)

open Classical in
/-- **`DyadicKernelDensity` from its two lowest levels** (Shimura's formula for $\mathbb H^k\perp N$ for all $k$ from the
cases $n\le6$): purely local; see the module docstring. -/
@[kb "hanke2005crelle" "(3.3), p. 8 (dyadic H^k ⊥ N with Λ̃_p ≠ Λ_p; from the levels n ≤ 6)"]
theorem dyadicKernelDensity_of_low (I : DyadicKernelDensityLow F) : DyadicKernelDensity F := by
  refine ⟨fun v h2 {k r} hn N hN hmax han hD hdet => ?_⟩
  set D := dN v N with hDdef
  set ram0 : Prop := ¬ IsUnramSqrt v ((-1) ^ (r / 2) * (D / 2 ^ r)) with hram0
  have hD0 : ‖D‖⁻¹ ≠ 1 := by rw [← norm_det_hypSum v N k]; exact hD
  -- the right-hand side at level `j`, normalized
  set S : ℕ → ℝ := fun j => 2 * ‖D‖⁻¹ * xiShimura (normQ v) (r + 2 * j) r ram0 False with hSdef
  have hrhs : ∀ j, 2 * ‖(((hypSum N j).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ *
      xiShimura (normQ v) (r + 2 * j) r
        (¬ IsUnramSqrt v ((-1) ^ ((r + 2 * j) / 2) *
          ((((hypSum N j).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) / 2 ^ (r + 2 * j))))
        (‖(((hypSum N j).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ = 1) = S j := by
    intro j
    rw [norm_det_hypSum, ram_hypSum, ← hDdef, ← hram0, eq_false hD0]
  rw [hrhs]
  set β : ℕ → ℝ := fun j => DVR.localDensityForm (hypSum N j) (hypSum N j) (NF.π v) with hβdef
  show β k = S k
  have han' := aniso_integral v N han
  have hq : ((DVR.q (v.adicCompletionIntegers F) : ℕ) : ℝ) = normQ v := DensitySD.q_eq v
  have hq1 : 1 < normQ v := one_lt_normQ v
  set Z : ℝ := (resZero (NF.π v) N : ℝ) with hZdef
  have hrec : ∀ j, β (j + 1) = rho (normQ v) r Z j * β j := by
    intro j
    rw [hβdef]
    simp only
    rw [localDensityForm_hypSum_succ (NF.irreducible_π v) N hN han' j, hq]
  -- the rank of the kernel
  have hr4 : r ≤ 4 := rank_le_four_of_aniso v _ han
  rcases Nat.eq_zero_or_pos r with hr0 | hr1
  · -- `r = 0`: then `|D| = 1`
    subst hr0
    exfalso
    apply hD0
    have : D = 1 := by rw [hDdef, dN]; simp [Matrix.det_isEmpty]
    rw [this, norm_one, inv_one]
  have hSrec : ∀ j, S (j + 1) = rho (normQ v) r (zStar (normQ v) r ram0) j * S j := by
    intro j
    simp only [hSdef]
    rw [xiShimura_succ hq1 hr1 hr4 ram0 j]
    ring
  by_cases hr1' : r = 1
  · -- `r = 1`: proved outright, `N = ⟨ε⟩` with `ε` a unit
    subst hr1'
    have hπ := NF.irreducible_π v
    have hε : IsUnit (N.coeff 0 0) :=
      isUnit_of_rank_one v N hN hmax ((detHyp_hypSum v N k).1 (hdet (by rw [Nat.odd_iff]; omega)))
    have hdiag := diag_of_rank_one N
    have hdet2 : N.hessian.det = 2 * N.coeff 0 0 := by
      rw [hdiag]; simp [QuadForm.hessian, QuadForm.diag, Matrix.det_unique]; ring
    -- the residue zero count is `1`
    have hZ1 : Z = zStar (normQ v) 1 ram0 := by
      have hmaxI : (Ideal.span {NF.π v ^ 1}).IsMaximal := by
        rw [pow_one, ← hπ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal _
      let _ : Field (v.adicCompletionIntegers F ⧸ Ideal.span {NF.π v ^ 1}) := Ideal.Quotient.field _
      simp only [hZdef, zStar, if_true]
      norm_cast
      unfold resZero zeroCount
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨0, eval_zero' _⟩, fun x => Subtype.ext ?_⟩
      have hx := x.2
      have hu := (hε.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ 1}))).ne_zero
      simp [QuadForm.evalIn, QuadForm.map] at hx
      funext i
      fin_cases i
      simpa [hu] using hx
    -- the base level `k = 0`
    obtain ⟨e, he, he'⟩ := exists_pow_dvd_not_dvd (NF.π v) hπ (two_ne_zero : (2 : v.adicCompletionIntegers F) ≠ 0)
    have hβ0 : β 0 = S 0 := by
      have hN1 : N = DVR.unary (N.coeff 0 0) := hdiag
      simp only [hβdef, hSdef]
      rw [show hypSum N 0 = N from rfl, hN1, localDensityForm_self_unary _ hπ e ⟨he, he'⟩ hε]
      have hDn : ‖D‖ = ((DVR.q (v.adicCompletionIntegers F) : ℝ) ^ e)⁻¹ := by
        rw [hDdef, dN, hdet2]
        refine Tamagawa.norm_coe_of_pow_dvd v (dvd_mul_of_dvd_left he _) fun h => he' ?_
        exact (IsUnit.dvd_mul_right hε).mp h
      rw [hDn, inv_inv, hq]
      simp [xiShimura, ppow]
    exact eq_of_rec 0 (by rw [← hZ1]; exact hrec) hSrec hβ0 k (Nat.zero_le _)
  have hr2 : 2 ≤ r := by omega
  -- the two lowest levels
  set k₀ : ℕ := if r ≤ 2 then 1 else 0 with hk₀
  have hk₀k : k₀ ≤ k := by rw [hk₀]; split_ifs <;> omega
  have hlow : ∀ j, k₀ ≤ j → j ≤ k₀ + 1 → β j = S j := by
    intro j hj1 hj2
    have h3 : 3 ≤ r + 2 * j := by rw [hk₀] at hj1; split_ifs at hj1 <;> omega
    have h6 : r + 2 * j ≤ 6 := by rw [hk₀] at hj2; split_ifs at hj2 <;> omega
    have hDj : ‖(((hypSum N j).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F)‖⁻¹ ≠ 1 := by
      rw [norm_det_hypSum]; exact hD0
    have hdetj : Odd (r + 2 * j) → ∃ c : v.adicCompletion F, c ≠ 0 ∧
        ‖(((hypSum N j).hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) /
          2 ^ (r + 2 * j) * c ^ 2‖ = 1 := by
      intro hodd
      have hodd' : Odd (r + 2 * k) := by
        rw [Nat.odd_iff] at hodd ⊢; omega
      exact (detHyp_hypSum v N j).2 ((detHyp_hypSum v N k).1 (hdet hodd'))
    have := I.density v h2 h3 h6 hr2 N hN hmax han hDj hdetj
    rw [hrhs] at this
    exact this
  -- the residue count is Shimura's
  have hpos : 0 < β k₀ := Tamagawa.localDensityForm_self_pos' v _ (hypSum_nondegenerate hN k₀)
  have hZ : Z = zStar (normQ v) r ram0 := by
    apply rho_injective hq1 r k₀
    have e1 := hrec k₀
    rw [hlow (k₀ + 1) (by omega) le_rfl, hSrec, ← hlow k₀ le_rfl (by omega)] at e1
    exact (mul_right_cancel₀ hpos.ne' e1).symm
  rw [hZ] at hrec
  exact eq_of_rec k₀ hrec hSrec (hlow k₀ le_rfl (by omega)) k hk₀k

/-- **`ShimuraMaximalDensityRest` from the two lowest levels of the dyadic kernel density.** -/
@[kb "hanke2005crelle" "(3.3), p. 8 (all places; from the dyadic kernel densities at n ≤ 6)"]
theorem shimuraMaximalDensityRest_of_low (I : DyadicKernelDensityLow F) : ShimuraMaximalDensityRest F :=
  shimuraMaximalDensityRest_of_kernelDensity (dyadicKernelDensity_of_low I)

end Reduction

end QuadFormsKB.Hanke2005
