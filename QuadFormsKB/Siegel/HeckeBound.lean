/-
# Hecke's bound for $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$, and Theorem 6.4 without Deligne

For $Q$ positive definite in $n = 2k$ variables, $c(m) = r_Q(m) - a_E(m)$ (`genusCuspCoeff`, $a_E$ = `genusRepAvg`, the genus
average) are the $q$-coefficients of the cusp form $\Theta_Q - \Theta_{\mathrm{Gen}(Q)} \in S_k(\Gamma_1(N))$ (`thetaGenCusp`). This file
replaces Deligne's bound ((4.8), the cited inputs `CuspBound` / `EigenformDecompDeligne`) by **Hecke's bound**
$$|c(m)| \le C\,m^{k/2}\qquad(m \ge 1)$$
(`exists_abs_genusCuspCoeff_le`, unconditional), from Mathlib's `CuspFormClass.qExpansion_isBigO` (the coefficients of a weight-$k$
cusp form on an arithmetic group are $O(m^{k/2})$, from the boundedness of $y^{k/2}|f|$). The constant $C$ is **not explicit**: it
is a bound for $y^{k/2}|\Theta_Q - \Theta_{\mathrm{Gen}}|$ on $\mathbb H$, obtained by compactness, plus the finitely many
coefficients before the $O$-bound takes over.

Since the main term grows like $m^{k-1}$ and $k - 1 > k/2 \iff k > 2 \iff n \ge 6$, Hecke's bound suffices for $n \ge 6$
(Hanke 2004, Thm 6.4, $n$ even; the paper uses (4.8) with Deligne's exponent $(k-1)/2$, which also works for $n = 4$):

* `cuspBound_hecke`: the repo's `CuspBound` for $c$ with exponent $k/2$ (no Deligne);
* `represents_of_genusRepAvg_ge` (**Tartakowsky type, conditional only on a main-term lower bound**): for every $\Lambda > 0$ there is
  $M_0$ such that every $m \ge M_0$ with $a_E(m) \ge \Lambda\,m^{k-1}$ is represented by $Q$ (no explicit $M_0$);
* `thm_6_4_even_hecke`: Hanke's Thm 6.4 ($n \ge 6$ even) with the hypotheses `ThetaSplit` and `CuspBound` (Deligne) removed:
  under Siegel's formula and the global bound `hglob` of `thm_6_4_even`, $Q$ represents $m$ once $m^{(n-4)/4} > C/\Lambda$, for a
  constant $C$ that exists but is not explicit.

The unconditional version (Siegel's formula and the main-term bound discharged over $F = \mathbb Q$) is in
`Siegel/Tartakowsky.lean`.

*Comparison.* `thm_6_4_even` (conditional on Deligne via `CuspBound`) has the explicit threshold
$m^{(n-2)/4}/\tau(m) > C/\Lambda$ with $C = \sum_i|\gamma_i|$ computable from the eigenform decomposition (4.7); here the threshold
$m^{(n-4)/4} > C/\Lambda$ is weaker in the exponent ($\frac{n-4}{4} < \frac{n-2}{4}$) and $C$ is ineffective as formalized (it
comes from a supremum over $\mathbb H$ and an `IsBigO` witness).

Sources: Iwaniec, *Topics in Classical
Automorphic Forms*, Thm 5.1 (Hecke's bound $a(n) \ll n^{k/2}$) [unverified]; Hanke 2004, Thm 6.4, p. 382.
-/
import QuadFormsKB.Siegel.ThetaSplitOf
import QuadFormsKB.Siegel.EigenformBound
import QuadFormsKB.Siegel.MainResults
import QuadFormsKB.Siegel.Thm63Inputs
import Mathlib.NumberTheory.ModularForms.Bounds

open Complex Filter Asymptotics UpperHalfPlane
open scoped MatrixGroups

namespace QuadFormsKB.Siegel

open LocalDensity

noncomputable section

variable {n : ℕ}

/-- **From an `IsBigO` at infinity to a bound for all $m \ge 1$**: if $a(m) = O(m^e)$ with $e \ge 0$, then
$\|a(m)\| \le C\,m^e$ for every $m \ge 1$, for some $C \ge 0$ (the finitely many early terms are absorbed, as $m^e \ge 1$). -/
theorem exists_norm_le_of_isBigO {a : ℕ → ℂ} {e : ℝ} (he : 0 ≤ e)
    (h : a =O[atTop] fun m : ℕ => (m : ℝ) ^ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ‖a m‖ ≤ C * (m : ℝ) ^ e := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hc
  set C : ℝ := max c 0 + ∑ j ∈ Finset.range m₀, ‖a j‖
  have hS : 0 ≤ ∑ j ∈ Finset.range m₀, ‖a j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C, by positivity, fun m hm => ?_⟩
  have hme : (1 : ℝ) ≤ (m : ℝ) ^ e := Real.one_le_rpow (by exact_mod_cast hm) he
  rcases le_or_gt m₀ m with h0 | h0
  · have := hm₀ m h0
    rw [Real.norm_of_nonneg (by positivity)] at this
    calc ‖a m‖ ≤ c * (m : ℝ) ^ e := this
      _ ≤ max c 0 * (m : ℝ) ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C * (m : ℝ) ^ e := mul_le_mul_of_nonneg_right (by simp only [C]; linarith) (by positivity)
  · have h1 : ‖a m‖ ≤ ∑ j ∈ Finset.range m₀, ‖a j‖ :=
      Finset.single_le_sum (f := fun j => ‖a j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 h0)
    have h2 : ∑ j ∈ Finset.range m₀, ‖a j‖ ≤ C := by simp only [C]; linarith [le_max_right c 0]
    calc ‖a m‖ ≤ C := h1.trans h2
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (m : ℝ) ^ e := mul_le_mul_of_nonneg_left hme (by linarith)

/-- **The $q$-coefficients of $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ are $c(m) = r_Q(m) - a_E(m)$** (any even $n = 2k$; the case
$k = 2$ is `qCoeff_thetaGenCusp`), by uniqueness of $q$-expansions applied to `hasSum_genusCuspCoeff`. -/
theorem qExpansion_thetaGenCusp_coeff {Q : IntQF n} (hQ : Q.PosDef) (hF : GenusFinite Q) {k : ℕ}
    (hn : n = 2 * k) {N : ℕ} (hN0 : 0 < N) (hN : ∀ Q', SameGenus Q Q' → IsThetaLevel Q' N) (m : ℕ) :
    (qExpansion 1 (thetaGenCusp hQ hF hn hN0 hN)).coeff m = (genusCuspCoeff Q m : ℂ) := by
  refine (ModularFormClass.qExpansion_coeff_unique (k := (k : ℤ)) (c := fun j => (genusCuspCoeff Q j : ℂ))
    one_pos (one_mem_strictPeriods_Gamma1 N) (f := thetaGenCusp hQ hF hn hN0 hN) (fun τ => ?_) m).symm
  convert hasSum_genusCuspCoeff hQ hF hn hN0 hN τ using 2 with j
  rw [Function.Periodic.qParam, smul_eq_mul, ← Complex.exp_nat_mul]
  congr 2; push_cast; ring

/-- **Hecke's bound for $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$** (unconditional; $Q$ positive definite in $n = 2k$ variables): there is
$C \ge 0$ with
$$|c(m)| = |r_Q(m) - a_E(m)| \le C\,m^{k/2}\qquad\text{for all } m \ge 1.$$
From Mathlib's `CuspFormClass.qExpansion_isBigO` for the cusp form `thetaGenCusp` on $\Gamma_1(N)$ ($T \in \Gamma_1(N)$, so the
strict width at $\infty$ is $1$), and `exists_norm_le_of_isBigO`. $C$ is not explicit. -/
@[kb "iwaniec1997" "Thm 5.1 (Hecke's bound a(m) ≪ m^{k/2}), applied to θ_Q − θ_Gen [unverified]"]
theorem exists_abs_genusCuspCoeff_le {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → |genusCuspCoeff Q m| ≤ C * (m : ℝ) ^ ((k : ℝ) / 2) := by
  have hF := genusFinite hQ
  obtain ⟨N, hN0, hN⟩ := exists_isThetaLevel_genus hQ hF
  have : NeZero N := ⟨hN0.ne'⟩
  set f := thetaGenCusp hQ hF hn hN0 hN
  have hO := CuspFormClass.qExpansion_isBigO (k := (k : ℤ))
    (Γ := ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) f
  have hw : (((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictWidthInfty
      = 1 := Subgroup.strictWidthInfty_eq_one_of_T_mem (CongruenceSubgroup.Gamma1_mem N _ |>.2
        ⟨by simp [ModularGroup.T], by simp [ModularGroup.T], by simp [ModularGroup.T]⟩)
  rw [hw] at hO
  simp only [Int.cast_natCast] at hO
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_isBigO (by positivity) hO
  refine ⟨C, hC0, fun m hm => ?_⟩
  have := hC m hm
  rwa [qExpansion_thetaGenCusp_coeff, Complex.norm_real, Real.norm_eq_abs] at this

/-- **`CuspBound` from Hecke's bound** (replacing the cited input (4.8) + Deligne for the exponent $k/2$): for $Q$ positive definite
in $n = 2k$ variables there is $C \ge 0$ with `CuspBound (genusCuspCoeff Q) (k/2) C`, i.e. $|c(m)| \le C\,\tau(m)\,m^{k/2}$
($\tau(m) \ge 1$). Unconditional. -/
@[kb "iwaniec1997" "Thm 5.1 (Hecke's bound) as CuspBound with exponent k/2, replacing (4.8) + Deligne [unverified]"]
theorem cuspBound_hecke {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ CuspBound (genusCuspCoeff Q) ((k : ℝ) / 2) C := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_genusCuspCoeff_le hQ hn
  refine ⟨C, hC0, ⟨fun m hm => ?_⟩⟩
  have hτ : (1 : ℝ) ≤ divCount m := by
    exact_mod_cast divCount_pos (Nat.one_le_iff_ne_zero.1 hm)
  calc |genusCuspCoeff Q m| ≤ C * (m : ℝ) ^ ((k : ℝ) / 2) := hC m hm
    _ = C * 1 * (m : ℝ) ^ ((k : ℝ) / 2) := by ring
    _ ≤ C * divCount m * (m : ℝ) ^ ((k : ℝ) / 2) := by gcongr

/-- **Main term beats Hecke** (the comparison step of Hanke 2004, §6, with Hecke's bound): for $n = 2k$, $k \ge 3$ (so $n \ge 6$),
$Q$ positive definite and any $\Lambda > 0$, there is $M_0$ such that every $m \ge M_0$ with $a_E(m) \ge \Lambda\,m^{k-1}$ is represented
by $Q$. Unconditional; $M_0$ exists but is not explicit (it depends on the Hecke constant of `exists_abs_genusCuspCoeff_le`). The
lower bound for $a_E(m)$ is the only hypothesis on $m$. -/
@[kb "hanke2004" "§6, p. 380 (a_E(m) > |c(m)|), with Hecke's bound in place of (4.8)"]
theorem represents_of_genusRepAvg_ge {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k) (hk : 3 ≤ k)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Λ * (m : ℝ) ^ (k - 1) ≤ genusRepAvg Q m → IntQF.Represents Q m := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_genusCuspCoeff_le hQ hn
  -- `m^{k-1} = m^{k/2} · m^{k/2 - 1}`, and `m^{k/2-1} > C/Λ` eventually
  set e : ℝ := (k : ℝ) / 2 - 1 with he
  have he0 : 0 < e := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    rw [he]; linarith
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 ((tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop
    |>.eventually_gt_atTop (C / Λ))
  refine ⟨M₀ + 1, fun m hm hlow => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hbig : C / Λ < (m : ℝ) ^ e := hM₀ m (by omega)
  have hsplit : (m : ℝ) ^ (k - 1) = (m : ℝ) ^ ((k : ℝ) / 2) * (m : ℝ) ^ e := by
    rw [← Real.rpow_add hmpos, ← Real.rpow_natCast, he]
    congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
  have hx : 0 < (m : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hmpos _
  have key : C * (m : ℝ) ^ ((k : ℝ) / 2) < Λ * (m : ℝ) ^ (k - 1) := by
    rw [hsplit]
    have h1 : C < Λ * (m : ℝ) ^ e := by
      rw [div_lt_iff₀ hΛ] at hbig; linarith
    nlinarith
  exact represents_of_abs_lt_aE (thetaSplit_genusCuspCoeff Q) (by omega) hm1
    (lt_of_le_of_lt (hC m hm1) (lt_of_lt_of_le key hlow))

open Classical in
/-- **Theorem 6.4, $n$ even, with Hecke's bound in place of Deligne's** (Hanke 2004, Thm 6.4, p. 382, $n \ge 6$ even). Let $Q$ be
positive definite in $n = 2k \ge 6$ variables satisfying Siegel's formula (`SiegelFormula`). Then there is a constant $C \ge 0$
(Hecke's, not explicit) such that, with $m = T'(m')^2$, $m' = \prod_{p \in S}p^{\nu_p}$ and the hypotheses of `thm_6_4_even`
(Thm 5.7(c) and the global bound `hglob` with constant $\hat\Lambda_n = \Lambda$), $Q$ represents $m$ whenever
$$m^{(n-4)/4} > C/\Lambda.$$
Compared with `thm_6_4_even`, the inputs `ThetaSplit` (now `thetaSplit_genusCuspCoeff`, a theorem) and `CuspBound` ((4.8) with
Deligne's exponent $(n-2)/4$) are gone; the threshold has the weaker exponent $(n-4)/4 = k/2 - 1$ and no $\tau(m)$, and $C$ is not
explicit. -/
@[kb "hanke2004" "Thm 6.4, p. 382 (n even ≥ 6), Hecke's bound in place of (4.8)"]
theorem thm_6_4_even_hecke (Q : IntQF n) (hQ : IntQF.PosDef Q) (hn : 6 ≤ n) (heven : Even n)
    (hSF : SiegelFormula Q) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {S : Finset ℕ}, (∀ p ∈ S, p.Prime) → (∀ p ∈ S, IsIsotropicPrime Q p) →
    ∀ (S₀ : Finset (Fin n)) {T : ℕ}, 0 < T → (∀ p ∈ S, IsPStable Q S₀ p T) →
    (∀ p ∈ S, IsGoodPrime Q p → ¬ (p : ℤ) ^ 2 ∣ T) → ∀ (ν : ℕ → ℕ) {Λ : ℝ}, 0 < Λ →
    (Λ * (T : ℝ) ^ ((n - 2) / 2) ≤ genusRepAvg Q T *
        (∏ p ∈ (S.filter (IsIsotropicPrime Q)).filter (fun p => ¬ IsGoodPrime Q p),
          localConstC' Q p T) *
        ∏ p ∈ (S.filter (IsGoodPrime Q)).filter
            (fun p => jacobiSym ((-1) ^ (n / 2) * Q.hessian.det) p = -1 ∧ ¬ (p : ℤ) ∣ T),
          (p : ℝ) ^ ((n - 2) / 2) / ((p : ℝ) ^ ((n - 2) / 2) + 1)) →
    ∀ {m : ℕ}, m = T * (∏ p ∈ S, p ^ ν p) ^ 2 →
    C / Λ < (m : ℝ) ^ (((n : ℝ) - 4) / 4) → IntQF.Represents Q m := by
  obtain ⟨k, hk⟩ := heven
  have hn2 : n = 2 * k := by omega
  obtain ⟨C, hC0, hC⟩ := exists_abs_genusCuspCoeff_le hQ hn2
  refine ⟨C, hC0, fun {S} hS hIso S₀ {T} hT hst hT2 ν {Λ} hΛ hglob {m} hm hbound => ?_⟩
  have hm'pos : 0 < ∏ p ∈ S, p ^ ν p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have h57 := thm_5_7_c_even_genus Q hSF hQ (by omega) ⟨k, hk⟩ hS S₀ (T := (T : ℤ))
    (by exact_mod_cast hT) hst hT2 ν
  rw [← natCast_mul_sqPart, ← hm, Finset.filter_true_of_mem hIso] at h57
  rw [Finset.filter_true_of_mem hIso] at hglob
  set M : ℝ := ∏ p ∈ S, (p : ℝ) ^ ν p with hM
  have hMm : (m : ℝ) = T * M ^ 2 := by rw [hm, hM]; push_cast; rfl
  have hk2 : 2 * ((n - 2) / 2) = n - 2 := by omega
  -- the main term: `a_E(m) ≥ Λ m^{(n-2)/2}`
  have hLB : Λ * (m : ℝ) ^ ((n - 2) / 2) ≤ genusRepAvg Q m := by
    have hrest : 0 ≤ M ^ (n - 2) := by positivity
    calc Λ * (m : ℝ) ^ ((n - 2) / 2) = Λ * (T : ℝ) ^ ((n - 2) / 2) * M ^ (n - 2) := by
          rw [hMm, mul_pow, ← pow_mul, hk2]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hglob hrest
      _ = _ := by ring
      _ ≤ genusRepAvg Q m := h57
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hsplit : (m : ℝ) ^ ((n - 2) / 2) = (m : ℝ) ^ ((k : ℝ) / 2) * (m : ℝ) ^ (((n : ℝ) - 4) / 4) := by
    rw [← Real.rpow_add hmpos, ← Real.rpow_natCast]
    congr 1
    rw [show (n - 2) / 2 = k - 1 by omega, Nat.cast_sub (by omega : 1 ≤ k), hn2]; push_cast; ring
  have hx : 0 < (m : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hmpos _
  have h1 : C < Λ * (m : ℝ) ^ (((n : ℝ) - 4) / 4) := by
    rw [div_lt_iff₀ hΛ] at hbound; linarith
  have key : C * (m : ℝ) ^ ((k : ℝ) / 2) < Λ * (m : ℝ) ^ ((n - 2) / 2) := by
    rw [hsplit]; nlinarith
  exact represents_of_abs_lt_aE (thetaSplit_genusCuspCoeff Q) (by omega) hm1
    (lt_of_le_of_lt (hC m hm1) (lt_of_lt_of_le key hLB))

end

end QuadFormsKB.Siegel
