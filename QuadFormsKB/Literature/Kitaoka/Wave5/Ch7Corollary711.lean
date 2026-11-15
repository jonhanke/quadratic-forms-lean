/-
# Kitaoka 1993, Corollary 7.1.1: a lower bound for the minimum of a tensor product

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §7.1, Corollary 7.1.1, p. 193.

**Statement.** Put $c_n = \min_{1 \le r \le n} r\,\mu_r^{-2}$ ($\mu_r$ Hermite's constant). If $L$, $M$ are positive
lattices with $\operatorname{rank} L = n$, then $\min(L \otimes M) \ge c_n \min(L)\min(M)$. Here (`corollary711`) the
bound is proved for every nonzero vector $X$ of $L \otimes M$: $Q(X) \ge c_n \min(L)\min(M)$, which is the statement
(the minimum is the infimum of these values).

**Proof** (Kitaoka's inequality (4) in the proof of Theorem 7.1.1). Write $X = PR$ with $P$ injective and $R$ of full
row rank $r$, $1 \le r \le n$ (`EType.exists_factor`), and let $L_1$, $M_1$ be the rank-$r$ lattices with Gram matrices
$G_A = {}^tP A P$, $G_B = R B\,{}^tR$. Then $Q(X) = \operatorname{tr}(G_A G_B) \ge r(\det G_A \det G_B)^{1/r}$
(Lemma 7.1.3) $\ge r\mu_r^{-2}\min(L_1)\min(M_1) \ge c_n\min(L)\min(M)$, as $\min(L_1) \ge \min(L)$,
$\min(M_1) \ge \min(M)$. Hermite's constant is finite for every $r \ge 1$ by Theorem 2.2.1 (`Blichfeldt.theorem221`).
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch2Blichfeldt
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Theorem711
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch7Lemma711

open Matrix

noncomputable section

namespace QuadFormsKB.Kitaoka.EType

/-- **The constant $c_n = \min_{1 \le r \le n} r/\mu_r^2$** of Kitaoka 1993, Corollary 7.1.1 (p. 193), with $\mu_r$
Hermite's constant (`Reduction.hermiteConst`). For $n = 0$ (empty range) it is $0$. -/
@[kb "kitaoka1993" "§7.1, Cor. 7.1.1, p. 193 (c_n = min r/μ_r²)"]
def tensorMinConst (n : ℕ) : ℝ :=
  if h : (Finset.Icc 1 n).Nonempty then
    (Finset.Icc 1 n).inf' h fun r => (r : ℝ) / Reduction.hermiteConst r ^ 2
  else 0

/-- **The minimum of a positive lattice** $L = (\mathbb Z^n, A)$ (Kitaoka 1993, §7.1, p. 190):
$\min(L) = \min\{Q(x) \mid 0 \ne x \in \mathbb Z^n\}$, here `Reduction.latMin` of the real Gram matrix. -/
@[kb "kitaoka1993" "§7.1, p. 190 (min L)"]
def gramMin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℝ :=
  Reduction.latMin (A.map (Rat.cast : ℚ → ℝ))

/-- $\min(L) \ge 0$ for a positive lattice of rank $a \ge 1$. -/
theorem gramMin_nonneg {a : ℕ} (ha : 1 ≤ a) {A : Matrix (Fin a) (Fin a) ℚ} (hA : IsPosGram A) :
    0 ≤ gramMin A := by
  refine le_csInf ⟨_, Pi.single ⟨0, ha⟩ 1, by simp, rfl⟩ ?_
  rintro _ ⟨x, -, rfl⟩
  rw [cast_quad]
  exact_mod_cast gramQ_nonneg hA x

/-- A sublattice has minimum at least that of the lattice: $\min(L) \le \min(L_1)$ for $L_1$ with Gram matrix
${}^tC A C$, $C$ injective. -/
theorem gramMin_le_conj {a b : ℕ} (hb : 1 ≤ b) (C : Matrix (Fin a) (Fin b) ℤ) (hC : ∀ v, C *ᵥ v = 0 → v = 0)
    {A : Matrix (Fin a) (Fin a) ℚ} (hA : IsPosGram A) :
    gramMin A ≤ Reduction.latMin (((qmat C)ᵀ * A * qmat C).map (Rat.cast : ℚ → ℝ)) := by
  refine le_csInf ⟨_, Pi.single ⟨0, hb⟩ 1, by simp, rfl⟩ ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [cast_quad, quad_conj_gramQ]
  refine csInf_le ⟨0, ?_⟩ ⟨C *ᵥ x, fun h => hx (hC x h), ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    rw [cast_quad]
    exact_mod_cast gramQ_nonneg hA y
  · rw [cast_quad]
    rfl

/-- Hermite's bound for one matrix: $\min p \le \mu_r (\det p)^{1/r}$ ($r \ge 1$; Hermite's constant is finite by
Theorem 2.2.1). -/
theorem latMin_le_hermiteConst_mul {r : ℕ} (hr : 1 ≤ r) (p : Matrix (Fin r) (Fin r) ℝ) (hp : p.PosDef) :
    Reduction.latMin p ≤ Reduction.hermiteConst r * p.det ^ ((1 : ℝ) / r) := by
  have hd : 0 < p.det ^ ((1 : ℝ) / r) := Real.rpow_pos_of_pos hp.det_pos _
  have hle : Reduction.latMin p / p.det ^ ((1 : ℝ) / r) ≤ Reduction.hermiteConst r := by
    refine le_csSup ⟨Blichfeldt.blichfeldtConst r, ?_⟩ ⟨p, hp, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hq.det_pos _)]
    exact Blichfeldt.latMin_le_blichfeldtConst_mul hr q hq
  rwa [div_le_iff₀ hd] at hle

/-- **Kitaoka 1993, Corollary 7.1.1** (p. 193): for positive lattices $L = (\mathbb Z^n, A)$ with $n \ge 1$ and
$M = (\mathbb Z^m, B)$, every nonzero $X \in L \otimes M$ (an integral $n \times m$ matrix) satisfies
$Q(X) \ge c_n \min(L) \min(M)$; hence $\min(L \otimes M) \ge c_n \min(L)\min(M)$. -/
@[kb "kitaoka1993" "§7.1, Cor. 7.1.1, p. 193"]
theorem corollary711 {n m : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsPosGram A)
    (B : Matrix (Fin m) (Fin m) ℚ) (hB : IsPosGram B) (X : Matrix (Fin n) (Fin m) ℤ) (hX : X ≠ 0) :
    tensorMinConst n * gramMin A * gramMin B ≤ (tensorQ A B X : ℝ) := by
  obtain ⟨r, P, R, hXPR, hP, hR⟩ := exists_factor X
  have hrn : r ≤ n := by
    have hinj : Function.Injective P.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      exact hP v hv
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      exact absurd (by rw [hXPR]; ext i j; simp [Matrix.mul_apply]) hX
    · exact h0
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exact absurd (by ext i j; exact j.elim0) hX
    · exact h0
  have hC : ∀ y, Rᵀ *ᵥ y = 0 → y = 0 := fun y h => hR y (by rwa [Matrix.mulVec_transpose] at h)
  set GA := (qmat P)ᵀ * A * qmat P with hGA
  set GB := (qmat Rᵀ)ᵀ * B * qmat Rᵀ with hGB
  set GAr := GA.map (Rat.cast : ℚ → ℝ) with hGAr
  set GBr := GB.map (Rat.cast : ℚ → ℝ) with hGBr
  have hAr : GAr.PosDef := posDef_ratCast GA (isPosGram_conj P hP A hA)
  have hBr : GBr.PosDef := posDef_ratCast GB (isPosGram_conj Rᵀ hC B hB)
  have hT : (tensorQ A B X : ℝ) = (GAr * GBr).trace := by
    rw [tensorQ_factor A B hB.1 X P R hXPR]
    have hmap : (GA * GB).map (Rat.cast : ℚ → ℝ) = GAr * GBr := Matrix.map_mul (f := Rat.castHom ℝ)
    have hGG : (qmat P)ᵀ * A * qmat P * ((qmat Rᵀ)ᵀ * B * qmat Rᵀ) = GA * GB := rfl
    rw [hGG, ← hmap]
    simp [Matrix.trace, Matrix.diag]
  have h713 := lemma713 r GAr GBr hAr hBr
  rw [← hT, Real.mul_rpow hAr.det_pos.le hBr.det_pos.le] at h713
  -- the ingredients
  set μ := Reduction.hermiteConst r with hμ
  set dA := GAr.det ^ ((1 : ℝ) / r) with hdA
  set dB := GBr.det ^ ((1 : ℝ) / r) with hdB
  have hdA0 : 0 < dA := Real.rpow_pos_of_pos hAr.det_pos _
  have hdB0 : 0 < dB := Real.rpow_pos_of_pos hBr.det_pos _
  have hLA : gramMin A ≤ Reduction.latMin GAr := gramMin_le_conj hr1 P hP hA
  have hLB : gramMin B ≤ Reduction.latMin GBr := gramMin_le_conj hr1 Rᵀ hC hB
  have hμA : Reduction.latMin GAr ≤ μ * dA := latMin_le_hermiteConst_mul hr1 GAr hAr
  have hμB : Reduction.latMin GBr ≤ μ * dB := latMin_le_hermiteConst_mul hr1 GBr hBr
  have ha0 := gramMin_nonneg hn hA
  have hb0 := gramMin_nonneg hm1 hB
  have hLA0 : 0 ≤ Reduction.latMin GAr := ha0.trans hLA
  have hLB0 : 0 ≤ Reduction.latMin GBr := hb0.trans hLB
  have hμ0 : 0 ≤ μ := by
    by_contra h
    push Not at h
    nlinarith
  have hc : tensorMinConst n ≤ (r : ℝ) / μ ^ 2 := by
    have hmem : r ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hr1, hrn⟩
    unfold tensorMinConst
    rw [dite_eq_left_of_eq_true (eq_true ⟨r, hmem⟩)]
    exact Finset.inf'_le _ hmem
  have hq0 : 0 ≤ (r : ℝ) / μ ^ 2 := by positivity
  have hfin : (r : ℝ) / μ ^ 2 * (μ * dA * (μ * dB)) ≤ r * (dA * dB) := by
    rcases eq_or_lt_of_le hμ0 with h | h
    · rw [← h]; simp; positivity
    · rw [show (r : ℝ) / μ ^ 2 * (μ * dA * (μ * dB)) = r * (dA * dB) by field_simp]
  calc tensorMinConst n * gramMin A * gramMin B
      = tensorMinConst n * (gramMin A * gramMin B) := by ring
    _ ≤ (r : ℝ) / μ ^ 2 * (gramMin A * gramMin B) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (r : ℝ) / μ ^ 2 * (Reduction.latMin GAr * Reduction.latMin GBr) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hLA hLB hb0 hLA0) hq0
    _ ≤ (r : ℝ) / μ ^ 2 * (μ * dA * (μ * dB)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hμA hμB hLB0 (by positivity)) hq0
    _ ≤ r * (dA * dB) := hfin
    _ ≤ (tensorQ A B X : ℝ) := h713

end QuadFormsKB.Kitaoka.EType
