/-
# The E₈ lattice: $\Theta_{E_8} = E_4$ and $r_{E_8}(m) = 240\,\sigma_3(m)$

The $E_8$ root lattice as the integral quadratic form $Q_{E_8}(\vec{x}) = \tfrac12 \vec{x}^{\mathsf T} C \vec{x}$ in
8 variables, where $C$ is the $E_8$ Cartan matrix (Mathlib's `CartanMatrix.E 8`, Bourbaki's labeling: Dynkin
edges $0\!-\!2$, $1\!-\!3$, $2\!-\!3$, $3\!-\!4$, $4\!-\!5$, $5\!-\!6$, $6\!-\!7$, 0-based). $C$ is even with
$\det C = 1$ (Mathlib's `CartanMatrix.E₈_det`), so $Q_{E_8}$ is even unimodular of rank 8.

* `e8_hessian`, `e8_det`, `e8_eval`, `e8_posDef`: $H = C$, $\det H = 1$, the explicit polynomial, and positive
  definiteness (an explicit sum-of-squares identity, the $LDL^{\mathsf T}$ decomposition of $C$).
* `thetaE8`: $\Theta_{E_8}$ as a level-one modular form of weight 4 (`thetaMF`, `Siegel/ThetaModular.lean`).
* `thetaE8_eq_E₄`: $\Theta_{E_8} = E_4$ (Mathlib's normalized Eisenstein series $E_4 = 1 + 240\sum \sigma_3(m) q^m$),
  because $\dim M_4(\mathrm{SL}_2(\mathbb{Z})) = 1$ (`ModularForm.levelOne_weight_four_rank_one`) and both have
  constant term $1$.
* `repNum_e8`: $r_{E_8}(m) = 240\,\sigma_3(m)$ for $m \ge 1$; `repNum_e8_one`: there are 240 roots.

Source: Serre, *A Course in Arithmetic*, Ch. VII §6.6, Example 1 (and §6.5 for $E_8$ itself) [unverified].
-/
import QuadFormsKB.Siegel.ThetaModular

open Complex Matrix ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups ArithmeticFunction.sigma

namespace QuadFormsKB.Siegel

/-- **The $E_8$ form** $Q_{E_8}(\vec{x}) = \sum_{i=0}^{7} x_i^2 - \sum_{\{i,j\} \text{ an edge}} x_i x_j$, i.e. the form with
upper-triangular coefficients $c_{ii} = 1$ and $c_{ij} = C_{ij}$ ($i < j$) for $C$ = `CartanMatrix.E 8`; its Hessian is
$C$ (`e8_hessian`) and its values are given by `e8_eval`. -/
@[kb "serre1973" "Ch. V §1.4.3, the lattice E₈ [unverified]"]
def e8 : QuadForm ℤ 8 := QuadForm.ofUpper fun i j => if i = j then 1 else CartanMatrix.E 8 i j

/-- The Hessian of $Q_{E_8}$ is the $E_8$ Cartan matrix. -/
theorem e8_hessian : e8.hessian = CartanMatrix.E 8 := by decide

/-- $Q_{E_8}$ is unimodular: $\det H = 1$. -/
theorem e8_det : e8.hessian.det = 1 := by rw [e8_hessian]; exact CartanMatrix.E₈_det

/-- **The $E_8$ form explicitly:**
$Q_{E_8}(\vec{x}) = \sum_{i} x_i^2 - x_0x_2 - x_1x_3 - x_2x_3 - x_3x_4 - x_4x_5 - x_5x_6 - x_6x_7$. -/
theorem e8_eval (x : Fin 8 → ℤ) : e8.eval x =
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
      - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7 := by
  simp [QuadForm.evalIn, e8, QuadForm.ofUpper, Fin.sum_univ_eight, CartanMatrix.E]
  ring

/-- **$Q_{E_8}$ is positive definite.** *Proof:* the identity
$840\, Q_{E_8}(\vec{x}) = 210(2x_7 - x_6)^2 + 70(3x_6 - 2x_5)^2 + 35(4x_5 - 3x_4)^2 + 21(5x_4 - 4x_3)^2
+ 14(6x_3 - 5x_1 - 5x_2)^2 + 10(7x_1 - 5x_2)^2 + 15(4x_2 - 7x_0)^2 + 105x_0^2$
(the $LDL^{\mathsf T}$ decomposition of $C$), whose squares vanish together only at $\vec{x} = 0$. -/
theorem e8_posDef : IntQF.PosDef e8 := by
  intro x hx
  rw [e8_eval]
  by_contra hle
  rw [not_lt] at hle
  have key : 840 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
      - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7) =
      210 * (2 * x 7 - x 6) ^ 2 + 70 * (3 * x 6 - 2 * x 5) ^ 2 + 35 * (4 * x 5 - 3 * x 4) ^ 2
      + 21 * (5 * x 4 - 4 * x 3) ^ 2 + 14 * (6 * x 3 - 5 * x 1 - 5 * x 2) ^ 2
      + 10 * (7 * x 1 - 5 * x 2) ^ 2 + 15 * (4 * x 2 - 7 * x 0) ^ 2 + 105 * x 0 ^ 2 := by ring
  have h1 := sq_nonneg (2 * x 7 - x 6)
  have h2 := sq_nonneg (3 * x 6 - 2 * x 5)
  have h3 := sq_nonneg (4 * x 5 - 3 * x 4)
  have h4 := sq_nonneg (5 * x 4 - 4 * x 3)
  have h5 := sq_nonneg (6 * x 3 - 5 * x 1 - 5 * x 2)
  have h6 := sq_nonneg (7 * x 1 - 5 * x 2)
  have h7 := sq_nonneg (4 * x 2 - 7 * x 0)
  have h8 := sq_nonneg (x 0)
  have e1 : (2 * x 7 - x 6) ^ 2 = 0 := by linarith
  have e2 : (3 * x 6 - 2 * x 5) ^ 2 = 0 := by linarith
  have e3 : (4 * x 5 - 3 * x 4) ^ 2 = 0 := by linarith
  have e4 : (5 * x 4 - 4 * x 3) ^ 2 = 0 := by linarith
  have e5 : (6 * x 3 - 5 * x 1 - 5 * x 2) ^ 2 = 0 := by linarith
  have e6 : (7 * x 1 - 5 * x 2) ^ 2 = 0 := by linarith
  have e7 : (4 * x 2 - 7 * x 0) ^ 2 = 0 := by linarith
  have e8' : x 0 ^ 2 = 0 := by linarith
  simp only [pow_eq_zero_iff two_ne_zero] at e1 e2 e3 e4 e5 e6 e7 e8'
  apply hx
  ext i; fin_cases i <;> simp <;> omega

/-- $r_Q(0) = 1$ for $Q$ positive definite (only $\vec{x} = 0$). -/
theorem repNum_zero_of_posDef {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) : repNum Q 0 = 1 := by
  have : repSet Q 0 = {0} := by
    ext x
    simp only [repSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h; by_contra hx; exact (hQ x hx).ne' h
    · rintro rfl; simp [QuadForm.evalIn]
  rw [repNum, this, Nat.card_unique]

/-- **$\Theta_{E_8}$ as a modular form of weight 4 for $\mathrm{SL}_2(\mathbb{Z})$** (`thetaMF` with $n = 8$, $k = 4$):
$\Theta_{E_8}(\tau) = \sum_{\vec{x} \in \mathbb{Z}^8} e(\tau\, Q_{E_8}(\vec{x}))$. -/
@[kb "serre1973" "Ch. VII §6.5, Thm. 7 [unverified]"]
noncomputable def thetaE8 : ModularForm 𝒮ℒ 4 :=
  thetaMF e8_posDef e8_det (k := 4) rfl (dvd_refl 4)

/-- **$\Theta_{E_8} = E_4$** as modular forms, $E_4$ Mathlib's normalized weight-4 Eisenstein series (constant term
1). *Proof:* $\dim_{\mathbb{C}} M_4(\mathrm{SL}_2(\mathbb{Z})) = 1$ and $E_4 \ne 0$, so $\Theta_{E_8} = c\,E_4$; comparing
constant terms ($r_{E_8}(0) = 1$) gives $c = 1$. -/
@[kb "serre1973" "Ch. VII §6.6, Example 1 [unverified]"]
theorem thetaE8_eq_E₄ : thetaE8 = E₄ := by
  have hE : E₄ ≠ 0 := E_ne_zero (by norm_num) ⟨2, rfl⟩
  have hr : Module.finrank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
    Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' E₄ hE).mp hr thetaE8
  have h0 := congrArg (fun f : ModularForm 𝒮ℒ 4 => (qExpansion 1 f).coeff 0) hc
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, E_qExpansion_coeff_zero (k := 4) _ ⟨2, rfl⟩, thetaE8, qExpansion_thetaMF_coeff,
    Nat.cast_zero, repNum_zero_of_posDef e8_posDef] at h0
  rw [← hc, show c = 1 by simpa using h0, one_smul]

/-- **The representation numbers of $E_8$:** for $m \ge 1$,
$$r_{E_8}(m) = \#\{\vec{x} \in \mathbb{Z}^8 : Q_{E_8}(\vec{x}) = m\} = 240\,\sigma_3(m), \qquad \sigma_3(m) = \sum_{d \mid m} d^3.$$
*Proof:* compare $q$-expansion coefficients in `thetaE8_eq_E₄` (`qExpansion_thetaMF_coeff`, Mathlib's
`EisensteinSeries.E_qExpansion_coeff`); the factor $-2k/B_k = 240$ is read off from `E₄_qExpansion_coeff_one`. -/
@[kb "serre1973" "Ch. VII §6.6, Example 1 [unverified]"]
theorem repNum_e8 {m : ℕ} (hm : 1 ≤ m) : repNum e8 m = 240 * σ 3 m := by
  have h := qExpansion_thetaMF_coeff e8_posDef e8_det (k := 4) rfl (dvd_refl 4) m
  have h1 := E₄_qExpansion_coeff_one
  rw [E_qExpansion_coeff (k := 4) _ ⟨2, rfl⟩] at h1
  simp only [one_ne_zero, ↓reduceIte,
    show (σ (4 - 1) 1 : ℂ) = 1 by simp [ArithmeticFunction.sigma_apply], mul_one] at h1
  change (qExpansion 1 thetaE8).coeff m = _ at h
  have hm0 : m ≠ 0 := by omega
  rw [thetaE8_eq_E₄, E_qExpansion_coeff (k := 4) _ ⟨2, rfl⟩] at h
  simp only [hm0, ↓reduceIte, h1] at h
  exact_mod_cast h.symm

/-- **$E_8$ has 240 roots** (vectors with $Q_{E_8}(\vec{x}) = 1$, i.e. $\vec{x}^{\mathsf T} C\vec{x} = 2$). -/
theorem repNum_e8_one : repNum e8 1 = 240 := by
  simpa [ArithmeticFunction.sigma_apply] using repNum_e8 (m := 1) le_rfl

/-- $r_{E_8}(2) = 240 \cdot 9 = 2160$. -/
theorem repNum_e8_two : repNum e8 2 = 2160 := by
  have h := repNum_e8 (m := 2) (by norm_num)
  rw [show σ 3 2 = 9 by decide] at h
  exact_mod_cast h

end QuadFormsKB.Siegel
