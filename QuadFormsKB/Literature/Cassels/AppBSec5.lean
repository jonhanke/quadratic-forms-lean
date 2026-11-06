/-
# Cassels, Appendix B, §5: consequences of the modularity of theta series at level one

**Layer:** positive definite integral forms $Q$ in $n = 2k$ variables with $\det H = 1$ and $4 \mid k$ (even unimodular
lattices; Cassels: improperly primitive forms of determinant $1$, Stufe $N = 1$), their theta series
$\Theta_Q = \sum_m r_Q(m)q^m \in M_k(\mathrm{SL}_2(\mathbb Z))$ (`Siegel.thetaMF`, `Siegel.qExpansion_thetaMF_coeff`), and
Mathlib's level-one theory (the Sturm bound `sturm_bound_levelOne_nat`, the Eisenstein series `E`, the discriminant
`ModularForm.discriminant`).

**Proves** (Cassels, App. B, §5, pp. 386–387)
* `repNum_linear_relation` (p. 387, case $N = 1$): a linear relation $\sum_j b_jr_{f_j}(m) = 0$ between the
  representation numbers of forms $f_j$ of this kind holds for all $m$ as soon as it holds for $m \le k/12$ (Cassels:
  "for the first $m_0$ coefficients"; at level one $m_0 = [k/12] + 1$ by the Sturm bound);
* `witt_sixteen` (p. 386, Witt 1941): $\Gamma_{16}$ and $2\Gamma_8 = E_8 \perp E_8$ lie in one genus, are not equivalent,
  and represent every integer the same number of times;
* `repNum_rank24` (p. 387): for an even unimodular $Q$ in $24$ variables,
  $r_Q(m) = e_{12}(m) + (r_Q(1) - e_{12}(1))\,\tau(m)$ for $m \ge 1$, where $e_{12}(m)$ is the $m$-th coefficient of the
  normalized Eisenstein series $E_{12}$ ($= \tfrac{65520}{691}\sigma_{11}(m)$) and $\tau(m)$ that of $\Delta$
  (Ramanujan's function): the cusp forms of weight $12$ are the multiples of $\Delta$.

*Not formalized:* the sum of $24$ squares (level $4$), and the statement that the genus of $\Gamma_{16}$ has exactly two
classes.
-/
import QuadFormsKB.Literature.Cassels.AppA.Gamma16Genus
import QuadFormsKB.Literature.Cassels.AppBCitations

open Matrix ModularForm EisensteinSeries
open UpperHalfPlane hiding I

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel
open scoped MatrixGroups

/-- **A level-one linear relation between theta series** (Cassels, App. B, §5, p. 387, for Stufe $N = 1$): let
$f_j$ ($j \in s$) be positive definite integral forms in $n = 2k$ variables with $\det H = 1$, $4 \mid k$, and
$b_j \in \mathbb C$. If $\sum_j b_jr_{f_j}(m) = 0$ for $0 \le m \le k/12$, then $\sum_j b_jr_{f_j}(m) = 0$ for every $m$. -/
@[kb "cassels1978" "App. B, §5, p. 387 (a relation Σ b_j Θ(f_j, t) = 0 follows from the first m₀ coefficients; N = 1)"]
theorem repNum_linear_relation {n k : ℕ} (hn : n = 2 * k) (hk : 4 ∣ k) {ι : Type*} (s : Finset ι)
    (f : ι → IntQF n) (hf : ∀ j ∈ s, (f j).PosDef) (hdet : ∀ j ∈ s, (f j).hessian.det = 1) (b : ι → ℂ)
    (h : ∀ m : ℕ, m ≤ k / 12 → ∑ j ∈ s, b j * (repNum (f j) m : ℂ) = 0) (m : ℕ) :
    ∑ j ∈ s, b j * (repNum (f j) m : ℂ) = 0 := by
  let F : ModularForm 𝒮ℒ (k : ℤ) := ∑ j ∈ s.attach, b j • thetaMF (hf j j.2) (hdet j j.2) hn hk
  have hcoeff : ∀ m : ℕ, (qExpansion 1 F).coeff m = ∑ j ∈ s, b j * (repNum (f j) m : ℂ) := by
    intro m
    have h1 : qExpansion 1 F = ∑ j ∈ s.attach,
        b j • qExpansion 1 (thetaMF (hf j j.2) (hdet j j.2) hn hk) := by
      have := map_sum (ModularForm.qExpansionAddHom (Γ := 𝒮ℒ) (h := 1) one_pos one_mem_strictPeriods_SL
        (k : ℤ)) (fun j : s => b j • thetaMF (hf j j.2) (hdet j j.2) hn hk) s.attach
      simp only [ModularForm.qExpansionAddHom_apply] at this
      rw [show F = _ from rfl, this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [FunLike.coe_smul]
      exact ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (b j)
        (thetaMF (hf j j.2) (hdet j j.2) hn hk)
    rw [h1, map_sum, ← Finset.sum_attach s]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_smul, qExpansion_thetaMF_coeff, smul_eq_mul]
  have hF : F = 0 := by
    apply sturm_bound_levelOne_nat
    refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ (k / 12 + 1) ?_)
    intro i hi
    rw [hcoeff]
    exact h i (by omega)
  have := hcoeff m
  rw [hF] at this
  rw [show ⇑(0 : ModularForm 𝒮ℒ (k : ℤ)) = 0 from rfl, qExpansion_zero] at this
  simpa using this.symm

/-- The sum-of-squares form over $\mathbb Q$ evaluates to $\sum x_i^2$. -/
private theorem sumSq_eval' {n : ℕ} (x : Fin n → ℚ) : (sumSqForm n).eval x = ∑ i, x i ^ 2 := by
  rw [sumSqForm, QuadForm.eval, QuadForm.evalIn_diag]; simp

/-- $\gamma_{16}$ is positive definite. -/
theorem gamma16_posDef : IntQF.PosDef gamma16 := by
  intro c hc
  have h2 := two_mul_gamma16_eval c
  have hne : gamma16Basis *ᵥ (fun i => (c i : ℚ)) ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_gamma16Basis]; exact one_ne_zero) h0
    apply hc
    ext i
    have := congrFun h1 i
    simpa using this
  have hpos : 0 < (sumSqForm 16).eval (gamma16Basis *ᵥ fun i => (c i : ℚ)) := by
    rw [sumSq_eval']
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hi2 : 0 < ((gamma16Basis *ᵥ fun i => (c i : ℚ)) i) ^ 2 := by
      have hi' : (gamma16Basis *ᵥ fun i => (c i : ℚ)) i ≠ 0 := hi
      positivity
    exact lt_of_lt_of_le hi2
      (Finset.single_le_sum (f := fun i => (gamma16Basis *ᵥ fun i => (c i : ℚ)) i ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i))
  rw [← h2] at hpos
  have : (0 : ℚ) < ((gamma16.eval c : ℤ) : ℚ) := by linarith
  exact_mod_cast this

/-- $E_8 \perp E_8$ is positive definite. -/
theorem twoE8_posDef : IntQF.PosDef twoE8 := by
  intro x hx
  have h := QuadForm.evalIn_orthSum ℤ e8 e8 x
  change twoE8.eval x = _ at h
  rw [h]
  by_cases h1 : (fun a : Fin 8 => x (Fin.castAdd 8 a)) = 0
  · have h2 : (fun a : Fin 8 => x (Fin.natAdd 8 a)) ≠ 0 := by
      intro h2
      apply hx
      ext i
      obtain ⟨i', rfl⟩ := (finSumFinEquiv (m := 8) (n := 8)).surjective i
      rcases i' with a | a
      · exact congrFun h1 a
      · exact congrFun h2 a
    have := e8_posDef _ h2
    have h0 : e8.evalIn ℤ (fun a : Fin 8 => x (Fin.castAdd 8 a)) = 0 := by
      rw [h1]; simp [QuadForm.evalIn]
    rw [h0]
    exact (by simpa [QuadForm.eval] using this)
  · have := e8_posDef _ h1
    have h3 : 0 ≤ e8.evalIn ℤ (fun a : Fin 8 => x (Fin.natAdd 8 a)) := by
      by_cases h2 : (fun a : Fin 8 => x (Fin.natAdd 8 a)) = 0
      · rw [h2]; simp [QuadForm.evalIn]
      · exact (e8_posDef _ h2).le
    have h4 : 0 < e8.evalIn ℤ (fun a : Fin 8 => x (Fin.castAdd 8 a)) := this
    omega

/-- The coefficient matrix of an orthogonal sum, entrywise. -/
private theorem orthSum_coeff_apply {m n : ℕ} (Q₁ : QuadForm ℤ m) (Q₂ : QuadForm ℤ n) (i j : Fin (m + n)) :
    (QuadForm.orthSum Q₁ Q₂).coeff i j = if i ≤ j then
      Fin.addCases (fun a => Fin.addCases (fun b => Q₁.coeff a b) (fun _ => 0) j)
        (fun a => Fin.addCases (fun _ => 0) (fun b => Q₂.coeff a b) j) i else 0 := rfl

/-- The upper-left block of the coefficient matrix of an orthogonal sum. -/
private theorem orthSum_coeff_ll {m n : ℕ} (Q₁ : QuadForm ℤ m) (Q₂ : QuadForm ℤ n) (a b : Fin m) :
    (QuadForm.orthSum Q₁ Q₂).coeff (Fin.castAdd n a) (Fin.castAdd n b) = Q₁.coeff a b := by
  rw [orthSum_coeff_apply, Fin.addCases_left, Fin.addCases_left]
  split_ifs with h
  · rfl
  · exact (Q₁.upper (Fin.lt_def.mpr (by simpa using Fin.lt_def.mp (not_le.mp h)))).symm

/-- The lower-right block of the coefficient matrix of an orthogonal sum. -/
private theorem orthSum_coeff_rr {m n : ℕ} (Q₁ : QuadForm ℤ m) (Q₂ : QuadForm ℤ n) (a b : Fin n) :
    (QuadForm.orthSum Q₁ Q₂).coeff (Fin.natAdd m a) (Fin.natAdd m b) = Q₂.coeff a b := by
  rw [orthSum_coeff_apply, Fin.addCases_right, Fin.addCases_right]
  split_ifs with h
  · rfl
  · exact (Q₂.upper (Fin.lt_def.mpr (by show b.val < a.val; have := Fin.lt_def.mp (not_le.mp h); simp at this; omega))).symm

/-- The upper-right block of the coefficient matrix of an orthogonal sum vanishes. -/
private theorem orthSum_coeff_lr {m n : ℕ} (Q₁ : QuadForm ℤ m) (Q₂ : QuadForm ℤ n) (a : Fin m) (b : Fin n) :
    (QuadForm.orthSum Q₁ Q₂).coeff (Fin.castAdd n a) (Fin.natAdd m b) = 0 := by
  rw [orthSum_coeff_apply, Fin.addCases_left, Fin.addCases_right]
  split_ifs <;> rfl

/-- The lower-left block of the coefficient matrix of an orthogonal sum vanishes. -/
private theorem orthSum_coeff_rl {m n : ℕ} (Q₁ : QuadForm ℤ m) (Q₂ : QuadForm ℤ n) (a : Fin n) (b : Fin m) :
    (QuadForm.orthSum Q₁ Q₂).coeff (Fin.natAdd m a) (Fin.castAdd n b) = 0 := by
  rw [orthSum_coeff_apply]
  split_ifs with h
  · exfalso
    have := Fin.le_def.mp h
    simp at this
    omega
  · rfl

/-- $E_8 \perp E_8$ is unimodular: $\det H = 1$. -/
theorem twoE8_det : twoE8.hessian.det = 1 := by
  have h : twoE8.hessian = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks e8.hessian 0 0 e8.hessian) := by
    ext i j
    obtain ⟨i', rfl⟩ := (finSumFinEquiv (m := 8) (n := 8)).surjective i
    obtain ⟨j', rfl⟩ := (finSumFinEquiv (m := 8) (n := 8)).surjective j
    rcases i' with a | a <;> rcases j' with b | b <;>
      (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
       simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right, twoE8, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply,
        orthSum_coeff_ll, orthSum_coeff_rr, orthSum_coeff_lr, orthSum_coeff_rl, add_zero])
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, e8_det]
  simp

/-- **Witt's example** (Cassels, App. B, §5, p. 386; Witt 1941): $\Gamma_{16}$ and $2\Gamma_8 = E_8 \perp E_8$ are in the
same genus (`gamma16_sameGenus`), are not equivalent (`gamma16_not_isometric`), and represent every integer the same
number of times, $r_{\Gamma_{16}}(m) = r_{2\Gamma_8}(m)$, since there are no non-zero cusp forms of weight $8$ and level
$1$. -/
@[kb "cassels1978" "App. B, §5, p. 386 (Witt: two classes of the genus of determinant 1 in 16 variables with equal theta series)"]
theorem witt_sixteen :
    Siegel.SameGenus gamma16 twoE8 ∧ ¬ IsometricGL gamma16 twoE8 ∧ ∀ m : ℤ, repNum gamma16 m = repNum twoE8 m := by
  refine ⟨gamma16_sameGenus, gamma16_not_isometric, fun m => ?_⟩
  have hneg : ∀ {Q : IntQF 16}, Q.PosDef → m < 0 → repNum Q m = 0 := by
    intro Q hQ hm
    have : repSet Q m = ∅ := by
      ext x
      simp only [repSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      by_cases hx0 : x = 0
      · subst hx0; simp [QuadForm.evalIn] at hx; omega
      · have := hQ x hx0
        omega
    rw [repNum, this]; simp
  rcases lt_or_ge m 0 with hm | hm
  · rw [hneg gamma16_posDef hm, hneg twoE8_posDef hm]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have key := repNum_linear_relation (n := 16) (k := 8) rfl (by norm_num) (Finset.univ : Finset (Fin 2))
      ![gamma16, twoE8]
      (fun j _ => by fin_cases j; exacts [gamma16_posDef, twoE8_posDef])
      (fun j _ => by fin_cases j; exacts [gamma16_det, twoE8_det]) ![1, -1]
      (fun m hm => by
        have : m = 0 := by omega
        subst this
        simp [Fin.sum_univ_two, repNum_zero_of_posDef gamma16_posDef, repNum_zero_of_posDef twoE8_posDef]) m
    simp only [Fin.sum_univ_two] at key
    simp at key
    have : (repNum gamma16 m : ℂ) = repNum twoE8 m := by linear_combination key
    exact_mod_cast this

/-- **Ramanujan's function** $\tau(m)$: the $m$-th $q$-expansion coefficient of $\Delta(z) = q\prod_{m \ge 1}(1 - q^m)^{24}$
(Cassels, App. B, (1.9), p. 370, and §5, p. 387). -/
@[kb "cassels1978" "App. B, (1.9), p. 370, and §5, p. 387 (Ramanujan's τ(m), the coefficients of Δ)"]
def ramanujanTau (m : ℕ) : ℂ := (qExpansion 1 ModularForm.discriminant).coeff m

/-- **Even unimodular lattices of rank 24** (Cassels, App. B, §5, p. 387): for $Q$ positive definite in $24$ variables
with $\det H = 1$ and $m \ge 1$,
$$r_Q(m) = e_{12}(m) + \bigl(r_Q(1) - e_{12}(1)\bigr)\tau(m),$$
where $e_{12}(m)$ is the $m$-th coefficient of the normalized Eisenstein series $E_{12}$ (Mathlib's `E`, constant term
$1$; $e_{12}(m) = \tfrac{65520}{691}\sigma_{11}(m)$) and $\tau$ is `ramanujanTau`. *Proof:* $\Theta_Q - E_{12}$ is a
cusp form of weight $12$, hence a multiple $c\Delta$; compare the coefficients of $q$ ($\tau(1) = 1$). -/
@[kb "cassels1978" "App. B, §5, p. 387 (k = 12, N = 1: representation numbers through E₁₂ and τ(m))"]
theorem repNum_rank24 {Q : IntQF 24} (hQ : Q.PosDef) (hdet : Q.hessian.det = 1) {m : ℕ} (hm : 1 ≤ m) :
    (repNum Q m : ℂ) = (qExpansion 1 (E (k := 12) (by norm_num))).coeff m +
      ((repNum Q 1 : ℂ) - (qExpansion 1 (E (k := 12) (by norm_num))).coeff 1) * ramanujanTau m := by
  clear hm
  have hev : Even 12 := ⟨6, rfl⟩
  set G := thetaMF hQ hdet (k := 12) rfl (by norm_num) with hG
  set E12 := E (k := 12) (by norm_num) with hE12
  have hGc : ∀ m : ℕ, (qExpansion 1 G).coeff m = repNum Q m := fun m => qExpansion_thetaMF_coeff hQ hdet _ _ m
  have hsub : ∀ m : ℕ, (qExpansion 1 (G - E12)).coeff m = (qExpansion 1 G).coeff m - (qExpansion 1 E12).coeff m := by
    intro m
    rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, map_sub]
  have h0 : (qExpansion 1 (G - E12)).coeff 0 = 0 := by
    rw [hsub, hGc, E_qExpansion_coeff_zero (k := 12) _ hev, Nat.cast_zero, repNum_zero_of_posDef hQ]
    simp
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm (G - E12) h0)
  have hfun : (⇑G - ⇑E12 : ℍ → ℂ) = c • ModularForm.discriminant := by
    have := congrArg DFunLike.coe hc
    exact this.symm
  have hq : ∀ m : ℕ, (qExpansion 1 G).coeff m - (qExpansion 1 E12).coeff m = c * ramanujanTau m := by
    intro m
    rw [← hsub, hfun]
    have := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant
    change qExpansion 1 (c • ModularForm.discriminant) = c • qExpansion 1 ModularForm.discriminant at this
    rw [this, PowerSeries.coeff_smul, smul_eq_mul]
    rfl
  have hc1 : c = (repNum Q 1 : ℂ) - (qExpansion 1 E12).coeff 1 := by
    have h1 := hq 1
    rw [hGc] at h1
    have : ramanujanTau 1 = 1 := discriminant_qExpansion_coeff_one
    rw [this, mul_one] at h1
    simpa using h1.symm
  have h2 := hq m
  rw [hGc, hc1] at h2
  rw [mul_comm]
  linear_combination h2

end QuadFormsKB.Lattices
