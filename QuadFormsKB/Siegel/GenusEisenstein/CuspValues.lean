/-
# Constant terms of a weight-2 form on $\Gamma_1(N)$ at the cusps
For $f \in M_2(\Gamma_1(N))$ (Mathlib's `ModularForm (Gamma1 N) 2`) and $\gamma \in \mathrm{SL}_2(\mathbb{Z})$:

* `tendsto_cuspVal`: $f\,|_2\,\gamma \to c_f(\gamma)$ at $i\infty$, with $c_f(\gamma)$ the constant term of the $q$-expansion of
  $f|\gamma$ in $q_N = e(\tau/N)$ (`cuspVal`; $f|\gamma$ has period $N$ since $\gamma T^N\gamma^{-1} \in \Gamma(N) \le \Gamma_1(N)$).
* `cuspVal_eq_of_cuspVec_eq`: $c_f(\gamma)$ depends only on $v(\gamma) = (-\gamma_{10}, \gamma_{00}) \bmod N$ (`cuspVec`):
  if $v(\gamma) = v(\gamma')$ then $\gamma^{-1}\gamma' = T^k\varepsilon$ with $\varepsilon \in \Gamma(N)$, and $f|\gamma T^k$ is
  $\Gamma(N)$-invariant ($\Gamma(N)$ is normal).
* `cuspVal_neg`, `cuspVal_T_mul`: $c_f(-\gamma) = c_f(\gamma)$ (even weight), $c_f(T^j\gamma) = c_f(\gamma)$.
-/
import QuadFormsKB.Siegel.EisensteinWt2.Cusps
import Mathlib.NumberTheory.ModularForms.QExpansion
import QuadFormsKB.Citation

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

variable {N : ℕ} [NeZero N]

local notation "Γ₁" => CongruenceSubgroup.Gamma1

/-- $f\,|_2\,\delta = f$ for $\delta \in \Gamma_1(N)$. -/
lemma slash_of_mem_gamma1 (f : ModularForm (Γ₁ N) 2) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ₁ N) :
    (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] δ = ⇑f := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ ⟨δ, hδ, rfl⟩

lemma gamma_le_gamma1 {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) : δ ∈ Γ₁ N := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ
  rw [CongruenceSubgroup.Gamma1_mem]
  exact ⟨hδ.1, hδ.2.2.2, hδ.2.2.1⟩

/-- $f|\eta$ is invariant under $\Gamma(N)$, for every $\eta \in \mathrm{SL}_2(\mathbb{Z})$. -/
lemma slash_slash_of_mem_gamma (f : ModularForm (Γ₁ N) 2) (η : SL(2, ℤ)) {ε : SL(2, ℤ)}
    (hε : ε ∈ CongruenceSubgroup.Gamma N) :
    ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] η) ∣[(2 : ℤ)] ε = (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] η := by
  have hc : η * ε * η⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem ε hε η
  rw [← SlashAction.slash_mul, show η * ε = (η * ε * η⁻¹) * η by group, SlashAction.slash_mul,
    slash_of_mem_gamma1 f (gamma_le_gamma1 hc)]

lemma T_zpow_mem_gamma : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem, ModularGroup.coe_T_zpow]
  simp

lemma slash_T_zpow_apply (g : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (g ∣[(2 : ℤ)] (ModularGroup.T ^ k)) τ = g ((k : ℝ) +ᵥ τ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, ModularGroup.coe_T_zpow,
    UpperHalfPlane.modular_T_zpow_smul]
  simp

/-- $f|\gamma$ has period $N$. -/
lemma periodic_slash (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) :
    Function.Periodic (((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) ∘ UpperHalfPlane.ofComplex) (N : ℝ) :=
  UpperHalfPlane.periodic_comp_ofComplex fun τ => by
    have h := congrFun (slash_slash_of_mem_gamma f γ (T_zpow_mem_gamma (N := N))) τ
    rw [slash_T_zpow_apply] at h
    simpa using h

lemma mdiff_slash (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) :
    MDiff ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) := by
  rw [ModularForm.SL_slash]
  exact (ModularFormClass.holo f).slash _ _

/-- **The constant term of $f$ at the cusp $\gamma\infty$**: the $0$-th coefficient of the $q_N$-expansion of $f|_2\gamma$. -/
noncomputable def cuspVal (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) : ℂ :=
  (UpperHalfPlane.qExpansion (N : ℝ) ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ)).coeff 0

lemma hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- $f\,|_2\,\gamma \to c_f(\gamma)$ at $i\infty$. -/
theorem tendsto_cuspVal (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) :
    Tendsto ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 (cuspVal f γ)) :=
  UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion hN_pos
    (UpperHalfPlane.hasSum_qExpansion hN_pos (periodic_slash f γ) (mdiff_slash f γ)
      (ModularFormClass.bdd_at_infty_slash f γ))

lemma cuspVal_eq_of_tendsto (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) {L : ℂ}
    (h : Tendsto ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 L)) : cuspVal f γ = L :=
  tendsto_nhds_unique (tendsto_cuspVal f γ) h

lemma tendsto_slash_T_zpow' {g : ℍ → ℂ} {L : ℂ} (h : Tendsto g UpperHalfPlane.atImInfty (𝓝 L)) (k : ℤ) :
    Tendsto (g ∣[(2 : ℤ)] (ModularGroup.T ^ k)) UpperHalfPlane.atImInfty (𝓝 L) := by
  have hmap : Tendsto (fun τ : ℍ => (k : ℝ) +ᵥ τ) UpperHalfPlane.atImInfty UpperHalfPlane.atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    refine (tendsto_comap (f := UpperHalfPlane.im)).congr fun τ => ?_
    simp
  exact (h.comp hmap).congr fun τ => (slash_T_zpow_apply g k τ).symm

/-- $v(\gamma) = (-\gamma_{10}, \gamma_{00}) \bmod N$: the first column of $\gamma$ (up to the sign of the lower entry), the
datum on which the constant term at $\gamma\infty$ depends. -/
def cuspVec (N : ℕ) (γ : SL(2, ℤ)) : ZMod N × ZMod N :=
  (((-γ 1 0 : ℤ) : ZMod N), ((γ 0 0 : ℤ) : ZMod N))

lemma det_SL' (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rw [Matrix.det_fin_two] at this; exact this

/-- **$c_f(\gamma)$ depends only on $v(\gamma)$.** -/
theorem cuspVal_eq_of_cuspVec_eq (f : ModularForm (Γ₁ N) 2) {γ γ' : SL(2, ℤ)}
    (h : cuspVec N γ = cuspVec N γ') : cuspVal f γ = cuspVal f γ' := by
  simp only [cuspVec, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : ((γ 1 0 : ℤ) : ZMod N) = ((γ' 1 0 : ℤ) : ZMod N) := by
    have := congrArg Neg.neg h1; push_cast at this; simpa using this
  set δ := γ⁻¹ * γ' with hδ
  have hd := det_SL' γ
  have hd' := det_SL' γ'
  have hdδ := det_SL' δ
  -- entries of δ = γ⁻¹ γ'
  have e00 : δ 0 0 = γ 1 1 * γ' 0 0 - γ 0 1 * γ' 1 0 := by
    rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have e10 : δ 1 0 = -(γ 1 0) * γ' 0 0 + γ 0 0 * γ' 1 0 := by
    rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
  have m00 : ((δ 0 0 : ℤ) : ZMod N) = 1 := by
    rw [e00]; push_cast; rw [← h2, ← h1']
    have := congrArg (fun x : ℤ => (x : ZMod N)) hd; push_cast at this; linear_combination this
  have m10 : ((δ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [e10]; push_cast; rw [← h2, ← h1']; ring
  have m11 : ((δ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod N)) hdδ
    push_cast at this; rw [m00, m10] at this; linear_combination this
  set k : ℤ := δ 0 1 with hk
  set ε := ModularGroup.T ^ (-k) * δ with hε
  have hεmem : ε ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem]
    rw [hε, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [one_mul]; rw [m00, m10]; ring
    · simp only [one_mul]; rw [m11, hk]; ring
    · simp only [zero_mul, zero_add, one_mul]; exact m10
    · simp only [zero_mul, zero_add, one_mul]; exact m11
  have hγ' : γ' = γ * ModularGroup.T ^ k * ε := by
    rw [hε, hδ]; group
  have hfun : (⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ' = ((⇑f : ℍ → ℂ) ∣[(2 : ℤ)] γ) ∣[(2 : ℤ)] (ModularGroup.T ^ k) := by
    rw [hγ', SlashAction.slash_mul, slash_slash_of_mem_gamma f _ hεmem, SlashAction.slash_mul]
  symm
  apply cuspVal_eq_of_tendsto
  rw [hfun]
  exact tendsto_slash_T_zpow' (tendsto_cuspVal f γ) k

lemma slash_neg (g : ℍ → ℂ) (γ : SL(2, ℤ)) : g ∣[(2 : ℤ)] (-γ) = g ∣[(2 : ℤ)] γ := by
  ext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul,
    ModularGroup.denom_apply, ModularGroup.denom_apply]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
  congr 1
  rw [show (-((γ 1 0 : ℤ) : ℂ) * τ + -((γ 1 1 : ℤ) : ℂ)) = -(((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) by ring,
    Even.neg_zpow (by decide)]

/-- $c_f(-\gamma) = c_f(\gamma)$ (weight $2$ is even). -/
theorem cuspVal_neg (f : ModularForm (Γ₁ N) 2) (γ : SL(2, ℤ)) : cuspVal f (-γ) = cuspVal f γ := by
  rw [cuspVal, slash_neg]; rfl

lemma T_zpow_mem_gamma1 (j : ℤ) : ModularGroup.T ^ j ∈ Γ₁ N := by
  rw [CongruenceSubgroup.Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

/-- $c_f(T^j\gamma) = c_f(\gamma)$. -/
theorem cuspVal_T_mul (f : ModularForm (Γ₁ N) 2) (j : ℤ) (γ : SL(2, ℤ)) :
    cuspVal f (ModularGroup.T ^ j * γ) = cuspVal f γ := by
  rw [cuspVal, SlashAction.slash_mul, slash_of_mem_gamma1 f (T_zpow_mem_gamma1 j)]; rfl

lemma cuspVec_neg (γ : SL(2, ℤ)) : cuspVec N (-γ) = -cuspVec N γ := by
  simp [cuspVec, Matrix.SpecialLinearGroup.coe_neg]

lemma cuspVec_T_mul (j : ℤ) (γ : SL(2, ℤ)) :
    cuspVec N (ModularGroup.T ^ j * γ) = ((cuspVec N γ).1, (cuspVec N γ).2 - j * (cuspVec N γ).1) := by
  simp only [cuspVec, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- $v(\gamma)$ is primitive: $s\,v_1 + t\,v_2 = 1$ for some $s, t \in \mathbb{Z}/N$. -/
lemma cuspVec_prim (γ : SL(2, ℤ)) :
    ∃ s t : ZMod N, s * (cuspVec N γ).1 + t * (cuspVec N γ).2 = 1 := by
  refine ⟨((γ 0 1 : ℤ) : ZMod N), ((γ 1 1 : ℤ) : ZMod N), ?_⟩
  have := congrArg (fun x : ℤ => (x : ZMod N)) (det_SL' γ)
  simp only [cuspVec]; push_cast at this ⊢; linear_combination this

/-- Every primitive-by-an-integer-pair vector is some $v(\gamma)$: for coprime integers $x$, $y$ there is $\gamma$ with
$(-\gamma_{10}, \gamma_{00}) = (x, y)$. -/
lemma exists_SL_of_isCoprime {x y : ℤ} (h : IsCoprime x y) :
    ∃ γ : SL(2, ℤ), γ 1 0 = -x ∧ γ 0 0 = y := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨⟨!![y, u; -x, v], ?_⟩, by simp, by simp⟩
  rw [Matrix.det_fin_two_of]; linear_combination huv

end QuadFormsKB.Siegel.GenusEis
