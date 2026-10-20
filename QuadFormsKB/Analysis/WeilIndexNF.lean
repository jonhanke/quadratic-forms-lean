import QuadFormsKB.Analysis.AdelicPoisson
import QuadFormsKB.Analysis.WeilIndex

/-!
# The Weil index at a finite place of a number field

For a finite place $v$ of a number field $F$, with the standard character $\psi_v$ (`psiV`) and the self-dual
measure (`selfDualV`), the general theory of `WeilIndex.lean` gives the **Weil constant**
$$\gamma_v(b) = \int_{\|x\|\le R}\psi_v(bx^2)\,dx_v \qquad (R \gg 0), \qquad b \in F_v^\times$$
(`weilV`). This file proves what the global argument needs:

* `weilV_identity`: $\mathcal F\big(\psi_v(bx^2)\,\widehat{\mathbf 1_{\mathcal O_v}}\big)(y) =
  \gamma_v(b)\,\psi_v(cy^2)\,\mathcal F\big(\mathbf 1_{\mathcal O_v}\psi_v(cx^2)\big)(2cy)$, $c = -1/(4b)$;
* `weilV_eq_one`: $\gamma_v(b) = 1$ if $v \nmid 2$, $d_v = 0$ and $b \in \mathcal O_v^\times$;
* `finite_weilV_ne_one`: for $b \in F^\times$, $\gamma_v(b) = 1$ for all but finitely many $v$;
* `isSchwartzBruhatV_chirp`: $x \mapsto \mathbf 1_{\mathfrak p_v^k}(x)\,\psi_v(bx^2)$ is Schwartz–Bruhat.
-/

open IsDedekindDomain NumberField WithZero MeasureTheory
open scoped NNReal

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

lemma norm_le_one_iff_valued {x : Fv} : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff

/-- $\psi_v$ is a standard character: continuous, trivial on $\mathcal O_v$, nontrivial. -/
theorem isStdChar_psiV : Weil.IsStdChar (psiV v) where
  cont := continuous_psiV v
  triv := ⟨1, one_pos, fun x hx => psiV_eq_one_of_le_one v ((norm_le_one_iff_valued v).mp hx)⟩
  nontriv := ⟨_, psiV_nontrivial v⟩

/-- **The Weil constant at a finite place:** $\gamma_v(b) = \int_{\|x\|\le R}\psi_v(bx^2)\,dx_v$ for $R$ large
(self-dual measure). Weil's index of $x \mapsto \psi_v(bx^2)$ is $\gamma_v(b)/|\gamma_v(b)|$. -/
@[kb "weil1964" "§14 (the index $\\gamma(f)$ of a character of second degree) [unverified]"]
def weilV (b : Fv) : ℂ := Weil.gaussInt (selfDualV v) (psiV v) b

lemma ballIndV_zero (k : ℤ) : ballIndV v 0 k = (latticeV v k : Set Fv).indicator 1 := by
  ext x
  simp only [ballIndV, sub_zero]
  rfl

lemma latticeV_zero_eq_bsub : (latticeV v 0 : Set Fv) = (Weil.bsub Fv 1 : Set Fv) := by
  ext x
  simp only [SetLike.mem_coe, mem_latticeV, neg_zero, exp_zero, Weil.mem_bsub, NNReal.coe_one]
  exact (norm_le_one_iff_valued v).symm

lemma ballIndV_zero_zero : ballIndV v 0 0 = (Weil.bsub Fv 1 : Set Fv).indicator 1 := by
  rw [ballIndV_zero, latticeV_zero_eq_bsub]

/-- **The Weil identity at a finite place** for $\varphi = \mathbf 1_{\mathcal O_v}$:
$$\mathcal F\big(x\mapsto\psi_v(bx^2)\,\widehat{\mathbf 1_{\mathcal O_v}}(x)\big)(y) =
  \gamma_v(b)\,\psi_v(cy^2)\,\mathcal F\big(x\mapsto\mathbf 1_{\mathcal O_v}(x)\psi_v(cx^2)\big)(2cy), \qquad c = -\tfrac1{4b}.$$ -/
@[kb "weil1964" "§14, Thm. 2 (local Weil identity) [unverified]"]
theorem weilV_identity {b : Fv} (hb : b ≠ 0) (y : Fv) :
    fourierV v (fun x => (psiV v (b * x ^ 2) : ℂ) * fourierV v (ballIndV v 0 0) x) y =
      weilV v b * (psiV v (-(4 * b)⁻¹ * y ^ 2) : ℂ) *
        fourierV v (fun x => ballIndV v 0 0 x * (psiV v (-(4 * b)⁻¹ * x ^ 2) : ℂ))
          (2 * (-(4 * b)⁻¹) * y) := by
  rw [ballIndV_zero_zero]
  exact Weil.weil_identity_ball (isStdChar_psiV v) two_ne_zero hb one_pos y

/-- $\operatorname{vol}(\mathcal O_v) = 1$ when $d_v = 0$. -/
lemma selfDualV_real_Ov_of_diffExp (hd : diffExp v = 0) : (selfDualV v).real (latticeV v 0) = 1 := by
  rw [selfDualV_real_latticeV, hd]; simp

/-- **The Weil constant is $1$ at good places:** if $v \nmid 2$, $d_v = 0$ and $v(b) = 1$, then $\gamma_v(b) = 1$. -/
theorem weilV_eq_one (hd : diffExp v = 0) (h2 : Valued.v (2 : Fv) = 1) {b : Fv}
    (hb : Valued.v b = 1) : weilV v b = 1 := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  obtain ⟨R₀, hR₀⟩ := Weil.gaussInt_spec (μ := selfDualV v) (isStdChar_psiV v) two_ne_zero hb0
  set R := max R₀ 1
  unfold weilV
  rw [← hR₀ R (le_max_left _ _)]
  have hεt : ∀ h : Fv, ‖h‖ ≤ (1 : ℝ≥0) → psiV v (b * h ^ 2) = 1 := by
    intro h hh
    refine psiV_eq_one_of_le_one v ?_
    have : Valued.v h ≤ 1 := (norm_le_one_iff_valued v).mp (by exact_mod_cast hh)
    rw [map_mul, map_pow, hb, one_mul]
    exact pow_le_one₀ zero_le this
  rw [Weil.gaussI_eq_of_ge (continuous_psiV v) one_pos hεt le_rfl (le_max_right _ _)]
  · -- the integral over `O_v`
    unfold Weil.gaussI
    rw [setIntegral_congr_fun (Weil.measurableSet_bsub _) (g := fun _ => (1 : ℂ))
      (fun x hx => by rw [hεt x hx, Circle.coe_one]), setIntegral_const, ← latticeV_zero_eq_bsub,
      selfDualV_real_Ov_of_diffExp v hd]
    simp
  · intro x hx
    have hx1 : 1 < Valued.v x := by
      by_contra h
      exact absurd ((norm_le_one_iff_valued v).mpr (not_lt.mp h)) (not_le.mpr (by exact_mod_cast hx))
    have hnot : 2 * b * x ∉ invDiffV v := by
      rw [mem_invDiffV_iff, hd, Nat.cast_zero, exp_zero, map_mul, map_mul, h2, hb, one_mul, one_mul]
      exact not_le.mpr hx1
    simp only [invDiffV, Set.mem_ofPred_eq, not_forall] at hnot
    obtain ⟨h, hh, hne⟩ := hnot
    refine ⟨h, by exact_mod_cast (norm_le_one_iff_valued v).mpr hh, ?_⟩
    rwa [mul_comm]

/-- **$\gamma_v(b) = 1$ for almost all $v$:** for $b \in F^\times$, the set of finite places with $\gamma_v(b) \ne 1$ is
finite. -/
theorem finite_weilV_ne_one (b : F) (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | weilV v (algebraMap F (v.adicCompletion F) b) ≠ 1}.Finite := by
  refine ((finite_support_diffExp.union (HeightOneSpectrum.Support.finite (𝓞 F) b)).union
    ((HeightOneSpectrum.Support.finite (𝓞 F) b⁻¹).union
      (HeightOneSpectrum.Support.finite (𝓞 F) (2 : F)⁻¹))).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Function.mem_support, HeightOneSpectrum.Support, Set.mem_ofPred_eq,
    not_or, not_not, not_lt] at hc
  obtain ⟨⟨hd, hb1⟩, hbi, h2i⟩ := hc
  apply hw
  have hv0 : w.valuation F b ≠ 0 := by simpa using hb
  have hb' : w.valuation F b = 1 := by
    rw [map_inv₀] at hbi
    exact le_antisymm hb1 (by
      have := (inv_le_one₀ (pos_iff_ne_zero.mpr hv0)).mp hbi
      exact this)
  have h2' : w.valuation F (2 : F) = 1 := by
    have h2le : w.valuation F (2 : F) ≤ 1 := by
      have := w.valuation_le_one (K := F) ((2 : ℕ) : 𝓞 F)
      exact_mod_cast this
    have hv2 : w.valuation F (2 : F) ≠ 0 := by simp
    rw [map_inv₀] at h2i
    exact le_antisymm h2le ((inv_le_one₀ (pos_iff_ne_zero.mpr hv2)).mp h2i)
  refine weilV_eq_one w (by exact_mod_cast hd) ?_ ?_
  · rw [show (2 : w.adicCompletion F) = algebraMap F _ 2 from (map_ofNat _ 2).symm, HN.valued_algebraMap, h2']
  · rw [HN.valued_algebraMap, hb']

/-- A scalar multiple of a Schwartz–Bruhat function is Schwartz–Bruhat. -/
lemma IsSchwartzBruhatV.const_mul {f : Fv → ℂ} (hf : IsSchwartzBruhatV v f) (a : ℂ) :
    IsSchwartzBruhatV v (fun x => a * f x) := by
  obtain ⟨n, c, d, k, rfl⟩ := hf
  exact ⟨n, fun i => a * c i, d, k, by ext x; simp [Finset.mul_sum, mul_assoc]⟩

/-- **Chirped lattice indicators are Schwartz–Bruhat:** $x \mapsto \mathbf 1_{\mathfrak p_v^k}(x)\,\psi_v(bx^2)$ is a
finite linear combination of coset indicators (it is constant on the cosets of a small $\mathfrak p_v^m$). -/
theorem isSchwartzBruhatV_chirp (k : ℤ) (b : Fv) :
    IsSchwartzBruhatV v (fun x => ballIndV v 0 k x * (psiV v (b * x ^ 2) : ℂ)) := by
  obtain ⟨β, hβ⟩ := exists_valued_le_exp b
  set m : ℤ := max k (max ((β : ℤ) - k) β)
  have hkm : k ≤ m := le_max_left _ _
  have hinv : ∀ x ∈ latticeV v k, ∀ h ∈ latticeV v m,
      (psiV v (b * (x + h) ^ 2) : ℂ) = (psiV v (b * x ^ 2) : ℂ) := by
    intro x hx h hh
    rw [mem_latticeV] at hx hh
    have h2 : Valued.v (2 : Fv) ≤ 1 := by
      have := (norm_le_one_iff_valued v).mp (show ‖(2 : Fv)‖ ≤ 1 from by
        rw [show (2 : Fv) = ((2 : ℕ) : Fv) by norm_num]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      exact this
    have hsmall : Valued.v (2 * b * x * h + b * h ^ 2) ≤ 1 := by
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul, map_mul, map_mul]
        calc Valued.v (2 : Fv) * Valued.v b * Valued.v x * Valued.v h ≤
            1 * exp (β : ℤ) * exp (-k) * exp (-m) := by gcongr
          _ = exp ((β : ℤ) - k - m) := by rw [one_mul, ← exp_add, ← exp_add]; congr 1
          _ ≤ 1 := by
            rw [← exp_zero, exp_le_exp]
            have : (β : ℤ) - k ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
            linarith
      · rw [map_mul, map_pow]
        calc Valued.v b * Valued.v h ^ 2 ≤ exp (β : ℤ) * exp (-m) ^ 2 := by gcongr
          _ = exp ((β : ℤ) - 2 * m) := by rw [← exp_nsmul, ← exp_add]; congr 1; simp; ring
          _ ≤ 1 := by
            rw [← exp_zero, exp_le_exp]
            have h1 : (β : ℤ) ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
            have h0 : (0 : ℤ) ≤ β := Int.natCast_nonneg β
            linarith
    rw [show b * (x + h) ^ 2 = b * x ^ 2 + (2 * b * x * h + b * h ^ 2) by ring, AddChar.map_add_eq_mul,
      psiV_eq_one_of_le_one v hsmall, mul_one]
  have hLc : IsCompact (latticeV v k : Set Fv) := isCompact_latticeV v k
  have hPo : IsOpen (latticeV v m : Set Fv) := by
    rw [coe_latticeV]
    exact IsUltrametricDist.isOpen_closedBall _ (norm_ne_zero_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v)))
  have hPL : latticeV v m ≤ latticeV v k := fun x hx => by
    rw [mem_latticeV] at hx ⊢
    exact hx.trans (exp_le_exp.mpr (by linarith))
  obtain ⟨n, c, -, hsum⟩ := Weil.exists_coset_sum (latticeV v k) (latticeV v m) hLc hPo hPL
    (fun x => (psiV v (b * x ^ 2) : ℂ)) hinv
  refine ⟨n, fun i => (psiV v (b * c i ^ 2) : ℂ), c, fun _ => m, ?_⟩
  ext x
  rw [ballIndV_zero]
  have := hsum x
  by_cases hx : x ∈ (latticeV v k : Set Fv)
  · rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul]
    rw [Set.indicator_of_mem hx] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
  · rw [Set.indicator_of_notMem hx, zero_mul]
    rw [Set.indicator_of_notMem hx] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1

end

end QuadFormsKB.Analysis
