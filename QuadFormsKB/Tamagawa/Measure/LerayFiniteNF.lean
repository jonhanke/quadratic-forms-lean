import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.LerayThick
import QuadFormsKB.Tamagawa.Measure.LerayCone

/-!
# Thickened Leray measures at a finite place: the densities and the cone factor

$F_v$ = `v.adicCompletion F`, $Q$ a quadratic form over $\mathcal O_v$ in $n$ variables, $\nu$ a Haar measure on $F_v$,
$\mathrm{vol} = \nu^{\otimes n}$, shells $B_k(\rho) = \rho + \mathfrak p_v^k$ (`shell`), and
$\lambda_{\rho,k} = $ `lerayThick ν Q (shell ρ k)` (`LerayThick.lean`).

* `lerayThick_latL_eq_localDensity` (**the Leray volume of the lattice points is the local density**): for
  $\rho \in \mathcal O_v\smallsetminus0$ and all large $k$, $\lambda_{\rho,k}(L_v) = \beta_v(L,\rho)\,\nu(\mathcal O_v)^{n-1}$.
  With $\nu = $ `haarV` this is $\beta_v(L, \rho)$ itself.
* `lerayThick_prim_eq_coneFactor` (**the Leray volume of the primitive null cone**): for all large $j$,
  $\lambda_{0,j}(L_v\smallsetminus\pi L_v) = \nu(\mathcal O_v)^{n-1}\gamma_v(Q)$, $\gamma_v$ = `LerayCone.coneFactor`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero
open scoped ENNReal NNReal Pointwise
open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta
open QuadFormsKB.Tamagawa.Measure.LerayThick QuadFormsKB.Tamagawa.Measure.LerayCone

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayFinite

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-- **The quadratic function** $x \mapsto Q(x)$ on $V_v = F_v^n$. -/
abbrev Qv (Q : QuadForm 𝔬 n) : (Fin n → Fv) → Fv := fun x => Q.evalIn Fv x

/-- **The shell** $B_k(\rho) = \rho + \mathfrak p_v^k = \{y : |y - \rho|_v \le q^{-k}\}$. -/
def shell (ρ : Fv) (k : ℕ) : Set Fv := {y | Valued.v (y - ρ) ≤ exp (-(k : ℤ))}

lemma shell_eq (ρ : Fv) (k : ℕ) :
    shell v ρ k = (fun y : Fv => y + (-ρ)) ⁻¹' (latticeV v (k : ℤ) : Set Fv) := by
  ext y
  simp [shell, mem_latticeV, sub_eq_add_neg]

section Haar

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

lemma measure_latticeV_pos (k : ℤ) : 0 < ν (latticeV v k : Set Fv) :=
  Measure.measure_pos_of_nonempty_interior ν (interior_latticeV_nonempty v k)

lemma measure_latticeV_ne_top (k : ℤ) : ν (latticeV v k : Set Fv) ≠ ⊤ :=
  (isCompact_latticeV v k).measure_lt_top.ne

lemma measure_shell (ρ : Fv) (k : ℕ) : ν (shell v ρ k) = ν (latticeV v (k : ℤ) : Set Fv) := by
  rw [shell_eq]; exact measure_preimage_add_right ν (-ρ) _

lemma real_shell (ρ : (v.adicCompletion F)) (k : ℕ) : ν.real (shell v ρ k) = ν.real (latticeV v (k : ℤ) : Set (v.adicCompletion F)) := by
  rw [Measure.real, measure_shell]; rfl

lemma real_latticeV_pos (k : ℤ) : 0 < ν.real (latticeV v k : Set (v.adicCompletion F)) :=
  ENNReal.toReal_pos (measure_latticeV_pos v ν k).ne' (measure_latticeV_ne_top v ν k)

lemma measure_shell_pos (ρ : Fv) (k : ℕ) : 0 < ν (shell v ρ k) := by
  rw [measure_shell]; exact measure_latticeV_pos v ν k

lemma measure_shell_ne_top (ρ : Fv) (k : ℕ) : ν (shell v ρ k) ≠ ⊤ := by
  rw [measure_shell]; exact measure_latticeV_ne_top v ν k

/-- **The Leray volume of the lattice points** (`volume_ballQ_eq_localDensity`): for $\rho \in \mathcal O_v$, $\rho \ne 0$,
$\nu^{\otimes n}(L_v \cap Q^{-1}(\rho + \mathfrak p^k))/\nu(\mathfrak p^k) = \beta_v(L,\rho)\nu(\mathcal O_v)^{n-1}$ for all large $k$. -/
theorem lerayThick_latL_eq_localDensity (Q : QuadForm 𝔬 n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (ρ : 𝔬) (hρ : ρ ≠ 0) :
    ∀ᶠ k : ℕ in atTop, lerayThick ν (Qv v Q) (shell v (ρ : Fv) k) (latL v n) =
      ENNReal.ofReal (DVR.localDensity Q πv ρ * ν.real (latticeV v 0) ^ (n - 1)) := by
  filter_upwards [volume_ballQ_eq_localDensity v ν Q hQ hn ρ hρ] with k hk
  have hpos : 0 < ν.real (latticeV v (k : ℤ) : Set Fv) :=
    ENNReal.toReal_pos (measure_latticeV_pos v ν k).ne' (measure_latticeV_ne_top v ν k)
  have hcong : latL v n ∩ (Qv v Q) ⁻¹' (shell v (ρ : Fv) k) = congSet v Q (ρ : Fv) k := by
    ext x; simp [congSet, shell, Qv, and_comm]
  have hfin : (volV ν n) (congSet v Q (ρ : Fv) k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (congSet_subset_latL v Q (ρ : Fv) k))
    rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne
  have hvol : (volV ν n) (congSet v Q (ρ : Fv) k) = ENNReal.ofReal
      (DVR.localDensity Q πv ρ * ν.real (latticeV v (k : ℤ) : Set Fv) * ν.real (latticeV v 0) ^ (n - 1)) := by
    rw [← hk, ← ENNReal.ofReal_toReal hfin]; rfl
  have hb : 0 ≤ DVR.localDensity Q πv ρ * ν.real (latticeV v (k : ℤ) : Set Fv) * ν.real (latticeV v 0) ^ (n - 1) := by
    rw [← hk]; exact ENNReal.toReal_nonneg
  rw [lerayThick, Measure.smul_apply, Measure.restrict_apply (measurableSet_latL v), hcong, hvol, measure_shell,
    smul_eq_mul]
  have hc : 0 ≤ DVR.localDensity Q πv ρ * ν.real (latticeV v 0) ^ (n - 1) := by
    have h0 : 0 ≤ ν.real (latticeV v 0) ^ (n - 1) := by positivity
    by_contra hneg
    push Not at hneg
    have : DVR.localDensity Q πv ρ * ν.real (latticeV v (k : ℤ) : Set Fv) * ν.real (latticeV v 0) ^ (n - 1) < 0 := by
      calc _ = (DVR.localDensity Q πv ρ * ν.real (latticeV v 0) ^ (n - 1)) * ν.real (latticeV v (k : ℤ) : Set Fv) := by ring
        _ < 0 := mul_neg_of_neg_of_pos hneg hpos
    linarith
  have hr : ν (latticeV v (k : ℤ) : Set Fv) = ENNReal.ofReal (ν.real (latticeV v (k : ℤ) : Set Fv)) :=
    (ENNReal.ofReal_toReal (measure_latticeV_ne_top v ν k)).symm
  rw [hr, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
  congr 1
  field_simp

/-- $Q(cx) = c^2Q(x)$ for a form over $\mathcal O_v$ evaluated on $F_v^n$. -/
theorem qv_smul (Q : QuadForm 𝔬 n) (c : Fv) (x : Fin n → Fv) : Qv v Q (c • x) = c ^ 2 * Qv v Q x := by
  simp only [Qv]
  rw [QuadForm.evalIn_eq_dotProduct Fv Q, QuadForm.evalIn_eq_dotProduct Fv Q, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The lattice $L_v$ and the sublattice $\mathfrak p_vL_v$**. -/
def pL : Set (Fin n → Fv) := {x | ∀ i, Valued.v (x i) ≤ exp (-1 : ℤ)}

lemma pL_eq : pL v (n := n) = (fun x : Fin n → Fv => ((ϖU v : Fvˣ) : Fv) • x) '' latL v n := by
  ext x
  simp only [pL, latL, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hx
    refine ⟨fun i => x i / HN.ϖ v, fun i => ?_, funext fun i => ?_⟩
    · rw [map_div₀, HN.valued_ϖ]
      exact div_le_one_of_le₀ (hx i) (by simp)
    · simp [ϖU, mul_div_cancel₀ _ (HN.ϖ_ne_zero v)]
  · rintro ⟨y, hy, rfl⟩ i
    simp only [Pi.smul_apply, smul_eq_mul, ϖU, Units.val_mk0, map_mul, HN.valued_ϖ]
    calc exp (-1 : ℤ) * Valued.v (y i) ≤ exp (-1 : ℤ) * 1 := by gcongr; exact hy i
      _ = exp (-1 : ℤ) := mul_one _


/-- **The modulus of a uniformizer is $q^{-1}$** (not proved in `LocalFourierNF`): $\Delta_v = N(v)^{-1}$. -/
theorem modV_eq : (modV v : ℝ) = ((DVR.q 𝔬 : ℕ) : ℝ)⁻¹ := by
  have h1 := haarV_real_latticeV v 1
  have h2 := real_latticeV_eq v (haarV v) 1
  rw [haarV_real_O] at h2
  simp only [Nat.cast_one, zpow_one, pow_one, one_mul] at h1 h2
  rw [← h1]
  exact h2

lemma shell_zero_eq (k : ℕ) : shell v ((0 : 𝔬) : Fv) k = (latticeV v (k : ℤ) : Set Fv) := by
  ext y; simp [shell, mem_latticeV]

end Haar

section Cone

variable (ν : Measure (v.adicCompletion F)) [ν.IsAddHaarMeasure]

/-- **The Leray volume of $L_v$ for the cone shells**: $\lambda_{0,j}(L_v) = \nu(\mathcal O_v)^{n-1}q^ja_j$
($a_j = r_{\mathfrak p^j}(0)/q^{jn}$). -/
theorem lerayThick_latL_cone (Q : QuadForm 𝔬 n) (hn : 1 ≤ n) (j : ℕ) :
    lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : Fv) j) (latL v n) =
      ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * (((DVR.q 𝔬 : ℕ) : ℝ) ^ j * (aSeq v Q j : ℝ))) := by
  have hcong : latL v n ∩ (Qv v Q) ⁻¹' (shell v ((0 : 𝔬) : Fv) j) = congSet v Q ((0 : 𝔬) : Fv) j := by
    ext x; simp [congSet, shell, Qv, and_comm]
  have hfin : (volV ν n) (congSet v Q ((0 : 𝔬) : Fv) j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (congSet_subset_latL v Q ((0 : 𝔬) : Fv) j))
    rw [measure_latL]; exact ENNReal.pow_ne_top (isCompact_latticeV v 0).measure_lt_top.ne
  rw [lerayThick_eq_ofReal ν _ _ (measurableSet_latL v) (measure_shell_pos v ν _ j).ne'
    (measure_shell_ne_top v ν _ j) (by rw [hcong]; exact hfin), hcong, real_congSet_zero, Measure.real,
    real_shell, real_latticeV_eq]
  congr 1
  have hc : 0 < ν.real (latticeV v 0) := real_latticeV_pos v ν 0
  have hq : (0 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast q_pos v
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hc ⊢
  rw [← Measure.real]
  field_simp
  ring

lemma smul_shell (i : ℕ) :
    ((((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) • shell v ((0 : 𝔬) : v.adicCompletion F) i) =
      shell v ((0 : 𝔬) : v.adicCompletion F) (i + 2) := by
  have hϖ : Valued.v (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) = exp (-2 : ℤ) := by
    simp [ϖU, HN.valued_ϖ, pow_two, ← exp_add]
  have hne : (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F) ≠ 0 := Units.ne_zero _
  ext x
  simp only [Set.mem_smul_set, shell, Set.mem_ofPred_eq, smul_eq_mul, ZeroMemClass.coe_zero, sub_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_mul, hϖ]
    calc exp (-2 : ℤ) * Valued.v y ≤ exp (-2 : ℤ) * exp (-(i : ℤ)) := by gcongr
      _ = exp (-((i + 2 : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring
  · intro hx
    refine ⟨x / (((ϖU v ^ 2 : Fvˣ)) : v.adicCompletion F), ?_, mul_div_cancel₀ _ hne⟩
    rw [map_div₀, hϖ, div_le_iff₀ (by simp)]
    calc Valued.v x ≤ exp (-((i + 2 : ℕ) : ℤ)) := hx
      _ = exp (-(i : ℤ)) * exp (-2 : ℤ) := by rw [← exp_add]; congr 1; push_cast; ring

/-- **Scaling of the cone shells by a uniformizer**: $\Delta^2/\Delta^n\cdot\lambda_{0,i+2}(\mathfrak p_vL_v)=\lambda_{0,i}(L_v)$. -/
theorem lerayThick_pL (Q : QuadForm 𝔬 n) (i : ℕ) :
    ((modV v : ℝ≥0∞) ^ 2 / (modV v : ℝ≥0∞) ^ n) *
        lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) (i + 2)) (pL v) =
      lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) i) (latL v n) := by
  have h := map_smul_lerayThick ν (Qv v Q) (ϖU v) (qv_smul v Q _) (shell v ((0 : 𝔬) : v.adicCompletion F) i)
  have hemb : MeasurableEmbedding (fun x : Fin n → v.adicCompletion F => ((ϖU v : Fvˣ) : v.adicCompletion F) • x) := by
    have := (smulEquiv (K := v.adicCompletion F) (m := n) (ϖU v)).measurableEmbedding
    rwa [coe_smulEquiv] at this
  have e1 : lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) i) (latL v n) =
      (Measure.map (fun x : Fin n → v.adicCompletion F => ((ϖU v : Fvˣ) : v.adicCompletion F) • x)
        (lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) i))) (pL v) := by
    rw [hemb.map_apply, pL_eq, Set.preimage_image_eq _ hemb.injective]
  rw [e1, h, Measure.smul_apply, smul_eq_mul, show (distribHaarChar (v.adicCompletion F) (ϖU v) : ℝ≥0) = modV v from rfl,
    ← smul_shell]

lemma measurableSet_pL : MeasurableSet (pL v (n := n)) := by
  have : pL v (n := n) = Set.univ.pi fun _ : Fin n => (latticeV v 1 : Set (v.adicCompletion F)) := by
    ext x; simp [pL, mem_latticeV]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_latticeV v 1

lemma pL_subset : pL v (n := n) ⊆ latL v n := by
  intro x hx i
  exact (hx i).trans (by rw [← exp_zero, exp_le_exp]; omega)

/-- **The Leray volume of the primitive vectors on the null cone** (i.e. of $L_v \smallsetminus \mathfrak p_vL_v$ in the shell
$|Q| \le q^{-j}$): for $j \ge 2$ it is $\nu(\mathcal O_v)^{n-1}q^jc_j$ (the primitive part). -/
theorem lerayThick_prim (Q : QuadForm 𝔬 n) (hn : 2 ≤ n) (i : ℕ) :
    lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) (i + 2)) (latL v n \ pL v) =
      ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * (((DVR.q 𝔬 : ℕ) : ℝ) ^ (i + 2) * (cSeq v Q (i + 2) : ℝ))) := by
  have hq : (0 : ℝ) < ((DVR.q 𝔬 : ℕ) : ℝ) := by exact_mod_cast q_pos v
  have hc : 0 < ν.real (latticeV v 0) := real_latticeV_pos v ν 0
  set q : ℝ := ((DVR.q 𝔬 : ℕ) : ℝ) with hqdef
  have hq0 : q ≠ 0 := hq.ne'
  set c : ℝ := ν.real (latticeV v 0) with hcdef
  have hL2 := lerayThick_latL_cone v ν Q (by omega) (i + 2)
  have hL0 := lerayThick_latL_cone v ν Q (by omega) i
  have hp := lerayThick_pL v ν Q i
  have hmod : (modV v : ℝ≥0∞) = ENNReal.ofReal q⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal]; congr 1; exact modV_eq v
  -- the factor
  have hfac : (modV v : ℝ≥0∞) ^ 2 / (modV v : ℝ≥0∞) ^ n = ENNReal.ofReal (q ^ (n - 2)) := by
    rw [hmod, ← ENNReal.ofReal_pow (inv_nonneg.mpr hq.le), ← ENNReal.ofReal_pow (inv_nonneg.mpr hq.le),
      ← ENNReal.ofReal_div_of_pos (pow_pos (inv_pos.mpr hq) n)]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [inv_pow, inv_pow, pow_add (q) k 2]
    field_simp
  rw [hfac, hL0] at hp
  have haI : 0 ≤ (aSeq v Q i : ℝ) := aSeq_nonneg v Q i
  have hYnn : 0 ≤ c ^ (n - 1) * (q ^ i * (aSeq v Q i : ℝ)) := by positivity
  have hX : lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) (i + 2)) (pL v) =
      ENNReal.ofReal ((q ^ (n - 2))⁻¹ * (c ^ (n - 1) * (q ^ i * (aSeq v Q i : ℝ)))) := by
    have hne : ENNReal.ofReal (q ^ (n - 2)) ≠ 0 := by
      simpa using pow_pos hq (n - 2)
    have := congrArg (fun z => (ENNReal.ofReal (q ^ (n - 2)))⁻¹ * z) hp
    simp only [ENNReal.inv_mul_cancel_left hne ENNReal.ofReal_ne_top] at this
    rw [this, ← ENNReal.ofReal_inv_of_pos (pow_pos hq _), ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_pos hq _).le)]
  have hsub : MeasurableSet (pL v (n := n)) := measurableSet_pL v
  have hfinp : lerayThick ν (Qv v Q) (shell v ((0 : 𝔬) : v.adicCompletion F) (i + 2)) (pL v) ≠ ⊤ := by
    rw [hX]; exact ENNReal.ofReal_ne_top
  rw [measure_sdiff (pL_subset v) hsub.nullMeasurableSet hfinp, hL2, hX,
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1
  have hrec := aSeq_rec v Q (i + 2) (by omega)
  have hrec' : (aSeq v Q (i + 2) : ℝ) = (cSeq v Q (i + 2) : ℝ) + ((q ^ n))⁻¹ * (aSeq v Q i : ℝ) := by
    have := congrArg (fun z : ℚ => (z : ℝ)) hrec
    simp only [Nat.add_sub_cancel] at this
    push_cast at this
    rw [this]
  rw [hrec']
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show k + 2 - 1 = k + 1 by omega]
  field_simp
  ring

/-- **The Leray volume of the primitive null cone is the cone factor**: for a global
nondegenerate form $Q$ in $n \ge 2$ variables and all large $j$,
$$\lambda_{0,j}(L_v \smallsetminus \mathfrak p_vL_v) = \nu(\mathcal O_v)^{n-1}\,\gamma_v(Q).$$ -/
theorem lerayThick_prim_eq_coneFactor (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 2 ≤ n) :
    ∀ᶠ j : ℕ in atTop, lerayThick ν (Qv v (NF.Qp v Q)) (shell v ((0 : 𝔬) : v.adicCompletion F) j)
        (latL v n \ pL v) = ENNReal.ofReal (ν.real (latticeV v 0) ^ (n - 1) * coneFactor Q v) := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (eventually_coneSeq_eq Q hQ (by omega) v)
  refine Filter.eventually_atTop.mpr ⟨J + 2, fun j hj => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  rw [lerayThick_prim v ν (NF.Qp v Q) hn i, mul_comm (((DVR.q 𝔬 : ℕ) : ℝ) ^ (i + 2)), hJ (i + 2) (by omega)]

end Cone

end QuadFormsKB.Tamagawa.Measure.LerayFinite
