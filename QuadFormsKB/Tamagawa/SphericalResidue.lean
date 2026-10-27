/-
# The residue of Weil's spherical sum at $s = 0$ (Weil's (4)–(8))

**Layer:** global assembly. Inputs: the local layer (`SphericalLocal.lean`: Weil's bound for $e(\mathfrak p)$, the parity factors and
their twisted closed forms), the square-class arithmetic (`SquareClassDuality.lean`, `SquareClassParam.lean`: $\Lambda_S$, the finite
Poisson formula, the parametrization of $F^\times/F^{\times2}$, the characters $\chi_\lambda$), the no-pole theorem for quadratic twists
(`QuadraticTwist.lean`) and the residue of the plain zeta integral (`ZetaResidue.lean`).

**Weil's argument** (1982, §4.5, pp. 105–108), as formalized here. Fix $S$ (finite places) containing the bad places of $Q$, the
dyadic places, a set $S_0$ generating the class group, and the places of the kernel condition. For $\mathfrak p \notin S$ let
$P_0(\mathfrak p), P_1(\mathfrak p)$ be the even/odd parity parts of Weil's local zeta function ($P_0 + P_1 = Z_\mathfrak p$) and
$r_\mathfrak p = P_1/P_0$. Then:
1. (**(7)**, p. 107) $Z_\mathfrak p(s,\rho) = e_\mathfrak p(\rho)\,P_{\operatorname{ord}_\mathfrak p\rho \bmod 2}(\mathfrak p)$ with $|e_\mathfrak p - 1| \le 2N\mathfrak p^{-2}$
   ($n \ge 5$), so $Z(s,\rho) = E_S(\rho)\cdot|d_F|^{-n/2}\alpha_S(\rho)\,B_S\prod_{\mathfrak p\in T(\rho)}r_\mathfrak p$, $E_S(\rho) \in [\mu(S), \mu'(S)]$.
2. (**(4)–(6)**, p. 106) summing over $F^\times/F^{\times2} \cong \{T\}\times\Lambda_S$ with the finite Poisson formula gives
   $|\Lambda_S|^{-1}\sum_{\lambda\in\Lambda_S}\hat\alpha_S(\lambda)\prod_{\mathfrak p\notin S}(1 + \chi_\lambda(\mathfrak p)r_\mathfrak p)$, whose $\lambda = 1$ term is the
   `globalZeta` and whose other terms are $o(1/s)$ (`QTwist.tendsto_mul_LFunction_zero`).
3. (**(8)**, p. 108) letting $S \to \infty$, $\mu(S), \mu'(S) \to 1$.
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SphericalLocal
import QuadFormsKB.Tamagawa.SphericalSum
import QuadFormsKB.Tamagawa.QuadraticTwist

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SphericalZeta

open QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.GlobalZeta QuadFormsKB.Siegel QuadFormsKB.SqDual
open QuadFormsKB.NFEuler

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $q_v$ as a real number. -/
local notation "qv" v => ((DVR.q (HeightOneSpectrum.adicCompletionIntegers F v) : ℕ) : ℝ)

/-! ### The parity factors at the finite places -/

/-- $X_v = q_v^{-s}$. -/
def Xv (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ := (qv v) ^ (-s)

/-- **The even-parity factor** $P_0(v) = (1-q_v^{-1})^{-1}\int_{\operatorname{ord}Q(x)\ \mathrm{even}}|Q|^s\,dx$ (Weil's $\int_{F(x)\in H_\mathfrak p\rho}$ for
$\rho$ a unit, p. 107). -/
def Pe (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  parSeries v (NF.Qp v Q) 0 (Xv v s) / (1 - (qv v)⁻¹)

/-- **The odd-parity factor** $P_1(v)$ (Weil's $\int_{F(x)\in H_\mathfrak p\rho}$ for $\rho$ of odd order). -/
def Po (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  parSeries v (NF.Qp v Q) 1 (Xv v s) / (1 - (qv v)⁻¹)

lemma Xv_pos (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : 0 < Xv v s :=
  Real.rpow_pos_of_pos (by have := one_lt_qv v; linarith) _

lemma Xv_le_one (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 ≤ s) : Xv v s ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_lt_qv v).le (by linarith)

lemma abs_Xv_le_one (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 ≤ s) : |Xv v s| ≤ 1 := by
  rw [abs_of_pos (Xv_pos v s)]; exact Xv_le_one v hs

lemma one_sub_inv_qv_pos' (v : HeightOneSpectrum (𝓞 F)) : 0 < 1 - (qv v)⁻¹ := one_sub_inv_qv_pos v

/-- $P_0 + P_1 = Z_\mathfrak p$ (Weil's local zeta function, `zetaWeil`). -/
lemma Pe_add_Po (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 ≤ s) : Pe Q v s + Po Q v s = zetaWeil Q v s := by
  rw [Pe, Po, ← add_div, parSeries_add v _ (NF.nondegenerate_Qp v hQ) hn (abs_Xv_le_one v hs), zetaWeil, zetaStd,
    Xv, genSeries_eq_zetaInt v _ (NF.nondegenerate_Qp v hQ) hn hs]

lemma Pe_nonneg (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : 0 ≤ Pe Q v s :=
  div_nonneg (parSeries_nonneg v _ 0 (Xv_pos v s).le) (one_sub_inv_qv_pos' v).le

lemma Po_nonneg (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : 0 ≤ Po Q v s :=
  div_nonneg (parSeries_nonneg v _ 1 (Xv_pos v s).le) (one_sub_inv_qv_pos' v).le

section Good

variable {Q : QuadForm (𝓞 F) n} {v : HeightOneSpectrum (𝓞 F)}

lemma inv_one_sub_inv_qv_le (h2 : ¬ NF.π v ∣ 2) : (1 - (qv v)⁻¹)⁻¹ ≤ 3 / 2 := by
  have hq3 : (3 : ℝ) ≤ qv v := by
    haveI : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
    exact_mod_cast DVR.three_le_q (NF.irreducible_π v) h2
  have h0 : (0 : ℝ) < qv v := by linarith
  rw [inv_le_comm₀ (one_sub_inv_qv_pos' v) (by norm_num)]
  have : (qv v)⁻¹ ≤ 1 / 3 := by rw [inv_le_comm₀ h0 (by norm_num)]; linarith
  linarith

/-- $P_0 \ge 1/3$ at a good place. -/
lemma Pe_ge (hv : IsGoodPlace Q v) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 1 / 3 ≤ Pe Q v s := by
  obtain ⟨h2, hdet⟩ := not_dvd_of_isGoodPlace hv
  have h := parSeries_zero_ge_third v (NF.Qp v Q) hn h2 hdet (Xv_pos v s).le (Xv_le_one v hs)
  rw [Pe, le_div_iff₀ (one_sub_inv_qv_pos' v)]
  have : 0 < (qv v)⁻¹ := inv_pos.mpr (by have := one_lt_qv v; linarith)
  nlinarith

/-- $|P_0 - 1| \le 10q^{-2}$ at a good place ($n \ge 4$). -/
lemma abs_Pe_sub_one_le (hv : IsGoodPlace Q v) (hn : 4 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    |Pe Q v s - 1| ≤ 10 * ((qv v) ^ 2)⁻¹ := by
  obtain ⟨h2, hdet⟩ := not_dvd_of_isGoodPlace hv
  exact abs_parSeries_zero_sub_one_le v (NF.Qp v Q) hn h2 hdet (Xv_pos v s).le (Xv_le_one v hs)

/-- $P_1 \le 3q^{-1}X$ at a good place. -/
lemma Po_le (hv : IsGoodPlace Q v) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    Po Q v s ≤ 3 * (qv v)⁻¹ * Xv v s := by
  obtain ⟨h2, hdet⟩ := not_dvd_of_isGoodPlace hv
  have h := parSeries_one_le_good v (NF.Qp v Q) hn h2 hdet (Xv_pos v s).le (Xv_le_one v hs)
  have hi := inv_one_sub_inv_qv_le (v := v) h2
  rw [Po, div_eq_mul_inv]
  have h0 : 0 ≤ parSeries v (NF.Qp v Q) 1 (Xv v s) := parSeries_nonneg v _ 1 (Xv_pos v s).le
  have hx : 0 ≤ (qv v)⁻¹ * Xv v s := mul_nonneg (inv_pos.mpr (by have := one_lt_qv v; linarith)).le (Xv_pos v s).le
  calc parSeries v (NF.Qp v Q) 1 (Xv v s) * (1 - (qv v)⁻¹)⁻¹ ≤ (2 * (qv v)⁻¹ * Xv v s) * (3 / 2) :=
        mul_le_mul h hi (inv_pos.mpr (one_sub_inv_qv_pos' v)).le (by nlinarith)
    _ = 3 * (qv v)⁻¹ * Xv v s := by ring

/-- **The twisted factor**: $P_0 + cP_1 = R(cX)/(1 - cq^{-1}X)$ for $c = \pm1$ ($R$ = `genRatio`). -/
lemma Pe_add_mul_Po (hQ : Q.Nondegenerate) (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) {c : ℝ} (hc : c = 1 ∨ c = -1) :
    Pe Q v s + c * Po Q v s = genRatio v (NF.Qp v Q) (c * Xv v s) / (1 - c * (qv v)⁻¹ * Xv v s) := by
  have hcX : |c * Xv v s| ≤ 1 := by
    rcases hc with rfl | rfl <;> simp [abs_Xv_le_one v hs]
  have h := parSeries_add_mul v (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) hn (abs_Xv_le_one v hs) hc
  have h1 : 1 - (qv v)⁻¹ ≠ 0 := (one_sub_inv_qv_pos' v).ne'
  have h2 : 1 - c * (qv v)⁻¹ * Xv v s ≠ 0 := by
    have hq : (qv v)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_qv v)
    have := abs_le_one_aux (inv_pos.mpr (by have := one_lt_qv v; linarith)).le hq hcX
    intro h0
    have : (qv v)⁻¹ * (c * Xv v s) = 1 := by linarith
    have h3 := (abs_lt.mp ‹|(qv v)⁻¹ * (c * Xv v s)| < 1›).2
    linarith
  rw [Pe, Po, mul_div_assoc', ← add_div, h, genRatio,
    show (qv v)⁻¹ * (c * Xv v s) = c * (qv v)⁻¹ * Xv v s by ring, div_right_comm,
    mul_div_cancel_right₀ _ h2]

end Good

/-! ### Weil's $e(\mathfrak p)$ for a global $\rho$ -/

/-- The parity factor matching $\rho$: $P_1$ if $\operatorname{ord}_v\rho$ is odd, $P_0$ otherwise. -/
def Ppar (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : Fˣ) (s : ℝ) : ℝ :=
  if Odd (ordL v ρ) then Po Q v s else Pe Q v s

lemma Ppar_nonneg (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (ρ : Fˣ) (s : ℝ) : 0 ≤ Ppar Q v ρ s := by
  unfold Ppar; split_ifs <;> [exact Po_nonneg Q v s; exact Pe_nonneg Q v s]

/-- **Weil's (7) at a good place** ($n \ge 5$, $\rho \in F^\times$, $s \ge 0$): $|Z_\mathfrak p(s,\rho) - P_{\operatorname{ord}\rho}| \le
2N\mathfrak p^{-2}P_{\operatorname{ord}\rho}$, i.e. $1 - 2q^{-2} \le e(\mathfrak p) \le 1 + 2q^{-2}$ (Weil 1982, p. 107: $1 - q^{-m'} < \theta(\mathfrak p) <
1 + q^{-m'}$). From `abs_two_sphInt_sub_le` after writing $\rho = \pi^{j_0}w\lambda^2$ in $F_v$. -/
@[kb "weil1982" "§4.5, (7) and the bound for θ(p), p. 107"]
theorem abs_sphLocal_sub_Ppar_le {Q : QuadForm (𝓞 F) n} (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsGoodPlace Q v) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s) :
    |sphLocal Q v (algebraMap F (v.adicCompletion F) (ρ : F)) s - Ppar Q v ρ s| ≤
      2 * ((qv v) ^ 2)⁻¹ * Ppar Q v ρ s := by
  obtain ⟨h2, hdet⟩ := not_dvd_of_isGoodPlace hv
  have hρ0 : algebraMap F (v.adicCompletion F) (ρ : F) ≠ 0 := (map_ne_zero _).mpr ρ.ne_zero
  obtain ⟨m, a, ha, hma⟩ := exists_zpow_mul_unit v hρ0
  have hπ0 : (NF.π v : v.adicCompletion F) ≠ 0 := by
    intro h; have := NF.valued_π v; rw [h, map_zero] at this; exact WithZero.zero_ne_coe this
  -- the order: m = - ordL v ρ
  have hm : m = -ordL v ρ := by
    have h1 := congrArg Valued.v hma
    rw [HN.valued_algebraMap, valuation_eq_exp_ordL, map_mul, valued_π_zpow, valued_eq_one_of_isUnit v ha,
      mul_one, exp_inj] at h1
    omega
  set j₀ : ℕ := (m % 2).toNat
  have hj₀ : j₀ < 2 := by have := Int.emod_nonneg m two_ne_zero; have := Int.emod_lt_of_pos m two_pos; omega
  set k : ℤ := m / 2
  have hmk : m = 2 * k + j₀ := by have := Int.emod_nonneg m two_ne_zero; omega
  -- ρ = π^{j₀} a (π^k)² in F_v
  have hdecomp : algebraMap F (v.adicCompletion F) (ρ : F) =
      ((NF.π v ^ j₀ * a : v.adicCompletionIntegers F) : v.adicCompletion F) * ((NF.π v : v.adicCompletion F) ^ k) ^ 2 := by
    have e1 : (NF.π v : v.adicCompletion F) ^ (2 * k) = ((NF.π v : v.adicCompletion F) ^ k) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]; norm_num
    rw [hma, hmk, zpow_add₀ hπ0, zpow_natCast, e1]
    push_cast
    ring
  have hloc : sphLocal Q v (algebraMap F (v.adicCompletion F) (ρ : F)) s =
      2 * sphInt Q v ((NF.π v ^ j₀ * a : v.adicCompletionIntegers F) : v.adicCompletion F) s / (1 - (qv v)⁻¹) := by
    rw [sphLocal, hdecomp, sphInt_mul_sq Q v _ (zpow_ne_zero _ hπ0)]
  have hbound := abs_two_sphInt_sub_le v (NF.Qp v Q) (NF.nondegenerate_Qp v hQ) (by omega) h2 hdet j₀ hj₀ ha hs
  have hpar : Ppar Q v ρ s = parSeries v (NF.Qp v Q) j₀ (Xv v s) / (1 - (qv v)⁻¹) := by
    unfold Ppar
    have hodd : Odd (ordL v ρ) ↔ j₀ = 1 := by
      constructor
      · rintro ⟨t, ht⟩; omega
      · intro h; exact ⟨-(k + 1), by omega⟩
    by_cases h : Odd (ordL v ρ)
    · rw [if_pos h, (hodd.mp h), Po]
    · have : j₀ = 0 := by have := hodd.not.mp h; omega
      rw [if_neg h, this, Pe]
  have hθ : 2 * ((qv v) ^ ((n - 1) / 2))⁻¹ ≤ 2 * ((qv v) ^ 2)⁻¹ := by
    have h1 : (1 : ℝ) ≤ qv v := (one_lt_qv v).le
    have := inv_anti₀ (by positivity : (0 : ℝ) < (qv v) ^ 2) (pow_le_pow_right₀ h1 (by omega : 2 ≤ (n - 1) / 2))
    linarith
  rw [hloc, hpar, sphInt]
  have hpos := one_sub_inv_qv_pos' v
  have hP : 0 ≤ parSeries v (NF.Qp v Q) j₀ (Xv v s) := parSeries_nonneg v _ j₀ (Xv_pos v s).le
  rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |2 * ∫ x in latL v n ∩ (NF.Qp v Q).evalIn (v.adicCompletion F) ⁻¹'
          sqClass ((NF.π v ^ j₀ * a : v.adicCompletionIntegers F) : v.adicCompletion F),
          ‖(NF.Qp v Q).evalIn (v.adicCompletion F) x‖ ^ s ∂(Measure.pi fun _ : Fin n => haarV v) -
        parSeries v (NF.Qp v Q) j₀ (Xv v s)|
      ≤ 2 * ((qv v) ^ ((n - 1) / 2))⁻¹ * parSeries v (NF.Qp v Q) j₀ (Xv v s) := hbound
    _ ≤ 2 * ((qv v) ^ 2)⁻¹ * parSeries v (NF.Qp v Q) j₀ (Xv v s) := mul_le_mul_of_nonneg_right hθ hP
    _ = _ := by rw [mul_div_assoc', div_mul_cancel₀ _ hpos.ne']

/-! ### Square-class partitions of the local integrals -/

section Partition

variable {K : Type*} [Field K]

/-- $[t] = [a]$ in $K^\times/K^{\times2}$ iff $t = a y^2$ for some $y \ne 0$. -/
lemma mk_eq_mk_iff (a b : Kˣ) :
    (QuotientGroup.mk a : SqCl K) = QuotientGroup.mk b ↔ ∃ y : K, y ≠ 0 ∧ (b : K) = a * y ^ 2 := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(y : K), Units.ne_zero _, ?_⟩
    have := congrArg Units.val hy
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val] at this
    rw [this]; field_simp
  · rintro ⟨y, hy, hb⟩
    refine ⟨Units.mk0 y hy, Units.ext ?_⟩
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0, hb]
    field_simp

lemma mem_sqClass_iff_mk (a : Kˣ) (t : K) :
    t ∈ sqClass (a : K) ↔ ∃ ht : t ≠ 0, (QuotientGroup.mk (Units.mk0 t ht) : SqCl K) = QuotientGroup.mk a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have ht : (a : K) * y ^ 2 ≠ 0 := mul_ne_zero (Units.ne_zero _) (pow_ne_zero 2 hy)
    refine ⟨ht, ?_⟩
    rw [eq_comm, mk_eq_mk_iff]
    exact ⟨y, hy, rfl⟩
  · rintro ⟨ht, h⟩
    rw [eq_comm, mk_eq_mk_iff] at h
    obtain ⟨y, hy, h⟩ := h
    exact ⟨y, hy, h⟩

lemma mem_sqClass_out_iff (c : SqCl K) (t : K) :
    t ∈ sqClass ((Quotient.out c : Kˣ) : K) ↔ ∃ ht : t ≠ 0, (QuotientGroup.mk (Units.mk0 t ht) : SqCl K) = c := by
  rw [mem_sqClass_iff_mk]
  have : (QuotientGroup.mk (Quotient.out c) : SqCl K) = c := Quotient.out_eq c
  rw [this]

lemma sqClass_out_mk (a : Kˣ) :
    sqClass ((Quotient.out (QuotientGroup.mk a : SqCl K) : Kˣ) : K) = sqClass (a : K) := by
  ext t
  rw [mem_sqClass_out_iff, mem_sqClass_iff_mk]

/-- **The square classes partition $\{q \ne 0\}$**: for $q : X \to K$ and $g$ integrable on $\{q \ne 0\}$,
$\sum_{c\in K^\times/K^{\times2}}\int_{q(x)\in c}g = \int_{q \ne 0}g$. -/
theorem sum_setIntegral_sqClass {X : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype (SqCl K)]
    (q : X → K) (g : X → ℝ) (hmeas : ∀ c : SqCl K, MeasurableSet (q ⁻¹' sqClass ((Quotient.out c : Kˣ) : K)))
    (hint : IntegrableOn g {x | q x ≠ 0} μ) :
    ∑ c : SqCl K, ∫ x in q ⁻¹' sqClass ((Quotient.out c : Kˣ) : K), g x ∂μ = ∫ x in {x | q x ≠ 0}, g x ∂μ := by
  have hU : (⋃ c : SqCl K, q ⁻¹' sqClass ((Quotient.out c : Kˣ) : K)) = {x | q x ≠ 0} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, mem_sqClass_out_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨c, ht, -⟩; exact ht
    · intro ht; exact ⟨_, ht, rfl⟩
  have hsub : ∀ c : SqCl K, q ⁻¹' sqClass ((Quotient.out c : Kˣ) : K) ⊆ {x | q x ≠ 0} := fun c =>
    hU ▸ Set.subset_iUnion (fun c => q ⁻¹' sqClass ((Quotient.out c : Kˣ) : K)) c
  rw [← hU, integral_iUnion_fintype hmeas]
  · intro c c' hcc'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_preimage, mem_sqClass_out_iff] at hx hx'
    obtain ⟨_, h1⟩ := hx; obtain ⟨_, h2⟩ := hx'
    exact hcc' (h1.symm.trans h2)
  · intro c; exact hint.mono_set (hsub c)

end Partition

/-! ### The local functions on $G_S$ -/

section LocalFns

/-- The local spherical factor at a finite place as a function of the square class: $c \mapsto Z_\mathfrak p(s, c)$. -/
def Afin (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (c : SqCl (v.adicCompletion F)) : ℝ :=
  sphLocal Q v ((Quotient.out c : (v.adicCompletion F)ˣ) : v.adicCompletion F) s

open Classical in
/-- The local spherical factor at an infinite place as a function of the square class of $F_w$ (via $F_w \cong \mathbb R$ at a real
place; $1$ at a complex place, where there is only one class). -/
def Ainf (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (w : InfinitePlace F) (s : ℝ)
    (c : SqCl w.Completion) : ℝ :=
  if hw : w.IsReal then
    2 * ∫ x in (fun x => (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (realVal Q ⟨w, hw⟩ x)) ⁻¹'
        sqClass ((Quotient.out c : w.Completionˣ) : w.Completion),
      |realVal Q ⟨w, hw⟩ x| ^ s * Φ ⟨w, hw⟩ x
  else 1

lemma Afin_mk (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) (ρ : Fˣ) :
    Afin Q v s (QuotientGroup.mk (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ρ)) =
      sphLocal Q v (algebraMap F (v.adicCompletion F) (ρ : F)) s := by
  rw [Afin, sphLocal, sphLocal, sphInt, sphInt, sqClass_out_mk]
  rfl

lemma preimage_symm_sqClass {K : Type*} [Field K] (e : K ≃+* ℝ) (a : K) (g : (Fin n → ℝ) → ℝ) :
    (fun x => e.symm (g x)) ⁻¹' sqClass a = g ⁻¹' sqClass (e a) := by
  ext x
  simp only [Set.mem_preimage, mem_sqClass]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨e y, (map_ne_zero e).mpr hy, ?_⟩
    rw [← map_pow, ← map_mul, ← h, RingEquiv.apply_symm_apply]
  · rintro ⟨y, hy, h⟩
    refine ⟨e.symm y, (map_ne_zero e.symm).mpr hy, ?_⟩
    rw [h, map_mul, map_pow, RingEquiv.symm_apply_apply]

lemma Ainf_mk (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (w : RealPlace F) (s : ℝ) (ρ : Fˣ) :
    Ainf Q Φ w.1 s (QuotientGroup.mk (Units.map (algebraMap F w.1.Completion).toMonoidHom ρ)) =
      sphArchAt Q w (Φ w) (realEmb w ρ) s := by
  rw [Ainf, dif_pos w.2, sphArchAt, sqClass_out_mk, preimage_symm_sqClass]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [HN.real_algebraMap]
  rfl

/-- **The finite-place sum over square classes**: $\sum_{c\in F_v^\times/F_v^{\times2}}Z_\mathfrak p(s, c) = 2Z_\mathfrak p(s)$ (every finite place,
dyadic included; $T(\rho)$ covers $\{Q \in \rho F_v^{\times2}\}$ twice). -/
theorem sum_Afin (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 ≤ s) [Fintype (SqCl (v.adicCompletion F))] :
    ∑ c : SqCl (v.adicCompletion F), Afin Q v s c = 2 * zetaWeil Q v s := by
  set μ := Measure.pi fun _ : Fin n => haarV v
  set q := (NF.Qp v Q).evalIn (v.adicCompletion F)
  have hcont : Continuous q := by
    unfold q QuadForm.evalIn
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
      split_ifs <;> fun_prop
  have hmeas : ∀ c : SqCl (v.adicCompletion F),
      MeasurableSet (q ⁻¹' sqClass ((Quotient.out c : (v.adicCompletion F)ˣ) : v.adicCompletion F)) :=
    fun c => ((isOpen_sqClass v (Units.ne_zero _)).preimage hcont).measurableSet
  have hLfin : μ (latL v n) ≠ ⊤ := measure_latL_haar_ne_top v
  have hint : IntegrableOn (fun x => ‖q x‖ ^ s) {x | q x ≠ 0} (μ.restrict (latL v n)) := by
    rw [IntegrableOn, Measure.restrict_restrict' (measurableSet_latL v)]
    refine (Measure.integrableOn_of_bounded (M := 1) hLfin
      ((continuous_norm.comp hcont).measurable.pow_const s).aestronglyMeasurable ?_).mono_set
      Set.inter_subset_right
    refine (ae_restrict_iff' (measurableSet_latL v)).mpr (Eventually.of_forall fun x hx => ?_)
    show ‖‖q x‖ ^ s‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one (norm_nonneg _) (norm_le_one_of_valued v (valued_evalIn_le_one v _ hx)) hs
  have h := sum_setIntegral_sqClass (μ.restrict (latL v n)) q (fun x => ‖q x‖ ^ s) hmeas hint
  have hterm : ∀ c, Afin Q v s c = 2 / (1 - (qv v)⁻¹) *
      ∫ x in q ⁻¹' sqClass ((Quotient.out c : (v.adicCompletion F)ˣ) : v.adicCompletion F),
        ‖q x‖ ^ s ∂(μ.restrict (latL v n)) := by
    intro c
    rw [Afin, sphLocal, sphInt, Measure.restrict_restrict (hmeas c), Set.inter_comm]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, h, Measure.restrict_restrict (by
    exact (isClosed_eq hcont continuous_const).isOpen_compl.measurableSet)]
  have hnull : μ (nullCone v (NF.Qp v Q)) = 0 := measure_nullCone v (haarV v) _ (NF.nondegenerate_Qp v hQ) hn
  have hae : ({x | q x ≠ 0} ∩ latL v n : Set _) =ᵐ[μ] latL v n := by
    have : ({x | q x ≠ 0} ∩ latL v n : Set _) = latL v n \ nullCone v (NF.Qp v Q) := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, nullCone, q]; tauto
    rw [this]; exact sdiff_null_ae_eq_self hnull
  rw [setIntegral_congr_set hae, zetaWeil, zetaStd, zetaInt]
  ring

/-- A real square class $r\mathbb R^{\times2}$ ($r \ne 0$) is the open half-line $\{t : tr > 0\}$. -/
lemma isOpen_sqClass_real {r : ℝ} (hr : r ≠ 0) : IsOpen (sqClass r) := by
  have : sqClass r = {t : ℝ | 0 < t * r} := by
    ext t
    simp only [mem_sqClass, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : 0 < y ^ 2 := by positivity
      have h2 : 0 < r * r := mul_self_pos.mpr hr
      nlinarith
    · intro ht
      have hq : 0 < t / r := by
        rw [div_eq_mul_inv, show t * r⁻¹ = (t * r) * (r⁻¹ * r⁻¹) by field_simp]
        exact mul_pos ht (mul_self_pos.mpr (inv_ne_zero hr))
      refine ⟨Real.sqrt (t / r), (Real.sqrt_pos.mpr hq).ne', ?_⟩
      rw [Real.sq_sqrt hq.le]; field_simp
  rw [this]; exact isOpen_lt continuous_const (continuous_id.mul continuous_const)

/-- **The real-place sum over square classes**: $\sum_{c}Z_w(s, c) = 2Z_w(s)$ ($\{Q_w = 0\}$ null; $|Q_w|^s\varphi$ integrable). -/
theorem sum_Ainf (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (w : RealPlace F) {s : ℝ}
    (hint : Integrable fun x => |realVal Q w x| ^ s * Φ w x) (hnull : ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0)
    [Fintype (SqCl w.1.Completion)] :
    ∑ c : SqCl w.1.Completion, Ainf Q Φ w.1 s c = 2 * archZetaAt Q w (Φ w) s := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal w.2
  set q : (Fin n → ℝ) → w.1.Completion := fun x => e.symm (realVal Q w x)
  have hmeas : ∀ c : SqCl w.1.Completion,
      MeasurableSet (q ⁻¹' sqClass ((Quotient.out c : w.1.Completionˣ) : w.1.Completion)) := by
    intro c
    rw [preimage_symm_sqClass]
    have hne : e ((Quotient.out c : w.1.Completionˣ) : w.1.Completion) ≠ 0 :=
      (map_ne_zero e).mpr (Units.ne_zero _)
    have hopen := isOpen_sqClass_real hne
    exact (hopen.preimage (continuous_realVal Q w)).measurableSet
  have h := sum_setIntegral_sqClass (volume : Measure (Fin n → ℝ)) q (fun x => |realVal Q w x| ^ s * Φ w x) hmeas
    hint.integrableOn
  have hterm : ∀ c, Ainf Q Φ w.1 s c = 2 * ∫ x in q ⁻¹' sqClass ((Quotient.out c : w.1.Completionˣ) :
      w.1.Completion), |realVal Q w x| ^ s * Φ w x := by
    intro c; rw [Ainf, dif_pos w.2]
  simp_rw [hterm]
  rw [← Finset.mul_sum, h]
  congr 1
  have hae : {x | q x ≠ 0} =ᵐ[(volume : Measure (Fin n → ℝ))] (Set.univ : Set (Fin n → ℝ)) := by
    filter_upwards [hnull] with x hx
    simp only [Set.mem_ofPred_eq, Set.mem_univ, eq_iff_iff, iff_true]
    exact (map_ne_zero e.symm).mpr hx
  rw [setIntegral_congr_set hae, Measure.restrict_univ, archZetaAt]

end LocalFns

lemma univ_eq_of_fintype {α : Type*} (i j : Fintype α) : @Finset.univ α i = @Finset.univ α j := by
  rw [Subsingleton.elim i j]

/-! ### The function $\alpha_S$ on $G_S$ and its total sum -/

section Alpha

open Classical

/-- **$\alpha_S$** on $G_S = \prod_{v\in S\cup\infty}F_v^\times/F_v^{\times2}$: the product of the local spherical factors at the places
of $S \cup \infty$. For $\rho \in F^\times$, $\alpha_S([\rho]) = \prod_{v\in S}Z_v(s,\rho)\prod_wZ_w(s,\rho)$ (`alphaS_locMap`). -/
def alphaS (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (s : ℝ) (h : GS F S) : ℝ :=
  (∏ v : S, Afin Q v.1 s (h.1 v)) * ∏ w : InfinitePlace F, Ainf Q Φ w s (h.2 w)

/-- The real places are all the infinite places of a totally real field. -/
def realPlaceEquiv (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : RealPlace F ≃ InfinitePlace F :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyReal.isReal w

/-- A product over the infinite places of a function that is $1$ at the complex places is the product over the real places. -/
lemma prod_infinite_eq_prod_real (f : InfinitePlace F → ℝ) (hf : ∀ w : InfinitePlace F, ¬ w.IsReal → f w = 1) :
    ∏ w : InfinitePlace F, f w = ∏ w : RealPlace F, f w.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal) f,
    Fintype.prod_eq_one (fun w : {w : InfinitePlace F // ¬ w.IsReal} => f w.1) (fun w => hf w.1 w.2), mul_one]

/-- At a complex place there is one square class ($\mathbb C^\times = \mathbb C^{\times2}$). -/
lemma card_sqCl_complex {w : InfinitePlace F} (hw : ¬ w.IsReal) [Fintype (SqCl w.Completion)] :
    Fintype.card (SqCl w.Completion) = 1 := by
  have h := HN.index_sq_infinite w
  rw [if_neg hw, Subgroup.index] at h
  rw [← Nat.card_eq_fintype_card]; exact h

lemma alphaS_locMap (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) (ρ : Fˣ) :
    alphaS Q Φ S s (locMap S ρ) = (∏ v : S, sphLocal Q v.1 (algebraMap F (v.1.adicCompletion F) (ρ : F)) s) *
      ∏ w : RealPlace F, sphArchAt Q w (Φ w) (realEmb w ρ) s := by
  rw [alphaS, prod_infinite_eq_prod_real _ fun w hw => by simp only [Ainf, dif_neg hw]]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => Afin_mk Q v.1 s ρ
  · exact Finset.prod_congr rfl fun w _ => Ainf_mk Q Φ w s ρ

/-- **$\hat\alpha_S(1) = \sum_{h\in G_S}\alpha_S(h) = \prod_{v\in S}2Z_v(s)\prod_w2Z_w(s)$** (the class sums `sum_Afin`, `sum_Ainf`). -/
theorem sum_alphaS (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 1 ≤ n)
    (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 0 ≤ s)
    (hint : ∀ w, Integrable fun x => |realVal Q w x| ^ s * Φ w x)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    ∑ h : GS F S, alphaS Q Φ S s h =
      (∏ v : S, 2 * zetaWeil Q v.1 s) * ∏ w : RealPlace F, 2 * archZetaAt Q w (Φ w) s := by
  classical
  letI : ∀ v : S, Fintype (SqCl (v.1.adicCompletion F)) := fun v => Fintype.ofFinite _
  letI : ∀ w : InfinitePlace F, Fintype (SqCl w.Completion) := fun w => Fintype.ofFinite _
  have e1 : ∑ h : GS F S, alphaS Q Φ S s h = ∑ h₁ : ((v : S) → SqCl (v.1.adicCompletion F)),
      ∑ h₂ : ((w : InfinitePlace F) → SqCl w.Completion), alphaS Q Φ S s (h₁, h₂) := by
    rw [← Fintype.sum_prod_type']
    congr 1
    exact univ_eq_of_fintype _ _
  rw [e1]
  simp only [alphaS]
  rw [← Finset.sum_mul_sum, ← Fintype.prod_sum (fun (v : S) (c : SqCl (v.1.adicCompletion F)) => Afin Q v.1 s c),
    ← Fintype.prod_sum (fun (w : InfinitePlace F) (c : SqCl w.Completion) => Ainf Q Φ w s c)]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => sum_Afin Q hQ hn v.1 hs
  · rw [prod_infinite_eq_prod_real _ fun w hw => by
      simp only [Ainf, dif_neg hw, Finset.sum_const, Finset.card_univ, card_sqCl_complex hw, one_smul]]
    exact Finset.prod_congr rfl fun w _ => sum_Ainf Q Φ w (hint w) (hnull w)

end Alpha

/-! ### Step A: the factorization of $Z(s,\rho)$ outside $S$ -/

section StepA

open Classical

/-- $\theta_v = 2N\mathfrak p_v^{-2}$, the width of Weil's bound for $e(\mathfrak p)$. -/
def thetaV (v : HeightOneSpectrum (𝓞 F)) : ℝ := 2 * ((qv v) ^ 2)⁻¹

lemma thetaV_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ thetaV v := by
  have := one_lt_qv v; unfold thetaV; positivity

lemma thetaV_le_one (v : HeightOneSpectrum (𝓞 F)) : thetaV v ≤ 1 := by
  have h2 : (2 : ℝ) ≤ qv v := by exact_mod_cast (q_ge_two v)
  unfold thetaV
  rw [mul_comm, ← div_eq_inv_mul, div_le_one (by positivity)]
  nlinarith

lemma inv_qv_sq_eq (v : HeightOneSpectrum (𝓞 F)) : ((qv v) ^ 2)⁻¹ = (normP v : ℝ) ^ (-(2 : ℝ)) := by
  rw [qv_eq, Real.rpow_neg (by positivity), Real.rpow_two]

lemma summable_inv_qv_sq : Summable fun v : HeightOneSpectrum (𝓞 F) => ((qv v) ^ 2)⁻¹ := by
  simp_rw [inv_qv_sq_eq]; exact summable_normP_rpow (by norm_num)

lemma summable_thetaV_subtype (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Summable fun p : PS S => thetaV p.1 :=
  ((summable_inv_qv_sq (F := F)).mul_left 2).subtype _

/-- A product over $\mathfrak p \notin S$ converges if its factors are $1 + O(N\mathfrak p^{-2})$ off a finite set. -/
lemma multipliable_subtype_of_bound (S : Finset (HeightOneSpectrum (𝓞 F))) (g : HeightOneSpectrum (𝓞 F) → ℝ)
    {C : ℝ} (B : Finset (HeightOneSpectrum (𝓞 F))) (hg : ∀ p ∉ B, |g p - 1| ≤ C * ((qv p) ^ 2)⁻¹) :
    Multipliable fun p : PS S => g p.1 := by
  have hs : Summable fun p : PS S => g p.1 - 1 := by
    have hsum : Summable fun p : PS S => C * ((qv p.1) ^ 2)⁻¹ := ((summable_inv_qv_sq (F := F)).mul_left C).subtype _
    refine Summable.of_norm_bounded_eventually hsum ?_
    have hfin : {p : PS S | p.1 ∈ B}.Finite :=
      (B.finite_toSet.preimage Subtype.val_injective.injOn)
    filter_upwards [hfin.compl_mem_cofinite] with p hp
    rw [Real.norm_eq_abs]; exact hg p.1 hp
  simpa using Real.multipliable_one_add_of_summable hs

lemma multipliable_of_bound (g : HeightOneSpectrum (𝓞 F) → ℝ) {C : ℝ} (B : Finset (HeightOneSpectrum (𝓞 F)))
    (hg : ∀ p ∉ B, |g p - 1| ≤ C * ((qv p) ^ 2)⁻¹) : Multipliable g := by
  refine multipliable_of_abs_sub_one_le g (C := C) (σ := 2) (by norm_num) ?_
  filter_upwards [B.finite_toSet.compl_mem_cofinite] with p hp
  have := hg p hp
  rw [inv_qv_sq_eq] at this
  convert this using 3

variable {Q : QuadForm (𝓞 F) n}

/-- The local factor $Z_\mathfrak p(s,\rho)$ at a finite place, as a function of the place. -/
abbrev zf (Q : QuadForm (𝓞 F) n) (ρ : Fˣ) (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  sphLocal Q v (algebraMap F (v.adicCompletion F) (ρ : F)) s

lemma abs_zf_sub_one_le (hQ : Q.Nondegenerate) (hn : 5 ≤ n) {v : HeightOneSpectrum (𝓞 F)} (hv : IsGoodPlace Q v)
    (ρ : Fˣ) (hρ : ordL v ρ = 0) {s : ℝ} (hs : 0 ≤ s) :
    |zf Q ρ s v - 1| ≤ 25 * ((qv v) ^ 2)⁻¹ := by
  have h1 := abs_sphLocal_sub_Ppar_le hQ hn hv ρ hs
  have hP : Ppar Q v ρ s = Pe Q v s := by unfold Ppar; rw [if_neg (by rw [hρ]; exact Int.not_odd_iff_even.mpr ⟨0, rfl⟩)]
  rw [hP] at h1
  have h2 := abs_Pe_sub_one_le hv (by omega) hs
  have hq := inv_pos.mpr (show (0 : ℝ) < (qv v) ^ 2 by have := one_lt_qv v; positivity)
  have hPe : Pe Q v s ≤ 1 + 10 * ((qv v) ^ 2)⁻¹ := by linarith [(abs_le.mp h2).2]
  have hq9 : ((qv v) ^ 2)⁻¹ ≤ 1 / 4 := by
    have h2 : (2 : ℝ) ≤ qv v := by exact_mod_cast (q_ge_two v)
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  calc |zf Q ρ s v - 1| ≤ |zf Q ρ s v - Pe Q v s| + |Pe Q v s - 1| := abs_sub_le _ _ _
    _ ≤ 2 * ((qv v) ^ 2)⁻¹ * Pe Q v s + 10 * ((qv v) ^ 2)⁻¹ := add_le_add h1 h2
    _ ≤ 2 * ((qv v) ^ 2)⁻¹ * (1 + 10 * ((qv v) ^ 2)⁻¹) + 10 * ((qv v) ^ 2)⁻¹ := by
        gcongr
    _ ≤ 25 * ((qv v) ^ 2)⁻¹ := by nlinarith

/-- The finite set of places where the $e(\mathfrak p)$ estimate is not available for $\rho$: bad places and places where $\rho$
is not a unit. -/
def badSet (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (ρ : Fˣ) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_not_isGoodPlace Q hQ).toFinset ∪ (finite_ordL_ne_zero ρ).toFinset

lemma not_mem_badSet {Q : QuadForm (𝓞 F) n} {hQ : Q.Nondegenerate} {ρ : Fˣ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badSet Q hQ ρ) : IsGoodPlace Q v ∧ ordL v ρ = 0 := by
  simp only [badSet, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_or, not_not] at hv
  exact hv

lemma multipliable_zf (hQ : Q.Nondegenerate) (hn : 5 ≤ n) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s) :
    Multipliable (zf Q ρ s) :=
  multipliable_of_bound _ (badSet Q hQ ρ) fun v hv =>
    abs_zf_sub_one_le hQ hn (not_mem_badSet hv).1 ρ (not_mem_badSet hv).2 hs

lemma multipliable_zf_subtype (hQ : Q.Nondegenerate) (hn : 5 ≤ n) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Multipliable fun p : PS S => zf Q ρ s p.1 :=
  multipliable_subtype_of_bound S _ (badSet Q hQ ρ) fun v hv =>
    abs_zf_sub_one_le hQ hn (not_mem_badSet hv).1 ρ (not_mem_badSet hv).2 hs

/-- **Splitting off $S$**: $Z(s,\rho) = |d_F|^{-n/2}\,\alpha_S([\rho])\prod_{\mathfrak p\notin S}Z_\mathfrak p(s,\rho)$. -/
theorem sphericalZetaAt_split (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s) :
    sphericalZetaAt Q Φ (ρ : F) s = |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) *
      alphaS Q Φ S s (locMap S ρ) * ∏' p : PS S, zf Q ρ s p.1 := by
  rw [sphericalZetaAt, alphaS_locMap]
  have hsplit := Multipliable.tprod_mul_tprod_compl (f := zf Q ρ s) (s := (S : Set (HeightOneSpectrum (𝓞 F))))
    (hasProd_fintype _).multipliable (multipliable_zf_subtype hQ hn ρ hs S)
  have hc : ∏' x : ↑((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), zf Q ρ s x = ∏' p : PS S, zf Q ρ s p.1 := rfl
  rw [← hsplit, Finset.tprod_subtype' S (zf Q ρ s), ← Finset.prod_coe_sort S, hc]
  ring

/-- $\delta_S = \sum_{\mathfrak p\notin S}\theta_\mathfrak p$. -/
def deltaS (S : Finset (HeightOneSpectrum (𝓞 F))) : ℝ := ∑' p : PS S, thetaV p.1

lemma Pe_pos_good {v : HeightOneSpectrum (𝓞 F)} (hv : IsGoodPlace Q v) (hn : 2 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 < Pe Q v s :=
  lt_of_lt_of_le (by norm_num) (Pe_ge hv hn hs)

lemma multipliable_Ppar (hQ : Q.Nondegenerate) (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, IsGoodPlace Q v) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s) :
    Multipliable fun p : PS S => Ppar Q p.1 ρ s := by
  refine multipliable_subtype_of_bound S (fun v => Ppar Q v ρ s) (C := 10)
    (S ∪ (finite_ordL_ne_zero ρ).toFinset) fun v hv => ?_
  · have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
    have hvo : ordL v ρ = 0 := by
      by_contra h
      exact hv (Finset.mem_union_right _ ((finite_ordL_ne_zero ρ).mem_toFinset.mpr h))
    have hP : Ppar Q v ρ s = Pe Q v s := by
      unfold Ppar; rw [if_neg (by rw [hvo]; exact Int.not_odd_iff_even.mpr ⟨0, rfl⟩)]
    show |Ppar Q v ρ s - 1| ≤ 10 * ((qv v) ^ 2)⁻¹
    rw [hP]
    exact abs_Pe_sub_one_le (hS v hvS) (by omega) hs

/-- **Weil's sandwich for one class** ($\mu(S) < Z(s,\rho)/Z_S(s,\rho) < \mu'(S)$, p. 108): with $\delta_S = \sum_{\mathfrak p\notin S}2N\mathfrak p^{-2}$,
$(1-\delta_S)\prod_{\mathfrak p\notin S}P_{\rho}(\mathfrak p) \le \prod_{\mathfrak p\notin S}Z_\mathfrak p(s,\rho) \le e^{\delta_S}\prod_{\mathfrak p\notin S}P_\rho(\mathfrak p)$. -/
theorem tprod_zf_sandwich (hQ : Q.Nondegenerate) (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, IsGoodPlace Q v) (ρ : Fˣ) {s : ℝ} (hs : 0 ≤ s) :
    (1 - deltaS S) * ∏' p : PS S, Ppar Q p.1 ρ s ≤ ∏' p : PS S, zf Q ρ s p.1 ∧
      ∏' p : PS S, zf Q ρ s p.1 ≤ Real.exp (deltaS S) * ∏' p : PS S, Ppar Q p.1 ρ s := by
  refine SphericalSum.tprod_sandwich (fun p : PS S => zf Q ρ s p.1) (fun p => Ppar Q p.1 ρ s)
    (fun p => thetaV p.1) (multipliable_zf_subtype hQ hn ρ hs S).hasProd
    (multipliable_Ppar hQ hn S hS ρ hs).hasProd (fun p => Ppar_nonneg Q p.1 ρ s) (fun p => thetaV_nonneg _)
    (fun p => thetaV_le_one _) (summable_thetaV_subtype S) le_rfl (fun p => ?_) (fun p => ?_)
  · have h := abs_sphLocal_sub_Ppar_le hQ hn (hS p.1 p.2) ρ hs
    have := (abs_le.mp h).1
    simp only [thetaV] at *
    nlinarith
  · have h := abs_sphLocal_sub_Ppar_le hQ hn (hS p.1 p.2) ρ hs
    have := (abs_le.mp h).2
    simp only [thetaV] at *
    nlinarith

/-- $B_S(s) = \prod_{\mathfrak p\notin S}P_0(\mathfrak p)$. -/
def BSe (Q : QuadForm (𝓞 F) n) (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) : ℝ := ∏' p : PS S, Pe Q p.1 s

/-- $r_\mathfrak p = P_1(\mathfrak p)/P_0(\mathfrak p)$. -/
def rS (Q : QuadForm (𝓞 F) n) (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) (p : PS S) : ℝ :=
  Po Q p.1 s / Pe Q p.1 s

lemma multipliable_Pe (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v)
    {s : ℝ} (hs : 0 ≤ s) : Multipliable fun p : PS S => Pe Q p.1 s :=
  multipliable_subtype_of_bound S _ S fun v hv => abs_Pe_sub_one_le (hS v hv) (by omega) hs

/-- **$\prod_{\mathfrak p\notin S}P_\rho(\mathfrak p) = B_S\prod_{\mathfrak p\in T(\rho)}r_\mathfrak p$**, $T(\rho)$ the primes outside $S$ where $\rho$ has odd order. -/
theorem tprod_Ppar_eq (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v)
    (ρ : Fˣ) (T : Finset (PS S)) (hT : ∀ p : PS S, p ∈ T ↔ Odd (ordL p.1 ρ)) {s : ℝ} (hs : 0 ≤ s) :
    ∏' p : PS S, Ppar Q p.1 ρ s = BSe Q S s * ∏ p ∈ T, rS Q S s p := by
  have hfac : ∀ p : PS S, Ppar Q p.1 ρ s = Pe Q p.1 s * (if p ∈ T then rS Q S s p else 1) := by
    intro p
    have hpos := Pe_pos_good (hS p.1 p.2) (by omega : 2 ≤ n) hs
    unfold Ppar rS
    by_cases hp : p ∈ T
    · rw [if_pos ((hT p).mp hp), if_pos hp]; field_simp
    · rw [if_neg (fun h => hp ((hT p).mpr h)), if_neg hp, mul_one]
  have h2 : HasProd (fun p : PS S => if p ∈ T then rS Q S s p else 1) (∏ p ∈ T, rS Q S s p) := by
    have : HasProd (fun p : PS S => if p ∈ T then rS Q S s p else 1)
        (∏ p ∈ T, if p ∈ T then rS Q S s p else 1) := hasProd_prod_of_ne_finset_one (fun p hp => by simp [hp])
    convert this using 1
    exact (Finset.prod_congr rfl fun p hp => by simp [hp]).symm
  rw [tprod_congr hfac, ((multipliable_Pe hn S hS hs).hasProd.mul h2).tprod_eq, BSe]

end StepA

/-! ### Step B: summing over $F^\times/F^{\times2} \cong \{T\}\times\Lambda_S$ -/

section StepB

open Classical

variable {Q : QuadForm (𝓞 F) n}

lemma rS_nonneg (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) (p : PS S) : 0 ≤ rS Q S s p :=
  div_nonneg (Po_nonneg Q p.1 s) (Pe_nonneg Q p.1 s)

lemma rS_le (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v) {s : ℝ}
    (hs : 0 ≤ s) (p : PS S) : rS Q S s p ≤ 9 * (normP p.1 : ℝ) ^ (-(1 + s)) := by
  have hPe := Pe_ge (hS p.1 p.2) (by omega : 2 ≤ n) hs
  have hPo := Po_le (hS p.1 p.2) (by omega : 2 ≤ n) hs
  rw [rS, div_le_iff₀ (by linarith), normP_rpow_neg_one_add, ← Xv]
  have : 0 ≤ (qv p.1)⁻¹ * Xv p.1 s := mul_nonneg (inv_pos.mpr (by have := one_lt_qv p.1; linarith)).le
    (Xv_pos p.1 s).le
  nlinarith

lemma summable_rS (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v) {s : ℝ}
    (hs : 0 < s) : Summable (rS Q S s) :=
  Summable.of_nonneg_of_le (rS_nonneg S s) (rS_le hn S hS hs.le)
    (((summable_normP_rpow (F := F) (by linarith : 1 < 1 + s)).mul_left 9).subtype _)

variable {S₀ S : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (hsub : S₀ ⊆ S)

/-- $\hat\alpha_S(\lambda) = \sum_{h\in G_S}\alpha_S(h)\langle\lambda,h\rangle_S$: the product of Weil's twisted local integrals at the places of
$S\cup\infty$ (p. 106, $\int|F|^s\lambda(F(x))\Phi$). -/
def ahat (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (s : ℝ) (d : LamS S) : ℝ :=
  ∑ h : GS F S, alphaS Q Φ S s h * (BS S d h : ℝ)

/-- **The restricted sum** $Y_S(s) = |d_F|^{-n/2}B_S|\Lambda_S|^{-1}\sum_{\lambda\in\Lambda_S}\hat\alpha_S(\lambda)\prod_{\mathfrak p\notin S}(1 + \chi_\lambda(\mathfrak p)r_\mathfrak p)$,
i.e. $2^{|S|}$ times Weil's $Z_S(s)$ (pp. 106–107). -/
def YS (Q : QuadForm (𝓞 F) n) (Φ : RealPlace F → (Fin n → ℝ) → ℝ) (s : ℝ) : ℝ :=
  |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * BSe Q S s *
    ((Fintype.card (LamS S) : ℝ)⁻¹ * ∑ d : LamS S, ahat Q Φ S s d *
      ∏' p : PS S, (1 + (chiS hS₀ hsub d p : ℝ) * rS Q S s p))

lemma alphaS_nonneg (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℝ) (h : GS F S) : 0 ≤ alphaS Q Φ S s h := by
  unfold alphaS
  refine mul_nonneg (Finset.prod_nonneg fun v _ => sphLocal_nonneg Q v.1 _ s) (Finset.prod_nonneg fun w _ => ?_)
  unfold Ainf
  split_ifs with hw
  · exact mul_nonneg zero_le_two (setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hΦ0 _ x)))
  · exact zero_le_one

include hS₀ hsub in
/-- **The sandwich for the whole spherical sum, with summability** (Weil 1982, §4.5, (4)–(6) and the bounds on p. 108):
for $s > 0$ the family $\rho \mapsto Z(s,\rho)$ is summable and
$$(1-\delta_S)\,Y_S(s) \le Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) \le e^{\delta_S}\,Y_S(s).$$ -/
theorem sphericalZeta_sandwich_summable (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hSg : ∀ v ∉ S, IsGoodPlace Q v)
    (hker : SqKernelCond S) {s : ℝ} (hs : 0 < s) :
    Summable (fun c : SqClasses F => sphericalZetaAt Q Φ ((Quotient.out c : Fˣ) : F) s) ∧
    ((1 - deltaS S) * YS hS₀ hsub Q Φ s ≤ sphericalZeta Q Φ s ∧
      sphericalZeta Q Φ s ≤ Real.exp (deltaS S) * YS hS₀ hsub Q Φ s) := by
  set C : ℝ := |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2)
  have hC : 0 ≤ C := Real.rpow_nonneg (abs_nonneg _) _
  set e := sqParam hS₀ hsub hker
  set a : Finset (PS S) → LamS S → ℝ := fun T d => alphaS Q Φ S s (locMap S (rhoT hS₀ hsub T) * d)
  -- the abstract Poisson–Euler identity
  have hpois : ∀ T, ∑ d, a T d = (Fintype.card (LamS S) : ℝ)⁻¹ *
      ∑ d, (∏ p ∈ T, (chiS hS₀ hsub d p : ℝ)) * ahat Q Φ S s d := by
    intro T
    have := sum_LamS_translate S hS2 hker (alphaS Q Φ S s) (locMap S (rhoT hS₀ hsub T))
    rw [this]
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [BS_rhoT]; push_cast; rfl
  have hW := (SphericalSum.hasSum_poisson (rS Q S s) (rS_nonneg S s) (summable_rS hn S hSg hs)
    (fun d p => (chiS hS₀ hsub d p : ℝ))
    (fun d p => by rcases chiS_pm hS₀ hsub d p with h | h <;> rw [h] <;> norm_num) a
    (fun T d => alphaS_nonneg Q hΦ0 S s _) (ahat Q Φ S s) hpois).mul_left (C * BSe Q S s)
  -- the terms
  set Zx : Finset (PS S) × LamS S → ℝ := fun x => sphericalZetaAt Q Φ ((Quotient.out (e x) : Fˣ) : F) s
  have hZx : ∀ x, Zx x = sphericalZetaAt Q Φ ((rhoT hS₀ hsub x.1 * liftU x.2 : Fˣ) : F) s := by
    intro x
    have hmk : (QuotientGroup.mk (Quotient.out (e x)) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) =
        QuotientGroup.mk (rhoT hS₀ hsub x.1 * liftU x.2) := by
      rw [show (QuotientGroup.mk (Quotient.out (e x)) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range) = e x from
        Quotient.out_eq _]
      rfl
    rw [mk_eq_mk_iff] at hmk
    obtain ⟨y, hy, hxy⟩ := hmk
    simp only [Zx]
    rw [hxy, sphericalZetaAt_mul_sq _ _ _ hy]
  set δ := deltaS S
  set W : Finset (PS S) × LamS S → ℝ := fun x => C * BSe Q S s * (a x.1 x.2 * ∏ p ∈ x.1, rS Q S s p)
  have hbound : ∀ x, (1 - δ) * W x ≤ Zx x ∧ Zx x ≤ Real.exp δ * W x := by
    rintro ⟨T, d⟩
    set ρ := rhoT hS₀ hsub T * liftU d
    have hsplit := sphericalZetaAt_split hQ hn Φ S ρ hs.le
    have hα : alphaS Q Φ S s (locMap S ρ) = a T d := by
      simp only [ρ, a, map_mul, locMap_liftU]
    have hT : ∀ p : PS S, p ∈ T ↔ Odd (ordL p.1 ρ) := by
      intro p
      rw [ordL_rhoT_mul_sUnit hS₀ hsub T (liftU_mem d)]
      split_ifs with h
      · exact ⟨fun _ => ⟨-1, by ring⟩, fun _ => h⟩
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h' (Int.not_odd_iff_even.mpr ⟨0, rfl⟩)⟩
    have hPP := tprod_Ppar_eq hn S hSg ρ T hT hs.le
    obtain ⟨hl, hu⟩ := tprod_zf_sandwich hQ hn S hSg ρ hs.le
    rw [hPP] at hl hu
    have ha0 : 0 ≤ a T d := alphaS_nonneg Q hΦ0 S s _
    rw [hZx]
    simp only [W]
    rw [hsplit, hα]
    constructor
    · calc (1 - δ) * (C * BSe Q S s * (a T d * ∏ p ∈ T, rS Q S s p))
          = C * a T d * ((1 - δ) * (BSe Q S s * ∏ p ∈ T, rS Q S s p)) := by ring
        _ ≤ C * a T d * ∏' p : PS S, zf Q ρ s p.1 := mul_le_mul_of_nonneg_left hl (mul_nonneg hC ha0)
    · calc C * a T d * ∏' p : PS S, zf Q ρ s p.1
          ≤ C * a T d * (Real.exp δ * (BSe Q S s * ∏ p ∈ T, rS Q S s p)) :=
            mul_le_mul_of_nonneg_left hu (mul_nonneg hC ha0)
        _ = Real.exp δ * (C * BSe Q S s * (a T d * ∏ p ∈ T, rS Q S s p)) := by ring
  have hZ0 : ∀ x, 0 ≤ Zx x := fun x => sphericalZetaAt_nonneg Q hΦ0 _ s
  have hWs : HasSum W _ := hW
  have hZs : Summable Zx :=
    Summable.of_nonneg_of_le hZ0 (fun x => (hbound x).2) (hWs.mul_left (Real.exp δ)).summable
  have hZeq : sphericalZeta Q Φ s = ∑' x, Zx x :=
    (Equiv.tsum_eq e (fun c => sphericalZetaAt Q Φ ((Quotient.out c : Fˣ) : F) s)).symm
  have hYS : YS hS₀ hsub Q Φ s = C * BSe Q S s * ((Fintype.card (LamS S) : ℝ)⁻¹ *
      ∑ d : LamS S, ahat Q Φ S s d * ∏' p : PS S, (1 + (chiS hS₀ hsub d p : ℝ) * rS Q S s p)) := rfl
  refine ⟨(e.summable_iff (f := fun c : SqClasses F => sphericalZetaAt Q Φ ((Quotient.out c : Fˣ) : F) s)).mp hZs,
    ?_⟩
  rw [hZeq, hYS]
  constructor
  · exact hasSum_le (fun x => (hbound x).1) (hWs.mul_left (1 - δ)) hZs.hasSum
  · exact hasSum_le (fun x => (hbound x).2) hZs.hasSum (hWs.mul_left (Real.exp δ))

include hS₀ hsub in
/-- **The sandwich for the whole spherical sum** (Weil 1982, §4.5, (4)–(6) and the bounds on p. 108): for $s > 0$,
$$(1-\delta_S)\,Y_S(s) \le Z(s) = \sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) \le e^{\delta_S}\,Y_S(s).$$ -/
theorem sphericalZeta_sandwich (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hSg : ∀ v ∉ S, IsGoodPlace Q v)
    (hker : SqKernelCond S) {s : ℝ} (hs : 0 < s) :
    (1 - deltaS S) * YS hS₀ hsub Q Φ s ≤ sphericalZeta Q Φ s ∧
      sphericalZeta Q Φ s ≤ Real.exp (deltaS S) * YS hS₀ hsub Q Φ s :=
  (sphericalZeta_sandwich_summable hS₀ hsub hQ hn hΦ0 hS2 hSg hker hs).2

end StepB

/-! ### Step C: the $\lambda = 1$ term is the plain zeta integral -/

section StepC

open Classical

variable {Q : QuadForm (𝓞 F) n}

lemma multipliable_one_add_chi_rS (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v)
    {s : ℝ} (hs : 0 < s) (χ : PS S → ℝ) (hχ : ∀ p, |χ p| ≤ 1) :
    Multipliable fun p : PS S => 1 + χ p * rS Q S s p := by
  refine Real.multipliable_one_add_of_summable ?_
  refine Summable.of_norm_bounded (summable_rS hn S hS hs) fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rS_nonneg S s p)]
  exact mul_le_of_le_one_left (rS_nonneg S s p) (hχ p)

/-- $B_S\prod_{\mathfrak p\notin S}(1 + \chi(\mathfrak p)r_\mathfrak p) = \prod_{\mathfrak p\notin S}(P_0 + \chi(\mathfrak p)P_1)$. -/
lemma BSe_mul_tprod (hn : 5 ≤ n) (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsGoodPlace Q v)
    {s : ℝ} (hs : 0 < s) (χ : PS S → ℝ) (hχ : ∀ p, |χ p| ≤ 1) :
    BSe Q S s * ∏' p : PS S, (1 + χ p * rS Q S s p) = ∏' p : PS S, (Pe Q p.1 s + χ p * Po Q p.1 s) := by
  rw [BSe, ← (multipliable_Pe hn S hS hs.le).tprod_mul (multipliable_one_add_chi_rS hn S hS hs χ hχ)]
  refine tprod_congr fun p => ?_
  have hpos := Pe_pos_good (hS p.1 p.2) (by omega : 2 ≤ n) hs.le
  rw [rS]; field_simp

/-- **The complex-place factor** $2^{-r_2}$, $r_2$ the number of complex places. It is $1$ for $F$ totally real; in general
the real-places-only spherical sum has residue $2^{-r_2}\rho_F\int\Phi$, the missing $2^{r_2}$ being supplied by the complex
local factors $Z_w(s,\rho) = 2\int_{\mathbb C^n}|Q_w|_{\mathbb C}^s\Phi_w$ (`SphericalResidueNF.lean`). -/
def cplxFac (F : Type) [Field F] [NumberField F] : ℝ := ((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F)⁻¹

lemma cplxFac_pos : 0 < cplxFac F := inv_pos.mpr (by positivity)

lemma cplxFac_eq_one [IsTotallyReal F] : cplxFac F = 1 := by
  rw [cplxFac, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, inv_one]

lemma card_infinitePlace_eq' :
    Fintype.card (InfinitePlace F) = Fintype.card (RealPlace F) + InfinitePlace.nrComplexPlaces F :=
  by convert InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F using 2

lemma integrable_rpow_mul (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    (w : RealPlace F) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Integrable fun x => |realVal Q w x| ^ s * Φ w x := by
  have hc := continuous_realVal Q w
  refine ((hΦ.integrable w).abs.add (by simpa [abs_mul] using (hΦ.integrable_mul w).abs)).mono'
    (((continuous_abs.comp hc).measurable.pow_const s).aestronglyMeasurable.mul
      (hΦ.integrable w).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have := rpow_le_one_add (abs_nonneg (realVal Q w x)) hs
  simp only [Pi.add_apply]
  nlinarith [abs_nonneg (Φ w x)]

/-- **The $\lambda = 1$ term is the zeta integral** (Weil 1982, p. 106: the integral with $\lambda = 1$ is
$\int_{V_\mathbb A}|F(x)|^s\Phi(x)\,d'x$): $|d_F|^{-n/2}B_S|\Lambda_S|^{-1}\hat\alpha_S(1)\prod_{\mathfrak p\notin S}(1 + r_\mathfrak p) = 2^{-r_2}Z(s)$ (`globalZeta`,
real places only; $2^{-r_2} = 1$ for $F$ totally real). -/
theorem lambda_one_term (hQ : Q.Nondegenerate) (hn : 5 ≤ n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : IsArchTestFn Q Φ) (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0)
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hS : ∀ v ∉ S, IsGoodPlace Q v) (hker : SqKernelCond S)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * BSe Q S s *
      ((Fintype.card (LamS S) : ℝ)⁻¹ * (ahat Q Φ S s 1 * ∏' p : PS S, (1 + 1 * rS Q S s p))) =
      cplxFac F * globalZeta Q Φ s := by
  have hahat : ahat Q Φ S s 1 = (∏ v : S, 2 * zetaWeil Q v.1 s) * ∏ w : RealPlace F, 2 * archZetaAt Q w (Φ w) s := by
    rw [ahat, ← sum_alphaS Q hQ (by omega) Φ S hs.le (fun w => integrable_rpow_mul Q hΦ w ⟨hs.le, hs1⟩) hnull]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [show (BS S ((1 : LamS S) : GS F S) h : ℝ) = 1 by
      rw [show ((1 : LamS S) : GS F S) = 1 from rfl, BS_one_left]; norm_num, mul_one]
  have hcard : (Fintype.card (LamS S) : ℝ) = 2 ^ S.card * 2 ^ Fintype.card (RealPlace F) *
      2 ^ InfinitePlace.nrComplexPlaces F := by
    rw [← Nat.card_eq_fintype_card, card_LamS S hker, card_infinitePlace_eq', pow_add, pow_add]; push_cast; ring
  have hprod : BSe Q S s * ∏' p : PS S, (1 + 1 * rS Q S s p) = ∏' p : PS S, zetaWeil Q p.1 s := by
    rw [BSe_mul_tprod hn S hS hs (fun _ => 1) (fun _ => by norm_num)]
    exact tprod_congr fun p => by rw [one_mul, Pe_add_Po Q hQ (by omega) p.1 hs.le]
  have hmult : Multipliable fun p : PS S => zetaWeil Q p.1 s := by
    have := (multipliable_Pe hn S hS hs.le).mul (multipliable_one_add_chi_rS hn S hS hs (fun _ => 1)
      (fun _ => by norm_num))
    refine this.congr fun p => ?_
    have hpos := Pe_pos_good (hS p.1 p.2) (by omega : 2 ≤ n) hs.le
    simp only [Pi.mul_apply, one_mul]
    rw [← Pe_add_Po Q hQ (by omega) p.1 hs.le, rS]; field_simp
  have hsplit := Multipliable.tprod_mul_tprod_compl (f := fun v => zetaWeil Q v s)
    (s := (S : Set (HeightOneSpectrum (𝓞 F)))) (hasProd_fintype _).multipliable hmult
  have hc : ∏' x : ↑((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ), zetaWeil Q x s = ∏' p : PS S, zetaWeil Q p.1 s := rfl
  rw [Finset.tprod_subtype' S (fun v => zetaWeil Q v s), hc, ← Finset.prod_coe_sort S] at hsplit
  rw [globalZeta, ← hsplit, archZeta, hahat, hcard, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ, Fintype.card_coe, cplxFac]
  calc |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * BSe Q S s *
        ((2 ^ S.card * 2 ^ Fintype.card (RealPlace F) * 2 ^ InfinitePlace.nrComplexPlaces F)⁻¹ *
          (2 ^ S.card * (∏ v : S, zetaWeil Q v.1 s) *
          (2 ^ Fintype.card (RealPlace F) * ∏ w, archZetaAt Q w (Φ w) s) * ∏' p : PS S, (1 + 1 * rS Q S s p)))
      = ((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F)⁻¹ * (|(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) *
          (∏ w, archZetaAt Q w (Φ w) s) *
          ((∏ v : S, zetaWeil Q v.1 s) * (BSe Q S s * ∏' p : PS S, (1 + 1 * rS Q S s p)))) := by
        field_simp
    _ = _ := by rw [hprod]

end StepC

/-! ### Step C': the $\lambda \ne 1$ terms have no pole -/

section StepC'

open Classical

variable {Q : QuadForm (𝓞 F) n}

lemma zetaStd_le_one (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 ≤ s) :
    zetaStd Q v s ≤ 1 := by
  rw [zetaStd, zetaInt]
  calc ∫ x in latL v n, ‖(NF.Qp v Q).evalIn (v.adicCompletion F) x‖ ^ s ∂(Measure.pi fun _ : Fin n => haarV v)
      ≤ ∫ x in latL v n, (1 : ℝ) ∂(Measure.pi fun _ : Fin n => haarV v) := by
        refine setIntegral_mono_on ?_ (integrableOn_const (measure_latL_haar_ne_top v)) (measurableSet_latL v)
          fun x hx => Real.rpow_le_one (norm_nonneg _)
            (norm_le_one_of_valued v (valued_evalIn_le_one v _ hx)) hs
        refine (Measure.integrableOn_of_bounded (M := 1) (measure_latL_haar_ne_top v) ?_ ?_)
        · have hcont : Continuous fun x : Fin n → v.adicCompletion F => (NF.Qp v Q).evalIn (v.adicCompletion F) x := by
            unfold QuadForm.evalIn
            exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by
              split_ifs <;> fun_prop
          exact ((continuous_norm.comp hcont).measurable.pow_const s).aestronglyMeasurable
        · refine (ae_restrict_iff' (measurableSet_latL v)).mpr (Eventually.of_forall fun x hx => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          exact Real.rpow_le_one (norm_nonneg _) (norm_le_one_of_valued v (valued_evalIn_le_one v _ hx)) hs
    _ = 1 := by
        rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, measure_latL, ENNReal.toReal_pow,
          ← Measure.real, haarV_real_O, one_pow]

lemma zetaWeil_le_two (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 0 ≤ s) :
    zetaWeil Q v s ≤ 2 := by
  have h2 : (2 : ℝ) ≤ qv v := by exact_mod_cast (q_ge_two v)
  rw [zetaWeil, div_le_iff₀ (one_sub_inv_qv_pos' v)]
  have := zetaStd_le_one Q v hs
  have : (qv v)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  linarith

lemma zetaWeil_nonneg' (Q : QuadForm (𝓞 F) n) (v : HeightOneSpectrum (𝓞 F)) (s : ℝ) : 0 ≤ zetaWeil Q v s := by
  rw [zetaWeil, zetaStd, zetaInt]
  exact div_nonneg (setIntegral_nonneg_of_ae_restrict (Eventually.of_forall fun _ =>
    Real.rpow_nonneg (norm_nonneg _) _)) (one_sub_inv_qv_pos' v).le

lemma archZetaAt_le (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ)
    (hΦ0 : ∀ w x, 0 ≤ Φ w x) (w : RealPlace F) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    archZetaAt Q w (Φ w) s ≤ ∫ x, (Φ w x + |realVal Q w x| * Φ w x) := by
  rw [archZetaAt]
  refine integral_mono (integrable_rpow_mul Q hΦ w hs) ((hΦ.integrable w).add (hΦ.integrable_mul w)) fun x => ?_
  have := rpow_le_one_add (abs_nonneg (realVal Q w x)) hs
  have := hΦ0 w x
  simp only
  nlinarith

lemma archZetaAt_nonneg (Q : QuadForm (𝓞 F) n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (w : RealPlace F) (s : ℝ) : 0 ≤ archZetaAt Q w (Φ w) s :=
  integral_nonneg fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hΦ0 w x)

/-- **$|\hat\alpha_S(\lambda)| \le \hat\alpha_S(1) \le K$** uniformly for $s \in (0, 1]$. -/
lemma abs_ahat_le (hQ : Q.Nondegenerate) (hn : 5 ≤ n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ}
    (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x) (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 F))) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (d : LamS S) :
    |ahat Q Φ S s d| ≤ (∏ v : S, (4 : ℝ)) * ∏ w : RealPlace F, 2 * ∫ x, (Φ w x + |realVal Q w x| * Φ w x) := by
  have h1 : |ahat Q Φ S s d| ≤ ∑ h : GS F S, alphaS Q Φ S s h := by
    rw [ahat]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [abs_mul, abs_of_nonneg (alphaS_nonneg Q hΦ0 S s h)]
    have : |(BS S d h : ℝ)| = 1 := by rcases BS_pm S d h with h' | h' <;> rw [h'] <;> norm_num
    rw [this, mul_one]
  rw [sum_alphaS Q hQ (by omega) Φ S hs.le (fun w => integrable_rpow_mul Q hΦ w ⟨hs.le, hs1⟩) hnull] at h1
  refine h1.trans (mul_le_mul (Finset.prod_le_prod₀ (fun v _ => by
      have := zetaWeil_nonneg' Q v.1 s; positivity) fun v _ => by
      have := zetaWeil_le_two Q v.1 hs.le; linarith)
    (Finset.prod_le_prod₀ (fun w _ => by have := archZetaAt_nonneg Q hΦ0 w s; positivity) fun w _ => by
      have := archZetaAt_le Q hΦ hΦ0 w ⟨hs.le, hs1⟩; linarith)
    (Finset.prod_nonneg fun w _ => by have := archZetaAt_nonneg Q hΦ0 w s; positivity)
    (Finset.prod_nonneg fun v _ => by norm_num))

variable {S₀ S : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (hsub : S₀ ⊆ S)

lemma liftU_not_isSquare {d : LamS S} (hd : d ≠ 1) : ¬ IsSquare ((liftU d : Fˣ) : F) := by
  rintro ⟨y, hy⟩
  apply hd
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have h1 : liftU d = Units.mk0 y hy0 ^ 2 := Units.ext (by simp [hy, sq])
  have h2 := locMap_liftU d
  rw [h1, map_pow, GS_sq] at h2
  exact Subtype.ext h2.symm

/-- An integral non-square in the class of $u_\lambda$: $a = u_\lambda\cdot\mathrm{den}^2 \in \mathcal O_F$. -/
lemma exists_integral_rep (u : Fˣ) : ∃ a : 𝓞 F, ∃ m : F, m ≠ 0 ∧ (a : F) = (u : F) * m ^ 2 := by
  obtain ⟨num, den, hden, hu⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (u : F)
  have hden0 : (algebraMap (𝓞 F) F den) ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hden
  refine ⟨num * den, algebraMap (𝓞 F) F den, hden0, ?_⟩
  rw [← hu]; push_cast; field_simp

include hS₀ hsub in
/-- **The $\lambda \ne 1$ terms are $o(1/s)$** (Weil 1982, p. 106, "only the one corresponding to $\lambda = 1$ gives a residue"): for
$\lambda \ne 1$, $s\,|d_F|^{-n/2}B_S|\Lambda_S|^{-1}\hat\alpha_S(\lambda)\prod_{\mathfrak p\notin S}(1 + \chi_\lambda(\mathfrak p)r_\mathfrak p) \to 0$. The twisted
product is $\prod R_\mathfrak p(\chi X)\cdot L^{(S)}(1+s,\chi_\lambda)$ with $\prod R$ bounded, and $sL^{(S)}(1+s,\chi_\lambda) \to 0$
(`QTwist.tendsto_mul_LFunction_zero`, via $\zeta_E/\zeta_F$, $E = F(\sqrt{u_\lambda})$). -/
theorem tendsto_twist_term (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hSg : ∀ v ∉ S, IsGoodPlace Q v)
    (d : LamS S) (hd : d ≠ 1) :
    Tendsto (fun s : ℝ => s * (|(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * BSe Q S s *
      ((Fintype.card (LamS S) : ℝ)⁻¹ * (ahat Q Φ S s d *
        ∏' p : PS S, (1 + (chiS hS₀ hsub d p : ℝ) * rS Q S s p))))) (𝓝[>] 0) (𝓝 0) := by
  set C : ℝ := |(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2)
  set χ : PS S → ℝ := fun p => (chiS hS₀ hsub d p : ℝ)
  have hχ : ∀ p, χ p = 1 ∨ χ p = -1 := fun p => by
    rcases chiS_pm hS₀ hsub d p with h | h <;> simp [χ, h]
  have hχa : ∀ p, |χ p| ≤ 1 := fun p => by rcases hχ p with h | h <;> rw [h] <;> norm_num
  -- the extended character and the L-function
  set χ' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if h : v ∈ S then 0 else χ ⟨v, h⟩
  obtain ⟨a, m, hm, ham⟩ := exists_integral_rep (liftU d)
  have hasq : ¬ IsSquare (a : F) := by
    intro ⟨y, hy⟩
    apply liftU_not_isSquare hd
    exact ⟨y / m, by rw [ham] at hy; field_simp; linear_combination hy⟩
  have hL := QTwist.tendsto_mul_LFunction_zero S a hasq χ' (fun p hp => by simp [χ', hp])
    (fun p hp => by simp only [χ', dif_neg hp]; exact hχ ⟨p, hp⟩)
    (fun p hp h => by
      simp only [χ', dif_neg hp] at h
      have h' : ((chiS hS₀ hsub d ⟨p, hp⟩ : ℤ) : ℝ) = 1 := h
      obtain ⟨z, hz⟩ := isSquare_of_chiS hS₀ hsub hS2 d ⟨p, hp⟩ (by exact_mod_cast h')
      refine ⟨z * algebraMap F _ m, ?_⟩
      rw [ham, map_mul, map_pow, hz]; ring)
  -- bounded part
  set δR : ℝ := ∑' p : PS S, 4 * ((qv p.1) ^ 2)⁻¹
  -- the key estimate on (0, 1]
  have hKα := fun s (hs : 0 < s) (hs1 : s ≤ 1) => abs_ahat_le hQ hn hΦ hΦ0 hnull S hs hs1 d
  set Kα : ℝ := (∏ v : S, (4 : ℝ)) * ∏ w : RealPlace F, 2 * ∫ x, (Φ w x + |realVal Q w x| * Φ w x)
  have hC : 0 ≤ C := Real.rpow_nonneg (abs_nonneg _) _
  have hcard : 0 < (Fintype.card (LamS S) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hest : ∀ s, 0 < s → s ≤ 1 →
      |s * (C * BSe Q S s * ((Fintype.card (LamS S) : ℝ)⁻¹ * (ahat Q Φ S s d *
        ∏' p : PS S, (1 + χ p * rS Q S s p))))| ≤
      C * (Fintype.card (LamS S) : ℝ)⁻¹ * Kα * Real.exp δR *
        (s * ∏' v, (1 - χ' v * (normP v : ℝ) ^ (-(1 + s)))⁻¹) := by
    intro s hs hs1
    set R : PS S → ℝ := fun p => genRatio p.1 (NF.Qp p.1 Q) (χ p * Xv p.1 s)
    set L : PS S → ℝ := fun p => (1 - χ p * (normP p.1 : ℝ) ^ (-(1 + s)))⁻¹
    have hgood : ∀ p : PS S, ¬ NF.π p.1 ∣ 2 ∧ ¬ NF.π p.1 ∣ (NF.Qp p.1 Q).hessian.det :=
      fun p => not_dvd_of_isGoodPlace (hSg p.1 p.2)
    have hχX : ∀ p : PS S, |χ p * Xv p.1 s| ≤ 1 := fun p => by
      rw [abs_mul]; exact mul_le_one₀ (hχa p) (abs_nonneg _) (abs_Xv_le_one p.1 hs.le)
    have hRb : ∀ p : PS S, |R p - 1| ≤ 4 * ((qv p.1) ^ 2)⁻¹ := fun p => by
      have h := abs_genRatio_sub_one_le p.1 (NF.Qp p.1 Q) (by omega) (hgood p).1 (hgood p).2 (hχX p)
      refine h.trans (mul_le_mul_of_nonneg_left (inv_anti₀ (by have := one_lt_qv p.1; positivity)
        (pow_le_pow_right₀ (one_lt_qv p.1).le (by omega))) (by norm_num))
    have hq3 : ∀ p : PS S, (3 : ℝ) ≤ qv p.1 := fun p => by
      haveI : Fintype (IsLocalRing.ResidueField (p.1.adicCompletionIntegers F)) := Fintype.ofFinite _
      exact_mod_cast DVR.three_le_q (NF.irreducible_π p.1) (hgood p).1
    have hθ1 : ∀ p : PS S, 4 * ((qv p.1) ^ 2)⁻¹ ≤ 1 := fun p => by
      have := hq3 p
      rw [mul_comm, ← div_eq_inv_mul, div_le_one (by positivity)]; nlinarith
    have hRpos : ∀ p : PS S, 0 < R p := fun p => by
      have := (abs_le.mp (hRb p)).1
      have h9 : 4 * ((qv p.1) ^ 2)⁻¹ ≤ 4 / 9 := by
        have := hq3 p
        rw [mul_comm, ← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      linarith
    have hLb : ∀ p : PS S, |L p - 1| ≤ 2 * (normP p.1 : ℝ) ^ (-(1 + s)) := fun p =>
      QTwist.abs_lfac_sub_one_le p.1 (by linarith) (hχa p)
    have hLpos : ∀ p : PS S, 0 < L p := fun p => inv_pos.mpr (QTwist.one_sub_pos p.1 (by linarith) (hχa p))
    have hRm : Multipliable R := by
      have := multipliable_subtype_of_bound S (fun v => if h : v ∈ S then 1 else R ⟨v, h⟩) S fun v hv => by
        simp only [dif_neg hv]; exact hRb ⟨v, hv⟩
      exact this.congr fun p => by simp only [dif_neg p.2]
    have hLm : Multipliable L := by
      have hs' : Summable fun p : PS S => L p - 1 :=
        Summable.of_norm_bounded ((((summable_normP_rpow (F := F) (by linarith : 1 < 1 + s)).mul_left 2).subtype
          ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)))
          (fun p => by rw [Real.norm_eq_abs]; exact hLb p)
      simpa using Real.multipliable_one_add_of_summable hs'
    have hBP : BSe Q S s * ∏' p : PS S, (1 + χ p * rS Q S s p) = (∏' p : PS S, R p) * ∏' p : PS S, L p := by
      rw [BSe_mul_tprod hn S hSg hs χ hχa, ← hRm.tprod_mul hLm]
      refine tprod_congr fun p => ?_
      rw [Pe_add_mul_Po hQ (by omega) hs.le (hχ p)]
      simp only [R, L]
      rw [normP_rpow_neg_one_add, div_eq_mul_inv, Xv]
      congr 2; ring
    -- bounds on the two products
    have hR0 : 0 ≤ ∏' p : PS S, R p := tprod_nonneg fun p => (hRpos p).le
    have hRup : ∏' p : PS S, R p ≤ Real.exp δR := by
      have := (SphericalSum.tprod_sandwich R (fun _ => (1 : ℝ)) (fun p => 4 * ((qv p.1) ^ 2)⁻¹)
        hRm.hasProd hasProd_one (fun _ => zero_le_one) (fun p => by have := one_lt_qv p.1; positivity)
        hθ1 (((summable_inv_qv_sq (F := F)).mul_left 4).subtype _) le_rfl
        (fun p => by have := (abs_le.mp (hRb p)).1; linarith) (fun p => by have := (abs_le.mp (hRb p)).2; linarith)).2
      simpa using this
    have hL0 : 0 ≤ ∏' p : PS S, L p := tprod_nonneg fun p => (hLpos p).le
    have hLeq : ∏' p : PS S, L p = ∏' v, (1 - χ' v * (normP v : ℝ) ^ (-(1 + s)))⁻¹ := by
      have hm' : Multipliable fun x : ↑((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) =>
          (1 - χ' x * (normP x.1 : ℝ) ^ (-(1 + s)))⁻¹ := by
        refine hLm.congr fun p => ?_
        simp only [χ', L, dif_neg p.2]
      have hsplit := Multipliable.tprod_mul_tprod_compl (f := fun v => (1 - χ' v * (normP v : ℝ) ^ (-(1 + s)))⁻¹)
        (s := (S : Set (HeightOneSpectrum (𝓞 F)))) (hasProd_fintype _).multipliable hm'
      rw [← hsplit]
      have h1 : ∏' x : ↑(S : Set (HeightOneSpectrum (𝓞 F))), (1 - χ' x * (normP x.1 : ℝ) ^ (-(1 + s)))⁻¹ = 1 := by
        rw [Finset.tprod_subtype' S (fun v => (1 - χ' v * (normP v : ℝ) ^ (-(1 + s)))⁻¹)]
        exact Finset.prod_eq_one fun v hv => by simp [χ', hv]
      rw [h1, one_mul]
      exact tprod_congr fun p => by simp only [χ', L, dif_neg p.2]
    have hA := hKα s hs hs1
    rw [show C * BSe Q S s * ((Fintype.card (LamS S) : ℝ)⁻¹ * (ahat Q Φ S s d *
        ∏' p : PS S, (1 + χ p * rS Q S s p))) = C * (Fintype.card (LamS S) : ℝ)⁻¹ * ahat Q Φ S s d *
        (BSe Q S s * ∏' p : PS S, (1 + χ p * rS Q S s p)) by ring, hBP, ← hLeq]
    rw [abs_mul, abs_of_pos hs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hC, abs_of_nonneg (inv_pos.mpr hcard).le,
      abs_of_nonneg (mul_nonneg hR0 hL0)]
    have hKα0 : 0 ≤ Kα := le_trans (abs_nonneg _) hA
    calc s * (C * (Fintype.card (LamS S) : ℝ)⁻¹ * |ahat Q Φ S s d| * ((∏' p : PS S, R p) * ∏' p : PS S, L p))
        ≤ s * (C * (Fintype.card (LamS S) : ℝ)⁻¹ * Kα * (Real.exp δR * ∏' p : PS S, L p)) := by
          gcongr
      _ = C * (Fintype.card (LamS S) : ℝ)⁻¹ * Kα * Real.exp δR * (s * ∏' p : PS S, L p) := by ring
  have hT : Tendsto (fun s : ℝ => C * (Fintype.card (LamS S) : ℝ)⁻¹ * Kα * Real.exp δR *
      (s * ∏' v, (1 - χ' v * (normP v : ℝ) ^ (-(1 + s)))⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    have := hL.const_mul (C * (Fintype.card (LamS S) : ℝ)⁻¹ * Kα * Real.exp δR)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ hT
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  rw [Real.norm_eq_abs]
  exact hest s hs.1 hs.2

include hS₀ hsub in
/-- **Weil's (4): the residue of the restricted sum** $s\,Y_S(s) \to 2^{-r_2}\rho_F\int\Phi\,dx$ (real places only): the $\lambda = 1$ term is the zeta integral
(`lambda_one_term`, `GlobalZeta.tendsto_mul_globalZeta_zero`) and the others vanish (`tendsto_twist_term`). -/
theorem tendsto_mul_YS (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (hSg : ∀ v ∉ S, IsGoodPlace Q v)
    (hker : SqKernelCond S) :
    Tendsto (fun s => s * YS hS₀ hsub Q Φ s) (𝓝[>] 0)
      (𝓝 (cplxFac F * (dedekindZeta_residue F * phiIntegral Φ))) := by
  set term : LamS S → ℝ → ℝ := fun d s => s * (|(NumberField.discr F : ℝ)| ^ (-(n : ℝ) / 2) * BSe Q S s *
    ((Fintype.card (LamS S) : ℝ)⁻¹ *
    (ahat Q Φ S s d * ∏' p : PS S, (1 + (chiS hS₀ hsub d p : ℝ) * rS Q S s p))))
  have hsum : ∀ s, s * YS hS₀ hsub Q Φ s = ∑ d, term d s := by
    intro s
    simp only [YS, term, Finset.mul_sum]
  have h1 : Tendsto (term 1) (𝓝[>] 0) (𝓝 (cplxFac F * (dedekindZeta_residue F * phiIntegral Φ))) := by
    refine ((GlobalZeta.tendsto_mul_globalZeta_zero Q hQ (by omega) hΦ hnull).const_mul (cplxFac F)).congr' ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    simp only [term]
    have hp : ∏' p : PS S, (1 + (chiS hS₀ hsub 1 p : ℝ) * rS Q S s p) = ∏' p : PS S, (1 + 1 * rS Q S s p) :=
      tprod_congr fun p => by rw [chiS_one]; norm_num
    rw [hp, lambda_one_term hQ hn hΦ hnull hSg hker hs.1 hs.2]
    ring
  have h2 : Tendsto (fun s => ∑ d ∈ Finset.univ.erase 1, term d s) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ.erase (1 : LamS S)) (f := term) (x := 𝓝[>] (0 : ℝ))
      (a := fun _ => (0 : ℝ)) fun d hd =>
        tendsto_twist_term hS₀ hsub hQ hn hΦ hΦ0 hnull hS2 hSg d (Finset.ne_of_mem_erase hd)
    rw [Finset.sum_const_zero] at this
    exact this
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun s => ?_
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : LamS S))]

end StepC'

/-! ### The theorem: Weil's (8) -/

open Classical in
lemma phiIntegral_nonneg {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x) : 0 ≤ phiIntegral Φ :=
  mul_nonneg (Finset.prod_nonneg fun w _ => integral_nonneg (hΦ0 w))
    (tprod_nonneg fun v => measureReal_nonneg)

/-- **Weil's (8), real places only, any number field** (A. Weil, *Adeles and Algebraic Groups*, 1982, §4.5, (8), p. 108). For
$F$ any number field with $r_2$ complex places, the spherical sum built from the real places only (`sphericalZeta`) satisfies
$\lim_{s\to0^+}s\sum_\rho Z(s,\rho) = 2^{-r_2}\rho_F\int\Phi\,dx$ (`cplxFac`). The complex places are added in
`SphericalResidueNF.lean` (`tendsto_mul_sphericalZetaNF_zero`), which removes the $2^{-r_2}$. Below: the totally real case
`tendsto_mul_sphericalZeta_zero` ($r_2 = 0$). Hypotheses as there: $Q$ nondegenerate over $\mathcal O_F$ in $n \ge 5$ variables, and $\Phi = \bigotimes_w\Phi_w\otimes\bigotimes_v\mathbf 1_{L_v}$ with
$\Phi_w \ge 0$ admissible (`IsArchTestFn`) and the real null cones Lebesgue-null,
$$\lim_{s\to0^+}s\sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) = \rho_F\int_{V(\mathbb A)}\Phi(x)\,dx,$$
$Z(s,\rho)$ Weil's spherical zeta function (`sphericalZetaAt`, (1) p. 102), $\rho_F$ = `dedekindZeta_residue F`, $dx$ the Tamagawa
(self-dual) measure (`phiIntegral`). The same constant as the plain zeta integral (`tendsto_mul_globalZeta_zero`).

*Proof* (Weil's, without class field theory or Hecke $L$-functions): for every finite $S$ containing the bad places, the dyadic
places, a class-group generating set and the kernel-condition places, $(1-\delta_S)Y_S(s) \le Z(s) \le e^{\delta_S}Y_S(s)$
(`sphericalZeta_sandwich`, Weil's $\mu(S), \mu'(S)$) and $sY_S(s) \to \rho_F\int\Phi$ (`tendsto_mul_YS`); $\delta_S =
\sum_{\mathfrak p\notin S}2N\mathfrak p^{-2} \to 0$ as $S$ grows (`tendsto_mul_of_sandwich`). Unconditional. -/
@[kb "weil1982" "§4.5, (8), p. 108 (residue of Z(s) = Σ_ρ Z(s,ρ) at s = 0; real places)"]
theorem tendsto_mul_sphericalZeta_zero_real (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hn : 5 ≤ n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    Tendsto (fun s => s * sphericalZeta Q Φ s) (𝓝[>] 0)
      (𝓝 (cplxFac F * (dedekindZeta_residue F * phiIntegral Φ))) := by
  classical
  have hL : 0 ≤ cplxFac F * (dedekindZeta_residue F * phiIntegral Φ) :=
    mul_nonneg cplxFac_pos.le (mul_nonneg (dedekindZeta_residue_pos F).le (phiIntegral_nonneg hΦ0))
  refine SphericalSum.tendsto_mul_of_sandwich hL fun ε hε => ?_
  set δ : ℝ := min (ε / 2) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨S₀, hS₀⟩ := exists_genProp (F := F)
  obtain ⟨S₁, hS₀₁, hS₁⟩ := exists_sqKernelCond hS₀
  obtain ⟨A, hA⟩ := SphericalSum.exists_tail_le (fun v : HeightOneSpectrum (𝓞 F) => thetaV v)
    (fun v => thetaV_nonneg v) ((summable_inv_qv_sq (F := F)).mul_left 2) hδ0
  set D : Finset (HeightOneSpectrum (𝓞 F)) := (QTwist.finite_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).toFinset
  set Bd : Finset (HeightOneSpectrum (𝓞 F)) := (finite_not_isGoodPlace Q hQ).toFinset
  set S := S₁ ∪ D ∪ Bd ∪ A
  have hsub : S₀ ⊆ S := hS₀₁.trans (by intro v hv; simp [S, hv])
  have hker : SqKernelCond S := hS₁ S (by intro v hv; simp [S, hv])
  have hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S := fun v hv => by
    have hD : v ∈ D := (QTwist.finite_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).mem_toFinset.mpr hv
    simp only [S, Finset.mem_union]; left; left; right; exact hD
  have hSg : ∀ v ∉ S, IsGoodPlace Q v := fun v hv => by
    by_contra h
    apply hv
    simp only [S, Finset.mem_union]; left; right
    exact (finite_not_isGoodPlace Q hQ).mem_toFinset.mpr h
  have hdel : deltaS S ≤ δ := by
    have h := hA S (by intro v hv; simp [S, hv])
    have hg : Summable fun v : HeightOneSpectrum (𝓞 F) => if v ∈ S then 0 else thetaV v :=
      ((summable_inv_qv_sq (F := F)).mul_left 2).of_nonneg_of_le
        (fun v => by split_ifs <;> simp [thetaV_nonneg v]) fun v => by
          split_ifs <;> simp [thetaV, thetaV_nonneg v]
    refine le_trans (Summable.tsum_le_tsum_of_inj (fun p : PS S => p.1) Subtype.val_injective
      (fun v _ => by split_ifs <;> simp [thetaV_nonneg v]) (fun p => by simp [p.2])
      (summable_thetaV_subtype S) hg) h
  have hdel0 : 0 ≤ deltaS S := tsum_nonneg fun p => thetaV_nonneg _
  refine ⟨1 - deltaS S, Real.exp (deltaS S), YS hS₀ hsub Q Φ, by linarith, by linarith, ?_, ?_,
    tendsto_mul_YS hS₀ hsub hQ hn hΦ hΦ0 hnull hS2 hSg hker⟩
  · have h1 : Real.exp (deltaS S) ≤ Real.exp δ := Real.exp_le_exp.mpr hdel
    have h2 : |Real.exp δ - 1| ≤ 2 * |δ| := Real.abs_exp_sub_one_le (by rw [abs_of_pos hδ0]; linarith)
    rw [abs_of_pos hδ0] at h2
    have := (abs_le.mp h2).2
    linarith
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sphericalZeta_sandwich hS₀ hsub hQ hn hΦ0 hS2 hSg hker hs

/-- **Weil's (8): the residue of the spherical sum** (A. Weil, *Adeles and Algebraic Groups*, 1982, §4.5, (8), p. 108). For $F$
totally real, $Q$ nondegenerate over $\mathcal O_F$ in $n \ge 5$ variables, and $\Phi = \bigotimes_w\Phi_w\otimes\bigotimes_v\mathbf 1_{L_v}$ with
$\Phi_w \ge 0$ admissible (`IsArchTestFn`) and the real null cones Lebesgue-null,
$$\lim_{s\to0^+}s\sum_{\rho\in F^\times/F^{\times2}}Z(s,\rho) = \rho_F\int_{V(\mathbb A)}\Phi(x)\,dx,$$
$Z(s,\rho)$ Weil's spherical zeta function (`sphericalZetaAt`, (1) p. 102), $\rho_F$ = `dedekindZeta_residue F`, $dx$ the Tamagawa
(self-dual) measure (`phiIntegral`). The same constant as the plain zeta integral (`tendsto_mul_globalZeta_zero`).

*Proof* (Weil's, without class field theory or Hecke $L$-functions): for every finite $S$ containing the bad places, the dyadic
places, a class-group generating set and the kernel-condition places, $(1-\delta_S)Y_S(s) \le Z(s) \le e^{\delta_S}Y_S(s)$
(`sphericalZeta_sandwich`, Weil's $\mu(S), \mu'(S)$) and $sY_S(s) \to \rho_F\int\Phi$ (`tendsto_mul_YS`); $\delta_S =
\sum_{\mathfrak p\notin S}2N\mathfrak p^{-2} \to 0$ as $S$ grows (`tendsto_mul_of_sandwich`). Unconditional. The general-field version is `tendsto_mul_sphericalZeta_zero_real`. -/
@[kb "weil1982" "§4.5, (8), p. 108 (residue of Z(s) = Σ_ρ Z(s,ρ) at s = 0)"]
theorem tendsto_mul_sphericalZeta_zero [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hn : 5 ≤ n) {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ : IsArchTestFn Q Φ) (hΦ0 : ∀ w x, 0 ≤ Φ w x)
    (hnull : ∀ w, ∀ᵐ x : Fin n → ℝ, realVal Q w x ≠ 0) :
    Tendsto (fun s => s * sphericalZeta Q Φ s) (𝓝[>] 0) (𝓝 (dedekindZeta_residue F * phiIntegral Φ)) := by
  simpa [cplxFac_eq_one] using tendsto_mul_sphericalZeta_zero_real Q hQ hn hΦ hΦ0 hnull

/-- **The spherical sum converges** for $s > 0$ and $\Phi_w \ge 0$ (any number field; real places only): the family
$\rho \mapsto Z(s,\rho)$ over $F^\times/F^{\times2}$ is summable (from the sandwich, Weil p. 108). -/
theorem summable_sphericalZetaAt (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate) (hn : 5 ≤ n)
    {Φ : RealPlace F → (Fin n → ℝ) → ℝ} (hΦ0 : ∀ w x, 0 ≤ Φ w x) {s : ℝ} (hs : 0 < s) :
    Summable (fun c : SqClasses F => sphericalZetaAt Q Φ ((Quotient.out c : Fˣ) : F) s) := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_genProp (F := F)
  obtain ⟨S₁, hS₀₁, hS₁⟩ := exists_sqKernelCond hS₀
  set D : Finset (HeightOneSpectrum (𝓞 F)) := (QTwist.finite_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).toFinset
  set Bd : Finset (HeightOneSpectrum (𝓞 F)) := (finite_not_isGoodPlace Q hQ).toFinset
  set S := S₁ ∪ D ∪ Bd
  have hsub : S₀ ⊆ S := hS₀₁.trans (by intro v hv; simp [S, hv])
  have hker : SqKernelCond S := hS₁ S (by intro v hv; simp [S, hv])
  have hS2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S := fun v hv => by
    have hD : v ∈ D := (QTwist.finite_mem_asIdeal (two_ne_zero : (2 : 𝓞 F) ≠ 0)).mem_toFinset.mpr hv
    simp only [S, Finset.mem_union]; left; right; exact hD
  have hSg : ∀ v ∉ S, IsGoodPlace Q v := fun v hv => by
    by_contra h
    apply hv
    simp only [S, Finset.mem_union]; right
    exact (finite_not_isGoodPlace Q hQ).mem_toFinset.mpr h
  exact (sphericalZeta_sandwich_summable hS₀ hsub hQ hn hΦ0 hS2 hSg hker hs).1

/-- **Weil's (8) for a totally positive definite form and the Gaussian** $\Phi_w = e^{-aQ_w}$ ($a > 0$): unconditional,
$\lim_{s\to0^+}s\sum_{\rho}Z(s,\rho) = \rho_F|d_F|^{-n/2}\prod_w\int_{\mathbb R^n}e^{-aQ_w(x)}dx$. -/
@[kb "weil1982" "§4.5, (8), p. 108 (totally definite case, Gaussian Φ_∞)"]
theorem tendsto_mul_sphericalZeta_zero_gaussian [IsTotallyReal F] (Q : QuadForm (𝓞 F) n) (hQ : Q.Nondegenerate)
    (hpos : GlobalZeta.IsTotallyPosDef Q) (hn : 5 ≤ n) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s => s * sphericalZeta Q (gaussian Q a) s) (𝓝[>] 0)
      (𝓝 (dedekindZeta_residue F * phiIntegral (gaussian Q a))) :=
  tendsto_mul_sphericalZeta_zero Q hQ hn (isArchTestFn_gaussian hpos ha)
    (fun w x => (Real.exp_pos _).le) (fun w => ae_realVal_ne_zero hpos (by omega) w)

end QuadFormsKB.SphericalZeta
