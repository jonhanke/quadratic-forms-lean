/-
# The example $x^2 + y^2 + z^2 + 2w^2$: level 8, character $\chi_8$ (deliverable 4)

$Q = x_0^2 + x_1^2 + x_2^2 + 2x_3^2$ (`q1112`, level 8, $\chi_Q = \chi_8$). The Eisenstein space of $M_2(\Gamma_0(8), \chi_8)$ is
spanned by $E^{1,\chi_8}$ and $E^{\chi_8,1}$ (`dsEisMF` with $(u, v, t) = (1, 8, 1)$ and $(8, 1, 1)$), and
$$E_Q := \frac{4\sqrt2}{\pi^2}E^{1,\chi_8} - \frac1{\pi^2}E^{\chi_8,1}
  = 1 + \sum_{e \ge 1}\bigl(-2\sigma_1^{1,\chi_8}(e) + 8\sigma_1^{\chi_8,1}(e)\bigr)q^e$$
(`eisQ1112_eq_qExpansion`). The constants come from $g(\chi_8) = 2\sqrt2$ (`gaussSum_chi8`) and
$L(2,\chi_8) = \pi^2/(8\sqrt2)$, i.e. $\sum_{d\in\mathbb{Z}}\chi_8(d)d^{-2} = \pi^2/(4\sqrt2)$ (`tsum_chi8_div_sq`, from the Fourier
series of the Bernoulli polynomial $B_2$, Mathlib's `hasSum_one_div_nat_pow_mul_cos`).

**Cuspidality** (`isZeroAtImInfty_thetaGen_sub_eisQ1112`): $\Theta_{\mathrm{Gen}(Q)} - E_Q$ vanishes at every cusp. Every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$ is $\gamma_0\delta T^k$ with $\gamma_0 \in \Gamma_0(8)$ and $\delta \in \{1, S, \delta_2, \delta_4\}$,
$\delta_g = \begin{pmatrix}1&0\\g&1\end{pmatrix}$ (`exists_gamma0_eight`; cusps $\infty, 0, \tfrac12, \tfrac14$), and the constant terms are:

| cusp | $\Theta_Q$ | $E_Q$ |
|---|---|---|
| $\infty$ | $1$ | $1$ |
| $0$ ($S$) | $M_A(0,1) = -\tfrac14\cdot 2^{-1/2}$ | $-\pi^{-2}\sum_n\chi_8(n)n^{-2} = -\tfrac1{4\sqrt2}$ |
| $\tfrac12$, $\tfrac14$ | $M_A(1, 2) = M_A(1, 4) = 0$ (vanishing Gauss sums) | $0$ |
-/
import QuadFormsKB.Siegel.EisensteinWt2.A2A2
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

open Complex Filter Topology ModularForm
open scoped Real UpperHalfPlane MatrixGroups

namespace QuadFormsKB.Siegel.EisensteinWt2

open QuadFormsKB.Siegel

/-! ### $\chi_8$ as a complex Dirichlet character -/

/-- $\chi_8$ ($\mathbb{Q}(\sqrt2)$) as a Dirichlet character modulo 8 with values in $\mathbb{C}$. -/
noncomputable def chi8C : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

lemma chi8C_apply (a : ZMod 8) : chi8C a = (ZMod.χ₈ a : ℂ) := rfl

lemma chi8C_intCast (n : ℤ) :
    chi8C (n : ZMod 8) = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  rw [chi8C_apply, ZMod.χ₈_int_eq_if_mod_eight]
  split_ifs <;> simp

lemma chi8C_neg_one : chi8C (-1) = 1 := by
  have : ZMod.χ₈ (-1) = 1 := by decide
  rw [chi8C_apply, this]; simp

lemma chi8C_ne_one : chi8C ≠ 1 := by
  intro h
  have h3 := congr_arg (fun χ : DirichletCharacter ℂ 8 => χ 3) h
  simp only [chi8C_apply] at h3
  have hu : IsUnit (3 : ZMod 8) := by decide
  rw [MulChar.one_apply hu] at h3
  have : (ZMod.χ₈ 3 : ℂ) = -1 := by norm_num [show ZMod.χ₈ 3 = -1 from rfl]
  rw [this] at h3; norm_num at h3

lemma chi8C_inv : chi8C⁻¹ = chi8C := by
  ext a
  rw [MulChar.inv_apply_eq_inv', chi8C_apply]
  have : ∀ x : ZMod 8, ZMod.χ₈ x = 0 ∨ ZMod.χ₈ x = 1 ∨ ZMod.χ₈ x = -1 := by decide
  rcases this a with h | h | h <;> simp [h]

/-- $\chi_8$ is primitive: it does not factor through $\mathbb{Z}/4$ ($\chi_8(5) = -1$, $5 \equiv 1 \bmod 4$). -/
lemma chi8C_isPrimitive : chi8C.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hd := chi8C.conductor_dvd_level
  have h8 : chi8C.conductor ∣ 8 := hd
  by_contra hne
  have h4 : chi8C.conductor ∣ 4 := by
    have : chi8C.conductor ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨h8, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]
    · exact absurd h hne
  have hf : chi8C.FactorsThrough 4 := by
    obtain ⟨h, χ₀, hχ₀⟩ := chi8C.factorsThrough_conductor
    refine ⟨by norm_num, DirichletCharacter.changeLevel h4 χ₀, ?_⟩
    rw [← DirichletCharacter.changeLevel_trans χ₀ h4 (by norm_num : 4 ∣ 8)]
    exact hχ₀
  obtain ⟨h, χ₀, hχ₀⟩ := hf
  have h5 := congr_arg (fun χ : DirichletCharacter ℂ 8 => χ (5 : ZMod 8)) hχ₀
  have hu5 : IsUnit (5 : ZMod 8) := by decide
  rw [show (5 : ZMod 8) = ((hu5.unit : (ZMod 8)ˣ) : ZMod 8) from rfl,
    DirichletCharacter.changeLevel_eq_cast_of_dvd] at h5
  have hc : (ZMod.cast ((hu5.unit : (ZMod 8)ˣ) : ZMod 8) : ZMod 4) = 1 := by
    simp only [IsUnit.unit_spec]; decide
  rw [hc, map_one, ← show (5 : ZMod 8) = ((hu5.unit : (ZMod 8)ˣ) : ZMod 8) from rfl, chi8C_apply] at h5
  have : (ZMod.χ₈ 5 : ℂ) = -1 := by norm_num [show ZMod.χ₈ 5 = -1 from rfl]
  rw [this] at h5; norm_num at h5

/-! ### The Gauss sum $g(\chi_8) = 2\sqrt2$ and $L(2, \chi_8) = \pi^2/(8\sqrt2)$ -/

lemma exp_two_pi_I_eighth_add (x : ℝ) (j : ℤ) :
    cexp (2 * π * I * (j * 8 + x) / 8) = cexp (2 * π * I * x / 8) := by
  rw [show 2 * π * I * (j * 8 + x) / 8 = j * (2 * π * I) + 2 * π * I * x / 8 by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- $\sum_{a \bmod 8}\chi_8(a)e(na/8) = 2\cos(2\pi n/8) - 2\cos(2\pi\cdot3n/8)$. -/
lemma sum_chi8_mul_stdAddChar (n : ℤ) :
    ∑ a : ZMod 8, chi8C a * ZMod.stdAddChar ((n : ZMod 8) * a) =
      2 * Complex.cos (2 * π * n / 8) - 2 * Complex.cos (2 * π * (3 * n) / 8) := by
  have he : ∀ k : ℤ, (ZMod.stdAddChar ((n : ZMod 8) * (k : ZMod 8)) : ℂ) = cexp (2 * π * I * (n * k) / 8) := by
    intro k
    rw [show (n : ZMod 8) * (k : ZMod 8) = ((n * k : ℤ) : ZMod 8) by push_cast; ring, ZMod.stdAddChar_coe]
    push_cast; ring_nf
  have hsum : ∑ a : ZMod 8, chi8C a * ZMod.stdAddChar ((n : ZMod 8) * a) =
      ∑ k ∈ Finset.range 8, chi8C ((k : ℤ) : ZMod 8) * ZMod.stdAddChar ((n : ZMod 8) * ((k : ℤ) : ZMod 8)) :=
    (sum_range_zmod (N := 8) (fun a => chi8C a * ZMod.stdAddChar ((n : ZMod 8) * a))).symm
  rw [hsum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, he]
  have hv : ∀ k : ℤ, chi8C (k : ZMod 8) = if k % 2 = 0 then 0 else if k % 8 = 1 ∨ k % 8 = 7 then 1 else -1 :=
    chi8C_intCast
  simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, hv]
  norm_num
  -- pair a = 1 with a = 7 and a = 3 with a = 5
  have h7 : cexp (2 * π * I * (n * 7) / 8) = cexp (-(2 * π * n / 8) * I) := by
    rw [show 2 * π * I * (n * 7) / 8 = (n : ℂ) * (2 * π * I) + -(2 * π * n / 8) * I by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have h5 : cexp (2 * π * I * (n * 5) / 8) = cexp (-(2 * π * (3 * n) / 8) * I) := by
    rw [show 2 * π * I * (n * 5) / 8 = (n : ℂ) * (2 * π * I) + -(2 * π * (3 * n) / 8) * I by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have h1 : cexp (2 * π * I * (n * 1) / 8) = cexp ((2 * π * n / 8) * I) := by congr 1; ring
  have h3 : cexp (2 * π * I * (n * 3) / 8) = cexp ((2 * π * (3 * n) / 8) * I) := by congr 1; ring
  rw [Complex.two_cos, Complex.two_cos, ← h1, ← h7, ← h3, ← h5]
  ring_nf

lemma cos_three_pi_div_four : Real.cos (3 * π / 4) = -(Real.sqrt 2 / 2) := by
  rw [show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]

/-- **$g(\chi_8) = 2\sqrt2$.** -/
lemma gaussSum_chi8 : _root_.gaussSum chi8C ZMod.stdAddChar = 2 * Real.sqrt 2 := by
  have h := sum_chi8_mul_stdAddChar 1
  simp only [Int.cast_one, one_mul, mul_one] at h
  rw [_root_.gaussSum, h]
  have e1 : Complex.cos (2 * π / 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
    rw [show (2 * π / 8 : ℂ) = ((π / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      Real.cos_pi_div_four]
  have e3 : Complex.cos (2 * π * 3 / 8) = ((-(Real.sqrt 2 / 2) : ℝ) : ℂ) := by
    rw [show (2 * π * 3 / 8 : ℂ) = ((3 * π / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
      cos_three_pi_div_four]
  rw [e1, e3]
  push_cast
  ring

lemma gaussSum_chi8_ne_zero : _root_.gaussSum chi8C ZMod.stdAddChar ≠ 0 := by
  rw [gaussSum_chi8]
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')

/-- **$\chi_8$ as a trigonometric polynomial:** $\chi_8(n) = \frac{1}{\sqrt2}\bigl(\cos\frac{2\pi n}{8} - \cos\frac{2\pi\cdot3n}{8}\bigr)$. -/
lemma chi8_eq_cos (n : ℤ) :
    (ZMod.χ₈ n : ℝ) = (Real.cos (2 * π * n / 8) - Real.cos (2 * π * (3 * n) / 8)) / Real.sqrt 2 := by
  have h := sum_chi8_mul_stdAddChar n
  have hprim := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar chi8C_isPrimitive (n : ZMod 8)
  rw [show chi8C⁻¹ = chi8C from chi8C_inv, gaussSum_chi8] at hprim
  have hl : _root_.gaussSum chi8C (ZMod.stdAddChar.mulShift (n : ZMod 8)) =
      ∑ a : ZMod 8, chi8C a * ZMod.stdAddChar ((n : ZMod 8) * a) := by
    simp [_root_.gaussSum, AddChar.mulShift_apply]
  rw [hl, h, chi8C_apply] at hprim
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hc : (((ZMod.χ₈ n : ℝ) * (2 * Real.sqrt 2) : ℝ) : ℂ) =
      (((2 * Real.cos (2 * π * n / 8) - 2 * Real.cos (2 * π * (3 * n) / 8)) : ℝ) : ℂ) := by
    push_cast
    exact hprim.symm
  have hc' := Complex.ofReal_injective hc
  rw [eq_div_iff hs.ne']
  linarith [hc']

lemma bernoulli_two_eval (x : ℝ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)).eval x = x ^ 2 - x + 1 / 6 := by
  simp [Polynomial.bernoulli_def, Finset.sum_range_succ, bernoulli_one, bernoulli_two]
  ring

/-- $\sum_{n \ge 1}\chi_8(n)n^{-2} = \pi^2/(8\sqrt2)$. -/
lemma hasSum_chi8_div_sq :
    HasSum (fun n : ℕ => (ZMod.χ₈ n : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / (8 * Real.sqrt 2)) := by
  have h1 := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero (x := 1 / 8) ⟨by norm_num, by norm_num⟩
  have h3 := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero (x := 3 / 8) ⟨by norm_num, by norm_num⟩
  have h := (h1.sub h3).div_const (Real.sqrt 2)
  rw [bernoulli_two_eval, bernoulli_two_eval] at h
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  convert h using 1
  · ext n
    have := chi8_eq_cos n
    push_cast at this
    rw [this]
    field_simp
  · simp [Nat.factorial]
    field_simp
    ring

/-- $\sum_{d \in \mathbb{Z}}\chi_8(d)\,d^{-2} = 2L(2,\chi_8) = \pi^2/(4\sqrt2)$. -/
lemma tsum_chi8_div_sq :
    ∑' d : ℤ, chi8C⁻¹ (d : ZMod 8) * ((d : ℂ) ^ 2)⁻¹ = (π : ℂ) ^ 2 / (4 * Real.sqrt 2) := by
  rw [chi8C_inv]
  set f : ℤ → ℂ := fun d => chi8C (d : ZMod 8) * ((d : ℂ) ^ 2)⁻¹ with hf
  set a : ℂ := (π : ℂ) ^ 2 / (8 * Real.sqrt 2)
  have hR : HasSum (fun n : ℕ => (((ZMod.χ₈ n : ℝ) / (n : ℝ) ^ 2 : ℝ) : ℂ)) a := by
    have := Complex.hasSum_ofReal.mpr hasSum_chi8_div_sq
    convert this using 1
    simp [a]
  have hN : HasSum (fun n : ℕ => f n) a := by
    refine hR.congr_fun fun n => ?_
    simp [hf, chi8C_apply, div_eq_mul_inv]
  have h0 : f 0 = 0 := by simp [hf]
  have hshift : HasSum (fun n : ℕ => f ((n + 1 : ℕ) : ℤ)) a := by
    have := (hasSum_nat_add_iff' 1).mpr hN
    simp only [Finset.sum_range_one, Nat.cast_zero, h0, sub_zero] at this
    exact this
  have hneg : HasSum (fun n : ℕ => f (-((n : ℤ) + 1))) a := by
    refine hshift.congr_fun fun n => ?_
    simp only [hf]
    have hm : chi8C (Int.cast (-((n : ℤ) + 1)) : ZMod 8) = chi8C (((n + 1 : ℕ) : ℤ) : ZMod 8) := by
      rw [show (Int.cast (-((n : ℤ) + 1)) : ZMod 8) = (-1) * (((n + 1 : ℕ) : ℤ) : ZMod 8) by
        push_cast; ring, map_mul, chi8C_neg_one, one_mul]
    rw [hm]
    push_cast
    ring
  rw [(hN.of_nat_of_neg_add_one hneg).tsum_eq]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  simp only [a]
  field_simp
  ring

/-! ### The two Eisenstein series and $E_Q$ -/

lemma one_char_apply (a : ZMod 1) : (1 : DirichletCharacter ℂ 1) a = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton a)

lemma one_char_isPrimitive : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  exact Nat.dvd_one.mp (DirichletCharacter.conductor_dvd_level _)

lemma gaussSum_one_char : _root_.gaussSum (1 : DirichletCharacter ℂ 1)⁻¹ ZMod.stdAddChar = 1 := by
  simp only [_root_.gaussSum, Fintype.sum_unique, one_char_apply, inv_one,
    one_mul]
  exact (congr_arg _ (Subsingleton.elim _ _)).trans (AddChar.map_zero_eq_one _)

/-- $E^{1,\chi_8}$ ($u = 1$, $v = 8$, $t = 1$) on $\Gamma_1(8)$. -/
noncomputable def eis1chi8 : ModularForm (CongruenceSubgroup.Gamma1 8) 2 :=
  dsEisMF (N := 8) (1 : DirichletCharacter ℂ 1) chi8C 1 (by norm_num) (Or.inr chi8C_ne_one)

/-- $E^{\chi_8,1}$ ($u = 8$, $v = 1$, $t = 1$) on $\Gamma_1(8)$. -/
noncomputable def eischi81 : ModularForm (CongruenceSubgroup.Gamma1 8) 2 :=
  dsEisMF (N := 8) chi8C (1 : DirichletCharacter ℂ 1) 1 (by norm_num) (Or.inl chi8C_ne_one)

/-- **The Eisenstein series of $x^2+y^2+z^2+2w^2$:** $E_Q = \frac{4\sqrt2}{\pi^2}E^{1,\chi_8} - \frac1{\pi^2}E^{\chi_8,1}$. -/
@[kb "diamondshurman2005" "§4.6 (M_2(Γ₀(8), χ₈) Eisenstein space) [unverified]"]
noncomputable def eisQ1112 : ModularForm (CongruenceSubgroup.Gamma1 8) 2 :=
  (4 * (Real.sqrt 2 : ℂ) / (π : ℂ) ^ 2) • eis1chi8 + (-(1 / (π : ℂ) ^ 2)) • eischi81

lemma eisQ1112_apply (z : ℍ) :
    eisQ1112 z = 4 * (Real.sqrt 2 : ℂ) / (π : ℂ) ^ 2 * eis1chi8 z - 1 / (π : ℂ) ^ 2 * eischi81 z := by
  simp [eisQ1112, sub_eq_add_neg]

/-- **The $q$-expansion of $E_Q$** ($Q = x^2+y^2+z^2+2w^2$):
$E_Q = 1 - 2\sum_{e\ge1}\sigma_1^{1,\chi_8}(e)q^e + 8\sum_{e\ge1}\sigma_1^{\chi_8,1}(e)q^e$, i.e. the coefficient of $q^e$ is
$-2\sum_{d\mid e}\chi_8(d)d + 8\sum_{d\mid e}\chi_8(e/d)d$. -/
theorem eisQ1112_eq_qExpansion (z : ℍ) :
    eisQ1112 z = 1 -
      2 * ∑' e : ℕ+, sigmaTw (fun n => (1 : DirichletCharacter ℂ 1) n) (fun n => chi8C n) e *
        cexp (2 * π * I * z) ^ (e : ℕ) +
      8 * ∑' e : ℕ+, sigmaTw (fun n => chi8C n) (fun n => (1 : DirichletCharacter ℂ 1) n) e *
        cexp (2 * π * I * z) ^ (e : ℕ) := by
  have h1 := dsEisMF_eq_qExpansion (N := 8) (v := 8) (ψ := (1 : DirichletCharacter ℂ 1)) (φ := chi8C)
    chi8C_isPrimitive (by rw [one_char_apply, chi8C_neg_one, one_mul]) (t := 1) one_ne_zero
    (by norm_num) (Or.inr chi8C_ne_one) z
  have h2 := dsEisMF_eq_qExpansion (N := 8) (v := 1) (ψ := chi8C) (φ := (1 : DirichletCharacter ℂ 1))
    one_char_isPrimitive (by rw [one_char_apply, chi8C_neg_one, one_mul]) (t := 1) one_ne_zero
    (by norm_num) (Or.inl chi8C_ne_one) z
  rw [eisQ1112_apply, eis1chi8, eischi81, h1, h2, one_char_apply, tsum_chi8_div_sq, chi8C_inv,
    gaussSum_chi8, gaussSum_one_char]
  have h0 : chi8C 0 = 0 := by
    have : ZMod.χ₈ 0 = 0 := by decide
    rw [chi8C_apply, this]; simp
  rw [h0]
  simp only [pow_one, zero_mul, zero_add, Nat.cast_one, one_pow, div_one, mul_one]
  set S1 := ∑' e : ℕ+, sigmaTw (fun n => (1 : DirichletCharacter ℂ 1) n) (fun n => chi8C n) e *
    cexp (2 * π * I * z) ^ (e : ℕ)
  set S2 := ∑' e : ℕ+, sigmaTw (fun n => chi8C n) (fun n => (1 : DirichletCharacter ℂ 1) n) e *
    cexp (2 * π * I * z) ^ (e : ℕ)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  field_simp
  ring_nf
  rw [I_sq, hs]
  ring

/-! ### The cusps of $\Gamma_0(8)$ -/

/-- $\delta_g = \begin{pmatrix}1&0\\g&1\end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z})$. -/
def deltaG (g : ℤ) : SL(2, ℤ) := ⟨!![1, 0; g, 1], by simp [Matrix.det_fin_two]⟩

lemma deltaG_mul (g h : ℤ) : deltaG g * deltaG h = deltaG (g + h) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [deltaG, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma deltaG_zero : deltaG 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [deltaG]

/-- Every $\gamma$ with $\gamma_{10}$ a unit mod $N$ is $\gamma_0 S T^k$ with $\gamma_0 \in \Gamma_0(N)$. -/
lemma exists_gamma0_mul_S_mul_T_of_isUnit {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (hc : IsUnit ((γ 1 0 : ℤ) : ZMod N)) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ ∃ k : ℤ,
      γ = γ₀ * ModularGroup.S * ModularGroup.T ^ k := by
  set u := hc.unit
  set k : ℤ := ((((γ 1 1 : ℤ) : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)).val : ℤ) with hkdef
  have hkx : ((k : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    rw [hkdef, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((γ 1 0 : ℤ) : ZMod N) = 1 := by
    rw [show ((γ 1 0 : ℤ) : ZMod N) = (u : ZMod N) from (IsUnit.unit_spec hc).symm]; simp
  have hk : (((γ 1 1 - k * γ 1 0 : ℤ)) : ZMod N) = 0 := by
    push_cast
    rw [hkx, mul_assoc, hu, mul_one, sub_self]
  have hSS : (ModularGroup.S * ModularGroup.S : SL(2, ℤ)) = -1 := by
    ext i j
    have := congr_fun (congr_fun ModularGroup.S_mul_S_eq i) j
    simpa using this
  refine ⟨-(γ * ModularGroup.T ^ (-k) * ModularGroup.S), ?_, k, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, ModularGroup.coe_S]
    simp only [Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp
    rw [← neg_eq_zero, ← hk]
    push_cast
    ring
  · have e : -(γ * ModularGroup.T ^ (-k) * ModularGroup.S) * ModularGroup.S * ModularGroup.T ^ k =
        -(γ * ModularGroup.T ^ (-k) * (ModularGroup.S * ModularGroup.S) * ModularGroup.T ^ k) := by
      simp only [neg_mul, mul_assoc]
    rw [e, hSS, mul_neg, mul_one, neg_mul, neg_neg]
    group

lemma isUnit_zmod_eight_of_odd {c : ℤ} (hc : c % 2 = 1) : IsUnit ((c : ZMod 8)) := by
  have h : (c : ZMod 8) = ((c % 8 : ℤ) : ZMod 8) := (ZMod.intCast_mod c 8).symm
  have h8 : c % 8 = 1 ∨ c % 8 = 3 ∨ c % 8 = 5 ∨ c % 8 = 7 := by omega
  rw [h]
  rcases h8 with h8 | h8 | h8 | h8 <;> rw [h8] <;> decide

/-- **Cusp representatives for $\Gamma_0(8)$:** every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ is $\gamma_0\delta T^k$ with
$\gamma_0 \in \Gamma_0(8)$, $k \in \mathbb{Z}$ and $\delta \in \{1, S, \delta_2, \delta_4\}$ (cusps $\infty$, $0$, $\tfrac12$, $\tfrac14$). -/
lemma exists_gamma0_eight (γ : SL(2, ℤ)) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 8 ∧ ∃ k : ℤ,
      γ = γ₀ * ModularGroup.T ^ k ∨ γ = γ₀ * ModularGroup.S * ModularGroup.T ^ k ∨
      γ = γ₀ * deltaG 2 * ModularGroup.T ^ k ∨ γ = γ₀ * deltaG 4 * ModularGroup.T ^ k := by
  have hdet := det_SL γ
  set c := γ 1 0 with hcdef
  set d := γ 1 1 with hddef
  rcases Int.emod_two_eq_zero_or_one c with hc2 | hc2
  · -- c even, so d odd
    have hd2 : d % 2 = 1 := by
      by_contra h
      have hd0 : d % 2 = 0 := by omega
      obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
      obtain ⟨d', hd'⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
      have : 2 * (γ 0 0 * d' - γ 0 1 * c') = 1 := by
        rw [hc', hd'] at hdet; linear_combination hdet
      omega
    obtain ⟨m, hm⟩ : ∃ m, d = 2 * m + 1 := ⟨d / 2, by omega⟩
    have hmem : ∀ γ₀ : SL(2, ℤ), (8 : ℤ) ∣ γ₀ 1 0 → γ₀ ∈ CongruenceSubgroup.Gamma0 8 := fun γ₀ h => by
      rw [CongruenceSubgroup.Gamma0_mem]; exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h
    rcases (show c % 8 = 0 ∨ c % 8 = 4 ∨ c % 4 = 2 by omega) with h8 | h8 | h4
    · exact ⟨γ, hmem γ (by omega), 0, Or.inl (by simp)⟩
    · -- c ≡ 4 mod 8: δ₄, k = 0
      obtain ⟨s, hs⟩ : ∃ s, c = 8 * s + 4 := ⟨c / 8, by omega⟩
      refine ⟨γ * deltaG (-4), hmem _ ?_, 0, Or.inr (Or.inr (Or.inr ?_))⟩
      · rw [Matrix.SpecialLinearGroup.coe_mul]
        simp only [deltaG, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        rw [← hcdef, ← hddef, hs, hm]
        exact ⟨s - m, by ring⟩
      · simp only [zpow_zero, mul_one]
        rw [mul_assoc, deltaG_mul, show (-4 : ℤ) + 4 = 0 by norm_num, deltaG_zero, mul_one]
    · -- c ≡ 2 mod 4: δ₂, k = m - s
      obtain ⟨s, hs⟩ : ∃ s, c = 4 * s + 2 := ⟨c / 4, by omega⟩
      refine ⟨γ * ModularGroup.T ^ (-(m - s)) * deltaG (-2), hmem _ ?_, m - s,
        Or.inr (Or.inr (Or.inl ?_))⟩
      · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          ModularGroup.coe_T_zpow]
        simp only [deltaG, Matrix.mul_apply, Fin.sum_univ_two]
        simp
        rw [← hcdef, ← hddef, hs, hm]
        exact ⟨s * (m - s), by ring⟩
      · rw [mul_assoc (γ * _), deltaG_mul, show (-2 : ℤ) + 2 = 0 by norm_num, deltaG_zero, mul_one]
        group
  · obtain ⟨γ₀, h₀, k, hk⟩ := exists_gamma0_mul_S_mul_T_of_isUnit (N := 8) γ
      (isUnit_zmod_eight_of_odd hc2)
    exact ⟨γ₀, h₀, k, Or.inr (Or.inl hk)⟩

/-- **Vanishing at all cusps of $\Gamma_0(8)$ from four cusps:** if $f\,|_2\,\gamma_0 = c(\gamma_0)f$ on $\Gamma_0(8)$ and
$f$, $f|S$, $f|\delta_2$, $f|\delta_4$ tend to $0$ at $i\infty$, then $f|\gamma \to 0$ for every $\gamma$. -/
theorem isZeroAtImInfty_slash_of_gamma0_eight {f : ℍ → ℂ} (cf : SL(2, ℤ) → ℂ)
    (hf : ∀ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 8 → f ∣[(2 : ℤ)] γ₀ = cf γ₀ • f)
    (h1 : Tendsto f UpperHalfPlane.atImInfty (𝓝 0))
    (hS : Tendsto (f ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty (𝓝 0))
    (h2 : Tendsto (f ∣[(2 : ℤ)] deltaG 2) UpperHalfPlane.atImInfty (𝓝 0))
    (h4 : Tendsto (f ∣[(2 : ℤ)] deltaG 4) UpperHalfPlane.atImInfty (𝓝 0)) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty (f ∣[(2 : ℤ)] γ) := by
  obtain ⟨γ₀, hγ₀, k, hk⟩ := exists_gamma0_eight γ
  have key : ∀ δ : SL(2, ℤ), Tendsto (f ∣[(2 : ℤ)] δ) UpperHalfPlane.atImInfty (𝓝 0) →
      Tendsto (f ∣[(2 : ℤ)] (γ₀ * δ * ModularGroup.T ^ k)) UpperHalfPlane.atImInfty (𝓝 0) := by
    intro δ hδ
    rw [SlashAction.slash_mul, SlashAction.slash_mul, hf γ₀ hγ₀, ModularForm.SL_smul_slash,
      ModularForm.SL_smul_slash]
    have := (tendsto_slash_T_zpow hδ k).const_mul (cf γ₀)
    rw [mul_zero] at this
    exact this
  rcases hk with rfl | rfl | rfl | rfl
  · have := key 1 (by simpa using h1)
    rw [mul_one] at this
    exact this
  · exact key _ hS
  · exact key _ h2
  · exact key _ h4

/-! ### $\Theta_Q$ for $Q = x^2+y^2+z^2+2w^2$ -/

theorem q1112_eval (x : Fin 4 → ℤ) : q1112.eval x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + 2 * x 3 ^ 2 := by
  simp [QuadForm.evalIn, q1112, QuadForm.diag, Fin.sum_univ_four, Matrix.diagonal]
  ring

theorem q1112_posDef : IntQF.PosDef q1112 := by
  intro x hx
  rw [q1112_eval]
  by_contra hle
  rw [not_lt] at hle
  have h0 := sq_nonneg (x 0); have h1 := sq_nonneg (x 1)
  have h2 := sq_nonneg (x 2); have h3 := sq_nonneg (x 3)
  have e0 : x 0 ^ 2 = 0 := by linarith
  have e1 : x 1 ^ 2 = 0 := by linarith
  have e2 : x 2 ^ 2 = 0 := by linarith
  have e3 : x 3 ^ 2 = 0 := by linarith
  simp only [pow_eq_zero_iff two_ne_zero] at e0 e1 e2 e3
  apply hx
  ext i; fin_cases i <;> simp [e0, e1, e2, e3]

lemma isThetaLevel_q1112 : IsThetaLevel q1112 8 := level_q1112 ▸ isThetaLevel_level q1112_posDef

lemma thetaChi_q1112 (d : ℤ) (hd : IsCoprime d (8 : ℕ)) :
    (thetaChi q1112 2 8 d : ℂ) = chi8C (d : ZMod 8) := by
  obtain ⟨ho, hmod, _⟩ := oddRep_spec (by norm_num : 0 < 8) hd
  rw [thetaChi_eq_chi q1112_posDef rfl (by norm_num) isThetaLevel_q1112 hd ho hmod, chi_q1112 ho,
    chi8C_apply]
  congr 2
  have : ((oddRep 8 d : ℤ) : ZMod 8) = (d : ZMod 8) := (ZMod.intCast_eq_intCast_iff' _ _ _).mpr hmod
  simpa using this

lemma thetaH_q1112_slash {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 8) :
    thetaH q1112 ∣[(2 : ℤ)] γ = chi8C ((γ 1 1 : ℤ) : ZMod 8) • thetaH q1112 := by
  have h := thetaH_slash_gamma0 q1112_posDef (k := 2) rfl (by norm_num) isThetaLevel_q1112 hγ
  rw [thetaChi_q1112 _ (isCoprime_of_gamma0 (dvd_gamma10_of_mem hγ))] at h
  exact h

lemma gramMatrix_q1112_symm : Matrix.transpose (gramMatrix q1112) = gramMatrix q1112 := by
  have := gramMatrix_isHermitian q1112
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma det_gramMatrix_q1112 : (gramMatrix q1112).det = 2 := by
  rw [det_gramMatrix, det_hessian_q1112]; norm_num

/-- A Gauss sum vanishes if a shift multiplies every term by $-1$. -/
lemma gaussSum_q1112_eq_zero {c : ℕ} [NeZero c] (t : Fin 4 → ℤ)
    (ht : ∀ x : Fin 4 → ℤ, gsTerm (gramMatrix q1112) 1 c 0 (x + t) = -gsTerm (gramMatrix q1112) 1 c 0 x) :
    gaussSum (gramMatrix q1112) 1 c 0 = 0 := by
  have h := gaussSum_shift gramMatrix_q1112_symm (quadAt_gramMatrix_int q1112) 1 c 0 t
  simp_rw [ht] at h
  rw [Finset.sum_neg_distrib, ← gaussSum_eq_sum_gsTerm] at h
  linear_combination -h / 2

lemma gsTerm_q1112 (c : ℕ) (x : Fin 4 → ℤ) :
    gsTerm (gramMatrix q1112) 1 c 0 x = cexp (2 * π * I * ((q1112.eval x : ℤ) : ℂ) / c) := by
  simp only [gsTerm, quadAt_gramMatrix, Int.cast_one, one_mul, Pi.zero_apply, Int.cast_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  congr 1
  push_cast
  ring

lemma gaussSum_q1112_two : gaussSum (gramMatrix q1112) 1 2 0 = 0 := by
  refine gaussSum_q1112_eq_zero (c := 2) (Pi.single 0 1) fun x => ?_
  rw [gsTerm_q1112, gsTerm_q1112, q1112_eval, q1112_eval]
  simp only [Pi.add_apply, Pi.single_apply]
  simp
  rw [show 2 * π * I * (((x 0 : ℂ) + 1) ^ 2 + (x 1 : ℂ) ^ 2 + (x 2 : ℂ) ^ 2 + 2 * (x 3 : ℂ) ^ 2) / 2 =
      2 * π * I * ((x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2 + (x 2 : ℂ) ^ 2 + 2 * (x 3 : ℂ) ^ 2) / 2 +
        (x 0 : ℂ) * (2 * π * I) + π * I by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

lemma gaussSum_q1112_four : gaussSum (gramMatrix q1112) 1 4 0 = 0 := by
  refine gaussSum_q1112_eq_zero (c := 4) (Pi.single 3 1) fun x => ?_
  rw [gsTerm_q1112, gsTerm_q1112, q1112_eval, q1112_eval]
  simp only [Pi.add_apply, Pi.single_apply]
  simp
  rw [show 2 * π * I * ((x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2 + (x 2 : ℂ) ^ 2 + 2 * ((x 3 : ℂ) + 1) ^ 2) / 4 =
      2 * π * I * ((x 0 : ℂ) ^ 2 + (x 1 : ℂ) ^ 2 + (x 2 : ℂ) ^ 2 + 2 * (x 3 : ℂ) ^ 2) / 4 +
        (x 3 : ℂ) * (2 * π * I) + π * I by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  ring

lemma thetaMult_q1112_zero_one : thetaMult (gramMatrix q1112) 2 0 1 = -1 / (4 * Real.sqrt 2) := by
  have hG : gaussSum (gramMatrix q1112) 0 1 0 = 1 := by simp [gaussSum]
  rw [thetaMult, det_gramMatrix_q1112, hG]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring_nf
  rw [I_sq]; ring

lemma tendsto_thetaH_q1112_S :
    Tendsto (thetaH q1112 ∣[(2 : ℤ)] ModularGroup.S) UpperHalfPlane.atImInfty
      (𝓝 (-1 / (4 * Real.sqrt 2))) := by
  have h := tendsto_theta_cusp q1112_posDef (k := 2) rfl (a := 0) (b := -1) (d := 0) (c := 1)
    (by norm_num)
  rw [thetaMult_q1112_zero_one] at h
  refine h.congr fun τ => ?_
  rw [SlashInvariantForm.slash_S_apply]
  simp only [thetaH]
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  push_cast
  rw [zpow_neg, zpow_two, ← sq]
  congr 2
  · simp only [add_zero, zero_mul, zero_add]
    field_simp
  · ring

lemma tendsto_thetaH_q1112_deltaG {g : ℕ} [NeZero g]
    (hG : gaussSum (gramMatrix q1112) 1 g 0 = 0) :
    Tendsto (thetaH q1112 ∣[(2 : ℤ)] deltaG g) UpperHalfPlane.atImInfty (𝓝 0) := by
  have h := tendsto_theta_cusp q1112_posDef (k := 2) rfl (a := 1) (b := 0) (d := 1) (c := g)
    (by ring)
  rw [thetaMult, hG, mul_zero] at h
  refine h.congr fun τ => ?_
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply]
  simp only [thetaH]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [deltaG, zpow_neg]

/-! ### Constant terms of $E_Q$ -/

lemma chi8C_zero : chi8C 0 = 0 := by
  have : ZMod.χ₈ 0 = 0 := by decide
  rw [chi8C_apply, this]; simp

lemma chi8C_even {n : ℤ} (h : n % 2 = 0) : chi8C (n : ZMod 8) = 0 := by
  rw [chi8C_intCast]; simp [h]

lemma chi8C_neg (n : ℤ) : chi8C ((-n : ℤ) : ZMod 8) = chi8C (n : ZMod 8) := by
  rw [Int.cast_neg, neg_eq_neg_one_mul, map_mul, chi8C_neg_one, one_mul]

lemma tsum_chi8C_div_sq : ∑' n : ℤ, chi8C (n : ZMod 8) * ((n : ℂ) ^ 2)⁻¹ = (π : ℂ) ^ 2 / (4 * Real.sqrt 2) := by
  have := tsum_chi8_div_sq; rwa [chi8C_inv] at this

lemma eis1chi8_slash_apply (γ : SL(2, ℤ)) :
    Tendsto ((⇑eis1chi8 : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : ℤ, dsF (1 : DirichletCharacter ℂ 1) chi8C 8 (-(n * γ 1 0)) (n * γ 0 0) *
        ((n : ℂ) ^ 2)⁻¹)) :=
  tendsto_dsEisMF_cusp (N := 8) _ _ γ

lemma eischi81_slash_apply (γ : SL(2, ℤ)) :
    Tendsto ((⇑eischi81 : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (∑' n : ℤ, dsF chi8C (1 : DirichletCharacter ℂ 1) 1 (-(n * γ 1 0)) (n * γ 0 0) *
        ((n : ℂ) ^ 2)⁻¹)) :=
  tendsto_dsEisMF_cusp (N := 8) _ _ γ

lemma dsF_one_chi8 (c d : ℤ) :
    dsF (1 : DirichletCharacter ℂ 1) chi8C 8 c d = (if (8 : ℤ) ∣ c then 1 else 0) * chi8C d := by
  simp only [dsF, chi8C_inv, one_char_apply]
  push_cast
  rfl

lemma dsF_chi8_one (c d : ℤ) :
    dsF chi8C (1 : DirichletCharacter ℂ 1) 1 c d = chi8C c := by
  simp [dsF, one_char_apply]

lemma slash_eisQ1112 (γ : SL(2, ℤ)) :
    (⇑eisQ1112 : ℍ → ℂ) ∣[(2 : ℤ)] γ = fun τ => 4 * (Real.sqrt 2 : ℂ) / (π : ℂ) ^ 2 *
      ((⇑eis1chi8 : ℍ → ℂ) ∣[(2 : ℤ)] γ) τ - 1 / (π : ℂ) ^ 2 * ((⇑eischi81 : ℍ → ℂ) ∣[(2 : ℤ)] γ) τ := by
  ext τ
  simp only [ModularForm.SL_slash_apply, eisQ1112_apply]
  ring

lemma tendsto_eisQ1112_slash {γ : SL(2, ℤ)} {L₁ L₂ : ℂ}
    (h₁ : ∑' n : ℤ, dsF (1 : DirichletCharacter ℂ 1) chi8C 8 (-(n * γ 1 0)) (n * γ 0 0) *
      ((n : ℂ) ^ 2)⁻¹ = L₁)
    (h₂ : ∑' n : ℤ, dsF chi8C (1 : DirichletCharacter ℂ 1) 1 (-(n * γ 1 0)) (n * γ 0 0) *
      ((n : ℂ) ^ 2)⁻¹ = L₂) :
    Tendsto ((⇑eisQ1112 : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (4 * (Real.sqrt 2 : ℂ) / (π : ℂ) ^ 2 * L₁ - 1 / (π : ℂ) ^ 2 * L₂)) := by
  rw [slash_eisQ1112, ← h₁, ← h₂]
  exact ((eis1chi8_slash_apply γ).const_mul _).sub ((eischi81_slash_apply γ).const_mul _)

lemma tsum_zero_of_forall {f : ℤ → ℂ} (h : ∀ n, f n = 0) : ∑' n, f n = 0 := by
  simp [h]

/-- **$\Theta_Q - E_Q$ vanishes at every cusp** ($Q = x^2+y^2+z^2+2w^2$). -/
theorem isZeroAtImInfty_theta_sub_eisQ1112 (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty ((thetaH q1112 - ⇑eisQ1112) ∣[(2 : ℤ)] γ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  have hsub : ∀ δ : SL(2, ℤ), (thetaH q1112 - ⇑eisQ1112) ∣[(2 : ℤ)] δ =
      thetaH q1112 ∣[(2 : ℤ)] δ - (⇑eisQ1112 : ℍ → ℂ) ∣[(2 : ℤ)] δ := fun δ => by
    rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
  refine isZeroAtImInfty_slash_of_gamma0_eight (fun γ₀ => chi8C ((γ₀ 1 1 : ℤ) : ZMod 8)) ?_ ?_ ?_ ?_ ?_ γ
  · intro γ₀ hγ₀
    have hcop := isCoprime_of_gamma0 (dvd_gamma10_of_mem hγ₀)
    have hE1 := isModularFormWithChar_dsEisMF (N := 8) (ψ := (1 : DirichletCharacter ℂ 1))
      (φ := chi8C) (t := 1) (by norm_num) (Or.inr chi8C_ne_one) γ₀ hγ₀
    have hE2 := isModularFormWithChar_dsEisMF (N := 8) (ψ := chi8C)
      (φ := (1 : DirichletCharacter ℂ 1)) (t := 1) (by norm_num) (Or.inl chi8C_ne_one) γ₀ hγ₀
    simp only [dsChar_intCast _ _ hcop, one_char_apply, one_mul, mul_one] at hE1 hE2
    rw [hsub, thetaH_q1112_slash hγ₀, slash_eisQ1112]
    change _ - (fun τ => _ * ((⇑eis1chi8 : ℍ → ℂ) ∣[(2 : ℤ)] γ₀) τ -
      _ * ((⇑eischi81 : ℍ → ℂ) ∣[(2 : ℤ)] γ₀) τ) = _
    rw [show (⇑eis1chi8 : ℍ → ℂ) ∣[(2 : ℤ)] γ₀ = _ from hE1,
      show (⇑eischi81 : ℍ → ℂ) ∣[(2 : ℤ)] γ₀ = _ from hE2]
    ext τ
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eisQ1112_apply, eis1chi8, eischi81]
    ring
  · -- at ∞
    have hθ := tendsto_theta_atImInfty q1112_posDef
    have hE : Tendsto (⇑eisQ1112 : ℍ → ℂ) UpperHalfPlane.atImInfty (𝓝 1) := by
      have := tendsto_eisQ1112_slash (γ := 1) (L₁ := (π : ℂ) ^ 2 / (4 * Real.sqrt 2)) (L₂ := 0) ?_ ?_
      · rw [SlashAction.slash_one] at this
        convert this using 2
        field_simp; ring
      · simp only [dsF_one_chi8, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne one_ne_zero,
          Matrix.one_apply_eq, mul_zero, neg_zero, dvd_zero, ↓reduceIte, one_mul, mul_one]
        exact tsum_chi8C_div_sq
      · refine tsum_zero_of_forall fun n => ?_
        simp [dsF_chi8_one, chi8C_zero]
    have := hθ.sub hE
    rw [sub_self] at this
    exact this
  · -- at 0 (S)
    have hE := tendsto_eisQ1112_slash (γ := ModularGroup.S) (L₁ := 0)
      (L₂ := (π : ℂ) ^ 2 / (4 * Real.sqrt 2)) ?_ ?_
    · rw [hsub]
      have := tendsto_thetaH_q1112_S.sub hE
      convert this using 2
      field_simp
      ring
    · refine tsum_zero_of_forall fun n => ?_
      simp [dsF_one_chi8, ModularGroup.S, chi8C_zero]
    · simp only [dsF_chi8_one, ModularGroup.coe_S]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, chi8C_neg]
      exact tsum_chi8C_div_sq
  · -- at 1/2
    have hE := tendsto_eisQ1112_slash (γ := deltaG 2) (L₁ := 0) (L₂ := 0) ?_ ?_
    · rw [hsub]
      have := (tendsto_thetaH_q1112_deltaG (g := 2) gaussSum_q1112_two).sub hE
      convert this using 2
      ring
    · refine tsum_zero_of_forall fun n => ?_
      simp only [dsF_one_chi8, deltaG]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mul_one]
      split_ifs with h
      · rw [chi8C_even (by omega)]; simp
      · simp
    · refine tsum_zero_of_forall fun n => ?_
      simp only [dsF_chi8_one, deltaG]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [chi8C_even (by omega)]; simp
  · -- at 1/4
    have hE := tendsto_eisQ1112_slash (γ := deltaG 4) (L₁ := 0) (L₂ := 0) ?_ ?_
    · rw [hsub]
      have := (tendsto_thetaH_q1112_deltaG (g := 4) gaussSum_q1112_four).sub hE
      convert this using 2
      ring
    · refine tsum_zero_of_forall fun n => ?_
      simp only [dsF_one_chi8, deltaG]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, mul_one]
      split_ifs with h
      · rw [chi8C_even (by omega)]; simp
      · simp
    · refine tsum_zero_of_forall fun n => ?_
      simp only [dsF_chi8_one, deltaG]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      rw [chi8C_even (by omega)]; simp

/-! ### $\Theta_{\mathrm{Gen}(Q)} - E_Q$ is cuspidal -/

/-- **From $\Theta_Q$ to $\Theta_{\mathrm{Gen}(Q)}$:** if $\Theta_Q - E$ vanishes at every cusp, so does
$\Theta_{\mathrm{Gen}(Q)} - E$ (because $\Theta_Q - \Theta_{\mathrm{Gen}(Q)}$ does, `isZeroAtImInfty_theta_sub_slash`). -/
theorem isZeroAtImInfty_thetaGen_sub_of {n : ℕ} {Q : IntQF n} (hQ : Q.PosDef) {k : ℕ} (hn : n = 2 * k)
    {E : ℍ → ℂ} (h : ∀ γ : SL(2, ℤ), UpperHalfPlane.IsZeroAtImInfty ((thetaH Q - E) ∣[(k : ℤ)] γ))
    (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty ((fun τ : ℍ => thetaGen Q τ - E τ) ∣[(k : ℤ)] γ) := by
  have hF := genusFinite hQ
  have hsplit : (fun τ : ℍ => thetaGen Q τ - E τ) =
      (thetaH Q - E) - fun τ : ℍ => ((mass Q : ℂ))⁻¹ *
        ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ * (thetaH Q - thetaH c.out) τ := by
    ext τ
    simp only [Pi.sub_apply, thetaH]
    rw [← theta_sub_thetaGen hQ hF]
    ring
  rw [hsplit, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]
  have h1 := h γ
  suffices h2 : UpperHalfPlane.IsZeroAtImInfty ((fun τ : ℍ => ((mass Q : ℂ))⁻¹ *
      ∑ c ∈ hF.finite_classes.toFinset, ((c.autCard : ℂ))⁻¹ * (thetaH Q - thetaH c.out) τ) ∣[(k : ℤ)] γ) by
    have := Filter.Tendsto.sub h1 h2
    rw [sub_zero] at this
    exact this
  have hlin : (fun τ : ℍ => ((mass Q : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
      ((c.autCard : ℂ))⁻¹ * (thetaH Q - thetaH c.out) τ) ∣[(k : ℤ)] γ =
      fun τ => ((mass Q : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
        ((c.autCard : ℂ))⁻¹ * ((thetaH Q - thetaH c.out) ∣[(k : ℤ)] γ) τ := by
    ext τ
    simp only [ModularForm.SL_slash_apply, Finset.sum_mul, mul_assoc]
  rw [hlin]
  have : Tendsto (fun τ : ℍ => ((mass Q : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
      ((c.autCard : ℂ))⁻¹ * ((thetaH Q - thetaH c.out) ∣[(k : ℤ)] γ) τ)
      UpperHalfPlane.atImInfty (𝓝 (((mass Q : ℂ))⁻¹ * ∑ c ∈ hF.finite_classes.toFinset,
        ((c.autCard : ℂ))⁻¹ * 0)) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun c hc => tendsto_const_nhds.mul ?_)
    exact isZeroAtImInfty_theta_sub_slash hQ
      (sameGenus_out_of_mem ((Set.Finite.mem_toFinset _).mp hc)) hn γ
  simp only [mul_zero, Finset.sum_const_zero] at this
  exact this

/-- **$\Theta_{\mathrm{Gen}(Q)} - E_Q$ is cuspidal** for $Q = x^2+y^2+z^2+2w^2$: it vanishes at every cusp. -/
@[kb "hanke2004" "(4.3)–(4.5), p. 365 (Θ_Gen − E cuspidal), example x²+y²+z²+2w² [unverified]"]
theorem isZeroAtImInfty_thetaGen_sub_eisQ1112 (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsZeroAtImInfty
      ((fun τ : ℍ => thetaGen q1112 τ - eisQ1112 τ) ∣[(2 : ℤ)] γ) :=
  isZeroAtImInfty_thetaGen_sub_of q1112_posDef (k := 2) rfl isZeroAtImInfty_theta_sub_eisQ1112 γ

end QuadFormsKB.Siegel.EisensteinWt2
