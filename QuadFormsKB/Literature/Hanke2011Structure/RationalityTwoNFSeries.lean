/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoNFBeta
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoSeries
import QuadFormsKB.Tamagawa.Odd7Units
import QuadFormsKB.Literature.Hanke2005.Lemma22

/-!
# Paper 6, Theorem 5.4 and Corollary 5.5 at $F_{\mathfrak p} = \mathbb Q_2$ of a number field

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4 and Cor. 5.5, p. 23-24.

Let $F$ be a number field and $\mathfrak p$ a finite prime of $F$ with $N\mathfrak p = 2$ and $2 \notin \mathfrak p^2$
(equivalently $F_{\mathfrak p} \cong \mathbb Q_2$; `IsQ2Prime`).  For the true local genera $G_{\mathfrak p}$
(`LocGenus v n`), every rank $n$, every unit $w \in \mathcal O_{\mathfrak p}^\times$ and every reference genus $G_0$, the
fixed-unit series $\sum_\nu A^*_{\mathfrak p;n}([2^\nu w])X^\nu$ and $\sum_\nu B^*_{\mathfrak p;n}([2^\nu w])X^\nu$ are rational
functions of $X = 2^{-s}$ (`theorem_5_4_two_nf_A`, `theorem_5_4_two_nf_B`), and so are the Euler factors of
the distinguished family $\lambda(2^i) = 2^i$ (`cor_5_5_two_nf_A`, `cor_5_5_two_nf_B`).

*Proof (transport from $\mathbb Q$).*  Fix a ring isomorphism $\sigma : \mathfrak o_{\mathfrak p} \cong \mathfrak o_{\mathfrak p_2}$ with the
completion of $\mathbb Z$ at $2$ (`IsQ2Prime.equiv`).  It carries local genera, Hessian determinant squareclasses,
Hasse invariants and the densities $\beta$ of one side to the other (`RationalityTwoNFTransport.lean`,
`RationalityTwoNFBeta.lean`), so the normalized mass sums are $\beta(G_0)/\beta(G_1)$ times those over $\mathbb Q$ for a
fixed reference genus $G_1$, and the rationality over $\mathbb Q$ (`RatTwo.theorem_5_4_two_A_rank`) applies.

*Uniformizer.*  Since $N\mathfrak p = 2$ and $2 \notin \mathfrak p^2$, the element $2$ is itself a uniformizer of
$\mathcal O_{\mathfrak p}$ (`IsQ2Prime.associated`); the series are stated for the uniformizer $\pi = 2$, as in the
rational case.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Structure.RatTwoNF

open QuadFormsKB.Hanke2011Structure.RatOdd (RatSeries)

noncomputable section

/-! ### The prime of $\mathbb Q$ above $2$ -/

section Rat

theorem isQ2Prime_rat (v : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : IsQ2Prime v where
  two_mem := h2
  two_not_mem_sq := by
    intro h
    have hp : ConwaySloane.Mass.pv v = 2 := ConwaySloane.Mass.pv_eq_two_of_two_mem v h2
    have hp' : Rat.HeightOneSpectrum.natGenerator v = 2 := hp
    have := (Odd7.intCast_mem_pow_iff v (2 : ℤ) 2).1 (by exact_mod_cast h)
    rw [hp'] at this
    norm_num at this
  absNorm_eq := by
    rw [LocalDensity.NF.absNorm_rat]
    exact ConwaySloane.Mass.pv_eq_two_of_two_mem v h2

theorem exists_dyadic_rat : ∃ v : HeightOneSpectrum (𝓞 ℚ), (2 : 𝓞 ℚ) ∈ v.asIdeal := by
  let P : Nat.Primes := ⟨2, Nat.prime_two⟩
  refine ⟨Rat.HeightOneSpectrum.primesEquiv.symm P, ?_⟩
  have h := Odd7.pv_mem (Rat.HeightOneSpectrum.primesEquiv.symm P)
  have hp : ConwaySloane.Mass.pv (Rat.HeightOneSpectrum.primesEquiv.symm P) = 2 := by
    unfold ConwaySloane.Mass.pv
    rw [Equiv.apply_symm_apply]
  rw [hp] at h
  simpa using h

end Rat

/-! ### Squareclasses of $2^\nu w$ -/

section Sq

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
  {v : HeightOneSpectrum (𝓞 F)} {v' : HeightOneSpectrum (𝓞 F')} {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Fw" => v'.adicCompletion F'
local notation "𝔮" => v'.adicCompletionIntegers F'

theorem sqNF_mul {x y : 𝔬} (hx : x ≠ 0) (hy : y ≠ 0) :
    RatND.sqNF (x * y) = RatND.sqNF x * RatND.sqNF y := by
  rw [RatND.sqNF_of_ne hx, RatND.sqNF_of_ne hy, RatND.sqNF_of_ne (mul_ne_zero hx hy), ← map_mul]
  congr 1
  apply Units.ext
  simp

theorem sqMap_sqNF (σ : 𝔬 ≃+* 𝔮) {x : 𝔬} (hx : x ≠ 0) : sqMap σ (RatND.sqNF x) = RatND.sqNF (σ x) := by
  rw [RatND.sqNF_of_ne hx, RatND.sqNF_of_ne ((map_ne_zero_iff _ σ.injective).2 hx), sqMap_mk]
  congr 1
  apply Units.ext
  show fracIso σ (algebraMap 𝔬 Fv x) = algebraMap 𝔮 Fw (σ x)
  exact fracIso_algebraMap σ x

end Sq

section SqRat

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

theorem sqNF_two_pow (ν : ℕ) : RatND.sqNF ((2 : 𝔬) ^ ν) = Dyadic7.zSqCl v (2 ^ ν) := by
  have h1 : ((2 : 𝔬) ^ ν) ≠ 0 := pow_ne_zero _ (by
    intro h
    have := congrArg (fun z : 𝔬 => (z : Fv)) h
    simp at this)
  rw [RatND.sqNF_of_ne h1, Dyadic7.zSqCl_of_ne v (pow_ne_zero _ two_ne_zero)]
  refine congrArg SqCl.mk (Units.ext ?_)
  simp
  norm_cast

/-- Every unit of $\mathfrak o_v$ ($v \mid 2$ of $\mathbb Q$) has the squareclass of an odd integer. -/
theorem exists_odd_class (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) {u : 𝔬} (hu : IsUnit u) :
    ∃ w' : ℤ, Odd w' ∧ RatND.sqNF u = Dyadic7.zSqCl v w' := by
  have hu0 : u ≠ 0 := hu.ne_zero
  have hord : SqCl.ordZ (localOrd v) (localUnits_le_ker v) (RatND.sqNF u) = ((0 : ℕ) : ℤ) := by
    rw [RatND.sqNF_of_ne hu0, SqCl.ordZ_mk]
    have hmem : Units.mk0 ((u : 𝔬) : Fv) (by simpa using hu0) ∈ localUnits v :=
      ⟨hu.unit, Units.ext rfl⟩
    have := localUnits_le_ker v hmem
    rw [MonoidHom.mem_ker] at this
    rw [this]; rfl
  obtain ⟨w', hw', hS⟩ := Dyadic7.exists_zSqCl_eq v h2 _ 0 hord
  refine ⟨w', ?_, by simpa using hS⟩
  simp only [Dyadic7.sqUnits, Finset.mem_insert, Finset.mem_singleton] at hw'
  rcases hw' with rfl | rfl | rfl | rfl <;> decide

end SqRat

/-! ### The headline theorems -/

section Main

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The reference genus $\langle 1,\dots,1\rangle$ over $\mathbb Q$ has $\beta > 0$. -/
theorem beta_one_pos (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    0 < (LocGenus.mk (QuadForm.diag fun _ : Fin n => (1 : w.adicCompletionIntegers ℚ))).beta := by
  rw [LocGenus.beta_mk]
  unfold betaForm
  have e : Hanke2005.gramOf w (QuadForm.diag fun _ : Fin n => (1 : w.adicCompletionIntegers ℚ)) =
      (1 : Matrix (Fin n) (Fin n) (w.adicCompletion ℚ)) := by
    unfold Hanke2005.gramOf
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply,
      QuadForm.diag, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, map_add, map_one]
      norm_num
    · simp [hij, Ne.symm hij]
  rw [e]
  exact Hanke2005.hankeBeta_std_one_pos (v := w)

/-- **The transport identity for $A^*$.** -/
theorem trueAstarNF_transport {F' : Type} [Field F'] [NumberField F'] {v' : HeightOneSpectrum (𝓞 F')}
    (hv : IsQ2Prime v) (hv' : IsQ2Prime v') (σ : v.adicCompletionIntegers F ≃+* v'.adicCompletionIntegers F')
    {n : ℕ} (G₀ : LocGenus v n) (G₁ : LocGenus v' n) (h1 : G₁.beta ≠ 0) (S : LocalSqCl v) :
    RatND.trueAstarNF v n G₀ S = G₀.beta / G₁.beta * RatND.trueAstarNF v' n G₁ (sqMap σ S) := by
  rw [trueAstarNF_eq_mul, trueAstarNF_eq_mul, invBetaSum_transport hv hv' σ S 1,
    invBetaSum_transport hv hv' σ S (-1)]
  field_simp

theorem trueBstarNF_transport {F' : Type} [Field F'] [NumberField F'] {v' : HeightOneSpectrum (𝓞 F')}
    (hv : IsQ2Prime v) (hv' : IsQ2Prime v') (σ : v.adicCompletionIntegers F ≃+* v'.adicCompletionIntegers F')
    {n : ℕ} (G₀ : LocGenus v n) (G₁ : LocGenus v' n) (h1 : G₁.beta ≠ 0) (S : LocalSqCl v) :
    RatND.trueBstarNF v n G₀ S = G₀.beta / G₁.beta * RatND.trueBstarNF v' n G₁ (sqMap σ S) := by
  rw [trueBstarNF_eq_mul, trueBstarNF_eq_mul, invBetaSum_transport hv hv' σ S 1,
    invBetaSum_transport hv hv' σ S (-1)]
  field_simp

/-- The class of $2^\nu w$ is carried by $\hat\sigma$ to the class of $2^\nu w'$, $w'$ odd independent of $\nu$. -/
theorem sqMap_two_pow_mul (hv : IsQ2Prime v) (w₂ : HeightOneSpectrum (𝓞 ℚ)) (h2 : (2 : 𝓞 ℚ) ∈ w₂.asIdeal)
    (σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ) {w : 𝔬} (hw : IsUnit w) :
    ∃ w' : ℤ, Odd w' ∧ ∀ ν : ℕ,
      sqMap σ (RatND.sqNF ((2 : 𝔬) ^ ν * w)) = Dyadic7.zSqCl w₂ (2 ^ ν * w') := by
  obtain ⟨w', hw', hcl⟩ := exists_odd_class w₂ h2 (hw.map σ)
  refine ⟨w', hw', fun ν => ?_⟩
  have hw0 : w ≠ 0 := hw.ne_zero
  have h2ν : ((2 : 𝔬) ^ ν) ≠ 0 := pow_ne_zero _ (by
    intro h
    have := congrArg (fun z : 𝔬 => (z : Fv)) h
    simp at this)
  have hw'0 : w' ≠ 0 := by rintro rfl; exact absurd hw' (by decide)
  rw [sqMap_sqNF σ (mul_ne_zero h2ν hw0), map_mul, map_pow, map_ofNat,
    sqNF_mul (pow_ne_zero _ (by
      intro h
      have := congrArg (fun z : w₂.adicCompletionIntegers ℚ => (z : w₂.adicCompletion ℚ)) h
      simp at this)) (hw.map σ).ne_zero, sqNF_two_pow, hcl,
    ← Dyadic7.zSqCl_mul w₂ (pow_ne_zero _ two_ne_zero) hw'0]

/-- **Theorem 5.4 (for $A^*$) at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ of a number field, every rank $n$,
true local genera.**  Let $\mathfrak p$ be a finite prime of a number field $F$ with $N\mathfrak p = 2$ and
$2 \notin \mathfrak p^2$ (so $F_{\mathfrak p} \cong \mathbb Q_2$), $w \in \mathcal O_{\mathfrak p}^\times$ a unit and $G_0$ a reference
local genus.  Then the fixed-unit series $\sum_\nu A^*_{\mathfrak p;n}([2^\nu w])\,X^\nu$, $X = 2^{-s}$ (the uniformizer is $2$), is a
rational function of $X$: $P/Q$ for polynomials $P$, $Q$ with $Q(0) \ne 0$.  Unconditional (transport from
`RatTwo.theorem_5_4_two_A_rank`). -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23-24 (A*, F_p = Q_2, every n, every number field)"]
theorem theorem_5_4_two_nf_A (hv : IsQ2Prime v) {n : ℕ} {w : 𝔬} (hw : IsUnit w) (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun ν : ℕ => RatND.trueAstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ ν * w))) := by
  obtain ⟨w₂, h2⟩ := exists_dyadic_rat
  have hv₂ := isQ2Prime_rat w₂ h2
  let σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ := hv.equiv.trans hv₂.equiv.symm
  obtain ⟨w', hw', hcl⟩ := sqMap_two_pow_mul hv w₂ h2 σ hw
  set G₁ : LocGenus w₂ n := LocGenus.mk (QuadForm.diag fun _ : Fin n => (1 : w₂.adicCompletionIntegers ℚ)) with hG₁
  have hβ : G₁.beta ≠ 0 := (beta_one_pos w₂ n).ne'
  have hser := RatTwo.theorem_5_4_two_A_rank h2 hw' G₁
  have e : (PowerSeries.mk fun ν : ℕ => RatND.trueAstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ ν * w))) =
      PowerSeries.C (G₀.beta / G₁.beta) * PowerSeries.X ^ 0 *
        PowerSeries.mk fun ν : ℕ => RatTwo.trueAstar2 w₂ n G₁ (Dyadic7.zSqCl w₂ (2 ^ ν * w')) := by
    ext ν
    simp only [PowerSeries.coeff_mk, pow_zero, mul_one, PowerSeries.coeff_C_mul]
    rw [trueAstarNF_transport hv hv₂ σ G₀ G₁ hβ, hcl ν]
    rfl
  rw [e]
  exact RatSeries.CXpowMul _ 0 hser

/-- **Theorem 5.4 (for $B^*$) at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ of a number field, every rank $n$**: the fixed-unit
series $\sum_\nu B^*_{\mathfrak p;n}([2^\nu w])X^\nu$ is a rational function of $X = 2^{-s}$ (same hypotheses as
`theorem_5_4_two_nf_A`).  Unconditional. -/
@[kb "hanke2011structure" "Thm. 5.4, p. 23-24 (B*, F_p = Q_2, every n, every number field)"]
theorem theorem_5_4_two_nf_B (hv : IsQ2Prime v) {n : ℕ} {w : 𝔬} (hw : IsUnit w) (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun ν : ℕ => RatND.trueBstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ ν * w))) := by
  obtain ⟨w₂, h2⟩ := exists_dyadic_rat
  have hv₂ := isQ2Prime_rat w₂ h2
  let σ : 𝔬 ≃+* w₂.adicCompletionIntegers ℚ := hv.equiv.trans hv₂.equiv.symm
  obtain ⟨w', hw', hcl⟩ := sqMap_two_pow_mul hv w₂ h2 σ hw
  set G₁ : LocGenus w₂ n := LocGenus.mk (QuadForm.diag fun _ : Fin n => (1 : w₂.adicCompletionIntegers ℚ)) with hG₁
  have hβ : G₁.beta ≠ 0 := (beta_one_pos w₂ n).ne'
  have hser := RatTwo.theorem_5_4_two_B_rank h2 hw' G₁
  have e : (PowerSeries.mk fun ν : ℕ => RatND.trueBstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ ν * w))) =
      PowerSeries.C (G₀.beta / G₁.beta) * PowerSeries.X ^ 0 *
        PowerSeries.mk fun ν : ℕ => RatTwo.trueBstar2 w₂ n G₁ (Dyadic7.zSqCl w₂ (2 ^ ν * w')) := by
    ext ν
    simp only [PowerSeries.coeff_mk, pow_zero, mul_one, PowerSeries.coeff_C_mul]
    rw [trueBstarNF_transport hv hv₂ σ G₀ G₁ hβ, hcl ν]
    rfl
  rw [e]
  exact RatSeries.CXpowMul _ 0 hser

/-- **Corollary 5.5 for $A^*$ at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ of a number field, every rank $n$**
(distinguished family $\lambda(2^i) = 2^i$): the Euler factor $\sum_i A^*_{\mathfrak p;n}([2^i])\,2^{-is}$ is a rational
function of $2^{-s}$. -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (A*, F_p = Q_2, every n, every number field, lambda(2^i) = 2^i)"]
theorem cor_5_5_two_nf_A (hv : IsQ2Prime v) {n : ℕ} (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun i : ℕ => RatND.trueAstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ i))) := by
  simpa only [mul_one] using theorem_5_4_two_nf_A hv isUnit_one G₀

/-- **Corollary 5.5 for $B^*$ at a prime with $F_{\mathfrak p} \cong \mathbb Q_2$ of a number field, every rank $n$**
($\lambda(2^i) = 2^i$). -/
@[kb "hanke2011structure" "Cor. 5.5, p. 24 (B*, F_p = Q_2, every n, every number field, lambda(2^i) = 2^i)"]
theorem cor_5_5_two_nf_B (hv : IsQ2Prime v) {n : ℕ} (G₀ : LocGenus v n) :
    RatSeries (PowerSeries.mk fun i : ℕ => RatND.trueBstarNF v n G₀ (RatND.sqNF ((2 : 𝔬) ^ i))) := by
  simpa only [mul_one] using theorem_5_4_two_nf_B hv isUnit_one G₀

end Main

end

end QuadFormsKB.Hanke2011Structure.RatTwoNF

#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.theorem_5_4_two_nf_A
#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.theorem_5_4_two_nf_B
#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.cor_5_5_two_nf_A
#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.cor_5_5_two_nf_B
