/-
# Watson (1963), §7, Lemma 9 (i): the quaternary forms $g(4, q^2)$

For every prime $q$ there is a positive definite quaternary form $g$ over $\mathbb Z$ with $\det H_g = q^2$ and
$r_q(g) = 2$ (Watson 1963, §7, (7.8)–(7.11), Lemma 9 (i), pp. 560–561), which has rank $\ge 2$ modulo every prime
and whose reduction modulo $2$ vanishes on the radical of its polar form.

**Constructions** (indices 0-based; Watson's $x_1, \dots, x_4$ are `x 0, …, x 3` here).
* $q = 2$: $g = \Phi_4 = D_4$ (`phiD 3`, Watson's $g(4,4) = \Phi_4$), $\det H = 4$; modulo $2$ the radical is
  $\{(a,a,a,b)\}$, of dimension $2$.
* $q \equiv 3 \pmod 4$: $g = h \perp h$ with $h = x_0^2 + x_0x_1 + \tfrac14(q+1)x_1^2$ (Watson (7.8)); $\det H_h = q$.
* $q \equiv 1 \pmod 4$ (Watson (7.11), $\varepsilon = 1$): choose a prime $A \equiv 3 \pmod 4$ with $(A/q) = -1$
  (Dirichlet's theorem), and $w$ with $w^2 \equiv -q \pmod A$ (quadratic reciprocity); then, with
  $m = (w^2 + q)/A$, $C = (Aq + 1)/4$, $D = (q^2 - 1)/4$,
  $$g = A x_0^2 + q x_0 x_1 + q(mC - D) x_1^2 + 2w x_0 x_2 + m x_2^2 + q x_2 x_3 + C x_3^2 .$$

*Remark on coefficients.* The expansion $A g = (A x_0 + w x_2)^2 + A q x_0x_1 + \tfrac14 A q (Aq+1) x_1^2 + q x_2^2
+ A q x_2x_3 + \tfrac14 A (Aq+1) x_3^2$ of (7.11) as transcribed gives $\det H_g \ne q^2$ (e.g. $q = 5$, $A = 3$, $w = 1$
gives $225$); here the coefficient of $x_1^2$ is taken to be $q(mC - D)$, the value for which $\det H_g = q^2$ (checked in
`quat4_one_det`). Only the properties of $g$ stated in `exists_quaternary` are used downstream.
-/
import QuadFormsKB.Literature.Watson1963.ProbeFacts
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-! ### A family of quaternary forms -/

/-- **The family** $A x_0^2 + b\,x_0x_1 + c\,x_1^2 + 2w\,x_0x_2 + m\,x_2^2 + b'\,x_2x_3 + e\,x_3^2$ of quaternary
forms (the shape of Watson's (7.9) and (7.11)). Hessian
$\begin{pmatrix} 2A & b & 2w & 0 \\ b & 2c & 0 & 0 \\ 2w & 0 & 2m & b' \\ 0 & 0 & b' & 2e \end{pmatrix}$. -/
def quat4 (A b c w m b' e : ℤ) : QuadForm ℤ 4 :=
  QuadForm.ofUpper ![![A, b, 2 * w, 0], ![0, c, 0, 0], ![0, 0, m, b'], ![0, 0, 0, e]]

theorem quat4_hessian (A b c w m b' e : ℤ) : (quat4 A b c w m b' e).hessian =
    !![2 * A, b, 2 * w, 0; b, 2 * c, 0, 0; 2 * w, 0, 2 * m, b'; 0, 0, b', 2 * e] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quat4, QuadForm.hessian, QuadForm.ofUpper] <;> ring

theorem quat4_hessian_det (A b c w m b' e : ℤ) : (quat4 A b c w m b' e).hessian.det =
    -b ^ 2 * (4 * m * e - b' ^ 2) + 2 * c * (8 * A * m * e - 2 * A * b' ^ 2 - 8 * w ^ 2 * e) := by
  rw [quat4_hessian, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

theorem quat4_evalIn {K : Type*} [CommRing K] (A b c w m b' e : ℤ) (x : Fin 4 → K) :
    (quat4 A b c w m b' e).evalIn K x = A * x 0 ^ 2 + b * (x 0 * x 1) + c * x 1 ^ 2 + 2 * w * (x 0 * x 2) +
      m * x 2 ^ 2 + b' * (x 2 * x 3) + e * x 3 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_four, quat4, QuadForm.ofUpper]
  ring

/-! ### The radical modulo an odd prime -/

/-- The polar condition for `quat4` modulo $p$: $\bar x \perp \bar H \bar z$ for all $\bar z$ iff the four columns
of $\bar H$ are orthogonal to $\bar x$. -/
theorem quat4_orth_iff {p : ℕ} [Fact p.Prime] (A b c w m b' e : ℤ) (x : Fin 4 → ZMod p) :
    (∀ z, x ⬝ᵥ ((quat4 A b c w m b' e).hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0) ↔
      (x 0 * (2 * A) + x 1 * b + x 2 * (2 * w) = 0 ∧ x 0 * b + x 1 * (2 * c) = 0 ∧
        x 0 * (2 * w) + x 2 * (2 * m) + x 3 * b' = 0 ∧ x 2 * b' + x 3 * (2 * e) = 0) := by
  rw [quat4_hessian]
  constructor
  · intro h
    have h0 := h (Pi.single 0 1)
    have h1 := h (Pi.single 1 1)
    have h2 := h (Pi.single 2 1)
    have h3 := h (Pi.single 3 1)
    simp [dotProduct, mulVec, Fin.sum_univ_four, Pi.single_apply] at h0 h1 h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
  · rintro ⟨h0, h1, h2, h3⟩ z
    simp [dotProduct, mulVec, Fin.sum_univ_four]
    linear_combination z 0 * h0 + z 1 * h1 + z 2 * h2 + z 3 * h3

/-- For odd $p$, membership in the radical modulo $p$ is just the polar condition (since $2\bar g(\bar x) =
\bar x^{\mathsf T}\bar H\bar x$). -/
theorem quat4_mem_rad_iff {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (A b c w m b' e : ℤ)
    (x : Fin 4 → ZMod p) : x ∈ radModP p (quat4 A b c w m b' e) ↔
      (x 0 * (2 * A) + x 1 * b + x 2 * (2 * w) = 0 ∧ x 0 * b + x 1 * (2 * c) = 0 ∧
        x 0 * (2 * w) + x 2 * (2 * m) + x 3 * b' = 0 ∧ x 2 * b' + x 3 * (2 * e) = 0) := by
  rw [mem_radModP, quat4_orth_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨h0, h1, h2, h3⟩ := h
    rw [quat4_evalIn]
    have : (2 : ZMod p) * (A * x 0 ^ 2 + b * (x 0 * x 1) + c * x 1 ^ 2 + 2 * w * (x 0 * x 2) + m * x 2 ^ 2 +
        b' * (x 2 * x 3) + e * x 3 ^ 2) = 0 := by
      linear_combination x 0 * h0 + x 1 * h1 + x 2 * h2 + x 3 * h3
    exact (mul_eq_zero.1 this).resolve_left hp2

/-- **Rank $2$ from two radical vectors and two determining coordinates.** If $v_1, v_2$ are linearly independent
elements of the radical of $f$ modulo $p$, and an element of the radical with coordinates $i$ and $j$ zero is zero,
then $r_p(f) = 4 - 2 = 2$. -/
theorem rankModP_eq_two {p : ℕ} [Fact p.Prime] (f : QuadForm ℤ 4) (v₁ v₂ : Fin 4 → ZMod p)
    (h₁ : v₁ ∈ radModP p f) (h₂ : v₂ ∈ radModP p f)
    (hli : ∀ s t : ZMod p, s • v₁ + t • v₂ = 0 → s = 0 ∧ t = 0) (i j : Fin 4)
    (hinj : ∀ x ∈ radModP p f, x i = 0 → x j = 0 → x = 0) : rankModP p f = 2 := by
  have hge : 2 ≤ Module.finrank (ZMod p) (radModP p f) := by
    have hli' : LinearIndependent (ZMod p) ![v₁, v₂] := LinearIndependent.pair_iff.2 hli
    have hsp : Submodule.span (ZMod p) (Set.range ![v₁, v₂]) ≤ radModP p f := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      fin_cases k <;> simpa
    have := Submodule.finrank_mono hsp
    rwa [finrank_span_eq_card hli', Fintype.card_fin] at this
  have hle : Module.finrank (ZMod p) (radModP p f) ≤ 2 := by
    let φ : radModP p f →ₗ[ZMod p] ZMod p × ZMod p :=
      ((LinearMap.proj i).comp (radModP p f).subtype).prod ((LinearMap.proj j).comp (radModP p f).subtype)
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have hx' : x.1 i = 0 ∧ x.1 j = 0 := by simpa [φ] using hx
      exact Subtype.ext (hinj x.1 x.2 hx'.1 hx'.2)
    have := LinearMap.finrank_le_finrank_of_injective hφ
    simpa using this
  have := rankModP_add_finrank p f
  omega

/-! ### Assembling the conclusion -/

theorem two_ne_zero_zmod (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 h')

/-- A vector orthogonal to all columns of $\bar H$ is zero when $p \nmid \det H$. -/
theorem eq_zero_of_orth_of_not_dvd_det {n : ℕ} (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n)
    (h : ¬ (p : ℤ) ∣ f.hessian.det) (x : Fin n → ZMod p)
    (hx : ∀ z, x ⬝ᵥ (f.hessian.map (algebraMap ℤ (ZMod p)) *ᵥ z) = 0) : x = 0 := by
  set M := f.hessian.map (algebraMap ℤ (ZMod p))
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    have : M.det = ((f.hessian.det : ℤ) : ZMod p) := by
      rw [show M = (Int.castRingHom (ZMod p)).mapMatrix f.hessian from rfl, ← RingHom.map_det]
      rfl
    rw [this, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  have hv : x ᵥ* M = 0 := by
    funext j
    have := hx (Pi.single j 1)
    rw [dotProduct_mulVec, dotProduct_single, mul_one] at this
    simpa using this
  have := congrArg (· ᵥ* M⁻¹) hv
  simp only [vecMul_vecMul, mul_nonsing_inv _ hdet, vecMul_one, zero_vecMul] at this
  exact this

/-- **Assembling `exists_quaternary`:** positive definiteness, $\det H = q^2$, $r_q(g) = 2$ and the radical
condition at $2$ imply rank $\ge 2$ modulo every prime (for $p \ne q$ the rank is $4$ since $p \nmid q^2$). -/
theorem quaternary_of_data (q : ℕ) [hq : Fact q.Prime] (g : QuadForm ℤ 4) (hpd : IntQF.PosDef g)
    (hdet : g.hessian.det = (q : ℤ) ^ 2) (hr : rankModP q g = 2)
    (h2 : ∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
      g.evalIn (ZMod 2) x = 0) :
    ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧ g.hessian.det = (q : ℤ) ^ 2 ∧ rankModP q g = 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
      (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
        g.evalIn (ZMod 2) x = 0) := by
  refine ⟨g, hpd, hdet, hr, fun p hp => ?_, h2⟩
  by_cases hpq : p = q
  · subst hpq
    exact hr.ge
  · rw [rankModP_eq_of_not_dvd_det p ?_]
    · norm_num
    · rw [hdet]
      intro hd
      have : p ∣ q := hp.out.dvd_of_dvd_pow (n := 2) (by exact_mod_cast hd)
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq.out).1 this)

/-- The radical condition at $2$ when $\det H$ is odd: the radical of the polar form is zero. -/
theorem quat_rad_two_of_odd (g : QuadForm ℤ 4) (h : ¬ ((2 : ℕ) : ℤ) ∣ g.hessian.det)
    (x : Fin 4 → ZMod 2) (hx : ∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) :
    g.evalIn (ZMod 2) x = 0 := by
  rw [eq_zero_of_orth_of_not_dvd_det 2 g h x hx]
  simp [QuadForm.evalIn]

/-! ### The case $q = 2$: $g = \Phi_4$ -/

theorem phiD3_check : ∀ x : Fin 4 → ZMod 2, (phiD 3).evalIn (ZMod 2) x = 0 →
    (∀ z, x ⬝ᵥ ((phiD 3).hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) → x 0 = 0 → x 3 = 0 → x = 0 := by
  decide +kernel

theorem phiD3_v1 : (phiD 3).evalIn (ZMod 2) ![1, 1, 1, 0] = 0 ∧
    ∀ z, (![1, 1, 1, 0] : Fin 4 → ZMod 2) ⬝ᵥ ((phiD 3).hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0 := by
  decide +kernel

theorem phiD3_v2 : (phiD 3).evalIn (ZMod 2) ![0, 0, 0, 1] = 0 ∧
    ∀ z, (![0, 0, 0, 1] : Fin 4 → ZMod 2) ⬝ᵥ ((phiD 3).hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0 := by
  decide +kernel

theorem phiD3_li : ∀ s t : ZMod 2, s • (![1, 1, 1, 0] : Fin 4 → ZMod 2) + t • ![0, 0, 0, 1] = 0 →
    s = 0 ∧ t = 0 := by
  decide +kernel

theorem phiD3_rad2 : ∀ x : Fin 4 → ZMod 2,
    (∀ z, x ⬝ᵥ ((phiD 3).hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
    (phiD 3).evalIn (ZMod 2) x = 0 := by
  decide +kernel

/-- **$r_2(\Phi_4) = 2$:** the radical of $\Phi_4 = D_4$ modulo $2$ is $\{(a, a, a, b)\}$. -/
theorem rankModP_two_phiD3 : rankModP 2 (phiD 3) = 2 :=
  rankModP_eq_two (phiD 3) ![1, 1, 1, 0] ![0, 0, 0, 1] phiD3_v1 phiD3_v2 phiD3_li 0 3
    (fun x hx h0 h3 => phiD3_check x hx.1 hx.2 h0 h3)

theorem exists_quaternary_two :
    ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧ g.hessian.det = ((2 : ℕ) : ℤ) ^ 2 ∧ rankModP 2 g = 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
      (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
        g.evalIn (ZMod 2) x = 0) :=
  quaternary_of_data 2 (phiD 3) (phiD_posDef 3 (by norm_num)) (by rw [phiD_hessian_det]; norm_num)
    rankModP_two_phiD3 phiD3_rad2

/-! ### The case $q \equiv 3 \pmod 4$: $g = h \perp h$ -/

/-- **$h \perp h$ is positive definite:** $4 g = (2x_0 + x_1)^2 + q x_1^2 + (2x_2 + x_3)^2 + q x_3^2$ for
$q = 4k + 3$, $h = x_0^2 + x_0x_1 + (k+1)x_1^2$. -/
theorem quat4_three_posDef (k : ℕ) : IntQF.PosDef (quat4 1 1 (k + 1) 0 1 1 (k + 1)) := by
  intro x hx
  by_contra hle
  rw [not_lt] at hle
  have key : 4 * (quat4 1 1 (k + 1) 0 1 1 (k + 1)).eval x = (2 * x 0 + x 1) ^ 2 + (4 * k + 3) * x 1 ^ 2 +
      (2 * x 2 + x 3) ^ 2 + (4 * k + 3) * x 3 ^ 2 := by
    rw [QuadForm.eval, quat4_evalIn]
    push_cast
    ring
  have hk : (0 : ℤ) ≤ k := by positivity
  have h1 := sq_nonneg (2 * x 0 + x 1)
  have h2 := sq_nonneg (2 * x 2 + x 3)
  have h3 : 0 ≤ ((k : ℤ)) * x 1 ^ 2 := by positivity
  have h4 : 0 ≤ ((k : ℤ)) * x 3 ^ 2 := by positivity
  have h5 := sq_nonneg (x 1)
  have h6 := sq_nonneg (x 3)
  have hx1 : x 1 ^ 2 = 0 := by nlinarith
  have hx3 : x 3 ^ 2 = 0 := by nlinarith
  have hx1' : x 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hx1
  have hx3' : x 3 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hx3
  have hx0 : (2 * x 0) ^ 2 = 0 := by
    rw [hx1'] at h1 key
    rw [hx3'] at h2 key
    nlinarith
  have hx2 : (2 * x 2) ^ 2 = 0 := by
    rw [hx1'] at h1 key
    rw [hx3'] at h2 key
    nlinarith
  have hx0' : x 0 = 0 := by simpa using (pow_eq_zero_iff (two_ne_zero) |>.1 hx0)
  have hx2' : x 2 = 0 := by simpa using (pow_eq_zero_iff (two_ne_zero) |>.1 hx2)
  apply hx
  funext i
  fin_cases i <;> simp [hx0', hx1', hx2', hx3']

theorem quat4_three_det (k : ℕ) :
    (quat4 1 1 (k + 1) 0 1 1 (k + 1)).hessian.det = ((4 * k + 3 : ℕ) : ℤ) ^ 2 := by
  rw [quat4_hessian_det]
  push_cast
  ring

/-- **$r_q(h \perp h) = 2$** for $q = 4k + 3$: the radical modulo $q$ is spanned by $(1, -2, 0, 0)$ and
$(0, 0, 1, -2)$ (each binary $h$ has Hessian $\begin{pmatrix} 2 & 1 \\ 1 & (q+1)/2 \end{pmatrix}$ of rank $1$
modulo $q$). -/
theorem rankModP_quat4_three (q : ℕ) [hq : Fact q.Prime] (k : ℕ) (hk : q = 4 * k + 3) :
    rankModP q (quat4 1 1 (k + 1) 0 1 1 (k + 1)) = 2 := by
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod q (by omega)
  have h0 : ((4 * k + 3 : ℕ) : ZMod q) = 0 := by rw [← hk]; exact ZMod.natCast_self q
  push_cast at h0
  refine rankModP_eq_two _ ![1, -2, 0, 0] ![0, 0, 1, -2] ?_ ?_ ?_ 0 2 ?_
  · rw [quat4_mem_rad_iff h2]
    simp
    linear_combination (-1 : ZMod q) * h0
  · rw [quat4_mem_rad_iff h2]
    simp
    linear_combination (-1 : ZMod q) * h0
  · intro s t hst
    have e0 := congrFun hst 0
    have e2 := congrFun hst 2
    simp at e0 e2
    exact ⟨e0, e2⟩
  · intro x hx hx0 hx2
    rw [quat4_mem_rad_iff h2] at hx
    obtain ⟨e0, e1, e2, e3⟩ := hx
    simp [hx0, hx2] at e0 e2
    funext i
    fin_cases i <;> simp [hx0, hx2, e0, e2]

theorem exists_quaternary_three (q : ℕ) [hq : Fact q.Prime] (h4 : q % 4 = 3) :
    ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧ g.hessian.det = (q : ℤ) ^ 2 ∧ rankModP q g = 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
      (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
        g.evalIn (ZMod 2) x = 0) := by
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
  have hdet := quat4_three_det k
  rw [← hk] at hdet
  refine quaternary_of_data q _ (quat4_three_posDef k) hdet (rankModP_quat4_three q k hk)
    (quat_rad_two_of_odd _ ?_)
  rw [hdet]
  intro hd
  have : (2 : ℕ) ∣ q := by exact_mod_cast Int.Prime.dvd_pow' (by norm_num) hd
  omega

/-! ### The case $q \equiv 1 \pmod 4$ -/

theorem eq_zero_of_mul_sq {c s : ℤ} (hc : 0 < c) (h : c * s ^ 2 = 0) : s = 0 :=
  pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 h).resolve_left hc.ne')

/-- **The determinant of the $q \equiv 1 \pmod 4$ family:** $\det H = q^2$ when $A m = w^2 + q$, $4C = Aq + 1$,
$4D = q^2 - 1$. -/
theorem quat4_one_det (A q w m C D : ℤ) (hm : A * m = w ^ 2 + q) (hC : 4 * C = A * q + 1)
    (hD : 4 * D = q ^ 2 - 1) :
    (quat4 A q (q * (m * C - D)) w m q C).hessian.det = q ^ 2 := by
  rw [quat4_hessian_det]
  linear_combination (16 * (q * (m * C - D)) * C) * hm + (4 * (q * (m * C - D)) * q) * hC - q ^ 2 * hD

/-- **Positive definiteness of the $q \equiv 1 \pmod 4$ family** (for $A, q > 0$): with $K = w^2(Aq+1) + A$,
$P = w^2 q + 1$, $u = 2A x_0 + q x_1 + 2w x_2$, $v = K x_1 - 2w x_2$, $y = 2P x_2 + K x_3$,
$$4AKP\, g(\vec x) = KP\,u^2 + qP\,v^2 + qA\,y^2 + AK\,x_3^2 .$$ -/
theorem quat4_one_posDef (A q w m C D : ℤ) (hA : 0 < A) (hq : 0 < q) (hm : A * m = w ^ 2 + q)
    (hC : 4 * C = A * q + 1) (hD : 4 * D = q ^ 2 - 1) :
    IntQF.PosDef (quat4 A q (q * (m * C - D)) w m q C) := by
  intro x hx
  by_contra hle
  rw [not_lt] at hle
  have hK : 0 < w ^ 2 * (A * q + 1) + A := by positivity
  have hP : 0 < w ^ 2 * q + 1 := by positivity
  have key : 4 * A * (w ^ 2 * (A * q + 1) + A) * (w ^ 2 * q + 1) *
      (quat4 A q (q * (m * C - D)) w m q C).eval x =
      (w ^ 2 * (A * q + 1) + A) * (w ^ 2 * q + 1) * (2 * A * x 0 + q * x 1 + 2 * w * x 2) ^ 2 +
      q * (w ^ 2 * q + 1) * ((w ^ 2 * (A * q + 1) + A) * x 1 - 2 * w * x 2) ^ 2 +
      q * A * (2 * (w ^ 2 * q + 1) * x 2 + (w ^ 2 * (A * q + 1) + A) * x 3) ^ 2 +
      A * (w ^ 2 * (A * q + 1) + A) * x 3 ^ 2 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
    have hmQ : (m : ℚ) = (w ^ 2 + q) / A := by
      rw [eq_div_iff hAq]
      exact_mod_cast (by linarith : m * A = w ^ 2 + q)
    have hCQ : (C : ℚ) = (A * q + 1) / 4 := by
      have : (4 : ℚ) * C = A * q + 1 := by exact_mod_cast hC
      linarith
    have hDQ : (D : ℚ) = (q ^ 2 - 1) / 4 := by
      have : (4 : ℚ) * D = q ^ 2 - 1 := by exact_mod_cast hD
      linarith
    rw [QuadForm.eval, quat4_evalIn]
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hmQ, hCQ, hDQ]
    field_simp
    ring
  have hg : 4 * A * (w ^ 2 * (A * q + 1) + A) * (w ^ 2 * q + 1) *
      (quat4 A q (q * (m * C - D)) w m q C).eval x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
  rw [key] at hg
  have t1 : 0 ≤ (w ^ 2 * (A * q + 1) + A) * (w ^ 2 * q + 1) * (2 * A * x 0 + q * x 1 + 2 * w * x 2) ^ 2 :=
    by positivity
  have t2 : 0 ≤ q * (w ^ 2 * q + 1) * ((w ^ 2 * (A * q + 1) + A) * x 1 - 2 * w * x 2) ^ 2 := by positivity
  have t3 : 0 ≤ q * A * (2 * (w ^ 2 * q + 1) * x 2 + (w ^ 2 * (A * q + 1) + A) * x 3) ^ 2 := by positivity
  have t4 : 0 ≤ A * (w ^ 2 * (A * q + 1) + A) * x 3 ^ 2 := by positivity
  have hx3 : x 3 = 0 := eq_zero_of_mul_sq (c := A * (w ^ 2 * (A * q + 1) + A)) (by positivity) (by linarith)
  have z4 : A * (w ^ 2 * (A * q + 1) + A) * x 3 ^ 2 = 0 := by rw [hx3]; ring
  have hy : 2 * (w ^ 2 * q + 1) * x 2 + (w ^ 2 * (A * q + 1) + A) * x 3 = 0 :=
    eq_zero_of_mul_sq (c := q * A) (by positivity) (by linarith)
  have z3 : q * A * (2 * (w ^ 2 * q + 1) * x 2 + (w ^ 2 * (A * q + 1) + A) * x 3) ^ 2 = 0 := by
    rw [hy]; ring
  have hx2 : x 2 = 0 := by
    rw [hx3, mul_zero, add_zero] at hy
    exact (mul_eq_zero.1 hy).resolve_left (by positivity)
  have hv : (w ^ 2 * (A * q + 1) + A) * x 1 - 2 * w * x 2 = 0 :=
    eq_zero_of_mul_sq (c := q * (w ^ 2 * q + 1)) (by positivity) (by linarith)
  have z2 : q * (w ^ 2 * q + 1) * ((w ^ 2 * (A * q + 1) + A) * x 1 - 2 * w * x 2) ^ 2 = 0 := by
    rw [hv]; ring
  have hx1 : x 1 = 0 := by
    rw [hx2, mul_zero, sub_zero] at hv
    exact (mul_eq_zero.1 hv).resolve_left hK.ne'
  have hu : 2 * A * x 0 + q * x 1 + 2 * w * x 2 = 0 :=
    eq_zero_of_mul_sq (c := (w ^ 2 * (A * q + 1) + A) * (w ^ 2 * q + 1)) (by positivity) (by linarith)
  have hx0 : x 0 = 0 := by
    rw [hx2, hx1] at hu
    simp only [mul_zero, add_zero] at hu
    exact (mul_eq_zero.1 hu).resolve_left (by positivity)
  apply hx
  funext i
  fin_cases i <;> simp [hx0, hx1, hx2, hx3]

/-- **$r_q(g) = 2$ for the $q \equiv 1 \pmod 4$ family** (any odd prime $p$ with $p \mid Q$ and $p \nmid A$): the
radical modulo $p$ is spanned by $(0, 1, 0, 0)$ and $(w, 0, -A, 0)$. -/
theorem rankModP_quat4_one {p : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (A Q w m C D : ℤ)
    (hQ : (Q : ZMod p) = 0) (hA : (A : ZMod p) ≠ 0) (hm : A * m = w ^ 2 + Q) (hC : 4 * C = A * Q + 1) :
    rankModP p (quat4 A Q (Q * (m * C - D)) w m Q C) = 2 := by
  have hAm : (A : ZMod p) * m = w ^ 2 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hm
    push_cast at this
    rw [hQ, add_zero] at this
    exact this
  have hC4 : (4 : ZMod p) * C = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod p) hC
    push_cast at this
    rw [hQ, mul_zero, zero_add] at this
    exact this
  have hCne : (C : ZMod p) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hC4
    exact zero_ne_one hC4
  refine rankModP_eq_two _ ![0, 1, 0, 0] ![(w : ZMod p), 0, -A, 0] ?_ ?_ ?_ 1 2 ?_
  · rw [quat4_mem_rad_iff hp2]
    simp [hQ]
  · rw [quat4_mem_rad_iff hp2]
    simp
    exact ⟨by ring, Or.inr hQ, by linear_combination (-2 : ZMod p) * hAm, Or.inr hQ⟩
  · intro s t hst
    have e1 := congrFun hst 1
    have e2 := congrFun hst 2
    simp at e1 e2
    exact ⟨e1, e2.resolve_right hA⟩
  · intro x hx hx1 hx2
    rw [quat4_mem_rad_iff hp2] at hx
    obtain ⟨e0, e1, e2, e3⟩ := hx
    have h2A : (2 : ZMod p) * A ≠ 0 := mul_ne_zero hp2 hA
    have h2C : (2 : ZMod p) * C ≠ 0 := mul_ne_zero hp2 hCne
    have hx0 : x 0 = 0 := by
      rw [hx1, hx2] at e0
      have : x 0 * (2 * A) = 0 := by simpa using e0
      exact (mul_eq_zero.1 this).resolve_right (by simpa [mul_comm] using h2A)
    have hx3 : x 3 = 0 := by
      rw [hx2] at e3
      have : x 3 * (2 * C) = 0 := by simpa using e3
      exact (mul_eq_zero.1 this).resolve_right (by simpa [mul_comm] using h2C)
    funext i
    fin_cases i <;> simp [hx0, hx1, hx2, hx3]

/-- **Dirichlet and quadratic reciprocity step of Watson (7.11):** for a prime $q \equiv 1 \pmod 4$ there are a
prime $A \equiv 3 \pmod 4$ with $q \nmid A$ (indeed $(A/q) = -1$) and $w \in \mathbb Z$ with $A \mid w^2 + q$. -/
theorem exists_prime_three_mod_four_sqrt (q : ℕ) [hq : Fact q.Prime] (hq4 : q % 4 = 1) :
    ∃ (A : ℕ) (w : ℤ), A.Prime ∧ A % 4 = 3 ∧ ¬ q ∣ A ∧ (A : ℤ) ∣ w ^ 2 + q := by
  have hq2 : q ≠ 2 := by omega
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2)
  have hn0 : n ≠ 0 := fun h => hn ⟨0, by simp [h]⟩
  have co4 : Nat.Coprime 4 q := by
    rw [Nat.Coprime, Nat.gcd_rec, hq4]
    rfl
  have : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨a0, ha4, haq⟩ := Nat.chineseRemainder co4 3 n.val
  have hacast : (a0 : ZMod q) = n := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 haq, ZMod.natCast_zmod_val]
  have ha4' : a0 % 4 = 3 := by
    unfold Nat.ModEq at ha4
    omega
  have hcop : Nat.Coprime a0 (4 * q) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, ha4']
      rfl
    · have : ¬ q ∣ a0 := by
        intro h
        have := (ZMod.natCast_eq_zero_iff a0 q).2 h
        rw [hacast] at this
        exact hn0 this
      exact ((Nat.Prime.coprime_iff_not_dvd hq.out).2 this).symm
  obtain ⟨A, -, hAp, hAmod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 (q := 4 * q) (a := a0)
    (by have := hq.out.pos; omega) hcop
  have hA4 : A % 4 = 3 := by
    have := Nat.ModEq.of_mul_right q hAmod
    unfold Nat.ModEq at this
    omega
  have hAq : (A : ZMod q) = n := by
    rw [← hacast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.of_mul_left 4 hAmod)
  have hqA : ¬ q ∣ A := by
    intro h
    have := (ZMod.natCast_eq_zero_iff A q).2 h
    rw [hAq] at this
    exact hn0 this
  have : Fact A.Prime := ⟨hAp⟩
  have hA2 : A ≠ 2 := by omega
  have hsym : legendreSym A (-(q : ℤ)) = 1 := by
    have e1 : legendreSym A (-1) = -1 := by
      rw [legendreSym.at_neg_one hA2]
      exact ZMod.χ₄_nat_three_mod_four hA4
    have e2 : legendreSym A (q : ℤ) = -1 := by
      rw [legendreSym.quadratic_reciprocity_one_mod_four hq4 hA2]
      exact (legendreSym.eq_neg_one_iff' (p := q)).2 (by rw [hAq]; exact hn)
    rw [show -(q : ℤ) = -1 * q by ring, legendreSym.mul, e1, e2]
    norm_num
  have hne : ((-(q : ℤ) : ℤ) : ZMod A) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg] at h
    have h1 : A ∣ q := Int.natCast_dvd_natCast.1 h
    have h2 := (Nat.prime_dvd_prime_iff_eq hAp hq.out).1 h1
    exact hqA ⟨1, by omega⟩
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff A hne).1 hsym
  refine ⟨A, (r.val : ℤ), hAp, hA4, hqA, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast at hr ⊢
  rw [ZMod.natCast_zmod_val r]
  linear_combination (-1 : ZMod A) * hr

/-- **Watson's quaternary form for $q \equiv 1 \pmod 4$** (Watson 1963, (7.11) with $\varepsilon = 1$; see the
module docstring for the corrected coefficient). -/
theorem exists_quaternary_one (q : ℕ) [hq : Fact q.Prime] (h4 : q % 4 = 1) :
    ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧ g.hessian.det = (q : ℤ) ^ 2 ∧ rankModP q g = 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
      (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
        g.evalIn (ZMod 2) x = 0) := by
  obtain ⟨A, w, hAp, hA4, hqA, ⟨m, hm⟩⟩ := exists_prime_three_mod_four_sqrt q h4
  obtain ⟨a, ha⟩ : ∃ a, A = 4 * a + 3 := ⟨A / 4, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, 4 * C = (A : ℤ) * q + 1 :=
    ⟨4 * a * k + a + 3 * k + 1, by rw [ha, hk]; push_cast; ring⟩
  obtain ⟨D, hD⟩ : ∃ D : ℤ, 4 * D = (q : ℤ) ^ 2 - 1 := ⟨4 * k ^ 2 + 2 * k, by rw [hk]; push_cast; ring⟩
  have hm' : (A : ℤ) * m = w ^ 2 + q := hm.symm
  have hApos : (0 : ℤ) < A := by exact_mod_cast hAp.pos
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.out.pos
  have hdet := quat4_one_det A q w m C D hm' hC hD
  have hp2 := two_ne_zero_zmod q (by omega)
  have hQ : (((q : ℕ) : ℤ) : ZMod q) = 0 := by simp
  have hAne : ((A : ℤ) : ZMod q) ≠ 0 := by
    intro h
    apply hqA
    exact (ZMod.natCast_eq_zero_iff A q).1 (by exact_mod_cast h)
  refine quaternary_of_data q _ (quat4_one_posDef A q w m C D hApos hqpos hm' hC hD) hdet
    (rankModP_quat4_one hp2 A q w m C D hQ hAne hm' hC) (quat_rad_two_of_odd _ ?_)
  rw [hdet]
  intro hd
  have : (2 : ℕ) ∣ q := by exact_mod_cast Int.Prime.dvd_pow' (by norm_num) hd
  omega

/-- **Watson's quaternary forms $g(4, q^2)$** (Watson 1963, §7, Lemma 9 (i), p. 560, with (7.8), (7.9), (7.11) and
$g(4,4) = \Phi_4$): for every prime $q$ there is a positive definite quaternary $\mathbb Z$-form $g$ with
$\det H_g = q^2$, rank $r_q(g) = 2$ modulo $q$, rank $\ge 2$ modulo every prime, and such that modulo $2$ the form
vanishes on the radical of its polar form. **Unconditional** (uses Dirichlet's theorem and quadratic reciprocity
from Mathlib).

Constructions: $q = 2$: $\Phi_4$; $q \equiv 3 \pmod 4$: $h \perp h$ with $h = x_0^2 + x_0x_1 + \tfrac14(q+1)x_1^2$;
$q \equiv 1 \pmod 4$: the form of (7.11) built from a prime $A \equiv 3 \pmod 4$ with $(A/q) = -1$. -/
@[kb "watson1963" "§7, Lemma 9 (i), (7.8)–(7.11), pp. 560–561"]
theorem exists_quaternary (q : ℕ) [hq : Fact q.Prime] :
    ∃ g : QuadForm ℤ 4, IntQF.PosDef g ∧ g.hessian.det = (q : ℤ) ^ 2 ∧ rankModP q g = 2 ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 ≤ rankModP p g) ∧
      (∀ x : Fin 4 → ZMod 2, (∀ z, x ⬝ᵥ (g.hessian.map (algebraMap ℤ (ZMod 2)) *ᵥ z) = 0) →
        g.evalIn (ZMod 2) x = 0) := by
  rcases hq.out.eq_two_or_odd with h2 | hodd
  · subst h2
    exact exists_quaternary_two
  · have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases this with h | h
    · exact exists_quaternary_one q h
    · exact exists_quaternary_three q h

end QuadFormsKB.Watson1963
