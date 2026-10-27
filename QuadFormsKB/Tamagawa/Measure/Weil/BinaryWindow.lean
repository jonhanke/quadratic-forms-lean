import QuadFormsKB.Tamagawa.Measure.Weil.BinaryTorusLocal
import QuadFormsKB.Tamagawa.Measure.Weil.PDFinRatio

/-!
# The window: the torus image of $1+\varpi^k\mathfrak o_v[\omega]$ is a principal congruence subgroup

**Layer:** a finite place $v$ of a number field $F$ (dyadic included), $D\in\mathcal O_F$, $Q_0 = \langle1,D\rangle$,
$E_v = F_v[\omega]$, $\omega^2 = -D$, $R_v = \mathfrak o_v[\omega]$, $|2|_v = q^{-s}$ ($s$ = `sExp v`).

**Proves**
* **`torSOK_image_window`**: for $k\ge1$, the torus map $z\mapsto z/\bar z$ carries
  $W_k = \{z : z\equiv1\bmod\varpi^kR_v\}$ (`windowZ`) **onto** the principal congruence subgroup
  $\{g\in SO(V)(F_v) : g\equiv1\bmod\varpi^{k+s}\}$ (`congSetSO`). *Proof:* for $z = 1+\varpi^ky$, $N(z)$ is a unit and
  $z/\bar z = 1 + 2\,(\ldots)$; conversely $g = \rho(p+q\omega)$ with $p\equiv1$, $q\equiv0\bmod\varpi^{k+s}$ is the image of
  $z = 1 + \frac{q}{1+p}\,\omega$, and $|1+p|_v = |2|_v$.
-/

open WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa.BinaryNormOne QuadFormsKB.Lattices QuadFormsKB.HilbertModular
  QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- **The window** $W_k = \{z\in E_v^\times : \mathrm{re}\,z\equiv1,\ \mathrm{im}\,z\equiv0\bmod\varpi^k\}$. -/
def windowZ (k : ℕ) : Set (QuadK D Fv)ˣ :=
  {z | Valued.v ((z : QuadK D Fv).re - 1) ≤ exp (-(k : ℤ)) ∧ Valued.v (z : QuadK D Fv).im ≤ exp (-(k : ℤ))}

/-- **The principal congruence subgroup of level $m$ of $SO(V)(F_v)$** (as a set): $g\equiv1\bmod\varpi^m$. -/
def congSetSO (m : ℕ) : Set (soSub (formF (diagForm1 D)) Fv) :=
  {g | ∀ i j, Valued.v ((((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val i j) -
      (1 : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ exp (-(m : ℤ))}

theorem valued_D_le_one : Valued.v (dIn D Fv) ≤ 1 := by
  simp only [dIn]
  rw [← IsScalarTower.algebraMap_apply]
  exact valued_int_le_one v D

theorem exp_neg_le_one (k : ℕ) : (exp (-(k : ℤ)) : ℤᵐ⁰) ≤ 1 := by
  rw [← exp_zero, exp_le_exp]; omega

theorem exp_mul_exp_le {a b c : ℕ} (h : c ≤ a + b) :
    (exp (-(a : ℤ)) : ℤᵐ⁰) * exp (-(b : ℤ)) ≤ exp (-(c : ℤ)) := by
  rw [← exp_add, exp_le_exp]; omega


theorem torP_smul' {K : Type*} [Field K] {d : K} (c : K) (hc : c ≠ 0) (z : QuadraticAlgebra K d 0) :
    torP (c • z) = torP z := by
  simp only [torP, norm_eq, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  by_cases hN : z.re * z.re - d * z.im * z.im = 0
  · have : c * z.re * (c * z.re) - d * (c * z.im) * (c * z.im) = c ^ 2 * (z.re * z.re - d * z.im * z.im) := by ring
    rw [this, hN, mul_zero, div_zero, div_zero]
  · field_simp

theorem torQ_smul' {K : Type*} [Field K] {d : K} (c : K) (hc : c ≠ 0) (z : QuadraticAlgebra K d 0) :
    torQ (c • z) = torQ z := by
  simp only [torQ, norm_eq, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]
  by_cases hN : z.re * z.re - d * z.im * z.im = 0
  · have : c * z.re * (c * z.re) - d * (c * z.im) * (c * z.im) = c ^ 2 * (z.re * z.re - d * z.im * z.im) := by ring
    rw [this, hN, mul_zero, div_zero, div_zero]
  · field_simp

set_option maxHeartbeats 2000000 in
/-- **The torus image of the window is the principal congruence subgroup of level $k + s$.** -/
@[kb "weil1982" "§2.2 (gauge-form volumes; linearization at 1) [unverified]"]
theorem torSOK_image_window (hD : D ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    torSOK D Fv '' windowZ D v k = congSetSO D v (k + sExp v) := by
  have h2 : Valued.v (2 : Fv) = exp (-(sExp v : ℤ)) := valued_two_eq v
  have hdD : algebraMap F Fv (dD D) = -(dIn D Fv) := dD_algebraMap D Fv
  ext g
  constructor
  · rintro ⟨z, ⟨hre, him⟩, rfl⟩
    set x := (z : QuadK D Fv).re
    set y := (z : QuadK D Fv).im
    have hk1 : (exp (-(k : ℤ)) : ℤᵐ⁰) < 1 := by rw [← exp_zero, exp_lt_exp]; omega
    have hx1 : Valued.v x = 1 := by
      have : x = 1 + (x - 1) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hre.trans_lt hk1), map_one]
    have hdv : Valued.v (algebraMap F Fv (dD D)) ≤ 1 := by rw [hdD, Valuation.map_neg]; exact valued_D_le_one D v
    have hN : (z : QuadK D Fv).norm = 1 + (2 * (x - 1) + (x - 1) ^ 2 - algebraMap F Fv (dD D) * y ^ 2) := by
      rw [norm_eq]; ring
    have hy2 : Valued.v (y ^ 2) ≤ exp (-(k : ℤ)) := by
      rw [map_pow, sq]
      calc Valued.v y * Valued.v y ≤ exp (-(k : ℤ)) * 1 :=
            mul_le_mul' him ((him).trans (exp_neg_le_one k))
        _ = _ := mul_one _
    have hrest : Valued.v (2 * (x - 1) + (x - 1) ^ 2 - algebraMap F Fv (dD D) * y ^ 2) < 1 := by
      refine lt_of_le_of_lt ?_ hk1
      refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans (max_le ?_ ?_)) ?_)
      · rw [map_mul]
        calc Valued.v (2 : Fv) * Valued.v (x - 1) ≤ 1 * exp (-(k : ℤ)) :=
              mul_le_mul' (by rw [h2]; exact exp_neg_le_one _) hre
          _ = _ := one_mul _
      · rw [map_pow, sq]
        calc Valued.v (x - 1) * Valued.v (x - 1) ≤ exp (-(k : ℤ)) * 1 :=
              mul_le_mul' hre (hre.trans (exp_neg_le_one k))
          _ = _ := mul_one _
      · rw [map_mul]
        calc Valued.v (algebraMap F Fv (dD D)) * Valued.v (y ^ 2) ≤ 1 * exp (-(k : ℤ)) := mul_le_mul' hdv hy2
          _ = _ := one_mul _
    have hNv : Valued.v (z : QuadK D Fv).norm = 1 := by
      rw [hN, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact hrest), map_one]
    have hP1 : torP (z : QuadK D Fv) - 1 = 2 * algebraMap F Fv (dD D) * y ^ 2 / (z : QuadK D Fv).norm := by
      have hN0 : (z : QuadK D Fv).norm ≠ 0 := norm_ne_zero_of_unit z
      rw [torP, div_sub_one hN0, norm_eq]; ring
    have hεs : ∀ t : Fv, Valued.v t ≤ exp (-(k : ℤ)) →
        Valued.v (2 * t) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := fun t ht => by
      rw [map_mul, h2, mul_comm]
      calc Valued.v t * exp (-(sExp v : ℤ)) ≤ exp (-(k : ℤ)) * exp (-(sExp v : ℤ)) := mul_le_mul' ht le_rfl
        _ ≤ _ := exp_mul_exp_le (by omega)
    have hpv : Valued.v (torP (z : QuadK D Fv) - 1) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := by
      rw [hP1, map_div₀, hNv, div_one, mul_assoc]
      refine hεs _ ?_
      rw [map_mul]
      calc Valued.v (algebraMap F Fv (dD D)) * Valued.v (y ^ 2) ≤ 1 * exp (-(k : ℤ)) := mul_le_mul' hdv hy2
        _ = _ := one_mul _
    have hqv : Valued.v (torQ (z : QuadK D Fv)) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := by
      rw [torQ, map_div₀, hNv, div_one, mul_assoc]
      refine hεs _ ?_
      rw [map_mul, hx1, one_mul]; exact him
    intro i j
    have hval := torSOK_val D Fv z
    rw [hval]
    fin_cases i <;> fin_cases j
    · simpa [rotMat, normOneOf, normOneG] using hpv
    · have h01 : Valued.v (-dIn D Fv * 1 * torQ (z : QuadK D Fv) * 1) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := by
        rw [mul_one, Valuation.map_mul, Valuation.map_mul, Valuation.map_neg, map_one, mul_one]
        calc Valued.v (dIn D Fv) * Valued.v (torQ (z : QuadK D Fv)) ≤ 1 * exp (-((k + sExp v : ℕ) : ℤ)) :=
              mul_le_mul' (valued_D_le_one D v) hqv
          _ = _ := one_mul _
      simpa [rotMat, normOneOf, normOneG] using h01
    · simpa [rotMat, normOneOf, normOneG] using hqv
    · simpa [rotMat, normOneOf, normOneG] using hpv
  · intro hg
    obtain ⟨e1, -, e3, -⟩ := orth_diag D hD (g : orthGroup (formF (diagForm1 D)) Fv).2
    have hdet : (((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val).det = 1 := mem_soSub.1 g.2
    set p := ((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 0 0
    set q := ((g : orthGroup (formF (diagForm1 D)) Fv) : GL (Fin 2) Fv).val 1 0
    have hp : Valued.v (p - 1) ≤ exp (-((k + sExp v : ℕ) : ℤ)) := by simpa using hg 0 0
    have hq : Valued.v q ≤ exp (-((k + sExp v : ℕ) : ℤ)) := by simpa using hg 1 0
    have hlt : Valued.v (p - 1) < Valued.v (2 : Fv) := by
      rw [h2]; refine hp.trans_lt ?_; rw [exp_lt_exp]; omega
    have h1p : Valued.v (1 + p) = Valued.v (2 : Fv) := by
      have : 1 + p = 2 + (p - 1) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ hlt]
    have h1p0 : 1 + p ≠ 0 := by
      intro h0; rw [h0, Valuation.map_zero, h2] at h1p; exact exp_ne_zero h1p.symm
    have hnorm : p ^ 2 + dIn D Fv * q ^ 2 = 1 := e3
    have hdk : algebraMap F Fv (dD D) = -(dIn D Fv) := hdD
    have hz0 : (⟨1 + p, q⟩ : QuadK D Fv).norm ≠ 0 := by
      rw [norm_one_add hdk hnorm]; exact mul_ne_zero two_ne_zero h1p0
    set z0 : QuadK D Fv := (1 + p)⁻¹ • (⟨1 + p, q⟩ : QuadK D Fv)
    have hz0' : z0.norm ≠ 0 := by
      have : z0.norm = ((1 + p)⁻¹) ^ 2 * (⟨1 + p, q⟩ : QuadK D Fv).norm := by
        simp only [z0, norm_eq, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, smul_eq_mul]; ring
      rw [this]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero h1p0)) hz0
    refine ⟨unitOfNorm z0 hz0', ⟨?_, ?_⟩, ?_⟩
    · have : (unitOfNorm z0 hz0' : QuadK D Fv).re - 1 = 0 := by
        simp only [coe_unitOfNorm, z0, QuadraticAlgebra.re_smul, smul_eq_mul]; field_simp; ring
      rw [this, Valuation.map_zero]; exact bot_le
    · simp only [coe_unitOfNorm, z0, QuadraticAlgebra.im_smul, smul_eq_mul, map_mul, map_inv₀, h1p, h2]
      calc _ ≤ (exp (-(sExp v : ℤ)))⁻¹ * exp (-((k + sExp v : ℕ) : ℤ)) := mul_le_mul' le_rfl hq
        _ = exp (-(k : ℤ)) := by rw [← exp_neg, ← exp_add]; congr 1; push_cast; ring
    · obtain ⟨hP, hQ⟩ := torP_torQ_one_add hdk hnorm h1p0
      refine torSOK_eq_of_torP_torQ D Fv hD _ g ?_ ?_
      · change torP z0 = p
        rw [torP_smul' _ (inv_ne_zero h1p0), hP]
      · change torQ z0 = q
        rw [torQ_smul' _ (inv_ne_zero h1p0), hQ]

end QuadFormsKB.Tamagawa.Measure.Weil
