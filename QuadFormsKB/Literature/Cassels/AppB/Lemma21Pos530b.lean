/-
# Cassels, Appendix B, §2, Lemma 2.1 for $D > 0$, part b: the proper automorphs of an indefinite form

The group `AutSL f` of an integral binary form $f = ax^2 + bxy + cy^2$ of non-square discriminant $D$: its elements are
$\begin{pmatrix}(t-bu)/2 & -cu\\ au & (t+bu)/2\end{pmatrix}$ with $t^2 - Du^2 = 4$ (for primitive $f$).
-/
import QuadFormsKB.Literature.Cassels.AppB.Lemma21Pos530

open Filter Topology Matrix MeasureTheory
open scoped Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels

namespace Lemma21Pos530

open QuadFormsKB.Binary

section Aut

/-- Helper: **the shape of a proper automorph of a primitive form.** For a primitive integral binary form
$f = ax^2 + bxy + cy^2$ with $a \ne 0$ and $\gamma = \begin{pmatrix} p & q\\ r & s\end{pmatrix} \in \mathrm{Aut}^+(f)$ there
are integers $t, u$ with $t^2 - (b^2 - 4ac)u^2 = 4$, $2p = t - bu$, $q = -cu$, $r = au$, $2s = t + bu$.
(Proof: $\gamma$ commutes with $\begin{pmatrix} b & 2c\\ -2a & -b\end{pmatrix}$; primitivity gives $a \mid r$.)
Arguments: `f` the form, `hprim` its primitivity, `ha` that $a \ne 0$, `γ` the automorph, `hγ` its membership in
`AutSL f`. -/
theorem autSL_data (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) {γ : GL (Fin 2) ℤ} (hγ : γ ∈ AutSL f) :
    ∃ t u : ℤ, t ^ 2 - (f.b ^ 2 - 4 * f.a * f.c) * u ^ 2 = 4 ∧ 2 * γ.val 0 0 = t - f.b * u ∧
      γ.val 0 1 = -(f.c * u) ∧ γ.val 1 0 = f.a * u ∧ 2 * γ.val 1 1 = t + f.b * u := by
  have hd : γ.val.det = 1 := (mem_autSL.mp hγ).2
  rw [Matrix.det_fin_two] at hd
  have e1 := Lemma21Aux.eval_mulVec_aut f hγ ![1, 0]
  have e2 := Lemma21Aux.eval_mulVec_aut f hγ ![0, 1]
  have e3 := Lemma21Aux.eval_mulVec_aut f hγ ![1, 1]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, BinQF.eval_eq] at e1 e2 e3
  generalize γ.val 0 0 = p at *
  generalize γ.val 0 1 = q at *
  generalize γ.val 1 0 = r at *
  generalize γ.val 1 1 = s at *
  have h00 : f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2 - f.a = 0 := by linear_combination e1
  have h11 : f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2 - f.c = 0 := by linear_combination e2
  have h01 : 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s - f.b = 0 := by
    linear_combination e3 - e1 - e2
  have hdet : p * s - q * r = 1 := hd
  have k1 : f.a * q + f.c * r = 0 := by
    have : 2 * (f.a * q + f.c * r) = 0 := by
      linear_combination (-2 * q) * h00 + p * h01 - (f.b * p + 2 * f.c * r) * hdet
    linarith
  have k2 : f.a * (s - p) = f.b * r := by
    have : 2 * (f.a * (s - p) - f.b * r) = 0 := by
      linear_combination (-s) * (2 * h00) + r * h01 + (2 * f.a * p + f.b * r) * hdet
    linarith
  -- primitivity gives `a ∣ r`
  have hbez : ∃ x y z : ℤ, x * f.a + y * f.b + z * f.c = 1 := by
    have hg1 : ((Int.gcd f.b f.c : ℕ) : ℤ) = f.b * Int.gcdA f.b f.c + f.c * Int.gcdB f.b f.c :=
      Int.gcd_eq_gcd_ab _ _
    have hg2 : ((Int.gcd f.a ((Int.gcd f.b f.c : ℕ) : ℤ) : ℕ) : ℤ) =
        f.a * Int.gcdA f.a ((Int.gcd f.b f.c : ℕ) : ℤ) + ((Int.gcd f.b f.c : ℕ) : ℤ) *
          Int.gcdB f.a ((Int.gcd f.b f.c : ℕ) : ℤ) := Int.gcd_eq_gcd_ab _ _
    have hu : IsUnit ((Int.gcd f.a ((Int.gcd f.b f.c : ℕ) : ℤ) : ℕ) : ℤ) :=
      hprim _ (Int.gcd_dvd_left _ _)
        ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _))
        ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _))
    have h1 : ((Int.gcd f.a ((Int.gcd f.b f.c : ℕ) : ℤ) : ℕ) : ℤ) = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h
      · exact h
      · have := Int.natCast_nonneg (Int.gcd f.a ((Int.gcd f.b f.c : ℕ) : ℤ))
        omega
    refine ⟨Int.gcdA f.a ((Int.gcd f.b f.c : ℕ) : ℤ),
      Int.gcdB f.a ((Int.gcd f.b f.c : ℕ) : ℤ) * Int.gcdA f.b f.c,
      Int.gcdB f.a ((Int.gcd f.b f.c : ℕ) : ℤ) * Int.gcdB f.b f.c, ?_⟩
    rw [h1] at hg2
    linear_combination -hg2 - (Int.gcdB f.a ((Int.gcd f.b f.c : ℕ) : ℤ)) * hg1
  have hdvd2 : f.a ∣ r := by
    obtain ⟨x, y, z, hxyz⟩ := hbez
    refine ⟨x * r + y * (s - p) - z * q, ?_⟩
    linear_combination (-r) * hxyz - y * k2 + z * k1
  obtain ⟨u, hu⟩ := hdvd2
  have hq : q = -(f.c * u) := by
    refine mul_left_cancel₀ ha ?_
    rw [hu] at k1
    linear_combination k1
  have hsp : s - p = f.b * u := by
    refine mul_left_cancel₀ ha ?_
    rw [hu] at k2
    linear_combination k2
  refine ⟨p + s, u, ?_, by linarith, hq, hu, by linarith⟩
  subst hq
  rw [hu] at hdet
  have hs : s = p + f.b * u := by linarith
  subst hs
  linear_combination 4 * hdet

/-- Helper: **parity.** If $t^2 - (b^2 - 4ac)u^2 = 4$ then $t \equiv bu \pmod 2$, i.e. $t = 2p + bu$ for an integer $p$.
Arguments: `f` the form (coefficients $a, b, c$), `t u` the integers, `h` the equation. -/
theorem pell_parity (f : BinQF) {t u : ℤ} (h : t ^ 2 - (f.b ^ 2 - 4 * f.a * f.c) * u ^ 2 = 4) :
    ∃ p : ℤ, t = 2 * p + f.b * u := by
  have hev : Even ((t - f.b * u) * (t + f.b * u)) :=
    ⟨2 * (1 - f.a * f.c * u ^ 2), by linear_combination h⟩
  have h1 : Even (t - f.b * u) := by
    rcases Int.even_mul.mp hev with h1 | h1
    · exact h1
    · have := h1.sub (even_two_mul (f.b * u))
      have e : t + f.b * u - 2 * (f.b * u) = t - f.b * u := by ring
      rwa [e] at this
  obtain ⟨k, hk⟩ := h1
  exact ⟨k, by linarith⟩

/-- Helper: **every solution of $t^2 - Du^2 = 4$ gives a proper automorph.** For an integral binary form $f$ and integers
$t, u$ with $t^2 - (b^2 - 4ac)u^2 = 4$ there are an integer $p$ with $t = 2p + bu$ and
$\gamma \in \mathrm{Aut}^+(f)$ with matrix $\begin{pmatrix} p & -cu\\ au & p + bu\end{pmatrix}$. -/
theorem exists_autSL_of_pell (f : BinQF) {t u : ℤ} (h : t ^ 2 - (f.b ^ 2 - 4 * f.a * f.c) * u ^ 2 = 4) :
    ∃ γ ∈ AutSL f, ∃ p : ℤ, t = 2 * p + f.b * u ∧ γ.val = !![p, -(f.c * u); f.a * u, p + f.b * u] := by
  obtain ⟨p, hp⟩ := pell_parity f h
  subst hp
  have hdet : p * (p + f.b * u) - (-(f.c * u)) * (f.a * u) = 1 := by
    have : 4 * (p * (p + f.b * u) - (-(f.c * u)) * (f.a * u) - 1) = 0 := by linear_combination h
    linarith
  have hsq : (p * (p + f.b * u) - (-(f.c * u)) * (f.a * u)) ^ 2 = 1 := by rw [hdet]; norm_num
  refine ⟨glOf p (-(f.c * u)) (f.a * u) (p + f.b * u) hsq, ?_, p, rfl, rfl⟩
  rw [mem_autSL]
  refine ⟨?_, by simpa [Matrix.det_fin_two_of] using hdet⟩
  have key : ∀ x : Fin 2 → ℤ, f.eval ((!![p, -(f.c * u); f.a * u, p + f.b * u] *ᵥ x) 0)
      ((!![p, -(f.c * u); f.a * u, p + f.b * u] *ᵥ x) 1) = f.eval (x 0) (x 1) := by
    intro x
    simp only [BinQF.eval_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2) * hdet
  intro x
  have e1 : (!![p, -(f.c * u); f.a * u, p + f.b * u] *ᵥ x) =
      ![(!![p, -(f.c * u); f.a * u, p + f.b * u] *ᵥ x) 0, (!![p, -(f.c * u); f.a * u, p + f.b * u] *ᵥ x) 1] :=
    vec_two_eq _
  have e2 : x = ![x 0, x 1] := vec_two_eq _
  have := key x
  unfold BinQF.eval at this
  rw [← e1, ← e2] at this
  exact this

end Aut

section Coord

/-- Helper: **$\sqrt D$ for the discriminant $D = b^2 - 4ac$ of $f$**, as a real number. Argument: `f` the form. -/
noncomputable def sD (f : BinQF) : ℝ := Real.sqrt (f.disc : ℝ)

/-- Helper: $(\sqrt D)^2 = b^2 - 4ac$ when $D \ge 0$. Arguments: `f` the form, `h` that $\operatorname{disc} f \ge 0$. -/
theorem sD_sq (f : BinQF) (h : 0 ≤ f.disc) : sD f ^ 2 = (f.b : ℝ) ^ 2 - 4 * f.a * f.c := by
  unfold sD
  rw [Real.sq_sqrt (by exact_mod_cast h)]
  simp [BinQF.disc]

/-- Helper: **the matrix of the two real linear forms $L_1 = ax + \tfrac{b - \sqrt D}{2}y$,
$L_2 = x + \tfrac{b + \sqrt D}{2a}y$ with $L_1L_2 = f$.** Argument: `f` the form (with $a \ne 0$ for the second row). -/
noncomputable def Bm (f : BinQF) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(f.a : ℝ), ((f.b : ℝ) - sD f) / 2; 1, ((f.b : ℝ) + sD f) / (2 * f.a)]

/-- Helper: $\det B = \sqrt D$ ($a \ne 0$). Arguments: `f` the form, `ha : a ≠ 0`. -/
theorem det_Bm (f : BinQF) (ha : f.a ≠ 0) : (Bm f).det = sD f := by
  have ha' : (f.a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [Bm, Matrix.det_fin_two_of]
  field_simp
  ring

/-- Helper: **the real coordinates $(L_1(w), L_2(w))$ of an integer vector $w$.** Arguments: `f` the form, `w` the
vector. -/
noncomputable def yv (f : BinQF) (w : Fin 2 → ℤ) : Fin 2 → ℝ := (Bm f).mulVec (fun i => (w i : ℝ))

/-- Helper: the first coordinate $L_1(w)$. -/
theorem yv_zero (f : BinQF) (w : Fin 2 → ℤ) :
    yv f w 0 = f.a * (w 0 : ℝ) + ((f.b : ℝ) - sD f) / 2 * (w 1 : ℝ) := by
  simp [yv, Bm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper: the second coordinate $L_2(w)$. -/
theorem yv_one (f : BinQF) (w : Fin 2 → ℤ) :
    yv f w 1 = (w 0 : ℝ) + ((f.b : ℝ) + sD f) / (2 * f.a) * (w 1 : ℝ) := by
  simp [yv, Bm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper: **$L_1(w)L_2(w) = f(w)$** (for $D \ge 0$, $a \ne 0$). Arguments: `f` the form, `hD : 0 ≤ disc f`,
`ha : a ≠ 0`, `w` the vector. -/
theorem yv_mul (f : BinQF) (hD : 0 ≤ f.disc) (ha : f.a ≠ 0) (w : Fin 2 → ℤ) :
    yv f w 0 * yv f w 1 = ((f.eval (w 0) (w 1) : ℤ) : ℝ) := by
  have ha' : (f.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hs := sD_sq f hD
  rw [yv_zero, yv_one, BinQF.eval_eq]
  push_cast
  field_simp
  linear_combination (-(w 1 : ℝ) ^ 2) * hs

/-- Helper: **a proper automorph with data $(t, u)$ scales $L_1$ by $(t - \sqrt D u)/2$ and $L_2$ by $(t + \sqrt D u)/2$.**
Arguments: `f` the form, `hD : 0 ≤ disc f`, `ha : a ≠ 0`, `M` the matrix of the automorph, `t u` the integers with the
shape equations `h00 h01 h10 h11` of `autSL_data`, `w` the vector. -/
theorem yv_aut (f : BinQF) (hD : 0 ≤ f.disc) (ha : f.a ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℤ) (t u : ℤ)
    (h00 : 2 * M 0 0 = t - f.b * u) (h01 : M 0 1 = -(f.c * u)) (h10 : M 1 0 = f.a * u)
    (h11 : 2 * M 1 1 = t + f.b * u) (w : Fin 2 → ℤ) :
    yv f (M *ᵥ w) 0 = (t - sD f * u) / 2 * yv f w 0 ∧ yv f (M *ᵥ w) 1 = (t + sD f * u) / 2 * yv f w 1 := by
  have ha' : (f.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hs := sD_sq f hD
  have r00 : (M 0 0 : ℝ) = (t - f.b * u) / 2 := by
    have : (2 * M 0 0 : ℝ) = t - f.b * u := by exact_mod_cast h00
    linarith
  have r11 : (M 1 1 : ℝ) = (t + f.b * u) / 2 := by
    have : (2 * M 1 1 : ℝ) = t + f.b * u := by exact_mod_cast h11
    linarith
  have r01 : (M 0 1 : ℝ) = -(f.c * u) := by exact_mod_cast h01
  have r10 : (M 1 0 : ℝ) = f.a * u := by exact_mod_cast h10
  have e0 : ((M *ᵥ w) 0 : ℝ) = M 0 0 * w 0 + M 0 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have e1 : ((M *ᵥ w) 1 : ℝ) = M 1 0 * w 0 + M 1 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · rw [yv_zero, yv_zero, e0, e1]
    simp only [r00, r01, r10, r11]
    field_simp
    linear_combination (-(u : ℝ) * (w 1 : ℝ)) * hs
  · rw [yv_one, yv_one, e0, e1]
    simp only [r00, r01, r10, r11]
    field_simp
    linear_combination (-(u : ℝ) * (w 1 : ℝ)) * hs

end Coord

section Domain

/-- Helper: **minimality of the fundamental unit for integer solutions.** If `η` is the fundamental unit of norm $+1$ of
discriminant $D$ (`IsNormOneFundamentalUnit D η`) and $t, u > 0$ are integers with $t^2 - Du^2 = 4$, then
$\eta \le (t + u\sqrt D)/2$. -/
theorem unit_ge {D : ℤ} {η : ℝ} (hη : IsNormOneFundamentalUnit D η) {t u : ℤ} (ht : 0 < t) (hu : 0 < u)
    (h : t ^ 2 - D * u ^ 2 = 4) : η ≤ ((t : ℝ) + u * Real.sqrt D) / 2 := by
  obtain ⟨tn, rfl⟩ := Int.eq_ofNat_of_zero_le ht.le
  obtain ⟨un, rfl⟩ := Int.eq_ofNat_of_zero_le hu.le
  have := hη.2.2 tn un (by exact_mod_cast hu) h
  simpa using this

/-- Helper: **uniqueness in the fundamental domain.** If a proper automorph $\gamma$ of the primitive form $f$
($a \ne 0$, $D > 0$, `η` the fundamental unit of norm $+1$) maps a vector $w$ whose coordinates $(L_1, L_2)(w)$ lie in the
sector `sectorCone η` to a vector whose coordinates also lie in the sector, then $\gamma w = w$. Arguments: `f` the form,
`hprim` its primitivity, `ha : a ≠ 0`, `hD : 0 < disc f`, `η` and `hη` the unit, `γ` and `hγ` the automorph, `w` the vector,
`h1` and `h2` the two sector memberships. -/
theorem sector_unique (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) (hD : 0 < f.disc) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) {γ : GL (Fin 2) ℤ} (hγ : γ ∈ AutSL f) {w : Fin 2 → ℤ}
    (h1 : yv f w ∈ sectorCone η) (h2 : yv f (γ.val *ᵥ w) ∈ sectorCone η) : γ.val *ᵥ w = w := by
  obtain ⟨t, u, htu, h00, h01, h10, h11⟩ := autSL_data f hprim ha hγ
  have hD' : (0 : ℝ) < f.disc := by exact_mod_cast hD
  have hs := sD_sq f hD.le
  have hs0 : 0 < sD f := Real.sqrt_pos.mpr hD'
  have hdisc : f.disc = f.b ^ 2 - 4 * f.a * f.c := by simp [BinQF.disc]
  rw [← hdisc] at htu
  obtain ⟨hy0, hy1⟩ := yv_aut f hD.le ha γ.val t u h00 h01 h10 h11 w
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  simp only [hy0, hy1] at b1 b2 b3
  have ey0 : 0 < yv f w 0 := lt_of_lt_of_le a1 a2
  have htuR : (t : ℝ) ^ 2 - (f.disc : ℝ) * (u : ℝ) ^ 2 = 4 := by exact_mod_cast htu
  have hdiscR : (f.disc : ℝ) = sD f ^ 2 := by rw [hs]; simp [BinQF.disc]
  have hlm : (t - sD f * u) / 2 * ((t + sD f * u) / 2) = 1 := by
    rw [hdiscR] at htuR
    linear_combination htuR / 4
  set lam : ℝ := (t - sD f * u) / 2 with hlam_def
  set mu : ℝ := (t + sD f * u) / 2 with hmu_def
  have hη1 : 1 < η := hη.1
  have hlam : 0 < lam := (mul_pos_iff_of_pos_right ey0).mp (lt_of_lt_of_le b1 b2)
  have hmu : 0 < mu := (mul_pos_iff_of_pos_right a1).mp b1
  have hη0 : 0 < η := by linarith
  -- both scalings are `< η`
  have hlt : lam < η := by
    have h3 : lam ^ 2 * yv f w 0 < η ^ 2 * yv f w 1 := by
      have := mul_lt_mul_of_pos_left b3 hlam
      nlinarith
    have h4 : lam ^ 2 < η ^ 2 := by
      have : η ^ 2 * yv f w 1 ≤ η ^ 2 * yv f w 0 := mul_le_mul_of_nonneg_left a2 (by positivity)
      by_contra hc
      push Not at hc
      nlinarith
    by_contra hc
    push Not at hc
    nlinarith
  have hmult : mu < η := by
    have h3 : yv f w 1 ≤ lam ^ 2 * yv f w 0 := by
      have := mul_le_mul_of_nonneg_left b2 hlam.le
      nlinarith
    have h4 : 1 < lam ^ 2 * η ^ 2 := by
      have h5 : lam ^ 2 * yv f w 0 < lam ^ 2 * (η ^ 2 * yv f w 1) := mul_lt_mul_of_pos_left a3 (by positivity)
      by_contra hc
      push Not at hc
      nlinarith
    have h6 : 1 < lam * η := by
      by_contra hc
      push Not at hc
      have hp := mul_pos hlam hη0
      have := pow_le_one₀ hp.le hc (n := 2)
      nlinarith
    nlinarith
  have hdisc' : f.disc = f.b ^ 2 - 4 * f.a * f.c := hdisc
  have hU : ∀ {t' u' : ℤ}, 0 < t' → 0 < u' → t' ^ 2 - f.disc * u' ^ 2 = 4 →
      η ≤ ((t' : ℝ) + u' * sD f) / 2 := fun ht hu h => unit_ge hη ht hu h
  rcases lt_trichotomy u 0 with hu | hu | hu
  · exfalso
    have huR : (u : ℝ) < 0 := by exact_mod_cast hu
    have htpos : (0 : ℝ) < t := by
      have : (t : ℝ) = lam + mu := by rw [hlam_def, hmu_def]; ring
      rw [this]; linarith
    have := hU (t' := t) (u' := -u) (by exact_mod_cast htpos) (by omega) (by rw [← hdisc'] at *; linear_combination htu)
    push_cast at this
    have e : ((t : ℝ) + -(u : ℝ) * sD f) / 2 = lam := by rw [hlam_def]; ring
    linarith
  · subst hu
    have htR : (t : ℝ) = 2 * lam := by rw [hlam_def]; push_cast; ring
    have ht2 : (t : ℝ) ^ 2 = 4 := by simpa using htuR
    have ht0 : (0 : ℝ) < t := by rw [htR]; linarith
    have ht2' : t = 2 := by
      have : (t : ℝ) = 2 := by nlinarith
      exact_mod_cast this
    subst ht2'
    have hM : γ.val = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> omega
    rw [hM, Matrix.one_mulVec]
  · exfalso
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have htpos : (0 : ℝ) < t := by
      have : (t : ℝ) = lam + mu := by rw [hlam_def, hmu_def]; ring
      rw [this]; linarith
    have := hU (t' := t) (u' := u) (by exact_mod_cast htpos) hu (by rw [← hdisc'] at *; linear_combination htu)
    have e : ((t : ℝ) + u * sD f) / 2 = mu := by rw [hmu_def]; ring
    linarith

/-- Helper: **the generator of the proper automorphs.** For $D > 0$ and `η` the fundamental unit of norm $+1$ there is
$\gamma_0 \in \mathrm{Aut}^+(f)$ with $L_1(\gamma_0 w) = \eta L_1(w)$ and $L_2(\gamma_0 w) = \eta^{-1}L_2(w)$. Arguments:
`f` the form, `hD : 0 < disc f`, `ha : a ≠ 0`, `hη` the unit. -/
theorem exists_gen (f : BinQF) (hD : 0 < f.disc) (ha : f.a ≠ 0) {η : ℝ} (hη : IsNormOneFundamentalUnit f.disc η) :
    ∃ γ ∈ AutSL f, ∀ w : Fin 2 → ℤ, yv f (γ.val *ᵥ w) 0 = η * yv f w 0 ∧
      yv f (γ.val *ᵥ w) 1 = η⁻¹ * yv f w 1 := by
  obtain ⟨-, ⟨t, u, hu, htu, hηeq⟩, -⟩ := hη
  have hdisc : f.disc = f.b ^ 2 - 4 * f.a * f.c := by simp [BinQF.disc]
  have htu' : (t : ℤ) ^ 2 - (f.b ^ 2 - 4 * f.a * f.c) * (-(u : ℤ)) ^ 2 = 4 := by
    rw [← hdisc]; linear_combination htu
  obtain ⟨γ, hγ, p, hp, hM⟩ := exists_autSL_of_pell f htu'
  have hs := sD_sq f hD.le
  have hs0 : 0 < sD f := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hdiscR : (f.disc : ℝ) = sD f ^ 2 := by rw [hs]; simp [BinQF.disc]
  have htuR : (t : ℝ) ^ 2 - (f.disc : ℝ) * (u : ℝ) ^ 2 = 4 := by exact_mod_cast htu
  refine ⟨γ, hγ, fun w => ?_⟩
  have := yv_aut f hD.le ha γ.val t (-(u : ℤ)) (by rw [hM]; simp; linarith) (by rw [hM]; simp)
    (by rw [hM]; simp) (by rw [hM]; simp; linarith) w
  push_cast at this
  have e1 : ((t : ℝ) - sD f * (-(u : ℝ))) / 2 = η := by
    rw [hηeq]; unfold sD; ring
  have e2 : ((t : ℝ) + sD f * (-(u : ℝ))) / 2 = η⁻¹ := by
    refine (inv_eq_of_mul_eq_one_right ?_).symm
    rw [hηeq]
    unfold sD at *
    rw [hdiscR] at htuR
    linear_combination htuR / 4
  rw [e1, e2] at this
  exact this

/-- Helper: **the generator $\gamma_0$ and its inverse scale the coordinates; a power does too.** For `γ₀ ∈ AutSL f` with
$L_1(\gamma_0 w) = \eta L_1(w)$ and $L_2(\gamma_0 w) = \eta^{-1}L_2(w)$ for all $w$ and every integer $k$:
$L_1(\gamma_0^k w) = \eta^k L_1(w)$, $L_2(\gamma_0^k w) = \eta^{-k}L_2(w)$. Arguments: `f` the form, `η` the unit
(nonzero), `γ₀` the generator, `h₀` its scaling property, `k` the exponent, `w` the vector. -/
theorem zpow_scale (f : BinQF) {η : ℝ} (hη0 : η ≠ 0) (γ₀ : GL (Fin 2) ℤ)
    (h₀ : ∀ w : Fin 2 → ℤ, yv f (γ₀.val *ᵥ w) 0 = η * yv f w 0 ∧ yv f (γ₀.val *ᵥ w) 1 = η⁻¹ * yv f w 1)
    (k : ℤ) (w : Fin 2 → ℤ) :
    yv f ((γ₀ ^ k).val *ᵥ w) 0 = η ^ k * yv f w 0 ∧ yv f ((γ₀ ^ k).val *ᵥ w) 1 = (η ^ k)⁻¹ * yv f w 1 := by
  have hinv : ∀ w : Fin 2 → ℤ, yv f (γ₀⁻¹.val *ᵥ w) 0 = η⁻¹ * yv f w 0 ∧ yv f (γ₀⁻¹.val *ᵥ w) 1 = η * yv f w 1 := by
    intro w
    have h := h₀ (γ₀⁻¹.val *ᵥ w)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h
    constructor
    · rw [h.1]; field_simp
    · have := h.2
      rw [this]; field_simp
  induction k using Int.induction_on generalizing w with
  | zero => simp
  | succ i ih =>
    have e : ((γ₀ ^ ((i : ℤ) + 1)).val *ᵥ w) = (γ₀ ^ (i : ℤ)).val *ᵥ (γ₀.val *ᵥ w) := by
      rw [_root_.zpow_add_one, Units.val_mul, Matrix.mulVec_mulVec]
    rw [e, (ih _).1, (ih _).2, (h₀ w).1, (h₀ w).2, zpow_add_one₀ hη0]
    constructor
    · ring
    · rw [mul_inv]; ring
  | pred i ih =>
    have e : ((γ₀ ^ (-(i : ℤ) - 1)).val *ᵥ w) = (γ₀ ^ (-(i : ℤ))).val *ᵥ (γ₀⁻¹.val *ᵥ w) := by
      rw [_root_.zpow_sub_one, Units.val_mul, Matrix.mulVec_mulVec]
    rw [e, (ih _).1, (ih _).2, (hinv w).1, (hinv w).2, zpow_sub_one₀ hη0]
    constructor
    · ring
    · rw [mul_inv, inv_inv]; ring

/-- Helper: **existence in the fundamental domain.** For the primitive-or-not form $f$ with $D > 0$, $a \ne 0$ and every
vector $w \in \mathbb Z^2$ with $f(w) > 0$ (i.e. $L_1(w)L_2(w) > 0$) there is a proper automorph $\gamma$ with the
coordinates of $\gamma w$ in the sector `sectorCone η`. Arguments: `f` the form, `hD : 0 < disc f`, `ha : a ≠ 0`, `hη` the
fundamental unit, `w` the vector, `hpos` that $L_1(w)L_2(w) > 0$. -/
theorem sector_exists (f : BinQF) (hD : 0 < f.disc) (ha : f.a ≠ 0) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) (w : Fin 2 → ℤ) (hpos : 0 < yv f w 0 * yv f w 1) :
    ∃ γ ∈ AutSL f, yv f (γ.val *ᵥ w) ∈ sectorCone η := by
  obtain ⟨γ₀, hγ₀, h₀⟩ := exists_gen f hD ha hη
  have hη1 : 1 < η := hη.1
  have hη0 : 0 < η := by linarith
  have key : ∀ w' : Fin 2 → ℤ, 0 < yv f w' 0 → 0 < yv f w' 1 →
      ∃ γ ∈ AutSL f, yv f (γ.val *ᵥ w') ∈ sectorCone η := by
    intro w' hy0 hy1
    have hρ : 0 < yv f w' 0 / yv f w' 1 := div_pos hy0 hy1
    obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hρ (one_lt_pow₀ hη1 (two_ne_zero) : 1 < η ^ 2)
    have hq : 0 < η ^ n := zpow_pos hη0 n
    have hsq : (η ^ 2) ^ n = (η ^ n) ^ 2 := by
      rw [← zpow_natCast η 2, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    have hsq1 : (η ^ 2) ^ (n + 1) = (η ^ n) ^ 2 * η ^ 2 := by
      rw [zpow_add_one₀ (pow_ne_zero 2 hη0.ne'), hsq]
    rw [hsq] at hn1
    rw [hsq1] at hn2
    have hn1' : (η ^ n) ^ 2 * yv f w' 1 ≤ yv f w' 0 := (le_div_iff₀ hy1).mp hn1
    have hn2' : yv f w' 0 < (η ^ n) ^ 2 * η ^ 2 * yv f w' 1 := (div_lt_iff₀ hy1).mp hn2
    refine ⟨γ₀ ^ (-n), zpow_mem hγ₀ _, ?_⟩
    have hs := zpow_scale f hη0.ne' γ₀ h₀ (-n) w'
    rw [_root_.zpow_neg η n, inv_inv] at hs
    refine ⟨?_, ?_, ?_⟩
    · rw [hs.2]; positivity
    · rw [hs.1, hs.2, ← div_eq_inv_mul, le_div_iff₀ hq]
      nlinarith
    · rw [hs.1, hs.2, ← div_eq_inv_mul, div_lt_iff₀ hq]
      nlinarith
  obtain ⟨γm, hγm, hm⟩ : ∃ γ ∈ AutSL f, ∀ w : Fin 2 → ℤ, yv f (γ.val *ᵥ w) 0 = -yv f w 0 ∧
      yv f (γ.val *ᵥ w) 1 = -yv f w 1 := by
    have h : (-2 : ℤ) ^ 2 - (f.b ^ 2 - 4 * f.a * f.c) * (0 : ℤ) ^ 2 = 4 := by norm_num
    obtain ⟨γ, hγ, p, hp, hM⟩ := exists_autSL_of_pell f h
    refine ⟨γ, hγ, fun w => ?_⟩
    have := yv_aut f hD.le ha γ.val (-2) 0 (by rw [hM]; simp; linarith) (by rw [hM]; simp)
      (by rw [hM]; simp) (by rw [hM]; simp; linarith) w
    simpa using this
  rcases lt_or_gt_of_ne (show yv f w 0 ≠ 0 by rintro h; rw [h] at hpos; simp at hpos) with h0 | h0
  · have h1 : yv f w 1 < 0 := by
      by_contra hc
      push Not at hc
      nlinarith
    obtain ⟨γ, hγ, hγs⟩ := key (γm.val *ᵥ w) (by rw [(hm w).1]; linarith) (by rw [(hm w).2]; linarith)
    refine ⟨γ * γm, mul_mem hγ hγm, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact hγs
  · have h1 : 0 < yv f w 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    exact key w h0 h1

/-- Helper: **finiteness of the lattice points of the truncated sector.** For $D > 0$, $a \ne 0$, $\eta > 1$ and real
$c$, only finitely many $w \in \mathbb Z^2$ have $(L_1(w), L_2(w))$ in `sectorCone η` with $L_1(w)L_2(w) \le c$.
Arguments: `f` the form, `hD`, `ha`, `η`, `hη : 1 < η`, `c` the bound. -/
theorem finite_sector (f : BinQF) (hD : 0 < f.disc) (ha : f.a ≠ 0) {η : ℝ} (hη : 1 < η) (c : ℝ) :
    Set.Finite {w : Fin 2 → ℤ | yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ c} := by
  have ha' : (f.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hs0 : 0 < sD f := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hη2 : 1 ≤ η ^ 2 := by nlinarith
  set R : ℝ := η ^ 2 * (1 + |c|) with hR
  set K1 : ℝ := (|(f.a : ℝ)| + 1) * R / sD f with hK1
  set γc : ℝ := ((f.b : ℝ) + sD f) / (2 * f.a) with hγc
  set K : ℝ := R + |γc| * K1 + K1 with hK
  set m : ℤ := ⌈K⌉ with hm
  refine (Set.Finite.pi (t := fun _ : Fin 2 => Set.Icc (-m) m) (fun _ => Set.finite_Icc _ _)).subset ?_
  intro w hw
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hw
  simp only [hyp] at h4
  have hc1 : yv f w 1 ≤ 1 + |c| := by
    by_contra hcon
    push Not at hcon
    have : yv f w 1 * yv f w 1 ≤ c := by nlinarith [le_abs_self c]
    nlinarith [le_abs_self c]
  have hy1R : yv f w 1 ≤ R := by
    calc yv f w 1 ≤ 1 + |c| := hc1
      _ ≤ η ^ 2 * (1 + |c|) := by nlinarith [abs_nonneg c]
  have hy0R : yv f w 0 ≤ R := by
    have : yv f w 0 < η ^ 2 * (1 + |c|) := lt_of_lt_of_le h3 (by nlinarith)
    exact this.le
  have hw1 : sD f * (w 1 : ℝ) = f.a * yv f w 1 - yv f w 0 := by
    rw [yv_zero, yv_one]
    field_simp
    ring
  have hw1b : |(w 1 : ℝ)| ≤ K1 := by
    rw [hK1, le_div_iff₀ hs0]
    have : sD f * |(w 1 : ℝ)| = |(f.a : ℝ) * yv f w 1 - yv f w 0| := by
      rw [← hw1, abs_mul, abs_of_pos hs0]
    rw [mul_comm, this]
    calc |(f.a : ℝ) * yv f w 1 - yv f w 0| ≤ |(f.a : ℝ) * yv f w 1| + |yv f w 0| := abs_sub _ _
      _ = |(f.a : ℝ)| * yv f w 1 + yv f w 0 := by rw [abs_mul, abs_of_pos h1, abs_of_pos (show 0 < yv f w 0 by linarith)]
      _ ≤ (|(f.a : ℝ)| + 1) * R := by nlinarith [abs_nonneg (f.a : ℝ)]
  have hK10 : 0 ≤ K1 := le_trans (abs_nonneg _) hw1b
  have hw0 : (w 0 : ℝ) = yv f w 1 - γc * w 1 := by
    rw [yv_one]; ring
  have hw0b : |(w 0 : ℝ)| ≤ K := by
    rw [hw0]
    calc |yv f w 1 - γc * w 1| ≤ |yv f w 1| + |γc * w 1| := abs_sub _ _
      _ = yv f w 1 + |γc| * |(w 1 : ℝ)| := by rw [abs_of_pos h1, abs_mul]
      _ ≤ R + |γc| * K1 := by gcongr
      _ ≤ K := by rw [hK]; linarith
  have hw1c : |(w 1 : ℝ)| ≤ K := by
    refine hw1b.trans ?_
    rw [hK]
    have := mul_nonneg (abs_nonneg γc) hK10
    have : 0 ≤ R := by positivity
    linarith
  have hKm : K ≤ m := Int.le_ceil _
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  fin_cases i
  · have h := (abs_le.mp (hw0b.trans hKm))
    show -m ≤ w 0 ∧ w 0 ≤ m
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · have h := (abs_le.mp (hw1c.trans hKm))
    show -m ≤ w 1 ∧ w 1 ≤ m
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

end Domain

section Orbits2

open Lemma21Aux

/-- Helper: **$L_1(w)L_2(w) = F(w)$ with $F$ the integer value** (`Fint`), for $D \ge 0$, $a \ne 0$. -/
theorem hyp_yv (f : BinQF) (hD : 0 ≤ f.disc) (ha : f.a ≠ 0) (w : Fin 2 → ℤ) :
    hyp (yv f w) = ((Fint f.a f.b f.c w : ℤ) : ℝ) := by
  rw [hyp, yv_mul f hD ha, eval_eq_Fint]

/-- Helper: a vector whose coordinates lie in the sector has $F(w) > 0$. -/
theorem Fint_pos_of_cone (f : BinQF) (hD : 0 ≤ f.disc) (ha : f.a ≠ 0) {η : ℝ} {w : Fin 2 → ℤ}
    (h : yv f w ∈ sectorCone η) : 0 < Fint f.a f.b f.c w := by
  obtain ⟨h1, h2, -⟩ := h
  have : 0 < hyp (yv f w) := by
    rw [hyp]; exact mul_pos (lt_of_lt_of_le h1 h2) h1
  rw [hyp_yv f hD ha] at this
  exact_mod_cast this

/-- Helper: **$a^*_f(m)$ is the number of lattice points of the sector with $f = m$** (Cassels' fundamental domain for
the proper automorphs $\pm\eta^k$). Arguments: `f` the form, `hprim`, `ha`, `hD`, `hη` as in `sector_unique`, `m` the
integer, `hm : 0 < m`. -/
theorem repOrbitCount_eq (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) (hD : 0 < f.disc) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) (m : ℕ) (hm : 0 < m) :
    repOrbitCount f m = Nat.card {w : Fin 2 → ℤ // f.eval (w 0) (w 1) = m ∧ yv f w ∈ sectorCone η} := by
  unfold repOrbitCount
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun w : {w : Fin 2 → ℤ // f.eval (w 0) (w 1) = m ∧ yv f w ∈ sectorCone η} =>
      (Quotient.mk _ (⟨w.1, w.2.1⟩ : repVecs f m) :
        Quotient ((autOrbitSetoid f).comap (Subtype.val : repVecs f m → Fin 2 → ℤ)))) ⟨?_, ?_⟩)
  · intro w w' h
    obtain ⟨γ, hγ, e⟩ := Quotient.exact h
    have := sector_unique f hprim ha hD hη hγ w.2.2 (by rw [e]; exact w'.2.2)
    exact Subtype.ext (this.symm.trans e)
  · intro q
    induction q using Quotient.inductionOn with
    | h v =>
      obtain ⟨v, hv⟩ := v
      have hv' : f.eval (v 0) (v 1) = m := hv
      have hpos : 0 < yv f v 0 * yv f v 1 := by
        rw [yv_mul f hD.le ha, hv']
        exact_mod_cast hm
      obtain ⟨γ, hγ, hcone⟩ := sector_exists f hD ha hη v hpos
      refine ⟨⟨γ.val *ᵥ v, ?_, hcone⟩, ?_⟩
      · rw [Lemma21Aux.eval_mulVec_aut f hγ, hv']
      · exact Quotient.sound ((autOrbitSetoid f).iseqv.symm ⟨γ, hγ, rfl⟩)

/-- Helper: **$A^*_f(M)$ is the number of lattice points of the truncated sector satisfying the congruence conditions**
(Cassels, proof of Lemma 2.1): $A^*_f(M) = \#\{w \in \mathbb Z^2 : (L_1, L_2)(w) \in \text{sector},\ f(w) \le M,\
p \nmid f(w)\ \forall p \mid D\}$. Arguments as for `repOrbitCount_eq`, `M` the bound. -/
theorem orbitCountSum_eq (f : BinQF) (hprim : f.IsPrimitive) (ha : f.a ≠ 0) (hD : 0 < f.disc) {η : ℝ}
    (hη : IsNormOneFundamentalUnit f.disc η) (M : ℕ) :
    orbitCountSum f M = Nat.card {w : Fin 2 → ℤ // yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧
      ∀ p ∈ f.disc.natAbs.primeFactors, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w} := by
  classical
  have hN0 : f.disc.natAbs ≠ 0 := by omega
  have hfin := finite_sector f hD ha hη.1 (M : ℝ)
  set S : Set (Fin 2 → ℤ) := {w | yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧
      ∀ p ∈ f.disc.natAbs.primeFactors, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w} with hS
  have hSfin : S.Finite := hfin.subset (fun w hw => ⟨hw.1, hw.2.1⟩)
  have h1 : Nat.card {w : Fin 2 → ℤ // yv f w ∈ sectorCone η ∧ hyp (yv f w) ≤ (M : ℝ) ∧
      ∀ p ∈ f.disc.natAbs.primeFactors, ¬ (p : ℤ) ∣ Fint f.a f.b f.c w} = hSfin.toFinset.card := by
    show Nat.card ↥S = _
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card S hSfin]
  rw [h1]
  unfold orbitCountSum
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w => (Fint f.a f.b f.c w).toNat)
    (t := (Finset.Icc 1 M).filter (fun m => Nat.Coprime m f.disc.natAbs))]
  · refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hmM⟩, hmcop⟩ := hm
    rw [repOrbitCount_eq f hprim ha hD hη m hm1, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun w => ?_))
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, hS, Set.mem_ofPred_eq]
    rw [eval_eq_Fint]
    constructor
    · rintro ⟨hw, hc⟩
      refine ⟨⟨hc, ?_, ?_⟩, by omega⟩
      · rw [hyp_yv f hD.le ha, hw]; exact_mod_cast hmM
      · intro p hp hpv
        rw [hw] at hpv
        exact (coprime_iff_noPrime m _ hN0).mp hmcop p hp (by exact_mod_cast hpv)
    · rintro ⟨⟨hc, -, -⟩, ht⟩
      have := Fint_pos_of_cone f hD.le ha hc
      exact ⟨by omega, hc⟩
  · intro w hw
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, hS, Set.mem_ofPred_eq] at hw
    obtain ⟨hc, hM, hg⟩ := hw
    have hpos := Fint_pos_of_cone f hD.le ha hc
    rw [hyp_yv f hD.le ha] at hM
    have hM' : Fint f.a f.b f.c w ≤ M := by exact_mod_cast hM
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [coprime_iff_noPrime _ _ hN0]
    intro p hp hpm
    apply hg p hp
    have : Fint f.a f.b f.c w = ((Fint f.a f.b f.c w).toNat : ℤ) := (Int.toNat_of_nonneg hpos.le).symm
    rw [this]
    exact_mod_cast hpm

end Orbits2

end Lemma21Pos530

end QuadFormsKB.Cassels
