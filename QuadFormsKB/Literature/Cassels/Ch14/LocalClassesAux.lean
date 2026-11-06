/-
# Cassels, Chapter 14, §3: auxiliary lemmas on binary forms over $\mathbb Z_p$

Helpers for `LocalClasses.lean`: the form `bq a b c` $= a x^2 + b xy + c y^2$ over a commutative ring, equivalences
by explicit matrices, and the reduction of a primitive $\mathbb Z_p$-form to a diagonal form $u x^2 + e y^2$.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Existence

namespace QuadFormsKB.Composition

open QuadForm Siegel

section Basic

variable {R : Type*} [CommRing R]

/-- The binary form $a x^2 + b xy + c y^2$. -/
def bq (a b c : R) : QuadForm R 2 := QuadForm.ofUpper ![![a, b], ![0, c]]

theorem bq_eval (a b c s t : R) : (bq a b c).eval ![s, t] = a * s ^ 2 + b * s * t + c * t ^ 2 := by
  rw [eval_two]; simp [bq, QuadForm.ofUpper]

theorem bq_coeff00 (a b c : R) : (bq a b c).coeff 0 0 = a := by simp [bq, QuadForm.ofUpper]
theorem bq_coeff01 (a b c : R) : (bq a b c).coeff 0 1 = b := by simp [bq, QuadForm.ofUpper]
theorem bq_coeff11 (a b c : R) : (bq a b c).coeff 1 1 = c := by simp [bq, QuadForm.ofUpper]

/-- $-\det H = b^2 - 4ac$ for `bq a b c`. -/
theorem neg_det_bq (a b c : R) : -(bq a b c).hessian.det = b ^ 2 - 4 * a * c := by
  rw [Binary.hessian_det_two, bq_coeff00, bq_coeff01, bq_coeff11]; ring

/-- The discriminant $b^2 - 4ac$ of a binary form. -/
def disc2 (F : QuadForm R 2) : R := F.coeff 0 1 ^ 2 - 4 * F.coeff 0 0 * F.coeff 1 1

theorem neg_det_eq_disc2 (F : QuadForm R 2) : -F.hessian.det = disc2 F := by
  rw [Binary.hessian_det_two, disc2]; ring

omit [CommRing R] in
theorem vec_eta (x : Fin 2 → R) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

theorem mulVec_two (a b c d s t : R) :
    Matrix.mulVec (Matrix.of ![![a, b], ![c, d]]) ![s, t] = ![a * s + b * t, c * s + d * t] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Equivalence by an explicit matrix with unit determinant. -/
theorem isometricGL_of_matrix (F G : QuadForm R 2) (a b c d : R) (hM : IsUnit (a * d - b * c))
    (h : ∀ s t : R, F.eval ![a * s + b * t, c * s + d * t] = G.eval ![s, t]) : IsometricGL F G := by
  have hdet : IsUnit (Matrix.of ![![a, b], ![c, d]]).det := by
    rw [Matrix.det_fin_two_of]; exact hM
  refine ⟨Matrix.nonsingInvUnit _ hdet, fun x => ?_⟩
  rw [vec_eta x]
  have : ((Matrix.nonsingInvUnit _ hdet : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      Matrix.of ![![a, b], ![c, d]] := rfl
  rw [this, mulVec_two, h]

/-- The change of variables $x \mapsto x + k y$. -/
theorem isometricGL_shear (w b c k : R) :
    IsometricGL (bq w b c) (bq w (b + 2 * w * k) (w * k ^ 2 + b * k + c)) := by
  refine isometricGL_of_matrix _ _ 1 k 0 1 (by simp) fun s t => ?_
  rw [bq_eval, bq_eval]; ring

/-- Rescaling the variables by units $z, \delta$ (diagonal case). -/
theorem isometricGL_scale (u e z δ : R) (hz : IsUnit z) (hδ : IsUnit δ) :
    IsometricGL (bq u 0 e) (bq (u * z ^ 2) 0 (e * δ ^ 2)) := by
  refine isometricGL_of_matrix _ _ z 0 0 δ (by simpa using hz.mul hδ) fun s t => ?_
  rw [bq_eval, bq_eval]; ring

/-- Swapping the variables. -/
theorem isometricGL_swap (a b c : R) : IsometricGL (bq a b c) (bq c b a) := by
  refine isometricGL_of_matrix _ _ 0 1 1 0 (by simp) fun s t => ?_
  rw [bq_eval, bq_eval]; ring

end Basic

section Local

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **Completing a unit value to a basis.** If a binary form $F$ takes a unit value $w$ at $v$, then $F$ is
$\mathrm{SL}_2$-equivalent to $w x^2 + b' xy + c' y^2$, with the same discriminant. -/
theorem exists_first {F : QuadForm R 2} {v : Fin 2 → R} (hv : IsUnit (F.eval v)) :
    ∃ b' c' : R, b' ^ 2 - 4 * F.eval v * c' = disc2 F ∧ IsometricGL F (bq (F.eval v) b' c') := by
  obtain ⟨x, y, rfl⟩ : ∃ x y : R, v = ![x, y] := ⟨v 0, v 1, vec_eta v⟩
  set a := F.coeff 0 0
  set b := F.coeff 0 1
  set c := F.coeff 1 1
  have hw : F.eval ![x, y] = a * x ^ 2 + b * x * y + c * y ^ 2 := by rw [eval_two]
  rw [hw] at hv ⊢
  by_cases hx : IsUnit x
  · obtain ⟨xi, hxi⟩ := hx.exists_right_inv
    refine ⟨b + 2 * c * y * xi, c * xi ^ 2, ?_, ?_⟩
    · rw [disc2]; linear_combination (-4 * a * c * (x * xi + 1) - 4 * b * c * y * xi) * hxi
    · refine isometricGL_of_matrix _ _ x 0 y xi (by simp [hxi]) fun s t => ?_
      rw [eval_two, bq_eval]
      linear_combination (b * s * t) * hxi
  · have hy : IsUnit y := by
      by_contra hy
      have hxm : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hx
      have hym : y ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hy
      have hmem : a * x ^ 2 + b * x * y + c * y ^ 2 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hxm 2 (by norm_num)))
          (Ideal.mul_mem_left _ _ hym)) (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hym 2 (by norm_num)))
      exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hv
    obtain ⟨yi, hyi⟩ := hy.exists_right_inv
    refine ⟨-2 * a * x * yi - b, a * yi ^ 2, ?_, ?_⟩
    · rw [disc2]
      linear_combination (-(4 * a * b * x * yi + 4 * a * c * (1 + y * yi))) * hyi
    · refine isometricGL_of_matrix _ _ x (-yi) y 0 (by simp [mul_comm, hyi]) fun s t => ?_
      rw [eval_two, bq_eval]
      linear_combination (-(b * s * t)) * hyi

/-- **Normal form from a unit value.** If a binary form $F$ of discriminant $D$ takes a unit value $w$ and the
middle coefficient of every form of discriminant $D$ with unit leading coefficient is divisible by $2$, then
$F \sim_{\mathrm{GL}_2} w x^2 + e y^2$ with $-4 w e = D$. -/
theorem exists_diag_of_unit_value {F : QuadForm R 2} {v : Fin 2 → R} (hv : IsUnit (F.eval v)) {D : R}
    (hD : disc2 F = D) (hhalf : ∀ b' c' w : R, IsUnit w → b' ^ 2 - 4 * w * c' = D → ∃ β, b' = 2 * β) :
    ∃ e : R, -4 * F.eval v * e = D ∧ IsometricGL F (bq (F.eval v) 0 e) := by
  obtain ⟨b', c', hdisc, hiso⟩ := exists_first hv
  rw [hD] at hdisc
  obtain ⟨β, rfl⟩ := hhalf b' c' _ hv hdisc
  obtain ⟨wi, hwi⟩ := hv.exists_right_inv
  set w := F.eval v
  have h0 : 2 * β + 2 * w * (-β * wi) = 0 := by linear_combination (-2 * β) * hwi
  refine ⟨w * (-β * wi) ^ 2 + 2 * β * (-β * wi) + c', ?_, ?_⟩
  · linear_combination (-(2 * β + 2 * w * (-β * wi))) * h0 + hdisc
  · have := hiso.trans (isometricGL_shear w (2 * β) c' (-β * wi))
    rwa [h0] at this

omit [IsLocalRing R] in
/-- In a domain where $2$ is prime and divides $D$, a form of discriminant $D$ has even middle coefficient. -/
theorem half_of_two_dvd {D : R} (h2 : Prime (2 : R)) (hD : (2 : R) ∣ D) :
    ∀ b' c' w : R, IsUnit w → b' ^ 2 - 4 * w * c' = D → ∃ β, b' = 2 * β := by
  intro b' c' w _ h
  have : (2 : R) ∣ b' ^ 2 := by
    have e : b' ^ 2 = D + 4 * w * c' := by linear_combination h
    rw [e]; exact dvd_add hD ⟨2 * w * c', by ring⟩
  exact h2.dvd_of_dvd_pow this

omit [IsLocalRing R] in
/-- If $2$ is a unit, every middle coefficient is even. -/
theorem half_of_isUnit_two (h2 : IsUnit (2 : R)) (D : R) :
    ∀ b' c' w : R, IsUnit w → b' ^ 2 - 4 * w * c' = D → ∃ β, b' = 2 * β := by
  intro b' _ _ _ _
  obtain ⟨i, hi⟩ := h2.exists_right_inv
  exact ⟨b' * i, by linear_combination (-b') * hi⟩

end Local

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem four_ne_zero_padic : (4 : ℤ_[p]) ≠ 0 := by norm_num

/-- For $p$ odd, $2$ is a unit of $\mathbb Z_p$. -/
theorem isUnit_two_padic (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) :=
  Kneser.isUnit_of_toZMod_ne_zero (Kneser.toZMod_two_ne_zero hp2)

/-- **Equivalence of diagonal forms from a represented unit.** If $u x^2 + e y^2 = u'$ is a unit and both forms
have the same discriminant $D$ (with $2$ dividing middle coefficients as in `exists_diag_of_unit_value`), then
$u x^2 + e y^2 \sim u' x^2 + e' y^2$. -/
theorem diag_equiv_of_rep {D : ℤ_[p]}
    (hhalf : ∀ b' c' w : ℤ_[p], IsUnit w → b' ^ 2 - 4 * w * c' = D → ∃ β, b' = 2 * β)
    {u e u' e' s t : ℤ_[p]} (hu' : IsUnit u') (hD : -4 * u * e = D) (hD' : -4 * u' * e' = D)
    (hst : u * s ^ 2 + e * t ^ 2 = u') : IsometricGL (bq u 0 e) (bq u' 0 e') := by
  have hev : (bq u 0 e).eval ![s, t] = u' := by rw [bq_eval]; rw [← hst]; ring
  have hdisc : disc2 (bq u 0 e) = D := by
    rw [disc2, bq_coeff00, bq_coeff01, bq_coeff11, ← hD]; ring
  obtain ⟨e'', h1, h2⟩ := exists_diag_of_unit_value (v := ![s, t]) (hev ▸ hu') hdisc hhalf
  rw [hev] at h1 h2
  have : e'' = e' := by
    have hne : (-4 * u' : ℤ_[p]) ≠ 0 := mul_ne_zero (by simp) hu'.ne_zero
    exact mul_left_cancel₀ hne (by linear_combination h1 - hD')
  rwa [this] at h2

/-- **Lemma 3.1 (i), the key step:** for $p$ odd and $D$ a unit, all diagonal forms $u x^2 + e y^2$ with
$-4ue = D$, $u$ a unit, are equivalent. -/
theorem odd_equiv_of_isUnit (hp2 : p ≠ 2) {D : ℤ_[p]} (hD : IsUnit D) {u e u' e' : ℤ_[p]}
    (hu : IsUnit u) (hu' : IsUnit u') (h : -4 * u * e = D) (h' : -4 * u' * e' = D) :
    IsometricGL (bq u 0 e) (bq u' 0 e') := by
  have hhalf := half_of_isUnit_two (isUnit_two_padic hp2) D
  obtain ⟨i4, hi4⟩ := (show IsUnit (4 : ℤ_[p]) by
    simpa [show (4 : ℤ_[p]) = 2 * 2 by norm_num] using (isUnit_two_padic hp2).mul (isUnit_two_padic hp2)).exists_right_inv
  have hc : ∀ {u e : ℤ_[p]}, IsUnit u → -4 * u * e = D → IsometricGL (bq u 0 e) (bq 1 0 (-D * i4)) := by
    intro u e hu h
    have he : IsUnit e := by
      have : IsUnit (-4 * u * e) := h ▸ hD
      exact (isUnit_of_mul_isUnit_right this)
    obtain ⟨x, y, hxy⟩ := Kneser.exists_binary_one hp2 hu he
    exact diag_equiv_of_rep hhalf isUnit_one h (by linear_combination (D) * hi4) hxy
  exact (hc hu h).trans (hc hu' h').symm

/-- **Lemma 3.1 (ii), the key step:** for $p$ odd with $p \mid D$, diagonal forms $u x^2 + e y^2$ and
$u' x^2 + e' y^2$ ($u, u'$ units, $-4ue = -4u'e' = D$) are equivalent iff $u'/u$ is a square. -/
theorem odd_equiv_iff (hp2 : p ≠ 2) {D : ℤ_[p]} (hpD : (p : ℤ_[p]) ∣ D) {u e u' e' : ℤ_[p]}
    (hu : IsUnit u) (hu' : IsUnit u') (h : -4 * u * e = D) (h' : -4 * u' * e' = D) :
    IsometricGL (bq u 0 e) (bq u' 0 e') ↔ ∃ z : ℤ_[p], u' = u * z ^ 2 := by
  have hne : (-4 * u : ℤ_[p]) ≠ 0 := mul_ne_zero (by simp) hu.ne_zero
  constructor
  · rintro ⟨g, hg⟩
    have h1 := hg ![1, 0]
    have hv : Matrix.mulVec g.val ![1, 0] = ![g.val 0 0, g.val 1 0] := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [hv, bq_eval, bq_eval] at h1
    set s := g.val 0 0
    set t := g.val 1 0
    have h1' : u * s ^ 2 + e * t ^ 2 = u' := by linear_combination h1
    have hD0 : PadicInt.toZMod D = 0 := by
      obtain ⟨c, hc⟩ := hpD
      rw [hc, map_mul, Kneser.toZMod_natCast_self, zero_mul]
    have hu0 := Kneser.toZMod_ne_zero_of_isUnit hu
    have hu0' := Kneser.toZMod_ne_zero_of_isUnit hu'
    have h2 : (2 : ZMod p) ≠ 0 := by have := Kneser.toZMod_two_ne_zero hp2; rwa [map_ofNat] at this
    have he0 : PadicInt.toZMod e = 0 := by
      have := congrArg PadicInt.toZMod h
      rw [hD0] at this
      simp only [map_mul, map_neg, map_ofNat] at this
      have h4 : (4 : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd (neg_eq_zero.mp h) h4
        · exact absurd h hu0
      · exact h
    have h3 := congrArg PadicInt.toZMod h1'
    simp only [map_add, map_mul, map_pow, he0, zero_mul] at h3
    have hs0 : PadicInt.toZMod s ≠ 0 := by
      intro hs
      rw [hs] at h3
      simp at h3
      exact hu0' h3.symm
    obtain ⟨ui, hui⟩ := hu.exists_right_inv
    have hui' : PadicInt.toZMod u * PadicInt.toZMod ui = 1 := by rw [← map_mul, hui, map_one]
    obtain ⟨z, hz⟩ := Kneser.exists_sq_eq_of_toZMod hp2 (u' * ui) hs0
      (by rw [map_mul, ← h3]; linear_combination (PadicInt.toZMod s ^ 2) * hui')
    exact ⟨z, by linear_combination (-u') * hui - u * hz⟩ 
  · rintro ⟨z, hz⟩
    have hzu : IsUnit z := by
      have : IsUnit (u * z ^ 2) := hz ▸ hu'
      exact (isUnit_pow_iff (two_ne_zero)).mp (isUnit_of_mul_isUnit_right this)
    obtain ⟨zi, hzi⟩ := hzu.exists_right_inv
    have hee : e = z ^ 2 * e' := mul_left_cancel₀ hne (by linear_combination h - h' + (-4 * e') * hz)
    have hzi' : IsUnit zi := ⟨⟨zi, z, by rw [mul_comm]; exact hzi, hzi⟩, rfl⟩
    have := isometricGL_scale u e z zi hzu hzi'
    have hee' : e * zi ^ 2 = e' := by
      rw [hee]; linear_combination (e' * (z * zi + 1) * zi * 0 + e' * (z * zi + 1)) * hzi
    rwa [hee', ← hz] at this

/-- For $p$ odd, $-4ue = D$ is solvable for a unit $u$. -/
theorem exists_e_of_odd (hp2 : p ≠ 2) (D : ℤ_[p]) {u : ℤ_[p]} (hu : IsUnit u) : ∃ e : ℤ_[p], -4 * u * e = D := by
  obtain ⟨i4, hi4⟩ := (show IsUnit (4 : ℤ_[p]) by
    simpa [show (4 : ℤ_[p]) = 2 * 2 by norm_num] using (isUnit_two_padic hp2).mul (isUnit_two_padic hp2)).exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  exact ⟨-D * i4 * ui, by linear_combination (D * u * ui) * hi4 + D * hui⟩

/-- Two nonsquares of a finite field of odd characteristic differ by a square. -/
theorem exists_sq_of_nonsquares {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : ∃ s : F, a = b * s ^ 2 := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have hab : quadraticChar F (a * b) = 1 := by
    rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
    norm_num
  obtain ⟨s, hs⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).mp hab
  refine ⟨s * b⁻¹, ?_⟩
  field_simp
  linear_combination hs

/-- A unit of $\mathbb Z_p$ ($p$ odd) is a square times $1$ or times a fixed unit non-residue $r$. -/
theorem sq_class_two (hp2 : p ≠ 2) {r : ℤ_[p]} (hr : ¬ IsSquare (PadicInt.toZMod r)) {u : ℤ_[p]} (hu : IsUnit u) :
    (∃ z : ℤ_[p], u = 1 * z ^ 2) ∨ ∃ z : ℤ_[p], u = r * z ^ 2 := by
  have hu0 := Kneser.toZMod_ne_zero_of_isUnit hu
  have hr0 : PadicInt.toZMod r ≠ 0 := fun h => hr (h ▸ IsSquare.zero)
  have hrU : IsUnit r := Kneser.isUnit_of_toZMod_ne_zero hr0
  by_cases hsq : IsSquare (PadicInt.toZMod u)
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := fun h => hu0 (by rw [hs, h, mul_zero])
    obtain ⟨z, hz⟩ := Kneser.exists_sq_eq_of_toZMod hp2 u hs0 (by rw [hs]; ring)
    exact Or.inl ⟨z, by rw [hz]; ring⟩
  · have hF : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]; exact hp2
    obtain ⟨s, hs⟩ := exists_sq_of_nonsquares hF hsq hr
    have hs0 : s ≠ 0 := fun h => hu0 (by rw [hs, h]; ring)
    obtain ⟨ri, hri⟩ := hrU.exists_right_inv
    have hri' : PadicInt.toZMod r * PadicInt.toZMod ri = 1 := by rw [← map_mul, hri, map_one]
    obtain ⟨z, hz⟩ := Kneser.exists_sq_eq_of_toZMod hp2 (u * ri) hs0
      (by rw [map_mul, hs]; linear_combination (s ^ 2) * hri')
    exact Or.inr ⟨z, by linear_combination (-u) * hri - r * hz⟩

/-- A unit non-residue lifted to $\mathbb Z_p$ ($p$ odd). -/
theorem exists_nonresidue (hp2 : p ≠ 2) : ∃ r : ℤ_[p], ¬ IsSquare (PadicInt.toZMod r) := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  refine ⟨(a.val : ℤ_[p]), ?_⟩
  simpa using ha

end Padic

end QuadFormsKB.Composition
