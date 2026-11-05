/-
# Hanke 2011, §2: binary even unimodular matrices over a dyadic local ring (for Sublemma 2.7)

Let $R$ be a discrete valuation ring that is Henselian with finite residue field, in which $2$ is not a unit and $2 \ne 0$
(a dyadic local ring of characteristic $0$, e.g. the integers of a completion of a number field at a prime over $2$).
A *binary even unimodular* matrix is $H = \begin{pmatrix} 2a & b\\ b & 2c\end{pmatrix}$ with $\det H = 4ac - b^2$ a
unit, the Hessian matrix of $a x^2 + b x y + c y^2$.

**Proves** (all unconditional)
* `hensel_lin`: a quadratic $A s^2 + B s + C$ with $B$ a unit and $C \in \mathfrak p$ has a root in $R$;
* `exists_represents_unit`: a binary form $a x^2 + b x y + c y^2$ with $b$ a unit represents every unit of $R$
  (so, with `cong_P`, every binary even unimodular matrix is congruent to $\begin{pmatrix} 2 & 1\\ 1 & 2t\end{pmatrix}$,
  the Hessian matrix of $x^2 + xy + ty^2$);
* `cong_P_of_det`: the matrices for $t$ and $t'$ are congruent when $1 - 4t' = u^2(1 - 4t)$ with $u$ a unit (the
  two forms are $\mathcal O$-isometric, by an explicit change of variables, using that $u \equiv 1 \bmod 2$ for such $u$);
* `cong_binary`: two binary even unimodular matrices whose determinants differ by a unit square are congruent
  (the $n = 2$ case of Hanke 2011, Sublemma 2.7, as a statement about Hessian matrices).
-/
import QuadFormsKB.Literature.Hanke2011Structure.DyadicCong
import QuadFormsKB.Literature.OMeara.Sec93D3

open Matrix IsLocalRing

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Hanke2011Structure.Dyadic

section Hensel

variable {R : Type*} [CommRing R] [HenselianLocalRing R]

/-- **Hensel's lemma for a quadratic with a unit linear term:** $A s^2 + B s + C = 0$ has a root in $R$ if $B$ is a
unit and $C \in \mathfrak p$. (The root is $s = C/z$ for the root $z \equiv -B$ of the monic polynomial
$z^2 + Bz + AC$; the usual `hensel_quad` needs a unit leading coefficient.) -/
theorem hensel_lin {A B C : R} (hB : IsUnit B) (hC : C ∈ maximalIdeal R) :
    ∃ s : R, A * s ^ 2 + B * s + C = 0 := by
  have h2 : (-B) ^ 2 + B * (-B) + A * C ∈ maximalIdeal R := by
    have : (-B) ^ 2 + B * (-B) + A * C = A * C := by ring
    rw [this]; exact Ideal.mul_mem_left _ _ hC
  have hd : IsUnit (2 * 1 * (-B) + B) := by
    have : 2 * 1 * (-B) + B = -B := by ring
    rw [this]; exact hB.neg
  obtain ⟨z, hz, hzz⟩ := QuadFormsKB.OMeara.D93.hensel_quad (a := (1 : R)) (b := B) (c := A * C) (r₀ := -B)
    isUnit_one (by simpa using h2) hd
  have hzu : IsUnit z := by
    by_contra hz'
    have hzm : z ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal z).2 hz'
    have : -B ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hzm hzz
      simpa using this
    exact ((IsLocalRing.mem_maximalIdeal _).1 this) hB.neg
  obtain ⟨w, hw⟩ := hzu.exists_right_inv
  refine ⟨C * w, ?_⟩
  linear_combination (C * w ^ 2) * hz + (-(B * C * w + C * (1 + w * z))) * hw

end Hensel

section Represent

variable {R : Type*} [CommRing R] [IsDomain R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- In a local ring with finite residue field in which $2 \in \mathfrak p$ (residue characteristic $2$), every
element is a square modulo $\mathfrak p$ (the Frobenius of a finite field is surjective). -/
theorem exists_sq_sub_mem (h2 : (2 : R) ∈ maximalIdeal R) (z : R) : ∃ x : R, z - x ^ 2 ∈ maximalIdeal R := by
  have h2k : (residue R 2 : ResidueField R) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 h2
  have h2k' : (2 : ResidueField R) = 0 := by rw [← map_ofNat (residue R) 2]; exact h2k
  have hinj : Function.Injective (fun x : ResidueField R => x ^ 2) := by
    intro x y hxy
    have h1 : (x - y) ^ 2 = 0 := by
      simp only at hxy
      linear_combination hxy + (y ^ 2 - x * y) * h2k'
    exact sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h1)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) (residue R z)
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨x, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow]
  simp only at hy
  rw [hy, sub_self]

/-- **Representing a unit, with a unit leading coefficient:** if $a$, $b$ are units then $a x^2 + b x y + c y^2$
represents every unit $T$. (Take $x_0$ with $a x_0^2 \equiv T$, then solve for $y$ by `hensel_lin`.) -/
theorem rep_aux (h2 : (2 : R) ∈ maximalIdeal R) {a b c T : R} (ha : IsUnit a) (hb : IsUnit b)
    (hT : IsUnit T) : ∃ x y : R, a * x ^ 2 + b * x * y + c * y ^ 2 = T := by
  obtain ⟨a', ha'⟩ := ha.exists_right_inv
  obtain ⟨x0, hx0⟩ := exists_sq_sub_mem h2 (T * a')
  have hax : a * x0 ^ 2 - T ∈ maximalIdeal R := by
    have : a * x0 ^ 2 - T = -(a * (T * a' - x0 ^ 2)) := by linear_combination T * ha'
    rw [this]; exact Ideal.neg_mem_iff _ |>.2 (Ideal.mul_mem_left _ _ hx0)
  have hx0u : IsUnit x0 := by
    by_contra hu
    have hm : x0 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x0).2 hu
    have : T ∈ maximalIdeal R := by
      have h1 : a * x0 ^ 2 ∈ maximalIdeal R :=
        Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 (by norm_num))
      have := Ideal.sub_mem _ h1 hax
      simpa using this
    exact ((IsLocalRing.mem_maximalIdeal _).1 this) hT
  obtain ⟨y, hy⟩ := hensel_lin (A := c) (B := b * x0) (C := a * x0 ^ 2 - T) (hb.mul hx0u) hax
  exact ⟨x0, y, by linear_combination hy⟩

/-- **A binary form with a unit cross coefficient represents every unit** (in a Henselian local ring with finite
residue field of characteristic $2$): for $b$ a unit and $T$ a unit, $a x^2 + b x y + c y^2 = T$ is solvable. -/
theorem exists_represents_unit (h2 : (2 : R) ∈ maximalIdeal R) {a b c T : R} (hb : IsUnit b) (hT : IsUnit T) :
    ∃ x y : R, a * x ^ 2 + b * x * y + c * y ^ 2 = T := by
  by_cases hc : IsUnit c
  · obtain ⟨u, v, h⟩ := rep_aux h2 (a := c) (b := b) (c := a) hc hb hT
    exact ⟨v, u, by linear_combination h⟩
  · have hcm : c ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal c).2 hc
    obtain ⟨b', hb'⟩ := hb.exists_right_inv
    set y0 := (T - a) * b' with hy0
    have hB : IsUnit (b + 2 * c * y0) := by
      by_contra hu
      have hm : b + 2 * c * y0 ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hu
      have h22 : 2 * c * y0 ∈ maximalIdeal R :=
        Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2)
      have : b ∈ maximalIdeal R := by
        have := Ideal.sub_mem _ hm h22
        simpa using this
      exact ((IsLocalRing.mem_maximalIdeal _).1 this) hb
    obtain ⟨s, hs⟩ := hensel_lin (A := c) (B := b + 2 * c * y0) (C := c * y0 ^ 2) hB
      (Ideal.mul_mem_right _ _ hcm)
    refine ⟨1, y0 + s, ?_⟩
    have hby : b * y0 = T - a := by
      rw [hy0]; linear_combination (T - a) * hb'
    linear_combination hs + hby

end Represent

section Normalize

variable {R : Type*} [CommRing R] [IsDomain R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- A unit plus an element of the maximal ideal is a unit. -/
theorem isUnit_add_of_mem {u z : R} (hu : IsUnit u) (hz : z ∈ maximalIdeal R) : IsUnit (u + z) := by
  by_contra h
  have hm : u + z ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have : u ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hm hz
  exact ((IsLocalRing.mem_maximalIdeal _).1 this) hu

/-- If $4c - \beta^2$ is a unit (and $2 \in \mathfrak p$) then $\beta$ is a unit. -/
theorem isUnit_of_isUnit_four_sub_sq (h2 : (2 : R) ∈ maximalIdeal R) {β c : R}
    (h : IsUnit (4 * c - β ^ 2)) : IsUnit β := by
  by_contra hβ
  have hm : β ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hβ
  have h4 : (4 : R) * c ∈ maximalIdeal R := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2)
  have : 4 * c - β ^ 2 ∈ maximalIdeal R :=
    Ideal.sub_mem _ h4 (Ideal.pow_mem_of_mem _ hm 2 (by norm_num))
  exact ((IsLocalRing.mem_maximalIdeal _).1 this) h

/-- Scaling the second basis vector: $\begin{pmatrix} 2 & \beta\\ \beta & 2c\end{pmatrix}$ is congruent to
$\begin{pmatrix} 2 & 1\\ 1 & 2c\beta'^2\end{pmatrix}$ when $\beta\beta' = 1$. -/
theorem cong_scale {β β' c : R} (h : β * β' = 1) :
    Cong (!![2, β; β, 2 * c] : Matrix (Fin 2) (Fin 2) R) (!![2, 1; 1, 2 * (c * β' ^ 2)]) := by
  have hU : IsUnit (!![1, 0; 0, β'] : Matrix (Fin 2) (Fin 2) R).det := by
    rw [Matrix.det_fin_two_of]
    simpa using (Units.mk β' β (by rw [mul_comm]; exact h) h).isUnit
  have := cong_of_isUnit_det (!![2, β; β, 2 * c] : Matrix (Fin 2) (Fin 2) R) _ hU
  convert this using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h | linear_combination (-1 : R) * h

/-- **Every binary even unimodular matrix is congruent to $\begin{pmatrix} 2 & 1\\ 1 & 2t\end{pmatrix}$** (the Hessian
matrix of $x^2 + xy + ty^2$) for some $t \in R$, when its cross coefficient $b$ is a unit (this is automatic when
$4ac - b^2$ is a unit). *Proof:* the form represents $1$ (`exists_represents_unit`) by a primitive vector $v$; complete
$v$ to a basis, then rescale the second basis vector. -/
theorem cong_P (h2 : (2 : R) ∈ maximalIdeal R) {a b c : R} (hb : IsUnit b) :
    ∃ t : R, Cong (!![2 * a, b; b, 2 * c] : Matrix (Fin 2) (Fin 2) R) (!![2, 1; 1, 2 * t]) := by
  obtain ⟨x, y, hxy⟩ := exists_represents_unit h2 (a := a) (b := b) (c := c) hb isUnit_one
  obtain ⟨w0, w1, hU⟩ : ∃ w0 w1 : R, IsUnit (x * w1 - w0 * y) := by
    by_cases hx : IsUnit x
    · exact ⟨0, 1, by simpa using hx⟩
    · have hy : IsUnit y := by
        by_contra hy
        have hxm : x ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).2 hx
        have hym : y ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal y).2 hy
        have h1 : (1 : R) ∈ maximalIdeal R := by
          rw [← hxy]
          refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
          · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hxm 2 (by norm_num))
          · exact Ideal.mul_mem_left _ _ hym
          · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hym 2 (by norm_num))
        exact ((IsLocalRing.mem_maximalIdeal _).1 h1) isUnit_one
      exact ⟨1, 0, by simpa using hy.neg⟩
  set U : Matrix (Fin 2) (Fin 2) R := !![x, w0; y, w1] with hUdef
  have hdetU : IsUnit U.det := by
    rw [hUdef, Matrix.det_fin_two_of]; simpa using hU
  set H : Matrix (Fin 2) (Fin 2) R := !![2 * a, b; b, 2 * c] with hHdef
  set β : R := 2 * a * x * w0 + b * (x * w1 + y * w0) + 2 * c * y * w1 with hβ
  set c1 : R := a * w0 ^ 2 + b * w0 * w1 + c * w1 ^ 2 with hc1
  have hH1 : Uᵀ * H * U = !![2, β; β, 2 * c1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hUdef, hHdef, Matrix.mul_apply, Fin.sum_univ_two, hβ, hc1] <;>
      first | ring1 | linear_combination 2 * hxy
  have hdetH : IsUnit H.det := by
    rw [hHdef, Matrix.det_fin_two_of]
    have h4 : (4 : R) * (a * c) ∈ maximalIdeal R := by
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h2)
    have := isUnit_add_of_mem (hb.pow 2).neg h4
    convert this using 1; ring
  have hdet1 : IsUnit (4 * c1 - β ^ 2) := by
    have h := congrArg Matrix.det hH1
    have hr : (!![2, β; β, 2 * c1] : Matrix (Fin 2) (Fin 2) R).det = 4 * c1 - β ^ 2 := by
      rw [Matrix.det_fin_two_of]; ring
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hr] at h
    rw [← h]; exact (hdetU.mul hdetH).mul hdetU
  have hβu : IsUnit β := isUnit_of_isUnit_four_sub_sq h2 hdet1
  obtain ⟨β', hβ'⟩ := hβu.exists_right_inv
  refine ⟨c1 * β' ^ 2, ?_⟩
  have h1 : Cong H (!![2, β; β, 2 * c1] : Matrix (Fin 2) (Fin 2) R) := by
    have := cong_of_isUnit_det H U hdetU
    rwa [hH1] at this
  exact h1.trans (cong_scale hβ')

end Normalize

section Squares

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **A unit square congruent to $1$ modulo $4$ is congruent to $1$ modulo $2$:** if $a(a + 2) = 4k$ then $2 \mid a$
(in a discrete valuation ring; compare $a = u - 1$, $a(a+2) = u^2 - 1$). -/
theorem two_dvd_of_mul_eq {a k : R} (h : a * (a + 2) = 4 * k) : 2 ∣ a := by
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond a (2 : R)
  · by_cases ha : a = 0
    · rw [ha]; exact dvd_zero _
    · have h1 : a ^ 2 * (1 + c) = a ^ 2 * (c ^ 2 * k) := by
        have : (4 : R) = a ^ 2 * c ^ 2 := by rw [← mul_pow, hc]; norm_num
        calc a ^ 2 * (1 + c) = a * (a + a * c) := by ring
          _ = a * (a + 2) := by rw [hc]
          _ = 4 * k := h
          _ = a ^ 2 * (c ^ 2 * k) := by rw [this]; ring
      have h2 := mul_left_cancel₀ (pow_ne_zero 2 ha) h1
      have hcd : c * (c * k - 1) = 1 := by linear_combination -h2
      refine ⟨c * k - 1, ?_⟩
      calc a = a * (c * (c * k - 1)) := by rw [hcd, mul_one]
        _ = 2 * (c * k - 1) := by rw [← mul_assoc, hc]
  · exact ⟨c, hc.symm⟩

/-- **The forms $x^2 + xy + ty^2$ and $x^2 + xy + t'y^2$ are isometric when $1 - 4t' = u^2(1 - 4t)$, $u$ a unit**
(in a discrete valuation ring of characteristic $\ne 2$): with $u = 1 - 2m$ (`two_dvd_of_mul_eq`), the change of
variables $(x, y) \mapsto (x + my, uy)$ turns $x^2 + xy + ty^2$ into $x^2 + xy + t'y^2$. As Hessian matrices. -/
theorem cong_P_of_det (h20 : (2 : R) ≠ 0) {t t' u : R} (hu : IsUnit u) (h : 1 - 4 * t' = u ^ 2 * (1 - 4 * t)) :
    Cong (!![2, 1; 1, 2 * t] : Matrix (Fin 2) (Fin 2) R) (!![2, 1; 1, 2 * t']) := by
  have hk : (u - 1) * (u - 1 + 2) = 4 * (u ^ 2 * t - t') := by linear_combination -h
  obtain ⟨n, hn⟩ := two_dvd_of_mul_eq hk
  set m : R := -n with hm
  have hum : u = 1 - 2 * m := by rw [hm]; linear_combination hn
  have h4 : (4 : R) ≠ 0 := by
    have : (4 : R) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h20 h20
  have ht' : t' = m ^ 2 + m * u + t * u ^ 2 := by
    apply mul_left_cancel₀ h4
    rw [hum] at h ⊢
    linear_combination -h
  have hU : IsUnit (!![1, m; 0, u] : Matrix (Fin 2) (Fin 2) R).det := by
    rw [Matrix.det_fin_two_of]; simpa using hu
  have := cong_of_isUnit_det (!![2, 1; 1, 2 * t] : Matrix (Fin 2) (Fin 2) R) _ hU
  convert this using 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | (rw [ht']; ring1) | (rw [hum]; ring1)

end Squares

section Classify

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]

/-- A $2 \times 2$ Hessian matrix is $\begin{pmatrix} 2a & b\\ b & 2c\end{pmatrix}$. -/
theorem isHess_fin_two {H : Matrix (Fin 2) (Fin 2) R} (h : IsHess H) :
    ∃ a b c : R, H = !![2 * a, b; b, 2 * c] := by
  obtain ⟨G, rfl⟩ := h
  refine ⟨G 0 0, G 0 1 + G 1 0, G 1 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **Binary even unimodular matrices are classified by their determinants** (the $n = 2$ case of Hanke 2011,
Sublemma 2.7, as a statement about Hessian matrices; `cong_P` normalizes both, `cong_P_of_det` compares them): two
$2 \times 2$ Hessian matrices with unit determinants whose determinants differ by the square of a unit are congruent.
Here $R$ is a Henselian discrete valuation ring with finite residue field, $2 \in \mathfrak p$ and $2 \ne 0$. -/
theorem cong_binary (h2 : (2 : R) ∈ maximalIdeal R) (h20 : (2 : R) ≠ 0) {H H' : Matrix (Fin 2) (Fin 2) R}
    (hH : IsHess H) (hH' : IsHess H') (hd : IsUnit H.det) (hd' : IsUnit H'.det) {u : R} (hu : IsUnit u)
    (h : H'.det = u ^ 2 * H.det) : Cong H H' := by
  obtain ⟨a, b, c, rfl⟩ := isHess_fin_two hH
  obtain ⟨a', b', c', rfl⟩ := isHess_fin_two hH'
  have hb : IsUnit b := by
    refine isUnit_of_isUnit_four_sub_sq h2 (c := a * c) ?_
    rw [Matrix.det_fin_two_of] at hd
    convert hd using 1; ring
  have hb' : IsUnit b' := by
    refine isUnit_of_isUnit_four_sub_sq h2 (c := a' * c') ?_
    rw [Matrix.det_fin_two_of] at hd'
    convert hd' using 1; ring
  obtain ⟨t, ht⟩ := cong_P h2 (a := a) (c := c) hb
  obtain ⟨t', ht'⟩ := cong_P h2 (a := a') (c := c') hb'
  obtain ⟨w1, hw1, e1⟩ := ht.det
  obtain ⟨w2, hw2, e2⟩ := ht'.det
  obtain ⟨w1', hw1'⟩ := hw1.exists_right_inv
  have hPt : (!![2, 1; 1, 2 * t] : Matrix (Fin 2) (Fin 2) R).det = 4 * t - 1 := by
    rw [Matrix.det_fin_two_of]; ring
  have hPt' : (!![2, 1; 1, 2 * t'] : Matrix (Fin 2) (Fin 2) R).det = 4 * t' - 1 := by
    rw [Matrix.det_fin_two_of]; ring
  rw [hPt] at e1
  rw [hPt'] at e2
  have hv : IsUnit (w1' * w2 * u) := by
    have h1' : IsUnit w1' := isUnit_iff_exists_inv'.2 ⟨w1, hw1'⟩
    exact (h1'.mul hw2).mul hu
  have key : 1 - 4 * t' = (w1' * w2 * u) ^ 2 * (1 - 4 * t) := by
    rw [h] at e2
    linear_combination (-1 : R) * e2 + ((w1' * w2 * u) ^ 2) * e1 +
      (w2 ^ 2 * u ^ 2 * (!![2 * a, b; b, 2 * c] : Matrix (Fin 2) (Fin 2) R).det * (w1 * w1' + 1)) * hw1'
  exact ht.trans ((cong_P_of_det h20 hv key).trans ht'.symm)

end Classify

end QuadFormsKB.Hanke2011Structure.Dyadic
