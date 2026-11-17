import QuadFormsKB.Historical.Gauss.CompositionTransitivity

/-!
# Gauss's quantity $\Delta$ and the sign relation $\Delta = D n n'$
(Disquisitiones Arithmeticae, Art. 235)

(sign of $\Delta$; proved), with the identities of that it uses.

Indices are $0$-based: Gauss's $p, p', p'', p'''$ are `p 0, p 1, p 2, p 3`, and $(P, Q, R, S, T, U)$ are
`minors p q 0, …, 5`. Forms are Gauss's: $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ (`gaussForm`, middle
library coefficient $2B$, $2b$, $2b'$), with determinants $D = B^2 - AC$, $d = b^2 - ac$, $d' = b'^2 - a'c'$.

## What is proved

* `art235_delta_eq`: for a bilinear substitution transforming $F$ into $f f'$ with the six relations of Art. 235
  and $\Delta$ defined by $A p_0p_3 + B(p_0q_3 + q_0p_3) + C q_0q_3 = bb' + \Delta$, one has $\Delta = D n n'$
  (when $f$ and $f'$ are not the zero form).
  The proof follows Gauss: the nine coefficient identities of $F(X, Y) = f f'$ give the Gram matrix of the four
  vectors $(p_i, q_i)$, its $2 \times 2$ minors are $-D$ times products of the six numbers (Binet-Cauchy), and the nine
  products $a a', 2ab', \dots, cc'$ times $\Delta - D n n'$ vanish.
* `art235_delta_sq`: $\Delta^2 = d d'$.
* `art235_delta_sign`: if $D \ne 0$ then $\Delta D > 0$ iff $n n' > 0$ and $\Delta D < 0$ iff $n n' < 0$
  ($\Delta$ has the sign of $D$ iff $n, n'$ have equal signs).

* `art235_gcd_determinant` (fourth conclusion): with $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$,
  $x = \gcd(P, R-S, U) = m|n'|$, $y = \gcd(Q, R+S, T) = m'|n|$, $k = \gcd(P, \dots, U) = \gcd(x, y)$ and
  $|D| k^2 = \gcd(d m'^2, d' m^2)$ (Gauss writes $D k^2$).
* `art235_coprime_iff`, `art235_isCompounded_det`: $k = 1$ iff $|D| = \gcd(d m'^2, d' m^2)$, and this holds for a
  compounded form.
* `art235_extremal`: with $k = 1$, every other form transformed into $ff'$ with the relations has $|D_2| \le |D|$
  (the relations for every transformation are a hypothesis, not proved).

Nothing is assumed beyond the displayed relations; no positivity or coprimality (except where stated).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- The Gram entry $F(v_i, v_j)$ of the vectors $v_i = (p_i, q_i)$ for $F = (A, B, C)$ (Gauss's form with
middle coefficient $2B$). -/
private def gz (A B C : ℤ) (p q : Fin 4 → ℤ) (i j : Fin 4) : ℤ :=
  A * p i * p j + B * (p i * q j + q i * p j) + C * q i * q j

/-- The $2 \times 2$ minor $p_i q_j - q_i p_j$. -/
private def mm (p q : Fin 4 → ℤ) (i j : Fin 4) : ℤ := p i * q j - q i * p j

private theorem gz_comm (A B C : ℤ) (p q : Fin 4 → ℤ) (i j : Fin 4) : gz A B C p q i j = gz A B C p q j i := by
  simp only [gz]; ring

/-- Binet-Cauchy for the Gram matrix: $g_{ik} g_{jl} - g_{il} g_{jk} = -D\, m_{ij} m_{kl}$. -/
private theorem gz_minor (A B C : ℤ) (p q : Fin 4 → ℤ) (i j k l : Fin 4) :
    gz A B C p q i k * gz A B C p q j l - gz A B C p q i l * gz A B C p q j k =
      -(B ^ 2 - A * C) * mm p q i j * mm p q k l := by
  simp only [gz, mm]; ring

private theorem delta_core {a b c a' b' c' n n' Δ D M01 M02 M03 M12 M13 M23 : ℚ}
    (r01 : M01 = a * n') (r02 : M02 = a' * n) (r13 : M13 = c' * n) (r23 : M23 = c * n')
    (rM : M03 - M12 = 2 * b * n') (rP : M03 + M12 = 2 * b' * n)
    (I1 : a * a' * (b * b' - Δ) - b * a' * (a * b') = -D * M01 * M02)
    (Ia : a * a' * (b * c') - (b * b' + Δ) * (a * b') = -D * M01 * M03)
    (Ib : a * b' * (b * b' - Δ) - b * a' * (a * c') = -D * M01 * M12)
    (Ic : a * b' * (b * c') - (b * b' + Δ) * (a * c') = -D * M01 * M13)
    (Id : a * a' * (c * b') - (b * b' + Δ) * (b * a') = -D * M02 * M03)
    (Ie : a * b' * (c * a') - b * a' * (b * b' - Δ) = -D * M02 * M12)
    (If : a * a' * (c * c') - (b * b' + Δ) * (b * b' + Δ) = -D * M03 * M03)
    (Ig : a * c' * (c * a') - (b * b' - Δ) * (b * b' - Δ) = -D * M12 * M12)
    (Ih : a * b' * (c * c') - b * c' * (b * b' + Δ) = -D * M13 * M03)
    (Ii : a * c' * (c * b') - (b * b' - Δ) * (b * c') = -D * M13 * M12)
    (Ij : b * a' * (c * b') - c * a' * (b * b' + Δ) = -D * M23 * M02)
    (Ik : b * a' * (c * c') - c * b' * (b * b' + Δ) = -D * M23 * M03)
    (Il : (b * b' - Δ) * (c * b') - c * a' * (b * c') = -D * M23 * M12)
    (Im : (b * b' - Δ) * (c * c') - c * b' * (b * c') = -D * M23 * M13) :
    a * a' * (Δ - D * n * n') = 0 ∧ a * b' * (Δ - D * n * n') = 0 ∧ a * c' * (Δ - D * n * n') = 0 ∧
    b * a' * (Δ - D * n * n') = 0 ∧ b * b' * (Δ - D * n * n') = 0 ∧ b * c' * (Δ - D * n * n') = 0 ∧
    c * a' * (Δ - D * n * n') = 0 ∧ c * b' * (Δ - D * n * n') = 0 ∧ c * c' * (Δ - D * n * n') = 0 := by
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (-1) * I1 + D * M02 * r01 + D * a * n' * r02
  · have : 2 * (a * b' * (Δ - D * n * n')) = 0 := by
      linear_combination (-1) * Ia + (-1) * Ib + D * (M03 + M12) * r01 + D * a * n' * rP
    exact (mul_eq_zero.mp this).resolve_left h2
  · linear_combination (-1) * Ic + D * M13 * r01 + D * a * n' * r13
  · have : 2 * (b * a' * (Δ - D * n * n')) = 0 := by
      linear_combination (-1) * Id + Ie + D * (M03 - M12) * r02 + D * a' * n * rM
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : 4 * (b * b' * (Δ - D * n * n')) = 0 := by
      linear_combination (-1) * If + Ig + D * (M03 + M12) * rM + D * (2 * b * n') * rP
    exact (mul_eq_zero.mp this).resolve_left h4
  · have : 2 * (b * c' * (Δ - D * n * n')) = 0 := by
      linear_combination (-1) * Ih + Ii + D * (M03 - M12) * r13 + D * c' * n * rM
    exact (mul_eq_zero.mp this).resolve_left h2
  · linear_combination (-1) * Ij + D * M02 * r23 + D * c * n' * r02
  · have : 2 * (c * b' * (Δ - D * n * n')) = 0 := by
      linear_combination (-1) * Ik + (-1) * Il + D * (M03 + M12) * r23 + D * c * n' * rP
    exact (mul_eq_zero.mp this).resolve_left h2
  · linear_combination (-1) * Im + D * M13 * r23 + D * c * n' * r13

/-- A Gauss form that is not the zero form has a nonzero coefficient. -/
private theorem coeff_ne_zero {a b c : ℤ} (h : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  obtain ⟨x, y, hv⟩ := h
  apply hv
  rw [eval_gaussForm]; simp [ha, hb, hc]

/-- **Gauss, *Disq. Arith.* Art. 235, $\Delta = D n n'$:** let $F = (A, B, C)$ be
transformed into $f f'$, $f = (a, b, c)$, $f' = (a', b', c')$, by the bilinear substitution $(p, q)$ (`TransformsInto`),
let the six relations of Art. 235 hold with rational $n, n'$,
$$P = a n',\ R - S = 2 b n',\ U = c n',\qquad Q = a' n,\ R + S = 2 b' n,\ T = c' n,$$
and let $\Delta$ be defined by $A p_0 p_3 + B (p_0 q_3 + q_0 p_3) + C q_0 q_3 = b b' + \Delta$ (Gauss's
$App''' + B(pq''' + qp''') + Cqq''' = bb' + \Delta$, $0$-based). If neither $f$ nor $f'$ is the zero form, then
$\Delta = D n n'$ with $D = B^2 - AC$ (in $\mathbb Q$). Gauss's route is followed: the nine coefficient equations
(`gz` entries) give $D P Q = \Delta a a'$ and eight similar identities, here as minors of the Gram matrix
(Binet-Cauchy), so $a a', 2ab', \dots, cc'$ times $\Delta - Dnn'$ all vanish. No positivity and no coprimality of the six
numbers is used. Sanity check: $(1, 0, 1)$ into $(1,0,1)(1,0,1)$ by $p = (1, 0, 0, -1)$, $q = (0, 1, 1, 0)$ gives
$\Delta = -1 = D n n'$ with $D = -1$, $n = n' = 1$. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_delta_eq {A B C a b c a' b' c' Δ : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q)
    (h0 : (minors p q 0 : ℚ) = a * n') (h1 : (minors p q 2 : ℚ) - minors p q 3 = 2 * b * n')
    (h2 : (minors p q 5 : ℚ) = c * n') (h3 : (minors p q 1 : ℚ) = a' * n)
    (h4 : (minors p q 2 : ℚ) + minors p q 3 = 2 * b' * n) (h5 : (minors p q 4 : ℚ) = c' * n)
    (hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 = b * b' + Δ)
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    (Δ : ℚ) = gaussDet A B C * n * n' := by
  have ev : ∀ x y x' y' : ℤ,
      A * (bilin p x y x' y') ^ 2 + 2 * B * bilin p x y x' y' * bilin q x y x' y' + C * (bilin q x y x' y') ^ 2 =
        (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a' * x' ^ 2 + 2 * b' * x' * y' + c' * y' ^ 2) := by
    intro x y x' y'
    have := hT x y x' y'
    rw [eval_gaussForm, eval_gaussForm, eval_gaussForm] at this
    exact this
  have e00 : gz A B C p q 0 0 = a * a' := by
    have h := ev 1 0 1 0
    simp only [bilin, gz] at h ⊢; linear_combination h
  have e11 : gz A B C p q 1 1 = a * c' := by
    have h := ev 1 0 0 1
    simp only [bilin, gz] at h ⊢; linear_combination h
  have e22 : gz A B C p q 2 2 = c * a' := by
    have h := ev 0 1 1 0
    simp only [bilin, gz] at h ⊢; linear_combination h
  have e33 : gz A B C p q 3 3 = c * c' := by
    have h := ev 0 1 0 1
    simp only [bilin, gz] at h ⊢; linear_combination h
  have e01 : gz A B C p q 0 1 = a * b' := by
    have h := ev 1 0 1 1
    have : 2 * gz A B C p q 0 1 = 2 * (a * b') := by
      simp only [bilin, gz] at h e00 e11 ⊢; linear_combination h - e00 - e11
    exact mul_left_cancel₀ two_ne_zero this
  have e02 : gz A B C p q 0 2 = b * a' := by
    have h := ev 1 1 1 0
    have : 2 * gz A B C p q 0 2 = 2 * (b * a') := by
      simp only [bilin, gz] at h e00 e22 ⊢; linear_combination h - e00 - e22
    exact mul_left_cancel₀ two_ne_zero this
  have e23 : gz A B C p q 2 3 = c * b' := by
    have h := ev 0 1 1 1
    have : 2 * gz A B C p q 2 3 = 2 * (c * b') := by
      simp only [bilin, gz] at h e22 e33 ⊢; linear_combination h - e22 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e13 : gz A B C p q 1 3 = b * c' := by
    have h := ev 1 1 0 1
    have : 2 * gz A B C p q 1 3 = 2 * (b * c') := by
      simp only [bilin, gz] at h e11 e33 ⊢; linear_combination h - e11 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e03 : gz A B C p q 0 3 = b * b' + Δ := by
    simp only [gz]; linear_combination hΔ
  have e12 : gz A B C p q 1 2 = b * b' - Δ := by
    have h := ev 1 1 1 1
    have : gz A B C p q 0 3 + gz A B C p q 1 2 = 2 * (b * b') := by
      have : 2 * (gz A B C p q 0 3 + gz A B C p q 1 2) = 2 * (2 * (b * b')) := by
        simp only [bilin, gz] at h e00 e11 e22 e33 e01 e02 e13 e23 ⊢
        linear_combination h - e00 - e11 - e22 - e33 - 2 * e01 - 2 * e02 - 2 * e13 - 2 * e23
      exact mul_left_cancel₀ two_ne_zero this
    linarith
  have e10 : gz A B C p q 1 0 = a * b' := by rw [gz_comm]; exact e01
  have e20 : gz A B C p q 2 0 = b * a' := by rw [gz_comm]; exact e02
  have e32 : gz A B C p q 3 2 = c * b' := by rw [gz_comm]; exact e23
  have e31 : gz A B C p q 3 1 = b * c' := by rw [gz_comm]; exact e13
  have e30 : gz A B C p q 3 0 = b * b' + Δ := by rw [gz_comm]; exact e03
  have e21 : gz A B C p q 2 1 = b * b' - Δ := by rw [gz_comm]; exact e12
  -- the minor identities, in `ℚ`
  have mI : ∀ i j k l : Fin 4, ∀ L : ℤ,
      (gz A B C p q i k * gz A B C p q j l - gz A B C p q i l * gz A B C p q j k = L) →
      L = -(B ^ 2 - A * C) * mm p q i j * mm p q k l := by
    intro i j k l L hL; rw [← hL]; exact gz_minor A B C p q i j k l
  have key : ∀ (i j k l : Fin 4) (L : ℤ),
      gz A B C p q i k * gz A B C p q j l - gz A B C p q i l * gz A B C p q j k = L →
      (L : ℚ) = -((B : ℚ) ^ 2 - A * C) * (mm p q i j : ℤ) * (mm p q k l : ℤ) := by
    intro i j k l L hL
    have := mI i j k l L hL
    exact_mod_cast this
  have K := fun i j k l => key i j k l
  have I1 := K 0 1 0 2 (a * a' * (b * b' - Δ) - b * a' * (a * b')) (by
    simp only [e00, e12, e02, e10])
  have Ia := K 0 1 0 3 (a * a' * (b * c') - (b * b' + Δ) * (a * b')) (by
    simp only [e00, e13, e03, e10])
  have Ib := K 0 1 1 2 (a * b' * (b * b' - Δ) - b * a' * (a * c')) (by
    simp only [e01, e12, e02, e11])
  have Ic := K 0 1 1 3 (a * b' * (b * c') - (b * b' + Δ) * (a * c')) (by
    simp only [e01, e13, e03, e11])
  have Id := K 0 2 0 3 (a * a' * (c * b') - (b * b' + Δ) * (b * a')) (by
    simp only [e00, e23, e03, e20])
  have Ie := K 0 2 1 2 (a * b' * (c * a') - b * a' * (b * b' - Δ)) (by
    simp only [e01, e22, e02, e21])
  have If := K 0 3 0 3 (a * a' * (c * c') - (b * b' + Δ) * (b * b' + Δ)) (by
    simp only [e00, e33, e03, e30])
  have Ig := K 1 2 1 2 (a * c' * (c * a') - (b * b' - Δ) * (b * b' - Δ)) (by
    simp only [e11, e22, e12, e21])
  have Ih := K 1 3 0 3 (a * b' * (c * c') - b * c' * (b * b' + Δ)) (by
    simp only [e10, e33, e13, e30])
  have Ii := K 1 3 1 2 (a * c' * (c * b') - (b * b' - Δ) * (b * c')) (by
    simp only [e11, e32, e12, e31])
  have Ij := K 2 3 0 2 (b * a' * (c * b') - c * a' * (b * b' + Δ)) (by
    simp only [e20, e32, e22, e30])
  have Ik := K 2 3 0 3 (b * a' * (c * c') - c * b' * (b * b' + Δ)) (by
    simp only [e20, e33, e23, e30])
  have Il := K 2 3 1 2 ((b * b' - Δ) * (c * b') - c * a' * (b * c')) (by
    simp only [e21, e32, e22, e31])
  have Im := K 2 3 1 3 ((b * b' - Δ) * (c * c') - c * b' * (b * c')) (by
    simp only [e21, e33, e23, e31])
  -- the relations in terms of `mm`
  have m01 : minors p q 0 = mm p q 0 1 := by rfl
  have m02 : minors p q 1 = mm p q 0 2 := by rfl
  have m03 : minors p q 2 = mm p q 0 3 := by rfl
  have m12 : minors p q 3 = mm p q 1 2 := by rfl
  have m13 : minors p q 4 = mm p q 1 3 := by rfl
  have m23 : minors p q 5 = mm p q 2 3 := by rfl
  rw [m01] at h0
  rw [m23] at h2
  rw [m02] at h3
  rw [m13] at h5
  rw [m03, m12] at h1 h4
  have core := delta_core (D := (B : ℚ) ^ 2 - A * C) (Δ := (Δ : ℚ)) h0 h3 h5 h2 h1 h4
    (by push_cast at I1; linear_combination I1) (by push_cast at Ia; linear_combination Ia)
    (by push_cast at Ib; linear_combination Ib) (by push_cast at Ic; linear_combination Ic)
    (by push_cast at Id; linear_combination Id) (by push_cast at Ie; linear_combination Ie)
    (by push_cast at If; linear_combination If) (by push_cast at Ig; linear_combination Ig)
    (by push_cast at Ih; linear_combination Ih) (by push_cast at Ii; linear_combination Ii)
    (by push_cast at Ij; linear_combination Ij) (by push_cast at Ik; linear_combination Ik)
    (by push_cast at Il; linear_combination Il) (by push_cast at Im; linear_combination Im)
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, z9⟩ := core
  have hZ : (Δ : ℚ) - ((B : ℚ) ^ 2 - A * C) * n * n' = 0 := by
    have ca : (a : ℚ) ≠ 0 ∨ (b : ℚ) ≠ 0 ∨ (c : ℚ) ≠ 0 := by
      rcases coeff_ne_zero hf with h | h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (Or.inl (by exact_mod_cast h))
      · exact Or.inr (Or.inr (by exact_mod_cast h))
    have cb : (a' : ℚ) ≠ 0 ∨ (b' : ℚ) ≠ 0 ∨ (c' : ℚ) ≠ 0 := by
      rcases coeff_ne_zero hf' with h | h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (Or.inl (by exact_mod_cast h))
      · exact Or.inr (Or.inr (by exact_mod_cast h))
    have hz : ∀ u v : ℚ, u * v * ((Δ : ℚ) - ((B : ℚ) ^ 2 - A * C) * n * n') = 0 → u ≠ 0 → v ≠ 0 →
        (Δ : ℚ) - ((B : ℚ) ^ 2 - A * C) * n * n' = 0 := by
      intro u v h hu hv
      exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu hv)
    rcases ca with ha | ha | ha <;> rcases cb with hb | hb | hb
    · exact hz _ _ z1 ha hb
    · exact hz _ _ z2 ha hb
    · exact hz _ _ z3 ha hb
    · exact hz _ _ z4 ha hb
    · exact hz _ _ z5 ha hb
    · exact hz _ _ z6 ha hb
    · exact hz _ _ z7 ha hb
    · exact hz _ _ z8 ha hb
    · exact hz _ _ z9 ha hb
  simp only [gaussDet]
  push_cast
  linear_combination hZ

/-- **Gauss, *Disq. Arith.* Art. 235 (the historical sources/00332), $\Delta^2 = d d'$:** under the hypotheses of
`art235_delta_eq`, $\Delta^2 = d d'$ for the determinants $d = b^2 - ac$ and $d' = b'^2 - a'c'$ of $f$, $f'$ (in
$\mathbb Q$). Proof: $\Delta = Dnn'$, $d = Dn^2$, $d' = Dn'^2$ (`disc_mul_sq_of_rel_first`,
`disc_mul_sq_of_rel_second`). -/
@[kb "gauss1801" "Art. 235"]
theorem art235_delta_sq {A B C a b c a' b' c' Δ : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q)
    (h0 : (minors p q 0 : ℚ) = a * n') (h1 : (minors p q 2 : ℚ) - minors p q 3 = 2 * b * n')
    (h2 : (minors p q 5 : ℚ) = c * n') (h3 : (minors p q 1 : ℚ) = a' * n)
    (h4 : (minors p q 2 : ℚ) + minors p q 3 = 2 * b' * n) (h5 : (minors p q 4 : ℚ) = c' * n)
    (hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 = b * b' + Δ)
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    ((Δ : ℤ) : ℚ) ^ 2 = gaussDet a b c * gaussDet a' b' c' := by
  have hΔq := art235_delta_eq hT h0 h1 h2 h3 h4 h5 hΔ hf hf'
  have e1 := disc_mul_sq_of_rel_first hT (by simpa using h3) (by simpa using h4) (by simpa using h5) hf'
  have e2 := disc_mul_sq_of_rel_second hT (by simpa using h0) (by simpa using h1) (by simpa using h2) hf
  simp only [disc_gaussForm] at e1 e2
  push_cast at e1 e2
  rw [hΔq]
  linear_combination (-(gaussDet a' b' c' : ℚ) / 4) * e1 - (gaussDet A B C : ℚ) * n ^ 2 / 4 * e2

/-- **Gauss, *Disq. Arith.* Art. 235, the sign of $\Delta$:** under the hypotheses of
`art235_delta_eq`, if $D \ne 0$ then $\Delta D > 0$ (that is, $\Delta$ has the sign of $D$) iff $n n' > 0$, and
$\Delta D < 0$ iff $n n' < 0$. Because $d = Dn^2$ and $d' = Dn'^2$, "the sign of $D$" is also the sign of $d$ and $d'$
(when $n, n' \ne 0$). -/
@[kb "gauss1801" "Art. 235"]
theorem art235_delta_sign {A B C a b c a' b' c' Δ : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q)
    (h0 : (minors p q 0 : ℚ) = a * n') (h1 : (minors p q 2 : ℚ) - minors p q 3 = 2 * b * n')
    (h2 : (minors p q 5 : ℚ) = c * n') (h3 : (minors p q 1 : ℚ) = a' * n)
    (h4 : (minors p q 2 : ℚ) + minors p q 3 = 2 * b' * n) (h5 : (minors p q 4 : ℚ) = c' * n)
    (hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 = b * b' + Δ)
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hD : gaussDet A B C ≠ 0) :
    (0 < (Δ : ℚ) * gaussDet A B C ↔ 0 < n * n') ∧ ((Δ : ℚ) * gaussDet A B C < 0 ↔ n * n' < 0) := by
  have hΔq := art235_delta_eq hT h0 h1 h2 h3 h4 h5 hΔ hf hf'
  have hDq : (gaussDet A B C : ℚ) ≠ 0 := by exact_mod_cast hD
  have hD2 : 0 < (gaussDet A B C : ℚ) ^ 2 := by positivity
  have e : (Δ : ℚ) * gaussDet A B C = (gaussDet A B C : ℚ) ^ 2 * (n * n') := by rw [hΔq]; ring
  rw [e]
  refine ⟨⟨fun h => ?_, fun h => mul_pos hD2 h⟩, ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hD2 h⟩⟩
  · by_contra hn
    exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hD2.le (not_lt.mp hn)))
  · by_contra hn
    exact absurd h (not_lt.mpr (mul_nonneg hD2.le (not_lt.mp hn)))

/-! ### The fourth conclusion of Art. 235: $k = \gcd(mn', m'n)$ and $|D| k^2 = \gcd(d m'^2, d' m^2)$ -/

/-- **The relations of Art. 235** for $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ and rationals $n, n'$:
the bilinear substitution $(p, q)$ transforms $F$ into $f f'$ and
$P = a n'$, $R - S = 2 b n'$, $U = c n'$, $Q = a' n$, $R + S = 2 b' n$, $T = c' n$ (third conclusion of Art. 235;
$0$-based indices, $P, \dots, U$ = `minors p q 0, …, 5`). No positivity and no coprimality. -/
def GaussRelations (A B C a b c a' b' c' : ℤ) (p q : Fin 4 → ℤ) (n n' : ℚ) : Prop :=
  TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q ∧
    (minors p q 0 : ℚ) = a * n' ∧ (minors p q 2 : ℚ) - minors p q 3 = 2 * b * n' ∧
    (minors p q 5 : ℚ) = c * n' ∧ (minors p q 1 : ℚ) = a' * n ∧
    (minors p q 2 : ℚ) + minors p q 3 = 2 * b' * n ∧ (minors p q 4 : ℚ) = c' * n

/-- **The greatest common divisor $k$ of the six numbers** $P, Q, R, S, T, U$ of $(p, q)$ (a natural number). -/
def sixGcd (p q : Fin 4 → ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd (minors p q 0).natAbs (minors p q 1).natAbs)
    (minors p q 2).natAbs) (minors p q 3).natAbs) (minors p q 4).natAbs) (minors p q 5).natAbs

/-- **The content $\gcd(a, b, c)$** of three integers (a natural number). Gauss's $m = \gcd(a, 2b, c)$ is
`cont3 a (2 * b) c`. -/
def cont3 (a b c : ℤ) : ℕ := Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs

private theorem dvd_cont3_iff (d : ℕ) (a b c : ℤ) :
    d ∣ cont3 a b c ↔ (d : ℤ) ∣ a ∧ (d : ℤ) ∣ b ∧ (d : ℤ) ∣ c := by
  unfold cont3
  rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd]
  tauto

private theorem dvd_sixGcd_iff (d : ℕ) (p q : Fin 4 → ℤ) :
    d ∣ sixGcd p q ↔ (d : ℤ) ∣ minors p q 0 ∧ (d : ℤ) ∣ minors p q 1 ∧ (d : ℤ) ∣ minors p q 2 ∧
      (d : ℤ) ∣ minors p q 3 ∧ (d : ℤ) ∣ minors p q 4 ∧ (d : ℤ) ∣ minors p q 5 := by
  unfold sixGcd
  rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, Int.natCast_dvd,
    Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd, Int.natCast_dvd]
  tauto

/-- The Plucker relation $P U - Q T + R S = 0$ among the six numbers. -/
private theorem minors_pluecker (p q : Fin 4 → ℤ) :
    minors p q 0 * minors p q 5 - minors p q 1 * minors p q 4 + minors p q 2 * minors p q 3 = 0 := by
  simp only [minors, Matrix.cons_val]; ring

/-- **A parity lemma:** if $d$ divides $P, Q, T, U$ and $R - S$, $R + S$, and $PU - QT + RS = 0$, then $d$ divides
$R$ and $S$. (Write $R + S = ds$, $R - S = dt$: $d^2 \mid RS$ forces $s \equiv t \pmod 2$.) -/
private theorem dvd_RS_of {d P Q R S T U : ℤ} (hpl : P * U - Q * T + R * S = 0) (hP : d ∣ P) (hQ : d ∣ Q)
    (hT : d ∣ T) (hU : d ∣ U) (h1 : d ∣ R - S) (h2 : d ∣ R + S) : d ∣ R ∧ d ∣ S := by
  by_cases hd : d = 0
  · subst hd
    have a1 := zero_dvd_iff.mp h1
    have a2 := zero_dvd_iff.mp h2
    exact ⟨by rw [zero_dvd_iff]; omega, by rw [zero_dvd_iff]; omega⟩
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨T', rfl⟩ := hT
  obtain ⟨U', rfl⟩ := hU
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  have hRS : 4 * (R * S) = d ^ 2 * (s ^ 2 - t ^ 2) := by
    have : 4 * (R * S) = (R + S) ^ 2 - (R - S) ^ 2 := by ring
    rw [this, hs, ht]; ring
  have h3 : d ^ 2 * (s ^ 2 - t ^ 2) = d ^ 2 * (4 * (Q' * T' - P' * U')) := by
    linear_combination (-1) * hRS + 4 * hpl
  have h4 : s ^ 2 - t ^ 2 = 4 * (Q' * T' - P' * U') := mul_left_cancel₀ (pow_ne_zero 2 hd) h3
  have h5 : (s - t) * (s + t) = 4 * (Q' * T' - P' * U') := by linear_combination h4
  obtain ⟨w, hw⟩ : ∃ w, w = Q' * T' - P' * U' := ⟨_, rfl⟩
  rw [← hw] at h5
  have h6 : (s + t) % 2 = 0 := by
    by_contra h
    have h7 : (s + t) % 2 = 1 := by omega
    have h8 : (s - t) % 2 = 1 := by omega
    have h9 : ((s - t) * (s + t)) % 2 = 1 := by rw [Int.mul_emod, h7, h8]; norm_num
    rw [h5] at h9; omega
  obtain ⟨u, hu⟩ : ∃ u, s + t = 2 * u := ⟨(s + t) / 2, by omega⟩
  have hR : R = d * u := by
    have : 2 * R = 2 * (d * u) := by linear_combination hs + ht + d * hu
    exact mul_left_cancel₀ two_ne_zero this
  have hS : S = d * (s - u) := by linear_combination hs - hR
  exact ⟨⟨u, hR⟩, ⟨s - u, hS⟩⟩

/-- **Gauss's six numbers have the same common divisors as $P, Q, T, U, R - S, R + S$** (no relations needed;
the parity of $R, S$ is settled by the Plucker relation): $k = \gcd(P, Q, R, S, T, U) = \gcd(x, y)$ with
$x = \gcd(P, R - S, U)$ and $y = \gcd(Q, R + S, T)$. -/
theorem sixGcd_eq_gcd_cont3 (p q : Fin 4 → ℤ) :
    sixGcd p q = Nat.gcd (cont3 (minors p q 0) (minors p q 2 - minors p q 3) (minors p q 5))
      (cont3 (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4)) := by
  have key : ∀ d : ℕ, d ∣ sixGcd p q ↔ d ∣ Nat.gcd (cont3 (minors p q 0) (minors p q 2 - minors p q 3)
      (minors p q 5)) (cont3 (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4)) := by
    intro d
    rw [Nat.dvd_gcd_iff, dvd_cont3_iff, dvd_cont3_iff, dvd_sixGcd_iff]
    constructor
    · rintro ⟨h0, h1, h2, h3, h4, h5⟩
      exact ⟨⟨h0, dvd_sub h2 h3, h5⟩, ⟨h1, dvd_add h2 h3, h4⟩⟩
    · rintro ⟨⟨hP, h23, hU⟩, ⟨hQ, h23', hT⟩⟩
      obtain ⟨hR, hS⟩ := dvd_RS_of (minors_pluecker p q) hP hQ hT hU h23 h23'
      exact ⟨hP, hQ, hR, hS, hT, hU⟩
  exact Nat.dvd_antisymm ((key _).1 dvd_rfl) ((key _).2 dvd_rfl)

private theorem cont3_scale (t s a b c u v w : ℤ) (hu : t * u = s * a) (hv : t * v = s * b) (hw : t * w = s * c) :
    t.natAbs * cont3 u v w = s.natAbs * cont3 a b c := by
  have hu' := congrArg Int.natAbs hu
  have hv' := congrArg Int.natAbs hv
  have hw' := congrArg Int.natAbs hw
  rw [Int.natAbs_mul, Int.natAbs_mul] at hu' hv' hw'
  unfold cont3
  calc t.natAbs * Nat.gcd (Nat.gcd u.natAbs v.natAbs) w.natAbs
      = Nat.gcd (Nat.gcd (t.natAbs * u.natAbs) (t.natAbs * v.natAbs)) (t.natAbs * w.natAbs) := by
        rw [Nat.gcd_mul_left, Nat.gcd_mul_left]
    _ = Nat.gcd (Nat.gcd (s.natAbs * a.natAbs) (s.natAbs * b.natAbs)) (s.natAbs * c.natAbs) := by
        rw [hu', hv', hw']
    _ = s.natAbs * Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs := by
        rw [Nat.gcd_mul_left, Nat.gcd_mul_left]

/-- **Scaling the content by a rational:** if $u = a r$, $v = b r$, $w = c r$ are integers, with $a, b, c$ integers
and $r$ rational, then $\gcd(u, v, w) = |r| \gcd(a, b, c)$ (in particular $|r| \gcd(a, b, c)$ is an integer). -/
theorem cont3_rat (r : ℚ) (a b c u v w : ℤ) (hu : (u : ℚ) = a * r) (hv : (v : ℚ) = b * r)
    (hw : (w : ℚ) = c * r) : (cont3 u v w : ℚ) = |r| * cont3 a b c := by
  have hden : (0 : ℚ) < r.den := by exact_mod_cast r.den_pos
  have hr : r * r.den = r.num := Rat.mul_den_eq_num r
  have k1 : ((r.den : ℤ) * u : ℤ) = r.num * a := by
    have : ((r.den : ℚ)) * u = r.num * a := by rw [hu, ← hr]; ring
    exact_mod_cast this
  have k2 : ((r.den : ℤ) * v : ℤ) = r.num * b := by
    have : ((r.den : ℚ)) * v = r.num * b := by rw [hv, ← hr]; ring
    exact_mod_cast this
  have k3 : ((r.den : ℤ) * w : ℤ) = r.num * c := by
    have : ((r.den : ℚ)) * w = r.num * c := by rw [hw, ← hr]; ring
    exact_mod_cast this
  have := cont3_scale _ _ a b c u v w k1 k2 k3
  rw [Int.natAbs_natCast] at this
  have h' : ((r.den : ℕ) : ℚ) * (cont3 u v w : ℚ) = (r.num.natAbs : ℚ) * cont3 a b c := by exact_mod_cast this
  have habs : (r.num.natAbs : ℚ) = |r| * r.den := by
    have : ((r.num.natAbs : ℕ) : ℚ) = |(r.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this, ← hr, abs_mul, abs_of_pos hden]
  rw [habs] at h'
  have hne : (r.den : ℚ) ≠ 0 := hden.ne'
  apply mul_left_cancel₀ hne
  linear_combination h'

private theorem nat_gcd_sq (x y : ℕ) : Nat.gcd (x ^ 2) (y ^ 2) = (Nat.gcd x y) ^ 2 := by
  rcases Nat.eq_zero_or_pos (Nat.gcd x y) with h | h
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp h
    simp
  · have hc := Nat.coprime_div_gcd_div_gcd h
    obtain ⟨x', hx'⟩ := Nat.gcd_dvd_left x y
    obtain ⟨y', hy'⟩ := Nat.gcd_dvd_right x y
    generalize Nat.gcd x y = g at h hc hx' hy' ⊢
    subst hx' hy'
    have hc' : Nat.Coprime x' y' := by simpa [Nat.mul_div_cancel_left _ h] using hc
    calc Nat.gcd ((g * x') ^ 2) ((g * y') ^ 2) = Nat.gcd (g ^ 2 * x' ^ 2) (g ^ 2 * y' ^ 2) := by
          rw [mul_pow, mul_pow]
      _ = g ^ 2 * Nat.gcd (x' ^ 2) (y' ^ 2) := Nat.gcd_mul_left _ _ _
      _ = g ^ 2 := by rw [Nat.Coprime.pow 2 2 hc', mul_one]

/-- **Gauss, *Disq. Arith.* Art. 235, fourth conclusion, first half, $k = \gcd(mn', m'n)$
and $|D| k^2 = \gcd(d m'^2, d' m^2)$:** let the relations of Art. 235 (`GaussRelations`) hold for
$F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$, with $f, f'$ not the zero form, and let
$k$ = `sixGcd p q` be the greatest common divisor of the six numbers, $m = \gcd(a, 2b, c)$,
$m' = \gcd(a', 2b', c')$ (`cont3`). Then, with $x = \gcd(P, R - S, U)$, $y = \gcd(Q, R + S, T)$:

* $x = m|n'|$ and $y = m'|n|$ in $\mathbb Q$ (so $m n'$ and $m' n$ are integers up to sign: **integrality of
  $m n'$, $m' n$ follows from the relations**; for $n, n' > 0$ these are $m n'$, $m' n$);
* $k = \gcd(x, y) = \gcd(m|n'|, m'|n|)$ (the parity of $R, S$ is handled by `sixGcd_eq_gcd_cont3`);
* $|D|\, k^2 = \gcd(d m'^2, d' m^2)$ with $d = b^2 - ac$, $d' = b'^2 - a'c'$.

Difference from the source: Gauss writes $D k^2$; $\gcd$ is nonnegative, so $|D|$ appears here. Gauss's $n, n'$
are rational in Art. 235; no integrality hypothesis is needed. The proof does not use Gauss's identities
$\Omega$ at all: $d = Dn^2$ (`disc_mul_sq_of_rel_first`) gives $d m'^2 = D y^2$ and $d' m^2 = D x^2$. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_gcd_determinant {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    ((cont3 (minors p q 0) (minors p q 2 - minors p q 3) (minors p q 5) : ℕ) : ℚ) =
        |n'| * cont3 a (2 * b) c ∧
      ((cont3 (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4) : ℕ) : ℚ) =
        |n| * cont3 a' (2 * b') c' ∧
      sixGcd p q = Nat.gcd (cont3 (minors p q 0) (minors p q 2 - minors p q 3) (minors p q 5))
        (cont3 (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4)) ∧
      (gaussDet A B C).natAbs * sixGcd p q ^ 2 =
        Int.gcd (gaussDet a b c * ((cont3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)
          (gaussDet a' b' c' * ((cont3 a (2 * b) c : ℕ) : ℤ) ^ 2) := by
  obtain ⟨hT, h0, h1, h2, h3, h4, h5⟩ := hR
  have hx := cont3_rat n' a (2 * b) c (minors p q 0) (minors p q 2 - minors p q 3) (minors p q 5) h0
    (by push_cast; linear_combination h1) h2
  have hy := cont3_rat n a' (2 * b') c' (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4) h3
    (by push_cast; linear_combination h4) h5
  refine ⟨hx, hy, sixGcd_eq_gcd_cont3 p q, ?_⟩
  have e1 := disc_mul_sq_of_rel_first hT (by simpa using h3) (by simpa using h4) (by simpa using h5) hf'
  have e2 := disc_mul_sq_of_rel_second hT (by simpa using h0) (by simpa using h1) (by simpa using h2) hf
  simp only [disc_gaussForm] at e1 e2
  push_cast at e1 e2
  generalize hxx : cont3 (minors p q 0) (minors p q 2 - minors p q 3) (minors p q 5) = x at hx ⊢
  generalize hyy : cont3 (minors p q 1) (minors p q 2 + minors p q 3) (minors p q 4) = y at hy ⊢
  have hdy : gaussDet a b c * ((cont3 a' (2 * b') c' : ℕ) : ℤ) ^ 2 = gaussDet A B C * (y : ℤ) ^ 2 := by
    have : (gaussDet a b c : ℚ) * (cont3 a' (2 * b') c' : ℚ) ^ 2 = (gaussDet A B C : ℚ) * (y : ℚ) ^ 2 := by
      rw [hy, mul_pow, sq_abs]
      linear_combination ((cont3 a' (2 * b') c' : ℚ) ^ 2 / 4) * e1
    exact_mod_cast this
  have hdx : gaussDet a' b' c' * ((cont3 a (2 * b) c : ℕ) : ℤ) ^ 2 = gaussDet A B C * (x : ℤ) ^ 2 := by
    have : (gaussDet a' b' c' : ℚ) * (cont3 a (2 * b) c : ℚ) ^ 2 = (gaussDet A B C : ℚ) * (x : ℚ) ^ 2 := by
      rw [hx, mul_pow, sq_abs]
      linear_combination ((cont3 a (2 * b) c : ℚ) ^ 2 / 4) * e2
    exact_mod_cast this
  rw [hdy, hdx, Int.gcd_mul_left, sixGcd_eq_gcd_cont3, hxx, hyy,
    show ((y : ℤ) ^ 2) = ((y ^ 2 : ℕ) : ℤ) by push_cast; ring,
    show ((x : ℤ) ^ 2) = ((x ^ 2 : ℕ) : ℤ) by push_cast; ring, Int.gcd_natCast_natCast, nat_gcd_sq,
    Nat.gcd_comm y x]

/-- **Gauss, *Disq. Arith.* Art. 235, fourth conclusion, "compounded iff":** under the
hypotheses of `art235_gcd_determinant` and $D \ne 0$, the six numbers are coprime ($k = 1$) iff
$|D| = \gcd(d m'^2, d' m^2)$. A form compounded of $f, f'$ (`IsCompounded`, which also asks $n, n' > 0$) therefore
satisfies $|D| = \gcd(d m'^2, d' m^2)$ (`art235_isCompounded_det`). -/
@[kb "gauss1801" "Art. 235"]
theorem art235_coprime_iff {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hD : gaussDet A B C ≠ 0) :
    sixGcd p q = 1 ↔ ((gaussDet A B C).natAbs : ℕ) =
      Int.gcd (gaussDet a b c * ((cont3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)
        (gaussDet a' b' c' * ((cont3 a (2 * b) c : ℕ) : ℤ) ^ 2) := by
  have h := (art235_gcd_determinant hR hf hf').2.2.2
  have hDn : (gaussDet A B C).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  constructor
  · intro hk; rw [← h, hk]; simp
  · intro hk
    rw [← hk] at h
    have h2 : sixGcd p q ^ 2 = 1 := by
      have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hDn) (h.trans (mul_one _).symm)
      exact this
    simpa using h2

/-- **Gauss, *Disq. Arith.* Art. 235, fourth conclusion, for a compounded form:** if
$F = (A, B, C)$ is compounded directly of $f = (a, b, c)$ and $f' = (a', b', c')$ (`IsCompounded`), $f, f'$ are not
the zero form and $D \ne 0$, then $|D| = \gcd(d m'^2, d' m^2)$, where $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_isCompounded_det {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hD : gaussDet A B C ≠ 0) :
    ((gaussDet A B C).natAbs : ℕ) =
      Int.gcd (gaussDet a b c * ((cont3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)
        (gaussDet a' b' c' * ((cont3 a (2 * b) c : ℕ) : ℤ) ^ 2) := by
  obtain ⟨p, q, hT, hcop, n, n', -, -, h0, h1, h2, h3, h4, h5⟩ := h
  have hR : GaussRelations A B C a b c a' b' c' p q n n' :=
    ⟨hT, by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
      by simpa using h5⟩
  refine (art235_coprime_iff hR hf hf' hD).1 ?_
  have hu : IsUnit ((sixGcd p q : ℕ) : ℤ) := by
    apply hcop
    intro i
    have := (dvd_sixGcd_iff (sixGcd p q) p q).1 dvd_rfl
    obtain ⟨d0, d1, d2, d3, d4, d5⟩ := this
    fin_cases i
    exacts [d0, d1, d2, d3, d4, d5]
  have h1 := Int.isUnit_iff_natAbs_eq.mp hu
  simpa using h1

/-- **Gauss, *Disq. Arith.* Art. 235, the extremal property:** a form compounded of
$f, f'$ has the largest possible determinant. Precisely: if $(p, q)$ transforms $F = (A, B, C)$ into $f f'$ with the
relations of Art. 235 and coprime six numbers ($k = 1$), $D \ne 0$, and $(p_2, q_2)$ transforms any form
$F_2 = (A_2, B_2, C_2)$ into the same $f f'$ with the relations of Art. 235 (for some rationals), then
$|D_2| \le |D|$. (Gauss's third conclusion, that the relations hold for every transformation, is taken as a
hypothesis here: it is not proved.) -/
@[kb "gauss1801" "Art. 235"]
theorem art235_extremal {A B C A₂ B₂ C₂ a b c a' b' c' : ℤ} {p q p₂ q₂ : Fin 4 → ℤ} {n n' n₂ n₂' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n') (hR₂ : GaussRelations A₂ B₂ C₂ a b c a' b' c' p₂ q₂ n₂ n₂')
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hD : gaussDet A B C ≠ 0) (hk : sixGcd p q = 1) :
    (gaussDet A₂ B₂ C₂).natAbs ≤ (gaussDet A B C).natAbs := by
  have h1 := (art235_gcd_determinant hR hf hf').2.2.2
  have h2 := (art235_gcd_determinant hR₂ hf hf').2.2.2
  rw [hk] at h1
  rw [← h2] at h1
  have hDn : (gaussDet A B C).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hk2 : sixGcd p₂ q₂ ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
    exact hD h1
  have : 1 ≤ sixGcd p₂ q₂ ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hk2)
  calc (gaussDet A₂ B₂ C₂).natAbs = (gaussDet A₂ B₂ C₂).natAbs * 1 := (mul_one _).symm
    _ ≤ (gaussDet A₂ B₂ C₂).natAbs * sixGcd p₂ q₂ ^ 2 := Nat.mul_le_mul_left _ this
    _ = (gaussDet A B C).natAbs := by rw [← h1]; simp

end QuadFormsKB.Historical.Gauss

