import QuadFormsKB.Historical.Gauss.Forms

/-!
# Determinants and orders of Gauss's forms (Disquisitiones Arithmeticae, Arts. 171, 215, 226)

(Art. 171, forms with a vanishing outer coefficient) (Art. 215,
the determinant of an implicated form) and (Art. 226, the order of a form).

* `art171_det_of_outer_zero`, `art171_outer_ne_zero` (Art. 171): if $a = 0$ or $c = 0$ the determinant of $(a, b, c)$
  is $b^2 \ge 0$; so a form of negative determinant has $a \ne 0$ and $c \ne 0$.
* `art215_det_implicated` (Art. 215): if $(a, b, c)$ implicates $(a', b', c')$ (the latter is obtained from the former
  by an integral substitution) then $b'^2 - a'c' = (\alpha\delta - \beta\gamma)^2 (b^2 - ac)$, so the determinant of
  the first divides that of the second; a form of determinant $0$ implicates only forms of determinant $0$.
* `gaussOrder` (Art. 226): Gauss's *order* of $(a, b, c)$ is determined by its determinant $b^2 - ac$ and the two
  numbers $\gcd(a, b, c)$ and $\gcd(a, 2b, c)$. `art226_order_of_sl` proves it is invariant under proper
  equivalence and `art226_opposite_same_order` that opposite classes belong to the same order.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **Gauss's forms are determined by their three coefficients:** $(a, b, c) = (a', b', c')$ as forms iff
$a = a'$, $b = b'$, $c = c'$. -/
theorem gaussForm_inj {a b c a' b' c' : ℤ} (h : gaussForm a b c = gaussForm a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg BinQF.a h
  have h2 := congrArg BinQF.b h
  have h3 := congrArg BinQF.c h
  simp only [a_gaussForm, b_gaussForm, c_gaussForm] at h1 h2 h3
  exact ⟨h1, by omega, h3⟩

/-- **Gauss, *Disq. Arith.* Art. 171: a form with a vanishing outer coefficient has square
determinant.** If $a = 0$ or $c = 0$ then the determinant of $(a, b, c)$ is $b^2$, a square, hence $\ge 0$. -/
@[kb "gauss1801" "Art. 171"]
theorem art171_det_of_outer_zero {a b c : ℤ} (h : a = 0 ∨ c = 0) :
    gaussDet a b c = b ^ 2 ∧ 0 ≤ gaussDet a b c := by
  have : gaussDet a b c = b ^ 2 := by
    rcases h with rfl | rfl <;> simp [gaussDet]
  exact ⟨this, by rw [this]; positivity⟩

/-- **Gauss, *Disq. Arith.* Art. 171: a form of negative determinant has both outer
coefficients nonzero.** If $b^2 - ac < 0$ then $a \ne 0$ and $c \ne 0$. -/
@[kb "gauss1801" "Art. 171"]
theorem art171_outer_ne_zero {a b c : ℤ} (h : gaussDet a b c < 0) : a ≠ 0 ∧ c ≠ 0 := by
  constructor <;> intro h0 <;> have := (art171_det_of_outer_zero (a := a) (b := b) (c := c) (by tauto)).2 <;> omega

/-- **Gauss, *Disq. Arith.* Art. 215: the determinant of an implicated form.** If
$(a, b, c)$ implicates $(a', b', c')$, i.e. the substitution $x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$
carries $(a, b, c)$ to $(a', b', c')$, then
$$b'^2 - a'c' = (\alpha\delta - \beta\gamma)^2\,(b^2 - ac),$$
so the determinant of $(a, b, c)$ divides that of $(a', b', c')$; and if $(a, b, c)$ has determinant $0$, so has
every form it implicates. -/
@[kb "gauss1801" "Art. 215"]
theorem art215_det_implicated {a b c a' b' c' : ℤ} (α β γ δ : ℤ)
    (h : subst α β γ δ (gaussForm a b c) = gaussForm a' b' c') :
    gaussDet a' b' c' = (α * δ - β * γ) ^ 2 * gaussDet a b c ∧ gaussDet a b c ∣ gaussDet a' b' c' ∧
      (gaussDet a b c = 0 → gaussDet a' b' c' = 0) := by
  rw [subst_gaussForm] at h
  obtain ⟨rfl, rfl, rfl⟩ := gaussForm_inj h
  have e := gaussDet_subst a b c α β γ δ
  refine ⟨e, ⟨(α * δ - β * γ) ^ 2, by rw [e]; ring⟩, fun h0 => by rw [e, h0]; ring⟩

/-- **Divisibility of the three coefficients under a substitution** (used for Art. 226): a common divisor of
$a, b, c$ divides $a', b', c'$. -/
theorem dvd_subst_gaussForm {a b c a' b' c' : ℤ} (α β γ δ : ℤ)
    (h : subst α β γ δ (gaussForm a b c) = gaussForm a' b' c') {d : ℤ} (h1 : d ∣ a) (h2 : d ∣ b) (h3 : d ∣ c) :
    d ∣ a' ∧ d ∣ b' ∧ d ∣ c' := by
  rw [subst_gaussForm] at h
  obtain ⟨rfl, rfl, rfl⟩ := gaussForm_inj h
  obtain ⟨x, rfl⟩ := h1
  obtain ⟨y, rfl⟩ := h2
  obtain ⟨z, rfl⟩ := h3
  exact ⟨⟨x * α ^ 2 + 2 * y * α * γ + z * γ ^ 2, by ring⟩,
    ⟨x * α * β + y * (α * δ + β * γ) + z * γ * δ, by ring⟩,
    ⟨x * β ^ 2 + 2 * y * β * δ + z * δ ^ 2, by ring⟩⟩

/-- **Divisibility of $a, 2b, c$ under a substitution** (used for Art. 226): a common divisor of $a, 2b, c$ divides
$a', 2b', c'$. -/
theorem dvd_subst_gaussForm' {a b c a' b' c' : ℤ} (α β γ δ : ℤ)
    (h : subst α β γ δ (gaussForm a b c) = gaussForm a' b' c') {d : ℤ} (h1 : d ∣ a) (h2 : d ∣ 2 * b)
    (h3 : d ∣ c) : d ∣ a' ∧ d ∣ 2 * b' ∧ d ∣ c' := by
  rw [subst_gaussForm] at h
  obtain ⟨rfl, rfl, rfl⟩ := gaussForm_inj h
  obtain ⟨x, rfl⟩ := h1
  obtain ⟨y, hy⟩ := h2
  obtain ⟨z, rfl⟩ := h3
  refine ⟨⟨x * α ^ 2 + y * α * γ + z * γ ^ 2, ?_⟩, ⟨x * (2 * α * β) + y * (α * δ + β * γ) + z * (2 * γ * δ), ?_⟩,
    ⟨x * β ^ 2 + y * β * δ + z * δ ^ 2, ?_⟩⟩
  · linear_combination (α * γ) * hy
  · linear_combination (α * δ + β * γ) * hy
  · linear_combination (β * δ) * hy

/-- The greatest common divisor $\gcd(a, b, c)$ of three integers, as a natural number. -/
def gcd3 (a b c : ℤ) : ℕ := Int.gcd (Int.gcd a b) c

theorem dvd_gcd3 (d a b c : ℤ) : d ∣ (gcd3 a b c : ℤ) ↔ d ∣ a ∧ d ∣ b ∧ d ∣ c := by
  unfold gcd3
  constructor
  · intro h
    have e1 := Int.gcd_dvd_left (↑(Int.gcd a b)) c
    have e2 := Int.gcd_dvd_right (↑(Int.gcd a b)) c
    exact ⟨h.trans (e1.trans (Int.gcd_dvd_left a b)), h.trans (e1.trans (Int.gcd_dvd_right a b)), h.trans e2⟩
  · rintro ⟨h1, h2, h3⟩
    exact Int.dvd_coe_gcd (Int.dvd_coe_gcd h1 h2) h3

theorem gcd3_eq_of_iff {a b c a' b' c' : ℤ} (h : ∀ d : ℤ, (d ∣ a ∧ d ∣ b ∧ d ∣ c) ↔ (d ∣ a' ∧ d ∣ b' ∧ d ∣ c')) :
    gcd3 a b c = gcd3 a' b' c' := by
  apply Nat.dvd_antisymm
  · rw [← Int.natCast_dvd_natCast, dvd_gcd3, ← h]; exact (dvd_gcd3 _ a b c).mp dvd_rfl
  · rw [← Int.natCast_dvd_natCast, dvd_gcd3, h]; exact (dvd_gcd3 _ a' b' c').mp dvd_rfl

/-- **Gauss's order of a form** (*Disq. Arith.* Art. 226): the triple
$(b^2 - ac,\ \gcd(a, b, c),\ \gcd(a, 2b, c))$ of the determinant and the two greatest common divisors; forms with
the same triple belong to the same order. (Gauss's *orders* are distinguished by these three numbers; the form is
*properly primitive* when $\gcd(a, 2b, c) = 1$.) -/
@[kb "gauss1801" "Art. 226"]
def gaussOrder (a b c : ℤ) : ℤ × ℕ × ℕ := (gaussDet a b c, gcd3 a b c, gcd3 a (2 * b) c)

/-- **The order is invariant under a substitution with an inverse:** if $(a, b, c)$ goes to $(a', b', c')$ by
$x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$ and back by $(\alpha', \beta', \gamma', \delta')$, the orders
agree. -/
theorem gaussOrder_eq_of_subst {a b c a' b' c' : ℤ} (α β γ δ α' β' γ' δ' : ℤ)
    (h : subst α β γ δ (gaussForm a b c) = gaussForm a' b' c')
    (h' : subst α' β' γ' δ' (gaussForm a' b' c') = gaussForm a b c)
    (hd : (α * δ - β * γ) ^ 2 = 1) :
    gaussOrder a b c = gaussOrder a' b' c' := by
  have hdet := (art215_det_implicated α β γ δ h).1
  rw [hd, one_mul] at hdet
  unfold gaussOrder
  refine Prod.ext hdet.symm (Prod.ext ?_ ?_)
  · exact gcd3_eq_of_iff fun d => ⟨fun ⟨h1, h2, h3⟩ => dvd_subst_gaussForm α β γ δ h h1 h2 h3,
      fun ⟨h1, h2, h3⟩ => dvd_subst_gaussForm α' β' γ' δ' h' h1 h2 h3⟩
  · exact gcd3_eq_of_iff fun d => ⟨fun ⟨h1, h2, h3⟩ => dvd_subst_gaussForm' α β γ δ h h1 h2 h3,
      fun ⟨h1, h2, h3⟩ => dvd_subst_gaussForm' α' β' γ' δ' h' h1 h2 h3⟩

/-- **The order is invariant under proper equivalence** (*Disq. Arith.* Art. 226): properly equivalent forms have
the same determinant, the same $\gcd(a, b, c)$ and the same $\gcd(a, 2b, c)$. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_order_of_sl {a b c a' b' c' : ℤ} (h : SLEquiv (gaussForm a b c) (gaussForm a' b' c')) :
    gaussOrder a' b' c' = gaussOrder a b c := by
  obtain ⟨p, q, r, s, hd, hs⟩ := (sLEquiv_iff _ _).mp h
  have hback : subst s (-q) (-r) p (gaussForm a' b' c') = gaussForm a b c := by
    rw [← hs, subst_subst,
      show p * s + q * -r = 1 by linarith, show p * -q + q * p = 0 by ring,
      show r * s + s * -r = 0 by ring, show r * -q + s * p = 1 by linarith, subst_one]
  exact (gaussOrder_eq_of_subst s (-q) (-r) p p q r s hback hs (by
    have : s * p - -q * -r = 1 := by linarith
    rw [this]; norm_num)).symm.symm

/-- **The opposite form has the same order** (*Disq. Arith.* Art. 226): $(a, -b, c)$ has the determinant, the
$\gcd(a, b, c)$ and the $\gcd(a, 2b, c)$ of $(a, b, c)$. -/
theorem gaussOrder_opposite (a b c : ℤ) : gaussOrder a (-b) c = gaussOrder a b c := by
  unfold gaussOrder
  refine Prod.ext (by simp [gaussDet]) (Prod.ext ?_ ?_)
  · exact gcd3_eq_of_iff fun d => by simp only [dvd_neg]
  · exact gcd3_eq_of_iff fun d => by
      simp only [mul_neg, dvd_neg]

/-- **Gauss, *Disq. Arith.* Art. 226: opposite classes belong to the same order.** If
$(a', b', c')$ is properly equivalent to the form $(a, -b, c)$ opposite to $(a, b, c)$, then it has the same order
as $(a, b, c)$: the same determinant, the same $\gcd(a, b, c)$ and the same $\gcd(a, 2b, c)$. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_opposite_same_order {a b c a' b' c' : ℤ}
    (h : SLEquiv (gaussForm a (-b) c) (gaussForm a' b' c')) :
    gaussOrder a' b' c' = gaussOrder a b c :=
  (art226_order_of_sl h).trans (gaussOrder_opposite a b c)

end QuadFormsKB.Historical.Gauss
