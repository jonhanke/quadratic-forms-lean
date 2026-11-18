import QuadFormsKB.Historical.Gauss.Orders

/-!
# Complements to the orders of Gauss's forms (Disquisitiones Arithmeticae, Arts. 226 and 256)

Art. 256 I and Art. 226, two recorded loose ends. These complete `Orders.lean`.

* **Simplest forms satisfy the hypotheses of Art. 256 I.** In `Orders.lean` the hypothesis
  $A \mid C$ is part of `IsGaussSimplestForm`. Here it is derived for the actual simplest forms of an order, the
  forms of `art226_order_realized_iff` (`gaussOrder_proper_rep`, `gaussOrder_improper_rep`):
  `isGaussSimplestForm_proper` ($m\,(1, 0, -e) = (m, 0, -me)$), `isGaussSimplestForm_improper`
  ($m\,(2, 1, 2k) = (2m, m, 2mk)$), the versions in terms of the order $(D, m, m')$
  (`gaussSimplestProper_of_order`, `gaussSimplestImproper_of_order`), and the restatements of
  `art256_admissible` for them (`art256_admissible_proper`, `art256_admissible_improper`).
* **The number of orders for $D$ alone.** `art226_number_of_orders_of_ne_zero` states Gauss's count of
  `art226_number_of_orders_product` for any nonzero $D$ by producing the decomposition $D = D' s^2$,
  $s = 2^{\mu} u$ itself (existential statement; the decomposition is unique, but uniqueness is not stated).

Everything is proved; nothing is assumed.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Row : the actual simplest forms are simplest forms -/

/-- **The properly primitive simplest form is of simplest shape** (Gauss, *Disq. Arith.* Art. 256 I, the historical sources
): for $m > 0$ the form $m\,(1, 0, -e) = (m, 0, -me)$ satisfies
`IsGaussSimplestForm`; in particular $A = m$ divides $C = -me$ (derived, not assumed). -/
@[kb "gauss1801" "Art. 256"]
theorem isGaussSimplestForm_proper (m : ℕ) (hm : 0 < m) (e : ℤ) :
    IsGaussSimplestForm (m : ℤ) 0 (-((m : ℤ) * e)) :=
  ⟨by exact_mod_cast hm, ⟨-e, by ring⟩, Or.inl rfl⟩

/-- **The improperly primitive simplest form is of simplest shape** (Gauss, *Disq. Arith.* Art. 256 I, the historical sources
): for $m > 0$ the form $m\,(2, 1, 2k) = (2m, m, 2mk)$ satisfies
`IsGaussSimplestForm` ($A = 2m$, $2B = A$, $A \mid C$ derived). -/
@[kb "gauss1801" "Art. 256"]
theorem isGaussSimplestForm_improper (m : ℕ) (hm : 0 < m) (k : ℤ) :
    IsGaussSimplestForm (2 * (m : ℤ)) m (2 * m * k) :=
  ⟨by have : (0 : ℤ) < m := by exact_mod_cast hm
      omega, ⟨k, rfl⟩, Or.inr rfl⟩

/-- **The simplest form of the order $(D, m, m)$** (Gauss, *Disq. Arith.* Arts. 226 and 256 I, the historical sources
): if $m > 0$ and $m^2 \mid D$ then the form $m\,(1, 0, -D/m^2)$ has order
$(D, m, m)$ and is of simplest shape (`IsGaussSimplestForm`, with $A \mid C$ derived). -/
@[kb "gauss1801" "Art. 256"]
theorem gaussSimplestProper_of_order (D : ℤ) (m : ℕ) (hm : 0 < m) (h : (m : ℤ) ^ 2 ∣ D) :
    IsGaussSimplestForm (m : ℤ) 0 (-((m : ℤ) * (D / (m : ℤ) ^ 2))) ∧
      gaussOrder (m : ℤ) 0 (-((m : ℤ) * (D / (m : ℤ) ^ 2))) = (D, m, m) := by
  obtain ⟨e, rfl⟩ := h
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ hm0]
  exact ⟨isGaussSimplestForm_proper m hm e, gaussOrder_proper_rep m e⟩

/-- **The simplest form of the order $(D, m, 2m)$** (Gauss, *Disq. Arith.* Arts. 226 and 256 I, the historical sources
): if $m > 0$, $m^2 \mid D$ and $D/m^2 \equiv 1 \pmod 4$ then the form
$m\,(2, 1, (1 - D/m^2)/2) = (2m, m, 2m k)$ with $k = (1 - D/m^2)/4$ has order $(D, m, 2m)$ and is of simplest shape
(`IsGaussSimplestForm`, with $A \mid C$ derived). -/
@[kb "gauss1801" "Art. 256"]
theorem gaussSimplestImproper_of_order (D : ℤ) (m : ℕ) (hm : 0 < m) (h : (m : ℤ) ^ 2 ∣ D)
    (h4 : D / (m : ℤ) ^ 2 % 4 = 1) :
    IsGaussSimplestForm (2 * (m : ℤ)) m (2 * m * ((1 - D / (m : ℤ) ^ 2) / 4)) ∧
      gaussOrder (2 * (m : ℤ)) m (2 * m * ((1 - D / (m : ℤ) ^ 2) / 4)) = (D, m, 2 * m) := by
  obtain ⟨e, rfl⟩ := h
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := by positivity
  rw [Int.mul_ediv_cancel_left _ hm0] at h4 ⊢
  refine ⟨isGaussSimplestForm_improper m hm _, ?_⟩
  rw [gaussOrder_improper_rep]
  have hk : (1 : ℤ) - 4 * ((1 - e) / 4) = e := by omega
  rw [hk]

/-- **Art. 256 I for the properly primitive simplest form** (Gauss, *Disq. Arith.* Art. 256 I, the historical sources
): for the form $(m, 0, -me)$, $m > 0$, the first coefficient is admissible:
$\gcd(m, 0, -me) = m$ (so also $\gcd(A, 2B, C) = A = m$) and $m^2 \mid \det = m^2 e$. This is the `B = 0` half of
`art256_admissible`, now without assuming $A \mid C$. -/
@[kb "gauss1801" "Art. 256"]
theorem art256_admissible_proper (m : ℕ) (hm : 0 < m) (e : ℤ) :
    (gcd3 (m : ℤ) (2 * 0) (-((m : ℤ) * e)) : ℤ) = m ∧ (gcd3 (m : ℤ) 0 (-((m : ℤ) * e)) : ℤ) = m ∧
      (m : ℤ) ^ 2 ∣ gaussDet (m : ℤ) 0 (-((m : ℤ) * e)) :=
  (art256_admissible (isGaussSimplestForm_proper m hm e)).1 rfl

/-- **Art. 256 I for the improperly primitive simplest form** (Gauss, *Disq. Arith.* Art. 256 I, the historical sources
): for the form $(2m, m, 2mk)$, $m > 0$: $A = 2m$ is even,
$\gcd(A, 2B, C) = A$, $2 \gcd(A, B, C) = A$, $B^2 \mid \det$, $\det/B^2 \equiv 1 \pmod 4$ and
$4 \det / A^2 = \det / B^2$. This is the `2B = A` half of `art256_admissible`, now without assuming $A \mid C$. -/
@[kb "gauss1801" "Art. 256"]
theorem art256_admissible_improper (m : ℕ) (hm : 0 < m) (k : ℤ) :
    Even (2 * (m : ℤ)) ∧ (gcd3 (2 * (m : ℤ)) (2 * m) (2 * m * k) : ℤ) = 2 * m ∧
      2 * (gcd3 (2 * (m : ℤ)) m (2 * m * k) : ℤ) = 2 * m ∧
      (m : ℤ) ^ 2 ∣ gaussDet (2 * (m : ℤ)) m (2 * m * k) ∧
      gaussDet (2 * (m : ℤ)) m (2 * m * k) / (m : ℤ) ^ 2 % 4 = 1 ∧
      4 * gaussDet (2 * (m : ℤ)) m (2 * m * k) / (2 * (m : ℤ)) ^ 2 =
        gaussDet (2 * (m : ℤ)) m (2 * m * k) / (m : ℤ) ^ 2 :=
  (art256_admissible (isGaussSimplestForm_improper m hm k)).2 rfl

/-! ### Row : the number of orders for a nonzero determinant -/

/-- **The number of orders of determinant $D$, for any nonzero $D$ alone** (Gauss, *Disq. Arith.* Art. 226,
the historical sources): for every integer $D \ne 0$ there are $D'$ squarefree and natural
numbers $s$, $\mu$, $u$ with $u$ odd, $D = D' s^2$, $s = 2^{\mu} u$, and the number of orders of determinant $D$ is
$(\mu + 2) \prod_{p \mid u} (v_p(u) + 1)$ if $D' \equiv 1 \pmod 4$ and $(\mu + 1) \prod_{p \mid u} (v_p(u) + 1)$
otherwise (`art226_number_of_orders_product`). The decomposition is produced from $D$ (Mathlib
`exists_sq_mul_squarefree` applied to $|D|$ and `Nat.exists_eq_two_pow_mul_odd`; $D'$ carries the sign of $D$); it is
stated existentially, uniqueness of $(D', s)$ is not part of the statement. -/
@[kb "gauss1801" "Art. 226"]
theorem art226_number_of_orders_of_ne_zero {D : ℤ} (hD : D ≠ 0) :
    ∃ (D' : ℤ) (s μ u : ℕ), D = D' * (s : ℤ) ^ 2 ∧ Squarefree D' ∧ s = 2 ^ μ * u ∧ Odd u ∧
      (gaussOrdersOfDet D).ncard =
        (if D' % 4 = 1 then μ + 2 else μ + 1) * ∏ p ∈ u.primeFactors, (u.factorization p + 1) := by
  obtain ⟨b, a, hab, hsq⟩ := exists_sq_mul_squarefree D.natAbs
  have hb0 : b ≠ 0 := by
    rintro rfl
    have : D.natAbs = 0 := by rw [← hab]; simp
    exact hD (Int.natAbs_eq_zero.mp this)
  obtain ⟨μ, u, hu, hbu⟩ := Nat.exists_eq_two_pow_mul_odd hb0
  have hab' : (b : ℤ) ^ 2 * a = D.natAbs := by exact_mod_cast hab
  obtain ⟨D', hDeq, hsqf⟩ : ∃ D' : ℤ, D = D' * (b : ℤ) ^ 2 ∧ Squarefree D' := by
    rcases Int.natAbs_eq D with h | h
    · refine ⟨a, ?_, Int.squarefree_natAbs.mp (by simpa using hsq)⟩
      rw [mul_comm, hab']; exact h
    · refine ⟨-a, ?_, Int.squarefree_natAbs.mp (by simpa using hsq)⟩
      rw [neg_mul, mul_comm, hab']; exact h
  refine ⟨D', b, μ, u, hDeq, hsqf, hbu, hu, ?_⟩
  have := art226_number_of_orders_product hsqf hu hbu
  rwa [← hDeq] at this

end QuadFormsKB.Historical.Gauss