/-
# Kitaoka 1993, Propositions 1.5.1 and 1.5.3: pure quaternions, and when $(a, b)$ splits

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.5, Proposition 1.5.1 (p. 24) and Proposition 1.5.3
(p. 26) (printed pages).

**Setting.** $F$ is a field of characteristic $\ne 2$ (`(2 : F) ≠ 0`; Kitaoka's standing assumption from §1.4 on) and
$C = (\alpha, \beta)$, $\alpha, \beta \in F^\times$, the quaternion algebra with basis $1, x_1, x_2, x_3$,
$x_1^2 = \alpha$, $x_2^2 = \beta$, $x_3 = x_1x_2 = -x_2x_1$: Mathlib's `ℍ[F,α,β]` $= ℍ[F,\alpha,0,\beta]$ with
$x = a_0 + a_1x_1 + a_2x_2 + a_3x_3$ having `x.re` $= a_0$, `x.imI` $= a_1$, `x.imJ` $= a_2$, `x.imK` $= a_3$.
$C^0 = Fx_1 + Fx_2 + Fx_3$ is the set of pure quaternions (`x.re = 0`); $F \subset C$ through the scalars
`(c : ℍ[F,α,β])`. The norm form is `Kitaoka.quatNorm α β` ($N(x) = a_0^2 - \alpha a_1^2 - \beta a_2^2 +
\alpha\beta a_3^2$) and its pure part `Kitaoka.quatNormPure α β` ($\langle -\alpha\rangle \perp \langle -\beta\rangle
\perp \langle \alpha\beta\rangle$ on $F^3$).

**Proves** (unconditional).
* `proposition151` (Proposition 1.5.1): $C^0 = \{x \in C : x^2 \in F,\ x \notin F\} \cup \{0\}$.
* `proposition153` (Proposition 1.5.3): for $a, b \in F^\times$ the following are equivalent:
  (i) $(a, b) \cong (1, -1)$ as $F$-algebras; (ii) $(a, b)$ is not a division algebra (some $x \ne 0$ is not a unit);
  (iii) $(a, b)$ is isotropic for $N$; (iv) $(a, b)^0$ is isotropic for $N$; (v) $\langle a\rangle \perp \langle b\rangle$
  represents $1$; (vi) $a \in N_{F'/F}(F'^\times)$ for $F' = F(\sqrt b)$, written $a = x^2 - by^2$ with $x, y \in F$
  (the norm of $x + y\sqrt b$; when $b$ is a square, $F' = F$ and both sides are all of $F^\times$).

**Proof.** Proposition 1.5.1: Kitaoka's computation $x^2 = (a_0^2 + \alpha a_1^2 + \beta a_2^2 - \alpha\beta a_3^2) +
2a_0(a_1x_1 + a_2x_2 + a_3x_3)$. Proposition 1.5.3: each condition is shown equivalent to $(a, b)_F = 1$
(`hilbertSymbol F a b = 1`): (i) and (iii) by the library's splitting criteria `Quat.nonempty_algEquiv_matrix_iff` and
`Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero` (since $(1, -1)$ is split, $(a, b) \cong (1, -1)$ iff
$(a, b) \cong M_2(F)$), (v) by `hilbertSymbol_eq_one_iff_conic`; (ii) $\Leftrightarrow$ (iii) because
$x\bar x = N(x)$; (iv) and (vi) by Kitaoka's explicit substitutions ($ax^2 + by^2 = 1$ gives the isotropic pure vector
$(by, ax, 1)$ and, for $x \ne 0$, $a = x^{-2} - b(y/x)^2$).
-/
import QuadFormsKB.Literature.Kitaoka.Wave2.Ch1Quaternion
import QuadFormsKB.Tamagawa.Quaternion

open Quaternion

noncomputable section

namespace QuadFormsKB.Kitaoka.Quaternion153

variable {F : Type} [Field F]

/-- **Kitaoka 1993, Proposition 1.5.1** (p. 24). In a quaternion algebra $C = (\alpha, \beta)$ over a field of
characteristic $\ne 2$, an element $x$ is pure ($x \in C^0 = Fx_1 + Fx_2 + Fx_3$) if and only if $x = 0$, or $x^2 \in F$
and $x \notin F$. Unconditional. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.1, p. 24"]
theorem proposition151 (h2 : (2 : F) ≠ 0) (α β : F) (x : ℍ[F,α,β]) :
    x.re = 0 ↔ x = 0 ∨ ((∃ c : F, x * x = (c : ℍ[F,α,β])) ∧ ¬ ∃ c : F, x = (c : ℍ[F,α,β])) := by
  constructor
  · intro h0
    by_cases hx : x = 0
    · exact Or.inl hx
    refine Or.inr ⟨⟨(x * x).re, ?_⟩, ?_⟩
    · ext <;> simp [h0] <;> ring
    · rintro ⟨c, rfl⟩
      apply hx
      have : c = 0 := by simpa using h0
      simp [this]
  · rintro (rfl | ⟨⟨c, hc⟩, hnot⟩)
    · rfl
    have e1 := congrArg QuaternionAlgebra.imI hc
    have e2 := congrArg QuaternionAlgebra.imJ hc
    have e3 := congrArg QuaternionAlgebra.imK hc
    simp at e1 e2 e3
    by_contra hre
    apply hnot
    have hI : x.imI = 0 := by
      have : (2 * x.re) * x.imI = 0 := by linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd ((mul_eq_zero.mp h).resolve_left h2) hre
      · exact h
    have hJ : x.imJ = 0 := by
      have : (2 * x.re) * x.imJ = 0 := by linear_combination e2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd ((mul_eq_zero.mp h).resolve_left h2) hre
      · exact h
    have hK : x.imK = 0 := by
      have : (2 * x.re) * x.imK = 0 := by linear_combination e3
      rcases mul_eq_zero.mp this with h | h
      · exact absurd ((mul_eq_zero.mp h).resolve_left h2) hre
      · exact h
    exact ⟨x.re, by ext <;> simp [hI, hJ, hK]⟩

section Prop153

variable {a b : F}

/-- $(C, N)^0$ in coordinates: $-a y_0^2 - b y_1^2 + ab y_2^2$. -/
theorem quatNormPure_eq (y : Fin 3 → F) :
    quatNormPure a b y = -a * y 0 ^ 2 - b * y 1 ^ 2 + a * b * y 2 ^ 2 := by
  simp [quatNormPure, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_three]
  ring

/-- Kitaoka's norm form is the library's reduced norm. -/
theorem quatNorm_eq_nrd (x : ℍ[F,a,b]) : quatNorm a b x = Quat.nrd x := by
  rw [quatNorm_apply]; rfl

/-- $(1, -1)$ is split. -/
theorem hilbertSymbol_one_neg_one (h2 : (2 : F) ≠ 0) : hilbertSymbol F 1 (-1) = 1 :=
  (hilbertSymbol_eq_one_iff_conic F h2 one_ne_zero (neg_ne_zero.mpr one_ne_zero)).mpr ⟨1, 0, by ring⟩

/-- (i) $\Leftrightarrow (a, b)_F = 1$. -/
theorem cond_i_iff (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,1,-1]) ↔ hilbertSymbol F a b = 1 := by
  obtain ⟨e₁⟩ := (Quat.nonempty_algEquiv_matrix_iff h2 one_ne_zero (neg_ne_zero.mpr one_ne_zero)).mpr
    (hilbertSymbol_one_neg_one h2)
  rw [← Quat.nonempty_algEquiv_matrix_iff h2 ha hb]
  exact ⟨fun ⟨e⟩ => ⟨e.trans e₁⟩, fun ⟨e⟩ => ⟨e.trans e₁.symm⟩⟩

/-- (iii) $\Leftrightarrow (a, b)_F = 1$. -/
theorem cond_iii_iff (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x : ℍ[F,a,b], x ≠ 0 ∧ quatNorm a b x = 0) ↔ hilbertSymbol F a b = 1 := by
  simp only [quatNorm_eq_nrd]
  exact (Quat.hilbertSymbol_eq_one_iff_exists_nrd_eq_zero h2 ha hb).symm

/-- $\bar x x = N(x)$. -/
theorem star_mul_eq_nrd (x : ℍ[F,a,b]) : star x * x = ((Quat.nrd x : F) : ℍ[F,a,b]) := by
  ext <;> simp only [QuaternionAlgebra.re_coe, QuaternionAlgebra.imI_coe, QuaternionAlgebra.imJ_coe,
    QuaternionAlgebra.imK_coe] <;> simp [Quat.nrd] <;> ring

/-- (ii) $\Leftrightarrow$ (iii): a nonzero $x$ is a non-unit iff $N(x) = 0$. -/
theorem cond_ii_iff_iii :
    (∃ x : ℍ[F,a,b], x ≠ 0 ∧ ¬ IsUnit x) ↔ (∃ x : ℍ[F,a,b], x ≠ 0 ∧ quatNorm a b x = 0) := by
  simp only [quatNorm_eq_nrd]
  constructor
  · rintro ⟨x, hx, hu⟩
    refine ⟨x, hx, ?_⟩
    by_contra hn
    apply hu
    have h₁ : x * ((Quat.nrd x)⁻¹ • star x) = 1 := by
      rw [mul_smul_comm, Quat.mul_star_eq_nrd, ← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
        inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]
    have h₂ : ((Quat.nrd x)⁻¹ • star x) * x = 1 := by
      rw [smul_mul_assoc, star_mul_eq_nrd, ← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul,
        inv_mul_cancel₀ hn, QuaternionAlgebra.coe_one]
    exact ⟨⟨x, _, h₁, h₂⟩, rfl⟩
  · rintro ⟨x, hx, hn⟩
    refine ⟨x, hx, fun hu => hx ?_⟩
    have h := Quat.mul_star_eq_nrd x
    rw [hn, QuaternionAlgebra.coe_zero] at h
    have hs : star x = 0 := by
      have := congrArg (fun y => hu.unit⁻¹.1 * y) h
      simpa [← mul_assoc] using this
    simpa using congrArg star hs

/-- (iv) $\Leftrightarrow$ (v). -/
theorem cond_iv_iff_v (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∃ y : Fin 3 → F, y ≠ 0 ∧ quatNormPure a b y = 0) ↔ hilbertSymbol F a b = 1 := by
  constructor
  · rintro ⟨y, hy, hq⟩
    rw [← cond_iii_iff h2 ha hb]
    refine ⟨⟨0, y 0, y 1, y 2⟩, fun h => hy ?_, ?_⟩
    · have e0 := congrArg QuaternionAlgebra.imI h
      have e1 := congrArg QuaternionAlgebra.imJ h
      have e2 := congrArg QuaternionAlgebra.imK h
      simp at e0 e1 e2
      funext i; fin_cases i <;> simp [e0, e1, e2]
    · rw [quatNorm_apply]
      rw [quatNormPure_eq] at hq
      show (0 : F) ^ 2 - a * y 0 ^ 2 - b * y 1 ^ 2 + a * b * y 2 ^ 2 = 0
      linear_combination hq
  · intro h
    obtain ⟨x, y, hxy⟩ := (hilbertSymbol_eq_one_iff_conic F h2 ha hb).mp h
    refine ⟨![b * y, a * x, 1], fun h0 => (one_ne_zero : (1 : F) ≠ 0) (by simpa using congrFun h0 2), ?_⟩
    rw [quatNormPure_eq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    linear_combination (-(a * b)) * hxy

/-- (vi) $\Leftrightarrow$ (v). -/
theorem cond_vi_iff_v (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ x y : F, a = x ^ 2 - b * y ^ 2) ↔ ∃ x y : F, a * x ^ 2 + b * y ^ 2 = 1 := by
  constructor
  · rintro ⟨x, y, hxy⟩
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := by rintro rfl; simp at hxy; exact ha hxy
      -- $b(Y^2 - (yX)^2) = 1$ with $Y - yX = 1$, $Y + yX = b^{-1}$
      refine ⟨(b⁻¹ - 1) / (2 * y), (1 + b⁻¹) / 2, ?_⟩
      rw [hxy]
      field_simp
      ring
    · refine ⟨x⁻¹, y / x, ?_⟩
      rw [hxy]
      field_simp
      ring
  · rintro ⟨x, y, hxy⟩
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := by rintro rfl; simp at hxy
      -- $b = (1/y)^2$, and $a = X^2 - (Y/y)^2$ with $X = (a + 1)/2$, $Y/y = (a - 1)/2$
      refine ⟨(a + 1) * 2⁻¹, y * ((a - 1) * 2⁻¹), ?_⟩
      have hb' : b * y ^ 2 = 1 := by simpa using hxy
      have hh : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      linear_combination ((2 : F)⁻¹ ^ 2 * (a - 1) ^ 2) * hb' + (-a * (1 + 2 * 2⁻¹)) * hh
    · refine ⟨x⁻¹, y / x, ?_⟩
      field_simp
      linear_combination hxy

/-- **Kitaoka 1993, Proposition 1.5.3** (p. 26). For a field $F$ of characteristic $\ne 2$ and $a, b \in F^\times$, the
following are equivalent:
(i) $(a, b) \cong (1, -1)$ as $F$-algebras;
(ii) $(a, b)$ is not a division algebra: some $x \ne 0$ in $(a, b)$ is not invertible;
(iii) $(a, b)$ is isotropic as a quadratic space for the norm $N$;
(iv) $(a, b)^0$ is isotropic for $N$;
(v) $\langle a\rangle \perp \langle b\rangle$ represents $1$;
(vi) $a \in N_{F'/F}(F'^\times)$ for $F' = F(\sqrt b)$, i.e. $a = x^2 - by^2$ for some $x, y \in F$.
Unconditional. -/
@[kb "kitaoka1993" "§1.5, Prop. 1.5.3, p. 26"]
theorem proposition153 (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    List.TFAE [Nonempty (ℍ[F,a,b] ≃ₐ[F] ℍ[F,1,-1]),
      ∃ x : ℍ[F,a,b], x ≠ 0 ∧ ¬ IsUnit x,
      ∃ x : ℍ[F,a,b], x ≠ 0 ∧ quatNorm a b x = 0,
      ∃ y : Fin 3 → F, y ≠ 0 ∧ quatNormPure a b y = 0,
      ∃ x y : F, a * x ^ 2 + b * y ^ 2 = 1,
      ∃ x y : F, a = x ^ 2 - b * y ^ 2] := by
  have hv := hilbertSymbol_eq_one_iff_conic F h2 ha hb
  tfae_have 1 ↔ 5 := (cond_i_iff h2 ha hb).trans hv
  tfae_have 2 ↔ 3 := cond_ii_iff_iii
  tfae_have 3 ↔ 5 := (cond_iii_iff h2 ha hb).trans hv
  tfae_have 4 ↔ 5 := (cond_iv_iff_v ha hb h2).trans hv
  tfae_have 6 ↔ 5 := cond_vi_iff_v h2 ha hb
  tfae_finish

end Prop153

end QuadFormsKB.Kitaoka.Quaternion153
