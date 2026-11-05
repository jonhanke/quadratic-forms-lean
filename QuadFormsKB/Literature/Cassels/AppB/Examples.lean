/-
# Cassels, Appendix B, Examples 3 and 5 (partial)

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), Examples, pp. 389-390.

**Formalized.** Example 3 (the unique nontrivial real character modulo an odd prime, and $\tau(\chi, p)^2 = \chi(-1)p$);
Example 5: the Fourier transform $F$ on $\mathbb Z/n$, $F^2$ the reflection $k \mapsto -k$ (ii), $F^4 = I$ and the eigenvalues
are fourth roots of unity (i), and the identity $\sum_j e(j^2/p) = \tau(\chi, p)$ behind the trace formula (iii).

**Formalized elsewhere:** Example 1 (`AppB/Ex1Ex4.lean`, unconditional form in `AppB/GaussSum.lean`),
Example 2 (`AppB/Ex2.lean`, with an erratum in (ii)), Example 4 (`AppB/Ex1Ex4.lean`), Example 5 (i)–(v) and (vi) for
$n \not\equiv 0 \pmod 4$ (`AppB/Ex5Schur.lean`: Schur's determination of the sign of the quadratic Gauss sum); the Gauss
sum (2.20) of `Sec2Lemmas.lean` is proved in `AppB/GaussSum.lean`. Not formalized: the sign in Example 5 (vi) for
$n \equiv 0 \pmod 4$ (only $\pm(1+i)\sqrt n$).
-/
import QuadFormsKB.Binary.KroneckerChar

open Complex

namespace QuadFormsKB.Cassels


/-- Helper: the quadratic (Legendre) character modulo a prime $p$ as a complex-valued Dirichlet character
$\chi : \mathbb Z/p \to \mathbb C$ (values $0, \pm1$). -/
noncomputable def quadDir (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- **Cassels, Appendix B, Example 3, first part (p. 389).** For an odd prime $p$, every real-valued character
$\chi \ne 1$ modulo $p$ equals the quadratic character: apart from the trivial character there is exactly one real-valued
character modulo $p$ (the case $p = 2$ is excluded: there is no nontrivial character modulo $2$, so the printed "precisely
one" fails for $p = 2$). Arguments: `p` the odd prime, `χ` the character (Mathlib `MulChar (ZMod p) ℂ`),
`hχ1 : χ ≠ 1`, `hreal` that all values are real. Existence is `quadDir` (the Legendre symbol). -/
@[kb "cassels1978" "App. B, Ex. 3 (first part), p. 389 (the unique nontrivial real character mod an odd prime)"]
theorem real_char_eq_quad (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (χ : MulChar (ZMod p) ℂ)
    (hχ1 : χ ≠ 1) (hreal : ∀ r, (χ r).im = 0) : χ = quadDir p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  -- values on units are ±1
  have hpm : ∀ u : (ZMod p)ˣ, χ u = 1 ∨ χ u = -1 := by
    intro u
    have h1 : (χ u) ^ (p - 1) = 1 := by
      rw [← map_pow]
      have : (u : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one (by simp)
      simp [this]
    have hn : ‖χ u‖ = 1 := norm_eq_one_of_pow_eq_one h1 (by have := hp.out.two_le; omega)
    have him := hreal u
    have hre : (χ u).re ^ 2 = 1 := by
      have := Complex.sq_norm (χ u)
      rw [hn, Complex.normSq_apply] at this
      nlinarith
    have : (χ u).re = 1 ∨ (χ u).re = -1 := by
      have : ((χ u).re - 1) * ((χ u).re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases this with h | h
    · left; exact Complex.ext (by simpa using h) (by simpa using him)
    · right; exact Complex.ext (by simpa using h) (by simpa using him)
  -- a fixed nonsquare
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  have hqa : quadraticChar (ZMod p) a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have hsq : ∀ x : ZMod p, x ≠ 0 → IsSquare x → χ x = 1 := by
    rintro x hx ⟨w, hw⟩
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw; exact hx hw
    have := hpm (Units.mk0 w hw0)
    rw [hw, map_mul]
    simp only [Units.val_mk0] at this
    rcases this with h | h <;> rw [h] <;> norm_num
  have hsqprod : ∀ x : ZMod p, x ≠ 0 → ¬ IsSquare x → IsSquare (x * a⁻¹) := by
    intro x hx hxs
    have hqx : quadraticChar (ZMod p) x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxs
    have h1 : IsSquare (x * a) := by
      rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hx ha0), map_mul, hqx, hqa]; norm_num
    obtain ⟨w, hw⟩ := h1
    exact ⟨w * a⁻¹, by
      have : x * a⁻¹ = (x * a) * (a⁻¹ * a⁻¹) := by field_simp
      rw [this, hw]; ring⟩
  have hnonsq : ∀ x : ZMod p, x ≠ 0 → ¬ IsSquare x → χ x = χ a := by
    intro x hx hxs
    have h := hsq _ (mul_ne_zero hx (inv_ne_zero ha0)) (hsqprod x hx hxs)
    rw [map_mul] at h
    have hai : χ a ≠ 0 := by
      have := hpm (Units.mk0 a ha0); simp only [Units.val_mk0] at this
      rcases this with h | h <;> rw [h] <;> norm_num
    have : χ a⁻¹ * χ a = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ha0, MulChar.map_one]
    -- χ x = χ a
    have h2 : χ x * χ a⁻¹ * χ a = χ a := by rw [h, one_mul]
    rw [mul_assoc, this, mul_one] at h2
    exact h2
  have hχa : χ a = -1 := by
    have := hpm (Units.mk0 a ha0); simp only [Units.val_mk0] at this
    rcases this with h | h
    · exfalso
      apply hχ1
      refine MulChar.ext' (fun x => ?_)
      by_cases hx : x = 0
      · subst hx; rw [MulChar.map_zero, MulChar.map_zero]
      · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
        by_cases hxs : IsSquare x
        · exact hsq x hx hxs
        · rw [hnonsq x hx hxs, h]
    · exact h
  refine MulChar.ext' (fun x => ?_)
  by_cases hx : x = 0
  · subst hx; rw [MulChar.map_zero]; simp [quadDir]
  · by_cases hxs : IsSquare x
    · rw [hsq x hx hxs]
      simp [quadDir, (quadraticChar_one_iff_isSquare hx).mpr hxs]
    · rw [hnonsq x hx hxs, hχa]
      simp [quadDir, quadraticChar_neg_one_iff_not_isSquare.mpr hxs]

/-- **Cassels, Appendix B, Example 3, second part (p. 389):** for the nontrivial real character $\chi$ modulo a prime $p$,
$\tau(\chi, p)^2 = \chi(-1)\,p$ where $\tau(\chi, p) = \sum_{r \bmod p}\chi(r)\,e(r/p)$, $e(x) = e^{2\pi i x}$
(`ZMod.stdAddChar r` $= e(r/p)$). Mathlib's `gaussSum_sq` applied to the primitive additive character. Arguments: `p` the
prime, `χ` the character with `hχ1 : χ ≠ 1` and `hq : χ.IsQuadratic` (values in $\{0, \pm1\}$; by `real_char_eq_quad` this
is the unique nontrivial real character for $p$ odd). -/
@[kb "cassels1978" "App. B, Ex. 3 (second part), p. 389 (τ(χ,p)² = χ(−1)p)"]
theorem gauss_sq (p : ℕ) [hp : Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ1 : χ ≠ 1) (hq : χ.IsQuadratic) :
    (∑ r : ZMod p, χ r * ZMod.stdAddChar r) ^ 2 = χ (-1) * p := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := gaussSum_sq hχ1 hq (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at this
  exact this

/-- **Cassels, Appendix B, Example 5 (p. 390): the Fourier transform** $F$ on functions $\mathbb Z/n \to \mathbb C$,
$(F\Phi)_k = \frac{1}{\sqrt n}\sum_j \Phi_j\,e(jk/n)$. Indices are the residues $j, k \in \mathbb Z/n$ (Cassels' $0, \dots,
n-1$; `ZMod.stdAddChar (j * k)` $= e(jk/n)$). Argument `n`: the length ($n > 1$ in the book; any $n \ge 1$ here). -/
noncomputable def dftF (n : ℕ) [NeZero n] (Φ : ZMod n → ℂ) : ZMod n → ℂ :=
  fun k => ((Real.sqrt n : ℝ) : ℂ)⁻¹ * ∑ j : ZMod n, Φ j * ZMod.stdAddChar (j * k)

/-- **Cassels, Appendix B, Example 5 (ii) (p. 390), first part:** $F^2$ is the reflection $\Phi_k \mapsto \Phi_{-k}$
(printed as the transformation $(a_0, a_1, \dots, a_{n-1}) \mapsto (a_0, a_{n-1}, \dots, a_1)$). -/
@[kb "cassels1978" "App. B, Ex. 5 (ii), p. 390 (F² is the reflection a_j ↦ a_{−j})"]
theorem dftF_dftF (n : ℕ) [NeZero n] (Φ : ZMod n → ℂ) : dftF n (dftF n Φ) = fun k => Φ (-k) := by
  classical
  funext k
  have hsq : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
    exact_mod_cast this.ne'
  have hsq2 : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = n := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]; simp
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  set c : ℂ := ((Real.sqrt n : ℝ) : ℂ) with hc
  have h1 : ∀ j : ZMod n, (c⁻¹ * ∑ i : ZMod n, Φ i * ZMod.stdAddChar (i * j)) * ZMod.stdAddChar (j * k) =
      c⁻¹ * ∑ i : ZMod n, Φ i * ZMod.stdAddChar (j * (i + k)) := by
    intro j
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have h2 : dftF n (dftF n Φ) k = c⁻¹ * ∑ j : ZMod n, c⁻¹ * ∑ i : ZMod n, Φ i * ZMod.stdAddChar (j * (i + k)) := by
    show c⁻¹ * ∑ j : ZMod n, (c⁻¹ * ∑ i : ZMod n, Φ i * ZMod.stdAddChar (i * j)) * ZMod.stdAddChar (j * k) = _
    exact congrArg _ (Finset.sum_congr rfl (fun j _ => h1 j))
  rw [h2]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar n)]
  rw [Finset.sum_eq_single (-k)]
  · have : (-k + k : ZMod n) = 0 := by ring
    rw [ite_eq_left this, ZMod.card, ← mul_assoc, ← sq, ← hsq2]
    field_simp
  · intro i _ hi
    have : i + k ≠ 0 := fun h => hi (by linear_combination h)
    rw [ite_eq_right this]; simp
  · simp

/-- **Cassels, Appendix B, Example 5 (i) (p. 390), first part:** $F^4 = I$. -/
@[kb "cassels1978" "App. B, Ex. 5 (i), p. 390 (F⁴ = I)"]
theorem dftF_pow_four (n : ℕ) [NeZero n] (Φ : ZMod n → ℂ) : dftF n (dftF n (dftF n (dftF n Φ))) = Φ := by
  rw [dftF_dftF, dftF_dftF]
  funext k; simp

/-- **Cassels, Appendix B, Example 5 (iii) (p. 390), the trace identity:** for an odd prime $p$,
$\sum_{j \bmod p} e(j^2/p) = \tau(\chi, p)$ with $\chi$ the quadratic character (`quadDir`), so that
$\operatorname{tr}F = \frac{1}{\sqrt p}\sum_j e(j^2/p) = \tau(\chi, p)/\sqrt p$ (the diagonal entries of $F$ are
$\frac1{\sqrt p}e(k^2/p)$). Uses $\#\{x : x^2 = r\} = 1 + \chi(r)$ (Mathlib `quadraticChar_card_sqrts`) and
$\sum_r e(r/p) = 0$. -/
@[kb "cassels1978" "App. B, Ex. 5 (iii), p. 390 (trace of F; Σ e(j²/p) = τ(χ,p))"]
theorem sum_sq_eq_gauss (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ x : ZMod p, (ZMod.stdAddChar (x * x) : ℂ) = ∑ r : ZMod p, quadDir p r * ZMod.stdAddChar r := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have h0 : ∑ r : ZMod p, (ZMod.stdAddChar r : ℂ) = 0 := by
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) 1 (ZMod.isPrimitive_stdAddChar p)
    simpa using this
  have h1 : ∑ x : ZMod p, (ZMod.stdAddChar (x * x) : ℂ) =
      ∑ r : ZMod p, ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = r)).card : ℂ) * ZMod.stdAddChar r := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x * x)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2] : ∀ x ∈ Finset.univ.filter (fun x : ZMod p => x * x = r), (ZMod.stdAddChar (x * x) : ℂ) = ZMod.stdAddChar r)]
    simp [sq]
  rw [h1]
  have h2 : ∀ r : ZMod p, ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = r)).card : ℂ) = quadDir p r + 1 := by
    intro r
    have := quadraticChar_card_sqrts hF r
    have h3 : (Finset.univ.filter (fun x : ZMod p => x ^ 2 = r)) = (({x : ZMod p | x ^ 2 = r} : Set (ZMod p)).toFinset) := by
      ext x; simp
    rw [h3]
    have h4 := congrArg (fun z : ℤ => (z : ℂ)) this
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at h4
    rw [h4]; simp [quadDir]
  simp_rw [h2, add_mul, Finset.sum_add_distrib, one_mul, h0, add_zero]

/-- Helper: $F$ is homogeneous: $F(c\Phi) = cF(\Phi)$. -/
theorem dftF_smul (n : ℕ) [NeZero n] (c : ℂ) (Φ : ZMod n → ℂ) : dftF n (c • Φ) = c • dftF n Φ := by
  funext k
  simp only [dftF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Cassels, Appendix B, Example 5 (i) (p. 390), eigenvalues:** every eigenvalue $\lambda$ of $F$ satisfies
$\lambda^4 = 1$, i.e. $\lambda \in \{i^\mu\}$. (The multiplicities $m_\mu$ and $\sum m_\mu = n$ are not formalized.) -/
@[kb "cassels1978" "App. B, Ex. 5 (i), p. 390 (eigenvalues are fourth roots of unity)"]
theorem dftF_eigenvalue (n : ℕ) [NeZero n] (lam : ℂ) (Φ : ZMod n → ℂ) (hΦ : Φ ≠ 0) (h : dftF n Φ = lam • Φ) :
    lam ^ 4 = 1 := by
  have h4 := dftF_pow_four n Φ
  have : dftF n (dftF n (dftF n (dftF n Φ))) = lam ^ 4 • Φ := by
    simp only [h, dftF_smul, smul_smul]
    congr 1; ring
  rw [h4] at this
  by_contra hne
  apply hΦ
  have h1 : (1 - lam ^ 4) • Φ = 0 := by rw [sub_smul, one_smul, ← this]; simp
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact absurd (by linear_combination -h2) hne
  · exact h2

end QuadFormsKB.Cassels
