import QuadFormsKB.Tamagawa.Unitary.HermDensityStab
import QuadFormsKB.Tamagawa.Unitary.FiniteCount

/-!
# The hermitian local density at the good places

**Layer:** $F$ a number field, $v$ a finite place with $2\notin\mathfrak p_v$, $H_0$ an integral hermitian matrix over
$\mathcal O_F[\omega]$ whose reduction mod $\mathfrak p_v$ has unit determinant. $q = N\mathfrak p_v$.

**Proves** (combining the Hensel stabilization `hermDensity_eq_of_good` with the orders of the finite unitary groups
`FiniteCount.card_unitary_split`, `FiniteCount.card_unitary_inert`):
* **`hermDensity_eq_split`**: if $-D$ is a nonzero square mod $\mathfrak p_v$ ($v$ splits in $E$),
  $\beta^h_v(\Lambda,\Lambda) = |GL_m(\mathbb F_q)|/q^{m^2} = \prod_{i=1}^m(1 - q^{-i})$;
* **`hermDensity_eq_inert`**: if $-D$ is not a square mod $\mathfrak p_v$ ($v$ inert in $E$),
  $\beta^h_v(\Lambda,\Lambda) = q^{m(m-1)/2}\prod_{i=1}^m(q^i-(-1)^i)/q^{m^2} = \prod_{i=1}^m(1-(-1)^iq^{-i})$.

These are the good-place values that, with $\lambda_v = L_v(1,\chi)^{-1} = 1-\chi(v)q^{-1}$, give
$\beta^h_v/\lambda_v = \prod_{i=2}^m(1-\chi(v)^iq^{-i})$ (Gan–Hanke–Yu 2001, (2.11): $L_v(M^\vee(1))^{-1} = q^{-\dim}\#\overline H_v(\mathbb F_q)$).
-/

open scoped QuadraticAlgebra

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Unitary

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (D : 𝓞 F) {m : ℕ} (v : HeightOneSpectrum (𝓞 F))
  (H₀ : Matrix (Fin m) (Fin m) (QuadO D))

instance isMaximal_pow_one : (v.asIdeal ^ 1).IsMaximal := by rw [pow_one]; exact v.isMaximal

/-- The residue field $\mathcal O_F/\mathfrak p_v$ (written $\mathcal O_F/\mathfrak p_v^1$, the ring of `repCountHerm` at $k = 1$). -/
abbrev resField : Type := 𝓞 F ⧸ v.asIdeal ^ 1

instance : Field (resField v) := Ideal.Quotient.field _

instance : Fintype (resField v) := by
  haveI : Finite (resField v) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    rw [pow_one]; exact v.ne_bot)
  exact Fintype.ofFinite _

theorem card_resField : Fintype.card (resField v) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Fintype.card_eq_nat_card]
  show Nat.card (𝓞 F ⧸ v.asIdeal ^ 1) = _
  rw [pow_one]

theorem ringChar_resField (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : ringChar (resField v) ≠ 2 := by
  intro hc
  apply h2
  have : ((2 : 𝓞 F) : resField v) = 0 := by
    have := ringChar.spec (resField v) 2
    rw [hc] at this
    exact_mod_cast this.mpr dvd_rfl
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at this
  exact this

theorem resQ_star (z : QuadO D) : resQ D v 1 (star z) = star (resQ D v 1 z) := by
  ext <;> simp [resQ]

theorem map_resQ_isHermitian (hH : H₀.IsHermitian) : (H₀.map (resQ D v 1)).IsHermitian := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, ← resQ_star]
  rw [← Matrix.conjTranspose_apply, hH.eq]

/-- **$\beta^h_v$ at a split good place**: $\beta^h_v(\Lambda,\Lambda) = |GL_m(\mathbb F_q)|/q^{m^2}$. -/
@[kb "ganhankeyu2001" "(2.11), p. 104 (L_v(M^∨(1))^{-1} = q^{-dim} #H̄_v(A_v/π_v); H_v = GL_m at split v)"]
theorem hermDensity_eq_split (hH : H₀.IsHermitian) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hdet : IsUnit (H₀.map (resQ D v 1)).det)
    (hsq : IsSquare (Ideal.Quotient.mk (v.asIdeal ^ 1) (-D) : resField v))
    (hne : (Ideal.Quotient.mk (v.asIdeal ^ 1) (-D) : resField v) ≠ 0) :
    hermDensity D H₀ v = (Nat.card (GL (Fin m) (resField v)) : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ m ^ 2 := by
  rw [hermDensity_eq_of_good D v H₀ hH h2 hdet, repCountHerm,
    FiniteCount.card_unitary_split hsq hne (ringChar_resField v h2) _ (map_resQ_isHermitian D v H₀ hH)
      hdet.ne_zero]

/-- **$\beta^h_v$ at an inert good place**:
$\beta^h_v(\Lambda,\Lambda) = q^{m(m-1)/2}\prod_{i=0}^{m-1}(q^{i+1}-(-1)^{i+1})/q^{m^2}$. -/
@[kb "ganhankeyu2001" "(2.11), p. 104 and Table 1 (#U_m(𝔽_q), v inert)"]
theorem hermDensity_eq_inert (hH : H₀.IsHermitian) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hdet : IsUnit (H₀.map (resQ D v 1)).det)
    (hsq : ¬ IsSquare (Ideal.Quotient.mk (v.asIdeal ^ 1) (-D) : resField v)) :
    hermDensity D H₀ v = ((Ideal.absNorm v.asIdeal : ℝ) ^ (m * (m - 1) / 2) *
      ∏ i ∈ Finset.range m, ((Ideal.absNorm v.asIdeal : ℝ) ^ (i + 1) - (-1) ^ (i + 1))) /
        (Ideal.absNorm v.asIdeal : ℝ) ^ m ^ 2 := by
  classical
  rw [hermDensity_eq_of_good D v H₀ hH h2 hdet, repCountHerm]
  have h := FiniteCount.card_unitary_inert hsq (ringChar_resField v h2) _ (map_resQ_isHermitian D v H₀ hH)
    hdet.ne_zero
  rw [card_resField] at h
  congr 1
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h'
  convert h' using 1

end QuadFormsKB.Tamagawa.Unitary
