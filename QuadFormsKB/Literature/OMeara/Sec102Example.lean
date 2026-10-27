/-
# O'Meara Example 102:6: local representations everywhere without a global one

**Layer:** $F = \mathbb Q$, $V = \mathbb Q^2$ with the form $Q(x, y) = x^2 + 11y^2$ (`omeara102_6Form`, a diagonal
`QuadForm ℚ 2`), and the lattice $L = \mathbb Z^2$ = `intVec` (O'Meara's $L \cong \langle 1\rangle \perp
\langle 11\rangle$), with all finite spots.

**Proves** Example 102:6 (O'Meara 1973, §102A, p. 300, `omeara102_6`): $V$ represents $3$, every localization
$L_p$ represents $3$, but $L$ does not represent $3$.

*Proof.* O'Meara uses $3 = (8/5)^2 + 11(1/5)^2$ at $p \ne 5$ and Corollary 92:1b at $p = 5$. Here a second rational
representation $3 = (1/2)^2 + 11(1/2)^2$ is used at $p \ne 2$, so that every local representation is by a rational
vector and no local theory is needed: $(1/2, 1/2) \in \mathbb Z_p^2$ for $p \ne 2$ and $(8/5, 1/5) \in \mathbb Z_2^2$.
Over $\mathbb Z$, $x^2 + 11y^2 = 3$ has no solution ($y = 0$ gives $x^2 = 3$; $y \ne 0$ gives a value $\ge 11$).
-/
import QuadFormsKB.Lattices.Finite

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

/-- **The form** $Q(x, y) = x^2 + 11y^2$ of Example 102:6. -/
def omeara102_6Form : QuadForm ℚ 2 := QuadForm.diag ![1, 11]

theorem omeara102_6Form_evalIn {K : Type*} [CommRing K] [Algebra ℚ K] (x : Fin 2 → K) :
    omeara102_6Form.evalIn K x = x 0 * x 0 + 11 * (x 1 * x 1) := by
  simp [omeara102_6Form, QuadForm.evalIn, QuadForm.diag, Fin.sum_univ_two, Matrix.diagonal, map_ofNat]
  ring

/-- $\lvert q/r\rvert_\mathfrak p \le 1$ for $q, r \in \mathcal O_F$ with $r \notin \mathfrak p$. -/
theorem valued_div_le_one {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (q : 𝓞 F)
    {r : 𝓞 F} (hr : r ∉ v.asIdeal) :
    Valued.v (algebraMap F (v.adicCompletion F) ((q : F) / (r : F))) ≤ 1 := by
  rw [valued_algebraMap, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.mpr hr, div_one]
  exact v.intValuation_le_one _

theorem omeara102_6Form_evalIn_locVec (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℚ) :
    omeara102_6Form.evalIn (v.adicCompletion ℚ) (locVec v ![a, b]) =
      algebraMap ℚ (v.adicCompletion ℚ) (a * a + 11 * (b * b)) := by
  rw [omeara102_6Form_evalIn]
  simp [locVec_apply, map_ofNat]

/-- **Example 102:6** (O'Meara 1973, §102A, p. 300): for $L = \mathbb Z^2$ on $V$ with $Q(x, y) = x^2 + 11y^2$, the
scalar $3$ is represented by $V$ and by $L_p$ at every prime $p$, but not by $L$. -/
@[kb "omeara1963" "§102A, 102:6, p. 300"]
theorem omeara102_6 :
    (∃ x : Fin 2 → ℚ, omeara102_6Form.eval x = 3) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ y ∈ loc v (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ)),
      omeara102_6Form.evalIn (v.adicCompletion ℚ) y = 3) ∧
    ¬ ∃ x ∈ (intVec : Submodule (𝓞 ℚ) (Fin 2 → ℚ)), omeara102_6Form.eval x = 3 := by
  refine ⟨⟨![1 / 2, 1 / 2], ?_⟩, fun v => ?_, ?_⟩
  · rw [QuadForm.eval, omeara102_6Form_evalIn]; norm_num
  · rw [loc_intVec]
    by_cases h2 : ((2 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · -- `p = 2`: use `(8/5, 1/5)`; `5 ∉ p` since `1 = 5 - 2 * 2`
      have h5 : ((5 : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
        intro h5
        apply v.isPrime.ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : 𝓞 ℚ) = ((5 : ℕ) : 𝓞 ℚ) - 2 * ((2 : ℕ) : 𝓞 ℚ) := by push_cast; ring
        rw [this]
        exact v.asIdeal.sub_mem h5 (v.asIdeal.mul_mem_left _ h2)
      refine ⟨locVec v ![8 / 5, 1 / 5], (mem_ball v).mpr fun i => ?_, ?_⟩
      · simp only [locVec_apply, neg_zero, WithZero.exp_zero]
        fin_cases i
        · convert valued_div_le_one v 8 (r := 5) (by exact_mod_cast h5) using 3; simp; first | norm_cast | simp [map_ofNat] | rfl
        · convert valued_div_le_one v 1 (r := 5) (by exact_mod_cast h5) using 3; simp; first | norm_cast | simp [map_ofNat] | rfl
      · rw [omeara102_6Form_evalIn_locVec]; norm_num
    · -- `p ≠ 2`: use `(1/2, 1/2)`
      refine ⟨locVec v ![1 / 2, 1 / 2], (mem_ball v).mpr fun i => ?_, ?_⟩
      · simp only [locVec_apply, neg_zero, WithZero.exp_zero]
        fin_cases i <;> convert valued_div_le_one v 1 (r := 2) (by exact_mod_cast h2) using 3 <;> simp <;> first | norm_cast | simp [map_ofNat] | rfl
      · rw [omeara102_6Form_evalIn_locVec]; norm_num
  · rintro ⟨x, hx, hQ⟩
    obtain ⟨a, ha⟩ := hx 0
    obtain ⟨b, hb⟩ := hx 1
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, ((k : ℤ) : 𝓞 ℚ) = b :=
      ⟨Rat.ringOfIntegersEquiv b, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply b)⟩
    rw [QuadForm.eval, omeara102_6Form_evalIn, ← ha, ← hb] at hQ
    simp only [map_intCast] at hQ
    have hZ : m * m + 11 * (k * k) = 3 := by exact_mod_cast hQ
    rcases eq_or_ne k 0 with rfl | hk
    · have : m * m = 3 := by linarith
      have hm : m ≤ 2 := by nlinarith
      have hm' : -2 ≤ m := by nlinarith
      interval_cases m <;> omega
    · have : 1 ≤ k * k := by nlinarith [mul_self_pos.mpr hk]
      nlinarith [mul_self_nonneg m]

end QuadFormsKB.Lattices
