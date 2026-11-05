import QuadFormsKB.Literature.Hanke2011Ternary.GlobalNF
import QuadFormsKB.Tamagawa.SquareClassParam
import QuadFormsKB.Tamagawa.SquareClassDuality
import QuadFormsKB.Tamagawa.SphericalLocal
import QuadFormsKB.Literature.HasseNorm.SquareClasses

/-!
# The Hilbert symbol $(-1, \alpha)_{\mathfrak p}$ at a non-dyadic place

For a non-dyadic finite place $v$ of a number field $F$ with $q_v = N\mathfrak p$:

* `isSquare_neg_one_iff`: $-1 \in F_v^{\times 2} \iff q_v \equiv 1 \pmod 4$;
* `hilbert_neg_one_nondyadic`: $(-1, \alpha)_v = \left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_v \alpha}$,
  where $\left(\frac{-1}{\mathfrak p}\right) = $ `epsOdd v`.
-/

open IsDedekindDomain NumberField

namespace QuadFormsKB.Hanke2011Ternary.NF

variable {F : Type} [Field F] [NumberField F]

/-- **$-1$ is a local square at a non-dyadic place iff $q_v \equiv 1 \pmod 4$.**
For $2 \notin \mathfrak p$, $-1 \in F_v^{\times 2} \iff \left(\tfrac{-1}{\mathfrak p}\right) = 1
\iff N\mathfrak p \equiv 1 \pmod 4$ (a unit is a square iff its residue is, by Hensel). -/
@[kb "omeara1963" "§63B, 63:11–63:13, p. 166 (Hilbert symbol at a non-dyadic place)"]
theorem isSquare_neg_one_iff (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    IsSquare (-1 : v.adicCompletion F) ↔ qv v % 4 = 1 := by
  classical
  have h2' : ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    intro h
    have := (LocalDensity.NF.π_pow_dvd_two_iff v 1).mp (by simpa using h)
    exact h2 (by simpa using this)
  let _ : Fintype (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
  have hch := LocalDensity.DVR.ringChar_residueField_ne_two (LocalDensity.NF.irreducible_π v) h2'
  have hcard : Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = qv v := by
    rw [← Nat.card_eq_fintype_card, HN.card_residueField]; rfl
  have hodd : qv v % 2 = 1 := hcard ▸ FiniteField.odd_card_of_char_ne_two hch
  have hres : IsSquare (-1 : v.adicCompletion F) ↔
      IsSquare (IsLocalRing.residue (v.adicCompletionIntegers F) (-1)) := by
    constructor
    · rintro ⟨x, hx⟩
      have hx1 : Valued.v x = 1 := by
        have h1 : Valued.v x * Valued.v x = 1 := by
          rw [← map_mul, ← hx, Valuation.map_neg, map_one]
        have hle : Valued.v x ≤ 1 := by
          by_contra h
          have h' : 1 < Valued.v x := lt_of_not_ge h
          exact absurd (h1 ▸ one_lt_mul h'.le h') (lt_irrefl _)
        have hge : 1 ≤ Valued.v x := by
          by_contra h
          have h' : Valued.v x < 1 := lt_of_not_ge h
          have : Valued.v x * Valued.v x < 1 := by
            calc _ < 1 * 1 := mul_lt_mul' hle h' (zero_le) one_pos
              _ = 1 := mul_one 1
          exact absurd h1 this.ne
        exact le_antisymm hle hge
      refine ⟨IsLocalRing.residue _ ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx1.le⟩, ?_⟩
      rw [← map_mul]; congr 1; apply Subtype.ext; exact hx
    · intro hsq
      obtain ⟨a, -, ha⟩ := LocalZeta.exists_sq_of_residue_isSquare v h2' (u := -1) (isUnit_one.neg) hsq
      refine ⟨(a : v.adicCompletion F), ?_⟩
      have := congrArg (fun z : v.adicCompletionIntegers F => (z : v.adicCompletion F)) ha
      simpa [sq] using this
  rw [hres, map_neg, map_one, FiniteField.isSquare_neg_one_iff, hcard]
  omega

open QuadFormsKB.SqDual in
/-- **Hilbert symbol $(-1, \alpha)_v$ at a non-dyadic place.**
$$(-1, \alpha)_v = \left(\frac{-1}{\mathfrak p}\right)^{\operatorname{ord}_v \alpha},$$
with $\left(\frac{-1}{\mathfrak p}\right) = $ `epsOdd v` $= \pm 1$ according as $q_v \equiv \pm 1 \pmod 4$.
Here `ordL v α` is $\log v(\alpha) = -\operatorname{ord}_v \alpha$ (sign irrelevant: $\varepsilon^{\pm k}$ agree). -/
@[kb "omeara1963" "§63B, 63:11–63:13, p. 166 (Hilbert symbol at a non-dyadic place)"]
theorem hilbert_neg_one_nondyadic (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (α : Fˣ) :
    (NFPlace.finite v).hilbert (-1 : F) (α : F) = ((epsOdd v ^ ordL v α : ℤˣ) : ℤ) := by
  have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  by_cases hsq : IsSquare (-1 : v.adicCompletion F)
  · have he : epsOdd v = 1 := by
      have := (isSquare_neg_one_iff v h2).mp hsq
      simp [epsOdd, negOneChar, this]
    rw [he, one_zpow, Units.val_one]
    obtain ⟨s, hs⟩ := hsq
    simp only [NFPlace.hilbert, hilbertSymbol]
    rw [if_pos]
    refine ⟨1, 0, s, ?_, ?_⟩
    · intro h; have := congrArg (fun p => p.1) h; simp at this
    · simp [hs, sq]
  · have he : epsOdd v = -1 := by
      have : ¬ qv v % 4 = 1 := fun h => hsq ((isSquare_neg_one_iff v h2).mpr h)
      simp [epsOdd, negOneChar, this]
    rw [he]
    obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
    have hval : v.valuation F ((π : 𝓞 F) : F) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]; exact hπ
    have hπ0 : ((π : 𝓞 F) : F) ≠ 0 := by
      intro h; rw [h, map_zero] at hval; exact WithZero.exp_ne_zero hval.symm
    let p : Fˣ := Units.mk0 _ hπ0
    have hp_ord : ordL v p = -1 := by
      show WithZero.log (v.valuation F ((π : 𝓞 F) : F)) = -1
      rw [hval, WithZero.log_exp]
    let G : Fˣ → ℤ := fun x => (NFPlace.finite v).hilbert (-1 : F) (x : F)
    have hmul : ∀ x y : Fˣ, G (x * y) = G x * G y := fun x y => by
      simp only [G, Units.val_mul]
      exact NFPlace.hilbert_mul_right _ hm1 x.ne_zero y.ne_zero
    have hunit : ∀ x : Fˣ, ordL v x = 0 → G x = 1 := fun x hx =>
      hilbert_units_nondyadic v h2 _ _ (by rw [Valuation.map_neg, map_one]) ((ordL_eq_zero_iff v x).mp hx)
    have hG1 : G 1 = 1 := hunit 1 (ordL_one v)
    have hGp : G p = -1 := by
      have := hilbert_unit_unif_eq_neg_one v h2 (-1) p (by simp [ordL, Valuation.map_neg])
        (by rw [hp_ord]; exact ⟨-1, by norm_num⟩) (by simpa using hsq)
      simpa [G] using this
    have hpow : ∀ m : ℤ, G (p ^ m) = (((-1 : ℤˣ) ^ m : ℤˣ) : ℤ) := by
      intro m
      induction m using Int.induction_on with
      | zero => simpa using hG1
      | succ m ih => rw [zpow_add_one, hmul, ih, hGp, zpow_add_one]; simp
      | pred m ih =>
        have h := hmul (p ^ (-(m : ℤ) - 1)) p
        rw [← zpow_add_one, sub_add_cancel, ih, hGp] at h
        have h' : ((((-1 : ℤˣ) ^ (-(m : ℤ)) : ℤˣ)) : ℤ) = G (p ^ (-(m : ℤ) - 1)) * (-1) := h
        have : G (p ^ (-(m : ℤ) - 1)) = - ((((-1 : ℤˣ) ^ (-(m : ℤ)) : ℤˣ)) : ℤ) := by linarith
        rw [this, zpow_sub_one]; simp
    set k := ordL v α with hk
    have hu : ordL v (α * p ^ k) = 0 := by rw [ordL_mul, ordL_zpow, hp_ord]; ring
    have hα : α = (α * p ^ k) * p ^ (-k) := by group
    have : G α = G (p ^ (-k)) := by
      conv_lhs => rw [hα]
      rw [hmul, hunit _ hu, one_mul]
    show G α = _
    rw [this, hpow, zpow_neg, Int.units_inv_eq_self]

#print axioms isSquare_neg_one_iff
#print axioms hilbert_neg_one_nondyadic

end QuadFormsKB.Hanke2011Ternary.NF
