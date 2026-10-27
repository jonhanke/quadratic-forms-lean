/-
# The character of a rank-2 complement: the ternary character, and the natural order over $\mathbb Q$

**Layer:** number fields; $\mathbb Q$.

**Proves**
* `chiForms_unary_eq_chiTern`: for a ternary $Q_0$ and $T_0 = \langle m\rangle$ ($H_T = (2m)$), the character `chiForms` of
  $\delta = -2m\det H_{Q_0}$ is the ternary character `chiTern Q₀ m` (Hanke's $\psi_m$), at every prime;
* `naturalOrderEulerOne_chiForms_rat_nondeg`: over $\mathbb Q$, for **every** nondegenerate $Q_0$, $T_0$ with
  $\delta = -\det H_{Q_0}\det H_{T_0}$ not a square (any signature), the prime ideal theorem for $\chi$ = `chiForms Q₀ T₀`
  (`NaturalOrderEulerOne`) holds: $\chi$ is a Kronecker character off a finite set
  (`naturalOrderEulerOne_of_almost_kron`). This extends `naturalOrderEulerOne_chiForms_rat` (positive definite) to
  indefinite forms.
-/
import QuadFormsKB.Tamagawa.FrameSiegelUncond

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Frames QuadFormsKB.RegProd LocalDensity
open QuadFormsKB.Tamagawa.RatHeadline3 QuadFormsKB.Binary QuadFormsKB.Tamagawa.BinaryTauRat RatBridge

theorem unary_det_hessian {F : Type} [Field F] [NumberField F] (m : 𝓞 F) :
    (DVR.unary m).hessian.det = 2 * m := by
  rw [Matrix.det_unique]; simp [DVR.unary, QuadForm.hessian, QuadForm.diag, two_mul]

/-- Any squarefree `s ≠ 1` gives a fundamental discriminant in its square class. -/
theorem exists_isQuadDisc_of_squarefree {s : ℤ} (hs : Squarefree s) (hs1 : s ≠ 1) :
    ∃ D : ℤ, IsQuadDisc D ∧ ∃ u w : ℤ, u ≠ 0 ∧ w ≠ 0 ∧ D * u ^ 2 = s * w ^ 2 := by
  have h4 : ¬ (4 : ℤ) ∣ s := by
    intro h
    have h' : (2 * 2 : ℤ) ∣ s := by simpa using h
    have := hs 2 h'
    exact absurd (Int.isUnit_iff.mp this) (by norm_num)
  by_cases h : s % 4 = 1
  · exact ⟨s, ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hs⟩), hs1⟩, 1, 1, one_ne_zero,
      one_ne_zero, by ring⟩
  · have e : 4 * s / 4 = s := by omega
    exact ⟨4 * s, ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inr ⟨by omega, by rwa [e], by omega⟩),
      by omega⟩, 1, 2, one_ne_zero, two_ne_zero, by ring⟩

/-- Every nonzero non-square integer is, up to squares, a fundamental discriminant. -/
theorem exists_isQuadDisc_sq_of_nonsq {n : ℤ} (hn : n ≠ 0) (hns : ¬ IsSquare n) :
    ∃ D : ℤ, IsQuadDisc D ∧ ∃ u w : ℤ, u ≠ 0 ∧ w ≠ 0 ∧ D * u ^ 2 = n * w ^ 2 := by
  obtain ⟨b, a, hb2a, hsq⟩ := exists_sq_mul_squarefree n.natAbs
  have hb0 : (b : ℤ) ≠ 0 := by
    rintro h
    have : b = 0 := by exact_mod_cast h
    subst this
    simp at hb2a
    omega
  have key : ∀ s : ℤ, Squarefree s → n = (b : ℤ) ^ 2 * s → ∃ D : ℤ, IsQuadDisc D ∧ ∃ u w : ℤ, u ≠ 0 ∧
      w ≠ 0 ∧ D * u ^ 2 = n * w ^ 2 := by
    intro s hs hns'
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hns ⟨b, by rw [hns']; ring⟩
    obtain ⟨D, hD, u, w, hu, hw, h⟩ := exists_isQuadDisc_of_squarefree hs hs1
    refine ⟨D, hD, u * b, w, mul_ne_zero hu hb0, hw, ?_⟩
    rw [hns']
    linear_combination ((b : ℤ) ^ 2) * h
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have e : n = (b : ℤ) ^ 2 * (-(a : ℤ)) := by
      have : (n.natAbs : ℤ) = -n := by omega
      rw [← hb2a] at this
      push_cast at this
      linarith
    exact key _ (Int.squarefree_natAbs.mp (by simpa using hsq)) e
  · have e : n = (b : ℤ) ^ 2 * (a : ℤ) := by
      have : (n.natAbs : ℤ) = n := by omega
      rw [← hb2a] at this
      push_cast at this
      linarith
    exact key _ (Int.squarefree_natCast.mpr hsq) e

/-- **`chiForms` of a ternary form and $\langle m\rangle$ is the ternary character** `chiTern Q₀ m`. -/
theorem chiForms_unary_eq_chiTern {F : Type} [Field F] [NumberField F] (Q₀ : QuadForm (𝓞 F) 3) (m : 𝓞 F) :
    chiForms Q₀ (DVR.unary m) = chiTern Q₀ m := by
  funext v
  have hδ : deltaForms Q₀ (DVR.unary m) = (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m := by
    unfold deltaForms
    rw [unary_det_hessian]; norm_num; ring
  rw [chiTern, Siegel.psiNF, chiForms, Siegel.IsGoodPrimeNF, hδ]
  by_cases hg : Siegel.IsGoodPrimeNF Q₀ v
  · have h2 : (2 : 𝓞 F) ∉ v.asIdeal := hg.1
    have hd : Q₀.hessian.det ∉ v.asIdeal := hg.2
    by_cases hm : m ∈ v.asIdeal
    · have hE : (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m ∈ v.asIdeal :=
        v.asIdeal.mul_mem_left _ hm
      rw [if_neg (fun h => h.2 hE), if_pos ⟨h2, hd⟩, charNF_eq_zero_of_mem v hE]
      simp
    · have hE : (-1) ^ ((3 - 1) / 2) * (2 * Q₀.hessian.det) * m ∉ v.asIdeal := by
        intro h
        rcases v.isPrime.mem_or_mem h with h | h
        · rcases v.isPrime.mem_or_mem h with h | h
          · exact absurd ((Ideal.eq_top_iff_one _).mpr (by simpa using h)) v.isPrime.ne_top
          · rcases v.isPrime.mem_or_mem h with h | h
            · exact h2 h
            · exact hd h
        · exact hm h
      rw [if_pos ⟨h2, hE⟩, if_pos ⟨h2, hd⟩]
  · rw [if_neg (fun h : 2 ∉ v.asIdeal ∧ Q₀.hessian.det ∉ v.asIdeal => hg h)]
    rw [if_neg]
    rintro ⟨h2, hE⟩
    apply hg
    refine ⟨h2, fun hd => hE ?_⟩
    exact v.asIdeal.mul_mem_right _ (v.asIdeal.mul_mem_left _ (v.asIdeal.mul_mem_left _ hd))

/-- **The prime ideal theorem for `chiForms` over $\mathbb Q$**, every signature: if
$\delta = -\det H_{Q_0}\det H_{T_0}$ is not a square in $\mathbb Q$, then `NaturalOrderEulerOne (chiForms Q₀ T₀)`. -/
theorem naturalOrderEulerOne_chiForms_rat_nondeg {N r : ℕ} (Q₀ : QuadForm (𝓞 ℚ) N) (T₀ : QuadForm (𝓞 ℚ) r)
    (hQ : Q₀.Nondegenerate) (hT : T₀.Nondegenerate)
    (hW : ¬ IsSquare (algebraMap (𝓞 ℚ) ℚ (deltaForms Q₀ T₀))) :
    NaturalOrderEulerOne (chiForms Q₀ T₀) := by
  have hδ0 := deltaForms_ne_zero hQ hT
  set n : ℤ := eZ (deltaForms Q₀ T₀) with hn
  have hδ : deltaForms Q₀ T₀ = ((n : ℤ) : 𝓞 ℚ) := by
    have := eZ_symm_apply (eZ (deltaForms Q₀ T₀))
    rw [eZ.symm_apply_apply] at this
    exact this
  have hn0 : n ≠ 0 := by
    intro h; apply hδ0; rw [hδ, h]; simp
  have hns : ¬ IsSquare n := by
    intro h
    apply hW
    rw [hδ, map_intCast]
    exact Rat.isSquare_intCast_iff.mpr h
  obtain ⟨D, hD, u, w, hu, hw, hDuw⟩ := exists_isQuadDisc_sq_of_nonsq hn0 hns
  have hN : (2 * n * u * w).natAbs ≠ 0 := by
    refine Int.natAbs_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hn0) hu) hw)
  have key : ∀ v ∉ (finite_natGenerator_dvd hN).toFinset, chiForms Q₀ T₀ v = kronChi D v := by
    intro v hv
    set p := Rat.HeightOneSpectrum.natGenerator v with hpdef
    have hpp : p.Prime := Rat.HeightOneSpectrum.prime_natGenerator v
    have : Fact p.Prime := ⟨hpp⟩
    have hndiv : ¬ (p : ℤ) ∣ 2 * n * u * w := fun h =>
      hv ((Set.Finite.mem_toFinset _).mpr (Int.natCast_dvd.mp h))
    have h2 : ¬ (p : ℤ) ∣ 2 := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_right h _) _) _)
    have hkd : ¬ (p : ℤ) ∣ n := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left h _) _) _)
    have hud : ¬ (p : ℤ) ∣ u := fun h => hndiv (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
    have hwd : ¬ (p : ℤ) ∣ w := fun h => hndiv (Dvd.dvd.mul_left h _)
    have hp2 : p ≠ 2 := fun h => h2 (by rw [h]; norm_num)
    have h2I : (2 : 𝓞 ℚ) ∉ v.asIdeal := by
      have := (intCast_mem_iff v 2).not.mpr h2
      simpa using this
    have hδI : deltaForms Q₀ T₀ ∉ v.asIdeal := by
      rw [hδ]; exact (intCast_mem_iff v n).not.mpr hkd
    rw [chiForms, if_pos ⟨h2I, hδI⟩, hδ, charNF_intCast_eq_legendreSym v hkd]
    have hleg : legendreSym p n = legendreSym p D := by
      have hu' : (u : ZMod p) ≠ 0 := fun h => hud ((ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp h)
      have hw' : (w : ZMod p) ≠ 0 := fun h => hwd ((ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp h)
      have := congrArg (legendreSym p) hDuw
      rwa [legendreSym.mul, legendreSym.mul, legendreSym.sq_one' p hu', legendreSym.sq_one' p hw', mul_one,
        mul_one, eq_comm] at this
    rw [kronChi, kronR, kronZ_odd_prime p hp2, hleg]
  have := hD
  exact (naturalOrderEulerOne_of_almost_kron (D := D) (abs_chiForms_le Q₀ T₀) _ key).1

end QuadFormsKB.Tamagawa.Indefinite
