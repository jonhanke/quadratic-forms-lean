/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import QuadFormsKB.Tamagawa.Odd7Units
import QuadFormsKB.Literature.Hanke2011Ternary.Global
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37
import QuadFormsKB.Literature.LocalGlobal.HasseConventionsNF

/-!
# Paper 7 at odd primes: the Hasse invariant of the genus of a tuple

For a place $v \nmid 2$ of $\mathbb Q$ ($p = p_v$) and a tuple $(a, b; u_1, u_2, u_3)$ of Lemma 2.1, the local genus
`tupG v c a b e₁ e₂ e₃` of $u_1x^2 + p^au_2y^2 + p^bu_3z^2$ has Hasse invariant (Serre's convention,
$\prod_{i<j}(a_i, a_j)_p$)
$$c_p = \varepsilon_1^{a+b}\varepsilon_2^{b}\varepsilon_3^{a}(\varepsilon')^{ab},\qquad \varepsilon' = \left(\tfrac{-1}{p}\right)
= \texttt{negOneChar}\ p,$$
i.e. `oddHasse (negOneChar p) a b e₁ e₂ e₃` (`hasse_tupG`; paper 7, Lemma 2.2, from `lemma_2_2_padic`).

Indices are 0-based.
-/

open IsDedekindDomain NumberField Matrix Finset

namespace QuadFormsKB.Odd7

open QuadFormsKB.Hanke2011Structure QuadFormsKB.Hanke2011Ternary QuadFormsKB.ConwaySloane
  QuadFormsKB.ConwaySloane.Mass Cassels QuadFormsKB.HilbertLocal QuadFormsKB.Siegel QuadFormsKB.Tamagawa

noncomputable section

section AtV

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- $(-1)^{(p-1)/2} = \left(\frac{-1}{p}\right)$ = `negOneChar p` for odd $p$. -/
theorem negOne_pow (hp2 : pv v ≠ 2) : ((-1 : ℤ) ^ ((pv v - 1) / 2)) = ((negOneChar (pv v) : ℤˣ) : ℤ) := by
  have hodd : pv v % 2 = 1 := (Fact.out : (pv v).Prime).eq_two_or_odd.resolve_left hp2
  unfold negOneChar
  by_cases h : pv v % 4 = 1
  · rw [if_pos h]
    have h' : (pv v - 1) / 2 = 2 * ((pv v - 1) / 4) := by omega
    rw [h', pow_mul]
    simp
  · rw [if_neg h]
    have h3 : pv v % 4 = 3 := by omega
    have h' : (pv v - 1) / 2 = 2 * ((pv v - 3) / 4) + 1 := by omega
    rw [h', pow_succ, pow_mul]
    simp

theorem unitChar_repU {c : ℤ} (hc : jacobiSym c (pv v) = -1) (e : ℤˣ) : unitChar (repU hc e) = (e : ℤ) := by
  have h : unitChar (repU hc e) = ((chiU (repU hc e) : ℤˣ) : ℤ) := rfl
  rw [h, chiU_repU]

theorem tupleVec_ne_zero {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ) (e₁ e₂ e₃ : ℤˣ) (i : Fin 3) :
    tupleVec (pv v) c a b e₁ e₂ e₃ i ≠ 0 := by
  have hpz : ((pv v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : (pv v).Prime).ne_zero
  have hr : ∀ e : ℤˣ, rep c e ≠ 0 := fun e h => not_dvd_rep hc e (h ▸ dvd_zero _)
  fin_cases i
  · exact hr e₁
  · exact mul_ne_zero (pow_ne_zero _ hpz) (hr e₂)
  · exact mul_ne_zero (pow_ne_zero _ hpz) (hr e₃)

/-- **Paper 7, Lemma 2.2 for the true local genera.** For $v \nmid 2$ and a Jordan tuple $(a, b; u_1, u_2, u_3)$ (any
$a, b$, any signs), the Hasse invariant of the genus of $u_1x^2 + p^au_2y^2 + p^bu_3z^2$ is
$c_p = \varepsilon_1^{a+b}\varepsilon_2^{b}\varepsilon_3^{a}(\varepsilon')^{ab}$ with $\varepsilon' = \left(\frac{-1}{p}\right)$
(`negOneChar p`): `oddHasse (negOneChar p) a b e₁ e₂ e₃`. Unconditional. -/
@[kb "hanke2011ternary" "§2, Lemma 2.2, p. 5 (Hasse invariant of the genus of a tuple)"]
theorem hasse_tupG (hv : (2 : 𝓞 ℚ) ∉ v.asIdeal) {c : ℤ} (hc : jacobiSym c (pv v) = -1) (a b : ℕ)
    (e₁ e₂ e₃ : ℤˣ) :
    (tupG v c a b e₁ e₂ e₃).hasse = ((oddHasse (negOneChar (pv v)) a b e₁ e₂ e₃ : ℤˣ) : ℤ) := by
  have hp2 := pv_ne_two v hv
  classical
  set d := tupleVec (pv v) c a b e₁ e₂ e₃ with hd
  have hnz : ∀ i, algebraMap ℚ Fv (((d i : ℤ) : ℚ)) ≠ 0 := by
    intro i
    refine (map_ne_zero _).2 ?_
    exact_mod_cast tupleVec_ne_zero hc a b e₁ e₂ e₃ i
  have hiso : ((tupleForm (pv v) c a b e₁ e₂ e₃).map (algebraMap ℤ 𝔬)).map (algebraMap 𝔬 Fv) =
      QuadForm.diag (fun i => algebraMap ℚ Fv (((d i : ℤ) : ℚ))) := by
    unfold tupleForm
    rw [map_diag_eq, map_diag_eq]
    congr 1
    funext i
    simp [hd]
  unfold tupG
  rw [LocGenus.hasse_mk, hasseForm, hiso, hasseC_diag v _ hnz]
  have e2 : PadicClass.hasseVec (fun i => algebraMap ℚ Fv (((d i : ℤ) : ℚ))) =
      (NFPlace.finite v).hasseSerre (fun i => ((d i : ℤ) : ℚ)) := by
    unfold NFPlace.hasseSerre PadicClass.hasseVec
    simp only [NFPlace.hilbert, eq_ratCast]
    try rfl
  rw [e2, NFPlace.hasseSerre_rat]
  have e3 : (NFPlace.finite v).toRatPlace.hasseSerre (fun i => ((d i : ℤ) : ℚ)) =
      hasseInvariant ℚ_[pv v] (fun i => ((d i : ℤ) : ℚ)) :=
    RatPlace.hasseSerre_finite (Rat.HeightOneSpectrum.primesEquiv v) _
  rw [e3]
  have e4 : hasseInvariant ℚ_[pv v] (fun i => ((d i : ℤ) : ℚ)) =
      PadicClass.hasseVec (fun i : Fin 3 => (((d i : ℤ) : ℚ) : ℚ_[pv v])) := rfl
  rw [e4]
  have key := lemma_2_2_padic hp2 a b (repU hc e₁) (repU hc e₂) (repU hc e₃)
  have e5 : PadicClass.hasseVec (fun i : Fin 3 => (((d i : ℤ) : ℚ) : ℚ_[pv v])) =
      hilbertSymbol ℚ_[pv v] ((rep c e₁ : ℤ) : ℚ_[pv v])
          (((pv v : ℕ) : ℚ_[pv v]) ^ a * ((rep c e₂ : ℤ) : ℚ_[pv v])) *
        hilbertSymbol ℚ_[pv v] ((rep c e₁ : ℤ) : ℚ_[pv v])
          (((pv v : ℕ) : ℚ_[pv v]) ^ b * ((rep c e₃ : ℤ) : ℚ_[pv v])) *
        hilbertSymbol ℚ_[pv v] (((pv v : ℕ) : ℚ_[pv v]) ^ a * ((rep c e₂ : ℤ) : ℚ_[pv v]))
          (((pv v : ℕ) : ℚ_[pv v]) ^ b * ((rep c e₃ : ℤ) : ℚ_[pv v])) := by
    simp [PadicClass.hasseVec, Fin.prod_univ_three, hd, tupleVec_zero, tupleVec_one, tupleVec_two]
  rw [e5]
  refine key.trans ?_
  rw [unitChar_repU hc, unitChar_repU hc, unitChar_repU hc, negOne_pow hp2]
  simp only [oddHasse, Units.val_mul, Units.val_pow_eq_pow_val]

end AtV

end

end QuadFormsKB.Odd7
