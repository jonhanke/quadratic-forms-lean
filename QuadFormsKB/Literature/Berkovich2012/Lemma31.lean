import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Literature.Berkovich2012.SGenus
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Siegel.FourSquares

/-!
# Berkovich–Hanke–Jagy, Lemma 3.1 and Definition 3.2: derived parts

Source: A. Berkovich, J. Hanke and W. Jagy, arXiv:1010.1926v2 (bib key `berkovich2012`), §3.

This file proves two fields of the named input `SGenusStructure` (`Theorem61.lean`) from the definitions:

* `epsP_eq_legendre`: if a ternary integral form $Q'$ lies in the genus of $Q$, $p$ is a prime, and
  $Q \sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$ with $p \nmid \alpha$, then
  $\varepsilon_p(Q') = \left(\frac{-\alpha}{p}\right)$ (Definition 3.2 and Remark 3.4). Class version:
  `QClass.epsP_eq_legendre`.
* `local_good_of_disc`: for $p \nmid 2S$ and $B$ with $b^2 - 4ac = -8S$, the form $B(x,y) + 2Sz^2$
  is $\mathbb{Z}_p$-equivalent to $x^2 + y^2 + z^2$ (Lemma 3.1, first case).
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.Siegel Matrix

/-! ### $\varepsilon_p$ from the local structure -/

section Eps

variable (p : ℕ) [hp : Fact p.Prime]

private lemma map_eval' {R T : Type*} [CommRing R] [CommRing T] {n : ℕ} (f : R →+* T)
    (Q : QuadForm R n) (x : Fin n → R) :
    f (Q.eval x) = (Q.map f).eval (fun i => f (x i)) := by
  simp [QuadForm.evalIn, QuadForm.map, map_sum, apply_ite]

private lemma map_map_int' {R T : Type*} [CommRing R] [CommRing T] {n : ℕ} (f : R →+* T)
    (Q : QuadForm ℤ n) :
    (Q.map (Int.castRingHom R)).map f = Q.map (Int.castRingHom T) := by
  ext i j; simp [QuadForm.map]

/-- Evaluating the base change $D = \langle \alpha, \alpha p, p\rangle$ modulo $p$:
$D(w) \equiv \alpha w_0^2 \pmod p$. -/
private lemma toZMod_eval_D (α : ℤ) (w : Fin 3 → ℤ_[p]) :
    PadicInt.toZMod (((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])).eval w) =
      (α : ZMod p) * (PadicInt.toZMod (w 0)) ^ 2 := by
  have h : ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])).eval w =
      (α : ℤ_[p]) * w 0 ^ 2 + (α * p : ℤ) * w 1 ^ 2 + (p : ℤ) * w 2 ^ 2 := by
    have := Kneser.eval_diag (n := 3)
      (R := ℤ_[p]) ![(α : ℤ_[p]), ((α * p : ℤ) : ℤ_[p]), ((p : ℤ) : ℤ_[p])] w
    have e : (QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p]) =
        QuadForm.diag ![(α : ℤ_[p]), ((α * p : ℤ) : ℤ_[p]), ((p : ℤ) : ℤ_[p])] := by
      ext i j
      simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; fin_cases i <;> simp
      · simp [hij]
    rw [e, this, Fin.sum_univ_three]; simp
  rw [h]
  simp [map_add, map_mul, map_pow, map_intCast]

/-- **Key congruence.** If $Q'_{\mathbb{Z}_p} \sim D = \langle\alpha, \alpha p, p\rangle$ and
$v \in \mathbb{Z}^3$ has $p \nmid Q'(v)$, then
$\left(\frac{-Q'(v)}{p}\right) = \left(\frac{-\alpha}{p}\right)$. -/
private lemma legendre_eq_of_isometric (Q' : QuadForm ℤ 3) (α : ℤ)
    (h : IsometricGL (Q'.map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])))
    (v : Fin 3 → ℤ) (hv : ¬ (p : ℤ) ∣ Q'.eval v) :
    legendreSym p (-Q'.eval v) = legendreSym p (-α) := by
  obtain ⟨g, hg⟩ := h
  set w : Fin 3 → ℤ_[p] := (g⁻¹).val *ᵥ (fun i => ((v i : ℤ) : ℤ_[p])) with hw
  have h1 : (Q'.map (Int.castRingHom ℤ_[p])).eval (fun i => ((v i : ℤ) : ℤ_[p])) =
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])).eval w := by
    rw [← hg, hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have h2 := congrArg PadicInt.toZMod h1
  rw [toZMod_eval_D] at h2
  have h3 : PadicInt.toZMod ((Q'.map (Int.castRingHom ℤ_[p])).eval (fun i => ((v i : ℤ) : ℤ_[p]))) =
      ((Q'.eval v : ℤ) : ZMod p) := by
    rw [show (fun i => ((v i : ℤ) : ℤ_[p])) = fun i => Int.castRingHom ℤ_[p] (v i) from rfl,
      ← map_eval']
    simp
  have hne : ((Q'.eval v : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [h3] at h2
  have ht : PadicInt.toZMod (w 0) ≠ 0 := by
    intro h0; rw [h0] at h2; simp at h2; exact hne h2
  unfold legendreSym
  push_cast
  rw [show (-(Q'.eval v : ZMod p)) = (-(α : ZMod p)) * PadicInt.toZMod (w 0) ^ 2 by rw [h2]; ring,
    map_mul, quadraticChar_sq_one' ht, mul_one]

/-- **$\varepsilon_p$ from the local structure** (Definition 3.2 and Remark 3.4; Lemma 3.1): if $Q'$
is in the genus of the ternary form $Q$, and $Q \sim_{\mathbb{Z}_p} \alpha x^2 + \alpha p y^2 + p z^2$ with
$p \nmid \alpha$, then $\varepsilon_p(Q') = \left(\frac{-\alpha}{p}\right)$. -/
@[kb "berkovich2012" "§3, Lemma 3.1 and Definition 3.2, pp. 2–3"]
theorem epsP_eq_legendre {Q Q' : QuadForm ℤ 3} (hQ : SameGenus Q Q') {α : ℤ}
    (hα : ¬ (p : ℤ) ∣ α)
    (h : IsometricGL (Q.map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p]))) :
    epsP p Q' = legendreSym p (-α) := by
  classical
  have h' : IsometricGL (Q'.map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])) :=
    ((hQ.1 p).symm).trans h
  have hα0 : ((-α : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg]; exact hα
  -- existence of a value prime to p
  have hex : ∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ Q'.eval v := by
    obtain ⟨g, hg⟩ := h'
    set v₀ : Fin 3 → ℤ_[p] := g.val *ᵥ (Pi.single 0 1) with hv₀
    have hval : PadicInt.toZMod ((Q'.map (Int.castRingHom ℤ_[p])).eval v₀) = (α : ZMod p) := by
      rw [hv₀, hg, toZMod_eval_D]; simp
    choose v hv using fun i => ZMod.intCast_surjective (PadicInt.toZMod (v₀ i))
    refine ⟨v, fun hd => ?_⟩
    have e1 := map_eval' (PadicInt.toZMod) (Q'.map (Int.castRingHom ℤ_[p])) v₀
    rw [map_map_int'] at e1
    have e2 := map_eval' (Int.castRingHom (ZMod p)) Q' v
    have e3 : (fun i => PadicInt.toZMod (v₀ i)) = fun i => (Int.castRingHom (ZMod p)) (v i) := by
      funext i; simp [hv i]
    rw [e3, ← e2] at e1
    rw [hval] at e1
    have : ((Q'.eval v : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    simp at e1
    rw [this] at e1
    exact hα ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e1)
  have hcond : (∃ v : Fin 3 → ℤ, ¬ (p : ℤ) ∣ Q'.eval v ∧ legendreSym p (-Q'.eval v) = 1) ↔
      legendreSym p (-α) = 1 := by
    constructor
    · rintro ⟨v, hv, hl⟩
      rw [← legendre_eq_of_isometric p Q' α h' v hv]; exact hl
    · intro hl
      obtain ⟨v, hv⟩ := hex
      exact ⟨v, hv, by rw [legendre_eq_of_isometric p Q' α h' v hv]; exact hl⟩
  unfold epsP
  by_cases hl : legendreSym p (-α) = 1
  · rw [if_pos (hcond.mpr hl), hl]
  · rw [if_neg (fun h => hl (hcond.mp h))]
    rcases legendreSym.eq_one_or_neg_one p hα0 with h1 | h1
    · exact absurd h1 hl
    · exact h1.symm

/-- **Class version.** Every class in the genus of $Q$ has $\varepsilon_p = \left(\frac{-\alpha}{p}\right)$. -/
@[kb "berkovich2012" "§3, Lemma 3.1 and Definition 3.2, pp. 2–3"]
theorem QClass.epsP_eq_legendre {Q : QuadForm ℤ 3} {α : ℤ} (hα : ¬ (p : ℤ) ∣ α)
    (h : IsometricGL (Q.map (Int.castRingHom ℤ_[p]))
      ((QuadForm.diag ![α, α * p, (p : ℤ)]).map (Int.castRingHom ℤ_[p])))
    {c : QClass 3} (hc : c ∈ genusClasses Q) : QClass.epsP p c = legendreSym p (-α) := by
  obtain ⟨Q', rfl, hQ'⟩ := hc
  exact Berkovich2012.epsP_eq_legendre p hQ' hα h

end Eps

/-! ### The good primes $p \nmid 2S$ -/

section Good

variable (p : ℕ) [hp : Fact p.Prime]

private lemma hessian_map' {R T : Type*} [CommRing R] [CommRing T] {n : ℕ} (f : R →+* T)
    (Q : QuadForm R n) : (Q.map f).hessian = Q.hessian.map f := by
  ext i j; simp [QuadForm.hessian, QuadForm.map, Matrix.map_apply]

/-- The Hessian determinant of $B(x,y) + 2Sz^2$ with $b^2 - 4ac = -8S$ is $32 S^2$. -/
private lemma hessian_det_sForm (S : ℕ) (B : BinQF) (hd : B.disc = -8 * S) :
    (sForm S B).hessian.det = 32 * (S : ℤ) ^ 2 := by
  simp [sForm, QuadForm.hessian, QuadForm.ofUpper, Matrix.det_fin_three]
  have : B.b ^ 2 - 4 * B.a * B.c = -8 * S := hd
  nlinarith

private lemma not_dvd_of_not_dvd_two_mul (S : ℕ) (hpS : ¬ p ∣ 2 * S) (k : ℤ)
    (hk : k = 32 * (S : ℤ) ^ 2) : ¬ (p : ℤ_[p]) ∣ (k : ℤ_[p]) := by
  intro hdvd
  have h0 : PadicInt.toZMod (k : ℤ_[p]) = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, hk] at h0
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h1 : (p : ℤ) ∣ 2 ^ 5 * (S : ℤ) ^ 2 := by
    have : (32 : ℤ) = 2 ^ 5 := by norm_num
    rwa [this] at h0
  rcases hp'.dvd_or_dvd h1 with h2 | h2
  · have h3 : (p : ℤ) ∣ 2 := hp'.dvd_of_dvd_pow h2
    exact hpS ((Int.natCast_dvd_natCast.mp (by exact_mod_cast h3 : (p : ℤ) ∣ ((2 : ℕ) : ℤ))).trans
      (dvd_mul_right 2 S))
  · have h3 : (p : ℤ) ∣ (S : ℤ) := hp'.dvd_of_dvd_pow h2
    exact hpS ((Int.natCast_dvd_natCast.mp h3).trans (dvd_mul_left S 2))

/-- **Lemma 3.1, case $p \nmid 2S$:** for $p \nmid 2S$ and a binary form $B$ with $b^2 - 4ac = -8S$, the
form $B(x,y) + 2Sz^2$ is $\mathrm{GL}_3(\mathbb{Z}_p)$-equivalent to $x^2 + y^2 + z^2$. Both are
$p$-unimodular with Gram determinants $4S^2$ and $1$ in the same square class, so this is the
classification of unimodular $\mathbb{Z}_p$-forms, $p$ odd (O'Meara 92:2; `isometricGL_of_unimodular`). -/
@[kb "berkovich2012" "§3, Lemma 3.1, p. 2"]
theorem local_good_of_disc (S : ℕ) (B : BinQF) (hd : B.disc = -8 * S) (hpS : ¬ p ∣ 2 * S) :
    IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[p]))
      ((sumSq 3).map (Int.castRingHom ℤ_[p])) := by
  have hp2 : p ≠ 2 := by
    rintro rfl; exact hpS (dvd_mul_right 2 S)
  set D1 : QuadForm ℤ_[p] 3 := QuadForm.diag ![((2 * S : ℤ) : ℤ_[p]) ^ 2, 1, 1] with hD1
  have hdet1 : D1.hessian.det = ((32 * (S : ℤ) ^ 2 : ℤ) : ℤ_[p]) := by
    simp [hD1, QuadForm.hessian, QuadForm.diag, Matrix.det_diagonal, Fin.prod_univ_three]
    ring
  have hdet0 : ((sForm S B).map (Int.castRingHom ℤ_[p])).hessian.det =
      ((32 * (S : ℤ) ^ 2 : ℤ) : ℤ_[p]) := by
    rw [hessian_map']
    show (RingHom.mapMatrix (Int.castRingHom ℤ_[p]) (sForm S B).hessian).det = _
    rw [← RingHom.map_det, hessian_det_sForm S B hd]; rfl
  have e1 : IsometricGL ((sForm S B).map (Int.castRingHom ℤ_[p])) D1 :=
    Kneser.isometricGL_of_unimodular hp2 _ _
      (by rw [hdet0]; exact not_dvd_of_not_dvd_two_mul p S hpS _ rfl) (hdet1.trans hdet0.symm)
  have hunit : IsUnit ((2 * S : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => ?_)
    rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
    exact hpS (by exact_mod_cast hlt)
  have e2 := Kneser.isometricGL_diag_scale (fun _ : Fin 3 => (1 : ℤ_[p])) 0 hunit.unit
  have e3 : (sumSq 3).map (Int.castRingHom ℤ_[p]) = QuadForm.diag (fun _ : Fin 3 => (1 : ℤ_[p])) := by
    ext i j
    simp only [sumSq, QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have e4 : QuadForm.diag (Function.update (fun _ : Fin 3 => (1 : ℤ_[p])) 0
      (((hunit.unit : ℤ_[p]ˣ) : ℤ_[p]) ^ 2 * 1)) = D1 := by
    rw [hD1]; congr 1; funext i; fin_cases i <;> simp
  rw [e3]
  exact e1.trans (e4 ▸ e2).symm

end Good

end QuadFormsKB.Berkovich2012
