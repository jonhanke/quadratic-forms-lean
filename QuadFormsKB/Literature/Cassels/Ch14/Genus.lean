/-
# Cassels, Chapter 14, §3: duplication and the principal genus (Theorem 3.1)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §3, p. 339.

The *principal genus* (14.r6) is the genus of the principal form (1.11): the forms equivalent to it over every
$\mathbb Z_p$ and over $\mathbb R$ (`InPrincipalGenus`, with the library's genus `Siegel.SameGenus`, which uses
$\mathrm{GL}_2$ at every place as Cassels does). Gauss' duplication theorem (Theorem 3.1, `thm_3_1`): a class is a
square if and only if it lies in the principal genus. This is proved for every discriminant $D \ne 0$:

* "square $\Rightarrow$ principal genus" (`inPrincipalGenus_of_sq`): by Lemma 2.5 the class represents primitively
  some $w^2$ with $w$ prime to $2D$; over $\mathbb Z_p$ for $p \mid 2D$ and over $\mathbb R$ such a form is
  equivalent to the principal form, and for $p \nmid 2D$ all primitive forms of discriminant $D$ are
  $\mathbb Z_p$-equivalent (Lemma 3.1 (i), `Binary.isometricGL_padic_of_not_dvd`).
* "principal genus $\Rightarrow$ square" (`exists_sq_of_inPrincipalGenus`): Cassels uses Ch. 9, Thm. 7.1 (the
  alternative he names): $f$ and the principal form are equivalent over $\mathbb Q$ (strong Hasse principle,
  `isometric_iff_everywhere`) and over $\mathbb Z_p$ for $p \mid 2D$, hence over $\mathbb Z^{(P)}$
  (`Siegel.equivAway_of_local`), so $f$ represents primitively a square $w^2$ with $w$ prime to $2D$; then Lemma 2.5.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Literature.Cassels.Ch9Sec7
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel

/-- **The principal genus** (Cassels, Ch. 14, §3, p. 339): $f$ is in the principal genus if it is equivalent to the
principal form (1.11) of its discriminant over every $\mathbb Z_p$ and over $\mathbb R$ ("including
$p = \infty$"). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (the principal genus)"]
def InPrincipalGenus (f : BinQF) : Prop := Siegel.SameGenus f (principalForm f.disc)

/-- **Being in the principal genus is a class invariant.** -/
theorem InPrincipalGenus.of_sLEquiv {f g : BinQF} (h : SLEquiv f g) (hf : InPrincipalGenus f) :
    InPrincipalGenus g := by
  unfold InPrincipalGenus at *
  rw [← Composition.SLEquiv.disc_eq h]
  exact (h.intEquiv.sameGenus).symm.trans hf

/-- **A form $[w^2, b, c]$ is equivalent to the principal form wherever $w$ is a unit** (Cassels, Ch. 14, proof of
Thm. 3.1 (ii), p. 339: "$\mathfrak C$ represents $1$ over $\mathbb Z_p$"): for a commutative ring $R$ in which $w$ is
a unit, the substitution $x \mapsto w^{-1}x + kw^{-1}y$, $y \mapsto wy$ (determinant $1$) with $k = (\beta - b)/2$
and $\beta = D \bmod 2$ takes $[w^2, b, c]$ to the principal form (1.11) of its discriminant $D$. -/
theorem isometricGL_principal_of_isUnit {R : Type*} [CommRing R] {w b c : ℤ} (hu : IsUnit (w : R)) :
    IsometricGL ((BinQF.mk (w ^ 2) b c).map (Int.castRingHom R))
      ((principalForm (BinQF.mk (w ^ 2) b c).disc).map (Int.castRingHom R)) := by
  obtain ⟨u0, hu0⟩ := hu
  set u : R := ((u0⁻¹ : Rˣ) : R)
  have hwu : (w : R) * u = 1 := by rw [← hu0]; exact u0.mul_inv
  have huw : u * (w : R) = 1 := by rw [mul_comm]; exact hwu
  set β : ℤ := (BinQF.mk (w ^ 2) b c).disc % 2 with hβ
  have hβ' : β * β = β := by
    have : β = 0 ∨ β = 1 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  have hbk : ∃ k : ℤ, b = β - 2 * k := by
    have : (BinQF.mk (w ^ 2) b c).disc = b ^ 2 - 4 * w ^ 2 * c := rfl
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' b
    · refine ⟨-m, ?_⟩
      have : β = 0 := by simp only [hβ, BinQF.disc, a_mk, b_mk, c_mk, hm]; ring_nf; omega
      omega
    · refine ⟨-m, ?_⟩
      have : β = 1 := by simp only [hβ, BinQF.disc, a_mk, b_mk, c_mk, hm]; ring_nf; omega
      omega
  obtain ⟨k, hk⟩ := hbk
  have hc4 : (β - (BinQF.mk (w ^ 2) b c).disc) / 4 = β * k - k ^ 2 + w ^ 2 * c := by
    have : β - (BinQF.mk (w ^ 2) b c).disc = 4 * (β * k - k ^ 2 + w ^ 2 * c) := by
      simp only [BinQF.disc, a_mk, b_mk, c_mk]
      rw [hk]
      linear_combination (-1 : ℤ) * hβ'
    rw [this]; omega
  refine isometricGL_of_mat !![u, (k : R) * u; 0, (w : R)] !![(w : R), -((k : R) * u); 0, u] ?_ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hwu, huw]
    ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hwu, huw]
    ring
  · intro v
    rw [eval_map_two, eval_map_two]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      principalForm, a_mk, b_mk, c_mk]
    rw [show ((BinQF.mk (w ^ 2) b c).disc % 2 : ℤ) = β from rfl, hc4]
    rw [hk]
    simp only [Int.coe_castRingHom, Int.cast_pow, Int.cast_one, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_ofNat]
    linear_combination (((w : R) * u + 1) * (v 0 + (k : R) * v 1) ^ 2 +
      ((β : R) - 2 * k) * (v 0 + (k : R) * v 1) * v 1) * hwu

/-- **A primitive form representing $w^2$ with $w$ prime to $2D$ is in the principal genus** (Cassels, Ch. 14, proof of
Thm. 3.1 (ii), p. 339): over $\mathbb Z_p$ with $p \nmid w$ and over $\mathbb R$ by
`isometricGL_principal_of_isUnit`, and over $\mathbb Z_p$ with $p \mid w$ ($p$ odd, $p \nmid D$) by Lemma 3.1 (i)
(`Binary.isometricGL_padic_of_not_dvd`). -/
theorem inPrincipalGenus_of_eval_sq {f : BinQF} (hf : f.IsPrimitive) {w x y : ℤ} (hxy : IsCoprime x y)
    (hw : IsCoprime w (2 * f.disc)) (h : f.eval x y = w ^ 2) : InPrincipalGenus f := by
  obtain ⟨g, e, ha⟩ := exists_sLEquiv_a_of_eval (f := f) hxy
  rw [h] at ha
  have hdisc := Composition.SLEquiv.disc_eq e
  refine InPrincipalGenus.of_sLEquiv (Binary.SLEquiv.symm e) ?_
  have hg : g = BinQF.mk (w ^ 2) g.b g.c := BinQF.ext_abc (by simp [ha]) (by simp) (by simp)
  have hw' : IsCoprime w (2 * g.disc) := hdisc ▸ hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    have := (isCoprime_zero_left.mp hw')
    rcases Int.isUnit_iff.mp this with h1 | h1 <;> omega
  unfold InPrincipalGenus
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp : (p : ℤ) ∣ w
    · have hp1 : ¬ (p : ℤ) ∣ 2 * g.disc := by
        intro hd
        obtain ⟨a, b, hab⟩ := hw'
        have : (p : ℤ) ∣ 1 := by
          rw [← hab]; exact dvd_add (dvd_mul_of_dvd_right hp _) (dvd_mul_of_dvd_right hd _)
        have := Int.eq_one_of_dvd_one (by positivity) this
        have hp1 := (Fact.out : p.Prime).one_lt
        omega
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hp1 (dvd_mul_right _ _)
      exact isometricGL_padic_of_not_dvd hp2
        (principalForm_spec (BinQF.disc_mod_four g)).2.symm (fun hd => hp1 (dvd_mul_of_dvd_right hd _))
    · have hu : IsUnit ((w : ℤ) : ℤ_[p]) := by
        rw [PadicInt.isUnit_iff]
        have h1 := PadicInt.norm_le_one ((w : ℤ) : ℤ_[p])
        have h2 := PadicInt.norm_int_lt_one_iff_dvd (p := p) w
        exact le_antisymm h1 (not_lt.mp (fun hlt => hp (h2.mp hlt)))
      have key := isometricGL_principal_of_isUnit (R := ℤ_[p]) (w := w) (b := g.b) (c := g.c) hu
      rw [← hg] at key
      exact key
  · have hu : IsUnit ((w : ℤ) : ℝ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hw0)
    have key := isometricGL_principal_of_isUnit (R := ℝ) (w := w) (b := g.b) (c := g.c) hu
    rw [← hg] at key
    exact key

/-- Arithmetic core of `exists_eval_sq_of_inPrincipalGenus`: a representation `f(x', y') = d²` with `d` prime to
the primes of `2D` yields a primitive representation of `w²` with `w` prime to `2D`. -/
theorem exists_coprime_sq_of_eval_eq {f : BinQF} {x' y' d : ℤ} (hd : d ≠ 0) (h : f.eval x' y' = d ^ 2)
    (hdp : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * f.disc → ¬ (p : ℤ) ∣ d) :
    ∃ w x y : ℤ, IsCoprime x y ∧ IsCoprime w (2 * f.disc) ∧ f.eval x y = w ^ 2 := by
  have hg0 : 0 < Int.gcd x' y' := by
    rcases Nat.eq_zero_or_pos (Int.gcd x' y') with h0 | h0
    · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
      rw [BinQF.eval_eq] at h
      exact absurd (by simpa using h.symm) (pow_ne_zero 2 hd)
    · exact h0
  set g : ℤ := (Int.gcd x' y' : ℤ) with hgdef
  have hgne : g ≠ 0 := by simp only [hgdef]; exact_mod_cast hg0.ne'
  obtain ⟨x, hx⟩ := Int.gcd_dvd_left (a := x') (b := y')
  obtain ⟨y, hy⟩ := Int.gcd_dvd_right (a := x') (b := y')
  have hxy : IsCoprime x y := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_div_gcd_div_gcd (i := x') (j := y') hg0
    have e1 : x' / g = x := by rw [hx]; exact Int.mul_ediv_cancel_left _ hgne
    have e2 : y' / g = y := by rw [hy]; exact Int.mul_ediv_cancel_left _ hgne
    rw [← e1, ← e2]; exact this
  have hsc : f.eval x' y' = g ^ 2 * f.eval x y := by
    have hx' : x' = g * x := hx
    have hy' : y' = g * y := hy
    have : f.eval x' y' = f.eval (g * x) (g * y) := congrArg₂ f.eval hx' hy'
    rw [this, BinQF.eval_eq, BinQF.eval_eq]; ring
  have hgd : g ∣ d := by
    have : g ^ 2 ∣ d ^ 2 := ⟨f.eval x y, by rw [← h, hsc]⟩
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp this
  obtain ⟨w, hw⟩ := hgd
  refine ⟨w, x, y, hxy, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
    have hqd' : (q : ℤ) ∣ (Int.gcd w (2 * f.disc) : ℤ) := Int.natCast_dvd_natCast.mpr hqd
    have h1 : (q : ℤ) ∣ w := hqd'.trans (Int.gcd_dvd_left ..)
    have h2 : (q : ℤ) ∣ 2 * f.disc := hqd'.trans (Int.gcd_dvd_right ..)
    exact hdp q hq h2 (by rw [hw]; exact dvd_mul_of_dvd_right h1 _)
  · have : g ^ 2 * f.eval x y = g ^ 2 * w ^ 2 := by rw [← hsc, h, hw]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hgne) this

/-- **A form in the principal genus represents primitively a square prime to $2D$** (Cassels, Ch. 14, proof of
Thm. 3.1 (i), p. 339, by Ch. 9, Thm. 7.1): $f$ and the principal form are equivalent over $\mathbb Z^{(P)}$ for the set
$P$ of primes dividing $2D$ (`Siegel.semiEquiv_of_sameGenus`); the image of $(1, 0)$ is $(x/d, y/d)$ with $d$ prime to
$P$, so $f(x, y) = d^2$, and dividing by $\gcd(x, y)$ (which is prime to $P$ and divides $d$) gives a primitive
representation of $w^2$, $w$ prime to $2D$. -/
theorem exists_eval_sq_of_inPrincipalGenus {f : BinQF} (hD : f.disc ≠ 0) (h : InPrincipalGenus f) :
    ∃ w x y : ℤ, IsCoprime x y ∧ IsCoprime w (2 * f.disc) ∧ f.eval x y = w ^ 2 := by
  classical
  set P : Finset Nat.Primes := (2 * f.disc).natAbs.primeFactors.subtype Nat.Prime with hP
  have hn0 : (2 * f.disc).natAbs ≠ 0 := by simpa using hD
  have hmem : ∀ p : ℕ, ∀ hp : p.Prime, (p : ℤ) ∣ 2 * f.disc → (⟨p, hp⟩ : Nat.Primes) ∈ P := by
    intro p hp hd
    exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp hd, hn0⟩)
  have hs := (principalForm_spec (BinQF.disc_mod_four f)).2
  have hdet : (principalForm f.disc).hessian.det ≠ 0 := by
    have : (principalForm f.disc).hessian.det = -f.disc := by
      rw [Binary.hessian_det_two]
      have hs' : (principalForm f.disc).b ^ 2 - 4 * (principalForm f.disc).a * (principalForm f.disc).c =
          f.disc := hs
      show 4 * (principalForm f.disc).a * (principalForm f.disc).c - (principalForm f.disc).b ^ 2 = _
      linarith
    rw [this]; exact neg_ne_zero.mpr hD
  obtain ⟨S, hS⟩ := semiEquiv_of_sameGenus _ _ hdet h.symm P
  have hv := hS ![1, 0]
  rw [evalIn_map_rat_eq, evalIn_map_rat_eq] at hv
  rw [Binary.eval_map_two, Binary.eval_map_two] at hv
  set q0 : ℚ := ((S.val 0 0 : intAway P) : ℚ) with hq0
  set q1 : ℚ := ((S.val 1 0 : intAway P) : ℚ) with hq1
  have hv' : (f.a : ℚ) * q0 ^ 2 + f.b * q0 * q1 + f.c * q1 ^ 2 = 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, principalForm] at hv
    simpa [hq0, hq1] using hv
  have hB : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), ‖(q : ℚ_[p])‖ ≤ 1 → ¬ p ∣ q.den := by
    intro p _ q hq hdvd
    have hu := PadicInt.isUnit_den (p := p) q hq
    rw [PadicInt.isUnit_iff] at hu
    have h1 : ‖((q.den : ℤ) : ℤ_[p])‖ < 1 :=
      (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
    have h2 : ((q.den : ℕ) : ℤ_[p]) = ((q.den : ℤ) : ℤ_[p]) := by simp
    rw [h2] at hu
    linarith
  have hB' : ∀ (a : intAway P) (p : ℕ) (hp : p.Prime), (⟨p, hp⟩ : Nat.Primes) ∈ P →
      ¬ p ∣ (a : ℚ).den := by
    intro a p hp hm
    haveI := Fact.mk hp
    exact hB p (a : ℚ) (a.2 ⟨p, hp⟩ hm)
  have hden : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2 * f.disc → ¬ p ∣ q0.den * q1.den := by
    intro p hp hd hdvd
    have hm := hmem p hp hd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h0 | h1
    · exact hB' (S.val 0 0) p hp hm h0
    · exact hB' (S.val 1 0) p hp hm h1
  set d : ℤ := ((q0.den * q1.den : ℕ) : ℤ) with hd
  have hd0 : d ≠ 0 := by
    simp only [hd]; exact_mod_cast Nat.mul_ne_zero q0.den_nz q1.den_nz
  have e0 : (q0 : ℚ) * q0.den = q0.num := Rat.mul_den_eq_num q0
  have e1 : (q1 : ℚ) * q1.den = q1.num := Rat.mul_den_eq_num q1
  have hx : (((q0.num * q1.den : ℤ)) : ℚ) = q0 * d := by
    simp only [hd]; push_cast; rw [← e0]; ring
  have hy : (((q1.num * q0.den : ℤ)) : ℚ) = q1 * d := by
    simp only [hd]; push_cast; rw [← e1]; ring
  have hfe : f.eval (q0.num * q1.den) (q1.num * q0.den) = d ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    rw [BinQF.eval_eq]
    push_cast at hx hy ⊢
    rw [hx, hy]
    push_cast
    linear_combination ((d : ℚ) ^ 2) * hv'
  refine exists_coprime_sq_of_eval_eq hd0 hfe ?_
  intro p hp hdp hdd
  exact hden p hp hdp (by exact_mod_cast Int.natCast_dvd_natCast.mp hdd)

/-- **Cassels, Ch. 14, Theorem 3.1, part (ii) of the proof** (p. 339): *if $\mathfrak C = \mathfrak C_1^2$ then
$\mathfrak C$ is in the principal genus.* -/
@[kb "cassels1978" "Ch. 14, Thm. 3.1, p. 339 (squares are in the principal genus)"]
theorem inPrincipalGenus_of_sq {D : ℤ} [NonzeroDisc D] (f : PrimForm D) (h : ∃ C₁ : FormClass D, C₁ ^ 2 = mk f) :
    InPrincipalGenus f.1 := by
  obtain ⟨f', hf', w, x, y, hxy, hw, hv⟩ := (exists_pow_eq_iff (D := D) (n := 2) (by norm_num) (mk f)).mp h
  have hd : f'.1.disc = D := f'.2.2
  have h1 : InPrincipalGenus f'.1 := inPrincipalGenus_of_eval_sq f'.2.1 hxy (by rw [hd]; exact hw) hv
  exact h1.of_sLEquiv (mk_eq_mk.mp hf')

/-- **Cassels, Ch. 14, Theorem 3.1, part (i) of the proof** (p. 339): *a form in the principal genus represents
properly a square $w^2$ with $w$ prime to $2D$; hence its class is a square* (Lemma 2.5). -/
@[kb "cassels1978" "Ch. 14, Thm. 3.1, p. 339 (the principal genus consists of squares)"]
theorem exists_sq_of_inPrincipalGenus {D : ℤ} [NonzeroDisc D] (f : PrimForm D) (h : InPrincipalGenus f.1) :
    ∃ C₁ : FormClass D, C₁ ^ 2 = mk f := by
  have hD : f.1.disc ≠ 0 := by rw [f.2.2]; exact NonzeroDisc.ne_zero
  obtain ⟨w, x, y, hxy, hw, hv⟩ := exists_eval_sq_of_inPrincipalGenus hD h
  rw [f.2.2] at hw
  exact (exists_pow_eq_iff (D := D) (n := 2) (by norm_num) (mk f)).mpr ⟨f, rfl, w, x, y, hxy, hw, hv⟩

/-- **Cassels, Ch. 14, Theorem 3.1 (Gauss)** (p. 339): *a necessary and sufficient condition that a class
$\mathfrak C$ be in the principal genus is that $\mathfrak C = \mathfrak C_1^2$ for some class $\mathfrak C_1$.*
For every discriminant $D \ne 0$. -/
@[kb "cassels1978" "Ch. 14, Thm. 3.1, p. 339"]
theorem thm_3_1 {D : ℤ} [NonzeroDisc D] (f : PrimForm D) :
    (∃ C₁ : FormClass D, C₁ ^ 2 = mk f) ↔ InPrincipalGenus f.1 :=
  ⟨inPrincipalGenus_of_sq f, exists_sq_of_inPrincipalGenus f⟩

end QuadFormsKB.Composition
