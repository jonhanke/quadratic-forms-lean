/-
# Cassels, Chapter 14, Examples 6 and 7 (iii)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, Examples 6 and 7, pp. 360–361.

With $g(x, y, z) = y^2 - xz$, $f(x, y) = g(x\mathbf r + y\mathbf s)$ and $h$ the form of Ex. 7 built from
$\mathbf e = \mathbf r \times \mathbf s$, we prove

* `ex7ClassRelation`: $\mathfrak C = \mathfrak D^{-2}$ (Ex. 7 (iii)), and
* `principalGenusRepCriterion`: $f$ is in the principal genus iff it is primitively represented by $g$ (Ex. 6),

without any new hypotheses. The proof of Ex. 7 (iii) follows Cassels' hint:

1. (normal form) if $r_0 = 0$ and $e_2 = r_0s_1 - r_1s_0 = -r_1s_0$ is prime to $2D$, then $s_0 \mid D$ and
   $s_0 \mid e_2$ force $s_0 = \pm 1$, $f = [e_2^2, B, C]$ is the composition of $F = [e_2, B, e_2C]$ with itself
   (concordant), and $F$ is properly equivalent to $[e_0, e_1, e_2] = h^{-1}$ (`key_normal`);
2. (reduction) Ex. 7 (ii) (`ex7_ii_surj`) moves $h$ within its class to have $e_2$ prime to $2D$, and then a
   substitution in $\mathrm{SL}_2(\mathbb Z)$ on $(\mathbf r, \mathbf s)$ makes $r_0 = 0$ without changing $\mathbf e$
   and replacing $f$ by a properly equivalent form (`ex7_core`).

For Ex. 6, "$\Leftarrow$" is Ex. 7 (iii) with Theorem 3.1; "$\Rightarrow$" takes $h$ in the class $\mathfrak C_1^{-1}$
where $\mathfrak C = \mathfrak C_1^2$ (Theorem 3.1), finds $\mathbf r, \mathbf s$ with $\mathbf r \times \mathbf s$ the
prescribed vector (`exists_cross`), $\mathbf t$ by primitivity of $h$, and moves $f$ to the given form by $\mathrm{SL}_2$.
-/
import QuadFormsKB.Literature.Cassels.Ch14.NamedStatements
import QuadFormsKB.Literature.Cassels.Ch14.Genus

namespace QuadFormsKB.Composition

open BinQF Binary FormClass Siegel Matrix

private theorem mk_eta' (f : BinQF) : BinQF.mk f.a f.b f.c = f :=
  ext_abc (by simp) (by simp) (by simp)

/-! ### Elementary identities -/

/-- Helper: the determinant of the basis matrix is $\mathbf t \cdot (\mathbf r \times \mathbf s)$. -/
theorem det_ofRST (r s t : Fin 3 → ℤ) : (Matrix.of ![r, s, t]).det =
    t 0 * (r 1 * s 2 - r 2 * s 1) + t 1 * (r 2 * s 0 - r 0 * s 2) + t 2 * (r 0 * s 1 - r 1 * s 0) := by
  rw [Matrix.det_fin_three]; simp; ring

/-- Helper: the same in terms of the coefficients of $h$. -/
theorem det_eq_h (r s t : Fin 3 → ℤ) : (Matrix.of ![r, s, t]).det =
    t 0 * (hOfRS r s).a - t 1 * (hOfRS r s).b + t 2 * (hOfRS r s).c := by
  rw [det_ofRST]; simp [hOfRS]; ring

/-- Helper: an $\mathrm{SL}_2(\mathbb Z)$ change of $(\mathbf r, \mathbf s)$ substitutes in $f$. -/
theorem fOfRS_act (r s : Fin 3 → ℤ) (p q r' s' : ℤ) :
    fOfRS (p • r + r' • s) (q • r + s' • s) = BinQF.subst p q r' s' (fOfRS r s) := by
  refine ext_abc ?_ ?_ ?_ <;>
    simp only [fOfRS, subst, a_mk, b_mk, c_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Helper: an $\mathrm{SL}_2(\mathbb Z)$ change of $(\mathbf r, \mathbf s)$ does not change $\mathbf r \times \mathbf s$,
hence not $h$. -/
theorem hOfRS_act (r s : Fin 3 → ℤ) {p q r' s' : ℤ} (hdet : p * s' - q * r' = 1) :
    hOfRS (p • r + r' • s) (q • r + s' • s) = hOfRS r s := by
  refine ext_abc ?_ ?_ ?_ <;>
    simp only [hOfRS, a_mk, b_mk, c_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · linear_combination (r 1 * s 2 - r 2 * s 1) * hdet
  · linear_combination (-(r 2 * s 0 - r 0 * s 2)) * hdet
  · linear_combination (r 0 * s 1 - r 1 * s 0) * hdet

/-- Helper: every vector is a cross product $\mathbf r \times \mathbf s$ of integer vectors. -/
theorem exists_cross (e0 e1 e2 : ℤ) : ∃ r s : Fin 3 → ℤ,
    r 1 * s 2 - r 2 * s 1 = e0 ∧ r 2 * s 0 - r 0 * s 2 = e1 ∧ r 0 * s 1 - r 1 * s 0 = e2 := by
  by_cases h : 0 < Int.gcd e0 e1
  · obtain ⟨g, p, q, hg, hpq, hp, hq⟩ := Int.exists_gcd_one' h
    obtain ⟨x, y, hxy⟩ : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.2 hpq
    refine ⟨![-q, p, 0], ![-(e2 * x), -(e2 * y), g], ?_, ?_, ?_⟩
    · simp; linear_combination -hp
    · simp; linear_combination -hq
    · simp; linear_combination e2 * hxy
  · have h0 : Int.gcd e0 e1 = 0 := by omega
    obtain ⟨he0, he1⟩ := Int.gcd_eq_zero_iff.1 h0
    refine ⟨![1, 0, 0], ![0, e2, 0], ?_, ?_, ?_⟩
    · simp [he0]
    · simp [he1]
    · simp

/-- Helper: a primitive triple has a Bezout combination equal to $1$. -/
theorem exists_bezout3 {a b c : ℤ} (h : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) :
    ∃ x y z : ℤ, x * a + y * b + z * c = 1 := by
  have h1 : IsCoprime ((Int.gcd a b : ℕ) : ℤ) c := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h2 : (((Int.gcd ((Int.gcd a b : ℕ) : ℤ) c : ℕ)) : ℤ) ∣ ((Int.gcd a b : ℕ) : ℤ) := Int.gcd_dvd_left ..
    have hu := h (((Int.gcd ((Int.gcd a b : ℕ) : ℤ) c : ℕ)) : ℤ)
      (h2.trans (Int.gcd_dvd_left ..)) (h2.trans (Int.gcd_dvd_right ..)) (Int.gcd_dvd_right ..)
    rcases Int.isUnit_iff.1 hu with h3 | h3 <;> omega
  obtain ⟨u, v, huv⟩ := h1
  have hg := Int.gcd_eq_gcd_ab a b
  exact ⟨u * Int.gcdA a b, u * Int.gcdB a b, v, by rw [hg] at huv; linear_combination huv⟩

/-- Helper: for $(u, v)$ there is an $\mathrm{SL}_2(\mathbb Z)$ matrix whose first column kills $pu + r'v$. -/
theorem exists_rotate (u v : ℤ) :
    ∃ p q r' s' : ℤ, p * s' - q * r' = 1 ∧ p * u + r' * v = 0 := by
  by_cases h : 0 < Int.gcd u v
  · obtain ⟨g, m, n, hg, hmn, hm, hn⟩ := Int.exists_gcd_one' h
    have hc : IsCoprime n (-m) := (Int.isCoprime_iff_gcd_eq_one.2 hmn).symm.neg_right
    obtain ⟨a, b, hab⟩ := hc
    refine ⟨n, -b, -m, a, by linear_combination hab, ?_⟩
    rw [hm, hn]; ring
  · have h0 : Int.gcd u v = 0 := by omega
    obtain ⟨hu, hv⟩ := Int.gcd_eq_zero_iff.1 h0
    exact ⟨1, 0, 0, 1, by norm_num, by rw [hu, hv]; ring⟩

/-! ### The normal form -/

/-- **Ex. 7 (iii) in normal form**: if $r_0 = 0$ and $e_2 = r_0s_1 - r_1s_0$ is prime to $2D$, then $f$ is primitive
and $\mathfrak C = \mathfrak D^{-2}$. -/
theorem key_normal {D : ℤ} [NonzeroDisc D] (r s : Fin 3 → ℤ) (hr0 : r 0 = 0) (hD : (fOfRS r s).disc = D)
    (hcop : IsCoprime (hOfRS r s).c (2 * D)) (hH : (hOfRS r s).IsPrimitive) :
    ∃ hf : (fOfRS r s).IsPrimitive,
      mk (⟨fOfRS r s, hf, hD⟩ : PrimForm D) =
        (mk (⟨hOfRS r s, hH, (ex7_disc_h r s).trans hD⟩ : PrimForm D))⁻¹ ^ 2 := by
  have hcH : (hOfRS r s).c = -(r 1 * s 0) := by simp [hOfRS, hr0]
  have hHa : (hOfRS r s).a = r 1 * s 2 - r 2 * s 1 := rfl
  have hHb : (hOfRS r s).b = -(r 2 * s 0) := by simp [hOfRS, hr0]
  have hfa : (fOfRS r s).a = r 1 ^ 2 := by simp [fOfRS, hr0]
  have hfb : (fOfRS r s).b = 2 * r 1 * s 1 - r 2 * s 0 := by simp [fOfRS, hr0]
  have hDq : D = s 0 * (r 2 ^ 2 * s 0 - 4 * r 1 * r 2 * s 1 + 4 * r 1 ^ 2 * s 2) := by
    rw [← hD]; simp only [BinQF.disc, fOfRS, a_mk, b_mk, c_mk, hr0]; ring
  have hfd : (fOfRS r s).b ^ 2 - 4 * (fOfRS r s).a * (fOfRS r s).c = D := hD
  obtain ⟨c, hcdef⟩ : ∃ c : ℤ, c = -(r 1 * s 0) := ⟨_, rfl⟩
  rw [hcH, ← hcdef] at hcop
  have hcH' : (hOfRS r s).c = c := hcH.trans hcdef.symm
  have hcopD : IsCoprime c D := hcop.of_isCoprime_of_dvd_right ⟨2, by ring⟩
  have hc0 : c ≠ 0 := ne_zero_of_coprime_two_mul hcop
  have hs0 : IsUnit (s 0) :=
    hcopD.isUnit_of_dvd' ⟨-(r 1), by rw [hcdef]; ring⟩ ⟨_, hDq⟩
  have hs : s 0 * s 0 = 1 := by
    rcases Int.isUnit_iff.1 hs0 with h | h <;> rw [h] <;> norm_num
  have hcc : c * c = (fOfRS r s).a := by
    rw [hfa, hcdef]; linear_combination (r 1 ^ 2) * hs
  -- the form F = [c, b, c C]
  have hFdisc : ((fOfRS r s).b) ^ 2 - 4 * c * (c * (fOfRS r s).c) = D := by
    linear_combination hfd - 4 * (fOfRS r s).c * hcc
  have hFprim : (BinQF.mk c (fOfRS r s).b (c * (fOfRS r s).c)).IsPrimitive := by
    intro d h1 h2 h3
    simp only [a_mk, b_mk, c_mk] at h1 h2 h3
    refine hcopD.isUnit_of_dvd' h1 ?_
    rw [← hFdisc]
    exact dvd_sub (dvd_pow h2 two_ne_zero) (((h1.mul_left 4).mul_right _))
  have hfprim : (fOfRS r s).IsPrimitive := by
    intro d h1 h2 h3
    refine (hcopD.mul_left hcopD).isUnit_of_dvd' (by rw [hcc]; exact h1) ?_
    rw [← hD]
    exact dvd_sub (dvd_pow h2 two_ne_zero) ((h1.mul_left 4).mul_right _)
  refine ⟨hfprim, ?_⟩
  obtain ⟨Fp, hFp⟩ : ∃ Fp : PrimForm D, Fp.1 = BinQF.mk c (fOfRS r s).b (c * (fOfRS r s).c) :=
    ⟨⟨_, hFprim, by simp only [BinQF.disc, a_mk, b_mk, c_mk]; exact hFdisc⟩, rfl⟩
  have hconc : Concordant Fp.1 Fp.1 := by
    refine ⟨?_, rfl, rfl, ?_⟩
    · rw [hFp, a_mk]; exact mul_ne_zero hc0 hc0
    · rw [Fp.2.2, hFp, a_mk, b_mk]
      exact ⟨(fOfRS r s).c, by linear_combination hfd - 4 * (fOfRS r s).c * hcc⟩
  have hcomp : (PrimForm.comp Fp Fp hconc).1 = fOfRS r s := by
    apply eq_of_a_b_disc
    · rw [primComp_a, hFp, a_mk]; exact mul_ne_zero hc0 hc0
    · rw [primComp_a, hFp, a_mk, hcc]
    · rw [primComp_b, hFp, b_mk]
    · exact (PrimForm.comp Fp Fp hconc).2.2.trans hD.symm
  have hsq : mk (⟨fOfRS r s, hfprim, hD⟩ : PrimForm D) = mk Fp * mk Fp := by
    rw [mk_mul_mk Fp Fp hconc]
    exact (mk_eq_mk.2 (by
      show SLEquiv (fOfRS r s) (PrimForm.comp Fp Fp hconc).1
      rw [hcomp]; exact SLEquiv.refl _)).trans rfl
  -- F ∼ conj h
  obtain ⟨Hp, hHp⟩ : ∃ Hp : PrimForm D, Hp.1 = hOfRS r s :=
    ⟨⟨hOfRS r s, hH, (ex7_disc_h r s).trans hD⟩, rfl⟩
  have hHpeq : (⟨hOfRS r s, hH, (ex7_disc_h r s).trans hD⟩ : PrimForm D) = Hp := Subtype.ext hHp.symm
  have hFH : mk Fp = (mk Hp)⁻¹ := by
    rw [mk_inv]
    refine mk_eq_mk.2 ?_
    show SLEquiv Fp.1 (conjForm Hp.1)
    rw [hHp]
    have e1' : SLEquiv (conjForm (hOfRS r s))
        (BinQF.mk (hOfRS r s).c (hOfRS r s).b (hOfRS r s).a) := by
      have := sLEquiv_swap (hOfRS r s).a (-(hOfRS r s).b) (hOfRS r s).c
      rw [neg_neg] at this
      exact this
    have e1 := e1'
    rw [hcH'] at e1
    have e2 := sLEquiv_translate c (hOfRS r s).b (hOfRS r s).a (-(s 0 * s 1))
    have e3 := e1.trans e2
    have hT : BinQF.mk c ((hOfRS r s).b + 2 * c * (-(s 0 * s 1)))
        (c * (-(s 0 * s 1)) ^ 2 + (hOfRS r s).b * (-(s 0 * s 1)) + (hOfRS r s).a) = Fp.1 := by
      apply eq_of_a_b_disc
      · rw [a_mk]; exact hc0
      · rw [a_mk, hFp, a_mk]
      · rw [b_mk, hFp, b_mk, hHb, hfb, hcdef]; linear_combination (2 * r 1 * s 1) * hs
      · rw [← SLEquiv.disc_eq e3, disc_conjForm, ex7_disc_h, hD, Fp.2.2]
    rw [hT] at e3
    exact e3.symm
  rw [hHpeq, hsq, ← hFH, pow_two]

/-! ### The reduction -/

/-- **Ex. 7 (iii), general form** (Cassels, Ch. 14, Ex. 7 (iii), p. 361): for any $\mathbf r, \mathbf s$ with $h$
primitive of non-zero discriminant $D$ (so $D \equiv 0, 1 \bmod 4$ automatically), $f$ is primitive and
$\mathfrak C = \mathfrak D^{-2}$. The basis vector $\mathbf t$ is only used to see that $h$ is primitive. -/
theorem ex7_core {D : ℤ} [NonzeroDisc D] (r s : Fin 3 → ℤ) (hD : (fOfRS r s).disc = D)
    (hH : (hOfRS r s).IsPrimitive) :
    ∃ hf : (fOfRS r s).IsPrimitive,
      mk (⟨fOfRS r s, hf, hD⟩ : PrimForm D) =
        (mk (⟨hOfRS r s, hH, (ex7_disc_h r s).trans hD⟩ : PrimForm D))⁻¹ ^ 2 := by
  have hHD : (hOfRS r s).disc = D := (ex7_disc_h r s).trans hD
  obtain ⟨g, hg, hga⟩ := exists_rep_coprime (mk (⟨hOfRS r s, hH, hHD⟩ : PrimForm D)) (M := 2 * D)
    (mul_ne_zero two_ne_zero NonzeroDisc.ne_zero)
  have e : SLEquiv (hOfRS r s) (BinQF.mk g.1.c (-g.1.b) g.1.a) := by
    have h1 : SLEquiv (hOfRS r s) g.1 := (mk_eq_mk.1 hg).symm
    have h2 := sLEquiv_swap g.1.a g.1.b g.1.c
    rw [mk_eta'] at h2
    exact h1.trans h2
  obtain ⟨α, β, γ, δ, hdet, hh⟩ := ex7_ii_surj r s e
  have hf1 := (ex7_h_star r s hdet).1
  generalize autG α β γ δ *ᵥ r = r1 at hh hf1
  generalize autG α β γ δ *ᵥ s = s1 at hh hf1
  obtain ⟨p, q, r', s', hdet2, hrot⟩ := exists_rotate (r1 0) (s1 0)
  have hfR : fOfRS (p • r1 + r' • s1) (q • r1 + s' • s1) = BinQF.subst p q r' s' (fOfRS r s) := by
    rw [fOfRS_act, hf1]
  have hhR : hOfRS (p • r1 + r' • s1) (q • r1 + s' • s1) = BinQF.mk g.1.c (-g.1.b) g.1.a := by
    rw [hOfRS_act _ _ hdet2, hh]
  have hR0 : (p • r1 + r' • s1) 0 = 0 := by simpa using hrot
  have eS : SLEquiv (fOfRS r s) (fOfRS (p • r1 + r' • s1) (q • r1 + s' • s1)) :=
    (sLEquiv_iff _ _).2 ⟨p, q, r', s', hdet2, hfR.symm⟩
  have hDR : (fOfRS (p • r1 + r' • s1) (q • r1 + s' • s1)).disc = D :=
    (SLEquiv.disc_eq eS).symm.trans hD
  have hHR : (hOfRS (p • r1 + r' • s1) (q • r1 + s' • s1)).IsPrimitive := by
    rw [hhR]; exact SLEquiv.isPrimitive e hH
  have hcopR : IsCoprime (hOfRS (p • r1 + r' • s1) (q • r1 + s' • s1)).c (2 * D) := by
    rw [hhR]; simpa using hga
  obtain ⟨hfR', hrel⟩ := key_normal _ _ hR0 hDR hcopR hHR
  have hf : (fOfRS r s).IsPrimitive := SLEquiv.isPrimitive eS.symm hfR'
  refine ⟨hf, ?_⟩
  have hmkH : mk (⟨hOfRS (p • r1 + r' • s1) (q • r1 + s' • s1), hHR,
      (ex7_disc_h _ _).trans hDR⟩ : PrimForm D) = mk (⟨hOfRS r s, hH, hHD⟩ : PrimForm D) :=
    mk_eq_mk.2 (by show SLEquiv (hOfRS (p • r1 + r' • s1) (q • r1 + s' • s1)) (hOfRS r s)
                   rw [hhR]; exact e.symm)
  rw [← hmkH, ← hrel]
  exact mk_eq_mk.2 eS

/-- **Cassels, Ch. 14, Ex. 7 (iii)** (p. 361): *with $f = g(x\mathbf r + y\mathbf s)$ primitive ($\mathbf r, \mathbf s,
\mathbf t$ a basis of $\mathbb Z^3$, $g = y^2 - xz$) and $h(x, y) = e_0x^2 - e_1xy + e_2y^2$ with $\mathbf e = \mathbf r
\times \mathbf s$ (`hOfRS`), the classes $\mathfrak C$ of $f$ and $\mathfrak D$ of $h$ in the class group of
discriminant $D = \operatorname{disc} f$ satisfy $\mathfrak C = \mathfrak D^{-2}$.* Field: `rel`. Proved
unconditionally, exactly as stated (no erratum in the exponent or sign convention). -/
@[kb "cassels1978" "Ch. 14, Ex. 7 (iii), p. 361 (proved)"]
theorem ex7ClassRelation : Ex7ClassRelation :=
  ⟨fun r s t hb _ hf => by
    obtain ⟨_, h⟩ := ex7_core (D := (fOfRS r s).disc) r s rfl (ex7_h_isPrimitive r s t hb)
    exact h⟩

/-! ### Ex. 6 -/

/-- **Cassels, Ch. 14, Ex. 6** (p. 360): *a primitive integral form $f$ of discriminant $D \ne 0$ is in the principal
genus if and only if it is primitively represented by $g(x, y, z) = y^2 - xz$*, i.e. $f(x, y) = g(x\mathbf r +
y\mathbf s)$ for a basis $\mathbf r, \mathbf s, \mathbf t$ of $\mathbb Z^3$. ($\Leftarrow$): Ex. 7 (iii) makes the
class of $f$ a square, then Theorem 3.1. ($\Rightarrow$): by Theorem 3.1 $f$ lies in $\mathfrak C_1^2$; take $h$ in the
class $\mathfrak C_1^{-1}$, $\mathbf r \times \mathbf s$ = the coefficient vector of $h$, $\mathbf t$ from the
primitivity of $h$; then $g(x\mathbf r + y\mathbf s)$ is properly equivalent to $f$ by Ex. 7 (iii), and one adjusts
$(\mathbf r, \mathbf s)$ by that $\mathrm{SL}_2(\mathbb Z)$ substitution. -/
@[kb "cassels1978" "Ch. 14, Ex. 6, p. 360 (proved)"]
theorem principalGenusRepCriterion : PrincipalGenusRepCriterion := by
  refine ⟨fun f hprim hD0 => ⟨fun hpg => ?_, fun hrep => ?_⟩⟩
  · have : NonzeroDisc f.disc := ⟨hD0, BinQF.disc_mod_four f⟩
    obtain ⟨C, hC⟩ := (thm_3_1 (⟨f, hprim, rfl⟩ : PrimForm f.disc)).2 hpg
    obtain ⟨Hp, hHp⟩ := mk_surjective C⁻¹
    obtain ⟨r, s, hr1, hr2, hr3⟩ := exists_cross Hp.1.a (-Hp.1.b) Hp.1.c
    have hHeq : hOfRS r s = Hp.1 :=
      ext_abc (by simp [hOfRS, hr1]) (by simp [hOfRS, hr2]) (by simp [hOfRS, hr3])
    have hH : (hOfRS r s).IsPrimitive := by rw [hHeq]; exact Hp.2.1
    obtain ⟨x, y, z, hxyz⟩ := exists_bezout3 Hp.2.1
    have hb0 : IsUnit (Matrix.of ![r, s, ![x, -y, z]]).det := by
      rw [det_eq_h, hHeq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons]
      have : x * Hp.1.a - -y * Hp.1.b + z * Hp.1.c = 1 := by linear_combination hxyz
      rw [this]; exact isUnit_one
    have hDe : (fOfRS r s).disc = f.disc :=
      (ex7_disc_h r s).symm.trans ((congrArg BinQF.disc hHeq).trans Hp.2.2)
    obtain ⟨hf', hrel⟩ := ex7_core (D := f.disc) r s hDe hH
    have hmkH : mk (⟨hOfRS r s, hH, (ex7_disc_h r s).trans hDe⟩ : PrimForm f.disc) = C⁻¹ :=
      (mk_eq_mk.2 (by show SLEquiv (hOfRS r s) Hp.1; rw [hHeq]; exact SLEquiv.refl _)).trans hHp
    have hmkf : mk (⟨fOfRS r s, hf', hDe⟩ : PrimForm f.disc) = mk (⟨f, hprim, rfl⟩ : PrimForm f.disc) := by
      rw [hrel, hmkH, inv_inv]; exact hC
    obtain ⟨p, q, r', s', hdet, hsub⟩ := (sLEquiv_iff _ _).1 (mk_eq_mk.1 hmkf)
    refine ⟨p • r + r' • s, q • r + s' • s, ![x, -y, z], ?_, ?_⟩
    · rw [det_eq_h, hOfRS_act r s hdet, ← det_eq_h]; exact hb0
    · rw [fOfRS_act]; exact hsub
  · obtain ⟨r, s, t, hb, rfl⟩ := hrep
    have : NonzeroDisc (fOfRS r s).disc := ⟨hD0, BinQF.disc_mod_four _⟩
    have hrel := ex7ClassRelation.rel r s t hb hprim
    exact (thm_3_1 (⟨fOfRS r s, hprim, rfl⟩ : PrimForm (fOfRS r s).disc)).1 ⟨_, hrel.symm⟩

end QuadFormsKB.Composition
