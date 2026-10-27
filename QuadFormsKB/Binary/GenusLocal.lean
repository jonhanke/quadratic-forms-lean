import QuadFormsKB.Binary.GenusCharacters
import QuadFormsKB.Siegel.UnimodularPadic

/-!
# Genus = local equivalence for binary forms

For primitive positive definite forms $f, g$ of fundamental discriminant $D$:
$$f, g \text{ are in the same genus (equivalent over every } \mathbb{Z}_p \text{ and over } \mathbb{R}) \iff
\chi_p(f) = \chi_p(g) \text{ for every prime } p \mid D$$
(`sameGenus_iff_formChar_eq`). This is the bridge from Gauss's genus (equal characters) to the repo's genus
`Siegel.SameGenus`. Everything is local; no global input is used.

**The local classification used.** Over $K = \mathbb{Z}_p$ (any $p$, including $p = 2$) or $K = \mathbb{R}$, if
$f = [a, b, c]$ and $g = [a', b', c']$ have the same discriminant, $a$ is a unit of $K$, and $a' = a s^2$ with
$s \in K^\times$, then $f \cong g$ over $K$ by the triangular substitution
$\begin{pmatrix} s & r \\ 0 & s^{-1}\end{pmatrix}$, $r = \tfrac{b' - b}{2as}$ (`isometricGL_map_of_sq`; $b \equiv b'
\pmod 2$ because both $b^2 \equiv D \pmod 4$). So a binary form over $\mathbb{Z}_p$ representing a unit $u$ is
determined by the square class of $u$, and it remains to find, in each form, a value in the right square class:

* $p$ odd, $p \mid D$: the square class of a value prime to $p$ is the character $\chi_p$;
* $p$ odd, $p \nmid D$: unimodular forms with equal determinant (the repo's
  `Siegel.Kneser.isometricGL_of_unimodular`);
* $p = 2 \nmid D$: $f(1, 2k)$, $k = 0, 1, 2, 3$, runs through all odd classes mod $8$;
* $p = 2 \mid D$: $f(1, 0)$ and $f(1, 2)$ or $f(x, 1)$ cover the two classes mod $8$ with the given $\psi_2$;
* $\mathbb{R}$: $a, a' > 0$, so $a'/a$ is a square.

Conversely (`formChar_eq_of_isometricGL`), a $\mathbb{Z}_p$-equivalence carries a value $m$ of $f$ prime to $p$ to a
$p$-adic value of $g$; approximating mod $p$ (mod $8$ if $p = 2$) gives an integer value of $g$ congruent to $m$,
so $\chi_p(g) = \psi_p(m) = \chi_p(f)$.

Sources: Gauss, *Disq. Arith.* §§229–233 and §§257–260; Cassels, *Rational Quadratic Forms*, Ch. 8, §3 (forms over
$\mathbb{Z}_p$) and Ch. 14, §3, pp. 339–340 (genera of binary forms; Lemmas 3.1–3.3 list the $\mathbb{Z}_p$-classes); Cox, §3.B and Theorem 6.1-type comparisons
(*genus via local equivalence*); Buell, Ch. 4.
-/

set_option linter.unusedSectionVars false

open Matrix

namespace QuadFormsKB.Binary

open BinQF Siegel

variable {D : ℤ}

/-! ### Binary forms over a commutative ring -/

section General

variable {K : Type*} [CommRing K]

/-- **A form in two variables in coordinates:** $F(v) = c_{00} v_0^2 + c_{01} v_0 v_1 + c_{11} v_1^2$. -/
theorem quadForm_eval_two (F : QuadForm K 2) (v : Fin 2 → K) :
    F.eval v = F.coeff 0 0 * v 0 ^ 2 + F.coeff 0 1 * v 0 * v 1 + F.coeff 1 1 * v 1 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_two]; ring

/-- **The base change of an integral binary form:** $(\varphi_* f)(v) = \varphi(a) v_0^2 + \varphi(b) v_0 v_1 +
\varphi(c) v_1^2$ for $\varphi : \mathbb{Z} \to K$. -/
theorem eval_map_two (f : BinQF) (φ : ℤ →+* K) (v : Fin 2 → K) :
    (f.map φ).eval v = φ f.a * v 0 ^ 2 + φ f.b * v 0 * v 1 + φ f.c * v 1 ^ 2 := by
  rw [quadForm_eval_two]; rfl

/-- An integral binary form at an integer vector: $f(v) = a v_0^2 + b v_0 v_1 + c v_1^2$. -/
theorem quadForm_eval_bin (f : BinQF) (v : Fin 2 → ℤ) :
    QuadForm.eval f v = f.a * v 0 ^ 2 + f.b * v 0 * v 1 + f.c * v 1 ^ 2 := by
  rw [quadForm_eval_two]; rfl

/-- **An equivalence from an explicit invertible $2 \times 2$ matrix.** -/
theorem isometricGL_of_mat {F G : QuadForm K 2} (M N : Matrix (Fin 2) (Fin 2) K) (hMN : M * N = 1)
    (hNM : N * M = 1) (h : ∀ v, F.eval (M *ᵥ v) = G.eval v) : IsometricGL F G :=
  ⟨⟨M, N, hMN, hNM⟩, h⟩

/-- $b \equiv b' \pmod 2$ for forms of the same discriminant ($b^2 \equiv D \pmod 4$). -/
theorem two_dvd_b_sub_of_disc_eq {f g : BinQF} (h : f.disc = g.disc) : (2 : ℤ) ∣ g.b - f.b := by
  have h2 : ((f.disc : ℤ) : ZMod 2) = ((g.disc : ℤ) : ZMod 2) := by rw [h]
  simp only [disc, Int.cast_sub, Int.cast_mul, Int.cast_pow] at h2
  have h4 : ((4 : ℤ) : ZMod 2) = 0 := by decide
  push_cast at h2 h4
  rw [h4] at h2
  simp only [zero_mul, sub_zero] at h2
  have key : ∀ x y : ZMod 2, x ^ 2 = y ^ 2 → y = x := by decide
  have := key _ _ h2
  exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).mp this.symm

/-- **The local normal-form lemma** (Cassels, Ch. 8, §3, proof of Thm. 3.1, p. 116, completing the square, there for $p \ne 2$; Gauss §§157–158 for the substitution):
over an integral domain $K$ with $2 \ne 0$, let $f, g$ be integral binary forms of the same discriminant with
$\varphi(a_f)$ a unit and $\varphi(a_g) = \varphi(a_f)\, s^2$ for a unit $s$. Then $\varphi_* f \cong \varphi_* g$
over $K$, by $\begin{pmatrix} s & r \\ 0 & s^{-1}\end{pmatrix}$ with $r = \tfrac{(b_g - b_f)/2}{a_f s}$. -/
@[kb "cassels1978" "Ch. 8, §3, proof of Thm. 3.1, p. 116 (completing the square)"]
theorem isometricGL_map_of_sq [IsDomain K] (h2 : (2 : K) ≠ 0) (φ : ℤ →+* K) {f g : BinQF}
    (hdisc : f.disc = g.disc) (hu : IsUnit (φ f.a)) (s : Kˣ) (hv : φ g.a = φ f.a * (s : K) ^ 2) :
    IsometricGL (f.map φ) (g.map φ) := by
  obtain ⟨k, hk⟩ := two_dvd_b_sub_of_disc_eq hdisc
  obtain ⟨u, hu'⟩ := hu
  set A := φ f.a
  set B := φ f.b
  set C := φ f.c
  set A' := φ g.a
  set B' := φ g.b
  set C' := φ g.c
  have hD : B ^ 2 - 4 * A * C = B' ^ 2 - 4 * A' * C' := by
    have := congrArg φ hdisc
    simp only [disc, map_sub, map_mul, map_pow, map_ofNat] at this
    exact this
  set t : K := ((s⁻¹ : Kˣ) : K)
  have hst : (s : K) * t = 1 := s.mul_inv
  set w : K := ((u⁻¹ : Kˣ) : K) * t
  have hw : A * s * w = 1 := by
    rw [← hu']; simp only [w]
    calc (u : K) * s * (↑u⁻¹ * t) = ((u : K) * ↑u⁻¹) * (s * t) := by ring
      _ = 1 := by rw [u.mul_inv, hst, one_mul]
  set r : K := φ k * w
  have hB' : B' = B + 2 * A * s * r := by
    have e : B' - B = 2 * φ k := by
      simp only [B', B, ← map_sub, hk, map_mul, map_ofNat]
    calc B' = B + 2 * φ k * (A * s * w) := by rw [hw]; linear_combination e
      _ = B + 2 * A * s * r := by simp only [r]; ring
  have hA' : A' = A * s ^ 2 := hv
  clear_value r w t
  have hA0 : A ≠ 0 := by rw [← hu']; exact u.ne_zero
  have h4A' : 4 * A' ≠ 0 := by
    rw [hA']
    exact mul_ne_zero (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2)
      (mul_ne_zero hA0 (pow_ne_zero _ s.ne_zero))
  have hC' : C' = A * r ^ 2 + B * r * t + C * t ^ 2 := by
    apply mul_left_cancel₀ h4A'
    rw [hA'] at hD ⊢
    rw [hB'] at hD
    linear_combination hD - (4 * A * B * s * r + 4 * A * C * (s * t + 1)) * hst
  have hts : t * (s : K) = 1 := by rw [mul_comm]; exact hst
  refine isometricGL_of_mat !![(s : K), r; 0, t] !![t, -r; 0, (s : K)] ?_ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hst, hts]
    ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hst, hts]
    ring
  · intro v
    rw [eval_map_two, eval_map_two]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [show φ g.a = A' from rfl, show φ g.b = B' from rfl, show φ g.c = C' from rfl, hA', hB', hC']
    linear_combination (B * v 0 * v 1) * hst

end General

/-! ### Integral equivalence: moving a primitive value to the first coefficient -/

/-- **A primitively represented value is the first coefficient of an equivalent form:** if $\gcd(x, y) = 1$ there
is $g \sim_{\mathbb{Z}} f$ ($\mathrm{SL}_2(\mathbb{Z})$-equivalent, hence `IntEquiv`) with $a_g = f(x, y)$ and the same
discriminant. -/
theorem exists_intEquiv_a_eq (f : BinQF) {x y : ℤ} (hxy : IsCoprime x y) :
    ∃ g : BinQF, IntEquiv f g ∧ g.a = f.eval x y ∧ g.disc = f.disc := by
  obtain ⟨r, s, hdet, ha⟩ := exists_subst_a_eq f hxy
  refine ⟨subst x r y s f, ?_, ha, disc_subst_of_det _ _ _ _ _ (by rw [hdet]; norm_num)⟩
  refine isometricGL_of_mat !![x, r; y, s] !![s, -r; -y, x] ?_ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
  · intro v
    rw [quadForm_eval_bin, quadForm_eval_bin]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, subst, a_mk,
      b_mk, c_mk]
    ring

/-! ### The Hessian determinant of a binary form -/

/-- $\det H = 4c_{00}c_{11} - c_{01}^2$ for a form in two variables ($H = C + C^{\mathsf T}$). -/
theorem hessian_det_two {K : Type*} [CommRing K] (F : QuadForm K 2) :
    F.hessian.det = 4 * F.coeff 0 0 * F.coeff 1 1 - F.coeff 0 1 ^ 2 := by
  have h10 : F.coeff 1 0 = 0 := F.upper (show (0 : Fin 2) < 1 by decide)
  rw [Matrix.det_fin_two, QuadForm.hessian]
  simp only [Matrix.add_apply, Matrix.transpose_apply, h10]
  ring

/-! ### Squares and units in $\mathbb{Z}_p$ -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integer prime to $p$ is a unit of $\mathbb{Z}_p$. -/
theorem isUnit_intCast_padic {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : IsUnit (n : ℤ_[p]) := by
  apply Kneser.isUnit_of_toZMod_ne_zero
  rw [map_intCast]
  intro h
  exact hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp h)

/-- $p \mid x$ in $\mathbb{Z}_p$ for an integer $x$ forces $p \mid x$ in $\mathbb{Z}$. -/
theorem int_dvd_of_padic_dvd {n : ℤ} (h : (p : ℤ_[p]) ∣ (n : ℤ_[p])) : (p : ℤ) ∣ n := by
  obtain ⟨c, hc⟩ := h
  have := congrArg PadicInt.toZMod hc
  rw [map_intCast, map_mul, Kneser.toZMod_natCast_self, zero_mul] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp this

/-- **Hensel, $p$ odd:** an integer $c$ prime to $p$ with $\left(\frac cp\right) = 1$ is a square in $\mathbb{Z}_p$. -/
theorem exists_sq_padic_odd (hp2 : p ≠ 2) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hJ : jacobiSym c p = 1) :
    ∃ z : ℤ_[p], z ^ 2 = c := by
  obtain ⟨y, hy⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  refine Kneser.exists_sq_eq_of_toZMod hp2 (c : ℤ_[p]) (s := y) ?_ ?_
  · rintro rfl
    rw [mul_zero] at hy
    exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hy)
  · rw [map_intCast, hy, sq]

/-- **Hensel, $p = 2$:** an integer $c \equiv 1 \pmod 8$ is a square in $\mathbb{Z}_2$. -/
theorem exists_sq_padic_two {c : ℤ} (hc : (c : ZMod 8) = 1) : ∃ z : ℤ_[2], z ^ 2 = c := by
  have h8 : (2 : ℤ) ^ 3 ∣ 1 - c := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub c 1 8).mp (by rw [hc]; simp)
    norm_num; exact this
  have hn : ‖((1 - c : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := by
    have := (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (k := 1 - c) (n := 3)).mpr (by exact_mod_cast h8)
    exact_mod_cast this
  have h2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
    (F := Polynomial.X ^ 2 - Polynomial.C (c : ℤ_[2])) (a := 1) (by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Polynomial.derivative_X_pow, Polynomial.derivative_C]
      simp
      rw [h2]
      push_cast at hn
      refine lt_of_le_of_lt hn ?_
      norm_num)
  refine ⟨z, ?_⟩
  simp at hz
  exact sub_eq_zero.mp hz

/-- **Equivalence over $\mathbb{Z}_p$ from a square class:** if $f, g$ have the same discriminant, $p \nmid a_f a_g$,
and $a_f a_g$ is a square in $\mathbb{Z}_p$, then $f \cong g$ over $\mathbb{Z}_p$ (`isometricGL_map_of_sq` with
$s = z / a_f$). -/
theorem isometricGL_padic_of_sq {f g : BinQF} (hdisc : f.disc = g.disc) (hfa : ¬ (p : ℤ) ∣ f.a)
    (hga : ¬ (p : ℤ) ∣ g.a) {z : ℤ_[p]} (hz : z ^ 2 = ((f.a * g.a : ℤ) : ℤ_[p])) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) := by
  have hu := isUnit_intCast_padic hfa
  have hug := isUnit_intCast_padic hga
  have hzU : IsUnit z := by
    have : IsUnit (z ^ 2) := by rw [hz]; push_cast; exact hu.mul hug
    exact (isUnit_pow_iff two_ne_zero).mp this
  refine isometricGL_map_of_sq two_ne_zero _ hdisc (by simpa using hu) (hzU.unit * hu.unit⁻¹) ?_
  have hui : ((f.a : ℤ) : ℤ_[p]) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    exact hu.mul_val_inv
  simp only [eq_intCast, Units.val_mul, IsUnit.unit_spec]
  push_cast at hz
  linear_combination (-(f.a : ℤ_[p]) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ^ 2) * hz -
    ((g.a : ℤ_[p]) * ((f.a : ℤ_[p]) * ((hu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) + 1)) * hui

/-- **Unimodular case ($p$ odd, $p \nmid D$):** forms of the same discriminant $D$ with $p \nmid D$ are equivalent
over $\mathbb{Z}_p$ (O'Meara 92:2 via `Siegel.Kneser.isometricGL_of_unimodular`; here $\det H = -D$). -/
@[kb "omeara1963" "§92, 92:2, pp. 246–247 (via `Siegel.Kneser.isometricGL_of_unimodular`)"]
theorem isometricGL_padic_of_not_dvd (hp2 : p ≠ 2) {f g : BinQF} (hdisc : f.disc = g.disc)
    (hpD : ¬ (p : ℤ) ∣ f.disc) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) := by
  have hdet : ∀ h : BinQF, (h.map (Int.castRingHom ℤ_[p])).hessian.det = ((-h.disc : ℤ) : ℤ_[p]) := by
    intro h
    rw [hessian_det_two]
    show 4 * (h.a : ℤ_[p]) * (h.c : ℤ_[p]) - (h.b : ℤ_[p]) ^ 2 = _
    simp only [disc]; push_cast; ring
  refine Kneser.isometricGL_of_unimodular hp2 _ _ ?_ ?_
  · rw [hdet]
    intro h
    exact hpD (by simpa using int_dvd_of_padic_dvd h)
  · rw [hdet, hdet, hdisc]

end Padic

/-! ### Values in the right square class at $p = 2$ -/

/-- An odd integer is $1, 3, 5$ or $7$ mod $8$. -/
theorem odd_zmod8 {n : ℤ} (h : ¬ (2 : ℤ) ∣ n) :
    (n : ZMod 8) = 1 ∨ (n : ZMod 8) = 3 ∨ (n : ZMod 8) = 5 ∨ (n : ZMod 8) = 7 := by
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases this with h | h | h | h
  · left; simpa using zmod8_cast_eq_of_emod (r := 1) (by simp [h])
  · right; left; simpa using zmod8_cast_eq_of_emod (r := 3) (by simp [h])
  · right; right; left; simpa using zmod8_cast_eq_of_emod (r := 5) (by simp [h])
  · right; right; right; simpa using zmod8_cast_eq_of_emod (r := 7) (by simp [h])

/-- The square of an odd integer is $\equiv 1 \pmod 8$. -/
theorem sq_odd_zmod8 {n : ℤ} (h : ¬ (2 : ℤ) ∣ n) : (n : ZMod 8) ^ 2 = 1 := by
  rcases odd_zmod8 h with h | h | h | h <;> rw [h] <;> decide

/-- $\psi_2$ through residues mod $8$. -/
theorem genusChar_two_eq (D n : ℤ) : genusChar D 2 n =
    if D % 32 = 8 then ZMod.χ₈ (n : ZMod 8) else if D % 32 = 24 then ZMod.χ₈' (n : ZMod 8)
      else ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) (n : ZMod 8)) := by
  simp [genusChar, map_intCast]

/-- From $8 \mid t - m$ to $t \equiv m$ in $\mathbb{Z}/8$. -/
theorem zmod8_eq_of_dvd {t m : ℤ} (h : (8 : ℤ) ∣ t - m) : (t : ZMod 8) = (m : ZMod 8) :=
  ((ZMod.intCast_eq_intCast_iff_dvd_sub m t 8).mpr (by exact_mod_cast h)).symm

/-- From $t \equiv m$ in $\mathbb{Z}/8$ to $8 \mid t - m$. -/
theorem dvd_of_zmod8_eq {t m : ℤ} (h : (t : ZMod 8) = (m : ZMod 8)) : (8 : ℤ) ∣ t - m := by
  exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub m t 8).mp h.symm

/-- **$p = 2 \nmid D$: $f(1, 2k)$, $k = 0, \dots, 3$, runs through all odd classes mod $8$** (for $a$ odd; then $b$ is
odd). So $f$ primitively represents every odd class mod $8$. -/
theorem exists_value_two_odd {f : BinQF} (hDodd : ¬ (2 : ℤ) ∣ f.disc) (ha : ¬ (2 : ℤ) ∣ f.a) {m : ℤ}
    (hm : ¬ (2 : ℤ) ∣ m) : ∃ x y, IsCoprime x y ∧ ((f.eval x y : ℤ) : ZMod 8) = (m : ZMod 8) := by
  have hb : ¬ (2 : ℤ) ∣ f.b := by
    rintro ⟨t, ht⟩
    apply hDodd
    exact ⟨2 * t ^ 2 - 2 * f.a * f.c, by rw [disc, ht]; ring⟩
  have e : ∀ k : ℤ, f.eval 1 (2 * k) = f.a + 2 * f.b * k + 4 * f.c * k ^ 2 := by
    intro k; rw [eval_eq]; ring
  have hc : ∀ k : ℤ, IsCoprime (1 : ℤ) (2 * k) := fun k => isCoprime_one_left
  by_cases h0 : (8 : ℤ) ∣ f.a - m
  · exact ⟨1, 0, isCoprime_one_left, zmod8_eq_of_dvd (by rw [eval_eq]; simpa using h0)⟩
  by_cases h4 : (8 : ℤ) ∣ f.a + 4 - m
  · refine ⟨1, 2 * 2, hc 2, zmod8_eq_of_dvd ?_⟩
    rw [e]; omega
  by_cases h1 : (8 : ℤ) ∣ f.a + 2 * f.b + 4 * f.c - m
  · refine ⟨1, 2 * 1, hc 1, zmod8_eq_of_dvd ?_⟩
    rw [e]; omega
  · refine ⟨1, 2 * 3, hc 3, zmod8_eq_of_dvd ?_⟩
    rw [e]
    have hm2 : ¬ (2 : ℤ) ∣ m := hm
    have ha2 : ¬ (2 : ℤ) ∣ f.a := ha
    have hb2 : ¬ (2 : ℤ) ∣ f.b := hb
    have hb4 : f.b % 4 = 1 ∨ f.b % 4 = 3 := by omega
    have hc2 : f.c % 2 = 0 ∨ f.c % 2 = 1 := by omega
    have hu : (f.a - m) % 8 = 2 ∨ (f.a - m) % 8 = 6 := by omega
    rcases hb4 with h | h <;> rcases hc2 with h' | h' <;> rcases hu with h'' | h'' <;> omega

/-- **$p = 2 \mid D$: the two odd classes mod $8$ with the character value $\psi_2(a)$ are both represented**
primitively (for $a$ odd): $a$ by $(1, 0)$, and $5a$ by $(1, 2)$ ($\psi_2 = \delta$), $7a$ by $(x, 1)$
($\psi_2 = \varepsilon$), $3a$ by $(x, 1)$ ($\psi_2 = \delta\varepsilon$), from $a f(x, y) = (ax + b'y)^2 - \tfrac D4 y^2$.
So $f$ primitively represents every odd $m$ with $\psi_2(m) = \psi_2(a)$, mod $8$. -/
theorem exists_value_two_even [IsQuadDisc D] {f : BinQF} (hD : f.disc = D) (h2D : (2 : ℤ) ∣ D)
    (ha : ¬ (2 : ℤ) ∣ f.a) {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) (hψ : genusChar D 2 m = genusChar D 2 f.a) :
    ∃ x y, IsCoprime x y ∧ ((f.eval x y : ℤ) : ZMod 8) = (m : ZMod 8) := by
  have hb : (2 : ℤ) ∣ f.b := by
    have : f.b ^ 2 = D + 4 * f.a * f.c := by rw [← hD, disc]; ring
    have h2 : (2 : ℤ) ∣ f.b ^ 2 := by
      rw [this]; exact dvd_add h2D (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (by norm_num) _) _)
    exact int_prime_dvd_of_dvd_sq (p := 2) Nat.prime_two (by exact_mod_cast h2)
  obtain ⟨b', hb'⟩ := hb
  have hd4 : D / 4 = b' ^ 2 - f.a * f.c := by
    rw [← hD, disc, hb']
    rw [show (2 * b') ^ 2 - 4 * f.a * f.c = 4 * (b' ^ 2 - f.a * f.c) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  have hcases := (two_dvd_iff_of_fund (D := D)).mp h2D
  have hA := odd_zmod8 ha
  have hM := odd_zmod8 hm
  rw [genusChar_two_eq, genusChar_two_eq] at hψ
  -- the generic finishing step: a second value `t` with `a t ≡ c₀`, and a check mod 8
  have finish : ∀ x y : ℤ, IsCoprime x y → ((m : ZMod 8) = f.a ∨ (m : ZMod 8) = f.eval x y) →
      ∃ x y, IsCoprime x y ∧ ((f.eval x y : ℤ) : ZMod 8) = (m : ZMod 8) := by
    rintro x y hxy (h | h)
    · exact ⟨1, 0, isCoprime_one_left, by rw [eval_eq]; simpa using h.symm⟩
    · exact ⟨x, y, hxy, h.symm⟩
  -- `a f(x,y) = X² - d y²` in `ℤ/8`
  have hid : ∀ x y : ℤ, ((f.a : ℤ) : ZMod 8) * ((f.eval x y : ℤ) : ZMod 8) =
      ((f.a * x + b' * y : ℤ) : ZMod 8) ^ 2 - ((D / 4 : ℤ) : ZMod 8) * (y : ZMod 8) ^ 2 := by
    intro x y
    have := congrArg (fun z : ℤ => (z : ZMod 8)) (a_mul_eval_of_even f hb' x y)
    rw [hd4]
    push_cast at this ⊢
    exact this
  split_ifs at hψ with h8 h24
  · -- `ψ₂ = ε`, `d ≡ 2 (mod 8)`: `t = f(x, 1)` with `ax + b'` odd, `a t ≡ 7`
    have hd : ((D / 4 : ℤ) : ZMod 8) = 2 := zmod8_cast_eq_of_emod (r := 2) (by omega)
    obtain ⟨x, hx⟩ : ∃ x : ℤ, ¬ (2 : ℤ) ∣ f.a * x + b' * 1 := by
      by_cases hb2 : (2 : ℤ) ∣ b'
      · exact ⟨1, by omega⟩
      · exact ⟨0, by simpa using hb2⟩
    have hAT := hid x 1
    rw [sq_odd_zmod8 hx, hd] at hAT
    norm_num at hAT
    have key : ∀ A T M : ZMod 8, A * T = 1 - 2 → (A = 1 ∨ A = 3 ∨ A = 5 ∨ A = 7) →
        (M = 1 ∨ M = 3 ∨ M = 5 ∨ M = 7) → ZMod.χ₈ M = ZMod.χ₈ A → M = A ∨ M = T := by decide
    exact finish x 1 isCoprime_one_right (key _ _ _ hAT hA hM hψ)
  · -- `ψ₂ = δε`, `d ≡ 6 (mod 8)`: `a t ≡ 3`
    have hd : ((D / 4 : ℤ) : ZMod 8) = 6 := zmod8_cast_eq_of_emod (r := 6) (by omega)
    obtain ⟨x, hx⟩ : ∃ x : ℤ, ¬ (2 : ℤ) ∣ f.a * x + b' * 1 := by
      by_cases hb2 : (2 : ℤ) ∣ b'
      · exact ⟨1, by omega⟩
      · exact ⟨0, by simpa using hb2⟩
    have hAT := hid x 1
    rw [sq_odd_zmod8 hx, hd] at hAT
    norm_num at hAT
    have key : ∀ A T M : ZMod 8, A * T = 1 - 6 → (A = 1 ∨ A = 3 ∨ A = 5 ∨ A = 7) →
        (M = 1 ∨ M = 3 ∨ M = 5 ∨ M = 7) → ZMod.χ₈' M = ZMod.χ₈' A → M = A ∨ M = T := by decide
    exact finish x 1 isCoprime_one_right (key _ _ _ hAT hA hM hψ)
  · -- `ψ₂ = δ`, `d` odd: `t = f(1, 2)`, `a t ≡ 5`
    have hx : ¬ (2 : ℤ) ∣ f.a * 1 + b' * 2 := by omega
    have hd : ((D / 4 : ℤ) : ZMod 8) * ((2 : ℤ) : ZMod 8) ^ 2 = 4 := by
      have hdo : ¬ (2 : ℤ) ∣ D / 4 := by omega
      rcases odd_zmod8 hdo with h | h | h | h <;> rw [h] <;> decide
    have hAT := hid 1 2
    rw [sq_odd_zmod8 hx, hd] at hAT
    have key : ∀ A T M : ZMod 8, A * T = 1 - 4 → (A = 1 ∨ A = 3 ∨ A = 5 ∨ A = 7) →
        (M = 1 ∨ M = 3 ∨ M = 5 ∨ M = 7) →
        ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) M) =
          ZMod.χ₄ (ZMod.castHom (show 4 ∣ 8 by norm_num) (ZMod 4) A) → M = A ∨ M = T := by decide
    exact finish 1 2 isCoprime_one_left (key _ _ _ hAT hA hM hψ)

/-! ### Equal characters imply local equivalence -/

section Local

variable {p : ℕ} [hp : Fact p.Prime]

/-- A primitive form has an equivalent form whose first coefficient is a value prime to $p$. -/
theorem exists_intEquiv_a_not_dvd {f : BinQF} (hf : Primitive f) (hp' : p.Prime) :
    ∃ x y : ℤ, ∃ f' : BinQF, IntEquiv f f' ∧ f'.a = f.eval x y ∧ f'.disc = f.disc ∧
      ¬ (p : ℤ) ∣ f.eval x y := by
  obtain ⟨x, y, -, -, hxy, hv⟩ := exists_coprime_value hf (N := p) hp'.ne_zero
  obtain ⟨f', h1, h2, h3⟩ := exists_intEquiv_a_eq f hxy
  exact ⟨x, y, f', h1, h2, h3, hv p hp' (dvd_refl p)⟩

/-- **Equal characters at $p$ give equivalence over $\mathbb{Z}_p$** (Cassels, Ch. 14, §3, Lemmas 3.1–3.3, pp. 339–340; Gauss §§257–260): for
primitive $f, g$ of fundamental discriminant $D$ and any prime $p$, if $\chi_p(f) = \chi_p(g)$ whenever $p \mid D$,
then $f \cong g$ over $\mathbb{Z}_p$. Move values $m$ of $f$ and $m'$ of $g$ prime to $p$ to the first coefficients;
then $m m'$ is a $p$-adic square (by the character for odd $p \mid D$; after replacing $m$ by a value
$\equiv m' \pmod 8$ for $p = 2$, `exists_value_two_odd`/`exists_value_two_even`), and `isometricGL_padic_of_sq`
applies. For odd $p \nmid D$ the forms are unimodular (`isometricGL_padic_of_not_dvd`). -/
@[kb "cassels1978" "Ch. 14, §3, Lemmas 3.1–3.3, pp. 339–340"]
theorem isometricGL_padic_of_formChar [IsQuadDisc D] {f g : BinQF} (hf : Primitive f) (hg : Primitive g)
    (hfD : f.disc = D) (hgD : g.disc = D) (hchar : (p : ℤ) ∣ D → formChar f p = formChar g p) :
    IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p])) := by
  have hp' := hp.out
  set φ := Int.castRingHom ℤ_[p]
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨x, y, f', hff', hfa, hfd, hm⟩ := exists_intEquiv_a_not_dvd hf hp'
    obtain ⟨x', y', g', hgg', hga, hgd, hm'⟩ := exists_intEquiv_a_not_dvd hg hp'
    push_cast at hm hm'
    have hfa' : ¬ (2 : ℤ) ∣ f'.a := hfa ▸ hm
    have hga' : ¬ (2 : ℤ) ∣ g'.a := hga ▸ hm'
    -- a value of `f'` congruent to `a_{g'}` mod 8
    obtain ⟨x₂, y₂, hc₂, hv₂⟩ : ∃ x₂ y₂, IsCoprime x₂ y₂ ∧
        ((f'.eval x₂ y₂ : ℤ) : ZMod 8) = (g'.a : ZMod 8) := by
      by_cases h2D : (2 : ℤ) ∣ D
      · refine exists_value_two_even (hfd.trans hfD) h2D hfa' hga' ?_
        have e1 := genusChar_eval_eq_formChar hf hfD Nat.prime_two (by exact_mod_cast h2D) x y
          (by exact_mod_cast hm)
        have e2 := genusChar_eval_eq_formChar hg hgD Nat.prime_two (by exact_mod_cast h2D) x' y'
          (by exact_mod_cast hm')
        rw [hfa, hga, e1, e2, hchar (by exact_mod_cast h2D)]
      · exact exists_value_two_odd (by rwa [hfd, hfD]) hfa' hga'
    obtain ⟨f'', hf'f'', hfa'', hfd''⟩ := exists_intEquiv_a_eq f' hc₂
    have hfa''2 : ¬ (2 : ℤ) ∣ f''.a := by
      have := dvd_of_zmod8_eq hv₂
      rw [hfa'']; omega
    obtain ⟨z, hz⟩ := exists_sq_padic_two (c := f''.a * g'.a) (by
      push_cast; rw [hfa'', hv₂, ← sq, sq_odd_zmod8 hga'])
    have hmain := isometricGL_padic_of_sq (p := 2) (by rw [hfd'', hfd, hgd, hfD, hgD]) hfa''2 hga' hz
    exact (hff'.map φ).trans ((hf'f''.map φ).trans (hmain.trans (hgg'.map φ).symm))
  · by_cases hpD : (p : ℤ) ∣ D
    · obtain ⟨x, y, f', hff', hfa, hfd, hm⟩ := exists_intEquiv_a_not_dvd hf hp'
      obtain ⟨x', y', g', hgg', hga, hgd, hm'⟩ := exists_intEquiv_a_not_dvd hg hp'
      have e1 := genusChar_eval_eq_formChar hf hfD hp' hpD x y hm
      have e2 := genusChar_eval_eq_formChar hg hgD hp' hpD x' y' hm'
      have hJ : jacobiSym (f'.a * g'.a) p = 1 := by
        rw [← genusChar_of_ne_two D hp2, genusChar_mul, hfa, hga, e1, e2, hchar hpD, ← sq, ← e2]
        exact genusChar_sq D hp' hm'
      have hnd : ¬ (p : ℤ) ∣ f'.a * g'.a := by
        rw [hfa, hga]; exact fun h => (int_prime_dvd_mul hp' h).elim hm hm'
      obtain ⟨z, hz⟩ := exists_sq_padic_odd hp2 hnd hJ
      have hmain := isometricGL_padic_of_sq (p := p) (by rw [hfd, hgd, hfD, hgD])
        (by rw [hfa]; exact hm) (by rw [hga]; exact hm') hz
      exact (hff'.map φ).trans (hmain.trans (hgg'.map φ).symm)
    · exact isometricGL_padic_of_not_dvd hp2 (hfD.trans hgD.symm) (by rwa [hfD])

/-! ### Local equivalence implies equal characters -/

/-- **A $\mathbb{Z}_p$-equivalence preserves the genus character at $p$** (Gauss §§229–231: the characters are
invariants; here as $p$-adic invariants): if $f \cong g$ over $\mathbb{Z}_p$, $p \mid D$, then
$\chi_p(f) = \chi_p(g)$. A value $m = f(x, y)$ prime to $p$ is a $p$-adic value of $g$; reducing that $p$-adic vector
mod $p$ (mod $8$ if $p = 2$) gives integers $X, Y$ with $g(X, Y) \equiv m$, hence
$\chi_p(g) = \psi_p(g(X, Y)) = \psi_p(m) = \chi_p(f)$. -/
@[kb "cassels1978" "Ch. 14, §3, Lemmas 3.1–3.3, pp. 339–340"]
theorem formChar_eq_of_isometricGL [IsQuadDisc D] {f g : BinQF} (hf : Primitive f) (hg : Primitive g)
    (hfD : f.disc = D) (hgD : g.disc = D) (hpD : (p : ℤ) ∣ D)
    (h : IsometricGL (f.map (Int.castRingHom ℤ_[p])) (g.map (Int.castRingHom ℤ_[p]))) :
    formChar f p = formChar g p := by
  have hp' := hp.out
  obtain ⟨x, y, -, -, -, hxy⟩ := exists_coprime_value hf (N := p) hp'.ne_zero
  have hm := hxy p hp' (dvd_refl p)
  obtain ⟨M, hM⟩ := h
  set v : Fin 2 → ℤ_[p] := ![(x : ℤ_[p]), (y : ℤ_[p])]
  set w := (M⁻¹ : GL (Fin 2) ℤ_[p]).val *ᵥ v
  have hgw : (g.map (Int.castRingHom ℤ_[p])).eval w = ((f.eval x y : ℤ) : ℤ_[p]) := by
    rw [← hM w]
    simp only [w, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
    rw [eval_map_two, eval_eq]
    simp [v]
  set k : ℕ := if p = 2 then 3 else 1
  have hk : (charMod p : ℤ) = (p : ℤ) ^ k := by
    simp only [charMod, k]; split_ifs with h2 <;> simp [h2]
  set ψ := PadicInt.toZModPow (p := p) k
  set X : ℤ := ((ψ (w 0)).val : ℤ)
  set Y : ℤ := ((ψ (w 1)).val : ℤ)
  have hX : ((X : ℤ) : ZMod (p ^ k)) = ψ (w 0) := by simp [X]
  have hY : ((Y : ℤ) : ZMod (p ^ k)) = ψ (w 1) := by simp [Y]
  have hcong : ((g.eval X Y : ℤ) : ZMod (p ^ k)) = ((f.eval x y : ℤ) : ZMod (p ^ k)) := by
    have := congrArg ψ hgw
    rw [eval_map_two] at this
    simp only [map_add, map_mul, map_pow, eq_intCast, map_intCast] at this
    rw [eval_eq]; push_cast
    rw [hX, hY, this]
  have hdiv : (charMod p : ℤ) ∣ g.eval X Y - f.eval x y := by
    rw [hk]
    exact_mod_cast (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcong.symm
  have hpk : (p : ℤ) ∣ (charMod p : ℤ) := by
    rw [hk]; exact dvd_pow_self _ (by simp only [k]; split_ifs <;> norm_num)
  have hgX : ¬ (p : ℤ) ∣ g.eval X Y := by
    intro h'
    apply hm
    have := dvd_sub h' (hpk.trans hdiv)
    simpa using this
  rw [← genusChar_eval_eq_formChar hf hfD hp' hpD x y hm, ← genusChar_eval_eq_formChar hg hgD hp' hpD X Y hgX]
  exact (genusChar_congr D p hdiv).symm

end Local

/-! ### The real place -/

/-- **Positive definite binary forms of the same discriminant are equivalent over $\mathbb{R}$** ($a, a' > 0$, so
$a'/a$ is a square; `isometricGL_map_of_sq`). -/
theorem isometricGL_real {f g : BinQF} (hdisc : f.disc = g.disc) (hf : f.PosDef') (hg : g.PosDef') :
    IsometricGL (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)) := by
  have ha : (0 : ℝ) < f.a := by exact_mod_cast hf.1
  have hb : (0 : ℝ) < g.a := by exact_mod_cast hg.1
  have hs : Real.sqrt (g.a / f.a) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hb ha)).ne'
  refine isometricGL_map_of_sq two_ne_zero _ hdisc (by simpa using ha.ne'.isUnit) (Units.mk0 _ hs) ?_
  simp only [eq_intCast, Units.val_mk0, Real.sq_sqrt (div_pos hb ha).le]
  field_simp

/-! ### The theorem -/

/-- **Genus = local equivalence** (Gauss's genus theory and the local–global description of the genus; Cassels,
*Rational Quadratic Forms*, Ch. 14, §3, p. 339 (genus: equivalence over every $\mathbb{Z}_p$ and $\mathbb{R}$) and Lemmas 3.1–3.3,
pp. 339–340; Cox, §3.B and Theorem 6.1's setting; Buell, Ch. 4): for primitive positive
definite forms $f, g$ of fundamental discriminant $D$,
$$\texttt{SameGenus}\ f\ g \iff \chi_p(f) = \chi_p(g) \text{ for every prime } p \mid D,$$
where `Siegel.SameGenus` is equivalence over $\mathbb{Z}_p$ for every prime $p$ and over $\mathbb{R}$, and
$\chi_p = $ `formChar` are Gauss's genus characters (well defined by `genusChar_eval_eq_formChar`). Purely local:
`formChar_eq_of_isometricGL` ($\Rightarrow$) and `isometricGL_padic_of_formChar`, `isometricGL_real` ($\Leftarrow$). -/
@[kb "cassels1978" "Ch. 14, §3, p. 339 (genus), Lemmas 3.1–3.3, pp. 339–340"]
theorem sameGenus_iff_formChar_eq [IsQuadDisc D] {f g : BinQF} (hf : Primitive f) (hg : Primitive g)
    (hfD : f.disc = D) (hgD : g.disc = D) (hfpos : f.PosDef') (hgpos : g.PosDef') :
    SameGenus f g ↔ ∀ p ∈ D.natAbs.primeFactors, formChar f p = formChar g p := by
  constructor
  · intro h p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    exact formChar_eq_of_isometricGL hf hg hfD hgD
      (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp)) (h.1 p)
  · intro h
    refine ⟨fun p _ => ?_, isometricGL_real (hfD.trans hgD.symm) hfpos hgpos⟩
    refine isometricGL_padic_of_formChar hf hg hfD hgD fun hpD => h p ?_
    have hN : D.natAbs ≠ 0 := by have := three_le_natAbs (D := D); omega
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, Int.natCast_dvd.mp hpD, hN⟩

end QuadFormsKB.Binary
