import QuadFormsKB.Literature.LocalGlobal.ConwaySloane
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.LocalGlobal.HasseConventions
import QuadFormsKB.Literature.LocalGlobal.LocalClassificationNF

/-!
# Conway–Sloane, Ch. 15, §§5–6: rational classification by the $p$-excesses

J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 15, §§5–6, pp. 371–378
(`conwaysloane1999`). Forms are integer diagonal forms $\mathrm{diag}\{a_0, \dots, a_{n-1}\}$ (0-based), with the
$p$-excesses and oddity of `Literature/LocalGlobal/ConwaySloane.lean`.

**Proves**
* the explicit small equivalences of §2 and §6.3 ((21), the $p = 2$ list, $\langle 1,1\rangle \not\cong_{\mathbb Z}
  \langle 2, 2\rangle$ while $\cong_{\mathbb Q}$);
* the replacement lemma, Theorem 8 (`replacement_lemma`, with its binary and ternary steps);
* Theorem 3 (`theorem3`, `theorem3_excess`) and Theorem 4 (`theorem4`). *Route:* through Hasse–Minkowski
  (`isometric_iff_everywhere`) and the relation of the excesses to the Hasse invariants, not through the book's §6
  induction;
* Theorem 7 (`theorem7`), as a corollary of Theorem 3;
* Table 15.3 at $p = 2$: the representation criterion by oddities (`represents_two_adic_iff_oddity`) and the finite check
  of the 64 table entries (`table_check`).
-/

namespace QuadFormsKB.ConwaySloane.Rational

open QuadForm Matrix Finset

/-! ### Explicit isometries of small diagonal forms -/

theorem isometricIn_diag_two_mk (a0 a1 b0 b1 p00 p01 p10 p11 : ℚ)
    (hdet : p00 * p11 - p01 * p10 ≠ 0)
    (h : ∀ x0 x1 : ℚ, a0 * (p00 * x0 + p01 * x1) ^ 2 + a1 * (p10 * x0 + p11 * x1) ^ 2 =
      b0 * x0 ^ 2 + b1 * x1 ^ 2) :
    (diag ![a0, a1]).IsometricIn ℚ (diag ![b0, b1]) := by
  refine ⟨!![p00, p01; p10, p11], ?_, fun x => ?_⟩
  · rw [Matrix.det_fin_two_of]; exact isUnit_iff_ne_zero.mpr hdet
  · simp only [evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h (x 0) (x 1)

theorem isometricIn_diag_snoc {a0 a1 b0 b1 : ℚ} (c : ℚ)
    (h : (diag ![a0, a1]).IsometricIn ℚ (diag ![b0, b1])) :
    (diag ![a0, a1, c]).IsometricIn ℚ (diag ![b0, b1, c]) := by
  obtain ⟨P, hP, hev⟩ := h
  refine ⟨!![P 0 0, P 0 1, 0; P 1 0, P 1  1, 0; 0, 0, 1], ?_, fun x => ?_⟩
  · rw [Matrix.det_fin_three]
    rw [Matrix.det_fin_two] at hP
    simpa using hP
  · have := hev ![x 0, x 1]
    simp only [evalIn_diag, Algebra.algebraMap_self, RingHom.id_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two] at this ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three] at this ⊢
    linarith

/-! ### Binary forms: the §6.1 observation and the equivalences (21), §6.3 -/

/-- **The observation of §6.1**: a nondegenerate binary form $\langle A, B\rangle$ over $\mathbb{Q}$ that represents
$c \ne 0$ is equivalent to $\langle c, AB/c\rangle$ (the class of a binary form is determined by its determinant and
one represented number). Explicit change of variables: if $A x^2 + B y^2 = c$, then
$(u,v) \mapsto (x u - B y v/c,\; y u + A x v/c)$ has determinant $1$ and carries $\langle A, B\rangle$ to
$\langle c, AB/c\rangle$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, p. 373"]
theorem binary_equiv_of_represents {A B c x y : ℚ} (hc : c ≠ 0) (hxy : A * x ^ 2 + B * y ^ 2 = c) :
    (diag ![A, B]).IsometricIn ℚ (diag ![c, A * B / c]) := by
  subst hxy
  refine isometricIn_diag_two_mk _ _ _ _ x (-(B * y / (A * x ^ 2 + B * y ^ 2))) y
    (A * x / (A * x ^ 2 + B * y ^ 2)) ?_ ?_
  · have : x * (A * x / (A * x ^ 2 + B * y ^ 2)) -
        -(B * y / (A * x ^ 2 + B * y ^ 2)) * y = 1 := by
      calc _ = (A * x ^ 2 + B * y ^ 2) / (A * x ^ 2 + B * y ^ 2) := by ring
        _ = 1 := div_self hc
    rw [this]; exact one_ne_zero
  · intro u v
    field_simp
    ring

/-- Swapping the two entries of a binary diagonal form is an isometry. -/
theorem diag_two_swap (a b : ℚ) : (diag ![a, b]).IsometricIn ℚ (diag ![b, a]) :=
  isometricIn_diag_two_mk _ _ _ _ 0 1 1 0 (by norm_num) fun x0 x1 => by ring

/-- Scaling the second entry of a binary diagonal form by a square: $\langle c, d\rangle \cong \langle c, s^2 d\rangle$
for $s \ne 0$. -/
theorem diag_two_scale (c d s : ℚ) (hs : s ≠ 0) :
    (diag ![c, d]).IsometricIn ℚ (diag ![c, s ^ 2 * d]) :=
  isometricIn_diag_two_mk _ _ _ _ 1 0 0 s (by simpa using hs) fun x0 x1 => by ring

/-- **Equation (21)** (§6.3, p. 378; the book writes it for the $p$-terms $-p, p$ of an integral form):
$\mathrm{diag}\{-p, p\} \sim \mathrm{diag}\{-1, 1\}$ over $\mathbb{Q}$, for **every** nonzero rational $p$.
Explicit substitution: $y_0 = \tfrac12\big((1+\tfrac1p)x_0 + (1-\tfrac1p)x_1\big)$,
$y_1 = \tfrac12\big((1-\tfrac1p)x_0 + (1+\tfrac1p)x_1\big)$ (determinant $1/p$), since
$-p y_0^2 + p y_1^2 = p(y_1-y_0)(y_1+y_0) = (x_1 - x_0)(x_1+x_0)$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, p. 378, eq. (21)"]
theorem diag_neg_p_p_equiv (p : ℚ) (hp : p ≠ 0) :
    (diag ![-p, p]).IsometricIn ℚ (diag ![-1, 1]) := by
  refine isometricIn_diag_two_mk _ _ _ _ ((1 + 1 / p) / 2) ((1 - 1 / p) / 2) ((1 - 1 / p) / 2)
    ((1 + 1 / p) / 2) ?_ fun x0 x1 => ?_
  · have : (1 + 1 / p) / 2 * ((1 + 1 / p) / 2) - (1 - 1 / p) / 2 * ((1 - 1 / p) / 2) = 1 / p := by
      ring
    rw [this]; exact one_div_ne_zero hp
  · field_simp
    ring

/-- The companion of (21) with the signs exchanged, $\mathrm{diag}\{p, -p\} \sim \mathrm{diag}\{1, -1\}$ (used in the
$p = 2$ list, p. 378, with $p = 2$: $\mathrm{diag}\{2,-2\} \sim \mathrm{diag}\{1,-1\}$); same substitution as
`diag_neg_p_p_equiv`. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, p. 378 (p = 2 list, second equivalence)"]
theorem diag_p_neg_p_equiv (p : ℚ) (hp : p ≠ 0) :
    (diag ![p, -p]).IsometricIn ℚ (diag ![1, -1]) := by
  refine isometricIn_diag_two_mk _ _ _ _ ((1 + 1 / p) / 2) ((1 - 1 / p) / 2) ((1 - 1 / p) / 2)
    ((1 + 1 / p) / 2) ?_ fun x0 x1 => ?_
  · have : (1 + 1 / p) / 2 * ((1 + 1 / p) / 2) - (1 - 1 / p) / 2 * ((1 - 1 / p) / 2) = 1 / p := by
      ring
    rw [this]; exact one_div_ne_zero hp
  · field_simp
    ring

/-- **§6.3, $p = 2$, first equivalence** (p. 378): $\mathrm{diag}\{2, 2\} \sim \mathrm{diag}\{1, 1\}$ over $\mathbb{Q}$,
by $(x_0, x_1) \mapsto \tfrac12(x_0 + x_1,\, x_0 - x_1)$ (determinant $-\tfrac12$): $2 y_0^2 + 2 y_1^2 =
x_0^2 + x_1^2$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, p. 378 (p = 2 list, first equivalence)"]
theorem diag_two_two_equiv : (diag ![(2 : ℚ), 2]).IsometricIn ℚ (diag ![1, 1]) :=
  isometricIn_diag_two_mk _ _ _ _ (1 / 2) (1 / 2) (1 / 2) (-1 / 2) (by norm_num) fun x0 x1 => by ring

/-- **§6.3, $p = 2$, third equivalence** (p. 378): $\mathrm{diag}\{-2, -2\} \sim \mathrm{diag}\{-1, -1\}$ over
$\mathbb{Q}$ (the same substitution, negated). -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, p. 378 (p = 2 list, third equivalence)"]
theorem diag_neg_two_neg_two_equiv : (diag ![(-2 : ℚ), -2]).IsometricIn ℚ (diag ![-1, -1]) :=
  isometricIn_diag_two_mk _ _ _ _ (1 / 2) (1 / 2) (1 / 2) (-1 / 2) (by norm_num) fun x0 x1 => by ring

/-- **§2, p. 356 (worked example)**: $x^2 + y^2 \cong 2 z^2 + 2 t^2$ over $\mathbb{Q}$ (the same equivalence as
`diag_two_two_equiv`, read backwards). -/
@[kb "conwaysloane1999" "Ch. 15, §2, p. 356"]
theorem diag_one_one_equiv_two_two : (diag ![(1 : ℚ), 1]).IsometricIn ℚ (diag ![2, 2]) :=
  isometricIn_symm ℚ diag_two_two_equiv

/-- **§2, p. 356: the equivalence above is not an integral one.** There is no $U \in \mathrm{GL}_2(\mathbb{Z})$
(integer entries $u_{ij}$, $\det U = \pm 1$) with $2(u_{00}x_0 + u_{01}x_1)^2 + 2(u_{10}x_0 + u_{11}x_1)^2 = x_0^2 + x_1^2$
(at $x = e_0$ the left side is even and the right side is $1$); and none in the other direction,
$(u_{00}x_0 + u_{01}x_1)^2 + (u_{10}x_0 + u_{11}x_1)^2 = 2x_0^2 + 2x_1^2$ (apply the first-direction
argument to $x = U^{-1} e_0$: the left side is then $1$, the right side even). -/
@[kb "conwaysloane1999" "Ch. 15, §2, p. 356"]
theorem not_intEquiv_one_one_two_two :
    (¬ ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ ∀ x0 x1 : ℤ,
      2 * (U 0 0 * x0 + U 0 1 * x1) ^ 2 + 2 * (U 1 0 * x0 + U 1 1 * x1) ^ 2 = x0 ^ 2 + x1 ^ 2) ∧
    (¬ ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ ∀ x0 x1 : ℤ,
      (U 0 0 * x0 + U 0 1 * x1) ^ 2 + (U 1 0 * x0 + U 1 1 * x1) ^ 2 = 2 * x0 ^ 2 + 2 * x1 ^ 2) := by
  constructor
  · rintro ⟨U, -, h⟩
    have h1 := h 1 0
    have : (2 : ℤ) ∣ 1 := ⟨(U 0 0 * 1 + U 0 1 * 0) ^ 2 + (U 1 0 * 1 + U 1 1 * 0) ^ 2, by linarith⟩
    omega
  · rintro ⟨U, hU, h⟩
    have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
    have e00 := congrFun (congrFun h1 0) 0
    have e10 := congrFun (congrFun h1 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
      ne_eq, Fin.isValue, one_ne_zero, not_false_eq_true] at e00 e10
    have h2 := h (U⁻¹ 0 0) (U⁻¹ 1 0)
    rw [e00, e10] at h2
    have : (2 : ℤ) ∣ 1 := ⟨U⁻¹ 0 0 ^ 2 + U⁻¹ 1 0 ^ 2, by linarith⟩
    omega

/-! ### Theorem 8: the replacement lemma -/

/-- **Theorem 8, binary core** (the identity of the proof, p. 377): for integers with $ab = x^2 - p y$, $y \ne 0$ and
$p, a, b, t \ne 0$, the form $\mathrm{diag}\{pat, -pbt\}$ represents $-ybt$ (by
$pat\,(b/p)^2 - pbt\,(x/p)^2 = -ybt$), hence, by the observation of §6.1 (`binary_equiv_of_represents`),
$\mathrm{diag}\{pat, -pbt\} \sim \mathrm{diag}\{yat, -ybt\}$ over $\mathbb{Q}$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377"]
theorem replacement_binary {p a b t x y : ℤ} (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hy : y ≠ 0) (hab : a * b = x ^ 2 - p * y) :
    (diag ![(p : ℚ) * a * t, -((p : ℚ) * b * t)]).IsometricIn ℚ
      (diag ![(y : ℚ) * a * t, -((y : ℚ) * b * t)]) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy
  have hab' : (a : ℚ) * b = x ^ 2 - p * y := by exact_mod_cast hab
  have hc : -((y : ℚ) * b * t) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hy' hb') ht')
  have hrep : (p : ℚ) * a * t * (b / p) ^ 2 + -((p : ℚ) * b * t) * (x / p) ^ 2 = -((y : ℚ) * b * t) := by
    have e1 : (p : ℚ) * a * t * (b / p) ^ 2 + -((p : ℚ) * b * t) * (x / p) ^ 2 =
        b * t / p * ((a : ℚ) * b - x ^ 2) := by
      field_simp
      ring
    rw [e1, hab']
    field_simp
    ring
  have h1 := binary_equiv_of_represents hc hrep
  have e : ((p : ℚ) * a * t) * (-((p : ℚ) * b * t)) / -((y : ℚ) * b * t) =
      ((p : ℚ) / y) ^ 2 * ((y : ℚ) * a * t) := by
    field_simp
  rw [e] at h1
  exact isometricIn_trans ℚ (isometricIn_trans ℚ h1 (isometricIn_symm ℚ (diag_two_scale _ _ _ (div_ne_zero hp' hy'))))
    (diag_two_swap _ _)

/-- $x^2 - y^2$ represents every number: $\mathrm{diag}\{1,-1\} \sim \mathrm{diag}\{-q, q\}$ for $q \ne 0$
(the isotropic binary form, p. 377, "$x^2 - y^2$ represents all numbers, in particular $-pbt$"). Substitution
$y_0 = \tfrac12((q-1)x_0 + (q+1)x_1)$, $y_1 = \tfrac12((q+1)x_0 + (q-1)x_1)$ (determinant $-q$). -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377"]
theorem diag_one_neg_one_equiv (q : ℚ) (hq : q ≠ 0) :
    (diag ![(1 : ℚ), -1]).IsometricIn ℚ (diag ![-q, q]) := by
  refine isometricIn_diag_two_mk _ _ _ _ ((q - 1) / 2) ((q + 1) / 2) ((q + 1) / 2) ((q - 1) / 2) ?_
    fun x0 x1 => by ring
  have : (q - 1) / 2 * ((q - 1) / 2) - (q + 1) / 2 * ((q + 1) / 2) = -q := by ring
  rw [this]; exact neg_ne_zero.mpr hq

/-- **Theorem 8, ternary form** (p. 377): with $ab = x^2 - py$ ($y \ne 0$, $p,a,b,t \ne 0$),
$$\mathrm{diag}\{pat, 1, -1\} \sim \mathrm{diag}\{yat, -ybt, pbt\}$$
over $\mathbb{Q}$: the chain $\mathrm{diag}\{pat,1,-1\} \sim \mathrm{diag}\{pat,-pbt,pbt\} \sim
\mathrm{diag}\{yat,-ybt,pbt\}$ of the book (the first step is `diag_one_neg_one_equiv`, the second is
`replacement_binary` with $pbt$ carried along). -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377"]
theorem replacement_ternary {p a b t x y : ℤ} (hp : p ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hy : y ≠ 0) (hab : a * b = x ^ 2 - p * y) :
    (diag ![(p : ℚ) * a * t, 1, -1]).IsometricIn ℚ
      (diag ![(y : ℚ) * a * t, -((y : ℚ) * b * t), (p : ℚ) * b * t]) := by
  have hq : (p : ℚ) * b * t ≠ 0 := by
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have : (t : ℚ) ≠ 0 := by exact_mod_cast ht
    positivity
  have h1 : (diag ![(p : ℚ) * a * t, 1, -1]).IsometricIn ℚ
      (diag ![(p : ℚ) * a * t, -((p : ℚ) * b * t), (p : ℚ) * b * t]) :=
    isometricIn_diag_cons_of ℚ ((p : ℚ) * a * t) (α := ![1, -1]) (β := ![-((p : ℚ) * b * t), (p : ℚ) * b * t])
      (diag_one_neg_one_equiv _ hq)
  exact isometricIn_trans ℚ h1 (isometricIn_diag_snoc _ (replacement_binary hp ha hb ht hy hab))

/-- **Theorem 8, degenerate case** $y = 0$ (not discussed in the book): if $ab = x^2$ exactly, then the single terms
$\langle pat \rangle$ and $\langle pbt \rangle$ are already equivalent over $\mathbb{Q}$ (by $u \mapsto (x/a) u$, as
$pat\,(x/a)^2 = p t\,x^2/a = pbt$). So replacing $pat$ by $pbt$ is a rational equivalence with no
adjoined summands. *Update:* the proof of Theorem 8 as printed divides by $y$ ($\langle yat, -ybt\rangle$ has a zero entry
when $y=0$); this case must be handled separately, as here. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377 (Update: case y = 0)"]
theorem replacement_degenerate {p a b t x : ℤ} (ha : a ≠ 0) (hx : x ≠ 0) (hab : a * b = x ^ 2) :
    (diag ![(p : ℚ) * a * t]).IsometricIn ℚ (diag ![(p : ℚ) * b * t]) := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hab' : (a : ℚ) * b = x ^ 2 := by exact_mod_cast hab
  refine ⟨!![(x : ℚ) / a], ?_, fun u => ?_⟩
  · rw [Matrix.det_fin_one_of]; exact isUnit_iff_ne_zero.mpr (div_ne_zero hx' ha')
  · simp [evalIn_diag, dotProduct]
    field_simp
    rw [← hab']
    ring

/-- **The bound on $y$** (p. 377: "$ab = x^2 - py$, with $|x| < \tfrac12 p$, and so $|y| < p$"): for $p \ge 3$,
$-1 \le a, b \le p - 1$ and $2|x| < p$, $ab = x^2 - py$ forces $|y| < p$. Consequently every prime dividing $y \ne 0$ is
$< p$ (`prime_lt_of_dvd_of_abs_lt`): the replacement introduces no prime $\ge p$ beyond those already
present. -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377"]
theorem replacement_abs_lt {p a b x y : ℤ} (hp : 3 ≤ p) (ha1 : -1 ≤ a) (ha2 : a < p) (hb1 : -1 ≤ b)
    (hb2 : b < p) (hx : 2 * |x| < p) (hab : a * b = x ^ 2 - p * y) : |y| < p := by
  have hx2 : 4 * x ^ 2 < p ^ 2 := by
    have h0 : 0 ≤ |x| := abs_nonneg x
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith
  have hu : a * b ≤ p * p - p + 1 := by nlinarith
  have hl : -a - b - 1 ≤ a * b := by nlinarith
  rw [abs_lt]
  constructor
  · by_contra hcon
    replace hcon := not_lt.mp hcon
    nlinarith [sq_nonneg x]
  · by_contra hcon
    replace hcon := not_lt.mp hcon
    nlinarith

/-- Every prime dividing a nonzero integer $y$ with $|y| < p$ is less than $p$. -/
theorem prime_lt_of_dvd_of_abs_lt {p y : ℤ} (hy : y ≠ 0) (hyp : |y| < p) {q : ℕ} (hq : (q : ℤ) ∣ y) :
    (q : ℤ) < p := by
  have := Int.le_of_dvd (abs_pos.mpr hy) ((dvd_abs _ _).mpr hq)
  omega

/-- A centered representative: for odd $p > 0$ and any $z$ there is $x \equiv z \pmod p$ with $2|x| < p$. -/
theorem exists_centered_rep (p z : ℤ) (hp : Odd p) (hp0 : 0 < p) : ∃ x, 2 * |x| < p ∧ p ∣ x - z := by
  obtain ⟨k, hk⟩ := hp
  have h0 := Int.emod_nonneg z hp0.ne'
  have h1 := Int.emod_lt_of_pos z hp0
  have hd : z % p = z - p * (z / p) := Int.emod_def z p
  by_cases hc : 2 * (z % p) < p
  · refine ⟨z % p, ?_, ⟨-(z / p), ?_⟩⟩
    · rw [abs_of_nonneg h0]; exact hc
    · rw [hd]; ring
  · refine ⟨z % p - p, ?_, ⟨-(z / p) - 1, ?_⟩⟩
    · rw [abs_of_neg (by omega)]; omega
    · rw [hd]; ring

/-- **Theorem 8, with its hypothesis as printed** (p. 377): let $p \ge 3$ be odd, $-1 \le a, b < p$ nonzero with $ab$
congruent to a square modulo $p$, and $t \ne 0$. Then there are integers $x, y$ with $ab = x^2 - py$,
$|x| < p/2$ and $|y| < p$, and if $y \ne 0$ (i.e. $ab$ is not itself a square; for $y = 0$ see
`replacement_degenerate`) the $p$-term $pat$ may be replaced by $pbt$ at the cost of adjoining $\pm 1$:
$\mathrm{diag}\{pat, 1, -1\} \sim \mathrm{diag}\{yat, -ybt, pbt\}$, where $|y| < p$ so every prime dividing $y$ is
$< p$ (the "no larger prime" clause). -/
@[kb "conwaysloane1999" "Ch. 15, §6.3, Thm. 8, p. 377"]
theorem replacement_lemma {p a b t : ℤ} (hp : 3 ≤ p) (hpo : Odd p) (ha1 : -1 ≤ a) (ha2 : a < p) (hb1 : -1 ≤ b)
    (hb2 : b < p) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (hsq : ∃ z : ℤ, p ∣ a * b - z ^ 2) :
    ∃ x y : ℤ, 2 * |x| < p ∧ |y| < p ∧ a * b = x ^ 2 - p * y ∧
      (y ≠ 0 →
        (diag ![(p : ℚ) * a * t, 1, -1]).IsometricIn ℚ
          (diag ![(y : ℚ) * a * t, -((y : ℚ) * b * t), (p : ℚ) * b * t]) ∧
        ∀ q : ℕ, (q : ℤ) ∣ y → (q : ℤ) < p) := by
  obtain ⟨z, c, hc⟩ := hsq
  obtain ⟨x, hx, m, hm⟩ := exists_centered_rep p z hpo (by omega)
  have hxz : x = z + p * m := by linarith
  have hab : a * b = x ^ 2 - p * (m * (2 * z + p * m) - c) := by
    rw [hxz]; linear_combination hc
  have hy := replacement_abs_lt hp ha1 ha2 hb1 hb2 hx hab
  refine ⟨x, m * (2 * z + p * m) - c, hx, hy, hab, fun hy0 => ⟨?_, fun q hq => ?_⟩⟩
  · exact replacement_ternary (by omega) ha hb ht hy0 hab
  · exact prime_lt_of_dvd_of_abs_lt hy0 hy hq

/-! ### The invariants depend only on the square class of the determinant -/

/-- The $p$-excess of $\langle x^2 \rangle$ vanishes ($p$ odd, $x \ne 0$). -/
theorem pExcessEntry_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {x : ℤ} (hx : x ≠ 0) :
    pExcessEntry p (x ^ 2) = 0 := by
  have hr := natCast_zmod8_odd (hp.out.odd_of_ne_two hp2)
  rw [pow_two]
  unfold pExcessEntry
  rw [padicValInt.mul hx hx, pow_zmod8_eq hr]
  have : ¬ Odd (padicValInt p x + padicValInt p x) := Nat.not_odd_iff_even.mpr ⟨_, rfl⟩
  simp [this]

/-- The oddity of $\langle x^2 \rangle$ is $1$ ($x \ne 0$): the unit part of $x^2$ is a square of an odd number,
$\equiv 1 \pmod 8$, and the exponent of $2$ is even. -/
theorem oddityEntry_sq {x : ℤ} (hx : x ≠ 0) : oddityEntry (x ^ 2) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu := intCast_zmod8_odd (by exact_mod_cast not_dvd_unitPart (p := 2) hx)
  rw [pow_two]
  unfold oddityEntry
  rw [padicValInt.mul hx hx, unitPart_mul hx hx, Int.cast_mul]
  have : ¬ Odd (padicValInt 2 x + padicValInt 2 x) := Nat.not_odd_iff_even.mpr ⟨_, rfl⟩
  simp only [this, false_and, ite_false, add_zero]
  generalize ((unitPart 2 x : ℤ) : ZMod 8) = r at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

theorem sgn4_one : sgn4 1 = 0 := by simp [sgn4]

/-- $p$-excess of $\langle D x^2\rangle$ equals that of $\langle D\rangle$ ($p$ odd). -/
theorem pExcessEntry_mul_sq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {D x : ℤ} (hD : D ≠ 0) (hx : x ≠ 0) :
    pExcessEntry p (D * x ^ 2) = pExcessEntry p D := by
  have h := pExcessEntry_mul p hp2 hD (pow_ne_zero 2 hx)
  rw [pExcessEntry_sq p hp2 hx] at h
  have hh : (RatPlace.finite ⟨p, hp.out⟩).hilbert (D : ℚ) ((x ^ 2 : ℤ) : ℚ) = 1 := by
    push_cast
    exact RatPlace.hilbert_sq_right _ _ _ (by exact_mod_cast hx)
  rw [hh, sgn4_one] at h
  linear_combination -h

/-- Oddity of $\langle D x^2\rangle$ equals that of $\langle D\rangle$. -/
theorem oddityEntry_mul_sq {D x : ℤ} (hD : D ≠ 0) (hx : x ≠ 0) :
    oddityEntry (D * x ^ 2) = oddityEntry D := by
  have h := oddityEntry_mul hD (pow_ne_zero 2 hx)
  rw [oddityEntry_sq hx] at h
  have hh : (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert (D : ℚ) ((x ^ 2 : ℤ) : ℚ) = 1 := by
    push_cast
    exact RatPlace.hilbert_sq_right _ _ _ (by exact_mod_cast hx)
  rw [hh, sgn4_one] at h
  linear_combination -h

/-- **Square-class invariance of the rank-one $p$-excess**: if $D D'$ is a perfect square ($D, D' \ne 0$, $p$ odd) then
$p\text{-excess}\langle D\rangle = p\text{-excess}\langle D'\rangle$. -/
theorem pExcessEntry_congr (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) {D D' m : ℤ} (hD : D ≠ 0) (hD' : D' ≠ 0)
    (h : D * D' = m ^ 2) : pExcessEntry p D' = pExcessEntry p D := by
  have hm : m ≠ 0 := fun h0 => by
    rw [h0] at h; simp at h; rcases h with h | h <;> contradiction
  have e1 := pExcessEntry_mul_sq p hp2 hD' hD
  have e2 := pExcessEntry_mul_sq p hp2 hD hm
  rw [← e1, ← e2]
  congr 1
  linear_combination D * h

/-- **Square-class invariance of the rank-one oddity**: if $D D'$ is a perfect square then $\mathrm{oddity}\langle D\rangle =
\mathrm{oddity}\langle D'\rangle$. -/
theorem oddityEntry_congr {D D' m : ℤ} (hD : D ≠ 0) (hD' : D' ≠ 0)
    (h : D * D' = m ^ 2) : oddityEntry D' = oddityEntry D := by
  have hm : m ≠ 0 := fun h0 => by
    rw [h0] at h; simp at h; rcases h with h | h <;> contradiction
  have e1 := oddityEntry_mul_sq hD' hD
  have e2 := oddityEntry_mul_sq hD hm
  rw [← e1, ← e2]
  congr 1
  linear_combination D * h

/-- If the quotient $A/B$ of two integers ($B \ne 0$) is a rational square then $AB$ is the square of an integer. -/
theorem exists_int_sq_of_isSquare_div {A B : ℤ} (hB : B ≠ 0) (h : IsSquare ((A : ℚ) / (B : ℚ))) :
    ∃ m : ℤ, A * B = m ^ 2 := by
  obtain ⟨s, hs⟩ := h
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have e : ((A * B : ℤ) : ℚ) = ((B : ℚ) * s) * ((B : ℚ) * s) := by
    push_cast
    have : (A : ℚ) = (B : ℚ) * s * s := by
      field_simp at hs; linarith
    rw [this]; ring
  have : IsSquare ((A * B : ℤ) : ℚ) := ⟨_, e⟩
  obtain ⟨m, hm⟩ := Rat.isSquare_intCast_iff.mp this
  exact ⟨m, by rw [hm]; ring⟩

/-! ### Theorem 3 (via Hasse–Minkowski) -/

variable {n : ℕ}

/-- **The rational diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ of an integer vector** (the book's "form
$\mathrm{diag}\{A_1, \dots, A_n\}$", 0-based here), viewed in $\mathbb{Q}[x_0,\dots,x_{n-1}]$. -/
def intDiag (a : Fin n → ℤ) : QuadForm ℚ n := diag fun i => (a i : ℚ)

/-- **Equivalence over the rationals** of two integer diagonal forms: $\mathrm{diag}\{a\}(P x) = \mathrm{diag}\{b\}(x)$ for
some $P \in \mathrm{GL}_n(\mathbb{Q})$ (`QuadForm.IsometricIn ℚ`). -/
def RatEquivalent (a b : Fin n → ℤ) : Prop := (intDiag a).IsometricIn ℚ (intDiag b)

theorem sgn4_inj {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) : sgn4 x = sgn4 y ↔ x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [sgn4] <;> decide

/-- **The signature in terms of the number of negative entries**: $\mathrm{signature} = n - 2 n_-$. -/
theorem signature_eq_sub (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) :
    signature a = n - 2 * (negCount fun i => (a i : ℚ) : ℕ) := by
  have key : ∀ i, Int.sign (a i) = 1 - 2 * (if (a i : ℚ) < 0 then (1 : ℤ) else 0) := by
    intro i
    rcases lt_or_gt_of_ne (ha i) with h | h
    · have h' : (a i : ℚ) < 0 := by exact_mod_cast h
      simp [Int.sign_eq_neg_one_of_neg h, h']
    · have h' : ¬ (a i : ℚ) < 0 := by
        have : (0 : ℚ) < a i := by exact_mod_cast h
        exact not_lt.mpr this.le
      simp [Int.sign_eq_one_of_pos h, h']
  unfold signature negCount
  rw [Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- Integer diagonal forms with the same number of negative entries are equivalent over $\mathbb{R}$ (Sylvester). -/
theorem isometricIn_real_of_negCount {n : ℕ} (a b : Fin n → ℚ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (h : negCount a = negCount b) : (diag a).IsometricIn ℝ (diag b) := by
  rw [isometricIn_cast]
  have ha' : ∀ i, algebraMap ℚ ℝ (a i) ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, algebraMap ℚ ℝ (b i) ≠ 0 := fun i => by simpa using hb i
  rw [LocalClassNF.isometric_real_vec_iff _ _ ha' hb']
  have : ∀ c : Fin n → ℚ, HasseIsoNF.negCountR (fun i => algebraMap ℚ ℝ (c i)) = negCount c := by
    intro c
    simp [HasseIsoNF.negCountR, negCount]
  rw [this, this]; exact h

/-- **$p$-excess equality is Hasse-invariant equality** ($p$ odd, determinants in the same square class). -/
theorem pExcess_eq_iff_hasse (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (a b : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hsq : ∃ m : ℤ, (∏ i, a i) * (∏ i, b i) = m ^ 2) :
    pExcess p a = pExcess p b ↔
      (RatPlace.finite ⟨p, hp.out⟩).hasseSerre (fun i => (a i : ℚ)) =
        (RatPlace.finite ⟨p, hp.out⟩).hasseSerre (fun i => (b i : ℚ)) := by
  obtain ⟨m, hm⟩ := hsq
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  rw [pExcess_eq_hasse p hp2 a ha, pExcess_eq_hasse p hp2 b hb, pExcessEntry_congr p hp2 hA hB hm,
    add_right_inj, sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]

/-- **Oddity equality is Hasse-invariant equality at 2** (determinants in the same square class). -/
theorem oddity_eq_iff_hasse (a b : Fin n → ℤ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (hsq : ∃ m : ℤ, (∏ i, a i) * (∏ i, b i) = m ^ 2) :
    oddity a = oddity b ↔
      (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre (fun i => (a i : ℚ)) =
        (RatPlace.finite ⟨2, Nat.prime_two⟩).hasseSerre (fun i => (b i : ℚ)) := by
  obtain ⟨m, hm⟩ := hsq
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  rw [oddity_eq_hasse a ha, oddity_eq_hasse b hb, oddityEntry_congr hA hB hm,
    add_right_inj, sgn4_inj (hasseSerre_pm _ _) (hasseSerre_pm _ _)]

/-- **Theorem 3, "only if"**: rational equivalence of nonsingular integer diagonal forms forces (i) the quotient of the
determinants to be a rational square and (ii)' equal signature, oddity and $p$-excesses at all odd primes
(and hence (ii)). -/
theorem theorem3_of_equiv (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (h : RatEquivalent a b) :
    IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ)) ∧ signature a = signature b ∧
      oddity a = oddity b ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → pExcess p a = pExcess p b := by
  have ha' : ∀ i, (fun i => (a i : ℚ)) i ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, (fun i => (b i : ℚ)) i ≠ 0 := fun i => by simpa using hb i
  have hev := (isometric_iff_everywhere (intDiag a) (intDiag b) (nondegenerate_diag ha')
    (nondegenerate_diag hb')).mp h
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  obtain ⟨t, ht, e⟩ := sameSq_gen (K := ℚ) (fun i => (a i : ℚ)) (fun i => (b i : ℚ)) h
  have hsqQ : IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ)) := by
    refine ⟨1 / t, ?_⟩
    have hA' : ((∏ i, a i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hA
    simp only [Rat.cast_id] at e
    push_cast at e ⊢
    rw [e]
    have : (∏ i, (a i : ℚ)) ≠ 0 := by push_cast at hA'; exact hA'
    field_simp
  obtain ⟨m, hm⟩ := exists_int_sq_of_isSquare_div hB hsqQ
  refine ⟨hsqQ, ?_, ?_, ?_⟩
  · have hR : (diag fun i => (a i : ℚ)).IsometricIn ℝ (diag fun i => (b i : ℚ)) := hev RatPlace.infinite
    have := negCount_eq_of_isometric _ _ hR
    rw [signature_eq_sub a ha, signature_eq_sub b hb, this]
  · exact (oddity_eq_iff_hasse a b ha hb ⟨m, hm⟩).mpr
      (RatPlace.hasseSerre_isometric _ _ _ ha' hb' (hev (RatPlace.finite ⟨2, Nat.prime_two⟩)))
  · intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    exact (pExcess_eq_iff_hasse p hp2 a b ha hb ⟨m, hm⟩).mpr
      (RatPlace.hasseSerre_isometric _ _ _ ha' hb' (hev (RatPlace.finite ⟨p, hp⟩)))

/-- **Theorem 3, "if"**: the converse, by Hasse–Minkowski (`isometric_iff_everywhere`) and the classification over
$\mathbb{R}$ and $\mathbb{Q}_p$ (`isometric_padic_iff_invariants`). -/
theorem equiv_of_theorem3 (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hsq : IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ))) (hsig : signature a = signature b)
    (hodd : oddity a = oddity b) (hex : ∀ p : ℕ, p.Prime → p ≠ 2 → pExcess p a = pExcess p b) :
    RatEquivalent a b := by
  have ha' : ∀ i, (fun i => (a i : ℚ)) i ≠ 0 := fun i => by simpa using ha i
  have hb' : ∀ i, (fun i => (b i : ℚ)) i ≠ 0 := fun i => by simpa using hb i
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  have hB : (∏ i, b i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hb i
  obtain ⟨m, hm⟩ := exists_int_sq_of_isSquare_div hB hsq
  refine (isometric_iff_everywhere (intDiag a) (intDiag b) (nondegenerate_diag ha')
    (nondegenerate_diag hb')).mpr fun v => ?_
  cases v with
  | infinite =>
    have hneg : negCount (fun i => (a i : ℚ)) = negCount (fun i => (b i : ℚ)) := by
      have h1 := signature_eq_sub a ha
      have h2 := signature_eq_sub b hb
      omega
    exact isometricIn_real_of_negCount _ _ ha' hb' hneg
  | finite p =>
    have : Fact p.1.Prime := ⟨p.2⟩
    show (diag fun i => (a i : ℚ)).IsometricIn ℚ_[p.1] (diag fun i => (b i : ℚ))
    rw [isometric_padic_iff_invariants p.1 _ _ ha' hb']
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hs⟩ := hsq
      have hs0 : s ≠ 0 := by
        rintro rfl
        have : ((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ) = 0 := by rw [hs]; simp
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact hA (by exact_mod_cast h)
        · exact hB (by exact_mod_cast h)
      have hB' : ((∏ i, b i : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hB
      have hAB : ((∏ i, a i : ℤ) : ℚ) = s ^ 2 * ((∏ i, b i : ℤ) : ℚ) := by
        field_simp at hs; rw [pow_two]; linarith
      refine ⟨(s : ℚ_[p.1]), by exact_mod_cast hs0, ?_⟩
      simp only [eq_ratCast]
      push_cast at hAB ⊢
      exact_mod_cast hAB
    · rw [← RatPlace.hasseSerre_finite, ← RatPlace.hasseSerre_finite]
      by_cases hp2 : p.1 = 2
      · have := (oddity_eq_iff_hasse a b ha hb ⟨m, hm⟩).mp hodd
        have e : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
        rw [e]; exact this
      · exact (pExcess_eq_iff_hasse p.1 hp2 a b ha hb ⟨m, hm⟩).mp (hex p.1 p.2 hp2)

/-- **Theorem 3 (Conway–Sloane, §5.1, p. 372)**, in the (ii)' form. Two nonsingular diagonal integer forms
$\mathrm{diag}\{a_0,\dots,a_{n-1}\}$, $\mathrm{diag}\{b_0,\dots,b_{n-1}\}$ of the same dimension are equivalent over
$\mathbb{Q}$ if and only if
(i) $\det(a)/\det(b)$ is a rational square, and
(ii)' they have the same signature (an **integer**, the book's $(-1)$-signature, equal as integers), the same oddity
and, for all odd primes $p$, the same $p$-excess modulo $8$.

*Proof route.* NOT Conway–Sloane's (theirs is §6: binary equivalences, Witt cancellation and Theorem 7). Here:
Hasse–Minkowski (`isometric_iff_everywhere`) reduces to $\mathbb{R}$ and each $\mathbb{Q}_p$; the local classification
(`PadicClass.isometric_padic_iff_invariants`) says "same determinant square class and same Hasse invariant"; and
the $p$-excess, oddity and signature determine the Hasse invariant given the determinant (`pExcess_eq_hasse`,
`oddity_eq_hasse`, `signature_eq_hasse`, via `pExcess_eq_iff_hasse`, `oddity_eq_iff_hasse`).

*Normalization (checked).* In (ii) at $p = -1$ the signature must be compared as an integer: comparing it only modulo $8$
is false (e.g. $\langle 1^8\rangle$ and $\langle (-1)^8\rangle$ have all excesses $\equiv 0 \bmod 8$ and the same
determinant, but are inequivalent over $\mathbb{R}$). The book's own use (p. 377, "since signature$(f)$ = signature$(g)$,
the numbers of positive and negative terms agree") is the integral reading. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, Thm. 3, p. 372"]
theorem theorem3 (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    RatEquivalent a b ↔
      IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ)) ∧ signature a = signature b ∧
        oddity a = oddity b ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → pExcess p a = pExcess p b :=
  ⟨theorem3_of_equiv a b ha hb, fun ⟨h1, h2, h3, h4⟩ => equiv_of_theorem3 a b ha hb h1 h2 h3 h4⟩

/-- **Theorem 3 in its (ii) form**: (i) and, for every place $p$ of the book (`excess`: the $(-1)$-excess, the $2$-excess
$n - \mathrm{oddity}$ and the $p$-excesses), equal excesses, together with the integral signature (see the normalization
note of `theorem3`). Equivalent to (ii)' since the dimensions agree. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, Thm. 3, (ii), p. 372"]
theorem theorem3_excess (a b : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    RatEquivalent a b ↔
      IsSquare (((∏ i, a i : ℤ) : ℚ) / ((∏ i, b i : ℤ) : ℚ)) ∧ signature a = signature b ∧
        ∀ v : RatPlace, excess v a = excess v b := by
  rw [theorem3 a b ha hb]
  refine and_congr_right fun _ => ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun v => ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_, ?_⟩⟩
  · cases v with
    | infinite => simp [excess, negOneExcess, h1]
    | finite p =>
      by_cases hp2 : p.1 = 2
      · simp [excess, twoExcess, hp2, h2]
      · simp [excess, hp2, h3 p.1 p.2 hp2]
  · have := h2 (RatPlace.finite ⟨2, Nat.prime_two⟩)
    simpa [excess, twoExcess] using this
  · intro p hp hp2
    have := h2 (RatPlace.finite ⟨p, hp⟩)
    simpa [excess, hp2] using this

/-- **Theorem 4 (the weak Hasse principle)** (p. 372): two nondegenerate rational forms are equivalent over $\mathbb{Q}$ iff
they are equivalent over $\mathbb{R}$ and over every $\mathbb{Q}_p$. This is `isometric_iff_everywhere` (Serre IV §3.3,
Thm. 9), restated; the book defers the proof to the literature. -/
@[kb "conwaysloane1999" "Ch. 15, §5.1, Thm. 4, p. 372"]
theorem theorem4 (Q R : RatQF n) (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.IsometricIn ℚ R ↔ RatPlace.Everywhere fun K _ _ => Q.IsometricIn K R :=
  isometric_iff_everywhere Q R hQ hR

/-! ### Theorem 7: forms with trivial invariants -/

/-- **Trivial invariants** (p. 376): all the $p$-excesses ($p = -1$, $p = 2$ and the odd primes; `excess`) are
$\equiv 0 \pmod 8$ and the determinant is a perfect square. -/
@[kb "conwaysloane1999" "Ch. 15, §6.2, p. 376"]
def TrivialInvariants (a : Fin n → ℤ) : Prop :=
  (∀ v : RatPlace, excess v a = 0) ∧ IsSquare ((∏ i, a i : ℤ) : ℚ)

theorem oddityEntry_one : oddityEntry 1 = 1 := by
  simp [oddityEntry, unitPart]

theorem oddityEntry_neg_one : oddityEntry (-1) = -1 := by
  have h : padicValInt 2 (-1) = 0 := padicValInt.eq_zero_of_not_dvd (by norm_num)
  simp [oddityEntry, unitPart, h]

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    Int.sign (∏ i ∈ s, f i) = ∏ i ∈ s, Int.sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [prod_insert hk, prod_insert hk, Int.sign_mul, ih]

theorem sign_sign_of_ne {x : ℤ} (hx : x ≠ 0) : Int.sign (Int.sign x) = Int.sign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]

/-- **Theorem 7** (p. 376). A nonsingular diagonal integer form with trivial invariants is equivalent over $\mathbb{Q}$ to
$\mathrm{diag}\{\pm 1, \dots, \pm 1\}$ (namely, to the form of its sign pattern $\langle \mathrm{sign}(a_0), \dots\rangle$).

*Proof route: not Conway–Sloane's* (theirs, §6.3, pp. 377–378, reduces the largest prime of a square-free entries by the
replacement lemma, Theorem 8, adjoining $\pm 1$'s). Here it is a corollary of `theorem3`: the form $s_i = \mathrm{sign}(a_i)$
has the same signature as $a$; its oddity is that signature mod $8$ and its odd $p$-excesses vanish, which are also the
values for $a$ (the $2$-excess and $(-1)$-excess vanishing give $\mathrm{oddity}(a) \equiv n \equiv \mathrm{signature}(a)$); and
$\det s = \mathrm{sign}(\det a) = 1$ as $\det a$ is a positive square. The version of the book (with $N$ extra
summands $\mathrm{diag}\{1^N, (-1)^N\}$ adjoined) follows by adding the same summands to both sides.
*Note.* The hypothesis "square-free entries" of the book's proof is not needed. -/
@[kb "conwaysloane1999" "Ch. 15, §6.2, Thm. 7, p. 376"]
theorem theorem7 (a : Fin n → ℤ) (ha : ∀ i, a i ≠ 0) (h : TrivialInvariants a) :
    ∃ s : Fin n → ℤ, (∀ i, s i = 1 ∨ s i = -1) ∧ RatEquivalent a s := by
  obtain ⟨hex, hsq⟩ := h
  set s : Fin n → ℤ := fun i => Int.sign (a i) with hs
  have hspm : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    rcases lt_or_gt_of_ne (ha i) with h | h
    · right; simp [hs, Int.sign_eq_neg_one_of_neg h]
    · left; simp [hs, Int.sign_eq_one_of_pos h]
  have hs0 : ∀ i, s i ≠ 0 := fun i => by rcases hspm i with h | h <;> simp [h]
  refine ⟨s, hspm, ?_⟩
  have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
  -- the determinant of `s` is `1`
  have hDa : 0 < ∏ i, a i := by
    obtain ⟨r, hr⟩ := Rat.isSquare_intCast_iff.mp hsq
    rw [hr]
    exact mul_self_pos.mpr fun h0 => hA (by rw [hr, h0]; simp)
  have hDs : (∏ i, s i) = 1 := by
    have : Int.sign (∏ i, a i) = ∏ i, Int.sign (a i) := sign_prod _ _
    rw [← this]; exact Int.sign_eq_one_of_pos hDa
  have hsig : signature a = signature s := by
    unfold signature
    exact Finset.sum_congr rfl fun i _ => (sign_sign_of_ne (ha i)).symm
  have hex2 := hex (RatPlace.finite ⟨2, Nat.prime_two⟩)
  have hex1 := hex RatPlace.infinite
  simp only [excess, ite_true, twoExcess, negOneExcess] at hex2 hex1
  have hoddA : oddity a = (signature a : ZMod 8) := by
    linear_combination (-1 : ZMod 8) * hex2 - hex1
  have hoddS : oddity s = (signature s : ZMod 8) := by
    have : ∀ i, oddityEntry (s i) = ((s i : ℤ) : ZMod 8) := fun i => by
      rcases hspm i with h | h <;> simp [h, oddityEntry_one, oddityEntry_neg_one]
    unfold oddity signature
    rw [Finset.sum_congr rfl fun i _ => this i]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hspm i with h | h
    · rw [h]; simp [Int.sign_one]
    · rw [h]; simp
  refine equiv_of_theorem3 a s ha hs0 ?_ hsig (by rw [hoddA, hoddS, hsig]) ?_
  · rw [hDs]; simpa using hsq
  · intro p hp hp2
    have h1 := hex (RatPlace.finite ⟨p, hp⟩)
    simp only [excess, hp2, ite_false] at h1
    rw [h1]
    unfold pExcess
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    apply pExcessEntry_of_not_dvd
    have key : ¬ (p : ℤ) ∣ 1 := fun hd => by
      have := Int.eq_one_of_dvd_one (by positivity) hd
      have := hp.one_lt
      omega
    rcases hspm i with h | h <;> rw [h]
    · exact key
    · rwa [dvd_neg]

/-! ### Binary 2-adic forms and Table 15.3 (the $p = 2$ part) -/

theorem padicValInt_two_pow (e : ℕ) : padicValInt 2 ((2 : ℤ) ^ e) = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp [padicValInt, Int.natAbs_pow]

/-- **The oddity of a rank-one form $\langle 2^e u\rangle$, $u$ odd:** $u + 4[e \text{ odd and } u \equiv \pm 3 \bmod 8]$. -/
theorem oddityEntry_two_pow_mul (e : ℕ) (u : ℤ) (hu : ¬ (2 : ℤ) ∣ u) :
    oddityEntry (2 ^ e * u) =
      (u : ZMod 8) + if Odd e ∧ ((u : ZMod 8) = 3 ∨ (u : ZMod 8) = 5) then 4 else 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := fun h => hu (h ▸ dvd_zero _)
  have h2 : (2 : ℤ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
  have hv : padicValInt 2 (2 ^ e * u) = e := by
    rw [padicValInt.mul h2 hu0, padicValInt_two_pow, padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hu)]
    simp
  have hw : unitPart 2 (2 ^ e * u) = u := by
    unfold unitPart
    rw [hv]
    simp [h2]
  unfold oddityEntry
  rw [hv, hw]

/-- **The mechanism behind Table 15.3 ($p = 2$)** (§6.1, pp. 373–375). For nonzero integers $a, b, r$, the binary form
$\langle a, b\rangle$ represents $r$ over $\mathbb{Q}_2$ if and only if
$$\mathrm{oddity}\langle a, b\rangle = \mathrm{oddity}\langle ab\rangle + \mathrm{oddity}\langle r\rangle +
\mathrm{oddity}\langle -ab\rangle - \mathrm{oddity}\langle -rab\rangle \pmod 8$$
(rank-one oddities). *Proof.* Serre's criterion (`represents_padic_two_iff`): $\langle a,b\rangle$ represents $r$ iff
$(r, -ab)_2 = (a,b)_2$; and by `oddityEntry_mul`, $\mathrm{oddity}\langle a\rangle + \mathrm{oddity}\langle b\rangle \equiv
\mathrm{oddity}\langle ab\rangle + 1 + [\![(a,b)_2]\!]$, $\mathrm{oddity}\langle r\rangle + \mathrm{oddity}\langle -ab\rangle \equiv
\mathrm{oddity}\langle -rab\rangle + 1 + [\![(r,-ab)_2]\!]$. -/
@[kb "conwaysloane1999" "Ch. 15, §6.1, Table 15.3, p. 374 (p = 2)"]
theorem represents_two_adic_iff_oddity {a b r : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    (diag ![(a : ℚ), b]).RepresentsIn ℚ_[2] (r : ℚ) ↔
      oddity ![a, b] = oddityEntry (a * b) + oddityEntry r + oddityEntry (-(a * b)) -
        oddityEntry (-(r * (a * b))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hcast : ∀ i, (![(a : ℚ), b] : Fin 2 → ℚ) i ≠ 0 := fun i => by
    fin_cases i <;> simp [ha, hb]
  have hrep := represents_padic_two_iff 2 ![(a : ℚ), b] hcast (r : ℚ) (by exact_mod_cast hr)
  rw [hrep]
  have e1 : hilbertSymbol ℚ_[2] (algebraMap ℚ ℚ_[2] (r : ℚ)) (algebraMap ℚ ℚ_[2] (-∏ i, (![(a : ℚ), b] : Fin 2 → ℚ) i)) =
      (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert (r : ℚ) ((-(a * b) : ℤ) : ℚ) := by
    simp [RatPlace.hilbert, Fin.prod_univ_two]
  have e2 : hasseInvariant ℚ_[2] ![(a : ℚ), b] = (RatPlace.finite ⟨2, Nat.prime_two⟩).hilbert (a : ℚ) (b : ℚ) := by
    simp [hasseInvariant, Fin.prod_univ_two, RatPlace.hilbert]
  rw [e1, e2]
  have m1 := oddityEntry_mul ha hb
  have m2 := oddityEntry_mul hr (neg_ne_zero.mpr hab)
  have hodd : oddity ![a, b] = oddityEntry a + oddityEntry b := by
    simp [oddity, Fin.sum_univ_two]
  have hY := RatPlace.hilbert_pm (RatPlace.finite ⟨2, Nat.prime_two⟩) (r : ℚ) ((-(a * b) : ℤ) : ℚ)
  have hX := RatPlace.hilbert_pm (RatPlace.finite ⟨2, Nat.prime_two⟩) (a : ℚ) (b : ℚ)
  have e3 : r * -(a * b) = -(r * (a * b)) := by ring
  rw [e3] at m2
  rw [← sgn4_inj hY hX, hodd]
  constructor
  · intro h
    linear_combination m1 - m2 - h
  · intro h
    linear_combination m1 - m2 - h

/-- **Table 15.3, $p = 2$: the square classes of $\mathbb{Q}_2^\times$ represented by the first-row forms.** A square class of
$\mathbb{Q}_2^\times$ is $2^{e} u$ with $e \in \{0, 1\}$ and $u \in \{1,3,5,7\}$ (the book's $u_1, u_3, u_5, u_7$,
$2u_1, \dots, 2u_7$), recorded as the pair `(e, u)`. For the determinant class `(e', u')`, `tableRow e' u'` is the list of
classes in the first row of the book's table for that determinant (p. 374; for $u_7$ the single row "all"). -/
def tableRow (e' : ℕ) (u' : ℤ) : List (ℕ × ℤ) :=
  match e', u' with
  | 0, 1 => [(0, 1), (0, 5), (1, 1), (1, 5)]
  | 0, 3 => [(0, 1), (0, 3), (0, 5), (0, 7)]
  | 0, 5 => [(0, 1), (0, 5), (1, 3), (1, 7)]
  | 0, 7 => [(0, 1), (0, 3), (0, 5), (0, 7), (1, 1), (1, 3), (1, 5), (1, 7)]
  | 1, 1 => [(0, 1), (0, 3), (1, 1), (1, 3)]
  | 1, 3 => [(0, 1), (0, 7), (1, 3), (1, 5)]
  | 1, 5 => [(0, 1), (0, 3), (1, 5), (1, 7)]
  | 1, 7 => [(0, 1), (0, 7), (1, 1), (1, 7)]
  | _, _ => []

/-- The oddity attached to the first row of the table for the determinant class `(e', u')` (p. 374). -/
def tableOdd1 (e' : ℕ) (u' : ℤ) : ZMod 8 :=
  match e', u' with
  | 0, 1 => 2
  | 0, 3 => 4
  | 0, 5 => 6
  | 0, 7 => 0
  | 1, 1 => 2
  | 1, 3 => 0
  | 1, 5 => 2
  | 1, 7 => 0
  | _, _ => 0

/-- The oddity attached to the second row of the table for the determinant class `(e', u')` (p. 374; for $u_7$ there is
no second row and the value is irrelevant, set to the same $0$). -/
def tableOdd2 (e' : ℕ) (u' : ℤ) : ZMod 8 :=
  match e', u' with
  | 0, 1 => 6
  | 0, 3 => 0
  | 0, 5 => 2
  | 0, 7 => 0
  | 1, 1 => 6
  | 1, 3 => 4
  | 1, 5 => 6
  | 1, 7 => 4
  | _, _ => 0

/-- **The oddity that the table assigns to a binary 2-adic form of determinant class `(e', u')` representing the class
`(e, u)`**: the first-row oddity if `(e, u)` lies in the first row, the second-row oddity otherwise. -/
def tableValue (e' : ℕ) (u' : ℤ) (e : ℕ) (u : ℤ) : ZMod 8 :=
  if (e, u) ∈ tableRow e' u' then tableOdd1 e' u' else tableOdd2 e' u'

/-- Rank-one oddity formula of `oddityEntry_two_pow_mul`, as a function. -/
def oddT (k : ℕ) (w : ℤ) : ZMod 8 := (w : ZMod 8) + if Odd k ∧ ((w : ZMod 8) = 3 ∨ (w : ZMod 8) = 5) then 4 else 0

/-- **Table 15.3 ($p=2$), the finite check**: for all 64 pairs of classes the table value is
$\mathrm{oddity}\langle d\rangle + \mathrm{oddity}\langle r\rangle + \mathrm{oddity}\langle -d\rangle -
\mathrm{oddity}\langle -rd\rangle$ with $d = 2^{e'}u'$, $r = 2^e u$. -/
theorem table_check : ∀ e' ∈ ({0, 1} : Finset ℕ), ∀ e ∈ ({0, 1} : Finset ℕ), ∀ u' ∈ ({1, 3, 5, 7} : Finset ℤ),
    ∀ u ∈ ({1, 3, 5, 7} : Finset ℤ),
    tableValue e' u' e u = oddT e' u' + oddT e u + oddT e' (-u') - oddT (e + e') (-(u * u')) := by
  decide

end QuadFormsKB.ConwaySloane.Rational
