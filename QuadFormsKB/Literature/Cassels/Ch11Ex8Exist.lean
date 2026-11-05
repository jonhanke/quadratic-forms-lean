/-
# Cassels, Chapter 11, Example 8: the positive halves, via the classes of the genus of $x^2 - 2y^2 + 64z^2$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Example 8 (p. 253), for
$f = x_0^2 - 2x_1^2 + 64x_2^2$ (`Siegel.ex23Form`) and $g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2$ (`ex8G`).

**Proved (unconditionally).**
* `ex8_classify`: every integral form in the genus of $f$ is integrally equivalent to $f$ or to $g$.
* `ex8Existence_holds : Ex8Existence` (the named statement of `Ch11Ex8.lean`): $m^2$ is primitively represented by $f$
  if $m \equiv \pm 1 \pmod 8$ and by $g$ if $m \equiv \pm 3 \pmod 8$; hence `ex8_primRep_iff'`, the full answer of the
  example, unconditionally.

**Route.** Not the spinor genus theory suggested by the book (the dyadic spinor norm groups of this lattice are not in
the library), but an elementary reduction of *isotropic* ternary forms and a finite check:
* A form $Q'$ in the genus of $f$ is rationally equivalent to $f$ (`Lattices.isometricGL_rat_of_sameGenus`), and
  $f(8, 8, 1) = 0$, so $Q'$ has a primitive integral zero $\vec e$ (`exists_primitive_isotropic`).
* Completing $\vec e$ to a basis (`Reduction.extendsBasis_iff_gcd`), then a Bézout change of the other two basis
  vectors (`intEquiv_bezout`) and a translation by multiples of $\vec e$ (`intEquiv_shift`), $Q'$ becomes the form of a
  sextuple $(0, \beta, \delta, 0, k, \gamma)$, i.e. $\beta x_1^2 + \delta x_2^2 + k x_0x_2 + \gamma x_1x_2$, with
  $k > 0$, $0 \le \gamma, \delta < k$ (`exists_isotropic_reduced`); the determinant $-2\beta k^2 = -1024$ forces
  $k \in \{1, 2, 4, 8, 16\}$, $\beta = 512/k^2$: $341$ sextuples.
* A kernel check (`ex8_chk`) gives for each of them an equivalence certificate to $f$ or $g$ ($4 + 4$), or a residue
  modulo $2$, $4$ or $8$ represented by exactly one of $f$ and the sextuple's form ($333$; not in the genus).
* Existence: by Chapter 9, Theorem 5.1 (`exists_sameGenus_primRep`; the only local condition is at $p = 2$, where
  $(m, 0, 0)$ works for odd $m$) some form of the genus represents $m^2$ primitively; it is equivalent to $f$ or $g$,
  and the negative halves `ex8_f_not_primRep`, `ex8_g_not_primRep` decide which.
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex8
import QuadFormsKB.Literature.Cassels.Ch11Ex8ExistData
import QuadFormsKB.Literature.Cassels.Ch1Examples

open Matrix QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Cassels.Ch11Ex4

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Ch11Ex8

/-! ### Changes of basis of ternary forms -/

/-- **The form in a new basis:** for $T \in \mathrm{GL}_3(\mathbb Z)$ with columns $\vec t_0, \vec t_1, \vec t_2$, $Q$ is
equivalent to `tf` with coefficients $Q(\vec t_0), Q(\vec t_1), Q(\vec t_2)$ and $B(\vec t_i, \vec t_j)$ ($i < j$), the
entries of $T^{\mathsf T}H_QT$. -/
theorem intEquiv_tf_of_GL (Q : QuadForm ℤ 3) (T : GL (Fin 3) ℤ) :
    IntEquiv Q (tf (Q.eval (fun k => T.val k 0)) (Q.eval (fun k => T.val k 1)) (Q.eval (fun k => T.val k 2))
      ((T.valᵀ * Q.hessian * T.val) 0 1) ((T.valᵀ * Q.hessian * T.val) 0 2) ((T.valᵀ * Q.hessian * T.val) 1 2)) := by
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A = T.valᵀ * Q.hessian * T.val := ⟨_, rfl⟩
  have hdiag : ∀ i, A i i = 2 * Q.eval (fun k => T.val k i) := by
    intro i
    rw [hAdef, Hermite.conj_apply, LocalDensity.two_mul_eval_eq_hessian]
  have hsym : ∀ i j, A j i = A i j := by
    intro i j
    have hs : Aᵀ = A := by
      rw [hAdef]
      simp [Matrix.transpose_mul, (LocalDensity.hessian_isSymm Q).eq, Matrix.mul_assoc]
    simpa [Matrix.transpose_apply] using congrFun (congrFun hs i) j
  rw [← hAdef]
  refine ⟨T, (eval_mulVec_eq_iff_hessian Q _ T.val).mpr ?_⟩
  rw [← hAdef, hessian_tf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, hsym 0 1, hsym 0 2, hsym 1 2]

/-- **The Bézout step:** for $x_0^2$-coefficient $0$, $h = dh'$, $g = dg'$ and $xh' + yg' = 1$, the new basis
$\vec e_0$, $\vec w = g'\vec e_1 - h'\vec e_2$, $\vec v = x\vec e_1 + y\vec e_2$ (determinant $1$) has $B(\vec e_0, \vec w) = 0$
and $B(\vec e_0, \vec v) = d$. -/
theorem intEquiv_bezout (b c h g f d h' g' x y : ℤ) (hh : h = d * h') (hg : g = d * g') (hxy : x * h' + y * g' = 1) :
    IntEquiv (tf 0 b c h g f) (tf 0 (b * g' ^ 2 - f * g' * h' + c * h' ^ 2) (b * x ^ 2 + f * x * y + c * y ^ 2) 0 d
      (2 * b * g' * x + f * (g' * y - h' * x) - 2 * c * h' * y)) := by
  subst hh hg
  refine ⟨⟨!![1, 0, 0; 0, g', x; 0, -h', y], !![1, 0, 0; 0, y, -x; 0, h', g'], ?_, ?_⟩,
    (eval_mulVec_eq_iff_hessian _ _ _).mpr ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination hxy
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination hxy
  · rw [hessian_tf, hessian_tf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination d * hxy

/-- **The translation step:** $\vec w \mapsto \vec w + u\vec e_0$, $\vec v \mapsto \vec v + s\vec e_0$ changes
$(\delta, \gamma)$ to $(\delta + sd, \gamma + ud)$ when $Q(\vec e_0) = 0$, $B(\vec e_0, \vec w) = 0$, $B(\vec e_0, \vec v) = d$. -/
theorem intEquiv_shift (β δ d γ u s : ℤ) :
    IntEquiv (tf 0 β δ 0 d γ) (tf 0 β (δ + s * d) 0 d (γ + u * d)) := by
  refine ⟨⟨!![1, u, s; 0, 1, 0; 0, 0, 1], !![1, -u, -s; 0, 1, 0; 0, 0, 1], ?_, ?_⟩,
    (eval_mulVec_eq_iff_hessian _ _ _).mpr ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  · rw [hessian_tf, hessian_tf]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring1

/-- **Reduction of a form with a primitive zero:** if $Q(\vec e) = 0$ with $\gcd(\vec e) = 1$ and $\det H_Q \ne 0$,
then $Q$ is equivalent to the form of a sextuple $(0, \beta, \delta, 0, k, \gamma)$ with $k > 0$ and
$0 \le \gamma, \delta < k$. -/
theorem exists_isotropic_reduced (Q : QuadForm ℤ 3) (hdet : Q.hessian.det ≠ 0) {e : Fin 3 → ℤ}
    (he : Reduction.tailGcd 0 e = 1) (hQe : Q.eval e = 0) :
    ∃ β δ k γ : ℤ, IntEquiv Q (tf 0 β δ 0 k γ) ∧ 0 < k ∧ 0 ≤ γ ∧ γ < k ∧ 0 ≤ δ ∧ δ < k := by
  obtain ⟨T, -, hT⟩ := (Reduction.extendsBasis_iff_gcd 0 e).2 he
  have hcol : (fun k => T.val k 0) = e := funext hT
  have h1 := intEquiv_tf_of_GL Q T
  rw [hcol, hQe] at h1
  generalize Q.eval (fun k => T.val k 1) = b at h1
  generalize Q.eval (fun k => T.val k 2) = c at h1
  generalize (T.valᵀ * Q.hessian * T.val) 0 1 = h at h1
  generalize (T.valᵀ * Q.hessian * T.val) 0 2 = g at h1
  generalize (T.valᵀ * Q.hessian * T.val) 1 2 = f at h1
  have hd1 : (tf 0 b c h g f).hessian.det ≠ 0 := by
    rw [← SameGenus.hessian_det_eq h1.sameGenus]; exact hdet
  have hhg : h ≠ 0 ∨ g ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hd1
    rw [det_hessian_tf, hc.1, hc.2]; unfold tupDet; ring
  set d : ℤ := (Int.gcd h g : ℤ) with hd
  have hdpos : 0 < d := by
    rw [hd]; exact_mod_cast Int.gcd_pos_iff.mpr hhg
  have hh : h = d * (h / d) := (Int.mul_ediv_cancel' (Int.gcd_dvd_left h g)).symm
  have hg : g = d * (g / d) := (Int.mul_ediv_cancel' (Int.gcd_dvd_right h g)).symm
  have hxy : Int.gcdA h g * (h / d) + Int.gcdB h g * (g / d) = 1 := by
    have hb : d = h * Int.gcdA h g + g * Int.gcdB h g := Int.gcd_eq_gcd_ab h g
    have : d * (Int.gcdA h g * (h / d) + Int.gcdB h g * (g / d)) = d * 1 := by
      linear_combination -hb - Int.gcdA h g * hh - Int.gcdB h g * hg
    exact mul_left_cancel₀ hdpos.ne' this
  have h2 := h1.trans (intEquiv_bezout b c h g f d (h / d) (g / d) _ _ hh hg hxy)
  generalize b * (g / d) ^ 2 - f * (g / d) * (h / d) + c * (h / d) ^ 2 = β at h2
  generalize b * Int.gcdA h g ^ 2 + f * Int.gcdA h g * Int.gcdB h g + c * Int.gcdB h g ^ 2 = δ at h2
  generalize 2 * b * (g / d) * Int.gcdA h g + f * ((g / d) * Int.gcdB h g - (h / d) * Int.gcdA h g) -
    2 * c * (h / d) * Int.gcdB h g = γ at h2
  have h3 := h2.trans (intEquiv_shift β δ d γ (-(γ / d)) (-(δ / d)))
  refine ⟨β, δ + -(δ / d) * d, d, γ + -(γ / d) * d, h3, hdpos, ?_, ?_, ?_, ?_⟩
  · have := Int.emod_nonneg γ hdpos.ne'; rw [Int.emod_def] at this; linarith
  · have := Int.emod_lt_of_pos γ hdpos; rw [Int.emod_def] at this; linarith
  · have := Int.emod_nonneg δ hdpos.ne'; rw [Int.emod_def] at this; linarith
  · have := Int.emod_lt_of_pos δ hdpos; rw [Int.emod_def] at this; linarith

/-! ### A primitive zero of every form of the genus -/

/-- Helper: values of the rational form of an integral form. -/
theorem eval_map_rat (Q : QuadForm ℤ 3) (x : Fin 3 → ℚ) :
    (Q.map (Int.castRingHom ℚ)).eval x = Q.evalIn ℚ x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- **Every form in the genus of $f$ has a primitive integral zero:** it is rationally equivalent to $f$, and
$f(8, 8, 1) = 0$. -/
theorem exists_primitive_isotropic (Q' : QuadForm ℤ 3) (h : SameGenus ex23Form Q') :
    ∃ e : Fin 3 → ℤ, Reduction.tailGcd 0 e = 1 ∧ Q'.eval e = 0 := by
  obtain ⟨S, hS⟩ := Lattices.isometricGL_rat_of_sameGenus ex23Form Q' h.hessian_det_eq
    (by rw [ex8_hessian_det_f]; norm_num) h
  set v : Fin 3 → ℚ := (S⁻¹).val *ᵥ ![8, 8, 1] with hv
  have hSv : S.val *ᵥ v = ![8, 8, 1] := by
    rw [hv, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, mulVec_zero] at hSv
    have := congrFun hSv 2
    simp at this
  have hval : Q'.evalIn ℚ v = 0 := by
    rw [← eval_map_rat, ← hS, hSv, eval_map_ex23Form]
    simp; norm_num
  obtain ⟨w, hw0, hw⟩ := Ch1.exists_int_zero_of_rat_zero Q' hv0 hval
  obtain ⟨y, hy, hyz⟩ := exists_primitive_zero Q' hw0 hw
  refine ⟨y, ?_, hyz⟩
  have hfil : (Finset.univ.filter fun k : Fin 3 => (0 : Fin 3) ≤ k) = Finset.univ := by
    ext k; simp
  unfold Reduction.tailGcd
  rw [hfil]
  have hdvd : ∀ i, Finset.univ.gcd y ∣ y i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hu := hy _ (dvd_zero _) hdvd
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · exact h1
  · have := Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := y))
    omega

/-! ### The classification -/

/-- The sextuple of $f = x_0^2 - 2x_1^2 + 64x_2^2$. -/
def fT : Tup := (1, -2, 64, 0, 0, 0)

/-- The sextuple of $g = 4x_0^2 - 2x_1^2 + 17x_2^2 + 4x_0x_2$. -/
def gT : Tup := (4, -2, 17, 0, 4, 0)

/-- Helper: $f$ is the form of its sextuple. -/
theorem ex23Form_eq_tupForm : ex23Form = tupForm fT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex23Form, tupForm, tf, fT, QuadForm.diag, QuadForm.ofUpper]

/-- Helper: $g$ is the form of its sextuple. -/
theorem ex8G_eq_tupForm : ex8G = tupForm gT := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex8G, tupForm, tf, gT, QuadForm.ofUpper]

/-- **The finite check** (kernel evaluation): for $1 \le k \le 22$ and $0 \le \gamma, \delta < k$ with $\beta k^2 = 512$,
$\beta = 512/k^2$, the verdict on the sextuple $(0, \beta, \delta, 0, k, \gamma)$ holds (an equivalence certificate to
$f$ or $g$, or a separating residue). -/
def ex8chkB : Bool :=
  (intRange 1 22).all fun k => (intRange 0 (k - 1)).all fun γ => (intRange 0 (k - 1)).all fun δ =>
    !(decide (512 / (k * k) * (k * k) = 512)) ||
      verdict fT gT Ex8Data.isoF Ex8Data.isoG Ex8Data.seps (0, 512 / (k * k), δ, 0, k, γ)

/-- The finite check succeeds (kernel evaluation). -/
theorem ex8_chk : ex8chkB = true := by decide +kernel

/-- **Every form in the genus of $f = x_0^2 - 2x_1^2 + 64x_2^2$ is equivalent to $f$ or to
$g = (2x_0 + x_2)^2 - 2x_1^2 + 16x_2^2$** (Cassels, Ch. 11, Example 8). -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (the classes of the genus)"]
theorem ex8_classify (Q' : QuadForm ℤ 3) (h : SameGenus ex23Form Q') : IntEquiv ex23Form Q' ∨ IntEquiv ex8G Q' := by
  have hdet : Q'.hessian.det = -1024 := by rw [← h.hessian_det_eq, ex8_hessian_det_f]
  obtain ⟨e, he, hQe⟩ := exists_primitive_isotropic Q' h
  obtain ⟨β, δ, k, γ, heq, hk, hγ0, hγ1, hδ0, hδ1⟩ :=
    exists_isotropic_reduced Q' (by rw [hdet]; norm_num) he hQe
  have hdt : tupDet 0 β δ 0 k γ = -1024 := by
    rw [← det_hessian_tf, ← hdet]; exact (SameGenus.hessian_det_eq heq.sameGenus).symm
  have hbk : β * (k * k) = 512 := by unfold tupDet at hdt; linarith
  have hk22 : k ≤ 22 := by
    have hβ : 0 < β := by
      by_contra hc
      push Not at hc
      nlinarith [mul_pos hk hk]
    nlinarith
  have hβe : 512 / (k * k) = β := by rw [← hbk]; exact Int.mul_ediv_cancel β (by positivity)
  have hv : verdict fT gT Ex8Data.isoF Ex8Data.isoG Ex8Data.seps (0, β, δ, 0, k, γ) = true := by
    have := ex8_chk
    simp only [ex8chkB, List.all_eq_true] at this
    have h' := this k (mem_intRange (by omega) hk22) γ (mem_intRange hγ0 (by omega))
      δ (mem_intRange hδ0 (by omega))
    rw [hβe] at h'
    simpa [hbk] using h'
  have hsg : SameGenus (tupForm fT) (tupForm (0, β, δ, 0, k, γ)) := by
    rw [← ex23Form_eq_tupForm]; exact h.trans heq.sameGenus
  rcases verdict_sound hv hsg with e1 | e1
  · rw [← ex23Form_eq_tupForm] at e1
    exact Or.inl (IsometricGL.trans e1 (IsometricGL.symm heq))
  · rw [← ex8G_eq_tupForm] at e1
    exact Or.inr (IsometricGL.trans e1 (IsometricGL.symm heq))

/-! ### The positive halves -/

/-- Helper: a primitive representation of an odd square $m^2$ by $f$ or by $g$ (Chapter 9, Theorem 5.1 gives one by a
form of the genus; `ex8_classify` and `primRep_of_intEquiv` transport it). -/
theorem ex8_primRep_f_or_g (m : ℤ) (hm2 : m % 2 = 1) :
    (primRepSet ex23Form (m ^ 2)).Nonempty ∨ (primRepSet ex8G (m ^ 2)).Nonempty := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm2
  have hloc : ∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ (p : ℤ) ∣ ex23Form.hessian.det ∨ (3 = 2 ∧ (p : ℤ) ∣ m ^ 2)) →
      ∃ x : Fin 3 → ℤ_[p], (∃ i, IsUnit (x i)) ∧ (ex23Form.map (Int.castRingHom ℤ_[p])).eval x = ((m ^ 2 : ℤ) : ℤ_[p]) := by
    intro p _ hc
    have hp2 : p = 2 := by
      rcases hc with h | h | ⟨h, -⟩
      · exact h
      · rw [ex8_hessian_det_f] at h
        have h' : (p : ℤ) ∣ 2 ^ 10 := by
          have : (p : ℤ) ∣ -1024 := h
          rw [show (2 : ℤ) ^ 10 = -(-1024) by norm_num]; exact this.neg_right
        have : p ∣ 2 ^ 10 := by exact_mod_cast h'
        exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((Fact.out : p.Prime).dvd_of_dvd_pow this)
      · omega
    subst hp2
    refine ⟨![(m : ℤ_[2]), 0, 0], ⟨0, ?_⟩, ?_⟩
    · simpa using (isUnit_intCast_padic (p := 2) m).mpr (by omega)
    · rw [eval_map_ex23Form]; simp
  obtain ⟨f', hg, x, hx, hfx⟩ := exists_sameGenus_primRep ex23Form (by norm_num)
    (by rw [ex8_hessian_det_f]; norm_num) (a := m ^ 2) (pow_ne_zero 2 hm0)
    ⟨![(m : ℝ), 0, 0], by
      rw [show ex23Form.evalIn ℝ ![(m : ℝ), 0, 0] = (ex23Form.map (Int.castRingHom ℝ)).eval ![(m : ℝ), 0, 0] by
        simp [QuadForm.map, QuadForm.evalIn], eval_map_ex23Form]
      simp⟩ hloc
  rcases ex8_classify f' hg with he | he
  · obtain ⟨y, hy, hye⟩ := primRep_of_intEquiv he ⟨x, hx, hfx⟩
    exact Or.inl ⟨y, hy, hye⟩
  · obtain ⟨y, hy, hye⟩ := primRep_of_intEquiv he ⟨x, hx, hfx⟩
    exact Or.inr ⟨y, hy, hye⟩

/-- **Cassels, Ch. 11, Example 8** (p. 253), the positive halves, proved: $m^2$ is primitively represented by
$f = x^2 - 2y^2 + 64z^2$ if $m \equiv \pm 1 \pmod 8$, and by $g = (2x + z)^2 - 2y^2 + 16z^2$ if $m \equiv \pm 3
\pmod 8$. *Proof:* one of $f, g$ represents $m^2$ primitively (`ex8_primRep_f_or_g`), and the other one cannot
(`ex8_g_not_primRep`, `ex8_f_not_primRep`). -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (positive halves, proof)"]
theorem ex8Existence_holds : Ex8Existence where
  f_rep m hm := by
    rcases ex8_primRep_f_or_g m (by omega) with h | h
    · exact h
    · rw [ex8_g_not_primRep hm] at h; exact absurd h Set.not_nonempty_empty
  g_rep m hm := by
    rcases ex8_primRep_f_or_g m (by omega) with h | h
    · rw [ex8_f_not_primRep hm] at h; exact absurd h Set.not_nonempty_empty
    · exact h

/-- **Cassels, Ch. 11, Example 8** (p. 253), the full answer, unconditional: for odd $m$, $m^2$ is primitively
represented by $f$ iff $m \equiv \pm 1 \pmod 8$ and by $g$ iff $m \equiv \pm 3 \pmod 8$ (`ex8_primRep_iff` with
`ex8Existence_holds`). -/
@[kb "cassels1978" "Ch. 11, Ex. 8, p. 253 (answer, unconditional)"]
theorem ex8_primRep_iff' (m : ℤ) (hodd : m % 2 = 1) :
    ((primRepSet ex23Form (m ^ 2)).Nonempty ↔ (m % 8 = 1 ∨ m % 8 = 7)) ∧
      ((primRepSet ex8G (m ^ 2)).Nonempty ↔ (m % 8 = 3 ∨ m % 8 = 5)) :=
  ex8_primRep_iff ex8Existence_holds m hodd

end QuadFormsKB.Cassels.Ch11Ex8
