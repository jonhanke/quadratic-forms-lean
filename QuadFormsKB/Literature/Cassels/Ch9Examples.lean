/-
# Cassels, Chapter 9: examples (exercises) and the example of §3

**Layer:** integer-valued forms `QuadForm ℤ n`, the genus `Siegel.SameGenus`, $\mathrm{GL}_n(\mathbb Z)$-classes
`IntEquiv`, proper classes `ProperIntEquiv` (`Ch9Sec1.lean`).

**Proves**
* Example 8 (`sameGenus_improper`, `hasImproperAut_of_one_proper_class`): $f(\mathbf x)$ and $f(T\mathbf x)$ with
  $\det T = -1$ are in one genus; a form in a genus with a single proper class has an improper automorph;
* Example 5 for $c = 1, -1, -2, -3$ (`one_class_sumSq_add`): $x^2 + y^2 + cz^2$ is in a genus of one class
  ($c = 2, 3$ are not formalized); the case $c = -3$ is the example of §3, p. 139 (9.r9).

*Proof of Example 5 for $c < 0$ (not Cassels' hint):* Chapter 11, Theorem 1.5 (`isProperIsometric_of_sameGenus_of_det`,
an indefinite form whose determinant has no high prime powers is alone in its genus), transported from lattices to forms
(`intEquiv_of_sameGenus_of_lattice_one_class`).
-/
import QuadFormsKB.Literature.Cassels.Ch9Sec1
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.Cassels.Ch11Thm13
import QuadFormsKB.Siegel.FourSquaresClassNumber

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### Example 8 -/

/-- **Cassels, Ch. 9, Example 8** (p. 163), first part: *let $f(\mathbf x)$ be an integral quadratic form in $n$
variables and let $T$ be an integral $n \times n$ matrix, $\det(T) = -1$. Show that $f(\mathbf x)$ and $f(T\mathbf x)$
are in the same genus.* (They are even $\mathbb Z$-equivalent.) -/
@[kb "cassels1978" "Ch. 9, Ex. 8, p. 163 (first part)"]
theorem sameGenus_improper (f f' : QuadForm ℤ n) (T : GL (Fin n) ℤ) (_hT : T.val.det = -1)
    (hf' : ∀ x, f'.eval x = f.eval (T.val *ᵥ x)) : SameGenus f f' :=
  IntEquiv.sameGenus ⟨T, fun x => (hf' x).symm⟩

/-- **Cassels, Ch. 9, Example 8** (p. 163), second part: *deduce that if $f$ is in a genus consisting of a single
proper equivalence class then $f$ has an integral automorph of determinant $-1$* ($n \ge 1$). -/
@[kb "cassels1978" "Ch. 9, Ex. 8, p. 163 (second part)"]
theorem hasImproperAut_of_one_proper_class (hn : 0 < n) (f : QuadForm ℤ n)
    (h : ∀ f', SameGenus f f' → ProperIntEquiv f f') : HasImproperAut f := by
  by_contra hno
  exact not_properIntEquiv_twist hn hno (h _ (improperIntEquiv_twist hn f).intEquiv.sameGenus)

/-! ### Example 5 -/

/-- The form $x^2 + y^2 + cz^2$ (variables $x_0, x_1, x_2$). -/
def sumSqAdd (c : ℤ) : QuadForm ℤ 3 := QuadForm.diag ![1, 1, c]

/-- The Hessian determinant of $x^2 + y^2 + cz^2$ is $8c$. -/
theorem hessian_det_sumSqAdd (c : ℤ) : (sumSqAdd c).hessian.det = 8 * c := by
  rw [sumSqAdd, hessian_diag, det_diagonal, Fin.prod_univ_three]
  simp
  ring

/-- Evaluation of $x^2 + y^2 + cz^2$ (over $\mathbb Q$) in a $\mathbb Q$-algebra field. -/
theorem evalIn_map_sumSqAdd {K : Type*} [Field K] {_ : Algebra ℚ K} (c : ℤ) (x : Fin 3 → K) :
    ((sumSqAdd c).map (Int.castRingHom ℚ)).evalIn K x = x 0 ^ 2 + x 1 ^ 2 + (c : K) * x 2 ^ 2 := by
  simp [QuadForm.evalIn, Fin.sum_univ_three, sumSqAdd, QuadForm.diag, QuadForm.map, Matrix.diagonal_apply]
  ring

/-- For $c < 0$ the form $x^2 + y^2 + cz^2$ is indefinite (isotropic over $\mathbb R$ at $(\sqrt{-c}, 0, 1)$). -/
theorem isIndefinite_sumSqAdd {c : ℤ} (hc : c < 0) :
    Lattices.IsIndefinite ((sumSqAdd c).map (Int.castRingHom ℚ)) := by
  refine ⟨Rat.infinitePlace, ?_⟩
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  have hc' : (0 : ℝ) ≤ -(c : ℝ) := by
    have : (c : ℝ) < 0 := by exact_mod_cast hc
    linarith
  refine ⟨fun i => ψ.symm (![Real.sqrt (-(c : ℝ)), 0, 1] i), ?_, ?_⟩
  · intro h0
    have := congrFun h0 2
    simp at this
  · rw [evalIn_map_sumSqAdd]
    apply ψ.injective
    simp only [map_add, map_mul, map_pow, map_intCast, map_zero, RingEquiv.apply_symm_apply]
    simp
    rw [Real.sq_sqrt hc']
    ring

/-- **One class in the genus, from Chapter 11, Theorem 1.5** (lattice form `Lattices.isProperIsometric_of_sameGenus_of_det`,
transported to forms): an indefinite integer-valued form in $n \ge 3$ variables satisfying the determinant conditions
of Chapter 11, Theorem 1.5 is $\mathbb Z$-equivalent to every form of its genus. -/
theorem intEquiv_of_sameGenus_of_ch11 {n : ℕ} (hn : 3 ≤ n) (f : QuadForm ℤ n) (hf : f.hessian.det ≠ 0)
    (hind : Lattices.IsIndefinite (f.map (Int.castRingHom ℚ)))
    (hi : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ^ (n * (n - 1) / 2) ∣ f.hessian.det)
    (hii : ¬ IsClassicallyIntegral f ∨ ¬ (2 : ℤ) ^ (Lattices.casselsExpTwo n + n).toNat ∣ f.hessian.det)
    (f' : QuadForm ℤ n) (h : SameGenus f f') : IntEquiv f f' := by
  have hd := h.hessian_det_eq
  have hQ := Lattices.isometricGL_rat_of_sameGenus f f' hd hf h
  obtain ⟨γ, hγ1, hFγ⟩ := Lattices.exists_pos_det_one f f' (by omega) hd hf hQ
  have hgen := Lattices.sameGenus_latOf_of_sameGenus hFγ h
  have e1 : Lattices.latOf (1 : GL (Fin n) ℚ) = (Lattices.stdLat : Lattices.Lat ℚ n).1 := by
    rw [Lattices.latOf, Lattices.glImage_one]; rfl
  rw [e1] at hgen
  obtain ⟨hall, -⟩ := Lattices.isProperIsometric_of_sameGenus_of_det hn f
    (Lattices.nondegenerate_map_of_det_ne_zero f hf) hind hi hii
  obtain ⟨σ, hσ, hσL⟩ := hall ⟨Lattices.latOf γ, Lattices.latOf_isLattice γ⟩ hgen
  have hσ1 : ((σ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det = 1 := hσ
  have hlat : Lattices.latOf γ = Lattices.latOf (σ : GL (Fin n) ℚ) := by
    rw [Lattices.latOf]
    exact hσL.symm
  obtain ⟨U, hUdet, hU⟩ := Lattices.exists_unimod_of_latOf_eq (γ := γ) (δ := (σ : GL (Fin n) ℚ))
    (by rw [hγ1]; exact one_pos) (by rw [hσ1]; exact one_pos) hlat
  have hFσ : Lattices.FormOf f (σ : GL (Fin n) ℚ) f := fun x => by
    have := Lattices.evalIn_mulVec_of_mem (f.map (Int.castRingHom ℚ)) σ.2 x
    rw [Lattices.map_evalIn_rat, Lattices.map_evalIn_rat] at this
    exact this.symm
  have key := Lattices.eval_eq_of_latOf_eq f hFγ hFσ hU
  exact (Siegel.isometricGL_iff_isometricIn _ _).mpr
    ⟨U, by rw [hUdet]; exact isUnit_one, fun x => (key x).symm⟩

/-- **Cassels, Ch. 9, Example 5** (p. 162), for $c = 1, -1, -2, -3$: *show that $x^2 + y^2 + cz^2$ is in a genus of $1$
class.* For $c = -3$ this is also the example of §3 (p. 139): *consider forms $f$ in the genus of
$x^2 + y^2 - 3z^2$ (\*) … it is now easy to establish equivalence with (\*).* -/
@[kb "cassels1978" "Ch. 9, Ex. 5, p. 162 (c = 1, −1, −2, −3); Ch. 9, §3, p. 139 (the genus of x² + y² − 3z²)"]
theorem one_class_sumSqAdd {c : ℤ} (hc : c = 1 ∨ c = -1 ∨ c = -2 ∨ c = -3) (f' : QuadForm ℤ 3)
    (h : SameGenus (sumSqAdd c) f') : IntEquiv (sumSqAdd c) f' := by
  by_cases hc1 : c = 1
  · subst hc1
    have e : sumSqAdd 1 = sumSq 3 := by
      unfold sumSqAdd sumSq
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [e] at h ⊢
    exact sameGenus_sumSq_intEquiv (by norm_num) h
  · have hneg : c < 0 := by omega
    have hlo : -3 ≤ c := by omega
    have hdet := hessian_det_sumSqAdd c
    refine intEquiv_of_sameGenus_of_ch11 le_rfl (sumSqAdd c) (by rw [hdet]; omega)
      (isIndefinite_sumSqAdd hneg) ?_ ?_ f' h
    · intro p hp hp2 hd
      rw [hdet] at hd
      have h3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have h27 : (27 : ℤ) ≤ (p : ℤ) ^ (3 * (3 - 1) / 2) := by
        have : (3 : ℤ) ≤ p := by exact_mod_cast h3
        calc (27 : ℤ) = 3 ^ 3 := by norm_num
          _ ≤ (p : ℤ) ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
          _ = _ := by norm_num
      have := Int.le_of_dvd (by omega) ((dvd_neg).mpr hd)
      omega
    · right
      rw [hdet]
      have e : (Lattices.casselsExpTwo 3 + (3 : ℕ)).toNat = 5 := by
        simp [Lattices.casselsExpTwo]
      rw [e]
      rintro ⟨k, hk⟩
      omega

/-! ### Example 1 -/

/-- **Cassels, Ch. 9, Example 1** (p. 161): *find a form $ax^2 + 2bxy + cy^2$ which is properly integrally equivalent
to $3x^2 + 2xy + 12y^2$ and for which $b \equiv 0 \pmod{81}$.* Answer: $17x^2 + 2 \cdot 81\,xy + 388y^2$, by the
substitution $(x, y) \mapsto (x + 4y, x + 5y)$ of determinant $1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 1, p. 161"]
theorem ex1 : ∃ a b c : ℤ, 81 ∣ b ∧
    ProperIntEquiv (QuadForm.ofUpper ![![3, 2], ![0, 12]]) (QuadForm.ofUpper ![![a, 2 * b], ![0, c]]) := by
  refine ⟨17, 81, 388, dvd_refl _, Binary.glOf 1 4 1 5 (by norm_num), by simp [Matrix.det_fin_two_of], ?_⟩
  intro x
  simp [QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two, dotProduct]
  ring

/-! ### Example 3 -/

/-- $g = 3x^2 + 2xy + 23y^2$ (Example 3). -/
def ex3g : QuadForm ℤ 2 := QuadForm.ofUpper ![![3, 2], ![0, 23]]

/-- $h = 7x^2 + 6xy + 11y^2$ (Example 3). -/
def ex3h : QuadForm ℤ 2 := QuadForm.ofUpper ![![7, 6], ![0, 11]]

theorem eval_ex3h (x : Fin 2 → ℤ) : ex3h.eval x = 7 * x 0 ^ 2 + 6 * x 0 * x 1 + 11 * x 1 ^ 2 := by
  simp [ex3h, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]; ring

/-- **Cassels, Ch. 9, Example 3 (i)** (p. 162), second half: *the forms $g = 3x^2 + 2xy + 23y^2$ and
$h = 7x^2 + 6xy + 11y^2$ are not equivalent* ($g$ represents $3$, $h$ does not: $7h = (7x + 3y)^2 + 68y^2$). -/
@[kb "cassels1978" "Ch. 9, Ex. 3 (i), p. 162 (the forms are not equivalent)"]
theorem ex3_not_intEquiv : ¬ IntEquiv ex3g ex3h := by
  rintro ⟨T, hT⟩
  have h3 : ∀ x, ex3h.eval x ≠ 3 := by
    intro x hx
    rw [eval_ex3h] at hx
    have hy : x 1 = 0 := by nlinarith [sq_nonneg (7 * x 0 + 3 * x 1), sq_nonneg (x 1)]
    rw [hy] at hx
    have : x 0 ^ 2 * 7 = 3 := by linarith
    omega
  apply h3 ((T⁻¹).val *ᵥ ![1, 0])
  rw [← hT, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  simp [ex3g, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]

/-- $z^2 - g(x, y)$ in the variables $(x, y, z) = (x_0, x_1, x_2)$. -/
def ex3G : QuadForm ℤ 3 := QuadForm.ofUpper ![![-3, -2, 0], ![0, -23, 0], ![0, 0, 1]]

/-- $z^2 - h(x, y)$ in the variables $(x, y, z) = (x_0, x_1, x_2)$. -/
def ex3H : QuadForm ℤ 3 := QuadForm.ofUpper ![![-7, -6, 0], ![0, -11, 0], ![0, 0, 1]]

/-- The matrix $S$ with columns $(1, 0, 2)$, $(-4, -5, -22)$, $(-1, -1, -5)$, of determinant $1$. -/
def ex3S : GL (Fin 3) ℤ where
  val := !![1, -4, -1; 0, -5, -1; 2, -22, -5]
  inv := !![3, 2, -1; -2, -3, 1; 10, 14, -5]
  val_inv := by decide
  inv_val := by decide

/-- **Cassels, Ch. 9, Example 3 (ii)** (p. 162): *show that the ternary forms $z^2 - g(x, y)$ and $z^2 - h(x, y)$
are properly integrally equivalent.* $(z^2 - h)(S\mathbf x) = (z^2 - g)(\mathbf x)$ with $\det S = 1$; the third column
$-(1, 1, 5)$ comes from Cassels' hint $5^2 - h(1, 1) = 1$. -/
@[kb "cassels1978" "Ch. 9, Ex. 3 (ii), p. 162"]
theorem ex3_ternary : ProperIntEquiv ex3H ex3G := by
  refine ⟨ex3S, by decide, fun x => ?_⟩
  simp [ex3H, ex3G, ex3S, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three, dotProduct]
  ring

end QuadFormsKB.Siegel
