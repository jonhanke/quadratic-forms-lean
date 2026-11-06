/-
# Cassels, Chapter 9, Example 11 (iv): the cancellation $\langle 1, -1\rangle \perp g \to 2y_0y_1 + g$

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 11 (iv), p. 164 (attributed to
Serre; "The proof of (iv) is rather difficult"). Companion to `Ch9/Ex11.lean` (statement `Ex11_ii`, `Ex11_iv`) and
`Ch9/Ex11Serre.lean` (proof of (ii)).

**Conventions** as in `Ch9/Ex11.lean`: forms `QuadForm ℤ n` (0-based variables), `IsUnimodularCI` (classically integral of
determinant $\pm 1$), `oddPlane` $= y_0^2 - y_1^2$, `hypPlane` $= 2y_0y_1$, equivalence over $\mathbb Z$ `IntEquiv`, the
genus `Siegel.SameGenus` (equivalence over every $\mathbb Z_p$ and over $\mathbb R$).

**Proves (unconditionally).**
* `ex11_iv_holds` (**Cassels, Ch. 9, Ex. 11 (iv)**): the named statement `Ex11_iv` holds.
* `ex11_v_holds`, `ex11_vi_holds`: Ex. 11 (v) and (vi), previously conditional on `Ex11_ii` and `Ex11_iv`, now
  unconditional.

**Route (not Cassels' hint; local theory and Chapter 11).** Let $F_k = 2y_0y_1 + g_k$, a form in $n = m + 2$ variables,
$m \ge 1$ ($g_k$ improperly primitive forces $m \ge 1$). Then:
* $F_1, F_2$ are in one genus: at odd $p$ both are unimodular with the same determinant
  ($\det g_1 = \det g_2$ because $y_0^2 - y_1^2 + g_1 \cong y_0^2 - y_1^2 + g_2$), so equivalent over $\mathbb Z_p$
  (O'Meara 92:2, `Siegel.Kneser.isometricGL_of_unimodular`); at $p = 2$ they are $2G_1$, $2G_2$ for integer-valued forms
  $G_k$ with unimodular Hessian of the same determinant (even unimodular lattices), equivalent over $\mathbb Z_2$ by
  `isometricGL_two_of_unimodular` (`Ch9/EvenUnimodularTwo.lean`); over $\mathbb R$, $F_k \cong y_0^2 - y_1^2 + g_k$.
* $F_1$ is indefinite with determinant $\pm 2^n$, so by Chapter 11, Theorem 1.5 (`Siegel.intEquiv_of_sameGenus_of_ch11`:
  an indefinite form in $n \ge 3$ variables whose determinant is not divisible by $p^{n(n-1)/2}$ for odd $p$, nor, when
  classically integral, by the power of $2$ of Chapter 11, Theorem 1.3 (ii)) its genus has one class.
-/
import QuadFormsKB.Literature.Cassels.Ch9.Ex11Serre
import QuadFormsKB.Literature.Cassels.Ch9.EvenUnimodularTwo
import QuadFormsKB.Literature.Cassels.Ch9Examples
import QuadFormsKB.Siegel.UnimodularPadic

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch9Ex11

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels.Ch9EvenUnimodularTwo

variable {n m : ℕ}

/-! ### Determinants -/

/-- Helper: Cassels' matrix of an orthogonal sum of classically integral forms has determinant the product. -/
theorem det_casselsMat_orthSum {a : ℕ} {P : QuadForm ℤ a} {g : QuadForm ℤ m} (hP : IsClassicallyIntegral P)
    (hg : IsClassicallyIntegral g) :
    (Siegel.casselsMat (QuadForm.orthSum P g)).det = (Siegel.casselsMat P).det * (Siegel.casselsMat g).det := by
  have e : QuadForm.orthSum P g = Siegel.ofGram (blockMat (Siegel.casselsMat P) (Siegel.casselsMat g)) := by
    rw [← orthSum_ofGram (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g), Siegel.ofGram_casselsMat hP,
      Siegel.ofGram_casselsMat hg]
  rw [e, Siegel.casselsMat_ofGram (blockMat_isSymm (Siegel.casselsMat_isSymm P) (Siegel.casselsMat_isSymm g)),
    det_blockMat]

/-- Helper: the determinant of Cassels' matrix of the odd plane is $-1$. -/
theorem det_casselsMat_oddPlane : (Siegel.casselsMat oddPlane).det = -1 := by
  rw [casselsMat_oddPlane]; simp [Matrix.det_fin_two]

/-- Helper: the determinant of Cassels' matrix of the hyperbolic plane is $-1$. -/
theorem det_casselsMat_hypPlane : (Siegel.casselsMat hypPlane).det = -1 := by
  rw [casselsMat_hypPlane]; simp [Matrix.det_fin_two]

/-- Helper: if $y_0^2 - y_1^2 + g_1 \cong y_0^2 - y_1^2 + g_2$ then $\det g_1 = \det g_2$ (Cassels' matrices). -/
theorem det_eq_of_intEquiv_oddPlane {g₁ g₂ : QuadForm ℤ m} (h₁ : IsClassicallyIntegral g₁)
    (h₂ : IsClassicallyIntegral g₂)
    (h : IntEquiv (QuadForm.orthSum oddPlane g₁) (QuadForm.orthSum oddPlane g₂)) :
    (Siegel.casselsMat g₁).det = (Siegel.casselsMat g₂).det := by
  have hci : IsClassicallyIntegral oddPlane := (isUnimodularCI_oddPlane).1
  have := det_casselsMat_of_intEquiv (isClassicallyIntegral_orthSum hci h₁) (isClassicallyIntegral_orthSum hci h₂) h
  rw [det_casselsMat_orthSum hci h₁, det_casselsMat_orthSum hci h₂, det_casselsMat_oddPlane] at this
  linarith

/-- Helper: the Hessian determinant of a classically integral form is $2^n \det(f_{ij})$. -/
theorem hessian_det_eq_casselsMat {f : QuadForm ℤ n} (hf : IsClassicallyIntegral f) :
    f.hessian.det = 2 ^ n * (Siegel.casselsMat f).det := by
  rw [Siegel.hessian_eq_two_smul_casselsMat hf, Matrix.det_smul, Fintype.card_fin]

/-- Helper: the determinant of a mapped integer matrix is the image of the determinant. -/
theorem det_map_int {S : Type*} [CommRing S] (M : Matrix (Fin n) (Fin n) ℤ) :
    (M.map (Int.castRingHom S)).det = ((M.det : ℤ) : S) := (RingHom.map_det _ M).symm

/-! ### Values of scalar multiples and of mapped forms -/

/-- Helper: $(c\,Q)(\mathbf x) = c\,Q(\mathbf x)$. -/
theorem eval_smul_form {R : Type*} [CommRing R] (c : R) (Q : QuadForm R n) (x : Fin n → R) :
    (c • Q).eval x = c * Q.eval x := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- Helper: mapping commutes with scalar multiplication by an integer. -/
theorem map_smul_form {S : Type*} [CommRing S] (φ : ℤ →+* S) (c : ℤ) (Q : QuadForm ℤ n) :
    (c • Q).map φ = φ c • Q.map φ := by
  apply QuadForm.ext
  ext i j
  show φ ((c • Q.coeff) i j) = (φ c • Q.coeff.map φ) i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  rfl

/-- Helper: if $Q \cong Q'$ then $cQ \cong cQ'$ (the same matrix). -/
theorem IsometricGL.smul {R : Type*} [CommRing R] {Q Q' : QuadForm R n} (c : R) (h : IsometricGL Q Q') :
    IsometricGL (c • Q) (c • Q') := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun x => by rw [eval_smul_form, eval_smul_form, hg]⟩

/-- Helper: real equivalence of integral forms as equivalence of the forms mapped to $\mathbb R$. -/
theorem isometricGL_real_of_isometricIn {f g : QuadForm ℤ n} (h : f.IsometricIn ℝ g) :
    IsometricGL (f.map (Int.castRingHom ℝ)) (g.map (Int.castRingHom ℝ)) := by
  rw [isometricGL_iff_isometricIn]
  obtain ⟨P, hP, e⟩ := h
  refine ⟨P, hP, fun x => ?_⟩
  have h1 : ∀ (Q : QuadForm ℤ n) (y : Fin n → ℝ), (Q.map (Int.castRingHom ℝ)).evalIn ℝ y = Q.evalIn ℝ y := by
    intro Q y; simp [QuadForm.evalIn, QuadForm.map]
  rw [h1, h1, e]

/-! ### Indefiniteness in the sense of Chapter 11 -/

/-- Helper: an integral form which is indefinite (a positive and a negative real value) is indefinite in the sense of
Chapter 11 (`Lattices.IsIndefinite`: isotropic at the real place of $\mathbb Q$). -/
theorem lattices_isIndefinite {f : QuadForm ℤ n} (hind : IsIndefinite f) :
    Lattices.IsIndefinite (f.map (Int.castRingHom ℚ)) := by
  obtain ⟨x, hx0, hx⟩ := isotropicIn_real_of_indefinite hind
  refine ⟨Rat.infinitePlace, ?_⟩
  set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  refine ⟨fun i => ψ.symm (x i), fun h0 => hx0 (funext fun i => by simpa using congrArg ψ (congrFun h0 i)), ?_⟩
  apply ψ.injective
  rw [map_zero, ← hx]
  simp only [QuadForm.evalIn, map_sum, map_mul, map_pow, RingEquiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  split_ifs <;> simp

/-! ### The genus of $2y_0y_1 + g$ -/

/-- Helper: $p$-adic Hessian determinants of integral forms: a unit when $p \nmid \det H$. -/
theorem not_dvd_hessian_det_map (p : ℕ) [Fact p.Prime] (f : QuadForm ℤ n) (h : ¬ (p : ℤ) ∣ f.hessian.det) :
    ¬ (p : ℤ_[p]) ∣ (f.map (Int.castRingHom ℤ_[p])).hessian.det := by
  rw [Siegel.hessian_map, det_map_int]
  intro hd
  have hu : IsUnit ((f.hessian.det : ℤ) : ℤ_[p]) := Binary.isUnit_intCast_padic h
  exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_unit hd (by simpa using hu))

/-- Helper: the forms $2y_0y_1 + g_1$ and $2y_0y_1 + g_2$ are in one genus when $g_1, g_2$ are improperly primitive
unimodular (in $m$ variables) and $y_0^2 - y_1^2 + g_1 \cong y_0^2 - y_1^2 + g_2$. -/
theorem sameGenus_hyp {g₁ g₂ : QuadForm ℤ m} (hm : 0 < m) (hu₁ : IsUnimodularCI g₁) (hu₂ : IsUnimodularCI g₂)
    (he₁ : ∀ i, 2 ∣ g₁.coeff i i) (he₂ : ∀ i, 2 ∣ g₂.coeff i i)
    (h : IntEquiv (QuadForm.orthSum oddPlane g₁) (QuadForm.orthSum oddPlane g₂)) :
    SameGenus (QuadForm.orthSum hypPlane g₁) (QuadForm.orthSum hypPlane g₂) := by
  set F₁ := QuadForm.orthSum hypPlane g₁
  set F₂ := QuadForm.orthSum hypPlane g₂
  have hc₁ : IsClassicallyIntegral F₁ := isClassicallyIntegral_orthSum ci_hypPlane hu₁.1
  have hc₂ : IsClassicallyIntegral F₂ := isClassicallyIntegral_orthSum ci_hypPlane hu₂.1
  have hdg := det_eq_of_intEquiv_oddPlane hu₁.1 hu₂.1 h
  have hdC : (Siegel.casselsMat F₁).det = (Siegel.casselsMat F₂).det := by
    rw [det_casselsMat_orthSum ci_hypPlane hu₁.1, det_casselsMat_orthSum ci_hypPlane hu₂.1, hdg]
  have hdH : F₂.hessian.det = F₁.hessian.det := by
    rw [hessian_det_eq_casselsMat hc₁, hessian_det_eq_casselsMat hc₂, hdC]
  have hU₁ : (Siegel.casselsMat F₁).det = 1 ∨ (Siegel.casselsMat F₁).det = -1 :=
    (isUnimodularCI_orthSum isUnimodularCI_hypPlane hu₁).2
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp2 : p = 2
    · subst hp2
      -- the halves `G_k` with `F_k = 2 G_k` and Hessian `casselsMat F_k`
      have hi₁ := isImproperlyPrimitive_of_even (by omega) (isUnimodularCI_orthSum isUnimodularCI_hypPlane hu₁)
        (diag_even_orthSum ci_hypPlane hu₁.1 diag_even_hypPlane he₁)
      have hi₂ := isImproperlyPrimitive_of_even (by omega) (isUnimodularCI_orthSum isUnimodularCI_hypPlane hu₂)
        (diag_even_orthSum ci_hypPlane hu₂.1 diag_even_hypPlane he₂)
      obtain ⟨G₁, hG₁, -⟩ := exists_half_of_improperlyPrimitive hi₁
      obtain ⟨G₂, hG₂, -⟩ := exists_half_of_improperlyPrimitive hi₂
      have hH : ∀ {F G : QuadForm ℤ (2 + m)}, IsClassicallyIntegral F → (2 : ℤ) • G = F →
          G.hessian = Siegel.casselsMat F := by
        intro F G hF hGF
        have h1 := Siegel.hessian_eq_two_smul_casselsMat hF
        have h2 : F.hessian = (2 : ℤ) • G.hessian := by
          rw [← hGF]; ext i j
          simp only [QuadForm.hessian, QuadForm.smul_coeff, Matrix.add_apply, Matrix.transpose_apply,
            Matrix.smul_apply, smul_eq_mul]
          ring
        rw [h2] at h1
        exact smul_right_injective _ (two_ne_zero) h1
      have hGH₁ := hH hc₁ hG₁
      have hGH₂ := hH hc₂ hG₂
      have hloc : IsometricGL (G₁.map (Int.castRingHom ℤ_[2])) (G₂.map (Int.castRingHom ℤ_[2])) := by
        refine isometricGL_two_of_unimodular _ _ ?_ ?_
        · rw [Siegel.hessian_map, det_map_int, hGH₁]
          rcases hU₁ with h1 | h1 <;> rw [h1] <;> simp
        · rw [Siegel.hessian_map, Siegel.hessian_map, det_map_int, det_map_int, hGH₁, hGH₂, hdC]
      have := IsometricGL.smul (2 : ℤ_[2]) hloc
      rw [show F₁ = (2 : ℤ) • G₁ from hG₁.symm, show F₂ = (2 : ℤ) • G₂ from hG₂.symm, map_smul_form,
        map_smul_form]
      simpa using this
    · refine Kneser.isometricGL_of_unimodular hp2 _ _ (not_dvd_hessian_det_map p F₁ ?_) ?_
      · rw [hessian_det_eq_casselsMat hc₁]
        intro hd
        have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
        rcases hpp.dvd_or_dvd hd with h2 | h2
        · have h' : p ∣ 2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast hpp.dvd_of_dvd_pow h2)
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
        · rcases hU₁ with h1 | h1 <;> rw [h1] at h2
          · exact hpp.not_isUnit (isUnit_of_dvd_one h2)
          · exact hpp.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp h2))
      · rw [Siegel.hessian_map, Siegel.hessian_map, det_map_int, det_map_int, hdH]
  · apply isometricGL_real_of_isometricIn
    refine isometricIn_real_trans (isometricIn_real_hyp_odd g₁) (isometricIn_real_trans ?_
      (isometricIn_real_symm (isometricIn_real_hyp_odd g₂)))
    exact isometricIn_real_of_intEquiv (isClassicallyIntegral_orthSum isUnimodularCI_oddPlane.1 hu₁.1)
      (isClassicallyIntegral_orthSum isUnimodularCI_oddPlane.1 hu₂.1) h

/-! ### (iv), (v), (vi) -/

/-- **Cassels, Ch. 9, Ex. 11 (iv)** (p. 164): *if $g_1, g_2$ are improperly primitive (classically integral of
determinant $\pm 1$) and $y_0^2 - y_1^2 + g_1$, $y_0^2 - y_1^2 + g_2$ are equivalent, then $2y_0y_1 + g_1$ and
$2y_0y_1 + g_2$ are equivalent.* The named statement `Ex11_iv` holds, unconditionally (see the module docstring for the
route, which is not Cassels'). -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (iv), p. 164 (proof)"]
theorem ex11_iv_holds : Ex11_iv := by
  intro m g₁ g₂ hu₁ hu₂ hp₁ hp₂ h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exfalso
      exact (show ¬ IsUnit (0 : ℤ) by simp) (hp₁.1.2 0 fun i => i.elim0)
    · exact hm
  set F₁ := QuadForm.orthSum hypPlane g₁
  have hc₁ : IsClassicallyIntegral F₁ := isClassicallyIntegral_orthSum ci_hypPlane hu₁.1
  have hU₁ : (Siegel.casselsMat F₁).det = 1 ∨ (Siegel.casselsMat F₁).det = -1 :=
    (isUnimodularCI_orthSum isUnimodularCI_hypPlane hu₁).2
  have hind : IsIndefinite F₁ :=
    isIndefinite_of_isometricIn (isometricIn_real_hyp_odd g₁) (isIndefinite_orthSum_oddPlane g₁)
  refine intEquiv_of_sameGenus_of_ch11 (by omega) F₁ ?_ (lattices_isIndefinite hind) ?_ ?_ _
    (sameGenus_hyp hm hu₁ hu₂ hp₁.2 hp₂.2 h)
  · rw [hessian_det_eq_casselsMat hc₁]
    rcases hU₁ with h1 | h1 <;> rw [h1] <;> simp
  · intro p hp hp2 hd
    rw [hessian_det_eq_casselsMat hc₁] at hd
    have hk : 1 ≤ (2 + m) * (2 + m - 1) / 2 := by
      have e : 2 + m - 1 = 1 + m := by omega
      have : 2 ≤ (2 + m) * (2 + m - 1) := by rw [e]; nlinarith
      omega
    have hpd : (p : ℤ) ∣ 2 ^ (2 + m) * (Siegel.casselsMat F₁).det :=
      dvd_trans (dvd_pow_self _ (by omega)) hd
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpp.dvd_or_dvd hpd with h2 | h2
    · have h' : p ∣ 2 := Int.natCast_dvd_natCast.mp (by exact_mod_cast hpp.dvd_of_dvd_pow h2)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · rcases hU₁ with h1 | h1 <;> rw [h1] at h2
      · exact hpp.not_isUnit (isUnit_of_dvd_one h2)
      · exact hpp.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp h2))
  · right
    rw [hessian_det_eq_casselsMat hc₁]
    intro hd
    have hE : 2 + m + 1 ≤ (Lattices.casselsExpTwo (2 + m) + ((2 + m : ℕ) : ℤ)).toNat := by
      unfold Lattices.casselsExpTwo
      have h1 : (1 : ℤ) ≤ ((2 + m : ℕ) : ℤ) * (((2 + m : ℕ) : ℤ) - 3) / 2 + (((2 + m : ℕ) : ℤ) + 1) / 2 := by
        have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
        push_cast
        have e1 : 0 ≤ ((2 : ℤ) + m) * ((2 + m) - 3) / 2 := by
          apply Int.ediv_nonneg _ (by norm_num); nlinarith
        have e2 : 1 ≤ ((2 : ℤ) + m + 1) / 2 := by omega
        linarith
      omega
    have h2 : (2 : ℤ) ^ (2 + m + 1) ∣ 2 ^ (2 + m) * (Siegel.casselsMat F₁).det :=
      dvd_trans (pow_dvd_pow 2 hE) hd
    rw [pow_succ, mul_comm ((2 : ℤ) ^ (2 + m)) 2, mul_comm ((2 : ℤ) ^ (2 + m))] at h2
    have h3 := (mul_dvd_mul_iff_right (by positivity : (2 : ℤ) ^ (2 + m) ≠ 0)).mp h2
    rcases hU₁ with h1 | h1 <;> rw [h1] at h3 <;> omega

/-- **Cassels, Ch. 9, Ex. 11 (v)** (p. 164), unconditional: indefinite improperly primitive unimodular forms which are
equivalent over $\mathbb R$ are equivalent over $\mathbb Z$ (`ex11_v` with `ex11_ii_holds`, `ex11_iv_holds`). -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (v), p. 164 (unconditional)"]
theorem ex11_v_holds (f₁ f₂ : QuadForm ℤ (2 + m)) (hf₁ : IsUnimodularCI f₁) (hf₂ : IsUnimodularCI f₂)
    (hi₁ : IsIndefinite f₁) (hi₂ : IsIndefinite f₂) (hp₁ : Siegel.IsImproperlyPrimitive f₁) (hp₂ : Siegel.IsImproperlyPrimitive f₂)
    (hR : f₁.IsometricIn ℝ f₂) : IntEquiv f₁ f₂ :=
  ex11_v ex11_ii_holds ex11_iv_holds f₁ f₂ hf₁ hf₂ hi₁ hi₂ hp₁ hp₂ hR

/-- **Cassels, Ch. 9, Ex. 11 (vi)** (p. 164), unconditional: an indefinite improperly primitive unimodular form $f$, or
$-f$, is equivalent to an orthogonal sum of hyperbolic planes $2y_0y_1$ and copies of $E_8$ (`ex11_vi` with
`ex11_ii_holds`, `ex11_iv_holds`). -/
@[kb "cassels1978" "Ch. 9, Ex. 11 (vi), p. 164 (unconditional)"]
theorem ex11_vi_holds (f : QuadForm ℤ n) (hf : IsUnimodularCI f) (hind : IsIndefinite f)
    (hp : Siegel.IsImproperlyPrimitive f) : IsHypE8Sum n f ∨ IsHypE8Sum n (negForm f) :=
  ex11_vi ex11_ii_holds ex11_iv_holds f hf hind hp

end QuadFormsKB.Cassels.Ch9Ex11
