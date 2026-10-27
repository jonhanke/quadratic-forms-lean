/-
# Cassels, Chapter 11, §6: the language of forms (Theorems 6.1, 6.2)

**Layer:** integer-valued forms $f$ = `f : QuadForm ℤ n` (Cassels' integral forms are the classically integral ones,
`IsClassicallyIntegral`); the determinant $d$ of Cassels is $2^{-n}\det H$ for the Hessian $H$ (`f.hessian`), so
"the same determinant" is the same `hessian.det`; rational equivalence is `Siegel.IsometricGL` of the forms over
$\mathbb Q$; proper $\mathbb Z$-equivalence $g \sim^+ f$: $g(x) = f(Ux)$ with $U \in \mathrm{SL}_n(\mathbb Z)$; the genus
is `Siegel.SameGenus` (Cassels Ch. 9).

**Proves**
* Theorem 6.1 (p. 224) (`exists_chain_of_isometricGL_rat`): two classically integral forms of the same determinant
  $d \ne 0$ in $n \ge 2$ variables that are rationally equivalent are joined by a chain $g_0 = f_1, \dots, g_V = f_2$
  of classically integral forms of determinant $d$, each step either a proper $\mathbb Z$-equivalence or the
  substitution $g_{v+1}(x) = g_v(px_0, x_1, \dots, x_{n-2}, p^{-1}x_{n-1})$ for a prime $p$ (0-based; the display of
  (ii) is garbled in the scan and is read from the proof: the change from the basis $b_0, \dots, b_{n-2}, pb_{n-1}$
  of one lattice to the basis $pb_0, b_1, \dots, b_{n-1}$ of the next, Theorem 5.1, Corollary).
* Theorem 6.2 (p. 225), converse part (`sameGenus_of_chain`): if such a chain uses only primes $p \nmid 2d$, then
  $f_1, f_2$ are in the same genus.

*Proof of 6.1 (as in Cassels).* A rational equivalence $g$ of determinant $1$ (composing with a rational reflection
if $\det g = -1$) gives lattices $\Lambda = \mathbb Z^n$, $\Gamma = g\mathbb Z^n$ of the same determinant, both classically
integral; Lemma 4.4, Corollary, joins them by a chain with prime indices; consecutive lattices have bases as in
Theorem 5.1, Corollary; positively oriented bases of one lattice give properly $\mathbb Z$-equivalent forms
(Lemma 1.1, Corollary 2, here `exists_unimod_of_latOf_eq`). *Proof of 6.2:* a step (ii) with $p \nmid 2d$ is an
isometry over $\mathbb Z_q$ for $q \ne p$ and over $\mathbb R$ by the scaled matrix, and over $\mathbb Z_p$ because
both forms are unimodular of the same determinant.
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec5
import QuadFormsKB.Literature.Cassels.Ch11Sec4Chain
import QuadFormsKB.Literature.Cassels.Ch11Sec1Forms
import QuadFormsKB.Siegel.Genus
import QuadFormsKB.Siegel.NeighborGenus
import QuadFormsKB.Equiv.Integral

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {n : ℕ}

/-- The substitution of Cassels' Theorem 6.1 (ii) (0-based): $x \mapsto (px_0, x_1, \dots, x_{n-2}, p^{-1}x_{n-1})$. -/
def casselsSubst (p : ℕ) (x : Fin n → ℚ) : Fin n → ℚ :=
  fun j => if j.1 = 0 then (p : ℚ) * x j else if j.1 = n - 1 then x j / p else x j

/-- The diagonal matrix $\mathrm{diag}(p, 1, \dots, 1, p^{-1})$ of the substitution `casselsSubst`. -/
def casselsSubstDiag (n p : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun j => if j.1 = 0 then (p : ℚ) else if j.1 = n - 1 then 1 / (p : ℚ) else 1

theorem casselsSubst_eq (p : ℕ) (x : Fin n → ℚ) : casselsSubst p x = casselsSubstDiag n p *ᵥ x := by
  ext j
  simp only [casselsSubst, casselsSubstDiag, mulVec_diagonal]
  split_ifs <;> ring

theorem map_evalIn_rat (Q : QuadForm ℤ n) (x : Fin n → ℚ) :
    (Q.map (Int.castRingHom ℚ)).evalIn ℚ x = Q.evalIn ℚ x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-! ### Theorem 6.2, converse: one step (ii) preserves the genus when $p \nmid 2d$ -/

/-- One step (ii) with $p \nmid 2d$ stays in the genus: the scaled matrices give equivalence over $\mathbb Z_q$,
$q \ne p$, and over $\mathbb R$; at $p$ both forms are unimodular of the same determinant. -/
theorem sameGenus_of_subst (hn : 2 ≤ n) {p : ℕ} (hp : p.Prime) (Q Q' : QuadForm ℤ n)
    (hpd : ¬ (p : ℤ) ∣ 2 * Q.hessian.det) (hdet : Q'.hessian.det = Q.hessian.det)
    (h : ∀ x : Fin n → ℚ, (Q'.map (Int.castRingHom ℚ)).evalIn ℚ x =
      (Q.map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x)) : Siegel.SameGenus Q Q' := by
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpd (dvd_mul_right _ _)
  have hpdet : ¬ (p : ℤ) ∣ Q.hessian.det := fun hd => hpd (Dvd.dvd.mul_left hd _)
  let D : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.diagonal fun j => if j.1 = 0 then (p : ℤ) ^ 2 else if j.1 = n - 1 then 1 else p
  let D' : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.diagonal fun j => if j.1 = 0 then 1 else if j.1 = n - 1 then (p : ℤ) ^ 2 else p
  have hDD : ∀ i j, (D * D') i j = if i = j then (p : ℤ) ^ 2 else 0 := by
    intro i j
    simp only [D, D', diagonal_mul_diagonal, diagonal_apply]
    by_cases hij : i = j
    · subst hij
      have hn1 : n - 1 ≠ 0 := by omega
      by_cases h0 : i.1 = 0
      · have : i.1 ≠ n - 1 := by omega
        simp [h0, this]
      · by_cases h1 : i.1 = n - 1
        · simp [h0, h1, hn1]
        · simp [h0, h1]; ring
    · simp [hij]
  have hD'D : ∀ i j, (D' * D) i j = if i = j then (p : ℤ) ^ 2 else 0 := by
    intro i j
    have : D' * D = D * D' := by
      simp only [D, D', diagonal_mul_diagonal]
      congr 1; funext k; ring
    rw [this]; exact hDD i j
  have hQD : ∀ x, Q.eval (D *ᵥ x) = (((p : ℤ) ^ 2) • Q').eval x := by
    intro x
    rw [Siegel.Kneser.eval_smul_form]
    have e1 : Siegel.Kneser.cv (D *ᵥ x) = (p : ℚ) • casselsSubst p (Siegel.Kneser.cv x) := by
      ext j
      simp only [D, mulVec_diagonal, Siegel.Kneser.cv_apply, casselsSubst, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> push_cast <;> field_simp
    have := Siegel.Kneser.evalIn_cv Q (D *ᵥ x)
    rw [e1, Siegel.Kneser.evalIn_smulQ, ← map_evalIn_rat Q, ← h, map_evalIn_rat,
      Siegel.Kneser.evalIn_cv] at this
    exact_mod_cast this.symm
  refine ⟨fun ℓ _ => ?_, ?_⟩
  · by_cases hℓ : ℓ = p
    · subst hℓ
      apply Siegel.Kneser.isometricGL_of_unimodular hp2
      · rw [Siegel.Kneser.hessian_map, Siegel.Kneser.det_map_eq]
        rintro ⟨c, hc⟩
        apply hpdet
        rw [← Siegel.Kneser.dvd_of_red, ← Siegel.Kneser.toZMod_intCast (ℓ := ℓ)]
        change PadicInt.toZMod ((Int.castRingHom ℤ_[ℓ]) Q.hessian.det) = 0
        rw [hc, map_mul, Siegel.Kneser.toZMod_natCast_self, zero_mul]
      · rw [Siegel.Kneser.hessian_map, Siegel.Kneser.hessian_map, Siegel.Kneser.det_map_eq,
          Siegel.Kneser.det_map_eq, hdet]
    · have hu : IsUnit ((p : ℤ) : ℤ_[ℓ]) := by
        apply Siegel.Kneser.isUnit_of_toZMod_ne_zero
        rw [Siegel.Kneser.toZMod_intCast]
        intro h
        rw [Siegel.Kneser.dvd_of_red] at h
        have : ℓ ∣ p := by exact_mod_cast h
        exact hℓ ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp this)
      exact Siegel.Kneser.isometricGL_of_scaled (Int.castRingHom ℤ_[ℓ]) (p : ℤ) hu.unit (by simp) hDD hD'D hQD
  · have hu : IsUnit (((p : ℤ)) : ℝ) := by
      simp only [Int.cast_natCast]
      exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
    exact Siegel.Kneser.isometricGL_of_scaled (Int.castRingHom ℝ) (p : ℤ) hu.unit (by simp) hDD hD'D hQD

/-- The chain argument of Theorem 6.2: along a chain of steps (i)/(ii) with $p \nmid 2d$ and constant Hessian
determinant, the first and last forms are in the same genus. -/
theorem sameGenus_of_chain_aux (hn : 2 ≤ n) (V : ℕ) (g : Fin (V + 1) → QuadForm ℤ n)
    (hdet : ∀ v, (g v).hessian.det = (g 0).hessian.det)
    (hstep : ∀ v : Fin V,
        (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, (g v.succ).eval x = (g v.castSucc).eval (U *ᵥ x)) ∨
        ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ 2 * (g 0).hessian.det ∧ ∀ x : Fin n → ℚ,
          ((g v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
            ((g v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x)) :
    Siegel.SameGenus (g 0) (g (Fin.last V)) := by
  have key : ∀ k (hk : k ≤ V), Siegel.SameGenus (g 0) (g ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => intro _; exact Siegel.SameGenus.refl _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      set v : Fin V := ⟨k, by omega⟩
      refine h1.trans ?_
      rcases hstep v with ⟨U, hU, hUe⟩ | ⟨p, hp, hpd, hsub⟩
      · have : Siegel.IntEquiv (g v.castSucc) (g v.succ) :=
          (Siegel.isometricGL_iff_isometricIn _ _).mpr
            ⟨U, by rw [hU]; exact isUnit_one, fun x => (hUe x).symm⟩
        exact this.sameGenus
      · exact sameGenus_of_subst hn hp _ _ (by
          change ¬ (p : ℤ) ∣ 2 * (g v.castSucc).hessian.det
          rw [hdet v.castSucc]; exact hpd)
          ((hdet v.succ).trans (hdet v.castSucc).symm) hsub
  exact key V le_rfl

/-- **Cassels, Theorem 6.2** (Ch. 11, p. 225), converse part: *if $f_1, f_2$ are classically integral forms of
determinant $d$ and there is a sequence of forms $g_v$ such that for each $v$ either (i) holds or (ii) holds with
$p \nmid 2d$, then $f_1, f_2$ are in the same genus.* -/
@[kb "cassels1978" "Ch. 11, Thm. 6.2, p. 225 (converse part)"]
theorem sameGenus_of_chain (hn : 2 ≤ n) (V : ℕ) (g : Fin (V + 1) → QuadForm ℤ n)
    (hint : ∀ v, IsClassicallyIntegral (g v)) (hdet : ∀ v, (g v).hessian.det = (g 0).hessian.det)
    (hd0 : (g 0).hessian.det ≠ 0)
    (hstep : ∀ v : Fin V,
        (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, (g v.succ).eval x = (g v.castSucc).eval (U *ᵥ x)) ∨
        ∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ 2 * (g 0).hessian.det ∧ ∀ x : Fin n → ℚ,
          ((g v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
            ((g v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x)) :
    Siegel.SameGenus (g 0) (g (Fin.last V)) :=
  sameGenus_of_chain_aux hn V g hdet hstep

/-! ### Theorem 6.1: lattices and their integer forms -/

open Tamagawa.SiegelSpace in
theorem diagLat_one_eq : diagLat (F := ℚ) (N := n) (fun _ => 1) = intVec := by
  ext ξ
  rw [mem_diagLat, mem_intVec]
  simp only [Units.val_one, FractionalIdeal.mem_one_iff]
  rfl

open Tamagawa.SiegelSpace in
/-- The index of the free lattice $\gamma\mathbb Z^n$ is $|\det\gamma|^{-1}$. -/
theorem latIndex_latOf (γ : GL (Fin n) ℚ) :
    latIndex (⟨latOf γ, latOf_isLattice γ⟩ : Lat ℚ n) = |(γ : Matrix (Fin n) (Fin n) ℚ).det|⁻¹ := by
  rw [latIndex_eq_inv_covol (⟨latOf γ, latOf_isLattice γ⟩ : Lat ℚ n) γ (fun _ => 1)
    (by rw [diagLat_one_eq]; rfl)]
  simp [LatCovol.covol, IdeleClass.idealNorm]

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

/-- **Classical integrality of a submodule** for a form `Q` over `ℚ`: `B(x, y) = x ᵀ H y ∈ 2ℤ`
for all `x, y` in the submodule. -/
def LatCI (Q : QuadForm ℚ n) (X : Submodule (𝓞 ℚ) (Fin n → ℚ)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∃ z : ℤ, qbil Q ℚ x y = 2 * z

theorem ok2_two_mul_int (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) : Ok2 v (2 * (z : ℚ)) := by
  have h := Ok2.mul v (q := 2) (r := (z : ℚ)) (le_refl _) (val_intCast_le_one v z)
  rwa [mul_comm] at h

/-- Global classical integrality is local classical integrality at every prime. -/
theorem latCI_iff_loc (Q : QuadForm ℚ n) (X : Submodule (𝓞 ℚ) (Fin n → ℚ)) :
    LatCI Q X ↔ ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ x ∈ loc v X, ∀ y ∈ loc v X,
      Valued.v (qbil Q (v.adicCompletion ℚ) x y) ≤ Valued.v (2 : v.adicCompletion ℚ) := by
  constructor
  · intro h v
    refine loc_qbil_le Q v X fun x hx y hy => ?_
    obtain ⟨z, hz⟩ := h x hx y hy
    rw [hz]; exact ok2_two_mul_int v z
  · intro h x hx y hy
    have hq : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (qbil Q ℚ x y / 2) ≤ 1 := by
      intro v
      have h1 := ok2_of_loc Q v X (h v) x hx y hy
      have h2 : v.valuation ℚ (2 : ℚ) ≠ 0 := by simp
      rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr h2)]
      exact h1
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 ℚ) ℚ _ hq
    obtain ⟨z, hz⟩ : ∃ z : ℤ, a = (z : 𝓞 ℚ) := by
      refine ⟨Rat.ringOfIntegersEquiv a, ?_⟩
      apply Rat.ringOfIntegersEquiv.injective
      simp
    refine ⟨z, ?_⟩
    rw [hz] at ha
    have ha' : (z : ℚ) = qbil Q ℚ x y / 2 := by rw [← ha]; simp
    linarith [ha', show qbil Q ℚ x y = 2 * (qbil Q ℚ x y / 2) by ring]

section Forms

variable (f : QuadForm ℤ n)

/-- `F` is the integer form of the basis `γ` (columns) for the form `f`: `F(x) = f(γx)`. -/
def FormOf (γ : GL (Fin n) ℚ) (F : QuadForm ℤ n) : Prop :=
  ∀ x : Fin n → ℚ, F.evalIn ℚ x = f.evalIn ℚ (γ.val *ᵥ x)

theorem qbil_map_int (x y : Fin n → ℚ) :
    qbil (f.map (Int.castRingHom ℚ)) ℚ x y = Siegel.Kneser.bQ f x y := by
  unfold qbil Siegel.Kneser.bQ
  rw [Siegel.Kneser.hessian_map, Matrix.map_map]
  rfl

theorem mem_latOf_cv (γ : GL (Fin n) ℚ) (c : Fin n → ℤ) :
    γ.val *ᵥ Siegel.Kneser.cv c ∈ latOf γ := by
  refine mulVec_mem_glImage ?_
  rw [mem_intVec]
  intro i
  exact ⟨(c i : 𝓞 ℚ), by simp [Siegel.Kneser.cv]⟩

/-- A classically integral lattice has an integer, classically integral form in any basis. -/
theorem exists_formOf (γ : GL (Fin n) ℚ) (h : LatCI (f.map (Int.castRingHom ℚ)) (latOf γ)) :
    ∃ F : QuadForm ℤ n, FormOf f γ F ∧ IsClassicallyIntegral F := by
  have hq : ∀ c d : Fin n → ℤ, ∃ z : ℤ, Siegel.Kneser.bQ f (γ.val *ᵥ Siegel.Kneser.cv c)
      (γ.val *ᵥ Siegel.Kneser.cv d) = 2 * z := fun c d => by
    obtain ⟨z, hz⟩ := h _ (mem_latOf_cv γ c) _ (mem_latOf_cv γ d)
    exact ⟨z, by rw [← qbil_map_int]; exact hz⟩
  have hint : ∀ c : Fin n → ℤ, ∃ z : ℤ, f.evalIn ℚ (γ.val *ᵥ Siegel.Kneser.cv c) = z := by
    intro c
    obtain ⟨z, hz⟩ := hq c c
    refine ⟨z, ?_⟩
    have := Siegel.Kneser.two_mul_evalIn f (γ.val *ᵥ Siegel.Kneser.cv c)
    unfold Siegel.Kneser.bQ at hz
    simp only [algebraMap_int_eq] at this hz
    linarith
  obtain ⟨F, hF⟩ := Siegel.Kneser.exists_gramForm (Q := f) (g := γ.val) hint
  refine ⟨F, hF, ?_⟩
  rw [isClassicallyIntegral_iff]
  intro i j hij
  have hH := Siegel.Kneser.hessian_eq_conj hF
  have h1 := congrFun (congrFun hH i) j
  rw [Siegel.Kneser.conj_apply_col] at h1
  have hcol : ∀ i, γ.val.col i = γ.val *ᵥ Siegel.Kneser.cv (Pi.single i 1) := by
    intro i; ext r; simp [mulVec, dotProduct, Pi.single_apply, Matrix.col_apply, Siegel.Kneser.cv]
  obtain ⟨z, hz⟩ := hq (Pi.single i 1) (Pi.single j 1)
  rw [hcol, hcol] at h1
  have h2 : F.hessian i j = F.coeff i j := by
    simp [QuadForm.hessian, F.upper hij]
  refine ⟨z, ?_⟩
  have h3 : ((F.coeff i j : ℤ) : ℚ) = 2 * z := by
    rw [← h2]
    have h4 : ((F.hessian i j : ℤ) : ℚ) = Siegel.Kneser.bQ f (γ.val *ᵥ Siegel.Kneser.cv (Pi.single i 1))
        (γ.val *ᵥ Siegel.Kneser.cv (Pi.single j 1)) := h1
    rw [h4]
    exact hz
  have : F.coeff i j = 2 * z := by exact_mod_cast h3
  omega

theorem formOf_hessian_det {γ : GL (Fin n) ℚ} {F : QuadForm ℤ n} (hF : FormOf f γ F)
    (hγ : |(γ : Matrix (Fin n) (Fin n) ℚ).det| = 1) : F.hessian.det = f.hessian.det := by
  have hH := Siegel.Kneser.hessian_eq_conj hF
  have h1 := congrArg Matrix.det hH
  rw [det_mul, det_mul, det_transpose, Siegel.Kneser.det_map_eq, Siegel.Kneser.det_map_eq] at h1
  have hsq : (γ : Matrix (Fin n) (Fin n) ℚ).det * (γ : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    have := congrArg (· ^ 2) hγ
    simp only [sq_abs, one_pow] at this
    rw [← sq]; exact this
  rw [show (γ : Matrix (Fin n) (Fin n) ℚ).det * algebraMap ℤ ℚ f.hessian.det *
      (γ : Matrix (Fin n) (Fin n) ℚ).det = algebraMap ℤ ℚ f.hessian.det by
    rw [mul_comm, ← mul_assoc, mul_comm _ (γ : Matrix (Fin n) (Fin n) ℚ).det, hsq, one_mul]] at h1
  exact_mod_cast h1

theorem cast_mulVec_cv (U : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    U.map (Int.castRingHom ℚ) *ᵥ Siegel.Kneser.cv x = Siegel.Kneser.cv (U *ᵥ x) := by
  ext i
  simp [mulVec, dotProduct, Siegel.Kneser.cv]

/-- **Step (i):** two positively oriented bases of the same lattice differ by a matrix in $\mathrm{SL}_n(\mathbb Z)$
(Cassels, Lemma 1.1, Corollary 2). -/
theorem exists_unimod_of_latOf_eq {γ δ : GL (Fin n) ℚ} (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det)
    (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det) (h : latOf γ = latOf δ) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ U.map (Int.castRingHom ℚ) = (δ⁻¹ * γ).val := by
  have hP : glImage (δ⁻¹ * γ) intVec = intVec := by
    rw [glImage_mul]
    change glImage δ⁻¹ (latOf γ) = intVec
    rw [h, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
  obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
  have e : (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) ℚ) = (δ⁻¹ * γ).val :=
    congrArg Units.val hP₀
  set U : Matrix (Fin n) (Fin n) ℤ := (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).map Rat.ringOfIntegersEquiv
  have hU : U.map (Int.castRingHom ℚ) = (δ⁻¹ * γ).val := by
    rw [← e]
    ext i j
    simp [U, Rat.ringOfIntegersEquiv_apply_coe]
  have hdet : ((U.det : ℤ) : ℚ) = (δ⁻¹ : GL (Fin n) ℚ).val.det * γ.val.det := by
    have := congrArg Matrix.det hU
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    rw [show ((U.det : ℤ) : ℚ) = Int.castRingHom ℚ U.det from rfl, this, Units.val_mul, det_mul]
  have hinv : (δ⁻¹ : GL (Fin n) ℚ).val.det * δ.val.det = 1 := by
    rw [← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
  have hpos : 0 < (δ⁻¹ : GL (Fin n) ℚ).val.det := by
    by_contra hc
    push Not at hc
    nlinarith
  have hunit : IsUnit U.det := by
    have : IsUnit (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det := P₀.isUnit.map Matrix.detMonoidHom
    have h2 := this.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
    have h3 : U.det = (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (P₀ : Matrix (Fin n) (Fin n) (𝓞 ℚ)).det :=
      (RingHom.map_det (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) _).symm
    rwa [h3]
  refine ⟨U, ?_, hU⟩
  rcases Int.isUnit_iff.mp hunit with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hdet
    have := mul_pos hpos hγ
    simp only [Int.cast_neg, Int.cast_one] at hdet
    linarith

theorem eval_eq_of_latOf_eq {γ δ : GL (Fin n) ℚ} {F F' : QuadForm ℤ n}
    (hF : FormOf f γ F) (hF' : FormOf f δ F') {U : Matrix (Fin n) (Fin n) ℤ}
    (hU : U.map (Int.castRingHom ℚ) = (δ⁻¹ * γ).val) (x : Fin n → ℤ) :
    F.eval x = F'.eval (U *ᵥ x) := by
  have h1 := Siegel.Kneser.evalIn_cv F x
  have h2 := Siegel.Kneser.evalIn_cv F' (U *ᵥ x)
  rw [← cast_mulVec_cv, hF'] at h2
  rw [hF] at h1
  rw [hU, Units.val_mul, ← mulVec_mulVec] at h2
  have e : (δ : Matrix (Fin n) (Fin n) ℚ) *ᵥ ((δ⁻¹ : GL (Fin n) ℚ).val *ᵥ (γ.val *ᵥ Siegel.Kneser.cv x)) =
      γ.val *ᵥ Siegel.Kneser.cv x := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [e] at h2
  exact_mod_cast h1.symm.trans h2

end Forms

/-! ### Bases, spans, signs -/

theorem latOf_eq_span (γ : GL (Fin n) ℚ) :
    latOf γ = Submodule.span (𝓞 ℚ) (Set.range fun j : Fin n => γ.val *ᵥ Pi.single j (1 : ℚ)) := by
  apply le_antisymm
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hz
    have h1 := sum_smul_col γ (intCoe x)
    show γ.val *ᵥ intCoe x ∈ _
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : intCoe x j • (γ.val *ᵥ Pi.single j (1 : ℚ)) = x j • (γ.val *ᵥ Pi.single j (1 : ℚ)) := by
      rw [← algebraMap_smul ℚ (x j)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact mulVec_mem_glImage (single_one_mem_intVec j)

theorem cols_mul_diagonal (B : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) (j : Fin n) :
    (B * Matrix.diagonal d) *ᵥ Pi.single j (1 : ℚ) = d j • (B *ᵥ Pi.single j (1 : ℚ)) := by
  rw [← mulVec_mulVec, ← mulVec_smul]
  congr 1
  ext i
  simp only [mulVec_diagonal, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- A diagonal matrix with entries `1` and `ε = ±1` (at index 0) stabilizes `ℤⁿ`. -/
theorem exists_signMat (hn : 0 < n) (ε : ℚ) (hε : ε = 1 ∨ ε = -1) :
    ∃ E : GL (Fin n) ℚ, E.val = Matrix.diagonal (Function.update (1 : Fin n → ℚ) ⟨0, hn⟩ ε) ∧
      glImage E intVec = intVec ∧ E.val.det = ε := by
  set e : Fin n → ℚ := Function.update (1 : Fin n → ℚ) ⟨0, hn⟩ ε with he
  have hee : ∀ i, e i = 1 ∨ e i = -1 := by
    intro i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi; simpa [he] using hε
    · left; simp [he, Function.update_of_ne hi]
  have hsq : Matrix.diagonal e * Matrix.diagonal e = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i
    rcases hee i with h | h <;> simp [h]
  have hcl : ∀ y ∈ (intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)), Matrix.diagonal e *ᵥ y ∈ intVec := by
    intro y hy i
    rw [mulVec_diagonal]
    have := hy i
    rcases hee i with h | h <;> rw [h]
    · simpa using this
    · simpa using (algebraMap (𝓞 ℚ) ℚ).range.neg_mem this
  refine ⟨⟨Matrix.diagonal e, Matrix.diagonal e, hsq, hsq⟩, rfl, ?_, ?_⟩
  · ext y
    rw [mem_glImage]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hcl z hz
    · intro hy
      refine ⟨Matrix.diagonal e *ᵥ y, hcl y hy, ?_⟩
      show Matrix.diagonal e *ᵥ (Matrix.diagonal e *ᵥ y) = y
      rw [mulVec_mulVec, hsq, one_mulVec]
  · show (Matrix.diagonal e).det = ε
    rw [det_diagonal, he]
    simp [Finset.prod_update_of_mem]

theorem det_casselsDiag {p : ℕ} (hn : 2 ≤ n) (hp : p ≠ 0) : (casselsSubstDiag n p).det = 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  unfold casselsSubstDiag
  rw [det_diagonal]
  obtain ⟨z0, hz0⟩ : ∃ z0 : Fin n, z0.1 = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨zl, hzl⟩ : ∃ zl : Fin n, zl.1 = n - 1 := ⟨⟨n - 1, by omega⟩, rfl⟩
  have hne : z0 ≠ zl := fun h => by have := congrArg Fin.val h; omega
  rw [Finset.prod_eq_mul z0 zl hne]
  · simp [hz0, hzl, show n - 1 ≠ 0 by omega, hp0]
  · intro c _ hc
    have h1 : c.1 ≠ 0 := fun h => hc.1 (Fin.ext (by omega))
    have h2 : c.1 ≠ n - 1 := fun h => hc.2 (Fin.ext (by omega))
    simp [h1, h2]
  · simp
  · simp

/-! ### The chain relation -/

section Chain

open Tamagawa.SiegelSpace

variable (f : QuadForm ℤ n)

/-- Admissible forms of the chain: classically integral, with the same Hessian determinant as `f`. -/
def GoodForm (F : QuadForm ℤ n) : Prop := IsClassicallyIntegral F ∧ F.hessian.det = f.hessian.det

/-- One step of Theorem 6.1: (i) a proper `ℤ`-equivalence, or (ii) the substitution at a prime `p`. -/
def ChainStep (F G : QuadForm ℤ n) : Prop :=
  (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, G.eval x = F.eval (U *ᵥ x)) ∨
    ∃ p : ℕ, p.Prime ∧ ∀ x : Fin n → ℚ, (G.map (Int.castRingHom ℚ)).evalIn ℚ x =
      (F.map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x)

/-- The relation whose reflexive-transitive closure is the chain of Theorem 6.1. -/
def ChainRel (F G : QuadForm ℤ n) : Prop := GoodForm f F ∧ GoodForm f G ∧ ChainStep F G

/-- A good lattice: classically integral for `f` and of index `1`. -/
def LatGood (L : Lat ℚ n) : Prop := LatCI (f.map (Int.castRingHom ℚ)) L.1 ∧ latIndex L = 1

variable {f}

theorem abs_det_of_latGood {L : Lat ℚ n} (hL : LatGood f L) {γ : GL (Fin n) ℚ} (h : latOf γ = L.1) :
    |(γ : Matrix (Fin n) (Fin n) ℚ).det| = 1 := by
  have h1 := latIndex_latOf γ
  have e : (⟨latOf γ, latOf_isLattice γ⟩ : Lat ℚ n) = L := Subtype.ext h
  rw [e, hL.2] at h1
  have h2 : (|(γ : Matrix (Fin n) (Fin n) ℚ).det|⁻¹ : ℚ) = 1 := by exact_mod_cast h1.symm
  exact inv_eq_one.mp h2

theorem exists_good_formOf {L : Lat ℚ n} (hL : LatGood f L) {γ : GL (Fin n) ℚ} (h : latOf γ = L.1) :
    ∃ F : QuadForm ℤ n, FormOf f γ F ∧ GoodForm f F := by
  obtain ⟨F, hF, hFc⟩ := exists_formOf f γ (h ▸ hL.1)
  exact ⟨F, hF, hFc, formOf_hessian_det f hF (abs_det_of_latGood hL h)⟩

theorem chainRel_of_latOf_eq {γ δ : GL (Fin n) ℚ}
    (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det) (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det)
    (h : latOf γ = latOf δ) {F G : QuadForm ℤ n} (hF : FormOf f γ F) (hG : FormOf f δ G)
    (hFg : GoodForm f F) (hGg : GoodForm f G) : ChainRel f F G := by
  obtain ⟨U, hU1, hU⟩ := exists_unimod_of_latOf_eq hδ hγ h.symm
  exact ⟨hFg, hGg, Or.inl ⟨U, hU1, eval_eq_of_latOf_eq f hG hF hU⟩⟩

/-- **Step (ii) for a prime-index pair of good lattices:** the forms of `L` and `M` (`I(M, L) = p`) are joined by
(i), (ii), (i) (Theorem 5.1, Corollary, gives the bases). -/
theorem reach_prime (hn : 2 ≤ n) {L M : Lat ℚ n} (hL : LatGood f L) (hM : LatGood f M) {p : ℕ}
    (hp : p.Prime) (hI : casselsI M L = p) {γ δ : GL (Fin n) ℚ}
    (hγ : 0 < (γ : Matrix (Fin n) (Fin n) ℚ).det) (hδ : 0 < (δ : Matrix (Fin n) (Fin n) ℚ).det)
    (hγL : latOf γ = L.1) (hδM : latOf δ = M.1) {F G : QuadForm ℤ n}
    (hF : FormOf f γ F) (hFg : GoodForm f F) (hG : FormOf f δ G) (hGg : GoodForm f G) :
    Relation.ReflTransGen (ChainRel f) F G := by
  have hlat : latIndex M = latIndex L := hM.2.trans hL.2.symm
  obtain ⟨b, hli, hMs, hLs⟩ := exists_basis_of_casselsI_prime hn hlat hp hI
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0 : 0 < n := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  -- the matrices
  set B : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => b j i with hB
  have hBcol : ∀ j, B *ᵥ Pi.single j (1 : ℚ) = b j := by
    intro j; ext i; simp [B, mulVec, dotProduct, Pi.single_apply]
  have hBu : IsUnit B.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    convert hli using 1
    funext j; ext i; rfl
  set t : Fin n → ℚ := fun j => if j.1 = n - 1 then (p : ℚ) else 1 with ht
  set S : Matrix (Fin n) (Fin n) ℚ := casselsSubstDiag n p with hS
  have hSdet : S.det = 1 := det_casselsDiag hn hp.ne_zero
  have htu : IsUnit (Matrix.diagonal t).det := by
    rw [det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by simp only [ht]; split_ifs <;> simp [hp0]
  have h1u : IsUnit (B * Matrix.diagonal t).det := by rw [det_mul]; exact hBu.mul htu
  have h2u : IsUnit (B * Matrix.diagonal t * S).det := by
    rw [det_mul, hSdet]; simpa using h1u
  set γ₁ : GL (Fin n) ℚ := Matrix.nonsingInvUnit _ h1u with hγ₁
  set γ₂ : GL (Fin n) ℚ := Matrix.nonsingInvUnit _ h2u with hγ₂
  have hγ₁v : (γ₁ : Matrix (Fin n) (Fin n) ℚ) = B * Matrix.diagonal t := rfl
  have hγ₂v : (γ₂ : Matrix (Fin n) (Fin n) ℚ) = γ₁.val * S := rfl
  have hLγ₁ : latOf γ₁ = L.1 := by
    rw [latOf_eq_span, hLs, hγ₁v]
    congr 2
    ext j : 1
    rw [cols_mul_diagonal, hBcol]
    simp only [ht]
    split_ifs <;> simp
  have hMγ₂ : latOf γ₂ = M.1 := by
    rw [latOf_eq_span, hMs, hγ₂v, hγ₁v, Matrix.mul_assoc, hS, casselsSubstDiag, diagonal_mul_diagonal]
    congr 2
    ext j : 1
    rw [cols_mul_diagonal, hBcol]
    simp only [ht]
    by_cases h0' : j.1 = 0
    · simp [h0', hn1.symm]
    · by_cases hl : j.1 = n - 1
      · simp [h0', hl, hn1, hp0]
      · simp [h0', hl]
  -- sign adjustment
  have hs0 : (γ₁ : Matrix (Fin n) (Fin n) ℚ).det ≠ 0 := (γ₁.isUnit.map Matrix.detMonoidHom).ne_zero
  obtain ⟨E, hEv, hEstab, hEdet⟩ := exists_signMat hn0
    (if 0 < (γ₁ : Matrix (Fin n) (Fin n) ℚ).det then 1 else -1) (by split_ifs <;> simp)
  have hpos1 : 0 < ((γ₁ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [Units.val_mul, det_mul, hEdet]
    split_ifs with h
    · simpa using h
    · have := lt_of_le_of_ne (not_lt.mp h) hs0
      nlinarith
  have hES : E.val * S = S * E.val := by
    rw [hEv, hS, casselsSubstDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext j; ring
  have hv2 : ((γ₂ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) =
      ((γ₁ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) * S := by
    rw [Units.val_mul, Units.val_mul, hγ₂v, Matrix.mul_assoc, Matrix.mul_assoc, hES]
  have hpos2 : 0 < ((γ₂ * E : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).det := by
    rw [hv2, det_mul, hSdet, mul_one]; exact hpos1
  have hL1 : latOf (γ₁ * E) = L.1 := by
    rw [← hLγ₁, latOf, latOf, glImage_mul, hEstab]
  have hM2 : latOf (γ₂ * E) = M.1 := by
    rw [← hMγ₂, latOf, latOf, glImage_mul, hEstab]
  obtain ⟨F', hF', hF'g⟩ := exists_good_formOf hL hL1
  obtain ⟨G', hG', hG'g⟩ := exists_good_formOf hM hM2
  have R1 : ChainRel f F F' := chainRel_of_latOf_eq hγ hpos1 (by rw [hγL, hL1]) hF hF' hFg hF'g
  have R3 : ChainRel f G' G := chainRel_of_latOf_eq hpos2 hδ (by rw [hδM, hM2]) hG' hG hG'g hGg
  have R2 : ChainRel f F' G' := by
    refine ⟨hF'g, hG'g, Or.inr ⟨p, hp, fun x => ?_⟩⟩
    rw [map_evalIn_rat, map_evalIn_rat, hG', hF', casselsSubst_eq, mulVec_mulVec, ← hv2]
  exact ((Relation.ReflTransGen.single R1).tail R2).tail R3

end Chain

/-! ### Assembly of Theorem 6.1 -/

section Assembly

open Tamagawa.SiegelSpace

theorem two_dvd_hessian {F : QuadForm ℤ n} (hF : IsClassicallyIntegral F) (i j : Fin n) :
    (2 : ℤ) ∣ F.hessian i j := by
  rw [isClassicallyIntegral_iff] at hF
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
  rcases lt_trichotomy i j with h | h | h
  · rw [F.upper h, add_zero]; exact even_iff_two_dvd.mp (hF i j h)
  · subst h; exact ⟨F.coeff i i, by ring⟩
  · rw [F.upper h, zero_add]; exact even_iff_two_dvd.mp (hF j i h)

theorem latCI_latOf (f : QuadForm ℤ n) {γ : GL (Fin n) ℚ} {F : QuadForm ℤ n} (hF : FormOf f γ F)
    (hFc : IsClassicallyIntegral F) : LatCI (f.map (Int.castRingHom ℚ)) (latOf γ) := by
  have hH := Siegel.Kneser.hessian_eq_conj hF
  have key : ∀ y y' : Fin n → ℚ, Siegel.Kneser.bQ f (γ.val *ᵥ y) (γ.val *ᵥ y') =
      y ⬝ᵥ (F.hessian.map (algebraMap ℤ ℚ) *ᵥ y') := by
    intro y y'
    unfold Siegel.Kneser.bQ
    rw [hH, ← Siegel.Kneser.dotProduct_conj]
  have toInt : ∀ x ∈ latOf γ, ∃ c : Fin n → ℤ, x = γ.val *ᵥ Siegel.Kneser.cv c := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := mem_intVec_iff_exists.mp hz
    refine ⟨fun i => Rat.ringOfIntegersEquiv (a i), ?_⟩
    have : intCoe a = Siegel.Kneser.cv (fun i => Rat.ringOfIntegersEquiv (a i)) := by
      ext i
      simp [Siegel.Kneser.cv, intCoe, Rat.ringOfIntegersEquiv_apply_coe]
    show γ.val *ᵥ intCoe a = _
    rw [this]
  intro x hx y hy
  obtain ⟨c, rfl⟩ := toInt x hx
  obtain ⟨d, rfl⟩ := toInt y hy
  rw [qbil_map_int, key]
  obtain ⟨z, hz⟩ : (2 : ℤ) ∣ c ⬝ᵥ (F.hessian *ᵥ d) := by
    unfold dotProduct mulVec dotProduct
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (two_dvd_hessian hFc i j) _
  refine ⟨z, ?_⟩
  have : Siegel.Kneser.cv c ⬝ᵥ (F.hessian.map (algebraMap ℤ ℚ) *ᵥ Siegel.Kneser.cv d) =
      ((c ⬝ᵥ (F.hessian *ᵥ d) : ℤ) : ℚ) := by
    simp [dotProduct, mulVec, Siegel.Kneser.cv]
  rw [this, hz]; push_cast; ring

theorem exists_fin_of_reflTransGen {α : Type*} (r : α → α → Prop) (P : α → Prop)
    (hP : ∀ a b, r a b → P b) {a b : α} (h : Relation.ReflTransGen r a b) (ha : P a) :
    ∃ (V : ℕ) (g : Fin (V + 1) → α), g 0 = a ∧ g (Fin.last V) = b ∧ (∀ v, P (g v)) ∧
      ∀ v : Fin V, r (g v.castSucc) (g v.succ) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun _ => ha, fun v => v.elim0⟩
  | @tail b' c' _ hbc ih =>
    obtain ⟨V, g, h0, hl, hPg, hr⟩ := ih
    refine ⟨V + 1, Fin.snoc g c', ?_, ?_, ?_, ?_⟩
    · rw [← Fin.castSucc_zero, Fin.snoc_castSucc, h0]
    · simp
    · intro v
      refine Fin.lastCases ?_ (fun u => ?_) v
      · simpa using hP _ _ hbc
      · rw [Fin.snoc_castSucc]; exact hPg u
    · intro v
      refine Fin.lastCases ?_ (fun u => ?_) v
      · simpa [hl] using hbc
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hr u

/-- A rational equivalence of the forms can be taken of determinant $1$ (compose with a rational reflection). -/
theorem exists_pos_det_one (f₁ f₂ : QuadForm ℤ n) (hn : 1 ≤ n) (hd : f₁.hessian.det = f₂.hessian.det)
    (hd0 : f₁.hessian.det ≠ 0)
    (hQ : Siegel.IsometricGL (f₁.map (Int.castRingHom ℚ)) (f₂.map (Int.castRingHom ℚ))) :
    ∃ g : GL (Fin n) ℚ, (g : Matrix (Fin n) (Fin n) ℚ).det = 1 ∧ FormOf f₁ g f₂ := by
  obtain ⟨g, hg⟩ := hQ
  have hF : FormOf f₁ g f₂ := fun x => by
    rw [← map_evalIn_rat f₂, ← map_evalIn_rat f₁]; exact (hg x).symm
  have hH := Siegel.Kneser.hessian_eq_conj hF
  have h1 := congrArg Matrix.det hH
  rw [det_mul, det_mul, det_transpose, Siegel.Kneser.det_map_eq, Siegel.Kneser.det_map_eq] at h1
  rw [← hd] at h1
  have hd0' : (algebraMap ℤ ℚ f₁.hessian.det) ≠ 0 := by
    simpa using hd0
  have hsq : (g : Matrix (Fin n) (Fin n) ℚ).det * (g : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    apply mul_right_cancel₀ hd0'
    linear_combination -h1
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact ⟨g, h, hF⟩
  · -- compose with a rational reflection
    set Q := f₁.map (Int.castRingHom ℚ) with hQdef
    have hnd : Q.Nondegenerate := by
      unfold QuadForm.Nondegenerate
      rw [hQdef, Siegel.Kneser.hessian_map, Siegel.Kneser.det_map_eq]
      simpa using hd0
    obtain ⟨x, hx⟩ := ArchTest.exists_evalIn_ne_zero hnd hn
    refine ⟨((symm Q ℚ x : orthGroup Q ℚ) : GL (Fin n) ℚ) * g, ?_, fun y => ?_⟩
    · rw [Units.val_mul, det_mul, symm_det Q ℚ hx, h]; norm_num
    · rw [hF y, Units.val_mul, ← mulVec_mulVec]
      have := evalIn_mulVec_of_mem Q (symm Q ℚ x).2 (g.val *ᵥ y)
      simp only [hQdef, map_evalIn_rat] at this
      exact this.symm

/-- The core of Theorem 6.1: the forms are related by the reflexive-transitive closure of the chain relation. -/
theorem exists_chain_core (hn : 2 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (hQ : Siegel.IsometricGL (f₁.map (Int.castRingHom ℚ)) (f₂.map (Int.castRingHom ℚ))) :
    Relation.ReflTransGen (ChainRel f₁) f₁ f₂ := by
  have hn0 : 0 < n := by omega
  obtain ⟨g, hg1, hFg⟩ := exists_pos_det_one f₁ f₂ (by omega) hd hd0 hQ
  set Q := f₁.map (Int.castRingHom ℚ) with hQdef
  have hF1 : FormOf f₁ 1 f₁ := fun x => by simp
  have hΛCI : LatCI Q (latOf 1) := latCI_latOf f₁ hF1 h₁
  have hΓCI : LatCI Q (latOf g) := latCI_latOf f₁ hFg h₂
  have hΛ1 : latIndex (⟨latOf 1, latOf_isLattice 1⟩ : Lat ℚ n) = 1 := by
    have := latIndex_latOf (1 : GL (Fin n) ℚ); simpa using this
  have hΓ1 : latIndex (⟨latOf g, latOf_isLattice g⟩ : Lat ℚ n) = 1 := by
    have := latIndex_latOf g; rw [hg1] at this; simpa using this
  obtain ⟨J, Λs, h0, hlast, hlatΛ, hprime, -, hint⟩ := exists_casselsI_chain Q
    (L := ⟨latOf 1, latOf_isLattice 1⟩) (M := ⟨latOf g, latOf_isLattice g⟩) (hΛ1.trans hΓ1.symm)
    Set.univ (fun _ _ => Set.mem_univ _)
    (fun v _ => (latCI_iff_loc Q _).mp hΛCI v) (fun v _ => (latCI_iff_loc Q _).mp hΓCI v)
  have hgood : ∀ j, LatGood f₁ (Λs j) := fun j =>
    ⟨(latCI_iff_loc Q _).mpr (fun v => hint j v (Set.mem_univ _)), (hlatΛ j).trans hΛ1⟩
  have key : ∀ k (hk : k ≤ J) (γ : GL (Fin n) ℚ) (F : QuadForm ℤ n),
      0 < (γ : Matrix (Fin n) (Fin n) ℚ).det → latOf γ = (Λs ⟨k, by omega⟩).1 → FormOf f₁ γ F →
      GoodForm f₁ F → Relation.ReflTransGen (ChainRel f₁) f₁ F := by
    intro k
    induction k with
    | zero =>
      intro _ γ F hγ hL hF hFg
      have e : (⟨0, by omega⟩ : Fin (J + 1)) = 0 := rfl
      rw [e, h0] at hL
      exact Relation.ReflTransGen.single
        (chainRel_of_latOf_eq (γ := 1) (by simp) hγ hL.symm hF1 hF ⟨h₁, rfl⟩ hFg)
    | succ k ih =>
      intro hk γ F hγ hL hF hFg
      set v : Fin J := ⟨k, by omega⟩ with hv
      have hv2 : (⟨k + 1, by omega⟩ : Fin (J + 1)) = v.succ := rfl
      rw [hv2] at hL
      obtain ⟨γk, hγk, hLk⟩ := exists_latOf_pos_rat hn0 (Λs v.castSucc)
      obtain ⟨Fk, hFk, hFkg⟩ := exists_good_formOf (hgood v.castSucc) hLk.symm
      have r1 := ih (by omega) γk Fk hγk hLk.symm hFk hFkg
      have hI : casselsI (Λs v.succ) (Λs v.castSucc) = casselsI (Λs v.castSucc) (Λs v.succ) :=
        casselsI_comm (((hgood v.succ).2).trans (hgood v.castSucc).2.symm)
      have r2 := reach_prime hn (hgood v.castSucc) (hgood v.succ) (hprime v) hI hγk hγ hLk.symm hL
        hFk hFkg hF hFg
      exact r1.trans r2
  exact key J le_rfl g f₂ (by rw [hg1]; exact one_pos) (congrArg Subtype.val hlast.symm) hFg ⟨h₂, hd.symm⟩

end Assembly

/-- **Cassels, Theorem 6.1** (Ch. 11, p. 224): *let $f_1, f_2$ be two classically integral quadratic forms over
$\mathbb Z$ in $n \ge 2$ variables and with the same determinant $d \ne 0$. Suppose that they are rationally
equivalent. Then there is a sequence of quadratic forms $g_v$, all classically integral and of determinant $d$, with
$g_1 = f_1$, $g_V = f_2$, such that for each $v < V$ either (i) $g_{v+1}$ is properly $\mathbb Z$-equivalent to $g_v$,
or (ii) there is a prime $p$ such that $g_{v+1}(x) = g_v(px_1, x_2, \dots, x_{n-1}, p^{-1}x_n)$.* 0-based, (ii)
reconstructed (module docstring). -/
@[kb "cassels1978" "Ch. 11, Thm. 6.1, p. 224 ((ii) reconstructed; 0-based)"]
theorem exists_chain_of_isometricGL_rat (hn : 2 ≤ n) (f₁ f₂ : QuadForm ℤ n)
    (h₁ : IsClassicallyIntegral f₁) (h₂ : IsClassicallyIntegral f₂)
    (hd : f₁.hessian.det = f₂.hessian.det) (hd0 : f₁.hessian.det ≠ 0)
    (hQ : Siegel.IsometricGL (f₁.map (Int.castRingHom ℚ)) (f₂.map (Int.castRingHom ℚ))) :
    ∃ (V : ℕ) (g : Fin (V + 1) → QuadForm ℤ n), g 0 = f₁ ∧ g (Fin.last V) = f₂ ∧
      (∀ v, IsClassicallyIntegral (g v) ∧ (g v).hessian.det = f₁.hessian.det) ∧
      ∀ v : Fin V,
        (∃ U : Matrix (Fin n) (Fin n) ℤ, U.det = 1 ∧ ∀ x, (g v.succ).eval x = (g v.castSucc).eval (U *ᵥ x)) ∨
        ∃ p : ℕ, p.Prime ∧ ∀ x : Fin n → ℚ, ((g v.succ).map (Int.castRingHom ℚ)).evalIn ℚ x =
          ((g v.castSucc).map (Int.castRingHom ℚ)).evalIn ℚ (casselsSubst p x) := by
  have hrt := exists_chain_core hn f₁ f₂ h₁ h₂ hd hd0 hQ
  obtain ⟨V, g, h0, hl, hP, hr⟩ := exists_fin_of_reflTransGen (ChainRel f₁) (GoodForm f₁)
    (fun a b h => h.2.1) hrt ⟨h₁, rfl⟩
  exact ⟨V, g, h0, hl, fun v => hP v, fun v => (hr v).2.2⟩

end QuadFormsKB.Lattices
