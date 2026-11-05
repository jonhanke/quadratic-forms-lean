/-
# Conway–Sloane, Ch. 15, §3.5: local lemmas for the "only if" direction of Estes–Pall

Helper for `Section3EstesPallOnlyIf.lean` (Conway–Sloane, Ch. 15, §3.5, p. 366, citing Estes–Pall 1973).

**Layer.** Over $\mathbb Q$ at a finite prime $v$ (the completion $\mathbb Q_v$ with the completion's $\mathbb Q$-algebra
structure, as in `Section3EstesPallIf.lean`); a binary integral form $f = [a, b, c]$ with discriminant
$D = b^2 - 4ac \ne 0$, the rational form $Q$ = `formF (up f)` on $\mathbb Q_v^2$ with Hessian
$H = \begin{pmatrix} 2a & b \\ b & 2c\end{pmatrix}$, the standard lattice $\mathbb Z_v^2$ (`std v`) and its isometries
`stdStab`.

**Proves**
* `integral_of_mem_stdStab`, `locAct_std_of_integral`: an integral matrix of unit determinant maps $\mathbb Z_v^2$ onto
  itself, and conversely;
* `exists_sq_eq_stdStab` (**integral square roots**): if $v \nmid 2D$ and $\sigma \in O^+(\mathbb Z_v^2)$ has
  $\theta(\sigma) = 1$, then $\sigma = \kappa^2$ with $\kappa \in O^+(\mathbb Z_v^2)$. (Since
  $(2 + \operatorname{tr}\sigma) + (2 - \operatorname{tr}\sigma) = 4$ is a unit, one of the square roots
  $(1 + \sigma)/c$, $(1 - \sigma)J/c'$ of `Section3BinaryRotations.lean` has $c$ a unit.)
* `sq_integral_of_integral` (**the squaring lemma**): for the form $f' = [a, B, Cw^4]$ with $\gcd(a, B) = 1$,
  $\Gamma = \operatorname{diag}(w, w^{-1})$ and a rotation $\kappa = M(s, t)$ of $f'$: if $\Gamma^{-1}\kappa$ is
  integral then so is $\Gamma^{-2}\kappa^2$. In lattice terms: $\kappa\mathbb Z_v^2 = \Gamma\mathbb Z_v^2$ implies
  $\kappa^2\mathbb Z_v^2 = \Gamma^2\mathbb Z_v^2$ (`sq_locAct_eq`). *Proof:* with $E = \Gamma^{-1}\kappa$ and
  $u = 2tw = xE_{10} + y(E_{11} - w^2E_{00})$ ($xa + yB = 1$), the entries of $\Gamma^{-2}\kappa^2$ are
  $E_{00}^2 - aCu^2$, $-Cu(E_{11} + w^2E_{00})$, $au(E_{11} + w^2E_{00})$ and $E_{11}^2 - aCw^4u^2$.
-/
import QuadFormsKB.Literature.ConwaySloane.Section3BinaryRotations
import QuadFormsKB.Literature.ConwaySloane.Section3EstesPallIf
import QuadFormsKB.Literature.ConwaySloane.Section9EvenUnimodular
import QuadFormsKB.Tamagawa.FrameLatChecks

open NumberField Matrix IsDedekindDomain WithZero

noncomputable section

attribute [local instance 2000] HeightOneSpectrum.instAlgebraAdicCompletion

namespace QuadFormsKB.ConwaySloane.EstesPall

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa.RatBridge EvenUnimodular

set_option linter.unusedSectionVars false

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "Fv" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-! ### Integral matrices and the standard lattice -/

/-- An isometry of $\mathbb Z_v^n$ has integral entries. -/
theorem integral_of_locAct_std {n : ℕ} (g : GL (Fin n) Fv) (hg : locAct v g (std v) = std v) :
    ∀ i j, Valued.v (g.val i j) ≤ 1 := by
  intro i j
  have hmem : g.val *ᵥ (Pi.single j (1 : Fv)) ∈ std v := by
    rw [← hg]; exact mem_locAct.mpr ⟨_, single_one_mem_std v j, rfl⟩
  have := mem_std_iff.mp hmem i
  simpa [mulVec_single] using this

/-- An integral matrix of unit determinant maps $\mathbb Z_v^n$ onto itself. -/
theorem locAct_std_of_integral {n : ℕ} (g : GL (Fin n) Fv) (hg : ∀ i j, Valued.v (g.val i j) ≤ 1)
    (hdet : Valued.v g.val.det = 1) : locAct v g (std v) = std v := by
  refine Tamagawa.FramesLat.locAct_std_eq_of_le_unit v g (fun y hy => ?_) hdet
  obtain ⟨x, hx, rfl⟩ := mem_locAct.mp hy
  exact mem_std_iff.mpr (mulVec_integral _ _ hg (mem_std_iff.mp hx))

theorem valued_eq_one_of_sq {c : Fv} (h : Valued.v c ^ 2 = 1) : Valued.v c = 1 := by
  rcases lt_trichotomy (Valued.v c) 1 with hlt | heq | hgt
  · exfalso
    have : Valued.v c ^ 2 < 1 := pow_lt_one₀ zero_le hlt (by norm_num)
    rw [h] at this; exact lt_irrefl _ this
  · exact heq
  · exfalso
    have : 1 < Valued.v c ^ 2 := one_lt_pow₀ hgt (by norm_num)
    rw [h] at this; exact lt_irrefl _ this

/-! ### Integral square roots -/

section Roots

variable (f : BinQF)

local notation "Qf" => HilbertModular.formF (up f)
set_option quotPrecheck false in
local notation "Hf" => (HilbertModular.formF (up f)).hessian.map (algebraMap ℚ Fv)

theorem hessF_apply (i j : Fin 2) : Hf i j = ((f.hessian i j : ℤ) : Fv) := by
  rw [formF_up, QuadForm.hessian_map]
  simp [Matrix.map_apply]

theorem hessF_integral (i j : Fin 2) : Valued.v (Hf i j) ≤ 1 := by
  rw [hessF_apply]; exact valued_intCast_le_one _

theorem hessF_det : Matrix.det Hf = ((-f.disc : ℤ) : Fv) := by
  have : Hf = f.hessian.map (Int.cast : ℤ → Fv) := by ext i j; rw [hessF_apply]; rfl
  rw [this, ← hessian_det_binQF]
  exact (RingHom.map_det (Int.castRingHom Fv) f.hessian).symm

theorem rotJ_integral (i j : Fin 2) : Valued.v (rotJ Hf i j) ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp only [rotJ, of_apply, cons_val', cons_val_zero, cons_val_one,
    empty_val', cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Valuation.map_neg] <;> exact hessF_integral f _ _

/-- **Integral square roots of spinor-kernel rotations** (at $v \nmid 2D$): if $\sigma \in O^+(\mathbb Z_v^2)$ and
$\theta(\sigma) = 1$, then $\sigma = \kappa^2$ with $\kappa \in O^+(\mathbb Z_v^2)$. -/
theorem exists_sq_eq_stdStab (hQ : (Qf).Nondegenerate) (h2D : ((2 * f.disc : ℤ) : 𝓞 ℚ) ∉ v.asIdeal)
    (σ : orthGroup (Qf) Fv) (hσL : σ ∈ stdStab (Qf) v) (hσ : σ ∈ Tamagawa.soSub (Qf) Fv)
    (hθ : spinorNorm (Qf) Fv σ = 1) :
    ∃ κ : orthGroup (Qf) Fv, κ ∈ stdStab (Qf) v ∧ κ ∈ Tamagawa.soSub (Qf) Fv ∧ κ * κ = σ := by
  have h2 : ((2 : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => h2D (by push_cast; exact Ideal.mul_mem_right _ _ (by simpa using h))
  have hD : ((f.disc : ℤ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => h2D (by push_cast; exact Ideal.mul_mem_left _ _ h)
  have hv2 : Valued.v (2 : Fv) = 1 := by simpa using valued_intCast_eq_one v h2
  have hvD : Valued.v (Matrix.det Hf) = 1 := by
    rw [hessF_det, Int.cast_neg, Valuation.map_neg]; exact valued_intCast_eq_one v hD
  have hσi := integral_of_locAct_std (σ : GL (Fin 2) Fv) hσL
  set T := (σ : GL (Fin 2) Fv).val 0 0 + (σ : GL (Fin 2) Fv).val 1 1 with hT
  have hTi : Valued.v T ≤ 1 := Valuation.map_add_le _ (hσi 0 0) (hσi 1 1)
  have h4 : Valued.v ((2 + T) + (2 - T)) = 1 := by
    rw [show (2 + T) + (2 - T) = 2 * 2 by ring, map_mul, hv2, one_mul]
  have hXY : Valued.v (2 + T) = 1 ∨ Valued.v (2 - T) = 1 := by
    have hX1 : Valued.v (2 + T) ≤ 1 := Valuation.map_add_le _ (by rw [hv2]) hTi
    have hY1 : Valued.v (2 - T) ≤ 1 := Valuation.map_sub_le _ (by rw [hv2]) hTi
    by_contra hne
    push_neg at hne
    have := Valuation.map_add_lt Valued.v (lt_of_le_of_ne hX1 hne.1) (lt_of_le_of_ne hY1 hne.2)
    rw [h4] at this; exact lt_irrefl _ this
  have hdetκ : ∀ κ : orthGroup (Qf) Fv, κ ∈ Tamagawa.soSub (Qf) Fv → Valued.v (κ : GL (Fin 2) Fv).val.det = 1 :=
    fun κ hκ => by rw [show (κ : GL (Fin 2) Fv).val.det = 1 from hκ, map_one]
  rcases hXY with hX | hY
  · have hX0 : 2 + T ≠ 0 := fun h => by rw [h, map_zero] at hX; exact zero_ne_one hX
    obtain ⟨c, hc, κ, hκ, hκσ, hκv⟩ := exists_sq_eq_plus (Qf) Fv hQ σ hσ hθ hX0
    have hcv : Valued.v c = 1 := valued_eq_one_of_sq (by rw [← map_pow, hc, hX])
    have hci : Valued.v c⁻¹ = 1 := by rw [map_inv₀, hcv, inv_one]
    refine ⟨κ, locAct_std_of_integral _ (fun i j => ?_) (hdetκ κ hκ), hκ, hκσ⟩
    rw [hκv, Matrix.smul_apply, smul_eq_mul, map_mul, hci, one_mul, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hσi i j)
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_ne hij]
  · have hY0 : 2 - T ≠ 0 := fun h => by rw [h, map_zero] at hY; exact zero_ne_one hY
    obtain ⟨c, hc, κ, hκ, hκσ, hκv⟩ := exists_sq_eq_minus (Qf) Fv hQ σ hσ hθ hY0
    have hcv : Valued.v c = 1 := valued_eq_one_of_sq (by rw [← map_pow, hc, map_mul, hY, hvD, one_mul])
    have hci : Valued.v c⁻¹ = 1 := by rw [map_inv₀, hcv, inv_one]
    refine ⟨κ, locAct_std_of_integral _ (fun i j => ?_) (hdetκ κ hκ), hκ, hκσ⟩
    rw [hκv, Matrix.smul_apply, smul_eq_mul, map_mul, hci, one_mul]
    refine mul_integral _ _ (fun i j => ?_) (rotJ_integral f) i j
    rw [Matrix.sub_apply]
    refine Valuation.map_sub_le _ ?_ (hσi i j)
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_ne hij]

end Roots

/-! ### The squaring lemma -/

/-- The Hessian $\begin{pmatrix} 2a & B \\ B & 2Cw^4\end{pmatrix}$ of $f' = [a, B, Cw^4]$ over $\mathbb Q_v$. -/
def hessW (a B C w : ℤ) : Matrix (Fin 2) (Fin 2) Fv := !![2 * (a : Fv), B; B, 2 * C * (w : Fv) ^ 4]

/-- $\operatorname{diag}(w^{-1}, w)$ (for $\Gamma = \operatorname{diag}(w, w^{-1})$ this is $\Gamma^{-1}$). -/
def gamInv (w : Fv) : Matrix (Fin 2) (Fin 2) Fv := !![w⁻¹, 0; 0, w]

theorem mem_o_iff (z : Fv) : z ∈ 𝔬 ↔ Valued.v z ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

/-- **The squaring lemma**: for $f' = [a, B, Cw^4]$ with $\gcd(a, B) = 1$ and a matrix $\kappa = M(s, t)$ of the
algebra of $f'$, if $\Gamma^{-1}\kappa$ is integral ($\Gamma = \operatorname{diag}(w, w^{-1})$) then so is
$\Gamma^{-2}\kappa^2$. -/
theorem sq_integral_of_integral {a B C w : ℤ} (hw : (w : Fv) ≠ 0) (hcop : IsCoprime a B) (s t : Fv)
    (hE : ∀ i j, Valued.v ((gamInv (w : Fv) * rotM (hessW a B C w) s t) i j) ≤ 1) :
    ∀ i j, Valued.v ((gamInv ((w : Fv) ^ 2) * (rotM (hessW a B C w) s t * rotM (hessW a B C w) s t) :
      Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1 := by
  obtain ⟨x, y, hxy⟩ := hcop
  have hxy' : (x : Fv) * a + y * B = 1 := by exact_mod_cast hxy
  have hsym : hessW (v := v) a B C w 1 0 = hessW a B C w 0 1 := by simp [hessW]
  set e0 := (w : Fv)⁻¹ * (s - t * B) with he0
  set e1 := (w : Fv) * (t * (2 * a)) with he1
  set e3 := (w : Fv) * (s + t * B) with he3
  have hE' : ∀ i j, (gamInv (w : Fv) * rotM (hessW a B C w) s t) i j ∈ 𝔬 := fun i j => (mem_o_iff _).mpr (hE i j)
  have h0 : e0 ∈ 𝔬 := by
    have := hE' 0 0; simpa [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, he0] using this
  have h1 : e1 ∈ 𝔬 := by
    have := hE' 1 0; simpa [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, he1] using this
  have h3 : e3 ∈ 𝔬 := by
    have := hE' 1 1; simpa [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, he3] using this
  have hwi : (w : Fv) ∈ 𝔬 := intCast_mem _ w
  have hai : (a : Fv) ∈ 𝔬 := intCast_mem _ a
  have hCi : (C : Fv) ∈ 𝔬 := intCast_mem _ C
  set u := (x : Fv) * e1 + y * (e3 - (w : Fv) ^ 2 * e0) with hu
  have hui : u ∈ 𝔬 := add_mem (mul_mem (intCast_mem _ x) h1)
    (mul_mem (intCast_mem _ y) (sub_mem h3 (mul_mem (pow_mem hwi 2) h0)))
  have hu2 : u = 2 * t * w := by
    have e : (w : Fv) ^ 2 * ((w : Fv)⁻¹ * (s - t * B)) = w * (s - t * B) := by field_simp
    rw [hu, he0, he1, he3, e]; linear_combination (2 * t * (w : Fv)) * hxy'
  have hS : e3 + (w : Fv) ^ 2 * e0 ∈ 𝔬 := add_mem h3 (mul_mem (pow_mem hwi 2) h0)
  intro i j
  rw [← mem_o_iff, rotM_mul hsym]
  fin_cases i <;> fin_cases j
  · have e : (gamInv ((w : Fv) ^ 2) * rotM (hessW a B C w) (s * s - t * t * (hessW a B C w).det)
        (s * t + t * s) : Matrix (Fin 2) (Fin 2) Fv) 0 0 = e0 ^ 2 - a * C * u ^ 2 := by
      rw [hu2, he0]; simp [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
      field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue] at e ⊢; rw [e]
    exact sub_mem (pow_mem h0 2) (mul_mem (mul_mem hai hCi) (pow_mem hui 2))
  · have e : (gamInv ((w : Fv) ^ 2) * rotM (hessW a B C w) (s * s - t * t * (hessW a B C w).det)
        (s * t + t * s) : Matrix (Fin 2) (Fin 2) Fv) 0 1 = -(C * u * (e3 + (w : Fv) ^ 2 * e0)) := by
      rw [hu2, he0, he3]; simp [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
      field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e ⊢; rw [e]
    exact neg_mem (mul_mem (mul_mem hCi hui) hS)
  · have e : (gamInv ((w : Fv) ^ 2) * rotM (hessW a B C w) (s * s - t * t * (hessW a B C w).det)
        (s * t + t * s) : Matrix (Fin 2) (Fin 2) Fv) 1 0 = a * u * (e3 + (w : Fv) ^ 2 * e0) := by
      rw [hu2, he0, he3]; simp [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
      field_simp; ring
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at e ⊢; rw [e]
    exact mul_mem (mul_mem hai hui) hS
  · have e : (gamInv ((w : Fv) ^ 2) * rotM (hessW a B C w) (s * s - t * t * (hessW a B C w).det)
        (s * t + t * s) : Matrix (Fin 2) (Fin 2) Fv) 1 1 = e3 ^ 2 - a * C * (w : Fv) ^ 4 * u ^ 2 := by
      rw [hu2, he3]; simp [gamInv, rotM_apply, hessW, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two]
      field_simp; ring
    simp only [Fin.isValue, Fin.mk_one] at e ⊢; rw [e]
    exact sub_mem (pow_mem h3 2) (mul_mem (mul_mem (mul_mem hai hCi) (pow_mem hwi 4)) (pow_mem hui 2))

/-! ### The squaring lemma for lattices -/

/-- $\Gamma = \operatorname{diag}(w, w^{-1})$ as an invertible matrix. -/
def gamGL {L : Type*} [Field L] (w : L) (hw : w ≠ 0) : GL (Fin 2) L :=
  ⟨!![w, 0; 0, w⁻¹], !![w⁻¹, 0; 0, w], by simp [Matrix.one_fin_two, hw], by simp [Matrix.one_fin_two, hw]⟩

theorem gamGL_mul_self {L : Type*} [Field L] (w : L) (hw : w ≠ 0) :
    gamGL w hw * gamGL w hw = gamGL (w ^ 2) (pow_ne_zero 2 hw) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gamGL, Matrix.mul_apply, Fin.sum_univ_two, sq]

theorem hessian_mk_apply (a b c : ℤ) (i j : Fin 2) :
    (BinQF.mk a b c).hessian i j = !![2 * a, b; b, 2 * c] i j := by
  fin_cases i <;> fin_cases j <;> simp [QuadForm.hessian, BinQF.mk, QuadForm.ofUpper] <;> ring

theorem hessF_mk (a B C w : ℤ) :
    (HilbertModular.formF (up (BinQF.mk a B (C * w ^ 4)))).hessian.map (algebraMap ℚ Fv) = hessW a B C w := by
  ext i j
  rw [hessF_apply, hessian_mk_apply]
  fin_cases i <;> fin_cases j <;> simp [hessW] <;> push_cast <;> ring

/-- **The squaring lemma for lattices**: let $f \circ P = f' = [a, B, Cw^4]$ with $P \in \mathrm{SL}_2(\mathbb Z)$,
$\gcd(a, B) = 1$, and let $\kappa$ be a rotation of $(\mathbb Q_v^2, f)$ with $\kappa\mathbb Z_v^2 = P\Gamma\mathbb Z_v^2$,
$\Gamma = \operatorname{diag}(w, w^{-1})$. Then $\kappa^2\mathbb Z_v^2 = P\Gamma^2\mathbb Z_v^2$. -/
theorem sq_locAct_eq (f : BinQF) {a B C w : ℤ} (hw : (w : Fv) ≠ 0) (hcop : IsCoprime a B)
    (hQ' : (HilbertModular.formF (up (BinQF.mk a B (C * w ^ 4)))).Nondegenerate)
    (P : GL (Fin 2) ℤ) (hP : P.val.det = 1)
    (hfP : ∀ x, QuadForm.eval f (P.val *ᵥ x) = QuadForm.eval (BinQF.mk a B (C * w ^ 4)) x)
    (κ : orthGroup (HilbertModular.formF (up f)) Fv) (hκ : κ ∈ Tamagawa.soSub (HilbertModular.formF (up f)) Fv)
    (hL : locAct v (κ : GL (Fin 2) Fv) (std v) =
      locAct v (GeneralLinearGroup.map (Int.castRingHom Fv) P * gamGL (w : Fv) hw) (std v)) :
    locAct v ((κ * κ : orthGroup (HilbertModular.formF (up f)) Fv) : GL (Fin 2) Fv) (std v) =
      locAct v (GeneralLinearGroup.map (Int.castRingHom Fv) P * gamGL ((w : Fv) ^ 2) (pow_ne_zero 2 hw))
        (std v) := by
  set f' := BinQF.mk a B (C * w ^ 4) with hf'
  set Pv := GeneralLinearGroup.map (Int.castRingHom Fv) P with hPv
  have hPval : Pv.val = P.val.map (Int.cast : ℤ → Fv) := rfl
  -- `P` stabilizes `ℤ_v²`
  have hPstd : locAct v Pv (std v) = std v := by
    refine locAct_std_of_integral Pv (fun i j => ?_) ?_
    · rw [hPval, Matrix.map_apply]; exact valued_intCast_le_one _
    · have e : (P.val.map (Int.cast : ℤ → Fv)).det = ((P.val.det : ℤ) : Fv) :=
        (RingHom.map_det (Int.castRingHom Fv) P.val).symm
      rw [hPval, e, hP]; simp
  -- the values of `f'`
  have hval : ∀ y : Fin 2 → Fv, bq f (Pv.val *ᵥ y) = bq f' y := fun y => by
    rw [hPval]; exact bq_mulVec_of_int hfP y
  -- the conjugate `κ'' = P⁻¹κP` is a rotation of `f'`
  set κ'' : GL (Fin 2) Fv := Pv⁻¹ * (κ : GL (Fin 2) Fv) * Pv with hκ''
  have hκo : κ'' ∈ orthGroup (HilbertModular.formF (up f')) Fv := by
    refine mem_orthGroup_of_evalIn _ fun z => ?_
    rw [evalIn_formF_up, evalIn_formF_up, ← hval, ← hval, hκ'', Units.val_mul, Units.val_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, mulVec_inv_mulVec, ← evalIn_formF_up f Fv, ← evalIn_formF_up f Fv]
    exact evalIn_mulVec_of_mem _ κ.2 _
  have hκdet : κ''.val.det = 1 := by
    have e : Pv.val.det * Pv⁻¹.val.det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    rw [hκ'', Units.val_mul, Units.val_mul, det_mul, det_mul, show (κ : GL (Fin 2) Fv).val.det = 1 from hκ, mul_one,
      mul_comm, e]
  obtain ⟨t, ht⟩ := exists_rotM_of_rot _ Fv hQ' ⟨κ'', hκo⟩ hκdet
  rw [hessF_mk] at ht
  set s := ((⟨κ'', hκo⟩ : orthGroup (HilbertModular.formF (up f')) Fv) : GL (Fin 2) Fv).val 0 0 / 2 +
    ((⟨κ'', hκo⟩ : orthGroup (HilbertModular.formF (up f')) Fv) : GL (Fin 2) Fv).val 1 1 / 2 with hs
  have ht' : κ''.val = rotM (hessW a B C w) s t := by rw [hs, ← add_div]; exact ht
  -- the lattice of `κ''`
  have hPinv : locAct v Pv⁻¹ (std v) = std v := (locAct_eq_iff.mp hPstd).symm
  have hκ''L : locAct v κ'' (std v) = locAct v (gamGL (w : Fv) hw) (std v) := by
    rw [hκ'', locAct_mul, locAct_mul, hPstd, hL, ← locAct_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  have hint : ∀ i j, Valued.v ((gamInv (w : Fv) * rotM (hessW a B C w) s t) i j) ≤ 1 := by
    have h1 : locAct v ((gamGL (w : Fv) hw)⁻¹ * κ'') (std v) = std v := by
      rw [locAct_mul, hκ''L, ← locAct_mul, inv_mul_cancel, locAct_one]
    have h1' := integral_of_locAct_std _ h1
    intro i j
    have := h1' i j
    rwa [Units.val_mul, ht'] at this
  have hsq := sq_integral_of_integral hw hcop s t hint
  have h2 : locAct v ((gamGL ((w : Fv) ^ 2) (pow_ne_zero 2 hw))⁻¹ * (κ'' * κ'')) (std v) = std v := by
    refine locAct_std_of_integral _ (fun i j => ?_) ?_
    · rw [Units.val_mul, Units.val_mul, ht']; exact hsq i j
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hκdet]
      have e : ((gamGL ((w : Fv) ^ 2) (pow_ne_zero 2 hw))⁻¹ : GL (Fin 2) Fv).val.det = 1 := by
        show (!![((w : Fv) ^ 2)⁻¹, 0; 0, (w : Fv) ^ 2] : Matrix (Fin 2) (Fin 2) Fv).det = 1
        rw [det_fin_two_of]; field_simp; ring
      rw [e]; simp
  have h3 : locAct v (κ'' * κ'') (std v) = locAct v (gamGL ((w : Fv) ^ 2) (pow_ne_zero 2 hw)) (std v) := by
    rw [locAct_mul] at h2
    rw [locAct_eq_iff.mp h2, inv_inv]
  -- back to `κ`
  have e : ((κ * κ : orthGroup (HilbertModular.formF (up f)) Fv) : GL (Fin 2) Fv) = Pv * (κ'' * κ'') * Pv⁻¹ := by
    rw [hκ'']; simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [e, locAct_mul, locAct_mul, hPinv, h3, ← locAct_mul]

end QuadFormsKB.ConwaySloane.EstesPall
