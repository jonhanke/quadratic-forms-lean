/-
# Hanke 2005, §3: Witt index of a unimodular lattice at a non-dyadic place

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

At a non-dyadic place, a diagonal form $\langle a_0,\dots,a_{m-1}\rangle$ with unit coefficients has Witt index at least
$\lfloor(m-1)/2\rfloor$ over $F_\mathfrak p$ (`wittIndex_diag_units`), so its anisotropic kernel has dimension at most $2$.
*Proof:* a ternary unit form is isotropic (`DVR.isotropicIn_of_isLocalLevel_zero`, O'Meara 92:1b), hence
$\langle a_0,a_1,a_2\rangle\cong\mathbb H\perp\langle-a_0a_1a_2\rangle$ (determinants, `exists_witt_diag`); induct.
-/
import QuadFormsKB.Literature.Hanke2005.WittDiag
import QuadFormsKB.Literature.Hanke2005.LocalTypesAux

open NumberField IsDedekindDomain QuadraticMap QuadraticForm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

namespace SelfDualN

section Generic

variable {K : Type*} [Field K]

/-- Values of a diagonal form over an extension ring. -/
theorem evalIn_diag {R : Type*} [CommRing R] {L : Type*} [CommRing L] [Algebra R L] {n : ℕ}
    (a : Fin n → R) (x : Fin n → L) :
    (QuadForm.diag a).evalIn L x = ∑ i, algebraMap R L (a i) * x i ^ 2 := by
  rw [QuadForm.evalIn_eq_dotProduct]
  simp [QuadForm.diag, dotProduct, Matrix.mulVec, Matrix.diagonal_apply, apply_ite (algebraMap R L),
    Finset.sum_ite_eq]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Hessian of a diagonal form is $\mathrm{diag}(2a_i)$. -/
theorem hessian_diag' {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    (QuadForm.diag a).hessian = Matrix.diagonal fun i => 2 * a i := by
  unfold QuadForm.hessian QuadForm.diag
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_add, two_mul]

/-- The Mathlib form of `QuadForm.diag b` is `weightedSumSquares`. -/
theorem toQF_diag {n : ℕ} (b : Fin n → K) :
    (QuadForm.diag b).toQuadraticForm = weightedSumSquares K b := by
  ext x
  rw [QuadForm.toQuadraticForm_apply, QuadForm.eval, evalIn_diag, weightedSumSquares_apply]
  simp [smul_eq_mul, _root_.sq]

theorem nondeg_diag (h2 : (2 : K) ≠ 0) {n : ℕ} (b : Fin n → K) (hb : ∀ i, b i ≠ 0) :
    (QuadForm.diag b).Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [hessian_diag', Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero h2 (hb i)

theorem radical_wss (h2 : (2 : K) ≠ 0) {n : ℕ} (b : Fin n → K) (hb : ∀ i, b i ≠ 0) :
    (weightedSumSquares K b).radical = ⊥ := by
  rw [← toQF_diag]
  have hnd := QuadForm.nondegenerate_polarBilin_toQuadraticFormIn (K := K) (nondeg_diag h2 b hb)
  have e : (QuadForm.diag b).toQuadraticFormIn K = (QuadForm.diag b).toQuadraticForm := by
    unfold QuadForm.toQuadraticFormIn
    congr 1
  rw [e] at hnd
  exact radical_eq_bot_of_nondegenerate _ hnd

/-- Splitting the variables of a diagonal form. -/
def splitIso (m n : ℕ) (a : Fin (m + n) → K) :
    (weightedSumSquares K a).IsometryEquiv
      ((weightedSumSquares K (fun i => a (Fin.castAdd n i))).prod
        (weightedSumSquares K (fun j => a (Fin.natAdd m j)))) where
  toLinearEquiv := QuadForm.finAddLinearEquiv K m n
  map_app' x := by
    simp [weightedSumSquares_apply, Fin.sum_univ_add, QuadForm.finAddLinearEquiv]

/-- Rescaling a unary form by a square. -/
def scaleIso (u d : K) (hd : d ≠ 0) (a' : Fin 1 → K) (h : a' 0 = d ^ 2 * u) :
    (weightedSumSquares K a').IsometryEquiv (weightedSumSquares K (fun _ : Fin 1 => u)) where
  toLinearEquiv := LinearEquiv.smulOfNeZero K _ d hd
  map_app' x := by
    simp [weightedSumSquares_apply, h]
    ring

/-- A ternary isotropic diagonal form is $\mathbb H\perp\langle -b_0b_1b_2\rangle$ (over a field with $2\ne0$). -/
theorem ternary (h2 : (2 : K) ≠ 0) (b : Fin 3 → K) (hb : ∀ i, b i ≠ 0)
    (hiso : ∃ x : Fin 3 → K, x ≠ 0 ∧ ∑ i, b i * x i ^ 2 = 0) :
    (weightedSumSquares K b).Equivalent
      ((hyperbolicSpace K 1).prod (weightedSumSquares K (fun _ : Fin 1 => -(b 0 * b 1 * b 2)))) := by
  rw [← toQF_diag b]
  have hnd := nondeg_diag h2 b hb
  have hdetQ : (QuadForm.diag b).hessian.det = 2 ^ 3 * (b 0 * b 1 * b 2) := by
    rw [hessian_diag', Matrix.det_diagonal, Fin.prod_univ_three]
    ring
  have key : ∀ a' : Fin 1 → K, (∃ c : K, c ≠ 0 ∧ (QuadForm.diag b).hessian.det =
        c ^ 2 * (-1) ^ 1 * 2 ^ 1 * ∏ i, a' i) →
      (QuadForm.diag b).toQuadraticForm.Equivalent ((hyperbolicSpace K 1).prod (weightedSumSquares K a')) →
      (QuadForm.diag b).toQuadraticForm.Equivalent
        ((hyperbolicSpace K 1).prod (weightedSumSquares K (fun _ : Fin 1 => -(b 0 * b 1 * b 2)))) := by
    rintro a' ⟨c, hc, hdet⟩ hE
    rw [hdetQ, Fin.prod_univ_one] at hdet
    have h3 : a' 0 * c ^ 2 + 4 * (b 0 * b 1 * b 2) = 0 := by
      have h4 : (2 : K) * (a' 0 * c ^ 2 + 4 * (b 0 * b 1 * b 2)) = 0 := by linear_combination hdet
      exact (mul_eq_zero.1 h4).resolve_left h2
    have hP : a' 0 = (2 / c) ^ 2 * (-(b 0 * b 1 * b 2)) := by
      rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hc)]
      linear_combination h3
    exact hE.trans ⟨(QuadraticMap.IsometryEquiv.refl _).prod
      (scaleIso _ (2 / c) (div_ne_zero h2 hc) a' hP)⟩
  obtain ⟨hle, a, hanis, ⟨c, hc, hdet⟩, hE⟩ := exists_witt_diag_aux h2 (QuadForm.diag b) hnd
  obtain ⟨x, hx0, hx⟩ := hiso
  generalize hw : wittIndex (QuadForm.diag b).toQuadraticForm = w at *
  have hw1 : w = 1 := by
    rcases (by omega : w = 0 ∨ w = 1) with h0 | h1
    · exfalso
      subst h0
      let e' := hE.some.trans (Witt.hyperbolicSpaceZeroProd _)
      have hm := e'.map_app x
      simp only [toQF_diag, weightedSumSquares_apply, smul_eq_mul] at hm
      have hx' : ∑ i, b i * (x i * x i) = 0 := by simpa [_root_.sq] using hx
      rw [hx'] at hm
      have := hanis (e' x) (by simpa [_root_.sq] using hm)
      exact hx0 (e'.injective (this.trans (map_zero e').symm))
    · exact h1
  subst hw1
  exact key a ⟨c, hc, hdet⟩ hE

end Generic

theorem map_diag_toQF {m : ℕ} (a : Fin m → 𝔬) :
    ((QuadForm.diag a).map (algebraMap 𝔬 Fv)).toQuadraticForm =
      weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a i)) := by
  have : (QuadForm.diag a).map (algebraMap 𝔬 Fv) = QuadForm.diag (fun i => algebraMap 𝔬 Fv (a i)) := by
    unfold QuadForm.map QuadForm.diag
    congr 1
    exact Matrix.diagonal_map (map_zero _)
  rw [this, toQF_diag]

theorem two_ne_zero_Fv : (2 : Fv) ≠ 0 := by
  have := (map_ne_zero_iff (algebraMap 𝔬 Fv) (IsFractionRing.injective 𝔬 Fv)).2 (NF.two_ne_zero' v)
  simpa using this

theorem ne_zero_Fv {x : 𝔬} (hx : IsUnit x) : algebraMap 𝔬 Fv x ≠ 0 :=
  (map_ne_zero_iff (algebraMap 𝔬 Fv) (IsFractionRing.injective 𝔬 Fv)).2 hx.ne_zero

/-- A ternary unit form is isotropic over $F_\mathfrak p$ (level $0$, `DVR.isotropicIn_of_isLocalLevel_zero`). -/
theorem isotropic_three (a : Fin 3 → 𝔬) (ha : ∀ i, IsUnit (a i)) (h2 : IsUnit (2 : 𝔬)) :
    ∃ x : Fin 3 → Fv, x ≠ 0 ∧ ∑ i, algebraMap 𝔬 Fv (a i) * x i ^ 2 = 0 := by
  have hdet : IsUnit (QuadForm.diag a).hessian.det := by
    rw [hessian_diag', Matrix.det_diagonal, Fin.prod_univ_three]
    exact (h2.mul (ha 0)).mul (h2.mul (ha 1)) |>.mul (h2.mul (ha 2))
  have hL := isLocalLevel_zero_of_isUnit_det (QuadForm.diag a) (NF.π v) hdet
  obtain ⟨x, hx, h0⟩ := DVR.isotropicIn_of_isLocalLevel_zero Fv (QuadForm.diag a) (NF.irreducible_π v)
    (NF.two_ne_zero' v) hL le_rfl
  exact ⟨x, hx, by rw [← evalIn_diag]; exact h0⟩

/-- The induction: peel off a ternary block $\mathbb H\perp\langle-a_0a_1a_2\rangle$. -/
theorem main (h2 : IsUnit (2 : 𝔬)) : ∀ (m : ℕ) (a : Fin m → 𝔬), (∀ i, IsUnit (a i)) →
    (m - 1) / 2 ≤ wittIndex (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a i))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a ha
  by_cases hm : m < 3
  · have : (m - 1) / 2 = 0 := by omega
    rw [this]; exact Nat.zero_le _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3 ≤ m)
    have h2' := two_ne_zero_Fv v
    let a3 : Fin 3 → 𝔬 := fun i => a (Fin.castAdd k i)
    let r : Fin k → 𝔬 := fun j => a (Fin.natAdd 3 j)
    have ha3 : ∀ i, IsUnit (a3 i) := fun i => ha _
    have hr : ∀ j, IsUnit (r j) := fun j => ha _
    have hT := ternary h2' (fun i => algebraMap 𝔬 Fv (a3 i)) (fun i => ne_zero_Fv v (ha3 i))
      (isotropic_three v a3 ha3 h2)
    let u : 𝔬 := -(a3 0 * a3 1 * a3 2)
    have hu : IsUnit u := (((ha3 0).mul (ha3 1)).mul (ha3 2)).neg
    have hιu : algebraMap 𝔬 Fv u =
        -(algebraMap 𝔬 Fv (a3 0) * algebraMap 𝔬 Fv (a3 1) * algebraMap 𝔬 Fv (a3 2)) := by
      simp [u]
    let a' : Fin (1 + k) → 𝔬 := Fin.append (fun _ : Fin 1 => u) r
    have ha' : ∀ i, IsUnit (a' i) := by
      intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa [a'] using hu
      · simpa [a'] using hr j
    have e1 := splitIso (K := Fv) 3 k (fun i => algebraMap 𝔬 Fv (a i))
    have e4 : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i))).Equivalent
        ((weightedSumSquares Fv (fun _ : Fin 1 => algebraMap 𝔬 Fv u)).prod
          (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (r j)))) := by
      have h : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i))).Equivalent
          ((weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' (Fin.castAdd k i)))).prod
            (weightedSumSquares Fv (fun j => algebraMap 𝔬 Fv (a' (Fin.natAdd 1 j))))) :=
        ⟨splitIso (K := Fv) 1 k (fun i => algebraMap 𝔬 Fv (a' i))⟩
      simp only [a', Fin.append_left, Fin.append_right] at h
      exact h
    rw [← hιu] at hT
    have hE : (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a i))).Equivalent
        ((hyperbolicSpace Fv 1).prod (weightedSumSquares Fv (fun i => algebraMap 𝔬 Fv (a' i)))) := by
      exact ⟨e1.trans ((hT.some.prod (QuadraticMap.IsometryEquiv.refl _)).trans
        ((Witt.prodAssoc _ _ _).trans ((QuadraticMap.IsometryEquiv.refl _).prod e4.some.symm)))⟩
    have hrad1 := radical_wss h2' (fun i => algebraMap 𝔬 Fv (a i)) (fun i => ne_zero_Fv v (ha i))
    have hrad2 := radical_wss h2' (fun i => algebraMap 𝔬 Fv (a' i)) (fun i => ne_zero_Fv v (ha' i))
    rw [wittIndex_eq_of_equivalent hE hrad1, wittIndex_hyperbolic_prod 1 _ hrad2]
    have := ih (1 + k) (by omega) a' ha'
    omega

end SelfDualN

/-- **Unit diagonal forms at a non-dyadic place have Witt index $\ge\lfloor(m-1)/2\rfloor$** (O'Meara 92:1, 92:1b). -/
theorem wittIndex_diag_units (h2 : IsUnit (2 : 𝔬)) : ∀ (m : ℕ) (a : Fin m → 𝔬), (∀ i, IsUnit (a i)) →
    (m - 1) / 2 ≤ wittIndex ((QuadForm.diag a).map (algebraMap 𝔬 Fv)).toQuadraticForm := by
  intro m a ha
  rw [SelfDualN.map_diag_toQF]
  exact SelfDualN.main v h2 m a ha

end QuadFormsKB.Hanke2005
