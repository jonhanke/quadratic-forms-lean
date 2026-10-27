import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.Measure.ConeAlgebra
import QuadFormsKB.Lattices.SAEqualPairs
import QuadFormsKB.Tamagawa.OrderNormForm
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarGlobal

/-!
# Reduction of an isotropic space to the cone form

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n = k + 2$ variables whose space
$V = (F^n, Q_0)$ is **isotropic**. A hyperbolic pair $e, f$ ($Q(e) = Q(f) = 0$, $B(e, f) = 1$) gives the vectors
$p_0 = e + f$, $p_1 = e - f$ with $Q(p_0) = 1$, $Q(p_1) = -1$, $B(p_0, p_1) = 0$, and a basis $w_1, \dots, w_k$ of
$\{e, f\}^\perp$. In the basis $(p_0, p_1, w)$ the form is $\langle 1\rangle\perp\langle -1\rangle\perp Q'$
(`exists_coneBasis`). Clearing denominators by $d \in \mathcal O_F\setminus 0$ gives an **integral** change of variables:

* **`exists_compMat_eq_cone`**: there are $G \in M_n(\mathcal O_F)$ with $\det G \ne 0$, $c_0 = d^2 \ne 0$ and a nondegenerate
  $Q_0'$ over $\mathcal O_F$ in $k$ variables with
  $$Q_0\circ G = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'\qquad(\texttt{splitForm } c_0\ (\texttt{splitForm } (-c_0)\ Q_0')),$$
  the cone form of `ConeAlgebra.lean` over $\mathcal O_F$.
* **`covolume_muTam_eq_cone`**: the Tamagawa covolume of $SO(V)(F)$ in $SO(V)(\mathbb A)$ (Weil's measure `muTam`,
  every signature) equals that of the cone form. This is the transport `covolume_muTam_simForm` (conjugation by $G$
  at every place; the local Haar measures change by $|\det G|_v$-powers, `lerayMeasure_unique` at the real places,
  the lattice independence of `muLoc` at the finite places, and the product of the local factors is $1$ by the product
  formula). So **$\tau(SO(V)) = 2$ for every isotropic $V$ follows from the cone forms**
  (`tamagawaNumberTwoAdelic_iff_cone`).
-/

open Matrix MeasureTheory

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.ConeReduction

open NumberField IsDedekindDomain QuadFormsKB QuadFormsKB.QuadForm QuadFormsKB.Tamagawa QuadFormsKB.Lattices
open QuadFormsKB.Tamagawa.Measure.ConeAlgebra

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-! ### Over the field: a basis adapted to a hyperbolic pair -/

section Field

variable (Q : QuadForm F (k + 1 + 1))

theorem qbil_eq (x y : Fin (k + 1 + 1) → F) : qbil Q F x y = (Q.hessian *ᵥ x) ⬝ᵥ y := by
  unfold qbil
  rw [show Q.hessian.map (algebraMap F F) = Q.hessian by ext; simp, dotProduct_comm, hess_dot_comm]

/-- The linear map $x \mapsto (B(x, e), B(x, f))$. -/
def pairL (e f : Fin (k + 1 + 1) → F) : (Fin (k + 1 + 1) → F) →ₗ[F] (Fin 2 → F) where
  toFun x := ![(Q.hessian *ᵥ x) ⬝ᵥ e, (Q.hessian *ᵥ x) ⬝ᵥ f]
  map_add' x y := by ext i; fin_cases i <;> simp [mulVec_add, add_dotProduct]
  map_smul' c x := by ext i; fin_cases i <;> simp [mulVec_smul, smul_dotProduct]

/-- **A basis adapted to a hyperbolic pair**: for $Q$ nondegenerate and isotropic over $F$ there are $P \in M_n(F)$,
$\det P \ne 0$, and a nondegenerate $Q'$ in $k$ variables with $Q(Px) = x_0^2 - x_1^2 + Q'(x')$. -/
theorem exists_coneBasis (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn F) :
    ∃ P : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) F, P.det ≠ 0 ∧
      ∃ Q' : QuadForm F k, Q'.Nondegenerate ∧ ∀ x, Q.eval (P *ᵥ x) = (coneForm 1 Q').eval x := by
  obtain ⟨e, f, he, hf, hef⟩ := exists_hyperbolic_pair Q F hQ hiso
  rw [qbil_eq] at hef
  have he' : Q.eval e = 0 := he
  have hf' : Q.eval f = 0 := hf
  have hfe : (Q.hessian *ᵥ f) ⬝ᵥ e = 1 := by rw [hess_dot_comm, hef]
  have hee : (Q.hessian *ᵥ e) ⬝ᵥ e = 0 := by rw [dotProduct_comm, dotProduct_hessian_self, he', mul_zero]
  have hff : (Q.hessian *ᵥ f) ⬝ᵥ f = 0 := by rw [dotProduct_comm, dotProduct_hessian_self, hf', mul_zero]
  -- the complement `W = {e, f}^⊥`
  set L := pairL Q e f
  have hsurj : LinearMap.range L = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    refine ⟨y 1 • e + y 0 • f, ?_⟩
    ext i; fin_cases i <;>
      simp [L, pairL, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, hee, hef, hfe, hff]
  have hrank : Module.finrank F (LinearMap.ker L) = k := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  let b : Module.Basis (Fin k) F (LinearMap.ker L) := Module.finBasisOfFinrankEq F _ hrank
  set X : Matrix (Fin (k + 1 + 1)) (Fin k) F := fun l i => (b i : Fin (k + 1 + 1) → F) l with hX
  have hXmem : ∀ y : Fin k → F, X *ᵥ y ∈ LinearMap.ker L := by
    intro y
    have : X *ᵥ y = ((∑ i, y i • b i : LinearMap.ker L) : Fin (k + 1 + 1) → F) := by
      ext l; simp [X, mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]; exact Submodule.coe_mem _
  have hXorth : ∀ y, (Q.hessian *ᵥ (X *ᵥ y)) ⬝ᵥ e = 0 ∧ (Q.hessian *ᵥ (X *ᵥ y)) ⬝ᵥ f = 0 := by
    intro y
    have h := hXmem y
    rw [LinearMap.mem_ker] at h
    exact ⟨congrFun h 0, congrFun h 1⟩
  set p₀ := e + f
  set p₁ := e - f
  set P : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) F :=
    fun l j => Fin.cases (p₀ l) (fun j => Fin.cases (p₁ l) (fun i => X l i) j) j with hP
  have hPv : ∀ x, P *ᵥ x = x 0 • p₀ + x 1 • p₁ + X *ᵥ tl x := by
    intro x
    ext l
    simp only [P, mulVec, dotProduct, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Fin.cases_zero, Fin.cases_succ, tl]
    rw [Fin.succ_zero_eq_one]; ring
  set Q' := Q.compMat X
  have hQ'eval : ∀ y, Q'.eval y = Q.eval (X *ᵥ y) := eval_compMat Q X
  have hval : ∀ x, Q.eval (P *ᵥ x) = (coneForm 1 Q').eval x := by
    intro x
    rw [hPv, eval_coneForm, hQ'eval]
    have h1 := eval_add_smul_gen Q (x 0 • p₀ + x 1 • p₁) (X *ᵥ tl x) 1
    rw [one_smul, one_mul, one_pow, one_mul] at h1
    rw [h1]
    have hcross : (Q.hessian *ᵥ (x 0 • p₀ + x 1 • p₁)) ⬝ᵥ (X *ᵥ tl x) = 0 := by
      rw [hess_dot_comm]
      obtain ⟨h0, h1⟩ := hXorth (tl x)
      simp only [p₀, p₁, dotProduct_add, dotProduct_smul, dotProduct_sub, h0, h1, smul_eq_mul]
      ring
    have h2 := eval_add_smul_gen Q (x 0 • p₀) p₁ (x 1)
    rw [h2, eval_smul_gen, hcross]
    have hp0 : Q.eval p₀ = 1 := by
      have := eval_add_smul_gen Q e f 1
      rw [one_smul] at this; rw [this, he', hf', hef]; ring
    have hp1 : Q.eval p₁ = -1 := by
      have := eval_add_smul_gen Q e f (-1)
      rw [neg_one_smul, ← sub_eq_add_neg] at this; rw [this, he', hf', hef]; ring
    have hp01 : (Q.hessian *ᵥ (x 0 • p₀)) ⬝ᵥ p₁ = 0 := by
      simp only [p₀, p₁, mulVec_smul, smul_dotProduct, mulVec_add, add_dotProduct, dotProduct_sub, hee, hef,
        hfe, hff, smul_eq_mul]
      ring
    rw [hp0, hp1, hp01]; ring
  -- `det P ≠ 0`: the columns are independent
  have hdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hPx := hPv x
    rw [hx] at hPx
    obtain ⟨hXe, hXf⟩ := hXorth (tl x)
    have hBe : (Q.hessian *ᵥ (x 0 • p₀ + x 1 • p₁ + X *ᵥ tl x)) ⬝ᵥ e = x 0 - x 1 := by
      simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, p₀, p₁, mulVec_sub, sub_dotProduct,
        smul_eq_mul, hXe]
      rw [hee, hfe]; ring
    have hBf : (Q.hessian *ᵥ (x 0 • p₀ + x 1 • p₁ + X *ᵥ tl x)) ⬝ᵥ f = x 0 + x 1 := by
      simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, p₀, p₁, mulVec_sub, sub_dotProduct,
        smul_eq_mul, hXf]
      rw [hef, hff]; ring
    rw [← hPx, mulVec_zero, zero_dotProduct] at hBe hBf
    have hx0' : x 0 = 0 := by linear_combination (-1 / 2 : F) * hBe + (-1 / 2 : F) * hBf
    have hx1' : x 1 = 0 := by linear_combination (1 / 2 : F) * hBe + (-1 / 2 : F) * hBf
    rw [hx0', hx1', zero_smul, zero_smul, zero_add, zero_add] at hPx
    have hXt : X *ᵥ tl x = 0 := hPx.symm
    have htl : tl x = 0 := by
      have hsum : ((∑ i, tl x i • b i : LinearMap.ker L) : Fin (k + 1 + 1) → F) = 0 := by
        rw [← hXt]; ext l; simp [X, mulVec, dotProduct, Finset.sum_apply, mul_comm]
      have hsum' : (∑ i, tl x i • b i : LinearMap.ker L) = 0 := Subtype.ext hsum
      have := (Fintype.linearIndependent_iff.mp b.linearIndependent) (tl x) hsum'
      exact funext this
    apply hx0
    rw [← v3_eta x, hx0', hx1', htl]
    ext i; refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => rfl) i) i
  refine ⟨P, hdet, Q', ?_, hval⟩
  -- nondegeneracy of `Q'`
  have hH := PadicClass.transpose_mul_hessian_mul (Q := Q) (Q' := coneForm 1 Q') (P := P) hval
  have h1 := congrArg Matrix.det hH
  rw [det_mul, det_mul, det_transpose, coneForm, det_hessian_splitForm, det_hessian_splitForm] at h1
  rw [QuadForm.Nondegenerate]
  intro h0
  rw [h0] at h1
  have : P.det * Q.hessian.det * P.det = 0 := by rw [h1]; ring
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hdet h
    · exact hQ h
  · exact hdet h

end Field

/-! ### Over $\mathcal O_F$: an integral change of variables to the cone form -/

section Integral

theorem nondegenerate_map {m : ℕ} {Q₀ : QuadForm (𝓞 F) m} (hQ : Q₀.Nondegenerate) :
    (Q₀.map (algebraMap (𝓞 F) F)).Nondegenerate := by
  rw [QuadForm.Nondegenerate]
  have : (Q₀.map (algebraMap (𝓞 F) F)).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hQ

/-- A form over $\mathcal O_F$ is determined by its values over $F$. -/
theorem eq_of_evalIn_eq {m : ℕ} {Q Q' : QuadForm (𝓞 F) m} (h : ∀ y : Fin m → F, Q.evalIn F y = Q'.evalIn F y) :
    Q = Q' := by
  apply QuadFormsKB.LocalDensity.NF.map_injective (IsFractionRing.injective (𝓞 F) F)
  refine eq_of_eval_eq fun y => ?_
  have e1 : ∀ S : QuadForm (𝓞 F) m, (S.map (algebraMap (𝓞 F) F)).eval y = S.evalIn F y := fun S => by
    simp [QuadForm.evalIn, QuadForm.map]
  rw [e1, e1, h]

theorem nondegenerate_splitForm {m : ℕ} {a : 𝓞 F} (ha : a ≠ 0) {S : QuadForm (𝓞 F) m} (hS : S.Nondegenerate) :
    (splitForm a S).Nondegenerate := by
  rw [QuadForm.Nondegenerate, det_hessian_splitForm]
  exact mul_ne_zero (mul_ne_zero two_ne_zero ha) hS

theorem evalIn_map_eq {m : ℕ} (S : QuadForm (𝓞 F) m) (y : Fin m → F) :
    (S.map (algebraMap (𝓞 F) F)).eval y = S.evalIn F y := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- **Reduction of an isotropic space to the cone form, integrally.** For $Q_0$ nondegenerate over $\mathcal O_F$ in
$k + 2$ variables with $Q_0\otimes F$ isotropic there are $G \in M_{k+2}(\mathcal O_F)$, $\det G \ne 0$, $c_0 \ne 0$ and a
nondegenerate $Q_0'$ over $\mathcal O_F$ in $k$ variables with
$Q_0\circ G = \langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0'$. -/
@[kb "omeara1963" "§42, 42:10, p. 95 (a regular isotropic space splits a hyperbolic plane); weil1982 §4.5 [unverified]"]
theorem exists_compMat_eq_cone (Q₀ : QuadForm (𝓞 F) (k + 1 + 1)) (hQ : Q₀.Nondegenerate)
    (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F) :
    ∃ G : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (𝓞 F), G.det ≠ 0 ∧ ∃ c₀ : 𝓞 F, c₀ ≠ 0 ∧
      ∃ Q₀' : QuadForm (𝓞 F) k, Q₀'.Nondegenerate ∧ Q₀.compMat G = splitForm c₀ (splitForm (-c₀) Q₀') := by
  classical
  set QF := Q₀.map (algebraMap (𝓞 F) F)
  obtain ⟨P, hP, Q', hQ', hval⟩ := exists_coneBasis QF (nondegenerate_map hQ) hiso
  -- clear the denominators of `P` and of the coefficients of `Q'`
  let f : (Fin (k + 1 + 1) × Fin (k + 1 + 1)) ⊕ (Fin k × Fin k) → F := fun i =>
    Sum.elim (fun p => P p.1 p.2) (fun p => Q'.coeff p.1 p.2) i
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) Finset.univ f
  set d : 𝓞 F := (b : 𝓞 F)
  have hd : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hd
  have hint : ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * f i := by
    intro i
    obtain ⟨r, hr⟩ := hb i (Finset.mem_univ i)
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose r hr using hint
  set G : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) (𝓞 F) := fun i j => r (Sum.inl (i, j))
  have hGF : G.map (algebraMap (𝓞 F) F) = algebraMap (𝓞 F) F d • P := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact hr (Sum.inl (i, j))
  set Q₀' : QuadForm (𝓞 F) k := QuadForm.ofUpper fun i j => d * r (Sum.inr (i, j))
  have hQ₀'map : Q₀'.map (algebraMap (𝓞 F) F) = (algebraMap (𝓞 F) F d ^ 2) • Q' := by
    ext i j
    simp only [Q₀', QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply, smul_coeff,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [map_mul, hr]; simp [f]; ring
    · rw [map_zero, Q'.upper (show id j < id i from not_le.mp h), mul_zero]
  refine ⟨G, ?_, d ^ 2, pow_ne_zero 2 hd, Q₀', ?_, ?_⟩
  · intro h0
    have := congrArg (algebraMap (𝓞 F) F) h0
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGF, det_smul, map_zero] at this
    rcases mul_eq_zero.mp this with h | h
    · exact pow_ne_zero _ hdF h
    · exact hP h
  · rw [QuadForm.Nondegenerate]
    intro h0
    have hH : (Q₀'.map (algebraMap (𝓞 F) F)).hessian.det = 0 := by
      have : (Q₀'.map (algebraMap (𝓞 F) F)).hessian = Q₀'.hessian.map (algebraMap (𝓞 F) F) := by
        ext i j; simp [QuadForm.hessian, QuadForm.map]
      rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hQ₀'map] at hH
    have : ((algebraMap (𝓞 F) F d ^ 2) • Q').hessian = (algebraMap (𝓞 F) F d ^ 2) • Q'.hessian := by
      ext i j; simp [QuadForm.hessian, smul_coeff, Matrix.smul_apply, mul_add]
    rw [this, det_smul] at hH
    rcases mul_eq_zero.mp hH with h | h
    · exact pow_ne_zero _ (pow_ne_zero 2 hdF) h
    · exact hQ' h
  · refine eq_of_evalIn_eq fun y => ?_
    have hy' : Q₀'.evalIn F (tl y) = algebraMap (𝓞 F) F d ^ 2 * Q'.eval (tl y) := by
      rw [← evalIn_map_eq, hQ₀'map, QuadForm.eval, QuadForm.evalIn]
      simp only [QuadForm.evalIn, smul_coeff, Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self,
        RingHom.id_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    have hL : (Q₀.compMat G).evalIn F y =
        algebraMap (𝓞 F) F d ^ 2 * (1 * y 0 ^ 2 - 1 * y 1 ^ 2 + Q'.eval (tl y)) := by
      rw [← evalIn_map_eq, ← map_compMat, eval_compMat, hGF, smul_mulVec, eval_smul_gen, hval, eval_coneForm]
    have hR : (splitForm (d ^ 2) (splitForm (-d ^ 2) Q₀')).evalIn F y =
        algebraMap (𝓞 F) F (d ^ 2) * y 0 * y 0 + (algebraMap (𝓞 F) F (-d ^ 2) * y 1 * y 1 +
          Q₀'.evalIn F (tl y)) := by
      conv_lhs => rw [← v3_eta y]
      rw [v3, evalIn_splitForm, evalIn_splitForm]
    rw [hL, hR, hy']
    simp only [map_pow, map_neg]
    ring

set_option maxHeartbeats 2000000 in
open QuadFormsKB.Tamagawa.Measure.Weil in
/-- **The Tamagawa covolume of an isotropic space is that of a cone form** (any signature, $k \ge 1$, $n = k + 2$):
with $G, c_0, Q_0'$ from `exists_compMat_eq_cone`,
$\mathrm{covol}(SO(V)(F), \mu_{\mathrm{Tam}}) = \mathrm{covol}(SO(\langle c_0\rangle\perp\langle -c_0\rangle\perp Q_0')(F),
\mu_{\mathrm{Tam}})$. -/
@[kb "weil1982" "§2.3, Thm 2.3.1, pp. 21–22 (independence of choices); §4.5 [unverified]"]
theorem covolume_muTam_eq_cone (hk : 1 ≤ k) (Q₀ : QuadForm (𝓞 F) (k + 1 + 1)) (hQ : Q₀.Nondegenerate)
    (hiso : (Q₀.map (algebraMap (𝓞 F) F)).IsotropicIn F) :
    ∃ (c₀ : 𝓞 F) (hc₀ : c₀ ≠ 0) (Q₀' : QuadForm (𝓞 F) k) (hQ' : Q₀'.Nondegenerate),
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) =
        covolume (GammaSOAdele (splitForm c₀ (splitForm (-c₀) Q₀'))) (SOAdele (splitForm c₀ (splitForm (-c₀) Q₀')))
          (muTam (splitForm c₀ (splitForm (-c₀) Q₀'))
            (nondegenerate_splitForm hc₀ (nondegenerate_splitForm (neg_ne_zero.mpr hc₀) hQ')) fun _ => 1) := by
  have hex := exists_compMat_eq_cone Q₀ hQ hiso
  obtain ⟨G, hG, hex⟩ := hex
  obtain ⟨c₀, hc₀, hex⟩ := hex
  obtain ⟨Q₀', hQ', heq⟩ := hex
  refine Exists.intro c₀ (Exists.intro hc₀ (Exists.intro Q₀' (Exists.intro hQ' ?_)))
  have h := covolume_muTam_simForm (Q₀ := Q₀) (c := 1) (G := G) (by omega) (by omega) hQ one_ne_zero hG
  have hone : ∀ S : QuadForm (𝓞 F) (k + 1 + 1), (1 : 𝓞 F) • S = S := fun S => by ext a b; simp [smul_coeff]
  have hs : simForm Q₀ 1 G = splitForm c₀ (splitForm (-c₀) Q₀') := by
    rw [simForm, hone, heq]
  have key : ∀ (Q₁ Q₂ : QuadForm (𝓞 F) (k + 1 + 1)) (_ : Q₁ = Q₂) (h₁ : Q₁.Nondegenerate) (h₂ : Q₂.Nondegenerate),
      covolume (GammaSOAdele Q₁) (SOAdele Q₁) (muTam Q₁ h₁ fun _ => 1) =
        covolume (GammaSOAdele Q₂) (SOAdele Q₂) (muTam Q₂ h₂ fun _ => 1) := by
    rintro _ _ rfl _ _; rfl
  exact h.symm.trans (key _ _ hs _ _)

end Integral

end QuadFormsKB.Tamagawa.Measure.ConeReduction
