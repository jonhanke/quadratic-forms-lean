import QuadFormsKB.Tamagawa.Measure.Weil.SphereOrbitsNF
import QuadFormsKB.Tamagawa.Measure.Weil.SphereBlock
import QuadFormsKB.Tamagawa.OrthFq

/-!
# The integral complement of an anisotropic vector

$F$ a number field, $Q_0$ a nondegenerate form over $\mathcal O_F$ in $k + 1$ variables, $\xi\in F^{k+1}$ with
$Q_0(\xi)\ne0$. A **`SphereComplement Q₀ ξ`** is an integral matrix $G\in M_{k+1}(\mathcal O_F)$, $\det G\ne0$, whose first
column is $d\xi$ ($d\in\mathcal O_F\setminus0$) and whose other columns span $\xi^\perp$, so that
$$Q_0\circ G = \langle m_0\rangle\perp Q',\qquad m_0 = d^2Q_0(\xi)\in\mathcal O_F\setminus0,$$
with $Q'$ nondegenerate over $\mathcal O_F$ in $k$ variables (the form of the complement $\xi^\perp$). It exists
(**`exists_sphereComplement`**): over $F$ split off $\xi$ (`QuadForm.exists_split`, $2Q_0(\xi)$ and some $\xi_i$ are units of
$F$) and clear denominators.
-/

open Matrix NumberField

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

open QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

/-- **The integral complement of $\xi$**: fields `d`, `G`, `m₀`, `Q'` with $G e_0 = d\xi$ (`col`),
$Q_0\circ G = \langle m_0\rangle\perp Q'$ (`split`), $\det G\ne0$, $d, m_0\ne0$ and $Q'$ nondegenerate. -/
structure SphereComplement (Q₀ : QuadForm (𝓞 F) (k + 1)) (ξ : Fin (k + 1) → F) where
  /-- The denominator $d$. -/
  d : 𝓞 F
  /-- The integral matrix $G = [d\xi\mid G']$. -/
  G : Matrix (Fin (k + 1)) (Fin (k + 1)) (𝓞 F)
  /-- $m_0 = Q_0(d\xi)$. -/
  m₀ : 𝓞 F
  /-- The complement form. -/
  Q' : QuadForm (𝓞 F) k
  hd : d ≠ 0
  hG : G.det ≠ 0
  hm : m₀ ≠ 0
  col : ∀ i, algebraMap (𝓞 F) F (G i 0) = algebraMap (𝓞 F) F d * ξ i
  split : Q₀.compMat G = splitForm m₀ Q'
  hQ' : Q'.Nondegenerate

/-- Scaling the matrix by `c` scales off-diagonal-column coefficients by `c ^ 2`. -/
theorem compMat_smul_coeff_zero_succ {K : Type*} [Field K] {m : ℕ} (Q : QuadFormsKB.QuadForm K (m + 1))
    (c : K) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (j : Fin m) :
    (Q.compMat (c • X)).coeff 0 j.succ = c ^ 2 * (Q.compMat X).coeff 0 j.succ := by
  rw [QuadFormsKB.QuadForm.compMat_coeff, QuadFormsKB.QuadForm.compMat_coeff,
    if_pos (Fin.zero_le _), if_pos (Fin.zero_le _), if_neg (Fin.succ_ne_zero j).symm,
    if_neg (Fin.succ_ne_zero j).symm]
  have h1 : (fun l => (c • X) l 0) = c • (fun l => X l 0) := by ext l; simp
  have h2 : (fun l => (c • X) l j.succ) = c • (fun l => X l j.succ) := by ext l; simp
  rw [h1, h2, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]; ring

/-- `f (Q x) = (f Q)(f x)`. -/
theorem map_eval_apply' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {m : ℕ} (Q : QuadFormsKB.QuadForm A m)
    (x : Fin m → A) : f (Q.eval x) = (Q.map f).eval (fun l => f (x l)) := by
  simp [QuadFormsKB.QuadForm.map, QuadFormsKB.QuadForm.eval, QuadFormsKB.QuadForm.evalIn, map_sum, apply_ite f]

/-- **Existence of the integral complement.** -/
theorem exists_sphereComplement (Q₀ : QuadForm (𝓞 F) (k + 1)) (hQ : Q₀.Nondegenerate) (ξ : Fin (k + 1) → F)
    (hξ : qF Q₀ ξ ≠ 0) : Nonempty (SphereComplement Q₀ ξ) := by
  classical
  set f := algebraMap (𝓞 F) F with hf
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective (𝓞 F) F
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hξ0 : ξ ≠ 0 := fun h => hξ (by rw [h]; simp [qF, QuadForm.eval, QuadForm.evalIn])
  obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
    by_contra hcon; push_neg at hcon; exact hξ0 (funext hcon)
  obtain ⟨g, hg1, hg2⟩ := QuadFormsKB.QuadForm.exists_split (Q₀.map f) ξ
    (isUnit_iff_ne_zero.mpr (mul_ne_zero h2 hξ)) i (isUnit_iff_ne_zero.mpr hi)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1)))
    (fun p => g.val p.1 p.2)
  choose G0 hG0 using fun i j => hb (i, j) (Finset.mem_univ _)
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin (k + 1)) (Fin (k + 1)) (𝓞 F), ∀ i j, f (G i j) = f (b : 𝓞 F) * g.val i j :=
    ⟨G0, fun i j => by
      have := hG0 i j
      rw [Algebra.smul_def] at this
      exact this⟩
  set d : 𝓞 F := (b : 𝓞 F) with hd
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hGf : ∀ i j, f (G i j) = f d * g.val i j := hG
  have hmap : G.map f = f d • g.val := by ext i j; simp [hGf]
  have hcol0 : ∀ i, f (G i 0) = f d * ξ i := fun i => by
    rw [hGf, ← hg1]; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdetG : G.det ≠ 0 := by
    intro h
    have : (G.map f).det = 0 := by
      have h' : (G.map f).det = f G.det := (RingHom.map_det f G).symm
      rw [h', h, map_zero]
    rw [hmap, Matrix.det_smul] at this
    have hgd : g.val.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.mp g.isUnit).ne_zero
    simp only [Fintype.card_fin] at this
    exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff f hinj).mpr hd0)) hgd this
  set m₀ : 𝓞 F := Q₀.eval (fun l => G l 0) with hm₀
  set Q' : QuadForm (𝓞 F) k := Q₀.compMat (G.submatrix id Fin.succ) with hQ'
  have hsplit : Q₀.compMat G = splitForm m₀ Q' := by
    refine QuadFormsKB.QuadForm.ext_upper fun i j hij => ?_
    rw [splitForm_coeff]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp [QuadFormsKB.QuadForm.compMat_coeff, hm₀]
      | succ j =>
        rw [cornerMat_zero_succ]
        apply hinj
        have hm := congrArg (fun Q => Q.coeff 0 j.succ) (QuadFormsKB.QuadForm.map_compMat f Q₀ G)
        simp only [hmap] at hm
        have h := compMat_smul_coeff_zero_succ (Q₀.map f) (f d) g.val j
        rw [hg2 j, mul_zero] at h
        rw [map_zero]
        exact hm.symm.trans h
    | succ a =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp [Fin.le_def])
      | succ b =>
        rw [cornerMat_succ_succ, QuadFormsKB.QuadForm.compMat_coeff, hQ', QuadFormsKB.QuadForm.compMat_coeff]
        simp [Fin.succ_le_succ_iff, Fin.succ_inj]
  have hdet : (Q₀.compMat G).hessian.det ≠ 0 := by
    rw [QuadFormsKB.QuadForm.hessian_compMat, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hdetG hQ) hdetG
  rw [hsplit, hessian_splitForm, det_cornerMat] at hdet
  have hm : m₀ ≠ 0 := fun h => hdet (by rw [h, mul_zero, zero_mul])
  exact ⟨⟨d, G, m₀, Q', hd0, hdetG, hm, hcol0, hsplit, fun h => hdet (by rw [h, mul_zero])⟩⟩

/-- $m_0 = d^2Q_0(\xi)$ in $F$. -/
theorem SphereComplement.m₀_eq {Q₀ : QuadForm (𝓞 F) (k + 1)} {ξ : Fin (k + 1) → F} (C : SphereComplement Q₀ ξ) :
    algebraMap (𝓞 F) F C.m₀ = algebraMap (𝓞 F) F C.d ^ 2 * qF Q₀ ξ := by
  have h := congrArg (fun Q => Q.coeff 0 0) C.split
  simp only [QuadFormsKB.QuadForm.compMat_coeff, splitForm_coeff, cornerMat_zero_zero, le_refl, if_true] at h
  rw [← h, map_eval_apply']
  have hc : (fun l => algebraMap (𝓞 F) F (C.G l 0)) = algebraMap (𝓞 F) F C.d • ξ := by
    ext l; simp [C.col]
  rw [hc]
  exact qF_smul Q₀ _ ξ

end

end QuadFormsKB.Tamagawa.Measure.Weil
