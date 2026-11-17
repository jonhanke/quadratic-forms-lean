/-
# Chenevier–Lannes (1.3.2): the Witt–Igusa identities for $g \le 3$ from the vanishing of $S_8$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.3, p. 7, (1.3.2); §5.1, p. 123 (Siegel's operator $\Phi$
and theta series). Printed page numbers.

**Route.** $\vartheta_g(E_8 \oplus E_8)$ and $\vartheta_g(E_{16})$ are Siegel modular forms of weight $8$ for
$\mathrm{Sp}_{2g}(\mathbb{Z})$ (`siegelThetaModular`). Siegel's operator sends a theta series of genus $g + 1$ to
the theta series of genus $g$ of the same lattice (`tendsto_siegelTheta_phiEmbed`: in
$\vartheta_{g+1}\begin{pmatrix}Z'&0\\0&it\end{pmatrix}$ the terms whose last column is nonzero tend to $0$). So if the
identity holds in genus $g$, the difference in genus $g + 1$ is a cusp form of weight $8$; it vanishes if
$S_8(\mathrm{Sp}_{2g+2}(\mathbb{Z})) = 0$. Starting from genus $1$ (`wittIgusa_genus_one`, proved), the identities for
$g = 2, 3$ follow from the named input

* `CuspFormsWeightEightVanish` ($S_8(\mathrm{Sp}_4(\mathbb{Z})) = S_8(\mathrm{Sp}_6(\mathbb{Z})) = 0$; Igusa for genus
  $2$, Tsuyumine / Poor–Yuen for genus $3$; not proved here: it needs the structure of the rings of Siegel modular
  forms of genus 2 and 3).

This input is a statement about modular forms alone (no lattice enters), so it is strictly smaller than `WittIgusa`;
the book's own proof (Kneser's lattice argument, Appendix A) avoids it, and is not formalized.

**Main results.**
* `IsSiegelModularForm.sub`: the difference of two Siegel modular forms of the same weight is one.
* `tendsto_siegelTheta_phiEmbed` (unconditional): $\Phi\,\vartheta_{g+1}(L) = \vartheta_g(L)$ for $Q$ positive definite.
* `wittIgusa_of_cuspVanish` (conditional on `CuspFormsWeightEightVanish`): `WittIgusa`.
-/
import QuadFormsKB.Literature.ChenevierLannes.ThetaModular
import QuadFormsKB.Literature.ChenevierLannes.Classification

open Complex Matrix Filter Topology
open QuadFormsKB.Lattices

namespace QuadFormsKB.ChenevierLannes

noncomputable section

/-- **Input: no cusp forms of weight $8$ in genus $2$ and $3$** (Igusa 1962 for genus $2$: the first cusp form has
weight $10$; Tsuyumine 1986 for genus $3$: the first cusp form has weight $12$) [unverified]: every Siegel cusp form of
weight $8$ for $\mathrm{Sp}_4(\mathbb{Z})$ or $\mathrm{Sp}_6(\mathbb{Z})$ vanishes on the Siegel upper half space.
`IsSiegelCuspForm 8 g f` is a cusp form of genus $g + 1$. Assumed, not proved. -/
@[kb "chenevierlannes2019" "§1.3, p. 7 (S_8(Sp_4(Z)) = S_8(Sp_6(Z)) = 0, used for (1.3.2); as an input)"]
structure CuspFormsWeightEightVanish : Prop where
  /-- Genus $g + 1 \in \{2, 3\}$: a weight-$8$ cusp form is $0$ on $\mathbb{H}_{g+1}$. -/
  vanish : ∀ g : ℕ, 1 ≤ g → g ≤ 2 → ∀ f, IsSiegelCuspForm 8 g f → ∀ Z ∈ siegelUpper (g + 1), f Z = 0

/-- The difference of two Siegel modular forms of weight $k$ and genus $g$ is a Siegel modular form. -/
theorem IsSiegelModularForm.sub {k : ℤ} {g : ℕ} {f₁ f₂ : Matrix (Fin g) (Fin g) ℂ → ℂ}
    (h₁ : IsSiegelModularForm k g f₁) (h₂ : IsSiegelModularForm k g f₂) :
    IsSiegelModularForm k g (fun Z => f₁ Z - f₂ Z) := by
  refine ⟨?_, fun γ hγ Z hZ => ?_, ?_⟩
  · letI : NormedAddCommGroup (Matrix (Fin g) (Fin g) ℂ) := Matrix.normedAddCommGroup
    letI : NormedSpace ℂ (Matrix (Fin g) (Fin g) ℂ) := Matrix.normedSpace
    exact fun W hW => (h₁.holo W hW).sub (h₂.holo W hW)
  · rw [h₁.modular γ hγ Z hZ, h₂.modular γ hγ Z hZ]; ring
  · obtain ⟨C₁, hC₁⟩ := h₁.bounded
    obtain ⟨C₂, hC₂⟩ := h₂.bounded
    exact ⟨C₁ + C₂, fun Z hZ hp => (norm_sub_le _ _).trans (add_le_add (hC₁ Z hZ hp) (hC₂ Z hZ hp))⟩

section PhiTheta

open QuadFormsKB.Lattices

variable {n g : ℕ}

/-- The Hessian of a positive definite integral form is a real positive definite matrix. -/
theorem hessianR_posDef' {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) :
    (Q.hessian.map ((↑) : ℤ → ℝ)).PosDef := by
  have h := (QuadFormsKB.Siegel.gramMatrix_posDef hQ).smul (show (0 : ℝ) < 2 by norm_num)
  convert h using 1
  unfold QuadFormsKB.Siegel.gramMatrix
  rw [smul_smul]
  norm_num

/-- $c^{\mathsf T} H c$ for an integer vector $c$. -/
def qv (Q : QuadForm ℤ n) (c : Fin n → ℤ) : ℤ := c ⬝ᵥ Q.hessian *ᵥ c

theorem qv_pos {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {c : Fin n → ℤ} (hc : c ≠ 0) :
    0 < qv Q c := by
  have h := (hessianR_posDef' hQ).dotProduct_mulVec_pos
    (show (fun a => (c a : ℝ)) ≠ 0 from fun h0 => hc (funext fun a => by
      have := congrFun h0 a
      simpa using this))
  have e : ((qv Q c : ℤ) : ℝ) = star (fun a => (c a : ℝ)) ⬝ᵥ (Q.hessian.map ((↑) : ℤ → ℝ)) *ᵥ (fun a => (c a : ℝ)) := by
    simp [qv, dotProduct, mulVec]
  rw [← e] at h
  exact_mod_cast h

theorem qv_nonneg {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (c : Fin n → ℤ) : 0 ≤ qv Q c := by
  by_cases hc : c = 0
  · subst hc; simp [qv]
  · exact (qv_pos hQ hc).le

/-- The first $g$ columns. -/
def colInit (X : Matrix (Fin n) (Fin (g + 1)) ℤ) : Matrix (Fin n) (Fin g) ℤ :=
  Matrix.of fun a j => X a j.castSucc

/-- The last column. -/
def colLast (X : Matrix (Fin n) (Fin (g + 1)) ℤ) : Fin n → ℤ := fun a => X a (Fin.last g)

theorem summable_norm_thTerm' {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {Z : Matrix (Fin g) (Fin g) ℂ}
    (hZ : Z ∈ siegelUpper g) : Summable fun X : Matrix (Fin n) (Fin g) ℤ => ‖thTerm Q X Z‖ :=
  (WeilRep.Genus.summable_thetaG (hessianR_posDef' hQ) hZ).congr fun X => by
    rw [thTerm, thetaArg_eq]

theorem phiEmbed_mem {Z' : Matrix (Fin g) (Fin g) ℂ} (hZ : Z' ∈ siegelUpper g) {t : ℝ} (ht : 0 < t) :
    phiEmbed Z' t ∈ siegelUpper (g + 1) := by
  have hsymm : (phiEmbed Z' t)ᵀ = phiEmbed Z' t := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [phiEmbed]
    · simp [phiEmbed]
    · simp [phiEmbed]
    · have := congrFun (congrFun hZ.1 i') j'
      simp [phiEmbed, Matrix.transpose_apply] at this ⊢
      exact this
  refine ⟨hsymm, ?_⟩
  have hH : ((phiEmbed Z' t).map Complex.im).IsHermitian := by
    ext i j
    have := congrFun (congrFun hsymm i) j
    have h2 := congrArg Complex.im this
    simpa [Matrix.conjTranspose_apply] using h2
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hq : x ⬝ᵥ ((phiEmbed Z' t).map Complex.im) *ᵥ x =
      (fun i => x i.castSucc) ⬝ᵥ (Z'.map Complex.im) *ᵥ (fun i => x i.castSucc) + t * x (Fin.last g) ^ 2 := by
    simp [dotProduct, mulVec, Fin.sum_univ_castSucc, phiEmbed, Finset.sum_add_distrib, mul_add, add_mul]
    ring
  rw [star_trivial, hq]
  by_cases h0 : (fun i : Fin g => x i.castSucc) = 0
  · have hl : x (Fin.last g) ≠ 0 := by
      intro hl
      apply hx
      funext i
      refine Fin.lastCases hl (fun i' => ?_) i
      exact congrFun h0 i'
    rw [h0]
    simp only [Matrix.mulVec_zero, dotProduct_zero, zero_add]
    positivity
  · have h1 := hZ.2.dotProduct_mulVec_pos h0
    have h2 : 0 ≤ t * x (Fin.last g) ^ 2 := by positivity
    simpa using add_pos_of_pos_of_nonneg h1 h2

theorem thTerm_phiEmbed (Q : QuadForm ℤ n) (X : Matrix (Fin n) (Fin (g + 1)) ℤ)
    (Z' : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) :
    thTerm Q X (phiEmbed Z' t) =
      thTerm Q (colInit X) Z' * ((Real.exp (-(Real.pi * t * (qv Q (colLast X) : ℝ))) : ℝ) : ℂ) := by
  unfold thTerm
  have hE : ∀ i j : Fin g, ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ)) i.castSucc j.castSucc =
      (((colInit X)ᵀ * Q.hessian * colInit X).map (Int.cast : ℤ → ℂ)) i j := by
    intro i j; simp [Matrix.mul_apply, colInit]
  have hL : ((Xᵀ * Q.hessian * X).map (Int.cast : ℤ → ℂ)) (Fin.last g) (Fin.last g) =
      (qv Q (colLast X) : ℂ) := by
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, qv, dotProduct, mulVec, colLast]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have htr : ∀ A : Matrix (Fin (g + 1)) (Fin (g + 1)) ℂ, (A * phiEmbed Z' t).trace =
      (∑ i : Fin g, ∑ j : Fin g, A i.castSucc j.castSucc * Z' j i) + A (Fin.last g) (Fin.last g) * (I * t) := by
    intro A
    simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_castSucc, phiEmbed]
  have htr' : ∀ A : Matrix (Fin g) (Fin g) ℂ, (A * Z').trace = ∑ i : Fin g, ∑ j : Fin g, A i j * Z' j i := by
    intro A; simp [Matrix.trace, Matrix.mul_apply]
  rw [Complex.ofReal_exp, ← Complex.exp_add, htr, htr']
  congr 1
  simp only [hE, hL]
  push_cast
  rw [mul_add]
  linear_combination ((Real.pi : ℂ) * (t : ℂ) * ((qv Q (colLast X) : ℤ) : ℂ)) * Complex.I_mul_I

end PhiTheta

/-- **Siegel's operator on theta series**: for $Q$ positive definite and $Z' \in \mathbb{H}_g$,
$\lim_{t \to +\infty}\vartheta_{g+1}(L)\begin{pmatrix}Z'&0\\0&it\end{pmatrix} = \vartheta_g(L)(Z')$. Unconditional. -/
@[kb "chenevierlannes2019" "§5.1, p. 123 (Φ ϑ_{g+1}(L) = ϑ_g(L))"]
theorem tendsto_siegelTheta_phiEmbed {n : ℕ} {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) {g : ℕ}
    {Z' : Matrix (Fin g) (Fin g) ℂ} (hZ : Z' ∈ siegelUpper g) :
    Tendsto (fun t : ℝ => siegelTheta (g + 1) Q (phiEmbed Z' t)) atTop (nhds (siegelTheta g Q Z')) := by
  classical
  have hsum : Summable fun X : Matrix (Fin n) (Fin (g + 1)) ℤ => ‖thTerm Q X (phiEmbed Z' 1)‖ :=
    summable_norm_thTerm' hQ (phiEmbed_mem hZ one_pos)
  have hlim : ∀ X : Matrix (Fin n) (Fin (g + 1)) ℤ, Tendsto (fun t : ℝ => thTerm Q X (phiEmbed Z' t)) atTop
      (nhds (if colLast X = 0 then thTerm Q (colInit X) Z' else 0)) := by
    intro X
    simp only [thTerm_phiEmbed]
    by_cases hc : colLast X = 0
    · simp [hc, qv]
    · simp only [hc, if_false]
      have hq : (0 : ℝ) < (qv Q (colLast X) : ℝ) := by exact_mod_cast qv_pos hQ hc
      have h1 : Tendsto (fun t : ℝ => Real.exp (-(Real.pi * t * (qv Q (colLast X) : ℝ)))) atTop (nhds 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have : Tendsto (fun t : ℝ => (Real.pi * (qv Q (colLast X) : ℝ)) * t) atTop atTop :=
          tendsto_id.const_mul_atTop (by positivity)
        refine (tendsto_neg_atTop_atBot.comp this).congr fun t => ?_
        simp only [Function.comp]; ring_nf
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa using h2.const_mul (thTerm Q (colInit X) Z')
  have hbd : ∀ᶠ t : ℝ in atTop, ∀ X : Matrix (Fin n) (Fin (g + 1)) ℤ,
      ‖thTerm Q X (phiEmbed Z' t)‖ ≤ ‖thTerm Q X (phiEmbed Z' 1)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht X
    rw [thTerm_phiEmbed, thTerm_phiEmbed, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (0 : ℝ) ≤ (qv Q (colLast X) : ℝ) := by exact_mod_cast qv_nonneg hQ _
    nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le this]
  have key := tendsto_tsum_of_dominated_convergence hsum hlim hbd
  have hι : Function.Injective fun X' : Matrix (Fin n) (Fin g) ℤ =>
      (Matrix.of fun a j => Fin.lastCases (0 : ℤ) (fun j' => X' a j') j : Matrix (Fin n) (Fin (g + 1)) ℤ) := by
    intro X Y h
    ext a j
    have := congrFun (congrFun h a) j.castSucc
    simpa using this
  have hlast : ∀ X' : Matrix (Fin n) (Fin g) ℤ,
      colLast (Matrix.of fun a j => Fin.lastCases (0 : ℤ) (fun j' => X' a j') j : Matrix (Fin n) (Fin (g + 1)) ℤ) = 0 := by
    intro X'; funext a; simp [colLast]
  have hinit : ∀ X' : Matrix (Fin n) (Fin g) ℤ,
      colInit (Matrix.of fun a j => Fin.lastCases (0 : ℤ) (fun j' => X' a j') j : Matrix (Fin n) (Fin (g + 1)) ℤ) = X' := by
    intro X'; ext a j; simp [colInit]
  have hval : ∑' X : Matrix (Fin n) (Fin (g + 1)) ℤ, (if colLast X = 0 then thTerm Q (colInit X) Z' else 0) =
      siegelTheta g Q Z' := by
    rw [← hι.tsum_eq]
    · simp only [hlast, hinit, if_true]; rfl
    · intro X hX
      have hc : colLast X = 0 := by
        by_contra hc; exact hX (by simp [hc])
      refine ⟨colInit X, ?_⟩
      ext a j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simpa [colLast] using (congrFun hc a).symm
      · simp [colInit]
  rw [hval] at key
  simpa only [siegelTheta_eq_tsum] using key

/-- **The Witt–Igusa identities (1.3.2)** (Chenevier–Lannes, §1.3, p. 7): $\vartheta_g(E_8 \oplus E_8) =
\vartheta_g(E_{16})$ for $g \le 3$, **conditional** on `CuspFormsWeightEightVanish`. -/
@[kb "chenevierlannes2019" "(1.3.2), p. 7 (conditional on S_8 = 0 in genus 2, 3)"]
theorem wittIgusa_of_cuspVanish (h : CuspFormsWeightEightVanish) : WittIgusa := by
  have step : ∀ g : ℕ, 1 ≤ g → g ≤ 2 →
      (∀ Z ∈ siegelUpper g, siegelTheta g twoE8 Z = siegelTheta g gamma16 Z) →
      ∀ Z ∈ siegelUpper (g + 1), siegelTheta (g + 1) twoE8 Z = siegelTheta (g + 1) gamma16 Z := by
    intro g hg1 hg2 hprev Z hZ
    have h1 := siegelThetaModular_of_evenUnimodular twoE8 isEvenUnimodular_twoE8 (g + 1)
    have h2 := siegelThetaModular_of_evenUnimodular gamma16 isEvenUnimodular_gamma16 (g + 1)
    have e : ((16 / 2 : ℕ) : ℤ) = 8 := by norm_num
    rw [e] at h1 h2
    have hcusp : IsSiegelCuspForm 8 g
        (fun Z => siegelTheta (g + 1) twoE8 Z - siegelTheta (g + 1) gamma16 Z) := by
      refine ⟨h1.sub h2, fun Z' hZ' => ?_⟩
      have := (tendsto_siegelTheta_phiEmbed twoE8_posDef hZ').sub
        (tendsto_siegelTheta_phiEmbed gamma16_posDef hZ')
      rwa [hprev Z' hZ', sub_self] at this
    exact sub_eq_zero.mp (h.vanish g hg1 hg2 _ hcusp Z hZ)
  intro g hg Z hZ
  interval_cases g
  · simp [siegelTheta_zero]
  · exact wittIgusa_genus_one Z
  · exact step 1 le_rfl (by norm_num) (fun Z _ => wittIgusa_genus_one Z) Z hZ
  · exact step 2 (by norm_num) le_rfl
      (step 1 le_rfl (by norm_num) (fun Z _ => wittIgusa_genus_one Z)) Z hZ

end

end QuadFormsKB.ChenevierLannes
