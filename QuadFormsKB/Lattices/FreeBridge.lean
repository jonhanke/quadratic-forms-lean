/-
# Free lattices in $(F^n, Q)$ and forms over $\mathcal O_F$

**Layer:** bridge between lattices in the coordinate space $(F^n, Q)$ (`Lattices/Genus.lean`) and forms
`QuadForm (𝓞 F) n`. A *free* lattice is $\gamma\,\mathcal O_F^n$ for $\gamma \in \mathrm{GL}_n(F)$ (`latOf γ`, basis: the
columns of $\gamma$); its **Gram form** is $Q_\gamma(x) = Q(\gamma x)$ (`gramZ`, over $\mathcal O_F$ when the lattice is
integral; the abstract version is `gramForm`, `Lattices/Basic.lean`).

**Proves**
* `isIsometric_latOf_iff`: $\gamma\mathcal O_F^n \cong \delta\mathcal O_F^n$ in $(F^n, Q)$ iff the Gram forms are
  $\mathrm{GL}_n(\mathcal O_F)$-equivalent (`Siegel.IsometricGL`): **classes of free lattices = classes of forms**;
* `exists_gl_int_of_glImage_eq`: the stabilizer of $\mathcal O_F^n$ in $\mathrm{GL}_n(F)$ is $\mathrm{GL}_n(\mathcal O_F)$;
* `mem_orthGroup_of_eval`: a matrix preserving the values of $Q$ is in $O(V)(F)$;
* `eval_eq_of_eval_int`: two forms over $F$ that agree on $\mathcal O_F^n$ agree on $F^n$.
-/
import QuadFormsKB.Lattices.Forms
import QuadFormsKB.Lattices.Finite

open NumberField IsDedekindDomain Matrix WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type*} [Field F] [NumberField F] {n : ℕ}

/-! ### $\mathrm{GL}_n(\mathcal O_F)$ and the standard lattice -/

/-- The image of an integral vector, as a vector over $F$. -/
abbrev intCoe (x : Fin n → 𝓞 F) : Fin n → F := fun i => algebraMap (𝓞 F) F (x i)

theorem intCoe_mem (x : Fin n → 𝓞 F) : intCoe x ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) :=
  fun i => ⟨x i, rfl⟩

theorem mem_intVec_iff_exists {y : Fin n → F} : y ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) ↔
    ∃ x : Fin n → 𝓞 F, intCoe x = y := by
  constructor
  · intro hy
    choose x hx using hy
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩; exact intCoe_mem x

/-- The entrywise image of an integral matrix acting on integral vectors. -/
theorem map_mulVec_intCoe (P : Matrix (Fin n) (Fin n) (𝓞 F)) (x : Fin n → 𝓞 F) :
    P.map (algebraMap (𝓞 F) F) *ᵥ intCoe x = intCoe (P *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap (𝓞 F) F) P x i).symm

/-- **$\mathrm{GL}_n(\mathcal O_F)$ stabilizes $\mathcal O_F^n$.** -/
theorem glImage_map_intVec (P : GL (Fin n) (𝓞 F)) :
    glImage (GeneralLinearGroup.map (algebraMap (𝓞 F) F) P) intVec = intVec := by
  ext y
  rw [mem_glImage]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hz
    change P.val.map (algebraMap (𝓞 F) F) *ᵥ intCoe x ∈ intVec
    rw [map_mulVec_intCoe]; exact intCoe_mem _
  · intro hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hy
    refine ⟨intCoe (P⁻¹.val *ᵥ x), intCoe_mem _, ?_⟩
    change P.val.map (algebraMap (𝓞 F) F) *ᵥ intCoe (P⁻¹.val *ᵥ x) = intCoe x
    rw [map_mulVec_intCoe, mulVec_inv_mulVec]

/-- The columns of $P$ lie in $\mathcal O_F^n$ if $P\,\mathcal O_F^n \subseteq \mathcal O_F^n$. -/
theorem entries_int_of_glImage_le {P : GL (Fin n) F} (h : glImage P intVec ≤ intVec) (i j : Fin n) :
    P.val i j ∈ (algebraMap (𝓞 F) F).range := by
  have hm : P.val *ᵥ Pi.single j 1 ∈ (intVec : Submodule (𝓞 F) (Fin n → F)) :=
    h (mulVec_mem_glImage (single_one_mem_intVec j))
  simpa [mulVec_single_one] using hm i

/-- **The stabilizer of $\mathcal O_F^n$ in $\mathrm{GL}_n(F)$ is $\mathrm{GL}_n(\mathcal O_F)$.** -/
theorem exists_gl_int_of_glImage_eq {P : GL (Fin n) F} (h : glImage P intVec = intVec) :
    ∃ P₀ : GL (Fin n) (𝓞 F), GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀ = P := by
  have h' : glImage P⁻¹ intVec = intVec := by
    conv_lhs => rw [← h]
    rw [← glImage_mul, inv_mul_cancel, glImage_one]
  choose A hA using entries_int_of_glImage_le h.le
  choose B hB using entries_int_of_glImage_le h'.le
  have hAm : (Matrix.of A).map (algebraMap (𝓞 F) F) = P.val := by
    ext i j; simp only [Matrix.map_apply, Matrix.of_apply]; exact hA i j
  have hBm : (Matrix.of B).map (algebraMap (𝓞 F) F) = P⁻¹.val := by
    ext i j; simp only [Matrix.map_apply, Matrix.of_apply]; exact hB i j
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) (𝓞 F) => M.map (algebraMap (𝓞 F) F)) :=
    fun M M' hMM => Matrix.ext fun i j =>
      IsFractionRing.injective (𝓞 F) F (congrFun (congrFun hMM i) j)
  have hAB : Matrix.of A * Matrix.of B = 1 := hinj (by
    simp only [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : Matrix.of B * Matrix.of A = 1 := hinj (by
    simp only [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, Units.ext hAm⟩

/-! ### Values of forms -/

variable (Q : QuadForm F n)

/-- **Value-preserving matrices are isometries:** if $Q(\rho z) = Q(z)$ for all $z \in F^n$ then
$\rho^{\mathsf T} H \rho = H$ (polarize). -/
theorem mem_orthGroup_of_eval {ρ : GL (Fin n) F} (h : ∀ z, Q.eval (ρ.val *ᵥ z) = Q.eval z) :
    ρ ∈ orthGroup Q F := by
  rw [mem_orthGroup]
  have e : Q.hessian.map (algebraMap F F) = Q.hessian := by ext; simp
  rw [e]
  ext i j
  have hp := QuadForm.polar_eq_hessian F Q (ρ.val *ᵥ Pi.single i 1) (ρ.val *ᵥ Pi.single j 1)
  have hp' := QuadForm.polar_eq_hessian F Q (Pi.single i 1) (Pi.single j 1)
  rw [← mulVec_add] at hp
  simp only [QuadForm.eval] at h
  rw [h, h, h, hp', e] at hp
  rw [← single_dotProduct_mulVec_single (ρ.valᵀ * Q.hessian * ρ.val) i j,
    ← single_dotProduct_mulVec_single Q.hessian i j, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]
  exact hp.symm

/-- **Forms agreeing on $\mathcal O_F^n$ agree on $F^n$** (clear denominators; both sides are homogeneous of
degree 2). -/
theorem eval_eq_of_eval_int {A B : QuadForm F n} (h : ∀ x : Fin n → 𝓞 F, A.eval (intCoe x) = B.eval (intCoe x))
    (y : Fin n → F) : A.eval y = B.eval y := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_mem_intVec y
  obtain ⟨x, hx⟩ := mem_intVec_iff_exists.mp hc
  have hc' : algebraMap (𝓞 F) F c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have e : c • y = (algebraMap (𝓞 F) F c) • y := (algebraMap_smul F c y).symm
  have h1 := h x
  rw [hx, e] at h1
  simp only [QuadForm.eval] at h1 ⊢
  rw [evalIn_smul', evalIn_smul'] at h1
  exact mul_left_cancel₀ (pow_ne_zero 2 hc') h1

/-! ### Free lattices and their Gram forms -/

/-- **The free lattice** $\gamma\,\mathcal O_F^n$ with basis the columns of $\gamma \in \mathrm{GL}_n(F)$. -/
def latOf (γ : GL (Fin n) F) : Submodule (𝓞 F) (Fin n → F) := glImage γ intVec

theorem latOf_isLattice (γ : GL (Fin n) F) : (latOf γ).IsLattice F :=
  glImage_isLattice γ intVec_isLattice

theorem isIntegralLattice_iff (L : Submodule (𝓞 F) (Fin n → F)) :
    IsIntegralLattice Q.toQuadraticForm L ↔ IsIntegral Q L := by
  simp only [IsIntegralLattice, IsIntegral, QuadForm.toQuadraticForm_apply]

theorem sum_smul_col (γ : GL (Fin n) F) (y : Fin n → F) :
    ∑ j, y j • (γ.val *ᵥ Pi.single j 1) = γ.val *ᵥ y := by
  conv_rhs => rw [← Finset.univ_sum_single y]
  rw [mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]

theorem eval_gramFormF_col (γ : GL (Fin n) F) (y : Fin n → F) :
    (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).eval y = Q.eval (γ.val *ᵥ y) := by
  rw [eval_gramFormF, sum_smul_col, QuadForm.toQuadraticForm_apply]

theorem evalIn_gramFormF_col (γ : GL (Fin n) F) (y : Fin n → F) :
    (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).evalIn F y =
      Q.evalIn F (γ.val *ᵥ y) := eval_gramFormF_col Q γ y

/-- **The Gram form** $Q_\gamma \in$ `QuadForm (𝓞 F) n` of an integral free lattice $\gamma\mathcal O_F^n$:
$Q_\gamma(x) = Q(\gamma x)$ for $x \in \mathcal O_F^n$ (`algebraMap_eval_gramZ`). -/
@[kb "omeara1963" "§82B, p. 221 (matrix of a free lattice)"]
def gramZ (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) : QuadForm (𝓞 F) n :=
  QuadForm.ofUpper fun i j => (gramFormF_coeff_mem Q.toQuadraticForm ((isIntegralLattice_iff Q _).mpr h)
    (b := fun j => γ.val *ᵥ Pi.single j 1) (fun j => mulVec_mem_glImage (single_one_mem_intVec j)) i j).choose

theorem gramZ_map (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) :
    (gramZ Q γ h).map (algebraMap (𝓞 F) F) = gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1) := by
  ext i j
  simp only [gramZ, QuadForm.map, QuadForm.ofUpper, Matrix.map_apply, Matrix.of_apply]
  split_ifs with hij
  · exact (gramFormF_coeff_mem Q.toQuadraticForm ((isIntegralLattice_iff Q _).mpr h)
      (b := fun j => γ.val *ᵥ Pi.single j 1) (fun j => mulVec_mem_glImage (single_one_mem_intVec j)) i j).choose_spec
  · rw [map_zero, (gramFormF _ _).upper (show j < i from not_le.mp hij)]

/-- $Q_\gamma(x) = Q(\gamma x)$. -/
theorem algebraMap_eval_gramZ (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) (x : Fin n → 𝓞 F) :
    algebraMap (𝓞 F) F ((gramZ Q γ h).eval x) = Q.eval (γ.val *ᵥ intCoe x) := by
  rw [← eval_map_comp, gramZ_map, eval_gramFormF_col]

/-- **Classes of free lattices are classes of forms:** $\gamma\mathcal O_F^n$ and $\delta\mathcal O_F^n$ are isometric in
$(F^n, Q)$ iff their Gram forms are $\mathrm{GL}_n(\mathcal O_F)$-equivalent, $Q_\delta(Px) = Q_\gamma(x)$ for some
$P \in \mathrm{GL}_n(\mathcal O_F)$. -/
@[kb "omeara1963" "§82B, 82:1 (2), p. 222; cassels1978 Ch. 7, §2, p. 103 (forms and lattices); Ch. 11, Lemma 1.1, p. 197"]
theorem isIsometric_latOf_iff (γ δ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    (hδ : IsIntegral Q (latOf δ)) :
    IsIsometric Q (latOf γ) (latOf δ) ↔ Siegel.IsometricGL (gramZ Q δ hδ) (gramZ Q γ hγ) := by
  constructor
  · rintro ⟨ρ, hρ, he⟩
    have hP : glImage (δ⁻¹ * ρ * γ) intVec = intVec := by
      rw [glImage_mul, glImage_mul]
      change glImage δ⁻¹ (glImage ρ (latOf γ)) = intVec
      rw [he, latOf, ← glImage_mul, inv_mul_cancel, glImage_one]
    obtain ⟨P₀, hP₀⟩ := exists_gl_int_of_glImage_eq hP
    refine ⟨P₀, fun x => IsFractionRing.injective (𝓞 F) F ?_⟩
    rw [algebraMap_eval_gramZ, algebraMap_eval_gramZ, ← map_mulVec_intCoe]
    have e : P₀.val.map (algebraMap (𝓞 F) F) = (δ⁻¹ * ρ * γ).val := congrArg Units.val hP₀
    rw [e, mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      Units.val_mul, ← mulVec_mulVec]
    exact evalIn_mulVec_of_mem Q hρ _
  · rintro ⟨P₀, hP₀⟩
    set P := GeneralLinearGroup.map (algebraMap (𝓞 F) F) P₀
    have hval : ∀ y, Q.eval (δ.val *ᵥ (P.val *ᵥ y)) = Q.eval (γ.val *ᵥ y) := by
      have hA : ∀ x : Fin n → 𝓞 F, (gramFormF Q.toQuadraticForm (fun j => δ.val *ᵥ Pi.single j 1)).eval
          (P.val *ᵥ intCoe x) = (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).eval
          (intCoe x) := by
        intro x
        have e : P.val *ᵥ intCoe x = intCoe (P₀.val *ᵥ x) := map_mulVec_intCoe _ x
        rw [e, ← gramZ_map Q δ hδ, ← gramZ_map Q γ hγ, eval_map_comp, eval_map_comp, hP₀]
      intro y
      have e1 : Q.eval (δ.val *ᵥ (P.val *ᵥ y)) = (gramFormF Q.toQuadraticForm
          (fun j => δ.val *ᵥ Pi.single j 1)).eval (P.val *ᵥ y) := (eval_gramFormF_col Q δ _).symm
      have e2 : Q.eval (γ.val *ᵥ y) = (gramFormF Q.toQuadraticForm
          (fun j => γ.val *ᵥ Pi.single j 1)).eval y := (eval_gramFormF_col Q γ y).symm
      rw [e1, e2]
      -- the form `y ↦ Q_δ(P y)` over `F`
      let A : QuadForm F n := gramFormF Q.toQuadraticForm (fun j => (δ * P).val *ᵥ Pi.single j 1)
      have hAe : ∀ z, A.eval z = (gramFormF Q.toQuadraticForm (fun j => δ.val *ᵥ Pi.single j 1)).eval
          (P.val *ᵥ z) := by
        intro z
        rw [eval_gramFormF_col, eval_gramFormF_col, Units.val_mul, mulVec_mulVec]
      rw [← hAe]
      refine eval_eq_of_eval_int (fun x => ?_) y
      rw [hAe, hA]
    refine ⟨δ * P * γ⁻¹, mem_orthGroup_of_eval Q fun z => ?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hval, mulVec_inv_mulVec]
    · rw [latOf, ← glImage_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, glImage_mul,
        glImage_map_intVec]
      rfl

/-! ### The genus of free lattices is the genus of their Gram forms -/

/-- **Value-preserving matrices are isometries** over any $F$-algebra $R$. -/
theorem mem_orthGroup_of_evalIn {R : Type*} [CommRing R] [Algebra F R] {ρ : GL (Fin n) R}
    (h : ∀ z, Q.evalIn R (ρ.val *ᵥ z) = Q.evalIn R z) : ρ ∈ orthGroup Q R := by
  rw [mem_orthGroup]
  ext i j
  have hp := QuadForm.polar_eq_hessian R Q (ρ.val *ᵥ Pi.single i 1) (ρ.val *ᵥ Pi.single j 1)
  have hp' := QuadForm.polar_eq_hessian R Q (Pi.single i 1) (Pi.single j 1)
  rw [← mulVec_add, h, h, h, hp'] at hp
  have e1 : ∀ A : Matrix (Fin n) (Fin n) R, A i j = Pi.single i (1 : R) ⬝ᵥ (A *ᵥ Pi.single j 1) := by
    intro A; simp
  rw [e1 (ρ.valᵀ * _ * ρ.val), e1 (Q.hessian.map (algebraMap F R)), ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]
  exact hp.symm

/-- The Hessian of $y \mapsto Q(\gamma y)$ is $\gamma^{\mathsf T} H \gamma$. -/
theorem hessian_gramF (γ : GL (Fin n) F) :
    (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).hessian = γ.valᵀ * Q.hessian * γ.val := by
  ext i j
  have hp := QuadForm.polar_eq_hessian F (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1))
    (Pi.single i 1) (Pi.single j 1)
  have hq := QuadForm.polar_eq_hessian F Q (γ.val *ᵥ Pi.single i 1) (γ.val *ᵥ Pi.single j 1)
  rw [evalIn_gramFormF_col, evalIn_gramFormF_col, evalIn_gramFormF_col, mulVec_add] at hp
  rw [hp] at hq
  have e : ∀ A : Matrix (Fin n) (Fin n) F, A.map (algebraMap F F) = A := fun A => by ext; simp
  rw [e, e] at hq
  rw [← single_dotProduct_mulVec_single
      (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).hessian i j, hq,
    ← single_dotProduct_mulVec_single (γ.valᵀ * Q.hessian * γ.val) i j,
    ← mulVec_mulVec, ← mulVec_mulVec]
  conv_rhs => rw [dotProduct_mulVec, vecMul_transpose]

/-- **$Q(\gamma\,\cdot)$ over an extension:** $(Q \circ \gamma)(z) = Q(\gamma z)$ for $z \in R^n$, $R$ an $F$-algebra domain of
characteristic $0$ (e.g. $F_\mathfrak p$, $\mathbb R$). -/
theorem evalIn_gramF (γ : GL (Fin n) F) {R : Type*} [CommRing R] [Algebra F R] [IsDomain R] [CharZero R]
    (z : Fin n → R) :
    (gramFormF Q.toQuadraticForm (fun j => γ.val *ᵥ Pi.single j 1)).evalIn R z =
      Q.evalIn R (γ.val.map (algebraMap F R) *ᵥ z) := by
  apply mul_left_cancel₀ (two_ne_zero (α := R))
  rw [two_mul_evalIn, two_mul_evalIn, hessian_gramF, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- Evaluation over an $R$-algebra is evaluation of the base change. -/
theorem evalIn_eq_eval_map {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] (B : QuadForm A n)
    (z : Fin n → K) : B.evalIn K z = (B.map (algebraMap A K)).eval z := by
  simp [QuadForm.evalIn, QuadForm.map]

section LocalFree

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

theorem mulVec_mem_std {A : Matrix (Fin n) (Fin n) Fv} (hA : ∀ i j, Valued.v (A i j) ≤ 1)
    {y : Fin n → Fv} (hy : y ∈ std v) : A *ᵥ y ∈ std v := by
  intro i
  rw [mulVec, dotProduct, neg_zero, exp_zero]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  have := hy j
  rw [neg_zero, exp_zero] at this
  exact mul_le_one' (hA i j) this

theorem single_one_mem_std (j : Fin n) : (Pi.single j (1 : Fv) : Fin n → Fv) ∈ std v := by
  intro i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- **$\mathrm{GL}_n(\mathfrak o_\mathfrak p)$ stabilizes $\mathfrak o_\mathfrak p^n$.** -/
theorem locAct_map_std (P : GL (Fin n) 𝔬) :
    locAct v (GeneralLinearGroup.map (algebraMap 𝔬 Fv) P) (std v) = std v := by
  have hint : ∀ (B : Matrix (Fin n) (Fin n) 𝔬) i j, Valued.v ((B.map (algebraMap 𝔬 Fv)) i j) ≤ 1 :=
    fun B i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (B i j).2
  ext y
  rw [mem_locAct]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mulVec_mem_std v (hint P.val) hz
  · intro hy
    refine ⟨(GeneralLinearGroup.map (algebraMap 𝔬 Fv) P)⁻¹.val *ᵥ y, ?_, mulVec_inv_mulVec _ y⟩
    rw [← map_inv]
    exact mulVec_mem_std v (hint P⁻¹.val) hy

/-- **The stabilizer of $\mathfrak o_\mathfrak p^n$ in $\mathrm{GL}_n(F_\mathfrak p)$ is $\mathrm{GL}_n(\mathfrak o_\mathfrak p)$.** -/
theorem exists_gl_o_of_locAct_eq {P : GL (Fin n) Fv} (h : locAct v P (std v) = std v) :
    ∃ P₀ : GL (Fin n) 𝔬, GeneralLinearGroup.map (algebraMap 𝔬 Fv) P₀ = P := by
  have h' : locAct v P⁻¹ (std v) = std v := by
    conv_lhs => rw [← h]
    rw [locAct_inv_locAct]
  have hent : ∀ {R : GL (Fin n) Fv}, locAct v R (std v) = std v → ∀ i j, Valued.v (R.val i j) ≤ 1 := by
    intro R hR i j
    have hm : R.val *ᵥ Pi.single j 1 ∈ std v := hR ▸ ⟨_, single_one_mem_std v j, rfl⟩
    have := hm i
    rw [neg_zero, exp_zero] at this
    simpa [mulVec_single_one] using this
  set A : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun i j => toO v _ (hent h i j)
  set B : Matrix (Fin n) (Fin n) 𝔬 := Matrix.of fun i j => toO v _ (hent h' i j)
  have hAm : A.map (algebraMap 𝔬 Fv) = P.val := by ext i j; rfl
  have hBm : B.map (algebraMap 𝔬 Fv) = P⁻¹.val := by ext i j; rfl
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) 𝔬 => M.map (algebraMap 𝔬 Fv)) :=
    fun M M' hMM => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMM i) j)
  have hAB : A * B = 1 := hinj (by
    simp only [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
  have hBA : B * A = 1 := hinj (by
    simp only [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAm⟩

/-- The values of the Gram form over $\mathfrak o_\mathfrak p$: $Q_\gamma(x) = Q(\gamma x)$ in $F_\mathfrak p$. -/
theorem coe_eval_gramZ_map (γ : GL (Fin n) F) (h : IsIntegral Q (latOf γ)) (x : Fin n → 𝔬) :
    (((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).eval x : Fv) =
      Q.evalIn Fv (γ.val.map (algebraMap F Fv) *ᵥ fun i => (x i : Fv)) := by
  have e1 := eval_map_comp (algebraMap 𝔬 Fv) ((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)) x
  have e2 : ((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).map (algebraMap 𝔬 Fv) =
      ((gramZ Q γ h).map (algebraMap (𝓞 F) F)).map (algebraMap F Fv) := by
    have e3 : (algebraMap 𝔬 Fv).comp (algebraMap (𝓞 F) 𝔬) = (algebraMap F Fv).comp (algebraMap (𝓞 F) F) :=
      RingHom.ext fun a => rfl
    rw [QuadForm.map_map, QuadForm.map_map, e3]
  calc ((((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).eval x : 𝔬) : Fv)
      = algebraMap 𝔬 Fv (((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).eval x) := rfl
    _ = (((gramZ Q γ h).map (algebraMap (𝓞 F) 𝔬)).map (algebraMap 𝔬 Fv)).eval
          (fun i => algebraMap 𝔬 Fv (x i)) := e1.symm
    _ = Q.evalIn Fv (γ.val.map (algebraMap F Fv) *ᵥ fun i => (x i : Fv)) := by
      rw [e2, gramZ_map, ← evalIn_eq_eval_map, evalIn_gramF]; rfl

/-- Two forms over $F$, evaluated over $F_\mathfrak p$, that agree on $\mathfrak o_\mathfrak p^n$ agree on $F_\mathfrak p^n$. -/
theorem evalIn_eq_of_evalIn_o {A B : (Fin n → Fv) → Fv}
    (hA : ∀ (c : Fv) y, A (c • y) = c ^ 2 * A y) (hB : ∀ (c : Fv) y, B (c • y) = c ^ 2 * B y)
    (h : ∀ x : Fin n → 𝔬, A (fun i => (x i : Fv)) = B (fun i => (x i : Fv))) (y : Fin n → Fv) :
    A y = B y := by
  classical
  choose k hk using fun i => exists_valued_le v (y i)
  set K : ℕ := Finset.univ.sup k
  have hc : ∀ i, Valued.v (ϖk v K * y i) ≤ 1 := by
    intro i
    rw [map_mul, valued_ϖk]
    calc exp (-(K : ℤ)) * Valued.v (y i) ≤ exp (-(K : ℤ)) * exp (k i : ℤ) := mul_le_mul_right (hk i) _
      _ ≤ 1 := by
        rw [← exp_add, ← exp_zero, exp_le_exp]
        have : k i ≤ K := Finset.le_sup (Finset.mem_univ i)
        omega
  have h1 := h fun i => toO v _ (hc i)
  have e : (fun i => ((toO v _ (hc i) : 𝔬) : Fv)) = ϖk v K • y := by funext i; rfl
  rw [e, hA, hB] at h1
  exact mul_left_cancel₀ (pow_ne_zero 2 (ϖk_ne_zero v K)) h1

end LocalFree

/-- **The genus of free lattices is the genus of their Gram forms:** $\gamma\mathcal O_F^n$ and $\delta\mathcal O_F^n$ are in
the same genus in $(F^n, Q)$ iff the Gram forms $Q_\gamma, Q_\delta$ are in the same genus over $\mathcal O_F$
(`FormSameGenus`). With `formSameGenus_rat_iff` this identifies the lattice genus over $\mathbb Q$ with
`Siegel.SameGenus`. -/
@[kb "omeara1963" "§102A, p. 297; §82B, 82:1, p. 222; cassels1978 Ch. 7, §2, p. 103 (forms and lattices); Ch. 11, Lemma 1.1, p. 197"]
theorem sameGenus_latOf_iff (γ δ : GL (Fin n) F) (hγ : IsIntegral Q (latOf γ))
    (hδ : IsIntegral Q (latOf δ)) :
    SameGenus Q (latOf γ) (latOf δ) ↔ FormSameGenus (gramZ Q γ hγ) (gramZ Q δ hδ) := by
  have hloc : ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GL (Fin n) F),
      loc v (latOf ε) = locAct v (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) ε) (std v) :=
    fun v ε => by rw [latOf, loc_glImage, loc_intVec]
  constructor
  · intro h
    refine ⟨fun v => ?_, fun σ => ?_⟩
    · obtain ⟨g, hg, he⟩ := h v
      set γv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ
      set δv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) δ
      rw [hloc, hloc] at he
      have hP : locAct v (γv⁻¹ * g⁻¹ * δv) (std v) = std v := by
        rw [locAct_mul, locAct_mul, ← he, locAct_inv_locAct, locAct_inv_locAct]
      obtain ⟨P₀, hP₀⟩ := exists_gl_o_of_locAct_eq v hP
      refine ⟨P₀, fun x => Subtype.ext ?_⟩
      rw [coe_eval_gramZ_map, coe_eval_gramZ_map]
      have e : (fun i => ((P₀.val *ᵥ x) i : v.adicCompletion F)) =
          P₀.val.map (algebraMap _ (v.adicCompletion F)) *ᵥ fun i => (x i : v.adicCompletion F) := by
        funext i; exact RingHom.map_mulVec (algebraMap _ (v.adicCompletion F)) P₀.val x i
      rw [e, show P₀.val.map (algebraMap _ (v.adicCompletion F)) = (γv⁻¹ * g⁻¹ * δv).val from
        congrArg Units.val hP₀]
      change Q.evalIn _ (γv.val *ᵥ ((γv⁻¹ * g⁻¹ * δv).val *ᵥ _)) = Q.evalIn _ (δv.val *ᵥ _)
      rw [mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
        Units.val_mul, ← mulVec_mulVec]
      exact evalIn_mulVec_of_mem Q ((orthGroup Q _).inv_mem hg) _
    · let _ : Algebra F ℝ := σ.toAlgebra
      have hσ : algebraMap F ℝ = σ := rfl
      have hval : ∀ (ε : GL (Fin n) F) (hε : IsIntegral Q (latOf ε)) (w : Fin n → ℝ),
          ((gramZ Q ε hε).map (σ.comp (algebraMap (𝓞 F) F))).eval w =
            Q.evalIn ℝ (ε.val.map σ *ᵥ w) := by
        intro ε hε w
        rw [← QuadForm.map_map, gramZ_map, ← hσ, ← evalIn_eq_eval_map, evalIn_gramF]
      refine ⟨GeneralLinearGroup.map σ (γ⁻¹ * δ), fun z => ?_⟩
      rw [hval, hval]
      change Q.evalIn ℝ (γ.val.map σ *ᵥ ((γ⁻¹ * δ).val.map σ *ᵥ z)) = _
      rw [mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  · rintro ⟨hfin, -⟩ v
    obtain ⟨P₀, hP₀⟩ := hfin v
    set γv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ
    set δv := GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) δ
    set P := GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) P₀
    have hval : ∀ y, Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)) = Q.evalIn _ (δv.val *ᵥ y) := by
      refine evalIn_eq_of_evalIn_o v (A := fun y => Q.evalIn _ (γv.val *ᵥ (P.val *ᵥ y)))
        (B := fun y => Q.evalIn _ (δv.val *ᵥ y)) (fun c y => ?_) (fun c y => ?_) (fun x => ?_)
      · simp only [mulVec_smul, evalIn_smul']
      · simp only [mulVec_smul, evalIn_smul']
      · have h1 := congrArg (fun t : v.adicCompletionIntegers F => (t : v.adicCompletion F)) (hP₀ x)
        rw [coe_eval_gramZ_map, coe_eval_gramZ_map] at h1
        have e : (P.val *ᵥ fun i => ((x i : v.adicCompletionIntegers F) : v.adicCompletion F)) =
            fun i => (((P₀.val *ᵥ x) i : v.adicCompletionIntegers F) : v.adicCompletion F) := by
          funext i; exact (RingHom.map_mulVec (algebraMap _ (v.adicCompletion F)) P₀.val x i).symm
        change Q.evalIn _ (γ.val.map (algebraMap F _) *ᵥ (P.val *ᵥ _)) =
          Q.evalIn _ (δ.val.map (algebraMap F _) *ᵥ _)
        rw [e]; exact h1
    refine ⟨δv * P⁻¹ * γv⁻¹, mem_orthGroup_of_evalIn Q fun z => ?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, ← hval, mulVec_inv_mulVec,
        mulVec_inv_mulVec]
    · rw [hloc, hloc, ← locAct_mul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, locAct_mul,
        show P⁻¹ = GeneralLinearGroup.map (algebraMap _ (v.adicCompletion F)) P₀⁻¹ from (map_inv _ _).symm,
        locAct_map_std]

end QuadFormsKB.Lattices
