import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Binary.SiegelBinaryF
import QuadFormsKB.Binary.RelGenusHilbert

/-!
# The discriminant tower and the determinant of the norm lattice

Let $E/F$ be an extension of number fields and $b = (b_j)_{j \in \kappa}$ a basis of $\mathcal O_E$ as an $\mathcal O_F$-module (when $\mathcal O_E$ is
free over $\mathcal O_F$). With the relative discriminant $\Delta_{E/F}(b) = \det\big(\mathrm{Tr}_{E/F}(b_jb_l)\big) \in F$ (Mathlib's
`Algebra.discr F b`):

* **The discriminant tower** (`discr_tower`): $d_E = d_F^{\,[E:F]}\cdot N_{F/\mathbb Q}(\Delta_{E/F}(b))$, an identity of integers (no absolute
  values). Proof: the products $c_ib_j$ ($c$ a $\mathbb Z$-basis of $\mathcal O_F$) form a $\mathbb Z$-basis of $\mathcal O_E$ (Mathlib's `Basis.smulTower'`); its
  trace matrix factors as $(1 \otimes G_F)\cdot\mathcal A$, $G_F$ the trace matrix of $c$ and $\mathcal A$ the $\mathbb Q$-matrix of the $F$-linear map
  $\big(\mathrm{Tr}_{E/F}(b_jb_l)\big)$ on $F^\kappa$; $\det\mathcal A = N_{F/\mathbb Q}(\Delta)$ is Mathlib's `Matrix.det_det` (determinant of a block matrix with
  commuting blocks). Mathlib has only the ideal form `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`.
* **The norm form in the basis $b$** ($[E:F] = 2$; `normFormBasis`, `normFormBasis_eval`):
  $Q_b(x_0, x_1) = N_{E/F}(x_0b_0 + x_1b_1) = N(b_0)x_0^2 + \mathrm{Tr}(b_0\sigma b_1)x_0x_1 + N(b_1)x_1^2$, a binary form over $\mathcal O_F$. Its Hessian
  determinant is $4N(b_0)N(b_1) - \mathrm{Tr}(b_0\sigma b_1)^2 = -\Delta_{E/F}(b)$ (`hessian_det_normFormBasis`), so
  $D_w = \det(H_w/2) = -\sigma_w(\Delta)/4$ at each real place $w$.
* **`hasNormLatticeDet`**: for a CM field $K$, $F = K^+$, and any $\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$, $Q_b$ is totally positive definite
  (`isTotallyPosDef_normFormBasis`; $N_{K/K^+}(x) = |x|^2$ under every embedding) and satisfies the condition
  `HasNormLatticeDet`: $\prod_w D_w = |d_K|/(4^d|d_{K^+}|^2)$. Hence **`siegelConstant_binaryF_basis`**: the Siegel constant
  holds for the norm lattice with no condition left.

Sources: Neukirch, *Algebraic Number Theory*, Ch. III §2, Cor. 2.10 (discriminant tower) [unverified locator]; Fröhlich–Taylor
[not in the bibliography]; Hanke 2004, (5.5).
-/

open NumberField Module Filter Topology Matrix
open scoped Kronecker

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Binary.Rel

/-! ### The discriminant tower $d_E = d_F^{[E:F]}\,N_{F/\mathbb Q}(\Delta_{E/F}(b))$ -/

section Tower

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsScalarTower ℚ F E]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- $\mathrm{Tr}_{E/\mathbb Q}(a\,y) = \mathrm{Tr}_{F/\mathbb Q}(a\,\mathrm{Tr}_{E/F}(y))$ for $a \in F$, $y \in E$. -/
theorem trace_algebraMap_mul (a : F) (y : E) :
    Algebra.trace ℚ E (algebraMap F E a * y) = Algebra.trace ℚ F (a * Algebra.trace F E y) := by
  rw [← Algebra.trace_trace (S := F), ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **The discriminant tower** for an extension $E/F$ of number fields with $\mathcal O_E$ free over $\mathcal O_F$ (basis $b$):
$$d_E = d_F^{\,|\kappa|}\cdot N_{F/\mathbb Q}\big(\Delta_{E/F}(b)\big),\qquad \Delta_{E/F}(b) = \det\big(\mathrm{Tr}_{E/F}(b_jb_l)\big)_{j,l}.$$ -/
@[kb "neukirch1999" "Ch. III §2, Cor. 2.10 [unverified]"]
theorem discr_tower (b : Basis κ (𝓞 F) (𝓞 E)) :
    (discr E : ℚ) = (discr F : ℚ) ^ Fintype.card κ *
      Algebra.norm ℚ (Algebra.discr F (fun j => ((b j : 𝓞 E) : E))) := by
  classical
  set ι := Free.ChooseBasisIndex ℤ (𝓞 F)
  set cF : Basis ι ℚ F := integralBasis F
  set B := (RingOfIntegers.basis F).smulTower' b
  -- d_E = discr ℚ of the product basis
  have hE : (discr E : ℚ) =
      Algebra.discr ℚ (fun k : κ × ι => algebraMap F E (cF k.2) * ((b k.1 : 𝓞 E) : E)) := by
    rw [← discr_eq_discr E B, ← eq_intCast (algebraMap ℤ ℚ),
      ← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) E B]
    congr 1
    funext k
    rw [Basis.localizationLocalization_apply, Basis.smulTower'_apply, integralBasis_apply, Algebra.smul_def,
      map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have hF : (discr F : ℚ) = Algebra.discr ℚ cF := coe_discr F
  let T : Matrix κ κ F := Algebra.traceMatrix F (fun j => ((b j : 𝓞 E) : E))
  let G : Matrix ι ι ℚ := Algebra.traceMatrix ℚ cF
  let f : F →+* Matrix ι ι ℚ := (Algebra.leftMulMatrix cF).toRingHom
  let 𝒜 : Matrix (κ × ι) (κ × ι) ℚ := Matrix.comp κ κ ι ι ℚ (T.map f)
  have hM : Algebra.traceMatrix ℚ (fun k : κ × ι => algebraMap F E (cF k.2) * ((b k.1 : 𝓞 E) : E)) =
      ((1 : Matrix κ κ ℚ) ⊗ₖ G) * 𝒜 := by
    ext ⟨j, i⟩ ⟨l, k⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single j (fun j' _ hj' => Finset.sum_eq_zero
      fun m _ => by rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hj'), zero_mul, zero_mul])
      (fun h => absurd (Finset.mem_univ j) h)]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
    change Algebra.traceForm ℚ E _ _ = ∑ m, Algebra.traceForm ℚ F (cF i) (cF m) *
      Algebra.leftMulMatrix cF (Algebra.traceForm F E ((b j : 𝓞 E) : E) ((b l : 𝓞 E) : E)) m k
    simp only [Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
    rw [show algebraMap F E (cF i) * ((b j : 𝓞 E) : E) * (algebraMap F E (cF k) * ((b l : 𝓞 E) : E)) =
        algebraMap F E (cF i * cF k) * (((b j : 𝓞 E) : E) * ((b l : 𝓞 E) : E)) by rw [map_mul]; ring,
      trace_algebraMap_mul]
    set t := Algebra.trace F E (((b j : 𝓞 E) : E) * ((b l : 𝓞 E) : E))
    conv_lhs => rw [show cF i * cF k * t = cF i * (t * cF k) by ring, ← cF.sum_repr (t * cF k)]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.smul_def, show cF i * (algebraMap ℚ F (cF.repr (t * cF k) m) * cF m) =
        algebraMap ℚ F (cF.repr (t * cF k) m) * (cF i * cF m) by ring, ← Algebra.smul_def, map_smul,
      smul_eq_mul, mul_comm]
  have hA : 𝒜.det = Algebra.norm ℚ (Algebra.discr F (fun j => ((b j : 𝓞 E) : E))) := by
    rw [Algebra.norm_eq_matrix_det cF, Algebra.discr_def]
    exact (Matrix.det_det T f).symm
  rw [hE, hF, Algebra.discr_def, hM, Matrix.det_mul, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul,
    hA, Algebra.discr_def]
  rfl

end Tower

/-! ### The norm form in an $\mathcal O_F$-basis of $\mathcal O_E$ -/

section NormFormBasis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

theorem evalIn_ofUpper_two {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (c : Fin 2 → Fin 2 → R)
    (x : Fin 2 → K) :
    (QuadForm.ofUpper c).evalIn K x =
      algebraMap R K (c 0 0) * x 0 ^ 2 + algebraMap R K (c 0 1) * x 0 * x 1 + algebraMap R K (c 1 1) * x 1 ^ 2 := by
  simp [QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_two]
  ring

variable (b : Basis (Fin 2) (𝓞 F) (𝓞 E))

/-- **The norm form of $\mathcal O_E$ in the $\mathcal O_F$-basis $b$:** $Q_b(x_0, x_1) = N(b_0)x_0^2 + \mathrm{Tr}(b_0\sigma b_1)x_0x_1 + N(b_1)x_1^2$
(`Algebra.intNorm`, `Algebra.intTrace`), so that $Q_b(x) = N_{E/F}(x_0b_0 + x_1b_1)$ (`normFormBasis_eval`). -/
@[kb "omeara1963" "§57 (norm form) [unverified]; hanke2004 §5"]
def normFormBasis : QuadForm (𝓞 F) 2 :=
  QuadForm.ofUpper ![![Algebra.intNorm (𝓞 F) (𝓞 E) (b 0), Algebra.intTrace (𝓞 F) (𝓞 E) (b 0 * conjO F E (b 1))],
    ![0, Algebra.intNorm (𝓞 F) (𝓞 E) (b 1)]]

theorem algebraMap_intTrace' (x : 𝓞 E) :
    algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) x) = Algebra.trace F E (algebraMap (𝓞 E) E x) :=
  Algebra.algebraMap_intTrace (L := E) x

theorem algebraMap_algebraMap_intTrace (x : 𝓞 E) :
    algebraMap F E (algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) x)) =
      algebraMap (𝓞 E) E x + conj F E (algebraMap (𝓞 E) E x) := by
  rw [algebraMap_intTrace', algebraMap_trace]

theorem algebraMap_algebraMap_intNorm (x : 𝓞 E) :
    algebraMap F E (algebraMap (𝓞 F) F (Algebra.intNorm (𝓞 F) (𝓞 E) x)) =
      algebraMap (𝓞 E) E x * conj F E (algebraMap (𝓞 E) E x) := by
  rw [algebraMap_intNorm', nrm, algebraMap_norm]

theorem algebraMap_smul_O (a : 𝓞 F) (y : 𝓞 E) :
    algebraMap (𝓞 E) E (a • y) = algebraMap F E (algebraMap (𝓞 F) F a) * algebraMap (𝓞 E) E y := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]

/-- **$Q_b$ is the norm form:** $Q_b(x_0, x_1) = N_{E/F}(x_0b_0 + x_1b_1)$ for $x_0, x_1 \in \mathcal O_F$. -/
@[kb "omeara1963" "§57 [unverified]"]
theorem normFormBasis_eval (x : Fin 2 → 𝓞 F) :
    (normFormBasis b).eval x = Algebra.intNorm (𝓞 F) (𝓞 E) (x 0 • b 0 + x 1 • b 1) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  apply (algebraMap F E).injective
  rw [QuadForm.eval, normFormBasis, evalIn_ofUpper_two, algebraMap_algebraMap_intNorm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.algebraMap_self_apply, map_add, map_mul,
    map_pow, algebraMap_algebraMap_intNorm, algebraMap_algebraMap_intTrace, algebraMap_smul_O, algebraMap_conjO,
    conj_algebraMap, conj_conj]
  ring

/-- **The Hessian determinant of $Q_b$ is $-\Delta_{E/F}(b)$:** $4N(b_0)N(b_1) - \mathrm{Tr}(b_0\sigma b_1)^2 = -\det(\mathrm{Tr}_{E/F}(b_jb_l))$. -/
@[kb "omeara1963" "§57 [unverified]"]
theorem hessian_det_normFormBasis :
    algebraMap (𝓞 F) F (normFormBasis b).hessian.det = -Algebra.discr F (fun j => ((b j : 𝓞 E) : E)) := by
  apply (algebraMap F E).injective
  rw [Algebra.discr_def, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [normFormBasis, QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  simp only [Fin.isValue, le_refl, if_true, Fin.zero_le, Fin.one_pos.not_ge, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero, zero_add, map_sub, map_mul, map_add, map_neg,
    algebraMap_algebraMap_intNorm, algebraMap_algebraMap_intTrace, algebraMap_trace, algebraMap_conjO,
    conj_conj]
  ring

/-- The Hessian determinant of $Q_b$ is the relative norm of $\theta_b = b_0\sigma(b_1) - \sigma(b_0)b_1$ (note $\sigma\theta_b = -\theta_b$). -/
theorem hessian_det_normFormBasis_eq_norm :
    algebraMap (𝓞 F) F (normFormBasis b).hessian.det =
      Algebra.norm F (((b 0 : 𝓞 E) : E) * conj F E ((b 1 : 𝓞 E) : E) -
        conj F E ((b 0 : 𝓞 E) : E) * ((b 1 : 𝓞 E) : E)) := by
  apply (algebraMap F E).injective
  rw [algebraMap_norm]
  simp only [normFormBasis, QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.det_fin_two]
  simp only [Fin.isValue, le_refl, if_true, Fin.zero_le, Fin.one_pos.not_ge, if_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero, zero_add, map_sub, map_mul, map_add,
    algebraMap_algebraMap_intNorm, algebraMap_algebraMap_intTrace, algebraMap_conjO, conj_conj]
  ring

/-- $D_w(Q_b) = -\sigma_w(\Delta_{E/F}(b))/4$ at every real place $w$ of $F$. -/
theorem gramDetNF_normFormBasis (w : Siegel.RealPlace F) :
    Siegel.gramDetNF (normFormBasis b) w = -Siegel.realEmb w (Algebra.discr F (fun j => ((b j : 𝓞 E) : E))) / 4 := by
  rw [Siegel.gramDetNF, Siegel.realForm, ← map_neg, ← hessian_det_normFormBasis]
  have : (QuadForm.map ((Siegel.realEmb w).comp (algebraMap (𝓞 F) F)) (normFormBasis b)).hessian =
      (normFormBasis b).hessian.map ((Siegel.realEmb w).comp (algebraMap (𝓞 F) F)) := by
    ext i j
    simp [QuadForm.hessian, QuadForm.map]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp only [RingHom.comp_apply, map_neg]
  norm_num

end NormFormBasis

/-! ### CM: $Q_b$ is totally positive and has the determinant of the norm lattice -/

section CM

variable (K : Type) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

open Classical

/-- **Relative norms from a CM field are totally positive:** $\sigma_w(N_{K/K^+}(x)) = |\varphi(x)|^2 > 0$ for $x \ne 0$, $w$ a real place of $K^+$,
$\varphi$ an embedding of $K$ above $w$. -/
@[kb "washington1997" "§4.1 [unverified]"]
theorem realEmb_norm_pos {x : K} (hx : x ≠ 0) (w : Siegel.RealPlace K⁺) :
    0 < Siegel.realEmb w (Algebra.norm K⁺ x) := by
  obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := K⁺) (K := K) w.1
  set φ := W.embedding
  have hreal := InfinitePlace.isReal_iff.mp w.2
  have hψ : φ.comp (algebraMap K⁺ K) = w.1.embedding := by
    have h1 : InfinitePlace.mk (φ.comp (algebraMap K⁺ K)) = InfinitePlace.mk w.1.embedding := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]
      exact hW
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · exact h
    · calc φ.comp (algebraMap K⁺ K)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ.comp (algebraMap K⁺ K))) :=
            (ComplexEmbedding.involutive_conjugate K⁺ (φ.comp (algebraMap K⁺ K))).symm
        _ = ComplexEmbedding.conjugate w.1.embedding := by rw [h]
        _ = w.1.embedding := ComplexEmbedding.isReal_iff.mp hreal
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have key : ((Siegel.realEmb w (Algebra.norm K⁺ x) : ℝ) : ℂ) = (Complex.normSq (φ x) : ℂ) := by
    rw [Siegel.realEmb, InfinitePlace.embedding_of_isReal_apply, ← hψ, RingHom.comp_apply, algebraMap_norm,
      map_mul, (isConj_conj (F := K⁺) φ).eq, RCLike.star_def, Complex.mul_conj]
  rw [Complex.ofReal_injective key]
  exact Complex.normSq_pos.mpr hφx

variable {K}

/-- **$Q_b$ is totally positive definite** for any $\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$ ($K$ CM). -/
@[kb "washington1997" "§4.1 [unverified]; hanke2004 §5"]
theorem isTotallyPosDef_normFormBasis (b : Basis (Fin 2) (𝓞 K⁺) (𝓞 K)) :
    Siegel.IsTotallyPosDef (normFormBasis b) := by
  intro w y hy
  have hb : ∀ j, ((b j : 𝓞 K) : K) ≠ 0 := fun j => algebraMap_ne_zero (b.ne_zero j)
  set θ := ((b 0 : 𝓞 K) : K) * conj K⁺ K ((b 1 : 𝓞 K) : K) - conj K⁺ K ((b 0 : 𝓞 K) : K) * ((b 1 : 𝓞 K) : K)
  -- θ ≠ 0, from the discriminant tower
  have hθ : θ ≠ 0 := by
    intro h0
    have hΔ : Algebra.discr K⁺ (fun j => ((b j : 𝓞 K) : K)) = 0 := by
      rw [← neg_eq_zero, ← hessian_det_normFormBasis b, hessian_det_normFormBasis_eq_norm]
      change Algebra.norm K⁺ θ = 0
      rw [h0, Algebra.norm_zero]
    have := discr_tower b
    rw [hΔ, Algebra.norm_zero, mul_zero] at this
    exact discr_ne_zero K (by exact_mod_cast this)
  set g : 𝓞 K⁺ →+* ℝ := (Siegel.realEmb w).comp (algebraMap (𝓞 K⁺) K⁺)
  set a := g (Algebra.intNorm (𝓞 K⁺) (𝓞 K) (b 0))
  set m := g (Algebra.intTrace (𝓞 K⁺) (𝓞 K) (b 0 * conjO K⁺ K (b 1)))
  set c := g (Algebra.intNorm (𝓞 K⁺) (𝓞 K) (b 1))
  have hev : (Siegel.realForm (normFormBasis b) w).evalIn ℝ y = a * y 0 ^ 2 + m * y 0 * y 1 + c * y 1 ^ 2 := by
    simp [Siegel.realForm, QuadForm.map, QuadForm.evalIn, normFormBasis, QuadForm.ofUpper, Fin.sum_univ_two, a,
      m, c, g]
    ring
  have ha : 0 < a := by
    change 0 < Siegel.realEmb w (algebraMap (𝓞 K⁺) K⁺ _)
    rw [algebraMap_intNorm']
    exact realEmb_norm_pos K (hb 0) w
  have hD : 0 < 4 * a * c - m ^ 2 := by
    have h1 : g (normFormBasis b).hessian.det = 4 * a * c - m ^ 2 := by
      simp only [normFormBasis, QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.of_apply, Matrix.det_fin_two]
      simp only [Fin.isValue, le_refl, if_true, Fin.zero_le, Fin.one_pos.not_ge, if_false, Matrix.cons_val_zero,
        Matrix.cons_val_one, add_zero, zero_add, map_sub, map_mul, map_add, a, m, c]
      ring
    rw [← h1]
    change 0 < Siegel.realEmb w (algebraMap (𝓞 K⁺) K⁺ _)
    rw [hessian_det_normFormBasis_eq_norm]
    exact realEmb_norm_pos K hθ w
  rw [hev]
  by_cases h1 : y 1 = 0
  · have h0 : y 0 ≠ 0 := by
      intro h0; apply hy; ext i; fin_cases i <;> simp [h0, h1]
    rw [h1]
    have : 0 < y 0 ^ 2 := by positivity
    nlinarith
  · have hy1 : 0 < y 1 ^ 2 := by positivity
    have key : 4 * a * (a * y 0 ^ 2 + m * y 0 * y 1 + c * y 1 ^ 2) =
        (2 * a * y 0 + m * y 1) ^ 2 + (4 * a * c - m ^ 2) * y 1 ^ 2 := by ring
    have : 0 < 4 * a * (a * y 0 ^ 2 + m * y 0 * y 1 + c * y 1 ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (2 * a * y 0 + m * y 1), mul_pos hD hy1]
    nlinarith

/-- **The condition `HasNormLatticeDet` holds for the norm form:** for $K$ CM and any $\mathcal O_{K^+}$-basis $b$ of $\mathcal O_K$,
$\prod_w D_w(Q_b) = |d_K|/(4^d|d_{K^+}|^2)$, $d = [K^+ : \mathbb Q]$. (From $D_w = -\sigma_w(\Delta)/4 > 0$ and the discriminant tower
$d_K = d_{K^+}^2 N_{K^+/\mathbb Q}(\Delta)$, `discr_tower`.) -/
@[kb "neukirch1999" "Ch. III §2, Cor. 2.10 [unverified]; hanke2004 (5.5)"]
theorem hasNormLatticeDet (b : Basis (Fin 2) (𝓞 K⁺) (𝓞 K)) : HasNormLatticeDet K (normFormBasis b) := by
  constructor
  set Δ := Algebra.discr K⁺ (fun j => ((b j : 𝓞 K) : K))
  have hQ := isTotallyPosDef_normFormBasis b
  have hw : ∀ w : Siegel.RealPlace K⁺, Siegel.gramDetNF (normFormBasis b) w = w.1 Δ / 4 := by
    intro w
    rw [← abs_of_pos (Siegel.gramDetNF_pos hQ w), gramDetNF_normFormBasis, abs_div, abs_neg,
      Siegel.abs_realEmb]
    norm_num
    rfl
  have htow := discr_tower b
  rw [Fintype.card_fin] at htow
  have htowR : ((discr K : ℚ) : ℝ) = ((discr K⁺ : ℚ) : ℝ) ^ 2 * ((Algebra.norm ℚ Δ : ℚ) : ℝ) := by
    rw [htow]; push_cast; ring
  push_cast at htowR
  rw [Finset.prod_congr rfl (fun w _ => hw w), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    card_realPlace K, Siegel.prod_realPlace_eq_abs_norm, htowR, abs_mul, abs_pow]
  have hdF : (0 : ℝ) < |(discr K⁺ : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero _))
  field_simp
  push_cast
  ring

open Classical in
/-- **Siegel's constant for $n = 2$ over $F = K^+$, unconditionally for the norm lattice:** for $K$ CM, any $\mathcal O_{K^+}$-basis $b$ of
$\mathcal O_K$, every $\nu$, and $\lambda = L(1,\chi_{K/K^+})$,
$\tfrac12\,|d_{K^+}|^{-1/2}\,\beta_\infty(\nu)\,\lambda^{-1} = \dfrac{Q_K\,w_K\,h_{K^+}}{2\,h_K}$ for the norm form $Q_b$ (`siegelConstant_binaryF` with its condition discharged by `hasNormLatticeDet`). -/
@[kb "hanke2004" "(5.3)–(5.5); Washington Thm. 4.17 [unverified]; cf. eisQ_coeff_eq_discr_mul_aENF"]
theorem siegelConstant_binaryF_basis (b : Basis (Fin 2) (𝓞 K⁺) (𝓞 K)) (ν : K⁺) {lam : ℝ}
    (hlam : Tendsto (relLR K⁺ K) (𝓝[>] 1) (𝓝 lam)) :
    (1 / 2 : ℝ) * |(discr K⁺ : ℝ)| ^ (-(1 / 2 : ℝ)) * Siegel.betaInfNF (normFormBasis b) ν / lam =
      IsCMField.indexRealUnits K * Units.torsionOrder K * classNumber K⁺ / (2 * classNumber K) :=
  siegelConstant_binaryF K (isTotallyPosDef_normFormBasis b) (hasNormLatticeDet b) ν hlam

end CM


/-! ### CM extensions in general: the genus characters at the infinite places -/

section CMGeneral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

/-- **Relative norms from a CM extension are totally positive** ($E/F$ with $F$ totally real, $E$ totally complex):
$\sigma_w(N_{E/F}(x)) > 0$ for $x \ne 0$ and every real place $w$ of $F$. -/
@[kb "washington1997" "§4.1 [unverified]"]
theorem realEmb_norm_pos' {x : E} (hx : x ≠ 0) (w : Siegel.RealPlace F) :
    0 < Siegel.realEmb w (Algebra.norm F x) := by
  obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w.1
  set φ := W.embedding
  have hreal := InfinitePlace.isReal_iff.mp w.2
  have hψ : φ.comp (algebraMap F E) = w.1.embedding := by
    have h1 : InfinitePlace.mk (φ.comp (algebraMap F E)) = InfinitePlace.mk w.1.embedding := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]
      exact hW
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · exact h
    · calc φ.comp (algebraMap F E)
          = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (φ.comp (algebraMap F E))) :=
            (ComplexEmbedding.involutive_conjugate F (φ.comp (algebraMap F E))).symm
        _ = ComplexEmbedding.conjugate w.1.embedding := by rw [h]
        _ = w.1.embedding := ComplexEmbedding.isReal_iff.mp hreal
  have hφx : φ x ≠ 0 := (map_ne_zero φ).mpr hx
  have key : ((Siegel.realEmb w (Algebra.norm F x) : ℝ) : ℂ) = (Complex.normSq (φ x) : ℂ) := by
    rw [Siegel.realEmb, InfinitePlace.embedding_of_isReal_apply, ← hψ, RingHom.comp_apply, algebraMap_norm,
      map_mul, (isConj_conj (F := F) φ).eq, RCLike.star_def, Complex.mul_conj]
  rw [Complex.ofReal_injective key]
  exact Complex.normSq_pos.mpr hφx

/-- $\delta = \theta^2$ is totally negative in a CM extension. -/
theorem realEmb_relD_neg (w : Siegel.RealPlace F) : Siegel.realEmb w (relD F E) < 0 := by
  have h : relD F E = -Algebra.norm F (relGen F E : E) := by
    apply (algebraMap F E).injective
    rw [algebraMap_relD, map_neg, algebraMap_norm, conj_relGen]
    ring
  rw [h, map_neg, neg_lt_zero]
  exact realEmb_norm_pos' relGen_ne_zero w

/-- **The genus characters at the infinite places, CM case:** $\psi_w(x) = 1$ iff $\sigma_w(x) > 0$ ($x \ne 0$, $w$ real). So on a totally
positive definite lattice $(L, cN)$ (all values totally positive) every $\psi_w$ is trivial; only the finite places carry genus
information. -/
@[kb "serre1973" "Ch. III §1.2 [unverified]; washington1997 §4.1 [unverified]"]
theorem genusSym_infinite_iff (w : Siegel.RealPlace F) {x : F} (hx : x ≠ 0) :
    genusSym E (NFPlace.infinite w.1) x = 1 ↔ 0 < Siegel.realEmb w x := by
  have hd := realEmb_relD_neg (E := E) w
  have hx' : Siegel.realEmb w x ≠ 0 := (map_ne_zero _).mpr hx
  have e : genusSym E (NFPlace.infinite w.1) x =
      hilbertSymbol ℝ (Siegel.realEmb w (relD F E)) (Siegel.realEmb w x) := by
    rw [genusSym, HN.hilbert_infinite_real w.2]
    rfl
  rw [e]
  constructor
  · intro h
    by_contra hneg
    have hlt : Siegel.realEmb w x < 0 := lt_of_le_of_ne (not_lt.mp hneg) hx'
    have := (hilbertSymbol_real _ _ hd.ne hx').mpr ⟨hd, hlt⟩
    rw [h] at this; norm_num at this
  · intro hpos
    rcases HN.hilbertSymbol_eq_one_or ℝ (Siegel.realEmb w (relD F E)) (Siegel.realEmb w x) with h | h
    · exact h
    · exact absurd ((hilbertSymbol_real _ _ hd.ne hx').mp h).2 (not_lt.mpr hpos.le)

end CMGeneral

end QuadFormsKB.Binary.Rel
