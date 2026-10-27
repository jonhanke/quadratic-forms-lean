import QuadFormsKB.Analysis.DifferentLocal
import QuadFormsKB.Analysis.LatticePoisson

/-!
# Poisson summation over a fractional ideal in $F_\infty$

$F_\infty = F\otimes_{\mathbb{Q}}\mathbb{R}$ is Mathlib's mixed (Minkowski) space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$
(`mixedEmbedding.mixedSpace F`, ring-isomorphic to `InfiniteAdeleRing F` by `InfiniteAdeleRing.ringEquiv_mixedSpace`),
with $F \hookrightarrow F_\infty$ the mixed embedding.

* `traceInf`: $\operatorname{Tr}_\infty(y) = \sum_{w\ \mathrm{real}} y_w + \sum_{w\ \mathrm{complex}} 2\operatorname{Re}y_w$;
  `traceInf_mixedEmbedding`: it restricts to $\operatorname{Tr}_{F/\mathbb{Q}}$ on $F$.
* `psiInf` $= e\circ\operatorname{Tr}_\infty$ (the character $e(x)$ at a real place, $e(2\operatorname{Re}z)$ at a complex
  place); `selfDualInf` $= 2^{r_2}\cdot$`volume` (Lebesgue at real places, twice Lebesgue $2\,dx\,dy$ at complex
  places); `fourierInf` $\hat f(z) = \int f(y)\psi_\infty(yz)\,dy$.
* **`poisson_fractionalIdeal`**: for a nonzero fractional ideal $I$, a Schwartz function $f$ on $F_\infty$ and
  $\xi \in F$,
  $$\sum_{x\in I} f(\xi+x) = \big(2^{r_2}\operatorname{covol}(I)\big)^{-1}\sum_{\mu\in I^\vee}\hat f(\mu)\,
    e(-\operatorname{Tr}_{F/\mathbb{Q}}(\xi\mu)),$$
  $I^\vee$ = `FractionalIdeal.dual ℤ ℚ I` the trace dual; both sides converge absolutely
  (`summable_poisson_lhs`, `summable_poisson_rhs`); `selfDual_covolume_idealLattice`:
  $2^{r_2}\operatorname{covol}(I) = N(I)|d_F|^{1/2}$ (Mathlib's `covolume_idealLattice`).

*Proof.* A $\mathbb{Z}$-basis $b$ of $I$ gives coordinates $T : \mathbb{R}^n \to F_\infty$, $T(\mathbb{Z}^n) = I$
(`Tmap`, `Tmap_intVec`), with $T_*(\mathrm{Lebesgue}) = \operatorname{covol}(I)^{-1}\mathrm{vol}$ (`map_Tmap_volume`).
Poisson summation over $\mathbb{Z}^n$ (vendored `poissonSummation_standard`) applied to $f\circ T$, and
$\langle T^{-1}y, m\rangle = \operatorname{Tr}_\infty\big(y\sum_j m_jb_j^\vee\big)$ for the trace-dual basis $b^\vee$
(`inner_Tmap_symm`), whose $\mathbb{Z}$-span is $I^\vee$ (Mathlib's `traceDual_span_of_basis`).

Sources: Tate's thesis, Cassels–Fröhlich Ch. XV, §4.1, Lemma 4.1.4, p. 330 (the volume $\sqrt{|d|}$, with the
factor $2^{r_2}$ from the measure at complex places), and §4.2, Lemma 4.2.4, p. 333 (Tate's adelic Poisson formula,
proved on $V$ mod $k$ rather than through lattices); Weil, *Basic Number Theory*, Ch. VII §2
[unverified]; Neukirch, *Algebraic Number Theory*, Ch. I §5 (Minkowski theory) [unverified].
-/

open IsDedekindDomain NumberField WithZero MeasureTheory NumberField.InfinitePlace
open NumberField.mixedEmbedding
open scoped Real FourierTransform nonZeroDivisors Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

/-- **The trace on $F_\infty = F \otimes \mathbb{R}$:** for $y = ((y_w)_{w\ \mathrm{real}}, (y_w)_{w\ \mathrm{complex}})$ in
the mixed (Minkowski) space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$, $\operatorname{Tr}_\infty(y) = \sum_{w\ \mathrm{real}} y_w +
\sum_{w\ \mathrm{complex}} 2\operatorname{Re} y_w$ (the sum of the local traces $\operatorname{Tr}_{F_w/\mathbb{R}}$). -/
def traceInf (y : V) : ℝ := (∑ w, y.1 w) + ∑ w, 2 * (y.2 w).re

lemma traceInf_add (y z : V) : traceInf (y + z) = traceInf y + traceInf z := by
  simp only [traceInf, Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, Finset.sum_add_distrib,
    mul_add]
  ring

lemma traceInf_smul (c : ℝ) (y : V) : traceInf (c • y) = c * traceInf y := by
  simp only [traceInf, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum, mul_add]
  congr 1
  refine Finset.sum_congr rfl fun w _ => by ring

/-- `traceInf` as an `ℝ`-linear functional. -/
def traceInfL : V →ₗ[ℝ] ℝ where
  toFun := traceInf
  map_add' := traceInf_add
  map_smul' := traceInf_smul

lemma continuous_traceInf : Continuous (traceInf (F := F)) :=
  LinearMap.continuous_of_finiteDimensional (traceInfL (F := F))

/-- **$\operatorname{Tr}_\infty$ restricts to the trace on $F$:** $\operatorname{Tr}_\infty(x) = \operatorname{Tr}_{F/\mathbb{Q}}(x)$. -/
@[kb "neukirch1999" "Ch. I, §5 (Minkowski theory) [unverified]"]
theorem traceInf_mixedEmbedding (x : F) :
    traceInf (mixedEmbedding F x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h := congrArg Complex.re (trace_eq_sum_embeddings (E := ℂ) (K := ℚ) (L := F) (x := x))
  rw [eq_ratCast, Complex.ratCast_re, Complex.re_sum] at h
  rw [h, ← Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => (φ x).re)
    (fun σ => (σ x).re) fun _ => by simp [RingHom.equivRatAlgHom_apply]]
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => (φ x).re)]
  have hfib : ∀ (w : InfinitePlace F) (φ : F →+* ℂ), φ ∈ ({φ | mk φ = w} : Finset _) →
      (φ x).re = (w.embedding x).re := by
    intro w φ hφ
    have h1 : mk φ = mk w.embedding := by rw [(Finset.mem_filter.mp hφ).2, mk_embedding]
    rcases mk_eq_iff.mp h1 with h2 | h2
    · rw [h2]
    · rw [← h2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  simp_rw [Finset.sum_congr rfl (hfib _), Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [InfinitePlace.sum_eq_sum_add_sum, traceInf]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, mixedEmbedding_apply_isReal, ← embedding_of_isReal_apply w.2, Complex.ofReal_re]
    simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex]
    simp

lemma traceInf_neg (y : V) : traceInf (-y) = -traceInf y := by
  have := traceInf_smul (-1) y
  rwa [neg_one_smul, neg_one_mul] at this

/-- **The standard character at infinity:** $\psi_\infty(y) = e(\operatorname{Tr}_\infty y)$, i.e. $e(y_w)$ at a real
place and $e(2\operatorname{Re} y_w) = e(\operatorname{Tr}_{\mathbb{C}/\mathbb{R}} y_w)$ at a complex place. This is
$e^{-2\pi i\lambda(y)}$ for Tate's $\lambda$ ($-x$ at a real place, $-2\operatorname{Re}\xi$ at a complex place;
Cassels–Fröhlich Ch. XV, pp. 309 and 318), the complex conjugate of Tate's character; the Fourier transforms agree. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, p. 309 (Case 1: λ(x) = −x) and §2.5, p. 318 (complex place: λ(ξ) = −2 Re ξ)"]
def psiInf (y : V) : Circle := 𝐞 (traceInf y)

/-- **The self-dual measure on $F_\infty$:** Lebesgue measure on each real place and twice Lebesgue measure
$2\,dx\,dy$ on each complex place ($\mathbb{C} = \mathbb{R}^2$), i.e. $2^{r_2}$ times Mathlib's `volume` on the mixed space. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, p. 310 (Lebesgue measure at a real place, twice Lebesgue measure at a complex place)"]
def selfDualInf : Measure V := ((2 : NNReal) ^ nrComplexPlaces F) • volume

/-- **The Fourier transform on $F_\infty$:** $\hat f(z) = \int_{F_\infty} f(y)\,\psi_\infty(yz)\,dy$ for the self-dual
measure (product in the ring $F_\infty = \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2, Thm. 2.2.2, p. 310, at each infinite place; products of places as in §3.3, Lemma 3.3.3, p. 327"]
def fourierInf (f : V → ℂ) (z : V) : ℂ := ∫ y, f y * (psiInf (y * z) : ℂ) ∂selfDualInf

lemma fourierChar_coe_eq_exp (t : ℝ) :
    ((𝐞 t : Circle) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-! ### Lattice coordinates for a fractional ideal -/

section Coordinates

variable (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

lemma card_basisIndex : Fintype.card (Module.Free.ChooseBasisIndex ℤ I) = Module.finrank ℚ F := by
  rw [← Module.finrank_eq_card_basis (fractionalIdealLatticeBasis F I), mixedEmbedding.finrank]

/-- An indexing of a `ℤ`-basis of `I` by `Fin n`, `n = [F:ℚ]`. -/
def idxEquiv : Module.Free.ChooseBasisIndex ℤ I ≃ Fin (Module.finrank ℚ F) :=
  Fintype.equivFinOfCardEq (card_basisIndex I)

/-- A `ℚ`-basis of `F` that is a `ℤ`-basis of `I`. -/
def bq : Module.Basis (Fin (Module.finrank ℚ F)) ℚ F := (basisOfFractionalIdeal F I).reindex (idxEquiv I)

/-- Its image, an `ℝ`-basis of the mixed space. -/
def bR : Module.Basis (Fin (Module.finrank ℚ F)) ℝ V :=
  (fractionalIdealLatticeBasis F I).reindex (idxEquiv I)

lemma bR_apply (j : Fin (Module.finrank ℚ F)) : bR I j = mixedEmbedding F (bq I j) := by
  simp [bR, bq]

/-- The lattice point $\sum_j k_j b_j \in I$. -/
def latElt (k : Fin (Module.finrank ℚ F) → ℤ) : F := ∑ j, (k j : F) * bq I j

/-- The dual lattice point $\sum_j m_j b_j^\vee \in I^\vee$ (trace-dual basis). -/
def dualElt (m : Fin (Module.finrank ℚ F) → ℤ) : F := ∑ j, (m j : F) * (bq I).traceDual j

lemma dualElt_neg (m : Fin (Module.finrank ℚ F) → ℤ) : dualElt I (-m) = -dualElt I m := by
  simp [dualElt, Finset.sum_neg_distrib]

lemma trace_bq_mul_dualElt (i : Fin (Module.finrank ℚ F)) (m : Fin (Module.finrank ℚ F) → ℤ) :
    Algebra.trace ℚ F (bq I i * dualElt I m) = m i := by
  rw [dualElt, Finset.mul_sum, map_sum]
  have h : ∀ j, Algebra.trace ℚ F (bq I i * ((m j : F) * (bq I).traceDual j)) =
      (m j : ℚ) * (if i = j then 1 else 0) := by
    intro j
    rw [mul_left_comm, show (m j : F) = algebraMap ℚ F (m j) by simp, ← Algebra.smul_def, map_smul,
      Module.Basis.trace_mul_traceDual, smul_eq_mul]
  simp [h]

local notation "E" => EuclideanSpace ℝ (Fin (Module.finrank ℚ F))

/-- The coordinate map $\mathbb{R}^n \to F_\infty$, $t \mapsto \sum_j t_j b_j$, taking $\mathbb{Z}^n$ onto $I$. -/
def Tmap : E ≃L[ℝ] V :=
  ((EuclideanSpace.basisFun (Fin (Module.finrank ℚ F)) ℝ).toBasis.equiv (bR I)
    (Equiv.refl _)).toContinuousLinearEquiv

lemma Tmap_single (j : Fin (Module.finrank ℚ F)) :
    Tmap I (EuclideanSpace.single j 1) = bR I j := by
  rw [← EuclideanSpace.basisFun_apply, ← OrthonormalBasis.coe_toBasis]
  change ((EuclideanSpace.basisFun (Fin (Module.finrank ℚ F)) ℝ).toBasis.equiv (bR I)
    (Equiv.refl _)) _ = _
  rw [Module.Basis.equiv_apply]
  rfl

lemma intVec_eq_sum (k : Fin (Module.finrank ℚ F) → ℤ) :
    SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) k =
      ∑ j, (k j : ℝ) • EuclideanSpace.single j (1 : ℝ) := by
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec, Pi.single_apply]

lemma Tmap_intVec (k : Fin (Module.finrank ℚ F) → ℤ) :
    Tmap I (SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) k) =
      mixedEmbedding F (latElt I k) := by
  rw [intVec_eq_sum, map_sum, latElt, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Tmap_single, bR_apply, map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

lemma inner_Tmap_symm (y : V) (m : Fin (Module.finrank ℚ F) → ℤ) :
    inner ℝ ((Tmap I).symm y) (SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) m) =
      traceInf (y * mixedEmbedding F (dualElt I m)) := by
  let L1 : V →ₗ[ℝ] ℝ := (innerSL ℝ (SchwartzMap.PoissonSummation.Standard.intVec
    (d := Module.finrank ℚ F) m)).toLinearMap ∘ₗ (Tmap I).symm.toLinearMap
  let L2 : V →ₗ[ℝ] ℝ := traceInfL ∘ₗ LinearMap.mulRight ℝ (mixedEmbedding F (dualElt I m))
  have h : L1 = L2 := by
    refine (bR I).ext fun j => ?_
    rw [← Tmap_single]
    show inner ℝ (SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) m)
        ((Tmap I).symm ((Tmap I) (EuclideanSpace.single j 1))) =
      traceInf ((Tmap I) (EuclideanSpace.single j 1) * mixedEmbedding F (dualElt I m))
    rw [ContinuousLinearEquiv.symm_apply_apply, Tmap_single, EuclideanSpace.inner_single_right,
      bR_apply, ← map_mul]
    rw [traceInf_mixedEmbedding, trace_bq_mul_dualElt]
    simp
  have := congrArg (fun L : V →ₗ[ℝ] ℝ => L y) h
  simp only [L1, L2, LinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, LinearMap.mulRight_apply] at this
  rw [real_inner_comm]
  exact this

/-- **The coordinate measure:** $T_*(\mathrm{Lebesgue}) = \operatorname{covol}(I)^{-1}\cdot\mathrm{vol}$ on $F_\infty$. -/
lemma map_Tmap_volume : Measure.map (Tmap I) (volume : Measure E) =
    ((ZLattice.covolume (idealLattice F I)).toNNReal)⁻¹ • (volume : Measure V) := by
  rw [← (EuclideanSpace.basisFun (Fin (Module.finrank ℚ F)) ℝ).addHaar_eq_volume,
    Module.Basis.map_addHaar]
  have hb : (EuclideanSpace.basisFun (Fin (Module.finrank ℚ F)) ℝ).toBasis.map
      ((Tmap I : E ≃L[ℝ] V) : E ≃ₗ[ℝ] V) = bR I := by
    change _ = bR I
    have := Module.Basis.map_equiv (EuclideanSpace.basisFun (Fin (Module.finrank ℚ F)) ℝ).toBasis
      (bR I) (Equiv.refl _)
    rw [Equiv.refl_symm, Module.Basis.reindex_refl] at this
    exact this
  have hc : ENNReal.ofReal (ZLattice.covolume (idealLattice F I)) =
      volume (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis F I)) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice F I),
      measureReal_def, ENNReal.ofReal_toReal]
    rw [← lt_top_iff_ne_top]
    exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  have hpos : 0 < (ZLattice.covolume (idealLattice F I)).toNNReal :=
    Real.toNNReal_pos.mpr (ZLattice.covolume_pos _ _)
  rw [hb, Module.Basis.addHaar_eq_iff, Measure.smul_apply, Measure.nnreal_smul_coe_apply,
    Module.Basis.coe_parallelepiped,
    ← measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped (bR I) volume), bR,
    ZSpan.fundamentalDomain_reindex, ← hc, ENNReal.ofReal, ← ENNReal.coe_mul, inv_mul_cancel₀ hpos.ne',
    ENNReal.coe_one]

/-- $\mathbb{Z}^n \cong I$, $k \mapsto \sum_j k_j b_j$. -/
def latEquiv : (Fin (Module.finrank ℚ F) → ℤ) ≃ ((I : FractionalIdeal (𝓞 F)⁰ F) : Set F) :=
  ((fractionalIdealBasis F (I : FractionalIdeal (𝓞 F)⁰ F)).reindex (idxEquiv I)).equivFun.symm.toEquiv

lemma latEquiv_coe (k : Fin (Module.finrank ℚ F) → ℤ) : (latEquiv I k : F) = latElt I k := by
  simp only [latEquiv, LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply, latElt]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show ((k j • ((fractionalIdealBasis F (I : FractionalIdeal (𝓞 F)⁰ F)).reindex (idxEquiv I)) j :
      ((I : FractionalIdeal (𝓞 F)⁰ F) : Set F)) : F) = k j • (((fractionalIdealBasis F
        (I : FractionalIdeal (𝓞 F)⁰ F)).reindex (idxEquiv I)) j : F) from rfl,
    zsmul_eq_mul, bq, Module.Basis.reindex_apply, Module.Basis.reindex_apply,
    basisOfFractionalIdeal_apply]

lemma mem_dual_iff_mem_span (x : F) :
    x ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 F)⁰ F) ↔
      x ∈ Submodule.span ℤ (Set.range (bq I).traceDual) := by
  have hI : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero I
  have hspan : Submodule.restrictScalars ℤ ((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) =
      Submodule.span ℤ (Set.range (bq I)) := by
    ext y
    rw [Submodule.restrictScalars_mem, bq, Module.Basis.range_reindex,
      mem_span_basisOfFractionalIdeal]
    rfl
  have h := Submodule.traceDual_span_of_basis ℤ (K := ℚ)
    ((I : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) (bq I) hspan
  rw [← h, Submodule.restrictScalars_mem, ← FractionalIdeal.coe_dual ℤ ℚ hI]
  rfl

lemma linearIndependent_traceDual_int : LinearIndependent ℤ (bq I).traceDual :=
  (bq I).traceDual.linearIndependent.restrict_scalars' ℤ

/-- $\mathbb{Z}^n \cong I^\vee$, $m \mapsto \sum_j m_j b_j^\vee$. -/
def dualEquiv : (Fin (Module.finrank ℚ F) → ℤ) ≃
    ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) : Set F) :=
  (Module.Basis.span (linearIndependent_traceDual_int I)).equivFun.symm.toEquiv.trans
    (Equiv.subtypeEquivRight fun x => (mem_dual_iff_mem_span I x).symm)

lemma dualEquiv_coe (m : Fin (Module.finrank ℚ F) → ℤ) : (dualEquiv I m : F) = dualElt I m := by
  simp only [dualEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv, Module.Basis.equivFun_symm_apply,
    Equiv.subtypeEquivRight_apply_coe, Submodule.coe_sum, dualElt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, zsmul_eq_mul, Module.Basis.span_apply]

/-- The Fourier transform of $f \circ T$ at $m \in \mathbb{Z}^n$ is
$(2^{r_2}\operatorname{covol} I)^{-1}\hat f(-\sum_j m_j b_j^\vee)$. -/
lemma fourier_comp_Tmap (f : SchwartzMap V ℂ) (m : Fin (Module.finrank ℚ F) → ℤ) :
    𝓕 (fun x : E => (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f) x)
        (SchwartzMap.PoissonSummation.Standard.intVec m) =
      (((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F I))⁻¹ : ℝ) *
        fourierInf f (mixedEmbedding F (dualElt I (-m))) := by
  have hcov : 0 < ZLattice.covolume (idealLattice F I) := ZLattice.covolume_pos _ _
  have hgx : ∀ t, (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f) t = f (Tmap I t) :=
    fun t => rfl
  set h : V → ℂ := fun y => ((𝐞 (-inner ℝ ((Tmap I).symm y)
    (SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) m)) : Circle) : ℂ) *
      f y with hh
  have h1 : 𝓕 (fun x : E => (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f) x)
      (SchwartzMap.PoissonSummation.Standard.intVec m) = ∫ t, h (Tmap I t) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hh, ContinuousLinearEquiv.symm_apply_apply, hgx, Circle.smul_def, smul_eq_mul]
  have h2 : ∫ t, h (Tmap I t) = ∫ y, h y ∂(Measure.map (Tmap I) (volume : Measure E)) := by
    rw [show (Measure.map (Tmap I) (volume : Measure E)) =
      Measure.map (Tmap I).toHomeomorph.toMeasurableEquiv volume from rfl, integral_map_equiv]
    rfl
  have h3 : fourierInf f (mixedEmbedding F (dualElt I (-m))) =
      ((2 : NNReal) ^ nrComplexPlaces F) • ∫ y, h y := by
    rw [fourierInf, selfDualInf, integral_smul_nnreal_measure]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hh, psiInf, inner_Tmap_symm, dualElt_neg, map_neg, mul_neg, traceInf_neg]
    ring
  rw [h1, h2, map_Tmap_volume, integral_smul_nnreal_measure, h3, NNReal.smul_def, NNReal.smul_def,
    Complex.real_smul, Complex.real_smul, NNReal.coe_inv, Real.coe_toNNReal _ hcov.le]
  push_cast
  field_simp

/-- **Poisson summation for a fractional ideal $I$ in $F_\infty$:** for a Schwartz function $f$ on
$F_\infty = \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ and $\xi \in F$,
$$\sum_{x \in I} f(\xi + x) = \operatorname{covol}(I)^{-1}\sum_{\mu \in I^\vee}\hat f(\mu)\,e(-\operatorname{Tr}(\xi\mu)),$$
where $I^\vee$ = `dual ℤ ℚ I` is the trace dual, $\hat f$ = `fourierInf` (self-dual measure) and
$\operatorname{covol}(I) = 2^{r_2}\operatorname{covol}_{\mathrm{Mathlib}}(I)$ is the covolume for the self-dual measure.
*Proof:* coordinates $t \mapsto \sum_j t_j b_j$ for a $\mathbb{Z}$-basis $b$ of $I$, Poisson summation over $\mathbb{Z}^n$
(`poissonSummation_standard`), the trace-dual basis $b^\vee$ for the dual lattice. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.1, Lemma 4.1.4, p. 330 (the volume √|d| of the parallelotope of 𝒪); §4.2, Lemma 4.2.4, p. 333"]
theorem poisson_fractionalIdeal (f : SchwartzMap V ℂ) (ξ : F) :
    ∑' x : ((I : FractionalIdeal (𝓞 F)⁰ F) : Set F), f (mixedEmbedding F (ξ + x)) =
      (((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F I))⁻¹ : ℝ) *
        ∑' μ : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 F)⁰ F) :
            FractionalIdeal (𝓞 F)⁰ F) : Set F),
          fourierInf f (mixedEmbedding F μ) *
            (𝐞 (-((Algebra.trace ℚ F (ξ * μ) : ℚ) : ℝ)) : ℂ) := by
  set g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f with hg
  have hgx : ∀ t, g t = f (Tmap I t) := fun t => rfl
  set v : E := (Tmap I).symm (mixedEmbedding F ξ)
  have hP := SchwartzMap.PoissonSummation.Standard.poissonSummation_standard (d := Module.finrank ℚ F) g v
  rw [← (SchwartzMap.PoissonSummation.Standard.equivIntVec (d := Module.finrank ℚ F)).tsum_eq] at hP
  -- left side
  have hL : ∀ k : Fin (Module.finrank ℚ F) → ℤ,
      g (v + ((SchwartzMap.PoissonSummation.Standard.equivIntVec (d := Module.finrank ℚ F) k :
        SchwartzMap.standardLattice _) : E)) = f (mixedEmbedding F (ξ + latEquiv I k)) := by
    intro k
    rw [hgx, map_add, ContinuousLinearEquiv.apply_symm_apply]
    change f (_ + Tmap I (SchwartzMap.PoissonSummation.Standard.intVec k)) = _
    rw [Tmap_intVec, latEquiv_coe, RingHom.map_add]
  simp_rw [hL] at hP
  simp only [← RCLike.inner_eq_wInner_one] at hP
  rw [← (latEquiv I).tsum_eq, hP]
  -- right side
  have hF : ∀ m : Fin (Module.finrank ℚ F) → ℤ,
      𝓕 (fun x : E => g x) (SchwartzMap.PoissonSummation.Standard.intVec m) =
        (((2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F I))⁻¹ : ℝ) *
          fourierInf f (mixedEmbedding F (dualElt I (-m))) := fun m => fourier_comp_Tmap I f m
  have hph : ∀ m : Fin (Module.finrank ℚ F) → ℤ,
      inner ℝ v (SchwartzMap.PoissonSummation.Standard.intVec (d := Module.finrank ℚ F) m) =
        ((Algebra.trace ℚ F (ξ * dualElt I m) : ℚ) : ℝ) := by
    intro m
    rw [inner_Tmap_symm, ← map_mul, traceInf_mixedEmbedding]
  simp_rw [hF, hph, ← fourierChar_coe_eq_exp]
  rw [← (dualEquiv I).tsum_eq, ← tsum_mul_left, ← (Equiv.neg (Fin (Module.finrank ℚ F) → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.neg_apply, neg_neg, dualEquiv_coe, dualElt_neg, mul_neg, map_neg, Rat.cast_neg]
  ring

/-- $\sum_{k\in\mathbb{Z}^n}|g(v + k)| < \infty$ for a Schwartz function $g$. -/
lemma summable_norm_shift (g : SchwartzMap E ℂ) (v : E) :
    Summable fun k : Fin (Module.finrank ℚ F) → ℤ =>
      ‖g (v + SchwartzMap.PoissonSummation.Standard.intVec k)‖ := by
  let K : TopologicalSpace.Compacts E := ⟨{v}, isCompact_singleton⟩
  have h := SchwartzMap.PoissonSummation.Standard.summable_norm_translate_restrict
    (d := Module.finrank ℚ F) g K
  have h' := (SchwartzMap.PoissonSummation.Standard.equivIntVec
    (d := Module.finrank ℚ F)).summable_iff.mpr h
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h'
  exact ContinuousMap.norm_coe_le_norm ((SchwartzMap.PoissonSummation.Standard.translate
    (d := Module.finrank ℚ F) g (SchwartzMap.PoissonSummation.Standard.equivIntVec k)).restrict K)
    ⟨v, rfl⟩

/-- The left side of `poisson_fractionalIdeal` converges absolutely. -/
theorem summable_poisson_lhs (f : SchwartzMap V ℂ) (ξ : F) :
    Summable fun x : ((I : FractionalIdeal (𝓞 F)⁰ F) : Set F) => f (mixedEmbedding F (ξ + x)) := by
  rw [← (latEquiv I).summable_iff]
  refine Summable.of_norm ?_
  convert summable_norm_shift (F := F) (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f)
    ((Tmap I).symm (mixedEmbedding F ξ)) using 2 with k
  change _ = ‖f (Tmap I _)‖
  rw [map_add, ContinuousLinearEquiv.apply_symm_apply, Tmap_intVec, Function.comp_apply, latEquiv_coe,
    RingHom.map_add]

/-- The right side of `poisson_fractionalIdeal` converges absolutely. -/
theorem summable_poisson_rhs (f : SchwartzMap V ℂ) (ξ : F) :
    Summable fun μ : ((FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 F)⁰ F) :
        FractionalIdeal (𝓞 F)⁰ F) : Set F) =>
      fourierInf f (mixedEmbedding F μ) * (𝐞 (-((Algebra.trace ℚ F (ξ * μ) : ℚ) : ℝ)) : ℂ) := by
  rw [← (dualEquiv I).summable_iff]
  refine Summable.of_norm ?_
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (Tmap I) f
  set K : ℝ := (2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F I)
  have hK : 0 < K := mul_pos (pow_pos two_pos _) (ZLattice.covolume_pos _ _)
  have hs := (summable_norm_intPt (𝓕 g)).comp_injective (neg_injective (G := Fin (Module.finrank ℚ F) → ℤ))
  refine (hs.mul_left K).congr fun m => ?_
  simp only [Function.comp_apply, dualEquiv_coe, norm_mul, Circle.norm_coe, mul_one]
  have h := fourier_comp_Tmap I f (-m)
  rw [neg_neg] at h
  rw [SchwartzMap.fourier_coe, intPt, h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hK), ← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]

/-- **The covolume of $I$ for the self-dual measure** is $2^{r_2}\operatorname{covol}(I) = N(I)\,|d_F|^{1/2}$. -/
@[kb "neukirch1999" "Ch. I, Prop. 5.2 ($\\mathrm{vol}(\\mathfrak a) = 2^{-r_2}N(\\mathfrak a)|d_F|^{1/2}$) [unverified]"]
theorem selfDual_covolume_idealLattice :
    (2 : ℝ) ^ nrComplexPlaces F * ZLattice.covolume (idealLattice F I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) * Real.sqrt |(discr F : ℝ)| := by
  rw [covolume_idealLattice]
  have : (2 : ℝ) ^ nrComplexPlaces F * (2⁻¹) ^ nrComplexPlaces F = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  calc (2 : ℝ) ^ nrComplexPlaces F * ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) *
        (2⁻¹) ^ nrComplexPlaces F * Real.sqrt |(discr F : ℝ)|)
      = ((2 : ℝ) ^ nrComplexPlaces F * (2⁻¹) ^ nrComplexPlaces F) *
          ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) * Real.sqrt |(discr F : ℝ)|) := by
        ring
    _ = _ := by rw [this, one_mul]

end Coordinates

end

end QuadFormsKB.Analysis
