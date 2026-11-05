/-
# Hanke 2011, Lemma 3.7 over $\mathbb Q$: genera of integral ternary forms and tuples of local genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), Lemma 3.7, p. 13, for $F = \mathbb Q$, $n = 3$, positive definite forms.

* `locGenusOf_latOf`: the local genus of a free lattice $\gamma\mathcal O_F^n$ on $(F^n, Q)$ is that of $\mathcal O_F^n$ on
  $(F^n, Q\circ\gamma)$ (any number field).
* `formTuple Q`: the tuple of local genera of a form $Q$ over $\mathbb Z$ (those of $\mathbb Z^n$ on $(\mathbb Q^n, Q)$).
* `formTuple_mem_genStar`: for $Q \in \mathrm{Cls}^*(N;3)$ the tuple lies in $\mathrm{Gen}^*(N, (3,0); 3)$.
-/
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist
import QuadFormsKB.Literature.Hanke2011Structure.RationalTernary
import QuadFormsKB.Tamagawa.FormClassNF
import QuadFormsKB.Tamagawa.SiegelSpace
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal
import QuadFormsKB.Tamagawa.InputsFollowup

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Transport along a global basis -/

section Transport

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $\mathcal O_F^n$ is integral for a form over $\mathcal O_F$ (every number field). -/
theorem isIntegral_intVec_formF (Q₀ : QuadForm (𝓞 F) n) :
    IsIntegral (formF Q₀) (intVec : Submodule (𝓞 F) (Fin n → F)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_intVec_iff_exists.mp hx
  exact ⟨Q₀.eval y, by rw [← eval_map_comp]⟩

/-- **The local genus of a free lattice** $\gamma\mathcal O_F^n$ on $(F^n, Q)$ is that of $\mathcal O_F^n$ on
$(F^n, Q\circ\gamma)$. -/
theorem locGenusOf_latOf (v : HeightOneSpectrum (𝓞 F)) (Q : QuadForm F n) (γ : GL (Fin n) F)
    (hγ : IsIntegral Q (latOf γ)) :
    locGenusOf v Q ⟨latOf γ, latOf_isLattice γ⟩ hγ =
      locGenusOf v (formF (gramZ Q γ hγ)) ⟨intVec, intVec_isLattice⟩ (isIntegral_intVec_formF _) := by
  have h1 : loc v (latOf γ) =
      locAct v (Matrix.GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) γ) (std v) := by
    rw [latOf, loc_glImage, loc_intVec]
  have h2 : loc v (intVec : Submodule (𝓞 F) (Fin n → F)) = locAct v 1 (std v) := by
    rw [locAct_one, loc_intVec]
  rw [locGenusOf_eq v Q ⟨latOf γ, latOf_isLattice γ⟩ hγ h1,
    locGenusOf_eq v (formF (gramZ Q γ hγ)) ⟨intVec, intVec_isLattice⟩ (isIntegral_intVec_formF _) h2]
  congr 1
  apply QuadForm.map_injective_O v
  simp only
  rw [QuadForm.map_toO, QuadForm.map_toO, localForm, localForm, Units.val_one, QuadForm.compMat_one,
    Tamagawa.SiegelSpace.formF_gramZ', ← QuadForm.map_compMat]
  rfl

end Transport

/-! ### The tuple of local genera of an integral form over $\mathbb Q$ -/

open Tamagawa.RatBridge

/-- **The local genera of an integral form** $Q$ over $\mathbb Z$: those of $\mathbb Z^n$ on $(\mathbb Q^n, Q)$. -/
def formTuple {n : ℕ} (Q : QuadForm ℤ n) : LocTuple ℚ n :=
  fun v => locGenusOf v (formF (up Q)) (Tamagawa.stdLat ℚ n) (isIntegral_intVec_formF _)

/-- The class of a positive integer $N$ as a non-archimedean squareclass of $\mathbb Q$ (the diagonal image of $N$). -/
def ratS (a : ℚˣ) : AdelicSqCl ℚ := SqCl.mk (FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ a)

/-- The positive definite signature $(n, 0)$ at the real place of $\mathbb Q$. -/
def sigPos (n : ℕ) : SignatureVector ℚ n := fun _ => ⟨(n, 0), by simp⟩

theorem epsInf_sigPos (n : ℕ) : epsInf (sigPos n) = 1 := by
  unfold epsInf sigPos hasseReal
  simp


theorem isTotallyPos_rat {q : ℚ} (h : IsTotallyPos q) : 0 < q := by
  have := h (Algebra.ofId ℚ ℂ)
  simp only [eq_ratCast] at this
  have h2 : (0 : ℂ) < ((q : ℝ) : ℂ) := by rw [Complex.ofReal_ratCast]; exact this
  have h3 : (0 : ℝ) < q := Complex.zero_lt_real.mp h2
  exact_mod_cast h3

/-- A positive rational number is a square at the real place of $\mathbb Q$. -/
theorem exists_sq_realPlace {w : InfinitePlace ℚ} (hw : w.IsReal) {q : ℚ} (hq : 0 < q) :
    ∃ r : w.Completion, r ≠ 0 ∧ r ^ 2 = (q : w.Completion) := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨φ.symm (Real.sqrt q), ?_, ?_⟩
  · intro h
    have := congrArg φ h
    rw [RingEquiv.apply_symm_apply, map_zero, Real.sqrt_eq_zero'] at this
    exact absurd this (not_le.mpr (by exact_mod_cast hq))
  · apply φ.injective
    rw [map_pow, RingEquiv.apply_symm_apply, Real.sq_sqrt (by exact_mod_cast hq.le), map_ratCast]

/-- **Positive definite forms have the positive definite signature** at the real place of $\mathbb Q$. -/
theorem hasSignature_sigPos {n : ℕ} {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) : HasSignature (formF (up Q)) (sigPos n) := by
  intro w
  let _ : Algebra ℚ w.1.Completion := InfinitePlace.Completion.instAlgebra w.1 ℚ
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (formF (up Q)).Nondegenerate := hpd.nondegenerate
  obtain ⟨a, ha, hQa⟩ := FieldGen.exists_isometric_diag _ hnd
  have hpos : ∀ i, 0 < a i := by
    intro i
    obtain ⟨P, hP, hPx⟩ := hQa
    have hx := hPx (Pi.single i 1)
    have hne : P *ᵥ Pi.single i 1 ≠ 0 := fun h0 => by
      have h1 : P⁻¹ *ᵥ (P *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      have := congrFun h1 i
      simp at this
    have h1 := isTotallyPos_rat (hpd _ hne)
    have e : (formF (up Q)).eval (P *ᵥ Pi.single i 1) = a i := by
      rw [QuadForm.eval]
      rw [show (formF (up Q)).evalIn ℚ (P *ᵥ Pi.single i 1) = (QuadForm.diag a).evalIn ℚ (Pi.single i 1) from hx]
      rw [QuadForm.evalIn_diag]
      simp [Pi.single_apply]
    rw [← e]; exact h1
  choose r hr0 hr using fun i => exists_sq_realPlace (w := w.1) w.2 (hpos i)
  have hsig : sigVec ℚ (sigPos n w) = fun _ => 1 := by
    funext i; unfold sigVec sigPos; simp [i.2]
  rw [hsig, isometricIn_map_iff]
  refine QuadForm.isometricIn_trans _ (FieldGen.isometricIn_of_base _ hQa) ?_
  refine ⟨Matrix.diagonal fun i => (r i)⁻¹, by simp [Matrix.det_diagonal, Finset.prod_ne_zero_iff, hr0], fun x => ?_⟩
  rw [QuadForm.evalIn_diag, QuadForm.evalIn_diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal, eq_ratCast (algebraMap ℚ w.1.Completion), eq_ratCast (algebraMap ℚ w.1.Completion),
    ← hr i, Rat.cast_one]
  field_simp [hr0 i]


theorem loc_intVec_eq_locAct_one {n : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) :
    loc v (Tamagawa.stdLat ℚ n).1 = locAct v 1 (std v) := by
  rw [locAct_one]; exact loc_intVec v

/-- The local genus of $\mathbb Z^n$ on $(\mathbb Q^n, Q)$ is the class of $Q$ over $\mathcal O_{\mathfrak p}$. -/
theorem formTuple_eq {n : ℕ} (Q : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) :
    formTuple Q v = LocGenus.mk (QuadForm.toO v (localForm (formF (up Q)) v 1)
      (localForm_coeff_integral v _ _ (isIntegral_intVec_formF _) (loc_intVec_eq_locAct_one v))) :=
  locGenusOf_eq v _ _ _ (loc_intVec_eq_locAct_one v)

/-- The coefficients of the local form of $\mathbb Z^n$ are those of $Q$. -/
theorem coeff_toO_localForm_one {n : ℕ} (Q : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) (h) (i j : Fin n) :
    (QuadForm.toO v (localForm (formF (up Q)) v 1) h).coeff i j = (Q.coeff i j : v.adicCompletionIntegers ℚ) := by
  apply Subtype.ext
  change (localForm (formF (up Q)) v 1).coeff i j = _
  rw [localForm, Units.val_one, QuadForm.compMat_one, formF_up]
  simp [QuadForm.map]

/-- **Primitivity at every prime** of a primitive integral form ($\gcd$ of the coefficients $1$). -/
theorem prim_formTuple {n : ℕ} {Q : QuadForm ℤ n} (hp : Hanke2011Ternary.IsPrimitiveForm Q)
    (v : HeightOneSpectrum (𝓞 ℚ)) : (formTuple Q v).Prim := by
  rw [formTuple_eq, LocGenus.prim_mk]
  -- the coefficients of `Q` generate `ℤ`
  have hI : Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2) = ⊤ := by
    obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal
      (Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2))).principal
    have hdiv : ∀ i j, d ∣ Q.coeff i j := fun i j => by
      have : Q.coeff i j ∈ Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2) :=
        Ideal.subset_span (Set.mem_range.mpr ⟨(i, j), rfl⟩)
      rw [hd] at this
      exact Ideal.mem_span_singleton.mp this
    rw [hd]
    exact Ideal.span_singleton_eq_top.mpr (hp d hdiv)
  have h1 : (1 : ℤ) ∈ Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2) := by rw [hI]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h1
  unfold IsPrimitiveForm
  rw [Ideal.eq_top_iff_one]
  have e : (1 : v.adicCompletionIntegers ℚ) = ∑ p : Fin n × Fin n, (c p : v.adicCompletionIntegers ℚ) *
      (QuadForm.toO v (localForm (formF (up Q)) v 1)
        (localForm_coeff_integral v _ _ (isIntegral_intVec_formF _) (loc_intVec_eq_locAct_one v))).coeff p.1 p.2 := by
    simp_rw [coeff_toO_localForm_one]
    have := congrArg (Int.castRingHom (v.adicCompletionIntegers ℚ)) hc
    simp only [map_sum, smul_eq_mul, map_mul, map_one, eq_intCast] at this
    exact this.symm
  rw [e]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range.mpr ⟨p, rfl⟩))

/-- **$\det_H(\mathbb Z^n) = N$** on $(\mathbb Q^n, Q)$ for $\det_H(Q) = N$, as non-archimedean squareclasses. -/
theorem detH_formF_up {n : ℕ} {Q : QuadForm ℤ n} {N : ℤ} (hdet : Q.hessian.det = N) (hN : (N : ℚ) ≠ 0)
    (hQ' : (formF (up Q)).hessian.det ≠ 0) :
    detH (formF (up Q)) hQ' (Tamagawa.stdLat ℚ n) = ratS (Units.mk0 (N : ℚ) hN) := by
  refine AdelicSqCl.ext fun v => ?_
  rw [detH_comp _ _ _ v (loc_intVec_eq_locAct_one v), ratS, AdelicSqCl.comp_mk, ideleComp_unitEmbedding]
  congr 1
  apply Units.ext
  rw [localHessDet, Units.val_mk0, Units.val_one, Matrix.det_one, one_pow, mul_one, hessian_det_formF_up, hdet,
    unitsToLocal_val, Units.val_mk0]

/-- **The tuple of a form of $\mathrm{Cls}^*(N;3)$ lies in $\mathrm{Gen}^*(N, (3,0); 3)$.** -/
theorem formTuple_mem_genStar {N : ℕ} (hN : (N : ℚ) ≠ 0) {Q : QuadForm ℤ 3} (hQ : IsPrimTernary N Q) :
    formTuple Q ∈ GenStar (ratS (Units.mk0 (N : ℚ) hN)) (sigPos 3) ∅ (fun _ => 1) := by
  have hQ' : (formF (up Q)).hessian.det ≠ 0 := by
    rw [hessian_det_formF_up, hQ.2.2]; exact_mod_cast hN
  refine ⟨formF (up Q), hQ', Tamagawa.stdLat ℚ 3, isIntegral_intVec_formF _, hasSignature_sigPos hQ.1, ?_,
    fun v => prim_formTuple hQ.2.1 v, fun v hv => absurd hv (Set.notMem_empty v), rfl⟩
  have := detH_formF_up (N := (N : ℤ)) hQ.2.2 (by exact_mod_cast hN) hQ'
  convert this using 2


/-- **The tuple is constant on a genus** (positive definite forms): forms in the same genus have the same local genera. -/
theorem formTuple_eq_of_sameGenus {Q Q' : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) (hg : SameGenus Q Q') :
    formTuple Q = formTuple Q' := by
  obtain ⟨γ, h, hs, hQ'⟩ := exists_latOf_of_sameGenus Q hQ hg
  have hgram : gramZ (formF (up Q)) γ h = up Q' := by rw [← hQ', up_down]
  funext v
  have e1 := (sameGenus_iff_locGenusOf (formF (up Q)) (Tamagawa.stdLat ℚ 3) ⟨latOf γ, latOf_isLattice γ⟩
    (isIntegral_intVec_formF _) h).mp hs v
  unfold formTuple
  rw [e1, locGenusOf_latOf v (formF (up Q)) γ h]
  congr 1
  · rw [hgram]

/-- A global isometry of forms over $\mathbb Q$ from local isometries at every place (Hasse–Minkowski, O'Meara 66:4), for
two positive definite forms with the same local genera. -/
theorem isometricIn_of_formTuple_eq {Q Q' : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) (hQ' : IntQF.PosDef Q')
    (h : formTuple Q = formTuple Q') : (formF (up Q)).IsometricIn ℚ (formF (up Q')) := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hpd' := (isTotallyPosDef_up_iff Q').mpr hQ'
  refine Tamagawa.FormClassNF.isometricIn_of_everywhere_nf _ _ hpd.nondegenerate hpd'.nondegenerate fun v => ?_
  cases v with
  | finite v =>
    dsimp only [NFPlace.atPlace]
    let _ : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    have hv := congrFun h v
    rw [formTuple_eq, formTuple_eq, LocGenus.mk_eq_mk] at hv
    have hv' := Tamagawa.RatBridge.isometricGL_map_hom (algebraMap _ (v.adicCompletion ℚ)) hv
    rw [QuadForm.map_toO, QuadForm.map_toO, localForm, localForm, Units.val_one, QuadForm.compMat_one,
      QuadForm.compMat_one, isometricGL_iff_isometricIn, isometricIn_map_iff] at hv'
    convert hv' using 2
  | infinite w =>
    dsimp only [NFPlace.atPlace]
    have hw : w.IsReal := IsTotallyReal.isReal w
    let _ : Algebra ℚ w.Completion := InfinitePlace.Completion.instAlgebra w ℚ
    have h1 := (isometricIn_map_iff _ _).mp (hasSignature_sigPos hQ ⟨w, hw⟩)
    have h2 := (isometricIn_map_iff _ _).mp (hasSignature_sigPos hQ' ⟨w, hw⟩)
    exact QuadForm.isometricIn_trans _ h1 (QuadForm.isometricIn_symm _ h2)

/-- **Equal local genera give the same genus** (positive definite forms; Lemma 3.7, injectivity of the localization
map). -/
theorem sameGenus_of_formTuple_eq {Q Q' : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) (hQ' : IntQF.PosDef Q')
    (h : formTuple Q = formTuple Q') : SameGenus Q Q' := by
  obtain ⟨P, hP, hPx⟩ := isometricIn_of_formTuple_eq hQ hQ' h
  set γ : GL (Fin 3) ℚ := ((Matrix.isUnit_iff_isUnit_det P).mpr hP).unit
  have hγP : γ.val = P := rfl
  have hval : ∀ x : Fin 3 → 𝓞 ℚ,
      (formF (up Q)).eval (γ.val *ᵥ intCoe x) = algebraMap (𝓞 ℚ) ℚ ((up Q').eval x) := by
    intro x
    have := hPx (intCoe x)
    rw [hγP, QuadForm.eval]
    rw [show (formF (up Q)).evalIn ℚ (P *ᵥ intCoe x) = (formF (up Q')).evalIn ℚ (intCoe x) from this]
    rw [← QuadForm.eval, ← eval_map_comp]
  have hint : IsIntegral (formF (up Q)) (latOf γ) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_glImage.mp hy
    obtain ⟨x, rfl⟩ := mem_intVec_iff_exists.mp hw
    exact ⟨(up Q').eval x, (hval x).symm⟩
  have hG : gramZ (formF (up Q)) γ hint = up Q' :=
    QuadForm.ext_eval fun x => IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [algebraMap_eval_gramZ, hval])
  have hloc : ∀ v, locGenusOf v (formF (up Q)) (Tamagawa.stdLat ℚ 3) (isIntegral_intVec_formF _) =
      locGenusOf v (formF (up Q)) ⟨latOf γ, latOf_isLattice γ⟩ hint := by
    intro v
    rw [locGenusOf_latOf v (formF (up Q)) γ hint]
    have e : locGenusOf v (formF (gramZ (formF (up Q)) γ hint)) ⟨intVec, intVec_isLattice⟩ (isIntegral_intVec_formF _) =
        formTuple Q' v := by
      unfold formTuple; congr 1
      · rw [hG]
    rw [e, ← h]
    rfl
  have hs := (sameGenus_iff_locGenusOf (formF (up Q)) (Tamagawa.stdLat ℚ 3) ⟨latOf γ, latOf_isLattice γ⟩
    (isIntegral_intVec_formF _) hint).mpr hloc
  have := sameGenus_down_gramZ Q γ hs hint
  rwa [hG, down_up] at this


/-- **A form of positive definite signature over $\mathbb Q$ is positive definite.** -/
theorem eval_pos_of_hasSignature {n : ℕ} {V : QuadForm ℚ n} (hσ : HasSignature V (sigPos n)) {y : Fin n → ℚ}
    (hy : y ≠ 0) : 0 < V.eval y := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace ℚ, w.IsReal := ⟨Rat.infinitePlace, IsTotallyReal.isReal _⟩
  let _ : Algebra ℚ w.Completion := InfinitePlace.Completion.instAlgebra w ℚ
  obtain ⟨P, hP, hPx⟩ := hσ ⟨w, hw⟩
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set y' : Fin n → w.Completion := fun i => algebraMap ℚ w.Completion (y i)
  set x := P⁻¹ *ᵥ y'
  have hx : P *ᵥ x = y' := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have hval := hPx x
  rw [hx] at hval
  -- the left side is the image of `V(y)`, the right side a nonzero sum of squares
  have hl : V.evalIn w.Completion y' = algebraMap ℚ w.Completion (V.eval y) := by
    simp only [QuadForm.evalIn, QuadForm.eval, y', map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [Algebra.algebraMap_self]
  have hsig : sigVec ℚ (sigPos n ⟨w, hw⟩) = fun _ => 1 := by
    funext i; unfold sigVec sigPos; simp [i.2]
  rw [hsig, OMeara.evalIn_map_algebraMap, OMeara.evalIn_map_algebraMap, QuadForm.evalIn_diag, hl] at hval
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hx
    apply hy
    funext i
    have := congrFun hx i
    simp only [Pi.zero_apply, y'] at this
    exact (map_eq_zero_iff _ (algebraMap ℚ w.Completion).injective).mp this.symm
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx0 (funext h)
  have hφ := congrArg φ hval
  rw [eq_ratCast (algebraMap ℚ w.Completion), map_ratCast, map_sum] at hφ
  have hpos : (0 : ℝ) < ∑ i, φ (algebraMap ℚ w.Completion 1 * x i ^ 2) := by
    simp only [map_one, one_mul, map_pow]
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, ?_⟩
    have : φ (x i0) ≠ 0 := (map_ne_zero _).mpr hi0
    positivity
  rw [← hφ] at hpos
  exact_mod_cast hpos


/-- A nonunit integer lies in some prime of $\mathcal O_{\mathbb Q}$. -/
theorem exists_prime_mem_int {d : ℤ} (hd : ¬ IsUnit d) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (d : 𝓞 ℚ) ∈ v.asIdeal := by
  have hdu : ¬ IsUnit (d : 𝓞 ℚ) := fun h => hd (by simpa using h.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ))
  have hI : Ideal.span {(d : 𝓞 ℚ)} ≠ ⊤ := fun h => hdu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hI
  have hne : M ≠ ⊥ := (Ideal.bot_lt_of_maximal M (RingOfIntegers.not_isField ℚ)).ne'
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.subset_span rfl)⟩

/-- **Primitivity at every prime gives primitivity** of an integral form. -/
theorem isPrimitiveForm_of_prim_formTuple {n : ℕ} {Q : QuadForm ℤ n} (h : ∀ v, (formTuple Q v).Prim) :
    Hanke2011Ternary.IsPrimitiveForm Q := by
  intro d hd
  by_contra hu
  obtain ⟨v, hv⟩ := exists_prime_mem_int hu
  have hp := h v
  rw [formTuple_eq, LocGenus.prim_mk] at hp
  unfold IsPrimitiveForm at hp
  -- `d` lies in the maximal ideal of `𝔬_𝔭`
  have hdm : ((d : ℤ) : v.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h1
    let _ : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    have h2 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (d : ℚ)) < 1 := by
      rw [valued_algebraMap]
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) v (d : 𝓞 ℚ)).mpr hv
      exact_mod_cast this
    have h3 : ((((d : ℤ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)) =
        algebraMap ℚ (v.adicCompletion ℚ) (d : ℚ) := by
      rw [map_intCast]; push_cast; rfl
    rw [h3] at h1
    exact absurd h1 h2.ne
  have hle : Ideal.span (Set.range fun p : Fin n × Fin n =>
      (QuadForm.toO v (localForm (formF (up Q)) v 1)
        (localForm_coeff_integral v _ _ (isIntegral_intVec_formF _) (loc_intVec_eq_locAct_one v))).coeff p.1 p.2) ≤
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    simp only [coeff_toO_localForm_one]
    obtain ⟨k, hk⟩ := hd i j
    rw [hk, Int.cast_mul]
    exact Ideal.mul_mem_right _ _ hdm
  rw [hp] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- **Two positive integers with the same non-archimedean squareclass are equal.** -/
theorem eq_of_ratS_eq {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (ha' : (a : ℚ) ≠ 0) (hb' : (b : ℚ) ≠ 0)
    (h : ratS (Units.mk0 (a : ℚ) ha') = ratS (Units.mk0 (b : ℚ) hb')) : a = b := by
  set q : ℚ := (b : ℚ) / a with hq
  have hq0 : q ≠ 0 := div_ne_zero hb' ha'
  -- `q` is a unit at every prime
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q = 1 := by
    intro v
    let _ : Algebra ℚ (v.adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    have hv := congrArg (AdelicSqCl.comp v) h
    simp only [ratS, AdelicSqCl.comp_mk, ideleComp_unitEmbedding] at hv
    obtain ⟨u, hu, hue⟩ := SqCl.exists_eq_mul_sq hv
    have hu1 := (mem_localUnits_iff v).mp hu
    have e : algebraMap ℚ (v.adicCompletion ℚ) q = (u : v.adicCompletion ℚ) ^ 2 := by
      have := congrArg Units.val hue
      rw [Units.val_mul, Units.val_pow_eq_pow_val, unitsToLocal_val, unitsToLocal_val, Units.val_mk0,
        Units.val_mk0] at this
      have ha0 : algebraMap ℚ (v.adicCompletion ℚ) (a : ℚ) ≠ 0 := (map_ne_zero _).mpr ha'
      rw [hq, map_div₀, this]
      field_simp
    rw [← valued_algebraMap, e, map_pow, hu1, one_pow]
  have hint : ∀ x : ℚ, (∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ x ≤ 1) → ∃ z : ℤ, (z : ℚ) = x := by
    intro x hx
    obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ x hx
    exact ⟨Rat.ringOfIntegersEquiv z, by rw [Rat.ringOfIntegersEquiv_apply_coe, hz]⟩
  obtain ⟨z, hz⟩ := hint q fun v => (hval v).le
  obtain ⟨z', hz'⟩ := hint q⁻¹ fun v => by rw [map_inv₀, hval v, inv_one]
  have hzz : z * z' = 1 := by
    have : (z : ℚ) * z' = 1 := by rw [hz, hz', mul_inv_cancel₀ hq0]
    exact_mod_cast this
  have hqpos : 0 < q := div_pos (by exact_mod_cast hb) (by exact_mod_cast ha)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hzz with h1 | h1
  · have : q = 1 := by rw [← hz, h1]; simp
    rw [hq, div_eq_one_iff_eq ha'] at this
    exact_mod_cast this.symm
  · have : q = -1 := by rw [← hz, h1]; simp
    linarith


/-- **Lemma 3.7 over $\mathbb Q$, surjectivity onto the genera of integral forms:** every tuple of
$\mathrm{Gen}^*(N,(3,0);3)$ is the tuple of a form of $\mathrm{Cls}^*(N;3)$ (every lattice over $\mathbb Z$ is free). -/
theorem exists_form_of_mem_genStar {N : ℕ} (hN0 : 0 < N) (hN : (N : ℚ) ≠ 0) {c : HeightOneSpectrum (𝓞 ℚ) → ℤ}
    {t : LocTuple ℚ 3} (ht : t ∈ GenStar (ratS (Units.mk0 (N : ℚ) hN)) (sigPos 3) ∅ c) :
    ∃ Q : QuadForm ℤ 3, IsPrimTernary N Q ∧ formTuple Q = t := by
  obtain ⟨V, hV, L, hL, hσ, hS, hprim, -, rfl⟩ := ht
  obtain ⟨γ, hγ⟩ := exists_latOf_of_isPrincipalIdealRing L
  have hLeq : L = ⟨latOf γ, latOf_isLattice γ⟩ := Subtype.ext hγ
  subst hLeq
  set Q₀ := gramZ V γ hL with hQ₀
  have hupQ : up (down Q₀) = Q₀ := up_down Q₀
  -- the tuple
  have htup : formTuple (down Q₀) = fun v => locGenusOf v V ⟨latOf γ, latOf_isLattice γ⟩ hL := by
    funext v
    rw [locGenusOf_latOf v V γ hL]
    unfold formTuple
    congr 1
    · rw [hupQ]
  -- primitive
  have hprimQ : Hanke2011Ternary.IsPrimitiveForm (down Q₀) :=
    isPrimitiveForm_of_prim_formTuple fun v => by rw [htup]; exact hprim v
  -- positive definite
  have hpd : IntQF.PosDef (down Q₀) := by
    intro x hx
    set x' : Fin 3 → 𝓞 ℚ := fun i => (x i : 𝓞 ℚ)
    have hxx : (fun i => Rat.ringOfIntegersEquiv (x' i)) = x := by
      funext i; simp [x']
    have e1 := down_map_eval Q₀ x'
    rw [hxx] at e1
    have e2 : (((down Q₀).eval x : ℤ) : ℚ) = V.eval (γ.val *ᵥ intCoe x') := by
      rw [e1, Rat.ringOfIntegersEquiv_apply_coe, algebraMap_eval_gramZ]
    have hne : γ.val *ᵥ intCoe x' ≠ 0 := by
      intro h0
      apply hx
      have h1 : intCoe x' = 0 := by
        have := congrArg (fun y => γ⁻¹.val *ᵥ y) h0
        simpa [Matrix.mulVec_mulVec] using this
      funext i
      have := congrFun h1 i
      simpa [x', intCoe] using this
    have := eval_pos_of_hasSignature hσ hne
    rw [← e2] at this
    exact_mod_cast this
  -- the determinant
  have hdetpos := Siegel.det_hessian_pos hpd
  have hQ' : (formF (up (down Q₀))).hessian.det ≠ 0 := by
    rw [hessian_det_formF_up]; exact_mod_cast hdetpos.ne'
  have hdet : (down Q₀).hessian.det = N := by
    have h1 := detH_formF_up (Q := down Q₀) (N := (down Q₀).hessian.det) rfl
      (by exact_mod_cast hdetpos.ne') hQ'
    have h2 : detH (formF (up (down Q₀))) hQ' (Tamagawa.stdLat ℚ 3) = detH V hV ⟨latOf γ, latOf_isLattice γ⟩ :=
      AdelicSqCl.ext fun v => by
        rw [← (det_locGenusOf v _ hQ' _ (isIntegral_intVec_formF _)).2, ← (det_locGenusOf v V hV _ hL).2]
        congr 1
        exact congrFun htup v
    rw [h2, hS] at h1
    have := eq_of_ratS_eq (a := (N : ℤ)) (b := (down Q₀).hessian.det) (by exact_mod_cast hN0) hdetpos
      (by exact_mod_cast hN) (by exact_mod_cast hdetpos.ne') (by
        convert h1 using 2)
    exact this.symm
  exact ⟨down Q₀, ⟨hpd, hprimQ, hdet⟩, htup⟩


/-! ### The sum over the genera as $T^*$, and the reduction of the payoff to local data -/

/-- The local form of $\mathbb Z^n$ at $\mathfrak p$ is $Q$ over $\mathcal O_{\mathfrak p}$ (`NF.Qp`). -/
theorem toO_localForm_one_eq_Qp {n : ℕ} (Q : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) (h) :
    QuadForm.toO v (localForm (formF (up Q)) v 1) h = LocalDensity.NF.Qp v (up Q) := by
  apply QuadForm.map_injective_O v
  simp only
  rw [QuadForm.map_toO, localForm, Units.val_one, QuadForm.compMat_one, Tamagawa.map_Qp_eq]

/-- **The local densities of the local genera of $Q$** are Hanke's local densities of $Q$. -/
theorem beta_formTuple {n : ℕ} (Q : QuadForm ℤ n) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (formTuple Q v).beta = localBeta v (up Q) := by
  rw [formTuple_eq, LocGenus.beta_mk, betaForm, toO_localForm_one_eq_Qp]
  rfl

/-- The inverse local densities of a positive definite ternary form are multipliable, with product the inverse of the
product of the densities. -/
theorem hasProd_inv_localBeta {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) :
    HasProd (fun v => (localBeta v (up Q))⁻¹) (∏' v, localBeta v (up Q))⁻¹ := by
  have hpd := (isTotallyPosDef_up_iff Q).mpr hQ
  have hnd : (up Q).Nondegenerate := Tamagawa.nondegenerate_of_map hpd.nondegenerate
  have hgram : ∀ v, localBeta v (up Q) =
      ‖(2 : v.adicCompletion ℚ)‖ ^ (3 * (3 - 1) / 2) * LocalDensity.NF.siegelDensity v (up Q) (up Q) :=
    fun v => Hanke2005.hankeBeta_gramV v (up Q) hnd
  have hm2 : Multipliable fun v : HeightOneSpectrum (𝓞 ℚ) => ‖(2 : v.adicCompletion ℚ)‖ ^ (3 * (3 - 1) / 2) :=
    multipliable_of_hasFiniteMulSupport (Hanke2005.hasFiniteMulSupport_norm_two.pow _)
  have hms := Tamagawa.multipliable_siegelDensity (by norm_num) (by norm_num) (up Q) hnd
  have hm : Multipliable fun v => localBeta v (up Q) := by
    simp_rw [hgram]; exact hm2.mul hms
  have hne : ∏' v, localBeta v (up Q) ≠ 0 := by
    have h := Hanke2005.tprod_hankeBeta (up Q) hnd (by norm_num) (by norm_num)
    have hs := Tamagawa.tprod_siegelDensity_ne_zero (up Q) hpd (Tamagawa.LatChange.isIntegral_std (up Q))
      (Tamagawa.massFormulaHolds_ternary_nf (up Q) hpd)
    unfold localBeta
    rw [h]
    exact mul_ne_zero (inv_ne_zero (by positivity)) hs
  exact hm.hasProd.inv₀ hne

/-- **The summand of $T^*$ at the tuple of $Q$ is $\prod_p\beta_{Q,p}(Q)^{-1}$.** -/
theorem invDensityTuple_formTuple {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) :
    invDensityTuple (formTuple Q) = invDensityProd Q := by
  classical
  have h := hasProd_inv_localBeta hQ
  have hb : (fun v => ((formTuple Q v).beta)⁻¹) = fun v => (localBeta v (up Q))⁻¹ := by
    funext v; rw [beta_formTuple]
  unfold invDensityTuple invDensityProd
  rw [hb, ite_eq_left_iff.mpr (fun hn => absurd h.multipliable hn), h.tprod_eq]

open Classical in
/-- A representative form of a genus of $\mathrm{Cls}^*(N;3)$. -/
def genusRep (N : ℕ) (G : Set (QClass 3)) : QuadForm ℤ 3 :=
  if h : ∃ Q : QuadForm ℤ 3, IsPrimTernary N Q ∧ genusClasses Q = G then h.choose else QuadForm.diag fun _ => 0

theorem genusRep_spec {N : ℕ} {G : Set (QClass 3)} (hG : G ∈ primitiveTernaryGenera N) :
    IsPrimTernary N (genusRep N G) ∧ genusClasses (genusRep N G) = G := by
  classical
  obtain ⟨c, hc, rfl⟩ := hG
  have hex : ∃ Q : QuadForm ℤ 3, IsPrimTernary N Q ∧ genusClasses Q = genusClasses c.out :=
    ⟨c.out, mem_primitiveTernaryClasses_iff.mp hc, rfl⟩
  unfold genusRep
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- **The sum over the genera of $\mathrm{Cls}^*(N;3)$ is $T^*_{(3,0);3}(N)$** (Definition 3.4 over $\mathbb Q$): the localization
map is a bijection from the genera onto $\mathrm{Gen}^*(N,(3,0);3)$ (`formTuple_mem_genStar`, `sameGenus_of_formTuple_eq`,
`exists_form_of_mem_genStar`) preserving the inverse density products. -/
@[kb "hanke2011structure" "Def. 3.4, p. 12, and Lemma 3.7, p. 13 (F = Q, n = 3: genera of forms = Gen*)"]
theorem sum_genera_eq_totalMassT {N : ℕ} (hN0 : 0 < N) (hN : (N : ℚ) ≠ 0) :
    ∑ᶠ G ∈ primitiveTernaryGenera N, genusInvDensity N G =
      totalMassT (ratS (Units.mk0 (N : ℚ) hN)) (sigPos 3) ∅ (fun _ => 1) := by
  unfold totalMassT
  refine finsum_mem_eq_of_bijOn (fun G => formTuple (genusRep N G)) ⟨?_, ?_, ?_⟩ ?_
  · intro G hG
    exact formTuple_mem_genStar hN (genusRep_spec hG).1
  · intro G1 hG1 G2 hG2 h12
    have h1 := genusRep_spec hG1
    have h2 := genusRep_spec hG2
    have hs := sameGenus_of_formTuple_eq h1.1.1 h2.1.1 h12
    rw [← h1.2, ← h2.2]
    exact genusClasses_eq_of_sameGenus hs
  · intro t ht
    obtain ⟨Q, hQ, rfl⟩ := exists_form_of_mem_genStar hN0 hN ht
    have hc : classOf Q ∈ Hanke2011Ternary.primitiveTernaryClasses N := ⟨Q, rfl, hQ.1, hQ.2.1, hQ.2.2⟩
    have he : IntEquiv Q (classOf Q).out := classOf_eq_classOf_iff.mp (Quotient.out_eq _).symm
    refine ⟨genusClasses Q, ⟨classOf Q, hc, (genusClasses_eq_of_sameGenus he.sameGenus).symm⟩, ?_⟩
    have hG : genusClasses Q ∈ primitiveTernaryGenera N :=
      ⟨classOf Q, hc, (genusClasses_eq_of_sameGenus he.sameGenus).symm⟩
    obtain ⟨-, hr2⟩ := genusRep_spec hG
    show formTuple (genusRep N (genusClasses Q)) = formTuple Q
    generalize genusRep N (genusClasses Q) = R at hr2 ⊢
    -- the representative is in the genus of `Q`
    have hmem : classOf R ∈ genusClasses Q := by
      have := classOf_self_mem_genusClasses R
      rwa [hr2] at this
    obtain ⟨Q', hQ', hs⟩ := hmem
    have hs' : SameGenus Q R := hs.trans (IntEquiv.sameGenus (classOf_eq_classOf_iff.mp hQ'))
    exact (formTuple_eq_of_sameGenus hQ.1 hs').symm
  · intro G hG
    have hr := genusRep_spec hG
    rw [show genusInvDensity N G = genusInvDensity N (genusClasses (genusRep N G)) by rw [hr.2],
      genusInvDensity_eq hr.1, invDensityTuple_formTuple hr.1.1]

/-- **Named input: the local mass formula for primitive positive definite ternary forms over $\mathbb Q$.** For every
$N \ge 1$, the primitive total adelic non-archimedean mass of the true local genera (Definition 3.5, `totalMassM`) is
$$M^*_{1;3}(N) = \sum_{(G_p)\in\mathrm{Gen}^*_f(N,1;3)}\prod_p\beta_{G_p,p}(G_p)^{-1} = 2\zeta(2)\,\big(A^*_3(N) + B^*_3(N)\big),$$
with paper 7's $A^*_3(N)$, $B^*_3(N)$ (`Hanke2011Ternary.globalA`, `Hanke2011Ternary.globalB`). Field: `mass_eq`.

A purely local statement: it concerns tuples of local genera of $\mathbb Z_p$-forms (one at each prime) with $\det_H = N$
and $\prod_pc_p = 1$, and Hanke's local densities; no global forms, classes or masses. It is paper 6's Theorem 4.8 for the
true local data (proved here for abstract finite data, `LocalGenusData.theorem_4_8_mass`) with Remark 4.14
($\beta^{-1}_{3,f} = 4\zeta(2)$), and paper 7's identification of the true local data with its local models (Lemma 2.3
from Conway–Sloane at $p$ odd, Table 5.3 at $p = 2$). It implies `TernaryGenusDensityFormula` (`lemma_3_7` and the bridge
`sum_genera_eq_totalMassT`), hence paper 7's `PrimitiveMassLocalFormula`. -/
@[kb "hanke2011structure" "Def. 3.5, p. 12, Thm. 4.8, p. 17, Rem. 4.14, p. 20; hanke2011ternary §§2–7"]
structure TernaryLocalMassFormula : Prop where
  /-- $M^*_{1;3}(N) = 2\zeta(2)(A^*_3(N) + B^*_3(N))$ for $N \ge 1$. -/
  mass_eq : ∀ N : ℕ, (hN : (N : ℚ) ≠ 0) →
    totalMassM 3 (ratS (Units.mk0 (N : ℚ) hN)) 1 ∅ (fun _ => 1) =
      2 * (Real.pi ^ 2 / 6) * ((Hanke2011Ternary.globalA N + Hanke2011Ternary.globalB N : ℚ) : ℝ)

/-- **Lemma 3.7 over $\mathbb Q$ for the positive definite ternary genera:** the sum over the genera of $\mathrm{Cls}^*(N;3)$
of $\prod_p\beta_{G,p}(G)^{-1}$ is $M^*_{1;3}(N)$, the sum over the tuples of local genera. -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (F = Q, n = 3, positive definite)"]
theorem sum_genera_eq_totalMassM {N : ℕ} (hN0 : 0 < N) (hN : (N : ℚ) ≠ 0) :
    ∑ᶠ G ∈ primitiveTernaryGenera N, genusInvDensity N G =
      totalMassM 3 (ratS (Units.mk0 (N : ℚ) hN)) 1 ∅ (fun _ => 1) := by
  rw [sum_genera_eq_totalMassT hN0 hN, ← epsInf_sigPos 3]
  refine (lemma_3_7 (by norm_num) _ _ _ _ (Units.mk0 (N : ℚ) hN) (fun v => ?_) (fun w => ?_)).2
  · simp only [ratS, AdelicSqCl.comp_mk, ideleComp_unitEmbedding, rhoLocal_mk]
  · let _ : Algebra ℚ w.1.Completion := InfinitePlace.Completion.instAlgebra w.1 ℚ
    obtain ⟨r, -, hr⟩ := exists_sq_realPlace w.2 (show (0 : ℚ) < (-1) ^ (sigPos 3 w).1.2 * N by
      simp [sigPos]; exact_mod_cast hN0)
    refine ⟨r, ?_⟩
    rw [eq_ratCast (algebraMap ℚ w.1.Completion), Units.val_mk0, ← hr, sq]

/-- **The payoff, reduced to local data:** `TernaryLocalMassFormula` implies `TernaryGenusDensityFormula`. -/
theorem ternaryGenusDensityFormula_of_local (H : TernaryLocalMassFormula) : TernaryGenusDensityFormula := by
  refine ⟨fun N hN => ?_⟩
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [sum_genera_eq_totalMassM (Nat.pos_of_ne_zero hN) hN', H.mass_eq N hN']

/-- **Paper 7's named input `PrimitiveMassLocalFormula` from the local mass formula.** -/
@[kb "hanke2011structure" "Cor. 6.4, p. 26, Lemma 3.7, p. 13 (F = Q, n = 3)"]
theorem primitiveMassLocalFormula_of_local (H : TernaryLocalMassFormula) :
    Hanke2011Ternary.PrimitiveMassLocalFormula :=
  primitiveMassLocalFormula_of_genus (ternaryGenusDensityFormula_of_local H)

/-- **Paper 7, Corollary 8.2 (primitive part), under the local input `TernaryLocalMassFormula`.** -/
@[kb "hanke2011ternary" "§8, Cor. 8.2, p. 27 (primitive part), via paper 6 Lemma 3.7 and Cor. 6.3–6.4"]
theorem cor_8_2_primitive_of_local (H : TernaryLocalMassFormula) :
    Hanke2011Ternary.DMass3star = (1 / 48 : ℚ) • (Hanke2011Ternary.twoPowNegS *
      ((Hanke2011Ternary.zetaShiftZ 1 (-1) * Hanke2011Ternary.zetaShiftZ 2 (-1) -
        Hanke2011Ternary.zetaShiftZ 2 (-2) * Hanke2011Ternary.zetaShiftZ 1 0) *
          Hanke2011Ternary.zetaShiftInv 3 0)) :=
  Hanke2011Ternary.cor_8_2_primitive (primitiveMassLocalFormula_of_local H)

/-- **Paper 7, Theorem 1.1, under the local input `TernaryLocalMassFormula`.** -/
@[kb "hanke2011ternary" "§1, Thm. 1.1, p. 2, via paper 6 Lemma 3.7 and Cor. 6.3–6.4"]
theorem theorem_1_1_of_local (H : TernaryLocalMassFormula) :
    (∀ m : ℕ, m ≠ 0 → Hanke2011Ternary.TMass3 (2 * m) = (1 / 48) *
      ∑ ab ∈ (m.divisors ×ˢ m.divisors).filter (fun ab => ab.1 * ab.2 ^ 2 = m),
        ((ab.1 : ℚ) * ab.2 - (ab.2 : ℚ) ^ 2)) ∧
    (∀ N : ℕ, ¬ 2 ∣ N → Hanke2011Ternary.TMass3 N = 0) :=
  Hanke2011Ternary.theorem_1_1 (primitiveMassLocalFormula_of_local H)

end

end QuadFormsKB.Hanke2011Structure
