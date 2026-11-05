/-
# Hanke 2011, Lemma 3.7, part C: every admissible tuple of local genera comes from a global lattice

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §3, Lemma 3.7, p. 13 (surjectivity of the localization map).

Given a tuple $(G_{\mathfrak p})_{\mathfrak p} \in \mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$ with $S$ globally rational,
$\rho_f(S) = \Delta(\alpha)$, and with the sign of $\alpha$ at every real place $w$ equal to $(-1)^{\sigma_{w,-}}$:

* `exists_global_space`: there is a nondegenerate space $(F^n, V)$ of signature $\vec\sigma_\infty$ with
  $V \otimes F_{\mathfrak p} \cong G_{\mathfrak p} \otimes F_{\mathfrak p}$ at every prime (O'Meara 72:1, `OMeara.exists_global_iff`; its
  conditions follow from $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$, the product $\prod_{\mathfrak p}c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon_\infty$ and
  Hilbert reciprocity for $(-1, \alpha/2^n)$).
-/
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37
import QuadFormsKB.Literature.Hanke2011Structure.SquareclassSeries

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### Squares at the infinite places -/

/-- At a complex place every element of $F_w \cong \mathbb C$ is a square. -/
theorem isSquare_complexPlace {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) : IsSquare x := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e x) (n := 2) (by norm_num)
  refine ⟨e.symm s, ?_⟩
  apply e.injective
  rw [map_mul, RingEquiv.apply_symm_apply, ← sq, hs]

/-- At a real place, $2^k$ is a square in $F_w \cong \mathbb R$. -/
theorem isSquare_two_pow_realPlace {w : InfinitePlace F} (hw : w.IsReal) (k : ℕ) :
    IsSquare ((2 : w.Completion) ^ k) := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  refine ⟨φ.symm (Real.sqrt 2 ^ k), ?_⟩
  apply φ.injective
  rw [map_mul, RingEquiv.apply_symm_apply, map_pow, map_ofNat, ← mul_pow, Real.mul_self_sqrt (by norm_num)]

/-! ### The sign vectors at the infinite places -/

/-- The product of the entries of the sign vector is $(-1)^{\sigma_-}$. -/
theorem prod_sigVec (K : Type*) [Field K] (p : SigPair n) : ∏ i, sigVec K p i = (-1) ^ p.1.2 := by
  have e : ∀ i : Fin n, sigVec K p i = (-1) ^ (if (i : ℕ) < p.1.1 then 0 else 1) := fun i => by
    unfold sigVec; split_ifs <;> simp
  simp_rw [e]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => if i < p.1.1 then 0 else 1) n,
    sum_range_not_lt]
  congr 1
  have := p.2
  omega

open Classical in
/-- The diagonal vectors used at the infinite places: the sign vector of $\vec\sigma_\infty$ at a real place, $1$ at a
complex place. -/
def infVec (σ : SignatureVector F n) (w : InfinitePlace F) : Fin n → F :=
  if h : w.IsReal then sigVec F (σ ⟨w, h⟩) else fun _ => 1

open Classical in
theorem infVec_ne_zero (σ : SignatureVector F n) (w : InfinitePlace F) (i : Fin n) : infVec σ w i ≠ 0 := by
  unfold infVec
  split_ifs
  · exact sigVec_ne_zero F _ i
  · exact one_ne_zero

/-! ### The global space -/

/-- The diagonalization over $F_{\mathfrak p}$ of a nondegenerate local genus representative. -/
theorem exists_diag_out (v : HeightOneSpectrum (𝓞 F)) (G : LocGenus v n) (hG : G.Nondeg) :
    ((G.out.map (algebraMap _ (v.adicCompletion F))).Nondegenerate) := by
  have h : G.out.hessian.det ≠ 0 := by
    have := hG
    rw [← Quotient.out_eq G] at this
    exact this
  unfold QuadForm.Nondegenerate
  rw [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (algebraMap_ne_zero_iff (v := v)).mpr h

/-- **Step C1 (O'Meara 72:1).** For a tuple $(G_{\mathfrak p}) \in \mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$, $S$ globally
rational with $\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ at every prime, and $(-1)^{\sigma_{w,-}}\alpha$ a square at every real
place $w$, there is a nondegenerate quadratic space $(F^n, V)$ of signature $\vec\sigma_\infty$ with
$V\otimes F_{\mathfrak p} \cong G_{\mathfrak p}\otimes F_{\mathfrak p}$ for every prime $\mathfrak p$. -/
theorem exists_global_space (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) {t : LocTuple F n} (ht : t ∈ GenStarF S (epsInf σ) 𝕊 c) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    ∃ V : QuadForm F n, V.hessian.det ≠ 0 ∧ HasSignature V σ ∧
      ∀ v, (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
        ((t v).out.map (algebraMap _ (v.adicCompletion F))) := by
  classical
  obtain ⟨hloc, -, hsupp, hprod⟩ := ht
  set T : ∀ v : HeightOneSpectrum (𝓞 F), QuadForm (v.adicCompletionIntegers F) n := fun v => (t v).out with hTdef
  have htT : ∀ v, t v = LocGenus.mk (T v) := fun v => (Quotient.out_eq _).symm
  have hTnd : ∀ v, ((T v).map (algebraMap _ (v.adicCompletion F))).Nondegenerate :=
    fun v => exists_diag_out v (t v) (hloc v).1
  -- the local diagonalizations
  set u : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → v.adicCompletion F :=
    fun v => Classical.choose (FieldGen.exists_isometric_diag _ (hTnd v)) with hudef
  have hu : ∀ v, (∀ i, u v i ≠ 0) ∧ ((T v).map (algebraMap _ (v.adicCompletion F))).IsometricIn
      (v.adicCompletion F) (QuadForm.diag (u v)) := fun v => Classical.choose_spec (FieldGen.exists_isometric_diag _ (hTnd v))
  have hhasse : ∀ v, (t v).hasse = PadicClass.hasseVec (u v) := by
    intro v
    rw [htT v, LocGenus.hasse_mk, hasseForm]
    unfold Composition.hasseC
    rw [dite_eq_left (hTnd v)]
  set d : F := (α : F) / 2 ^ n with hd
  have hd0 : d ≠ 0 := div_ne_zero α.ne_zero (pow_ne_zero _ two_ne_zero)
  -- (1) the determinants
  have h1 : ∀ v, IsSquare ((∏ i, u v i) / algebraMap F (v.adicCompletion F) d) := by
    intro v
    obtain ⟨P, hP, hPx⟩ := (hu v).2
    have hform : ((T v).map (algebraMap _ (v.adicCompletion F))).compMat P = QuadForm.diag (u v) :=
      QuadForm.eq_of_eval_eq fun x => by
        rw [QuadForm.eval_compMat]
        have := hPx x
        simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply] at this
        rw [QuadForm.eval, QuadForm.eval]
        exact this
    have hdet := congrArg (fun q => q.hessian.det) hform
    rw [det_hessian_compMat] at hdet
    -- $\det_H(T_{\mathfrak p}) = \alpha s^2$
    have hTd : (t v).det = AdelicSqCl.comp v S := (hloc v).2.2
    rw [htT v, LocGenus.det_mk] at hTd
    have hne : algebraMap _ (v.adicCompletion F) (T v).hessian.det ≠ 0 := by
      have := hTnd v
      unfold QuadForm.Nondegenerate at this
      rwa [QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    unfold detSqForm at hTd
    rw [dite_eq_left hne] at hTd
    have hr := hα v
    rw [← hTd, rhoLocal_mk] at hr
    obtain ⟨s, -, hs⟩ := SqCl.exists_eq_mul_sq hr
    have hs' : algebraMap F (v.adicCompletion F) (α : F) =
        algebraMap _ _ (T v).hessian.det * (s : v.adicCompletion F) ^ 2 := by
      have := congrArg Units.val hs
      rwa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, unitsToLocal_val] at this
    have hdiag : (QuadForm.diag (u v)).hessian.det = 2 ^ n * ∏ i, u v i := by
      unfold QuadForm.hessian QuadForm.diag
      rw [show Matrix.diagonal (u v) + (Matrix.diagonal (u v))ᵀ = Matrix.diagonal (fun i => 2 * u v i) by
        ext i j; by_cases h : i = j
        · subst h; simp [two_mul]
        · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]]
      rw [Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hdiag, QuadForm.hessian_map', ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
    have hPd : P.det ≠ 0 := hP.ne_zero
    have hs0 : (s : v.adicCompletion F) ≠ 0 := s.ne_zero
    refine ⟨P.det / s, ?_⟩
    have h2n : (2 : v.adicCompletion F) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    have hprod' : ∏ i, u v i = P.det ^ 2 * algebraMap _ _ (T v).hessian.det / 2 ^ n := by
      field_simp
      rw [hdet]; ring
    rw [hprod', hd, map_div₀, map_pow, map_ofNat, hs']
    field_simp
  -- (1') the infinite places
  have h1' : ∀ w : InfinitePlace F,
      IsSquare ((∏ i, algebraMap F w.Completion (infVec σ w i)) / algebraMap F w.Completion d) := by
    intro w
    rcases w.isReal_or_isComplex with hw | hw
    · have hv : infVec σ w = sigVec F (σ ⟨w, hw⟩) := by unfold infVec; rw [dif_pos hw]
      rw [hv, ← map_prod, prod_sigVec, ← map_div₀]
      obtain ⟨r, hr⟩ := hsign ⟨w, hw⟩
      obtain ⟨q, hq⟩ := isSquare_two_pow_realPlace (F := F) hw n
      have hα' : algebraMap F w.Completion (α : F) ≠ 0 := (map_ne_zero _).mpr α.ne_zero
      refine ⟨r * q / algebraMap F w.Completion (α : F), ?_⟩
      have e : algebraMap F w.Completion ((-1) ^ (σ ⟨w, hw⟩).1.2 / d) =
          algebraMap F w.Completion ((-1) ^ (σ ⟨w, hw⟩).1.2 * (α : F)) * 2 ^ n /
            (algebraMap F w.Completion (α : F)) ^ 2 := by
        rw [hd]
        simp only [map_div₀, map_mul, map_pow, map_neg, map_one, map_ofNat]
        field_simp
      rw [e, hr, hq]
      field_simp
    · exact isSquare_complexPlace hw _
  -- (2) the Hasse symbols at the finite places: `S_𝔭 = c_𝔭 · (-1, d)_𝔭`
  have hS : ∀ v, OMeara.hasseS (v.adicCompletion F) (u v) =
      (t v).hasse * (NFPlace.finite v).hilbert (-1) d := by
    intro v
    rw [OMeara.hasseS_eq_hasseVec_mul v (u v) (hu v).1, hhasse v]
    congr 1
    obtain ⟨r, hr⟩ := h1 v
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [mul_zero, div_eq_zero_iff] at hr
      rcases hr with h | h
      · exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hu v).1 i) h
      · exact (map_ne_zero _).mpr hd0 h
    have hpr : ∏ i, u v i = r ^ 2 * algebraMap F (v.adicCompletion F) d := by
      rw [sq, ← hr, div_mul_cancel₀ _ ((map_ne_zero _).mpr hd0)]
    rw [hpr, PadicClass.hs_sq_right _ _ _ hr0]
    simp only [NFPlace.hilbert, map_neg, map_one]
  obtain ⟨hHsupp, hHprod⟩ := NFPlace.finprod_hilbert (-1 : F) d (by norm_num) hd0
  have hfinH : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => (NFPlace.finite v).hilbert (-1) d).Finite := by
    have : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => (NFPlace.finite v).hilbert (-1) d) ⊆
        NFPlace.finite ⁻¹' Function.mulSupport (fun v : NFPlace F => v.hilbert (-1) d) := fun v hv => hv
    exact (Set.Finite.preimage (fun _ _ _ _ h => NFPlace.finite.inj h) hHsupp).subset this
  have h2 : {v : HeightOneSpectrum (𝓞 F) | OMeara.hasseS (v.adicCompletion F) (u v) ≠ 1}.Finite := by
    refine (hsupp.union hfinH).subset fun v hv => ?_
    simp only [Set.mem_ofPred_eq, hS] at hv
    by_contra hn
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hn
    exact hv (by rw [hn.1, hn.2, one_mul])
  -- (3) the product formula
  have hinf : ∀ w : InfinitePlace F, OMeara.hasseS w.Completion (fun i => algebraMap F w.Completion (infVec σ w i)) =
      (if h : w.IsReal then hasseReal (σ ⟨w, h⟩).1.2 else 1) * (NFPlace.infinite w).hilbert (-1) d := by
    intro w
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    have hmul : ∀ a b b' : w.Completion, a ≠ 0 → b ≠ 0 → b' ≠ 0 →
        hilbertSymbol _ a (b * b') = hilbertSymbol _ a b * hilbertSymbol _ a b' :=
      fun a b b' ha hb hb' => OMeara.hilbertSymbol_mul_right_infinite w ha hb hb'
    rw [OMeara.hasseS_eq_vec_mul_of_mul hmul _ (fun i => (map_ne_zero _).mpr (infVec_ne_zero σ w i))]
    rcases w.isReal_or_isComplex with hw | hw
    · rw [dif_pos hw]
      have hv : infVec σ w = sigVec F (σ ⟨w, hw⟩) := by unfold infVec; rw [dif_pos hw]
      rw [hv]
      congr 1
      · exact hasseSerre_sigVec w hw (σ ⟨w, hw⟩)
      · obtain ⟨r, hr⟩ := h1' w
        rw [hv] at hr
        have hr0 : r ≠ 0 := by
          rintro rfl
          simp only [mul_zero, div_eq_zero_iff] at hr
          rcases hr with h | h
          · exact Finset.prod_ne_zero_iff.mpr (fun i _ => (map_ne_zero _).mpr (sigVec_ne_zero F _ i)) h
          · exact (map_ne_zero _).mpr hd0 h
        have hpr : ∏ i, algebraMap F w.Completion (sigVec F (σ ⟨w, hw⟩) i) =
            r ^ 2 * algebraMap F w.Completion d := by
          rw [sq, ← hr, div_mul_cancel₀ _ ((map_ne_zero _).mpr hd0)]
        rw [hpr, PadicClass.hs_sq_right _ _ _ hr0]
        simp only [NFPlace.hilbert, map_neg, map_one]
    · have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
      rw [dif_neg hw', one_mul]
      have e1 : PadicClass.hasseVec (fun i => algebraMap F w.Completion (infVec σ w i)) = 1 := by
        unfold PadicClass.hasseVec
        refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
        split_ifs
        · exact HasseIsoNF.hilbertSymbol_complex_place hw _ _
        · rfl
      rw [e1, one_mul, HasseIsoNF.hilbertSymbol_complex_place hw]
      simp only [NFPlace.hilbert]
      rw [HasseIsoNF.hilbertSymbol_complex_place hw]
  have h3 : (∏ᶠ v : HeightOneSpectrum (𝓞 F), OMeara.hasseS (v.adicCompletion F) (u v)) *
      ∏ w : InfinitePlace F, OMeara.hasseS w.Completion (fun i => algebraMap F w.Completion (infVec σ w i)) = 1 := by
    simp only [hS, hinf]
    rw [finprod_mul_distrib hsupp hfinH, hprod, Finset.prod_mul_distrib]
    have hreal : ∏ w : InfinitePlace F, (if h : w.IsReal then hasseReal (σ ⟨w, h⟩).1.2 else 1) = epsInf σ := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
      have hc : ∏ w : {w : InfinitePlace F // ¬ w.IsReal}, (if h : w.1.IsReal then hasseReal (σ ⟨w.1, h⟩).1.2 else 1) = 1 :=
        Finset.prod_eq_one fun w _ => dif_neg w.2
      rw [hc, mul_one]
      unfold epsInf
      exact Finset.prod_congr rfl fun w _ => dif_pos w.2
    rw [hreal]
    have hrec := hHprod
    rw [OMeara.finprod_nfPlace _ hHsupp] at hrec
    have hε := epsInf_mem σ
    calc epsInf σ * (∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert (-1) d) *
          (epsInf σ * ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1) d)
        = (epsInf σ * epsInf σ) * ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (NFPlace.finite v).hilbert (-1) d) *
            ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (-1) d) := by ring
      _ = 1 := by
        rw [hrec, mul_one]
        rcases hε with h | h <;> rw [h] <;> norm_num
  -- apply 72:1
  obtain ⟨V, hV, hVloc, hVinf⟩ := (OMeara.exists_global_iff n u (fun v => (hu v).1)
    (fun w i => algebraMap F w.Completion (infVec σ w i))
    (fun w i => (map_ne_zero _).mpr (infVec_ne_zero σ w i))).mpr ⟨⟨d, hd0, h1, h1'⟩, h2, h3⟩
  refine ⟨V, hV, fun w => ?_, fun v => ?_⟩
  · have := hVinf w.1
    have hv : infVec σ w.1 = sigVec F (σ w) := by unfold infVec; rw [dif_pos w.2]
    rw [hv, ← OMeara.map_diag'] at this
    exact this
  · exact QuadForm.isometricIn_trans _ (hVloc v) (QuadForm.isometricIn_symm _ (hu v).2)

/-! ### Local bases -/

/-- Over a local ring, a form with unit Hessian determinant is primitive ($n \ge 1$). -/
theorem isPrimitiveForm_of_isUnit_det {R : Type*} [CommRing R] [IsLocalRing R] (hn : 1 ≤ n) (Q : QuadForm R n)
    (h : IsUnit Q.hessian.det) : IsPrimitiveForm Q := by
  by_contra hp
  have hle : Ideal.span (Set.range fun p : Fin n × Fin n => Q.coeff p.1 p.2) ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hp
  have hc : ∀ i j, Q.coeff i j ∈ IsLocalRing.maximalIdeal R := fun i j =>
    hle (Ideal.subset_span (Set.mem_range.mpr ⟨(i, j), rfl⟩))
  have hH : ∀ i j, Q.hessian i j ∈ IsLocalRing.maximalIdeal R := fun i j => by
    unfold QuadForm.hessian
    exact Ideal.add_mem _ (hc i j) (hc j i)
  have hdet : Q.hessian.det ∈ IsLocalRing.maximalIdeal R := by
    rw [Matrix.det_apply]
    refine Ideal.sum_mem _ fun σ _ => ?_
    have i0 : Fin n := ⟨0, hn⟩
    rw [Units.smul_def]
    refine Submodule.smul_of_tower_mem _ _ ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0)]
    exact Ideal.mul_mem_right _ _ (hH _ _)
  exact (IsLocalRing.mem_maximalIdeal _).mp hdet h

/-- $2$ is a unit of $\mathcal O_{\mathfrak p}$ at a prime $\mathfrak p \nmid 2$. -/
theorem isUnit_two_of_not_mem (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    IsUnit (2 : v.adicCompletionIntegers F) := by
  have hnd : ¬ LocalDensity.NF.π v ∣ (2 : v.adicCompletionIntegers F) := by
    have := (LocalDensity.NF.π_pow_dvd_ι_iff v 1 2).not.mpr (by rwa [pow_one])
    rwa [pow_one, map_ofNat] at this
  exact LocalDensity.DVR.dvr_isUnit_of_not_dvd (LocalDensity.NF.irreducible_π v) hnd

/-- A local squareclass $[x]$ which is a unit class has $x \in \mathcal O_{\mathfrak p}^\times$. -/
theorem mem_localUnits_of_mk_mem (v : HeightOneSpectrum (𝓞 F)) {x : (v.adicCompletion F)ˣ}
    (h : (SqCl.mk x : LocalSqCl v) ∈ localUnitSqCl F v) : x ∈ localUnits v := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨w, hw, hx⟩ := SqCl.exists_eq_mul_sq he
  rw [hx]
  exact (localUnits v).mul_mem hu ((localUnits v).pow_mem hw 2)

/-- An isometry over $F_{\mathfrak p}$ as a composition: $(V\otimes F_{\mathfrak p})\circ g = T\otimes F_{\mathfrak p}$. -/
theorem exists_compMat_of_isometricIn (v : HeightOneSpectrum (𝓞 F)) {V : QuadForm F n}
    {T : QuadForm (v.adicCompletionIntegers F) n}
    (h : (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
      (T.map (algebraMap _ (v.adicCompletion F)))) :
    ∃ g : GL (Fin n) (v.adicCompletion F),
      (V.map (algebraMap F (v.adicCompletion F))).compMat g.val = T.map (algebraMap _ (v.adicCompletion F)) := by
  obtain ⟨P, hP, hPx⟩ := h
  refine ⟨Matrix.nonsingInvUnit P hP, QuadForm.eq_of_eval_eq fun x => ?_⟩
  rw [QuadForm.eval_compMat]
  have := hPx x
  simp only [QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [QuadForm.eval, QuadForm.eval]
  exact this

/-- **The good primes (Theorem 2.6 for $\mathfrak p \nmid 2$).** If $V$ has $\mathcal O_{\mathfrak p}$-coefficients with unit Hessian
determinant (`VO`), $T$ is primitive with unit Hessian determinant and $V \cong T$ over $F_{\mathfrak p}$, then
$V\circ U = T$ for some $U \in \mathrm{GL}_n(\mathcal O_{\mathfrak p})$. -/
theorem exists_unit_basis_of_good (hn : 1 ≤ n) (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (V : QuadForm F n) (VO T : QuadForm (v.adicCompletionIntegers F) n)
    (hVO : VO.map (algebraMap _ (v.adicCompletion F)) = V.map (algebraMap F (v.adicCompletion F)))
    (hVOunit : IsUnit VO.hessian.det) (hTprim : IsPrimitiveForm T) (hTunit : IsUnit T.hessian.det)
    (hiso : (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
      (T.map (algebraMap _ (v.adicCompletion F)))) :
    ∃ U : GL (Fin n) (v.adicCompletionIntegers F),
      (V.map (algebraMap F (v.adicCompletion F))).compMat
        (Matrix.GeneralLinearGroup.map (algebraMap _ (v.adicCompletion F)) U).val =
      T.map (algebraMap _ (v.adicCompletion F)) := by
  obtain ⟨P, hP⟩ := exists_compMat_of_isometricIn v hiso
  rw [← hVO] at hP
  -- $\det_H(T) = \det(P)^2\det_H(V_O)$ over $F_{\mathfrak p}$
  have hdetP : algebraMap _ (v.adicCompletion F) T.hessian.det =
      P.val.det ^ 2 * algebraMap _ (v.adicCompletion F) VO.hessian.det := by
    have := congrArg (fun q => q.hessian.det) hP
    simp only [det_hessian_compMat, QuadForm.hessian_map'] at this
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      eq_comm] at this
  -- the two determinants are units of `𝔬_𝔭`, equal modulo squares of units
  set a : (v.adicCompletion F)ˣ := Units.map (algebraMap _ (v.adicCompletion F)).toMonoidHom hVOunit.unit
  set b : (v.adicCompletion F)ˣ := Units.map (algebraMap _ (v.adicCompletion F)).toMonoidHom hTunit.unit
  have ha : a ∈ localUnits v := ⟨hVOunit.unit, rfl⟩
  have hb : b ∈ localUnits v := ⟨hTunit.unit, rfl⟩
  have hab : (SqCl.mk a : LocalSqCl v) = SqCl.mk b := by
    refine localSqCl_eq_of_rho ha hb ?_
    rw [rhoLocal_mk]
    have hPu : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
    refine (SqCl.mk_mul_sq a (Subgroup.mem_top hPu.unit)).symm.trans ?_
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    change algebraMap _ _ VO.hessian.det * _ = algebraMap _ _ T.hessian.det
    rw [hdetP, mul_comm]
  obtain ⟨w, ⟨u0, hu0⟩, hwe⟩ := SqCl.exists_eq_mul_sq hab
  have hdetT : T.hessian.det = (u0 : v.adicCompletionIntegers F) ^ 2 * VO.hessian.det := by
    apply IsFractionRing.injective (v.adicCompletionIntegers F) (v.adicCompletion F)
    have := congrArg Units.val hwe
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← hu0] at this
    change algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) T.hessian.det =
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) VO.hessian.det *
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (u0 : v.adicCompletionIntegers F)) ^ 2 at this
    rw [map_mul, map_pow, this, mul_comm]
  have hiso' := (uniqueNormalizedLocalGenus_completion v h2 n).unique VO T
    (isPrimitiveForm_of_isUnit_det hn VO hVOunit) hTprim
    (by
      unfold IsNormalizedHessian
      rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hVOunit]
      split_ifs
      · rfl
      · exact (IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (isUnit_two_of_not_mem v h2)).symm)
    u0 u0.isUnit hdetT
  obtain ⟨U, hU⟩ := isometricGL_iff_compMat.mp hiso'
  refine ⟨U, ?_⟩
  rw [hU, ← QuadForm.map_compMat, hVO]
  rfl

/-- **Step C2.** With $V$ as in step C1 there are local bases $g_{\mathfrak p}$ with
$(V\otimes F_{\mathfrak p})\circ g_{\mathfrak p} = G_{\mathfrak p}$ at every prime and $g_{\mathfrak p}\mathcal O_{\mathfrak p}^n = \mathcal O_{\mathfrak p}^n$
at almost every prime (at the primes $\mathfrak p \nmid 2$ where $V$ is $\mathcal O_{\mathfrak p}$-unimodular and $S_{\mathfrak p}$ is a
unit class, by Theorem 2.6, `uniqueNormalizedLocalGenus_completion`). -/
theorem exists_local_bases (hn : 1 ≤ n) (S : AdelicSqCl F) (ε : ℤ) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) {t : LocTuple F n} (ht : t ∈ GenStarF S ε 𝕊 c) (V : QuadForm F n)
    (hV : V.hessian.det ≠ 0)
    (hVloc : ∀ v, (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
      ((t v).out.map (algebraMap _ (v.adicCompletion F)))) :
    ∃ g : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F),
      (∀ v, (V.map (algebraMap F (v.adicCompletion F))).compMat (g v).val =
        (t v).out.map (algebraMap _ (v.adicCompletion F))) ∧
      ∀ᶠ v in Filter.cofinite, locAct v (g v) (std v) = std v := by
  classical
  -- the good primes
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    (∀ i j, v.valuation F (V.coeff i j) ≤ 1) ∧
    Units.mk0 (algebraMap F (v.adicCompletion F) V.hessian.det) ((map_ne_zero _).mpr hV) ∈ localUnits v ∧
    (2 : 𝓞 F) ∉ v.asIdeal ∧ AdelicSqCl.comp v S ∈ localUnitSqCl F v
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    have hS : ∀ᶠ v in Filter.cofinite, adelicOrd v S = 0 := by
      have := supp_finite S
      rw [Filter.eventually_cofinite]
      simpa [supp] using this
    filter_upwards [Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
        eventually_valuation_le_one (V.coeff i j),
      eventually_algebraMap_mem_localUnits hV, eventually_not_mem (two_ne_zero : (2 : 𝓞 F) ≠ 0), hS]
      with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, mem_localUnitSqCl_of_ordZ v h4⟩
  have hex : ∀ v, ∃ g : GL (Fin n) (v.adicCompletion F),
      (V.map (algebraMap F (v.adicCompletion F))).compMat g.val = (t v).out.map (algebraMap _ (v.adicCompletion F)) ∧
        (good v → locAct v g (std v) = std v) := by
    intro v
    by_cases hv : good v
    · obtain ⟨hint, hdetV, h2, hSv⟩ := hv
      have htT : t v = LocGenus.mk (t v).out := (Quotient.out_eq _).symm
      obtain ⟨hTnd, hTprim, hTdet⟩ := (ht.1 v)
      rw [htT, LocGenus.nondeg_mk] at hTnd
      rw [htT, LocGenus.prim_mk] at hTprim
      rw [htT, LocGenus.det_mk] at hTdet
      have hVint : ∀ i j, (V.map (algebraMap F (v.adicCompletion F))).coeff i j ∈ v.adicCompletionIntegers F :=
        fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
          show Valued.v (algebraMap F (v.adicCompletion F) (V.coeff i j)) ≤ 1
          rw [valued_algebraMap]; exact hint i j)
      obtain ⟨VO, hVOmap⟩ : ∃ VO : QuadForm (v.adicCompletionIntegers F) n,
          VO.map (algebraMap _ (v.adicCompletion F)) = V.map (algebraMap F (v.adicCompletion F)) :=
        ⟨_, QuadForm.map_toO v _ hVint⟩
      have hVOdet : algebraMap _ (v.adicCompletion F) VO.hessian.det = algebraMap F _ V.hessian.det := by
        have := congrArg (fun q => q.hessian.det) hVOmap
        simp only [QuadForm.hessian_map'] at this
        rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      have hVOunit : IsUnit VO.hessian.det := by
        refine HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ?_
        have e : ((VO.hessian.det : v.adicCompletionIntegers F) : v.adicCompletion F) =
            algebraMap F _ V.hessian.det := hVOdet
        rw [e]
        have h := (mem_localUnits_iff v).mp hdetV
        rwa [Units.val_mk0] at h
      have hTne : algebraMap _ (v.adicCompletion F) (t v).out.hessian.det ≠ 0 :=
        (algebraMap_ne_zero_iff (v := v)).mpr hTnd
      rw [detSqForm_of_ne hTne] at hTdet
      have hTunitF : Units.mk0 _ hTne ∈ localUnits v := mem_localUnits_of_mk_mem v (hTdet ▸ hSv)
      have hTunit : IsUnit (t v).out.hessian.det := by
        refine HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr ?_
        have h := (mem_localUnits_iff v).mp hTunitF
        rwa [Units.val_mk0] at h
      obtain ⟨U, hU⟩ := exists_unit_basis_of_good hn v h2 V VO (t v).out hVOmap hVOunit hTprim hTunit (hVloc v)
      exact ⟨_, hU, fun _ => locAct_map_std v U⟩
    · obtain ⟨g, hg⟩ := exists_compMat_of_isometricIn v (hVloc v)
      exact ⟨g, hg, fun h => absurd h hv⟩
  choose g hg hgg using hex
  refine ⟨g, hg, ?_⟩
  filter_upwards [hgood] with v hv
  exact hgg v hv

/-- The local lattices $g_{\mathfrak p}\mathcal O_{\mathfrak p}^n$, almost all standard. -/
def basisFamily (g : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hg : ∀ᶠ v in Filter.cofinite, locAct v (g v) (std v) = std v) : LocFamily F n where
  M v := locAct v (g v) (std v)
  isLattice v := locAct_isLattice _ (isLattice_of_bounds v le_rfl le_rfl)
  eventually_std := hg

/-- **Step C3: Lemma 3.7, surjectivity** (p. 13, with the sign hypothesis, see the module docstring of `Lemma37.lean`):
if $S$ is globally rational, $\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ for every prime, and $(-1)^{\sigma_{w,-}}\alpha$ is a square at
every real place $w$, then every tuple of $\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$ is the tuple of local genera
of a primitive $\mathcal O_F$-valued lattice $L$ on a space of signature $\vec\sigma_\infty$ with $\det_H(L) = S$ (O'Meara 72:1 for
the space, Theorem 2.6 for $\mathfrak p \nmid 2$, and O'Meara 81:14 for the lattice). -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (surjectivity of λ; corrected hypothesis)"]
theorem genStarF_subset_genStar (hn : 1 ≤ n) (S : AdelicSqCl F) (σ : SignatureVector F n)
    (𝕊 : Set (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → ℤ) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    GenStarF S (epsInf σ) 𝕊 c ⊆ GenStar S σ 𝕊 c := by
  intro t ht
  obtain ⟨V, hV, hσV, hVloc⟩ := exists_global_space S σ 𝕊 c ht α hα hsign
  obtain ⟨g, hg, hgev⟩ := exists_local_bases hn S (epsInf σ) 𝕊 c ht V hV hVloc
  let M : LocFamily F n := basisFamily g hgev
  let L : Lat F n := ⟨M.glue, M.glue_isLattice⟩
  have hloc : ∀ v, loc v L.1 = locAct v (g v) (std v) := fun v => M.loc_glue v
  -- `L` is `𝒪_F`-valued: its values are integral at every prime
  have hLi : IsIntegral V L.1 := by
    intro x hx
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
    have hxv : locVec v x ∈ locAct v (g v) (std v) := by rw [← hloc v]; exact locVec_mem_loc v hx
    obtain ⟨y, hy, hyx⟩ := mem_locAct.mp hxv
    rw [← valued_algebraMap, ← evalIn_locVec V v x, ← hyx]
    have e : V.evalIn (v.adicCompletion F) ((g v).val *ᵥ y) =
        ((t v).out.map (algebraMap _ (v.adicCompletion F))).eval y := by
      rw [← hg v, QuadForm.eval_compMat]
      unfold QuadForm.eval QuadForm.evalIn QuadForm.map
      simp
    rw [e]
    have hy' : ∀ i, y i ∈ v.adicCompletionIntegers F := fun i =>
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (by
        have := (mem_ball v).mp hy i
        simpa using this)
    set y' : Fin n → v.adicCompletionIntegers F := fun i => ⟨y i, hy' i⟩
    have hyy : y = fun i => algebraMap _ (v.adicCompletion F) (y' i) := rfl
    have hev : ((t v).out.map (algebraMap _ (v.adicCompletion F))).eval y =
        algebraMap _ (v.adicCompletion F) (((t v).out).eval y') := by
      rw [hyy]
      unfold QuadForm.eval QuadForm.evalIn QuadForm.map
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [hev]
    exact (((t v).out).eval y').2
  have htv : ∀ v, locGenusOf v V L hLi = t v := by
    intro v
    rw [locGenusOf_eq v V L hLi (hloc v)]
    conv_rhs => rw [← Quotient.out_eq (t v)]
    congr 1
    apply QuadForm.map_injective_O v
    simp only
    rw [QuadForm.map_toO]
    exact hg v
  refine ⟨V, hV, L, hLi, hσV, ?_, fun v => ?_, fun v hv => ?_, funext htv⟩
  · exact AdelicSqCl.ext fun v => by rw [← (det_locGenusOf v V hV L hLi).2, htv, (ht.1 v).2.2]
  · rw [htv]; exact (ht.1 v).2.1
  · rw [htv]; exact ht.2.1 v hv

/-! ### Definitions 3.4 and 3.5, and Lemma 3.7 -/

open Classical in
/-- The summand of Definitions 3.4 and 3.5: $\prod_{\mathfrak p}\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$ when the infinite product
converges, and $0$ otherwise (Definition 3.5: "when the infinite product converges, and zero otherwise"). -/
def invDensityTuple (t : LocTuple F n) : ℝ :=
  if Multipliable (fun v => ((t v).beta)⁻¹) then ∏' v, ((t v).beta)⁻¹ else 0

/-- **Definition 3.4** (p. 12): the *primitive total rational non-archimedean mass*
$T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S) = \sum_{G\in\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)}\prod_{\mathfrak p}\beta_{G,\mathfrak p}(G)^{-1}$
(a `finsum` over the genera, represented by their local genera; Hanke's densities in Gram coordinates). -/
@[kb "hanke2011structure" "Def. 3.4, p. 12"]
def totalMassT (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) : ℝ :=
  ∑ᶠ t ∈ GenStar S σ 𝕊 c, invDensityTuple t

/-- **Definition 3.5** (p. 12), for the true local genera: the *primitive total adelic non-archimedean mass*
$M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S) = \sum_{(G_{\mathfrak p})\in\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)}\prod_{\mathfrak p}
\beta_{G_{\mathfrak p},\mathfrak p}(G_{\mathfrak p})^{-1}$. -/
@[kb "hanke2011structure" "Def. 3.5, p. 12 (true local genera)"]
def totalMassM (m : ℕ) (S : AdelicSqCl F) (ε : ℤ) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) : ℝ :=
  ∑ᶠ t ∈ (GenStarF S ε 𝕊 c : Set (LocTuple F m)), invDensityTuple t

/-- **Lemma 3.7** (p. 13), with the sign hypothesis that the formalization shows is needed (see `Lemma37.lean`): let
$n \ge 1$, $S$ globally rational with $\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ at every prime ($\alpha \in F^\times$), and suppose
$(-1)^{\sigma_{w,-}}\alpha$ is a square at every real place $w$ (i.e. $\alpha$ has the sign $(-1)^{\sigma_{w,-}}$ there). Then the
localization map identifies $\mathrm{Gen}^*(S,\vec\sigma_\infty,\vec c_{\mathbb S};n)$ with $\mathrm{Gen}^*_f(S,\varepsilon_\infty,\vec c_{\mathbb S};n)$,
$\varepsilon_\infty = \prod_{v\mid\infty}c_v((\vec\sigma_\infty)_v)$, and
$$T^*_{\vec\sigma_\infty,\vec c_{\mathbb S};n}(S) = M^*_{\varepsilon_\infty,\vec c_{\mathbb S};n}(S).$$ -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (corrected hypothesis)"]
theorem lemma_3_7 (hn : 1 ≤ n) (S : AdelicSqCl F) (σ : SignatureVector F n) (𝕊 : Set (HeightOneSpectrum (𝓞 F)))
    (c : HeightOneSpectrum (𝓞 F) → ℤ) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    GenStar S σ 𝕊 c = GenStarF S (epsInf σ) 𝕊 c ∧ totalMassT S σ 𝕊 c = totalMassM n S (epsInf σ) 𝕊 c := by
  have h : GenStar S σ 𝕊 c = GenStarF S (epsInf σ) 𝕊 c :=
    (genStar_subset_genStarF S σ 𝕊 c).antisymm (genStarF_subset_genStar hn S σ 𝕊 c α hα hsign)
  exact ⟨h, by unfold totalMassT totalMassM; rw [h]⟩

end

end QuadFormsKB.Hanke2011Structure
