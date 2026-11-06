/-
# Hanke 2011, Lemma 3.7 and Corollary 6.3 for not necessarily primitive lattices

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §3, Lemma 3.7, p. 13, and §6, Corollary 6.3, p. 26;
J. Hanke, *Explicit formulas for masses of ternary quadratic lattices of varying determinant over number fields*,
arXiv:1109.1054 (bib key `hanke2011ternary`), §8, p. 27.

The files `Lemma37.lean`, `Lemma37Exist.lean` and `GlobalMassSummed.lean` treat the genera of *primitive*
$\mathcal O_F$-valued lattices. The ternary paper's Theorem 8.1 also needs the total masses of *all* (not necessarily
primitive) $\mathcal O_F$-valued lattices of Hessian determinant $S$. This file removes primitivity:

* `GenAll S σ` (the set of tuples of local genera of $\mathcal O_F$-valued lattices on nondegenerate spaces of signature
  $\vec\sigma_\infty$ with $\det_H(L) = S$) and `GenAllF S ε` (tuples of nondegenerate local genera with
  $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$, almost all Hasse invariants $1$, product $\varepsilon$);
* `genAll_subset_genAllF`, `genAllF_subset_genAll`: the non-primitive Lemma 3.7 (same hypotheses as `lemma_3_7`);
* `IsRealizationAll`, `massOfTupleAll`: the mass of a tuple;
* `massOfTupleAll_eq`, `sum_massOfTupleAll_eq`: the non-primitive Corollary 6.3, summed over all genera, for totally
  real $F$ and $n \ge 3$.

The proofs follow those of the primitive versions. Primitivity is used there only at the primes where the Hessian
determinant is a unit, and there it is automatic (`isPrimitiveForm_of_isUnit_det`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassSummed
import QuadFormsKB.Literature.Hanke2011Structure.Lemma37Exist

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices QuadFormsKB.HilbertModular Real

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-! ### The sets of tuples -/

/-- **$\mathrm{Gen}(S,\vec\sigma_\infty;n)$, all lattices** (ternary paper §8, p. 27): the tuples of local genera
$(L_{\mathfrak p})_{\mathfrak p}$ of $\mathcal O_F$-valued lattices $L$ (not necessarily primitive) on nondegenerate
spaces $(F^n, Q)$ of signature $\vec\sigma_\infty$ with $\det_H(L) = S$. Fields of the defining condition: the quadratic
form `Q` over $F$, nondegeneracy `hQ` of its Hessian, the lattice `L`, integrality `hL` ($Q(L) \subseteq \mathcal O_F$),
the signature condition, the determinant condition $\det_H(L) = S$, and equality of the tuple with the tuple of local
genera of $L$. -/
@[kb "hanke2011ternary" "§8, p. 27 (Gen(λ(a), σ; 3), all O_F-valued lattices)"]
def GenAll (S : AdelicSqCl F) (σ : SignatureVector F n) : Set (LocTuple F n) :=
  {t | ∃ (Q : QuadForm F n) (hQ : Q.hessian.det ≠ 0) (L : Lat F n) (hL : IsIntegral Q L.1),
    HasSignature Q σ ∧ detH Q hQ L = S ∧ (fun v => locGenusOf v Q L hL) = t}

/-- **$\mathrm{Gen}_f(S,\varepsilon;n)$, all lattices** (ternary paper §8, p. 27): the tuples $(G_{\mathfrak p})_{\mathfrak p}$ of
nondegenerate local genera (not necessarily primitive) with $\det_H(G_{\mathfrak p}) = S_{\mathfrak p}$ at every prime, with
$c_{\mathfrak p}(G_{\mathfrak p}) = 1$ for almost all $\mathfrak p$, and $\prod_{\mathfrak p}c_{\mathfrak p}(G_{\mathfrak p}) = \varepsilon$. -/
@[kb "hanke2011ternary" "§8, p. 27 (Gen(λ(a), σ; 3), all O_F-valued lattices)"]
def GenAllF (S : AdelicSqCl F) (ε : ℤ) : Set (LocTuple F n) :=
  {t | (∀ v, (t v).Nondeg ∧ (t v).det = AdelicSqCl.comp v S) ∧
    (Function.mulSupport fun v => (t v).hasse).Finite ∧ ∏ᶠ v, (t v).hasse = ε}

/-- **The localization map lands in $\mathrm{Gen}_f$** (Lemma 3.7, p. 13, non-primitive lattices). -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (non-primitive lattices)"]
theorem genAll_subset_genAllF (S : AdelicSqCl F) (σ : SignatureVector F n) :
    GenAll S σ ⊆ GenAllF S (epsInf σ) := by
  rintro t ⟨Q, hQ, L, hL, hσ, hS, rfl⟩
  obtain ⟨hfin, hprod⟩ := finprod_hasse_locGenusOf Q hQ L hL σ hσ
  refine ⟨fun v => ⟨(det_locGenusOf v Q hQ L hL).1, ?_⟩, hfin, hprod⟩
  rw [(det_locGenusOf v Q hQ L hL).2, hS]

/-! ### The global space -/

/-- **Step C1 (O'Meara 72:1), non-primitive.** For a tuple $(G_{\mathfrak p}) \in \mathrm{Gen}_f(S,\varepsilon_\infty;n)$ with
$\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ at every prime and $(-1)^{\sigma_{w,-}}\alpha$ a square at every real place $w$, there
is a nondegenerate space $(F^n, V)$ of signature $\vec\sigma_\infty$ with $V\otimes F_{\mathfrak p} \cong G_{\mathfrak p}\otimes F_{\mathfrak p}$ for
every prime $\mathfrak p$. (Verbatim `exists_global_space`; primitivity of $G_{\mathfrak p}$ is not used there.) -/
theorem exists_global_space_all (S : AdelicSqCl F) (σ : SignatureVector F n)
    {t : LocTuple F n} (ht : t ∈ GenAllF S (epsInf σ)) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    ∃ V : QuadForm F n, V.hessian.det ≠ 0 ∧ HasSignature V σ ∧
      ∀ v, (V.map (algebraMap F (v.adicCompletion F))).IsometricIn (v.adicCompletion F)
        ((t v).out.map (algebraMap _ (v.adicCompletion F))) := by
  classical
  obtain ⟨hloc, hsupp, hprod⟩ := ht
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
    have hTd : (t v).det = AdelicSqCl.comp v S := (hloc v).2
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

/-- **Step C2, non-primitive.** With $V$ as in step C1 there are local bases $g_{\mathfrak p}$ with
$(V\otimes F_{\mathfrak p})\circ g_{\mathfrak p} = G_{\mathfrak p}$ at every prime and $g_{\mathfrak p}\mathcal O_{\mathfrak p}^n = \mathcal O_{\mathfrak p}^n$ at almost
every prime. At the good primes the determinant of $G_{\mathfrak p}$ is a unit, so $G_{\mathfrak p}$ is primitive anyway
(`isPrimitiveForm_of_isUnit_det`). -/
theorem exists_local_bases_all (hn : 1 ≤ n) (S : AdelicSqCl F) (ε : ℤ)
    {t : LocTuple F n} (ht : t ∈ GenAllF S ε) (V : QuadForm F n)
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
      obtain ⟨hTnd, hTdet⟩ := (ht.1 v)
      rw [htT, LocGenus.nondeg_mk] at hTnd
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
      have hTprim : IsPrimitiveForm (t v).out := isPrimitiveForm_of_isUnit_det hn _ hTunit
      obtain ⟨U, hU⟩ := exists_unit_basis_of_good hn v h2 V VO (t v).out hVOmap hVOunit hTprim hTunit (hVloc v)
      exact ⟨_, hU, fun _ => locAct_map_std v U⟩
    · obtain ⟨g, hg⟩ := exists_compMat_of_isometricIn v (hVloc v)
      exact ⟨g, hg, fun h => absurd h hv⟩
  choose g hg hgg using hex
  refine ⟨g, hg, ?_⟩
  filter_upwards [hgood] with v hv
  exact hgg v hv

/-! ### Lemma 3.7, non-primitive -/

/-- **Lemma 3.7, surjectivity, non-primitive lattices** (p. 13): if $S$ is globally rational,
$\rho_{\mathfrak p}(S_{\mathfrak p}) = \alpha$ at every prime and $(-1)^{\sigma_{w,-}}\alpha$ is a square at every real place $w$, then every
tuple of $\mathrm{Gen}_f(S,\varepsilon_\infty;n)$ is the tuple of local genera of an $\mathcal O_F$-valued lattice $L$ on a space of
signature $\vec\sigma_\infty$ with $\det_H(L) = S$. Together with `genAll_subset_genAllF` this identifies
$\mathrm{Gen}(S,\vec\sigma_\infty;n)$ with $\mathrm{Gen}_f(S,\varepsilon_\infty;n)$. -/
@[kb "hanke2011structure" "Lemma 3.7, p. 13 (non-primitive lattices)"]
theorem genAllF_subset_genAll (hn : 1 ≤ n) (S : AdelicSqCl F) (σ : SignatureVector F n) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal},
      IsSquare (algebraMap F w.1.Completion ((-1) ^ (σ w).1.2 * (α : F)))) :
    GenAllF S (epsInf σ) ⊆ GenAll S σ := by
  intro t ht
  obtain ⟨V, hV, hσV, hVloc⟩ := exists_global_space_all S σ ht α hα hsign
  obtain ⟨g, hg, hgev⟩ := exists_local_bases_all hn S (epsInf σ) ht V hV hVloc
  let M : LocFamily F n := basisFamily g hgev
  let L : Lat F n := ⟨M.glue, M.glue_isLattice⟩
  have hloc : ∀ v, loc v L.1 = locAct v (g v) (std v) := fun v => M.loc_glue v
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
  refine ⟨V, hV, L, hLi, hσV, ?_, funext htv⟩
  exact AdelicSqCl.ext fun v => by rw [← (det_locGenusOf v V hV L hLi).2, htv, (ht.1 v).2]

/-! ### The mass of a tuple of local genera, all lattices -/

/-- **$(Q, L)$ realizes the tuple $t$ of $\mathrm{Gen}(S,\vec\sigma_\infty;n)$:** $Q$ nondegenerate of signature
$\vec\sigma_\infty$, $L$ an $\mathcal O_F$-valued lattice with $\det_H(L) = S$ and tuple of local genera $t$. -/
def IsRealizationAll (S : AdelicSqCl F) (σ : SignatureVector F n) (t : LocTuple F n) (Q : QuadForm F n)
    (L : Lat F n) : Prop :=
  ∃ (hQ : Q.hessian.det ≠ 0) (hL : IsIntegral Q L.1), HasSignature Q σ ∧ detH Q hQ L = S ∧
    (fun v => locGenusOf v Q L hL) = t

theorem mem_genAll_iff (S : AdelicSqCl F) (σ : SignatureVector F n) (t : LocTuple F n) :
    t ∈ GenAll S σ ↔ ∃ p : QuadForm F n × Lat F n, IsRealizationAll S σ t p.1 p.2 := by
  constructor
  · rintro ⟨Q, hQ, L, hL, h⟩
    exact ⟨(Q, L), hQ, hL, h⟩
  · rintro ⟨⟨Q, L⟩, hQ, hL, h⟩
    exact ⟨Q, hQ, L, hL, h⟩

open Classical in
/-- **The mass of a tuple of local genera** $t \in \mathrm{Gen}(S,\vec\sigma_\infty;n)$ (all lattices): the mass
`Lattices.mass Q L` of a chosen realization $(Q, L)$ of $t$ (`IsRealizationAll`); $0$ if $t \notin \mathrm{Gen}$. It does not
depend on the choice (`mass_eq_of_realizationAll`). -/
@[kb "hanke2011ternary" "§8, p. 27 (Gen(λ(a), σ; 3), all O_F-valued lattices)"]
def massOfTupleAll (S : AdelicSqCl F) (σ : SignatureVector F n) (t : LocTuple F n) : ℝ :=
  if h : ∃ p : QuadForm F n × Lat F n, IsRealizationAll S σ t p.1 p.2 then
    Lattices.mass h.choose.1 h.choose.2
  else 0

section Sum

variable [IsTotallyReal F]

/-- **The mass of any realization of a tuple $t \in \mathrm{Gen}$** (totally positive signature, all lattices) is
$C(S)\prod_\mathfrak p\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (non-primitive lattices)"]
theorem mass_eq_of_realizationAll (S : AdelicSqCl F) (hn : 3 ≤ n) {t : LocTuple F n} {Q : QuadForm F n} {L : Lat F n}
    (h : IsRealizationAll S (totPosSig F n) t Q L) :
    Lattices.mass Q L = massConst F n S * invDensityTuple t := by
  obtain ⟨hQ, hL, hσ, hS, rfl⟩ := h
  rw [mass_of_rep hn hQ L hL hσ, hS]

/-- **The mass of a tuple of local genera, all lattices:** for $t \in \mathrm{Gen}(S,\vec\sigma_\infty;n)$ with $\vec\sigma_\infty$
totally positive, `massOfTupleAll t` $= C(S)\prod_\mathfrak p\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}$. -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (non-primitive lattices)"]
theorem massOfTupleAll_eq (S : AdelicSqCl F) (hn : 3 ≤ n) {t : LocTuple F n} (ht : t ∈ GenAll S (totPosSig F n)) :
    massOfTupleAll S (totPosSig F n) t = massConst F n S * invDensityTuple t := by
  have h := (mem_genAll_iff S (totPosSig F n) t).mp ht
  unfold massOfTupleAll
  rw [dif_pos h]
  exact mass_eq_of_realizationAll S hn h.choose_spec

/-- For totally positive signature, $\varepsilon_\infty = 1$ (every real Hasse invariant of $(n,0)$ is $1$). -/
theorem epsInf_totPosSig_all : epsInf (totPosSig F n) = 1 := by
  simp [epsInf, totPosSig, hasseReal]

/-- **Corollary 6.3 summed over all genera of (not necessarily primitive) lattices** (totally real $F$, $n \ge 3$, totally
positive definite signature; $S$ globally rational with $\rho_\mathfrak p(S_\mathfrak p) = \alpha$ at every prime, $\alpha$ a square at every real
place):
$$\sum_{t \in \mathrm{Gen}(S,\vec\sigma_\infty;n)}\mathrm{Mass}(t) = C(S)\sum_{t \in \mathrm{Gen}_f(S,1;n)}\prod_\mathfrak p\beta_{t_\mathfrak p,\mathfrak p}(t_\mathfrak p)^{-1}.$$ -/
@[kb "hanke2011structure" "Cor. 6.3, p. 26 (non-primitive lattices)"]
theorem sum_massOfTupleAll_eq (hn : 3 ≤ n) (S : AdelicSqCl F) (α : Fˣ)
    (hα : ∀ v, rhoLocal v (AdelicSqCl.comp v S) = SqCl.mk (unitsToLocal v α))
    (hsign : ∀ w : {w : InfinitePlace F // w.IsReal}, IsSquare (algebraMap F w.1.Completion (α : F))) :
    ∑ᶠ t ∈ GenAll S (totPosSig F n), massOfTupleAll S (totPosSig F n) t =
      massConst F n S * ∑ᶠ t ∈ (GenAllF S 1 : Set (LocTuple F n)), invDensityTuple t := by
  have hsub : GenAll S (totPosSig F n) = GenAllF S (epsInf (totPosSig F n)) :=
    (genAll_subset_genAllF S _).antisymm
      (genAllF_subset_genAll (by omega) S _ α hα (fun w => by simpa [totPosSig] using hsign w))
  rw [epsInf_totPosSig_all] at hsub
  rw [hsub, mul_finsum_mem]
  refine finsum_mem_congr rfl fun t ht => ?_
  exact massOfTupleAll_eq S hn (hsub ▸ ht)

end Sum

end

end QuadFormsKB.Hanke2011Structure

#print axioms QuadFormsKB.Hanke2011Structure.genAll_subset_genAllF
#print axioms QuadFormsKB.Hanke2011Structure.genAllF_subset_genAll
#print axioms QuadFormsKB.Hanke2011Structure.massOfTupleAll_eq
#print axioms QuadFormsKB.Hanke2011Structure.sum_massOfTupleAll_eq
