/-
# Hanke 2011, Cor. 6.3 summed over the genera: transport of a representative to an $\mathcal O_F$-form

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (bib key `hanke2011structure`), §6, pp. 25–27.

A representative $(Q, L)$ of a tuple in $\mathrm{Gen}^*$ has $Q$ over $F$, whereas `mass_eq_local` needs a form
$Q_0$ over $\mathcal O_F$. For $g \in \mathrm{GL}_n(F)$ the pair $(Q\circ g,\ g^{-1}L)$ has the same mass
(`mass_transport`), the same local genera (`locGenusOf_transport`), the same $\det_H$ (`detH_transport`), the same
integrality and signature (`isIntegral_transport`, `hasSignature_compMat`). Taking $g = k\cdot 1$ for an integer $k$
clearing the denominators of $Q$ gives an $\mathcal O_F$-model (`exists_integral_model`). A signature vector that is
$(n,0)$ at every real place makes $Q$ totally positive definite (`isTotallyPosDef_of_hasSignature`).
-/
import QuadFormsKB.Literature.Hanke2011Structure.GlobalMassLattice
import QuadFormsKB.Literature.Hanke2005.Lemma61
import QuadFormsKB.Tamagawa.OrbitalFrame

namespace QuadFormsKB.Hanke2011Structure

open IsDedekindDomain NumberField Matrix QuadFormsKB.Lattices QuadFormsKB.HilbertModular

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

section Transport

variable (Q : QuadForm F n) (g : GL (Fin n) F)

theorem evalIn_compMat_F (x : Fin n → F) :
    (Q.compMat g.val).evalIn F x = Q.evalIn F (g.val *ᵥ x) := by
  rw [QuadFormsKB.Tamagawa.evalIn_compMat_gl Q g F x]
  have : g.val.map (algebraMap F F) = g.val := by ext i j; simp
  rw [this]

theorem mulVec_mulVec_inv (y : Fin n → F) : g.val *ᵥ (g⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

/-- The transported lattice $g^{-1}L$ is integral for $Q\circ g$ when $L$ is integral for $Q$. -/
theorem isIntegral_transport {L : Lat F n} (hL : IsIntegral Q L.1) :
    IsIntegral (Q.compMat g.val) (Lat.image g⁻¹ L).1 := by
  rintro x ⟨y, hy, rfl⟩
  show (Q.compMat g.val).evalIn F (g⁻¹.val *ᵥ y) ∈ _
  rw [evalIn_compMat_F, mulVec_mulVec_inv]
  exact hL y hy

/-- **The mass is unchanged by the transport** $(Q, L) \mapsto (Q\circ g, g^{-1}L)$. -/
theorem mass_transport (L : Lat F n) : Lattices.mass (Q.compMat g.val) (Lat.image g⁻¹ L) = Lattices.mass Q L := by
  have h := Tamagawa.LatChange.mass_similar Q (c := 1) one_ne_zero g (Lat.image g⁻¹ L)
  rw [Tamagawa.LatChange.one_smul_form] at h
  rw [h]
  congr 1
  exact Subtype.ext (by
    show glImage g (glImage g⁻¹ L.1) = L.1
    rw [← glImage_mul, mul_inv_cancel, glImage_one])

theorem hessian_det_compMat_ne (hQ : Q.hessian.det ≠ 0) : (Q.compMat g.val).hessian.det ≠ 0 := by
  rw [QuadForm.hessian_compMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hg : g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  exact mul_ne_zero (mul_ne_zero hg hQ) hg

/-- $Q$ is isometric over any field extension to $Q\circ g$. -/
theorem isometricIn_compMat (K : Type*) [Field K] [Algebra F K] :
    Q.IsometricIn K (Q.compMat g.val) := by
  refine ⟨g.val.map (algebraMap F K), ?_, fun x => (QuadFormsKB.Tamagawa.evalIn_compMat_gl Q g K x).symm⟩
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (Matrix.GeneralLinearGroup.map (algebraMap F K) g))

/-- The signature (at every real place) is unchanged by $Q \mapsto Q\circ g$. -/
theorem hasSignature_compMat {σ : SignatureVector F n} (h : HasSignature Q σ) :
    HasSignature (Q.compMat g.val) σ := by
  intro w
  have h1 := (isometricIn_map_iff Q _).mp (h w)
  have h2 := QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ (isometricIn_compMat Q g w.1.Completion)) h1
  exact (isometricIn_map_iff _ _).mpr h2

section Local

variable (v : HeightOneSpectrum (𝓞 F))

/-- A basis of $(g^{-1}L)_{\mathfrak p}$: $g^{-1}\gamma$ for a basis $\gamma$ of $L_{\mathfrak p}$. -/
theorem locBasisTransport (L : Lat F n) :
    loc v (Lat.image g⁻¹ L).1 =
      locAct v ((GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g)⁻¹ * locBasis v L) (std v) := by
  show loc v (glImage g⁻¹ L.1) = _
  rw [loc_glImage, map_inv, locBasis_spec v L, locAct_mul]

theorem localForm_transport (L : Lat F n) :
    localForm (Q.compMat g.val) v ((GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g)⁻¹ * locBasis v L) =
      localForm Q v (locBasis v L) := by
  unfold localForm
  rw [← QuadForm.map_compMat]
  have : (g.val.map (algebraMap F (v.adicCompletion F))) =
      (GeneralLinearGroup.map (algebraMap F (v.adicCompletion F)) g).val := rfl
  rw [this, QuadForm.compMat_mul, ← Units.val_mul, mul_inv_cancel_left]

/-- **The local genera are unchanged by the transport.** -/
theorem locGenusOf_transport (L : Lat F n) (hL : IsIntegral Q L.1) :
    locGenusOf v (Q.compMat g.val) (Lat.image g⁻¹ L) (isIntegral_transport Q g hL) = locGenusOf v Q L hL := by
  rw [locGenusOf_eq v _ _ _ (locBasisTransport g v L)]
  unfold locGenusOf
  congr 1
  apply QuadForm.map_injective_O v
  simp only
  rw [QuadForm.map_toO, QuadForm.map_toO, localForm_transport]

end Local

/-- **$\det_H$ is unchanged by the transport.** -/
theorem detH_transport (hQ : Q.hessian.det ≠ 0) (L : Lat F n) :
    detH (Q.compMat g.val) (hessian_det_compMat_ne Q g hQ) (Lat.image g⁻¹ L) = detH Q hQ L := by
  apply AdelicSqCl.ext
  intro v
  rw [detH_comp _ _ _ v (locBasisTransport g v L), detH_comp Q hQ L v (locBasis_spec v L)]
  congr 1
  apply Units.ext
  rw [← det_hessian_localForm (Q.compMat g.val) (hessian_det_compMat_ne Q g hQ) v,
    ← det_hessian_localForm Q hQ v, localForm_transport]

end Transport

/-! ### An $\mathcal O_F$-model -/

/-- **Clearing denominators:** for every form $Q$ over $F$ there are $g \in \mathrm{GL}_n(F)$ and a form $Q_0$ over
$\mathcal O_F$ with $Q_0 \otimes F = Q\circ g$ (indeed $g = k\cdot 1$, $k \in \mathbb Z$, $Q\circ g = k^2Q$). -/
theorem exists_integral_model (Q : QuadForm F n) :
    ∃ (g : GL (Fin n) F) (Q₀ : QuadForm (𝓞 F) n), formF Q₀ = Q.compMat g.val := by
  classical
  obtain ⟨k, hk, hkmem⟩ := exists_int_mul_mem (Finset.univ.image fun ij : Fin n × Fin n => Q.coeff ij.1 ij.2)
  set c : F := (k : F) with hcdef
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr hk
  set g := Hanke2005.scalGLF (n := n) c hc with hg
  have key : Q.compMat g.val = c ^ 2 • Q := by
    have h := Hanke2005.compMat_scalGLF Q c hc
    ext i j
    have h' := congrArg (fun R : QuadForm F n => R.coeff i j) h
    simp only [QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul] at h' ⊢
    rw [← h', hg]
    field_simp
  have hmem : ∀ i j, (Q.compMat g.val).coeff i j ∈ (algebraMap (𝓞 F) F).range := by
    intro i j
    rw [key, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul]
    have h1 := hkmem (Q.coeff i j) (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j)))
    have h2 : c ∈ (algebraMap (𝓞 F) F).range := ⟨(k : 𝓞 F), by simp [hcdef]⟩
    have : c ^ 2 * Q.coeff i j = c * (c * Q.coeff i j) := by ring
    rw [this]
    exact Subring.mul_mem _ h2 h1
  refine ⟨g, QuadForm.ofUpper fun i j => (hmem i j).choose, ?_⟩
  apply QuadForm.ext_upper
  intro i j hij
  have e : (formF (QuadForm.ofUpper fun i j => (hmem i j).choose)).coeff i j =
      algebraMap (𝓞 F) F ((hmem i j).choose) := by
    simp [formF, QuadForm.map, QuadForm.ofUpper, hij]
  rw [e]
  exact (hmem i j).choose_spec

/-! ### Totally positive signature -/

/-- The totally positive definite signature vector: $(n, 0)$ at every real place. -/
def totPosSig (F : Type*) [Field F] [NumberField F] (n : ℕ) : SignatureVector F n := fun _ => ⟨(n, 0), rfl⟩

theorem algebraMap_completion_real' {w : InfinitePlace F} (hw : w.IsReal) (y : F) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion y) =
      InfinitePlace.embedding_of_isReal hw y := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.algebraMap_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

theorem evalIn_algebraMap_F (K : Type*) [CommRing K] [Algebra F K] (Q : QuadForm F n) (x : Fin n → F) :
    Q.evalIn K (fun i => algebraMap F K (x i)) = algebraMap F K (Q.eval x) := by
  simp only [QuadForm.evalIn, map_sum, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- A form of the totally positive signature $(n,0)$ at every real place of a totally real field is totally positive
definite. -/
theorem isTotallyPosDef_of_hasSignature [IsTotallyReal F] {Q : QuadForm F n} (h : HasSignature Q (totPosSig F n)) :
    IsTotallyPosDef Q := by
  intro x hx σ
  set φ : F →+* ℂ := σ.toRingHom with hφ
  have hwr : (InfinitePlace.mk φ).IsReal := IsTotallyReal.isReal _
  set w := InfinitePlace.mk φ with hw
  have hφr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.mp hwr
  have hemb : InfinitePlace.embedding w = φ := InfinitePlace.embedding_mk_eq_of_isReal hφr
  have hpos : 0 < InfinitePlace.embedding_of_isReal hwr (Q.eval x) := by
    obtain ⟨P, hP, hPe⟩ := (isometricIn_map_iff Q _).mp (h ⟨w, hwr⟩)
    set ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hwr
    set z : Fin n → w.Completion := fun i => algebraMap F w.Completion (x i)
    have hz : z ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := congrFun h0 i
      exact (map_eq_zero_iff _ (algebraMap F w.Completion).injective).mp this
    set y := P⁻¹ *ᵥ z with hy
    have hy0 : y ≠ 0 := by
      intro h0
      apply hz
      have : P *ᵥ y = z := by
        rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
      rw [← this, h0, Matrix.mulVec_zero]
    have h1 : Q.evalIn w.Completion z = algebraMap F w.Completion (Q.eval x) :=
      evalIn_algebraMap_F w.Completion Q x
    have h2 := hPe y
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec] at h2
    rw [h1] at h2
    have h3 := congrArg ψ h2
    rw [algebraMap_completion_real' hwr] at h3
    rw [h3]
    have h4 : (QuadForm.diag (sigVec F ((totPosSig F n) ⟨w, hwr⟩))).evalIn w.Completion y =
        ∑ i, y i ^ 2 := by
      rw [QuadForm.evalIn_diag]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : sigVec F ((totPosSig F n) ⟨w, hwr⟩) i = 1 := by
        simp [sigVec, totPosSig]
      rw [this, map_one, one_mul]
    rw [h4, map_sum]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rw [map_pow]; exact sq_nonneg _
    · rw [map_pow]
      have : ψ (y i) ≠ 0 := by simpa using hi
      positivity
  have := InfinitePlace.embedding_of_isReal_apply hwr (Q.eval x)
  rw [hemb] at this
  have h5 : (σ (Q.eval x) : ℂ) = ((InfinitePlace.embedding_of_isReal hwr (Q.eval x) : ℝ) : ℂ) := by
    rw [this]; rfl
  rw [h5]
  exact_mod_cast hpos

end

end QuadFormsKB.Hanke2011Structure
