import QuadFormsKB.Weil.Genus.Global
import QuadFormsKB.Weil.GlobalSchwartz
import QuadFormsKB.Weil.Genus.HaarGL

/-!
# $\omega(w)$ on genus-$g$ data with an arbitrary Schwartz archimedean part

`thetaDistG_gWG` (`Weil/Genus/Global.lean`) needs fully factorizable data. Here:

* `opWg_flat`: for **every** function $\Phi$ on $V^g = M_{n\times g}(K)$ ($K$ a local field with a model `IsModel`),
  the genus-$g$ operator $\omega(w)$ is the genus-one $\omega(w)$ of $V^g \cong \langle a_i\rangle_{(i,j)}$ (dimension
  $2mg$) after flattening, $\omega_g(w)\Phi = \omega(w)(\Phi\circ\flat^{-1})\circ\flat$; the flattening
  $M_{n\times g}(K) \simeq K^{ng}$ carries the product measure to the product measure (`measurePreserving_flatPt_symm`).
* `flatD_gWG_all`: hence $\flat(\omega(w)\Phi) = \omega(w)(\flat\Phi)$ for every global datum $\Phi$.
* **`thetaDistG_gWG_schwartz`**: $\Theta(\omega(w)\Phi) = \Theta(\Phi)$ for every genus-$g$ datum whose flattening has an
  arbitrary Schwartz archimedean part and coordinate-pure finite parts (`GDatumG.IsSchwartzInfG`); this is
  `thetaDist_gW_schwartz` (`Weil/GlobalSchwartz.lean`) in dimension $2mg$; `thetaDistG_gWG_schwartzAdm`: the same for
  every admissible datum with a Schwartz archimedean part and finite components in $S(V_v^g)$ (`IsSchwartzAdmG`).
* **`thetaDistG_actWord`**: $\Theta(\omega(s_0)\cdots\omega(s_{k-1})\Phi) = \Theta(\Phi)$ for every word in the generators
  $n(B)$, $m(A)$, $w$ of $\mathrm{Sp}_{2g}(F)$ (`SpGen`, `actWord`) and every such datum. The class is stable under the
  generators: admissibility (`GDatumG.Adm.gNG`, `.gMG`, `.gWG`), Schwartz at $\infty$ (`IsSchwartzFlat.opNg`: a
  chirp of temperate growth, `hasTemperateGrowth_psiInf_bilin`; `.opMg`: a linear change of variables; `.opWg`: the
  Fourier transform, `exists_schwartz_opWf`), and $S(V_v^g)$ at the finite places (`opNg_mem_Sg_nonarch`,
  `opMg_mem_Sg_nonarch`, `opWg_mem`).
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Matrix
open QuadFormsKB.Analysis
open scoped MatrixGroups Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep.Genus

open WeilRep WeilRep.LocalData

variable {m g : ℕ}

/-- Currying carries $\mu^{\otimes(\iota\times\kappa)}$ to $(\mu^{\otimes\kappa})^{\otimes\iota}$. -/
lemma map_curry_symm_pi {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map (MeasurableEquiv.curry ι κ X).symm =
      Measure.pi fun _ : ι × κ => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
  have h : (MeasurableEquiv.curry ι κ X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext x
    simp [MeasurableEquiv.curry, Equiv.curry]
  rw [h, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

lemma measurePreserving_curry_pi {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ X) (Measure.pi fun _ : ι × κ => μ)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) where
  measurable := (MeasurableEquiv.curry ι κ X).measurable
  map_eq := by rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, map_curry_symm_pi]

/-- The inverse flattening $K^{ng} \simeq M_{n\times g}(K)$ as a measurable equivalence. -/
def flatME (K : Type*) [MeasurableSpace K] : (Fin (2 * (m * g)) → K) ≃ᵐ PtG m g K :=
  (MeasurableEquiv.piCongrLeft (fun _ => K) (eG m g)).trans (MeasurableEquiv.curry _ _ K)

lemma flatME_apply {K : Type*} [MeasurableSpace K] (x : Fin (2 * (m * g)) → K) :
    flatME (m := m) (g := g) K x = flatPt.symm x := by
  ext i j
  show Function.curry (MeasurableEquiv.piCongrLeft (fun _ => K) (eG m g) x) i j = _
  simp [Function.curry, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

lemma measurePreserving_flatPt_symm {K : Type*} [CommRing K] [MeasurableSpace K] (D : LocalData K) [SigmaFinite D.μ] :
    MeasurePreserving (flatME (m := m) (g := g) K) (D.muN (2 * (m * g))) (muG D m g) :=
  (measurePreserving_piCongrLeft (fun _ => D.μ) (eG m g)).trans (measurePreserving_curry_pi D.μ)

lemma sum_flat {M : Type*} [AddCommMonoid M] (h : Fin (2 * m) → Fin g → M) :
    ∑ p : Fin (2 * (m * g)), h (eG m g p).1 (eG m g p).2 = ∑ i, ∑ j, h i j := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (eG m g) _ _ fun p => rfl

/-- **The genus-$g$ $\omega(w)$ is the flattened genus-one $\omega(w)$, on every function.** -/
theorem opWg_flat {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} (hD : D.IsModel)
    [SigmaFinite D.μ] (a : Fin (2 * m) → Kˣ) (Φ : PtG m g K → ℂ) (y : Fin (2 * (m * g)) → K) :
    opWg D a Φ (flatPt.symm y) = D.opWf (aFlat (g := g) a) (Φ ∘ flatPt.symm) y := by
  have hc : D.cB (aFlat (g := g) a) = D.cB a ^ g := by
    simp only [cB, aFlat]
    rw [prod_flat (m := m) (g := g) (fun i (_ : Fin g) => (Real.sqrt (D.md (2 * (a i : K))) : ℂ)),
      ← Finset.prod_pow]
    simp
  have hB : ∀ x, BX a (flatPt.symm x) (flatPt.symm y) = Bform (aFlat (g := g) a) x y := by
    intro x
    simp only [BX, Bform, aFlat, flatPt_symm_apply]
    rw [← sum_flat (m := m) (g := g) (fun i j => 2 * (a i : K) * x ((eG m g).symm (i, j)) *
      y ((eG m g).symm (i, j)))]
    simp
  have hI := (measurePreserving_flatPt_symm (m := m) (g := g) D).integral_comp'
    (fun X => Φ X * (D.ψ (BX a X (flatPt.symm y)) : ℂ))
  rw [opWg, opWf, gammaV_aFlat hD, hc, ← hI]
  congr 1
  simp only [flatME_apply, hB, Function.comp_apply]

variable {F : Type} [Field F] [NumberField F] (a : Fin (2 * m) → Fˣ)

/-- **$\flat(\omega(w)\Phi) = \omega(w)(\flat\Phi)$ for every global datum** of genus $g$. -/
lemma flatD_gWG_all (Φ : GDatumG F m g) : flatD (gWG a Φ) = gW (aFlat a) (flatD Φ) := by
  show GDatum.mk _ _ = GDatum.mk _ _
  congr 1
  · funext x
    simp only [flatD, gWG, Function.comp_apply]
    rw [opWg_flat isModel_inf]
    rfl
  · funext v x
    have := (isOps_V v).sigmaFinite
    simp only [flatD, gWG, Function.comp_apply]
    rw [opWg_flat (isModel_V v)]
    rfl

/-- **Genus-$g$ data with a Schwartz archimedean part**: the flattened datum on $F^{2mg}$ has an arbitrary Schwartz
archimedean component and coordinate-pure finite components, standard at almost all $v$ (`GDatum.IsSchwartzInf`). -/
def GDatumG.IsSchwartzInfG (Φ : GDatumG F m g) : Prop := (flatD Φ).IsSchwartzInf

/-- **$\Theta$ is invariant under $\omega(w)$ on genus-$g$ data with an arbitrary Schwartz archimedean part**
(`IsSchwartzInfG`): flatten to $V^g \cong \langle a_i\rangle_{(i,j)}$ (`flatD_gWG_all`) and apply
`thetaDist_gW_schwartz` in dimension $2mg$. -/
@[kb "weil1964" "§29–§30 (Poisson summation formula, $X = V^g$) [unverified]"]
theorem thetaDistG_gWG_schwartz {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzInfG) :
    thetaDistG (gWG a Φ) = thetaDistG Φ := by
  rw [thetaDistG_eq_flat, thetaDistG_eq_flat, flatD_gWG_all a Φ]
  exact thetaDist_gW_schwartz (aFlat a) hΦ

/-- Flattening carries $S(V_v^g)$ into $S(V_v^{\oplus g})$: pure tensors in the matrix entries are pure tensors in the
$2mg$ coordinates. -/
lemma comp_flatPt_mem_Sn {K : Type*} [CommRing K] [MeasurableSpace K] {D : LocalData K} {Ψ : PtG m g K → ℂ}
    (hΨ : Ψ ∈ Sg D m g) : Ψ ∘ flatPt.symm ∈ D.Sn (2 * (m * g)) := by
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have : ptG f ∘ flatPt.symm = ptensor (fun p => f (eG m g p).1 (eG m g p).2) := by
      funext y
      rw [Function.comp_apply, ptG_flat, Equiv.apply_symm_apply]
    rw [this]
    exact LocalData.ptensor_mem_Sn fun p => hf _ _
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

/-- **Admissible genus-$g$ data with a Schwartz archimedean part** (`IsSchwartzAdmG`): $\Phi_\infty$ an arbitrary
Schwartz function on $M_{n\times g}(F_\infty) \cong F_\infty^{2mg}$, every $\Phi_v \in S(V_v^g)$ (`Sg`), and
$\Phi_v = \mathbf 1_{\mathcal O_v^{n\times g}}$ for almost all $v$ (`GDatumG.Adm`). -/
def GDatumG.IsSchwartzAdmG (Φ : GDatumG F m g) : Prop :=
  (∃ G : SchwartzMap (Fin (2 * (m * g)) → mixedSpace F) ℂ,
      Φ.inf ∘ flatPt.symm = (G : (Fin (2 * (m * g)) → mixedSpace F) → ℂ)) ∧
    (∀ v, Φ.fin v ∈ Sg (localDataV v) m g) ∧ Φ.Adm

lemma GDatumG.IsSchwartzAdmG.flat {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) : (flatD Φ).IsSchwartzAdm := by
  obtain ⟨hG, hS, T, hT⟩ := hΦ
  refine ⟨hG, fun v => comp_flatPt_mem_Sn (hS v), T, fun v hv => ?_⟩
  show Φ.fin v ∘ flatPt.symm = oneV v (2 * (m * g))
  rw [hT v hv]
  funext y
  rw [Function.comp_apply, oneVG, ptG_flat, Equiv.apply_symm_apply]
  rfl

/-- **$\Theta$ is invariant under $\omega(w)$ on admissible genus-$g$ data with an arbitrary Schwartz archimedean part
and arbitrary finite components in $S(V_v^g)$** (`IsSchwartzAdmG`): `thetaDist_gW_schwartzAdm` for the flattened
quadratic space $V^g \cong \langle a_i\rangle_{(i,j)}$ of dimension $2mg$. -/
@[kb "weil1964" "§29–§30 (Poisson summation formula, $X = V^g$) [unverified]"]
theorem thetaDistG_gWG_schwartzAdm {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) :
    thetaDistG (gWG a Φ) = thetaDistG Φ := by
  rw [thetaDistG_eq_flat, thetaDistG_eq_flat, flatD_gWG_all a Φ]
  exact thetaDist_gW_schwartzAdm (aFlat a) hΦ.flat

/-! ### Admissibility under the genus-$g$ generators -/

lemma oneVG_eq_ite (v : HeightOneSpectrum (𝓞 F)) (X : PtG m g (v.adicCompletion F)) :
    oneVG v m g X = if ∀ i j, Valued.v (X i j) ≤ 1 then 1 else 0 := by
  unfold oneVG ptG
  split_ifs with h
  · refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    show ballIndV v 0 0 (X i j) = 1
    rw [ballIndV, Set.indicator_of_mem]
    simpa using h i j
  · push Not at h
    obtain ⟨i, j, hij⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) ?_)
    show ballIndV v 0 0 (X i j) = 0
    rw [ballIndV, Set.indicator_of_notMem]
    simpa using hij

lemma oneVG_comp_flat (v : HeightOneSpectrum (𝓞 F)) :
    oneVG v m g ∘ flatPt.symm = oneV v (2 * (m * g)) := by
  funext y
  rw [Function.comp_apply, oneVG, ptG_flat, Equiv.apply_symm_apply]
  rfl

lemma GDatumG.Adm.flat {Φ : GDatumG F m g} (hΦ : Φ.Adm) : (flatD Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  exact ⟨T, fun v hv => by show Φ.fin v ∘ flatPt.symm = _; rw [hT v hv, oneVG_comp_flat]⟩

lemma GDatumG.adm_of_flat {Φ : GDatumG F m g} (hΦ : (flatD Φ).Adm) : Φ.Adm := by
  obtain ⟨T, hT⟩ := hΦ
  refine ⟨T, fun v hv => ?_⟩
  have h := hT v hv
  rw [← oneVG_comp_flat] at h
  funext X
  have := congrFun h (flatPt X)
  simpa [flatD] using this

lemma GDatumG.Adm.gWG {Φ : GDatumG F m g} (hΦ : Φ.Adm) : (gWG a Φ).Adm :=
  GDatumG.adm_of_flat (by rw [flatD_gWG_all]; exact hΦ.flat.gW (aFlat a))

lemma entry_mul_le_one {v : HeightOneSpectrum (𝓞 F)} {p q r : ℕ}
    {M : Matrix (Fin p) (Fin q) (v.adicCompletion F)} {N : Matrix (Fin q) (Fin r) (v.adicCompletion F)} (hM : ∀ i j, Valued.v (M i j) ≤ 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1)
    (i : Fin p) (j : Fin r) : Valued.v ((M * N) i j) ≤ 1 := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i k) (hN k j)

/-- The finite places where some entry of $B$ or some $a_i$ is not integral. -/
def badNG (B : Matrix (Fin g) (Fin g) F) : Set (HeightOneSpectrum (𝓞 F)) :=
  (⋃ j, ⋃ k, (HeightOneSpectrum.Support (𝓞 F) (B j k) : Set _)) ∪
    ⋃ i, (HeightOneSpectrum.Support (𝓞 F) (a i : F) : Set _)

lemma badNG_finite (B : Matrix (Fin g) (Fin g) F) : (badNG a B).Finite :=
  (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => HeightOneSpectrum.Support.finite (𝓞 F) _).union
    (Set.finite_iUnion fun _ => HeightOneSpectrum.Support.finite (𝓞 F) _)

lemma GDatumG.Adm.gNG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (B : Matrix (Fin g) (Fin g) F) : (gNG a B Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  refine ⟨T ∪ (badNG_finite a B).toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or] at hv
  have hB : ∀ j k, Valued.v ((B.map (algebraMap F (v.adicCompletion F))) j k) ≤ 1 := fun j k =>
    valued_le_one_of_not_mem_support fun h => hv.2 (Or.inl (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨k, h⟩⟩))
  have ha : ∀ i, Valued.v ((aV a v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 := fun i =>
    valued_le_one_of_not_mem_support fun h => hv.2 (Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩))
  show opNg (localDataV v) (aV a v) (B.map (algebraMap F _)) (Φ.fin v) = oneVG v m g
  rw [hT v hv.1]
  funext X
  rw [opNg, oneVG_eq_ite]
  split_ifs with hX
  · rw [mul_one, show ((localDataV v).ψ _ : ℂ) = (psiV v _ : ℂ) from rfl, psiV_eq_one_of_le_one v, Circle.coe_one]
    rw [Matrix.trace]
    refine Valuation.map_sum_le _ fun k _ => ?_
    refine entry_mul_le_one hB (fun j k => ?_) k k
    refine entry_mul_le_one (fun j l => ?_) hX j k
    refine entry_mul_le_one (fun j l => by simpa using hX l j) (fun l l' => ?_) j l
    by_cases h : l = l'
    · subst h; simpa using ha l
    · simp [Matrix.diagonal_apply_ne _ h]
  · rw [mul_zero]

/-- The finite places where $A$ or $A^{-1}$ has a non-integral entry, $\det A$ is not a unit, or the Hilbert symbol
$(\det A, \operatorname{disc} V)_v$ is $-1$. -/
def badMG (A : GL (Fin g) F) : Set (HeightOneSpectrum (𝓞 F)) :=
  (HeightOneSpectrum.Support (𝓞 F) (Matrix.GeneralLinearGroup.det A : F) : Set _) ∪
    (HeightOneSpectrum.Support (𝓞 F) (Matrix.GeneralLinearGroup.det A : F)⁻¹ : Set _) ∪
    {v | (NFPlace.finite v).hilbert (Matrix.GeneralLinearGroup.det A : F) ((discV a : Fˣ) : F) = -1} ∪
    (⋃ j, ⋃ k, (HeightOneSpectrum.Support (𝓞 F) ((A : Matrix (Fin g) (Fin g) F) j k) : Set _)) ∪
    (⋃ j, ⋃ k, (HeightOneSpectrum.Support (𝓞 F) (((A⁻¹ : GL (Fin g) F) : Matrix (Fin g) (Fin g) F) j k) : Set _))

lemma badMG_finite (A : GL (Fin g) F) : (badMG a A).Finite := by
  refine ((((HeightOneSpectrum.Support.finite (𝓞 F) _).union (HeightOneSpectrum.Support.finite (𝓞 F) _)).union
    ?_).union (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => HeightOneSpectrum.Support.finite (𝓞 F) _)).union
    (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => HeightOneSpectrum.Support.finite (𝓞 F) _)
  exact HN.finite_hilbert_finite_eq_neg_one _ _ (Matrix.GeneralLinearGroup.det A).ne_zero (discV a).ne_zero

lemma GDatumG.Adm.gMG {Φ : GDatumG F m g} (hΦ : Φ.Adm) (A : GL (Fin g) F) : (gMG a A Φ).Adm := by
  obtain ⟨T, hT⟩ := hΦ
  refine ⟨T ∪ (badMG_finite a A).toFinset, fun v hv => ?_⟩
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, not_or, badMG, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_iUnion, not_exists] at hv
  obtain ⟨hvT, ⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩ := hv
  set t : Fˣ := Matrix.GeneralLinearGroup.det A
  set ι := algebraMap F (v.adicCompletion F)
  set A' : GL (Fin g) (v.adicCompletion F) := Matrix.GeneralLinearGroup.map ι A
  have hval := valued_eq_one_of_not_mem t.ne_zero hv1 hv2
  have hdet : (A' : Matrix (Fin g) (Fin g) (v.adicCompletion F)).det = ι t := by
    simp [A', t, RingHom.map_det]
  have hχ : (localDataV v).chiV (aV a v) (ι t) = 1 := by
    simp only [LocalData.chiV, LocalData.hC, discV_aV]
    rcases HN.hilbertSymbol_eq_one_or (v.adicCompletion F) (ι t) (ι ((discV a : Fˣ) : F)) with h | h
    · rw [show (localDataV v).hilb = hilbertSymbol (v.adicCompletion F) from rfl, h]; simp
    · exact absurd h hv3
  have hmd : (localDataV v).md (ι t) = 1 := by
    show Analysis.Weil.modK _ _ = 1
    rw [modK_eq_norm v ((map_ne_zero _).mpr t.ne_zero), norm_eq_one_of_valued hval]
  have hA : ∀ j k, Valued.v ((A' : Matrix (Fin g) (Fin g) (v.adicCompletion F)) j k) ≤ 1 := fun j k =>
    valued_le_one_of_not_mem_support (hv4 j k)
  have hA' : ∀ j k, Valued.v (((A'⁻¹ : GL (Fin g) (v.adicCompletion F)) :
      Matrix (Fin g) (Fin g) (v.adicCompletion F)) j k) ≤ 1 := fun j k => by
    rw [show A'⁻¹ = Matrix.GeneralLinearGroup.map ι A⁻¹ from (map_inv _ A).symm]
    exact valued_le_one_of_not_mem_support (hv5 j k)
  show opMg (localDataV v) (aV a v) A' (Φ.fin v) = oneVG v m g
  rw [hT v hvT]
  funext X
  rw [opMg, hdet, hχ, hmd, Complex.ofReal_one, one_pow, one_mul, one_mul, oneVG_eq_ite, oneVG_eq_ite]
  congr 1
  refine propext ⟨fun h i j => ?_, fun h i j => entry_mul_le_one h hA i j⟩
  have hX : X = (X * (A' : Matrix (Fin g) (Fin g) (v.adicCompletion F))) *
      ((A'⁻¹ : GL (Fin g) (v.adicCompletion F)) : Matrix (Fin g) (Fin g) (v.adicCompletion F)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [hX]
  exact entry_mul_le_one h hA' i j

/-! ### The archimedean operators preserve Schwartz functions on $M_{n\times g}(F_\infty) \cong F_\infty^{2mg}$ -/

/-- **$x \mapsto \psi_\infty(q(x, x))$ has temperate growth** for a continuous bilinear $q : W\times W \to F_\infty$. -/
lemma hasTemperateGrowth_psiInf_bilin {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (q : W →L[ℝ] W →L[ℝ] mixedSpace F) :
    Function.HasTemperateGrowth fun x : W => (psiInf (q x x) : ℂ) := by
  have hB : Function.HasTemperateGrowth fun x : W => q x x :=
    q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id Function.HasTemperateGrowth.id
  set L : mixedSpace F →L[ℝ] ℝ := (2 * Real.pi) • LinearMap.toContinuousLinearMap (traceInfL (F := F))
  have h := Complex.hasTemperateGrowth_exp_mul_I.comp (L.hasTemperateGrowth.comp hB)
  convert h using 1
  ext x
  simp only [Function.comp_apply, psiInf, Real.fourierChar_apply, L]
  congr 1

/-- The bilinear form $(x, y) \mapsto \operatorname{tr}(B\,{}^tX\,\mathrm{diag}(a)\,Y)$, $X = \flat^{-1}x$, $Y = \flat^{-1}y$. -/
def bilNG (B : Matrix (Fin g) (Fin g) (mixedSpace F)) (a' : Fin (2 * m) → (mixedSpace F)ˣ) :
    (Fin (2 * (m * g)) → mixedSpace F) →ₗ[ℝ] (Fin (2 * (m * g)) → mixedSpace F) →ₗ[ℝ] mixedSpace F :=
  LinearMap.mk₂ ℝ (fun x y => trace (B * ((flatPt.symm x)ᵀ * diagonal (fun i => (a' i : mixedSpace F)) *
      flatPt.symm y)))
    (fun x x' y => by
      rw [show flatPt.symm (x + x') = flatPt.symm x + flatPt.symm x' from rfl, transpose_add, Matrix.add_mul,
        Matrix.add_mul, Matrix.mul_add, trace_add])
    (fun c x y => by
      rw [show flatPt.symm (c • x) = c • flatPt.symm x from rfl, transpose_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_smul, trace_smul])
    (fun x y y' => by
      rw [show flatPt.symm (y + y') = flatPt.symm y + flatPt.symm y' from rfl, Matrix.mul_add, Matrix.mul_add,
        trace_add])
    (fun c x y => by
      rw [show flatPt.symm (c • y) = c • flatPt.symm y from rfl, Matrix.mul_smul, Matrix.mul_smul, trace_smul])

/-- `bilNG` as a continuous bilinear map. -/
def bilNGL (B : Matrix (Fin g) (Fin g) (mixedSpace F)) (a' : Fin (2 * m) → (mixedSpace F)ˣ) :
    (Fin (2 * (m * g)) → mixedSpace F) →L[ℝ] (Fin (2 * (m * g)) → mixedSpace F) →L[ℝ] mixedSpace F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ bilNG B a')

lemma bilNGL_apply (B : Matrix (Fin g) (Fin g) (mixedSpace F)) (a' : Fin (2 * m) → (mixedSpace F)ˣ)
    (x y : Fin (2 * (m * g)) → mixedSpace F) :
    bilNGL B a' x y = trace (B * ((flatPt.symm x)ᵀ * diagonal (fun i => (a' i : mixedSpace F)) *
      flatPt.symm y)) :=
  rfl

variable (F) in
/-- The flattened archimedean component is a Schwartz function. -/
def IsSchwartzFlat (Ψ : PtG m g (mixedSpace F) → ℂ) : Prop :=
  ∃ G : SchwartzMap (Fin (2 * (m * g)) → mixedSpace F) ℂ, Ψ ∘ flatPt.symm = (G : (Fin (2 * (m * g)) → mixedSpace F) → ℂ)

lemma IsSchwartzFlat.opNg {Ψ : PtG m g (mixedSpace F) → ℂ} (hΨ : IsSchwartzFlat F Ψ)
    (B : Matrix (Fin g) (Fin g) (mixedSpace F)) (a' : Fin (2 * m) → (mixedSpace F)ˣ) :
    IsSchwartzFlat F (opNg localDataInf a' B Ψ) := by
  obtain ⟨G, hG⟩ := hΨ
  have ht := hasTemperateGrowth_psiInf_bilin (bilNGL B a')
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun y => (psiInf (bilNGL B a' y y) : ℂ)) G, ?_⟩
  funext y
  rw [SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul, ← hG, Function.comp_apply, Function.comp_apply,
    Genus.opNg, bilNGL_apply]
  rfl

/-- Right multiplication by $A \in \mathrm{GL}_g(F_\infty)$ in the flattened coordinates. -/
def rightMulL (A : GL (Fin g) (mixedSpace F)) :
    (Fin (2 * (m * g)) → mixedSpace F) ≃L[ℝ] (Fin (2 * (m * g)) → mixedSpace F) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => flatPt (flatPt.symm y * (A : Matrix (Fin g) (Fin g) (mixedSpace F)))
      invFun := fun y => flatPt (flatPt.symm y * ((A⁻¹ : GL (Fin g) (mixedSpace F)) :
        Matrix (Fin g) (Fin g) (mixedSpace F)))
      map_add' := fun x y => by
        rw [show flatPt.symm (x + y) = flatPt.symm x + flatPt.symm y from rfl, Matrix.add_mul]
        rfl
      map_smul' := fun c x => by
        rw [show flatPt.symm (c • x) = c • flatPt.symm x from rfl, Matrix.smul_mul]
        rfl
      left_inv := fun y => by
        simp only [Equiv.symm_apply_apply]
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one,
          Equiv.apply_symm_apply]
      right_inv := fun y => by
        simp only [Equiv.symm_apply_apply]
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one,
          Equiv.apply_symm_apply] }

lemma IsSchwartzFlat.opMg {Ψ : PtG m g (mixedSpace F) → ℂ} (hΨ : IsSchwartzFlat F Ψ)
    (A : GL (Fin g) (mixedSpace F)) (a' : Fin (2 * m) → (mixedSpace F)ˣ) :
    IsSchwartzFlat F (opMg localDataInf a' A Ψ) := by
  obtain ⟨G, hG⟩ := hΨ
  refine ⟨((localDataInf (F := F)).chiV a' (A : Matrix (Fin g) (Fin g) (mixedSpace F)).det *
      ((localDataInf (F := F)).md (A : Matrix (Fin g) (Fin g) (mixedSpace F)).det : ℂ) ^ m) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulL A) G, ?_⟩
  funext y
  simp only [_root_.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smul_eq_mul, ← hG]
  rw [Genus.opMg]
  congr 1
  show _ = Ψ (flatPt.symm (flatPt (flatPt.symm y * (A : Matrix (Fin g) (Fin g) (mixedSpace F)))))
  rw [Equiv.symm_apply_apply]

lemma IsSchwartzFlat.opWg {Ψ : PtG m g (mixedSpace F) → ℂ} (hΨ : IsSchwartzFlat F Ψ) :
    IsSchwartzFlat F (opWg localDataInf (aInf a) Ψ) := by
  obtain ⟨G, hG⟩ := hΨ
  obtain ⟨H, hH⟩ := exists_schwartz_opWf (aFlat (g := g) a) G
  refine ⟨H, ?_⟩
  funext y
  rw [Function.comp_apply, opWg_flat isModel_inf, hH, hG]
  rfl

/-! ### Invariance under every word in the generators -/

lemma GDatumG.IsSchwartzAdmG.gNG {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) (B : Matrix (Fin g) (Fin g) F) :
    (gNG a B Φ).IsSchwartzAdmG := by
  obtain ⟨hG, hS, hadm⟩ := hΦ
  refine ⟨IsSchwartzFlat.opNg hG _ _, fun v => ?_, hadm.gNG a B⟩
  exact opNg_mem_Sg_nonarch rfl (isStdChar_psiV v) _ (hS v)

lemma GDatumG.IsSchwartzAdmG.gMG {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) (A : GL (Fin g) F) :
    (gMG a A Φ).IsSchwartzAdmG := by
  obtain ⟨hG, hS, hadm⟩ := hΦ
  refine ⟨IsSchwartzFlat.opMg hG _ _, fun v => ?_, hadm.gMG a A⟩
  exact opMg_mem_Sg_nonarch rfl _ (hS v)

lemma GDatumG.IsSchwartzAdmG.gWG {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) : (gWG a Φ).IsSchwartzAdmG := by
  obtain ⟨hG, hS, hadm⟩ := hΦ
  refine ⟨IsSchwartzFlat.opWg a hG, fun v => ?_, hadm.gWG a⟩
  exact opWg_mem (isOps_V v) (hS v)

/-- **The generators of $\mathrm{Sp}_{2g}(K)$**: $n(B)$ ($B \in M_g(K)$), $m(A)$ ($A \in \mathrm{GL}_g(K)$) and $w$. -/
inductive SpGen (K : Type*) [CommRing K] (g : ℕ)
  | n (B : Matrix (Fin g) (Fin g) K)
  | m (A : GL (Fin g) K)
  | w

/-- The action of a generator on global data of genus $g$. -/
def SpGen.act : SpGen F g → GDatumG F m g → GDatumG F m g
  | .n B => gNG a B
  | .m A => gMG a A
  | .w => gWG a

/-- The action of a word $s_0 s_1 \cdots s_{k-1}$ in the generators: $\omega(s_0)\cdots\omega(s_{k-1})\Phi$. -/
def actWord : List (SpGen F g) → GDatumG F m g → GDatumG F m g
  | [] => id
  | s :: L => SpGen.act a s ∘ actWord L

lemma GDatumG.IsSchwartzAdmG.actWord {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) (L : List (SpGen F g)) :
    (actWord a L Φ).IsSchwartzAdmG := by
  induction L with
  | nil => exact hΦ
  | cons s L ih =>
    cases s with
    | n B => exact ih.gNG a B
    | m A => exact ih.gMG a A
    | w => exact ih.gWG a

/-- **The genus-$g$ theta distribution is invariant under every word in $n(B)$, $m(A)$, $w$** on admissible data with
an arbitrary Schwartz archimedean component on $M_{n\times g}(F_\infty)$ and arbitrary finite components in
$S(V_v^g)$ (`IsSchwartzAdmG`): for every word $s_0\cdots s_{k-1}$,
$\Theta(\omega(s_0)\cdots\omega(s_{k-1})\Phi) = \Theta(\Phi)$. The class is stable under the three generators
(`GDatumG.IsSchwartzAdmG.gNG`, `.gMG`, `.gWG`); the invariances are `thetaDistG_gNG`, `thetaDistG_gMG` and
`thetaDistG_gWG_schwartzAdm`. These words exhaust $\mathrm{Sp}_{2g}(F)$ (the generators generate it); a global
representation of $\mathrm{Sp}_{2g}(F)$ on such data is not constructed here. -/
@[kb "weil1964" "§29–§30, Thm. 4 (the distribution is invariant under $\\mathrm{Sp}(X_k)$, $X = V^g$) [unverified]"]
theorem thetaDistG_actWord {Φ : GDatumG F m g} (hΦ : Φ.IsSchwartzAdmG) (L : List (SpGen F g)) :
    thetaDistG (actWord a L Φ) = thetaDistG Φ := by
  induction L with
  | nil => rfl
  | cons s L ih =>
    have h := hΦ.actWord a L
    cases s with
    | n B => exact (thetaDistG_gNG a h.2.2 B).trans ih
    | m A => exact (thetaDistG_gMG a h.2.2 A).trans ih
    | w => exact (thetaDistG_gWG_schwartzAdm a h).trans ih

end QuadFormsKB.WeilRep.Genus



