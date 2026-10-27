import QuadFormsKB.Tamagawa.Measure.Weil.SimilarLocal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.Measure.ProductSO
import QuadFormsKB.Tamagawa.LocalOrbitalGlobal

/-!
# Similar forms: the finite adelic groups and the finite Tamagawa measure

**Layer:** a number field $F$; $Q_0$ nondegenerate over $\mathcal O_F$ in $n$ variables, $G \in M_n(\mathcal O_F)$,
$\det G \ne 0$, $c \ne 0$, $Q_1 = c\,(Q_0\circ G)$ (`simForm`), $\delta = c^{n(n+1)/2}\det(G)^{n+1}$ (`simJac`).

**Proves**
* `simConjV_preimage_stdStab_of_good`: at a place with $\delta \notin v$, conjugation maps $O(\mathfrak o_v^n)$ for $Q_0$
  onto $O(\mathfrak o_v^n)$ for $Q_1$;
* `simConjFin`: $SO(Q_0)(\mathbb A_f) \cong SO(Q_1)(\mathbb A_f)$, $g \mapsto G^{-1}gG$ placewise;
* `map_muFin_simConjFin`: $(g\mapsto G^{-1}gG)_*\mu_f^{Q_0} = \prod'_v\|\delta\|_v\cdot\mu_f^{Q_1}$ ($n \ne 0, 2$).

Source: Weil 1982, §2.3, Thm 2.3.1, pp. 21–22.
-/

open MeasureTheory Measure Matrix
open scoped ENNReal NNReal RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.LocalDensity QuadFormsKB.QuadForm
  QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} {c : 𝓞 F}
  {G : Matrix (Fin n) (Fin n) (𝓞 F)}

theorem sim_isUnit_det_of_notMem (v : HeightOneSpectrum (𝓞 F)) (h : simJac c G ∉ v.asIdeal) :
    IsUnit (G.map (NF.ι v)).det := by
  have hG : G.det ∉ v.asIdeal := fun hm =>
    h (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm _ (Nat.succ_pos n)))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, NF.valued_ι,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact hG

/-- at every $v$ with $\delta \notin v$, conjugation maps $O(\mathfrak o_v^n)$ for $Q_0$ onto $O(\mathfrak o_v^n)$ for $Q_1$ -/
theorem simConjV_preimage_stdStab_of_good (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (h : simJac c G ∉ v.asIdeal) :
    simConjV (Q₀ := Q₀) v hc hG ⁻¹' ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v :
        Subgroup (orthGroup _ (v.adicCompletion F))) : Set (orthGroup _ (v.adicCompletion F))) =
      ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F))) := by
  rw [simConjV_preimage_stdStab]
  have hlat : latOf v (G.map (NF.ι v)) = std v := by
    rw [latOf_eq v _ (LatChange.det_map_ι_ne_zero v hG)]
    exact locAct_glOf_unit v _ (sim_isUnit_det_of_notMem v h) (LatChange.det_map_ι_ne_zero v hG)
  rw [hlat]
  rfl

section Fin

theorem simBad_finite (hc : c ≠ 0) (hG : G.det ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | simJac c G ∈ v.asIdeal}.Finite := by
  have h_span_nezero : Ideal.span {simJac c G} ≠ 0 := by simp [simJac_ne_zero hc hG]
  simp only [← Ideal.dvd_span_singleton]
  exact Ideal.finite_factors h_span_nezero

theorem simGood_eventually (hc : c ≠ 0) (hG : G.det ≠ 0) :
    ∀ᶠ v in Filter.cofinite, simJac c G ∉ (v : HeightOneSpectrum (𝓞 F)).asIdeal :=
  Filter.eventually_cofinite.mpr (by simpa using simBad_finite hc hG)

theorem simConjV_mapsTo_of_good (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (hv : simJac c G ∉ v.asIdeal) :
    Set.MapsTo (simConjV (Q₀ := Q₀) v hc hG)
      ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F)))
      ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F))) := by
  intro x hx
  have h := simConjV_preimage_stdStab_of_good (Q₀ := Q₀) v hc hG hv
  have hx' : x ∈ simConjV (Q₀ := Q₀) v hc hG ⁻¹' ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v :
      Subgroup (orthGroup _ (v.adicCompletion F))) : Set (orthGroup _ (v.adicCompletion F))) := by
    rw [h]; exact hx
  exact Set.mem_preimage.mp hx'

theorem simConjV_symm_mapsTo_of_good (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (hv : simJac c G ∉ v.asIdeal) :
    Set.MapsTo ((simConjV (Q₀ := Q₀) v hc hG).symm)
      ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F)))
      ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F))) := by
  intro x hx
  have h := simConjV_preimage_stdStab_of_good (Q₀ := Q₀) v hc hG hv
  have hx' : (simConjV (Q₀ := Q₀) v hc hG).symm x ∈ simConjV (Q₀ := Q₀) v hc hG ⁻¹'
      ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v :
      Subgroup (orthGroup _ (v.adicCompletion F))) : Set (orthGroup _ (v.adicCompletion F))) := by
    rw [Set.mem_preimage, ContinuousMulEquiv.apply_symm_apply]; exact hx
  rw [h] at hx'
  exact hx'

theorem simConjV_mapsTo_good (hc : c ≠ 0) (hG : G.det ≠ 0) :
    ∀ᶠ v in Filter.cofinite, Set.MapsTo (simConjV (Q₀ := Q₀) v hc hG)
      ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F)))
      ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F))) :=
  simGood_eventually hc hG |>.mono fun v hv => simConjV_mapsTo_of_good v hc hG hv

theorem simConjV_symm_mapsTo_good (hc : c ≠ 0) (hG : G.det ≠ 0) :
    ∀ᶠ v in Filter.cofinite, Set.MapsTo ((simConjV (Q₀ := Q₀) v hc hG).symm)
      ((stdStab ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F)))
      ((stdStab (Q₀.map (algebraMap (𝓞 F) F)) v : Subgroup (orthGroup _ (v.adicCompletion F))) :
        Set (orthGroup _ (v.adicCompletion F))) :=
  simGood_eventually hc hG |>.mono fun v hv => simConjV_symm_mapsTo_of_good v hc hG hv

variable (Q₀) in
/-- The placewise conjugation on the restricted product (forward) -/
def simConjOAf (hc : c ≠ 0) (hG : G.det ≠ 0) :
    OAf (Q₀.map (algebraMap (𝓞 F) F)) → OAf ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) :=
  RestrictedProduct.map (fun v => (simConjV (Q₀ := Q₀) v hc hG : _ → _)) (simConjV_mapsTo_good hc hG)

variable (Q₀) in
/-- The placewise conjugation on the restricted product (backward) -/
def simConjOAfSymm (hc : c ≠ 0) (hG : G.det ≠ 0) :
    OAf ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) → OAf (Q₀.map (algebraMap (𝓞 F) F)) :=
  RestrictedProduct.map (fun v => ((simConjV (Q₀ := Q₀) v hc hG).symm : _ → _)) (simConjV_symm_mapsTo_good hc hG)

theorem simConjOAf_continuous (hc : c ≠ 0) (hG : G.det ≠ 0) : Continuous (simConjOAf Q₀ hc hG) :=
  RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _ (simConjV_mapsTo_good hc hG) fun v => (simConjV v hc hG).continuous

theorem simConjOAfSymm_continuous (hc : c ≠ 0) (hG : G.det ≠ 0) : Continuous (simConjOAfSymm Q₀ hc hG) :=
  RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id _ (simConjV_symm_mapsTo_good hc hG) fun v => (simConjV v hc hG).symm.continuous

theorem simConjOAf_apply (hc : c ≠ 0) (hG : G.det ≠ 0) (g : OAf (Q₀.map (algebraMap (𝓞 F) F))) (v : HeightOneSpectrum (𝓞 F)) :
    simConjOAf Q₀ hc hG g v = simConjV v hc hG (g v) := rfl

theorem simConjOAfSymm_apply (hc : c ≠ 0) (hG : G.det ≠ 0)
    (g : OAf ((simForm Q₀ c G).map (algebraMap (𝓞 F) F))) (v : HeightOneSpectrum (𝓞 F)) :
    simConjOAfSymm Q₀ hc hG g v = (simConjV v hc hG).symm (g v) := rfl

theorem simConjOAf_mem_soAf (hc : c ≠ 0) (hG : G.det ≠ 0) (g : SOAf Q₀) :
    simConjOAf Q₀ hc hG g.1 ∈ soAf ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) := fun v =>
  simConjV_mem_soSub v hc hG ⟨g.1 v, g.2 v⟩

theorem simConjOAfSymm_mem_soAf (hc : c ≠ 0) (hG : G.det ≠ 0) (g : SOAf (simForm Q₀ c G)) :
    simConjOAfSymm Q₀ hc hG g.1 ∈ soAf (Q₀.map (algebraMap (𝓞 F) F)) := fun v =>
  simConjV_symm_mem_soSub v hc hG ⟨g.1 v, g.2 v⟩

/-- **The finite adelic conjugation** $SO(Q_0)(\mathbb A_f) \cong SO(Q_1)(\mathbb A_f)$, $g \mapsto G^{-1}gG$ placewise
(`simConjV` at every finite place; at the finitely many $v$ with $\delta \in v$ it does not preserve the standard
stabilizers, but it still maps the restricted product to the restricted product since it does at cofinitely many). -/
def simConjFin (hc : c ≠ 0) (hG : G.det ≠ 0) : SOAf Q₀ ≃ₜ* SOAf (simForm Q₀ c G) where
  toFun g := ⟨simConjOAf Q₀ hc hG g.1, simConjOAf_mem_soAf hc hG g⟩
  invFun g := ⟨simConjOAfSymm Q₀ hc hG g.1, simConjOAfSymm_mem_soAf hc hG g⟩
  left_inv g := Subtype.ext (RestrictedProduct.ext _ _ fun v => by exact (simConjV v hc hG).symm_apply_apply _)
  right_inv g := Subtype.ext (RestrictedProduct.ext _ _ fun v => by exact (simConjV v hc hG).apply_symm_apply _)
  map_mul' g h := Subtype.ext (RestrictedProduct.ext _ _ fun v => by exact map_mul (simConjV v hc hG) _ _)
  continuous_toFun := Continuous.subtype_mk ((simConjOAf_continuous hc hG).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk ((simConjOAfSymm_continuous hc hG).comp continuous_subtype_val) _

theorem simConjFin_apply (hc : c ≠ 0) (hG : G.det ≠ 0) (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    (((simConjFin hc hG g : SOAf (simForm Q₀ c G)) : OAf ((simForm Q₀ c G).map (algebraMap (𝓞 F) F))) v) =
      simConjV v hc hG (((g : SOAf Q₀) : OAf (Q₀.map (algebraMap (𝓞 F) F))) v) := rfl

end Fin

section Meas

theorem simU_eq_of_good (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (h : simJac c G ∉ v.asIdeal) :
    (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹' (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) =
      (soStabSO v Q₀ : Set (SOv v Q₀)) := by
  ext x
  exact Set.ext_iff.mp (simConjV_preimage_stdStab_of_good (Q₀ := Q₀) v hc hG h) x.1

theorem sim_evalSO_simConjFin (hc : c ≠ 0) (hG : G.det ≠ 0) (g : SOAf Q₀) (v : HeightOneSpectrum (𝓞 F)) :
    evalSO (simForm Q₀ c G) v (simConjFin hc hG g) = simConjSOV v hc hG (evalSO Q₀ v g) :=
  rfl

theorem simConjSOV_mem_iff_of_good (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (h : simJac c G ∉ v.asIdeal) (x : SOv v Q₀) :
    simConjSOV v hc hG x ∈ soStabSO v (simForm Q₀ c G) ↔ x ∈ soStabSO v Q₀ :=
  by
  have h1 := Set.ext_iff.mp (simU_eq_of_good (Q₀ := Q₀) v hc hG h) x
  rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe] at h1
  exact h1

theorem sim_mem_boxSO_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v, Set (SOv v Q₀)) (g : SOAf Q₀) :
    g ∈ boxSO Q₀ S U ↔ (∀ v ∈ S, evalSO Q₀ v g ∈ U v) ∧ ∀ v ∉ S, evalSO Q₀ v g ∈ soStabSO v Q₀ :=
  Iff.rfl

theorem simConjFin_preimage_KSO (hc : c ≠ 0) (hG : G.det ≠ 0) :
    simConjFin (Q₀ := Q₀) hc hG ⁻¹' (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) =
      boxSO Q₀ (simBad_finite hc hG).toFinset
        (fun v => simConjSOV (Q₀ := Q₀) v hc hG ⁻¹' (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) := by
  ext g
  rw [Set.mem_preimage, SetLike.mem_coe, mem_KSO_iff, sim_mem_boxSO_iff]
  simp only [Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro h
    refine ⟨fun v _ => ?_, fun v hv => ?_⟩
    · have := h v
      rw [sim_evalSO_simConjFin] at this
      exact this
    · have hv' : simJac c G ∉ v.asIdeal := by simpa using hv
      have := h v
      rw [sim_evalSO_simConjFin] at this
      exact (simConjSOV_mem_iff_of_good v hc hG hv' _).mp this
  · rintro ⟨h1, h2⟩ v
    rw [sim_evalSO_simConjFin]
    by_cases hv : v ∈ (simBad_finite hc hG).toFinset
    · exact h1 v hv
    · have hv' : simJac c G ∉ v.asIdeal := by simpa using hv
      exact (simConjSOV_mem_iff_of_good v hc hG hv' _).mpr (h2 v hv)

theorem sim_muLocSO_simU (hn : 0 < n) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0)
    (hG : G.det ≠ 0) :
    muLocSO v Q₀ 1 (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹' (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) =
      ENNReal.ofReal ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ *
        ENNReal.ofReal (NF.siegelDensity v (simForm Q₀ c G) (simForm Q₀ c G)) := by
  have h := congrArg (fun m : Measure (SOv v (simForm Q₀ c G)) => m (soStabSO v (simForm Q₀ c G) : Set _))
    (map_muLocSO_simConjSOV v hn hQ hc hG)
  have hm : Measurable (simConjSOV (Q₀ := Q₀) v hc hG) := (simConjSOV v hc hG).continuous.measurable
  rw [Measure.map_apply hm (isOpen_soStabSO v _).measurableSet, Measure.smul_apply, smul_eq_mul,
    muLocSO_soStabSO, div_one] at h
  exact h

theorem sim_alpha_eq_of_good (hn : 0 < n) (hQ : Q₀.Nondegenerate) (v : HeightOneSpectrum (𝓞 F)) (hc : c ≠ 0)
    (hG : G.det ≠ 0) (h : simJac c G ∉ v.asIdeal) :
    NF.siegelDensity v Q₀ Q₀ = NF.siegelDensity v (simForm Q₀ c G) (simForm Q₀ c G) := by
  have h1 := sim_muLocSO_simU hn hQ v hc hG
  have hn1 : ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ = 1 :=
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v _).mpr h
  rw [hn1, ENNReal.ofReal_one, one_mul] at h1
  have h2 : (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹' (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) =
      (soStabSO v Q₀ : Set (SOv v Q₀)) := simU_eq_of_good v hc hG h
  rw [h2, muLocSO_soStabSO, div_one] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (siegelDensity_self_pos' Q₀ hQ v).le
    (siegelDensity_self_pos' _ (nondegenerate_simForm hQ hc hG) v).le).mp h1

theorem sim_haarNorm_mul {G' : Type*} [Group G'] [TopologicalSpace G'] [MeasurableSpace G'] [BorelSpace G']
    [IsTopologicalGroup G'] [LocallyCompactSpace G'] (K : Subgroup G') (hc : IsCompact (K : Set G'))
    (ho : IsOpen (K : Set G')) (a b : ℝ≥0) :
    haarNorm K hc ho (a * b) = a • haarNorm K hc ho b := by
  unfold haarNorm
  exact mul_smul _ _ _

theorem map_muFin_simConjFin (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hQ : Q₀.Nondegenerate) (hc : c ≠ 0)
    (hG : G.det ≠ 0) :
    (muFin Q₀ fun _ => 1).map (simConjFin hc hG) =
      ENNReal.ofReal (∏' v : HeightOneSpectrum (𝓞 F), ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖) •
        muFin (simForm Q₀ c G) fun _ => 1 := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hQ₁ := nondegenerate_simForm hQ hc hG
  have : LocallyCompactSpace (SOAf (simForm Q₀ c G)) :=
    (isClosed_soAf _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  set S := (simBad_finite hc hG).toFinset with hS
  set e := simConjFin (Q₀ := Q₀) hc hG with he
  have hmeas : Measurable e := e.continuous.measurable
  set nδ : HeightOneSpectrum (𝓞 F) → ℝ :=
    fun v => ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 F) F (simJac c G))‖ with hnδ
  set α₀ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v Q₀ Q₀ with hα₀def
  set α₁ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => NF.siegelDensity v (simForm Q₀ c G) (simForm Q₀ c G) with hα₁def
  have hα₀ : ∀ v, 0 < α₀ v := fun v => siegelDensity_self_pos' Q₀ hQ v
  have hα₁ : ∀ v, 0 < α₁ v := fun v => siegelDensity_self_pos' _ hQ₁ v
  have hnδpos : ∀ v, 0 < nδ v := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr (coe_ne_zero_of_ne_zero (simJac_ne_zero hc hG)))
  have hnδ1 : ∀ v ∉ S, nδ v = 1 := fun v hv =>
    (NumberField.FinitePlace.norm_eq_one_iff_notMem F v _).mpr (by simpa [hS] using hv)
  have : IsMulLeftInvariant ((muFin Q₀ fun _ => 1).map e) :=
    isMulLeftInvariant_map e.toMulEquiv.toMonoidHom.toMulHom hmeas e.surjective
  have : SigmaFinite ((muFin Q₀ fun _ => 1).map e) :=
    (e.toHomeomorph.toMeasurableEquiv).sigmaFinite_map
  have hμK : ∀ v, muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (α₀ v) := fun v => by
    rw [muLocSO_soStabSO, div_one]
  have hμU : ∀ v, muLocSO v Q₀ 1 (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
      (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) = ENNReal.ofReal (nδ v * α₁ v) := fun v => by
    rw [sim_muLocSO_simU hn hQ v hc hG, ENNReal.ofReal_mul (hnδpos v).le]
  have hgood : ∀ v ∉ S, α₀ v = α₁ v := fun v hv =>
    sim_alpha_eq_of_good hn hQ v hc hG (by simpa [hS] using hv)
  have hm₀ : Multipliable α₀ := multipliable_siegelDensity hn0 hn2 Q₀ hQ
  have hm₁ : Multipliable α₁ := multipliable_siegelDensity hn0 hn2 _ hQ₁
  have hval : ((muFin Q₀ fun _ => 1).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) =
      ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) fun _ => 1) := by
    have hU : ∀ v ∈ S, MeasurableSet (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) := fun v _ =>
      ((isOpen_soStabSO v _).preimage (simConjSOV v hc hG).continuous).measurableSet
    rw [Measure.map_apply hmeas (isOpen_KSO _).measurableSet, simConjFin_preimage_KSO,
      muFin_boxSO Q₀ hQ (fun _ => one_pos) S _ hU]
    have hr : ∀ v, muLocSO v Q₀ 1 (simConjSOV (Q₀ := Q₀) v hc hG ⁻¹'
        (soStabSO v (simForm Q₀ c G) : Set (SOv v (simForm Q₀ c G)))) /
          muLocSO v Q₀ 1 (soStabSO v Q₀ : Set (SOv v Q₀)) = ENNReal.ofReal (nδ v * α₁ v / α₀ v) := fun v => by
      rw [hμU, hμK, ENNReal.ofReal_div_of_pos (hα₀ v)]
    rw [Finset.prod_congr rfl fun v _ => hr v,
      ← ENNReal.ofReal_prod_of_nonneg (fun v _ => (div_pos (mul_pos (hnδpos v) (hα₁ v)) (hα₀ v)).le),
      ← ENNReal.ofReal_mul (finFactor_nonneg _ _)]
    congr 1
    rw [finFactor_one _ hQ, finFactor_one _ hQ₁,
      tprod_eq_prod_mul_tprod_ite α₀ hm₀ S (fun v _ => (hα₀ v).ne'),
      tprod_eq_prod_mul_tprod_ite α₁ hm₁ S (fun v _ => (hα₁ v).ne'), tprod_eq_prod hnδ1,
      show (∏' v, if v ∈ S then (1 : ℝ) else α₀ v) = ∏' v, if v ∈ S then (1 : ℝ) else α₁ v from
        tprod_congr fun v => by by_cases hv : v ∈ S <;> simp [hv, hgood]]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    have h0 : ∏ v ∈ S, α₀ v ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => (hα₀ v).ne'
    field_simp
  have hfin : ((muFin Q₀ fun _ => 1).map e) (KSO (simForm Q₀ c G) : Set (SOAf (simForm Q₀ c G))) ≠ ∞ := by
    rw [hval]; exact ENNReal.ofReal_ne_top
  have hP : 0 ≤ ∏' v, nδ v := tprod_nonneg fun v => (hnδpos v).le
  rw [eq_haarNorm (isCompact_KSO _) (isOpen_KSO _) _ hfin, hval]
  unfold muFin
  rw [show (ENNReal.ofReal ((∏' v, nδ v) * finFactor (simForm Q₀ c G) fun _ => 1)).toNNReal =
      (∏' v, nδ v).toNNReal * (finFactor (simForm Q₀ c G) fun _ => 1).toNNReal by
    rw [← Real.toNNReal_mul hP]; exact ENNReal.toNNReal_coe _,
    sim_haarNorm_mul]
  ext A hA
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rfl

end Meas

end QuadFormsKB.Tamagawa.Measure.Weil
