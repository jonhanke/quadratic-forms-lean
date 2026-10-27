/-
# Consistency checks for Siegel's formula over every number field

* **Totally real fields** (`siegelIndefinite_uncond_specializes`): for totally real $F$ the headline
  `siegelIndefinite_uncond` has the same two sides as `siegelIndefinite_release_totallyReal_uncond`: the constants agree
  (`cInfNF_eq_cInf`) and the measures of representations agree class by class (`repMeasure_archFibrationNF_eq`: the
  fibration `archFibrationNF`, transported to the parameter space along $T_\infty\cong T^{NF}_\infty$, has the same
  stabilizer
  measures as `totallyRealArchFibration`, by uniqueness `ArchFibration.μH_eq`). For forms by forms see `cInfTNF_eq_cInfT`,
  `repMeasureT_frameArchFibrationNF_eq` (`FormsIndefiniteNF.lean`).
* **Rank one** (every number field): $c_\infty(\langle m\rangle)$ = `cInfNF m` (`cInfTNF_unary`), and the two headlines give the
  same total measure of the representations of $m$ (`siegelIndefiniteForms_unary_consistentNF`).
-/
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplex
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteNF
import QuadFormsKB.Tamagawa.Indefinite.FormsIndefiniteChecks

open MeasureTheory Measure MulAction Set NumberField
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Tamagawa.Measure.SphereLeray QuadFormsKB.Tamagawa.Measure.SphereLerayC
  NumberField.InfinitePlace LocalDensity

/-! ### Transport of a fibration along a change of parameters -/

section Transport

variable {A : Type*} [Group A] [MeasurableSpace A] [MeasurableMul A] {μA : Measure A}
  {Y : Type*} [MulAction A Y] {T T' : Type*} [MeasurableSpace T] [MeasurableSpace T'] {P : Set Y} {σ : Measure T}
  {τ : T → Y} {c : ℝ≥0∞}

/-- Orbit coordinates transported along $e : T'\cong T$. -/
def _root_.QuadFormsKB.Tamagawa.Measure.Weil.OrbitCoord.reparam {H G : Type*} [Group H] [Group G] [MeasurableSpace H] [MeasurableSpace G] [MulAction G Y]
    {ι : H →* G} {y₀ : Y} (C : OrbitCoord ι τ y₀) (e : T' ≃ᵐ T) : OrbitCoord ι (τ ∘ e) y₀ where
  coord := (MeasurableEquiv.prodCongr e (MeasurableEquiv.refl H)).trans C.coord
  mul x h h' := C.mul (e x) h h'
  orbit x h := C.orbit (e x) h

/-- **An archimedean fibration transported along a change of parameters** $e : T'\cong T$: the same stabilizer measures,
the measure $(e^{-1})_*\sigma$ and the parametrization $\tau\circ e$. -/
def ArchFibration.transport [SigmaFinite σ] (𝔉 : ArchFibration μA P σ τ c) (e : T' ≃ᵐ T) :
    ArchFibration μA P (σ.map e.symm) (τ ∘ e) c where
  μH := 𝔉.μH
  coord y hy := (𝔉.coord y hy).reparam e
  sigmaFinite := 𝔉.sigmaFinite
  leftInv := 𝔉.leftInv
  fib y hy := by
    have := 𝔉.sigmaFinite y
    have : SigmaFinite (σ.map e.symm) := e.symm.sigmaFinite_map
    refine (𝔉.fib y hy).trans ?_
    congr 1
    show _ = ((σ.map e.symm).prod (𝔉.μH y)).map ((𝔉.coord y hy).coord ∘ Prod.map e id)
    rw [← Measure.map_map (𝔉.coord y hy).coord.measurable (e.measurable.prodMap measurable_id),
      ← map_prod_map _ _ e.measurable measurable_id, Measure.map_id, e.map_map_symm]

/-- An archimedean fibration with its quadric, measure, parametrization and constant replaced by equal ones. -/
def ArchFibration.congr (𝔉 : ArchFibration μA P σ τ c) {P' : Set Y} {σ' : Measure T} {τ' : T → Y} {c' : ℝ≥0∞}
    (hP : P = P') (hσ : σ = σ') (hτ : τ = τ') (hc : c = c') : ArchFibration μA P' σ' τ' c' := by
  subst hP hσ hτ hc; exact 𝔉

theorem ArchFibration.congr_μH (𝔉 : ArchFibration μA P σ τ c) {P' : Set Y} {σ' : Measure T} {τ' : T → Y}
    {c' : ℝ≥0∞} (hP : P = P') (hσ : σ = σ') (hτ : τ = τ') (hc : c = c') : (𝔉.congr hP hσ hτ hc).μH = 𝔉.μH := by
  subst hP hσ hτ hc; rfl

end Transport

/-! ### Totally real fields -/

section TotallyReal

open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {k : ℕ} (Q₀ : QuadForm (𝓞 F) (k + 1))
  (hQ : Q₀.Nondegenerate)

open Classical in
/-- For totally real $F$, `cInfNF` is the constant `cInf`. -/
theorem cInfNF_eq_cInf (m : F) : cInfNF (k := k) m = cInf (k := k) m := by
  rw [cInfNF, cInf, Finset.univ_eq_empty (α := {w : InfinitePlace F // w.IsComplex}), Finset.prod_empty,
    Finset.prod_empty]

/-- The parameter space and the new one coincide when there is no complex place. -/
def tInfEquiv (m : F) : TInf Q₀ m ≃ᵐ TInfNF Q₀ m :=
  MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.ofUniqueOfUnique _ _)

theorem quadricInfNF_eq (m : F) : quadricInfNF Q₀ m = quadricInf Q₀ m := by
  ext x
  simp only [quadricInfNF, quadricInf, mem_prod, mem_univ_pi]
  exact and_congr Iff.rfl ⟨fun _ w => isEmptyElim w, fun _ w => isEmptyElim w⟩

theorem τInfNF_comp_tInfEquiv (m : F) : τInfNF Q₀ m ∘ tInfEquiv Q₀ m = τInf Q₀ m :=
  funext fun _ => Prod.ext rfl (funext fun w => isEmptyElim w)

theorem sigInfNF_map_tInfEquiv {m : F} (hm : m ≠ 0) :
    (sigInfNF Q₀ m).map (tInfEquiv Q₀ m).symm = sigInf Q₀ m := by
  have := fun w => sigmaFinite_sig (Q := QRe Q₀ w) (mR_ne_zero hm w)
  have hB : (Measure.pi fun w : {w : InfinitePlace F // w.IsComplex} =>
      ((2 : ℝ≥0∞) ^ k) • sigC (QCx Q₀ w) (mC m w)) = dirac isEmptyElim := Measure.pi_of_empty _
  have hB' : (Measure.pi fun _ : {w : InfinitePlace F // w.IsComplex} => (0 : Measure (Fin (k + 1) → ℂ))) =
      dirac isEmptyElim := Measure.pi_of_empty _
  rw [sigInfNF, sigInf, hB, hB']
  set e2 := MeasurableEquiv.ofUniqueOfUnique (∀ _w : {w : InfinitePlace F // w.IsComplex}, Fin (k + 1) → ℂ)
    (∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (mC m w))
  have key := map_prod_map (Measure.pi fun w => sig (QRe Q₀ w) (σR w m))
    (dirac (isEmptyElim : ∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (mC m w)))
    measurable_id e2.symm.measurable
  calc _ = ((Measure.pi fun w => sig (QRe Q₀ w) (σR w m)).map id).prod
        ((dirac (isEmptyElim : ∀ w : {w : InfinitePlace F // w.IsComplex}, SphC (QCx Q₀ w) (mC m w))).map e2.symm) :=
        key.symm
    _ = _ := by
        rw [Measure.map_id, map_dirac' e2.symm.measurable]
        congr 2

/-- `archFibrationNF` transported to the parameter space (same stabilizer measures). -/
def archFibrationNF_toTR {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) :
    ArchFibration (muArchTamSO Q₀ hQ) (quadricInf Q₀ m) (sigInf Q₀ m) (τInf Q₀ m) (cInf (k := k) m) :=
  haveI := sigmaFinite_sigInfNF Q₀ hm
  ((archFibrationNF Q₀ hQ hm hk).transport (tInfEquiv Q₀ m)).congr (quadricInfNF_eq Q₀ m)
    (sigInfNF_map_tInfEquiv Q₀ hm) (τInfNF_comp_tInfEquiv Q₀ m) (cInfNF_eq_cInf m)

/-- **Consistency of the measures of representations**: for totally real $F$, $\rho(M_i, m)$ computed with
`archFibrationNF` equals $\rho(M_i, m)$ computed with the `totallyRealArchFibration`. -/
theorem repMeasure_archFibrationNF_eq {m : F} (hm : m ≠ 0) (hk : 1 ≤ k) (η : RatSphere Q₀ m) (i : DC Q₀) :
    repMeasure Q₀ hQ m (archFibrationNF Q₀ hQ hm hk) i = repMeasure Q₀ hQ m (totallyRealArchFibration Q₀ hQ hm hk) i := by
  have h := repMeasure_eq_totallyReal Q₀ hQ hm hk (archFibrationNF_toTR Q₀ hQ hm hk) (sigInf_ne_zero Q₀ hm η) i
  refine Eq.trans ?_ h
  have := sigmaFinite_sigInfNF Q₀ hm
  show repMeasureOf _ _ (archFibrationNF Q₀ hQ hm hk).μH = repMeasureOf _ _ (archFibrationNF_toTR Q₀ hQ hm hk).μH
  rw [archFibrationNF_toTR, ArchFibration.congr_μH]
  rfl

/-- **The headline over every number field specializes to the totally real headline**: for totally real $F$ the two sides
of `siegelIndefinite_uncond` are those of `siegelIndefinite_release_totallyReal_uncond`. -/
theorem siegelIndefinite_uncond_specializes (hk : 3 ≤ k) {m : 𝓞 F} (hm : (m : F) ≠ 0) (ξ : RatSphere Q₀ (m : F)) :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (archFibrationNF Q₀ hQ hm (by omega)) i =
      cInf (k := k) (m : F) * ∑' i, repMeasure Q₀ hQ (m : F) (totallyRealArchFibration Q₀ hQ hm (by omega)) i := by
  exact congrArg₂ (· * ·) (cInfNF_eq_cInf _) (tsum_congr fun i => repMeasure_archFibrationNF_eq Q₀ hQ hm (by omega) ξ i)

end TotallyReal

/-! ### Rank one, every number field -/

section Unary

variable {F : Type} [Field F] [NumberField F] {n' : ℕ} (Q₀ : QuadForm (𝓞 F) (1 + n')) (m : 𝓞 F)

/-- For $r = 1$: $c_\infty(\langle m\rangle) = c_F(N)\prod_{w\mid\infty}|2m|_w^{-(N-1)}$ = `cInfNF m` (every number field). -/
theorem cInfTNF_unary : cInfTNF Q₀ (DVR.unary m) = cInfNF (k := n') (algebraMap (𝓞 F) F m) := by
  have hdet : algebraMap (𝓞 F) F (DVR.unary m).hessian.det = 2 * algebraMap (𝓞 F) F m := by
    rw [Matrix.det_unique]
    simp [DVR.unary, QuadForm.hessian, QuadForm.diag, two_mul]
  rw [cInfTNF, cInfNF, add_comm 1 n']
  simp only [hdet, map_mul, map_ofNat]

/-- **Consistency for $r = 1$, every number field**: the frame headline `siegelIndefiniteForms_uncond` and the vector headline
`siegelIndefinite_uncond` give the same total measure of the representations of $m$ (the form $Q_1$ in $1 + k$ variables
is transported to $k + 1$ variables along `Nat.add_comm`). -/
theorem siegelIndefiniteForms_unary_consistentNF {k : ℕ} (hk : 3 ≤ k)
    (Q₁ : QuadForm (𝓞 F) (1 + k)) (hQ₁ : Q₁.Nondegenerate) {m : 𝓞 F} (hm : (m : F) ≠ 0)
    (Ξ : RatFrame Q₁ (DVR.unary m)) :
    ∑' i, repMeasureT Q₁ (DVR.unary m) hQ₁
        (frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ) i =
      ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) (m : F)
        (archFibrationNF _ (nondegenerate_transport _ hQ₁) hm (by omega)) i := by
  have hT := unary_nondegenerate hm
  have h1 := siegelIndefiniteForms_uncond Q₁ hQ₁ (DVR.unary m) hT hk Ξ le_rfl
  obtain ⟨ξ⟩ := nonempty_ratSphere_transport (Nat.add_comm 1 k) Q₁ _ (ratFrameEquivRatSphere Q₁ m Ξ)
  have h2 := siegelIndefinite_uncond (nondegenerate_transport (Nat.add_comm 1 k) hQ₁) hk hm ξ
  have e : cInfNF (k := k) (m : F) = cInfTNF Q₁ (DVR.unary m) := (cInfTNF_unary Q₁ m).symm
  set B := ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) (m : F)
        (archFibrationNF _ (nondegenerate_transport _ hQ₁) hm (by omega)) i with hB
  clear_value B
  rw [e] at h2
  have hd : frameDensityProduct Q₁ (DVR.unary m) =
      finDensityProduct (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) m := by
    rw [frameDensityProduct_unary, finDensityProduct]
    simp only [localDensity_transport]
    congr 2
    push_cast
    ring
  rw [hd, ← tsum_unitVolume_transport (Nat.add_comm 1 k) Q₁ hQ₁] at h1
  have hc := cInfTNF_ne_zero_top Q₁ (DVR.unary m) hT
  exact (ENNReal.mul_right_inj hc.1 hc.2).1 (h1.trans h2.symm)

end Unary

end QuadFormsKB.Tamagawa.Indefinite
