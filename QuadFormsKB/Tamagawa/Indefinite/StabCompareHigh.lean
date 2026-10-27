/-
# Forms of rank one, $n' = N - 1\ge3$: the measures of representations class by class

**Layer:** number fields. $F$ a number field, $Q_1$ nondegenerate over $\mathcal O_F$ in $N = 1 + k$ variables, $k\ge3$ (any
signature), $m\in\mathcal O_F$, $m\ne0$, $\Xi$ a rational $1$-frame of $\langle m\rangle$. The forms headline
`siegelIndefiniteForms_uncond` at $r = 1$ measures the representations of $\langle m\rangle$ with the stabilizer
measures of `frameArchFibrationNF`; the numbers headline `siegelIndefinite_uncond` measures the representations of $m$
by
the transported form $h\triangleright Q_1$ ($h : 1 + k = k + 1$) with those of `archFibrationNF`. Until now only the totals
were compared (`siegelIndefiniteForms_unary_consistent`, totally real $F$).

**Proves** (unconditional)
* `map_frameArchFibrationNF_μH`: at every $X = a\,\Xi_\infty$, the frame stabilizer measure is that of
  `archFibrationNF` at $X_0$ (transported);
* **`repMeasureT_frameArchFibrationNF_unary`**: $\rho(M_i,\langle m\rangle)$ (frames) $=\rho(M_i, m)$
  (`archFibrationNF`, transported
  form, class `dcTransport i`) for every class $i$;
* **`siegelIndefinite_uncond_of_forms`**: the numbers headline for $h\triangleright Q_1$, derived from the forms
  headline
  `siegelIndefiniteForms_uncond` at $r = 1$ (every number field).
-/
import QuadFormsKB.Tamagawa.Indefinite.StabCompareCast
import QuadFormsKB.Tamagawa.Indefinite.StabCompareTernary
import QuadFormsKB.Tamagawa.Indefinite.SiegelComplexChecks

open MeasureTheory Measure Matrix MulAction Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil LocalDensity IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {k : ℕ} (hk : 3 ≤ k) (Q₁ : QuadForm (𝓞 F) (1 + k))
  (hQ₁ : Q₁.Nondegenerate) {m : 𝓞 F} (hm : (m : F) ≠ 0) (Ξ : RatFrame Q₁ (DVR.unary m))

/-- The frame data at infinity of the transported form, from the chosen frame data of `frameArchFibrationNF`. -/
abbrev highData : SplitDataInf (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (m : F)
    (fun i => Ξ.1 (Fin.cast (Nat.add_comm 1 k).symm i) 0) :=
  (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).toAlg.toSplitDataInfCast hm

/-- The sphere fibration of `archFibrationNF` of the transported form. -/
abbrev highSphere :=
  archFibrationNF (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) hm (by omega)

/-- The stabilizer measures of `archFibrationNF`, carried back to $G_\infty(Q_1)$. -/
def highFamily (y : VInf F (1 + k)) : Measure (stabilizer (GInfSO Q₁) y) :=
  ((highSphere hk Q₁ hQ₁ hm).μH (vCast (Nat.add_comm 1 k) y)).map (stabCast (Nat.add_comm 1 k) Q₁ y).symm

theorem frameLamNF_eq_lam : frameLamNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ =
    (highData hk Q₁ hQ₁ hm Ξ).lam := by
  have hg : (towerAdapted Q₁ hQ₁ (DVR.unary m) Ξ (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ)
      (unary_nondegenerate hm)).g.val.det =
      ((highData hk Q₁ hQ₁ hm Ξ).g : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det := by
    rw [towerAdapted_g_val, adaptedMat_eq, FrameTowerAlg.toSplitDataInfCast_g, det_castMat]
    rfl
  unfold frameLamNF SplitDataInf.lam
  rw [hg]

/-- **The stabilizer measures of `archFibrationNF` in terms of the frame data of $Q_1$**: at $y = a\,\Xi_{\infty,0}$,
the image of
$\lambda\,\mu^{\mathrm{Tam}}_{Q''}$ under $h\mapsto a\,\iota_\infty(h)\,a^{-1}$, for any such $a$. -/
theorem highFamily_eq (a : GInfSO Q₁) {y : VInf F (1 + k)} (ha : a • ratAT Q₁ (DVR.unary m) Ξ 0 = y)
    (f : GInfSO (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).Q'' → stabilizer (GInfSO Q₁) y)
    (hf : ∀ h, (f h : GInfSO Q₁) = a * (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).ιInf h * a⁻¹)
    (hfm : Measurable f) :
    highFamily hk Q₁ hQ₁ hm y = (frameLamNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ •
      muArchTamSO (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).Q''
        (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).hQ'').map f := by
  have ha' : gCast (Nat.add_comm 1 k) Q₁ a • ξInf (k := k) (fun i => Ξ.1 (Fin.cast (Nat.add_comm 1 k).symm i) 0) =
      vCast (Nat.add_comm 1 k) y := by
    rw [← vCast_ratAT, gCast_smul, ha]
  have hm1 := (highData hk Q₁ hQ₁ hm Ξ).measurable_conjHomAt _ ha'
  have hm2 := measurable_stabCast_symm (Nat.add_comm 1 k) Q₁ y
  unfold highFamily
  rw [archFibrationNF_μH_eq_at _ _ hm _ (highData hk Q₁ hQ₁ hm Ξ) _ ha', ← frameLamNF_eq_lam hk Q₁ hQ₁ hm Ξ,
    Measure.map_smul _ hm1.aemeasurable, Measure.map_smul _ hm2.aemeasurable, Measure.map_smul _ hfm.aemeasurable,
    Measure.map_map hm2 hm1]
  congr 2
  funext h
  apply Subtype.ext
  rw [Function.comp_apply, coe_stabCast_symm, SplitDataInf.conjHomAt_apply]
  refine Eq.trans ?_ (hf h).symm
  change (gCast _ Q₁).symm (gCast _ Q₁ a *
    gCast _ Q₁ ((chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).ιInf h) * (gCast _ Q₁ a)⁻¹) = _
  rw [← map_inv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]

theorem highFamily_leftInv (y : VInf F (1 + k)) : (highFamily hk Q₁ hQ₁ hm y).IsMulLeftInvariant := by
  haveI := (highSphere hk Q₁ hQ₁ hm).leftInv (vCast (Nat.add_comm 1 k) y)
  haveI := measurableMul_subgroup (stabilizer (GInfSO Q₁) y)
  haveI := measurableMul_subgroup (stabilizer (GInfSO (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)))
    (vCast (Nat.add_comm 1 k) y))
  exact isMulLeftInvariant_map (stabCast (Nat.add_comm 1 k) Q₁ y).symm.toMulHom
    (measurable_stabCast_symm _ _ _) (stabCast (Nat.add_comm 1 k) Q₁ y).symm.surjective

/-- $h\mapsto a\,\iota_\infty(h)\,a^{-1}$ into the stabilizer of $y = a\,\Xi_{\infty,0}$. -/
def highConj (a : GInfSO Q₁) {y : VInf F (1 + k)} (ha : a • ratAT Q₁ (DVR.unary m) Ξ 0 = y)
    (h : GInfSO (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).Q'') : stabilizer (GInfSO Q₁) y :=
  ⟨a * (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).ιInf h * a⁻¹, by
    show (a * _ * a⁻¹) • y = y
    rw [← ha, mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (a • ·) (congrFun (FrameTowerAlg.ιInf_smul_ratAT Q₁ hQ₁ (DVR.unary m) Ξ
      (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).toAlg h) 0)⟩

theorem measurable_highConj (a : GInfSO Q₁) {y : VInf F (1 + k)} (ha : a • ratAT Q₁ (DVR.unary m) Ξ 0 = y) :
    Measurable (highConj hk Q₁ hQ₁ hm Ξ a ha) :=
  (((measurable_const_mul a).comp
    (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).measurable_ιInf).mul_const _).subtype_mk

include hk hQ₁ hm in
/-- Every representation of $\langle m\rangle$ lies in the $G_\infty$-orbit of $\Xi_\infty$ (Witt's theorem over $F$). -/
theorem mem_orbit_high (i : DC Q₁) (X : repsT Q₁ (DVR.unary m) i) :
    (X : Fin 1 → VInf F (1 + k)) ∈ Set.range fun a : GInfSO Q₁ => a • ratAT Q₁ (DVR.unary m) Ξ := by
  obtain ⟨Ξ', hΞ'⟩ := exists_ratFrame_of_mem_repsT Q₁ m i X
  obtain ⟨γ, hγ⟩ := FrameTowerAlg.exists_smul_eq_ratFrame Q₁ hQ₁ (DVR.unary m) Ξ
    (chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).toAlg (unary_nondegenerate hm) (by omega) Ξ'
  exact ⟨(γ : SOAdele Q₁).1, by rw [← hΞ', ← hγ, ratAT_smul]⟩

/-- **The frame stabilizer measure is that of `archFibrationNF`**: at every $X = a\,\Xi_\infty$, carried by
$H_X = H_{X_0}$. -/
theorem map_frameArchFibrationNF_μH (X : Fin 1 → VInf F (1 + k))
    (hX : X ∈ Set.range fun a : GInfSO Q₁ => a • ratAT Q₁ (DVR.unary m) Ξ) :
    ((frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).μH X).map (stabFrameVecME X) =
      highFamily hk Q₁ hQ₁ hm (X 0) := by
  have ha := hX.choose_spec
  set a := hX.choose
  have ha0 : a • ratAT Q₁ (DVR.unary m) Ξ 0 = X 0 := congrFun ha 0
  set D := chosenTower Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ
  have hf : ∀ h, (((stabFrameVecME X).symm (highConj hk Q₁ hQ₁ hm Ξ a ha0 h) : stabilizer (GInfSO Q₁) X) :
      GInfSO Q₁) = a * D.ιInf h * a⁻¹ := fun h => rfl
  have hm1 : Measurable fun h => (stabFrameVecME X).symm (highConj hk Q₁ hQ₁ hm Ξ a ha0 h) :=
    (stabFrameVecME X).symm.measurable.comp (measurable_highConj hk Q₁ hQ₁ hm Ξ a ha0)
  have h1 : (frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ).μH X =
      frameLamNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ • (muArchTamSO D.Q'' D.hQ'').map
        (fun h => (stabFrameVecME X).symm (highConj hk Q₁ hQ₁ hm Ξ a ha0 h)) := by
    haveI := sigmaFinite_frameσA Q₁ hQ₁ (DVR.unary m) Ξ D
    show _ • (frameArchFibTam Q₁ hQ₁ (DVR.unary m) Ξ D).μH X = _
    rw [frameArchFibTam, archFibrationOfCoord_μH _ _ _ _ _ _ _ hX]
    exact congrArg _ (stabMeasureAt_eq_map_of _ _ _ _ _ _ _ hf)
  rw [h1, Measure.map_smul _ (stabFrameVecME X).measurable.aemeasurable,
    highFamily_eq hk Q₁ hQ₁ hm Ξ a ha0 _ (fun h => rfl) (measurable_highConj hk Q₁ hQ₁ hm Ξ a ha0),
    Measure.map_smul _ (measurable_highConj hk Q₁ hQ₁ hm Ξ a ha0).aemeasurable]
  congr 1
  refine (Measure.map_map (stabFrameVecME X).measurable hm1).trans ?_
  exact congrArg (fun f => Measure.map f _) (funext fun h => (stabFrameVecME X).apply_symm_apply _)

/-- **The measures of representations of the forms headline at $r = 1$ are those of `archFibrationNF`, class by
class** ($n' = k\ge3$, every
number field): for every class $i$, $\rho(M_i,\langle m\rangle)$ for `frameArchFibrationNF` equals $\rho(M_i, m)$ for
the
sphere fibration `archFibrationNF` of the transported form ($1 + k = k + 1$), class `dcTransport i`. -/
@[kb "siegel1935" "Über die analytische Theorie der quadratischen Formen; measure of representations (forms of rank one = numbers, class by class) [unverified]"]
theorem repMeasureT_frameArchFibrationNF_unary (i : DC Q₁) :
    repMeasureT Q₁ (DVR.unary m) hQ₁ (frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ) i =
      repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) (m : F)
        (archFibrationNF _ (nondegenerate_transport _ hQ₁) hm (by omega)) (dcTransport (Nat.add_comm 1 k) Q₁ i) := by
  set 𝔉T := frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ
  have := countable_GammaSOAdele Q₁
  haveI : Countable (unitGroup Q₁ i) := countable_levelGroup (Γ := GammaSOAdele Q₁) (KSO Q₁) (dcRep Q₁ i)
  unfold repMeasureT repMeasure
  rw [repMeasureOf_cast]
  change _ = repMeasureOf (unitGroup Q₁ i) (reps Q₁ (m : F) i) (highFamily hk Q₁ hQ₁ hm)
  refine repMeasureOf_congr _ _ _ (repsFrameVec Q₁ m i) (repsFrameVec_smul Q₁ m i) _ _ ?_ ?_
  · intro X
    have hX := mem_orbit_high hk Q₁ hQ₁ hm Ξ i X
    have key : ∀ y' (h : (X : Fin 1 → VInf F (1 + k)) 0 = y'),
        covolume (stabArith (unitGroup Q₁ i) (X : Fin 1 → VInf F (1 + k)))
          (stabilizer (GInfSO Q₁) (X : Fin 1 → VInf F (1 + k))) (𝔉T.μH X) =
        covolume (stabArith (unitGroup Q₁ i) y') (stabilizer (GInfSO Q₁) y') (highFamily hk Q₁ hQ₁ hm y') := by
      rintro _ rfl
      haveI := 𝔉T.leftInv (X : Fin 1 → VInf F (1 + k))
      haveI := highFamily_leftInv hk Q₁ hQ₁ hm ((X : Fin 1 → VInf F (1 + k)) 0)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₁ i) (X : Fin 1 → VInf F (1 + k)))
        (𝔉T.μH X)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₁ i) ((X : Fin 1 → VInf F (1 + k)) 0))
        (highFamily hk Q₁ hQ₁ hm ((X : Fin 1 → VInf F (1 + k)) 0))
      exact covolume_stabArith_conj _ _ _ 1 (Subgroup.one_mem _) (stabFrameVec (X : Fin 1 → VInf F (1 + k)))
        (fun s => by simp [coe_stabFrameVec]) _ _ (map_frameArchFibrationNF_μH hk Q₁ hQ₁ hm Ξ _ hX)
    exact key _ (repsFrameVec_apply Q₁ m i X).symm
  · intro y γ
    obtain ⟨a, ha⟩ : ∃ a : GInfSO Q₁, a • ratAT Q₁ (DVR.unary m) Ξ 0 = (y : VInf F (1 + k)) := by
      obtain ⟨a, ha⟩ := mem_orbit_high hk Q₁ hQ₁ hm Ξ i ((repsFrameVec Q₁ m i).symm y)
      refine ⟨a, ?_⟩
      have h1 := congrFun ha 0
      have h2 := repsFrameVec_apply Q₁ m i ((repsFrameVec Q₁ m i).symm y)
      rw [Equiv.apply_symm_apply] at h2
      rw [h2]
      exact h1
    have key : ∀ y'' (h : (γ : GInfSO Q₁) • (y : VInf F (1 + k)) = y''),
        covolume (stabArith (unitGroup Q₁ i) y'') (stabilizer (GInfSO Q₁) y'') (highFamily hk Q₁ hQ₁ hm y'') =
        covolume (stabArith (unitGroup Q₁ i) (y : VInf F (1 + k))) (stabilizer (GInfSO Q₁) (y : VInf F (1 + k)))
          (highFamily hk Q₁ hQ₁ hm y) := by
      rintro _ rfl
      haveI := highFamily_leftInv hk Q₁ hQ₁ hm (y : VInf F (1 + k))
      haveI := highFamily_leftInv hk Q₁ hQ₁ hm ((γ : GInfSO Q₁) • (y : VInf F (1 + k)))
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₁ i) (y : VInf F (1 + k)))
        (highFamily hk Q₁ hQ₁ hm y)
      haveI := smulInvariantMeasure_subgroup (stabArith (unitGroup Q₁ i) ((γ : GInfSO Q₁) • (y : VInf F (1 + k))))
        (highFamily hk Q₁ hQ₁ hm ((γ : GInfSO Q₁) • (y : VInf F (1 + k))))
      have hγa : ((γ : GInfSO Q₁) * a) • ratAT Q₁ (DVR.unary m) Ξ 0 = (γ : GInfSO Q₁) • (y : VInf F (1 + k)) := by
        rw [mul_smul, ha]
      refine (covolume_stabArith_conj _ _ _ (γ : GInfSO Q₁) γ.2 (stabConj (γ : GInfSO Q₁) (y : VInf F (1 + k)))
        (coe_stabConj _ _) _ _ ?_).symm
      rw [highFamily_eq hk Q₁ hQ₁ hm Ξ a ha _ (fun h => rfl) (measurable_highConj hk Q₁ hQ₁ hm Ξ a ha),
        highFamily_eq hk Q₁ hQ₁ hm Ξ _ hγa _ (fun h => rfl) (measurable_highConj hk Q₁ hQ₁ hm Ξ _ hγa),
        Measure.map_map (measurable_stabConj _ _) (measurable_highConj hk Q₁ hQ₁ hm Ξ a ha)]
      congr 1
      funext h
      apply Subtype.ext
      simp only [Function.comp_apply, coe_stabConj, highConj, mul_assoc, _root_.mul_inv_rev]
    exact key _ rfl

include Ξ in
/-- **The numbers headline from the forms headline at $r = 1$** ($N = k + 1\ge4$, every number field): for a
nondegenerate $Q_1$ over $\mathcal O_F$ in $1 + k$ variables, $k\ge3$ (any signature), and $m\in\mathcal O_F\setminus0$ represented
over $F$ (a rational $1$-frame $\Xi$ of $\langle m\rangle$), the transported form $Q_0 = h\triangleright Q_1$ in $k + 1$ variables satisfies
$$c_\infty(m)\sum_i\rho(M_i, m) = |d_F|^{-(N-1)/2}\prod_\mathfrak p\beta_\mathfrak p(L, m)\cdot\sum_iv(M_i),$$
with the measures of representations of `archFibrationNF` (`archFibrationNF`). This is the statement of
`siegelIndefinite_uncond`, derived
here from `siegelIndefiniteForms_uncond` at $r = 1$ and `repMeasureT_frameArchFibrationNF_unary` (no use of the numbers
headline). **Unconditional.** -/
@[kb "siegel1936" "Indefinite quadratische Formen, Hauptsatz (measure form; numbers as forms of rank one; every number field) [unverified]"]
theorem siegelIndefinite_uncond_of_forms :
    cInfNF (k := k) (m : F) * ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1))
        (nondegenerate_transport _ hQ₁) (m : F) (archFibrationNF _ (nondegenerate_transport _ hQ₁) hm (by omega)) i =
      ENNReal.ofReal (finDensityProduct (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) m) *
        ∑' i, unitVolume (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁) i := by
  have h1 := siegelIndefiniteForms_uncond Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ le_rfl
  have e1 : cInfNF (k := k) (m : F) = cInfTNF Q₁ (DVR.unary m) := (cInfTNF_unary Q₁ m).symm
  have hd : frameDensityProduct Q₁ (DVR.unary m) =
      finDensityProduct (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) m := by
    rw [frameDensityProduct_unary, finDensityProduct]
    simp only [localDensity_transport]
    congr 2
    push_cast
    ring
  have hs : ∑' i, repMeasure (Nat.add_comm 1 k ▸ Q₁ : QuadForm (𝓞 F) (k + 1)) (nondegenerate_transport _ hQ₁)
      (m : F) (archFibrationNF _ (nondegenerate_transport _ hQ₁) hm (by omega)) i =
      ∑' i, repMeasureT Q₁ (DVR.unary m) hQ₁
        (frameArchFibrationNF Q₁ hQ₁ (DVR.unary m) (unary_nondegenerate hm) hk Ξ) i := by
    rw [← (dcTransport (Nat.add_comm 1 k) Q₁).tsum_eq]
    exact tsum_congr fun i => (repMeasureT_frameArchFibrationNF_unary hk Q₁ hQ₁ hm Ξ i).symm
  rw [hs, e1, ← hd, tsum_unitVolume_transport (Nat.add_comm 1 k) Q₁ hQ₁]
  exact h1

end QuadFormsKB.Tamagawa.Indefinite
