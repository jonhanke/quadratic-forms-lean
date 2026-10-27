/-
# The archimedean fibration of frames from the adelic frame coordinates

**Layer:** number fields, adeles. $F$ a number field, $Q_0$ nondegenerate over $\mathcal O_F$ in $N = r + n'$ variables
(any signature), $T_0$ of rank $r$, a rational frame $\Xi$ of $T_0$ and frame coordinates `D : FrameTower Q₀ hQ n' Ξ`
(complement $Q''$, $\iota = \iota_\infty\times\iota_f$).

**Defines**
* `splitFrame`: an adelic frame as (archimedean frame, finite frame); `frameCprod`: the coordinates of `D` on
  $V_\infty^r\times(\mathbb A_f^N)^r$;
* `frameCA`: their archimedean factor $T_A\times SO(Q'')(F_\infty)\cong SO(V)(F_\infty)$, $T_A$ the $G_\infty$-orbit of
  $\Xi_\infty$ (`OrbitCoord.fstFactor`; no archimedean sections are constructed);
* `frameσA`: the archimedean quotient measure, $\mu_{G_\infty} = \mathrm{coord}_*(\sigma_A\otimes\mu_{H_\infty})$ (Tamagawa
  measures, `frameσA_fib`);
* **`frameArchFibTam`**: the archimedean fibration over the orbit of $\Xi_\infty$ (`ArchFibration`), stabilizer
  measures the transported Tamagawa measures of $SO(Q'')(F_\infty)$, constant $1$.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameTower
import QuadFormsKB.Tamagawa.Indefinite.FrameClassical
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamUnimodular
import QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereCont

open MeasureTheory Set Matrix MulAction
open scoped ENNReal Pointwise

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open NumberField NumberField.InfinitePlace IsDedekindDomain QuadFormsKB.Lattices QuadFormsKB.Tamagawa
  QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil

variable {F : Type} [Field F] [NumberField F] {r n' : ℕ}

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Splitting adelic frames into archimedean and finite parts -/

/-- An adelic frame as (archimedean frame, finite frame). -/
def splitFrame {N : ℕ} (Y : Fin r → AdeleSpace F (Fin N)) : (Fin r → VInf F N) × (Fin r → Fin N → AF) :=
  (fun j => archVec (Y j), fun j => finVec (Y j))

theorem splitFrame_smul {N : ℕ} (Q₀ : QuadForm (𝓞 F) N) (g : SOAdele Q₀) (Y : Fin r → AdeleSpace F (Fin N)) :
    splitFrame (g • Y) = g • splitFrame Y := by
  rw [prod_smul_def]
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
  · exact archVec_smul Q₀ g (Y j)
  · exact finVec_smul Q₀ g (Y j)

theorem splitFrame_injective {N : ℕ} : Function.Injective (splitFrame (F := F) (r := r) (N := N)) := by
  intro Y Y' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  funext j k
  have a1 := congrFun (congrArg Prod.fst (congrFun h1 j)) 
  have a2 := congrFun (congrArg Prod.snd (congrFun h1 j))
  have b := congrFun (congrFun h2 j) k
  refine Prod.ext (Prod.ext ?_ ?_) b
  · funext w
    exact congrFun (a1 w) k
  · funext w
    exact congrFun (a2 w) k

variable (Q₀ : QuadForm (𝓞 F) (r + n')) (hQ : Q₀.Nondegenerate) (T₀ : QuadForm (𝓞 F) r) (Ξ : RatFrame Q₀ T₀)
  (D : FrameTower Q₀ hQ n' (cols Ξ.1))

theorem splitFrame_ratFrame : splitFrame (frameA (cols Ξ.1)) = (ratAT Q₀ T₀ Ξ, ratFT Q₀ T₀ Ξ) := rfl

/-- The frame coordinates of `D` on archimedean × finite frames. -/
def frameCprod : OrbitCoord (MonoidHom.prodMap D.ιInf D.ιFin) (splitFrame ∘ D.τ) (ratAT Q₀ T₀ Ξ, ratFT Q₀ T₀ Ξ) :=
  D.C.transport splitFrame (splitFrame_smul Q₀)

theorem stabIn_frameCprod : StabIn (MonoidHom.prodMap D.ιInf D.ιFin) (ratAT Q₀ T₀ Ξ, ratFT Q₀ T₀ Ξ) := by
  intro g hg
  refine D.stab g (splitFrame_injective ?_)
  rw [splitFrame_smul, splitFrame_ratFrame]
  exact hg

theorem measurable_inv_smul_ratAT : Measurable fun a : GInfSO Q₀ => a⁻¹ • ratAT Q₀ T₀ Ξ :=
  Measurable.of_eval fun j =>
    ((continuous_GInf_smul Q₀).comp ((continuous_inv).prodMk (continuous_const (y := ratAT Q₀ T₀ Ξ j)))).measurable

theorem countablySeparated_prod' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountablySeparated α] [MeasurableSpace.CountablySeparated β] :
    MeasurableSpace.CountablySeparated (α × β) := by
  obtain ⟨S, hSc, hSm, hS⟩ := (MeasurableSpace.countablySeparated_def.mp ‹MeasurableSpace.CountablySeparated α›)
  obtain ⟨S', hSc', hSm', hS'⟩ := (MeasurableSpace.countablySeparated_def.mp ‹MeasurableSpace.CountablySeparated β›)
  refine MeasurableSpace.countablySeparated_def.mpr
    ⟨(fun u => u ×ˢ (univ : Set β)) '' S ∪ (fun u => (univ : Set α) ×ˢ u) '' S', (hSc.image _).union (hSc'.image _),
      ?_, ?_⟩
  · rintro _ (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hSm u hu).prod MeasurableSet.univ
    · exact MeasurableSet.univ.prod (hSm' u hu)
  · rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
    refine Prod.ext (hS a trivial a' trivial fun u hu => ?_) (hS' b trivial b' trivial fun u hu => ?_)
    · simpa using h _ (Or.inl ⟨u, hu, rfl⟩)
    · simpa using h _ (Or.inr ⟨u, hu, rfl⟩)

theorem countablySeparated_frameSet {N : ℕ} (s : Set (Fin r → VInf F N)) :
    MeasurableSpace.CountablySeparated s := by
  have h1 : OpensMeasurableSpace (Fin r → VInf F N) :=
    @Pi.opensMeasurableSpace (Fin r) (fun _ => VInf F N) _ _ _ _ _
  have h2 : SecondCountableTopology (Fin r → VInf F N) := inferInstance
  have h3 : HasCountableSeparatingOn (Fin r → VInf F N) IsOpen s := inferInstance
  have h4 : HasCountableSeparatingOn (Fin r → VInf F N) MeasurableSet s :=
    h3.mono (fun _ hu => hu.measurableSet) subset_rfl
  exact MeasurableSpace.CountablySeparated.subtype_iff.mpr h4

/-- **The archimedean coordinates** $T_A\times SO(Q'')(F_\infty)\cong SO(V)(F_\infty)$ of the orbit of $\Xi_\infty$. -/
def frameCA : OrbitCoord D.ιInf
    (Subtype.val : factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ) → Fin r → VInf F (r + n')) (ratAT Q₀ T₀ Ξ) := by
  haveI := polishSpace_of_isTopologicalGroup (GInfSO Q₀)
  haveI := polishSpace_of_isTopologicalGroup (GInfSO D.Q'')
  haveI : MeasurableSpace.CountablySeparated (factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ)) :=
    countablySeparated_frameSet _
  haveI : MeasurableSpace.CountablySeparated (GInfSO D.Q'') := inferInstance
  haveI : MeasurableSpace.CountablySeparated (factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ) × GInfSO D.Q'') :=
    countablySeparated_prod'
  refine OrbitCoord.fstFactor (ιA := D.ιInf) (ιB := D.ιFin) (τ := splitFrame ∘ D.τ) (a₀ := ratAT Q₀ T₀ Ξ)
    (b₀ := ratFT Q₀ T₀ Ξ) (frameCprod Q₀ hQ T₀ Ξ D) ?_ ?_
  · exact stabIn_frameCprod Q₀ hQ T₀ Ξ D
  · exact measurable_inv_smul_ratAT Q₀ T₀ Ξ

instance finOnCompacts_muArchTamSO_frame {N : ℕ} (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) :
    IsFiniteMeasureOnCompacts (muArchTamSO Q hQ) := by
  classical
  have := LerayArch.isHaarMeasure_muArchLeray (QRe Q) (QCx Q) (gramDetR_QRe_ne_zero Q hQ)
    (gramDetC_QCx_ne_zero Q hQ)
  unfold muArchTamSO LerayArch.muArchNF; rw [ofReal_smul_eq]; infer_instance

theorem muArchTamSO_ne_zero' {N : ℕ} (Q : QuadForm (𝓞 F) N) (hQ : Q.Nondegenerate) : muArchTamSO Q hQ ≠ 0 :=
  fun h => muArchTamSO_univ_ne_zero Q hQ (by rw [h]; rfl)

/-- A reference set $U\subseteq SO(Q'')(F_\infty)$ with $0 < \mu(U) < \infty$. -/
theorem exists_refSetInf : ∃ U : Set (GInfSO D.Q''), MeasurableSet U ∧ muArchTamSO D.Q'' D.hQ'' U ≠ 0 ∧
    muArchTamSO D.Q'' D.hQ'' U ≠ ⊤ :=
  OrbitSection.exists_pos_lt_top _ (muArchTamSO_ne_zero' D.Q'' D.hQ'')

/-- **The archimedean quotient measure** on $T_A$: $\mu_{G_\infty}/\mu_{H_\infty}$ for the Tamagawa measures. -/
def frameσA : Measure (factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ)) :=
  quotMeasure (frameCA Q₀ hQ T₀ Ξ D).coord (muArchTamSO Q₀ hQ) (exists_refSetInf Q₀ hQ T₀ Ξ D).choose
    (muArchTamSO D.Q'' D.hQ'')

/-- The covering sets $A_i = \{t : C(t, 1)\in K_i\}$ of the archimedean parameter space. -/
def frameCover (i : ℕ) : Set (factorT (splitFrame ∘ D.τ) (ratFT Q₀ T₀ Ξ)) :=
  (fun t => (frameCA Q₀ hQ T₀ Ξ D).coord (t, 1)) ⁻¹' compactCovering (GInfSO Q₀) i

theorem measurableSet_frameCover (i : ℕ) : MeasurableSet (frameCover Q₀ hQ T₀ Ξ D i) :=
  ((frameCA Q₀ hQ T₀ Ξ D).coord.measurable.comp (measurable_id.prodMk measurable_const))
    (isCompact_compactCovering (GInfSO Q₀) i).isClosed.measurableSet

theorem iUnion_frameCover : ⋃ i, frameCover Q₀ hQ T₀ Ξ D i = univ := by
  simp only [frameCover, ← preimage_iUnion, iUnion_compactCovering, preimage_univ]

theorem frameCover_fin (i : ℕ) (K : Set (GInfSO D.Q'')) (hK : IsCompact K) :
    muArchTamSO Q₀ hQ ((frameCA Q₀ hQ T₀ Ξ D).coord.symm ⁻¹' (frameCover Q₀ hQ T₀ Ξ D i ×ˢ K)) ≠ ⊤ := by
  have hc : IsCompact (D.ιInf '' K * compactCovering (GInfSO Q₀) i) :=
    (hK.image D.continuous_ιInf).mul (isCompact_compactCovering (GInfSO Q₀) i)
  refine ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono ?_)
  intro g hg
  simp only [mem_preimage, mem_prod] at hg
  have e : g = (frameCA Q₀ hQ T₀ Ξ D).coord ((frameCA Q₀ hQ T₀ Ξ D).coord.symm g) :=
    ((frameCA Q₀ hQ T₀ Ξ D).coord.apply_symm_apply g).symm
  rw [e, (frameCA Q₀ hQ T₀ Ξ D).coord_eq]
  exact Set.mul_mem_mul ⟨_, hg.2, rfl⟩ hg.1

theorem frame_hμ (h' : GInfSO D.Q'') (E : Set (GInfSO Q₀)) :
    muArchTamSO Q₀ hQ ((fun g => D.ιInf h' * g) ⁻¹' E) = muArchTamSO Q₀ hQ E :=
  measure_preimage_mul _ _ _

theorem sigmaFinite_frameσA : SigmaFinite (frameσA Q₀ hQ T₀ Ξ D) := by
  have hspec := (exists_refSetInf Q₀ hQ T₀ Ξ D).choose_spec
  have := sigmaFinite_quotMeasure (frameCA Q₀ hQ T₀ Ξ D).coord D.ιInf (frameCA Q₀ hQ T₀ Ξ D).mul
    (muArchTamSO Q₀ hQ) (fun h' E _ => frame_hμ Q₀ hQ T₀ Ξ D h' E) (muArchTamSO D.Q'' D.hQ'')
    (muArchTamSO_ne_zero' D.Q'' D.hQ'') hspec.1 hspec.2.1 hspec.2.2 (frameCover Q₀ hQ T₀ Ξ D)
    (measurableSet_frameCover Q₀ hQ T₀ Ξ D) (iUnion_frameCover Q₀ hQ T₀ Ξ D) (frameCover_fin Q₀ hQ T₀ Ξ D)
  exact this

theorem frameσA_fib : muArchTamSO Q₀ hQ = ((frameσA Q₀ hQ T₀ Ξ D).prod (muArchTamSO D.Q'' D.hQ'')).map
    (frameCA Q₀ hQ T₀ Ξ D).coord := by
  have hspec := (exists_refSetInf Q₀ hQ T₀ Ξ D).choose_spec
  exact map_prod_quotMeasure (frameCA Q₀ hQ T₀ Ξ D).coord D.ιInf (frameCA Q₀ hQ T₀ Ξ D).mul
    (muArchTamSO Q₀ hQ) (fun h' E _ => frame_hμ Q₀ hQ T₀ Ξ D h' E) (muArchTamSO D.Q'' D.hQ'')
    (muArchTamSO_ne_zero' D.Q'' D.hQ'') hspec.1 hspec.2.1 hspec.2.2 (frameCover Q₀ hQ T₀ Ξ D)
    (measurableSet_frameCover Q₀ hQ T₀ Ξ D) (iUnion_frameCover Q₀ hQ T₀ Ξ D) (frameCover_fin Q₀ hQ T₀ Ξ D)

theorem frameσA_ne_zero : frameσA Q₀ hQ T₀ Ξ D ≠ 0 := by
  intro h
  have := frameσA_fib Q₀ hQ T₀ Ξ D
  rw [h, Measure.zero_prod, Measure.map_zero] at this
  exact muArchTamSO_ne_zero' Q₀ hQ this

theorem stab_ιInf (g : GInfSO Q₀) (hg : g • ratAT Q₀ T₀ Ξ = ratAT Q₀ T₀ Ξ) : ∃ h, D.ιInf h = g := by
  obtain ⟨h, hh⟩ := stabIn_frameCprod Q₀ hQ T₀ Ξ D (g, 1) (by
    rw [prod_smul_def, hg, one_smul])
  exact ⟨h.1, congrArg Prod.fst hh⟩

theorem injective_ιInf : Function.Injective D.ιInf := fun a b hab => by
  have := D.C.ι_injective (a₁ := ((a : GInfSO D.Q''), (1 : SOAf D.Q''))) (a₂ := (b, 1))
    (Prod.ext hab (by simp))
  exact congrArg Prod.fst this

theorem measurableEmbedding_ιInf : MeasurableEmbedding D.ιInf := by
  have := polishSpace_of_isTopologicalGroup (GInfSO D.Q'')
  have := polishSpace_of_isTopologicalGroup (GInfSO Q₀)
  have : MeasurableSpace.CountablySeparated (GInfSO Q₀) := inferInstance
  exact D.measurable_ιInf.measurableEmbedding (injective_ιInf Q₀ hQ T₀ Ξ D)

/-- **The archimedean fibration of frames** (Tamagawa normalization): over the $G_\infty$-orbit of $\Xi_\infty$, stabilizer
measures the transported Tamagawa measures of $SO(Q'')(F_\infty)$, measure $\sigma_A$, constant $1$. -/
def frameArchFibTam :
    haveI := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
    ArchFibration (muArchTamSO Q₀ hQ) (Set.range fun a : GInfSO Q₀ => a • ratAT Q₀ T₀ Ξ) (frameσA Q₀ hQ T₀ Ξ D)
      Subtype.val 1 :=
  haveI := sigmaFinite_frameσA Q₀ hQ T₀ Ξ D
  archFibrationOfCoord (frameCA Q₀ hQ T₀ Ξ D) (stab_ιInf Q₀ hQ T₀ Ξ D) (measurableEmbedding_ιInf Q₀ hQ T₀ Ξ D)
    (muArchTamSO Q₀ hQ) (muArchTamSO D.Q'' D.hQ'') 1 (by rw [one_smul]; exact frameσA_fib Q₀ hQ T₀ Ξ D)

end QuadFormsKB.Tamagawa.Indefinite
