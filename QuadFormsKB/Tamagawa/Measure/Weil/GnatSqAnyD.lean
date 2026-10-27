import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqFibration
import QuadFormsKB.Tamagawa.Measure.Weil.SplitSL1Final

/-!
# The square model for every quaternion algebra, and the semidirect fibration on sets

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus0$, $D = \mathbb H[F,a,b]$ any quaternion algebra (division or
$M_2(F)$), the square model $G^\natural = \{(\alpha,\beta,u) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta = u\}$ (`gnatSqO`).

Earlier results assumed $D$ to be a division algebra (hypothesis `hdiv`) for two facts about $\mu_{\mathrm{SL}_1}$: its
conjugation invariance and $\tau(\mathrm{SL}_1(D)) = 1$. Both hold for every $D$ (`map_adK_muSL1_of_isMulRightInvariant`
with `isMulRightInvariant_muSL1_of_lt_top`, and `tauSL1EqOne`). This file removes the hypothesis:

* `map_adK_muSL1N_any`, `covolume_muSL1N_any`, `map_adK_muSq_any`, `covolume_muSq_any`;
* **`covolume_gnatSq_any`**: $\operatorname{vol}(P(F)\backslash P(\mathbb A),\mu_P) = 2$ for every quaternion algebra over every
  number field.

It also generalizes the semidirect fibration `muP_sqS0` from open subgroups to open **sets** $H, E$, which is what
a test set with a small archimedean component needs:

* **`muP_sqS0Set`**: for $S_0 = \{(\alpha,\beta,u) : \beta\in H,\ \alpha\beta^{-1}\in E\}$ and a measurable $B\subseteq\mathbb A^\times$
  with $\mathrm{tamIdeles}\{u : \beta u\in H,\ u^2\operatorname{nrd}\beta\in B\} = c\in(0,\infty)$ for every $\beta\in H$,
  $$\mu_P(\pi(S_0)) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mu_{PD}(\operatorname{pd}(H)).$$

Source: Weil 1982, §2.4, Thm 2.4.4; §3.7, pp. 64–65 [unverified page].
-/

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "dSq" => gnatSqO ha0 hb0

/-! ### $\mu_{\mathrm{SL}_1}$ for every quaternion algebra -/

/-- **$\mu_{\mathrm{SL}_1}$ is right invariant** for every quaternion algebra ($\tau(\mathrm{SL}_1) < \infty$). -/
theorem isMulRightInvariant_muSL1_any :
    (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)).IsMulRightInvariant :=
  isMulRightInvariant_muSL1_of_lt_top _ _ _ _ (covolume_muSL1_ne_top a b ha0 hb0)

/-- **Conjugation by any unit of $D\otimes\mathbb A$ preserves `muSL1N`**, for every quaternion algebra. -/
theorem map_adK_muSL1N_any (m : (QuatAdele (a : F) (b : F))ˣ) :
    (muSL1N ha0 hb0).map (NormalFib.adK (nrdHom (a : F) (b : F)) m) = muSL1N ha0 hb0 := by
  have := isMulRightInvariant_muSL1_any ha0 hb0
  rw [adK_nrdHom_eq, muSL1N]
  have h1 : Measurable (kerNrdEquiv (a : F) (b : F)) := (kerNrdEquiv _ _).continuous.measurable
  have h2 : Measurable (kerNrdEquiv (a : F) (b : F)).symm := (kerNrdEquiv _ _).symm.continuous.measurable
  have h3 := NormalFib.measurable_adK (nrdOne (a : F) (b : F)) (quatSplit (a : F) (b : F) m).1
  rw [Measure.map_map (h2.comp (h3.comp h1)) h2]
  have : ((kerNrdEquiv (a : F) (b : F)).symm ∘ NormalFib.adK (nrdOne (a : F) (b : F)) (quatSplit _ _ m).1 ∘
      kerNrdEquiv (a : F) (b : F)) ∘ (kerNrdEquiv (a : F) (b : F)).symm =
      (kerNrdEquiv (a : F) (b : F)).symm ∘ NormalFib.adK (nrdOne (a : F) (b : F)) (quatSplit _ _ m).1 := by
    funext y; simp
  rw [this, ← Measure.map_map h2 h3, map_adK_muSL1_of_isMulRightInvariant]

/-- **$\tau(\mathrm{SL}_1(D)) = 1$ on $\ker\operatorname{nrd}$**, for every quaternion algebra (`tauSL1EqOne`). -/
theorem covolume_muSL1N_any :
    covolume ((quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) = 1 := by
  have hH := isHaarMeasure_muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (F := F)
    (by simpa using ha0) (by simpa using hb0)
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := (a : F)) (b := (b : F))
  have hFD : IsExactFD (Γ := (quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      ((kerNrdEquiv (a : F) (b : F)).symm '' DK) :=
    isExactFD_image_mulEquiv' (kerNrdEquiv (a : F) (b : F)).symm.toMulEquiv
      (kerNrdEquiv (a : F) (b : F)).continuous.measurable _ _
      (fun y => by
        rw [← kerNrdEquiv_mem_iff]
        change (kerNrdEquiv _ _) ((kerNrdEquiv _ _).symm y) ∈ _ ↔ _
        rw [ContinuousMulEquiv.apply_symm_apply]) hDK
  have : SMulInvariantMeasure ((quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker)
      (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  have hm : Measurable (kerNrdEquiv (a : F) (b : F)).symm := (kerNrdEquiv _ _).symm.continuous.measurable
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have h1 := covolume_SL1_eq (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hDK
  rw [(tauSL1EqOne a b).covolume_eq_one ha0 hb0] at h1
  rw [(hFD.isFundamentalDomain _).covolume_eq_volume, muSL1N, Measure.map_apply hm hFD.1,
    (kerNrdEquiv (a : F) (b : F)).symm.injective.preimage_image]
  exact h1.symm

theorem map_adK_muSq_any (m : (QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) :
    (muSq ha0 hb0).map (NormalFib.adK (nuSq ha0 hb0) m) = muSq ha0 hb0 := by
  have hk : Measurable (kerSqEquiv ha0 hb0) := (kerSqEquiv ha0 hb0).continuous.measurable
  have hks : Measurable (kerSqEquiv ha0 hb0).symm := (kerSqEquiv ha0 hb0).symm.continuous.measurable
  have h1 := NormalFib.measurable_adK (nrdHom (a : F) (b : F)) m.1
  have h2 := NormalFib.measurable_adK (nrdHom (a : F) (b : F)) m.2
  rw [adK_sq_eq, muSq, Measure.map_map (hks.comp ((h1.prodMap h2).comp hk)) hks]
  have : ((kerSqEquiv ha0 hb0).symm ∘ Prod.map (NormalFib.adK (nrdHom (a : F) (b : F)) m.1)
      (NormalFib.adK (nrdHom (a : F) (b : F)) m.2) ∘ kerSqEquiv ha0 hb0) ∘ (kerSqEquiv ha0 hb0).symm =
      (kerSqEquiv ha0 hb0).symm ∘ Prod.map (NormalFib.adK (nrdHom (a : F) (b : F)) m.1)
        (NormalFib.adK (nrdHom (a : F) (b : F)) m.2) := by
    funext y; simp
  rw [this, ← Measure.map_map hks (h1.prodMap h2), ← Measure.map_prod_map _ _ h1 h2,
    map_adK_muSL1N_any ha0 hb0, map_adK_muSL1N_any ha0 hb0]

set_option maxHeartbeats 1600000 in
/-- **$\tau(\mathrm{SL}_1(D)\times\mathrm{SL}_1(D)) = 1$** for every quaternion algebra. -/
theorem covolume_muSq_any :
    covolume ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (nuSq ha0 hb0).ker (muSq ha0 hb0) = 1 := by
  set Γ1 := (quatUnitsSub (a : F) (b : F)).subgroupOf (nrdHom (a : F) (b : F)).ker
  obtain ⟨D1, hD1m, hD1⟩ := exists_measurableSet_forall_existsUnique_smul_mem Γ1
  have hμ1 : muSL1N ha0 hb0 D1 = 1 := by
    have : SMulInvariantMeasure Γ1 (nrdHom (a : F) (b : F)).ker (muSL1N ha0 hb0) :=
      ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
    rw [← covolume_muSL1N_any ha0 hb0, ((IsExactFD.isFundamentalDomain ⟨hD1m, hD1⟩) _).covolume_eq_volume]
  set e := (kerSqEquiv ha0 hb0).symm
  have hmem : ∀ y, e y ∈ (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker ↔ y ∈ Γ1.prod Γ1 := by
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_prod, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hFDprod : IsExactFD (Γ := Γ1.prod Γ1) (D1 ×ˢ D1) := isExactFD_prod ⟨hD1m, hD1⟩ ⟨hD1m, hD1⟩
  have hFD : IsExactFD (Γ := (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (e '' (D1 ×ˢ D1)) :=
    isExactFD_image_mulEquiv' e.toMulEquiv (kerSqEquiv ha0 hb0).continuous.measurable _ _ hmem hFDprod
  have : Countable ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) :=
    Injective.countable (f := fun x : (dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker =>
      (⟨((x : (nuSq ha0 hb0).ker) : _ × _), x.2⟩ : (dSq).ΓM))
      fun x y h => by have h' := congrArg Subtype.val h; exact Subtype.ext (Subtype.ext h')
  have : SMulInvariantMeasure ((dSq).ΓM.subgroupOf (nuSq ha0 hb0).ker) (nuSq ha0 hb0).ker
      (muSq ha0 hb0) := ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  have hks : Measurable e := e.continuous.measurable
  rw [(hFD.isFundamentalDomain _).covolume_eq_volume, muSq, Measure.map_apply hks hFD.1,
    e.injective.preimage_image, Measure.prod_prod, hμ1, one_mul]

/-- **For every quaternion algebra: $\operatorname{vol}(P(F)\backslash P(\mathbb A),\mu_P) = 2$** for the square model
$P = G^\natural(\mathbb A)/\mathbb A^\times$ ($= SO(D,\operatorname{nrd})(\mathbb A)$), every $D = \mathbb H[F,a,b]$ (division or split) over every
number field. Unconditional; generalizes `covolume_gnatSq` (which assumed a division algebra). -/
@[kb "weil1982" "§3.7, pp. 64-65 (m = 4, square discriminant) [unverified page]; §3.2, p. 43 (centre)"]
theorem covolume_gnatSq_any :
    covolume (dSq).gamP (dSq).P ((dSq).muP (muSq ha0 hb0)) = 2 := by
  have h := (dSq).covolume_muP (muSq ha0 hb0) (gnatSq_hsΓ _ _) (gnatSq_heich _ _) (gnatSq_hsign _ _)
    (map_adK_muSq_any ha0 hb0) (covolume_muSq_any ha0 hb0)
  rw [h, mul_one]

/-! ### The fibration along $\pi$ for open sets -/

namespace GnatData

variable {k : Type} [Field k] [NumberField k] {M T : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  (d : GnatData k M T) (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]

/-- **Along $\pi$, for an open set**: for an open $S_0\subseteq G^\natural$ and $S = \{g\in S_0 : p(g)\in B\}$, if
$\mathrm{tamIdeles}\{u : g\,z(u)\in S_0,\ p(g)u^2\in B\} = c$ for all $g\in S_0$, then $\mu_{G^\natural}(S) = c\,\mu_P(\pi(S_0))$. -/
theorem muG_eq_mul_muP_set (S₀ : Set d.G) (hS₀ : IsOpen S₀) {B : Set (Adeles k)ˣ}
    (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ g ∈ S₀, tamIdeles k {u | g * d.zHom u ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 * u ^ 2 ∈ B} = c) :
    d.muG μSν {g | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} = c * d.muP μSν (d.π '' S₀) := by
  have hopen : IsOpen (d.π '' S₀) := QuotientGroup.isOpenMap_coe _ hS₀
  have hS : MeasurableSet {g : d.G | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} :=
    hS₀.measurableSet.inter (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  rw [← d.fibMeas_muP μSν]
  refine fibMeas_apply_of_kern _ _ d.measurable_π _ _ hS hopen.measurableSet c ?_ ?_
  · rintro q ⟨g, hg, rfl⟩
    refine ⟨g, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _)), ← hc g hg]
    rfl
  · intro g hg
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _))]
    convert measure_empty (μ := tamIdeles k)
    ext u
    simp only [mem_preimage, mem_empty_iff_false, iff_false, GnatData.coe_kerZEquiv, mem_ofPred_eq]
    rintro ⟨h1, -⟩
    apply hg
    refine ⟨_, h1, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 (d.mem_ker_π.2 ⟨u, rfl⟩), mul_one]

end GnatData

/-! ### The set $S_0$ -/

section S0Set

variable (H E : Set (QuatAdele (a : F) (b : F))ˣ)

/-- **$S_0 = \{(\alpha,\beta,u) : \beta\in H,\ \alpha\beta^{-1}\in E\}$** for sets $H, E$. -/
def sqS0Set : Set (dSq).G := {g | gβ ha0 hb0 g ∈ H ∧ gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹ ∈ E}

theorem isOpen_sqS0Set (hHo : IsOpen H) (hEo : IsOpen E) : IsOpen (sqS0Set ha0 hb0 H E) := by
  have hβ : Continuous (gβ ha0 hb0) := continuous_snd.comp (continuous_fst.comp continuous_subtype_val)
  have hα : Continuous (gα ha0 hb0) := continuous_fst.comp (continuous_fst.comp continuous_subtype_val)
  exact (hHo.preimage hβ).inter (hEo.preimage (hα.mul hβ.inv))

/-- The set $S = \{g\in S_0 : u\in B\}$. -/
def sqSSet (B : Set (Adeles F)ˣ) : Set (dSq).G := {g | g ∈ sqS0Set ha0 hb0 H E ∧ gu ha0 hb0 g ∈ B}

theorem measurableSet_sqSSet (hHo : IsOpen H) (hEo : IsOpen E) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) :
    MeasurableSet (sqSSet ha0 hb0 H E B) :=
  (isOpen_sqS0Set ha0 hb0 H E hHo hEo).measurableSet.inter
    (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)

theorem gβ_mul_zHom (g : (dSq).G) (u : (Adeles F)ˣ) :
    gβ ha0 hb0 (g * (dSq).zHom u) = gβ ha0 hb0 g * quatScalar _ _ u := rfl

theorem gα_mul_zHom (g : (dSq).G) (u : (Adeles F)ˣ) :
    gα ha0 hb0 (g * (dSq).zHom u) = gα ha0 hb0 g * quatScalar _ _ u := rfl

theorem gu_mul_zHom (g : (dSq).G) (u : (Adeles F)ˣ) :
    gu ha0 hb0 (g * (dSq).zHom u) = gu ha0 hb0 g * u ^ 2 := rfl

/-- $g\,z(u)\in S_0\iff\beta u\in H$ for $g\in S_0$ (the scalars commute and cancel in $\alpha\beta^{-1}$). -/
theorem mul_zHom_mem_sqS0Set {g : (dSq).G} (hg : g ∈ sqS0Set ha0 hb0 H E) (u : (Adeles F)ˣ) :
    g * (dSq).zHom u ∈ sqS0Set ha0 hb0 H E ↔ gβ ha0 hb0 g * quatScalar _ _ u ∈ H := by
  change gβ ha0 hb0 (g * (dSq).zHom u) ∈ H ∧
    gα ha0 hb0 (g * (dSq).zHom u) * (gβ ha0 hb0 (g * (dSq).zHom u))⁻¹ ∈ E ↔ _
  rw [gβ_mul_zHom, gα_mul_zHom]
  have e : gα ha0 hb0 g * quatScalar _ _ u * (gβ ha0 hb0 g * quatScalar _ _ u)⁻¹ =
      gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_assoc (gα ha0 hb0 g), mul_inv_cancel, mul_one]
  rw [e]
  exact and_iff_left hg.2

/-- **Along $\pi$ for sets**: $\mu_{G^\natural}(S) = c\,\mu_P(\pi(S_0))$. -/
theorem muG_sqSSet_eq_muP (μSν : Measure ((dSq).ν : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) →*
      (Adeles F)ˣ × (Adeles F)ˣ).ker) [μSν.IsHaarMeasure]
    (hHo : IsOpen H) (hEo : IsOpen E) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | β * quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    (dSq).muG μSν (sqSSet ha0 hb0 H E B) = c * (dSq).muP μSν ((dSq).π '' (sqS0Set ha0 hb0 H E)) := by
  refine (dSq).muG_eq_mul_muP_set μSν (sqS0Set ha0 hb0 H E) (isOpen_sqS0Set ha0 hb0 H E hHo hEo) hB c
    fun g hg => ?_
  rw [← hc _ hg.1]
  congr 1
  ext u
  simp only [mem_ofPred_eq]
  rw [mul_zHom_mem_sqS0Set ha0 hb0 H E hg, show (g : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) ×
    (Adeles F)ˣ).2 = gu ha0 hb0 g from rfl, ← nrd_gβ, mul_comm]

end S0Set

/-! ### The $\mathrm{SL}_1\times\mathrm{SL}_1$ fibre, for sets and every quaternion algebra -/

theorem muSL1N_preimage_mul_right_any (w : (nrdHom (a : F) (b : F)).ker) {A : Set (nrdHom (a : F) (b : F)).ker}
    (hA : MeasurableSet A) :
    muSL1N ha0 hb0 ((fun z : (nrdHom (a : F) (b : F)).ker => z * w) ⁻¹' A) = muSL1N ha0 hb0 A := by
  have hrw : (fun z : (nrdHom (a : F) (b : F)).ker => z * w) = (fun z : (nrdHom (a : F) (b : F)).ker => w * z) ∘
      NormalFib.adK (nrdHom (a : F) (b : F)) ((w : (QuatAdele (a : F) (b : F))ˣ)⁻¹) := by
    funext z; apply Subtype.ext; simp only [comp_apply, Subgroup.coe_mul, NormalFib.coe_adK, inv_inv]; group
  rw [hrw, preimage_comp, ← Measure.map_apply (NormalFib.measurable_adK _ _)
    (hA.preimage (measurable_const_mul w)), map_adK_muSL1N_any ha0 hb0, measure_preimage_mul]

set_option maxHeartbeats 1600000 in
/-- **The fibre of the $p$-fibration, for sets**: for $\operatorname{nrd}\alpha = \operatorname{nrd}\beta$,
$(\mu\times\mu)\{(x,y) : \beta y\in H,\ \alpha x(\beta y)^{-1}\in E\} = \mu(E\cap\mathrm{SL}_1)\cdot\mu\{y : \beta y\in H\}$. -/
theorem muSL1N_prod_pair_set (α β : (QuatAdele (a : F) (b : F))ˣ) (hαβ : nrdUnit α = nrdUnit β)
    (H E : Set (QuatAdele (a : F) (b : F))ˣ) (hHm : MeasurableSet H) (hEm : MeasurableSet E) :
    ((muSL1N ha0 hb0).prod (muSL1N ha0 hb0))
        {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker | β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
          α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        muSL1N ha0 hb0 {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} := by
  have hval : Measurable (fun k : (nrdHom (a : F) (b : F)).ker => (k : (QuatAdele (a : F) (b : F))ˣ)) :=
    measurable_subtype_coe
  have hT : MeasurableSet {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
      β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
      α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} :=
    (hHm.preimage ((measurable_const_mul β).comp (hval.comp measurable_snd))).inter
      (hEm.preimage ((((measurable_const_mul α).comp (hval.comp measurable_fst)).mul
        ((measurable_const_mul β).comp (hval.comp measurable_snd)).inv)))
  have hEk : MeasurableSet {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} :=
    hEm.preimage hval
  rw [Measure.prod_apply_symm hT]
  have hinner : ∀ y : (nrdHom (a : F) (b : F)).ker, muSL1N ha0 hb0 ((fun x => (x, y)) ⁻¹'
      {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
        β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
        α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E}) =
      {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H}.indicator
        (fun _ => muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E}) y := by
    intro y
    by_cases hy : β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H
    · rw [indicator_of_mem (show y ∈ {y : (nrdHom (a : F) (b : F)).ker |
        β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} from hy)]
      have hw : α * (y : (QuatAdele (a : F) (b : F))ˣ)⁻¹ * β⁻¹ ∈ (nrdHom (a : F) (b : F)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 y.2, inv_one, mul_one]
        change nrdUnit α * (nrdUnit β)⁻¹ = 1
        rw [hαβ, mul_inv_cancel]
      obtain ⟨w, hw'⟩ : ∃ w : (nrdHom (a : F) (b : F)).ker,
          (w : (QuatAdele (a : F) (b : F))ˣ) = α * (y : (QuatAdele (a : F) (b : F))ˣ)⁻¹ * β⁻¹ := ⟨⟨_, hw⟩, rfl⟩
      have hset : (fun x => (x, y)) ⁻¹' {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
          β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
          α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} =
          NormalFib.adK (nrdHom (a : F) (b : F)) α ⁻¹'
            ((fun z : (nrdHom (a : F) (b : F)).ker => z * w) ⁻¹'
              {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E}) := by
        ext x
        have e : ((NormalFib.adK (nrdHom (a : F) (b : F)) α x * w : (nrdHom (a : F) (b : F)).ker) :
            (QuatAdele (a : F) (b : F))ˣ) =
            α * (x : (QuatAdele (a : F) (b : F))ˣ) * (β * (y : (QuatAdele (a : F) (b : F))ˣ))⁻¹ := by
          rw [Subgroup.coe_mul, NormalFib.coe_adK, hw']; group
        change (β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧ _) ↔ _
        rw [mem_preimage, mem_preimage, mem_ofPred_eq, e]
        exact and_iff_right hy
      rw [hset, ← Measure.map_apply (NormalFib.measurable_adK _ _) (hEk.preimage (measurable_mul_const w)),
        map_adK_muSL1N_any ha0 hb0, muSL1N_preimage_mul_right_any ha0 hb0 w hEk]
    · rw [indicator_of_notMem (show y ∉ {y : (nrdHom (a : F) (b : F)).ker |
        β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} from hy)]
      convert measure_empty (μ := muSL1N ha0 hb0)
      ext x; simp [hy]
  have hHy : MeasurableSet {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} :=
    hHm.preimage ((measurable_const_mul β).comp hval)
  rw [lintegral_congr hinner, lintegral_indicator_const hHy, mul_comm]

/-! ### The fibrations along $p$ and along $(D\otimes\mathbb A)^\times\to PD^\times(\mathbb A)$, for sets -/

section ResultSet

variable (H E : Set (QuatAdele (a : F) (b : F))ˣ)

set_option maxHeartbeats 1600000 in
/-- **Along $p$, for sets**: $\mu_{G^\natural}(S) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mathrm{tamQuat}(X)$,
$X = \{\beta\in H : \operatorname{nrd}\beta\in B\}$ (`sqX`). -/
theorem muG_sqSSet_eq_tamQuat (hHo : IsOpen H) (hEo : IsOpen E) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) :
    (dSq).muG (muSq ha0 hb0) (sqSSet ha0 hb0 H E B) =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        tamQuat (a : F) (b : F) {β | β ∈ H ∧ nrdUnit β ∈ B} := by
  have ha' : (a : F) ≠ 0 := by simpa using ha0
  have hb' : (b : F) ≠ 0 := by simpa using hb0
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  set cE := muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E}
  set X : Set (QuatAdele (a : F) (b : F))ˣ := {β | β ∈ H ∧ nrdUnit β ∈ B}
  have hXm : MeasurableSet X := hHo.measurableSet.inter (hB.preimage continuous_nrdHom.measurable)
  have hS := measurableSet_sqSSet ha0 hb0 H E hHo hEo hB
  rw [(dSq).muG_apply_of_fibK (muSq ha0 hb0) _ hS (fun c => cE * NormalFib.kern (nrdPos (a : F) (b : F))
    (nrdPos_surjective ha' hb') (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb') c X)]
  · refine (lintegral_const_mul cE ?_).trans ?_
    · exact NormalFib.measurable_kern_apply _ _ measurable_nrdPos _ hXm
    congr 1
    exact (NormalFib.fibMeas_apply _ _ measurable_nrdPos (muPosA (a : F) (b : F)) _ hXm).symm.trans
      (congrArg (fun μ : Measure (QuatAdele (a : F) (b : F))ˣ => μ X)
        (fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'))
  · intro g
    have hpg : (dSq).p g = nrdPos (a : F) (b : F) (gβ ha0 hb0 g) := Subtype.ext (nrd_gβ ha0 hb0 g).symm
    have hmS : MeasurableSet ((dSq).kerSEquiv.symm ⁻¹'
        ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqSSet ha0 hb0 H E B)) :=
      (hS.preimage (NormalFib.measurable_mul_val _ _)).preimage
        (map_continuous (dSq).kerSEquiv.symm).measurable
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muS, Measure.map_apply
      (map_continuous (dSq).kerSEquiv.symm).measurable (hS.preimage (NormalFib.measurable_mul_val _ _)),
      muSq, Measure.map_apply (map_continuous (kerSqEquiv ha0 hb0).symm).measurable hmS, hpg,
      NormalFib.kern_apply_N, NormalFib.fibK_apply _ _ _ hXm, muSL1P,
      Measure.map_apply (map_continuous (kerPosEquiv (a : F) (b : F)).symm).measurable
        (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    by_cases hu : gu ha0 hb0 g ∈ B
    · have hset : (kerSqEquiv ha0 hb0).symm ⁻¹' ((dSq).kerSEquiv.symm ⁻¹'
          ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqSSet ha0 hb0 H E B)) =
          {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
            gβ ha0 hb0 g * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
            gα ha0 hb0 g * (p.1 : (QuatAdele (a : F) (b : F))ˣ) *
              (gβ ha0 hb0 g * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} := by
        ext p
        change (_ ∧ _) ∧ gu ha0 hb0 g * 1 ∈ B ↔ _
        rw [mul_one]
        exact and_iff_left hu
      rw [hset, muSL1N_prod_pair_set ha0 hb0 _ _ ((nrd_gα ha0 hb0 g).trans (nrd_gβ ha0 hb0 g).symm) _ E
        hHo.measurableSet hEo.measurableSet]
      congr 1
      refine (muSL1N_eq_muSL1 ha0 hb0 ((fun x => gβ ha0 hb0 g * x) ⁻¹' H)
        (hHo.measurableSet.preimage (measurable_const_mul _))).trans ?_
      congr 1
      ext z
      change gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ H ↔
        gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
          nrdUnit (gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ)) ∈ B
      rw [nrdUnit_mul, mem_SL1A.1 z.2, mul_one, nrd_gβ]
      exact (and_iff_left hu).symm
    · have h1 : (kerSqEquiv ha0 hb0).symm ⁻¹' ((dSq).kerSEquiv.symm ⁻¹'
          ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqSSet ha0 hb0 H E B)) = ∅ := by
        ext p
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨-, h⟩
        change gu ha0 hb0 g * 1 ∈ B at h
        rw [mul_one] at h; exact hu h
      have h2 : (kerPosEquiv (a : F) (b : F)).symm ⁻¹' ((fun k : (nrdPos (a : F) (b : F)).ker =>
          gβ ha0 hb0 g * (k : (QuatAdele (a : F) (b : F))ˣ)) ⁻¹' X) = ∅ := by
        ext z
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨-, h⟩
        change nrdUnit (gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ)) ∈ B at h
        rw [nrdUnit_mul, mem_SL1A.1 z.2, mul_one, nrd_gβ] at h
        exact hu h
      rw [h1, h2, measure_empty, measure_empty, mul_zero]

set_option maxHeartbeats 1600000 in
/-- **Along $(D\otimes\mathbb A)^\times\to PD^\times(\mathbb A)$, for sets**: $\mathrm{tamQuat}(X) = c\,\mu_{PD}(\operatorname{pd}(H))$. -/
theorem tamQuat_sqXSet (hHo : IsOpen H) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | β * quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    tamQuat (a : F) (b : F) {β | β ∈ H ∧ nrdUnit β ∈ B} =
      c * muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
        (pdMk (a : F) (b : F) '' H) := by
  set X : Set (QuatAdele (a : F) (b : F))ˣ := {β | β ∈ H ∧ nrdUnit β ∈ B}
  have hXm : MeasurableSet X := hHo.measurableSet.inter (hB.preimage continuous_nrdHom.measurable)
  have hopen : IsOpen (pdMk (a : F) (b : F) '' H) := QuotientGroup.isOpenMap_coe _ hHo
  rw [← fibMeas_muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)]
  refine fibMeas_apply_of_kern _ _ (measurable_pdMk _ _) _ _ hXm hopen.measurableSet c ?_ ?_
  · rintro q ⟨β, hβ, rfl⟩
    refine ⟨β, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hXm, muZ, Measure.map_apply (map_continuous (kerEquiv _ _)).measurable
      (hXm.preimage (NormalFib.measurable_mul_val _ _)), ← hc β hβ]
    congr 1
    ext u
    simp only [mem_preimage, coe_kerEquiv, X, mem_ofPred_eq]
    rw [nrdUnit_mul, nrdUnit_quatScalar, mul_comm (nrdUnit β)]
  · intro β hβ
    rw [NormalFib.fibK_apply _ _ _ hXm, muZ, Measure.map_apply (map_continuous (kerEquiv _ _)).measurable
      (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    convert measure_empty (μ := tamIdeles F)
    ext u
    simp only [mem_preimage, coe_kerEquiv, X, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, -⟩
    apply hβ
    refine ⟨_, h1, ?_⟩
    rw [map_mul, (mem_ker_pdMk _ _).2 ⟨u, rfl⟩ |> MonoidHom.mem_ker.1, mul_one]

/-- **$\mu_P(\pi(S_0)) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mu_{PD}(\operatorname{pd}(H))$ for open sets $H, E$** and every
quaternion algebra (the measure form of $P\cong\mathrm{SL}_1(\mathbb A)\rtimes PD^\times(\mathbb A)$). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.7, p. 65 [unverified page]"]
theorem muP_sqS0Set (hHo : IsOpen H) (hEo : IsOpen E) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | β * quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    (dSq).muP (muSq ha0 hb0) ((dSq).π '' (sqS0Set ha0 hb0 H E)) =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
          (pdMk (a : F) (b : F) '' H) := by
  have h1 := muG_sqSSet_eq_muP ha0 hb0 H E (muSq ha0 hb0) hHo hEo hB c hc
  rw [muG_sqSSet_eq_tamQuat ha0 hb0 H E hHo hEo hB, tamQuat_sqXSet ha0 hb0 H hHo hB c hc] at h1
  refine (ENNReal.mul_right_inj hc0 hct).1 ?_
  rw [← h1]; ring

end ResultSet

end

end QuadFormsKB.Tamagawa.Measure.Weil
