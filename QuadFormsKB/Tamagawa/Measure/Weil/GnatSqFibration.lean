/-
# $\mu_P(\pi(S_0)) = \mu_{\mathrm{SL}_1}(E^1)\cdot\mu_{PD}(\bar H)$ for the square model

**Layer:** a number field $F$, $D = (a,b)_F$ a division algebra ($a, b\in\mathcal O_F\setminus0$), the square model
$G^\natural = \{(\alpha,\beta,u) : \operatorname{nrd}\alpha = \operatorname{nrd}\beta = u\}$ (`gnatSqO`), $P = G^\natural/Z$.

Data: open subgroups $H, E\le(D\otimes\mathbb A)^\times$ with $H$ normalizing $E$, a measurable set $B\subseteq\mathbb A^\times$ and
$c\in(0,\infty)$ with $\mathrm{tamIdeles}\{u : u\in H,\ u^2\operatorname{nrd}\beta\in B\} = c$ for every $\beta\in H$ (the scalar $u$ read
in $D\otimes\mathbb A$). Put $S_0 = \{(\alpha,\beta,u) : \beta\in H,\ \alpha\beta^{-1}\in E\}$ (`sqS0`, an open subgroup).

**`muP_sqS0`**: $\mu_P(\pi(S_0)) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mu_{PD}(\operatorname{pd}(H))$.

*Proof* (Weil's two fibrations): compute $\mu_{G^\natural}(S)$, $S = \{g\in S_0 : u\in B\}$,
* along $\pi$ (fibre $Z\cong\mathbb A^\times$, `fibMeas_muP`): $\mu_{G^\natural}(S) = c\,\mu_P(\pi(S_0))$;
* along $p$ (fibre $\mathrm{SL}_1\times\mathrm{SL}_1$): the fibre over $u = \operatorname{nrd}\beta$ is
  $\{(x,y) : \beta y\in H,\ \alpha xy^{-1}\beta^{-1}\in E\}$, of measure $\mu(E\cap\mathrm{SL}_1)\,\mu\{y : \beta y\in H\}$ (conjugation
  invariance of $\mu_{\mathrm{SL}_1}$, `map_adK_muSL1N`), so by the reduced-norm fibration of `tamQuat` (`fibMeas_nrdPos`)
  $\mu_{G^\natural}(S) = \mu(E\cap\mathrm{SL}_1)\cdot\mathrm{tamQuat}(X)$, $X = \{\beta\in H : \operatorname{nrd}\beta\in B\}$;
* along $(D\otimes\mathbb A)^\times\to PD^\times(\mathbb A)$ (fibre $\mathbb A^\times$, `fibMeas_muPD`):
  $\mathrm{tamQuat}(X) = c\,\mu_{PD}(\operatorname{pd}(H))$.
The constant $c$ cancels. This is $P\cong\mathrm{SL}_1(\mathbb A)\rtimes PD^\times(\mathbb A)$ at the level of measures.

Source: Weil 1982, §2.4, Thm 2.4.4; §3.7, p. 65 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.QuatNrdFibration
import QuadFormsKB.Tamagawa.Measure.Weil.GnatSqGlobal

open MeasureTheory Measure Set Function Topology NumberField
open scoped ENNReal NNReal Quaternion

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-! ### A fibred measure with constant fibres -/

section Generic

variable {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q] [StandardBorelSpace G]
  [MeasurableSpace.CountablySeparated Q]

/-- If the fibre measures of $s$ are $c$ over $X$ and $0$ elsewhere, then $\nu(s) = c\,\mu_Q(X)$. -/
theorem fibMeas_apply_of_kern (N : G →* Q) (hN : Surjective N) (hNm : Measurable N) (μQ : Measure Q)
    (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] {s : Set G} (hs : MeasurableSet s)
    {X : Set Q} (hX : MeasurableSet X) (c : ℝ≥0∞)
    (hk1 : ∀ q ∈ X, ∃ g, N g = q ∧ NormalFib.fibK N μK g s = c)
    (hk0 : ∀ g, N g ∉ X → NormalFib.fibK N μK g s = 0) :
    NormalFib.fibMeas N hN μQ μK s = c * μQ X := by
  rw [NormalFib.fibMeas_apply N hN hNm μQ μK hs]
  have : ∀ q, NormalFib.kern N hN μK q s = X.indicator (fun _ => c) q := fun q => by
    by_cases hq : q ∈ X
    · obtain ⟨g, rfl, hg⟩ := hk1 q hq
      rw [NormalFib.kern_apply_N, hg, indicator_of_mem hq]
    · obtain ⟨g, rfl⟩ := hN q
      rw [NormalFib.kern_apply_N, hk0 g hq, indicator_of_notMem hq]
  rw [lintegral_congr this, lintegral_indicator_const hX]

end Generic

/-! ### The two fibrations of $\mu_{G^\natural}$, abstractly -/

namespace GnatData

variable {k : Type} [Field k] [NumberField k] {M T : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  (d : GnatData k M T) (μSν : Measure (d.ν : M →* T).ker) [μSν.IsHaarMeasure]

/-- **Along $\pi$** (fibre $Z\cong\mathbb A^\times$): for an open subgroup $S_0\le G^\natural$ and $S = \{g\in S_0 : p(g)\in B\}$,
if $\mathrm{tamIdeles}\{u : z(u)\in S_0,\ p(g)u^2\in B\} = c$ for all $g\in S_0$, then $\mu_{G^\natural}(S) = c\,\mu_P(\pi(S_0))$. -/
theorem muG_eq_mul_muP (S₀ : Subgroup d.G) (hS₀ : IsOpen (S₀ : Set d.G)) {B : Set (Adeles k)ˣ}
    (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ g ∈ S₀, tamIdeles k {u | d.zHom u ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 * u ^ 2 ∈ B} = c) :
    d.muG μSν {g | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} = c * d.muP μSν (d.π '' S₀) := by
  have hopen : IsOpen (d.π '' (S₀ : Set d.G)) := QuotientGroup.isOpenMap_coe _ hS₀
  have hS : MeasurableSet {g : d.G | g ∈ S₀ ∧ (g : M × (Adeles k)ˣ).2 ∈ B} :=
    hS₀.measurableSet.inter (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)
  rw [← d.fibMeas_muP μSν]
  refine fibMeas_apply_of_kern _ _ d.measurable_π _ _ hS hopen.measurableSet c ?_ ?_
  · rintro q ⟨g, hg, rfl⟩
    refine ⟨g, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _)), ← hc g hg]
    congr 1
    ext u
    simp only [mem_preimage, mem_setOf_eq, GnatData.coe_kerZEquiv]
    rw [S₀.mul_mem_cancel_left hg]
    rfl
  · intro g hg
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muZ, Measure.map_apply (map_continuous d.kerZEquiv).measurable
      (hS.preimage (NormalFib.measurable_mul_val _ _))]
    convert measure_empty (μ := tamIdeles k)
    ext u
    simp only [mem_preimage, mem_empty_iff_false, iff_false, GnatData.coe_kerZEquiv, mem_setOf_eq]
    rintro ⟨h1, -⟩
    apply hg
    refine ⟨_, h1, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 (d.mem_ker_π.2 ⟨u, rfl⟩), mul_one]

/-- **Along $p$** (fibre $\ker\nu$): if the fibre measure of $S$ over $g$ is $f(p(g))$, then
$\mu_{G^\natural}(S) = \int_{A_+}f\,d\mu_{A_+}$. -/
theorem muG_apply_of_fibK (S : Set d.G) (hS : MeasurableSet S) (f : d.Apos → ℝ≥0∞)
    (hk : ∀ g, NormalFib.fibK d.p (d.muS μSν) g S = f (d.p g)) :
    d.muG μSν S = ∫⁻ a, f a ∂d.muA := by
  rw [muG, NormalFib.fibMeas_apply _ _ d.measurable_p _ _ hS]
  refine lintegral_congr fun a => ?_
  obtain ⟨g, rfl⟩ := d.p_surjective a
  rw [NormalFib.kern_apply_N, hk]

end GnatData

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (ha0 : a ≠ 0) (hb0 : b ≠ 0)

local notation "dSq" => gnatSqO ha0 hb0

/-! ### The open subgroup $S_0$ -/

section S0

variable (H E : Subgroup (QuatAdele (a : F) (b : F))ˣ) (hHE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E)

/-- The components of $g = (\alpha,\beta,u)\in G^\natural$. -/
abbrev gα (g : (dSq).G) : (QuatAdele (a : F) (b : F))ˣ := ((g : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) × (Adeles F)ˣ).1).1
abbrev gβ (g : (dSq).G) : (QuatAdele (a : F) (b : F))ˣ := ((g : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) × (Adeles F)ˣ).1).2
abbrev gu (g : (dSq).G) : (Adeles F)ˣ := (g : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) × (Adeles F)ˣ).2

theorem nrd_gβ (g : (dSq).G) : nrdUnit (gβ ha0 hb0 g) = gu ha0 hb0 g := congrArg Prod.snd g.2

theorem nrd_gα (g : (dSq).G) : nrdUnit (gα ha0 hb0 g) = gu ha0 hb0 g := congrArg Prod.fst g.2

theorem gα_mul (g h : (dSq).G) : gα ha0 hb0 (g * h) = gα ha0 hb0 g * gα ha0 hb0 h := rfl
theorem gβ_mul (g h : (dSq).G) : gβ ha0 hb0 (g * h) = gβ ha0 hb0 g * gβ ha0 hb0 h := rfl
theorem gα_inv (g : (dSq).G) : gα ha0 hb0 g⁻¹ = (gα ha0 hb0 g)⁻¹ := rfl
theorem gβ_inv (g : (dSq).G) : gβ ha0 hb0 g⁻¹ = (gβ ha0 hb0 g)⁻¹ := rfl
theorem gα_one : gα ha0 hb0 (1 : (dSq).G) = 1 := rfl
theorem gβ_one : gβ ha0 hb0 (1 : (dSq).G) = 1 := rfl

include hHE in
/-- **$S_0 = \{(\alpha,\beta,u) : \beta\in H,\ \alpha\beta^{-1}\in E\}$**, a subgroup since $H$ normalizes $E$. -/
def sqS0 : Subgroup (dSq).G where
  carrier := {g | gβ ha0 hb0 g ∈ H ∧ gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹ ∈ E}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [gβ_one]; exact H.one_mem
    · rw [gα_one, gβ_one, inv_one, mul_one]; exact E.one_mem
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [gβ_mul]; exact H.mul_mem hg.1 hh.1
    · rw [gα_mul, gβ_mul]
      have := E.mul_mem hg.2 (hHE _ hg.1 _ hh.2)
      have e : gα ha0 hb0 g * gα ha0 hb0 h * (gβ ha0 hb0 g * gβ ha0 hb0 h)⁻¹ =
          gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹ * (gβ ha0 hb0 g * (gα ha0 hb0 h * (gβ ha0 hb0 h)⁻¹) *
            (gβ ha0 hb0 g)⁻¹) := by group
      rw [e]; exact this
  inv_mem' {g} hg := by
    refine ⟨?_, ?_⟩
    · rw [gβ_inv]; exact H.inv_mem hg.1
    · rw [gα_inv, gβ_inv]
      have := hHE _ (H.inv_mem hg.1) _ (E.inv_mem hg.2)
      have e : (gα ha0 hb0 g)⁻¹ * ((gβ ha0 hb0 g)⁻¹)⁻¹ =
          (gβ ha0 hb0 g)⁻¹ * (gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹)⁻¹ * ((gβ ha0 hb0 g)⁻¹)⁻¹ := by group
      rw [e]; exact this

theorem mem_sqS0 {g : (dSq).G} :
    g ∈ sqS0 ha0 hb0 H E hHE ↔ gβ ha0 hb0 g ∈ H ∧ gα ha0 hb0 g * (gβ ha0 hb0 g)⁻¹ ∈ E := Iff.rfl

theorem isOpen_sqS0 (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ)) (hEo : IsOpen (E : Set (QuatAdele (a : F) (b : F))ˣ)) :
    IsOpen (sqS0 ha0 hb0 H E hHE : Set (dSq).G) := by
  have hβ : Continuous (gβ ha0 hb0) := continuous_snd.comp (continuous_fst.comp continuous_subtype_val)
  have hα : Continuous (gα ha0 hb0) := continuous_fst.comp (continuous_fst.comp continuous_subtype_val)
  exact (hHo.preimage hβ).inter (hEo.preimage (hα.mul hβ.inv))

/-- The set $S = \{g\in S_0 : u\in B\}$. -/
def sqS (B : Set (Adeles F)ˣ) : Set (dSq).G := {g | g ∈ sqS0 ha0 hb0 H E hHE ∧ gu ha0 hb0 g ∈ B}

theorem measurableSet_sqS (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ)) (hEo : IsOpen (E : Set (QuatAdele (a : F) (b : F))ˣ)) {B : Set (Adeles F)ˣ}
    (hB : MeasurableSet B) : MeasurableSet (sqS ha0 hb0 H E hHE B) :=
  (isOpen_sqS0 ha0 hb0 H E hHE hHo hEo).measurableSet.inter
    (hB.preimage (continuous_snd.comp continuous_subtype_val).measurable)

/-- $z(u)\in S_0\iff u\in H$ (as a scalar of $D\otimes\mathbb A$). -/
theorem zHom_mem_sqS0 (u : (Adeles F)ˣ) :
    (dSq).zHom u ∈ sqS0 ha0 hb0 H E hHE ↔ quatScalar _ _ u ∈ H := by
  rw [mem_sqS0]
  change quatScalar _ _ u ∈ H ∧ quatScalar _ _ u * (quatScalar _ _ u)⁻¹ ∈ E ↔ _
  rw [mul_inv_cancel]; exact and_iff_left E.one_mem

/-! ### The fibration along $\pi$, concretely -/

include hHE in
/-- **Along $\pi$**: $\mu_{G^\natural}(S) = c\,\mu_P(\pi(S_0))$. -/
theorem muG_sqS_eq_muP (μSν : Measure ((dSq).ν : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) →*
      (Adeles F)ˣ × (Adeles F)ˣ).ker) [μSν.IsHaarMeasure]
    (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ)) (hEo : IsOpen (E : Set (QuatAdele (a : F) (b : F))ˣ))
    {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    (dSq).muG μSν (sqS ha0 hb0 H E hHE B) = c * (dSq).muP μSν ((dSq).π '' (sqS0 ha0 hb0 H E hHE)) := by
  refine (dSq).muG_eq_mul_muP μSν (sqS0 ha0 hb0 H E hHE) (isOpen_sqS0 ha0 hb0 H E hHE hHo hEo) hB c
    fun g hg => ?_
  rw [← hc _ hg.1]
  congr 1
  ext u
  simp only [mem_setOf_eq, zHom_mem_sqS0]
  rw [show (g : ((QuatAdele (a : F) (b : F))ˣ × (QuatAdele (a : F) (b : F))ˣ) × (Adeles F)ˣ).2 = gu ha0 hb0 g
    from rfl, ← nrd_gβ, mul_comm]

end S0

/-! ### The $\mathrm{SL}_1\times\mathrm{SL}_1$ fibre -/

section Pair

variable (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ)

include hdiv in
/-- `muSL1N` is right invariant (conjugation invariance + left invariance). -/
theorem muSL1N_preimage_mul_right (w : (nrdHom (a : F) (b : F)).ker) {A : Set (nrdHom (a : F) (b : F)).ker} (hA : MeasurableSet A) :
    muSL1N ha0 hb0 ((fun z : (nrdHom (a : F) (b : F)).ker => z * w) ⁻¹' A) = muSL1N ha0 hb0 A := by
  have hrw : (fun z : (nrdHom (a : F) (b : F)).ker => z * w) = (fun z : (nrdHom (a : F) (b : F)).ker => w * z) ∘ NormalFib.adK (nrdHom (a : F) (b : F))
      ((w : (QuatAdele (a : F) (b : F))ˣ)⁻¹) := by
    funext z; apply Subtype.ext; simp only [comp_apply, Subgroup.coe_mul, NormalFib.coe_adK, inv_inv]; group
  rw [hrw, preimage_comp, ← Measure.map_apply (NormalFib.measurable_adK _ _)
    (hA.preimage (measurable_const_mul w)), map_adK_muSL1N ha0 hb0 hdiv, measure_preimage_mul]

set_option maxHeartbeats 1600000 in
include hdiv in
/-- **The fibre of the $p$-fibration**: for $\operatorname{nrd}\alpha = \operatorname{nrd}\beta$ and a subgroup $E$,
$(\mu\times\mu)\{(x,y) : \beta y\in H,\ \alpha x(\beta y)^{-1}\in E\} = \mu(E\cap\mathrm{SL}_1)\cdot\mu\{y : \beta y\in H\}$. -/
theorem muSL1N_prod_pair (α β : (QuatAdele (a : F) (b : F))ˣ) (hαβ : nrdUnit α = nrdUnit β)
    (H E : Subgroup (QuatAdele (a : F) (b : F))ˣ)
    (hHm : MeasurableSet (H : Set (QuatAdele (a : F) (b : F))ˣ)) (hEm : MeasurableSet (E : Set (QuatAdele (a : F) (b : F))ˣ)) :
    ((muSL1N ha0 hb0).prod (muSL1N ha0 hb0))
        {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker | β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
          α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        muSL1N ha0 hb0 {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} := by
  have hval : Measurable (fun k : (nrdHom (a : F) (b : F)).ker => (k : (QuatAdele (a : F) (b : F))ˣ)) := measurable_subtype_coe
  have hT : MeasurableSet {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker | β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
      α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} :=
    (hHm.preimage ((measurable_const_mul β).comp (hval.comp measurable_snd))).inter
      (hEm.preimage ((((measurable_const_mul α).comp (hval.comp measurable_fst)).mul
        ((measurable_const_mul β).comp (hval.comp measurable_snd)).inv)))
  have hEk : MeasurableSet {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} := hEm.preimage hval
  rw [Measure.prod_apply_symm hT]
  have hinner : ∀ y : (nrdHom (a : F) (b : F)).ker, muSL1N ha0 hb0 ((fun x => (x, y)) ⁻¹' {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
      β * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
        α * (p.1 : (QuatAdele (a : F) (b : F))ˣ) * (β * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E}) =
      {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H}.indicator
        (fun _ => muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E}) y := by
    intro y
    by_cases hy : β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H
    · rw [indicator_of_mem (show y ∈ {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} from hy)]
      -- `w = α y⁻¹ β⁻¹ ∈ SL₁`
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
        rw [mem_preimage, mem_preimage, mem_setOf_eq, e]
        exact and_iff_right hy
      rw [hset, ← Measure.map_apply (NormalFib.measurable_adK _ _) (hEk.preimage (measurable_mul_const w)),
        map_adK_muSL1N ha0 hb0 hdiv, muSL1N_preimage_mul_right ha0 hb0 hdiv w hEk]
    · rw [indicator_of_notMem (show y ∉ {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} from hy)]
      convert measure_empty (μ := muSL1N ha0 hb0)
      ext x; simp [hy]
  have hHy : MeasurableSet {y : (nrdHom (a : F) (b : F)).ker | β * (y : (QuatAdele (a : F) (b : F))ˣ) ∈ H} :=
    hHm.preimage ((measurable_const_mul β).comp hval)
  rw [lintegral_congr hinner, lintegral_indicator_const hHy, mul_comm]

end Pair

/-! ### The fibrations along $p$ and along $(D\otimes\mathbb A)^\times\to PD^\times(\mathbb A)$, and the result -/

section Result

variable (H E : Subgroup (QuatAdele (a : F) (b : F))ˣ) (hHE : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E)
  (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ)

/-- $X = \{\beta\in H : \operatorname{nrd}\beta\in B\}$. -/
def sqX (B : Set (Adeles F)ˣ) : Set (QuatAdele (a : F) (b : F))ˣ := {β | β ∈ H ∧ nrdUnit β ∈ B}

theorem measurableSet_sqX (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ)) {B : Set (Adeles F)ˣ}
    (hB : MeasurableSet B) : MeasurableSet (sqX H B) :=
  hHo.measurableSet.inter (hB.preimage continuous_nrdHom.measurable)

theorem muSL1N_eq_muSL1 (s : Set (QuatAdele (a : F) (b : F))ˣ) (hs : MeasurableSet s) :
    muSL1N ha0 hb0 {y : (nrdHom (a : F) (b : F)).ker | (y : (QuatAdele (a : F) (b : F))ˣ) ∈ s} =
      muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
        {z : SL1A (a : F) (b : F) | ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ s} := by
  rw [muSL1N]
  exact (Measure.map_apply (map_continuous (kerNrdEquiv (a : F) (b : F)).symm).measurable
    (hs.preimage measurable_subtype_coe)).trans rfl

theorem muSL1P_eq_muSL1 (s : Set (QuatAdele (a : F) (b : F))ˣ) (hs : MeasurableSet s) :
    muSL1P (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
        {y : (nrdPos (a : F) (b : F)).ker | (y : (QuatAdele (a : F) (b : F))ˣ) ∈ s} =
      muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
        {z : SL1A (a : F) (b : F) | ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ s} := by
  rw [muSL1P]
  exact (Measure.map_apply (map_continuous (kerPosEquiv (a : F) (b : F)).symm).measurable
    (hs.preimage measurable_subtype_coe)).trans rfl

set_option maxHeartbeats 1600000 in
include hHE hdiv in
/-- **Along $p$**: $\mu_{G^\natural}(S) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mathrm{tamQuat}(X)$. -/
theorem muG_sqS_eq_tamQuat (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ))
    (hEo : IsOpen (E : Set (QuatAdele (a : F) (b : F))ˣ)) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B) :
    (dSq).muG (muSq ha0 hb0) (sqS ha0 hb0 H E hHE B) =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        tamQuat (a : F) (b : F) (sqX H B) := by
  have ha' : (a : F) ≠ 0 := by simpa using ha0
  have hb' : (b : F) ≠ 0 := by simpa using hb0
  have := isHaarMeasure_muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'
  set cE := muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E}
  have hXm := measurableSet_sqX H hHo hB
  have hS := measurableSet_sqS ha0 hb0 H E hHE hHo hEo hB
  rw [(dSq).muG_apply_of_fibK (muSq ha0 hb0) _ hS (fun c => cE * NormalFib.kern (nrdPos (a : F) (b : F))
    (nrdPos_surjective ha' hb') (muSL1P (valued_coe_le_one a) (valued_coe_le_one b) ha' hb') c (sqX H B))]
  · refine (lintegral_const_mul cE ?_).trans ?_
    · exact NormalFib.measurable_kern_apply _ _ measurable_nrdPos _ hXm
    congr 1
    exact (NormalFib.fibMeas_apply _ _ measurable_nrdPos (muPosA (a : F) (b : F)) _ hXm).symm.trans
      (congrArg (fun μ : Measure (QuatAdele (a : F) (b : F))ˣ => μ (sqX H B))
        (fibMeas_nrdPos (valued_coe_le_one a) (valued_coe_le_one b) ha' hb'))
  · intro g
    have hpg : (dSq).p g = nrdPos (a : F) (b : F) (gβ ha0 hb0 g) := Subtype.ext (nrd_gβ ha0 hb0 g).symm
    have hmS : MeasurableSet ((dSq).kerSEquiv.symm ⁻¹'
        ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqS ha0 hb0 H E hHE B)) :=
      (hS.preimage (NormalFib.measurable_mul_val _ _)).preimage
        (map_continuous (dSq).kerSEquiv.symm).measurable
    rw [NormalFib.fibK_apply _ _ _ hS, GnatData.muS, Measure.map_apply
      (map_continuous (dSq).kerSEquiv.symm).measurable (hS.preimage (NormalFib.measurable_mul_val _ _)),
      muSq, Measure.map_apply (map_continuous (kerSqEquiv ha0 hb0).symm).measurable hmS, hpg,
      NormalFib.kern_apply_N, NormalFib.fibK_apply _ _ _ hXm, muSL1P,
      Measure.map_apply (map_continuous (kerPosEquiv (a : F) (b : F)).symm).measurable
        (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    by_cases hu : gu ha0 hb0 g ∈ B
    · -- the fibre is the pair set
      have hset : (kerSqEquiv ha0 hb0).symm ⁻¹' ((dSq).kerSEquiv.symm ⁻¹'
          ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqS ha0 hb0 H E hHE B)) =
          {p : (nrdHom (a : F) (b : F)).ker × (nrdHom (a : F) (b : F)).ker |
            gβ ha0 hb0 g * (p.2 : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
            gα ha0 hb0 g * (p.1 : (QuatAdele (a : F) (b : F))ˣ) *
              (gβ ha0 hb0 g * (p.2 : (QuatAdele (a : F) (b : F))ˣ))⁻¹ ∈ E} := by
        ext p
        change (_ ∧ _) ∧ gu ha0 hb0 g * 1 ∈ B ↔ _
        rw [mul_one]
        exact and_iff_left hu
      rw [hset, muSL1N_prod_pair ha0 hb0 hdiv _ _ ((nrd_gα ha0 hb0 g).trans (nrd_gβ ha0 hb0 g).symm) _ E
        hHo.measurableSet hEo.measurableSet]
      congr 1
      refine (muSL1N_eq_muSL1 ha0 hb0 ((fun x => gβ ha0 hb0 g * x) ⁻¹' (H : Set (QuatAdele (a : F) (b : F))ˣ))
        (hHo.measurableSet.preimage (measurable_const_mul _))).trans ?_
      congr 1
      ext z
      change gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ H ↔
        gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ) ∈ H ∧
          nrdUnit (gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ)) ∈ B
      rw [nrdUnit_mul, mem_SL1A.1 z.2, mul_one, nrd_gβ]
      exact (and_iff_left hu).symm
    · have h1 : (kerSqEquiv ha0 hb0).symm ⁻¹' ((dSq).kerSEquiv.symm ⁻¹'
          ((fun k : (dSq).p.ker => g * (k : (dSq).G)) ⁻¹' sqS ha0 hb0 H E hHE B)) = ∅ := by
        ext p
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨-, h⟩
        change gu ha0 hb0 g * 1 ∈ B at h
        rw [mul_one] at h; exact hu h
      have h2 : (kerPosEquiv (a : F) (b : F)).symm ⁻¹' ((fun k : (nrdPos (a : F) (b : F)).ker =>
          gβ ha0 hb0 g * (k : (QuatAdele (a : F) (b : F))ˣ)) ⁻¹' sqX H B) = ∅ := by
        ext z
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        rintro ⟨-, h⟩
        change nrdUnit (gβ ha0 hb0 g * ((z : quatOne (a : F) (b : F)) : (QuatAdele (a : F) (b : F))ˣ)) ∈ B at h
        rw [nrdUnit_mul, mem_SL1A.1 z.2, mul_one, nrd_gβ] at h
        exact hu h
      rw [h1, h2, measure_empty, measure_empty, mul_zero]

set_option maxHeartbeats 1600000 in
/-- **Along $(D\otimes\mathbb A)^\times\to PD^\times(\mathbb A)$**: $\mathrm{tamQuat}(X) = c\,\mu_{PD}(\operatorname{pd}(H))$. -/
theorem tamQuat_sqX (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ)) {B : Set (Adeles F)ˣ}
    (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    tamQuat (a : F) (b : F) (sqX H B) =
      c * muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
        (pdMk (a : F) (b : F) '' H) := by
  have hXm := measurableSet_sqX H hHo hB
  have hopen : IsOpen (pdMk (a : F) (b : F) '' (H : Set (QuatAdele (a : F) (b : F))ˣ)) :=
    QuotientGroup.isOpenMap_coe _ hHo
  rw [← fibMeas_muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)]
  refine fibMeas_apply_of_kern _ _ (measurable_pdMk _ _) _ _ hXm hopen.measurableSet c ?_ ?_
  · rintro q ⟨β, hβ, rfl⟩
    refine ⟨β, rfl, ?_⟩
    rw [NormalFib.fibK_apply _ _ _ hXm, muZ, Measure.map_apply (map_continuous (kerEquiv _ _)).measurable
      (hXm.preimage (NormalFib.measurable_mul_val _ _)), ← hc β hβ]
    congr 1
    ext u
    simp only [mem_preimage, coe_kerEquiv, sqX, mem_setOf_eq]
    rw [H.mul_mem_cancel_left hβ, nrdUnit_mul, nrdUnit_quatScalar, mul_comm]
  · intro β hβ
    rw [NormalFib.fibK_apply _ _ _ hXm, muZ, Measure.map_apply (map_continuous (kerEquiv _ _)).measurable
      (hXm.preimage (NormalFib.measurable_mul_val _ _))]
    convert measure_empty (μ := tamIdeles F)
    ext u
    simp only [mem_preimage, coe_kerEquiv, sqX, mem_setOf_eq, mem_empty_iff_false, iff_false]
    rintro ⟨h1, -⟩
    apply hβ
    refine ⟨_, h1, ?_⟩
    rw [map_mul, (mem_ker_pdMk _ _).2 ⟨u, rfl⟩ |> MonoidHom.mem_ker.1, mul_one]

include hHE hdiv in
/-- **$\mu_P(\pi(S_0)) = \mu_{\mathrm{SL}_1}(E\cap\mathrm{SL}_1)\cdot\mu_{PD}(\operatorname{pd}(H))$** (the measure form of
$P\cong\mathrm{SL}_1(\mathbb A)\rtimes PD^\times(\mathbb A)$). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.7, p. 65 [unverified page]"]
theorem muP_sqS0 (hHo : IsOpen (H : Set (QuatAdele (a : F) (b : F))ˣ))
    (hEo : IsOpen (E : Set (QuatAdele (a : F) (b : F))ˣ)) {B : Set (Adeles F)ˣ} (hB : MeasurableSet B)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hc : ∀ β ∈ H, tamIdeles F {u | quatScalar _ _ u ∈ H ∧ u ^ 2 * nrdUnit β ∈ B} = c) :
    (dSq).muP (muSq ha0 hb0) ((dSq).π '' (sqS0 ha0 hb0 H E hHE)) =
      muSL1N ha0 hb0 {x : (nrdHom (a : F) (b : F)).ker | (x : (QuatAdele (a : F) (b : F))ˣ) ∈ E} *
        muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)
          (pdMk (a : F) (b : F) '' H) := by
  have h1 := muG_sqS_eq_muP ha0 hb0 H E hHE (muSq ha0 hb0) hHo hEo hB c hc
  rw [muG_sqS_eq_tamQuat ha0 hb0 H E hHE hdiv hHo hEo hB, tamQuat_sqX ha0 hb0 H hHo hB c hc] at h1
  refine (ENNReal.mul_right_inj hc0 hct).1 ?_
  rw [← h1]; ring

end Result

end

end QuadFormsKB.Tamagawa.Measure.Weil
