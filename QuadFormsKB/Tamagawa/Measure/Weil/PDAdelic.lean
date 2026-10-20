/-
# $(D\otimes\mathbb A)^\times/\mathbb A^\times \cong SO(D^0)(\mathbb A)$

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus 0$, $D = (a,b)_F$, $D^0$ the pure quaternions with
$\operatorname{nrd}|_{D^0} = \langle -a,-b,ab\rangle$ = `QuatZeta.pureFormO a b` $=: Q_0$ (a form over $\mathcal O_F$, so
The $SO(V)(\mathbb A_f)$ = `SOAf Q₀` and $SO(V)(\mathbb A)$ = `SOAdele Q₀` apply).

**Defines/proves** (finite part)
* `conjFin a b : (D\otimes\mathbb A_f)^\times \to SO(V)(\mathbb A_f)`, $\alpha\mapsto(c_v(\alpha_v))_v$ (the conjugation at
  every finite place; it lands in the restricted product because $\alpha_v\in\Lambda_v^\times$ for almost all $v$,
  `conjOrth_mem_stdStab`); **`continuous_conjFin`**;
* **`conjFin_surjective`**: every $g \in SO(V)(\mathbb A_f)$ is $c(\alpha)$: lift each $g_v$ (over $F_v$), and at the
  cofinitely many $v$ with $|2a b|_v = 1$ and $g_v \in SO(\mathfrak o_v^3)$ rescale the lift into $\Lambda_v^\times$
  (`exists_smul_mem_lamLocUnits`), so the lifts form an idele of $D$;
* **`conjFin_eq_one_iff`**: the kernel is $\mathbb A_f^\times$ (central scalars).

Source: Weil 1982, §3.7(a), p. 63 ($SO_3 \cong D^\times/G_m$ as algebraic groups, hence on adelic points); restricted
products as in Weil 1982, §1.2 [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.PDLocal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.Measure.Weil.QuatTamagawaGlobal
import QuadFormsKB.Tamagawa.QuaternionZeta

open Matrix Quaternion NumberField IsDedekindDomain WithZero Topology Filter
open scoped RestrictedProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-! ### Valuations of integers at almost all places -/

theorem valued_algebraMap_int_le_one (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 := by
  rw [← IsScalarTower.algebraMap_apply]
  exact valued_int_le_one v a

theorem eventually_valued_eq_one {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  filter_upwards [eventually_valuation_le_one (F := F) x, eventually_valuation_le_one (F := F) x⁻¹] with v h1 h2
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := by simpa using hx
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans
    (le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2))

/-- $\alpha_v \in \Lambda_v^\times$ for almost all $v$. -/
theorem eventually_unitAtQ_mem_lamLocUnits (A B : F) (α : (QuatFin A B)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, unitAtQ A B v α ∈ lamLocUnits A B v := by
  filter_upwards [(α : QuatFin A B).re.2, (α : QuatFin A B).imI.2, (α : QuatFin A B).imJ.2,
    (α : QuatFin A B).imK.2, ((α⁻¹ : (QuatFin A B)ˣ) : QuatFin A B).re.2,
    ((α⁻¹ : (QuatFin A B)ˣ) : QuatFin A B).imI.2, ((α⁻¹ : (QuatFin A B)ˣ) : QuatFin A B).imJ.2,
    ((α⁻¹ : (QuatFin A B)ˣ) : QuatFin A B).imK.2] with v h0 h1 h2 h3 h0' h1' h2' h3'
  refine ⟨⟨h0, h1, h2, h3⟩, ?_⟩
  rw [← map_inv]
  exact ⟨h0', h1', h2', h3'⟩

/-! ### The finite adelic map -/

variable (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (pureFormO a b)

theorem hQF : QF = pureForm (a : F) (b : F) := map_pureFormO a b

/-- The local components of `conjFin`. -/
def conjFinFun (α : (QuatFin (a : F) (b : F))ˣ) : OAf QF :=
  ⟨fun v => conjOrth QF (hQF a b) (unitAtQ _ _ v α), by
    filter_upwards [eventually_unitAtQ_mem_lamLocUnits _ _ α] with v hv
    exact conjOrth_mem_stdStab v (hQF a b) (valued_algebraMap_int_le_one v a) (valued_algebraMap_int_le_one v b) hv⟩

@[simp] theorem conjFinFun_apply (α : (QuatFin (a : F) (b : F))ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    conjFinFun a b α v = conjOrth QF (hQF a b) (unitAtQ _ _ v α) := rfl

/-- **$(D\otimes\mathbb A_f)^\times \to SO(V)(\mathbb A_f)$**, $\alpha \mapsto (y \mapsto \alpha_v y \alpha_v^{-1})_v$. -/
@[kb "weil1982" "§3.7(a), p. 63"]
def conjFin : (QuatFin (a : F) (b : F))ˣ →* SOAf Q₀ where
  toFun α := ⟨conjFinFun a b α, fun v => conjOrth_mem_soSub QF (hQF a b) _⟩
  map_one' := by
    ext v : 2
    simp
  map_mul' α β := by
    ext v : 2
    simp

@[simp] theorem conjFin_apply (α : (QuatFin (a : F) (b : F))ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((conjFin a b α : SOAf Q₀) : OAf QF) v = conjOrth QF (hQF a b) (unitAtQ _ _ v α) := rfl

/-- Continuity of the local conjugation map on $(D\otimes\mathbb A_f)^\times$ at one place. -/
theorem continuous_conjOrth_unitAtQ (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun α : (QuatFin (a : F) (b : F))ˣ => conjOrth QF (hQF a b) (unitAtQ _ _ v α) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_conjGL_comp (fun α : (QuatFin (a : F) (b : F))ˣ => unitAtQ _ _ v α) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fre _ _).comp Units.continuous_val)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimI _ _).comp Units.continuous_val)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimJ _ _).comp Units.continuous_val)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimK _ _).comp Units.continuous_val)
  all_goals simp only [← map_inv]
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fre _ _).comp Units.continuous_coe_inv)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimI _ _).comp Units.continuous_coe_inv)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimJ _ _).comp Units.continuous_coe_inv)
  · exact (RestrictedProduct.continuous_eval v).comp ((continuous_fimK _ _).comp Units.continuous_coe_inv)

/-- **`conjFin` is continuous.** On the open subgroup $\hat\Lambda^\times$ it factors through
$\prod_v O(\mathfrak o_v^3)$, where the restricted product topology is the product topology (Mathlib's
`RestrictedProduct.isEmbedding_structureMap`; a homomorphism continuous at $1$ is continuous, Mathlib's
`continuous_of_continuousAt_one`). -/
theorem continuous_conjFin : Continuous (conjFin a b) := by
  refine continuous_of_continuousAt_one _ ?_
  have hU : lamHatUnits (a : F) (b : F) ∈ 𝓝 (1 : (QuatFin (a : F) (b : F))ˣ) :=
    (isOpen_lamHatUnits _ _).mem_nhds (one_mem_lamHatUnits _ _)
  have hmem : ∀ α ∈ lamHatUnits (a : F) (b : F), ∀ v,
      conjOrth QF (hQF a b) (unitAtQ _ _ v α) ∈ stdStab QF v := fun α hα v =>
    conjOrth_mem_stdStab v (hQF a b) (valued_algebraMap_int_le_one v a) (valued_algebraMap_int_le_one v b)
      ((mem_lamHatUnits_iff _ _ α).1 hα v)
  let g : lamHatUnits (a : F) (b : F) → ∀ v, (stdStab QF v : Set (orthGroup QF (v.adicCompletion F))) :=
    fun α v => ⟨_, hmem α.1 α.2 v⟩
  have hg : Continuous g := continuous_pi fun v =>
    ((continuous_conjOrth_unitAtQ a b v).comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous fun α : lamHatUnits (a : F) (b : F) => ((conjFin a b α.1 : SOAf Q₀) : OAf QF) := by
    have := (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => orthGroup QF (v.adicCompletion F))
      (A := fun v => (stdStab QF v : Set (orthGroup QF (v.adicCompletion F)))) (𝓕 := cofinite)).continuous.comp hg
    refine this.congr fun α => ?_
    ext v : 1
    rfl
  have hon : ContinuousOn (fun α => ((conjFin a b α : SOAf Q₀) : OAf QF)) (lamHatUnits (a : F) (b : F)) :=
    continuousOn_iff_continuous_domRestrict.2 hcomp
  have hat := hon.continuousAt hU
  exact (Topology.IsInducing.subtypeVal.continuousAt_iff).2 hat

/-! ### Kernel and surjectivity of the finite map -/

/-- A finite adele from a family that is integral at almost all places. -/
def mkAF (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ᶠ v in cofinite, f v ∈ v.adicCompletionIntegers F) : AF := ⟨f, hf⟩

@[simp] theorem mkAF_apply (f : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hf : ∀ᶠ v in cofinite, f v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : mkAF f hf v = f v :=
  rfl

/-- The central scalars $\mathbb A_f^\times \to (D\otimes\mathbb A_f)^\times$. -/
def finScalar (A B : F) : AFˣ →* (QuatFin A B)ˣ := Units.map (algebraMap AF (QuatFin A B)).toMonoidHom

theorem unitAtQ_finScalar (A B : F) (c : AFˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtQ A B v (finScalar A B c) ∈ centerUnits (algebraMap F (v.adicCompletion F) A)
      (algebraMap F (v.adicCompletion F) B) := by
  refine mem_centerUnits.2 ⟨(c : AF) v, ?_⟩
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> rfl

theorem conjOrth_eq_one_iff {K : Type*} [Field K] [Algebra F K] (Q : QuadForm F 3) {A B : F}
    (hQ : Q = pureForm A B) (hA : A ≠ 0) (α : (ℍ[K, algebraMap F K A, algebraMap F K B])ˣ) :
    conjOrth Q hQ α = 1 ↔ α ∈ centerUnits (algebraMap F K A) (algebraMap F K B) := by
  rw [← conjSOK_eq_one_iff Q hQ hA α]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-- **The kernel of $(D\otimes\mathbb A_f)^\times \to SO(V)(\mathbb A_f)$ is $\mathbb A_f^\times$.** -/
theorem conjFin_eq_one_iff (ha : a ≠ 0) (α : (QuatFin (a : F) (b : F))ˣ) :
    conjFin a b α = 1 ↔ α ∈ (finScalar (a : F) (b : F)).range := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  constructor
  · intro h
    have hv : ∀ (β : (QuatFin (a : F) (b : F))ˣ), conjFin a b β = 1 → ∀ v,
        (β : QuatFin (a : F) (b : F)).imI v = 0 ∧ (β : QuatFin (a : F) (b : F)).imJ v = 0 ∧
          (β : QuatFin (a : F) (b : F)).imK v = 0 := by
      intro β hβ v
      have h1 : conjOrth QF (hQF a b) (unitAtQ _ _ v β) = 1 := by
        have := congrArg (fun g : SOAf Q₀ => ((g : OAf QF) v)) hβ
        exact this
      obtain ⟨r, hr⟩ := mem_centerUnits.1 ((conjOrth_eq_one_iff QF (hQF a b) hA _).1 h1)
      refine ⟨?_, ?_, ?_⟩
      · exact congrArg QuaternionAlgebra.imI hr
      · exact congrArg QuaternionAlgebra.imJ hr
      · exact congrArg QuaternionAlgebra.imK hr
    have hα := hv α h
    have hα' := hv α⁻¹ (by rw [map_inv, h, inv_one])
    have e0 : ∀ x : AF, (∀ v, x v = 0) → x = 0 := fun x hx => Subtype.ext (funext hx)
    have hI := e0 _ fun v => (hα v).1
    have hJ := e0 _ fun v => (hα v).2.1
    have hK := e0 _ fun v => (hα v).2.2
    have hI' := e0 _ fun v => (hα' v).1
    have hJ' := e0 _ fun v => (hα' v).2.1
    have hK' := e0 _ fun v => (hα' v).2.2
    have hre : ∀ β γ : QuatFin (a : F) (b : F), β.imI = 0 → β.imJ = 0 → β.imK = 0 → γ.imI = 0 → γ.imJ = 0 →
        γ.imK = 0 → (β * γ).re = β.re * γ.re := by
      intro β γ h1 h2 h3 h4 h5 h6
      simp [QuaternionAlgebra.re_mul, h1, h2, h3, h4, h5, h6]
    have m1 : (α : QuatFin (a : F) (b : F)).re * ((α⁻¹ : (QuatFin (a : F) (b : F))ˣ) : QuatFin (a : F) (b : F)).re
        = 1 := by
      rw [← hre _ _ hI hJ hK hI' hJ' hK', Units.mul_inv]; rfl
    have m2 : ((α⁻¹ : (QuatFin (a : F) (b : F))ˣ) : QuatFin (a : F) (b : F)).re * (α : QuatFin (a : F) (b : F)).re
        = 1 := by rw [mul_comm, m1]
    refine ⟨⟨_, _, m1, m2⟩, Units.ext ?_⟩
    refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
    · rfl
    · exact hI.symm
    · exact hJ.symm
    · exact hK.symm
  · rintro ⟨c, rfl⟩
    ext v : 2
    exact (conjOrth_eq_one_iff QF (hQF a b) hA _).2 (unitAtQ_finScalar _ _ c v)

/-- **$(D\otimes\mathbb A_f)^\times \to SO(V)(\mathbb A_f)$ is surjective** ($a, b \ne 0$).

*Proof.* Lift each $g_v$ to $\beta_v \in D_v^\times$ (`conjSO_surjective` over $F_v$). At the cofinitely many $v$
with $|2|_v = |a|_v = |b|_v = 1$ and $g_v \in SO(\mathfrak o_v^3)$, the conjugation matrix $g_v$ is integral, so the lift
can be rescaled into $\Lambda_v^\times$ (`exists_smul_mem_lamLocUnits`). Then $(\beta_v)_v$ and $(\beta_v^{-1})_v$ are
finite adeles of $D$, inverse to each other. -/
@[kb "weil1982" "§3.7(a), p. 63"]
theorem conjFin_surjective (ha : a ≠ 0) (hb : b ≠ 0) : Function.Surjective (conjFin a b) := by
  intro g
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  set gv : ∀ v : HeightOneSpectrum (𝓞 F), soSub QF (v.adicCompletion F) := fun v => ⟨(g : OAf QF) v, g.2 v⟩
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | Valued.v (2 : v.adicCompletion F) = 1 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧
    (g : OAf QF) v ∈ stdStab QF v}
  have hS : ∀ᶠ v in cofinite, v ∈ S := by
    have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : v.adicCompletion F) = 1 := by
      filter_upwards [eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hv
      rwa [map_ofNat] at hv
    filter_upwards [h2, eventually_valued_eq_one hA, eventually_valued_eq_one hB, (g : OAf QF).2] with v h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hlift : ∀ v, ∃ β : (QuatV (a : F) (b : F) v)ˣ, conjSOK QF (hQF a b) β = gv v ∧
      (v ∈ S → β ∈ lamLocUnits (a : F) (b : F) v) := by
    intro v
    obtain ⟨α, hα⟩ := conjSOK_surjective (K := v.adicCompletion F) QF (hQF a b) hA hB (gv v)
    by_cases hv : v ∈ S
    · obtain ⟨h2, hav, hbv, hst⟩ := hv
      have hint : ∀ i j, Valued.v (((conjGL α : GL (Fin 3) (v.adicCompletion F)) :
          Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1 := by
        intro i j
        have := entry_le_one_of_mem_stdStab v hst i j
        have e : ((conjGL α : GL (Fin 3) (v.adicCompletion F)) : Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) =
            omat ((g : OAf QF) v) := by
          rw [← conjSOK_coe QF (hQF a b) α]
          exact congrArg (fun x : soSub QF (v.adicCompletion F) => omat (x : orthGroup QF (v.adicCompletion F))) hα
        rw [e]
        exact this
      obtain ⟨r, hr⟩ := exists_smul_mem_lamLocUnits v (fun w => valued_algebraMap_int_le_one w a)
        (fun w => valued_algebraMap_int_le_one w b) h2 hav hbv α hint
      refine ⟨_, ?_, fun _ => hr⟩
      rw [← hα]
      ext : 3
      simp only [conjSOK_coe]
      rw [conjGL_smul]
    · exact ⟨α, hα, fun h => absurd h hv⟩
  choose β hβ hβS using hlift
  have hev : ∀ᶠ v in cofinite, β v ∈ lamLocUnits (a : F) (b : F) v := by
    filter_upwards [hS] with v hv
    exact hβS v hv
  let x : QuatFin (a : F) (b : F) :=
    ⟨mkAF (fun v => (β v : QuatV (a : F) (b : F) v).re) (by filter_upwards [hev] with v hv; exact hv.1.1),
     mkAF (fun v => (β v : QuatV (a : F) (b : F) v).imI) (by filter_upwards [hev] with v hv; exact hv.1.2.1),
     mkAF (fun v => (β v : QuatV (a : F) (b : F) v).imJ) (by filter_upwards [hev] with v hv; exact hv.1.2.2.1),
     mkAF (fun v => (β v : QuatV (a : F) (b : F) v).imK) (by filter_upwards [hev] with v hv; exact hv.1.2.2.2)⟩
  let y : QuatFin (a : F) (b : F) :=
    ⟨mkAF (fun v => (((β v)⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v).re)
        (by filter_upwards [hev] with v hv; exact hv.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v).imI)
        (by filter_upwards [hev] with v hv; exact hv.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v).imJ)
        (by filter_upwards [hev] with v hv; exact hv.2.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v).imK)
        (by filter_upwards [hev] with v hv; exact hv.2.2.2.2)⟩
  have hx : ∀ v, projQ _ _ v x = β v := fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hy : ∀ v, projQ _ _ v y = (((β v)⁻¹ : (QuatV (a : F) (b : F) v)ˣ) : QuatV (a : F) (b : F) v) :=
    fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hxy : x * y = 1 := projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.inv_mul]
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  ext v : 2
  have hu : unitAtQ _ _ v ⟨x, y, hxy, hyx⟩ = β v := Units.ext (hx v)
  rw [conjFin_apply, hu]
  exact congrArg Subtype.val (hβ v)

end QuadFormsKB.Tamagawa.Measure.Weil
