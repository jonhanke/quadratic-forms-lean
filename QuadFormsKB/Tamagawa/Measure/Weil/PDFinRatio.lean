import QuadFormsKB.Tamagawa.Measure.Weil.PDCongruence
import QuadFormsKB.Tamagawa.Measure.ProductSO
import QuadFormsKB.Tamagawa.Measure.Weil.ChartMeasures

/-!
# The quotient measure on $PD^\times(\mathbb A_f)$ and the finite ratio $r_f$

**Layer:** $F$ a number field, $a, b \in \mathcal O_F\setminus 0$, $D = \mathbb H[F,a,b]$, $Q_0 = \langle -a,-b,ab\rangle$.

**Defines/proves**
* generic: `relIndex_map_eq_of_ker_le` (indices are preserved by a homomorphism whose kernel meets $A$ inside $H$);
  `exists_quatFin_of_local` (local units in $\Lambda_v^\times$ assemble to a finite adele of $D$);
* `muPDFin a b`: **Weil's quotient Tamagawa measure on $PD^\times(\mathbb A_f) = (D\otimes\mathbb A_f)^\times/\mathbb A_f^\times$**,
  the Haar measure with $\mu(\text{image of }\hat\Lambda^\times) = \mu_{D^\times}(\hat\Lambda^\times)/\mu_{G_m}(\hat{\mathcal O}^\times)$
  (`muFinQuat`, `muFinUnits`, i.e. $\prod_v\lambda_v^{-1}\omega_v^{D^\times}/\lambda_v^{-1}\omega_v^{G_m}$);
* **`map_muPDFin`**: its image under $PD^\times(\mathbb A_f) \cong SO(V)(\mathbb A_f)$ is $r_f\cdot$`muFin Q₀ 1` with
  $r_f = |N_{F/\mathbb Q}(8a^3b^3)|^{-1}\,|d_F|^{-3/2}$ (`rF`), from the local ratios of `PDCongruence.lean` at the
  finitely many bad places and the good-place ratios.
-/

open MeasureTheory Matrix Quaternion NumberField IsDedekindDomain WithZero Set Filter
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta

/-! ### Generic facts -/

section Generic

variable {G G' : Type*} [Group G] [Group G']

/-- **Indices under a homomorphism:** if $H \le A$ and $A \cap \ker f \le H$, then $[f(A) : f(H)] = [A : H]$. -/
theorem relIndex_map_eq_of_ker_le (f : G →* G') {H A : Subgroup G} (hHA : H ≤ A) (hker : A ⊓ f.ker ≤ H) :
    (H.map f).relIndex (A.map f) = H.relIndex A := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ← Subgroup.inf_relIndex_right]
  congr 1
  apply le_antisymm
  · rintro x ⟨hx, hxA⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    have hzA : z ∈ A := by
      have := A.mul_mem (A.inv_mem (hHA hy)) hxA
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    exact H.mul_mem hy (hker ⟨hzA, hz⟩)
  · exact fun x hx => ⟨Subgroup.mem_sup_left hx, hHA hx⟩

/-- **Splitting an Euler product off a finite set:** if $Q_v = O_vL_v$ outside $S$, $O$ has finite support and $L$ is
multipliable, then $\prod'_vQ_v = \prod_{v\in S}\frac{Q_v}{O_vL_v}\cdot\prod^f_vO_v\cdot\prod'_vL_v$. -/
theorem tprod_eq_prod_mul_finprod_mul_tprod {ι : Type*} (Q O L : ι → ℝ) (S : Finset ι)
    (hO : (Function.mulSupport O).Finite) (hL : Multipliable L) (hOL : ∀ v ∈ S, O v * L v ≠ 0)
    (hQ : ∀ v ∉ S, Q v = O v * L v) :
    ∏' v, Q v = (∏ v ∈ S, Q v / (O v * L v)) * ((∏ᶠ v, O v) * ∏' v, L v) := by
  classical
  set g : ι → ℝ := fun v => if v ∈ S then Q v / (O v * L v) else 1
  have hfun : Q = fun v => g v * (O v * L v) := by
    funext v
    by_cases hv : v ∈ S
    · simp only [g, hv, ite_true]; rw [div_mul_cancel₀ _ (hOL v hv)]
    · simp only [g, hv, ite_false, one_mul]; exact hQ v hv
  have hg1 : ∀ v ∉ S, g v = 1 := fun v hv => by simp [g, hv]
  have hg : Multipliable g := multipliable_of_ne_finset_one hg1
  have hOm : Multipliable O := multipliable_of_ne_finset_one (s := hO.toFinset) fun v hv => by
    simpa using hv
  conv_lhs => rw [hfun]
  rw [Multipliable.tprod_mul hg (hOm.mul hL), Multipliable.tprod_mul hOm hL, tprod_eq_prod hg1,
    tprod_eq_finprod hO]
  congr 1
  exact Finset.prod_congr rfl fun v hv => by simp [g, hv]

end Generic

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

/-- Every nonzero integer has valuation $q^{-e}$, $e \in \mathbb N$, at every finite place. -/
theorem exists_valued_eq_exp (x : 𝓞 F) (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℕ, Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = exp (-(e : ℤ)) := by
  set y := Valued.v (algebraMap F (v.adicCompletion F) (x : F))
  have hy0 : y ≠ 0 := by
    have : algebraMap F (v.adicCompletion F) (x : F) ≠ 0 :=
      (map_ne_zero _).2 (by exact_mod_cast hx)
    simpa [y] using this
  have hy1 : y ≤ 1 := valued_algebraMap_le_one x v
  have hlog : WithZero.log y ≤ 0 := by
    have := (WithZero.log_le_log hy0 one_ne_zero).mpr hy1
    simpa using this
  refine ⟨(-WithZero.log y).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hy0]

/-- **Assembly:** local units $\beta_v \in \Lambda_v^\times$ at every place come from a finite adele $\alpha$ of $D$. -/
theorem exists_quatFin_of_local (A B : F) (β : ∀ v : HeightOneSpectrum (𝓞 F), (QuatV A B v)ˣ)
    (hβ : ∀ v, β v ∈ lamLocUnits A B v) : ∃ α : (QuatFin A B)ˣ, ∀ v, unitAtQ A B v α = β v := by
  have hev : ∀ᶠ v in cofinite, β v ∈ lamLocUnits A B v := Filter.Eventually.of_forall hβ
  let x : QuatFin A B :=
    ⟨mkAF (fun v => (β v : QuatV A B v).re) (by filter_upwards [hev] with v hv; exact hv.1.1),
     mkAF (fun v => (β v : QuatV A B v).imI) (by filter_upwards [hev] with v hv; exact hv.1.2.1),
     mkAF (fun v => (β v : QuatV A B v).imJ) (by filter_upwards [hev] with v hv; exact hv.1.2.2.1),
     mkAF (fun v => (β v : QuatV A B v).imK) (by filter_upwards [hev] with v hv; exact hv.1.2.2.2)⟩
  let y : QuatFin A B :=
    ⟨mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).re) (by filter_upwards [hev] with v hv; exact hv.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imI)
        (by filter_upwards [hev] with v hv; exact hv.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imJ)
        (by filter_upwards [hev] with v hv; exact hv.2.2.2.1),
     mkAF (fun v => (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v).imK)
        (by filter_upwards [hev] with v hv; exact hv.2.2.2.2)⟩
  have hx : ∀ v, projQ _ _ v x = β v := fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hy : ∀ v, projQ _ _ v y = (((β v)⁻¹ : (QuatV A B v)ˣ) : QuatV A B v) :=
    fun v => QuaternionAlgebra.ext rfl rfl rfl rfl
  have hxy : x * y = 1 := projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := projQ_injective _ _ fun v => by rw [map_mul, map_one, hx, hy, Units.inv_mul]
  exact ⟨⟨x, y, hxy, hyx⟩, fun v => Units.ext (hx v)⟩

/-! ### The bad places, the exponents, and the congruence levels -/

section Global

variable (a b : 𝓞 F)

local notation "Q₀" => pureFormO a b
local notation "QF" => QuadForm.map (algebraMap (𝓞 F) F) (pureFormO a b)

theorem intA (a : 𝓞 F) : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) (a : F)) ≤ 1 :=
  fun v => valued_algebraMap_le_one a v

/-- A place is *good* if $|2|_v = |a|_v = |b|_v = 1$, $\mathrm{vol}(\mathfrak o_v) = 1$ and the good-place ratio holds. -/
def GoodPlace (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  Valued.v (2 : v.adicCompletion F) = 1 ∧ Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1 ∧
    Valued.v (algebraMap F (v.adicCompletion F) (b : F)) = 1 ∧
    (Analysis.selfDualV v).real (Analysis.latticeV v 0) = 1 ∧
    Measure.muLocSO v Q₀ 1 (Measure.soStabSO v Q₀ : Set (Measure.SOv v Q₀)) =
      ENNReal.ofReal (quatLocalFactor (a : F) (b : F) v)

variable {a b}

theorem eventually_goodPlace (ha : a ≠ 0) (hb : b ≠ 0) : ∀ᶠ v in cofinite, GoodPlace a b v := by
  have ha0 : (a : F) ≠ 0 := by exact_mod_cast ha
  have hb0 : (b : F) ≠ 0 := by exact_mod_cast hb
  filter_upwards [eventually_good_place ha0 hb0,
    eventually_muLocSO_soStabSO_eq_quatLocalFactor a b ha hb] with v ⟨h1, h2, h3, h4⟩ h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The finite set of bad places** (where some of the conditions of `GoodPlace` fail). -/
def badSet (ha : a ≠ 0) (hb : b ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Filter.eventually_cofinite.mp (eventually_goodPlace ha hb)).toFinset

theorem goodPlace_of_not_mem_badSet (ha : a ≠ 0) (hb : b ≠ 0) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ badSet ha hb) : GoodPlace a b v := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).mpr h)

theorem exists_valued_two_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℕ, Valued.v (2 : v.adicCompletion F) = exp (-(e : ℤ)) := by
  obtain ⟨e, he⟩ := exists_valued_eq_exp (2 : 𝓞 F) two_ne_zero v
  refine ⟨e, ?_⟩
  rw [← he]
  congr 1
  rw [show (((2 : 𝓞 F) : F)) = algebraMap (𝓞 F) F 2 from rfl, map_ofNat, map_ofNat]

/-- The exponents: $|2|_v = q^{-s_v}$, $|a|_v = q^{-e_a(v)}$, $|b|_v = q^{-e_b(v)}$. -/
def sExp (v : HeightOneSpectrum (𝓞 F)) : ℕ := (exists_valued_two_eq v).choose

theorem valued_two_eq (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (2 : v.adicCompletion F) = exp (-(sExp v : ℤ)) :=
  (exists_valued_two_eq v).choose_spec

def eExp (x : 𝓞 F) (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : ℕ := (exists_valued_eq_exp x hx v).choose

theorem valued_eExp (x : 𝓞 F) (hx : x ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = exp (-(eExp x hx v : ℤ)) :=
  (exists_valued_eq_exp x hx v).choose_spec

/-- The congruence level $m_v = 2d_v + 1$, $d_v = 3s_v + 2e_a(v) + 2e_b(v)$. -/
def mLev (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  2 * (3 * sExp v + 2 * eExp a ha v + 2 * eExp b hb v) + 1

theorem one_le_mLev (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : 1 ≤ mLev ha hb v := by
  unfold mLev; omega

/-! ### The subgroups $H_S \le \hat\Lambda^\times$ and $c(H_S)$ -/

variable (a b) in
/-- $\hat\Lambda^\times$ for integral $a, b$. -/
abbrev lamHatSub : Subgroup (QuatFin (a : F) (b : F))ˣ := lamHatUnitsSub (intA a) (intA b)

/-- **$H_S$**: the $u \in \hat\Lambda^\times$ with $u_v \in \Lambda^{(m_v)}_v$ at the bad places. -/
def quatCong (ha : a ≠ 0) (hb : b ≠ 0) : Subgroup (QuatFin (a : F) (b : F))ˣ :=
  lamHatSub a b ⊓ ⨅ v ∈ badSet ha hb, (lamCong v a b (mLev ha hb v) (one_le_mLev ha hb v)).comap (unitAtQ _ _ v)

theorem quatCong_le (ha : a ≠ 0) (hb : b ≠ 0) : quatCong ha hb ≤ lamHatSub a b := inf_le_left

/-- The local sets of the box: $\Lambda^{(m_v)}_v$ at the bad places. -/
def congU (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : Set (QuatV (a : F) (b : F) v)ˣ :=
  lamCong v a b (mLev ha hb v) (one_le_mLev ha hb v)

open scoped Classical in
theorem coe_quatCong (ha : a ≠ 0) (hb : b ≠ 0) :
    (quatCong ha hb : Set (QuatFin (a : F) (b : F))ˣ) = quatBox (a : F) (b : F) (badSet ha hb) (congU ha hb) := by
  ext u
  simp only [SetLike.mem_coe, quatCong, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, quatBox,
    ChartData.chartBox, Set.mem_ofPred_eq]
  change (u ∈ lamHatUnits (a : F) (b : F) ∧ _) ↔ _
  rw [mem_lamHatUnits_iff]
  constructor
  · rintro ⟨h1, h2⟩ v
    change unitAtQ _ _ v u ∈ (if v ∈ badSet ha hb then congU ha hb v else lamLocUnits (a : F) (b : F) v)
    split_ifs with hv
    · exact h2 v hv
    · exact h1 v
  · intro h
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ badSet ha hb then congU ha hb v else lamLocUnits (a : F) (b : F) v) at this
      split_ifs at this with hv
      · exact this.2
      · exact this
    · have := h v
      change unitAtQ _ _ v u ∈ (if v ∈ badSet ha hb then congU ha hb v else lamLocUnits (a : F) (b : F) v) at this
      rwa [ite_eq_left_iff.mpr (fun h => absurd hv h)] at this

/-- The scalar units in $\hat\Lambda^\times$ lie in $H_S$. -/
theorem lamHat_inf_ker_le (ha : a ≠ 0) (hb : b ≠ 0) :
    lamHatSub a b ⊓ (conjFin a b).ker ≤ quatCong ha hb := by
  rintro u ⟨hu, hk⟩
  refine ⟨hu, Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun hv => ?_⟩
  rw [Subgroup.mem_comap]
  obtain ⟨c, rfl⟩ := (conjFin_eq_one_iff a b ha u).mp hk
  have huv : unitAtQ _ _ v (finScalar (a : F) (b : F) c) ∈ lamLocUnits (a : F) (b : F) v :=
    (mem_lamHatUnits_iff _ _ _).mp hu v
  refine ⟨?_, huv⟩
  -- a central unit acts trivially, so it lies in `K_m`
  have h1 : conjOrth QF (hQF a b) (unitAtQ _ _ v (finScalar (a : F) (b : F) c)) = 1 :=
    (conjOrth_eq_one_iff QF (hQF a b) (by exact_mod_cast ha) _).2 (unitAtQ_finScalar _ _ c v)
  show unitAtQ _ _ v (finScalar (a : F) (b : F) c) ∈ (LerayPadic.congSub v Q₀ (mLev ha hb v)
    (one_le_mLev ha hb v)).comap (conjOrth QF (hQF a b))
  rw [Subgroup.mem_comap, h1]
  exact Subgroup.one_mem _

/-- The local sets on the orthogonal side: $K_{m_v}$ inside $SO(V)(F_v)$. -/
def congSO (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) : Set (Measure.SOv v Q₀) :=
  Subtype.val ⁻¹' (LerayPadic.congSub v Q₀ (mLev ha hb v) (one_le_mLev ha hb v) : Set (orthGroup QF _))

/-- **$c(H_S)$ is the box** $\prod_{v\in S}K_{m_v}\times\prod_{v\notin S}SO(L_v)$. -/
theorem coe_map_quatCong (ha : a ≠ 0) (hb : b ≠ 0) :
    ((quatCong ha hb).map (conjFin a b) : Set (SOAf Q₀)) = QuadFormsKB.Tamagawa.Measure.boxSO Q₀ (badSet ha hb) (congSO ha hb) := by
  have hA : (a : F) ≠ 0 := by exact_mod_cast ha
  have hB : (b : F) ≠ 0 := by exact_mod_cast hb
  ext g
  simp only [SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ∀ v, unitAtQ _ _ v u ∈ lamLocUnits (a : F) (b : F) v :=
      (mem_lamHatUnits_iff _ _ _).mp (quatCong_le ha hb hu)
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have := (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hu.2 v) hv)
      exact this.1
    · exact conjOrth_mem_stdStab v (hQF a b) (intA a v) (intA b v) (hu' v)
  · rintro ⟨hS, hnS⟩
    have hlift : ∀ v, ∃ β : (QuatV (a : F) (b : F) v)ˣ, conjOrth QF (hQF a b) β = (g : OAf QF) v ∧
        β ∈ lamLocUnits (a : F) (b : F) v ∧ (v ∈ badSet ha hb → β ∈ congU ha hb v) := by
      intro v
      by_cases hv : v ∈ badSet ha hb
      · have hg : (g : OAf QF) v ∈ LerayPadic.congSub v Q₀ (mLev ha hb v) (one_le_mLev ha hb v) := hS v hv
        rw [← map_lamCong v a b ha hb (valued_two_eq v) (valued_eExp a ha v) (by unfold mLev; omega)
          (by unfold mLev; omega) (one_le_mLev ha hb v)] at hg
        obtain ⟨β, hβ, hβg⟩ := hg
        exact ⟨β, hβg, hβ.2, fun _ => hβ⟩
      · obtain ⟨h2, hav, hbv, -, -⟩ := goodPlace_of_not_mem_badSet ha hb hv
        have hst : (g : OAf QF) v ∈ stdStab QF v := hnS v hv
        obtain ⟨α, hα⟩ := conjSOK_surjective (K := v.adicCompletion F) QF (hQF a b) hA hB ⟨(g : OAf QF) v, g.2 v⟩
        have hαg : conjOrth QF (hQF a b) α = (g : OAf QF) v := congrArg Subtype.val hα
        have hint : ∀ i j, Valued.v (((conjGL α : GL (Fin 3) (v.adicCompletion F)) :
            Matrix (Fin 3) (Fin 3) (v.adicCompletion F)) i j) ≤ 1 := by
          intro i j
          have := entry_le_one_of_mem_stdStab v hst i j
          rwa [← hαg] at this
        obtain ⟨r, hr⟩ := exists_smul_mem_lamLocUnits v (intA a) (intA b) h2 hav hbv α hint
        refine ⟨_, ?_, hr, fun h => absurd h hv⟩
        rw [← hαg]
        ext : 2
        exact congrArg Units.val (conjGL_smul α r)
    choose β hβg hβL hβS using hlift
    obtain ⟨α, hα⟩ := exists_quatFin_of_local (a : F) (b : F) β hβL
    refine ⟨α, ⟨(mem_lamHatUnits_iff _ _ _).mpr fun v => by rw [hα]; exact hβL v,
      Subgroup.mem_iInf.mpr fun v => Subgroup.mem_iInf.mpr fun hv => by
        rw [Subgroup.mem_comap, hα]; exact hβS v hv⟩, ?_⟩
    ext v : 2
    rw [conjFin_apply, hα, hβg]

/-! ### Topology of $\Lambda^{(m)}_v$ and $H_S$ -/

theorem continuous_conjOrth_loc (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (conjOrth QF (hQF a b) : (QuatV (a : F) (b : F) v)ˣ → orthGroup QF (v.adicCompletion F)) := by
  have hc : ∀ i, Continuous fun x : QuatV (a : F) (b : F) v => quatLocCoord _ _ x i := fun i =>
    (continuous_apply i).comp (continuous_quatLocCoord _ _)
  refine Continuous.subtype_mk ?_ _
  refine continuous_conjGL_comp (fun α : (QuatV (a : F) (b : F) v)ˣ => α) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact (hc 0).comp Units.continuous_val
  · exact (hc 1).comp Units.continuous_val
  · exact (hc 2).comp Units.continuous_val
  · exact (hc 3).comp Units.continuous_val
  · exact (hc 0).comp Units.continuous_coe_inv
  · exact (hc 1).comp Units.continuous_coe_inv
  · exact (hc 2).comp Units.continuous_coe_inv
  · exact (hc 3).comp Units.continuous_coe_inv

theorem isOpen_lamCong (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : 1 ≤ m) :
    IsOpen (lamCong v a b m hm : Set (QuatV (a : F) (b : F) v)ˣ) :=
  ((LerayPadic.isOpen_congSub v Q₀ m hm).preimage (continuous_conjOrth_loc v)).inter
    (isOpen_lamLocUnits (a : F) (b : F) v)

theorem isOpen_quatCong (ha : a ≠ 0) (hb : b ≠ 0) :
    IsOpen (quatCong ha hb : Set (QuatFin (a : F) (b : F))ˣ) := by
  rw [quatCong, Subgroup.coe_inf]
  refine (isOpen_lamHatUnits (a : F) (b : F)).inter ?_
  simp only [Subgroup.coe_iInf]
  exact isOpen_biInter_finset fun v _ =>
    (isOpen_lamCong v (mLev ha hb v) (one_le_mLev ha hb v)).preimage (continuous_unitAtQ _ _ v)

/-! ### The measures: indices and boxes -/

variable (a b) in
/-- $c(\hat\Lambda^\times) \le SO(V)(\mathbb A_f)$. -/
def lamHatSO : Subgroup (SOAf Q₀) := (lamHatSub a b).map (conjFin a b)

theorem isCompact_lamHatSO : IsCompact (lamHatSO a b : Set (SOAf Q₀)) := by
  rw [lamHatSO, Subgroup.coe_map]
  exact (isCompact_lamHatUnits (a : F) (b : F)).image (continuous_conjFin a b)

theorem isOpen_map_conjFin (ha : a ≠ 0) (hb : b ≠ 0) {H : Subgroup (QuatFin (a : F) (b : F))ˣ}
    (hH : IsOpen (H : Set (QuatFin (a : F) (b : F))ˣ)) : IsOpen (H.map (conjFin a b) : Set (SOAf Q₀)) := by
  rw [Subgroup.coe_map]
  exact MonoidHom.isOpenMap_of_sigmaCompact _ (conjFin_surjective a b ha hb) (continuous_conjFin a b) _ hH

theorem relIndex_quatCong_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) :
    (quatCong ha hb).relIndex (lamHatSub a b) ≠ 0 :=
  Measure.relIndex_ne_zero_of_isOpen (isCompact_lamHatUnits (a : F) (b : F)) (isOpen_quatCong ha hb)

theorem isHaarMeasure_muFinQuat' (ha : a ≠ 0) (hb : b ≠ 0) : (muFinQuat (a : F) (b : F)).IsHaarMeasure :=
  isHaarMeasure_muFinQuat (intA a) (intA b) (by exact_mod_cast ha) (by exact_mod_cast hb)

/-- $\mu_{D^\times}(\hat\Lambda^\times) = [\hat\Lambda^\times : H_S]\,\mu_{D^\times}(H_S)$. -/
theorem muFinQuat_lamHat_eq (ha : a ≠ 0) (hb : b ≠ 0) :
    muFinQuat (a : F) (b : F) (lamHatUnits (a : F) (b : F)) =
      ((quatCong ha hb).relIndex (lamHatSub a b) : ℝ≥0∞) * muFinQuat (a : F) (b : F) (quatCong ha hb) := by
  have := isHaarMeasure_muFinQuat' ha hb
  have h := Measure.measure_subgroup_eq_relIndex_mul (muFinQuat (a : F) (b : F)) (A := lamHatSub a b)
    (B := quatCong ha hb) (isOpen_quatCong ha hb) (quatCong_le ha hb) (relIndex_quatCong_ne_zero ha hb)
  exact h

/-- $\mu_f(c(\hat\Lambda^\times)) = [\hat\Lambda^\times : H_S]\,\mu_f(c(H_S))$. -/
theorem muFin_lamHatSO_eq (ha : a ≠ 0) (hb : b ≠ 0) :
    QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) (lamHatSO a b : Set (SOAf Q₀)) =
      ((quatCong ha hb).relIndex (lamHatSub a b) : ℝ≥0∞) *
        QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) ((quatCong ha hb).map (conjFin a b) : Set (SOAf Q₀)) := by
  unfold lamHatSO
  rw [← relIndex_map_eq_of_ker_le (conjFin a b) (quatCong_le ha hb) (lamHat_inf_ker_le ha hb)]
  refine Measure.measure_subgroup_eq_relIndex_mul _ (isOpen_map_conjFin ha hb (isOpen_quatCong ha hb))
    (Subgroup.map_mono (quatCong_le ha hb)) ?_
  rw [relIndex_map_eq_of_ker_le (conjFin a b) (quatCong_le ha hb) (lamHat_inf_ker_le ha hb)]
  exact relIndex_quatCong_ne_zero ha hb

theorem muFinQuat_quatCong (ha : a ≠ 0) (hb : b ≠ 0) :
    muFinQuat (a : F) (b : F) (quatCong ha hb) = ENNReal.ofReal (quatHatVol (a : F) (b : F)) *
      ∏ v ∈ badSet ha hb, omegaQuatV v (a : F) (b : F) (congU ha hb v) /
        omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v) := by
  rw [coe_quatCong]
  exact muFinQuat_quatBox_of_measurable (intA a) (intA b) (by exact_mod_cast ha) (by exact_mod_cast hb) _ _
    fun v _ => (isOpen_lamCong v _ _).measurableSet

theorem measurableSet_congSO (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (congSO ha hb v) :=
  ((LerayPadic.isOpen_congSub v Q₀ _ _).preimage continuous_subtype_val).measurableSet

theorem muFin_map_quatCong (ha : a ≠ 0) (hb : b ≠ 0) :
    QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) ((quatCong ha hb).map (conjFin a b) : Set (SOAf Q₀)) =
      ENNReal.ofReal (QuadFormsKB.Tamagawa.Measure.finFactor Q₀ fun _ => 1) *
        ∏ v ∈ badSet ha hb, Measure.muLocSO v Q₀ 1 (congSO ha hb v) /
          Measure.muLocSO v Q₀ 1 (Measure.soStabSO v Q₀ : Set (Measure.SOv v Q₀)) := by
  rw [coe_map_quatCong]
  exact QuadFormsKB.Tamagawa.Measure.muFin_boxSO Q₀ (nondegenerate_pureFormO a b ha hb) (fun _ => one_pos) _ _
    fun v _ => measurableSet_congSO ha hb v

/-- On $SO$, the gauge-form measure of $K_m$ is that of `muLoc` ($K_m \subseteq SO$ by `map_lamCong`). -/
theorem muLocSO_congSO (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Measure.muLocSO v Q₀ 1 (congSO ha hb v) =
      Measure.muLoc v Q₀ 1 (LerayPadic.congSub v Q₀ (mLev ha hb v) (one_le_mLev ha hb v) : Set _) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  rw [Measure.muLocSO_eq_comap v Q₀ hQ (by norm_num) one_pos,
    (Measure.measurableEmbedding_soSub v Q₀ hQ).comap_apply]
  congr 1
  rw [congSO, Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left]
  intro g hg
  rw [← map_lamCong v a b ha hb (valued_two_eq v) (valued_eExp a ha v) (by unfold mLev; omega)
    (by unfold mLev; omega) (one_le_mLev ha hb v)] at hg
  obtain ⟨u, -, rfl⟩ := hg
  exact conjOrth_mem_soSub QF (hQF a b) u

/-! ### Weil's quotient measure on $PD^\times(\mathbb A_f)$ -/

variable (a b) in
/-- The normalizing constant $\mu_{D^\times}(\hat\Lambda^\times)/\mu_{G_m}(\hat{\mathcal O}^\times) =
\prod_v\lambda_v^{-1}\omega^{D^\times}_v(\Lambda_v^\times)/\prod_v\lambda_v^{-1}\omega^{G_m}_v(\mathcal O_v^\times)$. -/
def cPD : ℝ≥0∞ := muFinQuat (a : F) (b : F) (lamHatUnits (a : F) (b : F)) / muFinUnits F (OHatUnits F)

variable (a b) in
/-- **The finite ratio** $r_f = c_{PD}/\mu_f(c(\hat\Lambda^\times))$. -/
def rF : ℝ≥0∞ := cPD a b / QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) (lamHatSO a b : Set (SOAf Q₀))

/-- **Weil's quotient Tamagawa measure on $PD^\times(\mathbb A_f) = (D\otimes\mathbb A_f)^\times/\mathbb A_f^\times$**: the Haar
measure giving the image $J$ of $\hat\Lambda^\times$ the mass $\mu_{D^\times}(\hat\Lambda^\times)/\mu_{G_m}(\hat{\mathcal O}^\times)$
(`muPDFin_image_lamHat`), i.e. $\prod_v\lambda_v^{-1}\omega_v^{D^\times}/\prod_v\lambda_v^{-1}\omega_v^{G_m}$ (the convergence
factors cancel). It is realized as a multiple of the transport of `muFin` (a Haar measure) along
$PD^\times(\mathbb A_f) \cong SO(V)(\mathbb A_f)$; the normalization on $J$ is what determines it. -/
@[kb "weil1982" "§2.3, p. 21; §3.7(a), p. 63"]
def muPDFin (ha : a ≠ 0) (hb : b ≠ 0) : Measure (PDFin a b) :=
  rF a b • (QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1)).map (pdFinEquiv a b ha hb).symm

/-! ### Computing $r_f$ -/

/-- $r_f = \mu_{D^\times}(H_S)/(\mu_{G_m}(\hat{\mathcal O}^\times)\,\mu_f(c(H_S)))$ (the index $[\hat\Lambda^\times : H_S]$
cancels). -/
theorem rF_eq_div (ha : a ≠ 0) (hb : b ≠ 0) :
    rF a b = muFinQuat (a : F) (b : F) (quatCong ha hb) / (muFinUnits F (OHatUnits F) *
      QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) ((quatCong ha hb).map (conjFin a b) : Set (SOAf Q₀))) := by
  unfold rF cPD
  rw [muFinQuat_lamHat_eq ha hb, muFin_lamHatSO_eq ha hb]
  set N := ((quatCong ha hb).relIndex (lamHatSub a b) : ℝ≥0∞)
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (relIndex_quatCong_ne_zero ha hb)
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hU0 : muFinUnits F (OHatUnits F) ≠ 0 := by
    rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'
  have hUt : muFinUnits F (OHatUnits F) ≠ ⊤ := by rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top
  set X := muFinQuat (a : F) (b : F) (quatCong ha hb)
  set U := muFinUnits F (OHatUnits F)
  set Y := QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) ((quatCong ha hb).map (conjFin a b) : Set (SOAf Q₀))
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hN0) (Or.inl hNt)]
  calc (N⁻¹ * Y⁻¹) * (U⁻¹ * (N * X)) = (N * N⁻¹) * ((U * Y)⁻¹ * X) := by
        rw [ENNReal.mul_inv (Or.inl hU0) (Or.inl hUt)]
        ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hN0 hNt, one_mul]

/-- The local ratio at a place, in real numbers ($q = N(v)$, $\nu_v = \mathrm{vol}(\mathfrak o_v)$). -/
theorem local_ratio_real (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    (omegaQuatV v (a : F) (b : F) (congU ha hb v)).toReal *
        (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * (sExp v + eExp a ha v + eExp b hb v)) =
      (omegaV v (unitsVSub v)).toReal * (Analysis.selfDualV v).real (Analysis.latticeV v 0) ^ 3 *
        (Measure.muLocSO v Q₀ 1 (congSO ha hb v)).toReal := by
  have h := omegaQuatV_lamCong_mul v a b ha hb (valued_two_eq v) (valued_eExp a ha v) (valued_eExp b hb v)
    (m := mLev ha hb v) le_rfl
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast] at h'
  rw [muLocSO_congSO ha hb v]
  exact h'

theorem omegaQuatV_congU_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    omegaQuatV v (a : F) (b : F) (congU ha hb v) ≠ 0 :=
  (isOpen_lamCong v _ _).measure_ne_zero _ ⟨1, Subgroup.one_mem _⟩

theorem omegaQuatV_congU_ne_top (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    omegaQuatV v (a : F) (b : F) (congU ha hb v) ≠ ⊤ :=
  ((measure_mono fun _ hu => hu.2).trans_lt (isCompact_lamLocUnits (a : F) (b : F) v).measure_lt_top).ne

theorem muLocSO_congSO_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Measure.muLocSO v Q₀ 1 (congSO ha hb v) ≠ 0 := by
  rw [muLocSO_congSO]
  have := Measure.isHaarMeasure_muLoc v Q₀ (nondegenerate_pureFormO a b ha hb) one_pos
  exact (LerayPadic.isOpen_congSub v Q₀ _ _).measure_ne_zero _ ⟨1, Subgroup.one_mem _⟩

theorem muLocSO_congSO_ne_top (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    Measure.muLocSO v Q₀ 1 (congSO ha hb v) ≠ ⊤ := by
  rw [muLocSO_congSO]
  have := Measure.isHaarMeasure_muLoc v Q₀ (nondegenerate_pureFormO a b ha hb) one_pos
  exact ((measure_mono (LerayPadic.congSub_le_stdStab v Q₀ _ _)).trans_lt
    (Measure.isCompact_stdStab v QF).measure_lt_top).ne

theorem muLocSO_soStabSO_toReal (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    0 < (Measure.muLocSO v Q₀ 1 (Measure.soStabSO v Q₀ : Set (Measure.SOv v Q₀))).toReal := by
  rw [Measure.muLocSO_soStabSO, div_one, ENNReal.toReal_ofReal
    (QuadFormsKB.Tamagawa.Measure.siegelDensity_self_pos' Q₀ (nondegenerate_pureFormO a b ha hb) v).le]
  exact QuadFormsKB.Tamagawa.Measure.siegelDensity_self_pos' Q₀ (nondegenerate_pureFormO a b ha hb) v

theorem selfDualV_real_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < (Analysis.selfDualV v).real (Analysis.latticeV v 0) := by
  rw [Measure.real, ← coe_adicCompletionIntegers_eq]
  exact ENNReal.toReal_pos (volO_pos v).ne' (volO_ne_top v)

theorem lamV_inv_mul_omegaV_real (v : HeightOneSpectrum (𝓞 F)) :
    (lamV v)⁻¹ * (omegaV v (unitsVSub v)).toReal = (Analysis.selfDualV v).real (Analysis.latticeV v 0) := by
  have h := congrArg ENNReal.toReal (lamV_inv_mul_omegaV_unitsVSub v)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (lamV_pos v).le), volO_eq_ofReal,
    ENNReal.toReal_ofReal measureReal_nonneg] at h
  exact h

theorem quatLocalFactor_eq_real (v : HeightOneSpectrum (𝓞 F)) :
    quatLocalFactor (a : F) (b : F) v =
      (lamV v)⁻¹ * (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal := by
  rw [quatLocalFactor, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (lamV_pos v).le)]

/-- **The finite ratio $r_f$ in closed form:** $r_f = \prod_{v\in S}\mathrm{vol}(\mathfrak o_v)^3\,q_v^{-3(s_v+e_a(v)+e_b(v))}$
over the bad places, i.e. $\prod_v|8a^3b^3|_v\,\mathrm{vol}(\mathfrak o_v)^3$. -/
theorem rF_toReal (ha : a ≠ 0) (hb : b ≠ 0) :
    (rF a b).toReal = ∏ v ∈ badSet ha hb, (Analysis.selfDualV v).real (Analysis.latticeV v 0) ^ 3 /
      (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * (sExp v + eExp a ha v + eExp b hb v)) := by
  have hQ := nondegenerate_pureFormO a b ha hb
  set S := badSet ha hb
  set Q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => quatLocalFactor (a : F) (b : F) v
  set ν : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Analysis.selfDualV v).real (Analysis.latticeV v 0)
  set μL : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (Measure.muLocSO v Q₀ 1 (Measure.soStabSO v Q₀ : Set (Measure.SOv v Q₀))).toReal
  have hsplit := tprod_eq_prod_mul_finprod_mul_tprod Q ν μL S (mulSupport_volO_real_finite (F := F))
    (QuadFormsKB.Tamagawa.Measure.multipliable_muLocSO_one Q₀ hQ (by norm_num) (by norm_num))
    (fun v _ => (mul_pos (selfDualV_real_pos v) (muLocSO_soStabSO_toReal ha hb v)).ne')
    (fun v hv => by
      obtain ⟨-, -, -, hvol, hgood⟩ := goodPlace_of_not_mem_badSet ha hb hv
      simp only [Q, ν, μL, hvol, one_mul, hgood]
      rw [ENNReal.toReal_ofReal (quatLocalFactor_pos _ _ v).le])
  have hQH : quatHatVol (a : F) (b : F) = ∏' v, Q v := rfl
  have hFF : QuadFormsKB.Tamagawa.Measure.finFactor Q₀ (fun _ => 1) = ∏' v, μL v := rfl
  have hOH : ohatVol F = ∏ᶠ v, ν v := ohatVol_eq_finprod
  have hQHpos := quatHatVol_pos (intA a) (intA b) (by exact_mod_cast ha : (a : F) ≠ 0)
    (by exact_mod_cast hb : (b : F) ≠ 0)
  have hOHpos : 0 < ohatVol F := ohatVol_pos
  have hFF0 : QuadFormsKB.Tamagawa.Measure.finFactor Q₀ (fun _ => 1) ≠ 0 := by
    intro h0
    rw [hQH, hsplit, ← hOH, ← hFF, h0, mul_zero, mul_zero] at hQHpos
    exact lt_irrefl _ hQHpos
  have hFFnn := QuadFormsKB.Tamagawa.Measure.finFactor_nonneg Q₀ (fun _ => 1)
  rw [rF_eq_div ha hb, muFinQuat_quatCong ha hb, muFin_map_quatCong ha hb, muFinUnits_OHatUnits]
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hQHpos.le,
    ENNReal.toReal_ofReal hOHpos.le, ENNReal.toReal_ofReal hFFnn, ENNReal.toReal_prod, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_div]
  rw [hQH, hsplit, ← hOH, ← hFF, mul_div_assoc]
  set P := ∏ v ∈ S, Q v / (ν v * μL v)
  set OH := ohatVol F
  set FF := QuadFormsKB.Tamagawa.Measure.finFactor Q₀ (fun _ => 1)
  rw [show P * (OH * FF) * ((∏ v ∈ S, (omegaQuatV v (a : F) (b : F) (congU ha hb v)).toReal /
        (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal) /
      (OH * (FF * ∏ v ∈ S, (Measure.muLocSO v Q₀ 1 (congSO ha hb v)).toReal / μL v))) =
      P * (∏ v ∈ S, (omegaQuatV v (a : F) (b : F) (congU ha hb v)).toReal /
        (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal) /
      (∏ v ∈ S, (Measure.muLocSO v Q₀ 1 (congSO ha hb v)).toReal / μL v) by
    field_simp]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hloc := local_ratio_real ha hb v
  have hΩ := lamV_inv_mul_omegaV_real v
  have hQv : Q v = (lamV v)⁻¹ * (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal :=
    quatLocalFactor_eq_real v
  have hωL : (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨omegaQuatV_lamLocUnits_ne_zero _ _ v, omegaQuatV_lamLocUnits_ne_top _ _ v⟩
  have hμK : (Measure.muLocSO v Q₀ 1 (congSO ha hb v)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨muLocSO_congSO_ne_zero ha hb v, muLocSO_congSO_ne_top ha hb v⟩
  have hμL : μL v ≠ 0 := (muLocSO_soStabSO_toReal ha hb v).ne'
  have hν : ν v ≠ 0 := (selfDualV_real_pos v).ne'
  have hlam : lamV v ≠ 0 := (lamV_pos v).ne'
  have hq : (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ≠ 0 := by
    exact_mod_cast (LocalZeta.q_pos v).ne'
  set ωC := (omegaQuatV v (a : F) (b : F) (congU ha hb v)).toReal
  set ωL := (omegaQuatV v (a : F) (b : F) (lamLocUnits (a : F) (b : F) v)).toReal
  set μK := (Measure.muLocSO v Q₀ 1 (congSO ha hb v)).toReal
  set Ω := (omegaV v (unitsVSub v)).toReal
  set qe := (LocalDensity.DVR.q (v.adicCompletionIntegers F) : ℝ) ^ (3 * (sExp v + eExp a ha v + eExp b hb v))
  have hqe : qe ≠ 0 := pow_ne_zero _ hq
  have hΩ' : Ω = lamV v * ν v := by
    have : (lamV v)⁻¹ * Ω = ν v := hΩ
    field_simp at this
    linarith
  rw [hΩ'] at hloc
  have hloc' : ωC * qe = lamV v * ν v * ν v ^ 3 * μK := hloc
  rw [hQv]
  calc (lamV v)⁻¹ * ωL / (ν v * μL v) * (ωC / ωL) / (μK / μL v) = (lamV v)⁻¹ * ωC / (ν v * μK) := by
        field_simp
    _ = ν v ^ 3 / qe := by
        rw [div_eq_div_iff (mul_ne_zero hν hμK) hqe, mul_assoc, hloc']
        field_simp

theorem rF_toReal_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < (rF a b).toReal := by
  rw [rF_toReal ha hb]
  exact Finset.prod_pos fun v _ => div_pos (pow_pos (selfDualV_real_pos v) 3)
    (pow_pos (by exact_mod_cast LocalZeta.q_pos v) _)

theorem rF_ne_top (ha : a ≠ 0) (hb : b ≠ 0) : rF a b ≠ ⊤ := fun h => by
  have := rF_toReal_pos ha hb; rw [h, ENNReal.toReal_top] at this; exact lt_irrefl _ this

theorem rF_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : rF a b ≠ 0 := fun h => by
  have := rF_toReal_pos ha hb; rw [h, ENNReal.toReal_zero] at this; exact lt_irrefl _ this

theorem measurable_pdFinEquiv (ha : a ≠ 0) (hb : b ≠ 0) :
    Measurable (⇑(pdFinEquiv a b ha hb) : PDFin a b → SOAf Q₀) := (map_continuous _).measurable

theorem measurable_pdFinEquiv_symm (ha : a ≠ 0) (hb : b ≠ 0) :
    Measurable (⇑(pdFinEquiv a b ha hb).symm : SOAf Q₀ → PDFin a b) := (map_continuous _).measurable

/-- **The image of `muPDFin` in $SO(V)(\mathbb A_f)$ is $r_f\cdot\mu_f$** (the hypothesis hF, discharged). -/
@[kb "weil1982" "§2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem map_muPDFin (ha : a ≠ 0) (hb : b ≠ 0) :
    (muPDFin ha hb).map (pdFinEquiv a b ha hb) = rF a b • QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) := by
  rw [muPDFin, Measure.map_smul,
    Measure.map_map (measurable_pdFinEquiv ha hb) (measurable_pdFinEquiv_symm ha hb)]
  · congr 1
    convert Measure.map_id
    funext x
    simp
  · exact (measurable_pdFinEquiv ha hb).aemeasurable

instance (ha : a ≠ 0) (hb : b ≠ 0) : SFinite (muPDFin ha hb) := by
  unfold muPDFin; infer_instance

instance (ha : a ≠ 0) (hb : b ≠ 0) : (muPDFin ha hb).IsMulLeftInvariant := by
  unfold muPDFin
  have := isMulLeftInvariant_map (μ := QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1))
    (pdFinEquiv a b ha hb).symm.toMulEquiv.toMonoidHom.toMulHom (measurable_pdFinEquiv_symm ha hb)
    (pdFinEquiv a b ha hb).symm.surjective
  have : (Measure.map (⇑(pdFinEquiv a b ha hb).symm)
    (QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1))).IsMulLeftInvariant := this
  infer_instance

theorem cPD_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : cPD a b ≠ 0 := by
  unfold cPD
  refine (ENNReal.div_pos ?_ ?_).ne'
  · rw [muFinQuat_lamHatUnits]
    exact (ENNReal.ofReal_pos.mpr (quatHatVol_pos (intA a) (intA b) (by exact_mod_cast ha)
      (by exact_mod_cast hb))).ne'
  · rw [muFinUnits_OHatUnits]; exact ENNReal.ofReal_ne_top

theorem cPD_ne_top : cPD a b ≠ ⊤ := by
  unfold cPD
  refine ENNReal.div_ne_top ?_ ?_
  · rw [muFinQuat_lamHatUnits]; exact ENNReal.ofReal_ne_top
  · rw [muFinUnits_OHatUnits]; exact (ENNReal.ofReal_pos.mpr ohatVol_pos).ne'

/-- **The normalization of `muPDFin`:** the image $J$ of $\hat\Lambda^\times$ in $PD^\times(\mathbb A_f)$ has mass
$\mu_{D^\times}(\hat\Lambda^\times)/\mu_{G_m}(\hat{\mathcal O}^\times)$. -/
theorem muPDFin_image_lamHat (ha : a ≠ 0) (hb : b ≠ 0) :
    muPDFin ha hb ((QuotientGroup.mk : (QuatFin (a : F) (b : F))ˣ → PDFin a b) '' lamHatUnits (a : F) (b : F)) =
      cPD a b := by
  have himg : (pdFinEquiv a b ha hb).symm ⁻¹' ((QuotientGroup.mk : (QuatFin (a : F) (b : F))ˣ → PDFin a b) ''
      lamHatUnits (a : F) (b : F)) = (lamHatSO a b : Set (SOAf Q₀)) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_image, lamHatSO, Subgroup.coe_map, SetLike.mem_coe]
    constructor
    · rintro ⟨u, hu, hug⟩
      refine ⟨u, hu, ?_⟩
      have := congrArg (pdFinEquiv a b ha hb) hug
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [eq_comm, ContinuousMulEquiv.symm_apply_eq]
      rfl
  have hmeas : MeasurableSet ((QuotientGroup.mk : (QuatFin (a : F) (b : F))ˣ → PDFin a b) ''
      lamHatUnits (a : F) (b : F)) :=
    (QuotientGroup.isOpenMap_coe _ (isOpen_lamHatUnits (a : F) (b : F))).measurableSet
  set K := QuadFormsKB.Tamagawa.Measure.muFin Q₀ (fun _ => 1) (lamHatSO a b : Set (SOAf Q₀))
  have hK0 : K ≠ 0 := fun h0 => rF_ne_top ha hb (by
    rw [rF]; show cPD a b / K = ⊤; rw [h0]; exact ENNReal.div_zero (cPD_ne_zero ha hb))
  have hKt : K ≠ ⊤ := fun ht => rF_ne_zero ha hb (by
    rw [rF]; show cPD a b / K = 0; rw [ht]; exact ENNReal.div_top)
  rw [muPDFin, Measure.smul_apply, Measure.map_apply (measurable_pdFinEquiv_symm ha hb) hmeas, himg, smul_eq_mul,
    rF, ENNReal.div_mul_cancel hK0 hKt]

end Global

end QuadFormsKB.Tamagawa.Measure.Weil
