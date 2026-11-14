import QuadFormsKB.Tamagawa.Measure.Weil.SLnInduct

/-!
# Siegel's mean value theorem for $\mathrm{SL}_n$ and finiteness of $\tau(\mathrm{SL}_n)$

$F$ a number field, $n = k + 2$, $\mu_n$ = `muSL F (k + 1)` the Tamagawa measure of $\mathrm{SL}_n(\mathbb A_F)$
(`SLnInduct.lean`), $\tau_m = \operatorname{covol}(\mathrm{SL}_m(F)\backslash\mathrm{SL}_m(\mathbb A_F), \mu_m)$ (`tauSL`).

* **`lintegral_tsum_mulVec_eqN`** (Siegel's mean value theorem; Weil 1982, Lemma 2.4.2 and Thm 2.4.3): for every
  fundamental domain $D$ of $G_{\mathbb A}/G_k$ and every measurable $f\ge0$ on $\mathbb A_F^n$,
  $$\int_D\sum_{\xi\in F^n\setminus0}f(g\xi)\,d\mu_n(g) = \tau_{n-1}\int_{\mathbb A_F^n}f(y)\,dy .$$
  *Proof:* $\mathrm{SL}_n(F)$ is transitive on $F^n\setminus0$ (the local section `secM` over $F$) with stabilizer
  $P(F) = F^{n-1}\rtimes\mathrm{SL}_{n-1}(F)$ at $e_0$; unfold (`lintegral_orbit_unfold`) to an exact fundamental domain
  $E$ of $P(F)$, which in the coordinates $g = s(y)\operatorname{blk}(h, c)$ is $\{h\in D_{n-1},\ c\in D_{\mathbb A}^{n-1}\}$;
  the integral is $\int_X f\,dy\cdot\mu_{n-1}(D_{n-1})\cdot\operatorname{vol}(\mathbb A^{n-1}/F^{n-1})$, and
  $\operatorname{vol}(\mathbb A^{n-1}/F^{n-1}) = 1$.
* **`tauSL_lt_top`, `tauSL_ne_zero`**: $0 < \tau_n < \infty$ for every $n$ (by induction; finiteness from adelic
  Minkowski, `exists_isCompact_forall_SL_mulVec_mem`, as for $n = 2$).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology NumberField.mixedEmbedding Matrix
open scoped ENNReal NNReal Classical MatrixGroups

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil.SLn

noncomputable section

variable {F : Type} [Field F] [NumberField F] {k : ℕ}

variable (F) in
/-- **The Tamagawa number** $\tau(\mathrm{SL}_{k+1}) = \operatorname{vol}(\mathrm{SL}_{k+1}(\mathbb A_F)/\mathrm{SL}_{k+1}(F))$
for the measure `muSL F k`. -/
def tauSL (k : ℕ) : ℝ≥0∞ :=
  covolume (Matrix.SpecialLinearGroup (Fin (k + 1)) F) (SLnA F (Fin (k + 1))) (muSL F k)

instance (μ : Measure (SLnA F (Fin (k + 1)))) :
    HasFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 1)) F) (SLnA F (Fin (k + 1))) μ := by
  obtain ⟨D, hD, h⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin (k + 1))
  exact ⟨⟨D, IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩⟩

theorem tauSL_eq {D : Set (SLnA F (Fin (k + 1)))}
    (hD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 1)) F) D (muSL F k)) : tauSL F k = muSL F k D :=
  hD.covolume_eq_volume

/-! ### The nonzero vectors of $F^n$ -/

variable (F k) in
/-- The nonzero vectors of $F^n$, $n = k + 2$. -/
def NZ : Type := {ξ : Fin (k + 2) → F // ξ ≠ 0}

theorem mulVec_ne_zero_SL (γ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) {ξ : Fin (k + 2) → F} (hξ : ξ ≠ 0) :
    (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ ≠ 0 := by
  intro h
  apply hξ
  have e : ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *
      (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc ξ = (((γ⁻¹ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *
        (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F)) *ᵥ ξ := by rw [e, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h, mulVec_zero]

instance : MulAction (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (NZ F k) where
  smul γ ξ := ⟨(γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ.1, mulVec_ne_zero_SL γ ξ.2⟩
  one_smul ξ := Subtype.ext (by show (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ.1 = ξ.1; rw [one_mulVec])
  mul_smul γ δ ξ := Subtype.ext (by
    show ((γ * δ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ.1 =
      (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ((δ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ.1)
    rw [mulVec_mulVec]; rfl)

theorem NZ.smul_val (γ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) (ξ : NZ F k) :
    (γ • ξ).1 = (γ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ ξ.1 := rfl

instance : Countable (NZ F k) := Subtype.countable

variable (F k) in
/-- $e_0\in F^n\setminus0$. -/
def e0F : NZ F k := ⟨Pi.single 0 1, fun h => by simpa using congrFun h 0⟩

/-- **$\mathrm{SL}_n(F)$ is transitive on $F^n\setminus0$** (the local section with $B = F$). -/
theorem exists_smul_e0F (ξ : NZ F k) : ∃ γ : Matrix.SpecialLinearGroup (Fin (k + 2)) F, γ • e0F F k = ξ := by
  have hpiv : ∃ i, PivP (Set.univ : Set F) ξ.1 i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp ξ.2
    exact ⟨i, hi, fun _ => Set.mem_univ _⟩
  refine ⟨⟨secM Set.univ ξ.1, det_secM hpiv⟩, Subtype.ext ?_⟩
  show secM Set.univ ξ.1 *ᵥ Pi.single 0 1 = ξ.1
  funext r
  rw [mulVec_single_one]
  exact secM_col _ _ r

theorem slnEmb_mulVec_diagVec {m : ℕ} (γ : Matrix.SpecialLinearGroup (Fin m) F) (ξ : Fin m → F) :
    (slnEmb F (Fin m) γ : Matrix (Fin m) (Fin m) (Adeles F)) *ᵥ diagVec F (Fin m) ξ =
      diagVec F (Fin m) ((γ : Matrix (Fin m) (Fin m) F) *ᵥ ξ) := by
  funext i
  exact (RingHom.map_mulVec (diagRing F) (γ : Matrix (Fin m) (Fin m) F) ξ i).symm

/-! ### Siegel's mean value theorem -/

/-- The fibre coordinate of $g\,q$ for $q$ in the stabilizer. -/
theorem fib_mul_stab (g : SLnA F (Fin (k + 2))) (q : (orbSec F k).stab) :
    (orbSec F k).fib (g * q) = (orbSec F k).fib g * q := by
  have hq : (q : SLnA F (Fin (k + 2))) • (orbSec F k).base = (orbSec F k).base := q.2
  refine Subtype.ext ?_
  simp only [OrbitSection.fib, Subgroup.coe_mul, mul_smul, hq, mul_assoc]

variable (F k) in
/-- The exact fundamental domain of $P(F)$: $\{g = s(y)\operatorname{blk}(h, c) : h\in D,\ c\in D_{\mathbb A}^{n-1}\}$. -/
def stabDomN (D : Set (SLnA F (Fin (k + 1)))) : Set (SLnA F (Fin (k + 2))) :=
  {g | stabInv ((orbSec F k).fib g) ∈ D ×ˢ fundDomVec F (Fin (k + 1))}

theorem measurableSet_stabDomN {D : Set (SLnA F (Fin (k + 1)))} (hD : MeasurableSet D) :
    MeasurableSet (stabDomN F k D) :=
  (hD.prod (MeasurableSet.univ_pi fun _ => measurableSet_fundDom)).preimage
    (measurable_stabInv.comp (orbSec F k).measurable_fib)

theorem stabInv_fib_slnEmb (g : SLnA F (Fin (k + 2))) (δ : Matrix.SpecialLinearGroup (Fin (k + 2)) F)
    (hδ : (δ : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    stabInv ((orbSec F k).fib (g * slnEmb F (Fin (k + 2)) δ)) =
      ((stabInv ((orbSec F k).fib g)).1 * slnEmb F (Fin (k + 1)) (lowBlkSL δ hδ),
        diagVec F (Fin (k + 1)) (topRow δ) + vecMul (stabInv ((orbSec F k).fib g)).2
          (slnEmb F (Fin (k + 1)) (lowBlkSL δ hδ) : Matrix (Fin (k + 1)) (Fin (k + 1)) (Adeles F))) := by
  have e : g * slnEmb F (Fin (k + 2)) δ = g * ((stabMap (slnEmb F (Fin (k + 1)) (lowBlkSL δ hδ),
      diagVec F (Fin (k + 1)) (topRow δ)) : (orbSec F k).stab) : SLnA F (Fin (k + 2))) := by
    rw [← slnEmb_mem_stab δ hδ]
  rw [e, fib_mul_stab]
  conv_lhs => rw [← stabMap_stabInv ((orbSec F k).fib g), stabMap_mul, stabInv_stabMap]

theorem stab_mulVec_e0 (s : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k)) :
    ((s : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 :=
  congrArg Subtype.val s.2

theorem stab_inv_mulVec_e0 (s : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k)) :
    ((s⁻¹ : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k)) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  stab_mulVec_e0 s⁻¹

/-- **Exactness of the fundamental domain of $P(F)$.** -/
theorem existsUnique_stab_smul_mem_stabDomN {D : Set (SLnA F (Fin (k + 1)))}
    (hD : ∀ h : SLnA F (Fin (k + 1)), ∃! γ : Matrix.SpecialLinearGroup (Fin (k + 1)) F, γ • h ∈ D)
    (g : SLnA F (Fin (k + 2))) :
    ∃! s : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k), s • g ∈ stabDomN F k D := by
  set h := (stabInv ((orbSec F k).fib g)).1
  set c := (stabInv ((orbSec F k).fib g)).2
  -- `s • g ∈ E` in terms of `s⁻¹ = blk δ ξ`
  have hmem : ∀ s : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k),
      s • g ∈ stabDomN F k D ↔
        h * slnEmb F (Fin (k + 1)) (lowBlkSL _ (stab_inv_mulVec_e0 s)) ∈ D ∧
        diagVec F (Fin (k + 1)) (topRow ((s⁻¹ : MulAction.stabilizer _ (e0F F k)) :
            Matrix (Fin (k + 2)) (Fin (k + 2)) F)) +
          vecMul c (slnEmb F (Fin (k + 1)) (lowBlkSL _ (stab_inv_mulVec_e0 s)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (Adeles F)) ∈ fundDomVec F (Fin (k + 1)) := by
    intro s
    have hs : s • g = g * slnEmb F (Fin (k + 2)) ((s⁻¹ : MulAction.stabilizer _ (e0F F k)) :
        Matrix.SpecialLinearGroup (Fin (k + 2)) F) := by
      show g * (slnEmb F (Fin (k + 2)) (s : Matrix.SpecialLinearGroup (Fin (k + 2)) F))⁻¹ = _
      rw [← map_inv]; rfl
    rw [hs, stabDomN, Set.mem_ofPred_eq, stabInv_fib_slnEmb g _ (stab_inv_mulVec_e0 s), Set.mem_prod]
  -- existence
  obtain ⟨γ', hγ', hγ'u⟩ := hD h
  set δ : Matrix.SpecialLinearGroup (Fin (k + 1)) F := γ'⁻¹
  obtain ⟨⟨_, ξ, rfl⟩, hξ, hξu⟩ := existsUnique_vadd_mem_fundDomVec
    (vecMul c (slnEmb F (Fin (k + 1)) δ : Matrix (Fin (k + 1)) (Fin (k + 1)) (Adeles F)))
  have hb : ((blk δ ξ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ
      Pi.single 0 1 = Pi.single 0 1 := blkM_mulVec_single _ _
  set t : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k) :=
    ⟨blk δ ξ, Subtype.ext hb⟩
  have hlow : ∀ (u : MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k))
      (hu : ((u : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) *ᵥ Pi.single 0 1 = Pi.single 0 1),
      u = t → lowBlkSL _ hu = δ ∧ topRow ((u : Matrix.SpecialLinearGroup (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) = ξ := by
    rintro u hu rfl
    exact ⟨Subtype.ext rfl, rfl⟩
  refine ⟨t⁻¹, ?_, fun s hs => ?_⟩
  · show t⁻¹ • g ∈ stabDomN F k D
    rw [hmem]
    have h1 := hlow (t⁻¹⁻¹) (stab_inv_mulVec_e0 t⁻¹) (inv_inv t)
    rw [h1.1, h1.2]
    refine ⟨?_, hξ⟩
    have : h * slnEmb F (Fin (k + 1)) δ = γ' • h := by
      show _ = h * (slnEmb F (Fin (k + 1)) γ')⁻¹
      rw [← map_inv]
    rw [this]; exact hγ'
  · have hs' : s • g ∈ stabDomN F k D := hs
    rw [hmem] at hs'
    obtain ⟨hs1, hs2⟩ := hs'
    set δ' := lowBlkSL _ (stab_inv_mulVec_e0 s)
    have hδ' : δ' = δ := by
      have : δ'⁻¹ • h ∈ D := by
        show h * (slnEmb F (Fin (k + 1)) δ'⁻¹)⁻¹ ∈ D
        rw [map_inv, inv_inv]; exact hs1
      have := hγ'u _ this
      show δ' = γ'⁻¹
      rw [← this, inv_inv]
    rw [hδ'] at hs2
    have hξ' := hξu ⟨_, _, rfl⟩ hs2
    have hξeq : topRow ((s⁻¹ : MulAction.stabilizer _ (e0F F k)) : Matrix (Fin (k + 2)) (Fin (k + 2)) F) = ξ :=
      diagVec_injective (congrArg Subtype.val hξ')
    have hsinv : s⁻¹ = t := by
      refine Subtype.ext ?_
      rw [eq_blk _ (stab_inv_mulVec_e0 s)]
      show blk δ' _ = blk δ ξ
      rw [hδ', hξeq]
    rw [← inv_inv s, hsinv]

/-! ### The integral over the fundamental domain of $P(F)$ -/

theorem col_ofCoord (p : PX F k × (orbSec F k).stab) :
    col ((orbSec F k).ofCoord p) = (p.1 : AdeleSpace F (Fin (k + 2))) := by
  have h := congrArg Subtype.val ((orbSec F k).ofCoord_smul p)
  rw [← h]
  exact (smul_e0X _).symm

theorem fib_ofCoord (p : PX F k × (orbSec F k).stab) : (orbSec F k).fib ((orbSec F k).ofCoord p) = p.2 :=
  congrArg Prod.snd ((orbSec F k).toCoord_ofCoord p)

theorem lintegral_nuX (f : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞) :
    ∫⁻ x, f (x : AdeleSpace F (Fin (k + 2))) ∂nuX F k = ∫⁻ y, f y ∂muAddVec F (Fin (k + 2)) := by
  have hemb := MeasurableEmbedding.subtype_coe (measurableSet_primSub (F := F) (k := k))
  show ∫⁻ x : {x // x ∈ (primSub F k : Set (AdeleSpace F (Fin (k + 2))))}, f x.1
    ∂((muAddVec F (Fin (k + 2))).comap Subtype.val) = _
  rw [← hemb.lintegral_map, hemb.map_comap, Subtype.range_coe_subtype,
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.mp muAddVec_compl_primSetN |>.mono
      fun y hy => by
        have : y ∈ primSetN F k := by simpa using hy
        exact this)]

/-- $\int_E f(ge_0)\,d\mu_n = \mu_{n-1}(D)\int_{\mathbb A^n}f\,dy$ (coordinates $g = s(y)\operatorname{blk}(h,c)$,
$\operatorname{vol}(D_{\mathbb A}^{n-1}) = 1$, $X$ conull). -/
theorem setLIntegral_stabDomN {D : Set (SLnA F (Fin (k + 1)))} (hDm : MeasurableSet D)
    (f : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g in stabDomN F k D, f (col g) ∂muSL F (k + 1) = muSL F k D * ∫⁻ y, f y ∂muAddVec F (Fin (k + 2)) := by
  have := sigmaFinite_muP (F := F) (muSL F k)
  have hE := measurableSet_stabDomN (k := k) hDm
  have hDF : MeasurableSet (D ×ˢ fundDomVec F (Fin (k + 1))) :=
    hDm.prod (MeasurableSet.univ_pi fun _ => measurableSet_fundDom)
  have hS : MeasurableSet (stabInv (F := F) (k := k) ⁻¹' (D ×ˢ fundDomVec F (Fin (k + 1)))) :=
    hDF.preimage measurable_stabInv
  rw [← lintegral_indicator hE, muSL_succ,
    (orbSec F k).lintegral_fibMeasure _ _
      ((show Measurable fun g => f (col g) from hf.comp measurable_col).indicator hE)]
  have hpt : ∀ (x : PX F k) (q : (orbSec F k).stab),
      (stabDomN F k D).indicator (fun g => f (col g)) ((orbSec F k).sec x * q) =
        f (x : AdeleSpace F (Fin (k + 2))) *
          (stabInv ⁻¹' (D ×ˢ fundDomVec F (Fin (k + 1)))).indicator 1 q := by
    intro x q
    have e : (orbSec F k).sec x * q = (orbSec F k).ofCoord (x, q) := rfl
    rw [e]
    by_cases hq : q ∈ stabInv ⁻¹' (D ×ˢ fundDomVec F (Fin (k + 1)))
    · have : (orbSec F k).ofCoord (x, q) ∈ stabDomN F k D := by
        rw [stabDomN, Set.mem_ofPred_eq, fib_ofCoord]; exact hq
      rw [Set.indicator_of_mem this, Set.indicator_of_mem hq, Pi.one_apply, mul_one, col_ofCoord]
    · have : (orbSec F k).ofCoord (x, q) ∉ stabDomN F k D := by
        intro h
        apply hq
        rwa [stabDomN, Set.mem_ofPred_eq, fib_ofCoord] at h
      rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hq, mul_zero]
  simp_rw [hpt]
  have hinner : ∀ x : PX F k, ∫⁻ q, f (x : AdeleSpace F (Fin (k + 2))) *
      (stabInv ⁻¹' (D ×ˢ fundDomVec F (Fin (k + 1)))).indicator 1 q ∂muP (muSL F k) =
      f (x : AdeleSpace F (Fin (k + 2))) * muSL F k D := by
    intro x
    rw [lintegral_const_mul _ (measurable_one.indicator hS), lintegral_indicator_one hS, muP,
      Measure.map_apply measurable_stabMap hS]
    have : stabMap ⁻¹' (stabInv ⁻¹' (D ×ˢ fundDomVec F (Fin (k + 1)))) = D ×ˢ fundDomVec F (Fin (k + 1)) := by
      ext p; simp only [Set.mem_preimage, stabInv_stabMap]
    rw [this, Measure.prod_prod, muAddVec_fundDomVec, mul_one]
  simp_rw [hinner]
  rw [lintegral_mul_const _ (show Measurable fun x : PX F k => f (x : AdeleSpace F (Fin (k + 2))) from
    hf.comp measurable_subtype_coe), lintegral_nuX, mul_comm]

instance smulInvariantMeasure_muSL' (k : ℕ) :
    SMulInvariantMeasure (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (SLnA F (Fin (k + 2))) (muSL F (k + 1)) :=
  smulInvariantMeasure_muSL (k + 1)

theorem diagVec_single : diagVec F (Fin (k + 2)) (Pi.single 0 1) = Pi.single 0 1 := by
  funext i
  by_cases hi : i = 0
  · subst hi; rw [diagVec_apply, Pi.single_eq_same, Pi.single_eq_same, ← diagRing_apply, map_one]
  · simp [hi, diagVec_apply]

/-- **Siegel's mean value theorem for $\mathrm{SL}_n$ over a number field**, $n = k + 2$: for every fundamental domain
$D$ of $\mathrm{SL}_n(\mathbb A_F)/\mathrm{SL}_n(F)$ and every measurable $f\ge0$ on $\mathbb A_F^n$,
$\int_D\sum_{\xi\in F^n\setminus0}f(g\xi)\,d\mu_n(g) = \tau(\mathrm{SL}_{n-1})\int_{\mathbb A_F^n}f\,dy$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.2 (unfolding) and Thm 2.4.3 [unverified pages]; Siegel's mean value theorem"]
theorem lintegral_tsum_mulVec_eqN {D : Set (SLnA F (Fin (k + 2)))}
    (hD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1)))
    (f : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g in D, ∑' ξ : NZ F k, f ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1)
      ∂muSL F (k + 1) = tauSL F k * ∫⁻ y, f y ∂muAddVec F (Fin (k + 2)) := by
  obtain ⟨D', hD'm, hD'⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin (k + 1))
  have hFD' : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 1)) F) D' (muSL F k) :=
    IsFundamentalDomain.mk' hD'm.nullMeasurableSet hD'
  have horb : ∀ ξ : NZ F k, ξ ∈ MulAction.orbit (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k) :=
    fun ξ => exists_smul_e0F ξ
  let e : MulAction.orbit (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k) ≃ NZ F k :=
    Equiv.subtypeUnivEquiv horb
  set Φ : NZ F k → SLnA F (Fin (k + 2)) → ℝ≥0∞ :=
    fun ξ g => f ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1)
  have hΦ : ∀ (γ : Matrix.SpecialLinearGroup (Fin (k + 2)) F) (ξ : NZ F k) (g : SLnA F (Fin (k + 2))),
      Φ (γ • ξ) (γ • g) = Φ ξ g := by
    intro γ ξ g
    simp only [Φ, NZ.smul_val, slnRight_smul_def, ← slnEmb_mulVec_diagVec, Matrix.SpecialLinearGroup.coe_mul,
      mulVec_mulVec]
    rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul _ (slnEmb F (Fin (k + 2)) γ), inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have hcol : ∀ g : SLnA F (Fin (k + 2)), Φ (e0F F k) g = f (col g) := fun g => by
    simp only [Φ, e0F, diagVec_single, col_eq_mulVec]
  have hmeas : Measurable (Φ (e0F F k)) := by
    rw [show Φ (e0F F k) = fun g => f (col g) from funext hcol]; exact hf.comp measurable_col
  calc ∫⁻ g in D, ∑' ξ : NZ F k, f ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ
        diagVec F (Fin (k + 2)) ξ.1) ∂muSL F (k + 1)
      = ∫⁻ g in D, ∑' ξ : MulAction.orbit (Matrix.SpecialLinearGroup (Fin (k + 2)) F) (e0F F k), Φ ξ g
          ∂muSL F (k + 1) := lintegral_congr fun g => (e.tsum_eq (fun ξ => Φ ξ g)).symm
    _ = ∫⁻ g in stabDomN F k D', Φ (e0F F k) g ∂muSL F (k + 1) :=
        lintegral_orbit_unfold (e0F F k) Φ hΦ hmeas hD (measurableSet_stabDomN hD'm)
          (existsUnique_stab_smul_mem_stabDomN hD')
    _ = ∫⁻ g in stabDomN F k D', f (col g) ∂muSL F (k + 1) := lintegral_congr fun g => hcol g
    _ = tauSL F k * ∫⁻ y, f y ∂muAddVec F (Fin (k + 2)) := by
        rw [setLIntegral_stabDomN hD'm f hf, tauSL_eq hFD']

/-! ### Finiteness and positivity -/

theorem muSL_fundDomain_lt_top (hτ : tauSL F k < ∞) {D : Set (SLnA F (Fin (k + 2)))}
    (hD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1))) :
    muSL F (k + 1) D < ∞ := by
  obtain ⟨K, hK, hKmem⟩ := exists_isCompact_forall_SL_mulVec_mem (F := F) (ι := Fin (k + 2))
  have hf : Measurable (K.indicator (1 : AdeleSpace F (Fin (k + 2)) → ℝ≥0∞)) :=
    measurable_one.indicator hK.isClosed.measurableSet
  have hone : ∀ g : SLnA F (Fin (k + 2)), (1 : ℝ≥0∞) ≤ ∑' ξ : NZ F k, K.indicator 1
      ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1) := by
    intro g
    obtain ⟨ξ, hξ, hmem⟩ := hKmem g
    calc (1 : ℝ≥0∞) = K.indicator 1 ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ
          diagVec F (Fin (k + 2)) (⟨ξ, hξ⟩ : NZ F k).1) := by rw [Set.indicator_of_mem hmem, Pi.one_apply]
      _ ≤ _ := ENNReal.le_tsum (f := fun ξ : NZ F k => K.indicator 1
          ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1)) ⟨ξ, hξ⟩
  calc muSL F (k + 1) D = ∫⁻ _ in D, 1 ∂muSL F (k + 1) := by simp
    _ ≤ ∫⁻ g in D, ∑' ξ : NZ F k, K.indicator 1
          ((g : Matrix (Fin (k + 2)) (Fin (k + 2)) (Adeles F)) *ᵥ diagVec F (Fin (k + 2)) ξ.1) ∂muSL F (k + 1) :=
        lintegral_mono fun g => hone g
    _ = tauSL F k * muAddVec F (Fin (k + 2)) K := by
        rw [lintegral_tsum_mulVec_eqN hD _ hf, lintegral_indicator_one hK.isClosed.measurableSet]
    _ < ∞ := ENNReal.mul_lt_top hτ hK.measure_lt_top

theorem muSL_fundDomain_ne_zero (hτ : tauSL F k ≠ 0) {D : Set (SLnA F (Fin (k + 2)))}
    (hD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1))) :
    muSL F (k + 1) D ≠ 0 := by
  intro h0
  have h := lintegral_tsum_mulVec_eqN hD (fun _ => 1) measurable_const
  rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure, lintegral_const, one_mul] at h
  have hA : muAddVec F (Fin (k + 2)) Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos (muAddVec F (Fin (k + 2))) Set.univ_nonempty).ne'
  exact (mul_ne_zero hτ hA) h.symm

theorem tauSL_zero : tauSL F 0 = 1 := by
  have hFD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin 1) F) (Set.univ : Set (SLnA F (Fin 1)))
      (muSL F 0) :=
    IsFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet fun g =>
      ⟨1, Set.mem_univ _, fun γ _ => Subsingleton.elim _ _⟩
  rw [tauSL_eq hFD, muSL_zero, Measure.dirac_apply_of_mem (Set.mem_univ _)]

/-- **$0 < \tau(\mathrm{SL}_{k+1}) < \infty$** for every $k$ (induction with Siegel's mean value theorem and adelic
Minkowski). -/
@[kb "weil1982" "§2.4, p. 23 (τ(G) finite) [unverified page]; Siegel's mean value argument"]
theorem tauSL_pos_lt_top : ∀ k, tauSL F k ≠ 0 ∧ tauSL F k < ∞
  | 0 => by rw [tauSL_zero]; exact ⟨one_ne_zero, ENNReal.one_lt_top⟩
  | k + 1 => by
    obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_right' (F := F) (ι := Fin (k + 2))
    have hFD : IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin (k + 2)) F) D (muSL F (k + 1)) :=
      IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
    have ih := tauSL_pos_lt_top k
    rw [tauSL_eq hFD]
    exact ⟨muSL_fundDomain_ne_zero ih.1 hFD, muSL_fundDomain_lt_top ih.2 hFD⟩

end

end QuadFormsKB.Tamagawa.Measure.Weil.SLn
