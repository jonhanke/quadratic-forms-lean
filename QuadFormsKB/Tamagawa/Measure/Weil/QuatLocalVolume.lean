import QuadFormsKB.Tamagawa.Measure.Weil.QuatFinite
import QuadFormsKB.Literature.HasseNorm.SquareClasses
import QuadFormsKB.LocalDensity.DVRTable2

/-!
# Local volumes $\omega_v(\Lambda_v^\times)$ for the standard order of $\mathbb H[F,a,b]$

$F$ a number field, $v$ a finite place, $q = N(v)$, $k_v$ the residue field, $dx_v$ the self-dual measure on $F_v$,
$\omega_v = \|\operatorname{nrd}x\|_v^{-2}dx_v$ on $(\mathbb H\otimes F_v)^\times$ (`omegaQuatV`), $a, b$ integral at $v$,
$\Lambda_v = \mathcal O_v\langle1,i,j,k\rangle$.

* **Reduction lemma** (`pi_selfDualV_res`, any $n$): for a predicate $P$ on $k_v^n$,
  $\operatorname{vol}\{c\in\mathcal O_v^n : P(\bar c)\} = \#\{r\in k_v^n : P(r)\}\cdot\operatorname{vol}(\varpi\mathcal O_v)^n
  = \#P\cdot q^{-n}\operatorname{vol}(\mathcal O_v)^n$ (fibres of the reduction are translates of $(\varpi\mathcal O_v)^n$).
* **`omegaQuatV_lamLocUnits_eq`**: $\omega_v(\Lambda_v^\times) = \operatorname{vol}\{c\in\mathcal O_v^4 :
  |c_0^2 - ac_1^2 - bc_2^2 + abc_3^2|_v = 1\}$ (on $\Lambda_v^\times$, $|\operatorname{nrd}|_v = 1$).
* **Split places** (`omegaQuatV_lamLocUnits_good`): if $v\nmid 2$ and $a, b\in\mathcal O_v^\times$, then
  $\omega_v(\Lambda_v^\times) = (1-q^{-1})(1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$. Here
  $\Lambda_v\cong M_2(\mathcal O_v)$ and this is $\#\mathrm{GL}_2(\mathbb F_q)/q^4 = (q^2-1)(q^2-q)/q^4$; the proof counts
  directly: $\#\{r\in k_v^4 : r_0^2 - \bar ar_1^2 - \bar br_2^2 + \bar a\bar br_3^2 = 0\} = q^3 + q^2 - q$ (Table 1 over
  $k_v$, `DVR.diagCountF_even`: the form has square discriminant $\bar a^2\bar b^2$).
  Hence **`lamV_inv_mul_omegaQuatV_good`**: $\lambda_v^{-1}\omega_v(\Lambda_v^\times) = (1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$.
* **Ramified places** (`omegaQuatV_lamLocUnits_ram`): if $v\nmid2$, $|a|_v < 1$ and $b\in\mathcal O_v^\times$ with $\bar b$
  a non-square (e.g. $v(a) = 1$: then $\Lambda_v$ is the maximal order $\mathcal O_D$ of the division algebra), then
  $\omega_v(\Lambda_v^\times) = (1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$ ($\bar Q = r_0^2 - \bar br_2^2$ is anisotropic).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Quaternion Pointwise Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Kv" => v.adicCompletion F
local notation "Ov" => v.adicCompletionIntegers F
local notation "kv" => IsLocalRing.ResidueField (v.adicCompletionIntegers F)

/-! ### The reduction map and the volume of its fibres -/

/-- The reduction $F_v\to k_v$ on $\mathcal O_v$, extended by $0$. -/
def resV (x : Kv) : kv := if h : x ∈ Ov then IsLocalRing.residue Ov ⟨x, h⟩ else 0

theorem resV_of_mem {x : Kv} (h : x ∈ Ov) : resV v x = IsLocalRing.residue Ov ⟨x, h⟩ := by
  rw [resV, dif_pos h]

theorem mem_latticeV_one_iff (x : Kv) : x ∈ Analysis.latticeV v 1 ↔ Valued.v x < 1 := by
  rw [Analysis.mem_latticeV]
  by_cases hx : Valued.v x = 0
  · rw [hx]; exact ⟨fun _ => zero_lt_one, fun _ => zero_le⟩
  · rw [← WithZero.exp_log hx, WithZero.exp_le_exp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega

theorem mem_O_of_mem_latticeV_one {x : Kv} (hx : x ∈ Analysis.latticeV v 1) : x ∈ Ov :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((mem_latticeV_one_iff v x).mp hx).le

theorem residue_eq_zero_iff (z : Ov) : IsLocalRing.residue Ov z = 0 ↔ Valued.v (z : Kv) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, HN.mem_maximalIdeal_iff]

/-- A chosen lift $k_v\to\mathcal O_v$ of the reduction. -/
def liftV (y : kv) : Ov := Function.surjInv IsLocalRing.residue_surjective y

theorem residue_liftV (y : kv) : IsLocalRing.residue Ov (liftV v y) = y :=
  Function.surjInv_eq IsLocalRing.residue_surjective y

/-- **The fibre of the reduction over $r$ is $\tilde r + (\varpi\mathcal O_v)^n$.** -/
theorem mem_fibre_iff {n : ℕ} (r : Fin n → kv) (c : Fin n → Kv) :
    ((∀ i, c i ∈ Ov) ∧ (fun i => resV v (c i)) = r) ↔
      (-(fun i => (liftV v (r i) : Kv)) + c) ∈ Set.pi univ fun _ => (Analysis.latticeV v 1 : Set Kv) := by
  simp only [Set.mem_pi, mem_univ, true_imp_iff, SetLike.mem_coe, Pi.add_apply, Pi.neg_apply]
  constructor
  · rintro ⟨hO, hr⟩ i
    rw [mem_latticeV_one_iff, neg_add_eq_sub]
    have h1 : resV v (c i) = r i := congrFun hr i
    rw [resV_of_mem v (hO i), ← residue_liftV v (r i), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
    exact h1
  · intro h
    have hO : ∀ i, c i ∈ Ov := fun i => by
      have := add_mem (liftV v (r i)).2 (mem_O_of_mem_latticeV_one v (h i))
      rwa [add_neg_cancel_left] at this
    refine ⟨hO, funext fun i => ?_⟩
    rw [resV_of_mem v (hO i), ← residue_liftV v (r i), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    have := (mem_latticeV_one_iff v _).mp (h i)
    rwa [neg_add_eq_sub] at this

/-- **Reduction lemma**: $\operatorname{vol}\{c\in\mathcal O_v^n : P(\bar c)\} = \#\{r : P(r)\}\cdot
\operatorname{vol}(\varpi\mathcal O_v)^n$. -/
theorem pi_selfDualV_res [Fintype kv] {n : ℕ} (P : (Fin n → kv) → Prop) :
    Measure.pi (fun _ : Fin n => Analysis.selfDualV v)
        {c | (∀ i, c i ∈ Ov) ∧ P fun i => resV v (c i)} =
      (Finset.univ.filter P).card * Analysis.selfDualV v (Analysis.latticeV v 1) ^ n := by
  set μ := Measure.pi (fun _ : Fin n => Analysis.selfDualV v)
  set Fib : (Fin n → kv) → Set (Fin n → Kv) := fun r => {c | (∀ i, c i ∈ Ov) ∧ (fun i => resV v (c i)) = r}
  have hset : {c : Fin n → Kv | (∀ i, c i ∈ Ov) ∧ P fun i => resV v (c i)} =
      ⋃ r ∈ Finset.univ.filter P, Fib r := by
    ext c
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop, Fib, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨_, h2, h1, rfl⟩, fun ⟨r, hr, h1, h2⟩ => ⟨h1, h2 ▸ hr⟩⟩
  have hfib : ∀ r, Fib r = (fun c => -(fun i => (liftV v (r i) : Kv)) + c) ⁻¹'
      Set.pi univ fun _ => (Analysis.latticeV v 1 : Set Kv) := by
    intro r; ext c; exact mem_fibre_iff v r c
  have hmeasP : MeasurableSet (Set.pi univ fun _ : Fin n => (Analysis.latticeV v 1 : Set Kv)) :=
    MeasurableSet.univ_pi fun _ => Analysis.measurableSet_latticeV v 1
  have hmeas : ∀ r, MeasurableSet (Fib r) := fun r => by
    rw [hfib]; exact (measurable_const_add _) hmeasP
  have hval : ∀ r, μ (Fib r) = Analysis.selfDualV v (Analysis.latticeV v 1) ^ n := by
    intro r
    rw [hfib, measure_preimage_add, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hset, measure_biUnion_finset (fun r _ r' _ hrr' => ?_) (fun r _ => hmeas r)]
  · rw [Finset.sum_congr rfl fun r _ => hval r, Finset.sum_const, nsmul_eq_mul]
  · exact Set.disjoint_left.mpr fun c h1 h2 => hrr' (h1.2.symm.trans h2.2)

/-- $\operatorname{vol}(\varpi\mathcal O_v) = q^{-1}\operatorname{vol}(\mathcal O_v)$. -/
theorem selfDualV_latticeV_one :
    Analysis.selfDualV v (Analysis.latticeV v 1) = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) * volO v := by
  have h0 : Analysis.selfDualV v (Analysis.latticeV v 0 : Set (v.adicCompletion F)) = volO v := by
    rw [volO, coe_adicCompletionIntegers_eq]
  rw [show (1 : ℤ) = 0 + 1 from rfl, Analysis.latticeV_succ, ← distribHaarChar_mul, ← Analysis.modV, h0,
    ← Analysis.modV_eq, ENNReal.ofReal_coe_nnreal]

theorem card_residueField_eq [Fintype kv] : (Fintype.card kv : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
  rw [← Nat.card_eq_fintype_card, HN.card_residueField]

/-! ### $\omega_v(\Lambda_v^\times)$ as the volume of $\{c\in\mathcal O_v^4 : |Q(c)|_v = 1\}$ -/

/-- The reduced norm form in the coordinates $1,i,j,k$: $Q(c) = c_0^2 - ac_1^2 - bc_2^2 + abc_3^2$. -/
def nrdForm {K : Type*} [CommRing K] (a b : K) (c : Fin 4 → K) : K :=
  c 0 ^ 2 - a * c 1 ^ 2 - b * c 2 ^ 2 + a * b * c 3 ^ 2

theorem nrdLoc_eq_nrdForm {K : Type*} [Field K] (a b : K) (x : QuatLoc a b) :
    nrdLoc a b x = nrdForm a b (quatLocCoord a b x) := by
  have hc : quatLocCoord a b x = ![x.re, x.imI, x.imJ, x.imK] := by
    ext i; fin_cases i <;> rfl
  rw [hc]
  simp only [nrdLoc, nrdForm, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  simp
  ring

variable {v} {a b : F}

/-- **$\omega_v(\Lambda_v^\times) = \operatorname{vol}\{c\in\mathcal O_v^4 : |Q(c)|_v = 1\}$** ($a, b$ integral). -/
theorem omegaQuatV_lamLocUnits_eq
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1) :
    omegaQuatV v a b (lamLocUnits a b v) =
      Measure.pi (fun _ : Fin 4 => Analysis.selfDualV v)
        {c | (∀ i, c i ∈ Ov) ∧ Valued.v (nrdForm (algebraMap F Kv a) (algebraMap F Kv b) c) = 1} := by
  set T := {c : Fin 4 → Kv | (∀ i, c i ∈ Ov) ∧ Valued.v (nrdForm (algebraMap F Kv a) (algebraMap F Kv b) c) = 1}
  have h1 : ∀ u ∈ lamLocUnits a b v, distribHaarChar (QuatV a b v) u = 1 := by
    intro u hu
    have hu' : nrdLocUnit _ _ u ∈ unitsVSub v := ((mem_lamLocUnits_iff ha hb u).mp hu).2
    rw [distribHaarChar_quatLoc, distribHaarChar_eq_one_of_mem_unitsVSub hu', one_pow]
  rw [omegaQuatV, omegaQuatLoc, unitsHaar_apply_of_forall_eq_one (isOpenEmbedding_val_quatLoc _ _)
    (continuous_distribHaarChar_quatLoc _ _ (continuous_distribHaarChar_adic v)) _
    (isOpen_lamLocUnits a b v).measurableSet h1]
  have himg : Units.val '' lamLocUnits a b v = quatLocCoord _ _ ⁻¹' T := by
    ext x
    simp only [mem_image, mem_preimage, T, mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hL, hn⟩ := (mem_lamLocUnits_iff ha hb u).mp hu
      rw [lamLoc_eq] at hL
      refine ⟨fun i => hL i (mem_univ i), ?_⟩
      rwa [← nrdLoc_eq_nrdForm]
    · rintro ⟨hL, hn⟩
      rw [← nrdLoc_eq_nrdForm] at hn
      have hn0 : nrdLoc _ _ x ≠ 0 := fun h0 => by rw [h0, map_zero] at hn; exact zero_ne_one hn
      obtain ⟨u, rfl⟩ := (isUnit_iff_nrdLoc_ne_zero _ _ x).mpr hn0
      refine ⟨u, (mem_lamLocUnits_iff ha hb u).mpr ⟨?_, hn⟩, rfl⟩
      rw [lamLoc_eq]
      exact fun i _ => hL i
  have hTm : MeasurableSet T := by
    have hO : MeasurableSet {c : Fin 4 → Kv | ∀ i, c i ∈ Ov} := by
      have : {c : Fin 4 → Kv | ∀ i, c i ∈ Ov} = Set.pi univ fun _ => (Ov : Set Kv) := by
        ext c; simp
      rw [this]
      exact MeasurableSet.univ_pi fun _ => (isOpen_adicCompletionIntegers v).measurableSet
    have hcont : Continuous fun c : Fin 4 → Kv => nrdForm (algebraMap F Kv a) (algebraMap F Kv b) c := by
      unfold nrdForm; fun_prop
    have hU : MeasurableSet {c : Fin 4 → Kv | Valued.v (nrdForm (algebraMap F Kv a) (algebraMap F Kv b) c) = 1} :=
      (measurableSet_unitsV v).preimage hcont.measurable
    exact hO.inter hU
  rw [himg, quatLocVol, Measure.map_apply (quatLocCLE _ _).symm.continuous.measurable
    (hTm.preimage (continuous_quatLocCoord _ _).measurable)]
  congr 1
  ext c
  simp only [mem_preimage]
  change (quatLocCoord _ _) ((quatLocCoord _ _).symm c) ∈ T ↔ c ∈ T
  rw [LinearEquiv.apply_symm_apply]

/-! ### Reduction of the norm form -/

variable (v)

theorem map_nrdForm {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (c : Fin 4 → R) :
    f (nrdForm a b c) = nrdForm (f a) (f b) (fun i => f (c i)) := by
  simp only [nrdForm, map_add, map_sub, map_mul, map_pow]

theorem nrdForm_mem_and_resV {α β : Kv} (hα : α ∈ Ov) (hβ : β ∈ Ov) {c : Fin 4 → Kv} (hc : ∀ i, c i ∈ Ov) :
    ∃ h : nrdForm α β c ∈ Ov, IsLocalRing.residue Ov ⟨_, h⟩ =
      nrdForm (IsLocalRing.residue Ov ⟨α, hα⟩) (IsLocalRing.residue Ov ⟨β, hβ⟩)
        (fun i => IsLocalRing.residue Ov ⟨c i, hc i⟩) := by
  have he : nrdForm α β c = ((nrdForm (⟨α, hα⟩ : Ov) ⟨β, hβ⟩ fun i => (⟨c i, hc i⟩ : Ov) : Ov) : Kv) := by
    have := map_nrdForm (v.adicCompletionIntegers F).subtype (⟨α, hα⟩ : Ov) ⟨β, hβ⟩ fun i => (⟨c i, hc i⟩ : Ov)
    exact this.symm
  refine ⟨he ▸ (nrdForm (⟨α, hα⟩ : Ov) ⟨β, hβ⟩ fun i => (⟨c i, hc i⟩ : Ov)).2, ?_⟩
  rw [← map_nrdForm]
  congr 1

theorem valued_eq_one_iff_residue_ne_zero (z : Ov) :
    Valued.v (z : Kv) = 1 ↔ IsLocalRing.residue Ov z ≠ 0 := by
  rw [Ne, residue_eq_zero_iff, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm z.2 h⟩

/-- On $\mathcal O_v^4$ (and $a, b\in\mathcal O_v$): $|Q(c)|_v = 1\iff\bar Q(\bar c)\ne0$. -/
theorem setOf_nrdForm_eq {α β : Kv} (hα : α ∈ Ov) (hβ : β ∈ Ov) :
    {c : Fin 4 → Kv | (∀ i, c i ∈ Ov) ∧ Valued.v (nrdForm α β c) = 1} =
      {c | (∀ i, c i ∈ Ov) ∧ nrdForm (resV v α) (resV v β) (fun i => resV v (c i)) ≠ 0} := by
  ext c
  simp only [mem_ofPred_eq]
  refine and_congr_right fun hc => ?_
  obtain ⟨h, hres⟩ := nrdForm_mem_and_resV v hα hβ hc
  rw [resV_of_mem v hα, resV_of_mem v hβ]
  simp_rw [resV_of_mem v (hc _)]
  rw [← hres, ← valued_eq_one_iff_residue_ne_zero v ⟨_, h⟩]

theorem ringChar_ne_two_of_valued_two (hv2 : Valued.v (2 : Kv) = 1) : ringChar kv ≠ 2 := by
  intro h
  have h2 : (2 : Kv) ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv2.le
  have hr := (valued_eq_one_iff_residue_ne_zero v ⟨2, h2⟩).mp hv2
  apply hr
  have : (⟨2, h2⟩ : Ov) = 2 := rfl
  rw [this, map_ofNat]
  have := ringChar.Nat.cast_ringChar (R := kv)
  rw [h] at this
  exact_mod_cast this

/-! ### Split places -/

variable {v}

/-- **The number of zeros of $r_0^2 - \bar ar_1^2 - \bar br_2^2 + \bar a\bar br_3^2$ on $k^4$** ($k$ finite of odd
characteristic, $\bar a\bar b\ne0$): $q^3 + q^2 - q$ (square discriminant). -/
theorem card_nrdForm_eq_zero {k : Type*} [Field k] [Fintype k] [DecidableEq k] (hk : ringChar k ≠ 2)
    {α β : k} (hα : α ≠ 0) (hβ : β ≠ 0) :
    ((Finset.univ.filter fun r : Fin 4 → k => nrdForm α β r = 0).card : ℤ) =
      (Fintype.card k : ℤ) ^ 3 + (Fintype.card k : ℤ) ^ 2 - Fintype.card k := by
  have hd := LocalDensity.DVR.diagCountF_even hk 1 4 rfl ![1, -α, -β, α * β]
    (fun i => by fin_cases i <;> simp [hα, hβ]) 0
  have hχ : quadraticChar k ((-1) ^ (1 + 1) * ∏ i, (![1, -α, -β, α * β] : Fin 4 → k) i) = 1 := by
    rw [Fin.prod_univ_four]
    have : (-1 : k) ^ (1 + 1) * ((![1, -α, -β, α * β] : Fin 4 → k) 0 * (![1, -α, -β, α * β] : Fin 4 → k) 1 *
        (![1, -α, -β, α * β] : Fin 4 → k) 2 * (![1, -α, -β, α * β] : Fin 4 → k) 3) = (α * β) ^ 2 := by
      simp; ring
    rw [this]
    exact quadraticChar_sq_one' (mul_ne_zero hα hβ)
  rw [hχ] at hd
  have hcount : LocalDensity.DVR.diagCountF (![1, -α, -β, α * β] : Fin 4 → k) 0 =
      ((Finset.univ.filter fun r : Fin 4 → k => nrdForm α β r = 0).card : ℤ) := by
    rw [LocalDensity.DVR.diagCountF, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    have : ∑ i, (![1, -α, -β, α * β] : Fin 4 → k) i * r i ^ 2 = nrdForm α β r := by
      rw [Fin.sum_univ_four, nrdForm]; simp; ring
    rw [this]
  rw [← hcount, hd]
  simp
  ring

/-- **$\omega_v(\Lambda_v^\times)$ at a split place**: if $v\nmid2$ and $a, b\in\mathcal O_v^\times$, then
$\omega_v(\Lambda_v^\times) = (1-q^{-1})(1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$ ($= \#\mathrm{GL}_2(\mathbb F_q)\,q^{-4}\,
\operatorname{vol}(\mathcal O_v)^4$, since $\Lambda_v\cong M_2(\mathcal O_v)$). -/
@[kb "weil1982" "§2.3 [unverified page] (ω_v(Λ_v^×) for A = ℍ at the unramified places)"]
theorem omegaQuatV_lamLocUnits_good
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
    (hv2 : Valued.v (2 : Kv) = 1) (hav : Valued.v (algebraMap F Kv a) = 1) (hbv : Valued.v (algebraMap F Kv b) = 1) :
    omegaQuatV v a b (lamLocUnits a b v) =
      ENNReal.ofReal ((1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) * (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹)) *
        volO v ^ 4 := by
  classical
  let _ : Fintype kv := Fintype.ofFinite kv
  have hαO : algebraMap F Kv a ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ha v)
  have hβO : algebraMap F Kv b ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hb v)
  have hα : resV v (algebraMap F Kv a) ≠ 0 := by
    rw [resV_of_mem v hαO]; exact (valued_eq_one_iff_residue_ne_zero v ⟨_, hαO⟩).mp hav
  have hβ : resV v (algebraMap F Kv b) ≠ 0 := by
    rw [resV_of_mem v hβO]; exact (valued_eq_one_iff_residue_ne_zero v ⟨_, hβO⟩).mp hbv
  rw [omegaQuatV_lamLocUnits_eq ha hb, setOf_nrdForm_eq v hαO hβO,
    pi_selfDualV_res v (fun r => nrdForm (resV v (algebraMap F Kv a)) (resV v (algebraMap F Kv b)) r ≠ 0),
    selfDualV_latticeV_one]
  have hcard := card_nrdForm_eq_zero (ringChar_ne_two_of_valued_two v hv2) hα hβ
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4 → kv)))
    (fun r => nrdForm (resV v (algebraMap F Kv a)) (resV v (algebraMap F Kv b)) r = 0)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  have hq : (Fintype.card kv : ℝ) = q := card_residueField_eq v
  have hq0 : q ≠ 0 := by have := one_lt_absNorm v; positivity
  have hN : ((Finset.univ.filter fun r : Fin 4 → kv =>
      nrdForm (resV v (algebraMap F Kv a)) (resV v (algebraMap F Kv b)) r ≠ 0).card : ℝ) =
      q ^ 4 - q ^ 3 - q ^ 2 + q := by
    have h1 : ((Finset.univ.filter fun r : Fin 4 → kv =>
        nrdForm (resV v (algebraMap F Kv a)) (resV v (algebraMap F Kv b)) r ≠ 0).card : ℤ) =
        (Fintype.card kv : ℤ) ^ 4 - ((Fintype.card kv : ℤ) ^ 3 + (Fintype.card kv : ℤ) ^ 2 -
          Fintype.card kv) := by
      rw [← hcard]
      have := congrArg (Nat.cast : ℕ → ℤ) hsplit
      push_cast at this
      linarith
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
    push_cast at h2
    rw [h2, hq]; ring
  rw [mul_pow, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have key : ∀ N : ℝ, N = q ^ 4 - q ^ 3 - q ^ 2 + q → N * q⁻¹ ^ 4 = (1 - q⁻¹) * (1 - (q ^ 2)⁻¹) := by
    intro N hN; rw [hN]; field_simp; ring
  exact key _ (by convert hN using 3; ext r; simp)

/-- **$\lambda_v^{-1}\omega_v(\Lambda_v^\times) = (1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$ at a split place**
($\lambda_v = 1-q^{-1}$). -/
@[kb "weil1982" "§2.3 [unverified page] (λ_v^{-1}ω_v(Λ_v^×) for A = ℍ; the product ∏_v converges)"]
theorem lamV_inv_mul_omegaQuatV_good
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
    (hv2 : Valued.v (2 : Kv) = 1) (hav : Valued.v (algebraMap F Kv a) = 1) (hbv : Valued.v (algebraMap F Kv b) = 1) :
    ENNReal.ofReal (lamV v)⁻¹ * omegaQuatV v a b (lamLocUnits a b v) =
      ENNReal.ofReal (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹) * volO v ^ 4 := by
  rw [omegaQuatV_lamLocUnits_good ha hb hv2 hav hbv, ← mul_assoc, ← ENNReal.ofReal_mul
    (inv_nonneg.2 (lamV_pos v).le), ← mul_assoc]
  have h := (lamV_pos v).ne'
  rw [lamV] at h ⊢
  rw [inv_mul_cancel₀ h, one_mul]

/-! ### Ramified places -/

/-- If $\bar\beta$ is a non-square, $r_0^2 - \bar\beta r_2^2 = 0$ only for $r_0 = r_2 = 0$: the zero set has $q^2$ points. -/
theorem card_nrdForm_ram_eq_zero {k : Type*} [Field k] [Fintype k] [DecidableEq k] {β : k} (hβ : ¬ IsSquare β) :
    (Finset.univ.filter fun r : Fin 4 → k => nrdForm 0 β r = 0).card = Fintype.card k ^ 2 := by
  have hset : (Finset.univ.filter fun r : Fin 4 → k => nrdForm 0 β r = 0) =
      Fintype.piFinset fun i : Fin 4 => if i = 0 ∨ i = 2 then ({0} : Finset k) else Finset.univ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, nrdForm, zero_mul, sub_zero]
    constructor
    · intro h i
      have h2 : r 2 = 0 := by
        by_contra h2
        exact hβ ⟨r 0 / r 2, by field_simp; linear_combination -h⟩
      have h0 : r 0 = 0 := by
        rw [h2] at h; simpa using h
      fin_cases i <;> simp [h0, h2]
    · intro h
      have h0 := h 0
      have h2 := h 2
      simp only [true_or, ite_true, Finset.mem_singleton, or_true] at h0 h2
      rw [h0, h2]; ring
  rw [hset, Fintype.card_piFinset, Fin.prod_univ_four]
  simp; ring

/-- **$\omega_v(\Lambda_v^\times)$ at a ramified place**: if $|a|_v < 1$, $b\in\mathcal O_v^\times$ and $\bar b$ is a
non-square in $k_v$, then $\omega_v(\Lambda_v^\times) = (1-q^{-2})\operatorname{vol}(\mathcal O_v)^4$ (the reduced norm
form reduces to the anisotropic binary form $r_0^2 - \bar br_2^2$). For $v\nmid2$ and $v(a) = 1$ the algebra is ramified
at $v$ and $\Lambda_v$ is its maximal order $\mathcal O_D$ (standard, not formalized here). -/
@[kb "weil1982" "§2.3 [unverified page] (ω_v(Λ_v^×) for A = ℍ at a ramified place)"]
theorem omegaQuatV_lamLocUnits_ram
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
    (hav : Valued.v (algebraMap F Kv a) < 1) (hbsq : ¬ IsSquare (resV v (algebraMap F Kv b))) :
    omegaQuatV v a b (lamLocUnits a b v) =
      ENNReal.ofReal (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ 2)⁻¹) * volO v ^ 4 := by
  let _ : Fintype kv := Fintype.ofFinite kv
  have hαO : algebraMap F Kv a ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (ha v)
  have hβO : algebraMap F Kv b ∈ Ov := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hb v)
  have hα : resV v (algebraMap F Kv a) = 0 := by
    rw [resV_of_mem v hαO, residue_eq_zero_iff]; exact hav
  rw [omegaQuatV_lamLocUnits_eq ha hb, setOf_nrdForm_eq v hαO hβO, hα,
    pi_selfDualV_res v (fun r => nrdForm 0 (resV v (algebraMap F Kv b)) r ≠ 0), selfDualV_latticeV_one]
  have hcard := card_nrdForm_ram_eq_zero hbsq
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4 → kv))) (fun r => nrdForm 0 (resV v (algebraMap F Kv b)) r = 0)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsplit
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  have hq : (Fintype.card kv : ℝ) = q := card_residueField_eq v
  have hq0 : q ≠ 0 := by have := one_lt_absNorm v; positivity
  have hN : ((Finset.univ.filter fun r : Fin 4 → kv => nrdForm 0 (resV v (algebraMap F Kv b)) r ≠ 0).card : ℝ) =
      q ^ 4 - q ^ 2 := by
    have h2 := congrArg (Nat.cast : ℕ → ℝ) hsplit
    push_cast at h2
    rw [← hq]
    have h3 := congrArg (Nat.cast : ℕ → ℝ) hcard
    push_cast at h3
    linarith
  rw [mul_pow, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have key : ∀ N : ℝ, N = q ^ 4 - q ^ 2 → N * q⁻¹ ^ 4 = 1 - (q ^ 2)⁻¹ := by
    intro N hN; rw [hN]; field_simp
  exact key _ (by convert hN using 3; ext r; simp)

end

end QuadFormsKB.Tamagawa.Measure.Weil
