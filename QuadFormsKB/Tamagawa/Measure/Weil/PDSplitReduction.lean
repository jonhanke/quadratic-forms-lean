import QuadFormsKB.Tamagawa.Measure.Weil.PDArchRatio

/-!
# $\tau(SO(D^0))$ for every quaternion algebra, split or not, from $\tau(\mathrm{SL}_1(D))$

**Layer:** $F$ a number field, $a, b\in\mathcal O_F\setminus 0$, $D = \mathbb H[F,a,b]$ any quaternion algebra (division
or $M_2(F)$), any signature, $Q_0 = \langle -a,-b,ab\rangle$.

The earlier arguments used the hypothesis that $D$ is a division algebra twice: for $c_A' = \rho_F$ (through
Fujisaki), and
for the conjugation invariance of $\mu_{\mathrm{SL}_1}$ under $\mathbb H_{\mathbb A}^1$ (through the unimodularity of
$\mathbb H_{\mathbb A}^1$, again Fujisaki). Here both are replaced by statements about $\mathrm{SL}_1(D)$ alone.

**Proves**
* `map_adK_muSL1_of_isMulRightInvariant`: if $\mathrm{SL}_1(\mathbb A)$ is unimodular, conjugation by every
  $g\in\mathbb H_{\mathbb A}^1$ preserves $\mu_{\mathrm{SL}_1}$. *Proof.* $\operatorname{Ad}(g)_*\mu = c\,\mu$ by Haar
  uniqueness; $g^2 = k\,z$ with $k\in\mathrm{SL}_1(\mathbb A)$ and $z = \operatorname{nrd}(g)$ central (scalars have
  $\operatorname{nrd} z = z^2$), so $c^2 = 1$, and $c > 0$.
* `quatVolConst_eq_covolume_mul_of_lt_top`: $c_A' = \tau(\mathrm{SL}_1)\cdot\operatorname{vol}(F^\times\backslash\mathbb A^1)$
  whenever $\tau(\mathrm{SL}_1) < \infty$ (any quaternion algebra).
* `covolume_muPD_eq_two_mul`: $\tau(PD^\times) = 2\,\tau(\mathrm{SL}_1(D))$ whenever $\tau(\mathrm{SL}_1(D)) < \infty$.
* `covolume_muTam_pureForm_of_tauSL1`: under the named input `TauSL1EqOne a b` ($\tau(\mathrm{SL}_1(D)) = 1$),
  the covolume of $SO(V)(F)$ for `muTam` is $2$, for every quaternion algebra over every number field; the input is a theorem for
  division algebras (`tauSL1EqOne_of_division`).
-/

open MeasureTheory Set NumberField IsDedekindDomain NumberField.InfinitePlace Quaternion
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.QuatZeta QuadFormsKB.Siegel

variable {F : Type} [Field F] [NumberField F]

section Conj

instance {a b : F} : StandardBorelSpace (SL1A a b) := by
  have := polishSpace_of_isTopologicalGroup (SL1A a b)
  infer_instance

variable {a b : F} (ha : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) a) ≤ 1)
  (hb : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (v.adicCompletion F) b) ≤ 1)
  (ha0 : a ≠ 0) (hb0 : b ≠ 0)

/-- The scalar $\operatorname{nrd}(g)\in\mathbb A^1$ as an element of $\mathbb H_{\mathbb A}^1$. -/
def nrdScalar (g : quatOne a b) : quatOne a b :=
  ⟨quatScalar a b (nrdUnit (g : (QuatAdele a b)ˣ)), (quatScalar_mem_quatOne a b).2
    (mem_ideleOne.2 ((mem_quatOne a b).1 g.2))⟩

theorem nrdScalar_comm (g x : quatOne a b) : nrdScalar g * x = x * nrdScalar g := by
  apply Subtype.ext; apply Units.ext
  change algebraMap (Adeles F) (QuatAdele a b) _ * _ = _ * algebraMap (Adeles F) (QuatAdele a b) _
  exact Algebra.commutes _ _

/-- $g^2\operatorname{nrd}(g)^{-1}\in\mathrm{SL}_1(\mathbb A)$. -/
theorem sq_mul_nrdScalar_inv_mem (g : quatOne a b) : g * g * (nrdScalar g)⁻¹ ∈ SL1A a b := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, mul_inv_eq_one]
  apply Subtype.ext; apply Subtype.ext
  have hz : ((nrdScalar g : quatOne a b) : (QuatAdele a b)ˣ) = quatScalar a b (nrdUnit (g : (QuatAdele a b)ˣ)) := rfl
  simp only [Subgroup.coe_mul, coe_nrdOne, hz, nrdUnit_quatScalar, sq]

theorem adK_nrdScalar (g : quatOne a b) : NormalFib.adK (nrdOne a b) (nrdScalar g) = id := by
  funext k; apply Subtype.ext
  change nrdScalar g * (k : quatOne a b) * (nrdScalar g)⁻¹ = k
  rw [nrdScalar_comm, mul_inv_cancel_right]

theorem adK_mul (g h : quatOne a b) :
    NormalFib.adK (nrdOne a b) (g * h) = NormalFib.adK (nrdOne a b) g ∘ NormalFib.adK (nrdOne a b) h := by
  funext k; apply Subtype.ext
  simp only [Function.comp_apply, NormalFib.coe_adK]; group

set_option maxHeartbeats 2000000 in
include ha hb ha0 hb0 in
/-- **Conjugation invariance of $\mu_{\mathrm{SL}_1}$ from the unimodularity of $\mathrm{SL}_1(\mathbb A)$** (any quaternion
algebra): $\operatorname{Ad}(g)_*\mu_{\mathrm{SL}_1} = \mu_{\mathrm{SL}_1}$ for every $g\in\mathbb H_{\mathbb A}^1$. -/
theorem map_adK_muSL1_of_isMulRightInvariant [hR : (muSL1 ha hb ha0 hb0).IsMulRightInvariant] (g : quatOne a b) :
    (muSL1 ha hb ha0 hb0).map (NormalFib.adK (nrdOne a b) g) = muSL1 ha hb ha0 hb0 := by
  set μ := muSL1 ha hb ha0 hb0
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have hmeas : ∀ h : quatOne a b, Measurable (NormalFib.adK (nrdOne a b) h) := fun h =>
    NormalFib.measurable_adK _ h
  -- inner automorphisms of `SL₁(𝔸)` preserve `μ`
  have hinner : ∀ k : SL1A a b, μ.map (NormalFib.adK (nrdOne a b) (k : quatOne a b)) = μ := fun k => by
    have : NormalFib.adK (nrdOne a b) (k : quatOne a b) = (fun x => x * k⁻¹) ∘ (fun x => k * x) := by
      funext x; apply Subtype.ext; rfl
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]
  -- Haar uniqueness
  have hH : (μ.map (NormalFib.adKEquiv (nrdOne a b) g)).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  set c := (μ.map (NormalFib.adKEquiv (nrdOne a b) g)).haarScalarFactor μ
  have hc : μ.map (NormalFib.adK (nrdOne a b) g) = (c : ℝ≥0∞) • μ := by
    rw [← NormalFib.coe_adKEquiv]; exact Measure.isMulLeftInvariant_eq_smul _ _
  -- `g² = k z`
  set k : SL1A a b := ⟨_, sq_mul_nrdScalar_inv_mem g⟩
  have hgg : g * g = (k : quatOne a b) * nrdScalar g := by
    change g * g = g * g * (nrdScalar g)⁻¹ * nrdScalar g; group
  have h2 : μ.map (NormalFib.adK (nrdOne a b) (g * g)) = μ := by
    rw [hgg, adK_mul, adK_nrdScalar, Function.comp_id, hinner]
  rw [adK_mul, ← Measure.map_map (hmeas g) (hmeas g), hc, Measure.map_smul _ (hmeas g).aemeasurable, hc,
    smul_smul] at h2
  -- `c² = 1`
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (SL1A a b)))
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have ht : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hcc := congrArg (fun ν : Measure (SL1A a b) => ν K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at hcc
  have hcc' : (c : ℝ≥0∞) * c = 1 := by
    have : (c : ℝ≥0∞) * c * μ K = 1 * μ K := by rw [one_mul]; exact hcc
    exact (ENNReal.mul_left_inj h0 ht).1 this
  have hc1 : c = 1 := by
    have : c * c = 1 := by exact_mod_cast hcc'
    nlinarith [c.2, sq_nonneg ((c : ℝ) - 1), show ((c : ℝ)) * c = 1 by exact_mod_cast this]
  rw [hc, hc1, ENNReal.coe_one, one_smul]

include ha hb ha0 hb0 in
/-- $\mathrm{SL}_1(\mathbb A)$ is unimodular as soon as $\tau(\mathrm{SL}_1) < \infty$ (a lattice of finite covolume). -/
theorem isMulRightInvariant_muSL1_of_lt_top
    (hfin : covolume (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) ≠ ∞) :
    (muSL1 ha hb ha0 hb0).IsMulRightInvariant := by
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := a) (b := b)
  rw [covolume_SL1_eq ha hb ha0 hb0 hDK] at hfin
  have : SMulInvariantMeasure (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  have h0 : muSL1 ha hb ha0 hb0 DK ≠ 0 :=
    (hDK.isFundamentalDomain (muSL1 ha hb ha0 hb0)).measure_ne_zero (NeZero.ne _)
  exact NormalFib.isMulRightInvariant_of_exactFD _ (SL1F a b) hDK h0 hfin

set_option maxHeartbeats 2000000 in
include ha hb ha0 hb0 in
/-- **$c_A' = \tau(\mathrm{SL}_1)\cdot\operatorname{vol}(F^\times\backslash\mathbb A^1)$ for every quaternion algebra** with
$\tau(\mathrm{SL}_1) < \infty$ (`quatVolConst_eq_covolume_mul` without the division hypothesis). -/
@[kb "weil1982" "§2.4, Thm 2.4.4; §3.1 (c_A = τ(SL₁)·ρ) [unverified pages]"]
theorem quatVolConst_eq_covolume_mul_of_lt_top
    (hfin : covolume (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) ≠ ∞) :
    quatVolConst ha hb ha0 hb0 =
      covolume (SL1F a b) (SL1A a b) (muSL1 ha hb ha0 hb0) * muIdeleClass F univ := by
  have := isMulRightInvariant_muSL1_of_lt_top ha hb ha0 hb0 hfin
  obtain ⟨DK, hDK⟩ := exists_exactFD_SL1F (a := a) (b := b)
  obtain ⟨DQ, hDQ⟩ := exists_exactFD_nrdGlobal (a := a) (b := b)
  obtain ⟨D, hDm, hD⟩ := exists_measurableSet_forall_existsUnique_smul_mem (quatUnitsOne a b)
  have := isHaarMeasure_muSL1 ha hb ha0 hb0
  have hfib : quatVolConst ha hb ha0 hb0 = muSL1 ha hb ha0 hb0 DK * muPosOne a b DQ := by
    rw [quatVolConst_eq ha hb ha0 hb0 hDm hD, ← fibMeas_muSL1 ha hb ha0 hb0]
    exact NormalFib.fibMeas_exactFD _ _ (quatUnitsOne a b) measurable_nrdOne _ _
      (map_adK_muSL1_of_isMulRightInvariant ha hb ha0 hb0) ⟨hDm, hD⟩ hDK hDQ
  rw [hfib, covolume_SL1_eq ha hb ha0 hb0 hDK, muPosOne_apply,
    muIdeleClass_univ ((isExactFD_image_posOne ha0 hb0 hDQ).isFundamentalDomain _)]

end Conj

section Tau

variable (a b : 𝓞 F)

/-- **Input (named): $\tau(\mathrm{SL}_1(D)) = 1$** for Weil's Tamagawa measure `muSL1` on $\mathrm{SL}_1(D)(\mathbb A)$,
$D = \mathbb H[F,a,b]$ (Weil 1982, §3.7 and Thm 3.2.1; for split $D$ this is $\tau(\mathrm{SL}_2) = 1$, the
`tamagawa_SL2_gauge`, once `muSL1` is identified with the $\mathrm{SL}_2$ measure). It concerns $\mathrm{SL}_1(D)$, not
$SO(V)$ or $PD^\times$. Proved for division algebras (`tauSL1EqOne_of_division`). -/
structure TauSL1EqOne : Prop where
  /-- $\operatorname{covol}(\mathrm{SL}_1(D)(F)\backslash\mathrm{SL}_1(D)(\mathbb A), \mu_{\mathrm{SL}_1}) = 1$. -/
  covolume_eq_one (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) = 1

/-- `TauSL1EqOne` holds for every quaternion division algebra (`tamagawa_SL1_division_unconditional`). -/
theorem tauSL1EqOne_of_division (hdiv : ∀ ξ : ℍ[F,(a : F),(b : F)], ξ ≠ 0 → IsUnit ξ) : TauSL1EqOne a b :=
  ⟨fun ha0 hb0 => tamagawa_SL1_division_unconditional ha0 hb0 hdiv⟩

set_option maxHeartbeats 2000000 in
/-- **$\tau(PD^\times) = 2\,\tau(\mathrm{SL}_1(D))$ for every quaternion algebra $D = \mathbb H[F,a,b]$** (split or not)
with $\tau(\mathrm{SL}_1(D)) < \infty$, every number field, every signature. -/
@[kb "weil1982" "Thm 3.2.1, p. 43 (τ(PD^×) = 2 via τ(SL₁) and the centre)"]
theorem covolume_muPD_eq_two_mul (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hfin : covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
      (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) ≠ ∞) :
    covolume (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) =
      2 * covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
        (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) (by simpa using ha0) (by simpa using hb0)) := by
  have ha0' : (a : F) ≠ 0 := by simpa using ha0
  have hb0' : (b : F) ≠ 0 := by simpa using hb0
  have hH := isHaarMeasure_muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0'
  obtain ⟨DQ, hDQ⟩ := exists_exactFD_gammaPD a b ha0 hb0
  have h1 := quatVolConst_eq_mul_muPDOne (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hDQ
  rw [quatVolConst_eq_covolume_mul_of_lt_top (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' hfin,
    muIdeleClass_univ_eq_residue] at h1
  have hρ0 : ENNReal.ofReal (dedekindZeta_residue F) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact dedekindZeta_residue_pos F
  have hμ1 : muPDOne (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0' DQ =
      covolume (SL1F (a : F) (b : F)) (SL1A (a : F) (b : F))
        (muSL1 (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0') := by
    rw [mul_comm] at h1
    exact ((ENNReal.mul_right_inj hρ0 ENNReal.ofReal_ne_top).1 h1).symm
  have := countable_pdGamma a b
  rw [gammaPD_eq_pdGamma] at hDQ
  have : SMulInvariantMeasure (pdGamma a b) (PDAdele a b)
      (muPD (valued_coe_le_one a) (valued_coe_le_one b) ha0' hb0') :=
    ⟨fun γ s _ => measure_preimage_mul _ _ _⟩
  rw [(hDQ.isFundamentalDomain _).covolume_eq_volume, muPD, Measure.smul_apply, hμ1, smul_eq_mul]

/-- **The covolume of $SO(V)(F)$ for `muTam` is $2$ for every quaternion algebra** $D = \mathbb H[F,a,b]$ (split or
not), every number field, every signature, conditional only on the named input `TauSL1EqOne a b`
($\tau(\mathrm{SL}_1(D)) = 1$). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63"]
theorem covolume_muTam_pureForm_of_tauSL1 (ha : a ≠ 0) (hb : b ≠ 0) (hτ : TauSL1EqOne a b) :
    covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
        (muTam (pureFormO a b) (nondegenerate_pureFormO a b ha hb) fun _ => 1) = 2 := by
  have h := covolume_muPD_eq_two_mul a b ha hb (by rw [hτ.covolume_eq_one ha hb]; exact ENNReal.one_ne_top)
  rw [hτ.covolume_eq_one ha hb, mul_one] at h
  exact covolume_muTam_pureForm_of_covolume_muPD a b ha hb h

/-- **$\tau(SO(V)) = 2$ for `muTamWeil` $=$ `muTam`, every quaternion algebra**, conditional only on
`TauSL1EqOne a b` (the same statement as `covolume_muTam_pureForm_of_tauSL1`). -/
@[kb "weil1982" "Thm 3.2.1, p. 43; §2.3, Thm 2.3.1; §3.7(a), p. 63; Thm 3.7.1 (m = 3), p. 65"]
theorem covolume_muTamWeil_pureForm_of_tauSL1 (ha : a ≠ 0) (hb : b ≠ 0) (hτ : TauSL1EqOne a b) :
    covolume (GammaSOAdele (pureFormO a b)) (SOAdele (pureFormO a b))
      (muTamWeil (pureFormO a b) (nondegenerate_pureFormO a b ha hb)) = 2 :=
  covolume_muTam_pureForm_of_tauSL1 a b ha hb hτ

end Tau

end QuadFormsKB.Tamagawa.Measure.Weil
