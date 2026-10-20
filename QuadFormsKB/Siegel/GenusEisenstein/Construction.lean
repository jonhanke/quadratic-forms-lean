/-
# The Eisenstein part of a weight-2 form on $\Gamma_1(N)$

For every $f \in M_2(\Gamma_1(N))$ we build an Eisenstein series $E_f$ (`eisQ f`, a finite combination of the series
$E_W$ of `EisensteinWt2`) with the same constant term as $f$ at every cusp, so that $f - E_f$ is a cusp form
(`cuspPart f`, **`cuspPart_apply`**). Applied to $f = \Theta_{\mathrm{Gen}(Q)}$ this is the Eisenstein series $E_Q$ of Siegel's
formula.

**Construction.** Let $S \subseteq (\mathbb{Z}/N)^2$ be the set of vectors $v(\gamma) = (-\gamma_{10}, \gamma_{00})$ (`cuspFinset`),
$h(v) = c_f(\gamma)/2$ for $v = v(\gamma)$ (`halfVal`; well defined by `cuspVal_eq_of_cuspVec_eq`), $\kappa$ the mean of $h$
over $S$ (`kappa`) and $W = (h - \kappa)\mathbf 1_S$ (`eisW`, total mass $0$). Put $W_r(x, y) = W(rx, ry)$ (`eisWr`, mass $0$:
for $r$ a unit by reindexing, otherwise $rv$ is never primitive) and
$$E_f = \sum_{r \in \mathbb{Z}/N} a_r\,E_{W_r}, \qquad a_r = \sum_{g \ge 1,\ g \equiv r}\mu(g)g^{-2}$$
(`moebCoeff`). By `tendsto_eis2_slash` and the Möbius identity `moebius_const`, the constant term of $E_f$ at $\gamma\infty$ is
$2W(v(\gamma)) = c_f(\gamma) - 2\kappa$ (`tendsto_eisQ_slash`): this is the "primitive" series
$\sum_{(c,d)=1}W(c,d)(cz+d)^{-2}$.

**The mass condition** $\kappa = 0$ (`kappa_eq_zero`): $g = f - E_f$ has constant term $2\kappa$ at every cusp, so its trace to
$\mathrm{SL}_2(\mathbb{Z})$ (Mathlib's `ModularForm.trace`) tends to $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_1(N)]\cdot 2\kappa$; but
$M_2(\mathrm{SL}_2(\mathbb{Z})) = 0$ (Mathlib's `levelOne_weight_two_rank_zero`). This is the weight-2 "residue theorem"
obstruction (no $E_2$), obtained without contour integration.
-/
import QuadFormsKB.Siegel.GenusEisenstein.CuspValues
import QuadFormsKB.Siegel.GenusEisenstein.Moebius
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

open Complex Filter Topology ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Siegel.GenusEis

open EisensteinWt2

variable {N : ℕ} [NeZero N]

local notation "Γ₁" => CongruenceSubgroup.Gamma1

/-- The vectors $v(\gamma) = (-\gamma_{10}, \gamma_{00}) \bmod N$, $\gamma \in \mathrm{SL}_2(\mathbb{Z})$. -/
noncomputable def cuspFinset (N : ℕ) [NeZero N] : Finset (ZMod N × ZMod N) := by
  classical exact Finset.univ.filter (fun v => ∃ γ : SL(2, ℤ), cuspVec N γ = v)

lemma mem_cuspFinset {v : ZMod N × ZMod N} : v ∈ cuspFinset N ↔ ∃ γ : SL(2, ℤ), cuspVec N γ = v := by
  classical simp [cuspFinset]

lemma cuspVec_mem (γ : SL(2, ℤ)) : cuspVec N γ ∈ cuspFinset N := mem_cuspFinset.mpr ⟨γ, rfl⟩

lemma cuspFinset_card_pos : 0 < (cuspFinset N).card :=
  Finset.card_pos.mpr ⟨_, cuspVec_mem 1⟩

lemma prim_of_mem {v : ZMod N × ZMod N} (hv : v ∈ cuspFinset N) : ∃ s t : ZMod N, s * v.1 + t * v.2 = 1 := by
  obtain ⟨γ, rfl⟩ := mem_cuspFinset.mp hv
  exact cuspVec_prim γ

variable (f : ModularForm (Γ₁ N) 2)

/-- $h(v) = c_f(\gamma)/2$ for $v = v(\gamma)$, and $0$ off $S$. -/
noncomputable def halfVal (v : ZMod N × ZMod N) : ℂ := by
  classical exact if h : ∃ γ : SL(2, ℤ), cuspVec N γ = v then cuspVal f h.choose / 2 else 0

lemma halfVal_cuspVec (γ : SL(2, ℤ)) : halfVal f (cuspVec N γ) = cuspVal f γ / 2 := by
  have h : ∃ γ' : SL(2, ℤ), cuspVec N γ' = cuspVec N γ := ⟨γ, rfl⟩
  classical
  rw [halfVal, dif_pos h]
  rw [cuspVal_eq_of_cuspVec_eq f h.choose_spec]

/-- $\kappa = |S|^{-1}\sum_{v \in S}h(v)$. -/
noncomputable def kappa : ℂ := (∑ v ∈ cuspFinset N, halfVal f v) / (cuspFinset N).card

/-- The weight $W = (h - \kappa)\mathbf 1_S$. -/
noncomputable def eisW (x y : ZMod N) : ℂ := by
  classical exact if (x, y) ∈ cuspFinset N then halfVal f (x, y) - kappa f else 0

lemma eisW_of_mem {x y : ZMod N} (h : (x, y) ∈ cuspFinset N) : eisW f x y = halfVal f (x, y) - kappa f := by
  classical simp [eisW, h]

lemma eisW_of_not_mem {x y : ZMod N} (h : (x, y) ∉ cuspFinset N) : eisW f x y = 0 := by
  classical simp [eisW, h]

lemma eisW_cuspVec (γ : SL(2, ℤ)) :
    eisW f (cuspVec N γ).1 (cuspVec N γ).2 = cuspVal f γ / 2 - kappa f := by
  rw [eisW_of_mem f (by simpa using cuspVec_mem γ), Prod.mk.eta, halfVal_cuspVec]

lemma totalSum_eisW : totalSum (eisW f) = 0 := by
  classical
  have hc : ((cuspFinset N).card : ℂ) ≠ 0 := by exact_mod_cast (cuspFinset_card_pos (N := N)).ne'
  rw [totalSum, ← Fintype.sum_prod_type' (fun a b => eisW f a b)]
  have : ∀ v : ZMod N × ZMod N, eisW f v.1 v.2 = if v ∈ cuspFinset N then halfVal f v - kappa f else 0 := by
    intro v; simp [eisW]
  simp_rw [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, kappa]
  field_simp
  ring

/-- $W_r(x, y) = W(rx, ry)$. -/
noncomputable def eisWr (r : ZMod N) (x y : ZMod N) : ℂ := eisW f (r * x) (r * y)

lemma totalSum_eisWr (r : ZMod N) : totalSum (eisWr f r) = 0 := by
  by_cases hr : IsUnit r
  · have e : ∀ g : ZMod N → ℂ, ∑ x, g (r * x) = ∑ x, g x := fun g =>
      Fintype.sum_equiv (Units.mulLeft hr.unit) _ _ (fun x => by simp)
    simp only [totalSum, eisWr]
    rw [Finset.sum_congr rfl fun a _ => e (fun b => eisW f (r * a) b), e (fun a => ∑ b, eisW f a b)]
    exact totalSum_eisW f
  · simp only [totalSum, eisWr]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => eisW_of_not_mem f fun hm => hr ?_
    obtain ⟨s, t, hst⟩ := prim_of_mem hm
    exact IsUnit.of_mul_eq_one (s * a + t * b) (by simp only at hst; linear_combination hst)

lemma mem_cuspFinset_shift {x y : ZMod N} (h : (x, y) ∈ cuspFinset N) (j : ℤ) :
    (x, y - j * x) ∈ cuspFinset N ∧ halfVal f (x, y - j * x) = halfVal f (x, y) := by
  obtain ⟨γ, hγ⟩ := mem_cuspFinset.mp h
  have hv := cuspVec_T_mul (N := N) j γ
  rw [hγ] at hv
  refine ⟨mem_cuspFinset.mpr ⟨_, hv⟩, ?_⟩
  rw [← hv, ← hγ, halfVal_cuspVec, halfVal_cuspVec, cuspVal_T_mul]

lemma intCast_val (t : ZMod N) : (((t.val : ℕ) : ℤ) : ZMod N) = t := by
  simp

/-- $W(x, y + tx) = W(x, y)$ ($T$-invariance). -/
lemma eisW_shift (x y t : ZMod N) : eisW f x (y + t * x) = eisW f x y := by
  by_cases h : (x, y) ∈ cuspFinset N
  · have h2 := mem_cuspFinset_shift f h (-(t.val : ℤ))
    rw [Int.cast_neg, intCast_val, neg_mul, sub_neg_eq_add] at h2
    rw [eisW_of_mem f h2.1, eisW_of_mem f h, h2.2]
  · have h' : (x, y + t * x) ∉ cuspFinset N := by
      intro h'
      have h2 := mem_cuspFinset_shift f h' (t.val : ℤ)
      rw [intCast_val, add_sub_cancel_right] at h2
      exact h h2.1
    rw [eisW_of_not_mem f h, eisW_of_not_mem f h']

/-- $W(-x, -y) = W(x, y)$. -/
lemma eisW_neg (x y : ZMod N) : eisW f (-x) (-y) = eisW f x y := by
  have key : ∀ {x y : ZMod N}, (x, y) ∈ cuspFinset N →
      (-x, -y) ∈ cuspFinset N ∧ halfVal f (-x, -y) = halfVal f (x, y) := by
    intro x y h
    obtain ⟨γ, hγ⟩ := mem_cuspFinset.mp h
    have hv := cuspVec_neg (N := N) γ
    rw [hγ] at hv
    refine ⟨mem_cuspFinset.mpr ⟨_, hv.trans (by simp)⟩, ?_⟩
    rw [show ((-x, -y) : ZMod N × ZMod N) = cuspVec N (-γ) by rw [hv]; simp, ← hγ, halfVal_cuspVec,
      halfVal_cuspVec, cuspVal_neg]
  by_cases h : (x, y) ∈ cuspFinset N
  · rw [eisW_of_mem f (key h).1, eisW_of_mem f h, (key h).2]
  · have h' : (-x, -y) ∉ cuspFinset N := fun h' => h (by simpa using (key h').1)
    rw [eisW_of_not_mem f h, eisW_of_not_mem f h']

lemma slashW_eisWr (r : ZMod N) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ₁ N) : slashW (eisWr f r) δ = eisWr f r := by
  obtain ⟨h00, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem N δ).mp hδ
  funext a b
  simp only [slashW, eisWr]
  rw [h11, h10, h00, mul_one, mul_zero, sub_zero, mul_one]
  rw [show r * (-(a * ((δ 0 1 : ℤ) : ZMod N)) + b) = r * b + (-((δ 0 1 : ℤ) : ZMod N)) * (r * a) by ring]
  exact eisW_shift f _ _ _

/-- $E_{W_r} \in M_2(\Gamma_1(N))$. -/
noncomputable def eisMF (r : ZMod N) : ModularForm (Γ₁ N) 2 :=
  eis2MF (eisWr f r) (totalSum_eisWr f r) (fun _ hδ => slashW_eisWr f r hδ)

/-- **The Eisenstein part of $f$:** $E_f = \sum_r a_r E_{W_r}$. -/
@[kb "diamondshurman2005" "§4.5–4.6 (Eisenstein space spans the constant terms) [unverified]"]
noncomputable def eisQ : ModularForm (Γ₁ N) 2 := ∑ r : ZMod N, moebCoeff N r • eisMF f r

lemma modularForm_sum_apply {ι : Type*} (s : Finset ι) (F : ι → ModularForm (Γ₁ N) 2) (τ : ℍ) :
    (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma eisQ_apply (τ : ℍ) : eisQ f τ = ∑ r : ZMod N, moebCoeff N r * eis2 (eisWr f r) τ := by
  rw [eisQ, modularForm_sum_apply]
  rfl

lemma eisQ_slash (γ : SL(2, ℤ)) :
    (⇑(eisQ f) : ℍ → ℂ) ∣[(2 : ℤ)] γ =
      fun τ => ∑ r : ZMod N, moebCoeff N r * ((eis2 (eisWr f r)) ∣[(2 : ℤ)] γ) τ := by
  ext τ
  rw [ModularForm.SL_slash_apply, eisQ_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [ModularForm.SL_slash_apply, mul_assoc]

/-- **The constant term of $E_f$ at $\gamma\infty$ is $c_f(\gamma) - 2\kappa$.** -/
theorem tendsto_eisQ_slash (γ : SL(2, ℤ)) :
    Tendsto ((⇑(eisQ f) : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (cuspVal f γ - 2 * kappa f)) := by
  rw [eisQ_slash]
  have h := tendsto_finsetSum (Finset.univ : Finset (ZMod N)) fun r _ =>
    (tendsto_eis2_slash (eisWr f r) (totalSum_eisWr f r) γ).const_mul (moebCoeff N r)
  set x := (cuspVec N γ).1
  set y := (cuspVec N γ).2
  set φ : ZMod N → ℂ := fun u => eisW f (u * x) (u * y) with hφ
  have hval : ∀ r : ZMod N, ∑' n : ℤ, wt (eisWr f r) (-(n * γ 1 0)) (n * γ 0 0) * ((n : ℂ) ^ 2)⁻¹ =
      ∑' n : ℤ, φ (r * (n : ZMod N)) * ((n : ℂ) ^ 2)⁻¹ := by
    intro r
    refine tsum_congr fun n => ?_
    simp only [wt, eisWr, hφ, x, y, cuspVec]
    push_cast
    ring_nf
  simp_rw [hval] at h
  rw [moebius_const φ (fun u => by simp only [hφ, neg_mul]; exact eisW_neg f _ _)] at h
  simp only [hφ, one_mul, x, y, eisW_cuspVec] at h
  convert h using 2
  ring

/-! ### The mass condition $\kappa = 0$ -/

lemma tendsto_sub_eisQ_slash (γ : SL(2, ℤ)) :
    Tendsto ((⇑(f - eisQ f) : ℍ → ℂ) ∣[(2 : ℤ)] γ) UpperHalfPlane.atImInfty (𝓝 (2 * kappa f)) := by
  have h := (tendsto_cuspVal f γ).sub (tendsto_eisQ_slash f γ)
  rw [show cuspVal f γ - (cuspVal f γ - 2 * kappa f) = 2 * kappa f by ring] at h
  refine h.congr fun τ => ?_
  simp [ModularForm.SL_slash_apply, sub_mul]

/-- **$\kappa = 0$:** the trace of $f - E_f$ to $\mathrm{SL}_2(\mathbb{Z})$ is a level-one weight-2 form, hence $0$, and it tends to
$[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_1(N)]\cdot 2\kappa$. -/
theorem kappa_eq_zero : kappa f = 0 := by
  classical
  have htr : ModularForm.trace 𝒮ℒ (f - eisQ f) = 0 :=
    rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero _
  have hfun := congrArg (fun F : ModularForm 𝒮ℒ 2 => (⇑F : ℍ → ℂ)) htr
  simp only [ModularForm.coe_trace] at hfun
  let _ : Fintype (𝒮ℒ ⧸ (((Γ₁ N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ) :=
    Fintype.ofFinite _
  have hq : ∀ q : 𝒮ℒ ⧸ (((Γ₁ N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ,
      Tendsto (SlashInvariantForm.quotientFunc (f - eisQ f) q)
        UpperHalfPlane.atImInfty (𝓝 (2 * kappa f)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      rw [SlashInvariantForm.quotientFunc_mk]
      obtain ⟨e, he⟩ := r.2
      have : (r.val)⁻¹ = ((e⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
        rw [← he, ← map_inv]; rfl
      rw [this, ← ModularForm.SL_slash]
      exact tendsto_sub_eisQ_slash f e⁻¹
  have hsum := tendsto_finsetSum Finset.univ fun q _ => hq q
  have hzero : Tendsto (fun τ : ℍ => ∑ q : 𝒮ℒ ⧸ (((Γ₁ N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ, SlashInvariantForm.quotientFunc (f - eisQ f) q τ)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    have : (fun τ : ℍ => ∑ q : 𝒮ℒ ⧸ (((Γ₁ N : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ, SlashInvariantForm.quotientFunc (f - eisQ f) q τ) = 0 := by
      ext τ
      have := congrFun hfun τ
      simp only [Finset.sum_apply] at this
      convert this using 1
    rw [this]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique (hsum.congr fun τ => by simp [Finset.sum_apply]) hzero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at heq
  have hcard : (Fintype.card (𝒮ℒ ⧸ (((Γ₁ N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ))).subgroupOf 𝒮ℒ) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨⟦1⟧⟩).ne'
  have := (mul_eq_zero.mp heq).resolve_left hcard
  simpa using this

/-- **$f - E_f$ is a cusp form.** -/
@[kb "diamondshurman2005" "§4.5–4.6 (M_k = E_k ⊕ S_k), weight 2 [unverified]"]
noncomputable def cuspPart : CuspForm (Γ₁ N) 2 where
  toSlashInvariantForm := (f - eisQ f).toSlashInvariantForm
  holo' := (f - eisQ f).holo'
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    have h := tendsto_sub_eisQ_slash f γ
    rw [kappa_eq_zero, mul_zero] at h
    exact h

@[simp] theorem cuspPart_apply (τ : ℍ) : cuspPart f τ = f τ - eisQ f τ := rfl

end QuadFormsKB.Siegel.GenusEis
