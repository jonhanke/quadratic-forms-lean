/-
# The double coset mass of $K'$ for every class number: $\mathrm{dcMass}(\Gamma, K') = h_F^{-1}\sum_{[J]}w_J^{-1}$


**Layer:** $F$ totally real (any class number), $D = (a,b)_F$ totally definite, $\mathcal O \supseteq \mathcal O_F\langle1,i,j,k\rangle$ maximal,
$L = \mathcal O^0$, $Q = \langle -a,-b,ab\rangle$, $G = SO(Q)(\mathbb A_f)$, $\Gamma = SO(Q)(F)$, $K' = \prod_vc_v(\mathcal O_v^\times)$.

By `TernaryMassNF` the double cosets $\Gamma\backslash G/K'$ are the left ideal classes modulo $\mathrm{Cl}(F)$ (`TernaryClsNF`). For the coset $y_J$
of an element attached to $J$:
* the **stabilizer homomorphism** $\varphi : \mathrm{Stab}_\Gamma(y_J) \to \mathrm{Cl}(F)$, $c(\beta) \mapsto [\mathfrak a][\mathfrak b]^{-1}$ for
  $\mathfrak bJ = \mathfrak aJ\beta^{-1}$ (`stabHom`; well defined by `scaleIdeal_cancel`), has image $\mathrm{Stab}_{\mathrm{Cl}(F)}[J]$ and kernel
  $\cong \Gamma_J/\mathcal O_F^\times$; hence **$|\mathrm{Stab}_\Gamma(y_J)| = [\Gamma_J:\mathcal O_F^\times]\cdot|\mathrm{Stab}_{\mathrm{Cl}(F)}[J]|$**;
* with orbit–stabilizer for $\mathrm{Cl}(F)$: **`dcMass_KpNF_eq`**: $h_F\cdot\mathrm{dcMass}(\Gamma, K') = \sum_{[J]\ne0}[\Gamma_J:\mathcal O_F^\times]^{-1}$.

Source: Voight 2021, §§26.5 (Eichler's mass formula with $h_F$, the class group acting on classes); Weil 1982, §3.7(a), §2.4, p. 23 and Lemma 2.4.2, p. 26.
-/
import QuadFormsKB.Tamagawa.TernaryMassNF
import QuadFormsKB.Tamagawa.TernaryClsNF

open NumberField IsDedekindDomain Matrix Quaternion WithZero MulAction
open scoped RestrictedProduct nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity.NF IsLocalization

attribute [-instance] NumberField.RingOfIntegers.instAlgebra

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} {O : Subalgebra (𝓞 F) (QuatF F a b)}

/-! ### Set-level identities for $\mathfrak aJ\gamma$ -/

section Sets

open Gen

/-- $\mathfrak cJ$ as a set. -/
abbrev Sc (J : Ideal O) (𝔠 : Ideal (𝓞 F)) : Set (QuatF F a b) := (scaleSet 𝔠 (idealSet J) : Set (QuatF F a b))

theorem Sc_eq_idealSet (J : Ideal O) (𝔠 : Ideal (𝓞 F)) : Sc J 𝔠 = idealSet (scaleIdeal 𝔠 J) :=
  (idealSet_scaleIdeal 𝔠 J).symm

theorem Sc_top (J : Ideal O) : Sc J ⊤ = idealSet J := by rw [Sc_eq_idealSet, idealSet_scaleIdeal_top]

theorem Sc_mul (J : Ideal O) (𝔠 𝔡 : Ideal (𝓞 F)) :
    (scaleSet 𝔠 (Sc J 𝔡) : Set (QuatF F a b)) = Sc J (𝔠 * 𝔡) := by
  rw [Sc, scaleSet_scaleSet]

theorem scale_both {J : Ideal O} {𝔞 𝔟 : Ideal (𝓞 F)} {δ : QuatF F a b} (h : Sc J 𝔟 = rTrans (Sc J 𝔞) δ)
    (𝔠 : Ideal (𝓞 F)) : Sc J (𝔠 * 𝔟) = rTrans (Sc J (𝔠 * 𝔞)) δ := by
  rw [← Sc_mul, ← Sc_mul, h, scaleSet_rTrans]

theorem Sc_span_mul (J : Ideal O) (μ : 𝓞 F) (𝔠 : Ideal (𝓞 F)) :
    Sc J (Ideal.span {μ} * 𝔠) = rTrans (Sc J 𝔠) (algebraMap (𝓞 F) (QuatF F a b) μ) := by
  rw [← Sc_mul, scaleSet_span_singleton]

theorem rTrans_mul_rTrans_inv (S : Set (QuatF F a b)) (γ δ : (QuatF F a b)ˣ) :
    rTrans (rTrans S (γ : QuatF F a b)) ((γ⁻¹ * δ : (QuatF F a b)ˣ) : QuatF F a b) = rTrans S (δ : QuatF F a b) := by
  rw [rTrans_rTrans, ← Units.val_mul, mul_inv_cancel_left]

/-- **Cancellation with a scalar:** $\mathfrak cJ\,(p/q) = \mathfrak dJ$ gives $(p)\mathfrak c = (q)\mathfrak d$. -/
theorem span_mul_eq_of_Sc_scalar (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {𝔠 𝔡 : Ideal (𝓞 F)}
    (h𝔠 : 𝔠 ≠ ⊥) (h𝔡 : 𝔡 ≠ ⊥) {p q : 𝓞 F} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (h : rTrans (Sc J 𝔠) (algebraMap F (QuatF F a b) (algebraMap (𝓞 F) F p / algebraMap (𝓞 F) F q)) = Sc J 𝔡) :
    Ideal.span {p} * 𝔠 = Ideal.span {q} * 𝔡 := by
  have hqF : algebraMap (𝓞 F) F q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hq0
  have h2 : rTrans (Sc J 𝔠) (algebraMap (𝓞 F) (QuatF F a b) p) = rTrans (Sc J 𝔡) (algebraMap (𝓞 F) (QuatF F a b) q) := by
    rw [← h, rTrans_rTrans]
    congr 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b) p, IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b) q,
      ← map_mul]
    congr 1
    field_simp
  rw [← Sc_span_mul, ← Sc_span_mul, Sc_eq_idealSet, Sc_eq_idealSet] at h2
  have hp' : Ideal.span {p} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hq' : Ideal.span {q} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0
  exact scaleIdeal_cancel hO hJ (mul_ne_zero hp' h𝔠) (mul_ne_zero hq' h𝔡) h2

theorem mk0_eq_of_Sc_scalar (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {𝔠 𝔡 : Ideal (𝓞 F)}
    (h𝔠 : 𝔠 ≠ ⊥) (h𝔡 : 𝔡 ≠ ⊥) {r : F} (hr : r ≠ 0)
    (h : rTrans (Sc J 𝔠) (algebraMap F (QuatF F a b) r) = Sc J 𝔡) :
    ClassGroup.mk0 (nzIdeal h𝔠) = ClassGroup.mk0 (nzIdeal h𝔡) := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) r
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hr
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨p, q, hp0, hq0, span_mul_eq_of_Sc_scalar hO hJ h𝔠 h𝔡 hp0 hq0 h⟩

/-- **A scalar fixing $J$ is a unit of $\mathcal O_F$.** -/
theorem exists_unit_of_rTrans_scalar (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {r : F}
    (hr : r ≠ 0) (h : rTrans (idealSet J) (algebraMap F (QuatF F a b) r) = idealSet J) :
    ∃ w : (𝓞 F)ˣ, algebraMap (𝓞 F) F w = r := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) r
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hr
  have h' := span_mul_eq_of_Sc_scalar hO hJ top_ne_bot top_ne_bot hp0 hq0 (by rw [Sc_top]; exact h)
  rw [Ideal.mul_top, Ideal.mul_top, Ideal.span_singleton_eq_span_singleton] at h'
  obtain ⟨u, hu⟩ := h'
  refine ⟨u⁻¹, ?_⟩
  have hpF : algebraMap (𝓞 F) F p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hp0
  have huF : algebraMap (𝓞 F) F (u : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 u.ne_zero
  have hu' : algebraMap (𝓞 F) F ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * algebraMap (𝓞 F) F (u : 𝓞 F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [← hu, map_mul, eq_div_iff (mul_ne_zero hpF huF)]
  linear_combination (algebraMap (𝓞 F) F p) * hu'

end Sets

/-! ### The stabilizer homomorphism -/

section Stab

open Gen

/-- $\beta \mapsto c(\beta)$ as a homomorphism $D^\times \to \Gamma$. -/
def rhoNF : (QuatF F a b)ˣ →* GamNF a b where
  toFun β := ⟨⟨diagF (QP a b) (cv0NF β), diagF_cv0NF_mem_soAf β⟩, Subgroup.mem_subgroupOf.2 ⟨cv0NF β, rfl⟩⟩
  map_one' := by ext1; ext1; simp
  map_mul' x y := by ext1; ext1; simp

@[simp] theorem coe_rhoNF (β : (QuatF F a b)ˣ) :
    (((rhoNF β : GamNF a b) : soAf (QP a b)) : OAf (QP a b)) = diagF (QP a b) (cv0NF β) := rfl

/-- The coset of an element attached to $J$. -/
abbrev cosetJ {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g) : soAf (QP a b) ⧸ KpNF O :=
  QuotientGroup.mk ⟨g, isGenNF_mem_soAf hg⟩

theorem mem_stab_iff {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g) (γ : GamNF a b) :
    γ ∈ stabilizer (GamNF a b) (cosetJ hg) ↔ ((((γ : soAf (QP a b)) : OAf (QP a b)) * g)⁻¹ * g) ∈ KANF O := by
  rw [MulAction.mem_stabilizer_iff]
  change (QuotientGroup.mk ((γ : soAf (QP a b)) * ⟨g, isGenNF_mem_soAf hg⟩) : soAf (QP a b) ⧸ KpNF O) =
    QuotientGroup.mk ⟨g, isGenNF_mem_soAf hg⟩ ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

/-- **Representation data** of $\gamma \in \Gamma$ relative to $J$: $\gamma = c(\beta)$ and $\mathfrak bJ = \mathfrak aJ\beta^{-1}$. -/
def RepData (J : Ideal O) (γ : GamNF a b) (𝔞 𝔟 : Ideal (𝓞 F)) : Prop :=
  𝔞 ≠ ⊥ ∧ 𝔟 ≠ ⊥ ∧ ∃ β : (QuatF F a b)ˣ, ((γ : soAf (QP a b)) : OAf (QP a b)) = diagF (QP a b) (cv0NF β) ∧
    Sc J 𝔟 = rTrans (Sc J 𝔞) ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)

theorem exists_repData (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : OAf (QP a b)} (hg : IsGenNF J g) {γ : GamNF a b}
    (hγ : γ ∈ stabilizer (GamNF a b) (cosetJ hg)) : ∃ 𝔞 𝔟, RepData J γ 𝔞 𝔟 := by
  have hγr : (((γ : soAf (QP a b)) : OAf (QP a b))) ∈ ratPoints (QP a b) := Subgroup.mem_subgroupOf.1 γ.2
  obtain ⟨β, hβ⟩ := exists_cv0NF_of_mem ha hb hγr (γ : soAf (QP a b)).2
  have hst := (mem_stab_iff hg γ).1 hγ
  rw [hβ] at hst
  obtain ⟨𝔞, 𝔟, h𝔞, h𝔟, h⟩ := exists_scale_of_mem_KANF ha hO hJ hJ hg hg β hst
  exact ⟨𝔞, 𝔟, h𝔞, h𝔟, β, hβ, by rw [Sc_eq_idealSet, Sc_eq_idealSet, h]⟩

theorem inv_mul_eq_scalar {β β' : (QuatF F a b)ˣ} {r : F} (hr : (β : QuatF F a b) = algebraMap F (QuatF F a b) r * β')
    (hr0 : r ≠ 0) : ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) * β' = algebraMap F (QuatF F a b) r⁻¹ := by
  have h1 : (β : QuatF F a b) * algebraMap F (QuatF F a b) r⁻¹ = β' := by
    rw [hr, mul_assoc, ← Algebra.commutes r⁻¹ (β' : QuatF F a b), ← mul_assoc, ← map_mul, mul_inv_cancel₀ hr0,
      map_one, one_mul]
  rw [← h1, ← mul_assoc, Units.inv_mul, one_mul]

theorem nzIdeal_mul {𝔞 𝔟 : Ideal (𝓞 F)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    nzIdeal (mul_ne_zero h𝔞 h𝔟 : 𝔞 * 𝔟 ≠ ⊥) = nzIdeal h𝔞 * nzIdeal h𝔟 := rfl

/-- **The class $[\mathfrak a][\mathfrak b]^{-1}$ does not depend on the representation data.** -/
theorem repData_unique (ha : a ≠ 0) (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥) {γ : GamNF a b}
    {𝔞 𝔟 𝔞' 𝔟' : Ideal (𝓞 F)} (h : RepData J γ 𝔞 𝔟) (h' : RepData J γ 𝔞' 𝔟') :
    ClassGroup.mk0 (nzIdeal h.1) * (ClassGroup.mk0 (nzIdeal h.2.1))⁻¹ =
      ClassGroup.mk0 (nzIdeal h'.1) * (ClassGroup.mk0 (nzIdeal h'.2.1))⁻¹ := by
  obtain ⟨h𝔞, h𝔟, β, hβ, h1⟩ := h
  obtain ⟨h𝔞', h𝔟', β', hβ', h2⟩ := h'
  have hcv : cv0NF β = cv0NF β' := diagF_injective_QP (hβ.symm.trans hβ')
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  obtain ⟨r, hr⟩ := (cvHom_eq_iff (b := algebraMap (𝓞 F) F b) two_ne_zero ha' 1 β β').1 (congrArg Subtype.val hcv)
  have hr0 : r ≠ 0 := by rintro rfl; exact β.ne_zero (by rw [hr, map_zero, zero_mul])
  have e1 := scale_both h1 𝔟'
  have e2 := scale_both h2 𝔟
  rw [mul_comm 𝔟 𝔟', e1] at e2
  -- `𝔟'𝔞J β⁻¹ = 𝔟𝔞'J β'⁻¹`, so `𝔟'𝔞J r⁻¹ = 𝔟𝔞'J`
  have e3 : rTrans (Sc J (𝔟' * 𝔞)) (algebraMap F (QuatF F a b) r⁻¹) = Sc J (𝔟 * 𝔞') := by
    have := congrArg (fun S => rTrans S (β' : QuatF F a b)) e2
    simp only [rTrans_rTrans] at this
    rw [inv_mul_eq_scalar hr hr0, Units.inv_mul, rTrans_one] at this
    exact this
  have hc := mk0_eq_of_Sc_scalar hO hJ (mul_ne_zero h𝔟' h𝔞) (mul_ne_zero h𝔟 h𝔞') (inv_ne_zero hr0) e3
  rw [nzIdeal_mul h𝔟' h𝔞, nzIdeal_mul h𝔟 h𝔞', map_mul, map_mul] at hc
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, mul_comm (ClassGroup.mk0 (nzIdeal h𝔞)), hc,
    mul_comm]

theorem repData_one (J : Ideal O) : RepData J (1 : GamNF a b) ⊤ ⊤ :=
  ⟨top_ne_bot, top_ne_bot, 1, by rw [map_one, map_one]; rfl, by rw [inv_one, Units.val_one, rTrans_one]⟩

theorem repData_mul {J : Ideal O} {γ₁ γ₂ : GamNF a b} {𝔞₁ 𝔟₁ 𝔞₂ 𝔟₂ : Ideal (𝓞 F)} (h₁ : RepData J γ₁ 𝔞₁ 𝔟₁)
    (h₂ : RepData J γ₂ 𝔞₂ 𝔟₂) : RepData J (γ₁ * γ₂) (𝔞₁ * 𝔞₂) (𝔟₁ * 𝔟₂) := by
  obtain ⟨h𝔞₁, h𝔟₁, β₁, hβ₁, e₁⟩ := h₁
  obtain ⟨h𝔞₂, h𝔟₂, β₂, hβ₂, e₂⟩ := h₂
  refine ⟨mul_ne_zero h𝔞₁ h𝔞₂, mul_ne_zero h𝔟₁ h𝔟₂, β₁ * β₂, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, hβ₁, hβ₂, map_mul]
  · have f₂ := scale_both e₂ 𝔞₁
    have f₁ := scale_both e₁ 𝔟₂
    rw [_root_.mul_inv_rev, Units.val_mul, ← rTrans_rTrans, ← f₂, mul_comm 𝔞₁ 𝔟₂, ← f₁, mul_comm]

/-- The chosen representation data of an element of the stabilizer. -/
def repA (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) (γ : stabilizer (GamNF a b) (cosetJ hg)) : Ideal (𝓞 F) :=
  (exists_repData ha hb hO hJ hg γ.2).choose

def repB (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) (γ : stabilizer (GamNF a b) (cosetJ hg)) : Ideal (𝓞 F) :=
  (exists_repData ha hb hO hJ hg γ.2).choose_spec.choose

theorem repSpec (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) (γ : stabilizer (GamNF a b) (cosetJ hg)) :
    RepData J γ (repA ha hb hO hJ hg γ) (repB ha hb hO hJ hg γ) :=
  (exists_repData ha hb hO hJ hg γ.2).choose_spec.choose_spec

/-- The class $[\mathfrak a][\mathfrak b]^{-1}$ of representation data. -/
def repVal {J : Ideal O} {γ : GamNF a b} {𝔞 𝔟 : Ideal (𝓞 F)} (h : RepData J γ 𝔞 𝔟) : ClassGroup (𝓞 F) :=
  ClassGroup.mk0 (nzIdeal h.1) * (ClassGroup.mk0 (nzIdeal h.2.1))⁻¹

theorem repVal_mul {J : Ideal O} {γ₁ γ₂ : GamNF a b} {𝔞₁ 𝔟₁ 𝔞₂ 𝔟₂ : Ideal (𝓞 F)} (h₁ : RepData J γ₁ 𝔞₁ 𝔟₁)
    (h₂ : RepData J γ₂ 𝔞₂ 𝔟₂) : repVal (repData_mul h₁ h₂) = repVal h₁ * repVal h₂ := by
  unfold repVal
  rw [nzIdeal_mul h₁.1 h₂.1, nzIdeal_mul h₁.2.1 h₂.2.1, map_mul, map_mul, mul_inv]
  ac_rfl

theorem repVal_one (J : Ideal O) : repVal (repData_one (O := O) (a := a) (b := b) J) = 1 := by
  unfold repVal
  exact mul_inv_cancel _

theorem repVal_unique (ha : a ≠ 0) (hO : IsOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {γ γ' : GamNF a b} (he : γ = γ') {𝔞 𝔟 𝔞' 𝔟' : Ideal (𝓞 F)} (h : RepData J γ 𝔞 𝔟) (h' : RepData J γ' 𝔞' 𝔟') :
    repVal h = repVal h' := by
  subst he; exact repData_unique ha hO hJ h h'

/-- **The stabilizer homomorphism** $\mathrm{Stab}_\Gamma(y_J) \to \mathrm{Cl}(F)$, $c(\beta) \mapsto [\mathfrak a][\mathfrak b]^{-1}$
($\mathfrak bJ = \mathfrak aJ\beta^{-1}$). -/
def stabHom (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) : stabilizer (GamNF a b) (cosetJ hg) →* ClassGroup (𝓞 F) where
  toFun γ := repVal (repSpec ha hb hO hJ hg γ)
  map_one' := (repVal_unique ha hO.1 hJ rfl (repSpec ha hb hO hJ hg 1) (repData_one J)).trans (repVal_one J)
  map_mul' γ₁ γ₂ := (repVal_unique ha hO.1 hJ rfl (repSpec ha hb hO hJ hg (γ₁ * γ₂))
      (repData_mul (repSpec ha hb hO hJ hg γ₁) (repSpec ha hb hO hJ hg γ₂))).trans (repVal_mul _ _)

theorem stabHom_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) (γ : stabilizer (GamNF a b) (cosetJ hg)) {𝔞 𝔟 : Ideal (𝓞 F)}
    (h : RepData J γ 𝔞 𝔟) :
    stabHom ha hb hO hJ hg γ = repVal h :=
  repVal_unique ha hO.1 hJ rfl (repSpec ha hb hO hJ hg γ) h

theorem nzIdeal_top : nzIdeal (top_ne_bot : (⊤ : Ideal (𝓞 F)) ≠ ⊥) = 1 :=
  Subtype.ext Ideal.one_eq_top.symm

theorem repVal_smul {J : Ideal O} {γ : GamNF a b} {𝔞 𝔟 : Ideal (𝓞 F)} (h : RepData J γ 𝔞 𝔟) :
    repVal h • Quotient.mk (idealSetoid O) J = Quotient.mk (idealSetoid O) J := by
  have hrel : IdealRel (scaleIdeal 𝔞 J) (scaleIdeal 𝔟 J) := by
    obtain ⟨-, -, β, -, e⟩ := h
    exact ⟨β⁻¹, by rw [← Sc_eq_idealSet, ← Sc_eq_idealSet, e]⟩
  have hAB : ClassGroup.mk0 (nzIdeal h.1) • Quotient.mk (idealSetoid O) J =
      ClassGroup.mk0 (nzIdeal h.2.1) • Quotient.mk (idealSetoid O) J := by
    rw [mk0_smul_mk, mk0_smul_mk]; exact Quotient.sound hrel
  unfold repVal
  rw [mul_comm, mul_smul, hAB, inv_smul_smul]

theorem exists_stab_of_smul_eq (ha : a ≠ 0) {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g)
    (cl : ClassGroup (𝓞 F)) (hcl : cl • Quotient.mk (idealSetoid O) J = Quotient.mk (idealSetoid O) J) :
    ∃ γ : stabilizer (GamNF a b) (cosetJ hg), RepData J γ ((clsIdeal cl : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) ⊤ := by
  have h𝔞 := clsIdeal_ne_bot' cl
  rw [cls_smul_def, Gen.classScale_mk] at hcl
  obtain ⟨δ, hδ⟩ := Quotient.exact hcl
  have hδ' : idealSet (scaleIdeal ⊤ J) = rTrans (idealSet (scaleIdeal
      ((clsIdeal cl : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) J)) (δ : QuatF F a b) := by
    rw [idealSet_scaleIdeal_top]; exact hδ
  have hmem : rhoNF δ⁻¹ ∈ stabilizer (GamNF a b) (cosetJ hg) := by
    rw [mem_stab_iff, coe_rhoNF]
    exact mem_KANF_of_scale ha hg hg h𝔞 top_ne_bot δ hδ'
  exact ⟨⟨rhoNF δ⁻¹, hmem⟩, h𝔞, top_ne_bot, δ⁻¹, rfl, by rw [inv_inv, Sc_top, Sc_eq_idealSet]; exact hδ⟩

set_option maxHeartbeats 2000000 in
/-- **The image of the stabilizer homomorphism is the stabilizer of $[J]$ in $\mathrm{Cl}(F)$.** -/
theorem range_stabHom (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : OAf (QP a b)} (hg : IsGenNF J g) :
    (stabHom ha hb hO hJ hg).range = stabilizer (ClassGroup (𝓞 F)) (Quotient.mk (idealSetoid O) J) := by
  ext cl
  rw [MonoidHom.mem_range, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [stabHom_eq ha hb hO hJ hg γ (repSpec ha hb hO hJ hg γ)]
    exact repVal_smul _
  · intro hcl
    obtain ⟨γ, hrep⟩ := exists_stab_of_smul_eq ha hg cl hcl
    refine ⟨γ, ?_⟩
    rw [stabHom_eq ha hb hO hJ hg γ hrep]
    unfold repVal
    rw [nzIdeal_top, map_one, inv_one, mul_one]
    exact mk0_clsIdeal cl

theorem rhoNF_mem_stab (ha : a ≠ 0) {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g) (δ : rStab J) :
    rhoNF (δ : (QuatF F a b)ˣ) ∈ stabilizer (GamNF a b) (cosetJ hg) := by
  have hδ : (δ : (QuatF F a b)ˣ)⁻¹ ∈ rStab J := (rStab J).inv_mem δ.2
  have h : idealSet (scaleIdeal ⊤ J) = rTrans (idealSet (scaleIdeal ⊤ J))
      (((δ : (QuatF F a b)ˣ)⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) := by
    rw [idealSet_scaleIdeal_top]; exact (mem_rStab.1 hδ).symm
  rw [mem_stab_iff, coe_rhoNF]
  have := mem_KANF_of_scale ha hg hg top_ne_bot top_ne_bot _ h
  rwa [inv_inv] at this

/-- $\delta \mapsto c(\delta)$, $\Gamma_J \to \mathrm{Stab}_\Gamma(y_J)$. -/
def psiHom (ha : a ≠ 0) {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g) :
    rStab J →* stabilizer (GamNF a b) (cosetJ hg) :=
  (rhoNF.comp (rStab J).subtype).codRestrict _ (rhoNF_mem_stab ha hg)

theorem psiHom_coe (ha : a ≠ 0) {J : Ideal O} {g : OAf (QP a b)} (hg : IsGenNF J g) (δ : rStab J) :
    ((psiHom ha hg δ : stabilizer (GamNF a b) (cosetJ hg)) : GamNF a b) = rhoNF (δ : (QuatF F a b)ˣ) := rfl

theorem cv0NF_unitOf (ha : a ≠ 0) {μ : 𝓞 F} (hμ : μ ≠ 0) : cv0NF (unitOf (a := a) (b := b) hμ) = 1 := by
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  ext1
  refine (cvHom_eq_one_iff (b := algebraMap (𝓞 F) F b) two_ne_zero ha' 1 _).2 ⟨algebraMap (𝓞 F) F μ, ?_⟩
  rw [unitOf_val, IsScalarTower.algebraMap_apply (𝓞 F) F (QuatF F a b)]

theorem rhoNF_eq_iff (ha : a ≠ 0) (β δ : (QuatF F a b)ˣ) :
    rhoNF β = rhoNF δ ↔ cv0NF β = cv0NF δ := by
  constructor
  · intro h
    exact diagF_injective_QP (congrArg (fun γ : GamNF a b => ((γ : soAf (QP a b)) : OAf (QP a b))) h)
  · intro h
    apply Subtype.ext; apply Subtype.ext
    simp only [coe_rhoNF, h]

set_option maxHeartbeats 2000000 in
/-- **The kernel of the stabilizer homomorphism is the image of $\Gamma_J$.** -/
theorem range_psiHom (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : OAf (QP a b)} (hg : IsGenNF J g) :
    (psiHom ha hg).range = (stabHom ha hb hO hJ hg).ker := by
  ext γ
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨δ, rfl⟩
    have hδ : ((δ : (QuatF F a b)ˣ))⁻¹ ∈ rStab J := (rStab J).inv_mem δ.2
    have hrep : RepData J ((psiHom ha hg δ : stabilizer (GamNF a b) (cosetJ hg)) : GamNF a b) ⊤ ⊤ :=
      ⟨top_ne_bot, top_ne_bot, δ, rfl, by rw [Sc_top]; exact (mem_rStab.1 hδ).symm⟩
    rw [stabHom_eq ha hb hO hJ hg _ hrep]
    exact mul_inv_cancel _
  · intro h1
    have h := repSpec ha hb hO hJ hg γ
    rw [stabHom_eq ha hb hO hJ hg γ h] at h1
    obtain ⟨h𝔞, h𝔟, β, hβ, e⟩ := h
    have hcls : ClassGroup.mk0 (nzIdeal h𝔞) = ClassGroup.mk0 (nzIdeal h𝔟) := mul_inv_eq_one.1 h1
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 hcls
    have e1 := scale_both e (Ideal.span {x})
    rw [coe_nzIdeal, coe_nzIdeal] at hxy
    rw [hxy, Sc_span_mul, Sc_span_mul, rTrans_rTrans] at e1
    -- `δ₀ = y β⁻¹ x⁻¹` fixes `𝔟J`
    set δ₀ : (QuatF F a b)ˣ := unitOf hy * β⁻¹ * (unitOf hx)⁻¹
    have hδ₀ : δ₀ ∈ rStab (scaleIdeal (repB ha hb hO hJ hg γ) J) := by
      rw [mem_rStab, ← Sc_eq_idealSet]
      have := congrArg (fun S => rTrans S (((unitOf (a := a) (b := b) hx)⁻¹ : (QuatF F a b)ˣ) : QuatF F a b)) e1
      simp only [rTrans_rTrans] at this
      rw [← unitOf_val hx, Units.mul_inv, rTrans_one] at this
      have hδc : (δ₀ : QuatF F a b) = algebraMap (𝓞 F) (QuatF F a b) y * ((β⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) *
          (((unitOf (a := a) (b := b) hx)⁻¹ : (QuatF F a b)ˣ) : QuatF F a b) := by
        simp only [δ₀, Units.val_mul, unitOf_val]
      rw [hδc, ← this]
    obtain ⟨𝔟', μ, hμ, h𝔟'⟩ := exists_mul_eq_span h𝔟
    rw [rStab_scaleIdeal hμ h𝔟'] at hδ₀
    refine ⟨⟨δ₀, hδ₀⟩⁻¹, ?_⟩
    apply Subtype.ext
    rw [psiHom_coe]
    have hcv : cv0NF δ₀⁻¹ = cv0NF β := by
      simp only [δ₀, map_mul, map_inv, cv0NF_unitOf ha, inv_one, one_mul, mul_one, inv_inv]
    have h2 := (rhoNF_eq_iff ha _ _).2 hcv
    change rhoNF δ₀⁻¹ = (γ : GamNF a b)
    rw [h2]
    apply Subtype.ext; apply Subtype.ext
    rw [coe_rhoNF, ← hβ]

set_option maxHeartbeats 4000000 in
theorem ker_psiHom (ha : a ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O} (hJ : leftNrdIdeal J ≠ ⊥)
    {g : OAf (QP a b)} (hg : IsGenNF J g) : (psiHom ha hg).ker = centralUnitsIn (R := 𝓞 F) J := by
  have ha' : algebraMap (𝓞 F) F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 ha
  ext δ
  rw [MonoidHom.mem_ker, centralUnitsIn, Subgroup.mem_subgroupOf]
  have e1 : psiHom ha hg δ = 1 ↔ cv0NF (δ : (QuatF F a b)ˣ) = 1 := by
    have e2 : psiHom ha hg δ = 1 ↔ rhoNF (δ : (QuatF F a b)ˣ) = rhoNF 1 := by
      rw [map_one]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [e2, rhoNF_eq_iff ha, map_one]
  rw [e1]
  constructor
  · intro h1
    have h4 : cvHom (1 : GL (Fin 3) F) (δ : (QuatF F a b)ˣ) = 1 := congrArg Subtype.val h1
    obtain ⟨r, hr⟩ := (cvHom_eq_one_iff (b := algebraMap (𝓞 F) F b) two_ne_zero ha' 1 _).1 h4
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact (δ : (QuatF F a b)ˣ).ne_zero (by rw [hr]; simp)
    have hrJ : rTrans (idealSet J) (algebraMap F (QuatF F a b) r) = idealSet J := by
      have := mem_rStab.1 δ.2; rwa [hr] at this
    obtain ⟨w, hw⟩ := exists_unit_of_rTrans_scalar hO.1 hJ hr0 hrJ
    refine ⟨w, Units.ext ?_⟩
    rw [hr, ← hw]; rfl
  · rintro ⟨w, hw⟩
    ext1
    refine (cvHom_eq_one_iff (b := algebraMap (𝓞 F) F b) two_ne_zero ha' 1 _).2 ⟨algebraMap (𝓞 F) F w, ?_⟩
    rw [← hw]; rfl

set_option maxHeartbeats 4000000 in
/-- **$|\mathrm{Stab}_\Gamma(y_J)| = [\Gamma_J : \mathcal O_F^\times]\cdot|\mathrm{Stab}_{\mathrm{Cl}(F)}[J]|$.** -/
theorem card_stab_eq (ha : a ≠ 0) (hb : b ≠ 0) (hO : IsMaximalOrder (𝓞 F) F O) {J : Ideal O}
    (hJ : leftNrdIdeal J ≠ ⊥) {g : OAf (QP a b)} (hg : IsGenNF J g) :
    Nat.card (stabilizer (GamNF a b) (cosetJ hg)) =
      (centralUnitsIn (R := 𝓞 F) J).index * Nat.card (stabilizer (ClassGroup (𝓞 F)) (Quotient.mk (idealSetoid O) J)) := by
  have h1 := Subgroup.card_mul_index (stabHom ha hb hO hJ hg).ker
  rw [Subgroup.index_ker, range_stabHom ha hb hO hJ hg, ← range_psiHom ha hb hO hJ hg] at h1
  rw [← h1, ← ker_psiHom ha hO hJ hg, Subgroup.index_ker]

end Stab

/-! ### The mass -/

section Mass

open Gen

theorem mem_orbit_iff_NF (ha : a ≠ 0) (hb : b ≠ 0) {g g' : OAf (QP a b)} (hg : g ∈ soAf (QP a b))
    (hg' : g' ∈ soAf (QP a b)) :
    (QuotientGroup.mk (⟨g', hg'⟩ : soAf (QP a b)) : soAf (QP a b) ⧸ KpNF O) ∈
        orbit (GamNF a b) (QuotientGroup.mk (⟨g, hg⟩ : soAf (QP a b)) : soAf (QP a b) ⧸ KpNF O) ↔
      ∃ β : (QuatF F a b)ˣ, (diagF (QP a b) (cv0NF β) * g)⁻¹ * g' ∈ KANF O := by
  constructor
  · rintro ⟨γ, hγ⟩
    have hγ' : (QuotientGroup.mk ((γ : soAf (QP a b)) * ⟨g, hg⟩) : soAf (QP a b) ⧸ KpNF O) =
      QuotientGroup.mk ⟨g', hg'⟩ := hγ
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hγ'
    obtain ⟨β, hβ⟩ := exists_cv0NF_of_mem ha hb (Subgroup.mem_subgroupOf.1 γ.2) (γ : soAf (QP a b)).2
    refine ⟨β, ?_⟩
    rw [← hβ]; exact hγ'
  · rintro ⟨β, hβ⟩
    refine ⟨rhoNF β, ?_⟩
    change (QuotientGroup.mk (((rhoNF β : GamNF a b) : soAf (QP a b)) * ⟨g, hg⟩) : soAf (QP a b) ⧸ KpNF O) =
      QuotientGroup.mk ⟨g', hg'⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hβ

theorem card_orbit_mul_card_stab_cls (x : Quotient (idealSetoid O)) :
    Nat.card (orbit (ClassGroup (𝓞 F)) x) * Nat.card (stabilizer (ClassGroup (𝓞 F)) x) =
      NumberField.classNumber F := by
  rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ClassGroup (𝓞 F)) x),
    NumberField.classNumber, Nat.card_eq_fintype_card]

set_option maxHeartbeats 8000000 in
/-- **The double coset mass of $K'$ for every class number**:
$$h_F\cdot\mathrm{dcMass}(SO(Q)(F), K') = \sum_{[J]\ne0}\frac1{[\Gamma_J:\mathcal O_F^\times]}.$$ -/
@[kb "voight2021" "§26.5 (Eichler's mass formula with h_F; the class group acting on classes)"]
theorem classNumber_mul_dcMass_KpNF [IsTotallyReal F] (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b)
    (hO : IsMaximalOrder (𝓞 F) F O) (hstd : stdOrder F a b ≤ O) :
    (NumberField.classNumber F : ℝ) * dcMass (GamNF a b) (KpNF O) =
      ∑' c : {c : Quotient (idealSetoid O) // c.out ≠ ⊥}, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ := by
  classical
  have hdiv : ∀ x : QuatF F a b, nrd x = 0 → x = 0 := fun x hx => eq_zero_of_nrd_eq_zero hdef hx
  have : Finite (Quotient (idealSetoid O)) := Gen.finite_classes ha hb hO hdiv
  set C := {c : Quotient (idealSetoid O) // c.out ≠ ⊥}
  have : Finite C := Subtype.finite
  let _ : Fintype C := Fintype.ofFinite _
  have hJc : ∀ c : C, leftNrdIdeal c.1.out ≠ ⊥ := fun c => Gen.leftNrdIdeal_ne_bot hO.1 hdiv c.2
  choose g hg using fun c : C => exists_isGenNF ha hb hO (hJc c)
  set Y := orbitRel.Quotient (GamNF a b) (soAf (QP a b) ⧸ KpNF O)
  let Ψ : C → Y := fun c => Quotient.mk'' (cosetJ (hg c))
  -- the orbit relation in terms of ideal classes
  have hrel : ∀ c c' : C, Ψ c = Ψ c' ↔ ∃ cl : ClassGroup (𝓞 F), cl • c.1 = c'.1 := by
    intro c c'
    have e1 : Ψ c = Ψ c' ↔ (cosetJ (hg c')) ∈ orbit (GamNF a b) (cosetJ (hg c)) := by
      constructor
      · intro h
        have := Quotient.exact' h.symm
        rwa [orbitRel_apply] at this
      · intro h
        exact (Quotient.sound' (orbitRel_apply.2 h)).symm
    rw [e1, mem_orbit_iff_NF ha hb]
    conv_rhs => rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
    rw [exists_smul_eq_iff]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨𝔞, 𝔟, h𝔞, h𝔟, h⟩ := exists_scale_of_mem_KANF ha hO (hJc c) (hJc c') (hg c) (hg c') β hβ
      exact ⟨𝔞, 𝔟, h𝔞, h𝔟, ⟨β⁻¹, h⟩⟩
    · rintro ⟨𝔞, 𝔟, h𝔞, h𝔟, ⟨δ, hδ⟩⟩
      exact ⟨δ⁻¹, mem_KANF_of_scale ha (hg c) (hg c') h𝔞 h𝔟 δ hδ⟩
  -- surjectivity
  have hsurj : Function.Surjective Ψ := by
    intro ω
    induction ω using Quotient.inductionOn' with | h y => ?_
    induction y using QuotientGroup.induction_on with | H h => ?_
    obtain ⟨J, hJ, hJh⟩ := exists_isGenNF_of_mem ha hb hO hdiv h.2
    have hJ0 : J ≠ ⊥ := by
      rintro rfl
      apply hJ
      refine Ideal.span_eq_bot.2 fun r ⟨x, hx, hr⟩ => ?_
      have h0 : nrd (x : QuatF F a b) = 0 := by rw [show x = 0 from hx]; simp [nrd]
      rw [h0] at hr
      exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 hr
    have hrelJ : IdealRel (Quotient.mk (idealSetoid O) J).out J := by
      have := Quotient.exact (Quotient.out_eq (Quotient.mk (idealSetoid O) J))
      exact this
    have hout : (Quotient.mk (idealSetoid O) J).out ≠ ⊥ := fun h0 => hJ0 (eq_bot_of_idealRel_bot_nf (h0 ▸ hrelJ))
    refine ⟨⟨Quotient.mk (idealSetoid O) J, hout⟩, Quotient.sound' ?_⟩
    rw [orbitRel_apply]
    obtain ⟨δ, hδ⟩ := hrelJ
    have hδ' : idealSet (scaleIdeal ⊤ J) = rTrans (idealSet (scaleIdeal ⊤ (Quotient.mk (idealSetoid O) J).out))
        (δ : QuatF F a b) := by rw [idealSet_scaleIdeal_top, idealSet_scaleIdeal_top]; exact hδ
    have hmem := mem_KANF_of_scale ha (hg ⟨_, hout⟩) hJh top_ne_bot top_ne_bot δ hδ'
    have hh : h = ⟨(h : OAf (QP a b)), h.2⟩ := rfl
    rw [hh]
    exact MulAction.mem_orbit_symm.1 ((mem_orbit_iff_NF ha hb (isGenNF_mem_soAf (hg ⟨_, hout⟩)) h.2).2 ⟨_, hmem⟩)
  have : Finite Y := Finite.of_surjective Ψ hsurj
  let _ : Fintype Y := Fintype.ofFinite _
  -- the stabilizer orders
  set S : Y → ℕ := fun ω => Nat.card (stabilizer (GamNF a b) ω.out)
  have hS : ∀ c : C, S (Ψ c) = (centralUnitsIn (R := 𝓞 F) c.1.out).index *
      Nat.card (stabilizer (ClassGroup (𝓞 F)) c.1) := by
    intro c
    have h1 := card_stabilizer_of_mem_orbit (out_mem_orbit (Ψ c) (cosetJ (hg c)) rfl)
    simp only [S]
    rw [h1, card_stab_eq ha hb hO (hJc c) (hg c), Quotient.out_eq]
  -- the fibres
  set fib : Y → ℕ := fun ω => Nat.card {c : C // Ψ c = ω}
  have hfib : ∀ c : C, fib (Ψ c) = Nat.card (orbit (ClassGroup (𝓞 F)) c.1) := by
    intro c
    simp only [fib]
    refine Nat.card_congr
      { toFun := fun c' => ⟨c'.1.1, (hrel c c'.1).1 c'.2.symm⟩
        invFun := fun x => ⟨⟨x.1, ?_⟩, ?_⟩
        left_inv := fun c' => rfl
        right_inv := fun x => rfl }
    · obtain ⟨cl, hcl⟩ := x.2
      dsimp only at hcl
      rw [← hcl, ← Quotient.out_eq c.1, cls_smul_def, Gen.classScale_mk]
      intro h0
      have hrel0 : IdealRel (Quotient.mk (idealSetoid O)
          (scaleIdeal ((clsIdeal cl : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) c.1.out)).out
          (scaleIdeal ((clsIdeal cl : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) c.1.out) := by
        have := Quotient.exact (Quotient.out_eq (Quotient.mk (idealSetoid O)
          (scaleIdeal ((clsIdeal cl : (Ideal (𝓞 F))⁰) : Ideal (𝓞 F)) c.1.out)))
        exact this
      rw [h0] at hrel0
      have := eq_bot_of_idealRel_bot_nf hrel0
      exact leftNrdIdeal_scaleIdeal_ne_bot hO.1 (clsIdeal_ne_bot' cl) (hJc c) (by
        rw [this]; simp only [leftNrdIdeal]
        refine Ideal.span_eq_bot.2 fun r ⟨x, hx, hr⟩ => ?_
        have h0 : nrd (x : QuatF F a b) = 0 := by rw [show x = 0 from hx]; simp [nrd]
        rw [h0] at hr
        exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).1 hr)
    · obtain ⟨cl, hcl⟩ := x.2
      dsimp only at hcl
      symm
      exact (hrel c _).2 ⟨cl, hcl⟩
  have hfin : ∀ c : C, (centralUnitsIn (R := 𝓞 F) c.1.out).FiniteIndex := fun c =>
    finiteIndex_centralUnitsIn (O := O) hdef hO.1 hstd c.2
  -- each term
  have hterm : ∀ c : C, (((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℕ) : ℝ)⁻¹ =
      (NumberField.classNumber F : ℝ) / ((fib (Ψ c) : ℝ) * (S (Ψ c) : ℝ)) := by
    intro c
    have hw : ((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℝ) ≠ 0 := by exact_mod_cast (hfin c).index_ne_zero
    have hh : (NumberField.classNumber F : ℝ) ≠ 0 := by exact_mod_cast NumberField.classNumber_ne_zero F
    have key : (fib (Ψ c) : ℝ) * (S (Ψ c) : ℝ) =
        ((centralUnitsIn (R := 𝓞 F) c.1.out).index : ℝ) * (NumberField.classNumber F : ℝ) := by
      rw [hfib, hS, ← card_orbit_mul_card_stab_cls c.1]
      push_cast; ring
    rw [key]; field_simp
  rw [tsum_fintype (L := .unconditional _)]
  simp_rw [hterm]
  rw [← Finset.sum_fiberwise Finset.univ Ψ]
  have hω : ∀ ω : Y, ∑ c ∈ Finset.univ.filter (fun c => Ψ c = ω),
      (NumberField.classNumber F : ℝ) / ((fib (Ψ c) : ℝ) * (S (Ψ c) : ℝ)) =
        (NumberField.classNumber F : ℝ) * ((S ω : ℝ))⁻¹ := by
    intro ω
    obtain ⟨c₀, hc₀⟩ := hsurj ω
    have hf0 : (fib ω : ℝ) ≠ 0 := by
      have : 0 < fib ω := Nat.card_pos_iff.2 ⟨⟨⟨c₀, hc₀⟩⟩, inferInstance⟩
      exact_mod_cast this.ne'
    rw [Finset.sum_congr rfl fun c hc => by rw [(Finset.mem_filter.1 hc).2], Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun c => Ψ c = ω)).card : ℝ) = fib ω := by
      simp only [fib]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcard]
    field_simp
  rw [Finset.sum_congr rfl fun ω _ => hω ω, ← Finset.mul_sum]
  congr 1
  unfold dcMass orbitMass
  rw [finsum_eq_sum_of_fintype]

end Mass

end QuadFormsKB.QuatOrder
