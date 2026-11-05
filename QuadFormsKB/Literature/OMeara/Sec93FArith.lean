/-
# O'Meara 93:28: the arithmetic of the ideals $\mathfrak f_i$

**Setting** (as in `Sec93FIdeal.lean`): $R$ a Henselian discrete valuation ring with fraction field $F$, $2 \ne 0$ in
$R$, $\pi$ a prime element, `dord hπ` the order function, `quadDefect R` the quadratic defect $\mathfrak d$ (§63A).

**Proves** (the "direct calculation using the definition of $\mathfrak f_1$" in the proof of 93:28, p. 269)
* `sqEquivMod_one_add`: $1 + \gamma \cong 1 \bmod \mathfrak a$ when $\gamma \in \mathfrak p$, $\mathfrak d(\gamma)
  \subseteq \mathfrak a$, and $2\eta \in \mathfrak a$ for every $\eta$ with $\eta^2$ of order at least that of $\gamma$
  (if $\gamma \notin \mathfrak a$);
* `sqEquivMod_one_add_mul`: for $\mathfrak s = \mathfrak o$, $\alpha \in \mathfrak g$, $\beta \in \mathfrak g'$ with
  $\mathfrak g \subseteq a\mathfrak o$, $\mathfrak g' \subseteq a'\mathfrak o$ and $\operatorname{ord} a \ge 0$,
  $\operatorname{ord} a' \ge 1$: $1 + \alpha\beta \cong 1 \bmod \mathfrak f$, $\mathfrak f$ the ideal `fIdealOf` of
  O'Meara p. 264.
-/
import QuadFormsKB.Literature.OMeara.Sec93EFund
import QuadFormsKB.Literature.OMeara.Sec93Rel

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Arith28

open FIdealAux

section Arith

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- **$1 + \gamma \cong 1 \bmod \mathfrak a$** (O'Meara 1963, the computation behind p. 269): let $\gamma \in
\mathfrak p$ with $\mathfrak d(\gamma) \subseteq \mathfrak a$. If $\gamma \in \mathfrak a$ take $\varepsilon = 1$;
otherwise $\gamma = \eta^2 + w$ with $w\mathfrak o = \mathfrak d(\gamma) \subseteq \mathfrak a$ (63A), and then
$\operatorname{ord}\eta^2 \ge \operatorname{ord}\gamma$, so $1 + \gamma = (1 + \eta)^2 - 2\eta + w$; the hypothesis
`h2η` puts $2\eta$ into $\mathfrak a$. -/
theorem sqEquivMod_one_add (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {γ : F} (hγ : γ = 0 ∨ 1 ≤ dord hπ γ)
    {X : Submodule R F} (hdef : quadDefect R γ ≤ X)
    (h2η : γ ∉ X → ∀ η : F, η ≠ 0 → γ ≠ 0 → dord hπ γ ≤ 2 * dord hπ η → 2 * η ∈ X) :
    SqEquivMod X (1 + γ) 1 := by
  -- `γ` lies in `𝔭`
  obtain ⟨c, hcm, hc⟩ : ∃ c ∈ maximalIdeal R, algebraMap R F c = γ := by
    rcases hγ with h | h
    · exact ⟨0, zero_mem _, by rw [h, map_zero]⟩
    · by_cases h0 : γ = 0
      · exact ⟨0, zero_mem _, by rw [h0, map_zero]⟩
      · exact exists_max_of_pos hπ h0 h
  have hunit : IsUnit (1 + c) := by
    by_contra hnu
    have h1 : (1 + c) - c ∈ maximalIdeal R := sub_mem hnu hcm
    rw [add_sub_cancel_right] at h1
    exact h1 isUnit_one
  refine ⟨⟨1 + c, hunit, by rw [map_add, map_one, hc, mul_one]⟩, ?_⟩
  by_cases hγX : γ ∈ X
  · exact ⟨1, isUnit_one, by rw [map_one, one_pow, mul_one, add_sub_cancel_left]; exact hγX⟩
  have hγ0 : γ ≠ 0 := fun h => hγX (h ▸ zero_mem X)
  obtain ⟨η, hη⟩ := exists_quadDefect_eq h2 γ
  have hw : γ - η ^ 2 ∈ X := hdef (hη ▸ mem_span_singleton_self _)
  have hη0 : η ≠ 0 := by
    rintro rfl
    apply hγX; simpa using hw
  -- `ord η² ≥ ord γ`
  have hord : dord hπ γ ≤ 2 * dord hπ η := by
    by_contra hlt
    push Not at hlt
    have hη2 : η ^ 2 ≠ 0 := pow_ne_zero 2 hη0
    have hd2 : dord hπ (η ^ 2) = 2 * dord hπ η := dord_sq hπ hη0
    have hsum : -(η ^ 2) + γ ≠ 0 := by
      intro h
      have : γ = η ^ 2 := by linear_combination h
      rw [this, hd2] at hlt; omega
    have hdw : dord hπ (-(η ^ 2) + γ) = dord hπ (-(η ^ 2)) :=
      dord_add_of_lt hπ (neg_ne_zero.2 hη2) hγ0 hsum (by rw [dord_neg hπ hη2, hd2]; exact hlt)
    have hmem : γ ∈ span R {-(η ^ 2) + γ} := by
      rw [mem_span_iff hπ hγ0 hsum, hdw, dord_neg hπ hη2, hd2]; exact hlt.le
    have hX : span R {-(η ^ 2) + γ} ≤ X := by
      rw [span_singleton_le_iff_mem]; convert hw using 1; ring
    exact hγX (hX hmem)
  -- `η ∈ 𝔭`
  have hη1 : 1 ≤ dord hπ η := by
    have : 1 ≤ dord hπ γ := hγ.resolve_left hγ0
    omega
  obtain ⟨δ, -, hδ⟩ := exists_max_of_pos hπ hη0 hη1
  refine ⟨1 + δ, ?_, ?_⟩
  · have hδm : δ ∈ maximalIdeal R := by
      obtain ⟨δ', hδ'm, hδ'⟩ := exists_max_of_pos hπ hη0 hη1
      have : δ = δ' := IsFractionRing.injective R F (hδ.trans hδ'.symm)
      rw [this]; exact hδ'm
    by_contra hnu
    have h1 : (1 + δ) - δ ∈ maximalIdeal R := sub_mem hnu hδm
    rw [add_sub_cancel_right] at h1
    exact h1 isUnit_one
  · have h2η' := h2η hγX η hη0 hγ0 hord
    have : 1 + γ - 1 * algebraMap R F (1 + δ) ^ 2 = (γ - η ^ 2) - 2 * η := by
      rw [map_add, map_one, hδ]; ring
    rw [this]
    exact sub_mem hw h2η'

lemma dord_ge_of_mem (hπ : Irreducible π) {x a : F} (hx : x ≠ 0) (ha : a ≠ 0) (h : x ∈ R ∙ a) :
    dord hπ a ≤ dord hπ x :=
  (mem_span_iff hπ hx ha).1 h

/-- **$1 + \alpha\beta \cong 1 \bmod \mathfrak f$** (O'Meara 1963, p. 269, "by a direct calculation using the
definition of $\mathfrak f_1$"), for $\mathfrak s = \mathfrak o$: if $\alpha \in \mathfrak g \subseteq a\mathfrak o$,
$\beta \in \mathfrak g' \subseteq a'\mathfrak o$ with $\operatorname{ord} a \ge 0$ and $\operatorname{ord} a' \ge 1$,
then $1 + \alpha\beta \cong 1 \bmod \mathfrak f$, where $\mathfrak f = \sum \mathfrak d(\alpha\beta) +
2\mathfrak p^{\frac12(u + u')}$ ($u + u'$ even) or $\sum\mathfrak d(\alpha\beta) = aa'\mathfrak o$ ($u + u'$ odd). -/
theorem sqEquivMod_one_add_mul (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {g g' : AddSubgroup F} {a a' : F}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hag : a ∈ g) (hag' : a' ∈ g') (hg : ∀ x ∈ g, x ∈ R ∙ a)
    (hg' : ∀ x ∈ g', x ∈ R ∙ a') (hu : 0 ≤ dord hπ a) (hu' : 1 ≤ dord hπ a') {α β : F} (hα : α ∈ g) (hβ : β ∈ g') :
    SqEquivMod (fIdealOf R (R ∙ (1 : F)) g g' (R ∙ a) (R ∙ a')) (1 + α * β) 1 := by
  set X := fIdealOf R (R ∙ (1 : F)) g g' (R ∙ a) (R ∙ a') with hX
  have h1 : (R ∙ (1 : F)) * (R ∙ (1 : F)) * X = X := by
    rw [← Submodule.one_eq_span, one_mul, one_mul]
  have h2F : (2 : F) ≠ 0 := by
    rw [← map_ofNat (algebraMap R F) 2]; exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 h2
  have hdefX : ∀ α ∈ g, ∀ β ∈ g', quadDefect R (α * β) ≤ X := by
    intro α hα β hβ
    rw [← h1, mul_fIdealOf one_ne_zero]
    refine le_sup_of_le_left ?_
    exact le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le β (le_iSup_of_le hβ le_rfl)))
  have hd1 : dord hπ (1 : F) = 0 := by
    simpa using dord_unit (F := F) hπ isUnit_one
  refine sqEquivMod_one_add hπ h2 ?_ (hdefX α hα β hβ) ?_
  · by_cases h0 : α * β = 0
    · exact Or.inl h0
    · right
      have hα0 : α ≠ 0 := left_ne_zero_of_mul h0
      have hβ0 : β ≠ 0 := right_ne_zero_of_mul h0
      rw [dord_mul hπ hα0 hβ0]
      have := dord_ge_of_mem hπ hα0 ha (hg α hα)
      have := dord_ge_of_mem hπ hβ0 ha' (hg' β hβ)
      omega
  · intro hγX η hη0 hγ0 hord
    have hα0 : α ≠ 0 := left_ne_zero_of_mul hγ0
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul hγ0
    have hdγ : dord hπ (α * β) = dord hπ α + dord hπ β := dord_mul hπ hα0 hβ0
    have hdα := dord_ge_of_mem hπ hα0 ha (hg α hα)
    have hdβ := dord_ge_of_mem hπ hβ0 ha' (hg' β hβ)
    by_cases hev : Even (dord hπ a + dord hπ a')
    · -- `2η ∈ 2𝔭^{(u+u')/2} ⊆ 𝔣`
      have hXe := mul_fIdealOf_even hπ one_ne_zero ha ha' hev g g'
      rw [h1, hd1, add_zero] at hXe
      rw [hXe]
      refine le_sup_right (a := ⨆ (α : F) (_ : α ∈ g) (β : F) (_ : β ∈ g'), quadDefect R (α * β)) ?_
      obtain ⟨k, hk⟩ := hev
      have hk2 : (dord hπ a + dord hπ a') / 2 = k := by omega
      rw [hk2]
      have hpk : algebraMap R F π ^ k ≠ 0 := zpow_ne_zero _ (alg_pi_ne_zero hπ)
      rw [mem_span_iff hπ (mul_ne_zero h2F hη0) (mul_ne_zero h2F hpk), dord_mul hπ h2F hη0,
        dord_mul hπ h2F hpk, dord_zpow]
      omega
    · -- odd case: `αβ ∈ aa'𝔬 = 𝔡(aa') ⊆ 𝔣`
      exfalso
      apply hγX
      have haa : a * a' ≠ 0 := mul_ne_zero ha ha'
      obtain ⟨w, hw, hw'⟩ := dord_spec hπ haa
      have hdef : quadDefect R (a * a') = R ∙ (a * a') := by
        rw [hw']
        refine quadDefect_of_odd hπ hw ?_
        rw [dord_mul hπ ha ha']; exact Int.not_even_iff_odd.mp hev
      have hmem : α * β ∈ R ∙ (a * a') := by
        rw [mem_span_iff hπ hγ0 haa, dord_mul hπ ha ha', hdγ]; omega
      exact hdefX a hag a' hag' (hdef ▸ hmem)

end Arith

section SqMod

variable {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- $x \cong 1$ and $y \cong 1 \bmod \mathfrak a$ give $xy \cong 1 \bmod \mathfrak a$. -/
theorem sqEquivMod_mul_one {X : Submodule R F} {x y : F} (hx : SqEquivMod X x 1) (hy : SqEquivMod X y 1) :
    SqEquivMod X (x * y) 1 := by
  obtain ⟨⟨u, hu, hux⟩, ε, hε, hxε⟩ := hx
  obtain ⟨⟨v, hv, hvy⟩, δ, hδ, hyδ⟩ := hy
  rw [mul_one] at hux hvy
  subst hux hvy
  rw [one_mul] at hxε hyδ
  refine ⟨⟨u * v, hu.mul hv, by rw [map_mul, mul_one]⟩, ε * δ, hε.mul hδ, ?_⟩
  rw [one_mul]
  have : algebraMap R F u * algebraMap R F v - algebraMap R F (ε * δ) ^ 2 =
      v • (algebraMap R F u - algebraMap R F ε ^ 2) + (ε ^ 2) • (algebraMap R F v - algebraMap R F δ ^ 2) := by
    simp only [Algebra.smul_def, map_mul, map_pow]; ring
  rw [this]
  exact add_mem (smul_mem _ _ hxε) (smul_mem _ _ hyδ)

/-- $x \cong 1 \bmod \mathfrak a$ gives $x^{-1} \cong 1 \bmod \mathfrak a$. -/
theorem sqEquivMod_inv_one {X : Submodule R F} {x : F} (hx : SqEquivMod X x 1) : SqEquivMod X x⁻¹ 1 := by
  obtain ⟨⟨u, hu, hux⟩, ε, hε, hxε⟩ := hx
  rw [mul_one] at hux
  subst hux
  rw [one_mul] at hxε
  obtain ⟨u', hu'⟩ := hu.exists_left_inv
  obtain ⟨ε', hε'⟩ := hε.exists_left_inv
  have hu'F : algebraMap R F u' * algebraMap R F u = 1 := by rw [← map_mul, hu', map_one]
  have hε'F : algebraMap R F ε' * algebraMap R F ε = 1 := by rw [← map_mul, hε', map_one]
  have huinv : (algebraMap R F u)⁻¹ = algebraMap R F u' := (eq_inv_of_mul_eq_one_left hu'F).symm
  refine ⟨⟨u', IsUnit.of_mul_eq_one u hu', by rw [huinv, mul_one]⟩, ε', IsUnit.of_mul_eq_one ε hε', ?_⟩
  rw [huinv, one_mul]
  have : algebraMap R F u' - algebraMap R F ε' ^ 2 =
      (-(u' * ε' ^ 2)) • (algebraMap R F u - algebraMap R F ε ^ 2) := by
    simp only [Algebra.smul_def, map_mul, map_pow, map_neg]
    linear_combination (algebraMap R F ε' ^ 2) * hu'F -
      (algebraMap R F u' * (algebraMap R F ε' * algebraMap R F ε + 1)) * hε'F
  rw [this]; exact smul_mem _ _ hxε

/-- $r^2x \cong 1 \bmod \mathfrak a$ if $x \cong 1$ and $r$ is a unit. -/
theorem sqEquivMod_sq_mul_one {X : Submodule R F} {x : F} (hx : SqEquivMod X x 1) {r : R} (hr : IsUnit r) :
    SqEquivMod X (algebraMap R F r ^ 2 * x) 1 := by
  refine sqEquivMod_mul_one ⟨⟨r ^ 2, hr.pow 2, by rw [map_pow, mul_one]⟩, r, hr, ?_⟩ hx
  rw [one_mul, sub_self]; exact zero_mem _

end SqMod

section Arith2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] {π : R}

/-- **$(1 - c)^2 + \alpha\beta \cong 1 \bmod \mathfrak f$** for $c \in \mathfrak p$, $\alpha \in \mathfrak g$,
$\beta \in \mathfrak g'$, when $\mathfrak g$ is stable under multiplication by squares of $\mathfrak o$ (as norm groups
are): $(1-c)^2 + \alpha\beta = (1-c)^2\bigl(1 + ((1-c)^{-1})^2\alpha\cdot\beta\bigr)$ and `sqEquivMod_one_add_mul`. -/
theorem sqEquivMod_sq_add_mul (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {g g' : AddSubgroup F} {a a' : F}
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hag : a ∈ g) (hag' : a' ∈ g') (hg : ∀ x ∈ g, x ∈ R ∙ a)
    (hg' : ∀ x ∈ g', x ∈ R ∙ a') (hu : 0 ≤ dord hπ a) (hu' : 1 ≤ dord hπ a')
    (hgsq : ∀ x ∈ g, ∀ r : R, algebraMap R F r ^ 2 * x ∈ g) {c : R} (hc : c ∈ maximalIdeal R) {α β : F}
    (hα : α ∈ g) (hβ : β ∈ g') :
    SqEquivMod (fIdealOf R (R ∙ (1 : F)) g g' (R ∙ a) (R ∙ a')) ((1 - algebraMap R F c) ^ 2 + α * β) 1 := by
  have hunit : IsUnit (1 - c) := by
    by_contra hnu
    have h1 : (1 - c) + c ∈ maximalIdeal R := add_mem hnu hc
    rw [sub_add_cancel] at h1
    exact h1 isUnit_one
  obtain ⟨w, hw⟩ := hunit.exists_left_inv
  have hwF : algebraMap R F w * (1 - algebraMap R F c) = 1 := by
    rw [← map_one (algebraMap R F), ← map_sub, ← map_mul, hw, map_one]
  have hα' : algebraMap R F w ^ 2 * α ∈ g := hgsq α hα w
  have key := sqEquivMod_sq_mul_one (sqEquivMod_one_add_mul hπ h2 ha ha' hag hag' hg hg' hu hu' hα' hβ) hunit
  convert key using 1
  rw [map_sub, map_one]
  linear_combination (-(algebraMap R F w * (1 - algebraMap R F c)) - 1) * α * β * hwF

end Arith2

end QuadFormsKB.OMeara.Arith28
