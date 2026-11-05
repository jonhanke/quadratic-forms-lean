/-
# O'Meara §93A: properties of the weight $\mathfrak wL$ (p. 253) and of $Q(L)$ versus $\mathfrak gL$ (p. 252)

**Setting** (as in `Sec93Gap2.lean`): $R$ a Henselian discrete valuation ring with finite residue field
(O'Meara's $\mathfrak o$), $F$ its fraction field, $2 \in F^\times$, a quadratic space $(V, Q)$ over $F$, lattices
= `Submodule R V`; $\mathfrak gL$ = `normGroup Q L`, $\mathfrak mL$ = `normGroupIdeal Q L`, $\mathfrak wL$ = `weight Q L`,
$\mathfrak sL$ = `scale Q L`, $\mathfrak nL$ = `normIdeal Q L`; $\operatorname{ord}$ = `dord hπ`. "Dyadic" means
`¬ IsUnit (2 : R)`.

**Proves** (O'Meara 1963, §93A, pp. 252–253)
* `weight_mono`: $K \subseteq L \Rightarrow \mathfrak wK \subseteq \mathfrak wL$ (any local ring);
* `weight_eq_of_normGroup_eq`: $\mathfrak gK = \mathfrak gL$ and $\mathfrak sK = \mathfrak sL$ imply $\mathfrak wK = \mathfrak wL$;
* `weight_cases` (auxiliary): $\mathfrak mL = m\mathfrak o$ with $\operatorname{ord}\mathfrak nL + \operatorname{ord}\mathfrak mL$
  even, and either $\mathfrak wL = \pi m\mathfrak o = \mathfrak p(\mathfrak mL)$ or $\mathfrak wL = \mathfrak mL = 2(\mathfrak sL)$;
* `odd_iff_weight_eq_mul_normGroupIdeal`, `weight_eq_normGroupIdeal_of_even`: for a norm generator $a$ and a weight
  generator $b$, $\operatorname{ord} a + \operatorname{ord} b$ is odd iff $\mathfrak wL = \mathfrak p(\mathfrak mL)$, and if
  even then $\mathfrak wL = \mathfrak mL = 2(\mathfrak sL)$;
* `weight_eq_normIdeal_iff`: $\mathfrak wL = \mathfrak nL \iff 2(\mathfrak sL) = \mathfrak nL$;
* `two_smul_scale_le_weight_gen`, `weight_gen_lt_scale`, `weight_gen_le_norm_gen`, `weight_gen_eq_of_even`,
  `weight_gen_eq_norm_gen_iff`: $|2(\mathfrak sL)| \le |b| < |\mathfrak sL|$, $|b| \le |a|$, $b\mathfrak o =
  2(\mathfrak sL)$ if $\operatorname{ord} a + \operatorname{ord} b$ is even, and $b\mathfrak o = a\mathfrak o \iff
  a\mathfrak o = 2(\mathfrak sL)$;
* `not_exists_ideal_subset_image_rank_one`, `image_ne_normGroup_rank_one` (p. 252): for $L = \mathfrak o x$,
  $Q(L) = \{\varepsilon^2 Q(x)\}$ contains no non-zero fractional ideal, so $Q(L) \ne \mathfrak gL$.

No finite generation of $L$ is needed except in `weight_eq_normIdeal_iff` (to obtain a norm generator).
-/
import QuadFormsKB.Literature.OMeara.Sec93E

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Mono

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- $K \subseteq L \Rightarrow \mathfrak mK \subseteq \mathfrak mL$. -/
theorem normGroupIdeal_mono {K L : Submodule R V} (h : K ≤ L) :
    normGroupIdeal Q K ≤ normGroupIdeal Q L :=
  fun _ hz r => normGroup_mono Q h (hz r)

/-- **Monotonicity of the weight** (O'Meara 1963, §93A, p. 253): $K \subseteq L \Rightarrow \mathfrak wK \subseteq
\mathfrak wL$. -/
@[kb "omeara1963" "§93A, p. 253 (K ⊆ L ⇒ wK ⊆ wL)"]
theorem weight_mono [IsLocalRing R] {K L : Submodule R V} (h : K ≤ L) : weight Q K ≤ weight Q L := by
  unfold weight
  refine sup_le_sup (mul_le_mul' le_rfl (normGroupIdeal_mono Q h)) ?_
  rintro _ ⟨c, hc, rfl⟩
  exact Submodule.smul_mem_pointwise_smul _ (2 : F) _ (scale_mono Q h hc)

/-- **$\mathfrak gK = \mathfrak gL$ and $\mathfrak sK = \mathfrak sL$ imply $\mathfrak wK = \mathfrak wL$** (O'Meara
1963, §93A, p. 253): the weight $\mathfrak p(\mathfrak mL) + 2(\mathfrak sL)$ depends only on $\mathfrak gL$ and
$\mathfrak sL$. -/
@[kb "omeara1963" "§93A, p. 253 (gK = gL with sK = sL ⇒ wK = wL)"]
theorem weight_eq_of_normGroup_eq [IsLocalRing R] {K L : Submodule R V}
    (hg : normGroup Q K = normGroup Q L) (hs : scale Q K = scale Q L) : weight Q K = weight Q L := by
  have hm : normGroupIdeal Q K = normGroupIdeal Q L := by
    ext z
    change (∀ r : R, r • z ∈ normGroup Q K) ↔ (∀ r : R, r • z ∈ normGroup Q L)
    rw [hg]
  unfold weight
  rw [hm, hs]

end Mono

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

omit [HenselianLocalRing R] [Finite (ResidueField R)] [Invertible (2 : F)] in
/-- A non-zero submodule of $F$ inside $a\mathfrak o$ is principal. -/
theorem exists_gen_of_le {S : Submodule R F} {a : F} (h : S ≤ R ∙ a) (hS : S ≠ ⊥) :
    ∃ s : F, s ≠ 0 ∧ S = R ∙ s :=
  exists_eq_span_singleton (FG.of_le (fg_span_singleton a) h) hS

omit [HenselianLocalRing R] [Finite (ResidueField R)] [Invertible (2 : F)] in
/-- Equal principal submodules have equal orders. -/
theorem dord_eq_of_span_eq {π : R} (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : R ∙ x = R ∙ y) : dord hπ x = dord hπ y := by
  have h1 : x ∈ R ∙ y := h ▸ mem_span_singleton_self x
  have h2 : y ∈ R ∙ x := h ▸ mem_span_singleton_self y
  have := (mem_span_iff hπ hx hy).mp h1
  have := (mem_span_iff hπ hy hx).mp h2
  omega

omit [HenselianLocalRing R] [Finite (ResidueField R)] [Invertible (2 : F)] in
theorem dord_pi {π : R} (hπ : Irreducible π) : dord hπ (algebraMap R F π) = 1 := by
  rw [show algebraMap R F π = algebraMap R F π ^ (1 : ℤ) by simp, dord_zpow]

/-- $\mathfrak p \cdot m\mathfrak o = \pi m\mathfrak o$. -/
theorem map_maximalIdeal_mul_span {π : R} (hπ : Irreducible π) (m : F) :
    Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * (R ∙ m) = R ∙ (algebraMap R F π * m) := by
  have hmax : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have h1 : Submodule.map (Algebra.linearMap R F) (maximalIdeal R) = R ∙ (algebraMap R F π) := by
    rw [hmax, Ideal.span, Submodule.map_span, Set.image_singleton]; rfl
  rw [h1, Submodule.span_mul_span, Set.singleton_mul_singleton]

/-- **Structure of $\mathfrak mL$ and $\mathfrak wL$** (O'Meara 1963, §93A, p. 253): over a dyadic local field, let
$a \ne 0$ be a norm generator of $L$. Then $\mathfrak mL = m\mathfrak o$ with $m \ne 0$ and $\operatorname{ord} a +
\operatorname{ord} m$ even, and either $\mathfrak wL = \pi m\,\mathfrak o$ $(= \mathfrak p(\mathfrak mL))$, or
$\mathfrak wL = \mathfrak mL = 2(\mathfrak sL)$. -/
theorem weight_cases (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V} {a : F}
    (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) :
    ∃ m : F, m ≠ 0 ∧ normGroupIdeal Q L = R ∙ m ∧ Even (dord hπ a + dord hπ m) ∧
      (weight Q L = R ∙ (algebraMap R F π * m) ∨
        (weight Q L = normGroupIdeal Q L ∧ normGroupIdeal Q L = (2 : F) • scale Q L)) := by
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hm_le : normGroupIdeal Q L ≤ R ∙ a := ha.2 ▸ normGroupIdeal_le_normIdeal Q L
  have h2a : 2 * a ∈ (2 : F) • scale Q L :=
    Submodule.smul_mem_pointwise_smul _ (2 : F) _ (normIdeal_le_scale Q L (ha.2 ▸ mem_span_singleton_self a))
  have h2a0 : 2 * a ≠ 0 := mul_ne_zero (two_ne_zero' F) ha0
  have hs_le : (2 : F) • scale Q L ≤ normGroupIdeal Q L := two_smul_scale_le_normGroupIdeal Q L
  obtain ⟨s, hs0, hs⟩ := exists_gen_of_le (hs_le.trans hm_le)
    (fun h => h2a0 (by simpa [h] using h2a))
  obtain ⟨m, hm0, hm⟩ := exists_gen_of_le hm_le
    (fun h => hs0 (by
      have : s ∈ normGroupIdeal Q L := hs_le (hs ▸ mem_span_singleton_self s)
      simpa [h] using this))
  have hdm : dord hπ a ≤ dord hπ m :=
    (mem_span_iff hπ hm0 ha0).mp (hm_le (hm ▸ mem_span_singleton_self m))
  have hds : dord hπ m ≤ dord hπ s := by
    have : s ∈ R ∙ m := hm ▸ hs_le (hs ▸ mem_span_singleton_self s)
    exact (mem_span_iff hπ hs0 hm0).mp this
  have heven : Even (dord hπ a + dord hπ m) := by
    rcases Int.even_or_odd (dord hπ m - dord hπ a) with ⟨k, hk⟩ | ho
    · exact ⟨k + dord hπ a, by omega⟩
    · exfalso
      have hz : m ∈ normGroupIdeal Q L := hm ▸ mem_span_singleton_self m
      have h1 := div_pi_mem_normGroupIdeal Q h2p hπ ha ha0 hz hm0 ho
      have hne : m / algebraMap R F π ≠ 0 := div_ne_zero hm0 hπF
      have h2 := (mem_span_iff hπ hne hm0).mp (hm ▸ h1)
      have h3 : dord hπ m = dord hπ (m / algebraMap R F π) + 1 := by
        rw [← dord_pi (F := F) hπ, ← dord_mul hπ hne hπF, div_mul_cancel₀ _ hπF]
      omega
  refine ⟨m, hm0, hm, heven, ?_⟩
  have hw : weight Q L = R ∙ (algebraMap R F π * m) ⊔ R ∙ s := by
    change Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * normGroupIdeal Q L
      + (2 : F) • scale Q L = _
    rw [hm, hs, map_maximalIdeal_mul_span hπ]
    rfl
  have hπm : algebraMap R F π * m ≠ 0 := mul_ne_zero hπF hm0
  have hdπm : dord hπ (algebraMap R F π * m) = dord hπ m + 1 := by
    rw [dord_mul hπ hπF hm0, dord_pi hπ]; ring
  rcases eq_or_lt_of_le hds with heq | hlt
  · right
    have hms : R ∙ m = R ∙ s := span_eq_of_dord_eq hπ hm0 hs0 heq
    have h2 : normGroupIdeal Q L = (2 : F) • scale Q L := by rw [hm, hs, hms]
    refine ⟨?_, h2⟩
    refine le_antisymm (weight_bounds Q L).2.1 ?_
    rw [h2]; exact (weight_bounds Q L).2.2.1
  · left
    rw [hw]
    refine sup_eq_left.mpr ?_
    rw [span_singleton_le_iff_mem, mem_span_iff hπ hs0 hπm]
    omega

/-- A weight generator is non-zero (given a non-zero norm generator): $2a \in 2(\mathfrak sL) \subseteq \mathfrak wL$. -/
theorem weight_gen_ne_zero {L : Submodule R V} {a b : F} (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0)
    (hb : IsWeightGenerator Q L b) : b ≠ 0 := by
  intro hb0
  have h2a : 2 * a ∈ (2 : F) • scale Q L :=
    Submodule.smul_mem_pointwise_smul _ (2 : F) _ (normIdeal_le_scale Q L (ha.2 ▸ mem_span_singleton_self a))
  have h := (weight_bounds Q L).2.2.1 h2a
  rw [← hb, hb0] at h
  simp only [span_singleton_eq_bot.mpr rfl, mem_bot] at h
  exact mul_ne_zero (two_ne_zero' F) ha0 h

/-- **$\operatorname{ord}\mathfrak nL + \operatorname{ord}\mathfrak wL$ odd $\iff \mathfrak wL = \mathfrak p(\mathfrak mL)$**
(O'Meara 1963, §93A, p. 253): over a dyadic local field, for a norm generator $a$ and a weight generator $b$ of a
non-zero regular lattice $L$ ($b \ne 0$ follows), $\operatorname{ord} a + \operatorname{ord} b$ is odd if and only if
$\mathfrak wL = \mathfrak p(\mathfrak mL)$. -/
@[kb "omeara1963" "§93A, p. 253 (ord nL + ord wL odd ⇔ wL = p(mL); even ⇒ wL = mL = 2(sL))"]
theorem odd_iff_weight_eq_mul_normGroupIdeal (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) :
    Odd (dord hπ a + dord hπ b) ↔
      weight Q L = Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * normGroupIdeal Q L := by
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  obtain ⟨m, hm0, hm, hev, hcase⟩ := weight_cases Q h2p hπ ha ha0
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hπm : algebraMap R F π * m ≠ 0 := mul_ne_zero hπF hm0
  have hdπm : dord hπ (algebraMap R F π * m) = dord hπ m + 1 := by
    rw [dord_mul hπ hπF hm0, dord_pi hπ]; ring
  have hpm := map_maximalIdeal_mul_span (F := F) hπ m
  rw [← hm] at hpm
  rcases hcase with hA | ⟨hB, -⟩
  · have hdb : dord hπ b = dord hπ m + 1 := by
      rw [← hdπm]; exact dord_eq_of_span_eq hπ hb0 hπm (hb.trans hA)
    refine iff_of_true ?_ (hA.trans hpm.symm)
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  · have hdb : dord hπ b = dord hπ m := dord_eq_of_span_eq hπ hb0 hm0 (hb.trans (hB.trans hm))
    refine iff_of_false ?_ ?_
    · rintro ⟨k, hk⟩; obtain ⟨j, hj⟩ := hev; omega
    · intro h
      have h' : R ∙ b = R ∙ (algebraMap R F π * m) := by rw [hb, h, hpm]
      have := dord_eq_of_span_eq hπ hb0 hπm h'
      omega

/-- **Even case** (O'Meara 1963, §93A, p. 253): over a dyadic local field, if $a$ is a norm generator and $b$ a weight
generator of a non-zero regular lattice $L$ with $\operatorname{ord} a + \operatorname{ord} b$ even, then
$\mathfrak wL = \mathfrak mL$ and $\mathfrak mL = 2(\mathfrak sL)$. -/
@[kb "omeara1963" "§93A, p. 253 (ord nL + ord wL odd ⇔ wL = p(mL); even ⇒ wL = mL = 2(sL))"]
theorem weight_eq_normGroupIdeal_of_even (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) (hev : Even (dord hπ a + dord hπ b)) :
    weight Q L = normGroupIdeal Q L ∧ normGroupIdeal Q L = (2 : F) • scale Q L := by
  have ha0 := ha.ne_zero Q hreg hne
  have hb0 := weight_gen_ne_zero Q ha ha0 hb
  obtain ⟨m, hm0, hm, hev', hcase⟩ := weight_cases Q h2p hπ ha ha0
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hπm : algebraMap R F π * m ≠ 0 := mul_ne_zero hπF hm0
  have hdπm : dord hπ (algebraMap R F π * m) = dord hπ m + 1 := by
    rw [dord_mul hπ hπF hm0, dord_pi hπ]; ring
  rcases hcase with hA | hB
  · exfalso
    have hdb : dord hπ b = dord hπ m + 1 := by
      rw [← hdπm]; exact dord_eq_of_span_eq hπ hb0 hπm (hb.trans hA)
    obtain ⟨k, hk⟩ := hev; obtain ⟨j, hj⟩ := hev'; omega
  · exact hB

/-- $\mathfrak wL = \mathfrak nL \Rightarrow 2(\mathfrak sL) = \mathfrak nL$ for a non-zero norm generator $a$
(no finiteness needed). -/
theorem two_smul_scale_eq_of_weight_eq (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π)
    {L : Submodule R V} {a : F} (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0)
    (h : weight Q L = normIdeal Q L) : (2 : F) • scale Q L = normIdeal Q L := by
  obtain ⟨m, hm0, hm, hev, hcase⟩ := weight_cases Q h2p hπ ha ha0
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hπm : algebraMap R F π * m ≠ 0 := mul_ne_zero hπF hm0
  have hdπm : dord hπ (algebraMap R F π * m) = dord hπ m + 1 := by
    rw [dord_mul hπ hπF hm0, dord_pi hπ]; ring
  have hmn : normGroupIdeal Q L = normIdeal Q L :=
    le_antisymm (normGroupIdeal_le_normIdeal Q L) (h ▸ (weight_bounds Q L).2.1)
  rcases hcase with hA | ⟨-, hB⟩
  · exfalso
    have h1 : R ∙ (algebraMap R F π * m) = R ∙ a := hA.symm.trans (h.trans ha.2.symm)
    have h2 : R ∙ m = R ∙ a := hm.symm.trans (hmn.trans ha.2.symm)
    have := dord_eq_of_span_eq hπ hπm ha0 h1
    have := dord_eq_of_span_eq hπ hm0 ha0 h2
    omega
  · exact hB.symm.trans hmn

/-- **$\mathfrak wL = \mathfrak nL \iff 2(\mathfrak sL) = \mathfrak nL$** (O'Meara 1963, §93A, p. 253): over a dyadic
local field, for a non-zero regular finitely generated lattice $L$, the weight equals the norm
$\mathfrak nL = \mathfrak o\,a$ if and only if $2(\mathfrak sL) = \mathfrak nL$. -/
@[kb "omeara1963" "§93A, p. 253 (wL = nL ⇔ 2(sL) = nL)"]
theorem weight_eq_normIdeal_iff (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hL : L.FG)
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    weight Q L = normIdeal Q L ↔ (2 : F) • scale Q L = normIdeal Q L := by
  constructor
  · intro h
    obtain ⟨x, -, ha⟩ := exists_isNormGenerator_Q Q hL
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    exact two_smul_scale_eq_of_weight_eq Q h2p hπ ha (ha.ne_zero Q hreg hne) h
  · intro h
    exact le_antisymm (weight_bounds Q L).2.2.2 (h ▸ (weight_bounds Q L).2.2.1)

/-- $2(\mathfrak sL) \subseteq b\mathfrak o$ (O'Meara 1963, §93A, p. 253, "$|2(\mathfrak sL)| \le |b|$"). -/
@[kb "omeara1963" "§93A, p. 253 (|2(sL)| ≤ |b| < |sL|, |b| ≤ |a|, ...)"]
theorem two_smul_scale_le_weight_gen {L : Submodule R V} {b : F} (hb : IsWeightGenerator Q L b) :
    (2 : F) • scale Q L ≤ R ∙ b := by
  rw [hb]; exact (weight_bounds Q L).2.2.1

/-- $b\mathfrak o \subseteq a\mathfrak o$ (O'Meara 1963, §93A, p. 253, "$|b| \le |a|$"). -/
@[kb "omeara1963" "§93A, p. 253 (|2(sL)| ≤ |b| < |sL|, |b| ≤ |a|, ...)"]
theorem weight_gen_le_norm_gen {L : Submodule R V} {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) : R ∙ b ≤ R ∙ a := by
  rw [hb, ha.2]; exact (weight_bounds Q L).2.2.2

/-- **$|b| < |\mathfrak sL|$** (O'Meara 1963, §93A, p. 253): over a dyadic local field, the weight generator
$b$ of a non-zero regular lattice satisfies $b\mathfrak o \subsetneq \mathfrak sL$. -/
@[kb "omeara1963" "§93A, p. 253 (|2(sL)| ≤ |b| < |sL|, |b| ≤ |a|, ...)"]
theorem weight_gen_lt_scale (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) : R ∙ b < scale Q L := by
  have ha0 := ha.ne_zero Q hreg hne
  have hwn := (weight_bounds Q L).2.2.2
  refine lt_of_le_of_ne ((hb ▸ hwn).trans (normIdeal_le_scale Q L)) ?_
  intro heq
  have hw : weight Q L = normIdeal Q L :=
    le_antisymm hwn ((normIdeal_le_scale Q L).trans (by rw [← heq, hb]))
  have hs : scale Q L = normIdeal Q L := by
    apply le_antisymm _ (normIdeal_le_scale Q L)
    rw [← heq, hb]; exact hwn
  have h2 := two_smul_scale_eq_of_weight_eq Q h2p hπ ha ha0 hw
  have hamem : a ∈ (2 : F) • scale Q L := h2 ▸ ha.2 ▸ mem_span_singleton_self a
  obtain ⟨c, hc, hca⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hamem
  have hc' : c ∈ R ∙ a := ha.2 ▸ hs ▸ hc
  obtain ⟨r, hr⟩ := mem_span_singleton.mp hc'
  rw [Algebra.smul_def] at hr
  simp only [smul_eq_mul] at hca
  rw [← hr] at hca
  have h1 : algebraMap R F (2 * r) = algebraMap R F 1 := by
    rw [map_mul, map_ofNat, map_one]
    apply mul_right_cancel₀ ha0
    linear_combination hca
  have h3 : 2 * r = 1 := alg_inj h1
  exact h2p (IsUnit.of_mul_eq_one r h3)

/-- **$b\mathfrak o = 2(\mathfrak sL)$ in the even case** (O'Meara 1963, §93A, p. 253): over a dyadic local field, if
$\operatorname{ord} a + \operatorname{ord} b$ is even then $b\mathfrak o = 2(\mathfrak sL)$. -/
@[kb "omeara1963" "§93A, p. 253 (|2(sL)| ≤ |b| < |sL|, |b| ≤ |a|, ...)"]
theorem weight_gen_eq_of_even (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) (hev : Even (dord hπ a + dord hπ b)) :
    R ∙ b = (2 : F) • scale Q L := by
  obtain ⟨h1, h2⟩ := weight_eq_normGroupIdeal_of_even Q h2p hπ hreg hne ha hb hev
  rw [hb, h1, h2]

/-- **$b\mathfrak o = a\mathfrak o \iff a\mathfrak o = 2(\mathfrak sL)$** (O'Meara 1963, §93A, p. 253). -/
@[kb "omeara1963" "§93A, p. 253 (|2(sL)| ≤ |b| < |sL|, |b| ≤ |a|, ...)"]
theorem weight_gen_eq_norm_gen_iff (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a b : F} (ha : IsNormGenerator Q L a)
    (hb : IsWeightGenerator Q L b) : R ∙ b = R ∙ a ↔ R ∙ a = (2 : F) • scale Q L := by
  have ha0 := ha.ne_zero Q hreg hne
  constructor
  · intro h
    have hw : weight Q L = normIdeal Q L := hb.symm.trans (h.trans ha.2)
    rw [ha.2]
    exact (two_smul_scale_eq_of_weight_eq Q h2p hπ ha ha0 hw).symm
  · intro h
    exact le_antisymm (weight_gen_le_norm_gen Q ha hb) (h ▸ two_smul_scale_le_weight_gen Q hb)

end Main

section RankOne

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$Q(L)$ contains no non-zero fractional ideal for $L = \mathfrak o x$** (O'Meara 1963, §93A, p. 252): if
$Q(x) \ne 0$, then $Q(\mathfrak o x) = \{\varepsilon^2 Q(x) : \varepsilon \in \mathfrak o\}$ contains no
$c\mathfrak o$ with $c \ne 0$ (the orders of non-zero values all have the parity of $\operatorname{ord} Q(x)$, while
$c$ and $c\pi$ have orders of different parity). -/
@[kb "omeara1963" "§93A, p. 252 (Q(L) and gL need not be equal: L = ox)"]
theorem not_exists_ideal_subset_image_rank_one {π : R} (hπ : Irreducible π) {L : Submodule R V} {x : V}
    (hL : L = R ∙ x) (hx : Q x ≠ 0) :
    ¬ ∃ c : F, c ≠ 0 ∧ ((R ∙ c : Submodule R F) : Set F) ⊆ Q '' (L : Set V) := by
  rintro ⟨c, hc0, hsub⟩
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  -- every non-zero value has order congruent to `ord Q x` mod 2
  have key : ∀ z : F, z ≠ 0 → z ∈ Q '' (L : Set V) → ∃ k : ℤ, dord hπ z = dord hπ (Q x) + 2 * k := by
    rintro z hz0 ⟨y, hy, rfl⟩
    rw [hL] at hy
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hy
    have hQ : Q (r • x) = algebraMap R F r ^ 2 * Q x := by
      rw [← algebraMap_smul F r x, QuadraticMap.map_smul]; simp only [smul_eq_mul]; ring
    rw [hQ] at hz0 ⊢
    have hr : algebraMap R F r ≠ 0 := fun h => hz0 (by rw [h]; simp)
    exact ⟨dord hπ (algebraMap R F r), by
      rw [dord_mul hπ (pow_ne_zero 2 hr) hx, dord_sq hπ hr]; ring⟩
  have hcmem : c ∈ Q '' (L : Set V) := hsub (mem_span_singleton_self c)
  have hcπ : algebraMap R F π * c ∈ Q '' (L : Set V) :=
    hsub (by rw [← Algebra.smul_def]; exact smul_mem _ _ (mem_span_singleton_self c))
  obtain ⟨k₁, h₁⟩ := key c hc0 hcmem
  obtain ⟨k₂, h₂⟩ := key _ (mul_ne_zero hπF hc0) hcπ
  rw [dord_mul hπ hπF hc0, dord_pi hπ] at h₂
  omega

/-- **$Q(L) \ne \mathfrak gL$ for $L = \mathfrak o x$** (O'Meara 1963, §93A, p. 252): if $Q(x) \ne 0$, the value set
$Q(\mathfrak o x)$ is not the norm group $\mathfrak g(\mathfrak o x)$, since the latter contains the non-zero ideal
$2(\mathfrak sL) \ni 2Q(x)$. -/
@[kb "omeara1963" "§93A, p. 252 (Q(L) and gL need not be equal: L = ox)"]
theorem image_ne_normGroup_rank_one {π : R} (hπ : Irreducible π) {L : Submodule R V} {x : V}
    (hL : L = R ∙ x) (hx : Q x ≠ 0) : (Q '' (L : Set V)) ≠ (normGroup Q L : Set F) := by
  intro heq
  refine not_exists_ideal_subset_image_rank_one Q hπ hL hx ⟨2 * Q x, mul_ne_zero (two_ne_zero' F) hx, ?_⟩
  rw [heq]
  intro z hz
  obtain ⟨r, rfl⟩ := mem_span_singleton.mp hz
  have hxL : x ∈ L := hL ▸ mem_span_singleton_self x
  have hQs : Q x ∈ scale Q L := by rw [← bil_self]; exact bil_mem_scale Q hxL hxL
  refine ⟨0, L.zero_mem, r • Q x, smul_mem _ r hQs, ?_⟩
  simp only [Algebra.smul_def, map_zero]
  ring

end RankOne

end QuadFormsKB.OMeara
