/-
# O'Meara §93A: $\mathfrak gL = a\mathfrak o^2 + b\mathfrak o$ over a dyadic local field (93:4, 93:6)

**Setting** (as in `Sec93.lean` and `Sec63B.lean`): $R$ a Henselian discrete valuation ring with finite residue field
(O'Meara's $\mathfrak o$; only the Henselian property of the complete ring is used), $F$ its fraction field,
$2 \in F^\times$, and $F$ *dyadic*: $2$ is not a unit of $R$. A quadratic space $(V, Q)$ over $F$, O'Meara's
$B$ = `bil Q`, lattices = `Submodule R V`; $\mathfrak gL$ = `normGroup Q L`, $\mathfrak mL$ = `normGroupIdeal Q L`,
$\mathfrak wL$ = `weight Q L` (all from `Sec93.lean`); $\operatorname{ord}$ is the order function `dord hπ` of a prime
element $\pi$ (`Sec63A.lean`).

**Proves** (O'Meara 1963, §93A, pp. 253–254)
* `mem_normGroup_of_odd` (p. 254): if $a$ is a norm generator and $\beta \in \mathfrak gL$ with
  $\operatorname{ord} a + \operatorname{ord}\beta$ odd, then $\beta\mathfrak o \subseteq \mathfrak gL$;
* `mem_weight_of_odd` (p. 254, "every element of $\mathfrak gL$ whose order has opposite parity to the order of
  $\mathfrak nL$ is in $\mathfrak wL$"), together with the parity statement of p. 253 in the form used there
  (`div_pi_mem_normGroupIdeal`: an element of $\mathfrak mL$ of order of parity opposite to $\operatorname{ord}
  \mathfrak nL$ lies in $\mathfrak p\,\mathfrak mL$, which is equivalent to $\operatorname{ord}\mathfrak nL +
  \operatorname{ord}\mathfrak mL$ even);
* `normGroup_eq_sq_add` (**93:4**): $\mathfrak gL = a\mathfrak o^2 + b\mathfrak o$ for a norm generator $a$ and a
  weight generator $b$ of a non-zero regular lattice $L$;
* `weight_eq_sup`, `weight_eq_of_largest_odd_value` (**93:5**, weight generators): $\mathfrak wL = b_0\mathfrak o +
  2(\mathfrak sL)$ for a value $b_0 = Q(x_0)$ of largest absolute value among the values of order of parity opposite to
  $\operatorname{ord} a$, and $\mathfrak wL = 2(\mathfrak sL)$ if there is none;
* `sqEquivMod_of_isNormGenerator` and `isNormGenerator_iff_sqEquivMod` (**93:6**): $a'$ is a norm generator if and only
  if $a \cong a' \bmod \mathfrak wL$.

**Proof notes.** O'Meara uses Proposition 63:11 (a binary space of prime discriminant represents $\gamma$ or
$\gamma\Delta$) for the space $\langle a, \beta\rangle$; here it enters through the library lemma `B63.NF_or` (every
$c \ne 0$ has $c$ or $c\Delta$ of the form $s^2 + p\,t^2$, $p$ prime), with the unit $\Delta$ of quadratic defect
$4\mathfrak o$ normalized to $\Delta = 1 + 4\rho$. The principle of domination is `dord_add_of_lt`. The parity statement
uses that every residue is a square (`exists_sq_mod`, the residue field is perfect of characteristic $2$).
-/
import QuadFormsKB.Literature.OMeara.Sec93Gap
import QuadFormsKB.Literature.OMeara.Sec63B

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace G93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- A unit of quadratic defect $4\mathfrak o$ of the form $1 + 4\rho$. -/
lemma exists_delta [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) :
    ∃ ρ : R, IsUnit (1 + 4 * ρ) ∧ quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)} := by
  obtain ⟨-, ⟨u, hu, hud⟩, -⟩ := exists_quadDefect_dyadic (F := F) h2 h2p hπ
  obtain ⟨η, hη⟩ := exists_quadDefect_eq (R := R) h2 (algebraMap R F u)
  rw [hud] at hη
  have h4 : algebraMap R F u - η ^ 2 ∈ span R {(4 : F)} := hη ▸ mem_span_singleton_self _
  obtain ⟨c, hc⟩ := mem_span_singleton.mp h4
  have hη2 : η ^ 2 = algebraMap R F (u - c * 4) := by
    rw [map_sub, map_mul, ← four_F_eq, ← Algebra.smul_def, hc]; ring
  obtain ⟨δ, rfl⟩ := exists_alg_of_sq hη2
  have hδu : IsUnit δ := by
    have h' : δ ^ 2 = u - c * 4 := alg_inj (R := R) (F := F) (by rw [map_pow, hη2])
    have h4m : c * 4 ∈ maximalIdeal R := by
      refine Ideal.mul_mem_left _ _ ?_
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr h2p)
    have : IsUnit (δ ^ 2) := by
      rw [h']
      by_contra hn
      exact ((mem_maximalIdeal _).mp (by simpa using add_mem ((mem_maximalIdeal _).mpr hn) h4m)) hu
    exact isUnit_of_mul_isUnit_left (by rwa [pow_two] at this)
  obtain ⟨δ', hδ'⟩ := hδu.exists_left_inv
  refine ⟨c * δ' ^ 2, ?_, ?_⟩
  · have : 1 + 4 * (c * δ' ^ 2) = δ' ^ 2 * u := by
      have h' : δ ^ 2 = u - c * 4 := alg_inj (R := R) (F := F) (by rw [map_pow, hη2])
      calc 1 + 4 * (c * δ' ^ 2) = (δ' * δ) ^ 2 + 4 * (c * δ' ^ 2) := by rw [hδ']; ring
        _ = δ' ^ 2 * (δ ^ 2 + c * 4) := by ring
        _ = δ' ^ 2 * u := by rw [h']; ring
    rw [this]
    exact ((isUnit_iff_exists_inv.2 ⟨δ, hδ'⟩ : IsUnit δ').pow 2).mul hu
  · have h' : δ ^ 2 = u - c * 4 := alg_inj (R := R) (F := F) (by rw [map_pow, hη2])
    have : algebraMap R F (1 + 4 * (c * δ' ^ 2)) = algebraMap R F δ' ^ 2 * algebraMap R F u := by
      rw [← map_pow, ← map_mul]; congr 1
      calc 1 + 4 * (c * δ' ^ 2) = (δ' * δ) ^ 2 + 4 * (c * δ' ^ 2) := by rw [hδ']; ring
        _ = δ' ^ 2 * (δ ^ 2 + c * 4) := by ring
        _ = δ' ^ 2 * u := by rw [h']; ring
    rw [this, quadDefect_sq_mul, hud, span_mul_span, Set.singleton_mul_singleton, ← map_pow]
    have hu' : IsUnit (δ' ^ 2) := (isUnit_iff_exists_inv.2 ⟨δ, hδ'⟩ : IsUnit δ').pow 2
    rw [← Algebra.smul_def]
    exact span_singleton_smul_eq hu' _

/-- **Decomposition** (O'Meara's use of 63:11 on p. 254): for $a, \beta \ne 0$ with $\operatorname{ord}\beta -
\operatorname{ord} a$ odd and $y \ne 0$, there are $\rho_0 \in R$ and $s, t \in F$ with
$y(1 + 4\rho_0) = as^2 + \beta t^2$. -/
lemma decomp [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0) {ρ : R}
    (hΔ : IsUnit (1 + 4 * ρ)) (hΔd : quadDefect R (algebraMap R F (1 + 4 * ρ)) = span R {(4 : F)})
    {π : R} (hπ : Irreducible π) {a β y : F} (ha : a ≠ 0) (hβ : β ≠ 0) (hy : y ≠ 0)
    (hodd : Odd (dord hπ β - dord hπ a)) :
    ∃ ρ₀ : R, ∃ s t : F, y * (1 + 4 * algebraMap R F ρ₀) = a * s ^ 2 + β * t ^ 2 := by
  have hq : β / a ≠ 0 := div_ne_zero hβ ha
  obtain ⟨u, hu, hqu⟩ := dord_spec hπ hq
  have hd : dord hπ (β / a) = dord hπ β - dord hπ a := by
    have := dord_mul hπ ha hq
    rw [mul_div_cancel₀ _ ha] at this; omega
  obtain ⟨k, hk⟩ := hodd
  rw [hd, hk] at hqu
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hπ' : Irreducible (u * π) := (irreducible_isUnit_mul hu).mpr hπ
  have hβa : β = a * (algebraMap R F (u * π) * (algebraMap R F π ^ k) ^ 2) := by
    have : β = a * (β / a) := by field_simp
    have hsq : (algebraMap R F π ^ k) ^ 2 = algebraMap R F π ^ (2 * k) := by
      rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
    rw [this, hqu, map_mul, zpow_add₀ hπF, zpow_one, hsq]; ring
  have hpk : algebraMap R F π ^ k ≠ 0 := zpow_ne_zero _ hπF
  have hΔF : algebraMap R F (1 + 4 * ρ) = 1 + 4 * algebraMap R F ρ := by
    rw [map_add, map_mul, map_one, ← four_F_eq]
  rcases B63.NF_or h2 hπ' hΔ hΔd (div_ne_zero hy ha) with ⟨s, t, hst⟩ | ⟨s, t, hst⟩
  · refine ⟨0, s, t / algebraMap R F π ^ k, ?_⟩
    rw [hβa, map_zero, mul_zero, add_zero, mul_one]
    field_simp at hst ⊢
    rw [← hst]
  · refine ⟨ρ, s, t / algebraMap R F π ^ k, ?_⟩
    rw [hβa, ← hΔF]
    have e : a * (algebraMap R F (u * π) * (algebraMap R F π ^ k) ^ 2) * (t / algebraMap R F π ^ k) ^ 2
        = a * algebraMap R F (u * π) * t ^ 2 := by field_simp
    rw [e]
    have hst' : a * (s ^ 2 + algebraMap R F (u * π) * t ^ 2) = y * algebraMap R F (1 + 4 * ρ) := by
      rw [hst]; field_simp
    linear_combination (-1) * hst'

/-- **Principle of domination** for $as^2 + \beta t^2$ with $\operatorname{ord} a$, $\operatorname{ord}\beta$ of
opposite parity: both terms lie in $y\mathfrak o$ when $y(1 + 4\rho_0) = as^2 + \beta t^2$, $1 + 4\rho_0$ a unit. -/
lemma dom {π : R} (hπ : Irreducible π) {a β y s t X : F} (ha : a ≠ 0) (hβ : β ≠ 0) (hy : y ≠ 0)
    {x : R} (hx : IsUnit x) (hX : X = algebraMap R F x)
    (hodd : Odd (dord hπ β - dord hπ a)) (h : y * X = a * s ^ 2 + β * t ^ 2) :
    a * s ^ 2 ∈ span R {y} ∧ β * t ^ 2 ∈ span R {y} := by
  have hXmem : y * X ∈ span R {y} := by
    rw [hX, mul_comm, ← Algebra.smul_def]; exact smul_mem _ _ (mem_span_singleton_self y)
  have hX0 : X ≠ 0 := by rw [hX]; exact alg_ne_zero_of_unit hx
  have hyX : y * X ≠ 0 := mul_ne_zero hy hX0
  have hdyX : dord hπ (y * X) = dord hπ y := by rw [dord_mul hπ hy hX0, hX, dord_unit hπ hx, add_zero]
  by_cases hs : s = 0
  · subst hs
    refine ⟨by simp, ?_⟩
    rw [h] at hXmem; simpa using hXmem
  by_cases ht : t = 0
  · subst ht
    refine ⟨?_, by simp⟩
    rw [h] at hXmem; simpa using hXmem
  have h1 : a * s ^ 2 ≠ 0 := mul_ne_zero ha (pow_ne_zero 2 hs)
  have h2' : β * t ^ 2 ≠ 0 := mul_ne_zero hβ (pow_ne_zero 2 ht)
  have hd1 : dord hπ (a * s ^ 2) = dord hπ a + 2 * dord hπ s := by
    rw [dord_mul hπ ha (pow_ne_zero 2 hs), dord_sq hπ hs]
  have hd2 : dord hπ (β * t ^ 2) = dord hπ β + 2 * dord hπ t := by
    rw [dord_mul hπ hβ (pow_ne_zero 2 ht), dord_sq hπ ht]
  have hne : dord hπ (a * s ^ 2) ≠ dord hπ (β * t ^ 2) := by
    rw [hd1, hd2]; obtain ⟨k, hk⟩ := hodd; omega
  have hsum : a * s ^ 2 + β * t ^ 2 ≠ 0 := h ▸ hyX
  rw [mem_span_iff hπ h1 hy, mem_span_iff hπ h2' hy]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := dord_add_of_lt hπ h1 h2' hsum hlt
    rw [← h, hdyX] at this; omega
  · have := dord_add_of_lt hπ h2' h1 (by rwa [add_comm]) hlt
    rw [add_comm, ← h, hdyX] at this; omega

end G93

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

include F in
omit [HenselianLocalRing R] [Finite (ResidueField R)] in
lemma two_ne_zero_R : (2 : R) ≠ 0 := by
  intro h
  have : (2 : F) = 0 := by rw [← map_ofNat (algebraMap R F) 2, h, map_zero]
  exact two_ne_zero' F this

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- $4\mathfrak nL \subseteq \mathfrak gL$: $4ry = 2(2ry)$ with $2ry \in \mathfrak nL \subseteq \mathfrak sL$. -/
lemma four_mul_mem_normGroup {L : Submodule R V} {y : F} (hy : y ∈ normIdeal Q L) (r : R) :
    4 * (algebraMap R F r * y) ∈ normGroup Q L := by
  have : 2 * (algebraMap R F (2 * r) * y) ∈ normGroup Q L := by
    refine two_mul_mem_normGroup Q (normIdeal_le_scale Q L ?_)
    rw [← Algebra.smul_def]; exact smul_mem _ _ hy
  convert this using 1; rw [map_mul, map_ofNat]; ring

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
lemma four_mul_mem_two_smul_scale {L : Submodule R V} {y : F} (hy : y ∈ normIdeal Q L) (r : R) :
    4 * (algebraMap R F r * y) ∈ (2 : F) • scale Q L := by
  have h1 : algebraMap R F (2 * r) * y ∈ scale Q L := by
    refine normIdeal_le_scale Q L ?_
    rw [← Algebra.smul_def]; exact smul_mem _ _ hy
  have := Submodule.smul_mem_pointwise_smul _ (2 : F) _ h1
  convert this using 1; rw [smul_eq_mul, map_mul, map_ofNat]; ring

/-- **$\beta\mathfrak o \subseteq \mathfrak gL$ for $\beta$ of the opposite parity** (O'Meara 1963, §93A, p. 254): over a
dyadic local field, if $a$ is a norm generator of $L$ with $a \ne 0$, and $\beta \in \mathfrak gL$ has
$\operatorname{ord} a + \operatorname{ord}\beta$ odd, then $\beta\mathfrak o \subseteq \mathfrak gL$. -/
@[kb "omeara1963" "§93A, p. 254 (β ∈ gL of opposite parity ⇒ βo ⊆ gL)"]
theorem mem_normGroup_of_odd (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V} {a β : F}
    (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) (hβ : β ∈ normGroup Q L) (hβ0 : β ≠ 0)
    (hodd : Odd (dord hπ β - dord hπ a)) {y : F} (hy : y ∈ R ∙ β) : y ∈ normGroup Q L := by
  have h2 : (2 : R) ≠ 0 := two_ne_zero_R (F := F)
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem _
  obtain ⟨ρ, hΔ, hΔd⟩ := G93.exists_delta (F := F) h2 h2p hπ
  obtain ⟨ρ₀, s, t, hst⟩ := G93.decomp h2 hΔ hΔd hπ ha0 hβ0 hy0 hodd
  have hnL : ∀ z ∈ normGroup Q L, z ∈ R ∙ a := fun z hz => ha.2 ▸ normGroup_subset_normIdeal Q L hz
  have hβa := hnL β hβ
  have hya : y ∈ R ∙ a := (span_singleton_le_iff_mem _ _).mpr hβa hy
  have hX : IsUnit (1 + 4 * ρ₀) := by
    by_contra hn
    have h4m : 4 * ρ₀ ∈ maximalIdeal R := by
      refine Ideal.mul_mem_right _ _ ?_
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr h2p)
    have h1m : (1 : R) ∈ maximalIdeal R := by
      simpa using sub_mem ((mem_maximalIdeal _).mpr hn) h4m
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  obtain ⟨h1, h2'⟩ := G93.dom hπ ha0 hβ0 hy0 hX (X := 1 + 4 * algebraMap R F ρ₀) (by rw [map_add, map_mul, map_one, ← four_F_eq]) hodd hst
  have hyspan : span R {y} ≤ span R {β} := (span_singleton_le_iff_mem _ _).mpr hy
  have hyspan' : span R {y} ≤ span R {a} := (span_singleton_le_iff_mem _ _).mpr hya
  -- `s, t ∈ R`
  have hs : ∃ s' : R, algebraMap R F s' = s := by
    by_cases hs0 : s = 0
    · exact ⟨0, by simp [hs0]⟩
    have := hyspan' h1
    obtain ⟨c, hc⟩ := mem_span_singleton.mp this
    have : s ^ 2 = algebraMap R F c := by
      rw [Algebra.smul_def] at hc; field_simp at hc ⊢; linear_combination -hc
    exact exists_alg_of_sq this
  have ht : ∃ t' : R, algebraMap R F t' = t := by
    have := hyspan h2'
    obtain ⟨c, hc⟩ := mem_span_singleton.mp this
    have : t ^ 2 = algebraMap R F c := by
      rw [Algebra.smul_def] at hc; field_simp at hc ⊢; linear_combination -hc
    exact exists_alg_of_sq this
  obtain ⟨s', rfl⟩ := hs
  obtain ⟨t', rfl⟩ := ht
  have hm1 : a * algebraMap R F s' ^ 2 ∈ normGroup Q L := by
    rw [mul_comm]; exact mul_sq_mem_normGroup Q ha.1 ⟨s', rfl⟩
  have hm2 : β * algebraMap R F t' ^ 2 ∈ normGroup Q L := by
    rw [mul_comm]; exact mul_sq_mem_normGroup Q hβ ⟨t', rfl⟩
  have hm3 : 4 * (algebraMap R F ρ₀ * y) ∈ normGroup Q L :=
    four_mul_mem_normGroup Q (ha.2 ▸ hya) ρ₀
  have : y = (a * algebraMap R F s' ^ 2 + β * algebraMap R F t' ^ 2) - 4 * (algebraMap R F ρ₀ * y) := by
    rw [← hst]; ring
  rw [this]
  exact sub_mem (add_mem hm1 hm2) hm3

/-- **Parity of $\mathfrak mL$** (O'Meara 1963, §93A, p. 253, "$\operatorname{ord}_\mathfrak p\,\mathfrak nL +
\operatorname{ord}_\mathfrak p\,\mathfrak mL$ is even", in the form used on p. 254): over a dyadic local field, if $a$
is a norm generator of $L$ and $z \in \mathfrak mL$, $z \ne 0$, has $\operatorname{ord} z - \operatorname{ord} a$
odd, then $z/\pi \in \mathfrak mL$; so $z \in \mathfrak p\,\mathfrak mL$, i.e. $z$ does not generate $\mathfrak mL$. -/
@[kb "omeara1963" "§93A, p. 253 (ord nL + ord mL is even)"]
theorem div_pi_mem_normGroupIdeal (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    {a z : F} (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) (hz : z ∈ normGroupIdeal Q L) (hz0 : z ≠ 0)
    (hodd : Odd (dord hπ z - dord hπ a)) : z / algebraMap R F π ∈ normGroupIdeal Q L := by
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  intro r
  by_cases hr : IsUnit r
  · -- `r` a unit: `r z / π` has the parity of `a`, and is a square times `a` modulo `𝔪L`
    have hza : z ∈ R ∙ a := ha.2 ▸ normGroup_subset_normIdeal Q L (normGroupIdeal_subset Q L hz)
    have hge : dord hπ a ≤ dord hπ z := (mem_span_iff hπ hz0 ha0).mp hza
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k := ⟨k.toNat, by omega⟩
    have hza' : z / a ≠ 0 := div_ne_zero hz0 ha0
    obtain ⟨v, hv, hzv⟩ := dord_spec hπ hza'
    have hd : dord hπ (z / a) = dord hπ z - dord hπ a := by
      have := dord_mul hπ ha0 hza'
      rw [mul_div_cancel₀ _ ha0] at this; omega
    rw [hd, hk, ← hn] at hzv
    have hzeq : z = a * algebraMap R F v * algebraMap R F π ^ (2 * n + 1) := by
      have : z = a * (z / a) := by field_simp
      rw [this, hzv, ← zpow_natCast]; push_cast; ring
    obtain ⟨δ, hδ⟩ := exists_sq_mod h2p (r * v)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hδ
    obtain ⟨e, he⟩ := hδ
    obtain ⟨r', hr'⟩ := hr.exists_left_inv
    obtain ⟨v', hv'⟩ := hv.exists_left_inv
    have hsq : a * algebraMap R F (δ * π ^ n) ^ 2 ∈ normGroup Q L := by
      rw [mul_comm]; exact mul_sq_mem_normGroup Q ha.1 ⟨_, rfl⟩
    have hrest : (e * v') • z ∈ normGroup Q L := hz _
    have hkey : r • (z / algebraMap R F π) = a * algebraMap R F (δ * π ^ n) ^ 2 + (e * v') • z := by
      have hvF : algebraMap R F r * algebraMap R F v
          = algebraMap R F δ ^ 2 + algebraMap R F π * algebraMap R F e := by
        have := congrArg (algebraMap R F) he
        simp only [map_sub, map_mul, map_pow] at this
        linear_combination this
      have hv'F : algebraMap R F v' * algebraMap R F v = 1 := by rw [← map_mul, hv', map_one]
      have hzP : z / algebraMap R F π = a * algebraMap R F v * algebraMap R F π ^ (2 * n) := by
        rw [hzeq, pow_succ]; field_simp
      rw [hzP]
      simp only [Algebra.smul_def, map_mul, map_pow]
      rw [hzeq]
      linear_combination (a * algebraMap R F π ^ (2 * n)) * hvF
        - (algebraMap R F e * a * algebraMap R F π ^ (2 * n + 1)) * hv'F
    rw [hkey]; exact add_mem hsq hrest
  · -- `r ∈ 𝔭`: `r = π r'` and `r (z / π) = r' z`
    have hrm : r ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hr
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hrm
    obtain ⟨r', rfl⟩ := hrm
    have : (π * r') • (z / algebraMap R F π) = r' • z := by
      simp only [Algebra.smul_def, map_mul]; field_simp
    rw [this]; exact hz r'

/-- **Elements of $\mathfrak gL$ of the opposite parity lie in $\mathfrak wL$** (O'Meara 1963, §93A, p. 254): over a
dyadic local field, if $a \ne 0$ is a norm generator of $L$ and $\beta \in \mathfrak gL$ has
$\operatorname{ord} a + \operatorname{ord}\beta$ odd, then $\beta \in \mathfrak wL$. -/
@[kb "omeara1963" "§93A, p. 254 (elements of gL of opposite parity to nL lie in wL)"]
theorem mem_weight_of_odd (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V} {a β : F}
    (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) (hβ : β ∈ normGroup Q L) (hβ0 : β ≠ 0)
    (hodd : Odd (dord hπ β - dord hπ a)) : β ∈ weight Q L := by
  have hm : β ∈ normGroupIdeal Q L := fun r =>
    mem_normGroup_of_odd Q h2p hπ ha ha0 hβ hβ0 hodd (smul_mem _ r (mem_span_singleton_self β))
  have hm' := div_pi_mem_normGroupIdeal Q h2p hπ ha ha0 hm hβ0 hodd
  have hπp : algebraMap R F π ∈ Submodule.map (Algebra.linearMap R F) (maximalIdeal R) :=
    ⟨π, hπ.not_isUnit, rfl⟩
  have := mul_mem_mul hπp hm'
  rw [mul_div_cancel₀ _ (alg_pi_ne_zero (R := R) (F := F) hπ)] at this
  exact le_sup_left (a := Submodule.map (Algebra.linearMap R F) (maximalIdeal R) * normGroupIdeal Q L) this

/-- The key step of 93:4: every $\alpha \in \mathfrak gL$ is $\alpha \equiv a\varepsilon^2 \bmod \mathfrak wL$ for some
$\varepsilon \in \mathfrak o$. -/
theorem exists_sub_sq_mem_weight (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} {a α : F}
    (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) (hα : α ∈ normGroup Q L) :
    ∃ ε : R, α - a * algebraMap R F ε ^ 2 ∈ weight Q L := by
  have h2 : (2 : R) ≠ 0 := two_ne_zero_R (F := F)
  by_cases hα0 : α = 0
  · exact ⟨0, by simp [hα0]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have hβ0 : a * algebraMap R F π ≠ 0 := mul_ne_zero ha0 hπF
  have hodd : Odd (dord hπ (a * algebraMap R F π) - dord hπ a) := by
    rw [dord_mul hπ ha0 hπF, show algebraMap R F π = algebraMap R F π ^ (1 : ℤ) by simp, dord_zpow]
    exact ⟨0, by ring⟩
  obtain ⟨ρ, hΔ, hΔd⟩ := G93.exists_delta (F := F) h2 h2p hπ
  obtain ⟨ρ₀, s, t, hst⟩ := G93.decomp h2 hΔ hΔd hπ ha0 hβ0 hα0 hodd
  have hX : IsUnit (1 + 4 * ρ₀) := by
    by_contra hn
    have h4m : 4 * ρ₀ ∈ maximalIdeal R := by
      refine Ideal.mul_mem_right _ _ ?_
      have : (4 : R) = 2 * 2 := by norm_num
      rw [this]; exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr h2p)
    have h1m : (1 : R) ∈ maximalIdeal R := by
      simpa using sub_mem ((mem_maximalIdeal _).mpr hn) h4m
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  obtain ⟨h1, -⟩ := G93.dom hπ ha0 hβ0 hα0 hX (X := 1 + 4 * algebraMap R F ρ₀) (by rw [map_add, map_mul, map_one, ← four_F_eq]) hodd hst
  have hαa : α ∈ R ∙ a := ha.2 ▸ normGroup_subset_normIdeal Q L hα
  have hs : ∃ s' : R, algebraMap R F s' = s := by
    have := (span_singleton_le_iff_mem _ _).mpr hαa h1
    obtain ⟨c, hc⟩ := mem_span_singleton.mp this
    have : s ^ 2 = algebraMap R F c := by
      rw [Algebra.smul_def] at hc; field_simp at hc ⊢; linear_combination -hc
    exact exists_alg_of_sq this
  obtain ⟨s', rfl⟩ := hs
  refine ⟨s', ?_⟩
  set γ := a * algebraMap R F π * t ^ 2 with hγ
  have hm1 : a * algebraMap R F s' ^ 2 ∈ normGroup Q L := by
    rw [mul_comm]; exact mul_sq_mem_normGroup Q ha.1 ⟨s', rfl⟩
  have hn4 : 4 * (algebraMap R F ρ₀ * α) ∈ normGroup Q L := four_mul_mem_normGroup Q (ha.2 ▸ hαa) ρ₀
  have hγg : γ ∈ normGroup Q L := by
    have : γ = α + 4 * (algebraMap R F ρ₀ * α) - a * algebraMap R F s' ^ 2 := by
      rw [hγ]; linear_combination -hst
    rw [this]; exact sub_mem (add_mem hα hn4) hm1
  have hγw : γ ∈ weight Q L := by
    by_cases ht : t = 0
    · rw [hγ, ht]; simp
    have hγ0 : γ ≠ 0 := mul_ne_zero hβ0 (pow_ne_zero 2 ht)
    refine mem_weight_of_odd Q h2p hπ ha ha0 hγg hγ0 ?_
    rw [hγ, dord_mul hπ hβ0 (pow_ne_zero 2 ht), dord_sq hπ ht]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + dord hπ t, by omega⟩
  have h4w : 4 * (algebraMap R F ρ₀ * α) ∈ weight Q L :=
    le_sup_right (b := (2 : F) • scale Q L) (four_mul_mem_two_smul_scale Q (ha.2 ▸ hαa) ρ₀)
  have : α - a * algebraMap R F s' ^ 2 = γ - 4 * (algebraMap R F ρ₀ * α) := by
    rw [hγ]; linear_combination hst
  rw [this]; exact sub_mem hγw h4w

omit [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- A norm generator of a non-zero regular lattice is non-zero. -/
theorem IsNormGenerator.ne_zero {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a : F}
    (ha : IsNormGenerator Q L a) : a ≠ 0 := by
  intro ha0
  apply hne
  rw [eq_bot_iff]
  intro x hx
  refine (mem_bot R).mpr (hreg x hx fun y hy => ?_)
  have hQ : ∀ z ∈ L, Q z = 0 := fun z hz => by
    have := Q_mem_normIdeal Q hz
    rw [← ha.2, ha0, span_singleton_eq_bot.mpr rfl] at this
    exact (mem_bot R).mp this
  have h := Q_add Q x y
  rw [hQ _ (L.add_mem hx hy), hQ x hx, hQ y hy] at h
  have : (2 : F) * bil Q x y = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left (two_ne_zero' F)

/-- **Proposition 93:4** (O'Meara 1963, p. 254): let $L$ be a non-zero regular lattice over a dyadic local field, with
norm generator $a$ and weight generator $b$. Then $\mathfrak gL = a\mathfrak o^2 + b\mathfrak o$, i.e. the elements of
$\mathfrak gL$ are exactly the $a\varepsilon^2 + b\eta$ with $\varepsilon, \eta \in \mathfrak o$. -/
@[kb "omeara1963" "§93A, 93:4, p. 254"]
theorem normGroup_eq_sq_add (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hreg : IsRegular Q L) (hne : L ≠ ⊥)
    {a b : F} (ha : IsNormGenerator Q L a) (hb : IsWeightGenerator Q L b) :
    (normGroup Q L : Set F) = {z | ∃ ε η : R, z = a * algebraMap R F ε ^ 2 + b * algebraMap R F η} := by
  have ha0 := ha.ne_zero Q hreg hne
  ext z
  constructor
  · intro hz
    obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 hz
    rw [← hb] at hε
    obtain ⟨η, hη⟩ := mem_span_singleton.mp hε
    exact ⟨ε, η, by rw [Algebra.smul_def] at hη; rw [mul_comm b, hη]; ring⟩
  · rintro ⟨ε, η, rfl⟩
    refine add_mem ?_ ?_
    · rw [mul_comm]; exact mul_sq_mem_normGroup Q ha.1 ⟨ε, rfl⟩
    · have : b * algebraMap R F η ∈ weight Q L := by
        rw [← hb, mul_comm, ← Algebra.smul_def]; exact smul_mem _ _ (mem_span_singleton_self b)
      exact normGroupIdeal_subset Q L ((weight_bounds Q L).2.1 this)

/-- **Example 93:6, "only if" direction** (O'Meara 1963, p. 254): over a dyadic local field, any two norm generators
$a, a'$ of a non-zero regular lattice $L$ satisfy $a \cong a' \bmod \mathfrak wL$. -/
@[kb "omeara1963" "§93A, 93:6, p. 254 (two norm generators satisfy a ≅ a' mod wL)"]
theorem sqEquivMod_of_isNormGenerator (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hreg : IsRegular Q L)
    (hne : L ≠ ⊥) {a a' : F} (ha : IsNormGenerator Q L a) (ha' : IsNormGenerator Q L a') :
    SqEquivMod (weight Q L) a a' := by
  have ha0 := ha.ne_zero Q hreg hne
  have ha'0 := ha'.ne_zero Q hreg hne
  obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp (ha'.2.trans ha.2.symm)
  refine ⟨⟨u, u.isUnit, by rw [← hu, Units.smul_def, Algebra.smul_def]⟩, ?_⟩
  obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 ha'.1
  by_cases hεu : IsUnit ε
  · obtain ⟨ε', hε'⟩ := hεu.exists_left_inv
    refine ⟨ε', isUnit_iff_exists_inv.2 ⟨ε, hε'⟩, ?_⟩
    have hεF : algebraMap R F ε' * algebraMap R F ε = 1 := by rw [← map_mul, hε', map_one]
    have := smul_mem (weight Q L) (-(ε' ^ 2)) hε
    convert this using 1
    rw [Algebra.smul_def, map_neg, map_pow]
    linear_combination (-a) * (algebraMap R F ε' * algebraMap R F ε + 1) * hεF
  · -- `ε ∈ 𝔭`: then `a' ∈ 𝔴L`, hence `𝔴L = 𝔫L` and `ε = 1` works
    refine ⟨1, isUnit_one, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have ha'w : a' ∈ weight Q L := by
      by_cases hε0 : ε = 0
      · simpa [hε0] using hε
      have hεF : algebraMap R F ε ≠ 0 := (map_ne_zero_iff _ alg_inj).2 hε0
      have hdε : 1 ≤ dord hπ (algebraMap R F ε) := by
        have hm : ε ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hεu
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hm
        obtain ⟨c, rfl⟩ := hm
        have hc0 : c ≠ 0 := by rintro rfl; simp at hε0
        rw [map_mul, dord_mul hπ (alg_pi_ne_zero hπ) ((map_ne_zero_iff _ alg_inj).2 hc0),
          show algebraMap R F π = algebraMap R F π ^ (1 : ℤ) by simp, dord_zpow]
        have := dord_alg_nonneg (F := F) hπ hc0
        omega
      have hda : dord hπ a' = dord hπ a := by
        obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp (ha.2.trans ha'.2.symm)
        rw [← hu, Units.smul_def, Algebra.smul_def, dord_mul hπ (alg_ne_zero_of_unit u.isUnit) ha0,
          dord_unit hπ u.isUnit, zero_add]
      have h2' : -(a * algebraMap R F ε ^ 2) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha0 (pow_ne_zero 2 hεF))
      have hlt : dord hπ a' < dord hπ (-(a * algebraMap R F ε ^ 2)) := by
        rw [dord_neg hπ (mul_ne_zero ha0 (pow_ne_zero 2 hεF)), dord_mul hπ ha0 (pow_ne_zero 2 hεF),
          dord_sq hπ hεF]; omega
      by_cases hsum : a' + -(a * algebraMap R F ε ^ 2) = 0
      · exfalso; rw [add_neg_eq_zero] at hsum; rw [hsum] at hlt
        rw [dord_neg hπ (mul_ne_zero ha0 (pow_ne_zero 2 hεF))] at hlt; omega
      have hd := dord_add_of_lt hπ ha'0 h2' hsum hlt
      rw [← sub_eq_add_neg] at hd hsum
      have : a' ∈ R ∙ (a' - a * algebraMap R F ε ^ 2) := (mem_span_iff hπ ha'0 hsum).mpr hd.le
      exact (span_singleton_le_iff_mem _ _).mpr hε this
    have haw : a ∈ weight Q L := by
      obtain ⟨u, hu⟩ := span_singleton_eq_span_singleton.mp (ha'.2.trans ha.2.symm)
      rw [← hu, Units.smul_def]; exact smul_mem _ _ ha'w
    simpa using sub_mem haw ha'w

/-- **Example 93:6** (O'Meara 1963, p. 254): over a dyadic local field, if $a$ is a norm generator of a non-zero
regular lattice $L$, then $a'$ is a norm generator of $L$ if and only if $a \cong a' \bmod \mathfrak wL$. -/
@[kb "omeara1963" "§93A, 93:6, p. 254"]
theorem isNormGenerator_iff_sqEquivMod (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hreg : IsRegular Q L)
    (hne : L ≠ ⊥) {a a' : F} (ha : IsNormGenerator Q L a) :
    IsNormGenerator Q L a' ↔ SqEquivMod (weight Q L) a a' :=
  ⟨fun ha' => sqEquivMod_of_isNormGenerator Q h2p hreg hne ha ha',
    fun h => isNormGenerator_of_sqEquivMod Q ha h⟩

/-- An element $\gamma \in \mathfrak gL$ of order of parity opposite to $\operatorname{ord} a$ lies in
$S + 2\mathfrak sL$ when $S$ contains every such value $Q(y)$, $y \in L$. -/
theorem mem_sup_of_odd {π : R} (hπ : Irreducible π) {L : Submodule R V} {a : F} {S : Submodule R F}
    (hS : ∀ y ∈ L, Q y ≠ 0 → Odd (dord hπ (Q y) - dord hπ a) → Q y ∈ S) {γ : F} (hγ : γ ∈ normGroup Q L)
    (hγ0 : γ ≠ 0) (hodd : Odd (dord hπ γ - dord hπ a)) : γ ∈ S ⊔ (2 : F) • scale Q L := by
  obtain ⟨y, hy, c, hc, rfl⟩ := hγ
  have h2c : 2 * c ∈ (2 : F) • scale Q L := Submodule.smul_mem_pointwise_smul _ (2 : F) _ hc
  by_cases hQ : Q y = 0
  · rw [hQ, zero_add]; exact mem_sup_right h2c
  by_cases hc0 : 2 * c = 0
  · rw [hc0, add_zero] at hodd hγ0 ⊢
    exact mem_sup_left (hS y hy hQ hodd)
  by_cases hle : dord hπ (2 * c) ≤ dord hπ (Q y + 2 * c)
  · refine mem_sup_right ?_
    have : Q y + 2 * c ∈ R ∙ (2 * c) := (mem_span_iff hπ hγ0 hc0).mpr hle
    exact (span_singleton_le_iff_mem _ _).mpr h2c this
  · push_neg at hle
    have hd : dord hπ (Q y + 2 * c + -(2 * c)) = dord hπ (Q y + 2 * c) :=
      dord_add_of_lt hπ hγ0 (neg_ne_zero.mpr hc0) (by simpa using hQ)
        (by rwa [dord_neg hπ hc0])
    simp only [add_neg_cancel_right] at hd
    have hmem : Q y + 2 * c ∈ R ∙ Q y := (mem_span_iff hπ hγ0 hQ).mpr hd.le
    exact mem_sup_left ((span_singleton_le_iff_mem _ _).mpr (hS y hy hQ (by rwa [hd])) hmem)

/-- **The weight from values of the opposite parity** (O'Meara 1963, §93A, 93:5, p. 254, general form): over a dyadic
local field, let $a \ne 0$ be a norm generator of $L$ and $S \subseteq \mathfrak wL$ an $\mathfrak o$-submodule
containing every non-zero value $Q(y)$, $y \in L$, with $\operatorname{ord} Q(y) + \operatorname{ord} a$ odd. Then
$\mathfrak wL = S + 2(\mathfrak sL)$. -/
theorem weight_eq_sup (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V} {a : F}
    (ha : IsNormGenerator Q L a) (ha0 : a ≠ 0) {S : Submodule R F} (hSw : S ≤ weight Q L)
    (hS : ∀ y ∈ L, Q y ≠ 0 → Odd (dord hπ (Q y) - dord hπ a) → Q y ∈ S) :
    weight Q L = S ⊔ (2 : F) • scale Q L := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le hSw le_sup_right)
  rw [Submodule.mul_le]
  rintro _ ⟨r, hr, rfl⟩ z hz
  simp only [Algebra.linearMap_apply]
  have hr' : r ∈ maximalIdeal R := hr
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.mem_span_singleton] at hr'
  obtain ⟨r', rfl⟩ := hr'
  set z' := algebraMap R F r' * z with hz'
  have hz'm : z' ∈ normGroupIdeal Q L := by
    rw [hz', ← Algebra.smul_def]; exact smul_mem _ _ hz
  have hπF := alg_pi_ne_zero (R := R) (F := F) hπ
  have heq : algebraMap R F (π * r') * z = algebraMap R F π * z' := by rw [hz', map_mul]; ring
  rw [heq]
  by_cases hz0 : z' = 0
  · rw [hz0, mul_zero]; exact zero_mem _
  have hz'g := normGroupIdeal_subset Q L hz'm
  have hπz : algebraMap R F π * z' ∈ normGroupIdeal Q L := by
    rw [← Algebra.smul_def]; exact smul_mem _ _ hz'm
  have hd : dord hπ (algebraMap R F π * z') = dord hπ z' + 1 := by
    rw [dord_mul hπ hπF hz0, show algebraMap R F π = algebraMap R F π ^ (1 : ℤ) by simp, dord_zpow]; ring
  rcases Int.even_or_odd (dord hπ z' - dord hπ a) with he | ho
  · refine mem_sup_of_odd Q hπ hS (normGroupIdeal_subset Q L hπz) (mul_ne_zero hπF hz0) ?_
    rw [hd]; obtain ⟨k, hk⟩ := he; exact ⟨k, by omega⟩
  · have := mem_sup_of_odd Q hπ hS hz'g hz0 ho
    rw [← Algebra.smul_def]; exact smul_mem _ _ this

/-- **Example 93:5, weight generators** (O'Meara 1963, p. 254): over a dyadic local field, let $L$ be a non-zero
regular lattice with norm generator $a$. (1) If $b_0 = Q(x_0)$, $x_0 \in L$, is a value of largest absolute value among
the values $Q(y) \ne 0$ with $\operatorname{ord} a + \operatorname{ord} Q(y)$ odd, then $\mathfrak wL = b_0\mathfrak o +
2(\mathfrak sL)$; so $\mathfrak wL = b_0\mathfrak o$ if $b_0\mathfrak o \supseteq 2(\mathfrak sL)$, and
$\mathfrak wL = 2(\mathfrak sL)$ otherwise. (2) If there is no such value, $\mathfrak wL = 2(\mathfrak sL)$. -/
@[kb "omeara1963" "§93A, 93:5, p. 254 (finding a weight generator)"]
theorem weight_eq_of_largest_odd_value (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {L : Submodule R V}
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) {a : F} (ha : IsNormGenerator Q L a) :
    (∀ {x₀ : V}, x₀ ∈ L → Q x₀ ≠ 0 → Odd (dord hπ (Q x₀) - dord hπ a) →
      (∀ y ∈ L, Q y ≠ 0 → Odd (dord hπ (Q y) - dord hπ a) → Q y ∈ R ∙ Q x₀) →
      weight Q L = (R ∙ Q x₀) ⊔ (2 : F) • scale Q L) ∧
    ((∀ y ∈ L, Q y ≠ 0 → ¬ Odd (dord hπ (Q y) - dord hπ a)) → weight Q L = (2 : F) • scale Q L) := by
  have ha0 := ha.ne_zero Q hreg hne
  refine ⟨fun {x₀} hx₀ hQ0 hodd hmax => ?_, fun hnone => ?_⟩
  · refine weight_eq_sup Q h2p hπ ha ha0 ?_ hmax
    rw [span_singleton_le_iff_mem]
    exact mem_weight_of_odd Q h2p hπ ha ha0 (Q_mem_normGroup Q hx₀) hQ0 hodd
  · have := weight_eq_sup Q h2p hπ ha ha0 (S := ⊥) bot_le (fun y hy hQ hodd => absurd hodd (hnone y hy hQ))
    rwa [bot_sup_eq] at this

end Main

end QuadFormsKB.OMeara
