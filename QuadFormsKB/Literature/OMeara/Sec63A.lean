/-
# O'Meara §63A: the quadratic defect

**Setting.** O'Meara (1973 printing, §63, pp. 158–163) works over a local field $F$ with ring of integers
$\mathfrak o$, maximal ideal $\mathfrak p$, prime element $\pi$, characteristic of $F$ not $2$. Here $R$ is a discrete
valuation ring with fraction field $F$ (`IsFractionRing R F`), $\pi$ is a prime element of $R$ (`Irreducible π`),
$2 \ne 0$ in $R$, and fractional ideals of $F$ are $R$-submodules of $F$ (`Submodule R F`); $\mathfrak o$ is
`(1 : Submodule R F)` and $\alpha\mathfrak o$ is `span R {α}`. Of the completeness of $F$ only the Henselian property
of $R$ is used (`HenselianLocalRing R`, through the Local Square Theorem `isSquare_one_add_four_mul` of `Sec91.lean`),
and of the finiteness of the residue field only that it is finite (`Finite (ResidueField R)`), each where needed.
$F$ is *dyadic* when $2 \in \mathfrak p$ (`¬ IsUnit (2 : R)`), *non-dyadic* when $2$ is a unit.

**Defines** the quadratic defect (§63A, pp. 159–160)
$$\mathfrak d(\xi) = \bigcap_{\xi = \eta^2 + \alpha} \alpha\mathfrak o = \bigcap_{\eta \in F} (\xi - \eta^2)\mathfrak o$$
(`quadDefect R ξ`), a fractional ideal or $0$.

**Proves** (pp. 160–162)
* `quadDefect_le_span` ($\mathfrak d(\xi) \subseteq \xi\mathfrak o$), `isSquare_iff_quadDefect_eq_bot`
  ($\xi \in F^{2} \iff \mathfrak d(\xi) = 0$), `exists_quadDefect_eq` (the defect is attained:
  $\xi = \eta^2 + \alpha$ with $\alpha\mathfrak o = \mathfrak d(\xi)$), `quadDefect_sq_mul`
  ($\mathfrak d(\alpha^2\xi) = \alpha^2\mathfrak d(\xi)$), `quadDefect_of_odd` ($\mathfrak d(\xi) = \xi\mathfrak o$ if
  $\operatorname{ord}\xi$ is odd), `quadDefect_zpow_mul` ($\mathfrak d(\pi^{2r}\varepsilon) = \pi^{2r}\mathfrak
  d(\varepsilon)$), `quadDefect_eq_pow_iff` ($\mathfrak d(\varepsilon) = \mathfrak p^d$ iff $\varepsilon$ is a square
  mod $\mathfrak p^d$ but not mod $\mathfrak p^{d+1}$);
* Proposition 63:2 (`quadDefect_unit_nondyadic`, `quadDefect_unit_dyadic`), Proposition 63:5
  (`quadDefect_one_add`), Remark 63:6 (`exists_quadDefect_nondyadic`, `exists_quadDefect_dyadic`).
-/
import QuadFormsKB.Literature.OMeara.Sec91

open Submodule IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- **The quadratic defect** $\mathfrak d(\xi)$ of $\xi \in F$ (O'Meara 1963, §63A, pp. 159–160): the intersection of
the ideals $\alpha\mathfrak o$ over all expressions $\xi = \eta^2 + \alpha$ with $\eta, \alpha \in F$, i.e.
$\bigcap_{\eta \in F} (\xi - \eta^2)\mathfrak o$. It is a fractional ideal or $0$. -/
@[kb "omeara1963" "§63A, pp. 159–160 (the quadratic defect 𝔡(ξ))"]
def quadDefect (ξ : F) : Submodule R F := ⨅ η : F, span R {ξ - η ^ 2}

variable {R}

/-! ### Auxiliary: the order function on $F$ -/

section OrdAux

variable {π : R}

lemma alg_inj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F

lemma alg_pi_ne_zero (hπ : Irreducible π) : algebraMap R F π ≠ 0 :=
  (map_ne_zero_iff _ (alg_inj (R := R) (F := F))).2 hπ.ne_zero

lemma exists_rep (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ∃ (k : ℤ) (u : R), IsUnit u ∧ x = algebraMap R F u * algebraMap R F π ^ k := by
  obtain ⟨k, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (K := F) hπ hx
  exact ⟨k, u, u.isUnit, by rw [h, Units.smul_def, Algebra.smul_def]⟩

lemma rep_le (hπ : Irreducible π) {u v : R} (hu : IsUnit u) (hv : IsUnit v) {k l : ℤ}
    (h : algebraMap R F u * algebraMap R F π ^ k = algebraMap R F v * algebraMap R F π ^ l) : k ≤ l := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = k - l := ⟨(k - l).toNat, by omega⟩
  have hm0 : m ≠ 0 := by omega
  have hk : algebraMap R F π ^ k = algebraMap R F π ^ l * algebraMap R F π ^ m := by
    rw [← zpow_natCast, ← zpow_add₀ hne]; congr 1; omega
  rw [hk] at h
  have h2 : algebraMap R F v = algebraMap R F u * algebraMap R F π ^ m := by
    have hl : algebraMap R F π ^ l ≠ 0 := zpow_ne_zero _ hne
    apply mul_right_cancel₀ hl
    rw [← h]; ring
  have h3 : v = u * π ^ m := alg_inj (by rw [h2]; simp)
  have : π ∣ v := h3 ▸ dvd_mul_of_dvd_right (dvd_pow_self π hm0) u
  exact hπ.not_isUnit (isUnit_of_dvd_unit this hv)

open Classical in
/-- The order of $x \in F$ at $\pi$ (junk value $0$ at $x = 0$). -/
def dord (hπ : Irreducible π) (x : F) : ℤ :=
  if hx : x = 0 then 0 else (exists_rep hπ hx).choose

lemma dord_spec (hπ : Irreducible π) {x : F} (hx : x ≠ 0) :
    ∃ u : R, IsUnit u ∧ x = algebraMap R F u * algebraMap R F π ^ dord hπ x := by
  unfold dord; rw [dif_neg hx]; exact (exists_rep hπ hx).choose_spec

lemma dord_eq (hπ : Irreducible π) {x : F} {u : R} (hu : IsUnit u) {k : ℤ}
    (h : x = algebraMap R F u * algebraMap R F π ^ k) : dord hπ x = k := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  have hx : x ≠ 0 := by
    rw [h]; exact mul_ne_zero ((map_ne_zero_iff _ alg_inj).2 hu.ne_zero) (zpow_ne_zero _ hne)
  obtain ⟨v, hv, h'⟩ := dord_spec hπ hx
  have := h.symm.trans h'
  exact le_antisymm (rep_le hπ hv hu this.symm) (rep_le hπ hu hv this)

lemma dord_mul (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    dord hπ (x * y) = dord hπ x + dord hπ y := by
  obtain ⟨u, hu, hxu⟩ := dord_spec hπ hx
  obtain ⟨v, hv, hyv⟩ := dord_spec hπ hy
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  refine dord_eq hπ (u := u * v) (hu.mul hv) ?_
  conv_lhs => rw [hxu, hyv]
  rw [zpow_add₀ hne, map_mul]; ring

lemma dord_unit (hπ : Irreducible π) {u : R} (hu : IsUnit u) : dord hπ (algebraMap R F u) = 0 :=
  dord_eq hπ hu (by simp)

lemma dord_zpow (hπ : Irreducible π) (k : ℤ) : dord hπ (algebraMap R F π ^ k) = k :=
  dord_eq hπ (u := 1) isUnit_one (by simp)

lemma dord_neg (hπ : Irreducible π) {x : F} (hx : x ≠ 0) : dord hπ (-x) = dord hπ x := by
  obtain ⟨u, hu, h⟩ := dord_spec hπ hx
  generalize dord hπ x = k at h ⊢
  exact dord_eq hπ (u := -u) hu.neg (by rw [h]; simp)

lemma dord_sq (hπ : Irreducible π) {x : F} (hx : x ≠ 0) : dord hπ (x ^ 2) = 2 * dord hπ x := by
  rw [pow_two, dord_mul hπ hx hx]; ring

lemma exists_alg_of_nonneg (hπ : Irreducible π) {x : F} (hx : x ≠ 0) (h : 0 ≤ dord hπ x) :
    ∃ r : R, algebraMap R F r = x := by
  obtain ⟨u, hu, h'⟩ := dord_spec hπ hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = dord hπ x := ⟨(dord hπ x).toNat, by omega⟩
  rw [← hn] at h'
  exact ⟨u * π ^ n, by rw [h']; simp⟩

lemma exists_max_of_pos (hπ : Irreducible π) {x : F} (hx : x ≠ 0) (h : 1 ≤ dord hπ x) :
    ∃ r ∈ IsLocalRing.maximalIdeal R, algebraMap R F r = x := by
  obtain ⟨u, hu, h'⟩ := dord_spec hπ hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = dord hπ x - 1 := ⟨(dord hπ x - 1).toNat, by omega⟩
  refine ⟨u * π ^ n * π, ?_, ?_⟩
  · exact Ideal.mul_mem_left _ _ (hπ.not_isUnit)
  · have : dord hπ x = (n : ℤ) + 1 := by omega
    rw [this] at h'
    rw [h', zpow_add₀ (alg_pi_ne_zero (R := R) (F := F) hπ)]; simp; ring

lemma dord_alg_nonneg (hπ : Irreducible π) {r : R} (hr : r ≠ 0) : 0 ≤ dord hπ (algebraMap R F r) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
  rw [dord_eq hπ (u := u) u.isUnit (k := (n : ℤ)) (by simp)]
  exact Int.natCast_nonneg n

lemma mem_span_iff (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    x ∈ span R {y} ↔ dord hπ y ≤ dord hπ x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; simp at hx
    rw [Algebra.smul_def, dord_mul hπ ((map_ne_zero_iff _ alg_inj).2 hr) hy]
    linarith [dord_alg_nonneg (F := F) hπ hr]
  · intro h
    have hxy : x / y ≠ 0 := div_ne_zero hx hy
    have : dord hπ x = dord hπ (x / y) + dord hπ y := by
      rw [← dord_mul hπ hxy hy, div_mul_cancel₀ _ hy]
    obtain ⟨r, hr⟩ := exists_alg_of_nonneg hπ hxy (by omega)
    exact ⟨r, by rw [Algebra.smul_def, hr, div_mul_cancel₀ _ hy]⟩

lemma mem_span_zpow_iff (hπ : Irreducible π) {x : F} (hx : x ≠ 0) (k : ℤ) :
    x ∈ span R {algebraMap R F π ^ k} ↔ k ≤ dord hπ x := by
  rw [mem_span_iff hπ hx (zpow_ne_zero _ (alg_pi_ne_zero (R := R) (F := F) hπ)), dord_zpow]

lemma mem_span_zpow_iff' (hπ : Irreducible π) (x : F) (k : ℤ) :
    x ∈ span R {algebraMap R F π ^ k} ↔ x = 0 ∨ k ≤ dord hπ x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx, mem_span_zpow_iff hπ hx]

lemma dord_add_ge (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (dord hπ x) (dord hπ y) ≤ dord hπ (x + y) := by
  rw [← mem_span_zpow_iff hπ hxy]
  exact add_mem ((mem_span_zpow_iff hπ hx _).2 (min_le_left _ _)) ((mem_span_zpow_iff hπ hy _).2 (min_le_right _ _))

lemma dord_add_of_lt (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)
    (h : dord hπ x < dord hπ y) : dord hπ (x + y) = dord hπ x := by
  have h1 := dord_add_ge hπ hx hy hxy
  rw [min_eq_left h.le] at h1
  by_contra hne
  have hlt : dord hπ x + 1 ≤ dord hπ (x + y) := by omega
  have hx' : x ∈ span R {algebraMap R F π ^ (dord hπ x + 1)} := by
    suffices key : (x + y) + (-y) ∈ span R {algebraMap R F π ^ (dord hπ x + 1)} by
      rwa [show (x + y) + -y = x by ring] at key
    refine add_mem ((mem_span_zpow_iff hπ hxy _).2 hlt) ((mem_span_zpow_iff hπ (neg_ne_zero.2 hy) _).2 ?_)
    rw [dord_neg hπ hy]; omega
  rw [mem_span_zpow_iff hπ hx] at hx'
  omega

lemma mem_span_scale {c : F} (hc : c ≠ 0) (w y : F) :
    c * w ∈ span R {c * y} ↔ w ∈ span R {y} := by
  simp only [Submodule.mem_span_singleton, Algebra.smul_def]
  refine exists_congr fun r => ?_
  constructor
  · intro h; apply mul_left_cancel₀ hc; rw [← h]; ring
  · intro h; rw [← h]; ring

lemma mem_span_mul {c : F} (hc : c ≠ 0) (N : Submodule R F) (z : F) :
    z ∈ span R {c} * N ↔ c⁻¹ * z ∈ N := by
  rw [Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [inv_mul_cancel_left₀ hc]
  · intro h; exact ⟨_, h, mul_inv_cancel_left₀ hc z⟩

lemma alg_mem_span_iff (x y : R) :
    algebraMap R F y ∈ span R {algebraMap R F x} ↔ y ∈ Ideal.span {x} := by
  rw [Submodule.mem_span_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, alg_inj (by rw [← hr, Algebra.smul_def]; simp [mul_comm])⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [Algebra.smul_def]; simp [mul_comm]⟩

lemma exists_alg_of_sq {η : F} {c : R} (h : η ^ 2 = algebraMap R F c) : ∃ δ : R, algebraMap R F δ = η := by
  have : IsIntegral R η := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [h]; exact isIntegral_algebraMap
  exact IsIntegrallyClosed.isIntegral_iff.1 this

lemma four_ne_zero' (h2 : (2 : R) ≠ 0) : (4 : R) ≠ 0 := by
  rw [show (4 : R) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2

lemma four_F_eq : (4 : F) = algebraMap R F 4 := (map_ofNat (algebraMap R F) 4).symm

lemma four_F_ne (h2 : (2 : R) ≠ 0) : (4 : F) ≠ 0 := by
  rw [four_F_eq (R := R)]; exact (map_ne_zero_iff _ alg_inj).2 (four_ne_zero' h2)

lemma dord_four_nonneg (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) : 0 ≤ dord hπ (4 : F) := by
  rw [four_F_eq (R := R)]; exact dord_alg_nonneg hπ (four_ne_zero' h2)

/-- Key step of the Local Square Theorem argument (63:1a). -/
lemma isSquare_of_dord_gt [HenselianLocalRing R] (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {ξ η : F}
    (hξ : ξ ≠ 0) (hne : ξ - η ^ 2 ≠ 0) (h : dord hπ ξ + dord hπ (4 : F) < dord hπ (ξ - η ^ 2)) :
    IsSquare ξ := by
  have h4 := dord_four_nonneg (F := F) hπ h2
  have h4ne := four_F_ne (R := R) (F := F) h2
  have hη : η ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at h
    omega
  have hη2 : η ^ 2 ≠ 0 := pow_ne_zero 2 hη
  have hle : dord hπ (η ^ 2) ≤ dord hπ ξ := by
    by_contra hlt
    have := dord_add_ge hπ hη2 hne (by rw [show η ^ 2 + (ξ - η ^ 2) = ξ by ring]; exact hξ)
    rw [show η ^ 2 + (ξ - η ^ 2) = ξ by ring] at this
    rw [min_def] at this
    split_ifs at this <;> omega
  set a := (ξ - η ^ 2) / (4 * η ^ 2) with ha_def
  have ha : ξ - η ^ 2 = a * (4 * η ^ 2) := by rw [ha_def]; field_simp
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_mul] at ha; exact hne ha
  have hd : dord hπ (ξ - η ^ 2) = dord hπ a + (dord hπ (4 : F) + dord hπ (η ^ 2)) := by
    conv_lhs => rw [ha]
    rw [dord_mul hπ ha0 (mul_ne_zero h4ne hη2), dord_mul hπ h4ne hη2]
  obtain ⟨r, hr, hra⟩ := exists_max_of_pos hπ ha0 (by omega)
  obtain ⟨s, hs⟩ := isSquare_one_add_four_mul hr
  refine ⟨η * algebraMap R F s, ?_⟩
  have h1 : (1 : F) + 4 * a = algebraMap R F s * algebraMap R F s := by
    rw [← map_mul, ← hs, map_add, map_one, map_mul, ← four_F_eq, hra]
  calc ξ = η ^ 2 * (1 + 4 * a) := by linear_combination ha
    _ = _ := by rw [h1]; ring

lemma dord_le_of_not_isSquare [HenselianLocalRing R] (hπ : Irreducible π) (h2 : (2 : R) ≠ 0) {ξ : F}
    (hns : ¬ IsSquare ξ) (η : F) :
    ξ - η ^ 2 ≠ 0 ∧ dord hπ (ξ - η ^ 2) ≤ dord hπ ξ + dord hπ (4 : F) := by
  have hξ : ξ ≠ 0 := by rintro rfl; exact hns ⟨0, by simp⟩
  have hne : ξ - η ^ 2 ≠ 0 := by
    intro h0; exact hns ⟨η, by rw [← sq]; linear_combination h0⟩
  refine ⟨hne, ?_⟩
  by_contra hlt
  exact hns (isSquare_of_dord_gt hπ h2 hξ hne (not_le.1 hlt))

lemma exists_alg_of_mem_span_zpow (hπ : Irreducible π) {z : F} {n : ℤ} (hn : 0 ≤ n)
    (hz : z ∈ span R {algebraMap R F π ^ n}) : ∃ c : R, algebraMap R F c = z := by
  by_cases h0 : z = 0
  · exact ⟨0, by simp [h0]⟩
  · exact exists_alg_of_nonneg hπ h0 (le_trans hn ((mem_span_zpow_iff hπ h0 n).1 hz))

/-- If $a - \eta^2 \in \pi^d\mathfrak o$ with $a$ integral, then $\eta$ is integral. -/
lemma exists_alg_of_sub (hπ : Irreducible π) {a : R} {η : F} {d : ℕ}
    (hz : algebraMap R F a - η ^ 2 ∈ span R {algebraMap R F π ^ (d : ℤ)}) :
    ∃ δ : R, algebraMap R F δ = η := by
  obtain ⟨c, hc⟩ := exists_alg_of_mem_span_zpow hπ (Int.natCast_nonneg d) hz
  exact exists_alg_of_sq (c := a - c) (by rw [map_sub, hc]; ring)

lemma sub_sq_mem_span_iff (a δ : R) (d : ℕ) :
    algebraMap R F a - (algebraMap R F δ) ^ 2 ∈ span R {algebraMap R F π ^ d} ↔
      a - δ ^ 2 ∈ Ideal.span {π ^ d} := by
  rw [← alg_mem_span_iff (F := F)]
  simp

lemma pow_mem_or (hπ : Irreducible π) (z : F) (d : ℤ) :
    algebraMap R F π ^ d ∈ span R {z} ∨ z ∈ span R {algebraMap R F π ^ (d + 1)} := by
  by_cases hz : z = 0
  · right; simp [hz]
  · rw [mem_span_iff hπ (zpow_ne_zero _ (alg_pi_ne_zero hπ)) hz, mem_span_zpow_iff hπ hz, dord_zpow]
    omega

lemma span_eq_of_dord_eq (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : dord hπ x = dord hπ y) : span R {x} = span R {y} := by
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, mem_span_iff hπ hx hy]; omega
  · rw [Submodule.span_singleton_le_iff_mem, mem_span_iff hπ hy hx]; omega

lemma alg_ne_zero_of_unit {u : R} (hu : IsUnit u) : algebraMap R F u ≠ 0 :=
  (map_ne_zero_iff _ alg_inj).2 hu.ne_zero

lemma exists_sq_mod [Finite (IsLocalRing.ResidueField R)] (h2p : ¬ IsUnit (2 : R)) (v : R) :
    ∃ y : R, v - y ^ 2 ∈ IsLocalRing.maximalIdeal R := by
  have h2z : (2 : IsLocalRing.ResidueField R) = 0 := by
    have : IsLocalRing.residue R 2 = 0 := (IsLocalRing.residue_eq_zero_iff _).2
      (by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2p)
    rwa [map_ofNat] at this
  have hc : CharP (IsLocalRing.ResidueField R) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2z
  have hring : ringChar (IsLocalRing.ResidueField R) = 2 := ringChar.eq _ 2
  obtain ⟨z, hz⟩ := FiniteField.isSquare_of_char_two hring (IsLocalRing.residue R v)
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  refine ⟨y, (IsLocalRing.residue_eq_zero_iff _).1 ?_⟩
  rw [map_sub, map_pow, hz, sq, sub_self]

lemma exists_better_sq [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) {u δ : R} {r : ℕ} (hx : u - δ ^ 2 ≠ 0)
    (hord : dord hπ (algebraMap R F (u - δ ^ 2)) = 2 * r)
    (hr : ((2 * r : ℕ) : ℤ) < dord hπ (4 : F)) :
    ∃ δ' : R, u - δ' ^ 2 ∈ Ideal.span {π ^ (2 * r + 1)} := by
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hn : (n : ℤ) = 2 * r := by
    rw [← hord]; symm; exact dord_eq hπ v.isUnit (k := n) (by rw [hv]; simp)
  obtain ⟨t, w, h2eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h2 hπ
  have h2F' : (2 : F) = algebraMap R F 2 := (map_ofNat _ 2).symm
  have h2F : (2 : F) ≠ 0 := by
    rw [h2F']; exact (map_ne_zero_iff _ alg_inj).2 h2
  have ht : dord hπ (2 : F) = t :=
    dord_eq hπ w.isUnit (by rw [h2F', h2eq]; simp)
  have h4 : dord hπ (4 : F) = 2 * t := by
    rw [show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F, ht]; ring
  obtain ⟨y, hy⟩ := exists_sq_mod h2p (v : R)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at hy
  obtain ⟨s, hs⟩ := hy
  have hn' : n = 2 * r := by omega
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t = r + 1 + t' := ⟨t - (r + 1), by push_cast at hr; omega⟩
  subst hn' ht'
  refine ⟨δ + π ^ r * y, ?_⟩
  rw [Ideal.mem_span_singleton]
  exact ⟨s - w * π ^ t' * δ * y, by linear_combination hv + π ^ (2 * r) * hs - δ * π ^ r * y * h2eq⟩

end OrdAux

/-- **$\mathfrak d(\xi) \subseteq \xi\mathfrak o$** (O'Meara 1963, §63A, p. 160). -/
@[kb "omeara1963" "§63A, p. 160 (𝔡(ξ) ⊆ ξ𝔬)"]
theorem quadDefect_le_span (ξ : F) : quadDefect R ξ ≤ span R {ξ} := by
  refine (iInf_le _ 0).trans ?_
  simp

/-- **$\xi \in F^{2}$ if and only if $\mathfrak d(\xi) = 0$** (O'Meara 1963, §63A, p. 160; the converse direction uses
the Local Square Theorem). -/
@[kb "omeara1963" "§63A, p. 160 (ξ ∈ F² if and only if 𝔡(ξ) = 0)"]
theorem isSquare_iff_quadDefect_eq_bot [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) (ξ : F) :
    IsSquare ξ ↔ quadDefect R ξ = ⊥ := by
  constructor
  · rintro ⟨η, rfl⟩
    refine eq_bot_iff.2 ((iInf_le _ η).trans ?_)
    rw [show η * η - η ^ 2 = 0 by ring]; simp
  · intro h
    by_contra hns
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmem : algebraMap R F π ^ (dord hπ ξ + dord hπ (4 : F)) ∈ quadDefect R ξ := by
      rw [quadDefect, Submodule.mem_iInf]
      intro η
      obtain ⟨hne, hle⟩ := dord_le_of_not_isSquare hπ h2 hns η
      exact (mem_span_iff hπ (zpow_ne_zero _ (alg_pi_ne_zero hπ)) hne).2 (by rw [dord_zpow]; exact hle)
    rw [h] at hmem
    exact zpow_ne_zero _ (alg_pi_ne_zero (R := R) (F := F) hπ) ((Submodule.mem_bot R).1 hmem)

/-- **The defect is attained** (O'Meara 1963, §63A, p. 160): every $\xi$ has an expression $\xi = \eta^2 + \alpha$ with
$\alpha\mathfrak o = \mathfrak d(\xi)$. -/
@[kb "omeara1963" "§63A, p. 160 (ξ = η² + α with α𝔬 = 𝔡(ξ))"]
theorem exists_quadDefect_eq [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) (ξ : F) :
    ∃ η : F, span R {ξ - η ^ 2} = quadDefect R ξ := by
  by_cases hsq : IsSquare ξ
  · obtain ⟨η, hη⟩ := hsq
    refine ⟨η, ?_⟩
    rw [(isSquare_iff_quadDefect_eq_bot h2 ξ).1 ⟨η, hη⟩, hη, show η * η - η ^ 2 = 0 by ring]
    simp
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨z, ⟨η₀, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd
      (P := fun z => ∃ η : F, dord hπ (ξ - η ^ 2) = z)
      ⟨dord hπ ξ + dord hπ (4 : F), by
        rintro z ⟨η, rfl⟩; exact (dord_le_of_not_isSquare hπ h2 hsq η).2⟩ ⟨_, 0, rfl⟩
    refine ⟨η₀, le_antisymm (le_iInf fun η => ?_) (iInf_le _ η₀)⟩
    rw [Submodule.span_singleton_le_iff_mem]
    exact (mem_span_iff hπ (dord_le_of_not_isSquare hπ h2 hsq η₀).1 (dord_le_of_not_isSquare hπ h2 hsq η).1).2
      (hz _ ⟨η, rfl⟩)

/-- **$\mathfrak d(\alpha^2\xi) = \alpha^2\mathfrak d(\xi)$** for all $\alpha, \xi \in F$ (O'Meara 1963, §63A, p. 160).
-/
@[kb "omeara1963" "§63A, p. 160 (𝔡(α²ξ) = α²𝔡(ξ))"]
theorem quadDefect_sq_mul (α ξ : F) : quadDefect R (α ^ 2 * ξ) = span R {α ^ 2} * quadDefect R ξ := by
  by_cases hα : α = 0
  · subst hα
    have : quadDefect R ((0 : F) ^ 2 * ξ) = ⊥ := by
      refine eq_bot_iff.2 ((iInf_le _ 0).trans ?_)
      simp
    rw [this]; simp
  · have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
    ext z
    rw [mem_span_mul hα2]
    simp only [quadDefect, Submodule.mem_iInf]
    refine Iff.symm ((Equiv.mulLeft₀ α hα).forall_congr (fun η => ?_))
    have e1 : z = α ^ 2 * ((α ^ 2)⁻¹ * z) := by field_simp
    have e2 : α ^ 2 * ξ - (α * η) ^ 2 = α ^ 2 * (ξ - η ^ 2) := by ring
    change (α ^ 2)⁻¹ * z ∈ span R {ξ - η ^ 2} ↔ z ∈ span R {α ^ 2 * ξ - (α * η) ^ 2}
    rw [e2]
    conv_rhs => rw [e1]
    exact (mem_span_scale hα2 _ _).symm

/-- **$\mathfrak d(\xi) = \xi\mathfrak o$ if $\operatorname{ord}\xi$ is odd** (O'Meara 1963, §63A, p. 160): here
$\xi = \varepsilon\pi^{k}$ with $\varepsilon$ a unit and $k$ odd. -/
@[kb "omeara1963" "§63A, p. 160 (𝔡(ξ) = ξ𝔬 if ord ξ is odd)"]
theorem quadDefect_of_odd {π : R} (hπ : Irreducible π) {u : R} (hu : IsUnit u) {k : ℤ} (hk : Odd k) :
    quadDefect R (algebraMap R F u * algebraMap R F π ^ k) = span R {algebraMap R F u * algebraMap R F π ^ k} := by
  set ξ := algebraMap R F u * algebraMap R F π ^ k with hξdef
  have hdξ : dord hπ ξ = k := dord_eq hπ hu hξdef
  have hξ : ξ ≠ 0 := by
    rw [hξdef]
    exact mul_ne_zero ((map_ne_zero_iff _ alg_inj).2 hu.ne_zero) (zpow_ne_zero _ (alg_pi_ne_zero hπ))
  refine le_antisymm (quadDefect_le_span _) (le_iInf fun η => ?_)
  rw [Submodule.span_singleton_le_iff_mem]
  by_cases hη : η = 0
  · simp [hη]
  have hη2 : η ^ 2 ≠ 0 := pow_ne_zero 2 hη
  have hev : dord hπ (η ^ 2) = 2 * dord hπ η := dord_sq hπ hη
  obtain ⟨m, hm⟩ := hk
  by_cases hz : ξ - η ^ 2 = 0
  · exfalso
    have : ξ = η ^ 2 := by linear_combination hz
    rw [this, hev] at hdξ
    omega
  rw [mem_span_iff hπ hξ hz]
  by_contra hlt
  replace hlt := not_le.1 hlt
  have hsum : η ^ 2 + (ξ - η ^ 2) = ξ := by ring
  rcases lt_or_ge (dord hπ (η ^ 2)) (dord hπ (ξ - η ^ 2)) with hl | hl
  · have := dord_add_of_lt hπ hη2 hz (by rw [hsum]; exact hξ) hl
    rw [hsum] at this
    omega
  · have := dord_add_ge hπ hη2 hz (by rw [hsum]; exact hξ)
    rw [hsum, min_eq_right hl] at this
    omega

/-- **Even order reduces to units** (O'Meara 1963, §63A, p. 160): $\mathfrak d(\pi^{2r}\varepsilon) =
\pi^{2r}\mathfrak d(\varepsilon)$. -/
@[kb "omeara1963" "§63A, p. 160 (𝔡(π^{2r}ε) = π^{2r}𝔡(ε))"]
theorem quadDefect_zpow_mul (π : R) (r : ℤ) (ε : F) :
    quadDefect R (algebraMap R F π ^ (2 * r) * ε) = span R {algebraMap R F π ^ (2 * r)} * quadDefect R ε := by
  have h : algebraMap R F π ^ (2 * r) = (algebraMap R F π ^ r) ^ 2 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]; norm_num
  rw [h]
  exact quadDefect_sq_mul _ _

/-- **The meaning of the defect of a unit** (O'Meara 1963, §63A, p. 160): for a unit $\varepsilon$ and $d \ge 0$,
$\mathfrak d(\varepsilon) = \mathfrak p^{d}$ if and only if $\varepsilon$ is congruent to a square modulo
$\mathfrak p^{d}$ but not modulo $\mathfrak p^{d+1}$ (squares of integers $\delta$; for $d \ge 1$ such $\delta$ are
units). -/
@[kb "omeara1963" "§63A, p. 160 (𝔡(ε) = 𝔭^d iff ε is a square mod 𝔭^d but not mod 𝔭^{d+1})"]
theorem quadDefect_eq_pow_iff [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) {π : R} (hπ : Irreducible π) {u : R}
    (hu : IsUnit u) (d : ℕ) :
    quadDefect R (algebraMap R F u) = span R {algebraMap R F π ^ d} ↔
      (∃ δ : R, u - δ ^ 2 ∈ Ideal.span {π ^ d}) ∧ ¬ ∃ δ : R, u - δ ^ 2 ∈ Ideal.span {π ^ (d + 1)} := by
  have hzp : ∀ n : ℕ, algebraMap R F π ^ n = algebraMap R F π ^ (n : ℤ) := fun n => (zpow_natCast _ _).symm
  have hπne : ∀ k : ℤ, algebraMap R F π ^ k ≠ 0 := fun k => zpow_ne_zero _ (alg_pi_ne_zero hπ)
  constructor
  · intro hD
    obtain ⟨η, hη⟩ := exists_quadDefect_eq (F := F) h2 (algebraMap R F u)
    have hdd : algebraMap R F π ^ (d : ℤ) ∈ quadDefect R (algebraMap R F u) := by
      rw [← hzp d, hD]; exact Submodule.mem_span_singleton_self _
    have hmem : algebraMap R F u - η ^ 2 ∈ span R {algebraMap R F π ^ (d : ℤ)} := by
      rw [hD] at hη
      rw [← hzp d, ← hη]; exact Submodule.mem_span_singleton_self _
    obtain ⟨δ, rfl⟩ := exists_alg_of_sub hπ hmem
    refine ⟨⟨δ, ?_⟩, ?_⟩
    · rw [← sub_sq_mem_span_iff (F := F)]; rwa [← hzp] at hmem
    · rintro ⟨δ', hδ'⟩
      rw [← sub_sq_mem_span_iff (F := F)] at hδ'
      have h1 : quadDefect R (algebraMap R F u) ≤ span R {algebraMap R F π ^ (d + 1)} :=
        (iInf_le _ (algebraMap R F δ')).trans (by rw [Submodule.span_singleton_le_iff_mem]; exact hδ')
      have h3 := h1 hdd
      rw [hzp (d + 1), mem_span_zpow_iff hπ (hπne _), dord_zpow] at h3
      push_cast at h3
      omega
  · rintro ⟨⟨δ, hδ⟩, hnot⟩
    have hδ' := (sub_sq_mem_span_iff (F := F) u δ d).2 hδ
    have hle : quadDefect R (algebraMap R F u) ≤ span R {algebraMap R F π ^ d} :=
      (iInf_le _ (algebraMap R F δ)).trans (by rw [Submodule.span_singleton_le_iff_mem]; exact hδ')
    refine le_antisymm hle (le_iInf fun η => ?_)
    rw [Submodule.span_singleton_le_iff_mem, hzp d]
    rcases pow_mem_or hπ (algebraMap R F u - η ^ 2) (d : ℤ) with h | h
    · exact h
    · exfalso
      have h' : algebraMap R F u - η ^ 2 ∈ span R {algebraMap R F π ^ ((d + 1 : ℕ) : ℤ)} := by
        push_cast; exact h
      obtain ⟨δ'', rfl⟩ := exists_alg_of_sub hπ h'
      rw [← hzp] at h'
      exact hnot ⟨δ'', (sub_sq_mem_span_iff (F := F) u δ'' (d + 1)).1 h'⟩

/-- **Proposition 63:2, non-dyadic case** (O'Meara 1963, p. 160): if $2$ is a unit, the defect of a unit
$\varepsilon$ is $0$ or $\mathfrak o$. -/
@[kb "omeara1963" "§63A, 63:2, p. 160 (non-dyadic: 𝔡(ε) is 0 or 𝔬)"]
theorem quadDefect_unit_nondyadic [HenselianLocalRing R] (h2 : IsUnit (2 : R)) {u : R} (hu : IsUnit u) :
    quadDefect R (algebraMap R F u) = ⊥ ∨ quadDefect R (algebraMap R F u) = 1 := by
  have h2' := h2.ne_zero
  by_cases hsq : IsSquare (algebraMap R F u)
  · exact Or.inl ((isSquare_iff_quadDefect_eq_bot h2' _).1 hsq)
  right
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨η, hη⟩ := exists_quadDefect_eq (F := F) h2' (algebraMap R F u)
  obtain ⟨hne, hle⟩ := dord_le_of_not_isSquare hπ h2' hsq η
  have h4 : dord hπ (4 : F) = 0 := by
    rw [four_F_eq (R := R)]
    exact dord_unit hπ (by rw [show (4 : R) = 2 * 2 by norm_num]; exact h2.mul h2)
  have hu0 : dord hπ (algebraMap R F u) = 0 := dord_unit hπ hu
  have hx : algebraMap R F u - η ^ 2 ∈ span R {algebraMap R F u} := by
    have := quadDefect_le_span (R := R) (algebraMap R F u)
    rw [← hη] at this
    exact this (Submodule.mem_span_singleton_self _)
  rw [mem_span_iff hπ hne (alg_ne_zero_of_unit hu)] at hx
  rw [← hη, Submodule.one_eq_span]
  refine span_eq_of_dord_eq hπ hne one_ne_zero ?_
  have : dord hπ (1 : F) = 0 := by simpa using dord_unit (F := F) hπ (u := 1) isUnit_one
  omega

/-- **Proposition 63:2, dyadic case** (O'Meara 1963, p. 160): if $2 \in \mathfrak p$ (and the residue field is finite,
hence perfect), the defect of a unit $\varepsilon$ is $0$, $4\mathfrak o$, or $\mathfrak p^{d}$ with $d$ odd and
$4\mathfrak o \subset \mathfrak p^{d} \subseteq \mathfrak p$. -/
@[kb "omeara1963" "§63A, 63:2, p. 160 (dyadic: 𝔡(ε) is 0, 4𝔬, or 𝔭^d with d odd, 4𝔬 ⊂ 𝔭^d ⊆ 𝔭)"]
theorem quadDefect_unit_dyadic [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) {u : R} (hu : IsUnit u) :
    quadDefect R (algebraMap R F u) = ⊥ ∨ quadDefect R (algebraMap R F u) = span R {(4 : F)} ∨
      ∃ d : ℕ, Odd d ∧ span R {(4 : F)} < span R {algebraMap R F π ^ d} ∧
        quadDefect R (algebraMap R F u) = span R {algebraMap R F π ^ d} := by
  have hzp : ∀ n : ℕ, algebraMap R F π ^ n = algebraMap R F π ^ (n : ℤ) := fun n => (zpow_natCast _ _).symm
  by_cases hsq : IsSquare (algebraMap R F u)
  · exact Or.inl ((isSquare_iff_quadDefect_eq_bot h2 _).1 hsq)
  right
  obtain ⟨η, hη⟩ := exists_quadDefect_eq (F := F) h2 (algebraMap R F u)
  obtain ⟨hne, hle⟩ := dord_le_of_not_isSquare hπ h2 hsq η
  have hu0 : dord hπ (algebraMap R F u) = 0 := dord_unit hπ hu
  have hx : algebraMap R F u - η ^ 2 ∈ span R {algebraMap R F u} := by
    have := quadDefect_le_span (R := R) (algebraMap R F u)
    rw [← hη] at this
    exact this (Submodule.mem_span_singleton_self _)
  rw [mem_span_iff hπ hne (alg_ne_zero_of_unit hu)] at hx
  rw [hu0] at hx hle
  have hx0 : algebraMap R F u - η ^ 2 ∈ span R {algebraMap R F π ^ ((0 : ℕ) : ℤ)} :=
    (mem_span_zpow_iff hπ hne _).2 (by simpa using hx)
  obtain ⟨δ, rfl⟩ := exists_alg_of_sub hπ hx0
  have hne' : u - δ ^ 2 ≠ 0 := by
    intro h0; apply hne; rw [← map_pow, ← map_sub, h0, map_zero]
  have hcast : algebraMap R F (u - δ ^ 2) = algebraMap R F u - algebraMap R F δ ^ 2 := by
    rw [map_sub, map_pow]
  have h4 : (0 : ℤ) ≤ dord hπ (4 : F) := dord_four_nonneg hπ h2
  by_cases hk : dord hπ (algebraMap R F u - algebraMap R F δ ^ 2) = dord hπ (4 : F)
  · rw [← hη]
    exact Or.inl (span_eq_of_dord_eq hπ hne (four_F_ne h2) hk)
  have hlt : dord hπ (algebraMap R F u - algebraMap R F δ ^ 2) < dord hπ (4 : F) := by omega
  rcases Int.even_or_odd (dord hπ (algebraMap R F u - algebraMap R F δ ^ 2)) with ⟨r, hr⟩ | hodd
  · exfalso
    obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r' : ℤ) = r := ⟨r.toNat, by omega⟩
    obtain ⟨δ', hδ'⟩ := exists_better_sq (F := F) hπ h2 h2p (r := r') hne'
      (by rw [hcast]; omega) (by push_cast; omega)
    have h5 := (sub_sq_mem_span_iff (F := F) u δ' (2 * r' + 1)).2 hδ'
    have h6 : algebraMap R F u - algebraMap R F δ ^ 2 ∈ span R {algebraMap R F π ^ (2 * r' + 1)} := by
      have : quadDefect R (algebraMap R F u) ≤ span R {algebraMap R F π ^ (2 * r' + 1)} :=
        (iInf_le _ (algebraMap R F δ')).trans (by rw [Submodule.span_singleton_le_iff_mem]; exact h5)
      rw [← hη] at this
      exact this (Submodule.mem_span_singleton_self _)
    rw [hzp, mem_span_zpow_iff hπ hne] at h6
    push_cast at h6
    omega
  · obtain ⟨m, hm⟩ := hodd
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = dord hπ (algebraMap R F u - algebraMap R F δ ^ 2) :=
      ⟨(dord hπ (algebraMap R F u - algebraMap R F δ ^ 2)).toNat, by omega⟩
    refine Or.inr ⟨d, ⟨m.toNat, by omega⟩, ?_, ?_⟩
    · rw [hzp d]
      refine lt_of_le_of_ne ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem, mem_span_zpow_iff hπ (four_F_ne h2)]; omega
      · intro heq
        have : algebraMap R F π ^ (d : ℤ) ∈ span R {(4 : F)} := by
          rw [heq]; exact Submodule.mem_span_singleton_self _
        rw [mem_span_iff hπ (zpow_ne_zero _ (alg_pi_ne_zero hπ)) (four_F_ne h2), dord_zpow] at this
        omega
    · rw [← hη, hzp d]
      exact span_eq_of_dord_eq hπ hne (zpow_ne_zero _ (alg_pi_ne_zero hπ)) (by rw [dord_zpow]; omega)

/-- **Proposition 63:5** (O'Meara 1963, p. 162): in a dyadic field, if $\varepsilon = 1 + \alpha$ with
$\lvert 4\rvert < \lvert\alpha\rvert < 1$ and $\operatorname{ord}\alpha$ odd, then $\mathfrak d(\varepsilon) =
\alpha\mathfrak o$. Here $\alpha = \pi^{d}w$ with $w$ a unit and $d$ odd, and $\lvert 4\rvert < \lvert\alpha\rvert$ is
$4\mathfrak o \subset \alpha\mathfrak o$ ($d \ge 1$ gives $\lvert\alpha\rvert < 1$). -/
@[kb "omeara1963" "§63A, 63:5, p. 162 (𝔡(1 + α) = α𝔬 for |4| < |α| < 1, ord α odd)"]
theorem quadDefect_one_add [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) {π : R} (hπ : Irreducible π) {w : R}
    (hw : IsUnit w) {d : ℕ} (hd : Odd d) (h4 : span R {(4 : F)} < span R {algebraMap R F (π ^ d * w)}) :
    quadDefect R (1 + algebraMap R F (π ^ d * w)) = span R {algebraMap R F (π ^ d * w)} := by
  set α := algebraMap R F (π ^ d * w) with hαdef
  have hα : α = algebraMap R F w * algebraMap R F π ^ (d : ℤ) := by
    rw [hαdef, map_mul, map_pow, zpow_natCast]; ring
  have hdα : dord hπ α = d := dord_eq hπ hw hα
  have hα0 : α ≠ 0 := by
    rw [hα]; exact mul_ne_zero (alg_ne_zero_of_unit hw) (zpow_ne_zero _ (alg_pi_ne_zero hπ))
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  have he : dord hπ (4 : F) = 2 * dord hπ (2 : F) := by
    rw [show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F]; ring
  have hd4 : d ≤ dord hπ (4 : F) := by
    have h := h4.le (Submodule.mem_span_singleton_self (4 : F))
    rw [mem_span_iff hπ (four_F_ne h2) hα0] at h
    omega
  have hdlt : (d : ℤ) < dord hπ (4 : F) := by
    obtain ⟨m, hm⟩ := hd
    omega
  refine le_antisymm ?_ (le_iInf fun η => ?_)
  · refine (iInf_le _ 1).trans ?_
    rw [show 1 + α - 1 ^ 2 = α by ring]
  · rw [Submodule.span_singleton_le_iff_mem]
    rcases pow_mem_or hπ (1 + α - η ^ 2) (d : ℤ) with h | h
    · have := Submodule.smul_mem (span R {1 + α - η ^ 2}) w h
      rw [Algebra.smul_def, ← hα] at this
      exact this
    · exfalso
      set z := 1 + α - η ^ 2 with hz
      have hzd : z = 0 ∨ (d : ℤ) + 1 ≤ dord hπ z := (mem_span_zpow_iff' hπ z _).1 h
      have hαz : α - z ≠ 0 ∧ dord hπ (α - z) = d := by
        by_cases h0 : z = 0
        · rw [h0, sub_zero]; exact ⟨hα0, hdα⟩
        · have hz1 := hzd.resolve_left h0
          have hlt : dord hπ α < dord hπ (-z) := by rw [dord_neg hπ h0, hdα]; omega
          have hne : α + -z ≠ 0 := by
            intro h'
            have : z = α := by linear_combination -h'
            rw [this, hdα] at hz1
            omega
          rw [sub_eq_add_neg]
          exact ⟨hne, by rw [dord_add_of_lt hπ hα0 (neg_ne_zero.2 h0) hne hlt, hdα]⟩
      have key : (η - 1) * ((η - 1) + 2) = α - z := by rw [hz]; ring
      have hne := hαz.1
      rw [← key] at hne
      have hy := left_ne_zero_of_mul hne
      have hy2 := right_ne_zero_of_mul hne
      have hdd : dord hπ (η - 1) + dord hπ ((η - 1) + 2) = d := by
        rw [← dord_mul hπ hy hy2, key]; exact hαz.2
      have hsum : (η - 1) + 2 ≠ 0 := hy2
      rcases lt_or_ge (dord hπ (η - 1)) (dord hπ (2 : F)) with hl | hl
      · have := dord_add_of_lt hπ hy h2F hsum hl
        obtain ⟨m, hm⟩ := hd
        omega
      · have := dord_add_ge hπ hy h2F hsum
        rw [min_eq_right hl] at this
        omega

lemma isUnit_of_not_dvd' {π : R} (hπ : Irreducible π) {x : R} (h : ¬ π ∣ x) : IsUnit x := by
  by_contra hx
  apply h
  have : x ∈ IsLocalRing.maximalIdeal R := by
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
  rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at this

/-- Copy of `two_dvd_sub_one_of_sq_eq` (`DyadicArf.lean`): a square root of $1 - 4t$ is $\equiv 1 \pmod 2$. -/
lemma two_dvd_sub_one_of_sq_eq' {π : R} (hπ : Irreducible π) {t y : R}
    (h : y ^ 2 = 1 - 4 * t) : 2 ∣ y - 1 := by
  by_contra hu
  set u := y - 1 with hu_def
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero 2)
  obtain ⟨w, hw⟩ : u ∣ 2 := (ValuationRing.dvd_total u 2).resolve_right hu
  have hwm : ¬ IsUnit w := fun hw' =>
    hu ⟨((hw'.unit⁻¹ : Rˣ) : R), by rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  have hπw : π ∣ w := by
    by_contra hπw
    exact hwm (isUnit_of_not_dvd' hπ hπw)
  have h1w : IsUnit (1 + w) := by
    refine isUnit_of_not_dvd' hπ fun h' => hπ.not_isUnit ?_
    have : π ∣ 1 := by simpa using dvd_sub h' hπw
    exact isUnit_of_dvd_one this
  have key : u ^ 2 * (1 + w) = u ^ 2 * (w ^ 2 * (-t)) := by
    have e1 : u * (u + 2) = -(4 * t) := by rw [hu_def]; linear_combination h
    have e2 : (4 : R) = u ^ 2 * w ^ 2 := by rw [show (4 : R) = 2 ^ 2 by norm_num, hw]; ring
    rw [e2] at e1
    linear_combination e1 - u * hw
  have := mul_left_cancel₀ (pow_ne_zero 2 hu0) key
  exact hwm (isUnit_of_mul_isUnit_left (x := w) (y := w * -t)
    (by rw [← mul_assoc, ← sq, ← this]; exact h1w))

/-- **Remark 63:6, non-dyadic case** (O'Meara 1963, p. 162): both ideals of 63:2 occur as defects of units
(the residue field is finite of odd characteristic, so it has a non-square). -/
@[kb "omeara1963" "§63A, 63:6, p. 162 (non-dyadic: each ideal of 63:2 is a defect)"]
theorem exists_quadDefect_nondyadic [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : IsUnit (2 : R)) :
    (∃ u : R, IsUnit u ∧ quadDefect R (algebraMap R F u) = ⊥) ∧
      ∃ u : R, IsUnit u ∧ quadDefect R (algebraMap R F u) = 1 := by
  have h2' := h2.ne_zero
  refine ⟨⟨1, isUnit_one, ?_⟩, ?_⟩
  · rw [map_one]; exact (isSquare_iff_quadDefect_eq_bot h2' _).1 ⟨1, by simp⟩
  · have hring : ringChar (IsLocalRing.ResidueField R) ≠ 2 := by
      intro h
      have hc : CharP (IsLocalRing.ResidueField R) 2 := ringChar.of_eq h
      have h0 := CharP.cast_eq_zero (IsLocalRing.ResidueField R) 2
      rw [Nat.cast_ofNat] at h0
      have : IsLocalRing.residue R 2 = 0 := by rwa [map_ofNat]
      exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).2 h2) this
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hring
    obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective a
    have hu : IsUnit u := (IsLocalRing.residue_ne_zero_iff_isUnit u).1
      (by intro h0; apply ha; rw [h0]; exact ⟨0, by simp⟩)
    refine ⟨u, hu, ?_⟩
    rcases quadDefect_unit_nondyadic (F := F) h2 hu with h | h
    · exfalso
      obtain ⟨η, hη⟩ := (isSquare_iff_quadDefect_eq_bot h2' _).2 h
      obtain ⟨δ, hδ⟩ := exists_alg_of_sq (c := u) (η := η) (by rw [sq, ← hη])
      apply ha
      have hu' : u = δ * δ := alg_inj (F := F) (by rw [map_mul, hδ]; exact hη)
      exact ⟨IsLocalRing.residue R δ, by rw [hu', map_mul]⟩
    · exact h

/-- **Remark 63:6, dyadic case** (O'Meara 1963, p. 162): each ideal of 63:2 occurs as the defect of a unit:
$0$ ($\varepsilon = 1$), $4\mathfrak o$ (Proposition 63:4), and $\mathfrak p^{d}$ for odd $d$ with
$4\mathfrak o \subset \mathfrak p^{d}$ ($\varepsilon = 1 + \pi^{d}$, Proposition 63:5). -/
@[kb "omeara1963" "§63A, 63:6, p. 162 (dyadic: each ideal of 63:2 is a defect)"]
theorem exists_quadDefect_dyadic [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) {π : R} (hπ : Irreducible π) :
    (∃ u : R, IsUnit u ∧ quadDefect R (algebraMap R F u) = ⊥) ∧
      (∃ u : R, IsUnit u ∧ quadDefect R (algebraMap R F u) = span R {(4 : F)}) ∧
      ∀ d : ℕ, Odd d → span R {(4 : F)} < span R {algebraMap R F π ^ d} →
        ∃ u : R, IsUnit u ∧ quadDefect R (algebraMap R F u) = span R {algebraMap R F π ^ d} := by
  have h2z : (2 : IsLocalRing.ResidueField R) = 0 := by
    have : IsLocalRing.residue R 2 = 0 := (IsLocalRing.residue_eq_zero_iff _).2
      (by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using h2p)
    rwa [map_ofNat] at this
  have h4z : (4 : IsLocalRing.ResidueField R) = 0 := by
    rw [show (4 : IsLocalRing.ResidueField R) = 2 * 2 by norm_num, h2z, zero_mul]
  refine ⟨⟨1, isUnit_one, ?_⟩, ?_, ?_⟩
  · rw [map_one]; exact (isSquare_iff_quadDefect_eq_bot h2 _).1 ⟨1, by simp⟩
  · have hns : ∃ z : IsLocalRing.ResidueField R, ∀ y : IsLocalRing.ResidueField R, y ^ 2 + y ≠ z := by
      by_contra hcon
      push Not at hcon
      have hsurj : Function.Surjective (fun y : IsLocalRing.ResidueField R => y ^ 2 + y) := hcon
      have hinj := Finite.injective_iff_surjective.2 hsurj
      have := @hinj 0 1 (by
        show (0 : IsLocalRing.ResidueField R) ^ 2 + 0 = 1 ^ 2 + 1
        linear_combination (-1 : IsLocalRing.ResidueField R) * h2z)
      exact zero_ne_one this
    obtain ⟨z0, hz0⟩ := hns
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective z0
    have hu : IsUnit (1 - 4 * t) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1
      (by rw [map_sub, map_mul, map_one, map_ofNat, h4z]; simp)
    have hnsq : ¬ IsSquare (algebraMap R F (1 - 4 * t)) := by
      rintro ⟨η, hη⟩
      obtain ⟨y, hy⟩ := exists_alg_of_sq (c := 1 - 4 * t) (η := η) (by rw [sq, ← hη])
      have hy2 : y ^ 2 = 1 - 4 * t := alg_inj (F := F) (by rw [map_pow, hy, sq, ← hη])
      obtain ⟨c, hc⟩ := two_dvd_sub_one_of_sq_eq' hπ hy2
      have h4 : (4 : R) * (c ^ 2 + c + t) = 0 := by
        have : y = 1 + 2 * c := by linear_combination hc
        rw [this] at hy2; linear_combination hy2
      have hx := (mul_eq_zero.1 h4).resolve_left (four_ne_zero' h2)
      have := congrArg (IsLocalRing.residue R) hx
      simp only [map_add, map_pow, map_zero] at this
      exact hz0 (IsLocalRing.residue R c) (by linear_combination this - IsLocalRing.residue R t * h2z)
    refine ⟨1 - 4 * t, hu, ?_⟩
    rcases quadDefect_unit_dyadic (F := F) h2 h2p hπ hu with h | h | ⟨d, hd, hlt, hD⟩
    · exact absurd ((isSquare_iff_quadDefect_eq_bot h2 _).2 h) hnsq
    · exact h
    · exfalso
      have hle : quadDefect R (algebraMap R F (1 - 4 * t)) ≤ span R {(4 : F)} := by
        refine (iInf_le _ 1).trans ?_
        rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
        refine ⟨-t, ?_⟩
        rw [Algebra.smul_def]; simp [four_F_eq (R := R) (F := F)]; ring
      rw [hD] at hle
      exact absurd hlt (not_lt_of_ge hle)
  · intro d hd hlt
    have hd0 : d ≠ 0 := by rintro rfl; exact absurd hd (by decide)
    have hres : IsLocalRing.residue R (π ^ d) = 0 := by
      rw [map_pow, (IsLocalRing.residue_eq_zero_iff π).2 (by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hπ.not_isUnit), zero_pow hd0]
    have hu : IsUnit (1 + π ^ d) :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rw [map_add, hres, map_one]; simp)
    refine ⟨1 + π ^ d, hu, ?_⟩
    have := quadDefect_one_add (F := F) h2 hπ (w := 1) isUnit_one hd (by simpa using hlt)
    simpa using this

end QuadFormsKB.OMeara
