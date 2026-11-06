/-
# The conductor of the ramified binary kernel at a dyadic place equals its discriminant exponent

W. T. Gan, J. Hanke, J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), Lemma A.1(iv), p. 123,
and §6, (6.13): for $E/F$ a ramified quadratic extension of local fields, $U^i \subseteq N E^\times$ iff $i \ge d$, where $d$ is
the exponent of the discriminant (of the different) of $E/F$.

Setting (purely local, over a discrete valuation ring $R$ with uniformizer $\pi$): the Eisenstein norm form
$N(a,b) = a^2 + tab + nb^2$ (`nrm`), the norm form of $\mathcal O_E = R[\varpi]$, $\varpi^2 - t\varpi + n = 0$, with $\pi\mid t$,
$n = \pi w$, $w$ a unit; $2 = \pi^e v_2$ with $v_2$ a unit and $e\ge1$; $1 + \pi^{2e+1}R$ consists of squares (local square
theorem, O'Meara 63:1); $\pi^d\,\|\,4n - t^2$ (so $d$ is the discriminant exponent of $\mathcal O_E/R$).

* `disc_cases`: either $\pi^{e+1}\mid t$ and $d = 2e+1$, or $t = \pi^s t'$ with $t'$ a unit, $1\le s\le e$, and $d = 2s$.
* `isNorm_of_pow_dvd` (**every unit $u\equiv1 \bmod \pi^d$ is a norm**): for $d = 2e+1$ by the local square theorem; for
  $d = 2s$ by successive approximation, $N(1, \pi^{m-s}z) = 1 + \pi^m t'z + \pi^{2m-2s+1}wz^2$ for $m\ge2s$.
* `exists_not_isNorm` (**some unit $u\equiv1 \bmod \pi^{d-1}$ is not a norm**): $u = 1 + \pi^{d-1}c$ with $\bar c$ outside the
  image of $\gamma\mapsto A\gamma^2 + B\gamma$ on the residue field ($A, B$ units; the map is not injective, hence not
  surjective). Writing a norm as $a^2(1 + t\beta + n\beta^2)$: if $\beta$ is small the second factor is $1 + \pi^{\mathrm{odd}}\cdot$unit at
  a level where no square is (`sq_sub_one_succ`), and otherwise the level-$(d-1)$ coefficient of $u$ lies in that image.

So the conductor exponent of $F(\sqrt\delta)/F$, $\delta = (t^2 - 4n)/4$, is $d$; the place-level statement is in
`GHYConductorDyadic.lean`. Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.DyadicR2RamNorm

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.R2Ram

open QuadForm LocalDensity LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

section Conductor

/-! ### Divisibility helpers -/

theorem not_pow_dvd_pow_mul_unit (hπ : Irreducible π) {ξ : R} (hξ : IsUnit ξ) {k m : ℕ} (hkm : k < m) :
    ¬ π ^ m ∣ π ^ k * ξ := by
  intro h
  have h' : π ^ k * π ^ (m - k) ∣ π ^ k * ξ := by rwa [← pow_add, Nat.add_sub_cancel' hkm.le]
  have := (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).1 h'
  exact hπ.not_isUnit (isUnit_of_dvd_unit ((dvd_pow_self π (by omega)).trans this) hξ)

theorem dvd_of_pow_succ_dvd_pow_mul (hπ : Irreducible π) {k : ℕ} {y : R} (h : π ^ (k + 1) ∣ π ^ k * y) : π ∣ y := by
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).1 h

theorem isUnit_add_of_dvd (hπ : Irreducible π) {a b : R} (ha : IsUnit a) (hb : π ∣ b) : IsUnit (a + b) :=
  dvr_isUnit_of_not_dvd hπ fun h => dvr_not_dvd_of_isUnit hπ ha (by simpa using dvd_sub h hb)

theorem isUnit_one_add_pow_mul (hπ : Irreducible π) {m : ℕ} (hm : 1 ≤ m) (c : R) : IsUnit (1 + π ^ m * c) :=
  isUnit_add_of_dvd hπ isUnit_one (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _)

/-- The exponent of an exact power is unique. -/
theorem eq_of_exact (hπ : Irreducible π) {X ξ : R} {d k : ℕ} (hd : π ^ d ∣ X) (hd' : ¬ π ^ (d + 1) ∣ X)
    (hX : X = π ^ k * ξ) (hξ : IsUnit ξ) : d = k := by
  rcases lt_trichotomy d k with h | h | h
  · exact absurd ((pow_dvd_pow π (by omega : d + 1 ≤ k)).trans (hX ▸ dvd_mul_right _ _)) hd'
  · exact h
  · exact absurd (hX ▸ hd) (not_pow_dvd_pow_mul_unit hπ hξ h)

/-! ### Squares near $1$ -/

theorem dvd_sub_one_of_dvd_sq_sub_one (hπ : Irreducible π) (h2 : π ∣ 2) {a : R} (h : π ∣ a ^ 2 - 1) : π ∣ a - 1 := by
  have e : (a - 1) ^ 2 = (a ^ 2 - 1) - 2 * (a - 1) := by ring
  have : π ∣ (a - 1) ^ 2 := by rw [e]; exact dvd_sub h (dvd_mul_of_dvd_left h2 _)
  exact hπ.prime.dvd_of_dvd_pow this

/-- $(1 + \pi^k\xi)^2 - 1 = \pi^{2k}\cdot$unit for $\xi$ a unit and $k < e$. -/
theorem sq_sub_one_of_lt (hπ : Irreducible π) {e : ℕ} {v2 : R} (h2e : (2 : R) = π ^ e * v2) {k : ℕ} (hk : k < e)
    {ξ : R} (hξ : IsUnit ξ) : ∃ μ : R, IsUnit μ ∧ (1 + π ^ k * ξ) ^ 2 - 1 = π ^ (2 * k) * μ := by
  refine ⟨ξ ^ 2 + π ^ (e - k) * v2 * ξ, ?_, ?_⟩
  · exact isUnit_add_of_dvd hπ (hξ.pow 2)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _) _)
  · have hp : π ^ e = π ^ k * π ^ (e - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
    rw [show (1 + π ^ k * ξ) ^ 2 - 1 = 2 * (π ^ k * ξ) + (π ^ k * ξ) ^ 2 by ring, h2e, hp]
    ring

/-- **No square is $1 + \pi^{\mathrm{odd}}\cdot$unit below level $2e$:** if $m$ is odd, $m + 1\le 2e$ and
$a^2\equiv1 \bmod \pi^m$, then $a^2\equiv1 \bmod \pi^{m+1}$. -/
theorem sq_sub_one_succ (hπ : Irreducible π) {e : ℕ} {v2 : R} (h2e : (2 : R) = π ^ e * v2) {m : ℕ} (hm : Odd m)
    (hme : m + 1 ≤ 2 * e) {a : R} (h : π ^ m ∣ a ^ 2 - 1) : π ^ (m + 1) ∣ a ^ 2 - 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h2 : π ∣ (2 : R) := by rw [h2e]; exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
  have h1 : π ∣ a - 1 := dvd_sub_one_of_dvd_sq_sub_one hπ h2 ((dvd_pow_self π (by omega)).trans h)
  by_cases hx : π ^ (j + 1) ∣ a - 1
  · obtain ⟨y, hy⟩ := hx
    have ha : a = 1 + π ^ (j + 1) * y := by rw [← hy]; ring
    have hp : π ^ e = π ^ (j + 1) * π ^ (e - (j + 1)) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    refine ⟨y ^ 2 + π ^ (e - (j + 1)) * v2 * y, ?_⟩
    rw [ha, show (1 + π ^ (j + 1) * y) ^ 2 - 1 = 2 * (π ^ (j + 1) * y) + (π ^ (j + 1) * y) ^ 2 by ring, h2e, hp,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
    ring
  · have hx0 : a - 1 ≠ 0 := fun h0 => hx (h0 ▸ dvd_zero _)
    obtain ⟨k, ξ, hkξ, hξ⟩ := dvr_eq_pow_mul_unit hπ hx0
    have hk : k < j + 1 := by
      by_contra hk
      exact hx (hkξ ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)
    obtain ⟨μ, hμ, he⟩ := sq_sub_one_of_lt hπ h2e (by omega : k < e) hξ
    have ha : a = 1 + π ^ k * ξ := by rw [← hkξ]; ring
    rw [ha, he] at h
    exact absurd h (not_pow_dvd_pow_mul_unit hπ hμ (by omega))

/-- **Squares at level $2e$:** if $a^2\equiv1 \bmod \pi^{2e}$ then $a^2\equiv1 + \pi^{2e}(\gamma^2 + v_2\gamma) \bmod \pi^{2e+1}$. -/
theorem sq_sub_one_two_e (hπ : Irreducible π) {e : ℕ} {v2 : R} (h2e : (2 : R) = π ^ e * v2) (he : 1 ≤ e) {a : R}
    (h : π ^ (2 * e) ∣ a ^ 2 - 1) : ∃ γ : R, π ^ (2 * e + 1) ∣ a ^ 2 - 1 - π ^ (2 * e) * (γ ^ 2 + v2 * γ) := by
  have h2 : π ∣ (2 : R) := by rw [h2e]; exact dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
  by_cases hx : π ^ e ∣ a - 1
  · obtain ⟨γ, hγ⟩ := hx
    have ha : a = 1 + π ^ e * γ := by rw [← hγ]; ring
    refine ⟨γ, ⟨0, ?_⟩⟩
    rw [ha]; linear_combination (π ^ e * γ) * h2e
  · have hx0 : a - 1 ≠ 0 := fun h0 => hx (h0 ▸ dvd_zero _)
    obtain ⟨k, ξ, hkξ, hξ⟩ := dvr_eq_pow_mul_unit hπ hx0
    have hk : k < e := by
      by_contra hk
      exact hx (hkξ ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)
    obtain ⟨μ, hμ, he'⟩ := sq_sub_one_of_lt hπ h2e hk hξ
    have ha : a = 1 + π ^ k * ξ := by rw [← hkξ]; ring
    rw [ha, he'] at h
    exact absurd h (not_pow_dvd_pow_mul_unit hπ hμ (by omega))

/-! ### The norm form near $1$ -/

theorem isUnit_fst_of_nrm (hπ : Irreducible π) {t n a b u : R} (ht : π ∣ t) (hn : π ∣ n) (hu : IsUnit u)
    (h : nrm t n a b = u) : IsUnit a := by
  refine dvr_isUnit_of_not_dvd hπ fun ha => dvr_not_dvd_of_isUnit hπ hu ?_
  rw [← h, nrm]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left ht _)) (dvd_mul_of_dvd_left hn _)

theorem nrm_eq_sq_mul {t n a b ai : R} (hai : a * ai = 1) :
    nrm t n a b = a ^ 2 * (1 + t * (b * ai) + n * (b * ai) ^ 2) := by
  unfold nrm
  linear_combination (-(a * b * t) - b ^ 2 * n - a * ai * b ^ 2 * n) * hai

/-- **The odd-level obstruction:** $u = a^2M$ with $M = 1 + \pi^m\mu$ ($\mu$ a unit, $m$ odd, $m + 1\le2e$) is not
$\equiv1 \bmod \pi^{m+1}$. -/
theorem not_odd_level (hπ : Irreducible π) {e : ℕ} {v2 : R} (h2e : (2 : R) = π ^ e * v2) {m : ℕ} (hm : Odd m)
    (hme : m + 1 ≤ 2 * e) {a M μ u : R} (hμ : IsUnit μ) (hM : M - 1 = π ^ m * μ) (hu : u = a ^ 2 * M)
    (hu1 : π ^ (m + 1) ∣ u - 1) : False := by
  have hm1 : 1 ≤ m := by obtain ⟨j, rfl⟩ := hm; omega
  have hMu : IsUnit M := by
    have := isUnit_one_add_pow_mul hπ hm1 μ
    rwa [← hM, add_sub_cancel] at this
  have e1 : u - 1 = (a ^ 2 - 1) * M + (M - 1) := by rw [hu]; ring
  have h1 : π ^ m ∣ (a ^ 2 - 1) * M := by
    have := dvd_sub ((pow_dvd_pow π (Nat.le_succ m)).trans hu1) (hM ▸ dvd_mul_right (π ^ m) μ : π ^ m ∣ M - 1)
    rwa [e1, add_sub_cancel_right] at this
  have h2 := sq_sub_one_succ hπ h2e hm hme ((hMu.dvd_mul_right).1 h1)
  have h3 : π ^ (m + 1) ∣ M - 1 := by
    have := dvd_sub hu1 (dvd_mul_of_dvd_left h2 M)
    rwa [e1, add_sub_cancel_left] at this
  rw [hM] at h3
  exact not_pow_dvd_pow_mul_unit hπ hμ (Nat.lt_succ_self m) h3

/-! ### The two shapes of the discriminant -/

/-- **The discriminant exponent:** either $\pi^{e+1}\mid t$ and $4n - t^2 = \pi^{2e+1}\cdot$unit, or $t = \pi^st'$ with $t'$ a unit,
$1\le s\le e$, and $4n - t^2 = \pi^{2s}\cdot$unit. -/
theorem disc_cases (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w)
    {e : ℕ} {v2 : R} (hv2 : IsUnit v2) (h2e : (2 : R) = π ^ e * v2) :
    (∃ t₁ μ : R, t = π ^ (e + 1) * t₁ ∧ IsUnit μ ∧ 4 * n - t ^ 2 = π ^ (2 * e + 1) * μ) ∨
    (∃ (s : ℕ) (t' μ : R), 1 ≤ s ∧ s ≤ e ∧ IsUnit t' ∧ t = π ^ s * t' ∧ IsUnit μ ∧
      4 * n - t ^ 2 = π ^ (2 * s) * μ) := by
  have h4 : (4 : R) = π ^ (2 * e) * v2 ^ 2 := by
    rw [show (4 : R) = 2 * 2 by norm_num, h2e]; ring
  by_cases h : π ^ (e + 1) ∣ t
  · obtain ⟨t₁, rfl⟩ := h
    refine Or.inl ⟨t₁, v2 ^ 2 * w + π * (-t₁ ^ 2), rfl, isUnit_add_of_dvd hπ ((hv2.pow 2).mul hw) (dvd_mul_right _ _), ?_⟩
    rw [hn, h4]; ring
  · have ht0 : t ≠ 0 := fun h0 => h (h0 ▸ dvd_zero _)
    obtain ⟨s, t', hst, ht'⟩ := dvr_eq_pow_mul_unit hπ ht0
    have hs1 : 1 ≤ s := by
      by_contra hs
      have : s = 0 := by omega
      subst this
      rw [pow_zero, one_mul] at hst
      exact dvr_not_dvd_of_isUnit hπ ht' (hst ▸ ht)
    have hse : s ≤ e := by
      by_contra hs
      exact h (hst ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)
    refine Or.inr ⟨s, t', -t' ^ 2 + π * (π ^ (2 * e - 2 * s) * v2 ^ 2 * w), hs1, hse, ht', hst,
      isUnit_add_of_dvd hπ (ht'.pow 2).neg (dvd_mul_right _ _), ?_⟩
    have hp : π ^ (2 * e) = π ^ (2 * s) * π ^ (2 * e - 2 * s) := by
      rw [← pow_add, Nat.add_sub_cancel' (by omega)]
    rw [hn, h4, hst, hp]; ring

/-! ### Units $\equiv 1 \bmod \pi^d$ are norms -/

variable {t n w : R} {e : ℕ} {v2 : R} {d : ℕ}

/-- **Every unit $u\equiv1 \bmod \pi^d$ is a norm** from $\mathcal O_E$ ($\pi^d\,\|\,4n - t^2$; GHY 2001, Lemma A.1(iv),
$U^d\subseteq NE^\times$). -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (U^i ⊆ N E^× for i ≥ d, E ramified dyadic)"]
theorem isNorm_of_pow_dvd (hπ : Irreducible π) (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w)
    (hv2 : IsUnit v2) (h2e : (2 : R) = π ^ e * v2) (hsq : ∀ x : R, π ^ (2 * e + 1) ∣ x - 1 → IsSquare x)
    (hd : π ^ d ∣ 4 * n - t ^ 2) (hd' : ¬ π ^ (d + 1) ∣ 4 * n - t ^ 2)
    {u : R} (hu : IsUnit u) (hud : π ^ d ∣ u - 1) : ∃ a b, nrm t n a b = u := by
  have sqn : ∀ x : R, IsSquare x → ∃ a b, nrm t n a b = x := by
    rintro x ⟨r, rfl⟩
    exact ⟨r, 0, by simp [nrm]⟩
  rcases disc_cases hπ ht hn hw hv2 h2e with ⟨t₁, μ, -, hμ, hX⟩ | ⟨s, t', μ, hs1, hse, ht', hst, hμ, hX⟩
  · obtain rfl := eq_of_exact hπ hd hd' hX hμ
    exact sqn u (hsq u hud)
  · obtain rfl := eq_of_exact hπ hd hd' hX hμ
    obtain ⟨ti, hti⟩ := ht'.exists_right_inv
    -- descending induction on the level `m = 2e + 1 - j`
    have step : ∀ j : ℕ, ∀ u : R, IsUnit u → π ^ (2 * e + 1 - j) ∣ u - 1 → 2 * s ≤ 2 * e + 1 - j →
        ∃ a b, nrm t n a b = u := by
      intro j
      induction j with
      | zero => intro u _ hu1 _; exact sqn u (hsq u hu1)
      | succ j ih =>
        intro u hu hu1 hle
        set m := 2 * e + 1 - (j + 1) with hm
        obtain ⟨c, hc⟩ := hu1
        set z := c * ti
        set b := π ^ (m - s) * z
        set N0 := nrm t n 1 b
        have hN0 : u - N0 = π ^ (m + 1) * (-(π ^ (m - 2 * s) * w * z ^ 2)) := by
          have hp1 : π ^ m = π ^ s * π ^ (m - s) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
          have hp2 : π ^ (m + 1) * π ^ (m - 2 * s) = π * (π ^ (m - s)) ^ 2 := by
            rw [← pow_mul, ← pow_succ', ← pow_add]; congr 1; omega
          have hu' : u = 1 + π ^ m * c := by rw [← hc]; ring
          have htz : t * b = π ^ m * c := by
            simp only [b, z]; rw [hst, hp1]; linear_combination (π ^ s * π ^ (m - s) * c) * hti
          simp only [N0, nrm]
          rw [hu', hn]
          linear_combination -htz + (w * z ^ 2) * hp2
        have hN0u : IsUnit N0 := by
          have := isUnit_add_of_dvd hπ hu (dvd_neg.2 (hN0 ▸ dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _))
          rwa [neg_sub, add_sub_cancel] at this
        obtain ⟨Ni, hNi⟩ := hN0u.exists_right_inv
        have hu'u : IsUnit (u * Ni) := hu.mul (IsUnit.of_mul_eq_one N0 (by rw [mul_comm]; exact hNi))
        have h1 : π ^ (2 * e + 1 - j) ∣ u * Ni - 1 := by
          have e1 : u * Ni - 1 = (u - N0) * Ni := by linear_combination hNi
          rw [e1, hN0, show 2 * e + 1 - j = m + 1 by omega]
          exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
        have hprod := isNorm_mul (ih (u * Ni) hu'u h1 (by omega)) ⟨1, b, rfl⟩
        rwa [mul_assoc, mul_comm Ni N0, hNi, mul_one] at hprod
    exact step (2 * e + 1 - 2 * s) u hu (by rwa [show 2 * e + 1 - (2 * e + 1 - 2 * s) = 2 * s by omega])
      (by omega)

/-! ### A unit $\equiv 1 \bmod \pi^{d-1}$ that is not a norm -/

/-- The map $\gamma\mapsto A\gamma^2 + B\gamma$ ($A$, $B$ units) is not surjective mod $\pi$. -/
theorem exists_not_quad_mod [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) {A B : R} (hA : IsUnit A)
    (hB : IsUnit B) : ∃ c : R, ∀ γ : R, ¬ π ∣ c - (A * γ ^ 2 + B * γ) := by
  set k := IsLocalRing.ResidueField R
  set r := IsLocalRing.residue R
  have hres : ∀ x : R, r x = 0 ↔ π ∣ x := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ,
      Ideal.mem_span_singleton]
  have hA0 : r A ≠ 0 := (hA.map r).ne_zero
  have hB0 : r B ≠ 0 := (hB.map r).ne_zero
  let f : k → k := fun y => r A * y ^ 2 + r B * y
  have hni : ¬ Function.Injective f := by
    intro hf
    have h := @hf 0 (-(r B / r A)) (by simp only [f]; field_simp; ring)
    exact (neg_ne_zero.2 (div_ne_zero hB0 hA0)) h.symm
  have hns : ¬ Function.Surjective f := fun hs => hni (Finite.injective_iff_surjective.2 hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨c0, hc0⟩ := hns
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective c0
  refine ⟨c, fun γ hγ => hc0 (r γ) ?_⟩
  have := (hres _).2 hγ
  simp only [map_sub, map_add, map_mul, map_pow, sub_eq_zero] at this
  exact this.symm

/-- **Some unit $u\equiv1 \bmod \pi^{d-1}$ is not a norm** from $\mathcal O_E$ (GHY 2001, Lemma A.1(iv): $U^i\subseteq NE^\times$
only for $i\ge d$). -/
@[kb "ganhankeyu2001" "Lemma A.1(iv), p. 123 (U^{d-1} ⊄ N E^×, E ramified dyadic)"]
theorem exists_not_isNorm [Finite (IsLocalRing.ResidueField R)] (hπ : Irreducible π) (ht : π ∣ t) (hn : n = π * w)
    (hw : IsUnit w) (hv2 : IsUnit v2) (h2e : (2 : R) = π ^ e * v2) (he : 1 ≤ e)
    (hd : π ^ d ∣ 4 * n - t ^ 2) (hd' : ¬ π ^ (d + 1) ∣ 4 * n - t ^ 2) :
    ∃ u : R, IsUnit u ∧ π ^ (d - 1) ∣ u - 1 ∧ ¬ ∃ a b, nrm t n a b = u := by
  have hπn : π ∣ n := hn ▸ dvd_mul_right _ _
  -- the common reduction: a norm `u` is `a² M` with `M = 1 + tβ + nβ²`
  have red : ∀ u : R, IsUnit u → (∃ a b, nrm t n a b = u) →
      ∃ a β : R, u = a ^ 2 * (1 + t * β + n * β ^ 2) := by
    rintro u hu ⟨a, b, hab⟩
    obtain ⟨ai, hai⟩ := (isUnit_fst_of_nrm hπ ht hπn hu hab).exists_right_inv
    exact ⟨a, b * ai, by rw [← hab, nrm_eq_sq_mul hai]⟩
  rcases disc_cases hπ ht hn hw hv2 h2e with ⟨t₁, μ, ht₁, hμ, hX⟩ | ⟨s, t', μ, hs1, hse, ht', hst, hμ, hX⟩
  · obtain rfl := eq_of_exact hπ hd hd' hX hμ
    obtain ⟨c, hc⟩ := exists_not_quad_mod hπ isUnit_one hv2
    refine ⟨1 + π ^ (2 * e) * c, isUnit_one_add_pow_mul hπ (by omega) c, ⟨c, by simp⟩, fun hN => ?_⟩
    obtain ⟨a, β, hu⟩ := red _ (isUnit_one_add_pow_mul hπ (by omega) c) hN
    set u := 1 + π ^ (2 * e) * c
    by_cases hβ : π ^ e ∣ β
    · obtain ⟨γ, rfl⟩ := hβ
      have hM : t * (π ^ e * γ) + n * (π ^ e * γ) ^ 2 = π ^ (2 * e + 1) * (t₁ * γ + w * γ ^ 2) := by
        rw [ht₁, hn]; ring
      have e1 : u - 1 = (a ^ 2 - 1) + a ^ 2 * (π ^ (2 * e + 1) * (t₁ * γ + w * γ ^ 2)) := by
        rw [hu, add_assoc, hM]; ring
      have ha : π ^ (2 * e) ∣ a ^ 2 - 1 := by
        have h0 : π ^ (2 * e) ∣ u - 1 := ⟨c, by simp [u]⟩
        rw [e1] at h0
        have := dvd_sub h0 (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow π (Nat.le_succ _)) (t₁ * γ + w * γ ^ 2)) (a ^ 2))
        rwa [add_sub_cancel_right] at this
      obtain ⟨γ', hγ'⟩ := sq_sub_one_two_e hπ h2e he ha
      apply hc γ'
      apply dvd_of_pow_succ_dvd_pow_mul hπ (k := 2 * e)
      have e2 : π ^ (2 * e) * (c - (1 * γ' ^ 2 + v2 * γ')) =
          (a ^ 2 - 1 - π ^ (2 * e) * (γ' ^ 2 + v2 * γ')) + a ^ 2 * (π ^ (2 * e + 1) * (t₁ * γ + w * γ ^ 2)) := by
        have : π ^ (2 * e) * c = u - 1 := by simp [u]
        rw [mul_sub, this, e1]; ring
      rw [e2]
      exact dvd_add hγ' (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
    · have hβ0 : β ≠ 0 := fun h0 => hβ (h0 ▸ dvd_zero _)
      obtain ⟨j, ξ, hjξ, hξ⟩ := dvr_eq_pow_mul_unit hπ hβ0
      have hj : j < e := by
        by_contra hj
        exact hβ (hjξ ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)
      have hM : 1 + t * β + n * β ^ 2 - 1 = π ^ (2 * j + 1) * (w * ξ ^ 2 + π * (π ^ (e - j - 1) * t₁ * ξ)) := by
        have hp : π ^ (e + 1) * π ^ j = π ^ (2 * j + 1) * (π * π ^ (e - j - 1)) := by
          rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega
        rw [hjξ, ht₁, hn]
        linear_combination (t₁ * ξ) * hp
      exact not_odd_level hπ h2e ⟨j, rfl⟩ (by omega)
        (isUnit_add_of_dvd hπ (hw.mul (hξ.pow 2)) (dvd_mul_right _ _)) hM hu
        ((pow_dvd_pow π (by omega : 2 * j + 1 + 1 ≤ 2 * e)).trans ⟨c, by simp [u]⟩)
  · obtain rfl := eq_of_exact hπ hd hd' hX hμ
    obtain ⟨c, hc⟩ := exists_not_quad_mod hπ hw ht'
    have hlev : 1 ≤ 2 * s - 1 := by omega
    refine ⟨1 + π ^ (2 * s - 1) * c, isUnit_one_add_pow_mul hπ hlev c, ⟨c, by simp⟩, fun hN => ?_⟩
    obtain ⟨a, β, hu⟩ := red _ (isUnit_one_add_pow_mul hπ hlev c) hN
    set u := 1 + π ^ (2 * s - 1) * c
    by_cases hβ : π ^ (s - 1) ∣ β
    · obtain ⟨γ, rfl⟩ := hβ
      set M := 1 + t * (π ^ (s - 1) * γ) + n * (π ^ (s - 1) * γ) ^ 2
      have hM : M - 1 = π ^ (2 * s - 1) * (w * γ ^ 2 + t' * γ) := by
        have hp1 : π ^ s * π ^ (s - 1) = π ^ (2 * s - 1) := by rw [← pow_add]; congr 1; omega
        have hp2 : π * (π ^ (s - 1)) ^ 2 = π ^ (2 * s - 1) := by rw [← pow_mul, ← pow_succ']; congr 1; omega
        simp only [M]
        rw [hst, hn]
        linear_combination (t' * γ) * hp1 + (w * γ ^ 2) * hp2
      have e1 : u - 1 = (a ^ 2 - 1) * M + (M - 1) := by rw [hu]; ring
      have hMu : IsUnit M := by
        have := isUnit_one_add_pow_mul hπ hlev (w * γ ^ 2 + t' * γ)
        rwa [← hM, add_sub_cancel] at this
      have ha : π ^ (2 * s - 1) ∣ a ^ 2 - 1 := by
        have h0 : π ^ (2 * s - 1) ∣ u - 1 := ⟨c, by simp [u]⟩
        rw [e1] at h0
        have := dvd_sub h0 (hM ▸ dvd_mul_right _ _ : π ^ (2 * s - 1) ∣ M - 1)
        rw [add_sub_cancel_right] at this
        exact hMu.dvd_mul_right.1 this
      have ha' := sq_sub_one_succ hπ h2e ⟨s - 1, by omega⟩ (by omega) ha
      rw [show 2 * s - 1 + 1 = 2 * s by omega] at ha'
      apply hc γ
      apply dvd_of_pow_succ_dvd_pow_mul hπ (k := 2 * s - 1)
      have e2 : π ^ (2 * s - 1) * (c - (w * γ ^ 2 + t' * γ)) = (a ^ 2 - 1) * M := by
        have : π ^ (2 * s - 1) * c = u - 1 := by simp [u]
        rw [mul_sub, this, ← hM, e1]; ring
      rw [e2, show 2 * s - 1 + 1 = 2 * s by omega]
      exact dvd_mul_of_dvd_left ha' _
    · have hβ0 : β ≠ 0 := fun h0 => hβ (h0 ▸ dvd_zero _)
      obtain ⟨j, ξ, hjξ, hξ⟩ := dvr_eq_pow_mul_unit hπ hβ0
      have hj : j + 1 < s := by
        by_contra hj
        exact hβ (hjξ ▸ dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)
      have hM : 1 + t * β + n * β ^ 2 - 1 = π ^ (2 * j + 1) * (w * ξ ^ 2 + π * (π ^ (s - j - 2) * t' * ξ)) := by
        have hp : π ^ s * π ^ j = π ^ (2 * j + 1) * (π * π ^ (s - j - 2)) := by
          rw [← pow_succ', ← pow_add, ← pow_add]; congr 1; omega
        rw [hjξ, hst, hn]
        linear_combination (t' * ξ) * hp
      exact not_odd_level hπ h2e ⟨j, rfl⟩ (by omega)
        (isUnit_add_of_dvd hπ (hw.mul (hξ.pow 2)) (dvd_mul_right _ _)) hM hu
        ((pow_dvd_pow π (by omega : 2 * j + 1 + 1 ≤ 2 * s - 1)).trans ⟨c, by simp [u]⟩)

end Conductor

end QuadFormsKB.Hanke2005.R2Ram
