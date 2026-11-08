/-
# The ramified binary kernel at a dyadic place: norms and ramification

For the Eisenstein norm form $N(a,b) = a^2 + tab + nb^2$ over a discrete valuation ring $R$ with fraction field $K$
($\pi\mid t$, $n = \pi w$, $w$ a unit), put $\delta = (t^2 - 4n)/4 \in K$, so that $N(a,b) = (a + tb/2)^2 - \delta b^2$.

* `integral_of_nrm`: $N(a,b) \in R$ with $a, b \in K$ forces $a, b \in R$ (the lattice is maximal);
* `nrm_eq_zero_iff`, `not_isSquare_delta`: $N$ is anisotropic over $K$, so $\delta \notin K^{\times2}$;
* `isNorm_iff_hilbert`: a unit $u$ is a value of $N$ on $R^2$ iff $(u, \delta)_K = 1$;
* `indexTwo_of_hilbert`: from multiplicativity and nondegeneracy of $(\cdot,\delta)_K$, the unit norms have index $2$
  (`IndexTwo`);
* `not_unram_delta` (complete $R$, $\pi \mid 2$): $\delta$ is not of the form $(1 + 4y)/c^2$ with $1 + 4y$ a unit, i.e. $K(\sqrt\delta)/K$
  is ramified: the nonzero values of $X^2 - (1+4y)Y^2$ have even valuation (Hensel, `isSquare_one_sub_four_mul_iff`), while
  $N(0, 1) = n$ has valuation $1$.

Sources: O'Meara 1963, §63B (63:3, 63:4, 63:10, 63:11a); Gan–Hanke–Yu 2001, §6. Indices are 0-based.
-/
import QuadFormsKB.Literature.Hanke2005.DyadicR2RamLevel

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005.R2Ram

open QuadForm LocalDensity LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "ι" => algebraMap R K

theorem ι_inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

/-- Every element of $K$ becomes integral after multiplication by a power of $\pi$. -/
theorem exists_pow_mul_eq (hπ : Irreducible π) (x : K) : ∃ m : ℕ, ∃ A : R, ι (π ^ m) * x = ι A := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  refine ⟨m, a * ↑u⁻¹, ?_⟩
  have hu : ι (u : R) ≠ 0 := (map_ne_zero_iff _ (ι_inj (K := K))).2 u.ne_zero
  have hπm : ι (π ^ m) ≠ 0 := (map_ne_zero_iff _ (ι_inj (K := K))).2 (pow_ne_zero _ hπ.ne_zero)
  have : ι (↑u⁻¹ : R) = (ι (u : R))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [map_mul (algebraMap R K) a, this, map_mul (algebraMap R K) (u : R)]
  field_simp

/-- Two elements with a common power of $\pi$ clearing denominators. -/
theorem exists_pow_mul_eq₂ (hπ : Irreducible π) (x y : K) :
    ∃ m : ℕ, ∃ A B : R, ι (π ^ m) * x = ι A ∧ ι (π ^ m) * y = ι B := by
  obtain ⟨m₁, A, hA⟩ := exists_pow_mul_eq hπ x
  obtain ⟨m₂, B, hB⟩ := exists_pow_mul_eq hπ y
  refine ⟨m₁ + m₂, π ^ m₂ * A, π ^ m₁ * B, ?_, ?_⟩
  · rw [pow_add, mul_comm (π ^ m₁), map_mul, mul_assoc, hA, map_mul]
  · rw [pow_add, map_mul, mul_assoc, hB, map_mul]

theorem nrm_map (t n a b : R) : nrm (ι t) (ι n) (ι a) (ι b) = ι (nrm t n a b) := by
  simp [nrm]

theorem eq_zero_of_forall_pow_dvd (hπ : Irreducible π) {x : R} (h : ∀ j : ℕ, π ^ j ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have := h (j + 1)
  rw [pow_succ, mul_comm (u : R)] at this
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 this
  exact hπ.not_isUnit (isUnit_of_dvd_unit h2 u.isUnit)

/-- $\delta = (t^2 - 4n)/4$. -/
def delta (t n : R) : K := ((ι t) ^ 2 - 4 * ι n) / 4

theorem hilbertSymbol_eq_one_iff {a b : K} :
    hilbertSymbol K a b = 1 ↔ ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2 := by
  unfold hilbertSymbol
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => by norm_num at h', fun h' => absurd h' h⟩

theorem hilbertSymbol_eq_one_or_neg (a b : K) : hilbertSymbol K a b = 1 ∨ hilbertSymbol K a b = -1 := by
  unfold hilbertSymbol; split_ifs <;> simp

section Norms

variable (hπ : Irreducible π) {t n w : R} (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w)
include hπ ht hn hw

/-- **The lattice $R^2$ is maximal for $N$:** $N(a, b) \in R$ with $a, b\in K$ gives $a, b\in R$. -/
theorem integral_of_nrm {a b : K} {r : R} (h : nrm (ι t) (ι n) a b = ι r) : ∃ a' b' : R, a = ι a' ∧ b = ι b' := by
  obtain ⟨m, A, B, hA, hB⟩ := exists_pow_mul_eq₂ hπ a b
  have hπm : ι (π ^ m) ≠ 0 := (map_ne_zero_iff _ (ι_inj (K := K))).2 (pow_ne_zero _ hπ.ne_zero)
  have e : nrm t n A B = π ^ (2 * m) * r := by
    apply (ι_inj (K := K))
    rw [← nrm_map, ← hA, ← hB, nrm_smul, h, ← map_pow, ← map_mul, ← pow_mul, mul_comm m 2]
  have hdvd : π ^ (2 * m) ∣ nrm t n A B := ⟨r, e⟩
  rw [pow_dvd_nrm_iff hπ ht hn hw, show (2 * m + 1) / 2 = m by omega, show 2 * m / 2 = m by omega] at hdvd
  obtain ⟨⟨A', rfl⟩, ⟨B', rfl⟩⟩ := hdvd
  refine ⟨A', B', ?_, ?_⟩
  · apply mul_left_cancel₀ hπm; rw [hA, map_mul]
  · apply mul_left_cancel₀ hπm; rw [hB, map_mul]

/-- **$N$ is anisotropic over $K$.** -/
theorem nrm_eq_zero_iff {a b : K} : nrm (ι t) (ι n) a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    obtain ⟨a', b', rfl, rfl⟩ := integral_of_nrm (K := K) hπ ht hn hw (r := 0) (by rw [h, map_zero])
    have h0 : nrm t n a' b' = 0 := (ι_inj (K := K)) (by rw [← nrm_map, h, map_zero])
    have hall : ∀ j, π ^ j ∣ a' ∧ π ^ j ∣ b' := fun j => by
      have := (pow_dvd_nrm_iff hπ ht hn hw (2 * j) a' b').1 (by rw [h0]; exact dvd_zero _)
      rwa [show (2 * j + 1) / 2 = j by omega, show 2 * j / 2 = j by omega] at this
    rw [eq_zero_of_forall_pow_dvd hπ fun j => (hall j).1,
      eq_zero_of_forall_pow_dvd hπ fun j => (hall j).2]
    simp
  · rintro ⟨rfl, rfl⟩; simp [nrm]

theorem nrm_eq_sq_sub (h2 : (2 : K) ≠ 0) (a b : K) :
    nrm (ι t) (ι n) a b = (a + ι t * b / 2) ^ 2 - delta t n * b ^ 2 := by
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  unfold nrm delta; field_simp; ring

/-- **$\delta$ is not a square in $K$.** -/
theorem not_isSquare_delta (h2 : (2 : K) ≠ 0) : ¬ IsSquare (delta (K := K) t n) := by
  rintro ⟨s, hs⟩
  have := (nrm_eq_zero_iff (K := K) hπ ht hn hw (a := s - ι t / 2) (b := 1)).1 (by
    rw [nrm_eq_sq_sub hπ ht hn hw h2, hs]; ring)
  exact one_ne_zero this.2

theorem delta_ne_zero (h2 : (2 : K) ≠ 0) : delta (K := K) t n ≠ 0 := fun h =>
  not_isSquare_delta hπ ht hn hw h2 ⟨0, by rw [h]; ring⟩

/-- **Norms are Hilbert-symbol trivial:** for $u \ne 0$ in $R$, $u = N(a, b)$ with $a, b \in R$ iff $(u, \delta)_K = 1$. -/
theorem isNorm_iff_hilbert (h2 : (2 : K) ≠ 0) {u : R} (hu : u ≠ 0) :
    (∃ a b : R, nrm t n a b = u) ↔ hilbertSymbol K (ι u) (delta t n) = 1 := by
  rw [hilbertSymbol_eq_one_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨1, ι b, ι a + ι t * ι b / 2, by simp, ?_⟩
    rw [← nrm_map, nrm_eq_sq_sub hπ ht hn hw h2]; ring
  · rintro ⟨x, y, z, hne, hz⟩
    by_cases hx : x = 0
    · exfalso
      subst hx
      have hy : y ≠ 0 := by
        rintro rfl
        apply hne
        have : z ^ 2 = 0 := by rw [hz]; ring
        simp [pow_eq_zero_iff (two_ne_zero) |>.1 this]
      exact not_isSquare_delta hπ ht hn hw h2 ⟨z / y, by field_simp; rw [hz]; ring⟩
    · have hval : nrm (ι t) (ι n) (z / x - ι t * (y / x) / 2) (y / x) = ι u := by
        rw [nrm_eq_sq_sub hπ ht hn hw h2, show z / x - ι t * (y / x) / 2 + ι t * (y / x) / 2 = z / x by ring,
          div_pow, div_pow, hz]
        field_simp; ring
      obtain ⟨a', b', ha, hb⟩ := integral_of_nrm (K := K) hπ ht hn hw hval
      refine ⟨a', b', (ι_inj (K := K)) ?_⟩
      rw [← nrm_map, ← ha, ← hb, hval]

/-- **Index two from the Hilbert symbol:** if $(\cdot, \delta)_K$ is multiplicative and nontrivial, the unit norms have index
$2$ in the units of $R$. -/
theorem indexTwo_of_hilbert (h2 : (2 : K) ≠ 0)
    (hmul : ∀ a b : K, a ≠ 0 → b ≠ 0 →
      hilbertSymbol K (a * b) (delta t n) = hilbertSymbol K a (delta t n) * hilbertSymbol K b (delta t n))
    (hsq : ∀ a c : K, a ≠ 0 → c ≠ 0 → hilbertSymbol K (a * c ^ 2) (delta t n) = hilbertSymbol K a (delta t n))
    (hnd : ∃ x : K, x ≠ 0 ∧ hilbertSymbol K x (delta t n) = -1) : IndexTwo t n := by
  have hι0 : ∀ {r : R}, r ≠ 0 → ι r ≠ 0 := fun h => (map_ne_zero_iff _ (ι_inj (K := K))).2 h
  have hn0 : n ≠ 0 := by rw [hn]; exact mul_ne_zero hπ.ne_zero hw.ne_zero
  have hnorm_n : hilbertSymbol K (ι n) (delta t n) = 1 :=
    (isNorm_iff_hilbert hπ ht hn hw h2 hn0).1 ⟨0, 1, by simp [nrm]⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx0, hx⟩ := hnd
    obtain ⟨m, A, hA⟩ := exists_pow_mul_eq hπ x
    have hA0 : A ≠ 0 := by
      rintro rfl
      rw [map_zero] at hA
      exact mul_ne_zero (hι0 (pow_ne_zero m hπ.ne_zero)) hx0 hA
    -- `(A, δ) = (π^m x, δ)`, and `A = n^j u` up to the norm `n^j`
    obtain ⟨j, u, hAu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hA0 hπ
    -- the symbol of `π^j` equals that of `w^{-j}` (since `n = π w` is a norm)
    have key : ∀ j : ℕ, ∀ u : Rˣ, hilbertSymbol K (ι (u * π ^ j)) (delta t n) =
        hilbertSymbol K (ι (u * (↑hw.unit⁻¹ : R) ^ j)) (delta t n) := by
      intro j
      induction j with
      | zero => intro u; simp
      | succ j ih =>
        intro u
        have e1 : ι ((u : R) * π ^ (j + 1)) = ι ((u * hw.unit⁻¹ : Rˣ) * π ^ j) * ι n := by
          rw [← map_mul]; congr 1; rw [hn]; push_cast
          have hw1 : (↑hw.unit⁻¹ : R) * w = 1 := hw.val_inv_mul
          linear_combination (-((u : R) * π ^ (j + 1))) * hw1
        rw [e1, hmul _ _ (hι0 (mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ hπ.ne_zero))) (hι0 hn0), hnorm_n,
          mul_one, ih]
        congr 2; push_cast; ring
    have h1 : hilbertSymbol K (ι (A * π ^ m)) (delta t n) = -1 := by
      have e : ι (A * π ^ m) = x * (ι (π ^ m)) ^ 2 := by rw [map_mul, ← hA]; ring
      rw [e, hsq _ _ hx0 (hι0 (pow_ne_zero m hπ.ne_zero)), hx]
    rw [hAu, mul_assoc, ← pow_add, key] at h1
    have hu0 : IsUnit ((u : R) * (↑hw.unit⁻¹ : R) ^ (j + m)) := u.isUnit.mul (Units.isUnit _ |>.pow _)
    refine ⟨_, hu0, fun h => ?_⟩
    rw [isNorm_iff_hilbert hπ ht hn hw h2 hu0.ne_zero, h1] at h
    norm_num at h
  · intro u u' hu hu' hnu hnu'
    have hu0 := hu.ne_zero
    have hu0' := hu'.ne_zero
    rw [isNorm_iff_hilbert hπ ht hn hw h2 hu0] at hnu
    rw [isNorm_iff_hilbert hπ ht hn hw h2 hu0'] at hnu'
    rw [isNorm_iff_hilbert hπ ht hn hw h2 (mul_ne_zero hu0 hu0'), map_mul, hmul _ _ (hι0 hu0) (hι0 hu0'),
      (hilbertSymbol_eq_one_or_neg _ _).resolve_left hnu, (hilbertSymbol_eq_one_or_neg _ _).resolve_left hnu']
    norm_num

end Norms

/-- The form $f(a,b) = a^2 + ab - yb^2$ (norm form of $R[(1+\sqrt{1+4y})/2]$). -/
def asNrm (y a b : R) : R := a * a + a * b - y * (b * b)

/-- **$f$ is anisotropic mod $\pi$ when $1 + 4y$ is not a square** (complete $R$, $\pi \mid 2$): a root of
$X^2 + X - y$ mod $\pi$ would lift (Hensel) and make $1 + 4y$ a square. -/
theorem dvd_of_dvd_asNrm [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (hπ : Irreducible π) (h2π : π ∣ 2)
    (h20 : (2 : R) ≠ 0) {y : R} (hy : ¬ IsSquare (1 + 4 * y)) {a b : R} (h : π ∣ asNrm y a b) :
    π ∣ a ∧ π ∣ b := by
  have := charP_residueField_two hπ h2π
  by_cases hb : π ∣ b
  · refine ⟨?_, hb⟩
    have e : a * a = asNrm y a b - b * (a - y * b) := by unfold asNrm; ring
    have : π ∣ a * a := by rw [e]; exact dvd_sub h (dvd_mul_of_dvd_left hb _)
    exact (hπ.prime.dvd_or_dvd this).elim id id
  · exfalso
    have hbu := dvr_isUnit_of_not_dvd hπ hb
    set s := a * ↑hbu.unit⁻¹
    have e : asNrm y a b = b ^ 2 * (s ^ 2 + s - y) := by
      have : a = s * b := by simp only [s, mul_assoc, hbu.val_inv_mul, mul_one]
      rw [this]; unfold asNrm; ring
    have h1 : π ∣ s ^ 2 + s - y := by
      rw [e] at h
      rcases hπ.prime.dvd_or_dvd h with h' | h'
      · exact absurd (hπ.prime.dvd_of_dvd_pow h') hb
      · exact h'
    apply hy
    have := (isSquare_one_sub_four_mul_iff hπ h2π h20 (-y)).2 ⟨IsLocalRing.residue R s, ?_⟩
    · simpa using this
    · have h3 := (residue_eq_zero_iff_dvd hπ _).2 h1
      simp only [map_sub, map_add, map_pow] at h3
      rw [map_neg, CharTwo.neg_eq]
      linear_combination h3

/-- **Every nonzero pair has a primitive part:** $(A, B) = \pi^i(A', B')$ with $\pi\nmid A'$ or $\pi\nmid B'$. -/
theorem exists_primitive (hπ : Irreducible π) {A B : R} (hB : B ≠ 0) :
    ∃ i : ℕ, ∃ A' B' : R, A = π ^ i * A' ∧ B = π ^ i * B' ∧ ¬ (π ∣ A' ∧ π ∣ B') := by
  classical
  have hex : ∃ i, ¬ (π ^ (i + 1) ∣ A ∧ π ^ (i + 1) ∣ B) := by
    obtain ⟨j, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hB hπ
    refine ⟨j, fun h => ?_⟩
    have h2 := h.2
    rw [pow_succ, mul_comm (u : R)] at h2
    exact hπ.not_isUnit (isUnit_of_dvd_unit ((mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 h2) u.isUnit)
  obtain ⟨i, hispec, himin⟩ : ∃ i, ¬ (π ^ (i + 1) ∣ A ∧ π ^ (i + 1) ∣ B) ∧
      ∀ j < i, ¬ ¬ (π ^ (j + 1) ∣ A ∧ π ^ (j + 1) ∣ B) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hdiv : π ^ i ∣ A ∧ π ^ i ∣ B := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0]; simp
    · have := not_not.mp (himin (i - 1) (by omega))
      rwa [show i - 1 + 1 = i by omega] at this
  obtain ⟨⟨A', hA'⟩, ⟨B', hB'⟩⟩ := hdiv
  refine ⟨i, A', B', hA', hB', fun ⟨h1, h2⟩ => hispec ⟨?_, ?_⟩⟩
  · rw [hA', pow_succ]; exact mul_dvd_mul_left _ h1
  · rw [hB', pow_succ]; exact mul_dvd_mul_left _ h2

/-- **$K(\sqrt\delta)/K$ is ramified** (complete $R$, $\pi\mid 2$): $\delta c^2 = 1 + 4y$ with $1 + 4y$ a unit is impossible. -/
theorem not_unram_delta [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (hπ : Irreducible π) {t n w : R}
    (ht : π ∣ t) (hn : n = π * w) (hw : IsUnit w) (h2π : π ∣ 2) (h20 : (2 : R) ≠ 0) :
    ¬ ∃ c : K, c ≠ 0 ∧ ∃ y : R, IsUnit (1 + 4 * y) ∧ delta t n * c ^ 2 = ι (1 + 4 * y) := by
  rintro ⟨c, hc, y, -, hδ⟩
  have h2K : (2 : K) ≠ 0 := by
    rw [← map_ofNat (algebraMap R K) 2]; exact (map_ne_zero_iff _ (ι_inj (K := K))).2 h20
  -- `1 + 4y` is not a square
  have hy : ¬ IsSquare (1 + 4 * y) := by
    rintro ⟨s, hs⟩
    apply not_isSquare_delta (K := K) hπ ht hn hw h2K
    refine ⟨ι s / c, ?_⟩
    have : delta (K := K) t n = ι (1 + 4 * y) / c ^ 2 := by rw [← hδ]; field_simp
    rw [this, hs, map_mul]; field_simp
  -- `n = f(X - Y, 2Y)` with `X = t/2`, `Y = 1/c`
  set X : K := ι t / 2
  set Y : K := 1 / c
  have hY : Y ≠ 0 := by simp [Y, hc]
  have hfn : ι n = (X - Y) * (X - Y) + (X - Y) * (2 * Y) - ι y * ((2 * Y) * (2 * Y)) := by
    have e1 : ι (1 + 4 * y) = 1 + 4 * ι y := by rw [map_add, map_one, map_mul, map_ofNat]
    have e2 : delta (K := K) t n = (1 + 4 * ι y) / c ^ 2 := by rw [← e1, ← hδ]; field_simp
    have h4K : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2K h2K
    have e3 : ι n = X ^ 2 - delta t n := by simp only [X, delta]; field_simp; ring
    rw [e3, e2]; simp only [Y]; field_simp; ring
  obtain ⟨m, A, B, hA, hB⟩ := exists_pow_mul_eq₂ hπ (X - Y) (2 * Y)
  have hB0 : B ≠ 0 := by
    rintro rfl
    rw [map_zero] at hB
    exact mul_ne_zero ((map_ne_zero_iff _ (ι_inj (K := K))).2 (pow_ne_zero m hπ.ne_zero)) (mul_ne_zero h2K hY) hB
  obtain ⟨i, A', B', rfl, rfl, hprim⟩ := exists_primitive (A := A) hπ hB0
  have hfu : IsUnit (asNrm y A' B') := by
    refine dvr_isUnit_of_not_dvd hπ fun h => hprim ?_
    exact dvd_of_dvd_asNrm hπ h2π h20 hy h
  have key : π ^ (2 * m) * (π * w) = π ^ (2 * i) * asNrm y A' B' := by
    apply (ι_inj (K := K))
    have : ι (π ^ (2 * m) * n) = ι (π ^ (2 * i) * asNrm y A' B') := by
      have hgen : ∀ a b : R, ι (asNrm y a b) = ι a * ι a + ι a * ι b - ι y * (ι b * ι b) := by
        intro a b; simp [asNrm]
      have hsc : asNrm y (π ^ i * A') (π ^ i * B') = π ^ (2 * i) * asNrm y A' B' := by unfold asNrm; ring
      rw [← hsc, hgen, ← hA, ← hB, map_mul, hfn, show 2 * m = m * 2 by ring, pow_mul, map_pow]
      ring
    rwa [hn] at this
  rcases le_or_gt i m with him | him
  · -- `π ^ (2(m - i) + 1) w = f'`
    have e : π ^ (2 * i) * (π ^ (2 * (m - i) + 1) * w) = π ^ (2 * i) * asNrm y A' B' := by
      rw [← key, ← mul_assoc, ← pow_add, show 2 * i + (2 * (m - i) + 1) = 2 * m + 1 by omega, pow_succ]; ring
    have e' := mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) e
    apply hπ.not_isUnit
    refine isUnit_of_dvd_unit ?_ hfu
    rw [← e', pow_succ]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · have e : π ^ (2 * m + 1) * w = π ^ (2 * m + 1) * (π ^ (2 * i - 2 * m - 1) * asNrm y A' B') := by
      rw [← mul_assoc, ← pow_add, show 2 * m + 1 + (2 * i - 2 * m - 1) = 2 * i by omega, ← key, pow_succ]; ring
    have e' := mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) e
    apply hπ.not_isUnit
    refine isUnit_of_dvd_unit ?_ hw
    rw [e', show 2 * i - 2 * m - 1 = (2 * i - 2 * m - 2) + 1 by omega, pow_succ]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _


end QuadFormsKB.Hanke2005.R2Ram
