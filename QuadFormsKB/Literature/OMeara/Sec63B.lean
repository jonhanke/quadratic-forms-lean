/-
# O'Meara §63B: binary spaces of prime discriminant and the unit $\Delta$

**Setting** (as in `Sec63A.lean`): $R$ is a Henselian discrete valuation ring (O'Meara's $\mathfrak o$; only the
Henselian property of the complete ring is used) with finite residue field, $F$ its fraction field, $2 \ne 0$ in $R$,
$\pi$ a prime element. $\Delta \in R$ is a unit of quadratic defect $\mathfrak d(\Delta) = 4\mathfrak o$ (O'Meara's
fixed unit, Proposition 63:4). The Hilbert symbol is the library's `hilbertSymbol F` (for $\alpha, \beta \ne 0$ it is
$1$ exactly when $\alpha\xi^2 + \beta\eta^2 = 1$ is solvable, `hilbertSymbol_eq_one_iff_conic`, which is O'Meara's
definition, §63B, p. 164). Quadratic spaces are Mathlib `QuadraticForm F V`; $dV$ is the discriminant
$\det(B(b_i, b_j))$ of a base $b$ (`OMeara.gram`).

**Proves**
* Proposition 63:11 (p. 164): a binary space whose discriminant is a prime element represents exactly one of
  $\gamma$, $\gamma\Delta$, for every $\gamma \ne 0$ (`represents_xor_of_disc_prime`);
* Corollary 63:11a (p. 165): $(\varepsilon, \Delta)_\mathfrak p = 1$ for units $\varepsilon$ and
  $(\pi, \Delta)_\mathfrak p = -1$ (`hilbertSymbol_unit_delta`, `hilbertSymbol_prime_delta`);
* Corollary 63:11b, first part (p. 165): $\left(\frac{\pi,\Delta}{F}\right)$ is a division algebra
  (`quat_prime_delta_division`).

O'Meara proves 63:11 with the quadratic defect (Propositions 63:2, 63:4, 63:5) and deduces 63:11a from it; the proofs
here follow that route.
-/
import QuadFormsKB.Literature.OMeara.Sec63A
import QuadFormsKB.Literature.OMeara.Sec82
import QuadFormsKB.Tamagawa.Quaternion

open Submodule IsLocalRing QuadraticMap Module
open scoped Quaternion

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### Auxiliary lemmas (no `@[kb]`)

Proof outline. Write $N = \{s^2 + p t^2\}$ (`B63.NF`) for the norm form of a prime element $p$. A binary space with
discriminant $p$ represents $\gamma$ iff $\gamma/a \in N$ (`B63.rep_NF`), so 63:11 says: for $c \ne 0$ exactly one of
$c$, $c\Delta$ lies in $N$ (`B63.NF_xor`). Units are handled by a descent on the congruence modulo $\pi^m$
(`B63.unit_PU`), with the two classes of units of defect $4\mathfrak o$ treated through the additive map
$z \mapsto z^2 + z$ on the residue field (`B63.index_two_aux`); $\Delta \notin N$ is `B63.not_NF_delta`
(Proposition 63:5). $(\varepsilon, \Delta) = 1$ is `B63.exists_conic_unit`. -/

namespace B63

section NF
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- `c` is a value of the norm form `s² + p t²`. -/
def NF (p c : F) : Prop := ∃ s t : F, s ^ 2 + p * t ^ 2 = c

lemma NF_mul {p c c' : F} (h : NF p c) (h' : NF p c') : NF p (c * c') := by
  obtain ⟨s, t, rfl⟩ := h
  obtain ⟨s', t', rfl⟩ := h'
  exact ⟨s * s' - p * t * t', s * t' + t * s', by ring⟩

lemma NF_sq_mul {p c : F} (z : F) (h : NF p c) : NF p (z ^ 2 * c) := by
  obtain ⟨s, t, rfl⟩ := h
  exact ⟨z * s, z * t, by ring⟩

lemma NF_inv {p c : F} (hc : c ≠ 0) (h : NF p c) : NF p c⁻¹ := by
  obtain ⟨s, t, h⟩ := h
  refine ⟨s / c, t / c, ?_⟩
  rw [← h] at hc ⊢
  field_simp

lemma NF_sq (p z : F) : NF p (z ^ 2) := ⟨z, 0, by ring⟩

lemma NF_self (p : F) : NF p p := ⟨0, 1, by ring⟩

lemma NF_zpow {p : F} (hp : p ≠ 0) (k : ℤ) : NF p (p ^ k) := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · have : p ^ (2 * m) = (p ^ m) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]; norm_num
    rw [this]; exact NF_sq _ _
  · have e : p ^ (2 * m) = (p ^ m) ^ 2 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]; norm_num
    have : p ^ (2 * m + 1) = (p ^ m) ^ 2 * p := by
      rw [zpow_add_one₀ hp, e]
    rw [this]; exact NF_sq_mul _ (NF_self p)

/-- `c` or `c Δ` is a value of the norm form. -/
def PU (p Δ c : F) : Prop := NF p c ∨ NF p (c * Δ)

lemma PU_sq_mul {p Δ c : F} (z : F) (h : PU p Δ c) : PU p Δ (z ^ 2 * c) := by
  rcases h with h | h
  · exact Or.inl (NF_sq_mul z h)
  · right; rw [mul_assoc]; exact NF_sq_mul z h

lemma PU_mul_NF {p Δ c n : F} (h : PU p Δ c) (hn : NF p n) : PU p Δ (c * n) := by
  rcases h with h | h
  · exact Or.inl (NF_mul h hn)
  · right; rw [mul_right_comm]; exact NF_mul h hn

lemma PU_of_sq {p Δ c : F} (h : IsSquare c) : PU p Δ c := by
  obtain ⟨z, rfl⟩ := h
  exact Or.inl (by rw [← _root_.sq]; exact NF_sq p z)

variable {π : R}

lemma dord_inv' (hπ : Irreducible π) {x : F} (hx : x ≠ 0) : dord hπ x⁻¹ = - dord hπ x := by
  have h := dord_mul hπ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx] at h
  have h1 : dord hπ (1 : F) = 0 := by simpa using dord_unit (F := F) hπ (u := 1) isUnit_one
  omega

lemma span_unit_mul (hπ : Irreducible π) {c : F} (hc : c ≠ 0) (hc0 : dord hπ c = 0) {y : F} (hy : y ≠ 0) :
    span R {c} * span R {y} = span R {y} := by
  ext z
  rw [mem_span_mul hc]
  by_cases hz : z = 0
  · simp [hz]
  · have hcz : c⁻¹ * z ≠ 0 := mul_ne_zero (inv_ne_zero hc) hz
    rw [mem_span_iff hπ hcz hy, mem_span_iff hπ hz hy, dord_mul hπ (inv_ne_zero hc) hz, dord_inv' hπ hc, hc0]
    simp

lemma pi_mem_max (hπ : Irreducible π) : π ∈ maximalIdeal R := by
  simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hπ.not_isUnit

lemma mem_max_iff (hπ : Irreducible π) (x : R) : x ∈ maximalIdeal R ↔ π ∣ x := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton]

lemma not_dvd_of_isUnit (hπ : Irreducible π) {x : R} (hx : IsUnit x) : ¬ π ∣ x :=
  fun h => hπ.not_isUnit (isUnit_of_dvd_unit h hx)

lemma isSquare_of_close [HenselianLocalRing R] (hπ : Irreducible π) {u δ x : R} (hδ : IsUnit δ)
    (h : u - δ ^ 2 = 4 * π * x) : IsSquare u := by
  obtain ⟨di, hdi⟩ := hδ.exists_right_inv
  have hmem : π * x * di ^ 2 ∈ maximalIdeal R :=
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (pi_mem_max hπ))
  obtain ⟨s, hs⟩ := isSquare_one_add_four_mul hmem
  refine ⟨δ * s, ?_⟩
  calc u = δ ^ 2 * (1 + 4 * (π * x * di ^ 2)) := by
        linear_combination h - (4 * π * x * (1 + δ * di)) * hdi
    _ = δ * s * (δ * s) := by rw [hs]; ring

lemma sq_mod_iff (hπ : Irreducible π) (v : R) :
    (∃ δ : R, π ∣ v - δ ^ 2) ↔ IsSquare (residue R v) := by
  constructor
  · rintro ⟨δ, hδ⟩
    refine ⟨residue R δ, ?_⟩
    have := (residue_eq_zero_iff _).2 ((mem_max_iff hπ _).2 hδ)
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [this]; ring
  · rintro ⟨z, hz⟩
    obtain ⟨δ, rfl⟩ := residue_surjective z
    refine ⟨δ, (mem_max_iff hπ _).1 ((residue_eq_zero_iff _).1 ?_)⟩
    rw [map_sub, map_pow, hz]; ring

/-- In a finite field of characteristic $2$ the image of $z \mapsto z^2 + z$ has index $2$. -/
lemma index_two_aux (k : Type*) [Field k] [Finite k] [CharP k 2] (x y : k)
    (hx : ¬ ∃ z : k, z ^ 2 + z = x) (hy : ¬ ∃ z : k, z ^ 2 + z = y) : ∃ z : k, z ^ 2 + z = x + y := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  let f : k →+ k :=
    { toFun := fun z => z ^ 2 + z
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [CharTwo.add_sq]; ring }
  have hf : ∀ z, f z = z ^ 2 + z := fun z => rfl
  have hker : Nat.card f.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨0, by simp⟩, ⟨1, by simp [hf]; linear_combination h2⟩,
      ?_, ?_⟩
    · intro h
      have := congrArg Subtype.val h
      simp at this
    · ext ⟨z, hz⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
      rw [AddMonoidHom.mem_ker, hf] at hz
      have : z * (z + 1) = 0 := by linear_combination hz
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · right; linear_combination h - h2
  have : Finite f.range := inferInstance
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have h3 : Nat.card (k ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have h4 := AddSubgroup.card_mul_index f.range
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hind : f.range.index = 2 := by
    rw [h3, hker] at h1
    have : Nat.card f.range * f.range.index = Nat.card f.range * 2 := by rw [h4, h1]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  obtain ⟨a, ha⟩ := AddSubgroup.index_eq_two_iff.1 hind
  have hxr : x ∉ f.range := fun ⟨z, hz⟩ => hx ⟨z, by rw [← hf]; exact hz⟩
  have hyr : y ∉ f.range := fun ⟨z, hz⟩ => hy ⟨z, by rw [← hf]; exact hz⟩
  have hx' : x + a ∈ f.range := by
    rcases ha x with h | h
    · exact h.1
    · exact absurd h.1 hxr
  have hy' : y + a ∈ f.range := by
    rcases ha y with h | h
    · exact h.1
    · exact absurd h.1 hyr
  obtain ⟨z, hz⟩ := add_mem hx' hy'
  refine ⟨z, ?_⟩
  rw [← hf, hz]; linear_combination a * h2

lemma nonsq_mul_nonsq' {k : Type*} [Field k] [Fintype k] {a b : k} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a * b) := by
  classical
  have ha0 : a ≠ 0 := fun h => ha (h ▸ ⟨0, by simp⟩)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ ⟨0, by simp⟩)
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

lemma dyadic_data (h2 : (2 : R) ≠ 0) (h2p : ¬ IsUnit (2 : R)) (hπ : Irreducible π) :
    ∃ (e : ℕ) (w2 wi : R), 1 ≤ e ∧ IsUnit w2 ∧ w2 * wi = 1 ∧ (2 : R) = w2 * π ^ e ∧
      (4 : R) = w2 ^ 2 * π ^ (2 * e) ∧ π ^ (2 * e) = 4 * wi ^ 2 := by
  obtain ⟨e, w2, h2eq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h2 hπ
  have he : 1 ≤ e := by
    by_contra h0
    have : e = 0 := by omega
    subst this
    apply h2p; rw [h2eq]; simp
  have h4 : (4 : R) = (w2 : R) ^ 2 * π ^ (2 * e) := by
    calc (4 : R) = 2 * 2 := by norm_num
      _ = ((w2 : R) * π ^ e) * ((w2 : R) * π ^ e) := by rw [← h2eq]
      _ = _ := by ring
  have hwi : (w2 : R) * ((w2⁻¹ : Rˣ) : R) = 1 := w2.mul_inv
  refine ⟨e, w2, ((w2⁻¹ : Rˣ) : R), he, w2.isUnit, hwi, h2eq, h4, ?_⟩
  rw [h4]
  linear_combination (-(π ^ (2 * e)) * (1 + (w2 : R) * ((w2⁻¹ : Rˣ) : R))) * hwi

lemma isSq_of_residue_sq_dyadic [HenselianLocalRing R] (hπ : Irreducible π) {e : ℕ} {w2 : R} (he : 1 ≤ e)
    (h2eq : (2 : R) = w2 * π ^ e)
    (a z c : R) (hc : a - z ^ 2 - z = π * c) : IsSquare (1 + 4 * a) := by
  have hπ2 : π ∣ 2 := by rw [h2eq]; exact Dvd.dvd.mul_left (dvd_pow_self π (by omega)) _
  have hu : IsUnit (1 + 2 * z) := by
    refine isUnit_of_not_dvd' hπ fun hd => hπ.not_isUnit ?_
    have : π ∣ 1 := by
      have := dvd_sub hd (Dvd.dvd.mul_right hπ2 z)
      simpa using this
    exact isUnit_of_dvd_one this
  exact isSquare_of_close hπ hu (x := c) (by linear_combination 4 * hc)

lemma PU_of_sqR (p Δ : F) {x : R} (h : IsSquare x) : PU p Δ (algebraMap R F x) := by
  obtain ⟨s, rfl⟩ := h
  exact PU_of_sq ⟨algebraMap R F s, by rw [map_mul]⟩

lemma D_case [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0) (h2p : ¬ IsUnit (2 : R))
    (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) (a : R) :
    PU (algebraMap R F π) (algebraMap R F Δ) (algebraMap R F (1 + 4 * a)) := by
  obtain ⟨e, w2, wi, he, hw2, hwi, h2eq, h4, hpe⟩ := dyadic_data h2 h2p hπ
  have hπ4 : π ∣ 4 := by rw [h4]; exact Dvd.dvd.mul_left (dvd_pow_self π (by omega)) _
  have h4ne := four_F_ne (R := R) (F := F) h2
  have hΔd' : quadDefect R (algebraMap R F Δ) = span R {algebraMap R F π ^ (2 * e)} := by
    rw [hΔd]
    have h4F : dord hπ (4 : F) = ((2 * e : ℕ) : ℤ) :=
      dord_eq hπ (u := w2 ^ 2) (hw2.pow 2) (by rw [four_F_eq (R := R), h4]; simp only [map_mul, map_pow, zpow_natCast])
    rw [← zpow_natCast]
    exact span_eq_of_dord_eq hπ h4ne (zpow_ne_zero _ (alg_pi_ne_zero hπ)) (by rw [h4F, dord_zpow])
  obtain ⟨⟨δΔ, hδΔ⟩, hnot⟩ := (quadDefect_eq_pow_iff h2 hπ hΔ (2 * e)).1 hΔd'
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hδΔ
  have hδΔu : IsUnit δΔ := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hΔ (by
    have : Δ = δΔ ^ 2 + 4 * (wi ^ 2 * r) := by linear_combination hr + r * hpe
    rw [this]
    exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (Dvd.dvd.mul_right hπ4 _))
  obtain ⟨di, hdi⟩ := hδΔu.exists_right_inv
  obtain ⟨aΔ, hΔeq, hnotI⟩ : ∃ aΔ : R, Δ = δΔ ^ 2 * (1 + 4 * aΔ) ∧ ¬ ∃ z : R, π ∣ aΔ - z ^ 2 - z := by
    refine ⟨wi ^ 2 * r * di ^ 2, by linear_combination hr + r * hpe - (4 * wi ^ 2 * r * (1 + δΔ * di)) * hdi, ?_⟩
    rintro ⟨z, c, hc⟩
    refine hnot ⟨δΔ * (1 + 2 * z), ?_⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨w2 ^ 2 * δΔ ^ 2 * c, ?_⟩
    have hΔeq : Δ = δΔ ^ 2 * (1 + 4 * (wi ^ 2 * r * di ^ 2)) := by
      linear_combination hr + r * hpe - (4 * wi ^ 2 * r * (1 + δΔ * di)) * hdi
    linear_combination hΔeq + 4 * δΔ ^ 2 * hc + δΔ ^ 2 * π * c * h4
  have h2z : (2 : ResidueField R) = 0 := by
    have : residue R 2 = 0 := (residue_eq_zero_iff _).2 ((mem_max_iff hπ _).2 (by
      rw [h2eq]; exact Dvd.dvd.mul_left (dvd_pow_self π (by omega)) _))
    rwa [map_ofNat] at this
  have hc2 : CharP (ResidueField R) 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2z
  have h4r : residue R (4 : R) = 0 := (residue_eq_zero_iff _).2 ((mem_max_iff hπ _).2 hπ4)
  by_cases hI : ∃ z : R, π ∣ a - z ^ 2 - z
  · obtain ⟨z, c, hc⟩ := hI
    exact PU_of_sqR _ _ (isSq_of_residue_sq_dyadic hπ he h2eq a z c hc)
  · have hx : ¬ ∃ z : ResidueField R, z ^ 2 + z = residue R a := by
      rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := residue_surjective z
      apply hI
      refine ⟨z, (mem_max_iff hπ _).1 ((residue_eq_zero_iff _).1 ?_)⟩
      simp only [map_sub, map_pow]
      linear_combination (-1) * hz
    have hy : ¬ ∃ z : ResidueField R, z ^ 2 + z = residue R aΔ := by
      rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := residue_surjective z
      apply hnotI
      refine ⟨z, (mem_max_iff hπ _).1 ((residue_eq_zero_iff _).1 ?_)⟩
      simp only [map_sub, map_pow]
      linear_combination (-1) * hz
    obtain ⟨zb, hzb⟩ := index_two_aux (ResidueField R) _ _ hx hy
    obtain ⟨z0, rfl⟩ := residue_surjective zb
    have hmem : π ∣ (a + aΔ + 4 * a * aΔ) - z0 ^ 2 - z0 := by
      refine (mem_max_iff hπ _).1 ((residue_eq_zero_iff _).1 ?_)
      simp only [map_sub, map_add, map_mul, map_pow, h4r]
      linear_combination (-1) * hzb
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨s, hs⟩ := isSq_of_residue_sq_dyadic hπ he h2eq _ z0 c hc
    right
    have hsq : (1 + 4 * a) * Δ = (δΔ * s) ^ 2 := by
      rw [hΔeq]; linear_combination δΔ ^ 2 * hs
    refine ⟨algebraMap R F (δΔ * s), 0, ?_⟩
    rw [← map_mul, hsq]; simp

/-- The statement `Q m` of the descent: every unit congruent to a square mod `π^m` is in the class. -/
def QP (p Δ : F) (π : R) (m : ℕ) : Prop :=
  ∀ v : R, IsUnit v → ∀ δ : R, v - δ ^ 2 ∈ Ideal.span {π ^ m} → PU p Δ (algebraMap R F v)

lemma unit_PU_dyadic [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) (u : R) (hu : IsUnit u) :
    PU (algebraMap R F π) (algebraMap R F Δ) (algebraMap R F u) := by
  have hD := D_case (F := F) h2 h2p hπ hΔ hΔd
  obtain ⟨e, w2, wi, he, hw2, hwi, h2eq, h4, hpe⟩ := dyadic_data h2 h2p hπ
  have base : ∀ m, 2 * e + 1 ≤ m →
      QP (algebraMap R F π) (algebraMap R F Δ) π m := by
    intro m hm v hv δ h
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.1 h
    have hδ : IsUnit δ := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hv (by
      have : v = δ ^ 2 + π ^ m * x := by linear_combination hx
      rw [this]
      exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _))
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * e + 1 + k := ⟨m - (2 * e + 1), by omega⟩
    have hsq := isSquare_of_close hπ hδ (x := wi ^ 2 * π ^ k * x) (by
      rw [hx, hk]; linear_combination (π * π ^ k * x) * hpe)
    exact PU_of_sqR _ _ hsq
  have step : ∀ m, m ≤ 2 * e → QP (algebraMap R F π) (algebraMap R F Δ) π (m + 1) →
      QP (algebraMap R F π) (algebraMap R F Δ) π m := by
    intro m hm hQ v hv δ h
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · obtain ⟨y, hy⟩ := exists_sq_mod h2p v
      exact hQ v hv y (by rw [Ideal.mem_span_singleton, zero_add, pow_one]; exact (mem_max_iff hπ _).1 hy)
    by_cases hb : ∃ δ' : R, v - δ' ^ 2 ∈ Ideal.span {π ^ (m + 1)}
    · obtain ⟨δ', h'⟩ := hb
      exact hQ v hv δ' h'
    push Not at hb
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.1 h
    have hwu : IsUnit w := isUnit_of_not_dvd' hπ fun hd => hb δ (by
      rw [Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := hd
      exact ⟨c, by rw [pow_succ]; linear_combination hw + π ^ m * hc⟩)
    have hδ : IsUnit δ := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hv (by
      have : v = δ ^ 2 + π ^ m * w := by linear_combination hw
      rw [this]
      exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _))
    obtain ⟨y, hy⟩ := exists_sq_mod h2p w
    obtain ⟨s, hs⟩ := (mem_max_iff hπ _).1 hy
    obtain ⟨di, hdi⟩ := hδ.exists_right_inv
    rcases Nat.even_or_odd m with ⟨r, hr⟩ | ⟨r, hr⟩
    · by_cases hlt : m < 2 * e
      · exfalso
        obtain ⟨t', ht'⟩ : ∃ t', e = r + 1 + t' := ⟨e - (r + 1), by omega⟩
        subst hr
        subst ht'
        refine hb (δ + π ^ r * y) ?_
        rw [Ideal.mem_span_singleton]
        exact ⟨s - w2 * π ^ t' * δ * y, by
          linear_combination hw + π ^ (r + r) * hs - (δ * π ^ r * y) * h2eq⟩
      · have hme : m = 2 * e := by omega
        subst hme
        have hv' : v = δ ^ 2 * (1 + 4 * (wi ^ 2 * w * di ^ 2)) := by
          linear_combination hw + w * hpe - (4 * wi ^ 2 * w * (1 + δ * di)) * hdi
        have := PU_sq_mul (algebraMap R F δ) (hD (wi ^ 2 * w * di ^ 2))
        have e1 : algebraMap R F v = algebraMap R F δ ^ 2 * algebraMap R F (1 + 4 * (wi ^ 2 * w * di ^ 2)) := by
          rw [← map_pow, ← map_mul, ← hv']
        rw [e1]; exact this
    · subst hr
      have hnu : IsUnit (1 + (y * di) ^ 2 * π ^ (2 * r + 1)) := by
        refine isUnit_of_not_dvd' hπ fun hd => hπ.not_isUnit (isUnit_of_dvd_one ?_)
        exact (dvd_add_left (Dvd.dvd.mul_left (dvd_pow_self π (by omega)) _)).1 hd
      obtain ⟨ni, hni⟩ := hnu.exists_right_inv
      have hniu : IsUnit ni := isUnit_of_dvd_one ⟨_, by rw [mul_comm]; exact hni.symm⟩
      have hQ' := hQ (v * ni) (hv.mul hniu) δ (by
        rw [Ideal.mem_span_singleton]
        exact ⟨s * ni, by
          linear_combination ni * hw + ni * π ^ (2 * r + 1) * hs
            - ni * π ^ (2 * r + 1) * y ^ 2 * (1 + δ * di) * hdi + δ ^ 2 * hni⟩)
      have hNF : NF (algebraMap R F π) (algebraMap R F (1 + (y * di) ^ 2 * π ^ (2 * r + 1))) :=
        ⟨1, algebraMap R F (y * di) * algebraMap R F π ^ r, by
          simp only [map_add, map_mul, map_pow, map_one]; ring⟩
      have := PU_mul_NF hQ' hNF
      have hvv : algebraMap R F v = algebraMap R F (v * ni) *
          algebraMap R F (1 + (y * di) ^ 2 * π ^ (2 * r + 1)) := by
        rw [← map_mul]; congr 1; linear_combination (-v) * hni
      rw [hvv]; exact this
  have key : ∀ j m, 2 * e + 1 ≤ m + j → QP (algebraMap R F π) (algebraMap R F Δ) π m := by
    intro j
    induction j with
    | zero => intro m hm; exact base m (by omega)
    | succ j ih =>
      intro m hm
      by_cases hm' : 2 * e + 1 ≤ m
      · exact base m hm'
      · exact step m (by omega) (ih (m + 1) (by omega))
  exact key (2 * e + 1) 0 (by omega) u hu 0 (by simp)

lemma unit_PU_nondyadic [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : IsUnit (2 : R))
    (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) (u : R) (hu : IsUnit u) :
    PU (algebraMap R F π) (algebraMap R F Δ) (algebraMap R F u) := by
  have h2' := h2.ne_zero
  have h4u : IsUnit (4 : R) := by rw [show (4 : R) = 2 * 2 by norm_num]; exact h2.mul h2
  obtain ⟨i4, hi4⟩ := h4u.exists_right_inv
  -- a unit close to a square mod π is a square
  have close : ∀ v : R, IsUnit v → (∃ δ : R, π ∣ v - δ ^ 2) → IsSquare v := by
    rintro v hv ⟨δ, r, hr⟩
    have hδ : IsUnit δ := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hv (by
      have : v = δ ^ 2 + π * r := by linear_combination hr
      rw [this]
      exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (Dvd.dvd.mul_right dvd_rfl _))
    exact isSquare_of_close hπ hδ (x := r * i4) (by linear_combination hr - (π * r) * hi4)
  have hΔns : ¬ IsSquare (residue R Δ) := by
    intro hs
    have := close Δ hΔ ((sq_mod_iff hπ Δ).2 hs)
    obtain ⟨s, hs'⟩ := this
    have hsq : IsSquare (algebraMap R F Δ) := ⟨algebraMap R F s, by rw [hs', map_mul]⟩
    rw [isSquare_iff_quadDefect_eq_bot h2', hΔd] at hsq
    exact four_F_ne (R := R) (F := F) h2' (by simpa using hsq)
  have : Fintype (ResidueField R) := Fintype.ofFinite _
  by_cases hs : IsSquare (residue R u)
  · exact PU_of_sqR _ _ (close u hu ((sq_mod_iff hπ u).2 hs))
  · have hs2 : IsSquare (residue R (u * Δ)) := by
      rw [map_mul]; exact nonsq_mul_nonsq' hs hΔns
    have := close (u * Δ) (hu.mul hΔ) ((sq_mod_iff hπ _).2 hs2)
    obtain ⟨s, hs'⟩ := this
    right
    refine ⟨algebraMap R F s, 0, ?_⟩
    rw [← map_mul, hs']; simp [pow_two]

lemma unit_PU [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) (u : R) (hu : IsUnit u) :
    PU (algebraMap R F π) (algebraMap R F Δ) (algebraMap R F u) := by
  by_cases h2u : IsUnit (2 : R)
  · exact unit_PU_nondyadic h2u hπ hΔ hΔd u hu
  · exact unit_PU_dyadic h2 h2u hπ hΔ hΔd u hu

lemma conic_aux1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (ε' δ a k : K) (ha : a ≠ 0) (hδ : δ ≠ 0)
    (hk : k * k = 1 + 4 * a * (1 - ε')) (hs : (1 + k) / (4 * a) + 1 ≠ 0) :
    ∃ X Y : K, ε' * X ^ 2 + (δ ^ 2 * (1 + 4 * a)) * Y ^ 2 = 1 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4a : 4 * a ≠ 0 := mul_ne_zero h4 ha
  set w := (1 + k) / (4 * a) with hw
  have hw1 : 4 * a * w = 1 + k := by rw [hw]; field_simp
  clear_value w
  have key : 4 * a * w ^ 2 - 2 * w + ε' - 1 = 0 := by
    have : (4 * a) * (4 * a * w ^ 2 - 2 * w + ε' - 1) = 0 := by
      linear_combination (4 * a * w + 1 + k - 2) * hw1 + hk
    exact (mul_eq_zero.1 this).resolve_left h4a
  refine ⟨1 / (w + 1), (w / δ) / (w + 1), ?_⟩
  field_simp
  linear_combination key

lemma conic_aux {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (ε' δ a k : K) (ha : a ≠ 0) (hδ : δ ≠ 0)
    (h1a : 1 + 4 * a ≠ 0) (hk : k * k = 1 + 4 * a * (1 - ε')) :
    ∃ X Y : K, ε' * X ^ 2 + (δ ^ 2 * (1 + 4 * a)) * Y ^ 2 = 1 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h4a : 4 * a ≠ 0 := mul_ne_zero h4 ha
  have sg : ∀ k' : K, (1 + k') / (4 * a) + 1 = 0 ↔ 1 + k' + 4 * a = 0 := by
    intro k'; rw [div_add_one h4a, div_eq_zero_iff]; simp [h4a]
  by_cases h : 1 + k + 4 * a = 0
  · refine conic_aux1 h2 ε' δ a (-k) ha hδ (by rw [← hk]; ring) ?_
    rw [Ne, sg]
    intro h'
    apply h1a
    have : 2 * (1 + 4 * a) = 0 := by linear_combination h + h'
    exact (mul_eq_zero.1 this).resolve_left h2
  · exact conic_aux1 h2 ε' δ a k ha hδ hk (by rw [Ne, sg]; exact h)

lemma exists_sq_add_sq_eq_one_b {k : Type*} [Field k] [Fintype k] (hF : ringChar k ≠ 2) {a b : k}
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x y : k, a * x ^ 2 + b * y ^ 2 = 1 := by
  have h := FiniteField.exists_root_sum_quadratic (f := Polynomial.C a * Polynomial.X ^ 2)
    (g := Polynomial.C b * Polynomial.X ^ 2 - Polynomial.C 1) (by
      rw [Polynomial.degree_C_mul_X_pow 2 ha]; rfl) (by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;>
      rw [Polynomial.degree_C_mul_X_pow 2 hb] <;> simp)
    (FiniteField.odd_card_of_char_ne_two hF)
  obtain ⟨x, y, h⟩ := h
  refine ⟨x, y, ?_⟩
  simp at h
  linear_combination h

lemma delta_form [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (h2p : ¬ IsUnit (2 : R)) (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) :
    ∃ δΔ a : R, IsUnit δΔ ∧ Δ = δΔ ^ 2 * (1 + 4 * a) := by
  obtain ⟨e, w2, wi, he, hw2, hwi, h2eq, h4, hpe⟩ := dyadic_data h2 h2p hπ
  have hπ4 : π ∣ 4 := by rw [h4]; exact Dvd.dvd.mul_left (dvd_pow_self π (by omega)) _
  have h4ne := four_F_ne (R := R) (F := F) h2
  have hΔd' : quadDefect R (algebraMap R F Δ) = span R {algebraMap R F π ^ (2 * e)} := by
    rw [hΔd]
    have h4F : dord hπ (4 : F) = ((2 * e : ℕ) : ℤ) :=
      dord_eq hπ (u := w2 ^ 2) (hw2.pow 2) (by rw [four_F_eq (R := R), h4]; simp only [map_mul, map_pow, zpow_natCast])
    rw [← zpow_natCast]
    exact span_eq_of_dord_eq hπ h4ne (zpow_ne_zero _ (alg_pi_ne_zero hπ)) (by rw [h4F, dord_zpow])
  obtain ⟨⟨δΔ, hδΔ⟩, -⟩ := (quadDefect_eq_pow_iff h2 hπ hΔ (2 * e)).1 hΔd'
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 hδΔ
  have hδΔu : IsUnit δΔ := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hΔ (by
    have : Δ = δΔ ^ 2 + 4 * (wi ^ 2 * r) := by linear_combination hr + r * hpe
    rw [this]
    exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (Dvd.dvd.mul_right hπ4 _))
  obtain ⟨di, hdi⟩ := hδΔu.exists_right_inv
  exact ⟨δΔ, wi ^ 2 * r * di ^ 2, hδΔu, by
    linear_combination hr + r * hpe - (4 * wi ^ 2 * r * (1 + δΔ * di)) * hdi⟩

/-- $(\varepsilon, \Delta) = 1$ for a unit $\varepsilon$, in the conic form $\varepsilon x^2 + \Delta y^2 = 1$. -/
lemma exists_conic_unit [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0) {Δ : R}
    (hΔ : IsUnit Δ) (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {ε : R} (hε : IsUnit ε) :
    ∃ x y : F, algebraMap R F ε * x ^ 2 + algebraMap R F Δ * y ^ 2 = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  by_cases h2u : IsUnit (2 : R)
  · have h4u : IsUnit (4 : R) := by rw [show (4 : R) = 2 * 2 by norm_num]; exact h2u.mul h2u
    obtain ⟨i4, hi4⟩ := h4u.exists_right_inv
    have : Fintype (ResidueField R) := Fintype.ofFinite _
    have hring : ringChar (ResidueField R) ≠ 2 := by
      intro h
      have hc : CharP (ResidueField R) 2 := ringChar.of_eq h
      have h0 := CharP.cast_eq_zero (ResidueField R) 2
      rw [Nat.cast_ofNat] at h0
      have : residue R 2 = 0 := by rwa [map_ofNat]
      exact ((residue_ne_zero_iff_isUnit _).2 h2u) this
    obtain ⟨xb, yb, hxy⟩ := exists_sq_add_sq_eq_one_b hring ((residue_ne_zero_iff_isUnit _).2 hε)
      ((residue_ne_zero_iff_isUnit _).2 hΔ)
    obtain ⟨x, rfl⟩ := residue_surjective xb
    obtain ⟨y, rfl⟩ := residue_surjective yb
    have hmem : ε * x ^ 2 + Δ * y ^ 2 - 1 ∈ maximalIdeal R := by
      refine (residue_eq_zero_iff _).1 ?_
      simp only [map_sub, map_add, map_mul, map_pow, map_one]
      linear_combination hxy
    obtain ⟨r, hr⟩ := (mem_max_iff hπ _).1 hmem
    obtain ⟨z, hz⟩ := isSquare_of_close hπ (u := ε * x ^ 2 + Δ * y ^ 2) (δ := 1) isUnit_one (x := r * i4)
      (by linear_combination hr - (π * r) * hi4)
    have hu : IsUnit (ε * x ^ 2 + Δ * y ^ 2) := by
      refine isUnit_of_not_dvd' hπ fun hd => hπ.not_isUnit (isUnit_of_dvd_one ?_)
      have h1 : (1 : R) = (ε * x ^ 2 + Δ * y ^ 2) - π * r := by linear_combination -hr
      rw [h1]
      exact dvd_sub hd (dvd_mul_right π r)
    have hzu : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ hu)
    have hzne := alg_ne_zero_of_unit (F := F) hzu
    refine ⟨algebraMap R F x / algebraMap R F z, algebraMap R F y / algebraMap R F z, ?_⟩
    have : algebraMap R F (ε * x ^ 2 + Δ * y ^ 2) = algebraMap R F z * algebraMap R F z := by
      rw [← map_mul, hz]
    simp only [map_add, map_mul, map_pow] at this
    field_simp
    linear_combination this
  · obtain ⟨δΔ, a, hδΔ, hΔeq⟩ := delta_form (F := F) h2 h2u hπ hΔ hΔd
    obtain ⟨y0, hy0⟩ := exists_sq_mod h2u ε
    obtain ⟨c0, hc0⟩ := (mem_max_iff hπ _).1 hy0
    have hy0u : IsUnit y0 := isUnit_of_not_dvd' hπ fun hd => not_dvd_of_isUnit hπ hε (by
      have : ε = y0 ^ 2 + π * c0 := by linear_combination hc0
      rw [this]
      exact dvd_add (Dvd.dvd.pow hd two_ne_zero) (dvd_mul_right _ _))
    obtain ⟨di0, hdi0⟩ := hy0u.exists_right_inv
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hsq : IsSquare (algebraMap R F Δ) := ⟨algebraMap R F δΔ, by
        rw [hΔeq]; simp only [map_mul, map_pow, map_one, mul_zero, add_zero]; ring⟩
      rw [isSquare_iff_quadDefect_eq_bot h2, hΔd] at hsq
      exact four_F_ne (R := R) (F := F) h2 (by simpa using hsq)
    have hmem : a * (1 - ε * di0 ^ 2) ∈ maximalIdeal R := by
      refine Ideal.mul_mem_left _ _ ((mem_max_iff hπ _).2 ⟨-c0 * di0 ^ 2, ?_⟩)
      linear_combination (-di0 ^ 2) * hc0 - (1 + y0 * di0) * hdi0
    obtain ⟨kk, hkk⟩ := isSquare_one_add_four_mul hmem
    have hΔne := alg_ne_zero_of_unit (F := F) hΔ
    have hδne := alg_ne_zero_of_unit (F := F) hδΔ
    have h1a : (1 : F) + 4 * algebraMap R F a ≠ 0 := by
      intro h0
      apply hΔne
      rw [hΔeq]
      simp only [map_mul, map_pow, map_add, map_one, map_ofNat]
      rw [h0]; ring
    have han : algebraMap R F a ≠ 0 := (map_ne_zero_iff _ alg_inj).2 ha0
    obtain ⟨X, Y, hXY⟩ := conic_aux h2F (algebraMap R F ε * algebraMap R F di0 ^ 2) (algebraMap R F δΔ)
      (algebraMap R F a) (algebraMap R F kk) han hδne h1a (by
        have := congrArg (algebraMap R F) hkk
        simp only [map_add, map_mul, map_pow, map_one, map_sub, map_ofNat] at this
        linear_combination -this)
    refine ⟨algebraMap R F di0 * X, Y, ?_⟩
    have hΔ' : algebraMap R F Δ = algebraMap R F δΔ ^ 2 * (1 + 4 * algebraMap R F a) := by
      rw [hΔeq]; simp only [map_mul, map_pow, map_add, map_one, map_ofNat]
    rw [hΔ']
    linear_combination hXY

lemma not_NF_delta [HenselianLocalRing R] (h2 : (2 : R) ≠ 0) {Δ : R} (hp : Irreducible π) (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) :
    ¬ NF (algebraMap R F π) (algebraMap R F Δ) := by
  rintro ⟨s, t, hst⟩
  have hpne := alg_pi_ne_zero (R := R) (F := F) hp
  have h4ne := four_F_ne (R := R) (F := F) h2
  have hΔne := alg_ne_zero_of_unit (F := F) hΔ
  by_cases ht : t = 0
  · subst ht
    have hsq : IsSquare (algebraMap R F Δ) := ⟨s, by rw [← hst]; ring⟩
    rw [isSquare_iff_quadDefect_eq_bot h2, hΔd] at hsq
    exact h4ne (by simpa using hsq)
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hpt : algebraMap R F π * t ^ 2 ≠ 0 := mul_ne_zero hpne ht2
  have hp1 : dord hp (algebraMap R F π) = 1 := by
    have := dord_zpow (F := F) hp 1
    rwa [zpow_one] at this
  have hdpt : dord hp (algebraMap R F π * t ^ 2) = 1 + 2 * dord hp t := by
    rw [dord_mul hp hpne ht2, dord_sq hp ht, hp1]
  have hΔ0 : dord hp (algebraMap R F Δ) = 0 := dord_unit hp hΔ
  have hΔeq : algebraMap R F Δ = s ^ 2 + algebraMap R F π * t ^ 2 := hst.symm
  by_cases hs : s = 0
  · subst hs
    have : algebraMap R F Δ = algebraMap R F π * t ^ 2 := by rw [hΔeq]; ring
    rw [this, hdpt] at hΔ0
    omega
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hds2 : dord hp (s ^ 2) = 2 * dord hp s := dord_sq hp hs
  have hsum : s ^ 2 + algebraMap R F π * t ^ 2 ≠ 0 := by rw [← hΔeq]; exact hΔne
  have hmain : dord hp s = 0 ∧ 0 ≤ dord hp t := by
    rcases lt_trichotomy (dord hp (s ^ 2)) (dord hp (algebraMap R F π * t ^ 2)) with hl | hl | hl
    · have := dord_add_of_lt hp hs2 hpt hsum hl
      rw [← hΔeq, hΔ0] at this
      omega
    · omega
    · have := dord_add_of_lt hp hpt hs2 (by rwa [add_comm]) hl
      rw [add_comm, ← hΔeq, hΔ0] at this
      omega
  obtain ⟨hs0, ht0⟩ := hmain
  set β := algebraMap R F π * t ^ 2 / s ^ 2 with hβdef
  have hβne : β ≠ 0 := div_ne_zero hpt hs2
  have hβeq : (s⁻¹) ^ 2 * algebraMap R F Δ = 1 + β := by
    rw [hΔeq, hβdef]; field_simp
  have hdβ : dord hp β = 1 + 2 * dord hp t := by
    have : β = algebraMap R F π * t ^ 2 * (s ^ 2)⁻¹ := by rw [hβdef]; ring
    rw [this, dord_mul hp hpt (inv_ne_zero hs2), dord_inv' hp hs2, hdpt, hds2, hs0]; ring
  have hs'0 : dord hp ((s⁻¹) ^ 2) = 0 := by
    rw [dord_sq hp (inv_ne_zero hs), dord_inv' hp hs, hs0]; ring
  have hdef : quadDefect R (1 + β) = span R {(4 : F)} := by
    rw [← hβeq, quadDefect_sq_mul, hΔd]
    exact span_unit_mul hp (pow_ne_zero 2 (inv_ne_zero hs)) hs'0 h4ne
  obtain ⟨w, hw, hβw⟩ := dord_spec hp hβne
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = dord hp β := ⟨(dord hp β).toNat, by omega⟩
  have hβ' : β = algebraMap R F (π ^ d * w) := by
    rw [hβw, map_mul, map_pow, ← hd, zpow_natCast]; ring
  have hdodd : Odd d := ⟨(dord hp t).toNat, by omega⟩
  have h4 : dord hp (4 : F) = 2 * dord hp (2 : F) := by
    have h2F : (2 : F) ≠ 0 := by
      rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
      exact (map_ne_zero_iff _ alg_inj).2 h2
    rw [show (4 : F) = 2 * 2 by norm_num, dord_mul hp h2F h2F]; ring
  have hle : span R {(4 : F)} ≤ span R {β} := by
    rw [← hdef]
    refine (iInf_le _ 1).trans ?_
    rw [show 1 + β - 1 ^ 2 = β by ring]
  have h4mem : (4 : F) ∈ span R {β} := hle (Submodule.mem_span_singleton_self _)
  rw [mem_span_iff hp h4ne hβne] at h4mem
  have hlt : span R {(4 : F)} < span R {algebraMap R F (π ^ d * w)} := by
    rw [← hβ']
    refine lt_of_le_of_ne hle ?_
    intro heq
    have : β ∈ span R {(4 : F)} := by rw [heq]; exact Submodule.mem_span_singleton_self _
    rw [mem_span_iff hp hβne h4ne] at this
    omega
  have h63 := quadDefect_one_add (F := F) h2 hp hw hdodd hlt
  rw [← hβ', hdef] at h63
  rw [← hβ'] at hlt
  exact hlt.ne h63

lemma NF_or [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {c : F} (hc : c ≠ 0) :
    NF (algebraMap R F π) c ∨ NF (algebraMap R F π) (c * algebraMap R F Δ) := by
  obtain ⟨k, u, hu, rfl⟩ := exists_rep hπ hc
  have hk := NF_zpow (alg_pi_ne_zero (R := R) (F := F) hπ) k
  rcases unit_PU h2 hπ hΔ hΔd u hu with h | h
  · exact Or.inl (NF_mul h hk)
  · right
    rw [show algebraMap R F u * algebraMap R F π ^ k * algebraMap R F Δ =
      algebraMap R F u * algebraMap R F Δ * algebraMap R F π ^ k by ring]
    exact NF_mul h hk

lemma NF_xor [HenselianLocalRing R] [Finite (ResidueField R)] (h2 : (2 : R) ≠ 0)
    (hπ : Irreducible π) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {c : F} (hc : c ≠ 0) :
    Xor (NF (algebraMap R F π) c) (NF (algebraMap R F π) (c * algebraMap R F Δ)) := by
  have hnot := not_NF_delta (F := F) h2 hπ hΔ hΔd
  rcases NF_or h2 hπ hΔ hΔd hc with h | h
  · left
    refine ⟨h, fun h' => hnot ?_⟩
    have := NF_mul h' (NF_inv hc h)
    rwa [show c * algebraMap R F Δ * c⁻¹ = algebraMap R F Δ by field_simp] at this
  · right
    refine ⟨h, fun h' => hnot ?_⟩
    have := NF_mul h (NF_inv hc h')
    rwa [show c * algebraMap R F Δ * c⁻¹ = algebraMap R F Δ by field_simp] at this

end NF

section Coord
variable {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*} [AddCommGroup V] [Module F V]
  (Q : QuadraticForm F V) (b : Basis (Fin 2) F V)

lemma bil_symm' (x y : V) : bil Q x y = bil Q y x := by
  have := QuadraticMap.associated_isSymm F Q x y
  exact this

lemma bil_coords (c0 c1 e0 e1 : F) :
    bil Q (c0 • b 0 + c1 • b 1) (e0 • b 0 + e1 • b 1) =
      c0 * e0 * bil Q (b 0) (b 0) + (c0 * e1 + c1 * e0) * bil Q (b 0) (b 1) +
        c1 * e1 * bil Q (b 1) (b 1) := by
  have h10 := bil_symm' Q (b 1) (b 0)
  simp only [bil, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at *
  rw [h10]; ring

lemma Q_coords (c0 c1 : F) :
    Q (c0 • b 0 + c1 • b 1) = c0 ^ 2 * bil Q (b 0) (b 0) + 2 * c0 * c1 * bil Q (b 0) (b 1) +
        c1 ^ 2 * bil Q (b 1) (b 1) := by
  have := bil_coords Q b c0 c1 c0 c1
  have h : bil Q (c0 • b 0 + c1 • b 1) (c0 • b 0 + c1 • b 1) = Q (c0 • b 0 + c1 • b 1) :=
    QuadraticMap.associated_eq_self_apply F Q _
  rw [h] at this; rw [this]; ring

lemma exists_coords (v : V) : ∃ c0 c1 : F, v = c0 • b 0 + c1 • b 1 :=
  ⟨b.repr v 0, b.repr v 1, by
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_two]⟩

lemma det_gram : (gram Q b).det =
    bil Q (b 0) (b 0) * bil Q (b 1) (b 1) - bil Q (b 0) (b 1) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp only [gram, Matrix.of_apply]
  rw [bil_symm' Q (b 1) (b 0)]; ring

lemma rep_iff (g00 g01 g11 x0 x1 γ : F) (ha : g00 * x0 ^ 2 + 2 * x0 * x1 * g01 + g11 * x1 ^ 2 ≠ 0)
    (hd : g00 * g11 - g01 ^ 2 ≠ 0) :
    (∃ c0 c1 : F, g00 * c0 ^ 2 + 2 * c0 * c1 * g01 + g11 * c1 ^ 2 = γ) ↔
      ∃ s t : F, (g00 * x0 ^ 2 + 2 * x0 * x1 * g01 + g11 * x1 ^ 2) *
        (s ^ 2 + (g00 * g11 - g01 ^ 2) * t ^ 2) = γ := by
  set a := g00 * x0 ^ 2 + 2 * x0 * x1 * g01 + g11 * x1 ^ 2 with ha_def
  set d := g00 * g11 - g01 ^ 2 with hd_def
  constructor
  · rintro ⟨c0, c1, h⟩
    refine ⟨(g00 * c0 * x0 + g01 * (c0 * x1 + c1 * x0) + g11 * c1 * x1) / a,
      (g00 * c0 * (g01 * x0 + g11 * x1) + g01 * (c0 * (-(g00 * x0 + g01 * x1)) + c1 * (g01 * x0 + g11 * x1))
        + g11 * c1 * (-(g00 * x0 + g01 * x1))) / (d * a), ?_⟩
    rw [← h]
    field_simp
    simp only [ha_def, hd_def]
    ring
  · rintro ⟨s, t, h⟩
    refine ⟨s * x0 + t * (g01 * x0 + g11 * x1), s * x1 + t * (-(g00 * x0 + g01 * x1)), ?_⟩
    rw [← h]
    simp only [ha_def, hd_def]
    ring

/-- A binary space with $\det$ of the Gram matrix $d \ne 0$ represents $\gamma$ iff $\gamma / a$ is a value of the
norm form $s^2 + d t^2$, for a suitable $a \ne 0$ (namely a nonzero value of the form). -/
lemma rep_NF (h2 : (2 : F) ≠ 0) {d : F} (hd : (gram Q b).det = d) (hd0 : d ≠ 0) :
    ∃ a : F, a ≠ 0 ∧ ∀ γ : F, (∃ x : V, Q x = γ) ↔ NF d (γ / a) := by
  set g00 := bil Q (b 0) (b 0) with hg00
  set g01 := bil Q (b 0) (b 1) with hg01
  set g11 := bil Q (b 1) (b 1) with hg11
  have hdd : g00 * g11 - g01 ^ 2 = d := (det_gram Q b).symm.trans hd
  have hrep : ∀ γ, (∃ x : V, Q x = γ) ↔
      ∃ c0 c1 : F, g00 * c0 ^ 2 + 2 * c0 * c1 * g01 + g11 * c1 ^ 2 = γ := by
    intro γ
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨c0, c1, rfl⟩ := exists_coords b x
      exact ⟨c0, c1, by rw [Q_coords]; ring⟩
    · rintro ⟨c0, c1, h⟩
      exact ⟨c0 • b 0 + c1 • b 1, by rw [Q_coords, ← h]; ring⟩
  obtain ⟨x0, x1, hx⟩ : ∃ x0 x1 : F, g00 * x0 ^ 2 + 2 * x0 * x1 * g01 + g11 * x1 ^ 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e1 : g00 = 0 := by simpa using hcon 1 0
    have e2 : g11 = 0 := by simpa using hcon 0 1
    have e3 : 2 * g01 = 0 := by
      have := hcon 1 1
      rw [e1, e2] at this
      linear_combination this
    have e4 : g01 = 0 := (mul_eq_zero.1 e3).resolve_left h2
    apply hd0
    rw [← hdd, e1, e2, e4]; ring
  refine ⟨g00 * x0 ^ 2 + 2 * x0 * x1 * g01 + g11 * x1 ^ 2, hx, fun γ => ?_⟩
  rw [hrep, rep_iff g00 g01 g11 x0 x1 γ hx (by rw [hdd]; exact hd0), hdd]
  constructor
  · rintro ⟨s, t, h⟩
    exact ⟨s, t, by rw [eq_div_iff hx, ← h]; ring⟩
  · rintro ⟨s, t, h⟩
    exact ⟨s, t, by rw [h, mul_comm]; exact div_mul_cancel₀ γ hx⟩

end Coord

end B63

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)]
variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- **Proposition 63:11** (O'Meara 1963, p. 164): let $V$ be a binary quadratic space over the local field $F$ whose
discriminant is a prime element (here: $d(b_0, b_1) = \det(B(b_i, b_j))$ is a prime element $p$ of $R$ for a base $b$),
and let $\Delta$ be a unit of quadratic defect $4\mathfrak o$. Then for every $\gamma \ne 0$, $V$ represents $\gamma$ or
$\gamma\Delta$ but not both. -/
@[kb "omeara1963" "§63B, 63:11, p. 164 (dV prime: V represents γ or γΔ but not both)"]
theorem represents_xor_of_disc_prime [Invertible (2 : F)] (h2 : (2 : R) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module F V] (Q : QuadraticForm F V) (b : Basis (Fin 2) F V) {p : R} (hp : Irreducible p)
    (hd : (gram Q b).det = algebraMap R F p) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {γ : F} (hγ : γ ≠ 0) :
    Xor (∃ x : V, Q x = γ) (∃ x : V, Q x = γ * algebraMap R F Δ) := by
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  obtain ⟨a, ha, hrep⟩ := B63.rep_NF Q b h2F hd (alg_pi_ne_zero (R := R) (F := F) hp)
  rw [hrep γ, hrep (γ * algebraMap R F Δ), mul_div_right_comm]
  exact B63.NF_xor h2 hp hΔ hΔd (div_ne_zero hγ ha)

/-- **Corollary 63:11a, first part** (O'Meara 1963, p. 165): $(\varepsilon, \Delta)_\mathfrak p = 1$ for every unit
$\varepsilon$, where $\Delta$ is a unit of quadratic defect $4\mathfrak o$. -/
@[kb "omeara1963" "§63B, 63:11a, p. 165 ((ε, Δ) = 1 for units ε)"]
theorem hilbertSymbol_unit_delta (h2 : (2 : R) ≠ 0) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {ε : R} (hε : IsUnit ε) :
    hilbertSymbol F (algebraMap R F ε) (algebraMap R F Δ) = 1 := by
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  exact (hilbertSymbol_eq_one_iff_conic F h2F (alg_ne_zero_of_unit hε) (alg_ne_zero_of_unit hΔ)).2
    (B63.exists_conic_unit h2 hΔ hΔd hε)

/-- **Corollary 63:11a, second part** (O'Meara 1963, p. 165): $(\pi, \Delta)_\mathfrak p = -1$ for a prime element
$\pi$. -/
@[kb "omeara1963" "§63B, 63:11a, p. 165 ((π, Δ) = −1)"]
theorem hilbertSymbol_prime_delta (h2 : (2 : R) ≠ 0) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {π : R} (hπ : Irreducible π) :
    hilbertSymbol F (algebraMap R F π) (algebraMap R F Δ) = -1 := by
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  have hpm : hilbertSymbol F (algebraMap R F π) (algebraMap R F Δ) = 1 ∨
      hilbertSymbol F (algebraMap R F π) (algebraMap R F Δ) = -1 := by
    unfold hilbertSymbol; split_ifs <;> simp
  refine hpm.resolve_left fun h1 => ?_
  obtain ⟨x, y, hxy⟩ := (hilbertSymbol_eq_one_iff_conic F h2F (alg_pi_ne_zero (R := R) (F := F) hπ)
    (alg_ne_zero_of_unit hΔ)).1 h1
  have hπ' : Irreducible (-π) := by
    have := (irreducible_isUnit_mul (isUnit_one.neg : IsUnit (-1 : R))).2 hπ
    simpa using this
  refine B63.not_NF_delta h2 hπ' hΔ hΔd ?_
  by_cases hy : y = 0
  · exfalso
    subst hy
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hxy
    have hpx : algebraMap R F π * x ^ 2 = 1 := by linear_combination hxy
    have h1 : dord hπ (algebraMap R F π * x ^ 2) = 1 + 2 * dord hπ x := by
      have hp1 : dord hπ (algebraMap R F π) = 1 := by
        have := dord_zpow (F := F) hπ 1
        rwa [zpow_one] at this
      rw [dord_mul hπ (alg_pi_ne_zero (R := R) (F := F) hπ) (pow_ne_zero 2 hx), dord_sq hπ hx, hp1]
    have h0 : dord hπ (1 : F) = 0 := by simpa using dord_unit (F := F) hπ (u := 1) isUnit_one
    rw [hpx, h0] at h1
    omega
  · refine ⟨1 / y, x / y, ?_⟩
    rw [map_neg]
    field_simp
    linear_combination -hxy

/-- **Corollary 63:11b, first part** (O'Meara 1963, p. 165): the quaternion algebra
$\left(\frac{\pi,\Delta}{F}\right)$ is a division algebra. -/
@[kb "omeara1963" "§63B, 63:11b, p. 165 ((π, Δ) is a division algebra)"]
theorem quat_prime_delta_division (h2 : (2 : R) ≠ 0) {Δ : R} (hΔ : IsUnit Δ)
    (hΔd : quadDefect R (algebraMap R F Δ) = span R {(4 : F)}) {π : R} (hπ : Irreducible π) :
    ∀ q : ℍ[F,algebraMap R F π,algebraMap R F Δ], q ≠ 0 → IsUnit q := by
  have h2F : (2 : F) ≠ 0 := by
    rw [show (2 : F) = algebraMap R F 2 from (map_ofNat _ 2).symm]
    exact (map_ne_zero_iff _ alg_inj).2 h2
  exact (Quat.hilbertSymbol_eq_neg_one_iff_division h2F (alg_pi_ne_zero (R := R) (F := F) hπ)
    (alg_ne_zero_of_unit hΔ)).1 (hilbertSymbol_prime_delta h2 hΔ hΔd hπ)

end QuadFormsKB.OMeara
