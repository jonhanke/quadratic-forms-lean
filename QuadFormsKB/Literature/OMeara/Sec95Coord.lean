/-
# O'Meara §95: coordinates in a normalized base of an anisotropic quaternary space

**Setting.** $R$ is a complete discrete valuation ring (O'Meara's $\mathfrak o$; `IsAdicComplete`) with finite
residue field and fraction field $F$, non-dyadic ($2 \in R^\times$), $\pi$ a prime element; $(V, Q)$ an anisotropic
quadratic space over $F$ with a normalized orthogonal base `N : S95.NormalBasis Q π`
($Q(e_0) = a_0$, $Q(e_1) = a_1$, $Q(e_2) = \pi a_2$, $Q(e_3) = \pi a_3$, $a_i \in \mathfrak u$; `Sec95Basis.lean`).

**Proves** the two facts behind step 4 of the proof of O'Meara's 95:1 (1973 printing, p. 282): the lattice
$L = \mathfrak oe_0 + \cdots + \mathfrak oe_3$ is $\{z \in V : Q(z) \in \mathfrak o\}$ (`NormalBasis.integral`: every
coordinate of such $z$ is integral), and $L^{\mathfrak p} = \mathfrak pe_0 + \mathfrak pe_1 + \mathfrak oe_2 +
\mathfrak oe_3$ is $\{z \in L : Q(z) \in \mathfrak p\}$ (`NormalBasis.mem_pi`: the coordinates $0, 1$ of such $z$ lie
in $\mathfrak p$). Both rest on the anisotropy of $\langle a_0, a_1\rangle$ and $\langle a_2, a_3\rangle$ modulo
$\mathfrak p$ (`NormalBasis.isUnit_add01`, `NormalBasis.isUnit_add23`).
-/
import QuadFormsKB.Literature.OMeara.Sec95Basis
import QuadFormsKB.Literature.OMeara.Sec63A
import QuadFormsKB.Literature.OMeara.Sec92Class

open QuadraticMap Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace S95

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Fintype (ResidueField R)] [DecidableEq (ResidueField R)] [IsAdicComplete (maximalIdeal R) R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {Q : QuadraticForm F V} {π : R}

namespace NormalBasis

variable (N : NormalBasis Q π)

/-- In an anisotropic space $-a_0a_1$ is not a square in $R$ (else $se_0 + a_0e_1$ would be isotropic). -/
theorem not_isSquare_neg_mul01 (hQ : Q.Anisotropic) : ¬ IsSquare (-(N.a 0 * N.a 1)) := by
  rintro ⟨s, hs⟩
  set c : Fin 4 → F := ![algebraMap R F s, algebraMap R F (N.a 0), 0, 0] with hc
  have h0 : algebraMap R F (N.a 0 * (s * s + N.a 0 * N.a 1)) = 0 := by
    rw [show s * s + N.a 0 * N.a 1 = 0 by linear_combination -hs]; simp
  have hv := hQ (∑ i, c i • N.e i) (by
    rw [N.Q_eq]
    simp only [map_mul, map_add] at h0
    simp [hc]
    linear_combination h0)
  have h1 := congrArg (fun v => N.e.repr v 1) hv
  simp only [N.e.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, hc] at h1
  simp at h1
  exact (N.unit 0).ne_zero h1

/-- In an anisotropic space $-a_2a_3$ is not a square in $R$. -/
theorem not_isSquare_neg_mul23 (hQ : Q.Anisotropic) : ¬ IsSquare (-(N.a 2 * N.a 3)) := by
  rintro ⟨s, hs⟩
  set c : Fin 4 → F := ![0, 0, algebraMap R F s, algebraMap R F (N.a 2)] with hc
  have h0 : algebraMap R F (N.a 2 * (s * s + N.a 2 * N.a 3)) = 0 := by
    rw [show s * s + N.a 2 * N.a 3 = 0 by linear_combination -hs]; simp
  have hv := hQ (∑ i, c i • N.e i) (by
    rw [N.Q_eq]
    simp only [map_mul, map_add] at h0
    simp [hc]
    right
    linear_combination h0)
  have h1 := congrArg (fun v => N.e.repr v 3) hv
  simp only [N.e.repr_sum_self, map_zero, Finsupp.coe_zero, Pi.zero_apply, hc] at h1
  simp at h1
  exact (N.unit 2).ne_zero h1

/-- Binary forms $au^2 + bv^2$ with $-ab$ a nonsquare are unit-valued off $\mathfrak p$ (Hensel). -/
lemma isUnit_binary (h2 : IsUnit (2 : R)) (hπ : Irreducible π) {a b u v : R} (ha : IsUnit a)
    (hb : IsUnit b) (hab : ¬ IsSquare (-(a * b))) (h : ¬ (π ∣ u ∧ π ∣ v)) :
    IsUnit (a * u ^ 2 + b * v ^ 2) := by
  by_contra hnu
  have h2' : ¬ π ∣ 2 := fun h => hπ.not_isUnit (isUnit_of_dvd_unit h h2)
  have hres : ∀ x : R, residue R x = 0 ↔ π ∣ x := fun x =>
    LocalDensity.DVR.residue_eq_zero_iff_dvd hπ x
  have hne : ∀ x : R, IsUnit x → residue R x ≠ 0 := fun x hx h0 => by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h0; exact h0 hx
  have h0 : residue R (a * u ^ 2 + b * v ^ 2) = 0 := by
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]; exact hnu
  simp only [map_add, map_mul, map_pow] at h0
  have ha' := hne a ha
  have hb' := hne b hb
  have hu : residue R u ≠ 0 := by
    intro hu0
    rw [hu0] at h0
    have : residue R v = 0 := by simpa [hb'] using h0
    exact h ⟨(hres u).1 hu0, (hres v).1 this⟩
  have hv : residue R v ≠ 0 := by
    intro hv0
    rw [hv0] at h0
    simp [ha', hu] at h0
  obtain ⟨z, hz⟩ := Lattices.Nbr.exists_sq_eq_of_residue hπ h2' (-(a * b))
    (s := residue R b * residue R v / residue R u) (by simp [hb', hv, hu])
    (by
      simp only [map_neg, map_mul]
      rw [div_pow, eq_div_iff (pow_ne_zero 2 hu)]
      linear_combination (-(residue R b)) * h0)
  exact hab ⟨z, by rw [← hz]; ring⟩

/-- $a_0u^2 + a_1v^2$ is a unit when $u, v \in R$ are not both in $\mathfrak p$ (the binary form
$\langle a_0, a_1\rangle$ is anisotropic modulo $\mathfrak p$, by the Local Square Theorem). -/
theorem isUnit_add01 (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {u v : R}
    (h : ¬ (π ∣ u ∧ π ∣ v)) : IsUnit (N.a 0 * u ^ 2 + N.a 1 * v ^ 2) :=
  isUnit_binary h2 hπ (N.unit 0) (N.unit 1) (N.not_isSquare_neg_mul01 hQ) h

/-- $a_2u^2 + a_3v^2$ is a unit when $u, v \in R$ are not both in $\mathfrak p$. -/
theorem isUnit_add23 (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {u v : R}
    (h : ¬ (π ∣ u ∧ π ∣ v)) : IsUnit (N.a 2 * u ^ 2 + N.a 3 * v ^ 2) :=
  isUnit_binary h2 hπ (N.unit 2) (N.unit 3) (N.not_isSquare_neg_mul23 hQ) h

/-- A unit plus a multiple of $\pi$ is a unit. -/
lemma isUnit_add_mul_pi (hπ : Irreducible π) {x y : R} (hx : IsUnit x) : IsUnit (x + π * y) := by
  by_contra h
  have h1 : x + π * y ∈ maximalIdeal R := by rwa [mem_maximalIdeal, mem_nonunits_iff]
  have h2 : π * y ∈ maximalIdeal R :=
    Ideal.mul_mem_right _ _ (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hπ.not_isUnit)
  have := (maximalIdeal R).sub_mem h1 h2
  rw [add_sub_cancel_right, mem_maximalIdeal, mem_nonunits_iff] at this
  exact this hx

/-- The integral value $q = a_0c_0^2 + a_1c_1^2 + \pi(a_2c_2^2 + a_3c_3^2)$ is a unit, or $\pi$ times a
unit with $\pi \mid c_0, c_1$. -/
lemma q_cases (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {c : Fin 4 → R}
    (h : ¬ (π ∣ c 0 ∧ π ∣ c 1 ∧ π ∣ c 2 ∧ π ∣ c 3)) :
    (¬ (π ∣ c 0 ∧ π ∣ c 1) ∧
        IsUnit (N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 + π * (N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2))) ∨
      (π ∣ c 0 ∧ π ∣ c 1 ∧ ∃ w, IsUnit w ∧
        N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 + π * (N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2) = π * w) := by
  by_cases h01 : π ∣ c 0 ∧ π ∣ c 1
  · right
    obtain ⟨⟨d0, hd0⟩, ⟨d1, hd1⟩⟩ := h01
    have h23 : ¬ (π ∣ c 2 ∧ π ∣ c 3) := fun h' => h ⟨⟨d0, hd0⟩, ⟨d1, hd1⟩, h'⟩
    refine ⟨⟨d0, hd0⟩, ⟨d1, hd1⟩, _,
      isUnit_add_mul_pi hπ (N.isUnit_add23 h2 hπ hQ h23)
        (y := N.a 0 * d0 ^ 2 + N.a 1 * d1 ^ 2), ?_⟩
    rw [hd0, hd1]; ring
  · left
    exact ⟨h01, isUnit_add_mul_pi hπ (N.isUnit_add01 h2 hπ hQ h01)⟩

open Classical in
/-- Rescaling the coordinates of $z \ne 0$ by a power of $\pi$ makes them integral, not all divisible by $\pi$. -/
lemma exists_scale (hπ : Irreducible π) {z : V} (hz : z ≠ 0) :
    ∃ (m : ℤ) (c : Fin 4 → R), (∀ i, N.e.repr z i = algebraMap R F (c i) * algebraMap R F π ^ m) ∧
      ¬ (π ∣ c 0 ∧ π ∣ c 1 ∧ π ∣ c 2 ∧ π ∣ c 3) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  set x : Fin 4 → F := fun i => N.e.repr z i with hx
  have hex : ∃ i, x i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hz
    rw [← N.e.sum_repr z]
    exact Finset.sum_eq_zero fun i _ => by rw [show N.e.repr z i = 0 from hall i, zero_smul]
  set S : Finset (Fin 4) := Finset.univ.filter fun i => x i ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hS, hi]⟩
  set m : ℤ := S.inf' hSne (fun i => dord hπ (x i)) with hm
  obtain ⟨j, hjS, hjm⟩ := Finset.exists_mem_eq_inf' hSne (fun i => dord hπ (x i))
  have hxj : x j ≠ 0 := by simpa [hS] using hjS
  have hint : ∀ i, ∃ c : R, algebraMap R F c = x i * algebraMap R F π ^ (-m) := by
    intro i
    by_cases hi : x i = 0
    · exact ⟨0, by simp [hi]⟩
    · have hiS : i ∈ S := by simp [hS, hi]
      have hle : m ≤ dord hπ (x i) := Finset.inf'_le _ hiS
      have hpne : algebraMap R F π ^ (-m) ≠ 0 := zpow_ne_zero _ hne
      refine exists_alg_of_nonneg hπ (mul_ne_zero hi hpne) ?_
      rw [dord_mul hπ hi hpne, dord_zpow]; omega
  choose c hc using hint
  have hcoord : ∀ i, N.e.repr z i = algebraMap R F (c i) * algebraMap R F π ^ m := by
    intro i
    rw [hc i, mul_assoc, ← zpow_add₀ hne]; simp [hx]
  refine ⟨m, c, hcoord, ?_⟩
  rintro ⟨hj0, hj1, hj2, hj3⟩
  have hcj : π ∣ c j := by fin_cases j <;> assumption
  have hcj0 : c j ≠ 0 := by
    intro h0
    have := hc j
    rw [h0, map_zero] at this
    exact (mul_ne_zero hxj (zpow_ne_zero _ hne)) this.symm
  obtain ⟨d, hd⟩ := hcj
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd; exact hcj0 hd
  have hdord : dord hπ (algebraMap R F (c j)) = 0 := by
    rw [hc j, dord_mul hπ hxj (zpow_ne_zero _ hne), dord_zpow, ← hjm]; ring
  have hpi : dord hπ (algebraMap R F π) = 1 := dord_eq hπ (u := 1) isUnit_one (k := 1) (by simp)
  rw [hd, map_mul, dord_mul hπ hne ((map_ne_zero_iff _ alg_inj).2 hd0), hpi] at hdord
  have := dord_alg_nonneg (F := F) hπ hd0
  omega

/-- The value of $Q$ in rescaled coordinates, and its order. -/
lemma dord_Q (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {z : V} (hz : z ≠ 0) :
    ∃ (m : ℤ) (c : Fin 4 → R), (∀ i, N.e.repr z i = algebraMap R F (c i) * algebraMap R F π ^ m) ∧
      ((dord hπ (Q z) = 2 * m ∧ ¬ (π ∣ c 0 ∧ π ∣ c 1)) ∨
        (dord hπ (Q z) = 2 * m + 1 ∧ π ∣ c 0 ∧ π ∣ c 1)) := by
  have hne := alg_pi_ne_zero (R := R) (F := F) hπ
  obtain ⟨m, c, hcoord, hnd⟩ := N.exists_scale hπ hz
  refine ⟨m, c, hcoord, ?_⟩
  have hp : (algebraMap R F π ^ m) ^ 2 = algebraMap R F π ^ (2 * m) := by
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have hQz : ∀ q : R, q = N.a 0 * c 0 ^ 2 + N.a 1 * c 1 ^ 2 +
      π * (N.a 2 * c 2 ^ 2 + N.a 3 * c 3 ^ 2) →
      Q z = algebraMap R F q * algebraMap R F π ^ (2 * m) := by
    intro q hq
    rw [← hp, N.Q_repr z, hq, hcoord 0, hcoord 1, hcoord 2, hcoord 3]
    simp only [map_add, map_mul, map_pow]; ring
  rcases N.q_cases h2 hπ hQ hnd with ⟨h01, hu⟩ | ⟨h0, h1, w, hw, hqw⟩
  · left
    exact ⟨dord_eq hπ hu (hQz _ rfl), h01⟩
  · right
    refine ⟨dord_eq hπ hw (k := 2 * m + 1) ?_, h0, h1⟩
    rw [hQz (π * w) hqw.symm, zpow_add₀ hne, map_mul]; simp; ring

/-- **$\{z : Q(z) \in \mathfrak o\} = \mathfrak oe_0 + \cdots + \mathfrak oe_3$** (O'Meara 1973, proof of 95:1,
step 4, p. 282: $L = L_1 \perp L_2$ is the unique $\mathfrak o$-maximal lattice on $V$): if $Q(z) \in \mathfrak o$
then every coordinate of $z$ in the base $e$ is integral. -/
theorem integral (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {z : V} {r : R}
    (hz : Q z = algebraMap R F r) (i : Fin 4) : ∃ c : R, N.e.repr z i = algebraMap R F c := by
  by_cases hz0 : z = 0
  · exact ⟨0, by simp [hz0]⟩
  obtain ⟨m, c, hcoord, hcase⟩ := N.dord_Q h2 hπ hQ hz0
  have hr : r ≠ 0 := by
    rintro rfl
    exact hz0 (hQ z (by simpa using hz))
  have hnn := dord_alg_nonneg (F := F) hπ hr
  rw [← hz] at hnn
  have hm : 0 ≤ m := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, by omega⟩
  refine ⟨c i * π ^ n, ?_⟩
  rw [hcoord i, ← hn, zpow_natCast]; simp

/-- **$\{z \in L : Q(z) \in \mathfrak p\} = \mathfrak pe_0 + \mathfrak pe_1 + \mathfrak oe_2 + \mathfrak oe_3$**
(O'Meara 1973, proof of 95:1, step 4, p. 282: $L^{\mathfrak p} = \mathfrak pL_1 \perp L_2$): if $Q(z) \in \mathfrak p$
then the coordinates $0$ and $1$ of $z$ lie in $\mathfrak p$. -/
theorem mem_pi (h2 : IsUnit (2 : R)) (hπ : Irreducible π) (hQ : Q.Anisotropic) {z : V} {r : R}
    (hz : Q z = algebraMap R F (π * r)) (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    ∃ c : R, N.e.repr z i = algebraMap R F (π * c) := by
  by_cases hz0 : z = 0
  · exact ⟨0, by simp [hz0]⟩
  obtain ⟨m, c, hcoord, hcase⟩ := N.dord_Q h2 hπ hQ hz0
  have hr : π * r ≠ 0 := by
    intro h0
    rw [h0] at hz
    exact hz0 (hQ z (by simpa using hz))
  have hnn := dord_alg_nonneg (F := F) hπ hr
  have hpi : dord hπ (algebraMap R F π) = 1 := dord_eq hπ (u := 1) isUnit_one (k := 1) (by simp)
  have hrne : r ≠ 0 := right_ne_zero_of_mul hr
  have hdq : 1 ≤ dord hπ (Q z) := by
    rw [hz, map_mul, dord_mul hπ (alg_pi_ne_zero (R := R) (F := F) hπ)
      ((map_ne_zero_iff _ alg_inj).2 hrne), hpi]
    have := dord_alg_nonneg (F := F) hπ hrne
    omega
  have hdiv : ∀ j : Fin 4, (j = 0 ∨ j = 1) → (π ∣ c j ∨ 1 ≤ m) := by
    intro j hj
    rcases hcase with ⟨h, hnd⟩ | ⟨h, h0, h1⟩
    · right; omega
    · by_cases hm : 1 ≤ m
      · right; exact hm
      · left; rcases hj with rfl | rfl <;> assumption
  have hm0 : 0 ≤ m := by rcases hcase with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  rcases hdiv i hi with ⟨d, hd⟩ | hm1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, by omega⟩
    refine ⟨d * π ^ n, ?_⟩
    rw [hcoord i, ← hn, zpow_natCast, hd]; simp; ring
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = m - 1 := ⟨(m - 1).toNat, by omega⟩
    refine ⟨c i * π ^ n, ?_⟩
    have hm' : m = (n : ℤ) + 1 := by omega
    rw [hcoord i, hm', zpow_add₀ (alg_pi_ne_zero (R := R) (F := F) hπ), zpow_natCast, zpow_one]
    simp; ring

end NormalBasis

end S95

end QuadFormsKB.OMeara
