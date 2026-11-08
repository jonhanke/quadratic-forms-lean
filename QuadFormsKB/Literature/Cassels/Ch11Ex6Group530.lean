/-
# Cassels, Ch. 11, Example 6 (i), (ii): $P = \{2\}$, $|G| = 2$, two spinor genera, $g(w)$

J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 11, Example 6, p. 252 (`cassels1978`).

**Layer.** $f = x_0^2 + x_1^2 + 16x_2^2$ (`ex6f`), the lattice $\Lambda = \mathbb Z^3$ (`stdLat`), Cassels' group
$G = R/ST$ of (3.15) for $P = \{2\}$ (`CasselsG`) and $g(c)$ of (4.5) (`casselsg`).

**Route (Cassels' own).** (i) Away from $2$ the lattice is unimodular ($\det H = 128$), so (3.7) holds for $P = \{2\}$
by Lemma 3.3 (`casselsCond_std`). At $2$, $\theta(\Lambda_2) = \{a : a\mathbb Q_2^{\times2} \in H\}$ with
$H = \{1, 2, 5, 10\}$ (`mem_theta6_iff`). By $R = XT$ (`exists_casselsX_mul_casselsT`) every element of $G$ is the
class of a $2$-adic unit $x$; $x \equiv 1 \pmod 4$ gives $x \in H$, $x \equiv 3 \pmod 4$ gives $-x \in H$. So $G$ is
$\{1, [-1]\}$, and $[-1] \ne 1$ because the character "square class at $2$ modulo $H$" kills $ST$ ($f$ is definite,
so $j = 1$; `not_mem_casselsST_of_subgroup`). By Theorem 3.1 the genus has two (proper) spinor genera. (ii) For odd
$w > 0$, $g(w)$ is the class of the unit $w$, trivial iff $w \in H$ iff $w \equiv 1 \pmod 4$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Ex6Spinor530b
import QuadFormsKB.Literature.Cassels.Ch11SpinorGeneraCount530
import QuadFormsKB.Literature.Cassels.Ch11Ex35
import QuadFormsKB.Literature.ConwaySloane.Section9TwoSpinorGenera
import QuadFormsKB.Literature.ConwaySloane.Section9Group

open NumberField IsDedekindDomain WithZero Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Ex4

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.ConwaySloane

/-! ### The form over $\mathbb Q$ and its Gram matrix -/

/-- $f$ of Example 6 is the form of the Gram matrix $A_6 = \mathrm{diag}(1, 1, 16)$. -/
theorem ex6f_eq_gramForm : ex6f = Cassels.Ch8Ex2.gramForm A6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ex6f, QuadForm.diag, Cassels.Ch8Ex2.gramForm, A6]

/-- The rational form of Example 6. -/
abbrev ex6Q : QuadForm ℚ 3 := ex6f.map (Int.castRingHom ℚ)

theorem ex6Q_eq : ex6Q = csQ A6 := by rw [ex6Q, ex6f_eq_gramForm]

theorem ex6Q_nondeg : ex6Q.Nondegenerate :=
  Lattices.nondegenerate_map_of_det_ne_zero ex6f (by rw [hessian_det_ex6f]; norm_num)

/-- Equal forms have equal local spinor norm groups (transport along an equality). -/
theorem localSpinorNormGroup_congr {n : ℕ} {Q Q' : QuadForm ℚ n} (e : Q = Q') (hQ : Q.Nondegenerate)
    (hQ' : Q'.Nondegenerate) (v : HeightOneSpectrum (𝓞 ℚ)) (L : Lat ℚ n) :
    localSpinorNormGroup Q hQ v L = localSpinorNormGroup Q' hQ' v L := by
  subst e; rfl

/-- $\theta(\Lambda_2)$ for Example 6: the square classes in $H = \{1, 2, 5, 10\}$. Arguments: `h2` ($v \mid 2$),
`a` the unit. -/
theorem mem_theta_ex6_two {v : HeightOneSpectrum (𝓞 ℚ)} (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal)
    (a : (v.adicCompletion ℚ)ˣ) :
    a ∈ localSpinorNormGroup ex6Q ex6Q_nondeg v stdLat ↔ SqClass.mk a ∈ H6 v := by
  rw [localSpinorNormGroup_congr ex6Q_eq ex6Q_nondeg A6_nondeg]
  exact mem_theta6_iff h2 a

/-- $f$ is positive definite, so not indefinite (Cassels' $j = 1$). -/
theorem not_isIndefinite_ex6Q : ¬ IsIndefinite ex6Q := by
  rintro ⟨w, y, hy0, hy⟩
  have hw : w.IsReal := IsTotallyReal.isReal w
  let ψ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hy' : y 0 ^ 2 + y 1 ^ 2 + 16 * y 2 ^ 2 = 0 := by
    rw [← hy]
    simp [QuadForm.evalIn, ex6Q, QuadForm.map, ex6f, QuadForm.diag, Matrix.diagonal_apply, Fin.sum_univ_three]
    ring
  have h0 := congrArg ψ hy'
  simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h0
  set a := ψ (y 0)
  set b := ψ (y 1)
  set c := ψ (y 2)
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  apply hy0
  funext i
  fin_cases i
  · show y 0 = 0; exact ψ.injective (by rw [map_zero]; exact ha)
  · show y 1 = 0; exact ψ.injective (by rw [map_zero]; exact hb)
  · show y 2 = 0; exact ψ.injective (by rw [map_zero]; exact hc)

theorem casselsJ_ex6Q : casselsJ ex6Q = 1 := by
  simp [casselsJ, not_isIndefinite_ex6Q]

/-! ### $2$-adic units modulo $H$ -/

section Two

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "F2" => v.adicCompletion ℚ
local notation "𝔬" => v.adicCompletionIntegers ℚ

/-- A $2$-adic unit is $1 + 4k$ or $3 + 4k$ with $k \in \mathbb Z_2$. Arguments: `h2` ($v \mid 2$), `x` the unit. -/
theorem unit_one_or_three (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x : F2) (hx : Valued.v x = 1) :
    ∃ k : 𝔬, x = ((1 + 4 * k : 𝔬) : F2) ∨ x = ((3 + 4 * k : 𝔬) : F2) := by
  let y : 𝔬 := ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hx.le⟩
  have hu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hx
  have hxy : x = (y : F2) := rfl
  obtain ⟨a, ha⟩ := Rl.exists h2 y
  rcases ha.unit_od h2 hu with rfl | rfl | rfl | rfl
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 1) (by simpa using ha)
    exact ⟨2 * m, Or.inl (by rw [hxy, hm]; congr 1; push_cast; ring)⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 3) (by simpa using ha)
    exact ⟨2 * m, Or.inr (by rw [hxy, hm]; congr 1; push_cast; ring)⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 5) (by simpa using ha)
    exact ⟨1 + 2 * m, Or.inl (by rw [hxy, hm]; congr 1; push_cast; ring)⟩
  · obtain ⟨m, hm⟩ := Rl.of_cast (n := 7) (by simpa using ha)
    exact ⟨1 + 2 * m, Or.inr (by rw [hxy, hm]; congr 1; push_cast; ring)⟩

theorem coe_three_add_four (k : 𝔬) : ((3 + 4 * k : 𝔬) : F2) = 3 + 4 * (k : F2) := by
  push_cast; rw [coe_three6, coe_four6]

theorem coe_one_add_four (k : 𝔬) : ((1 + 4 * k : 𝔬) : F2) = 1 + 4 * (k : F2) := by
  push_cast; rw [coe_four6]

theorem sqClass_mk_eq (x : F2ˣ) : SqClass.mk x = sqClassOf (x : F2) := by
  rw [sqClassOf_of_ne_zero x.ne_zero]; congr 1; exact Units.ext rfl

/-- A $2$-adic unit $x$ has $x \in H$ or $-x \in H$, and not both of $x \equiv 3 \pmod 4$ and $x \in H$. -/
theorem unit_mem_H6_or_neg (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) (x : F2ˣ) (hx : Valued.v (x : F2) = 1) :
    SqClass.mk x ∈ H6 v ∨ SqClass.mk (-x) ∈ H6 v := by
  obtain ⟨k, hk | hk⟩ := unit_one_or_three h2 _ hx
  · left
    rw [sqClass_mk_eq, hk, coe_one_add_four]
    exact one_add_four_mem_H6 h2 k
  · right
    rw [sqClass_mk_eq, Units.val_neg, hk, coe_three_add_four]
    have := one_add_four_mem_H6 h2 (-1 - k)
    convert this using 2
    push_cast; ring

/-- $-1 \notin H$. -/
theorem neg_one_not_mem_H6 (h2 : (2 : 𝓞 ℚ) ∈ v.asIdeal) : SqClass.mk (-1 : F2ˣ) ∉ H6 v := by
  rw [sqClass_mk_eq]
  have := three_add_four_not_mem_H6 h2 (-1)
  convert this using 2
  push_cast; norm_num

end Two

/-! ### The group $G$ for $P = \{2\}$ -/

section Group

variable (v₂ : HeightOneSpectrum (𝓞 ℚ)) (hv₂ : Rat.HeightOneSpectrum.natGenerator v₂ = 2)

include hv₂

/-- Cassels' condition (3.7) for $P = \{2\}$: away from $2$, $\theta(\Lambda_v)$ is the group of unit square classes
(Lemma 3.3, the lattice being unimodular at odd $p$). -/
theorem ex6_cond :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ ({v₂} : Finset _) → ∀ u : (v.adicCompletion ℚ)ˣ,
      u ∈ localSpinorNormGroup ex6Q ex6Q_nondeg v stdLat ↔ IsUnitSqClass v (SqClass.mk u) := by
  refine casselsCond_std (by norm_num) ex6f ex6Q_nondeg {v₂} fun v hv hd => hv ?_
  rw [hessian_det_ex6f] at hd
  have hp := Rat.HeightOneSpectrum.prime_natGenerator v
  have hd' : primeOf v ∣ 2 ^ 8 := by exact_mod_cast hd
  have h2 : primeOf v = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd')
  rw [Finset.mem_singleton]
  exact natGenerator_inj' (h2.trans hv₂.symm)

theorem two_mem_v₂ : (2 : 𝓞 ℚ) ∈ v₂.asIdeal := (two_mem_iff_natGenerator v₂).mpr hv₂

/-- The family $-1 \in R$ is not in $ST$. -/
theorem ex6_neg_one_not_mem :
    (fun _ => -1 : CasselsR ({v₂} : Finset _)) ∉ casselsST ex6Q ex6Q_nondeg stdLat {v₂} := by
  have h2 := two_mem_v₂ v₂ hv₂
  let q : ({v₂} : Finset _) := ⟨v₂, Finset.mem_singleton_self _⟩
  refine not_mem_casselsST_of_subgroup ex6Q ex6Q_nondeg stdLat {v₂} (by norm_num) q (H6 v₂) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [sqClass_mk_eq]
    have : ((primeUnit ({v₂} : Finset _) q : (v₂.adicCompletion ℚ)ˣ) : v₂.adicCompletion ℚ) = 2 := by
      rw [primeUnit, casselsDiag_apply]
      simp [natGenUnit, q, hv₂]
    rw [this]; exact two_mem_H6
  · intro A hA
    exact (mem_theta_ex6_two h2 A).mp hA
  · intro p hpq
    exact absurd (Subtype.ext (Finset.mem_singleton.mp p.2)) hpq
  · rw [casselsJ_ex6Q, map_one, Pi.one_apply,
      show SqClass.mk (1 : (v₂.adicCompletion ℚ)ˣ) = 1 from map_one (sqClassHom _)]
    exact (H6 v₂).one_mem
  · intro p
    simp
  · exact neg_one_not_mem_H6 h2

/-- **$|G| = 2$** (Cassels, Ch. 11, Example 6 (i)): for $P = \{2\}$ the group $G = R/ST$ has two elements, $1$ and the
class of $-1$. -/
theorem ex6_card_casselsG :
    Nat.card (CasselsG ex6Q ex6Q_nondeg stdLat ({v₂} : Finset _)) = 2 := by
  classical
  have h2 := two_mem_v₂ v₂ hv₂
  set P : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v₂} with hP
  let q : P := ⟨v₂, Finset.mem_singleton_self _⟩
  have hPq : ∀ p : P, p = q := fun p => Subtype.ext (Finset.mem_singleton.mp p.2)
  let x₀ : CasselsR P := fun _ => -1
  have hS : ∀ r : CasselsR P, SqClass.mk (r q) ∈ H6 v₂ → r ∈ casselsS ex6Q ex6Q_nondeg stdLat P := by
    intro r hr
    rw [casselsS, Subgroup.mem_pi]
    intro p _
    obtain rfl := (hPq p).symm
    exact (mem_theta_ex6_two h2 _).mpr hr
  have hupper : ∀ r : CasselsR P, r ∈ casselsST ex6Q ex6Q_nondeg stdLat P ∨
      r * x₀⁻¹ ∈ casselsST ex6Q ex6Q_nondeg stdLat P := by
    intro r
    obtain ⟨x, hx, t, ht, rfl⟩ := exists_casselsX_mul_casselsT ex6Q ex6Q_nondeg P (by norm_num) r
    have hT : casselsDiag P t ∈ casselsST ex6Q ex6Q_nondeg stdLat P :=
      Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
    rcases unit_mem_H6_or_neg h2 (x q) (hx q) with h | h
    · left
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hS x h)) hT
    · right
      have hx' : x * x₀⁻¹ ∈ casselsST ex6Q ex6Q_nondeg stdLat P := by
        refine Subgroup.mem_sup_left (hS _ ?_)
        convert h using 2
        show x q * (-1)⁻¹ = -x q
        simp
      rw [show x * casselsDiag P t * x₀⁻¹ = x * x₀⁻¹ * casselsDiag P t from mul_right_comm _ _ _]
      exact Subgroup.mul_mem _ hx' hT
  have hnot := ex6_neg_one_not_mem v₂ hv₂
  rw [Nat.card_eq_two_iff]
  refine ⟨1, QuotientGroup.mk x₀, ?_, ?_⟩
  · intro h
    exact hnot ((QuotientGroup.eq_one_iff _).mp h.symm)
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction g using QuotientGroup.induction_on with
    | H r =>
      rcases hupper r with h | h
      · left
        exact (QuotientGroup.eq_one_iff r).mpr h
      · right
        rw [QuotientGroup.eq]
        have := Subgroup.inv_mem _ h
        rwa [_root_.mul_inv_rev, inv_inv, mul_comm] at this

/-- **$g(w)$ for odd $w > 0$** (Cassels, Ch. 11, Example 6 (ii)): $g(w) = 1$ in $G$ iff $w \equiv 1 \pmod 4$.
Arguments: `w` the odd positive integer (`hw`, `hodd`). -/
theorem ex6_casselsg_odd (w : ℕ) (hw : 0 < w) (hodd : w % 2 = 1) :
    casselsg ex6Q ex6Q_nondeg stdLat ({v₂} : Finset _) (Units.mk0 (w : ℚ) (by exact_mod_cast hw.ne')) = 1 ↔
      w % 4 = 1 := by
  classical
  have h2 := two_mem_v₂ v₂ hv₂
  set P : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v₂} with hP
  let q : P := ⟨v₂, Finset.mem_singleton_self _⟩
  have hPq : ∀ p : P, p = q := fun p => Subtype.ext (Finset.mem_singleton.mp p.2)
  set c : CasselsR P := casselsDiag P (Units.mk0 (w : ℚ) (by exact_mod_cast hw.ne')) with hc
  have hcq : ∀ p : P, ((c p : (p.1.adicCompletion ℚ)ˣ) : p.1.adicCompletion ℚ) = (w : p.1.adicCompletion ℚ) := by
    intro p
    rw [hc, casselsDiag_apply]
    simp
  have hval : ∀ p : P, Valued.v ((c p : (p.1.adicCompletion ℚ)ˣ) : p.1.adicCompletion ℚ) = 1 := by
    intro p
    rw [hcq]
    have := valued_natCast_eq_one' (v := p.1) (m := w) (by
      rw [show Rat.HeightOneSpectrum.natGenerator p.1 = 2 by rw [hPq p]; exact hv₂]; omega)
    simpa using this
  have e : ((((w / 4 : ℕ) : v₂.adicCompletionIntegers ℚ)) : v₂.adicCompletion ℚ) =
      ((w / 4 : ℕ) : v₂.adicCompletion ℚ) :=
    map_natCast (v₂.adicCompletionIntegers ℚ).subtype _
  have hd := Nat.div_add_mod w 4
  have hw1 : w % 4 = 1 → (w : v₂.adicCompletion ℚ) =
      1 + 4 * (((w / 4 : ℕ) : v₂.adicCompletionIntegers ℚ) : v₂.adicCompletion ℚ) := by
    intro h
    rw [e]
    conv_lhs => rw [← hd, h]
    push_cast; ring
  have hw3 : w % 4 = 3 → (w : v₂.adicCompletion ℚ) =
      3 + 4 * (((w / 4 : ℕ) : v₂.adicCompletionIntegers ℚ) : v₂.adicCompletion ℚ) := by
    intro h
    rw [e]
    conv_lhs => rw [← hd, h]
    push_cast; ring
  unfold casselsg
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hmem
    by_contra h4
    have h43 : w % 4 = 3 := by omega
    refine not_mem_casselsST_of_subgroup ex6Q ex6Q_nondeg stdLat P (by norm_num) q (H6 v₂) ?_ ?_ ?_ ?_
      (x := c) hval ?_ hmem
    · rw [sqClass_mk_eq]
      have : ((primeUnit P q : (v₂.adicCompletion ℚ)ˣ) : v₂.adicCompletion ℚ) = 2 := by
        rw [primeUnit, casselsDiag_apply]
        simp [natGenUnit, q, hv₂]
      rw [this]; exact two_mem_H6
    · intro A hA
      exact (mem_theta_ex6_two h2 A).mp hA
    · intro p hpq
      exact absurd (hPq p) hpq
    · rw [casselsJ_ex6Q, map_one, Pi.one_apply,
        show SqClass.mk (1 : (v₂.adicCompletion ℚ)ˣ) = 1 from map_one (sqClassHom _)]
      exact (H6 v₂).one_mem
    · rw [sqClass_mk_eq, hcq q, hw3 h43]
      exact three_add_four_not_mem_H6 h2 _
  · intro h4
    refine Subgroup.mem_sup_left ?_
    rw [casselsS, Subgroup.mem_pi]
    intro p _
    obtain rfl := (hPq p).symm
    refine (mem_theta_ex6_two h2 _).mpr ?_
    rw [sqClass_mk_eq, hcq q, hw1 h4]
    exact one_add_four_mem_H6 h2 _

end Group

/-- **Cassels, Ch. 11, Example 6 (i), (ii)** (p. 252), proved: for $f = x^2 + y^2 + 16z^2$ on $\mathbb Z^3$, the set
$P = \{2\}$ satisfies (3.7), $G$ has order $2$, the genus consists of two proper spinor genera, and $g(w) = 1$ for odd
$w > 0$ iff $w \equiv 1 \pmod 4$. Unconditional. -/
@[kb "cassels1978" "Ch. 11, Ex. 6 (i), (ii), p. 252 (proved)"]
theorem ex6SpinorGenera_holds : Ex6SpinorGenera where
  spinorGenusNumber := by
    have hv := natGenerator_ratPlace 2 Nat.prime_two
    exact properSpinorGenusNumber_eq_two_of_card ex6Q ex6Q_nondeg stdLat {ratPlace 2 Nat.prime_two}
      (by norm_num) (ex6_cond _ hv) (ex6_card_casselsG _ hv)
  unitsAway v₂ hv₂ v hv a :=
    ex6_cond v₂ hv₂ v (by rwa [Finset.mem_singleton]) a
  orderG v₂ hv₂ := ex6_card_casselsG v₂ hv₂
  g_odd v₂ hv₂ w hw hodd := ex6_casselsg_odd v₂ hv₂ w hw hodd

end QuadFormsKB.Cassels.Ch11Ex4
