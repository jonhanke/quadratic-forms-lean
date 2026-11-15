/-
# Kitaoka 1993, Theorem 1.2.2 (Kneser): Assertion 1 in rank one

**Source.** Y. Kitaoka, *Arithmetic of Quadratic Forms* (1993), §1.2, proof of Theorem 1.2.2, Assertion 1, case
$\operatorname{rank} M = 1$, pp. 7–9 (printed pages).

**Setting.** As in `Ch1KneserSym.lean`; moreover $R \to \tilde R$ is injective, $P$ is the maximal ideal of $R$ and
$\bar R = R/P$ its residue field. $J \subseteq L$ are $R$-submodules of $U$ with $q(J) \subseteq R$ and
$b(L, J) \subseteq R$ (Kitaoka's condition (1), for $H = J$).

**Proves** `rankOne`: let $m, n \in L$ with $q(m) = q(n)$, $n - m \in J$, and $b(m, y) = 1$, $b(n, y') = 1$ for some
$y, y' \in J$ (condition (2) for $M = Rm$, $N = Rn$). Suppose there is $e \in J$ with $q(e) \in R^\times$ and, if
$\#\bar R = 2$, $b(e, J) \subseteq P$ (conditions (5), (6)). Then some $g \in S(J)$ has $g(m) = n$.

**Proof** (Kitaoka's). Put $h = n - m$; then $q(h) = b(n, h) = -b(m, h)$. If $q(h)$ is a unit, $\tau_h(m) = n$. Otherwise
an $f \in J$ with $q(f), b(f, m), b(f, n)$ units gives $g = n - \tau_f(m) \in J$ with $q(g)$ a unit and
$\tau_g\tau_f(m) = n$. Such an $f$ exists: otherwise (residues in $\bar R$, written $\lambda(y) = \overline{b(y, m)}$,
$\mu(y) = \overline{b(y, n)}$, $\bar q$, $\bar b$) $\bar q$ vanishes on the $y \in J$ with $\lambda(y)\mu(y) \ne 0$
("good" $y$); if $\#\bar R \ne 2$ this forces $\bar b(h, J) = 0$, hence $\lambda = \mu$, hence $\bar q = 0$ on $J$; if
$\#\bar R = 2$, $e + y$ is good for a good $y$ when $\lambda(e) = 0$, so $\bar q(e) = 0$. Both contradict $q(e) \in
R^\times$.
-/
import QuadFormsKB.Literature.Kitaoka.Wave5.Ch1KneserSym
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite

open QuadraticMap IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Kitaoka.Kneser

variable {R Rt U : Type} [CommRing R] [IsLocalRing R] [CommRing Rt] [Algebra R Rt]
  [AddCommGroup U] [Module Rt U] [Module R U] [IsScalarTower R Rt U]

/-! ### Residues of elements of $R \subseteq \tilde R$ -/

section Res

open Classical in
variable (R) in
/-- A preimage in $R$ of $t \in \tilde R$ ($0$ if there is none). -/
def toR (t : Rt) : R := if h : t ∈ (algebraMap R Rt).range then h.choose else 0

theorem toR_spec {t : Rt} (ht : t ∈ (algebraMap R Rt).range) : algebraMap R Rt (toR R t) = t := by
  classical
  rw [toR, dif_pos ht]; exact ht.choose_spec

variable (hinj : Function.Injective (algebraMap R Rt))
include hinj

theorem toR_algebraMap (r : R) : toR R (algebraMap R Rt r) = r :=
  hinj (toR_spec ⟨r, rfl⟩)

variable (R) in
/-- The residue $\bar t \in \bar R$ of $t \in R \subseteq \tilde R$. -/
def rs (t : Rt) : ResidueField R := residue R (toR R t)

theorem rs_algebraMap (r : R) : rs R (algebraMap R Rt r) = residue R r := by
  rw [rs, toR_algebraMap hinj]

theorem rs_add {t t' : Rt} (ht : t ∈ (algebraMap R Rt).range) (ht' : t' ∈ (algebraMap R Rt).range) :
    rs R (t + t') = rs R t + rs R t' := by
  obtain ⟨a, rfl⟩ := ht; obtain ⟨b, rfl⟩ := ht'
  rw [← map_add, rs_algebraMap hinj, rs_algebraMap hinj, rs_algebraMap hinj, map_add]

theorem rs_mul {t t' : Rt} (ht : t ∈ (algebraMap R Rt).range) (ht' : t' ∈ (algebraMap R Rt).range) :
    rs R (t * t') = rs R t * rs R t' := by
  obtain ⟨a, rfl⟩ := ht; obtain ⟨b, rfl⟩ := ht'
  rw [← map_mul, rs_algebraMap hinj, rs_algebraMap hinj, rs_algebraMap hinj, map_mul]

theorem rs_neg {t : Rt} (ht : t ∈ (algebraMap R Rt).range) : rs R (-t) = -rs R t := by
  obtain ⟨a, rfl⟩ := ht
  rw [← map_neg, rs_algebraMap hinj, rs_algebraMap hinj, map_neg]

theorem rs_one : rs R (1 : Rt) = 1 := by
  rw [← map_one (algebraMap R Rt), rs_algebraMap hinj, map_one]

theorem rs_ne_zero_iff {t : Rt} (ht : t ∈ (algebraMap R Rt).range) :
    rs R t ≠ 0 ↔ ∃ u : R, IsUnit u ∧ t = algebraMap R Rt u := by
  obtain ⟨a, rfl⟩ := ht
  rw [rs_algebraMap hinj, residue_ne_zero_iff_isUnit]
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · rintro ⟨u, hu, h⟩; rw [hinj h]; exact hu

end Res

/-! ### The rank-one case -/

variable (q : QuadraticForm Rt U)

variable (R) in
/-- $t = u$ with $u \in R^\times$. -/
def IsUnitVal (t : Rt) : Prop := ∃ u : R, IsUnit u ∧ t = algebraMap R Rt u

/-- The inverse of a unit value, in $\tilde R$. -/
theorem exists_inv_of_isUnitVal {t : Rt} (h : IsUnitVal R t) : ∃ c : Rt, c * t = 1 := by
  obtain ⟨u, ⟨v, rfl⟩, rfl⟩ := h
  exact ⟨algebraMap R Rt (↑v⁻¹ : R), by rw [← map_mul, Units.inv_mul, map_one]⟩

/-- A symmetry in a vector of unit value lies in $S(J)$. -/
theorem InS.sym_of {J : Submodule R U} {z : U} (hz : z ∈ J) (hzu : IsUnitVal R (q z)) :
    ∃ c : Rt, ∃ hc : c * q z = 1, InS q J (symEquiv q z c hc) := by
  obtain ⟨c, hc⟩ := exists_inv_of_isUnitVal hzu
  obtain ⟨u, hu, hq⟩ := hzu
  exact ⟨c, hc, InS.sym hz hu hq hc⟩

section RankOne

variable {q} (hinj : Function.Injective (algebraMap R Rt)) {L J : Submodule R U} (hJL : J ≤ L)
  (hqJ : ∀ z ∈ J, q z ∈ (algebraMap R Rt).range)
  (hLJ : ∀ x ∈ L, ∀ z ∈ J, polar q x z ∈ (algebraMap R Rt).range)
include hinj hJL hqJ hLJ

theorem polar_range_comm {x z : U} (hx : x ∈ L) (hz : z ∈ J) : polar q z x ∈ (algebraMap R Rt).range := by
  rw [polar_comm]; exact hLJ x hx z hz

/-- The residue expansion $\bar q(ax + y) = \bar a^2\bar q(x) + \bar a\,\bar b(x, y) + \bar q(y)$. -/
theorem rs_q_smul_add {x y : U} (hx : x ∈ J) (hy : y ∈ J) (a : R) :
    rs R (q (a • x + y)) = residue R a ^ 2 * rs R (q x) + residue R a * rs R (polar q x y) + rs R (q y) := by
  have hxy : polar q x y ∈ (algebraMap R Rt).range := hLJ x (hJL hx) y hy
  have e : q (a • x + y) = algebraMap R Rt a * algebraMap R Rt a * q x + (algebraMap R Rt a * polar q x y + q y) := by
    rw [← algebraMap_smul Rt a x, QuadraticMap.map_add q, QuadraticMap.map_smul, polar_smul_left, smul_eq_mul,
      smul_eq_mul]
    ring
  have hr : ∀ r : R, algebraMap R Rt r ∈ (algebraMap R Rt).range := fun r => ⟨r, rfl⟩
  rw [e, rs_add hinj ((algebraMap R Rt).range.mul_mem ((algebraMap R Rt).range.mul_mem (hr a) (hr a)) (hqJ x hx))
      ((algebraMap R Rt).range.add_mem ((algebraMap R Rt).range.mul_mem (hr a) hxy) (hqJ y hy)),
    rs_mul hinj ((algebraMap R Rt).range.mul_mem (hr a) (hr a)) (hqJ x hx), rs_mul hinj (hr a) (hr a),
    rs_add hinj ((algebraMap R Rt).range.mul_mem (hr a) hxy) (hqJ y hy), rs_mul hinj (hr a) hxy, rs_algebraMap hinj]
  ring

/-- Linearity of $y \mapsto \overline{b(y, w)}$ on $J$ for $w \in L$. -/
theorem rs_polar_smul_add {w : U} (hw : w ∈ L) {x y : U} (hx : x ∈ J) (hy : y ∈ J) (a : R) :
    rs R (polar q (a • x + y) w) = residue R a * rs R (polar q x w) + rs R (polar q y w) := by
  have hxw := polar_range_comm hinj hJL hqJ hLJ hw hx
  have hyw := polar_range_comm hinj hJL hqJ hLJ hw hy
  have hr : algebraMap R Rt a ∈ (algebraMap R Rt).range := ⟨a, rfl⟩
  rw [← algebraMap_smul Rt a x, polar_add_left, polar_smul_left, smul_eq_mul,
    rs_add hinj ((algebraMap R Rt).range.mul_mem hr hxw) hyw, rs_mul hinj hr hxw, rs_algebraMap hinj]

/-- **The key existence** (Kitaoka's (10)): with $h = n - m$ and $q(h) \in P$, some $f \in J$ has $q(f)$, $b(f, m)$,
$b(f, n)$ units. -/
theorem exists_good {m n : U} (hm : m ∈ L) (hn : n ∈ L) (hmn : n - m ∈ J)
    (hqmn : q n = q m) (hym : ∃ y ∈ J, polar q m y = 1) (hyn : ∃ y ∈ J, polar q n y = 1)
    (he : ∃ e ∈ J, IsUnitVal R (q e) ∧ (Nat.card (ResidueField R) = 2 → ∀ z ∈ J, rs R (polar q e z) = 0))
    (hqh : rs R (q (n - m)) = 0) :
    ∃ f ∈ J, IsUnitVal R (q f) ∧ IsUnitVal R (polar q f m) ∧ IsUnitVal R (polar q f n) := by
  have hpr : ∀ {x z : U}, x ∈ L → z ∈ J → polar q z x ∈ (algebraMap R Rt).range :=
    fun hx hz => polar_range_comm hinj hJL hqJ hLJ hx hz
  -- units versus residues
  have hU : ∀ {t : Rt}, t ∈ (algebraMap R Rt).range → (IsUnitVal R t ↔ rs R t ≠ 0) :=
    fun ht => (rs_ne_zero_iff hinj ht).symm
  by_contra hcon
  push_neg at hcon
  -- (13): $\bar q$ vanishes on the good vectors
  have h13 : ∀ y ∈ J, rs R (polar q y m) ≠ 0 → rs R (polar q y n) ≠ 0 → rs R (q y) = 0 := by
    intro y hy h1 h2
    by_contra h3
    exact hcon y hy ((hU (hqJ y hy)).mpr h3) ((hU (hpr hm hy)).mpr h1) ((hU (hpr hn hy)).mpr h2)
  -- linearity in the first argument (with $a = 1$)
  have hlin : ∀ {w x y : U}, w ∈ L → x ∈ J → y ∈ J → rs R (polar q (x + y) w) = rs R (polar q x w) + rs R (polar q y w) := by
    intro w x y hw hx hy
    have := rs_polar_smul_add hinj hJL hqJ hLJ hw hx hy 1
    rwa [one_smul, map_one, one_mul] at this
  have hqadd : ∀ {x y : U}, x ∈ J → y ∈ J → rs R (q (x + y)) = rs R (q x) + rs R (polar q x y) + rs R (q y) := by
    intro x y hx hy
    have := rs_q_smul_add hinj hJL hqJ hLJ hx hy 1
    rwa [one_smul, map_one, one_pow, one_mul, one_mul] at this
  set h := n - m with hhdef
  have hn_eq : n = m + h := by rw [hhdef]; abel
  -- $\lambda(h) = \mu(h) = 0$
  have hqh_sub : q h = q n + q m - polar q n m := by
    have e1 : polar q n (-m) = q (n + -m) - q n - q (-m) := rfl
    rw [polar_neg_right, QuadraticMap.map_neg] at e1
    rw [hhdef, sub_eq_add_neg]
    linear_combination -e1
  have hpmh : polar q h m = -q h := by
    rw [polar_comm, hhdef, polar_sub_right, QuadraticMap.polar_self, two_nsmul, hqh_sub, hqmn, polar_comm q n m]
    first | done | ring
  have hpnh : polar q h n = q h := by
    rw [polar_comm, hhdef, polar_sub_right, QuadraticMap.polar_self, two_nsmul, hqh_sub, hqmn]
    first | done | ring
  have hlamh : rs R (polar q h m) = 0 := by rw [hpmh, rs_neg hinj (hqJ h hmn), hqh, neg_zero]
  have hmuh : rs R (polar q h n) = 0 := by rw [hpnh, hqh]
  -- $\mu(y) = \lambda(y) + \bar b(y, h)$
  have hmulam : ∀ y ∈ J, rs R (polar q y n) = rs R (polar q y m) + rs R (polar q h y) := by
    intro y hy
    rw [hn_eq, polar_add_right, rs_add hinj (hpr hm hy) (hLJ m hm y hy |> fun _ => by
      rw [polar_comm]; exact hLJ h (hJL hmn) y hy), polar_comm q y h]
  -- a good vector
  obtain ⟨y1, hy1, hpy1⟩ := hym
  obtain ⟨y2, hy2, hpy2⟩ := hyn
  have hlam1 : rs R (polar q y1 m) = 1 := by rw [polar_comm, hpy1, rs_one hinj]
  have hmu2 : rs R (polar q y2 n) = 1 := by rw [polar_comm, hpy2, rs_one hinj]
  obtain ⟨y0, hy0, hlam0, hmu0⟩ : ∃ y0 ∈ J, rs R (polar q y0 m) ≠ 0 ∧ rs R (polar q y0 n) ≠ 0 := by
    by_cases a1 : rs R (polar q y1 n) ≠ 0
    · exact ⟨y1, hy1, by rw [hlam1]; exact one_ne_zero, a1⟩
    by_cases a2 : rs R (polar q y2 m) ≠ 0
    · exact ⟨y2, hy2, a2, by rw [hmu2]; exact one_ne_zero⟩
    push_neg at a1 a2
    refine ⟨y1 + y2, J.add_mem hy1 hy2, ?_, ?_⟩
    · rw [hlin hm hy1 hy2, hlam1, a2, add_zero]; exact one_ne_zero
    · rw [hlin hn hy1 hy2, hmu2, a1, zero_add]; exact one_ne_zero
  have hq0 : rs R (q y0) = 0 := h13 y0 hy0 hlam0 hmu0
  obtain ⟨e, heJ, heu, he2⟩ := he
  have hqe : rs R (q e) ≠ 0 := (hU (hqJ e heJ)).mp heu
  by_cases hk : Nat.card (ResidueField R) = 2
  · -- $\#\bar R = 2$
    have hrad := he2 hk
    have hmue : rs R (polar q e n) = rs R (polar q e m) := by
      rw [hmulam e heJ, polar_comm q h e, hrad h hmn, add_zero]
    by_cases hlame : rs R (polar q e m) ≠ 0
    · exact hqe (h13 e heJ hlame (by rw [hmue]; exact hlame))
    · push_neg at hlame
      have hg1 : rs R (polar q (e + y0) m) ≠ 0 := by rw [hlin hm heJ hy0, hlame, zero_add]; exact hlam0
      have hg2 : rs R (polar q (e + y0) n) ≠ 0 := by rw [hlin hn heJ hy0, hmue, hlame, zero_add]; exact hmu0
      have := h13 (e + y0) (J.add_mem heJ hy0) hg1 hg2
      rw [hqadd heJ hy0, hrad y0 hy0, hq0, add_zero, add_zero] at this
      exact hqe this
  · -- $\#\bar R \ne 2$: an element $t \ne 0, 1$ of $\bar R$
    obtain ⟨t, ht0, ht1⟩ : ∃ t : ResidueField R, t ≠ 0 ∧ t ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hk
      rw [Nat.card_eq_two_iff]
      refine ⟨0, 1, zero_ne_one, ?_⟩
      ext t
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      by_cases h0 : t = 0
      · exact Or.inl h0
      · exact Or.inr (hall t h0)
    -- Step A
    have stepA : ∀ x ∈ J, rs R (polar q x m) = 0 → rs R (polar q x n) = 0 →
        ∀ y ∈ J, rs R (polar q y m) ≠ 0 → rs R (polar q y n) ≠ 0 →
          rs R (q x) = 0 ∧ rs R (polar q x y) = 0 := by
      intro x hx hxm hxn y hy hym' hyn'
      have hqy : rs R (q y) = 0 := h13 y hy hym' hyn'
      have key : ∀ a : R, residue R a ^ 2 * rs R (q x) + residue R a * rs R (polar q x y) = 0 := by
        intro a
        have hg := h13 (a • x + y) (J.add_mem (J.smul_mem a hx) hy)
          (by rw [rs_polar_smul_add hinj hJL hqJ hLJ hm hx hy, hxm, mul_zero, zero_add]; exact hym')
          (by rw [rs_polar_smul_add hinj hJL hqJ hLJ hn hx hy, hxn, mul_zero, zero_add]; exact hyn')
        rw [rs_q_smul_add hinj hJL hqJ hLJ hx hy, hqy, add_zero] at hg
        exact hg
      obtain ⟨a, ha⟩ := residue_surjective t
      have k1 := key 1
      have k2 := key a
      rw [map_one] at k1
      rw [ha] at k2
      have hQ : rs R (q x) = 0 := by
        have : t * (t - 1) * rs R (q x) = 0 := by linear_combination k2 - t * k1
        rcases mul_eq_zero.mp this with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h ht0
          · exact absurd (sub_eq_zero.mp h) ht1
        · exact h
      refine ⟨hQ, ?_⟩
      rw [hQ] at k1
      linear_combination k1
    -- Step B
    have stepB : ∀ x ∈ J, rs R (polar q x m) = 0 → rs R (polar q x n) = 0 → ∀ z ∈ J, rs R (polar q z x) = 0 := by
      intro x hx hxm hxn z hz
      have hx0 : rs R (polar q y0 x) = 0 := by
        rw [polar_comm]; exact (stepA x hx hxm hxn y0 hy0 hlam0 hmu0).2
      -- some $s$ with $s y_0 + z$ good
      obtain ⟨s, hs1, hs2⟩ : ∃ s : ResidueField R,
          s * rs R (polar q y0 m) + rs R (polar q z m) ≠ 0 ∧ s * rs R (polar q y0 n) + rs R (polar q z n) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have bad : ∀ s : ResidueField R, s = -(rs R (polar q z m)) / rs R (polar q y0 m) ∨
            s = -(rs R (polar q z n)) / rs R (polar q y0 n) := by
          intro s
          by_cases h1 : s * rs R (polar q y0 m) + rs R (polar q z m) = 0
          · left; field_simp; linear_combination h1
          · right; have := hall s h1; field_simp; linear_combination this
        rcases bad 0 with h0 | h0 <;> rcases bad 1 with h1 | h1 <;> rcases bad t with h2 | h2
        all_goals first
          | exact ht0 (h2.trans h0.symm)
          | exact ht1 (h2.trans h1.symm)
          | exact zero_ne_one (h0.trans h1.symm)
      obtain ⟨a, ha⟩ := residue_surjective s
      have hw : a • y0 + z ∈ J := J.add_mem (J.smul_mem a hy0) hz
      have hgood := (stepA x hx hxm hxn (a • y0 + z) hw
        (by rw [rs_polar_smul_add hinj hJL hqJ hLJ hm hy0 hz, ha]; exact hs1)
        (by rw [rs_polar_smul_add hinj hJL hqJ hLJ hn hy0 hz, ha]; exact hs2)).2
      rw [polar_comm, rs_polar_smul_add hinj hJL hqJ hLJ (hJL hx) hy0 hz, hx0, mul_zero, zero_add] at hgood
      exact hgood
    -- $\bar b(h, J) = 0$, hence $\lambda = \mu$ on $J$
    have hlammu : ∀ y ∈ J, rs R (polar q y n) = rs R (polar q y m) := by
      intro y hy
      rw [hmulam y hy, polar_comm q h y, stepB h hmn hlamh hmuh y hy, add_zero]
    -- $\bar q = 0$ on $J$
    have hall : ∀ y ∈ J, rs R (q y) = 0 := by
      intro y hy
      by_cases hlamy : rs R (polar q y m) ≠ 0
      · exact h13 y hy hlamy (by rw [hlammu y hy]; exact hlamy)
      · push_neg at hlamy
        exact (stepA y hy hlamy (by rw [hlammu y hy, hlamy]) y0 hy0 hlam0 hmu0).1
    exact hqe (hall e heJ)

/-- **Assertion 1, rank one** (Kitaoka 1993, p. 7): some $g \in S(J)$ maps $m$ to $n$. -/
theorem rankOne {m n : U} (hm : m ∈ L) (hn : n ∈ L) (hmn : n - m ∈ J)
    (hqmn : q n = q m) (hym : ∃ y ∈ J, polar q m y = 1) (hyn : ∃ y ∈ J, polar q n y = 1)
    (he : ∃ e ∈ J, IsUnitVal R (q e) ∧ (Nat.card (ResidueField R) = 2 → ∀ z ∈ J, rs R (polar q e z) = 0)) :
    ∃ g : U ≃ₗ[Rt] U, InS q J g ∧ g m = n := by
  set h := n - m with hhdef
  have hqh_sub : q h = q n + q m - polar q n m := by
    have e1 : polar q n (-m) = q (n + -m) - q n - q (-m) := rfl
    rw [polar_neg_right, QuadraticMap.map_neg] at e1
    rw [hhdef, sub_eq_add_neg]
    linear_combination -e1
  have hpmh : polar q m h = -q h := by
    rw [hhdef, polar_sub_right, QuadraticMap.polar_self, two_nsmul, hqh_sub, hqmn, polar_comm q n m]
    first | done | ring
  have hpnh : polar q n h = q h := by
    rw [hhdef, polar_sub_right, QuadraticMap.polar_self, two_nsmul, hqh_sub, hqmn]
    first | done | ring
  have hrange : q h ∈ (algebraMap R Rt).range := hqJ h hmn
  by_cases hu : IsUnitVal R (q h)
  · obtain ⟨c, hc, hS⟩ := InS.sym_of q hmn hu
    refine ⟨_, hS, ?_⟩
    rw [symEquiv_apply, symMap_apply, hpmh, mul_neg, hc, neg_smul, one_smul, sub_neg_eq_add, hhdef]
    abel
  · have hqh : rs R (q h) = 0 := by
      by_contra hne; exact hu ((rs_ne_zero_iff hinj hrange).mp hne)
    obtain ⟨f, hf, hfu, hfm, hfn⟩ := exists_good hinj hJL hqJ hLJ hm hn hmn hqmn hym hyn he hqh
    obtain ⟨c, hc, hSf⟩ := InS.sym_of q hf hfu
    obtain ⟨u, hu', hq'⟩ := hfu
    have hmf : polar q m f ∈ (algebraMap R Rt).range := hLJ m hm f hf
    obtain ⟨r, hr⟩ := coeff_mem hu' hq' hc hmf
    set g := h + (c * polar q m f) • f with hgdef
    have hgJ : g ∈ J := by rw [hgdef, hr]; exact J.add_mem hmn (J.smul_mem r hf)
    have hg_eq : g = n - symMap q f c m := by rw [hgdef, symMap_apply, hhdef]; abel
    have hqg : q g = q h + c * polar q m f * polar q n f := by
      have hn' : polar q n f = polar q m f + polar q h f := by
        rw [show n = m + h by rw [hhdef]; abel, polar_add_left]
      rw [hgdef, QuadraticMap.map_add q, QuadraticMap.map_smul, polar_smul_right, smul_eq_mul, smul_eq_mul, hn']
      linear_combination (c * polar q m f * polar q m f) * hc
    have hgu : IsUnitVal R (q g) := by
      have hcR : c = algebraMap R Rt (↑(hu'.unit⁻¹) : R) := by
        have h1 : algebraMap R Rt (↑(hu'.unit⁻¹) : R) * q f = 1 := by
          rw [hq', ← map_mul]; simp
        calc c = c * (q f * algebraMap R Rt (↑(hu'.unit⁻¹) : R)) := by rw [mul_comm (q f), h1, mul_one]
          _ = (c * q f) * algebraMap R Rt (↑(hu'.unit⁻¹) : R) := by ring
          _ = _ := by rw [hc, one_mul]
      have hcr : c ∈ (algebraMap R Rt).range := ⟨_, hcR.symm⟩
      have hfm' : polar q m f ∈ (algebraMap R Rt).range := hmf
      have hfn' : polar q n f ∈ (algebraMap R Rt).range := hLJ n hn f hf
      have hgr : q g ∈ (algebraMap R Rt).range := hqJ g hgJ
      apply (rs_ne_zero_iff hinj hgr).mp
      rw [hqg, rs_add hinj hrange ((algebraMap R Rt).range.mul_mem ((algebraMap R Rt).range.mul_mem hcr hfm') hfn'),
        rs_mul hinj ((algebraMap R Rt).range.mul_mem hcr hfm') hfn', rs_mul hinj hcr hfm', hqh, zero_add]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · rw [hcR, rs_algebraMap hinj, residue_ne_zero_iff_isUnit]; exact Units.isUnit _
      · rw [polar_comm]; exact (rs_ne_zero_iff hinj (by rw [polar_comm]; exact hfm')).mpr hfm
      · rw [polar_comm]; exact (rs_ne_zero_iff hinj (by rw [polar_comm]; exact hfn')).mpr hfn
    obtain ⟨c', hc', hSg⟩ := InS.sym_of q hgJ hgu
    have hng : polar q n g = q g := by
      rw [hgdef, polar_add_right, polar_smul_right, smul_eq_mul, hpnh, hqg, polar_comm q n f]
      first | done | ring
    have hτg : symMap q g c' n = symMap q f c m := by
      rw [symMap_apply, hng, hc', one_smul, hg_eq, sub_sub_cancel]
    refine ⟨(symEquiv q f c hc).trans (symEquiv q g c' hc'), hSf.trans hSg, ?_⟩
    simp only [LinearEquiv.trans_apply, symEquiv_apply]
    rw [← hτg, symMap_symMap q hc']

end RankOne

end QuadFormsKB.Kitaoka.Kneser
