/-
# The Davenport–Cassels lemma

**Theorem (Davenport–Cassels).** Let $Q(\vec{x}) = \sum_{0 \le i \le j < m} c_{ij} x_i x_j$ be an
integral quadratic form ($c_{ij} \in \mathbb{Z}$) which is positive definite over $\mathbb{Q}$, and
suppose that every rational point is within $Q$-distance $< 1$ of an integral point:
$$\forall \vec{x} \in \mathbb{Q}^m \ \exists \vec{y} \in \mathbb{Z}^m : \ Q(\vec{x} - \vec{y}) < 1.$$
Then every integer $n$ represented by $Q$ over $\mathbb{Q}$ is represented by $Q$ over $\mathbb{Z}$.

*Proof* (Serre, *A Course in Arithmetic*, Ch. IV, Appendix "Sums of three squares", Lemma B
(Davenport–Cassels), p. 46, proof pp. 46–47; the earlier "Lemma 5.1" locator for Cassels was wrong:
Cassels' *Rational Quadratic Forms* does not state this lemma; its Ch. 6 Example 6, p. 100, proves
"integral = sum of $n$ rational squares" for $n = 2,3,4$ by a different, isotropy-based argument,
Aubry's method of Ch. 6 §8, p. 86, Lemma 8.1, p. 87, and credits Aubry (1912) and Serre (1970)). Write a rational solution as $\vec{v}/d$ with
$\vec{v} \in \mathbb{Z}^m$, $d \ge 1$, $Q(\vec{v}) = d^2 n$, and descend on $d$. Pick
$\vec{y} \in \mathbb{Z}^m$ with $Q(\vec{v} - d\vec{y}) < d^2$. If $\vec{v} = d\vec{y}$, then
$Q(\vec{y}) = n$. Otherwise, with $B(\vec{u}, \vec{w}) = Q(\vec{u} + \vec{w}) - Q(\vec{u}) - Q(\vec{w})$,
$a = Q(\vec{y}) - n$ and $b = 2dn - B(\vec{v}, \vec{y})$, one has
$Q(\vec{v} - d\vec{y}) = d (da + b)$, so $d' = da + b$ satisfies $0 < d' < d$, and
$Q(a\vec{v} + b\vec{y}) = d'^2 n$: the second intersection of the line through $\vec{v}/d$ and
$\vec{y}$ with the quadric $Q = n$ has the smaller denominator $d'$.

**Main results.**
* `QuadFormsKB.DavenportCassels.davenport_cassels`: the lemma above.
* `QuadFormsKB.DavenportCassels.sum_sq_int_of_rat`: for $m \le 3$, an integer that is a sum of
  $m$ rational squares is a sum of $m$ integer squares (rounding gives $Q(\vec{x} - \vec{y}) \le m/4 < 1$).
-/
import QuadFormsKB.Defs.QuadForm

open Matrix

namespace QuadFormsKB.DavenportCassels

open QuadForm

variable {R : Type*} [CommRing R] {m : ℕ}

/-- **Expansion of $Q$ along a plane:** for $a, b \in K$ and $\vec{u}, \vec{w} \in K^m$,
$$Q(a\vec{u} + b\vec{w}) = a^2 Q(\vec{u}) + ab\, B(\vec{u}, \vec{w}) + b^2 Q(\vec{w}),$$
where $B(\vec{u}, \vec{w}) = Q(\vec{u} + \vec{w}) - Q(\vec{u}) - Q(\vec{w})$ is the polar form. -/
theorem evalIn_smul_add_smul (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R m)
    (a b : K) (u w : Fin m → K) :
    Q.evalIn K (a • u + b • w) = a ^ 2 * Q.evalIn K u
      + a * b * (Q.evalIn K (u + w) - Q.evalIn K u - Q.evalIn K w) + b ^ 2 * Q.evalIn K w := by
  simp only [evalIn, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- $Q(s\vec{u}) = s^2 Q(\vec{u})$. -/
theorem evalIn_smul' (K : Type*) [CommRing K] [Algebra R K] (Q : QuadForm R m)
    (s : K) (u : Fin m → K) : Q.evalIn K (s • u) = s ^ 2 * Q.evalIn K u := by
  have h := evalIn_smul_add_smul K Q s 0 u u
  simpa using h

/-- Evaluating an integral form at an integral vector commutes with $\mathbb{Z} \to \mathbb{Q}$. -/
theorem evalIn_rat_intCast (Q : QuadForm ℤ m) (w : Fin m → ℤ) :
    Q.evalIn ℚ (fun i => (w i : ℚ)) = (Q.evalIn ℤ w : ℚ) := by
  simp only [evalIn, algebraMap_int_eq, eq_intCast, Int.cast_sum, Algebra.algebraMap_self]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> push_cast <;> ring

/-- **The integral descent** behind the Davenport–Cassels lemma. Let $Q$ be an integral form with
$Q(\vec{w}) > 0$ for every $\vec{w} \in \mathbb{Z}^m \setminus \{0\}$, such that for all
$\vec{v} \in \mathbb{Z}^m$ and $d \ge 1$ there is $\vec{y} \in \mathbb{Z}^m$ with
$Q(\vec{v} - d\vec{y}) < d^2$. If $Q(\vec{v}) = d^2 n$ for some $\vec{v} \in \mathbb{Z}^m$ and
integer $d \ge 1$, then $Q(\vec{w}) = n$ for some $\vec{w} \in \mathbb{Z}^m$.

*Proof.* Strong induction on $d$, as in the module docstring (Serre IV, Appendix, Lemma B, pp. 46–47). -/
theorem descent (Q : QuadForm ℤ m) (hpos : ∀ w : Fin m → ℤ, w ≠ 0 → 0 < Q.evalIn ℤ w)
    (hround : ∀ (v : Fin m → ℤ) (d : ℤ), 0 < d → ∃ y : Fin m → ℤ, Q.evalIn ℤ (v - d • y) < d ^ 2)
    (n : ℤ) : ∀ (d : ℕ) (v : Fin m → ℤ), 0 < d → Q.evalIn ℤ v = (d : ℤ) ^ 2 * n →
      ∃ w : Fin m → ℤ, Q.evalIn ℤ w = n := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro v hd hv
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  obtain ⟨y, hy⟩ := hround v d hdZ
  by_cases h0 : v - (d : ℤ) • y = 0
  · refine ⟨y, ?_⟩
    have hvy : v = (d : ℤ) • y := sub_eq_zero.mp h0
    rw [hvy, evalIn_smul'] at hv
    exact mul_left_cancel₀ (by positivity) hv
  · have hpu := hpos _ h0
    have hu' : v - (d : ℤ) • y = (1 : ℤ) • v + (-(d : ℤ)) • y := by
      rw [one_smul, neg_smul, sub_eq_add_neg]
    have hQu : Q.evalIn ℤ (v - (d : ℤ) • y) = (d : ℤ) * ((d : ℤ) * (Q.evalIn ℤ y - n)
        + (2 * d * n - (Q.evalIn ℤ (v + y) - Q.evalIn ℤ v - Q.evalIn ℤ y))) := by
      rw [hu', evalIn_smul_add_smul, hv]; ring
    set d' : ℤ := (d : ℤ) * (Q.evalIn ℤ y - n)
        + (2 * d * n - (Q.evalIn ℤ (v + y) - Q.evalIn ℤ v - Q.evalIn ℤ y)) with hd'
    have hd'pos : 0 < d' := by
      rw [hQu] at hpu; exact pos_of_mul_pos_right hpu hdZ.le
    have hd'lt : d' < d := by
      rw [hQu] at hy; nlinarith
    have hv' : Q.evalIn ℤ ((Q.evalIn ℤ y - n) • v
        + (2 * d * n - (Q.evalIn ℤ (v + y) - Q.evalIn ℤ v - Q.evalIn ℤ y)) • y)
        = ((d'.toNat : ℕ) : ℤ) ^ 2 * n := by
      rw [Int.toNat_of_nonneg hd'pos.le, hd', evalIn_smul_add_smul]
      generalize Q.evalIn ℤ (v + y) = A at *
      generalize Q.evalIn ℤ y = C at *
      rw [hv]; ring
    exact ih d'.toNat (by omega) _ (by omega) hv'

/-- **The Davenport–Cassels lemma** (Serre, *A Course in Arithmetic*, Ch. IV, Appendix, Lemma B,
p. 46, there named "Davenport–Cassels"; for Cassels' book see the module docstring). Let
$Q(\vec{x}) = \sum_{0 \le i \le j < m} c_{ij} x_i x_j$ with $c_{ij} \in \mathbb{Z}$ be positive definite
over $\mathbb{Q}$ (`hpos`: $Q(\vec{x}) > 0$ for $\vec{x} \in \mathbb{Q}^m \setminus \{0\}$), and suppose
(`hDC`) that for every $\vec{x} \in \mathbb{Q}^m$ there is $\vec{y} \in \mathbb{Z}^m$ with
$Q(\vec{x} - \vec{y}) < 1$. Then for every $n \in \mathbb{Z}$: if $Q(\vec{x}) = n$ for some
$\vec{x} \in \mathbb{Q}^m$, then $Q(\vec{y}) = n$ for some $\vec{y} \in \mathbb{Z}^m$.

*Proof.* Clear denominators, $\vec{x} = \vec{v}/d$ with $d = \prod_i \operatorname{den}(x_i)$, and apply
`descent`; the rounding hypothesis for $\vec{v}/d$ scales to $Q(\vec{v} - d\vec{y}) < d^2$. -/
@[kb "serre1973" "Ch. IV, Appendix, Lemma B, p. 46"]
theorem davenport_cassels (Q : QuadForm ℤ m)
    (hpos : ∀ x : Fin m → ℚ, x ≠ 0 → 0 < Q.evalIn ℚ x)
    (hDC : ∀ x : Fin m → ℚ, ∃ y : Fin m → ℤ, Q.evalIn ℚ (x - fun i => (y i : ℚ)) < 1)
    (n : ℤ) (h : Q.RepresentsIn ℚ n) : Q.RepresentsIn ℤ n := by
  obtain ⟨x, hx⟩ := h
  rw [algebraMap_int_eq, eq_intCast] at hx
  -- integral positivity
  have hposZ : ∀ w : Fin m → ℤ, w ≠ 0 → 0 < Q.evalIn ℤ w := by
    intro w hw
    have hw' : (fun i => (w i : ℚ)) ≠ 0 := by
      intro h; apply hw; funext i
      have := congrFun h i
      simpa using this
    have := hpos _ hw'
    rw [evalIn_rat_intCast] at this
    exact_mod_cast this
  -- integral rounding
  have hroundZ : ∀ (v : Fin m → ℤ) (d : ℤ), 0 < d →
      ∃ y : Fin m → ℤ, Q.evalIn ℤ (v - d • y) < d ^ 2 := by
    intro v d hd
    obtain ⟨y, hy⟩ := hDC fun i => (v i : ℚ) / d
    refine ⟨y, ?_⟩
    have hdq : (0 : ℚ) < d := by exact_mod_cast hd
    have hvec : ((fun i => (v i : ℚ) / d) - fun i => (y i : ℚ))
        = (1 / (d : ℚ)) • fun i => ((v - d • y) i : ℚ) := by
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
      field_simp
    rw [hvec, evalIn_smul', evalIn_rat_intCast] at hy
    have h2 : ((Q.evalIn ℤ (v - d • y) : ℤ) : ℚ) < (d : ℚ) ^ 2 := by
      have hd2 : (0 : ℚ) < (d : ℚ) ^ 2 := by positivity
      have e : (1 / (d : ℚ)) ^ 2 * ((Q.evalIn ℤ (v - d • y) : ℤ) : ℚ) * (d : ℚ) ^ 2
          = ((Q.evalIn ℤ (v - d • y) : ℤ) : ℚ) := by field_simp
      nlinarith [mul_lt_mul_of_pos_right hy hd2]
    exact_mod_cast h2
  -- clear denominators
  set d : ℕ := ∏ i, (x i).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun i _ => (x i).den_pos
  let v : Fin m → ℤ := fun i => (x i).num * ((d / (x i).den : ℕ) : ℤ)
  have hv : (fun i => (v i : ℚ)) = (d : ℚ) • x := by
    funext i
    have hdvd : (x i).den ∣ d := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hk : ((d / (x i).den : ℕ) : ℚ) * (x i).den = d := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    simp only [v, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [← Rat.mul_den_eq_num, ← hk]; ring
  have hQv : Q.evalIn ℤ v = (d : ℤ) ^ 2 * n := by
    have := evalIn_rat_intCast Q v
    rw [hv, evalIn_smul', hx] at this
    exact_mod_cast this.symm
  obtain ⟨w, hw⟩ := descent Q hposZ hroundZ n d v hdpos hQv
  exact ⟨w, by simpa using hw⟩

/-- Values of the sum of $m$ squares $\langle 1, \dots, 1 \rangle$:
$Q(\vec{x}) = \sum_{0 \le i < m} x_i^2$ over any $\mathbb{Z}$-algebra $K$. -/
theorem evalIn_diag_one (K : Type*) [CommRing K] (x : Fin m → K) :
    (QuadForm.diag (fun _ : Fin m => (1 : ℤ))).evalIn K x = ∑ i, x i ^ 2 := by
  simp only [evalIn, QuadForm.diag]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- **Sums of at most three squares descend from $\mathbb{Q}$ to $\mathbb{Z}$** (Serre, *A Course
in Arithmetic*, Ch. IV, Appendix, p. 47, proof of the Theorem from Lemma B for $x_0^2 + x_1^2 + x_2^2$): for $m \le 3$ and
$n \in \mathbb{Z}$, if $n = \sum_{0 \le i < m} x_i^2$ with $x_i \in \mathbb{Q}$, then
$n = \sum_{0 \le i < m} y_i^2$ with $y_i \in \mathbb{Z}$.

*Proof.* `davenport_cassels` for $\langle 1, \dots, 1 \rangle$: rounding each coordinate,
$y_i = \operatorname{round}(x_i)$, gives $\sum_i (x_i - y_i)^2 \le m/4 \le 3/4 < 1$. -/
@[kb "serre1973" "Ch. IV, Appendix, Lemma B, p. 46"]
theorem sum_sq_int_of_rat (hm : m ≤ 3) (n : ℤ) (h : ∃ x : Fin m → ℚ, ∑ i, x i ^ 2 = n) :
    ∃ y : Fin m → ℤ, ∑ i, y i ^ 2 = n := by
  have hQ := davenport_cassels (QuadForm.diag (fun _ : Fin m => (1 : ℤ))) ?_ ?_ n ?_
  · obtain ⟨y, hy⟩ := hQ
    exact ⟨y, by rw [evalIn_diag_one] at hy; simpa using hy⟩
  · intro x hx
    rw [evalIn_diag_one]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by simpa using sq_pos_of_ne_zero hi⟩
  · intro x
    refine ⟨fun i => round (x i), ?_⟩
    rw [evalIn_diag_one]
    have hle : ∀ i, (x - fun i => ((round (x i) : ℤ) : ℚ)) i ^ 2 ≤ 1 / 4 := by
      intro i
      have h1 := abs_sub_round (x i)
      have h2 : |x i - round (x i)| ^ 2 ≤ (1 / 2) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      simp only [Pi.sub_apply, sq_abs] at h2 ⊢
      linarith
    calc ∑ i, (x - fun i => ((round (x i) : ℤ) : ℚ)) i ^ 2 ≤ ∑ _i : Fin m, (1 / 4 : ℚ) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = m / 4 := by simp; ring
      _ < 1 := by
          have : (m : ℚ) ≤ 3 := by exact_mod_cast hm
          linarith
  · obtain ⟨x, hx⟩ := h
    exact ⟨x, by rw [evalIn_diag_one, hx]; simp⟩

end QuadFormsKB.DavenportCassels
