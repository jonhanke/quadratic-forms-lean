/-
# Cassels, Chapter 8, Example 5: $\mathbb Q_2$-equivalence of unimodular $\mathbb Z_2$-forms

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 8, *Examples*, Ex. 5, p. 125.

**Setting** (as in `Ch8/Examples.lean`, Example 4). A classically integral $\mathbb Z_2$-form in $n$ variables
$x_0, \dots, x_{n-1}$ is given by its symmetric Gram matrix $F \in M_n(\mathbb Z_2)$, $f(\vec x) = \vec x^{t}F\vec x$,
and has *unit determinant* when $\det F \in \mathbb Z_2^{\times}$. A *characteristic vector* of $f$ is a $\vec b \in
\mathbb Z_2^n$ with $f(\vec a) \equiv f(\vec a, \vec b) = \vec a^{t}F\vec b \pmod 2$ for all $\vec a \in \mathbb Z_2^n$
(Example 4 (i)); by Example 4 (ii) the value $f(\vec b) \bmod 8$ does not depend on the choice.  Two forms are
$\mathbb Q_2$-equivalent (`QEquiv`) when $G = P^{t}FP$ for some $P \in \mathrm{GL}_n(\mathbb Q_2)$.  (Cassels says
"improperly primitive" in Example 3 only; Examples 4 and 5 concern every classically integral $\mathbb Z_2$-form with
unit determinant, which is what is formalized here.)

**Statement.** If $f_1, f_2$ are two such forms in the same number $n$ of variables, with characteristic vectors
$\vec b_1, \vec b_2$, then $f_1, f_2$ are $\mathbb Q_2$-equivalent if and only if $\det F_1 \equiv \det F_2 \pmod 8$
and $f_1(\vec b_1) \equiv f_2(\vec b_2) \pmod 8$.

**Method.** Both directions go through the classification of nondegenerate forms over $\mathbb Q_2$ by dimension,
determinant class and Hasse invariant (`PadicClass.isometric_iff_invariants`).  The input is Example 4 (iv)
(`ex4_iv`): $F$ is $\mathbb Q_2$-equivalent to a diagonal form $\langle a_0, \dots, a_{n-1}\rangle$ with
$c_2 = \prod_{i<j}(a_i, a_j)_2 = (-1)^{s}$, $4s \equiv f(\vec b) - d(f) - n + 1 \pmod 8$.  It is proved by induction on
$n$ (`good_main`): a unit on the diagonal splits off a one-dimensional summand over $\mathbb Z_2$ (`split_front`);
otherwise Lemma 4.1's even blocks $2xy$, $2x^{2} + 2xy + 2y^{2}$ split off (`dyadic_EU_split`); orthogonal sums are
handled by the Hilbert symbol of two units (`GoodV.orthSum`, `hs_units`, `hasseVec_append`).  Example 5 then follows
(`ex5`, `ex5_iff`): units congruent mod $8$ differ by a square (`isSquare_two_adic_unit_iff`), and the parity of
$s$ is read off $f(\vec b)$ and $d$.  Everything is unconditional; `Ex4ivHasse` is just the name of the statement
of Example 4 (iv), kept as a structure so that `ex5` can be read as "Example 5 given Example 4 (iv)".
-/
import QuadFormsKB.Literature.Cassels.Ch8.ExamplesDyadic
import QuadFormsKB.Literature.LocalGlobal.PadicClassification
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

open Matrix QuadFormsKB QuadFormsKB.PadicClass QuadForm

noncomputable section

namespace QuadFormsKB.Cassels.Ex5

variable {n : ℕ}

/-- **$\mathbb Q_2$-equivalence of forms given by symmetric matrices** $F, G \in M_n(\mathbb Q_2)$: $G = P^{t}FP$ for an
invertible $P \in M_n(\mathbb Q_2)$ (Cassels' "$f$ is $\mathbb Q_2$-equivalent to $g$": $g(\vec x) = f(P\vec x)$). -/
def QEquiv (F G : Matrix (Fin n) (Fin n) ℚ_[2]) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℚ_[2], IsUnit P.det ∧ Pᵀ * F * P = G

/-- Helper: $\mathbb Q_2$-equivalence is reflexive. -/
theorem QEquiv.refl (F : Matrix (Fin n) (Fin n) ℚ_[2]) : QEquiv F F :=
  ⟨1, by simp, by simp⟩

/-- Helper: $\mathbb Q_2$-equivalence is symmetric. -/
theorem QEquiv.symm {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : QEquiv F G) : QEquiv G F := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P⁻¹, Matrix.isUnit_nonsing_inv_det P hP, ?_⟩
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  calc (P⁻¹)ᵀ * (Pᵀ * F * P) * P⁻¹ = (P * P⁻¹)ᵀ * F * (P * P⁻¹) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = F := by rw [h1]; simp

/-- Helper: $\mathbb Q_2$-equivalence is transitive. -/
theorem QEquiv.trans {F G H : Matrix (Fin n) (Fin n) ℚ_[2]} (h₁ : QEquiv F G) (h₂ : QEquiv G H) :
    QEquiv F H := by
  obtain ⟨P, hP, rfl⟩ := h₁
  obtain ⟨R, hR, rfl⟩ := h₂
  refine ⟨P * R, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hP.mul hR
  · simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- Helper: the determinant of a $\mathbb Q_2$-equivalent form is a square times the determinant. -/
theorem QEquiv.det {F G : Matrix (Fin n) (Fin n) ℚ_[2]} (h : QEquiv F G) :
    ∃ x : ℚ_[2], x ≠ 0 ∧ G.det = x ^ 2 * F.det := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det, hP.ne_zero, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring

/-- Helper: the value of a diagonal matrix form. -/
theorem dot_diagonal (a x : Fin n → ℚ_[2]) :
    x ⬝ᵥ (diagonal a *ᵥ x) = ∑ i, a i * x i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Helper: the Hessian of a diagonal form is twice the diagonal matrix. -/
theorem hessian_diag (a : Fin n → ℚ_[2]) :
    (QuadForm.diag a).hessian = (2 : ℚ_[2]) • diagonal a := by
  ext i j
  by_cases h : i = j
  · subst h; simp [QuadForm.hessian, QuadForm.diag, two_mul]
  · simp [QuadForm.hessian, QuadForm.diag, h, Matrix.diagonal_apply_ne]

/-- Helper: $\mathbb Q_2$-equivalence of diagonal matrices is isometry of the diagonal forms of `QuadForm`. -/
theorem qequiv_diagonal_iff (a b : Fin n → ℚ_[2]) :
    QEquiv (diagonal a) (diagonal b) ↔ (QuadForm.diag a).IsometricIn ℚ_[2] (QuadForm.diag b) := by
  constructor
  · rintro ⟨P, hP, hPe⟩
    refine ⟨P, hP, fun x => ?_⟩
    rw [evalIn_diag_self, evalIn_diag_self, ← dot_diagonal, ← dot_diagonal, ← hPe]
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec x Pᵀ, Matrix.vecMul_transpose]
  · rintro ⟨P, hP, hPe⟩
    refine ⟨P, hP, ?_⟩
    have h := transpose_mul_hessian_mul hPe
    rw [hessian_diag, hessian_diag, Matrix.mul_smul, Matrix.smul_mul] at h
    exact smul_right_injective _ (two_ne_zero) h

/-- **Diagonalization data**: $F$ is $\mathbb Q_2$-equivalent to $\langle a_0, \dots, a_{n-1}\rangle$ with all $a_i
\ne 0$. -/
def QDiag (F : Matrix (Fin n) (Fin n) ℚ_[2]) (a : Fin n → ℚ_[2]) : Prop :=
  (∀ i, a i ≠ 0) ∧ QEquiv F (diagonal a)

/-- Helper: two diagonalized forms are $\mathbb Q_2$-equivalent iff the determinants agree up to a square and the Hasse
invariants agree (classification over $\mathbb Q_2$). -/
theorem qequiv_iff_invariants {F G : Matrix (Fin n) (Fin n) ℚ_[2]} {a b : Fin n → ℚ_[2]}
    (ha : QDiag F a) (hb : QDiag G b) :
    QEquiv F G ↔ (∃ t : ℚ_[2], t ≠ 0 ∧ ∏ i, b i = t ^ 2 * ∏ i, a i) ∧ hasseVec a = hasseVec b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isometric_iff_invariants (localHilbertField_padic (p := 2)) ha.1 hb.1, ← qequiv_diagonal_iff]
  constructor
  · intro h
    exact ha.2.symm.trans (h.trans hb.2)
  · intro h
    exact ha.2.trans (h.trans hb.2.symm)

/-- **Example 4 (iv) with diagonalization** (the input of Example 5; the content of Cassels Ch. 8, Ex. 4 (iv)).
For every classically integral $\mathbb Z_2$-form with symmetric Gram matrix $F$ and unit determinant, and every
characteristic vector $\vec b$, the form is $\mathbb Q_2$-equivalent to a diagonal form
$\langle a_0, \dots, a_{n-1}\rangle$ whose Hasse invariant $c_2 = \prod_{i<j}(a_i,a_j)_2$ equals $(-1)^{s}$, where
$s \in \mathbb N$ satisfies $4s \equiv f(\vec b) - \det F - n + 1 \pmod 8$ (so $s$ is determined mod $2$).
Proved as `ex4_iv`; it is not the conclusion of Example 5. -/
structure Ex4ivHasse : Prop where
  exists_diag : ∀ (n : ℕ) (F : Matrix (Fin n) (Fin n) ℤ_[2]), Fᵀ = F → IsUnit F.det →
    ∀ b : Fin n → ℤ_[2], (∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)) →
    ∃ a : Fin n → ℚ_[2], QDiag (F.map PadicInt.Coe.ringHom) a ∧
      ∃ s : ℕ, (8 : ℤ_[2]) ∣ (b ⬝ᵥ (F *ᵥ b) - F.det - n + 1 - 4 * s) ∧ hasseVec a = (-1) ^ s


/-! ### Arithmetic in $\mathbb Z_2$ -/

/-- Helper: $8 \mid x$ in $\mathbb Z_2$ iff the reduction of $x$ modulo $2^3$ vanishes. -/
theorem eight_dvd_iff (x : ℤ_[2]) : (8 : ℤ_[2]) ∣ x ↔ PadicInt.toZModPow 3 x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

/-- Helper: the square of a unit of $\mathbb Z_2$ is $\equiv 1 \pmod 8$. -/
theorem eight_dvd_sq_sub_one {w : ℤ_[2]} (hw : IsUnit w) : (8 : ℤ_[2]) ∣ w ^ 2 - 1 := by
  have key : ∀ y : ZMod (2 ^ 3), IsUnit y → y ^ 2 = 1 := by decide
  rw [eight_dvd_iff, map_sub, map_pow, map_one, key _ (hw.map _), sub_self]

/-- Helper: if the ratio of two units of $\mathbb Z_2$ is a square in $\mathbb Q_2$, they are congruent mod $8$. -/
theorem eight_dvd_of_sq {d₁ d₂ : ℤ_[2]} (h₁ : IsUnit d₁) (h₂ : IsUnit d₂) {y : ℚ_[2]}
    (hy : ((d₂ : ℤ_[2]) : ℚ_[2]) = y ^ 2 * (d₁ : ℚ_[2])) : (8 : ℤ_[2]) ∣ d₂ - d₁ := by
  have n1 : ‖(d₁ : ℚ_[2])‖ = 1 := by rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 h₁
  have n2 : ‖(d₂ : ℚ_[2])‖ = 1 := by rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 h₂
  have hy1 : ‖y‖ = 1 := by
    have := congrArg norm hy
    rw [norm_mul, norm_pow, n1, n2] at this
    have h0 : 0 ≤ ‖y‖ := norm_nonneg y
    nlinarith
  set w : ℤ_[2] := ⟨y, hy1.le⟩ with hw
  have hwu : IsUnit w := PadicInt.isUnit_iff.2 hy1
  have : d₂ = w ^ 2 * d₁ := by
    apply Subtype.ext
    show ((d₂ : ℤ_[2]) : ℚ_[2]) = ((w ^ 2 * d₁ : ℤ_[2]) : ℚ_[2])
    rw [PadicInt.coe_mul, PadicInt.coe_pow]
    exact hy
  have e : d₂ - d₁ = (w ^ 2 - 1) * d₁ := by rw [this]; ring
  rw [e]
  exact (eight_dvd_sq_sub_one hwu).mul_right _

/-- Helper: two units of $\mathbb Z_2$ congruent mod $8$ differ by a square of $\mathbb Q_2^{\times}$. -/
theorem sq_of_eight_dvd {d₁ d₂ : ℤ_[2]} (h₁ : IsUnit d₁) (h₂ : IsUnit d₂) (h : (8 : ℤ_[2]) ∣ d₂ - d₁) :
    ∃ y : ℚ_[2], y ≠ 0 ∧ ((d₂ : ℤ_[2]) : ℚ_[2]) = y ^ 2 * (d₁ : ℚ_[2]) := by
  obtain ⟨u₁, rfl⟩ := h₁
  obtain ⟨u₂, rfl⟩ := h₂
  set u : ℤ_[2]ˣ := u₂ * u₁⁻¹ with hu
  have hmul : (u : ℤ_[2]) * u₁ = u₂ := by simp [hu]
  have hred : PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 := by
    have h1 : PadicInt.toZModPow 3 (u₂ : ℤ_[2]) = PadicInt.toZModPow 3 (u₁ : ℤ_[2]) := by
      have := (eight_dvd_iff _).1 h
      rwa [map_sub, sub_eq_zero] at this
    have h2 : PadicInt.toZModPow 3 (u : ℤ_[2]) * PadicInt.toZModPow 3 (u₁ : ℤ_[2]) =
        1 * PadicInt.toZModPow 3 (u₁ : ℤ_[2]) := by
      rw [← map_mul, hmul, h1, one_mul]
    exact (u₁.isUnit.map (PadicInt.toZModPow 3)).mul_left_inj.1 h2
  obtain ⟨r, hr⟩ := (HilbertLocal.isSquare_two_adic_unit_iff u).2 hred
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : ((u : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
      intro h
      exact u.ne_zero (Subtype.ext (by simpa using h))
    exact this (by simp at hr)
  refine ⟨r, hr0, ?_⟩
  have : ((u₂ : ℤ_[2]) : ℚ_[2]) = ((u : ℤ_[2]) : ℚ_[2]) * ((u₁ : ℤ_[2]) : ℚ_[2]) := by
    rw [← PadicInt.coe_mul, hmul]
  rw [this, hr]; ring

/-- Helper: equal powers of $-1$ give $8 \mid 4s_1 - 4s_2$ in $\mathbb Z_2$. -/
theorem eight_dvd_of_pow_eq {s₁ s₂ : ℕ} (h : ((-1 : ℤ)) ^ s₁ = (-1) ^ s₂) :
    (8 : ℤ_[2]) ∣ 4 * (s₁ : ℤ_[2]) - 4 * (s₂ : ℤ_[2]) := by
  rcases Nat.even_or_odd' s₁ with ⟨k, rfl | rfl⟩ <;> rcases Nat.even_or_odd' s₂ with ⟨l, rfl | rfl⟩ <;>
    simp [pow_succ, pow_mul] at h
  · exact ⟨(k : ℤ_[2]) - l, by push_cast; ring⟩
  · exact ⟨(k : ℤ_[2]) - l, by push_cast; ring⟩

/-- Helper: $8 \mid 4s_1 - 4s_2$ in $\mathbb Z_2$ gives equal powers of $-1$. -/
theorem pow_eq_of_eight_dvd {s₁ s₂ : ℕ} (h : (8 : ℤ_[2]) ∣ 4 * (s₁ : ℤ_[2]) - 4 * (s₂ : ℤ_[2])) :
    ((-1 : ℤ)) ^ s₁ = (-1) ^ s₂ := by
  obtain ⟨c, hc⟩ := h
  have h2 : (s₁ : ℤ_[2]) - s₂ = 2 * c := by
    have : (4 : ℤ_[2]) * ((s₁ : ℤ_[2]) - s₂) = 4 * (2 * c) := by linear_combination hc
    exact mul_left_cancel₀ (by norm_num) this
  have h3 : ((s₁ : ℕ) : ZMod 2) = ((s₂ : ℕ) : ZMod 2) := by
    have := congrArg (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) h2
    simp only [map_sub, map_natCast, map_mul] at this
    have h22 : (PadicInt.toZMod (2 : ℤ_[2])) = 0 := by
      have : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
      rw [this, map_natCast]; decide
    rw [h22, zero_mul, sub_eq_zero] at this
    exact this
  rw [ZMod.natCast_eq_natCast_iff'] at h3
  rw [neg_one_pow_eq_pow_mod_two, h3, ← neg_one_pow_eq_pow_mod_two]


/-- Helper: for a diagonalization $F \sim \langle a_i\rangle$ of the image of an integral matrix, $\prod a_i$ is a
nonzero square multiple of $\det F$. -/
theorem prod_eq_sq_mul_det {F : Matrix (Fin n) (Fin n) ℤ_[2]} {a : Fin n → ℚ_[2]}
    (h : QDiag (F.map PadicInt.Coe.ringHom) a) :
    ∃ x : ℚ_[2], x ≠ 0 ∧ ∏ i, a i = x ^ 2 * ((F.det : ℤ_[2]) : ℚ_[2]) := by
  obtain ⟨x, hx0, hx⟩ := h.2.det
  refine ⟨x, hx0, ?_⟩
  rw [← dyadic_det_map_coe, ← hx, Matrix.det_diagonal]

/-- Helper: **Cassels, Ch. 8, Example 5 (p. 125)**, given Example 4 (iv). Let $f_1, f_2$ be classically integral $\mathbb Z_2$-forms in the same number
$n$ of variables with unit determinants (Gram matrices $F_1, F_2$, Example 4), and $\vec b_1, \vec b_2 \in \mathbb Z_2^n$
characteristic vectors in the sense of Example 4 (i). Then $f_1, f_2$ are $\mathbb Q_2$-equivalent if and only if
$d(f_1) \equiv d(f_2) \pmod 8$ and $f_1(\vec b_1) \equiv f_2(\vec b_2) \pmod 8$. Here $d(f_i) = \det F_i$ and
$f_i(\vec b_i) = \vec b_i^{t}F_i\vec b_i$; $\mathbb Q_2$-equivalence is `QEquiv` of the matrices viewed over
$\mathbb Q_2$. The argument `hI` is the statement `Ex4ivHasse` of Example 4 (iv), proved as `ex4_iv`; see `ex5_iff`. -/
theorem ex5 (hI : Ex4ivHasse) (F₁ F₂ : Matrix (Fin n) (Fin n) ℤ_[2]) (hF₁ : F₁ᵀ = F₁) (hF₂ : F₂ᵀ = F₂)
    (hd₁ : IsUnit F₁.det) (hd₂ : IsUnit F₂.det) (b₁ b₂ : Fin n → ℤ_[2])
    (hb₁ : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F₁ *ᵥ a) - a ⬝ᵥ (F₁ *ᵥ b₁))
    (hb₂ : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F₂ *ᵥ a) - a ⬝ᵥ (F₂ *ᵥ b₂)) :
    QEquiv (F₁.map PadicInt.Coe.ringHom) (F₂.map PadicInt.Coe.ringHom) ↔
      (8 : ℤ_[2]) ∣ F₁.det - F₂.det ∧ (8 : ℤ_[2]) ∣ b₁ ⬝ᵥ (F₁ *ᵥ b₁) - b₂ ⬝ᵥ (F₂ *ᵥ b₂) := by
  obtain ⟨a₁, ha₁, s₁, hs₁, hh₁⟩ := hI.exists_diag n F₁ hF₁ hd₁ b₁ hb₁
  obtain ⟨a₂, ha₂, s₂, hs₂, hh₂⟩ := hI.exists_diag n F₂ hF₂ hd₂ b₂ hb₂
  obtain ⟨x₁, hx₁, hp₁⟩ := prod_eq_sq_mul_det ha₁
  obtain ⟨x₂, hx₂, hp₂⟩ := prod_eq_sq_mul_det ha₂
  rw [qequiv_iff_invariants ha₁ ha₂, hh₁, hh₂]
  constructor
  · rintro ⟨⟨t, ht0, ht⟩, hh⟩
    have hs : ((-1 : ℤ)) ^ s₁ = (-1) ^ s₂ := hh
    have hd : (8 : ℤ_[2]) ∣ F₂.det - F₁.det := by
      refine eight_dvd_of_sq hd₁ hd₂ (y := t * x₁ / x₂) ?_
      have h1 : x₂ ^ 2 * ((F₂.det : ℤ_[2]) : ℚ_[2]) = t ^ 2 * (x₁ ^ 2 * ((F₁.det : ℤ_[2]) : ℚ_[2])) := by
        rw [← hp₁, ← hp₂]; exact ht
      field_simp
      linear_combination h1
    have hd' : (8 : ℤ_[2]) ∣ F₁.det - F₂.det := by
      have := dvd_neg.2 hd; simpa using this
    refine ⟨hd', ?_⟩
    have e : b₁ ⬝ᵥ (F₁ *ᵥ b₁) - b₂ ⬝ᵥ (F₂ *ᵥ b₂) =
        ((b₁ ⬝ᵥ (F₁ *ᵥ b₁) - F₁.det - n + 1 - 4 * s₁) - (b₂ ⬝ᵥ (F₂ *ᵥ b₂) - F₂.det - n + 1 - 4 * s₂)) +
        (F₁.det - F₂.det) + (4 * (s₁ : ℤ_[2]) - 4 * (s₂ : ℤ_[2])) := by ring
    rw [e]
    exact dvd_add (dvd_add (dvd_sub hs₁ hs₂) hd') (eight_dvd_of_pow_eq hs)
  · rintro ⟨hd, ht⟩
    have h4 : (8 : ℤ_[2]) ∣ 4 * (s₁ : ℤ_[2]) - 4 * (s₂ : ℤ_[2]) := by
      have e : 4 * (s₁ : ℤ_[2]) - 4 * (s₂ : ℤ_[2]) =
          -((b₁ ⬝ᵥ (F₁ *ᵥ b₁) - F₁.det - n + 1 - 4 * s₁) -
            (b₂ ⬝ᵥ (F₂ *ᵥ b₂) - F₂.det - n + 1 - 4 * s₂)) +
          (b₁ ⬝ᵥ (F₁ *ᵥ b₁) - b₂ ⬝ᵥ (F₂ *ᵥ b₂)) - (F₁.det - F₂.det) := by ring
      rw [e]
      exact dvd_sub (dvd_add (dvd_neg.2 (dvd_sub hs₁ hs₂)) ht) hd
    refine ⟨?_, by rw [pow_eq_of_eight_dvd h4]⟩
    obtain ⟨y, hy0, hy⟩ := sq_of_eight_dvd hd₁ hd₂ (by simpa using dvd_neg.2 hd)
    refine ⟨x₂ * y / x₁, by positivity, ?_⟩
    rw [hp₁, hp₂, hy]
    field_simp


/-! ### Orthogonal sums of matrices over $\mathbb Z_2$ -/

section OrthSum

variable {R : Type*} [CommRing R] {m k : ℕ}

/-- Helper: entries of the orthogonal sum, upper left block. -/
theorem os_cc (F : Matrix (Fin m) (Fin m) R) (G : Matrix (Fin k) (Fin k) R) (i j : Fin m) :
    orthSumMat F G (Fin.castAdd k i) (Fin.castAdd k j) = F i j := by
  simp [dyadic_orthSumMat_eq]

/-- Helper: entries of the orthogonal sum, upper right block. -/
theorem os_cn (F : Matrix (Fin m) (Fin m) R) (G : Matrix (Fin k) (Fin k) R) (i : Fin m) (j : Fin k) :
    orthSumMat F G (Fin.castAdd k i) (Fin.natAdd m j) = 0 := by
  simp [dyadic_orthSumMat_eq]

/-- Helper: entries of the orthogonal sum, lower left block. -/
theorem os_nc (F : Matrix (Fin m) (Fin m) R) (G : Matrix (Fin k) (Fin k) R) (i : Fin k) (j : Fin m) :
    orthSumMat F G (Fin.natAdd m i) (Fin.castAdd k j) = 0 := by
  simp [dyadic_orthSumMat_eq]

/-- Helper: entries of the orthogonal sum, lower right block. -/
theorem os_nn (F : Matrix (Fin m) (Fin m) R) (G : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    orthSumMat F G (Fin.natAdd m i) (Fin.natAdd m j) = G i j := by
  simp [dyadic_orthSumMat_eq]

/-- Helper: the bilinear pairing against an orthogonal sum splits. -/
theorem quad_orthSum (A : Matrix (Fin m) (Fin m) R) (S : Matrix (Fin k) (Fin k) R) (a c : Fin (m + k) → R) :
    a ⬝ᵥ (orthSumMat A S *ᵥ c) = (a ∘ Fin.castAdd k) ⬝ᵥ (A *ᵥ (c ∘ Fin.castAdd k)) +
      (a ∘ Fin.natAdd m) ⬝ᵥ (S *ᵥ (c ∘ Fin.natAdd m)) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, os_cc, os_cn, os_nc, os_nn, Function.comp,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add]

/-- Helper: the determinant of an orthogonal sum. -/
theorem det_orthSum (A : Matrix (Fin m) (Fin m) R) (S : Matrix (Fin k) (Fin k) R) :
    (orthSumMat A S).det = A.det * S.det := by
  rw [dyadic_orthSumMat_eq, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

/-- Helper: mapping an orthogonal sum along a ring homomorphism. -/
theorem map_orthSum {R' : Type*} [CommRing R'] (f : R →+* R') (A : Matrix (Fin m) (Fin m) R)
    (S : Matrix (Fin k) (Fin k) R) :
    (orthSumMat A S).map f = orthSumMat (A.map f) (S.map f) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [orthSumMat, Matrix.reindex_apply, Matrix.fromBlocks]

/-- Helper: the orthogonal sum of diagonal matrices is the diagonal matrix of the concatenation. -/
theorem orthSum_diagonal (a : Fin m → R) (b : Fin k → R) :
    orthSumMat (diagonal a) (diagonal b) = diagonal (Fin.append a b) := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [os_cc]
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      simpa [Fin.ext_iff] using h
  · rw [os_cn, Matrix.diagonal_apply_ne]
    simp [Fin.ext_iff]; omega
  · rw [os_nc, Matrix.diagonal_apply_ne]
    simp [Fin.ext_iff]; omega
  · rw [os_nn]
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      simpa [Fin.ext_iff] using h

end OrthSum

/-! ### The Hasse invariant of a concatenation -/

/-- Helper: the Hasse invariant of a concatenation is the product of the two Hasse invariants and the Hilbert symbol
of the two products of entries (Cassels Ch. 4, Lemma 2.3 for sums). -/
theorem hasseVec_append {m k : ℕ} (hK : LocalHilbertField ℚ_[2]) (a : Fin m → ℚ_[2]) (b : Fin k → ℚ_[2])
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    hasseVec (Fin.append a b) = hasseVec a * hasseVec b * hilbertSymbol ℚ_[2] (∏ i, a i) (∏ j, b j) := by
  have hpb : (∏ j, b j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hb j
  have hcross : ∏ i, ∏ j, hilbertSymbol ℚ_[2] (a i) (b j) = hilbertSymbol ℚ_[2] (∏ i, a i) (∏ j, b j) := by
    have h1 : ∀ i, ∏ j, hilbertSymbol ℚ_[2] (a i) (b j) = hilbertSymbol ℚ_[2] (a i) (∏ j, b j) :=
      fun i => hs_prod_right hK (ha i) hb
    simp only [h1]
    have h2 : ∀ i, hilbertSymbol ℚ_[2] (a i) (∏ j, b j) = hilbertSymbol ℚ_[2] (∏ j, b j) (a i) :=
      fun i => hilbertSymbol_comm _ _ _
    simp only [h2]
    rw [hs_prod_right hK hpb ha, hilbertSymbol_comm]
  rw [← hcross]
  unfold hasseVec
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  have e1 : ∀ (i j : Fin m), (Fin.castAdd k i < Fin.castAdd k j) ↔ i < j := fun i j => Iff.rfl
  have e2 : ∀ (i : Fin m) (j : Fin k), Fin.castAdd k i < Fin.natAdd m j := fun i j => by
    show (i : ℕ) < m + (j : ℕ); omega
  have e3 : ∀ (i : Fin k) (j : Fin m), ¬ Fin.natAdd m i < Fin.castAdd k j := fun i j => by
    show ¬ m + (i : ℕ) < (j : ℕ); omega
  simp only [e1, e2, e3, Fin.natAdd_lt_natAdd_iff, ite_true, ite_false, Finset.prod_const_one,
    Finset.prod_mul_distrib]
  ring

/-! ### The inductive invariant -/

/-- **The inductive statement** `GoodV M t`: the unimodular $\mathbb Z_2$-form with Gram matrix $M$ in $k$ variables is
$\mathbb Q_2$-equivalent to a diagonal form $\langle a_0, \dots, a_{k-1}\rangle$ with Hasse invariant $(-1)^{s}$, where
$4s \equiv t - \det M - k + 1 \pmod 8$ ($t$ plays the role of $f(\vec b)$). -/
def GoodV {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ_[2]) (t : ℤ_[2]) : Prop :=
  ∃ a : Fin k → ℚ_[2], QDiag (M.map PadicInt.Coe.ringHom) a ∧
    ∃ s : ℕ, (8 : ℤ_[2]) ∣ (t - M.det - k + 1 - 4 * s) ∧ hasseVec a = (-1) ^ s

/-- Helper: $\mathbb Q_2$-equivalence is compatible with orthogonal sums. -/
theorem QEquiv.orthSum {m k : ℕ} {B B' : Matrix (Fin m) (Fin m) ℚ_[2]} {E E' : Matrix (Fin k) (Fin k) ℚ_[2]}
    (h1 : QEquiv B B') (h2 : QEquiv E E') : QEquiv (orthSumMat B E) (orthSumMat B' E') := by
  obtain ⟨P, hP, rfl⟩ := h1
  obtain ⟨R, hR, rfl⟩ := h2
  refine ⟨orthSumMat P R, ?_, ?_⟩
  · rw [det_orthSum]; exact hP.mul hR
  · rw [dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, dyadic_orthSumMat_eq, Matrix.transpose_submatrix,
      ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
      ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp

/-- Helper: a unit of $\mathbb Z_2$ is $r + 8c$ with $r \in \{1, 3, 5, 7\}$ and has reduction $r$ modulo $2^3$. -/
theorem unit_data {d : ℤ_[2]} (hd : IsUnit d) :
    ∃ (r : ℤ) (c : ℤ_[2]), d = r + 8 * c ∧ (r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) ∧
      PadicInt.toZModPow 3 d = (r : ZMod (2 ^ 3)) := by
  obtain ⟨r, hr, c, hc⟩ := dyadic_exists_mod8 hd
  refine ⟨r, c, ?_, hr, ?_⟩
  · have : d = r + (2 : ℤ_[2]) ^ 3 * c := by rw [← hc]; ring
    rw [this]; norm_num
  · have h : (d - r) ∈ RingHom.ker (PadicInt.toZModPow 3) := by
      rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; exact ⟨c, by simpa using hc⟩
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
    rw [h]; simp

/-- Helper: for $r, r' \in \{1,3,5,7\}$, $(r-1)(r'-1) + 4\,\varepsilon(r)\varepsilon(r') \equiv 0 \pmod 8$, where
$\varepsilon$ is `HilbertLocal.twoEps`. -/
theorem eps_arith {r r' : ℤ} (h : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) (h' : r' = 1 ∨ r' = 3 ∨ r' = 5 ∨ r' = 7) :
    (8 : ℤ) ∣ (r - 1) * (r' - 1) + 4 * ((HilbertLocal.twoEps (r : ZMod (2 ^ 3)) *
      HilbertLocal.twoEps (r' : ZMod (2 ^ 3)) : ℕ) : ℤ) := by
  rcases h with rfl | rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl | rfl <;>
    simp [HilbertLocal.twoEps] <;> decide

/-- Helper: the Hilbert symbol of two units of $\mathbb Z_2$ and the $\varepsilon$ exponent. -/
theorem hs_units {d d' : ℤ_[2]} (hd : IsUnit d) (hd' : IsUnit d') :
    hilbertSymbol ℚ_[2] ((d : ℤ_[2]) : ℚ_[2]) ((d' : ℤ_[2]) : ℚ_[2]) =
      (-1) ^ (HilbertLocal.twoEps (PadicInt.toZModPow 3 d) * HilbertLocal.twoEps (PadicInt.toZModPow 3 d')) := by
  have := HilbertLocal.hilbertSymbol_two_formula 0 0 hd.unit hd'.unit
  simpa using this

/-- **Orthogonal sums** (the induction step for sums): if $M_1$, $M_2$ are unimodular and `GoodV` holds for them with
values $t_1, t_2$, then it holds for $M_1 \perp M_2$ with value $t_1 + t_2$. -/
theorem GoodV.orthSum {m k : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[2]} {S : Matrix (Fin k) (Fin k) ℤ_[2]}
    {tA tS : ℤ_[2]} (hA : GoodV A tA) (hS : GoodV S tS) (hdA : IsUnit A.det) (hdS : IsUnit S.det) :
    GoodV (orthSumMat A S) (tA + tS) := by
  have hK : LocalHilbertField ℚ_[2] := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact localHilbertField_padic (p := 2)
  obtain ⟨a₁, hq₁, s₁, hs₁, hh₁⟩ := hA
  obtain ⟨a₂, hq₂, s₂, hs₂, hh₂⟩ := hS
  obtain ⟨x₁, hx₁, hp₁⟩ := prod_eq_sq_mul_det hq₁
  obtain ⟨x₂, hx₂, hp₂⟩ := prod_eq_sq_mul_det hq₂
  obtain ⟨r, c, hrc, hr, hred⟩ := unit_data hdA
  obtain ⟨r', c', hrc', hr', hred'⟩ := unit_data hdS
  refine ⟨Fin.append a₁ a₂, ⟨?_, ?_⟩, s₁ + s₂ + HilbertLocal.twoEps (PadicInt.toZModPow 3 A.det) *
    HilbertLocal.twoEps (PadicInt.toZModPow 3 S.det), ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using hq₁.1 i
    · simpa using hq₂.1 i
  · rw [map_orthSum, ← orthSum_diagonal]
    exact QEquiv.orthSum hq₁.2 hq₂.2
  · rw [det_orthSum]
    have e1 := eps_arith hr hr'
    rw [← hred, ← hred'] at e1
    obtain ⟨q, hq⟩ := e1
    have hq' : ((r : ℤ_[2]) - 1) * ((r' : ℤ_[2]) - 1) + 4 * ((HilbertLocal.twoEps (PadicInt.toZModPow 3 A.det) *
        HilbertLocal.twoEps (PadicInt.toZModPow 3 S.det) : ℕ) : ℤ_[2]) = 8 * (q : ℤ_[2]) := by
      exact_mod_cast hq
    have key : (tA + tS) - A.det * S.det - ((m + k : ℕ) : ℤ_[2]) + 1 -
        4 * ((s₁ + s₂ + HilbertLocal.twoEps (PadicInt.toZModPow 3 A.det) *
          HilbertLocal.twoEps (PadicInt.toZModPow 3 S.det) : ℕ) : ℤ_[2]) =
        ((tA - A.det - m + 1 - 4 * s₁) + (tS - S.det - k + 1 - 4 * s₂)) -
          8 * ((q : ℤ_[2]) + c * (r' - 1) + c' * (r - 1) + 8 * c * c') := by
      push_cast at hq' ⊢
      linear_combination (-(S.det - 1)) * hrc + (-((r : ℤ_[2]) - 1 + 8 * c)) * hrc' - hq'
    rw [key]
    exact dvd_sub (dvd_add hs₁ hs₂) (dvd_mul_right _ _)
  · rw [hasseVec_append hK a₁ a₂ hq₁.1 hq₂.1, hh₁, hh₂, hp₁, hp₂, hs_sq_left _ _ _ hx₁, hs_sq_right _ _ _ hx₂,
      hs_units hdA hdS, pow_add, pow_add]

/-- Helper: congruence invariance of `GoodV`. -/
theorem GoodV.congr {k : ℕ} {M M' : Matrix (Fin k) (Fin k) ℤ_[2]} {t : ℤ_[2]} (T : Matrix (Fin k) (Fin k) ℤ_[2])
    (hT : IsUnit T.det) (hMM' : M' = Tᵀ * M * T) (h : GoodV M' t) : GoodV M t := by
  obtain ⟨a, ⟨ha, hq⟩, s, hs, hh⟩ := h
  have hTu : IsUnit ((T.det : ℤ_[2]) : ℚ_[2]) := by
    have := PadicInt.isUnit_iff.1 hT
    exact isUnit_iff_ne_zero.2 (fun h0 => by rw [PadicInt.norm_def, h0] at this; simp at this)
  refine ⟨a, ⟨ha, ?_⟩, s, ?_, hh⟩
  · refine QEquiv.trans ⟨T.map PadicInt.Coe.ringHom, ?_, ?_⟩ hq
    · rw [dyadic_det_map_coe]; exact hTu
    · rw [hMM', Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  · have hdet : M'.det = T.det ^ 2 * M.det := by
      rw [hMM', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
    have e : t - M.det - k + 1 - 4 * s = (t - M'.det - k + 1 - 4 * s) + (T.det ^ 2 - 1) * M.det := by
      rw [hdet]; ring
    rw [e]
    exact dvd_add hs ((eight_dvd_sq_sub_one hT).mul_right _)

/-- Helper: `GoodV` depends on $t$ only modulo $8$. -/
theorem GoodV.val {k : ℕ} {M : Matrix (Fin k) (Fin k) ℤ_[2]} {t t' : ℤ_[2]} (h : GoodV M t)
    (ht : (8 : ℤ_[2]) ∣ t - t') : GoodV M t' := by
  obtain ⟨a, hq, s, hs, hh⟩ := h
  refine ⟨a, hq, s, ?_, hh⟩
  have e : t' - M.det - k + 1 - 4 * s = (t - M.det - k + 1 - 4 * s) - (t - t') := by ring
  rw [e]; exact dvd_sub hs ht

/-! ### Atoms: one-dimensional forms, $2xy$ and $2x^{2} + 2xy + 2y^{2}$ -/

/-- Helper: $2 \mid x$ in $\mathbb Z_2$ iff the reduction of $x$ modulo $2$ vanishes. -/
theorem two_dvd_iff_toZMod (x : ℤ_[2]) : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  simp

/-- Helper: a characteristic vector of $f(\vec a) \equiv f(\vec a, \vec b) \pmod 2$ (Example 4 (i)). -/
def IsChar {k : ℕ} (F : Matrix (Fin k) (Fin k) ℤ_[2]) (b : Fin k → ℤ_[2]) : Prop :=
  ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F *ᵥ a) - a ⬝ᵥ (F *ᵥ b)

/-- Helper: a one-dimensional form with unit coefficient is `GoodV` with $t = $ its coefficient. -/
theorem goodV_one (B : Matrix (Fin 1) (Fin 1) ℤ_[2]) (hu : IsUnit (B 0 0)) : GoodV B (B 0 0) := by
  have hne : ((B 0 0 : ℤ_[2]) : ℚ_[2]) ≠ 0 := fun h => hu.ne_zero (by simpa using h)
  refine ⟨![((B 0 0 : ℤ_[2]) : ℚ_[2])], ⟨?_, ?_⟩, 0, ?_, ?_⟩
  · intro i; fin_cases i; simpa using hne
  · refine ⟨1, by simp, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp
  · rw [Matrix.det_fin_one]; simp
  · simp [hasseVec]

/-- Helper: `(1)` is a characteristic vector of a one-dimensional form. -/
theorem isChar_one (B : Matrix (Fin 1) (Fin 1) ℤ_[2]) : IsChar B (fun _ => 1) := by
  intro a
  have key : ∀ z : ZMod 2, z * (z - 1) = 0 := by decide
  have e : a ⬝ᵥ (B *ᵥ a) - a ⬝ᵥ (B *ᵥ fun _ => 1) = B 0 0 * (a 0 * (a 0 - 1)) := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]; ring
  rw [e]
  refine Dvd.dvd.mul_left ?_ _
  rw [two_dvd_iff_toZMod, map_mul, map_sub, map_one]
  exact key _

/-- Helper: the value of the characteristic vector `(1)` of a one-dimensional form. -/
theorem value_one (B : Matrix (Fin 1) (Fin 1) ℤ_[2]) :
    (fun _ : Fin 1 => (1 : ℤ_[2])) ⬝ᵥ (B *ᵥ fun _ => 1) = B 0 0 := by
  simp [dotProduct, Matrix.mulVec]

/-- Helper: $2xy$ (the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$) is `GoodV` with $t = 0$. -/
theorem goodV_hyp : GoodV (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 := by
  refine ⟨![1, -1], ⟨?_, ?_⟩, 0, ?_, ?_⟩
  · intro i; fin_cases i <;> simp
  · refine ⟨!![1, 1; 1/2, -1/2], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      refine isUnit_iff_ne_zero.2 ?_
      norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> norm_num
  · rw [Matrix.det_fin_two_of]; norm_num
  · rw [hasseVec_two, hs_one_left]; simp

/-- Helper: $2x^{2} + 2xy + 2y^{2}$ is `GoodV` with $t = 0$ (Hasse invariant $(2, 6)_2 = -1$). -/
theorem goodV_ell : GoodV (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 := by
  have hc2 : (((2 : ℤ_[2])) : ℚ_[2]) = 2 := by norm_cast
  have hc3 : (((3 : ℤ_[2])) : ℚ_[2]) = 3 := by norm_cast
  refine ⟨![2, 6], ⟨?_, ?_⟩, 1, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · refine ⟨!![1, -1; 0, 2], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      refine isUnit_iff_ne_zero.2 ?_
      norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hc2] <;> norm_num
  · rw [Matrix.det_fin_two_of]; exact ⟨-1, by norm_num⟩
  · rw [hasseVec_two]
    have h := HilbertLocal.hilbertSymbol_two_formula 1 1 1 dyadic_isUnit_three.unit
    have h6 : ((2 : ℚ_[2]) ^ 1 * (((dyadic_isUnit_three.unit : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2])) = 6 := by
      rw [IsUnit.unit_spec]; rw [hc3]; norm_num
    have h2 : ((2 : ℚ_[2]) ^ 1 * ((((1 : ℤ_[2]ˣ)) : ℤ_[2]) : ℚ_[2])) = 2 := by simp
    rw [h6, h2] at h
    rw [h]
    have h3 : PadicInt.toZModPow 3 (((dyadic_isUnit_three.unit : ℤ_[2]ˣ) : ℤ_[2])) = (3 : ZMod (2 ^ 3)) := by
      rw [IsUnit.unit_spec]
      have h33 : (3 : ℤ_[2]) = ((3 : ℕ) : ℤ_[2]) := by norm_num
      rw [h33, map_natCast]; norm_num
    rw [h3]
    simp [HilbertLocal.twoEps, HilbertLocal.twoOmega]
    decide

/-- Helper: `0` is a characteristic vector of $2xy$. -/
theorem isChar_hyp : IsChar (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 := by
  intro a
  refine ⟨a 0 * a 1, ?_⟩
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]; ring

/-- Helper: `0` is a characteristic vector of $2x^{2} + 2xy + 2y^{2}$. -/
theorem isChar_ell : IsChar (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 := by
  intro a
  refine ⟨a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2, ?_⟩
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]; ring

/-! ### Characteristic vectors and congruences -/

/-- Helper: the form after a change of variables. -/
theorem cong_quad {k : ℕ} (T N : Matrix (Fin k) (Fin k) ℤ_[2]) (x y : Fin k → ℤ_[2]) :
    x ⬝ᵥ ((Tᵀ * N * T) *ᵥ y) = (T *ᵥ x) ⬝ᵥ (N *ᵥ (T *ᵥ y)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Tᵀ,
    Matrix.vecMul_transpose]

/-- Helper: characteristic vectors transport along a change of variables. -/
theorem isChar_cong {k : ℕ} {M M' : Matrix (Fin k) (Fin k) ℤ_[2]} {T : Matrix (Fin k) (Fin k) ℤ_[2]}
    (hT : IsUnit T.det) (hMM' : M' = Tᵀ * M * T) {b : Fin k → ℤ_[2]} (hb : IsChar M b) :
    IsChar M' (T⁻¹ *ᵥ b) ∧ (T⁻¹ *ᵥ b) ⬝ᵥ (M' *ᵥ (T⁻¹ *ᵥ b)) = b ⬝ᵥ (M *ᵥ b) := by
  have hTT : T *ᵥ (T⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]
  refine ⟨fun a' => ?_, ?_⟩
  · have := hb (T *ᵥ a')
    rw [hMM', cong_quad, cong_quad, hTT]
    exact this
  · rw [hMM', cong_quad, hTT]

/-- Helper: the concatenation of characteristic vectors is a characteristic vector of the orthogonal sum. -/
theorem isChar_append {m k : ℕ} {A : Matrix (Fin m) (Fin m) ℤ_[2]} {S : Matrix (Fin k) (Fin k) ℤ_[2]}
    {bA : Fin m → ℤ_[2]} {bS : Fin k → ℤ_[2]} (hA : IsChar A bA) (hS : IsChar S bS) :
    IsChar (orthSumMat A S) (Fin.append bA bS) := by
  intro a
  have e1 : (Fin.append bA bS) ∘ Fin.castAdd k = bA := by funext i; simp
  have e2 : (Fin.append bA bS) ∘ Fin.natAdd m = bS := by funext i; simp
  rw [quad_orthSum, quad_orthSum, e1, e2]
  have := dvd_add (hA (a ∘ Fin.castAdd k)) (hS (a ∘ Fin.natAdd m))
  convert this using 1; ring

/-- Helper: the value of the concatenation of two vectors on an orthogonal sum. -/
theorem value_append {m k : ℕ} (A : Matrix (Fin m) (Fin m) ℤ_[2]) (S : Matrix (Fin k) (Fin k) ℤ_[2])
    (bA : Fin m → ℤ_[2]) (bS : Fin k → ℤ_[2]) :
    (Fin.append bA bS) ⬝ᵥ (orthSumMat A S *ᵥ Fin.append bA bS) = bA ⬝ᵥ (A *ᵥ bA) + bS ⬝ᵥ (S *ᵥ bS) := by
  have e1 : (Fin.append bA bS) ∘ Fin.castAdd k = bA := by funext i; simp
  have e2 : (Fin.append bA bS) ∘ Fin.natAdd m = bS := by funext i; simp
  rw [quad_orthSum, e1, e2]

/-! ### Splitting off a block -/

/-- Helper: from a block $B$ with $C = B\Lambda$, a unimodular change of variables splits off $B$ (over any
commutative ring; the analogue of `dyadic_zpEquiv_split`). -/
theorem split_front {R : Type*} [CommRing R] {a b : ℕ} (F : Matrix (Fin (a + b)) (Fin (a + b)) R) (hF : Fᵀ = F)
    (Λ : Matrix (Fin a) (Fin b) R)
    (hC : F.submatrix (Fin.castAdd b) (Fin.natAdd a) =
      F.submatrix (Fin.castAdd b) (Fin.castAdd b) * Λ) :
    ∃ T : Matrix (Fin (a + b)) (Fin (a + b)) R, T.det = 1 ∧
      Tᵀ * F * T = orthSumMat (F.submatrix (Fin.castAdd b) (Fin.castAdd b))
        (F.submatrix (Fin.natAdd a) (Fin.natAdd a) -
          Λᵀ * F.submatrix (Fin.castAdd b) (Fin.castAdd b) * Λ) := by
  set B := F.submatrix (Fin.castAdd b) (Fin.castAdd b) with hB
  set C := F.submatrix (Fin.castAdd b) (Fin.natAdd a) with hCdef
  set E := F.submatrix (Fin.natAdd a) (Fin.natAdd a) with hE
  have hBt : Bᵀ = B := by
    ext i j; simp [hB, Matrix.transpose_apply]; exact congrFun (congrFun hF _) _
  have hFe : F = (Matrix.fromBlocks B C Cᵀ E).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [hB, hCdef, hE, Matrix.transpose_apply, Matrix.fromBlocks]
    exact congrFun (congrFun hF _) _
  refine ⟨(Matrix.fromBlocks 1 (-Λ) 0 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm, ?_, ?_⟩
  · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]; simp
  have hCt : Cᵀ = Λᵀ * B := by
    rw [hC, Matrix.transpose_mul, hBt]
  conv_lhs => rw [hFe]
  rw [dyadic_orthSumMat_eq, Matrix.transpose_submatrix,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective,
    ← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  simp [hC, hBt, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  abel

/-- Helper: a permutation of the variables is a unimodular change of variables. -/
theorem perm_cong {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ_[2]) (σ : Equiv.Perm (Fin k)) :
    ∃ P : Matrix (Fin k) (Fin k) ℤ_[2], IsUnit P.det ∧ Pᵀ * M * P = M.submatrix σ σ := by
  refine ⟨(1 : Matrix (Fin k) (Fin k) ℤ_[2]).submatrix id σ, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := (1 : Matrix (Fin k) (Fin k) ℤ_[2]).submatrix σ id) ?_
    rw [← Matrix.submatrix_mul _ _ _ _ _ σ.bijective, Matrix.mul_one]; simp
  · rw [Matrix.transpose_submatrix, Matrix.transpose_one]
    calc _ = (1 : Matrix (Fin k) (Fin k) ℤ_[2]).submatrix σ id * M.submatrix id id *
        (1 : Matrix (Fin k) (Fin k) ℤ_[2]).submatrix id σ := rfl
      _ = M.submatrix σ σ := by
        rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
          ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one]

/-- Helper: $\mathbb Z_2$-equivalence of integral matrices, from `ZpEquiv` of their images in $\mathbb Q_2$. -/
theorem zp_to_z {k : ℕ} {M G : Matrix (Fin k) (Fin k) ℤ_[2]}
    (h : ZpEquiv (M.map PadicInt.Coe.ringHom) (G.map PadicInt.Coe.ringHom)) :
    ∃ T : Matrix (Fin k) (Fin k) ℤ_[2], IsUnit T.det ∧ Tᵀ * M * T = G := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.val, (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit, ?_⟩
  have h2 : (T.val ᵀ * M * T.val).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) =
      G.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    exact hT
  exact Matrix.map_injective (fun x y hxy => Subtype.ext hxy) h2

/-! ### The induction -/

/-- Helper: **the induction step.** If a unimodular symmetric $M$ is carried by a unimodular change of variables $T$ to
an orthogonal sum $A \perp S$, where `GoodV` holds for $A$ at the value of a characteristic vector of $A$ and (by
induction) for every characteristic vector of $S$, then `GoodV` holds for $M$ at the value of every characteristic
vector of $M$. -/
theorem good_step {m k : ℕ} {M : Matrix (Fin (m + k)) (Fin (m + k)) ℤ_[2]} (hM : Mᵀ = M) (hd : IsUnit M.det)
    {A : Matrix (Fin m) (Fin m) ℤ_[2]} {S : Matrix (Fin k) (Fin k) ℤ_[2]}
    {T : Matrix (Fin (m + k)) (Fin (m + k)) ℤ_[2]} (hT : IsUnit T.det) (hTe : Tᵀ * M * T = orthSumMat A S)
    {bA : Fin m → ℤ_[2]} (hbA : IsChar A bA) (hA : GoodV A (bA ⬝ᵥ (A *ᵥ bA)))
    (hS : Sᵀ = S → IsUnit S.det → ∀ bS : Fin k → ℤ_[2], IsChar S bS → GoodV S (bS ⬝ᵥ (S *ᵥ bS))) :
    ∀ b : Fin (m + k) → ℤ_[2], IsChar M b → GoodV M (b ⬝ᵥ (M *ᵥ b)) := by
  have hOSsym : (orthSumMat A S)ᵀ = orthSumMat A S := by
    rw [← hTe]; simp [Matrix.transpose_mul, hM, Matrix.mul_assoc]
  have hdet : (orthSumMat A S).det = T.det ^ 2 * M.det := by
    rw [← hTe, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
  have hdOS : IsUnit (orthSumMat A S).det := by rw [hdet]; exact (hT.pow 2).mul hd
  rw [det_orthSum] at hdOS
  obtain ⟨hdA, hdS⟩ := IsUnit.mul_iff.1 hdOS
  have hSsym : Sᵀ = S := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hOSsym (Fin.natAdd m i)) (Fin.natAdd m j)
    simpa [Matrix.transpose_apply, os_nn] using this
  intro b hb
  obtain ⟨bS, hbS⟩ := ex4_exists_char S hSsym hdS
  have hGS := hS hSsym hdS bS hbS
  have hOS := hA.orthSum hGS hdA hdS
  obtain ⟨hb', hv⟩ := isChar_cong hT hTe.symm hb
  have hc := isChar_append hbA hbS
  have h8 := ex4_char_value (orthSumMat A S) hOSsym (by rw [det_orthSum]; exact hdOS) hb' hc
  rw [hv, value_append] at h8
  have hOS' : GoodV (orthSumMat A S) (b ⬝ᵥ (M *ᵥ b)) := by
    refine hOS.val ?_
    have := dvd_neg.2 h8
    convert this using 1; ring
  exact GoodV.congr T hT hTe.symm hOS'

/-- Helper: **the main induction.** Every unimodular classically integral $\mathbb Z_2$-form is `GoodV` at the value
$f(\vec b)$ of every characteristic vector $\vec b$. -/
theorem good_main : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ_[2]), Mᵀ = M → IsUnit M.det →
    ∀ b : Fin n → ℤ_[2], IsChar M b → GoodV M (b ⬝ᵥ (M *ᵥ b)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hM hd b hb
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun i => i.elim0, ⟨fun i => i.elim0, ⟨1, by simp, Subsingleton.elim _ _⟩⟩, 0, ?_, ?_⟩
    · simp
    · simp [hasseVec]
  by_cases hpiv : ∃ i, IsUnit (M i i)
  · obtain ⟨i, hi⟩ := hpiv
    obtain ⟨k, rfl⟩ : ∃ k, n = 1 + k := ⟨n - 1, by omega⟩
    obtain ⟨P, hP, hPe⟩ := perm_cong M (Equiv.swap 0 i)
    set M1 := M.submatrix (Equiv.swap 0 i) (Equiv.swap 0 i) with hM1
    have hM1sym : M1ᵀ = M1 := by rw [hM1, Matrix.transpose_submatrix, hM]
    have hu0 : IsUnit (M1 (Fin.castAdd k 0) (Fin.castAdd k 0)) := by
      have : Fin.castAdd k (0 : Fin 1) = 0 := by ext; simp
      rw [this]
      simpa [hM1] using hi
    obtain ⟨u, hu⟩ := hu0
    set Λ : Matrix (Fin 1) (Fin k) ℤ_[2] :=
      Matrix.of fun _ j => M1 (Fin.castAdd k 0) (Fin.natAdd 1 j) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hΛ
    have hC : M1.submatrix (Fin.castAdd k) (Fin.natAdd 1) =
        M1.submatrix (Fin.castAdd k) (Fin.castAdd k) * Λ := by
      refine Matrix.ext fun i j => ?_
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst hi0
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_one, hΛ, Matrix.of_apply]
      rw [← hu, mul_left_comm, Units.mul_inv, mul_one]
    obtain ⟨T1, hT1, hT1e⟩ := split_front M1 hM1sym Λ hC
    refine good_step (m := 1) (k := k) hM hd
      (A := M1.submatrix (Fin.castAdd k) (Fin.castAdd k))
      (S := M1.submatrix (Fin.natAdd 1) (Fin.natAdd 1) -
        Λᵀ * M1.submatrix (Fin.castAdd k) (Fin.castAdd k) * Λ) (T := P * T1) ?_ ?_ (isChar_one _) ?_ ?_ b hb
    · rw [Matrix.det_mul, hT1, mul_one]; exact hP
    · have : (P * T1)ᵀ * M * (P * T1) = T1ᵀ * (Pᵀ * M * P) * T1 := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [this, hPe, hT1e]
    · rw [value_one]
      refine goodV_one _ ?_
      show IsUnit (M1 (Fin.castAdd k 0) (Fin.castAdd k 0))
      rw [← hu]; exact u.isUnit
    · intro hS hdS bS hbS
      exact ih k (by omega) _ hS hdS bS hbS
  · push Not at hpiv
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · exfalso
      obtain rfl : n = 1 := by omega
      exact hpiv 0 (by rw [Matrix.det_fin_one] at hd; exact hd)
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
    have hEU : dyadicEU (M.map PadicInt.Coe.ringHom) := by
      refine ⟨by rw [← Matrix.transpose_map, hM], fun i j => PadicInt.norm_le_one _, fun i => ?_, ?_⟩
      · have : ‖M i i‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _)
          (fun h => hpiv i (PadicInt.isUnit_iff.2 h))
        simpa [Matrix.map_apply, PadicInt.norm_coe] using this
      · rw [dyadic_det_map_coe, PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 hd
    obtain ⟨X, E', hX, hE', hz⟩ := dyadic_EU_split hEU
    obtain ⟨Ez, hEz⟩ := dyadic_lift_mat hE'.2.1
    rcases hX with rfl | rfl
    · have hmap : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]).map PadicInt.Coe.ringHom =
          (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      have hz' : ZpEquiv (M.map PadicInt.Coe.ringHom)
          ((orthSumMat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ_[2]) Ez).map PadicInt.Coe.ringHom) := by
        rw [map_orthSum, hEz, hmap]; exact hz
      obtain ⟨T, hT, hTe⟩ := zp_to_z hz'
      exact good_step (m := 2) (k := m) hM hd hT hTe isChar_hyp (by simpa using goodV_hyp)
        (fun hS hdS bS hbS => ih m (by omega) Ez hS hdS bS hbS) b hb
    · have hmap : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).map PadicInt.Coe.ringHom =
          (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℚ_[2]) := by
        have hc2 : (((2 : ℤ_[2])) : ℚ_[2]) = 2 := by norm_cast
        ext i j; fin_cases i <;> fin_cases j <;> simp [hc2]
      have hz' : ZpEquiv (M.map PadicInt.Coe.ringHom)
          ((orthSumMat (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]) Ez).map PadicInt.Coe.ringHom) := by
        rw [map_orthSum, hEz, hmap]; exact hz
      obtain ⟨T, hT, hTe⟩ := zp_to_z hz'
      exact good_step (m := 2) (k := m) hM hd hT hTe isChar_ell (by simpa using goodV_ell)
        (fun hS hdS bS hbS => ih m (by omega) Ez hS hdS bS hbS) b hb

/-- **Example 4 (iv)** (the input `Ex4ivHasse`), proved: every classically integral $\mathbb Z_2$-form with unit
determinant is $\mathbb Q_2$-equivalent to a diagonal form whose Hasse invariant is $(-1)^{s}$ with
$4s \equiv f(\vec b) - d(f) - n + 1 \pmod 8$. -/
@[kb "cassels1978" "Ch. 8, Ex. 4 (iv), p. 125 ($c_2(f) = (-1)^s$)"]
theorem ex4_iv : Ex4ivHasse where
  exists_diag n F hF hd b hb := good_main n F hF hd b hb

/-- **Cassels, Ch. 8, Example 5 (p. 125), unconditional.** Let $f_1, f_2$ be classically integral $\mathbb Z_2$-forms in
the same number $n$ of variables with unit determinants, with characteristic vectors $\vec b_1, \vec b_2$
(Example 4 (i)). They are $\mathbb Q_2$-equivalent if and only if $d(f_1) \equiv d(f_2) \pmod 8$ and
$f_1(\vec b_1) \equiv f_2(\vec b_2) \pmod 8$. -/
@[kb "cassels1978" "Ch. 8, Ex. 5, p. 125"]
theorem ex5_iff (F₁ F₂ : Matrix (Fin n) (Fin n) ℤ_[2]) (hF₁ : F₁ᵀ = F₁) (hF₂ : F₂ᵀ = F₂)
    (hd₁ : IsUnit F₁.det) (hd₂ : IsUnit F₂.det) (b₁ b₂ : Fin n → ℤ_[2])
    (hb₁ : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F₁ *ᵥ a) - a ⬝ᵥ (F₁ *ᵥ b₁))
    (hb₂ : ∀ a, (2 : ℤ_[2]) ∣ a ⬝ᵥ (F₂ *ᵥ a) - a ⬝ᵥ (F₂ *ᵥ b₂)) :
    QEquiv (F₁.map PadicInt.Coe.ringHom) (F₂.map PadicInt.Coe.ringHom) ↔
      (8 : ℤ_[2]) ∣ F₁.det - F₂.det ∧ (8 : ℤ_[2]) ∣ b₁ ⬝ᵥ (F₁ *ᵥ b₁) - b₂ ⬝ᵥ (F₂ *ᵥ b₂) :=
  ex5 ex4_iv F₁ F₂ hF₁ hF₂ hd₁ hd₂ b₁ b₂ hb₁ hb₂

end QuadFormsKB.Cassels.Ex5

end
