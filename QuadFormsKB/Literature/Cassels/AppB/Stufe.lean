/-
# Cassels, Appendix B, §5: the Stufe (level) of an even-dimensional form

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), §5, p. 385.

**Source.** For an integer-valued form $Q$ in $n = 2k$ variables with Hessian (the book's even-diagonal integral matrix
$F$, so that $Q(\vec x) = \tfrac12 \vec x^{\mathsf T} H \vec x$), the book states that there is a uniquely defined integer
$N > 0$ such that $N H^{-1}$ corresponds (in the same way) to a primitive integer-valued form, calls it the *Stufe* of $Q$,
and remarks that $N$ and $\det H$ have the same prime factors (with different multiplicities in general).

**Conventions.** $H$ is `Q.hessian`; "$N H^{-1}$ corresponds to an integer-valued form" is the library predicate
`IsThetaLevel Q N` (`Siegel/ThetaModular.lean`): $N \cdot \tfrac12\vec y^{\mathsf T}H^{-1}\vec y \in \mathbb Z$ for all
$\vec y \in \mathbb Z^n$. "Primitive" is formalized as: no prime divides every value (`IsPrimitiveThetaLevel`); this is
equivalent to the book's primitivity of the coefficients, since the coefficients are integer combinations of values
(at $\vec e_i$ and $\vec e_i + \vec e_j$) and conversely.

**Formalized (all proved, no assumed inputs).**
* `stufe Q`: the least $N > 0$ with `IsThetaLevel Q N`; it exists for every $Q$ (`exists_pos_isThetaLevel`, with
  $N = |2\det H|$ when $\det H \ne 0$).
* `isThetaLevel_iff_stufe_dvd`: $N$ is a level iff `stufe Q` divides $N$ (this is the "uniquely defined").
* `isPrimitiveThetaLevel_stufe`, `eq_stufe_of_isPrimitiveThetaLevel`: the form at $N = $ `stufe Q` is primitive, and a
  level at which the form is primitive is `stufe Q`.
* `prime_dvd_stufe_iff`: a prime $p$ divides `stufe Q` iff $p \mid \det H$.

**Generalizations.** The book has $Q$ primitive, positive definite, $n = 2k \ge 4$. None of this is used: items 1, 2 hold
for every $Q$ (if $\det H = 0$ the library's `dualGram` is $0$ and `stufe Q` $= 1$); `prime_dvd_stufe_iff` needs only
$\det H \ne 0$; primitivity needs $\det H \ne 0$ and $n \ge 1$ (for $n = 0$ the form is zero, hence not primitive).
-/
import QuadFormsKB.Siegel.ThetaModular

open Matrix
open QuadFormsKB.Analysis (quadAt)

namespace QuadFormsKB.Siegel

noncomputable section

variable {n : ℕ}

/-! ### Real and integer forms of the dual -/

/-- Helper: the Hessian $H$ of $Q$ as a real matrix. -/
private abbrev hr (Q : QuadForm ℤ n) : Matrix (Fin n) (Fin n) ℝ := Q.hessian.map (Int.cast : ℤ → ℝ)

/-- Helper: $\det$ of the real Hessian is the cast of the integer determinant. -/
private lemma hr_det (Q : QuadForm ℤ n) : (hr Q).det = (Q.hessian.det : ℝ) := by
  have h := RingHom.map_det (Int.castRingHom ℝ) Q.hessian
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

/-- Helper: the real Hessian is symmetric. -/
private lemma hr_symm (Q : QuadForm ℤ n) : (hr Q).IsSymm := by
  ext i j
  simp [hr, QuadForm.hessian, add_comm]

/-- Helper: the library's `dualGram` is $\tfrac12 H^{-1}$ when $\det H \ne 0$. -/
private lemma dualGram_eq (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) :
    dualGram Q = (1 / 2 : ℝ) • (hr Q)⁻¹ := by
  have hu : IsUnit (hr Q).det := by
    rw [hr_det]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet)
  have h1 : (gramMatrix Q)⁻¹ = (2 : ℝ) • (hr Q)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [show gramMatrix Q = (1 / 2 : ℝ) • hr Q from rfl, smul_mul_smul_comm, Matrix.mul_nonsing_inv _ hu]
    simp
  rw [dualGram, h1, smul_smul]; norm_num

/-- Helper: $Q^*(\vec y) = \tfrac12 \vec y^{\mathsf T} H^{-1}\vec y$ when $\det H \ne 0$. -/
private lemma quadAt_dualGram (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (y : Fin n → ℤ) :
    quadAt (dualGram Q) y =
      (1 / 2 : ℝ) * ((fun i => (y i : ℝ)) ⬝ᵥ (hr Q)⁻¹ *ᵥ (fun i => (y i : ℝ))) := by
  rw [dualGram_eq Q hdet]; simp [quadAt, smul_mulVec, dotProduct_smul]

/-- Helper: the integer $c(\vec y) = \vec y^{\mathsf T}\operatorname{adj}(H)\,\vec y$, so that
$Q^*(\vec y) = c(\vec y)/(2\det H)$. -/
private def cf (Q : QuadForm ℤ n) (y : Fin n → ℤ) : ℤ := y ⬝ᵥ (Q.hessian.adjugate *ᵥ y)

/-- Helper: $Q^*(\vec y) = c(\vec y) / (2\det H)$ when $\det H \ne 0$. -/
private lemma quadAt_dualGram_cf (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (y : Fin n → ℤ) :
    quadAt (dualGram Q) y = (cf Q y : ℝ) / (2 * Q.hessian.det) := by
  have hd : (Q.hessian.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have hinv : (hr Q)⁻¹ = ((Q.hessian.det : ℝ))⁻¹ • Q.hessian.adjugate.map (Int.cast : ℤ → ℝ) := by
    rw [Matrix.inv_def, hr_det, Ring.inverse_eq_inv']
    congr 1
    have := (RingHom.map_adjugate (Int.castRingHom ℝ) Q.hessian)
    simpa [hr] using this.symm
  have key : ((fun i => (y i : ℝ)) ⬝ᵥ (Q.hessian.adjugate.map (Int.cast : ℤ → ℝ)) *ᵥ
      (fun i => (y i : ℝ))) = (cf Q y : ℝ) := by
    simp [cf, dotProduct, mulVec]
  rw [quadAt_dualGram Q hdet, hinv, Matrix.smul_mulVec, dotProduct_smul, key]
  simp only [smul_eq_mul]
  field_simp

/-- Helper: pure arithmetic form of the level criterion. -/
private lemma level_arith (N : ℕ) (c d : ℤ) (hd : d ≠ 0) :
    (∃ m : ℤ, (N : ℝ) * ((c : ℝ) / (2 * (d : ℝ))) = m) ↔ 2 * d ∣ (N : ℤ) * c := by
  have hd2 : (2 * (d : ℝ)) ≠ 0 := by
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    positivity
  rw [← mul_div_assoc]
  constructor
  · rintro ⟨m, hm⟩
    rw [div_eq_iff hd2] at hm
    exact ⟨m, by have : (N : ℤ) * c = m * (2 * d) := by exact_mod_cast hm
                 rw [this]; ring⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [div_eq_iff hd2]
    have : (N : ℤ) * c = m * (2 * d) := by rw [hm]; ring
    exact_mod_cast this

/-- Helper: for $\det H \ne 0$, $N$ is a level iff $2\det H \mid N\,c(\vec y)$ for all $\vec y$. -/
private lemma isThetaLevel_iff_dvd (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (N : ℕ) :
    IsThetaLevel Q N ↔ ∀ y, (2 * Q.hessian.det) ∣ (N : ℤ) * cf Q y := by
  unfold IsThetaLevel
  refine forall_congr' fun y => ?_
  rw [quadAt_dualGram_cf Q hdet]
  exact level_arith N _ _ hdet

/-- Helper: $2\,Q(\vec x) = \vec x^{\mathsf T} H \vec x$ over $\mathbb Z$. -/
private lemma two_mul_eval_hessian (Q : QuadForm ℤ n) (x : Fin n → ℤ) :
    2 * Q.eval x = x ⬝ᵥ (Q.hessian *ᵥ x) := by
  have h := Q.evalIn_eq_dotProduct ℤ x
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, QuadForm.eval] at h ⊢
  have h2 : x ⬝ᵥ (x ᵥ* Q.coeff) = x ⬝ᵥ (Q.coeff *ᵥ x) := by
    rw [dotProduct_comm, ← dotProduct_mulVec]
  rw [QuadForm.hessian, add_mulVec, dotProduct_add, mulVec_transpose, h2, ← h]
  ring

/-- Helper: $d \cdot c(\vec y) = 2\,Q(\operatorname{adj}(H)\vec y)$ is even, where $d = \det H$. -/
private lemma det_mul_cf_even (Q : QuadForm ℤ n) (y : Fin n → ℤ) :
    Q.hessian.det * cf Q y = 2 * Q.eval (Q.hessian.adjugate *ᵥ y) := by
  rw [two_mul_eval_hessian]
  have h : Q.hessian *ᵥ (Q.hessian.adjugate *ᵥ y) = Q.hessian.det • y := by
    rw [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]
  rw [dotProduct_comm, h, smul_dotProduct, cf, smul_eq_mul]

/-! ### Integrality of the scaled inverse -/

/-- Helper: real casts of standard basis vectors. -/
private lemma cast_single (i : Fin n) :
    (fun k => (((Pi.single i (1 : ℤ) : Fin n → ℤ) k : ℤ) : ℝ)) = Pi.single i (1 : ℝ) := by
  ext k
  by_cases h : k = i
  · subst h; simp
  · simp [h]

/-- Helper: if $r\,Q^*(\vec y) = m(\vec y) \in \mathbb Z$ for all integer $\vec y$ (and $\det H \ne 0$), then
$r H^{-1}$ is an integer matrix (entries by polarization: $r\,(H^{-1})_{ij} = m(\vec e_i + \vec e_j) - m(\vec e_i) -
m(\vec e_j)$). -/
private lemma exists_intMatrix (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (r : ℝ)
    (m : (Fin n → ℤ) → ℤ) (h : ∀ y, r * quadAt (dualGram Q) y = m y) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ, B.map (Int.cast : ℤ → ℝ) = r • (hr Q)⁻¹ := by
  set M := (hr Q)⁻¹ with hM
  have hMs : Mᵀ = M := by
    rw [hM, Matrix.transpose_nonsing_inv]
    have := hr_symm Q
    rw [Matrix.IsSymm] at this
    rw [this]
  have h' : ∀ y : Fin n → ℤ, r * ((fun i => (y i : ℝ)) ⬝ᵥ M *ᵥ (fun i => (y i : ℝ))) = 2 * m y := by
    intro y
    have := h y
    rw [quadAt_dualGram Q hdet] at this
    linarith
  have hsym : ∀ a b : Fin n → ℝ, b ⬝ᵥ M *ᵥ a = a ⬝ᵥ M *ᵥ b := by
    intro a b
    have : a ⬝ᵥ Mᵀ *ᵥ b = b ⬝ᵥ M *ᵥ a := by
      rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]
    rw [hMs] at this
    exact this.symm
  have hpol : ∀ a b : Fin n → ℤ, r * ((fun i => (a i : ℝ)) ⬝ᵥ M *ᵥ (fun i => (b i : ℝ))) =
      m (a + b) - m a - m b := by
    intro a b
    have h1 := h' (a + b)
    have h2 := h' a
    have h3 := h' b
    have hab : (fun i => (((a + b) i : ℤ) : ℝ)) = (fun i => (a i : ℝ)) + (fun i => (b i : ℝ)) := by
      ext i; simp
    rw [hab, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
      hsym (fun i => (a i : ℝ)) (fun i => (b i : ℝ))] at h1
    have : (m (a + b) : ℝ) - m a - m b = r * ((fun i => (a i : ℝ)) ⬝ᵥ M *ᵥ (fun i => (b i : ℝ))) := by
      linarith
    rw [← this]
  refine ⟨Matrix.of fun i j => m (Pi.single i 1 + Pi.single j 1) - m (Pi.single i 1) - m (Pi.single j 1), ?_⟩
  ext i j
  have := hpol (Pi.single i 1) (Pi.single j 1)
  rw [cast_single, cast_single] at this
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rw [← this]
  simp [dotProduct, mulVec, Pi.single_apply]

/-- Helper: $H \cdot (rH^{-1}) = r\,I$ for the real Hessian. -/
private lemma hr_mul_B (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (r : ℝ)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.map (Int.cast : ℤ → ℝ) = r • (hr Q)⁻¹) :
    ((Q.hessian * B).map (Int.cast : ℤ → ℝ)) = r • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  have hu : IsUnit (hr Q).det := by
    rw [hr_det]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hdet)
  have : (Q.hessian * B).map (Int.cast : ℤ → ℝ) = hr Q * B.map (Int.cast : ℤ → ℝ) := by
    exact Matrix.map_mul (f := Int.castRingHom ℝ)
  rw [this, hB, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hu]

/-! ### Existence and the definition of the Stufe -/

/-- Helper: if $\det H = 0$ every $N$ is a level (the library's `dualGram` is then $0$). -/
private lemma isThetaLevel_of_det_eq_zero (Q : QuadForm ℤ n) (hdet : Q.hessian.det = 0) (N : ℕ) :
    IsThetaLevel Q N := by
  have h0 : ¬ IsUnit (gramMatrix Q).det := by
    have : (gramMatrix Q).det = 0 := by
      rw [show gramMatrix Q = (1 / 2 : ℝ) • hr Q from rfl, Matrix.det_smul, hr_det, hdet]
      simp
    rw [this]; exact not_isUnit_zero
  intro y
  refine ⟨0, ?_⟩
  simp [dualGram, Matrix.nonsing_inv_apply_not_isUnit _ h0, quadAt]

/-- Helper: a positive level exists for every form ($N = 1$ if $\det H = 0$, $N = |2\det H|$ otherwise). -/
theorem exists_pos_isThetaLevel (Q : QuadForm ℤ n) : ∃ N : ℕ, 0 < N ∧ IsThetaLevel Q N := by
  by_cases hdet : Q.hessian.det = 0
  · exact ⟨1, one_pos, isThetaLevel_of_det_eq_zero Q hdet 1⟩
  · refine ⟨(2 * Q.hessian.det).natAbs, Int.natAbs_pos.mpr (mul_ne_zero two_ne_zero hdet), ?_⟩
    rw [isThetaLevel_iff_dvd Q hdet]
    intro y
    exact dvd_mul_of_dvd_left (Int.dvd_natAbs.mpr dvd_rfl) _

open scoped Classical in
/-- **The Stufe (level) of $Q$** (Cassels, App. B, §5, (5.18), p. 385): the least integer $N > 0$ such that
$N H^{-1}$ gives an integer-valued form, i.e. the least $N > 0$ with `IsThetaLevel Q N`
($N \cdot \tfrac12 \vec y^{\mathsf T}H^{-1}\vec y \in \mathbb Z$ for all $\vec y \in \mathbb Z^n$, $H$ = `Q.hessian`).
Argument: `Q`, the integral quadratic form in $n$ variables. It exists for every $Q$ (`exists_pos_isThetaLevel`); for
$\det H = 0$ the value is $1$ (the library's inverse of a singular matrix is $0$), which is outside the book's scope. -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (the Stufe N)"]
def stufe (Q : QuadForm ℤ n) : ℕ := Nat.find (exists_pos_isThetaLevel Q)

/-- Helper: the Stufe is positive. -/
theorem stufe_pos (Q : QuadForm ℤ n) : 0 < stufe Q := by
  classical
  exact (Nat.find_spec (exists_pos_isThetaLevel Q)).1

/-- The Stufe is a level: $\text{stufe}(Q) \cdot \tfrac12 \vec y^{\mathsf T}H^{-1}\vec y \in \mathbb Z$ for all integer
$\vec y$. Argument: `Q` the integral form. -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (the Stufe N is a level)"]
theorem isThetaLevel_stufe (Q : QuadForm ℤ n) : IsThetaLevel Q (stufe Q) := by
  classical
  exact (Nat.find_spec (exists_pos_isThetaLevel Q)).2

/-- Helper: minimality of the Stufe among positive levels. -/
theorem stufe_le {Q : QuadForm ℤ n} {N : ℕ} (hN : 0 < N) (h : IsThetaLevel Q N) : stufe Q ≤ N := by
  classical
  exact Nat.find_min' (exists_pos_isThetaLevel Q) ⟨hN, h⟩

/-- Helper: the gcd of two levels is a level (Bezout). -/
private lemma isThetaLevel_gcd {Q : QuadForm ℤ n} {a b : ℕ} (ha : IsThetaLevel Q a) (hb : IsThetaLevel Q b) :
    IsThetaLevel Q (Nat.gcd a b) := by
  intro y
  obtain ⟨m1, h1⟩ := ha y
  obtain ⟨m2, h2⟩ := hb y
  refine ⟨Nat.gcdA a b * m1 + Nat.gcdB a b * m2, ?_⟩
  have hg : ((Nat.gcd a b : ℕ) : ℝ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
    exact_mod_cast Nat.gcd_eq_gcd_ab a b
  rw [hg]; push_cast
  linear_combination (Nat.gcdA a b : ℝ) * h1 + (Nat.gcdB a b : ℝ) * h2

/-- **The Stufe is uniquely defined:** $N$ is a level iff the Stufe divides $N$ (the levels are exactly the multiples of
`stufe Q`). Arguments: `Q` the integral form, `N` a natural number ($N = 0$ is allowed and is a level). -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (the Stufe N is uniquely defined)"]
theorem isThetaLevel_iff_stufe_dvd (Q : QuadForm ℤ n) (N : ℕ) : IsThetaLevel Q N ↔ stufe Q ∣ N := by
  constructor
  · intro hN
    have hg := isThetaLevel_gcd hN (isThetaLevel_stufe Q)
    have hgpos : 0 < Nat.gcd N (stufe Q) := Nat.gcd_pos_of_pos_right _ (stufe_pos Q)
    have hle := stufe_le hgpos hg
    have hle' : Nat.gcd N (stufe Q) ≤ stufe Q := Nat.le_of_dvd (stufe_pos Q) (Nat.gcd_dvd_right _ _)
    have heq : Nat.gcd N (stufe Q) = stufe Q := le_antisymm hle' hle
    rw [← heq]
    exact Nat.gcd_dvd_left _ _
  · rintro ⟨k, rfl⟩ y
    obtain ⟨m, hm⟩ := isThetaLevel_stufe Q y
    refine ⟨k * m, ?_⟩
    push_cast
    rw [mul_comm (stufe Q : ℝ) k, mul_assoc, hm]

/-! ### Primitivity -/

/-- **Primitive at level $N$** (Cassels, App. B, §5, (5.18)): $N$ is a level and the integer-valued form
$\vec y \mapsto N \cdot \tfrac12\vec y^{\mathsf T}H^{-1}\vec y$ is primitive, i.e. there is no prime $p$ dividing all of
its values $N\,Q^*(\vec y)$, $\vec y \in \mathbb Z^n$. (Equivalent to the gcd of its coefficients being $1$.)
Arguments: `Q` the integral form, `N` the candidate level. -/
def IsPrimitiveThetaLevel (Q : QuadForm ℤ n) (N : ℕ) : Prop :=
  IsThetaLevel Q N ∧ ∀ p : ℕ, p.Prime →
    ¬ ∀ y : Fin n → ℤ, ∃ m : ℤ, (N : ℝ) * quadAt (dualGram Q) y = p * m

/-- **$N F^{-1}$ is primitive at $N$ = the Stufe** (Cassels, App. B, §5, (5.18), p. 385). Hypotheses: $\det H \ne 0$
and $n \ge 1$ (for $n = 0$ the form is zero, not primitive); the book has $n = 2k \ge 4$, $Q$ positive definite and
primitive, none of which is needed (*generalization*). *Proof idea:* if a prime $p$ divides all values, polarization
makes $(N/p)H^{-1}$ an integer matrix $B$; then $H B = (N/p) I$ forces $p \mid N$, and $N/p$ is a smaller level. -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (N F⁻¹ primitive)"]
theorem isPrimitiveThetaLevel_stufe [NeZero n] (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) :
    IsPrimitiveThetaLevel Q (stufe Q) := by
  refine ⟨isThetaLevel_stufe Q, fun p hp hall => ?_⟩
  choose m hm using hall
  set N := stufe Q with hNdef
  have hNpos : 0 < N := stufe_pos Q
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨B, hB⟩ := exists_intMatrix Q hdet ((N : ℝ) / p) m (fun y => by
    rw [div_mul_eq_mul_div, hm y]; field_simp)
  have hHB := hr_mul_B Q hdet _ B hB
  have h00 := congrFun (congrFun hHB 0) 0
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.map_apply] at h00
  set t : ℤ := (Q.hessian * B) 0 0 with ht
  have hNt : (N : ℝ) = p * t := by rw [h00]; field_simp
  have hNt' : (N : ℤ) = p * t := by exact_mod_cast hNt
  have htpos : 0 < t := by
    have : (0 : ℝ) < t := by
      have : (0 : ℝ) < N := by exact_mod_cast hNpos
      rw [hNt] at this
      exact pos_of_mul_pos_right this hp0.le
    exact_mod_cast this
  have hlev : IsThetaLevel Q t.toNat := by
    intro y
    refine ⟨m y, ?_⟩
    have h1 := hm y
    have : ((t.toNat : ℕ) : ℝ) = t := by exact_mod_cast Int.toNat_of_nonneg htpos.le
    rw [this]
    rw [hNt] at h1
    have : (p : ℝ) * (t * quadAt (dualGram Q) y) = p * m y := by linarith
    exact mul_left_cancel₀ hp0.ne' this
  have hle := stufe_le (by omega) hlev
  have h2 : 2 ≤ p := hp.two_le
  have : (N : ℤ) = p * t := hNt'
  have : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
  have hNle : (stufe Q : ℤ) ≤ t := by exact_mod_cast (this ▸ (by exact_mod_cast hle : (stufe Q : ℤ) ≤ (t.toNat : ℤ)))
  nlinarith

/-- **Converse (uniqueness in the book's sense):** a level at which the form is primitive is the Stufe. Argument:
`hN` states that the form is primitive at `N` (`IsPrimitiveThetaLevel`). No extra hypotheses. -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (N F⁻¹ primitive: converse)"]
theorem eq_stufe_of_isPrimitiveThetaLevel {Q : QuadForm ℤ n} {N : ℕ} (hN : IsPrimitiveThetaLevel Q N) :
    N = stufe Q := by
  obtain ⟨hlev, hprim⟩ := hN
  obtain ⟨k, hk⟩ := (isThetaLevel_iff_stufe_dvd Q N).mp hlev
  by_cases hk1 : k = 1
  · rw [hk, hk1, mul_one]
  · exfalso
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    obtain ⟨c, rfl⟩ := hpk
    refine hprim p hp fun y => ?_
    obtain ⟨m, hm⟩ := isThetaLevel_stufe Q y
    refine ⟨c * m, ?_⟩
    rw [hk]; push_cast
    rw [show ((stufe Q : ℝ) * ((p : ℝ) * c)) * quadAt (dualGram Q) y =
      p * (c * ((stufe Q : ℝ) * quadAt (dualGram Q) y)) by ring, hm]

/-- **Iff form:** the form is primitive at $N$ iff $N$ is the Stufe (hypotheses as in
`isPrimitiveThetaLevel_stufe`). -/
@[kb "cassels1978" "App. B, §5, (5.18), p. 385 (N F⁻¹ primitive iff N = Stufe)"]
theorem isPrimitiveThetaLevel_iff [NeZero n] (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (N : ℕ) :
    IsPrimitiveThetaLevel Q N ↔ N = stufe Q :=
  ⟨eq_stufe_of_isPrimitiveThetaLevel, fun h => h ▸ isPrimitiveThetaLevel_stufe Q hdet⟩

/-! ### The prime factors of the Stufe -/

/-- Helper: $d \mid N^n$ for a level $N$ (when $d = \det H \ne 0$), from $\det(H B) = N^n$ with $B = N H^{-1}$. -/
private lemma det_dvd_pow_of_level (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) {N : ℕ}
    (hN : IsThetaLevel Q N) : Q.hessian.det ∣ (N : ℤ) ^ n := by
  choose m hm using hN
  obtain ⟨B, hB⟩ := exists_intMatrix Q hdet (N : ℝ) m hm
  have hHB := hr_mul_B Q hdet _ B hB
  have hint : Q.hessian * B = (N : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
    apply Matrix.map_injective (Int.cast_injective (α := ℝ))
    show (Q.hessian * B).map (Int.cast : ℤ → ℝ) = _
    rw [hHB]; ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  have := congrArg Matrix.det hint
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  exact ⟨B.det, this.symm⟩

/-- **$N$ and $\det H$ have the same prime factors** (Cassels, App. B, §5, p. 385). For a prime $p$:
$p \mid \text{stufe}(Q) \iff p \mid \det H$, for every $Q$ with $\det H \ne 0$ (*generalization*: the book has $Q$
primitive positive definite in $n = 2k \ge 4$ variables). *Proof:* ($\Leftarrow$) $H\cdot(N H^{-1}) = N I$ with
$N H^{-1}$ integral gives $\det H \mid N^n$. ($\Rightarrow$) if $p \nmid \det H$ and $p \mid N$, then $N/p$ is still a
level: for odd $p$ because $p$ is invertible modulo $2\det H$; for $p = 2$ because $\det H$ is odd and then
$\vec y^{\mathsf T}\operatorname{adj}(H)\vec y$ is even (it equals $2\,Q(\operatorname{adj}(H)\vec y)/\det H$), contradicting
minimality of $N$. Arguments: `Q` the integral form, `p` a prime, `hdet` nonvanishing of $\det H$. -/
@[kb "cassels1978" "App. B, §5, p. 385 (N and det F have the same prime factors)"]
theorem prime_dvd_stufe_iff (Q : QuadForm ℤ n) (hdet : Q.hessian.det ≠ 0) (p : ℕ) (hp : p.Prime) :
    p ∣ stufe Q ↔ (p : ℤ) ∣ Q.hessian.det := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  constructor
  · rintro ⟨t, ht⟩
    by_contra hnd
    have hNpos := stufe_pos Q
    have hlev := (isThetaLevel_iff_dvd Q hdet _).mp (isThetaLevel_stufe Q)
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, mul_zero] at ht; omega
      · exact h0
    have hlev' : IsThetaLevel Q t := by
      rw [isThetaLevel_iff_dvd Q hdet]
      intro y
      have hy := hlev y
      rw [ht] at hy
      push_cast at hy
      by_cases hp2 : p = 2
      · subst hp2
        have hodd : ¬ (2 : ℤ) ∣ Q.hessian.det := by exact_mod_cast hnd
        have hev : (2 : ℤ) ∣ cf Q y := by
          have h := det_mul_cf_even Q y
          have : (2 : ℤ) ∣ Q.hessian.det * cf Q y := ⟨_, h⟩
          rcases Int.prime_two.dvd_mul.mp this with h1 | h1
          · exact absurd h1 hodd
          · exact h1
        have hcop : IsCoprime (2 : ℤ) Q.hessian.det :=
          (Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).mpr hodd
        have h1 : Q.hessian.det ∣ (t : ℤ) * cf Q y := by
          have : (2 : ℤ) * Q.hessian.det ∣ 2 * ((t : ℤ) * cf Q y) := by
            have e : (2 : ℤ) * ((t : ℤ) * cf Q y) = (2 * t) * cf Q y := by ring
            rw [e]; exact hy
          exact (mul_dvd_mul_iff_left (two_ne_zero)).mp this
        have h2 : (2 : ℤ) ∣ (t : ℤ) * cf Q y := dvd_mul_of_dvd_right hev _
        have := hcop.mul_dvd h2 h1
        exact this
      · have hnd2 : ¬ (p : ℤ) ∣ 2 * Q.hessian.det := by
          intro h
          rcases hpz.dvd_mul.mp h with h1 | h1
          · have : p ∣ 2 := by exact_mod_cast h1
            have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
            exact hp2 this
          · exact hnd h1
        have hcop : IsCoprime (2 * Q.hessian.det) (p : ℤ) :=
          ((Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr hnd2).symm
        refine hcop.dvd_of_dvd_mul_right ?_
        have e : ((p : ℤ) * t) * cf Q y = (t * cf Q y) * p := by ring
        rw [e] at hy
        exact hy
    have hle := stufe_le htpos hlev'
    have hp2 := hp.two_le
    rw [ht] at hle
    nlinarith
  · intro hpd
    have h1 := det_dvd_pow_of_level Q hdet (isThetaLevel_stufe Q)
    have h2 : (p : ℤ) ∣ (stufe Q : ℤ) ^ n := hpd.trans h1
    have h3 := hpz.dvd_of_dvd_pow h2
    exact_mod_cast h3

end

end QuadFormsKB.Siegel
