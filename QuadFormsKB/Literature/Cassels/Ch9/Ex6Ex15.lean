/-
# Cassels, Chapter 9, Examples 6 and 15

Source: J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 9, *Examples*, Ex. 6 (pp. 162--163) and
Ex. 15 (p. 165). Indices are 0-based: Cassels' variables $x, y, z$ are $x_0, x_1, x_2$ here.

**Example 6** (`ex6`). Cassels asks for a classically integral ternary form $g$ of determinant $5$ that is
$\mathbb Z_p$-equivalent to four given forms $f_2, f_3, f_5, f_7$ at $p = 2, 3, 5, 7$ respectively, where
$f_2 = 12x^2 - y^2 + 2xz + 3z^2$, $f_3 = -x^2 - y^2 - z^2$, $f_5 = 3x^2 - y^2 + 10z^2$,
$f_7 = 2x^2 - 2xy + 2y^2 + 4z^2$. A form is given by its symmetric (Gram) integer matrix, and
$\mathbb Z_p$-equivalence is the library's `Cassels.ZpEquiv` (matrices over $\mathbb Q_p$, change of variables in
$\mathrm{GL}_3(\mathbb Z_p)$). *Reconstructed:* the answer $g = x^2 + 2y^2 - 2yz + 3z^2$ (Gram matrix
$\operatorname{diag}(1) \oplus \begin{pmatrix} 2 & -1 \\ -1 & 3 \end{pmatrix}$, found by computer search; it is
positive definite). For $p = 2$ the equivalence is Lemma 5.1 (`dyadic_zpEquiv_of_int`: a substitution of odd determinant
and a congruence modulo $8$); for $p = 3, 7$ both forms are unimodular and the determinants differ by a unit square
(Lemma 5.2, `exists_equiv_of_congr_det`, with a square root from Hensel's lemma); for $p = 5$ a substitution of
determinant $2$ makes the forms congruent modulo $5 = 5^{v_5(\det f_5)}$ and Lemma 5.2 applies. Unconditional.

**Example 15** (positive definite rational ternary forms $f$; "proper integral automorph" = an integral matrix $T$
with $\det T = 1$ and $f(T\vec x) = f(\vec x)$, as in `Siegel.orderOf_mem_of_proper_automorph`, which is part (i)).
* (ii) `ex15_ii`: a proper integral automorph of order $3$ forces $f$ to be properly integrally equivalent to
  $l x^2 + m(y^2 + yz + z^2)$ or $l(3x + y - z)^2 + m(y^2 + yz + z^2)$ with rational $l, m > 0$, and $f$ then also has a
  proper integral automorph of order $2$.
* (iii) `ex15_iii`: if $f$ has a proper integral automorph other than the identity then $f$ is properly integrally
  equivalent to $a x^2 + b y^2 + c z^2 + l\,yz$ or $a x^2 + b y^2 + c z^2 + a\,xy + l\,yz$ (rational coefficients, here
  also $a, b, c > 0$).
* (iv) `ex15_iv_occur`: each of the orders $1, 2, 4, 6, 8, 12, 24$ occurs as the order of the group of proper
  integral automorphs (`RatAutPlus`), by certified enumerations of the automorph groups of seven integral forms.
  The other half of (iv), that no other order occurs, is stated as `Ex15ivOrders` and proved in `Ch9/Ex15Orders.lean`.

*Proof of (ii) and (iii)* (no eigenvalues): $\det(T - 1) = 0$, so $T$ fixes a primitive integral vector, which is
completed to a basis of $\mathbb Z^3$ (`exists_adapted`); then $T$ is conjugate to $\begin{pmatrix} 1 & \rho \\ 0 & A
\end{pmatrix}$ with $A \in M_2(\mathbb Z)$. For order $3$, $A^2 + A + 1 = 0$ and $A$ is conjugate in $\mathrm{GL}_2(\mathbb Z)$
to $\begin{pmatrix} 0 & -1 \\ 1 & -1 \end{pmatrix}$ by Euclidean descent in $\mathbb Z[\omega]$
(`exists_basis_order_three`); the row $\rho$ is reduced modulo the image of $1 - A$ (index $3$) to
$(j, 0)$, $j \in \{-1, 0, 1\}$, and solving $T^{\mathsf T}HT = H$ for the Gram matrix $H$ gives the normal forms.
For order $2$, $A = -1$ and $\rho$ is reduced modulo $2$ to $(0, 0)$ or $(1, 0)$. Since $\det(-U) = -\det U$ and
$f(-\vec x) = f(\vec x)$, integral equivalence and proper integral equivalence of ternary forms coincide
(`exists_det_one_of_gram`).

*Errata/updates:* none found. (In (iii) the printed statement is also valid with the positivity $a, b, c > 0$, which
is proved here.)
-/
import QuadFormsKB.Literature.Cassels.Ch8.CongruentDet
import QuadFormsKB.Literature.Cassels.Ch8.Dyadic
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal
import QuadFormsKB.Literature.Cassels.Ch9Examples4
import QuadFormsKB.Equiv.RationalGram
import QuadFormsKB.Siegel.KneserAut

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Matrix

namespace QuadFormsKB.Cassels.Ch9Ex6

section Ex6

variable {p : ℕ} [hp : Fact p.Prime]


/-- Helper: the entrywise cast $\mathbb Z \to \mathbb Q_p$ of an integer matrix `M` is the cast to $\mathbb Z_p$ followed by the inclusion $\mathbb Z_p \subset \mathbb Q_p$. -/
theorem intCast_map_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    M.map (Int.cast : ℤ → ℚ_[p]) = (M.map (Int.cast : ℤ → ℤ_[p])).map PadicInt.Coe.ringHom := by
  ext i j; simp

/-- Helper: an integer `k` not divisible by the prime `p` is a unit of $\mathbb Z_p$. -/
theorem isUnit_intCast {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : IsUnit ((k : ℤ) : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hk ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd k).1 hlt

/-- Helper: the determinant of the cast of an integer matrix `M` to $\mathbb Z_p$ is the cast of $\det M$. -/
theorem det_map_intCast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    (M.map (Int.cast : ℤ → ℤ_[p])).det = ((M.det : ℤ) : ℤ_[p]) := by
  have := RingHom.map_det (Int.castRingHom ℤ_[p]) M
  simpa using this.symm

/-- Helper: for integer matrices `P`, `T` with $p \nmid \det T$, `P` and $T^{\mathsf T}PT$ are $\mathbb Z_p$-equivalent (`hT`). -/
theorem zpEquiv_of_unit_det {n : ℕ} (P T : Matrix (Fin n) (Fin n) ℤ) (hT : ¬ (p : ℤ) ∣ T.det) :
    ZpEquiv (p := p) (P.map (Int.cast : ℤ → ℚ_[p])) ((Tᵀ * P * T).map (Int.cast : ℤ → ℚ_[p])) := by
  have hTu : IsUnit (T.map (Int.cast : ℤ → ℤ_[p])) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [det_map_intCast]; exact isUnit_intCast hT)
  refine ⟨hTu.unit, ?_⟩
  rw [intCast_map_eq, intCast_map_eq]
  have e : ∀ M : Matrix (Fin n) (Fin n) ℤ,
      (M.map (Int.cast : ℤ → ℤ_[p])).map PadicInt.Coe.ringHom = M.map (Int.castRingHom ℚ_[p]) := by
    intro M; ext i j; simp
  simp only [IsUnit.unit_spec, e]
  rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]

/-- Helper: for odd `p` (`hp2`) an integer `c` prime to `p` (`hc`) congruent to a square `s^2` modulo `p` (`hs`) is the square of a $p$-adic integer (Hensel's lemma). -/
theorem exists_unit_sq (hp2 : p ≠ 2) (c s : ℤ) (hc : ¬ (p : ℤ) ∣ c) (hs : (p : ℤ) ∣ c - s ^ 2) :
    ∃ w : ℤ_[p], w ^ 2 = ((c : ℤ) : ℤ_[p]) := by
  have hru : IsUnit ((c : ℤ) : ℤ_[p]) := isUnit_intCast hc
  have hsq : IsSquare (PadicInt.toZMod ((hru.unit : ℤ_[p]ˣ) : ℤ_[p])) := by
    refine ⟨(s : ZMod p), ?_⟩
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (c - s ^ 2) p).2 hs
    push_cast at h
    rw [IsUnit.unit_spec, map_intCast]
    exact sub_eq_zero.1 h |>.trans (by ring)
  obtain ⟨x, hx⟩ := (QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 hru.unit).2 hsq
  have hn1 : ‖(((c : ℤ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 hru
  rw [IsUnit.unit_spec] at hx
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_mul] at hn1
    nlinarith [norm_nonneg x]
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], (w : ℚ_[p]) = x := ⟨⟨x, hx1.le⟩, rfl⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  have h2 : ((w ^ 2 : ℤ_[p]) : ℚ_[p]) = x * x := by rw [PadicInt.coe_pow, hw, sq]
  exact h2.trans hx.symm

/-- Helper: if $p^{\delta + 1} \nmid k$ (`h`) for a nonzero integer `k` (`hk`), the $p$-adic valuation of `k` is at most `δ`. -/
theorem valuation_le_of_not_dvd (k : ℤ) (hk : k ≠ 0) (δ : ℕ) (h : ¬ (p : ℤ) ^ (δ + 1) ∣ k) :
    ((k : ℤ) : ℤ_[p]).valuation ≤ δ := by
  by_contra hlt
  push Not at hlt
  have hne : ((k : ℤ) : ℤ_[p]) ≠ 0 := by exact_mod_cast hk
  have := (PadicInt.mem_span_pow_iff_le_valuation _ hne (δ + 1)).2 hlt
  rw [← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_int_le_pow_iff_dvd] at this
  exact h this


/-- Helper: **$\mathbb Z_p$-equivalence from a congruence, $p$ odd.** Symmetric integer matrices `G`, `F` (`hG`, `hF`), $\det F \ne 0$ (`hF0`), a substitution `T` with $p \nmid \det T$ (`hT`) such that $T^{\mathsf T}GT \equiv F \pmod{p^\delta}$ (`hcong`) where $p^{\delta+1} \nmid \det F$ (`hδ`), and integers `a`, `b`, `s` prime to `p` with $\det(T^{\mathsf T}GT)\, b = \det F\, a$ and $ab \equiv s^2 \pmod p$ (the determinants differ by a unit square) give `ZpEquiv G F` (Lemma 5.2). -/
theorem zpEquiv_int_odd (hp2 : p ≠ 2) {n : ℕ} (G F T : Matrix (Fin n) (Fin n) ℤ) (hG : Gᵀ = G)
    (hF : Fᵀ = F) (hF0 : F.det ≠ 0) (hT : ¬ (p : ℤ) ∣ T.det) (δ : ℕ)
    (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ F.det)
    (hcong : ∀ i j, (p : ℤ) ^ δ ∣ (Tᵀ * G * T) i j - F i j) (a b : ℤ) (ha : ¬ (p : ℤ) ∣ a)
    (hb : ¬ (p : ℤ) ∣ b) (hab : (Tᵀ * G * T).det * b = F.det * a) (s : ℤ)
    (hs : (p : ℤ) ∣ a * b - s ^ 2) :
    ZpEquiv (p := p) (G.map (Int.cast : ℤ → ℚ_[p])) (F.map (Int.cast : ℤ → ℚ_[p])) := by
  have step1 := zpEquiv_of_unit_det (p := p) G T hT
  set G' := Tᵀ * G * T with hG'
  have hG's : G'ᵀ = G' := by
    simp only [hG', Matrix.transpose_mul, Matrix.transpose_transpose, hG, Matrix.mul_assoc]
  have hdetF : (F.map (Int.cast : ℤ → ℤ_[p])).det ≠ 0 := by
    rw [det_map_intCast]; exact_mod_cast hF0
  obtain ⟨w, hw⟩ := exists_unit_sq (p := p) hp2 (a * b) s (by
    intro h; rcases (Prime.dvd_mul (Nat.prime_iff_prime_int.1 hp.out)).1 h with h | h
    · exact ha h
    · exact hb h) hs
  obtain ⟨B, hB⟩ := isUnit_intCast (p := p) hb
  set binv : ℤ_[p] := ((B⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) with hbinv
  have hbb : (b : ℤ_[p]) * binv = 1 := by rw [← hB]; exact B.mul_inv
  have hwu : IsUnit w := by
    have hau : IsUnit ((a : ℤ) : ℤ_[p]) := isUnit_intCast ha
    have : IsUnit (w ^ 2) := by
      rw [hw]; push_cast
      exact hau.mul (isUnit_intCast hb)
    exact (isUnit_pow_iff (by norm_num)).1 this
  have hbunit : IsUnit ((b : ℤ) : ℤ_[p]) := isUnit_intCast hb
  have hu : IsUnit (w * binv) := hwu.mul (Units.isUnit _)
  have hu2 : (w * binv) ^ 2 * (b : ℤ_[p]) = (a : ℤ_[p]) := by
    push_cast at hw
    linear_combination ((binv ^ 2 * b : ℤ_[p])) * hw + (a : ℤ_[p]) * ((b : ℤ_[p]) * binv + 1) * hbb
  have hd : (G'.map (Int.cast : ℤ → ℤ_[p])).det = (F.map (Int.cast : ℤ → ℤ_[p])).det * (w * binv) ^ 2 := by
    rw [det_map_intCast, det_map_intCast]
    have h1 : ((G'.det : ℤ) : ℤ_[p]) * b = (F.det : ℤ_[p]) * a := by exact_mod_cast congrArg (fun z : ℤ => (z : ℤ_[p])) hab
    apply mul_right_cancel₀ hbunit.ne_zero
    rw [h1, mul_assoc, hu2]
  have hval : ((F.det : ℤ) : ℤ_[p]).valuation ≤ δ := valuation_le_of_not_dvd _ hF0 δ hδ
  obtain ⟨U, hU⟩ := exists_equiv_of_congr_det (p := p) hp2 (F.map (Int.cast : ℤ → ℤ_[p]))
    (G'.map (Int.cast : ℤ → ℤ_[p])) (by rw [← Matrix.transpose_map, hF]) (by rw [← Matrix.transpose_map, hG's])
    hdetF hu hd (fun i j => by
      have hz : (p : ℤ_[p]) ^ δ ∣ ((G' i j - F i j : ℤ) : ℤ_[p]) := by
        obtain ⟨c, hc⟩ := hcong i j
        refine ⟨c, ?_⟩
        have := congrArg (Int.cast : ℤ → ℤ_[p]) hc
        push_cast at this ⊢; exact this
      have h2 : (p : ℤ_[p]) ^ ((F.map (Int.cast : ℤ → ℤ_[p])).det.valuation) ∣
          (F.map (Int.cast : ℤ → ℤ_[p])) i j - (G'.map (Int.cast : ℤ → ℤ_[p])) i j := by
        rw [det_map_intCast]
        refine (pow_dvd_pow _ hval).trans ?_
        have := dvd_neg.2 hz
        simpa using this
      exact h2)
  have step2 : ZpEquiv (p := p) (F.map (Int.cast : ℤ → ℚ_[p])) (G'.map (Int.cast : ℤ → ℚ_[p])) := by
    refine ⟨U, ?_⟩
    rw [intCast_map_eq, intCast_map_eq, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  exact step1.trans step2.symm


/-- Helper: $5$ is prime (instance for $\mathbb Z_5$). -/
local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩
/-- Helper: $7$ is prime (instance for $\mathbb Z_7$). -/
local instance factPrimeSeven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- **The answer to Example 6:** the Gram matrix of $g = x^2 + 2y^2 - 2yz + 3z^2$ (variables $x_0, x_1, x_2$). -/
def gG : Matrix (Fin 3) (Fin 3) ℤ := !![1, 0, 0; 0, 2, -1; 0, -1, 3]
/-- The Gram matrix of $f_2 = 12x^2 - y^2 + 2xz + 3z^2$ (Example 6). -/
def f2 : Matrix (Fin 3) (Fin 3) ℤ := !![12, 0, 1; 0, -1, 0; 1, 0, 3]
/-- The Gram matrix of $f_3 = -x^2 - y^2 - z^2$ (Example 6). -/
def f3 : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, -1, 0; 0, 0, -1]
/-- The Gram matrix of $f_5 = 3x^2 - y^2 + 10z^2$ (Example 6). -/
def f5 : Matrix (Fin 3) (Fin 3) ℤ := !![3, 0, 0; 0, -1, 0; 0, 0, 10]
/-- The Gram matrix of $f_7 = 2x^2 - 2xy + 2y^2 + 4z^2$ (Example 6). -/
def f7 : Matrix (Fin 3) (Fin 3) ℤ := !![2, -1, 0; -1, 2, 0; 0, 0, 4]

/-- $\det$ `gG` $= 5$. -/
theorem det_gG : gG.det = 5 := by simp [gG, Matrix.det_fin_three]
/-- $\det$ `f2` $= -35$. -/
theorem det_f2 : f2.det = -35 := by simp [f2, Matrix.det_fin_three]
/-- $\det$ `f3` $= -1$. -/
theorem det_f3 : f3.det = -1 := by simp [f3, Matrix.det_fin_three]
/-- $\det$ `f5` $= -30$. -/
theorem det_f5 : f5.det = -30 := by simp [f5, Matrix.det_fin_three]
/-- $\det$ `f7` $= 12$. -/
theorem det_f7 : f7.det = 12 := by simp [f7, Matrix.det_fin_three]

/-- Helper: `gG` and `f2` are $\mathbb Z_2$-equivalent (substitution $T = \begin{pmatrix} 1&0&0\\0&1&0\\1&3&3\end{pmatrix}$ of odd determinant, $T^{\mathsf T}\,\text{gG}\,T \equiv \text{f2} \pmod 8$). -/
theorem ex6_two : ZpEquiv (p := 2) (gG.map (Int.cast : ℤ → ℚ_[2])) (f2.map (Int.cast : ℤ → ℚ_[2])) :=
  dyadic_zpEquiv_of_int gG f2 !![1, 0, 0; 0, 1, 0; 1, 3, 3] (by decide) (by decide)
    (by rw [det_gG]; decide) (by simp [Matrix.det_fin_three]; decide) (by
      intro i j; fin_cases i <;> fin_cases j <;> decide)

/-- Helper: `gG` and `f3` are $\mathbb Z_3$-equivalent (both unimodular, determinants $5$ and $-1$ differ by the unit square $-5 \equiv 1$). -/
theorem ex6_three : ZpEquiv (p := 3) (gG.map (Int.cast : ℤ → ℚ_[3])) (f3.map (Int.cast : ℤ → ℚ_[3])) := by
  refine zpEquiv_int_odd (by norm_num) gG f3 1 (by decide) (by decide) (by rw [det_f3]; norm_num)
    (by simp) 0 (by rw [det_f3]; norm_num) (by simp) (-5) 1 (by norm_num) (by norm_num)
    (by simp [det_gG, det_f3]) 1 (by norm_num)

/-- Helper: `gG` and `f5` are $\mathbb Z_5$-equivalent (substitution of determinant $2$, then congruence modulo $5$). -/
theorem ex6_five : ZpEquiv (p := 5) (gG.map (Int.cast : ℤ → ℚ_[5])) (f5.map (Int.cast : ℤ → ℚ_[5])) := by
  refine zpEquiv_int_odd (by norm_num) gG f5 !![0, 2, 0; 0, 0, 1; 1, 0, 2] (by decide) (by decide)
    (by rw [det_f5]; norm_num) (by simp [Matrix.det_fin_three]) 1 (by rw [det_f5]; norm_num) ?_ (-2) 3
    (by norm_num) (by norm_num) ?_ 2 (by norm_num)
  · intro i j; fin_cases i <;> fin_cases j <;> decide
  · rw [det_f5]; simp [Matrix.det_fin_three, gG]

/-- Helper: `gG` and `f7` are $\mathbb Z_7$-equivalent (both unimodular, $5/12 \equiv 1 \pmod 7$ is a square). -/
theorem ex6_seven : ZpEquiv (p := 7) (gG.map (Int.cast : ℤ → ℚ_[7])) (f7.map (Int.cast : ℤ → ℚ_[7])) := by
  refine zpEquiv_int_odd (by norm_num) gG f7 1 (by decide) (by decide) (by rw [det_f7]; norm_num)
    (by simp) 0 (by rw [det_f7]; norm_num) (by simp) 5 12 (by norm_num) (by norm_num)
    (by simp [det_gG, det_f7]) 2 (by norm_num)


/-- The Gram matrix `f2` represents $f_2 = 12x^2 - y^2 + 2xz + 3z^2$: $\vec x^{\mathsf T}(\text{f2})\vec x = f_2(\vec x)$. -/
theorem quad_f2 (x : Fin 3 → ℤ) :
    x ⬝ᵥ (f2 *ᵥ x) = 12 * x 0 ^ 2 - x 1 ^ 2 + 2 * x 0 * x 2 + 3 * x 2 ^ 2 := by
  simp [f2, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring

/-- The Gram matrix `f3` represents $f_3 = -x^2 - y^2 - z^2$. -/
theorem quad_f3 (x : Fin 3 → ℤ) : x ⬝ᵥ (f3 *ᵥ x) = -x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2 := by
  simp [f3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring

/-- The Gram matrix `f5` represents $f_5 = 3x^2 - y^2 + 10z^2$. -/
theorem quad_f5 (x : Fin 3 → ℤ) : x ⬝ᵥ (f5 *ᵥ x) = 3 * x 0 ^ 2 - x 1 ^ 2 + 10 * x 2 ^ 2 := by
  simp [f5, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring

/-- The Gram matrix `f7` represents $f_7 = 2x^2 - 2xy + 2y^2 + 4z^2$. -/
theorem quad_f7 (x : Fin 3 → ℤ) :
    x ⬝ᵥ (f7 *ᵥ x) = 2 * x 0 ^ 2 - 2 * x 0 * x 1 + 2 * x 1 ^ 2 + 4 * x 2 ^ 2 := by
  simp [f7, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring

/-- The Gram matrix `gG` represents $g = x^2 + 2y^2 - 2yz + 3z^2$ (positive definite, classically integral, with
$\det = 5$ by `det_gG`). -/
theorem quad_gG (x : Fin 3 → ℤ) : x ⬝ᵥ (gG *ᵥ x) = x 0 ^ 2 + 2 * x 1 ^ 2 - 2 * x 1 * x 2 + 3 * x 2 ^ 2 := by
  simp [gG, dotProduct, Matrix.mulVec, Fin.sum_univ_three]; ring

/-- **Cassels, Ch. 9, Example 6** (pp. 162--163). There is a classically integral ternary form
$g(\vec x) = \vec x^{\mathsf T} A\vec x$ ($A$ a symmetric integer $3 \times 3$ matrix, the Gram matrix; here
$g = x^2 + 2y^2 - 2yz + 3z^2$ with $A = $ `gG`) of determinant $\det A = 5$ which is $\mathbb Z_p$-equivalent to $f_p$
for $p = 2, 3, 5, 7$, where $f_2, f_3, f_5, f_7$ are given by the Gram matrices `f2`, `f3`, `f5`, `f7` (see
`quad_f2`, `quad_f3`, `quad_f5`, `quad_f7` for the polynomials). `ZpEquiv F G` means $G = T^{\mathsf T}FT$ for some
$T \in \mathrm{GL}_3(\mathbb Z_p)$, for matrices over $\mathbb Q_p$ (the integer matrices are mapped into $\mathbb Q_p$).
Unconditional. -/
@[kb "cassels1978" "Ch. 9, Ex. 6, pp. 162-163"]
theorem ex6 : ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.IsSymm ∧ A.det = 5 ∧
    ZpEquiv (p := 2) (A.map (Int.cast : ℤ → ℚ_[2])) (f2.map (Int.cast : ℤ → ℚ_[2])) ∧
    ZpEquiv (p := 3) (A.map (Int.cast : ℤ → ℚ_[3])) (f3.map (Int.cast : ℤ → ℚ_[3])) ∧
    ZpEquiv (p := 5) (A.map (Int.cast : ℤ → ℚ_[5])) (f5.map (Int.cast : ℤ → ℚ_[5])) ∧
    ZpEquiv (p := 7) (A.map (Int.cast : ℤ → ℚ_[7])) (f7.map (Int.cast : ℤ → ℚ_[7])) := by
  refine ⟨gG, ?_, det_gG, ex6_two, ex6_three, ex6_five, ex6_seven⟩
  unfold Matrix.IsSymm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gG]

end Ex6

section Ex15

open QuadFormsKB QuadFormsKB.Siegel


/-- Integer matrix mapped to $\mathbb Q$. -/
abbrev toQ (M : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℚ := M.map (Int.castRingHom ℚ)

/-- Helper: `toQ` is multiplicative. -/
theorem toQ_mul (M N : Matrix (Fin 3) (Fin 3) ℤ) : toQ (M * N) = toQ M * toQ N := by
  exact Matrix.map_mul

/-- Helper: `toQ` commutes with transposition. -/
theorem toQ_transpose (M : Matrix (Fin 3) (Fin 3) ℤ) : toQ Mᵀ = (toQ M)ᵀ := by
  simp [toQ, Matrix.transpose_map]

/-- Helper: `toQ` of the identity is the identity. -/
theorem toQ_one : toQ (1 : Matrix (Fin 3) (Fin 3) ℤ) = 1 := by
  simp [toQ]

/-- Helper: **polarization.** Symmetric rational matrices `A`, `B` (`hA`, `hB`) with $\vec x^{\mathsf T}A\vec x = \vec x^{\mathsf T}B\vec x$ for all `x` (`h`) are equal. -/
theorem eq_of_forall_dotProduct {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ x : Fin n → ℚ, x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x)) : A = B := by
  have hd : ∀ i, A i i = B i i := fun i => by
    have := h (Pi.single i 1)
    simpa [Matrix.mulVec_single_one, dotProduct_single] using this
  ext i j
  by_cases hij : i = j
  · subst hij; exact hd i
  · have := h (Pi.single i 1 + Pi.single j 1)
    have hAs : A j i = A i j := by simpa using congrFun (congrFun hA i) j
    have hBs : B j i = B i j := by simpa using congrFun (congrFun hB i) j
    simp [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hAs, hBs, hd] at this
    linarith


/-- The determinant identity $\det(T - 1) = \det T - \operatorname{tr}\operatorname{adj} T + \operatorname{tr} T - 1$
for $3 \times 3$ integer matrices. -/
theorem det_sub_one (T : Matrix (Fin 3) (Fin 3) ℤ) :
    (T - 1).det = T.det - (adjugate T).trace + T.trace - 1 := by
  rw [Matrix.eta_fin_three T]
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three]
  ring

/-- Helper: if $\det(T - 1) = 0$ (`h`) then `T` fixes a primitive integer vector `e` (coordinates with gcd $1$). -/
theorem exists_primitive_fixed (T : Matrix (Fin 3) (Fin 3) ℤ) (h : (T - 1).det = 0) :
    ∃ e : Fin 3 → ℤ, T *ᵥ e = e ∧ Int.gcd (Int.gcd (e 0) (e 1)) (e 2) = 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set g12 : ℕ := Int.gcd (v 0) (v 1) with hg12
  set g : ℕ := Int.gcd (g12 : ℤ) (v 2) with hg
  have hd2 : (g : ℤ) ∣ v 2 := Int.gcd_dvd_right _ _
  have hd01 : (g : ℤ) ∣ (g12 : ℤ) := Int.gcd_dvd_left _ _
  have hd0 : (g : ℤ) ∣ v 0 := hd01.trans (Int.gcd_dvd_left _ _)
  have hd1 : (g : ℤ) ∣ v 1 := hd01.trans (Int.gcd_dvd_right _ _)
  have hg0 : g ≠ 0 := by
    intro h0
    rw [hg, Int.gcd_eq_zero_iff] at h0
    have h12 : g12 = 0 := by exact_mod_cast h0.1
    rw [hg12, Int.gcd_eq_zero_iff] at h12
    apply hv0
    funext i
    fin_cases i <;> simp [h12.1, h12.2, h0.2]
  obtain ⟨e0, he0⟩ := hd0
  obtain ⟨e1, he1⟩ := hd1
  obtain ⟨e2, he2⟩ := hd2
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0
  set e : Fin 3 → ℤ := ![e0, e1, e2] with he
  have hve : v = (g : ℤ) • e := by
    funext i
    fin_cases i <;> simp [e, he0, he1, he2]
  refine ⟨e, ?_, ?_⟩
  · have h1 : (g : ℤ) • ((T - 1) *ᵥ e) = 0 := by rw [← Matrix.mulVec_smul, ← hve]; exact hv
    have h2 : (T - 1) *ᵥ e = 0 := (smul_eq_zero.1 h1).resolve_left hgz
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h2
    exact sub_eq_zero.1 h2
  · have h3 : g12 = g * Int.gcd e0 e1 := by
      rw [hg12, he0, he1, Int.gcd_mul_left, Int.natAbs_natCast]
    have h4 : g = g * Int.gcd (Int.gcd e0 e1) e2 := by
      conv_lhs => rw [hg, h3, he2]
      push_cast
      rw [Int.gcd_mul_left, Int.natAbs_natCast]
    have h5 : g * 1 = g * Int.gcd (Int.gcd e0 e1) e2 := by rw [mul_one]; exact h4
    exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) h5).symm


/-- Helper: a primitive integer vector is the first column of a unimodular matrix. -/
theorem exists_unimodular_col (e : Fin 3 → ℤ) (h : Int.gcd (Int.gcd (e 0) (e 1)) (e 2) = 1) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℤ, (U.det = 1 ∨ U.det = -1) ∧ ∀ i, U i 0 = e i := by
  by_cases hg : Int.gcd (e 0) (e 1) = 0
  · have h0 : e 0 = 0 := (Int.gcd_eq_zero_iff.1 hg).1
    have h1 : e 1 = 0 := (Int.gcd_eq_zero_iff.1 hg).2
    rw [hg] at h
    have h2 : (e 2).natAbs = 1 := by simpa using h
    refine ⟨!![0, 1, 0; 0, 0, 1; e 2, 0, 0], ?_, ?_⟩
    · rcases Int.natAbs_eq_iff.1 h2 with h3 | h3
      · left; simp [Matrix.det_fin_three, h3]
      · right; simp [Matrix.det_fin_three, h3]
    · intro i; fin_cases i <;> simp [h0, h1]
  · set g : ℕ := Int.gcd (e 0) (e 1) with hgdef
    obtain ⟨a', ha'⟩ : (g : ℤ) ∣ e 0 := Int.gcd_dvd_left _ _
    obtain ⟨b', hb'⟩ : (g : ℤ) ∣ e 1 := Int.gcd_dvd_right _ _
    have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg
    have hxy := Int.gcd_eq_gcd_ab (e 0) (e 1)
    set x := Int.gcdA (e 0) (e 1) with hx
    set y := Int.gcdB (e 0) (e 1) with hy
    have hxy' : a' * x + b' * y = 1 := by
      apply mul_left_cancel₀ hgz
      calc (g : ℤ) * (a' * x + b' * y) = (g * a') * x + (g * b') * y := by ring
        _ = e 0 * x + e 1 * y := by rw [← ha', ← hb']
        _ = g * 1 := by rw [mul_one]; exact hxy.symm
    have hst := Int.gcd_eq_gcd_ab (g : ℤ) (e 2)
    set s := Int.gcdA (g : ℤ) (e 2) with hs
    set t := Int.gcdB (g : ℤ) (e 2) with ht
    have hst' : (g : ℤ) * s + e 2 * t = 1 := by rw [← hst, h]; simp
    refine ⟨!![a', -y, 0; b', x, 0; 0, 0, 1] * !![(g : ℤ), 0, -t; 0, 1, 0; e 2, 0, s], ?_, ?_⟩
    · left
      rw [Matrix.det_mul]
      have d1 : (!![a', -y, 0; b', x, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
        simp [Matrix.det_fin_three]; linear_combination hxy'
      have d2 : (!![(g : ℤ), 0, -t; 0, 1, 0; e 2, 0, s] : Matrix (Fin 3) (Fin 3) ℤ).det = 1 := by
        simp [Matrix.det_fin_three]; linear_combination hst'
      rw [d1, d2]; norm_num
    · intro i
      fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha', hb'] <;> ring

/-- Helper: **adapted basis.** If $\det(T - 1) = 0$ for an integer $3 \times 3$ matrix $T$, there are
$Q \in \mathrm{GL}_3(\mathbb Z)$ and integers with $TQ = Q \begin{pmatrix} 1 & r & s \\ 0 & \alpha & \beta \\
0 & \gamma & \delta \end{pmatrix}$ (the first column of $Q$ is a primitive vector fixed by $T$). -/
theorem exists_adapted (T : Matrix (Fin 3) (Fin 3) ℤ) (h : (T - 1).det = 0) :
    ∃ (Q : GL (Fin 3) ℤ) (r s α β γ δ : ℤ),
      T * Q.val = Q.val * !![1, r, s; 0, α, β; 0, γ, δ] := by
  obtain ⟨e, he, hprim⟩ := exists_primitive_fixed T h
  obtain ⟨U, hU, hUe⟩ := exists_unimodular_col e hprim
  have hunit : IsUnit U.det := by rcases hU with h | h <;> simp [h]
  have hUu : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).2 hunit
  set Q : GL (Fin 3) ℤ := hUu.unit with hQ
  have hQval : Q.val = U := rfl
  set T' : Matrix (Fin 3) (Fin 3) ℤ := (Q⁻¹).val * T * Q.val with hT'
  have hTQ : T * Q.val = Q.val * T' := by
    rw [hT', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcol : T' *ᵥ (Pi.single 0 1) = Pi.single 0 1 := by
    have h1 : Q.val *ᵥ (Pi.single 0 1) = e := by
      rw [Matrix.mulVec_single_one]; funext i; simp [hQval, hUe]
    rw [hT', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, he, ← h1, Matrix.mulVec_mulVec,
      Units.inv_mul, Matrix.one_mulVec]
  have h0 : ∀ i, T' i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun hcol i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  refine ⟨Q, T' 0 1, T' 0 2, T' 1 1, T' 1 2, T' 2 1, T' 2 2, ?_⟩
  rw [hTQ]
  congr 1
  rw [Matrix.eta_fin_three T']
  simp [h0]

/-! ### The binary part: a matrix of order three is conjugate to a standard one -/

/-- Helper: the integral binary form $\varphi(u) = \det(u, Au)$ attached to
$A = \begin{pmatrix} \alpha & \beta \\ \gamma & \delta \end{pmatrix}$ and $u = (u_0, u_1)$. -/
def phi (α β γ δ u0 u1 : ℤ) : ℤ := u0 * (γ * u0 + δ * u1) - u1 * (α * u0 + β * u1)

/-- Helper: for $\operatorname{tr} A = -1$ (`h1`), $\det A = 1$ (`h2`), `phi` does not vanish at a nonzero vector (`hu`) (the form is definite of discriminant $-3$). -/
theorem phi_ne_zero {α β γ δ : ℤ} (h1 : α + δ = -1) (h2 : α * δ - β * γ = 1) {u0 u1 : ℤ}
    (hu : u0 ≠ 0 ∨ u1 ≠ 0) : phi α β γ δ u0 u1 ≠ 0 := by
  have hdisc : (δ - α) ^ 2 + 4 * β * γ = -3 := by nlinarith
  have hγ : γ ≠ 0 := by
    intro h0
    rw [h0] at hdisc
    nlinarith [sq_nonneg (δ - α)]
  intro h0
  have hid : 4 * γ * phi α β γ δ u0 u1 = (2 * γ * u0 + (δ - α) * u1) ^ 2 + 3 * u1 ^ 2 := by
    unfold phi; linear_combination (-(u1 ^ 2)) * hdisc
  rw [h0, mul_zero] at hid
  have hu1 : u1 = 0 := by nlinarith [sq_nonneg (2 * γ * u0 + (δ - α) * u1), sq_nonneg u1]
  have hu0 : u0 = 0 := by
    have : 2 * γ * u0 = 0 := by
      rw [hu1] at hid
      nlinarith [sq_nonneg (2 * γ * u0)]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by simpa using h) hγ
    · exact h
  rcases hu with h | h
  · exact h hu0
  · exact h hu1

/-- Helper: **a matrix of order three in $M_2(\mathbb Z)$ is conjugate to $\begin{pmatrix} 0 & -1 \\ 1 & -1
\end{pmatrix}$ over $\mathrm{GL}_2(\mathbb Z)$.** The hypotheses `h1`, `h2` say $\operatorname{tr} A = -1$ and
$\det A = 1$ (so $A^2 + A + 1 = 0$). The proof is Euclidean descent: choose $u \ne 0$ minimizing $|\det(u, Au)|$; every
integer vector is an integer combination of $u$ and $Au$ because $\mathbb Z[\omega]$ is Euclidean (rounding in the
norm $\xi^2 - \xi\eta + \eta^2 \le 3/4$). -/
theorem exists_basis_order_three (α β γ δ : ℤ) (h1 : α + δ = -1) (h2 : α * δ - β * γ = 1) :
    ∃ P : GL (Fin 2) ℤ, !![α, β; γ, δ] * P.val = P.val * !![0, -1; 1, -1] := by
  classical
  have hex : ∃ n, ∃ u0 u1 : ℤ, (u0 ≠ 0 ∨ u1 ≠ 0) ∧ (phi α β γ δ u0 u1).natAbs = n :=
    ⟨_, 1, 0, Or.inl one_ne_zero, rfl⟩
  obtain ⟨u0, u1, hu, hm⟩ := Nat.find_spec hex
  have hmin : ∀ w0 w1 : ℤ, (w0 ≠ 0 ∨ w1 ≠ 0) → Nat.find hex ≤ (phi α β γ δ w0 w1).natAbs :=
    fun w0 w1 hw => Nat.find_min' hex ⟨w0, w1, hw, rfl⟩
  set v0 : ℤ := α * u0 + β * u1 with hv0
  set v1 : ℤ := γ * u0 + δ * u1 with hv1
  set D : ℤ := u0 * v1 - u1 * v0 with hD
  have hDphi : D = phi α β γ δ u0 u1 := rfl
  have hD0 : D ≠ 0 := phi_ne_zero h1 h2 hu
  have hA0 : α * v0 + β * v1 = -u0 - v0 := by
    rw [hv0, hv1]; linear_combination (u0 * α + u1 * β) * h1 - u0 * h2
  have hA1 : γ * v0 + δ * v1 = -u1 - v1 := by
    rw [hv0, hv1]; linear_combination (γ * u0 + δ * u1) * h1 - u1 * h2
  have hspan : ∀ w0 w1 : ℤ, ∃ a b : ℤ, w0 = a * u0 + b * v0 ∧ w1 = a * u1 + b * v1 := by
    intro w0 w1
    have hDq0 : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
    set x : ℚ := ((w0 * v1 - w1 * v0 : ℤ) : ℚ) / (D : ℚ) with hx
    set y : ℚ := ((u0 * w1 - u1 * w0 : ℤ) : ℚ) / (D : ℚ) with hy
    have hDc : (D : ℚ) = (u0 : ℚ) * v1 - u1 * v0 := by rw [hD]; push_cast; ring
    have hx0 : (w0 : ℚ) = x * u0 + y * v0 := by
      rw [hx, hy]; field_simp; push_cast; rw [hDc]; ring
    have hx1 : (w1 : ℚ) = x * u1 + y * v1 := by
      rw [hx, hy]; field_simp; push_cast; rw [hDc]; ring
    clear_value x y
    refine ⟨round x, round y, ?_⟩
    by_contra hne
    set a : ℤ := round x with ha
    set b : ℤ := round y with hb
    set w0' : ℤ := w0 - a * u0 - b * v0 with hw0'
    set w1' : ℤ := w1 - a * u1 - b * v1 with hw1'
    have hne' : w0' ≠ 0 ∨ w1' ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne ⟨by omega, by omega⟩
    have hξ : |x - a| ≤ 1 / 2 := abs_sub_round x
    have hη : |y - b| ≤ 1 / 2 := abs_sub_round y
    have e0 : (w0' : ℚ) = (x - a) * u0 + (y - b) * v0 := by
      rw [hw0']; push_cast; rw [hx0]; ring
    have e1 : (w1' : ℚ) = (x - a) * u1 + (y - b) * v1 := by
      rw [hw1']; push_cast; rw [hx1]; ring
    have hA0q : (α : ℚ) * v0 + β * v1 = -u0 - v0 := by exact_mod_cast hA0
    have hA1q : (γ : ℚ) * v0 + δ * v1 = -u1 - v1 := by exact_mod_cast hA1
    have hphi : ((phi α β γ δ w0' w1' : ℤ) : ℚ) =
        ((x - a) ^ 2 - (x - a) * (y - b) + (y - b) ^ 2) * D := by
      unfold phi
      push_cast
      rw [e0, e1, hDc]
      have hv0q : (v0 : ℚ) = α * u0 + β * u1 := by exact_mod_cast hv0
      have hv1q : (v1 : ℚ) = γ * u0 + δ * u1 := by exact_mod_cast hv1
      linear_combination (-(((x - a) * u0 + (y - b) * v0) * (x - a))) * hv1q
        + (((x - a) * u0 + (y - b) * v0) * (y - b)) * hA1q
        + (((x - a) * u1 + (y - b) * v1) * (x - a)) * hv0q
        - (((x - a) * u1 + (y - b) * v1) * (y - b)) * hA0q
    have hN0 : 0 ≤ (x - a) ^ 2 - (x - a) * (y - b) + (y - b) ^ 2 := by
      nlinarith [sq_nonneg ((x - a) - (y - b) / 2), sq_nonneg (y - b)]
    have hN1 : (x - a) ^ 2 - (x - a) * (y - b) + (y - b) ^ 2 ≤ 3 / 4 := by
      obtain ⟨h3, h4⟩ := abs_le.1 hξ
      obtain ⟨h5, h6⟩ := abs_le.1 hη
      nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h6), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h5),
        mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h6), mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 h5)]
    have hlt : |((phi α β γ δ w0' w1' : ℤ) : ℚ)| < |(D : ℚ)| := by
      rw [hphi, abs_mul, abs_of_nonneg hN0]
      have hpos : 0 < |(D : ℚ)| := abs_pos.2 hDq0
      nlinarith
    have hlt' : |phi α β γ δ w0' w1'| < |D| := by exact_mod_cast hlt
    have h6 := hmin w0' w1' hne'
    rw [← hm] at h6
    have h7 : ((phi α β γ δ w0' w1').natAbs : ℤ) < (D.natAbs : ℤ) := by
      rw [← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs]; exact hlt'
    have h8 : D.natAbs ≤ (phi α β γ δ w0' w1').natAbs := h6
    omega
  obtain ⟨a, b, ha0, ha1⟩ := hspan 1 0
  obtain ⟨c, d, hc0, hc1⟩ := hspan 0 1
  have hPdet : IsUnit D := by
    have hprod : D * (a * d - b * c) = 1 := by
      have : (!![u0, v0; u1, v1] * !![a, c; b, d] : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith
      have h' := congrArg Matrix.det this
      simp [Matrix.det_fin_two] at h'
      rw [hD]; linear_combination h'
    exact isUnit_iff_exists_inv.2 ⟨_, hprod⟩
  have hPu : IsUnit (!![u0, v0; u1, v1] : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : (!![u0, v0; u1, v1] : Matrix (Fin 2) (Fin 2) ℤ).det = D := by
      simp [Matrix.det_fin_two, hD]; ring
    rw [this]; exact hPdet
  refine ⟨hPu.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hv0, hv1] <;> linarith

/-! ### Elements of order three -/

/-- Helper: an integer $3 \times 3$ matrix $T \ne 1$ with $T^3 = 1$ and $\det T = 1$ has $\operatorname{tr} T = 0$ and
$\operatorname{tr}\operatorname{adj} T = 0$ (the characteristic polynomial is $\lambda^3 - 1$). -/
theorem order_three_trace (T : Matrix (Fin 3) (Fin 3) ℤ) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) : T.trace = 0 ∧ (adjugate T).trace = 0 := by
  have hc := cayley3 T
  rw [hT3, hdet, one_smul] at hc
  set s := T.trace with hs
  set s' := (adjugate T).trace with hs'
  have h1 : s' • T = s • T ^ 2 := by
    have : s' • T - s • T ^ 2 = 0 := by rw [← hc]; abel
    exact sub_eq_zero.1 this
  have h2 : s' • (1 : Matrix (Fin 3) (Fin 3) ℤ) = s • T := by
    have e1 : (s' • T) * T ^ 2 = s' • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
      rw [smul_mul_assoc, ← pow_succ', hT3]
    have e2 : (s • T ^ 2) * T ^ 2 = s • T := by
      rw [smul_mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [← e1, h1, e2]
  have hs0 : s = 0 := by
    by_contra hne
    have hoff : ∀ i j, i ≠ j → T i j = 0 := by
      intro i j hij
      have := congrFun (congrFun h2 i) j
      simp [Matrix.one_apply, hij] at this
      rcases this with h | h
      · exact absurd h hne
      · exact h
    have hdiag : ∀ i, T i i = T 0 0 := by
      intro i
      have h3 := congrFun (congrFun h2 i) i
      have h4 := congrFun (congrFun h2 0) 0
      simp at h3 h4
      apply mul_left_cancel₀ hne
      rw [← h3, ← h4]
    have hTc : T = (T 0 0) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hdiag i]
      · simp [hoff i j hij, Matrix.one_apply, hij]
    have hc3 : (T 0 0) ^ 3 = 1 := by
      have := congrFun (congrFun hT3 0) 0
      rw [hTc, smul_pow, one_pow] at this
      simpa using this
    have hc1 : T 0 0 = 1 := by
      have h5 : (T 0 0 - 1) * ((T 0 0) ^ 2 + T 0 0 + 1) = 0 := by linear_combination hc3
      rcases mul_eq_zero.1 h5 with h | h
      · linarith
      · nlinarith [sq_nonneg (2 * T 0 0 + 1)]
    apply hT1
    rw [hTc, hc1, one_smul]
  refine ⟨hs0, ?_⟩
  have := congrFun (congrFun h2 0) 0
  rw [hs0] at this
  simpa using this

/-- Helper: a matrix with unit determinant as an element of $\mathrm{GL}_3(\mathbb Z)$. -/
noncomputable def glOf (M : Matrix (Fin 3) (Fin 3) ℤ) (h : IsUnit M.det) : GL (Fin 3) ℤ :=
  ((Matrix.isUnit_iff_isUnit_det M).2 h).unit

/-- Helper: the underlying matrix of `glOf M h` is `M`. -/
theorem glOf_val (M : Matrix (Fin 3) (Fin 3) ℤ) (h : IsUnit M.det) : (glOf M h).val = M := rfl

/-- Helper: **shape of an element of order three.** If $T \in M_3(\mathbb Z)$, $T^3 = 1$, $T \ne 1$, $\det T = 1$, there
are $Q \in \mathrm{GL}_3(\mathbb Z)$ and $j \in \{-1, 0, 1\}$ with
$TQ = Q \begin{pmatrix} 1 & j & 0 \\ 0 & 0 & -1 \\ 0 & 1 & -1 \end{pmatrix}$. -/
theorem order_three_shape (T : Matrix (Fin 3) (Fin 3) ℤ) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) :
    ∃ (Q : GL (Fin 3) ℤ) (j : ℤ), (j = 0 ∨ j = 1 ∨ j = -1) ∧
      T * Q.val = Q.val * !![1, j, 0; 0, 0, -1; 0, 1, -1] := by
  obtain ⟨htr, htra⟩ := order_three_trace T hT3 hT1 hdet
  have hdet1 : (T - 1).det = 0 := by rw [det_sub_one, hdet, htr, htra]; norm_num
  obtain ⟨Q1, r, s, α, β, γ, δ, hQ1⟩ := exists_adapted T hdet1
  have hconj : (Q1⁻¹).val * T * Q1.val = !![1, r, s; 0, α, β; 0, γ, δ] := by
    rw [Matrix.mul_assoc, hQ1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have htr1 := Matrix.trace_units_conj' Q1 T
  have hdet1' := Matrix.det_units_conj' Q1 T
  rw [hconj] at htr1 hdet1'
  have h1 : α + δ = -1 := by
    simp [Matrix.trace_fin_three, htr] at htr1; linarith
  have h2 : α * δ - β * γ = 1 := by
    rw [hdet] at hdet1'
    simp [Matrix.det_fin_three] at hdet1'; linarith
  obtain ⟨P, hP⟩ := exists_basis_order_three α β γ δ h1 h2
  have hPd : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  rw [Matrix.eta_fin_two P.val] at hP hPd
  set p00 := P.val 0 0 with hp00
  set p01 := P.val 0 1 with hp01
  set p10 := P.val 1 0 with hp10
  set p11 := P.val 1 1 with hp11
  have e00 : α * p00 + β * p10 = p01 := by
    have := congrFun (congrFun hP 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : α * p01 + β * p11 = -p00 - p01 := by
    have := congrFun (congrFun hP 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using this
  have e10 : γ * p00 + δ * p10 = p11 := by
    have := congrFun (congrFun hP 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : γ * p01 + δ * p11 = -p10 - p11 := by
    have := congrFun (congrFun hP 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg] using this
  have hQ2d : IsUnit (!![1, 0, 0; 0, p00, p01; 0, p10, p11] : Matrix (Fin 3) (Fin 3) ℤ).det := by
    simpa [Matrix.det_fin_three, Matrix.det_fin_two] using hPd
  set Q2 := glOf _ hQ2d with hQ2
  set r2 : ℤ := r * p00 + s * p10 with hr2
  set s2 : ℤ := r * p01 + s * p11 with hs2
  have hT12 : !![1, r, s; 0, α, β; 0, γ, δ] * Q2.val = Q2.val * !![1, r2, s2; 0, 0, -1; 0, 1, -1] := by
    rw [hQ2, glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hr2, hs2] <;> linarith
  obtain ⟨l, hl⟩ : ∃ l : ℤ, r2 - s2 - 3 * l = 0 ∨ r2 - s2 - 3 * l = 1 ∨ r2 - s2 - 3 * l = -1 :=
    ⟨(r2 - s2 + 1) / 3, by omega⟩
  set k : ℤ := -s2 - 2 * l with hk
  have hWd : IsUnit (!![1, k, l; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
    simp [Matrix.det_fin_three]
  set W := glOf _ hWd with hW
  have hT2W : !![1, r2, s2; 0, 0, -1; 0, 1, -1] * W.val
      = W.val * !![1, r2 - s2 - 3 * l, 0; 0, 0, -1; 0, 1, -1] := by
    rw [hW, glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hk] <;> ring
  refine ⟨Q1 * Q2 * W, r2 - s2 - 3 * l, hl, ?_⟩
  rw [Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  calc T * Q1.val * Q2.val * W.val
      = (Q1.val * !![1, r, s; 0, α, β; 0, γ, δ]) * Q2.val * W.val := by rw [hQ1]
    _ = Q1.val * (!![1, r, s; 0, α, β; 0, γ, δ] * Q2.val) * W.val := by simp only [Matrix.mul_assoc]
    _ = Q1.val * (Q2.val * !![1, r2, s2; 0, 0, -1; 0, 1, -1]) * W.val := by rw [hT12]
    _ = Q1.val * Q2.val * (!![1, r2, s2; 0, 0, -1; 0, 1, -1] * W.val) := by simp only [Matrix.mul_assoc]
    _ = Q1.val * Q2.val * (W.val * !![1, r2 - s2 - 3 * l, 0; 0, 0, -1; 0, 1, -1]) := by rw [hT2W]
    _ = Q1.val * Q2.val * W.val * !![1, r2 - s2 - 3 * l, 0; 0, 0, -1; 0, 1, -1] := by
        simp only [Matrix.mul_assoc]

/-! ### Normal forms for order three -/

/-- Helper: the Gram matrix of $l x^2 + m(y^2 + yz + z^2)$ (variables $x, y, z = x_0, x_1, x_2$). -/
def hn1 (l m : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := !![l, 0, 0; 0, m, m / 2; 0, m / 2, m]

/-- Helper: the Gram matrix of $l(3x + y - z)^2 + m(y^2 + yz + z^2)$. -/
def hn2 (l m : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![9 * l, 3 * l, -3 * l; 3 * l, l + m, m / 2 - l; -3 * l, m / 2 - l, l + m]

/-- Helper: a symmetric $3 \times 3$ matrix `H` (`hs`) is determined by its six upper entries. -/
theorem sym_eq_of (H : Matrix (Fin 3) (Fin 3) ℚ) (hs : Hᵀ = H) :
    H = !![H 0 0, H 0 1, H 0 2; H 0 1, H 1 1, H 1 2; H 0 2, H 1 2, H 2 2] := by
  have h10 : H 1 0 = H 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h20 : H 2 0 = H 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h21 : H 2 1 = H 1 2 := by simpa using congrFun (congrFun hs 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h21]

/-- Helper: **Gram matrices invariant under the standard order-three matrix.** A symmetric rational matrix `H3` (`hs`) invariant under the matrix with parameter `j` (`h`, `hj`) is transformed by some $U \in \mathrm{GL}_3(\mathbb Z)$ into `hn1 l m` or `hn2 l m`. -/
theorem gram_order_three (H3 : Matrix (Fin 3) (Fin 3) ℚ) (hs : H3ᵀ = H3) (j : ℤ)
    (hj : j = 0 ∨ j = 1 ∨ j = -1)
    (h : (toQ !![1, j, 0; 0, 0, -1; 0, 1, -1])ᵀ * H3 * toQ !![1, j, 0; 0, 0, -1; 0, 1, -1] = H3) :
    ∃ (U : GL (Fin 3) ℤ) (l m : ℚ), (toQ U.val)ᵀ * H3 * toQ U.val = hn1 l m ∨
      (toQ U.val)ᵀ * H3 * toQ U.val = hn2 l m := by
  rw [sym_eq_of H3 hs] at h ⊢
  set a := H3 0 0
  set p := H3 0 1
  set q := H3 0 2
  set b := H3 1 1
  set c := H3 1 2
  set d := H3 2 2
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e11 := congrFun (congrFun h 1) 1
  have e12 := congrFun (congrFun h 1) 2
  have e22 := congrFun (congrFun h 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, toQ] at e01 e02 e11 e12 e22
  rcases hj with rfl | rfl | rfl
  · push_cast at e01 e02 e11 e12 e22
    have hq : q = 0 := by linarith
    have hp : p = 0 := by linarith
    have hd : d = b := by nlinarith
    have hc : c = -b / 2 := by linarith
    have hU : IsUnit (!![1, 0, 0; 0, 1, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
      simp [Matrix.det_fin_three]
    refine ⟨glOf _ hU, a, b, Or.inl ?_⟩
    rw [glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, toQ, hn1, hq, hp, hd, hc] <;> ring
  · push_cast at e01 e02 e11 e12 e22
    have hq : q = -a / 3 := by linarith
    have hp : p = 2 * a / 3 := by linarith
    have hd : d = b - a / 3 := by linarith
    have hc : c = -b / 2 := by linarith
    have hU : IsUnit (!![1, 0, 0; 0, 1, 0; 0, 1, 1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
      simp [Matrix.det_fin_three]
    refine ⟨glOf _ hU, a / 9, b - 4 * a / 9, Or.inr ?_⟩
    rw [glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, toQ, hn2, hq, hp, hd, hc] <;> ring
  · push_cast at e01 e02 e11 e12 e22
    have hq : q = a / 3 := by linarith
    have hp : p = -2 * a / 3 := by linarith
    have hd : d = b - a / 3 := by linarith
    have hc : c = -b / 2 := by linarith
    have hU : IsUnit (!![1, 0, 0; 0, -1, 0; 0, -1, -1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
      simp [Matrix.det_fin_three]
    refine ⟨glOf _ hU, a / 9, b - 4 * a / 9, Or.inr ?_⟩
    rw [glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, toQ, hn2, hq, hp, hd, hc] <;> ring

/-! ### Rational forms: Gram matrices and integral equivalence -/

/-- Helper: $f(\vec x) = \vec x^{\mathsf T} A\vec x$ for the Gram matrix $A = \tfrac12 H$ of a rational form. -/
theorem eval_eq_gram (f : QuadForm ℚ 3) (x : Fin 3 → ℚ) : f.eval x = x ⬝ᵥ (RatQF.gram f *ᵥ x) := by
  have := RatQF.evalIn_eq_gram ℚ f x
  simpa using this

/-- Helper: the Gram matrix of a rational form is symmetric. -/
theorem gram_symm (f : QuadForm ℚ 3) : (RatQF.gram f)ᵀ = RatQF.gram f := (RatQF.gram_isSymm f)

/-- Helper: $f(M\vec x) = \vec x^{\mathsf T}(M^{\mathsf T}A_fM)\vec x$ for a rational matrix `M`. -/
theorem eval_comp (f : QuadForm ℚ 3) (M : Matrix (Fin 3) (Fin 3) ℚ) (x : Fin 3 → ℚ) :
    f.eval (M *ᵥ x) = x ⬝ᵥ ((Mᵀ * RatQF.gram f * M) *ᵥ x) := by
  rw [eval_eq_gram]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/-- Helper: $f(M\vec x) = g(\vec x)$ for all $\vec x \in \mathbb Q^3$ iff $M^{\mathsf T} A_f M = A_g$ for the Gram matrices. -/
theorem eval_comp_eq_iff (f g : QuadForm ℚ 3) (M : Matrix (Fin 3) (Fin 3) ℚ) :
    (∀ x, f.eval (M *ᵥ x) = g.eval x) ↔ Mᵀ * RatQF.gram f * M = RatQF.gram g := by
  constructor
  · intro h
    refine eq_of_forall_dotProduct ?_ (gram_symm g) fun x => ?_
    · simp [Matrix.transpose_mul, Matrix.mul_assoc, gram_symm f]
    · rw [← eval_comp, h, eval_eq_gram]
  · intro h x
    rw [eval_comp, h, eval_eq_gram]

/-- **Proper integral equivalence of rational forms.** $f$ is properly integrally equivalent to $g$ when
$f(U\vec x) = g(\vec x)$ for all $\vec x \in \mathbb Q^3$ for some integral matrix $U$ with $\det U = 1$ (so
$U \in \mathrm{SL}_3(\mathbb Z)$); this is `Siegel.ProperIntEquiv` for forms with rational coefficients. -/
def RatProperIntEquiv (f g : QuadForm ℚ 3) : Prop :=
  ∃ U : Matrix (Fin 3) (Fin 3) ℤ, U.det = 1 ∧ ∀ x : Fin 3 → ℚ, f.eval (toQ U *ᵥ x) = g.eval x

/-- Helper: `hn1 l m` is symmetric. -/
theorem hn1_symm (l m : ℚ) : (hn1 l m)ᵀ = hn1 l m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hn1]

/-- Helper: `hn2 l m` is symmetric. -/
theorem hn2_symm (l m : ℚ) : (hn2 l m)ᵀ = hn2 l m := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hn2]

/-- **The form** $l x^2 + m(y^2 + yz + z^2)$ in the variables $x = x_0$, $y = x_1$, $z = x_2$
(rational coefficients $l, m$; Gram matrix `hn1 l m`). -/
noncomputable def normForm1 (l m : ℚ) : QuadForm ℚ 3 := RatQF.ofGram (hn1 l m)

/-- **The form** $l(3x + y - z)^2 + m(y^2 + yz + z^2)$ in the variables $x = x_0$, $y = x_1$, $z = x_2$
(Gram matrix `hn2 l m`). -/
noncomputable def normForm2 (l m : ℚ) : QuadForm ℚ 3 := RatQF.ofGram (hn2 l m)

/-- The Gram matrix of `normForm1 l m` is `hn1 l m`. -/
theorem gram_normForm1 (l m : ℚ) : RatQF.gram (normForm1 l m) = hn1 l m :=
  RatQF.gram_ofGram _ (hn1_symm l m)

/-- The Gram matrix of `normForm2 l m` is `hn2 l m`. -/
theorem gram_normForm2 (l m : ℚ) : RatQF.gram (normForm2 l m) = hn2 l m :=
  RatQF.gram_ofGram _ (hn2_symm l m)

/-- The values of `normForm1`: $l x_0^2 + m(x_1^2 + x_1x_2 + x_2^2)$. -/
theorem eval_normForm1 (l m : ℚ) (x : Fin 3 → ℚ) :
    (normForm1 l m).eval x = l * x 0 ^ 2 + m * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
  rw [eval_eq_gram, gram_normForm1]
  simp [hn1, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The values of `normForm2`: $l(3x_0 + x_1 - x_2)^2 + m(x_1^2 + x_1x_2 + x_2^2)$. -/
theorem eval_normForm2 (l m : ℚ) (x : Fin 3 → ℚ) :
    (normForm2 l m).eval x = l * (3 * x 0 + x 1 - x 2) ^ 2 + m * (x 1 ^ 2 + x 1 * x 2 + x 2 ^ 2) := by
  rw [eval_eq_gram, gram_normForm2]
  simp [hn2, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- Helper: a unimodular Gram transformation can be taken with determinant $+1$ (replace $U$ by $-U$; every quadratic
form is even, and $\det(-U) = -\det U$ in dimension three). -/
theorem exists_det_one_of_gram {G Gn : Matrix (Fin 3) (Fin 3) ℚ} (U : GL (Fin 3) ℤ)
    (h : (toQ U.val)ᵀ * G * toQ U.val = Gn) :
    ∃ V : GL (Fin 3) ℤ, V.val.det = 1 ∧ (toQ V.val)ᵀ * G * toQ V.val = Gn := by
  rcases Siegel.det_GL_int_eq U with h1 | h1
  · exact ⟨U, h1, h⟩
  · have hd : IsUnit (-U.val).det := by
      rw [Matrix.det_neg, h1]; simp
    refine ⟨glOf _ hd, ?_, ?_⟩
    · rw [glOf_val, Matrix.det_neg, h1]; simp
    · rw [glOf_val]
      have : toQ (-U.val) = -toQ U.val := by ext i j; simp [toQ]
      rw [this]
      simpa [Matrix.transpose_neg] using h

/-- Helper: an element `V` of $\mathrm{GL}_3(\mathbb Z)$ maps nonzero rational vectors `x` (`hx`) to nonzero vectors. -/
theorem toQ_mulVec_ne_zero (V : GL (Fin 3) ℤ) {x : Fin 3 → ℚ} (hx : x ≠ 0) : toQ V.val *ᵥ x ≠ 0 := by
  intro h
  apply hx
  have h1 : toQ (V⁻¹).val * toQ V.val = 1 := by
    rw [← toQ_mul, Units.inv_mul, toQ_one]
  have := congrArg (fun y => toQ (V⁻¹).val *ᵥ y) h
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  exact this

/-- Helper: if `f` is positive definite (`hf`) and $f(V\vec x) = g(\vec x)$ (`h`) for some `V` in $\mathrm{GL}_3(\mathbb Z)$, then `g` is positive definite. -/
theorem ratPosDef_of_equiv {f g : QuadForm ℚ 3} (hf : Siegel.RatPosDef f) (V : GL (Fin 3) ℤ)
    (h : ∀ x, f.eval (toQ V.val *ᵥ x) = g.eval x) : Siegel.RatPosDef g := by
  intro x hx
  rw [← h]
  exact hf _ (toQ_mulVec_ne_zero V hx)

/-- Helper: the involution $(x, y, z) \mapsto (-x, z, y)$ of determinant $1$. -/
def invS : Matrix (Fin 3) (Fin 3) ℤ := !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- Helper: `invS` preserves the Gram matrix `hn1 l m`. -/
theorem invS_hn1 (l m : ℚ) : (toQ invS)ᵀ * hn1 l m * toQ invS = hn1 l m := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, toQ, invS, hn1] <;> ring

/-- Helper: `invS` preserves the Gram matrix `hn2 l m`. -/
theorem invS_hn2 (l m : ℚ) : (toQ invS)ᵀ * hn2 l m * toQ invS = hn2 l m := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, toQ, invS, hn2] <;> ring

/-- Helper: `invS` is an involution. -/
theorem invS_sq : invS * invS = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, invS]

/-- Helper: $\det$ `invS` $= 1$. -/
theorem invS_det : invS.det = 1 := by simp [invS, Matrix.det_fin_three]

/-- Helper: `invS` is not the identity. -/
theorem invS_ne : invS ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [invS] at this

/-- Helper: conjugating an automorph `S0` of the transformed Gram matrix `Gn` back gives an automorph of `G`. -/
theorem conj_automorph {G Gn : Matrix (Fin 3) (Fin 3) ℚ} (U : GL (Fin 3) ℤ) (S0 : Matrix (Fin 3) (Fin 3) ℤ)
    (hU : (toQ U.val)ᵀ * G * toQ U.val = Gn) (hS : (toQ S0)ᵀ * Gn * toQ S0 = Gn) :
    (toQ (U.val * S0 * (U⁻¹).val))ᵀ * G * toQ (U.val * S0 * (U⁻¹).val) = G := by
  have h1 : toQ U.val * toQ (U⁻¹).val = 1 := by rw [← toQ_mul, Units.mul_inv, toQ_one]
  have hG : G = (toQ (U⁻¹).val)ᵀ * Gn * toQ (U⁻¹).val := by
    rw [← hU]
    calc G = (toQ U.val * toQ (U⁻¹).val)ᵀ * G * (toQ U.val * toQ (U⁻¹).val) := by rw [h1]; simp
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  calc (toQ (U.val * S0 * (U⁻¹).val))ᵀ * G * toQ (U.val * S0 * (U⁻¹).val)
      = (toQ (U⁻¹).val)ᵀ * (toQ S0)ᵀ * ((toQ U.val)ᵀ * G * toQ U.val) * toQ S0 * toQ (U⁻¹).val := by
        simp only [toQ_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (toQ (U⁻¹).val)ᵀ * ((toQ S0)ᵀ * Gn * toQ S0) * toQ (U⁻¹).val := by
        rw [hU]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hS, ← hG]

/-- Helper: if $XQ = QY$ (`hX`) and $X^{\mathsf T}HX = H$ (`haut`) then `Y` preserves $Q^{\mathsf T}HQ$. -/
theorem conj_gram {H X Q Y : Matrix (Fin 3) (Fin 3) ℚ} (hX : X * Q = Q * Y) (haut : Xᵀ * H * X = H) :
    Yᵀ * (Qᵀ * H * Q) * Y = Qᵀ * H * Q := by
  calc Yᵀ * (Qᵀ * H * Q) * Y = (Q * Y)ᵀ * H * (Q * Y) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (X * Q)ᵀ * H * (X * Q) := by rw [hX]
    _ = Qᵀ * (Xᵀ * H * X) * Q := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Qᵀ * H * Q := by rw [haut]

/-- Helper: **Gram normal form for an automorph of order three.** For `f` with Gram matrix invariant under `T` (`haut`), $T^3 = 1$, $T \ne 1$, $\det T = 1$, there is `U` of determinant $1$ in $\mathrm{GL}_3(\mathbb Z)$ with $U^{\mathsf T}A_fU$ equal to `hn1 l m` or `hn2 l m`. -/
theorem order_three_normal (f : QuadForm ℚ 3) (T : Matrix (Fin 3) (Fin 3) ℤ) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) (haut : (toQ T)ᵀ * RatQF.gram f * toQ T = RatQF.gram f) :
    ∃ (U : GL (Fin 3) ℤ) (l m : ℚ), U.val.det = 1 ∧
      ((toQ U.val)ᵀ * RatQF.gram f * toQ U.val = hn1 l m ∨
        (toQ U.val)ᵀ * RatQF.gram f * toQ U.val = hn2 l m) := by
  obtain ⟨Q, j, hj, hTQ⟩ := order_three_shape T hT3 hT1 hdet
  have hX : toQ T * toQ Q.val = toQ Q.val * toQ !![1, j, 0; 0, 0, -1; 0, 1, -1] := by
    rw [← toQ_mul, ← toQ_mul, hTQ]
  have h3 := conj_gram hX haut
  have hs : ((toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val)ᵀ = (toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, gram_symm f]
  obtain ⟨U', l, m, hU'⟩ := gram_order_three _ hs j hj h3
  have hcomp : ∀ Gn : Matrix (Fin 3) (Fin 3) ℚ, (toQ U'.val)ᵀ * ((toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val) *
      toQ U'.val = Gn → (toQ (Q * U').val)ᵀ * RatQF.gram f * toQ (Q * U').val = Gn := by
    intro Gn h
    rw [← h, Units.val_mul, toQ_mul]
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨V, hV, hV'⟩ : ∃ V : GL (Fin 3) ℤ, V.val.det = 1 ∧
      ((toQ V.val)ᵀ * RatQF.gram f * toQ V.val = hn1 l m ∨
        (toQ V.val)ᵀ * RatQF.gram f * toQ V.val = hn2 l m) := by
    rcases hU' with h | h
    · obtain ⟨V, hV, hV'⟩ := exists_det_one_of_gram (Q * U') (hcomp _ h)
      exact ⟨V, hV, Or.inl hV'⟩
    · obtain ⟨V, hV, hV'⟩ := exists_det_one_of_gram (Q * U') (hcomp _ h)
      exact ⟨V, hV, Or.inr hV'⟩
  exact ⟨V, l, m, hV, hV'⟩

/-- Helper: a matrix `S` with $S^2 = 1$ (`h2`) and $S \ne 1$ (`h1`) has order $2$. -/
theorem orderOf_two_of_involution {S : Matrix (Fin 3) (Fin 3) ℤ} (h2 : S * S = 1) (h1 : S ≠ 1) :
    orderOf S = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [pow_two]; exact h2) h1

/-- **Cassels, Ch. 9, Example 15 (ii)** (p. 165): *let $f$ be a positive definite rational ternary form with a
proper integral automorph of order $3$. Then $f$ is properly integrally equivalent to $l x^2 + m(y^2 + yz + z^2)$ or
to $l(3x + y - z)^2 + m(y^2 + yz + z^2)$ with $l, m > 0$ rational; deduce that $f$ also has a proper integral
automorph of order $2$.*

Arguments: `f` (the form), `hf` (positive definite over $\mathbb Q$, `Siegel.RatPosDef`), `T` (an integral matrix),
`hdet` ($\det T = 1$), `haut` ($f(T\vec x) = f(\vec x)$ for all $\vec x \in \mathbb Q^3$, as in
`Siegel.orderOf_mem_of_proper_automorph`), `hord` ($T$ has order $3$ in the monoid $M_3(\mathbb Z)$). The first
conjunct gives $l, m$ and the equivalence with `normForm1 l m` or `normForm2 l m` (`RatProperIntEquiv`); the second
gives an integral $S$ with $\det S = 1$, order $2$, and $f(S\vec x) = f(\vec x)$. Unconditional. -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (ii), p. 165"]
theorem ex15_ii {f : QuadForm ℚ 3} (hf : Siegel.RatPosDef f) {T : Matrix (Fin 3) (Fin 3) ℤ}
    (hdet : T.det = 1)
    (haut : ∀ x : Fin 3 → ℚ, f.eval ((T.map (Int.castRingHom ℚ)) *ᵥ x) = f.eval x)
    (hord : orderOf T = 3) :
    (∃ l m : ℚ, 0 < l ∧ 0 < m ∧
      (RatProperIntEquiv f (normForm1 l m) ∨ RatProperIntEquiv f (normForm2 l m))) ∧
    ∃ S : Matrix (Fin 3) (Fin 3) ℤ, S.det = 1 ∧ orderOf S = 2 ∧
      ∀ x : Fin 3 → ℚ, f.eval (toQ S *ᵥ x) = f.eval x := by
  have hT3 : T ^ 3 = 1 := by
    have := pow_orderOf_eq_one T
    rwa [hord] at this
  have hT1 : T ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; omega
  have haut' := (eval_comp_eq_iff f f (toQ T)).1 haut
  obtain ⟨U, l, m, hU, hcases⟩ := order_three_normal f T hT3 hT1 hdet haut'
  have hiff1 := eval_comp_eq_iff f (normForm1 l m) (toQ U.val)
  have hiff2 := eval_comp_eq_iff f (normForm2 l m) (toQ U.val)
  rw [gram_normForm1] at hiff1
  rw [gram_normForm2] at hiff2
  refine ⟨?_, ?_⟩
  · rcases hcases with h | h
    · have hev := hiff1.2 h
      have hpd := ratPosDef_of_equiv hf U hev
      refine ⟨l, m, ?_, ?_, Or.inl ⟨U.val, hU, hev⟩⟩
      · have := hpd (Pi.single 0 1) (by
          intro h0; have := congrFun h0 0; simp at this)
        rw [eval_normForm1] at this
        simpa using this
      · have := hpd (Pi.single 1 1) (by
          intro h0; have := congrFun h0 1; simp at this)
        rw [eval_normForm1] at this
        simpa using this
    · have hev := hiff2.2 h
      have hpd := ratPosDef_of_equiv hf U hev
      refine ⟨l, m, ?_, ?_, Or.inr ⟨U.val, hU, hev⟩⟩
      · have := hpd (Pi.single 0 1) (by
          intro h0; have := congrFun h0 0; simp at this)
        rw [eval_normForm2] at this
        simp at this
        linarith
      · have := hpd ![1, -3, 0] (by
          intro h0; have := congrFun h0 0; simp at this)
        rw [eval_normForm2] at this
        simp at this
        linarith
  · refine ⟨U.val * invS * (U⁻¹).val, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, invS_det, hU]
      have : (U⁻¹).val.det = 1 := by
        have := congrArg Matrix.det (Units.mul_inv U)
        rw [Matrix.det_mul, hU, one_mul, Matrix.det_one] at this
        exact this
      rw [this]; norm_num
    · apply orderOf_two_of_involution
      · calc U.val * invS * (U⁻¹).val * (U.val * invS * (U⁻¹).val)
            = U.val * invS * ((U⁻¹).val * U.val) * invS * (U⁻¹).val := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [Units.inv_mul, Matrix.mul_one, Matrix.mul_assoc U.val, invS_sq, Matrix.mul_one,
                Units.mul_inv]
      · intro h
        have : invS = 1 := by
          have := congrArg (fun M => (U⁻¹).val * M * U.val) h
          simpa [Matrix.mul_assoc] using this
        exact invS_ne this
    · rcases hcases with h | h
      · exact (eval_comp_eq_iff f f _).2 (conj_automorph U invS h (invS_hn1 l m))
      · exact (eval_comp_eq_iff f f _).2 (conj_automorph U invS h (invS_hn2 l m))

/-! ### Elements of order two -/

/-- Helper: an integer $3 \times 3$ matrix $T \ne 1$ with $T^2 = 1$ and $\det T = 1$ has $\operatorname{adj} T = T$ and
$\operatorname{tr} T = -1$ (eigenvalues $1, -1, -1$). -/
theorem order_two_trace (T : Matrix (Fin 3) (Fin 3) ℤ) (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) : adjugate T = T ∧ T.trace = -1 := by
  have hadj : adjugate T = T := by
    have h1 : T * adjugate T = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
    calc adjugate T = (T * T) * adjugate T := by rw [hT2, Matrix.one_mul]
      _ = T * (T * adjugate T) := by rw [Matrix.mul_assoc]
      _ = T := by rw [h1, Matrix.mul_one]
  refine ⟨hadj, ?_⟩
  have hc := cayley3 T
  have hT2' : T ^ 2 = 1 := by rw [pow_two]; exact hT2
  have hT3 : T ^ 3 = T := by rw [pow_succ, hT2', one_mul]
  rw [hT3, hT2', hdet, hadj, one_smul] at hc
  set s := T.trace with hs
  by_contra hne
  have h : (1 + s) • (T - 1) = 0 := by linear_combination (norm := module) hc
  have h1s : (1 + s) ≠ 0 := fun h0 => hne (by linarith)
  exact hT1 (sub_eq_zero.1 ((smul_eq_zero.1 h).resolve_left h1s))

/-- Helper: **shape of an element of order two.** If $T \in M_3(\mathbb Z)$, $T^2 = 1$, $T \ne 1$, $\det T = 1$, then
$TQ = QD$ for some $Q \in \mathrm{GL}_3(\mathbb Z)$ with $D = \operatorname{diag}(1, -1, -1)$ or
$D = \begin{pmatrix} 1 & 1 & 0 \\ 0 & -1 & 0 \\ 0 & 0 & -1 \end{pmatrix}$. -/
theorem order_two_shape (T : Matrix (Fin 3) (Fin 3) ℤ) (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) :
    ∃ Q : GL (Fin 3) ℤ, T * Q.val = Q.val * !![1, 0, 0; 0, -1, 0; 0, 0, -1] ∨
      T * Q.val = Q.val * !![1, 1, 0; 0, -1, 0; 0, 0, -1] := by
  obtain ⟨hadj, htr⟩ := order_two_trace T hT2 hT1 hdet
  have hdet1 : (T - 1).det = 0 := by rw [det_sub_one, hdet, hadj, htr]; norm_num
  obtain ⟨Q1, r, s, α, β, γ, δ, hQ1⟩ := exists_adapted T hdet1
  have hconj : (Q1⁻¹).val * T * Q1.val = !![1, r, s; 0, α, β; 0, γ, δ] := by
    rw [Matrix.mul_assoc, hQ1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have htr1 := Matrix.trace_units_conj' Q1 T
  have hdet1' := Matrix.det_units_conj' Q1 T
  rw [hconj] at htr1 hdet1'
  have hsq : !![1, r, s; 0, α, β; 0, γ, δ] * !![1, r, s; 0, α, β; 0, γ, δ] = 1 := by
    rw [← hconj]
    calc (Q1⁻¹).val * T * Q1.val * ((Q1⁻¹).val * T * Q1.val)
        = (Q1⁻¹).val * (T * (Q1.val * (Q1⁻¹).val) * T) * Q1.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hT2, Matrix.mul_one, Units.inv_mul]
  have h1 : α + δ = -2 := by
    simp [Matrix.trace_fin_three, htr] at htr1; linarith
  have h2 : α * δ - β * γ = 1 := by
    rw [hdet] at hdet1'
    simp [Matrix.det_fin_three] at hdet1'; linarith
  have e11 := congrFun (congrFun hsq 1) 1
  have e12 := congrFun (congrFun hsq 1) 2
  have e21 := congrFun (congrFun hsq 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e11 e12 e21
  have hα : α = -1 := by nlinarith
  have hδ : δ = -1 := by linarith
  have hβ : β = 0 := by subst hα hδ; linarith
  have hγ : γ = 0 := by subst hα hδ; linarith
  subst hα hδ hβ hγ
  -- normalize `(r, s)` modulo `2`
  obtain ⟨k, l, hk, hl⟩ : ∃ k l : ℤ, (r + 2 * k = 0 ∨ r + 2 * k = 1) ∧ (s + 2 * l = 0 ∨ s + 2 * l = 1) :=
    ⟨-(r / 2), -(s / 2), by omega, by omega⟩
  have hWd : IsUnit (!![1, k, l; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
    simp [Matrix.det_fin_three]
  set W := glOf _ hWd with hW
  have hTW : !![1, r, s; 0, -1, 0; 0, 0, -1] * W.val
      = W.val * !![1, r + 2 * k, s + 2 * l; 0, -1, 0; 0, 0, -1] := by
    rw [hW, glOf_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  have hTQW : T * (Q1 * W).val
      = (Q1 * W).val * !![1, r + 2 * k, s + 2 * l; 0, -1, 0; 0, 0, -1] := by
    rw [Units.val_mul, ← Matrix.mul_assoc, hQ1, Matrix.mul_assoc, hTW, ← Matrix.mul_assoc]
  rcases hk with hk | hk <;> rcases hl with hl | hl
  · refine ⟨Q1 * W, Or.inl ?_⟩
    rw [hTQW, hk, hl]
  · -- `(0, 1)`: swap the last two coordinates
    have hPd : IsUnit (!![1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℤ).det := by
      simp [Matrix.det_fin_three]
    set P := glOf _ hPd with hP
    have hTP : !![1, r + 2 * k, s + 2 * l; 0, -1, 0; 0, 0, -1] * P.val
        = P.val * !![1, 1, 0; 0, -1, 0; 0, 0, -1] := by
      rw [hP, glOf_val, hk, hl]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    refine ⟨Q1 * W * P, Or.inr ?_⟩
    rw [Units.val_mul, ← Matrix.mul_assoc, hTQW, Matrix.mul_assoc, hTP, ← Matrix.mul_assoc]
  · refine ⟨Q1 * W, Or.inr ?_⟩
    rw [hTQW, hk, hl]
  · -- `(1, 1)`: shear
    have hPd : IsUnit (!![1, 0, 0; 0, 1, -1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ).det := by
      simp [Matrix.det_fin_three]
    set P := glOf _ hPd with hP
    have hTP : !![1, r + 2 * k, s + 2 * l; 0, -1, 0; 0, 0, -1] * P.val
        = P.val * !![1, 1, 0; 0, -1, 0; 0, 0, -1] := by
      rw [hP, glOf_val, hk, hl]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    refine ⟨Q1 * W * P, Or.inr ?_⟩
    rw [Units.val_mul, ← Matrix.mul_assoc, hTQW, Matrix.mul_assoc, hTP, ← Matrix.mul_assoc]

/-! ### Normal forms for order two -/

/-- Helper: the Gram matrix of $a x^2 + b y^2 + c z^2 + l\,yz$. -/
def hn3 (a b c l : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := !![a, 0, 0; 0, b, l / 2; 0, l / 2, c]

/-- Helper: the Gram matrix of $a x^2 + b y^2 + c z^2 + a\,xy + l\,yz$. -/
def hn4 (a b c l : ℚ) : Matrix (Fin 3) (Fin 3) ℚ := !![a, a / 2, 0; a / 2, b, l / 2; 0, l / 2, c]

/-- Helper: `hn3 a b c l` is symmetric. -/
theorem hn3_symm (a b c l : ℚ) : (hn3 a b c l)ᵀ = hn3 a b c l := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hn3]

/-- Helper: `hn4 a b c l` is symmetric. -/
theorem hn4_symm (a b c l : ℚ) : (hn4 a b c l)ᵀ = hn4 a b c l := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hn4]

/-- **The form** $a x^2 + b y^2 + c z^2 + l\,yz$ ($x = x_0$, $y = x_1$, $z = x_2$). -/
noncomputable def normForm3 (a b c l : ℚ) : QuadForm ℚ 3 := RatQF.ofGram (hn3 a b c l)

/-- **The form** $a x^2 + b y^2 + c z^2 + a\,xy + l\,yz$ ($x = x_0$, $y = x_1$, $z = x_2$). -/
noncomputable def normForm4 (a b c l : ℚ) : QuadForm ℚ 3 := RatQF.ofGram (hn4 a b c l)

/-- The Gram matrix of `normForm3 a b c l` is `hn3 a b c l`. -/
theorem gram_normForm3 (a b c l : ℚ) : RatQF.gram (normForm3 a b c l) = hn3 a b c l :=
  RatQF.gram_ofGram _ (hn3_symm a b c l)

/-- The Gram matrix of `normForm4 a b c l` is `hn4 a b c l`. -/
theorem gram_normForm4 (a b c l : ℚ) : RatQF.gram (normForm4 a b c l) = hn4 a b c l :=
  RatQF.gram_ofGram _ (hn4_symm a b c l)

/-- The values of `normForm3`: $a x_0^2 + b x_1^2 + c x_2^2 + l x_1 x_2$. -/
theorem eval_normForm3 (a b c l : ℚ) (x : Fin 3 → ℚ) :
    (normForm3 a b c l).eval x = a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 + l * x 1 * x 2 := by
  rw [eval_eq_gram, gram_normForm3]
  simp [hn3, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- The values of `normForm4`: $a x_0^2 + b x_1^2 + c x_2^2 + a x_0 x_1 + l x_1 x_2$. -/
theorem eval_normForm4 (a b c l : ℚ) (x : Fin 3 → ℚ) :
    (normForm4 a b c l).eval x = a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 + a * x 0 * x 1 + l * x 1 * x 2 := by
  rw [eval_eq_gram, gram_normForm4]
  simp [hn4, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- Helper: a symmetric rational matrix `H` (`hs`) invariant under one of the two standard involutions (`h`) is `hn3 a b c l` or `hn4 a b c l`. -/
theorem gram_order_two (H : Matrix (Fin 3) (Fin 3) ℚ) (hs : Hᵀ = H)
    (h : (toQ !![1, 0, 0; 0, -1, 0; 0, 0, -1])ᵀ * H * toQ !![1, 0, 0; 0, -1, 0; 0, 0, -1] = H ∨
      (toQ !![1, 1, 0; 0, -1, 0; 0, 0, -1])ᵀ * H * toQ !![1, 1, 0; 0, -1, 0; 0, 0, -1] = H) :
    (∃ a b c l : ℚ, H = hn3 a b c l) ∨ ∃ a b c l : ℚ, H = hn4 a b c l := by
  have hH := sym_eq_of H hs
  rcases h with h | h
  · left
    rw [hH] at h
    have e01 := congrFun (congrFun h 0) 1
    have e02 := congrFun (congrFun h 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, toQ] at e01 e02
    refine ⟨H 0 0, H 1 1, H 2 2, 2 * H 1 2, ?_⟩
    rw [hH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hn3] <;> linarith
  · right
    rw [hH] at h
    have e01 := congrFun (congrFun h 0) 1
    have e02 := congrFun (congrFun h 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, toQ] at e01 e02
    refine ⟨H 0 0, H 1 1, H 2 2, 2 * H 1 2, ?_⟩
    rw [hH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hn4] <;> linarith

/-- Helper: **Gram normal form for an involution.** For `f` with Gram matrix invariant under `T` (`haut`), $T^2 = 1$, $T \ne 1$, $\det T = 1$, there is `U` of determinant $1$ in $\mathrm{GL}_3(\mathbb Z)$ with $U^{\mathsf T}A_fU$ equal to `hn3 a b c l` or `hn4 a b c l`. -/
theorem order_two_normal (f : QuadForm ℚ 3) (T : Matrix (Fin 3) (Fin 3) ℤ) (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hdet : T.det = 1) (haut : (toQ T)ᵀ * RatQF.gram f * toQ T = RatQF.gram f) :
    ∃ (U : GL (Fin 3) ℤ) (a b c l : ℚ), U.val.det = 1 ∧
      ((toQ U.val)ᵀ * RatQF.gram f * toQ U.val = hn3 a b c l ∨
        (toQ U.val)ᵀ * RatQF.gram f * toQ U.val = hn4 a b c l) := by
  obtain ⟨Q, hQ⟩ := order_two_shape T hT2 hT1 hdet
  have hs : ((toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val)ᵀ = (toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc, gram_symm f]
  have hg : (toQ !![1, 0, 0; 0, -1, 0; 0, 0, -1])ᵀ * ((toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val) *
        toQ !![1, 0, 0; 0, -1, 0; 0, 0, -1] = (toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val ∨
      (toQ !![1, 1, 0; 0, -1, 0; 0, 0, -1])ᵀ * ((toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val) *
        toQ !![1, 1, 0; 0, -1, 0; 0, 0, -1] = (toQ Q.val)ᵀ * RatQF.gram f * toQ Q.val := by
    rcases hQ with hQ | hQ
    · left
      exact conj_gram (by rw [← toQ_mul, ← toQ_mul, hQ]) haut
    · right
      exact conj_gram (by rw [← toQ_mul, ← toQ_mul, hQ]) haut
  rcases gram_order_two _ hs hg with ⟨a, b, c, l, hl⟩ | ⟨a, b, c, l, hl⟩
  · obtain ⟨V, hV, hV'⟩ := exists_det_one_of_gram Q hl
    exact ⟨V, a, b, c, l, hV, Or.inl hV'⟩
  · obtain ⟨V, hV, hV'⟩ := exists_det_one_of_gram Q hl
    exact ⟨V, a, b, c, l, hV, Or.inr hV'⟩

/-- Helper: powers `T ^ k` of an automorph `T` (`h`) are automorphs. -/
theorem aut_pow {G : Matrix (Fin 3) (Fin 3) ℚ} {T : Matrix (Fin 3) (Fin 3) ℤ}
    (h : (toQ T)ᵀ * G * toQ T = G) (k : ℕ) : (toQ (T ^ k))ᵀ * G * toQ (T ^ k) = G := by
  induction k with
  | zero => simp [toQ_one]
  | succ k ih =>
    rw [pow_succ, toQ_mul, Matrix.transpose_mul]
    calc (toQ T)ᵀ * (toQ (T ^ k))ᵀ * G * (toQ (T ^ k) * toQ T)
        = (toQ T)ᵀ * ((toQ (T ^ k))ᵀ * G * toQ (T ^ k)) * toQ T := by simp only [Matrix.mul_assoc]
      _ = G := by rw [ih, h]

/-- **Cassels, Ch. 9, Example 15 (iii)** (p. 165): *if a positive definite rational ternary form $f$ has a proper
integral automorph other than the identity, then $f$ is properly integrally equivalent to
$a x^2 + b y^2 + c z^2 + l\,yz$ or to $a x^2 + b y^2 + c z^2 + a\,xy + l\,yz$* (rational $a, b, c, l$; here also
$a, b, c > 0$). Arguments as in `ex15_ii`, with `hne` ($T \ne 1$) in place of the order. The conclusion is a
disjunction of existence statements with `normForm3 a b c l` and `normForm4 a b c l`. Proof: by (i) the order of $T$
is $2, 3, 4$ or $6$; a power of $T$ (for $3$: the automorph of order $2$ of (ii)) is an involution, whose normal forms
are computed. Unconditional. -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (iii), p. 165"]
theorem ex15_iii {f : QuadForm ℚ 3} (hf : Siegel.RatPosDef f) {T : Matrix (Fin 3) (Fin 3) ℤ}
    (hdet : T.det = 1)
    (haut : ∀ x : Fin 3 → ℚ, f.eval ((T.map (Int.castRingHom ℚ)) *ᵥ x) = f.eval x) (hne : T ≠ 1) :
    (∃ a b c l : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ RatProperIntEquiv f (normForm3 a b c l)) ∨
    (∃ a b c l : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ RatProperIntEquiv f (normForm4 a b c l)) := by
  have haut' := (eval_comp_eq_iff f f (toQ T)).1 haut
  have hord := Siegel.orderOf_mem_of_proper_automorph hf hdet haut
  -- an involution
  obtain ⟨S, hSdet, hS2, hS1, hSaut⟩ : ∃ S : Matrix (Fin 3) (Fin 3) ℤ, S.det = 1 ∧ S * S = 1 ∧ S ≠ 1 ∧
      (toQ S)ᵀ * RatQF.gram f * toQ S = RatQF.gram f := by
    have hT1 : orderOf T ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hord
    have hpow : ∀ k, (T ^ k).det = 1 := fun k => by rw [Matrix.det_pow, hdet, one_pow]
    rcases hord with h | h | h | h | h
    · exact absurd h hT1
    · refine ⟨T, hdet, ?_, hne, haut'⟩
      have := pow_orderOf_eq_one T
      rw [h, pow_two] at this
      exact this
    · obtain ⟨-, S, hSd, hSo, hSa⟩ := ex15_ii hf hdet haut h
      refine ⟨S, hSd, ?_, ?_, (eval_comp_eq_iff f f _).1 hSa⟩
      · have := pow_orderOf_eq_one S
        rw [hSo, pow_two] at this
        exact this
      · intro h1; rw [h1, orderOf_one] at hSo; omega
    · refine ⟨T ^ 2, hpow 2, ?_, ?_, aut_pow haut' 2⟩
      · rw [← pow_add]; have := pow_orderOf_eq_one T; rwa [h] at this
      · intro h1
        have := orderOf_dvd_of_pow_eq_one h1
        rw [h] at this; omega
    · refine ⟨T ^ 3, hpow 3, ?_, ?_, aut_pow haut' 3⟩
      · rw [← pow_add]; have := pow_orderOf_eq_one T; rwa [h] at this
      · intro h1
        have := orderOf_dvd_of_pow_eq_one h1
        rw [h] at this; omega
  obtain ⟨U, a, b, c, l, hU, hcases⟩ := order_two_normal f S hS2 hS1 hSdet hSaut
  have hiff3 := eval_comp_eq_iff f (normForm3 a b c l) (toQ U.val)
  have hiff4 := eval_comp_eq_iff f (normForm4 a b c l) (toQ U.val)
  rw [gram_normForm3] at hiff3
  rw [gram_normForm4] at hiff4
  have hpos : ∀ g : QuadForm ℚ 3, (∀ x, f.eval (toQ U.val *ᵥ x) = g.eval x) →
      0 < g.eval (Pi.single 0 1) ∧ 0 < g.eval (Pi.single 1 1) ∧ 0 < g.eval (Pi.single 2 1) := by
    intro g hg
    have hpd := ratPosDef_of_equiv hf U hg
    refine ⟨hpd _ ?_, hpd _ ?_, hpd _ ?_⟩
    · intro h0; have := congrFun h0 0; simp at this
    · intro h0; have := congrFun h0 1; simp at this
    · intro h0; have := congrFun h0 2; simp at this
  rcases hcases with h | h
  · have hev := hiff3.2 h
    obtain ⟨h0, h1, h2⟩ := hpos _ hev
    rw [eval_normForm3] at h0 h1 h2
    simp at h0 h1 h2
    exact Or.inl ⟨a, b, c, l, h0, h1, h2, U.val, hU, hev⟩
  · have hev := hiff4.2 h
    obtain ⟨h0, h1, h2⟩ := hpos _ hev
    rw [eval_normForm4] at h0 h1 h2
    simp at h0 h1 h2
    exact Or.inr ⟨a, b, c, l, h0, h1, h2, U.val, hU, hev⟩

/-! ### (iv): the order of the group of proper integral automorphs -/

/-- **The group of proper integral automorphs** of a rational ternary form $f$: the matrices
$T \in \mathrm{GL}_3(\mathbb Z)$ with $\det T = 1$ and $f(T\vec x) = f(\vec x)$ for all $\vec x \in \mathbb Q^3$. For
a form with integer coefficients it is `Siegel.AutPlus` (`ratAutPlus_map`). -/
def RatAutPlus (f : QuadForm ℚ 3) : Subgroup (GL (Fin 3) ℤ) where
  carrier := {g | g.val.det = 1 ∧ ∀ x : Fin 3 → ℚ, f.eval (toQ g.val *ᵥ x) = f.eval x}
  mul_mem' := by
    rintro a b ⟨ha1, ha⟩ ⟨hb1, hb⟩
    refine ⟨by rw [Units.val_mul, Matrix.det_mul, ha1, hb1, one_mul], fun x => ?_⟩
    rw [Units.val_mul, toQ_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := ⟨by simp, fun x => by simp [toQ_one]⟩
  inv_mem' := by
    rintro a ⟨ha1, ha⟩
    refine ⟨?_, fun x => ?_⟩
    · have := congrArg Matrix.det (Units.mul_inv a)
      rw [Matrix.det_mul, ha1, one_mul, Matrix.det_one] at this
      exact this
    · have h1 : toQ a.val * toQ (a⁻¹).val = 1 := by rw [← toQ_mul, Units.mul_inv, toQ_one]
      have := ha (toQ (a⁻¹).val *ᵥ x)
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
      exact this.symm

/-- Helper: a form with integer coefficients, viewed over $\mathbb Q$, takes the value `Q.evalIn ℚ y`. -/
theorem eval_map_cast (Q : QuadForm ℤ 3) (y : Fin 3 → ℚ) :
    (Q.map (Int.castRingHom ℚ)).eval y = Q.evalIn ℚ y := by
  simp [QuadForm.eval, QuadForm.evalIn, QuadForm.map]

/-- For an integral form the group `RatAutPlus` is `Siegel.AutPlus`. -/
theorem ratAutPlus_map (Q : QuadForm ℤ 3) :
    RatAutPlus (Q.map (Int.castRingHom ℚ)) = Siegel.AutPlus Q := by
  ext g
  rw [Siegel.mem_autPlus_iff]
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨fun x => ?_, hd⟩
    have := h (fun i => (x i : ℚ))
    rw [eval_map_cast, eval_map_cast] at this
    have e : toQ g.val *ᵥ (fun i => (x i : ℚ)) = fun i => (((g.val *ᵥ x) i : ℤ) : ℚ) := by
      funext i; simp [toQ, Matrix.mulVec, dotProduct]
    rw [e, Siegel.evalIn_intCast, Siegel.evalIn_intCast] at this
    exact_mod_cast this
  · rintro ⟨h, hd⟩
    have h' : ∀ x : Fin 3 → ℤ, Q.eval (g.val *ᵥ x) = Q.eval x := h
    exact ⟨hd, Siegel.eval_mulVec_map (Int.castRingHom ℚ) h'⟩

/-- Helper: every integral ternary form has the improper automorph $-1$. -/
theorem hasImproperAut_three (Q : QuadForm ℤ 3) : Siegel.HasImproperAut Q := by
  have hd : IsUnit (-1 : Matrix (Fin 3) (Fin 3) ℤ).det := by
    simp [Matrix.det_neg]
  refine ⟨glOf _ hd, ?_, ?_⟩
  · show ∀ x : Fin 3 → ℤ, Q.eval ((glOf _ hd).val *ᵥ x) = Q.eval x
    intro x
    rw [glOf_val]
    have e : (-1 : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ x = -x := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [e]
    simp [QuadForm.evalIn]
  · rw [glOf_val]; simp [Matrix.det_neg]

/-- Helper: if $|\mathrm{Aut}(Q)| = 2n$ for an integral ternary form, the group of proper automorphs has order $n$
(the improper automorph $-1$ gives index $2$). -/
theorem card_ratAutPlus (Q : QuadForm ℤ 3) (n : ℕ) (h : Nat.card (Siegel.Aut Q) = 2 * n) :
    Nat.card (RatAutPlus (Q.map (Int.castRingHom ℚ))) = n := by
  rw [ratAutPlus_map]
  classical
  have hidx := Siegel.index_autPlus Q
  simp only [hasImproperAut_three Q, ite_true] at hidx
  rw [Subgroup.relIndex] at hidx
  have h1 := Subgroup.card_mul_index ((Siegel.AutPlus Q).subgroupOf (Siegel.Aut Q))
  have hle : Siegel.AutPlus Q ≤ Siegel.Aut Q := inf_le_left
  have h2 : Nat.card ((Siegel.AutPlus Q).subgroupOf (Siegel.Aut Q)) = Nat.card (Siegel.AutPlus Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2, hidx, h] at h1
  omega



/-- Helper: if $kv = s_1a^2 + s_2b^2 + s_3c^2$ with positive `k`, `s1`, `s2`, `s3` and `a`, `b`, `c` not all zero, then `v` is positive. -/
theorem pos_of_sos {k s1 s2 s3 a b c v : ℤ} (hk : 0 < k) (h1 : 0 < s1) (h2 : 0 < s2) (h3 : 0 < s3)
    (h : k * v = s1 * a ^ 2 + s2 * b ^ 2 + s3 * c ^ 2) (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : 0 < v := by
  have hpos : 0 < s1 * a ^ 2 + s2 * b ^ 2 + s3 * c ^ 2 := by
    rcases hne with h0 | h0 | h0
    · have := pow_pos (abs_pos.2 h0) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg b, sq_nonneg c]
    · have := pow_pos (abs_pos.2 h0) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg a, sq_nonneg c]
    · have := pow_pos (abs_pos.2 h0) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg a, sq_nonneg b]
  by_contra hv
  push Not at hv
  nlinarith

/-- Helper: the integral form with upper coefficient matrix `[[1, 0, 0], [0, 1, 0], [0, 0, 1]]` (see `eval_exQ24`). -/
def exQ24 : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- Helper: the value of the witness form `exQ24` as a polynomial. -/
theorem eval_exQ24 (x : Fin 3 → ℤ) : exQ24.eval x = 1 * x 0 ^ 2 + 1 * x 1 ^ 2 + 1 * x 2 ^ 2 := by
  simp [exQ24, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ24` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ24 : IntQF.PosDef exQ24 := by
  intro x hx
  refine pos_of_sos (k := 1) (s1 := 1) (s2 := 1) (s3 := 1) (a := x 0) (b := x 1) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ24]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 48$ for `exQ24` (certified enumeration, box size 1). -/
theorem card_aut_exQ24 : Nat.card (Siegel.Aut exQ24) = 48 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ24 (C := !![4, 0, 0; 0, 4, 0; 0, 0, 4]) (D := 8) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, 0, 1; 0, -1, 0], !![-1, 0, 0; 0, 0, -1; 0, 1, 0], !![-1, 0, 0; 0, 0, 1; 0, 1, 0], !![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 0, -1; -1, 0, 0; 0, -1, 0], !![0, 0, 1; -1, 0, 0; 0, -1, 0], !![0, 0, -1; -1, 0, 0; 0, 1, 0], !![0, 0, 1; -1, 0, 0; 0, 1, 0], !![0, 1, 0; -1, 0, 0; 0, 0, -1], !![0, 1, 0; -1, 0, 0; 0, 0, 1], !![0, -1, 0; 0, 0, -1; -1, 0, 0], !![0, -1, 0; 0, 0, 1; -1, 0, 0], !![0, 0, -1; 0, -1, 0; -1, 0, 0], !![0, 0, 1; 0, -1, 0; -1, 0, 0], !![0, 0, -1; 0, 1, 0; -1, 0, 0], !![0, 0, 1; 0, 1, 0; -1, 0, 0], !![0, 1, 0; 0, 0, -1; -1, 0, 0], !![0, 1, 0; 0, 0, 1; -1, 0, 0], !![0, -1, 0; 0, 0, -1; 1, 0, 0], !![0, -1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, -1; 0, -1, 0; 1, 0, 0], !![0, 0, 1; 0, -1, 0; 1, 0, 0], !![0, 0, -1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 1, 0; 0, 0, -1; 1, 0, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, -1, 0; 1, 0, 0; 0, 0, -1], !![0, -1, 0; 1, 0, 0; 0, 0, 1], !![0, 0, -1; 1, 0, 0; 0, -1, 0], !![0, 0, 1; 1, 0, 0; 0, -1, 0], !![0, 0, -1; 1, 0, 0; 0, 1, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, 1], !![1, 0, 0; 0, 0, -1; 0, -1, 0], !![1, 0, 0; 0, 0, 1; 0, -1, 0], !![1, 0, 0; 0, 0, -1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[1, 1, 0], [0, 1, 0], [0, 0, 1]]` (see `eval_exQ12`). -/
def exQ12 : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]]

/-- Helper: the value of the witness form `exQ12` as a polynomial. -/
theorem eval_exQ12 (x : Fin 3 → ℤ) : exQ12.eval x = 1 * x 0 ^ 2 + 1 * x 0 * x 1 + 1 * x 1 ^ 2 + 1 * x 2 ^ 2 := by
  simp [exQ12, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ12` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ12 : IntQF.PosDef exQ12 := by
  intro x hx
  refine pos_of_sos (k := 4) (s1 := 1) (s2 := 3) (s3 := 4) (a := 2 * x 0 + x 1) (b := x 1) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ12]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 24$ for `exQ12` (certified enumeration, box size 1). -/
theorem card_aut_exQ12 : Nat.card (Siegel.Aut exQ12) = 24 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ12 (C := !![4, -2, 0; -2, 4, 0; 0, 0, 3]) (D := 6) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, -1, 0; 0, 1, 0; 0, 0, -1], !![-1, -1, 0; 0, 1, 0; 0, 0, 1], !![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, -1, 0; 1, 0, 0; 0, 0, -1], !![-1, -1, 0; 1, 0, 0; 0, 0, 1], !![-1, 0, 0; 1, 1, 0; 0, 0, -1], !![-1, 0, 0; 1, 1, 0; 0, 0, 1], !![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, -1, 0; 0, 0, -1], !![0, 1, 0; -1, -1, 0; 0, 0, 1], !![0, -1, 0; 1, 1, 0; 0, 0, -1], !![0, -1, 0; 1, 1, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; -1, -1, 0; 0, 0, -1], !![1, 0, 0; -1, -1, 0; 0, 0, 1], !![1, 1, 0; -1, 0, 0; 0, 0, -1], !![1, 1, 0; -1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, -1, 0; 0, 0, -1], !![1, 1, 0; 0, -1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[1, 0, 0], [0, 1, 0], [0, 0, 2]]` (see `eval_exQ8`). -/
def exQ8 : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 1, 0], ![0, 0, 2]]

/-- Helper: the value of the witness form `exQ8` as a polynomial. -/
theorem eval_exQ8 (x : Fin 3 → ℤ) : exQ8.eval x = 1 * x 0 ^ 2 + 1 * x 1 ^ 2 + 2 * x 2 ^ 2 := by
  simp [exQ8, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ8` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ8 : IntQF.PosDef exQ8 := by
  intro x hx
  refine pos_of_sos (k := 1) (s1 := 1) (s2 := 1) (s3 := 2) (a := x 0) (b := x 1) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ8]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 16$ for `exQ8` (certified enumeration, box size 1). -/
theorem card_aut_exQ8 : Nat.card (Siegel.Aut exQ8) = 16 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ8 (C := !![8, 0, 0; 0, 8, 0; 0, 0, 4]) (D := 16) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, -1, 0; -1, 0, 0; 0, 0, 1], !![0, 1, 0; -1, 0, 0; 0, 0, -1], !![0, 1, 0; -1, 0, 0; 0, 0, 1], !![0, -1, 0; 1, 0, 0; 0, 0, -1], !![0, -1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, -1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[3, 1, 1], [0, 3, 1], [0, 0, 3]]` (see `eval_exQ6`). -/
def exQ6 : QuadForm ℤ 3 := QuadForm.ofUpper ![![3, 1, 1], ![0, 3, 1], ![0, 0, 3]]

/-- Helper: the value of the witness form `exQ6` as a polynomial. -/
theorem eval_exQ6 (x : Fin 3 → ℤ) : exQ6.eval x = 3 * x 0 ^ 2 + 1 * x 0 * x 1 + 1 * x 0 * x 2 + 3 * x 1 ^ 2 + 1 * x 1 * x 2 + 3 * x 2 ^ 2 := by
  simp [exQ6, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ6` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ6 : IntQF.PosDef exQ6 := by
  intro x hx
  refine pos_of_sos (k := 420) (s1 := 35) (s2 := 1) (s3 := 1200) (a := 6 * x 0 + x 1 + x 2) (b := 35 * x 1 + 5 * x 2) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ6]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 12$ for `exQ6` (certified enumeration, box size 1). -/
theorem card_aut_exQ6 : Nat.card (Siegel.Aut exQ6) = 12 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ6 (C := !![35, -5, -5; -5, 35, -5; -5, -5, 35]) (D := 200) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![0, -1, 0; -1, 0, 0; 0, 0, -1], !![0, 0, -1; -1, 0, 0; 0, -1, 0], !![0, -1, 0; 0, 0, -1; -1, 0, 0], !![0, 0, -1; 0, -1, 0; -1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[1, 0, 0], [0, 2, 0], [0, 0, 3]]` (see `eval_exQ4`). -/
def exQ4 : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 2, 0], ![0, 0, 3]]

/-- Helper: the value of the witness form `exQ4` as a polynomial. -/
theorem eval_exQ4 (x : Fin 3 → ℤ) : exQ4.eval x = 1 * x 0 ^ 2 + 2 * x 1 ^ 2 + 3 * x 2 ^ 2 := by
  simp [exQ4, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ4` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ4 : IntQF.PosDef exQ4 := by
  intro x hx
  refine pos_of_sos (k := 1) (s1 := 1) (s2 := 2) (s3 := 3) (a := x 0) (b := x 1) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ4]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 8$ for `exQ4` (certified enumeration, box size 1). -/
theorem card_aut_exQ4 : Nat.card (Siegel.Aut exQ4) = 8 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ4 (C := !![24, 0, 0; 0, 12, 0; 0, 0, 8]) (D := 48) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, -1, 0; 0, 0, 1], !![-1, 0, 0; 0, 1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, -1, 0; 0, 0, 1], !![1, 0, 0; 0, 1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[1, 0, 0], [0, 2, 1], [0, 0, 3]]` (see `eval_exQ2`). -/
def exQ2 : QuadForm ℤ 3 := QuadForm.ofUpper ![![1, 0, 0], ![0, 2, 1], ![0, 0, 3]]

/-- Helper: the value of the witness form `exQ2` as a polynomial. -/
theorem eval_exQ2 (x : Fin 3 → ℤ) : exQ2.eval x = 1 * x 0 ^ 2 + 2 * x 1 ^ 2 + 1 * x 1 * x 2 + 3 * x 2 ^ 2 := by
  simp [exQ2, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ2` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ2 : IntQF.PosDef exQ2 := by
  intro x hx
  refine pos_of_sos (k := 8) (s1 := 8) (s2 := 1) (s3 := 23) (a := x 0) (b := 4 * x 1 + x 2) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ2]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 4$ for `exQ2` (certified enumeration, box size 1). -/
theorem card_aut_exQ2 : Nat.card (Siegel.Aut exQ2) = 4 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ2 (C := !![23, 0, 0; 0, 12, -2; 0, -2, 8]) (D := 46) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![-1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: the integral form with upper coefficient matrix `[[2, 0, 1], [0, 3, 1], [0, 0, 2]]` (see `eval_exQ1`). -/
def exQ1 : QuadForm ℤ 3 := QuadForm.ofUpper ![![2, 0, 1], ![0, 3, 1], ![0, 0, 2]]

/-- Helper: the value of the witness form `exQ1` as a polynomial. -/
theorem eval_exQ1 (x : Fin 3 → ℤ) : exQ1.eval x = 2 * x 0 ^ 2 + 1 * x 0 * x 2 + 3 * x 1 ^ 2 + 1 * x 1 * x 2 + 2 * x 2 ^ 2 := by
  simp [exQ1, QuadForm.ofUpper, QuadForm.evalIn, Fin.sum_univ_three]
  ring

/-- Helper: the witness form `exQ1` is positive definite (sum-of-squares identity). -/
theorem posDef_exQ1 : IntQF.PosDef exQ1 := by
  intro x hx
  refine pos_of_sos (k := 24) (s1 := 3) (s2 := 2) (s3 := 43) (a := 4 * x 0 + x 2) (b := 6 * x 1 + x 2) (c := x 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [eval_exQ1]; ring) ?_
  by_contra hcon
  push Not at hcon
  apply hx
  funext i
  fin_cases i <;> simp <;> omega

set_option maxRecDepth 100000 in
/-- Helper: $|\mathrm{Aut}| = 2$ for `exQ1` (certified enumeration, box size 1). -/
theorem card_aut_exQ1 : Nat.card (Siegel.Aut exQ1) = 2 :=
  Siegel.Kneser.card_aut_eq_of_cert posDef_exQ1 (C := !![23, 1, -6; 1, 15, -4; -6, -4, 24]) (D := 86) (B := 1) (by decide) (by norm_num)
    (by decide) [!![-1, 0, 0; 0, -1, 0; 0, 0, -1], !![1, 0, 0; 0, 1, 0; 0, 0, 1]] (by decide) (by decide) (by decide)

/-- Helper: a positive definite integral form is positive definite over $\mathbb Q$ (as a rational form). -/
theorem ratPosDef_map {Q : QuadForm ℤ 3} (hQ : IntQF.PosDef Q) :
    Siegel.RatPosDef (Q.map (Int.castRingHom ℚ)) := by
  intro x hx
  rw [eval_map_cast]
  have hxr : (fun i => (x i : ℝ)) ≠ 0 := by
    intro h; apply hx; funext i
    have := congrFun h i
    simpa using this
  have h1 := hQ.evalIn_real_pos _ hxr
  have h2 : Q.evalIn ℝ (fun i => (x i : ℝ)) = ((Q.evalIn ℚ x : ℚ) : ℝ) := by
    simp only [QuadForm.evalIn, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h2] at h1
  exact_mod_cast h1

/-- **Cassels, Ch. 9, Example 15 (iv), existence half** (p. 165): each of the orders $1, 2, 4, 6, 8, 12, 24$ is the
order of the group of proper integral automorphs of some positive definite rational (indeed integral) ternary form.
Witnesses (variables $x, y, z$): $2x^2 + xz + 3y^2 + yz + 2z^2$ ($1$), $x^2 + 2y^2 + yz + 3z^2$ ($2$),
$x^2 + 2y^2 + 3z^2$ ($4$), $3x^2 + 3y^2 + 3z^2 + xy + xz + yz$ ($6$), $x^2 + y^2 + 2z^2$ ($8$),
$x^2 + xy + y^2 + z^2$ ($12$), $x^2 + y^2 + z^2$ ($24$); each count is a certified enumeration of the full
automorph group (twice the number of proper ones, since $-1$ is improper). -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (iv), p. 165 (all the orders occur)"]
theorem ex15_iv_occur : ∀ n ∈ ({1, 2, 4, 6, 8, 12, 24} : Finset ℕ),
    ∃ f : QuadForm ℚ 3, Siegel.RatPosDef f ∧ Nat.card (RatAutPlus f) = n := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, ratPosDef_map posDef_exQ1, card_ratAutPlus exQ1 1 card_aut_exQ1⟩
  · exact ⟨_, ratPosDef_map posDef_exQ2, card_ratAutPlus exQ2 2 card_aut_exQ2⟩
  · exact ⟨_, ratPosDef_map posDef_exQ4, card_ratAutPlus exQ4 4 card_aut_exQ4⟩
  · exact ⟨_, ratPosDef_map posDef_exQ6, card_ratAutPlus exQ6 6 card_aut_exQ6⟩
  · exact ⟨_, ratPosDef_map posDef_exQ8, card_ratAutPlus exQ8 8 card_aut_exQ8⟩
  · exact ⟨_, ratPosDef_map posDef_exQ12, card_ratAutPlus exQ12 12 card_aut_exQ12⟩
  · exact ⟨_, ratPosDef_map posDef_exQ24, card_ratAutPlus exQ24 24 card_aut_exQ24⟩

/-- **Cassels, Ch. 9, Example 15 (iv), the restriction on the order (statement).** For every positive
definite rational ternary form $f$ the order of the group of proper integral automorphs `RatAutPlus f` is one of
$1, 2, 4, 6, 8, 12, 24$. Proved in `Ch9/Ex15Orders.lean` (`Cassels.Ch9Ex15Orders.ex15ivOrders`) by counting poles
(the fixed axes of the rotations), with (i) (element orders $1, 2, 3, 4, 6$) and (ii) (an element of order $3$
forces an element of order $2$, which excludes the cyclic group of order $3$). -/
@[kb "cassels1978" "Ch. 9, Ex. 15 (iv), p. 165 (only these orders; statement)"]
def Ex15ivOrders : Prop :=
  ∀ f : QuadForm ℚ 3, Siegel.RatPosDef f →
    Nat.card (RatAutPlus f) ∈ ({1, 2, 4, 6, 8, 12, 24} : Finset ℕ)


end Ex15

end QuadFormsKB.Cassels.Ch9Ex6
