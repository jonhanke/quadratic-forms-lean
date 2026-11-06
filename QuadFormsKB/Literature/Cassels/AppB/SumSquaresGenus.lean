/-
# Cassels, Appendix B, §3, p. 377: the genus of a sum of squares contains further classes for $n > 8$

Cassels, *Rational Quadratic Forms* (1978), Appendix B, §3, p. 377, on the genus $\mathcal F_0$ of
$f_0 = x_1^2 + \dots + x_n^2$ (here `sumSq n`, variables $x_0, \dots, x_{n-1}$; Cassels' $x_1, \dots, x_n$ are shifted
by one).

**Convention.** Cassels' forms are classically integral: $f(\mathbf x) = \mathbf x^{\mathsf T} A \mathbf x$ with $A$ an
integral symmetric matrix. The library's `Siegel.e8` has $Q_{E_8}(\mathbf x) = \tfrac12\mathbf x^{\mathsf T} C \mathbf x$
($C$ the Cartan matrix), i.e. it is the half-norm form, whose roots have value $1$. The form with *Gram matrix* $C$,
the norm form of the lattice $E_8$ (roots have value $2$, so $E_8$ has no vector of norm $1$), is
$2\,Q_{E_8}$; it is `e8Gram` below, and $E_8 \perp I_k$ is `e8SumSq k = orthSum e8Gram (sumSq k)`.

**Proved (unconditional).**
* `sameGenus_sumSq_e8SumSq`: for $k \ge 1$, $I_{8+k}$ and $E_8 \perp I_k$ are in the same genus
  (`Siegel.SameGenus`). The proof is the one of `gamma16_sameGenus`: explicit integral $9 \times 9$ matrices $V_d, W_d$
  ($d = 3, 5$) with $I_9(V_d x) = d^2\,(E_8 \perp I_1)(x)$ and $V_dW_d = d^2 I$, found as follows. The lattice
  $\mathbb Z^9$ has the $d$-neighbour $L' = \{x : x \cdot v \equiv 0 \bmod d\} + \mathbb Z\,v/d$ for $v = (1,\dots,1)$,
  $d = 3$, resp. $v = (3,3,1,\dots,1)$, $d = 5$ ($v \cdot v = d^2$); $L'$ is an odd unimodular lattice with exactly two
  vectors of norm $1$, and a search found $E_8$ simple roots in the orthogonal complement of one of them. The columns of
  $V_d/d$ are these roots and the norm-one vector in $\mathbb Z^9$-coordinates. Then $d^{-1}V_d$ is an isometry over
  every commutative ring in which $d$ is a unit: use $d = 3$ over $\mathbb R$ and $\mathbb Z_p$, $p \ne 3$, and
  $d = 5$ over $\mathbb Z_3$. For $k > 1$ add $I_{k-1}$ orthogonally.
* `repNum_e8SumSq_one`, `repNum_sumSq_ne_e8SumSq`: $r_{E_8 \perp I_k}(1) = 2k$, whereas $r_{I_{8+k}}(1) = 2(8+k)$; so
  the two forms are not integrally equivalent.
* `pgenusClasses_sumSq_ne_singleton`: for $n > 8$ the genus of $f_0$ has a proper class besides that of $f_0$.
* `repNum_one_le_of_sameGenus`, `genusRepAvg_sumSq_one_lt`, `exists_repNum_ne_genusRepAvg_sumSq`: every form in the genus
  of $I_n$ has an even Hessian (`two_dvd_hessian_of_sameGenus`, from the $2$-adic equivalence) and hence at most $2n$
  vectors of norm $1$ (`repNum_one_le`); so for $n > 8$ the genus average of $r(1)$ is strictly below $r_{f_0}(1) = 2n$,
  the genus average does not give the number of representations by $f_0$ (p. 378).
* `genusClasses_sumSq_of_le_eight`, `genusRepAvg_sumSq_of_le_eight`: for $n \le 8$ the genus of $I_n$ is the single
  $\mathrm{GL}_n(\mathbb Z)$-class of $I_n$ and the genus average equals $r_{f_0}(m)$ for all $m$. For $n \le 5$ this was
  known (`genusClasses_sumSq`); for $n = 6, 7, 8$ it is deduced from O'Meara's classification of unimodular lattices
  (106:10 and 106:13, `omeara106_10_uncond`, `unimodular_rank8`) by a bridge from `Siegel.SameGenus`
  (`intEquiv_of_sameGenus_sumSq`): a form of the genus is rationally isometric to $I_n$ (Hasse–Minkowski,
  `isometricGL_rat_of_sameGenus`), its lattice is odd unimodular (`isUnimodularZ_glImage_of_sameGenus`,
  `exists_odd_value_of_sameGenus`), hence isometric to $\mathbb Z^n$.

*Not proved here:* the statement for *proper* classes ($n \le 8$, `pgenusClasses (sumSq n) = {pclassOf (sumSq n)}`) is
the same argument as `pgenusClasses_sumSq_of_le_five` of `SumSquares.lean` with `intEquiv_of_sameGenus_sumSq` in place of
`sameGenus_sumSq_intEquiv`; the weight and Magnus' formulas are not touched.
-/
import QuadFormsKB.Literature.Cassels.AppA.Watson
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Siegel.FourSquaresClassNumber
import QuadFormsKB.Siegel.E8
import QuadFormsKB.Siegel.NeighborGenus
import QuadFormsKB.Literature.Cassels.Ch9Sec4
import QuadFormsKB.Literature.OMeara.Sec106Rank9

open Matrix NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel

open QuadFormsKB.DefiniteForms

/-- **$E_8$ as a classically integral form (Gram matrix the Cartan matrix):** $\mathrm{e8Gram}(\mathbf x) =
\mathbf x^{\mathsf T} C \mathbf x = 2\,Q_{E_8}(\mathbf x)$ in 8 variables, where $C$ is the $E_8$ Cartan matrix and
$Q_{E_8}$ is `e8`. Its minimal nonzero value is $2$ (roots), as for the norm form of the lattice $E_8$. -/
def e8Gram : QuadForm ℤ 8 := (2 : ℤ) • e8

/-- **$E_8 \perp I_k$:** the orthogonal sum of `e8Gram` and the sum of $k$ squares, a form in $8 + k$ variables
(the first 8 variables carry $E_8$, the last $k$ carry $I_k$). It is the norm form of the lattice
$E_8 \perp \mathbb Z^k$, odd unimodular. -/
def e8SumSq (k : ℕ) : QuadForm ℤ (8 + k) := QuadForm.orthSum e8Gram (sumSq k)

/-- Helper: evaluation of the sum of squares over any commutative ring. -/
theorem evalIn_sumSq {n : ℕ} {S : Type*} [CommRing S] (x : Fin n → S) :
    (sumSq n).evalIn S x = ∑ i, x i ^ 2 := by
  simp only [sumSq, QuadForm.diag, QuadForm.evalIn, diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp [sq]

/-- Helper: `e8Gram` explicitly, over any commutative ring $S$ (twice the explicit polynomial of `e8_eval`). -/
theorem evalIn_e8Gram {S : Type*} [CommRing S] (x : Fin 8 → S) :
    e8Gram.evalIn S x =
      2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
        - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7) := by
  simp [QuadForm.evalIn, e8Gram, e8, QuadForm.ofUpper, Fin.sum_univ_eight, CartanMatrix.E]
  ring

/-- Helper: the value of $E_8 \perp I_1$ in 9 variables over any commutative ring. -/
theorem evalIn_e8SumSq_one {S : Type*} [CommRing S] (x : Fin 9 → S) :
    (e8SumSq 1).evalIn S x =
      2 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
        - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7) + x 8 ^ 2 := by
  rw [e8SumSq, QuadForm.evalIn_orthSum, evalIn_e8Gram, evalIn_sumSq]
  simp [Fin.castAdd, Fin.natAdd]

/-- Helper: the matrix $V_3$ ($V_3/3$ maps $E_8 \perp I_1$ isometrically onto $I_9$ away from $3$). -/
def nineV3 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-3, 2, 3, -2, 0, 0, 0, 0, -1;
      3, 2, 0, -2, 0, 0, 0, 0, -1;
      0, -1, 0, 1, 0, 0, 0, 0, -1;
      0, 2, -3, 1, 0, 0, 0, 0, -1;
      0, -1, 0, 1, 0, 0, 0, -3, -1;
      0, -1, 0, 1, 0, 0, -3, 3, -1;
      0, -1, 0, 1, 0, -3, 3, 0, -1;
      0, -1, 0, 1, -3, 3, 0, 0, -1;
      0, -1, 0, -2, 3, 0, 0, 0, -1]

/-- Helper: the matrix $W_3$ with $V_3W_3 = 9I$. -/
def nineW3 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-1, 2, 5, -1, -1, -1, -1, -1, -1;
      1, 1, 7, 1, -2, -2, -2, -2, -2;
      1, 1, 10, -2, -2, -2, -2, -2, -2;
      0, 0, 15, 0, -3, -3, -3, -3, -3;
      0, 0, 12, 0, -3, -3, -3, -3, 0;
      0, 0, 9, 0, -3, -3, -3, 0, 0;
      0, 0, 6, 0, -3, -3, 0, 0, 0;
      0, 0, 3, 0, -3, 0, 0, 0, 0;
      -1, -1, -1, -1, -1, -1, -1, -1, -1]

/-- Helper: the matrix $V_5$ ($V_5/5$ maps $E_8 \perp I_1$ isometrically onto $I_9$ away from $5$). -/
def nineV5 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-5, 2, 4, -2, 0, 0, 0, 0, -3;
      5, 2, -1, -2, 0, 0, 0, 0, -3;
      0, -1, -2, 1, 5, -5, 0, 0, -1;
      0, -1, -2, 1, 0, 5, -5, 0, -1;
      0, -1, -2, 1, 0, 0, 5, -5, -1;
      0, -1, -2, 1, 0, 0, 0, 5, -1;
      0, -1, -2, 1, 0, 0, 0, 0, -1;
      0, -6, 3, 1, 0, 0, 0, 0, -1;
      0, -1, -2, 6, -5, 0, 0, 0, -1]

/-- Helper: the matrix $W_5$ with $V_5W_5 = 25I$. -/
def nineW5 : Matrix (Fin 9) (Fin 9) ℤ :=
  !![-2, 3, 1, 1, 1, 1, -9, 1, 1;
      1, 1, 2, 2, 2, 2, -13, -3, 2;
      1, 1, 2, 2, 2, 2, -18, 2, 2;
      0, 0, 5, 5, 5, 5, -25, 0, 5;
      0, 0, 5, 5, 5, 5, -20, 0, 0;
      0, 0, 0, 5, 5, 5, -15, 0, 0;
      0, 0, 0, 0, 5, 5, -10, 0, 0;
      0, 0, 0, 0, 0, 5, -5, 0, 0;
      -3, -3, -1, -1, -1, -1, -1, -1, -1]

/-- Helper: $V_3W_3 = 9I$ (checked by the kernel). -/
theorem nineV3_mul_W3 : nineV3 * nineW3 = (9 : ℤ) • (1 : Matrix (Fin 9) (Fin 9) ℤ) := by
  decide +kernel

/-- Helper: $V_5W_5 = 25I$ (checked by the kernel). -/
theorem nineV5_mul_W5 : nineV5 * nineW5 = (25 : ℤ) • (1 : Matrix (Fin 9) (Fin 9) ℤ) := by
  decide +kernel

/-- Helper: $I_9(V_3\vec x) = 9\,(E_8 \perp I_1)(\vec x)$ over any commutative ring, with $\vec x$ the argument. -/
theorem eval_nineV3{S : Type*} [CommRing S] (x : Fin 9 → S) :
    (sumSq 9).evalIn S (nineV3.map (Int.castRingHom S) *ᵥ x) = 9 * (e8SumSq 1).evalIn S x := by
  rw [evalIn_sumSq, evalIn_e8SumSq_one]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, nineV3]
  ring

/-- Helper: $I_9(V_5\vec x) = 25\,(E_8 \perp I_1)(\vec x)$ over any commutative ring, with $\vec x$ the argument. -/
theorem eval_nineV5{S : Type*} [CommRing S] (x : Fin 9 → S) :
    (sumSq 9).evalIn S (nineV5.map (Int.castRingHom S) *ᵥ x) = 25 * (e8SumSq 1).evalIn S x := by
  rw [evalIn_sumSq, evalIn_e8SumSq_one]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, nineV5]
  ring


/-- Helper: scaling, $Q(s\vec y) = s^2 Q(\vec y)$, for the sum of squares. -/
theorem evalIn_sumSq_smul {n : ℕ} {S : Type*} [CommRing S] (s : S) (y : Fin n → S) :
    (sumSq n).evalIn S (s • y) = s ^ 2 * (sumSq n).evalIn S y := by
  rw [evalIn_sumSq, evalIn_sumSq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_pow]

/-- Helper: from an integral matrix $V$ with $I_9(Vx) = d^2\,(E_8 \perp I_1)(x)$ and a companion $W$ with
$VW = d^2 I$, for $d$ a unit of $S$, the forms $E_8 \perp I_1$ and $I_9$ are isometric over $S$ (via $d^{-1}V$). -/
theorem isoOver_nine_of_V {S : Type*} [CommRing S] (V W : Matrix (Fin 9) (Fin 9) ℤ) (d : ℤ)
    (hd : IsUnit (d : S)) (hVW : V * W = (d * d : ℤ) • (1 : Matrix (Fin 9) (Fin 9) ℤ))
    (hev : ∀ x : Fin 9 → S, (sumSq 9).evalIn S (V.map (Int.castRingHom S) *ᵥ x) =
      ((d : S) * d) * (e8SumSq 1).evalIn S x) :
    IsoOver S (e8SumSq 1) (sumSq 9) := by
  obtain ⟨u, hu⟩ := hd
  have hmul : V.map (Int.castRingHom S) * W.map (Int.castRingHom S) =
      (((d * d : ℤ) : S)) • (1 : Matrix (Fin 9) (Fin 9) S) := by
    rw [← Matrix.map_mul, hVW]
    ext i j
    by_cases h : i = j <;> simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, h, ite_true, ite_false, smul_eq_mul, mul_one, mul_zero, eq_intCast, Int.cast_zero]
  have hui : (↑u⁻¹ : S) * (↑u⁻¹ : S) * ((d : S) * d) = 1 := by
    rw [← hu]
    have : (↑u⁻¹ : S) * (u : S) = 1 := u.inv_mul
    calc (↑u⁻¹ : S) * ↑u⁻¹ * (↑u * ↑u) = ((↑u⁻¹ : S) * ↑u) * ((↑u⁻¹ : S) * ↑u) := by ring
      _ = 1 := by rw [this]; ring
  have h1 : ((↑u⁻¹ : S) • V.map (Int.castRingHom S)) * ((↑u⁻¹ : S) • W.map (Int.castRingHom S)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hmul, smul_smul, Int.cast_mul, hui, one_smul]
  let g : GL (Fin 9) S := ⟨(↑u⁻¹ : S) • V.map (Int.castRingHom S), (↑u⁻¹ : S) • W.map (Int.castRingHom S), h1,
    mul_eq_one_comm.mp h1⟩
  refine ⟨glEquiv g, fun x => ?_⟩
  rw [glEquiv_apply]
  show (sumSq 9).evalIn S (((↑u⁻¹ : S) • V.map (Int.castRingHom S)) *ᵥ x) = _
  rw [Matrix.smul_mulVec, evalIn_sumSq_smul, hev, ← mul_assoc, sq, hui, one_mul]

/-- Helper: $E_8 \perp I_1$ and $I_9$ are isometric over every commutative ring in which $3$ is a unit. -/
theorem isoOver_nine_of_isUnit_three {S : Type*} [CommRing S] (h : IsUnit (3 : S)) :
    IsoOver S (e8SumSq 1) (sumSq 9) := by
  refine isoOver_nine_of_V nineV3 nineW3 3 (by simpa using h) (by rw [nineV3_mul_W3]; norm_num) fun x => ?_
  rw [eval_nineV3]; norm_num

/-- Helper: $E_8 \perp I_1$ and $I_9$ are isometric over every commutative ring in which $5$ is a unit. -/
theorem isoOver_nine_of_isUnit_five {S : Type*} [CommRing S] (h : IsUnit (5 : S)) :
    IsoOver S (e8SumSq 1) (sumSq 9) := by
  refine isoOver_nine_of_V nineV5 nineW5 5 (by simpa using h) (by rw [nineV5_mul_W5]; norm_num) fun x => ?_
  rw [eval_nineV5]; norm_num

/-- Helper: `sumSq (a + b)` is `sumSq a ⊥ sumSq b` up to the identity map. -/
theorem isoOver_sumSq_add {S : Type*} [CommRing S] (a b : ℕ) :
    IsoOver S (sumSq (a + b)) (QuadForm.orthSum (sumSq a) (sumSq b)) := by
  refine ⟨LinearEquiv.refl _ _, fun x => ?_⟩
  rw [QuadForm.evalIn_orthSum, evalIn_sumSq, evalIn_sumSq, evalIn_sumSq, Fin.sum_univ_add]
  rfl

/-- Helper: `sumSq` transported along an equality of the numbers of variables. -/
theorem isoOver_sumSq_cast {S : Type*} [CommRing S] {a b : ℕ} (h : a = b) : IsoOver S (sumSq a) (sumSq b) := by
  subst h; exact IsoOver.refl _

/-- Helper: over a commutative ring in which $3$ or $5$ is a unit, $I_{9+j}$ and $E_8 \perp I_{1+j}$ are
isometric. -/
theorem isoOver_sumSq_e8SumSq_aux {S : Type*} [CommRing S] (h : IsoOver S (e8SumSq 1) (sumSq 9)) (j : ℕ) :
    IsoOver S (sumSq (8 + (1 + j))) (e8SumSq (1 + j)) := by
  have h1 : IsoOver S (sumSq (8 + (1 + j))) (sumSq (9 + j)) := isoOver_sumSq_cast (by omega)
  have h2 : IsoOver S (sumSq (9 + j)) (QuadForm.orthSum (sumSq 9) (sumSq j)) := isoOver_sumSq_add 9 j
  have h3 : IsoOver S (QuadForm.orthSum (sumSq 9) (sumSq j)) (QuadForm.orthSum (e8SumSq 1) (sumSq j)) :=
    IsoOver.orthSum h.symm (IsoOver.refl _)
  have h4 : IsoOver S (QuadForm.orthSum (e8SumSq 1) (sumSq j))
      (QuadForm.orthSum e8Gram (QuadForm.orthSum (sumSq 1) (sumSq j))) := by
    unfold e8SumSq
    exact (IsoOver.assoc e8Gram (sumSq 1) (sumSq j)).symm
  have h5 : IsoOver S (QuadForm.orthSum e8Gram (QuadForm.orthSum (sumSq 1) (sumSq j))) (e8SumSq (1 + j)) :=
    IsoOver.orthSum (IsoOver.refl _) (isoOver_sumSq_add 1 j).symm
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))


/-- Helper: $5$ is a unit of $\mathbb Z_p$ for a prime $p \ne 5$, and $3$ for $p \ne 3$. -/
theorem isUnit_natCast_padic_of_prime_ne {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (h : p ≠ q) :
    IsUnit ((q : ℕ) : ℤ_[p]) :=
  PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes (Fact.out) hq).mpr h))

/-- **$I_{8+k}$ and $E_8 \perp I_k$ are in the same genus** (for $k \ge 1$; Cassels, App. B, §3, p. 377: the genus
$\mathcal F_0$ of $f_0 = x_1^2 + \dots + x_n^2$, $n = 8 + k$, contains the class of $E_8 \perp I_{n-8}$). Here `k` is the
number of squares added to `e8Gram`; the proof uses the explicit isometries of the module docstring (over $\mathbb R$
and $\mathbb Z_p$, $p \ne 3$, away from $3$; over $\mathbb Z_3$, away from $5$). -/
theorem sameGenus_sumSq_e8SumSq {k : ℕ} (hk : 1 ≤ k) : SameGenus (sumSq (8 + k)) (e8SumSq k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
  refine ⟨fun p _ => ?_, ?_⟩
  · by_cases hp : p = 3
    · subst hp
      exact (isoOver_sumSq_e8SumSq_aux (isoOver_nine_of_isUnit_five (by
        simpa using isUnit_natCast_padic_of_prime_ne (p := 3) (q := 5) (by norm_num) (by norm_num))) j).isometricGL
    · exact (isoOver_sumSq_e8SumSq_aux (isoOver_nine_of_isUnit_three (by
        simpa using isUnit_natCast_padic_of_prime_ne (p := p) (q := 3) Nat.prime_three hp)) j).isometricGL
  · exact (isoOver_sumSq_e8SumSq_aux (isoOver_nine_of_isUnit_three (by
      simp)) j).isometricGL

/-- Helper: `e8Gram` is nonnegative on integer vectors and vanishes only at $0$; in particular its values are even
(it is twice a positive definite form). -/
theorem e8Gram_eval (x : Fin 8 → ℤ) : e8Gram.eval x = 2 * e8.eval x := by
  rw [e8_eval]
  simpa [QuadForm.eval] using evalIn_e8Gram x

/-- Helper: the value of $E_8 \perp I_k$ is the sum of the values of its two blocks. -/
theorem eval_e8SumSq {k : ℕ} (x : Fin (8 + k) → ℤ) :
    (e8SumSq k).eval x = e8Gram.eval (fun i => x (Fin.castAdd k i)) + (sumSq k).eval (fun j => x (Fin.natAdd 8 j)) := by
  unfold e8SumSq
  exact QuadForm.evalIn_orthSum ℤ e8Gram (sumSq k) x

/-- Helper: a vector of value $1$ for $E_8 \perp I_k$ has zero $E_8$-block and a norm-one $I_k$-block. -/
theorem e8SumSq_eval_one {k : ℕ} {x : Fin (8 + k) → ℤ} (hx : (e8SumSq k).eval x = 1) :
    (fun i => x (Fin.castAdd k i)) = 0 ∧ (sumSq k).eval (fun j => x (Fin.natAdd 8 j)) = 1 := by
  rw [eval_e8SumSq, e8Gram_eval] at hx
  have hs : 0 ≤ (sumSq k).eval (fun j => x (Fin.natAdd 8 j)) := by
    rw [eval_sumSq]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h0 : 0 ≤ e8.eval (fun i => x (Fin.castAdd k i)) := by
    by_cases hy : (fun i => x (Fin.castAdd k i)) = 0
    · rw [hy]; simp [QuadForm.evalIn]
    · exact (e8_posDef _ hy).le
  have hz : e8.eval (fun i => x (Fin.castAdd k i)) = 0 := by omega
  have hy : (fun i => x (Fin.castAdd k i)) = 0 := by
    by_contra hy
    have := e8_posDef _ hy
    omega
  refine ⟨hy, ?_⟩
  rw [hz] at hx
  omega

/-- **$E_8 \perp I_k$ has exactly $2k$ vectors of norm $1$:** $r_{E_8 \perp I_k}(1) = 2k$ (the $E_8$ block must vanish,
as $E_8$ has no vector of norm $1$, and $r_{I_k}(1) = 2k$). -/
theorem repNum_e8SumSq_one (k : ℕ) : repNum (e8SumSq k) 1 = 2 * k := by
  rw [← repNum_sumSq_one k, repNum, repNum]
  refine Nat.card_congr
    { toFun := fun x => ⟨fun j => x.1 (Fin.natAdd 8 j), (e8SumSq_eval_one x.2).2⟩
      invFun := fun z => ⟨Fin.append (0 : Fin 8 → ℤ) z.1, by
        show (e8SumSq k).eval _ = 1
        rw [eval_e8SumSq]
        have h1 : (fun i : Fin 8 => (Fin.append (0 : Fin 8 → ℤ) z.1 : Fin (8 + k) → ℤ) (Fin.castAdd k i)) = 0 := by
          funext i; simp
        have h2 : (fun j : Fin k => (Fin.append (0 : Fin 8 → ℤ) z.1 : Fin (8 + k) → ℤ) (Fin.natAdd 8 j)) = z.1 := by
          funext j; simp
        rw [h1, h2, e8Gram_eval]
        have : e8.eval (0 : Fin 8 → ℤ) = 0 := by simp [QuadForm.evalIn]
        rw [this]
        have hz : (sumSq k).eval z.1 = 1 := z.2
        omega⟩
      left_inv := fun x => by
        apply Subtype.ext
        have hy := (e8SumSq_eval_one x.2).1
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · simp only [Fin.append_left]
          exact (congrFun hy a).symm
        · simp
      right_inv := fun z => by
        apply Subtype.ext
        funext j
        simp }

/-- **$I_{8+k}$ and $E_8 \perp I_k$ are not integrally equivalent** (for $k \ge 0$): $r_{I_{8+k}}(1) = 2(8+k)$ whereas
$r_{E_8 \perp I_k}(1) = 2k$. -/
theorem not_intEquiv_sumSq_e8SumSq (k : ℕ) : ¬ IntEquiv (sumSq (8 + k)) (e8SumSq k) := by
  intro h
  have := repNum_eq_of_intEquiv h 1
  rw [repNum_sumSq_one, repNum_e8SumSq_one] at this
  omega

/-- **For $n > 8$ the genus of $f_0 = x_1^2 + \dots + x_n^2$ contains further classes** (Cassels, App. B, §3, p. 377),
unconditionally: besides the proper class of $I_n$ it contains that of $E_8 \perp I_{n-8}$ (`e8SumSq`), which is in
the same genus (`sameGenus_sumSq_e8SumSq`) but not integrally equivalent (`not_intEquiv_sumSq_e8SumSq`). Here `n` is the
number of variables and `pgenusClasses` the set of proper classes of the genus. This is the unconditional form of
`pgenusClasses_sumSq_ne_singleton_of_magnus`. -/
@[kb "cassels1978" "App. B, §3, p. 377 (𝓕₀ contains further classes for n > 8)"]
theorem pgenusClasses_sumSq_ne_singleton {n : ℕ} (hn : 8 < n) :
    pgenusClasses (sumSq n) ≠ {pclassOf (sumSq n)} := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 + k := ⟨n - 8, by omega⟩
  intro h
  have hmem : pclassOf (e8SumSq k) ∈ pgenusClasses (sumSq (8 + k)) :=
    ⟨e8SumSq k, rfl, sameGenus_sumSq_e8SumSq (by omega)⟩
  rw [h, Set.mem_singleton_iff, pclassOf_eq_pclassOf_iff] at hmem
  exact not_intEquiv_sumSq_e8SumSq k hmem.intEquiv.symm

/-! ### At most $2n$ vectors of norm $1$ in the genus of $I_n$ -/

section NormOne

variable {n : ℕ}

/-- Helper: $B(\vec x, \vec y) = Q(\vec x + \vec y) - Q(\vec x) - Q(\vec y) = \vec x^{\mathsf T} H \vec y$ for an
integral form $Q$ with Hessian $H$ and integer vectors. -/
theorem polar_int (Q : QuadForm ℤ n) (x y : Fin n → ℤ) :
    Q.eval (x + y) - Q.eval x - Q.eval y = x ⬝ᵥ (Q.hessian *ᵥ y) := by
  simpa using QuadForm.polar_eq_hessian ℤ Q x y

/-- Helper: $Q(-\vec y) = Q(\vec y)$ for integer vectors. -/
theorem eval_neg_int (Q : QuadForm ℤ n) (y : Fin n → ℤ) : Q.eval (-y) = Q.eval y := by
  simp only [QuadForm.eval, QuadForm.evalIn_eq_dotProduct, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct,
    neg_neg]

/-- Helper: evaluation of a base-changed integral form is `evalIn`. -/
theorem map_eval_eq_evalIn_int {S : Type*} [CommRing S] (Q : QuadForm ℤ n) (x : Fin n → S) :
    (Q.map (Int.castRingHom S)).eval x = Q.evalIn S x := by
  simp [QuadForm.map, QuadForm.evalIn]

/-- **Every form in the genus of $I_n$ has an even Hessian** (all entries of $H = C + C^{\mathsf T}$ are even): at the
prime $2$, $H_{ij} = B(\vec e_i, \vec e_j)$ is the polar form of $Q'$, which equals $2\,(g\vec e_i \cdot g\vec e_j)$ for
an isometry $g \in \mathrm{GL}_n(\mathbb Z_2)$ from $I_n$. (So members of the genus are classically integral.)
Here `Q'` is the form in the genus of `sumSq n`, and `i`, `j` index the Hessian entry. -/
theorem two_dvd_hessian_of_sameGenus {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q') (i j : Fin n) :
    2 ∣ Q'.hessian i j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := h.1 2
  have hg' : ∀ x : Fin n → ℤ_[2], (sumSq n).evalIn ℤ_[2] (g.val *ᵥ x) = Q'.evalIn ℤ_[2] x := by
    intro x
    have := hg x
    rwa [map_eval_eq_evalIn_int, map_eval_eq_evalIn_int] at this
  have h1 := QuadForm.polar_eq_hessian ℤ_[2] Q' (Pi.single i 1) (Pi.single j 1)
  have h2 := QuadForm.polar_eq_hessian ℤ_[2] (sumSq n) (g.val *ᵥ Pi.single i 1) (g.val *ᵥ Pi.single j 1)
  rw [← Matrix.mulVec_add] at h2
  simp only [hg'] at h2
  have h3 := h1.symm.trans h2
  have hm : (sumSq n).hessian.map (algebraMap ℤ ℤ_[2]) = (2 : ℤ_[2]) • (1 : Matrix (Fin n) (Fin n) ℤ_[2]) := by
    rw [hessian_sumSq]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hl : Pi.single i (1 : ℤ_[2]) ⬝ᵥ Q'.hessian.map (algebraMap ℤ ℤ_[2]) *ᵥ Pi.single j 1 =
      ((Q'.hessian i j : ℤ) : ℤ_[2]) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hl, hm, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul] at h3
  have h5 := congrArg PadicInt.toZMod h3
  rw [map_intCast, smul_eq_mul, map_mul] at h5
  have h2z : (PadicInt.toZMod (2 : ℤ_[2])) = 0 := by
    have : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [this, map_natCast]
    exact ZMod.natCast_self 2
  rw [h2z, zero_mul] at h5
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (Q'.hessian i j) 2).mp h5

/-- Helper: if all Hessian entries are even, then $B(\vec x, \vec y) = \vec x^{\mathsf T} H \vec y$ is even. -/
theorem two_dvd_bilin {Q : QuadForm ℤ n} (hH : ∀ i j, 2 ∣ Q.hessian i j) (x y : Fin n → ℤ) :
    2 ∣ x ⬝ᵥ (Q.hessian *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
  exact Finset.dvd_sum fun j _ => (hH i j).mul_right _

/-- Helper: $B(\vec y, \vec y) = 2\,Q(\vec y)$ for integer vectors. -/
theorem bilin_self_int (Q : QuadForm ℤ n) (y : Fin n → ℤ) : y ⬝ᵥ (Q.hessian *ᵥ y) = 2 * Q.eval y := by
  have h1 : y ⬝ᵥ (Q.coeffᵀ *ᵥ y) = y ⬝ᵥ (Q.coeff *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have h2 : Q.eval y = y ⬝ᵥ (Q.coeff *ᵥ y) := by
    simpa using QuadForm.evalIn_eq_dotProduct ℤ Q y
  rw [QuadForm.hessian, Matrix.add_mulVec, dotProduct_add, h1, h2]
  ring

/-- Helper: a nonzero integer vector or its negative is lexicographically positive. -/
theorem lex_pos_or_neg {x : Fin n → ℤ} (hx : x ≠ 0) : 0 < toLex x ∨ 0 < toLex (-x) := by
  have : toLex x ≠ 0 := fun h => hx (by simpa using congrArg ofLex h)
  rcases lt_or_gt_of_ne this with h | h
  · right
    have : toLex (-x) = - toLex x := rfl
    rw [this]; exact neg_pos.mpr h
  · left; exact h

/-- Helper: a vector and its negative are not both lexicographically positive. -/
theorem not_lex_pos_and_neg {x : Fin n → ℤ} (hx : 0 < toLex x) (h : 0 < toLex (-x)) : False := by
  have : toLex (-x) = - toLex x := rfl
  rw [this] at h
  exact absurd hx (not_lt.mpr (neg_pos.mp h).le)

/-- Helper: in a positive definite form with even Hessian, two vectors of value $1$ which are neither equal nor
opposite are orthogonal: $B(\vec x, \vec y) = 0$. -/
theorem bilin_eq_zero_of_norm_one {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hH : ∀ i j, 2 ∣ Q.hessian i j)
    {x y : Fin n → ℤ} (hx : Q.eval x = 1) (hy : Q.eval y = 1) (hne : y ≠ x) (hne' : y ≠ -x) :
    x ⬝ᵥ (Q.hessian *ᵥ y) = 0 := by
  have hB := two_dvd_bilin hH x y
  have hp1 := polar_int Q x y
  have hp2 := polar_int Q x (-y)
  rw [Matrix.mulVec_neg, dotProduct_neg, eval_neg_int] at hp2
  have hxy : x + y ≠ 0 := fun h => hne' (by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h)
  have hxy2 : x + -y ≠ 0 := fun h => hne (by
    rw [← sub_eq_add_neg, sub_eq_zero] at h
    exact h.symm)
  have hq1 := hQ _ hxy
  have hq2 := hQ _ hxy2
  generalize x ⬝ᵥ (Q.hessian *ᵥ y) = B at *
  obtain ⟨c, hc⟩ := hB
  omega

/-- **A positive definite form with even Hessian has at most $2n$ vectors of value $1$.** *Proof:* choose the
lexicographically positive half $P$ of the vectors of value $1$ (they come in pairs $\pm\vec x$); distinct elements of $P$
are orthogonal for the polar form $B$ and have $B(\vec x, \vec x) = 2$, hence are linearly independent over $\mathbb Z$,
so $\lvert P \rvert \le n$. Here `Q` is the form, `hQ` its positive definiteness, and `hH` the evenness of the
Hessian entries. -/
theorem repNum_one_le {Q : QuadForm ℤ n} (hQ : IntQF.PosDef Q) (hH : ∀ i j, 2 ∣ Q.hessian i j) :
    repNum Q 1 ≤ 2 * n := by
  classical
  have hfin : (repSet Q 1).Finite := hQ.repSet_finite 1
  set P : Set (Fin n → ℤ) := {x | Q.eval x = 1 ∧ 0 < toLex x} with hP
  have hPfin : P.Finite := hfin.subset fun x hx => hx.1
  have : Finite P := hPfin.to_subtype
  have hne0 : ∀ x : Fin n → ℤ, Q.eval x = 1 → x ≠ 0 := by
    rintro x hx rfl
    simp [QuadForm.evalIn] at hx
  let f : repSet Q 1 → P × Bool := fun x =>
    if h : 0 < toLex x.1 then (⟨x.1, x.2, h⟩, true)
    else (⟨-x.1, by rw [hP]; exact ⟨by rw [eval_neg_int]; exact x.2, (lex_pos_or_neg (hne0 _ x.2)).resolve_left h⟩⟩,
      false)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : 0 < toLex x.1 <;> by_cases hy : 0 < toLex y.1 <;> simp only [f, hx, hy, dite_true, dite_false] at hxy
    · exact Subtype.ext (congrArg (fun p : P × Bool => (p.1 : Fin n → ℤ)) hxy |>.trans rfl)
    · exact absurd (congrArg Prod.snd hxy) (by simp)
    · exact absurd (congrArg Prod.snd hxy) (by simp)
    · exact Subtype.ext (neg_injective (congrArg (fun p : P × Bool => (p.1 : Fin n → ℤ)) hxy))
  have h1 : Nat.card (repSet Q 1) ≤ Nat.card (P × Bool) := Nat.card_le_card_of_injective f hf
  have := hPfin.fintype
  have h2 : Nat.card (P × Bool) = 2 * Nat.card P := by
    rw [Nat.card_prod, mul_comm]
    simp
  have hli : LinearIndependent ℤ (fun x : P => (x.1 : Fin n → ℤ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg y
    have h := congrArg (fun z => (y.1 : Fin n → ℤ) ⬝ᵥ (Q.hessian *ᵥ z)) hg
    simp only [Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Matrix.mulVec_zero, dotProduct_zero] at h
    rw [Finset.sum_eq_single y] at h
    · rw [bilin_self_int, y.2.1] at h
      have : g y * 2 = 0 := by simpa using h
      omega
    · intro x _ hxy
      have hxy' : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      have hx' : x.1 ≠ -y.1 := fun h => not_lex_pos_and_neg y.2.2 (by rw [← h]; exact x.2.2)
      rw [bilin_eq_zero_of_norm_one hQ hH y.2.1 x.2.1 hxy' hx', mul_zero]
    · exact fun h => absurd (Finset.mem_univ y) h
  have h3 : Fintype.card P ≤ n := by
    simpa using hli.fintype_card_le_finrank
  have h4 : Nat.card P = Fintype.card P := Nat.card_eq_fintype_card
  have : repNum Q 1 = Nat.card (repSet Q 1) := rfl
  omega

end NormOne

/-- **Every form in the genus of $I_n$ has at most $2n$ vectors of norm $1$:** $r_{Q'}(1) \le 2n$ for $Q'$ in the
genus of `sumSq n` (positive definiteness is a genus invariant, `SameGenus.posDef`, and the Hessian is even,
`two_dvd_hessian_of_sameGenus`). -/
theorem repNum_one_le_of_sameGenus {n : ℕ} {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q') :
    repNum Q' 1 ≤ 2 * n :=
  repNum_one_le (h.posDef posDef_sumSq) (two_dvd_hessian_of_sameGenus h)

/-- **The genus average of the number of vectors of norm $1$ is below $r_{I_n}(1) = 2n$ for $n > 8$:**
$a(1) < 2n$, because every class in the genus has at most $2n$ such vectors and the class of $E_8 \perp I_{n-8}$ has
only $2(n-8)$ (the weights $1/\lvert\mathrm{Aut}\rvert$ are positive and the genus has finitely many classes). -/
theorem genusRepAvg_sumSq_one_lt {n : ℕ} (hn : 8 < n) : genusRepAvg (sumSq n) 1 < 2 * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 + k := ⟨n - 8, by omega⟩
  have hF := genusFinite (posDef_sumSq (n := 8 + k))
  have hmass := mass_pos (posDef_sumSq (n := 8 + k)) hF
  unfold genusRepAvg
  rw [div_lt_iff₀ hmass, genusRepSum_eq_sum hF, mass_eq_sum hF, Finset.mul_sum]
  have hapos : ∀ c ∈ hF.finite_classes.toFinset, (0 : ℝ) < c.autCard := fun c hc =>
    by exact_mod_cast autCard_pos_of_mem posDef_sumSq ((Set.Finite.mem_toFinset _).mp hc)
  have hE : classOf (e8SumSq k) ∈ hF.finite_classes.toFinset :=
    (Set.Finite.mem_toFinset _).mpr (classOf_mem_genusClasses_iff.mpr (sameGenus_sumSq_e8SumSq (by omega)))
  refine Finset.sum_lt_sum (fun c hc => ?_) ⟨classOf (e8SumSq k), hE, ?_⟩
  · obtain ⟨Q', rfl, hg⟩ := (Set.Finite.mem_toFinset _).mp hc
    have h1 := repNum_one_le_of_sameGenus hg
    have ha := hapos _ hc
    rw [QClass.repNum_classOf, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr ha.le)
    exact_mod_cast h1
  · have ha := hapos _ hE
    rw [QClass.repNum_classOf, repNum_e8SumSq_one, div_eq_mul_inv]
    refine mul_lt_mul_of_pos_right ?_ (inv_pos.mpr ha)
    push_cast
    linarith

/-- **For $n > 8$ the genus average does not give the number of representations by $f_0$** (Cassels, App. B, §3,
p. 378), unconditionally: there is an integer $m$ (namely $m = 1$) with $r_{f_0}(m) \ne a_{\mathcal F_0}(m)$, where
$r_{f_0}(m) = $ `repNum (sumSq n) m` and $a_{\mathcal F_0}(m) = $ `genusRepAvg (sumSq n) m` is the $1/\lvert\mathrm{Aut}\rvert$-weighted
average of the representation numbers over the classes of the genus. Here `n` is the number of variables. For $m = 1$,
$r_{f_0}(1) = 2n$ is the largest value in the genus, attained only by $f_0$ (`genusRepAvg_sumSq_one_lt`). -/
@[kb "cassels1978" "App. B, §3, p. 378 (the genus average gives r_{f₀}(m) for n ≤ 8 but not for n > 8)"]
theorem exists_repNum_ne_genusRepAvg_sumSq {n : ℕ} (hn : 8 < n) :
    ∃ m : ℤ, (repNum (sumSq n) m : ℝ) ≠ genusRepAvg (sumSq n) m := by
  refine ⟨1, fun h => ?_⟩
  have h1 := genusRepAvg_sumSq_one_lt hn
  rw [← h, repNum_sumSq_one] at h1
  push_cast at h1
  exact lt_irrefl _ h1

/-! ### The one-class property for $n \le 8$, from O'Meara's classification of unimodular lattices -/

section Bridge

variable {n : ℕ}

/-- Helper: a vector of $\mathbb Q^n$ lies in $\mathbb Z^n$ (`Lattices.intVec`) iff its coordinates are integers. -/
theorem mem_intVec_int {x : Fin n → ℚ} :
    x ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) ↔ ∀ i, ∃ m : ℤ, x i = m := by
  rw [Lattices.mem_intVec]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((m : ℤ) : 𝓞 ℚ) = a :=
      ⟨Rat.ringOfIntegersEquiv a, (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply a)⟩
    exact ⟨m, by rw [← ha, ← hm]; simp⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : 𝓞 ℚ), by rw [hm]; simp⟩

/-- Helper: the form `sumSqForm n` over $\mathbb Q$ evaluates as the sum of squares. -/
theorem evalIn_sumSqForm (x : Fin n → ℚ) : (Lattices.sumSqForm n).evalIn ℚ x = ∑ i, x i ^ 2 := by
  rw [Lattices.sumSqForm, QuadForm.evalIn_diag]; simp

/-- Helper: the Gram matrix $G = H/2$ of a form in the genus of $I_n$ with respect to the rational isometry $g$ from
$I_n$ (so that $g^{\mathsf T} g = G$) is a symmetric integral matrix of determinant $1$, and the lattice $g\,\mathbb Z^n$
is unimodular for the quadratic space $(\mathbb Q^n, I_n)$. Here `Q'` is the form in the genus of `sumSq n` and `g` the
rational isometry, `(sumSq n)(g x) = Q'(x)`. -/
theorem isUnimodularZ_glImage_of_sameGenus {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q')
    (g : GL (Fin n) ℚ) (hg : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x) :
    Lattices.IsUnimodularZ (Lattices.sumSqForm n) (Lattices.glImage g Lattices.intVec) := by
  -- the Gram matrix
  have hH := Kneser.hessian_eq_conj (Q := sumSq n) (g := g.val) (fun x => (hg x).symm)
  rw [hessian_sumSq] at hH
  have hev : ∀ i j, 2 ∣ Q'.hessian i j := two_dvd_hessian_of_sameGenus h
  let G : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => Q'.hessian i j / 2
  have hG2 : ∀ i j, 2 * G i j = Q'.hessian i j := fun i j => Int.mul_ediv_cancel' (hev i j)
  have e3 : (((2 : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)).map (algebraMap ℤ ℚ)) =
      (2 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hH
  have hGq : G.map (Int.castRingHom ℚ) = g.val.transpose * g.val := by
    ext i j
    have e1 := congrFun (congrFun hH i) j
    have e2 : (Q'.hessian i j : ℚ) = 2 * (G i j : ℚ) := by exact_mod_cast (hG2 i j).symm
    simp only [Matrix.map_apply, eq_intCast, Matrix.smul_apply, smul_eq_mul, algebraMap_int_eq] at e1 ⊢
    rw [e2] at e1
    linarith
  have hGH : Q'.hessian = (2 : ℤ) • G := by
    ext i j; simp [hG2]
  have hGdet : G.det = 1 := by
    have h1 := h.hessian_det_eq
    rw [hessian_sumSq, hGH, Matrix.det_smul, Matrix.det_smul, Matrix.det_one] at h1
    have h2 : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
    simpa [h2] using h1.symm
  have hGsymm : ∀ i j, G i j = G j i := by
    intro i j
    have := hG2 i j
    have h' := hG2 j i
    have hs : Q'.hessian i j = Q'.hessian j i := by
      simp [QuadForm.hessian, add_comm]
    omega
  -- the key product formula
  have hdotQ : ∀ v v' : Fin n → ℚ,
      (g.val *ᵥ v) ⬝ᵥ (g.val *ᵥ v') = ((G.map (Int.castRingHom ℚ)) *ᵥ v) ⬝ᵥ v' := by
    intro v v'
    rw [hGq, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hdot : ∀ y y' : Fin n → ℤ,
      (g.val *ᵥ (fun i => (y i : ℚ))) ⬝ᵥ (g.val *ᵥ (fun i => (y' i : ℚ))) = (((G *ᵥ y) ⬝ᵥ y' : ℤ) : ℚ) := by
    intro y y'
    rw [hdotQ]
    simp [dotProduct, Matrix.mulVec, Matrix.map_apply]
  have hint : ∀ {v : Fin n → ℚ}, v ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) →
      ∃ z : Fin n → ℤ, v = fun i => (z i : ℚ) := by
    intro v hv
    choose z hz using mem_intVec_int.mp hv
    exact ⟨z, funext hz⟩
  unfold Lattices.IsUnimodularZ
  ext x
  constructor
  · intro hx
    have hx' : ∀ y ∈ Lattices.glImage g Lattices.intVec, ∃ m : ℤ, Lattices.bil (Lattices.sumSqForm n) x y / 2 = m := hx
    set w : Fin n → ℚ := g⁻¹.val *ᵥ x with hw
    have hxw : g.val *ᵥ w = x := by
      rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcol : ∀ j, ∃ m : ℤ, ((G.map (Int.castRingHom ℚ)) *ᵥ w) j = m := by
      intro j
      have hej : (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
        rw [mem_intVec_int]
        intro i
        by_cases hij : i = j
        · exact ⟨1, by simp [hij]⟩
        · exact ⟨0, by simp [hij]⟩
      obtain ⟨m, hm⟩ := hx' _ (Lattices.mulVec_mem_glImage (γ := g) hej)
      refine ⟨m, ?_⟩
      rw [DefiniteForms.bil_sumSq, ← hxw, hdotQ, dotProduct_single_one] at hm
      linarith
    choose m hm using hcol
    have hwint : ∀ i, ∃ k : ℤ, w i = k := by
      intro i
      have e : (G.adjugate.map (Int.castRingHom ℚ)) *ᵥ ((G.map (Int.castRingHom ℚ)) *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.adjugate_mul, hGdet, one_smul, Matrix.map_one _ (map_zero _)
          (map_one _), Matrix.one_mulVec]
      refine ⟨∑ j, G.adjugate i j * m j, ?_⟩
      have hmv : (G.map (Int.castRingHom ℚ)) *ᵥ w = fun j => (m j : ℚ) := funext hm
      rw [hmv] at e
      rw [← congrFun e i]
      simp [Matrix.mulVec, dotProduct]
    exact ⟨w, mem_intVec_int.mpr hwint, hxw⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Lattices.mem_glImage.mp hx
    obtain ⟨z, rfl⟩ := hint hy
    intro y' hy'
    obtain ⟨v, hv, rfl⟩ := Lattices.mem_glImage.mp hy'
    obtain ⟨z', rfl⟩ := hint hv
    refine ⟨(G *ᵥ z) ⬝ᵥ z', ?_⟩
    rw [DefiniteForms.bil_sumSq, hdot]
    ring

/-- Helper: if $\sigma$ is a rational isometry of $I_n$ with $\sigma\mathbb Z^n = g\mathbb Z^n$ and
$(I_n)(g\vec x) = Q'(\vec x)$, then $Q'$ is integrally equivalent to $I_n$ (via $\sigma^{-1}g \in \mathrm{GL}_n(\mathbb Z)$).
Here `g` is the rational basis change, `σ` the isometry, `hσ` its membership in the orthogonal group of
`Lattices.sumSqForm n`, `hL` the equality of lattices and `hg` the isometry property of `g`. -/
theorem intEquiv_of_glImage_eq {Q' : QuadForm ℤ n} (g σ : GL (Fin n) ℚ)
    (hσ : σ ∈ Lattices.orthGroup (Lattices.sumSqForm n) ℚ)
    (hL : Lattices.glImage σ Lattices.intVec = Lattices.glImage g Lattices.intVec)
    (hg : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x) : IntEquiv (sumSq n) Q' := by
  set U : GL (Fin n) ℚ := σ⁻¹ * g with hU
  have hU1 : Lattices.glImage U Lattices.intVec = Lattices.intVec := by
    rw [hU, Lattices.glImage_mul, ← hL, ← Lattices.glImage_mul, inv_mul_cancel, Lattices.glImage_one]
  have hU2 : Lattices.glImage U⁻¹ Lattices.intVec = Lattices.intVec := by
    rw [hU, _root_.mul_inv_rev, inv_inv, Lattices.glImage_mul, hL, ← Lattices.glImage_mul, inv_mul_cancel,
      Lattices.glImage_one]
  have hcol : ∀ (V : GL (Fin n) ℚ), Lattices.glImage V Lattices.intVec = Lattices.intVec →
      ∃ A : Matrix (Fin n) (Fin n) ℤ, A.map (Int.castRingHom ℚ) = V.val := by
    intro V hV
    have : ∀ i j, ∃ m : ℤ, V.val i j = m := by
      intro i j
      have hej : (Pi.single j (1 : ℚ) : Fin n → ℚ) ∈ (Lattices.intVec : Submodule (𝓞 ℚ) (Fin n → ℚ)) := by
        rw [mem_intVec_int]
        intro k
        by_cases hkj : k = j
        · exact ⟨1, by simp [hkj]⟩
        · exact ⟨0, by simp [hkj]⟩
      have := mem_intVec_int.mp (hV ▸ Lattices.mulVec_mem_glImage (γ := V) hej) i
      simpa [Matrix.mulVec_single_one] using this
    choose A hA using this
    exact ⟨Matrix.of A, by ext i j; simp [hA]⟩
  obtain ⟨A, hA⟩ := hcol U hU1
  obtain ⟨B, hB⟩ := hcol U⁻¹ hU2
  have hAB : A * B = 1 := by
    have h : (A * B).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective h
  have hBA : B * A = 1 := by
    have h : (B * A).map (Int.castRingHom ℚ) = (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ) := by
      rw [Matrix.map_mul, hA, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    exact Matrix.map_injective (f := (Int.castRingHom ℚ : ℤ → ℚ)) Int.cast_injective h
  refine ⟨⟨A, B, hAB, hBA⟩, fun x => ?_⟩
  apply Int.cast_injective (α := ℚ)
  show (((sumSq n).eval (A *ᵥ x) : ℤ) : ℚ) = ((Q'.eval x : ℤ) : ℚ)
  rw [← evalIn_intCast, ← evalIn_intCast]
  have hv : (fun i => ((A *ᵥ x) i : ℚ)) = U.val *ᵥ (fun i => (x i : ℚ)) := by
    rw [← hA]
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [hv, hU, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hinv : σ⁻¹ ∈ Lattices.orthGroup (Lattices.sumSqForm n) ℚ := Subgroup.inv_mem _ hσ
  have := Lattices.evalIn_mulVec_of_mem (Lattices.sumSqForm n) hinv (g.val *ᵥ fun i => (x i : ℚ))
  rw [evalIn_sumSq, ← evalIn_sumSqForm, this, evalIn_sumSqForm, ← evalIn_sumSq, hg]

/-- **A form in the genus of $I_n$ ($n \ge 1$) takes an odd value** on $\mathbb Z^n$ (the genus of $I_n$ is odd):
if all values of $Q'$ were even, then every column of the $2$-adic isometry $g \in \mathrm{GL}_n(\mathbb Z_2)$ from $I_n$
would have an even sum of squares, hence an even coordinate sum, so $\mathbf 1^{\mathsf T}\bar g = 0$ modulo $2$,
contradicting the invertibility of $\bar g$. -/
theorem exists_odd_value_of_sameGenus (hn : 1 ≤ n) {Q' : QuadForm ℤ n} (h : SameGenus (sumSq n) Q') :
    ∃ x : Fin n → ℤ, ¬ 2 ∣ Q'.eval x := by
  by_contra hall
  push Not at hall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := h.1 2
  have hg' : ∀ x : Fin n → ℤ_[2], (sumSq n).evalIn ℤ_[2] (g.val *ᵥ x) = Q'.evalIn ℤ_[2] x := by
    intro x
    have := hg x
    rwa [map_eval_eq_evalIn_int, map_eval_eq_evalIn_int] at this
  let f : ℤ_[2] →+* ZMod 2 := PadicInt.toZMod
  -- the columns of `g` have even coordinate sum modulo 2
  have hcol : ∀ i : Fin n, ∑ k, f (g.val k i) = 0 := by
    intro i
    have h1 := hg' (fun k => ((Pi.single i (1 : ℤ) : Fin n → ℤ) k : ℤ_[2]))
    rw [evalIn_intCast] at h1
    have hv : g.val *ᵥ (fun k => ((Pi.single i (1 : ℤ) : Fin n → ℤ) k : ℤ_[2])) = fun k => g.val k i := by
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, evalIn_sumSq] at h1
    have h2 := congrArg f h1
    obtain ⟨t, ht⟩ := hall (Pi.single i 1)
    rw [map_sum] at h2
    simp only [map_pow, map_intCast, ht] at h2
    have h3 : ∀ k, f (g.val k i) ^ 2 = f (g.val k i) := fun k => by
      rw [sq]
      have := ZMod.pow_card (f (g.val k i))
      rwa [sq] at this
    simp only [h3] at h2
    rw [h2]
    push_cast
    have : (2 : ZMod 2) = 0 := by exact_mod_cast ZMod.natCast_self 2
    rw [this, zero_mul]
  have hinv : (g.val.map f) * ((g⁻¹).val.map f) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hzero : (fun _ : Fin n => (1 : ZMod 2)) ᵥ* (g.val.map f) = 0 := by
    funext i
    simpa [Matrix.vecMul, dotProduct] using hcol i
  have h0 : (fun _ : Fin n => (1 : ZMod 2)) ᵥ* ((g.val.map f) * ((g⁻¹).val.map f)) = 0 := by
    rw [← Matrix.vecMul_vecMul, hzero, Matrix.zero_vecMul]
  rw [hinv, Matrix.vecMul_one] at h0
  have := congrFun h0 ⟨0, hn⟩
  simp at this

/-- **The odd unimodular lattices of rank $n \le 8$ are integral forms equivalent to $I_n$** (the one-class property for
the genus of $I_n$, from O'Meara's classification of unimodular lattices, §106, 106:10 for $n \le 7$ and 106:13 for
$n = 8$). Let $Q'$ be in the genus of $I_n$, $1 \le n \le 8$. A rational isometry $g$ from $I_n$ to $Q'$ exists by the
Hasse–Minkowski theorem (`isometricGL_rat_of_sameGenus`); the lattice $g\mathbb Z^n \subset (\mathbb Q^n, I_n)$ is
unimodular (`isUnimodularZ_glImage_of_sameGenus`, using that the Hessian of a form in the genus is even with
determinant $2^n$), so is isometric to $\mathbb Z^n$ by O'Meara (for $n = 8$ the other possibility, the lattice $E$, is
even, whereas $Q'$ takes an odd value, `exists_odd_value_of_sameGenus`), and a rational isometry
carrying $\mathbb Z^n$ onto $g\mathbb Z^n$ composed with $g^{-1}$ is the required element of $\mathrm{GL}_n(\mathbb Z)$
(`intEquiv_of_glImage_eq`). Here `n` is the number of variables and `Q'` the form in the genus. -/
@[kb "cassels1978" "App. B, §3, p. 377 (one class for n ≤ 8)"]
theorem intEquiv_of_sameGenus_sumSq (hn1 : 1 ≤ n) (hn8 : n ≤ 8) {Q' : QuadForm ℤ n}
    (h : SameGenus (sumSq n) Q') : IntEquiv (sumSq n) Q' := by
  have hd0 : (sumSq n).hessian.det ≠ 0 := by
    rw [hessian_sumSq, Matrix.det_smul, Matrix.det_one]
    simp
  obtain ⟨g, hg⟩ := Lattices.isometricGL_rat_of_sameGenus (sumSq n) Q' h.hessian_det_eq hd0 h
  have hg' : ∀ x : Fin n → ℚ, (sumSq n).evalIn ℚ (g.val *ᵥ x) = Q'.evalIn ℚ x := by
    intro x
    have := hg x
    rwa [map_eval_eq_evalIn_int, map_eval_eq_evalIn_int] at this
  have hU := isUnimodularZ_glImage_of_sameGenus h g hg'
  let L : Lattices.Lat ℚ n :=
    ⟨Lattices.glImage g Lattices.intVec, Lattices.glImage_isLattice g Lattices.intVec_isLattice⟩
  have hL : Lattices.IsUnimodularZ (Lattices.sumSqForm n) L.1 := hU
  have key : ∃ σ ∈ Lattices.orthGroup (Lattices.sumSqForm n) ℚ,
      Lattices.glImage σ Lattices.intVec = Lattices.glImage g Lattices.intVec := by
    by_cases h7 : n ≤ 7
    · exact Lattices.omeara106_10_uncond hn1 h7 hL
    · have h8 : n = 8 := by omega
      subst h8
      rcases Lattices.unimodular_rank8 L hL with hD | hE
      · exact hD
      · exfalso
        obtain ⟨γ, hγ, hγE⟩ := hE
        obtain ⟨x, hx⟩ := exists_odd_value_of_sameGenus hn1 h
        have hmem : g.val *ᵥ (fun i => (x i : ℚ)) ∈ L.1 :=
          Lattices.mulVec_mem_glImage (γ := g) (mem_intVec_int.mpr fun i => ⟨x i, rfl⟩)
        rw [← hγE] at hmem
        obtain ⟨e, he, hee⟩ := Lattices.mem_glImage.mp hmem
        obtain ⟨m, hm⟩ := Lattices.omearaE_even (by norm_num) le_rfl e he
        have h1 := Lattices.evalIn_mulVec_of_mem (Lattices.sumSqForm 8) hγ e
        rw [hee] at h1
        have h2 : Q'.evalIn ℚ (fun i => (x i : ℚ)) = (Q'.eval x : ℚ) := evalIn_intCast Q' x
        have h3 : (Lattices.sumSqForm 8).evalIn ℚ (g.val *ᵥ fun i => (x i : ℚ)) = (Q'.eval x : ℚ) := by
          rw [← h2, ← hg', evalIn_sumSq, evalIn_sumSqForm]
        rw [h1] at h3
        have h4 : (Q'.eval x : ℚ) = ((2 * m : ℤ) : ℚ) := by
          have hm' : (Lattices.sumSqForm 8).evalIn ℚ e = 2 * m := hm
          rw [← h3, hm']; push_cast; ring
        exact hx ⟨m, by exact_mod_cast h4⟩
  obtain ⟨σ, hσ, hσL⟩ := key
  exact intEquiv_of_glImage_eq g σ hσ hσL hg'

end Bridge

/-- **The genus of $f_0 = x_1^2 + \dots + x_n^2$ consists of one class for $n \le 8$** (Cassels, App. B, §3, p. 377),
unconditionally: `genusClasses (sumSq n)` $= \{[I_n]\}$ for every $n \le 8$ (the cases $n \le 5$ are
`genusClasses_sumSq`, Hermite's bound; the cases $n = 6, 7, 8$ come from O'Meara's classification of unimodular lattices
through `intEquiv_of_sameGenus_sumSq`). Here `n` is the number of variables; `genusClasses` is the set of
$\mathrm{GL}_n(\mathbb Z)$-classes in the genus. This replaces the named statement `MagnusSumSquares` (`le_eight`) for
the one-class conclusion. -/
@[kb "cassels1978" "App. B, §3, p. 377 (one class for n ≤ 8)"]
theorem genusClasses_sumSq_of_le_eight {n : ℕ} (hn : n ≤ 8) :
    genusClasses (sumSq n) = {classOf (sumSq n)} := by
  by_cases h5 : n ≤ 5
  · exact genusClasses_sumSq h5
  · have hn1 : 1 ≤ n := by omega
    ext c
    induction c using Quotient.inductionOn with
    | h Q' =>
      change classOf Q' ∈ _ ↔ classOf Q' ∈ _
      rw [classOf_mem_genusClasses_iff, Set.mem_singleton_iff]
      constructor
      · intro hg
        exact classOf_eq_classOf_iff.mpr (intEquiv_of_sameGenus_sumSq hn1 hn hg).symm
      · intro he
        exact (classOf_mem_genusClasses_iff).mp (he ▸ classOf_self_mem_genusClasses _)

/-- **For $n \le 8$ the genus average gives the number of representations by $f_0$, for every $m$** (Cassels, App. B,
§3, p. 378): $a_{\mathcal F_0}(m) = r_{f_0}(m)$, because the genus of $f_0$ has one class
(`genusClasses_sumSq_of_le_eight`). Here `genusRepAvg` is the weighted genus average and `repNum` the number of
representations. The converse for $n > 8$ is `exists_repNum_ne_genusRepAvg_sumSq`. -/
@[kb "cassels1978" "App. B, §3, p. 378 (the genus average gives r_{f₀}(m) for n ≤ 8 but not for n > 8), here n ≤ 8"]
theorem genusRepAvg_sumSq_of_le_eight {n : ℕ} (hn : n ≤ 8) (m : ℤ) :
    genusRepAvg (sumSq n) m = repNum (sumSq n) m :=
  genusRepAvg_of_classNumber_one posDef_sumSq (genusClasses_sumSq_of_le_eight hn) m

end QuadFormsKB.Siegel
