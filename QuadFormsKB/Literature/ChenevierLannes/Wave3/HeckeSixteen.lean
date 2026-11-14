/-
# Chenevier–Lannes, §1.3 and §3.2: the operators $T_p$ on functions on $X_n$; commutation on $X_8$, $X_{16}$

Source: Chenevier–Lannes 2019 (`chenevierlannes2019`), §1.3, p. 6 ("The $T_p$ commute and are self-adjoint for a
suitable inner product on $\mathbb{R}[X_n]$"), §3.2, pp. 55–57 (Remarks: $T_A$ and $T_B$ commute, proved in
Chapter 4; Proposition 3.2.3; "for $n = 8, 16, 24$, the eigenvalues of $T_d$ are integers … nearly as trivial for
$n = 16$ because we have $|X_{16}| = 2$ and we already know one integral eigenvalue, namely $c_{16}(d)$"). Printed
page numbers.

**Layer.** $T_p$ on functions $f : X_n \to R$, $(T_pf)(x) = \sum_{y \in X_n} N_p(x, y) f(y)$ (`heckeT`), the
dual of the book's $T_p$ on $\mathbb{Z}[X_n]$ (matrix entries $N_p(x, y)$ = `nbNum p x y`).

**Proves** ($p$, $q$ odd primes; unconditional):
- `heckeT_selfAdjoint` (Proposition 3.2.3 on functions, every $n$): $\sum_x (T_pf)(x)\,g(x)/|O(x)| =
  \sum_x f(x)\,(T_pg)(x)/|O(x)|$;
- `heckeT_comm_eight`, `heckeT_comm_sixteen`: $T_pT_q = T_qT_p$ on functions on $X_8$ and on $X_{16}$;
- `heckeT_sixteen_const`, `heckeT_sixteen_eigen`: on $X_{16}$ the constant function $1$ is an eigenvector with eigenvalue
  $c_{16}(p)$, and the function $f$ with $f(E_8 \oplus E_8) = 405$, $f(E_{16}) = -286$ is an eigenvector with the
  integral eigenvalue $c_{16}(p) - N_p(E_8 \oplus E_8, E_{16}) - N_p(E_{16}, E_8 \oplus E_8)$.

**States** (named): `HeckeCommute n`, the commutation of all $T_p$, $T_q$ on functions on $X_n$ (the Remarks of §3.2,
proved in the book in Chapter 4 through the commutativity of the Hecke ring); proved here for $n = 8, 16$ and odd
$p, q$ (`heckeCommute_eight_odd`, `heckeCommute_sixteen_odd`).
-/
import QuadFormsKB.Literature.ChenevierLannes.Wave2.Consequences

open Matrix

namespace QuadFormsKB.ChenevierLannes

open QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser QuadFormsKB.Lattices

variable {n : ℕ}

/-! ### Helpers -/

private theorem nbCount_out {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q Q' R : QuadForm ℤ n}
    (hQ : IsEvenUnimodular Q) (hQ' : IsEvenUnimodular Q') (hR : IsEvenUnimodular R)
    (hc : classOf Q = classOf Q') : nbCount Q p (classOf R) = nbCount Q' p (classOf R) := by
  have h1 := nbCount_mul_autCard hp2 hQ.posDef hR.posDef (not_dvd_det hQ p) (not_dvd_det hR p)
  have h2 := nbCount_mul_autCard hp2 hQ'.posDef hR.posDef (not_dvd_det hQ' p) (not_dvd_det hR p)
  rw [← hc] at h2
  have hA : Nat.card (Aut Q) = Nat.card (Aut Q') := by
    have : (classOf Q).autCard = (classOf Q').autCard := by rw [hc]
    exact this
  exact Nat.eq_of_mul_eq_mul_right hR.posDef.card_aut_pos (h1.trans (by rw [hA]; exact h2.symm))

private theorem nbNum_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q R : QuadForm ℤ n}
    (hQ : IsEvenUnimodular Q) (hR : IsEvenUnimodular R) :
    nbNum p (classOf Q) (classOf R) = nbCount Q p (classOf R) := by
  unfold nbNum
  have hx : classOf Q ∈ classSet n := mem_classSet_classOf.mpr hQ
  exact nbCount_out hp2 (out_isEvenUnimodular hx) hQ hR (Quotient.out_eq _)

private theorem classes_ne : classOf twoE8 ≠ classOf gamma16 := fun he =>
  gamma16_not_isometric (IsometricGL.symm (classOf_eq_classOf_iff.mp he))

open Classical in
private theorem toFinset_sixteen :
    (classSet_finite 16).toFinset = {classOf twoE8, classOf gamma16} := by
  have h : classSet 16 = {classOf twoE8, classOf gamma16} := wittRankSixteen
  ext c
  simp [h]

open Classical in
private theorem heckeT_A {R : Type*} [AddCommMonoid R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : QClass 16 → R) :
    heckeT p f (classOf twoE8) = nbCount twoE8 p (classOf twoE8) • f (classOf twoE8) +
      nbCount twoE8 p (classOf gamma16) • f (classOf gamma16) := by
  unfold heckeT
  rw [toFinset_sixteen, Finset.sum_pair classes_ne,
    nbNum_eq hp2 isEvenUnimodular_twoE8 isEvenUnimodular_twoE8,
    nbNum_eq hp2 isEvenUnimodular_twoE8 isEvenUnimodular_gamma16]

open Classical in
private theorem heckeT_B {R : Type*} [AddCommMonoid R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : QClass 16 → R) :
    heckeT p f (classOf gamma16) = nbCount gamma16 p (classOf twoE8) • f (classOf twoE8) +
      nbCount gamma16 p (classOf gamma16) • f (classOf gamma16) := by
  unfold heckeT
  rw [toFinset_sixteen, Finset.sum_pair classes_ne,
    nbNum_eq hp2 isEvenUnimodular_gamma16 isEvenUnimodular_twoE8,
    nbNum_eq hp2 isEvenUnimodular_gamma16 isEvenUnimodular_gamma16]

private theorem mem_sixteen {x : QClass 16} (hx : x ∈ classSet 16) :
    x = classOf twoE8 ∨ x = classOf gamma16 := by
  have h : classSet 16 = {classOf twoE8, classOf gamma16} := wittRankSixteen
  rw [h] at hx
  exact hx

private theorem comb_smul {R : Type*} [AddCommMonoid R] (a b c d e f : ℕ) (x y : R) :
    a • (c • x + d • y) + b • (e • x + f • y) = (a * c + b * e) • x + (a * d + b * f) • y := by
  simp only [smul_add, smul_smul, add_smul]
  abel

private theorem coef_identities (a b u v a' b' u' v' c c' : ℕ) (h1 : u + a = c) (h2 : b + v = c)
    (h1' : u' + a' = c') (h2' : b' + v' = c') (hx : a * b' = a' * b) :
    (u * u' + a * b' = u' * u + a' * b) ∧ (u * a' + a * v' = u' * a + a' * v) ∧
    (b * u' + v * b' = b' * u + v' * b) ∧ (b * a' + v * v' = b' * a + v' * v) := by
  have z1 : (u : ℤ) + a = c := by exact_mod_cast h1
  have z2 : (b : ℤ) + v = c := by exact_mod_cast h2
  have z1' : (u' : ℤ) + a' = c' := by exact_mod_cast h1'
  have z2' : (b' : ℤ) + v' = c' := by exact_mod_cast h2'
  have zx : (a : ℤ) * b' = a' * b := by exact_mod_cast hx
  refine ⟨?_, ?_, ?_, ?_⟩ <;> zify
  · linear_combination zx
  · linear_combination (a' : ℤ) * z1 + (a : ℤ) * z2' - (a : ℤ) * z1' - (a' : ℤ) * z2 - zx
  · linear_combination (b : ℤ) * z1' + (b' : ℤ) * z2 - (b' : ℤ) * z1 - (b : ℤ) * z2' + zx
  · linear_combination (-1 : ℤ) * zx

private theorem cross_sixteen {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    nbCount twoE8 p (classOf gamma16) * nbCount gamma16 q (classOf twoE8) =
      nbCount twoE8 q (classOf gamma16) * nbCount gamma16 p (classOf twoE8) := by
  have hp := nbCount_gamma16_twoE8_mul hp2
  have hq := nbCount_gamma16_twoE8_mul hq2
  have zp : (405 : ℤ) * nbCount gamma16 p (classOf twoE8) = 286 * nbCount twoE8 p (classOf gamma16) := by
    exact_mod_cast hp
  have zq : (405 : ℤ) * nbCount gamma16 q (classOf twoE8) = 286 * nbCount twoE8 q (classOf gamma16) := by
    exact_mod_cast hq
  have : ((nbCount twoE8 p (classOf gamma16) * nbCount gamma16 q (classOf twoE8) : ℕ) : ℤ) =
      ((nbCount twoE8 q (classOf gamma16) * nbCount gamma16 p (classOf twoE8) : ℕ) : ℤ) := by
    apply mul_left_cancel₀ (show (405 : ℤ) ≠ 0 by norm_num)
    push_cast
    linear_combination (nbCount twoE8 p (classOf gamma16) : ℤ) * zq - (nbCount twoE8 q (classOf gamma16) : ℤ) * zp
  exact_mod_cast this

/-- **Proposition 3.2.3 on functions** (Chenevier–Lannes, p. 56; $p$ odd): $T_p$ is self-adjoint for the inner product
$\langle f, g\rangle = \sum_{x \in X_n} f(x)\,g(x)/|O(x)|$ on functions $X_n \to K$ ($K$ a field of characteristic $0$);
the dual statement of $(x \mid y) = |O(x)|\,\delta_{x,y}$ on $\mathbb{Z}[X_n]$. Unconditional (`nbNum_mul_autCard`). -/
@[kb "chenevierlannes2019" "Prop. 3.2.3, p. 56; §1.3, p. 6 (T_p self-adjoint, odd p)"]
theorem heckeT_selfAdjoint {K : Type*} [Field K] [CharZero K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (f g : QClass n → K) :
    ∑ x ∈ (classSet_finite n).toFinset, heckeT p f x * g x / x.autCard =
      ∑ x ∈ (classSet_finite n).toFinset, f x * heckeT p g x / x.autCard := by
  have hpos : ∀ x ∈ classSet n, (x.autCard : K) ≠ 0 := fun x hx => by
    have h := (out_isEvenUnimodular hx).posDef.card_aut_pos
    rw [autCard_eq_out x]
    exact_mod_cast h.ne'
  simp only [heckeT, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o ho => Finset.sum_congr rfl fun i hi => ?_
  have ho' := (Set.Finite.mem_toFinset _).mp ho
  have hi' := (Set.Finite.mem_toFinset _).mp hi
  have h := nbNum_mul_autCard hp2 ho' hi'
  have hK : (nbNum p o i : K) * i.autCard = nbNum p i o * o.autCard := by exact_mod_cast h
  rw [div_eq_div_iff (hpos o ho') (hpos i hi')]
  linear_combination (f i * g o) * hK

/-- **The Hecke operators commute on $X_n$** (Chenevier–Lannes, §1.3, p. 6, and Remarks in §3.2, p. 55, proved in
Chapter 4; named statement): for all primes $p, q$ and every function $f : X_n \to \mathbb{C}$,
$T_p(T_qf) = T_q(T_pf)$ on $X_n$. -/
@[kb "chenevierlannes2019" "§1.3, p. 6; §3.2, p. 55 (the T_p commute)"]
def HeckeCommute (n : ℕ) : Prop :=
  ∀ (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (f : QClass n → ℂ), ∀ x ∈ classSet n,
    heckeT p (heckeT q f) x = heckeT q (heckeT p f) x

/-- **$T_p$ and $T_q$ commute on $X_8$** ($p, q$ odd): $X_8 = \{E_8\}$ and $T_p = c_8(p)$ (`heckeT_eight`).
Unconditional. -/
@[kb "chenevierlannes2019" "§3.2, p. 55 (commutation, n = 8, odd p, q)"]
theorem heckeT_comm_eight {R : Type*} [AddCommMonoid R] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (f : QClass 8 → R) {x : QClass 8} (hx : x ∈ classSet 8) :
    heckeT p (heckeT q f) x = heckeT q (heckeT p f) x := by
  have h8 : classSet 8 = {classOf e8} := mordellRankEight
  rw [h8, Set.mem_singleton_iff] at hx
  subst hx
  simp only [heckeT_eight hp2, heckeT_eight hq2, smul_smul]
  rw [mul_comm]

/-- **$T_p$ and $T_q$ commute on $X_{16}$** ($p, q$ odd; Chenevier–Lannes, §3.2, p. 55). *Proof:* $X_{16}$ has two
elements (`wittRankSixteen`); with $a_p = N_p(E_8 \oplus E_8, E_{16})$, $b_p = N_p(E_{16}, E_8 \oplus E_8)$ the matrix
of $T_p$ is $\begin{pmatrix}c_{16}(p) - a_p & a_p\\ b_p & c_{16}(p) - b_p\end{pmatrix}$ (Proposition 3.2.2), and
$286\,a_p = 405\,b_p$ (Scholium 3.1.7), from which the two matrices commute. Unconditional. -/
@[kb "chenevierlannes2019" "§3.2, p. 55 (commutation, n = 16, odd p, q)"]
theorem heckeT_comm_sixteen {R : Type*} [AddCommMonoid R] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (f : QClass 16 → R) {x : QClass 16} (hx : x ∈ classSet 16) :
    heckeT p (heckeT q f) x = heckeT q (heckeT p f) x := by
  have hP := nbCount_sixteen_add_uncond hp2
  have hQ := nbCount_sixteen_add_uncond hq2
  have hx' := cross_sixteen hp2 hq2
  obtain ⟨e1, e2, e3, e4⟩ := coef_identities (nbCount twoE8 p (classOf gamma16))
    (nbCount gamma16 p (classOf twoE8)) (nbCount twoE8 p (classOf twoE8)) (nbCount gamma16 p (classOf gamma16))
    (nbCount twoE8 q (classOf gamma16)) (nbCount gamma16 q (classOf twoE8)) (nbCount twoE8 q (classOf twoE8))
    (nbCount gamma16 q (classOf gamma16)) (cn 16 p) (cn 16 q) hP.1 hP.2 hQ.1 hQ.2 hx'
  rcases mem_sixteen hx with rfl | rfl
  · simp only [heckeT_A hp2, heckeT_B hp2, heckeT_A hq2, heckeT_B hq2]
    rw [comb_smul, comb_smul, e1, e2]
  · simp only [heckeT_A hp2, heckeT_B hp2, heckeT_A hq2, heckeT_B hq2]
    rw [comb_smul, comb_smul, e3, e4]

/-- **The constant function is an eigenvector of $T_p$ on $X_{16}$ with eigenvalue $c_{16}(p)$** (Proposition 3.2.2;
$p$ odd). Unconditional. -/
theorem heckeT_sixteen_const {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x : QClass 16}
    (hx : x ∈ classSet 16) : heckeT p (fun _ => (1 : K)) x = (cn 16 p : K) := by
  have hP := nbCount_sixteen_add_uncond hp2
  have e1 : ((nbCount twoE8 p (classOf twoE8) : ℕ) : K) + nbCount twoE8 p (classOf gamma16) = cn 16 p := by
    have := congrArg (Nat.cast : ℕ → K) hP.1
    push_cast at this
    exact this
  have e2 : ((nbCount gamma16 p (classOf twoE8) : ℕ) : K) + nbCount gamma16 p (classOf gamma16) = cn 16 p := by
    have := congrArg (Nat.cast : ℕ → K) hP.2
    push_cast at this
    exact this
  rcases mem_sixteen hx with rfl | rfl
  · simp only [heckeT_A hp2, nsmul_eq_mul, mul_one]
    exact e1
  · simp only [heckeT_B hp2, nsmul_eq_mul, mul_one]
    exact e2

/-- **The second eigenvector of $T_p$ on $X_{16}$** (Chenevier–Lannes, §3.2, p. 57: the eigenvalues of $T_d$ on
$\mathbb{Z}[X_{16}]$ are integers; $p$ odd): the function $f$ with $f(E_8 \oplus E_8) = 405$, $f(E_{16}) = -286$
satisfies $T_pf = \lambda_p f$ on $X_{16}$ with
$\lambda_p = c_{16}(p) - N_p(E_8 \oplus E_8, E_{16}) - N_p(E_{16}, E_8 \oplus E_8) \in \mathbb{Z}$.
(Theorem A predicts $\lambda_p = c_{16}(p) - (1 + p + p^2 + p^3)(1 + p^{11} - \tau(p))$.) Unconditional. -/
@[kb "chenevierlannes2019" "§3.2, p. 57 (eigenvalues of T_p on Z[X_16], odd p)"]
theorem heckeT_sixteen_eigen {K : Type*} [CommRing K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : QClass 16 → K)
    (hf1 : f (classOf twoE8) = 405) (hf2 : f (classOf gamma16) = -286) {x : QClass 16} (hx : x ∈ classSet 16) :
    heckeT p f x = ((cn 16 p : ℤ) - nbCount twoE8 p (classOf gamma16) - nbCount gamma16 p (classOf twoE8) : ℤ) * f x := by
  have hP := nbCount_sixteen_add_uncond hp2
  have hm := nbCount_gamma16_twoE8_mul hp2
  have e1 : ((nbCount twoE8 p (classOf twoE8) : ℕ) : K) + nbCount twoE8 p (classOf gamma16) = cn 16 p := by
    have := congrArg (Nat.cast : ℕ → K) hP.1
    push_cast at this
    exact this
  have e2 : ((nbCount gamma16 p (classOf twoE8) : ℕ) : K) + nbCount gamma16 p (classOf gamma16) = cn 16 p := by
    have := congrArg (Nat.cast : ℕ → K) hP.2
    push_cast at this
    exact this
  have e3 : (405 : K) * nbCount gamma16 p (classOf twoE8) = 286 * nbCount twoE8 p (classOf gamma16) := by
    have := congrArg (Nat.cast : ℕ → K) hm
    push_cast at this
    exact this
  rcases mem_sixteen hx with rfl | rfl
  · rw [heckeT_A hp2, hf1, hf2]
    simp only [nsmul_eq_mul]
    push_cast
    linear_combination 405 * e1 + e3
  · rw [heckeT_B hp2, hf1, hf2]
    simp only [nsmul_eq_mul]
    push_cast
    linear_combination (-286) * e2 + e3

/-- `HeckeCommute 8` for odd primes. -/
theorem heckeCommute_eight_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (f : QClass 8 → ℂ) : ∀ x ∈ classSet 8, heckeT p (heckeT q f) x = heckeT q (heckeT p f) x :=
  fun _ hx => heckeT_comm_eight hp2 hq2 f hx

/-- `HeckeCommute 16` for odd primes. -/
theorem heckeCommute_sixteen_odd {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (f : QClass 16 → ℂ) : ∀ x ∈ classSet 16, heckeT p (heckeT q f) x = heckeT q (heckeT p f) x :=
  fun _ hx => heckeT_comm_sixteen hp2 hq2 f hx

end QuadFormsKB.ChenevierLannes
