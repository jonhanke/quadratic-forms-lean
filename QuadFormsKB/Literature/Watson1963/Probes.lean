/-
# Watson (1963), §6: the perfect forms $\varphi_v$, $\Phi_{m+1}$, $E_7$, $E_8$

G. L. Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963) 549–576, §6,
(6.1)–(6.2) and Lemmas 6–8 (pp. 558–559).

Variables are $x_0, \dots, x_{n-1}$ (0-based; Watson's $x_1, \dots, x_n$ are shifted down by one).

**Definitions.**
* `phiA v` $= \varphi_v = \sum_{0 \le i \le j < v} x_i x_j$ (Watson (6.1)); the root lattice $A_v$.
* `watsonForm m u w` $= \varphi_{m+1,u,c}$ (Watson (6.2), integral shape):
  $\varphi_m(x_0, \dots, x_{m-1}) + u\,(x_0 + \dots + x_{m-1})\,x_m + w\,x_m^2$.
* `phiD m` $= \Phi_{m+1}$ (`watsonForm m 2 2`, Watson's $c = 4$, $u = 2$): the root lattice $D_{m+1}$.
* `formE7` (`watsonForm 6 3 4`; Watson's $n = 7$, $c = 2$, $u = 3$) and `formE8` (`watsonForm 7 3 4`; $n = 8$, $c = 1$,
  $u = 3$): the root lattices $E_7$ and $E_8$.

**Proved here.**
* Evaluation formulas: $2\varphi_v(\vec x) = \sum x_i^2 + (\sum x_i)^2$ (`phiA_two_eval`); the value of a form at vectors
  supported on two or three coordinates (`eval2`, `eval3`); `watsonForm_eval`.
* Positive definiteness: `phiA_posDef`, `phiD_posDef`, `formE7_posDef`, `formE8_posDef`.
* Hessian determinants: $\det H(\varphi_v) = v + 1$ (`phiA_hessian_det`, all $v$);
  $\det H(\varphi_{m+1,u,w}) = 2w(m+1) - u^2 m$ for $w \ne 0$ (`watsonForm_hessian_det`), hence
  $\det \Phi_{m+1} = 4$ (`phiD_hessian_det`, all $m$; so $\Phi_5, \Phi_6, \Phi_9$ have determinant $4$),
  $\det E_7 = 2$ (`formE7_hessian_det`), $\det E_8 = 1$ (`formE8_hessian_det`).
* Perfection (Watson 1963, Lemmas 6, 7, 8, proofs on pp. 558–559): `phiA_isPerfectOne`, `phiD_isPerfectOne`
  ($m \ge 2$), `formE7_isPerfectOne`, `formE8_isPerfectOne`.
-/
import QuadFormsKB.Literature.Watson1963.Perfect

open Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace QuadFormsKB.Watson1963

/-! ### Values of a form at vectors with small support -/

/-- **Value at a vector supported on two coordinates.** For $i < j$,
$Q(a e_i + b e_j) = a^2 c_{ii} + b^2 c_{jj} + ab\, c_{ij}$. -/
theorem eval2 {n : ℕ} (Q : QuadForm ℤ n) {i j : Fin n} (hij : i < j) (a b : ℤ) :
    Q.eval (Pi.single i a + Pi.single j b) = a^2 * Q.coeff i i + b^2 * Q.coeff j j + a*b * Q.coeff i j := by
  rw [QuadForm.eval_eq_dotProduct']
  have hji : Q.coeff j i = 0 := Q.upper hij
  have h1 : i ≠ j := hij.ne
  simp [dotProduct, mulVec, Pi.single_apply, Finset.sum_add_distrib, mul_add, add_mul, h1, h1.symm, hji]
  ring

/-- **Value at a vector supported on three coordinates.** For $i < j < k$,
$Q(a e_i + b e_j + c e_k) = a^2 c_{ii} + b^2 c_{jj} + c^2 c_{kk} + ab\,c_{ij} + ac\,c_{ik} + bc\,c_{jk}$. -/
theorem eval3 {n : ℕ} (Q : QuadForm ℤ n) {i j k : Fin n} (hij : i < j) (hjk : j < k) (a b c : ℤ) :
    Q.eval (Pi.single i a + Pi.single j b + Pi.single k c) =
      a^2 * Q.coeff i i + b^2 * Q.coeff j j + c^2 * Q.coeff k k + a*b * Q.coeff i j + a*c * Q.coeff i k
      + b*c * Q.coeff j k := by
  rw [QuadForm.eval_eq_dotProduct']
  have hji : Q.coeff j i = 0 := Q.upper hij
  have hki : Q.coeff k i = 0 := Q.upper (hij.trans hjk)
  have hkj : Q.coeff k j = 0 := Q.upper hjk
  have h1 : i ≠ j := hij.ne
  have h2 : j ≠ k := hjk.ne
  have h3 : i ≠ k := (hij.trans hjk).ne
  simp [dotProduct, mulVec, Pi.single_apply, Finset.sum_add_distrib, mul_add, add_mul, h1, h2, h3, h1.symm, h2.symm,
    h3.symm, hji, hki, hkj]
  ring

/-! ### Definitions -/

/-- **Watson's $\varphi_v$** (Watson 1963, (6.1), p. 558): $\varphi_v = \sum_{0 \le i \le j < v} x_i x_j$, the root
lattice $A_v$ (value $1$ at $e_i$ and at $e_i - e_j$). Argument: the number of variables `v`. -/
@[kb "watson1963" "§6, (6.1), p. 558"]
def phiA (v : ℕ) : QuadForm ℤ v := QuadForm.ofUpper fun _ _ => 1

/-- **Watson's $\varphi_{m+1,u,c}$** (Watson 1963, (6.2), p. 558) in integral shape:
$\varphi_m(x_0, \dots, x_{m-1}) + u\,(x_0 + \dots + x_{m-1})\,x_m + w\,x_m^2$, a form in $m + 1$ variables. The last
variable is $x_m$. Arguments: `m`, the cross coefficient `u`, the last diagonal coefficient `w`. -/
@[kb "watson1963" "§6, (6.2), p. 558"]
def watsonForm (m : ℕ) (u w : ℤ) : QuadForm ℤ (m + 1) :=
  QuadForm.ofUpper fun i j => if j = Fin.last m then (if i = Fin.last m then w else u) else 1

/-- **Watson's $\Phi_{m+1}$** (Watson 1963, Lemma 8, p. 559; $c = 4$, $u = 2$): `watsonForm m 2 2`, the root lattice
$D_{m+1}$. -/
@[kb "watson1963" "§6, Lemma 8, p. 559"]
def phiD (m : ℕ) : QuadForm ℤ (m + 1) := watsonForm m 2 2

/-- **The form $E_7$** (Watson 1963, Lemma 7, p. 559; $n = 7$, $c = 2$, $u = 3$): `watsonForm 6 3 4`. -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
def formE7 : QuadForm ℤ 7 := watsonForm 6 3 4

/-- **The form $E_8$** (Watson 1963, Lemma 7, p. 559; $n = 8$, $c = 1$, $u = 3$): `watsonForm 7 3 4`. -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
def formE8 : QuadForm ℤ 8 := watsonForm 7 3 4

/-! ### Coefficients and values -/

theorem phiA_coeff {v : ℕ} (i j : Fin v) : (phiA v).coeff i j = if i ≤ j then 1 else 0 := by
  simp [phiA, QuadForm.ofUpper]

theorem watsonForm_coeff_cc {m : ℕ} (u w : ℤ) (i j : Fin m) :
    (watsonForm m u w).coeff i.castSucc j.castSucc = if i ≤ j then 1 else 0 := by
  simp [watsonForm, QuadForm.ofUpper, Fin.castSucc_ne_last]

theorem watsonForm_coeff_ct {m : ℕ} (u w : ℤ) (i : Fin m) :
    (watsonForm m u w).coeff i.castSucc (Fin.last m) = u := by
  simp [watsonForm, QuadForm.ofUpper, Fin.castSucc_ne_last, Fin.le_last]

theorem watsonForm_coeff_tt {m : ℕ} (u w : ℤ) : (watsonForm m u w).coeff (Fin.last m) (Fin.last m) = w := by
  simp [watsonForm, QuadForm.ofUpper]

/-- **Doubled value of $\varphi_v$:** $2\varphi_v(\vec x) = \sum_i x_i^2 + (\sum_i x_i)^2$. -/
theorem phiA_two_eval {v : ℕ} (x : Fin v → ℤ) :
    2 * (phiA v).eval x = ∑ i, x i ^ 2 + (∑ i, x i) ^ 2 := by
  have e : (phiA v).eval x = ∑ i, ∑ j, if i ≤ j then x i * x j else 0 := by
    simp only [QuadForm.eval, QuadForm.evalIn, phiA_coeff, algebraMap_int_eq, eq_intCast, Int.cast_id]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have e2 : (∑ i, ∑ j, if i ≤ j then x i * x j else 0) = ∑ i, ∑ j, if j ≤ i then x i * x j else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hd : ∑ i, x i ^ 2 = ∑ i, ∑ j, if i = j then x i * x j else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq]
  have e3 : (∑ i, ∑ j, if i ≤ j then x i * x j else 0) + (∑ i, ∑ j, if j ≤ i then x i * x j else 0)
      = (∑ i, x i) ^ 2 + ∑ i, x i ^ 2 := by
    rw [sq, Finset.sum_mul_sum, hd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : i = j
    · subst h1; simp
    · rcases lt_or_gt_of_ne h1 with h | h
      · simp [h.le, not_le.mpr h, h1]
      · simp [h.le, not_le.mpr h, h1]
  rw [e]
  linarith [e2, e3]

/-- **Value of $\varphi_{m+1,u,w}$:** $\varphi_m(\vec y) + u\,(\sum y_i)\,t + w\,t^2$ where $y_i = x_i$ ($i < m$) and
$t = x_m$. -/
theorem watsonForm_eval {m : ℕ} (u w : ℤ) (x : Fin (m + 1) → ℤ) :
    (watsonForm m u w).eval x = (phiA m).eval (fun i : Fin m => x i.castSucc)
      + u * (∑ i : Fin m, x i.castSucc) * x (Fin.last m) + w * x (Fin.last m) ^ 2 := by
  have h : ∀ i : Fin m, ¬ (Fin.last m ≤ i.castSucc) := fun i => not_le.mpr (Fin.castSucc_lt_last i)
  simp only [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_castSucc, algebraMap_int_eq, eq_intCast, Int.cast_id,
    watsonForm_coeff_cc, watsonForm_coeff_ct, watsonForm_coeff_tt, phiA_coeff, Fin.castSucc_le_castSucc_iff,
    Fin.le_last, h, ite_true, ite_false, Finset.sum_const_zero, add_zero, le_refl, Finset.mul_sum]
  have h2 : ∀ i j : Fin m, (if i ≤ j then (if i ≤ j then (1:ℤ) else 0) * x i.castSucc * x j.castSucc else 0)
      = (if i ≤ j then x i.castSucc * x j.castSucc else 0) := fun i j => by split_ifs <;> simp
  simp only [h2, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  ring

/-! ### Positive definiteness -/

theorem eq_zero_of_parts {m : ℕ} (x : Fin (m + 1) → ℤ) (h : ∀ i : Fin m, x i.castSucc = 0)
    (ht : x (Fin.last m) = 0) : x = 0 := by
  funext l
  induction l using Fin.lastCases with
  | last => exact ht
  | cast i => exact h i

theorem sum_sq_eq_zero {m : ℕ} (f : Fin m → ℤ) (h : ∑ i, f i ^ 2 ≤ 0) : ∀ i, f i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (f j))).1
    (le_antisymm h (Finset.sum_nonneg fun j _ => sq_nonneg _)) i (Finset.mem_univ i)
  exact pow_eq_zero_iff two_ne_zero |>.1 this

/-- **$\varphi_v$ is positive definite** (from $2\varphi_v = \sum x_i^2 + (\sum x_i)^2$; Watson 1963, §6, p. 558). -/
theorem phiA_posDef (v : ℕ) : IntQF.PosDef (phiA v) := by
  intro x hx
  have h2 := phiA_two_eval x
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  have : 0 < ∑ i, x i ^ 2 := lt_of_lt_of_le (sq_pos_of_ne_zero hi')
    (Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  nlinarith [sq_nonneg (∑ i, x i)]

/-- **$\Phi_{m+1}$ is positive definite:** $2\Phi_{m+1}(\vec x) = \sum_{i<m} x_i^2 + (s + 2x_m)^2$ with
$s = \sum_{i<m} x_i$ (Watson 1963, Lemma 8, p. 559). -/
@[kb "watson1963" "§6, Lemma 8, p. 559"]
theorem phiD_posDef (m : ℕ) (hm : 1 ≤ m) : IntQF.PosDef (phiD m) := by
  intro x hx
  by_contra hle
  rw [not_lt] at hle
  apply hx
  have e := watsonForm_eval 2 2 x
  have h2 := phiA_two_eval (fun i : Fin m => x i.castSucc)
  unfold phiD at hle
  have key : 2 * (watsonForm m 2 2).eval x = ∑ i : Fin m, x i.castSucc ^ 2
      + ((∑ i : Fin m, x i.castSucc) + 2 * x (Fin.last m)) ^ 2 := by
    rw [e]; linear_combination h2
  have hS : 0 ≤ ∑ i : Fin m, x i.castSucc ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hy := sum_sq_eq_zero (fun i : Fin m => x i.castSucc) (by nlinarith [sq_nonneg ((∑ i : Fin m, x i.castSucc) + 2 * x (Fin.last m))])
  have hs : ∑ i : Fin m, x i.castSucc = 0 := Finset.sum_eq_zero fun i _ => hy i
  have ht : x (Fin.last m) = 0 := by
    have : (2 * x (Fin.last m)) ^ 2 ≤ 0 := by
      rw [hs] at key
      have : ∑ i : Fin m, x i.castSucc ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by simp [hy i]
      nlinarith
    have := pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
    omega
  exact eq_zero_of_parts x hy ht

/-- **The identity behind positivity of $E_7$, $E_8$:**
$8\,\varphi_{m+1,3,4}(\vec x) = \sum_{i<m}(2x_i + t)^2 + (2s + 5t)^2 + (7 - m)\,t^2$, with $t = x_m$,
$s = \sum_{i<m} x_i$. For $m = 6$: $8E_7 = \dots + t^2$; for $m = 7$: $8E_8 = \dots$. -/
theorem watsonE_eight (m : ℕ) (x : Fin (m + 1) → ℤ) :
    8 * (watsonForm m 3 4).eval x = ∑ i : Fin m, (2 * x i.castSucc + x (Fin.last m)) ^ 2
      + (2 * (∑ i : Fin m, x i.castSucc) + 5 * x (Fin.last m)) ^ 2 + (7 - (m : ℤ)) * x (Fin.last m) ^ 2 := by
  have e := watsonForm_eval 3 4 x
  have h2 := phiA_two_eval (fun i : Fin m => x i.castSucc)
  have hsq : ∑ i : Fin m, (2 * x i.castSucc + x (Fin.last m)) ^ 2 = 4 * ∑ i : Fin m, x i.castSucc ^ 2
      + 4 * (∑ i : Fin m, x i.castSucc) * x (Fin.last m) + m * x (Fin.last m) ^ 2 := by
    simp only [add_sq, Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsq, e]
  linear_combination (4 : ℤ) * h2

theorem watsonE_posDef (m : ℕ) (hm : m = 6 ∨ m = 7) : IntQF.PosDef (watsonForm m 3 4) := by
  intro x hx
  by_contra hle
  rw [not_lt] at hle
  apply hx
  have key := watsonE_eight m x
  have hm7 : (m : ℤ) ≤ 7 := by rcases hm with rfl | rfl <;> norm_num
  have hA : 0 ≤ ∑ i : Fin m, (2 * x i.castSucc + x (Fin.last m)) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hC : 0 ≤ (7 - (m : ℤ)) * x (Fin.last m) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hy := sum_sq_eq_zero (fun i : Fin m => 2 * x i.castSucc + x (Fin.last m))
    (by nlinarith [sq_nonneg (2 * (∑ i : Fin m, x i.castSucc) + 5 * x (Fin.last m))])
  have hB : 2 * (∑ i : Fin m, x i.castSucc) + 5 * x (Fin.last m) = 0 := by
    have : (2 * (∑ i : Fin m, x i.castSucc) + 5 * x (Fin.last m)) ^ 2 ≤ 0 := by nlinarith
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))
  have h2s : 2 * (∑ i : Fin m, x i.castSucc) = -(m : ℤ) * x (Fin.last m) := by
    rw [Finset.mul_sum]
    have : ∀ i : Fin m, 2 * x i.castSucc = - x (Fin.last m) := fun i => by have h := hy i; linarith
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have ht : x (Fin.last m) = 0 := by
    have h5 : (5 - (m : ℤ)) * x (Fin.last m) = 0 := by linarith
    have hne : (5 - (m : ℤ)) ≠ 0 := by rcases hm with rfl | rfl <;> norm_num
    exact (mul_eq_zero.1 h5).resolve_left hne
  refine eq_zero_of_parts x (fun i => ?_) ht
  have h := hy i
  rw [ht] at h
  omega

/-- **$E_7$ is positive definite:** $8E_7 = \sum_{i<6}(2x_i + t)^2 + (2s + 5t)^2 + t^2$, $t = x_6$
(Watson 1963, Lemma 7, p. 559). -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE7_posDef : IntQF.PosDef formE7 := watsonE_posDef 6 (Or.inl rfl)

/-- **$E_8$ is positive definite:** $8E_8 = \sum_{i<7}(2x_i + t)^2 + (2s + 5t)^2$, $t = x_7$
(Watson 1963, Lemma 7, p. 559). -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE8_posDef : IntQF.PosDef formE8 := watsonE_posDef 7 (Or.inr rfl)

/-! ### Perfection (Watson 1963, proofs of Lemmas 6, 7, 8) -/

/-- If $\varphi'$ is $1$ wherever $\varphi$ is, then $c'_{ii} = 1$ when $\varphi(e_i) = 1$. -/
theorem diag_one {n : ℕ} (φ Q' : QuadForm ℤ n) (h : ∀ y, φ.eval y = 1 → Q'.eval y = 1) (i : Fin n)
    (hφ : φ.coeff i i = 1) : Q'.coeff i i = 1 := by
  rw [← QuadForm.eval_single]
  apply h
  rw [QuadForm.eval_single]
  exact hφ

/-- If $\varphi(e_i - e_j) = 1$ is forced and the diagonal coefficients agree, then $c'_{ij} = c_{ij} = 1$
($i < j$, all of $c_{ii}, c_{jj}, c_{ij}$ equal to $1$ for $\varphi$). -/
theorem off_one {n : ℕ} (φ Q' : QuadForm ℤ n) (h : ∀ y, φ.eval y = 1 → Q'.eval y = 1) {i j : Fin n}
    (hij : i < j) (hii : φ.coeff i i = 1) (hjj : φ.coeff j j = 1) (hφ : φ.coeff i j = 1)
    (hQi : Q'.coeff i i = 1) (hQj : Q'.coeff j j = 1) : Q'.coeff i j = 1 := by
  have := h (Pi.single i 1 + Pi.single j (-1)) (by rw [eval2 φ hij, hii, hjj, hφ]; norm_num)
  rw [eval2 Q' hij, hQi, hQj] at this
  linarith

/-- $\varphi_v$ is determined by the vectors of value $1$ (Watson 1963, Lemma 6, p. 558): a form $\varphi'$ with
value $1$ wherever $\varphi_v$ has value $1$ (at $e_i$ and $e_i - e_j$) equals $\varphi_v$. -/
@[kb "watson1963" "§6, Lemma 6, p. 558"]
theorem phiA_isPerfectOne (v : ℕ) : IsPerfectOne (phiA v) := by
  refine ⟨phiA_posDef v, fun Q' h => ?_⟩
  have hd : ∀ i, Q'.coeff i i = 1 := fun i => diag_one _ Q' h i (by simp [phiA_coeff])
  apply QuadForm.ext_upper
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · rw [off_one (phiA v) Q' h hlt (by simp [phiA_coeff]) (by simp [phiA_coeff]) (by simp [phiA_coeff, hlt.le])
      (hd i) (hd j)]
    simp [phiA_coeff, hlt.le]
  · rw [hd]; simp [phiA_coeff]

/-- The part of $\varphi'$ on the first $m$ variables equals that of $\varphi_{m+1,u,w}$ (all coefficients $1$). -/
theorem watson_Apart {m : ℕ} (u w : ℤ) (Q' : QuadForm ℤ (m + 1))
    (h : ∀ y, (watsonForm m u w).eval y = 1 → Q'.eval y = 1) :
    ∀ i j : Fin m, i ≤ j → Q'.coeff i.castSucc j.castSucc = 1 := by
  have hd : ∀ i : Fin m, Q'.coeff i.castSucc i.castSucc = 1 := fun i =>
    diag_one _ Q' h _ (by simp [watsonForm_coeff_cc])
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · exact off_one (watsonForm m u w) Q' h (Fin.castSucc_lt_castSucc_iff.2 hlt)
      (by simp [watsonForm_coeff_cc]) (by simp [watsonForm_coeff_cc])
      (by simp [watsonForm_coeff_cc, hlt.le]) (hd i) (hd j)
  · exact hd i

/-- A form with the right coefficients is $\varphi_{m+1,u,w}$. -/
theorem watson_ext {m : ℕ} (u w : ℤ) (Q' : QuadForm ℤ (m + 1))
    (hA : ∀ i j : Fin m, i ≤ j → Q'.coeff i.castSucc j.castSucc = 1)
    (hu : ∀ i : Fin m, Q'.coeff i.castSucc (Fin.last m) = u) (hw : Q'.coeff (Fin.last m) (Fin.last m) = w) :
    Q' = watsonForm m u w := by
  apply QuadForm.ext_upper
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => rw [hw, watsonForm_coeff_tt]
    | cast i => rw [hu, watsonForm_coeff_ct]
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd hij (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      have hij' : i ≤ j := Fin.castSucc_le_castSucc_iff.1 hij
      rw [hA i j hij', watsonForm_coeff_cc]
      simp [hij']

/-- Value $1$ at $-e_i + e_m$ forces $c'_{mm} - c'_{i m} = 0$ when $1 + w - u = 1$. -/
theorem watson_pair1 {m : ℕ} (u w : ℤ) (hv : 1 + w - u = 1) (Q' : QuadForm ℤ (m + 1))
    (h : ∀ y, (watsonForm m u w).eval y = 1 → Q'.eval y = 1) (i : Fin m) :
    Q'.coeff i.castSucc (Fin.last m) = Q'.coeff (Fin.last m) (Fin.last m) := by
  have hA := watson_Apart u w Q' h
  have := h (Pi.single i.castSucc (-1) + Pi.single (Fin.last m) 1) (by
    rw [eval2 _ (Fin.castSucc_lt_last i), watsonForm_coeff_cc, watsonForm_coeff_ct, watsonForm_coeff_tt]
    simp; linarith)
  rw [eval2 _ (Fin.castSucc_lt_last i), hA i i le_rfl] at this
  linarith

/-- Value $1$ at $-e_i - e_j + e_m$ ($i < j < m$) gives $3 + c'_{mm} - c'_{im} - c'_{jm} = 1$ when
$3 + w - 2u = 1$. -/
theorem watson_pair2 {m : ℕ} (u w : ℤ) (hv : 3 + w - 2 * u = 1) (Q' : QuadForm ℤ (m + 1))
    (h : ∀ y, (watsonForm m u w).eval y = 1 → Q'.eval y = 1) {i j : Fin m} (hij : i < j) :
    3 + Q'.coeff (Fin.last m) (Fin.last m) - Q'.coeff i.castSucc (Fin.last m)
      - Q'.coeff j.castSucc (Fin.last m) = 1 := by
  have hA := watson_Apart u w Q' h
  have hij' : i.castSucc < j.castSucc := Fin.castSucc_lt_castSucc_iff.2 hij
  have := h (Pi.single i.castSucc (-1) + Pi.single j.castSucc (-1) + Pi.single (Fin.last m) 1) (by
    rw [eval3 _ hij' (Fin.castSucc_lt_last j), watsonForm_coeff_cc, watsonForm_coeff_cc, watsonForm_coeff_cc,
      watsonForm_coeff_ct, watsonForm_coeff_ct, watsonForm_coeff_tt]
    simp [hij.le]; linarith)
  rw [eval3 _ hij' (Fin.castSucc_lt_last j), hA i i le_rfl, hA j j le_rfl, hA i j hij.le] at this
  linarith

/-- **$\Phi_{m+1}$ is perfect** ($m \ge 2$; Watson 1963, Lemma 8, p. 559). Vectors $-e_i + e_m$ and
$-e_i - e_j + e_m$ (value $1$) force $c'_{im} = c'_{mm} = 2$. -/
@[kb "watson1963" "§6, Lemma 8, p. 559"]
theorem phiD_isPerfectOne (m : ℕ) (hm : 2 ≤ m) : IsPerfectOne (phiD m) := by
  refine ⟨phiD_posDef m (by omega), fun Q' h => ?_⟩
  unfold phiD at h ⊢
  have h1 := watson_pair1 2 2 (by norm_num) Q' h
  have h2 := watson_pair2 2 2 (by norm_num) Q' h (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.lt_def])
  have hc : Q'.coeff (Fin.last m) (Fin.last m) = 2 := by
    rw [h1 ⟨0, by omega⟩, h1 ⟨1, by omega⟩] at h2
    linarith
  exact watson_ext 2 2 Q' (watson_Apart 2 2 Q' h) (fun i => by rw [h1, hc]) hc

/-- **Perfection of the $m = 6, 7$ forms $\varphi_{m+1,3,4}$** (Watson 1963, Lemma 7, p. 559): the vectors
$-e_i - e_j + e_m$ and $(-1, \dots, -1, 0 \text{ or } -1\ldots, 2)$ force $c'_{im} = 3$, $c'_{mm} = 4$. -/
theorem watsonE_isPerfectOne (m : ℕ) (hm : m = 6 ∨ m = 7) : IsPerfectOne (watsonForm m 3 4) := by
  refine ⟨watsonE_posDef m hm, fun Q' h => ?_⟩
  have hm3 : 3 ≤ m := by omega
  have hp := fun (i j : Fin m) (hij : i < j) => watson_pair2 3 4 (by norm_num) Q' h hij
  set a := fun i : Fin m => Q'.coeff i.castSucc (Fin.last m) with ha
  set c := Q'.coeff (Fin.last m) (Fin.last m) with hc
  have p01 := hp ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have p02 := hp ⟨0, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have p12 := hp ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have hall : ∀ i : Fin m, a i = a ⟨0, by omega⟩ := by
    intro i
    by_cases h0 : i.val = 0
    · congr 1; exact Fin.ext h0
    by_cases h1 : i.val = 1
    · have : i = ⟨1, by omega⟩ := Fin.ext h1
      rw [this]; simp only [ha]; linarith
    by_cases h2 : i.val = 2
    · have : i = ⟨2, by omega⟩ := Fin.ext h2
      rw [this]; simp only [ha]; linarith
    · have := hp ⟨0, by omega⟩ i (by simp [Fin.lt_def]; omega)
      simp only [ha]; linarith
  have hQ : Q' = watsonForm m (a ⟨0, by omega⟩) c :=
    watson_ext _ _ Q' (watson_Apart 3 4 Q' h) (fun i => hall i) rfl
  have hc2 : c = 2 * a ⟨0, by omega⟩ - 2 := by
    have := hall ⟨1, by omega⟩
    simp only [ha] at this ⊢
    linarith
  -- the long vector (-1, ..., -1, 0 or -1, 2)
  let y : Fin m → ℤ := fun i => if i.val < 6 then -1 else 0
  have hS : ∑ i : Fin m, y i ^ 2 = 6 ∧ ∑ i : Fin m, y i = -6 := by
    rcases hm with rfl | rfl <;> constructor <;> decide
  have hP : (phiA m).eval y = 21 := by
    have := phiA_two_eval y
    rw [hS.1, hS.2] at this
    linarith
  let x : Fin (m + 1) → ℤ := Fin.snoc (α := fun _ => ℤ) y 2
  have hx : (fun i : Fin m => x i.castSucc) = y := by funext i; simp [x]
  have hl : x (Fin.last m) = 2 := by simp [x]
  have hφ : (watsonForm m 3 4).eval x = 1 := by
    rw [watsonForm_eval, hx, hl, hP, hS.2]
    norm_num
  have h' := h x hφ
  rw [hQ, watsonForm_eval, hx, hl, hS.2, hP] at h'
  have ha0 : a ⟨0, by omega⟩ = 3 := by linarith
  have hc4 : c = 4 := by linarith
  exact hQ.trans (by rw [ha0, hc4])

/-- **$E_7$ is perfect** (Watson 1963, Lemma 7, p. 559): $\varphi' = 1$ wherever $E_7 = 1$ forces $\varphi' = E_7$. -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE7_isPerfectOne : IsPerfectOne formE7 := watsonE_isPerfectOne 6 (Or.inl rfl)

/-- **$E_8$ is perfect** (Watson 1963, Lemma 7, p. 559): $\varphi' = 1$ wherever $E_8 = 1$ forces $\varphi' = E_8$. -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE8_isPerfectOne : IsPerfectOne formE8 := watsonE_isPerfectOne 7 (Or.inr rfl)

/-! ### Hessian determinants -/

/-- **$\det H(\varphi_v) = v + 1$** (the discriminant of the root lattice $A_v$). The Hessian is $I + J$ with $J$ the
all-ones matrix. -/
theorem phiA_hessian_det (v : ℕ) : (phiA v).hessian.det = v + 1 := by
  have h : (phiA v).hessian = 1 + replicateCol (Fin 1) (1 : Fin v → ℤ) * replicateRow (Fin 1) (1 : Fin v → ℤ) := by
    ext i j
    simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, phiA_coeff, Matrix.one_apply,
      Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Pi.one_apply, Finset.univ_unique,
      Finset.sum_singleton, mul_one]
    rcases lt_trichotomy i j with hl | rfl | hg
    · simp [hl.le, not_le.mpr hl, hl.ne]
    · simp
    · simp [hg.le, not_le.mpr hg, hg.ne']
  rw [h]
  refine (det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (1 : Fin v → ℤ) 1).trans ?_
  simp [dotProduct]
  ring

theorem hess_cc {m : ℕ} (u w : ℤ) (i j : Fin m) :
    (watsonForm m u w).hessian i.castSucc j.castSucc = if i = j then 2 else 1 := by
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, watsonForm_coeff_cc]
  rcases lt_trichotomy i j with hl | rfl | hg
  · simp [hl.le, not_le.mpr hl, hl.ne]
  · simp
  · simp [hg.le, not_le.mpr hg, hg.ne']

theorem hess_ct {m : ℕ} (u w : ℤ) (i : Fin m) :
    (watsonForm m u w).hessian i.castSucc (Fin.last m) = u := by
  have hz : (watsonForm m u w).coeff (Fin.last m) i.castSucc = 0 :=
    (watsonForm m u w).upper (Fin.castSucc_lt_last i)
  simp [QuadForm.hessian, watsonForm_coeff_ct, hz]

theorem hess_tc {m : ℕ} (u w : ℤ) (i : Fin m) :
    (watsonForm m u w).hessian (Fin.last m) i.castSucc = u := by
  have hz : (watsonForm m u w).coeff (Fin.last m) i.castSucc = 0 :=
    (watsonForm m u w).upper (Fin.castSucc_lt_last i)
  simp [QuadForm.hessian, watsonForm_coeff_ct, hz]

theorem hess_tt {m : ℕ} (u w : ℤ) : (watsonForm m u w).hessian (Fin.last m) (Fin.last m) = 2 * w := by
  simp only [QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply, watsonForm_coeff_tt]
  ring

/-- **$\det H(\varphi_{m+1,u,w}) = 2w(m+1) - u^2 m$** for $w \ne 0$ (Schur complement of the last variable). -/
theorem watsonForm_hessian_det (m : ℕ) (u w : ℤ) (hw : w ≠ 0) :
    (watsonForm m u w).hessian.det = 2 * w * (m + 1) - u ^ 2 * m := by
  have hwq' : (w : ℚ) ≠ 0 := by exact_mod_cast hw
  have hwq : (2 * (w : ℚ)) ≠ 0 := mul_ne_zero two_ne_zero hwq'
  let A : Matrix (Fin m) (Fin m) ℚ := Matrix.of fun i j => if i = j then 2 else 1
  let B : Matrix (Fin m) (Fin 1) ℚ := Matrix.of fun _ _ => (u : ℚ)
  let C : Matrix (Fin 1) (Fin m) ℚ := Matrix.of fun _ _ => (u : ℚ)
  let D : Matrix (Fin 1) (Fin 1) ℚ := Matrix.of fun _ _ => 2 * (w : ℚ)
  let D' : Matrix (Fin 1) (Fin 1) ℚ := Matrix.of fun _ _ => (2 * (w : ℚ))⁻¹
  have hDD : D * D' = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [D, D', Matrix.mul_apply]
    field_simp
  let _ : Invertible D := invertibleOfRightInverse D D' hDD
  have hinv : ⅟D = D' := invOf_eq_right_inv hDD
  have hN : Matrix.fromBlocks A B C D = Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      ((watsonForm m u w).hessian.map (Int.castRingHom ℚ)) := by
    have hl : ∀ i : Fin m, finSumFinEquiv (Sum.inl i : Fin m ⊕ Fin 1) = i.castSucc := fun i => rfl
    have hr : ∀ i : Fin 1, finSumFinEquiv (Sum.inr i : Fin m ⊕ Fin 1) = Fin.last m := fun i => by
      ext; simp [Fin.fin_one_eq_zero i]
    ext p q
    rcases p with i | i <;> rcases q with j | j
    · simp [A, Matrix.reindex_apply, hl, hess_cc]
    · simp [B, Matrix.reindex_apply, hl, hr, hess_ct]
    · simp [C, Matrix.reindex_apply, hl, hr, hess_tc]
    · simp [D, Matrix.reindex_apply, hr, hess_tt]
  have hq : ((watsonForm m u w).hessian.det : ℚ) = 2 * w * (m + 1) - u ^ 2 * m := by
    have h1 : ((watsonForm m u w).hessian.det : ℚ) = ((watsonForm m u w).hessian.map (Int.castRingHom ℚ)).det :=
      (Int.castRingHom ℚ).map_det _
    rw [h1, ← Matrix.det_reindex_self finSumFinEquiv.symm, ← hN, Matrix.det_fromBlocks₂₂, hinv]
    have hS : A - B * D' * C = 1 + replicateCol (Fin 1) (fun _ : Fin m => 1 - (u : ℚ) ^ 2 / (2 * w)) *
        replicateRow (Fin 1) (fun _ : Fin m => (1 : ℚ)) := by
      ext i j
      simp [A, B, C, D', Matrix.mul_apply, Matrix.one_apply]
      split_ifs <;> field_simp <;> ring
    rw [hS]
    refine (congrArg (fun z => D.det * z) (det_one_add_replicateCol_mul_replicateRow (ι := Fin 1)
      (fun _ : Fin m => 1 - (u : ℚ) ^ 2 / (2 * w)) (fun _ : Fin m => (1 : ℚ)))).trans ?_
    simp [D, dotProduct]
    field_simp
    ring
  exact_mod_cast hq

/-- **$\det H(\Phi_{m+1}) = 4$** for every $m$; in particular $\Phi_5$, $\Phi_6$, $\Phi_9$ ($m = 4, 5, 8$) have
determinant $4$ (Watson 1963, Lemma 8, p. 559). -/
@[kb "watson1963" "§6, Lemma 8, p. 559"]
theorem phiD_hessian_det (m : ℕ) : (phiD m).hessian.det = 4 := by
  unfold phiD
  rw [watsonForm_hessian_det m 2 2 (by norm_num)]
  ring

/-- **$\det H(E_7) = 2$** (Watson 1963, Lemma 7, p. 559; $2 \cdot 4 \cdot 7 - 9 \cdot 6 = 2$). -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE7_hessian_det : formE7.hessian.det = 2 := by
  unfold formE7
  rw [watsonForm_hessian_det 6 3 4 (by norm_num)]
  norm_num

/-- **$\det H(E_8) = 1$** (Watson 1963, Lemma 7, p. 559; $2 \cdot 4 \cdot 8 - 9 \cdot 7 = 1$). -/
@[kb "watson1963" "§6, Lemma 7, p. 559"]
theorem formE8_hessian_det : formE8.hessian.det = 1 := by
  unfold formE8
  rw [watsonForm_hessian_det 7 3 4 (by norm_num)]
  norm_num

end QuadFormsKB.Watson1963
