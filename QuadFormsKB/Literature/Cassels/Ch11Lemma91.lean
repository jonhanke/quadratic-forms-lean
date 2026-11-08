/-
# Cassels, Chapter 11, Lemma 9.1: propagation of $\mathcal R(f, a)$ from $a$ to $q^m a$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, §9, Lemma 9.1, pp. 241–242. Companion to
`Ch11Sec9.lean`, which states the lemma as the named statement `Cassels.Lemma91` (read its docstring for the reconstructed
hypotheses) and deduces the case $n = 4$ of Theorem 1.6 from Lemmas 9.1 and 9.2.

**Conventions.** Forms `QuadForm ℤ 4`, classically integral (`IsClassicallyIntegral`, Cassels' matrix
`Siegel.casselsMat`), positive definite (`IntQF.PosDef`); Cassels' determinant $d(f)$ is `cassDet`; "$d \in U_q^2$" is
`IsUnitSquareAt q d`; $\mathcal R(f, a)$ is `LocGlobal f a`. Indices are 0-based: Cassels' $x_1, x_2, x_3, x_4$ are
$x_0, x_1, x_2, x_3$ here, and the substitution (9.26) is $g(\mathbf x) = q^{-m}f(x_0, x_1, q^mx_2, q^mx_3)$.

**Proves** `lemma91_holds : Lemma91`, unconditionally; hence `tartakowskyClassicalAt_four_of_lemma92` (Theorem 1.6 for
$n = 4$, conditional only on `Lemma92`; `Lemma92` is proved in `Ch11Lemma92Final.lean`, which gives the unconditional
`Ch11L92.tartakowskyClassicalAt_four_holds`).

**Proof** (Cassels' proof, pp. 241–242, with one simplification). For $m = 0$ the statement is the hypothesis (applied to
$f$ itself). Let $m \ge 1$.
1. *Local normal form* (`exists_isotropic_plane_local`): since $q \ne 2$ and $d \in U_q^2$, $d = \delta^2$, the form $f$ is
   $\mathbb Z_q$-equivalent to $2x_0x_2 + 2\delta x_1x_3$ (O'Meara 92:2, `Siegel.Kneser.isometricGL_of_unimodular`), so
   there is $T \in \mathrm{SL}_4(\mathbb Z_q)$ whose first two columns span a totally isotropic plane.
2. *Approximation* (`exists_good_basis`): Chapter 9, Theorem 2.1 (`Siegel.exists_basis_approx`) gives $C \in
   \mathrm{SL}_4(\mathbb Z)$ congruent to $T$ modulo $q^m$; the form $f' = f \circ C$ ($\mathbb Z$-equivalent to $f$) then has
   $f'_{00}, f'_{01}, f'_{11} \equiv 0 \pmod{q^m}$. This is all that is needed of (9.24) (Cassels asks for the congruence
   (9.25) modulo $q^{2m+1}$; modulo $q^m$ suffices, because $\mathcal R(g, a)$ over $\mathbb Z_q$ is obtained here from the
   unimodularity of $g$ at $q$ instead of from (9.27)).
3. *The form $g$* (`gForm`): $g(\mathbf x) = q^{-m}f'(x_0, x_1, q^mx_2, q^mx_3)$ is classically integral, positive definite,
   of determinant $d$ (`cassDet_gForm`).
4. *Local representations* (`primRepZp_gForm`): $a$ is primitively represented by $g$ over $\mathbb Z_p$, for $p \ne q$
   because $q^ma$ is primitively represented by $f'$ and $q$ is a $p$-adic unit, for $p = q$ because $g$ is unimodular at $q$
   and so $\mathbb Z_q$-equivalent to $2x_0x_2 + x_1^2 - dx_3^2$, which represents every $a$ with $x_0 = 1$.
5. *Global*: the hypothesis $\mathcal R(g, a)$ gives a primitive $\mathbf b$ with $g(\mathbf b) = a$; then
   $q^ma = f'(b_0, b_1, q^mb_2, q^mb_3)$, primitively: a common divisor prime to $q$ divides every $b_i$, and $q$ cannot
   divide both $b_0, b_1$, since then $q \mid g(\mathbf b) = a$ (all coefficients of $g$ involving only $x_2, x_3$ are
   divisible by $q^m$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Sec9
import QuadFormsKB.Literature.Cassels.Ch9Sec2
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Siegel.UnimodularPadic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11Lemma91

open QuadFormsKB QuadFormsKB.Siegel QuadFormsKB.Cassels

variable {k : ℕ}

/-! ### Generic algebra -/

/-- Helper: $Q(\mathbf x + c\,\mathbf e) = Q(\mathbf x) + c\,r$ for some $r$ (over any commutative ring). -/
theorem eval_add_smul (R : Type*) [CommRing R] (Q : QuadForm R k) (x e : Fin k → R) (c : R) :
    ∃ r, Q.eval (x + c • e) = Q.eval x + c * r := by
  refine ⟨∑ i, ∑ j, if i ≤ j then Q.coeff i j * (e i * x j + x i * e j + c * e i * e j) else 0, ?_⟩
  simp only [QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [Pi.add_apply, smul_eq_mul] <;> ring

/-- Helper: values of the mapped form are values over the bigger ring. -/
theorem eval_map_eq_evalIn (R : Type*) [CommRing R] (Q : QuadForm ℤ k) (x : Fin k → R) :
    (Q.map (Int.castRingHom R)).eval x = Q.evalIn R x := by
  simp [QuadForm.evalIn, QuadForm.map]

/-- Helper: the form of a symmetric integer matrix, evaluated over a domain of characteristic zero:
$(\mathrm{ofGram}\,A)(\mathbf x) = \mathbf x^{\mathsf T}A\mathbf x$. -/
theorem evalIn_ofGram_int (K : Type*) [CommRing K] [IsDomain K] [CharZero K] {A : Matrix (Fin k) (Fin k) ℤ}
    (hA : A.IsSymm) (x : Fin k → K) :
    (Siegel.ofGram A).evalIn K x = x ⬝ᵥ (A.map (Int.castRingHom K) *ᵥ x) := by
  have h1 := QuadForm.evalIn_eq_dotProduct K (Siegel.ofGram A) x
  have hH : (Siegel.ofGram A).hessian = (2 : ℤ) • A := by
    rw [Siegel.hessian_eq_two_smul_casselsMat (Siegel.ci_ofGram hA), Siegel.casselsMat_ofGram hA]
  have h2 : (2 : K) * (Siegel.ofGram A).evalIn K x =
      x ⬝ᵥ ((Siegel.ofGram A).hessian.map (Int.castRingHom K) *ᵥ x) := by
    rw [h1]
    simp only [QuadForm.hessian, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.add_apply,
      Matrix.transpose_apply, map_add, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib, two_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [algebraMap_int_eq, eq_intCast]
    ring
  rw [hH] at h2
  have h3 : (((2 : ℤ) • A).map (Int.castRingHom K)) = (2 : K) • A.map (Int.castRingHom K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat]
  rw [h3, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h2
  exact mul_left_cancel₀ two_ne_zero h2

/-- Helper: a common divisor of the coordinates of $C\mathbf x$, $C \in \mathrm{GL}_k(\mathbb Z)$, divides the coordinates of
$\mathbf x$. -/
theorem dvd_of_dvd_mulVec {C : Matrix (Fin k) (Fin k) ℤ} (hC : C.det = 1) {x : Fin k → ℤ} {e : ℤ}
    (h : ∀ i, e ∣ (C *ᵥ x) i) (i : Fin k) : e ∣ x i := by
  have hx : x = C.adjugate *ᵥ (C *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hC, one_smul, Matrix.one_mulVec]
  rw [hx]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (h j) _

/-- Helper: an odd prime does not divide a power of $2$. -/
theorem not_dvd_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) : ¬ (p : ℤ) ∣ 2 ^ k := by
  intro h
  have h' : p ∣ 2 ^ k := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))

/-! ### Local normal form at $q$ and approximation -/

section Local

variable {q : ℕ} [hq : Fact q.Prime]

/-- Helper: the form $2x_0x_2 + 2\delta x_1x_3$ over $\mathbb Z_q$ (Cassels' $2x_1x_3 + 2\delta x_2x_4$). -/
def hypForm (δ : ℤ_[q]) : QuadForm ℤ_[q] 4 :=
  QuadForm.ofUpper ![![0, 0, 2, 0], ![0, 0, 0, 2 * δ], ![0, 0, 0, 0], ![0, 0, 0, 0]]

/-- Helper: the Hessian of `hypForm δ`. -/
theorem hessian_hypForm (δ : ℤ_[q]) :
    (hypForm δ).hessian = !![0, 0, 2, 0; 0, 0, 0, 2 * δ; 2, 0, 0, 0; 0, 2 * δ, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypForm, QuadForm.hessian, QuadForm.ofUpper]

/-- Helper: the Hessian determinant of `hypForm δ` is $16\delta^2$. -/
theorem hessian_det_hypForm (δ : ℤ_[q]) : (hypForm δ).hessian.det = 16 * δ ^ 2 := by
  have e : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  rw [hessian_hypForm, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, e]
  ring

/-- Helper: `hypForm δ` vanishes on vectors with $x_2 = x_3 = 0$. -/
theorem eval_hypForm_of (δ : ℤ_[q]) (x : Fin 4 → ℤ_[q]) (h2 : x 2 = 0) (h3 : x 3 = 0) :
    (hypForm δ).eval x = 0 := by
  simp [hypForm, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four, h2, h3]

/-- Helper: an integer prime to $q$ is a $q$-adic unit, so not divisible by $q$ in $\mathbb Z_q$. -/
theorem not_dvd_of_isUnit {z : ℤ_[q]} (hz : IsUnit z) : ¬ (q : ℤ_[q]) ∣ z := fun h =>
  PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_unit h hz)

/-- Helper: for a classically integral $f$, `cassDet f` is the determinant of Cassels' matrix. -/
theorem cassDet_eq {f : QuadForm ℤ k} (hf : IsClassicallyIntegral f) :
    cassDet f = ((Siegel.casselsMat f).det : ℚ) := by
  rw [cassDet, Siegel.hessian_eq_two_smul_casselsMat hf, Matrix.det_smul, Fintype.card_fin]
  push_cast
  field_simp

/-- Helper: "$d \in U_q^2$" for an integer $d$ gives a $q$-adic unit $\delta$ with $\delta^2 = d$ in $\mathbb Z_q$. -/
theorem exists_sq_of_isUnitSquareAt {d : ℤ} (h : IsUnitSquareAt q (d : ℚ)) :
    ∃ δ : ℤ_[q], IsUnit δ ∧ δ ^ 2 = (d : ℤ_[q]) := by
  obtain ⟨u, hu, hu2⟩ := h
  refine ⟨u, hu, ?_⟩
  exact PadicInt.coe_inj.mp (by simpa using hu2)

/-- **Step 1 (local normal form).** If $f$ is classically integral in $4$ variables, $q \ne 2$ and $d(f) \in U_q^2$, there is
$T \in M_4(\mathbb Z_q)$ with $\det T = 1$ such that $f(T\mathbf x) = 0$ whenever $x_2 = x_3 = 0$ (the first two columns of $T$
span a totally isotropic plane). -/
theorem exists_isotropic_plane_local (hq2 : q ≠ 2) {f : QuadForm ℤ 4} (hf : IsClassicallyIntegral f)
    (hd : IsUnitSquareAt q (cassDet f)) :
    ∃ T : Matrix (Fin 4) (Fin 4) ℤ_[q], T.det = 1 ∧
      ∀ x : Fin 4 → ℤ_[q], x 2 = 0 → x 3 = 0 → f.evalIn ℤ_[q] (T *ᵥ x) = 0 := by
  rw [cassDet_eq hf] at hd
  obtain ⟨δ, hδu, hδ2⟩ := exists_sq_of_isUnitSquareAt hd
  set F := f.map (Int.castRingHom ℤ_[q])
  have hFdet : F.hessian.det = 16 * δ ^ 2 := by
    have hH : f.hessian.det = 16 * (Siegel.casselsMat f).det := by
      rw [Siegel.hessian_eq_two_smul_casselsMat hf, Matrix.det_smul, Fintype.card_fin]; norm_num
    rw [Siegel.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hH, map_mul, eq_intCast, eq_intCast,
      ← hδ2]
    norm_num
  have h16 : IsUnit (16 * δ ^ 2 : ℤ_[q]) := by
    refine IsUnit.mul ?_ (hδu.pow 2)
    have : ¬ ((q : ℤ) ∣ 16) := by
      have := not_dvd_two_pow hq.out hq2 4
      norm_num at this; exact this
    simpa using Binary.isUnit_intCast_padic this
  obtain ⟨g, hg⟩ := Kneser.isometricGL_of_unimodular hq2 F (hypForm δ)
    (by rw [hFdet]; exact not_dvd_of_isUnit h16) (by rw [hFdet, hessian_det_hypForm])
  -- normalize the determinant with `diag(det g⁻¹, 1, 1, 1)`
  have hgu : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  set D : Matrix (Fin 4) (Fin 4) ℤ_[q] := Matrix.diagonal (Function.update 1 0 (hgu.unit⁻¹ : ℤ_[q]ˣ).val) with hD
  refine ⟨g.val * D, ?_, fun x h2 h3 => ?_⟩
  · rw [Matrix.det_mul, hD, Matrix.det_diagonal, Fin.prod_univ_four]
    simp [Function.update]
  · rw [← Matrix.mulVec_mulVec, ← eval_map_eq_evalIn, hg]
    apply eval_hypForm_of
    · simp [hD, Matrix.mulVec_diagonal, Function.update, h2]
    · simp [hD, Matrix.mulVec_diagonal, Function.update, h3]

/-- Helper: $p$-adic closeness gives divisibility: $\lVert x\rVert < q^{-m}$ implies $x \in q^m\mathbb Z_q$. -/
theorem dvd_of_norm_lt {x : ℤ_[q]} {m : ℕ} (h : ‖x‖ < (q : ℝ) ^ (-(m : ℤ))) : (q : ℤ_[q]) ^ m ∣ x :=
  Ideal.mem_span_singleton.mp ((PadicInt.norm_le_pow_iff_mem_span_pow x m).mp h.le)

/-- Helper: divisibility of an integer by $q^m$ can be read in $\mathbb Z_q$. -/
theorem int_dvd_of_padic_dvd {z : ℤ} {m : ℕ} (h : (q : ℤ_[q]) ^ m ∣ (z : ℤ_[q])) : (q : ℤ) ^ m ∣ z := by
  rw [← PadicInt.norm_int_le_pow_iff_dvd]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ m).mpr (Ideal.mem_span_singleton.mpr h)

/-- **Step 2 (approximation).** Under the hypotheses of Step 1, for every $m$ there is $C \in M_4(\mathbb Z)$ with
$\det C = 1$ such that $q^m$ divides $f(C\mathbf x)$ for $\mathbf x = e_0, e_1, e_0 + e_1$ (so the entries $f'_{00}, f'_{11}$ and
$2f'_{01}$ of the form $f' = f \circ C$ are divisible by $q^m$). -/
theorem exists_good_basis (hq2 : q ≠ 2) {f : QuadForm ℤ 4} (hf : IsClassicallyIntegral f)
    (hd : IsUnitSquareAt q (cassDet f)) (m : ℕ) :
    ∃ C : Matrix (Fin 4) (Fin 4) ℤ, C.det = 1 ∧ ∀ x : Fin 4 → ℤ, x 2 = 0 → x 3 = 0 →
      (q : ℤ) ^ m ∣ f.eval (C *ᵥ x) := by
  obtain ⟨T, hTdet, hT⟩ := exists_isotropic_plane_local hq2 hf hd
  set qq : Nat.Primes := ⟨q, hq.out⟩
  have hε : (0 : ℝ) < (q : ℝ) ^ (-(m : ℤ)) := by
    have : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
    positivity
  obtain ⟨C, hCdet, hC⟩ := Siegel.exists_basis_approx (n := 4) (by norm_num) {qq} (δ := 1) (Or.inl rfl)
    (fun ⟨p, hp⟩ => by rw [Finset.mem_singleton] at hp; subst hp; exact T)
    (fun ⟨p, hp⟩ => by rw [Finset.mem_singleton] at hp; subst hp; exact hTdet) hε
  refine ⟨C, hCdet, fun x h2 h3 => ?_⟩
  have hCq := hC ⟨qq, Finset.mem_singleton_self qq⟩
  -- `C = T + q^m E` over `ℤ_q`
  have hE : ∀ i j, ∃ e : ℤ_[q], ((C i j : ℤ) : ℤ_[q]) = T i j + (q : ℤ_[q]) ^ m * e := by
    intro i j
    obtain ⟨e, he⟩ := dvd_of_norm_lt (hCq i j)
    exact ⟨e, by rw [← he]; ring⟩
  choose E₀ hE using hE
  set E : Matrix (Fin 4) (Fin 4) ℤ_[q] := Matrix.of E₀ with hEdef
  have hCm : C.map (Int.castRingHom ℤ_[q]) = T + (q : ℤ_[q]) ^ m • E := by
    ext i j; simp [hEdef, hE i j]
  have hvec : (fun i => ((C *ᵥ x) i : ℤ_[q])) =
      T *ᵥ (fun i => (x i : ℤ_[q])) + (q : ℤ_[q]) ^ m • (E *ᵥ (fun i => (x i : ℤ_[q]))) := by
    ext i
    rw [show ((C *ᵥ x) i : ℤ_[q]) = Int.castRingHom ℤ_[q] ((C *ᵥ x) i) from rfl, RingHom.map_mulVec, hCm,
      Matrix.add_mulVec, Matrix.smul_mulVec]
    rfl
  obtain ⟨r, hr⟩ := eval_add_smul ℤ_[q] (f.map (Int.castRingHom ℤ_[q])) (T *ᵥ fun i => (x i : ℤ_[q]))
    (E *ᵥ fun i => (x i : ℤ_[q])) ((q : ℤ_[q]) ^ m)
  rw [← hvec, eval_map_eq_evalIn, eval_map_eq_evalIn, Siegel.evalIn_intCast,
    hT _ (by simp [h2]) (by simp [h3]), zero_add] at hr
  exact int_dvd_of_padic_dvd ⟨r, hr⟩

end Local

/-! ### The form $g$ of (9.26) -/

section GForm

/-- The scaling vector $s = (1, 1, q^m, q^m)$ of (9.26). Arguments: `q` the prime, `m` the exponent. -/
def sVec (q m : ℕ) : Fin 4 → ℤ := ![1, 1, (q : ℤ) ^ m, (q : ℤ) ^ m]

/-- Cassels' matrix of $g$: $G_{ij} = q^{-m}A_{ij}s_is_j$, with $A$ Cassels' matrix of $f'$. Arguments: `q`, `m`, `A`. -/
def gMat (q m : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => A i j * sVec q m i * sVec q m j / (q : ℤ) ^ m

/-- **The form $g(\mathbf x) = q^{-m}f'(x_0, x_1, q^mx_2, q^mx_3)$ of (9.26).** Arguments: `q`, `m`, `A` (Cassels' matrix of $f'$). -/
def gForm (q m : ℕ) (A : Matrix (Fin 4) (Fin 4) ℤ) : QuadForm ℤ 4 := Siegel.ofGram (gMat q m A)

variable {q m : ℕ} {A : Matrix (Fin 4) (Fin 4) ℤ}

/-- Helper: $q^m$ divides every $A_{ij}s_is_j$ when it divides $A_{00}, A_{01}, A_{10}, A_{11}$. -/
theorem dvd_entry (h00 : (q : ℤ) ^ m ∣ A 0 0) (h01 : (q : ℤ) ^ m ∣ A 0 1) (h10 : (q : ℤ) ^ m ∣ A 1 0)
    (h11 : (q : ℤ) ^ m ∣ A 1 1) (i j : Fin 4) : (q : ℤ) ^ m ∣ A i j * sVec q m i * sVec q m j := by
  fin_cases i <;> fin_cases j <;> simp [sVec] <;>
    first
    | assumption
    | exact dvd_mul_of_dvd_right (dvd_refl _) _
    | exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    | exact Dvd.intro_left _ rfl
    | exact dvd_mul_left _ _

/-- Helper: $q^mG_{ij} = A_{ij}s_is_j$. -/
theorem gMat_mul (hdiv : ∀ i j, (q : ℤ) ^ m ∣ A i j * sVec q m i * sVec q m j) (i j : Fin 4) :
    (q : ℤ) ^ m * gMat q m A i j = A i j * sVec q m i * sVec q m j := by
  simp only [gMat, Matrix.of_apply]
  exact Int.mul_ediv_cancel' (hdiv i j)

/-- Helper: $G$ is symmetric when $A$ is. -/
theorem gMat_isSymm (hA : A.IsSymm) : (gMat q m A).IsSymm := by
  ext i j
  simp only [gMat, Matrix.transpose_apply, Matrix.of_apply]
  rw [hA.apply i j]
  ring_nf

/-- Helper: $q^m\,g(\mathbf x) = f'(s \odot \mathbf x)$ over any domain of characteristic zero. -/
theorem qpow_mul_evalIn_gForm (K : Type*) [CommRing K] [IsDomain K] [CharZero K] (hA : A.IsSymm)
    (hdiv : ∀ i j, (q : ℤ) ^ m ∣ A i j * sVec q m i * sVec q m j) (x : Fin 4 → K) :
    ((q : K) ^ m) * (gForm q m A).evalIn K x =
      (Siegel.ofGram A).evalIn K (fun i => (sVec q m i : K) * x i) := by
  rw [gForm, evalIn_ofGram_int K (gMat_isSymm hA), evalIn_ofGram_int K hA]
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg (Int.castRingHom K) (gMat_mul hdiv i j)
  simp only [map_mul, map_pow, map_natCast, eq_intCast] at h
  simp only [Matrix.map_apply, eq_intCast]
  linear_combination (x i * x j) * h

/-- Helper: the same identity over $\mathbb Z$. -/
theorem qpow_mul_eval_gForm (hA : A.IsSymm) (hdiv : ∀ i j, (q : ℤ) ^ m ∣ A i j * sVec q m i * sVec q m j)
    (x : Fin 4 → ℤ) :
    (q : ℤ) ^ m * (gForm q m A).eval x = (Siegel.ofGram A).eval (fun i => sVec q m i * x i) := by
  have := qpow_mul_evalIn_gForm ℤ hA hdiv x
  simpa using this

/-- Helper: $\det G = \det A$. -/
theorem det_gMat (hq : 0 < q) (hdiv : ∀ i j, (q : ℤ) ^ m ∣ A i j * sVec q m i * sVec q m j) :
    (gMat q m A).det = A.det := by
  have hM : (q : ℤ) ^ m • gMat q m A = Matrix.diagonal (sVec q m) * A * Matrix.diagonal (sVec q m) := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, gMat_mul hdiv, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  have h := congrArg Matrix.det hM
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Fintype.card_fin] at h
  simp only [sVec, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  have hq0 : ((q : ℤ) ^ m) ^ 4 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hq.ne'))
  apply mul_left_cancel₀ hq0
  rw [h]; ring

end GForm

/-! ### Lemma 9.1 -/

/-- Helper: if $M\mathbf y$ has a unit coordinate for a matrix $M$ over $\mathbb Z_p$, then so has $\mathbf y$. -/
theorem exists_isUnit_of_mulVec' {p : ℕ} [Fact p.Prime] {M : Matrix (Fin k) (Fin k) ℤ_[p]} {y : Fin k → ℤ_[p]}
    (h : ∃ i, IsUnit ((M *ᵥ y) i)) : ∃ i, IsUnit (y i) := by
  by_contra hno
  push Not at hno
  obtain ⟨i, hi⟩ := h
  have hmem : ∀ j, y j ∈ IsLocalRing.maximalIdeal ℤ_[p] := fun j =>
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hno j))
  have : (M *ᵥ y) i ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j)
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp this)) hi

/-- **Cassels, Ch. 11, Lemma 9.1** (p. 241), proved: the named statement `Lemma91` holds. Let $f$ be a positive definite
classically integral form in $4$ variables of determinant $d$, $a > 0$, $q \ne 2$ a prime with $q \nmid a$ and $d \in U_q^2$.
If $\mathcal R(g, a)$ holds for every positive definite classically integral quaternary $g$ with $d(g) = d$, then
$\mathcal R(f, q^ma)$ holds for every $m \ge 0$. See the module docstring for the proof. -/
@[kb "cassels1978" "Ch. 11, Lemma 9.1, pp. 241–242 (proof)"]
theorem lemma91_holds : Lemma91 := by
  refine ⟨fun Q hQ hci a ha q hq hq2 hqa hd hall m => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hall Q hQ hci rfl
  -- Step 2: the basis `C`
  obtain ⟨C, hCdet, hC⟩ := exists_good_basis hq2 hci hd m
  set A₀ := Siegel.casselsMat Q
  have hA₀ : A₀.IsSymm := Siegel.casselsMat_isSymm Q
  set A := Cᵀ * A₀ * C with hAdef
  have hA : A.IsSymm := by
    rw [hAdef, Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA₀.eq,
      Matrix.mul_assoc]
  set Q' := Siegel.ofGram A
  have hQ'eval : ∀ x, Q'.eval x = Q.eval (C *ᵥ x) := by
    intro x
    rw [Siegel.eval_ofGram hA, Siegel.eval_eq_casselsMat hci, hAdef, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hCu : IsUnit C.det := by rw [hCdet]; exact isUnit_one
  have hequiv : IsometricGL Q Q' := ⟨Matrix.nonsingInvUnit C hCu, fun x => (hQ'eval x).symm⟩
  -- it suffices to treat `Q'`
  refine locGlobal_of_isometricGL hequiv ?_
  -- divisibility of the entries `A₀₀, A₀₁, A₁₁`
  have hval : ∀ x : Fin 4 → ℤ, x 2 = 0 → x 3 = 0 → (q : ℤ) ^ m ∣ Q'.eval x := fun x h2 h3 => by
    rw [hQ'eval]; exact hC x h2 h3
  have hdiag : ∀ i : Fin 4, (i : ℕ) < 2 → A i i = Q'.eval (Pi.single i 1) := by
    intro i _
    rw [Siegel.eval_ofGram hA]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h00 : (q : ℤ) ^ m ∣ A 0 0 := by
    rw [hdiag 0 (by norm_num)]; exact hval _ (by simp) (by simp)
  have h11 : (q : ℤ) ^ m ∣ A 1 1 := by
    rw [hdiag 1 (by norm_num)]; exact hval _ (by simp) (by simp)
  have h01 : (q : ℤ) ^ m ∣ A 0 1 := by
    have hsum : Q'.eval (Pi.single 0 1 + Pi.single 1 1) = A 0 0 + 2 * A 0 1 + A 1 1 := by
      rw [Siegel.eval_ofGram hA]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.single_apply, hA.apply 1 0]
      ring
    have h2 : (q : ℤ) ^ m ∣ 2 * A 0 1 := by
      have := hval (Pi.single 0 1 + Pi.single 1 1) (by simp) (by simp)
      rw [hsum] at this
      have h' := dvd_sub (dvd_sub this h00) h11
      rwa [show A 0 0 + 2 * A 0 1 + A 1 1 - A 0 0 - A 1 1 = 2 * A 0 1 by ring] at h'
    have hcop : IsCoprime ((q : ℤ) ^ m) 2 := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := (Nat.coprime_primes hq.out Nat.prime_two).mpr hq2
      exact_mod_cast this
    exact hcop.dvd_of_dvd_mul_left h2
  have h10 : (q : ℤ) ^ m ∣ A 1 0 := by rw [hA.apply 0 1]; exact h01
  have hdiv := dvd_entry h00 h01 h10 h11
  -- Step 3: the form `g`
  set g := gForm q m A
  have hqpos : 0 < q := hq.out.pos
  have hgci : IsClassicallyIntegral g := Siegel.ci_ofGram (gMat_isSymm hA)
  have hgeval := qpow_mul_eval_gForm hA hdiv
  have hgpos : IntQF.PosDef g := by
    intro x hx
    have h1 := hgeval x
    have hsx : (fun i => sVec q m i * x i) ≠ 0 := by
      intro h0
      apply hx
      funext i
      have := congrFun h0 i
      have hs : sVec q m i ≠ 0 := by
        fin_cases i <;> simp [sVec] <;> intro h <;> omega
      simpa [hs] using this
    have hCx : C *ᵥ (fun i => sVec q m i * x i) ≠ 0 := by
      intro h0
      apply hsx
      have := congrArg (fun v => C.adjugate *ᵥ v) h0
      simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hCdet] using this
    have h2 := hQ _ hCx
    rw [← hQ'eval] at h2
    have hqm : (0 : ℤ) < (q : ℤ) ^ m := by positivity
    by_contra hle
    push Not at hle
    have : (q : ℤ) ^ m * g.eval x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hqm.le hle
    show False
    linarith [h1 ▸ h2]
  have hgdet : cassDet g = cassDet Q := by
    rw [cassDet_eq hgci, cassDet_eq hci, show Siegel.casselsMat g = gMat q m A from
      Siegel.casselsMat_ofGram (gMat_isSymm hA), det_gMat hqpos hdiv, hAdef, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, hCdet]
    simp [A₀]
  -- the entries of `G` in the block `x₂, x₃` are divisible by `q^m`
  have hq0 : (q : ℤ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hqpos.ne')
  have hGq : ∀ i j : Fin 4, 2 ≤ (i : ℕ) → 2 ≤ (j : ℕ) → gMat q m A i j = A i j * (q : ℤ) ^ m := by
    intro i j hi hj
    have h := gMat_mul hdiv i j
    have hs : ∀ l : Fin 4, 2 ≤ (l : ℕ) → sVec q m l = (q : ℤ) ^ m := by
      intro l hl
      fin_cases l <;> simp_all [sVec]
    rw [hs i hi, hs j hj] at h
    exact mul_left_cancel₀ hq0 (by rw [h]; ring)
  have hlow : ∀ (b : Fin 4 → ℤ) (i : Fin 4), (i : ℕ) < 2 → (q : ℤ) ∣ b 0 → (q : ℤ) ∣ b 1 → (q : ℤ) ∣ b i := by
    intro b i hi h0 h1
    fin_cases i <;> simp_all
  have hqg : ∀ b : Fin 4 → ℤ, (q : ℤ) ∣ b 0 → (q : ℤ) ∣ b 1 → (q : ℤ) ∣ g.eval b := by
    intro b h0 h1
    simp only [g, gForm]
    rw [Siegel.eval_ofGram (gMat_isSymm hA)]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
    by_cases hi : (i : ℕ) < 2
    · exact dvd_mul_of_dvd_left (hlow b i hi h0 h1) _
    · by_cases hj : (j : ℕ) < 2
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (hlow b j hj h0 h1) _) _
      · rw [hGq i j (by omega) (by omega)]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self _ hm.ne') _) _) _
  -- Step 5 (global), assuming Step 4
  intro hloc
  have hga : PrimRepZ g a := by
    refine hall g hgpos hgci hgdet fun p _ => ?_
    by_cases hpq : p = q
    · -- `p = q`: `g` is unimodular at `q`, hence equivalent to `2x₀x₂ + x₁² - d x₃²`
      subst hpq
      rw [cassDet_eq hci] at hd
      obtain ⟨δ, hδu, hδ2⟩ := exists_sq_of_isUnitSquareAt hd
      set d : ℤ := A₀.det
      set h' : QuadForm ℤ_[p] 4 :=
        QuadForm.ofUpper ![![0, 0, 2, 0], ![0, 1, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -(d : ℤ_[p])]]
      have hdh' : h'.hessian.det = 16 * (d : ℤ_[p]) := by
        have e : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
        rw [Matrix.det_succ_row_zero]
        simp [h', QuadForm.hessian, QuadForm.ofUpper, Fin.sum_univ_succ, Matrix.det_succ_row_zero, e]
        try push_cast
        ring
      have hGdet : (gMat p m A).det = d := by
        rw [det_gMat hqpos hdiv, hAdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hCdet]; simp [d]
      have hgH : (g.map (Int.castRingHom ℤ_[p])).hessian.det = 16 * (d : ℤ_[p]) := by
        have hGH : g.hessian.det = 16 * d := by
          rw [Siegel.hessian_eq_two_smul_casselsMat hgci,
            show Siegel.casselsMat g = gMat p m A from Siegel.casselsMat_ofGram (gMat_isSymm hA), Matrix.det_smul,
            Fintype.card_fin, hGdet]
          norm_num
        rw [Siegel.hessian_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hGH, map_mul, eq_intCast, eq_intCast]
        norm_num
      have h16 : IsUnit (16 * (d : ℤ_[p])) := by
        refine IsUnit.mul ?_ (by rw [← hδ2]; exact hδu.pow 2)
        have : ¬ ((p : ℤ) ∣ 16) := by
          have := not_dvd_two_pow (Fact.out : p.Prime) hq2 4
          norm_num at this; exact this
        simpa using Binary.isUnit_intCast_padic this
      obtain ⟨T2, hT2⟩ := Kneser.isometricGL_of_unimodular hq2 (g.map (Int.castRingHom ℤ_[p])) h'
        (by rw [hgH]; exact not_dvd_of_isUnit h16) (by rw [hgH, hdh'])
      have h2u : IsUnit (2 : ℤ_[p]) := by
        have : ¬ ((p : ℤ) ∣ 2) := by
          have := not_dvd_two_pow (Fact.out : p.Prime) hq2 1
          simpa using this
        simpa using Binary.isUnit_intCast_padic this
      obtain ⟨t, ht⟩ : ∃ t : ℤ_[p], 2 * t = 1 := ⟨((h2u.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), by simp⟩
      set z : Fin 4 → ℤ_[p] := ![1, 0, (a : ℤ_[p]) * t, 0]
      refine ⟨T2.val *ᵥ z, ?_, ?_⟩
      · refine exists_isUnit_of_mulVec' (M := (T2⁻¹ : GL (Fin 4) ℤ_[p]).val) ⟨0, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        simp [z]
      · rw [← eval_map_eq_evalIn, hT2]
        simp [h', z, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_four]
        linear_combination (a : ℤ_[p]) * ht
    · -- `p ≠ q`: from the primitive representation of `q^m a` by `Q'`
      obtain ⟨x, ⟨i₀, hi₀⟩, hx⟩ := hloc p
      have hqu : IsUnit ((q : ℤ_[p]) ^ m) := by
        refine IsUnit.pow _ ?_
        have : ¬ ((p : ℤ) ∣ q) := by
          intro h
          have : p ∣ q := Int.natCast_dvd_natCast.mp h
          exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out hq.out).mp this)
        simpa using Binary.isUnit_intCast_padic this
      set w : ℤ_[p] := ((hqu.unit⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      have hw : (q : ℤ_[p]) ^ m * w = 1 := by simp [w]
      have hwu : IsUnit w := (hqu.unit⁻¹).isUnit
      set ws : Fin 4 → ℤ_[p] := ![1, 1, w, w]
      have hws : ∀ i, ((sVec q m i : ℤ) : ℤ_[p]) * ws i = 1 := by
        intro i; fin_cases i <;> simp [sVec, ws, hw]
      have hwsu : ∀ i, IsUnit (ws i) := by
        intro i; fin_cases i <;> simp [ws, hwu]
      refine ⟨fun i => x i * ws i, ⟨i₀, hi₀.mul (hwsu i₀)⟩, ?_⟩
      have h1 := qpow_mul_evalIn_gForm ℤ_[p] hA hdiv (fun i => x i * ws i)
      have hsx : (fun i => ((sVec q m i : ℤ) : ℤ_[p]) * (x i * ws i)) = x := by
        funext i
        rw [← mul_assoc, mul_comm _ (x i), mul_assoc, hws, mul_one]
      rw [hsx, hx] at h1
      push_cast at h1
      exact mul_left_cancel₀ (hqu.ne_zero) h1
  obtain ⟨b, hb, hgb⟩ := hga
  refine ⟨fun i => sVec q m i * b i, ?_, ?_⟩
  · rw [gcd_eq_one_iff_forall_dvd] at hb ⊢
    intro e he
    have hpe : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
    by_cases hqe : (q : ℤ) ∣ e
    · exfalso
      have h0 : (q : ℤ) ∣ b 0 := by
        have := dvd_trans hqe (he 0); simpa [sVec] using this
      have h1 : (q : ℤ) ∣ b 1 := by
        have := dvd_trans hqe (he 1); simpa [sVec] using this
      exact hqa (hgb ▸ hqg b h0 h1)
    · have hcop : IsCoprime e ((q : ℤ) ^ m) :=
        IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hpe).mpr hqe).symm
      refine hb e fun i => ?_
      have := he i
      fin_cases i
      · simpa [sVec] using this
      · simpa [sVec] using this
      · exact hcop.dvd_of_dvd_mul_left (by simpa [sVec] using this)
      · exact hcop.dvd_of_dvd_mul_left (by simpa [sVec] using this)
  · rw [← hgeval, hgb]

/-- **Theorem 1.6 for $n = 4$** (Cassels, Ch. 11, pp. 242–243; classically integral forms), now conditional only on the named
statement `Lemma92` (the constant $N_1(f, q)$): `tartakowskyClassicalAt_four` with Lemma 9.1 supplied by `lemma91_holds`. -/
@[kb "cassels1978" "Ch. 11, Thm. 1.6 for n = 4, pp. 242–243 (conditional on Lemma 9.2 only)"]
theorem tartakowskyClassicalAt_four_of_lemma92 (h2 : Lemma92) : TartakowskyClassicalAt 4 :=
  tartakowskyClassicalAt_four lemma91_holds h2

end QuadFormsKB.Cassels.Ch11Lemma91
