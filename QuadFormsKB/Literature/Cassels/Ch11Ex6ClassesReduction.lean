/-
# Cassels, Chapter 11, Examples 6 and 7: the classes of a ternary genus by reduction and a finite check

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, Examples 6 and 7 (p. 252). The hint to
Example 6 allows the "heroic" way: enumerate the classes of positive definite ternary forms of the given determinant by
the reduction theory of Chapter 12 and sort them into genera. This file provides the generic machinery for that route;
the two examples are `Ch11Ex6Classes.lean` and `Ch11Ex7Classes.lean`.

**Notation.** A ternary integral form is written `tf a b c h g f`
$$= a x_0^2 + b x_1^2 + c x_2^2 + h x_0x_1 + g x_0x_2 + f x_1x_2,$$
with Hessian $\begin{pmatrix} 2a & h & g \\ h & 2b & f \\ g & f & 2c \end{pmatrix}$, and a sextuple
$t = (a, b, c, h, g, f)$ of integers (`Tup`) stands for the form `tupForm t = tf a b c h g f`.

**Proved (unconditionally).**
* `exists_reduced_tf`: every positive definite integral ternary form $Q$ is integrally equivalent to some
  `tf a b c h g f` satisfying the conditions `RedConds` ($0 < a \le b \le c$, $|h|, |g| \le a$, $|f| \le b$ and
  $a + b \pm h \pm g \pm f \ge 0$ for the four sign patterns of $Q(\pm e_0 \pm e_1 + e_2) \ge Q(e_2)$) and
  $4abc \le \det H_Q$. *Proof:* Minkowski reduction of the real Gram matrix $H_Q/2$
  (`Reduction.exists_isMinkowskiReduced`, Ch. 12, Thm. 1.1) and Gauss' inequality $f_{00}f_{11}f_{22} \le 2d$ for a
  reduced ternary form (`Reduction.example_3`, Ch. 12, Example 3).
* `mem_of_chkAll`: a Boolean check (`chkAll`, evaluated by the kernel) certifies that every reduced sextuple of a given
  determinant in a given box lies in an explicit list; $c$ is determined by the determinant, which is affine in $c$.
* `not_sameGenus_of_repB`: if a residue $m \bmod N$ is represented by exactly one of two forms, they are not in the same
  genus (the forms are equivalent modulo $N$ if they are in one genus, `SameGenus.isometricGL_zmod`).
* `classify_of_checks`: from these checks and per-sextuple verdicts (`verdict`: an equivalence certificate to $f$ or $g$,
  or a separating residue), every form in the genus of $f$ is equivalent to $f$ or to $g$.
-/
import QuadFormsKB.Literature.Cassels.Ch11Examples4
import QuadFormsKB.Literature.Cassels.Ch12.Examples
import QuadFormsKB.Siegel.KneserCert
import QuadFormsKB.Siegel.ThetaCuspidal

open Matrix QuadFormsKB.Siegel QuadFormsKB.Siegel.Kneser

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Ch11Ex4

/-! ### Ternary forms given by six coefficients -/

/-- **The ternary form** $a x_0^2 + b x_1^2 + c x_2^2 + h x_0x_1 + g x_0x_2 + f x_1x_2$ with integer coefficients
(upper-triangular coefficient matrix $\begin{pmatrix} a & h & g \\ 0 & b & f \\ 0 & 0 & c\end{pmatrix}$). -/
def tf (a b c h g f : ℤ) : QuadForm ℤ 3 := QuadForm.ofUpper ![![a, h, g], ![0, b, f], ![0, 0, c]]

/-- Helper: values of `tf a b c h g f`. -/
theorem eval_tf (a b c h g f : ℤ) (x : Fin 3 → ℤ) :
    (tf a b c h g f).eval x =
      a * x 0 ^ 2 + b * x 1 ^ 2 + c * x 2 ^ 2 + h * x 0 * x 1 + g * x 0 * x 2 + f * x 1 * x 2 := by
  simp [tf, QuadForm.eval, QuadForm.evalIn, QuadForm.ofUpper, Fin.sum_univ_three]
  ring

/-- Helper: the Hessian of `tf a b c h g f` is $\begin{pmatrix} 2a & h & g \\ h & 2b & f \\ g & f & 2c \end{pmatrix}$. -/
theorem hessian_tf (a b c h g f : ℤ) :
    (tf a b c h g f).hessian = !![2 * a, h, g; h, 2 * b, f; g, f, 2 * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tf, QuadForm.hessian, QuadForm.ofUpper] <;> ring

/-- **The Hessian determinant** of a ternary form in terms of its six coefficients:
$8abc + 2hgf - 2af^2 - 2bg^2 - 2ch^2$. -/
def tupDet (a b c h g f : ℤ) : ℤ := 8 * a * b * c + 2 * h * g * f - 2 * a * f * f - 2 * b * g * g - 2 * c * h * h

/-- Helper: $\det H$ of `tf a b c h g f` is `tupDet a b c h g f`. -/
theorem det_hessian_tf (a b c h g f : ℤ) : (tf a b c h g f).hessian.det = tupDet a b c h g f := by
  rw [hessian_tf, det_fin_three]
  simp [tupDet]
  ring

/-- **The reduction conditions** on the coefficients of `tf a b c h g f` (Minkowski reduction for ternary forms, in
the variables of the Hessian): $0 < a \le b \le c$, $|h| \le a$, $|g| \le a$, $|f| \le b$, and
$a + b + \epsilon_0\epsilon_1 h + \epsilon_0 g + \epsilon_1 f \ge 0$ for $\epsilon_0, \epsilon_1 = \pm 1$ (the conditions
$Q(\epsilon_0e_0 + \epsilon_1e_1 + e_2) \ge Q(e_2)$). -/
def RedConds (a b c h g f : ℤ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ -a ≤ h ∧ h ≤ a ∧ -a ≤ g ∧ g ≤ a ∧ -b ≤ f ∧ f ≤ b ∧
    0 ≤ a + b + h + g + f ∧ 0 ≤ a + b - h + g - f ∧ 0 ≤ a + b - h - g + f ∧ 0 ≤ a + b + h - g - f

instance (a b c h g f : ℤ) : Decidable (RedConds a b c h g f) := by unfold RedConds; infer_instance

/-! ### Minkowski reduction of an integral ternary form -/

/-- Helper: $\gcd(b_2) = 1$ for $\vec b = (e_0, e_1, 1)$ (the gcd condition of Ch. 12, (1.3) at $j = 2$). -/
theorem tailGcd_two (e0 e1 : ℤ) : Reduction.tailGcd (2 : Fin 3) ![e0, e1, 1] = 1 := by
  unfold Reduction.tailGcd
  have : (Finset.univ.filter fun k : Fin 3 => (2 : Fin 3) ≤ k) = {2} := by
    ext k; fin_cases k <;> simp
  rw [this, Finset.gcd_singleton]
  simp

/-- **Reduction of a positive definite integral ternary form** (Cassels, Ch. 12, Thm. 1.1 and Example 3, applied to
the Gram matrix $H_Q/2$): $Q$ is integrally equivalent to some `tf a b c h g f` whose coefficients satisfy the reduction
conditions `RedConds`, and $4abc \le \det H_Q$ (Gauss' bound $f_{00}f_{11}f_{22} \le 2\det(H_Q/2)$). -/
theorem exists_reduced_tf (Q : QuadForm ℤ 3) (hQ : IntQF.PosDef Q) :
    ∃ a b c h g f : ℤ, IntEquiv Q (tf a b c h g f) ∧ RedConds a b c h g f ∧ 4 * a * b * c ≤ Q.hessian.det := by
  obtain ⟨T, hT⟩ := Reduction.exists_isMinkowskiReduced (gramMatrix_posDef hQ)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A = T.valᵀ * Q.hessian * T.val := ⟨_, rfl⟩
  have hdiag : ∀ i, A i i = 2 * Q.eval (fun k => T.val k i) := by
    intro i
    rw [hAdef, Hermite.conj_apply, LocalDensity.two_mul_eval_eq_hessian]
  have hsym : ∀ i j, A j i = A i j := by
    intro i j
    have hs : Aᵀ = A := by
      rw [hAdef]
      simp [Matrix.transpose_mul, (LocalDensity.hessian_isSymm Q).eq, Matrix.mul_assoc]
    simpa [Matrix.transpose_apply] using congrFun (congrFun hs i) j
  have hAe : A = !![2 * Q.eval (fun k => T.val k 0), A 0 1, A 0 2;
      A 0 1, 2 * Q.eval (fun k => T.val k 1), A 1 2; A 0 2, A 1 2, 2 * Q.eval (fun k => T.val k 2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hdiag, hsym 0 1, hsym 0 2, hsym 1 2]
  have hF : ∀ i j, Reduction.act T.val (gramMatrix Q) i j = (A i j : ℝ) / 2 := by
    intro i j
    rw [hAdef]
    simp [Reduction.act, Reduction.castM, gramMatrix, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  have hdA : A.det = Q.hessian.det := by
    rw [hAdef, det_mul, det_mul, det_transpose]
    rcases Int.isUnit_iff.mp (Matrix.isUnits_det_units T) with h1 | h1 <;> rw [h1] <;> ring
  generalize Q.eval (fun k => T.val k 0) = a at hAe
  generalize Q.eval (fun k => T.val k 1) = b at hAe
  generalize Q.eval (fun k => T.val k 2) = c at hAe
  generalize A 0 1 = h at hAe
  generalize A 0 2 = g at hAe
  generalize A 1 2 = f at hAe
  rw [hAe] at hF hdA
  -- the entries of the reduced real Gram matrix
  have e00 : Reduction.act T.val (gramMatrix Q) 0 0 = a := by rw [hF]; simp
  have e11 : Reduction.act T.val (gramMatrix Q) 1 1 = b := by rw [hF]; simp
  have e22 : Reduction.act T.val (gramMatrix Q) 2 2 = c := by rw [hF]; simp
  have e01 : Reduction.act T.val (gramMatrix Q) 0 1 = h / 2 := by rw [hF]; simp
  have e10 : Reduction.act T.val (gramMatrix Q) 1 0 = h / 2 := by rw [hF]; simp
  have e02 : Reduction.act T.val (gramMatrix Q) 0 2 = g / 2 := by rw [hF]; simp
  have e20 : Reduction.act T.val (gramMatrix Q) 2 0 = g / 2 := by rw [hF]; simp
  have e12 : Reduction.act T.val (gramMatrix Q) 1 2 = f / 2 := by rw [hF]; simp
  have e21 : Reduction.act T.val (gramMatrix Q) 2 1 = f / 2 := by rw [hF]; simp
  refine ⟨a, b, c, h, g, f, ⟨T, (eval_mulVec_eq_iff_hessian Q _ T.val).mpr (by rw [← hAdef, hAe, hessian_tf])⟩,
    ?_, ?_⟩
  · -- the reduction conditions, from Minkowski reduction of the real Gram matrix
    have h01 := hT.abs_two_mul_le (i := 0) (j := 1) (by decide)
    have h02 := hT.abs_two_mul_le (i := 0) (j := 2) (by decide)
    have h12 := hT.abs_two_mul_le (i := 1) (j := 2) (by decide)
    have hab := hT.diag_mono (i := 0) (j := 1) (by decide)
    have hbc := hT.diag_mono (i := 1) (j := 2) (by decide)
    have ha := hT.1.diag_pos (i := 0)
    have hred := ((Reduction.isMinkowskiReduced_iff_gcd _).1 hT).2 2
    have s1 := hred ![1, 1, 1] (tailGcd_two 1 1)
    have s2 := hred ![1, -1, 1] (tailGcd_two 1 (-1))
    have s3 := hred ![-1, 1, 1] (tailGcd_two (-1) 1)
    have s4 := hred ![-1, -1, 1] (tailGcd_two (-1) (-1))
    rw [e00, e01] at h01
    rw [e00, e02] at h02
    rw [e11, e12] at h12
    rw [e00, e11] at hab
    rw [e11, e22] at hbc
    rw [e00] at ha
    simp only [Reduction.val, Reduction.cast, dotProduct, Matrix.mulVec, Fin.sum_univ_three,
      e00, e11, e22, e01, e10, e02, e20, e12, e21] at s1 s2 s3 s4
    norm_num at s1 s2 s3 s4
    rw [abs_le] at h01 h02 h12
    obtain ⟨h01l, h01r⟩ := h01
    obtain ⟨h02l, h02r⟩ := h02
    obtain ⟨h12l, h12r⟩ := h12
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast ha
    · exact_mod_cast hab
    · exact_mod_cast hbc
    · have : (-a : ℝ) ≤ h := by linarith
      exact_mod_cast this
    · have : (h : ℝ) ≤ a := by linarith
      exact_mod_cast this
    · have : (-a : ℝ) ≤ g := by linarith
      exact_mod_cast this
    · have : (g : ℝ) ≤ a := by linarith
      exact_mod_cast this
    · have : (-b : ℝ) ≤ f := by linarith
      exact_mod_cast this
    · have : (f : ℝ) ≤ b := by linarith
      exact_mod_cast this
    · have : (0 : ℝ) ≤ a + b + h + g + f := by linarith
      exact_mod_cast this
    · have : (0 : ℝ) ≤ a + b - h + g - f := by linarith
      exact_mod_cast this
    · have : (0 : ℝ) ≤ a + b - h - g + f := by linarith
      exact_mod_cast this
    · have : (0 : ℝ) ≤ a + b + h - g - f := by linarith
      exact_mod_cast this
  · -- Gauss' bound
    have hex := Reduction.example_3 hT
    rw [Matrix.det_fin_three] at hex
    simp only [e00, e11, e22, e01, e10, e02, e20, e12, e21] at hex
    have key : (4 * a * b * c : ℝ) ≤
        8 * a * b * c + 2 * h * g * f - 2 * a * f * f - 2 * b * g * g - 2 * c * h * h := by
      nlinarith [hex]
    have key' : 4 * a * b * c ≤ 8 * a * b * c + 2 * h * g * f - 2 * a * f * f - 2 * b * g * g - 2 * c * h * h := by
      exact_mod_cast key
    rw [← hdA, det_fin_three]
    simp
    nlinarith [key']

/-! ### The finite check of the reduced sextuples -/

/-- **A sextuple of integers** $(a, b, c, h, g, f)$, standing for the ternary form `tf a b c h g f`. -/
abbrev Tup := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

/-- The ternary form `tf a b c h g f` of a sextuple $t = (a, b, c, h, g, f)$. -/
def tupForm (t : Tup) : QuadForm ℤ 3 := tf t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- The values $a x_0^2 + b x_1^2 + c x_2^2 + h x_0x_1 + g x_0x_2 + f x_1x_2$ of the form of a sextuple, as a
polynomial function of $x_0, x_1, x_2$ (for kernel evaluation). -/
def tpoly (t : Tup) (x0 x1 x2 : ℤ) : ℤ :=
  t.1 * x0 * x0 + t.2.1 * x1 * x1 + t.2.2.1 * x2 * x2 + t.2.2.2.1 * x0 * x1 + t.2.2.2.2.1 * x0 * x2 +
    t.2.2.2.2.2 * x1 * x2

/-- Helper: the values of `tupForm t` are given by `tpoly t`. -/
theorem eval_tupForm (t : Tup) (x : Fin 3 → ℤ) : (tupForm t).eval x = tpoly t (x 0) (x 1) (x 2) := by
  rw [tupForm, eval_tf, tpoly]
  ring

/-- The integers $lo, lo + 1, \dots, hi$ as a list. -/
def intRange (lo hi : ℤ) : List ℤ := (List.range (hi - lo + 1).toNat).map fun i : ℕ => lo + (i : ℤ)

/-- Helper: $lo \le x \le hi$ implies $x \in$ `intRange lo hi`. -/
theorem mem_intRange {lo hi x : ℤ} (h1 : lo ≤ x) (h2 : x ≤ hi) : x ∈ intRange lo hi := by
  simp only [intRange, List.mem_map]
  refine ⟨(x - lo).toNat, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · omega

/-- **The check of one quintuple** $(a, b, h, g, f)$ for the determinant $D$ and the list $L$: with
$c = (D - 2hgf + 2af^2 + 2bg^2) / (2(4ab - h^2))$ (the only candidate, as $\det H$ is affine in $c$), either the
sextuple $(a, b, c, h, g, f)$ fails one of $\det = D$, `RedConds`, $4abc \le D$, or it lies in $L$. -/
def chkOne (D : ℤ) (L : List Tup) (a b h g f : ℤ) : Bool :=
  let c := (D - (2 * h * g * f - 2 * a * f * f - 2 * b * g * g)) / (2 * (4 * a * b - h * h))
  !(decide (tupDet a b c h g f = D) && decide (RedConds a b c h g f) && decide (4 * a * b * c ≤ D)) ||
    decide ((a, b, c, h, g, f) ∈ L)

/-- **The check of all quintuples** with $1 \le a \le A$, $a \le b \le B$, $|h|, |g| \le a$, $|f| \le b$. -/
def chkAll (D A B : ℤ) (L : List Tup) : Bool :=
  (intRange 1 A).all fun a => (intRange a B).all fun b => (intRange (-a) a).all fun h =>
    (intRange (-a) a).all fun g => (intRange (-b) b).all fun f => chkOne D L a b h g f

/-- **Soundness of `chkAll`:** if the check succeeds, every sextuple satisfying the reduction conditions with
$\det H = D$, $4abc \le D$, $a \le A$, $b \le B$ is in the list $L$. -/
theorem mem_of_chkAll {D A B : ℤ} {L : List Tup} (hchk : chkAll D A B L = true) {a b c h g f : ℤ}
    (hred : RedConds a b c h g f) (hdet : tupDet a b c h g f = D) (h4 : 4 * a * b * c ≤ D) (hA : a ≤ A)
    (hB : b ≤ B) : ((a, b, c, h, g, f) : Tup) ∈ L := by
  obtain ⟨ha, hab, hbc, hh1, hh2, hg1, hg2, hf1, hf2, -⟩ := id hred
  simp only [chkAll, List.all_eq_true] at hchk
  have := hchk a (mem_intRange (by omega) hA) b (mem_intRange hab hB) h (mem_intRange hh1 hh2)
    g (mem_intRange hg1 hg2) f (mem_intRange hf1 hf2)
  have hM : 2 * (4 * a * b - h * h) ≠ 0 := by
    have h1 : h * h ≤ a * a := by nlinarith
    have h2 : a * a ≤ a * b := by nlinarith
    have h3 : 0 < a * b := by nlinarith
    exact ne_of_gt (by linarith)
  have hc : (D - (2 * h * g * f - 2 * a * f * f - 2 * b * g * g)) / (2 * (4 * a * b - h * h)) = c := by
    rw [show D - (2 * h * g * f - 2 * a * f * f - 2 * b * g * g) = c * (2 * (4 * a * b - h * h)) by
      rw [← hdet]; unfold tupDet; ring]
    exact Int.mul_ediv_cancel c hM
  simp only [chkOne, hc] at this
  simpa [hdet, h4, hred] using this

/-! ### A genus invariant: the residues represented modulo $N$ -/

/-- **Residues represented modulo $N$ are a genus invariant:** if $Q$ and $Q'$ are in the same genus, then
$Q(\vec x) \equiv m$ is solvable in $(\mathbb Z/N)^n$ iff $Q'(\vec x) \equiv m$ is (`SameGenus.isometricGL_zmod`). -/
theorem rep_zmod_iff_of_sameGenus {n : ℕ} {Q Q' : QuadForm ℤ n} (h : SameGenus Q Q') {N : ℕ} (hN : N ≠ 0)
    (m : ZMod N) :
    (∃ x, (Q.map (Int.castRingHom (ZMod N))).eval x = m) ↔
      (∃ x, (Q'.map (Int.castRingHom (ZMod N))).eval x = m) := by
  obtain ⟨g, hg⟩ := h.isometricGL_zmod hN
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(g⁻¹).val *ᵥ x, ?_⟩
    rw [← hg, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, hx]
  · rintro ⟨x, hx⟩
    exact ⟨g.val *ᵥ x, by rw [hg, hx]⟩

/-- **Is the residue $m$ represented modulo $N$** by the form of the sextuple $t$: a search over
$\{0, \dots, N-1\}^3$ (for kernel evaluation). -/
def repB (t : Tup) (N : ℕ) (m : ℤ) : Bool :=
  (List.range N).any fun i => (List.range N).any fun j => (List.range N).any fun k =>
    decide (tpoly t i j k % N = m)

/-- **Correctness of `repB`:** for $0 \le m < N$, `repB t N m` holds iff $m$ is represented modulo $N$ by `tupForm t`. -/
theorem repB_iff (t : Tup) {N : ℕ} (hN : N ≠ 0) {m : ℤ} (hm0 : 0 ≤ m) (hmN : m < N) :
    repB t N m = true ↔ ∃ x : Fin 3 → ZMod N, ((tupForm t).map (Int.castRingHom (ZMod N))).eval x = (m : ZMod N) := by
  have : NeZero N := ⟨hN⟩
  have hev : ∀ y : Fin 3 → ℤ, ((tupForm t).map (Int.castRingHom (ZMod N))).eval (fun i => (y i : ZMod N)) =
      ((tpoly t (y 0) (y 1) (y 2) : ℤ) : ZMod N) := by
    intro y
    rw [← eval_tupForm]
    exact (map_eval_eq (Int.castRingHom (ZMod N)) (tupForm t) y).symm
  simp only [repB, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, j, hj, k, hk, he⟩
    refine ⟨fun l => ((![(i : ℤ), j, k] l : ℤ) : ZMod N), ?_⟩
    rw [hev]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← ZMod.intCast_mod, he]
  · rintro ⟨x, hx⟩
    have hxy : x = fun l => (((x l).val : ℤ) : ZMod N) := by
      funext l; simp
    rw [hxy, hev] at hx
    have h2 := (ZMod.intCast_eq_intCast_iff' _ _ N).mp hx
    rw [Int.emod_eq_of_lt hm0 hmN] at h2
    exact ⟨(x 0).val, ZMod.val_lt _, (x 1).val, ZMod.val_lt _, (x 2).val, ZMod.val_lt _, h2⟩

/-- **Separation by a residue:** if the residue $m$ ($0 \le m < N$) is represented modulo $N$ by exactly one of the forms
of $s$ and $t$, these forms are not in the same genus. -/
theorem not_sameGenus_of_repB {s t : Tup} {N : ℕ} (hN : N ≠ 0) {m : ℤ} (hm0 : 0 ≤ m) (hmN : m < N)
    (hne : repB s N m ≠ repB t N m) : ¬ SameGenus (tupForm s) (tupForm t) := by
  intro h
  apply hne
  have := rep_zmod_iff_of_sameGenus h hN (m : ZMod N)
  rw [← repB_iff s hN hm0 hmN, ← repB_iff t hN hm0 hmN] at this
  exact Bool.eq_iff_iff.mpr this

/-! ### Verdicts and the classification -/

/-- **The verdict on a sextuple $t$** (for the genus of the form of $f_T$, with second class $g_T$): an equivalence
certificate from `tupForm fT` or from `tupForm gT` to `tupForm t` (lists `isoF`, `isoG`), or a separating residue
$m \bmod N$ (list `seps` of $(t, N, m)$). -/
def verdict (fT gT : Tup) (isoF isoG : List (Tup × IsoCert 3)) (seps : List (Tup × ℕ × ℤ)) (t : Tup) : Bool :=
  (isoF.any fun e => decide (e.1 = t) && decide (e.2.Valid (tupForm fT) (tupForm t))) ||
    (isoG.any fun e => decide (e.1 = t) && decide (e.2.Valid (tupForm gT) (tupForm t))) ||
    (seps.any fun e => decide (e.1 = t) && decide (e.2.1 ≠ 0) && decide (0 ≤ e.2.2) &&
      decide (e.2.2 < (e.2.1 : ℤ)) && (repB fT e.2.1 e.2.2 != repB t e.2.1 e.2.2))

/-- **Soundness of a verdict:** if the verdict on $t$ holds and the form of $t$ is in the genus of the form of $f_T$,
it is equivalent to the form of $f_T$ or to that of $g_T$. -/
theorem verdict_sound {fT gT : Tup} {isoF isoG : List (Tup × IsoCert 3)} {seps : List (Tup × ℕ × ℤ)} {t : Tup}
    (hv : verdict fT gT isoF isoG seps t = true) (hg : SameGenus (tupForm fT) (tupForm t)) :
    IntEquiv (tupForm fT) (tupForm t) ∨ IntEquiv (tupForm gT) (tupForm t) := by
  simp only [verdict, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv with (⟨e, -, rfl, he⟩ | ⟨e, -, rfl, he⟩) | ⟨e, -, ⟨⟨⟨⟨rfl, hN⟩, hm0⟩, hmN⟩, hne⟩⟩
  · exact Or.inl (IsoCert.intEquiv he)
  · exact Or.inr (IsoCert.intEquiv he)
  · exact absurd hg (not_sameGenus_of_repB hN hm0 hmN (by simpa using hne))

/-- **The classification from the finite checks.** Let $f$ = `tupForm fT` be positive definite with $\det H_f = D$.
Assume (`hA`) that the reduction conditions with $4abc \le D$ force $a \le A$ and $b \le B$, that `chkAll D A B L`
succeeds, and that the verdict holds on every sextuple of $L$. Then every form $Q'$ in the genus of $f$ is integrally
equivalent to $f$ or to $g$ = `tupForm gT`. -/
theorem classify_of_checks (fT gT : Tup) (D A B : ℤ) (L : List Tup) (isoF isoG : List (Tup × IsoCert 3))
    (seps : List (Tup × ℕ × ℤ)) (hpos : IntQF.PosDef (tupForm fT)) (hdet : (tupForm fT).hessian.det = D)
    (hA : ∀ a b c : ℤ, 0 < a → a ≤ b → b ≤ c → 4 * a * b * c ≤ D → a ≤ A ∧ b ≤ B)
    (hchk : chkAll D A B L = true) (hver : L.all (verdict fT gT isoF isoG seps) = true)
    (Q' : QuadForm ℤ 3) (h : SameGenus (tupForm fT) Q') :
    IntEquiv (tupForm fT) Q' ∨ IntEquiv (tupForm gT) Q' := by
  have hQ' : IntQF.PosDef Q' := h.posDef hpos
  obtain ⟨a, b, c, hh, g, f, heq, hred, h4⟩ := exists_reduced_tf Q' hQ'
  have hdetQ' : Q'.hessian.det = D := by rw [← hdet]; exact (SameGenus.det_hessian_eq hpos h).symm
  have hdett : tupDet a b c hh g f = D := by
    rw [← det_hessian_tf, ← hdetQ']
    exact (SameGenus.det_hessian_eq hQ' heq.sameGenus).symm
  rw [hdetQ'] at h4
  obtain ⟨hA', hB'⟩ := hA a b c hred.1 hred.2.1 hred.2.2.1 h4
  have hmem := mem_of_chkAll hchk hred hdett h4 hA' hB'
  have hv := List.all_eq_true.mp hver _ hmem
  have hsg : SameGenus (tupForm fT) (tupForm (a, b, c, hh, g, f)) := h.trans heq.sameGenus
  rcases verdict_sound hv hsg with e | e
  · exact Or.inl (IsometricGL.trans e (IsometricGL.symm heq))
  · exact Or.inr (IsometricGL.trans e (IsometricGL.symm heq))

/-- **Two classes:** if every form of the genus of $f$ is equivalent to $f$ or to $g$, $g$ is in the genus and
$f \not\sim g$, the genus of $f$ has exactly two classes. -/
theorem ncard_genusClasses_eq_two {Q Q₂ : QuadForm ℤ 3} (h₂ : SameGenus Q Q₂) (hne : ¬ IntEquiv Q Q₂)
    (hcl : ∀ Q' : QuadForm ℤ 3, SameGenus Q Q' → IntEquiv Q Q' ∨ IntEquiv Q₂ Q') :
    (genusClasses Q).ncard = 2 := by
  have he : genusClasses Q = {classOf Q, classOf Q₂} := by
    ext c
    induction c using Quotient.inductionOn with
    | h Q' =>
      change classOf Q' ∈ _ ↔ classOf Q' ∈ _
      rw [classOf_mem_genusClasses_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, classOf_eq_classOf_iff]
      constructor
      · intro hQ'
        rcases hcl Q' hQ' with e | e
        · exact Or.inl (IsometricGL.symm e)
        · exact Or.inr (IsometricGL.symm e)
      · rintro (e | e)
        · exact IntEquiv.sameGenus (IsometricGL.symm e)
        · exact h₂.trans (IntEquiv.sameGenus (IsometricGL.symm e))
  rw [he, Set.ncard_pair (fun e => hne (classOf_eq_classOf_iff.mp e))]

end QuadFormsKB.Cassels.Ch11Ex4
