/-
# Cassels, Chapter 14, §4: the proper automorphs $O^{+}$ and the number of ambiguous forms in a class

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §4, pp. 342–343 (the discussion before and the proof of
Lemma 4.3), using Ch. 13, §3 (Theorem 3.1, Lemma 3.2, Example 1). Coverage row 14.r8.

Let $f = [a, b, c]$, $f(x, y) = a x^2 + b xy + c y^2$, be a primitive integral binary form of discriminant
$D = b^2 - 4ac \ne 0$ (`BinQF`, `BinQF.IsPrimitive`, `BinQF.disc`) and $O^{+}(f) = $ `Siegel.AutPlus f` the group of its
proper integral automorphs (matrices $T \in \mathrm{SL}_2(\mathbb Z)$ with $f(T\vec x) = f(\vec x)$, as a subgroup of
`GL (Fin 2) ℤ`). Indices are 0-based throughout.

**(a) The structure of $O^{+}(f)$** (the four cases printed on p. 343):
* `card_autPlus_of_neg_other`: $|O^{+}| = 2$ for $D < -4$ (namely $\{\pm 1\}$);
* `card_autPlus_of_disc_neg_four`, `card_autPlus_of_disc_neg_three`: $|O^{+}| = 4$ for $D = -4$ and $6$ for $D = -3$;
* `card_autPlus_of_pos_sq`: $|O^{+}| = 2$ for $D > 0$ a perfect square;
* `autPlus_equiv_of_pos_nonsq`: for $D > 0$ not a perfect square, $O^{+} \cong \{\pm 1\} \times \mathbb Z$ (a group
  isomorphism with `ℤˣ × Multiplicative ℤ`), i.e. every element is $\pm T_0^{k}$ for a unique sign and a unique
  $k \in \mathbb Z$ with $T_0$ of infinite order;
* `autSL_comm`: $O^{+}$ is abelian (for every $D \ne 0$; Cassels reads this off the four cases).
* `isCyclic_autPlus`: in the cases $D < 0$ and $D > 0$ a square the group is cyclic (Cassels' "cyclic of order $4$ or
  $6$" and "cyclic of order $2$"); the proof uses that the group is abelian with exactly two elements of order dividing
  $2$ (`card_sq_eq_one`).

*Proof route.* A primitive form $f$ is proportional to a classical form $A x^2 + 2B xy + C y^2$ (`Reduction.cform`)
with $\gcd(A, B, C) = 1$: $(A, B, C) = (a, b/2, c)$ if $b$ is even and $(2a, b, 2c)$ if $b$ is odd
(`exists_cform_data`); proportional forms have the same automorphs (`autPlus_eq_of_eval_smul`), so the results of Ch. 13
apply: Example 1 (`Reduction.example_1`) for the definite case, Lemma 3.2 (`Reduction.binary_isotropic_aut`) for a
square discriminant, Theorem 3.1 (`Reduction.autPlus_cform_cyclic`) for the nonsquare case. The shape of
the group in the last case is obtained by `exists_mulEquiv_of_pm_pow`.

**(b) The count** (`ncard_ambiguousForms_eq_index`, `ncard_ambiguousForms_in_class`): if the class of $f$ is ambiguous,
the number of ambiguous forms ($[a, 0, c]$ or $[a, a, c]$, `IsAmbiguousForm`) properly equivalent to $f$ equals the
index of the subgroup of squares of $O^{+}(f)$, i.e. the order of $O^{+}/(O^{+})^2$ (Cassels' argument: the improper
automorphs are $S' = TS$ with $T \in O^{+}$ and $S$ one fixed improper automorph; the ambiguous form attached to $S'$ is
unchanged exactly when $S'$ is replaced by $T' S' T'^{-1} = T'^2 S'$, $T' \in O^{+}$). The proof here is the same:
an improper automorph is an involution (4.2) conjugate in $\mathrm{SL}_2(\mathbb Z)$ to one of two standard matrices
`Rk false`, `Rk true` (4.3)–(4.5, `exists_conj_rk`), the ambiguous forms of the class correspond to the conjugacy
classes of improper automorphs under $O^{+}$ (`isRel_iff`), and these correspond to the cosets of the squares
(`card_conj_quotient`). The index is computed in each case (`index_squares_autPlus`, the group-theoretic part of
Lemma 4.3) and combined with the count in `ncard_ambiguousForms_in_class_eq`, which is **Lemma 4.3**: the number is
$4$ if $D > 0$ is not a perfect square and $2$ otherwise.

*Generalization.* The count (b) and the commutativity of $O^{+}$ hold for every binary form of nonzero discriminant
(primitivity is not used); primitivity is used in (a) and in the case computation of the index.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Ambiguous
import QuadFormsKB.Literature.Cassels.Ch13.Examples
import QuadFormsKB.Binary.FormAut

open Matrix

namespace QuadFormsKB.Composition

open BinQF Binary Reduction

/-! ### Plumbing: forms and matrices -/

/-- Helper: the form $g \circ M$, $(x, y) \mapsto g(M(x, y)^{\mathsf T})$, for $M \in \mathrm{GL}_2(\mathbb Z)$. -/
def actForm (g : BinQF) (M : GL (Fin 2) ℤ) : BinQF :=
  BinQF.subst (M.val 0 0) (M.val 0 1) (M.val 1 0) (M.val 1 1) g

/-- Helper: `actForm g M = h` iff $g(M\vec x) = h(\vec x)$ for all $\vec x \in \mathbb Z^2$ (`g h`: forms; `M`: the matrix). -/
theorem actForm_eq_iff {g h : BinQF} {M : GL (Fin 2) ℤ} :
    actForm g M = h ↔ ∀ x, QuadForm.eval g (M.val *ᵥ x) = QuadForm.eval h x :=
  (forall_eval_mulVec_iff g h M.val).symm

/-- Helper: the value of `actForm g M` at $\vec x$ is $g(M \vec x)$ (`g`: form; `M`: matrix; `x`: integer vector). -/
theorem eval_actForm (g : BinQF) (M : GL (Fin 2) ℤ) (x : Fin 2 → ℤ) :
    QuadForm.eval (actForm g M) x = QuadForm.eval g (M.val *ᵥ x) :=
  (actForm_eq_iff.mp rfl x).symm

/-- Helper: substituting the identity matrix does not change the form `g`. -/
theorem actForm_one (g : BinQF) : actForm g 1 = g :=
  actForm_eq_iff.mpr (fun x => by simp)

/-- Helper: two binary forms `g h` with the same values on all integer vectors are equal. -/
theorem ext_eval_vec {g h : BinQF} (H : ∀ x : Fin 2 → ℤ, QuadForm.eval g x = QuadForm.eval h x) :
    g = h := by
  rw [← actForm_one g]
  exact actForm_eq_iff.mpr (fun x => by simpa using H x)

/-- Helper: $(g \circ M) \circ N = g \circ (M N)$ (`g`: form; `M N`: matrices). -/
theorem actForm_mul (g : BinQF) (M N : GL (Fin 2) ℤ) :
    actForm g (M * N) = actForm (actForm g M) N := by
  apply ext_eval_vec
  intro x
  rw [eval_actForm, eval_actForm, eval_actForm, Units.val_mul, Matrix.mulVec_mulVec]

/-- Helper: `M` is an automorph of `f` iff `actForm f M = f` (`f`: form; `M`: matrix). -/
theorem mem_aut_iff_actForm {f : BinQF} {M : GL (Fin 2) ℤ} :
    M ∈ Siegel.Aut f ↔ actForm f M = f := mem_aut_iff

/-- Helper: the matrix $-1$ is an automorph of every form `g`. -/
theorem actForm_neg_one (g : BinQF) : actForm g (-1) = g := by
  unfold actForm
  have h00 : ((-1 : GL (Fin 2) ℤ).val 0 0) = -1 := by simp
  have h01 : ((-1 : GL (Fin 2) ℤ).val 0 1) = 0 := by simp
  have h10 : ((-1 : GL (Fin 2) ℤ).val 1 0) = 0 := by simp
  have h11 : ((-1 : GL (Fin 2) ℤ).val 1 1) = -1 := by simp
  rw [h00, h01, h10, h11]
  apply ext_abc <;> simp [BinQF.subst]

/-- Helper: the improper involution $\mathrm{diag}(1,-1)$ ($k$ false) or $\begin{pmatrix}1&1\\0&-1\end{pmatrix}$
($k$ true) as a matrix. -/
def Rm : Bool → Matrix (Fin 2) (Fin 2) ℤ
  | false => !![1, 0; 0, -1]
  | true => !![1, 1; 0, -1]

/-- Helper: `Rm k` as an element of $\mathrm{GL}_2(\mathbb Z)$. -/
noncomputable def Rk : Bool → GL (Fin 2) ℤ
  | false => Binary.glOf 1 0 0 (-1) (by norm_num)
  | true => Binary.glOf 1 1 0 (-1) (by norm_num)

/-- Helper: the matrix of `Rk k` is `Rm k` (`k`: Boolean selecting the standard involution). -/
theorem Rk_val (k : Bool) : (Rk k).val = Rm k := by cases k <;> rfl

/-- Helper: $\det$ of `Rk k` is $-1$ (`k`: Boolean selecting the standard involution). -/
theorem det_Rk (k : Bool) : (Rk k).val.det = -1 := by
  rw [Rk_val]; cases k <;> simp [Rm, Matrix.det_fin_two_of]

/-- Helper: `Rk k` is an involution (`k`: Boolean selecting the standard involution). -/
theorem Rk_mul_self (k : Bool) : Rk k * Rk k = 1 := by
  apply Units.ext
  rw [Units.val_mul, Rk_val]
  cases k <;> (ext i j; fin_cases i <;> fin_cases j <;> simp [Rm, Matrix.mul_apply, Fin.sum_univ_two])

/-- Helper: $g \circ \mathrm{diag}(1, -1) = [a, -b, c]$ for $g = [a, b, c]$. -/
theorem actForm_Rk_false (g : BinQF) :
    actForm g (Rk false) = BinQF.mk g.a (-g.b) g.c := by
  unfold actForm
  have : (Rk false).val = !![1, 0; 0, -1] := Rk_val false
  rw [this]
  apply ext_abc <;> simp [BinQF.subst]

/-- Helper: $g \circ \begin{pmatrix} 1 & 1 \\ 0 & -1 \end{pmatrix} = [a, 2a - b, a - b + c]$ for $g = [a, b, c]$. -/
theorem actForm_Rk_true (g : BinQF) :
    actForm g (Rk true) = BinQF.mk g.a (2 * g.a - g.b) (g.a - g.b + g.c) := by
  unfold actForm
  have : (Rk true).val = !![1, 1; 0, -1] := Rk_val true
  rw [this]
  apply ext_abc <;> simp [BinQF.subst] <;> ring

/-- Helper: the form `g` is fixed by $\mathrm{diag}(1, -1)$ iff $b = 0$ (ambiguous form of the first kind, (4.6)). -/
theorem actForm_Rk_false_eq_self_iff (g : BinQF) : actForm g (Rk false) = g ↔ g.b = 0 := by
  rw [actForm_Rk_false]
  constructor
  · intro h; have := congrArg BinQF.b h; simp at this; omega
  · intro h; apply ext_abc <;> simp [h]

/-- Helper: the form `g` is fixed by $\begin{pmatrix} 1 & 1 \\ 0 & -1 \end{pmatrix}$ iff $b = a$ (ambiguous form of the second kind, (4.7)). -/
theorem actForm_Rk_true_eq_self_iff (g : BinQF) : actForm g (Rk true) = g ↔ g.b = g.a := by
  rw [actForm_Rk_true]
  constructor
  · intro h; have := congrArg BinQF.b h; simp at this; omega
  · intro h; apply ext_abc <;> simp <;> omega



/-! ### Conjugacy of improper involutions to the standard ones -/

/-- Helper: if a matrix `P` of determinant $1$ (`hP`) conjugates `Rm k'` to `Rm k` ($P R_{k'} = R_k P$, `h`), then $k = k'$ and $P = \pm 1$. (The two standard improper involutions are not conjugate in $\mathrm{SL}_2(\mathbb Z)$, and the centralizer of each is $\{\pm 1\}$; this is the uniqueness in Cassels' (4.6)–(4.7).) -/
theorem conj_unique {P : Matrix (Fin 2) (Fin 2) ℤ} (hP : P.det = 1) {k k' : Bool}
    (h : P * Rm k' = Rm k * P) : k = k' ∧ (P = 1 ∨ P = -1) := by
  rw [Matrix.det_fin_two] at hP
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  have key : P 1 0 = 0 → P 0 1 = 0 → (P = 1 ∨ P = -1) := by
    intro hr hq
    rw [hq, hr] at hP
    have h0 : P 0 0 * P 1 1 = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h0 with h1 | h1
    · have h2 : P 1 1 = 1 := by rw [h1] at h0; linarith
      left; ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, hq, hr]
    · have h2 : P 1 1 = -1 := by rw [h1] at h0; linarith
      right; ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, hq, hr]
  cases k <;> cases k' <;> simp [Rm, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  · exact ⟨rfl, key (by omega) (by omega)⟩
  · exfalso
    have hr : P 1 0 = 0 := by omega
    have hp : P 0 0 = 2 * P 0 1 := by omega
    rw [hr, hp] at hP
    have : 2 * (P 0 1 * P 1 1) = 1 := by linarith
    omega
  · exfalso
    have hr : P 1 0 = 0 := by omega
    have hp : P 1 1 = -2 * P 0 1 := by omega
    rw [hr, hp] at hP
    have : 2 * (P 0 0 * P 0 1) = -1 := by linarith
    omega
  · have hr : P 1 0 = 0 := by omega
    refine ⟨rfl, ?_⟩
    have hP' := hP
    rw [hr] at hP'
    have h0 : P 0 0 * P 1 1 = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h0 with h1 | h1
    · have h2 : P 1 1 = 1 := by rw [h1] at h0; linarith
      exact key hr (by omega)
    · have h2 : P 1 1 = -1 := by rw [h1] at h0; linarith
      exact key hr (by omega)



/-- Helper: a matrix $\begin{pmatrix} p & q \\ r & -p \end{pmatrix}$ with $p^2 + qr = 1$ (an improper involution,
`h`) is conjugate by a matrix `M` of determinant $1$ to `Rm e` for some Boolean `e`: $S M = M R_e$ (Cassels'
(4.3)–(4.5): a primitive vector `x, y` fixed by $S$ is completed to a basis, and the remaining entry is reduced to
$0$ or $1$ modulo $2$). -/
theorem exists_conj_raw {p q r : ℤ} (h : p * p + q * r = 1) :
    ∃ (M : Matrix (Fin 2) (Fin 2) ℤ) (e : Bool), M.det = 1 ∧ !![p, q; r, -p] * M = M * Rm e := by
  obtain ⟨x, y, hxy, hf1, hf2⟩ : ∃ x y : ℤ, IsCoprime x y ∧ p * x + q * y = x ∧ r * x + (-p) * y = y := by
    by_cases h0 : q = 0 ∧ 1 - p = 0
    · refine exists_coprime_fixed (u₀ := 1 + p) (u₁ := r) (Or.inl (by omega)) ?_ (by ring)
      linear_combination h
    · exact exists_coprime_fixed (u₀ := q) (u₁ := 1 - p) (by tauto) (by ring) (by linear_combination h)
  obtain ⟨a, b, hab⟩ := hxy
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, z₀ = p * (-b) + q * a + (-b) := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = r * (-b) + (-p) * a + a := ⟨_, rfl⟩
  have hS0 : (p - 1) * z₀ + q * z₁ = 0 := by rw [hz₀, hz₁]; linear_combination (-b) * h
  have hS1 : r * z₀ - (p + 1) * z₁ = 0 := by rw [hz₀, hz₁]; linear_combination a * h
  have hv0 : (p - 1) * x + q * y = 0 := by linarith
  have hv1 : r * x - (p + 1) * y = 0 := by linarith
  have hD : z₀ * y - z₁ * x = 0 := by
    have e1 : (p - 1) * (z₀ * y - z₁ * x) = 0 := by
      linear_combination y * hS0 - z₁ * hv0
    have e2 : (p + 1) * (z₀ * y - z₁ * x) = 0 := by
      linear_combination (-z₀) * hv1 + x * hS1
    have : 2 * (z₀ * y - z₁ * x) = 0 := by linear_combination e2 - e1
    omega
  obtain ⟨k, hk⟩ : ∃ k, k = a * z₀ + b * z₁ := ⟨_, rfl⟩
  have hzx : z₀ = k * x := by
    rw [hk]; linear_combination (-z₀) * hab + b * hD
  have hzy : z₁ = k * y := by
    rw [hk]; linear_combination (-z₁) * hab - a * hD
  obtain ⟨m, e, hme⟩ : ∃ (m : ℤ) (e : Bool), k = 2 * m + (if e then 1 else 0) := by
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · exact ⟨m, false, by simp [hm]⟩
    · exact ⟨m, true, by simp [hm]⟩
  refine ⟨!![x, -b - m * x; y, a - m * y], e, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hab
  · cases e
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hme
      ext i j; fin_cases i <;> fin_cases j <;> simp [Rm, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hf1
      · linear_combination hzx - hz₀ + x * hme - m * hf1
      · linear_combination hf2
      · linear_combination hzy - hz₁ + y * hme - m * hf2
    · simp only [↓reduceIte] at hme
      ext i j; fin_cases i <;> fin_cases j <;> simp [Rm, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hf1
      · linear_combination hzx - hz₀ + x * hme - m * hf1
      · linear_combination hf2
      · linear_combination hzy - hz₁ + y * hme - m * hf2




/-! ### Improper automorphs -/

/-- Helper: the improper automorphs $\{S \in \mathrm{Aut}(f) : \det S = -1\}$ of $f$. -/
def ImproperAut (f : BinQF) : Set (GL (Fin 2) ℤ) := {S | S ∈ Siegel.Aut f ∧ S.val.det = -1}

/-- Helper: an improper automorph `S` of a form `f` of nonzero discriminant (hypotheses `hD`, `hS`) has trace $0$ and $S_{00}^2 + S_{01} S_{10} = 1$ (Cassels' (4.2)). -/
theorem improper_trace {f : BinQF} (hD : f.disc ≠ 0) {S : GL (Fin 2) ℤ} (hS : S ∈ ImproperAut f) :
    S.val 1 1 = - S.val 0 0 ∧ S.val 0 0 * S.val 0 0 + S.val 0 1 * S.val 1 0 = 1 := by
  obtain ⟨hA, hdet⟩ := hS
  rw [mem_aut_iff_actForm] at hA
  have hd' : S.val 0 0 * S.val 1 1 - S.val 0 1 * S.val 1 0 = -1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  have hs : S.val 1 1 = - S.val 0 0 := trace_zero_of_disc_ne hD hd' hA
  refine ⟨hs, ?_⟩
  rw [hs] at hd'
  linarith

/-- Helper: an improper automorph `S` of `f` (`hD`: $D \ne 0$; `hS`) has matrix $\begin{pmatrix} p & q \\ r & -p\end{pmatrix}$. -/
theorem improper_val {f : BinQF} (hD : f.disc ≠ 0) {S : GL (Fin 2) ℤ} (hS : S ∈ ImproperAut f) :
    S.val = !![S.val 0 0, S.val 0 1; S.val 1 0, -S.val 0 0] := by
  have := (improper_trace hD hS).1
  ext i j; fin_cases i <;> fin_cases j <;> simp [this]

/-- Helper: an improper automorph `S` of `f` (`hD`: $D \ne 0$; `hS`) satisfies $S^2 = 1$ (Cassels' (4.2)). -/
theorem improper_sq {f : BinQF} (hD : f.disc ≠ 0) {S : GL (Fin 2) ℤ} (hS : S ∈ ImproperAut f) :
    S * S = 1 := by
  obtain ⟨hs, hk⟩ := improper_trace hD hS
  apply Units.ext
  rw [Units.val_mul]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  · linarith
  · ring
  · ring
  · linarith

/-- Helper: a matrix of determinant $1$ as an element of $\mathrm{GL}_2(\mathbb Z)$. -/
noncomputable def glOfDet1 (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) : GL (Fin 2) ℤ :=
  Matrix.nonsingInvUnit M (by rw [h]; exact isUnit_one)

/-- Helper: the matrix of `glOfDet1 M h` is `M`. -/
@[simp] theorem glOfDet1_val (M : Matrix (Fin 2) (Fin 2) ℤ) (h : M.det = 1) :
    (glOfDet1 M h).val = M := rfl

/-- Helper: an improper automorph `S` of `f` (`hD`: $D \ne 0$; `hS`) is conjugate by a matrix `M` of determinant $1$ to `Rk k` for some `k`: $S M = M R_k$ (Cassels' (4.3)–(4.5)). -/
theorem exists_conj_rk {f : BinQF} (hD : f.disc ≠ 0) {S : GL (Fin 2) ℤ} (hS : S ∈ ImproperAut f) :
    ∃ (M : GL (Fin 2) ℤ) (k : Bool), M.val.det = 1 ∧ S * M = M * Rk k := by
  obtain ⟨M, e, hdet, hM⟩ := exists_conj_raw (improper_trace hD hS).2
  refine ⟨glOfDet1 M hdet, e, hdet, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, glOfDet1_val, Rk_val, improper_val hD hS]
  exact hM


/-! ### Group theory: conjugacy classes of improper automorphs -/

/-- Helper: if a relation `r` between `α` and `β` is total on both sides and relates `a a'` to `b b'` compatibly with the setoid `s` (`h3`: `a ≈ a'` iff `b = b'`), then the quotient of `α` by `s` has as many elements as `β`. -/
theorem card_quotient_eq_of_rel {α β : Type*} (s : Setoid α) (r : α → β → Prop)
    (h1 : ∀ a, ∃ b, r a b) (h2 : ∀ b, ∃ a, r a b)
    (h3 : ∀ a a' b b', r a b → r a' b' → (s.r a a' ↔ b = b')) :
    Nat.card (Quotient s) = Nat.card β := by
  refine Nat.card_congr
    { toFun := Quotient.lift (fun a => (h1 a).choose) (fun a a' haa' => ?_)
      invFun := fun b => Quotient.mk s (h2 b).choose
      left_inv := fun q => ?_
      right_inv := fun b => ?_ }
  · exact (h3 a a' _ _ (h1 a).choose_spec (h1 a').choose_spec).mp haa'
  · induction q using Quotient.inductionOn with
    | _ a =>
      apply Quotient.sound
      exact (h3 _ _ _ _ (h2 _).choose_spec (h1 a).choose_spec).mpr rfl
  · have hs := (h2 b).choose_spec
    show (h1 (h2 b).choose).choose = b
    exact ((h3 _ _ _ _ hs (h1 (h2 b).choose).choose_spec).mp (Setoid.refl _)).symm

/-- Helper: the setoid on a subset `I` of a group `Γ` of elements conjugate under the subgroup `A`: $S \sim S'$ iff $S' = T S T^{-1}$ for some `T ∈ A`. -/
def conjSetoid {Γ : Type*} [Group Γ] (A : Subgroup Γ) (I : Set Γ) : Setoid I where
  r S S' := ∃ T ∈ A, (S' : Γ) = T * S * T⁻¹
  iseqv :=
    { refl := fun S => ⟨1, A.one_mem, by simp⟩
      symm := by
        rintro S S' ⟨T, hT, h⟩
        refine ⟨T⁻¹, A.inv_mem hT, ?_⟩
        rw [h]; group
      trans := by
        rintro S S' S'' ⟨T, hT, h⟩ ⟨U, hU, h'⟩
        refine ⟨U * T, A.mul_mem hU hT, ?_⟩
        rw [h', h]; group }

/-- **The subgroup of squares** of a subgroup `A` of a group `Γ`: the subgroup of the group `↥A` generated by the squares $T^2$, $T \in A$. For abelian `A` it is the set of squares, and its index is the order of the quotient $A/A^2$ (Cassels' $O^{+}/(O^{+})^2$ for $A = O^{+}$). -/
def squares {Γ : Type*} [Group Γ] (A : Subgroup Γ) : Subgroup A :=
  Subgroup.closure (Set.range fun T : A => T * T)

/-- Helper: in an abelian subgroup `A` (`hcomm`), `x` lies in the subgroup `squares A` iff it is a square. -/
theorem mem_squares_iff {Γ : Type*} [Group Γ] (A : Subgroup Γ)
    (hcomm : ∀ T U : A, T * U = U * T) (x : A) :
    x ∈ squares A ↔ ∃ U : A, U * U = x := by
  constructor
  · intro hx
    unfold squares at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => obtain ⟨U, rfl⟩ := hy; exact ⟨U, rfl⟩
    | one => exact ⟨1, by simp⟩
    | mul y z _ _ hy hz =>
      obtain ⟨U, rfl⟩ := hy
      obtain ⟨V, rfl⟩ := hz
      refine ⟨U * V, ?_⟩
      calc U * V * (U * V) = U * (V * U) * V := by group
        _ = U * (U * V) * V := by rw [hcomm V U]
        _ = _ := by group
    | inv y _ hy =>
      obtain ⟨U, rfl⟩ := hy
      exact ⟨U⁻¹, by group⟩
  · rintro ⟨U, rfl⟩
    exact Subgroup.subset_closure ⟨U, rfl⟩

/-- Helper: if `I` is the set of the elements `T S₀` (`T` in the abelian subgroup `A`) of order dividing $2$, the number of `A`-conjugacy classes in `I` is the index of the squares of `A`. -/
theorem card_conj_quotient {Γ : Type*} [Group Γ] (A : Subgroup Γ) (I : Set Γ) (S₀ : Γ)
    (hS₀ : S₀ ∈ I) (hI : ∀ S ∈ I, ∃ T ∈ A, S = T * S₀) (hIA : ∀ T ∈ A, T * S₀ ∈ I)
    (hsq : ∀ S ∈ I, S * S = 1) (hcomm : ∀ T U : A, T * U = U * T) :
    Nat.card (Quotient (conjSetoid A I)) = (squares A).index := by
  have hS₀sq : S₀ * S₀ = 1 := hsq S₀ hS₀
  have hS₀inv : S₀⁻¹ = S₀ := inv_eq_of_mul_eq_one_right hS₀sq
  let e : A ≃ I :=
    { toFun := fun T => ⟨T * S₀, hIA T T.2⟩
      invFun := fun S => ⟨S * S₀⁻¹, by
        obtain ⟨T, hT, h⟩ := hI S S.2
        rw [h]; simpa using hT⟩
      left_inv := fun T => by ext; simp
      right_inv := fun S => by ext; simp }
  have hconj : ∀ U : A, S₀ * (U : Γ)⁻¹ * S₀ = U := by
    intro U
    have h1 := hsq _ (hIA (U : Γ)⁻¹ (A.inv_mem U.2))
    calc S₀ * (U : Γ)⁻¹ * S₀ = U * ((U : Γ)⁻¹ * S₀ * ((U : Γ)⁻¹ * S₀)) := by group
      _ = U := by rw [h1]; simp
  have key : ∀ T₁ T₂ : A, (conjSetoid A I).r (e T₁) (e T₂) ↔ T₁⁻¹ * T₂ ∈ squares A := by
    intro T₁ T₂
    rw [mem_squares_iff A hcomm]
    constructor
    · rintro ⟨U, hU, h⟩
      have h' : (T₂ : Γ) * S₀ = U * ((T₁ : Γ) * S₀) * U⁻¹ := h
      have h2 : (T₂ : Γ) = U * T₁ * U := by
        have : (T₂ : Γ) = U * T₁ * (S₀ * U⁻¹ * S₀) := by
          have e1 : (T₂ : Γ) = (T₂ * S₀) * S₀ := by rw [mul_assoc, hS₀sq, mul_one]
          rw [e1, h']
          group
        rw [this, hconj ⟨U, hU⟩]
      refine ⟨⟨U, hU⟩, ?_⟩
      have hc : (U : Γ) * T₁ = T₁ * U := congrArg Subtype.val (hcomm ⟨U, hU⟩ T₁)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h2, hc]; group
    · rintro ⟨V, hV⟩
      refine ⟨V, V.2, ?_⟩
      have h3 : (T₂ : Γ) = T₁ * (V * V) := by
        have : T₂ = T₁ * (V * V) := by rw [hV]; group
        rw [this]; rfl
      have hc : (T₁ : Γ) * V = V * T₁ := congrArg Subtype.val (hcomm T₁ V)
      have hv := hconj V
      show (T₂ : Γ) * S₀ = V * ((T₁ : Γ) * S₀) * (V : Γ)⁻¹
      calc (T₂ : Γ) * S₀ = (V : Γ) * T₁ * V * S₀ := by rw [h3, ← hc]; group
        _ = (V : Γ) * T₁ * (S₀ * (V : Γ)⁻¹ * S₀) * S₀ := by rw [hv]
        _ = V * ((T₁ : Γ) * S₀) * (V : Γ)⁻¹ * (S₀ * S₀) := by group
        _ = _ := by rw [hS₀sq, mul_one]
  refine Eq.trans (Nat.card_congr (Quotient.congr e.symm ?_)) (rfl)
  intro S S'
  obtain ⟨T₁, rfl⟩ := e.surjective S
  obtain ⟨T₂, rfl⟩ := e.surjective S'
  simp only [Equiv.symm_apply_apply]
  rw [key]; exact (QuotientGroup.leftRel_apply).symm



/-! ### Ambiguous forms and the matrices `Rk` -/

/-- Helper: a form `g` is ambiguous ($b = 0$ or $b = a$, `IsAmbiguousForm`) iff it is fixed by one of the matrices `Rk k`. -/
theorem isAmb_iff_exists_fixed (g : BinQF) :
    (g.b = 0 ∨ g.b = g.a) ↔ ∃ k, actForm g (Rk k) = g := by
  constructor
  · rintro (h | h)
    · exact ⟨false, (actForm_Rk_false_eq_self_iff g).mpr h⟩
    · exact ⟨true, (actForm_Rk_true_eq_self_iff g).mpr h⟩
  · rintro ⟨k, hk⟩
    cases k
    · exact Or.inl ((actForm_Rk_false_eq_self_iff g).mp hk)
    · exact Or.inr ((actForm_Rk_true_eq_self_iff g).mp hk)

/-- Helper: a form `g` of nonzero discriminant (`hD`) is fixed by at most one of the two matrices `Rk k` (`h`, `h'`). -/
theorem kind_unique {g : BinQF} (hD : g.disc ≠ 0) {k k' : Bool} (h : actForm g (Rk k) = g)
    (h' : actForm g (Rk k') = g) : k = k' := by
  cases k <;> cases k' <;> try rfl
  all_goals
    exfalso
    apply hD
    have b0 := (actForm_Rk_false_eq_self_iff g).mp (by assumption)
    have ba := (actForm_Rk_true_eq_self_iff g).mp (by assumption)
    simp only [BinQF.disc, b0, ← ba]
    ring

/-! ### The relation between improper automorphs and ambiguous forms -/

/-- Helper: `S` and `g` are related if `g = f ∘ M` and `S = M Rk M⁻¹` for some `M ∈ SL₂(ℤ)`. -/
def IsRel (f : BinQF) (S : GL (Fin 2) ℤ) (g : BinQF) : Prop :=
  ∃ (M : GL (Fin 2) ℤ) (k : Bool), M.val.det = 1 ∧ S * M = M * Rk k ∧ g = actForm f M

/-- Helper: the inverse of a matrix `M` of determinant $1$ has determinant $1$. -/
theorem det_inv_of_det_one {M : GL (Fin 2) ℤ} (hM : M.val.det = 1) : (M⁻¹).val.det = 1 := by
  have := congrArg Matrix.det (M.val_inv)
  have h2 : ((M⁻¹ : GL (Fin 2) ℤ).val * M.val).det = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  rw [Matrix.det_mul, hM, mul_one] at h2
  exact h2

/-- Helper: if $S M = M R$ and $\det M = 1$ then $\det S = \det R$. -/
theorem autDetConj {S M : GL (Fin 2) ℤ} {R : GL (Fin 2) ℤ} (hM : M.val.det = 1) (h : S * M = M * R) :
    S.val.det = R.val.det := by
  have := congrArg (fun X : GL (Fin 2) ℤ => X.val.det) h
  simp only [Units.val_mul, Matrix.det_mul, hM, mul_one, one_mul] at this
  exact this

/-- Helper: if `S` is an automorph of `f` with $S M = M R_k$ then $f \circ M$ is fixed by `Rk k`. -/
theorem fixed_of_witness {f : BinQF} {S M : GL (Fin 2) ℤ} {k : Bool} (hS : S ∈ Siegel.Aut f)
    (hSM : S * M = M * Rk k) : actForm (actForm f M) (Rk k) = actForm f M := by
  have hf : actForm f S = f := mem_aut_iff_actForm.mp hS
  calc actForm (actForm f M) (Rk k) = actForm f (M * Rk k) := (actForm_mul _ _ _).symm
    _ = actForm f (S * M) := by rw [hSM]
    _ = actForm (actForm f S) M := actForm_mul _ _ _
    _ = actForm f M := by rw [hf]

/-- Helper: every improper automorph `S` of `f` (`hD`, `hS`) is related to some form. -/
theorem exists_form_isRel {f : BinQF} (hD : f.disc ≠ 0) {S : GL (Fin 2) ℤ} (hS : S ∈ ImproperAut f) :
    ∃ g, IsRel f S g := by
  obtain ⟨M, k, hM, hSM⟩ := exists_conj_rk hD hS
  exact ⟨actForm f M, M, k, hM, hSM, rfl⟩

/-- Helper: $f \circ M$ is properly equivalent to `f` for `M` of determinant $1$. -/
theorem sLEquiv_of_det_one (f : BinQF) {M : GL (Fin 2) ℤ} (hM : M.val.det = 1) :
    SLEquiv f (actForm f M) := by
  rw [sLEquiv_iff]
  exact ⟨M.val 0 0, M.val 0 1, M.val 1 0, M.val 1 1, by rw [← Matrix.det_fin_two]; exact hM, rfl⟩

/-- Helper: a form `g` related to an automorph `S` of `f` is properly equivalent to `f` and ambiguous. -/
theorem isRel_mem {f : BinQF} {S : GL (Fin 2) ℤ} {g : BinQF} (hS : S ∈ Siegel.Aut f)
    (h : IsRel f S g) : SLEquiv f g ∧ (g.b = 0 ∨ g.b = g.a) := by
  obtain ⟨M, k, hM, hSM, rfl⟩ := h
  exact ⟨sLEquiv_of_det_one f hM, (isAmb_iff_exists_fixed _).mpr ⟨k, fixed_of_witness hS hSM⟩⟩

/-- Helper: an ambiguous form `g` properly equivalent to `f` is related to an improper automorph of `f` (Cassels' proof that the ambiguous forms of a class come from improper automorphs). -/
theorem exists_isRel_of_mem {f : BinQF} {g : BinQF} (hsl : SLEquiv f g) (hamb : g.b = 0 ∨ g.b = g.a) :
    ∃ S ∈ ImproperAut f, IsRel f S g := by
  obtain ⟨p, q, r, s, hd, hg⟩ := (sLEquiv_iff f g).mp hsl
  obtain ⟨k, hk⟩ := (isAmb_iff_exists_fixed g).mp hamb
  have hdet : (!![p, q; r, s] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]; exact hd
  set M : GL (Fin 2) ℤ := glOfDet1 !![p, q; r, s] hdet with hMdef
  have hMdet : M.val.det = 1 := hdet
  have hM : actForm f M = g := hg
  have hSM : (M * Rk k * M⁻¹) * M = M * Rk k := by simp [mul_assoc]
  refine ⟨M * Rk k * M⁻¹, ⟨?_, ?_⟩, M, k, hMdet, hSM, hM.symm⟩
  · rw [mem_aut_iff_actForm]
    calc actForm f (M * Rk k * M⁻¹) = actForm (actForm (actForm f M) (Rk k)) M⁻¹ := by
          rw [actForm_mul, actForm_mul]
      _ = actForm (actForm f M) M⁻¹ := by rw [hM, hk]
      _ = actForm f (M * M⁻¹) := (actForm_mul _ _ _).symm
      _ = f := by rw [mul_inv_cancel, actForm_one]
  · rw [autDetConj hMdet hSM, det_Rk]


/-- Helper: $f \circ M$ has the discriminant of `f` for `M` of determinant $1$. -/
theorem disc_actForm_of_det_one (f : BinQF) {M : GL (Fin 2) ℤ} (hM : M.val.det = 1) :
    (actForm f M).disc = f.disc := by
  apply BinQF.disc_subst_of_det
  rw [← Matrix.det_fin_two, hM]; norm_num

/-- Helper: an element of $\mathrm{GL}_2(\mathbb Z)$ whose matrix is $\pm 1$ is $\pm 1$. -/
theorem eq_one_or_neg_one_of_val {P : GL (Fin 2) ℤ} (h : P.val = 1 ∨ P.val = -1) : P = 1 ∨ P = -1 := by
  rcases h with h | h
  · left; exact Units.ext (by rw [h]; rfl)
  · right; exact Units.ext (by rw [h]; simp)

/-- Helper: for improper automorphs `S S'` of `f` related to forms `g g'`, the forms agree iff `S'` is conjugate to `S` by a proper automorph (Cassels' (4.8) and the argument after it). -/
theorem isRel_iff {f : BinQF} (hD : f.disc ≠ 0) {S S' : GL (Fin 2) ℤ} {g g' : BinQF}
    (hS : S ∈ Siegel.Aut f) (hS' : S' ∈ Siegel.Aut f) (h : IsRel f S g) (h' : IsRel f S' g') :
    (∃ T ∈ AutSL f, S' = T * S * T⁻¹) ↔ g = g' := by
  obtain ⟨M, k, hM, hSM, rfl⟩ := h
  obtain ⟨M', k', hM', hSM', rfl⟩ := h'
  constructor
  · rintro ⟨T, hT, hTS⟩
    obtain ⟨hTA, hTdet⟩ := mem_autSL.mp hT
    have hf : actForm f T = f := mem_aut_iff_actForm.mp hTA
    obtain ⟨N, hN⟩ : ∃ N, N = T * M := ⟨_, rfl⟩
    have hNdet : N.val.det = 1 := by
      rw [hN, Units.val_mul, Matrix.det_mul, hTdet, hM, one_mul]
    have hSN : S' * N = N * Rk k := by
      rw [hTS, hN]
      calc T * S * T⁻¹ * (T * M) = T * (S * M) := by group
        _ = T * (M * Rk k) := by rw [hSM]
        _ = T * M * Rk k := by group
    obtain ⟨P, hP⟩ : ∃ P, P = M'⁻¹ * N := ⟨_, rfl⟩
    have hPdet : P.val.det = 1 := by
      rw [hP, Units.val_mul, Matrix.det_mul, det_inv_of_det_one hM', hNdet, one_mul]
    have hPR : P * Rk k = Rk k' * P := by
      have e1 : M'⁻¹ * S' = Rk k' * M'⁻¹ := by
        calc M'⁻¹ * S' = M'⁻¹ * (S' * M') * M'⁻¹ := by group
          _ = M'⁻¹ * (M' * Rk k') * M'⁻¹ := by rw [hSM']
          _ = Rk k' * M'⁻¹ := by group
      calc P * Rk k = M'⁻¹ * (N * Rk k) := by rw [hP]; group
        _ = M'⁻¹ * (S' * N) := by rw [hSN]
        _ = (M'⁻¹ * S') * N := by group
        _ = Rk k' * M'⁻¹ * N := by rw [e1]
        _ = Rk k' * P := by rw [hP]; group
    have hPR' : P.val * Rm k = Rm k' * P.val := by
      have := congrArg Units.val hPR
      rwa [Units.val_mul, Units.val_mul, Rk_val, Rk_val] at this
    obtain ⟨_, hP1⟩ := conj_unique hPdet hPR'
    have hP2 := eq_one_or_neg_one_of_val hP1
    have hNP : N = M' * P := by rw [hP]; group
    have h1 : actForm f N = actForm f M' := by
      rw [hNP, actForm_mul]
      rcases hP2 with h | h
      · rw [h, actForm_one]
      · rw [h, actForm_neg_one]
    have h2 : actForm f N = actForm f M := by
      rw [hN, actForm_mul, hf]
    rw [← h2, h1]
  · intro hg
    have hdisc : (actForm f M).disc ≠ 0 := by rw [disc_actForm_of_det_one f hM]; exact hD
    have kk : k = k' := by
      refine kind_unique hdisc (fixed_of_witness hS hSM) ?_
      rw [hg]; exact fixed_of_witness hS' hSM'
    subst kk
    refine ⟨M' * M⁻¹, mem_autSL.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [mem_aut_iff_actForm]
      calc actForm f (M' * M⁻¹) = actForm (actForm f M') M⁻¹ := actForm_mul _ _ _
        _ = actForm (actForm f M) M⁻¹ := by rw [hg]
        _ = actForm f (M * M⁻¹) := (actForm_mul _ _ _).symm
        _ = f := by rw [mul_inv_cancel, actForm_one]
    · rw [Units.val_mul, Matrix.det_mul, hM', det_inv_of_det_one hM, mul_one]
    · have e1 : S = M * Rk k * M⁻¹ := eq_mul_inv_of_mul_eq hSM
      have e2 : S' = M' * Rk k * M'⁻¹ := eq_mul_inv_of_mul_eq hSM'
      rw [e1, e2]; group


/-! ### The count -/

/-- Helper (the count for $\mathrm{SL}_2$-equivalence over `BinQF`, in terms of the helper group `AutSL f`): for a form `f` of nonzero discriminant (`hD`) with an improper automorph `S₀` (`hS₀`) and abelian `AutSL f` (`hcomm`), the number of ambiguous forms properly equivalent to `f` is the index of the squares. -/
theorem ncard_ambiguous_aux {f : BinQF} (hD : f.disc ≠ 0) {S₀ : GL (Fin 2) ℤ}
    (hS₀ : S₀ ∈ ImproperAut f) (hcomm : ∀ T U : AutSL f, T * U = U * T) :
    {g : BinQF | SLEquiv f g ∧ (g.b = 0 ∨ g.b = g.a)}.ncard = (squares (AutSL f)).index := by
  have hsq : ∀ S ∈ ImproperAut f, S * S = 1 := fun S hS => improper_sq hD hS
  have hI : ∀ S ∈ ImproperAut f, ∃ T ∈ AutSL f, S = T * S₀ := by
    intro S hS
    refine ⟨S * S₀, mem_autSL.mpr ⟨(Siegel.Aut f).mul_mem hS.1 hS₀.1, ?_⟩, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hS.2, hS₀.2]; norm_num
    · rw [mul_assoc, hsq S₀ hS₀, mul_one]
  have hIA : ∀ T ∈ AutSL f, T * S₀ ∈ ImproperAut f := by
    intro T hT
    obtain ⟨hTA, hTd⟩ := mem_autSL.mp hT
    exact ⟨(Siegel.Aut f).mul_mem hTA hS₀.1, by rw [Units.val_mul, Matrix.det_mul, hTd, hS₀.2]; norm_num⟩
  rw [← card_conj_quotient (AutSL f) (ImproperAut f) S₀ hS₀ hI hIA hsq hcomm,
    ← Nat.card_coe_set_eq]
  symm
  refine card_quotient_eq_of_rel (conjSetoid (AutSL f) (ImproperAut f))
    (fun (S : ImproperAut f) (g : {g : BinQF | SLEquiv f g ∧ (g.b = 0 ∨ g.b = g.a)}) => IsRel f S.1 g.1)
    ?_ ?_ ?_
  · intro S
    obtain ⟨g, hg⟩ := exists_form_isRel hD S.2
    exact ⟨⟨g, isRel_mem S.2.1 hg⟩, hg⟩
  · intro g
    obtain ⟨S, hS, hrel⟩ := exists_isRel_of_mem g.2.1 g.2.2
    exact ⟨⟨S, hS⟩, hrel⟩
  · intro S S' g g' h h'
    exact (isRel_iff hD S.2.1 S'.2.1 h h').trans Subtype.ext_iff.symm


/-! ### The proper automorphism group is abelian -/

/-- Helper: the entries $p, q, r, s$ of an automorph of $[A, B, C]$ of determinant $1$ (`e1 e2 e3 hd`) satisfy $A(s - p) = Br$, $Aq = -Cr$, $C(s - p) = -Bq$. -/
theorem aut_rel {A B C p q r s : ℤ}
    (e1 : A * p ^ 2 + B * p * r + C * r ^ 2 = A)
    (e2 : 2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s = B)
    (e3 : A * q ^ 2 + B * q * s + C * s ^ 2 = C)
    (hd : p * s - q * r = 1) :
    A * (s - p) = B * r ∧ A * q = -C * r ∧ C * (s - p) = -B * q := by
  refine ⟨?_, ?_, ?_⟩
  · grind
  · grind
  · grind

/-- Helper: two solutions $(\alpha, q, r)$, $(\alpha', q', r')$ of the linear system $A\alpha = Br$, $Aq = -Cr$, $C\alpha = -Bq$ with $(A, B, C) \ne 0$ are proportional (their $2 \times 2$ minors vanish). -/
theorem minors_of_rel {A B C α q r α' q' r' : ℤ} (hABC : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0)
    (h1 : A * α = B * r) (h2 : A * q = -C * r) (h3 : C * α = -B * q)
    (h1' : A * α' = B * r') (h2' : A * q' = -C * r') (h3' : C * α' = -B * q') :
    q * α' = q' * α ∧ r * α' = r' * α ∧ q * r' = q' * r := by
  by_cases hA : A = 0
  · subst hA
    by_cases hB : B = 0
    · subst hB
      have hC : C ≠ 0 := by tauto
      have hr : r = 0 := by
        have : C * r = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hC
      have hr' : r' = 0 := by
        have : C * r' = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hC
      have ha : α = 0 := by
        have : C * α = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hC
      have ha' : α' = 0 := by
        have : C * α' = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hC
      subst hr hr' ha ha'
      simp
    · have hr : r = 0 := by
        have : B * r = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      have hr' : r' = 0 := by
        have : B * r' = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hB
      subst hr hr'
      refine ⟨?_, by simp, by simp⟩
      apply mul_left_cancel₀ hB
      linear_combination α' * h3 - α * h3'
  · refine ⟨?_, ?_, ?_⟩
    · apply mul_left_cancel₀ (mul_ne_zero hA hA)
      linear_combination (A * α') * h2 - (A * α) * h2' + (-C * r) * h1' - (-C * r') * h1
    · apply mul_left_cancel₀ hA
      linear_combination r * h1' - r' * h1
    · apply mul_left_cancel₀ hA
      linear_combination r' * h2 - r * h2'

/-- Helper: the entries of a proper automorph `T` of `f` satisfy $a(T_{11} - T_{00}) = b T_{10}$, $a T_{01} = -c T_{10}$, $c(T_{11} - T_{00}) = -b T_{01}$. -/
theorem autSL_rel {f : BinQF} {T : GL (Fin 2) ℤ} (hT : T ∈ AutSL f) :
    f.a * (T.val 1 1 - T.val 0 0) = f.b * T.val 1 0 ∧ f.a * T.val 0 1 = -f.c * T.val 1 0 ∧
      f.c * (T.val 1 1 - T.val 0 0) = -f.b * T.val 0 1 := by
  obtain ⟨hA, hd⟩ := mem_autSL.mp hT
  rw [mem_aut_iff_actForm] at hA
  have e1 := congrArg BinQF.a hA
  have e2 := congrArg BinQF.b hA
  have e3 := congrArg BinQF.c hA
  simp only [actForm, a_subst, b_subst, c_subst] at e1 e2 e3
  rw [Matrix.det_fin_two] at hd
  exact aut_rel (by linear_combination e1) (by linear_combination e2) (by linear_combination e3) hd

/-- **$O^{+}$ is abelian** (Cassels, Ch. 14, p. 343: the proper orthogonal group is abelian): any two proper automorphs `T U` of a binary form `f` of nonzero discriminant (`hD`) commute. Cassels reads this off the four cases; here it is proved directly (all proper automorphs commute with $\begin{pmatrix} -b & -2c \\ 2a & b \end{pmatrix}$, which is not scalar). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (O⁺ is abelian)"]
theorem autSL_comm {f : BinQF} (hD : f.disc ≠ 0) (T U : AutSL f) : T * U = U * T := by
  have hABC : f.a ≠ 0 ∨ f.b ≠ 0 ∨ f.c ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hD
    simp [BinQF.disc, h.1, h.2.1, h.2.2]
  obtain ⟨h1, h2, h3⟩ := autSL_rel T.2
  obtain ⟨h1', h2', h3'⟩ := autSL_rel U.2
  obtain ⟨m1, m2, m3⟩ := minors_of_rel hABC h1 h2 h3 h1' h2' h3'
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linarith
  · linarith
  · linarith
  · linarith


/-! ### The index of the squares -/

/-- Helper: $-1$ is a proper automorph of every binary form `f`. -/
theorem neg_one_mem_autSL (f : BinQF) : (-1 : GL (Fin 2) ℤ) ∈ AutSL f := by
  refine mem_autSL.mpr ⟨?_, ?_⟩
  · rw [mem_aut_iff_actForm]; exact actForm_neg_one f
  · simp [Matrix.det_fin_two]

/-- Helper: an element `T` of $\mathrm{SL}_2(\mathbb Z)$ (`hdet`) with $T^2 = 1$ (`hT`) is $\pm 1$. -/
theorem eq_one_or_neg_one_of_sq {T : GL (Fin 2) ℤ} (hdet : T.val.det = 1) (hT : T * T = 1) :
    T = 1 ∨ T = -1 := by
  have e := congrArg Units.val hT
  rw [Units.val_mul, Units.val_one] at e
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have h1 : T.val 0 1 * (T.val 0 0 + T.val 1 1) = 0 := by linarith
  have h2 : T.val 1 0 * (T.val 0 0 + T.val 1 1) = 0 := by linarith
  by_cases hs : T.val 0 0 + T.val 1 1 = 0
  · exfalso
    have : T.val 1 1 = -T.val 0 0 := by linarith
    rw [this] at hdet
    nlinarith
  · have hq : T.val 0 1 = 0 := (mul_eq_zero.mp h1).resolve_right hs
    have hr : T.val 1 0 = 0 := (mul_eq_zero.mp h2).resolve_right hs
    rw [hq, hr] at hdet e00 e11
    have h0 : T.val 0 0 * T.val 1 1 = 1 := by linarith
    apply eq_one_or_neg_one_of_val
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h0 with h | h
    · have h' : T.val 1 1 = 1 := by rw [h] at h0; linarith
      left; ext i j; fin_cases i <;> fin_cases j <;> simp [h, h', hq, hr]
    · have h' : T.val 1 1 = -1 := by rw [h] at h0; linarith
      right; ext i j; fin_cases i <;> fin_cases j <;> simp [h, h', hq, hr]

/-- Helper: exactly two proper automorphs `T` of the binary form `f` satisfy $T^2 = 1$, namely $\pm 1$. -/
theorem card_sq_eq_one (f : BinQF) :
    Nat.card {T : AutSL f // T * T = 1} = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, neg_one_mem_autSL f⟩, by
    apply Subtype.ext; simp⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : {T : AutSL f // T * T = 1} => ((x.1 : GL (Fin 2) ℤ).val 0 0)) h
    simp at this
  · ext ⟨T, hT⟩
    simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hT' : (T : GL (Fin 2) ℤ) * T = 1 := congrArg Subtype.val hT
    rcases eq_one_or_neg_one_of_sq (mem_autSL.mp T.2).2 hT' with h | h
    · left; apply Subtype.ext; apply Subtype.ext; simpa using h
    · right; apply Subtype.ext; apply Subtype.ext; simpa using h


/-- Helper: squaring as a homomorphism of an abelian group. -/
def autSqHom {G : Type*} [Group G] (hcomm : ∀ x y : G, x * y = y * x) : G →* G where
  toFun x := x * x
  map_one' := mul_one 1
  map_mul' x y := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hcomm y x]
      _ = _ := by group

/-- Helper: the subgroup `squares A` is the range of squaring `autSqHom` (`hcomm`: `A` is abelian). -/
theorem squares_eq_range_autSqHom {Γ : Type*} [Group Γ] (A : Subgroup Γ) (hcomm : ∀ T U : A, T * U = U * T) :
    squares A = (autSqHom hcomm).range := by
  ext x
  rw [mem_squares_iff A hcomm, MonoidHom.mem_range]
  rfl

/-- For a finite abelian group the index of the squares is the number of elements of order dividing $2$. -/
theorem index_squares_of_finite {Γ : Type*} [Group Γ] (A : Subgroup Γ)
    (hcomm : ∀ T U : A, T * U = U * T) [Finite A] :
    (squares A).index = Nat.card {x : A // x * x = 1} := by
  rw [squares_eq_range_autSqHom A hcomm]
  have h1 := Subgroup.card_ker_mul_card_range (autSqHom hcomm)
  have h2 := Subgroup.card_mul_index (autSqHom hcomm).range
  have hpos : 0 < Nat.card (autSqHom hcomm).range := Nat.card_pos
  have hker : Nat.card (autSqHom hcomm).ker = Nat.card {x : A // x * x = 1} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by rw [MonoidHom.mem_ker]; rfl)
  rw [← hker]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h2, mul_comm, h1]


/-- Helper: the homomorphism $\mathbb Z^\times \to \mathbb Z/2$ recording the sign (as a multiplicative group). -/
def autSignHom : ℤˣ →* Multiplicative (ZMod 2) where
  toFun ε := if ε = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' ε ε' := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
      decide

/-- Helper: the homomorphism $\mathbb Z^\times \times \mathbb Z \to (\mathbb Z/2)^2$ (parity of both coordinates). -/
def parityHom : ℤˣ × Multiplicative ℤ →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (autSignHom.comp (MonoidHom.fst _ _)).prod
    ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp (MonoidHom.snd _ _))

/-- Helper: `autSignHom` sends $1$ to $1$. -/
theorem autSignHom_one : autSignHom 1 = 1 := by simp [autSignHom]

/-- Helper: `autSignHom` sends $-1$ to the generator of $\mathbb Z/2$. -/
theorem autSignHom_neg_one : autSignHom (-1) = Multiplicative.ofAdd 1 := by
  have : ¬ ((-1 : ℤˣ) = 1) := by decide
  simp [autSignHom, this]

/-- Helper: the value of `parityHom` at $(\varepsilon, n)$. -/
theorem parityHom_apply (ε : ℤˣ) (n : Multiplicative ℤ) :
    parityHom (ε, n) = (autSignHom ε, Multiplicative.ofAdd ((Multiplicative.toAdd n : ℤ) : ZMod 2)) := rfl

/-- Helper: `parityHom` is surjective. -/
theorem parityHom_surjective : Function.Surjective parityHom := by
  rintro ⟨x, y⟩
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have key : ∀ (ε : ℤˣ) (n : Multiplicative ℤ), autSignHom ε = x →
      Multiplicative.ofAdd ((Multiplicative.toAdd n : ℤ) : ZMod 2) = y → parityHom (ε, n) = (x, y) := by
    intro ε n h1 h2
    rw [parityHom_apply, h1, h2]
  rcases hz x.toAdd with hx | hx <;> rcases hz y.toAdd with hy | hy
  · refine ⟨(1, Multiplicative.ofAdd 0), key _ _ ?_ ?_⟩
    · rw [autSignHom_one]; apply Multiplicative.toAdd.injective; simp [hx]
    · apply Multiplicative.toAdd.injective; simp [hy]
  · refine ⟨(1, Multiplicative.ofAdd 1), key _ _ ?_ ?_⟩
    · rw [autSignHom_one]; apply Multiplicative.toAdd.injective; simp [hx]
    · apply Multiplicative.toAdd.injective; simp [hy]
  · refine ⟨(-1, Multiplicative.ofAdd 0), key _ _ ?_ ?_⟩
    · rw [autSignHom_neg_one]; apply Multiplicative.toAdd.injective; simp [hx]
    · apply Multiplicative.toAdd.injective; simp [hy]
  · refine ⟨(-1, Multiplicative.ofAdd 1), key _ _ ?_ ?_⟩
    · rw [autSignHom_neg_one]; apply Multiplicative.toAdd.injective; simp [hx]
    · apply Multiplicative.toAdd.injective; simp [hy]

/-- Helper: the kernel of `parityHom` is the set of squares of $\mathbb Z^{\times} \times \mathbb Z$. -/
theorem mem_ker_parityHom {p : ℤˣ × Multiplicative ℤ} :
    p ∈ parityHom.ker ↔ ∃ u : ℤˣ × Multiplicative ℤ, u * u = p := by
  obtain ⟨ε, n⟩ := p
  rw [MonoidHom.mem_ker, parityHom_apply]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk_eq_one.mp h
    have hε : ε = 1 := by
      rcases Int.units_eq_one_or ε with h | h
      · exact h
      · exfalso; subst h
        rw [autSignHom_neg_one] at h1
        have := congrArg Multiplicative.toAdd h1
        revert this; decide
    have hm : ((Multiplicative.toAdd n : ℤ) : ZMod 2) = 0 := by
      have := congrArg Multiplicative.toAdd h2
      simpa using this
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (Multiplicative.toAdd n) 2).mp hm
    refine ⟨(1, Multiplicative.ofAdd k), ?_⟩
    apply Prod.ext
    · simp [hε]
    · apply Multiplicative.toAdd.injective
      simp only [Prod.snd_mul, toAdd_mul, toAdd_ofAdd]
      push_cast at hk
      omega
  · rintro ⟨⟨u, w⟩, h⟩
    have h1 : u * u = ε := congrArg Prod.fst h
    have h2 : w * w = n := congrArg Prod.snd h
    have hu : u * u = 1 := by rcases Int.units_eq_one_or u with h | h <;> subst h <;> simp
    rw [← h1, hu, autSignHom_one]
    refine Prod.ext rfl ?_
    show Multiplicative.ofAdd _ = (1 : Multiplicative (ZMod 2))
    apply Multiplicative.toAdd.injective
    rw [← h2]
    simp [toAdd_mul]
    exact (by decide : ∀ z : ZMod 2, z + z = 0) _


/-- For an abelian group isomorphic to $\{\pm 1\} \times \mathbb Z$ the squares have index $4$. -/
theorem index_squares_of_equiv {Γ : Type*} [Group Γ] (A : Subgroup Γ)
    (hcomm : ∀ T U : A, T * U = U * T) (e : A ≃* ℤˣ × Multiplicative ℤ) :
    (squares A).index = 4 := by
  have hsurj : Function.Surjective (parityHom.comp (e : A →* ℤˣ × Multiplicative ℤ)) :=
    parityHom_surjective.comp e.surjective
  have hker : squares A = (parityHom.comp (e : A →* ℤˣ × Multiplicative ℤ)).ker := by
    ext x
    rw [mem_squares_iff A hcomm, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      mem_ker_parityHom]
    constructor
    · rintro ⟨U, rfl⟩
      exact ⟨e U, by simp⟩
    · rintro ⟨u, hu⟩
      refine ⟨e.symm u, e.injective ?_⟩
      simp [hu]
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hsurj, Subgroup.card_top]
  simp


/-! ### Groups of the form $\{\pm 1\} \times \mathbb Z$ -/

/-- Helper: $1 \ne -1$ in $\mathrm{GL}_2(\mathbb Z)$. -/
theorem one_ne_neg_one_gl : (1 : GL (Fin 2) ℤ) ≠ -1 := by
  intro h
  have := congrArg (fun T : GL (Fin 2) ℤ => T.val 0 0) h
  simp at this

/-- Helper: the scalar matrix $\varepsilon \cdot 1 \in \mathrm{GL}_2(\mathbb Z)$ for $\varepsilon \in \mathbb Z^{\times}$ (`ε`), i.e. $1$ or $-1$. -/
def autSgn (ε : ℤˣ) : GL (Fin 2) ℤ := if ε = 1 then 1 else -1

/-- Helper: `autSgn` is multiplicative (`ε ε'`: signs). -/
theorem autSgn_mul (ε ε' : ℤˣ) : autSgn (ε * ε') = autSgn ε * autSgn ε' := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    simp [autSgn]

/-- Helper: `autSgn 1 = 1`. -/
theorem autSgn_one : autSgn 1 = 1 := by simp [autSgn]

/-- Helper: `autSgn (-1) = -1`. -/
theorem autSgn_neg_one : autSgn (-1) = -1 := by
  have : ¬ ((-1 : ℤˣ) = 1) := by decide
  simp [autSgn, this]

/-- Helper: `autSgn ε` is central (`ε`: sign; `x`: matrix). -/
theorem autSgn_commute (ε : ℤˣ) (x : GL (Fin 2) ℤ) : autSgn ε * x = x * autSgn ε := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [autSgn_one, autSgn_neg_one]

/-- Helper: `autSgn` is injective. -/
theorem autSgn_inj {ε ε' : ℤˣ} (h : autSgn ε = autSgn ε') : ε = ε' := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl <;>
    first | rfl | (exfalso; simp [autSgn_one, autSgn_neg_one] at h)

/-- Helper: a subgroup `G` of $\mathrm{GL}_2(\mathbb Z)$ containing $-1$ (`hm1`) all of whose elements are $\pm T_0^{\nu}$ (`hall`) for an element `T₀ ∈ G` of infinite order (`hord`) is isomorphic to $\mathbb Z^{\times} \times \mathbb Z$. -/
theorem exists_mulEquiv_of_pm_pow {G : Subgroup (GL (Fin 2) ℤ)} (hm1 : (-1 : GL (Fin 2) ℤ) ∈ G)
    {T₀ : GL (Fin 2) ℤ} (hT₀ : T₀ ∈ G) (hord : orderOf T₀ = 0)
    (hall : ∀ T ∈ G, ∃ ν : ℤ, T = T₀ ^ ν ∨ T = -(T₀ ^ ν)) :
    Nonempty (G ≃* ℤˣ × Multiplicative ℤ) := by
  have hmem : ∀ (ε : ℤˣ) (n : ℤ), autSgn ε * T₀ ^ n ∈ G := by
    intro ε n
    refine G.mul_mem ?_ (G.zpow_mem hT₀ n)
    rcases Int.units_eq_one_or ε with rfl | rfl
    · rw [autSgn_one]; exact G.one_mem
    · rw [autSgn_neg_one]; exact hm1
  have hinf : ¬ IsOfFinOrder T₀ := orderOf_eq_zero_iff.mp hord
  have hinj : Function.Injective (fun n : ℤ => T₀ ^ n) := injective_zpow_iff_not_isOfFinOrder.mpr hinf
  let φ : ℤˣ × Multiplicative ℤ →* G :=
    { toFun := fun p => ⟨autSgn p.1 * T₀ ^ (Multiplicative.toAdd p.2), hmem _ _⟩
      map_one' := by
        apply Subtype.ext; simp [autSgn_one]
      map_mul' := fun p q => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, autSgn_mul, toAdd_mul, Prod.fst_mul, Prod.snd_mul, _root_.zpow_add]
        calc autSgn p.1 * autSgn q.1 * (T₀ ^ Multiplicative.toAdd p.2 * T₀ ^ Multiplicative.toAdd q.2)
            = autSgn p.1 * (autSgn q.1 * T₀ ^ Multiplicative.toAdd p.2) * T₀ ^ Multiplicative.toAdd q.2 := by
              group
          _ = autSgn p.1 * (T₀ ^ Multiplicative.toAdd p.2 * autSgn q.1) * T₀ ^ Multiplicative.toAdd q.2 := by
              rw [autSgn_commute q.1 (T₀ ^ Multiplicative.toAdd p.2)]
          _ = _ := by group }
  have hφinj : Function.Injective φ := by
    rintro ⟨ε, n⟩ ⟨ε', n'⟩ h
    have h' : autSgn ε * T₀ ^ (Multiplicative.toAdd n) = autSgn ε' * T₀ ^ (Multiplicative.toAdd n') :=
      congrArg Subtype.val h
    -- reduce to `T₀ ^ m = ± T₀ ^ m'`
    have key : ε = ε' := by
      by_contra hne
      have hcase : (autSgn ε = 1 ∧ autSgn ε' = -1) ∨ (autSgn ε = -1 ∧ autSgn ε' = 1) := by
        rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or ε' with rfl | rfl
        · exact absurd rfl hne
        · left; simp [autSgn_one, autSgn_neg_one]
        · right; simp [autSgn_one, autSgn_neg_one]
        · exact absurd rfl hne
      -- T₀ ^ m = - T₀ ^ m' (or the reverse); square
      have hsq : T₀ ^ (2 * (Multiplicative.toAdd n - Multiplicative.toAdd n')) = 1 := by
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at h'
          have h3 : T₀ ^ (Multiplicative.toAdd n) = -T₀ ^ (Multiplicative.toAdd n') := by simpa using h'
          have : T₀ ^ (2 * (Multiplicative.toAdd n - Multiplicative.toAdd n')) =
              (T₀ ^ (Multiplicative.toAdd n) * (T₀ ^ (Multiplicative.toAdd n'))⁻¹) ^ 2 := by
            rw [← _root_.zpow_neg, ← _root_.zpow_add, ← _root_.zpow_natCast, ← _root_.zpow_mul]; congr 1; push_cast; ring
          rw [this, h3]
          simp
        · rw [h1, h2] at h'
          have h3 : -T₀ ^ (Multiplicative.toAdd n) = T₀ ^ (Multiplicative.toAdd n') := by simpa using h'
          have : T₀ ^ (2 * (Multiplicative.toAdd n - Multiplicative.toAdd n')) =
              (T₀ ^ (Multiplicative.toAdd n) * (T₀ ^ (Multiplicative.toAdd n'))⁻¹) ^ 2 := by
            rw [← _root_.zpow_neg, ← _root_.zpow_add, ← _root_.zpow_natCast, ← _root_.zpow_mul]; congr 1; push_cast; ring
          rw [this]
          have h4 : T₀ ^ (Multiplicative.toAdd n) = -T₀ ^ (Multiplicative.toAdd n') := by
            rw [← h3]; simp
          rw [h4]
          simp
      have hz : 2 * (Multiplicative.toAdd n - Multiplicative.toAdd n') = 0 := by
        apply hinj
        simpa using hsq
      have hnn : Multiplicative.toAdd n = Multiplicative.toAdd n' := by omega
      rw [hnn] at h'
      have := mul_right_cancel h'
      exact hne (autSgn_inj this)
    subst key
    have : Multiplicative.toAdd n = Multiplicative.toAdd n' := by
      apply hinj
      exact mul_left_cancel h'
    exact Prod.ext rfl (Multiplicative.toAdd.injective this)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨T, hT⟩
    obtain ⟨ν, hν | hν⟩ := hall T hT
    · exact ⟨(1, Multiplicative.ofAdd ν), Subtype.ext (by simp [φ, autSgn_one, hν])⟩
    · exact ⟨(-1, Multiplicative.ofAdd ν), Subtype.ext (by simp [φ, autSgn_neg_one, hν])⟩
  exact ⟨(MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).symm⟩



/-! ### Part (a): the structure of the proper automorphism group -/

/-- Helper: the group `AutSL f` of `Binary` is the library's `Siegel.AutPlus f` (`f`: a binary form). -/
theorem autSL_eq_autPlus (f : BinQF) : AutSL f = Siegel.AutPlus f := by
  ext T
  rw [mem_autSL, Siegel.mem_autPlus_iff]

/-- Helper: the value of a binary form `f` at an integer vector `x` is $a x_0^2 + b x_0 x_1 + c x_1^2$. -/
theorem eval_vec (f : BinQF) (x : Fin 2 → ℤ) :
    QuadForm.eval f x = f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2 :=
  binqf_evalIn ℤ f x

/-- Helper: forms with proportional values have the same proper automorphs. -/
theorem autPlus_eq_of_eval_smul {g f : BinQF} {k : ℤ} (hk : k ≠ 0)
    (h : ∀ x : Fin 2 → ℤ, QuadForm.eval g x = k * QuadForm.eval f x) :
    Siegel.AutPlus g = Siegel.AutPlus f := by
  ext T
  rw [Siegel.mem_autPlus_iff, Siegel.mem_autPlus_iff]
  have : T ∈ Siegel.Aut g ↔ T ∈ Siegel.Aut f := by
    rw [mem_aut_iff_actForm, mem_aut_iff_actForm, actForm_eq_iff, actForm_eq_iff]
    constructor
    · intro H x
      have := H x
      rw [h, h] at this
      exact mul_left_cancel₀ hk this
    · intro H x
      rw [h, h, H x]
  rw [this]

/-- Helper: from the coefficients of a primitive form to the coefficients $(A, B, C)$ of a classical form
$A x^2 + 2B xy + C y^2$ proportional to it (factor $k = 1$ if $b$ is even, $k = 2$ if $b$ is odd). -/
theorem exists_cform_data {f : BinQF} (hprim : f.IsPrimitive) :
    ∃ A B C k : ℤ, k ≠ 0 ∧ k * f.a = A ∧ k * f.b = 2 * B ∧ k * f.c = C ∧
      Int.gcd A (Int.gcd B C) = 1 ∧
      ((k ^ 2 = 1 ∧ f.disc % 4 = 0 ∧ ¬ (Even A ∧ Even C)) ∨
        (k ^ 2 = 4 ∧ f.disc % 4 = 1 ∧ Even A ∧ Even C)) := by
  rcases Int.even_or_odd f.b with ⟨B, hB⟩ | ⟨B, hB⟩
  · refine ⟨f.a, B, f.c, 1, one_ne_zero, by ring, by omega, by ring, ?_,
      Or.inl ⟨by norm_num, ?_, ?_⟩⟩
    · set g := Int.gcd f.a (Int.gcd B f.c) with hg
      have h1 : (g : ℤ) ∣ f.a := Int.gcd_dvd_left ..
      have h2 : (g : ℤ) ∣ (Int.gcd B f.c : ℤ) := Int.gcd_dvd_right ..
      have h3 : (g : ℤ) ∣ B := h2.trans (Int.gcd_dvd_left ..)
      have h4 : (g : ℤ) ∣ f.c := h2.trans (Int.gcd_dvd_right ..)
      have hu := hprim g h1 (by rw [hB]; exact dvd_add h3 h3) h4
      rw [Int.isUnit_iff] at hu
      omega
    · have : f.disc = 4 * (B * B - f.a * f.c) := by simp only [BinQF.disc, hB]; ring
      omega
    · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      have hu := hprim 2 ⟨r, by omega⟩ ⟨B, by omega⟩ ⟨s, by omega⟩
      rw [Int.isUnit_iff] at hu
      omega
  · refine ⟨2 * f.a, f.b, 2 * f.c, 2, two_ne_zero, rfl, by ring, rfl, ?_,
      Or.inr ⟨by norm_num, ?_, ⟨f.a, by ring⟩, ⟨f.c, by ring⟩⟩⟩
    · set g := Int.gcd (2 * f.a) (Int.gcd f.b (2 * f.c)) with hg
      have h1 : (g : ℤ) ∣ 2 * f.a := Int.gcd_dvd_left ..
      have h2 : (g : ℤ) ∣ (Int.gcd f.b (2 * f.c) : ℤ) := Int.gcd_dvd_right ..
      have h3 : (g : ℤ) ∣ f.b := h2.trans (Int.gcd_dvd_left ..)
      have h4 : (g : ℤ) ∣ 2 * f.c := h2.trans (Int.gcd_dvd_right ..)
      have hcop : IsCoprime f.b 2 := ⟨1, -B, by rw [hB]; ring⟩
      have hcop' : IsCoprime (g : ℤ) 2 := hcop.of_isCoprime_of_dvd_left h3
      have h1' : (g : ℤ) ∣ f.a := hcop'.dvd_of_dvd_mul_left h1
      have h4' : (g : ℤ) ∣ f.c := hcop'.dvd_of_dvd_mul_left h4
      have hu := hprim g h1' h3 h4'
      rw [Int.isUnit_iff] at hu
      omega
    · have : f.disc = 4 * (B * B + B - f.a * f.c) + 1 := by simp only [BinQF.disc, hB]; ring
      omega


/-- Helper: for $(A, B, C) = (k a, k b / 2, k c)$ (`ha hb hc`), $4(AC - B^2) = -k^2 D$. -/
theorem four_mul_cform_disc {f : BinQF} {A B C k : ℤ} (ha : k * f.a = A) (hb : k * f.b = 2 * B)
    (hc : k * f.c = C) : 4 * (A * C - B ^ 2) = -(k ^ 2) * f.disc := by
  have : 4 * (A * C - B ^ 2) = 4 * A * C - (2 * B) ^ 2 := by ring
  rw [this, ← ha, ← hc, ← hb]
  simp only [BinQF.disc]
  ring

/-- Helper: as `exists_cform_data`, with $A > 0$, for a form of negative discriminant. -/
theorem exists_cform_data_pos {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc < 0) :
    ∃ A B C k : ℤ, 0 < A ∧ k ≠ 0 ∧ k * f.a = A ∧ k * f.b = 2 * B ∧ k * f.c = C ∧
      Int.gcd A (Int.gcd B C) = 1 ∧
      ((k ^ 2 = 1 ∧ f.disc % 4 = 0 ∧ ¬ (Even A ∧ Even C)) ∨
        (k ^ 2 = 4 ∧ f.disc % 4 = 1 ∧ Even A ∧ Even C)) := by
  obtain ⟨A, B, C, k, hk, ha, hb, hc, hg, hpar⟩ := exists_cform_data hprim
  have hd := four_mul_cform_disc ha hb hc
  have hk2 : 0 < k ^ 2 := by positivity
  have hA : A ≠ 0 := by
    rintro rfl
    nlinarith [sq_nonneg B]
  rcases lt_or_gt_of_ne hA with hneg | hpos
  · refine ⟨-A, -B, -C, -k, by omega, neg_ne_zero.mpr hk, by linear_combination (-1) * ha,
      by linear_combination (-1) * hb, by linear_combination (-1) * hc, ?_, ?_⟩
    · simpa [Int.gcd_neg, Int.neg_gcd] using hg
    · simpa [even_neg] using hpar
  · exact ⟨A, B, C, k, hpos, hk, ha, hb, hc, hg, hpar⟩

/-- Helper: a binary form whose discriminant is a square is isotropic over $\mathbb Q$. -/
theorem isotropicIn_of_isSquare {f : BinQF} (hsq : IsSquare f.disc) : f.IsotropicIn ℚ := by
  obtain ⟨m, hm⟩ := hsq
  have hm' : (f.b : ℚ) ^ 2 - 4 * f.a * f.c = m * m := by
    have : f.b ^ 2 - 4 * f.a * f.c = m * m := hm
    exact_mod_cast this
  by_cases ha : f.a = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro h; have := congrFun h 0; simp at this
    · rw [binqf_evalIn]; simp [ha]
  · have ha' : (f.a : ℚ) ≠ 0 := by exact_mod_cast ha
    refine ⟨![(-(f.b : ℚ) + m) / (2 * f.a), 1], ?_, ?_⟩
    · intro h; have := congrFun h 1; simp at this
    · rw [binqf_evalIn]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      linear_combination (-1 : ℚ) * hm'

/-- Helper: the classical form $A x^2 + 2B xy + C y^2$ proportional to a binary form $f$ of nonsquare
discriminant is anisotropic over $\mathbb Q$. -/
theorem not_isotropicIn_cform {f : BinQF} (hD : f.disc ≠ 0) (hns : ¬ IsSquare f.disc) {A B C k : ℤ}
    (hk : k ≠ 0) (ha : k * f.a = A) (hb : k * f.b = 2 * B) (hc : k * f.c = C) :
    ¬ (cform A B C).IsotropicIn ℚ := by
  rintro ⟨x, hx0, hx⟩
  rw [evalIn_cform] at hx
  have hx' : (k : ℚ) * (f.a * x 0 ^ 2 + f.b * x 0 * x 1 + f.c * x 1 ^ 2) = 0 := by
    have ha' : (k : ℚ) * f.a = A := by exact_mod_cast ha
    have hb' : (k : ℚ) * f.b = 2 * B := by exact_mod_cast hb
    have hc' : (k : ℚ) * f.c = C := by exact_mod_cast hc
    linear_combination hx + (x 0 ^ 2) * ha' + (x 0 * x 1) * hb' + (x 1 ^ 2) * hc'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hiso : f.IsotropicIn ℚ := by
    refine ⟨x, hx0, ?_⟩
    rw [binqf_evalIn]
    exact (mul_eq_zero.mp hx').resolve_left hk'
  have hreg : f.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [binqf_det]
    intro h; apply hD; simp only [BinQF.disc]; linarith
  obtain ⟨M, -, hM⟩ := binqf_disc_sq f hreg hiso
  exact hns ⟨M, by simp only [BinQF.disc]; rw [hM]; ring⟩

/-- Helper: $-1$ is a proper automorph of every binary form `f`. -/
theorem neg_one_mem_autPlus (f : BinQF) : (-1 : GL (Fin 2) ℤ) ∈ Siegel.AutPlus f := by
  rw [← autSL_eq_autPlus]; exact neg_one_mem_autSL f

/-- Helper: a group of proper automorphs all of whose elements are $\pm 1$ has order $2$. -/
theorem card_autPlus_of_pm (f : BinQF) (h : ∀ T ∈ Siegel.AutPlus f, T = 1 ∨ T = -1) :
    Nat.card (Siegel.AutPlus f) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨-1, neg_one_mem_autPlus f⟩, ?_, ?_⟩
  · intro h'
    have := congrArg (fun T : Siegel.AutPlus f => (T : GL (Fin 2) ℤ).val 0 0) h'
    simp at this
  · ext ⟨T, hT⟩
    simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h T hT with rfl | rfl
    · left; rfl
    · right; rfl


/-- Helper: a binary form `f` of nonzero discriminant (`hD`) is nondegenerate. -/
theorem nondegenerate_of_disc_ne {f : BinQF} (hD : f.disc ≠ 0) : f.Nondegenerate := by
  unfold QuadForm.Nondegenerate
  rw [binqf_det]
  intro h; apply hD; simp only [BinQF.disc]; linarith

/-- Helper: if $(A, B, C)$ is proportional to the coefficients of `f` with factor `k` (`ha hb hc`), the classical form `cform A B C` has values $k f(\vec x)$. -/
theorem eval_cform_of_data {f : BinQF} {A B C k : ℤ} (ha : k * f.a = A) (hb : k * f.b = 2 * B)
    (hc : k * f.c = C) (x : Fin 2 → ℤ) :
    QuadForm.eval (cform A B C) x = k * QuadForm.eval f x := by
  rw [eval_cform, eval_vec]
  linear_combination (-(x 0) ^ 2) * ha + (-(x 0 * x 1)) * hb + (-(x 1) ^ 2) * hc

/-- **The group of proper automorphs of a primitive form of positive nonsquare discriminant**
(Cassels, Ch. 14, pp. 342–343, case (iv), after Ch. 13, Thm. 3.1): $O^{+}$ is the product of a cyclic group of
order $2$ ($\{\pm 1\}$) and an infinite cyclic group; here as a group isomorphism with
$\mathbb Z^{\times} \times \mathbb Z$ ($\mathbb Z$ written multiplicatively). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (iv), D > 0 not a square (O⁺ ≅ {±1} × ℤ)"]
theorem autPlus_equiv_of_pos_nonsq {f : BinQF} (hprim : f.IsPrimitive) (hD : 0 < f.disc)
    (hns : ¬ IsSquare f.disc) : Nonempty (Siegel.AutPlus f ≃* ℤˣ × Multiplicative ℤ) := by
  obtain ⟨A, B, C, k, hk, ha, hb, hc, hg, -⟩ := exists_cform_data hprim
  have hd := four_mul_cform_disc ha hb hc
  have hk2 : 0 < k ^ 2 := by positivity
  have hind : A * C - B ^ 2 < 0 := by nlinarith
  have haniso := not_isotropicIn_cform hD.ne' hns hk ha hb hc
  obtain ⟨T₀, hT₀, hord, hall⟩ := autPlus_cform_cyclic hg hind haniso
  have heq : Siegel.AutPlus (cform A B C) = Siegel.AutPlus f :=
    autPlus_eq_of_eval_smul hk (eval_cform_of_data ha hb hc)
  rw [heq] at hT₀ hall
  exact exists_mulEquiv_of_pm_pow (neg_one_mem_autPlus f) hT₀ hord hall

/-- **The group of proper automorphs of a form of positive square discriminant has order $2$**
(Cassels, Ch. 14, p. 343, case (iii), after Ch. 13, Lemma 3.2). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (iii), D a square (|O⁺| = 2)"]
theorem card_autPlus_of_pos_sq {f : BinQF} (hD : 0 < f.disc) (hsq : IsSquare f.disc) :
    Nat.card (Siegel.AutPlus f) = 2 :=
  card_autPlus_of_pm f
    (binary_isotropic_aut f (nondegenerate_of_disc_ne hD.ne') (isotropicIn_of_isSquare hsq)).1


/-! ### Negative discriminant: the definite case -/

/-- Helper: for a primitive form `f` of negative discriminant (`hprim`, `hD`) there is a positive definite classical form `cform A B C` with $A > 0$, $\gcd(A, B, C) = 1$, with the same proper automorphs as `f` and the invariants needed for Ch. 13, Example 1. -/
theorem neg_data {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc < 0) :
    ∃ A B C k : ℤ, 0 < A ∧ Int.gcd A (Int.gcd B C) = 1 ∧ 0 < A * C - B ^ 2 ∧
      4 * (A * C - B ^ 2) = -(k ^ 2) * f.disc ∧
      Siegel.AutPlus (cform A B C) = Siegel.AutPlus f ∧
      ((k ^ 2 = 1 ∧ f.disc % 4 = 0 ∧ ¬ (Even A ∧ Even C)) ∨
        (k ^ 2 = 4 ∧ f.disc % 4 = 1 ∧ Even A ∧ Even C)) := by
  obtain ⟨A, B, C, k, hA, hk, ha, hb, hc, hg, hpar⟩ := exists_cform_data_pos hprim hD
  have hd := four_mul_cform_disc ha hb hc
  have hk2 : 0 < k ^ 2 := by positivity
  exact ⟨A, B, C, k, hA, hg, by nlinarith, hd,
    autPlus_eq_of_eval_smul hk (eval_cform_of_data ha hb hc), hpar⟩

/-- **The group of proper automorphs for $D = -4$ has order $4$** (Cassels, Ch. 14, p. 343, case (ii), after
Ch. 13, Example 1). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (ii), D = -4 (|O⁺| = 4)"]
theorem card_autPlus_of_disc_neg_four {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc = -4) :
    Nat.card (Siegel.AutPlus f) = 4 := by
  obtain ⟨A, B, C, k, hA, hg, hd, h4, heq, hpar⟩ := neg_data hprim (by omega)
  rw [← heq]
  rcases hpar with ⟨hk2, h0, hnn⟩ | ⟨hk2, h1, -⟩
  · have hd1 : A * C - B ^ 2 = 1 := by rw [hD, hk2] at h4; omega
    exact (example_1 hA hd hg).2.1 hd1
  · omega

/-- **The group of proper automorphs for $D = -3$ has order $6$** (Cassels, Ch. 14, p. 343, case (ii), after
Ch. 13, Example 1). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (ii), D = -3 (|O⁺| = 6)"]
theorem card_autPlus_of_disc_neg_three {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc = -3) :
    Nat.card (Siegel.AutPlus f) = 6 := by
  obtain ⟨A, B, C, k, hA, hg, hd, h4, heq, hpar⟩ := neg_data hprim (by omega)
  rw [← heq]
  rcases hpar with ⟨hk2, h0, hnn⟩ | ⟨hk2, h1, hAe, hCe⟩
  · omega
  · have hd3 : A * C - B ^ 2 = 3 := by rw [hD, hk2] at h4; omega
    exact (example_1 hA hd hg).2.2.1 hd3 hAe hCe

/-- **The group of proper automorphs for $D < -4$ has order $2$**, namely $\{\pm 1\}$ (Cassels, Ch. 14, p. 343,
case (i), after Ch. 13, Example 1; the discriminants $-3, -4$ are the exceptions (ii), and $-1, -2$ do not occur). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (i), D < -4 (|O⁺| = 2)"]
theorem card_autPlus_of_neg_other {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc < -4) :
    Nat.card (Siegel.AutPlus f) = 2 := by
  obtain ⟨A, B, C, k, hA, hg, hd, hk, heq, hpar⟩ := neg_data hprim (by omega)
  by_cases hd3 : A * C - B ^ 2 = 3
  · rcases hpar with ⟨hk2, h0, hnn⟩ | ⟨hk2, h1, hAe, hCe⟩
    · rw [← heq]; exact (example_1 hA hd hg).2.2.2 hd3 hnn
    · exfalso; rw [hk2] at hk; omega
  · have hd1 : A * C - B ^ 2 ≠ 1 := by
      intro h1
      rcases hpar with ⟨hk2, h0, hnn⟩ | ⟨hk2, h1', hAe, hCe⟩
      · rw [hk2] at hk; omega
      · rw [hk2] at hk; omega
    exact card_autPlus_of_pm f (by rw [← heq]; exact (example_1 hA hd hg).1 hd1 hd3)


/-! ### The index of the squares, in every case -/

/-- Helper: `Siegel.AutPlus f` is finite if its cardinality is a nonzero number `n` (`hn`, `h`). -/
theorem finite_autPlus_of_card {f : BinQF} {n : ℕ} (hn : n ≠ 0) (h : Nat.card (Siegel.AutPlus f) = n) :
    Finite (Siegel.AutPlus f) :=
  Nat.finite_of_card_ne_zero (by rw [h]; exact hn)

/-- Helper: if $O^{+}(f)$ is finite (`hfin`) and $D \ne 0$ (`hD`), the squares have index $2$ ($O^{+}$ is abelian with exactly the two elements $\pm 1$ of order dividing $2$). -/
theorem index_squares_of_finite_autPlus {f : BinQF} (hD : f.disc ≠ 0) (hfin : Finite (Siegel.AutPlus f)) :
    (squares (Siegel.AutPlus f)).index = 2 := by
  rw [← autSL_eq_autPlus] at hfin ⊢
  rw [index_squares_of_finite (AutSL f) (autSL_comm hD)]
  exact card_sq_eq_one f

/-- Helper: if $O^{+}(f) \cong \mathbb Z^{\times} \times \mathbb Z$ (`e`) and $D \ne 0$ (`hD`), the squares have index $4$. -/
theorem index_squares_of_equiv_autPlus {f : BinQF} (hD : f.disc ≠ 0)
    (e : Siegel.AutPlus f ≃* ℤˣ × Multiplicative ℤ) : (squares (Siegel.AutPlus f)).index = 4 := by
  rw [← autSL_eq_autPlus] at e ⊢
  exact index_squares_of_equiv (AutSL f) (autSL_comm hD) e

/-- **The order of $O^{+}/(O^{+})^{2}$** (Cassels, Ch. 14, p. 343, "on computing $O^{+}/(O^{+})^{2}$ for these
groups"): for a primitive binary form $f$ of nonzero discriminant $D$, the index of the subgroup generated by the
squares of the group $O^{+}(f)$ of proper integral automorphs is $4$ if $D > 0$ is not a perfect square, and $2$
otherwise. -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (computation of O⁺/(O⁺)² for the groups (i)–(iv))"]
theorem index_squares_autPlus {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc ≠ 0) :
    (squares (Siegel.AutPlus f)).index = if 0 < f.disc ∧ ¬ IsSquare f.disc then 4 else 2 := by
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hnot : ¬ (0 < f.disc ∧ ¬ IsSquare f.disc) := fun h => absurd h.1 (not_lt.mpr hneg.le)
    simp only [hnot, ↓reduceIte]
    apply index_squares_of_finite_autPlus hD
    have hmod := BinQF.disc_mod_four f
    by_cases h4 : f.disc = -4
    · exact finite_autPlus_of_card (by norm_num) (card_autPlus_of_disc_neg_four hprim h4)
    by_cases h3 : f.disc = -3
    · exact finite_autPlus_of_card (by norm_num) (card_autPlus_of_disc_neg_three hprim h3)
    exact finite_autPlus_of_card (by norm_num) (card_autPlus_of_neg_other hprim (by omega))
  · by_cases hsq : IsSquare f.disc
    · have hnot : ¬ (0 < f.disc ∧ ¬ IsSquare f.disc) := fun h => h.2 hsq
      simp only [hnot, ↓reduceIte]
      exact index_squares_of_finite_autPlus hD
        (finite_autPlus_of_card (by norm_num) (card_autPlus_of_pos_sq hpos hsq))
    · have hP : 0 < f.disc ∧ ¬ IsSquare f.disc := ⟨hpos, hsq⟩
      simp only [hP]
      obtain ⟨e⟩ := autPlus_equiv_of_pos_nonsq hprim hpos hsq
      exact index_squares_of_equiv_autPlus hD e

/-- Helper: a finite group of order `n` with fewer than `n` elements `x` satisfying $x^2 = 1$ has an element with $x^2 \ne 1$. -/
theorem exists_sq_ne_one {G : Type*} [Group G] [Finite G] {n : ℕ} (hc : Nat.card G = n)
    (h2 : Nat.card {x : G // x * x = 1} < n) : ∃ x : G, x * x ≠ 1 := by
  by_contra h
  push Not at h
  have := Nat.card_congr (Equiv.subtypeUnivEquiv h)
  omega

/-- Helper: a group of order $4$ with exactly two elements satisfying $x^2 = 1$ is cyclic. -/
theorem isCyclic_of_card_four {G : Type*} [Group G] [Finite G] (hc : Nat.card G = 4)
    (h2 : Nat.card {x : G // x * x = 1} = 2) : IsCyclic G := by
  obtain ⟨x, hx⟩ := exists_sq_ne_one hc (by omega)
  have hdvd : orderOf x ∣ 4 := hc ▸ orderOf_dvd_natCard x
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have h4 : orderOf x = 4 := by
    generalize hn : orderOf x = n at hdvd hle
    interval_cases n
    · omega
    · exfalso
      have := pow_orderOf_eq_one x
      rw [hn, pow_one] at this
      exact hx (by rw [this]; simp)
    · exfalso
      have := pow_orderOf_eq_one x
      rw [hn] at this
      exact hx (by rw [← pow_two]; exact this)
    · omega
    · rfl
  exact isCyclic_of_orderOf_eq_card x (by rw [h4, hc])


/-- Helper: an abelian group (`hcomm`) of order $6$ with exactly two elements satisfying $x^2 = 1$ is cyclic. -/
theorem isCyclic_of_card_six {G : Type*} [Group G] [Finite G] (hc : Nat.card G = 6)
    (hcomm : ∀ x y : G, x * y = y * x) (h2 : Nat.card {x : G // x * x = 1} = 2) : IsCyclic G := by
  -- an element `z ≠ 1` with `z * z = 1`
  have hex : ∃ z : G, z ≠ 1 ∧ z * z = 1 := by
    obtain ⟨a, b, hab, -⟩ := Nat.card_eq_two_iff.mp h2
    by_cases ha : a.1 = 1
    · refine ⟨b.1, fun hb => hab (Subtype.ext (ha.trans hb.symm)), b.2⟩
    · exact ⟨a.1, ha, a.2⟩
  obtain ⟨z, hz1, hz⟩ := hex
  have hzo : orderOf z = 2 := by
    apply orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hc]; norm_num)
  have hcop : Nat.Coprime (orderOf z) (orderOf x) := by rw [hzo, hx]; norm_num
  have hcomm' : Commute z x := hcomm z x
  have h6 : orderOf (z * x) = 6 := by
    rw [hcomm'.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hzo, hx]
  exact isCyclic_of_orderOf_eq_card (z * x) (by rw [h6, hc])



/-- Helper: exactly two elements `T` of `Siegel.AutPlus f` satisfy $T^2 = 1$. -/
theorem card_sq_eq_one_autPlus (f : BinQF) : Nat.card {T : Siegel.AutPlus f // T * T = 1} = 2 := by
  rw [← autSL_eq_autPlus]; exact card_sq_eq_one f

/-- **$O^{+}$ is cyclic in the cases (i)--(iii)** (Cassels, Ch. 14, p. 343): for a primitive form `f` of negative
discriminant, or of positive square discriminant (`hD`), the group $O^{+}(f)$ of proper integral automorphs is
cyclic (of order $2$, $4$ or $6$, `card_autPlus_of_neg_other`, `card_autPlus_of_disc_neg_four`,
`card_autPlus_of_disc_neg_three`, `card_autPlus_of_pos_sq`). -/
@[kb "cassels1978" "Ch. 14, §4, p. 343 (i)-(iii) (O⁺ is cyclic)"]
theorem isCyclic_autPlus {f : BinQF} (hprim : f.IsPrimitive) (hD : f.disc < 0 ∨ (0 < f.disc ∧ IsSquare f.disc)) :
    IsCyclic (Siegel.AutPlus f) := by
  have hD0 : f.disc ≠ 0 := by
    rcases hD with h | h
    · omega
    · exact h.1.ne'
  have hcomm := autSL_comm hD0
  rw [autSL_eq_autPlus] at hcomm
  have hsq := card_sq_eq_one_autPlus f
  have h2 : ∀ {n : ℕ}, n ≠ 0 → Nat.card (Siegel.AutPlus f) = n → Finite (Siegel.AutPlus f) :=
    fun hn h => finite_autPlus_of_card hn h
  rcases hD with hneg | ⟨hpos, hsqr⟩
  · have hmod := BinQF.disc_mod_four f
    by_cases h4 : f.disc = -4
    · have hc := card_autPlus_of_disc_neg_four hprim h4
      have := h2 (by norm_num) hc
      exact isCyclic_of_card_four hc hsq
    by_cases h3 : f.disc = -3
    · have hc := card_autPlus_of_disc_neg_three hprim h3
      have := h2 (by norm_num) hc
      exact isCyclic_of_card_six hc (fun x y => hcomm x y) hsq
    · have hc := card_autPlus_of_neg_other hprim (by omega : f.disc < -4)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card hc
  · have hc := card_autPlus_of_pos_sq hpos hsqr
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card hc

/-! ### The count of ambiguous forms in an ambiguous class -/

/-- **The number of ambiguous forms in an ambiguous class is the order of $O^{+}/(O^{+})^{2}$** (Cassels, Ch. 14,
pp. 342–343): let $f$ be a binary form of nonzero discriminant that has an improper integral automorph (equivalently,
whose proper class is ambiguous, `isAmbiguous_iff_improper`). Then the number of ambiguous forms
($[a, 0, c]$ or $[a, a, c]$, `IsAmbiguousForm`) properly equivalent to $f$ equals the index of the subgroup of
squares in the group $O^{+}(f)$ of proper integral automorphs (the order of the quotient $O^{+}/(O^{+})^{2}$;
$O^{+}$ is abelian, `autSL_comm`). -/
@[kb "cassels1978" "Ch. 14, §4, pp. 342–343 (number of ambiguous forms in an ambiguous class = |O⁺/(O⁺)²|)"]
theorem ncard_ambiguousForms_eq_index {f : BinQF} (hD : f.disc ≠ 0) (hamb : Siegel.HasImproperAut f) :
    {g : BinQF | SLEquiv f g ∧ IsAmbiguousForm g}.ncard = (squares (Siegel.AutPlus f)).index := by
  obtain ⟨S₀, hS₀, hdet⟩ := hamb
  rw [← autSL_eq_autPlus]
  exact ncard_ambiguous_aux hD (S₀ := S₀) ⟨hS₀, hdet⟩ (autSL_comm hD)


section Classes

open FormClass

variable {D : ℤ}

/-- **Cassels, Ch. 14, pp. 342–343, for classes of primitive forms:** for an ambiguous class $\mathfrak C$ of
primitive forms of discriminant $D$ and any form $f \in \mathfrak C$, the number of ambiguous forms in $\mathfrak C$
(`IsAmbiguousForm`, forms of the shape $[a, 0, c]$ or $[a, a, c]$) is the index of the subgroup of squares in
$O^{+}(f)$, i.e. the order of $O^{+}/(O^{+})^{2}$. Here `f : PrimForm D` with `hC : IsAmbiguous (mk f)` (the class
of $f$ is ambiguous); the count is over `PrimForm D` with class `mk f`. -/
@[kb "cassels1978" "Ch. 14, §4, pp. 342–343 (ambiguous forms in an ambiguous class, O⁺/(O⁺)²)"]
theorem ncard_ambiguousForms_in_class [NonzeroDisc D] (f : PrimForm D) (hC : IsAmbiguous (mk f)) :
    {g : PrimForm D | mk g = mk f ∧ IsAmbiguousForm g.1}.ncard =
      (squares (Siegel.AutPlus f.1)).index := by
  have hD : f.1.disc ≠ 0 := by rw [f.2.2]; exact NonzeroDisc.ne_zero
  have hamb : Siegel.HasImproperAut f.1 := by
    obtain ⟨p, q, r, s, hd, h⟩ := (isAmbiguous_iff_improper f).mp hC
    refine ⟨Binary.glOf p q r s (by rw [hd]; norm_num), mem_aut_iff.mpr (by simpa using h), ?_⟩
    simp [Matrix.det_fin_two_of, hd]
  rw [← ncard_ambiguousForms_eq_index hD hamb]
  have himg : {g : BinQF | SLEquiv f.1 g ∧ IsAmbiguousForm g} =
      Subtype.val '' {g : PrimForm D | mk g = mk f ∧ IsAmbiguousForm g.1} := by
    ext g
    constructor
    · rintro ⟨hsl, hg⟩
      have hsl : SLEquiv f.1 g := hsl
      have hprim : g.IsPrimitive := SLEquiv.isPrimitive hsl f.2.1
      have hdisc : g.disc = D := by
        obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp hsl
        rw [BinQF.disc_subst, hd]
        simpa using f.2.2
      exact ⟨⟨g, hprim, hdisc⟩, ⟨mk_eq_mk.mpr (SLEquiv.symm hsl), hg⟩, rfl⟩
    · rintro ⟨g', ⟨hmk, hg⟩, rfl⟩
      exact ⟨(mk_eq_mk.mp hmk).symm, hg⟩
  rw [himg]
  exact (Set.ncard_image_of_injective _ Subtype.val_injective).symm

/-- **Cassels, Ch. 14, Lemma 4.3 (p. 343):** the number of ambiguous forms in an ambiguous class of primitive forms
of discriminant $D$ is $4$ if $D > 0$ is not a perfect square, and $2$ otherwise. Here `f : PrimForm D` with
`hC : IsAmbiguous (mk f)` and the count is over the forms of the class `mk f`. -/
@[kb "cassels1978" "Ch. 14, Lemma 4.3, p. 343"]
theorem ncard_ambiguousForms_in_class_eq [NonzeroDisc D] (f : PrimForm D) (hC : IsAmbiguous (mk f)) :
    {g : PrimForm D | mk g = mk f ∧ IsAmbiguousForm g.1}.ncard =
      if 0 < D ∧ ¬ IsSquare D then 4 else 2 := by
  have hD : f.1.disc ≠ 0 := by rw [f.2.2]; exact NonzeroDisc.ne_zero
  rw [ncard_ambiguousForms_in_class f hC, index_squares_autPlus f.2.1 hD, f.2.2]

end Classes

end QuadFormsKB.Composition
