/-
# The order of the orthogonal group over a finite field, and unimodular self-densities

**Layer:** forms over a commutative ring (column peeling), then a DVR $R$ with finite residue field of odd size $q$
($\pi \nmid 2$) and a unimodular form ($\pi \nmid \det H_Q$).

Witt's theorem over $\mathbb F_q$ is **not** needed (nor the order $|O_n(\mathbb F_q)|$):
we count self-representations column by column. For $T = \langle t_0, \dots, t_{r}\rangle$ diagonal and a first column
$x$ with $Q(x) = t_0$, the remaining columns lie in $x^\perp$, and $x^\perp$ carries a form $Q'_x$ in $n - 1$ variables
with $\det H_{Q'_x} \equiv \det H_Q/(2t_0)$ up to unit squares (`exists_split`); every $Q'_x$ has the **same** count by
induction (the count depends only on the dimension and the discriminant), so
$$A_\pi(Q, T) = r_\pi(Q, t_0)\cdot A_\pi(Q', T'),$$
with $r_\pi(Q, t_0)$ from Hanke's Table 1 (`card_mod_pi_of_unimodular`).

**Proves**
* `QuadForm.compMat_succ_iff` (first column / remaining columns), `QuadForm.exists_split` (an orthogonal splitting
  $Q \circ g = \langle Q(x)\rangle \perp Q'$ with $g e_0 = x$, over any commutative ring, when $2Q(x)$ and one coordinate
  of $x$ are units), `QuadForm.card_fiber_split`;
* `DVR.repCountForm_diag_unimodular`: $A_\pi(Q, \langle t\rangle) = o_n(\varepsilon)$ for unimodular $Q$ and unit $t$ of the
  same discriminant square class, where (`oCount`)
  $$o_{2m+1} = 2q^{m^2}\prod_{i=1}^{m}(q^{2i}-1), \qquad o_{2m}(\varepsilon) = 2q^{m(m-1)}(q^m - \varepsilon)\prod_{i=1}^{m-1}(q^{2i} - 1),$$
  $\varepsilon = \chi((-1)^m \det)$ (so $o_n = |O_n(\mathbb F_q)|$; Artin, *Geometric Algebra*, Ch. III [unverified]);
* `DVR.card_orthMod_one_unimodular`: $|O(Q \bmod \pi)| = o_n(\chi_D)$, $\chi_D$ = `chiDisc Q`;
* **the unimodular self-densities** (`DVR.localDensityForm_self_odd`, `DVR.localDensityForm_self_even`):
  $$\beta_\pi(Q, Q) = 2\prod_{i=1}^{m}(1 - q^{-2i})\ \ (n = 2m+1), \qquad
    \beta_\pi(Q, Q) = 2(1 - \chi_D q^{-m})\prod_{i=1}^{m-1}(1 - q^{-2i})\ \ (n = 2m),$$
  Siegel's $\alpha_\pi = \beta_\pi/2$ being the bracketed products (Kitaoka 1993, §5.6; Conway–Sloane 1988, Table 1
  [unverified]).
**Depends on** `FormDensitySelf.lean`, `DVRUnimodular.lean`. Indices 0-based ($x_0$ is the first coordinate).
-/
import QuadFormsKB.LocalDensity.FormDensitySelf
import QuadFormsKB.LocalDensity.DVRUnimodular
import QuadFormsKB.LocalDensity.NFFormDensity

open Matrix

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace QuadFormsKB.QuadForm

variable {A : Type*} [CommRing A] {m r N : ℕ}

/-! ### Peeling off the first coordinate -/

/-- **The tail of a form** in $m + 1$ variables: the form in $x_1, \dots, x_m$ (renumbered $0, \dots, m-1$) with
coefficients $c_{i+1, j+1}$, i.e. $Q$ restricted to $x_0 = 0$. -/
def tail (Q : QuadForm A (m + 1)) : QuadForm A m :=
  ⟨Q.coeff.submatrix Fin.succ Fin.succ, fun i j h => Q.upper (show id j.succ < id i.succ from
    Fin.succ_lt_succ_iff.mpr h)⟩

@[simp] theorem tail_coeff (Q : QuadForm A (m + 1)) (i j : Fin m) :
    Q.tail.coeff i j = Q.coeff i.succ j.succ := rfl

theorem tail_diag (t : Fin (m + 1) → A) : (diag t).tail = diag (fun i => t i.succ) := by
  ext i j
  simp [tail, diag, Matrix.diagonal_apply]

theorem tail_map {B : Type*} [CommRing B] (f : A →+* B) (Q : QuadForm A (m + 1)) :
    (Q.map f).tail = Q.tail.map f := by
  ext i j; rfl

/-- The columns $1, \dots, r$ of an $N \times (r+1)$ matrix. -/
abbrev restCols (X : Matrix (Fin N) (Fin (r + 1)) A) : Matrix (Fin N) (Fin r) A := X.submatrix id Fin.succ

/-- The first column of a matrix. -/
abbrev col0 (X : Matrix (Fin N) (Fin (r + 1)) A) : Fin N → A := fun l => X l 0

/-- **First column and remaining columns:** $Q \circ X = T$ iff $Q(X_0) = T_{00}$, $B(X_0, X_{j+1}) = T_{0,j+1}$ and
$Q \circ (X_1, \dots, X_r) = \mathrm{tail}(T)$. -/
theorem compMat_succ_iff (Q : QuadForm A N) (T : QuadForm A (r + 1)) (X : Matrix (Fin N) (Fin (r + 1)) A) :
    Q.compMat X = T ↔ Q.eval (col0 X) = T.coeff 0 0 ∧
      (∀ j : Fin r, col0 X ⬝ᵥ (Q.hessian *ᵥ fun l => X l j.succ) = T.coeff 0 j.succ) ∧
      Q.compMat (restCols X) = T.tail := by
  constructor
  · rintro rfl
    refine ⟨?_, fun j => ?_, ?_⟩
    · rw [compMat_coeff]; simp
    · rw [compMat_coeff, if_pos (Fin.zero_le _), if_neg (Fin.succ_ne_zero j).symm]
    · apply ext_upper
      intro i j hij
      rw [tail_coeff, compMat_coeff, compMat_coeff, if_pos hij, if_pos (Fin.succ_le_succ_iff.mpr hij)]
      simp only [Fin.succ_inj]
      rfl
  · rintro ⟨h0, h1, h2⟩
    apply ext_upper
    intro i j hij
    rw [compMat_coeff, if_pos hij]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using h0
      | succ j => rw [if_neg (Fin.succ_ne_zero j).symm]; exact h1 j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        have := congrArg (fun S : QuadForm A r => S.coeff i j) h2
        simp only [tail_coeff, compMat_coeff, if_pos (Fin.succ_le_succ_iff.mp hij)] at this
        simp only [Fin.succ_inj]
        exact this

/-- For a form split at $0$ ($c_{0,j+1} = 0$), $B(e_0, y) = 2c_{00}\,y_0$. -/
theorem single_zero_dotProduct_hessian (Q : QuadForm A (m + 1)) (hQ : ∀ j : Fin m, Q.coeff 0 j.succ = 0)
    (y : Fin (m + 1) → A) : Pi.single 0 1 ⬝ᵥ (Q.hessian *ᵥ y) = 2 * Q.coeff 0 0 * y 0 := by
  rw [single_one_dotProduct, mulVec, dotProduct, Fin.sum_univ_succ]
  have h1 : ∀ j : Fin m, Q.coeff j.succ 0 = 0 := fun j =>
    Q.upper (show id (0 : Fin (m + 1)) < id j.succ from Fin.succ_pos j)
  simp only [hessian, Matrix.add_apply, Matrix.transpose_apply, hQ, h1, zero_mul, add_zero,
    Finset.sum_const_zero]
  ring

/-- For a split form and $y_0 = 0$: $Q(y) = \mathrm{tail}(Q)(y_1, \dots, y_m)$. -/
theorem eval_of_zero (Q : QuadForm A (m + 1)) (y : Fin (m + 1) → A) (hy : y 0 = 0) :
    Q.eval y = Q.tail.eval (fun i => y i.succ) := by
  simp only [QuadForm.eval, QuadForm.evalIn, Fin.sum_univ_succ, hy, mul_zero, zero_mul, ite_self,
    Finset.sum_const_zero, zero_add, tail_coeff, Fin.succ_le_succ_iff]

/-- For $Y$ with first row $0$: $Q \circ Y = \mathrm{tail}(Q) \circ (\text{rows } 1, \dots, m \text{ of } Y)$. -/
theorem compMat_of_row_zero (Q : QuadForm A (m + 1)) (Y : Matrix (Fin (m + 1)) (Fin r) A)
    (hY : ∀ j, Y 0 j = 0) : Q.compMat Y = Q.tail.compMat (Y.submatrix Fin.succ id) := by
  apply eq_of_eval_eq
  intro z
  rw [eval_compMat, eval_compMat, eval_of_zero]
  · rfl
  · simp [mulVec, dotProduct, hY]

/-- **The fibre over $e_0$ for a split form.** If $Q$ is split at $0$ ($c_{0, j+1} = 0$), $2c_{00}$ is a unit and
$T = \langle t\rangle$ with $t_0 = c_{00}$, then the representations $X$ of $T$ by $Q$ with first column $e_0$ are in
bijection with the representations of $\langle t_1, \dots, t_r\rangle$ by $\mathrm{tail}(Q)$. -/
theorem card_fiber_split (Q : QuadForm A (m + 1)) (hQ : ∀ j : Fin m, Q.coeff 0 j.succ = 0)
    (hu : IsUnit (2 * Q.coeff 0 0)) (t : Fin (r + 1) → A) (ht : t 0 = Q.coeff 0 0) :
    Nat.card {X : Matrix (Fin (m + 1)) (Fin (r + 1)) A // Q.compMat X = diag t ∧ col0 X = Pi.single 0 1} =
      Nat.card {Z : Matrix (Fin m) (Fin r) A // Q.tail.compMat Z = diag (fun i => t i.succ)} := by
  classical
  have hdiag0 : ∀ j : Fin r, (diag t).coeff 0 j.succ = 0 := fun j => by
    simp [diag, (Fin.succ_ne_zero j).symm]
  -- the matrix with first column e₀, first row (1, 0, …, 0), lower block Z
  let build : Matrix (Fin m) (Fin r) A → Matrix (Fin (m + 1)) (Fin (r + 1)) A := fun Z =>
    Matrix.of fun l b => Fin.cases (motive := fun _ => A)
      ((Pi.single (0 : Fin (m + 1)) (1 : A) : Fin (m + 1) → A) l)
      (fun j => Fin.cases (motive := fun _ => A) 0 (fun l' => Z l' j) l) b
  have hrow : ∀ X : Matrix (Fin (m + 1)) (Fin (r + 1)) A, Q.compMat X = diag t →
      col0 X = Pi.single 0 1 → ∀ j : Fin r, X 0 j.succ = 0 := by
    intro X hX hX0 j
    have h1 := ((compMat_succ_iff Q (diag t) X).mp hX).2.1 j
    rw [hdiag0, hX0, single_zero_dotProduct_hessian Q hQ] at h1
    exact (hu.mul_right_eq_zero).mp h1
  have hB : ∀ Z : Matrix (Fin m) (Fin r) A, Q.tail.compMat Z = diag (fun i => t i.succ) →
      Q.compMat (build Z) = diag t := by
    intro Z hZ
    have hc0 : col0 (build Z) = Pi.single 0 1 := rfl
    rw [compMat_succ_iff]
    refine ⟨?_, fun j => ?_, ?_⟩
    · rw [hc0, eval_single, ← ht]; simp [diag]
    · rw [hc0, single_zero_dotProduct_hessian Q hQ, hdiag0]
      simp [build]
    · rw [compMat_of_row_zero Q _ (fun j => rfl), tail_diag]
      exact hZ
  refine Nat.card_congr
    { toFun := fun X => ⟨(restCols X.1).submatrix Fin.succ id, ?_⟩
      invFun := fun Z => ⟨build Z.1, hB Z.1 Z.2, rfl⟩
      left_inv := fun X => ?_
      right_inv := fun Z => rfl }
  · rw [← compMat_of_row_zero Q _ (hrow X.1 X.2.1 X.2.2), ← tail_diag]
    exact ((compMat_succ_iff Q (diag t) X.1).mp X.2.1).2.2
  · apply Subtype.ext
    ext l b
    induction b using Fin.cases with
    | zero => exact (congrFun X.2.2 l).symm
    | succ j =>
      induction l using Fin.cases with
      | zero => exact (hrow X.1 X.2.1 X.2.2 j).symm
      | succ l => rfl

/-- **Transport of fibres by $g \in \mathrm{GL}_N$:** $X \mapsto g^{-1}X$ bijects the representations of $T$ by $Q$ with
first column $x$ and those by $Q \circ g$ with first column $g^{-1}x$. -/
theorem card_fiber_transport (Q : QuadForm A N) (T : QuadForm A (r + 1)) (g : GL (Fin N) A)
    (x : Fin N → A) :
    Nat.card {X : Matrix (Fin N) (Fin (r + 1)) A // Q.compMat X = T ∧ col0 X = x} =
      Nat.card {Y : Matrix (Fin N) (Fin (r + 1)) A //
        (Q.compMat g.val).compMat Y = T ∧ col0 Y = g⁻¹.val *ᵥ x} := by
  have hcol : ∀ (M : Matrix (Fin N) (Fin N) A) (X : Matrix (Fin N) (Fin (r + 1)) A),
      col0 (M * X) = M *ᵥ col0 X := fun M X => by ext l; simp [mul_apply, mulVec, dotProduct]
  refine Nat.card_congr
    { toFun := fun X => ⟨g⁻¹.val * X.1, ?_, ?_⟩
      invFun := fun Y => ⟨g.val * Y.1, ?_, ?_⟩
      left_inv := fun X => ?_
      right_inv := fun Y => ?_ }
  · rw [compMat_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul]; exact X.2.1
  · rw [hcol, X.2.2]
  · rw [← compMat_mul]; exact Y.2.1
  · rw [hcol, Y.2.2, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  · apply Subtype.ext
    show g.val * (g⁻¹.val * X.1) = X.1
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  · apply Subtype.ext
    show g⁻¹.val * (g.val * Y.1) = Y.1
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem vecMulVec_mulVec (u v y : Fin N → A) : vecMulVec u v *ᵥ y = (v ⬝ᵥ y) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Orthogonal splitting off a vector** (over any commutative ring): if $2Q(x)$ and some coordinate $x_i$ are
units, there is $g \in \mathrm{GL}_{m+1}$ with $g e_0 = x$ and $(Q \circ g)$ split at $0$: $c'_{0, j+1} = 0$. Explicitly
$g = E L P$ with $E = 1 + (x - e_i)e_i^{\mathsf T}$ ($\det = x_i$), $L = 1 - e_i c^{\mathsf T}$ ($\det = 1$),
$c_s = B(x, e_s)/(2Q(x))$ ($s \ne i$), $c_i = 0$, and $P$ the transposition $(0\ i)$; its columns are $x$ and
$e_s - c_s x$ ($s \ne i$). -/
theorem exists_split (Q : QuadForm A (m + 1)) (x : Fin (m + 1) → A) (hx : IsUnit (2 * Q.eval x))
    (i : Fin (m + 1)) (hi : IsUnit (x i)) :
    ∃ g : GL (Fin (m + 1)) A, g.val *ᵥ Pi.single 0 1 = x ∧
      ∀ j : Fin m, (Q.compMat g.val).coeff 0 j.succ = 0 := by
  classical
  set u := hx.unit
  set ei : Fin (m + 1) → A := Pi.single i 1
  set c : Fin (m + 1) → A := fun s => if s = i then 0 else (x ⬝ᵥ (Q.hessian *ᵥ Pi.single s 1)) * ↑u⁻¹
  set E : Matrix (Fin (m + 1)) (Fin (m + 1)) A := 1 + vecMulVec (x - ei) ei
  set L : Matrix (Fin (m + 1)) (Fin (m + 1)) A := 1 - vecMulVec ei c
  set P : Matrix (Fin (m + 1)) (Fin (m + 1)) A := (Equiv.swap 0 i).permMatrix A
  set M := E * L * P
  have hE : ∀ y, E *ᵥ y = y + (ei ⬝ᵥ y) • (x - ei) := fun y => by
    rw [add_mulVec, one_mulVec, vecMulVec_mulVec]
  have hL : ∀ y, L *ᵥ y = y - (c ⬝ᵥ y) • ei := fun y => by
    rw [sub_mulVec, one_mulVec, vecMulVec_mulVec]
  have hP : ∀ b, P *ᵥ Pi.single b 1 = Pi.single (Equiv.swap 0 i b) 1 := fun b => by
    rw [permMatrix_mulVec]
    funext l
    simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]
  have hcol : ∀ b, M *ᵥ Pi.single b 1 = if b = 0 then x else
      Pi.single (Equiv.swap 0 i b) 1 - c (Equiv.swap 0 i b) • x := by
    intro b
    rw [show M = E * L * P from rfl, ← mulVec_mulVec, ← mulVec_mulVec, hP, hL, dotProduct_single]
    split_ifs with hb
    · subst hb
      rw [Equiv.swap_apply_left]
      have : c i = 0 := by simp [c]
      rw [this, mul_one, zero_smul, sub_zero, hE, single_one_dotProduct]
      simp [ei]
    · have hs : Equiv.swap 0 i b ≠ i := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact hb
      rw [mul_one, hE]
      have : ei ⬝ᵥ (Pi.single (Equiv.swap 0 i b) 1 - c (Equiv.swap 0 i b) • ei) = - c (Equiv.swap 0 i b) := by
        simp [ei, dotProduct_sub, hs]
      rw [this]
      module
  have hdetM : IsUnit M.det := by
    have hdE : E.det = x i := by
      rw [show E = 1 + replicateCol Unit (x - ei) * replicateRow Unit ei by
          simp only [E]; rw [vecMulVec_eq Unit],
        det_one_add_replicateCol_mul_replicateRow]
      simp [ei]
    have hdL : L.det = 1 := by
      rw [show L = 1 - replicateCol Unit ei * replicateRow Unit c by
          simp only [L]; rw [vecMulVec_eq Unit],
        det_one_sub_mul_comm, det_unique, Matrix.sub_apply, Matrix.one_apply_eq,
        replicateRow_mul_replicateCol_apply]
      simp [ei, c]
    rw [show M = E * L * P from rfl, det_mul, det_mul, hdE, hdL, det_permutation, mul_one]
    refine hi.mul ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 i)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.nonsingInvUnit M hdetM, ?_, fun j => ?_⟩
  · show M *ᵥ Pi.single 0 1 = x
    rw [hcol, if_pos rfl]
  · show (Q.compMat M).coeff 0 j.succ = 0
    rw [compMat_coeff, if_pos (Fin.zero_le _), if_neg (Fin.succ_ne_zero j).symm]
    have h0 : (fun l => M l 0) = x := by
      have := hcol 0
      rw [if_pos rfl, mulVec_single_one] at this
      exact this
    have h1 : (fun l => M l j.succ) = Pi.single (Equiv.swap 0 i j.succ) 1 - c (Equiv.swap 0 i j.succ) • x := by
      have := hcol j.succ
      rw [if_neg (Fin.succ_ne_zero j), mulVec_single_one] at this
      exact this
    have hs : Equiv.swap 0 i j.succ ≠ i := by
      rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact Fin.succ_ne_zero j
    rw [h0, h1, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, dotProduct_hessian_self]
    simp only [c, if_neg hs, smul_eq_mul]
    have : (2 * Q.eval x) * ↑u⁻¹ = 1 := by
      rw [show (2 * Q.eval x) = (u : A) from rfl, Units.mul_inv]
    linear_combination (-(x ⬝ᵥ (Q.hessian *ᵥ Pi.single (Equiv.swap 0 i j.succ) 1))) * this

end QuadFormsKB.QuadForm

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {m n : ℕ}

local notation "𝔽" => IsLocalRing.ResidueField R
local notation "res" => IsLocalRing.residue R

theorem eval_map_comp' {B : Type*} [CommRing B] (f : R →+* B) (Q : QuadForm R n) (x : Fin n → R) :
    (Q.map f).eval (fun i => f (x i)) = f (Q.eval x) := by
  simp only [QuadForm.evalIn, QuadForm.map, Matrix.map_apply, map_sum, Algebra.algebraMap_self,
    RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem map_diag {B : Type*} [CommRing B] (f : R →+* B) (t : Fin n → R) :
    (diag t).map f = diag (fun i => f (t i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dvd_eval_of_dvd (Q : QuadForm R n) (π : R) (x : Fin n → R) (hx : ∀ i, π ∣ x i) :
    π ∣ Q.eval x := by
  unfold QuadForm.eval QuadForm.evalIn
  refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
  split_ifs
  · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (hx i) _) _
  · exact dvd_zero _

/-- For a form split at $0$: $\det H_Q = 2c_{00}\det H_{\mathrm{tail}(Q)}$ (expand along row $0$). -/
theorem det_hessian_split (Q : QuadForm R (m + 1)) (hQ : ∀ j : Fin m, Q.coeff 0 j.succ = 0) :
    Q.hessian.det = 2 * Q.coeff 0 0 * Q.tail.hessian.det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  have h1 : ∀ j : Fin m, Q.hessian 0 j.succ = 0 := by
    intro j
    simp [hessian, hQ j, Q.upper (show id (0 : Fin (m + 1)) < id j.succ from Fin.succ_pos j)]
  simp only [h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  have : Q.hessian.submatrix Fin.succ Fin.succ = Q.tail.hessian := by
    ext i j; simp [hessian, tail]
  rw [this]
  have h00 : Q.hessian 0 0 = 2 * Q.coeff 0 0 := by simp [hessian]; ring
  rw [h00]

/-- Counting by the first column. -/
theorem card_eq_sum_fiber {A : Type*} [CommRing A] [Finite A] {N r : ℕ} (Q : QuadForm A N)
    (T : QuadForm A (r + 1)) [Fintype (Fin N → A)] :
    Nat.card {X : Matrix (Fin N) (Fin (r + 1)) A // Q.compMat X = T} =
      ∑ x : Fin N → A, Nat.card {X : Matrix (Fin N) (Fin (r + 1)) A // Q.compMat X = T ∧ col0 X = x} := by
  classical
  have : Finite (Matrix (Fin N) (Fin (r + 1)) A) := Pi.finite
  have hfin : ∀ x : Fin N → A, Fintype {X : Matrix (Fin N) (Fin (r + 1)) A // Q.compMat X = T ∧ col0 X = x} :=
    fun x => Fintype.ofFinite _
  rw [← Nat.card_sigma]
  refine Nat.card_congr ((Equiv.sigmaFiberEquiv (fun X : {X // Q.compMat X = T} => col0 X.1)).symm.trans
    (Equiv.sigmaCongrRight fun x =>
      { toFun := fun X => ⟨X.1.1, X.1.2, X.2⟩
        invFun := fun X => ⟨⟨X.1, X.2.1⟩, X.2.2⟩
        left_inv := fun X => rfl
        right_inv := fun X => rfl }))

variable (π : R)

local notation "mk" => Ideal.Quotient.mk (Ideal.span {π ^ 1})

/-- **The fibre over a first column** $x$ with $Q(x) \equiv t_0$, for unimodular non-dyadic data: it has
$A_\pi(Q', \langle t_1, \dots, t_m\rangle)$ elements for a form $Q'$ in $m$ variables with
$2a\det H_{Q'} = d^2\det H_Q$, $d$ a unit, $a \equiv t_0 \bmod \pi$ (from `QuadForm.exists_split` on a lift of $x$). -/
theorem card_fiber_eq (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (Q : QuadForm R (m + 1))
    (t : Fin (m + 1) → R) (ht0 : ¬ π ∣ t 0) (x : Fin (m + 1) → R ⧸ Ideal.span {π ^ 1})
    (hx : (Q.map mk).eval x = mk (t 0)) :
    ∃ Q' : QuadForm R m, ∃ d a : R, IsUnit d ∧ π ∣ a - t 0 ∧ 2 * a * Q'.hessian.det = d ^ 2 * Q.hessian.det ∧
      Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⧸ Ideal.span {π ^ 1}) //
        (Q.map mk).compMat X = (diag t).map mk ∧ col0 X = x} =
      repCountForm Q' (diag (fun i => t i.succ)) π 1 := by
  classical
  obtain ⟨x', hx'⟩ : ∃ x' : Fin (m + 1) → R, (fun l => mk (x' l)) = x :=
    ⟨fun l => (Ideal.Quotient.mk_surjective (x l)).choose,
      funext fun l => (Ideal.Quotient.mk_surjective (x l)).choose_spec⟩
  have hQx : mk (Q.eval x') = mk (t 0) := by rw [← eval_map_comp', hx', hx]
  have hdvd : π ∣ Q.eval x' - t 0 := by
    have := Ideal.Quotient.eq.mp hQx
    rwa [pow_one, Ideal.mem_span_singleton] at this
  have hQu : ¬ π ∣ Q.eval x' := fun h => ht0 (by simpa using dvd_sub h hdvd)
  have h2u : IsUnit (2 * Q.eval x') :=
    dvr_isUnit_of_not_dvd hπ (fun h => (hπ.prime.dvd_or_dvd h).elim h2 hQu)
  obtain ⟨i, hi⟩ : ∃ i, IsUnit (x' i) := by
    by_contra h
    push Not at h
    exact hQu (dvd_eval_of_dvd Q π x' fun i => by
      by_contra hc; exact h i (dvr_isUnit_of_not_dvd hπ hc))
  obtain ⟨g, hg0, hsplit⟩ := QuadForm.exists_split Q x' h2u i hi
  set Qt := Q.compMat g.val with hQt
  have hcol0 : (fun l => g.val l 0) = x' := by rw [← hg0, mulVec_single_one]; rfl
  have hQt00 : Qt.coeff 0 0 = Q.eval x' := by
    rw [hQt, compMat_coeff, if_pos le_rfl, if_pos rfl, hcol0]
  refine ⟨Qt.tail, g.val.det, Q.eval x', (Units.isUnit g).map Matrix.detMonoidHom, hdvd, ?_, ?_⟩
  · have h := det_hessian_split Qt hsplit
    rw [hQt, hessian_compMat, det_mul, det_mul, det_transpose] at h
    rw [← hQt, hQt00] at h
    linear_combination -h
  · let gb := Matrix.GeneralLinearGroup.map mk g
    rw [card_fiber_transport _ _ gb x]
    have hgx : gb⁻¹.val *ᵥ x = Pi.single 0 1 := by
      have h1 : gb.val *ᵥ Pi.single 0 1 = x := by
        rw [← hx', ← hg0]
        funext l
        rw [mulVec_single_one, mulVec_single_one]
        rfl
      rw [← h1, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    have hQm : (Q.map mk).compMat gb.val = Qt.map mk := map_compMat mk Q g.val
    rw [hgx, hQm, map_diag]
    have hu : IsUnit (2 * (Qt.map mk).coeff 0 0) := by
      have : 2 * (Qt.map mk).coeff 0 0 = mk (2 * Q.eval x') := by
        simp [QuadForm.map, hQt00, map_ofNat]
      rw [this]; exact h2u.map _
    rw [card_fiber_split (Qt.map mk) (fun j => by simp [QuadForm.map, hsplit j]) hu
      (fun i => mk (t i)) (by simp [QuadForm.map, hQt00, hQx])]
    unfold repCountForm
    rw [tail_map, map_diag]

/-! ### The count $o_n$ and the induction -/

/-- $o_{2m+1}(q) = 2q^{m^2}\prod_{i=1}^m(q^{2i}-1)$ $(= |O_{2m+1}(\mathbb F_q)|)$. -/
def oOdd (q : ℤ) (m : ℕ) : ℤ := 2 * q ^ (m ^ 2) * ∏ i ∈ Finset.range m, (q ^ (2 * (i + 1)) - 1)

/-- $o_{2m}(q, \varepsilon) = 2q^{m(m-1)}(q^m - \varepsilon)\prod_{i=1}^{m-1}(q^{2i}-1)$ $(= |O^{\varepsilon}_{2m}(\mathbb F_q)|$, $m \ge 1)$. -/
def oEven (q : ℤ) (m : ℕ) (ε : ℤ) : ℤ :=
  2 * q ^ (m * (m - 1)) * (q ^ m - ε) * ∏ i ∈ Finset.range (m - 1), (q ^ (2 * (i + 1)) - 1)

/-- **The order of the orthogonal group** of a nondegenerate quadratic space of dimension $n$ over $\mathbb F_q$,
$q$ odd, with $\varepsilon = \chi((-1)^{n/2}\det)$ for even $n$ (ignored for odd $n$): $o_0 = 1$, $o_{2m+1}$ = `oOdd`,
$o_{2m}$ = `oEven` (Artin, *Geometric Algebra*, Ch. III, Thm 3.12 [unverified]; Conway–Sloane 1988, §? [unverified]).
Proved to be $|O(Q \bmod \pi)|$ in `card_orthMod_one_unimodular`. -/
@[kb "kitaoka1993" "§5.6 (|O_n(F_q)|) [unverified]"]
def oCount (q : ℤ) (n : ℕ) (ε : ℤ) : ℤ :=
  if n = 0 then 1 else if Even n then oEven q (n / 2) ε else oOdd q (n / 2)

/-- The sign $\chi((-1)^{\lfloor n/2\rfloor}\prod_i t_i)$ of a diagonal form $\langle t_0, \dots, t_{n-1}\rangle$. -/
def epsT [Fintype 𝔽] [DecidableEq 𝔽] (t : Fin n → R) : ℤ :=
  quadraticChar 𝔽 ((-1) ^ (n / 2) * res (∏ i, t i))

theorem card_matrix_zero {A : Type*} [CommRing A] (P : Matrix (Fin 0) (Fin 0) A → Prop) (hP : ∀ X, P X) :
    Nat.card {X : Matrix (Fin 0) (Fin 0) A // P X} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩, ⟨⟨0, hP 0⟩⟩⟩

theorem res_ne_zero {π : R} (hπ : Irreducible π) {a : R} (ha : ¬ π ∣ a) : res a ≠ 0 :=
  fun h => ha ((residue_eq_zero_iff_dvd hπ a).1 h)

theorem res_prod_ne_zero {π : R} (hπ : Irreducible π) {t : Fin n → R} (ht : ∀ i, ¬ π ∣ t i) :
    res (∏ i, t i) ≠ 0 := by
  rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun i _ => res_ne_zero hπ (ht i)

theorem epsT_sq [Fintype 𝔽] [DecidableEq 𝔽] {π : R} (hπ : Irreducible π) {t : Fin n → R}
    (ht : ∀ i, ¬ π ∣ t i) : epsT t ^ 2 = 1 := by
  unfold epsT
  refine quadraticChar_sq_one (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (res_prod_ne_zero hπ ht))

theorem oCount_even_step (q : ℤ) (l : ℕ) (ε : ℤ) :
    (q ^ (2 * l + 1) - ε * q ^ l) * oCount q (2 * l + 1) 0 = oCount q (2 * l + 1 + 1) ε := by
  have h1 : ¬ Even (2 * l + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one l
  have h2 : Even (2 * l + 1 + 1) := ⟨l + 1, by ring⟩
  simp only [oCount, if_neg (by omega : 2 * l + 1 ≠ 0), if_neg h1, if_neg (by omega : 2 * l + 1 + 1 ≠ 0),
    if_pos h2, show (2 * l + 1) / 2 = l by omega, show (2 * l + 1 + 1) / 2 = l + 1 by omega, oOdd, oEven,
    Nat.add_sub_cancel]
  ring

theorem oCount_odd_step (q : ℤ) (l : ℕ) (ε : ℤ) (hε : ε ^ 2 = 1) :
    (q ^ (2 * (l + 1)) + ε * q ^ (l + 1)) * oCount q (2 * (l + 1)) ε = oCount q (2 * (l + 1) + 1) 0 := by
  have h1 : ¬ Even (2 * (l + 1) + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one _
  have h2 : Even (2 * (l + 1)) := ⟨l + 1, by ring⟩
  simp only [oCount, if_neg (by omega : 2 * (l + 1) + 1 ≠ 0), if_neg h1, if_neg (by omega : 2 * (l + 1) ≠ 0),
    if_pos h2, show (2 * (l + 1) + 1) / 2 = l + 1 by omega, show 2 * (l + 1) / 2 = l + 1 by omega, oOdd,
    oEven, Nat.add_sub_cancel, Finset.prod_range_succ]
  linear_combination (-2) * q ^ ((l + 1) * l) * q ^ (l + 1) *
    (∏ i ∈ Finset.range l, (q ^ (2 * (i + 1)) - 1)) * hε


theorem oCount_odd_any (q : ℤ) (l : ℕ) (ε ε' : ℤ) : oCount q (2 * l + 1) ε = oCount q (2 * l + 1) ε' := by
  have h1 : ¬ Even (2 * l + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one l
  simp only [oCount, if_neg (by omega : 2 * l + 1 ≠ 0), if_neg h1]

/-- **$A_\pi(Q, \langle t\rangle) = o_n$ for unimodular non-dyadic data** (by induction on $n$, peeling the first
column, `card_fiber_eq`): if $\pi \nmid 2\det H_Q$, all $t_i$ are units and $2^n\prod t_i \equiv c^2\det H_Q$ mod $\pi$
($c \ne 0$; same discriminant square class), then the number of $X \in M_n(R/\pi)$ with $Q \circ X = \langle t\rangle$
is $o_n(q, \chi((-1)^{\lfloor n/2\rfloor}\prod t_i))$. No Witt theorem is used: the induction carries the
discriminant, and the count of each fibre depends only on it. -/
@[kb "kitaoka1993" "§5.6 (|O_n(F_q)|) [unverified]"]
theorem repCountForm_diag_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (hπ : Irreducible π) (h2 : ¬ π ∣ 2) :
    ∀ (n : ℕ) (Q : QuadForm R n) (t : Fin n → R), ¬ π ∣ Q.hessian.det → (∀ i, ¬ π ∣ t i) →
      (∃ c : 𝔽, c ≠ 0 ∧ res (2 ^ n * ∏ i, t i) = c ^ 2 * res Q.hessian.det) →
      (repCountForm Q (QuadForm.diag t) π 1 : ℤ) = oCount (q R) n (epsT t) := by
  intro n
  induction n with
  | zero =>
    intro Q t _ _ _
    unfold repCountForm
    rw [card_matrix_zero _ (fun X => QuadForm.ext (Matrix.ext fun i => i.elim0))]
    simp [oCount]
  | succ m ih =>
    intro Q t hdet ht hdisc
    classical
    have := finite_quot_pow π hπ 1
    let _ : Fintype (R ⧸ Ideal.span {π ^ 1}) := Fintype.ofFinite _
    have h2F : (2 : 𝔽) ≠ 0 := by
      have := res_ne_zero hπ h2; rwa [map_ofNat] at this
    obtain ⟨c, hc, hcd⟩ := hdisc
    -- the fibres
    have hfib : ∀ x : Fin (m + 1) → R ⧸ Ideal.span {π ^ 1},
        (Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⧸ Ideal.span {π ^ 1}) //
          (Q.map mk).compMat X = (QuadForm.diag t).map mk ∧ col0 X = x} : ℤ) =
        if (Q.map mk).eval x = mk (t 0) then oCount (q R) m (epsT (fun i => t i.succ)) else 0 := by
      intro x
      split_ifs with hx
      · obtain ⟨Q', d, a, hd, ha, hrel, hcard⟩ := card_fiber_eq π hπ h2 Q t (ht 0) x hx
        rw [hcard]
        refine ih Q' (fun i => t i.succ) ?_ (fun i => ht i.succ) ?_
        · intro hD
          apply hdet
          have : π ∣ d ^ 2 * Q.hessian.det := hrel ▸ dvd_mul_of_dvd_right hD _
          exact (hd.pow 2).dvd_mul_left.mp this
        · have hδ : res d ≠ 0 := (hd.map res).ne_zero
          have hτ : res (t 0) ≠ 0 := res_ne_zero hπ (ht 0)
          have hra : res a = res (t 0) := by
            rw [← sub_eq_zero, ← map_sub]; exact (residue_eq_zero_iff_dvd hπ _).2 ha
          have hrel' := congrArg res hrel
          simp only [map_mul, map_pow, map_ofNat, hra] at hrel'
          refine ⟨c / res d, div_ne_zero hc hδ, ?_⟩
          have hprod : res (2 ^ (m + 1) * ∏ i, t i) =
              2 * res (t 0) * res (2 ^ m * ∏ i : Fin m, t i.succ) := by
            rw [Fin.prod_univ_succ]; simp only [map_mul, map_pow, map_ofNat]; ring
          rw [hprod] at hcd
          have h2τ : (2 : 𝔽) * res (t 0) ≠ 0 := mul_ne_zero h2F hτ
          apply mul_left_cancel₀ h2τ
          rw [hcd]
          calc c ^ 2 * res Q.hessian.det = c ^ 2 * (res d ^ 2 * res Q.hessian.det) / res d ^ 2 := by
                field_simp
            _ = c ^ 2 * (2 * res (t 0) * res Q'.hessian.det) / res d ^ 2 := by rw [hrel']
            _ = _ := by ring
      · rw [Nat.cast_eq_zero, Nat.card_eq_zero]
        left
        refine ⟨fun X => hx ?_⟩
        have h := ((compMat_succ_iff _ _ X.1).mp X.2.1).1
        rw [X.2.2, map_diag] at h
        simpa [QuadForm.diag] using h
    unfold repCountForm
    rw [card_eq_sum_fiber, Nat.cast_sum, Finset.sum_congr rfl (fun x _ => hfib x), Finset.sum_ite,
      Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    -- the number of first columns is r_π(t₀) (Table 1)
    have hrc : ((Finset.univ.filter fun x : Fin (m + 1) → R ⧸ Ideal.span {π ^ 1} =>
        (Q.map mk).eval x = mk (t 0)).card : ℤ) = repCount Q π 1 (t 0) := by
      unfold repCount
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 2
    rw [hrc]
    have T1 := card_mod_pi_of_unimodular Q π hπ h2 hdet (by omega) (t 0) (ht 0)
    -- the characters
    have hgram : resGramDet Q = res (∏ i, t i) * (c⁻¹) ^ 2 := by
      unfold resGramDet
      have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
      simp only [map_mul, map_pow, map_ofNat] at hcd
      field_simp
      linear_combination -hcd
    have hchi : ∀ y : 𝔽, quadraticChar 𝔽 (y * (c⁻¹) ^ 2) = quadraticChar 𝔽 y := fun y => by
      rw [map_mul, quadraticChar_sq_one' (inv_ne_zero hc), mul_one]
    rcases Nat.even_or_odd' m with ⟨l, rfl | rfl⟩
    · -- n = 2l + 1 odd
      have hodd : Odd (2 * l + 1) := odd_two_mul_add_one l
      rw [(T1.2 hodd).2]
      have heps : chiDiscT Q (t 0) = epsT (fun i : Fin (2 * l) => t i.succ) := by
        unfold chiDiscT epsT
        rw [hgram, Fin.prod_univ_succ, show (2 * l + 1 - 1) / 2 = 2 * l / 2 by omega]
        rw [show (-1 : 𝔽) ^ (2 * l / 2) * (res (t 0 * ∏ i : Fin (2 * l), t i.succ) * c⁻¹ ^ 2) * res (t 0) =
          ((-1) ^ (2 * l / 2) * res (∏ i : Fin (2 * l), t i.succ)) * (res (t 0) * c⁻¹) ^ 2 by
          rw [map_mul]; ring]
        rw [map_mul, quadraticChar_sq_one' (mul_ne_zero (res_ne_zero hπ (ht 0)) (inv_ne_zero hc)), mul_one]
      rw [heps, show 2 * l + 1 - 1 = 2 * l by omega, show (2 * l) / 2 = l by omega]
      rcases l with _ | l
      · simp [oCount, epsT, oOdd]
      · have hε := epsT_sq hπ (fun i : Fin (2 * (l + 1)) => ht i.succ)
        rw [oCount_odd_any (q R) (l + 1) _ 0, ← oCount_odd_step (q R) l _ hε]
    · -- n = 2l + 2 even
      have hev : Even (2 * l + 1 + 1) := ⟨l + 1, by ring⟩
      rw [(T1.1 hev).2]
      have heps : chiDisc Q = epsT t := by
        unfold chiDisc epsT
        rw [hgram, ← mul_assoc, hchi]
      rw [heps, show 2 * l + 1 + 1 - 1 = 2 * l + 1 by omega, show (2 * l + 1 + 1) / 2 - 1 = l by omega,
        oCount_odd_any (q R) l _ 0, ← oCount_even_step]

/-! ### Corollaries: $|O(Q \bmod \pi)|$ and the unimodular self-densities -/

/-- **$|O(Q \bmod \pi)| = o_n(q, \chi_D)$** for $\pi \nmid 2\det H_Q$, with $\chi_D$ = `chiDisc Q`
$= \chi((-1)^{\lfloor n/2\rfloor}\det(H_Q/2))$: the order of the orthogonal group of the nondegenerate quadratic space
$Q \bmod \pi$ over $\mathbb F_q$ ($q$ odd). This is the classical formula (Artin, *Geometric Algebra*, Ch. III;
Kitaoka 1993, §5.6 [unverified]) for $|O_n(\mathbb F_q)|$, here proved by column peeling. -/
@[kb "kitaoka1993" "§5.6 (|O_n(F_q)|) [unverified]"]
theorem card_orthMod_one_unimodular [Fintype 𝔽] [DecidableEq 𝔽] (Q : QuadForm R n) (hπ : Irreducible π)
    (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) :
    (Nat.card (orthMod Q π 1) : ℤ) = oCount (q R) n (chiDisc Q) := by
  rw [← repCountForm_self_eq_card_orthMod Q π hπ 0 1 (by simp) (by simpa using hdet) one_pos]
  obtain ⟨a, ha, ⟨U, hU, hUQ⟩, u, hu, hdu⟩ := exists_diag_of_unimodular Q π hπ h2 hdet
  have hiso : Siegel.IsometricGL Q (QuadForm.diag a) :=
    ⟨Matrix.nonsingInvUnit U hU, fun x => (hUQ x).symm⟩
  rw [repCountForm_congr_right Q hiso π 1]
  have hu0 : res u ≠ 0 := (hu.map res).ne_zero
  rw [repCountForm_diag_unimodular π hπ h2 n Q a hdet ha ⟨res u, hu0, by
    rw [hdu]; simp only [map_mul, map_pow]⟩]
  congr 1
  -- the characters agree
  have h2F : (2 : 𝔽) ≠ 0 := by
    have := res_ne_zero hπ h2; rwa [map_ofNat] at this
  have hres : res (∏ i, a i) = res u ^ 2 * resGramDet Q := by
    have h := congrArg res hdu
    simp only [map_mul, map_pow, map_ofNat] at h
    unfold resGramDet
    rw [mul_div_assoc', eq_div_iff (pow_ne_zero _ h2F), mul_comm, h]
  unfold epsT chiDisc
  rw [hres, show (-1 : 𝔽) ^ (n / 2) * (res u ^ 2 * resGramDet Q) =
    (-1) ^ (n / 2) * resGramDet Q * res u ^ 2 by ring, map_mul, quadraticChar_sq_one' hu0, mul_one]

theorem prod_sub_one_eq (x : ℝ) (hx : x ≠ 0) (m : ℕ) :
    ∏ i ∈ Finset.range m, (x ^ (2 * (i + 1)) - 1) =
      x ^ (m * (m + 1)) * ∏ i ∈ Finset.range m, (1 - (x ^ (2 * (i + 1)))⁻¹) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih,
      show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring, pow_add]
    have : x ^ (2 * (m + 1)) ≠ 0 := pow_ne_zero _ hx
    field_simp

/-- **Unimodular self-density, odd rank** ($\pi \nmid 2\det H_Q$, $n = 2m + 1$):
$$\beta_\pi(Q, Q) = 2\prod_{i=1}^{m}(1 - q^{-2i}),$$
so Siegel's $\alpha_\pi(Q, Q) = \beta_\pi/2 = \prod_{i=1}^m(1 - q^{-2i}) = \prod_{i=1}^m\zeta_\pi(2i)^{-1}$
(Kitaoka 1993, §5.6; Conway–Sloane 1988, Table 1 [unverified]). Index shift: the product runs over $i = 0, \dots, m-1$
with exponent $2(i + 1)$. -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_odd [Fintype 𝔽] [DecidableEq 𝔽] (m : ℕ) (Q : QuadForm R (2 * m + 1))
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) :
    localDensityForm Q Q π = 2 * ∏ i ∈ Finset.range m, (1 - ((q R : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [localDensityForm_self_unimodular Q π hπ (dvr_isUnit_of_not_dvd hπ hdet)]
  have h := card_orthMod_one_unimodular π Q hπ h2 hdet
  have h1 : ¬ Even (2 * m + 1) := by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m
  simp only [oCount, if_neg (by omega : 2 * m + 1 ≠ 0), if_neg h1, show (2 * m + 1) / 2 = m by omega,
    oOdd] at h
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hR : (Nat.card (orthMod Q π 1) : ℝ) = 2 * (q R : ℝ) ^ (m ^ 2) *
      ∏ i ∈ Finset.range m, ((q R : ℝ) ^ (2 * (i + 1)) - 1) := by exact_mod_cast h
  rw [hR, prod_sub_one_eq _ hq.ne', show (2 * m + 1) * (2 * m + 1 - 1) / 2 = m ^ 2 + m * (m + 1) by
    rw [Nat.add_sub_cancel, show (2 * m + 1) * (2 * m) = 2 * (m ^ 2 + m * (m + 1)) by ring,
      Nat.mul_div_cancel_left _ two_pos], pow_add]
  field_simp

/-- **Unimodular self-density, even rank** ($\pi \nmid 2\det H_Q$, $n = 2m$, $m \ge 1$):
$$\beta_\pi(Q, Q) = 2(1 - \chi_D q^{-m})\prod_{i=1}^{m-1}(1 - q^{-2i}),\qquad \chi_D = \chi((-1)^m\det(H_Q/2))$$
(`chiDisc Q`), so Siegel's $\alpha_\pi(Q, Q) = (1 - \chi_D q^{-m})\prod_{i=1}^{m-1}(1 - q^{-2i})$, the reciprocal of the
local factor of $L(m, \chi_D)\prod_{i=1}^{m-1}\zeta(2i)$ (Kitaoka 1993, §5.6; Conway–Sloane 1988, Table 1 [unverified]). -/
@[kb "kitaoka1993" "§5.6 [unverified]"]
theorem localDensityForm_self_even [Fintype 𝔽] [DecidableEq 𝔽] (m : ℕ) (hm : 1 ≤ m) (Q : QuadForm R (2 * m))
    (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (hdet : ¬ π ∣ Q.hessian.det) :
    localDensityForm Q Q π = 2 * (1 - (chiDisc Q : ℝ) * ((q R : ℝ) ^ m)⁻¹) *
      ∏ i ∈ Finset.range (m - 1), (1 - ((q R : ℝ) ^ (2 * (i + 1)))⁻¹) := by
  rw [localDensityForm_self_unimodular Q π hπ (dvr_isUnit_of_not_dvd hπ hdet)]
  have h := card_orthMod_one_unimodular π Q hπ h2 hdet
  have h1 : Even (2 * m) := even_two_mul m
  simp only [oCount, if_neg (by omega : 2 * m ≠ 0), if_pos h1, show 2 * m / 2 = m by omega, oEven] at h
  have hq : (0 : ℝ) < q R := by exact_mod_cast q_pos
  have hR : (Nat.card (orthMod Q π 1) : ℝ) = 2 * (q R : ℝ) ^ (m * (m - 1)) * ((q R : ℝ) ^ m - chiDisc Q) *
      ∏ i ∈ Finset.range (m - 1), ((q R : ℝ) ^ (2 * (i + 1)) - 1) := by exact_mod_cast h
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  rw [hR, Nat.add_sub_cancel, prod_sub_one_eq _ hq.ne',
    show 2 * (l + 1) * (2 * (l + 1) - 1) / 2 = (l + 1) * l + (l + 1) + l * (l + 1) by
      rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega,
        show 2 * (l + 1) * (2 * l + 1) = 2 * ((l + 1) * l + (l + 1) + l * (l + 1)) by ring,
        Nat.mul_div_cancel_left _ two_pos], pow_add, pow_add]
  have : (q R : ℝ) ^ (l + 1) ≠ 0 := pow_ne_zero _ hq.ne'
  field_simp
  ring

end QuadFormsKB.LocalDensity.DVR
