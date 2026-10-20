/-
# $\mathrm{SL}_2$ over a field: Bruhat cells and a presentation

**Layer:** pure algebra (any field $k$, any monoid $M$).

**Conventions** (Kudla, *Notes on the local theta correspondence*, §I.1; Weil 1964, §1 and §14):
$$n(b) = \begin{pmatrix}1 & b\\ 0 & 1\end{pmatrix},\qquad
  m(a) = \begin{pmatrix}a & 0\\ 0 & a^{-1}\end{pmatrix},\qquad
  w = \begin{pmatrix}0 & 1\\ -1 & 0\end{pmatrix}$$
(`nMat`, `mMat`, `wMat`). The **Bruhat decomposition** $\mathrm{SL}_2(k) = B \sqcup N w B$ in explicit form: for
$g = \begin{pmatrix}a & b\\ c & d\end{pmatrix}$,
$$g = m(a)\,n(b/a)\quad (c = 0), \qquad g = n(a/c)\,m(-c^{-1})\,w\,n(d/c)\quad (c \ne 0)$$
(`eq_cell_of_c_eq_zero`, `eq_cell_of_c_ne_zero`).

**The presentation** (`cellHom`). Let $N : k \to M$, $A : k^\times \to M$ and $W \in M$ satisfy (`SL2Relations`)
* (R1) $N(0) = 1$, $N(b + b') = N(b)N(b')$;
* (R2) $A(1) = 1$, $A(tt') = A(t)A(t')$;
* (R3) $A(t)N(b) = N(t^2b)A(t)$;
* (R4) $WA(t) = A(t^{-1})W$;
* (R5) $W^2 = A(-1)$;
* (R6) $WN(b)W = N(-b^{-1})\,A(-b^{-1})\,W\,N(-b^{-1})$ for $b \ne 0$ (the matrix identity
  $w\,n(b)\,w = n(-b^{-1})\,m(-b^{-1})\,w\,n(-b^{-1})$, `wMat_nMat_wMat`).

Then the **cell formula**
$$\rho(g) = A(a)\,N(b/a)\quad (c = 0),\qquad \rho(g) = N(a/c)\,A(-c^{-1})\,W\,N(d/c)\quad (c \ne 0)$$
(`cellRep`) is a monoid homomorphism $\mathrm{SL}_2(k) \to M$ with $\rho(n(b)) = N(b)$, $\rho(m(a)) = A(a)$,
$\rho(w) = W$. *Proof:* $\rho(gn(t)) = \rho(g)N(t)$, $\rho(gm(t)) = \rho(g)A(t)$, $\rho(gw) = \rho(g)W$ for every $g$
(a case check on the cells, using (R1)–(R6) once each), and every $h$ is a cell product. No cocycle appears. The
relations are necessary as well, since they hold in $\mathrm{SL}_2(k)$ (`nMat_add`, `mMat_mul`, `mMat_nMat`,
`wMat_mMat`, `wMat_mul_wMat`, `wMat_nMat_wMat`).

`SL2.induction_on`: a property that holds for $1$ and is stable under right multiplication by every $n(b)$, $m(a)$
and $w$ holds on all of $\mathrm{SL}_2(k)$.

Sources: Kudla, *Notes on the local theta correspondence* (1996), §I.1 (generators and the Bruhat decomposition)
[unverified]; Bump, *Automorphic Forms and Representations* (1997), Prop. 4.8.x (the Weil representation
defined on generators) [unverified]; Lang, *SL₂(ℝ)*, Ch. XI §2 [unverified].
-/
import Mathlib
import QuadFormsKB.Citation

open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

variable {k : Type*} [Field k]

/-! ### The generators -/

/-- **The unipotent element** $n(b) = \begin{pmatrix}1 & b\\ 0 & 1\end{pmatrix} \in \mathrm{SL}_2(k)$. -/
@[kb "kudla1996" "§I.1 (the elements $n(b)$, $m(a)$, $w$) [unverified]"]
def nMat (b : k) : SL(2, k) := ⟨!![1, b; 0, 1], by simp [det_fin_two]⟩

/-- **The diagonal element** $m(a) = \begin{pmatrix}a & 0\\ 0 & a^{-1}\end{pmatrix} \in \mathrm{SL}_2(k)$, $a \in k^\times$. -/
@[kb "kudla1996" "§I.1 (the elements $n(b)$, $m(a)$, $w$) [unverified]"]
def mMat (a : kˣ) : SL(2, k) := ⟨!![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)], by simp [det_fin_two]⟩

/-- **The Weyl element** $w = \begin{pmatrix}0 & 1\\ -1 & 0\end{pmatrix} \in \mathrm{SL}_2(k)$. -/
@[kb "kudla1996" "§I.1 (the elements $n(b)$, $m(a)$, $w$) [unverified]"]
def wMat : SL(2, k) := ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

@[simp] lemma nMat_coe (b : k) : (nMat b : Matrix (Fin 2) (Fin 2) k) = !![1, b; 0, 1] := rfl
@[simp] lemma mMat_coe (a : kˣ) :
    (mMat a : Matrix (Fin 2) (Fin 2) k) = !![(a : k), 0; 0, ((a⁻¹ : kˣ) : k)] := rfl
@[simp] lemma wMat_coe : ((wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl

lemma det_eq (g : SL(2, k)) :
    (g : Matrix (Fin 2) (Fin 2) k) 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2; rw [det_fin_two] at this; exact this

lemma a_ne_zero_of_c_eq_zero {g : SL(2, k)} (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k) 0 0 ≠ 0 := by
  intro ha; have := det_eq g; rw [ha, hc] at this; simp at this

lemma d_ne_zero_of_c_eq_zero {g : SL(2, k)} (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) k) 1 1 ≠ 0 := by
  intro hd; have := det_eq g; rw [hd, hc] at this; simp at this

/-! ### Relations in $\mathrm{SL}_2(k)$ -/

lemma nMat_add (b b' : k) : nMat (b + b') = nMat b * nMat b' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma mMat_mul (t t' : kˣ) : mMat (t * t') = mMat t * mMat t' := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma mMat_nMat (t : kˣ) (b : k) : mMat t * nMat b = nMat ((t : k) ^ 2 * b) * mMat t := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

lemma wMat_mMat (t : kˣ) : wMat * mMat t = mMat t⁻¹ * wMat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma wMat_mul_wMat : wMat * wMat = (mMat (-1) : SL(2, k)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The Bruhat relation:** $w\,n(b)\,w = n(-b^{-1})\,m(-b^{-1})\,w\,n(-b^{-1})$ for $b \ne 0$. -/
lemma wMat_nMat_wMat {b : k} (hb : b ≠ 0) :
    wMat * nMat b * wMat =
      nMat (-b⁻¹) * mMat (Units.mk0 (-b⁻¹) (by simpa using hb)) * wMat * nMat (-b⁻¹) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-! ### The Bruhat cells -/

lemma unit_ne_zero_aux {x : k} (hx : x ≠ 0) : -x⁻¹ ≠ 0 := by simpa using hx

/-- $g = m(a)\,n(b/a)$ when $c = 0$. -/
lemma eq_cell_of_c_eq_zero (g : SL(2, k)) (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    g = mMat (Units.mk0 _ (a_ne_zero_of_c_eq_zero hc)) *
      nMat ((g : Matrix (Fin 2) (Fin 2) k) 0 1 / g 0 0) := by
  have ha := a_ne_zero_of_c_eq_zero hc
  have hdet := det_eq g
  rw [hc, mul_zero, sub_zero] at hdet
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
  · field_simp
  · field_simp; linear_combination hdet

/-- $g = n(a/c)\,m(-c^{-1})\,w\,n(d/c)$ when $c \ne 0$. -/
lemma eq_cell_of_c_ne_zero (g : SL(2, k)) (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    g = nMat ((g : Matrix (Fin 2) (Fin 2) k) 0 0 / g 1 0) * mMat (Units.mk0 _ (unit_ne_zero_aux hc)) *
      wMat * nMat ((g : Matrix (Fin 2) (Fin 2) k) 1 1 / g 1 0) := by
  have hdet := det_eq g
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> first | ring1 | linear_combination hdet | linear_combination -hdet

/-! ### The cell formula and the presentation -/

variable {M : Type*} [Monoid M] (N : k → M) (A : kˣ → M) (W : M)

/-- **The relations of the presentation** of $\mathrm{SL}_2(k)$ on the generators $n(b)$, $m(t)$, $w$, for maps
$N : k \to M$, $A : k^\times \to M$ and $W \in M$ (images of $n$, $m$, $w$):

* `N_zero`, `N_add`: $N(0) = 1$, $N(b+b') = N(b)N(b')$;
* `A_one`, `A_mul`: $A(1) = 1$, $A(tt') = A(t)A(t')$;
* `A_N`: $A(t)N(b) = N(t^2b)A(t)$;
* `W_A`: $WA(t) = A(t^{-1})W$;
* `W_W`: $W^2 = A(-1)$;
* `W_N_W`: $WN(b)W = N(-b^{-1})A(-b^{-1})WN(-b^{-1})$ for $b \ne 0$. -/
@[kb "kudla1996" "§I.1 (relations among $n(b)$, $m(a)$, $w$) [unverified]"]
structure SL2Relations : Prop where
  N_zero : N 0 = 1
  N_add : ∀ b b' : k, N (b + b') = N b * N b'
  A_one : A 1 = 1
  A_mul : ∀ t t' : kˣ, A (t * t') = A t * A t'
  A_N : ∀ (t : kˣ) (b : k), A t * N b = N ((t : k) ^ 2 * b) * A t
  W_A : ∀ t : kˣ, W * A t = A t⁻¹ * W
  W_W : W * W = A (-1)
  W_N_W : ∀ (b : k) (hb : b ≠ 0), W * N b * W =
    N (-b⁻¹) * A (Units.mk0 (-b⁻¹) (unit_ne_zero_aux hb)) * W * N (-b⁻¹)

open Classical in
/-- $A$ extended to $k$ by $A(0) := 1$ (a junk value, never used by `cellRep`): avoids dependent proofs. -/
def Aof (x : k) : M := if h : x = 0 then 1 else A (Units.mk0 x h)

open Classical in
/-- **The Bruhat-cell formula.** For $g = \begin{pmatrix}a & b\\ c & d\end{pmatrix} \in \mathrm{SL}_2(k)$:
$$\rho(g) = A(a)\,N(b/a)\ \ (c = 0),\qquad \rho(g) = N(a/c)\,A(-c^{-1})\,W\,N(d/c)\ \ (c \ne 0).$$
Under `SL2Relations` this is a monoid homomorphism (`cellHom`). -/
@[kb "kudla1996" "§I.1 (Bruhat decomposition) [unverified]"]
def cellRep (g : SL(2, k)) : M :=
  if (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 then
    Aof A ((g : Matrix (Fin 2) (Fin 2) k) 0 0) * N ((g : Matrix (Fin 2) (Fin 2) k) 0 1 / g 0 0)
  else
    N ((g : Matrix (Fin 2) (Fin 2) k) 0 0 / g 1 0) * Aof A (-((g : Matrix (Fin 2) (Fin 2) k) 1 0)⁻¹) * W *
      N ((g : Matrix (Fin 2) (Fin 2) k) 1 1 / g 1 0)

variable {N A W}

lemma Aof_coe (t : kˣ) : Aof A (t : k) = A t := by
  rw [Aof, dif_neg t.ne_zero]; congr 1; ext; simp

lemma Aof_of_ne {x : k} (hx : x ≠ 0) : Aof A x = A (Units.mk0 x hx) := by
  rw [Aof, dif_neg hx]

lemma cellRep_of_c_eq_zero {g : SL(2, k)} (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    cellRep N A W g =
      Aof A ((g : Matrix (Fin 2) (Fin 2) k) 0 0) * N ((g : Matrix (Fin 2) (Fin 2) k) 0 1 / g 0 0) := by
  rw [cellRep, if_pos hc]

lemma cellRep_of_c_ne_zero {g : SL(2, k)} (hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0) :
    cellRep N A W g =
      N ((g : Matrix (Fin 2) (Fin 2) k) 0 0 / g 1 0) * Aof A (-((g : Matrix (Fin 2) (Fin 2) k) 1 0)⁻¹) * W *
        N ((g : Matrix (Fin 2) (Fin 2) k) 1 1 / g 1 0) := by
  rw [cellRep, if_neg hc]

section Relations

variable (hR : SL2Relations N A W)
include hR

lemma Aof_mul {x y : k} (hx : x ≠ 0) (hy : y ≠ 0) : Aof A (x * y) = Aof A x * Aof A y := by
  rw [Aof_of_ne hx, Aof_of_ne hy, Aof_of_ne (mul_ne_zero hx hy), ← hR.A_mul]; congr 1; ext; simp

lemma Aof_N {x : k} (hx : x ≠ 0) (b : k) : Aof A x * N b = N (x ^ 2 * b) * Aof A x := by
  rw [Aof_of_ne hx, hR.A_N]; rfl

lemma N_Aof {x : k} (hx : x ≠ 0) (b : k) : N b * Aof A x = Aof A x * N ((x ^ 2)⁻¹ * b) := by
  rw [Aof_N hR hx]; congr 2; field_simp

lemma W_Aof {x : k} (hx : x ≠ 0) : W * Aof A x = Aof A x⁻¹ * W := by
  rw [Aof_of_ne hx, hR.W_A, Aof_of_ne (inv_ne_zero hx)]; congr 2; ext; simp

lemma W_W' : W * W = Aof A (-1) := by
  rw [hR.W_W, Aof_of_ne (by norm_num : (-1 : k) ≠ 0)]; congr 1; ext; simp

lemma W_N_W' {b : k} (hb : b ≠ 0) : W * N b * W = N (-b⁻¹) * Aof A (-b⁻¹) * W * N (-b⁻¹) := by
  rw [hR.W_N_W b hb, Aof_of_ne (unit_ne_zero_aux hb)]

lemma cellRep_mul_nMat (g : SL(2, k)) (t : k) :
    cellRep N A W (g * nMat t) = cellRep N A W g * N t := by
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · have ha := a_ne_zero_of_c_eq_zero hc
    have hc' : ((g * nMat t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
    rw [cellRep_of_c_eq_zero hc', cellRep_of_c_eq_zero hc, mul_assoc, ← hR.N_add]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, nMat_coe]
    simp [hc]
    congr 1; field_simp; ring
  · have hc' : ((g * nMat t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using hc
    rw [cellRep_of_c_ne_zero hc', cellRep_of_c_ne_zero hc, mul_assoc _ _ (N t), ← hR.N_add]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, nMat_coe]
    simp
    congr 1; field_simp; ring

lemma cellRep_mul_mMat (g : SL(2, k)) (t : kˣ) :
    cellRep N A W (g * mMat t) = cellRep N A W g * A t := by
  have ht : (t : k) ≠ 0 := t.ne_zero
  rw [show A t = Aof A (t : k) from (Aof_coe t).symm]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · have ha := a_ne_zero_of_c_eq_zero hc
    have hc' : ((g * mMat t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc]
    rw [cellRep_of_c_eq_zero hc', cellRep_of_c_eq_zero hc, mul_assoc, N_Aof hR ht, ← mul_assoc,
      ← Aof_mul hR ha ht]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mMat_coe]
    simp [hc]
    congr 1; field_simp
  · have hc' : ((g * mMat t : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] using
        mul_ne_zero hc ht
    rw [cellRep_of_c_ne_zero hc', cellRep_of_c_ne_zero hc, mul_assoc _ _ (Aof A _), N_Aof hR ht]
    simp only [mul_assoc]
    rw [← mul_assoc W (Aof A _), W_Aof hR ht]
    simp only [← mul_assoc]
    rw [mul_assoc (N _) (Aof A _) (Aof A _), ← Aof_mul hR (unit_ne_zero_aux hc) (inv_ne_zero ht)]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mMat_coe]
    simp
    congr 2 <;> first | (congr 1; ring1) | (congr 1; field_simp; done) | (congr 1; field_simp; ring1) |
      (field_simp; done) | (field_simp; ring1)

lemma cellRep_mul_wMat (g : SL(2, k)) : cellRep N A W (g * wMat) = cellRep N A W g * W := by
  have hdet := det_eq g
  have h00 : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 0 = -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 1 = g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = -g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 1 = g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · -- `g = m(a) n(x)`, `g w` is in the big cell
    have hd := d_ne_zero_of_c_eq_zero hc
    have ha := a_ne_zero_of_c_eq_zero hc
    have hc' : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
      rw [h10]; exact neg_ne_zero.mpr hd
    rw [hc, mul_zero, sub_zero] at hdet
    rw [cellRep_of_c_ne_zero hc', cellRep_of_c_eq_zero hc, h00, h10, h11, hc, zero_div, hR.N_zero,
      mul_one, Aof_N hR ha]
    have hinv : -(-(g : Matrix (Fin 2) (Fin 2) k) 1 1)⁻¹ = g 0 0 := by
      field_simp; linear_combination -hdet
    rw [hinv]
    congr 3
    field_simp; linear_combination -(g 0 1) * hdet
  · by_cases hd : (g : Matrix (Fin 2) (Fin 2) k) 1 1 = 0
    · -- `g w` is in the Borel
      have hc' : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by rw [h10, hd, neg_zero]
      rw [hd, mul_zero, zero_sub] at hdet
      have hb : (g : Matrix (Fin 2) (Fin 2) k) 0 1 ≠ 0 := by
        intro h; rw [h, zero_mul, neg_zero] at hdet; exact zero_ne_one hdet
      rw [cellRep_of_c_eq_zero hc', cellRep_of_c_ne_zero hc, hd, zero_div, hR.N_zero, mul_one,
        mul_assoc, W_W' hR, mul_assoc, ← Aof_mul hR (unit_ne_zero_aux hc) (by norm_num), h00, h01,
        Aof_N hR (neg_ne_zero.mpr hb)]
      have hx : -((g : Matrix (Fin 2) (Fin 2) k) 1 0)⁻¹ * -1 = -g 0 1 := by
        field_simp; linear_combination -hdet
      rw [hx]
      congr 2
      field_simp
      linear_combination (g 0 0) * hdet
    · -- both in the big cell: use (R6)
      have hc' : ((g * wMat : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by
        rw [h10]; exact neg_ne_zero.mpr hd
      have hy : (g : Matrix (Fin 2) (Fin 2) k) 1 1 / g 1 0 ≠ 0 := div_ne_zero hd hc
      rw [cellRep_of_c_ne_zero hc', cellRep_of_c_ne_zero hc, h00, h10, h11]
      simp only [mul_assoc]
      rw [← mul_assoc W (N _) W, W_N_W' hR hy]
      simp only [← mul_assoc]
      rw [mul_assoc _ (Aof A _) (N _), Aof_N hR (unit_ne_zero_aux hc), ← mul_assoc, ← hR.N_add,
        mul_assoc _ (Aof A _) (Aof A _), ← Aof_mul hR (unit_ne_zero_aux hc) (unit_ne_zero_aux hy)]
      congr 3
      · congr 1; field_simp; linear_combination (-1 : k) * hdet
      · congr 1; field_simp
      · field_simp

lemma cellRep_one : cellRep N A W (1 : SL(2, k)) = 1 := by
  have hc : ((1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by simp
  rw [cellRep_of_c_eq_zero hc]
  have h1 : ((1 : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 0 = ((1 : kˣ) : k) := by simp
  rw [h1, Aof_coe, hR.A_one, one_mul]
  simpa using hR.N_zero

lemma cellRep_mul (g h : SL(2, k)) : cellRep N A W (g * h) = cellRep N A W g * cellRep N A W h := by
  by_cases hc : (h : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · conv_lhs => rw [eq_cell_of_c_eq_zero h hc, ← mul_assoc, cellRep_mul_nMat hR, cellRep_mul_mMat hR]
    rw [cellRep_of_c_eq_zero hc, mul_assoc, Aof_of_ne (a_ne_zero_of_c_eq_zero hc)]
  · conv_lhs => rw [eq_cell_of_c_ne_zero h hc]
    simp only [← mul_assoc]
    rw [cellRep_mul_nMat hR, cellRep_mul_wMat hR, cellRep_mul_mMat hR, cellRep_mul_nMat hR,
      cellRep_of_c_ne_zero hc, Aof_of_ne (unit_ne_zero_aux hc)]
    simp only [mul_assoc]

/-- **The presentation of $\mathrm{SL}_2(k)$:** if $N$, $A$, $W$ satisfy (R1)–(R6) (`SL2Relations`), the cell formula
`cellRep` is a monoid homomorphism $\rho : \mathrm{SL}_2(k) \to M$ (`cellHom_nMat`, `cellHom_mMat`, `cellHom_wMat`:
$\rho(n(b)) = N(b)$, $\rho(m(a)) = A(a)$, $\rho(w) = W$). -/
@[kb "kudla1996" "§I.1 (generators and relations for $\\mathrm{SL}_2$) [unverified]"]
def cellHom : SL(2, k) →* M where
  toFun := cellRep N A W
  map_one' := cellRep_one hR
  map_mul' := cellRep_mul hR

lemma cellHom_apply (g : SL(2, k)) : cellHom hR g = cellRep N A W g := rfl

@[simp] lemma cellHom_nMat (b : k) : cellHom hR (nMat b) = N b := by
  have := cellRep_mul_nMat hR 1 b
  rw [one_mul, cellRep_one hR, one_mul] at this
  exact this

@[simp] lemma cellHom_mMat (t : kˣ) : cellHom hR (mMat t) = A t := by
  have := cellRep_mul_mMat hR 1 t
  rw [one_mul, cellRep_one hR, one_mul] at this
  exact this

@[simp] lemma cellHom_wMat : cellHom hR wMat = W := by
  have := cellRep_mul_wMat hR 1
  rw [one_mul, cellRep_one hR, one_mul] at this
  exact this

end Relations

/-! ### Induction over generators -/

/-- **Generation of $\mathrm{SL}_2(k)$:** a predicate that holds at $1$ and is stable under right multiplication by
every $n(b)$, $m(a)$ and $w$ holds on all of $\mathrm{SL}_2(k)$ (from the Bruhat cells). -/
theorem SL2.induction_on {P : SL(2, k) → Prop} (h1 : P 1) (hn : ∀ g b, P g → P (g * nMat b))
    (hm : ∀ g t, P g → P (g * mMat t)) (hw : ∀ g, P g → P (g * wMat)) (g : SL(2, k)) : P g := by
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · rw [eq_cell_of_c_eq_zero g hc]
    simpa using hn _ _ (hm _ _ h1)
  · rw [eq_cell_of_c_ne_zero g hc]
    simpa [mul_assoc] using hn _ _ (hw _ (hm _ _ (hn _ _ h1)))

end QuadFormsKB.WeilRep
