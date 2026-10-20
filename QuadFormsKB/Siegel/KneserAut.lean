/-
# Kneser neighbours, part 9: certified automorphism counts

**Layer:** positive definite integral forms (`IntQF n`, `IntQF.PosDef`).

The mass criterion needs $|\mathrm{Aut}(Q_i)|$ for each class found. This file proves a **finite certificate** for
$|\mathrm{Aut}(Q)|$ ($\mathrm{Aut}(Q) \le \mathrm{GL}_n(\mathbb{Z})$, improper automorphisms included):

- `sq_le_of_adj` (a **box bound**): if $HC = D\cdot 1$ with $D > 0$ (e.g. $C = \operatorname{adj} H$, $D = \det H$) and $Q$ is positive
  definite, then $D\,x_i^2 \le 2C_{ii}\,Q(\vec{x})$ for all $\vec{x} \in \mathbb{Z}^n$ (Cauchy–Schwarz for $B$, applied to $\vec{x}$ and the
  $i$-th column of $C$). So the vectors of a given norm lie in an explicit box $[-B, B]^n$ (`boxList`, `mem_boxList`).
- `card_aut_eq_of_cert`: if a list `auts` of integer matrices is duplicate-free, consists of solutions of
  $M^{\mathsf T}HM = H$, and contains every such solution whose columns lie in the candidate lists (vectors in the box with
  $Q(\vec{m}_j) = Q(\vec{e}_j)$; a finite, decidable check over `colTuples`), then $|\mathrm{Aut}(Q)| = $ `auts.length`.

All hypotheses are checked by `decide` in the examples (`Siegel/KneserExample.lean`).
-/
import QuadFormsKB.Siegel.KneserClosure

open Matrix

namespace QuadFormsKB.Siegel.Kneser

open QuadFormsKB.Siegel

variable {n : ℕ}

/-! ### The box bound -/

/-- **The box bound.** For a positive definite integral $Q$ with Hessian $H$, and $C$, $D > 0$ with $HC = D\cdot 1$:
$$D\,x_i^2 \le 2\,C_{ii}\,Q(\vec{x}) \qquad (\vec{x} \in \mathbb{Z}^n).$$
*Proof:* with $\vec{y} = C\vec{e}_i$ one has $H\vec{y} = D\vec{e}_i$, $B(\vec{x}, \vec{y}) = Dx_i$, $2Q(\vec{y}) = DC_{ii} > 0$; then
$0 \le Q(2Q(\vec{y})\vec{x} - B(\vec{x}, \vec{y})\vec{y}) = Q(\vec{y})(4Q(\vec{y})Q(\vec{x}) - B(\vec{x}, \vec{y})^2)$. -/
theorem sq_le_of_adj {Q : IntQF n} (hQ : Q.PosDef) {C : Matrix (Fin n) (Fin n) ℤ} {D : ℤ}
    (hC : Q.hessian * C = D • (1 : Matrix (Fin n) (Fin n) ℤ)) (hD : 0 < D) (x : Fin n → ℤ) (i : Fin n) :
    D * x i ^ 2 ≤ 2 * C i i * Q.eval x := by
  set y : Fin n → ℤ := fun r => C r i
  have hHy : Q.hessian *ᵥ y = D • Pi.single i 1 := by
    ext r
    have := congrFun (congrFun hC r) i
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at this
    simp only [mulVec, dotProduct, y, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    rw [this]
  have hB : bZ Q x y = D * x i := by
    rw [bZ, hHy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
  have hq : 2 * Q.eval y = D * C i i := by
    rw [← bZ_self, bZ, hHy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one]
  have hy0 : y ≠ 0 := by
    intro h0
    have := congrFun hHy i
    rw [h0, mulVec_zero] at this
    simp at this; omega
  have hqpos : 0 < Q.eval y := hQ y hy0
  have hnn : 0 ≤ Q.eval ((2 * Q.eval y) • x + (-bZ Q x y) • y) := by
    by_cases hz : (2 * Q.eval y) • x + (-bZ Q x y) • y = 0
    · rw [hz]; simp [QuadForm.evalIn]
    · exact (hQ _ hz).le
  have hexp : Q.eval ((2 * Q.eval y) • x + (-bZ Q x y) • y) =
      Q.eval y * (4 * Q.eval y * Q.eval x - bZ Q x y ^ 2) := by
    rw [eval_add_smulZ, eval_smul_gen Q, bZ_smul_left]
    ring
  rw [hexp] at hnn
  have h4 : bZ Q x y ^ 2 ≤ 4 * Q.eval y * Q.eval x := by
    have := (mul_nonneg_iff_of_pos_left hqpos).mp hnn
    linarith
  rw [hB] at h4
  have h5 : D * (D * x i ^ 2) ≤ D * (2 * C i i * Q.eval x) := by nlinarith
  exact le_of_mul_le_mul_left h5 hD

/-- **Vectors in the box $[-B, B]^n$** (as a list; complete by `mem_boxList`). -/
def boxList (B : ℕ) : (n : ℕ) → List (Fin n → ℤ)
  | 0 => [Fin.elim0]
  | n + 1 => (boxList B n).flatMap fun v => (List.range (2 * B + 1)).map fun a : ℕ => Fin.cons (Int.ofNat a - B) v

theorem mem_boxList {B : ℕ} : ∀ {n : ℕ} (x : Fin n → ℤ), (∀ i, |x i| ≤ B) → x ∈ boxList B n
  | 0, x, _ => by simp [boxList]; exact funext fun i => i.elim0
  | n + 1, x, h => by
    simp only [boxList, List.mem_flatMap, List.mem_map]
    refine ⟨Fin.tail x, mem_boxList _ fun i => h i.succ, (x 0 + B).toNat, ?_, ?_⟩
    · rw [List.mem_range]; have := abs_le.mp (h 0); omega
    · have := abs_le.mp (h 0)
      rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega), add_sub_cancel_right]
      exact Fin.cons_self_tail x

/-- From the box bound: if $Q(\vec{x}) = m$ and $2C_{ii}m < (B+1)^2D$ for all $i$, then $\vec{x} \in [-B, B]^n$. -/
theorem mem_boxList_of_eval {Q : IntQF n} (hQ : Q.PosDef) {C : Matrix (Fin n) (Fin n) ℤ} {D : ℤ}
    (hC : Q.hessian * C = D • (1 : Matrix (Fin n) (Fin n) ℤ)) (hD : 0 < D) {B : ℕ} {m : ℤ}
    (hB : ∀ i, 2 * C i i * m < ((B : ℤ) + 1) ^ 2 * D) {x : Fin n → ℤ} (hx : Q.eval x = m) : x ∈ boxList B n := by
  refine mem_boxList x fun i => ?_
  have h1 := sq_le_of_adj hQ hC hD x i
  rw [hx] at h1
  have h2 := hB i
  by_contra hc
  push Not at hc
  have h3 : ((B : ℤ) + 1) ^ 2 ≤ x i ^ 2 := by
    have : (B : ℤ) + 1 ≤ |x i| := by omega
    calc ((B : ℤ) + 1) ^ 2 ≤ |x i| ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = x i ^ 2 := sq_abs _
  nlinarith

/-! ### Tuples of columns -/

/-- **All tuples** $(c_0, \dots, c_{n-1})$ with $c_j \in S_j$. -/
def colTuples {α : Type*} : {n : ℕ} → (Fin n → List α) → List (Fin n → α)
  | 0, _ => [Fin.elim0]
  | _ + 1, S => (S 0).flatMap fun a => (colTuples fun j => S j.succ).map (Fin.cons a)

theorem mem_colTuples {α : Type*} : ∀ {n : ℕ} (S : Fin n → List α) (f : Fin n → α), (∀ j, f j ∈ S j) →
    f ∈ colTuples S
  | 0, _, f, _ => by simp [colTuples]; exact funext fun i => i.elim0
  | _ + 1, S, f, h => by
    simp only [colTuples, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, h 0, Fin.tail f, mem_colTuples _ _ fun j => h j.succ, Fin.cons_self_tail f⟩

/-- **The candidate columns** for $\mathrm{Aut}(Q)$: vectors of the box with $Q(\vec{m}) = Q(\vec{e}_j)$. -/
def autCands (Q : QuadForm ℤ n) (B : ℕ) (j : Fin n) : List (Fin n → ℤ) :=
  (boxList B n).filter fun x => Q.eval x = Q.eval (Pi.single j 1)

/-! ### Counting automorphisms -/

theorem eval_col_of_conj {Q : QuadForm ℤ n} {M : Matrix (Fin n) (Fin n) ℤ}
    (h : Mᵀ * Q.hessian * M = Q.hessian) (j : Fin n) :
    Q.eval (fun i => M i j) = Q.eval (Pi.single j 1) := by
  have h1 := (eval_mulVec_eq_iff_hessian Q Q M).mpr h (Pi.single j 1)
  rwa [mulVec_single_one] at h1

/-- **A certified automorphism count.** Let $Q$ be positive definite with $HC = D\cdot 1$, $D > 0$, and $B$ a box size with
$2C_{ii}\,Q(\vec{e}_j) < (B+1)^2D$ for all $i, j$. If `auts` is a duplicate-free list of solutions of $M^{\mathsf T}HM = H$ that
contains every solution whose columns are candidates (`autCands`), then $|\mathrm{Aut}(Q)| = $ `auts.length`. -/
@[kb "scharlauhemkemeier1998" "§2 (automorphism groups) [unverified]"]
theorem card_aut_eq_of_cert {Q : IntQF n} (hQ : Q.PosDef) {C : Matrix (Fin n) (Fin n) ℤ} {D : ℤ}
    (hC : Q.hessian * C = D • (1 : Matrix (Fin n) (Fin n) ℤ)) (hD : 0 < D) {B : ℕ}
    (hB : ∀ i j, 2 * C i i * Q.eval (Pi.single j 1) < ((B : ℤ) + 1) ^ 2 * D)
    (auts : List (Matrix (Fin n) (Fin n) ℤ)) (hnodup : auts.Nodup)
    (hsound : ∀ M ∈ auts, Mᵀ * Q.hessian * M = Q.hessian)
    (hcomplete : ∀ cols ∈ colTuples (autCands Q B),
      (Matrix.of fun i j => cols j i)ᵀ * Q.hessian * (Matrix.of fun i j => cols j i) = Q.hessian →
        (Matrix.of fun i j => cols j i) ∈ auts) :
    Nat.card (Aut Q) = auts.length := by
  classical
  have hdetH : Q.hessian.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hC
    rw [det_mul, h0, zero_mul, det_smul, det_one, mul_one] at e
    exact pow_ne_zero _ hD.ne' e.symm
  have hunit : ∀ M ∈ auts, IsUnit M.det := by
    intro M hM
    have e := congrArg Matrix.det (hsound M hM)
    rw [det_mul, det_mul, det_transpose] at e
    have : M.det * M.det = 1 := by
      have : M.det * M.det * Q.hessian.det = 1 * Q.hessian.det := by linear_combination e
      exact mul_right_cancel₀ hdetH this
    exact isUnit_iff_exists_inv.mpr ⟨_, this⟩
  let e : Aut Q ≃ {M // M ∈ auts.toFinset} :=
    { toFun := fun g => ⟨g.1.val, by
        have hg : g.1.valᵀ * Q.hessian * g.1.val = Q.hessian := (eval_mulVec_eq_iff_hessian Q Q _).mp g.2
        have hcols : (fun j i => g.1.val i j) ∈ colTuples (autCands Q B) := by
          refine mem_colTuples _ _ fun j => ?_
          simp only [autCands, List.mem_filter, decide_eq_true_eq]
          exact ⟨mem_boxList_of_eval hQ hC hD (fun i => hB i j) (eval_col_of_conj hg j),
            eval_col_of_conj hg j⟩
        have em : (Matrix.of fun i j => (fun j i => g.1.val i j) j i) = g.1.val := by ext i j; rfl
        have := hcomplete _ hcols (by rw [em]; exact hg)
        rw [em] at this
        exact List.mem_toFinset.mpr this⟩
      invFun := fun M => ⟨M.1.nonsingInvUnit (hunit M.1 (List.mem_toFinset.mp M.2)),
        (eval_mulVec_eq_iff_hessian Q Q _).mpr (hsound M.1 (List.mem_toFinset.mp M.2))⟩
      left_inv := fun g => by ext1; ext1; rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodup]

end QuadFormsKB.Siegel.Kneser
