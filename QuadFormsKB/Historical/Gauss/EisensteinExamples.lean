import QuadFormsKB.Historical.Gauss.EisensteinTernary
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination

/-!
# Eisenstein's worked examples for $\delta$, proved (Eisenstein 1851, § 6, pp. 164-165)

. For each of the eight worked examples of `eisensteinDelta_examples`, the number
`automorphCount` of proper automorphs ($g \in \mathrm{SL}_3(\mathbb{Z})$ with $Q(gv) = Q(v)$) is computed and shown
to equal `eisensteinDelta`, the table value (24, 24, 24, 12, 8, 4, 2, 1).

Method: $g$ is an automorph iff its columns $c_j$ satisfy $Q(c_j) = Q(e_j)$ and $B_Q(c_i, c_j) = B_Q(e_i, e_j)$
(`automorph_iff`). For a positive definite $Q$ a column of value $\le N$ lies in a small cube $[-B, B]^3$
(proved per example by `nlinarith`), so the automorphs correspond to an explicit finite set of column triples
(`eisAutoSet`, `automorphCount_eq`), whose cardinality is computed by `decide +kernel` (no `native_decide`).
Unconditional: no inputs or hypotheses beyond the definitions.
-/

namespace QuadFormsKB.Historical.Gauss

open Matrix

/-- The polynomial $a x^2 + a' y^2 + a'' z^2 + 2b\,yz + 2b'\,xz + 2b''\,xy$. -/
def eisQf (a a' a'' b b' b'' x y z : ℤ) : ℤ :=
  a * x ^ 2 + a' * y ^ 2 + a'' * z ^ 2 + 2 * b * y * z + 2 * b' * x * z + 2 * b'' * x * y

/-- Bilinear form attached to `eisQf` (so that `eisQf (u + w) = eisQf u + eisQf w + eisBil u w`). -/
def eisBil (a a' a'' b b' b'' : ℤ) (u w : ℤ × ℤ × ℤ) : ℤ :=
  2 * a * u.1 * w.1 + 2 * a' * u.2.1 * w.2.1 + 2 * a'' * u.2.2 * w.2.2 +
  2 * b * (u.2.1 * w.2.2 + u.2.2 * w.2.1) + 2 * b' * (u.1 * w.2.2 + u.2.2 * w.1) +
  2 * b'' * (u.1 * w.2.1 + u.2.1 * w.1)

/-- `eisQf` on a triple. -/
def eisQv (a a' a'' b b' b'' : ℤ) (u : ℤ × ℤ × ℤ) : ℤ := eisQf a a' a'' b b' b'' u.1 u.2.1 u.2.2

/-- Determinant of the matrix with columns `u v w`. -/
def eisDet3 (u v w : ℤ × ℤ × ℤ) : ℤ :=
  u.1 * (v.2.1 * w.2.2 - w.2.1 * v.2.2) - v.1 * (u.2.1 * w.2.2 - w.2.1 * u.2.2) +
    w.1 * (u.2.1 * v.2.2 - v.2.1 * u.2.2)

/-- Vectors in the cube `[-B,B]^3` of value `d`. -/
def eisColSet (a a' a'' b b' b'' B d : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B).filter
    (fun u => eisQv a a' a'' b b' b'' u = d)

/-- The finite set of column triples of automorphs. -/
def eisAutoSet (a a' a'' b b' b'' B : ℤ) : Finset ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  (eisColSet a a' a'' b b' b'' B a ×ˢ eisColSet a a' a'' b b' b'' B a' ×ˢ eisColSet a a' a'' b b' b'' B a'').filter
    (fun t => eisBil a a' a'' b b' b'' t.1 t.2.1 = 2 * b'' ∧ eisBil a a' a'' b b' b'' t.1 t.2.2 = 2 * b' ∧
      eisBil a a' a'' b b' b'' t.2.1 t.2.2 = 2 * b ∧ eisDet3 t.1 t.2.1 t.2.2 = 1)

theorem eval_eisensteinForm (a a' a'' b b' b'' : ℤ) (v : Fin 3 → ℤ) :
    QuadForm.eval (eisensteinForm a a' a'' b b' b'') v = eisQf a a' a'' b b' b'' (v 0) (v 1) (v 2) := by
  simp [QuadForm.eval, QuadForm.evalIn, eisensteinForm, QuadForm.ofUpper, Fin.sum_univ_three, eisQf]
  ring

theorem automorph_iff (a a' a'' b b' b'' : ℤ) (g : Matrix (Fin 3) (Fin 3) ℤ) :
    (∀ v, QuadForm.eval (eisensteinForm a a' a'' b b' b'') (g *ᵥ v) =
        QuadForm.eval (eisensteinForm a a' a'' b b' b'') v) ↔
    (eisQf a a' a'' b b' b'' (g 0 0) (g 1 0) (g 2 0) = a ∧
     eisQf a a' a'' b b' b'' (g 0 1) (g 1 1) (g 2 1) = a' ∧
     eisQf a a' a'' b b' b'' (g 0 2) (g 1 2) (g 2 2) = a'' ∧
     eisBil a a' a'' b b' b'' (g 0 0, g 1 0, g 2 0) (g 0 1, g 1 1, g 2 1) = 2 * b'' ∧
     eisBil a a' a'' b b' b'' (g 0 0, g 1 0, g 2 0) (g 0 2, g 1 2, g 2 2) = 2 * b' ∧
     eisBil a a' a'' b b' b'' (g 0 1, g 1 1, g 2 1) (g 0 2, g 1 2, g 2 2) = 2 * b) := by
  simp only [eval_eisensteinForm]
  constructor
  · intro h
    have h0 := h ![1, 0, 0]
    have h1 := h ![0, 1, 0]
    have h2 := h ![0, 0, 1]
    have h01 := h ![1, 1, 0]
    have h02 := h ![1, 0, 1]
    have h12 := h ![0, 1, 1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, eisQf] at h0 h1 h2 h01 h02 h12
    simp only [eisQf, eisBil]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h01, h02, h12⟩ v
    simp only [eisQf, eisBil] at h0 h1 h2 h01 h02 h12 ⊢
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination (v 0) ^ 2 * h0 + (v 1) ^ 2 * h1 + (v 2) ^ 2 * h2 +
      (v 0) * (v 1) * h01 + (v 0) * (v 2) * h02 + (v 1) * (v 2) * h12

/-- Matrices versus triples of columns. -/
def eisColEquiv : Matrix (Fin 3) (Fin 3) ℤ ≃ (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) where
  toFun g := ((g 0 0, g 1 0, g 2 0), (g 0 1, g 1 1, g 2 1), (g 0 2, g 1 2, g 2 2))
  invFun t := !![t.1.1, t.2.1.1, t.2.2.1; t.1.2.1, t.2.1.2.1, t.2.2.2.1;
    t.1.2.2, t.2.1.2.2, t.2.2.2.2]
  left_inv g := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv t := by
    obtain ⟨⟨_, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _⟩⟩ := t
    rfl

theorem mem_eisColSet (a a' a'' b b' b'' B d : ℤ) (u : ℤ × ℤ × ℤ) :
    u ∈ eisColSet a a' a'' b b' b'' B d ↔
      ((-B ≤ u.1 ∧ u.1 ≤ B) ∧ (-B ≤ u.2.1 ∧ u.2.1 ≤ B) ∧ (-B ≤ u.2.2 ∧ u.2.2 ≤ B)) ∧
        eisQf a a' a'' b b' b'' u.1 u.2.1 u.2.2 = d := by
  unfold eisColSet
  rw [Finset.mem_filter]
  simp only [Finset.mem_product, Finset.mem_Icc, eisQv]

/-- Membership in `eisAutoSet`, given the bound hypotheses. -/
theorem mem_eisAutoSet (a a' a'' b b' b'' N B : ℤ)
    (hb : ∀ x y z, eisQf a a' a'' b b' b'' x y z ≤ N →
      -B ≤ x ∧ x ≤ B ∧ -B ≤ y ∧ y ≤ B ∧ -B ≤ z ∧ z ≤ B)
    (h0 : a ≤ N) (h1 : a' ≤ N) (h2 : a'' ≤ N) (t : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :
    t ∈ eisAutoSet a a' a'' b b' b'' B ↔
      (eisQf a a' a'' b b' b'' t.1.1 t.1.2.1 t.1.2.2 = a ∧
       eisQf a a' a'' b b' b'' t.2.1.1 t.2.1.2.1 t.2.1.2.2 = a' ∧
       eisQf a a' a'' b b' b'' t.2.2.1 t.2.2.2.1 t.2.2.2.2 = a'') ∧
      eisBil a a' a'' b b' b'' t.1 t.2.1 = 2 * b'' ∧ eisBil a a' a'' b b' b'' t.1 t.2.2 = 2 * b' ∧
      eisBil a a' a'' b b' b'' t.2.1 t.2.2 = 2 * b ∧ eisDet3 t.1 t.2.1 t.2.2 = 1 := by
  obtain ⟨u, v, w⟩ := t
  unfold eisAutoSet
  rw [Finset.mem_filter]
  simp only [Finset.mem_product, mem_eisColSet]
  have mem : ∀ x y z, eisQf a a' a'' b b' b'' x y z ≤ N →
      (-B ≤ x ∧ x ≤ B) ∧ (-B ≤ y ∧ y ≤ B) ∧ (-B ≤ z ∧ z ≤ B) := fun x y z h => by
    obtain ⟨l1, u1, l2, u2, l3, u3⟩ := hb x y z h
    exact ⟨⟨l1, u1⟩, ⟨l2, u2⟩, ⟨l3, u3⟩⟩
  constructor
  · rintro ⟨⟨⟨_, q0⟩, ⟨_, q1⟩, ⟨_, q2⟩⟩, c01, c02, c12, hd⟩
    exact ⟨⟨q0, q1, q2⟩, c01, c02, c12, hd⟩
  · rintro ⟨⟨q0, q1, q2⟩, c01, c02, c12, hd⟩
    exact ⟨⟨⟨mem _ _ _ (q0.le.trans h0), q0⟩, ⟨mem _ _ _ (q1.le.trans h1), q1⟩,
      ⟨mem _ _ _ (q2.le.trans h2), q2⟩⟩, c01, c02, c12, hd⟩

/-- **Counting reduction:** if the form is bounded on the cube `[-B,B]^3` whenever it is `≤ N`, and
the diagonal coefficients are `≤ N`, then the number of proper automorphs is the size of `eisAutoSet`. -/
theorem automorphCount_eq (a a' a'' b b' b'' N B : ℤ)
    (hb : ∀ x y z, eisQf a a' a'' b b' b'' x y z ≤ N →
      -B ≤ x ∧ x ≤ B ∧ -B ≤ y ∧ y ≤ B ∧ -B ≤ z ∧ z ≤ B)
    (h0 : a ≤ N) (h1 : a' ≤ N) (h2 : a'' ≤ N) :
    automorphCount (eisensteinForm a a' a'' b b' b'') = (eisAutoSet a a' a'' b b' b'' B).card := by
  classical
  unfold automorphCount
  rw [Nat.card_congr (show {g : SpecialLinearGroup (Fin 3) ℤ // ∀ v, QuadForm.eval
        (eisensteinForm a a' a'' b b' b'') ((g : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v) =
        QuadForm.eval (eisensteinForm a a' a'' b b' b'') v} ≃
      {g : Matrix (Fin 3) (Fin 3) ℤ // g.det = 1 ∧ ∀ v, QuadForm.eval
        (eisensteinForm a a' a'' b b' b'') (g *ᵥ v) =
        QuadForm.eval (eisensteinForm a a' a'' b b' b'') v} from
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })]
  rw [Nat.card_congr (Equiv.subtypeEquiv eisColEquiv (q := fun t => t ∈ eisAutoSet a a' a'' b b' b'' B)
    (fun g => by
      rw [automorph_iff, mem_eisAutoSet a a' a'' b b' b'' N B hb h0 h1 h2]
      have hdet : g.det = eisDet3 (g 0 0, g 1 0, g 2 0) (g 0 1, g 1 1, g 2 1) (g 0 2, g 1 2, g 2 2) := by
        rw [Matrix.det_fin_three]
        simp only [eisDet3]
        ring
      rw [hdet]
      constructor
      · rintro ⟨hd, q0, q1, q2, c01, c02, c12⟩
        exact ⟨⟨q0, q1, q2⟩, c01, c02, c12, hd⟩
      · rintro ⟨⟨q0, q1, q2⟩, c01, c02, c12, hd⟩
        exact ⟨hd, q0, q1, q2, c01, c02, c12⟩))]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Auxiliary: bounds on the coordinates from `eisQf ≤ N`. -/
macro "eis_bound" : tactic => `(tactic| (
  intro x y z h
  simp only [eisQf] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + z), sq_nonneg (x - z),
    sq_nonneg (y + z), sq_nonneg (y - z), sq_nonneg (x + y + z), sq_nonneg (x + y - z),
    sq_nonneg (x - y + z), sq_nonneg (x - y - z), sq_nonneg x, sq_nonneg y, sq_nonneg z]))

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (2, 2, 2; 1, 1, 1); the number δ of proper automorphs equals the table value $24$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_1 :
    automorphCount (eisensteinForm 2 2 2 1 1 1) = eisensteinDelta 2 2 2 1 1 1 := by
  have hc : (eisAutoSet 2 2 2 1 1 1 1).card = 24 := by decide +kernel
  rw [automorphCount_eq 2 2 2 1 1 1 2 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (1, 1, 1; 0, 0, 0); the number δ of proper automorphs equals the table value $24$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_2 :
    automorphCount (eisensteinForm 1 1 1 0 0 0) = eisensteinDelta 1 1 1 0 0 0 := by
  have hc : (eisAutoSet 1 1 1 0 0 0 1).card = 24 := by decide +kernel
  rw [automorphCount_eq 1 1 1 0 0 0 1 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (3, 3, 3; -1, -1, -1); the number δ of proper automorphs equals the table value $24$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_3 :
    automorphCount (eisensteinForm 3 3 3 (-1) (-1) (-1)) = eisensteinDelta 3 3 3 (-1) (-1) (-1) := by
  have hc : (eisAutoSet 3 3 3 (-1) (-1) (-1) 1).card = 24 := by decide +kernel
  rw [automorphCount_eq 3 3 3 (-1) (-1) (-1) 3 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (1, 2, 2; -1, 0, 0); the number δ of proper automorphs equals the table value $12$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_4 :
    automorphCount (eisensteinForm 1 2 2 (-1) 0 0) = eisensteinDelta 1 2 2 (-1) 0 0 := by
  have hc : (eisAutoSet 1 2 2 (-1) 0 0 1).card = 12 := by decide +kernel
  rw [automorphCount_eq 1 2 2 (-1) 0 0 2 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (2, 2, 3; -1, -1, 0); the number δ of proper automorphs equals the table value $8$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_5 :
    automorphCount (eisensteinForm 2 2 3 (-1) (-1) 0) = eisensteinDelta 2 2 3 (-1) (-1) 0 := by
  have hc : (eisAutoSet 2 2 3 (-1) (-1) 0 1).card = 8 := by decide +kernel
  rw [automorphCount_eq 2 2 3 (-1) (-1) 0 3 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (4, 5, 6; 1, 2, 2); the number δ of proper automorphs equals the table value $4$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_6 :
    automorphCount (eisensteinForm 4 5 6 1 2 2) = eisensteinDelta 4 5 6 1 2 2 := by
  have hc : (eisAutoSet 4 5 6 1 2 2 1).card = 4 := by decide +kernel
  rw [automorphCount_eq 4 5 6 1 2 2 6 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (2, 5, 8; -1, -1, 0); the number δ of proper automorphs equals the table value $2$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_7 :
    automorphCount (eisensteinForm 2 5 8 (-1) (-1) 0) = eisensteinDelta 2 5 8 (-1) (-1) 0 := by
  have hc : (eisAutoSet 2 5 8 (-1) (-1) 0 2).card = 2 := by decide +kernel
  rw [automorphCount_eq 2 5 8 (-1) (-1) 0 8 2 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked example (3, 4, 6; 2, 1, 1); the number δ of proper automorphs equals the table value $1$. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisenstein_row_8 :
    automorphCount (eisensteinForm 3 4 6 2 1 1) = eisensteinDelta 3 4 6 2 1 1 := by
  have hc : (eisAutoSet 3 4 6 2 1 1 1).card = 1 := by decide +kernel
  rw [automorphCount_eq 3 4 6 2 1 1 6 1 (by eis_bound) (by norm_num) (by norm_num) (by norm_num), hc]
  decide

/-- the historical sources: Eisenstein 1851, § 6, pp. 164-165, worked examples; for all eight examples
the number δ of proper automorphs equals the table value. -/
@[kb "eisenstein1851" "§ 6, pp. 164-165"]
theorem eisensteinDelta_rows_examples :
    automorphCount (eisensteinForm 2 2 2 1 1 1) = eisensteinDelta 2 2 2 1 1 1 ∧
    automorphCount (eisensteinForm 1 1 1 0 0 0) = eisensteinDelta 1 1 1 0 0 0 ∧
    automorphCount (eisensteinForm 3 3 3 (-1) (-1) (-1)) = eisensteinDelta 3 3 3 (-1) (-1) (-1) ∧
    automorphCount (eisensteinForm 1 2 2 (-1) 0 0) = eisensteinDelta 1 2 2 (-1) 0 0 ∧
    automorphCount (eisensteinForm 2 2 3 (-1) (-1) 0) = eisensteinDelta 2 2 3 (-1) (-1) 0 ∧
    automorphCount (eisensteinForm 4 5 6 1 2 2) = eisensteinDelta 4 5 6 1 2 2 ∧
    automorphCount (eisensteinForm 2 5 8 (-1) (-1) 0) = eisensteinDelta 2 5 8 (-1) (-1) 0 ∧
    automorphCount (eisensteinForm 3 4 6 2 1 1) = eisensteinDelta 3 4 6 2 1 1 :=
  ⟨eisenstein_row_1, eisenstein_row_2, eisenstein_row_3, eisenstein_row_4, eisenstein_row_5,
    eisenstein_row_6, eisenstein_row_7, eisenstein_row_8⟩

end QuadFormsKB.Historical.Gauss
