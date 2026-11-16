import QuadFormsKB.Historical.Gauss.Composition

/-!
# Representation of products by a composite (Disquisitiones Arithmeticae, Art. 244)

(Art. 244: if $f$ represents $a$, $f'$ represents $a'$ and $F$ is transformable into
$f f'$, then $F$ represents $aa'$; for negative determinants $F$ is positive iff $f, f'$ are both positive or both
negative).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **Gauss, *Disq. Arith.* Art. 244: a composite represents the products.** If $F$ is
transformable into $f f'$ by the bilinear substitution $X = \sum p_i(\cdot)$, $Y = \sum q_i(\cdot)$ (Art. 235,
`TransformsInto`), $f(x, y) = a$ and $f'(x', y') = a'$, then $F(X, Y) = a a'$ at
$X = p_0 xx' + p_1 xy' + p_2 yx' + p_3 yy'$, $Y = q_0 xx' + q_1 xy' + q_2 yx' + q_3 yy'$. -/
@[kb "gauss1801" "Art. 244"]
theorem art244_represents_product {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    {a a' x y x' y' : ℤ} (ha : f.eval x y = a) (ha' : f'.eval x' y' = a') :
    F.eval (bilin p x y x' y') (bilin q x y x' y') = a * a' := by
  rw [hT, ha, ha']

/-- A form of negative discriminant takes nonzero values of the sign of its first coefficient:
$4a \cdot f(x, y) = (2ax + by)^2 - \operatorname{disc}(f)\, y^2$. -/
theorem mul_eval_pos {f : BinQF} (hd : f.disc < 0) {x y : ℤ} (h : f.eval x y ≠ 0) : 0 < f.a * f.eval x y := by
  have e : 4 * (f.a * f.eval x y) = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
    rw [eval_eq]; simp only [disc]; ring
  have h0 : f.a * f.eval x y ≠ 0 := by
    intro h0
    have ha : f.a ≠ 0 := by
      intro ha; simp only [disc, ha] at hd; nlinarith [sq_nonneg f.b]
    exact h (by rcases mul_eq_zero.mp h0 with h1 | h1 <;> [exact absurd h1 ha; exact h1])
  have : 0 ≤ 4 * (f.a * f.eval x y) := by rw [e]; nlinarith [sq_nonneg (2 * f.a * x + f.b * y), sq_nonneg y]
  omega

/-- **Gauss, *Disq. Arith.* Art. 244, the signs:** for negative determinants, if $F$ is
transformable into $f f'$ then $F$ is positive (first coefficient $> 0$) iff $f$ and $f'$ are both positive or both
negative. -/
@[kb "gauss1801" "Art. 244"]
theorem art244_sign {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q) (hF : F.disc < 0)
    (hf : f.disc < 0) (hf' : f'.disc < 0) : (0 < F.a ↔ (0 < f.a ↔ 0 < f'.a)) := by
  have ha : f.a ≠ 0 := by intro h; simp only [disc, h] at hf; nlinarith [sq_nonneg f.b]
  have ha' : f'.a ≠ 0 := by intro h; simp only [disc, h] at hf'; nlinarith [sq_nonneg f'.b]
  have hv := hT 1 0 1 0
  have e1 : f.eval 1 0 = f.a := by rw [eval_eq]; ring
  have e2 : f'.eval 1 0 = f'.a := by rw [eval_eq]; ring
  rw [e1, e2] at hv
  have hne : F.eval (bilin p 1 0 1 0) (bilin q 1 0 1 0) ≠ 0 := by rw [hv]; exact mul_ne_zero ha ha'
  have hpos := mul_eval_pos hF hne
  rw [hv] at hpos
  rcases lt_or_gt_of_ne ha with h1 | h1 <;> rcases lt_or_gt_of_ne ha' with h2 | h2
  · have : 0 < f.a * f'.a := mul_pos_of_neg_of_neg h1 h2
    constructor
    · intro _; constructor <;> intro h <;> linarith
    · intro _; nlinarith
  · have : f.a * f'.a < 0 := mul_neg_of_neg_of_pos h1 h2
    constructor
    · intro h; nlinarith
    · intro h; exact absurd (h.mpr h2) (by linarith)
  · have : f.a * f'.a < 0 := mul_neg_of_pos_of_neg h1 h2
    constructor
    · intro h; nlinarith
    · intro h; exact absurd (h.mp h1) (by linarith)
  · have : 0 < f.a * f'.a := mul_pos h1 h2
    constructor
    · intro _; exact ⟨fun _ => h2, fun _ => h1⟩
    · intro _; nlinarith

end QuadFormsKB.Historical.Gauss
