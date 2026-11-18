import QuadFormsKB.Historical.Gauss.Forms

/-!
# Finiteness of the transformations of a form into another (Disquisitiones Arithmeticae, Art. 214)

(Gauss, *Disq. Arith.* Art. 214, closing remark).

Gauss remarks, after describing all proper transformations of $f$ into $F$ (see `Transformations.lean`), that
their number is **finite when the determinant $D$ is negative or a nonzero square**, and that it can be infinite
otherwise (for $D$ positive nonsquare, via the Pell equation, Arts. 202-205; for $D = 0$ trivially).

Proved here (all unconditional):

* `transformationsInto_finite_of_disc_neg`: if $\operatorname{disc}(f) < 0$ (positive or negative definite) then
  for every $F$ the set of substitutions $(\alpha, \beta, \gamma, \delta) \in \mathbb{Z}^4$ of **any**
  determinant carrying $f$ into $F$ is finite; hence so is the set of proper ones.
* `gauss_properTransformations_finite_of_gaussDet_neg`: the same for Gauss's forms $(a, b, c)$ with $b^2 - ac < 0$.
* `properTransformationsInto_finite_of_disc_sq`: if $\operatorname{disc}(f) = s^2$ with $s \ne 0$ then the set of
  **proper** transformations ($\alpha\delta - \beta\gamma = 1$) of $f$ into $F$ is finite.
  `gauss_properTransformations_finite_of_gaussDet_sq` is the version for Gauss's forms with $b^2 - ac = h^2$,
  $h \ne 0$.
* `properTransformations_infinite_gaussDet_zero`: for $D = 0$, $f = F = x^2 = (1, 0, 0)$ has infinitely many proper
  transformations $(1, 0, k, 1)$.
* `properTransformations_infinite_gaussDet_two`: for $D = 2$, $f = F = x^2 - 2y^2 = (1, 0, -2)$ has infinitely
  many proper transformations (the automorphs $(u, 2v, v, u)$ with $u^2 - 2v^2 = 1$).

Not formalized: Gauss's statement for $D$ a nonsquare positive that infinitely many always occur once one exists
(only the example $D = 2$ is given).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **All transformations of $f$ into $F$:** the substitutions $(\alpha, \beta, \gamma, \delta) \in \mathbb{Z}^4$
(of any determinant) with $F(x, y) = f(\alpha x + \beta y, \gamma x + \delta y)$. -/
def transformationsInto (f F : BinQF) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {T | subst T.1 T.2.1 T.2.2.1 T.2.2.2 f = F}

/-- **All proper transformations of $f$ into $F$:** the substitutions $(\alpha, \beta, \gamma, \delta)$ with
$\alpha\delta - \beta\gamma = 1$ and $F(x, y) = f(\alpha x + \beta y, \gamma x + \delta y)$ (Gauss, Art. 157). -/
def properTransformationsInto (f F : BinQF) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {T | T.1 * T.2.2.2 - T.2.1 * T.2.2.1 = 1 ∧ subst T.1 T.2.1 T.2.2.1 T.2.2.2 f = F}

theorem properTransformationsInto_subset (f F : BinQF) :
    properTransformationsInto f F ⊆ transformationsInto f F := fun _ h => h.2

private theorem abs_le_sq_int (z : ℤ) : |z| ≤ z ^ 2 := by
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |z| := Int.one_le_abs h
    nlinarith [sq_abs z, mul_nonneg (abs_nonneg z) (by linarith : (0:ℤ) ≤ |z| - 1)]

/-- A form of negative discriminant takes each value at only finitely many integer points. -/
private theorem finite_values_of_disc_neg (f : BinQF) (hD : f.disc < 0) (n : ℤ) :
    {p : ℤ × ℤ | f.eval p.1 p.2 = n}.Finite := by
  have ha : f.a ≠ 0 := by
    intro h
    have : f.disc = f.b ^ 2 := by simp [disc, h]
    nlinarith [sq_nonneg f.b]
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = 4 * |f.a| * |n| := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = N + |f.b| * N := ⟨_, rfl⟩
  apply (Set.finite_Icc ((-B, -B) : ℤ × ℤ) (B, B)).subset
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_setOf_eq] at hxy
  have key : (2 * f.a * x + f.b * y) ^ 2 + (-f.disc) * y ^ 2 = 4 * f.a * n := by
    rw [← hxy, eval_eq]; simp only [disc]; ring
  have hle : 4 * f.a * n ≤ N := by
    calc 4 * f.a * n ≤ |4 * f.a * n| := le_abs_self _
      _ = N := by rw [hN, abs_mul, abs_mul]; norm_num
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = 2 * f.a * x + f.b * y := ⟨_, rfl⟩
  rw [← hu] at key
  have hy2 : y ^ 2 ≤ N := by
    nlinarith [sq_nonneg u, mul_nonneg (by linarith : (0:ℤ) ≤ -f.disc - 1) (sq_nonneg y)]
  have hu2 : u ^ 2 ≤ N := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -f.disc) (sq_nonneg y)]
  have hy : |y| ≤ N := (abs_le_sq_int y).trans hy2
  have hu' : |u| ≤ N := (abs_le_sq_int u).trans hu2
  have hby : |f.b * y| ≤ |f.b| * N := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have hu'' := abs_le.1 hu'
  have hby' := abs_le.1 hby
  have hy'' := abs_le.1 hy
  have hax : |2 * f.a * x| ≤ B := by
    apply abs_le.2
    have : 2 * f.a * x = u - f.b * y := by rw [hu]; ring
    constructor <;> nlinarith
  have hx : |x| ≤ |2 * f.a * x| := by
    have h1 : 1 ≤ |2 * f.a| := Int.one_le_abs (by omega)
    rw [abs_mul]; nlinarith [abs_nonneg x]
  have hx' := abs_le.1 (hx.trans hax)
  simp only [Set.mem_Icc, Prod.mk_le_mk]
  exact ⟨⟨hx'.1, hy''.1.trans' (by nlinarith)⟩, hx'.2, hy''.2.trans (by nlinarith)⟩

/-- **Finitely many transformations when $\operatorname{disc}(f) < 0$** (Gauss, *Disq. Arith.* Art. 214,
closing remark): if the binary form $f$ has negative discriminant (it is positive
definite or negative definite; Gauss's $D < 0$) then for every form $F$ only finitely many
substitutions $(\alpha, \beta, \gamma, \delta) \in \mathbb{Z}^4$ carry $f$ into $F$, of any determinant, in
particular only finitely many proper ones. Proof: $F(1, 0) = f(\alpha, \gamma)$ and $F(0, 1) = f(\beta, \delta)$, and
a form of negative discriminant takes each value at finitely many integer points
(from $4a f(x, y) = (2ax + by)^2 + |\operatorname{disc}|\,y^2$). Gauss states this for his forms
$(a, b, c)$ with determinant $D < 0$, see `gauss_properTransformations_finite_of_gaussDet_neg`. -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem transformationsInto_finite_of_disc_neg (f F : BinQF) (hD : f.disc < 0) :
    (transformationsInto f F).Finite := by
  have h1 := finite_values_of_disc_neg f hD F.a
  have h2 := finite_values_of_disc_neg f hD F.c
  apply ((h1.prod h2).image (fun q : (ℤ × ℤ) × (ℤ × ℤ) => (q.1.1, q.2.1, q.1.2, q.2.2))).subset
  rintro ⟨α, β, γ, δ⟩ hT
  have hT' : subst α β γ δ f = F := hT
  refine ⟨((α, γ), (β, δ)), ⟨?_, ?_⟩, rfl⟩
  · show f.eval α γ = F.a
    rw [← hT', eval_eq]; simp only [subst, a_mk]
  · show f.eval β δ = F.c
    rw [← hT', eval_eq]; simp only [subst, c_mk]

/-- **Proper version for $\operatorname{disc}(f) < 0$** (Gauss, *Disq. Arith.* Art. 214, closing remark,
the historical sources): the set of proper transformations of $f$ into $F$ is finite. Consequence of
`transformationsInto_finite_of_disc_neg`. -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem properTransformationsInto_finite_of_disc_neg (f F : BinQF) (hD : f.disc < 0) :
    (properTransformationsInto f F).Finite :=
  (transformationsInto_finite_of_disc_neg f F hD).subset (properTransformationsInto_subset f F)

/-- **Gauss's headline, $D < 0$** (*Disq. Arith.* Art. 214, closing remark): if the
determinant $D = b^2 - ac$ of Gauss's form $(a, b, c)$ is negative, then for every form $F$ there are only finitely
many proper transformations of $(a, b, c)$ into $F$ (and indeed finitely many transformations of any determinant).
No difference from the source. -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem gauss_properTransformations_finite_of_gaussDet_neg (a b c : ℤ) (F : BinQF)
    (hD : gaussDet a b c < 0) : (properTransformationsInto (gaussForm a b c) F).Finite :=
  properTransformationsInto_finite_of_disc_neg _ F (by rw [disc_gaussForm]; omega)

/-- **Positive definite forms** ($0 < a$, $\operatorname{disc} < 0$): finitely many proper transformations into
any $F$. Special case of `properTransformationsInto_finite_of_disc_neg`. -/
theorem properTransformationsInto_finite_of_posDef' (f F : BinQF) (hf : f.PosDef') :
    (properTransformationsInto f F).Finite :=
  properTransformationsInto_finite_of_disc_neg f F hf.2

/-! ### Square discriminant -/

private theorem abs_le_abs_mul_int {x y : ℤ} (h : x * y ≠ 0) : |x| ≤ |x * y| := by
  have h1 : 1 ≤ |y| := Int.one_le_abs (right_ne_zero_of_mul h)
  rw [abs_mul]; nlinarith [abs_nonneg x]

private theorem abs_le_mul_left_int {κ : ℤ} (hκ : κ ≠ 0) (z : ℤ) : |z| ≤ |κ * z| := by
  have h1 : 1 ≤ |κ| := Int.one_le_abs hκ
  rw [abs_mul]; nlinarith [abs_nonneg z]

/-- If $AE - BC = d \ne 0$ then $|A| \le |AB| + |CE| + |d|$. -/
private theorem bound_A (A B C E d : ℤ) (hd : d ≠ 0) (h : A * E - B * C = d) :
    |A| ≤ |A * B| + |C * E| + |d| := by
  have h1 := abs_nonneg (A * B)
  have h2 := abs_nonneg (C * E)
  have h3 := abs_nonneg d
  rcases eq_or_ne A 0 with hA | hA
  · rw [hA, abs_zero]; positivity
  rcases eq_or_ne B 0 with hB | hB
  · have h4 : A * E = d := by rw [hB] at h; linarith
    have h5 : |A| ≤ |A * E| := abs_le_abs_mul_int (by rw [h4]; exact hd)
    rw [h4] at h5; linarith
  · have h6 : |A| ≤ |A * B| := abs_le_abs_mul_int (mul_ne_zero hA hB)
    linarith

/-- **Key lemma on isotropic vectors:** if $\operatorname{disc}(f) = s^2$ with $s \ne 0$ there are integer vectors
$(p, r)$, $(q, t)$ with $f(p, r) = f(q, t) = 0$ and $pt - qr \ne 0$. -/
private theorem exists_isotropic_pair (f : BinQF) {s : ℤ} (hs : s ≠ 0) (hD : f.disc = s ^ 2) :
    ∃ p q r t : ℤ, f.eval p r = 0 ∧ f.eval q t = 0 ∧ p * t - q * r ≠ 0 := by
  have hD' : f.b ^ 2 - 4 * f.a * f.c = s ^ 2 := hD
  by_cases ha : f.a = 0
  · have hb : f.b ≠ 0 := by
      intro h
      apply hs
      rw [ha, h] at hD'
      have : s ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    refine ⟨1, -f.c, 0, f.b, ?_, ?_, ?_⟩
    · rw [eval_eq, ha]; ring
    · rw [eval_eq, ha]; ring
    · simpa using hb
  · refine ⟨f.b + s, f.b - s, -2 * f.a, -2 * f.a, ?_, ?_, ?_⟩
    · rw [eval_eq]; linear_combination (-f.a) * hD'
    · rw [eval_eq]; linear_combination (-f.a) * hD'
    · have : (f.b + s) * (-2 * f.a) - (f.b - s) * (-2 * f.a) = -4 * f.a * s := by ring
      rw [this]
      exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hs

/-- **Finitely many proper transformations when $\operatorname{disc}(f)$ is a nonzero square** (Gauss,
*Disq. Arith.* Art. 214, closing remark): if $\operatorname{disc}(f) = s^2$ with
$s \ne 0$, then for every $F$ only finitely many substitutions $(\alpha, \beta, \gamma, \delta)$ with
$\alpha\delta - \beta\gamma = 1$ carry $f$ into $F$.
Proof: choose integer isotropic vectors $w_1 = (p, r)$, $w_2 = (q, t)$ of $f$ with $d = pt - qr \ne 0$; then
$d^2 f(v) = \kappa\,P(v)\,Q(v)$ with the integer linear forms $P(v) = \det(v, w_2)$, $Q(v) = \det(w_1, v)$ and
$\kappa = f(w_1 + w_2) \ne 0$. For a proper transformation with columns $v_1, v_2$ the integers
$A = P(v_1), B = Q(v_1), C = P(v_2), E = Q(v_2)$ satisfy $AE - BC = d$, $\kappa AB = d^2 F(1, 0)$,
$\kappa CE = d^2 F(0, 1)$, which bounds all four, and $(A, B, C, E)$ determines the transformation. -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem properTransformationsInto_finite_of_disc_sq (f F : BinQF) {s : ℤ} (hs : s ≠ 0)
    (hD : f.disc = s ^ 2) : (properTransformationsInto f F).Finite := by
  obtain ⟨p, q, r, t, h1, h2, hd⟩ := exists_isotropic_pair f hs hD
  obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, κ = f.eval (p + q) (r + t) := ⟨_, rfl⟩
  have key : ∀ x y : ℤ, (p * t - q * r) ^ 2 * f.eval x y =
      κ * ((x * t - y * q) * (p * y - r * x)) := by
    intro x y
    rw [eval_eq] at h1 h2 hκ ⊢
    linear_combination ((x * t - y * q) ^ 2 - (x * t - y * q) * (p * y - r * x)) * h1 +
      ((p * y - r * x) ^ 2 - (x * t - y * q) * (p * y - r * x)) * h2 -
      ((x * t - y * q) * (p * y - r * x)) * hκ
  have hd2 : (p * t - q * r) ^ 2 ≠ 0 := pow_ne_zero _ hd
  have hκ0 : κ ≠ 0 := by
    intro h0
    have z : ∀ x y : ℤ, f.eval x y = 0 := by
      intro x y
      have := key x y
      rw [h0, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hd2
    have e1 := z 1 0
    have e2 := z 0 1
    have e3 := z 1 1
    rw [eval_eq] at e1 e2 e3
    simp at e1 e2 e3
    have hb : f.b = 0 := by linarith
    apply hs
    have : s ^ 2 = 0 := by rw [← hD]; simp only [disc]; rw [hb, e1, e2]; ring
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = |(p * t - q * r) ^ 2 * F.a| + |(p * t - q * r) ^ 2 * F.c| +
      |p * t - q * r| := ⟨_, rfl⟩
  let g : ℤ × ℤ × ℤ × ℤ → ℤ × ℤ × ℤ × ℤ := fun x =>
    ((x.1 * p + x.2.1 * q) / (p * t - q * r), (x.2.2.1 * p + x.2.2.2 * q) / (p * t - q * r),
      (x.1 * r + x.2.1 * t) / (p * t - q * r), (x.2.2.1 * r + x.2.2.2 * t) / (p * t - q * r))
  apply ((Set.finite_Icc ((-K, -K, -K, -K) : ℤ × ℤ × ℤ × ℤ) (K, K, K, K)).image g).subset
  rintro ⟨α, β, γ, δ⟩ ⟨hdet, hT⟩
  have hdet' : α * δ - β * γ = 1 := hdet
  have hT' : subst α β γ δ f = F := hT
  have hFa : f.eval α γ = F.a := by
    rw [← hT', eval_eq]; simp only [subst, a_mk]
  have hFc : f.eval β δ = F.c := by
    rw [← hT', eval_eq]; simp only [subst, c_mk]
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = α * t - γ * q := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℤ, B = p * γ - r * α := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = β * t - δ * q := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℤ, E = p * δ - r * β := ⟨_, rfl⟩
  have hAE : A * E - B * C = p * t - q * r := by
    rw [hA, hBd, hC, hE]; linear_combination (p * t - q * r) * hdet'
  have nAB : κ * (A * B) = (p * t - q * r) ^ 2 * F.a := by
    rw [hA, hBd, ← hFa, key]
  have nCE : κ * (C * E) = (p * t - q * r) ^ 2 * F.c := by
    rw [hC, hE, ← hFc, key]
  have hAB : |A * B| ≤ |(p * t - q * r) ^ 2 * F.a| := by
    rw [← nAB]; exact abs_le_mul_left_int hκ0 _
  have hCE : |C * E| ≤ |(p * t - q * r) ^ 2 * F.c| := by
    rw [← nCE]; exact abs_le_mul_left_int hκ0 _
  have bA := bound_A A B C E _ hd hAE
  have bB := bound_A B A E C (-(p * t - q * r)) (neg_ne_zero.2 hd) (by linarith)
  have bC := bound_A C E A B (-(p * t - q * r)) (neg_ne_zero.2 hd) (by linarith)
  have bE := bound_A E C B A (p * t - q * r) hd (by linarith)
  have c1 : |B * A| = |A * B| := by rw [mul_comm]
  have c2 : |E * C| = |C * E| := by rw [mul_comm]
  rw [abs_neg] at bB bC
  have bA' := abs_le.1 (bA.trans (by rw [hK]; linarith) : |A| ≤ K)
  have bB' := abs_le.1 (bB.trans (by rw [hK]; linarith) : |B| ≤ K)
  have bC' := abs_le.1 (bC.trans (by rw [hK]; linarith) : |C| ≤ K)
  have bE' := abs_le.1 (bE.trans (by rw [hK]; linarith) : |E| ≤ K)
  refine ⟨(A, B, C, E), ?_, ?_⟩
  · simp only [Set.mem_Icc, Prod.mk_le_mk]
    exact ⟨⟨bA'.1, bB'.1, bC'.1, bE'.1⟩, bA'.2, bB'.2, bC'.2, bE'.2⟩
  · have e1 : A * p + B * q = (p * t - q * r) * α := by rw [hA, hBd]; ring
    have e2 : C * p + E * q = (p * t - q * r) * β := by rw [hC, hE]; ring
    have e3 : A * r + B * t = (p * t - q * r) * γ := by rw [hA, hBd]; ring
    have e4 : C * r + E * t = (p * t - q * r) * δ := by rw [hC, hE]; ring
    simp only [g]
    rw [Int.ediv_eq_of_eq_mul_right hd e1, Int.ediv_eq_of_eq_mul_right hd e2,
      Int.ediv_eq_of_eq_mul_right hd e3, Int.ediv_eq_of_eq_mul_right hd e4]

/-- **Gauss's headline, $D$ a nonzero square** (*Disq. Arith.* Art. 214, closing remark, the historical sources
): if the determinant $D = b^2 - ac = h^2$ of Gauss's form $(a, b, c)$ is a nonzero square, then for
every form $F$ there are only finitely many proper transformations of $(a, b, c)$ into $F$.
No difference from the source (here $\operatorname{disc} = 4h^2 = (2h)^2$). -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem gauss_properTransformations_finite_of_gaussDet_sq (a b c h : ℤ) (F : BinQF)
    (hh : h ≠ 0) (hD : gaussDet a b c = h ^ 2) :
    (properTransformationsInto (gaussForm a b c) F).Finite :=
  properTransformationsInto_finite_of_disc_sq _ F (s := 2 * h) (by omega)
    (by rw [disc_gaussForm, hD]; ring)

/-! ### Why $D < 0$ or square is needed -/

/-- **$D = 0$: infinitely many proper transformations** (*Disq. Arith.* Art. 214, closing remark; the historical sources
): Gauss's form $(1, 0, 0) = x^2$, of determinant $0$, goes into itself by the proper substitutions
$(1, 0, k, 1)$ ($x \mapsto x$, $y \mapsto k x + y$) for every integer $k$. -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem properTransformations_infinite_gaussDet_zero :
    gaussDet 1 0 0 = 0 ∧
      (properTransformationsInto (gaussForm 1 0 0) (gaussForm 1 0 0)).Infinite := by
  refine ⟨by simp [gaussDet], ?_⟩
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => ((1, 0, k, 1) : ℤ × ℤ × ℤ × ℤ))
    (fun k l h => by simpa using h) (fun k => ⟨by simp, ?_⟩)
  show subst 1 0 k 1 (gaussForm 1 0 0) = gaussForm 1 0 0
  apply ext_eval; intro x y
  simp only [eval_subst, eval_gaussForm]; ring

/-- The sequence of solutions of $u^2 - 2v^2 = 1$ generated by $(3, 2)$:
$(u, v) \mapsto (3u + 4v, 2u + 3v)$, starting at $(1, 0)$. -/
private def pellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pellSeq n).1 + 4 * (pellSeq n).2, 2 * (pellSeq n).1 + 3 * (pellSeq n).2)

private theorem pellSeq_prop (n : ℕ) :
    (pellSeq n).1 ^ 2 - 2 * (pellSeq n).2 ^ 2 = 1 ∧ 1 ≤ (pellSeq n).1 ∧ 0 ≤ (pellSeq n).2 := by
  induction n with
  | zero => simp [pellSeq]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [pellSeq]
    refine ⟨by linear_combination h1, by linarith, by linarith⟩

/-- **$D = 2$ (positive nonsquare): infinitely many proper transformations** (*Disq. Arith.* Art. 214,
closing remark, with Arts. 202-205): Gauss's form $(1, 0, -2) = x^2 - 2y^2$, of
determinant $2$, goes into itself by the infinitely many proper substitutions $(u, 2v, v, u)$ with
$u^2 - 2v^2 = 1$ (powers of $(3, 4, 2, 3)$). -/
@[kb "gauss1801" "Art. 214, closing remark"]
theorem properTransformations_infinite_gaussDet_two :
    gaussDet 1 0 (-2) = 2 ∧
      (properTransformationsInto (gaussForm 1 0 (-2)) (gaussForm 1 0 (-2))).Infinite := by
  refine ⟨by simp [gaussDet], ?_⟩
  have hmono : StrictMono (fun n : ℕ => (pellSeq n).1) := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨-, h2, h3⟩ := pellSeq_prop n
    simp only [pellSeq]; linarith
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (((pellSeq n).1, 2 * (pellSeq n).2, (pellSeq n).2, (pellSeq n).1) :
      ℤ × ℤ × ℤ × ℤ))
    (fun m n h => hmono.injective (by simpa using congrArg Prod.fst h)) (fun n => ?_)
  obtain ⟨hu, -, -⟩ := pellSeq_prop n
  refine ⟨by simp only; linear_combination hu, ?_⟩
  show subst _ _ _ _ (gaussForm 1 0 (-2)) = gaussForm 1 0 (-2)
  apply ext_eval; intro x y
  simp only [eval_subst, eval_gaussForm]
  linear_combination (x ^ 2 - 2 * y ^ 2) * hu

end QuadFormsKB.Historical.Gauss
