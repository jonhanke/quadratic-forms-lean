import QuadFormsKB.Historical.Gauss.Determinants
import QuadFormsKB.Historical.Gauss.SquareDeterminant

/-!
# Representations by forms of square determinant, and implication of forms of determinant $0$ (Disquisitiones Arithmeticae, Arts. 212, 215)

ids: (Art. 212: representations of $M \ne 0$, resp. $M = 0$, by a
form of square determinant $h^2$) (Art. 215 I) and (Art. 215 II) (forms of
determinant $0$).

* `art212_factorization` (proved, unconditional): a form $(a, b, c)$ with $b^2 - ac = h^2$ ($h$ any integer) is a
  product $a x^2 + 2bxy + cy^2 = (\delta x - \beta y)(f x - g y)$ of two integral linear forms. (Direct proof: $a = 0$
  is $y(2bx + cy)$; for $a \ne 0$ split $a$ and $b + h$ by their greatest common divisor.) `art212_factor_det`:
  then $(\delta g - \beta f)^2 = 4(b^2 - ac)$.
* `art212_zero_iff`: the representations of $0$ are the integral points of the two lines
  $\delta x = \beta y$, $f x = g y$.
* `art212_represent_iff`, `art212_represent_set`, `art212_cramer`, `art212_represent_finite`: for
  $M \ne 0$ the representations of $M$ are exactly the integral solutions of the systems
  $\delta x - \beta y = d$, $f x - g y = M / d$, $d$ a divisor of $M$; each system has at most one solution (Cramer's
  rule), so there are finitely many representations when the determinant is nonzero.
* `art215_I_implicates_iff`, `art215_I_transformations`: $m(gx+hy)^2$ implicates $M(GX+HY)^2$ iff
  $M = m e^2$, and the transformations are listed.
* `art215_II_transformations`, `art215_II_implicates_iff`: for $f$ of nonzero determinant, $f$
  implicates $M(GX+HY)^2$ iff $f$ represents $M$, and the transformations are $(G\xi, H\xi, G\upsilon, H\upsilon)$.

Conventions: `subst α β γ δ f` is $f(\alpha X + \beta Y, \gamma X + \delta Y)$, so Gauss's transformation
$(\alpha, \beta, \gamma, \delta)$ ($x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$) is the argument order of
`subst`. Everything here is proved unconditionally; no input structures are needed.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Art. 212 -/

/-- **Factorization of a form of square determinant (Gauss, *Disq. Arith.* Art. 212):
if $b^2 - ac = h^2$ then there are integers $\delta, \beta, f, g$ with
$a x^2 + 2bxy + cy^2 = (\delta x - \beta y)(f x - g y)$ for all $x, y$.** Gauss obtains the factorization by passing
to a properly equivalent $(A, h, 0)$ (Art. 206); here it is proved directly: for $a = 0$ the form is $y(2bx + cy)$;
for $a \ne 0$ write $a = a_1 k$, $b + h = p k$ with $k = \gcd(a, b + h)$ and $\gcd(a_1, p) = 1$, then
$a_1 \mid b - h$ and the form is $(a_1 x + p y)(k x + q_1 y)$ with $b - h = a_1 q_1$. No hypothesis on the sign of $h$. -/
@[kb "gauss1801" "Art. 212"]
theorem art212_factorization {a b c h : ℤ} (hd : gaussDet a b c = h ^ 2) :
    ∃ δ β f g : ℤ, ∀ x y : ℤ,
      a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y) := by
  simp only [gaussDet] at hd
  by_cases ha : a = 0
  · subst ha
    exact ⟨0, -1, 2 * b, -c, fun x y => by ring⟩
  · have hpos : 0 < Int.gcd a (b + h) := Int.gcd_pos_of_ne_zero_left _ ha
    obtain ⟨k, a1, p, hk0, hcop, ha1, hp⟩ := Int.exists_gcd_one' hpos
    have hk : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have ha1' : a1 ≠ 0 := by
      rintro rfl
      apply ha
      rw [ha1]; ring
    have hq : p * (b - h) = a1 * c := by
      apply mul_right_cancel₀ hk
      have h0 : (b + h) * (b - h) = a * c := by linear_combination hd
      linear_combination h0 - (b - h) * hp + c * ha1
    have hcop' : IsCoprime a1 p := Int.isCoprime_iff_gcd_eq_one.2 hcop
    have hdvd : a1 ∣ b - h := hcop'.dvd_of_dvd_mul_left (Dvd.intro c hq.symm)
    obtain ⟨q1, hq1⟩ := hdvd
    have hc : c = p * q1 := by
      apply mul_left_cancel₀ ha1'
      linear_combination (-1) * hq + p * hq1
    refine ⟨a1, -p, k, -q1, fun x y => ?_⟩
    linear_combination x ^ 2 * ha1 + x * y * (hq1 + hp) + y ^ 2 * hc

/-- **The determinant of a factored form (Art. 212):** if $a x^2 + 2bxy + cy^2 = (\delta x - \beta y)(f x - g y)$
for all $x, y$ then $(\delta g - \beta f)^2 = 4\,(b^2 - ac)$; in particular $\delta g - \beta f \ne 0$ iff the
determinant is nonzero. -/
theorem art212_factor_det {a b c δ β f g : ℤ}
    (hfac : ∀ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y)) :
    (δ * g - β * f) ^ 2 = 4 * gaussDet a b c := by
  have h1 := hfac 1 0
  have h2 := hfac 0 1
  have h3 := hfac 1 1
  have ha : a = δ * f := by linear_combination h1
  have hc : c = β * g := by linear_combination h2
  have hb : 2 * b = -(δ * g + β * f) := by linear_combination h3 - ha - hc
  simp only [gaussDet]
  linear_combination (-(2 * b - (δ * g + β * f))) * hb + 4 * c * ha + 4 * δ * f * hc

/-- **Representations of $0$ by a form of square determinant (Gauss, *Disq. Arith.* Art. 212, case $M = 0$;
the historical sources): given the factorization $a x^2 + 2bxy + cy^2 = (\delta x - \beta y)(f x - g y)$
(`art212_factorization`), the form vanishes at $(x, y)$ iff $\delta x = \beta y$ or $f x = g y$** (two lines). -/
@[kb "gauss1801" "Art. 212"]
theorem art212_zero_iff {a b c δ β f g : ℤ}
    (hfac : ∀ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y))
    (x y : ℤ) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = 0 ↔ δ * x = β * y ∨ f * x = g * y := by
  rw [hfac x y, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- **Representations of $M \ne 0$ by a form of square determinant (Gauss, *Disq. Arith.* Art. 212; the historical sources
): given the factorization $(\delta x - \beta y)(f x - g y)$, the form takes the value $M$ at $(x, y)$
iff there is a divisor $d$ of $M$ with $\delta x - \beta y = d$ and $f x - g y = M / d$.** Divisors are taken
positive and negative. -/
@[kb "gauss1801" "Art. 212"]
theorem art212_represent_iff {a b c δ β f g M : ℤ} (hM : M ≠ 0)
    (hfac : ∀ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y))
    (x y : ℤ) :
    a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = M ↔
      ∃ d : ℤ, d ∣ M ∧ δ * x - β * y = d ∧ f * x - g * y = M / d := by
  rw [hfac x y]
  constructor
  · intro h
    have hd : δ * x - β * y ≠ 0 := by
      intro h0
      apply hM
      rw [← h, h0, zero_mul]
    refine ⟨δ * x - β * y, ⟨f * x - g * y, h.symm⟩, rfl, ?_⟩
    rw [← h]
    exact (Int.mul_ediv_cancel_left _ hd).symm
  · rintro ⟨d, hdM, h1, h2⟩
    rw [h1, h2]
    exact Int.mul_ediv_cancel' hdM

/-- **The set of representations of $M \ne 0$ as a union over divisors (Gauss, *Disq. Arith.* Art. 212; the historical sources
):** the set of integral $(x, y)$ with $a x^2 + 2bxy + cy^2 = M$ equals the union, over the divisors
$d$ of $M$, of the solution sets of $\delta x - \beta y = d$, $f x - g y = M / d$. -/
@[kb "gauss1801" "Art. 212"]
theorem art212_represent_set {a b c δ β f g M : ℤ} (hM : M ≠ 0)
    (hfac : ∀ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y)) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + 2 * b * p.1 * p.2 + c * p.2 ^ 2 = M} =
      ⋃ d ∈ {d : ℤ | d ∣ M},
        {p : ℤ × ℤ | δ * p.1 - β * p.2 = d ∧ f * p.1 - g * p.2 = M / d} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  exact art212_represent_iff hM hfac x y

/-- **Cramer's rule for the system of Art. 212:** if $\delta x - \beta y = d$ and $f x - g y = e$ then
$(\delta g - \beta f)\,x = g d - \beta e$ and $(\delta g - \beta f)\,y = f d - \delta e$; so when
$\delta g - \beta f \ne 0$ the system has at most one solution, namely this rational one (the historical sources
). -/
theorem art212_cramer {δ β f g d e x y : ℤ} (h1 : δ * x - β * y = d) (h2 : f * x - g * y = e) :
    (δ * g - β * f) * x = g * d - β * e ∧ (δ * g - β * f) * y = f * d - δ * e :=
  ⟨by linear_combination g * h1 - β * h2, by linear_combination f * h1 - δ * h2⟩

private theorem abs_le_of_mul_eq {d e M : ℤ} (hM : M ≠ 0) (h : d * e = M) : |d| ≤ |M| ∧ |e| ≤ |M| := by
  have hd : d ≠ 0 := by rintro rfl; apply hM; rw [← h]; ring
  have he : e ≠ 0 := by rintro rfl; apply hM; rw [← h]; ring
  have h1 : 1 ≤ |d| := Int.one_le_abs hd
  have h2 : 1 ≤ |e| := Int.one_le_abs he
  have hm : |M| = |d| * |e| := by rw [← h, abs_mul]
  constructor
  · rw [hm]; exact le_mul_of_one_le_right (abs_nonneg _) h2
  · rw [hm]; exact le_mul_of_one_le_left (abs_nonneg _) h1

/-- **Finiteness of the set of representations (Gauss, *Disq. Arith.* Art. 212): a form
of nonzero square determinant represents $M \ne 0$ in only finitely many ways.** Given the factorization of
`art212_factorization`; each system $\delta x - \beta y = d$, $f x - g y = M/d$ has at most one solution
($\delta g - \beta f \ne 0$ by `art212_factor_det`), and $d$ runs over the finitely many divisors of $M$. -/
@[kb "gauss1801" "Art. 212"]
theorem art212_represent_finite {a b c δ β f g M : ℤ} (hM : M ≠ 0) (hdet : gaussDet a b c ≠ 0)
    (hfac : ∀ x y : ℤ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 = (δ * x - β * y) * (f * x - g * y)) :
    {p : ℤ × ℤ | a * p.1 ^ 2 + 2 * b * p.1 * p.2 + c * p.2 ^ 2 = M}.Finite := by
  have hΔ : δ * g - β * f ≠ 0 := by
    intro h0
    have := art212_factor_det hfac
    rw [h0] at this
    apply hdet
    linarith
  have hbox : (Set.Icc (-|M|) |M| ×ˢ Set.Icc (-|M|) |M|).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine Set.Finite.of_injOn (f := fun p : ℤ × ℤ => (δ * p.1 - β * p.2, f * p.1 - g * p.2))
    (t := Set.Icc (-|M|) |M| ×ˢ Set.Icc (-|M|) |M|) ?_ ?_ hbox
  · intro p hp
    have hp' : (δ * p.1 - β * p.2) * (f * p.1 - g * p.2) = M := by
      rw [← hfac]; exact hp
    obtain ⟨h1, h2⟩ := abs_le_of_mul_eq hM hp'
    exact ⟨abs_le.1 h1, abs_le.1 h2⟩
  · intro p _ q _ hpq
    have hpq' := Prod.mk.injEq _ _ _ _ ▸ hpq
    obtain ⟨h1, h2⟩ := hpq'
    have e1 : (δ * g - β * f) * (p.1 - q.1) = 0 := by linear_combination g * h1 - β * h2
    have e2 : (δ * g - β * f) * (p.2 - q.2) = 0 := by linear_combination f * h1 - δ * h2
    have e1' := sub_eq_zero.1 ((mul_eq_zero.1 e1).resolve_left hΔ)
    have e2' := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hΔ)
    exact Prod.ext e1' e2'

/-! ### Art. 215 -/

/-- **The form $m(gx + hy)^2$ (Gauss, *Disq. Arith.* Art. 215):** the form $(m g^2, m g h, m h^2)$ of determinant
$0$, $x, y \mapsto m (g x + h y)^2$. -/
@[kb "gauss1801" "Art. 215"]
def gaussLinearSquare (m g h : ℤ) : BinQF := gaussForm (m * g ^ 2) (m * g * h) (m * h ^ 2)

/-- **Values of $m(gx+hy)^2$:** $\text{gaussLinearSquare}(m, g, h)(x, y) = m (g x + h y)^2$. -/
theorem eval_gaussLinearSquare (m g h x y : ℤ) :
    (gaussLinearSquare m g h).eval x y = m * (g * x + h * y) ^ 2 := by
  unfold gaussLinearSquare
  rw [eval_gaussForm]; ring

/-- **Substitution into $m(gx+hy)^2$:** the substitution $(\alpha, \beta, \gamma, \delta)$ carries $m(gx+hy)^2$ to
$m\,(p X + q Y)^2$ with $p = g\alpha + h\gamma$, $q = g\beta + h\delta$. -/
theorem subst_gaussLinearSquare (m g h α β γ δ : ℤ) :
    subst α β γ δ (gaussLinearSquare m g h) = gaussLinearSquare m (g * α + h * γ) (g * β + h * δ) := by
  apply ext_eval
  intro x y
  simp only [eval_subst, eval_gaussLinearSquare]
  ring

/-- **Equality of two forms $m(px+qy)^2$ and $M(Gx+Hy)^2$ in coefficients.** -/
theorem gaussLinearSquare_eq_iff {m M p q G H : ℤ} :
    gaussLinearSquare m p q = gaussLinearSquare M G H ↔
      m * p ^ 2 = M * G ^ 2 ∧ m * p * q = M * G * H ∧ m * q ^ 2 = M * H ^ 2 := by
  constructor
  · intro h
    exact gaussForm_inj h
  · rintro ⟨h1, h2, h3⟩
    unfold gaussLinearSquare
    rw [h1, h2, h3]

/-- The sign analysis behind Art. 215 I: if $p^2 = e^2G^2$, $pq = e^2GH$, $q^2 = e^2H^2$ with $e \ne 0$ then
$(p, q) = \pm e\,(G, H)$ with one common sign. -/
private theorem sq_sign_aux {p q G H e : ℤ} (he : e ≠ 0) (h1 : p ^ 2 = e ^ 2 * G ^ 2)
    (h2 : p * q = e ^ 2 * G * H) (h3 : q ^ 2 = e ^ 2 * H ^ 2) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ p = s * e * G ∧ q = s * e * H := by
  have hp : p = e * G ∨ p = -(e * G) := sq_eq_sq_iff_eq_or_eq_neg.1 (by linear_combination h1)
  have hq : q = e * H ∨ q = -(e * H) := sq_eq_sq_iff_eq_or_eq_neg.1 (by linear_combination h3)
  have he2 : e ^ 2 ≠ 0 := pow_ne_zero 2 he
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact ⟨1, Or.inl rfl, by linear_combination hp, by linear_combination hq⟩
  · have h4 : e ^ 2 * (2 * (G * H)) = 0 := by rw [hp, hq] at h2; linear_combination -h2
    have h5 : G * H = 0 := by
      have := (mul_eq_zero.1 h4).resolve_left he2
      linarith
    rcases mul_eq_zero.1 h5 with hG | hH
    · exact ⟨-1, Or.inr rfl, by rw [hp, hG]; ring, by linear_combination hq⟩
    · exact ⟨1, Or.inl rfl, by linear_combination hp, by rw [hq, hH]; ring⟩
  · have h4 : e ^ 2 * (2 * (G * H)) = 0 := by rw [hp, hq] at h2; linear_combination -h2
    have h5 : G * H = 0 := by
      have := (mul_eq_zero.1 h4).resolve_left he2
      linarith
    rcases mul_eq_zero.1 h5 with hG | hH
    · exact ⟨1, Or.inl rfl, by rw [hp, hG]; ring, by linear_combination hq⟩
    · exact ⟨-1, Or.inr rfl, by linear_combination hp, by rw [hq, hH]; ring⟩
  · exact ⟨-1, Or.inr rfl, by linear_combination hp, by linear_combination hq⟩

/-- The core of Art. 215 I: if $m p^2 = M G^2$, $m p q = M G H$, $m q^2 = M H^2$ with $m \ne 0$ and $G, H$ coprime,
then $(p, q) = e\,(G, H)$ and $M = m e^2$ for an integer $e$. -/
private theorem implicates_aux {m M G H p q : ℤ} (hm : m ≠ 0) (hGH : IsCoprime G H)
    (h1 : m * p ^ 2 = M * G ^ 2) (h2 : m * p * q = M * G * H) (h3 : m * q ^ 2 = M * H ^ 2) :
    ∃ e : ℤ, p = G * e ∧ q = H * e ∧ M = m * e ^ 2 := by
  obtain ⟨u0, v0, huv⟩ := hGH
  have h0 : m * (p * H - q * G) ^ 2 = 0 := by
    linear_combination H ^ 2 * h1 - 2 * G * H * h2 + G ^ 2 * h3
  have hz : p * H - q * G = 0 :=
    pow_eq_zero_iff (two_ne_zero) |>.1 ((mul_eq_zero.1 h0).resolve_left hm)
  have hpe : p = G * (u0 * p + v0 * q) := by linear_combination (-p) * huv + v0 * hz
  have hqe : q = H * (u0 * p + v0 * q) := by linear_combination (-q) * huv - u0 * hz
  refine ⟨u0 * p + v0 * q, hpe, hqe, ?_⟩
  generalize u0 * p + v0 * q = e at hpe hqe
  subst hpe hqe
  have hne : G ^ 2 + H ^ 2 ≠ 0 := by
    intro h5
    have hG : G = 0 := by nlinarith [sq_nonneg G, sq_nonneg H]
    have hH : H = 0 := by nlinarith [sq_nonneg G, sq_nonneg H]
    rw [hG, hH] at huv
    simp at huv
  have h6 : (G ^ 2 + H ^ 2) * (M - m * e ^ 2) = 0 := by linear_combination (-1) * h1 + (-1) * h3
  have := (mul_eq_zero.1 h6).resolve_left hne
  linarith

/-- **Art. 215 I, implication of forms of determinant $0$ (Gauss, *Disq. Arith.* Art. 215 I; the historical sources
): for $m \ne 0$, $g, h$ coprime and $G, H$ coprime, the form $m(gx+hy)^2$ implicates
$M(GX+HY)^2$ (some integral substitution carries the first to the second) iff $M = m e^2$ for an integer $e$**,
i.e. iff $m \mid M$ and $M/m$ is a perfect square. Proved unconditionally; the hypothesis $M \ne 0$ of the source
is not needed for this part. -/
@[kb "gauss1801" "Art. 215 I"]
theorem art215_I_implicates_iff {m M g h G H : ℤ} (hm : m ≠ 0) (hgh : IsCoprime g h) (hGH : IsCoprime G H) :
    (∃ α β γ δ : ℤ, subst α β γ δ (gaussLinearSquare m g h) = gaussLinearSquare M G H) ↔
      ∃ e : ℤ, M = m * e ^ 2 := by
  constructor
  · rintro ⟨α, β, γ, δ, hT⟩
    rw [subst_gaussLinearSquare, gaussLinearSquare_eq_iff] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    obtain ⟨e, -, -, he⟩ := implicates_aux hm hGH h1 h2 h3
    exact ⟨e, he⟩
  · rintro ⟨e, hM⟩
    obtain ⟨u, v, hb⟩ := hgh
    refine ⟨e * G * u, e * H * u, e * G * v, e * H * v, ?_⟩
    have hp : g * (e * G * u) + h * (e * G * v) = e * G := by linear_combination e * G * hb
    have hq : g * (e * H * u) + h * (e * H * v) = e * H := by linear_combination e * H * hb
    rw [subst_gaussLinearSquare, hp, hq, gaussLinearSquare_eq_iff]
    subst hM
    exact ⟨by ring, by ring, by ring⟩

/-- **Art. 215 I, the transformations (Gauss, *Disq. Arith.* Art. 215 I): let
$M = m e^2$ with $m, e \ne 0$ and $u g + v h = 1$ (Gauss's $\mathfrak g, \mathfrak h$ are $u, v$). The substitution
$(\alpha, \beta, \gamma, \delta)$ carries $m(gx+hy)^2$ to $M(GX+HY)^2$ iff for a sign $s = \pm 1$ and integers
$z, z'$:**
$$\alpha = s e G u + h z,\quad \gamma = s e G v - g z,\quad \beta = s e H u + h z',\quad \delta = s e H v - g z'.$$
The sign $s$ is common to the four coefficients, as in the source's $\pm$ (the source's rendering does not say so
explicitly). Coprimality of $G, H$ is not needed. -/
@[kb "gauss1801" "Art. 215 I"]
theorem art215_I_transformations {m M g h G H e u v α β γ δ : ℤ} (hm : m ≠ 0) (hM : M = m * e ^ 2) (he : e ≠ 0)
    (hb : u * g + v * h = 1) :
    subst α β γ δ (gaussLinearSquare m g h) = gaussLinearSquare M G H ↔
      ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∃ z z' : ℤ,
        α = s * e * G * u + h * z ∧ γ = s * e * G * v - g * z ∧
        β = s * e * H * u + h * z' ∧ δ = s * e * H * v - g * z' := by
  have hgh : IsCoprime g h := ⟨u, v, hb⟩
  constructor
  · intro hT
    rw [subst_gaussLinearSquare, gaussLinearSquare_eq_iff] at hT
    obtain ⟨h1, h2, h3⟩ := hT
    subst hM
    have k1 : (g * α + h * γ) ^ 2 = e ^ 2 * G ^ 2 := mul_left_cancel₀ hm (by linear_combination h1)
    have k2 : (g * α + h * γ) * (g * β + h * δ) = e ^ 2 * G * H :=
      mul_left_cancel₀ hm (by linear_combination h2)
    have k3 : (g * β + h * δ) ^ 2 = e ^ 2 * H ^ 2 := mul_left_cancel₀ hm (by linear_combination h3)
    obtain ⟨s, hs, hp, hq⟩ := sq_sign_aux he k1 k2 k3
    have h₀ : g * (s * e * G * u) + h * (s * e * G * v) = s * e * G := by
      linear_combination s * e * G * hb
    have h₀' : g * (s * e * H * u) + h * (s * e * H * v) = s * e * H := by
      linear_combination s * e * H * hb
    obtain ⟨z, hz1, hz2⟩ := (art215_III_solutions hgh h₀ α γ).1 hp
    obtain ⟨z', hz1', hz2'⟩ := (art215_III_solutions hgh h₀' β δ).1 hq
    exact ⟨s, hs, z, z', by rw [hz1]; ring, by rw [hz2]; ring, by rw [hz1']; ring, by rw [hz2']; ring⟩
  · rintro ⟨s, hs, z, z', h1, h2, h3, h4⟩
    have hp : g * α + h * γ = s * e * G := by
      rw [h1, h2]; linear_combination s * e * G * hb
    have hq : g * β + h * δ = s * e * H := by
      rw [h3, h4]; linear_combination s * e * H * hb
    rw [subst_gaussLinearSquare, hp, hq, gaussLinearSquare_eq_iff]
    subst hM
    rcases hs with rfl | rfl <;> exact ⟨by ring, by ring, by ring⟩

/-- A substitution of the form $(G\xi, H\xi, G\upsilon, H\upsilon)$ carries $f$ to $f(\xi, \upsilon)\,(GX + HY)^2$. -/
theorem subst_gaussForm_linear (a b c G H ξ υ : ℤ) :
    subst (G * ξ) (H * ξ) (G * υ) (H * υ) (gaussForm a b c) =
      gaussLinearSquare (a * ξ ^ 2 + 2 * b * ξ * υ + c * υ ^ 2) G H := by
  apply ext_eval
  intro x y
  simp only [eval_subst, eval_gaussForm, eval_gaussLinearSquare]
  ring

/-- Auxiliary step of Art. 215 II: if $G \ne 0$, $\alpha\delta = \beta\gamma$ and the first two coefficient
equations hold then $G\beta = H\alpha$ and $G\delta = H\gamma$. -/
private theorem II_aux {a b c α β γ δ G H M : ℤ} (hM : M ≠ 0) (hG : G ≠ 0) (hD : α * δ - β * γ = 0)
    (hP : a * α ^ 2 + 2 * b * α * γ + c * γ ^ 2 = M * G ^ 2)
    (hQ : a * α * β + b * (α * δ + β * γ) + c * γ * δ = M * G * H) :
    G * β = H * α ∧ G * δ = H * γ := by
  have hB : (a * α + b * γ) * (G * β - H * α) + (b * α + c * γ) * (G * δ - H * γ) = 0 := by
    linear_combination G * hQ - H * hP
  have hMG : M * G ^ 2 ≠ 0 := mul_ne_zero hM (pow_ne_zero 2 hG)
  have hx : (G * β - H * α) * (M * G ^ 2) = 0 := by
    linear_combination α * hB - (b * α + c * γ) * G * hD - (G * β - H * α) * hP
  have hy : (G * δ - H * γ) * (M * G ^ 2) = 0 := by
    linear_combination γ * hB + (a * α + b * γ) * G * hD - (G * δ - H * γ) * hP
  have hx' := sub_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right hMG)
  have hy' := sub_eq_zero.1 ((mul_eq_zero.1 hy).resolve_right hMG)
  exact ⟨hx', hy'⟩

/-- **Art. 215 II, the transformations (Gauss, *Disq. Arith.* Art. 215 II): let $f = (a, b, c)$
have nonzero determinant, $M \ne 0$, and $G, H$ coprime. The substitution $(\alpha, \beta, \gamma, \delta)$ carries $f$
to $M(GX+HY)^2$ iff there is a representation $f(\xi, \upsilon) = M$ with
$(\alpha, \beta, \gamma, \delta) = (G\xi, H\xi, G\upsilon, H\upsilon)$.** Convention: `subst α β γ δ f` is
$f(\alpha X + \beta Y, \gamma X + \delta Y)$, so $x = \xi (GX + HY)$, $y = \upsilon (GX + HY)$, in the order of
Gauss's $(\alpha, \beta, \gamma, \delta)$. *Update:* the hypothesis $M \ne 0$ is needed for this description
(for $M = 0$ every substitution with proportional columns, e.g. $(1, 2, 0, 0)$ for $f = xy$, $G = 1$, $H = 0$,
carries $f$ to $0$ but is not of the stated shape); the source does not state it. -/
@[kb "gauss1801" "Art. 215 II"]
theorem art215_II_transformations {a b c M G H α β γ δ : ℤ} (hd : gaussDet a b c ≠ 0) (hM : M ≠ 0)
    (hGH : IsCoprime G H) :
    subst α β γ δ (gaussForm a b c) = gaussLinearSquare M G H ↔
      ∃ ξ υ : ℤ, a * ξ ^ 2 + 2 * b * ξ * υ + c * υ ^ 2 = M ∧
        α = G * ξ ∧ β = H * ξ ∧ γ = G * υ ∧ δ = H * υ := by
  constructor
  · intro hT
    have hT' := hT
    unfold gaussLinearSquare at hT'
    have hdet := (art215_det_implicated α β γ δ hT').1
    have hD : α * δ - β * γ = 0 := by
      have h0 : gaussDet (M * G ^ 2) (M * G * H) (M * H ^ 2) = 0 := by simp only [gaussDet]; ring
      rw [h0] at hdet
      have := (mul_eq_zero.1 hdet.symm).resolve_right hd
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    rw [subst_gaussForm] at hT'
    obtain ⟨hP, hQ, hR⟩ := gaussForm_inj hT'
    have hβδ : G * β = H * α ∧ G * δ = H * γ := by
      by_cases hG : G = 0
      · have hH : H ≠ 0 := by
          rintro rfl
          obtain ⟨u0, v0, huv⟩ := hGH
          rw [hG] at huv
          simp at huv
        have := II_aux (a := a) (b := b) (c := c) (α := β) (β := α) (γ := δ) (δ := γ) (G := H) (H := G)
          hM hH (by linear_combination -hD) hR (by linear_combination hQ)
        exact ⟨this.1.symm, this.2.symm⟩
      · exact II_aux hM hG hD hP hQ
    obtain ⟨hβ1, hδ1⟩ := hβδ
    obtain ⟨u0, v0, huv⟩ := hGH
    obtain ⟨ξ, hξ1, hξ2⟩ : ∃ ξ, α = G * ξ ∧ β = H * ξ :=
      ⟨u0 * α + v0 * β, by linear_combination (-α) * huv - v0 * hβ1,
        by linear_combination (-β) * huv + u0 * hβ1⟩
    obtain ⟨υ, hυ1, hυ2⟩ : ∃ υ, γ = G * υ ∧ δ = H * υ :=
      ⟨u0 * γ + v0 * δ, by linear_combination (-γ) * huv - v0 * hδ1,
        by linear_combination (-δ) * huv + u0 * hδ1⟩
    refine ⟨ξ, υ, ?_, hξ1, hξ2, hυ1, hυ2⟩
    subst hξ1 hξ2 hυ1 hυ2
    have hne : G ^ 2 + H ^ 2 ≠ 0 := by
      intro h5
      have hG : G = 0 := by nlinarith [sq_nonneg G, sq_nonneg H]
      have hH : H = 0 := by nlinarith [sq_nonneg G, sq_nonneg H]
      rw [hG, hH] at huv
      simp at huv
    have h6 : (G ^ 2 + H ^ 2) * (a * ξ ^ 2 + 2 * b * ξ * υ + c * υ ^ 2 - M) = 0 := by
      linear_combination hP + hR
    have := (mul_eq_zero.1 h6).resolve_left hne
    linarith
  · rintro ⟨ξ, υ, hr, rfl, rfl, rfl, rfl⟩
    rw [subst_gaussForm_linear, hr]

/-- **Art. 215 II, implication by a form of nonzero determinant (Gauss, *Disq. Arith.* Art. 215 II; the historical sources
): if $f = (a, b, c)$ has determinant $\ne 0$ and $G, H$ are coprime then $f$ implicates
$M(GX+HY)^2$ iff $M$ is represented by $f$** (some integers $\xi, \upsilon$ with $f(\xi, \upsilon) = M$). Here
$M = 0$ is allowed (it is represented by $(0, 0)$, and implicated by the zero substitution); the description of all
transformations is `art215_II_transformations` (for $M \ne 0$). -/
@[kb "gauss1801" "Art. 215 II"]
theorem art215_II_implicates_iff {a b c M G H : ℤ} (hd : gaussDet a b c ≠ 0) (hGH : IsCoprime G H) :
    (∃ α β γ δ : ℤ, subst α β γ δ (gaussForm a b c) = gaussLinearSquare M G H) ↔
      ∃ ξ υ : ℤ, a * ξ ^ 2 + 2 * b * ξ * υ + c * υ ^ 2 = M := by
  constructor
  · rintro ⟨α, β, γ, δ, hT⟩
    by_cases hM : M = 0
    · exact ⟨0, 0, by rw [hM]; ring⟩
    · obtain ⟨ξ, υ, hr, -⟩ := (art215_II_transformations hd hM hGH).1 hT
      exact ⟨ξ, υ, hr⟩
  · rintro ⟨ξ, υ, hr⟩
    exact ⟨G * ξ, H * ξ, G * υ, H * υ, by rw [subst_gaussForm_linear, hr]⟩

end QuadFormsKB.Historical.Gauss
