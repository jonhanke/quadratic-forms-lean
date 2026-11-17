import QuadFormsKB.Historical.Gauss.DuplicationSubstitution

/-!
# Gauss's relation $n^2 = d/D$ and the transport of compositions by substitutions
(Disquisitiones Arithmeticae, Arts. 235, 237, 238, 287 I)

(Art. 237) (Art. 238) (Art. 287 I, without the
hypothesis $n = n'$) and the loose end **a recorded loose end** (Art. 235, $n^2 = d/D$).

Indices are $0$-based: Gauss's $p, p', p'', p'''$ are `p 0, p 1, p 2, p 3`. The bilinear substitution is
$X = p_0\,xx' + p_1\,xy' + p_2\,yx' + p_3\,yy'$ (`bilin`), and $f = a x^2 + b xy + cy^2$,
$f' = a'x^2 + b'xy + c'y^2$ in the library's coefficients (Gauss's $2b$, $2b'$).

## What is proved

* `disc_mul_sq_of_rel_first` and `disc_mul_sq_of_rel_second` (Art. 235, $n^2 = d/D$): if $F$ is transformed into
  $f f'$ and the relations $Q = a'n$, $R + S = b'n$, $T = c'n$ hold, then $\operatorname{disc} f = n^2 \operatorname{disc} F$
  whenever $f'$ is not the zero form; if $P = an'$, $R - S = bn'$, $U = cn'$ hold, then
  $\operatorname{disc} f' = n'^2 \operatorname{disc} F$ whenever $f$ is not the zero form. No positivity and no
  coprimality are needed.
  `isCompounded_disc` is the corollary for `IsCompounded`.
* `art287_eq_of_compounded_self'` and `isCompounded_self_middle` (Art. 287 I): the hypothesis $n = n'$ of
  `art287_eq_of_compounded_self` is removed; it follows from $n^2 = n'^2$ and positivity when $\operatorname{disc} F \ne 0$.
* `art237_transformsInto`, `art237_minors`, `art237_relations` (Art. 237): replacing $f'$ by a form $f''$ that
  $f'$ contains.
* `art238_transformsInto`, `art238_minors`, `art238_relations`, `art238_isCompounded_one` (Art. 238): replacing $F$ by a
  form $F'$ that goes into $F$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-! ### Art. 235: $n^2 = d/D$ -/

/-- **A form with a proportional linear substitution:** if $F(\alpha x + \beta y, \gamma x + \delta y) = k\, f(x, y)$
for all integers $x, y$, then $(\alpha\delta - \beta\gamma)^2 \operatorname{disc} F = k^2 \operatorname{disc} f$. -/
theorem sq_det_mul_disc_of_eval (F f : BinQF) (α β γ δ k : ℤ)
    (h : ∀ x y : ℤ, F.eval (α * x + β * y) (γ * x + δ * y) = k * f.eval x y) :
    (α * δ - β * γ) ^ 2 * F.disc = k ^ 2 * f.disc := by
  have hG : ∀ x y : ℤ, (subst α β γ δ F).eval x y = k * f.eval x y := by
    intro x y; rw [eval_subst]; exact h x y
  have h1 := hG 1 0
  have h2 := hG 0 1
  have h3 := hG 1 1
  simp only [eval_eq] at h1 h2 h3
  have ha : (subst α β γ δ F).a = k * f.a := by linear_combination h1
  have hc : (subst α β γ δ F).c = k * f.c := by linear_combination h2
  have hb : (subst α β γ δ F).b = k * f.b := by linear_combination h3 - h1 - h2
  have := disc_subst α β γ δ F
  simp only [disc, ha, hb, hc] at this ⊢
  linear_combination -this

/-- A form with a nonzero discriminant takes a nonzero value at some integer point (it is not the zero form). -/
theorem exists_eval_ne_zero_of_disc_ne_zero {f : BinQF} (h : f.disc ≠ 0) : ∃ x y : ℤ, f.eval x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  simp only [eval_eq] at h1 h2 h3
  apply h
  have ha : f.a = 0 := by linarith
  have hc : f.c = 0 := by linarith
  have hb : f.b = 0 := by linarith
  simp [disc, ha, hb, hc]

/-- **Gauss, *Disq. Arith.* Art. 235, $n^2 = d/D$ for the first factor:** if $F$ is
transformed into $f f'$ by $(p, q)$ and $Q = a'n$, $R + S = b'n$, $T = c'n$ (the relations of Art. 235 involving
$f'$), then $\operatorname{disc} f = n^2 \operatorname{disc} F$ (Gauss's $d = Dn^2$, with discriminants, i.e. four times
the determinants, on both sides), provided $f'$ is not the zero form (`∃ x y, f'.eval x y ≠ 0`; this holds, for
instance, when $\operatorname{disc} f' \ne 0$, `exists_eval_ne_zero_of_disc_ne_zero`). No positivity of $n$ and no
coprimality of the six numbers is needed. The proof: for fixed $(x', y')$ the substitution
$(x, y) \mapsto (X, Y)$ is linear with determinant $n f'(x', y')$ and carries $F$ to $f'(x', y') f$. -/
@[kb "gauss1801" "Art. 235"]
theorem disc_mul_sq_of_rel_first {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q) {n : ℚ}
    (h3 : (minors p q 1 : ℚ) = f'.a * n) (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n)
    (h5 : (minors p q 4 : ℚ) = f'.c * n) (hf' : ∃ x y : ℤ, f'.eval x y ≠ 0) :
    (f.disc : ℚ) = n ^ 2 * F.disc := by
  obtain ⟨x', y', hv⟩ := hf'
  simp only [minors, Matrix.cons_val] at h3 h4 h5
  push_cast at h3 h4 h5
  have hdet : (((p 0 * x' + p 1 * y') * (q 2 * x' + q 3 * y') - (p 2 * x' + p 3 * y') * (q 0 * x' + q 1 * y') : ℤ) : ℚ)
      = n * (f'.eval x' y' : ℤ) := by
    rw [eval_eq]; push_cast
    linear_combination (x' : ℚ) ^ 2 * h3 + (x' : ℚ) * y' * h4 + (y' : ℚ) ^ 2 * h5
  have hmain := sq_det_mul_disc_of_eval F f (p 0 * x' + p 1 * y') (p 2 * x' + p 3 * y')
    (q 0 * x' + q 1 * y') (q 2 * x' + q 3 * y') (f'.eval x' y') (by
      intro x y
      have e1 : (p 0 * x' + p 1 * y') * x + (p 2 * x' + p 3 * y') * y = p 0 * x * x' + p 1 * x * y' + p 2 * y * x' + p 3 * y * y' := by ring
      have e2 : (q 0 * x' + q 1 * y') * x + (q 2 * x' + q 3 * y') * y = q 0 * x * x' + q 1 * x * y' + q 2 * y * x' + q 3 * y * y' := by ring
      rw [e1, e2]
      have hb := hT x y x' y'
      simp only [bilin] at hb
      rw [hb]; ring)
  have hmainQ := congrArg (fun z : ℤ => (z : ℚ)) hmain
  simp only [Int.cast_mul, Int.cast_pow] at hmainQ
  rw [hdet] at hmainQ
  have hk : ((f'.eval x' y' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hk)
  linear_combination -hmainQ

/-- **Gauss, *Disq. Arith.* Art. 235, $n'^2 = d'/D$ for the second factor:** if $F$ is
transformed into $f f'$ by $(p, q)$ and $P = an'$, $R - S = bn'$, $U = cn'$, then
$\operatorname{disc} f' = n'^2 \operatorname{disc} F$, provided $f$ is not the zero form. Same proof as
`disc_mul_sq_of_rel_first` with the roles of $(x, y)$ and $(x', y')$ exchanged; the determinant is now
$n' f(x, y)$. -/
@[kb "gauss1801" "Art. 235"]
theorem disc_mul_sq_of_rel_second {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q) {n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (hf : ∃ x y : ℤ, f.eval x y ≠ 0) :
    (f'.disc : ℚ) = n' ^ 2 * F.disc := by
  obtain ⟨x, y, hv⟩ := hf
  simp only [minors, Matrix.cons_val] at h0 h1 h2
  push_cast at h0 h1 h2
  have hdet : (((p 0 * x + p 2 * y) * (q 1 * x + q 3 * y) - (p 1 * x + p 3 * y) * (q 0 * x + q 2 * y) : ℤ) : ℚ)
      = n' * (f.eval x y : ℤ) := by
    rw [eval_eq]; push_cast
    linear_combination (x : ℚ) ^ 2 * h0 + (x : ℚ) * y * h1 + (y : ℚ) ^ 2 * h2
  have hmain := sq_det_mul_disc_of_eval F f' (p 0 * x + p 2 * y) (p 1 * x + p 3 * y)
    (q 0 * x + q 2 * y) (q 1 * x + q 3 * y) (f.eval x y) (by
      intro x' y'
      have e1 : (p 0 * x + p 2 * y) * x' + (p 1 * x + p 3 * y) * y' = p 0 * x * x' + p 1 * x * y' + p 2 * y * x' + p 3 * y * y' := by ring
      have e2 : (q 0 * x + q 2 * y) * x' + (q 1 * x + q 3 * y) * y' = q 0 * x * x' + q 1 * x * y' + q 2 * y * x' + q 3 * y * y' := by ring
      rw [e1, e2]
      have hb := hT x y x' y'
      simp only [bilin] at hb
      rw [hb])
  have hmainQ := congrArg (fun z : ℤ => (z : ℚ)) hmain
  simp only [Int.cast_mul, Int.cast_pow] at hmainQ
  rw [hdet] at hmainQ
  have hk : ((f.eval x y : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hk)
  linear_combination -hmainQ

/-- **Gauss, *Disq. Arith.* Art. 235, $n^2 = d/D$, for a form compounded of two forms**: if
$F$ is compounded directly of $f$ and $f'$ (`IsCompounded`) and $f$, $f'$ have nonzero discriminants, then there are
rationals $n, n' > 0$ with $\operatorname{disc} f = n^2 \operatorname{disc} F$ and
$\operatorname{disc} f' = n'^2 \operatorname{disc} F$ (the same $n, n'$ as in the six relations, for the same
substitution; the existential in `IsCompounded` is repeated here with the transformation). -/
@[kb "gauss1801" "Art. 235"]
theorem isCompounded_disc {F f f' : BinQF} (h : IsCompounded F f f') (hf : f.disc ≠ 0) (hf' : f'.disc ≠ 0) :
    ∃ p q : Fin 4 → ℤ, TransformsInto F f f' p q ∧ ∃ n n' : ℚ, 0 < n ∧ 0 < n' ∧
      (f.disc : ℚ) = n ^ 2 * F.disc ∧ (f'.disc : ℚ) = n' ^ 2 * F.disc := by
  obtain ⟨p, q, hT, -, n, n', hn, hn', h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨p, q, hT, n, n', hn, hn',
    disc_mul_sq_of_rel_first hT h3 h4 h5 (exists_eval_ne_zero_of_disc_ne_zero hf'),
    disc_mul_sq_of_rel_second hT h0 h1 h2 (exists_eval_ne_zero_of_disc_ne_zero hf)⟩

/-! ### Art. 287 I without the hypothesis $n = n'$ -/

/-- **Gauss, *Disq. Arith.* Art. 287 I, without the hypothesis $n = n'$:** if
$F$, with $\operatorname{disc} F \ne 0$, is transformed into $f f$ by $(p, q)$ with coprime six numbers and the six
relations hold with **positive** rationals $n$ (for the second factor) and $n'$ (for the first), then $n = n'$ and
$p_1 = p_2$, $q_1 = q_2$. Gauss's argument for $n = n'$: $n^2 = d/D = n'^2$ (Art. 235, `disc_mul_sq_of_rel_first`,
`disc_mul_sq_of_rel_second`); that $f$ is not the zero form follows from the coprimality (otherwise all six numbers
vanish). This supersedes the restriction recorded in `art287_eq_of_compounded_self`. -/
@[kb "gauss1801" "Art. 287 I"]
theorem art287_eq_of_compounded_self' {F f : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f p q)
    (hcop : ∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) (hF : F.disc ≠ 0) {n n' : ℚ} (hn : 0 < n) (hn' : 0 < n')
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f.b * n) (h5 : (minors p q 4 : ℚ) = f.c * n) :
    n = n' ∧ p 1 = p 2 ∧ q 1 = q 2 := by
  have hf : ∃ x y : ℤ, f.eval x y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon 1 0
    have e2 := hcon 0 1
    have e3 := hcon 1 1
    simp only [eval_eq] at e1 e2 e3
    have ha : f.a = 0 := by linarith
    have hc : f.c = 0 := by linarith
    have hb : f.b = 0 := by linarith
    have hz : ∀ i, minors p q i = 0 := by
      have g0 : (minors p q 0 : ℚ) = 0 := by rw [h0]; simp [ha]
      have g5 : (minors p q 5 : ℚ) = 0 := by rw [h2]; simp [hc]
      have g1 : (minors p q 1 : ℚ) = 0 := by rw [h3]; simp [ha]
      have g4 : (minors p q 4 : ℚ) = 0 := by rw [h5]; simp [hc]
      have g23 : (minors p q 2 : ℚ) + minors p q 3 = 0 := by rw [h4]; simp [hb]
      have g2m3 : (minors p q 2 : ℚ) - minors p q 3 = 0 := by rw [h1]; simp [hb]
      intro i
      fin_cases i
      · exact_mod_cast g0
      · exact_mod_cast g1
      · have : (minors p q 2 : ℚ) = 0 := by linarith
        exact_mod_cast this
      · have : (minors p q 3 : ℚ) = 0 := by linarith
        exact_mod_cast this
      · exact_mod_cast g4
      · exact_mod_cast g5
    exact not_isUnit_zero (hcop 0 (fun i => by rw [hz i]))
  have e1 := disc_mul_sq_of_rel_first hT h3 h4 h5 hf
  have e2 := disc_mul_sq_of_rel_second hT h0 h1 h2 hf
  have hFq : (F.disc : ℚ) ≠ 0 := by exact_mod_cast hF
  have hsq : n ^ 2 = n' ^ 2 := by
    apply mul_right_cancel₀ hFq
    linear_combination -e1 + e2
  have hnn : n = n' := by
    have : (n - n') * (n + n') = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  subst hnn
  exact ⟨rfl, art287_eq_of_compounded_self hT hcop h0 h1 h2 h3 h4 h5⟩

/-- **Gauss, *Disq. Arith.* Art. 287 I, for `IsCompounded`:** if $F$ with
$\operatorname{disc} F \ne 0$ is compounded directly of $f$ with itself, then some bilinear substitution transforming
$F$ into $f f$ (whose six numbers are coprime and satisfy Gauss's relations) has $p_1 = p_2$ and $q_1 = q_2$. -/
@[kb "gauss1801" "Art. 287 I"]
theorem isCompounded_self_middle {F f : BinQF} (h : IsCompounded F f f) (hF : F.disc ≠ 0) :
    ∃ p q : Fin 4 → ℤ, TransformsInto F f f p q ∧ p 1 = p 2 ∧ q 1 = q 2 := by
  obtain ⟨p, q, hT, hcop, n, n', hn, hn', h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨p, q, hT, (art287_eq_of_compounded_self' hT hcop hF hn hn' h0 h1 h2 h3 h4 h5).2⟩

/-! ### Art. 237: replacing the second form by a form it contains -/

/-- **Gauss, *Disq. Arith.* Art. 237, the substitution:** if $F$ is transformed into
$f f'$ by $(p, q)$ and $f'' = f'(\alpha x + \beta y, \gamma x + \delta y)$ (`subst`; $f'$ contains $f''$), then $F$ is
transformed into $f f''$ by the bilinear substitution with coefficients
$(p_0\alpha + p_1\gamma,\ p_0\beta + p_1\delta,\ p_2\alpha + p_3\gamma,\ p_2\beta + p_3\delta)$ and the same with $q$
(Gauss's $p\alpha + p'\gamma$, $p\beta + p'\delta$, $p''\alpha + p'''\gamma$, $p''\beta + p'''\delta$ with $0$-based
indices; this is `transport` with the identity on the first factor). -/
@[kb "gauss1801" "Art. 237"]
theorem art237_transformsInto {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    (α β γ δ : ℤ) :
    TransformsInto F f (subst α β γ δ f')
      ![p 0 * α + p 1 * γ, p 0 * β + p 1 * δ, p 2 * α + p 3 * γ, p 2 * β + p 3 * δ]
      ![q 0 * α + q 1 * γ, q 0 * β + q 1 * δ, q 2 * α + q 3 * γ, q 2 * β + q 3 * δ] := by
  intro x y x' y'
  rw [eval_subst, ← hT x y (α * x' + β * y') (γ * x' + δ * y')]
  simp only [bilin, Matrix.cons_val]
  congr 1 <;> ring

/-- **Gauss, *Disq. Arith.* Art. 237, the new six numbers:** with
$e = \alpha\delta - \beta\gamma$ and $(P, Q, R, S, T, U)$ the six numbers of $(p, q)$, those of the substitution of
`art237_transformsInto` are $P_{\text{new}} = eP$, $U_{\text{new}} = eU$,
$R_{\text{new}} - S_{\text{new}} = e(R - S)$, and $(Q, R + S, T)$ transform like the coefficients $(a, b, c)$ of a form
under the substitution:
$Q_{\text{new}} = \alpha^2 Q + \alpha\gamma(R + S) + \gamma^2 T$,
$R_{\text{new}} + S_{\text{new}} = 2\alpha\beta Q + (\alpha\delta + \beta\gamma)(R + S) + 2\gamma\delta T$,
$T_{\text{new}} = \beta^2 Q + \beta\delta(R + S) + \delta^2 T$. -/
@[kb "gauss1801" "Art. 237"]
theorem art237_minors (p q : Fin 4 → ℤ) (α β γ δ : ℤ) :
    let m := minors ![p 0 * α + p 1 * γ, p 0 * β + p 1 * δ, p 2 * α + p 3 * γ, p 2 * β + p 3 * δ]
      ![q 0 * α + q 1 * γ, q 0 * β + q 1 * δ, q 2 * α + q 3 * γ, q 2 * β + q 3 * δ]
    m 0 = (α * δ - β * γ) * minors p q 0 ∧ m 5 = (α * δ - β * γ) * minors p q 5 ∧
    m 2 - m 3 = (α * δ - β * γ) * (minors p q 2 - minors p q 3) ∧
    m 1 = α ^ 2 * minors p q 1 + α * γ * (minors p q 2 + minors p q 3) + γ ^ 2 * minors p q 4 ∧
    m 2 + m 3 = 2 * α * β * minors p q 1 + (α * δ + β * γ) * (minors p q 2 + minors p q 3) +
      2 * γ * δ * minors p q 4 ∧
    m 4 = β ^ 2 * minors p q 1 + β * δ * (minors p q 2 + minors p q 3) + δ ^ 2 * minors p q 4 := by
  intro m
  simp only [m, minors, Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

/-- **Gauss, *Disq. Arith.* Art. 237, the relations:** if $F$ is transformed into $f f'$
by $(p, q)$ and the six relations of Art. 235 hold with $n, n'$, then for $f'' = f'(\alpha x + \beta y, \gamma x + \delta y)$
and $e = \alpha\delta - \beta\gamma$ the six relations hold for the new substitution of `art237_transformsInto` with
$f, f''$ and the numbers $n$ (for $f''$) and $n' e$ (for $f$):
$P_{\text{new}} = a\,(n'e)$, $R_{\text{new}} - S_{\text{new}} = b\,(n'e)$, $U_{\text{new}} = c\,(n'e)$,
$Q_{\text{new}} = a''n$, $R_{\text{new}} + S_{\text{new}} = b''n$, $T_{\text{new}} = c''n$.
So Gauss's "the analogue of $\Omega$ holds with $n'e$ in place of $n'$" is correct for the $f$-relations; the
$f''$-relations keep $n$ (consistently with $\operatorname{disc} f'' = e^2 \operatorname{disc} f' = (n'e)^2
\operatorname{disc} F$). Neither positivity nor coprimality is part of this statement: the sign of $n'e$ is that of
$e$. -/
@[kb "gauss1801" "Art. 237"]
theorem art237_relations {f f' : BinQF} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n) (h5 : (minors p q 4 : ℚ) = f'.c * n)
    (α β γ δ : ℤ) :
    let m := minors ![p 0 * α + p 1 * γ, p 0 * β + p 1 * δ, p 2 * α + p 3 * γ, p 2 * β + p 3 * δ]
      ![q 0 * α + q 1 * γ, q 0 * β + q 1 * δ, q 2 * α + q 3 * γ, q 2 * β + q 3 * δ]
    (m 0 : ℚ) = f.a * (n' * (α * δ - β * γ : ℤ)) ∧
    ((m 2 : ℚ) - m 3) = f.b * (n' * (α * δ - β * γ : ℤ)) ∧
    (m 5 : ℚ) = f.c * (n' * (α * δ - β * γ : ℤ)) ∧
    (m 1 : ℚ) = (subst α β γ δ f').a * n ∧
    ((m 2 : ℚ) + m 3) = (subst α β γ δ f').b * n ∧
    (m 4 : ℚ) = (subst α β γ δ f').c * n := by
  intro m
  obtain ⟨k0, k5, k1, k2, k3, k4⟩ := art237_minors p q α β γ δ
  have c0 := congrArg (fun z : ℤ => (z : ℚ)) k0
  have c5 := congrArg (fun z : ℤ => (z : ℚ)) k5
  have c1 := congrArg (fun z : ℤ => (z : ℚ)) k1
  have c2 := congrArg (fun z : ℤ => (z : ℚ)) k2
  have c3 := congrArg (fun z : ℤ => (z : ℚ)) k3
  have c4 := congrArg (fun z : ℤ => (z : ℚ)) k4
  simp only [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] at c0 c5 c1 c2 c3 c4
  simp only [a_subst, b_subst, c_subst]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, h0]; ring
  · rw [c1, h1]; ring
  · rw [c5, h2]; ring
  · rw [c2]; linear_combination (α : ℚ) ^ 2 * h3 + (α : ℚ) * γ * h4 + (γ : ℚ) ^ 2 * h5
  · rw [c3]; linear_combination 2 * (α : ℚ) * β * h3 + ((α : ℚ) * δ + β * γ) * h4 + 2 * (γ : ℚ) * δ * h5
  · rw [c4]; linear_combination (β : ℚ) ^ 2 * h3 + (β : ℚ) * δ * h4 + (δ : ℚ) ^ 2 * h5

/-! ### Art. 238: replacing $F$ by a form that goes into it -/

/-- **Gauss, *Disq. Arith.* Art. 238, the substitution:** if $F = F'(\alpha X + \beta Y,
\gamma X + \delta Y)$ (`subst α β γ δ F'`: $F'$ goes into $F$) and $F$ is transformed into $f f'$ by $(p, q)$, then
$F'$ is transformed into $f f'$ by $p^{\text{new}}_i = \alpha p_i + \beta q_i$,
$q^{\text{new}}_i = \gamma p_i + \delta q_i$ (componentwise; Gauss's $\alpha p + \beta q$, $\gamma p + \delta q$ and
the same for $p', \dots$, matching the convention of `subst`). -/
@[kb "gauss1801" "Art. 238"]
theorem art238_transformsInto {F' f f' : BinQF} {p q : Fin 4 → ℤ} (α β γ δ : ℤ)
    (hT : TransformsInto (subst α β γ δ F') f f' p q) :
    TransformsInto F' f f' (fun i => α * p i + β * q i) (fun i => γ * p i + δ * q i) := by
  intro x y x' y'
  rw [← hT x y x' y', eval_subst]
  simp only [bilin]
  congr 1 <;> ring

/-- **Gauss, *Disq. Arith.* Art. 238, the new six numbers:** the six numbers of
$(\alpha p + \beta q,\ \gamma p + \delta q)$ are $e = \alpha\delta - \beta\gamma$ times those of $(p, q)$. -/
@[kb "gauss1801" "Art. 238"]
theorem art238_minors (α β γ δ : ℤ) (p q : Fin 4 → ℤ) (i : Fin 6) :
    minors (fun i => α * p i + β * q i) (fun i => γ * p i + δ * q i) i = (α * δ - β * γ) * minors p q i := by
  fin_cases i <;> simp [minors] <;> ring

/-- **Gauss, *Disq. Arith.* Art. 238, the relations:** if the six relations of Art. 235
hold for $(p, q)$ with $n, n'$ then they hold for $(\alpha p + \beta q, \gamma p + \delta q)$, the same forms
$f, f'$, with $n e$ and $n' e$ ($e = \alpha\delta - \beta\gamma$). For $e > 0$ the signs of $n, n'$ are kept
("the same way"); for $e < 0$ both are reversed ("opposite ways"). -/
@[kb "gauss1801" "Art. 238"]
theorem art238_relations {f f' : BinQF} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n) (h5 : (minors p q 4 : ℚ) = f'.c * n)
    (α β γ δ : ℤ) :
    let m := minors (fun i => α * p i + β * q i) (fun i => γ * p i + δ * q i)
    (m 0 : ℚ) = f.a * (n' * (α * δ - β * γ : ℤ)) ∧ ((m 2 : ℚ) - m 3) = f.b * (n' * (α * δ - β * γ : ℤ)) ∧
    (m 5 : ℚ) = f.c * (n' * (α * δ - β * γ : ℤ)) ∧ (m 1 : ℚ) = f'.a * (n * (α * δ - β * γ : ℤ)) ∧
    ((m 2 : ℚ) + m 3) = f'.b * (n * (α * δ - β * γ : ℤ)) ∧ (m 4 : ℚ) = f'.c * (n * (α * δ - β * γ : ℤ)) := by
  intro m
  have c : ∀ i, (m i : ℚ) = ((α * δ - β * γ : ℤ) : ℚ) * minors p q i := by
    intro i; simp only [m]; rw [art238_minors]; push_cast; ring
  have c2 := c 2
  have c3 := c 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c 0, h0]; ring
  · rw [c2, c3]; linear_combination ((α * δ - β * γ : ℤ) : ℚ) * h1
  · rw [c 5, h2]; ring
  · rw [c 1, h3]; ring
  · rw [c2, c3]; linear_combination ((α * δ - β * γ : ℤ) : ℚ) * h4
  · rw [c 4, h5]; ring

/-- **Gauss, *Disq. Arith.* Art. 238, a form that goes into a compounded form by a
proper substitution is compounded in the same way:** if $F = F'(\alpha X + \beta Y, \gamma X + \delta Y)$ with
$\alpha\delta - \beta\gamma = 1$ and $F$ is compounded directly of $f, f'$, then so is $F'$ (the six numbers of the new
substitution equal the old ones, so coprimality and the relations with the same $n, n' > 0$ persist). For general
$e > 0$ see `art238_relations`: the six numbers are multiplied by $e$ and are no longer coprime unless $e = 1$. -/
@[kb "gauss1801" "Art. 238"]
theorem art238_isCompounded_one {F' f f' : BinQF} (α β γ δ : ℤ) (he : α * δ - β * γ = 1)
    (h : IsCompounded (subst α β γ δ F') f f') : IsCompounded F' f f' := by
  obtain ⟨p, q, hT, hcop, n, n', hn, hn', h0, h1, h2, h3, h4, h5⟩ := h
  have hm : ∀ i, minors (fun i => α * p i + β * q i) (fun i => γ * p i + δ * q i) i = minors p q i := by
    intro i; rw [art238_minors, he, one_mul]
  refine ⟨_, _, art238_transformsInto α β γ δ hT, ?_, n, n', hn, hn', ?_⟩
  · intro d hd; exact hcop d (fun i => by rw [← hm i]; exact hd i)
  · simp only [hm]; exact ⟨h0, h1, h2, h3, h4, h5⟩

end QuadFormsKB.Historical.Gauss
