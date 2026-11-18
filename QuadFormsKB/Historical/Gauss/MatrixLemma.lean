import QuadFormsKB.Historical.Gauss.CompositionTransitivity
import QuadFormsKB.Historical.Gauss.CompositionInvariance

/-!
# Gauss's matrix lemma (Art. 234) and its uses in Arts. 238-239

(Art. 234, the matrix lemma) (Art. 239, a form transformable into
$f f'$ in the same way as a compounded form properly contains it) and (Art. 238, end: combined
transitivity).

Indices are $0$-based: Gauss's $p, p', p'', p'''$ are `p 0, p 1, p 2, p 3`; the index $\lambda = 0, \dots, n$ of
Art. 234 runs over an arbitrary finite index type.

## What is proved

* `matrix_lemma` (Art. 234): the $2 \times 2$ minors of the integral matrix $N = (c; d)$ are $k \ne 0$ times those of
  $M = (a; b)$, and those of $M$ are coprime, then $N = TM$ with $\det T = k$. The statement in the historical sources omits $k \ne 0$,
  without which it is false (`matrix_lemma_fails_of_zero`).
* `art239_contains` (Art. 239): if $F$ is compounded directly of $f, f'$ (nonzero discriminants) and $F'$ is
  transformed into $f f'$ in the same way (positive $n_1, n_1'$ for the six relations), then there is an integral
  substitution of determinant $k > 0$ taking $F'$ to $F$, and $\operatorname{disc} F = k^2 \operatorname{disc} F'$.
* `art238_combined_transformsInto`, `art238_combined_relations`, `art238_combined_same_way`,
  `art238_combined_isCompounded_one` (Art. 238, end): combined transitivity, with the sign rule of the mixed cases.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-! ### Art. 234: the matrix lemma -/

/-- **Gauss, *Disq. Arith.* Art. 234, the matrix lemma.** Let $a, b, c, d : \iota \to \mathbb Z$
be four integer families over a finite index type $\iota$ (Gauss's $\lambda = 0, \dots, n$), $k \ne 0$ an integer with
$c_i d_j - d_i c_j = k\,(a_i b_j - b_i a_j)$ for all $i, j$, and suppose the integers $a_i b_j - b_i a_j$ have no common
divisor other than units. Then there are integers $\alpha, \beta, \gamma, \delta$ with
$\alpha a_i + \beta b_i = c_i$, $\gamma a_i + \delta b_i = d_i$ for every $i$ and $\alpha\delta - \beta\gamma = k$.
Proof (Bezout, as in Gauss): with $\sum \lambda_{ij} (a_i b_j - b_i a_j) = 1$ put
$\alpha = \sum \lambda_{ij}(c_i b_j - b_i c_j)$, $\beta = \sum \lambda_{ij}(a_i c_j - c_i a_j)$ and $\gamma, \delta$ likewise
with $d$; the $3 \times 3$ determinant of $a, b, c$ at three columns is killed by $k$, hence zero.

*Update:* the hypothesis $k \ne 0$ is needed and absent from the statement in the historical sources: for $k = 0$,
$a = (1,0,0)$, $b = (0,1,0)$, $c = (0,0,1)$, $d = 0$ satisfy all other hypotheses but $c \notin \operatorname{span}(a, b)$
(`matrix_lemma_fails_of_zero`). Gauss applies the lemma with $k \ne 0$. Coprimality is stated as: every integer
dividing all $a_i b_j - b_i a_j$ is a unit (all ordered pairs $i, j$; the pairs $i \ge j$ add only $0$ and negatives). -/
@[kb "gauss1801" "Art. 234"]
theorem matrix_lemma {ι : Type*} [Fintype ι] (a b c d : ι → ℤ) (k : ℤ) (hk : k ≠ 0)
    (hrel : ∀ i j, c i * d j - d i * c j = k * (a i * b j - b i * a j))
    (hcop : ∀ e : ℤ, (∀ i j, e ∣ a i * b j - b i * a j) → IsUnit e) :
    ∃ α β γ δ : ℤ, (∀ i, α * a i + β * b i = c i ∧ γ * a i + δ * b i = d i) ∧ α * δ - β * γ = k := by
  obtain ⟨lam, hl⟩ : ∃ lam : ι × ι → ℤ, ∑ x, lam x * (a x.1 * b x.2 - b x.1 * a x.2) = 1 := by
    set I : Ideal ℤ := Ideal.span (Set.range fun x : ι × ι => a x.1 * b x.2 - b x.1 * a x.2) with hI
    have hg : IsUnit (Submodule.IsPrincipal.generator I) := by
      apply hcop
      intro i j
      have hm : (a i * b j - b i * a j) ∈ I := Ideal.subset_span ⟨(i, j), rfl⟩
      exact (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp hm
    have htop := Ideal.eq_top_of_isUnit_mem I (Submodule.IsPrincipal.generator_mem I) hg
    have h1 : (1 : ℤ) ∈ I := by rw [htop]; trivial
    rw [hI, Ideal.mem_span_range_iff_exists_fun] at h1
    obtain ⟨l, hl⟩ := h1
    exact ⟨l, by simpa [smul_eq_mul, mul_comm] using hl⟩
  -- a vector `u` with vanishing three-by-three determinants lies in the span of `a, b`
  have span_of : ∀ u : ι → ℤ, (∀ i j l, u l * (a i * b j - b i * a j) =
      a l * (u i * b j - b i * u j) + b l * (a i * u j - u i * a j)) →
      ∀ l, u l = (∑ x, lam x * (u x.1 * b x.2 - b x.1 * u x.2)) * a l +
        (∑ x, lam x * (a x.1 * u x.2 - u x.1 * a x.2)) * b l := by
    intro u hu l
    calc u l = u l * ∑ x, lam x * (a x.1 * b x.2 - b x.1 * a x.2) := by rw [hl, mul_one]
      _ = ∑ x, lam x * (u l * (a x.1 * b x.2 - b x.1 * a x.2)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ x, (lam x * (u x.1 * b x.2 - b x.1 * u x.2) * a l +
            lam x * (a x.1 * u x.2 - u x.1 * a x.2) * b l) :=
          Finset.sum_congr rfl (fun x _ => by
            have := hu x.1 x.2 l
            linear_combination lam x * this)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  have hc : ∀ i j l, c l * (a i * b j - b i * a j) =
      a l * (c i * b j - b i * c j) + b l * (a i * c j - c i * a j) := by
    intro i j l
    apply mul_left_cancel₀ hk
    linear_combination (-c l) * hrel i j + (-c i) * hrel j l + (-c j) * hrel l i
  have hd : ∀ i j l, d l * (a i * b j - b i * a j) =
      a l * (d i * b j - b i * d j) + b l * (a i * d j - d i * a j) := by
    intro i j l
    apply mul_left_cancel₀ hk
    linear_combination (-d l) * hrel i j + (-d i) * hrel j l + (-d j) * hrel l i
  have key : ∀ E : ℤ, (∀ i j, E * (a i * b j - b i * a j) = 0) → E = 0 := by
    intro E hE
    calc E = E * ∑ x, lam x * (a x.1 * b x.2 - b x.1 * a x.2) := by rw [hl, mul_one]
      _ = ∑ x, lam x * (E * (a x.1 * b x.2 - b x.1 * a x.2)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = 0 := Finset.sum_eq_zero (fun x _ => by rw [hE x.1 x.2, mul_zero])
  have sc := span_of c hc
  have sd := span_of d hd
  set α := ∑ x, lam x * (c x.1 * b x.2 - b x.1 * c x.2) with hα
  set β := ∑ x, lam x * (a x.1 * c x.2 - c x.1 * a x.2) with hβ
  set γ := ∑ x, lam x * (d x.1 * b x.2 - b x.1 * d x.2) with hγ
  set δ := ∑ x, lam x * (a x.1 * d x.2 - d x.1 * a x.2) with hδ
  have e1 : ∀ i, α * a i + β * b i = c i := fun i => (sc i).symm
  have e2 : ∀ i, γ * a i + δ * b i = d i := fun i => (sd i).symm
  refine ⟨α, β, γ, δ, fun i => ⟨e1 i, e2 i⟩, ?_⟩
  have hmin : ∀ i j, (α * δ - β * γ - k) * (a i * b j - b i * a j) = 0 := by
    intro i j
    have h := hrel i j
    rw [← e1 i, ← e1 j, ← e2 i, ← e2 j] at h
    linear_combination h
  have := key _ hmin
  linarith

/-- **The hypothesis $k \ne 0$ of the matrix lemma cannot be dropped** (Gauss, *Disq. Arith.* Art. 234; the historical sources
): for $k = 0$, $a = (1, 0, 0)$, $b = (0, 1, 0)$, $c = (0, 0, 1)$, $d = 0$ over three indices satisfy
the relations $c_i d_j - d_i c_j = 0 = 0 \cdot (a_i b_j - b_i a_j)$ and the coprimality (the minor for the pair
$(0, 1)$ is $1$), yet no $\alpha, \beta$ give $\alpha a + \beta b = c$. -/
theorem matrix_lemma_fails_of_zero :
    (∀ i j : Fin 3, (![0, 0, 1] : Fin 3 → ℤ) i * (0 : Fin 3 → ℤ) j - (0 : Fin 3 → ℤ) i * (![0, 0, 1] : Fin 3 → ℤ) j =
      0 * ((![1, 0, 0] : Fin 3 → ℤ) i * (![0, 1, 0] : Fin 3 → ℤ) j - (![0, 1, 0] : Fin 3 → ℤ) i * (![1, 0, 0] : Fin 3 → ℤ) j)) ∧
    (∀ e : ℤ, (∀ i j : Fin 3, e ∣ (![1, 0, 0] : Fin 3 → ℤ) i * (![0, 1, 0] : Fin 3 → ℤ) j -
        (![0, 1, 0] : Fin 3 → ℤ) i * (![1, 0, 0] : Fin 3 → ℤ) j) → IsUnit e) ∧
    ¬ ∃ α β γ δ : ℤ, (∀ i : Fin 3, α * (![1, 0, 0] : Fin 3 → ℤ) i + β * (![0, 1, 0] : Fin 3 → ℤ) i =
        (![0, 0, 1] : Fin 3 → ℤ) i ∧ γ * (![1, 0, 0] : Fin 3 → ℤ) i + δ * (![0, 1, 0] : Fin 3 → ℤ) i =
        (0 : Fin 3 → ℤ) i) ∧ α * δ - β * γ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; simp
  · intro e he
    have := he 0 1
    simp at this
    exact isUnit_of_dvd_one this
  · rintro ⟨α, β, γ, δ, h, -⟩
    have := (h 2).1
    simp at this

/-! ### Art. 239 -/

private theorem exists_eval_ne_zero' {f : BinQF} (h : f.disc ≠ 0) : ∃ x y : ℤ, f.eval x y ≠ 0 :=
  exists_eval_ne_zero_of_disc_ne_zero h

/-- **Gauss, *Disq. Arith.* Art. 239: a form transformable into $f f'$ in the same way as
a compounded form properly contains it.** Let $F$ be compounded directly of $f, f'$ (`IsCompounded`), with
$\operatorname{disc} f \ne 0 \ne \operatorname{disc} f'$, and let $F'$ be transformed into $f f'$ by $(p_1, q_1)$
(`TransformsInto`) with the six relations of Art. 235 holding with positive rationals $n_1, n_1'$ ("in the same way":
same signs as $n, n'$). Then there are integers $\alpha, \beta, \gamma, \delta$ with
$\alpha\delta - \beta\gamma = k > 0$ and $F'(\alpha x + \beta y, \gamma x + \delta y) = F(x, y)$
(`subst α β γ δ F' = F`: $F'$ properly contains $F$), and $\operatorname{disc} F = k^2 \operatorname{disc} F'$
(Gauss's $k = \sqrt{D'/D}$ with $D'$ the determinant of the form that is contained, here $F$).
No coprimality of the six numbers of $F'$ is needed. Proof as in Gauss: the six numbers of $(p_1, q_1)$ are
$r = n_1/n$ times those of $(p, q)$ (from $n^2 \operatorname{disc} F = \operatorname{disc} f = n_1^2 \operatorname{disc} F'$,
likewise for $f'$, and positivity); $r = k$ is an integer by coprimality of the six numbers of $(p, q)$; then the matrix
lemma (`matrix_lemma`, with the four-element index type of the entries) gives $(p_1, q_1) = (\alpha p + \beta q,
\gamma p + \delta q)$, so $F'(\alpha X + \beta Y, \gamma X + \delta Y) = F(X, Y)$ on all values $(X, Y)$ of $(p, q)$,
which suffice to determine a binary form. -/
@[kb "gauss1801" "Art. 239"]
theorem art239_contains {F F' f f' : BinQF} (hF : IsCompounded F f f') (hf : f.disc ≠ 0) (hf' : f'.disc ≠ 0)
    {p₁ q₁ : Fin 4 → ℤ} (hT' : TransformsInto F' f f' p₁ q₁) {n₁ n₁' : ℚ} (hn₁ : 0 < n₁) (hn₁' : 0 < n₁')
    (h0 : (minors p₁ q₁ 0 : ℚ) = f.a * n₁') (h1 : ((minors p₁ q₁ 2 : ℚ) - minors p₁ q₁ 3) = f.b * n₁')
    (h2 : (minors p₁ q₁ 5 : ℚ) = f.c * n₁') (h3 : (minors p₁ q₁ 1 : ℚ) = f'.a * n₁)
    (h4 : ((minors p₁ q₁ 2 : ℚ) + minors p₁ q₁ 3) = f'.b * n₁) (h5 : (minors p₁ q₁ 4 : ℚ) = f'.c * n₁) :
    ∃ α β γ δ k : ℤ, 0 < k ∧ α * δ - β * γ = k ∧ subst α β γ δ F' = F ∧ F.disc = k ^ 2 * F'.disc := by
  obtain ⟨p, q, hT, hcop, n, n', hn, hn', g0, g1, g2, g3, g4, g5⟩ := hF
  have hx := exists_eval_ne_zero' hf
  have hx' := exists_eval_ne_zero' hf'
  have e1 := disc_mul_sq_of_rel_first hT g3 g4 g5 hx'
  have e2 := disc_mul_sq_of_rel_second hT g0 g1 g2 hx
  have e1' := disc_mul_sq_of_rel_first hT' h3 h4 h5 hx'
  have e2' := disc_mul_sq_of_rel_second hT' h0 h1 h2 hx
  have hF'q : (F'.disc : ℚ) ≠ 0 := by
    intro h; rw [h, mul_zero] at e1'; exact hf (by exact_mod_cast e1')
  have hsq : (n₁' * n) ^ 2 = (n₁ * n') ^ 2 := by
    apply mul_right_cancel₀ hF'q
    linear_combination n ^ 2 * e2 - n' ^ 2 * e1 - n ^ 2 * e2' + n' ^ 2 * e1'
  have hnn : n₁' * n = n₁ * n' := by
    have hp1 : 0 < n₁' * n := mul_pos hn₁' hn
    have hp2 : 0 < n₁ * n' := mul_pos hn₁ hn'
    have : (n₁' * n - n₁ * n') * (n₁' * n + n₁ * n') = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  -- the six numbers of (p₁, q₁) are n₁ / n times those of (p, q)
  have s0 : (minors p₁ q₁ 0 : ℚ) * n = n₁ * minors p q 0 := by
    linear_combination n * h0 - n₁ * g0 + f.a * hnn
  have s1 : (minors p₁ q₁ 1 : ℚ) * n = n₁ * minors p q 1 := by
    linear_combination n * h3 - n₁ * g3
  have s5 : (minors p₁ q₁ 5 : ℚ) * n = n₁ * minors p q 5 := by
    linear_combination n * h2 - n₁ * g2 + f.c * hnn
  have s4 : (minors p₁ q₁ 4 : ℚ) * n = n₁ * minors p q 4 := by
    linear_combination n * h5 - n₁ * g5
  have sm : ((minors p₁ q₁ 2 : ℚ) - minors p₁ q₁ 3) * n = n₁ * ((minors p q 2 : ℚ) - minors p q 3) := by
    linear_combination n * h1 - n₁ * g1 + f.b * hnn
  have sp : ((minors p₁ q₁ 2 : ℚ) + minors p₁ q₁ 3) * n = n₁ * ((minors p q 2 : ℚ) + minors p q 3) := by
    linear_combination n * h4 - n₁ * g4
  have s2 : (minors p₁ q₁ 2 : ℚ) * n = n₁ * minors p q 2 := by linear_combination (sm + sp) / 2
  have s3 : (minors p₁ q₁ 3 : ℚ) * n = n₁ * minors p q 3 := by linear_combination (sp - sm) / 2
  have hM : ∀ i, (minors p₁ q₁ i : ℚ) * n = n₁ * minors p q i := by
    intro i; fin_cases i
    exacts [s0, s1, s2, s3, s4, s5]
  set r : ℚ := n₁ / n with hr
  have hint : ∀ i, (minors p₁ q₁ i : ℚ) = r * minors p q i := by
    intro i
    rw [hr, div_mul_eq_mul_div, eq_div_iff hn.ne']
    exact hM i
  -- r is an integer
  have hden : r.den = 1 := by
    have hdv : ∀ i, (r.den : ℤ) ∣ minors p q i := by
      intro i
      have hq : (minors p₁ q₁ i : ℚ) * r.den = r.num * minors p q i := by
        rw [hint i]
        calc r * (minors p q i : ℚ) * r.den = (r * r.den) * minors p q i := by ring
          _ = r.num * minors p q i := by rw [Rat.mul_den_eq_num]
      have hqz : (minors p₁ q₁ i) * (r.den : ℤ) = r.num * minors p q i := by exact_mod_cast hq
      have hcp : IsCoprime (r.den : ℤ) r.num := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have := r.reduced
        rw [Int.gcd_comm]
        simpa [Int.gcd] using this
      exact hcp.dvd_of_dvd_mul_left ⟨minors p₁ q₁ i, by linear_combination -hqz⟩
    have hu := hcop (r.den : ℤ) hdv
    rcases Int.isUnit_iff.mp hu with h | h
    · exact_mod_cast h
    · omega
  have hkr : ((r.num : ℤ) : ℚ) = r := by
    have := Rat.num_div_den r
    rw [hden] at this
    simpa using this
  set k : ℤ := r.num with hk
  have hrpos : 0 < r := div_pos hn₁ hn
  have hkpos : 0 < k := by
    have : (0 : ℚ) < k := by rw [hkr]; exact hrpos
    exact_mod_cast this
  have hmin : ∀ i, minors p₁ q₁ i = k * minors p q i := by
    intro i
    have := hint i
    rw [← hkr] at this
    exact_mod_cast this
  have hpair : ∀ i j : Fin 4, p₁ i * q₁ j - q₁ i * p₁ j = k * (p i * q j - q i * p j) := by
    have e0 : p₁ 0 * q₁ 1 - q₁ 0 * p₁ 1 = k * (p 0 * q 1 - q 0 * p 1) := hmin 0
    have e1 : p₁ 0 * q₁ 2 - q₁ 0 * p₁ 2 = k * (p 0 * q 2 - q 0 * p 2) := hmin 1
    have e2 : p₁ 0 * q₁ 3 - q₁ 0 * p₁ 3 = k * (p 0 * q 3 - q 0 * p 3) := hmin 2
    have e3 : p₁ 1 * q₁ 2 - q₁ 1 * p₁ 2 = k * (p 1 * q 2 - q 1 * p 2) := hmin 3
    have e4 : p₁ 1 * q₁ 3 - q₁ 1 * p₁ 3 = k * (p 1 * q 3 - q 1 * p 3) := hmin 4
    have e5 : p₁ 2 * q₁ 3 - q₁ 2 * p₁ 3 = k * (p 2 * q 3 - q 2 * p 3) := hmin 5
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first
      | linear_combination e0 | linear_combination -e0
      | linear_combination e1 | linear_combination -e1
      | linear_combination e2 | linear_combination -e2
      | linear_combination e3 | linear_combination -e3
      | linear_combination e4 | linear_combination -e4
      | linear_combination e5 | linear_combination -e5
      | ring1
  have hcop' : ∀ e : ℤ, (∀ i j : Fin 4, e ∣ p i * q j - q i * p j) → IsUnit e := by
    intro e he
    apply hcop e
    intro i
    fin_cases i
    · exact he 0 1
    · exact he 0 2
    · exact he 0 3
    · exact he 1 2
    · exact he 1 3
    · exact he 2 3
  obtain ⟨α, β, γ, δ, hm, hdet⟩ := matrix_lemma p q p₁ q₁ k hkpos.ne' hpair hcop'
  obtain ⟨x', y', hv⟩ := hx'
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = (p 0 * x' + p 1 * y') * (q 2 * x' + q 3 * y') -
      (p 2 * x' + p 3 * y') * (q 0 * x' + q 1 * y') := ⟨_, rfl⟩
  have hdq : (d : ℚ) = n * (f'.eval x' y' : ℤ) := by
    have g3' := g3
    have g4' := g4
    have g5' := g5
    simp only [minors, Matrix.cons_val] at g3' g4' g5'
    push_cast at g3' g4' g5'
    rw [hd, eval_eq]; push_cast
    linear_combination (x' : ℚ) ^ 2 * g3' + (x' : ℚ) * y' * g4' + (y' : ℚ) ^ 2 * g5'
  have hd0 : d ≠ 0 := by
    intro h
    rw [h] at hdq
    have h' : n * ((f'.eval x' y' : ℤ) : ℚ) = 0 := by rw [← hdq]; simp
    rcases mul_eq_zero.mp h' with h'' | h''
    · linarith
    · exact hv (by exact_mod_cast h'')
  have hlin1 : ∀ x y x' y' : ℤ, bilin p₁ x y x' y' = α * bilin p x y x' y' + β * bilin q x y x' y' := by
    intro x y x' y'
    simp only [bilin]
    rw [← (hm 0).1, ← (hm 1).1, ← (hm 2).1, ← (hm 3).1]
    ring
  have hlin2 : ∀ x y x' y' : ℤ, bilin q₁ x y x' y' = γ * bilin p x y x' y' + δ * bilin q x y x' y' := by
    intro x y x' y'
    simp only [bilin]
    rw [← (hm 0).2, ← (hm 1).2, ← (hm 2).2, ← (hm 3).2]
    ring
  have hbp : ∀ x y : ℤ, bilin p x y x' y' = (p 0 * x' + p 1 * y') * x + (p 2 * x' + p 3 * y') * y := by
    intro x y; simp only [bilin]; ring
  have hbq : ∀ x y : ℤ, bilin q x y x' y' = (q 0 * x' + q 1 * y') * x + (q 2 * x' + q 3 * y') * y := by
    intro x y; simp only [bilin]; ring
  have hev : ∀ u v : ℤ, (subst α β γ δ F').eval (d * u) (d * v) = F.eval (d * u) (d * v) := by
    intro u v
    obtain ⟨x, hxx⟩ : ∃ x : ℤ, x = (q 2 * x' + q 3 * y') * u - (p 2 * x' + p 3 * y') * v := ⟨_, rfl⟩
    obtain ⟨y, hyy⟩ : ∃ y : ℤ, y = -(q 0 * x' + q 1 * y') * u + (p 0 * x' + p 1 * y') * v := ⟨_, rfl⟩
    have hX : bilin p x y x' y' = d * u := by rw [hbp, hxx, hyy, hd]; ring
    have hY : bilin q x y x' y' = d * v := by rw [hbq, hxx, hyy, hd]; ring
    calc (subst α β γ δ F').eval (d * u) (d * v)
        = F'.eval (α * (d * u) + β * (d * v)) (γ * (d * u) + δ * (d * v)) := eval_subst _ _ _ _ _ _ _
      _ = F'.eval (bilin p₁ x y x' y') (bilin q₁ x y x' y') := by
          rw [hlin1, hlin2, hX, hY]
      _ = f.eval x y * f'.eval x' y' := hT' x y x' y'
      _ = F.eval (bilin p x y x' y') (bilin q x y x' y') := (hT x y x' y').symm
      _ = F.eval (d * u) (d * v) := by rw [hX, hY]
  have hsub : subst α β γ δ F' = F := by
    have c1 := hev 1 0
    have c2 := hev 0 1
    have c3 := hev 1 1
    simp only [eval_eq] at c1 c2 c3
    have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
    apply ext_abc
    · apply mul_left_cancel₀ hd2; linear_combination c1
    · apply mul_left_cancel₀ hd2; linear_combination c3 - c1 - c2
    · apply mul_left_cancel₀ hd2; linear_combination c2
  refine ⟨α, β, γ, δ, k, hkpos, hdet, hsub, ?_⟩
  rw [← hsub, disc_subst, hdet]

/-! ### Art. 238 (end): combined transitivity -/

/-- The coefficients of the bilinear substitution $p(\alpha x + \beta y, \gamma x + \delta y; x', y')$:
$(\alpha p_0 + \gamma p_2,\ \alpha p_1 + \gamma p_3,\ \beta p_0 + \delta p_2,\ \beta p_1 + \delta p_3)$. -/
def tfst (p : Fin 4 → ℤ) (α β γ δ : ℤ) : Fin 4 → ℤ :=
  ![α * p 0 + γ * p 2, α * p 1 + γ * p 3, β * p 0 + δ * p 2, β * p 1 + δ * p 3]

/-- **Art. 237 for the first factor** (the mirror image of `art237_transformsInto`): if $F$ is transformed into
$f f'$ by $(p, q)$ then $F$ is transformed into $g f'$, $g = f(\alpha x + \beta y, \gamma x + \delta y)$
(`subst`), by `tfst p α β γ δ`, `tfst q α β γ δ`. -/
theorem art237_first_transformsInto {F f f' : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    (α β γ δ : ℤ) :
    TransformsInto F (subst α β γ δ f) f' (tfst p α β γ δ) (tfst q α β γ δ) := by
  intro x y x' y'
  rw [eval_subst, ← hT (α * x + β * y) (γ * x + δ * y) x' y']
  simp only [bilin, tfst, Matrix.cons_val]
  congr 1 <;> ring

/-- **Art. 237 for the first factor, the relations** (mirror image of `art237_relations`): if the six relations hold
for $(p, q)$ with $n, n'$, then for $g = f(\alpha x + \beta y, \gamma x + \delta y)$ and
$e = \alpha\delta - \beta\gamma$ they hold for `tfst p α β γ δ`, `tfst q α β γ δ` with the forms $g, f'$ and the
numbers $n'$ (for $g$) and $n e$ (for $f'$). -/
theorem art237_first_relations {f f' : BinQF} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n) (h5 : (minors p q 4 : ℚ) = f'.c * n)
    (α β γ δ : ℤ) :
    (minors (tfst p α β γ δ) (tfst q α β γ δ) 0 : ℚ) = (subst α β γ δ f).a * n' ∧
    ((minors (tfst p α β γ δ) (tfst q α β γ δ) 2 : ℚ) - minors (tfst p α β γ δ) (tfst q α β γ δ) 3) =
      (subst α β γ δ f).b * n' ∧
    (minors (tfst p α β γ δ) (tfst q α β γ δ) 5 : ℚ) = (subst α β γ δ f).c * n' ∧
    (minors (tfst p α β γ δ) (tfst q α β γ δ) 1 : ℚ) = f'.a * (n * ((α * δ - β * γ : ℤ) : ℚ)) ∧
    ((minors (tfst p α β γ δ) (tfst q α β γ δ) 2 : ℚ) + minors (tfst p α β γ δ) (tfst q α β γ δ) 3) =
      f'.b * (n * ((α * δ - β * γ : ℤ) : ℚ)) ∧
    (minors (tfst p α β γ δ) (tfst q α β γ δ) 4 : ℚ) = f'.c * (n * ((α * δ - β * γ : ℤ) : ℚ)) := by
  simp only [minors, Matrix.cons_val] at h0 h1 h2 h3 h4 h5
  push_cast at h0 h1 h2 h3 h4 h5
  simp only [minors, tfst, Matrix.cons_val, a_subst, b_subst, c_subst]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (α : ℚ) ^ 2 * h0 + (α : ℚ) * γ * h1 + (γ : ℚ) ^ 2 * h2
  · linear_combination 2 * (α : ℚ) * β * h0 + ((α : ℚ) * δ + β * γ) * h1 + 2 * (γ : ℚ) * δ * h2
  · linear_combination (β : ℚ) ^ 2 * h0 + (β : ℚ) * δ * h1 + (δ : ℚ) ^ 2 * h2
  · linear_combination ((α : ℚ) * δ - β * γ) * h3
  · linear_combination ((α : ℚ) * δ - β * γ) * h4
  · linear_combination ((α : ℚ) * δ - β * γ) * h5

/-- **Gauss, *Disq. Arith.* Art. 238, end, combined transitivity, the substitution:** if $F$
is transformed into $f f'$ (by $(p, q)$), $g = f(\alpha x + \beta y, \gamma x + \delta y)$ ($f$ contains $g$),
$g' = f'(\alpha' x + \beta' y, \gamma' x + \delta' y)$ ($f'$ contains $g'$) and
$F = G(A X + B Y, C X + D Y)$ ($G$ contains $F$), then $G$ is transformed into $g g'$ (Art. 237 twice, then Art. 238). -/
@[kb "gauss1801" "Art. 238, end"]
theorem art238_combined_transformsInto {F f f' G : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    (α β γ δ α' β' γ' δ' A B C D : ℤ) (hG : subst A B C D G = F) :
    ∃ p' q' : Fin 4 → ℤ, TransformsInto G (subst α β γ δ f) (subst α' β' γ' δ' f') p' q' := by
  have t2 := art237_first_transformsInto (art237_transformsInto hT α' β' γ' δ') α β γ δ
  exact ⟨_, _, art238_transformsInto A B C D (by rw [hG]; exact t2)⟩

/-- **Gauss, *Disq. Arith.* Art. 238, end, combined transitivity, the relations and the sign
rule.** Under the hypotheses of `art238_combined_transformsInto`, with $e = \alpha\delta - \beta\gamma$,
$e' = \alpha'\delta' - \beta'\gamma'$, $e_G = AD - BC$ and the six relations of Art. 235 for $F, f, f'$ with $n, n'$,
the substitution of $G$ into $g g'$ obtained satisfies the six relations with
$$n_G = n\,e\,e_G \ (\text{for } g'), \qquad n'_G = n'\,e'\,e_G \ (\text{for } g).$$
So the sign of $n_G$ is that of $n$ times the sign of $e\,e_G$ (determinant of $f \to g$ times that of $G \to F$)
and the sign of $n'_G$ is that of $n'$ times the sign of $e'\,e_G$ (the constant belonging to $g$ is governed by the
substitution $f' \to g'$ of the *other* factor, as in Art. 237). Hence the orientation in the first factor reverses
exactly when $e e_G < 0$, in the second when $e' e_G < 0$: all three proper or all three improper keep both
(`art238_combined_same_way`); the mixed cases are decided by these two products. -/
@[kb "gauss1801" "Art. 238, end"]
theorem art238_combined_relations {F f f' G : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    {n n' : ℚ}
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n) (h5 : (minors p q 4 : ℚ) = f'.c * n)
    (α β γ δ α' β' γ' δ' A B C D : ℤ) (hG : subst A B C D G = F) :
    ∃ p' q' : Fin 4 → ℤ, TransformsInto G (subst α β γ δ f) (subst α' β' γ' δ' f') p' q' ∧
      (minors p' q' 0 : ℚ) = (subst α β γ δ f).a *
        (n' * ((α' * δ' - β' * γ' : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) ∧
      ((minors p' q' 2 : ℚ) - minors p' q' 3) = (subst α β γ δ f).b *
        (n' * ((α' * δ' - β' * γ' : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) ∧
      (minors p' q' 5 : ℚ) = (subst α β γ δ f).c *
        (n' * ((α' * δ' - β' * γ' : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) ∧
      (minors p' q' 1 : ℚ) = (subst α' β' γ' δ' f').a *
        (n * ((α * δ - β * γ : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) ∧
      ((minors p' q' 2 : ℚ) + minors p' q' 3) = (subst α' β' γ' δ' f').b *
        (n * ((α * δ - β * γ : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) ∧
      (minors p' q' 4 : ℚ) = (subst α' β' γ' δ' f').c *
        (n * ((α * δ - β * γ : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ)) := by
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := art237_relations h0 h1 h2 h3 h4 h5 α' β' γ' δ'
  obtain ⟨u0, u1, u2, u3, u4, u5⟩ := art237_first_relations r0 r1 r2 r3 r4 r5 α β γ δ
  have t2 := art237_first_transformsInto (art237_transformsInto hT α' β' γ' δ') α β γ δ
  have t3 := art238_transformsInto A B C D (by rw [hG]; exact t2)
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := art238_relations u0 u1 u2 u3 u4 u5 A B C D
  exact ⟨_, _, t3, v0, v1, v2, v3, v4, v5⟩

/-- **Art. 238, end: all three implications proper (or all improper) keep the way.** Under
the hypotheses of `art238_combined_relations` with $n, n' > 0$, if $e\,e_G > 0$ and $e'\,e_G > 0$ (in particular if
$e, e', e_G > 0$, all proper, or $e, e', e_G < 0$, all improper) then $G$ is transformed into $g g'$ with the six
relations holding with **positive** $n_G = n e e_G$ and $n'_G = n' e' e_G$, i.e. in the same way as $F$ into $f f'$. -/
@[kb "gauss1801" "Art. 238, end"]
theorem art238_combined_same_way {F f f' G : BinQF} {p q : Fin 4 → ℤ} (hT : TransformsInto F f f' p q)
    {n n' : ℚ} (hn : 0 < n) (hn' : 0 < n')
    (h0 : (minors p q 0 : ℚ) = f.a * n') (h1 : ((minors p q 2 : ℚ) - minors p q 3) = f.b * n')
    (h2 : (minors p q 5 : ℚ) = f.c * n') (h3 : (minors p q 1 : ℚ) = f'.a * n)
    (h4 : ((minors p q 2 : ℚ) + minors p q 3) = f'.b * n) (h5 : (minors p q 4 : ℚ) = f'.c * n)
    (α β γ δ α' β' γ' δ' A B C D : ℤ) (hG : subst A B C D G = F)
    (he : 0 < (α * δ - β * γ) * (A * D - B * C)) (he' : 0 < (α' * δ' - β' * γ') * (A * D - B * C)) :
    ∃ p' q' : Fin 4 → ℤ, ∃ nG nG' : ℚ, 0 < nG ∧ 0 < nG' ∧
      TransformsInto G (subst α β γ δ f) (subst α' β' γ' δ' f') p' q' ∧
      (minors p' q' 0 : ℚ) = (subst α β γ δ f).a * nG' ∧
      ((minors p' q' 2 : ℚ) - minors p' q' 3) = (subst α β γ δ f).b * nG' ∧
      (minors p' q' 5 : ℚ) = (subst α β γ δ f).c * nG' ∧
      (minors p' q' 1 : ℚ) = (subst α' β' γ' δ' f').a * nG ∧
      ((minors p' q' 2 : ℚ) + minors p' q' 3) = (subst α' β' γ' δ' f').b * nG ∧
      (minors p' q' 4 : ℚ) = (subst α' β' γ' δ' f').c * nG := by
  obtain ⟨p', q', t, v0, v1, v2, v3, v4, v5⟩ :=
    art238_combined_relations hT h0 h1 h2 h3 h4 h5 α β γ δ α' β' γ' δ' A B C D hG
  have e1 : (0 : ℚ) < ((α * δ - β * γ : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ) := by exact_mod_cast he
  have e2 : (0 : ℚ) < ((α' * δ' - β' * γ' : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ) := by exact_mod_cast he'
  refine ⟨p', q', n * ((α * δ - β * γ : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ),
    n' * ((α' * δ' - β' * γ' : ℤ) : ℚ) * ((A * D - B * C : ℤ) : ℚ), ?_, ?_, t, v0, v1, v2, v3, v4, v5⟩
  · rw [mul_assoc]; exact mul_pos hn e1
  · rw [mul_assoc]; exact mul_pos hn' e2

/-- **Art. 238, end, with coprimality:** if $F$ is compounded directly of $f, f'$ and the
three substitutions have determinant $1$, then $G$ is compounded directly of $g, g'$ (the six numbers are unchanged).
For general proper determinants coprimality is lost (the six numbers are multiplied by $e_G$ and the relations
rescale), see `art238_combined_same_way`. -/
@[kb "gauss1801" "Art. 238, end"]
theorem art238_combined_isCompounded_one {F f f' G : BinQF} (h : IsCompounded F f f')
    (α β γ δ α' β' γ' δ' A B C D : ℤ) (he : α * δ - β * γ = 1) (he' : α' * δ' - β' * γ' = 1)
    (heG : A * D - B * C = 1) (hG : subst A B C D G = F) :
    IsCompounded G (subst α β γ δ f) (subst α' β' γ' δ' f') := by
  have h1 := isCompounded_subst h ![α, β, γ, δ] ![α', β', γ', δ'] (by simpa using he) (by simpa using he')
  simp only [Matrix.cons_val] at h1
  exact art238_isCompounded_one A B C D heG (by rw [hG]; exact h1)

end QuadFormsKB.Historical.Gauss
