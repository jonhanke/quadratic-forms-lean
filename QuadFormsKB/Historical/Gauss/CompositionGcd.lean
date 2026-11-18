import QuadFormsKB.Historical.Gauss.CompositionOrders
import QuadFormsKB.Historical.Gauss.Orders

/-!
# The gcd conclusions of Art. 235 and the composition of orders (Disquisitiones Arithmeticae, Arts. 235, 240, 245)

(Art. 245, composition of orders), the divisibility part of
(Art. 235, the divisibility facts derived from the identities $\Omega$) and 
(Art. 240, step I, determinants of iterated composites).

Forms are Gauss's: $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ (`gaussForm`, library middle coefficient
$2B$, $2b$, $2b'$), $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$ (`gcd3 a (2 * b) c`), $M = \gcd(A, 2B, C)$.
Indices are $0$-based: Gauss's $p, p', p'', p'''$ are `p 0, …, p 3`.

## What is proved (everything, nothing assumed)

* `gaussCompositionGcds`, `gaussOrderComposition`, `gaussImproperComposition`: the three named propositions of
  `CompositionOrders.lean` (`GaussCompositionGcds`, `GaussOrderComposition`, `GaussImproperComposition`).
* `art235_divisibility`: $m m'$ divides $a a'$, $2ab'$, $ac'$, $2ba'$, $4bb'$, $2bc'$, $ca'$, $2cb'$, $cc'$,
  $2bb' + 2\Delta$ and $2bb' - 2\Delta$ (for any bilinear substitution with the relations of Art. 235; no coprimality).
* `art235_M_divisibility`: for a compounded form, $M = m m'$ and so $M$ divides $am'$, $2bm'$, $cm'$ and $m m'$.
* `art240_step_one`: determinants of the four composites of Art. 240, step I.

## Method

The Gram entries $g_{ij} = F(v_i, v_j)$ of the four vectors $v_i = (p_i, q_i)$ are $a a', a c', c a', c c'$ on the
diagonal, $a b', b a', b c', c b'$ at the pairs $(0,1), (0,2), (1,3), (2,3)$ and $b b' \pm \Delta$ at $(0,3), (1,2)$
(`art235_delta_eq`). That $m m'$ divides $2 g_{03}$ and $2 g_{12}$ is the one new fact: from $\Delta^2 = d d'$
(`art235_delta_sq`) and $m m' \mid 4bb'$, $(m m')^2 \mid (2g_{03})(2g_{12})$ one gets $m m' \mid 2g_{03}, 2g_{12}$
(`cg_split`). Then $A M_{ij}^2$, $2B M_{ij}^2$, $C M_{ij}^2$ are integer combinations of Gram entries for each of the
six minors $M_{ij}$, so $m m'$ divides them; the six minors are coprime, hence so are their squares, and
$m m' \mid A, 2B, C$. For $\gcd(A, B, C)$ the parity is settled by $|D| = \gcd(d m'^2, d' m^2)$ (Art. 235, fourth
conclusion): $m m' \mid A, B, C$ forces $(m m')^2 \mid D$, hence $m^2 \mid d$ and $m'^2 \mid d'$, hence $m \mid b$ and
$m' \mid b'$ (both factors proper); conversely if both are proper, $m m' \mid \Delta$ and all Gram entries are
divisible by $m m'$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-! ### Gram entries -/

/-- The Gram entry $F(v_i, v_j)$ (Gauss's half-polar form, $F = (A, B, C)$) of $v_i = (p_i, q_i)$, $v_j = (p_j, q_j)$. -/
private def gr (A B C : ℤ) (p q : Fin 4 → ℤ) (i j : Fin 4) : ℤ :=
  A * p i * p j + B * (p i * q j + q i * p j) + C * q i * q j

/-- The minor $p_i q_j - q_i p_j$. -/
private def mn (p q : Fin 4 → ℤ) (i j : Fin 4) : ℤ := p i * q j - q i * p j

private theorem cg_ev {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q) (x y x' y' : ℤ) :
    A * (bilin p x y x' y') ^ 2 + 2 * B * bilin p x y x' y' * bilin q x y x' y' + C * (bilin q x y x' y') ^ 2 =
      (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a' * x' ^ 2 + 2 * b' * x' * y' + c' * y' ^ 2) := by
  have := hT x y x' y'
  rw [eval_gaussForm, eval_gaussForm, eval_gaussForm] at this
  exact this

/-- The Gram entries at the pairs where the product $f f'$ determines them. -/
private theorem cg_gram {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q) :
    gr A B C p q 0 0 = a * a' ∧ gr A B C p q 1 1 = a * c' ∧ gr A B C p q 2 2 = c * a' ∧
    gr A B C p q 3 3 = c * c' ∧ gr A B C p q 0 1 = a * b' ∧ gr A B C p q 0 2 = b * a' ∧
    gr A B C p q 1 3 = b * c' ∧ gr A B C p q 2 3 = c * b' ∧
    gr A B C p q 0 3 + gr A B C p q 1 2 = 2 * (b * b') := by
  have ev := cg_ev hT
  have e00 : gr A B C p q 0 0 = a * a' := by
    have h := ev 1 0 1 0
    simp only [bilin, gr] at h ⊢; linear_combination h
  have e11 : gr A B C p q 1 1 = a * c' := by
    have h := ev 1 0 0 1
    simp only [bilin, gr] at h ⊢; linear_combination h
  have e22 : gr A B C p q 2 2 = c * a' := by
    have h := ev 0 1 1 0
    simp only [bilin, gr] at h ⊢; linear_combination h
  have e33 : gr A B C p q 3 3 = c * c' := by
    have h := ev 0 1 0 1
    simp only [bilin, gr] at h ⊢; linear_combination h
  have e01 : gr A B C p q 0 1 = a * b' := by
    have h := ev 1 0 1 1
    have : 2 * gr A B C p q 0 1 = 2 * (a * b') := by
      simp only [bilin, gr] at h e00 e11 ⊢; linear_combination h - e00 - e11
    exact mul_left_cancel₀ two_ne_zero this
  have e02 : gr A B C p q 0 2 = b * a' := by
    have h := ev 1 1 1 0
    have : 2 * gr A B C p q 0 2 = 2 * (b * a') := by
      simp only [bilin, gr] at h e00 e22 ⊢; linear_combination h - e00 - e22
    exact mul_left_cancel₀ two_ne_zero this
  have e23 : gr A B C p q 2 3 = c * b' := by
    have h := ev 0 1 1 1
    have : 2 * gr A B C p q 2 3 = 2 * (c * b') := by
      simp only [bilin, gr] at h e22 e33 ⊢; linear_combination h - e22 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e13 : gr A B C p q 1 3 = b * c' := by
    have h := ev 1 1 0 1
    have : 2 * gr A B C p q 1 3 = 2 * (b * c') := by
      simp only [bilin, gr] at h e11 e33 ⊢; linear_combination h - e11 - e33
    exact mul_left_cancel₀ two_ne_zero this
  have e03 : gr A B C p q 0 3 + gr A B C p q 1 2 = 2 * (b * b') := by
    have h := ev 1 1 1 1
    have : 2 * (gr A B C p q 0 3 + gr A B C p q 1 2) = 2 * (2 * (b * b')) := by
      simp only [bilin, gr] at h e00 e11 e22 e33 e01 e02 e13 e23 ⊢
      linear_combination h - e00 - e11 - e22 - e33 - 2 * e01 - 2 * e02 - 2 * e13 - 2 * e23
    exact mul_left_cancel₀ two_ne_zero this
  exact ⟨e00, e11, e22, e33, e01, e02, e13, e23, e03⟩

/-! ### Two arithmetic lemmas -/

/-- If $N \mid X + Y$ and $N^2 \mid XY$ then $N \mid X$ and $N \mid Y$. (Then $N^2 \mid (X - Y)^2 = (X+Y)^2 - 4XY$,
so $N \mid X - Y$, and $2X = (X + Y) + (X - Y) = N(u + v)$ with $u^2 - v^2 = 4z$ forces $u + v$ even.) -/
private theorem cg_split {N X Y : ℤ} (hs : N ∣ X + Y) (hp : N ^ 2 ∣ X * Y) : N ∣ X ∧ N ∣ Y := by
  obtain ⟨u, hu⟩ := hs
  obtain ⟨z, hz⟩ := hp
  by_cases hN : N = 0
  · subst hN
    have h1 : X + Y = 0 := by simpa using hu
    have h2 : X * Y = 0 := by simpa using hz
    have hY : Y = -X := by linarith
    have hX : X = 0 := by
      rw [hY] at h2
      have : X * X = 0 := by linarith
      exact mul_self_eq_zero.mp this
    subst hX
    have : Y = 0 := by linarith
    subst this
    simp
  · have hdiff : N ∣ X - Y := by
      have h2 : N ^ 2 ∣ (X - Y) ^ 2 :=
        ⟨u ^ 2 - 4 * z, by linear_combination (X + Y + N * u) * hu - 4 * hz⟩
      exact (Int.pow_dvd_pow_iff two_ne_zero).mp h2
    obtain ⟨v, hv⟩ := hdiff
    have h2X : 2 * X = N * (u + v) := by linear_combination hu + hv
    have h2Y : 2 * Y = N * (u - v) := by linear_combination hu - hv
    have h4 : N ^ 2 * (u ^ 2 - v ^ 2) = N ^ 2 * (4 * z) := by
      calc N ^ 2 * (u ^ 2 - v ^ 2) = (2 * X) * (2 * Y) := by rw [h2X, h2Y]; ring
        _ = 4 * (X * Y) := by ring
        _ = N ^ 2 * (4 * z) := by rw [hz]; ring
    have h5 : u ^ 2 - v ^ 2 = 4 * z := mul_left_cancel₀ (pow_ne_zero 2 hN) h4
    have h6 : Even (u ^ 2 - v ^ 2) := ⟨2 * z, by linarith⟩
    have h7 : Even (u + v) := by
      rw [Int.even_add]
      have := Int.even_sub.mp h6
      rwa [Int.even_pow' two_ne_zero, Int.even_pow' two_ne_zero] at this
    obtain ⟨r, hr⟩ := h7
    have hX : X = N * r := by
      have : 2 * X = 2 * (N * r) := by rw [h2X, hr]; ring
      exact mul_left_cancel₀ two_ne_zero this
    refine ⟨⟨r, hX⟩, ?_⟩
    have : Y = N * u - X := by linarith
    rw [this]
    exact dvd_sub ⟨u, rfl⟩ ⟨r, hX⟩

/-- If integers $x_0, \dots, x_5$ have no common divisor other than units and $d \mid A x_i^2$ for all $i$, then
$d \mid A$ (the squares generate the unit ideal). -/
private theorem cg_dvd_of_sq {d A : ℤ} (x : Fin 6 → ℤ) (hx : ∀ e : ℤ, (∀ i, e ∣ x i) → IsUnit e)
    (h : ∀ i, d ∣ A * x i ^ 2) : d ∣ A := by
  set I : Ideal ℤ := Ideal.span (Set.range x) with hI
  have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
    Submodule.IsPrincipal.span_singleton_generator I
  have hdvd : ∀ i, Submodule.IsPrincipal.generator I ∣ x i := fun i => by
    have : x i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [← hg, Ideal.mem_span_singleton] at this
    exact this
  have htop : I = ⊤ := by
    rw [← hg]; exact Ideal.span_singleton_eq_top.mpr (hx _ hdvd)
  have h2 : Ideal.span ((fun y : ℤ => y ^ 2) '' Set.range x) = ⊤ := Ideal.span_pow_eq_top _ htop 2
  have hr : Set.range (fun i => x i ^ 2) = (fun y : ℤ => y ^ 2) '' Set.range x := by
    rw [← Set.range_comp]; rfl
  have h1 : (1 : ℤ) ∈ Ideal.span (Set.range fun i => x i ^ 2) := by
    rw [hr, h2]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  rw [← mul_one A, ← hc, Finset.mul_sum]
  exact Finset.dvd_sum fun i _ => by
    rw [show A * (c i * x i ^ 2) = c i * (A * x i ^ 2) by ring]
    exact dvd_mul_of_dvd_right (h i) _

/-! ### Divisibility of the Gram entries -/

/-- A Gauss form that is not the zero form has a nonzero coefficient. -/
private theorem cg_coeff_ne_zero {a b c : ℤ} (h : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  obtain ⟨x, y, hv⟩ := h
  apply hv
  rw [eval_gaussForm]; simp [ha, hb, hc]

/-- A triple with nonzero coefficient gives a form with a nonzero value. -/
private theorem cg_nonzero_of_coeff {a b c : ℤ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h1 := hcon 1 0
  have h2 := hcon 0 1
  have h3 := hcon 1 1
  rw [eval_gaussForm] at h1 h2 h3
  have ha : a = 0 := by linarith
  have hc : c = 0 := by linarith
  have hb : b = 0 := by subst ha hc; linarith
  tauto

/-- $m = \gcd(a, 2b, c) \ne 0$ for a nonzero form. -/
private theorem cg_m_ne_zero {a b c : ℤ} (h : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) :
    gcd3 a (2 * b) c ≠ 0 := by
  have : 0 < gcd3 a (2 * b) c := by
    rw [gcd3_pos_iff]
    rcases cg_coeff_ne_zero h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr h)
  omega

/-- **Gauss, *Disq. Arith.* Art. 235, the divisibility facts:** let $F = (A, B, C)$ be
transformed into $f f'$ by the bilinear substitution $(p, q)$ with the six relations of Art. 235 (`GaussRelations`),
$f, f'$ not the zero form, $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$, $N = m m'$, and $\Delta$ defined by
$A p_0 p_3 + B (p_0 q_3 + q_0 p_3) + C q_0 q_3 = b b' + \Delta$. Then $N$ divides
$a a',\ 2ab',\ ac',\ 2ba',\ 4bb',\ 2bc',\ ca',\ 2cb',\ cc',\ 2bb' + 2\Delta,\ 2bb' - 2\Delta$.
(The first nine are the nine products of $a, 2b, c$ with $a', 2b', c'$ up to the factor $2$ of $bb'$; the last two are
the new ones: $N^2 \mid (2bb' + 2\Delta)(2bb' - 2\Delta) = 4b^2b'^2 - 4dd'$ by $\Delta^2 = dd'$, and $N \mid 4bb'$.)
No coprimality and no positivity are used. Differences from the source: none; the statement is taken in this form
(without the other facts of the statement in the historical sources, $N \mid A k^2$ and so on, which are not proved here). -/
@[kb "gauss1801" "Art. 235"]
theorem art235_divisibility {A B C a b c a' b' c' Δ N : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 = b * b' + Δ)
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hN : N = (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) :
    N ∣ a * a' ∧ N ∣ 2 * (a * b') ∧ N ∣ a * c' ∧ N ∣ 2 * (b * a') ∧ N ∣ 4 * (b * b') ∧ N ∣ 2 * (b * c') ∧
    N ∣ c * a' ∧ N ∣ 2 * (c * b') ∧ N ∣ c * c' ∧ N ∣ 2 * (b * b') + 2 * Δ ∧ N ∣ 2 * (b * b') - 2 * Δ := by
  obtain ⟨hT, h0, h1, h2, h3, h4, h5⟩ := hR
  have hsq := art235_delta_sq hT h0 h1 h2 h3 h4 h5 hΔ hf hf'
  have hΔZ : Δ ^ 2 = (b ^ 2 - a * c) * (b' ^ 2 - a' * c') := by
    simp only [gaussDet] at hsq
    exact_mod_cast hsq
  have hm := (dvd_gcd3 ((gcd3 a (2 * b) c : ℕ) : ℤ) a (2 * b) c).mp dvd_rfl
  have hm' := (dvd_gcd3 ((gcd3 a' (2 * b') c' : ℕ) : ℤ) a' (2 * b') c').mp dvd_rfl
  subst hN
  have f1 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ a * a' := mul_dvd_mul hm.1 hm'.1
  have f2 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ 2 * (a * b') := by
    rw [show 2 * (a * b') = a * (2 * b') by ring]; exact mul_dvd_mul hm.1 hm'.2.1
  have f3 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ a * c' := mul_dvd_mul hm.1 hm'.2.2
  have f4 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ 2 * (b * a') := by
    rw [show 2 * (b * a') = (2 * b) * a' by ring]; exact mul_dvd_mul hm.2.1 hm'.1
  have f5 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ 4 * (b * b') := by
    rw [show 4 * (b * b') = (2 * b) * (2 * b') by ring]; exact mul_dvd_mul hm.2.1 hm'.2.1
  have f6 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ 2 * (b * c') := by
    rw [show 2 * (b * c') = (2 * b) * c' by ring]; exact mul_dvd_mul hm.2.1 hm'.2.2
  have f7 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ c * a' := mul_dvd_mul hm.2.2 hm'.1
  have f8 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ 2 * (c * b') := by
    rw [show 2 * (c * b') = c * (2 * b') by ring]; exact mul_dvd_mul hm.2.2 hm'.2.1
  have f9 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ c * c' := mul_dvd_mul hm.2.2 hm'.2.2
  have hs : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣
      (2 * (b * b') + 2 * Δ) + (2 * (b * b') - 2 * Δ) := by
    rw [show (2 * (b * b') + 2 * Δ) + (2 * (b * b') - 2 * Δ) = 4 * (b * b') by ring]; exact f5
  have t1 : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣ (2 * b) * (2 * b) * (a' * c') := by
    rw [show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
      (gcd3 a (2 * b) c : ℤ) * (gcd3 a (2 * b) c : ℤ) * ((gcd3 a' (2 * b') c' : ℤ) * (gcd3 a' (2 * b') c' : ℤ))
      by ring]
    exact mul_dvd_mul (mul_dvd_mul hm.2.1 hm.2.1) (mul_dvd_mul hm'.1 hm'.2.2)
  have t2 : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣ (a * c) * ((2 * b') * (2 * b')) := by
    rw [show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
      (gcd3 a (2 * b) c : ℤ) * (gcd3 a (2 * b) c : ℤ) * ((gcd3 a' (2 * b') c' : ℤ) * (gcd3 a' (2 * b') c' : ℤ))
      by ring]
    exact mul_dvd_mul (mul_dvd_mul hm.1 hm.2.2) (mul_dvd_mul hm'.2.1 hm'.2.1)
  have t3 : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣ 4 * ((a * a') * (c * c')) := by
    refine Dvd.dvd.mul_left ?_ 4
    rw [show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
      (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) * ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ))
      by ring]
    exact mul_dvd_mul f1 f9
  have hp : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣
      (2 * (b * b') + 2 * Δ) * (2 * (b * b') - 2 * Δ) := by
    rw [show (2 * (b * b') + 2 * Δ) * (2 * (b * b') - 2 * Δ) =
      (2 * b) * (2 * b) * (a' * c') + (a * c) * ((2 * b') * (2 * b')) - 4 * ((a * a') * (c * c')) by
      linear_combination (-4) * hΔZ]
    exact dvd_sub (dvd_add t1 t2) t3
  obtain ⟨g1, g2⟩ := cg_split hs hp
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, g1, g2⟩

/-- The divisibility of the Gram entries needed for $N \mid A, 2B, C$. -/
private def GramDvd (N A B C : ℤ) (p q : Fin 4 → ℤ) : Prop :=
  N ∣ gr A B C p q 0 0 ∧ N ∣ gr A B C p q 1 1 ∧ N ∣ gr A B C p q 2 2 ∧ N ∣ gr A B C p q 3 3 ∧
  N ∣ 2 * gr A B C p q 0 1 ∧ N ∣ 2 * gr A B C p q 0 2 ∧ N ∣ 2 * gr A B C p q 0 3 ∧
  N ∣ 2 * gr A B C p q 1 2 ∧ N ∣ 2 * gr A B C p q 1 3 ∧ N ∣ 2 * gr A B C p q 2 3

/-- The divisibility of all Gram entries (needed for $N \mid B$). -/
private def GramDvdFull (N A B C : ℤ) (p q : Fin 4 → ℤ) : Prop :=
  N ∣ gr A B C p q 0 0 ∧ N ∣ gr A B C p q 1 1 ∧ N ∣ gr A B C p q 2 2 ∧ N ∣ gr A B C p q 3 3 ∧
  N ∣ gr A B C p q 0 1 ∧ N ∣ gr A B C p q 0 2 ∧ N ∣ gr A B C p q 0 3 ∧
  N ∣ gr A B C p q 1 2 ∧ N ∣ gr A B C p q 1 3 ∧ N ∣ gr A B C p q 2 3

private theorem cg_gramDvd {A B C a b c a' b' c' N : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hN : N = (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) : GramDvd N A B C p q := by
  obtain ⟨g00, g11, g22, g33, g01, g02, g13, g23, gs⟩ := cg_gram hR.1
  have hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 =
      b * b' + (gr A B C p q 0 3 - b * b') := by simp only [gr]; ring
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11⟩ := art235_divisibility hR hΔ hf hf' hN
  have e03 : gr A B C p q 0 3 = (b * b' + (gr A B C p q 0 3 - b * b')) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g00]; exact f1
  · rw [g11]; exact f3
  · rw [g22]; exact f7
  · rw [g33]; exact f9
  · rw [g01]; exact f2
  · rw [g02]; exact f4
  · rw [show 2 * gr A B C p q 0 3 = 2 * (b * b') + 2 * (gr A B C p q 0 3 - b * b') by ring]; exact f10
  · rw [show 2 * gr A B C p q 1 2 = 2 * (b * b') - 2 * (gr A B C p q 0 3 - b * b') by linarith]; exact f11
  · rw [g13]; exact f6
  · rw [g23]; exact f8

private theorem cg_A_pair {N A B C : ℤ} {p q : Fin 4 → ℤ} (i j : Fin 4) (hi : N ∣ gr A B C p q i i)
    (hj : N ∣ gr A B C p q j j) (hij : N ∣ 2 * gr A B C p q i j) : N ∣ A * mn p q i j ^ 2 := by
  have e : A * mn p q i j ^ 2 = q j ^ 2 * gr A B C p q i i - (q i * q j) * (2 * gr A B C p q i j) +
      q i ^ 2 * gr A B C p q j j := by simp only [gr, mn]; ring
  rw [e]
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hi _) (dvd_mul_of_dvd_right hij _)) (dvd_mul_of_dvd_right hj _)

private theorem cg_B2_pair {N A B C : ℤ} {p q : Fin 4 → ℤ} (i j : Fin 4) (hi : N ∣ gr A B C p q i i)
    (hj : N ∣ gr A B C p q j j) (hij : N ∣ 2 * gr A B C p q i j) : N ∣ 2 * B * mn p q i j ^ 2 := by
  have e : 2 * B * mn p q i j ^ 2 = (-(2 * (q j * p j))) * gr A B C p q i i +
      (q j * p i + q i * p j) * (2 * gr A B C p q i j) + (-(2 * (q i * p i))) * gr A B C p q j j := by
    simp only [gr, mn]; ring
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right hi _) (dvd_mul_of_dvd_right hij _)) (dvd_mul_of_dvd_right hj _)

private theorem cg_B_pair {N A B C : ℤ} {p q : Fin 4 → ℤ} (i j : Fin 4) (hi : N ∣ gr A B C p q i i)
    (hj : N ∣ gr A B C p q j j) (hij : N ∣ gr A B C p q i j) : N ∣ B * mn p q i j ^ 2 := by
  have e : B * mn p q i j ^ 2 = (-(q j * p j)) * gr A B C p q i i +
      (q j * p i + q i * p j) * gr A B C p q i j + (-(q i * p i)) * gr A B C p q j j := by
    simp only [gr, mn]; ring
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right hi _) (dvd_mul_of_dvd_right hij _)) (dvd_mul_of_dvd_right hj _)

private theorem cg_C_pair {N A B C : ℤ} {p q : Fin 4 → ℤ} (i j : Fin 4) (hi : N ∣ gr A B C p q i i)
    (hj : N ∣ gr A B C p q j j) (hij : N ∣ 2 * gr A B C p q i j) : N ∣ C * mn p q i j ^ 2 := by
  have e : C * mn p q i j ^ 2 = p j ^ 2 * gr A B C p q i i - (p i * p j) * (2 * gr A B C p q i j) +
      p i ^ 2 * gr A B C p q j j := by simp only [gr, mn]; ring
  rw [e]
  exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hi _) (dvd_mul_of_dvd_right hij _)) (dvd_mul_of_dvd_right hj _)

/-- $N \mid A, 2B, C$ from the Gram divisibility and the coprimality of the six minors. -/
private theorem cg_abc {N A B C : ℤ} {p q : Fin 4 → ℤ}
    (hcop : ∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) (g : GramDvd N A B C p q) :
    N ∣ A ∧ N ∣ 2 * B ∧ N ∣ C := by
  obtain ⟨d0, d1, d2, d3, s01, s02, s03, s12, s13, s23⟩ := g
  refine ⟨cg_dvd_of_sq (minors p q) hcop ?_, cg_dvd_of_sq (minors p q) hcop ?_,
    cg_dvd_of_sq (minors p q) hcop ?_⟩
  · intro i; fin_cases i
    exacts [cg_A_pair 0 1 d0 d1 s01, cg_A_pair 0 2 d0 d2 s02, cg_A_pair 0 3 d0 d3 s03,
      cg_A_pair 1 2 d1 d2 s12, cg_A_pair 1 3 d1 d3 s13, cg_A_pair 2 3 d2 d3 s23]
  · intro i; fin_cases i
    exacts [cg_B2_pair 0 1 d0 d1 s01, cg_B2_pair 0 2 d0 d2 s02, cg_B2_pair 0 3 d0 d3 s03,
      cg_B2_pair 1 2 d1 d2 s12, cg_B2_pair 1 3 d1 d3 s13, cg_B2_pair 2 3 d2 d3 s23]
  · intro i; fin_cases i
    exacts [cg_C_pair 0 1 d0 d1 s01, cg_C_pair 0 2 d0 d2 s02, cg_C_pair 0 3 d0 d3 s03,
      cg_C_pair 1 2 d1 d2 s12, cg_C_pair 1 3 d1 d3 s13, cg_C_pair 2 3 d2 d3 s23]

/-- $N \mid B$ from the divisibility of all Gram entries and the coprimality of the six minors. -/
private theorem cg_b {N A B C : ℤ} {p q : Fin 4 → ℤ}
    (hcop : ∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) (g : GramDvdFull N A B C p q) : N ∣ B := by
  obtain ⟨d0, d1, d2, d3, s01, s02, s03, s12, s13, s23⟩ := g
  refine cg_dvd_of_sq (minors p q) hcop ?_
  intro i; fin_cases i
  exacts [cg_B_pair 0 1 d0 d1 s01, cg_B_pair 0 2 d0 d2 s02, cg_B_pair 0 3 d0 d3 s03,
    cg_B_pair 1 2 d1 d2 s12, cg_B_pair 1 3 d1 d3 s13, cg_B_pair 2 3 d2 d3 s23]

/-! ### The proper case: all Gram entries divisible -/

/-- If $m \mid a, b, c$ then $m^2 \mid b^2 - ac$. -/
private theorem cg_sq_dvd_det {m a b c : ℤ} (ha : m ∣ a) (hb : m ∣ b) (hc : m ∣ c) : m ^ 2 ∣ b ^ 2 - a * c := by
  obtain ⟨α, rfl⟩ := ha
  obtain ⟨β, rfl⟩ := hb
  obtain ⟨γ, rfl⟩ := hc
  exact ⟨β ^ 2 - α * γ, by ring⟩

/-- If $m \mid a, 2b, c$ and $m^2 \mid b^2 - ac$ then $m \mid b$. (With $a = m\alpha$, $2b = m\beta$, $c = m\gamma$:
$m^2(\beta^2 - 4\alpha\gamma) = 4 (b^2 - ac)$ is divisible by $4m^2$, so $\beta$ is even.) -/
private theorem cg_proper_of_sq {a b c m : ℤ} (ha : m ∣ a) (hb : m ∣ 2 * b) (hc : m ∣ c)
    (hd : m ^ 2 ∣ b ^ 2 - a * c) : m ∣ b := by
  obtain ⟨α, rfl⟩ := ha
  obtain ⟨β, hβ⟩ := hb
  obtain ⟨γ, rfl⟩ := hc
  obtain ⟨z, hz⟩ := hd
  by_cases hm : m = 0
  · subst hm
    have : b = 0 := by simpa using hβ
    simp [this]
  · have h1 : m ^ 2 * (β ^ 2 - 4 * α * γ) = m ^ 2 * (4 * z) := by
      linear_combination 4 * hz - (m * β + 2 * b) * hβ
    have h2 : β ^ 2 - 4 * α * γ = 4 * z := mul_left_cancel₀ (pow_ne_zero 2 hm) h1
    have h3 : Even (β ^ 2) := ⟨2 * (z + α * γ), by linear_combination h2⟩
    obtain ⟨β1, hβ1⟩ := (Int.even_pow' two_ne_zero).mp h3
    refine ⟨β1, ?_⟩
    have : 2 * b = 2 * (m * β1) := by rw [hβ, hβ1]; ring
    linarith

private theorem cg_gramFull {A B C a b c a' b' c' N : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n')
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hN : N = (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ))
    (hb : (gcd3 a (2 * b) c : ℤ) ∣ b) (hb' : (gcd3 a' (2 * b') c' : ℤ) ∣ b') :
    GramDvdFull N A B C p q := by
  obtain ⟨g00, g11, g22, g33, g01, g02, g13, g23, gs⟩ := cg_gram hR.1
  have hΔ : A * p 0 * p 3 + B * (p 0 * q 3 + q 0 * p 3) + C * q 0 * q 3 =
      b * b' + (gr A B C p q 0 3 - b * b') := by simp only [gr]; ring
  obtain ⟨hT, h0, h1, h2, h3, h4, h5⟩ := hR
  have hsq := art235_delta_sq hT h0 h1 h2 h3 h4 h5 hΔ hf hf'
  have hΔZ : (gr A B C p q 0 3 - b * b') ^ 2 = (b ^ 2 - a * c) * (b' ^ 2 - a' * c') := by
    simp only [gaussDet] at hsq
    exact_mod_cast hsq
  have hm := (dvd_gcd3 ((gcd3 a (2 * b) c : ℕ) : ℤ) a (2 * b) c).mp dvd_rfl
  have hm' := (dvd_gcd3 ((gcd3 a' (2 * b') c' : ℕ) : ℤ) a' (2 * b') c').mp dvd_rfl
  subst hN
  have hΔd : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ gr A B C p q 0 3 - b * b' := by
    have h2' : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣
        (gr A B C p q 0 3 - b * b') ^ 2 := by
      rw [hΔZ, show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
        (gcd3 a (2 * b) c : ℤ) ^ 2 * (gcd3 a' (2 * b') c' : ℤ) ^ 2 by ring]
      exact mul_dvd_mul (cg_sq_dvd_det hm.1 hb hm.2.2) (cg_sq_dvd_det hm'.1 hb' hm'.2.2)
    exact (Int.pow_dvd_pow_iff two_ne_zero).mp h2'
  have hbb : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ b * b' := mul_dvd_mul hb hb'
  have d03 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ gr A B C p q 0 3 := by
    rw [show gr A B C p q 0 3 = b * b' + (gr A B C p q 0 3 - b * b') by ring]
    exact dvd_add hbb hΔd
  have d12 : (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) ∣ gr A B C p q 1 2 := by
    rw [show gr A B C p q 1 2 = 2 * (b * b') - gr A B C p q 0 3 by linarith]
    exact dvd_sub (dvd_mul_of_dvd_right hbb 2) d03
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, d03, d12, ?_, ?_⟩
  · rw [g00]; exact mul_dvd_mul hm.1 hm'.1
  · rw [g11]; exact mul_dvd_mul hm.1 hm'.2.2
  · rw [g22]; exact mul_dvd_mul hm.2.2 hm'.1
  · rw [g33]; exact mul_dvd_mul hm.2.2 hm'.2.2
  · rw [g01]; exact mul_dvd_mul hm.1 hb'
  · rw [g02]; exact mul_dvd_mul hb hm'.1
  · rw [g13]; exact mul_dvd_mul hb hm'.2.2
  · rw [g23]; exact mul_dvd_mul hm.2.2 hb'

/-! ### Extracting the relations from `IsCompounded` -/

private theorem cg_dvd_sixGcd {p q : Fin 4 → ℤ} (i : Fin 6) : ((sixGcd p q : ℕ) : ℤ) ∣ minors p q i := by
  unfold sixGcd
  have key : ∀ x y : ℕ, (x ∣ y) → ∀ z : ℤ, (y : ℤ) ∣ z → (x : ℤ) ∣ z := fun x y h z hz =>
    (Int.natCast_dvd_natCast.mpr h).trans hz
  rw [Int.natCast_dvd]
  fin_cases i
  · exact (((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans ((Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))))
  · exact (((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans ((Nat.gcd_dvd_left _ _).trans
      ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))))
  · exact (((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans ((Nat.gcd_dvd_left _ _).trans
      (Nat.gcd_dvd_right _ _)))
  · exact ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (Nat.gcd_dvd_right _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact Nat.gcd_dvd_right _ _

private theorem cg_core {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c')) :
    ∃ (p q : Fin 4 → ℤ) (n n' : ℚ), GaussRelations A B C a b c a' b' c' p q n n' ∧ sixGcd p q = 1 ∧
      (∀ d : ℤ, (∀ i, d ∣ minors p q i) → IsUnit d) := by
  obtain ⟨p, q, hT, hcop, n, n', -, -, h0, h1, h2, h3, h4, h5⟩ := h
  have hR : GaussRelations A B C a b c a' b' c' p q n n' :=
    ⟨hT, by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
      by simpa using h5⟩
  refine ⟨p, q, n, n', hR, ?_, hcop⟩
  have hu : IsUnit ((sixGcd p q : ℕ) : ℤ) := hcop _ (fun i => cg_dvd_sixGcd i)
  simpa using Int.isUnit_iff_natAbs_eq.mp hu

/-! ### The gcd conclusions -/

/-- **Gauss, *Disq. Arith.* Art. 235 conclusion 5 / Art. 245: $\gcd(A, 2B, C) = m m'$.**
If $F = (A, B, C)$ is compounded (`IsCompounded`) of the non-zero forms $f = (a, b, c)$, $f' = (a', b', c')$, then
$\gcd(A, 2B, C) = \gcd(a, 2b, c)\,\gcd(a', 2b', c')$. The inequality "divides $m m'$" is `art245_gcd_dvd`; the new
half $m m' \mid \gcd(A, 2B, C)$ is the Gram divisibility `art235_divisibility` plus the coprimality of the six
numbers. -/
@[kb "gauss1801" "Art. 245"]
theorem art245_gcd_two_eq {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    gcd3 A (2 * B) C = gcd3 a (2 * b) c * gcd3 a' (2 * b') c' := by
  obtain ⟨p, q, n, n', hR, -, hcop⟩ := cg_core h
  apply Nat.dvd_antisymm (art245_gcd_dvd hR.1)
  obtain ⟨hA, hB, hC⟩ := cg_abc hcop (cg_gramDvd hR hf hf' rfl)
  rw [← Int.natCast_dvd_natCast, dvd_gcd3]
  push_cast
  exact ⟨hA, hB, hC⟩

/-- A compounded form of non-zero forms is not the zero form. -/
private theorem cg_form_nonzero {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    ∃ x y : ℤ, (gaussForm A B C).eval x y ≠ 0 := by
  have h2 := art245_gcd_two_eq h hf hf'
  have hpos : 0 < gcd3 A (2 * B) C := by
    rw [h2]
    exact Nat.mul_pos (Nat.pos_of_ne_zero (cg_m_ne_zero hf)) (Nat.pos_of_ne_zero (cg_m_ne_zero hf'))
  rw [gcd3_pos_iff] at hpos
  apply cg_nonzero_of_coeff
  rcases hpos with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr h)

/-- Properness: $\gcd(a, b, c) = \gcd(a, 2b, c)$ iff $\gcd(a, 2b, c) \mid b$. -/
private theorem cg_proper_iff (a b c : ℤ) :
    gcd3 a b c = gcd3 a (2 * b) c ↔ ((gcd3 a (2 * b) c : ℕ) : ℤ) ∣ b := by
  constructor
  · intro h
    have := ((dvd_gcd3 ((gcd3 a b c : ℕ) : ℤ) a b c).mp dvd_rfl).2.1
    rw [h] at this
    exact this
  · intro h
    obtain ⟨ha, -, hc⟩ := (dvd_gcd3 ((gcd3 a (2 * b) c : ℕ) : ℤ) a (2 * b) c).mp dvd_rfl
    have h1 : (gcd3 a (2 * b) c : ℤ) ∣ (gcd3 a b c : ℤ) := (dvd_gcd3 _ a b c).mpr ⟨ha, h, hc⟩
    have h2 : gcd3 a b c ∣ gcd3 a (2 * b) c := by
      rw [← Int.natCast_dvd_natCast, dvd_gcd3]
      obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 a b c) a b c).mp dvd_rfl
      exact ⟨ha, dvd_mul_of_dvd_right hb 2, hc⟩
    exact Nat.dvd_antisymm h2 (Int.natCast_dvd_natCast.mp h1)

/-- If $m m' \mid A, B, C$ for a compounded form, both factors are proper ($m \mid b$ and $m' \mid b'$). -/
private theorem cg_proper_of_abc {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {n n' : ℚ}
    (hR : GaussRelations A B C a b c a' b' c' p q n n') (hk : sixGcd p q = 1)
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hA : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ∣ A)
    (hB : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ∣ B)
    (hC : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ∣ C) :
    (gcd3 a (2 * b) c : ℤ) ∣ b ∧ (gcd3 a' (2 * b') c' : ℤ) ∣ b' := by
  have h4 := (art235_gcd_determinant hR hf hf').2.2.2
  rw [hk] at h4
  simp only [cont3_eq_gcd3, one_pow, mul_one] at h4
  have hD : ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 ∣ ((gaussDet A B C).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, dvd_abs, show gaussDet A B C = B * B - A * C by unfold gaussDet; ring,
      show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
        ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) *
          ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) by ring]
    exact dvd_sub (mul_dvd_mul hB hB) (mul_dvd_mul hA hC)
  rw [h4] at hD
  have hx := hD.trans (Int.gcd_dvd_left _ _)
  have hy := hD.trans (Int.gcd_dvd_right _ _)
  have hm0 : (gcd3 a (2 * b) c : ℤ) ≠ 0 := by exact_mod_cast cg_m_ne_zero hf
  have hm0' : (gcd3 a' (2 * b') c' : ℤ) ≠ 0 := by exact_mod_cast cg_m_ne_zero hf'
  have hm := (dvd_gcd3 ((gcd3 a (2 * b) c : ℕ) : ℤ) a (2 * b) c).mp dvd_rfl
  have hm' := (dvd_gcd3 ((gcd3 a' (2 * b') c' : ℕ) : ℤ) a' (2 * b') c').mp dvd_rfl
  refine ⟨cg_proper_of_sq hm.1 hm.2.1 hm.2.2 ?_, cg_proper_of_sq hm'.1 hm'.2.1 hm'.2.2 ?_⟩
  · rw [show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
      (gcd3 a (2 * b) c : ℤ) ^ 2 * (gcd3 a' (2 * b') c' : ℤ) ^ 2 by ring] at hx
    exact (mul_dvd_mul_iff_right (pow_ne_zero 2 hm0')).mp hx
  · rw [show ((gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ)) ^ 2 =
      (gcd3 a' (2 * b') c' : ℤ) ^ 2 * (gcd3 a (2 * b) c : ℤ) ^ 2 by ring] at hy
    exact (mul_dvd_mul_iff_right (pow_ne_zero 2 hm0)).mp hy

/-- **Gauss, *Disq. Arith.* Art. 245, the gcd conclusions (PROVED):** for $F = (A, B, C)$
compounded directly of non-zero forms $f = (a, b, c)$, $f' = (a', b', c')$ with $m = \gcd(a, 2b, c)$,
$m' = \gcd(a', 2b', c')$: $\gcd(A, 2B, C) = m m'$, and $\gcd(A, B, C) = m m'$ if both $f$ and $f'$ are proper
($\gcd(a, b, c) = m$ and $\gcd(a', b', c') = m'$) and $\gcd(A, B, C) = m m' / 2$ otherwise. This is exactly the
proposition `GaussCompositionGcds` (Art. 235 conclusions 5-6), as stated in the notes of ; no correction
was needed. -/
@[kb "gauss1801" "Art. 245"]
theorem gaussCompositionGcds : GaussCompositionGcds := by
  intro A B C a b c a' b' c' h hf hf'
  have hg := art245_gcd_two_eq h hf hf'
  refine ⟨hg, ?_⟩
  obtain ⟨p, q, n, n', hR, hk, hcop⟩ := cg_core h
  obtain ⟨hA, hB, hC⟩ := cg_abc hcop (cg_gramDvd hR hf hf' rfl)
  have hdvd : gcd3 A B C ∣ gcd3 A (2 * B) C := by
    rw [← Int.natCast_dvd_natCast, dvd_gcd3]
    obtain ⟨ha, hb, hc⟩ := (dvd_gcd3 (gcd3 A B C) A B C).mp dvd_rfl
    exact ⟨ha, dvd_mul_of_dvd_right hb 2, hc⟩
  split_ifs with hc
  · rw [cg_proper_iff, cg_proper_iff] at hc
    have hfull := cg_gramFull hR hf hf' rfl hc.1 hc.2
    have hB' := cg_b hcop hfull
    rw [← hg]
    apply Nat.dvd_antisymm (hg ▸ hdvd)
    · rw [hg, ← Int.natCast_dvd_natCast, dvd_gcd3]
      push_cast
      exact ⟨hA, hB', hC⟩
  · have hne : gcd3 A B C ≠ gcd3 a (2 * b) c * gcd3 a' (2 * b') c' := by
      intro heq
      apply hc
      have hABC := (dvd_gcd3 ((gcd3 A B C : ℕ) : ℤ) A B C).mp dvd_rfl
      rw [heq] at hABC
      push_cast at hABC
      have := cg_proper_of_abc hR hk hf hf' hABC.1 hABC.2.1 hABC.2.2
      exact ⟨(cg_proper_iff a b c).mpr this.1, (cg_proper_iff a' b' c').mpr this.2⟩
    rcases art226_gcd_dichotomy A B C with h1 | h1
    · exact absurd (h1.symm.trans hg) hne
    · rw [hg] at h1
      omega

/-- The form $(a, b, c)$ with $\gcd(a, 2b, c) \ne 0$ is not the zero form. -/
private theorem cg_nonzero_of_gcd3 {a b c : ℤ} (h : gcd3 a (2 * b) c ≠ 0) :
    ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0 := by
  apply cg_nonzero_of_coeff
  have := (gcd3_pos_iff a (2 * b) c).mp (Nat.pos_of_ne_zero h)
  rcases this with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr h)

/-- **Gauss, *Disq. Arith.* Art. 245, composition of orders (PROVED):** if $F$ is
compounded of $f, f'$ and $G$ of $g, g'$ (all four non-zero), $f, g$ have the same order and $f', g'$ have the same
order (`gaussOrder`), then $F$ and $G$ have the same order. Determinant: `art245_det_determined`; $\gcd(A, 2B, C)$ and
$\gcd(A, B, C)$: `gaussCompositionGcds`, whose formulas depend only on the orders of the factors. -/
@[kb "gauss1801" "Art. 245"]
theorem gaussOrderComposition : GaussOrderComposition := by
  intro A B C a b c a' b' c' A₂ B₂ C₂ a₂ b₂ c₂ a₃ b₃ c₃ hF hG hf hf' hg hg' hord hord'
  have hdet := art245_det_determined hF hG hf hf' hg hg' hord hord'
  have hd1 : gcd3 a b c = gcd3 a₂ b₂ c₂ := congrArg (fun t => t.2.1) hord
  have hm : gcd3 a (2 * b) c = gcd3 a₂ (2 * b₂) c₂ := congrArg (fun t => t.2.2) hord
  have hd1' : gcd3 a' b' c' = gcd3 a₃ b₃ c₃ := congrArg (fun t => t.2.1) hord'
  have hm' : gcd3 a' (2 * b') c' = gcd3 a₃ (2 * b₃) c₃ := congrArg (fun t => t.2.2) hord'
  obtain ⟨e1, e2⟩ := gaussCompositionGcds A B C a b c a' b' c' hF hf hf'
  obtain ⟨e3, e4⟩ := gaussCompositionGcds A₂ B₂ C₂ a₂ b₂ c₂ a₃ b₃ c₃ hG hg hg'
  unfold gaussOrder
  refine Prod.ext hdet (Prod.ext ?_ ?_)
  · show gcd3 A B C = gcd3 A₂ B₂ C₂
    rw [e2, e4, hd1, hm, hd1', hm']
  · show gcd3 A (2 * B) C = gcd3 A₂ (2 * B₂) C₂
    rw [e1, e3, hm, hm']

/-- **Gauss, *Disq. Arith.* Art. 245, proper times improper is improper (PROVED):** if
$F$ is compounded of $f, f'$, one properly primitive ($\gcd(a, 2b, c) = 1$) and the other improperly primitive
($\gcd(a, b, c) = 1$, $\gcd(a, 2b, c) = 2$), then $\gcd(A, B, C) = 1$ and $\gcd(A, 2B, C) = 2$ (the form $F$ is
improperly primitive). The statement is `GaussImproperComposition`; the hypotheses force $f, f'$ to be non-zero. -/
@[kb "gauss1801" "Art. 245"]
theorem gaussImproperComposition : GaussImproperComposition := by
  intro A B C a b c a' b' c' h hcase
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hf := cg_nonzero_of_gcd3 (a := a) (b := b) (c := c) (by omega)
    have hf' := cg_nonzero_of_gcd3 (a := a') (b := b') (c := c') (by omega)
    obtain ⟨e1, e2⟩ := gaussCompositionGcds A B C a b c a' b' c' h hf hf'
    rw [h1, h3] at e1
    rw [if_neg (by rw [h2, h3]; omega)] at e2
    rw [h1, h3] at e2
    exact ⟨e2, e1⟩
  · have hf := cg_nonzero_of_gcd3 (a := a) (b := b) (c := c) (by omega)
    have hf' := cg_nonzero_of_gcd3 (a := a') (b := b') (c := c') (by omega)
    obtain ⟨e1, e2⟩ := gaussCompositionGcds A B C a b c a' b' c' h hf hf'
    rw [h2, h3] at e1
    rw [if_neg (by rw [h1, h2]; omega)] at e2
    rw [h2, h3] at e2
    exact ⟨e2, e1⟩

/-- **Gauss, *Disq. Arith.* Art. 235, the divisibility by $M$:** for a form $F = (A, B, C)$
compounded directly of non-zero $f = (a, b, c)$, $f' = (a', b', c')$ and $M = \gcd(A, 2B, C)$: $M = m m'$, hence $M$
divides $a m'$, $2b m'$, $c m'$ and $m m'$ (with $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$). The last three
facts for a general transformation (not compounded) are not claimed. -/
@[kb "gauss1801" "Art. 235"]
theorem art235_M_divisibility {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    gcd3 A (2 * B) C = gcd3 a (2 * b) c * gcd3 a' (2 * b') c' ∧
    (gcd3 A (2 * B) C : ℤ) ∣ a * (gcd3 a' (2 * b') c' : ℤ) ∧
    (gcd3 A (2 * B) C : ℤ) ∣ 2 * b * (gcd3 a' (2 * b') c' : ℤ) ∧
    (gcd3 A (2 * B) C : ℤ) ∣ c * (gcd3 a' (2 * b') c' : ℤ) ∧
    (gcd3 A (2 * B) C : ℤ) ∣ (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) := by
  have hg := art245_gcd_two_eq h hf hf'
  have hm := (dvd_gcd3 ((gcd3 a (2 * b) c : ℕ) : ℤ) a (2 * b) c).mp dvd_rfl
  rw [hg]
  push_cast
  exact ⟨rfl, mul_dvd_mul_right hm.1 _, mul_dvd_mul_right hm.2.1 _,
    mul_dvd_mul_right hm.2.2 _, dvd_rfl⟩

/-! ### Art. 240, step I: determinants of iterated composites -/

/-- Compounded form: the determinant of the first factor is $n^2 D$ with $n > 0$ rational. -/
private theorem cg_det_first {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    ∃ n : ℚ, 0 < n ∧ (gaussDet a b c : ℚ) = n ^ 2 * gaussDet A B C := by
  obtain ⟨p, q, hT, -, n, n', hn, -, h0, h1, h2, h3, h4, h5⟩ := h
  have e1 := disc_mul_sq_of_rel_first hT h3 h4 h5 hf'
  simp only [disc_gaussForm] at e1
  push_cast at e1
  exact ⟨n, hn, by linear_combination e1 / 4⟩

/-- Compounded form: the determinant of the second factor is $n'^2 D$ with $n' > 0$ rational. -/
private theorem cg_det_second {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) :
    ∃ n : ℚ, 0 < n ∧ (gaussDet a' b' c' : ℚ) = n ^ 2 * gaussDet A B C := by
  obtain ⟨p, q, hT, -, n, n', -, hn', h0, h1, h2, h3, h4, h5⟩ := h
  have e1 := disc_mul_sq_of_rel_second hT h0 h1 h2 hf
  simp only [disc_gaussForm] at e1
  push_cast at e1
  exact ⟨n', hn', by linear_combination e1 / 4⟩

/-- **$x$ is a positive rational multiple of $y$** ($x = r y$ with $r > 0$ in $\mathbb Q$): "the same sign, in square
ratio" for integers (both are zero if one is). Used to state that determinants have the same sign in Art. 240. -/
def Art240PositiveMultiple (x y : ℤ) : Prop := ∃ r : ℚ, 0 < r ∧ (x : ℚ) = r * y

private theorem cg_pm_trans {x y z : ℤ} (h1 : Art240PositiveMultiple x y) (h2 : Art240PositiveMultiple y z) :
    Art240PositiveMultiple x z := by
  obtain ⟨r, hr, e1⟩ := h1
  obtain ⟨s, hs, e2⟩ := h2
  exact ⟨r * s, mul_pos hr hs, by rw [e1, e2]; ring⟩

private theorem cg_pm_cancel {x y z : ℤ} (h1 : Art240PositiveMultiple x z) (h2 : Art240PositiveMultiple x y) :
    Art240PositiveMultiple y z := by
  obtain ⟨r, hr, e1⟩ := h1
  obtain ⟨s, hs, e2⟩ := h2
  refine ⟨r / s, div_pos hr hs, ?_⟩
  field_simp
  linarith

private theorem cg_pm_of_sq {x y : ℤ} {n : ℚ} (hn : 0 < n) (h : (x : ℚ) = n ^ 2 * y) :
    Art240PositiveMultiple x y := ⟨n ^ 2, by positivity, h⟩

/-- $|D| = \gcd(d m'^2, d' m^2)$ for a compounded form, with no hypothesis $D \ne 0$. -/
private theorem cg_det_formula {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    (gaussDet A B C).natAbs =
      Int.gcd (gaussDet a b c * ((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)
        (gaussDet a' b' c' * ((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2) := by
  obtain ⟨p, q, n, n', hR, hk, -⟩ := cg_core h
  have h4 := (art235_gcd_determinant hR hf hf').2.2.2
  rw [hk] at h4
  simp only [cont3_eq_gcd3, one_pow, mul_one] at h4
  exact h4

private theorem cg_nat1 (x y z u v w : ℕ) :
    Nat.gcd (Nat.gcd (x * v ^ 2) (y * u ^ 2) * w ^ 2) (z * (u * v) ^ 2) =
      Nat.gcd (Nat.gcd (x * (v ^ 2 * w ^ 2)) (y * (u ^ 2 * w ^ 2))) (z * (u ^ 2 * v ^ 2)) := by
  rw [← Nat.gcd_mul_right]
  have e1 : x * v ^ 2 * w ^ 2 = x * (v ^ 2 * w ^ 2) := by ring
  have e2 : y * u ^ 2 * w ^ 2 = y * (u ^ 2 * w ^ 2) := by ring
  have e3 : z * (u * v) ^ 2 = z * (u ^ 2 * v ^ 2) := by ring
  rw [e1, e2, e3]

private theorem cg_nat2 (x y z u v w : ℕ) :
    Nat.gcd (x * (v * w) ^ 2) (Nat.gcd (y * w ^ 2) (z * v ^ 2) * u ^ 2) =
      Nat.gcd (Nat.gcd (x * (v ^ 2 * w ^ 2)) (y * (u ^ 2 * w ^ 2))) (z * (u ^ 2 * v ^ 2)) := by
  rw [← Nat.gcd_mul_right, ← Nat.gcd_assoc]
  have e1 : x * (v * w) ^ 2 = x * (v ^ 2 * w ^ 2) := by ring
  have e2 : y * w ^ 2 * u ^ 2 = y * (u ^ 2 * w ^ 2) := by ring
  have e3 : z * v ^ 2 * u ^ 2 = z * (u ^ 2 * v ^ 2) := by ring
  rw [e1, e2, e3]

private theorem cg_chain1 (D d d' d'' E : ℤ) (u v w : ℕ)
    (hD : D.natAbs = Int.gcd (d * (v : ℤ) ^ 2) (d' * (u : ℤ) ^ 2))
    (hE : E.natAbs = Int.gcd (D * (w : ℤ) ^ 2) (d'' * ((u * v : ℕ) : ℤ) ^ 2)) :
    E.natAbs = Int.gcd (Int.gcd (d * ((v : ℤ) ^ 2 * (w : ℤ) ^ 2)) (d' * ((u : ℤ) ^ 2 * (w : ℤ) ^ 2)))
      (d'' * ((u : ℤ) ^ 2 * (v : ℤ) ^ 2)) := by
  rw [hE]
  simp only [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, Nat.cast_mul] at hD ⊢
  rw [hD]
  exact cg_nat1 d.natAbs d'.natAbs d''.natAbs u v w

private theorem cg_chain2 (D' d d' d'' E : ℤ) (u v w : ℕ)
    (hD : D'.natAbs = Int.gcd (d' * (w : ℤ) ^ 2) (d'' * (v : ℤ) ^ 2))
    (hE : E.natAbs = Int.gcd (d * ((v * w : ℕ) : ℤ) ^ 2) (D' * (u : ℤ) ^ 2)) :
    E.natAbs = Int.gcd (Int.gcd (d * ((v : ℤ) ^ 2 * (w : ℤ) ^ 2)) (d' * ((u : ℤ) ^ 2 * (w : ℤ) ^ 2)))
      (d'' * ((u : ℤ) ^ 2 * (v : ℤ) ^ 2)) := by
  rw [hE]
  simp only [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast, Nat.cast_mul] at hD ⊢
  rw [hD]
  exact cg_nat2 d.natAbs d'.natAbs d''.natAbs u v w

/-- **Gauss, *Disq. Arith.* Art. 240, step I, determinants of iterated composites
(PROVED).** Let $f = (a, b, c)$, $f' = (a', b', c')$, $f'' = (a'', b'', c'')$ be non-zero forms with determinants
$d, d', d''$ and $m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$, $m'' = \gcd(a'', 2b'', c'')$. Let $F = (A, B, C)$ be
compounded of $f, f'$ (determinant $D$), $\mathfrak F = (A_1, B_1, C_1)$ of $F, f''$ (determinant $\mathfrak D$),
$F' = (A_2, B_2, C_2)$ of $f', f''$ (determinant $D'$) and $\mathfrak F' = (A_3, B_3, C_3)$ of $f, F'$ (determinant
$\mathfrak D'$); the hypotheses are Gauss's four applications of `IsCompounded` (directly, Art. 235). Then:

* $M = \gcd(A, 2B, C) = m m'$ (and $\gcd(A_2, 2B_2, C_2) = m' m''$);
* $|D| = \gcd(d m'^2, d' m^2)$ (and $|D'| = \gcd(d' m''^2, d'' m'^2)$);
* $|\mathfrak D| = |\mathfrak D'| = \gcd(d m'^2 m''^2,\ d' m^2 m''^2,\ d'' m^2 m'^2)$, and $\mathfrak D = \mathfrak D'$;
* the determinants $d, d', d'', D, D', \mathfrak D'$ are all positive rational multiples of $\mathfrak D$ (they have the
  same sign, `Art240PositiveMultiple`; "in square ratio" holds since each ratio is a square of a rational, from
  $d = n^2 D$ etc.).

Differences from the source: Gauss writes $D$ for the determinant with a sign convention; the absolute value appears
here because $\gcd$ is nonnegative, and the sign is recorded by the positive-multiple statements and
$\mathfrak D = \mathfrak D'$. The proof applies the fourth conclusion of Art. 235 (`art235_gcd_determinant`) twice for
each bracketing, with $M = m m'$ from `art245_gcd_two_eq`. -/
@[kb "gauss1801" "Art. 240"]
theorem art240_step_one {A B C a b c a' b' c' a'' b'' c'' A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : ℤ}
    (hF : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hFf : IsCompounded (gaussForm A₁ B₁ C₁) (gaussForm A B C) (gaussForm a'' b'' c''))
    (hF' : IsCompounded (gaussForm A₂ B₂ C₂) (gaussForm a' b' c') (gaussForm a'' b'' c''))
    (hFf' : IsCompounded (gaussForm A₃ B₃ C₃) (gaussForm a b c) (gaussForm A₂ B₂ C₂))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hf'' : ∃ x y : ℤ, (gaussForm a'' b'' c'').eval x y ≠ 0) :
    gcd3 A (2 * B) C = gcd3 a (2 * b) c * gcd3 a' (2 * b') c' ∧
    gcd3 A₂ (2 * B₂) C₂ = gcd3 a' (2 * b') c' * gcd3 a'' (2 * b'') c'' ∧
    (gaussDet A B C).natAbs =
      Int.gcd (gaussDet a b c * ((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)
        (gaussDet a' b' c' * ((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2) ∧
    (gaussDet A₂ B₂ C₂).natAbs =
      Int.gcd (gaussDet a' b' c' * ((gcd3 a'' (2 * b'') c'' : ℕ) : ℤ) ^ 2)
        (gaussDet a'' b'' c'' * ((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2) ∧
    (gaussDet A₁ B₁ C₁).natAbs =
      Int.gcd (Int.gcd
        (gaussDet a b c * (((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2 * ((gcd3 a'' (2 * b'') c'' : ℕ) : ℤ) ^ 2))
        (gaussDet a' b' c' * (((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2 * ((gcd3 a'' (2 * b'') c'' : ℕ) : ℤ) ^ 2)))
        (gaussDet a'' b'' c'' * (((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2 * ((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)) ∧
    (gaussDet A₃ B₃ C₃).natAbs =
      Int.gcd (Int.gcd
        (gaussDet a b c * (((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2 * ((gcd3 a'' (2 * b'') c'' : ℕ) : ℤ) ^ 2))
        (gaussDet a' b' c' * (((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2 * ((gcd3 a'' (2 * b'') c'' : ℕ) : ℤ) ^ 2)))
        (gaussDet a'' b'' c'' * (((gcd3 a (2 * b) c : ℕ) : ℤ) ^ 2 * ((gcd3 a' (2 * b') c' : ℕ) : ℤ) ^ 2)) ∧
    gaussDet A₁ B₁ C₁ = gaussDet A₃ B₃ C₃ ∧
    Art240PositiveMultiple (gaussDet a b c) (gaussDet A₁ B₁ C₁) ∧
    Art240PositiveMultiple (gaussDet a' b' c') (gaussDet A₁ B₁ C₁) ∧
    Art240PositiveMultiple (gaussDet a'' b'' c'') (gaussDet A₁ B₁ C₁) ∧
    Art240PositiveMultiple (gaussDet A B C) (gaussDet A₁ B₁ C₁) ∧
    Art240PositiveMultiple (gaussDet A₂ B₂ C₂) (gaussDet A₁ B₁ C₁) ∧
    Art240PositiveMultiple (gaussDet A₃ B₃ C₃) (gaussDet A₁ B₁ C₁) := by
  have hg1 := art245_gcd_two_eq hF hf hf'
  have hg2 := art245_gcd_two_eq hF' hf' hf''
  have hFnz := cg_form_nonzero hF hf hf'
  have hF'nz := cg_form_nonzero hF' hf' hf''
  have e1 := cg_det_formula hF hf hf'
  have e2 := cg_det_formula hF' hf' hf''
  have e3 := cg_det_formula hFf hFnz hf''
  have e4 := cg_det_formula hFf' hf hF'nz
  rw [hg1] at e3
  rw [hg2] at e4
  have c1 := cg_chain1 _ _ _ _ _ _ _ _ e1 e3
  have c2 := cg_chain2 _ _ _ _ _ _ _ _ e2 e4
  -- signs
  obtain ⟨n1, hn1, s1⟩ := cg_det_first hF hf'
  obtain ⟨n1', hn1', s1'⟩ := cg_det_second hF hf
  obtain ⟨n2, hn2, s2⟩ := cg_det_first hFf hf''
  obtain ⟨n2', hn2', s2'⟩ := cg_det_second hFf hFnz
  obtain ⟨n3, hn3, s3⟩ := cg_det_first hF' hf''
  obtain ⟨n4, hn4, s4⟩ := cg_det_first hFf' hF'nz
  obtain ⟨n4', hn4', s4'⟩ := cg_det_second hFf' hf
  have pD : Art240PositiveMultiple (gaussDet A B C) (gaussDet A₁ B₁ C₁) := cg_pm_of_sq hn2 s2
  have pd : Art240PositiveMultiple (gaussDet a b c) (gaussDet A₁ B₁ C₁) :=
    cg_pm_trans (cg_pm_of_sq hn1 s1) pD
  have pd' : Art240PositiveMultiple (gaussDet a' b' c') (gaussDet A₁ B₁ C₁) :=
    cg_pm_trans (cg_pm_of_sq hn1' s1') pD
  have pd'' : Art240PositiveMultiple (gaussDet a'' b'' c'') (gaussDet A₁ B₁ C₁) := cg_pm_of_sq hn2' s2'
  have pD' : Art240PositiveMultiple (gaussDet A₂ B₂ C₂) (gaussDet A₁ B₁ C₁) :=
    cg_pm_cancel pd' (cg_pm_of_sq hn3 s3)
  have pE' : Art240PositiveMultiple (gaussDet A₃ B₃ C₃) (gaussDet A₁ B₁ C₁) :=
    cg_pm_cancel pd (cg_pm_of_sq hn4 s4)
  refine ⟨hg1, hg2, e1, e2, c1, c2, ?_, pd, pd', pd'', pD, pD', pE'⟩
  -- equality of the two determinants
  have habs : (gaussDet A₁ B₁ C₁).natAbs = (gaussDet A₃ B₃ C₃).natAbs := c1.trans c2.symm
  obtain ⟨r, hr, hrq⟩ := pE'
  have habsQ : |((gaussDet A₃ B₃ C₃ : ℤ) : ℚ)| = |((gaussDet A₁ B₁ C₁ : ℤ) : ℚ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs, ← Int.natCast_natAbs, ← Int.natCast_natAbs, habs]
  by_cases h0 : gaussDet A₁ B₁ C₁ = 0
  · have : (gaussDet A₃ B₃ C₃ : ℚ) = 0 := by rw [hrq, h0]; simp
    rw [h0]; exact_mod_cast this.symm
  · have hpos : 0 < |((gaussDet A₁ B₁ C₁ : ℤ) : ℚ)| := abs_pos.mpr (by exact_mod_cast h0)
    rw [hrq, abs_mul, abs_of_pos hr] at habsQ
    have hr1 : r = 1 := by
      have : (r - 1) * |((gaussDet A₁ B₁ C₁ : ℤ) : ℚ)| = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpos.ne'
    rw [hr1, one_mul] at hrq
    exact_mod_cast hrq.symm

end QuadFormsKB.Historical.Gauss
