import QuadFormsKB.Historical.Gauss.CompositionDeterminants
import QuadFormsKB.Historical.Gauss.Determinants

/-!
# Composition of orders (Disquisitiones Arithmeticae, Art. 245)

(Art. 245: forms compounded of forms of given orders lie in one order).

Forms are Gauss's: $F = (A, B, C)$, $f = (a, b, c)$, $f' = (a', b', c')$ (`gaussForm`, library middle coefficient
$2B$, $2b$, $2b'$), determinants $D = B^2 - AC$, $d = b^2 - ac$, $d' = b'^2 - a'c'$, and
$m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$ (`gcd3 a (2 * b) c`). The *order* of a form is
`gaussOrder` $= (\text{determinant}, \gcd(a, b, c), \gcd(a, 2b, c))$ (Art. 226). "Compounded" is `IsCompounded`
(directly, Art. 235; both $n, n' > 0$).

## What is proved

* `art245_det_determined` (**the determinant part of Gauss's claim**): if $F$ is compounded of $f, f'$ and $G$ of
  $g, g'$, none of the four factors being the zero form, and $f, g$ have the same determinant and the same
  $\gcd(a, 2b, c)$, and so do $f', g'$, then $F$ and $G$ have the same determinant. (By Art. 235, fourth conclusion,
  $|D| = \gcd(d m'^2, d' m^2)$, and $d = n^2 D$ with $n > 0$ gives the sign of $D$ from that of $d$.)
* `art245_gcd_dvd`: $\gcd(A, 2B, C)$ divides $m m'$ whenever $F$ is transformed into $f f'$ by a bilinear
  substitution (no coprimality or relations used).
* `art245_properly_primitive` (the first sentence of Gauss's last claim): if $f$ and $f'$ are properly primitive
  ($m = m' = 1$) then $\gcd(A, 2B, C) = 1$ and $\gcd(A, B, C) = 1$, i.e. $F$ is properly primitive.

## What is stated but not proved

The lower bound $m m' \mid \gcd(A, 2B, C)$ (Art. 235, conclusions 5-6) is not in the library, and so the full order
statement (also the $\gcd(A, B, C)$ part) and the improper case are stated as named propositions:
`GaussCompositionGcds`, `GaussOrderComposition`, `GaussImproperComposition`. Missing exactly: for $F$ compounded of
$f, f'$, $\gcd(A, 2B, C) = m m'$, and $\gcd(A, B, C) = m m'$ if both factors are proper ($\gcd(a, b, c) = m$,
$\gcd(a', b', c') = m'$) and $m m' / 2$ otherwise. In terms of the Gram entries $g_{ij}$ of $F$ on the four
vectors $(p_i, q_i)$ (they are $a a', \dots, c c'$ and $b b' \pm \Delta$) what is missing is $m m' \mid 2(b b' \pm \Delta)$.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition

/-- The two ways of writing the content agree: `cont3 a b c = gcd3 a b c`. -/
theorem cont3_eq_gcd3 (a b c : ℤ) : cont3 a b c = gcd3 a b c := by
  simp [cont3, gcd3, Int.gcd]

/-- Bezout for three integers: $\gcd(a, b, c) = \alpha a + \beta b + \gamma c$ for some integers. -/
private theorem gcd3_bezout (a b c : ℤ) :
    ∃ α β γ : ℤ, (gcd3 a b c : ℤ) = α * a + β * b + γ * c := by
  obtain ⟨s, t, hst⟩ : ∃ s t : ℤ, ((Int.gcd a b : ℕ) : ℤ) = a * s + b * t :=
    ⟨_, _, Int.gcd_eq_gcd_ab a b⟩
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, ((Int.gcd (Int.gcd a b : ℤ) c : ℕ) : ℤ) =
      ((Int.gcd a b : ℕ) : ℤ) * u + c * v := ⟨_, _, Int.gcd_eq_gcd_ab _ _⟩
  refine ⟨s * u, t * u, v, ?_⟩
  unfold gcd3
  linear_combination huv + u * hst

/-- If $d$ divides every product $x y$ with $x \in \{a, b, c\}$, $y \in \{a', b', c'\}$, then
$d \mid \gcd(a, b, c) \gcd(a', b', c')$. -/
private theorem dvd_gcd3_mul {d a b c a' b' c' : ℤ}
    (h : ∀ x y : ℤ, (x = a ∨ x = b ∨ x = c) → (y = a' ∨ y = b' ∨ y = c') → d ∣ x * y) :
    d ∣ (gcd3 a b c : ℤ) * (gcd3 a' b' c' : ℤ) := by
  obtain ⟨α, β, γ, hm⟩ := gcd3_bezout a b c
  obtain ⟨α', β', γ', hm'⟩ := gcd3_bezout a' b' c'
  obtain ⟨k1, e1⟩ := h a a' (Or.inl rfl) (Or.inl rfl)
  obtain ⟨k2, e2⟩ := h a b' (Or.inl rfl) (Or.inr (Or.inl rfl))
  obtain ⟨k3, e3⟩ := h a c' (Or.inl rfl) (Or.inr (Or.inr rfl))
  obtain ⟨k4, e4⟩ := h b a' (Or.inr (Or.inl rfl)) (Or.inl rfl)
  obtain ⟨k5, e5⟩ := h b b' (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  obtain ⟨k6, e6⟩ := h b c' (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  obtain ⟨k7, e7⟩ := h c a' (Or.inr (Or.inr rfl)) (Or.inl rfl)
  obtain ⟨k8, e8⟩ := h c b' (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
  obtain ⟨k9, e9⟩ := h c c' (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  refine ⟨α * α' * k1 + α * β' * k2 + α * γ' * k3 + β * α' * k4 + β * β' * k5 + β * γ' * k6 +
    γ * α' * k7 + γ * β' * k8 + γ * γ' * k9, ?_⟩
  rw [hm, hm']
  linear_combination α * α' * e1 + α * β' * e2 + α * γ' * e3 + β * α' * e4 + β * β' * e5 + β * γ' * e6 +
    γ * α' * e7 + γ * β' * e8 + γ * γ' * e9

private theorem gcd_dvd_aux {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ} {d : ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q)
    (hA : d ∣ A) (hB : d ∣ 2 * B) (hC : d ∣ C) :
    d ∣ (gcd3 a (2 * b) c : ℤ) * (gcd3 a' (2 * b') c' : ℤ) := by
  have v : ∀ x y x' y' : ℤ,
      d ∣ (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) * (a' * x' ^ 2 + 2 * b' * x' * y' + c' * y' ^ 2) := by
    intro x y x' y'
    have h := hT x y x' y'
    rw [eval_gaussForm, eval_gaussForm, eval_gaussForm] at h
    rw [← h]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hB _) _))
      (dvd_mul_of_dvd_left hC _)
  have cv : ∀ X Y : ℤ, X = Y → d ∣ X → d ∣ Y := fun X Y e h => e ▸ h
  have aa : d ∣ a * a' := cv _ _ (by ring) (v 1 0 1 0)
  have ac : d ∣ a * c' := cv _ _ (by ring) (v 1 0 0 1)
  have ca : d ∣ c * a' := cv _ _ (by ring) (v 0 1 1 0)
  have cc : d ∣ c * c' := cv _ _ (by ring) (v 0 1 0 1)
  have as' : d ∣ a * (a' + 2 * b' + c') := cv _ _ (by ring) (v 1 0 1 1)
  have cs' : d ∣ c * (a' + 2 * b' + c') := cv _ _ (by ring) (v 0 1 1 1)
  have sa : d ∣ (a + 2 * b + c) * a' := cv _ _ (by ring) (v 1 1 1 0)
  have sc : d ∣ (a + 2 * b + c) * c' := cv _ _ (by ring) (v 1 1 0 1)
  have ss : d ∣ (a + 2 * b + c) * (a' + 2 * b' + c') := cv _ _ (by ring) (v 1 1 1 1)
  have ab : d ∣ a * (2 * b') := cv _ _ (by ring) (dvd_sub (dvd_sub as' aa) ac)
  have cb : d ∣ c * (2 * b') := cv _ _ (by ring) (dvd_sub (dvd_sub cs' ca) cc)
  have ba : d ∣ (2 * b) * a' := cv _ _ (by ring) (dvd_sub (dvd_sub sa aa) ca)
  have bc : d ∣ (2 * b) * c' := cv _ _ (by ring) (dvd_sub (dvd_sub sc ac) cc)
  have bb : d ∣ (2 * b) * (2 * b') := by
    refine cv _ _ ?_ (dvd_sub (dvd_sub (dvd_sub (dvd_sub (dvd_sub (dvd_sub (dvd_sub (dvd_sub ss aa) ab) ac) ba) bc) ca)
      cb) cc)
    ring
  apply dvd_gcd3_mul
  rintro x y (rfl | rfl | rfl) (rfl | rfl | rfl)
  exacts [aa, ab, ac, ba, bb, bc, ca, cb, cc]

/-- **Gauss, *Disq. Arith.* Art. 245, the easy half of $\gcd(A, 2B, C) = m m'$:** if the
form $F = (A, B, C)$ is transformed into $f f'$ by a bilinear substitution (`TransformsInto`; in particular if $F$ is
compounded of $f, f'$), then $\gcd(A, 2B, C)$ divides $m m'$, with $m = \gcd(a, 2b, c)$ and $m' = \gcd(a', 2b', c')$.
No relations of Art. 235, no coprimality and no nonvanishing are used. The proof: $g = \gcd(A, 2B, C)$ divides every
value of $F$, hence of $f(x, y) f'(x', y')$; at $(x, y), (x', y') \in \{(1,0), (0,1), (1,1)\}$ this gives that $g$
divides all nine products of $a, 2b, c$ with $a', 2b', c'$, hence their Bezout combination $m m'$. -/
@[kb "gauss1801" "Art. 245"]
theorem art245_gcd_dvd {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q) :
    gcd3 A (2 * B) C ∣ gcd3 a (2 * b) c * gcd3 a' (2 * b') c' := by
  have h := gcd_dvd_aux (d := ((gcd3 A (2 * B) C : ℕ) : ℤ)) hT ((dvd_gcd3 _ A (2 * B) C).mp dvd_rfl).1
    ((dvd_gcd3 _ A (2 * B) C).mp dvd_rfl).2.1 ((dvd_gcd3 _ A (2 * B) C).mp dvd_rfl).2.2
  exact_mod_cast h

/-- **Gauss, *Disq. Arith.* Art. 245: two properly primitive forms compose to a properly
primitive form.** If $\gcd(a, 2b, c) = 1$ and $\gcd(a', 2b', c') = 1$ and $F = (A, B, C)$ is transformed into $f f'$
by a bilinear substitution (in particular if $F$ is compounded of $f, f'$), then $\gcd(A, 2B, C) = 1$ and
$\gcd(A, B, C) = 1$. This is `art245_gcd_dvd` with $m = m' = 1$. -/
@[kb "gauss1801" "Art. 245"]
theorem art245_properly_primitive {A B C a b c a' b' c' : ℤ} {p q : Fin 4 → ℤ}
    (hT : TransformsInto (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') p q)
    (hm : gcd3 a (2 * b) c = 1) (hm' : gcd3 a' (2 * b') c' = 1) :
    gcd3 A (2 * B) C = 1 ∧ gcd3 A B C = 1 := by
  have h := art245_gcd_dvd hT
  rw [hm, hm', mul_one] at h
  have h1 : gcd3 A (2 * B) C = 1 := Nat.dvd_one.mp h
  refine ⟨h1, Nat.dvd_one.mp ?_⟩
  rw [← h1, ← Int.natCast_dvd_natCast, dvd_gcd3]
  have := (dvd_gcd3 ((gcd3 A B C : ℕ) : ℤ) A B C).mp dvd_rfl
  exact ⟨this.1, dvd_mul_of_dvd_right this.2.1 2, this.2.2⟩

/-- Compounded form: $d = n^2 D$ with $n > 0$ rational (determinant of the first factor). -/
private theorem det_sq_first {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) :
    ∃ n : ℚ, 0 < n ∧ (gaussDet a b c : ℚ) = n ^ 2 * gaussDet A B C := by
  obtain ⟨p, q, hT, -, n, n', hn, -, h0, h1, h2, h3, h4, h5⟩ := h
  have e1 := disc_mul_sq_of_rel_first hT h3 h4 h5 hf'
  simp only [disc_gaussForm] at e1
  push_cast at e1
  exact ⟨n, hn, by linear_combination e1 / 4⟩

/-- Compounded form: $d' = n'^2 D$ with $n' > 0$ rational (determinant of the second factor). -/
private theorem det_sq_second {A B C a b c a' b' c' : ℤ}
    (h : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) :
    ∃ n : ℚ, 0 < n ∧ (gaussDet a' b' c' : ℚ) = n ^ 2 * gaussDet A B C := by
  obtain ⟨p, q, hT, -, n, n', -, hn', h0, h1, h2, h3, h4, h5⟩ := h
  have e1 := disc_mul_sq_of_rel_second hT h0 h1 h2 hf
  simp only [disc_gaussForm] at e1
  push_cast at e1
  exact ⟨n', hn', by linear_combination e1 / 4⟩

/-- **Gauss, *Disq. Arith.* Art. 245, the determinant of a compound is determined by the
orders of the factors.** Let $F = (A, B, C)$ be compounded directly of $f = (a, b, c)$ and $f' = (a', b', c')$, and
$G = (A_2, B_2, C_2)$ of $g = (a_2, b_2, c_2)$ and $g' = (a_3, b_3, c_3)$ (`IsCompounded`), none of the four factors
being the zero form. If $f$ and $g$ have the same order (`gaussOrder`: same determinant $d$, same
$\gcd(a, b, c)$, same $\gcd(a, 2b, c)$) and so do $f'$ and $g'$, then $F$ and $G$ have the same determinant:
$D = D_2$. Proof: by Art. 235 (`art235_isCompounded_det`), $|D| = \gcd(d m'^2, d' m^2)$ depends only on
$d, d', m, m'$; and $d = n^2 D$ with $n > 0$ gives $D$ the sign of $d$ (and $D = 0$ iff $d = 0$).

This is only the determinant half of Gauss's claim that $F$ and $G$ lie in the same order; the two $\gcd$ halves
need $\gcd(A, 2B, C) = m m'$ (see `GaussOrderComposition`). -/
@[kb "gauss1801" "Art. 245"]
theorem art245_det_determined {A B C a b c a' b' c' A₂ B₂ C₂ a₂ b₂ c₂ a₃ b₃ c₃ : ℤ}
    (hF : IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c'))
    (hG : IsCompounded (gaussForm A₂ B₂ C₂) (gaussForm a₂ b₂ c₂) (gaussForm a₃ b₃ c₃))
    (hf : ∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) (hf' : ∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0)
    (hg : ∃ x y : ℤ, (gaussForm a₂ b₂ c₂).eval x y ≠ 0) (hg' : ∃ x y : ℤ, (gaussForm a₃ b₃ c₃).eval x y ≠ 0)
    (hord : gaussOrder a b c = gaussOrder a₂ b₂ c₂) (hord' : gaussOrder a' b' c' = gaussOrder a₃ b₃ c₃) :
    gaussDet A B C = gaussDet A₂ B₂ C₂ := by
  have hd : gaussDet a b c = gaussDet a₂ b₂ c₂ := congrArg (fun t => t.1) hord
  have hm : gcd3 a (2 * b) c = gcd3 a₂ (2 * b₂) c₂ := congrArg (fun t => t.2.2) hord
  have hd' : gaussDet a' b' c' = gaussDet a₃ b₃ c₃ := congrArg (fun t => t.1) hord'
  have hm' : gcd3 a' (2 * b') c' = gcd3 a₃ (2 * b₃) c₃ := congrArg (fun t => t.2.2) hord'
  obtain ⟨n, hn, hnd⟩ := det_sq_first hF hf'
  obtain ⟨n₂, hn₂, hnd₂⟩ := det_sq_first hG hg'
  have hdq : (gaussDet a b c : ℚ) = gaussDet a₂ b₂ c₂ := by exact_mod_cast hd
  have hn2 : 0 < n ^ 2 := by positivity
  have hn22 : 0 < n₂ ^ 2 := by positivity
  by_cases hD : gaussDet A B C = 0
  · have h0 : (gaussDet a b c : ℚ) = 0 := by rw [hnd]; simp [hD]
    have h1 : n₂ ^ 2 * (gaussDet A₂ B₂ C₂ : ℚ) = 0 := by rw [← hnd₂, ← hdq, h0]
    have h2 : (gaussDet A₂ B₂ C₂ : ℚ) = 0 := (mul_eq_zero.mp h1).resolve_left hn22.ne'
    rw [hD]; exact_mod_cast h2.symm
  · have hD2 : gaussDet A₂ B₂ C₂ ≠ 0 := by
      intro h2
      apply hD
      have h1 : n ^ 2 * (gaussDet A B C : ℚ) = 0 := by rw [← hnd, hdq, hnd₂]; simp [h2]
      exact_mod_cast (mul_eq_zero.mp h1).resolve_left hn2.ne'
    have e1 := art235_isCompounded_det hF hf hf' hD
    have e2 := art235_isCompounded_det hG hg hg' hD2
    simp only [cont3_eq_gcd3] at e1 e2
    rw [hd, hd', hm, hm'] at e1
    have habs : (gaussDet A B C).natAbs = (gaussDet A₂ B₂ C₂).natAbs := e1.trans e2.symm
    rcases Int.natAbs_eq_natAbs_iff.mp habs with h | h
    · exact h
    · exfalso
      have h1 : (n ^ 2 + n₂ ^ 2) * (gaussDet A B C : ℚ) = 0 := by
        have h'' : (gaussDet A B C : ℚ) = -gaussDet A₂ B₂ C₂ := by exact_mod_cast h
        have h' : (gaussDet A₂ B₂ C₂ : ℚ) = -gaussDet A B C := by linarith
        linear_combination (-1) * hnd + hnd₂ + n₂ ^ 2 * h' + hdq
      have h2 : (gaussDet A B C : ℚ) = 0 :=
        (mul_eq_zero.mp h1).resolve_left (by positivity)
      exact hD (by exact_mod_cast h2)

/-- **Gauss, *Disq. Arith.* Art. 245, the gcd conclusions (stated here; proved as `gaussCompositionGcds`, `CompositionGcd.lean`).** For
$F = (A, B, C)$ compounded directly of non-zero forms $f = (a, b, c)$, $f' = (a', b', c')$ with
$m = \gcd(a, 2b, c)$, $m' = \gcd(a', 2b', c')$ and $M = m m'$:
$\gcd(A, 2B, C) = M$, and $\gcd(A, B, C) = M$ if both $f$ and $f'$ are proper ($\gcd(a, b, c) = m$ and
$\gcd(a', b', c') = m'$) and $\gcd(A, B, C) = M / 2$ otherwise (Art. 235 conclusions 5-6, as in the notes of
). What is proved is only $\gcd(A, 2B, C) \mid M$ (`art245_gcd_dvd`); missing: $M \mid \gcd(A, 2B, C)$,
i.e. (in the Gram entries of Art. 235) $M \mid 2(b b' \pm \Delta)$, and the parity statement for $\gcd(A, B, C)$. -/
@[kb "gauss1801" "Art. 245"]
def GaussCompositionGcds : Prop :=
  ∀ A B C a b c a' b' c' : ℤ,
    IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') →
    (∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) → (∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) →
      gcd3 A (2 * B) C = gcd3 a (2 * b) c * gcd3 a' (2 * b') c' ∧
      gcd3 A B C =
        if gcd3 a b c = gcd3 a (2 * b) c ∧ gcd3 a' b' c' = gcd3 a' (2 * b') c' then
          gcd3 a (2 * b) c * gcd3 a' (2 * b') c'
        else gcd3 a (2 * b) c * gcd3 a' (2 * b') c' / 2

/-- **Gauss, *Disq. Arith.* Art. 245, composition of orders (stated here; proved as `gaussOrderComposition`, `CompositionGcd.lean`).** If
$F$ is compounded of $f, f'$ and $G$ of $g, g'$ (non-zero forms), and $f, g$ have the same order and $f', g'$ have
the same order (`gaussOrder`), then $F$ and $G$ have the same order. Proved: the determinant component
(`art245_det_determined`). Missing: the components $\gcd(A, B, C)$ and $\gcd(A, 2B, C)$, which follow from
`GaussCompositionGcds` (not proved; see there for exactly what is missing). -/
@[kb "gauss1801" "Art. 245"]
def GaussOrderComposition : Prop :=
  ∀ A B C a b c a' b' c' A₂ B₂ C₂ a₂ b₂ c₂ a₃ b₃ c₃ : ℤ,
    IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') →
    IsCompounded (gaussForm A₂ B₂ C₂) (gaussForm a₂ b₂ c₂) (gaussForm a₃ b₃ c₃) →
    (∃ x y : ℤ, (gaussForm a b c).eval x y ≠ 0) → (∃ x y : ℤ, (gaussForm a' b' c').eval x y ≠ 0) →
    (∃ x y : ℤ, (gaussForm a₂ b₂ c₂).eval x y ≠ 0) → (∃ x y : ℤ, (gaussForm a₃ b₃ c₃).eval x y ≠ 0) →
    gaussOrder a b c = gaussOrder a₂ b₂ c₂ → gaussOrder a' b' c' = gaussOrder a₃ b₃ c₃ →
      gaussOrder A B C = gaussOrder A₂ B₂ C₂

/-- **Gauss, *Disq. Arith.* Art. 245, proper times improper (stated here; proved as `gaussImproperComposition`, `CompositionGcd.lean`).** If
$F$ is compounded of $f, f'$, one properly primitive ($\gcd(a, 2b, c) = 1$) and the other improperly primitive
($\gcd(a, b, c) = 1$, $\gcd(a, 2b, c) = 2$), then $F$ is improperly primitive: $\gcd(A, B, C) = 1$ and
$\gcd(A, 2B, C) = 2$. Proved: only $\gcd(A, 2B, C) \mid 2$ (`art245_gcd_dvd`); missing the lower bound
$2 \mid \gcd(A, 2B, C)$ (see `GaussCompositionGcds`). -/
@[kb "gauss1801" "Art. 245"]
def GaussImproperComposition : Prop :=
  ∀ A B C a b c a' b' c' : ℤ,
    IsCompounded (gaussForm A B C) (gaussForm a b c) (gaussForm a' b' c') →
    ((gcd3 a (2 * b) c = 1 ∧ gcd3 a' b' c' = 1 ∧ gcd3 a' (2 * b') c' = 2) ∨
      (gcd3 a b c = 1 ∧ gcd3 a (2 * b) c = 2 ∧ gcd3 a' (2 * b') c' = 1)) →
      gcd3 A B C = 1 ∧ gcd3 A (2 * B) C = 2

end QuadFormsKB.Historical.Gauss

