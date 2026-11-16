import QuadFormsKB.Historical.Gauss.Forms

/-!
# Reduced forms of negative determinant (Disquisitiones Arithmeticae, Arts. 171, 172, 223)

(Art. 223, the choice of one representing form per class; here Rule I, $D < 0$),
resting on (Art. 171, every form is properly equivalent to a reduced one) and 
(Art. 172, when two reduced forms are properly equivalent).

**Gauss's definition** (Art. 171): a form $(A, B, C) = A x^2 + 2Bxy + Cy^2$ of negative determinant $-\Delta$ is
*reduced* if $A \le \sqrt{4\Delta/3}$, $|B| \le A/2$ and $A \le C$ (`GaussReduced`). In the library's coefficients
$a x^2 + b x y + c y^2$ ($b = 2B$) the last two conditions read $|b| \le a \le c$ (`IsReduced`), and the first is a
consequence of them (`gaussReduced_iff`).

* `exists_reduced` (Art. 171): every positive definite form is properly equivalent to a reduced form.
* `art172_eq_or_opposite` (Art. 172): two distinct properly equivalent reduced positive definite forms are opposite,
  $(a, b, c)$ and $(a, -b, c)$, and either ambiguous ($|b| = a$, Gauss's $2B = \pm A$) or have $a = c$.
* `art223_rule_one` (Art. 223, Rule I): each class contains exactly one reduced form whose middle coefficient is
  $\ge 0$ whenever its opposite lies in the same class; this is Gauss's representative ("if a class contains two
  reduced forms, take the one with positive middle term").
* `art223_rule_one_gauss`: the same in Gauss's own terms, for his forms $(A, B, C)$ of negative determinant.

The statements are for **positive** forms; Gauss also treats negative forms of negative determinant (whose reduced
forms are the negatives of positive reduced forms). That restriction is recorded as a loose end.

The proofs are elementary (Lagrange's descent on the first coefficient, and the inequality
$f(x, y) \ge (a - |b| + c)\min(x^2, y^2)$ for reduced $f$). They are written from scratch for the library's
`BinQF`; Tau Ceti's `TauCeti.BinaryQuadraticForm` reduction (Chris Birkbeck) proves the same facts through the
modular fundamental domain and was not used.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **Reduced** (Gauss, *Disq. Arith.* Art. 171, in the library's coefficients): $|b| \le a \le c$ for
$f = a x^2 + b x y + c y^2$. For Gauss's form $(A, B, C)$ ($b = 2B$) this is $|2B| \le A \le C$. -/
@[kb "gauss1801" "Art. 171, p. 198"]
def IsReduced (f : BinQF) : Prop := |f.b| ≤ f.a ∧ f.a ≤ f.c

/-- **Gauss's definition of a reduced form** (*Disq. Arith.* Art. 171, p. 198), verbatim: for $(A, B, C)$ of
determinant $B^2 - AC = -\Delta < 0$: $A \le \sqrt{4\Delta/3}$ (written $3A^2 \le 4\Delta$, with $A \ge 0$),
$|B| \le A/2$ (written $2|B| \le A$) and $A \le C$. -/
@[kb "gauss1801" "Art. 171, p. 198"]
def GaussReduced (A B C : ℤ) : Prop :=
  0 ≤ A ∧ 3 * A ^ 2 ≤ 4 * (A * C - B ^ 2) ∧ 2 * |B| ≤ A ∧ A ≤ C

/-- The first coefficient of `subst p q r s f` is the value `f(p, r)`. -/
theorem a_subst (p q r s : ℤ) (f : BinQF) : (subst p q r s f).a = f.eval p r := by
  simp only [subst, a_mk, eval_eq]

/-- Proper equivalence preserves positive definiteness. -/
theorem posDef_of_sl {f g : BinQF} (hf : f.PosDef) (h : SLEquiv f g) : g.PosDef := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  intro x y hxy
  rw [eval_subst]
  apply hf
  intro h0
  simp only [Prod.mk.injEq] at h0
  apply hxy
  have hx : x = 0 := by
    have : x = s * (p * x + q * y) - q * (r * x + s * y) := by linear_combination (-x) * hd
    rw [this, h0.1, h0.2]; ring
  have hy : y = 0 := by
    have : y = p * (r * x + s * y) - r * (p * x + q * y) := by linear_combination (-y) * hd
    rw [this, h0.1, h0.2]; ring
  rw [hx, hy]

/-- Proper equivalence preserves the discriminant. -/
theorem disc_eq_of_sl {f g : BinQF} (h : SLEquiv f g) : g.disc = f.disc := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  rw [disc_subst, hd]; ring

theorem a_pos_of_posDef {f : BinQF} (hf : f.PosDef) : 0 < f.a := by
  have := hf 1 0 (by simp)
  simpa [eval_eq] using this

/-- Core lower bound for a reduced form. -/
theorem eval_ge_abs {f : BinQF} (hr : IsReduced f) (x y : ℤ) :
    f.a * |x| ^ 2 - f.a * |x| * |y| + f.c * |y| ^ 2 ≤ f.eval x y := by
  obtain ⟨hb, hac⟩ := hr
  have h1 := neg_abs_le (f.b * x * y)
  rw [abs_mul, abs_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right hb (mul_nonneg (abs_nonneg x) (abs_nonneg y))
  rw [eval_eq, ← sq_abs x, ← sq_abs y] at *
  nlinarith [abs_mul_abs_self x, abs_mul_abs_self y, sq_abs x, sq_abs y]

theorem ge_c_of_reduced {f : BinQF} (ha : 0 < f.a) (hr : IsReduced f) {x y : ℤ} (hy : y ≠ 0) :
    f.c ≤ f.eval x y := by
  have h := eval_ge_abs hr x y
  have hac := hr.2
  have hv : 1 ≤ |y| := Int.one_le_abs hy
  have hu := abs_nonneg x
  generalize |x| = u at *
  generalize |y| = v at *
  rcases le_or_gt v u with huv | huv
  · nlinarith [mul_nonneg ha.le (mul_nonneg hu (sub_nonneg.mpr huv)), mul_nonneg (by linarith : (0:ℤ) ≤ f.c) (by nlinarith : (0:ℤ) ≤ v ^ 2 - 1)]
  · nlinarith [mul_nonneg ha.le (sq_nonneg u), mul_nonneg (by linarith : (0:ℤ) ≤ f.c - f.a) (mul_nonneg hu (by linarith : (0:ℤ) ≤ v)),
      mul_nonneg (by linarith : (0:ℤ) ≤ f.c) (mul_nonneg (by linarith : (0:ℤ) ≤ v) (by linarith : (0:ℤ) ≤ v - u - 1)),
      mul_nonneg (by linarith : (0:ℤ) ≤ f.c) (by linarith : (0:ℤ) ≤ v - u - 1 + 0)]

theorem ge_a_of_reduced {f : BinQF} (ha : 0 < f.a) (hr : IsReduced f) {x y : ℤ} (hxy : (x, y) ≠ (0, 0)) :
    f.a ≤ f.eval x y := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := fun h => hxy (by simp [h])
    have := Int.one_le_abs hx
    rw [eval_eq]
    have h1 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
    nlinarith [mul_nonneg ha.le (by linarith : (0:ℤ) ≤ x ^ 2 - 1)]
  · have := ge_c_of_reduced ha hr (x := x) hy
    linarith [hr.2]

theorem eq_a_of_reduced {f : BinQF} (ha : 0 < f.a) (hr : IsReduced f) (hlt : f.a < f.c) {x y : ℤ}
    (h : f.eval x y = f.a) : y = 0 ∧ (x = 1 ∨ x = -1) := by
  have hy : y = 0 := by
    by_contra hy
    have := ge_c_of_reduced ha hr (x := x) hy
    linarith
  refine ⟨hy, ?_⟩
  subst hy
  rw [eval_eq] at h
  have : x ^ 2 = 1 := by
    have : f.a * (x ^ 2 - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · linarith
  have habs : |x| = 1 := by nlinarith [sq_abs x, abs_nonneg x]
  exact (abs_eq (by norm_num)).mp habs

theorem conjForm_conjForm (f : BinQF) : conjForm (conjForm f) = f :=
  ext_abc (by simp) (by simp) (by simp)

/-- First coefficients can only grow along a proper equivalence from a reduced form. -/
theorem a_le_of_sl {f g : BinQF} (hr : IsReduced f) (hf : f.PosDef) (h : SLEquiv f g) : f.a ≤ g.a := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  rw [a_subst]
  apply ge_a_of_reduced (a_pos_of_posDef hf) hr
  intro h0
  simp only [Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  simp at hd

theorem a_eq_of_sl {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g)
    (h : SLEquiv f g) : g.a = f.a :=
  le_antisymm (a_le_of_sl hgr (posDef_of_sl hf h) h.symm) (a_le_of_sl hfr hf h)

theorem c_eq_of_sl {f g : BinQF} (h : SLEquiv f g) (ha : g.a = f.a) (hpos : 0 < f.a)
    (hb2 : g.b ^ 2 = f.b ^ 2) : g.c = f.c := by
  have hd := disc_eq_of_sl h
  simp only [disc, ha, hb2] at hd
  have : f.a * (g.c - f.c) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · omega
  · linarith

theorem eq_or_conj_of_sl {f g : BinQF} (h : SLEquiv f g) (ha : g.a = f.a) (hpos : 0 < f.a)
    (hb : g.b = f.b ∨ g.b = -f.b) : g = f ∨ g = conjForm f := by
  have hb2 : g.b ^ 2 = f.b ^ 2 := by rcases hb with hb | hb <;> rw [hb]; ring
  have hc := c_eq_of_sl h ha hpos hb2
  rcases hb with hb | hb
  · exact Or.inl (ext_abc ha hb hc)
  · exact Or.inr (ext_abc (by simpa using ha) (by simpa using hb) (by simpa using hc))

/-- Lemma L of Art. 172: if `f` is reduced with `a < c`, any properly equivalent reduced `g` is `f` or
its opposite (the latter only if `|b| = a`). -/
theorem art172_aux {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g)
    (hac : f.a < f.c) (h : SLEquiv f g) : g = f ∨ (g = conjForm f ∧ |f.b| = f.a) := by
  have hga := a_eq_of_sl hf hfr hgr h
  have hpos := a_pos_of_posDef hf
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  rw [a_subst] at hga
  obtain ⟨hr0, hp⟩ := eq_a_of_reduced hpos hfr hac hga
  subst hr0
  have hps : p * s = 1 := by linarith
  have hs : s = p := by rcases hp with h | h <;> rw [h] at hps ⊢ <;> omega
  have hs' : p = s := hs.symm
  subst hs'
  have hgb : (subst p q 0 p f).b = f.b + 2 * f.a * (p * q) := by
    simp only [subst, b_mk]
    have : p * p = 1 := hps
    linear_combination (f.b) * this
  have h2 := abs_le.mp hfr.1
  have hga' : (subst p q 0 p f).a = f.a := by rw [a_subst]; exact hga
  have h1 := hgr.1
  rw [hga'] at h1
  have h1 := abs_le.mp h1
  rw [hgb] at h1
  by_cases hm : p * q = 0
  · have hb : (subst p q 0 p f).b = f.b := by rw [hgb, hm]; ring
    exact Or.inl (ext_abc hga' hb (c_eq_of_sl h hga' hpos (by rw [hb])))
  · have hcase : p * q ≥ 1 ∨ p * q ≤ -1 := by omega
    have hfb : |f.b| = f.a ∧ (subst p q 0 p f).b = -f.b := by
      rcases hcase with hc | hc
      · have : f.b = -f.a := by nlinarith
        refine ⟨by rw [this]; simp [abs_of_pos hpos], ?_⟩
        rw [hgb]; nlinarith
      · have : f.b = f.a := by nlinarith
        refine ⟨by rw [this]; simp [abs_of_pos hpos], ?_⟩
        rw [hgb]; nlinarith
    refine (eq_or_conj_of_sl h hga' hpos (Or.inr hfb.2)).imp id (fun h => ⟨h, hfb.1⟩)

/-- **Gauss's three conditions are the library's two:** $(A, B, C)$ is reduced in Gauss's sense iff the library
form $A x^2 + 2Bxy + Cy^2$ satisfies $|2B| \le A \le C$; the bound $A \le \sqrt{4\Delta/3}$ follows from the other
two ($3A^2 \le 4AC - 4B^2$ since $4B^2 \le A^2 \le AC$). -/
theorem gaussReduced_iff (A B C : ℤ) : GaussReduced A B C ↔ IsReduced (gaussForm A B C) := by
  simp only [GaussReduced, IsReduced, a_gaussForm, b_gaussForm, c_gaussForm, abs_mul]
  norm_num
  constructor
  · rintro ⟨-, -, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    have h0 := abs_nonneg B
    refine ⟨by linarith, ?_, h2, h3⟩
    nlinarith [sq_abs B, mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℤ) ≤ A)]

/-- **Opposite forms** (*Disq. Arith.* Art. 159): $(a, b, c)$ and $(a, -b, c)$; the library's `conjForm`. -/
theorem conjForm_gaussForm (a b c : ℤ) : conjForm (gaussForm a b c) = gaussForm a (-b) c := by
  exact ext_abc (by simp) (by simp) (by simp)

/-- **Gauss, *Disq. Arith.* Art. 171: every form of negative determinant is properly equivalent to a reduced
form** (here: every positive definite form $f$, any discriminant). -/
@[kb "gauss1801" "Art. 171, pp. 196-198"]
theorem exists_reduced {f : BinQF} (hf : f.PosDef) : ∃ g, SLEquiv f g ∧ IsReduced g := by
  have key : ∀ n : ℕ, ∀ f : BinQF, f.PosDef → f.a.toNat = n → ∃ g, SLEquiv f g ∧ IsReduced g := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn
      have ha := a_pos_of_posDef hf
      set t := f.b + f.a with ht
      have h2a : 0 < 2 * f.a := by linarith
      have e1 := Int.emod_add_mul_ediv t (2 * f.a)
      have e2 := Int.emod_nonneg t h2a.ne'
      have e3 := Int.emod_lt_of_pos t h2a
      set k := -(t / (2 * f.a)) with hk
      set f' := subst 1 k 0 1 f with hf'
      have hs1 : SLEquiv f f' := (sLEquiv_iff _ _).mpr ⟨1, k, 0, 1, by ring, rfl⟩
      have hp' : f'.PosDef := posDef_of_sl hf hs1
      have ha' : f'.a = f.a := by simp [hf', subst]
      have hb' : f'.b = f.b + 2 * f.a * k := by simp [hf', subst]; ring
      have hc' : 0 < f'.c := by
        have := hp' 0 1 (by simp)
        simpa [eval_eq] using this
      have hb1 : -f'.a ≤ f'.b := by rw [hb', ha', hk]; nlinarith
      have hb2 : f'.b ≤ f'.a := by rw [hb', ha', hk]; nlinarith
      by_cases hle : f'.a ≤ f'.c
      · exact ⟨f', hs1, abs_le.mpr ⟨hb1, hb2⟩, hle⟩
      · rw [not_le] at hle
        set f'' := subst 0 (-1) 1 0 f' with hf''
        have hs2 : SLEquiv f' f'' := (sLEquiv_iff _ _).mpr ⟨0, -1, 1, 0, by ring, rfl⟩
        have hp'' : f''.PosDef := posDef_of_sl hp' hs2
        have ha'' : f''.a = f'.c := by simp [hf'', subst]
        obtain ⟨g, hg1, hg2⟩ := ih f''.a.toNat (by
          rw [← hn, ha'', ← ha']; omega) f'' hp'' rfl
        exact ⟨g, hs1.trans (hs2.trans hg1), hg2⟩
  exact key _ f hf rfl

/-- **Gauss, *Disq. Arith.* Art. 172:** if two reduced positive definite forms $f \ne g$ are properly equivalent,
then they are opposite ($g = (a, -b, c)$ for $f = (a, b, c)$) and $f$ is ambiguous ($|b| = a$, Gauss's $2B = \pm A$)
or has equal outer coefficients ($a = c$). -/
@[kb "gauss1801" "Art. 172, pp. 198-200"]
theorem art172_eq_or_opposite {f g : BinQF} (hf : f.PosDef) (hfr : IsReduced f) (hgr : IsReduced g)
    (h : SLEquiv f g) (hne : f ≠ g) : g = conjForm f ∧ (|f.b| = f.a ∨ f.a = f.c) := by
  have hgp := posDef_of_sl hf h
  by_cases hlt : f.a < f.c
  · rcases art172_aux hf hfr hgr hlt h with h1 | ⟨h1, h2⟩
    · exact absurd h1.symm hne
    · exact ⟨h1, Or.inl h2⟩
  have hfe : f.a = f.c := le_antisymm hfr.2 (not_lt.mp hlt)
  by_cases hlt' : g.a < g.c
  · rcases art172_aux hgp hgr hfr hlt' h.symm with h1 | ⟨h1, h2⟩
    · exact absurd h1 hne
    · refine ⟨?_, Or.inr hfe⟩
      rw [h1, conjForm_conjForm]
  · have hge : g.a = g.c := le_antisymm hgr.2 (not_lt.mp hlt')
    have ha := a_eq_of_sl hf hfr hgr h
    have hd := disc_eq_of_sl h
    have hb2 : g.b = f.b ∨ g.b = -f.b := by
      simp only [disc] at hd
      have hgc : g.c = f.a := by linarith
      have : g.b ^ 2 = f.b ^ 2 := by rw [ha, hgc, ← hfe] at hd; linarith
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    rcases eq_or_conj_of_sl h ha (a_pos_of_posDef hf) hb2 with h1 | h1
    · exact absurd h1.symm hne
    · exact ⟨h1, Or.inr hfe⟩

/-- **Gauss, *Disq. Arith.* Art. 223, Rule I (case $D < 0$):** every class of positive
definite forms contains exactly one reduced form $g$ such that, if the opposite form $\bar g = (a, -b, c)$ also lies
in the class (so the class contains two reduced forms), the middle coefficient of $g$ is $\ge 0$ (Gauss: "take the
one with positive middle term"). -/
@[kb "gauss1801" "Art. 223, p. 311"]
theorem art223_rule_one {f : BinQF} (hf : f.PosDef) :
    ∃! g, SLEquiv f g ∧ IsReduced g ∧ (SLEquiv g (conjForm g) → 0 ≤ g.b) := by
  obtain ⟨g, hg1, hg2⟩ := exists_reduced hf
  have hex : ∃ g, SLEquiv f g ∧ IsReduced g ∧ (SLEquiv g (conjForm g) → 0 ≤ g.b) := by
    by_cases hh : SLEquiv g (conjForm g) ∧ g.b < 0
    · refine ⟨conjForm g, hg1.trans hh.1, ?_, fun _ => ?_⟩
      · have := abs_le.mp hg2.1
        exact ⟨by simp only [b_conjForm, a_conjForm, abs_neg]; exact hg2.1,
          by simpa using hg2.2⟩
      · simp only [b_conjForm]; linarith [hh.2]
    · refine ⟨g, hg1, hg2, fun hs => ?_⟩
      by_contra hn
      exact hh ⟨hs, not_le.mp hn⟩
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, hg, fun g2 hg2 => ?_⟩
  by_contra hne
  obtain ⟨h1, r1, p1⟩ := hg
  obtain ⟨h2, r2, p2⟩ := hg2
  have hs : SLEquiv g g2 := h1.symm.trans h2
  have hgp := posDef_of_sl hf h1
  obtain ⟨e, -⟩ := art172_eq_or_opposite hgp r1 r2 hs (Ne.symm hne)
  have c1 : SLEquiv g (conjForm g) := e ▸ hs
  have c2 : SLEquiv g2 (conjForm g2) := by
    rw [e, conjForm_conjForm]; exact c1.symm
  have b1 := p1 c1
  have b2 := p2 c2
  rw [e] at b2
  simp only [b_conjForm] at b2
  apply hne
  have : g2 = g := by
    rw [e]; exact ext_abc (by simp) (by simp; linarith) (by simp)
  exact this

/-- **Art. 223, Rule I, in Gauss's terms:** for a positive form $(a, b, c)$ (Gauss's $a x^2 + 2bxy + cy^2$, $a > 0$)
of negative determinant $b^2 - ac < 0$ there is exactly one reduced form $(A, B, C)$ in Gauss's sense (Art. 171)
properly equivalent to it with $B \ge 0$ whenever $(A, -B, C)$ is also properly equivalent to it. -/
@[kb "gauss1801" "Art. 223, p. 311"]
theorem art223_rule_one_gauss {a b c : ℤ} (ha : 0 < a) (hdet : gaussDet a b c < 0) :
    ∃! t : ℤ × ℤ × ℤ, SLEquiv (gaussForm a b c) (gaussForm t.1 t.2.1 t.2.2) ∧ GaussReduced t.1 t.2.1 t.2.2 ∧
      (SLEquiv (gaussForm a b c) (gaussForm t.1 (-t.2.1) t.2.2) → 0 ≤ t.2.1) := by
  have hf : (gaussForm a b c).PosDef :=
    (posDef_iff_posDef' _).mpr ⟨by simpa using ha, by rw [disc_gaussForm]; linarith⟩
  obtain ⟨g, ⟨h1, h2, h3⟩, huniq⟩ := art223_rule_one hf
  have hev : Even g.b := by
    obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h1
    exact even_b_subst (by simp) p q r s
  obtain ⟨A, B, C, rfl⟩ := (exists_gaussForm_iff g).mpr hev
  refine ⟨(A, B, C), ⟨h1, (gaussReduced_iff _ _ _).mpr h2, fun hc => ?_⟩, ?_⟩
  · rw [← conjForm_gaussForm] at hc
    have := h3 (h1.symm.trans hc)
    simp only [b_gaussForm] at this
    linarith
  · rintro ⟨A', B', C'⟩ ⟨k1, k2, k3⟩
    have := huniq (gaussForm A' B' C') ⟨k1, (gaussReduced_iff _ _ _).mp k2, fun hc => ?_⟩
    · have ha' := congrArg BinQF.a this
      have hb' := congrArg BinQF.b this
      have hc' := congrArg BinQF.c this
      simp only [a_gaussForm, b_gaussForm, c_gaussForm] at ha' hb' hc'
      have : B' = B := by omega
      simp [ha', this, hc']
    · have := k3 (by rw [← conjForm_gaussForm]; exact k1.trans hc)
      simp only [b_gaussForm]; linarith

end QuadFormsKB.Historical.Gauss
