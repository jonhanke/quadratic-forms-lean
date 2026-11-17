import QuadFormsKB.Historical.Gauss.Example161
import QuadFormsKB.Historical.Gauss.ResidueForms
import QuadFormsKB.Historical.Gauss.GenusGroup

/-!
# The principal genus of determinant $-161$ is exactly four classes (*Disq. Arith.* Art. 260)

(Gauss, *Disquisitiones Arithmeticae* (1801), Art. 260, the example $D = -161$);
this closes loose end **a recorded loose end**, the part of `art260_example_161` that was not proved ("exactly these four").

Gauss's forms $(a, b, c)$ of determinant $b^2 - ac = -161$ are the primitive forms of discriminant $-644$, and
`Composition.FormClass (-644)` is the group of their proper classes (positive and negative forms together).

**Proved** (`art260_example_161_exact`), unconditionally: a class lies in the principal genus (equivalently: has
trivial local data, equivalently: is a square in the class group) if and only if it is one of the four classes of
$(1, 0, 161)$, $(2, 1, 81)$, $(9, 1, 18)$, $(9, -1, 18)$.

**Proof.** A form $f$ of the principal genus properly represents a square $w^2$ with $w$ prime to $2D$
(`Composition.exists_eval_sq_of_inPrincipalGenus`), a positive value; as the discriminant is negative, $f$ is then
positive definite (the first coefficient has the sign of every value). So $f$ is properly equivalent to a reduced
form $(a, b, c)$, $|2b| \le a \le c$ (`exists_reduced`); this form is again in the principal genus, so by
Gauss's Art. 233 VI (`art233_six`) it is a quadratic residue of $-161$: there are $g, h$ with $g^2 \equiv a$,
$gh \equiv b$, $h^2 \equiv c$. The reduced forms of determinant $-161$ form a finite list ($a \le 14$, $|b| \le 7$,
$18$ forms); for the $13$ of them other than $(1,0,161)$, $(2,\pm1,81)$, $(9,\pm1,18)$ the residue condition
fails modulo $7$ or modulo $23$ (checked by `decide` in `ZMod 7`, `ZMod 23`; $161 = 7 \cdot 23$). The form
$(2, -1, 81)$ is properly equivalent to $(2, 1, 81)$ ($|2b| = a$).

The class number $16$ of the positive classes is not proved here.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary _root_.QuadFormsKB.Composition _root_.QuadFormsKB.Composition.FormClass

local instance : NonzeroDisc (-644) := ⟨by norm_num, by norm_num⟩

/-- A residue form of determinant $-161$ is a residue form modulo each divisor $p$ of $161$, read in `ZMod p`
(helper). -/
theorem res_zmod {a B c : ℤ} (p : ℕ) (hp : (p : ℤ) ∣ 161) (hdet : gaussDet a B c = -161)
    (h : IsResidueForm 1 a B c (gaussDet a B c)) :
    ∃ g k : ZMod p, g ^ 2 = (a : ZMod p) ∧ g * k = (B : ZMod p) ∧ k ^ 2 = (c : ZMod p) := by
  obtain ⟨g, k, h1, h2, h3⟩ := h
  rw [hdet] at h1 h2 h3
  have hp' : (p : ℤ) ∣ -161 := (dvd_neg).2 hp
  refine ⟨(g : ZMod p), (k : ZMod p), ?_, ?_, ?_⟩
  · have := (ZMod.intCast_eq_intCast_iff _ _ p).2 (Int.ModEq.of_dvd hp' h1)
    simpa using this
  · have := (ZMod.intCast_eq_intCast_iff _ _ p).2 (Int.ModEq.of_dvd hp' h2)
    simpa using this
  · have := (ZMod.intCast_eq_intCast_iff _ _ p).2 (Int.ModEq.of_dvd hp' h3)
    simpa using this

/-- **The $18$ reduced forms $(a, B, c)$ of determinant $-161$** ($|2B| \le a \le c$, $B^2 - ac = -161$)
(helper). -/
theorem reduced_list {a B c : ℤ} (ha : 0 < a) (hac : a ≤ c) (hB1 : -a ≤ 2 * B) (hB2 : 2 * B ≤ a)
    (hdet : B ^ 2 - a * c = -161) :
    (a = 1 ∧ B = 0 ∧ c = 161) ∨ (a = 2 ∧ B = -1 ∧ c = 81) ∨ (a = 2 ∧ B = 1 ∧ c = 81) ∨
    (a = 3 ∧ B = -1 ∧ c = 54) ∨ (a = 3 ∧ B = 1 ∧ c = 54) ∨ (a = 5 ∧ B = -2 ∧ c = 33) ∨
    (a = 5 ∧ B = 2 ∧ c = 33) ∨ (a = 6 ∧ B = -1 ∧ c = 27) ∨ (a = 6 ∧ B = 1 ∧ c = 27) ∨
    (a = 7 ∧ B = 0 ∧ c = 23) ∨ (a = 9 ∧ B = -1 ∧ c = 18) ∨ (a = 9 ∧ B = 1 ∧ c = 18) ∨
    (a = 10 ∧ B = -3 ∧ c = 17) ∨ (a = 10 ∧ B = 3 ∧ c = 17) ∨ (a = 11 ∧ B = -2 ∧ c = 15) ∨
    (a = 11 ∧ B = 2 ∧ c = 15) ∨ (a = 14 ∧ B = -7 ∧ c = 15) ∨ (a = 14 ∧ B = 7 ∧ c = 15) := by
  have h0 : 4 * B ^ 2 ≤ a ^ 2 := by
    have := mul_nonneg (show 0 ≤ a - 2 * B by omega) (show 0 ≤ a + 2 * B by omega)
    nlinarith
  have h0' : a * a ≤ a * c := mul_le_mul_of_nonneg_left hac ha.le
  have h1 : a ≤ 14 := by
    by_contra hc
    replace hc := not_le.1 hc
    nlinarith
  have h2 : -7 ≤ B := by omega
  have h3 : B ≤ 7 := by omega
  have hd2 : B * B - a * c = -161 := by rw [← hdet]; ring
  clear h0 h0' hdet
  have hm : a * c = B * B + 161 := by linarith
  have hc : c = (B * B + 161) / a := (Int.ediv_eq_of_eq_mul_right ha.ne' hm.symm).symm
  subst hc
  clear hd2
  interval_cases a <;> interval_cases B <;> first | (exfalso; omega) | simp

/-- **Reduced residue forms of determinant $-161$** (helper): a reduced form $(a, B, c)$ of determinant $-161$
that is a quadratic residue of $-161$ is one of $(1,0,161)$, $(2,\pm1,81)$, $(9,\pm1,18)$. -/
theorem residue_cases {a B c : ℤ} (ha : 0 < a) (hac : a ≤ c) (hB1 : -a ≤ 2 * B) (hB2 : 2 * B ≤ a)
    (hdet : B ^ 2 - a * c = -161) (hres : IsResidueForm 1 a B c (gaussDet a B c)) :
    (a = 1 ∧ B = 0 ∧ c = 161) ∨ (a = 2 ∧ B = -1 ∧ c = 81) ∨ (a = 2 ∧ B = 1 ∧ c = 81) ∨
    (a = 9 ∧ B = -1 ∧ c = 18) ∨ (a = 9 ∧ B = 1 ∧ c = 18) := by
  have hd : gaussDet a B c = -161 := hdet
  have r7 := res_zmod 7 (by norm_num) hd hres
  have r23 := res_zmod 23 (by norm_num) hd hres
  rcases reduced_list ha hac hB1 hB2 hdet with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals first
    | (simp; done)
    | (exfalso; revert r7; simp only [Int.cast_ofNat, Int.cast_neg]; decide)
    | (exfalso; revert r23; simp only [Int.cast_ofNat, Int.cast_neg]; decide)

/-- A primitive form of discriminant $-644$ in the principal genus is positive definite (helper): it represents
a square $w^2 \ne 0$, a positive value, and $4 a f(x, y) = (2 a x + b y)^2 + 644 y^2$. -/
theorem posDef_of_principal (f : PrimForm (-644)) (hf : InPrincipalGenus f.1) : f.1.PosDef := by
  have hdisc : f.1.disc = -644 := f.2.2
  obtain ⟨w, x, y, -, hw, hv⟩ := exists_eval_sq_of_inPrincipalGenus (f := f.1) (by rw [hdisc]; norm_num) hf
  have hw0 : w ≠ 0 := by
    rintro rfl
    have := Int.isUnit_iff.1 (isCoprime_zero_left.1 hw)
    rw [hdisc] at this
    omega
  have hpos : 0 < f.1.eval x y := by rw [hv]; positivity
  have hd : f.1.b ^ 2 - 4 * f.1.a * f.1.c = -644 := hdisc
  have key : 4 * f.1.a * f.1.eval x y = (2 * f.1.a * x + f.1.b * y) ^ 2 + 644 * y ^ 2 := by
    rw [eval_eq]; linear_combination (-(y ^ 2)) * hd
  refine (posDef_iff_posDef' _).2 ⟨?_, by rw [hdisc]; norm_num⟩
  by_contra hneg
  rcases (not_lt.1 hneg).lt_or_eq with ha | ha
  · have h1 : 4 * f.1.a * f.1.eval x y < 0 := by nlinarith
    nlinarith [sq_nonneg (2 * f.1.a * x + f.1.b * y), sq_nonneg y]
  · rw [ha] at hd; nlinarith [sq_nonneg f.1.b]

/-- **The principal genus of determinant $-161$ is exactly four classes** (the historical sources,
*Disq. Arith.* Art. 260; closes a recorded loose end): every primitive form $f$ of discriminant $-644$ in the
principal genus has the class of $(1,0,161)$, $(2,1,81)$, $(9,1,18)$ or $(9,-1,18)$. -/
theorem principal_genus_exact (f : PrimForm (-644)) (hf : InPrincipalGenus f.1) :
    mk f = gcls 1 0 161 (by decide) ∨ mk f = gcls 2 1 81 (by decide) ∨ mk f = gcls 9 1 18 (by decide) ∨
      mk f = gcls 9 (-1) 18 (by decide) := by
  have hdisc : f.1.disc = -644 := f.2.2
  have hpos := posDef_of_principal f hf
  obtain ⟨g, e, hr⟩ := exists_reduced hpos
  have hgd : g.disc = -644 := (disc_eq_of_sl e).trans hdisc
  have hpg : InPrincipalGenus g := InPrincipalGenus.of_sLEquiv e hf
  have hga : 0 < g.a := a_pos_of_posDef (posDef_of_sl hpos e)
  have hev : Even g.b := by
    have hd : g.b ^ 2 - 4 * g.a * g.c = -644 := hgd
    have : Even (g.b ^ 2) := ⟨2 * g.a * g.c - 322, by linarith⟩
    exact (Int.even_pow' two_ne_zero).1 this
  obtain ⟨a, B, c, rfl⟩ := (exists_gaussForm_iff g).2 hev
  have hdet : B ^ 2 - a * c = -161 := by
    rw [disc_gaussForm] at hgd; unfold gaussDet at hgd; linarith
  have hB := abs_le.1 hr.1
  simp only [a_gaussForm, b_gaussForm] at hB hr hga
  rcases residue_cases hga hr.2 (by linarith [hB.1]) (by linarith [hB.2]) hdet
      (art233_six (a := a) (b := B) (c := c) (by have : gaussDet a B c = -161 := hdet; omega) hpg) with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl (mk_eq_mk.2 e)
  · have e' : SLEquiv f.1 (gaussForm 2 1 81) :=
      e.trans (sl_of (gaussForm 2 (-1) 81) (gaussForm 2 1 81) 1 1 0 1 (by norm_num)
        (by norm_num [gaussForm]) (by norm_num [gaussForm]) (by norm_num [gaussForm]))
    exact Or.inr (Or.inl (mk_eq_mk.2 e'))
  · exact Or.inr (Or.inl (mk_eq_mk.2 e))
  · exact Or.inr (Or.inr (Or.inr (mk_eq_mk.2 e)))
  · exact Or.inr (Or.inr (Or.inl (mk_eq_mk.2 e)))

/-- **Gauss's example, $D = -161$, exactly** (*Disq. Arith.* Art. 260; closes loose end
a recorded loose end). In `Composition.FormClass (-644)` (Gauss's $(a, b, c)$ = library $[a, 2b, c]$), unconditionally:

1. a class $C$ is a square in the class group (equivalently: has trivial local data `globalToLocal`,
   equivalently: its forms lie in the principal genus) **if and only if** $C$ is the class of $(1,0,161)$,
   $(2,1,81)$, $(9,1,18)$ or $(9,-1,18)$;
2. together with everything proved in `art260_example_161`: these four classes are pairwise distinct, the
   first is the unit class, and the doubling relations of Gauss's table hold.

Differences from the source: none; Gauss's statement concerns positive forms, and here positive and negative forms
are counted together; the negative forms (all in other genera) are excluded in the proof. The class number $16$ is
not proved. -/
@[kb "gauss1801" "Art. 260"]
theorem art260_example_161_exact :
    (∀ C : FormClass (-644), (∃ C₁ : FormClass (-644), C₁ ^ 2 = C) ↔
      (C = gcls 1 0 161 (by decide) ∨ C = gcls 2 1 81 (by decide) ∨ C = gcls 9 1 18 (by decide) ∨
        C = gcls 9 (-1) 18 (by decide))) ∧
    (∀ C : FormClass (-644), globalToLocal (-644) C = 1 ↔
      (C = gcls 1 0 161 (by decide) ∨ C = gcls 2 1 81 (by decide) ∨ C = gcls 9 1 18 (by decide) ∨
        C = gcls 9 (-1) 18 (by decide))) ∧
    (InPrincipalGenus (gaussForm 1 0 161) ∧ InPrincipalGenus (gaussForm 2 1 81) ∧
      InPrincipalGenus (gaussForm 9 1 18) ∧ InPrincipalGenus (gaussForm 9 (-1) 18)) := by
  have h2 : ∀ C : FormClass (-644), (∃ C₁ : FormClass (-644), C₁ ^ 2 = C) ↔
      (C = gcls 1 0 161 (by decide) ∨ C = gcls 2 1 81 (by decide) ∨ C = gcls 9 1 18 (by decide) ∨
        C = gcls 9 (-1) 18 (by decide)) := by
    intro C
    obtain ⟨f, rfl⟩ := mk_surjective C
    refine ⟨fun hs => principal_genus_exact f ((thm_3_1 f).1 hs), ?_⟩
    rintro (h | h | h | h) <;> rw [h]
    · exact ⟨_, sq1⟩
    · exact ⟨_, sq5⟩
    · exact ⟨_, sq9⟩
    · exact ⟨_, sq13⟩
  exact ⟨h2, fun C => (globalToLocal_eq_one_iff_sq C).trans (h2 C), principal_genus_four⟩

end QuadFormsKB.Historical.Gauss
