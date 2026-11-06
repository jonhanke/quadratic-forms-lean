/-
# Cassels, Appendix B, §3 (p. 374) and §2 (p. 370): genera of one determinant, and the class number $h(D)$ for $D > 0$

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*).

## Part 1 (namespace `QuadFormsKB.Siegel`): §3, p. 374

Cassels remarks that two genera of the same determinant need not contain the same number of classes, and that two classes
of one genus need not have the same number of automorphs; this is the reason for the weight
$W = \sum 1/o^{+}(f)$ (`pweight`). Setting: classically integral positive definite forms $Q$ (`IsClassicallyIntegral`,
`IntQF.PosDef`), proper classes (`pgenusClasses`, `ProperIntEquiv`), proper automorphs (`AutPlus`), determinant of
Cassels' matrix (`casselsMat`, entries $\tfrac12 H_{ij}$). Both remarks are proved by explicit examples.

* `exists_genera_same_det_different_class_number`: in $n = 2$ variables, $Q = 2x_0^2 + 2x_0x_1 + 6x_1^2$ and
  $Q' = 3x_0^2 + 2x_0x_1 + 4x_1^2$ both have Cassels determinant $11$, the genus of $Q$ has exactly one proper class
  (`pgenusClasses_ex374Even`) and the genus of $Q'$ has at least two (`not_properIntEquiv_ex374Odd`: $Q'$ is not properly
  equivalent to $3x_0^2 - 2x_0x_1 + 4x_1^2$, which is improperly equivalent to it and so in its genus).
  ($Q = 2\,(x_0^2 + x_0x_1 + 3x_1^2)$ is not primitive; the genus of $Q'$ is that of primitive forms of discriminant $-44$,
  which has class number $3$, but only "$\ne 1$" is needed and proved.)
  The proof that the genus of $Q$ is a single proper class is a self-contained reduction argument (`reduce_ex374_aux`):
  every form in the genus has all values even (`dvd_eval_of_sameGenus`), positive definite and of discriminant $-44$
  (`SameGenus.posDef`, `SameGenus.det_hessian_eq`), and the reduction algorithm lands on $Q$.
* `exists_genus_different_aut_counts`: in $n = 3$ variables, $x_0^2 + x_1^2 + 7x_2^2$ and
  $x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ are in one genus (a certified $3$-neighbour,
  `Kneser.Examples.sameGenus_Q₁_Q₂`) and have $8$ and $4$ proper automorphs respectively (the full automorph groups have
  orders $16$ and $8$, `Kneser.Examples.card_aut_Q₁`, `card_aut_Q₂`, and in odd dimension $-1$ is improper).

Indices are 0-based (`Fin n`, variables $x_0, \dots, x_{n-1}$).

## Part 2 (namespace `QuadFormsKB.Cassels`): §2, p. 370, (2.3)(i), $h(D)$ for $D > 0$

`hPos D` is the number of proper classes of primitive integral binary forms of discriminant $D$ (the library's
`Composition.FormClass D`, Cassels, Ch. 14, §1). It is finite (`finite_hPos`; the reduction theory for indefinite forms
is in `Ch14/Group.lean`, `Composition.FormClass.finite`). Comparison with the case $D < 0$ of Cassels' (ii), which
counts classes of *positive definite* forms (`Binary.slSetoid`, `Binary.card_slClasses`): for $D < 0$ the primitive
forms of discriminant $D$ are positive or negative definite, and $f \mapsto -f$ exchanges the two kinds, so
`hPos_eq_two_mul_of_neg` shows $\texttt{hPos}\ D = 2 \cdot \#\{\text{classes of positive definite primitive forms}\}$.
Thus one definition (all primitive forms) does not serve both cases; (ii) is the half of it consisting of the positive
definite classes.

**Not formalized.** The value of $h(D)$ for any particular $D > 0$ (needs a computation of the class group of an indefinite
discriminant) and the class number formula (`Binary.classNumberFormula_pos` is in the library separately).
-/
import QuadFormsKB.Siegel.KneserExample
import QuadFormsKB.Literature.Cassels.Ch9Sec6Weight
import QuadFormsKB.Literature.Cassels.Ch9.Ex6Ex15
import QuadFormsKB.Literature.Cassels.Ch14.Group
import QuadFormsKB.Binary.GenusMass
import QuadFormsKB.Binary.SiegelNonPrimitive
import QuadFormsKB.Binary.ClassBijection

open Matrix

namespace QuadFormsKB.Siegel

open QuadFormsKB.BinQF QuadFormsKB.Binary

/-! ### Genera of one determinant with different numbers of classes -/

/-- Helper: reduction of the forms $a x^2 + b xy + c y^2$ with $a, b, c$ even, $a > 0$ and discriminant $-44$ to
$2x^2 + 2xy + 6y^2$ by proper substitutions. Arguments: `N` bounds `a.toNat` (the induction is on this bound), and
`a b c` are the coefficients (Gauss convention, so the Cassels matrix has off-diagonal entry $b/2$). The two steps are
the shift $x \mapsto x + ty$ making $|b| \le a$ and, if then $c < a$, the proper swap $(a, b, c) \mapsto (c, -b, a)$. -/
theorem reduce_ex374_aux : ∀ (N : ℕ) (a b c : ℤ), a.toNat ≤ N → 0 < a → b ^ 2 - 4 * a * c = -44 → 2 ∣ a → 2 ∣ b →
    2 ∣ c → SLEquiv (BinQF.mk a b c) (BinQF.mk 2 2 6) := by
  intro N
  induction N with
  | zero => intro a b c h ha; omega
  | succ N ih =>
    intro a b c hN ha hd h2a h2b h2c
    set q : ℤ := (b + a) / (2 * a) with hq
    have hdm := Int.emod_def (b + a) (2 * a)
    have hm0 := Int.emod_nonneg (b + a) (show 2 * a ≠ 0 by omega)
    have hm1 := Int.emod_lt_of_pos (b + a) (show 0 < 2 * a by omega)
    set t : ℤ := -q with ht
    set b' : ℤ := b + 2 * a * t with hb'
    set c' : ℤ := a * t ^ 2 + b * t + c with hc'
    have hb1 : -a ≤ b' ∧ b' ≤ a := by
      rw [← hq] at hdm
      constructor <;> nlinarith
    have hd' : b' ^ 2 - 4 * a * c' = -44 := by
      rw [hb', hc']
      linarith [hd, show (b + 2 * a * t) ^ 2 - 4 * a * (a * t ^ 2 + b * t + c) = b ^ 2 - 4 * a * c by ring]
    have h1 : SLEquiv (BinQF.mk a b c) (BinQF.mk a b' c') := by
      refine (sLEquiv_iff _ _).mpr ⟨1, t, 0, 1, by ring, ext_abc ?_ ?_ ?_⟩
      · simp
      · simp [hb']; ring
      · simp [hc']
    have h2b' : 2 ∣ b' := by
      rw [hb']; exact dvd_add h2b (dvd_mul_of_dvd_left (dvd_mul_right 2 a) t)
    have h2c' : 2 ∣ c' := by
      rw [hc']
      exact dvd_add (dvd_add (dvd_mul_of_dvd_left h2a _) (dvd_mul_of_dvd_left h2b _)) h2c
    have hcpos : 0 < c' := by
      by_contra hcn
      push Not at hcn
      nlinarith [sq_nonneg b']
    by_cases hlt : c' < a
    · have h2 : SLEquiv (BinQF.mk a b' c') (BinQF.mk c' (-b') a) := by
        refine (sLEquiv_iff _ _).mpr ⟨0, -1, 1, 0, by ring, ext_abc ?_ ?_ ?_⟩
        · simp
        · simp
        · simp
      exact h1.trans (h2.trans (ih c' (-b') a (by omega) hcpos (by linarith) h2c' (by omega) h2a))
    · push Not at hlt
      have h3 : a ≤ 3 := by nlinarith [hb1.1, hb1.2]
      have ha2 : a = 2 := by omega
      subst ha2
      have hc6 : b' = 2 ∨ b' = -2 := by
        have : b' = 0 ∨ b' = 2 ∨ b' = -2 := by omega
        rcases this with h | h | h
        · rw [h] at hd'; omega
        · exact Or.inl h
        · exact Or.inr h
      rcases hc6 with h | h
      · rw [h] at hd' h1
        have : c' = 6 := by omega
        rw [this] at h1
        exact h1
      · rw [h] at hd' h1
        have hc6 : c' = 6 := by omega
        rw [hc6] at h1
        refine h1.trans ((sLEquiv_iff _ _).mpr ⟨1, 1, 0, 1, by ring, ext_abc ?_ ?_ ?_⟩)
        · simp
        · simp
        · simp

/-- **The form $2x_0^2 + 2x_0x_1 + 6x_1^2$** ($= 2\,(x_0^2 + x_0x_1 + 3x_1^2)$, Cassels matrix
$\begin{pmatrix} 2 & 1 \\ 1 & 6 \end{pmatrix}$, determinant $11$, not primitive). -/
def ex374Even : BinQF := BinQF.mk 2 2 6

/-- **The form $3x_0^2 + 2x_0x_1 + 4x_1^2$** (Cassels matrix $\begin{pmatrix} 3 & 1 \\ 1 & 4 \end{pmatrix}$,
determinant $11$, primitive). -/
def ex374Odd : BinQF := BinQF.mk 3 2 4

/-- **The form $3x_0^2 - 2x_0x_1 + 4x_1^2$**, the image of `ex374Odd` under the improper substitution $x_1 \mapsto -x_1$. -/
def ex374OddConj : BinQF := BinQF.mk 3 (-2) 4

/-- Helper: `ex374Even` is twice the form $x_0^2 + x_0x_1 + 3x_1^2$. -/
theorem ex374Even_eq_smul : ex374Even = (2 : ℤ) • BinQF.mk 1 1 3 := by
  apply BinQF.ext_abc <;> simp [ex374Even, BinQF.a, BinQF.b, BinQF.c, BinQF.mk, QuadForm.ofUpper]

/-- Helper: a binary form $a x^2 + b xy + c y^2$ with $b$ even is classically integral (its Cassels matrix
$\begin{pmatrix} a & b/2 \\ b/2 & c \end{pmatrix}$ is integral). Arguments: the coefficients `a b c` and `hb : 2 ∣ b`. -/
theorem isClassicallyIntegral_binary_of_even {a b c : ℤ} (hb : 2 ∣ b) : IsClassicallyIntegral (BinQF.mk a b c) := by
  apply ci_of_two_dvd_hessian
  intro i j
  fin_cases i <;> fin_cases j <;> simp [BinQF.mk, QuadForm.hessian, QuadForm.ofUpper, hb] <;> omega

/-- Helper: `ex374Even` is positive definite. -/
theorem posDef_ex374Even : IntQF.PosDef ex374Even :=
  (intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr ⟨by simp [ex374Even], by simp [ex374Even, BinQF.disc]⟩)

/-- Helper: `ex374Odd` is positive definite. -/
theorem posDef_ex374Odd : IntQF.PosDef ex374Odd :=
  (intQF_posDef_iff _).mpr ((BinQF.posDef_iff_posDef' _).mpr ⟨by simp [ex374Odd], by simp [ex374Odd, BinQF.disc]⟩)

/-- Helper: the Cassels determinant of `ex374Even` is $11$. -/
theorem det_casselsMat_ex374Even : (casselsMat ex374Even).det = 11 := by
  simp [casselsMat, ex374Even, QuadForm.hessian, QuadForm.ofUpper, BinQF.mk, Matrix.det_fin_two]

/-- Helper: the Cassels determinant of `ex374Odd` is $11$. -/
theorem det_casselsMat_ex374Odd : (casselsMat ex374Odd).det = 11 := by
  simp [casselsMat, ex374Odd, QuadForm.hessian, QuadForm.ofUpper, BinQF.mk, Matrix.det_fin_two]

/-- Helper: **the genus of $2x_0^2 + 2x_0x_1 + 6x_1^2$ is a single proper class.** Every form $f'$ of the genus is
positive definite of discriminant $-44$ with all values even (as the genus of $2\cdot(x_0^2+x_0x_1+3x_1^2)$,
`dvd_eval_of_sameGenus`), hence has even coefficients, and `reduce_ex374_aux` reduces it to `ex374Even` by a proper
substitution. -/
theorem pgenusClasses_ex374Even : pgenusClasses ex374Even = {pclassOf ex374Even} := by
  ext C
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', rfl, hs⟩
    have hpos := SameGenus.posDef posDef_ex374Even hs
    have hdet := SameGenus.det_hessian_eq posDef_ex374Even hs
    have hdisc : BinQF.disc f' = -44 := by
      rw [disc_eq_neg_det_hessian, ← hdet, ← disc_eq_neg_det_hessian]; simp [ex374Even, BinQF.disc]
    obtain ⟨ha, _⟩ := (BinQF.posDef_iff_posDef' _).mp ((intQF_posDef_iff _).mp hpos)
    have hs2 : SameGenus ((2 : ℤ) • BinQF.mk 1 1 3) f' := ex374Even_eq_smul ▸ hs
    have e1 := dvd_eval_of_sameGenus (by norm_num) hs2 ![1, 0]
    have e2 := dvd_eval_of_sameGenus (by norm_num) hs2 ![0, 1]
    have e3 := dvd_eval_of_sameGenus (by norm_num) hs2 ![1, 1]
    change (2 : ℤ) ∣ BinQF.eval f' 1 0 at e1
    change (2 : ℤ) ∣ BinQF.eval f' 0 1 at e2
    change (2 : ℤ) ∣ BinQF.eval f' 1 1 at e3
    rw [BinQF.eval_eq] at e1 e2 e3
    simp at e1 e2 e3
    have hf : f' = BinQF.mk (BinQF.a f') (BinQF.b f') (BinQF.c f') :=
      BinQF.ext_abc (by simp) (by simp) (by simp)
    have key := reduce_ex374_aux (BinQF.a f').toNat (BinQF.a f') (BinQF.b f') (BinQF.c f') le_rfl ha
      (by unfold BinQF.disc at hdisc; linarith) e1 (by omega) e2
    refine pclassOf_eq_pclassOf_iff.mpr ?_
    rw [hf]
    exact key
  · rintro rfl
    exact ⟨_, rfl, SameGenus.refl _⟩

/-- Helper: `ex374Odd` is not properly equivalent to `ex374OddConj`. Indeed a substitution
$\begin{pmatrix} p & q \\ r & s \end{pmatrix}$ of determinant $1$ taking the first to the second has
$3p^2 + 2pr + 4r^2 = 3$, forcing $r = 0$, $ps = 1$, and then the cross coefficient gives $6pq = -4$, impossible. -/
theorem not_properIntEquiv_ex374Odd : ¬ ProperIntEquiv ex374Odd ex374OddConj := by
  intro h
  obtain ⟨p, q, r, s, hd, he⟩ := (sLEquiv_iff _ _).mp h
  have ha := congrArg BinQF.a he
  have hb := congrArg BinQF.b he
  simp [ex374Odd, ex374OddConj] at ha hb
  have hr : r = 0 := by
    by_contra hr0
    have : 0 < r ^ 2 := by positivity
    nlinarith [sq_nonneg (3 * p + r)]
  subst hr
  have hps : p * s = 1 := by linarith
  have : 6 * (p * q) = -4 := by nlinarith
  omega

/-- Helper: `ex374Odd` and `ex374OddConj` are in the same genus (they are $\mathrm{GL}_2(\mathbb Z)$-equivalent, by
$x_1 \mapsto -x_1$). -/
theorem sameGenus_ex374Odd_conj : SameGenus ex374Odd ex374OddConj := by
  refine IntEquiv.sameGenus ?_
  refine (intEquiv_iff _ _).mpr ⟨1, 0, 0, -1, by norm_num, BinQF.ext_abc ?_ ?_ ?_⟩ <;>
    simp [ex374Odd, ex374OddConj]

/-- Helper: the genus of `ex374Odd` does not consist of a single proper class (it contains the classes of `ex374Odd`
and `ex374OddConj`, which differ). -/
theorem ncard_pgenusClasses_ex374Odd_ne_one : (pgenusClasses ex374Odd).ncard ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp h
  have h1 : pclassOf ex374Odd ∈ pgenusClasses ex374Odd := ⟨ex374Odd, rfl, SameGenus.refl _⟩
  have h2 : pclassOf ex374OddConj ∈ pgenusClasses ex374Odd := ⟨ex374OddConj, rfl, sameGenus_ex374Odd_conj⟩
  rw [hx, Set.mem_singleton_iff] at h1 h2
  exact not_properIntEquiv_ex374Odd (pclassOf_eq_pclassOf_iff.mp (h1.trans h2.symm))

/-- **Two genera of the same determinant need not contain the same number of classes** (Cassels, App. B, §3, p. 374).
There are classically integral positive definite binary forms $Q, Q'$ (`QuadForm ℤ 2`) with the same determinant of
Cassels' matrix (`casselsMat`) whose genera contain different numbers of proper classes
(`(pgenusClasses Q).ncard ≠ (pgenusClasses Q').ncard`). Explicitly $Q = 2x_0^2 + 2x_0x_1 + 6x_1^2$ (one proper class in
its genus) and $Q' = 3x_0^2 + 2x_0x_1 + 4x_1^2$ (at least two), both of determinant $11$. -/
@[kb "cassels1978" "App. B, §3, p. 374 (genera of the same determinant with different class numbers)"]
theorem exists_genera_same_det_different_class_number :
    ∃ Q Q' : QuadForm ℤ 2, IsClassicallyIntegral Q ∧ IsClassicallyIntegral Q' ∧ IntQF.PosDef Q ∧ IntQF.PosDef Q' ∧
      (casselsMat Q).det = (casselsMat Q').det ∧ (pgenusClasses Q).ncard ≠ (pgenusClasses Q').ncard := by
  refine ⟨ex374Even, ex374Odd, isClassicallyIntegral_binary_of_even (by norm_num),
    isClassicallyIntegral_binary_of_even (by norm_num), posDef_ex374Even, posDef_ex374Odd,
    by rw [det_casselsMat_ex374Even, det_casselsMat_ex374Odd], ?_⟩
  rw [pgenusClasses_ex374Even, Set.ncard_singleton]
  exact fun h => ncard_pgenusClasses_ex374Odd_ne_one h.symm

/-! ### Classes of one genus with different numbers of automorphs -/

section Automorphs

open QuadFormsKB.Siegel.Kneser.Examples

/-- Helper: $x_0^2 + x_1^2 + 7x_2^2$ is classically integral. -/
theorem isClassicallyIntegral_Q₁ : IsClassicallyIntegral Q₁ := by
  apply ci_of_two_dvd_hessian
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Q₁, QuadForm.hessian, QuadForm.ofUpper]

/-- Helper: $x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ is classically integral. -/
theorem isClassicallyIntegral_Q₂ : IsClassicallyIntegral Q₂ := by
  apply ci_of_two_dvd_hessian
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Q₂, QuadForm.hessian, QuadForm.ofUpper]

/-- Helper: $x_0^2 + x_1^2 + 7x_2^2$ has $8$ proper automorphs ($16$ automorphs, half of them proper as $-1$ is
improper in dimension $3$). -/
theorem card_autPlus_Q₁ : Nat.card (AutPlus Q₁) = 8 := by
  have h := card_aut_eq_mul Q₁
  simp only [Cassels.Ch9Ex6.hasImproperAut_three Q₁, ite_true, card_aut_Q₁] at h
  omega

/-- Helper: $x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ has $4$ proper automorphs ($8$ automorphs, half proper). -/
theorem card_autPlus_Q₂ : Nat.card (AutPlus Q₂) = 4 := by
  have h := card_aut_eq_mul Q₂
  simp only [Cassels.Ch9Ex6.hasImproperAut_three Q₂, ite_true, card_aut_Q₂] at h
  omega

/-- **Two classes of a genus need not have the same number of automorphs** (Cassels, App. B, §3, p. 374). There are
classically integral positive definite ternary forms $Q, Q'$ (`QuadForm ℤ 3`) in the same genus (`SameGenus`) with different
numbers of proper automorphs (`Nat.card (AutPlus Q) ≠ Nat.card (AutPlus Q')`). Explicitly
$Q = x_0^2 + x_1^2 + 7x_2^2$ ($8$ proper automorphs) and $Q' = x_0^2 + 2x_1^2 - 2x_1x_2 + 4x_2^2$ ($4$ proper
automorphs). The genus relation is a certified $3$-neighbour (`Kneser.Examples.sameGenus_Q₁_Q₂`). -/
@[kb "cassels1978" "App. B, §3, p. 374 (classes of one genus with different numbers of automorphs)"]
theorem exists_genus_different_aut_counts :
    ∃ Q Q' : QuadForm ℤ 3, IsClassicallyIntegral Q ∧ IsClassicallyIntegral Q' ∧ IntQF.PosDef Q ∧ IntQF.PosDef Q' ∧
      SameGenus Q Q' ∧ Nat.card (AutPlus Q) ≠ Nat.card (AutPlus Q') :=
  ⟨Q₁, Q₂, isClassicallyIntegral_Q₁, isClassicallyIntegral_Q₂, posDef_Q₁, posDef_Q₂, sameGenus_Q₁_Q₂,
    by rw [card_autPlus_Q₁, card_autPlus_Q₂]; norm_num⟩

end Automorphs

end QuadFormsKB.Siegel

/-! ### $h(D)$ for $D > 0$ -/

namespace QuadFormsKB.Cassels

open QuadFormsKB.BinQF QuadFormsKB.Binary QuadFormsKB.Composition

/-- **$h(D)$, the number of classes of primitive forms of discriminant $D$ for proper equivalence** (Cassels, App. B,
§2, (2.3)(i), p. 370, for $D > 0$): the cardinality of `Composition.FormClass D`, the set of
$\mathrm{SL}_2(\mathbb Z)$-classes of primitive integral binary forms $a x^2 + b xy + c y^2$ of discriminant
$b^2 - 4ac = D$. The argument `D` is the discriminant; the definition makes sense for every integer (it is $0$ for
$D \equiv 2, 3 \pmod 4$ and `Nat.card` of an infinite type for $D = 0$ would be $0$), and Cassels uses it for $D > 0$. -/
@[kb "cassels1978" "App. B, §2, (2.3)(i), p. 370 (h(D) for D > 0)"]
noncomputable def hPos (D : ℤ) : ℕ := Nat.card (FormClass D)

/-- **$h(D)$ is finite, for every non-zero discriminant** (in particular for $D > 0$), i.e. the type of proper classes of
primitive forms of discriminant `D ≠ 0` is finite: `Composition.FormClass.finite` if $D \equiv 0, 1 \pmod 4$ and otherwise
there are no forms at all. -/
@[kb "cassels1978" "App. B, §2, (2.3)(i), p. 370 (h(D) for D > 0 is finite)"]
theorem finite_hPos {D : ℤ} (hD : D ≠ 0) : Finite (FormClass D) := by
  by_cases hmod : D % 4 = 0 ∨ D % 4 = 1
  · have : NonzeroDisc D := ⟨hD, hmod⟩
    exact FormClass.finite
  · have : IsEmpty (FormClass D) := ⟨fun C => by
      obtain ⟨f, _⟩ := FormClass.mk_surjective C
      exact hmod (f.2.2 ▸ BinQF.disc_mod_four f.1)⟩
    infer_instance

/-- Helper: a proper substitution carries a form of negative discriminant to a form whose leading coefficient has the same
sign ($a \cdot a' > 0$, as $4a\,f(p, r) = (2ap + br)^2 - D r^2$). Arguments: `hf : f.disc < 0` and `h : SLEquiv f g`. -/
theorem sign_slEquiv {f g : BinQF} (hf : f.disc < 0) (h : SLEquiv f g) : 0 < f.a * g.a := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  have ha : f.a ≠ 0 := by
    intro h0
    simp only [BinQF.disc, h0] at hf
    nlinarith [sq_nonneg f.b]
  simp only [a_subst]
  have key : 4 * f.a * (f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2) =
      (2 * f.a * p + f.b * r) ^ 2 + (-(f.b ^ 2 - 4 * f.a * f.c)) * r ^ 2 := by ring
  have hpr : p ≠ 0 ∨ r ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at hd
    simp at hd
  have hpos : 0 < 4 * f.a * (f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2) := by
    rw [key]
    unfold BinQF.disc at hf
    by_cases hr : r = 0
    · subst hr
      have hp : p ≠ 0 := by tauto
      have h2 : 2 * f.a * p + f.b * 0 ≠ 0 := by simpa using ⟨ha, hp⟩
      have h3 : 0 < (2 * f.a * p + f.b * 0) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h2))
      simpa using h3
    · have : 0 < (-(f.b ^ 2 - 4 * f.a * f.c)) * r ^ 2 := by
        apply mul_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg (2 * f.a * p + f.b * r)]
  nlinarith

/-- Helper: the negative of a primitive form is primitive. -/
theorem isPrimitive_binNeg {f : BinQF} (h : f.IsPrimitive) : f.neg.IsPrimitive := by
  intro d h1 h2 h3
  apply h d
  · simpa using h1
  · simpa using h2
  · simpa using h3

/-- Helper: $-f$ has the same discriminant as $f$. -/
theorem disc_binNeg (f : BinQF) : f.neg.disc = f.disc := by simp [BinQF.disc]

/-- Helper: $-(-f) = f$. -/
theorem binNeg_binNeg (f : BinQF) : f.neg.neg = f := BinQF.ext_abc (by simp) (by simp) (by simp)

/-- Helper: proper equivalence commutes with $f \mapsto -f$. -/
theorem slEquiv_binNeg {f g : BinQF} (h : SLEquiv f g) : SLEquiv f.neg g.neg := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).mp h
  refine (sLEquiv_iff _ _).mpr ⟨p, q, r, s, hd, BinQF.ext_abc ?_ ?_ ?_⟩ <;> simp <;> ring

/-- Helper: a form of negative discriminant has non-zero leading coefficient. -/
theorem binA_ne_zero_of_disc_neg {f : BinQF} (hf : f.disc < 0) : f.a ≠ 0 := by
  intro h0
  simp only [BinQF.disc, h0] at hf
  nlinarith [sq_nonneg f.b]

/-- Helper: a primitive form of discriminant $D < 0$ has negative discriminant. -/
theorem disc_lt_of_primForm {D : ℤ} (hD : D < 0) (f : PrimForm D) : f.1.disc < 0 := by rw [f.2.2]; exact hD

/-- Helper: the primitive positive definite form (`Binary.PrimPosForm`) with the given coefficients data. Arguments:
`hD : D < 0`, a form `f`, its primitivity `hp`, its discriminant `hd` and the positivity `ha` of its leading coefficient. -/
def mkPrimPos {D : ℤ} (hD : D < 0) (f : BinQF) (hp : f.IsPrimitive) (hd : f.disc = D) (ha : 0 < f.a) :
    PrimPosForm D :=
  ⟨f, hd, (BinQF.posDef_iff_posDef' f).mpr ⟨ha, hd ▸ hD⟩, hp⟩

/-- Helper: a primitive form with positive leading coefficient, as a positive definite form. -/
def posOf {D : ℤ} (hD : D < 0) (f : PrimForm D) (h : 0 < f.1.a) : PrimPosForm D :=
  mkPrimPos hD f.1 f.2.1 f.2.2 h

/-- Helper: the negative of a primitive form with non-positive leading coefficient, as a positive definite form. -/
def negOf {D : ℤ} (hD : D < 0) (f : PrimForm D) (h : ¬ 0 < f.1.a) : PrimPosForm D :=
  mkPrimPos hD f.1.neg (isPrimitive_binNeg f.2.1) ((disc_binNeg _).trans f.2.2)
    (by have := binA_ne_zero_of_disc_neg (disc_lt_of_primForm hD f); simp; omega)

/-- Helper: the map from proper classes of primitive forms of discriminant $D < 0$ to two copies of the proper classes
of positive definite ones: a class goes to the left copy if its forms are positive definite and to the right copy (via
$f \mapsto -f$) otherwise. -/
noncomputable def classToSum {D : ℤ} (hD : D < 0) :
    FormClass D → Quotient (slSetoid D) ⊕ Quotient (slSetoid D) :=
  Quotient.lift (s := primSetoid D) (fun f =>
    if h : 0 < f.1.a then Sum.inl (Quotient.mk (slSetoid D) (posOf hD f h))
    else Sum.inr (Quotient.mk (slSetoid D) (negOf hD f h)))
    (by
      intro f g hfg
      have hs := sign_slEquiv (disc_lt_of_primForm hD f) hfg
      have hfg' : SLEquiv f.1 g.1 := hfg
      by_cases hf : 0 < f.1.a
      · have hg : 0 < g.1.a := by
          by_contra hg
          nlinarith
        simp only [hf, hg, dite_true]
        exact congrArg Sum.inl (Quotient.sound hfg')
      · have hg : ¬ 0 < g.1.a := by
          intro hg
          nlinarith
        simp only [hf, hg, dite_false]
        exact congrArg Sum.inr (Quotient.sound (slEquiv_binNeg hfg')))

/-- Helper: `classToSum` on the class of a form with positive leading coefficient. -/
theorem classToSum_mk_pos {D : ℤ} (hD : D < 0) (g : PrimForm D) (h : 0 < g.1.a) :
    classToSum hD (FormClass.mk g) = Sum.inl (Quotient.mk (slSetoid D) (posOf hD g h)) := by
  simp [classToSum, FormClass.mk, h]

/-- Helper: `classToSum` on the class of a form with non-positive leading coefficient. -/
theorem classToSum_mk_neg {D : ℤ} (hD : D < 0) (g : PrimForm D) (h : ¬ 0 < g.1.a) :
    classToSum hD (FormClass.mk g) = Sum.inr (Quotient.mk (slSetoid D) (negOf hD g h)) := by
  simp [classToSum, FormClass.mk, h]

/-- Helper: the inverse of `classToSum`. -/
noncomputable def sumToClass {D : ℤ} (_hD : D < 0) :
    Quotient (slSetoid D) ⊕ Quotient (slSetoid D) → FormClass D :=
  Sum.elim
    (Quotient.lift (s := slSetoid D) (fun f => FormClass.mk ⟨f.1, f.2.2.2, f.2.1⟩)
      (fun _ _ h => Quotient.sound h))
    (Quotient.lift (s := slSetoid D)
      (fun f => FormClass.mk ⟨f.1.neg, isPrimitive_binNeg f.2.2.2, (disc_binNeg _).trans f.2.1⟩)
      (fun _ _ h => Quotient.sound (slEquiv_binNeg h)))

/-- Helper: the bijection between the proper classes of primitive forms of discriminant $D < 0$ and two copies of the
proper classes of primitive positive definite forms (`classToSum`, `sumToClass`). -/
noncomputable def formClassEquiv {D : ℤ} (hD : D < 0) :
    FormClass D ≃ Quotient (slSetoid D) ⊕ Quotient (slSetoid D) where
  toFun := classToSum hD
  invFun := sumToClass hD
  left_inv := by
    intro C
    induction C using Quotient.inductionOn with
    | h f =>
      by_cases hf : 0 < f.1.a
      · show sumToClass hD (classToSum hD (FormClass.mk f)) = _
        rw [classToSum_mk_pos hD f hf]
        rfl
      · show sumToClass hD (classToSum hD (FormClass.mk f)) = _
        rw [classToSum_mk_neg hD f hf]
        refine Quotient.sound ?_
        show SLEquiv f.1.neg.neg f.1
        rw [binNeg_binNeg]
        exact SLEquiv.refl _
  right_inv := by
    intro x
    rcases x with C | C
    · induction C using Quotient.inductionOn with
      | h f =>
        have hf : 0 < f.1.a := ((BinQF.posDef_iff_posDef' f.1).mp f.2.2.1).1
        show classToSum hD (FormClass.mk (⟨f.1, f.2.2.2, f.2.1⟩ : PrimForm D)) = _
        rw [classToSum_mk_pos hD (⟨f.1, f.2.2.2, f.2.1⟩ : PrimForm D) hf]
        rfl
    · induction C using Quotient.inductionOn with
      | h f =>
        have hf : 0 < f.1.a := ((BinQF.posDef_iff_posDef' f.1).mp f.2.2.1).1
        have hn : ¬ 0 < f.1.neg.a := by simp; omega
        show classToSum hD (FormClass.mk
          (⟨f.1.neg, isPrimitive_binNeg f.2.2.2, (disc_binNeg _).trans f.2.1⟩ : PrimForm D)) = _
        rw [classToSum_mk_neg hD
          (⟨f.1.neg, isPrimitive_binNeg f.2.2.2, (disc_binNeg _).trans f.2.1⟩ : PrimForm D) hn]
        refine congrArg Sum.inr (Quotient.sound ?_)
        show SLEquiv f.1.neg.neg f.1
        rw [binNeg_binNeg]
        exact SLEquiv.refl _

/-- **Comparison of `hPos` with Cassels' (ii) for $D < 0$** (Cassels, App. B, §2, (2.3), p. 370): for a negative
discriminant `D` the primitive forms of discriminant $D$ are positive or negative definite, $f \mapsto -f$ exchanges the
two kinds and respects proper equivalence, hence
$$\texttt{hPos}\ D = 2 \cdot \#\{\text{proper classes of primitive positive definite forms of discriminant } D\},$$
the right-hand cardinality being `Nat.card (Quotient (Binary.slSetoid D))`, which is the class number
$h(D)$ of (ii) for fundamental $D$ (`Binary.card_slClasses`). So one common definition counting all primitive forms
agrees with (ii) only up to the factor $2$; (ii) is the count of positive definite classes. -/
@[kb "cassels1978" "App. B, §2, (2.3), p. 370 (h(D) for D < 0: positive definite classes are half of all classes)"]
theorem hPos_eq_two_mul_of_neg {D : ℤ} (hD : D < 0) :
    hPos D = 2 * Nat.card (Quotient (slSetoid D)) := by
  have hfin : Finite (FormClass D) := finite_hPos hD.ne
  have h1 : Finite (Quotient (slSetoid D) ⊕ Quotient (slSetoid D)) :=
    Finite.of_equiv (FormClass D) (formClassEquiv hD)
  have h2 : Finite (Quotient (slSetoid D)) :=
    Finite.of_injective
      (Sum.inl : Quotient (slSetoid D) → Quotient (slSetoid D) ⊕ Quotient (slSetoid D)) Sum.inl_injective
  rw [hPos, Nat.card_congr (formClassEquiv hD), Nat.card_sum]
  ring

end QuadFormsKB.Cassels
