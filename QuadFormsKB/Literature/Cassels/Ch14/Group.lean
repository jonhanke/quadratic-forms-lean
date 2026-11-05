/-
# Cassels, Chapter 14, §2: the group of classes (Theorem 2.1, Lemma 2.5)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §1–§2, pp. 331–338.

For a discriminant $D \ne 0$, $D \equiv 0, 1 \pmod 4$ (`[NonzeroDisc D]`), `FormClass D` is the set of proper classes of primitive integral forms
$[a, b, c]$ of discriminant $D$ (`PrimForm D`, proper equivalence `Binary.SLEquiv`). Dirichlet's composition
(`Composition.comp` of concordant representatives, `Ch14/Composition.lean`) makes it a finite abelian group
(Theorem 2.1, `instCommGroup`, `finite`):

* $\mathfrak C_1\mathfrak C_2$ is the class of the composition of any concordant representatives (`mk_mul_mk`);
* the unit $\mathfrak E$ is the class of the forms which represent $1$ (`mk_eq_one_iff`), e.g. the principal form
  (1.11) (`principalForm`, `mk_principal`);
* the inverse is the class of the improperly equivalent forms, $[a, b, c]^{-1} = [a, -b, c]$ (`mk_inv`).

This holds for positive and negative $D$; the library's earlier identification with the ideal class group
(`Binary.isFormClassGroup`, `Binary.slClassEquiv`) is for fundamental $D < 0$ and positive definite forms.
-/
import QuadFormsKB.Literature.Cassels.Ch14.Composition

namespace QuadFormsKB.Composition

open BinQF Binary

/-- **Primitive integral binary forms of discriminant $D$** (Cassels, Ch. 14, (1.1)–(1.4), p. 331). -/
@[kb "cassels1978" "Ch. 14, §1, (1.1)–(1.4), p. 331"]
def PrimForm (D : ℤ) : Type := {f : BinQF // f.IsPrimitive ∧ f.disc = D}

/-- **Proper equivalence** on `PrimForm D` (Cassels, Ch. 14, p. 331: "by equivalence class we shall always in this
chapter mean class for proper equivalence"). -/
def primSetoid (D : ℤ) : Setoid (PrimForm D) where
  r f g := SLEquiv f.1 g.1
  iseqv := ⟨fun f => SLEquiv.refl f.1, SLEquiv.symm, SLEquiv.trans⟩

/-- **The proper classes of primitive forms of discriminant $D$** (Cassels' $\mathcal G$, Ch. 14, p. 331). -/
@[kb "cassels1978" "Ch. 14, §1, p. 331 (the set 𝒢 of proper classes)"]
def FormClass (D : ℤ) : Type := Quotient (primSetoid D)

/-- **A non-zero discriminant** (Cassels, Ch. 14, (1.4)–(1.6), p. 331): $D \ne 0$ and $D \equiv 0, 1 \pmod 4$, the
discriminants of integral binary forms (`BinQF.disc_mod_four`). For other $D$ there are no forms and $\mathcal G$ is
empty, so this is the standing hypothesis of the group law. -/
class NonzeroDisc (D : ℤ) : Prop where
  /-- $D \ne 0$. -/
  ne_zero : D ≠ 0
  /-- $D \equiv 0$ or $1 \pmod 4$. -/
  mod_four : D % 4 = 0 ∨ D % 4 = 1

namespace FormClass

variable {D : ℤ}

/-- The class of a primitive form. -/
def mk (f : PrimForm D) : FormClass D := Quotient.mk (primSetoid D) f

theorem mk_eq_mk {f g : PrimForm D} : mk f = mk g ↔ SLEquiv f.1 g.1 := Quotient.eq

theorem mk_surjective : Function.Surjective (mk : PrimForm D → FormClass D) := Quotient.mk_surjective

/-- **The principal form** (Cassels, Ch. 14, (1.11), p. 332): $x^2 - \tfrac14Dy^2$ if $D$ is even and
$x^2 + xy + \tfrac14(1 - D)y^2$ if $D$ is odd; in one formula $[1, \beta, (\beta - D)/4]$ with $\beta = D \bmod 2$. -/
@[kb "cassels1978" "Ch. 14, §1, (1.11), p. 332 (the principal form)"]
def principalForm (D : ℤ) : BinQF := BinQF.mk 1 (D % 2) ((D % 2 - D) / 4)

/-- The principal form has discriminant $D$ (for $D \equiv 0, 1 \bmod 4$) and is primitive. -/
theorem principalForm_spec {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (principalForm D).IsPrimitive ∧ (principalForm D).disc = D := by
  refine ⟨?_, ?_⟩
  · intro d h1 _ _
    simp only [principalForm, a_mk] at h1
    exact isUnit_of_dvd_one h1
  · obtain ⟨k, hk | hk⟩ : ∃ k, D = 4 * k ∨ D = 4 * k + 1 := ⟨D / 4, by omega⟩
    · have h2 : D % 2 = 0 := by omega
      have h3 : (D % 2 - D) / 4 = -k := by omega
      simp only [BinQF.disc, principalForm, a_mk, b_mk, c_mk]
      rw [h3, h2]
      linear_combination (-1 : ℤ) * hk
    · have h2 : D % 2 = 1 := by omega
      have h3 : (D % 2 - D) / 4 = -k := by omega
      simp only [BinQF.disc, principalForm, a_mk, b_mk, c_mk]
      rw [h3, h2]
      linear_combination (-1 : ℤ) * hk

/-- **Replace a representative by a properly equivalent form**: a form properly equivalent to a primitive form of
discriminant $D$ is again primitive of discriminant $D$. -/
def ofEquiv {D : ℤ} (f : PrimForm D) {g : BinQF} (e : SLEquiv f.1 g) : PrimForm D :=
  ⟨g, SLEquiv.isPrimitive e f.2.1, (SLEquiv.disc_eq e).symm.trans f.2.2⟩

theorem val_ofEquiv {D : ℤ} (f : PrimForm D) {g : BinQF} (e : SLEquiv f.1 g) :
    (ofEquiv f e).1 = g := rfl

theorem mk_ofEquiv {D : ℤ} (f : PrimForm D) {g : BinQF} (e : SLEquiv f.1 g) :
    mk (ofEquiv f e) = mk f :=
  mk_eq_mk.2 e.symm

private theorem eta' (f : BinQF) : BinQF.mk f.a f.b f.c = f := ext_abc (by simp) (by simp) (by simp)

/-- The translate $x \mapsto x + ly$ of a primitive form (helper). -/
private theorem exists_translate {D : ℤ} (f : PrimForm D) (l : ℤ) :
    ∃ g : PrimForm D, mk g = mk f ∧ g.1.a = f.1.a ∧ g.1.b = f.1.b + 2 * f.1.a * l ∧
      g.1.c = f.1.a * l ^ 2 + f.1.b * l + f.1.c := by
  have e := sLEquiv_translate f.1.a f.1.b f.1.c l
  rw [eta'] at e
  exact ⟨ofEquiv f e, mk_ofEquiv f e, by simp [val_ofEquiv], by simp [val_ofEquiv],
    by simp [val_ofEquiv]⟩

/-- $2N$ is never a unit of $\mathbb Z$. -/
theorem not_isUnit_two_mul (N : ℤ) : ¬ IsUnit (2 * N) := by
  intro hu
  have h2 : IsUnit (2 : ℤ) := isUnit_of_mul_isUnit_left hu
  rw [Int.isUnit_iff] at h2; omega

/-- An integer prime to $2N$ is non-zero. -/
theorem ne_zero_of_coprime_two_mul {a N : ℤ} (h : IsCoprime a (2 * N)) : a ≠ 0 := by
  rintro rfl
  rw [isCoprime_zero_left] at h
  exact not_isUnit_two_mul N h

variable [NonzeroDisc D]

/-- **Every class has a representative whose first coefficient is prime to a given $M \ne 0$** (Lemma 2.1,
`exists_sLEquiv_a_coprime`). -/
theorem exists_rep_coprime (x : FormClass D) {M : ℤ} (hM : M ≠ 0) :
    ∃ f : PrimForm D, mk f = x ∧ IsCoprime f.1.a M := by
  obtain ⟨f, rfl⟩ := mk_surjective x
  obtain ⟨g, e, hg⟩ := exists_sLEquiv_a_coprime f.2.1 hM
  exact ⟨ofEquiv f e, mk_ofEquiv f e, hg⟩

/-- **Representatives with $ac \ne 0$:** every class contains a form $[a, b, c]$ with $a$ prime to $2D$ and
$c \ne 0$ (translate $x \mapsto x + ly$, $l \in \{0, \pm 1\}$). -/
theorem exists_rep_ac_ne_zero (x : FormClass D) :
    ∃ f : PrimForm D, mk f = x ∧ IsCoprime f.1.a (2 * D) ∧ f.1.c ≠ 0 := by
  obtain ⟨f, hf, hc⟩ := exists_rep_coprime x (M := 2 * D) (mul_ne_zero two_ne_zero NonzeroDisc.ne_zero)
  have ha := ne_zero_of_coprime_two_mul hc
  by_cases h0 : f.1.c = 0
  · by_cases h1 : f.1.a + f.1.b = 0
    · obtain ⟨g, hg, hga, -, hgc⟩ := exists_translate f (-1)
      refine ⟨g, hg.trans hf, by rw [hga]; exact hc, ?_⟩
      rw [hgc, h0]
      intro h
      apply ha
      linarith
    · obtain ⟨g, hg, hga, -, hgc⟩ := exists_translate f 1
      refine ⟨g, hg.trans hf, by rw [hga]; exact hc, ?_⟩
      rw [hgc, h0]
      intro h
      apply h1
      linarith
  · exact ⟨f, hf, hc, h0⟩

/-- **Lemma 2.3 for classes:** any two classes have concordant representatives. -/
theorem exists_concordant_reps (x y : FormClass D) :
    ∃ g₁ g₂ : PrimForm D, mk g₁ = x ∧ mk g₂ = y ∧ Concordant g₁.1 g₂.1 := by
  obtain ⟨f₁, rfl⟩ := mk_surjective x
  obtain ⟨f₂, rfl⟩ := mk_surjective y
  obtain ⟨g₁, g₂, e₁, e₂, hc, -, -⟩ := exists_concordant f₁.2.1 f₂.2.1 (f₁.2.2.trans f₂.2.2.symm)
    (by rw [f₁.2.2]; exact NonzeroDisc.ne_zero) (M := 1) (hM := one_ne_zero)
  exact ⟨ofEquiv f₁ e₁, ofEquiv f₂ e₂, mk_ofEquiv f₁ e₁, mk_ofEquiv f₂ e₂, hc⟩

/-- **Three classes have representatives $[a_j, b, *]$ with a common middle coefficient and pairwise coprime
$a_1, a_2, a_3$** (Cassels, Ch. 14, proof of Thm. 2.1, p. 337). -/
theorem exists_triple_reps (x y z : FormClass D) :
    ∃ g₁ g₂ g₃ : PrimForm D, mk g₁ = x ∧ mk g₂ = y ∧ mk g₃ = z ∧ g₁.1.b = g₂.1.b ∧ g₂.1.b = g₃.1.b ∧
      g₁.1.a * g₂.1.a * g₃.1.a ≠ 0 ∧ IsCoprime g₁.1.a g₂.1.a ∧ IsCoprime (g₁.1.a * g₂.1.a) g₃.1.a := by
  have hD0 : D ≠ 0 := NonzeroDisc.ne_zero
  obtain ⟨f₁, rfl⟩ := mk_surjective x
  obtain ⟨f₂, rfl⟩ := mk_surjective y
  obtain ⟨g₁, g₂, e₁, e₂, hc, hcop12, -⟩ := exists_concordant f₁.2.1 f₂.2.1 (f₁.2.2.trans f₂.2.2.symm)
    (by rw [f₁.2.2]; exact hD0) (M := 1) (hM := one_ne_zero)
  have hne12 : g₁.a * g₂.a ≠ 0 := hc.1
  obtain ⟨f₃, hf₃, hcop3⟩ := exists_rep_coprime z (M := 2 * (D * (g₁.a * g₂.a)))
    (mul_ne_zero two_ne_zero (mul_ne_zero hD0 hne12))
  have ha3 : f₃.1.a ≠ 0 := ne_zero_of_coprime_two_mul hcop3
  have hcop123 : IsCoprime (g₁.a * g₂.a) f₃.1.a :=
    (hcop3.of_isCoprime_of_dvd_right
      (⟨2 * D, by ring⟩ : g₁.a * g₂.a ∣ 2 * (D * (g₁.a * g₂.a)))).symm
  have hD1 : g₁.disc = D := (SLEquiv.disc_eq e₁).symm.trans f₁.2.2
  obtain ⟨B, hB1, hB2⟩ := exists_common_b hcop123
    (two_dvd_b_sub_b (f := g₁) (g := f₃.1) (hD1.trans f₃.2.2.symm))
  obtain ⟨h₁, e₁', ha₁, hb₁⟩ := exists_sLEquiv_b (f := g₁) (B := B)
    (dvd_trans (⟨g₂.a, by ring⟩ : 2 * g₁.a ∣ 2 * (g₁.a * g₂.a)) hB1)
  obtain ⟨h₂, e₂', ha₂, hb₂⟩ := exists_sLEquiv_b (f := g₂) (B := B)
    (by rw [← hc.2.1]; exact dvd_trans (⟨g₁.a, by ring⟩ : 2 * g₂.a ∣ 2 * (g₁.a * g₂.a)) hB1)
  obtain ⟨h₃, e₃', ha₃, hb₃⟩ := exists_sLEquiv_b (f := f₃.1) (B := B) hB2
  refine ⟨ofEquiv f₁ (e₁.trans e₁'), ofEquiv f₂ (e₂.trans e₂'), ofEquiv f₃ e₃',
    mk_ofEquiv _ _, mk_ofEquiv _ _, (mk_ofEquiv _ _).trans hf₃, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [val_ofEquiv]; rw [hb₁, hb₂]
  · simp only [val_ofEquiv]; rw [hb₂, hb₃]
  · simp only [val_ofEquiv]; rw [ha₁, ha₂, ha₃]; exact mul_ne_zero hne12 ha3
  · simp only [val_ofEquiv]; rw [ha₁, ha₂]; exact hcop12
  · simp only [val_ofEquiv]; rw [ha₁, ha₂, ha₃]; exact hcop123

/-- The composition of two concordant primitive forms of discriminant $D$, as an element of `PrimForm D`. -/
def PrimForm.comp (g₁ g₂ : PrimForm D) (hc : Concordant g₁.1 g₂.1) : PrimForm D :=
  ⟨Composition.comp g₁.1 g₂.1, isPrimitive_comp hc g₁.2.1 g₂.2.1, (disc_comp hc).trans g₁.2.2⟩

theorem primComp_a (g₁ g₂ : PrimForm D) (hc : Concordant g₁.1 g₂.1) :
    (PrimForm.comp g₁ g₂ hc).1.a = g₁.1.a * g₂.1.a := a_comp _ _

theorem primComp_b (g₁ g₂ : PrimForm D) (hc : Concordant g₁.1 g₂.1) :
    (PrimForm.comp g₁ g₂ hc).1.b = g₁.1.b := b_comp _ _

/-- **The composition of two classes** (Cassels, Ch. 14, Thm. 2.1, p. 337): the class of $\operatorname{comp}(g_1, g_2)$
for concordant representatives $g_1 \in \mathfrak C_1$, $g_2 \in \mathfrak C_2$ (Lemma 2.3, chosen), well defined by
Lemma 2.4 (`mk_mul_mk`). -/
noncomputable instance : Mul (FormClass D) := ⟨fun x y =>
  mk (PrimForm.comp (exists_concordant_reps x y).choose (exists_concordant_reps x y).choose_spec.choose
    (exists_concordant_reps x y).choose_spec.choose_spec.2.2)⟩

/-- The principal form as an element of `PrimForm D`. -/
def principal (D : ℤ) [NonzeroDisc D] : PrimForm D :=
  ⟨principalForm D, principalForm_spec NonzeroDisc.mod_four⟩

/-- **The unit class $\mathfrak E$**: the class of the principal form (1.11). -/
instance : One (FormClass D) := ⟨mk (principal D)⟩

theorem one_def : (1 : FormClass D) = mk (principal D) := rfl

theorem mul_def (x y : FormClass D) :
    x * y = mk (PrimForm.comp (exists_concordant_reps x y).choose (exists_concordant_reps x y).choose_spec.choose
    (exists_concordant_reps x y).choose_spec.choose_spec.2.2) := rfl

/-- **The inverse class**: the class of $[a, -b, c]$ (`Binary.conjForm`). -/
instance : Inv (FormClass D) := ⟨Quotient.map (fun f : PrimForm D =>
  (⟨conjForm f.1, isPrimitive_conjForm f.2.1, (disc_conjForm f.1).trans f.2.2⟩ : PrimForm D))
  (fun _ _ h => sLEquiv_conjForm h)⟩

/-- **The product of classes is the class of the composition of any concordant representatives** (Cassels, Ch. 14,
(1.8)–(1.10), p. 332, and Lemma 2.4, pp. 336–337). -/
@[kb "cassels1978" "Ch. 14, (1.8)–(1.10), p. 332; Lemma 2.4, pp. 336–337"]
theorem mk_mul_mk (g₁ g₂ : PrimForm D) (hc : Concordant g₁.1 g₂.1) :
    mk g₁ * mk g₂ = mk (PrimForm.comp g₁ g₂ hc) := by
  rw [mul_def]
  have hs := (exists_concordant_reps (mk g₁) (mk g₂)).choose_spec.choose_spec
  exact mk_eq_mk.2 (comp_sLEquiv_comp (exists_concordant_reps (mk g₁) (mk g₂)).choose.2.1
    (exists_concordant_reps (mk g₁) (mk g₂)).choose_spec.choose.2.1 g₁.2.1 g₂.2.1
    (by rw [(exists_concordant_reps (mk g₁) (mk g₂)).choose.2.2]; exact NonzeroDisc.ne_zero)
    (mk_eq_mk.1 hs.1) (mk_eq_mk.1 hs.2.1) hs.2.2 hc)

/-- Associativity (Cassels, Ch. 14, proof of Thm. 2.1, p. 337: both products are the class of $[a_1a_2a_3, b, *]$). -/
theorem mul_assoc' (x y z : FormClass D) : x * y * z = x * (y * z) := by
  obtain ⟨g₁, g₂, g₃, h1, h2, h3, hb12, hb23, hne, hc12, hc123⟩ := exists_triple_reps x y z
  subst h1 h2 h3
  have ha12 : g₁.1.a * g₂.1.a ≠ 0 := left_ne_zero_of_mul hne
  have ha3 : g₃.1.a ≠ 0 := right_ne_zero_of_mul hne
  have ha1 : g₁.1.a ≠ 0 := left_ne_zero_of_mul ha12
  have ha2 : g₂.1.a ≠ 0 := right_ne_zero_of_mul ha12
  have hc13 : IsCoprime g₁.1.a g₃.1.a :=
    hc123.of_isCoprime_of_dvd_left (show g₁.1.a ∣ g₁.1.a * g₂.1.a from ⟨g₂.1.a, rfl⟩)
  have hc23 : IsCoprime g₂.1.a g₃.1.a :=
    hc123.of_isCoprime_of_dvd_left (show g₂.1.a ∣ g₁.1.a * g₂.1.a from ⟨g₁.1.a, by ring⟩)
  have C12 : Concordant g₁.1 g₂.1 :=
    concordant_of_coprime ha12 hb12 (g₁.2.2.trans g₂.2.2.symm) hc12
  have Cp3 : Concordant (PrimForm.comp g₁ g₂ C12).1 g₃.1 := concordant_of_coprime
    (by rw [primComp_a]; exact hne) (by rw [primComp_b]; exact hb12.trans hb23)
    ((PrimForm.comp g₁ g₂ C12).2.2.trans g₃.2.2.symm) (by rw [primComp_a]; exact hc123)
  have C23 : Concordant g₂.1 g₃.1 :=
    concordant_of_coprime (mul_ne_zero ha2 ha3) hb23 (g₂.2.2.trans g₃.2.2.symm) hc23
  have C1q : Concordant g₁.1 (PrimForm.comp g₂ g₃ C23).1 := concordant_of_coprime
    (by rw [primComp_a, ← mul_assoc]; exact hne) (by rw [primComp_b]; exact hb12)
    (g₁.2.2.trans (PrimForm.comp g₂ g₃ C23).2.2.symm)
    (by rw [primComp_a]; exact hc12.mul_right hc13)
  rw [mk_mul_mk g₁ g₂ C12, mk_mul_mk _ g₃ Cp3, mk_mul_mk g₂ g₃ C23, mk_mul_mk g₁ _ C1q]
  have e : (PrimForm.comp (PrimForm.comp g₁ g₂ C12) g₃ Cp3).1 =
      (PrimForm.comp g₁ (PrimForm.comp g₂ g₃ C23) C1q).1 := by
    apply eq_of_a_b_disc
    · simp only [primComp_a]; exact hne
    · simp only [primComp_a]; ring
    · simp only [primComp_b]
    · exact (PrimForm.comp (PrimForm.comp g₁ g₂ C12) g₃ Cp3).2.2.trans
        (PrimForm.comp g₁ (PrimForm.comp g₂ g₃ C23) C1q).2.2.symm
  exact mk_eq_mk.2 (by rw [e]; exact SLEquiv.refl _)

/-- Commutativity (Cassels, Ch. 14, proof of Thm. 2.1, p. 337). -/
theorem mul_comm' (x y : FormClass D) : x * y = y * x := by
  obtain ⟨g₁, g₂, h1, h2, hc⟩ := exists_concordant_reps x y
  subst h1 h2
  rw [mk_mul_mk g₁ g₂ hc, mk_mul_mk g₂ g₁ hc.symm]
  exact mk_eq_mk.2 (by
    show SLEquiv (Composition.comp g₁.1 g₂.1) (Composition.comp g₂.1 g₁.1)
    rw [hc.comp_comm]; exact SLEquiv.refl _)

/-- A form representing $1$ lies in the unit class (helper for `mk_eq_one_iff`). -/
private theorem mk_eq_one_of_represents (f : PrimForm D) (h : f.1.Represents 1) : mk f = 1 := by
  obtain ⟨x, y, hxy⟩ := h
  have hcop : IsCoprime x y := by
    have hx : ((Int.gcd x y : ℕ) : ℤ) ∣ x := Int.gcd_dvd_left ..
    have hy : ((Int.gcd x y : ℕ) : ℤ) ∣ y := Int.gcd_dvd_right ..
    have hg : ((Int.gcd x y : ℕ) : ℤ) ∣ f.1.eval x y := by
      rw [eval_eq]
      exact dvd_add (dvd_add ((dvd_pow hx two_ne_zero).mul_left _) ((hx.mul_left _).mul_right _))
        ((dvd_pow hy two_ne_zero).mul_left _)
    rw [hxy] at hg
    exact Int.isCoprime_iff_gcd_eq_one.2
      (by exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg _) hg)
  obtain ⟨g, e, hga⟩ := exists_sLEquiv_a_of_eval (f := f.1) hcop
  rw [hxy] at hga
  have hpf := principalForm_spec (D := D) NonzeroDisc.mod_four
  have hDg : g.disc = (principalForm D).disc :=
    (SLEquiv.disc_eq e).symm.trans (f.2.2.trans hpf.2.symm)
  have h2 := two_dvd_b_sub_b hDg
  obtain ⟨g', e', ha', hb'⟩ := exists_sLEquiv_b (f := g) (B := (principalForm D).b)
    (by
      rw [hga]
      obtain ⟨k, hk⟩ := h2
      exact ⟨-k, by linarith⟩)
  have hg' : g' = principalForm D := by
    apply eq_of_a_b_disc
    · rw [ha', hga]; exact one_ne_zero
    · rw [ha', hga]; simp [principalForm]
    · exact hb'
    · exact (SLEquiv.disc_eq e').symm.trans hDg
  rw [one_def]
  apply mk_eq_mk.2
  have := e.trans e'
  rw [hg'] at this
  exact this

/-- $\mathfrak E\mathfrak C = \mathfrak C$ (Cassels, Ch. 14, proof of Thm. 2.1, p. 338). -/
theorem one_mul' (x : FormClass D) : 1 * x = x := by
  obtain ⟨f, hf, hc⟩ := exists_rep_coprime x (M := 2 * D) (mul_ne_zero two_ne_zero NonzeroDisc.ne_zero)
  have ha := ne_zero_of_coprime_two_mul hc
  have hdisc : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
  obtain ⟨E, hE⟩ : ∃ E : PrimForm D, E.1 = BinQF.mk 1 f.1.b (f.1.a * f.1.c) :=
    ⟨⟨BinQF.mk 1 f.1.b (f.1.a * f.1.c),
      by
        intro d h1 _ _
        simp only [a_mk] at h1
        exact isUnit_of_dvd_one h1,
      by
        simp only [BinQF.disc, a_mk, b_mk, c_mk]
        linear_combination hdisc⟩, rfl⟩
  have hEa : E.1.a = 1 := by rw [hE, a_mk]
  have hEb : E.1.b = f.1.b := by rw [hE, b_mk]
  have hE1 : mk E = 1 := mk_eq_one_of_represents E ⟨1, 0, by rw [eval_eq, hEa]; ring⟩
  have hconc : Concordant E.1 f.1 := concordant_of_coprime (by rw [hEa, one_mul]; exact ha) hEb
    (E.2.2.trans f.2.2.symm) (by rw [hEa]; exact isCoprime_one_left)
  have hcomp : (PrimForm.comp E f hconc).1 = f.1 := by
    apply eq_of_a_b_disc
    · rw [primComp_a, hEa, one_mul]; exact ha
    · rw [primComp_a, hEa, one_mul]
    · rw [primComp_b, hEb]
    · exact (PrimForm.comp E f hconc).2.2.trans f.2.2.symm
  calc 1 * x = mk E * mk f := by rw [hE1, hf]
    _ = mk (PrimForm.comp E f hconc) := mk_mul_mk E f hconc
    _ = mk f := mk_eq_mk.2 (by rw [hcomp]; exact SLEquiv.refl _)
    _ = x := hf

/-- $\mathfrak C^{-1}\mathfrak C = \mathfrak E$ (Cassels, Ch. 14, proof of Thm. 2.1, p. 338: $[c, b, a]$ and
$[a, b, c]$ compose to $[ac, b, 1]$, which represents $1$). -/
theorem inv_mul_cancel' (x : FormClass D) : x⁻¹ * x = 1 := by
  obtain ⟨f, hf, hc, hc0⟩ := exists_rep_ac_ne_zero x
  have ha := ne_zero_of_coprime_two_mul hc
  have hdisc : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
  have e1 : SLEquiv (conjForm f.1) (BinQF.mk f.1.c f.1.b f.1.a) := by
    have := sLEquiv_swap f.1.a (-f.1.b) f.1.c
    rw [neg_neg] at this
    exact this
  obtain ⟨H, hH, hHk⟩ : ∃ H : PrimForm D, H.1 = BinQF.mk f.1.c f.1.b f.1.a ∧ mk H = x⁻¹ := by
    obtain ⟨Fc, hFc⟩ : ∃ Fc : PrimForm D, Fc.1 = conjForm f.1 :=
      ⟨⟨conjForm f.1, isPrimitive_conjForm f.2.1, (disc_conjForm f.1).trans f.2.2⟩, rfl⟩
    refine ⟨ofEquiv Fc (hFc ▸ e1), rfl, ?_⟩
    have hFc' : Fc = ⟨conjForm f.1, isPrimitive_conjForm f.2.1, (disc_conjForm f.1).trans f.2.2⟩ :=
      Subtype.ext hFc
    rw [mk_ofEquiv, ← hf, hFc']
    rfl
  have hconc : Concordant H.1 f.1 := by
    refine ⟨?_, ?_, H.2.2.trans f.2.2.symm, ?_⟩
    · rw [hH, a_mk]; exact mul_ne_zero hc0 ha
    · rw [hH, b_mk]
    · rw [H.2.2, hH, a_mk, b_mk]
      exact ⟨1, by linear_combination hdisc⟩
  have hKa : (PrimForm.comp H f hconc).1.a = f.1.c * f.1.a := by rw [primComp_a, hH, a_mk]
  have hKb : (PrimForm.comp H f hconc).1.b = f.1.b := by rw [primComp_b, hH, b_mk]
  have hKd : (PrimForm.comp H f hconc).1.b ^ 2 - 4 * (PrimForm.comp H f hconc).1.a *
      (PrimForm.comp H f hconc).1.c = D := (PrimForm.comp H f hconc).2.2
  rw [hKa, hKb] at hKd
  have hKc : (PrimForm.comp H f hconc).1.c = 1 := by
    have h4 : (4 * (f.1.c * f.1.a)) * (PrimForm.comp H f hconc).1.c = (4 * (f.1.c * f.1.a)) * 1 := by
      linear_combination hdisc - hKd
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) (mul_ne_zero hc0 ha)) h4
  calc x⁻¹ * x = mk H * mk f := by rw [hHk, hf]
    _ = mk (PrimForm.comp H f hconc) := mk_mul_mk H f hconc
    _ = 1 := mk_eq_one_of_represents _ ⟨0, 1, by rw [eval_eq, hKc]; ring⟩

/-- **Cassels, Ch. 14, Theorem 2.1** (p. 337): *composition gives the set $\mathcal G$ of primitive classes of
discriminant $D$ the structure of an abelian group; the neutral element is the class $\mathfrak E$ of forms
representing $1$, and the inverse of $\mathfrak C$ is the class of the forms improperly equivalent to those of
$\mathfrak C$.* The unit and inverse are `mk_eq_one_iff`, `mk_inv`; finiteness is `finite`. -/
@[kb "cassels1978" "Ch. 14, Thm. 2.1, pp. 337–338 (abelian group)"]
noncomputable instance instCommGroup : CommGroup (FormClass D) :=
  { Group.ofLeftAxioms mul_assoc' one_mul' inv_mul_cancel' with mul_comm := mul_comm' }

/-- **The unit $\mathfrak E$** (Cassels, Ch. 14, p. 337): *any two forms of the same discriminant $D$ which represent
$1$ are properly equivalent*, and their class is the neutral element. -/
@[kb "cassels1978" "Ch. 14, §2, p. 337 (the class 𝔈 of forms representing 1); Thm. 2.1, p. 337"]
theorem mk_eq_one_iff (f : PrimForm D) : mk f = 1 ↔ f.1.Represents 1 := by
  refine ⟨fun h => ?_, mk_eq_one_of_represents f⟩
  rw [one_def] at h
  exact SLEquiv.represents (mk_eq_mk.1 h) ⟨1, 0, by rw [eval_eq]; simp [principal, principalForm]⟩

/-- **The principal form (1.11) lies in the unit class** (Cassels, Ch. 14, p. 337: $f_0 \in \mathfrak E$). -/
@[kb "cassels1978" "Ch. 14, §2, p. 337 (f₀ ∈ 𝔈)"]
theorem mk_principal : mk (principal D) = 1 := rfl

/-- **The inverse class** (Cassels, Ch. 14, Thm. 2.1, pp. 337–338): $[a, b, c]^{-1}$ is the class of $[a, -b, c]$
(`Binary.conjForm`), the image of $[a, b, c]$ under the improper substitution $y \mapsto -y$; Cassels uses the
properly equivalent $[c, b, a]$. -/
@[kb "cassels1978" "Ch. 14, Thm. 2.1, pp. 337–338 (inverse: improperly equivalent forms)"]
theorem mk_inv (f : PrimForm D) :
    (mk f)⁻¹ = mk ⟨conjForm f.1, isPrimitive_conjForm f.2.1, (disc_conjForm f.1).trans f.2.2⟩ := rfl

/-- **$\mathcal G$ is finite** (Cassels, Ch. 14, Thm. 2.1, p. 337: "a special case of Theorem 1.1 of Chapter 9"). -/
@[kb "cassels1978" "Ch. 14, Thm. 2.1, p. 337 (finiteness)"]
theorem finite : Finite (FormClass D) := by
  have eval_smul : ∀ (c : ℤ) (Q : BinQF) (x : Fin 2 → ℤ), QuadForm.eval (c • Q) x = c * QuadForm.eval Q x := by
    intro c Q x
    simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.smul_coeff, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum, Algebra.algebraMap_self, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have hint : ∀ {f g : BinQF}, Siegel.IntEquiv ((2 : ℤ) • f) ((2 : ℤ) • g) ↔ Siegel.IntEquiv f g := by
    intro f g
    constructor
    · rintro ⟨γ, h⟩
      refine ⟨γ, fun x => ?_⟩
      have := h x
      rw [eval_smul, eval_smul] at this
      linarith
    · rintro ⟨γ, h⟩
      refine ⟨γ, fun x => ?_⟩
      rw [eval_smul, eval_smul, h x]
  let Φ : FormClass D → Siegel.QClass 2 := Quotient.lift
    (fun f : PrimForm D => Siegel.classOf ((2 : ℤ) • f.1))
    (fun f g (h : SLEquiv f.1 g.1) =>
      Siegel.classOf_eq_classOf_iff.2 (hint.2 (SLEquiv.intEquiv h)))
  have hfibre : ∀ x y : FormClass D, Φ x = Φ y → y = x ∨ y = x⁻¹ := by
    intro x y hxy
    obtain ⟨f, rfl⟩ := mk_surjective x
    obtain ⟨g, rfl⟩ := mk_surjective y
    have h1 : Siegel.IntEquiv f.1 g.1 :=
      hint.1 (Siegel.classOf_eq_classOf_iff.1 hxy)
    rcases (intEquiv_iff_sLEquiv_or _ _).1 h1 with h | h
    · exact Or.inl (mk_eq_mk.2 h.symm)
    · refine Or.inr ?_
      rw [mk_inv]
      exact mk_eq_mk.2 h.symm
  have hrange : (Set.range Φ).Finite := by
    refine (Siegel.finite_classes_of_det 2 (by norm_num) (d := -D)
      (neg_ne_zero.2 NonzeroDisc.ne_zero)).subset ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := mk_surjective x
    refine ⟨(2 : ℤ) • f.1, rfl, two_smul_isClassicallyIntegral _, ?_⟩
    rw [hessian_det_two]
    have e00 : ((2 : ℤ) • f.1).coeff 0 0 = 2 * f.1.a := by simp [BinQF.a]
    have e01 : ((2 : ℤ) • f.1).coeff 0 1 = 2 * f.1.b := by simp [BinQF.b]
    have e11 : ((2 : ℤ) • f.1).coeff 1 1 = 2 * f.1.c := by simp [BinQF.c]
    rw [e00, e01, e11]
    have hdisc : f.1.b ^ 2 - 4 * f.1.a * f.1.c = D := f.2.2
    linear_combination (-4 : ℤ) * hdisc
  have hfib : ∀ c : Siegel.QClass 2, (Φ ⁻¹' {c}).Finite := by
    intro c
    by_cases hne : (Φ ⁻¹' {c}).Nonempty
    · obtain ⟨x, hx⟩ := hne
      refine ((Set.finite_singleton x⁻¹).insert x).subset ?_
      intro y hy
      have hx' : Φ x = c := hx
      have hy' : Φ y = c := hy
      simpa using hfibre x y (hx'.trans hy'.symm)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  have huniv : (Set.univ : Set (FormClass D)).Finite := by
    refine (hrange.biUnion (fun c _ => hfib c)).subset ?_
    intro x _
    exact Set.mem_iUnion₂.2 ⟨Φ x, ⟨x, rfl⟩, rfl⟩
  exact Set.finite_univ_iff.1 huniv

instance : Finite (FormClass D) := finite

/-- The form $[w^{j+1}, b, w^t e]$, primitive of discriminant $D$ when $\gcd(w, b) = 1$ and
$b^2 - 4w^{m+1}e = D$, $j + t = m$ (helper for Lemma 2.5). -/
private def powForm {w b e : ℤ} {m : ℕ} (hcop : IsCoprime w b) (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D)
    (j t : ℕ) (h : j + t = m) : PrimForm D :=
  ⟨BinQF.mk (w ^ (j + 1)) b (w ^ t * e),
    by
      intro d h1 h2 _
      simp only [a_mk, b_mk] at h1 h2
      exact (hcop.pow_left).isUnit_of_dvd' h1 h2,
    by
      simp only [BinQF.disc, a_mk, b_mk, c_mk]
      subst h
      linear_combination hD⟩

private theorem powForm_val {w b e : ℤ} {m : ℕ} (hcop : IsCoprime w b)
    (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D) (j t : ℕ) (h : j + t = m) :
    (powForm hcop hD j t h).1 = BinQF.mk (w ^ (j + 1)) b (w ^ t * e) := rfl

/-- $\mathfrak C^{j+1}$ for $\mathfrak C = [w, b, w^m e]$ is $[w^{j+1}, b, w^{m-j} e]$ (helper for Lemma 2.5). -/
private theorem pow_powForm {w b e : ℤ} {m : ℕ} (hw : w ≠ 0) (hcop : IsCoprime w b)
    (hD : b ^ 2 - 4 * w ^ (m + 1) * e = D) :
    ∀ (j t : ℕ) (h : j + t = m),
      (mk (powForm hcop hD 0 m (zero_add m))) ^ (j + 1) = mk (powForm hcop hD j t h) := by
  intro j
  induction j with
  | zero =>
    intro t h
    have ht : t = m := by omega
    subst ht
    rw [zero_add, pow_one]
  | succ j ih =>
    intro t h
    have h' : j + (t + 1) = m := by omega
    have ih' := ih (t + 1) h'
    have hD' : b ^ 2 - 4 * w ^ (j + (t + 1) + 1) * e = D := by rw [h']; exact hD
    have hc : Concordant (powForm hcop hD j (t + 1) h').1 (powForm hcop hD 0 m (zero_add m)).1 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [powForm_val, a_mk]
        exact mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hw)
      · simp only [powForm_val, b_mk]
      · exact (powForm hcop hD j (t + 1) h').2.2.trans (powForm hcop hD 0 m (zero_add m)).2.2.symm
      · rw [(powForm hcop hD j (t + 1) h').2.2]
        simp only [powForm_val, a_mk, b_mk]
        exact ⟨w ^ t * e, by linear_combination hD'⟩
    have hcomp : (PrimForm.comp (powForm hcop hD j (t + 1) h') (powForm hcop hD 0 m (zero_add m)) hc).1 =
        (powForm hcop hD (j + 1) t h).1 := by
      apply eq_of_a_b_disc
      · simp only [primComp_a, powForm_val, a_mk]
        exact mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ hw)
      · simp only [primComp_a, powForm_val, a_mk]
        ring
      · simp only [primComp_b, powForm_val, b_mk]
      · exact (PrimForm.comp _ _ hc).2.2.trans (powForm hcop hD (j + 1) t h).2.2.symm
    rw [pow_succ, ih']
    exact (mk_mul_mk _ _ hc).trans (mk_eq_mk.2 (by rw [hcomp]; exact SLEquiv.refl _))

/-- Solving $w^m \mid w l^2 + b l + c$ when $\gcd(w, b) = 1$ (helper for Lemma 2.5). -/
private theorem exists_pow_dvd {w b c : ℤ} (hcw : IsCoprime w b) (m : ℕ) :
    ∃ l : ℤ, w ^ m ∣ w * l ^ 2 + b * l + c := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨l, t, ht⟩ := ih
    obtain ⟨u, v, huv⟩ := hcw
    refine ⟨l + w ^ k * (-(t * v)), ?_⟩
    exact ⟨t * u + 2 * l * (-(t * v)) + w ^ k * (-(t * v)) ^ 2,
      by linear_combination ht + (-(w ^ k * t)) * huv⟩

/-- **Cassels, Ch. 14, Lemma 2.5** (p. 338): *let $n \ge 1$. A class $\mathfrak C$ is of the form
$\mathfrak C = \mathfrak C_1^n$ if and only if $\mathfrak C$ represents primitively an integer $w^n$ with $w$ prime
to $2D$.* -/
@[kb "cassels1978" "Ch. 14, Lemma 2.5, p. 338"]
theorem exists_pow_eq_iff {n : ℕ} (hn : 1 ≤ n) (C : FormClass D) :
    (∃ C₁ : FormClass D, C₁ ^ n = C) ↔
      ∃ f : PrimForm D, mk f = C ∧ ∃ w x y : ℤ, IsCoprime x y ∧ IsCoprime w (2 * D) ∧ f.1.eval x y = w ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  constructor
  · rintro ⟨C₁, rfl⟩
    obtain ⟨g, rfl, hg⟩ := exists_rep_coprime C₁ (M := 2 * D)
      (mul_ne_zero two_ne_zero NonzeroDisc.ne_zero)
    have hw0 : g.1.a ≠ 0 := ne_zero_of_coprime_two_mul hg
    have hwD : IsCoprime g.1.a D := hg.of_isCoprime_of_dvd_right ⟨2, by ring⟩
    have hdisc : g.1.b ^ 2 - 4 * g.1.a * g.1.c = D := g.2.2
    have hcw : IsCoprime g.1.a g.1.b := by
      have h1 : IsCoprime g.1.a (g.1.b ^ 2) := by
        have : g.1.b ^ 2 = D + g.1.a * (4 * g.1.c) := by linear_combination hdisc
        rw [this]; exact hwD.add_mul_left_right _
      exact (IsCoprime.pow_right_iff two_pos).1 h1
    obtain ⟨l, E, hE⟩ := exists_pow_dvd (c := g.1.c) hcw m
    obtain ⟨g', hg'k, hg'a, hg'b, hg'c⟩ := exists_translate g l
    have hg'c' : g'.1.c = g.1.a ^ m * E := by rw [hg'c, hE]
    have hdisc' : g'.1.b ^ 2 - 4 * g.1.a ^ (m + 1) * E = D := by
      have h := g'.2.2
      have h' : g'.1.b ^ 2 - 4 * g'.1.a * g'.1.c = D := h
      rw [hg'a, hg'c'] at h'
      linear_combination h'
    have hcw' : IsCoprime g.1.a g'.1.b := by
      have : g'.1.b = g.1.b + g.1.a * (2 * l) := by rw [hg'b]; ring
      rw [this]; exact hcw.add_mul_left_right _
    have hform : (powForm hcw' hdisc' 0 m (zero_add m)).1 = g'.1 :=
      ext_abc (by simp [powForm_val, hg'a]) (by simp [powForm_val]) (by simp [powForm_val, hg'c'])
    have hP : mk (powForm hcw' hdisc' 0 m (zero_add m)) = mk g := by
      rw [← hg'k]
      exact mk_eq_mk.2 (by rw [hform]; exact SLEquiv.refl _)
    refine ⟨powForm hcw' hdisc' m 0 (add_zero m), ?_, g.1.a, 1, 0, isCoprime_one_left, hg, ?_⟩
    · rw [← hP]
      exact (pow_powForm hw0 hcw' hdisc' m 0 (add_zero m)).symm
    · rw [eval_eq]
      simp [powForm_val]
  · rintro ⟨f, rfl, w, x, y, hxy, hw, hev⟩
    obtain ⟨g, e, hga⟩ := exists_sLEquiv_a_of_eval (f := f.1) hxy
    rw [hev] at hga
    have hw0 : w ≠ 0 := ne_zero_of_coprime_two_mul hw
    have hdisc : g.disc = D := (SLEquiv.disc_eq e).symm.trans f.2.2
    have hD' : g.b ^ 2 - 4 * w ^ (m + 1) * g.c = D := by rw [← hga]; exact hdisc
    have hwD : IsCoprime w D := hw.of_isCoprime_of_dvd_right ⟨2, by ring⟩
    have hcw : IsCoprime w g.b := by
      have h1 : IsCoprime w (g.b ^ 2) := by
        have : g.b ^ 2 = D + w * (4 * w ^ m * g.c) := by linear_combination hD'
        rw [this]; exact hwD.add_mul_left_right _
      exact (IsCoprime.pow_right_iff two_pos).1 h1
    refine ⟨mk (powForm hcw hD' 0 m (zero_add m)), ?_⟩
    have hP : (powForm hcw hD' m 0 (add_zero m)).1 = g :=
      ext_abc (by simp [powForm_val, hga]) (by simp [powForm_val]) (by simp [powForm_val])
    rw [pow_powForm hw0 hcw hD' m 0 (add_zero m)]
    exact mk_eq_mk.2 (by rw [hP]; exact e.symm)

end FormClass

end QuadFormsKB.Composition
