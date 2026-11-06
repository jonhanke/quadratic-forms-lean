/-
# Cassels, Chapter 14, §6: the composition law on ambiguous forms (Lemma 6.1)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §6, pp. 346–348.

Cassels writes the primitive ambiguous forms of discriminant $D$ as
$$f(a) = [a, 0, c],\ D = -4ac \quad (6.5), \qquad g(a) = [a, a, c],\ D = a(a - 4c) \quad (6.6)$$
(`ambF D a`, `ambG D a`; the form is determined by $a$ and $D$), and makes the set $\mathcal B$ of these forms a group
of exponent $2$ by explicit rules (6.7)–(6.14) such that taking classes, $\mathcal B \to \mathcal A$, is a
homomorphism (Lemma 6.1). The rules are, with $a_1a_2 = a_3\gcd(a_1, a_2)^2$ (6.11) and
$\alpha_1\alpha_2 = \alpha_3\gcd(\alpha_1, \alpha_2)^2$ (6.14):

* the unit is the principal form $e = f(1)$ ($D$ even) or $g(1)$ ($D$ odd) (6.7) (`principalForm_eq_ambF`,
  `principalForm_eq_ambG`); every element is its own inverse (6.8)–(6.9);
* $f(a_1) * f(a_2) = f(a_3)$ (6.10) for every $D$;
* $g(a_1) * g(a_2) = g(a_3)$ (6.13) for $D$ odd (case (i));
* in case (iii), $D = 4d$ with $d \equiv -1 \pmod 4$, the elements are $f(\alpha)$ and $g(2\alpha)$ with $\alpha$ odd,
  and the table is $f(\alpha_1) * g(2\alpha_2) = g(2\alpha_3)$, $g(2\alpha_1) * g(2\alpha_2) = f(\alpha_3)$.

Here Lemma 6.1 is stated as what makes it work: each rule holds for the classes (`mk_mul_mk_ambF`,
`mk_mul_mk_ambG`, `mk_mul_mk_ambF_ambG`, `mk_mul_mk_ambG_ambG`, `mk_sq_of_isAmbiguousForm`), i.e. the class of the
product is the product of the classes.

*Reconstruction.* The table of case (iii) is lost in the machine-read text; the rules above are the ones that make
taking classes a homomorphism, and they are proved here. The table of case (v) ($2^5 \mid D$; elements $f(\alpha)$,
$f(2^\delta\alpha)$, $g(4\alpha)$, $g(2^\delta\alpha)$) is lost as well and is not reconstructed; rule (6.10) for the
forms $f(a)$ holds in that case too. That the rules define a group law on the set $\mathcal B$ itself (associativity
on $\mathcal B$) is not formalized: the statements are about the classes.

The definitions $f(a)$, $g(a)$, $e'$ and the facts (6.7), (6.15)–(6.17) are in `Ch14/AmbiguousFG.lean`.
-/
import QuadFormsKB.Literature.Cassels.Ch14.AmbiguousFG

namespace QuadFormsKB.Composition

open BinQF Binary FormClass

variable {D : ℤ}

/-! ### Helpers -/

private theorem isCoprime_of_prim {a c : ℤ} (h : ∀ d : ℤ, d ∣ a → d ∣ c → IsUnit d) : IsCoprime a c := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have := Int.isUnit_iff_natAbs_eq.mp (h (Int.gcd a c : ℤ) (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..))
  simpa using this

private theorem isCoprime_two_of_odd {x : ℤ} (h : x % 2 = 1) : IsCoprime x 2 :=
  ⟨1, -(x / 2), by omega⟩

private theorem odd_of_mul {x y : ℤ} (h : (x * y) % 2 = 1) : x % 2 = 1 := by
  have := Int.mul_emod x y 2
  rcases Int.emod_two_eq_zero_or_one x with h0 | h0
  · rw [h0] at this; omega
  · exact h0

private theorem sub_mod_four_of_mul {x y : ℤ} (h : (x * y) % 4 = 1) : (x - y) % 4 = 0 := by
  have h1 := Int.mul_emod x y 4
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hy : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] at h1 <;> omega

private theorem sub_mod_four_of_mul' {x y : ℤ} (h : (x * y) % 4 = 3) : (x - y) % 4 = 2 := by
  have h1 := Int.mul_emod x y 4
  have hx : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
  have hy : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] at h1 <;> omega

private theorem glue_classes {G : Type*} [CommGroup G] {g A B C X Y : G} (hX : X = g * A) (hY : Y = g * B)
    (hg : g ^ 2 = 1) (hAB : A * B = C) : X * Y = C := by
  rw [hX, hY, mul_mul_mul_comm, ← sq, hg, one_mul, hAB]

private theorem ambF_eq {x y : ℤ} (hx : x ≠ 0) (hD : D = -4 * x * y) : ambF D x = BinQF.mk x 0 y := by
  have : -D / (4 * x) = y := by
    rw [show -D = (4 * x) * y by linarith]
    exact Int.mul_ediv_cancel_left _ (mul_ne_zero (by norm_num) hx)
  rw [ambF, this]

private theorem ambG_eq {x y : ℤ} (hx : x ≠ 0) (hD : D = x * y) : ambG D x = BinQF.mk x x ((x - y) / 4) := by
  have : D / x = y := by rw [hD]; exact Int.mul_ediv_cancel_left _ hx
  rw [ambG, this]

/-- A form `[x, 0, y]` with `D = -4xy`, `x, y` coprime. -/
private theorem exists_primF [NonzeroDisc D] {x y : ℤ} (hD : D = -4 * x * y) (hc : IsCoprime x y) :
    ∃ f : PrimForm D, f.1 = ambF D x := by
  have hx : x ≠ 0 := by
    rintro rfl; apply NonzeroDisc.ne_zero (D := D); rw [hD]; ring
  rw [ambF_eq hx hD]
  refine ⟨⟨BinQF.mk x 0 y, ?_, ?_⟩, rfl⟩
  · intro d h1 _ h3
    simp only [a_mk, c_mk] at h1 h3
    exact hc.isUnit_of_dvd' h1 h3
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]; linarith


private theorem isCoprime_sub_self {a c : ℤ} (h : IsCoprime a c) : IsCoprime a (a - c) := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u + v, -v, by linear_combination huv⟩

/-- Extract the arithmetic of a form `f(a)`. -/
private theorem extract_F [NonzeroDisc D] {a : ℤ} (f : PrimForm D) (h : f.1 = ambF D a) :
    ∃ y, a ≠ 0 ∧ D = -4 * a * y ∧ IsCoprime a y := by
  obtain ⟨hp, hd⟩ := f.2
  rw [h] at hp hd
  obtain ⟨y, hy⟩ : ∃ y, ambF D a = BinQF.mk a 0 y := ⟨_, rfl⟩
  rw [hy] at hp hd
  simp only [BinQF.disc, a_mk, b_mk, c_mk] at hd
  have ha : a ≠ 0 := by
    rintro rfl; apply NonzeroDisc.ne_zero (D := D); linarith
  exact ⟨y, ha, by linarith, isCoprime_of_prim fun d h1 h3 => hp d (by simpa using h1) (by simp) (by simpa using h3)⟩

private theorem extract_G [NonzeroDisc D] (hD : D % 2 = 1) {a : ℤ} (f : PrimForm D) (h : f.1 = ambG D a) :
    ∃ y, a ≠ 0 ∧ D = a * y ∧ IsCoprime a y := by
  obtain ⟨hp, hd⟩ := f.2
  rw [h] at hp hd
  obtain ⟨c, hc⟩ : ∃ c, ambG D a = BinQF.mk a a c := ⟨_, rfl⟩
  rw [hc] at hp hd
  simp only [BinQF.disc, a_mk, b_mk, c_mk] at hd
  have hD' : D = a * (a - 4 * c) := by linear_combination -hd
  have hao : a % 2 = 1 := odd_of_mul (y := a - 4 * c) (by rw [← hD']; exact hD)
  have ha : a ≠ 0 := by rintro rfl; simp at hao
  have h1 : IsCoprime a c := isCoprime_of_prim fun d h1 h3 => hp d (by simpa using h1) (by simpa using h1) (by simpa using h3)
  have h4 : IsCoprime a 4 := by
    have := (isCoprime_two_of_odd hao).pow_right (n := 2)
    simpa using this
  refine ⟨a - 4 * c, ha, hD', isCoprime_sub_self (h4.mul_right h1)⟩

private theorem exists_primG [NonzeroDisc D] (hD : D % 2 = 1) {x y : ℤ} (hxy : D = x * y) (hc : IsCoprime x y) :
    ∃ f : PrimForm D, f.1 = ambG D x := by
  have hx : x ≠ 0 := by
    rintro rfl; apply NonzeroDisc.ne_zero (D := D); rw [hxy]; ring
  have h4 : (x - y) % 4 = 0 := sub_mod_four_of_mul (by rw [← hxy]; have := NonzeroDisc.mod_four (D := D); omega)
  rw [ambG_eq hx hxy]
  obtain ⟨c, hcdef⟩ : ∃ c, c = (x - y) / 4 := ⟨_, rfl⟩
  have hc4 : 4 * c = x - y := by omega
  rw [← hcdef]
  refine ⟨⟨BinQF.mk x x c, ?_, ?_⟩, rfl⟩
  · intro d h1 _ h3
    simp only [a_mk, c_mk] at h1 h3
    refine hc.isUnit_of_dvd' h1 ?_
    have : y = x - 4 * c := by linarith
    rw [this]; exact dvd_sub h1 (h3.mul_left 4)
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]
    rw [hxy]; linear_combination (-x) * hc4

/-- Splitting two pairs `(a₁, e₁)`, `(a₂, e₂)` with `a₁e₁ = a₂e₂` and `a_j` prime to `e_j`. -/
private theorem split_pairs {a₁ a₂ e₁ e₂ : ℤ} (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0) (h : a₁ * e₁ = a₂ * e₂)
    (c1 : IsCoprime a₁ e₁) (c2 : IsCoprime a₂ e₂) :
    ∃ g a₁' a₂' v : ℤ, g = (Int.gcd a₁ a₂ : ℤ) ∧ g ≠ 0 ∧ a₁ = g * a₁' ∧ a₂ = g * a₂' ∧ e₁ = a₂' * v ∧
      e₂ = a₁' * v ∧ IsCoprime g a₁' ∧ IsCoprime g a₂' ∧ IsCoprime a₁' a₂' ∧ IsCoprime g v ∧
      IsCoprime a₁' v ∧ IsCoprime a₂' v := by
  have hpos : 0 < Int.gcd a₁ a₂ := Int.gcd_pos_of_ne_zero_left _ h1
  have hg0 : ((Int.gcd a₁ a₂ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  obtain ⟨a₁', ha₁⟩ := Int.gcd_dvd_left (a := a₁) (b := a₂)
  obtain ⟨a₂', ha₂⟩ := Int.gcd_dvd_right (a := a₁) (b := a₂)
  set g : ℤ := (Int.gcd a₁ a₂ : ℤ) with hg
  have ha₁' : a₁' ≠ 0 := by rintro rfl; apply h1; rw [ha₁]; ring
  have ha₂' : a₂' ≠ 0 := by rintro rfl; apply h2; rw [ha₂]; ring
  have hcop : IsCoprime a₁' a₂' := by
    have := Int.gcd_div_gcd_div_gcd (i := a₁) (j := a₂) hpos
    rw [Int.isCoprime_iff_gcd_eq_one]
    have e1 : a₁ / g = a₁' := by rw [ha₁]; exact Int.mul_ediv_cancel_left _ hg0
    have e2 : a₂ / g = a₂' := by rw [ha₂]; exact Int.mul_ediv_cancel_left _ hg0
    rw [← e1, ← e2]; exact this
  have h' : a₁' * e₁ = a₂' * e₂ := by
    apply mul_left_cancel₀ hg0
    rw [ha₁, ha₂] at h; linear_combination h
  obtain ⟨u, hu⟩ : a₂' ∣ e₁ := hcop.symm.dvd_of_dvd_mul_left ⟨e₂, by linear_combination h'⟩
  obtain ⟨v, hv⟩ : a₁' ∣ e₂ := hcop.dvd_of_dvd_mul_left ⟨e₁, by linear_combination -h'⟩
  have huv : u = v := by
    apply mul_left_cancel₀ (mul_ne_zero ha₁' ha₂')
    rw [hu, hv] at h'; linear_combination h'
  subst huv
  have d1 : g ∣ a₁ := ⟨a₁', ha₁⟩
  have d2 : g ∣ a₂ := ⟨a₂', ha₂⟩
  have f1 : a₁' ∣ a₁ := ⟨g, by rw [ha₁]; ring⟩
  have f2 : a₂' ∣ a₂ := ⟨g, by rw [ha₂]; ring⟩
  have k1 : u ∣ e₁ := ⟨a₂', by rw [hu]; ring⟩
  have k2 : u ∣ e₂ := ⟨a₁', by rw [hv]; ring⟩
  have t1 : a₂' ∣ e₁ := ⟨u, hu⟩
  have t2 : a₁' ∣ e₂ := ⟨u, hv⟩
  exact ⟨g, a₁', a₂', u, rfl, hg0, ha₁, ha₂, hu, hv,
    (c2.of_isCoprime_of_dvd_left d2).of_isCoprime_of_dvd_right t2,
    (c1.of_isCoprime_of_dvd_left d1).of_isCoprime_of_dvd_right t1, hcop,
    (c1.of_isCoprime_of_dvd_left d1).of_isCoprime_of_dvd_right k1,
    (c1.of_isCoprime_of_dvd_left f1).of_isCoprime_of_dvd_right k1,
    (c2.of_isCoprime_of_dvd_left f2).of_isCoprime_of_dvd_right k2⟩

private theorem ambF_a (D x : ℤ) : (ambF D x).a = x := by simp [ambF]
private theorem ambF_b (D x : ℤ) : (ambF D x).b = 0 := by simp [ambF]
private theorem ambG_a (D x : ℤ) : (ambG D x).a = x := by simp [ambG]
private theorem ambG_b (D x : ℤ) : (ambG D x).b = x := by simp [ambG]

private theorem dvd_two_mul_of_odd (x : ℤ) {y : ℤ} (h : y % 2 = 1) : 2 * x ∣ x * y - x := by
  obtain ⟨k, hk⟩ : ∃ k, y = 2 * k + 1 := ⟨y / 2, by omega⟩
  exact ⟨k, by rw [hk]; ring⟩

/-- **Composition of two coprime classes of forms, moving to a common middle coefficient `B`.** -/
private theorem mul_of_coprime [NonzeroDisc D] (X Y Z : PrimForm D) (hX : X.1.a ≠ 0) (hY : Y.1.a ≠ 0)
    (hcop : IsCoprime X.1.a Y.1.a) {B : ℤ} (hB1 : 2 * X.1.a ∣ B - X.1.b) (hB2 : 2 * Y.1.a ∣ B - Y.1.b)
    (hZa : Z.1.a = X.1.a * Y.1.a) (hZb : Z.1.b = B) : mk X * mk Y = mk Z := by
  obtain ⟨X', eX, haX, hbX⟩ := exists_sLEquiv_b (f := X.1) (B := B) hB1
  obtain ⟨Y', eY, haY, hbY⟩ := exists_sLEquiv_b (f := Y.1) (B := B) hB2
  have hc : Concordant (ofEquiv X eX).1 (ofEquiv Y eY).1 := by
    simp only [val_ofEquiv]
    refine concordant_of_coprime ?_ (by rw [hbX, hbY]) ?_ ?_
    · rw [haX, haY]; exact mul_ne_zero hX hY
    · rw [← SLEquiv.disc_eq eX, ← SLEquiv.disc_eq eY, X.2.2, Y.2.2]
    · rw [haX, haY]; exact hcop
  calc mk X * mk Y = mk (ofEquiv X eX) * mk (ofEquiv Y eY) := by rw [mk_ofEquiv, mk_ofEquiv]
    _ = mk (PrimForm.comp _ _ hc) := mk_mul_mk _ _ hc
    _ = mk Z := by
      refine mk_eq_mk.2 ?_
      have : (PrimForm.comp _ _ hc).1 = Z.1 := by
        apply eq_of_a_b_disc
        · rw [primComp_a]; simp only [val_ofEquiv]; rw [haX, haY]; exact mul_ne_zero hX hY
        · rw [primComp_a]; simp only [val_ofEquiv]; rw [haX, haY, hZa]
        · rw [primComp_b]; simp only [val_ofEquiv]; rw [hbX, hZb]
        · exact (PrimForm.comp _ _ hc).2.2.trans Z.2.2.symm
      rw [this]; exact SLEquiv.refl _

/-- **(6.8)–(6.9): every element of $\mathcal B$ has order dividing $2$** (Cassels, Ch. 14, (6.8)–(6.9), p. 347): the
class of a primitive ambiguous form squares to the unit class. -/
@[kb "cassels1978" "Ch. 14, §6, (6.8)–(6.9), p. 347"]
theorem mk_sq_of_isAmbiguousForm [NonzeroDisc D] (f : PrimForm D) (h : IsAmbiguousForm f.1) : mk f ^ 2 = 1 :=
  isAmbiguous_of_isAmbiguousForm f h

/-- **Cassels, Ch. 14, Lemma 6.1, rule (6.10)–(6.11)** (p. 347): *$f(a_1) * f(a_2) = f(a_3)$ where
$a_1a_2 = a_3\gcd(a_1, a_2)^2$*, and taking classes respects it: for primitive forms $f(a_1)$, $f(a_2)$ of
discriminant $D$, the form $f(a_3)$ is a primitive form of discriminant $D$ and its class is the product of the
classes. (This holds for every $D \ne 0$; for $D$ odd there are no forms $f(a)$.) -/
@[kb "cassels1978" "Ch. 14, Lemma 6.1, (6.10)–(6.11), p. 347"]
theorem mk_mul_mk_ambF [NonzeroDisc D] {a₁ a₂ : ℤ} (f₁ f₂ : PrimForm D) (h₁ : f₁.1 = ambF D a₁)
    (h₂ : f₂.1 = ambF D a₂) :
    ∃ f₃ : PrimForm D, f₃.1 = ambF D (a₁ * a₂ / (Int.gcd a₁ a₂ : ℤ) ^ 2) ∧ mk f₁ * mk f₂ = mk f₃ := by
  obtain ⟨c₁, ha₁, hD1, hc1⟩ := extract_F f₁ h₁
  obtain ⟨c₂, ha₂, hD2, hc2⟩ := extract_F f₂ h₂
  obtain ⟨g, b₁, b₂, v, hg, hg0, e1, e2, ec1, ec2, cg1, cg2, c12, cgv, c1v, c2v⟩ :=
    split_pairs ha₁ ha₂ (by linarith) hc1 hc2
  obtain ⟨Fg, hFg⟩ := exists_primF (D := D) (x := g) (y := b₁ * b₂ * v) (by rw [hD1, e1, ec1]; ring)
    ((cg1.mul_right cg2).mul_right cgv)
  obtain ⟨F1, hF1⟩ := exists_primF (D := D) (x := b₁) (y := g * b₂ * v) (by rw [hD1, e1, ec1]; ring)
    ((cg1.symm.mul_right c12).mul_right c1v)
  obtain ⟨F2, hF2⟩ := exists_primF (D := D) (x := b₂) (y := g * b₁ * v) (by rw [hD2, e2, ec2]; ring)
    ((cg2.symm.mul_right c12.symm).mul_right c2v)
  obtain ⟨F3, hF3⟩ := exists_primF (D := D) (x := b₁ * b₂) (y := g * v) (by rw [hD1, e1, ec1]; ring)
    ((cg1.symm.mul_right c1v).mul_left (cg2.symm.mul_right c2v))
  have hdiv : a₁ * a₂ / (Int.gcd a₁ a₂ : ℤ) ^ 2 = b₁ * b₂ := by
    rw [← hg, e1, e2, show g * b₁ * (g * b₂) = b₁ * b₂ * g ^ 2 by ring]
    exact Int.mul_ediv_cancel _ (pow_ne_zero 2 hg0)
  refine ⟨F3, by rw [hF3, hdiv], ?_⟩
  have hg0' : Fg.1.a ≠ 0 := by rw [hFg, ambF_a]; exact hg0
  have hb0' : F1.1.a ≠ 0 := by rw [hF1, ambF_a]; exact right_ne_zero_of_mul (e1 ▸ ha₁)
  have hb0'' : F2.1.a ≠ 0 := by rw [hF2, ambF_a]; exact right_ne_zero_of_mul (e2 ▸ ha₂)
  have m1 : mk Fg * mk F1 = mk f₁ := mul_of_coprime Fg F1 f₁ hg0' hb0'
    (by rw [hFg, hF1, ambF_a, ambF_a]; exact cg1) (B := 0)
    (by rw [hFg, ambF_b]; simp) (by rw [hF1, ambF_b]; simp)
    (by rw [h₁, hFg, hF1, ambF_a, ambF_a, ambF_a]; exact e1) (by rw [h₁, ambF_b])
  have m2 : mk Fg * mk F2 = mk f₂ := mul_of_coprime Fg F2 f₂ hg0' hb0''
    (by rw [hFg, hF2, ambF_a, ambF_a]; exact cg2) (B := 0)
    (by rw [hFg, ambF_b]; simp) (by rw [hF2, ambF_b]; simp)
    (by rw [h₂, hFg, hF2, ambF_a, ambF_a, ambF_a]; exact e2) (by rw [h₂, ambF_b])
  have m3 : mk F1 * mk F2 = mk F3 := mul_of_coprime F1 F2 F3 hb0' hb0''
    (by rw [hF1, hF2, ambF_a, ambF_a]; exact c12) (B := 0)
    (by rw [hF1, ambF_b]; simp) (by rw [hF2, ambF_b]; simp)
    (by rw [hF1, hF2, hF3, ambF_a, ambF_a, ambF_a]) (by rw [hF3, ambF_b])
  exact glue_classes m1.symm m2.symm (mk_sq_of_isAmbiguousForm Fg (Or.inl (by rw [hFg, ambF_b]))) m3


/-- **Cassels, Ch. 14, Lemma 6.1, case (i), rule (6.13)** (p. 347): *for $D$ odd, $g(a_1) * g(a_2) = g(a_3)$ where
$a_1a_2 = a_3\gcd(a_1, a_2)^2$*, and taking classes respects it. -/
@[kb "cassels1978" "Ch. 14, Lemma 6.1, case (i), (6.12)–(6.13), p. 347"]
theorem mk_mul_mk_ambG [NonzeroDisc D] (hD : D % 2 = 1) {a₁ a₂ : ℤ} (f₁ f₂ : PrimForm D)
    (h₁ : f₁.1 = ambG D a₁) (h₂ : f₂.1 = ambG D a₂) :
    ∃ f₃ : PrimForm D, f₃.1 = ambG D (a₁ * a₂ / (Int.gcd a₁ a₂ : ℤ) ^ 2) ∧ mk f₁ * mk f₂ = mk f₃ := by
  obtain ⟨c₁, ha₁, hD1, hc1⟩ := extract_G hD f₁ h₁
  obtain ⟨c₂, ha₂, hD2, hc2⟩ := extract_G hD f₂ h₂
  obtain ⟨g, b₁, b₂, v, hg, hg0, e1, e2, ec1, ec2, cg1, cg2, c12, cgv, c1v, c2v⟩ :=
    split_pairs ha₁ ha₂ (by rw [← hD1, ← hD2]) hc1 hc2
  have hDg : D = g * (b₁ * b₂ * v) := by rw [hD1, e1, ec1]; ring
  have hD1' : D = b₁ * (g * b₂ * v) := by rw [hD1, e1, ec1]; ring
  have hD2' : D = b₂ * (g * b₁ * v) := by rw [hD2, e2, ec2]; ring
  have hD3 : D = b₁ * b₂ * (g * v) := by rw [hD1, e1, ec1]; ring
  obtain ⟨Gg, hGg⟩ := exists_primG hD hDg ((cg1.mul_right cg2).mul_right cgv)
  obtain ⟨G1, hG1⟩ := exists_primG hD hD1' ((cg1.symm.mul_right c12).mul_right c1v)
  obtain ⟨G2, hG2⟩ := exists_primG hD hD2' ((cg2.symm.mul_right c12.symm).mul_right c2v)
  obtain ⟨G3, hG3⟩ := exists_primG hD hD3 ((cg1.symm.mul_right c1v).mul_left (cg2.symm.mul_right c2v))
  have og : g % 2 = 1 := odd_of_mul (y := b₁ * b₂ * v) (by rw [← hDg]; exact hD)
  have o1 : b₁ % 2 = 1 := odd_of_mul (y := g * b₂ * v) (by rw [← hD1']; exact hD)
  have o2 : b₂ % 2 = 1 := odd_of_mul (y := g * b₁ * v) (by rw [← hD2']; exact hD)
  have hdiv : a₁ * a₂ / (Int.gcd a₁ a₂ : ℤ) ^ 2 = b₁ * b₂ := by
    rw [← hg, e1, e2, show g * b₁ * (g * b₂) = b₁ * b₂ * g ^ 2 by ring]
    exact Int.mul_ediv_cancel _ (pow_ne_zero 2 hg0)
  refine ⟨G3, by rw [hG3, hdiv], ?_⟩
  have z0 : Gg.1.a ≠ 0 := by rw [hGg, ambG_a]; exact hg0
  have z1 : G1.1.a ≠ 0 := by rw [hG1, ambG_a]; exact right_ne_zero_of_mul (e1 ▸ ha₁)
  have z2 : G2.1.a ≠ 0 := by rw [hG2, ambG_a]; exact right_ne_zero_of_mul (e2 ▸ ha₂)
  have m1 : mk Gg * mk G1 = mk f₁ := mul_of_coprime Gg G1 f₁ z0 z1
    (by rw [hGg, hG1, ambG_a, ambG_a]; exact cg1) (B := a₁)
    (by rw [hGg, ambG_a, ambG_b, e1]; exact dvd_two_mul_of_odd g o1)
    (by rw [hG1, ambG_a, ambG_b, e1, mul_comm g b₁]; exact dvd_two_mul_of_odd b₁ og)
    (by rw [h₁, hGg, hG1, ambG_a, ambG_a, ambG_a]; exact e1) (by rw [h₁, ambG_b])
  have m2 : mk Gg * mk G2 = mk f₂ := mul_of_coprime Gg G2 f₂ z0 z2
    (by rw [hGg, hG2, ambG_a, ambG_a]; exact cg2) (B := a₂)
    (by rw [hGg, ambG_a, ambG_b, e2]; exact dvd_two_mul_of_odd g o2)
    (by rw [hG2, ambG_a, ambG_b, e2, mul_comm g b₂]; exact dvd_two_mul_of_odd b₂ og)
    (by rw [h₂, hGg, hG2, ambG_a, ambG_a, ambG_a]; exact e2) (by rw [h₂, ambG_b])
  have m3 : mk G1 * mk G2 = mk G3 := mul_of_coprime G1 G2 G3 z1 z2
    (by rw [hG1, hG2, ambG_a, ambG_a]; exact c12) (B := b₁ * b₂)
    (by rw [hG1, ambG_a, ambG_b]; exact dvd_two_mul_of_odd b₁ o2)
    (by rw [hG2, ambG_a, ambG_b, mul_comm b₁ b₂]; exact dvd_two_mul_of_odd b₂ o1)
    (by rw [hG1, hG2, hG3, ambG_a, ambG_a, ambG_a]) (by rw [hG3, ambG_b])
  exact glue_classes m1.symm m2.symm (mk_sq_of_isAmbiguousForm Gg (Or.inr (by rw [hGg, ambG_a, ambG_b]))) m3


private theorem extract_G2 [NonzeroDisc D] (hD : D % 16 = 12) {α : ℤ} (f : PrimForm D)
    (h : f.1 = ambG D (2 * α)) : ∃ y, D = 4 * (α * y) ∧ IsCoprime α y := by
  obtain ⟨hp, hd⟩ := f.2
  rw [h] at hp hd
  obtain ⟨c, hc⟩ : ∃ c, ambG D (2 * α) = BinQF.mk (2 * α) (2 * α) c := ⟨_, rfl⟩
  rw [hc] at hp hd
  simp only [BinQF.disc, a_mk, b_mk, c_mk] at hd hp
  have hD' : D = 4 * (α * (α - 2 * c)) := by linear_combination -hd
  have hα : α % 2 = 1 := odd_of_mul (y := α - 2 * c) (by omega)
  have h1 : IsCoprime α c := isCoprime_of_prim fun d h1 h3 => hp d (h1.mul_left 2) (h1.mul_left 2) h3
  exact ⟨α - 2 * c, hD', isCoprime_sub_self ((isCoprime_two_of_odd hα).mul_right h1)⟩

private theorem exists_primG2 [NonzeroDisc D] (hD : D % 16 = 12) {x y : ℤ} (hxy : D = 4 * (x * y))
    (hc : IsCoprime x y) : ∃ f : PrimForm D, f.1 = ambG D (2 * x) := by
  have hP : (x * y) % 4 = 3 := by omega
  have hx : x % 2 = 1 := odd_of_mul (y := y) (by omega)
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h4 : (x - y) % 4 = 2 := sub_mod_four_of_mul' hP
  rw [ambG_eq (x := 2 * x) (y := 2 * y) (mul_ne_zero two_ne_zero hx0) (by rw [hxy]; ring)]
  obtain ⟨c, hcdef⟩ : ∃ c, c = (x - y) / 2 := ⟨_, rfl⟩
  have hc2 : 2 * c = x - y := by omega
  have hco : c % 2 = 1 := by omega
  have e : (2 * x - 2 * y) / 4 = c := by omega
  rw [e]
  have hxc : IsCoprime x c := isCoprime_of_prim fun d h1 h3 =>
    hc.isUnit_of_dvd' h1 (by
      have : y = x - 2 * c := by linarith
      rw [this]; exact dvd_sub h1 (h3.mul_left 2))
  have hcop : IsCoprime (2 * x) c := ((isCoprime_two_of_odd hco).symm).mul_left hxc
  refine ⟨⟨BinQF.mk (2 * x) (2 * x) c, ?_, ?_⟩, rfl⟩
  · intro d h1 _ h3
    simp only [a_mk, c_mk] at h1 h3
    exact hcop.isUnit_of_dvd' h1 h3
  · simp only [BinQF.disc, a_mk, b_mk, c_mk]
    rw [hxy]; linear_combination (-4 * x) * hc2

private theorem exists_T [NonzeroDisc D] (hD : D % 16 = 12) : ∃ T : PrimForm D, T.1 = ambG D 2 := by
  obtain ⟨T, hT⟩ := exists_primG2 hD (x := 1) (y := D / 4) (by omega) isCoprime_one_left
  exact ⟨T, by simpa using hT⟩

private theorem G2_eq_F_mul [NonzeroDisc D] (hD : D % 16 = 12) {x : ℤ} (Fx Gx T : PrimForm D)
    (hF : Fx.1 = ambF D x) (hG : Gx.1 = ambG D (2 * x)) (hT : T.1 = ambG D 2) :
    mk Gx = mk Fx * mk T := by
  obtain ⟨y, hx0, hDx, hcop⟩ := extract_F Fx hF
  have hP : D = -4 * (x * y) := by linarith
  have hx : x % 2 = 1 := odd_of_mul (y := y) (by omega)
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  exact (mul_of_coprime Fx T Gx (by rw [hF, ambF_a]; exact hx0) (by rw [hT, ambG_a]; norm_num)
    (by rw [hF, hT, ambF_a, ambG_a]; exact isCoprime_two_of_odd hx) (B := 2 * x)
    (by rw [hF, ambF_a, ambF_b]; simp)
    (by rw [hT, ambG_a, ambG_b]; exact ⟨k, by rw [hk]; ring⟩)
    (by rw [hG, hF, hT, ambG_a, ambF_a, ambG_a]; ring) (by rw [hG, ambG_b])).symm

/-- **Cassels, Ch. 14, Lemma 6.1, case (iii), mixed products** (p. 347; table reconstructed, see the module
docstring): *for $D = 4d$, $d \equiv -1 \pmod 4$: $f(\alpha_1) * g(2\alpha_2) = g(2\alpha_3)$ with
$\alpha_1\alpha_2 = \alpha_3\gcd(\alpha_1, \alpha_2)^2$* (6.14), and taking classes respects it. -/
@[kb "cassels1978" "Ch. 14, Lemma 6.1, case (iii), (6.14), p. 347 (table reconstructed)"]
theorem mk_mul_mk_ambF_ambG [NonzeroDisc D] (hD : D % 16 = 12) {α₁ α₂ : ℤ} (f₁ f₂ : PrimForm D)
    (h₁ : f₁.1 = ambF D α₁) (h₂ : f₂.1 = ambG D (2 * α₂)) :
    ∃ f₃ : PrimForm D, f₃.1 = ambG D (2 * (α₁ * α₂ / (Int.gcd α₁ α₂ : ℤ) ^ 2)) ∧ mk f₁ * mk f₂ = mk f₃ := by
  obtain ⟨y₂, hD2, hc2⟩ := extract_G2 hD f₂ h₂
  obtain ⟨F₂, hF₂⟩ := exists_primF (D := D) (x := α₂) (y := -y₂) (by rw [hD2]; ring) hc2.neg_right
  obtain ⟨T, hT⟩ := exists_T hD
  obtain ⟨f₃, hf₃, hm⟩ := mk_mul_mk_ambF f₁ F₂ h₁ hF₂
  obtain ⟨γ, -, hDγ, hcγ⟩ := extract_F f₃ hf₃
  obtain ⟨G₃, hG₃⟩ := exists_primG2 hD (x := α₁ * α₂ / (Int.gcd α₁ α₂ : ℤ) ^ 2) (y := -γ)
    (by rw [hDγ]; ring) hcγ.neg_right
  refine ⟨G₃, hG₃, ?_⟩
  calc mk f₁ * mk f₂ = mk f₁ * (mk F₂ * mk T) := by rw [G2_eq_F_mul hD F₂ f₂ T hF₂ h₂ hT]
    _ = (mk f₁ * mk F₂) * mk T := (mul_assoc _ _ _).symm
    _ = mk f₃ * mk T := by rw [hm]
    _ = mk G₃ := (G2_eq_F_mul hD f₃ G₃ T hf₃ hG₃ hT).symm


/-- **Cassels, Ch. 14, Lemma 6.1, case (iii), products of forms of the second kind** (p. 347; table reconstructed,
see the module docstring): *for $D = 4d$, $d \equiv -1 \pmod 4$: $g(2\alpha_1) * g(2\alpha_2) = f(\alpha_3)$ with
$\alpha_1\alpha_2 = \alpha_3\gcd(\alpha_1, \alpha_2)^2$* (6.14), and taking classes respects it. -/
@[kb "cassels1978" "Ch. 14, Lemma 6.1, case (iii), (6.14), p. 347 (table reconstructed)"]
theorem mk_mul_mk_ambG_ambG [NonzeroDisc D] (hD : D % 16 = 12) {α₁ α₂ : ℤ} (f₁ f₂ : PrimForm D)
    (h₁ : f₁.1 = ambG D (2 * α₁)) (h₂ : f₂.1 = ambG D (2 * α₂)) :
    ∃ f₃ : PrimForm D, f₃.1 = ambF D (α₁ * α₂ / (Int.gcd α₁ α₂ : ℤ) ^ 2) ∧ mk f₁ * mk f₂ = mk f₃ := by
  obtain ⟨y₁, hD1, hc1⟩ := extract_G2 hD f₁ h₁
  obtain ⟨y₂, hD2, hc2⟩ := extract_G2 hD f₂ h₂
  obtain ⟨F₁, hF₁⟩ := exists_primF (D := D) (x := α₁) (y := -y₁) (by rw [hD1]; ring) hc1.neg_right
  obtain ⟨F₂, hF₂⟩ := exists_primF (D := D) (x := α₂) (y := -y₂) (by rw [hD2]; ring) hc2.neg_right
  obtain ⟨T, hT⟩ := exists_T hD
  obtain ⟨f₃, hf₃, hm⟩ := mk_mul_mk_ambF F₁ F₂ hF₁ hF₂
  refine ⟨f₃, hf₃, ?_⟩
  exact glue_classes (g := mk T) (by rw [G2_eq_F_mul hD F₁ f₁ T hF₁ h₁ hT, mul_comm])
    (by rw [G2_eq_F_mul hD F₂ f₂ T hF₂ h₂ hT, mul_comm])
    (mk_sq_of_isAmbiguousForm T (Or.inr (by rw [hT, ambG_a, ambG_b]))) hm


end QuadFormsKB.Composition
