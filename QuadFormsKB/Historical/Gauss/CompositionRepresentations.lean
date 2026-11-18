import QuadFormsKB.Historical.Gauss.MatrixLemma
import QuadFormsKB.Historical.Gauss.RootForms

/-!
# Primitive representations under composition (Disquisitiones Arithmeticae, Art. 244)

(Art. 244, second part: primitive representations multiply and the roots combine by
the Chinese remainder theorem).

Notation as in Gauss: $(a, b, c)$ is `gaussForm a b c` $= a x^2 + 2 b x y + c y^2$, its determinant is
`gaussDet a b c` $= b^2 - a c$.

## What is proved

* `art244_represents_mul` (Art. 244, first part): if $F$ is compounded of $f$, $f'$, $f$ represents $a$ and $f'$
  represents $a'$, then $F$ represents $a a'$ (by the bilinear substitution of Art. 235).
* `isCompounded_united` (Dirichlet's united forms in Gauss's notation): $(a a', B, k)$ is compounded of
  $(a, B, a' k)$ and $(a', B, a k)$ as soon as $\gcd(a, a', 2B) = 1$.
* `exists_united_root`: for $a \mid b^2 - D$, $a' \mid b'^2 - D$, $\gcd(a, a', b + b') = 1$ there is $B$ with
  $B \equiv b \pmod a$, $B \equiv b' \pmod{a'}$, $a a' \mid B^2 - D$.
* `art244_primitive_representation_mul` (the case $\mu = 1$ of the second part): the headline. Uniqueness of the
  compound up to proper equivalence is taken from Art. 239 (`art239_contains`).
* `art244_primitive_representation_mul_of_coprime`: the special case $\gcd(a, a') = 1$.

## What is only stated

* `Art244GeneralModulus`: the case of general $\mu = \gcd(a, a', b + b')$ (the compound is properly equivalent to
  $(A, B, C)$ with $A = a a' / \mu^2$, and represents $a a'$ with values of gcd $\mu$). Not proved: it needs the
  compound of the two forms for $\mu > 1$ (Gauss, Art. 243), which is not in the library.
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-! ### Part 1: multiplicativity -/

/-- **Representations multiply under composition** (*Disq. Arith.* Art. 244, first part):
if $F$ is compounded of $f$ and $f'$ (`IsCompounded`), $f$ represents $a$ ($f(x, y) = a$) and $f'$ represents $a'$,
then $F$ represents $a a'$, namely at $(X, Y) = (\text{bilin } p\ x\,y\,x'\,y', \text{bilin } q\ x\,y\,x'\,y')$,
where $(p, q)$ is the bilinear substitution of Art. 235. Proved exactly as stated by Gauss (no primitivity of the
representations; this part needs nothing but `TransformsInto`). -/
@[kb "gauss1801" "Art. 244"]
theorem art244_represents_mul {F f f' : BinQF} (h : IsCompounded F f f') {a a' : ℤ}
    (hf : ∃ x y : ℤ, f.eval x y = a) (hf' : ∃ x y : ℤ, f'.eval x y = a') :
    ∃ X Y : ℤ, F.eval X Y = a * a' := by
  obtain ⟨p, q, hT, -⟩ := h
  obtain ⟨x, y, rfl⟩ := hf
  obtain ⟨x', y', rfl⟩ := hf'
  exact ⟨bilin p x y x' y', bilin q x y x' y', hT x y x' y'⟩

/-! ### Part 2: Dirichlet's united forms -/

/-- **The united forms are transformed into the product** (Dirichlet; Gauss, Art. 235): with
$X = x x' - k y y'$, $Y = a x y' + a' y x' + 2B y y'$ one has $(a a', B, k)(X, Y) = (a, B, a' k)(x, y) \cdot
(a', B, a k)(x', y')$ identically. -/
theorem transformsInto_united (a a' B k : ℤ) :
    TransformsInto (gaussForm (a * a') B k) (gaussForm a B (a' * k)) (gaussForm a' B (a * k))
      ![1, 0, 0, -k] ![0, a, a', 2 * B] := by
  intro x y x' y'
  simp only [bilin, eval_gaussForm]
  simp
  ring

/-- **Dirichlet's united forms are compounded in Gauss's sense** (Art. 244 with
Arts. 235-236): if $\gcd(a, a', 2B) = 1$ (every common divisor of $a$, $a'$, $2B$ is a unit) then
$(a a', B, k)$ is compounded directly (`IsCompounded`) of $(a, B, a' k)$ and $(a', B, a k)$, by
$X = x x' - k y y'$, $Y = a x y' + a' y x' + 2 B y y'$; the six numbers are $(a, a', 2B, 0, a k, a' k)$ and
$n = n' = 1$. Unlike `isCompounded_comp` no primitivity of the factors is assumed: the coprimality of the six
numbers is exactly $\gcd(a, a', 2B) = 1$. -/
@[kb "gauss1801" "Art. 244"]
theorem isCompounded_united {a a' B k : ℤ} (hcop : ∀ d : ℤ, d ∣ a → d ∣ a' → d ∣ 2 * B → IsUnit d) :
    IsCompounded (gaussForm (a * a') B k) (gaussForm a B (a' * k)) (gaussForm a' B (a * k)) := by
  refine ⟨![1, 0, 0, -k], ![0, a, a', 2 * B], transformsInto_united a a' B k, ?_, 1, 1, one_pos, one_pos, ?_⟩
  · intro d hd
    have h0 : d ∣ a := by simpa [minors] using hd 0
    have h1 : d ∣ a' := by simpa [minors] using hd 1
    have h2 : d ∣ 2 * B := by simpa [minors] using hd 2
    exact hcop d h0 h1 h2
  · simp [minors]

/-- **The root $B$ of the united forms** (Dirichlet; Gauss, Art. 244): if $a, a' \ne 0$, $a \mid b^2 - D$,
$a' \mid b'^2 - D$ and $\gcd(a, a', b + b') = 1$, there is $B$ with $B \equiv b \pmod a$, $B \equiv b' \pmod{a'}$
and $a a' \mid B^2 - D$. Proof: with $g = \gcd(a, a')$, $g \mid b - b'$ since $g \mid b^2 - b'^2$ and $g$ is
prime to $b + b'$; the Chinese remainder theorem (Bezout for $a$, $a'$) gives $B_0$; then
$B = B_0 + (a a'/g)\,t$ is corrected modulo $a a'$ using that $2B_0$ is invertible modulo $g$. -/
theorem exists_united_root {a a' b b' D : ℤ} (ha : a ≠ 0) (_ha' : a' ≠ 0) (h : a ∣ b ^ 2 - D)
    (h' : a' ∣ b' ^ 2 - D) (hμ : Int.gcd (Int.gcd a a') (b + b') = 1) :
    ∃ B : ℤ, B ≡ b [ZMOD a] ∧ B ≡ b' [ZMOD a'] ∧ a * a' ∣ B ^ 2 - D := by
  obtain ⟨g, hg⟩ : ∃ g : ℤ, g = (Int.gcd a a' : ℤ) := ⟨_, rfl⟩
  have hgpos : 0 < g := by
    rw [hg]; exact_mod_cast Int.gcd_pos_iff.mpr (Or.inl ha)
  have hga : g ∣ a := by rw [hg]; exact Int.gcd_dvd_left a a'
  have hga' : g ∣ a' := by rw [hg]; exact Int.gcd_dvd_right a a'
  obtain ⟨α, hα⟩ := hga
  obtain ⟨α', hα'⟩ := hga'
  have hcop : IsCoprime α α' := by
    have := Int.gcd_div_gcd_div_gcd (i := a) (j := a') (Int.gcd_pos_iff.mpr (Or.inl ha))
    rw [← hg, Int.ediv_eq_of_eq_mul_right hgpos.ne' hα, Int.ediv_eq_of_eq_mul_right hgpos.ne' hα'] at this
    exact Int.isCoprime_iff_gcd_eq_one.mpr this
  have hgb : IsCoprime g (b + b') := by
    rw [hg]; exact Int.isCoprime_iff_gcd_eq_one.mpr hμ
  have hgdvd : g ∣ b - b' := by
    apply hgb.dvd_of_dvd_mul_right
    have h1 : g ∣ b ^ 2 - D := (Dvd.intro _ hα.symm).trans h
    have h2 : g ∣ b' ^ 2 - D := (Dvd.intro _ hα'.symm).trans h'
    have := dvd_sub h1 h2
    convert this using 1; ring
  obtain ⟨t, ht⟩ := hgdvd
  have hbez : g = a * Int.gcdA a a' + a' * Int.gcdB a a' := by
    rw [hg]; exact Int.gcd_eq_gcd_ab a a'
  obtain ⟨u, hu⟩ : ∃ u, u = Int.gcdA a a' := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = Int.gcdB a a' := ⟨_, rfl⟩
  rw [← hu, ← hv] at hbez
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℤ, B₀ = b - a * (t * u) := ⟨_, rfl⟩
  have hB0a : a ∣ B₀ - b := ⟨-(t * u), by rw [hB₀]; ring⟩
  have hB0b' : B₀ - b' = a' * (t * v) := by
    rw [hB₀]; linear_combination ht + t * hbez
  have hB0a' : a' ∣ B₀ - b' := ⟨t * v, hB0b'⟩
  have hN : a ∣ B₀ ^ 2 - D := by
    have := dvd_add h (dvd_mul_of_dvd_left hB0a (B₀ + b))
    convert this using 1; ring
  have hN' : a' ∣ B₀ ^ 2 - D := by
    have := dvd_add h' (dvd_mul_of_dvd_left hB0a' (B₀ + b'))
    convert this using 1; ring
  obtain ⟨m, hm⟩ := hN
  obtain ⟨m', hm'⟩ := hN'
  have hmm : α * m = α' * m' := by
    apply mul_left_cancel₀ hgpos.ne'
    linear_combination hm' - hm - m * hα + m' * hα'
  have hα'm : α' ∣ m := hcop.symm.dvd_of_dvd_mul_left ⟨m', hmm⟩
  obtain ⟨w, hw⟩ := hα'm
  have hNw : B₀ ^ 2 - D = g * α * α' * w := by
    rw [hm, hα, hw]; ring
  -- invertibility of `2 * B₀` modulo `g`
  obtain ⟨e, he⟩ : g ∣ 2 * B₀ - (b + b') := by
    have h1 : g ∣ B₀ - b := (Dvd.intro _ hα.symm).trans hB0a
    have h2 : g ∣ B₀ - b' := (Dvd.intro _ hα'.symm).trans hB0a'
    have := dvd_add h1 h2
    convert this using 1; ring
  obtain ⟨u₂, v₂, huv⟩ := hgb
  have hbez2 : (u₂ - v₂ * e) * g + v₂ * (2 * B₀) = 1 := by
    linear_combination huv + v₂ * he
  obtain ⟨t₂, ht₂⟩ : ∃ t₂ : ℤ, t₂ = -w * v₂ := ⟨_, rfl⟩
  refine ⟨B₀ + g * α * α' * t₂, ?_, ?_, ?_⟩
  · refine Int.modEq_iff_dvd.mpr ⟨t * u - α' * t₂, ?_⟩
    linear_combination (-1 : ℤ) * hB₀ + α' * t₂ * hα
  · refine Int.modEq_iff_dvd.mpr ⟨-(t * v) - α * t₂, ?_⟩
    linear_combination (-1 : ℤ) * hB0b' + α * t₂ * hα'
  · have key : (B₀ + g * α * α' * t₂) ^ 2 - D = (g * α) * (g * α') * (w * (u₂ - v₂ * e) + α * α' * t₂ ^ 2) := by
      rw [ht₂]
      linear_combination hNw - g * α * α' * w * hbez2
    rw [hα, hα']
    exact ⟨_, key⟩

/-! ### Part 3: the headline -/

/-- **Art. 244, second part, case $\mu = 1$** (*Disq. Arith.* Art. 244): let
$f = (p, q, r)$, $f' = (p', q', r')$ have the same nonzero determinant $D$, let $F = (A, B_F, C)$ of determinant $D$
be compounded of $f$ and $f'$ (`IsCompounded`), let $a, a' \ne 0$ be represented primitively by $f$, $f'$ with values
(roots of $x^2 \equiv D$) $b \in$ `primitiveRepresentationValues p q r a`, $b' \in$
`primitiveRepresentationValues p' q' r' a'`, and $\gcd(a, a', b + b') = 1$ (in particular if $\gcd(a, a') = 1$, see
`art244_primitive_representation_mul_of_coprime`). Then there is $B$ with $B \equiv b \pmod a$,
$B \equiv b' \pmod{a'}$ and $B^2 - D = a a' k$, such that $F$ is properly equivalent to $(a a', B, k)$,
$F$ represents $a a'$ primitively and the representation belongs to the root $B$
(`B ∈ primitiveRepresentationValues A B_F C (a * a')`).

Proof: by Art. 168 (`art168_mem_values_iff`) $f$, $f'$ are properly equivalent to $(a, b, \cdot)$, $(a', b', \cdot)$,
and by `art224`-type shifts (`sLEquiv_of_modEq_roots`) to the united forms $(a, B, a' k)$, $(a', B, a k)$ with $B$ from
`exists_united_root`; composition is invariant under proper equivalence (`isCompounded_of_sLEquiv`), the united
composite $(a a', B, k)$ is compounded of the united forms (`isCompounded_united`), and two forms compounded of the
same two forms of nonzero determinant are properly equivalent when they have the same determinant (Art. 239,
`art239_contains`: the substitution has determinant $k'$ with $k'^2 = 1$, $k' > 0$).

Differences from Gauss: the hypotheses $a, a' \ne 0$, $D \ne 0$ (needed by Art. 239) and `F.disc = f.disc` ("same
determinant") are stated explicitly; the claim $B^2 \equiv D$ is part of the conclusion in the form
$B^2 - D = a a' k$. The general $\mu$ is `Art244GeneralModulus` (stated only). -/
@[kb "gauss1801" "Art. 244"]
theorem art244_primitive_representation_mul {p q r p' q' r' A B_F C a b a' b' : ℤ}
    (hD : gaussDet p q r = gaussDet p' q' r') (hD0 : gaussDet p q r ≠ 0)
    (hF : IsCompounded (gaussForm A B_F C) (gaussForm p q r) (gaussForm p' q' r'))
    (hFD : gaussDet A B_F C = gaussDet p q r) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ∈ primitiveRepresentationValues p q r a) (hb' : b' ∈ primitiveRepresentationValues p' q' r' a')
    (hμ : Int.gcd (Int.gcd a a') (b + b') = 1) :
    ∃ B k : ℤ, B ≡ b [ZMOD a] ∧ B ≡ b' [ZMOD a'] ∧ B ^ 2 - gaussDet p q r = a * a' * k ∧
      SLEquiv (gaussForm A B_F C) (gaussForm (a * a') B k) ∧
      B ∈ primitiveRepresentationValues A B_F C (a * a') ∧ HasPrimitiveRepresentation (gaussForm A B_F C) (a * a') := by
  obtain ⟨hd1, e1⟩ := (art168_mem_values_iff ha b).mp hb
  obtain ⟨hd1', e1'⟩ := (art168_mem_values_iff ha' b').mp hb'
  rw [← hD] at hd1' e1'
  obtain ⟨B, hBa, hBa', hBk⟩ := exists_united_root ha ha' hd1 hd1' hμ
  obtain ⟨k, hk⟩ := hBk
  have hq1 : (B ^ 2 - gaussDet p q r) / a = a' * k :=
    Int.ediv_eq_of_eq_mul_right ha (by linear_combination hk)
  have hq2 : (B ^ 2 - gaussDet p q r) / a' = a * k :=
    Int.ediv_eq_of_eq_mul_right ha' (by linear_combination hk)
  have s1 : SLEquiv (gaussForm p q r) (gaussForm a B (a' * k)) := by
    rw [← hq1]; exact e1.trans (sLEquiv_of_modEq_roots ha hd1 hBa.symm)
  have s2 : SLEquiv (gaussForm p' q' r') (gaussForm a' B (a * k)) := by
    rw [← hq2]
    exact e1'.trans (sLEquiv_of_modEq_roots ha' hd1' hBa'.symm)
  have hFg : IsCompounded (gaussForm A B_F C) (gaussForm a B (a' * k)) (gaussForm a' B (a * k)) :=
    isCompounded_of_sLEquiv hF s1 s2
  have hcop : ∀ d : ℤ, d ∣ a → d ∣ a' → d ∣ 2 * B → IsUnit d := by
    intro d h1 h2 h3
    have e3 : d ∣ b + b' := by
      have x1 : d ∣ B - b := h1.trans (Int.modEq_iff_dvd.mp hBa.symm)
      have x2 : d ∣ B - b' := h2.trans (Int.modEq_iff_dvd.mp hBa'.symm)
      have := dvd_sub (dvd_sub h3 x1) x2
      convert this using 1; ring
    have : d ∣ ((Int.gcd (Int.gcd a a') (b + b') : ℕ) : ℤ) :=
      Int.dvd_coe_gcd (Int.dvd_coe_gcd h1 h2) e3
    rw [hμ] at this
    exact isUnit_of_dvd_one (by simpa using this)
  have hG := isCompounded_united (k := k) hcop
  have hdetG : gaussDet (a * a') B k = gaussDet p q r := by
    unfold gaussDet at hk ⊢; linear_combination hk
  obtain ⟨p₁, q₁, hT', -, n₁, n₁', hn₁, hn₁', h0, h1, h2, h3, h4, h5⟩ := hG
  have hg0 : (gaussForm a B (a' * k)).disc ≠ 0 := by
    rw [disc_gaussForm]
    have : gaussDet a B (a' * k) = gaussDet p q r := by
      unfold gaussDet at hk ⊢; linear_combination hk
    rw [this]; exact mul_ne_zero four_ne_zero hD0
  have hg0' : (gaussForm a' B (a * k)).disc ≠ 0 := by
    rw [disc_gaussForm]
    have : gaussDet a' B (a * k) = gaussDet p q r := by
      unfold gaussDet at hk ⊢; linear_combination hk
    rw [this]; exact mul_ne_zero four_ne_zero hD0
  obtain ⟨α, β, γ, δ, k', hk'0, hk'det, hsub, hdisc⟩ :=
    art239_contains hFg hg0 hg0' hT' hn₁ hn₁' h0 h1 h2 h3 h4 h5
  rw [disc_gaussForm, disc_gaussForm, hFD, hdetG] at hdisc
  have h4D : (4 * gaussDet p q r) ≠ 0 := mul_ne_zero four_ne_zero hD0
  have hsq : k' ^ 2 = 1 := by
    apply mul_right_cancel₀ h4D
    rw [one_mul]
    linarith
  have hk1 : k' = 1 := by nlinarith
  subst hk1
  have hG : SLEquiv (gaussForm (a * a') B k) (gaussForm A B_F C) :=
    (sLEquiv_iff _ _).mpr ⟨α, β, γ, δ, hk'det, hsub⟩
  have hmem : B ∈ primitiveRepresentationValues (a * a') B k (a * a') :=
    ⟨1, 0, 1, 0, by ring, by rw [eval_gaussForm]; ring, by simp [art155Value]⟩
  have hmemF : B ∈ primitiveRepresentationValues A B_F C (a * a') := by
    rw [primitiveRepresentationValues_eq_of_sLEquiv hG.symm]; exact hmem
  refine ⟨B, k, hBa, hBa', hk, hG.symm, hmemF, ?_⟩
  obtain ⟨m, n, μ, ν, hb2, he, -⟩ := hmemF
  exact ⟨m, n, Int.isCoprime_iff_gcd_eq_one.mp ⟨μ, ν, by linarith⟩, he⟩

/-- **The case $\gcd(a, a') = 1$** (*Disq. Arith.* Art. 244): if $a$, $a'$ are coprime
then $\mu = 1$ and the conclusion of `art244_primitive_representation_mul` holds. -/
@[kb "gauss1801" "Art. 244"]
theorem art244_primitive_representation_mul_of_coprime {p q r p' q' r' A B_F C a b a' b' : ℤ}
    (hD : gaussDet p q r = gaussDet p' q' r') (hD0 : gaussDet p q r ≠ 0)
    (hF : IsCompounded (gaussForm A B_F C) (gaussForm p q r) (gaussForm p' q' r'))
    (hFD : gaussDet A B_F C = gaussDet p q r) (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hb : b ∈ primitiveRepresentationValues p q r a) (hb' : b' ∈ primitiveRepresentationValues p' q' r' a')
    (hcop : Int.gcd a a' = 1) :
    ∃ B k : ℤ, B ≡ b [ZMOD a] ∧ B ≡ b' [ZMOD a'] ∧ B ^ 2 - gaussDet p q r = a * a' * k ∧
      SLEquiv (gaussForm A B_F C) (gaussForm (a * a') B k) ∧
      B ∈ primitiveRepresentationValues A B_F C (a * a') ∧ HasPrimitiveRepresentation (gaussForm A B_F C) (a * a') :=
  art244_primitive_representation_mul hD hD0 hF hFD ha ha' hb hb' (by rw [hcop]; simp)

/-- **Art. 244, second part, general $\mu$ (stated, not proved)**: with the hypotheses of
`art244_primitive_representation_mul` except $\gcd(a, a', b + b') = 1$, put $\mu = \gcd(a, a', b + b')$. Then
$F$ is properly equivalent to a form $(A_0, B_0, C_0)$ of determinant $D$ with $A_0 \mu^2 = a a'$,
$B_0 \equiv b \pmod{a/\mu}$, $B_0 \equiv b' \pmod{a'/\mu}$, and $F$ represents $a a'$ by values $(x, y)$ with
$\gcd(x, y) = \mu$. Missing: Gauss's construction of the compound for $\mu > 1$ (Art. 243: divisibility of the
united forms by $\mu$ and the passage to $(a a'/\mu^2, \dots)$); the library has only the case $\mu = 1$
(`art244_primitive_representation_mul`). The statement is as Gauss prints it; it has not been checked for degenerate
cases beyond the hypotheses $a, a' \ne 0$, $D \ne 0$ added here. -/
def Art244GeneralModulus : Prop :=
  ∀ {p q r p' q' r' A B_F C a b a' b' : ℤ},
    gaussDet p q r = gaussDet p' q' r' → gaussDet p q r ≠ 0 →
    IsCompounded (gaussForm A B_F C) (gaussForm p q r) (gaussForm p' q' r') →
    gaussDet A B_F C = gaussDet p q r → a ≠ 0 → a' ≠ 0 →
    b ∈ primitiveRepresentationValues p q r a → b' ∈ primitiveRepresentationValues p' q' r' a' →
    ∃ A₀ B₀ C₀ : ℤ, A₀ * (Int.gcd (Int.gcd a a') (b + b') : ℤ) ^ 2 = a * a' ∧
      gaussDet A₀ B₀ C₀ = gaussDet p q r ∧
      B₀ ≡ b [ZMOD a / (Int.gcd (Int.gcd a a') (b + b') : ℤ)] ∧
      B₀ ≡ b' [ZMOD a' / (Int.gcd (Int.gcd a a') (b + b') : ℤ)] ∧
      SLEquiv (gaussForm A B_F C) (gaussForm A₀ B₀ C₀) ∧
      ∃ x y : ℤ, (gaussForm A B_F C).eval x y = a * a' ∧ Int.gcd x y = Int.gcd (Int.gcd a a') (b + b')

end QuadFormsKB.Historical.Gauss
