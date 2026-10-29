/-
# Cassels, Chapter 14, §2: composition of binary forms is well defined on classes

**Setting.** Integral binary forms $[a,b,c] = ax^2 + bxy + cy^2$ (`BinQF.mk a b c`; Cassels' notation (2.1)–(2.2),
the middle coefficient $b$ is not required to be even), discriminant $D = b^2 - 4ac$ (`BinQF.disc`), proper
equivalence $\sim$ (`Binary.SLEquiv`, $\mathrm{SL}_2(\mathbb Z)$), primitivity `Binary.Primitive`. Two primitive forms
$[a_1, b, c_1]$, $[a_2, b, c_2]$ of discriminant $D$ are *concordant* (p. 335) if $a_1a_2 \ne 0$ and
$[a_1a_2, b, c]$ is integral of discriminant $D$ for some $c$, i.e. $D = b^2 - 4a_1a_2c$; that form is their
*composition*. Here concordance is written out as these equations.

**Proves** (Cassels, *Rational Quadratic Forms*, Ch. 14):
* Lemma 2.2 (p. 334, `sLEquiv_mk_mul_left`): if $[a_1, b, lc_1] \sim [a_2, b, lc_2]$ and $\gcd(a_1, a_2, l) = 1$,
  then $[a_1l, b, c_1] \sim [a_2l, b, c_2]$. Cassels writes the third coefficients as $c_j$ with $l \mid c_j$ and the
  new ones as $c_j/l$; here $l \ne 0$ is explicit and primitivity is not needed.
* Lemma 2.3 (p. 335, `exists_concordant`): two classes of primitive forms of the same discriminant contain
  concordant forms $[a_1, b, *]$, $[a_2, b, *]$ with $a_1$, $a_2$ prime to each other and to a given $M \ne 0$.
* Lemma 2.4 (p. 336, `sLEquiv_compose`): the class of the composition of concordant forms depends only on the
  classes of the factors.

**Proof notes.** As in the book. Lemma 2.2: from the matrix identity one gets $a_1q = -lc_2r$ and $a_2q = -lc_1r$ for
the transformation $\begin{pmatrix}p&q\\r&s\end{pmatrix}$, hence $l \mid q$ and
$\begin{pmatrix}p&q/l\\rl&s\end{pmatrix}$ does the job. Lemma 2.3 uses Lemma 2.1 (`Binary.exists_coprime_value`)
and a translation $x \mapsto x + ty$ to equalize the middle coefficients. Lemma 2.4 (`sLEquiv_compose_core`): for
concordant pairs with coprime $a_1a_2$, $A_1A_2$, a common middle coefficient $\beta$ (Chinese remainder theorem) and
Lemma 2.2 twice (with $l = a_2$ and $l = A_1$) give $[a_1a_2, \beta, *] \sim [A_1a_2, \beta, *] \sim [A_1A_2, \beta, *]$;
the general case goes through a third pair from Lemma 2.3.
-/
import QuadFormsKB.Binary.ClassBijection
import QuadFormsKB.Binary.GenusCharacters

namespace QuadFormsKB.Cassels

open QuadFormsKB.Binary BinQF

/-- **Cassels, Ch. 14, Lemma 2.2, p. 334.** If $[a_1, b, lc_1] \sim [a_2, b, lc_2]$ (proper equivalence, the same
middle coefficient), $l \ne 0$ and $\gcd(a_1, a_2, l) = 1$, then $[a_1l, b, c_1] \sim [a_2l, b, c_2]$. -/
@[kb "cassels1978" "Ch. 14, Lemma 2.2, p. 334 (generalization: primitivity not needed; l ≠ 0 explicit)"]
theorem sLEquiv_mk_mul_left {a₁ a₂ b c₁ c₂ l : ℤ} (hl : l ≠ 0) (hgcd : Int.gcd (Int.gcd a₁ a₂) l = 1)
    (h : SLEquiv (mk a₁ b (l * c₁)) (mk a₂ b (l * c₂))) :
    SLEquiv (mk (a₁ * l) b c₁) (mk (a₂ * l) b c₂) := by
  rw [sLEquiv_iff] at h ⊢
  obtain ⟨p, q, r, s, hdet, hsub⟩ := h
  have ha := congrArg BinQF.a hsub
  have hb := congrArg BinQF.b hsub
  have hc := congrArg BinQF.c hsub
  simp only [subst, a_mk, b_mk, c_mk] at ha hb hc
  have hE : 2 * (a₁ * p * q + b * q * r + l * c₁ * r * s) = 0 := by linear_combination hb - b * hdet
  have k1 : a₁ * q + l * c₂ * r = 0 := by
    have : 2 * (a₁ * q + l * c₂ * r) = 0 := by linear_combination s * hE - 2 * a₁ * q * hdet - 2 * r * hc
    linarith
  have k2 : a₂ * q + l * c₁ * r = 0 := by
    have : 2 * (a₂ * q + l * c₁ * r) = 0 := by linear_combination p * hE - 2 * q * ha - 2 * l * c₁ * r * hdet
    linarith
  -- `l ∣ q`
  have hlq : l ∣ q := by
    have hco : IsCoprime ((Int.gcd a₁ a₂ : ℕ) : ℤ) l := Int.isCoprime_iff_gcd_eq_one.2 hgcd
    obtain ⟨u, w, huw⟩ := hco
    rw [Int.gcd_eq_gcd_ab] at huw
    have e : q = u * Int.gcdA a₁ a₂ * (a₁ * q) + u * Int.gcdB a₁ a₂ * (a₂ * q) + w * l * q := by
      linear_combination (-q) * huw
    rw [e]
    refine dvd_add (dvd_add ?_ ?_) (dvd_mul_of_dvd_left (dvd_mul_left l w) q)
    · exact dvd_mul_of_dvd_right ⟨-(c₂ * r), by linear_combination k1⟩ _
    · exact dvd_mul_of_dvd_right ⟨-(c₁ * r), by linear_combination k2⟩ _
  obtain ⟨q', rfl⟩ := hlq
  refine ⟨p, q', r * l, s, by linear_combination hdet, ?_⟩
  refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk]
  · linear_combination l * ha
  · linear_combination hb
  · apply mul_left_cancel₀ hl
    linear_combination hc

/-- A form is `mk` of its coefficients. -/
theorem eq_mk_abc (f : BinQF) : f = mk f.a f.b f.c := ext_abc (by simp) (by simp) (by simp)

/-- `f` is properly equivalent to its translate `x ↦ x + l y`. -/
theorem sLEquiv_translate (f : BinQF) (l : ℤ) :
    SLEquiv f (mk f.a (f.b + 2 * f.a * l) (f.a * l ^ 2 + f.b * l + f.c)) := by
  rw [sLEquiv_iff]
  refine ⟨1, l, 0, 1, by ring, ?_⟩
  simp only [subst]; congr 1 <;> ring

/-- A primitive form is properly equivalent to a form whose first coefficient is a value prime to `N`. -/
theorem exists_sLEquiv_a_coprime {f : BinQF} (hf : Primitive f) {N : ℤ} (hN : N ≠ 0) :
    ∃ g : BinQF, SLEquiv f g ∧ g.disc = f.disc ∧ g.a ≠ 0 ∧ IsCoprime g.a N := by
  have hN2 : (2 * N).natAbs ≠ 0 := by simp [hN]
  obtain ⟨x, y, -, -, hxy, hp⟩ := exists_coprime_value hf hN2
  obtain ⟨r, s, hdet, ha⟩ := exists_subst_a_eq f hxy
  have hco : IsCoprime (f.eval x y) (2 * N) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd]
    exact Nat.coprime_of_dvd fun q hq hq1 hq2 => hp q hq hq2 (Int.natCast_dvd.2 hq1)
  refine ⟨subst x r y s f, (sLEquiv_iff _ _).2 ⟨x, r, y, s, hdet, rfl⟩,
    disc_subst_of_det _ _ _ _ _ (by rw [hdet]; norm_num), ?_, ?_⟩
  · rw [ha]; rintro h0; rw [h0] at hco
    have := (isCoprime_zero_left).1 hco
    exact absurd (Int.isUnit_iff.1 (isUnit_of_dvd_unit (dvd_mul_right 2 N) this)) (by omega)
  · rw [ha]; exact hco.of_mul_right_right


/-- **Cassels, Ch. 14, Lemma 2.3, p. 335.** For primitive forms $f_1$, $f_2$ of the same discriminant $D$ and
$M \ne 0$ there are $a_1, a_2, b, c_1, c_2, c$ with $f_1 \sim [a_1, b, c_1]$, $f_2 \sim [a_2, b, c_2]$,
$a_1a_2 \ne 0$, $a_1$ and $a_2$ coprime to each other and to $M$, and $D = b^2 - 4a_1a_2c$ (so the two forms are
concordant, with composition $[a_1a_2, b, c]$). -/
@[kb "cassels1978" "Ch. 14, Lemma 2.3, p. 335"]
theorem exists_concordant {f₁ f₂ : BinQF} (h₁ : Primitive f₁) (h₂ : Primitive f₂) (hD : f₁.disc = f₂.disc)
    {M : ℤ} (hM : M ≠ 0) :
    ∃ a₁ a₂ b c₁ c₂ c : ℤ, SLEquiv f₁ (mk a₁ b c₁) ∧ SLEquiv f₂ (mk a₂ b c₂) ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      IsCoprime a₁ a₂ ∧ IsCoprime a₁ M ∧ IsCoprime a₂ M ∧ f₁.disc = b ^ 2 - 4 * a₁ * a₂ * c := by
  obtain ⟨g₁, e₁, d₁, n₁, k₁⟩ := exists_sLEquiv_a_coprime h₁ hM
  obtain ⟨g₂, e₂, d₂, n₂, k₂⟩ := exists_sLEquiv_a_coprime h₂ (mul_ne_zero n₁ hM)
  have hcop : IsCoprime g₁.a g₂.a := k₂.of_mul_right_left.symm
  have hdd : g₁.b ^ 2 - 4 * g₁.a * g₁.c = g₂.b ^ 2 - 4 * g₂.a * g₂.c := by
    have := d₁.trans (hD.trans d₂.symm); simpa [disc] using this
  have hpar : Even (g₂.b - g₁.b) := by
    have hev : Even ((g₂.b - g₁.b) * (g₂.b + g₁.b)) :=
      ⟨2 * (g₂.a * g₂.c - g₁.a * g₁.c), by linear_combination -hdd⟩
    rcases Int.even_mul.1 hev with h | h
    · exact h
    · rw [Int.even_sub]; rw [Int.even_add] at h; exact h
  obtain ⟨t, ht⟩ := hpar
  obtain ⟨u, v, huv⟩ := hcop
  set b := g₁.b + 2 * g₁.a * (t * u) with hbdef
  have hb2 : g₂.b + 2 * g₂.a * (-(t * v)) = b := by linear_combination ht - 2 * t * huv
  have E₁ := e₁.trans (sLEquiv_translate g₁ (t * u))
  have E₂ := e₂.trans (sLEquiv_translate g₂ (-(t * v)))
  rw [hb2] at E₂
  set C₁ := g₁.a * (t * u) ^ 2 + g₁.b * (t * u) + g₁.c
  set C₂ := g₂.a * (-(t * v)) ^ 2 + g₂.b * (-(t * v)) + g₂.c
  have hD₁ : f₁.disc = b ^ 2 - 4 * g₁.a * C₁ := by
    rw [← d₁, disc]; simp only [hbdef, C₁]; ring
  have hD₂ : f₁.disc = b ^ 2 - 4 * g₂.a * C₂ := by
    rw [hD, ← d₂, disc, ← hb2]; simp only [C₂]; ring
  have h4 : 4 * (g₂.a * C₂) = 4 * (g₁.a * C₁) := by linear_combination hD₂ - hD₁
  have hdiv : g₁.a ∣ g₂.a * C₂ := ⟨C₁, mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4⟩
  obtain ⟨c, hc⟩ := (IsCoprime.dvd_of_dvd_mul_left ⟨u, v, huv⟩ hdiv)
  refine ⟨g₁.a, g₂.a, b, C₁, C₂, c, E₁, E₂, n₁, n₂, ⟨u, v, huv⟩, k₁, k₂.of_mul_right_right, ?_⟩
  rw [hD₂, hc]; ring


/-- Translation `x ↦ x + t y` with the new middle coefficient named. -/
theorem sLEquiv_translate' {a b c β : ℤ} (t : ℤ) (h : β = b + 2 * a * t) :
    SLEquiv (mk a b c) (mk a β (a * t ^ 2 + b * t + c)) := by
  rw [sLEquiv_iff]
  refine ⟨1, t, 0, 1, by ring, ?_⟩
  simp only [subst, a_mk, b_mk, c_mk, h]; congr 1 <;> ring

/-- **Cassels, Ch. 14, proof of Lemma 2.4, (2.15), pp. 336–337.** Two concordant pairs
$[a_1,b,c_1], [a_2,b,c_2]$ (composition $[a_1a_2, b, c]$) and $[A_1,B,C_1], [A_2,B,C_2]$ (composition
$[A_1A_2, B, C]$) of discriminant $D$ with $[a_j,b,c_j] \sim [A_j,B,C_j]$ and $a_1a_2$ prime to $A_1A_2$ have
properly equivalent compositions. -/
@[kb "cassels1978" "Ch. 14, proof of Lemma 2.4, (2.15)–(2.22), pp. 336–337"]
theorem sLEquiv_compose_core {D a₁ a₂ b c₁ c₂ c A₁ A₂ B C₁ C₂ C : ℤ}
    (h₁ : D = b ^ 2 - 4 * a₁ * c₁) (h₂ : D = b ^ 2 - 4 * a₂ * c₂) (h : D = b ^ 2 - 4 * (a₁ * a₂) * c)
    (H₁ : D = B ^ 2 - 4 * A₁ * C₁) (H₂ : D = B ^ 2 - 4 * A₂ * C₂) (H : D = B ^ 2 - 4 * (A₁ * A₂) * C)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hA₁ : A₁ ≠ 0) (hA₂ : A₂ ≠ 0)
    (hco : IsCoprime (a₁ * a₂) (A₁ * A₂))
    (e₁ : SLEquiv (mk a₁ b c₁) (mk A₁ B C₁)) (e₂ : SLEquiv (mk a₂ b c₂) (mk A₂ B C₂)) :
    SLEquiv (mk (a₁ * a₂) b c) (mk (A₁ * A₂) B C) := by
  -- parity of the middle coefficients
  have hpar : Even (B - b) := by
    have hev : Even ((B - b) * (B + b)) := ⟨2 * (A₁ * C₁ - a₁ * c₁), by linear_combination h₁ - H₁⟩
    rcases Int.even_mul.1 hev with h' | h'
    · exact h'
    · rw [Int.even_sub]; rw [Int.even_add] at h'; exact h'
  have cop1 : IsCoprime a₂ A₁ := hco.of_mul_left_right.of_mul_right_left
  obtain ⟨t, ht⟩ := hpar
  obtain ⟨u, v, huv⟩ := hco
  set β := b + 2 * (a₁ * a₂) * (u * t) with hβ
  have hβ' : β = B + 2 * (A₁ * A₂) * (-(v * t)) := by linear_combination -ht + 2 * t * huv
  -- translate everything to middle coefficient `β`
  have E := sLEquiv_translate' (c := c) (u * t) hβ
  have F := sLEquiv_translate' (c := C) (-(v * t)) hβ'
  have E₁ := sLEquiv_translate' (c := c₁) (a₂ * (u * t)) (show β = b + 2 * a₁ * (a₂ * (u * t)) by rw [hβ]; ring)
  have E₂ := sLEquiv_translate' (c := c₂) (a₁ * (u * t)) (show β = b + 2 * a₂ * (a₁ * (u * t)) by rw [hβ]; ring)
  have F₁ := sLEquiv_translate' (c := C₁) (A₂ * (-(v * t))) (show β = B + 2 * A₁ * (A₂ * (-(v * t))) by
    rw [hβ']; ring)
  have F₂ := sLEquiv_translate' (c := C₂) (A₁ * (-(v * t))) (show β = B + 2 * A₂ * (A₁ * (-(v * t))) by
    rw [hβ']; ring)
  set γ := a₁ * a₂ * (u * t) ^ 2 + b * (u * t) + c
  set Γ := A₁ * A₂ * (-(v * t)) ^ 2 + B * (-(v * t)) + C
  set γ₁ := a₁ * (a₂ * (u * t)) ^ 2 + b * (a₂ * (u * t)) + c₁
  set γ₂ := a₂ * (a₁ * (u * t)) ^ 2 + b * (a₁ * (u * t)) + c₂
  set Γ₁ := A₁ * (A₂ * (-(v * t))) ^ 2 + B * (A₂ * (-(v * t))) + C₁
  set Γ₂ := A₂ * (A₁ * (-(v * t))) ^ 2 + B * (A₁ * (-(v * t))) + C₂
  have dγ : D = β ^ 2 - 4 * (a₁ * a₂) * γ := by rw [h, hβ]; ring
  have dΓ : D = β ^ 2 - 4 * (A₁ * A₂) * Γ := by rw [H, hβ']; ring
  have dγ₁ : D = β ^ 2 - 4 * a₁ * γ₁ := by rw [h₁, hβ]; ring
  have dγ₂ : D = β ^ 2 - 4 * a₂ * γ₂ := by rw [h₂, hβ]; ring
  have dΓ₁ : D = β ^ 2 - 4 * A₁ * Γ₁ := by rw [H₁, hβ']; ring
  have dΓ₂ : D = β ^ 2 - 4 * A₂ * Γ₂ := by rw [H₂, hβ']; ring
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  have hγ₁ : γ₁ = a₂ * γ := mul_left_cancel₀ (mul_ne_zero h4 ha₁) (by linear_combination dγ₁ - dγ)
  have hΓ₂ : Γ₂ = A₁ * Γ := mul_left_cancel₀ (mul_ne_zero h4 hA₂) (by linear_combination dΓ₂ - dΓ)
  obtain ⟨y₁, hy₁⟩ : a₂ ∣ Γ₁ := cop1.dvd_of_dvd_mul_left
    ⟨a₁ * γ, mul_left_cancel₀ h4 (by linear_combination dΓ₁ - dγ)⟩
  obtain ⟨x₂, hx₂⟩ : A₁ ∣ γ₂ := cop1.symm.dvd_of_dvd_mul_left
    ⟨A₂ * Γ, mul_left_cancel₀ h4 (by linear_combination dγ₂ - dΓ)⟩
  have hxy : y₁ = x₂ := by
    have hne : (4 : ℤ) * (a₂ * A₁) ≠ 0 := mul_ne_zero h4 (mul_ne_zero ha₂ hA₁)
    refine mul_left_cancel₀ hne ?_
    rw [hy₁] at dΓ₁; rw [hx₂] at dγ₂
    linear_combination dΓ₁ - dγ₂
  -- Lemma 2.2 twice
  have g1 : Int.gcd (Int.gcd a₁ A₁) a₂ = 1 :=
    Int.isCoprime_iff_gcd_eq_one.1 (cop1.symm.of_isCoprime_of_dvd_left (Int.gcd_dvd_right _ _))
  have g2 : Int.gcd (Int.gcd a₂ A₂) A₁ = 1 :=
    Int.isCoprime_iff_gcd_eq_one.1 (cop1.of_isCoprime_of_dvd_left (Int.gcd_dvd_left _ _))
  have L1 : SLEquiv (mk a₁ β (a₂ * γ)) (mk A₁ β (a₂ * y₁)) := by
    rw [← hγ₁, ← hy₁]; exact (E₁.symm.trans e₁).trans F₁
  have L2 : SLEquiv (mk a₂ β (A₁ * x₂)) (mk A₂ β (A₁ * Γ)) := by
    rw [← hx₂, ← hΓ₂]; exact (E₂.symm.trans e₂).trans F₂
  have M1 := sLEquiv_mk_mul_left ha₂ g1 L1
  have M2 := sLEquiv_mk_mul_left hA₁ g2 L2
  rw [mul_comm a₂ A₁, mul_comm A₂ A₁, ← hxy] at M2
  exact ((E.trans M1).trans M2).trans F.symm


/-- The discriminant is a class invariant. -/
theorem disc_eq_of_sLEquiv {f g : BinQF} (h : SLEquiv f g) : g.disc = f.disc := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := (sLEquiv_iff f g).1 h
  exact disc_subst_of_det _ _ _ _ _ (by rw [hdet]; norm_num)

/-- $\\operatorname{disc}[a,b,c] = b^2 - 4ac$. -/
theorem disc_mk (a b c : ℤ) : (mk a b c).disc = b ^ 2 - 4 * a * c := by simp [disc]

/-- **Cassels, Ch. 14, Lemma 2.4, p. 336 (composition is well defined on classes).** Let
$[a_1,b,c_1], [a_2,b,c_2]$ be concordant primitive forms of discriminant $D$ with composition $[a_1a_2, b, c]$, and
$[a_1',b',c_1'], [a_2',b',c_2']$ concordant forms of discriminant $D$ with composition $[a_1'a_2', b', c']$. If
$[a_j,b,c_j] \sim [a_j',b',c_j']$ for $j = 1, 2$, then $[a_1a_2, b, c] \sim [a_1'a_2', b', c']$. -/
@[kb "cassels1978" "Ch. 14, Lemma 2.4, p. 336"]
theorem sLEquiv_compose {D a₁ a₂ b c₁ c₂ c a₁' a₂' b' c₁' c₂' c' : ℤ}
    (h₁ : D = b ^ 2 - 4 * a₁ * c₁) (h₂ : D = b ^ 2 - 4 * a₂ * c₂) (h : D = b ^ 2 - 4 * (a₁ * a₂) * c)
    (h₁' : D = b' ^ 2 - 4 * a₁' * c₁') (h₂' : D = b' ^ 2 - 4 * a₂' * c₂')
    (h' : D = b' ^ 2 - 4 * (a₁' * a₂') * c')
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₁' : a₁' ≠ 0) (ha₂' : a₂' ≠ 0)
    (p₁ : Primitive (mk a₁ b c₁)) (p₂ : Primitive (mk a₂ b c₂))
    (e₁ : SLEquiv (mk a₁ b c₁) (mk a₁' b' c₁')) (e₂ : SLEquiv (mk a₂ b c₂) (mk a₂' b' c₂')) :
    SLEquiv (mk (a₁ * a₂) b c) (mk (a₁' * a₂') b' c') := by
  have hM : a₁ * a₂ * (a₁' * a₂') ≠ 0 := mul_ne_zero (mul_ne_zero ha₁ ha₂) (mul_ne_zero ha₁' ha₂')
  obtain ⟨A₁, A₂, B, C₁, C₂, C, E₁, E₂, n₁, n₂, -, k₁, k₂, hD⟩ :=
    exists_concordant p₁ p₂ (by rw [disc_mk, disc_mk, ← h₁, ← h₂]) hM
  have H₁ : D = B ^ 2 - 4 * A₁ * C₁ := by rw [← disc_mk, disc_eq_of_sLEquiv E₁, disc_mk, h₁]
  have H₂ : D = B ^ 2 - 4 * A₂ * C₂ := by rw [← disc_mk, disc_eq_of_sLEquiv E₂, disc_mk, h₂]
  have H : D = B ^ 2 - 4 * (A₁ * A₂) * C := by rw [h₁, ← disc_mk, hD]; ring
  have k : IsCoprime (A₁ * A₂) (a₁ * a₂ * (a₁' * a₂')) := k₁.mul_left k₂
  have c1 := sLEquiv_compose_core h₁ h₂ h H₁ H₂ H ha₁ ha₂ n₁ n₂ k.of_mul_right_left.symm E₁ E₂
  have c2 := sLEquiv_compose_core h₁' h₂' h' H₁ H₂ H ha₁' ha₂' n₁ n₂ k.of_mul_right_right.symm
    (e₁.symm.trans E₁) (e₂.symm.trans E₂)
  exact c1.trans c2.symm

end QuadFormsKB.Cassels
