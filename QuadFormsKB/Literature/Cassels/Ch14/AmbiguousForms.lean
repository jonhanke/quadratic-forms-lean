/-
# Cassels, Chapter 14, §4: ambiguous forms and their number (Lemma 4.2)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §1, p. 332, and §4, pp. 341–342.

The *ambiguous forms* of the first and second kind are $[a, 0, c]$ and $[a, a, c]$ ((4.6)–(4.7), `IsAmbiguousForm`).
Lemma 4.2 counts the primitive ones of a given discriminant $D \ne 0$ (`card_firstKind`, `card_secondKind`,
`card_ambiguousForms`).

*Reconstruction.* The table of Lemma 4.2 is garbled in the machine-read text; the counts here are computed from the
definitions (a form $[a, 0, c]$ is primitive iff $\gcd(a, c) = 1$, and $D = -4ac$; a form $[a, a, c]$ is primitive iff
$\gcd(a, c) = 1$, and $D = a(a - 4c)$), split by the $2$-adic shape of $D$ into six cases. With $\lambda$ the number
of distinct odd primes dividing $D$:

| $D$ | first kind | second kind |
|---|---|---|
| odd | $0$ | $2^{\lambda+1}$ |
| $4d$, $d \equiv 1 \pmod 4$ | $2^{\lambda+1}$ | $0$ |
| $4d$, $d \equiv 3 \pmod 4$ | $2^{\lambda+1}$ | $2^{\lambda+1}$ |
| $4d$, $d \equiv 2 \pmod 4$ | $2^{\lambda+2}$ | $0$ |
| $4d$, $d \equiv 4 \pmod 8$ | $2^{\lambda+2}$ | $0$ |
| $4d$, $d \equiv 0 \pmod 8$ | $2^{\lambda+2}$ | $2^{\lambda+2}$ |
-/
import QuadFormsKB.Binary.FormsIdeals
import QuadFormsKB.Binary.GenusDuplication
import QuadFormsKB.Literature.Cassels.Ch14.Composition

namespace QuadFormsKB.Composition

open BinQF

variable {D : ℤ}

/-! ### General helpers: counting coprime factorizations -/

private lemma card_unitary (m : ℕ) (hm : m ≠ 0) :
    (m.divisors.filter (fun a => Nat.Coprime a (m / a))).card = 2 ^ m.primeFactors.card := by
  classical
  set g : Finset ℕ → ℕ := fun T => ∏ p ∈ T, p ^ m.factorization p with hg
  have hprod : g m.primeFactors = m := by
    exact (Nat.prod_primeFactors_pow_factorization hm).symm
  have hpos : ∀ T, T ⊆ m.primeFactors → 0 < g T := fun T hT => Finset.prod_pos (fun p hp => by
    have := Nat.prime_of_mem_primeFactors (hT hp)
    exact pow_pos this.pos _)
  have hsplit : ∀ T ⊆ m.primeFactors, g (m.primeFactors \ T) * g T = m := by
    intro T hT
    simp only [hg]
    rw [Finset.prod_sdiff hT]
    exact hprod
  have hmem : ∀ T ⊆ m.primeFactors, g T ∈ m.divisors.filter (fun a => Nat.Coprime a (m / a)) := by
    intro T hT
    have h := hsplit T hT
    rw [Finset.mem_filter, Nat.mem_divisors]
    have hq : m / g T = g (m.primeFactors \ T) := by
      exact Nat.div_eq_of_eq_mul_left (hpos T hT) h.symm
    refine ⟨⟨⟨_, h.symm.trans (mul_comm _ _)⟩, hm⟩, ?_⟩
    rw [hq]
    apply Nat.Coprime.symm
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq'
    have hp' := Nat.prime_of_mem_primeFactors (hT hq')
    have hq'' := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1
    have hne : q ≠ p := fun e => (Finset.mem_sdiff.1 hp).2 (e ▸ hq')
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hq'' hp').2 (Ne.symm hne))
  have key : ∀ T T', T ⊆ m.primeFactors → T' ⊆ m.primeFactors → g T = g T' → T ⊆ T' := by
    intro T T' hT hT' h q hq
    have hqp := Nat.prime_of_mem_primeFactors (hT hq)
    have hqm : 0 < m.factorization q :=
      hqp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors (hT hq))
    have h1 : q ∣ g T :=
      (dvd_pow_self q hqm.ne').trans (Finset.dvd_prod_of_mem (fun p => p ^ m.factorization p) hq)
    rw [h] at h1
    obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).1 h1
    have := (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors (hT' hp))).1
      (hqp.dvd_of_dvd_pow hqp')
    exact this ▸ hp
  have hinj : Set.InjOn g (m.primeFactors.powerset : Set (Finset ℕ)) := by
    intro T hT T' hT' h
    have hT := Finset.mem_powerset.1 hT
    have hT' := Finset.mem_powerset.1 hT'
    exact Finset.Subset.antisymm (key T T' hT hT' h) (key T' T hT' hT h.symm)
  have himg : m.divisors.filter (fun a => Nat.Coprime a (m / a)) = m.primeFactors.powerset.image g := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_filter, Nat.mem_divisors] at ha
      obtain ⟨⟨hadvd, -⟩, hcop⟩ := ha
      have ha0 : a ≠ 0 := fun h0 => hm (by rw [h0] at hadvd; exact zero_dvd_iff.1 hadvd)
      have hq0 : m / a ≠ 0 := fun h0 => hm (by
        have := Nat.div_mul_cancel hadvd; rw [h0] at this; omega)
      refine Finset.mem_image.2 ⟨a.primeFactors, Finset.mem_powerset.2 (Nat.primeFactors_mono hadvd hm), ?_⟩
      simp only [hg]
      conv_rhs => rw [Nat.prod_primeFactors_pow_factorization ha0]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have hpa := Nat.dvd_of_mem_primeFactors hp
      have hnd : ¬ p ∣ m / a := fun hd =>
        (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpa hd)
      have h0 : (m / a).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
      have hmul : m.factorization p = a.factorization p + (m / a).factorization p := by
        conv_lhs => rw [← Nat.mul_div_cancel' hadvd]
        rw [Nat.factorization_mul ha0 hq0]; rfl
      rw [hmul, h0, add_zero]
    · intro ha
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 ha
      exact hmem T (Finset.mem_powerset.1 hT)
  rw [himg, Finset.card_image_of_injOn hinj, Finset.card_powerset]

private lemma isCoprime_iff_natAbs (a c : ℤ) : IsCoprime a c ↔ Nat.Coprime a.natAbs c.natAbs := by
  rw [Int.isCoprime_iff_gcd_eq_one]; rfl

private lemma ncard_coprime_mul (n : ℤ) (hn : n ≠ 0) :
    {p : ℤ × ℤ | p.1 * p.2 = n ∧ IsCoprime p.1 p.2}.ncard = 2 * 2 ^ n.natAbs.primeFactors.card := by
  classical
  have hm : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  rw [← card_unitary _ hm]
  have hc : 2 * (n.natAbs.divisors.filter (fun a => Nat.Coprime a (n.natAbs / a))).card =
      ((n.natAbs.divisors.filter (fun a => Nat.Coprime a (n.natAbs / a))) ×ˢ
        (Finset.univ : Finset Bool)).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
  rw [hc, ← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun p _ => (p.1.natAbs, decide (0 < p.1))) ?_ ?_ ?_
  · rintro ⟨a, c⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hn' : a.natAbs * c.natAbs = n.natAbs := by rw [← Int.natAbs_mul, h1]
    have hdiv : n.natAbs / a.natAbs = c.natAbs := Nat.div_eq_of_eq_mul_right
      (Nat.pos_of_ne_zero (by rintro h; rw [h] at hn'; simp at hn'; exact hm hn'.symm)) hn'.symm
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨⟨_, hn'.symm⟩, hm⟩, ?_⟩, Finset.mem_univ _⟩)
    show Nat.Coprime a.natAbs (n.natAbs / a.natAbs)
    rw [hdiv]; exact (isCoprime_iff_natAbs _ _).1 h2
  · rintro ⟨a, c⟩ ⟨a', c'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ h
    simp only [Prod.mk.injEq, decide_eq_decide] at h h1 h1'
    have ha : a ≠ 0 := fun h0 => hn (by rw [← h1, h0]; simp)
    have ha' : a' ≠ 0 := fun h0 => hn (by rw [← h1', h0]; simp)
    have : a = a' := by omega
    subst this
    have : c = c' := mul_left_cancel₀ ha (h1.trans h1'.symm)
    rw [this]
  · rintro ⟨u, s⟩ hus
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors,
      Finset.mem_univ, and_true] at hus
    obtain ⟨⟨hud, -⟩, hcop⟩ := hus
    have hu0 : u ≠ 0 := fun h0 => hm (by rw [h0] at hud; exact zero_dvd_iff.1 hud)
    have hdvd : (u : ℤ) ∣ n := Int.natCast_dvd.2 hud
    obtain ⟨a, ha1, ha2, ha3⟩ : ∃ a : ℤ, a.natAbs = u ∧ (0 < a ↔ s = true) ∧ a ∣ n := by
      cases s
      · exact ⟨-u, by simp, by simp, (neg_dvd).2 hdvd⟩
      · exact ⟨u, by simp, by simp; omega, hdvd⟩
    obtain ⟨c, hc⟩ := ha3
    have hn' : a.natAbs * c.natAbs = n.natAbs := by rw [← Int.natAbs_mul, hc]
    rw [ha1] at hn'
    have hdiv : n.natAbs / u = c.natAbs := Nat.div_eq_of_eq_mul_right (Nat.pos_of_ne_zero hu0) hn'.symm
    refine ⟨(a, c), ⟨hc.symm, ?_⟩, ?_⟩
    · rw [isCoprime_iff_natAbs, ha1, ← hdiv]; exact hcop
    · simp only [ha1, Prod.mk.injEq, true_and]
      cases s <;> simpa using ha2


/-- **Ambiguous forms** (Cassels, Ch. 14, (1.14)–(1.15), p. 332, and (4.6)–(4.7), p. 341): $[a, 0, c]$ (first kind)
or $[a, a, c]$ (second kind). -/
@[kb "cassels1978" "Ch. 14, §4, (4.6)–(4.7), p. 341 (ambiguous forms of the first and second kind)"]
def IsAmbiguousForm (f : BinQF) : Prop := f.b = 0 ∨ f.b = f.a

/-- **$a \mid D$ for ambiguous forms** (Cassels, Ch. 14, p. 341: "We note that $a \mid D$ in both (4.6) and (4.7)"). -/
@[kb "cassels1978" "Ch. 14, §4, p. 341 (a ∣ D for ambiguous forms)"]
theorem a_dvd_disc_of_isAmbiguousForm {f : BinQF} (h : IsAmbiguousForm f) : f.a ∣ f.disc := by
  rcases h with h | h
  · exact ⟨-4 * f.c, by simp only [BinQF.disc, h]; ring⟩
  · exact ⟨f.a - 4 * f.c, by simp only [BinQF.disc, h]; ring⟩

/-! ### The argument of Lemma 4.1 -/

section Lemma41

open Binary

/-- **An improper automorph of a form of nonzero discriminant has trace zero** ($S = -P$ for
$\gamma = \begin{pmatrix} P & Q\\ R & S\end{pmatrix}$, $\det\gamma = -1$, $f \circ \gamma = f$, $\operatorname{disc} f \ne 0$).
If $a \ne 0$ this is `improper_trace_zero`; if $c \ne 0$ the symmetric identity
$2c(P + S) = -2P(C - c) + Q(B - b) + (2cS + bQ)(PS - QR + 1)$ applies; if $a = c = 0$ then $b \ne 0$ and the
equations force $P = S = 0$. -/
theorem trace_zero_of_disc_ne {f : BinQF} (hD : f.disc ≠ 0) {P Q R S : ℤ}
    (hdet : P * S - Q * R = -1) (h : BinQF.subst P Q R S f = f) : S = -P := by
  by_cases ha : f.a = 0
  · by_cases hc : f.c = 0
    · have hb : f.b ≠ 0 := fun hb => hD (by simp [BinQF.disc, ha, hb, hc])
      have e1 := congrArg BinQF.a h
      have e2 := congrArg BinQF.b h
      have e3 := congrArg BinQF.c h
      simp only [a_subst, b_subst, c_subst, ha, hc] at e1 e2 e3
      have hps : P * S + Q * R = 1 :=
        mul_left_cancel₀ hb (by linear_combination e2)
      have hPR : P * R = 0 :=
        (mul_eq_zero.mp (show f.b * (P * R) = 0 by linear_combination e1)).resolve_left hb
      have hQS : Q * S = 0 :=
        (mul_eq_zero.mp (show f.b * (Q * S) = 0 by linear_combination e3)).resolve_left hb
      have hPS : P * S = 0 := by linarith
      have hQR : Q * R = 1 := by linarith
      have hQ : Q ≠ 0 := fun hq => by rw [hq] at hQR; simp at hQR
      have hR : R ≠ 0 := fun hr => by rw [hr] at hQR; simp at hQR
      have hP : P = 0 := (mul_eq_zero.mp hPR).resolve_right hR
      have hS : S = 0 := (mul_eq_zero.mp hQS).resolve_left hQ
      rw [hP, hS]; simp
    · have e2 := congrArg BinQF.b h
      have e3 := congrArg BinQF.c h
      simp only [b_subst, c_subst] at e2 e3
      have h2 : 2 * f.c * (P + S) = 0 := by
        linear_combination (-2 * P) * e3 + Q * e2 + (2 * f.c * S + f.b * Q) * hdet
      have : P + S = 0 := (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero hc)
      linarith
  · exact improper_trace_zero ha hdet h

/-- **Core of Lemma 4.1** (Cassels, Ch. 14, (4.2)–(4.5), p. 341): if $f$ is fixed by the improper trace-zero matrix
$\begin{pmatrix} s & q\\ -r & -s\end{pmatrix}$ (so $s^2 - qr = 1$), then $f$ is properly equivalent to a form $g$ with
$g_a \mid g_b$. (The proof of `exists_sLEquiv_a_dvd_b` without positivity.) -/
theorem exists_sLEquiv_a_dvd_b_of_automorph {f : BinQF} {s q r : ℤ} (hd : s * s - q * r = 1)
    (haut : BinQF.subst s q (-r) (-s) f = f) :
    ∃ g : BinQF, SLEquiv f g ∧ g.a ∣ g.b := by
  have hinv : ∀ X Y : ℤ, f.eval (s * X + q * Y) (-r * X + -s * Y) = f.eval X Y := fun X Y => by
    rw [← eval_subst, haut]
  obtain ⟨x, y, hxy, hfx, hfy⟩ : ∃ x y : ℤ, IsCoprime x y ∧ s * x + q * y = x ∧ -r * x + -s * y = y := by
    by_cases h0 : q = 0 ∧ 1 - s = 0
    · refine exists_coprime_fixed (u₀ := 1 + s) (u₁ := -r) (Or.inl (by omega)) ?_ (by ring)
      linear_combination hd
    · exact exists_coprime_fixed (u₀ := q) (u₁ := 1 - s) (by tauto) (by ring) (by linear_combination hd)
  obtain ⟨r', s', hdet', -⟩ := exists_subst_a_eq f hxy
  set w₀ := s * r' + q * s' + r' with hw₀d
  set w₁ := -r * r' + -s * s' + s' with hw₁d
  have hβ : x * w₁ - y * w₀ = 0 := by
    rw [hw₀d, hw₁d]; linear_combination (-s') * hfx + r' * hfy
  set k := w₀ * s' - w₁ * r' with hkd
  have hw₀ : w₀ = k * x := by
    rw [hkd, hw₀d, hw₁d]
    linear_combination (-r' * s') * hfx + r' ^ 2 * hfy + (-q * s' - r' * s - r') * hdet'
  have hw₁ : w₁ = k * y := by
    rw [hkd, hw₀d, hw₁d]
    linear_combination (-s' ^ 2) * hfx + (r' * s') * hfy + (r * r' + s * s' - s') * hdet'
  have e1 := hinv (x + r') (y + s')
  have e2 := hinv r' s'
  rw [show s * (x + r') + q * (y + s') = (1 + k) * x - r' by linear_combination hfx + hw₀d.symm + hw₀,
    show -r * (x + r') + -s * (y + s') = (1 + k) * y - s' by linear_combination hfy + hw₁d.symm + hw₁] at e1
  rw [show s * r' + q * s' = k * x - r' by linear_combination hw₀d.symm + hw₀,
    show -r * r' + -s * s' = k * y - s' by linear_combination hw₁d.symm + hw₁] at e2
  simp only [eval_eq] at e1 e2
  refine ⟨BinQF.subst x r' y s' f, (sLEquiv_iff _ _).mpr ⟨x, r', y, s', hdet', rfl⟩, ?_⟩
  refine ⟨k, ?_⟩
  have h2 : 2 * ((BinQF.subst x r' y s' f).b - (BinQF.subst x r' y s' f).a * k) = 0 := by
    rw [a_subst, b_subst]
    linear_combination e2 - e1
  have := (mul_eq_zero.mp h2).resolve_left two_ne_zero
  linarith

/-- **The argument of Lemma 4.1** (Cassels, Ch. 14, (4.2)–(4.7), p. 341): a form of discriminant $D \ne 0$ with an
improper automorph $S$ is properly equivalent to an ambiguous form. ($S^2 = I$ (4.2); a primitive $\mathbf b$ with
$S\mathbf b = -\mathbf b$ (4.3) extends to a basis $\mathbf a, \mathbf b$ of $\mathbb Z^2$ of determinant $1$ with
$S\mathbf a = \mathbf a + w\mathbf b$ (4.4), $w \in \{0, 1\}$ after $\mathbf a \mapsto \mathbf a + u\mathbf b$ (4.5); in the
basis $\mathbf a, \mathbf b$ the form is $[a, 0, c]$ if $w = 0$, and $[a', -c', c'] \sim [c', c', a']$ if $w = 1$.) -/
theorem exists_sLEquiv_ambiguousForm {f : BinQF} (hD : f.disc ≠ 0)
    (h : ∃ p q r s : ℤ, p * s - q * r = -1 ∧ BinQF.subst p q r s f = f) :
    ∃ g : BinQF, SLEquiv f g ∧ IsAmbiguousForm g := by
  obtain ⟨p, q, r, s, hdet, h⟩ := h
  have hs := trace_zero_of_disc_ne hD hdet h
  subst hs
  obtain ⟨g, hg, k, hk⟩ := exists_sLEquiv_a_dvd_b_of_automorph (f := f) (s := p) (q := q) (r := -r)
    (by linear_combination (-1) * hdet) (by rw [neg_neg]; exact h)
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · obtain ⟨g', hg', ha', hb'⟩ := exists_sLEquiv_b (f := g) (B := 0) ⟨-m, by rw [hk]; ring⟩
    exact ⟨g', hg.trans hg', Or.inl hb'⟩
  · obtain ⟨g', hg', ha', hb'⟩ := exists_sLEquiv_b (f := g) (B := g.a) ⟨-m, by rw [hk]; ring⟩
    exact ⟨g', hg.trans hg', Or.inr (hb'.trans ha'.symm)⟩

end Lemma41

/-! ### Lemma 4.2: the number of ambiguous forms -/

/-- The primitive ambiguous forms $[a, 0, c]$ of the first kind of discriminant $D$. -/
def firstKind (D : ℤ) : Set BinQF := {f | f.IsPrimitive ∧ f.disc = D ∧ f.b = 0}

/-- The primitive ambiguous forms $[a, a, c]$ of the second kind of discriminant $D$. -/
def secondKind (D : ℤ) : Set BinQF := {f | f.IsPrimitive ∧ f.disc = D ∧ f.b = f.a}

/-- $\lambda$: the number of distinct odd primes dividing $D$ (Cassels, Ch. 14, Lemma 3.4, p. 340, and Lemma 4.2,
p. 342). -/
def numOddPrimes (D : ℤ) : ℕ := (D.natAbs.primeFactors.erase 2).card

/-! ### Helpers for Lemma 4.2 -/

private lemma isPrimitive_iff {f : BinQF} (hb : f.b = 0 ∨ f.b = f.a) :
    f.IsPrimitive ↔ IsCoprime f.a f.c := by
  constructor
  · intro h
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hu : IsUnit ((Int.gcd f.a f.c : ℕ) : ℤ) := by
      apply h
      · exact Int.gcd_dvd_left _ _
      · rcases hb with hb | hb
        · rw [hb]; exact dvd_zero _
        · rw [hb]; exact Int.gcd_dvd_left _ _
      · exact Int.gcd_dvd_right _ _
    rcases Int.isUnit_iff.1 hu with h1 | h1 <;> omega
  · intro hc d h1 _ h3
    exact hc.isUnit_of_dvd' h1 h3

private lemma coprime_sub_mul {a c k : ℤ} (hk : IsCoprime a k) : IsCoprime a (a - k * c) ↔ IsCoprime a c := by
  constructor
  · rintro ⟨u, v, h⟩
    exact ⟨u + v, -(k * v), by linarith⟩
  · intro hc
    obtain ⟨u, v, h⟩ := hk.mul_right hc
    exact ⟨u + v, -v, by linarith⟩

private lemma isCoprime_two_of_odd {a : ℤ} (ha : a % 2 = 1) : IsCoprime a 2 :=
  ⟨1, -(a / 2), by omega⟩

private lemma isCoprime_four_of_odd {a : ℤ} (ha : a % 2 = 1) : IsCoprime a 4 := by
  have := (isCoprime_two_of_odd ha).mul_right (isCoprime_two_of_odd ha)
  simpa using this

private lemma mul_emod_two_odd {a e : ℤ} (ha : a % 2 = 1) (he : e % 2 = 1) : (a * e) % 2 = 1 := by
  rw [Int.mul_emod, ha, he]; rfl

private lemma numOddPrimes_four_mul {d : ℤ} (hd : d ≠ 0) : numOddPrimes (4 * d) = numOddPrimes d := by
  unfold numOddPrimes
  have h1 : (4 * d).natAbs = 2 ^ 2 * d.natAbs := by simp [Int.natAbs_mul]
  rw [h1, Nat.primeFactors_mul (by norm_num) (Int.natAbs_ne_zero.2 hd),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  congr 1
  ext p
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_singleton]
  tauto

private lemma card_pf_of_odd {d : ℤ} (hd : d % 2 = 1) :
    d.natAbs.primeFactors.card = numOddPrimes d := by
  unfold numOddPrimes
  rw [Finset.erase_eq_of_notMem]
  intro h
  have := Nat.dvd_of_mem_primeFactors h
  omega

private lemma card_pf_of_even {d : ℤ} (hd0 : d ≠ 0) (hd : d % 2 = 0) :
    d.natAbs.primeFactors.card = numOddPrimes d + 1 := by
  unfold numOddPrimes
  have h2 : 2 ∈ d.natAbs.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, by omega, Int.natAbs_ne_zero.2 hd0⟩
  rw [Finset.card_erase_of_mem h2]
  have := Finset.card_pos.2 ⟨2, h2⟩
  omega

/-- Finiteness of the factorizations of a nonzero integer. -/
private lemma finite_mul_eq {n : ℤ} (hn : n ≠ 0) : {p : ℤ × ℤ | p.1 * p.2 = n}.Finite := by
  apply Set.Finite.subset ((Set.finite_Icc (-(n.natAbs : ℤ)) n.natAbs).prod
    (Set.finite_Icc (-(n.natAbs : ℤ)) n.natAbs))
  rintro ⟨a, c⟩ h
  replace h : a * c = n := h
  have ha : a ∣ n := ⟨c, h.symm⟩
  have hc : c ∣ n := ⟨a, by rw [← h]; ring⟩
  have h1 := Int.le_of_dvd (by omega) ((Int.natAbs_dvd.2 ha) |> fun h => Int.dvd_natAbs.2 h)
  have h2 := Int.le_of_dvd (by omega) ((Int.natAbs_dvd.2 hc) |> fun h => Int.dvd_natAbs.2 h)
  simp only [Set.mem_prod, Set.mem_Icc]
  omega


private lemma firstKind_ncard (hD4 : D % 4 = 0) :
    (firstKind D).ncard = {p : ℤ × ℤ | p.1 * p.2 = -(D / 4) ∧ IsCoprime p.1 p.2}.ncard := by
  refine Set.ncard_congr (fun f _ => (f.a, f.c)) ?_ ?_ ?_
  · rintro f ⟨hp, hd, hb⟩
    have h : f.a * f.c * 4 = -D := by rw [← hd]; simp only [BinQF.disc, hb]; ring
    exact ⟨by show f.a * f.c = -(D / 4); omega, (isPrimitive_iff (Or.inl hb)).1 hp⟩
  · intro f g hf hg h
    simp only [Prod.mk.injEq] at h
    exact BinQF.ext_abc h.1 (by rw [hf.2.2, hg.2.2]) h.2
  · rintro ⟨a, c⟩ ⟨h1, h2⟩
    replace h1 : a * c = -(D / 4) := h1
    replace h2 : IsCoprime a c := h2
    refine ⟨BinQF.mk a 0 c, ⟨(isPrimitive_iff (Or.inl (by simp))).2 (by simpa using h2), ?_, by simp⟩, by simp⟩
    simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
    have : a * c * 4 = -D := by omega
    linarith

/-- **Cassels, Ch. 14, Lemma 4.2, first column** (p. 342; table reconstructed, see the module docstring): the number
of primitive ambiguous forms $[a, 0, c]$ of discriminant $D \ne 0$. -/
@[kb "cassels1978" "Ch. 14, Lemma 4.2, p. 342 (first kind; table reconstructed)"]
theorem card_firstKind (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (firstKind D).ncard =
      if D % 4 = 1 then 0
      else if D / 4 % 2 = 1 then 2 ^ (numOddPrimes D + 1)
      else 2 ^ (numOddPrimes D + 2) := by
  by_cases h1 : D % 4 = 1
  · simp only [h1, ↓reduceIte]
    have : firstKind D = ∅ := by
      ext f
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, hd, hb⟩
      have : f.a * f.c * 4 = -D := by rw [← hd]; simp only [BinQF.disc, hb]; ring
      omega
    rw [this, Set.ncard_empty]
  · have h0 : D % 4 = 0 := by omega
    simp only [h1, ↓reduceIte]
    rw [firstKind_ncard h0, ncard_coprime_mul _ (by omega), Int.natAbs_neg]
    have hD' : D = 4 * (D / 4) := by omega
    have hd0 : D / 4 ≠ 0 := by omega
    have hnum : numOddPrimes D = numOddPrimes (D / 4) := by
      have := numOddPrimes_four_mul hd0
      rwa [← hD'] at this
    split_ifs with h2
    · rw [card_pf_of_odd (by omega), ← hnum]; ring
    · rw [card_pf_of_even hd0 (by omega), ← hnum]; ring

private lemma odd_left_of_mul {a e : ℤ} (h : (a * e) % 2 = 1) : a % 2 = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  have : a * e = 2 * (k * e) := by rw [hk]; ring
  omega

private lemma sub_mod_four_of_one {a e : ℤ} (h : (a * e) % 4 = 1) : (a - e) % 4 = 0 := by
  have h' : (a % 4) * (e % 4) % 4 = 1 := by rw [← Int.mul_emod]; exact h
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have he : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases ha with ha | ha | ha | ha <;> rcases he with he | he | he | he <;>
    simp [ha, he] at h' <;> omega

private lemma sub_mod_four_of_three {a e : ℤ} (h : (a * e) % 4 = 3) : (a - e) % 4 = 2 := by
  have h' : (a % 4) * (e % 4) % 4 = 3 := by rw [← Int.mul_emod]; exact h
  have ha : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  have he : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases ha with ha | ha | ha | ha <;> rcases he with he | he | he | he <;>
    simp [ha, he] at h' <;> omega

private lemma two_not_isCoprime {x y : ℤ} (h : IsCoprime x y) (hx : x % 2 = 0) (hy : y % 2 = 0) : False := by
  have := h.isUnit_of_dvd' (by omega : (2 : ℤ) ∣ x) (by omega : (2 : ℤ) ∣ y)
  rcases Int.isUnit_iff.1 this with h | h <;> omega

private lemma sub_odd_of_coprime_even {x y : ℤ} (h : IsCoprime x y) (hxy : (x * y) % 2 = 0) :
    (x - y) % 2 = 1 := by
  by_contra hne
  have h1 : x % 2 = y % 2 := by omega
  rcases Int.emod_two_eq_zero_or_one x with hx | hx
  · exact two_not_isCoprime h hx (by omega)
  · have := mul_emod_two_odd hx (by omega : y % 2 = 1)
    omega

/-- The second-kind forms of discriminant `D ≡ 0 (mod 4)`: `a = 2 x`, `x (x - 2 c) = D / 4`, `c` odd. -/
private lemma secondKind_four (hD : D % 4 = 0) {f : BinQF} (hf : f ∈ secondKind D) :
    ∃ x, f.a = 2 * x ∧ x * (x - 2 * f.c) = D / 4 ∧ f.c % 2 = 1 := by
  obtain ⟨hp, hd, hb⟩ := hf
  have h : f.a * (f.a - 4 * f.c) = D := by rw [← hd]; simp only [BinQF.disc, hb]; ring
  have hc := (isPrimitive_iff (Or.inr hb)).1 hp
  have hae : f.a % 2 = 0 := by
    by_contra hne
    have := mul_emod_two_odd (by omega : f.a % 2 = 1) (by omega : (f.a - 4 * f.c) % 2 = 1)
    omega
  obtain ⟨x, hx⟩ : ∃ x, f.a = 2 * x := ⟨f.a / 2, by omega⟩
  refine ⟨x, hx, ?_, ?_⟩
  · have : 4 * (x * (x - 2 * f.c)) = D := by rw [← h, hx]; ring
    omega
  · by_contra hne
    exact two_not_isCoprime hc hae (by omega)

private lemma secondKind_mod (hD : D % 4 = 0) {f : BinQF} (hf : f ∈ secondKind D) :
    D / 4 % 4 = 3 ∨ D / 4 % 8 = 0 := by
  obtain ⟨x, hx, hxd, hc⟩ := secondKind_four hD hf
  generalize f.c = c at hxd hc
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
    have h4 : 4 * (k * (k - c)) = D / 4 := by linarith
    right
    rcases Int.emod_two_eq_zero_or_one k with h' | h'
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      have : D / 4 = 8 * (j * (2 * j - c)) := by linarith
      omega
    · obtain ⟨m, hm⟩ : ∃ m, k - c = 2 * m := ⟨(k - c) / 2, by omega⟩
      rw [hm] at h4
      have : D / 4 = 8 * (k * m) := by linarith
      omega
  · left
    obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l, c = 2 * l + 1 := ⟨c / 2, by omega⟩
    have : D / 4 = 4 * (k * k - 2 * k * l - l) - 1 := by rw [← hxd]; ring
    omega

private lemma secondKind_eq_empty (hD : D % 4 = 0) (h3 : ¬ D / 4 % 4 = 3) (h8 : ¬ D / 4 % 8 = 0) :
    secondKind D = ∅ := by
  ext f
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hf
  rcases secondKind_mod hD hf with h | h <;> contradiction

private lemma secondKind_ncard_odd (hD : D % 4 = 1) :
    (secondKind D).ncard = {p : ℤ × ℤ | p.1 * p.2 = D ∧ IsCoprime p.1 p.2}.ncard := by
  refine Set.ncard_congr (fun f _ => (f.a, f.a - 4 * f.c)) ?_ ?_ ?_
  · rintro f ⟨hp, hd, hb⟩
    have h : f.a * (f.a - 4 * f.c) = D := by rw [← hd]; simp only [BinQF.disc, hb]; ring
    have hao : f.a % 2 = 1 := odd_left_of_mul (by rw [h]; omega)
    exact ⟨h, (coprime_sub_mul (isCoprime_four_of_odd hao)).2 ((isPrimitive_iff (Or.inr hb)).1 hp)⟩
  · intro f g hf hg h
    simp only [Prod.mk.injEq] at h
    exact BinQF.ext_abc h.1 (by rw [hf.2.2, hg.2.2, h.1]) (by omega)
  · rintro ⟨a, e⟩ ⟨h1, h2⟩
    replace h1 : a * e = D := h1
    replace h2 : IsCoprime a e := h2
    have hao : a % 2 = 1 := odd_left_of_mul (by rw [h1]; omega)
    have h4 : (a - e) % 4 = 0 := sub_mod_four_of_one (by rw [h1]; exact hD)
    have he : e = a - 4 * ((a - e) / 4) := by omega
    refine ⟨BinQF.mk a a ((a - e) / 4), ⟨(isPrimitive_iff (Or.inr (by simp))).2 ?_, ?_, by simp⟩, ?_⟩
    · simp only [BinQF.a_mk, BinQF.c_mk]
      rw [he] at h2
      exact (coprime_sub_mul (isCoprime_four_of_odd hao)).1 h2
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
      rw [he] at h1
      linarith
    · simp only [BinQF.a_mk, BinQF.c_mk, Prod.mk.injEq, true_and]
      omega

private lemma secondKind_ncard_three (hD : D % 4 = 0) (h3 : D / 4 % 4 = 3) :
    (secondKind D).ncard = {p : ℤ × ℤ | p.1 * p.2 = D / 4 ∧ IsCoprime p.1 p.2}.ncard := by
  refine Set.ncard_congr (fun f _ => (f.a / 2, f.a / 2 - 2 * f.c)) ?_ ?_ ?_
  · intro f hf
    obtain ⟨x, hx, hxd, hc⟩ := secondKind_four hD hf
    have hxo : x % 2 = 1 := odd_left_of_mul (by rw [hxd]; omega)
    have hcop := (isPrimitive_iff (Or.inr hf.2.2)).1 hf.1
    rw [hx] at hcop
    have hxc : IsCoprime x f.c := hcop.of_mul_left_right
    have : f.a / 2 = x := by omega
    rw [this]
    exact ⟨hxd, (coprime_sub_mul (isCoprime_two_of_odd hxo)).2 hxc⟩
  · intro f g hf hg h
    obtain ⟨x, hx, -, -⟩ := secondKind_four hD hf
    obtain ⟨y, hy, -, -⟩ := secondKind_four hD hg
    simp only [Prod.mk.injEq] at h
    exact BinQF.ext_abc (by omega) (by rw [hf.2.2, hg.2.2]; omega) (by omega)
  · rintro ⟨x, y⟩ ⟨h1, h2⟩
    replace h1 : x * y = D / 4 := h1
    replace h2 : IsCoprime x y := h2
    have hxo : x % 2 = 1 := odd_left_of_mul (by rw [h1]; omega)
    have hyo : y % 2 = 1 := odd_left_of_mul (by rw [mul_comm, h1]; omega)
    have h4 : (x - y) % 4 = 2 := sub_mod_four_of_three (by rw [h1]; omega)
    have h2c : 2 * ((x - y) / 2) = x - y := by omega
    have hco : ((x - y) / 2) % 2 = 1 := by omega
    have hy' : y = x - 2 * ((x - y) / 2) := by omega
    have hxy : 4 * (x * y) = D := by omega
    refine ⟨BinQF.mk (2 * x) (2 * x) ((x - y) / 2), ⟨(isPrimitive_iff (Or.inr (by simp))).2 ?_, ?_, by simp⟩, ?_⟩
    · simp only [BinQF.a_mk, BinQF.c_mk]
      refine IsCoprime.mul_left (isCoprime_two_of_odd hco).symm ?_
      rw [hy'] at h2
      exact (coprime_sub_mul (isCoprime_two_of_odd hxo)).1 h2
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
      linear_combination (-4 * x) * h2c + hxy
    · simp only [BinQF.a_mk, BinQF.c_mk, Prod.mk.injEq]
      omega

private lemma secondKind_ncard_eight (hD : D % 4 = 0) (h8 : D / 4 % 8 = 0) :
    (secondKind D).ncard = {p : ℤ × ℤ | p.1 * p.2 = D / 16 ∧ IsCoprime p.1 p.2}.ncard := by
  refine Set.ncard_congr (fun f _ => (f.a / 4, f.a / 4 - f.c)) ?_ ?_ ?_
  · intro f hf
    obtain ⟨x, hx, hxd, hc⟩ := secondKind_four hD hf
    have hxe : x % 2 = 0 := by
      by_contra hne
      have := mul_emod_two_odd (by omega : x % 2 = 1) (by omega : (x - 2 * f.c) % 2 = 1)
      omega
    obtain ⟨z, hz⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
    have hcop := (isPrimitive_iff (Or.inr hf.2.2)).1 hf.1
    rw [hx, hz] at hcop
    have hzc : IsCoprime z f.c := (hcop.of_mul_left_right).of_mul_left_right
    have hfa : f.a / 4 = z := by omega
    rw [hfa]
    refine ⟨?_, ?_⟩
    · rw [hz] at hxd
      have : 4 * (z * (z - f.c)) = D / 4 := by linarith
      show z * (z - f.c) = D / 16
      omega
    · have := (coprime_sub_mul (a := z) (c := f.c) (k := 1) isCoprime_one_right).2 hzc
      simpa using this
  · intro f g hf hg h
    obtain ⟨x, hx, hxd, hc⟩ := secondKind_four hD hf
    obtain ⟨y, hy, hyd, hc'⟩ := secondKind_four hD hg
    have hxe : x % 2 = 0 := by
      by_contra hne
      have := mul_emod_two_odd (by omega : x % 2 = 1) (by omega : (x - 2 * f.c) % 2 = 1)
      omega
    have hye : y % 2 = 0 := by
      by_contra hne
      have := mul_emod_two_odd (by omega : y % 2 = 1) (by omega : (y - 2 * g.c) % 2 = 1)
      omega
    simp only [Prod.mk.injEq] at h
    exact BinQF.ext_abc (by omega) (by rw [hf.2.2, hg.2.2]; omega) (by omega)
  · rintro ⟨x, y⟩ ⟨h1, h2⟩
    replace h1 : x * y = D / 16 := h1
    replace h2 : IsCoprime x y := h2
    have hxy : 16 * (x * y) = D := by omega
    have hodd : (x - y) % 2 = 1 := sub_odd_of_coprime_even h2 (by rw [h1]; omega)
    refine ⟨BinQF.mk (4 * x) (4 * x) (x - y), ⟨(isPrimitive_iff (Or.inr (by simp))).2 ?_, ?_, by simp⟩, ?_⟩
    · simp only [BinQF.a_mk, BinQF.c_mk]
      refine IsCoprime.mul_left (isCoprime_four_of_odd hodd).symm ?_
      have := (coprime_sub_mul (a := x) (c := y) (k := 1) isCoprime_one_right).2 h2
      simpa using this
    · simp only [BinQF.disc, BinQF.a_mk, BinQF.b_mk, BinQF.c_mk]
      linear_combination hxy
    · simp only [BinQF.a_mk, BinQF.c_mk, Prod.mk.injEq]
      omega

/-- **Cassels, Ch. 14, Lemma 4.2, second column** (p. 342; table reconstructed, see the module docstring): the number
of primitive ambiguous forms $[a, a, c]$ of discriminant $D \ne 0$. -/
@[kb "cassels1978" "Ch. 14, Lemma 4.2, p. 342 (second kind; table reconstructed)"]
theorem card_secondKind (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    (secondKind D).ncard =
      if D % 4 = 1 then 2 ^ (numOddPrimes D + 1)
      else if D / 4 % 4 = 3 then 2 ^ (numOddPrimes D + 1)
      else if D / 4 % 8 = 0 then 2 ^ (numOddPrimes D + 2)
      else 0 := by
  by_cases h1 : D % 4 = 1
  · simp only [h1, ↓reduceIte]
    rw [secondKind_ncard_odd h1, ncard_coprime_mul _ hD, card_pf_of_odd (by omega)]
    ring
  · have h0 : D % 4 = 0 := by omega
    have hD' : D = 4 * (D / 4) := by omega
    have hd0 : D / 4 ≠ 0 := by omega
    have hnum : numOddPrimes D = numOddPrimes (D / 4) := by
      have := numOddPrimes_four_mul hd0
      rwa [← hD'] at this
    by_cases h3 : D / 4 % 4 = 3
    · simp only [h1, h3, ↓reduceIte]
      rw [secondKind_ncard_three h0 h3, ncard_coprime_mul _ hd0, card_pf_of_odd (by omega), ← hnum]
      ring
    · by_cases h8 : D / 4 % 8 = 0
      · simp only [h1, h3, h8, ↓reduceIte]
        have hn0 : D / 16 ≠ 0 := by omega
        have hD'' : D / 4 = 4 * (D / 16) := by omega
        have hnum' : numOddPrimes (D / 4) = numOddPrimes (D / 16) := by
          have := numOddPrimes_four_mul hn0
          rwa [← hD''] at this
        rw [secondKind_ncard_eight h0 h8, ncard_coprime_mul _ hn0,
          card_pf_of_even hn0 (by omega), hnum, hnum']
        ring
      · simp only [h1, h3, h8, ↓reduceIte]
        rw [secondKind_eq_empty h0 h3 h8, Set.ncard_empty]

/-- **Cassels, Ch. 14, Lemma 4.2, last column** (p. 342): the total number of primitive ambiguous forms; the two
kinds are disjoint ($a = 0$ would force $D = 0$). -/
@[kb "cassels1978" "Ch. 14, Lemma 4.2, p. 342 (total)"]
theorem card_ambiguousForms (hD : D ≠ 0) (hD4 : D % 4 = 0 ∨ D % 4 = 1) :
    {f : BinQF | f.IsPrimitive ∧ f.disc = D ∧ IsAmbiguousForm f}.ncard =
      (firstKind D).ncard + (secondKind D).ncard := by
  have hset : {f : BinQF | f.IsPrimitive ∧ f.disc = D ∧ IsAmbiguousForm f} =
      firstKind D ∪ secondKind D := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_union, firstKind, secondKind, IsAmbiguousForm]
    tauto
  have hfin1 : (firstKind D).Finite := by
    refine Set.Finite.of_injOn (f := fun f : BinQF => (f.a, -4 * f.c)) (t := {p : ℤ × ℤ | p.1 * p.2 = D})
      ?_ ?_ (finite_mul_eq hD)
    · rintro f ⟨-, hd, hb⟩
      show f.a * (-4 * f.c) = D
      rw [← hd]; simp only [BinQF.disc, hb]; ring
    · intro f hf g hg h
      simp only [Prod.mk.injEq] at h
      exact BinQF.ext_abc h.1 (by rw [hf.2.2, hg.2.2]) (by omega)
  have hfin2 : (secondKind D).Finite := by
    refine Set.Finite.of_injOn (f := fun f : BinQF => (f.a, f.a - 4 * f.c)) (t := {p : ℤ × ℤ | p.1 * p.2 = D})
      ?_ ?_ (finite_mul_eq hD)
    · rintro f ⟨-, hd, hb⟩
      show f.a * (f.a - 4 * f.c) = D
      rw [← hd]; simp only [BinQF.disc, hb]; ring
    · intro f hf g hg h
      simp only [Prod.mk.injEq] at h
      exact BinQF.ext_abc h.1 (by rw [hf.2.2, hg.2.2, h.1]) (by omega)
  have hdisj : Disjoint (firstKind D) (secondKind D) := by
    rw [Set.disjoint_left]
    rintro f ⟨-, hd, hb⟩ ⟨-, -, hb'⟩
    apply hD
    rw [← hd]
    have : f.a = 0 := by omega
    simp only [BinQF.disc, hb, this]; ring
  rw [hset, Set.ncard_union_eq hdisj hfin1 hfin2]

end QuadFormsKB.Composition
