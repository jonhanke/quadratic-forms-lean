/-
# Cassels, Chapter 14, §2: composition of binary forms (Dirichlet)

Cassels, *Rational Quadratic Forms* (1978), Ch. 14, §1–§2, pp. 331–338.

Conventions (Cassels, Ch. 14, (1.1)–(1.7), p. 331): an integral binary form is $f = [a, b, c] = ax^2 + bxy + cy^2$
with $a, b, c \in \mathbb Z$ (the library's `BinQF`, `BinQF.mk a b c`; Cassels' non-classical integrality), it is
*primitive* if $\gcd(a, b, c) = 1$ (`BinQF.IsPrimitive`), its discriminant is $D = b^2 - 4ac$ (`BinQF.disc`), and
"equivalent" means *properly* equivalent, $f \sim g$ if $g = f \circ T$ with $T \in \mathrm{SL}_2(\mathbb Z)$
(`Binary.SLEquiv`). Cassels' variables $x, y$ are the coordinates $x_0, x_1$ of `QuadForm ℤ 2`.

This file proves, for **every** discriminant $D$ (positive or negative, square or not), the elementary lemmas of
Dirichlet's composition:

* Lemma 2.1 (`exists_sLEquiv_a_coprime`: a primitive form is properly equivalent to a form whose first coefficient is
  prime to a given $M \ne 0$);
* Lemma 2.2 (`sLEquiv_mul_a_div_c`);
* concordant forms and their composition (14.r5, `Concordant`, `comp`, `isPrimitive_comp`, `disc_comp`);
* Lemma 2.3 (`exists_concordant`) and Lemma 2.4 (`comp_sLEquiv_comp`).

The group of classes (Theorem 2.1) is in `Ch14/Group.lean`.
-/
import QuadFormsKB.Binary.GenusComposition
import QuadFormsKB.Literature.Cassels.Ch9Sec3Finite

namespace QuadFormsKB.Composition

open BinQF Binary

/-! ### Elementary facts about proper equivalence -/

/-- **Proper equivalence preserves the discriminant.** -/
theorem SLEquiv.disc_eq {f g : BinQF} (h : SLEquiv f g) : f.disc = g.disc := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).1 h
  rw [disc_subst, hd]; simp

private theorem mk_eta (f : BinQF) : mk f.a f.b f.c = f := ext_abc (by simp) (by simp) (by simp)

private theorem subst_inv (p q r s : ℤ) (hd : p * s - q * r = 1) (f : BinQF) :
    subst s (-q) (-r) p (subst p q r s f) = f := by
  refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk]
  · linear_combination (f.a * (p * s - q * r + 1)) * hd
  · linear_combination (f.b * (p * s - q * r + 1)) * hd
  · linear_combination (f.c * (p * s - q * r + 1)) * hd

/-- **Proper equivalence preserves primitivity.** -/
theorem SLEquiv.isPrimitive {f g : BinQF} (h : SLEquiv f g) (hf : f.IsPrimitive) : g.IsPrimitive := by
  obtain ⟨p, q, r, s, hd, hg⟩ := (sLEquiv_iff _ _).1 h
  intro d da db dc
  have key : subst s (-q) (-r) p g = f := by rw [← hg]; exact subst_inv p q r s hd f
  have ea := congrArg BinQF.a key
  have eb := congrArg BinQF.b key
  have ec := congrArg BinQF.c key
  simp only [subst, a_mk, b_mk, c_mk] at ea eb ec
  apply hf d
  · have : f.a = g.a * s ^ 2 + g.b * (-(s * r)) + g.c * r ^ 2 := by rw [← ea]; ring
    rw [this]
    exact dvd_add (dvd_add (da.mul_right _) (db.mul_right _)) (dc.mul_right _)
  · have : f.b = g.a * (-(2 * s * q)) + g.b * (s * p + q * r) + g.c * (-(2 * r * p)) := by rw [← eb]; ring
    rw [this]
    exact dvd_add (dvd_add (da.mul_right _) (db.mul_right _)) (dc.mul_right _)
  · have : f.c = g.a * q ^ 2 + g.b * (-(q * p)) + g.c * p ^ 2 := by rw [← ec]; ring
    rw [this]
    exact dvd_add (dvd_add (da.mul_right _) (db.mul_right _)) (dc.mul_right _)

/-- **Proper equivalence is compatible with $[a, b, c] \mapsto [a, -b, c]$** (conjugate the substitution by
$\operatorname{diag}(1, -1)$: $\begin{pmatrix} p & q \\ r & s \end{pmatrix} \mapsto
\begin{pmatrix} p & -q \\ -r & s \end{pmatrix}$). -/
theorem sLEquiv_conjForm {f g : BinQF} (h : SLEquiv f g) : SLEquiv (conjForm f) (conjForm g) := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).1 h
  refine (sLEquiv_iff _ _).2 ⟨p, -q, -r, s, by linear_combination hd, ?_⟩
  refine ext_abc ?_ ?_ ?_ <;> simp only [conjForm, subst, a_mk, b_mk, c_mk] <;> ring

/-- **$[a, b, c] \sim [c, -b, a]$** (the substitution $x \mapsto -y$, $y \mapsto x$). -/
theorem sLEquiv_swap (a b c : ℤ) : SLEquiv (mk a b c) (mk c (-b) a) := by
  refine (sLEquiv_iff _ _).2 ⟨0, -1, 1, 0, by norm_num, ?_⟩
  refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk] <;> ring

/-- **Proper equivalence preserves represented values.** -/
theorem SLEquiv.represents {f g : BinQF} (h : SLEquiv f g) {m : ℤ} (hm : g.Represents m) : f.Represents m := by
  obtain ⟨p, q, r, s, hd, rfl⟩ := (sLEquiv_iff _ _).1 h
  obtain ⟨x, y, hxy⟩ := hm
  exact ⟨p * x + q * y, r * x + s * y, by rw [← eval_subst]; exact hxy⟩

/-- **The translation $x \mapsto x + ly$:** $[a, b, c] \sim [a,\ b + 2al,\ al^2 + bl + c]$. -/
theorem sLEquiv_translate (a b c l : ℤ) : SLEquiv (mk a b c) (mk a (b + 2 * a * l) (a * l ^ 2 + b * l + c)) := by
  refine (sLEquiv_iff _ _).2 ⟨1, l, 0, 1, by norm_num, ?_⟩
  refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk] <;> ring

/-- **A form is determined by $a \ne 0$, $b$ and $D$:** two forms with the same $a \ne 0$, the same $b$ and the same
discriminant are equal (Cassels' convention $[a, b, *]$, p. 335). -/
theorem eq_of_a_b_disc {f g : BinQF} (ha : f.a ≠ 0) (hab : f.a = g.a) (hb : f.b = g.b) (hD : f.disc = g.disc) :
    f = g := by
  refine ext_abc hab hb ?_
  have h : f.a * f.c = f.a * g.c := by
    simp only [BinQF.disc] at hD
    rw [← hab, ← hb] at hD
    linarith
  exact mul_left_cancel₀ ha h

/-- **Moving the middle coefficient** (the substitution $x \mapsto x + ly$ of Cassels, Ch. 14, p. 335): if
$B \equiv b \pmod{2a}$ then $f = [a, b, *]$ is properly equivalent to a form $[a, B, *]$. -/
theorem exists_sLEquiv_b {f : BinQF} {B : ℤ} (hB : 2 * f.a ∣ B - f.b) :
    ∃ g : BinQF, SLEquiv f g ∧ g.a = f.a ∧ g.b = B := by
  obtain ⟨l, hl⟩ := hB
  refine ⟨mk f.a B (f.a * l ^ 2 + f.b * l + f.c), ?_, by simp, by simp⟩
  have := sLEquiv_translate f.a f.b f.c l
  rw [mk_eta] at this
  have hB : B = f.b + 2 * f.a * l := by linarith
  rw [hB]; exact this

/-- **The common middle coefficient** (Cassels, Ch. 14, p. 336, "as in the proof of Lemma 2.3"): if $a, a'$ are coprime
and $b \equiv b' \pmod 2$, there is $B$ with $B \equiv b \pmod{2a}$ and $B \equiv b' \pmod{2a'}$. -/
theorem exists_common_b {a a' b b' : ℤ} (hcop : IsCoprime a a') (hbb : 2 ∣ b - b') :
    ∃ B : ℤ, 2 * a ∣ B - b ∧ 2 * a' ∣ B - b' := by
  obtain ⟨k, hk⟩ := hbb
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨b - 2 * a * u * k, ⟨-(u * k), by ring⟩, ⟨k * v, ?_⟩⟩
  linear_combination (-(2 * k)) * huv + hk

/-- **A primitively represented integer is a first coefficient:** if $f(x, y) = m$ with $\gcd(x, y) = 1$, then $f$ is
properly equivalent to a form $[m, *, *]$. -/
theorem exists_sLEquiv_a_of_eval {f : BinQF} {x y : ℤ} (hxy : IsCoprime x y) :
    ∃ g : BinQF, SLEquiv f g ∧ g.a = f.eval x y := by
  obtain ⟨r, s, hrs, ha⟩ := exists_subst_a_eq f hxy
  exact ⟨_, (sLEquiv_iff _ _).2 ⟨x, r, y, s, hrs, rfl⟩, ha⟩

/-- The middle coefficient has the parity of the discriminant. -/
theorem two_dvd_b_sub_b {f g : BinQF} (hD : f.disc = g.disc) : 2 ∣ f.b - g.b := by
  simp only [BinQF.disc] at hD
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' f.b <;> obtain ⟨m, hm | hm⟩ := Int.even_or_odd' g.b <;>
    rw [hk, hm] at hD ⊢
  · exact ⟨k - m, by ring⟩
  · exfalso
    obtain ⟨X, hX⟩ : ∃ X : ℤ, 4 * X = 1 := ⟨k ^ 2 - f.a * f.c - m ^ 2 - m + g.a * g.c, by linear_combination hD⟩
    omega
  · exfalso
    obtain ⟨X, hX⟩ : ∃ X : ℤ, 4 * X = 1 :=
      ⟨m ^ 2 - g.a * g.c - k ^ 2 - k + f.a * f.c, by linear_combination -hD⟩
    omega
  · exact ⟨k - m, by ring⟩

/-! ### Lemma 2.1 -/

/-- **Cassels, Ch. 14, Lemma 2.1** (p. 334), in the form used in §2: *let $f = [a,b,c]$ be a primitive form and $M$
any integer. Then $f$ represents an integer prime to $M$.* Here $M \ne 0$ and the represented integer
$a' = f(x, y)$ is represented primitively, so it is the first coefficient of a properly equivalent form
$[a', b', c'] \sim f$; for $M \ne \pm 1$ it is non-zero. (The statement with the values themselves is
`Binary.exists_coprime_value`.) -/
@[kb "cassels1978" "Ch. 14, Lemma 2.1, p. 334 (primitive representation, as a first coefficient)"]
theorem exists_sLEquiv_a_coprime {f : BinQF} (hf : f.IsPrimitive) {M : ℤ} (hM : M ≠ 0) :
    ∃ g : BinQF, SLEquiv f g ∧ IsCoprime g.a M := by
  obtain ⟨x, y, -, -, hxy, hp⟩ :=
    exists_coprime_value ((primitive_iff_isPrimitive f).2 hf) (N := M.natAbs) (Int.natAbs_ne_zero.2 hM)
  obtain ⟨g, e, ha⟩ := exists_sLEquiv_a_of_eval (f := f) hxy
  refine ⟨g, e, ?_⟩
  rw [ha, Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp', hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : (p : ℤ) ∣ f.eval x y :=
    (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left ..)
  have h2 : (p : ℤ) ∣ M := (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right ..)
  exact hp p hp' (Int.natCast_dvd.1 h2) h1

/-! ### Lemma 2.2 -/

/-- **Cassels, Ch. 14, Lemma 2.2** (pp. 334–335): *suppose that $[a_1, b, c_1] \sim [a_2, b, c_2]$, where the two
forms have the same middle coefficient. Let $l$ be an integer with $l \mid c_1$, $l \mid c_2$ (2.4), and suppose that
$\gcd(a_1, a_2, l) = 1$ (2.5). Then $[a_1l, b, c_1/l] \sim [a_2l, b, c_2/l]$ (2.6).*

The conditions (2.4) and the conclusion (2.6) are lost in the machine-read text; they are reconstructed from the
proof (an equivalence $T = \begin{pmatrix} r & s \\ t & u \end{pmatrix}$ gives $a_1s + c_2t = 0$, $a_2s + c_1t = 0$,
hence $l \mid s$, and $\begin{pmatrix} r & s/l \\ lt & u \end{pmatrix}$ is the new equivalence) and from its use in
Lemma 2.4 ((2.21)–(2.22) and the footnote on p. 337). Cassels assumes the two forms primitive; this is not needed.
The case $l = 0$ is excluded ($c_j/l$ is meaningless).

*Reconciliation*: Equivalent to `Cassels.sLEquiv_mk_mul_left` (write $c_j = lc_j'$), which carries the tag. -/
theorem sLEquiv_mul_a_div_c {a₁ a₂ b c₁ c₂ l : ℤ} (h : SLEquiv (mk a₁ b c₁) (mk a₂ b c₂)) (hl : l ≠ 0)
    (hl₁ : l ∣ c₁) (hl₂ : l ∣ c₂) (hg : Int.gcd (Int.gcd a₁ a₂) l = 1) :
    SLEquiv (mk (a₁ * l) b (c₁ / l)) (mk (a₂ * l) b (c₂ / l)) := by
  obtain ⟨c₁', rfl⟩ := hl₁
  obtain ⟨c₂', rfl⟩ := hl₂
  obtain ⟨p, q, r, s, hd, hsub⟩ := (sLEquiv_iff _ _).1 h
  have h1 := congrArg BinQF.a hsub
  have h2 := congrArg BinQF.b hsub
  have h3 := congrArg BinQF.c hsub
  simp only [subst, a_mk, b_mk, c_mk] at h1 h2 h3
  have E2 : 2 * (a₁ * p * q + b * q * r + l * c₁' * r * s) = 0 := by
    linear_combination h2 - b * hd
  have E : a₁ * p * q + b * q * r + l * c₁' * r * s = 0 := by linarith
  have hA : a₁ * q + (l * c₂') * r = 0 := by
    linear_combination s * E - r * h3 - a₁ * q * hd
  have hB : a₂ * q + (l * c₁') * r = 0 := by
    linear_combination p * E - (l * c₁') * r * hd - q * h1
  -- `l ∣ q`
  have hlA : l ∣ a₁ * q := ⟨-(c₂' * r), by linear_combination hA⟩
  have hlB : l ∣ a₂ * q := ⟨-(c₁' * r), by linear_combination hB⟩
  have hcop : IsCoprime l (Int.gcd a₁ a₂ : ℤ) := by
    have : IsCoprime (Int.gcd a₁ a₂ : ℤ) l := Int.isCoprime_iff_gcd_eq_one.2 hg
    exact this.symm
  have hlg : l ∣ q * (Int.gcd a₁ a₂ : ℤ) := by
    rw [Int.gcd_eq_gcd_ab a₁ a₂]
    have : q * (a₁ * Int.gcdA a₁ a₂ + a₂ * Int.gcdB a₁ a₂) =
        a₁ * q * Int.gcdA a₁ a₂ + a₂ * q * Int.gcdB a₁ a₂ := by ring
    rw [this]
    exact dvd_add (hlA.mul_right _) (hlB.mul_right _)
  obtain ⟨q', rfl⟩ := hcop.dvd_of_dvd_mul_right hlg
  rw [Int.mul_ediv_cancel_left _ hl, Int.mul_ediv_cancel_left _ hl]
  refine (sLEquiv_iff _ _).2 ⟨p, q', l * r, s, by linear_combination hd, ?_⟩
  refine ext_abc ?_ ?_ ?_ <;> simp only [subst, a_mk, b_mk, c_mk]
  · linear_combination l * h1
  · linear_combination h2
  · exact mul_left_cancel₀ hl (by linear_combination h3)

/-- If `4x` and `4y` divide `m` and `x, y` are coprime, then `4xy` divides `m`. -/
private theorem dvd4_of_coprime {x y m : ℤ} (hcop : IsCoprime x y) (hx : 4 * x ∣ m) (hy : 4 * y ∣ m) :
    4 * x * y ∣ m := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  have h : x * u = y * v := by linarith
  have hxv : x ∣ v := hcop.dvd_of_dvd_mul_left ⟨u, by linarith⟩
  obtain ⟨w, rfl⟩ := hxv
  exact ⟨w, by linear_combination hv⟩

/-- Shifting the middle coefficient by a multiple of `2x` preserves `4x ∣ b² - D`. -/
private theorem dvd4_shift {x b B D : ℤ} (hx : 4 * x ∣ b ^ 2 - D) (hB : 2 * x ∣ B - b) :
    4 * x ∣ B ^ 2 - D := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨t, ht⟩ := hB
  refine ⟨u + t * (x * t + b), ?_⟩
  have : B = b + 2 * x * t := by linarith
  subst this
  linear_combination hu

/-- The form `[a, B, (B² - D)/(4a)]` exists with discriminant `D` when `a ≠ 0` and `4a ∣ B² - D`. -/
private theorem exists_form {a B D : ℤ} (h : 4 * a ∣ B ^ 2 - D) :
    ∃ X : BinQF, X.a = a ∧ X.b = B ∧ X.disc = D := by
  obtain ⟨k, hk⟩ := h
  refine ⟨mk a B k, by simp, by simp, ?_⟩
  simp only [BinQF.disc, a_mk, b_mk, c_mk]
  linear_combination hk

/-- **Lemma 2.2 in the form used for Lemma 2.4:** if $f_1 = [a_1, B, *] \sim f_2 = [a_2, B, *]$ ($a_1a_2 \ne 0$) have
discriminant $D$, $l \ne 0$ is prime to $a_1$ (so $\gcd(a_1, a_2, l) = 1$), and $g_j = [a_jl, B, *]$ are integral
forms of discriminant $D$ (this is condition (2.4): $4a_jl \mid B^2 - D$), then $g_1 \sim g_2$. -/
theorem sLEquiv_mul_a {f₁ f₂ g₁ g₂ : BinQF} {l : ℤ} (h : SLEquiv f₁ f₂) (hb : f₁.b = f₂.b) (hl : l ≠ 0)
    (ha : f₁.a * f₂.a ≠ 0) (hcop : IsCoprime f₁.a l) (hD : f₁.disc = f₂.disc)
    (hg₁ : g₁.a = f₁.a * l ∧ g₁.b = f₁.b ∧ g₁.disc = f₁.disc)
    (hg₂ : g₂.a = f₂.a * l ∧ g₂.b = f₂.b ∧ g₂.disc = f₂.disc) : SLEquiv g₁ g₂ := by
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul ha
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul ha
  -- `l ∣ c_j`
  have hc : ∀ (f g : BinQF), f.a ≠ 0 → g.a = f.a * l ∧ g.b = f.b ∧ g.disc = f.disc → l ∣ f.c ∧ f.c / l = g.c := by
    intro f g hf ⟨hga, hgb, hgD⟩
    have : f.a * f.c = f.a * (l * g.c) := by
      simp only [BinQF.disc] at hgD
      rw [hga, hgb] at hgD
      linarith
    have hfc : f.c = l * g.c := mul_left_cancel₀ hf this
    exact ⟨⟨g.c, hfc⟩, by rw [hfc, Int.mul_ediv_cancel_left _ hl]⟩
  obtain ⟨hl₁, hq₁⟩ := hc f₁ g₁ ha₁ hg₁
  obtain ⟨hl₂, hq₂⟩ := hc f₂ g₂ ha₂ hg₂
  have e1 : f₁ = mk f₁.a f₁.b f₁.c := (mk_eta f₁).symm
  have e2 : f₂ = mk f₂.a f₁.b f₂.c := by rw [hb, mk_eta]
  have hgcd : Int.gcd (Int.gcd f₁.a f₂.a) l = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.1
    exact hcop.of_isCoprime_of_dvd_left (Int.gcd_dvd_left ..)
  rw [e1, e2] at h
  have := sLEquiv_mul_a_div_c h hl hl₁ hl₂ hgcd
  rw [hq₁, hq₂] at this
  have g1 : g₁ = mk (f₁.a * l) f₁.b g₁.c := by
    rw [← hg₁.1, ← hg₁.2.1, mk_eta]
  have g2 : g₂ = mk (f₂.a * l) f₁.b g₂.c := by
    rw [← hg₂.1, hb, ← hg₂.2.1, mk_eta]
  rw [g1, g2]; exact this

/-! ### Concordant forms and their composition (14.r5) -/

/-- **Concordant forms** (Cassels, Ch. 14, §2, (2.7)–(2.9), p. 335): $f_1 = [a_1, b_1, c_1]$ and
$f_2 = [a_2, b_2, c_2]$ of the same discriminant $D$ are *concordant* if (i) $a_1a_2 \ne 0$, (ii) $b_1 = b_2$ (`= b`),
and (iii) the form $[a_1a_2, b, (b^2 - D)/(4a_1a_2)]$ is integral, i.e. $4a_1a_2 \mid b^2 - D$. Cassels requires the
two forms to be primitive; here primitivity is a separate hypothesis where it is needed. -/
@[kb "cassels1978" "Ch. 14, §2, (2.7)–(2.9), p. 335 (concordant forms)"]
def Concordant (f₁ f₂ : BinQF) : Prop :=
  f₁.a * f₂.a ≠ 0 ∧ f₁.b = f₂.b ∧ f₁.disc = f₂.disc ∧ 4 * f₁.a * f₂.a ∣ f₁.b ^ 2 - f₁.disc

/-- **The composition of concordant forms** (Cassels, Ch. 14, (2.9), p. 335):
$f_3 = [a_1a_2,\ b,\ (b^2 - D)/(4a_1a_2)]$ with $b = b_1$, $D = \operatorname{disc} f_1$. (For forms which are not
concordant the integer division makes this a meaningless form; only concordant pairs are used.) -/
@[kb "cassels1978" "Ch. 14, §2, (2.9), p. 335 (composition of concordant forms)"]
def comp (f₁ f₂ : BinQF) : BinQF :=
  mk (f₁.a * f₂.a) f₁.b ((f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a))

@[simp] theorem a_comp (f₁ f₂ : BinQF) : (comp f₁ f₂).a = f₁.a * f₂.a := by simp [comp]
@[simp] theorem b_comp (f₁ f₂ : BinQF) : (comp f₁ f₂).b = f₁.b := by simp [comp]

/-- Concordance is symmetric. -/
theorem Concordant.symm {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) : Concordant f₂ f₁ := by
  obtain ⟨h0, hb, hD, hd⟩ := h
  refine ⟨by rwa [mul_comm], hb.symm, hD.symm, ?_⟩
  rw [← hb, ← hD, show 4 * f₂.a * f₁.a = 4 * f₁.a * f₂.a by ring]
  exact hd

/-- Composition is commutative on concordant pairs. -/
theorem Concordant.comp_comm {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) : comp f₁ f₂ = comp f₂ f₁ := by
  obtain ⟨h0, hb, hD, hd⟩ := h
  unfold comp
  rw [← hb, ← hD, show 4 * f₂.a * f₁.a = 4 * f₁.a * f₂.a by ring, mul_comm f₂.a f₁.a]

private theorem c_comp (f₁ f₂ : BinQF) :
    (comp f₁ f₂).c = (f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a) := by simp [comp]

/-- **The composition has discriminant $D$** (Cassels, Ch. 14, (2.9), p. 335). -/
@[kb "cassels1978" "Ch. 14, §2, (2.9), p. 335"]
theorem disc_comp {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) : (comp f₁ f₂).disc = f₁.disc := by
  obtain ⟨h0, hb, hD, k, hk⟩ := h
  have h4 : 4 * f₁.a * f₂.a ≠ 0 := by
    have : f₁.a * f₂.a ≠ 0 := h0
    intro h'; apply this; linarith
  have hq : (f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a) = k := by
    rw [hk]; exact Int.mul_ediv_cancel_left _ h4
  have : (comp f₁ f₂).disc = (comp f₁ f₂).b ^ 2 - 4 * (comp f₁ f₂).a * (comp f₁ f₂).c := rfl
  rw [this, a_comp, b_comp, c_comp, hq]
  linear_combination hk

/-- **The composition of primitive concordant forms is primitive** (Cassels, Ch. 14, p. 335: "$f_3$ is then necessarily
primitive"; the remark refers back to §1). Its third coefficient is $c_1/a_2 = c_2/a_1$. -/
@[kb "cassels1978" "Ch. 14, §2, p. 335 (the composition is primitive)"]
theorem isPrimitive_comp {f₁ f₂ : BinQF} (h : Concordant f₁ f₂) (h₁ : f₁.IsPrimitive) (h₂ : f₂.IsPrimitive) :
    (comp f₁ f₂).IsPrimitive := by
  obtain ⟨h0, hb, hD, k, hk⟩ := h
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul h0
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul h0
  have hq : (f₁.b ^ 2 - f₁.disc) / (4 * f₁.a * f₂.a) = k := by
    have h4 : 4 * f₁.a * f₂.a ≠ 0 := by
      intro h'; apply h0; linarith
    rw [hk]; exact Int.mul_ediv_cancel_left _ h4
  -- `c₁ = a₂ k`, `c₂ = a₁ k`
  have hd1 : f₁.disc = f₁.b ^ 2 - 4 * f₁.a * f₁.c := rfl
  have hd2 : f₂.disc = f₂.b ^ 2 - 4 * f₂.a * f₂.c := rfl
  have hc₁ : f₁.c = f₂.a * k := by
    have : (4 * f₁.a) * f₁.c = (4 * f₁.a) * (f₂.a * k) := by
      linear_combination hk + hd1
    exact mul_left_cancel₀ (by simpa using ha₁) this
  have hc₂ : f₂.c = f₁.a * k := by
    have : (4 * f₂.a) * f₂.c = (4 * f₂.a) * (f₁.a * k) := by
      linear_combination hd2 + hD - (f₁.b + f₂.b) * hb + hk
    exact mul_left_cancel₀ (by simpa using ha₂) this
  intro d hda hdb hdc
  rw [a_comp] at hda
  rw [b_comp] at hdb
  rw [c_comp, hq] at hdc
  have hcop : IsCoprime d f₁.a := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    set g := Int.gcd d f₁.a with hg
    have hgd : (g : ℤ) ∣ d := Int.gcd_dvd_left ..
    have hga : (g : ℤ) ∣ f₁.a := Int.gcd_dvd_right ..
    have hu := h₁ g hga (hgd.trans hdb) (by rw [hc₁]; exact (hgd.trans hdc).mul_left _)
    have := Int.isUnit_iff_natAbs_eq.mp hu
    simpa using this
  have hd2' : d ∣ f₂.a := hcop.dvd_of_dvd_mul_left hda
  exact h₂ d hd2' (hb ▸ hdb) (by rw [hc₂]; exact hdc.mul_left _)

/-- **Cassels' Note** (Ch. 14, p. 335): *when $\gcd(a_1, a_2) = 1$, condition (iii) follows automatically from (i) and
(ii)*, since $4a_1 \mid D - b^2$ and $4a_2 \mid D - b^2$. -/
@[kb "cassels1978" "Ch. 14, §2, Note, p. 335"]
theorem concordant_of_coprime {f₁ f₂ : BinQF} (ha : f₁.a * f₂.a ≠ 0) (hb : f₁.b = f₂.b) (hD : f₁.disc = f₂.disc)
    (hcop : IsCoprime f₁.a f₂.a) : Concordant f₁ f₂ := by
  refine ⟨ha, hb, hD, ?_⟩
  have hd1 : f₁.disc = f₁.b ^ 2 - 4 * f₁.a * f₁.c := rfl
  have hd2 : f₂.disc = f₂.b ^ 2 - 4 * f₂.a * f₂.c := rfl
  have e1 : f₁.b ^ 2 - f₁.disc = 4 * f₁.a * f₁.c := by rw [hd1]; ring
  have e2 : f₁.b ^ 2 - f₁.disc = 4 * f₂.a * f₂.c := by rw [hD, hb, hd2]; ring
  have hx : f₁.a ∣ f₂.c := by
    have : f₁.a ∣ f₂.c * f₂.a := ⟨f₁.c, by linarith⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨w, hw⟩ := hx
  exact ⟨w, by rw [e2, hw]; ring⟩

/-! ### Lemmas 2.3 and 2.4 -/

/-- **Cassels, Ch. 14, Lemma 2.3** (pp. 335–336): *let $\mathfrak C_1, \mathfrak C_2$ be two classes of primitive forms
of discriminant $D \ne 0$. Then there are concordant forms $f_j = [a_j, b, *] \in \mathfrak C_j$. Further, they may be
chosen so that $a_1, a_2$ are prime to one another and to any integer $M$ given in advance.* Here the classes are
given by representatives $f_1, f_2$ and $M \ne 0$.

*Reconciliation*: Superseded by `Cassels.exists_concordant`, the same conclusion without the hypothesis $D \ne 0$. -/
theorem exists_concordant {f₁ f₂ : BinQF} (h₁ : f₁.IsPrimitive) (h₂ : f₂.IsPrimitive) (hD : f₁.disc = f₂.disc)
    (hD0 : f₁.disc ≠ 0) {M : ℤ} (hM : M ≠ 0) :
    ∃ g₁ g₂ : BinQF, SLEquiv f₁ g₁ ∧ SLEquiv f₂ g₂ ∧ Concordant g₁ g₂ ∧ IsCoprime g₁.a g₂.a ∧
      IsCoprime (g₁.a * g₂.a) M := by
  have hnu : ∀ N : ℤ, ¬ IsUnit (2 * N) := by
    intro N hu
    have h2 : IsUnit (2 : ℤ) := isUnit_of_mul_isUnit_left hu
    rw [Int.isUnit_iff] at h2; omega
  obtain ⟨g₁, e₁, c₁⟩ := exists_sLEquiv_a_coprime h₁ (M := 2 * M) (mul_ne_zero two_ne_zero hM)
  have ha₁ : g₁.a ≠ 0 := by
    intro h0; rw [h0, isCoprime_zero_left] at c₁; exact hnu M c₁
  obtain ⟨g₂, e₂, c₂⟩ := exists_sLEquiv_a_coprime h₂ (M := 2 * (g₁.a * M))
    (mul_ne_zero two_ne_zero (mul_ne_zero ha₁ hM))
  have ha₂ : g₂.a ≠ 0 := by
    intro h0; rw [h0, isCoprime_zero_left] at c₂; exact hnu _ c₂
  have hcop12 : IsCoprime g₁.a g₂.a :=
    (c₂.of_isCoprime_of_dvd_right (⟨2 * M, by ring⟩ : g₁.a ∣ 2 * (g₁.a * M))).symm
  have hM2 : IsCoprime g₂.a M := c₂.of_isCoprime_of_dvd_right (⟨2 * g₁.a, by ring⟩ : M ∣ 2 * (g₁.a * M))
  have hM1 : IsCoprime g₁.a M := c₁.of_isCoprime_of_dvd_right (⟨2, by ring⟩ : M ∣ 2 * M)
  have hDg : g₁.disc = g₂.disc := by
    rw [← SLEquiv.disc_eq e₁, ← SLEquiv.disc_eq e₂]; exact hD
  obtain ⟨B, hB1, hB2⟩ := exists_common_b hcop12 (two_dvd_b_sub_b hDg)
  obtain ⟨h₁', e₁', ha₁', hb₁'⟩ := exists_sLEquiv_b hB1
  obtain ⟨h₂', e₂', ha₂', hb₂'⟩ := exists_sLEquiv_b hB2
  refine ⟨h₁', h₂', e₁.trans e₁', e₂.trans e₂', ?_, ?_, ?_⟩
  · refine concordant_of_coprime ?_ ?_ ?_ ?_
    · rw [ha₁', ha₂']; exact mul_ne_zero ha₁ ha₂
    · rw [hb₁', hb₂']
    · rw [← SLEquiv.disc_eq e₁', ← SLEquiv.disc_eq e₂']; exact hDg
    · rw [ha₁', ha₂']; exact hcop12
  · rw [ha₁', ha₂']; exact hcop12
  · rw [ha₁', ha₂']; exact hM1.mul_left hM2

/-- **The main step of Lemma 2.4** (Cassels, Ch. 14, (2.15)–(2.22), pp. 336–337): if $(f_1, f_2)$ and $(g_1, g_2)$ are
concordant pairs with $f_j \sim g_j$, $\gcd(g_1.a, g_2.a) = 1$ and $\gcd(f_1.a f_2.a,\ g_1.a g_2.a) = 1$, then
$\operatorname{comp}(f_1, f_2) \sim \operatorname{comp}(g_1, g_2)$. -/
theorem comp_sLEquiv_comp_of_coprime {f₁ f₂ g₁ g₂ : BinQF} (e₁ : SLEquiv f₁ g₁) (e₂ : SLEquiv f₂ g₂)
    (hc : Concordant f₁ f₂) (hc' : Concordant g₁ g₂) (hg : IsCoprime g₁.a g₂.a)
    (hfg : IsCoprime (f₁.a * f₂.a) (g₁.a * g₂.a)) :
    SLEquiv (comp f₁ f₂) (comp g₁ g₂) := by
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul hc.1
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul hc.1
  have hA₁ : g₁.a ≠ 0 := left_ne_zero_of_mul hc'.1
  have hA₂ : g₂.a ≠ 0 := right_ne_zero_of_mul hc'.1
  have hb := hc.2.1
  have hb' := hc'.2.1
  have hDfg₁ : f₁.disc = g₁.disc := SLEquiv.disc_eq e₁
  have hD12 := hc.2.2.1
  have hD12' := hc'.2.2.1
  have hcopsub : ∀ x y : ℤ, x ∣ f₁.a * f₂.a → y ∣ g₁.a * g₂.a → IsCoprime x y := fun x y hx hy =>
    (hfg.of_isCoprime_of_dvd_left hx).of_isCoprime_of_dvd_right hy
  have c_f₂g₁ : IsCoprime f₂.a g₁.a := hcopsub _ _ (dvd_mul_left _ _) (dvd_mul_right _ _)
  -- common middle coefficient
  obtain ⟨B, hB1, hB2⟩ := exists_common_b hfg (two_dvd_b_sub_b hDfg₁)
  have hB1₁ : 2 * f₁.a ∣ B - f₁.b :=
    dvd_trans (⟨f₂.a, by ring⟩ : 2 * f₁.a ∣ 2 * (f₁.a * f₂.a)) hB1
  have hB1₂ : 2 * f₂.a ∣ B - f₁.b :=
    dvd_trans (⟨f₁.a, by ring⟩ : 2 * f₂.a ∣ 2 * (f₁.a * f₂.a)) hB1
  have hB2₁ : 2 * g₁.a ∣ B - g₁.b :=
    dvd_trans (⟨g₂.a, by ring⟩ : 2 * g₁.a ∣ 2 * (g₁.a * g₂.a)) hB2
  have hB2₂ : 2 * g₂.a ∣ B - g₁.b :=
    dvd_trans (⟨g₁.a, by ring⟩ : 2 * g₂.a ∣ 2 * (g₁.a * g₂.a)) hB2
  obtain ⟨F₁, eF₁, haF₁, hbF₁⟩ := exists_sLEquiv_b (f := f₁) (B := B) hB1₁
  obtain ⟨F₂, eF₂, haF₂, hbF₂⟩ := exists_sLEquiv_b (f := f₂) (B := B) (by rw [← hb]; exact hB1₂)
  obtain ⟨Cf, eCf, haCf, hbCf⟩ := exists_sLEquiv_b (f := comp f₁ f₂) (B := B)
    (by rw [a_comp, b_comp]; exact hB1)
  obtain ⟨G₁, eG₁, haG₁, hbG₁⟩ := exists_sLEquiv_b (f := g₁) (B := B) hB2₁
  obtain ⟨G₂, eG₂, haG₂, hbG₂⟩ := exists_sLEquiv_b (f := g₂) (B := B) (by rw [← hb']; exact hB2₂)
  obtain ⟨Cg, eCg, haCg, hbCg⟩ := exists_sLEquiv_b (f := comp g₁ g₂) (B := B)
    (by rw [a_comp, b_comp]; exact hB2)
  rw [a_comp] at haCf haCg
  -- discriminants
  have dF₁ : F₁.disc = f₁.disc := (SLEquiv.disc_eq eF₁).symm
  have dF₂ : F₂.disc = f₁.disc := (SLEquiv.disc_eq eF₂).symm.trans hD12.symm
  have dG₁ : G₁.disc = f₁.disc := (SLEquiv.disc_eq eG₁).symm.trans hDfg₁.symm
  have dG₂ : G₂.disc = f₁.disc := (SLEquiv.disc_eq eG₂).symm.trans (hD12'.symm.trans hDfg₁.symm)
  have dCf : Cf.disc = f₁.disc := (SLEquiv.disc_eq eCf).symm.trans (disc_comp hc)
  have dCg : Cg.disc = f₁.disc :=
    (SLEquiv.disc_eq eCg).symm.trans ((disc_comp hc').trans hDfg₁.symm)
  -- divisibility `4x ∣ B² - D`
  have hf1 : 4 * f₁.a ∣ f₁.b ^ 2 - f₁.disc := (dvd_mul_right _ _).trans hc.2.2.2
  have hf2 : 4 * f₂.a ∣ f₁.b ^ 2 - f₁.disc :=
    dvd_trans (⟨f₁.a, by ring⟩ : 4 * f₂.a ∣ 4 * f₁.a * f₂.a) hc.2.2.2
  have hg1 : 4 * g₁.a ∣ g₁.b ^ 2 - f₁.disc := by
    rw [hDfg₁]; exact (dvd_mul_right _ _).trans hc'.2.2.2
  have hg2 : 4 * g₂.a ∣ g₁.b ^ 2 - f₁.disc := by
    rw [hDfg₁]; exact dvd_trans (⟨g₁.a, by ring⟩ : 4 * g₂.a ∣ 4 * g₁.a * g₂.a) hc'.2.2.2
  have P1 := dvd4_shift hf1 hB1₁
  have P2 := dvd4_shift hf2 hB1₂
  have Q1 := dvd4_shift hg1 hB2₁
  have Q2 := dvd4_shift hg2 hB2₂
  obtain ⟨X, hXa, hXb, hXD⟩ := exists_form (a := g₁.a * f₂.a) (B := B) (D := f₁.disc)
    (by have := dvd4_of_coprime c_f₂g₁.symm Q1 P2; rwa [mul_assoc] at this)
  -- first step: `[a₁'', B, *] ∼ [a₁, B, *]`, multiply by `a₂`
  have hGF : SLEquiv G₁ F₁ := (eG₁.symm.trans e₁.symm).trans eF₁
  have stepX : SLEquiv X Cf := by
    refine sLEquiv_mul_a (f₁ := G₁) (f₂ := F₁) (l := f₂.a) hGF (by rw [hbG₁, hbF₁]) ha₂
      (by rw [haG₁, haF₁]; exact mul_ne_zero hA₁ ha₁) (by rw [haG₁]; exact c_f₂g₁.symm)
      (by rw [dG₁, dF₁]) ⟨by rw [hXa, haG₁], by rw [hXb, hbG₁], by rw [hXD, dG₁]⟩
      ⟨by rw [haCf, haF₁], by rw [hbCf, hbF₁], by rw [dCf, dF₁]⟩
  -- second step: `[a₂, B, *] ∼ [a₂'', B, *]`, multiply by `a₁''`
  have hFG : SLEquiv F₂ G₂ := (eF₂.symm.trans e₂).trans eG₂
  have stepZ : SLEquiv X Cg := by
    refine sLEquiv_mul_a (f₁ := F₂) (f₂ := G₂) (l := g₁.a) hFG (by rw [hbF₂, hbG₂])
      hA₁ (by rw [haF₂, haG₂]; exact mul_ne_zero ha₂ hA₂) (by rw [haF₂]; exact c_f₂g₁)
      (by rw [dF₂, dG₂]) ⟨by rw [hXa, haF₂, mul_comm], by rw [hXb, hbF₂], by rw [hXD, dF₂]⟩
      ⟨by rw [haCg, haG₂, mul_comm], by rw [hbCg, hbG₂], by rw [dCg, dG₂]⟩
  exact eCf.trans (stepX.symm.trans (stepZ.trans eCg.symm))

/-- **Cassels, Ch. 14, Lemma 2.4** (pp. 336–337): *the class of the composition of $f_j \in \mathfrak C_j$ ($j = 1,2$)
depends only on $\mathfrak C_1, \mathfrak C_2$*: if $(f_1, f_2)$ and $(f_1', f_2')$ are pairs of concordant primitive
forms of discriminant $D \ne 0$ with $f_j \sim f_j'$, then $\operatorname{comp}(f_1, f_2) \sim \operatorname{comp}(f_1',
f_2')$ (2.12).

*Reconciliation*: Superseded by `Cassels.sLEquiv_compose`, which needs neither $D \ne 0$ nor primitivity of the second pair. -/
theorem comp_sLEquiv_comp {f₁ f₂ f₁' f₂' : BinQF} (h₁ : f₁.IsPrimitive) (h₂ : f₂.IsPrimitive)
    (h₁' : f₁'.IsPrimitive) (h₂' : f₂'.IsPrimitive) (hD0 : f₁.disc ≠ 0)
    (e₁ : SLEquiv f₁ f₁') (e₂ : SLEquiv f₂ f₂') (hc : Concordant f₁ f₂) (hc' : Concordant f₁' f₂') :
    SLEquiv (comp f₁ f₂) (comp f₁' f₂') := by
  have ha₁ : f₁.a ≠ 0 := left_ne_zero_of_mul hc.1
  have ha₂ : f₂.a ≠ 0 := right_ne_zero_of_mul hc.1
  have ha₁' : f₁'.a ≠ 0 := left_ne_zero_of_mul hc'.1
  have ha₂' : f₂'.a ≠ 0 := right_ne_zero_of_mul hc'.1
  have hM : f₁.a * f₂.a * f₁'.a * f₂'.a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₁') ha₂'
  have hD : f₁.disc = f₂.disc := hc.2.2.1
  obtain ⟨g₁, g₂, d₁, d₂, hcg, hgcop, hgM⟩ := exists_concordant h₁ h₂ hD hD0 hM
  have k₁ : SLEquiv f₁' g₁ := e₁.symm.trans d₁
  have k₂ : SLEquiv f₂' g₂ := e₂.symm.trans d₂
  have r1 := comp_sLEquiv_comp_of_coprime d₁ d₂ hc hcg hgcop
    (hgM.symm.of_isCoprime_of_dvd_left
      (show f₁.a * f₂.a ∣ f₁.a * f₂.a * f₁'.a * f₂'.a from ⟨f₁'.a * f₂'.a, by ring⟩))
  have r2 := comp_sLEquiv_comp_of_coprime k₁ k₂ hc' hcg hgcop
    (hgM.symm.of_isCoprime_of_dvd_left
      (show f₁'.a * f₂'.a ∣ f₁.a * f₂.a * f₁'.a * f₂'.a from ⟨f₁.a * f₂.a, by ring⟩))
  exact r1.trans r2.symm

end QuadFormsKB.Composition
