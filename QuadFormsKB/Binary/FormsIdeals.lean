import QuadFormsKB.Binary.QuadraticField
import QuadFormsKB.Defs.Binary
import QuadFormsKB.Equiv.Binary

/-!
# Binary quadratic forms and ideals of a quadratic order

Let $R = \mathbb{Z}[\omega]$ (`QOrder D`), $\omega^2 = a_D + b_D\omega$, $\omega = (b_D + \sqrt D)/2$. For an integral
binary form $f = (a, b, c)$ of discriminant $D$ put $k_f = (b + b_D)/2 \in \mathbb{Z}$ and
$$\mathfrak a_f = \mathbb{Z}a + \mathbb{Z}(k_f - \omega) = \mathbb{Z}a + \mathbb{Z}\,\tfrac{b - \sqrt D}{2},$$
an ideal of $R$ (`formIdeal`; Cox writes $[a, (-b + \sqrt D)/2]$, the same lattice). Conversely a $\mathbb{Z}$-basis
$(\alpha, \beta)$ of an ideal gives the form $N(x\alpha + y\beta)/\operatorname{odet}(\alpha, \beta)$ (`IsFormOf`), where
$\operatorname{odet}(\alpha, \beta) = (\alpha\bar\beta - \bar\alpha\beta)/\sqrt D$ is the oriented index.

This file: the dictionary between bases and forms (change of basis is $\mathrm{SL}_2(\mathbb{Z})$ / $\mathrm{GL}_2(\mathbb{Z})$
substitution, scaling a basis does not change the form), the key identity $\alpha\,\mathfrak a_g = g_a\,J$ when $(\alpha, \beta)$
is a basis of $J$ with form $g$ (`span_mul_formIdeal`), and the Hermite normal form $J = C\,\mathfrak a_f$ of every
nonzero ideal (`exists_eq_span_mul_formIdeal`).

Sources: Cox, *Primes of the form $x^2 + ny^2$*, §7.B (Thm. 7.7) and §5.C; Buell, *Binary Quadratic Forms*, Ch. 6;
Cohen, *A Course in Computational Algebraic Number Theory*, §5.2.
-/

open QuadraticAlgebra NumberField

set_option linter.unusedSectionVars false

namespace QuadFormsKB

namespace BinQF

/-- **Two binary forms with the same coefficients $a, b, c$ are equal** (the entry below the diagonal of the
upper-triangular coefficient matrix is $0$ for both). -/
theorem ext_abc {f g : BinQF} (ha : f.a = g.a) (hb : f.b = g.b) (hc : f.c = g.c) : f = g := by
  have h10 : f.coeff 1 0 = 0 := f.upper (show id (0 : Fin 2) < id 1 by decide)
  have h10' : g.coeff 1 0 = 0 := g.upper (show id (0 : Fin 2) < id 1 by decide)
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · simp [h10, h10']
  · exact hc

/-- **A binary form is determined by its values** at integer points. -/
theorem ext_eval {f g : BinQF} (h : ∀ x y : ℤ, f.eval x y = g.eval x y) : f = g := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [eval_eq] at h1 h2 h3
  refine ext_abc ?_ ?_ ?_ <;> linarith

/-- **Primitive form:** $\gcd(a, b, c) = 1$, i.e. the only common divisors of the coefficients are units. -/
def IsPrimitive (f : BinQF) : Prop := ∀ d : ℤ, d ∣ f.a → d ∣ f.b → d ∣ f.c → IsUnit d

/-- **The negative** $-f = (-a, -b, -c)$ (`a_neg`, `b_neg`, `c_neg`). -/
def neg (f : BinQF) : BinQF := mk (-f.a) (-f.b) (-f.c)

@[simp] theorem a_neg (f : BinQF) : f.neg.a = -f.a := by simp [neg]
@[simp] theorem b_neg (f : BinQF) : f.neg.b = -f.b := by simp [neg]
@[simp] theorem c_neg (f : BinQF) : f.neg.c = -f.c := by simp [neg]

@[simp] theorem a_subst (p q r s : ℤ) (f : BinQF) :
    (subst p q r s f).a = f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2 := by simp [subst]
@[simp] theorem b_subst (p q r s : ℤ) (f : BinQF) :
    (subst p q r s f).b = 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s := by simp [subst]
@[simp] theorem c_subst (p q r s : ℤ) (f : BinQF) :
    (subst p q r s f).c = f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2 := by simp [subst]

end BinQF

namespace Binary

open BinQF

variable {D : ℤ}

/-! ### The oriented index and the form of a basis -/

/-- **The oriented index** of $\alpha, \beta \in \mathbb{Z}[\omega]$:
$$\operatorname{odet}(\alpha, \beta) = \alpha_1\beta_0 - \alpha_0\beta_1 = \frac{\alpha\bar\beta - \bar\alpha\beta}{\sqrt D}$$
for $\alpha = \alpha_0 + \alpha_1\omega$, $\beta = \beta_0 + \beta_1\omega$ (0-based coordinates `re`, `im`). Up to sign it is
the index $[\mathbb{Z}[\omega] : \mathbb{Z}\alpha + \mathbb{Z}\beta]$; its sign is the orientation of the basis (Cox's
condition that $\beta/\alpha$ lies in the upper half plane, for $D < 0$, is $\operatorname{odet}(\alpha, \beta) > 0$ in Cox's
ordering $(\alpha, \beta) = (a, (-b+\sqrt D)/2)$ up to the reflection $y \mapsto -y$ used here). -/
def odet (α β : QOrder D) : ℤ := α.im * β.re - α.re * β.im

/-- **Change of basis multiplies the oriented index by the determinant:**
$\operatorname{odet}(p\alpha + r\beta,\ q\alpha + s\beta) = (ps - qr)\operatorname{odet}(\alpha, \beta)$. -/
theorem odet_comb (α β : QOrder D) (p q r s : ℤ) :
    odet (p • α + r • β) (q • α + s • β) = (p * s - q * r) * odet α β := by
  simp only [odet, re_add, im_add, re_smul, im_smul, smul_eq_mul]; ring

/-- **Scaling a basis by $\lambda$ multiplies the oriented index by $N(\lambda)$:**
$\operatorname{odet}(\lambda\alpha, \lambda\beta) = N(\lambda)\operatorname{odet}(\alpha, \beta)$. -/
theorem odet_mul (l α β : QOrder D) : odet (l * α) (l * β) = norm l * odet α β := by
  simp only [odet, re_mul, im_mul, norm_def]; ring

/-- **$f$ is the form of the pair $(\alpha, \beta)$:**
$$\operatorname{odet}(\alpha, \beta)\, f(x, y) = N(x\alpha + y\beta) \quad \text{for all } x, y \in \mathbb{Z},$$
i.e. $f(x, y) = N(x\alpha + y\beta)/\operatorname{odet}(\alpha, \beta)$ when $\operatorname{odet}(\alpha, \beta) \neq 0$. For a
$\mathbb{Z}$-basis of an ideal $\mathfrak a$, $|\operatorname{odet}(\alpha, \beta)| = N\mathfrak a$, so this is Cox's
$f(x, y) = N(x\alpha + y\beta)/N(\mathfrak a)$ for a positively oriented basis (Cox, Thm. 7.7 and its proof, with the
reflection $y \mapsto -y$ of Cox's $N(\alpha x - \beta y)$). Here $N$ is the norm of $\mathbb{Z}[\omega]$,
$N(u + v\omega) = u^2 + b_D uv - a_D v^2$. -/
@[kb "cox2013" "§7.B, Thm. 7.7 and its proof"]
def IsFormOf (f : BinQF) (α β : QOrder D) : Prop :=
  ∀ x y : ℤ, odet α β * f.eval x y = norm (x • α + y • β)

/-- **Coefficients of the form of a basis:** $n a = N\alpha$, $n c = N\beta$ and $n b = N(\alpha + \beta) - N\alpha - N\beta$,
$n = \operatorname{odet}(\alpha, \beta)$. -/
theorem IsFormOf.coeffs {f : BinQF} {α β : QOrder D} (h : IsFormOf f α β) :
    odet α β * f.a = norm α ∧ odet α β * f.c = norm β ∧
      odet α β * (f.a + f.b + f.c) = norm (α + β) := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  simp only [eval_eq, one_smul, zero_smul, add_zero, zero_add] at h1 h2 h3
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- **The form of a basis is unique** when $\operatorname{odet}(\alpha, \beta) \neq 0$. -/
theorem IsFormOf.unique {f g : BinQF} {α β : QOrder D} (hf : IsFormOf f α β) (hg : IsFormOf g α β)
    (hn : odet α β ≠ 0) : f = g :=
  ext_eval fun x y => mul_left_cancel₀ hn ((hf x y).trans (hg x y).symm)

/-- **Scaling a basis does not change its form:** if $f$ is the form of $(\alpha, \beta)$ then it is the form of
$(\lambda\alpha, \lambda\beta)$ for every $\lambda \in \mathbb{Z}[\omega]$ (both $N$ and $\operatorname{odet}$ scale by $N(\lambda)$).
This is the step "$\mathfrak a \sim \lambda\mathfrak a$ give the same form" of Cox, Thm. 7.7; the basis
$(\lambda\alpha, \lambda\beta)$ is positively oriented iff $N(\lambda)\operatorname{odet}(\alpha, \beta) > 0$. -/
@[kb "cox2013" "§7.B, proof of Thm. 7.7"]
theorem IsFormOf.mul {f : BinQF} {α β : QOrder D} (h : IsFormOf f α β) (l : QOrder D) :
    IsFormOf f (l * α) (l * β) := by
  intro x y
  rw [odet_mul, mul_assoc, h x y, ← map_mul]
  congr 1
  rw [mul_add, mul_smul_comm, mul_smul_comm]

/-- **Change of basis acts by substitution:** if $f$ is the form of $(\alpha, \beta)$ and
$g = \begin{pmatrix} p & q \\ r & s\end{pmatrix}$ has $\det g = ps - qr = \pm 1$, then the form of the basis
$(p\alpha + r\beta,\ q\alpha + s\beta)$ is $\det(g) \cdot (f \circ g)$, $(f\circ g)(x, y) = f(px + qy, rx + sy)$
(`BinQF.subst`). For $\det g = 1$ this is $f \circ g$ (`IsFormOf.subst`). -/
@[kb "cox2013" "§7.B, proof of Thm. 7.7"]
theorem IsFormOf.subst_det {f : BinQF} {α β : QOrder D} (h : IsFormOf f α β) {p q r s : ℤ}
    (hd : (p * s - q * r) ^ 2 = 1) :
    IsFormOf (mk ((p * s - q * r) * (subst p q r s f).a) ((p * s - q * r) * (subst p q r s f).b)
      ((p * s - q * r) * (subst p q r s f).c)) (p • α + r • β) (q • α + s • β) := by
  intro x y
  rw [odet_comb]
  have hx := h (p * x + q * y) (r * x + s * y)
  have he : x • (p • α + r • β) + y • (q • α + s • β) = (p * x + q * y) • α + (r * x + s * y) • β := by
    ext <;> simp <;> ring
  rw [he, ← hx]
  have := eval_subst p q r s f x y
  simp only [eval_eq, a_mk, b_mk, c_mk] at this ⊢
  rw [← this]
  linear_combination (odet α β * ((subst p q r s f).a * x ^ 2 + (subst p q r s f).b * x * y +
    (subst p q r s f).c * y ^ 2)) * hd

/-- **Proper change of basis:** if $f$ is the form of $(\alpha, \beta)$ and $ps - qr = 1$, then $f \circ g$ is the form of
$(p\alpha + r\beta,\ q\alpha + s\beta)$. -/
theorem IsFormOf.subst {f : BinQF} {α β : QOrder D} (h : IsFormOf f α β) {p q r s : ℤ}
    (hd : p * s - q * r = 1) : IsFormOf (BinQF.subst p q r s f) (p • α + r • β) (q • α + s • β) := by
  have := h.subst_det (p := p) (q := q) (r := r) (s := s) (by rw [hd]; norm_num)
  rw [hd] at this
  convert this using 1
  exact ext_abc (by simp) (by simp) (by simp)

/-! ### The ideal of a form -/

/-- **The integer $k_f = (b + b_D)/2$** of a form $f = (a, b, c)$ of discriminant $D$ ($b \equiv D \equiv b_D \pmod 2$,
`two_mul_kf`), so that $k_f - \omega = (b - \sqrt D)/2$. -/
def kf (D : ℤ) (f : BinQF) : ℤ := (f.b + qb D) / 2

/-- **The first basis vector** $a$ of $\mathfrak a_f$. -/
def fα (D : ℤ) (f : BinQF) : QOrder D := ⟨f.a, 0⟩

/-- **The second basis vector** $k_f - \omega = (b - \sqrt D)/2$ of $\mathfrak a_f$. -/
def fβ (D : ℤ) (f : BinQF) : QOrder D := ⟨kf D f, -1⟩

/-- **The ideal of a form** $f = (a, b, c)$:
$$\mathfrak a_f = (a,\ k_f - \omega) = \mathbb{Z}a + \mathbb{Z}\,\tfrac{b - \sqrt D}{2} \subseteq \mathbb{Z}[\omega],$$
as the ideal generated by $a$ and $k_f - \omega$. For $\operatorname{disc} f = D$ it is exactly the lattice
$\mathbb{Z}a + \mathbb{Z}(k_f - \omega)$ (`mem_formIdeal_iff_exists`), of norm $|a|$; it equals Cox's
$[a, (-b + \sqrt D)/2]$ (the second generator differs by sign). Source: Cox, Thm. 7.7 (ii) and Lemma 7.5;
Buell, Ch. 6. -/
@[kb "cox2013" "§7.B, Thm. 7.7"]
def formIdeal (D : ℤ) (f : BinQF) : Ideal (QOrder D) := Ideal.span {fα D f, fβ D f}

section disc
variable {f : BinQF} (hf : f.disc = D)
include hf

theorem disc_mod_four_of : D % 4 = 0 ∨ D % 4 = 1 := hf ▸ disc_mod_four f

/-- $D = b_D^2 + 4a_D$ for $D = \operatorname{disc} f$. -/
theorem qb_sq_add : qb D ^ 2 + 4 * qa D = D := by
  have := discr_qa_qb (disc_mod_four_of hf)
  rwa [discr_def] at this

/-- $2k_f = b + b_D$. -/
theorem two_mul_kf : 2 * kf D f = f.b + qb D := by
  have hD := disc_mod_four_of hf
  unfold kf qb
  rcases Int.even_or_odd f.b with ⟨m, hm⟩ | ⟨m, hm⟩
  · have e : D = 4 * (m * m - f.a * f.c) := by rw [← hf, disc, hm]; ring
    generalize m * m - f.a * f.c = t at e
    omega
  · have e : D = 4 * (m * m + m - f.a * f.c) + 1 := by rw [← hf, disc, hm]; ring
    generalize m * m + m - f.a * f.c = t at e
    omega

/-- $ac = k_f^2 - b_D k_f - a_D = N(k_f - \omega)$. -/
theorem a_mul_c : f.a * f.c = kf D f ^ 2 - qb D * kf D f - qa D := by
  have hk := two_mul_kf hf
  have hq := qb_sq_add hf
  have h4 : 4 * (f.a * f.c) = 4 * (kf D f ^ 2 - qb D * kf D f - qa D) := by
    have : f.b = 2 * kf D f - qb D := by linarith
    have hf' : (2 * kf D f - qb D) ^ 2 - 4 * f.a * f.c = D := by rw [← this]; exact hf
    linear_combination hq - hf'
  exact mul_left_cancel₀ (by norm_num) h4

/-- **Membership in $\mathfrak a_f$:** $u + v\omega \in \mathfrak a_f \iff a \mid u + k_f v$ (for $\operatorname{disc} f = D$).
The set on the right is closed under multiplication by $\omega$ because $a \mid N(k_f - \omega) = ac$. -/
theorem mem_formIdeal (z : QOrder D) : z ∈ formIdeal D f ↔ f.a ∣ z.re + kf D f * z.im := by
  have hac := a_mul_c hf
  constructor
  · intro hz
    refine Submodule.span_induction (p := fun z _ => f.a ∣ z.re + kf D f * z.im) ?_ ?_ ?_ ?_ hz
    · rintro w (rfl | rfl)
      · simp [fα]
      · simp [fβ]
    · simp
    · intro x y _ _ hx hy
      simp only [re_add, im_add]
      have := dvd_add hx hy
      convert this using 1; ring
    · intro r x _ hx
      obtain ⟨t, ht⟩ := hx
      simp only [smul_eq_mul, re_mul, im_mul]
      refine ⟨r.re * t + r.im * (kf D f * t) - r.im * x.im * f.c, ?_⟩
      have hre : x.re = f.a * t - kf D f * x.im := by linarith
      rw [hre]
      linear_combination (r.im * x.im) * hac
  · rintro ⟨t, ht⟩
    have hz : z = t • fα D f + (-z.im) • fβ D f := by
      ext <;> simp [fα, fβ]
      linarith
    rw [hz]
    exact add_mem (zsmul_mem (Ideal.subset_span (by simp)) _)
      (zsmul_mem (Ideal.subset_span (by simp)) _)

/-- **$\mathfrak a_f$ is the lattice $\mathbb{Z}a + \mathbb{Z}(k_f - \omega)$** (for $\operatorname{disc} f = D$). -/
theorem mem_formIdeal_iff_exists (z : QOrder D) :
    z ∈ formIdeal D f ↔ ∃ x y : ℤ, z = x • fα D f + y • fβ D f := by
  rw [mem_formIdeal hf]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, -z.im, by ext <;> simp [fα, fβ]; linarith⟩
  · rintro ⟨x, y, rfl⟩
    exact ⟨x, by simp [fα, fβ]; ring⟩

/-- **The oriented index of the basis $(a, k_f - \omega)$ is $a$.** -/
theorem odet_fα_fβ : odet (fα D f) (fβ D f) = f.a := by simp [odet, fα, fβ]

/-- **$f$ is the form of the basis $(a, k_f - \omega)$ of $\mathfrak a_f$:**
$a\,f(x, y) = N(xa + y(k_f - \omega))$ (for $\operatorname{disc} f = D$). Source: Cox, Thm. 7.7, proof. -/
@[kb "cox2013" "§7.B, proof of Thm. 7.7"]
theorem isFormOf_formIdeal : IsFormOf f (fα D f) (fβ D f) := by
  intro x y
  have hk := two_mul_kf hf
  have hac := a_mul_c hf
  rw [odet_fα_fβ hf, eval_eq]
  simp only [fα, fβ, norm_def, re_add, im_add, re_smul, im_smul, smul_eq_mul]
  have hb : f.b = 2 * kf D f - qb D := by linarith
  rw [hb]
  linear_combination (y ^ 2) * hac

end disc

/-! ### The key identity $\alpha\,\mathfrak a_g = g_a J$ -/

/-- **$\beta\bar\alpha = \operatorname{odet}(\alpha, \beta)\,(k_g - \omega)$** when $g$ (of discriminant $D$) is the form of
$(\alpha, \beta)$: the imaginary part of $\beta\bar\alpha$ is $-\operatorname{odet}(\alpha, \beta)$ identically, and its trace is
$N(\alpha + \beta) - N\alpha - N\beta = \operatorname{odet}(\alpha, \beta)\, b$. -/
theorem mul_star_eq {g : BinQF} (hg : g.disc = D) {α β : QOrder D} (h : IsFormOf g α β) :
    β * star α = odet α β • fβ D g := by
  obtain ⟨h1, h2, h3⟩ := h.coeffs
  have hk := two_mul_kf hg
  simp only [norm_def, re_add, im_add] at h1 h2 h3
  ext
  · simp only [re_mul, re_star, im_star, re_smul, smul_eq_mul, fβ]
    have : 2 * (β.re * (α.re + qb D * α.im) + qa D * β.im * -α.im) = 2 * (odet α β * kf D g) := by
      simp only [odet] at h1 h2 h3 ⊢
      linear_combination -(h3 - h1 - h2) - (α.im * β.re - α.re * β.im) * hk
    linarith
  · simp only [im_mul, re_star, im_star, im_smul, smul_eq_mul, fβ, odet]; ring

/-- **$\alpha\,(k_g - \omega) = g_a\,\beta$** when $g$ (with $g_a \neq 0$, $\operatorname{disc} g = D$, $D$ fundamental) is the
form of $(\alpha, \beta)$ with $\operatorname{odet}(\alpha, \beta) \neq 0$: multiply by $\bar\alpha$ and use
$\alpha\bar\alpha = N\alpha = \operatorname{odet}(\alpha,\beta)\, g_a$ and `mul_star_eq`; cancel $\bar\alpha \neq 0$. In other words
$\beta/\alpha = (k_g - \omega)/g_a$ is the root $\tau$ of $g(\tau, 1) = 0$ selected by the orientation. -/
theorem mul_fβ_eq [IsQuadDisc D] {g : BinQF} (hg : g.disc = D) (ha : g.a ≠ 0) {α β : QOrder D}
    (h : IsFormOf g α β) (hn : odet α β ≠ 0) : α * fβ D g = (g.a : QOrder D) * β := by
  obtain ⟨h1, -, -⟩ := h.coeffs
  have hs := mul_star_eq hg h
  have hα : star α ≠ 0 := by
    intro h0
    have : norm α = 0 := by rw [← QuadraticAlgebra.norm_star, h0, QuadraticAlgebra.norm_zero]
    rw [← h1] at this
    exact mul_ne_zero hn ha this
  refine mul_left_cancel₀ hα ?_
  have hN : star α * α = ((norm α : ℤ) : QOrder D) := by
    rw [mul_comm, ← algebraMap_norm_eq_mul_star]; rfl
  calc star α * (α * fβ D g) = (star α * α) * fβ D g := by ring
    _ = ((odet α β * g.a : ℤ) : QOrder D) * fβ D g := by rw [hN, h1]
    _ = (g.a : QOrder D) * (β * star α) := by
      rw [hs, zsmul_eq_mul]; push_cast; ring
    _ = star α * ((g.a : QOrder D) * β) := by ring

/-- **The key identity** (Cox, Thm. 7.7): if $J$ is an ideal with $\mathbb{Z}$-basis $(\alpha, \beta)$,
$\operatorname{odet}(\alpha, \beta) \neq 0$, and $g$ (of discriminant $D$, $g_a \neq 0$) is the form of $(\alpha, \beta)$, then
$$(\alpha)\,\mathfrak a_g = (g_a)\, J .$$
In particular $J$ and $\mathfrak a_g$ have the same ideal class (`mk0_formIdeal_eq`). -/
@[kb "cox2013" "§7.B, Thm. 7.7"]
theorem span_mul_formIdeal [IsQuadDisc D] {g : BinQF} (hg : g.disc = D) (ha : g.a ≠ 0) {α β : QOrder D}
    (h : IsFormOf g α β) (hn : odet α β ≠ 0) (J : Ideal (QOrder D))
    (hJ : ∀ z, z ∈ J ↔ ∃ x y : ℤ, z = x • α + y • β) :
    Ideal.span {α} * formIdeal D g = Ideal.span {(g.a : QOrder D)} * J := by
  have key := mul_fβ_eq hg ha h hn
  ext z
  rw [Ideal.mem_span_singleton_mul, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, y, rfl⟩ := (mem_formIdeal_iff_exists hg w).mp hw
    refine ⟨x • α + y • β, (hJ _).mpr ⟨x, y, rfl⟩, ?_⟩
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm, ← key]
    congr 1
    simp only [fα]
    congr 1
    ext <;> simp [mul_comm]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, y, rfl⟩ := (hJ w).mp hw
    refine ⟨x • fα D g + y • fβ D g, (mem_formIdeal_iff_exists hg _).mpr ⟨x, y, rfl⟩, ?_⟩
    rw [mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_smul_comm, mul_smul_comm, key]
    congr 1
    simp only [fα]
    congr 1
    ext <;> simp [mul_comm]

/-! ### Two bases of one lattice -/

/-- **Two $\mathbb{Z}$-bases of the same lattice differ by an element of $\mathrm{GL}_2(\mathbb{Z})$:** if
$\mathbb{Z}\alpha + \mathbb{Z}\beta = \mathbb{Z}\alpha' + \mathbb{Z}\beta'$ and $\operatorname{odet}(\alpha, \beta) \neq 0$, then
$\alpha' = p\alpha + r\beta$, $\beta' = q\alpha + s\beta$ with $ps - qr = \pm 1$ and
$\operatorname{odet}(\alpha', \beta') = (ps - qr)\operatorname{odet}(\alpha, \beta)$. -/
theorem exists_basis_change {α β α' β' : QOrder D}
    (h : ∀ z, (∃ x y : ℤ, z = x • α + y • β) ↔ (∃ x y : ℤ, z = x • α' + y • β'))
    (hn : odet α β ≠ 0) :
    ∃ p q r s : ℤ, α' = p • α + r • β ∧ β' = q • α + s • β ∧
      odet α' β' = (p * s - q * r) * odet α β ∧ (p * s - q * r = 1 ∨ p * s - q * r = -1) := by
  obtain ⟨p, r, hα'⟩ := (h α').mpr ⟨1, 0, by simp⟩
  obtain ⟨q, s, hβ'⟩ := (h β').mpr ⟨0, 1, by simp⟩
  obtain ⟨p', r', hα⟩ := (h α).mp ⟨1, 0, by simp⟩
  obtain ⟨q', s', hβ⟩ := (h β).mp ⟨0, 1, by simp⟩
  have e1 : odet α' β' = (p * s - q * r) * odet α β := by rw [hα', hβ', odet_comb]
  have e2 : odet α β = (p' * s' - q' * r') * odet α' β' := by
    have : odet α β = odet (p' • α' + r' • β') (q' • α' + s' • β') := by rw [← hα, ← hβ]
    rw [this, odet_comb]
  have hd : (p * s - q * r) * (p' * s' - q' * r') = 1 := by
    refine mul_left_cancel₀ hn ?_
    rw [e1] at e2
    linear_combination -e2
  exact ⟨p, q, r, s, hα', hβ', e1, Int.eq_one_or_neg_one_of_mul_eq_one hd⟩

/-- **Two positively oriented bases of the same lattice differ by an element of $\mathrm{SL}_2(\mathbb{Z})$**, so their
forms are properly ($\mathrm{SL}_2(\mathbb{Z})$-) equivalent: if $f$ is the form of $(\alpha, \beta)$, the form of
$(\alpha', \beta')$ is $f \circ g$ with $\det g = 1$. This is "$f_{\mathfrak a}$ is well defined up to proper equivalence"
(Cox, Thm. 7.7, proof). -/
@[kb "cox2013" "§7.B, proof of Thm. 7.7"]
theorem IsFormOf.exists_subst_of_lattice_eq {f : BinQF} {α β α' β' : QOrder D} (hf : IsFormOf f α β)
    (h : ∀ z, (∃ x y : ℤ, z = x • α + y • β) ↔ (∃ x y : ℤ, z = x • α' + y • β'))
    (hn : 0 < odet α β) (hn' : 0 < odet α' β') :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ IsFormOf (BinQF.subst p q r s f) α' β' := by
  obtain ⟨p, q, r, s, rfl, rfl, e, hd⟩ := exists_basis_change h hn.ne'
  have hd1 : p * s - q * r = 1 := by
    rcases hd with hd | hd
    · exact hd
    · rw [e, hd] at hn'; linarith
  exact ⟨p, q, r, s, hd1, hf.subst hd1⟩

/-! ### The Hermite normal form of an ideal -/

variable [IsQuadDisc D]

/-- $\mathbb{Z}[\omega]$ is a Dedekind domain (it is the ring of integers of $K_D$, `isIntegralClosure`). -/
instance : IsDedekindDomain (QOrder D) :=
  IsIntegralClosure.isDedekindDomain ℤ ℚ (QField D) (QOrder D)

omit [IsQuadDisc D] in
/-- The norm of a nonzero element of $\mathbb{Z}[\omega]$ is nonzero. -/
theorem norm_ne_zero [IsQuadDisc D] {z : QOrder D} (hz : z ≠ 0) : norm z ≠ 0 := by
  intro h
  have : z * star z = 0 := by
    rw [← algebraMap_norm_eq_mul_star, h, map_zero]
  rcases mul_eq_zero.mp this with h | h
  · exact hz h
  · exact hz (star_eq_zero.mp h)

/-- **Hermite normal form of an ideal:** every nonzero ideal $J$ of $\mathbb{Z}[\omega]$ is $J = C\,\mathfrak a_f$ for an integer
$C > 0$ and a form $f$ of discriminant $D$ with $a > 0$. *Proof:* $J \cap \mathbb{Z} = A\mathbb{Z}$ and
$\{\operatorname{im} z : z \in J\} = C\mathbb{Z}$ with $A, C > 0$; pick $\beta_0 \in J$ with $\operatorname{im}\beta_0 = C$. Then
$J = \mathbb{Z}A + \mathbb{Z}\beta_0$, and $\omega A, \omega\beta_0 \in J$ force $C \mid A$, $C \mid \operatorname{re}\beta_0$ and
$a = A/C \mid N(k - \omega)$, $k = -\operatorname{re}\beta_0 / C$. Source: Buell, Ch. 6; Cohen, §5.2.2 (HNF of ideals). -/
@[kb "cohen1993" "§5.2 [unverified locator]"]
theorem exists_eq_span_mul_formIdeal (J : Ideal (QOrder D)) (hJ : J ≠ ⊥) :
    ∃ (C : ℤ) (f : BinQF), 0 < C ∧ f.disc = D ∧ 0 < f.a ∧
      J = Ideal.span {(C : QOrder D)} * formIdeal D f := by
  classical
  -- `J ∩ ℤ = A₀ ℤ`
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℤ, ∀ u : ℤ, (u : QOrder D) ∈ J ↔ A₀ ∣ u := by
    obtain ⟨A₀, hA⟩ := Submodule.IsPrincipal.principal (J.comap (Int.castRingHom (QOrder D)))
    refine ⟨A₀, fun u => ?_⟩
    have := (Submodule.ext_iff.mp hA) u
    rw [Ideal.mem_comap, eq_intCast] at this
    rw [this]
    exact Ideal.mem_span_singleton
  -- `im J = C₀ ℤ`
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℤ, ∀ v : ℤ, (∃ z ∈ J, z.im = v) ↔ C₀ ∣ v := by
    obtain ⟨C₀, hC⟩ := Submodule.IsPrincipal.principal
      ((J.restrictScalars ℤ).map (imₗ (qa D) (qb D)))
    refine ⟨C₀, fun v => ?_⟩
    have := (Submodule.ext_iff.mp hC) v
    rw [Submodule.mem_map] at this
    rw [show (∃ z ∈ J, z.im = v) ↔ ∃ y ∈ J.restrictScalars ℤ, imₗ (qa D) (qb D) y = v from Iff.rfl, this]
    exact Ideal.mem_span_singleton
  -- `A₀ ≠ 0`
  obtain ⟨z, hzJ, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hNz : ((norm z : ℤ) : QOrder D) ∈ J := by
    have : ((norm z : ℤ) : QOrder D) = z * star z := algebraMap_norm_eq_mul_star z
    rw [this]; exact J.mul_mem_right _ hzJ
  have hA0 : A₀ ≠ 0 := by
    rintro rfl
    exact norm_ne_zero hz0 (zero_dvd_iff.mp ((hA₀ _).mp hNz))
  -- `C₀ ∣ A₀` and `C₀ ≠ 0`
  have hωA : ω * (A₀ : QOrder D) ∈ J := J.mul_mem_left _ ((hA₀ A₀).mpr dvd_rfl)
  have hCA : C₀ ∣ A₀ := (hC₀ A₀).mp ⟨_, hωA, by simp⟩
  have hC0 : C₀ ≠ 0 := by rintro rfl; exact hA0 (zero_dvd_iff.mp hCA)
  -- normalize signs
  set A := |A₀| with hAdef
  set C := |C₀| with hCdef
  have hA : ∀ u : ℤ, (u : QOrder D) ∈ J ↔ A ∣ u := fun u => (hA₀ u).trans (abs_dvd _ _).symm
  have hC : ∀ v : ℤ, (∃ z ∈ J, z.im = v) ↔ C ∣ v := fun v => (hC₀ v).trans (abs_dvd _ _).symm
  have hApos : 0 < A := abs_pos.mpr hA0
  have hCpos : 0 < C := abs_pos.mpr hC0
  have hCA' : C ∣ A := (abs_dvd_abs _ _).mpr hCA
  -- `β₀ ∈ J` with `im β₀ = C`
  obtain ⟨β₀, hβ₀J, hβ₀⟩ := (hC C).mpr dvd_rfl
  have hωβ : ω * β₀ ∈ J := J.mul_mem_left _ hβ₀J
  have hCre : C ∣ β₀.re := by
    have := (hC _).mp ⟨_, hωβ, rfl⟩
    simp only [im_mul, re_omega, im_omega, hβ₀] at this
    have h2 : C ∣ qb D * C := dvd_mul_left _ _
    have := (Int.dvd_add_left h2).mp (by simpa [add_comm] using this)
    exact this
  obtain ⟨a, ha⟩ := hCA'
  obtain ⟨m, hm⟩ := hCre
  set k := -m with hk
  -- membership in `J`
  have hmem : ∀ w : QOrder D, w ∈ J ↔ C ∣ w.im ∧ A ∣ w.re + k * w.im := by
    intro w
    constructor
    · intro hw
      obtain ⟨t, ht⟩ := (hC _).mp ⟨w, hw, rfl⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      have h1 : w - t • β₀ ∈ J := J.sub_mem hw (zsmul_mem hβ₀J t)
      have h2 : w - t • β₀ = (((w - t • β₀).re : ℤ) : QOrder D) := by
        ext
        · simp
        · simp [ht, hβ₀]; ring
      rw [h2] at h1
      have := (hA _).mp h1
      simp only [re_sub, re_smul, smul_eq_mul, hm] at this
      convert this using 1
      rw [ht, hk]; ring
    · rintro ⟨⟨t, ht⟩, hdiv⟩
      have h2 : w = t • β₀ + (((w - t • β₀).re : ℤ) : QOrder D) := by
        ext
        · simp
        · simp [ht, hβ₀]; ring
      rw [h2]
      refine J.add_mem (zsmul_mem hβ₀J t) ((hA _).mpr ?_)
      simp only [re_sub, re_smul, smul_eq_mul, hm]
      convert hdiv using 1
      rw [ht, hk]; ring
  have hapos : 0 < a := by
    rw [ha] at hApos; exact pos_of_mul_pos_right hApos hCpos.le
  -- `a ∣ N(k - ω)`
  have hdivN : a ∣ k ^ 2 - qb D * k - qa D := by
    have := ((hmem _).mp hωβ).2
    simp only [re_mul, im_mul, re_omega, im_omega, hβ₀, hm, ha] at this
    obtain ⟨t, ht⟩ := this
    refine ⟨-t, mul_left_cancel₀ hCpos.ne' ?_⟩
    rw [hk]
    linear_combination -ht
  obtain ⟨c, hc⟩ := hdivN
  set f : BinQF := mk a (2 * k - qb D) c with hfdef
  have hfD : f.disc = D := by
    have hq := discr_qa_qb (IsQuadDisc.fund (D := D)).1
    rw [discr_def] at hq
    simp only [hfdef, disc, a_mk, b_mk, c_mk]
    linear_combination hq + 4 * hc
  have hkf : kf D f = k := by
    simp only [kf, hfdef, b_mk]; omega
  refine ⟨C, f, hCpos, hfD, by simpa [hfdef] using hapos, ?_⟩
  ext w
  rw [Ideal.mem_span_singleton_mul, hmem]
  constructor
  · rintro ⟨⟨t, ht⟩, hdiv⟩
    have hre : C ∣ w.re := by
      have h1 : C ∣ w.re + k * w.im := (Dvd.intro a ha.symm).trans hdiv
      have h2 : C ∣ k * w.im := ⟨k * t, by rw [ht]; ring⟩
      exact (Int.dvd_add_left h2).mp h1
    obtain ⟨u, hu⟩ := hre
    refine ⟨⟨u, t⟩, (mem_formIdeal hfD _).mpr ?_, ?_⟩
    · rw [hkf]
      simp only [hfdef, a_mk]
      rw [ha, hu, ht] at hdiv
      obtain ⟨e, he⟩ := hdiv
      exact ⟨e, mul_left_cancel₀ hCpos.ne' (by linear_combination he)⟩
    · ext <;> simp [hu, ht]
  · rintro ⟨v, hv, rfl⟩
    rw [mem_formIdeal hfD, hkf] at hv
    simp only [hfdef, a_mk] at hv
    obtain ⟨e, he⟩ := hv
    refine ⟨⟨v.im, by simp⟩, ⟨e, ?_⟩⟩
    simp only [re_mul, im_mul, re_intCast, im_intCast, ha]
    linear_combination C * he

omit [IsQuadDisc D] in
/-- **A basis of $(x)\,\mathfrak a_f$** is $(x a,\ x(k_f - \omega))$ (for $\operatorname{disc} f = D$). -/
theorem mem_span_mul_formIdeal_iff {f : BinQF} (hf : f.disc = D) (x z : QOrder D) :
    z ∈ Ideal.span {x} * formIdeal D f ↔ ∃ u v : ℤ, z = u • (x * fα D f) + v • (x * fβ D f) := by
  rw [Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, v, rfl⟩ := (mem_formIdeal_iff_exists hf w).mp hw
    exact ⟨u, v, by rw [mul_add, mul_smul_comm, mul_smul_comm]⟩
  · rintro ⟨u, v, rfl⟩
    exact ⟨u • fα D f + v • fβ D f, (mem_formIdeal_iff_exists hf _).mpr ⟨u, v, rfl⟩,
      by rw [mul_add, mul_smul_comm, mul_smul_comm]⟩

omit [IsQuadDisc D] in
/-- $\mathfrak a_f \neq 0$ when $a \neq 0$. -/
theorem formIdeal_ne_bot {f : BinQF} (ha : f.a ≠ 0) : formIdeal D f ≠ ⊥ := by
  intro h
  have : fα D f ∈ formIdeal D f := Ideal.subset_span (by simp)
  rw [h, Ideal.mem_bot] at this
  exact ha (by simpa [fα] using congrArg QuadraticAlgebra.re this)

/-- **Every $\mathbb{Z}$-basis of a nonzero ideal has a form of discriminant $D$** (the map from ideals to forms,
Cox, Thm. 7.7 (i)): if $(\alpha, \beta)$ is a $\mathbb{Z}$-basis of $J \neq 0$ with $\operatorname{odet}(\alpha, \beta) \neq 0$, there is a
(unique, `IsFormOf.unique`) integral form $f$ with $\operatorname{odet}(\alpha, \beta)\,f(x, y) = N(x\alpha + y\beta)$, and
$\operatorname{disc} f = D$. *Proof:* write $J = C\mathfrak a_{f_0}$ (`exists_eq_span_mul_formIdeal`); the form of the basis
$(Ca, C(k - \omega))$ is $f_0$, and $(\alpha, \beta)$ is obtained by a change of basis of determinant $\pm 1$. -/
@[kb "cox2013" "§7.B, Thm. 7.7 (i)"]
theorem exists_isFormOf (J : Ideal (QOrder D)) (hJ : J ≠ ⊥) {α β : QOrder D}
    (hb : ∀ z, z ∈ J ↔ ∃ x y : ℤ, z = x • α + y • β) (hn : odet α β ≠ 0) :
    ∃ f : BinQF, IsFormOf f α β ∧ f.disc = D := by
  obtain ⟨C, f₀, hC, hf₀, ha₀, hJC⟩ := exists_eq_span_mul_formIdeal J hJ
  have h0 : IsFormOf f₀ ((C : QOrder D) * fα D f₀) ((C : QOrder D) * fβ D f₀) :=
    (isFormOf_formIdeal hf₀).mul _
  have hn0 : odet ((C : QOrder D) * fα D f₀) ((C : QOrder D) * fβ D f₀) ≠ 0 := by
    rw [odet_mul, odet_fα_fβ hf₀]
    exact mul_ne_zero (norm_ne_zero (by exact_mod_cast hC.ne')) ha₀.ne'
  have hlat : ∀ z, (∃ x y : ℤ, z = x • ((C : QOrder D) * fα D f₀) + y • ((C : QOrder D) * fβ D f₀)) ↔
      (∃ x y : ℤ, z = x • α + y • β) := fun z => by
    rw [← hb, hJC, mem_span_mul_formIdeal_iff hf₀]
  obtain ⟨p, q, r, s, rfl, rfl, -, hd⟩ := exists_basis_change hlat hn0
  refine ⟨_, h0.subst_det (by rcases hd with hd | hd <;> rw [hd] <;> norm_num), ?_⟩
  simp only [disc, a_mk, b_mk, c_mk]
  have := disc_subst p q r s f₀
  simp only [disc] at this
  have hf₀' : f₀.b ^ 2 - 4 * f₀.a * f₀.c = D := hf₀
  rcases hd with hd | hd <;> rw [hd] at this ⊢ <;> linear_combination this + hf₀'

/-! ### Primitivity -/

omit [IsQuadDisc D] in
/-- **A form of fundamental discriminant is primitive:** if $g = \gcd(a, b, c) > 1$ then $D = g^2 D'$ with
$D' = \operatorname{disc}(f/g) \equiv 0, 1 \pmod 4$, impossible for a fundamental discriminant. -/
@[kb "buell1989" "Ch. 2 [unverified locator]"]
theorem isPrimitive_of_fund {f : BinQF} (hD : Int.IsFundamentalDiscr D) (hf : f.disc = D) :
    f.IsPrimitive := by
  intro d hda hdb hdc
  by_contra hu
  have hd1 : d.natAbs ≠ 1 := fun h => hu (Int.isUnit_iff_natAbs_eq.mpr h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hpd' : (p : ℤ) ∣ d := Int.natCast_dvd.mpr hpd
  obtain ⟨a', ha'⟩ := hpd'.trans hda
  obtain ⟨b', hb'⟩ := hpd'.trans hdb
  obtain ⟨c', hc'⟩ := hpd'.trans hdc
  refine (Int.isFundamentalDiscr_iff_forall_prime.mp hD).2 p hp
    ⟨b' ^ 2 - 4 * a' * c', ?_, ?_⟩
  · rw [← hf, disc, ha', hb', hc']; ring
  · exact disc_mod_four (mk a' b' c') |>.imp (by simp [disc]) (by simp [disc])

/-! ### The conjugate form and the conjugate ideal -/

/-- **The opposite form** $\bar f = (a, -b, c)$, $\bar f(x, y) = f(x, -y)$ (`conjForm_eq_subst`). It corresponds to the
conjugate ideal $\bar{\mathfrak a}_f$, whose class is $[\mathfrak a_f]^{-1}$ (`formIdeal_conj_mul`). -/
def conjForm (f : BinQF) : BinQF := mk f.a (-f.b) f.c

@[simp] theorem a_conjForm (f : BinQF) : (conjForm f).a = f.a := by simp [conjForm]
@[simp] theorem b_conjForm (f : BinQF) : (conjForm f).b = -f.b := by simp [conjForm]
@[simp] theorem c_conjForm (f : BinQF) : (conjForm f).c = f.c := by simp [conjForm]

omit [IsQuadDisc D] in
/-- $\bar f = f \circ \operatorname{diag}(1, -1)$. -/
theorem conjForm_eq_subst (f : BinQF) : conjForm f = BinQF.subst 1 0 0 (-1) f :=
  ext_abc (by simp) (by simp) (by simp)

omit [IsQuadDisc D] in
@[simp] theorem disc_conjForm (f : BinQF) : (conjForm f).disc = f.disc := by simp [disc]

omit [IsQuadDisc D] in
theorem isPrimitive_conjForm {f : BinQF} (hf : f.IsPrimitive) : (conjForm f).IsPrimitive :=
  fun d ha hb hc => hf d (by simpa using ha) (by simpa using (dvd_neg.mpr (by simpa using hb))) (by simpa using hc)

omit [IsQuadDisc D] in
/-- Bézout for a primitive form: $ua + vb + wc = 1$. -/
theorem exists_bezout_of_isPrimitive {f : BinQF} (hf : f.IsPrimitive) :
    ∃ u v w : ℤ, u * f.a + v * f.b + w * f.c = 1 := by
  set g := Int.gcd (Int.gcd f.a f.b : ℤ) f.c
  have hg1 : (g : ℤ) ∣ (Int.gcd f.a f.b : ℤ) := Int.gcd_dvd_left _ _
  have hu : IsUnit (g : ℤ) := hf g ((hg1.trans (Int.gcd_dvd_left _ _))) (hg1.trans (Int.gcd_dvd_right _ _))
    (Int.gcd_dvd_right _ _)
  have hg : (g : ℤ) = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · have : (0 : ℤ) ≤ g := by positivity
      omega
  have e1 := Int.gcd_eq_gcd_ab (Int.gcd f.a f.b : ℤ) f.c
  have e2 := Int.gcd_eq_gcd_ab f.a f.b
  refine ⟨f.a.gcdA f.b * (Int.gcd f.a f.b : ℤ).gcdA f.c, f.b.gcdB f.a * 0 + f.a.gcdB f.b *
    (Int.gcd f.a f.b : ℤ).gcdA f.c, (Int.gcd f.a f.b : ℤ).gcdB f.c, ?_⟩
  rw [← hg]
  change _ = ((Int.gcd (Int.gcd f.a f.b : ℤ) f.c : ℕ) : ℤ)
  rw [e1, e2]
  ring

omit [IsQuadDisc D] in
/-- **$\bar{\mathfrak a}_f\,\mathfrak a_f = (a)$** for a primitive form $f$ of discriminant $D$: the products of generators
are $a^2$, $a(k_f - \omega)$, $a(k_{\bar f} - \omega)$ and $(k_{\bar f} - \omega)(k_f - \omega) = -ac$, all multiples of $a$, and
$a(k_f - \omega) - a(k_{\bar f} - \omega) = ab$, so $\gcd(a, b, c) = 1$ puts $a$ in the product. Source: Cox, Lemma 7.14 [unverified locator]
and its proof; Buell, Ch. 6. -/
@[kb "cox2013" "§7.C, Lemma 7.14 [unverified locator]"]
theorem formIdeal_conj_mul {f : BinQF} (hf : f.disc = D) (hp : f.IsPrimitive) :
    formIdeal D (conjForm f) * formIdeal D f = Ideal.span {(f.a : QOrder D)} := by
  have hk := two_mul_kf hf
  have hk' := two_mul_kf (f := conjForm f) (by rw [disc_conjForm, hf])
  have hac := a_mul_c hf
  simp only [b_conjForm] at hk'
  have hkk : kf D (conjForm f) = qb D - kf D f := by linarith
  simp only [formIdeal]
  rw [Ideal.span_pair_mul_span_pair]
  have hxz : fβ D (conjForm f) * fβ D f = ((-(f.a * f.c) : ℤ) : QOrder D) := by
    ext
    · simp only [fβ, hkk, re_mul, re_intCast, Int.cast_id]; linear_combination hac
    · simp only [fβ, hkk, im_mul, im_intCast]; ring
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact Ideal.mem_span_singleton'.mpr ⟨f.a, by ext <;> simp [fα]⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨fβ D f, by ext <;> simp [fα, fβ, mul_comm]⟩
    · exact Ideal.mem_span_singleton'.mpr ⟨fβ D (conjForm f), by ext <;> simp [fα, fβ, mul_comm]⟩
    · rw [hxz]
      exact Ideal.mem_span_singleton'.mpr ⟨(-f.c : ℤ), by push_cast; ring⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨u, v, w, huvw⟩ := exists_bezout_of_isPrimitive hp
    set S := Ideal.span {fα D (conjForm f) * fα D f, fα D (conjForm f) * fβ D f,
      fβ D (conjForm f) * fα D f, fβ D (conjForm f) * fβ D f}
    have m1 : fα D (conjForm f) * fα D f ∈ S := Ideal.subset_span (by simp)
    have m2 : fα D (conjForm f) * fβ D f ∈ S := Ideal.subset_span (by simp)
    have m3 : fβ D (conjForm f) * fα D f ∈ S := Ideal.subset_span (by simp)
    have m4 : fβ D (conjForm f) * fβ D f ∈ S := Ideal.subset_span (by simp)
    have e : (f.a : QOrder D) = (u : QOrder D) * (fα D (conjForm f) * fα D f) +
        (v : QOrder D) * (fα D (conjForm f) * fβ D f - fβ D (conjForm f) * fα D f) -
        (w : QOrder D) * (fβ D (conjForm f) * fβ D f) := by
      rw [hxz]
      have hb : f.b = 2 * kf D f - qb D := by linarith
      ext
      · simp only [fα, fβ, hkk, re_add, re_sub, re_mul, im_mul, re_intCast, im_intCast, a_conjForm,
          mul_zero, add_zero, zero_mul, Int.cast_id]
        linear_combination (-f.a) * huvw + f.a * v * hb
      · simp [fα, fβ, hkk]
    rw [SetLike.mem_coe, e]
    exact S.sub_mem (S.add_mem (S.mul_mem_left _ m1) (S.mul_mem_left _ (S.sub_mem m2 m3)))
      (S.mul_mem_left _ m4)

/-! ### The norm of $\mathfrak a_f$ -/

omit [IsQuadDisc D] in
/-- $k_f^2 = a_D + b_D k_f$ modulo $a$, so $\omega \mapsto k_f$ defines a ring map $\mathbb{Z}[\omega] \to \mathbb{Z}/a$. -/
theorem kf_sq_mod {f : BinQF} (hf : f.disc = D) :
    ((kf D f : ZMod f.a.natAbs)) * (kf D f : ZMod f.a.natAbs) =
      (qa D) • (1 : ZMod f.a.natAbs) + (qb D) • (kf D f : ZMod f.a.natAbs) := by
  have hac := a_mul_c hf
  have h0 : ((f.a * f.c : ℤ) : ZMod f.a.natAbs) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_natAbs, abs_dvd]
    exact dvd_mul_right _ _
  rw [hac] at h0
  push_cast at h0
  simp only [zsmul_eq_mul, mul_one]
  linear_combination h0

omit [IsQuadDisc D] in
/-- **The ring map** $\varphi_f : \mathbb{Z}[\omega] \to \mathbb{Z}/|a|$, $u + v\omega \mapsto u + v k_f$, whose kernel is $\mathfrak a_f$. -/
noncomputable def formHom {f : BinQF} (hf : f.disc = D) : QOrder D →+* ZMod f.a.natAbs :=
  (QuadraticAlgebra.lift ⟨(kf D f : ZMod f.a.natAbs), kf_sq_mod hf⟩ : QOrder D →ₐ[ℤ] ZMod f.a.natAbs)

omit [IsQuadDisc D] in
theorem formHom_apply {f : BinQF} (hf : f.disc = D) (z : QOrder D) :
    formHom hf z = ((z.re + kf D f * z.im : ℤ) : ZMod f.a.natAbs) := by
  simp [formHom, QuadraticAlgebra.lift, zsmul_eq_mul, mul_comm]

omit [IsQuadDisc D] in
theorem ker_formHom {f : BinQF} (hf : f.disc = D) : RingHom.ker (formHom hf) = formIdeal D f := by
  ext z
  rw [RingHom.mem_ker, formHom_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_natAbs, abs_dvd,
    mem_formIdeal hf]

/-- **$N(\mathfrak a_f) = |a|$** ($\mathbb{Z}[\omega]/\mathfrak a_f \cong \mathbb{Z}/|a|$ via $\varphi_f$). Source: Cox, Lemma 7.14 [unverified locator] (i)
context; Buell, Ch. 6. -/
@[kb "cox2013" "§7.A–C [unverified locator]"]
theorem absNorm_formIdeal {f : BinQF} (hf : f.disc = D) (ha : f.a ≠ 0) :
    Ideal.absNorm (formIdeal D f) = f.a.natAbs := by
  have hsurj : Function.Surjective (formHom hf) := by
    intro x
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨(n : QOrder D), by rw [formHom_apply]; simp⟩
  have : NeZero f.a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← ker_formHom hf,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]

end Binary

end QuadFormsKB
