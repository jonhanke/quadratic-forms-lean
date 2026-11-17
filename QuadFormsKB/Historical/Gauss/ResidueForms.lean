import QuadFormsKB.Historical.Gauss.Forms
import QuadFormsKB.Literature.Cassels.Ch14.Genus

/-!
# Forms that are quadratic residues (Disquisitiones Arithmeticae, Art. 233)

(definition) (Art. 233 I) (Art. 233 VIII) and
(Art. 233 VI).

Gauss calls $M(a, b, c)$ a **quadratic residue** of $m$ if there are integers $g, h$ with
$$g^2 \equiv Ma,\quad gh \equiv Mb,\quad h^2 \equiv Mc \pmod m$$
(`IsResidueForm`; written $\sqrt{M(a, b, c)} \pmod m$ has the value $(g, h)$).

* `art233_one` (Art. 233 I): if $M(a, b, c)$ is a residue of $m$ and $M$ is prime to $m$, then $m$ divides the
  determinant $b^2 - ac$.
* `art233_eight` (Art. 233 VIII): if $(a, b, c)$ goes into $(a', b', c')$ by $x = \alpha x' + \beta y'$,
  $y = \gamma x' + \delta y'$ and $(g, h)$ is a value of $\sqrt{M(a, b, c)} \pmod m$, then
  $(\alpha g + \gamma h, \beta g + \delta h)$ is a value of $\sqrt{M(a', b', c')} \pmod m$.
* `art233_six` (Art. 233 VI): every properly primitive form of the principal genus is a quadratic residue of its
  determinant ($1$ is a characteristic number of it). The principal genus is the library's
  `Composition.InPrincipalGenus` (same genus as the principal form, defined by local equivalence; its agreement with
  Gauss's characters is a recorded loose end).
-/

namespace QuadFormsKB.Historical.Gauss

open BinQF Binary

/-- **$M(a, b, c)$ is a quadratic residue of $m$** (Gauss, *Disq. Arith.* Art. 233): there are integers $g, h$ with
$g^2 \equiv Ma$, $gh \equiv Mb$, $h^2 \equiv Mc \pmod m$. -/
@[kb "gauss1801" "Art. 233"]
def IsResidueForm (M a b c m : ℤ) : Prop :=
  ∃ g h : ℤ, g ^ 2 ≡ M * a [ZMOD m] ∧ g * h ≡ M * b [ZMOD m] ∧ h ^ 2 ≡ M * c [ZMOD m]

/-- **Gauss, *Disq. Arith.* Art. 233 I:** if $M(a, b, c)$ is a quadratic residue of $m$
and $M$ is prime to $m$, then $m$ divides the determinant $b^2 - ac$. -/
@[kb "gauss1801" "Art. 233 I"]
theorem art233_one {M a b c m : ℤ} (h : IsResidueForm M a b c m) (hM : IsCoprime M m) :
    m ∣ gaussDet a b c := by
  obtain ⟨g, k, h1, h2, h3⟩ := h
  -- $M^2(b^2 - ac) \equiv (gk)^2 - g^2 k^2 = 0$
  have e : (M * b) ^ 2 ≡ M * a * (M * c) [ZMOD m] :=
    (h2.pow 2).symm.trans ((show (g * k) ^ 2 = g ^ 2 * k ^ 2 by ring) ▸ (h1.mul h3))
  have e2 := Int.ModEq.dvd e
  have h0 : M ^ 2 * gaussDet a b c = -(M * a * (M * c) - (M * b) ^ 2) := by simp only [gaussDet]; ring
  have hdvd : m ∣ M ^ 2 * gaussDet a b c := by rw [h0]; exact dvd_neg.mpr e2
  exact (hM.pow_left (m := 2)).symm.dvd_of_dvd_mul_left hdvd

/-- **Gauss, *Disq. Arith.* Art. 233 VIII:** if $(a, b, c)$ goes into $(a', b', c')$ by
the substitution $x = \alpha x' + \beta y'$, $y = \gamma x' + \delta y'$ and $(g, h)$ is a value of
$\sqrt{M(a, b, c)} \pmod m$, then $(\alpha g + \gamma h, \beta g + \delta h)$ is a value of
$\sqrt{M(a', b', c')} \pmod m$. -/
@[kb "gauss1801" "Art. 233 VIII"]
theorem art233_eight {M a b c m g h : ℤ} (α β γ δ : ℤ)
    (h1 : g ^ 2 ≡ M * a [ZMOD m]) (h2 : g * h ≡ M * b [ZMOD m]) (h3 : h ^ 2 ≡ M * c [ZMOD m]) :
    (α * g + γ * h) ^ 2 ≡ M * (a * α ^ 2 + 2 * b * α * γ + c * γ ^ 2) [ZMOD m] ∧
      (α * g + γ * h) * (β * g + δ * h) ≡ M * (a * α * β + b * (α * δ + β * γ) + c * γ * δ) [ZMOD m] ∧
      (β * g + δ * h) ^ 2 ≡ M * (a * β ^ 2 + 2 * b * β * δ + c * δ ^ 2) [ZMOD m] := by
  refine ⟨?_, ?_, ?_⟩
  · have := ((h1.mul_left (α ^ 2)).add (h2.mul_left (2 * α * γ))).add (h3.mul_left (γ ^ 2))
    convert this using 1 <;> ring
  · have := ((h1.mul_left (α * β)).add (h2.mul_left (α * δ + β * γ))).add (h3.mul_left (γ * δ))
    convert this using 1 <;> ring
  · have := ((h1.mul_left (β ^ 2)).add (h2.mul_left (2 * β * δ))).add (h3.mul_left (δ ^ 2))
    convert this using 1 <;> ring

/-- **Gauss, *Disq. Arith.* Art. 233 VI: every form of the principal genus is a
quadratic residue of its determinant**, i.e. $1$ is a characteristic number of it: for a properly primitive form
$(a, b, c)$ ($\gcd(a, 2b, c) = 1$) of nonzero determinant $D = b^2 - ac$ in the principal genus
(`Composition.InPrincipalGenus`), there are $g, h$ with $g^2 \equiv a$, $gh \equiv b$, $h^2 \equiv c \pmod D$. -/
@[kb "gauss1801" "Art. 233 VI"]
theorem art233_six {a b c : ℤ} (hD : gaussDet a b c ≠ 0)
    (hpg : Composition.InPrincipalGenus (gaussForm a b c)) : IsResidueForm 1 a b c (gaussDet a b c) := by
  set D := gaussDet a b c with hDdef
  have hdisc : (gaussForm a b c).disc ≠ 0 := by rw [disc_gaussForm]; exact mul_ne_zero four_ne_zero hD
  obtain ⟨w, x, y, hxy, hw, hval⟩ := Composition.exists_eval_sq_of_inPrincipalGenus hdisc hpg
  obtain ⟨u, v, huv⟩ := hxy
  -- the substitution $\begin{pmatrix} x & -v \\ y & u \end{pmatrix}$ of determinant $1$ carries $(a, b, c)$ to
  -- $(w^2, b', c')$
  set a' := a * x ^ 2 + 2 * b * x * y + c * y ^ 2 with ha'
  set b' := a * x * (-v) + b * (x * u + (-v) * y) + c * y * u with hb'
  set c' := a * (-v) ^ 2 + 2 * b * (-v) * u + c * u ^ 2 with hc'
  have hwa : a' = w ^ 2 := by rw [← hval, eval_gaussForm]
  have hdet' : b' ^ 2 - a' * c' = D := by
    have := gaussDet_subst a b c x (-v) y u
    simp only [gaussDet] at this
    rw [hDdef, gaussDet, ha', hb', hc', this]
    have h1 : x * u - -v * y = 1 := by linarith
    rw [h1]; ring
  -- $w$ is invertible modulo $D$
  have hwD : IsCoprime w D := by
    have : IsCoprime w (8 * D) := by
      have := hw; rwa [disc_gaussForm, show 2 * (4 * gaussDet a b c) = 8 * D by rw [hDdef]; ring] at this
    exact this.of_mul_right_right
  obtain ⟨s, t, hst⟩ := hwD
  -- residue of $(w^2, b', c')$: $g = w$, $h = s b'$
  have r1 : w ^ 2 ≡ 1 * a' [ZMOD D] := by rw [hwa, one_mul]
  have r2 : w * (s * b') ≡ 1 * b' [ZMOD D] := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨b' * t, by linear_combination (-b') * hst⟩
  have r3 : (s * b') ^ 2 ≡ 1 * c' [ZMOD D] := by
    apply Int.modEq_iff_dvd.mpr
    -- $s^2 b'^2 = s^2 (D + w^2 c') \equiv (sw)^2 c' \equiv c'$
    refine ⟨-(s ^ 2) + 2 * t * c' - t ^ 2 * D * c', ?_⟩
    linear_combination (-(s ^ 2)) * hdet' - s ^ 2 * c' * hwa - c' * (1 - t * D + s * w) * hst
  -- transport back by the inverse substitution $\begin{pmatrix} u & v \\ -y & x \end{pmatrix}$
  have back := art233_eight (M := 1) (a := a') (b := b') (c := c') (m := D) u v (-y) x r1 r2 r3
  have e1 : a' * u ^ 2 + 2 * b' * u * -y + c' * (-y) ^ 2 = a := by
    rw [ha', hb', hc']; linear_combination (a * (u * x + v * y + 1)) * huv
  have e2 : a' * u * v + b' * (u * x + v * -y) + c' * -y * x = b := by
    rw [ha', hb', hc']; linear_combination (b * (u * x + v * y + 1)) * huv
  have e3 : a' * v ^ 2 + 2 * b' * v * x + c' * x ^ 2 = c := by
    rw [ha', hb', hc']; linear_combination (c * (u * x + v * y + 1)) * huv
  refine ⟨u * w + -y * (s * b'), v * w + x * (s * b'), ?_, ?_, ?_⟩
  · have := back.1; rwa [e1] at this
  · have := back.2.1; rwa [e2] at this
  · have := back.2.2; rwa [e3] at this

end QuadFormsKB.Historical.Gauss
