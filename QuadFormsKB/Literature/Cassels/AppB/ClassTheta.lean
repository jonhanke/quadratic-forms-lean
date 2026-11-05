/-
# Cassels, Appendix B, §5: the theta series $\Theta_\chi$ of a class character (5.4)-(5.7)

Cassels, *Rational Quadratic Forms* (1978), Appendix B, §5, p. 383.

**Setting.** $D < 0$ is a fundamental discriminant (`[IsQuadDisc D]`, `[Fact (D < 0)]`), $h = h(D)$ the class number, and
$w \in \{2, 4, 6\}$ the number of roots of unity of $K_D = \mathbb Q(\sqrt D)$ (`NumberField.Units.torsionOrder`). The classes
are the proper ($\mathrm{SL}_2(\mathbb Z)$-) classes of primitive positive definite forms of discriminant $D$ (the library type
`Quotient (Binary.slSetoid D)`).

**Characters.** The library's Chapter 14 group `Composition.FormClass D` contains the negative definite classes as well when
$D < 0$ (it is the group of all primitive forms, of order $2h$), whereas Appendix B uses positive definite forms only. We therefore
use the group of positive definite classes through the bijection with the ideal class group
$\mathrm{Cl}(\mathcal O_{K_D})$, $[f] \mapsto [\mathfrak a_f]$ (`Binary.slClassEquiv`), and a *character* is a group homomorphism
$\chi : \mathrm{Cl}(\mathcal O_{K_D}) \to \mathbb C^\times$ (`ClassChar`); `classCharOfForm` evaluates it on a form. This bijection is
compatible with Dirichlet composition up to inversion, $[f] \mapsto [\mathfrak a_f]^{\pm1}$ according to the convention; since
the set of all characters is stable under $\chi \mapsto \chi^{-1}$ and all local factors below are symmetric under that
inversion, nothing depends on the convention.

**Formalized.**
* The coefficients $c_\chi(m) = \sum_{[f]} \chi(f)\,a_f(m)$ of $\Theta_\chi$ (5.4) (`classThetaCoeff`), where $a_f(m)$ is the
  number of integral representations of $m$ by $f$ (`Binary.slClassRepNum`, a function of the proper class).
* **The constant term of $\Theta_\chi$ vanishes unless $\chi$ is principal** (`classThetaCoeff_zero`): $c_\chi(0) = 0$ for
  $\chi \ne 1$ and $c_1(0) = h(D)$. Proved (orthogonality of characters).
* The local data $\lambda(p)$ (`classThetaLam`) and the Euler product (5.5)-(5.7) as the **named statement** `ClassThetaEulerProduct`
  (not proved: it needs the Dedekind-domain factorization of ideals by norm, twisted by a class character).

**Erratum (factor $w$ in (5.5)-(5.6)).** The printed Euler products have constant term $1$, but the coefficient of $1^{-s}$
of $\mathcal M(\Theta_\chi)$ is $\sum_{[f]}\chi(f)a_f(1) = w$, since only the principal class represents $1$, and it does so
$w$ times (`Binary.card_autSL`). The correct identity is $\mathcal M(\Theta_\chi) = w\prod_p(\dots)^{-1}$. Confirmed
numerically (a computer calculation outside Lean): for $D = -3, -4, -20, -23, -39$ and every character of the class group, the
coefficients $c_\chi(m)$, $1 \le m \le 60$, equal $w$ times the coefficients of the Euler product exactly, and differ from the
product alone. (The exact printed phrase is "the Mellin transforms can be written as products".)

**Mellin transform.** $\mathcal M(\Theta_\chi)$ is written as Mathlib's `LSeries` of the coefficient sequence, which is
exactly `Cassels.mellinFormal` (an abbreviation for `LSeries`, `AppB/Modular.lean`); this file does not import that module.

**Indexing.** Cassels' forms are $f(x, y)$ with $x, y$ the two variables; here `Fin 2`-vectors with entries $x_0, x_1$.
-/
import QuadFormsKB.Binary.RepresentationCount
import QuadFormsKB.Siegel.Inputs
import QuadFormsKB.Binary.GenusMass

open NumberField

namespace QuadFormsKB.Cassels

open Binary BinQF

variable {D : ℤ} [IsQuadDisc D] [Fact (D < 0)]

/-- **Characters of the class group** (Cassels, App. B, §5, p. 383): group homomorphisms from the ideal class group
$\mathrm{Cl}(\mathcal O_{K_D})$ of the imaginary quadratic field $K_D$ (equivalently, of the group of proper classes of
primitive positive definite forms of discriminant $D$, `Binary.slClassEquiv`) to $\mathbb C^\times$. The argument `D` is the
fundamental discriminant. -/
abbrev ClassChar (D : ℤ) [IsQuadDisc D] : Type := ClassGroup (𝓞 (QField D)) →* ℂˣ

/-- **The value $\chi(f)$ of a character on a form.** For a binary form `f` of discriminant `D` with positive leading
coefficient (hence primitive and positive definite, `Binary.mem_primPosForm_iff`) this is $\chi$ of the ideal class of the proper
class of `f` (`Binary.slClassEquiv`); for any other form it is $0$. Arguments: `χ` the character, `f` the form
$f = [a, b, c]$. -/
noncomputable def classCharOfForm (χ : ClassChar D) (f : BinQF) : ℂ :=
  if h : f.disc = D ∧ 0 < f.a then
    (χ (slClassEquiv (Fact.out : D < 0)
      (Quotient.mk (slSetoid D) ⟨f, (mem_primPosForm_iff (IsQuadDisc.fund (D := D)) Fact.out f).mpr h⟩)) : ℂ)
  else 0

/-- **The coefficients of $\Theta_\chi$** (Cassels, App. B, (5.4), p. 383): $c_\chi(m) = \sum_{[f]}\chi(f)\,a_f(m)$, the sum
over the (finitely many) proper classes $[f]$ of primitive positive definite forms of discriminant $D$, where $a_f(m)$ is the
number of integral representations of $m$ by $f$, primitive or not (`Binary.slClassRepNum`). Arguments: `χ` the character,
`m` the index of the coefficient (natural number, $m \ge 0$). -/
noncomputable def classThetaCoeff (χ : ClassChar D) (m : ℕ) : ℂ :=
  ∑ c : Quotient (slSetoid D),
    (χ (slClassEquiv (Fact.out : D < 0) c) : ℂ) * (slClassRepNum m c : ℂ)

/-- Helper: a nontrivial character of a finite group has vanishing sum. -/
theorem sum_char_eq_zero {G : Type*} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, χ g₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext h)
  have h1 : (χ g₀ : ℂ) * ∑ g : G, (χ g : ℂ) = ∑ g : G, (χ g : ℂ) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => ?_
    simp [map_mul]
  have h2 : (χ g₀ : ℂ) ≠ 1 := fun h => hg₀ (Units.ext h)
  have : ((χ g₀ : ℂ) - 1) * ∑ g : G, (χ g : ℂ) = 0 := by rw [sub_mul, h1]; ring
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h2)

omit [IsQuadDisc D] [Fact (D < 0)] in
/-- Helper: $a_f(0) = 1$ for every class of positive definite forms. -/
theorem slClassRepNum_zero (c : Quotient (slSetoid D)) : slClassRepNum 0 c = 1 := by
  induction c using Quotient.inductionOn with
  | h f =>
    simp only [slClassRepNum, Quotient.lift_mk]
    exact Siegel.repNum_zero (Q := f.1) ((intQF_posDef_iff _).mpr f.2.2.1)

/-- **The constant term of $\Theta_\chi$** (Cassels, App. B, §5, (5.4), p. 383: "the constant term of $\Theta_\chi$ is $0$
except when $\chi$ is the principal character"). The constant coefficient $c_\chi(0) = \sum_{[f]}\chi(f)$ is $0$ for a
nonprincipal character `χ` and equals the class number $h(D)$ for the principal character $\chi = 1$ (each form has exactly one
representation of $0$, namely $(0, 0)$). -/
@[kb "cassels1978" "App. B, §5, (5.4), p. 383 (the constant term of Θ_χ is 0 unless χ is principal)"]
theorem classThetaCoeff_zero (χ : ClassChar D) :
    classThetaCoeff χ 0 = if χ = 1 then (NumberField.classNumber (QField D) : ℂ) else 0 := by
  have hD : D < 0 := Fact.out
  have key : classThetaCoeff χ 0 = ∑ x : ClassGroup (𝓞 (QField D)), (χ x : ℂ) := by
    unfold classThetaCoeff
    simp only [slClassRepNum_zero, Nat.cast_one, mul_one]
    exact Fintype.sum_equiv (slClassEquiv hD) _ _ fun c => rfl
  rw [key]
  split_ifs with h
  · subst h
    simp [NumberField.classNumber]
  · exact sum_char_eq_zero χ h

/-- **The local datum $\lambda(p)$** of (5.6)-(5.7) (Cassels, App. B, §5, p. 383), for a prime `p` and a character `χ`:
the sum of $\chi$ over the forms $[p, b, (b^2 - D)/4p]$ of discriminant $D$ with leading coefficient $p$, $b$ running over the
residues $0 \le b < 2p$ with $b^2 \equiv D \pmod{4p}$ (translation $x \mapsto x + ly$ changes $b$ by $2pl$, so these residues
index the classes of forms with leading coefficient $p$ without repetition). For $\left(\frac Dp\right) = +1$ there are two
residues $\pm b$ and $\lambda(p) = \beta_p + \gamma_p$ (the values of $\chi$ on $px^2 \pm bxy + cy^2$, counted twice if the two
classes coincide); for $\left(\frac Dp\right) = 0$ there is exactly one, $\lambda(p) = \beta_p$; for
$\left(\frac Dp\right) = -1$ there is none, $\lambda(p) = 0$. -/
noncomputable def classThetaLam (χ : ClassChar D) (p : ℕ) : ℂ :=
  ∑ b ∈ Finset.range (2 * p),
    if ((b : ℤ) ^ 2 - D) % (4 * p) = 0 then classCharOfForm χ (BinQF.mk (p : ℤ) b (((b : ℤ) ^ 2 - D) / (4 * p))) else 0

/-- **The Euler product for $\mathcal M(\Theta_\chi)$, corrected by the factor $w$** (Cassels, App. B, §5, (5.5)-(5.7),
p. 383; the book says "this is easy to verify from the theory of composition"). *Assumed, not proved* (a named statement): for
every character `χ` of the class group and every complex `s` with $\operatorname{Re} s > 1$,
$$\mathcal M(\Theta_\chi)(s) = w \prod_p \bigl(1 - \lambda(p)\,p^{-s} + \varepsilon(p)\,p^{-2s}\bigr)^{-1},$$
where $\varepsilon(p) = \left(\frac Dp\right)$ (`Binary.kronZ`), $\lambda$ is `classThetaLam`, $w$ is `NumberField.Units.torsionOrder`, and the
product over all primes converges unconditionally (`HasProd`, indexed by `Nat.Primes`). Written with the factors
$(1-\beta_pp^{-s})^{-1}(1-\gamma_pp^{-s})^{-1}$ ($\varepsilon(p) = 1$, $\beta_p\gamma_p = 1$), $(1-\beta_pp^{-s})^{-1}$ ($\varepsilon(p) = 0$)
and $(1-p^{-2s})^{-1}$ ($\varepsilon(p) = -1$) this is (5.5); the two forms agree since $\lambda = \beta_p + \gamma_p$,
$\beta_p\gamma_p = \chi(\mathfrak p\bar{\mathfrak p}) = 1$.

*Erratum:* the printed products lack the factor $w$ (the coefficient of $1^{-s}$ of the left side is $w$); see the module
docstring for the numerical confirmation.

*What a proof needs:* by `Binary.repNum_eq`, $c_\chi(m) = w\sum_{N\mathfrak b = m}\chi(\mathfrak b)^{\mp1}$ (sum over ideals of
$\mathcal O_{K_D}$); then the Euler product of the Hecke $L$-series of an ideal class character, from unique factorization of
ideals and the splitting of rational primes in $K_D$ (split, ramified, inert according to $\varepsilon(p) = 1, 0, -1$); not in
the library (Mathlib has no Euler product for Hecke $L$-series of number fields). This is an assumed input. -/
@[kb "cassels1978" "App. B, §5, (5.5)–(5.7), p. 383 (Euler product of M(Θ_χ); corrected by the factor w)"]
structure ClassThetaEulerProduct (D : ℤ) [IsQuadDisc D] [Fact (D < 0)] : Prop where
  /-- For every character `χ` and every `s` with $\operatorname{Re} s > 1$, the product of the local factors over all
  primes converges unconditionally to $\mathcal M(\Theta_\chi)(s)/w$. -/
  hasProd : ∀ (χ : ClassChar D) (s : ℂ), 1 < s.re →
    HasProd (fun p : Nat.Primes =>
      (1 - classThetaLam χ p * (p : ℂ) ^ (-s) + (kronZ D ((p : ℕ) : ZMod D.natAbs) : ℂ) * (p : ℂ) ^ (-(2 * s)))⁻¹)
      (LSeries (classThetaCoeff χ) s / (NumberField.Units.torsionOrder (QField D) : ℂ))

end QuadFormsKB.Cassels
