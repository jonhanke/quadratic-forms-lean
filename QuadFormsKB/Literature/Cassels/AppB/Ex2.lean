/-
# Cassels, Appendix B, Example 2

Cassels, *Rational Quadratic Forms* (1978), Appendix B (*Analytic methods*), Examples, p. 389, Example 2.

**Source statement (paraphrased).** Let $\chi$ be a character of the group of residues prime to $n$ modulo $n$.
(i) If $n = lm$ with $l, m$ coprime, then $\chi(r) = \psi(r)\phi(r)$ for characters $\psi$ modulo $l$ and $\phi$ modulo $m$.
(ii) With $\tau(\chi, n) = \sum \chi(r)\, e(r/n)$ (sum over residues prime to $n$, $e(x) = e^{2\pi i x}$), the book
claims $\psi(m)\phi(l)\,\tau(\chi, n) = \tau(\psi, l)\,\tau(\phi, m)$.

**Erratum (ii).** The printed identity is wrong in general. Writing $r = am + bl$ ($a$ modulo $l$, $b$ modulo $m$) gives
$\chi(r) = \psi(a)\psi(m)\phi(b)\phi(l)$ and $e(r/n) = e(a/l)\,e(b/m)$, hence the correct identity
$\tau(\chi, n) = \psi(m)\phi(l)\,\tau(\psi, l)\,\tau(\phi, m)$. The printed one follows from it exactly when
$(\psi(m)\phi(l))^2 = 1$ (for instance for real-valued $\psi, \phi$, the case used in Example 4), or when
$\tau(\psi, l)\tau(\phi, m) = 0$. Counterexample (checked numerically in floating point): $l = 5$, $m = 3$, $\psi$ the character of
order $4$ modulo $5$ with $\psi(2) = i$, $\phi$ trivial modulo $3$, $\chi = \psi\phi$. Then $\psi(3)\phi(5) = -i$, so
$(\psi(m)\phi(l))^2 = -1$; $\tau(\psi, 5) \ne 0$ and $\tau(\phi, 3) = -1$. The computed values satisfy
$\tau(\chi, 15) = -i\,\tau(\psi, 5)\tau(\phi, 3)$ (the corrected identity) and the two sides of the printed identity
are negatives of each other and nonzero.

**Conventions.** Characters are Mathlib's `MulChar (ZMod n) ℂ` (a Dirichlet character, extended by $0$ to non-units); the
residue of an integer $r$ is its image in `ZMod n`. $e(r/n)$ is `ZMod.stdAddChar` (value $\exp(2\pi i r/n)$ on the
residue of $r$). The CRT isomorphism is `ZMod.chineseRemainder`. Part (i) needs no positivity assumption; for (ii) we
take $l, m \ge 1$ (`NeZero`). The cases $l = 1$ or $m = 1$ are not excluded: they are covered by the general proof
(modulo $1$ there is only the trivial character, $\tau(\cdot, 1) = 1$).

**Formalized.** `casselsGauss` ($\tau$ as a sum over units) and its comparison with Mathlib's `gaussSum`; (i) existence of
the factorization (`exists_char_factor`); (ii) the corrected identity (`casselsGauss_mul`), the printed identity under the
hypothesis $(\psi(m)\phi(l))^2 = 1$ (`casselsGauss_printed`), and for real-valued $\psi, \phi$ (`casselsGauss_printed_real`).
-/
import QuadFormsKB.Binary.KroneckerChar

open Complex

namespace QuadFormsKB.Cassels

/-- **Cassels' Gauss sum** $\tau(\chi, n) = \sum \chi(r)\,e(r/n)$, the sum over the residues $r$ modulo $n$ prime to $n$
(the units of `ZMod n`), $e(r/n)$ being `ZMod.stdAddChar r`. Arguments: `n` the modulus ($n \ge 1$), `χ` a character
modulo $n$. See `casselsGauss_eq_gaussSum` for the comparison with Mathlib's `gaussSum`. -/
noncomputable def casselsGauss {n : ℕ} [NeZero n] (χ : MulChar (ZMod n) ℂ) : ℂ :=
  ∑ u : (ZMod n)ˣ, χ (u : ZMod n) * ZMod.stdAddChar (u : ZMod n)

/-- Helper: comparison of Cassels' sum over units with Mathlib's Gauss sum over all of `ZMod n` (the terms at non-units
vanish because $\chi$ does). Arguments: `n` the modulus, `χ` the character. -/
theorem casselsGauss_eq_gaussSum {n : ℕ} [NeZero n] (χ : MulChar (ZMod n) ℂ) :
    casselsGauss χ = gaussSum χ ZMod.stdAddChar := by
  classical
  unfold casselsGauss gaussSum
  have hinj : Function.Injective (fun u : (ZMod n)ˣ => (u : ZMod n)) := Units.val_injective
  rw [← Finset.sum_image (f := fun x : ZMod n => χ x * ZMod.stdAddChar x) (s := Finset.univ)
    (g := fun u : (ZMod n)ˣ => (u : ZMod n)) (fun a _ b _ h => hinj h)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  have : ¬ IsUnit x := fun hu => hx (Finset.mem_image.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩)
  rw [MulChar.map_nonunit χ this, zero_mul]

/-- Helper: the part of a character modulo $lm$ at the first factor, $\psi(a) = \chi(\text{the residue} \equiv a \bmod l,\
\equiv 1 \bmod m)$. Arguments: `h` coprimality of $l, m$, `χ` the character modulo $lm$. -/
noncomputable def crtCharLeft {l m : ℕ} (h : l.Coprime m) (χ : MulChar (ZMod (l * m)) ℂ) : MulChar (ZMod l) ℂ where
  toFun a := χ ((ZMod.chineseRemainder h).symm (a, 1))
  map_one' := by
    have : ((1, 1) : ZMod l × ZMod m) = 1 := rfl
    rw [this, map_one, map_one]
  map_mul' a b := by
    have : ((a * b, 1) : ZMod l × ZMod m) = (a, 1) * (b, 1) := by simp
    rw [this, map_mul, map_mul]
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have := hu.map (ZMod.chineseRemainder h)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).1

/-- Helper: the part of a character modulo $lm$ at the second factor, $\phi(b) = \chi(\text{the residue} \equiv 1 \bmod l,\
\equiv b \bmod m)$. Arguments: `h` coprimality of $l, m$, `χ` the character modulo $lm$. -/
noncomputable def crtCharRight {l m : ℕ} (h : l.Coprime m) (χ : MulChar (ZMod (l * m)) ℂ) : MulChar (ZMod m) ℂ where
  toFun b := χ ((ZMod.chineseRemainder h).symm (1, b))
  map_one' := by
    have : ((1, 1) : ZMod l × ZMod m) = 1 := rfl
    rw [this, map_one, map_one]
  map_mul' a b := by
    have : ((1, a * b) : ZMod l × ZMod m) = (1, a) * (1, b) := by simp
    rw [this, map_mul, map_mul]
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have := hu.map (ZMod.chineseRemainder h)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).2

/-- Helper: $\chi(y) = \psi(y \bmod l)\,\phi(y \bmod m)$ for the canonical factors, for every residue $y$ modulo $lm$,
written through the CRT isomorphism. Arguments: `h` coprimality, `χ` the character, `y` the residue. -/
theorem crt_apply {l m : ℕ} (h : l.Coprime m) (χ : MulChar (ZMod (l * m)) ℂ) (y : ZMod (l * m)) :
    χ y = crtCharLeft h χ ((ZMod.chineseRemainder h) y).1 * crtCharRight h χ ((ZMod.chineseRemainder h) y).2 := by
  simp only [crtCharLeft, crtCharRight, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← map_mul]
  congr 1
  apply (ZMod.chineseRemainder h).injective
  simp

/-- **Cassels, Appendix B, Example 2 (i) (p. 389).** For coprime $l, m$ and a character $\chi$ modulo $lm$ there are
characters $\psi$ modulo $l$ and $\phi$ modulo $m$ with $\chi(r) = \psi(r)\phi(r)$ for every integer $r$ (characters
applied to the residues of $r$; both sides vanish when $r$ is not prime to $lm$). No positivity assumption is needed; the
cases $l = 1$ or $m = 1$ are included (then one factor is the trivial character modulo $1$). Arguments: `l`, `m` the
coprime moduli (`h`), `χ` the character modulo $lm$ (a Dirichlet character `DirichletCharacter ℂ (l * m)`). The factors
are the canonical `crtCharLeft`, `crtCharRight`. -/
@[kb "cassels1978" "App. B, Ex. 2 (i), p. 389 (characters mod lm factor as ψ·φ)"]
theorem exists_char_factor {l m : ℕ} (h : l.Coprime m) (χ : DirichletCharacter ℂ (l * m)) :
    ∃ (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ m),
      ∀ r : ℤ, χ (r : ZMod (l * m)) = ψ (r : ZMod l) * φ (r : ZMod m) := by
  refine ⟨crtCharLeft h χ, crtCharRight h χ, fun r => ?_⟩
  rw [crt_apply h χ]
  simp

/-- Helper: the map $(a, b) \mapsto$ the residue modulo $lm$ that is $\equiv am \bmod l$ and $\equiv bl \bmod m$ (i.e.
$r = am + bl$ of the book) is a bijection $\mathbb Z/l \times \mathbb Z/m \to \mathbb Z/lm$. -/
theorem crtShift_bijective {l m : ℕ} [NeZero l] [NeZero m] (h : l.Coprime m) :
    Function.Bijective (fun p : ZMod l × ZMod m =>
      (ZMod.chineseRemainder h).symm (p.1 * (m : ZMod l), p.2 * (l : ZMod m))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro p q hpq
  have h2 := congrArg (ZMod.chineseRemainder h) hpq
  simp only [RingEquiv.apply_symm_apply, Prod.mk.injEq] at h2
  have hm : IsUnit (m : ZMod l) := (ZMod.unitOfCoprime m h.symm).isUnit
  have hl : IsUnit (l : ZMod m) := (ZMod.unitOfCoprime l h).isUnit
  exact Prod.ext (hm.mul_left_inj.mp h2.1) (hl.mul_left_inj.mp h2.2)

/-- Helper: for the residue $y_{a,b}$ modulo $lm$ with $y \equiv am \bmod l$, $y \equiv bl \bmod m$, the additive
character factors: $e(y/(lm)) = e(a/l)\,e(b/m)$. -/
theorem stdAddChar_crtShift {l m : ℕ} [NeZero l] [NeZero m] (h : l.Coprime m) (a : ZMod l) (b : ZMod m) :
    ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (a * (m : ZMod l), b * (l : ZMod m))) =
      ZMod.stdAddChar a * ZMod.stdAddChar b := by
  set r : ℤ := (a.val : ℤ) * m + (b.val : ℤ) * l with hr
  have hy : (ZMod.chineseRemainder h).symm (a * (m : ZMod l), b * (l : ZMod m)) = ((r : ℤ) : ZMod (l * m)) := by
    apply (ZMod.chineseRemainder h).injective
    rw [RingEquiv.apply_symm_apply, map_intCast]
    ext <;> simp [hr]
  have ha : a = ((a.val : ℤ) : ZMod l) := by simp
  have hb : b = ((b.val : ℤ) : ZMod m) := by simp
  rw [hy, ha, hb, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hl : (l : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp only [hr]
  push_cast
  field_simp

/-- **Cassels, Appendix B, Example 2 (ii) (p. 389), corrected identity.** For coprime $l, m \ge 1$ and a character
$\chi$ modulo $lm$ with $\chi(r) = \psi(r)\phi(r)$ as in (i),
$$\tau(\chi, lm) = \psi(m)\,\phi(l)\,\tau(\psi, l)\,\tau(\phi, m).$$

*Erratum:* the book prints $\psi(m)\phi(l)\,\tau(\chi, n) = \tau(\psi, l)\tau(\phi, m)$, which differs by the factor
$(\psi(m)\phi(l))^2$ (counterexample in the module docstring: $l = 5$, $m = 3$, $\psi$ of order $4$, $\phi$ trivial; confirmed by
the computation $r = am + bl$, which is this proof, and numerically). The printed form is `casselsGauss_printed`.
Arguments: `h` coprimality, `χ` the character modulo $lm$, `ψ`, `φ` characters modulo $l$ and $m$ with
`hfac` the factorization of (i) on integers; $\psi(m)$ is `ψ (m : ZMod l)`, $\phi(l)$ is `φ (l : ZMod m)`. -/
@[kb "cassels1978" "App. B, Ex. 2 (ii), p. 389 (corrected: τ(χ,lm) = ψ(m)φ(l)τ(ψ,l)τ(φ,m); printed form has an erratum)"]
theorem casselsGauss_mul {l m : ℕ} [NeZero l] [NeZero m] (h : l.Coprime m)
    (χ : MulChar (ZMod (l * m)) ℂ) (ψ : MulChar (ZMod l) ℂ) (φ : MulChar (ZMod m) ℂ)
    (hfac : ∀ r : ℤ, χ (r : ZMod (l * m)) = ψ (r : ZMod l) * φ (r : ZMod m)) :
    casselsGauss χ = ψ (m : ZMod l) * φ (l : ZMod m) * (casselsGauss ψ * casselsGauss φ) := by
  rw [casselsGauss_eq_gaussSum, casselsGauss_eq_gaussSum, casselsGauss_eq_gaussSum]
  unfold gaussSum
  -- the factorization on all residues, via the CRT isomorphism
  have hfac' : ∀ y : ZMod (l * m), χ y =
      ψ ((ZMod.chineseRemainder h) y).1 * φ ((ZMod.chineseRemainder h) y).2 := by
    intro y
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective y
    rw [hfac r]
    simp
  rw [← Fintype.sum_bijective _ (crtShift_bijective h)
    (fun p => χ ((ZMod.chineseRemainder h).symm (p.1 * (m : ZMod l), p.2 * (l : ZMod m))) *
      ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (p.1 * (m : ZMod l), p.2 * (l : ZMod m))))
    (fun y => χ y * ZMod.stdAddChar y) (fun p => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hfac', stdAddChar_crtShift h]
  simp only [RingEquiv.apply_symm_apply, map_mul]
  ring

/-- **Cassels, Appendix B, Example 2 (ii) (p. 389), as printed, under the hypothesis that makes it true.** If
$(\psi(m)\phi(l))^2 = 1$ (equivalently $\psi(m)^2\phi(l)^2 = 1$) then $\psi(m)\phi(l)\,\tau(\chi, lm) =
\tau(\psi, l)\tau(\phi, m)$. *Erratum:* without the hypothesis the printed identity is false in general (see
`casselsGauss_mul`). Arguments as in `casselsGauss_mul`, plus `hsq : (ψ m * φ l)^2 = 1`. -/
@[kb "cassels1978" "App. B, Ex. 2 (ii), p. 389 (printed identity ψ(m)φ(l)τ(χ,n) = τ(ψ,l)τ(φ,m), under ψ(m)²φ(l)² = 1)"]
theorem casselsGauss_printed {l m : ℕ} [NeZero l] [NeZero m] (h : l.Coprime m)
    (χ : MulChar (ZMod (l * m)) ℂ) (ψ : MulChar (ZMod l) ℂ) (φ : MulChar (ZMod m) ℂ)
    (hfac : ∀ r : ℤ, χ (r : ZMod (l * m)) = ψ (r : ZMod l) * φ (r : ZMod m))
    (hsq : ψ (m : ZMod l) ^ 2 * φ (l : ZMod m) ^ 2 = 1) :
    ψ (m : ZMod l) * φ (l : ZMod m) * casselsGauss χ = casselsGauss ψ * casselsGauss φ := by
  rw [casselsGauss_mul h χ ψ φ hfac]
  linear_combination (casselsGauss ψ * casselsGauss φ) * hsq

/-- Helper: a real-valued character takes the value $\pm1$, so has square $1$, at every residue prime to the modulus.
Arguments: `n` the modulus ($\ge 1$), `χ` the character, `hreal` that all its values are real, `u` a unit. -/
theorem real_char_sq_unit {n : ℕ} [NeZero n] (χ : MulChar (ZMod n) ℂ) (hreal : ∀ r, (χ r).im = 0)
    (u : (ZMod n)ˣ) : χ (u : ZMod n) ^ 2 = 1 := by
  have h1 : (χ (u : ZMod n)) ^ Fintype.card (ZMod n)ˣ = 1 := by
    have : (u : ZMod n) ^ Fintype.card (ZMod n)ˣ = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one]
    rw [← map_pow, this, map_one]
  have hn : ‖χ (u : ZMod n)‖ = 1 :=
    norm_eq_one_of_pow_eq_one h1 (Fintype.card_ne_zero)
  have hre : (χ (u : ZMod n)).re ^ 2 = 1 := by
    have := Complex.sq_norm (χ (u : ZMod n))
    rw [hn, Complex.normSq_apply, hreal] at this
    nlinarith
  apply Complex.ext
  · simp [pow_two] at hre ⊢
    rw [hreal]; simpa using hre
  · simp [pow_two, hreal]

/-- **Cassels, Appendix B, Example 2 (ii) (p. 389), printed identity for real-valued characters** (the case used in
Example 4): if $\psi$ and $\phi$ are real-valued then $\psi(m)\phi(l)\,\tau(\chi, lm) = \tau(\psi, l)\tau(\phi, m)$,
because $\psi(m), \phi(l) \in \{\pm 1\}$ ($m$ is prime to $l$ and $l$ to $m$). Arguments as in `casselsGauss_mul`, plus
`hψ`, `hφ` real-valuedness of $\psi$, $\phi$. -/
@[kb "cassels1978" "App. B, Ex. 2 (ii), p. 389 (printed identity for real-valued ψ, φ)"]
theorem casselsGauss_printed_real {l m : ℕ} [NeZero l] [NeZero m] (h : l.Coprime m)
    (χ : MulChar (ZMod (l * m)) ℂ) (ψ : MulChar (ZMod l) ℂ) (φ : MulChar (ZMod m) ℂ)
    (hfac : ∀ r : ℤ, χ (r : ZMod (l * m)) = ψ (r : ZMod l) * φ (r : ZMod m))
    (hψ : ∀ r, (ψ r).im = 0) (hφ : ∀ r, (φ r).im = 0) :
    ψ (m : ZMod l) * φ (l : ZMod m) * casselsGauss χ = casselsGauss ψ * casselsGauss φ := by
  apply casselsGauss_printed h χ ψ φ hfac
  have h1 := real_char_sq_unit ψ hψ (ZMod.unitOfCoprime m h.symm)
  have h2 := real_char_sq_unit φ hφ (ZMod.unitOfCoprime l h)
  simp only [ZMod.coe_unitOfCoprime] at h1 h2
  rw [h1, h2, one_mul]

end QuadFormsKB.Cassels
