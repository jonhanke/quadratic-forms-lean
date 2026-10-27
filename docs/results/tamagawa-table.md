# Tamagawa numbers of SO(V) over every number field

For a nondegenerate quadratic space $`V`$ of dimension $`n`$ over a number field $`F`$, the Tamagawa number of the special orthogonal group is

| $`n`$ | $`\tau(\mathrm{SO}(V))`$ | Measure |
|---|---|---|
| $`n \ge 3`$ | $`2`$ | Weil's Tamagawa measure, convergence factors $`\lambda_v = 1`$ |
| $`n = 2`$, $`V`$ anisotropic | $`2`$ | convergence factors $`\lambda_v = L_v(1,\chi_E)^{-1}`$, global factor $`L_F(1,\chi_E)^{-1}`$, $`E`$ the discriminant field |
| $`n = 2`$, $`V`$ isotropic | $`1`$ | convergence factors $`\lambda_v = 1 - N(v)^{-1}`$, global factor $`\rho_F^{-1}`$, norm-one volume ($`\mathrm{SO}(V) \cong \mathbb{G}_m`$) |
| $`n = 1`$ | $`1`$ | $`\mathrm{SO}(V)`$ is trivial |

for every number field $`F`$ (real and complex places allowed), every signature at the real places, isotropic or anisotropic $`V`$, and every class number. This completes, over every number field, the result of release 0.1.0 (totally positive definite forms over totally real fields, [Tamagawa number and mass formula](tamagawa-mass-formula.md)).

## Statement

Let $`F`$ be a number field with discriminant $`d_F`$ and $`r_2`$ complex places, and let $`Q_0`$ be a nondegenerate quadratic form in $`n`$ variables with coefficients in the ring of integers of $`F`$; $`V = F^n`$ with $`Q_0`$, $`L`$ the standard lattice. The Tamagawa measure with convergence factors $`(\lambda_v)`$ is

```math
\mu_{\mathrm{Tam}} = |d_F|^{-n(n-1)/4}\, 2^{n(n-1)r_2/2}\, \mu_\infty \times \mu_f, \qquad \mu_f(\mathrm{SO}(\hat L)) = \prod_v \lambda_v^{-1}\, \alpha_v(L, L),
```

where $`\mu_\infty`$ is the product of the gauge-form (Leray) measures of $`\mathrm{SO}(V)`$ at the archimedean places and $`\alpha_v(L, L)`$ is Siegel's local density, the volume of $`\mathrm{SO}(L_v)`$. Then

```math
\tau(\mathrm{SO}(V)) = \mathrm{vol}\bigl(\mathrm{SO}(V)(F)\backslash \mathrm{SO}(V)(\mathbb{A}_F),\ \mu_{\mathrm{Tam}}\bigr)
```

takes the values in the table. The same holds for every quadratic space $`(V, Q)`$ over $`F`$: it has an integral model (a basis $`b`$, a nonzero $`d`$ and a form $`Q_0`$ with integral coefficients equal to $`d\cdot Q`$ in the coordinates of $`b`$), and every integral model gives the value in the table.

## Scope and hypotheses

- Every number field, every signature, every class number. At a complex place every form is indefinite.
- For $`n = 2`$ the plain product of the local volumes diverges and Weil's convergence factors are needed; with them the anisotropic case is Ono's $`\tau(R^1_{E/F}\mathbb{G}_m) = 2`$ and the isotropic case is $`\tau(\mathbb{G}_m) = 1`$ (measured on the norm-one subgroup).
- The covolume is Mathlib's `MeasureTheory.covolume` (the measure of a fundamental domain, and $`0`$ if there is none), so the nonzero values above also say that a fundamental domain exists.

## In Lean

The headline statements are in [`Challenge.lean`](../../Challenge.lean), section "The Tamagawa number of SO(V) over every number field". Each also states that the product of the local masses in $`\mu_f`$ converges unconditionally and, for $`n = 2`$ anisotropic, that $`L_F(1,\chi_E)`$ exists and is positive (lemmas in `QuadFormsKB/Tamagawa/HeadlineFactsWeil.lean`).

- `QuadFormsKB.Headlines.tamagawa_two_numberField` (from `QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release_uncond`): $`n \ge 3`$, forms.
- `QuadFormsKB.Headlines.tamagawa_two_space` (from `QuadFormsKB.Tamagawa.Measure.Weil.tauTwo_space_uncond`): $`n \ge 3`$, quadratic spaces.
- `QuadFormsKB.Headlines.tamagawa_one_rankOne` (from `QuadFormsKB.Tamagawa.Measure.Weil.covolume_muTam_rankOne`; the space version is `tauOne_space_rankOne`): $`n = 1`$.
- `QuadFormsKB.Headlines.tamagawa_two_binary` and `QuadFormsKB.Headlines.tamagawa_two_space_binary` (from `tauTwoBinaryAll_uncond`, `tauTwo_space_binary`): $`n = 2`$ anisotropic.
- `QuadFormsKB.Headlines.tamagawa_one_binary_isotropic` and `QuadFormsKB.Headlines.tamagawa_one_space_binary_isotropic` (from `tauOne_binary_isotropic_uncond`, `tauOne_space_binary_isotropic`): $`n = 2`$ isotropic.

## Proof outline

Weil's route (*Adeles and Algebraic Groups*). For $`n = 3`$, $`\mathrm{SO}(V) \cong D^\times/F^\times`$ for a quaternion algebra $`D`$, and $`\tau = 2`$ follows from Weil's computation for $`D^\times`$ (Fujisaki's lemma, the zeta function of $`D`$ and the residue of $`\zeta_F`$). For $`n = 4`$, $`\mathrm{SO}(V)`$ is a quotient of $`G^\natural = \{g \in (D \otimes E)^\times : \mathrm{nrd}(g) \in F^\times\}`$ for the discriminant algebra $`E`$, and Weil's comparison of Tamagawa measures under this isogeny-free quotient gives $`\tau = 2`$. For $`n \ge 5`$, Weil's induction fibres $`\mathrm{SO}(V)`$ over the spheres $`\{Q = \rho\}`$ and computes the adelic integral of a Gaussian test function by Poisson summation and the spherical zeta functions. For $`n = 2`$, $`\mathrm{SO}(V)`$ is the norm-one torus of the discriminant field $`E`$ (or $`\mathbb{G}_m`$ when $`V`$ is isotropic), and the centre argument of Weil (Thm 3.2.1) gives $`2\rho_E/\rho_F`$ for the full torus, hence $`2`$ with the global factor $`L_F(1,\chi_E)^{-1} = \rho_F/\rho_E`$.

## Erratum

An earlier version of the library assumed an input `AdelicSphereEulerGaussInputs` that is false; three theorems that assumed it are vacuous and are not headlines. See [errata](errata.md).

## References

- A. Weil, *Adeles and Algebraic Groups*, Birkhäuser, 1982, §2.3–2.4, §3.2 (Thm 3.2.1), §3.7 (Thm 3.7.1), §4.5 (Thm 4.5.1) [unverified locator].
- T. Ono, *On the Tamagawa number of algebraic tori*, Ann. of Math. 78 (1963) [unverified locator].

Bibliographic entries are in [references.bib](../../references.bib). Related: [Siegel's formula for indefinite forms](siegel-indefinite.md), [Tamagawa number and mass formula over totally real fields](tamagawa-mass-formula.md).
