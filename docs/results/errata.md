# Errata

Errors found in this repository's own statements. Errata and updates found in the literature while formalizing are noted in the docstrings of the declarations concerned (marked *Erratum:* or *Update:*).

## A false input: `AdelicSphereEulerGaussInputs` (found 2026-10-24)

**What was stated.** The library contains a named input (added after release 0.1.0, and kept so that the theorems below still compile), the structure `QuadFormsKB.Tamagawa.Measure.Weil.AdelicSphereEulerGaussInputs` (its field `eulerHat`), asserting that the spherical zeta integrals of the Fourier transform $`\hat\Phi`$ of the Gaussian test function factor as an Euler product with the **standard** local factors of $`Q_0`$ (those of the lattice $`\mathcal{O}_v^N`$):

```math
Z_{\hat\Phi}(s, c) = \kappa_h\, Z^{\mathrm{NF}}(s, \rho_c).
```

**Why it is false.** At the finite places $`\hat\Phi`$ (`gaussTestHat Q₀`) has the local lattices $`K_v = H^{-1}\mathfrak{d}_v^{-1}\mathcal{O}_v^N`$ ($`H`$ the Hessian of $`Q_0`$, $`\mathfrak{d}_v`$ the local different), not $`\mathcal{O}_v^N`$. Where $`K_v \ne \mathcal{O}_v^N`$, the ratio of the two local factors depends on the local square class of $`\rho`$, which no archimedean data and no constant can absorb.

**Counterexample.** $`F = \mathbb{Q}`$, $`Q_0 = x_0^2 + x_1^2 + x_2^2 + x_3^2 + 3x_4^2`$, and $`\rho = 1`$ versus $`\rho = 57`$ (same sign, same square class at $`2`$). At $`p = 3`$,

```math
\int_{K_3,\ Q \in 57\,\mathbb{Q}_3^{\times 2}} |Q|^s \ \ge\ c\, 3^{s}, \qquad \int_{\mathbb{Z}_3^5,\ Q \in 57\,\mathbb{Q}_3^{\times 2}} |Q|^s \ \le\ 3^{-s},
```

so the two sides of `eulerHat` cannot agree for both values of $`\rho`$.

**Weil's own statement is correct.** In *Adeles and Algebraic Groups* (§4.5, (1), p. 102, and p. 109) the local factors of $`\hat\Phi`$ are those of $`\hat\Phi_v`$, not the standard ones; the error was only in the repository's formulation of the input.

**Consequences.** Three theorems assumed this input and are therefore vacuous (their hypothesis can never be satisfied):

- `QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release` ($`\tau(\mathrm{SO}(V)) = 2`$ for $`n \ge 3`$, assuming the input),
- `QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release_totallyReal` (the same over totally real fields),
- `QuadFormsKB.Tamagawa.Measure.Weil.siegelIndefinite_release_totallyReal` (Siegel's formula for indefinite forms over totally real fields, assuming the input),

together with their variants with the suffix `_of_sphere`. They remain in the library (they are correct as implications) but are **not** headlines and are not in `Challenge.lean`.

**Replacements (unconditional).** Only the finiteness $`Z^+_{\hat\Phi}(1) < \infty`$ was ever needed, and it follows from the pointwise bound $`M_s\hat\Phi \le C\,M_s\Phi`$ (`QuadFormsKB.Tamagawa.Measure.Weil.mellinPhi_gaussTestHat_le`). The results are proved without any input:

- `QuadFormsKB.Tamagawa.Measure.Weil.tauTwoAll_release_uncond` and `tauTwoAll_release_totallyReal_uncond` (headline `QuadFormsKB.Headlines.tamagawa_two_numberField`),
- `QuadFormsKB.Tamagawa.Indefinite.siegelIndefinite_uncond` and `QuadFormsKB.Tamagawa.Measure.Weil.siegelIndefinite_release_totallyReal_uncond` (headline `QuadFormsKB.Headlines.siegel_indefinite_numberField`).

See [Tamagawa numbers](tamagawa-table.md) and [Siegel's formula for indefinite forms](siegel-indefinite.md).
