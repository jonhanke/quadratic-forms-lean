# Siegel's formula for indefinite forms over every number field

Siegel's formula in its measure form (Siegel 1935–1936; Weil 1965), for quadratic forms of any signature over every number field: the number of representations of a number, or of a form, by the classes in a genus, each measured by the volume of the stabilizers modulo the units, equals a product of local densities times the total volume of the unit groups. The statements are organised by the rank of the stabilizer $`\mathrm{SO}(\Xi^\perp)`$ of a representation $`\Xi`$, $`n' = N - r`$ (forms in $`N`$ variables representing forms of rank $`r`$).

## Statement

Let $`F`$ be a number field, $`Q_0`$ a nondegenerate quadratic form over the ring of integers of $`F`$ in $`N`$ variables (any signature), $`L`$ the standard lattice, and $`M_i`$ the proper classes in the genus of $`L`$. Let $`T_0`$ be a nondegenerate form of rank $`r`$ over the ring of integers, represented by $`Q_0`$ over $`F`$. With $`v(M_i)`$ the volume of $`\mathrm{SO}(M_i)\backslash \mathrm{SO}(V)(F_\infty)`$ for Weil's archimedean Tamagawa measure and $`\rho(M_i, T_0)`$ Siegel's measure of representations (the sum, over the unit-group orbits of the representations of $`T_0`$ by $`M_i`$, of the volumes of the stabilizers modulo their units):

| $`n' = N - r`$ | Formula |
|---|---|
| $`n' \ge 3`$ | $`c_\infty(T_0)\sum_i\rho(M_i, T_0) = \lvert d_F\rvert^{-(N(N-1)-n'(n'-1))/4}\prod_{\mathfrak p}\beta_{\mathfrak p}(L, T_0)\cdot\sum_i v(M_i)`$ |
| $`n' = 2`$, $`\delta`$ not a square | $`c_\infty(T_0)\sum_i\rho(M_i, T_0) = \lvert d_F\rvert^{-(N(N-1)-2)/4}\, L_F(1,\chi_\delta)\prod_{\mathfrak p}\beta_{\mathfrak p}(L, T_0)(1 - \chi_\delta(\mathfrak p)/N\mathfrak p)\cdot\sum_i v(M_i)`$ |
| $`n' = 2`$, $`\delta`$ a square | $`2\,c_\infty(T_0)\sum_i\rho^1(M_i, T_0) = \lvert d_F\rvert^{-(N(N-1)-2)/4}\, \rho_F\prod_{\mathfrak p}\beta_{\mathfrak p}(L, T_0)(1 - N\mathfrak p^{-1})\cdot\sum_i v(M_i)`$ |
| $`n' = 1`$ | $`c^{(1)}_\infty(Q_0)\sum_i n(M_i, T_0) = \tfrac12\lvert d_F\rvert^{-N(N-1)/4}\prod_{\mathfrak p}\beta_{\mathfrak p}(L, T_0)\cdot\sum_i v(M_i)`$ ($`N \ge 3`$); for $`N = 2`$, $`V`$ anisotropic, the product regularized by $`L_F(1,\chi_E)^{-1}`$ |
| $`n' = 0`$ | $`\sum_i n(M_i, T_0) = \prod_{w\mid\infty}\lvert\det\Xi\rvert_w^{-1}\prod_{\mathfrak p}\tfrac12\beta_{\mathfrak p}(L, T_0)\cdot\sum_i v(M_i)`$ ($`N \ge 3`$) |

Here $`\delta = -\det H_{Q_0}\det H_{T_0}`$, $`\chi_\delta`$ its quadratic character, $`\rho_F`$ the residue of $`\zeta_F`$ at $`1`$, $`\rho^1`$ the measure of representations for the norm-one stabilizers, $`n(M_i, T_0)`$ the number of representations modulo the units, $`\beta_{\mathfrak p}`$ the local densities, and $`c_\infty`$ explicit archimedean constants ($`|d_F|^{-N(N-1)/4}`$ times normalized archimedean absolute values of $`2m`$, $`\det H_{T_0}`$ or $`\det H_{Q_0}`$). For numbers ($`r = 1`$, $`T_0 = \langle m\rangle`$) the first row is Siegel's Hauptsatz for indefinite forms in $`N \ge 4`$ variables, and the two $`n' = 2`$ rows are ternary forms with $`m^\perp`$ anisotropic, respectively isotropic (Siegel's excluded case, regularized).

## Scope and hypotheses

- Every number field, every signature (at a complex place every form is indefinite), every class number; the only hypothesis is that $`T_0`$ is represented over $`F`$ (a rational frame), which is necessary for the formula to say anything.
- The sums over the classes are sums in $`[0, \infty]`$; the headline statements also state $`0 < \sum_i v(M_i) < \infty`$, that the products of local densities (plain or regularized) converge unconditionally, and that $`L_F(1,\chi)`$ exists and is positive.
- Not stated as headlines (no library lemma yet): the finiteness of the number of proper classes for indefinite $`Q_0`$ (the library proves it for classes under the full orthogonal group).
- Siegel's formula for **definite** forms representing **forms** over totally real fields (every rank $`1 \le r \le N`$) is also proved: `QuadFormsKB.Tamagawa.Frames.siegelForms_all_ranks`; the headline `QuadFormsKB.Headlines.siegelForms_totallyReal` states the case $`N \ge 3`$, $`N - r \ne 2`$.

## In Lean

The headline statements are in [`Challenge.lean`](../../Challenge.lean), section "Siegel's formula for indefinite forms over every number field":

- `QuadFormsKB.Headlines.siegel_indefinite_numberField` (from `QuadFormsKB.Tamagawa.Indefinite.siegelIndefinite_uncond`): numbers, $`N \ge 4`$.
- `QuadFormsKB.Headlines.siegel_indefinite_forms_numberField` (`siegelIndefiniteForms_uncond`): forms, $`n' \ge 3`$.
- `QuadFormsKB.Headlines.siegel_indefinite_forms_rank2` (`siegelIndefiniteForms_rank2_uncond`) and `QuadFormsKB.Headlines.siegel_indefinite_ternary` (`siegelIndefinite_ternary_uncond`): $`n' = 2`$, anisotropic stabilizer.
- `QuadFormsKB.Headlines.siegel_indefinite_forms_rank2_isotropic` (`siegelIndefiniteForms_rank2_isotropic_uncond`) and `QuadFormsKB.Headlines.siegel_indefinite_ternary_isotropic` (`siegelIndefinite_ternary_isotropic_uncond`): $`n' = 2`$, isotropic stabilizer, regularized.
- `QuadFormsKB.Headlines.siegel_indefinite_forms_corank1` (`siegelIndefiniteForms_corank1_uncond`) and `QuadFormsKB.Headlines.siegel_indefinite_binary` (`siegelIndefinite_binary_uncond`): $`n' = 1`$.
- `QuadFormsKB.Headlines.siegel_indefinite_forms_corank0` (`siegelIndefiniteForms_corank0_uncond`): $`n' = 0`$.
- `QuadFormsKB.Headlines.siegelForms_totallyReal` (`QuadFormsKB.Tamagawa.Frames.siegelForms_all_ranks`): definite forms by forms over totally real fields.

## Proof outline

Weil's adelic route. The adelic theta integral of a Schwartz–Bruhat function over $`\mathrm{SO}(V)(F)\backslash\mathrm{SO}(V)(\mathbb{A})`$ is unfolded in two ways: over the classes in the genus (giving the measures of representations and the unit volumes), and over the rational representations (giving the stabilizers and the local densities, through Weil's fibration of the Tamagawa measure over the orbits). The values $`\tau(\mathrm{SO}(V)) = 2`$ and $`\tau(\mathrm{SO}(\Xi^\perp))`$ ($`2`$ for $`n' \ge 3`$; $`2`$ with $`L_F(1,\chi)`$ or $`1`$ with $`\rho_F`$ for $`n' = 2`$; $`1`$ for $`n' = 1, 0`$) from the [Tamagawa table](tamagawa-table.md) give the constants, including Siegel's factor $`\tfrac12`$ in coranks $`0`$ and $`1`$.

## References

- C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36 (1935), and *II*, Ann. of Math. 37 (1936) (indefinite forms) [unverified locator].
- C. L. Siegel, *On the theory of indefinite quadratic forms*, Ann. of Math. 45 (1944), 577–622 [unverified locator] (the case of an isotropic binary stabilizer).
- A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965) [unverified locator]; *Adeles and Algebraic Groups*, Birkhäuser, 1982.

Bibliographic entries are in [references.bib](../../references.bib). Related: [Tamagawa table](tamagawa-table.md), [Siegel's theorem over totally real fields](siegel-totally-real.md), [classical cases](classical-cases.md).
