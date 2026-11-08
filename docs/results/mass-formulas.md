# Mass formulas

The **mass** of a genus of positive definite lattices is $`\sum_{L'} 1/|\mathrm{Aut}(L')|`$, the sum over the classes $`L'`$ in the genus. The library proves the mass formula in two kinds of form: Siegel's general form, which expresses the mass through local densities, and exact evaluations, which compute it in closed form from local invariants of the lattice. Every statement below is a headline of [`Challenge.lean`](../../Challenge.lean) (proved in [`Solution.lean`](../../Solution.lean)), checked by the Lean kernel with only the standard axioms and no unproved input. The headlines added in 0.4.0 are not yet reviewed by a human (see the README, Provenance).

## Siegel's general form (since 0.2.0)

- **Setting.** $`F`$ a totally real number field, $`Q_0`$ a totally positive definite form in $`n \ge 3`$ variables with coefficients in $`\mathcal{O}_F`$, $`L = \mathcal{O}_F^n`$; classes under the full orthogonal group.
- **Formula.** $`\sum_{L' \in \mathrm{Gen}(L)} 1/|\mathrm{O}(L')| = \big(|d_F|^{-n(n-1)/4} \prod_\sigma \mathrm{vol}(\mathrm{SO}(Q_0^\sigma)) \prod_{\mathfrak p} \alpha_{\mathfrak p}(Q_0, Q_0)\big)^{-1}`$, an Euler product of local densities $`\alpha_{\mathfrak p}`$ (it converges unconditionally); with $`\tau(\mathrm{SO}(Q_0)) = 2`$.
- **Lean.** `QuadFormsKB.Headlines.massFormula_totallyReal` ($`n \ge 4`$), `QuadFormsKB.Headlines.massFormula_totallyReal_ternary` ($`n = 3`$, new in 0.3.0). Details: [Tamagawa number and mass formula](tamagawa-mass-formula.md).

## Exact evaluations (new in 0.4.0)

### Over ℤ from the genus symbols (Conway and Sloane)

- **Source.** J. H. Conway and N. J. A. Sloane, "Low-dimensional lattices IV: the mass formula", Proc. R. Soc. Lond. A 419 (1988), formulas (2), (3), (6), (7).
- **Setting.** $`A`$ a symmetric $`n \times n`$ integer matrix, $`n \ge 3`$, with $`Q(x) = x^{\mathsf T}Ax`$ positive definite; a 2-adic genus symbol $`\tau`$ of $`A`$ and a $`p`$-adic symbol $`\sigma_p`$ for each odd prime $`p \mid \det A`$. Classes are $`\mathrm{GL}_n(\mathbb{Z})`$-classes of forms, with $`\mathrm{Aut}`$ including improper automorphisms.
- **Formula.** $`m(Q) = \mathrm{std}(n, \det A)\prod_{p \mid 2\det A} m_p/\mathrm{std}_p(n, \det A)`$, with $`\mathrm{std}`$ the standard mass (7), $`\mathrm{std}_p`$ the standard $`p`$-mass (6) and $`m_p`$ the $`p`$-mass (3) of the symbol (diagonal factors by Tables 1 and 2, cross terms, and the type factor at $`p = 2`$). The paper states (3) at $`p = 2`$ without proof; it is proved here. The headline also states that the genus has finitely many classes and positive mass.
- **Lean.** `QuadFormsKB.Headlines.massFormula_genusSymbols`, from `QuadFormsKB.ConwaySloane.Mass.mass_eq_stdMass_mul_symbols_unconditional`.

### Shimura's exact formula for SO over totally real fields (Gan, Hanke and Yu)

- **Source.** W. T. Gan, J. Hanke and J.-K. Yu, "On an exact mass formula of Shimura", Duke Math. J. 107 (2001), Propositions 7.4 and 7.5.
- **Setting.** $`F`$ totally real of degree $`d`$, $`Q_0`$ nondegenerate and totally positive definite in $`n`$ variables over $`\mathcal{O}_F`$, with $`L = \mathcal{O}_F^n`$ a maximal lattice. The mass is $`\sum_i 1/|\Gamma_i|`$ over the proper classes in the genus, $`\Gamma_i = \mathrm{SO}(L_i)`$.
- **Formula.** $`\sum_i 1/|\Gamma_i| = 2^{-kd}\,|L(M)|\,\tau(\mathrm{SO})\prod_{\mathfrak p}\lambda_{\mathfrak p}`$, $`\tau(\mathrm{SO}) = 2`$, with
  - $`n = 2k + 1 \ge 3`$ odd: $`|L(M)| = \prod_{r=1}^{k}|\zeta_F(1 - 2r)|`$;
  - $`n = 2k \ge 4`$ even: $`|L(M)| = \prod_{r=1}^{k-1}|\zeta_F(1 - 2r)| \cdot |L_F(1 - k, \chi)|`$, $`\chi`$ the quadratic character of $`F(\sqrt{\delta})`$, $`\delta = (-1)^k\det(H)/2^n`$;

  and $`\lambda_{\mathfrak p}`$ the local factors of Gan, Hanke and Yu ($`1`$ for all but finitely many $`\mathfrak p`$). The values at negative integers are written through the functional equations; the paper's $`L(M)`$ is read in absolute value. The headlines also state that there are finitely many classes and that every $`\Gamma_i`$ is finite.
- **Lean.** `QuadFormsKB.Headlines.shimuraMass_odd` (from `QuadFormsKB.Hanke2005.ghy_prop74`), `QuadFormsKB.Headlines.shimuraMass_even` (from `QuadFormsKB.Hanke2005.ghy_prop75_proved`).

### Hanke's exact formula over every number field, corrected general form

- **Source.** J. Hanke, "An exact mass formula for quadratic forms over number fields", J. Reine Angew. Math. 584 (2005), Theorem 5.1.
- **Setting.** $`F`$ any number field, $`Q_0`$ nondegenerate in $`n \ge 3`$ variables over $`\mathcal{O}_F`$, of any signature, with $`L = \mathcal{O}_F^n`$ maximal. Hanke's mass is the sum over the proper classes in the genus of the covolumes of the unit groups in the archimedean group, normalized by the volume of a maximal compact subgroup; for totally definite forms it is $`\sum_i 1/|\Gamma_i|`$.
- **Formula.** Hanke's closed form: a power of $`|d_F|`$, the values $`\zeta_F(2j)`$, the index $`[\tilde L : L]`$ of $`L`$ in its dual, local factors $`\lambda'_{\mathfrak p}`$, factors at the real and complex places, and for even $`n`$ the value $`L_F(n/2, \chi)`$ (displayed in the docstring of the headline).
- **Correction to the printed theorem.** Theorem 5.1 as printed omits Shimura's hypothesis that, for odd $`n`$, the determinant of $`Q_0`$ is at every prime a unit times a square, and it is false without it. The headline needs no such hypothesis: at the primes where the condition fails, Hanke's $`\lambda_{\mathfrak p}`$ is replaced by $`\lambda'_{\mathfrak p} = (1 + q^{-m})/2`$ if the anisotropic kernel at $`\mathfrak p`$ has dimension $`1`$ and $`(1 - q^{-m})/2`$ if it has dimension $`3`$ ($`m = \lfloor n/2 \rfloor`$, $`q = N\mathfrak p`$; from Gan, Hanke and Yu, Table 4); elsewhere $`\lambda'_{\mathfrak p} = \lambda_{\mathfrak p}`$. Under Shimura's hypothesis the formula is the printed one.
- **Lean.** `QuadFormsKB.Headlines.hankeMass_numberField`, from `QuadFormsKB.Hanke2005.theorem51_general`.
