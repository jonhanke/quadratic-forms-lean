/-
# Hanke, *Quadratic Forms and Automorphic Forms* (AWS 2009): the derivations D1–D24

J. Hanke, *Quadratic Forms and Automorphic Forms*, expanded notes from the 2009 Arizona Winter
School, arXiv:1105.5759 v3 (bibkey `hanke2011aws`; PDF page numbers = printed page numbers).

Below, every derivation or calculation of §2.6, §2.7, §3.5 and Ch. 4 is listed with its locator,
what it computes, what it assumes, and how it is formalized. **Status**: *proved* = no hypotheses
beyond the stated mathematical ones; *relative to …* = proved from the named input structures or
hypotheses (no new axioms and no unproved placeholders). The inputs are listed at the end.

## §2.6 Mass formulas (pp. 34–35) — `AWS/Measures.lean`

- **D1** (2.8), p. 34: $a_E(Q) = \frac{\sum r_{Q''}(Q)/|\mathrm{Aut}Q''|}{\sum 1/|\mathrm{Aut}Q''|} = 1/\mathrm{Mass}(Q)$,
  using $r_{Q''}(Q) = \#\mathrm{Aut}(Q)$ or $0$. Assumes: class representatives of equal nonzero
  determinant, finite $\mathrm{Aut}$. Formalized with Hessians: `reps`, `autZ`, `EquivZ`, `mass`,
  `card_reps_of_equiv`, `card_reps_of_not_equiv`, `eisenstein_coeff_self`. **Proved.** For positive
  definite forms the finiteness of $\mathrm{Aut}$ is proved (`finite_autZ`): `eisenstein_coeff_self_uncond`.
- **D2** p. 35: $\mathrm{Mass}(Q) \le h(Q)/2$ (since $\pm 1 \in \mathrm{Aut}$). `mass_le_half_classNumber`.
  **Proved** ($n \ge 1$).

## §2.7 The sum of four squares (pp. 35–40) — `AWS/Measures.lean`, `AWS/FourSquares.lean`

- **D3** §2.7.1, p. 36: $\mu_{\mathbb{Z}_p}(p^i\mathbb{Z}_p) = p^{-i}$, $\mu_{\mathbb{Z}_p^n}(p^i\mathbb{Z}_p^n) = p^{-ni}$
  for the normalized additive Haar measure (coset decomposition). `measure_span_pow`,
  `measure_pi_span_pow`. **Proved** for every translation-invariant measure of total mass 1.
- **D4** (2.9), p. 37: $\beta_\infty(m) = \pi^2 m$ from $\mathrm{Vol}(B_{4,r}) = \frac{\pi^2}{2}r^4$.
  `betaInf_calc`: the algebra (exact for each $\varepsilon$). **Proved** (the ball volume itself is
  taken from the notes, not formalized).
- **D5** Lemma 2.7.2, pp. 37–38: $\mathrm{Vol}(Q^{-1}(U_i))/\mathrm{Vol}(U_i) = r_{p^i}(m)/p^{(n-1)i}$; hence the
  notes' $\beta_p$ is the repo's `LocalDensity.localDensity`. `vol_preimage_div_vol`,
  `beta_eq_localDensity`. **Proved.**
- **D6** Lemma 2.7.4, p. 38: $\beta_p(m) = 1 - p^{-2}$ ($p \nmid m$), $(1-p^{-2})(1+p^{-1})$ ($p \parallel m$),
  $p$ odd. `beta_odd_unit`, `beta_odd_ord_one`. **Proved** from the Hanke 2004 formalization
  (`LocalDensity.localDensity_diag_even_unit`, `…_ord_one`).
- **D7** (2.10)–(2.23), pp. 39–40: $r_Q(1) = 8$, $r_Q(p) = 8(p+1)$, $r_Q(t) = 8\prod_{p\mid t}(p+1)$
  ($t$ odd squarefree), via $\prod_p(1-p^{-2}) = 6/\pi^2$. `r4_one`, `r4_prime`, `r4_squarefree`.
  **Relative to** `FourSquaresInputs` (Siegel's formula for $Q$; Lemma 2.7.6 at odd $m$); both fields are
  **proved** in `Siegel/FourSquaresSiegel.lean` (`Siegel.fourSquaresInputs`, from Jacobi's theorem and the local
  densities at all primes and all $m$), so D7 holds unconditionally.

## §3.5 Spinor equivalence (pp. 52–53) — `AWS/DoubleCosets.lean`

- **D8** p. 53: class $\subseteq$ spinor genus $\subseteq$ genus (the local equivalences are weaker).
  `classOf`, `spinorGenus`, `class_subset_spinorGenus`, `spinorGenus_subset_genus`, for any group
  with subgroups $\Gamma$ (rational isometries) and $\kappa$ (adelic spinor kernel). **Proved.**
  (Eichler's Theorem 3.5.1 is cited by the notes, not derived; not formalized.)

## §4.1–§4.2 Classical to adelic forms (pp. 55–58) — `AWS/ClassicalToAdelic.lean`, `AWS/DoubleCosets.lean`

- **D9** (4.1) and p. 56: for $f|_k\gamma = \chi(d)f$ on $\Gamma_0(N)$, $\tilde f(g) := (f|_kg)(i)$ has
  $\tilde f(\gamma g) = \chi(d)\tilde f(g)$, $g \in \mathrm{GL}_2^+(\mathbb{R})$. `HasNebentypus`, `liftGL`,
  `liftGL_mul` (Mathlib's slash action). **Proved.**
- **D10** p. 57: $\gamma \mapsto \chi(d_\gamma)$ is a character of $\Gamma_0(N)$. `charGamma0`. **Proved**
  (Mathlib's `Gamma0Map`).
- **D11** (4.2) and the bullets, p. 57: the adelic lift $\mathcal{F}$, left $\mathrm{SL}_2(\mathbb{Q})$-invariant,
  $\mathcal{F}(gk_f) = \varepsilon(k_f)^{-1}\mathcal{F}(g)$ (erratum: printed $\chi(k_f)$).
  `exists_unique_lift`, `lift_mul_right` (abstract, **proved**); `AdelicSL2Data`, `phiU`,
  `phiU_left`, `phiU_right`, `adelicLift_exists`, `printed_right_equivariance_forces`
  (**relative to** strong approximation for $\mathrm{SL}_2$ and $\mathrm{SL}_2(\mathbb{Q}) \cap U = \Gamma_0(N)$,
  as hypotheses `hSA`, `hΓU`).
- **D12** conditions (1)–(3), pp. 57–58: `IsAdelicAutomorphic` (conditions (4)–(5) omitted, as the
  notes allow for definite orthogonal groups). Definition.

## §4.3 The Weil representation (pp. 58–59) — `AWS/AdelicExp.lean`, `AWS/ThetaLift.lean`

- **D13** p. 59: $e_\mathbb{A}$ and $\chi_V$ are trivial on rational elements: $x - \sum_p\mathrm{Frac}_p(x) \in \mathbb{Z}$,
  $e_\mathbb{A}(x) = 1$; $\prod_v (a,d)_v = 1$. `sub_sum_frac_isInt`, `adelicExp_rat` (**proved**),
  `chiV_rat` (**proved**, = the repo's Hilbert reciprocity). The product formula $|a|_\mathbb{A} = 1$ is
  not formalized. Formulas 1–2 at $\infty$: `weilN`, `weilM` (definitions).

## §4.4 Theta kernels and lifts (pp. 60–61) — `AWS/ThetaLift.lean`

- **D14** Lemma 4.4.1, pp. 60–61: $\theta_\varphi$ is left $O(V)$-invariant ("permutes $V(F)$").
  `thetaKernel`, `thetaKernel_left_inv`. **Proved.** The $\mathrm{Sp}(W)$-half (Poisson summation) is a
  hypothesis of D21. The lift (4.3) is `QuotientIntegralInputs.I` applied to $F\cdot\theta$
  (erratum: (4.3) prints $F(g_\mathbb{A})$ for $F(h_\mathbb{A})$).

## §4.5 Simple automorphic forms on $O(V)$ (pp. 61–62) — `AWS/Adelic.lean`, `AWS/DoubleCosets.lean`

- **D15** Lemma 4.5.1, p. 61: lattices $\leftrightarrow$ local lattices. `Lat`, `LocLat`, `loc`;
  `mem_iff_forall_loc` ($L = \bigcap_p(V \cap L_p)$), `loc_injective`, `loc_eventually_std`
  (**proved**); existence of gluing `LatticeGluing` is **proved** too (`latticeGluing`,
  `AWS/Gluing.lean`).
- **D16** Lemma 4.5.2 and the bijections, p. 62: orbit = genus; $O(V_\mathbb{A})/K_\mathbb{A} \simeq \mathrm{Gen}(L)$;
  $O(V)\backslash O(V_\mathbb{A})/K_\mathbb{A} \simeq$ classes in $\mathrm{Gen}(L)$. `orthGroup`, `intStab`, `OAf`, `OA`,
  `KA`, `diag`, `ratPoints`, `latAction`, `diag_smul`, `latGenus`, `orbit_eq_genus`, `stabilizer_std`,
  `quotientStabilizerEquivOrbit`, `dosetEquivClasses` (abstract, **proved**),
  `dosetEquivClassesInGenus` (stated relative to `LatticeGluing`; **unconditional** versions
  `latAction'`, `diag_smul'`, `orbit_eq_genus'`, `stabilizer_std'`, `dosetEquivClassesInGenus'` in
  `AWS/Gluing.lean`).
- **D17** p. 62: $\Phi_{L_i}$ and $1$ are adelic automorphic forms. `dosetIndicator`,
  `isAdelicAutomorphic_of_biInvariant`, `isAdelicAutomorphic_indicator_doset`. **Proved.**

## §4.6 Classical theta functions as theta lifts (pp. 63–66) — `AWS/Unfolding.lean`, `AWS/ThetaLift.lean`

- **D18** (4.5)–(4.13), pp. 63–64: $\int_{\Gamma\backslash G}F = \sum_i |\Gamma_i|^{-1}\int_K F(\alpha_ih)\,dh$.
  `integral_eq_sum_doset`; with (4.11) $\Gamma \cap \alpha K\alpha^{-1} = \mathrm{Aut}(\alpha L)$: `card_stabilizer_smul`,
  `card_aut_eq`. **Relative to** `QuotientIntegralInputs` (Weil's formula, left Haar measure,
  $\mathrm{vol}(K) = 1$).
- **D19** (4.14)–(4.17), p. 64: only $i = j$ survives. `mem_doset_mul_iff` (**proved**),
  `integral_indicator_mul` (**relative to** `QuotientIntegralInputs`).
- **D20** (4.18)–(4.22), p. 64: $\theta(g_{\infty,z},\alpha_jh) = \sum_{\vec v\in L_j} y^{n/4}e^{2\pi izQ(\vec v)}$
  for $h \in K_\mathbb{A}$. `thetaKernel_mul_mem`, `mem_latSMul_std_iff` (relative to `LatticeGluing`);
  **unconditional**: `thetaKernel_mul_mem'`.
- **D21** (4.23), p. 65: via strong approximation the lift depends only on $g_\infty$.
  `thetaLift_depends_only_on_infty`. **Relative to** hypotheses (strong approximation for
  $\mathrm{SL}_2$, $\mathrm{Sp}(W)$-invariance of $\theta$, $K_f$-invariance; see the update there).
- **D22** (4.24)–(4.30), p. 65: $(W(g_{\infty,z})\varphi_\infty)(h_\infty^{-1}\vec v) = y^{n/4}e^{2\pi izQ(\vec v)}$.
  `weilGauss`, `weil_gaussian` (**proved**; $W$ on the Borel given by formulas 1–2); errata checks
  `weil_gaussian_pi`, `weil_gaussian_pi_ne`.
- **D23** (4.31)–(4.37), pp. 65–66: $y^{-n/4}\Theta(\Phi_{L_j})(g_{\infty,z}) = \Theta_{L_j}(z)/|\mathrm{Aut}(L_j)|$, with
  $g_{\infty,z}\cdot i = z$ and $(ci+d)^{n/2} = y^{-n/4}$. `thetaSeries`, `AWSInputs`,
  `thetaLift_indicator_eq`, `thetaLift_classical`, `gInf`, `gInf_smul_I`, `gInf_denom`,
  `exists_rep_infty_one`. **Relative to** `QuotientIntegralInputs` and `AWSInputs`. For positive definite
  $Q$, **relative to** `QuotientIntegralInputs` only (`AWS/Finiteness.lean`): `thetaLift_indicator_eq_posDef`,
  `thetaLift_classical_posDef`; the representatives exist (`exists_doset_reps`).
- **D24** (corollary; p. 62 "the constant function 1"): $\mathrm{vol}(O(V)\backslash O(V_\mathbb{A})) = \mathrm{Mass}(L)$
  and $y^{-n/4}\Theta(1) = \sum_j \Theta_{L_j}/|\mathrm{Aut}(L_j)|$. `integral_one_eq_mass`,
  `integral_eq_sum_integral_indicator_mul`, `thetaLift_one`. **Relative to** the same inputs; for positive
  definite $Q$ relative to `QuotientIntegralInputs` only: `integral_one_eq_mass_posDef`, `thetaLift_one_posDef`.

## The inputs (all hypotheses, none an `axiom`)

1. `QuotientIntegralInputs Γ K μ` (`AWS/Unfolding.lean`): the integral over $\Gamma\backslash G$, with
   Weil's formula $I(\sum_\gamma f(\gamma\,\cdot)) = \int_G f\,d\mu$, $\mu$ left-invariant, $K$ measurable,
   $\mu(K) = 1$.
2. `LatticeGluing n` (`AWS/Adelic.lean`): Lemma 4.5.1, existence half. **Proved** (`latticeGluing`,
   `AWS/Gluing.lean`), so it is no longer an input.
3. `AWSInputs Q` (`AWS/ThetaLift.lean`): `gluing` (= 2, proved; `AWSInputs.ofFinite` builds the bundle
   from the other two fields), `finite_classes` (finite class number),
   `finite_aut` (finite $\mathrm{Aut}(L')$). **Proved for positive definite $Q$** (`awsInputs_of_posDef`,
   `AWS/Finiteness.lean`: Hermite reduction and short vectors); `finite_aut` is false for indefinite $Q$
   (e.g. $x_0^2 - 2x_1^2$), so the bundle stays a hypothesis of the general statements.
4. `AdelicSL2Data N χ` with hypotheses `hSA`, `hΓU` (`AWS/ClassicalToAdelic.lean`): $K_f(N)$, its
   character $\varepsilon$, the diagonal $\Gamma_0(N)$, strong approximation for $\mathrm{SL}_2$,
   $\mathrm{SL}_2(\mathbb{Q}) \cap U = \Gamma_0(N)$.
5. Hypotheses of `thetaLift_depends_only_on_infty` (D21): strong approximation, $\mathrm{Sp}(W)$- and
   $K_f$-invariance of the kernel.
6. `FourSquaresInputs` (`AWS/FourSquares.lean`): Siegel's formula for $x^2+y^2+z^2+w^2$ with
   $\beta_\infty(m) = \pi^2 m$; $\beta_2(m) = 1$ for odd $m$ (Lemma 2.7.6).
-/
import QuadFormsKB.Literature.AWS.ThetaLift
import QuadFormsKB.Literature.AWS.ClassicalToAdelic
import QuadFormsKB.Literature.AWS.Measures
import QuadFormsKB.Literature.AWS.AdelicExp
import QuadFormsKB.Literature.AWS.FourSquares
