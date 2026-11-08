import QuadFormsKB.Tamagawa.Measure.Weil.SpaceHeadlines
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSOCorollaries
import QuadFormsKB.Tamagawa.InputsFollowup
import QuadFormsKB.Tamagawa.TernaryRamDyadicLocal

/-!
# Cassels, Appendix B, §4: Theorem 4.1 ($\tau = 2$) and its consequences, unconditionally

Cassels, *Rational Quadratic Forms*, Appendix B, §4, pp. 379–382. For a regular quadratic space $(V, \phi)$ of
dimension $n$ over $\mathbb Q$, Cassels defines the adele group $O^+_{\mathbb A}$ (components $\alpha_p \in O^+(V_p)$ for
all $p \le \infty$, almost all in $O^+(\Lambda_p)$), the Tamagawa measure $\tau$ on it (from an invariant differential
$\omega$ of degree $N = n(n-1)/2$ defined over $\mathbb Q$, independent of $\omega$ by the product formula), and states

**Theorem 4.1** (p. 380, (4.4)): $\tau(O^+_{\mathbb A}/O^+(V)) = 2$.

He gives no proof (Weil 1961, Kneser 1974), and notes that the convergence of $\prod_p \mu_p(O^+(\Lambda_p))$ holds
"with certain caveats if $n = 2$". He then sketches the deduction of Siegel's formulae (3.2) (the weight of a genus)
and (3.13) from Theorem 4.1.

## What is here

The library proves Weil's theorem unconditionally (`Tamagawa/Measure/Weil/`): for every number field $F$ and
every nondegenerate quadratic space $(V, Q)$ over $F$ of dimension $\ge 3$, every integral model $Q_0$ of $(V, Q)$ has
$\mathrm{covol}(SO(V)(F), SO(V)(\mathbb A), \mu_{\mathrm{Tam}}) = 2$ (`Measure.Weil.tauTwo_space_uncond`). Cassels'
$O^+$ is $SO$, his $O^+_{\mathbb A}/O^+(V)$ is the quotient whose covolume this is, and his $\tau$ is Weil's Tamagawa
measure with convergence factors $1$ (`muTam … fun _ => 1`). This file restates the result over $\mathbb Q$ with a
Cassels citation, and records the consequences Cassels draws in §§3–4, now unconditional:

* **`thm_4_1`**: Theorem 4.1 for every regular rational quadratic space of dimension $n \ge 3$;
* `thm_4_1_posDef`: Theorem 4.1 in the mass normalization of the library (`Tamagawa.TamagawaNumberTwo`,
  $\tau(SO) = \mu(K_{SO})\cdot \mathrm{mass}_{SO}$) for a positive definite integral form in $n \ge 3$ variables;
* `thm_4_1_adelic_posDef`: the same in the adelic normalization (`TamagawaNumberTwoAdelic`);
* `massFormula_uncond`, `massFormula_odd_uncond`, `massFormula_even_uncond`: the weight formula (3.2) (and its
  explicit odd/even forms), from Theorem 4.1 as Cassels deduces it (4.11)–(4.16), for positive definite forms in
  $n \ge 3$ variables;
* `siegelFormulaAt_uncond`: Siegel's formula (3.13) for numbers ($l = 1$), $n \ge 4$.

## Scope (dimension)

The statement is for $n \ge 3$. For $n = 1$, $O^+ = 1$ and $\tau = 1$ (`Measure.Weil.tauOne_space_rankOne`), so
Theorem 4.1 is false as printed; for $n = 2$ the group $O^+$ is a torus and, when $V$ is isotropic,
$O^+_{\mathbb A}/O^+(V)$ has infinite measure (these are Cassels' "caveats if $n = 2$"). Cassels' Appendix B treats
$n \ge 2$ implicitly through these caveats; the statement $n \ge 3$ is the one Weil and Kneser prove (*Update:* missing hypothesis $n \ge 3$).
-/

noncomputable section

namespace QuadFormsKB.Cassels.AppBThm41

open NumberField IsDedekindDomain QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Lattices
  QuadFormsKB.HilbertModular

/-- **Cassels, App. B, Theorem 4.1** (p. 380, (4.4)): *$\tau(O^+_{\mathbb A}/O^+(V)) = 2$*, for every regular
quadratic space $(V, Q)$ over $\mathbb Q$ of dimension $n = \dim_{\mathbb Q} V \ge 3$. Arguments: `V` a
finite-dimensional $\mathbb Q$-vector space, `hV` ($\dim V \ge 3$), `Q` a quadratic form on `V`, `hQ` (regular: the
polar bilinear form $B_Q(x, y) = Q(x+y) - Q(x) - Q(y)$ is nondegenerate). Conclusion `TamagawaNumberTwoSpace Q`:
$(V, Q)$ has an integral model, and for every integral model $Q_0$ (a basis of $V$ and $d \ne 0$ with $Q_0 = d\,Q$
integral in its coordinates) the covolume of $O^+(V) = SO(V)(\mathbb Q)$ in $O^+_{\mathbb A} = SO(V)(\mathbb A)$ for the
Tamagawa measure is $2$. **Unconditional**, every signature (Weil's theorem as proved in the library,
`Measure.Weil.tauTwo_space_uncond`). *Update:* the hypothesis $n \ge 3$ is needed and is not printed: for $n = 1$
the value is $1$, and for isotropic $n = 2$ the quotient has infinite measure. -/
@[kb "cassels1978" "App. B, §4, Thm. 4.1, (4.4), p. 380 (n ≥ 3; proved)"]
theorem thm_4_1 {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (hV : 3 ≤ Module.finrank ℚ V) (Q : QuadraticForm ℚ V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : TamagawaNumberTwoSpace Q :=
  tauTwo_space_uncond hV Q hQ

/-- **Cassels, App. B, Theorem 4.1, positive definite forms, mass normalization** (p. 380): for a positive definite
integral quadratic form $Q_0$ over $\mathbb Z = \mathcal O_{\mathbb Q}$ in $N \ge 3$ variables (`hN`, `Q₀`, `hpd`),
$\tau(SO) = 2$ in the normalization `Tamagawa.TamagawaNumberTwo` ($\tau(SO) = \mu_{\mathrm{Tam}}(K_{SO}) \cdot
\mathrm{mass}_{SO}$, the form in which Cassels uses it in (4.11)–(4.16)). **Unconditional.** -/
@[kb "cassels1978" "App. B, §4, Thm. 4.1, p. 380 (positive definite, mass normalization; proved)"]
theorem thm_4_1_posDef {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) :
    TamagawaNumberTwo Q₀ :=
  tamagawaNumberTwo_rat_all_ranks_uncond hN Q₀ hpd

/-- **Cassels, App. B, Theorem 4.1, positive definite forms, adelic normalization** (p. 380): for $Q_0$ as in
`thm_4_1_posDef` and nondegenerate (`hQ`), the covolume of $SO(Q_0)(\mathbb Q)$ in $SO(Q_0)(\mathbb A)$ for the
Tamagawa measure is $2$ (`TamagawaNumberTwoAdelic`). **Unconditional.** -/
@[kb "cassels1978" "App. B, §4, Thm. 4.1, (4.4), p. 380 (positive definite, adelic covolume; proved)"]
theorem thm_4_1_adelic_posDef {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (formF Q₀)) : TamagawaNumberTwoAdelic Q₀ hQ :=
  tamagawaNumberTwoAdelic_rat hN Q₀ hQ hpd

/-- **Cassels, App. B, (3.2): the weight of a genus, unconditionally** (p. 375; deduced from Theorem 4.1 by
(4.11)–(4.16), pp. 380–382): for a positive definite form $Q_0$ over $\mathbb Z$ in $N \ge 3$ variables (`hN`, `Q₀`,
`hpd`), the mass $\sum_{\text{classes in the genus of } L} 1/|O(M)|$ of $L = \mathbb Z^N$ equals
$\mu_{\mathrm{Tam}}(K_{SO})^{-1}$, the inverse of the product of the local Tamagawa volumes (Cassels' $\prod_p d_p$
and $g_\infty$ of (4.15)–(4.16)). The library's mass is over $GL_N$-classes, half of Cassels' weight over proper
classes (see `Tamagawa.mass_SO_eq_two_mul_mass`). **Unconditional** (from `thm_4_1_posDef`). -/
@[kb "cassels1978" "App. B, (3.2), p. 375, via Thm. 4.1, (4.11)–(4.16), pp. 380–382 (n ≥ 3; proved)"]
theorem massFormula_uncond {N : ℕ} (hN : 3 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀)) :
    MassFormulaHolds Q₀ :=
  massFormulaHolds_totallyReal hN Q₀ hpd

/-- **Cassels, App. B, (3.2)–(3.3), explicit form for odd $n = 2m + 1 \ge 3$, unconditionally**: `Tamagawa.massFormula_odd`
with its hypothesis $\tau(SO) = 2$ discharged by `thm_4_1_posDef`. Arguments: `m` ($m \ge 1$, `hm`), `Q₀`, `hQ`
(nondegenerate), `hpd` (positive definite), `hLi` ($\mathbb Z^n$ integral for $Q_0$). -/
@[kb "cassels1978" "App. B, (3.2), p. 375 (explicit form, n = 2m + 1 ≥ 3; proved)"]
theorem massFormula_odd_uncond (m : ℕ) (hm : 1 ≤ m) (Q₀ : QuadForm (𝓞 ℚ) (2 * m + 1)) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)))
    (hLi : Lattices.IsIntegral (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (Tamagawa.stdLat ℚ (2 * m + 1)).1) :
    mass (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (Tamagawa.stdLat ℚ (2 * m + 1)) =
      (|(discr ℚ : ℝ)|) ^ (((2 * m + 1 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) - 1) / 4) *
      (∏ σ : ℚ →ₐ[ℚ] ℂ, archVolSO (2 * m + 1) (detGram Q₀ σ))⁻¹ *
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericOdd m v)⁻¹ *
      ∏ i ∈ Finset.range m, NFEuler.dedekindZetaR ℚ ((2 * (i + 1) : ℕ) : ℝ) :=
  massFormula_odd m Q₀ hQ hpd hLi (thm_4_1_posDef (by omega) Q₀ hpd)

/-- **Cassels, App. B, (3.2)–(3.3), explicit form for even $n = 2m \ge 4$, unconditionally**:
`Tamagawa.massFormula_even` with its hypothesis $\tau(SO) = 2$ discharged by `thm_4_1_posDef`. Arguments as in
`massFormula_odd_uncond`, with `hm` ($m \ge 2$). -/
@[kb "cassels1978" "App. B, (3.2), p. 375 (explicit form, n = 2m ≥ 4; proved)"]
theorem massFormula_even_uncond (m : ℕ) (hm : 2 ≤ m) (Q₀ : QuadForm (𝓞 ℚ) (2 * m)) (hQ : Q₀.Nondegenerate)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 ℚ) ℚ)))
    (hLi : Lattices.IsIntegral (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (Tamagawa.stdLat ℚ (2 * m)).1) :
    mass (Q₀.map (algebraMap (𝓞 ℚ) ℚ)) (Tamagawa.stdLat ℚ (2 * m)) =
      (|(discr ℚ : ℝ)|) ^ (((2 * m : ℕ) : ℝ) * ((2 * m : ℕ) - 1) / 4) *
      (∏ σ : ℚ →ₐ[ℚ] ℂ, archVolSO (2 * m) (detGram Q₀ σ))⁻¹ *
      (∏ v ∈ (finite_badPrimes Q₀ hQ).toFinset, LocalDensity.NF.siegelDensity v Q₀ Q₀ / genericEven Q₀ m v)⁻¹ *
      NFEuler.LFunctionNF (chiP · Q₀) m *
      ∏ i ∈ Finset.range (m - 1), NFEuler.dedekindZetaR ℚ ((2 * (i + 1) : ℕ) : ℝ) :=
  massFormula_even m hm Q₀ hQ hpd hLi (thm_4_1_posDef (by omega) Q₀ hpd)

/-- **Cassels, App. B, (3.13) for $l = 1$ (Siegel's formula for numbers), unconditionally** (p. 378; "the deduction of
one of Siegel's formulae from Theorem 4.1", §4, pp. 380–382): for a positive definite form $Q_0$ over $\mathbb Z$ in
$N \ge 4$ variables (`hN`, `Q₀`, `hpd`) and a positive integer $m$ (`hm`), the weighted average over the genus of the
number of representations of $m$ equals the product of the local densities (`SiegelFormulaAt Q₀ m`).
**Unconditional** (`Tamagawa.siegelFormulaAt_rat_all_ranks_uncond`). -/
@[kb "cassels1978" "App. B, (3.13) (l = 1), p. 378, and §4, pp. 380–382 (n ≥ 4; proved)"]
theorem siegelFormulaAt_uncond {N : ℕ} (hN : 4 ≤ N) (Q₀ : QuadForm (𝓞 ℚ) N) (hpd : IsTotallyPosDef (formF Q₀))
    {m : 𝓞 ℚ} (hm : ∀ v, 0 < realEmb ℚ v (algebraMap (𝓞 ℚ) ℚ m)) : SiegelFormulaAt Q₀ m :=
  siegelFormulaAt_rat_all_ranks_uncond hN Q₀ hpd hm

end QuadFormsKB.Cassels.AppBThm41
