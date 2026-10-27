/-
# Siegel's formula for representations of forms by forms in every rank

**Layer:** $F$ a totally real number field; $Q_0$ over $\mathcal O_F$ of rank $N$ and $T_0$ over $\mathcal O_F$ of rank $r$, $1 \le r \le N$, both
totally positive definite; $L = \mathcal O_F^N$. No condition on the shape of $Q_0$ (it need not split off $T_0$), on the class number, or
on the primes.

**Defines**
* `siegelProductAll Q₀ T₀`, **Siegel's product in every rank**, the right reading of the local side for each pair $(N, r)$:
  | case | value | why |
  |---|---|---|
  | $N = 1$ | $2\,S(Q,T)$ (`siegelProductT`, $\varepsilon = \tfrac12$ at every place) | $\tau(SO_1) = 1$, not $2$: $\mathrm{Mass} = \tfrac12$, $\mu_{\mathrm{Tam}}(K_{SO}) = 1$ |
  | $N = 2$ | `siegelProductTRegWith (chiP · Q₀) (-1)`: $L_F(1,\chi_Q)^{-1}\prod_\mathfrak p\alpha_\mathfrak p(Q,T)(1-\chi_Q(\mathfrak p)N\mathfrak p^{-1})^{-1}$ | $\prod\alpha_\mathfrak p$ converges only conditionally |
  | $N \ge 3$, $N - r = 2$ | `siegelProductTReg`: $L_F(1,\chi)\prod_\mathfrak p\beta_\mathfrak p(Q,T)(1-\chi(\mathfrak p)N\mathfrak p^{-1})$, $\chi$ = `chiForms` | same, for the binary complement |
  | $N \ge 3$ otherwise | `siegelProductT` (plain products; $\varepsilon = \tfrac12$ per place for $r = N$, once for $r = N-1$) | absolutely convergent |
* `SiegelFormsAll Q₀ T₀`: $\sum_{\mathrm{cls}M\subseteq\mathrm{gen}L} r_M(T)/|O(M)| = \mathrm{Mass}(L)\cdot$ `siegelProductAll Q₀ T₀`.

**Proves**
* **`siegelForms_all_ranks`** (headline, **unconditional**): `SiegelFormsAll Q₀ T₀` for every $1 \le r \le N$, every totally real $F$.
  The cases: `siegelFormsAt_totallyReal_general` ($N - r \ge 3$), `siegelFormsAtReg_totallyReal` ($N - r = 2$),
  `siegelFormsAt_totallyReal_codimOne` ($N - r = 1$, $N \ge 3$), `siegelFormsAt_totallyReal_full` ($r = N \ge 3$),
  `siegelFormsBinaryOne_totallyReal`, `siegelFormsBinaryTwo_totallyReal` ($N = 2$), `siegelFormsRankOne_totallyReal` ($N = 1$).
* The natural-order reading of the regularized products (partial products over $N\mathfrak p \le X$ converge to the regularized value)
  is conditional on the named input `NaturalOrderEulerOne` over $F$ (`siegelFormsAtReg_natural`, `siegelFormulaAt2_natural_nf`) and
  unconditional over $\mathbb Q$ (`siegelFormsAtReg_natural_rat`).
* Consistency checks: `siegelFormsAll_iff_siegelFormsAt` ($N \ge 3$, $N - r \ne 2$); for $T = \langle m\rangle$,
  $N \ge 4$, it is
  `SiegelFormulaAt Q₀ m` (`siegelFormsAll_unary_iff`); for $T = Q$, $N \ge 3$, it is the mass formula `MassFormulaHolds Q₀`
  (`siegelFormsAll_self_iff`).

Sources: Siegel 1935, Hauptsatz; Siegel 1937 (over $F$) [unverified]; Weil 1982, §3.4–3.5, §4.5 [unverified]. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameSiegelUncond
import QuadFormsKB.Tamagawa.FrameSiegelLow

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadFormsKB.Tamagawa Lattices LocalDensity IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {N r : ℕ}

/-- **Siegel's product in every rank** (Siegel 1935, Hauptsatz [unverified]): the plain product `siegelProductT` when it converges
absolutely ($N \ge 3$, $N - r \ne 2$), the regularized product `siegelProductTReg` (character `chiForms`) when $N - r = 2$, the regularized
binary product (character $\chi_Q$ = `chiP · Q₀`, exponent $-1$) when $N = 2$, and $2\,S(Q,T)$ in rank one ($\tau(SO_1) = 1$). -/
@[kb "siegel1935" "Hauptsatz (local side, forms by forms, every rank) [unverified]"]
def siegelProductAll (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : ℝ :=
  if N = 1 then 2 * siegelProductT Q₀ T₀
  else if N = 2 then siegelProductTRegWith (fun v => chiP v Q₀) (-1) Q₀ T₀
  else if N = r + 2 then siegelProductTReg Q₀ T₀
  else siegelProductT Q₀ T₀

/-- **Siegel's formula for representations of $T$ by the genus of $Q$, every rank** (Siegel 1935, Hauptsatz [unverified]): with
$L = \mathcal O_F^N$,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(L)}\frac{r_M(T)}{|O(M)|} = \mathrm{Mass}(L)\cdot\texttt{siegelProductAll}(Q, T).$$

Field:
- `repMass_eq`: the displayed identity.

A statement, not an input: proved for every $1 \le r \le N$ over every totally real field (`siegelForms_all_ranks`). -/
@[kb "siegel1935" "Hauptsatz (forms by forms, every rank) [unverified]"]
structure SiegelFormsAll (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) : Prop where
  repMass_eq : repMassT (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) (T₀.map (algebraMap (𝓞 F) F)) =
    mass (Q₀.map (algebraMap (𝓞 F) F)) (stdLat F N) * siegelProductAll Q₀ T₀

theorem siegelProductAll_of_ge (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hN : 3 ≤ N) (h2 : N ≠ r + 2) :
    siegelProductAll Q₀ T₀ = siegelProductT Q₀ T₀ := by
  unfold siegelProductAll
  rw [if_neg (by omega), if_neg (by omega), if_neg h2]

theorem siegelProductAll_of_reg (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hN : 3 ≤ N) (h2 : N = r + 2) :
    siegelProductAll Q₀ T₀ = siegelProductTReg Q₀ T₀ := by
  unfold siegelProductAll
  rw [if_neg (by omega), if_neg (by omega), if_pos h2]

/-- **Consistency with `SiegelFormsAt`** for $N \ge 3$, $N - r \ne 2$ (the absolutely convergent cases). -/
theorem siegelFormsAll_iff_siegelFormsAt (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hN : 3 ≤ N)
    (h2 : N ≠ r + 2) : SiegelFormsAll Q₀ T₀ ↔ SiegelFormsAt Q₀ T₀ := by
  rw [show SiegelFormsAll Q₀ T₀ ↔ _ from ⟨fun h => h.repMass_eq, fun h => ⟨h⟩⟩,
    show SiegelFormsAt Q₀ T₀ ↔ _ from ⟨fun h => h.repMass_eq, fun h => ⟨h⟩⟩, siegelProductAll_of_ge Q₀ T₀ hN h2]

/-- **Consistency with `SiegelFormsAtReg`** for $N \ge 3$, $N - r = 2$. -/
theorem siegelFormsAll_iff_siegelFormsAtReg (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hN : 3 ≤ N)
    (h2 : N = r + 2) : SiegelFormsAll Q₀ T₀ ↔ SiegelFormsAtReg Q₀ T₀ := by
  rw [show SiegelFormsAll Q₀ T₀ ↔ _ from ⟨fun h => h.repMass_eq, fun h => ⟨h⟩⟩,
    show SiegelFormsAtReg Q₀ T₀ ↔ _ from ⟨fun h => h.repMass_eq, fun h => ⟨h⟩⟩, siegelProductAll_of_reg Q₀ T₀ hN h2]

/-- **Consistency check $r = 1$:** for $N \ge 4$ and $T = \langle m\rangle$ the formula is the `SiegelFormulaAt Q₀ m`
(Siegel's
formula for numbers, `siegelFormulaAt_totallyReal`). -/
@[kb "siegel1935" "Hauptsatz, r = 1 [unverified]"]
theorem siegelFormsAll_unary_iff (Q₀ : QuadForm (𝓞 F) N) (hN : 4 ≤ N) (m : 𝓞 F) :
    SiegelFormsAll Q₀ (DVR.unary m) ↔ SiegelFormulaAt Q₀ m :=
  (siegelFormsAll_iff_siegelFormsAt Q₀ _ (by omega) (by omega)).trans (siegelFormsAt_unary_iff Q₀ (by omega) m)

/-- **Consistency check $T = Q$:** for $N \ge 3$ the formula for $T = Q$ is the mass formula
$\mathrm{Mass}(L) = \mu_{\mathrm{Tam}}(K_{SO})^{-1}$ (`MassFormulaHolds`). -/
@[kb "siegel1935" "Hauptsatz, T = S (the mass formula) [unverified]"]
theorem siegelFormsAll_self_iff (Q₀ : QuadForm (𝓞 F) N) (hN : 3 ≤ N)
    (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAll Q₀ Q₀ ↔ MassFormulaHolds Q₀ :=
  (siegelFormsAll_iff_siegelFormsAt Q₀ Q₀ hN (by omega)).trans (siegelFormsAt_self_iff Q₀ (by omega) hpd)

/-- **Siegel's formula for representations of forms by forms, in every rank, over every totally real field** (unconditional):
for $Q_0$ over $\mathcal O_F$ of rank $N$ and $T_0$ over $\mathcal O_F$ of rank $r$, $1 \le r \le N$, both totally positive definite,
$$\sum_{\mathrm{cls}(M)\subseteq\mathrm{gen}(\mathcal O_F^N)}\frac{r_M(T_0)}{|O(M)|} = \mathrm{Mass}(\mathcal O_F^N)\cdot
\texttt{siegelProductAll}(Q_0, T_0)$$
(the product read as in the module docstring: plain for $N \ge 3$, $N - r \ne 2$; regularized by $L_F(1,\chi)$ for $N - r = 2$ and for
$N = 2$; doubled for $N = 1$). No condition on the shape of $Q_0$, the class number of $F$ or the primes. -/
@[kb "siegel1935" "Hauptsatz (forms by forms, every rank r ≤ N), over a totally real field [unverified]"]
theorem siegelForms_all_ranks [IsTotallyReal F] (Q₀ : QuadForm (𝓞 F) N) (T₀ : QuadForm (𝓞 F) r) (hr : 1 ≤ r)
    (hrN : r ≤ N) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (hpdT : IsTotallyPosDef (T₀.map (algebraMap (𝓞 F) F))) : SiegelFormsAll Q₀ T₀ := by
  rcases Nat.lt_or_ge N 3 with hN | hN
  · -- `N = 1` or `N = 2`
    rcases Nat.lt_or_ge N 2 with hN1 | hN2
    · obtain rfl : N = 1 := by omega
      obtain rfl : r = 1 := by omega
      refine ⟨?_⟩
      rw [siegelFormsRankOne_totallyReal Q₀ T₀ hpd hpdT]
      unfold siegelProductAll
      rw [if_pos rfl]
    · obtain rfl : N = 2 := by omega
      refine ⟨?_⟩
      unfold siegelProductAll
      rw [if_neg (by omega), if_pos rfl]
      rcases Nat.lt_or_ge r 2 with hr1 | hr2
      · obtain rfl : r = 1 := by omega
        exact siegelFormsBinaryOne_totallyReal Q₀ T₀ hpd hpdT
      · obtain rfl : r = 2 := by omega
        exact siegelFormsBinaryTwo_totallyReal Q₀ T₀ hpd hpdT
  · by_cases h2 : N = r + 2
    · exact (siegelFormsAll_iff_siegelFormsAtReg Q₀ T₀ hN h2).mpr
        (siegelFormsAtReg_totallyReal Q₀ T₀ hr h2 hpd hpdT)
    · refine (siegelFormsAll_iff_siegelFormsAt Q₀ T₀ hN h2).mpr ?_
      by_cases h1 : N = r + 1
      · exact siegelFormsAt_totallyReal_codimOne Q₀ T₀ (by omega) h1 hpd hpdT
      · by_cases h0 : N = r
        · exact siegelFormsAt_totallyReal_full Q₀ T₀ (by omega) h0 hpd hpdT
        · exact siegelFormsAt_totallyReal_general Q₀ T₀ hr (by omega) hpd hpdT

end QuadFormsKB.Tamagawa.Frames
