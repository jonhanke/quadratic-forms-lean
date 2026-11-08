/-
# Hanke 2013, §3.3: maximal $\mathfrak a$-valued bilinear lattices

J. Hanke, *Algorithms for computing maximal lattices in bilinear (and quadratic) spaces over number fields*,
Contemp. Math. 587 (2013); source used: arXiv:1208.2481v3 (bib key `hanke2013algorithms`), §3, pp. 7, 13–14.

**Setting** as in `Duality.lean` and `Discriminant.lean`.

**Defines** maximal $\mathfrak a$-valued lattices (`IsAMaximal`, §1 "maximal object" and §3) and maximal isotropic
submodules of the discriminant module (`IsMaxIsotropicSub`, §3 introduction and Algorithm 3.16).

**Proves**
* the reduction stated at the start of §3 and used in the proof of **Algorithm 3.16**: for an $\mathfrak a$-valued $L$ and
  an $\mathfrak a$-valued $L'\supseteq L$, $L'$ is maximal $\mathfrak a$-valued iff $L'/L$ is a maximal isotropic submodule of
  $D_{\mathfrak a}(L)$ (`isAMaximal_iff`, from Lemma 2.12);
* the **existence** of a maximal $\mathfrak a$-valued lattice containing a given $\mathfrak a$-valued lattice $L$ in a
  non-degenerate space (`exists_isAMaximal`; the goal of Algorithm 3.16), since $D_{\mathfrak a}(L)$ is a Noetherian
  (indeed finite) module. (For quadratic lattices and O'Meara's norm-maximal lattices, existence is O'Meara 82:18,
  `OMeara.exists_isMaximal`.)
-/
import QuadFormsKB.Literature.Hanke2013Algorithms.Discriminant

open QuadraticMap Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2013Algorithms

open QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Maximal $\mathfrak a$-valued lattice** (Hanke 2013, §1, p. 4 "maximal object", §3, p. 7): $L$ is $\mathfrak a$-valued
and no $\mathfrak a$-valued $L'\supsetneq L$ exists. -/
@[kb "hanke2013algorithms" "§3, p. 7 (maximal a-valued bilinear lattice)"]
def IsAMaximal (a : Submodule R F) (L : Submodule R V) : Prop :=
  IsAValued Q a L ∧ ∀ L' : Submodule R V, L ≤ L' → IsAValued Q a L' → L' = L

/-- **Maximal isotropic submodule** of $(D_{\mathfrak a}(L),\widetilde B)$ (Hanke 2013, §3, p. 7 and Algorithm 3.16,
p. 13). -/
@[kb "hanke2013algorithms" "§3, p. 7; Algorithm 3.16, p. 13 (maximal isotropic submodule of D_a(L))"]
def IsMaxIsotropicSub {a : Submodule R F} {L : Submodule R V} (N : Submodule R (DiscModule Q a L)) : Prop :=
  IsIsotropicSub Q N ∧ ∀ N' : Submodule R (DiscModule Q a L), N ≤ N' → IsIsotropicSub Q N' → N' = N

theorem toDisc_mono (a : Submodule R F) (L : Submodule R V) {L₁ L₂ : Submodule R V} (h : L₁ ≤ L₂) :
    toDisc Q a L L₁ ≤ toDisc Q a L L₂ :=
  Submodule.map_mono (Submodule.comap_mono h)

theorem ofDisc_mono {a : Submodule R F} {L : Submodule R V} {N₁ N₂ : Submodule R (DiscModule Q a L)}
    (h : N₁ ≤ N₂) : ofDisc Q N₁ ≤ ofDisc Q N₂ :=
  Submodule.map_mono (Submodule.comap_mono h)

/-- **Maximal lattices and maximal isotropic submodules** (Hanke 2013, §3, p. 7: "By Lemma 2.12 we can do this by
finding a maximal isotropic submodule of its $\mathfrak a$-discriminant module"; proof of Algorithm 3.16, p. 14): for an
$\mathfrak a$-valued $L$ and an $\mathfrak a$-valued $L'\supseteq L$, $L'$ is maximal $\mathfrak a$-valued if and only if
$L'/L$ is a maximal isotropic submodule of $D_{\mathfrak a}(L)$. -/
@[kb "hanke2013algorithms" "§3, p. 7; Algorithm 3.16, proof, p. 14"]
theorem isAMaximal_iff {a : Submodule R F} {L L' : Submodule R V} (hval : IsAValued Q a L) (hLL' : L ≤ L')
    (hL' : IsAValued Q a L') : IsAMaximal Q a L' ↔ IsMaxIsotropicSub Q (toDisc Q a L L') := by
  constructor
  · rintro ⟨-, hmax⟩
    refine ⟨isIsotropicSub_toDisc Q hL', fun N' hN hN' => ?_⟩
    have h1 : L' ≤ ofDisc Q N' := by
      rw [← ofDisc_toDisc Q hval hLL' hL']
      exact ofDisc_mono Q hN
    have h2 := hmax _ h1 (isAValued_ofDisc Q hN')
    rw [← toDisc_ofDisc Q N', h2]
  · rintro ⟨-, hmax⟩
    refine ⟨hL', fun L'' hL'' hv'' => ?_⟩
    have hL : L ≤ L'' := hLL'.trans hL''
    have h1 := hmax _ (toDisc_mono Q a L hL'') (isIsotropicSub_toDisc Q hv'')
    rw [← ofDisc_toDisc Q hval hL hv'', h1, ofDisc_toDisc Q hval hLL' hL']

end Defs

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Existence of maximal $\mathfrak a$-valued lattices** (Hanke 2013, Algorithm 3.16, p. 13, the output): every
$\mathfrak a$-valued lattice $L$ in a non-degenerate space ($\mathfrak a$ a non-zero fractional ideal) lies in a maximal
$\mathfrak a$-valued lattice $L'$. *Proof*: $D_{\mathfrak a}(L)$ is a quotient of the finitely generated module
$L^{\#\mathfrak a}$ over the Noetherian ring $R$, so its isotropic submodules have a maximal element; apply
`isAMaximal_iff`. -/
@[kb "hanke2013algorithms" "Algorithm 3.16, p. 13 (a maximal a-valued lattice containing L exists)"]
theorem exists_isAMaximal (hV : (QuadraticMap.associated Q).Nondegenerate) {a : Submodule R F} (ha : a.FG)
    (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.IsLattice F) (hval : IsAValued Q a L) :
    ∃ L' : Submodule R V, L ≤ L' ∧ IsAMaximal Q a L' := by
  have hfg : (aDual Q a L).FG := (isLattice_aDual Q hV ha ha0 hL).fg
  haveI : IsNoetherian R (aDual Q a L) := isNoetherian_of_fg_of_noetherian _ hfg
  haveI : IsNoetherian R (DiscModule Q a L) := inferInstance
  obtain ⟨N, hN, hmax⟩ := (set_has_maximal_iff_noetherian (R := R) (M := DiscModule Q a L)).2 inferInstance
    {N | IsIsotropicSub Q N} ⟨⊥, fun x hx y _ => by
      rw [Submodule.mem_bot] at hx; rw [hx, LinearMap.map_zero, LinearMap.zero_apply]⟩
  have hL' := isAValued_ofDisc Q hN
  have hLL' := le_ofDisc Q hval N
  refine ⟨ofDisc Q N, hLL', (isAMaximal_iff Q hval hLL' hL').2 ?_⟩
  rw [toDisc_ofDisc]
  refine ⟨hN, fun N' hle hN' => ?_⟩
  by_contra hne
  exact hmax N' hN' (lt_of_le_of_ne hle (Ne.symm hne))

end Dedekind

end QuadFormsKB.Hanke2013Algorithms
