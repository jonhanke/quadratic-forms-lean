/-
# Hanke 2005, §6: Lemmas 6.1, 6.2 and Theorem 6.3 (masses of $\mathfrak a$-maximal lattices), totally definite case

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ totally real, $Q_0$ a totally positive definite form over $\mathcal O_F$ in $n\ge3$ variables,
$V = (F^n, Q_0)$, lattices $L$ on $V$ of any Steinitz class (`Lat F n`), the repository's mass `Lattices.mass` (classes and
automorphisms for $O(V)$; Hanke's mass for $SO(V)$ is twice it, `hankeMass_definite_eq_two_mul_mass`, so equalities of
masses are the same for both), and the stabilizers $O(\hat L) = \prod_vO(L_v)$ (`locStab`).

**Lemma 6.1** (p. 20): $\mathrm{Mass}(\Lambda)/\mathrm{Mass}(\Lambda') = \mathrm{vol}(D'_h)/\mathrm{vol}(D_h)$; here in index form
(`lemma61_definite`): $\mathrm{Mass}(L) = \mathrm{Mass}(M)\cdot r(O(\hat M), O(\hat L))$ with $r(A,B) = [A:A\cap B]/[B:A\cap B] =
\mathrm{vol}(A)/\mathrm{vol}(B)$ (`relRatio`), from the mass formula for arbitrary lattices (`massFormula_lat_nf`) and $\tau = 2$.

**Lemma 6.2** (p. 20): conjugation by a similitude $\alpha$ of $\varphi_\mathfrak p$ preserves the volume of open compact subgroups of
$O(V_\mathfrak p)$ (`relRatio_conj_similitude`). Proof here: for lattice stabilizers via the $\alpha$-law
$r(O(P\mathfrak o^n), O(\mathfrak o^n))\,\beta(Q) = \beta(Q\circ P)\,|\det P|^{n+1}$ (`alphaLaw_global`), with
$Q\circ(\alpha P) = \xi\,(Q\circ P)$, $\beta(\xi Q') = |\xi|^{-n(n+1)/2}\beta(Q')$ (Lemma 3.1) and $|\det\alpha|^2 = |\xi|^n$; then for
every commensurable subgroup by the cocycle property of $r$.

**Theorem 6.3** (pp. 20–21, `theorem63_definite`): if $L$ is $\mathfrak a$-maximal and $M$ is maximal, and ($n$ odd) every
$\mathrm{ord}_\mathfrak p\mathfrak a$ is even, ($n$ even) $\mathfrak a_\mathfrak p$ is a norm from $K_\mathfrak p$ wherever $t_\mathfrak p = 2$
(i.e. $\mathrm{ord}_\mathfrak p\mathfrak a$ even when $\mathfrak p$ is unramified in $K$), then $\mathrm{Mass}(L) = \mathrm{Mass}(M)$.
Hanke's proof: at each $\mathfrak p$ some similitude has multiplier of valuation $\mathrm{ord}_\mathfrak p\mathfrak a$ (the computation of
$\mathrm{ord}_\mathfrak p\Xi_\mathfrak p(\theta_\mathfrak p)$, `Similitudes.lean`), it maps $M_\mathfrak p$ to an $\mathfrak a_\mathfrak p$-maximal lattice,
which is isometric to $L_\mathfrak p$ (all $\mathfrak a_\mathfrak p$-maximal lattices are isometric: [Shi2, Lemma 5.9], proved in the
repository as O'Meara 91:2, `OMeara.cls_eq_of_isMaximal`); then Lemmas 6.1 and 6.2.

**Named input** `SimilitudeOddMultiplier F` (Hanke, proof of Theorem 6.3, p. 21, with the models of $\theta_\mathfrak p$ from
[Shi, §3.2]): for even $n$, if $t_\mathfrak p = 0$, or $t_\mathfrak p = 2$ and $\mathfrak p$ ramifies in $K$, or $t_\mathfrak p = 4$, then
$\varphi_\mathfrak p$ has a similitude whose multiplier has valuation $1$ ($t = 0$: hyperbolic space, `multipliers_hyperbolic`;
$t = 2$: $(W,\theta)\cong(K_\mathfrak p,cN)$ and a norm of odd valuation; $t = 4$: $(W,\theta)\cong(B_\mathfrak p, N_B)$ and
$N_B(B_\mathfrak p^\times) = k_\mathfrak p^\times$). The identification of $\theta_\mathfrak p$ with these models is cited from Shimura, not
proved here.

Only the totally definite case is formalized: the repository defines the mass of an arbitrary lattice (any Steinitz
class) only for totally definite forms.
-/
import QuadFormsKB.Literature.Hanke2005.Lemma61
import QuadFormsKB.Literature.Hanke2005.Lemma62
import QuadFormsKB.Literature.Hanke2005.MaximalLocal
import QuadFormsKB.Literature.Hanke2005.MaximalSimilitude
import QuadFormsKB.Tamagawa.LatticeChangeNF
import QuadFormsKB.Tamagawa.LocalSmith
import QuadFormsKB.Literature.OMeara.Sec91Max
import QuadFormsKB.Literature.OMeara.Sec82Local

open MeasureTheory NumberField IsDedekindDomain Filter
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.LocalDensity QuadFormsKB.Tamagawa.LatChange

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

/-- $\mathrm{ord}_\mathfrak p(\mathcal O_F) = 0$. -/
theorem ordIdeal_top (v : HeightOneSpectrum (𝓞 F)) : ordIdeal v (⊤ : Ideal (𝓞 F)) = 0 := by
  unfold ordIdeal
  rw [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
  exact Associates.count_zero (Associates.irreducible_mk.mpr v.irreducible)

/-- The fractional ideal $\mathcal O_F$ of $F$ is the span of the image of the unit ideal. -/
theorem span_image_top : Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' ((⊤ : Ideal (𝓞 F)) : Set (𝓞 F))) =
    (1 : Submodule (𝓞 F) F) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨r, -, rfl⟩
    exact Submodule.mem_one.mpr ⟨r, rfl⟩
  · intro x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    exact Submodule.subset_span ⟨r, trivial, rfl⟩

/-- **The local step of Theorem 6.3**: $r(O(M_\mathfrak p), O(L_\mathfrak p)) = 1$. -/
theorem relRatio_stabLat_maximal (v : HeightOneSpectrum (𝓞 F)) (I₃ : SimilitudeOddMultiplier F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcond : HankeIdealCond Q₀ I) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)))
        (Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F)))) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    relRatio (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype (loc v M.1))
      (stabLat v (orthGroup (Q₀.map (algebraMap (𝓞 F) F)) (v.adicCompletion F)).subtype (loc v L.1)) = 1 := by
  have hL' := isMaximal_loc v Q₀ hQ I hI L hL
  have hM' := isMaximal_loc v Q₀ hQ ⊤ top_ne_bot M (by rw [span_image_top]; exact hM)
  rw [ordIdeal_top] at hM'
  obtain ⟨g, ξ, hξ, hg, hLM⟩ :=
    exists_similitude_of_isMaximal v I₃ hn Q₀ hQ (ordIdeal v I) (hcond v) (loc v L.1) (loc v M.1) hL' hM'
  rw [hLM, relRatio_symm', relRatio_stabLat_similitude v Q₀ hQ g hξ hg M, inv_one]

/-- **Theorem 6.3, totally definite case** (Hanke thesis, pp. 20–21): $F$ totally real, $Q_0$ totally positive definite in
$n\ge3$ variables, $L$ an $\mathfrak a$-maximal lattice and $M$ a maximal lattice on $V$, $\mathfrak a\ne0$ satisfying Hanke's
condition. Then $\mathrm{Mass}(L) = \mathrm{Mass}(M)$. Conditional on `SimilitudeOddMultiplier F` (used only for even $n$). -/
@[kb "hanke2005crelle" "Theorem 6.3, pp. 20–21 (totally definite case)"]
theorem theorem63_definite [IsTotallyReal F] (I₃ : SimilitudeOddMultiplier F) (hn : 3 ≤ n)
    (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) (hpd : IsTotallyPosDef (Q₀.map (algebraMap (𝓞 F) F)))
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcond : HankeIdealCond Q₀ I) (L M : Lat F n)
    (hL : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F)))
        (Submodule.span (𝓞 F) (algebraMap (𝓞 F) F '' (I : Set (𝓞 F)))) L.1)
    (hM : letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
      OMeara.IsMaximal (QuadForm.toQuadraticForm (Q₀.map (algebraMap (𝓞 F) F))) (1 : Submodule (𝓞 F) F) M.1) :
    mass (Q₀.map (algebraMap (𝓞 F) F)) L = mass (Q₀.map (algebraMap (𝓞 F) F)) M := by
  classical
  set Q := Q₀.map (algebraMap (𝓞 F) F)
  rw [lemma61_definite hn Q₀ hQ hpd L M]
  suffices h : relRatio (locStab Q M) (locStab Q L) = 1 by rw [h, mul_one]
  have hfin : ∀ N : Lat F n, {v : HeightOneSpectrum (𝓞 F) | ¬ loc v N.1 = std v}.Finite := fun N =>
    Filter.eventually_cofinite.mp (loc_eventually_std N.2)
  set S := (hfin L).toFinset ∪ (hfin M).toFinset
  have hS : ∀ N ∈ ({L, M} : Set (Lat F n)), ∀ v ∉ S, loc v N.1 = std v := by
    intro N hN v hv
    by_contra h
    rcases hN with rfl | rfl
    · exact hv (Finset.mem_union_left _ ((hfin _).mem_toFinset.mpr h))
    · exact hv (Finset.mem_union_right _ ((hfin _).mem_toFinset.mpr h))
  have hc : ∀ A B : Lat F n, Commens (locStab Q A) (locStab Q B) := fun A B =>
    ⟨(commensurable_locStab Q A B).1.relIndex_ne_zero, (commensurable_locStab Q A B).2.relIndex_ne_zero⟩
  rw [← relRatio_mul (hc M (stdLat F n)) (hc (stdLat F n) L) (hc M L), relRatio_symm',
    relRatio_locStab_eq_prod Q L S (hS L (by simp)), relRatio_locStab_eq_prod Q M S (hS M (by simp))]
  rw [inv_mul_eq_one₀ ?_]
  · refine (Finset.prod_congr rfl fun v _ => ?_).symm
    set ψ := (orthGroup Q (v.adicCompletion F)).subtype
    have h1 := commens_stabLat v ψ (std_isLattice v) (loc_isLattice v M.2)
    have h2 := commens_stabLat v ψ (loc_isLattice v M.2) (loc_isLattice v L.2)
    have h3 := commens_stabLat v ψ (std_isLattice v) (loc_isLattice v L.2)
    rw [stdStab_eq_stabLat, ← relRatio_mul h1 h2 h3,
      relRatio_stabLat_maximal v I₃ hn Q₀ hQ I hI hcond L M hL hM, mul_one]
  · exact (Finset.prod_pos fun v _ => relRatio_pos (by
      rw [stdStab_eq_stabLat]
      exact commens_stabLat v _ (std_isLattice v) (loc_isLattice v M.2))).ne'

end QuadFormsKB.Hanke2005
