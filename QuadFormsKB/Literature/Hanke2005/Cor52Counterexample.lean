import QuadFormsKB.Literature.Hanke2005.Cor52Local
import QuadFormsKB.Literature.Hanke2005.Cor52ClassNumber
import QuadFormsKB.Literature.Hanke2005.ClassGroupSignsObstruction
import QuadFormsKB.Literature.Hanke2005.ClassGroupSigns
import QuadFormsKB.Literature.Hanke2005.Cor52Maximal

/-!
# A counterexample to Hanke's Corollary 5.2(ii), checked in Lean

Hanke (Crelle 584 (2005); thesis p. 19), Corollary 5.2, second assertion: *if $k$ has class number one, then
$\mathrm{vol}(\Gamma_a\backslash Z)=\varepsilon\,\mathrm{Mass}$*, which in the proof needs a **single proper class** in the genus
of the maximal lattice $\Lambda$ (`corollary52_indefinite_classNumberOne`). This file shows by an explicit example that class
number one of $k$ does **not** give one proper class.

**The example.** $k=\mathbb Q(\alpha)$, $\alpha^3-\alpha^2-10\alpha-7=0$ (`Cor52.K`; totally real, $\operatorname{disc}=1489$),
$s=\alpha+2$ (a unit), $d=-s$. The quadratic space is $V=\langle1,1,s\rangle$; the lattice $\mathcal O_k^3$ with $Q=x^2+y^2+sz^2$ is
not maximal at $2$, a maximal lattice is $\Lambda=\mathcal O_k^3+\mathcal O_k\cdot\tfrac12(0,\alpha^2,1+\alpha)$ with Gram form
$Q_0'(x,y,z)=x^2+y^2+\alpha^2yz+4(\alpha+1)^2z^2$ (`Cor52.Q₀`; Hessian determinant $2\,s(1+\alpha)^2$).

**Proved in Lean (no sorry, standard axioms only):**
* `Cor52.poly_irreducible`: the polynomial is irreducible, so `Cor52.K` is a number field;
* `Cor52.classNumber_eq_one` (`Cor52ClassNumber.lean`): $h_k=1$ (Minkowski bound $<8.6$; the primes of norm $\le8$ are $(2)$ and
  $(\alpha)$);
* `Cor52.not_isSquare_d`: $d$ is not a square (negative at a real embedding with $\alpha>3$);
* `Cor52.isIndefinite_QF`: $V$ is isotropic at the real place with $\alpha\approx-2.14$; at the other two real places
  $s>0$, so $V$ is positive definite (`Cor52.not_isotropic_of_pos`) and $d<0$ there;
* `Cor52.hfin_d`: for every finite $v$ and $c\in\sigma(SO(L_v))$: $(c,d)_v=1$. At $v\mid2$ because $d$ is a square in $k_v$
  (`isSquare_algebraMap_of_two_mem`: $x^2=d+8w$ with $x=1+\alpha+\alpha^2$, $w=3+5\alpha+2\alpha^2$, so $d\equiv x^2\bmod 8$ and
  Hensel gives a square root; this holds at every dyadic prime, so $2$ being inert is not used); at $v\nmid2$ because
  $\sigma(SO(L_v))\subseteq\mathfrak o_v^\times k_v^{\times2}$ (Cassels Ch. 11 Lemma 3.3, `isUnitSqClass_of_mem_sigmaFin`) and
  $d$ is a unit (`hilbertSymbol_unitSqClass`);
* `Cor52.stdIsMaximal_Q₀`: $\mathcal O_k^3$ with $Q_0'$ is maximal;
* **`Cor52.two_le_card_DC`**: the genus of $\Lambda$ has at least $2$ proper classes
  (`two_le_card_DC_of_hilbert`), and **`Cor52.cor52_printed_fails`** packages: class number one, maximal, indefinite,
  $n=3$, yet $\ne1$ proper class.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace QuadFormsKB.Hanke2005.Cor52

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure QuadFormsKB.Tamagawa.Measure.Weil
  QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Hanke2005.EqualMasses QuadFormsKB.Hanke2005.SpinorIdele

theorem hessian_det_ne_zero : Q₀.hessian.det ≠ 0 := by
  rw [hessian_det]
  exact mul_ne_zero two_ne_zero (isUnit_sI.mul (isUnit_tI.pow 2)).ne_zero

/-- $Q_0'$ is nondegenerate. -/
theorem nondeg : Q₀.Nondegenerate := hessian_det_ne_zero

/-- $d=-(\alpha+2)$ is the image of $-s_I\in\mathcal O_k$. -/
theorem d_eq_coe : d = ((-sI : 𝓞 K) : K) := by
  have hα : algebraMap (𝓞 K) K αI = α := rfl
  have h2 : algebraMap (𝓞 K) K 2 = 2 := map_ofNat _ 2
  show d = algebraMap (𝓞 K) K (-sI)
  simp [d, sI, hα, h2]

theorem isUnit_negSI : IsUnit (-sI : 𝓞 K) := isUnit_sI.neg

/-- $d$ is a square in $k_v$ at every place $v\mid2$. -/
theorem isSquare_d_dyadic (v : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∈ v.asIdeal) :
    IsSquare (algebraMap K (v.adicCompletion K) d) := by
  rw [d_eq_coe]
  refine isSquare_algebraMap_of_two_mem v h2 (-sI) (1 + αI + αI ^ 2) (3 + 5 * αI + 2 * αI ^ 2) isUnit_negSI ?_
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hα : algebraMap (𝓞 K) K αI = α := rfl
  have h2 : algebraMap (𝓞 K) K 2 = 2 := map_ofNat _ 2
  have h3 : algebraMap (𝓞 K) K 3 = 3 := map_ofNat _ 3
  have h5 : algebraMap (𝓞 K) K 5 = 5 := map_ofNat _ 5
  have h8 : algebraMap (𝓞 K) K 8 = 8 := map_ofNat _ 8
  simp [sI, hα, h2, h3, h5, h8]
  have := α_cube
  linear_combination (α + 3) * this

/-- $d$ is a $v$-adic unit. -/
theorem valuation_d (v : HeightOneSpectrum (𝓞 K)) : v.valuation K d = 1 := by
  rw [d_eq_coe, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem isUnit_negSI)

/-- **Hypothesis (iii) of the obstruction**: $(c,d)_v=1$ for all $c$ with $cF_v^{\times2}\in\sigma(SO(L_v))$. -/
theorem hfin_d (v : HeightOneSpectrum (𝓞 K)) (c : v.adicCompletion K) (hc : c ≠ 0)
    (hmem : sqClassOf c ∈ sigmaFin QF (nondegenerate_map Q₀ nondeg) v) :
    hilbertSymbol (v.adicCompletion K) c (algebraMap K (v.adicCompletion K) d) = 1 := by
  by_cases h2 : (2 : 𝓞 K) ∈ v.asIdeal
  · exact hilbert_eq_one_of_isSquare_right c (isSquare_d_dyadic v h2)
  · have hdet : Q₀.hessian.det ∉ v.asIdeal := by
      rw [hessian_det]
      intro h
      rcases v.isPrime.mem_or_mem h with h | h
      · exact h2 h
      · exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (isUnit_sI.mul (isUnit_tI.pow 2)))
    exact hilbertSymbol_unitSqClass v h2 d (valuation_d v) c hc
      (isUnitSqClass_of_mem_sigmaFin Q₀ v (by norm_num) (nondegenerate_map Q₀ nondeg) h2 hdet hc hmem)

/-- **At least two proper classes in the genus of $\Lambda$** (instance of `two_le_card_DC_of_hilbert`). -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (counterexample to the second assertion: 2 proper classes although h_k = 1)"]
theorem two_le_card_DC : 2 ≤ Nat.card (DC Q₀) :=
  two_le_card_DC_of_hilbert Q₀ nondeg le_rfl isIndefinite_QF d d_ne_zero not_isSquare_d
    isSquare_d_of_isotropic hfin_d

/-- **Hanke's Corollary 5.2(ii) fails as printed.** For $k=\mathbb Q(\alpha)$ ($\alpha^3-\alpha^2-10\alpha-7=0$): $k$ has class number
one (`classNumber k = 1`, i.e. $\mathcal O_k$ is a principal ideal domain); $\Lambda=\mathcal O_k^3$ with $Q_0'$ is a maximal lattice
in $n=3$ variables, indefinite (at one real place, definite at the other two); and yet the genus has at least two proper classes,
so the hypothesis `Nat.card (DC Q₀) = 1` of the proof of the corollary (`corollary52_indefinite_classNumberOne`) fails. -/
@[kb "hanke2005crelle" "Corollary 5.2, p. 19 (counterexample to the second assertion)"]
theorem cor52_printed_fails :
    NumberField.classNumber K = 1 ∧ StdIsMaximal Q₀ ∧ IsIndefinite QF ∧ 3 ≤ 3 ∧ ¬ Nat.card (DC Q₀) = 1 :=
  ⟨classNumber_eq_one, stdIsMaximal_Q₀, isIndefinite_QF, le_rfl, by have := two_le_card_DC; omega⟩

end QuadFormsKB.Hanke2005.Cor52
