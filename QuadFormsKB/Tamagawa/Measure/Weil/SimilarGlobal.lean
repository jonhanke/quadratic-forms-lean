import QuadFormsKB.Tamagawa.Measure.Weil.SimilarLocal
import QuadFormsKB.Tamagawa.LatticeChangeGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.MuTamSO
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarArchGlobal
import QuadFormsKB.Tamagawa.Measure.Weil.SimilarFinGlobal

/-!
# Similar forms have the same Tamagawa covolume

**Layer:** a number field $F$; $Q_0$ a nondegenerate form over $\mathcal O_F$ in $n$ variables ($n \ne 0, 2$), $G \in
M_n(\mathcal O_F)$ with $\det G \ne 0$, $c \in \mathcal O_F \setminus 0$, $Q_1 = c\,(Q_0\circ G)$ (`simForm`).

**Proves**
* `prod_infinitePlace_mul_tprod_finitePlace`: the product formula
  $\prod_{w\mid\infty}|x|_w^{m_w}\cdot\prod_v\|x\|_v = 1$ for $x \in \mathcal O_F\setminus 0$.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.Weil

open NumberField IsDedekindDomain NumberField.InfinitePlace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F]

/-- **The product formula** for an algebraic integer $x \ne 0$:
$\prod_{w\mid\infty}|x|_w^{m_w}\cdot\prod_v\|x\|_v = 1$ (Mathlib's `InfinitePlace.prod_eq_abs_norm` and
`FinitePlace.prod_eq_inv_abs_norm`). -/
@[kb "weil1982" "Thm 2.3.1, pp. 21–22 (product formula) [unverified]"]
theorem prod_infinitePlace_mul_tprod_finitePlace {x : 𝓞 F} (hx : x ≠ 0) :
    (∏ w : InfinitePlace F, w (algebraMap (𝓞 F) F x) ^ w.mult) *
      ∏' v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖ = 1 := by
  have hx' : algebraMap (𝓞 F) F x ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hx
  have h2 := FinitePlace.prod_eq_inv_abs_norm hx'
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h2
  simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at h2
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖FinitePlace.embedding v (algebraMap (𝓞 F) F x)‖).Finite := by
    have h0 : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
      have h_span_nezero : Ideal.span {x} ≠ 0 := by simp [hx]
      simp only [← Ideal.dvd_span_singleton]
      exact Ideal.finite_factors h_span_nezero
    refine h0.subset fun v hv => ?_
    by_contra h
    exact hv ((FinitePlace.norm_eq_one_iff_notMem F v x).mpr h)
  rw [tprod_eq_finprod hfin, h2, InfinitePlace.prod_eq_abs_norm]
  have hN : (|Algebra.norm ℚ (algebraMap (𝓞 F) F x)| : ℝ) ≠ 0 := by
    have : Algebra.norm ℚ (algebraMap (𝓞 F) F x) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hx'
    exact_mod_cast abs_ne_zero.mpr this
  push_cast
  exact mul_inv_cancel₀ hN

section Covolume

variable {n : ℕ} {Q₀ : QuadForm (𝓞 F) n} {c : 𝓞 F} {G : Matrix (Fin n) (Fin n) (𝓞 F)}

/-- **Conjugation by $G$ on the rational points**: $SO(Q_0)(F)\cong SO(Q_1)(F)$, $\gamma\mapsto G^{-1}\gamma G$. -/
def simConjF (hc : c ≠ 0) (hG : G.det ≠ 0) :
    soSub (Q₀.map (algebraMap (𝓞 F) F)) F ≃* soSub ((simForm Q₀ c G).map (algebraMap (𝓞 F) F)) F :=
  simConjSO _ _ (LatChange.glF G hG) (c : F) (hessian_simForm hG) F (coe_ne_zero_of_ne_zero hc)

theorem simConjF_gl (hc : c ≠ 0) (hG : G.det ≠ 0) (γ : soSub (Q₀.map (algebraMap (𝓞 F) F)) F) :
    (simConjF hc hG γ).1.1 =
      (LatChange.glF G hG)⁻¹ * γ.1.1 * LatChange.glF G hG := by
  show (glK (LatChange.glF G hG) F)⁻¹ * _ * glK (LatChange.glF G hG) F = _
  congr 2

theorem map_simConjF_gl {S : Type*} [CommRing S] (σ : F →+* S) (hc : c ≠ 0) (hG : G.det ≠ 0)
    (γ : soSub (Q₀.map (algebraMap (𝓞 F) F)) F) :
    Matrix.GeneralLinearGroup.map σ (simConjF hc hG γ).1.1 =
      (Matrix.GeneralLinearGroup.map σ (LatChange.glF G hG))⁻¹ *
        Matrix.GeneralLinearGroup.map σ γ.1.1 *
          Matrix.GeneralLinearGroup.map σ (LatChange.glF G hG) := by
  rw [simConjF_gl, map_mul, map_mul, map_inv]

/-- **The adelic conjugation** $SO(V_0)(\mathbb A)\cong SO(V_1)(\mathbb A)$, $g\mapsto G^{-1}gG$ at every place. -/
def simConjAdele (hc : c ≠ 0) (hG : G.det ≠ 0) : SOAdele Q₀ ≃* SOAdele (simForm Q₀ c G) :=
  (simConjInf hc hG).toMulEquiv.prodCongr (simConjFin hc hG).toMulEquiv

/-- **Conjugation commutes with the diagonal embedding**: $\varphi(\gamma) = G^{-1}\gamma G$ on $SO(V_0)(F)$. -/
theorem simConjAdele_diag (hc : c ≠ 0) (hG : G.det ≠ 0) (γ : soSub (Q₀.map (algebraMap (𝓞 F) F)) F) :
    simConjAdele hc hG (diagSOAdele Q₀ γ) = diagSOAdele (simForm Q₀ c G) (simConjF hc hG γ) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext w
    refine Subtype.ext ?_
    exact (map_simConjF_gl (embedding_of_isReal w.2) hc hG γ).symm
  · funext w
    refine Subtype.ext ?_
    exact (map_simConjF_gl w.1.embedding hc hG γ).symm
  · apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    refine Subtype.ext ?_
    exact (map_simConjF_gl (algebraMap F (v.adicCompletion F)) hc hG γ).symm

theorem map_GammaSOAdele_simConjAdele (hc : c ≠ 0) (hG : G.det ≠ 0) :
    (GammaSOAdele Q₀).map (simConjAdele hc hG).toMonoidHom = GammaSOAdele (simForm Q₀ c G) := by
  ext x
  simp only [Subgroup.mem_map, GammaSOAdele, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨simConjF hc hG γ, (simConjAdele_diag hc hG γ).symm⟩
  · rintro ⟨γ, rfl⟩
    refine ⟨_, ⟨(simConjF hc hG).symm γ, rfl⟩, ?_⟩
    rw [simConjAdele_diag, MulEquiv.apply_symm_apply]

/-- **Similar forms have the same Tamagawa covolume** (every number field, every signature, $n \ne 0, 2$):
$\mathrm{covol}(SO(V_1)(F), \mu_{\mathrm{Tam}}) = \mathrm{covol}(SO(V_0)(F), \mu_{\mathrm{Tam}})$ for
$Q_1 = c\,(Q_0\circ G)$. *Proof:* conjugation by $G$ at every place carries $SO(V_0)(F)$ onto $SO(V_1)(F)$ and the
Tamagawa measures to each other up to $\prod_{w\mid\infty}|\delta|_w^{m_w}\cdot\prod_v\|\delta\|_v = 1$,
$\delta = c^{n(n+1)/2}\det(G)^{n+1}$ (product formula). -/
@[kb "weil1982" "§2.3, Thm 2.3.1, pp. 21–22 (independence of choices, product formula); §2.4, p. 22"]
theorem covolume_muTam_simForm (hn0 : n ≠ 0) (hn2 : n ≠ 2) (hQ : Q₀.Nondegenerate) (hc : c ≠ 0)
    (hG : G.det ≠ 0) :
    covolume (GammaSOAdele (simForm Q₀ c G)) (SOAdele (simForm Q₀ c G))
        (muTam (simForm Q₀ c G) (nondegenerate_simForm hQ hc hG) fun _ => 1) =
      covolume (GammaSOAdele Q₀) (SOAdele Q₀) (muTam Q₀ hQ fun _ => 1) := by
  have := countable_GammaSOAdele Q₀
  have hδ := simJac_ne_zero hc hG
  have hpf := prod_infinitePlace_mul_tprod_finitePlace hδ
  symm
  refine covolume_eq_of_localFactors (GammaSOAdele Q₀) (GammaSOAdele (simForm Q₀ c G))
    (simConjInf hc hG).toMulEquiv (simConjFin hc hG).toMulEquiv
    (simConjInf hc hG).continuous.measurable (simConjInf hc hG).symm.continuous.measurable
    (simConjFin hc hG).continuous.measurable (simConjFin hc hG).symm.continuous.measurable
    (map_GammaSOAdele_simConjAdele hc hG) _ _ _ _
    (map_muArchTamSO_simConjInf hQ hc hG) (map_muFin_simConjFin hn0 hn2 hQ hc hG) ?_
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => pow_nonneg (apply_nonneg _ _) _), hpf,
    ENNReal.ofReal_one]

end Covolume

end QuadFormsKB.Tamagawa.Measure.Weil
