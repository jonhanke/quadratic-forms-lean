/-
# Product formulas for the global Weil representation

**Layer:** global inputs over a number field $F$, each proved here from local facts plus a published global theorem.

* `modK_eq_norm`: **the Haar modulus of $F_v$ is Mathlib's normalized absolute value**, $|x|_v = \|x\| = N(v)^{-\mathrm{ord}_v x}$
  (local: $\mathrm{vol}(x\mathcal O_v)/\mathrm{vol}(\mathcal O_v) = \Delta_v^{\mathrm{ord}_vx}$ with $\Delta_v = N(v)^{-1}$, `modV_eq`).
* `prod_modulus_eq_one`: **the product formula** $|t|_\infty\prod_v|t|_v = 1$ for $t \in F^\times$, with
  $|t|_\infty = \prod_{w\ \mathrm{real}}|t_w|\prod_{w\ \mathrm{complex}}|t_w|^2$ (`mixedEmbedding.norm`): Mathlib's
  `FinitePlace.prod_eq_inv_abs_norm` and `mixedEmbedding.norm_eq_norm`.
* `prod_hilbert_eq_one`: **Hilbert reciprocity** $\prod_{w\mid\infty}(a,b)_w\prod_v(a,b)_v = 1$ for $a, b \in F^\times$, in
  product form (from `HN.prod_hilbert_infinite_mul_weilInf`, `HN.finprod_hilbert_finite_mul_weilV` and Weil's
  product formula `weilInf_mul_finprod_weilV`, as in `HN.hilbert_product_formula_nf`).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Weil.NonArch
import QuadFormsKB.Analysis.WeilIndexGlobal
import QuadFormsKB.Literature.HasseNorm.Reciprocity

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Metric
open QuadFormsKB.Analysis

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.WeilRep

variable {F : Type} [Field F] [NumberField F]

/-! ### The Haar modulus at a finite place -/

section Modulus

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

lemma norm_eq_absNorm_pow {x : Fv} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ WithZero.log (Valued.v x) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valued.v).ne_zero_iff.mpr hx)]
  push_cast; rfl

/-- **The Haar modulus of $F_v$ is the normalized absolute value:** $|x|_v = \|x\|$ (Mathlib's norm on
`v.adicCompletion F`, normalized by $N(v)$). -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §7, Def. and Thm., p. 51; §11, p. 59 (multiplication by a multiplies Haar measure by |a|, which characterizes the normalized valuation); Ch. XV (Tate), Lemma 2.2.5, p. 310"]
theorem modK_eq_norm {x : Fv} (hx : x ≠ 0) : Analysis.Weil.modK Fv x = ‖x‖ := by
  set n : ℤ := WithZero.log (Valued.v x) with hn
  have hvx : Valued.v x = WithZero.exp n := (WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hx)).symm
  have hϖ : ‖HN.ϖ v ^ (-n)‖ = ‖x‖ := by
    rw [norm_eq_absNorm_pow v (zpow_ne_zero _ (HN.ϖ_ne_zero v)), norm_eq_absNorm_pow v hx,
      valued_ϖ_zpow, neg_neg, WithZero.log_exp]
  rw [Analysis.Weil.modK_eq_ratio (haarV v) hx, ← hϖ, ← coe_latticeV, haarV_real_latticeV,
    show (closedBall (0 : Fv) 1) = (latticeV v 0 : Set Fv) by rw [coe_latticeV]; simp,
    haarV_real_latticeV, zpow_zero, div_one, modV_eq, inv_zpow', neg_neg, hϖ, norm_eq_absNorm_pow v hx]

end Modulus

/-! ### The product formula for the modulus -/

/-- For $t \in F$, $|t|_v = (\text{the finite place } v)(t)$. -/
lemma modK_algebraMap_eq (v : HeightOneSpectrum (𝓞 F)) {t : F} (ht : t ≠ 0) :
    Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t) =
      (FinitePlace.equivHeightOneSpectrum.symm v) t := by
  rw [modK_eq_norm v ((map_ne_zero _).mpr ht), FinitePlace.equivHeightOneSpectrum_symm_apply]
  rfl

lemma hasFiniteMulSupport_modK {t : F} (ht : t ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t) := by
  have h := FinitePlace.hasFiniteMulSupport (K := F) ht
  have : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t)) ⊆
      FinitePlace.equivHeightOneSpectrum '' Function.mulSupport fun w : FinitePlace F => w t := by
    intro v hv
    refine ⟨FinitePlace.equivHeightOneSpectrum.symm v, ?_, by simp⟩
    simp only [Function.mem_mulSupport] at hv ⊢
    rwa [modK_algebraMap_eq v ht] at hv
  exact (h.image _).subset this

/-- **The product formula for the modulus:** for $t \in F^\times$,
$$|t|_\infty\prod_v|t|_v = 1,\qquad |t|_\infty = \prod_{w\ \mathrm{real}}|t_w|\prod_{w\ \mathrm{complex}}|t_w|^2.$$ -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §12, Thm., p. 60 (proof p. 61; second proof §14, p. 66); Ch. XV (Tate), §4.3, Thm. 4.3.1, p. 334"]
theorem prod_modulus_eq_one {t : F} (ht : t ≠ 0) :
    mixedEmbedding.norm (mixedEmbedding F t) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t) = 1 := by
  have h1 : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) t)) =
      ∏ᶠ w : FinitePlace F, w t := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    · exact finprod_congr fun w => by
        rw [modK_algebraMap_eq _ ht]
  rw [h1, FinitePlace.prod_eq_inv_abs_norm ht, mixedEmbedding.norm_eq_norm]
  have : (Algebra.norm ℚ t : ℝ) ≠ 0 := by exact_mod_cast (Algebra.norm_ne_zero_iff.mpr ht)
  push_cast
  field_simp

/-! ### Hilbert reciprocity in product form -/

open scoped Classical

/-- The Hilbert symbol on $F_\infty = \mathbb R^{r_1}\times\mathbb C^{r_2}$: $\prod_{w\ \mathrm{real}}(s_w, t_w)_{\mathbb R}$
(complex places contribute $1$). -/
def hilbInf (s t : mixedSpace F) : ℤ := ∏ w : {w : InfinitePlace F // IsReal w}, hilbertSymbol ℝ (s.1 w) (t.1 w)

lemma hilbInf_eq (a b : F) :
    (hilbInf (mixedEmbedding F a) (mixedEmbedding F b) : ℂ) =
      ∏ w : InfinitePlace F, ((NFPlace.infinite w).hilbert a b : ℂ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => IsReal w)]
  have : ∏ w : {w : InfinitePlace F // ¬ IsReal w}, ((NFPlace.infinite w.1).hilbert a b : ℂ) = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [HN.hilbert_infinite_complex (not_isReal_iff_isComplex.mp w.2)]; simp
  rw [this, mul_one, hilbInf]
  push_cast
  exact Finset.prod_congr rfl fun w _ => by rw [HN.hilbert_infinite_real w.2]

/-- **Hilbert reciprocity, product form:** for $a, b \in F^\times$,
$$\prod_{w\mid\infty}(a,b)_w\cdot\prod_v(a,b)_v = 1.$$ -/
@[kb "omeara1963" "§71D, 71:18, p. 201"]
theorem prod_hilbert_eq_one {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (hilbInf (mixedEmbedding F a) (mixedEmbedding F b) : ℂ) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        (hilbertSymbol (v.adicCompletion F) (algebraMap F _ a) (algebraMap F _ b) : ℂ) = 1 := by
  rw [hilbInf_eq]
  have hinf := HN.prod_hilbert_infinite_mul_weilInf a b ha hb
  have hfin := HN.finprod_hilbert_finite_mul_weilV a b ha hb
  have eA := weilInf_mul_finprod_weilV a ha
  have eB := weilInf_mul_finprod_weilV b hb
  have eAB := weilInf_mul_finprod_weilV (a * b) (mul_ne_zero ha hb)
  have e1 := weilInf_mul_finprod_weilV (1 : F) one_ne_zero
  set PI := ∏ w : InfinitePlace F, ((NFPlace.infinite w).hilbert a b : ℂ)
  set PF := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((NFPlace.finite v).hilbert a b : ℂ)
  have hPF : (∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (hilbertSymbol (v.adicCompletion F) (algebraMap F _ a) (algebraMap F _ b) : ℂ)) = PF := rfl
  rw [hPF]
  set IA := weilInf (mixedEmbedding F a)
  set IB := weilInf (mixedEmbedding F b)
  set IAB := weilInf (mixedEmbedding F (a * b))
  set I1 := weilInf (mixedEmbedding F 1)
  set FA := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) a)
  set FB := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b)
  set FAB := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) (a * b))
  set F1 := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) (1 : F))
  have key : PI * PF * (IA * FA) * (IB * FB) = (IAB * FAB) * (I1 * F1) := by
    linear_combination (PF * FA * FB) * hinf + (IAB * I1) * hfin
  rw [eA, eB, eAB, e1] at key
  linear_combination key

end QuadFormsKB.WeilRep
