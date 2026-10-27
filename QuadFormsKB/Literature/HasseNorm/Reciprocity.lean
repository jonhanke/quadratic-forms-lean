import QuadFormsKB.Literature.HasseNorm.LocalIndexTwo
import QuadFormsKB.Analysis.WeilIndexGlobal
import QuadFormsKB.Analysis.WeilIndexLocal

/-!
# Hilbert reciprocity over a number field, via the Weil index

For a number field $F$ and $a, b \in F^\times$: $(a,b)_v = 1$ for all but finitely many places $v$, and
$$\prod_v (a,b)_v = 1$$
(`hilbert_product_formula_nf`, in the form of the $\mathbb{Q}$ statement `hilbert_product_formula`: the set of places
with $(a,b)_v = -1$ is finite and has even cardinality).

**Route (Weil, Acta Math. 111, 1964).** Let $\gamma_v(t)$ be the (unnormalized) Weil constant of $x \mapsto \psi_v(tx^2)$:
the Gauss integral $\int_{\|x\|_v \le R}\psi_v(tx^2)\,dx$ ($R \gg 0$) at finite places (`weilV`), and
$(i/(2t))^{1/2}$, $(2|t|)^{-1}$ at real and complex places (`weilR`, `weilC`). Then

1. **local identity** at every place (dyadic and archimedean included):
   $\gamma_v(ab)\,\gamma_v(1) = (a,b)_v\,\gamma_v(a)\,\gamma_v(b)$ (`weilV_mul_identity`, from
   `Weil.gaussInt_mul_identity`; `weilR_mul_identity`; `weilC_mul_identity`);
2. **global product formula** $\prod_v\gamma_v(t) = 1$ for $t \in F^\times$ (`weilInf_mul_finprod_weilV`, adelic
   Poisson summation);
3. multiply (1) over all places and use (2) four times.

The Hilbert symbol at a finite place enters only through its characterization by norms
(`hilbertSymbol_eq_one_iff_norm`) and its multiplicativity (`hilbertSymbol_mul_left_finite_nf`); no class
field theory is used.

As a consequence the Serre-route bundle `NFInputs.HMInputs F` now needs only elements with prescribed local
symbols (`hmInputs_of_prescribed`); those are proved downstream (`PresNF.exists_prescribed_hilbert`,
`LocalGlobal/PrescribedNF.lean`), giving the unconditional `NFInputs.hmInputs`.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Metric
open QuadFormsKB.Analysis
open scoped Real

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

/-! ### The local identity at a finite place -/

section Finite

variable (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- The Hilbert symbol $(a, \cdot)_v$ is a norm-residue character in the sense of `Weil.IsNormChar`. -/
lemma isNormChar_hilbertSymbol {a : Fv} (ha : a ≠ 0) :
    Weil.IsNormChar a (hilbertSymbol Fv a) where
  pm s := hilbertSymbol_eq_one_or _ a s
  one_iff s := by
    rw [hilbertSymbol_eq_one_iff_norm Fv two_ne_zero ha]
    constructor
    · rintro ⟨x₀, x₁, h⟩; exact ⟨(x₀, x₁), h.symm⟩
    · rintro ⟨z, rfl⟩; exact ⟨z.1, z.2, rfl⟩
  mul s t hs ht := by
    rw [hilbertSymbol_comm, hilbertSymbol_mul_left_finite_nf v s t a hs ht ha, hilbertSymbol_comm _ s,
      hilbertSymbol_comm _ t]

/-- The local square theorem in the form needed by `Weil.gaussInt_mul_identity`: all $u$ with
$\|u - 1\| \le \|4\|/2$ are squares. -/
lemma exists_sq_closedBall :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ u : Fv, u ∈ closedBall (1 : Fv) ρ → IsSquare u := by
  have h4 : 0 < ‖(4 : Fv)‖ := norm_pos_iff.mpr (by norm_num)
  have h4le : ‖(4 : Fv)‖ ≤ 1 := by
    rw [show (4 : Fv) = ((4 : ℕ) : Fv) by norm_num]; exact IsUltrametricDist.norm_natCast_le_one _ _
  refine ⟨‖(4 : Fv)‖ / 2, by positivity, by linarith, fun u hu => ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hu
  refine isSquare_of_valued_sub_one_lt v u ((Valued.toNormedField.norm_lt_iff).mp ?_)
  linarith

/-- **The local identity for the Weil constant at a finite place** (dyadic places included): for
$a, b \in F_v^\times$, $\gamma_v(ab)\,\gamma_v(1) = (a,b)_v\,\gamma_v(a)\,\gamma_v(b)$. -/
@[kb "weil1964" "§§22–28 (the index of $\\langle a, b\\rangle$ and the Hilbert symbol) [unverified]"]
theorem weilV_mul_identity {a b : Fv} (ha : a ≠ 0) (hb : b ≠ 0) :
    weilV v (a * b) * weilV v 1 = (hilbertSymbol Fv a b : ℂ) * weilV v a * weilV v b :=
  Weil.gaussInt_mul_identity (isStdChar_psiV v) two_ne_zero (isNormChar_hilbertSymbol v ha)
    (exists_sq_closedBall v) ha hb

lemma weilV_ne_zero {b : Fv} (hb : b ≠ 0) : weilV v b ≠ 0 :=
  Weil.gaussInt_ne_zero (isStdChar_psiV v) two_ne_zero hb

end Finite

/-! ### The local identity at the infinite places -/

section Infinite

lemma weilR_eq (t : ℝ) (ht : t ≠ 0) :
    weilR t = (if 0 < t then Complex.I ^ (1 / 2 : ℂ) else (-Complex.I) ^ (1 / 2 : ℂ)) *
      ((Real.sqrt (2 * |t|)⁻¹ : ℝ) : ℂ) := by
  have hsqrt : ∀ x : ℝ, 0 < x → ((x : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]; push_cast; ring_nf
  have hre : ∀ x : ℝ, 0 < x → 0 < ((x : ℂ)).re := fun x hx => by simpa using hx
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), weilR,
      show Complex.I / (2 * (t : ℂ)) = -Complex.I * (((2 * |t|)⁻¹ : ℝ) : ℂ) by
        rw [abs_of_neg hneg]; push_cast; field_simp,
      cpow_mul_of_re (by simp) (neg_ne_zero.mpr Complex.I_ne_zero)
        (hre _ (inv_pos.mpr (by positivity))), hsqrt _ (inv_pos.mpr (by positivity)),
      Real.sqrt_inv]
  · rw [if_pos hpos, weilR,
      show Complex.I / (2 * (t : ℂ)) = Complex.I * (((2 * |t|)⁻¹ : ℝ) : ℂ) by
        rw [abs_of_pos hpos]; push_cast; field_simp,
      cpow_mul_of_re (by simp) Complex.I_ne_zero (hre _ (inv_pos.mpr (by positivity))),
      hsqrt _ (inv_pos.mpr (by positivity)), Real.sqrt_inv]

/-- **The local identity at a real place:** $\gamma_{\mathbb R}(ab)\gamma_{\mathbb R}(1) = (a,b)_{\mathbb R}\,
\gamma_{\mathbb R}(a)\gamma_{\mathbb R}(b)$ (the phases $e^{\pm\pi i/4}$ multiply to $-1$ exactly when $a, b < 0$). -/
@[kb "weil1964" "§26 [unverified]"]
theorem weilR_mul_identity {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    weilR (a * b) * weilR 1 = (hilbertSymbol ℝ a b : ℂ) * weilR a * weilR b := by
  rw [weilR_eq _ (mul_ne_zero ha hb), weilR_eq _ one_ne_zero, weilR_eq _ ha, weilR_eq _ hb]
  have hsp : Complex.I ^ (1 / 2 : ℂ) * Complex.I ^ (1 / 2 : ℂ) = Complex.I := by
    rw [← sq, show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num]; exact Complex.cpow_ofNat_inv_pow _ 2
  have hsn : (-Complex.I) ^ (1 / 2 : ℂ) * (-Complex.I) ^ (1 / 2 : ℂ) = -Complex.I := by
    rw [← sq, show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num]; exact Complex.cpow_ofNat_inv_pow _ 2
  set sp : ℂ := Complex.I ^ (1 / 2 : ℂ)
  set sn : ℂ := (-Complex.I) ^ (1 / 2 : ℂ)
  have hroot : Real.sqrt (2 * |a * b|)⁻¹ * Real.sqrt (2 * |(1 : ℝ)|)⁻¹ =
      Real.sqrt (2 * |a|)⁻¹ * Real.sqrt (2 * |b|)⁻¹ := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [abs_mul, abs_one]; field_simp
  have hroot' : ((Real.sqrt (2 * |a * b|)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (2 * |(1 : ℝ)|)⁻¹ : ℝ) : ℂ) =
      ((Real.sqrt (2 * |a|)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (2 * |b|)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hroot, Complex.ofReal_mul]
  have h1 : (0 : ℝ) < 1 := one_pos
  rw [if_pos h1]
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · -- a < 0, b < 0
    have hab : 0 < a * b := mul_pos_of_neg_of_neg ha' hb'
    have hs : hilbertSymbol ℝ a b = -1 := (hilbertSymbol_real a b ha hb).mpr ⟨ha', hb'⟩
    rw [if_pos hab, if_neg (not_lt.mpr ha'.le), if_neg (not_lt.mpr hb'.le), hs]
    push_cast
    linear_combination (((Real.sqrt (2 * |a * b|)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (2 * |(1 : ℝ)|)⁻¹ : ℝ) : ℂ)) *
      hsp + (((Real.sqrt (2 * |a|)⁻¹ : ℝ) : ℂ) * ((Real.sqrt (2 * |b|)⁻¹ : ℝ) : ℂ)) * hsn +
      Complex.I * hroot'
  · -- a < 0, b > 0
    have hab : ¬ 0 < a * b := not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg ha'.le hb'.le)
    have hs : hilbertSymbol ℝ a b = 1 :=
      (hilbertSymbol_eq_one_or _ a b).resolve_right fun h =>
        absurd ((hilbertSymbol_real a b ha hb).mp h).2 (not_lt.mpr hb'.le)
    rw [if_neg hab, if_neg (not_lt.mpr ha'.le), if_pos hb', hs]
    push_cast
    linear_combination (sn * sp) * hroot'
  · -- a > 0, b < 0
    have hab : ¬ 0 < a * b := not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos ha'.le hb'.le)
    have hs : hilbertSymbol ℝ a b = 1 :=
      (hilbertSymbol_eq_one_or _ a b).resolve_right fun h =>
        absurd ((hilbertSymbol_real a b ha hb).mp h).1 (not_lt.mpr ha'.le)
    rw [if_neg hab, if_pos ha', if_neg (not_lt.mpr hb'.le), hs]
    push_cast
    linear_combination (sn * sp) * hroot'
  · -- a > 0, b > 0
    have hab : 0 < a * b := mul_pos ha' hb'
    have hs : hilbertSymbol ℝ a b = 1 :=
      (hilbertSymbol_eq_one_or _ a b).resolve_right fun h =>
        absurd ((hilbertSymbol_real a b ha hb).mp h).1 (not_lt.mpr ha'.le)
    rw [if_pos hab, if_pos ha', if_pos hb', hs]
    push_cast
    linear_combination (sp * sp) * hroot'

lemma hilbertSymbol_complex (a b : ℂ) : hilbertSymbol ℂ a b = 1 := by
  unfold hilbertSymbol
  rw [if_pos]
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq a (n := 2) (by norm_num)
  exact ⟨1, 0, s, by simp, by simp [hs]⟩

/-- **The local identity at a complex place:** $\gamma_{\mathbb C}(ab)\gamma_{\mathbb C}(1) =
\gamma_{\mathbb C}(a)\gamma_{\mathbb C}(b)$, and $(a,b)_{\mathbb C} = 1$. -/
@[kb "weil1964" "§26 [unverified]"]
theorem weilC_mul_identity (a b : ℂ) :
    weilC (a * b) * weilC 1 = (hilbertSymbol ℂ a b : ℂ) * weilC a * weilC b := by
  rw [hilbertSymbol_complex, weilC, weilC, weilC, weilC, norm_mul, norm_one]
  push_cast; ring

/-- Transport of the Hilbert symbol along a ring isomorphism. -/
lemma hilbertSymbol_ringEquiv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (a b : K) :
    hilbertSymbol K a b = hilbertSymbol L (e a) (e b) := by
  unfold hilbertSymbol
  congr 1
  apply propext
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨e x, e y, e z, ?_, ?_⟩
    · intro h0
      apply hne
      simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.injective] at h0 ⊢
      exact h0
    · rw [← map_pow, h]; simp
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨e.symm x, e.symm y, e.symm z, ?_, ?_⟩
    · intro h0
      apply hne
      simp only [Prod.mk_eq_zero, map_eq_zero_iff _ e.symm.injective] at h0 ⊢
      exact h0
    · apply e.injective
      simp [h]

lemma hilbert_infinite_real {w : InfinitePlace F} (hw : IsReal w) (a b : F) :
    (NFPlace.infinite w).hilbert a b =
      hilbertSymbol ℝ ((mixedEmbedding F a).1 ⟨w, hw⟩) ((mixedEmbedding F b).1 ⟨w, hw⟩) := by
  rw [NFPlace.hilbert, hilbertSymbol_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw),
    mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal]
  simp

lemma hilbert_infinite_complex {w : InfinitePlace F} (hw : IsComplex w) (a b : F) :
    (NFPlace.infinite w).hilbert a b = 1 := by
  rw [NFPlace.hilbert, hilbertSymbol_ringEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw),
    hilbertSymbol_complex]

end Infinite

/-! ### Hilbert reciprocity -/

section Global

open scoped Classical

/-- The local identities at the infinite places, multiplied together:
$\prod_{w\mid\infty}(a,b)_w\cdot\gamma_\infty(a)\gamma_\infty(b) = \gamma_\infty(ab)\gamma_\infty(1)$. -/
lemma prod_hilbert_infinite_mul_weilInf (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ w : InfinitePlace F, ((NFPlace.infinite w).hilbert a b : ℂ)) * weilInf (mixedEmbedding F a) *
      weilInf (mixedEmbedding F b) =
      weilInf (mixedEmbedding F (a * b)) * weilInf (mixedEmbedding F 1) := by
  have hsplit : (∏ w : InfinitePlace F, ((NFPlace.infinite w).hilbert a b : ℂ)) =
      ∏ w : {w : InfinitePlace F // IsReal w}, ((NFPlace.infinite w.1).hilbert a b : ℂ) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => IsReal w)]
    have : ∏ w : {w : InfinitePlace F // ¬ IsReal w}, ((NFPlace.infinite w.1).hilbert a b : ℂ) = 1 := by
      refine Finset.prod_eq_one fun w _ => ?_
      rw [hilbert_infinite_complex (not_isReal_iff_isComplex.mp w.2)]; simp
    rw [this, mul_one]
  have hR : ∀ w : {w : InfinitePlace F // IsReal w},
      weilR ((mixedEmbedding F (a * b)).1 w) * weilR ((mixedEmbedding F 1).1 w) =
        ((NFPlace.infinite w.1).hilbert a b : ℂ) * weilR ((mixedEmbedding F a).1 w) *
          weilR ((mixedEmbedding F b).1 w) := by
    intro w
    rw [map_mul, map_one, Prod.fst_mul, Prod.fst_one, Pi.mul_apply, Pi.one_apply,
      hilbert_infinite_real w.2]
    exact weilR_mul_identity (mixedEmbedding_fst_ne_zero ha w) (mixedEmbedding_fst_ne_zero hb w)
  have hC : ∀ w : {w : InfinitePlace F // IsComplex w},
      weilC ((mixedEmbedding F (a * b)).2 w) * weilC ((mixedEmbedding F 1).2 w) =
        weilC ((mixedEmbedding F a).2 w) * weilC ((mixedEmbedding F b).2 w) := by
    intro w
    rw [map_mul, map_one, Prod.snd_mul, Prod.snd_one, Pi.mul_apply, Pi.one_apply, weilC_mul_identity,
      hilbertSymbol_complex]
    push_cast; ring
  have hRp := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hR w
  have hCp := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hC w
  simp only [Finset.prod_mul_distrib] at hRp hCp
  rw [hsplit, weilInf, weilInf, weilInf, weilInf]
  linear_combination ((∏ w : {w : InfinitePlace F // IsComplex w}, weilC ((mixedEmbedding F (a * b)).2 w)) *
      ∏ w : {w : InfinitePlace F // IsComplex w}, weilC ((mixedEmbedding F 1).2 w)) * hRp.symm +
    ((∏ w : {w : InfinitePlace F // IsReal w}, ((NFPlace.infinite w.1).hilbert a b : ℂ)) *
      (∏ w : {w : InfinitePlace F // IsReal w}, weilR ((mixedEmbedding F a).1 w)) *
      ∏ w : {w : InfinitePlace F // IsReal w}, weilR ((mixedEmbedding F b).1 w)) * hCp.symm

/-- The finite places where $(a,b)_v = -1$ are finitely many (they lie among the places where one of
$\gamma_v(a), \gamma_v(b), \gamma_v(ab), \gamma_v(1)$ is not $1$). -/
lemma finite_hilbert_finite_eq_neg_one (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (NFPlace.finite v).hilbert a b = -1}.Finite := by
  refine ((finite_weilV_ne_one a ha).union ((finite_weilV_ne_one b hb).union
    ((finite_weilV_ne_one (a * b) (mul_ne_zero ha hb)).union (finite_weilV_ne_one 1 one_ne_zero)))).subset
    fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hid := weilV_mul_identity v ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr ha)
    ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hb)
  rw [← map_mul, h3, ← map_one (algebraMap F (v.adicCompletion F)), h4, h1, h2] at hid
  have : (hilbertSymbol (v.adicCompletion F) (algebraMap F _ a) (algebraMap F _ b) : ℂ) = 1 := by
    linear_combination -hid
  have hv' : (NFPlace.finite v).hilbert a b = -1 := hv
  rw [NFPlace.hilbert] at hv'
  rw [hv'] at this
  norm_num at this

/-- The local identities at the finite places, multiplied together. -/
lemma finprod_hilbert_finite_mul_weilV (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ((NFPlace.finite v).hilbert a b : ℂ)) *
      (∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) a)) *
        (∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b)) =
      (∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) (a * b))) *
        ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) 1) := by
  have hfh : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((NFPlace.finite v).hilbert a b : ℂ) := by
    refine (finite_hilbert_finite_eq_neg_one a b ha hb).subset fun v hv => ?_
    simp only [Function.mem_mulSupport, ne_eq] at hv
    rcases hilbertSymbol_eq_one_or (v.adicCompletion F) (algebraMap F _ a) (algebraMap F _ b) with h | h
    · exact absurd (by rw [NFPlace.hilbert, h]; simp) hv
    · exact h
  have hw := fun x (hx : x ≠ 0) => finite_weilV_ne_one (F := F) x hx
  have hfha : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((NFPlace.finite v).hilbert a b : ℂ) * weilV v (algebraMap F (v.adicCompletion F) a) :=
    hfh.mul (hw a ha)
  rw [← finprod_mul_distrib hfh (hw a ha), ← finprod_mul_distrib hfha (hw b hb),
    ← finprod_mul_distrib (hw _ (mul_ne_zero ha hb)) (hw 1 one_ne_zero)]
  refine finprod_congr fun v => ?_
  rw [map_mul, map_one, weilV_mul_identity v ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr ha)
    ((map_ne_zero (algebraMap F (v.adicCompletion F))).mpr hb)]
  rfl

/-- **Hilbert reciprocity over a number field** (Hilbert's product formula): for $a, b \in F^\times$, the local
symbol $(a,b)_v$ is $-1$ at only finitely many places $v$ of $F$, and at an even number of them; equivalently
$\prod_v (a,b)_v = 1$.

*Proof* (Weil's route, no class field theory): the local identities
$\gamma_v(ab)\gamma_v(1) = (a,b)_v\gamma_v(a)\gamma_v(b)$ at every place multiply, by Weil's product formula
$\prod_v\gamma_v(t) = 1$ (`weilInf_mul_finprod_weilV`, adelic Poisson summation), to $\prod_v(a,b)_v = 1$. -/
@[kb "omeara1963" "§71D, 71:18, p. 201"]
theorem hilbert_product_formula_nf (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    {v : NFPlace F | v.hilbert a b = -1}.Finite ∧ Even {v : NFPlace F | v.hilbert a b = -1}.ncard := by
  set Sinf : Set (InfinitePlace F) := {w | (NFPlace.infinite w).hilbert a b = -1}
  set Sfin : Set (HeightOneSpectrum (𝓞 F)) := {v | (NFPlace.finite v).hilbert a b = -1}
  have hSfin : Sfin.Finite := finite_hilbert_finite_eq_neg_one a b ha hb
  have hSinf : Sinf.Finite := Set.toFinite _
  have hS : {v : NFPlace F | v.hilbert a b = -1} = NFPlace.infinite '' Sinf ∪ NFPlace.finite '' Sfin := by
    ext v
    cases v with
    | infinite w => simp [Sinf, Sfin]
    | finite v => simp [Sinf, Sfin]
  have hinjI : Function.Injective (NFPlace.infinite (F := F)) := fun _ _ h => NFPlace.infinite.inj h
  have hinjF : Function.Injective (NFPlace.finite (F := F)) := fun _ _ h => NFPlace.finite.inj h
  have hdisj : Disjoint (NFPlace.infinite '' Sinf) (NFPlace.finite '' Sfin) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w, -, rfl⟩ ⟨v, -, h⟩
    cases h
  refine ⟨hS ▸ (hSinf.image _).union (hSfin.image _), ?_⟩
  rw [hS, Set.ncard_union_eq hdisj (hSinf.image _) (hSfin.image _), Set.ncard_image_of_injective _ hinjI,
    Set.ncard_image_of_injective _ hinjF]
  -- the product of all local symbols is `1`
  have hpm : ∀ v : NFPlace F, v.hilbert a b = 1 ∨ v.hilbert a b = -1 := by
    intro v; cases v <;> exact hilbertSymbol_eq_one_or _ _ _
  have hinf := prod_hilbert_infinite_mul_weilInf a b ha hb
  have hfin := finprod_hilbert_finite_mul_weilV a b ha hb
  have eA := weilInf_mul_finprod_weilV a ha
  have eB := weilInf_mul_finprod_weilV b hb
  have eAB := weilInf_mul_finprod_weilV (a * b) (mul_ne_zero ha hb)
  have e1 := weilInf_mul_finprod_weilV (1 : F) one_ne_zero
  set PI := ∏ w : InfinitePlace F, ((NFPlace.infinite w).hilbert a b : ℂ)
  set PF := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((NFPlace.finite v).hilbert a b : ℂ)
  set IA := weilInf (mixedEmbedding F a)
  set IB := weilInf (mixedEmbedding F b)
  set IAB := weilInf (mixedEmbedding F (a * b))
  set I1 := weilInf (mixedEmbedding F 1)
  set FA := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) a)
  set FB := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) b)
  set FAB := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) (a * b))
  set F1 := ∏ᶠ v, weilV v (algebraMap F (v.adicCompletion F) (1 : F))
  have hprod : PI * PF = 1 := by
    -- `PI PF (IA FA)(IB FB) = (IAB FAB)(I1 F1)`
    have key : PI * PF * (IA * FA) * (IB * FB) = (IAB * FAB) * (I1 * F1) := by
      linear_combination (PF * FA * FB) * hinf + (IAB * I1) * hfin
    rw [eA, eB, eAB, e1] at key
    linear_combination key
  -- each product is a power of `-1`
  have hinfpow : PI = (-1) ^ Sinf.ncard := by
    simp only [PI]
    rw [Finset.prod_congr rfl (g := fun w => if (NFPlace.infinite w).hilbert a b = -1 then (-1 : ℂ) else 1)
      (fun w _ => by
        rcases hpm (NFPlace.infinite w) with h | h
        · rw [if_neg (by rw [h]; norm_num), h]; simp
        · rw [if_pos h, h]; simp),
      Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Set.ncard_eq_toFinset_card' Sinf]
    congr 2
    ext w; simp [Sinf]
  have hfinpow : PF = (-1) ^ Sfin.ncard := by
    simp only [PF]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hSfin.toFinset) (fun v hv => by
      simp only [Function.mem_mulSupport, ne_eq] at hv
      simp only [Set.Finite.coe_toFinset]
      exact (hpm _).resolve_left fun h => hv (by rw [h]; simp))]
    rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℂ)) (fun v hv => by
        rw [Set.Finite.mem_toFinset] at hv; rw [show (NFPlace.finite v).hilbert a b = -1 from hv]; simp),
      Finset.prod_const, Set.ncard_eq_toFinset_card _ hSfin]
  rw [hinfpow, hfinpow, ← pow_add] at hprod
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hprod

/-- **The Serre-route bundle from prescribed symbols alone.** With Hilbert reciprocity over $F$ proved
(`hilbert_product_formula_nf`), `NFInputs.HMInputs F` follows from the existence of elements with prescribed
local symbols (`hpres`, the field `prescribed_hilbert`) alone. (`hpres` is proved downstream as
`PresNF.exists_prescribed_hilbert`; the unconditional bundle is `NFInputs.hmInputs`.) -/
theorem hmInputs_of_prescribed
    (hpres : ∀ {ι : Type} [Fintype ι] (a : ι → F), (∀ i, a i ≠ 0) →
      ∀ ε : ι → NFPlace F → ℤ, (∀ i v, ε i v = 1 ∨ ε i v = -1) →
      {v : NFPlace F | ∃ i, ε i v = -1}.Finite →
      (∀ i, Even {v : NFPlace F | ε i v = -1}.ncard) →
      (∀ v : NFPlace F, v.atPlace fun K _ _ =>
        ∃ x : K, x ≠ 0 ∧ ∀ i, hilbertSymbol K (algebraMap F K (a i)) x = ε i v) →
      ∃ x : F, x ≠ 0 ∧ ∀ i v, v.hilbert (a i) x = ε i v) :
    NFInputs.HMInputs F :=
  hmInputs_of hilbert_product_formula_nf hpres

end Global

end QuadFormsKB.HN
