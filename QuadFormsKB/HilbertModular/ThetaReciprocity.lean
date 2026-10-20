import QuadFormsKB.HilbertModular.ThetaGamma0

/-!
# Theta series over a totally real field VI: reciprocity for the theta multiplier

Notation of `ThetaGamma0.lean`. For $a, t \in \mathcal{O}_F$ the **dual Gauss sum** (`gaussSumDualF`) is
$$G^\#(t, a) = \sum_{r\in(\mathcal{O}_F/a)^n}e\Big(\operatorname{Tr}\frac{t\,Q^\#(r)}{a}\Big),\qquad Q^\#(y) = \tfrac14y^{\mathsf T}A^{-1}y.$$

**Reciprocity** (`thetaMultF_reciprocity`): for $c \in \mathfrak N$ (a level), $c \ne 0$, $a \ne 0$ coprime to the different
$\mathfrak d$,
$$M_Q(a, c) = N(a)^{-k}\,G^\#(-c, a),\qquad N(a)^k = \prod_v\varphi_v(a)^k.$$
So the Gauss sum modulo $c$ (whose prime factors divide the level) is traded for one modulo $a$, which can be taken prime to
$2\det H$ and $\mathfrak d$. This is `QuadFormsKB.Siegel.thetaMult_reciprocity` over $F$, where for $F = \mathbb{Q}$ the level was
pulled into the form ($NQ^*$); over $F$ the level condition makes $cQ^\#$ integral for the trace form directly.

*Proof.* Expand $\theta_Q$ at $z = \frac ac - \frac1{c^2u}$ (`tsum_latSet_cusp` for $\mathcal{O}_F^n$); alternatively write $z = -1/\tau$,
$\tau = -\frac ca - \frac1{a^2u'}$, $u' = u - \frac1{ac}$, apply the inversion (`thetaLat_inversion`) and expand the dual theta series of
$L^\# = (\mathfrak d^{-1})^n$ at the cusp $-c/a$ (`tsum_latSet_cusp` for $L^\#$, whose dual is $\mathcal{O}_F^n$ again; representatives of
$L^\#/aL^\#$ are taken in $\mathcal{O}_F^n$, which needs $a$ prime to $\mathfrak d$). Let $u = (it, \dots, it)$, $t \to \infty$: only the
constant terms survive (dominated convergence, `tendsto_tsum_thetaTerm`). This gives $M_Q(a, c) = U_Q\,N(a)^{-k}G^\#(-c, a)$
with a constant $U_Q > 0$ depending only on $Q$ (`thetaRecConst`, a product of covolumes); $U_Q = 1$ follows from
$m_Q(L(c))^2 = m_Q(L(2c))$ for $L(c) = \begin{pmatrix}1&0\\c&1\end{pmatrix}$, where $G^\#(\cdot, 1) = 1$ (`thetaRecConst_eq_one`).
-/

open Matrix NumberField NumberField.InfinitePlace Complex Filter Topology
open scoped Real nonZeroDivisors MatrixGroups ModularForm

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace QuadFormsKB.HilbertModular

noncomputable section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-! ### The dual lattice $(\mathfrak d^{-1})^n$ as a lattice $\bigoplus_iI_i$ -/

/-- The inverse different as a unit fractional ideal. -/
def invDiffUnit : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (invDifferent F) invDifferent_ne_zero

/-- The ideals $(\mathfrak d^{-1}, \dots, \mathfrak d^{-1})$. -/
abbrev invDiffIdeals : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun _ => invDiffUnit

lemma latSet_invDiff : latSet (invDiffIdeals (F := F) (n := n)) = dualSet (oneIdeals (F := F)) := by
  ext x
  rw [mem_dualSet_one]
  simp [latSet, invDiffUnit]

lemma dualSet_invDiff : dualSet (invDiffIdeals (F := F) (n := n)) = latSet (oneIdeals (F := F)) := by
  ext x
  rw [mem_latSet_one]
  have h : FractionalIdeal.dual ℤ ℚ (invDifferent F) = (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    FractionalIdeal.dual_dual ℤ ℚ (L := F) (B := 𝓞 F) 1
  simp [dualSet, invDiffUnit, h]

lemma isTotPosGram_dual {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    IsTotPosGram ((1 / 4 : F) • (gramF Q)⁻¹) := by
  intro v
  rw [Matrix.map_smul' _ _ _ (map_mul _), map_inv_realEmb hQ v]
  simp only [map_div₀, map_one, map_ofNat]
  exact ((hQ v).inv).smul (by norm_num)

lemma dual_dual_gram {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) :
    (1 / 4 : F) • ((1 / 4 : F) • (gramF Q)⁻¹)⁻¹ = gramF Q := by
  have hu : IsUnit (gramF Q).det := isUnit_iff_ne_zero.mpr (gramF_det_ne_zero hQ)
  have h : ((1 / 4 : F) • (gramF Q)⁻¹)⁻¹ = (4 : F) • gramF Q := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_nonsing_inv _ hu, smul_smul]
    norm_num
  rw [h, smul_smul]
  norm_num

/-! ### Representatives of $L^\#/aL^\#$ in $\mathcal{O}_F^n$ for $a$ prime to $\mathfrak d$ -/

lemma mul_mem_one_of_mem_differentIdeal {t : 𝓞 F} (ht : t ∈ differentIdeal ℤ (𝓞 F)) {y : F}
    (hy : y ∈ invDifferent F) : algebraMap (𝓞 F) F t * y ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  have h1 : algebraMap (𝓞 F) F t ∈ ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (𝓞 F)⁰ F) := (FractionalIdeal.mem_coeIdeal _).mpr ⟨t, ht, rfl⟩
  rw [coeIdeal_differentIdeal ℤ ℚ] at h1
  have := FractionalIdeal.mul_mem_mul h1 hy
  rwa [show invDifferent F = FractionalIdeal.dual ℤ ℚ 1 from rfl,
    inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)] at this

lemma exists_different_add_mul {a : 𝓞 F} (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) :
    ∃ t s : 𝓞 F, t ∈ differentIdeal ℤ (𝓞 F) ∧ t + a * s = 1 := by
  have h1 : (1 : 𝓞 F) ∈ Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) := by rw [ha]; trivial
  obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  exact ⟨t, s, ht, by rw [← hxt]; ring⟩

/-- For $a$ prime to $\mathfrak d$: an element of $\mathcal{O}_F \cap a\mathfrak d^{-1}$ lies in $a\mathcal{O}_F$. -/
lemma mem_one_of_mul_mem {a : 𝓞 F} (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤)
    {δ : F} (hδ : δ ∈ invDifferent F) (hw : algebraMap (𝓞 F) F a * δ ∈ (1 : FractionalIdeal (𝓞 F)⁰ F)) :
    δ ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  obtain ⟨t, s, ht, hts⟩ := exists_different_add_mul ha
  have h1 : δ = algebraMap (𝓞 F) F t * δ + algebraMap (𝓞 F) F s * (algebraMap (𝓞 F) F a * δ) := by
    have := congrArg (algebraMap (𝓞 F) F) hts
    simp only [map_add, map_mul, map_one] at this
    linear_combination (-δ) * this
  rw [h1]
  refine Submodule.add_mem _ (mul_mem_one_of_mem_differentIdeal ht hδ) ?_
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ s hw

lemma mem_latSet_invDiff {x : Fin n → F} :
    x ∈ latSet (invDiffIdeals (F := F) (n := n)) ↔ ∀ i, x i ∈ invDifferent F := by
  rw [latSet_invDiff, mem_dualSet_one]

/-- **Division with remainder in $(\mathfrak d^{-1})^n$ modulo $a$** ($a \ne 0$ prime to $\mathfrak d$):
$(\mathcal{O}_F/a)^n \times L^\# \simeq L^\#$, $(r, y) \mapsto \tilde r + ay$. -/
def dualSplitEquiv {a : 𝓞 F} (ha0 : a ≠ 0) (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) :
    (Fin n → 𝓞 F ⧸ Ideal.span {a}) × latSet (invDiffIdeals (F := F) (n := n)) ≃
      latSet (invDiffIdeals (F := F) (n := n)) :=
  Equiv.ofBijective
    (fun p => ⟨vecO (fun i => qlift (p.1 i)) + algebraMap (𝓞 F) F a • (p.2 : Fin n → F),
      mem_latSet_invDiff.mpr fun i => Submodule.add_mem _ (algebraMap_mem_invDifferent _)
        (algebraMap_mul_mem_invDifferent _ (mem_latSet_invDiff.mp p.2.2 i))⟩) <| by
    have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h => ha0 (FaithfulSMul.algebraMap_injective (𝓞 F) F
      (by rw [map_zero]; exact h))
    constructor
    · rintro ⟨r, y⟩ ⟨r', y'⟩ h
      have h1 := congrArg Subtype.val h
      simp only at h1
      have hr : r = r' := by
        funext i
        have hi := congrFun h1 i
        simp only [vecO, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
        have hδ : (y' : Fin n → F) i - (y : Fin n → F) i ∈ invDifferent F :=
          Submodule.sub_mem _ (mem_latSet_invDiff.mp y'.2 i) (mem_latSet_invDiff.mp y.2 i)
        have hw : algebraMap (𝓞 F) F a * ((y' : Fin n → F) i - (y : Fin n → F) i) ∈
            (1 : FractionalIdeal (𝓞 F)⁰ F) := by
          rw [show algebraMap (𝓞 F) F a * ((y' : Fin n → F) i - (y : Fin n → F) i) =
            algebraMap (𝓞 F) F (qlift (r i) - qlift (r' i)) by rw [map_sub]; linear_combination -hi]
          exact algebraMap_mem_one _
        obtain ⟨δ, hδ'⟩ := (FractionalIdeal.mem_one_iff _).mp (mem_one_of_mul_mem ha hδ hw)
        have h2 : qlift (r i) - qlift (r' i) = a * δ := by
          apply FaithfulSMul.algebraMap_injective (𝓞 F) F
          rw [map_sub, map_mul, hδ']; linear_combination hi
        rw [← mk_qlift (r i), ← mk_qlift (r' i), Ideal.Quotient.eq, h2]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
      subst hr
      have h2 : algebraMap (𝓞 F) F a • (y : Fin n → F) = algebraMap (𝓞 F) F a • (y' : Fin n → F) :=
        add_left_cancel h1
      have := smul_right_injective (Fin n → F) haF h2
      simp only [Prod.mk.injEq, true_and]
      exact Subtype.ext this
    · rintro ⟨x, hx⟩
      obtain ⟨t, s, ht, hts⟩ := exists_different_add_mul ha
      have hx' := mem_latSet_invDiff.mp hx
      choose τ hτ using fun i => (FractionalIdeal.mem_one_iff _).mp
        (mul_mem_one_of_mem_differentIdeal ht (hx' i))
      set r : Fin n → 𝓞 F ⧸ Ideal.span {a} := fun i => Ideal.Quotient.mk _ (τ i)
      set y : Fin n → F := fun i => algebraMap (𝓞 F) F s * x i + algebraMap (𝓞 F) F (qdiv a (τ i))
      have hy : y ∈ latSet (invDiffIdeals (F := F) (n := n)) := mem_latSet_invDiff.mpr fun i =>
        Submodule.add_mem _ (algebraMap_mul_mem_invDifferent _ (hx' i)) (algebraMap_mem_invDifferent _)
      refine ⟨(r, ⟨y, hy⟩), Subtype.ext ?_⟩
      funext i
      have hts' := congrArg (algebraMap (𝓞 F) F) hts
      simp only [map_add, map_mul, map_one] at hts'
      have hq := congrArg (algebraMap (𝓞 F) F) (qdiv_spec a (τ i))
      simp only [map_add, map_mul] at hq
      simp only [vecO, Pi.add_apply, Pi.smul_apply, smul_eq_mul, r, y]
      rw [hτ i] at hq
      linear_combination (x i) * hts' - hq

lemma dualSplitEquiv_coe {a : 𝓞 F} (ha0 : a ≠ 0) (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤)
    (p : (Fin n → 𝓞 F ⧸ Ideal.span {a}) × latSet (invDiffIdeals (F := F) (n := n))) :
    ((dualSplitEquiv ha0 ha p : latSet _) : Fin n → F) =
      vecO (fun i => qlift (p.1 i)) + algebraMap (𝓞 F) F a • (p.2 : Fin n → F) := rfl

/-! ### Constant terms at $i\infty$ -/

lemma realEmb_qv_pos {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A) {x : Fin n → F}
    (hx : x ≠ 0) (v : InfinitePlace F) : 0 < realEmb F v (qv A x) := by
  rw [realEmb_qv]
  have hv : (fun i => realEmb F v (x i)) ≠ 0 := by
    intro h; apply hx; funext i
    have := congrFun h i
    simpa using (map_eq_zero_iff _ (realEmb F v).injective).mp this
  simpa using (hA v).dotProduct_mulVec_pos hv

/-- **Constant term at $i\infty$**: for $A$ totally positive definite, $S \ni 0$ a set of vectors with
$\sum_{x\in S}|e(\sum_v\varphi_v(Q(x))\,i)| < \infty$, $g$ bounded on $S$ and $\operatorname{Im}w_v(t) = t$,
$\sum_{x\in S}e(\sum_v\varphi_v(Q(x))w_v(t))\,g(x) \to g(0)$ as $t \to \infty$. -/
theorem tendsto_tsum_thetaTerm {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    {S : Set (Fin n → F)} (h0 : (0 : Fin n → F) ∈ S)
    (hsum : Summable fun x : S => ‖thetaTerm A x (fun _ => Complex.I)‖) (g : S → ℂ) {B : ℝ}
    (hg : ∀ x, ‖g x‖ ≤ B) (w : ℝ → InfinitePlace F → ℂ) (hw : ∀ t v, (w t v).im = t) :
    Tendsto (fun t => ∑' x : S, thetaTerm A x (w t) * g x) atTop (𝓝 (g ⟨0, h0⟩)) := by
  classical
  have hlim : ∀ x : S, Tendsto (fun t => thetaTerm A x (w t) * g x) atTop
      (𝓝 (if x = ⟨0, h0⟩ then g ⟨0, h0⟩ else 0)) := by
    intro x
    by_cases hx : x = ⟨0, h0⟩
    · subst hx
      simp only [↓reduceIte]
      have : ∀ t, thetaTerm A ((⟨0, h0⟩ : S) : Fin n → F) (w t) = 1 := by
        intro t; simp [thetaTerm, qv]
      simp_rw [this, one_mul]
      exact tendsto_const_nhds
    · simp only [hx, ↓reduceIte]
      have hx' : (x : Fin n → F) ≠ 0 := fun h => hx (Subtype.ext h)
      rw [show (0 : ℂ) = 0 * g x by ring]
      refine Tendsto.mul_const _ ?_
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hpos : 0 < ∑ v, realEmb F v (qv A x) :=
        Finset.sum_pos (fun v _ => realEmb_qv_pos hA hx' v) Finset.univ_nonempty
      have hn : ∀ t, ‖thetaTerm A x (w t)‖ =
          Real.exp (-(2 * Real.pi * ∑ v, realEmb F v (qv A x)) * t) := by
        intro t
        rw [norm_thetaTerm]
        congr 1
        simp_rw [hw]
        rw [← Finset.sum_mul]; ring
      simp_rw [hn]
      exact Real.tendsto_exp_atBot.comp
        (Tendsto.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos]) tendsto_id)
  have hbound : ∀ᶠ t in atTop, ∀ x : S,
      ‖thetaTerm A x (w t) * g x‖ ≤ ‖thetaTerm A x (fun _ => Complex.I)‖ * B := by
    filter_upwards [eventually_ge_atTop 1] with t ht x
    rw [norm_mul]
    exact mul_le_mul (norm_thetaTerm_le hA _ fun v => by simp [hw, ht]) (hg x) (norm_nonneg _)
      (norm_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence (hsum.mul_right B) hlim hbound
  rwa [tsum_ite_eq] at h

/-! ### The dual theta series at the cusp $-c/a$ -/

lemma mem_invDifferent_of_level {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {c : 𝓞 F} (hc : c ∈ 𝔑) {x y : Fin n → F}
    (hx : ∀ i, x i ∈ invDifferent F) (hy : ∀ i, y i ∈ invDifferent F) :
    algebraMap (𝓞 F) F c * (y ⬝ᵥ (hessF Q)⁻¹ *ᵥ x) ∈ invDifferent F := by
  rw [← qDual_add hQ, mul_sub, mul_sub]
  exact Submodule.sub_mem _ (Submodule.sub_mem _
    (hlev c hc _ fun i => Submodule.add_mem _ (hx i) (hy i)) (hlev c hc _ hx)) (hlev c hc _ hy)

/-- **The dual theta series at the cusp $-c/a$** ($c \in \mathfrak N$, $a \ne 0$ prime to $\mathfrak d$):
$$\theta^\#_Q\Big(-\frac ca - \frac{1}{a^2u}\Big) = C^\#(u)\sum_{\lambda\in\mathcal{O}_F^n}e\Big(\sum_v\varphi_v(Q(\lambda))u_v\Big)
  \sum_{r\in(\mathcal{O}_F/a)^n}e\Big(\operatorname{Tr}\Big(-\frac caQ^\#(r) + \sum_i\lambda_i\frac{r_i}{a}\Big)\Big).$$ -/
theorem thetaLatDual_cuspPt {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q))
    {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {a c : 𝓞 F} (ha0 : a ≠ 0)
    (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) (hc : c ∈ 𝔑) [Fintype (𝓞 F ⧸ Ideal.span {a})]
    {u : InfinitePlace F → ℂ} (hu : ∀ v, 0 < (u v).im) :
    thetaLatDual (gramF Q) oneIdeals (cuspPt (-algebraMap (𝓞 F) F c) (algebraMap (𝓞 F) F a) u) =
      (((∏ v, Real.sqrt (((1 / 4 : F) • (gramF Q)⁻¹).map (realEmb F v)).det)⁻¹ *
          (∏ i : Fin n, embDet (invDiffIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (-Complex.I * u v / 2) ^ ((n : ℂ) / 2)) *
          ∑' l : dualSet (invDiffIdeals (F := F) (n := n)), thetaTerm (gramF Q) l u *
            ∑ r : Fin n → 𝓞 F ⧸ Ideal.span {a}, cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
              (-algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a * qDual Q (vecO (fun i => qlift (r i))) +
                ∑ i, (l : Fin n → F) i * ((algebraMap (𝓞 F) F a)⁻¹ * vecO (fun i => qlift (r i)) i)) :
                  ℚ) : ℂ)) := by
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h => ha0 (FaithfulSMul.algebraMap_injective (𝓞 F) F (by
    rw [map_zero]; exact h))
  have hint : ∀ (r : Fin n → 𝓞 F ⧸ Ideal.span {a}) (y : latSet (invDiffIdeals (F := F) (n := n))),
      ∃ m : ℤ, Algebra.trace ℚ F (-algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a *
        (qDual Q (vecO (fun i => qlift (r i)) + algebraMap (𝓞 F) F a • (y : Fin n → F)) -
          qDual Q (vecO (fun i => qlift (r i))))) = m := by
    intro r y
    refine trace_int_of_mem_invDifferent ?_
    have hy := mem_latSet_invDiff.mp y.2
    have hρ : ∀ i, vecO (fun i => qlift (r i)) i ∈ invDifferent F :=
      fun i => algebraMap_mem_invDifferent _
    have h1 := qDual_add hQ (vecO (fun i => qlift (r i))) (algebraMap (𝓞 F) F a • (y : Fin n → F))
    have h2 : qDual Q (algebraMap (𝓞 F) F a • (y : Fin n → F)) =
        algebraMap (𝓞 F) F a ^ 2 * qDual Q y := qv_smul_vec _ _ _
    have h3 : (algebraMap (𝓞 F) F a • (y : Fin n → F)) ⬝ᵥ (hessF Q)⁻¹ *ᵥ vecO (fun i => qlift (r i)) =
        algebraMap (𝓞 F) F a * ((y : Fin n → F) ⬝ᵥ (hessF Q)⁻¹ *ᵥ vecO (fun i => qlift (r i))) :=
      smul_dotProduct _ _ _
    have key : -algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a *
        (qDual Q (vecO (fun i => qlift (r i)) + algebraMap (𝓞 F) F a • (y : Fin n → F)) -
          qDual Q (vecO (fun i => qlift (r i)))) =
        -(algebraMap (𝓞 F) F a * (algebraMap (𝓞 F) F c * qDual Q y) +
          algebraMap (𝓞 F) F c * ((y : Fin n → F) ⬝ᵥ (hessF Q)⁻¹ *ᵥ vecO (fun i => qlift (r i)))) := by
      have : qDual Q (vecO (fun i => qlift (r i)) + algebraMap (𝓞 F) F a • (y : Fin n → F)) -
          qDual Q (vecO (fun i => qlift (r i))) = algebraMap (𝓞 F) F a ^ 2 * qDual Q y +
            algebraMap (𝓞 F) F a * ((y : Fin n → F) ⬝ᵥ (hessF Q)⁻¹ *ᵥ vecO (fun i => qlift (r i))) := by
        rw [← h2, ← h3, ← h1]; ring
      rw [this]; field_simp
    rw [key]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (algebraMap_mul_mem_invDifferent _ (hlev c hc _ hy)) (mem_invDifferent_of_level hQ hlev hc hρ hy))
  have hexp := tsum_latSet_cusp (isTotPosGram_dual hQ) invDiffIdeals (-algebraMap (𝓞 F) F c)
    (algebraMap (𝓞 F) F a) haF
    (fun r : Fin n → 𝓞 F ⧸ Ideal.span {a} => vecO (fun i => qlift (r i)))
    (dualSplitEquiv ha0 ha) (dualSplitEquiv_coe ha0 ha) hint hu
  rw [thetaLatDual_eq_tsum_dualSet,
    ← (Equiv.subtypeEquivProp (congrArg (fun S : Set (Fin n → F) => (· ∈ S))
      (latSet_invDiff (F := F) (n := n)))).tsum_eq]
  rw [dual_dual_gram hQ] at hexp
  exact hexp

/-! ### Reciprocity -/

/-- **The dual Gauss sum** $G^\#(t, a) = \sum_{r\in(\mathcal{O}_F/a)^n}e\big(\operatorname{Tr}\frac{t\,Q^\#(r)}{a}\big)$, $Q^\#(y) = \frac14y^{\mathsf T}A^{-1}y$
(a `finsum`; finite for $a \ne 0$). For $F = \mathbb{Q}$ and $t = -c_0$ it is `QuadFormsKB.Siegel.gaussSum (levelDualGram Q N) (-c₀) a 0`. -/
@[kb "iwaniec1997" "§10.4, reciprocity of Gauss sums [unverified]"]
def gaussSumDualF (Q : QuadForm (𝓞 F) n) (t a : 𝓞 F) : ℂ :=
  ∑ᶠ r : Fin n → 𝓞 F ⧸ Ideal.span {a}, cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
    (algebraMap (𝓞 F) F t * qDual Q (vecO (fun i => qlift (r i))) / algebraMap (𝓞 F) F a) : ℚ) : ℂ))

lemma norm_cexp_rat (q : ℚ) : ‖cexp (2 * Real.pi * Complex.I * (q : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma cusp_inv_identity (α γ u : ℂ) (hα : α ≠ 0) (hγ : γ ≠ 0) (hu : u ≠ 0) (h1 : α * γ * u - 1 ≠ 0) :
    α / γ - (γ ^ 2 * u)⁻¹ = -(-γ / α - (α ^ 2 * (u - (α * γ)⁻¹))⁻¹)⁻¹ := by
  have e1 : α ^ 2 * (u - (α * γ)⁻¹) = α * (α * γ * u - 1) / γ := by field_simp
  have e2 : -γ / α - (α * (α * γ * u - 1) / γ)⁻¹ = -(γ ^ 2 * u / (α * γ * u - 1)) := by
    rw [inv_div, div_sub_div _ _ hα (mul_ne_zero hα h1), neg_div',
      div_eq_div_iff (mul_ne_zero hα (mul_ne_zero hα h1)) h1]
    ring
  rw [e1, e2, inv_neg, neg_neg, inv_div]
  field_simp
lemma cusp_prod_identity (α γ u : ℂ) (hα : α ≠ 0) (hγ : γ ≠ 0) (hu : u ≠ 0) (h1 : α * γ * u - 1 ≠ 0) :
    (-Complex.I * (-γ / α - (α ^ 2 * (u - (α * γ)⁻¹))⁻¹) / 2) * (-Complex.I * (u - (α * γ)⁻¹) / 2) =
      (-Complex.I * u / 2) * (Complex.I * γ / (2 * α)) := by
  have e1 : α ^ 2 * (u - (α * γ)⁻¹) = α * (α * γ * u - 1) / γ := by field_simp
  have e2 : -γ / α - (α * (α * γ * u - 1) / γ)⁻¹ = -(γ ^ 2 * u / (α * γ * u - 1)) := by
    rw [inv_div, div_sub_div _ _ hα (mul_ne_zero hα h1), neg_div',
      div_eq_div_iff (mul_ne_zero hα (mul_ne_zero hα h1)) h1]
    ring
  have e3 : u - (α * γ)⁻¹ = (α * γ * u - 1) / (α * γ) := by field_simp
  rw [e1, e2, e3]
  have e4 : γ ^ 2 * u / (α * γ * u - 1) * ((α * γ * u - 1) / (α * γ)) = γ * u / α := by
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero h1 (mul_ne_zero hα hγ))]
    field_simp
  calc _ = -(Complex.I ^ 2) * (γ ^ 2 * u / (α * γ * u - 1) * ((α * γ * u - 1) / (α * γ))) / 4 := by ring
    _ = _ := by rw [e4]; ring

lemma discr_pos_of_isTotallyReal : 0 < NumberField.discr F := by
  have h := NumberField.sign_discr (K := F)
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero] at h
  exact Int.sign_eq_one_iff_pos.mp h

/-- **Reciprocity of the theta multiplier, with the constant.** For $c \in \mathfrak N$ (a level), $c \ne 0$, $a \ne 0$ prime to
$\mathfrak d$:
$$G(a, 0, c) = P^\#\prod_v\Big(\frac{i\varphi_v(c)}{2\varphi_v(a)}\Big)^kG^\#(-c, a),\qquad
  P^\# = \Big(\prod_v\sqrt{\det\varphi_v(\tfrac14A^{-1})}\Big)^{-1}\Delta(\mathfrak d^{-1})^{-n}.$$ -/
theorem gaussSumF_reciprocity {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {a c : 𝓞 F} (ha0 : a ≠ 0)
    (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) (hc0 : c ≠ 0) (hc : c ∈ 𝔑) :
    gaussSumF Q a c 0 =
      (((∏ v, Real.sqrt (((1 / 4 : F) • (gramF Q)⁻¹).map (realEmb F v)).det)⁻¹ *
          (∏ i : Fin n, embDet (invDiffIdeals (F := F) i))⁻¹ : ℝ) : ℂ) *
        (∏ v, (Complex.I * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) /
          (2 * (realEmb F v (algebraMap (𝓞 F) F a) : ℂ))) ^ k) * gaussSumDualF Q (-c) a := by
  have : Finite (𝓞 F ⧸ Ideal.span {a}) := finite_quot_span ha0
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {a})
  have : Finite (𝓞 F ⧸ Ideal.span {c}) := finite_quot_span hc0
  letI := Fintype.ofFinite (𝓞 F ⧸ Ideal.span {c})
  have hav : ∀ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ) ≠ 0 := realEmb_algebraMap_ne_zero ha0
  have hcv : ∀ v, (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) ≠ 0 := realEmb_algebraMap_ne_zero hc0
  have hnk : ((n : ℂ) / 2) = ((k : ℕ) : ℂ) := by rw [hn]; push_cast; ring
  set P1 : ℂ := (((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
    (∏ i : Fin n, embDet (oneIdeals (F := F) i))⁻¹ : ℝ) : ℂ) with hP1
  set P2 : ℂ := (((∏ v, Real.sqrt (((1 / 4 : F) • (gramF Q)⁻¹).map (realEmb F v)).det)⁻¹ *
    (∏ i : Fin n, embDet (invDiffIdeals (F := F) i))⁻¹ : ℝ) : ℂ) with hP2
  have hP1ne : P1 ≠ 0 := by
    rw [hP1, ofReal_ne_zero]
    refine mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => ?_))
      (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_))
    · exact (Real.sqrt_pos.mpr (hQ v).det_pos).ne'
    · rw [embDet_one]
      exact (Real.sqrt_pos.mpr (by exact_mod_cast (discr_pos_of_isTotallyReal (F := F)))).ne'
  set u : ℝ → InfinitePlace F → ℂ := fun t _ => Complex.I * t with hu_def
  set u' : ℝ → InfinitePlace F → ℂ := fun t v => Complex.I * t -
    ((realEmb F v (algebraMap (𝓞 F) F a) : ℂ) * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ))⁻¹
    with hu'_def
  have huim : ∀ t v, (u t v).im = t := fun t v => by simp [hu_def]
  have hu'im : ∀ t v, (u' t v).im = t := fun t v => by
    simp only [hu'_def, sub_im, mul_im, I_re, ofReal_im, mul_zero, I_im, ofReal_re, one_mul,
      zero_add]
    rw [← ofReal_mul, ← ofReal_inv, ofReal_im, sub_zero]
  set G2 : dualSet (invDiffIdeals (F := F) (n := n)) → ℂ := fun l =>
    ∑ r : Fin n → 𝓞 F ⧸ Ideal.span {a}, cexp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F
      (-algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a * qDual Q (vecO (fun i => qlift (r i))) +
        ∑ i, (l : Fin n → F) i * ((algebraMap (𝓞 F) F a)⁻¹ * vecO (fun i => qlift (r i)) i)) :
          ℚ) : ℂ)) with hG2
  set S1 : ℝ → ℂ := fun t => ∑' μ : dualSet (oneIdeals (F := F) (n := n)),
    thetaTerm ((1 / 4 : F) • (gramF Q)⁻¹) μ (u t) * gaussSumF Q a c μ with hS1
  set S2 : ℝ → ℂ := fun t => ∑' l : dualSet (invDiffIdeals (F := F) (n := n)),
    thetaTerm (gramF Q) l (u' t) * G2 l with hS2
  set K : ℂ := P2 * ∏ v, (Complex.I * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) /
    (2 * (realEmb F v (algebraMap (𝓞 F) F a) : ℂ))) ^ k with hK
  -- the identity for every `t > 0`
  have key : ∀ t : ℝ, 0 < t → S1 t = K * S2 t := by
    intro t ht
    have hu : ∀ v, 0 < (u t v).im := fun v => by rw [huim t v]; exact ht
    have hu' : ∀ v, 0 < (u' t v).im := fun v => by rw [hu'im t v]; exact ht
    have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h => ha0 (FaithfulSMul.algebraMap_injective (𝓞 F) F
      (by rw [map_zero]; exact h))
    set τ := cuspPt (-algebraMap (𝓞 F) F c) (algebraMap (𝓞 F) F a) (u' t) with hτ_def
    have hτ : ∀ v, 0 < (τ v).im := cuspPt_im_pos _ haF hu'
    have hut0 : ∀ v, u t v ≠ 0 := fun v h => by have := hu v; rw [h] at this; simp at this
    have h1 : ∀ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ) * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) *
        u t v - 1 ≠ 0 := by
      intro v h
      have hre : (realEmb F v (algebraMap (𝓞 F) F a) : ℂ) * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) *
          u t v - 1 = (((realEmb F v (algebraMap (𝓞 F) F a)) *
            (realEmb F v (algebraMap (𝓞 F) F c)) * t : ℝ) : ℂ) * Complex.I - 1 := by
        simp only [hu_def]; push_cast; ring
      rw [hre] at h
      have him := congrArg Complex.im h
      simp only [sub_im, mul_im, ofReal_re, ofReal_im, Complex.I_re, Complex.I_im, mul_one,
        zero_mul, add_zero, Complex.one_im, sub_zero, Complex.zero_im] at him
      have ha' : realEmb F v (algebraMap (𝓞 F) F a) ≠ 0 := by exact_mod_cast hav v
      have hc' : realEmb F v (algebraMap (𝓞 F) F c) ≠ 0 := by exact_mod_cast hcv v
      exact mul_ne_zero (mul_ne_zero ha' hc') ht.ne' him
    have hz : cuspPt (algebraMap (𝓞 F) F a) (algebraMap (𝓞 F) F c) (u t) = fun v => -(τ v)⁻¹ := by
      funext v
      simp only [cuspPt, hτ_def, hu'_def, map_div₀, map_neg, ofReal_div, ofReal_neg]
      exact cusp_inv_identity _ _ _ (hav v) (hcv v) (hut0 v) (h1 v)
    have E1 := thetaLat_one_cuspPt hQ a hc0 hu
    have E2 := thetaLat_inversion hQ oneIdeals hτ
    have E3 := thetaLatDual_cuspPt hQ hlev ha0 ha hc hu'
    rw [hz, E2, E3] at E1
    simp only [hnk, cpow_natCast] at E1
    have hprod : (∏ v, (-Complex.I * τ v / 2) ^ k) * (∏ v, (-Complex.I * u' t v / 2) ^ k) =
        (∏ v, (-Complex.I * u t v / 2) ^ k) * ∏ v, (Complex.I *
          (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) / (2 * (realEmb F v (algebraMap (𝓞 F) F a) : ℂ))) ^ k := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← mul_pow, ← mul_pow]
      congr 1
      simp only [hτ_def, cuspPt, hu'_def, map_div₀, map_neg, ofReal_div, ofReal_neg]
      exact cusp_prod_identity _ _ _ (hav v) (hcv v) (hut0 v) (h1 v)
    have hA0 : P1 * ∏ v, (-Complex.I * u t v / 2) ^ k ≠ 0 :=
      mul_ne_zero hP1ne (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _
        (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (hut0 v)) two_ne_zero))
    apply mul_left_cancel₀ hA0
    rw [hS1, hS2, hK]
    simp only
    rw [← hP1] at E1
    rw [← E1, ← hP2]
    linear_combination (P1 * P2 * ∑' l : dualSet (invDiffIdeals (F := F) (n := n)),
      thetaTerm (gramF Q) l (u' t) * G2 l) * hprod
  -- bounds for the Gauss sums
  have hbd : ∀ {R : Type} [Fintype R] (f : R → ℚ),
      ‖∑ r, cexp (2 * Real.pi * Complex.I * ((f r : ℚ) : ℂ))‖ ≤ Fintype.card R := by
    intro R _ f
    refine (norm_sum_le _ _).trans ?_
    simp [norm_cexp_rat]
  have hg1 : ∀ μ : dualSet (oneIdeals (F := F) (n := n)),
      ‖gaussSumF Q a c μ‖ ≤ Fintype.card (Fin n → 𝓞 F ⧸ Ideal.span {c}) := by
    intro μ
    rw [gaussSumF_eq_sum]
    exact hbd _
  have hg2 : ∀ l, ‖G2 l‖ ≤ Fintype.card (Fin n → 𝓞 F ⧸ Ideal.span {a}) := fun l => hbd _
  have h01 : (0 : Fin n → F) ∈ dualSet (oneIdeals (F := F) (n := n)) :=
    mem_dualSet_one.mpr fun _ => Submodule.zero_mem _
  have h02 : (0 : Fin n → F) ∈ dualSet (invDiffIdeals (F := F) (n := n)) := by
    rw [dualSet_invDiff, mem_latSet_one]; exact fun _ => Submodule.zero_mem _
  have hsum1 := summable_norm_thetaTerm_dualSet hQ (oneIdeals (F := F) (n := n))
    (z := fun _ => Complex.I) (fun _ => by simp)
  have hsum2 := summable_norm_thetaTerm_dualSet (isTotPosGram_dual hQ) (invDiffIdeals (F := F) (n := n))
    (z := fun _ => Complex.I) (fun _ => by simp)
  rw [dual_dual_gram hQ] at hsum2
  have lim1 := tendsto_tsum_thetaTerm (isTotPosGram_dual hQ) h01 hsum1 (fun μ => gaussSumF Q a c μ) hg1
    u huim
  have lim2 := tendsto_tsum_thetaTerm hQ h02 hsum2 G2 hg2 u' hu'im
  have hlim2 : Tendsto S1 atTop (𝓝 (K * G2 ⟨0, h02⟩)) := by
    refine (lim2.const_mul K).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (key t ht).symm
  have huniq := tendsto_nhds_unique lim1 hlim2
  simp only at huniq
  rw [huniq, hK]
  congr 1
  rw [gaussSumDualF, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 4
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, map_neg]
  ring

/-- **The reciprocity constant** $U_Q = \frac{1}{\sqrt{N(\det A)}\,d_F^{n/2}}\cdot\frac{1}{\sqrt{N(\det\frac14A^{-1})}\,\Delta(\mathfrak d^{-1})^n}
\cdot 4^{-kd}$; it equals $1$ (`thetaRecConst_eq_one`). -/
def thetaRecConst (Q : QuadForm (𝓞 F) n) (k : ℕ) : ℝ :=
  ((∏ v, Real.sqrt ((gramF Q).map (realEmb F v)).det)⁻¹ *
      (Real.sqrt (NumberField.discr F : ℝ) ^ n)⁻¹) *
    ((∏ v, Real.sqrt (((1 / 4 : F) • (gramF Q)⁻¹).map (realEmb F v)).det)⁻¹ *
      (∏ i : Fin n, embDet (invDiffIdeals (F := F) i))⁻¹) *
    ∏ _v : InfinitePlace F, ((1 / 4 : ℝ) ^ k)

/-- Reciprocity with the constant: $M_Q(a, c) = U_Q\,N(a)^{-k}\,G^\#(-c, a)$. -/
theorem thetaMultF_eq_thetaRecConst {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {a c : 𝓞 F} (ha0 : a ≠ 0)
    (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) (hc0 : c ≠ 0) (hc : c ∈ 𝔑) :
    thetaMultF Q k a c = (thetaRecConst Q k : ℂ) *
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ k)⁻¹ * gaussSumDualF Q (-c) a := by
  have hav : ∀ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ) ≠ 0 := realEmb_algebraMap_ne_zero ha0
  have hcv : ∀ v, (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) ≠ 0 := realEmb_algebraMap_ne_zero hc0
  rw [thetaMultF, gaussSumF_reciprocity hQ hn hlev ha0 ha hc0 hc, thetaRecConst]
  have h : (∏ v, (-Complex.I / (2 * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ))) ^ k) *
      (∏ v, (Complex.I * (realEmb F v (algebraMap (𝓞 F) F c) : ℂ) /
        (2 * (realEmb F v (algebraMap (𝓞 F) F a) : ℂ))) ^ k) =
      (∏ _v : InfinitePlace F, (((1 / 4 : ℝ) ^ k : ℝ) : ℂ)) *
        ((∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ k)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← mul_pow, ← inv_pow]
    push_cast
    rw [← mul_pow]
    congr 1
    have := hav v; have := hcv v
    field_simp
    rw [Complex.I_sq]
    ring
  have e : ∀ (A B C D G : ℂ), A * C * (B * D * G) = A * B * (C * D) * G := by intros; ring
  rw [e, h]
  push_cast
  ring

/-- $G^\#(t, 1) = 1$ for $t \in \mathfrak N$ (the sum has one term, and $tQ^\#(x) \in \mathfrak d^{-1}$). -/
lemma gaussSumDualF_one {Q : QuadForm (𝓞 F) n} {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑)
    {t : 𝓞 F} (ht : t ∈ 𝔑) : gaussSumDualF Q t 1 = 1 := by
  have hsub : Subsingleton (𝓞 F ⧸ Ideal.span {(1 : 𝓞 F)}) := by
    rw [Ideal.span_singleton_one]; infer_instance
  have : Unique (Fin n → 𝓞 F ⧸ Ideal.span {(1 : 𝓞 F)}) :=
    { default := 0, uniq := fun _ => Subsingleton.elim _ _ }
  rw [gaussSumDualF, finsum_unique, map_one, div_one]
  exact cexp_trace_eq_one (hlev t ht _ fun i => algebraMap_mem_invDifferent _)

/-- The lower unipotent $L(c) = \begin{pmatrix}1&0\\c&1\end{pmatrix}$. -/
def lowerU (c : 𝓞 F) : SL(2, 𝓞 F) := ⟨!![1, 0; c, 1], by simp [det_fin_two_of]⟩

lemma lowerU_mul (c c' : 𝓞 F) : lowerU c * lowerU c' = lowerU (c + c') := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [lowerU, Matrix.mul_apply, Fin.sum_univ_two]

lemma thetaMultG_ne_zero {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) {γ : SL(2, 𝓞 F)}
    (hγ : γ ∈ Gamma0R 𝔑) : thetaMultG Q k γ ≠ 0 := by
  intro h
  have h1 := thetaMultG_mul hQ hn hlev hγ (Subgroup.inv_mem _ hγ)
  rw [mul_inv_cancel, h, zero_mul] at h1
  have h2 : thetaMultG Q k 1 = 1 := by simp [thetaMultG]
  rw [h2] at h1
  exact one_ne_zero h1

/-- **The reciprocity constant is $1$**: $m_Q(L(c))^2 = m_Q(L(2c))$ and $m_Q(L(c)) = U_Q$ for every $c \in \mathfrak N \setminus 0$. -/
theorem thetaRecConst_eq_one {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) :
    thetaRecConst Q k = 1 := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔑
  have h1 : Ideal.span {(1 : 𝓞 F)} ⊔ differentIdeal ℤ (𝓞 F) = ⊤ := by
    rw [Ideal.span_singleton_one, top_sup_eq]
  have hL : ∀ c' : 𝓞 F, c' ∈ 𝔑 → c' ≠ 0 → thetaMultG Q k (lowerU c') = thetaRecConst Q k := by
    intro c' hc' hc'0
    have hl : (lowerU c') 1 0 = c' := rfl
    simp only [thetaMultG, hl, hc'0, ↓reduceIte]
    rw [show (lowerU c') 0 0 = 1 from rfl, thetaMultF_eq_thetaRecConst hQ hn hlev one_ne_zero h1 hc'0 hc',
      gaussSumDualF_one hlev (𝔑.neg_mem hc')]
    simp
  have hmem : ∀ c' : 𝓞 F, c' ∈ 𝔑 → lowerU c' ∈ Gamma0R 𝔑 := fun c' hc' => hc'
  have h2 : (2 : 𝓞 F) * c ≠ 0 := mul_ne_zero two_ne_zero hc0
  have hmul := thetaMultG_mul hQ hn hlev (hmem c hc) (hmem c hc)
  rw [lowerU_mul, ← two_mul, hL _ (𝔑.mul_mem_left 2 hc) h2, hL c hc hc0] at hmul
  have hne : (thetaRecConst Q k : ℂ) ≠ 0 := by
    rw [← hL c hc hc0]; exact thetaMultG_ne_zero hQ hn hlev (hmem c hc)
  have : (thetaRecConst Q k : ℂ) = 1 := by
    have := mul_left_cancel₀ hne (hmul.symm.trans (mul_one _).symm)
    exact this
  exact_mod_cast this

/-- **Reciprocity of the theta multiplier.** For $Q$ totally positive definite of rank $n = 2k$ over $\mathcal{O}_F$, $\mathfrak N \ne 0$
a level, $c \in \mathfrak N$, $c \ne 0$, and $a \ne 0$ prime to the different $\mathfrak d$:
$$M_Q(a, c) = N(a)^{-k}\,G^\#(-c, a),\qquad G^\#(t, a) = \sum_{r\in(\mathcal{O}_F/a)^n}e\Big(\operatorname{Tr}\frac{t\,Q^\#(r)}{a}\Big),$$
$N(a)^k = \prod_v\varphi_v(a)^k$. For $F = \mathbb{Q}$ this is `QuadFormsKB.Siegel.thetaMult_reciprocity`. -/
@[kb "hecke1923" "§§54–58, reciprocity of Gauss sums in number fields [unverified]"]
theorem thetaMultF_reciprocity {Q : QuadForm (𝓞 F) n} (hQ : IsTotPosGram (gramF Q)) {k : ℕ}
    (hn : n = 2 * k) {𝔑 : Ideal (𝓞 F)} (hlev : IsThetaLevelF Q 𝔑) (h𝔑 : 𝔑 ≠ ⊥) {a c : 𝓞 F}
    (ha0 : a ≠ 0) (ha : Ideal.span {a} ⊔ differentIdeal ℤ (𝓞 F) = ⊤) (hc0 : c ≠ 0) (hc : c ∈ 𝔑) :
    thetaMultF Q k a c =
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F a) : ℂ)) ^ k)⁻¹ * gaussSumDualF Q (-c) a := by
  rw [thetaMultF_eq_thetaRecConst hQ hn hlev ha0 ha hc0 hc, thetaRecConst_eq_one hQ hn hlev h𝔑]
  push_cast
  ring

end

end QuadFormsKB.HilbertModular
