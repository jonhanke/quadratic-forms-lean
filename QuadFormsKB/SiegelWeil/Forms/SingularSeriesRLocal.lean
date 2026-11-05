/-
# Local Whittaker integrals as finite sums over cosets (for the singular series)

**Setting.** $F_v$ a non-archimedean local field of a number field, $r \ge 0$, $\operatorname{Sym}_r(F_v)$ with coordinates
$u_{ij}$, $i \le j$ (`SymIdx r`) and the product of self-dual measures (`muSym`).

**Results.**
* `integral_ballSym_mul_periodic`: if $\rho_i$ ($i \in \iota$) are representatives of $\mathfrak p_v^{-k}/\mathcal O_v$ (every
  $x \in \mathfrak p_v^{-k}$ lies in exactly one $\rho_i + \mathcal O_v$) and $g$ on $F_v^{R}$ is invariant under translation by
  $\mathcal O_v^R$, then
  $$\int_{\mathfrak p_v^{-k}\text{-box}}g\,du = \operatorname{vol}(\mathcal O_v)^R\sum_{i\in\iota^R}g\big((\rho_{i_p})_p\big).$$
* `wgR_add_int`: the integrand $u \mapsto f_v(w\,n(\operatorname{symOf}u))\,\psi_v(-\operatorname{tr}(T_GB))$ of the local Whittaker integral
  is invariant under $u \mapsto u + y$ with $y \in \mathcal O_v^R$, when $a_i \in \mathcal O_v$ and $T$ has coefficients in
  $\mathcal O_v$.
* `whittakerTrR_eq_sum`: consequently
  $$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB
    = \operatorname{vol}(\mathcal O_v)^R\sum_{i\in\iota^R}f_v\big(w\,n(B_i)\big)\psi_v(-\operatorname{tr}(T_GB_i)),$$
  $B_i = \operatorname{symOf}((\rho_{i_p})_p)$, a finite sum over the cosets of $\operatorname{Sym}_r(\mathfrak p_v^{-k})/\operatorname{Sym}_r(\mathcal O_v)$.
-/
import QuadFormsKB.SiegelWeil.Forms.EisensteinUnfoldCoord

open MeasureTheory Matrix IsDedekindDomain NumberField WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData QuadFormsKB.WeilRep.Genus

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {m r : ℕ}

local notation "Fv" => v.adicCompletion F

/-- The truncation $\mathbf 1_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}$ is the indicator of $\{u : |u_p|_v \le q^{k}\ \forall p\}$
(in the valuation normalization $v(u_p) \le \exp k$). -/
lemma ballSym_eq_indicator (k : ℕ) (u : SymIdx r → Fv) :
    ballSym v k u = {u : SymIdx r → Fv | ∀ p, Valued.v (u p) ≤ exp (k : ℤ)}.indicator 1 u := by
  classical
  unfold ballSym
  simp only [ballIndV_eq_ite, neg_neg]
  rw [Finset.prod_ite_zero, Finset.prod_const_one, Set.indicator_apply]
  simp

/-- **Generic coset sum.** Let $\rho_i$ ($i \in \iota$) be representatives of $\mathfrak p_v^{-k}/\mathcal O_v$ and $g$ a function on
$F_v^{R}$ invariant under translation by $\mathcal O_v^{R}$ ($R = |\mathrm{SymIdx}\ r|$). Then
$$\int \mathbf 1_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}\,g\,d\mu = \operatorname{vol}(\mathcal O_v)^R\sum_{i\in\iota^R}g\big((\rho_{i_p})_p\big).$$
No continuity of $g$ is needed. -/
theorem integral_ballSym_mul_periodic {k : ℕ} {ι : Type*} [Fintype ι] (ρ : ι → Fv)
    (hρ : ∀ x : Fv, Valued.v x ≤ exp (k : ℤ) → ∃! i, Valued.v (x - ρ i) ≤ 1)
    (hρk : ∀ i, Valued.v (ρ i) ≤ exp (k : ℤ))
    (g : (SymIdx r → Fv) → ℂ)
    (hg : ∀ x y : SymIdx r → Fv, (∀ p, Valued.v (y p) ≤ 1) → g (x + y) = g x) :
    ∫ u, ballSym v k u * g u ∂muSym v r =
      (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) ^ Fintype.card (SymIdx r) *
        ∑ i : SymIdx r → ι, g (fun p => ρ (i p)) := by
  classical
  have : SigmaFinite (selfDualV v) := (isOps_V v).sigmaFinite
  obtain ⟨S, hS⟩ : ∃ S : Set (SymIdx r → Fv), S = {u | ∀ p, Valued.v (u p) ≤ exp (k : ℤ)} := ⟨_, rfl⟩
  obtain ⟨Box, hBox⟩ : ∃ Box : (SymIdx r → ι) → Set (SymIdx r → Fv),
      ∀ i, Box i = Set.univ.pi fun p => {z : Fv | Valued.v (z - ρ (i p)) ≤ 1} := ⟨_, fun _ => rfl⟩
  have hcoset : ∀ c : Fv, {z : Fv | Valued.v (z - c) ≤ 1} = (fun z => z + -c) ⁻¹' (latticeV v 0 : Set Fv) := by
    intro c; ext z; simp [mem_latticeV, sub_eq_add_neg]
  have hmeasBox : ∀ i, MeasurableSet (Box i) := fun i => by
    rw [hBox]
    refine MeasurableSet.univ_pi fun p => ?_
    rw [hcoset]
    exact (measurableSet_latticeV v 0).preimage (measurable_add_const _)
  have hvolBox : ∀ i, muSym v r (Box i) = (selfDualV v (latticeV v 0)) ^ Fintype.card (SymIdx r) := by
    intro i
    rw [hBox, muSym, Measure.pi_pi]
    have : ∀ p : SymIdx r, selfDualV v {z : Fv | Valued.v (z - ρ (i p)) ≤ 1} = selfDualV v (latticeV v 0) := by
      intro p
      rw [hcoset]
      exact measure_preimage_add_right (selfDualV v) _ _
    simp only [this, Finset.prod_const, Finset.card_univ]
  have hfin : (selfDualV v (latticeV v 0)) ≠ ⊤ := (isCompact_latticeV v 0).measure_lt_top.ne
  have hSunion : S = ⋃ i ∈ (Finset.univ : Finset (SymIdx r → ι)), Box i := by
    ext u
    simp only [hS, hBox, Set.mem_ofPred_eq, Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro hu
      choose i hi using fun p => (hρ (u p) (hu p)).exists
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩ p
      calc Valued.v (u p) = Valued.v ((u p - ρ (i p)) + ρ (i p)) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ exp (k : ℤ) := max_le ((hi p).trans (by rw [← exp_zero, exp_le_exp]; omega)) (hρk _)
  have hdisj : Set.Pairwise (↑(Finset.univ : Finset (SymIdx r → ι))) (Function.onFun Disjoint Box) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro u hi hj
    rw [hBox] at hi hj
    apply hij
    funext p
    have hu : Valued.v (u p) ≤ exp (k : ℤ) := by
      have hp : Valued.v (u p - ρ (i p)) ≤ 1 := hi p (Set.mem_univ _)
      calc Valued.v (u p) = Valued.v ((u p - ρ (i p)) + ρ (i p)) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ exp (k : ℤ) := max_le (hp.trans (by rw [← exp_zero, exp_le_exp]; omega)) (hρk _)
    exact (hρ (u p) hu).unique (hi p (Set.mem_univ _)) (hj p (Set.mem_univ _))
  have hSmeas : MeasurableSet S := by
    rw [hSunion]
    exact Finset.measurableSet_biUnion _ fun i _ => hmeasBox i
  have hconst : ∀ i, ∀ u ∈ Box i, g u = g (fun p => ρ (i p)) := by
    intro i u hu
    rw [hBox] at hu
    have := hg (fun p => ρ (i p)) (u - fun p => ρ (i p)) (fun p => by
      simpa using hu p (Set.mem_univ _))
    simpa using this
  have hvolfin : ∀ i, muSym v r (Box i) ≠ ⊤ := fun i => by
    rw [hvolBox]; exact ENNReal.pow_ne_top hfin
  have hint : ∀ i ∈ (Finset.univ : Finset (SymIdx r → ι)), IntegrableOn g (Box i) (muSym v r) := by
    intro i _
    have h1 : IntegrableOn (fun _ => g (fun p => ρ (i p))) (Box i) (muSym v r) :=
      integrableOn_const (hvolfin i)
    exact h1.congr_fun (fun u hu => (hconst i u hu).symm) (hmeasBox i)
  calc ∫ u, ballSym v k u * g u ∂muSym v r = ∫ u, S.indicator g u ∂muSym v r := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [ballSym_eq_indicator, hS]
        by_cases h : u ∈ {u : SymIdx r → Fv | ∀ p, Valued.v (u p) ≤ exp (k : ℤ)}
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; simp
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
    _ = ∫ u in S, g u ∂muSym v r := integral_indicator hSmeas
    _ = ∑ i : SymIdx r → ι, ∫ u in Box i, g u ∂muSym v r := by
        rw [hSunion]
        exact integral_biUnion_finset _ (fun i _ => hmeasBox i) hdisj hint
    _ = ∑ i : SymIdx r → ι, (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) ^ Fintype.card (SymIdx r) *
          g (fun p => ρ (i p)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [setIntegral_congr_fun (hmeasBox i) (fun u hu => hconst i u hu), setIntegral_const,
          Measure.real, hvolBox, ENNReal.toReal_pow, Complex.real_smul]
        simp [Measure.real]
    _ = _ := by rw [← Finset.mul_sum]

/-! ### Periodicity of the integrand -/

lemma pairT_add (T : QuadForm Fv r) (x y : SymIdx r → Fv) : pairT v T (x + y) = pairT v T x + pairT v T y := by
  simp only [pairT, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma valued_pairT_le_one (T : QuadForm Fv r) (hT : ∀ i j, Valued.v (T.coeff i j) ≤ 1) (y : SymIdx r → Fv)
    (hy : ∀ p, Valued.v (y p) ≤ 1) : Valued.v (pairT v T y) ≤ 1 :=
  Valuation.map_sum_le _ fun p _ => by
    rw [map_mul]
    exact mul_le_one' (hy p) (hT _ _)

/-- **The integrand of the local Whittaker integral of degree $r$:**
$u \mapsto f_v(w\,n(\operatorname{symOf}u))\,\psi_v(-\operatorname{tr}(T_GB))$. -/
def wgR {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ) (T : QuadForm Fv r) (u : SymIdx r → Fv) : ℂ :=
  wfunR v a u * (psiV v (-pairT v T u) : ℂ)

/-- **Periodicity of the local integrand:** for $a_i \in \mathcal O_v$ and $T$ with coefficients in $\mathcal O_v$,
$\mathrm{wgR}(x + y) = \mathrm{wgR}(x)$ whenever all $y_p \in \mathcal O_v$. -/
theorem wgR_add_int (a : Fin (2 * m) → (v.adicCompletion F)ˣ) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1)
    (T : QuadForm Fv r) (hT : ∀ i j, Valued.v (T.coeff i j) ≤ 1) (x y : SymIdx r → Fv)
    (hy : ∀ p, Valued.v (y p) ≤ 1) : wgR v a T (x + y) = wgR v a T x := by
  have hyi : ∀ i j, Valued.v (symOf y i j) ≤ 1 := by
    intro i j
    simp only [symOf, of_apply]
    split_ifs
    · exact hy _
    · exact hy _
  have e : spN (symOf (x + y)) (symOf_transpose (x + y)) =
      spN (symOf x) (symOf_transpose x) * spN (symOf y) (symOf_transpose y) := by
    rw [← spN_add]
    congr 1
    exact symOf_add x y
  have hw : wfunR v a (x + y) = wfunR v a x := by
    unfold wfunR
    rw [e, ← mul_assoc]
    exact secRV_oneSG_mul_spN v a ha _ _ _ hyi
  have hψ : (psiV v (-pairT v T (x + y)) : ℂ) = (psiV v (-pairT v T x) : ℂ) := by
    rw [pairT_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    have : psiV v (-pairT v T y) = 1 :=
      psiV_eq_one_of_le_one v (by rw [Valuation.map_neg]; exact valued_pairT_le_one v T hT y hy)
    rw [this]; simp
  unfold wgR
  rw [hw, hψ]

/-- **The truncated local Whittaker integral as a finite coset sum:** for $\rho_i$ ($i\in\iota$) representatives of
$\mathfrak p_v^{-k}/\mathcal O_v$, $a_i \in \mathcal O_v$ and $T$ with coefficients in $\mathcal O_v$,
$$\int_{\mathrm{Sym}_r(\mathfrak p_v^{-k})}f_v(wn(B))\psi_v(-\operatorname{tr}(T_GB))\,dB =
\operatorname{vol}(\mathcal O_v)^R\sum_{i\in\iota^R}\mathrm{wgR}\big((\rho_{i_p})_p\big).$$ -/
theorem whittakerTrR_eq_sum (a : Fin (2 * m) → (v.adicCompletion F)ˣ) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1)
    (T : QuadForm Fv r) (hT : ∀ i j, Valued.v (T.coeff i j) ≤ 1) {k : ℕ} {ι : Type*} [Fintype ι] (ρ : ι → Fv)
    (hρ : ∀ x : Fv, Valued.v x ≤ exp (k : ℤ) → ∃! i, Valued.v (x - ρ i) ≤ 1)
    (hρk : ∀ i, Valued.v (ρ i) ≤ exp (k : ℤ)) :
    whittakerTrR v a T k =
      (((selfDualV v).real (latticeV v 0) : ℝ) : ℂ) ^ Fintype.card (SymIdx r) *
        ∑ i : SymIdx r → ι, wgR v a T (fun p => ρ (i p)) :=
  integral_ballSym_mul_periodic v ρ hρ hρk (wgR v a T) fun x y hy => wgR_add_int v a ha T hT x y hy

end QuadFormsKB.SiegelWeil.Forms
