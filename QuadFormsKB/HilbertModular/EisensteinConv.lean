/-
# Hilbert Eisenstein series II: absolute convergence for $k \ge 3$

For a weight $W$ that is unit-equivariant, bounded, and supported on $I \times I$ for a fractional ideal $I$ (`EisWeight`), and
$k \ge 3$, the series $E_{W,k}(z) = \sum_{U\backslash F^2}W(x)N(cz+d)^{-k}$ converges absolutely and locally uniformly on
$\mathbb{H}^d$ (`exists_summable_bound`).

**Proof (balancing by Dirichlet's unit theorem).** Put $a_v(x) = \max(|\sigma_v c|, |\sigma_v d|)$ for $x = (c, d)$. Then
1. $|\sigma_v(c)z_v + \sigma_v(d)| \ge r(z_v)\,a_v(x)$ with Mathlib's $r(z) > 0$ (`r_mul_max_le_real`), so
   $|N(cz+d)| \ge \prod_v r(z_v)\cdot\prod_v a_v(x)$; and $r$ is bounded below on vertical strips;
2. $a_v(\varepsilon x) = |\sigma_v\varepsilon|\,a_v(x)$ and $\prod_v|\sigma_v\varepsilon| = 1$. Because the log-embedding of $U$ is a full lattice in
   the trace-zero hyperplane (`unitLattice_span_eq_top`, through `IsZLattice`), every orbit contains a **balanced**
   representative $x$, i.e. $a_v(x)^d \le C\prod_wa_w(x)$ for all $v$, with $C$ depending only on $F$ (`exists_unit_balance`);
3. for balanced $x$: $\prod_va_v(x) \ge C^{-1}\|x\|^d$ with $\|x\| = \max_va_v(x)$ the sup norm of the real embedding
   $x \mapsto (\sigma(c), \sigma(d)) \in \mathbb{R}^{2d}$ (`eisEmb`), whose image of $I \times I$ is a lattice of rank $2d$;
4. so the term of an orbit is at most $B\,(\prod_v r(z_v))^{-k}C^k\|x\|^{-dk}$ at its balanced representative $x$, and
   $\sum_{x \in I^2\setminus0}\|x\|^{-dk} < \infty$ since $dk > 2d$ (Mathlib's `ZLattice.summable_norm_zpow`). Distinct orbits have
   distinct representatives, which gives a summable majorant on $U\backslash F^2$.

Sources: Freitag, *Hilbert Modular Forms* (1990), Ch. I §5 (Eisenstein series, convergence) [unverified]; Garrett (1990),
Ch. 3 [unverified]. The balancing argument is the standard one (Siegel); here it is made explicit through Mathlib's
`NumberField.Units.unitLattice`.
-/
import QuadFormsKB.HilbertModular.EisensteinBasic

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Balancing by units -/

lemma mult_eq_one_of_totallyReal (v : InfinitePlace F) : v.mult = 1 := by
  simp [InfinitePlace.mult, IsTotallyReal.isReal v]

open Classical in
variable (F) in
/-- **The unit lattice is cocompact**: there is $R$ such that every $t$ in the log space is within $R$ of the
log-embedding of some unit. -/
lemma exists_unit_logEmbedding_near :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : logSpace F, ∃ u : (𝓞 F)ˣ, ‖t - logEmbedding F (Additive.ofMul u)‖ ≤ R := by
  set b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun t => ?_⟩
  have hfl : (ZSpan.floor b t : logSpace F) ∈ unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice F) (basisUnitLattice F)]
    exact (ZSpan.floor b t).2
  obtain ⟨a, -, ha⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul a, ?_⟩
  have : logEmbedding F (Additive.ofMul (Additive.toMul a)) = ZSpan.floor b t := by
    simpa using ha
  rw [this, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b t

/-- The log-embedding of a unit at a place $w \ne w_0$ is $\log|\sigma_w(u)|$ (totally real: multiplicity $1$). -/
lemma logEmbedding_apply_tr (u : (𝓞 F)ˣ) (w : {w : InfinitePlace F // w ≠ w₀}) :
    logEmbedding F (Additive.ofMul u) w = Real.log (w.1 (u : F)) := by
  rw [logEmbedding_component, mult_eq_one_of_totallyReal]; simp

lemma sum_log_place_unit (u : (𝓞 F)ˣ) : ∑ v : InfinitePlace F, Real.log (v (u : F)) = 0 := by
  rw [← Real.log_prod (fun v _ => (Units.pos_at_place u v).ne'), prod_place_unit, Real.log_one]

variable (F) in
/-- **Balancing (Dirichlet).** There is $C > 0$ such that for every $a \in \mathbb{R}_{>0}^\iota$ some unit $\varepsilon$ makes
$a' = (|\sigma_v\varepsilon|a_v)_v$ balanced: $a'^d_v \le C\prod_wa'_w$ for every $v$ ($d = |\iota|$). -/
theorem exists_unit_balance : ∃ C : ℝ, 0 < C ∧ ∀ a : InfinitePlace F → ℝ, (∀ v, 0 < a v) →
    ∃ ε : (𝓞 F)ˣ, ∀ v, (v (ε : F) * a v) ^ Fintype.card (InfinitePlace F) ≤
      C * ∏ w, (w (ε : F) * a w) := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_unit_logEmbedding_near F
  set d := Fintype.card (InfinitePlace F) with hd
  have hdpos : 0 < d := Fintype.card_pos
  refine ⟨Real.exp ((d : ℝ) * ((d : ℝ) * R)), Real.exp_pos _, fun a ha => ?_⟩
  set m : ℝ := (∑ w, Real.log (a w)) / d with hm
  set t : logSpace F := fun w => Real.log (a w.1) - m
  obtain ⟨u, hu⟩ := hR t
  refine ⟨u⁻¹, fun v => ?_⟩
  -- the balanced logarithms `ℓ w = log (w ε * a w) - m`
  set ℓ : InfinitePlace F → ℝ := fun w => Real.log (w ((u⁻¹ : (𝓞 F)ˣ) : F) * a w) - m with hℓ
  have hpos : ∀ w : InfinitePlace F, 0 < w ((u⁻¹ : (𝓞 F)ˣ) : F) * a w :=
    fun w => mul_pos (Units.pos_at_place _ w) (ha w)
  have hlog_inv : ∀ w : InfinitePlace F, Real.log (w ((u⁻¹ : (𝓞 F)ˣ) : F)) = -Real.log (w (u : F)) := by
    intro w
    have : w ((u⁻¹ : (𝓞 F)ˣ) : F) = (w (u : F))⁻¹ := by
      rw [show ((u⁻¹ : (𝓞 F)ˣ) : F) = ((u : F))⁻¹ by simp, map_inv₀]
    rw [this, Real.log_inv]
  have hℓeq : ∀ w : InfinitePlace F, ℓ w = Real.log (a w) - m - Real.log (w (u : F)) := by
    intro w
    simp only [hℓ]
    rw [Real.log_mul (Units.pos_at_place _ w).ne' (ha w).ne', hlog_inv]; ring
  -- components off `w₀` are small
  have hsmall : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |ℓ w.1| ≤ R := by
    intro w
    have h1 : |(t - logEmbedding F (Additive.ofMul u)) w| ≤ R :=
      (norm_le_pi_norm (t - logEmbedding F (Additive.ofMul u)) w).trans hu
    rw [Pi.sub_apply, logEmbedding_apply_tr] at h1
    rw [hℓeq]; simpa [t] using h1
  -- the components sum to zero
  have hsum : ∑ w, ℓ w = 0 := by
    simp_rw [hℓeq]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_log_place_unit, Finset.sum_const,
      Finset.card_univ, ← hd, hm, nsmul_eq_mul]
    field_simp
    ring
  have hall : ∀ w, ℓ w ≤ d * R := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have h := hsum
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at h
      have hle : -∑ w : {w : InfinitePlace F // w ≠ w₀}, ℓ w.1 ≤
          ∑ w : {w : InfinitePlace F // w ≠ w₀}, R := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum fun w _ => (neg_le_abs _).trans (hsmall w)
      have hcard : ∑ w : {w : InfinitePlace F // w ≠ w₀}, R ≤ d * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hR0
        exact_mod_cast (Fintype.card_subtype_le _).trans (le_of_eq hd.symm)
      linarith
    · have := (le_abs_self _).trans (hsmall ⟨w, hw⟩)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
      nlinarith
  -- exponentiate
  have hprod : Real.log (∏ w, (w ((u⁻¹ : (𝓞 F)ˣ) : F) * a w)) = d * m := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    have : ∀ w : InfinitePlace F, Real.log (w ((u⁻¹ : (𝓞 F)ˣ) : F) * a w) = ℓ w + m := by
      intro w; simp only [hℓ]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, ← hd, nsmul_eq_mul]
    ring
  have hP : 0 < ∏ w, (w ((u⁻¹ : (𝓞 F)ˣ) : F) * a w) := Finset.prod_pos fun w _ => hpos w
  rw [← Real.exp_log (pow_pos (hpos v) d), ← Real.exp_log hP, ← Real.exp_add, Real.exp_le_exp,
    Real.log_pow, hprod]
  have hv : Real.log (v ((u⁻¹ : (𝓞 F)ˣ) : F) * a v) = ℓ v + m := by simp only [hℓ]; ring
  rw [hv]
  have := hall v
  have hd0 : (0 : ℝ) ≤ d := by positivity
  nlinarith

/-! ### The embedding of $F^2$ into $\mathbb{R}^{2d}$ -/

/-- **The real embedding of pairs**, $x = (c, d) \mapsto (\sigma(c), \sigma(d)) \in \mathbb{R}^\iota \times \mathbb{R}^\iota$ (sup norm). -/
noncomputable def eisEmb (x : F × F) : (InfinitePlace F → ℝ) × (InfinitePlace F → ℝ) :=
  (realVec x.1, realVec x.2)

/-- $a_v(x) = \max(|\sigma_v c|, |\sigma_v d|)$. -/
noncomputable def placeMax (x : F × F) (v : InfinitePlace F) : ℝ :=
  max |realEmb F v x.1| |realEmb F v x.2|

lemma placeMax_nonneg (x : F × F) (v : InfinitePlace F) : 0 ≤ placeMax x v :=
  le_max_of_le_left (abs_nonneg _)

lemma placeMax_pos {x : F × F} (hx : x ≠ 0) (v : InfinitePlace F) : 0 < placeMax x v := by
  rcases (placeMax_nonneg x v).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx
    have h1 : |realEmb F v x.1| = 0 := le_antisymm (h ▸ le_max_left _ _) (abs_nonneg _)
    have h2 : |realEmb F v x.2| = 0 := le_antisymm (h ▸ le_max_right _ _) (abs_nonneg _)
    rw [abs_eq_zero, map_eq_zero_iff _ (realEmb_injective F v)] at h1 h2
    exact Prod.ext h1 h2

lemma placeMax_smul (ε : (𝓞 F)ˣ) (x : F × F) (v : InfinitePlace F) :
    placeMax (ε • x) v = v (ε : F) * placeMax x v := by
  simp only [placeMax, smul_fst, smul_snd, map_mul, abs_mul, abs_realEmb]
  exact (mul_max_of_nonneg _ _ (apply_nonneg v _)).symm

lemma norm_eisEmb_le {x : F × F} {M : ℝ} (hM : ∀ v, placeMax x v ≤ M) (hM0 : 0 ≤ M) :
    ‖eisEmb x‖ ≤ M := by
  rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg hM0, pi_norm_le_iff_of_nonneg hM0]
  exact ⟨fun v => by simpa [eisEmb, realVec, Real.norm_eq_abs] using (le_max_left _ _).trans (hM v),
    fun v => by simpa [eisEmb, realVec, Real.norm_eq_abs] using (le_max_right _ _).trans (hM v)⟩

variable (F) in
/-- **Balanced representatives**: every $x \ne 0$ has a unit multiple $x' = \varepsilon x$ with
$\|x'\|^d \le C\prod_va_v(x')$. -/
theorem exists_balanced : ∃ C : ℝ, 0 < C ∧ ∀ x : F × F, x ≠ 0 → ∃ ε : (𝓞 F)ˣ,
    ‖eisEmb (ε • x)‖ ^ Fintype.card (InfinitePlace F) ≤ C * ∏ v, placeMax (ε • x) v := by
  obtain ⟨C, hC, hbal⟩ := exists_unit_balance F
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨ε, hε⟩ := hbal (placeMax x) (placeMax_pos hx)
  refine ⟨ε, ?_⟩
  obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image Finset.univ (placeMax (ε • x)) Finset.univ_nonempty
  have hn : ‖eisEmb (ε • x)‖ ≤ placeMax (ε • x) v₀ :=
    norm_eisEmb_le (fun v => hv₀ v (Finset.mem_univ v)) (placeMax_nonneg _ _)
  calc ‖eisEmb (ε • x)‖ ^ Fintype.card (InfinitePlace F)
      ≤ placeMax (ε • x) v₀ ^ Fintype.card (InfinitePlace F) := pow_le_pow_left₀ (norm_nonneg _) hn _
    _ ≤ C * ∏ v, placeMax (ε • x) v := by
        simp_rw [placeMax_smul]; exact hε v₀

/-! ### The lattice $I \times I$ in $\mathbb{R}^{2d}$ -/

/-- The basis of $\mathbb{R}^\iota \times \mathbb{R}^\iota$ made of the lattice bases of $I$ in both factors. -/
noncomputable def pairBasis (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Module.Basis (Fin (Module.finrank ℚ F) ⊕ Fin (Module.finrank ℚ F)) ℝ
      ((InfinitePlace F → ℝ) × (InfinitePlace F → ℝ)) :=
  (koecherBasis I).prod (koecherBasis I)

lemma realVec_mem_span (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {β : F}
    (hβ : β ∈ (I : FractionalIdeal (𝓞 F)⁰ F)) :
    realVec β ∈ Submodule.span ℤ (Set.range (koecherBasis I)) := by
  obtain ⟨m, rfl⟩ := latElt_surj I hβ
  rw [← koecherBasis_symm, Module.Basis.equivFun_symm_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [show ((m j : ℝ)) • koecherBasis I j = (m j : ℤ) • koecherBasis I j from
    Int.cast_smul_eq_zsmul ℝ (m j) _]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma eisEmb_mem_span (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {x : F × F}
    (hx : x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F)) :
    eisEmb x ∈ Submodule.span ℤ (Set.range (pairBasis I)) := by
  have h1 : ((realVec x.1, 0) : (InfinitePlace F → ℝ) × (InfinitePlace F → ℝ)) ∈
      Submodule.span ℤ (Set.range (pairBasis I)) := by
    have := Submodule.mem_map_of_mem (f := LinearMap.inl ℤ (InfinitePlace F → ℝ) (InfinitePlace F → ℝ))
      (realVec_mem_span I hx.1)
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inl j, by simp [pairBasis]⟩
  have h2 : ((0, realVec x.2) : (InfinitePlace F → ℝ) × (InfinitePlace F → ℝ)) ∈
      Submodule.span ℤ (Set.range (pairBasis I)) := by
    have := Submodule.mem_map_of_mem (f := LinearMap.inr ℤ (InfinitePlace F → ℝ) (InfinitePlace F → ℝ))
      (realVec_mem_span I hx.2)
    rw [Submodule.map_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inr j, by simp [pairBasis]⟩
  have := Submodule.add_mem _ h1 h2
  simpa [eisEmb] using this

lemma card_infinitePlace_eq_finrank : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  have h := (mixedEquiv (F := F)).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, NumberField.mixedEmbedding.finrank] at h
  exact h.symm

lemma finrank_span_pairBasis (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (pairBasis I))) =
      2 * Fintype.card (InfinitePlace F) := by
  rw [finrank_span_eq_card ((pairBasis I).linearIndependent.restrict_scalars' ℤ)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [← card_infinitePlace_eq_finrank]; ring

lemma realVec_injective : Function.Injective (realVec : F → InfinitePlace F → ℝ) := by
  intro a b h
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact realEmb_injective F v (congrFun h v)

lemma eisEmb_injective : Function.Injective (eisEmb : F × F → _) := by
  intro x y h
  simp only [eisEmb, Prod.mk.injEq] at h
  exact Prod.ext (realVec_injective h.1) (realVec_injective h.2)

open Classical in
/-- **Summability over $I \times I$**: $\sum_{x \in I^2}\|x\|^{-n} < \infty$ for $n > 2d$ (the term $x = 0$ is $0$). -/
theorem summable_eisEmb_zpow (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {n : ℤ}
    (hn : 2 * (Fintype.card (InfinitePlace F) : ℤ) < n) :
    Summable fun x : F × F =>
      if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then
        ‖eisEmb x‖ ^ (-n) else 0 := by
  classical
  set S := {x : F × F | x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}
  have heq : (fun x : F × F => if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧
      x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then ‖eisEmb x‖ ^ (-n) else 0) =
      S.indicator fun x => ‖eisEmb x‖ ^ (-n) := by
    funext x; simp [Set.indicator, S]
  rw [heq, ← summable_subtype_iff_indicator]
  set L := Submodule.span ℤ (Set.range (pairBasis I))
  have hL : Summable fun y : L => ‖y‖ ^ (-n) := by
    refine ZLattice.summable_norm_zpow L (-n) ?_
    rw [finrank_span_pairBasis]; push_cast; linarith
  have hi : Function.Injective fun x : S => (⟨eisEmb x.1, eisEmb_mem_span I x.2⟩ : L) := by
    intro x y h
    exact Subtype.ext (eisEmb_injective (congrArg Subtype.val h))
  exact (hL.comp_injective hi).congr fun x => rfl

/-! ### Lower bounds for $|cz + d|$ -/

/-- **$|cz + d| \ge r(z)\max(|c|, |d|)$ for real $c, d$** ($r$ = Mathlib's `EisensteinSeries.r`, positive on $\mathbb{H}$). -/
lemma r_mul_max_le_real (z : ℍ) (c d : ℝ) :
    EisensteinSeries.r z * max |c| |d| ≤ ‖(c : ℂ) * z + d‖ := by
  set M := max |c| |d| with hMdef
  rcases (le_max_of_le_left (abs_nonneg c) : 0 ≤ M).lt_or_eq with hM | hM
  · have hc : (c : ℂ) * z + d = (((c / M : ℝ) : ℂ) * z + ((d / M : ℝ) : ℂ)) * ((M : ℝ) : ℂ) := by
      have : ((M : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hM.ne'
      push_cast; field_simp
    rw [hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hM.le]
    refine mul_le_mul_of_nonneg_right ?_ hM.le
    have hsq : ∀ t : ℝ, |t| = M → 1 ≤ (t / M) ^ 2 := by
      intro t ht
      rw [div_pow, ← sq_abs t, ht, div_self (pow_ne_zero 2 hM.ne')]
    rcases max_choice |c| |d| with h | h
    · exact EisensteinSeries.auxbound1 z (d / M) (hsq c (by rw [hMdef, h]))
    · exact EisensteinSeries.auxbound2 z (c / M) (hsq d (by rw [hMdef, h]))
  · rw [show M = 0 from hM.symm, mul_zero]; exact norm_nonneg _

/-- $|N(cz + d)| \ge \prod_vr(z_v)\cdot\prod_va_v(x)$. -/
lemma norm_eisDen_ge (x : F × F) (z : InfinitePlace F → ℍ) :
    (∏ v, EisensteinSeries.r (z v)) * ∏ v, placeMax x v ≤ ‖eisDen x fun v => (z v : ℂ)‖ := by
  rw [eisDen, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (EisensteinSeries.r_pos _).le (placeMax_nonneg _ _))
    fun v _ => r_mul_max_le_real (z v) _ _

lemma eisDen_zero (Z : InfinitePlace F → ℂ) : eisDen (0 : F × F) Z = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

/-! ### Admissible weights and the summable majorant -/

/-- **An admissible weight of parallel weight $k$**: $W : F^2 \to \mathbb{C}$ with
* `unit`: unit equivariance $W(\varepsilon x) = N(\varepsilon)^kW(x)$;
* `supp`: $W$ vanishes off $I \times I$ for some fractional ideal $I$;
* `bdd`: $|W| \le B$ for some $B$.

Example: $W(c, d) = \chi(d)^{-1}$ for $(c, d) \in \mathfrak N \times \mathcal{O}$, $0$ otherwise (`EisensteinChar.lean`). -/
structure EisWeight (W : F × F → ℂ) (k : ℤ) : Prop where
  unit : IsUnitEquivariant W k
  supp : ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∀ x, W x ≠ 0 →
    x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F)
  bdd : ∃ B : ℝ, ∀ x, ‖W x‖ ≤ B

/-- **A summable majorant for $k \ge 3$, uniform on vertical strips**: for $B > 0$ there is a summable
$h : U\backslash F^2 \to \mathbb{R}$ with $|W(x_o)N(c_oz + d_o)^{-k}| \le h(o)$ whenever $|\operatorname{Re}z_v| \le A$ and
$\operatorname{Im}z_v \ge B$ for all $v$. -/
theorem exists_summable_bound {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) (hk : 3 ≤ k)
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ h : UOrbit F → ℝ, Summable h ∧ ∀ z : InfinitePlace F → ℍ,
      (∀ v, z v ∈ verticalStrip A B) → ∀ o, ‖eisTerm W k o.out fun v => (z v : ℂ)‖ ≤ h o := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hn : 3 ≤ n := by exact_mod_cast hk
  obtain ⟨C, hC, hbal⟩ := exists_balanced F
  choose! ε hε using hbal
  obtain ⟨I, hI⟩ := hW.supp
  obtain ⟨Bw, hBw⟩ := hW.bdd
  have hBw0 : 0 ≤ Bw := (norm_nonneg _).trans (hBw 0)
  set d := Fintype.card (InfinitePlace F) with hd
  have hdpos : 0 < d := Fintype.card_pos
  set r₀ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ with hr₀
  have hr₀pos : 0 < r₀ := EisensteinSeries.r_pos _
  set g : F × F → ℝ := fun x =>
    if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then
      ‖eisEmb x‖ ^ (-((d * n : ℕ) : ℤ)) else 0 with hg
  have hgs : Summable g := summable_eisEmb_zpow I (by push_cast; nlinarith)
  set rep : UOrbit F → F × F := fun o => ε o.out • o.out
  have hrep : ∀ o, (Quotient.mk _ (rep o) : UOrbit F) = o := by
    intro o
    exact (Quotient.sound (orbitRel_iff.mpr ⟨ε o.out, rfl⟩)).trans (Quotient.out_eq o)
  have hinj : Function.Injective rep := by
    intro o o' h; rw [← hrep o, ← hrep o', h]
  refine ⟨fun o => Bw * (C / r₀ ^ d) ^ n * g (rep o), (hgs.comp_injective hinj).mul_left _,
    fun z hz o => ?_⟩
  have hterm : eisTerm W (n : ℤ) o.out (fun v => (z v : ℂ)) =
      eisTerm W (n : ℤ) (rep o) (fun v => (z v : ℂ)) := (eisTerm_smul hW.unit _ _ _).symm
  rw [hterm]
  set x := rep o
  have hg0 : 0 ≤ g x := by
    simp only [hg]; split_ifs <;> positivity
  have hC0 : 0 ≤ (C / r₀ ^ d) ^ n := by positivity
  by_cases hWx : W x = 0
  · simp only [eisTerm, hWx, zero_mul, norm_zero]; positivity
  by_cases hx0 : x = 0
  · rw [eisTerm, hx0, eisDen_zero, _root_.zero_zpow _ (by omega),
      mul_zero, norm_zero]
    positivity
  have hxI := hI x hWx
  have hgx : g x = ‖eisEmb x‖ ^ (-((d * n : ℕ) : ℤ)) := by simp only [hg, hxI, and_self, ite_true]
  have hox : o.out ≠ 0 := by
    intro h; apply hx0; simp [x, rep, h]
  have hbx : ‖eisEmb x‖ ^ d ≤ C * ∏ v, placeMax x v := hε o.out hox
  have he0 : 0 < ‖eisEmb x‖ := norm_pos_iff.mpr fun h => hx0 (eisEmb_injective (h.trans (by ext v <;> simp [eisEmb, realVec])))
  have hP : 0 < ∏ v, placeMax x v := Finset.prod_pos fun v _ => placeMax_pos hx0 v
  have hrz : r₀ ^ d ≤ ∏ v, EisensteinSeries.r (z v) := by
    rw [show r₀ ^ d = ∏ _v : InfinitePlace F, r₀ by rw [Finset.prod_const, Finset.card_univ]]
    exact Finset.prod_le_prod₀ (fun _ _ => hr₀pos.le)
      fun v _ => EisensteinSeries.r_lower_bound_on_verticalStrip (z v) hB (hz v)
  have hlow : r₀ ^ d * (‖eisEmb x‖ ^ d / C) ≤ ‖eisDen x fun v => (z v : ℂ)‖ := by
    refine le_trans ?_ (norm_eisDen_ge x z)
    refine mul_le_mul hrz ?_ (by positivity) (Finset.prod_nonneg fun _ _ => (EisensteinSeries.r_pos _).le)
    rw [div_le_iff₀ hC]; linarith
  have hlow0 : 0 < r₀ ^ d * (‖eisEmb x‖ ^ d / C) := by positivity
  show ‖eisTerm W (n : ℤ) x fun v => (z v : ℂ)‖ ≤ Bw * (C / r₀ ^ d) ^ n * g x
  rw [eisTerm, norm_mul, _root_.zpow_neg, zpow_natCast, norm_inv, norm_pow, hgx, _root_.zpow_neg,
    zpow_natCast]
  have hkey : (‖eisDen x fun v => (z v : ℂ)‖ ^ n)⁻¹ ≤ ((r₀ ^ d * (‖eisEmb x‖ ^ d / C)) ^ n)⁻¹ :=
    inv_anti₀ (pow_pos hlow0 n) (pow_le_pow_left₀ hlow0.le hlow n)
  have heq : ((r₀ ^ d * (‖eisEmb x‖ ^ d / C)) ^ n)⁻¹ = (C / r₀ ^ d) ^ n * (‖eisEmb x‖ ^ (d * n))⁻¹ := by
    have hr : r₀ ^ d ≠ 0 := pow_ne_zero _ hr₀pos.ne'
    rw [mul_pow, div_pow, div_pow, ← pow_mul, ← pow_mul]
    field_simp
  rw [mul_assoc, ← heq]
  exact mul_le_mul (hBw x) hkey (by positivity) hBw0

end QuadFormsKB.HilbertModular
