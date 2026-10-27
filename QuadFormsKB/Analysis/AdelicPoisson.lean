import QuadFormsKB.Analysis.MinkowskiPoisson

/-!
# Adelic Poisson summation for a number field

Let $F$ be a number field, $F_\infty = F\otimes\mathbb{R} = \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ (Mathlib's mixed space),
and $F_v$ the completion at a finite place $v$. Characters and measures (Tate's normalization):

* $\psi_\infty = e\circ\operatorname{Tr}_\infty$ (`psiInf`): $e(x)$ at a real place, $e(2\operatorname{Re}z)$ at a complex place;
  self-dual measure `selfDualInf` = Lebesgue at real places, $2\,dx\,dy$ at complex places;
* $\psi_v = \psi_p\circ\operatorname{Tr}_{F_v/\mathbb{Q}_p}$ (`psiV`), $\psi_p(x) = e(-\{x\}_p)$; self-dual measure `selfDualV v`
  with $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$;
* $\hat f(y) = \int f(x)\psi(xy)\,dx$ at every place (`fourierInf`, `fourierV`).

With these, $\psi = \psi_\infty\otimes\bigotimes_v\psi_v$ is trivial on $F$ (`fourierChar_trace_mul_finprod_psiV`) and

* **`adelicPoisson`**: for $f = f_\infty\otimes\bigotimes_v\mathbf 1_{\xi+\mathfrak p_v^{k_v}}$ ($f_\infty$ Schwartz, $\xi\in F$,
  $k_v = 0$ for almost all $v$), $\sum_{\gamma\in F}f(\gamma) = \sum_{\gamma\in F}\hat f(\gamma)$, both sums absolutely
  convergent (`summable_adelicPoisson_lhs`, `summable_adelicPoisson_rhs`).

Equivalently $\operatorname{vol}(\mathbb{A}_F/F) = 1$ for the self-dual measure: the constants match because
$\prod_v\operatorname{vol}(\mathfrak p_v^{k_v}) = (N(\mathfrak a)|d_F|^{1/2})^{-1}$ (`finprod_selfDualV_real`, from
$\prod_v N(v)^{d_v} = |d_F|$) and the covolume of $\mathfrak a$ for the self-dual measure on $F_\infty$ is
$N(\mathfrak a)|d_F|^{1/2}$ (`selfDual_covolume_idealLattice`).

* **`adelicPoisson_factorizable`**: the same for every factorizable Schwartz–Bruhat function
  $f = f_\infty\otimes\bigotimes_v f_v$, $f_v$ a finite linear combination of coset indicators (`IsSchwartzBruhatV`)
  and $f_v = \mathbf 1_{\mathcal O_v}$ for almost all $v$ (absolute convergence:
  `summable_adelicPoisson_factorizable_lhs`, `_rhs`). It reduces to `adelicPoisson` by expanding the product
  (`finprod_expand`) and recentering each product of cosets at a global point (`exists_strong_approx`, strong
  approximation for the finite adeles; `factorizable_expansion`).

The adele ring itself (`AdeleRing`) is not used: $f(\gamma)$ for $\gamma\in F$ is written directly as
$f_\infty(\gamma)\prod_v f_v(\gamma)$.

Sources: Tate's thesis, Cassels–Fröhlich Ch. XV, Thm. 4.2.1 [unverified]; Weil, *Basic Number Theory*,
Ch. VII §2, Prop. 4 and Ch. VIII [unverified].
-/

open IsDedekindDomain NumberField WithZero MeasureTheory NumberField.InfinitePlace
open NumberField.mixedEmbedding
open scoped Real FourierTransform nonZeroDivisors Classical

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Analysis

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F
local notation "FI" => FractionalIdeal (𝓞 F)⁰ F

/-- $N(v)$ as a real number. -/
abbrev Nv (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

lemma Nv_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Nv v := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

/-- $\operatorname{vol}(\mathfrak p_v^k) = N(\mathfrak d_v)^{-1/2}N(v)^{-k}$ for the self-dual measure. -/
lemma selfDualV_real_latticeV_eq (v : HeightOneSpectrum (𝓞 F)) (k : ℤ) :
    (selfDualV v).real (latticeV v k) = (Nv v ^ diffExp v) ^ (-(1 / 2 : ℝ)) * (Nv v ^ k)⁻¹ := by
  have hN := (Nv_pos v).le
  rw [selfDualV_real_latticeV, modV_eq, inv_zpow, Real.inv_rpow hN, ← Real.rpow_natCast,
    ← Real.rpow_mul hN, ← Real.rpow_neg hN]
  congr 2
  ring

/-- The rational finprod of a function supported in `S`, cast to `ℝ`. -/
lemma cast_finprod_eq {a : HeightOneSpectrum (𝓞 F) → ℚ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (h : Function.mulSupport a ⊆ S) : ((∏ᶠ v, a v : ℚ) : ℝ) = ∏ v ∈ S, (a v : ℝ) := by
  rw [finprod_eq_prod_of_mulSupport_subset a h, Rat.cast_prod]

/-- **The volume of $\hat{\mathfrak a} = \prod_v \mathfrak p_v^{k_v}$:** $\prod_v\operatorname{vol}(\mathfrak p_v^{k_v}) =
\big(N(\mathfrak a)\,|d_F|^{1/2}\big)^{-1}$ (self-dual measures). -/
theorem finprod_selfDualV_real {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite) :
    ∏ᶠ v, (selfDualV v).real (latticeV v (k v)) =
      ((FractionalIdeal.absNorm (idealOfExps k) : ℝ) * Real.sqrt |(discr F : ℝ)|)⁻¹ := by
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (hk.union finite_support_diffExp).toFinset with hS
  have hmem : ∀ v, v ∉ S → k v = 0 ∧ diffExp v = 0 := by
    intro v hv
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or, not_not] at hv
    exact ⟨hv.1, by exact_mod_cast hv.2⟩
  have hsub : ∀ {a : HeightOneSpectrum (𝓞 F) → ℝ}, (∀ v, k v = 0 → diffExp v = 0 → a v = 1) →
      Function.mulSupport a ⊆ S := by
    intro a ha v hv
    by_contra h
    exact hv (ha v (hmem v h).1 (hmem v h).2)
  rw [finprod_eq_prod_of_mulSupport_subset _ (hsub fun v hk hd => by
    rw [selfDualV_real_latticeV_eq, hk, hd]; simp)]
  simp_rw [selfDualV_real_latticeV_eq]
  rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun v _ => by positivity), Finset.prod_inv_distrib]
  -- the two finite products
  have h1 : ∏ v ∈ S, Nv v ^ diffExp v = |(discr F : ℝ)| := by
    have := finprod_absNorm_pow_diffExp (F := F)
    have h' := congrArg (fun q : ℚ => (q : ℝ)) this
    rw [cast_finprod_eq (S := S) ?_] at h'
    · rw [Rat.cast_abs, Rat.cast_intCast] at h'
      rw [← h']
      refine Finset.prod_congr rfl fun v _ => ?_
      push_cast; rfl
    · intro v hv
      by_contra h
      exact hv (by simp [(hmem v h).2])
  have h2 : ∏ v ∈ S, Nv v ^ k v = (FractionalIdeal.absNorm (idealOfExps k) : ℝ) := by
    rw [absNorm_idealOfExps hk, cast_finprod_eq (S := S)]
    · refine Finset.prod_congr rfl fun v _ => ?_
      push_cast; rfl
    · intro v hv
      by_contra h
      exact hv (by simp [(hmem v h).1])
  rw [h1, h2, Real.sqrt_eq_rpow, Real.rpow_neg (abs_nonneg _), mul_inv, mul_comm]

/-! ### The finite parts -/


/-- The finite part of $f$: $\prod_v \mathbf 1_{\xi + \mathfrak p_v^{k_v}}(\gamma) = \mathbf 1_{\xi + \mathfrak a}(\gamma)$ for
$\gamma \in F$, $\mathfrak a = \prod_v\mathfrak p_v^{k_v}$. -/
theorem finprod_ballIndV {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite)
    (ξ γ : F) :
    ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v) (algebraMap F (v.adicCompletion F) γ) =
      if γ - ξ ∈ idealOfExps k then 1 else 0 := by
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v)
      (algebraMap F (v.adicCompletion F) γ) =
        if Valued.v (algebraMap F (v.adicCompletion F) (γ - ξ)) ≤ exp (-k v) then 1 else 0 := by
    intro v
    simp only [ballIndV, Set.indicator, Set.mem_ofPred_eq, map_sub]
  simp_rw [hval]
  split_ifs with h
  · rw [mem_idealOfExps_iff hk] at h
    exact finprod_eq_one_of_forall_eq_one fun v => if_pos (h v)
  · rw [mem_idealOfExps_iff hk] at h
    push_neg at h
    obtain ⟨v, hv⟩ := h
    refine finprod_eq_zero _ v (if_neg (not_le.mpr hv)) ?_
    refine (hk.union (HeightOneSpectrum.Support.finite (𝓞 F) (γ - ξ))).subset fun w hw => ?_
    rw [Function.mem_mulSupport] at hw
    by_contra hw'
    simp only [Set.mem_union, Function.mem_support, not_or, not_not, HeightOneSpectrum.Support,
      Set.mem_ofPred_eq, not_lt] at hw'
    refine hw (if_pos ?_)
    rw [HN.valued_algebraMap, hw'.1, neg_zero, exp_zero]
    exact hw'.2

/-- The local transforms: $\prod_v\widehat{\mathbf 1_{\xi+\mathfrak p_v^{k_v}}}(\gamma) =
\operatorname{vol}(\hat{\mathfrak a})\,e(-\operatorname{Tr}(\xi\gamma))\,\mathbf 1_{\mathfrak a^\vee}(\gamma)$ for $\gamma \in F$. -/
theorem finprod_fourierV_ballIndV {k : HeightOneSpectrum (𝓞 F) → ℤ} (hk : (Function.support k).Finite)
    (ξ γ : F) :
    ∏ᶠ v, fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v))
        (algebraMap F (v.adicCompletion F) γ) =
      if γ ∈ FractionalIdeal.dual ℤ ℚ (idealOfExps k) then
        (((FractionalIdeal.absNorm (idealOfExps k) : ℝ) * Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) *
          ((𝐞 (-((Algebra.trace ℚ F (ξ * γ) : ℚ) : ℝ)) : Circle) : ℂ)
      else 0 := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) ξ)
      (k v)) (algebraMap F (v.adicCompletion F) γ) =
        if Valued.v (algebraMap F (v.adicCompletion F) γ) ≤ exp (k v + diffExp v) then
          ((selfDualV v).real (latticeV v (k v)) : ℂ) *
            (psiV v (algebraMap F (v.adicCompletion F) (ξ * γ)) : ℂ) else 0 := by
    intro v
    rw [fourierV_ballIndV, ← RingHom.map_mul]
    congr 1
    rw [eq_iff_iff, mem_latticeV]
    congr! 2
    ring
  simp_rw [hloc]
  have hS := (hk.union finite_support_diffExp).union
    ((HeightOneSpectrum.Support.finite (𝓞 F) γ).union (HeightOneSpectrum.Support.finite (𝓞 F) (ξ * γ)))
  have hsupp : ∀ {a : HeightOneSpectrum (𝓞 F) → ℂ}, (∀ v, k v = 0 → diffExp v = 0 →
      v.valuation F γ ≤ 1 → v.valuation F (ξ * γ) ≤ 1 → a v = 1) → (Function.mulSupport a).Finite := by
    intro a ha
    refine hS.subset fun v hv => ?_
    rw [Function.mem_mulSupport] at hv
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not, HeightOneSpectrum.Support,
      Set.mem_ofPred_eq, not_lt] at h
    exact hv (ha v h.1.1 (by exact_mod_cast h.1.2) h.2.1 h.2.2)
  have hone : ∀ v, k v = 0 → diffExp v = 0 → v.valuation F γ ≤ 1 → v.valuation F (ξ * γ) ≤ 1 →
      ((selfDualV v).real (latticeV v (k v)) : ℂ) *
        (psiV v (algebraMap F (v.adicCompletion F) (ξ * γ)) : ℂ) = 1 := by
    intro v hkv hdv _ hxg
    rw [selfDualV_real_latticeV_eq, hkv, hdv, psiV_eq_one_of_le_one v (by rwa [HN.valued_algebraMap])]
    simp
  split_ifs with h
  · rw [mem_dual_idealOfExps_iff hk] at h
    simp_rw [if_pos (h _)]
    rw [finprod_mul_distrib (hsupp fun v hkv hdv _ _ => by
        rw [selfDualV_real_latticeV_eq, hkv, hdv]; simp)
      (hsupp fun v _ _ _ hxg => by
        rw [psiV_eq_one_of_le_one v (by rwa [HN.valued_algebraMap])]; simp)]
    congr 1
    · rw [← finprod_selfDualV_real hk]
      have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
          (selfDualV v).real (latticeV v (k v)) :=
        (hk.union finite_support_diffExp).subset fun v hv => by
          rw [Function.mem_mulSupport] at hv
          by_contra h
          simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
          exact hv (by rw [selfDualV_real_latticeV_eq, h.1, show diffExp v = 0 by exact_mod_cast h.2]; simp)
      exact (MonoidHom.map_finprod Complex.ofRealHom.toMonoidHom hfin).symm
    · rw [← finprod_psiV_eq_fourierChar]
      exact (MonoidHom.map_finprod Circle.coeHom (hasFiniteMulSupport_psiV (ξ * γ))).symm
  · rw [mem_dual_idealOfExps_iff hk] at h
    push_neg at h
    obtain ⟨v, hv⟩ := h
    refine finprod_eq_zero _ v (if_neg (not_le.mpr hv)) (hsupp fun w hkw hdw hγ hxg => ?_)
    rw [if_pos]
    · exact hone w hkw hdw hγ hxg
    · rw [HN.valued_algebraMap, hkw, hdw]
      simpa using hγ

/-! ### Adelic Poisson summation -/

lemma lhs_eq_indicator (f : SchwartzMap V ℂ) (ξ : F) {k : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : (Function.support k).Finite) :
    (fun γ : F => f (mixedEmbedding F γ) *
      ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v) (algebraMap F (v.adicCompletion F) γ)) =
      fun γ => ((idealOfExps k : FI) : Set F).indicator (fun x => f (mixedEmbedding F (ξ + x))) (γ - ξ) := by
  funext γ
  rw [finprod_ballIndV hk]
  by_cases h : γ - ξ ∈ idealOfExps k
  · rw [if_pos h, mul_one, Set.indicator_of_mem (show γ - ξ ∈ ((idealOfExps k : FI) : Set F) from h),
      add_sub_cancel]
  · rw [if_neg h, mul_zero, Set.indicator_of_notMem (show γ - ξ ∉ ((idealOfExps k : FI) : Set F) from h)]

lemma rhs_eq_indicator (f : SchwartzMap V ℂ) (ξ : F) {k : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : (Function.support k).Finite) :
    (fun γ : F => fourierInf f (mixedEmbedding F γ) * ∏ᶠ v, fourierV v (ballIndV v
        (algebraMap F (v.adicCompletion F) ξ) (k v)) (algebraMap F (v.adicCompletion F) γ)) =
      fun γ => (((FractionalIdeal.dual ℤ ℚ (idealOfExps k) : FI)) : Set F).indicator
        (fun μ => (((FractionalIdeal.absNorm (idealOfExps k) : ℝ) * Real.sqrt |(discr F : ℝ)|)⁻¹ : ℝ) *
          (fourierInf f (mixedEmbedding F μ) *
            ((𝐞 (-((Algebra.trace ℚ F (ξ * μ) : ℚ) : ℝ)) : Circle) : ℂ))) γ := by
  funext γ
  rw [finprod_fourierV_ballIndV hk]
  by_cases h : γ ∈ FractionalIdeal.dual ℤ ℚ (idealOfExps k)
  · rw [if_pos h, Set.indicator_of_mem (show γ ∈ ((FractionalIdeal.dual ℤ ℚ (idealOfExps k) : FI) :
      Set F) from h)]
    ring
  · rw [if_neg h, mul_zero, Set.indicator_of_notMem (show γ ∉ ((FractionalIdeal.dual ℤ ℚ
      (idealOfExps k) : FI) : Set F) from h)]

/-- **Adelic Poisson summation over a number field** (for $f_v$ = coset indicators). Let $f_\infty$ be a
Schwartz function on $F_\infty = F\otimes\mathbb{R} = \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ (Mathlib's mixed space),
$\xi \in F$, and $k_v \in \mathbb{Z}$ with $k_v = 0$ for almost all finite places $v$. Put
$f = f_\infty\otimes\bigotimes_v f_v$ with $f_v = \mathbf 1_{\xi+\mathfrak p_v^{k_v}}$ (so $f_v = \mathbf 1_{\mathcal O_v}$ for
almost all $v$), and $\hat f = \hat f_\infty\otimes\bigotimes_v\hat f_v$, the product of the local Fourier transforms for
$\psi = \psi_\infty\otimes\bigotimes_v\psi_v$ ($\psi_\infty = e\circ\operatorname{Tr}_\infty$ = `psiInf`, $\psi_v$ = `psiV v`) and
the self-dual measures (`selfDualInf`, `selfDualV v`). Then
$$\sum_{\gamma\in F} f(\gamma) = \sum_{\gamma\in F}\hat f(\gamma),$$
both sums converging absolutely (`summable_adelicPoisson_lhs`, `summable_adelicPoisson_rhs`). Here
$f(\gamma) = f_\infty(\gamma)\prod_v f_v(\gamma)$ and the products over $v$ are finite products (`finprod`).

*Proof:* the finite parts restrict $\gamma$ to $\xi + \mathfrak a$, $\mathfrak a = \prod_v\mathfrak p_v^{k_v}$
(`finprod_ballIndV`), resp. give $\operatorname{vol}(\hat{\mathfrak a})\,e(-\operatorname{Tr}(\xi\gamma))\mathbf 1_{\mathfrak a^\vee}(\gamma)$
(`finprod_fourierV_ballIndV`, using the product formula `finprod_psiV_eq_fourierChar` and
$\mathfrak a^\vee = \mathfrak a^{-1}\mathfrak d^{-1}$); then `poisson_fractionalIdeal`, with
$\operatorname{vol}(\hat{\mathfrak a}) = (N(\mathfrak a)|d_F|^{1/2})^{-1} = (2^{r_2}\operatorname{covol}\mathfrak a)^{-1}$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 4.2.1 (Poisson summation formula) [unverified]"]
theorem adelicPoisson (f : SchwartzMap V ℂ) (ξ : F) {k : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : (Function.support k).Finite) :
    ∑' γ : F, f (mixedEmbedding F γ) *
        ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v) (algebraMap F (v.adicCompletion F) γ) =
      ∑' γ : F, fourierInf f (mixedEmbedding F γ) *
        ∏ᶠ v, fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v))
          (algebraMap F (v.adicCompletion F) γ) := by
  set Iu : FIˣ := Units.mk0 (idealOfExps k) (idealOfExps_ne_zero k)
  have hIu : (Iu : FI) = idealOfExps k := rfl
  rw [lhs_eq_indicator f ξ hk, rhs_eq_indicator f ξ hk]
  rw [← (Equiv.subRight ξ).symm.tsum_eq]
  simp only [Equiv.subRight_symm_apply, add_sub_cancel_right]
  rw [← tsum_subtype, ← tsum_subtype, tsum_mul_left, ← hIu, poisson_fractionalIdeal Iu f ξ,
    selfDual_covolume_idealLattice]

/-- The left side of `adelicPoisson` converges absolutely. -/
theorem summable_adelicPoisson_lhs (f : SchwartzMap V ℂ) (ξ : F) {k : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : (Function.support k).Finite) :
    Summable fun γ : F => f (mixedEmbedding F γ) *
      ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) ξ) (k v) (algebraMap F (v.adicCompletion F) γ) := by
  set Iu : FIˣ := Units.mk0 (idealOfExps k) (idealOfExps_ne_zero k)
  rw [lhs_eq_indicator f ξ hk, ← (Equiv.subRight ξ).symm.summable_iff]
  simp only [Function.comp_def, Equiv.subRight_symm_apply, add_sub_cancel_right]
  rw [← summable_subtype_iff_indicator]
  exact summable_poisson_lhs Iu f ξ

/-- The right side of `adelicPoisson` converges absolutely. -/
theorem summable_adelicPoisson_rhs (f : SchwartzMap V ℂ) (ξ : F) {k : HeightOneSpectrum (𝓞 F) → ℤ}
    (hk : (Function.support k).Finite) :
    Summable fun γ : F => fourierInf f (mixedEmbedding F γ) * ∏ᶠ v, fourierV v (ballIndV v
        (algebraMap F (v.adicCompletion F) ξ) (k v)) (algebraMap F (v.adicCompletion F) γ) := by
  set Iu : FIˣ := Units.mk0 (idealOfExps k) (idealOfExps_ne_zero k)
  rw [rhs_eq_indicator f ξ hk, ← summable_subtype_iff_indicator]
  exact (summable_poisson_rhs Iu f ξ).mul_left _

/-! ### Strong approximation and factorizable Schwartz–Bruhat functions -/

/-- The `v`-adic valuation of a nonzero integer `d`, as `exp (-ord_v d)`. -/
lemma valued_natCast_eq (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (hd : d ≠ 0) :
    Valued.v ((d : ℕ) : v.adicCompletion F) =
      exp (-(multiplicity v.asIdeal (Ideal.span {(d : 𝓞 F)}) : ℤ)) := by
  have hd' : (d : 𝓞 F) ≠ 0 := by exact_mod_cast hd
  have : ((d : ℕ) : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (d : 𝓞 F)) := by simp
  rw [this, HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hd']

/-- A positive integer `d` with `v(d · c_v) ≤ 1` at the finitely many places `v ∈ S`. -/
lemma exists_nat_clear (S : Finset (HeightOneSpectrum (𝓞 F))) (c : ∀ v : HeightOneSpectrum (𝓞 F),
    v.adicCompletion F) : ∃ d : ℕ, d ≠ 0 ∧ ∀ v ∈ S, Valued.v ((d : v.adicCompletion F) * c v) ≤ 1 := by
  choose m hm using fun v : HeightOneSpectrum (𝓞 F) => exists_valued_le_exp (c v)
  refine ⟨∏ v ∈ S, resChar v ^ m v, Finset.prod_ne_zero_iff.mpr fun v _ =>
    pow_ne_zero _ (Fact.out : (resChar v).Prime).ne_zero, fun v hv => ?_⟩
  have hle : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v ((resChar w : ℕ) : v.adicCompletion F) ≤ 1 := by
    intro w
    have : ((resChar w : ℕ) : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (resChar w : 𝓞 F)) := by
      simp
    rw [this, HN.valued_algebraMap]
    exact v.valuation_le_one _
  have hpv : Valued.v ((resChar v : ℕ) : v.adicCompletion F) ≤ exp (-1 : ℤ) := by
    refine HN.valued_le_exp_neg_one v ?_
    have : ((resChar v : ℕ) : v.adicCompletion F) = algebraMap F _ (algebraMap (𝓞 F) F (resChar v : 𝓞 F)) := by
      simp
    rw [this, HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact (resChar_eq_iff v _).mp rfl
  rw [Nat.cast_prod, ← Finset.mul_prod_erase _ _ hv, map_mul, map_mul]
  calc Valued.v (((resChar v ^ m v : ℕ) : v.adicCompletion F)) *
        Valued.v (∏ w ∈ S.erase v, ((resChar w ^ m w : ℕ) : v.adicCompletion F)) * Valued.v (c v)
      ≤ exp (-(m v : ℤ)) * 1 * exp (m v : ℤ) := by
        gcongr
        · rw [Nat.cast_pow, map_pow]
          calc Valued.v ((resChar v : ℕ) : v.adicCompletion F) ^ m v ≤ exp (-1 : ℤ) ^ m v :=
                pow_le_pow_left₀ zero_le hpv _
            _ = exp (-(m v : ℤ)) := by rw [← exp_nsmul]; congr 1; simp
        · rw [map_prod]
          exact Finset.prod_le_one fun w _ => by rw [Nat.cast_pow, map_pow]; exact pow_le_one' (hle w) _
        · exact hm v
    _ = 1 := by rw [mul_one, ← exp_add, neg_add_cancel, exp_zero]

lemma valued_algebraMap_int_le_of_mem (v : HeightOneSpectrum (𝓞 F)) {b : 𝓞 F} {n : ℕ}
    (h : b ∈ v.asIdeal ^ n) : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ exp (-(n : ℤ)) := by
  rw [HN.valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr h

/-- **Strong approximation for the finite adeles** (in the form needed here): for a finite set $S$ of finite
places, $c_v \in F_v$ and $k_v \in \mathbb{Z}$, there is $\xi \in F$ with $v(\xi - c_v) \le \exp(-k_v)$ for $v \in S$
and $\xi \in \mathcal O_v$ for $v \notin S$. -/
@[kb "casselsfrohlich1967" "Ch. II (Cassels), §15 (strong approximation) [unverified]"]
theorem exists_strong_approx (S : Finset (HeightOneSpectrum (𝓞 F)))
    (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (k : HeightOneSpectrum (𝓞 F) → ℤ) :
    ∃ ξ : F, (∀ v ∈ S, Valued.v (algebraMap F (v.adicCompletion F) ξ - c v) ≤ exp (-k v)) ∧
      ∀ v ∉ S, Valued.v (algebraMap F (v.adicCompletion F) ξ) ≤ 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_clear S c
  have hdO : (d : 𝓞 F) ≠ 0 := by exact_mod_cast hd0
  have hspan : Ideal.span {(d : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hdO
  set e : HeightOneSpectrum (𝓞 F) → ℕ := fun v => multiplicity v.asIdeal (Ideal.span {(d : 𝓞 F)})
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ (Ideal.finite_factors hspan).toFinset
  set N : HeightOneSpectrum (𝓞 F) → ℕ := fun v => if v ∈ S then (k v).toNat + e v else e v
  set t : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F :=
    fun v => if v ∈ S then (d : v.adicCompletion F) * c v else 0 with ht
  have ht1 : ∀ v, Valued.v (t v) ≤ 1 := by
    intro v
    by_cases hv : v ∈ S
    · simp only [ht, hv, if_true]; exact hd v hv
    · simp only [ht, hv, if_false, map_zero]; exact zero_le
  choose a ha using fun v : HeightOneSpectrum (𝓞 F) => exists_int_approx_pow v (N v) (t v) (ht1 v)
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) N
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  have hdv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((d : ℕ) : v.adicCompletion F) = exp (-(e v : ℤ)) :=
    fun v => valued_natCast_eq v hd0
  have hdne : ∀ v : HeightOneSpectrum (𝓞 F), ((d : ℕ) : v.adicCompletion F) ≠ 0 := fun v => by
    exact_mod_cast hd0
  refine ⟨(b : F) / d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := valued_algebraMap_int_le_of_mem v (hb v hvT)
    have h2 := ha v
    simp only [ht, hv, if_true] at h2
    have hNv : N v = (k v).toNat + e v := by simp [N, hv]
    rw [hNv] at h1 h2
    have e1 : algebraMap F (v.adicCompletion F) ((b : F) / d) - c v =
        (((d : ℕ) : v.adicCompletion F))⁻¹ *
          (algebraMap F (v.adicCompletion F) ((b - a v : 𝓞 F) : F) -
            ((d : v.adicCompletion F) * c v - algebraMap F (v.adicCompletion F) (a v : F))) := by
      rw [map_div₀, map_natCast]
      push_cast
      field_simp
      ring
    rw [e1, map_mul, map_inv₀, hdv]
    calc (exp (-(e v : ℤ)))⁻¹ * Valued.v (algebraMap F (v.adicCompletion F) ((b - a v : 𝓞 F) : F) -
          ((d : v.adicCompletion F) * c v - algebraMap F (v.adicCompletion F) (a v : F)))
        ≤ (exp (-(e v : ℤ)))⁻¹ * exp (-(((k v).toNat + e v : ℕ) : ℤ)) := by
          gcongr
          exact (Valuation.map_sub _ _ _).trans (max_le h1 h2)
      _ ≤ exp (-k v) := by
          rw [← exp_neg, ← exp_add, exp_le_exp]
          have := Int.self_le_toNat (k v)
          push_cast
          omega
  · have hb' : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ exp (-(e v : ℤ)) := by
      by_cases hvT : v ∈ T
      · have h1 := valued_algebraMap_int_le_of_mem v (hb v hvT)
        have h2 := ha v
        simp only [ht, hv, if_false, zero_sub, Valuation.map_neg] at h2
        have hNv : N v = e v := by simp [N, hv]
        rw [hNv] at h1 h2
        have : (b : F) = ((b - a v : 𝓞 F) : F) + (a v : F) := by push_cast; ring
        rw [this, map_add]
        exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
      · have he : e v = 0 := by
          refine multiplicity_eq_zero_of_not_dvd fun h => hvT ?_
          exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
        rw [he, Nat.cast_zero, neg_zero, exp_zero, HN.valued_algebraMap]
        exact v.valuation_le_one _
    rw [map_div₀, map_natCast, map_div₀, hdv, div_le_iff₀ (by simp)]
    simpa using hb'

/-- Recentering a ball: $c' + \mathfrak p_v^k = c + \mathfrak p_v^k$ when $c' - c \in \mathfrak p_v^k$. -/
lemma ballIndV_recenter (v : HeightOneSpectrum (𝓞 F)) {c c' : v.adicCompletion F} {k : ℤ}
    (h : Valued.v (c' - c) ≤ exp (-k)) : ballIndV v c k = ballIndV v c' k := by
  unfold ballIndV
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    have : x - c' = (x - c) - (c' - c) := by ring
    rw [this]; exact (Valuation.map_sub _ _ _).trans (max_le hx h)
  · intro hx
    have : x - c = (x - c') + (c' - c) := by ring
    rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hx h)

/-- Splitting a finite product at a finite set `S`. -/
lemma finprod_split {ι : Type*} (S : Finset ι) (g : ι → ℂ)
    (hg : Function.HasFiniteMulSupport fun v => if v ∈ S then 1 else g v) :
    ∏ᶠ v, g v = (∏ w : S, g w) * ∏ᶠ v, (if v ∈ S then 1 else g v) := by
  have hA : Function.HasFiniteMulSupport fun v => if v ∈ S then g v else 1 :=
    S.finite_toSet.subset fun v hv => by
      rw [Function.mem_mulSupport] at hv
      by_contra h; exact hv (if_neg h)
  have hpt : (fun v => g v) = fun v => (if v ∈ S then g v else 1) * (if v ∈ S then 1 else g v) := by
    funext v; by_cases h : v ∈ S <;> simp [h]
  rw [hpt, finprod_mul_distrib hA hg, finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun v hv => by
      rw [Function.mem_mulSupport] at hv
      by_contra h; exact hv (if_neg h)), ← Finset.prod_coe_sort S]
  congr 1
  exact Finset.prod_congr rfl fun w _ => if_pos w.2

/-- **Expanding a product of finite sums** over the places in `S`, the other factors being common. -/
lemma finprod_expand {ι : Type*} (S : Finset ι) (n : S → ℕ) (a B : ∀ w : S, Fin (n w) → ℂ)
    (G : ι → ℂ) (H : (∀ w : S, Fin (n w)) → ι → ℂ)
    (hG : ∀ w : S, G w = ∑ j, a w j * B w j) (hH : ∀ J (w : S), H J w = B w (J w))
    (hout : ∀ J, ∀ v ∉ S, H J v = G v)
    (hfin : Function.HasFiniteMulSupport fun v => if v ∈ S then 1 else G v) :
    ∏ᶠ v, G v = ∑ J : (∀ w : S, Fin (n w)), (∏ w, a w (J w)) * ∏ᶠ v, H J v := by
  have hR : ∀ J, (fun v => if v ∈ S then 1 else H J v) = fun v => if v ∈ S then 1 else G v := by
    intro J; funext v; by_cases h : v ∈ S
    · simp [h]
    · simp [h, hout J v h]
  rw [finprod_split S G hfin]
  simp_rw [fun J => finprod_split S (H J) (by rw [hR J]; exact hfin), hR, hG, hH]
  rw [Finset.prod_univ_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

/-! ### Factorizable Schwartz–Bruhat functions -/

section Factorizable

variable (fv : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
  (hS : ∀ v ∈ S, IsSchwartzBruhatV v (fv v)) (hout : ∀ v ∉ S, fv v = ballIndV v 0 0)

include hS in
/-- The data of `IsSchwartzBruhatV` at the places of `S`. -/
lemma exists_rep : ∃ (n : S → ℕ) (a : ∀ w : S, Fin (n w) → ℂ)
    (c : ∀ w : S, Fin (n w) → w.1.adicCompletion F) (k : ∀ w : S, Fin (n w) → ℤ),
    ∀ w : S, fv w = fun x => ∑ i, a w i * ballIndV w.1 (c w i) (k w i) x := by
  choose n a c k h using fun w : S => hS w.1 w.2
  exact ⟨n, a, c, k, h⟩

/-- The local transform of `1_{O_v}` is `1` at an integral point when `d_v = 0`. -/
lemma fourierV_ballIndV_zero_eq_one (v : HeightOneSpectrum (𝓞 F)) (hd : diffExp v = 0)
    {y : v.adicCompletion F} (hy : Valued.v y ≤ 1) : fourierV v (ballIndV v 0 0) y = 1 := by
  rw [fourierV_ballIndV, if_pos, zero_mul, AddChar.map_zero_eq_one, Circle.coe_one, mul_one,
    selfDualV_real_latticeV_eq, hd]
  · simp
  · rw [mem_latticeV, hd]; simpa using hy

include hS hout in
/-- **Reduction to pure tensors with a global center:** on $F$, a factorizable Schwartz–Bruhat function
$\prod_v f_v$ (with $f_v = \mathbf 1_{\mathcal O_v}$ outside $S$) is a finite combination
$\sum_J A_J\prod_v\mathbf 1_{\xi_J + \mathfrak p_v^{k_{J,v}}}$ with $\xi_J\in F$, and $\prod_v\hat f_v$ is the same
combination of the transforms. -/
lemma factorizable_expansion : ∃ (ι : Type) (_ : Fintype ι) (A : ι → ℂ) (ξ : ι → F)
    (k : ι → HeightOneSpectrum (𝓞 F) → ℤ), (∀ J, (Function.support (k J)).Finite) ∧
    (∀ γ : F, ∏ᶠ v, fv v (algebraMap F (v.adicCompletion F) γ) =
      ∑ J, A J * ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) (ξ J)) (k J v)
        (algebraMap F (v.adicCompletion F) γ)) ∧
    (∀ γ : F, ∏ᶠ v, fourierV v (fv v) (algebraMap F (v.adicCompletion F) γ) =
      ∑ J, A J * ∏ᶠ v, fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ J)) (k J v))
        (algebraMap F (v.adicCompletion F) γ)) := by
  obtain ⟨n, a, c, kk, hrep⟩ := exists_rep fv S hS
  -- exponents and centers of the pure tensors
  set kJ : (∀ w : S, Fin (n w)) → HeightOneSpectrum (𝓞 F) → ℤ :=
    fun J v => if h : v ∈ S then kk ⟨v, h⟩ (J ⟨v, h⟩) else 0 with hkJ
  set cJ : (∀ w : S, Fin (n w)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F :=
    fun J v => if h : v ∈ S then c ⟨v, h⟩ (J ⟨v, h⟩) else 0 with hcJ
  choose ξ hξS hξout using fun J => exists_strong_approx S (cJ J) (kJ J)
  have hfinJ : ∀ J, (Function.support (kJ J)).Finite := fun J =>
    S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (by simp only [hkJ, dif_neg (show v ∉ S from h)])
  have hball : ∀ J v, ballIndV v (algebraMap F (v.adicCompletion F) (ξ J)) (kJ J v) =
      if h : v ∈ S then ballIndV v (c ⟨v, h⟩ (J ⟨v, h⟩)) (kk ⟨v, h⟩ (J ⟨v, h⟩)) else ballIndV v 0 0 := by
    intro J v
    by_cases h : v ∈ S
    · rw [dif_pos h]
      have := hξS J v h
      simp only [hcJ, hkJ, dif_pos h] at this ⊢
      exact (ballIndV_recenter v this).symm
    · rw [dif_neg h]
      have := hξout J v h
      simp only [hkJ, dif_neg h]
      exact (ballIndV_recenter v (by simpa using this)).symm
  -- expansions, pointwise in `γ`
  have hL : ∀ γ : F, ∏ᶠ v, fv v (algebraMap F (v.adicCompletion F) γ) =
      ∑ J : (∀ w : S, Fin (n w)), (∏ w, a w (J w)) *
        ∏ᶠ v, ballIndV v (algebraMap F (v.adicCompletion F) (ξ J)) (kJ J v)
          (algebraMap F (v.adicCompletion F) γ) := by
    intro γ
    refine finprod_expand S n a (fun w j => ballIndV w.1 (c w j) (kk w j)
      (algebraMap F (w.1.adicCompletion F) γ)) _ _ (fun w => by rw [hrep w]) (fun J w => ?_)
      (fun J v hv => ?_) ?_
    · rw [hball, dif_pos w.2]
    · rw [hball, dif_neg hv, hout v hv]
    · refine (HeightOneSpectrum.Support.finite (𝓞 F) γ).subset fun v hv => ?_
      rw [Function.mem_mulSupport] at hv
      by_contra h
      refine hv ?_
      split_ifs with hvS
      · rfl
      · rw [hout v hvS, ballIndV, Set.indicator_of_mem]
        simpa [HeightOneSpectrum.Support, HN.valued_algebraMap] using h
  have hR : ∀ γ : F, ∏ᶠ v, fourierV v (fv v) (algebraMap F (v.adicCompletion F) γ) =
      ∑ J : (∀ w : S, Fin (n w)), (∏ w, a w (J w)) *
        ∏ᶠ v, fourierV v (ballIndV v (algebraMap F (v.adicCompletion F) (ξ J)) (kJ J v))
          (algebraMap F (v.adicCompletion F) γ) := by
    intro γ
    refine finprod_expand S n a (fun w j => fourierV w.1 (ballIndV w.1 (c w j) (kk w j))
      (algebraMap F (w.1.adicCompletion F) γ)) _ _ (fun w => by rw [hrep w, fourierV_sum])
      (fun J w => ?_) (fun J v hv => ?_) ?_
    · rw [hball, dif_pos w.2]
    · rw [hball, dif_neg hv, hout v hv]
    · refine (finite_support_diffExp.union (HeightOneSpectrum.Support.finite (𝓞 F) γ)).subset
        fun v hv => ?_
      rw [Function.mem_mulSupport] at hv
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not, HeightOneSpectrum.Support,
        Set.mem_ofPred_eq, not_lt] at h
      refine hv ?_
      split_ifs with hvS
      · rfl
      · rw [hout v hvS]
        exact fourierV_ballIndV_zero_eq_one v (by exact_mod_cast h.1)
          (by rw [HN.valued_algebraMap]; exact h.2)
  refine ⟨(∀ w : S, Fin (n w)), inferInstance, fun J => ∏ w, a w (J w), ξ, kJ, hfinJ,
    fun γ => ?_, fun γ => ?_⟩
  · exact hL γ
  · exact hR γ

include hS hout in
/-- **Adelic Poisson summation for factorizable Schwartz–Bruhat functions.** Let $f_\infty$ be a Schwartz function on
$F_\infty$, and for each finite place $v$ let $f_v : F_v \to \mathbb{C}$ be a Schwartz–Bruhat function (a finite linear
combination of coset indicators $\mathbf 1_{c+\mathfrak p_v^k}$, `IsSchwartzBruhatV`), with $f_v = \mathbf 1_{\mathcal O_v}$
for $v \notin S$, $S$ finite. For $f = f_\infty\otimes\bigotimes_v f_v$ and $\hat f = \hat f_\infty\otimes\bigotimes_v\hat f_v$
(local transforms for $\psi_\infty$, $\psi_v$ and the self-dual measures),
$$\sum_{\gamma\in F} f(\gamma) = \sum_{\gamma\in F}\hat f(\gamma),$$
both sums converging absolutely (`summable_adelicPoisson_factorizable_lhs`, `_rhs`).

*Proof:* expand $\prod_{v\in S}f_v$ into products of single cosets (`finprod_expand`), give each product of cosets a
global center by strong approximation (`exists_strong_approx`, `ballIndV_recenter`), and apply `adelicPoisson`
to each term (`factorizable_expansion`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), Thm. 4.2.1 (Poisson summation formula) [unverified]"]
theorem adelicPoisson_factorizable (f : SchwartzMap V ℂ) :
    ∑' γ : F, f (mixedEmbedding F γ) * ∏ᶠ v, fv v (algebraMap F (v.adicCompletion F) γ) =
      ∑' γ : F, fourierInf f (mixedEmbedding F γ) *
        ∏ᶠ v, fourierV v (fv v) (algebraMap F (v.adicCompletion F) γ) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion fv S hS hout
  simp_rw [hL, hR, Finset.mul_sum]
  rw [Summable.tsum_finsetSum, Summable.tsum_finsetSum]
  · refine Finset.sum_congr rfl fun J _ => ?_
    simp_rw [mul_left_comm (f _), mul_left_comm (fourierInf f _)]
    rw [tsum_mul_left, tsum_mul_left, adelicPoisson f (ξ J) (hfinJ J)]
  · intro J _
    simp_rw [mul_left_comm (fourierInf f _)]
    exact (summable_adelicPoisson_rhs f (ξ J) (hfinJ J)).mul_left _
  · intro J _
    simp_rw [mul_left_comm (f _)]
    exact (summable_adelicPoisson_lhs f (ξ J) (hfinJ J)).mul_left _

include hS hout in
/-- The left side of `adelicPoisson_factorizable` converges absolutely. -/
theorem summable_adelicPoisson_factorizable_lhs (f : SchwartzMap V ℂ) :
    Summable fun γ : F => f (mixedEmbedding F γ) * ∏ᶠ v, fv v (algebraMap F (v.adicCompletion F) γ) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion fv S hS hout
  simp_rw [hL, Finset.mul_sum]
  refine summable_sum fun J _ => ?_
  simp_rw [mul_left_comm (f _)]
  exact (summable_adelicPoisson_lhs f (ξ J) (hfinJ J)).mul_left _

include hS hout in
/-- The right side of `adelicPoisson_factorizable` converges absolutely. -/
theorem summable_adelicPoisson_factorizable_rhs (f : SchwartzMap V ℂ) :
    Summable fun γ : F => fourierInf f (mixedEmbedding F γ) *
      ∏ᶠ v, fourierV v (fv v) (algebraMap F (v.adicCompletion F) γ) := by
  obtain ⟨ι, _, A, ξ, kJ, hfinJ, hL, hR⟩ := factorizable_expansion fv S hS hout
  simp_rw [hR, Finset.mul_sum]
  refine summable_sum fun J _ => ?_
  simp_rw [mul_left_comm (fourierInf f _)]
  exact (summable_adelicPoisson_rhs f (ξ J) (hfinJ J)).mul_left _

end Factorizable

end

end QuadFormsKB.Analysis
