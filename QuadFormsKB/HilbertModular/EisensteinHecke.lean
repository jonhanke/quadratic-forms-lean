/-
# Hilbert Eisenstein series V: the Hecke-regularized series

For a weight $W$ (unit-equivariant of parallel weight $k$), $k \ge 2$ and $s \ge 0$ put
$$H_{W,k}(z, s) = \sum_{x \in U\backslash F^2}W(x)\,\prod_v\varphi_{k,s}\big(\sigma_v(c)z_v + \sigma_v(d)\big)
  = \sum_{x}W(x)\,N(cz+d)^{-k}\,|N(cz+d)|^{-2s}\qquad(\texttt{heckeSeries}),$$
with $\varphi_{k,s}(w) = w^{-k}|w|^{-2s}$ (`phiKS`). For $s = 0$ it is $E_{W,k}$ (`heckeSeries_zero`).

* `exists_summable_bound_rpow`: **absolute convergence** for $k + 2s > 2$, uniformly on vertical strips (the balancing
  argument of `EisensteinConv.lean` with a real exponent);
* `heckeSeries_slash`: the **transformation law** $H_{W,k}(Az, s)\prod_vj(A_v, z_v)^{-k} = |N(j(A, z))|^{2s}H_{W_A,k}(z, s)$ for
  $A \in \mathrm{SL}_2(F)$ (no convergence needed). As $s \to 0$ the factor $|N(j)|^{2s} \to 1$: this is Hecke's trick.
-/
import QuadFormsKB.HilbertModular.EisensteinForms
import QuadFormsKB.HilbertModular.FourierLine

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### The summand -/

/-- **The Hecke-regularized summand** $W(x)\prod_v\varphi_{k,s}(\sigma_v(c)Z_v + \sigma_v(d))$, $x = (c, d)$. -/
noncomputable def heckeTerm (W : F × F → ℂ) (k : ℕ) (s : ℝ) (x : F × F) (Z : InfinitePlace F → ℂ) : ℂ :=
  W x * ∏ v, phiKS k s ((realEmb F v x.1 : ℂ) * Z v + (realEmb F v x.2 : ℂ))

lemma norm_heckeTerm (W : F × F → ℂ) (k : ℕ) (s : ℝ) (x : F × F) (Z : InfinitePlace F → ℂ) :
    ‖heckeTerm W k s x Z‖ = ‖W x‖ * (‖eisDen x Z‖ ^ k)⁻¹ * ‖eisDen x Z‖ ^ (-2 * s) := by
  rw [heckeTerm, norm_mul, norm_prod, mul_assoc]
  congr 1
  simp_rw [norm_phiKS]
  rw [Finset.prod_mul_distrib, eisDen, norm_prod, ← Finset.prod_pow, ← Finset.prod_inv_distrib,
    Real.finset_prod_rpow _ _ (fun v _ => norm_nonneg _)]

/-- At $s = 0$ the Hecke summand is the Eisenstein summand. -/
lemma heckeTerm_zero (W : F × F → ℂ) (k : ℕ) (x : F × F) (Z : InfinitePlace F → ℂ) :
    heckeTerm W k 0 x Z = eisTerm W (k : ℤ) x Z := by
  rw [heckeTerm, eisTerm, eisDen]
  simp only [phiKS_zero]
  rw [Finset.prod_inv_distrib, Finset.prod_pow, _root_.zpow_neg, zpow_natCast]

lemma phiKS_mul_unit (k : ℕ) (s : ℝ) (ε : (𝓞 F)ˣ) (v : InfinitePlace F) (w : ℂ) :
    phiKS k s ((realEmb F v (ε : F) : ℂ) * w) =
      ((realEmb F v (ε : F) : ℂ) ^ k)⁻¹ * ((|realEmb F v (ε : F)| ^ (-2 * s) : ℝ) : ℂ) * phiKS k s w := by
  have h0 : algebraMap (𝓞 F) F (ε : 𝓞 F) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ε.ne_zero
  have hε : realEmb F v (ε : F) ≠ 0 := (map_ne_zero_iff _ (realEmb_injective F v)).mpr h0
  exact phiKS_real_mul k s hε w

lemma heckeTerm_smul {W : F × F → ℂ} {k : ℕ} (hW : IsUnitEquivariant W (k : ℤ)) (s : ℝ)
    (ε : (𝓞 F)ˣ) (x : F × F) (Z : InfinitePlace F → ℂ) :
    heckeTerm W k s (ε • x) Z = heckeTerm W k s x Z := by
  have hprod : ∏ v, phiKS k s ((realEmb F v (ε • x).1 : ℂ) * Z v + (realEmb F v (ε • x).2 : ℂ)) =
      ((unitNorm ε : ℂ) ^ k)⁻¹ * ∏ v, phiKS k s ((realEmb F v x.1 : ℂ) * Z v + (realEmb F v x.2 : ℂ)) := by
    have : ∀ v, (realEmb F v (ε • x).1 : ℂ) * Z v + (realEmb F v (ε • x).2 : ℂ) =
        (realEmb F v (ε : F) : ℂ) * ((realEmb F v x.1 : ℂ) * Z v + (realEmb F v x.2 : ℂ)) := by
      intro v; simp only [smul_fst, smul_snd, map_mul, ofReal_mul]; ring
    simp_rw [this, phiKS_mul_unit]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have habs : ∏ v, ((|realEmb F v (ε : F)| ^ (-2 * s) : ℝ) : ℂ) = 1 := by
      rw [← ofReal_prod, Real.finset_prod_rpow _ _ (fun v _ => abs_nonneg _), ← Finset.abs_prod]
      have := abs_unitNorm ε
      rw [unitNorm] at this
      rw [this, Real.one_rpow, ofReal_one]
    rw [habs, mul_one, unitNorm, ofReal_prod, Finset.prod_inv_distrib, Finset.prod_pow]
  rw [heckeTerm, heckeTerm, hW, hprod]
  have hu : ((unitNorm ε : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (unitNorm_ne_zero ε)
  rw [zpow_natCast]
  field_simp

lemma heckeTerm_out {W : F × F → ℂ} {k : ℕ} (hW : IsUnitEquivariant W (k : ℤ)) (s : ℝ) (x : F × F)
    (Z : InfinitePlace F → ℂ) :
    heckeTerm W k s (Quotient.mk _ x : UOrbit F).out Z = heckeTerm W k s x Z := by
  obtain ⟨ε, hε⟩ := exists_smul_out x
  rw [← hε, heckeTerm_smul hW]

/-- **The Hecke-regularized Eisenstein series** $H_{W,k}(z, s) = \sum_{x\in U\backslash F^2}W(x)N(cz+d)^{-k}|N(cz+d)|^{-2s}$. -/
@[kb "hecke1927" "Hecke's convergence trick (regularization |N(cz+d)|^{-2s}) [unverified]"]
noncomputable def heckeSeries (W : F × F → ℂ) (k : ℕ) (s : ℝ) (z : InfinitePlace F → ℍ) : ℂ :=
  ∑' o : UOrbit F, heckeTerm W k s o.out fun v => (z v : ℂ)

lemma heckeSeries_zero (W : F × F → ℂ) (k : ℕ) : heckeSeries W k 0 = eisSeries W (k : ℤ) := by
  funext z
  simp only [heckeSeries, eisSeries, eisSeriesC, heckeTerm_zero]

/-! ### Absolute convergence for $k + 2s > 2$ -/

open Classical in
/-- Summability over $I \times I$ with a real exponent: $\sum_{x\in I^2}\|x\|^{-p} < \infty$ for $p > 2d$. -/
theorem summable_eisEmb_rpow (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {p : ℝ}
    (hp : 2 * (Fintype.card (InfinitePlace F) : ℝ) < p) :
    Summable fun x : F × F =>
      if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then
        ‖eisEmb x‖ ^ (-p) else 0 := by
  set S := {x : F × F | x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}
  have heq : (fun x : F × F => if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧
      x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then ‖eisEmb x‖ ^ (-p) else 0) =
      S.indicator fun x => ‖eisEmb x‖ ^ (-p) := by
    funext x; simp [Set.indicator, S]
  rw [heq, ← summable_subtype_iff_indicator]
  set L := Submodule.span ℤ (Set.range (pairBasis I))
  have hL : Summable fun y : L => ‖y‖ ^ (-p) := by
    refine ZLattice.summable_norm_rpow L (-p) ?_
    rw [finrank_span_pairBasis]; push_cast; linarith
  have hi : Function.Injective fun x : S => (⟨eisEmb x.1, eisEmb_mem_span I x.2⟩ : L) := by
    intro x y h
    exact Subtype.ext (eisEmb_injective (congrArg Subtype.val h))
  exact (hL.comp_injective hi).congr fun x => rfl

/-- **A summable majorant for $|W(x)||N(cz+d)|^{-\sigma}$, $\sigma > 2$**, uniform on vertical strips. -/
theorem exists_summable_bound_rpow {W : F × F → ℂ} {k : ℤ} (hW : EisWeight W k) {σ : ℝ}
    (hσ : 2 < σ) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ h : UOrbit F → ℝ, Summable h ∧ ∀ z : InfinitePlace F → ℍ,
      (∀ v, z v ∈ verticalStrip A B) → ∀ o : UOrbit F,
        ‖W o.out‖ * ‖eisDen o.out fun v => (z v : ℂ)‖ ^ (-σ) ≤ h o := by
  classical
  obtain ⟨C, hC, hbal⟩ := exists_balanced F
  choose! ε hε using hbal
  obtain ⟨I, hI⟩ := hW.supp
  obtain ⟨Bw, hBw⟩ := hW.bdd
  have hBw0 : 0 ≤ Bw := (norm_nonneg _).trans (hBw 0)
  set d := Fintype.card (InfinitePlace F) with hd
  have hdpos : 0 < d := Fintype.card_pos
  set r₀ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ with hr₀
  have hr₀pos : 0 < r₀ := EisensteinSeries.r_pos _
  have hσ0 : 0 < σ := by linarith
  set g : F × F → ℝ := fun x =>
    if x.1 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) ∧ x.2 ∈ (I : FractionalIdeal (𝓞 F)⁰ F) then
      ‖eisEmb x‖ ^ (-(d * σ)) else 0 with hg
  have hgs : Summable g := summable_eisEmb_rpow I (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    nlinarith)
  set rep : UOrbit F → F × F := fun o => ε o.out • o.out
  have hrep : ∀ o, (Quotient.mk _ (rep o) : UOrbit F) = o := by
    intro o
    exact (Quotient.sound (orbitRel_iff.mpr ⟨ε o.out, rfl⟩)).trans (Quotient.out_eq o)
  have hinj : Function.Injective rep := by
    intro o o' h; rw [← hrep o, ← hrep o', h]
  set K : ℝ := (r₀ ^ d / C) ^ (-σ)
  refine ⟨fun o => Bw * K * g (rep o), (hgs.comp_injective hinj).mul_left _, fun z hz o => ?_⟩
  -- move to the balanced representative
  have hεo : ε o.out • o.out = rep o := rfl
  have hnormW : ‖W o.out‖ = ‖W (rep o)‖ := by
    rw [← hεo, hW.unit, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm,
      _root_.one_zpow, one_mul]
  have hnormD : ‖eisDen o.out fun v => (z v : ℂ)‖ = ‖eisDen (rep o) fun v => (z v : ℂ)‖ := by
    rw [← hεo, eisDen_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm, one_mul]
  rw [hnormW, hnormD]
  set x := rep o
  have hg0 : 0 ≤ g x := by simp only [hg]; split_ifs <;> positivity
  have hK0 : 0 ≤ K := by positivity
  by_cases hWx : W x = 0
  · rw [hWx, norm_zero, zero_mul]; positivity
  by_cases hx0 : x = 0
  · rw [hx0, eisDen_zero, norm_zero, Real.zero_rpow (by linarith), mul_zero]; positivity
  have hxI := hI x hWx
  have hgx : g x = ‖eisEmb x‖ ^ (-(d * σ)) := by simp only [hg, hxI, and_self, ite_true]
  have hox : o.out ≠ 0 := by
    intro h; apply hx0; simp [x, rep, h]
  have hbx : ‖eisEmb x‖ ^ d ≤ C * ∏ v, placeMax x v := hε o.out hox
  have he0 : 0 < ‖eisEmb x‖ :=
    norm_pos_iff.mpr fun h => hx0 (eisEmb_injective (h.trans (by ext v <;> simp [eisEmb, realVec])))
  have hrz : r₀ ^ d ≤ ∏ v, EisensteinSeries.r (z v) := by
    rw [show r₀ ^ d = ∏ _v : InfinitePlace F, r₀ by rw [Finset.prod_const, Finset.card_univ]]
    exact Finset.prod_le_prod₀ (fun _ _ => hr₀pos.le)
      fun v _ => EisensteinSeries.r_lower_bound_on_verticalStrip (z v) hB (hz v)
  have hlow : r₀ ^ d / C * ‖eisEmb x‖ ^ d ≤ ‖eisDen x fun v => (z v : ℂ)‖ := by
    refine le_trans ?_ (norm_eisDen_ge x z)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    refine mul_le_mul hrz ?_ (by positivity) (Finset.prod_nonneg fun _ _ => (EisensteinSeries.r_pos _).le)
    rw [div_le_iff₀ hC]; linarith
  have hlow0 : 0 < r₀ ^ d / C * ‖eisEmb x‖ ^ d := by positivity
  have hkey : ‖eisDen x fun v => (z v : ℂ)‖ ^ (-σ) ≤ (r₀ ^ d / C * ‖eisEmb x‖ ^ d) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hlow0 hlow (by linarith)
  have heq : (r₀ ^ d / C * ‖eisEmb x‖ ^ d) ^ (-σ) = K * ‖eisEmb x‖ ^ (-(d * σ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      show ‖eisEmb x‖ ^ d = ‖eisEmb x‖ ^ (d : ℝ) from (Real.rpow_natCast _ _).symm,
      ← Real.rpow_mul he0.le, show (d : ℝ) * -σ = -(d * σ) by ring]
  show ‖W x‖ * ‖eisDen x fun v => (z v : ℂ)‖ ^ (-σ) ≤ Bw * K * g x
  rw [hgx, mul_assoc, ← heq]
  exact mul_le_mul (hBw x) hkey (by positivity) hBw0

/-- **Absolute convergence of the Hecke series** for $k + 2s > 2$, uniformly on vertical strips: a summable majorant for
the norms of the terms. -/
theorem exists_summable_bound_hecke {W : F × F → ℂ} {k : ℕ} (hW : EisWeight W (k : ℤ)) {s : ℝ}
    (hks : 2 < (k : ℝ) + 2 * s) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ h : UOrbit F → ℝ, Summable h ∧ ∀ z : InfinitePlace F → ℍ,
      (∀ v, z v ∈ verticalStrip A B) → ∀ o : UOrbit F,
        ‖heckeTerm W k s o.out fun v => (z v : ℂ)‖ ≤ h o := by
  obtain ⟨h, hs, hb⟩ := exists_summable_bound_rpow hW hks A hB
  refine ⟨h, hs, fun z hz o => ?_⟩
  have hb' := hb z hz o
  rw [norm_heckeTerm, mul_assoc]
  by_cases h0 : ‖eisDen o.out fun v => (z v : ℂ)‖ = 0
  · have hz0 : ((‖eisDen o.out fun v => (z v : ℂ)‖ ^ k)⁻¹ * ‖eisDen o.out fun v => (z v : ℂ)‖ ^ (-2 * s)) = 0 := by
      rw [h0]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        have : -2 * s ≠ 0 := by push_cast at hks; intro h; linarith
        rw [Real.zero_rpow this, mul_zero]
      · rw [zero_pow hk.ne', _root_.inv_zero, zero_mul]
    rw [hz0, mul_zero]
    exact (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)).trans hb'
  refine le_trans (le_of_eq ?_) hb'
  congr 1
  · have hpos : 0 < ‖eisDen o.out fun v => (z v : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
    congr 1; ring

/-! ### The transformation law -/

lemma phiKS_div (k : ℕ) (s : ℝ) {w j : ℂ} (hj : j ≠ 0) :
    phiKS k s (w / j) = (j ^ k) * ((‖j‖ ^ (2 * s) : ℝ) : ℂ) * phiKS k s w := by
  have hjn : 0 < ‖j‖ := norm_pos_iff.mpr hj
  rw [phiKS, phiKS, div_pow, inv_div, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  have h1 : ‖j‖ ^ (-2 * s) = (‖j‖ ^ (2 * s))⁻¹ := by
    rw [show -2 * s = -(2 * s) by ring, Real.rpow_neg (norm_nonneg _)]
  rw [h1, div_inv_eq_mul, ofReal_mul]
  have hjk : j ^ k ≠ 0 := pow_ne_zero _ hj
  rw [div_eq_mul_inv]; ring

/-- **The transformation law of the Hecke series**: for $A \in \mathrm{SL}_2(F)$,
$H_{W,k}(Az, s)\prod_vj(A_v, z_v)^{-k} = \prod_v|j(A_v, z_v)|^{2s}\cdot H_{W_A,k}(z, s)$. -/
theorem heckeSeries_smul {W : F × F → ℂ} {k : ℕ} (hW : IsUnitEquivariant W (k : ℤ)) (s : ℝ)
    (A : SL(2, F)) (z : InfinitePlace F → ℍ) :
    heckeSeries W k s (slHom (realEmb F) A • z) *
        ∏ v, (denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ k)⁻¹ =
      (∏ v, ((‖denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)‖ ^ (2 * s) : ℝ) : ℂ)) *
        heckeSeries (slashWeight W A) k s z := by
  rw [heckeSeries, heckeSeries, ← tsum_mul_right, ← tsum_mul_left]
  have hW' := hW.slashWeight A
  have hterm : ∀ o : UOrbit F,
      heckeTerm W k s o.out (fun v => (((slHom (realEmb F) A • z) v : ℍ) : ℂ)) *
        ∏ v, (denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ k)⁻¹ =
      (∏ v, ((‖denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)‖ ^ (2 * s) : ℝ) : ℂ)) *
        heckeTerm (slashWeight W A) k s (orbitMulEquiv A o).out fun v => (z v : ℂ) := by
    intro o
    conv_rhs => rw [← Quotient.out_eq o, orbitMulEquiv_mk, heckeTerm_out hW']
    rw [heckeTerm, heckeTerm, slashWeight, rowMul_rowMul_inv]
    -- one place at a time
    have hplace : ∀ v, phiKS k s ((realEmb F v (o.out).1 : ℂ) *
        (((slHom (realEmb F) A • z) v : ℍ) : ℂ) + (realEmb F v (o.out).2 : ℂ)) *
        (denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ k)⁻¹ =
        ((‖denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)‖ ^ (2 * s) : ℝ) : ℂ) *
          phiKS k s ((realEmb F v (rowMul o.out A).1 : ℂ) * (z v : ℂ) +
            (realEmb F v (rowMul o.out A).2 : ℂ)) := by
      intro v
      set j := denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)
      have hj : j ≠ 0 := denom_ne_zero _ _
      have hrow : (realEmb F v (o.out).1 : ℂ) * (((slHom (realEmb F) A • z) v : ℍ) : ℂ) +
          (realEmb F v (o.out).2 : ℂ) = ((realEmb F v (rowMul o.out A).1 : ℂ) * (z v : ℂ) +
            (realEmb F v (rowMul o.out A).2 : ℂ)) / j := by
        rw [eq_div_iff hj]
        have := eisDen_smul_mul (o.out) A z
        rw [Pi.smul_apply', glPos_smul_eq, coe_smul_of_det_pos (det_glPos_pos _)]
        have key : ∀ c d n D : ℂ, D ≠ 0 → (c * (n / D) + d) * D = c * n + d * D := by
          intro c d n D hD; field_simp
        rw [key _ _ _ _ hj]
        simp only [j, num, denom, slHom_apply_coe, rowMul, map_add, map_mul, ofReal_add, ofReal_mul]
        ring
      rw [hrow, phiKS_div k s hj]
      have hjk : j ^ k ≠ 0 := pow_ne_zero _ hj
      field_simp
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    simp_rw [hplace]
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hterm]
  exact (orbitMulEquiv A).tsum_eq fun o => (∏ v, ((‖denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) :
    GL (Fin 2) ℝ) (z v)‖ ^ (2 * s) : ℝ) : ℂ)) * heckeTerm (slashWeight W A) k s o.out fun v => (z v : ℂ)

end QuadFormsKB.HilbertModular
