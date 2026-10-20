/-
# Hilbert Eisenstein series VIII: parallel weight 2 by Hecke's trick, $d \ge 2$

For an integral weight $W$ of weight $2$ (`IntWeight W 2 𝔐`) and $[F:\mathbb{Q}] = d \ge 2$:
$$E_{W,2}(z) := \lim_{s\to0^+}H_{W,2}(z, s) = \lim_{s\to0^+}\sum_{U\backslash F^2}W(c,d)N(cz+d)^{-2}|N(cz+d)|^{-2s}$$
exists (`tendsto_heckeSeries_two`) and equals the **holomorphic** series
$$\mathrm{c}_\infty(W) + \sum_{t\ne0}\sum_{\nu}c_{\mathfrak M}R_W(\tilde t, \nu)\prod_vT_{2,0}(\nu_v, \sigma_v(\tilde t)y_v)\,e\Big(\sum_v\nu_v\sigma_v(\tilde t)x_v\Big)
  \qquad(\texttt{eis2})$$
(the $s = 0$ Fourier expansion; every term is $e(\operatorname{Tr}\mu z)$ with $\mu \gg 0$, `rowCoeff_zero_eq`). **There is no
non-holomorphic correction for $d \ge 2$**: the $\nu = 0$ terms of $H_{W,2}(z, s)$ are
$\prod_vT_{2,s}(0, h_v) = O(s^d)\prod_v|h_v|^{-1-2s}$ (`norm_lineFT_two_zero_le`), and
$\sum_{t}|N\tilde t|^{-1-2s} = O(1/s)$ (balanced representatives + `ZLattice.tsum_norm_rpow_le`), so they contribute
$O(s^{d-1}) \to 0$. For $d = 1$ they contribute the classical $-\pi/y$ term instead (cf. `EisensteinWt2` over $\mathbb{Q}$,
where it is removed by a mass-zero condition). The terms with $\nu \ne 0$ converge by dominated convergence: each is
bounded uniformly in $s \in [0,1]$ by $e^{-\pi|\nu_v||h_v|}$-decay (`norm_lineFT_le`).

Sources: Hecke (1927) [unverified]; Shimura (Duke 1978), §3, Prop. 3.4 (the case $k = 2$) [unverified]; Garrett (1990),
Ch. 3 [unverified]; Freitag (1990), Ch. I §5 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinQExp

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory Set
open scoped MatrixGroups ModularForm nonZeroDivisors Real Nat

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Elementary estimates -/

/-- $\sum_{k\ge0}k^{-1-\varepsilon} \le 1 + 1/\varepsilon$ (the $k = 0$ term is $0$). -/
lemma tsum_nat_rpow_neg_le {ε : ℝ} (hε : 0 < ε) :
    Summable (fun k : ℕ => (k : ℝ) ^ (-1 - ε)) ∧ ∑' k : ℕ, (k : ℝ) ^ (-1 - ε) ≤ 1 + 1 / ε := by
  have hs : Summable fun k : ℕ => (k : ℝ) ^ (-1 - ε) := by
    have := Real.summable_nat_rpow.mpr (show -1 - ε < -1 by linarith)
    exact this
  refine ⟨hs, ?_⟩
  set g : ℝ → ℝ := fun x => (x + 1) ^ (-1 - ε)
  have hanti : AntitoneOn g (Ici 0) := by
    intro x hx y hy hxy
    have hx' : (0 : ℝ) ≤ x := hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  -- the antiderivative `G(x) = -(x+1)^{-ε}/ε`
  set G : ℝ → ℝ := fun x => -((x + 1) ^ (-ε)) / ε
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt G (g x) x := by
    intro x hx
    have hx' : (0 : ℝ) < x + 1 := by have : (0 : ℝ) ≤ x := hx; linarith
    have h1 := ((hasDerivAt_id x).add_const 1).rpow_const (p := -ε) (Or.inl hx'.ne')
    have h2 := (h1.neg).div_const ε
    convert h2 using 1
    · funext y; simp [G]
    · simp only [g, id, one_mul]
      rw [show -1 - ε = -ε - 1 by ring]
      field_simp
  have hG : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (x + 1) ^ (-ε)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hε).comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
    have := (h1.neg.div_const ε)
    simpa [G] using this
  have hgnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ g x := fun x hx => by
    have : (0 : ℝ) < x := hx
    exact Real.rpow_nonneg (by linarith) _
  have hint : IntegrableOn g (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hgnn hG
  have hval : ∫ x in Ioi (0 : ℝ), g x = 1 / ε := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hG]
    simp [G]; field_simp
  have hle := hanti.tsum_le_integral hint hgnn
  have hshift : ∑' k : ℕ, (k : ℝ) ^ (-1 - ε) = ∑' k : ℕ, g k := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, g, Nat.cast_add, Nat.cast_one]
    rw [Real.zero_rpow (by linarith), zero_add]
  rw [hshift]
  refine hle.trans (le_of_eq ?_)
  rw [hval]; simp [g]

/-- **Algebraic integers have norm $\ge 1$**: $\prod_v|\sigma_v(x)| \ge 1$ for $x \in \mathcal{O}_F \setminus 0$. -/
lemma one_le_prod_abs_realEmb {x : 𝓞 F} (hx : x ≠ 0) :
    1 ≤ ∏ v, |realEmb F v (algebraMap (𝓞 F) F x)| := by
  have h := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 F) F x)
  have hm : ∀ v : InfinitePlace F, v.mult = 1 := fun v => mult_eq_one_of_totallyReal v
  simp only [hm, pow_one] at h
  simp_rw [abs_realEmb]
  rw [h]
  have hn : Algebra.norm ℚ (algebraMap (𝓞 F) F x) = ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [← Algebra.coe_norm_int]
  rw [hn]
  have hn0 : (Algebra.norm ℤ x : ℤ) ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hn0
  push_cast
  exact_mod_cast this

/-- Nonzero dual vectors have $\ell^1$-norm $\ge \rho > 0$. -/
lemma exists_l1_dualVec_ge {J : Type*} [Fintype J] (b : Module.Basis J ℝ (InfinitePlace F → ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : J → ℤ, n ≠ 0 → ρ ≤ l1 (dualVec b n) := by
  set C := ∑ j, l1 (b j) + 1
  have hC : 0 < C := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => l1_nonneg (b j); linarith
  refine ⟨1 / C, by positivity, fun n hn => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h; push Not at h; exact hn (funext h)
  have h1 : (1 : ℝ) ≤ |(n j : ℝ)| := by
    have := Int.one_le_abs hj; exact_mod_cast this
  have h2 : |(n j : ℝ)| ≤ l1 (dualVec b n) * l1 (b j) := by
    rw [← pair_dualVec b n j]; exact abs_pair_le _ _
  have h3 : l1 (b j) ≤ C := by
    have := Finset.single_le_sum (f := fun j => l1 (b j)) (fun j _ => l1_nonneg _) (Finset.mem_univ j)
    linarith
  rw [div_le_iff₀ hC]
  nlinarith [l1_nonneg (dualVec b n)]

/-! ### Balanced representatives: size bounds -/

/-- $P(c) = \prod_v|\sigma_v(c)| = |N(c)|$. -/
noncomputable def absNorm (c : F) : ℝ := ∏ v, |realEmb F v c|

lemma absNorm_pos {c : F} (hc : c ≠ 0) : 0 < absNorm c :=
  Finset.prod_pos fun v _ => abs_pos.mpr ((map_ne_zero_iff _ (realEmb_injective F v)).mpr hc)

/-- For a balanced representative: $\|\sigma(\tilde t)\|^d \le C\,P(\tilde t)$. -/
lemma norm_realVec_crep_pow_le {t : UOrbitF F} (ht : t.out ≠ 0) :
    ‖realVec (crep t)‖ ^ Fintype.card (InfinitePlace F) ≤ balConst F * absNorm (crep t) := by
  obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image Finset.univ (fun v => |realEmb F v (crep t)|)
    Finset.univ_nonempty
  have hn : ‖realVec (crep t)‖ ≤ |realEmb F v₀ (crep t)| := by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun v => ?_
    simpa [realVec, Real.norm_eq_abs] using hv₀ v (Finset.mem_univ v)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn _).trans (crep_balanced ht v₀)

/-- For a balanced representative: $P(\tilde t) \le C^{d-1}|\sigma_v\tilde t|^d$ for every $v$. -/
lemma absNorm_le_pow_crep {t : UOrbitF F} (ht : t.out ≠ 0) (v : InfinitePlace F) :
    absNorm (crep t) ≤ balConst F ^ (Fintype.card (InfinitePlace F) - 1) *
      |realEmb F v (crep t)| ^ Fintype.card (InfinitePlace F) := by
  classical
  set d := Fintype.card (InfinitePlace F)
  set P := absNorm (crep t)
  have hc : crep t ≠ 0 := (crep_eq_zero_iff t).not.mpr ht
  have hP : 0 < P := absNorm_pos hc
  have hC := balConst_pos (F := F)
  -- `P^d = |σ_v|^d ∏_{w ≠ v} |σ_w|^d ≤ |σ_v|^d (CP)^{d-1}`
  have h1 : P ^ d = |realEmb F v (crep t)| ^ d * ∏ w ∈ Finset.univ.erase v, |realEmb F w (crep t)| ^ d := by
    rw [show P = ∏ w, |realEmb F w (crep t)| from rfl, ← Finset.prod_pow,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
  have h2 : ∏ w ∈ Finset.univ.erase v, |realEmb F w (crep t)| ^ d ≤ (balConst F * P) ^ (d - 1) := by
    calc ∏ w ∈ Finset.univ.erase v, |realEmb F w (crep t)| ^ d
        ≤ ∏ _w ∈ Finset.univ.erase v, balConst F * P :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity) fun w _ => crep_balanced ht w
      _ = (balConst F * P) ^ (d - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  have h3 : P ^ d ≤ |realEmb F v (crep t)| ^ d * (balConst F * P) ^ (d - 1) := by
    rw [h1]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hd : 1 ≤ d := Fintype.card_pos
  have h4 : P ^ d = P * P ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  rw [h4, mul_pow] at h3
  have h5 : P * P ^ (d - 1) ≤ (balConst F ^ (d - 1) * |realEmb F v (crep t)| ^ d) * P ^ (d - 1) := by
    linarith [h3]
  exact le_of_mul_le_mul_right h5 (pow_pos hP _)

/-- The lattice $\sigma(\mathcal{O}_F) \subset \mathbb{R}^d$, the $\mathbb{Z}$-span of the lattice basis of $(1)$. -/
noncomputable abbrev intLatF (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Submodule ℤ (InfinitePlace F → ℝ) :=
  Submodule.span ℤ (Set.range (koecherBasis (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)))

lemma finrank_intLatF : Module.finrank ℤ (intLatF F) = Fintype.card (InfinitePlace F) := by
  rw [finrank_span_eq_card ((koecherBasis _).linearIndependent.restrict_scalars' ℤ), Fintype.card_fin,
    card_infinitePlace_eq_finrank]

lemma realVec_mem_intLatF (x : 𝓞 F) : realVec (algebraMap (𝓞 F) F x) ∈ intLatF F :=
  realVec_mem_span 1 ((FractionalIdeal.mem_one_iff _).mpr ⟨x, rfl⟩)

/-- $t \in U\backslash\mathcal{O}_F$ (an orbit of algebraic integers). -/
def IsIntOrbit (t : UOrbitF F) : Prop := ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = t.out

lemma crep_int {t : UOrbitF F} (ht : IsIntOrbit t) : ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = crep t := by
  obtain ⟨x, hx⟩ := ht
  refine ⟨((exists_crep_unit t).choose : 𝓞 F) * x, ?_⟩
  rw [map_mul, hx]; rfl

lemma crep_injective : Function.Injective (crep (F := F)) := by
  intro t t' h; rw [← crep_mk t, ← crep_mk t', h]

/-! ### The sum $\sum_t|N\tilde t|^{-1-2s} = O(1/s)$ -/

/-- Integral nonzero orbits. -/
abbrev IntOrbits (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :=
  {t : UOrbitF F // IsIntOrbit t ∧ t.out ≠ 0}

/-- The lattice point of an integral orbit. -/
noncomputable def latPt (t : IntOrbits F) : intLatF F :=
  ⟨realVec (crep t.1), by
    obtain ⟨x, hx⟩ := crep_int t.2.1
    rw [← hx]; exact realVec_mem_intLatF x⟩

lemma latPt_injective : Function.Injective (latPt (F := F)) := by
  intro t t' h
  have h1 : realVec (crep t.1) = realVec (crep t'.1) := congrArg Subtype.val h
  exact Subtype.ext (crep_injective (realVec_injective h1))

lemma latPt_ne_zero (t : IntOrbits F) : latPt t ≠ 0 := by
  intro h
  have h1 : realVec (crep t.1) = 0 := congrArg Subtype.val h
  have : crep t.1 = 0 := realVec_injective (h1.trans (by funext v; simp [realVec]))
  exact t.2.2 ((crep_eq_zero_iff _).mp this)

lemma norm_latPt (t : IntOrbits F) : ‖latPt t‖ = ‖realVec (crep t.1)‖ := rfl

lemma rpow_le_max {A r : ℝ} (hA : 0 < A) {lo hi : ℝ} (h1 : lo ≤ r) (h2 : r ≤ hi) :
    A ^ r ≤ max (A ^ lo) (A ^ hi) := by
  rcases le_or_gt 1 A with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le h h2).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge hA h.le h1).trans (le_max_left _ _)

/-- **The key estimate for Hecke's trick**: there is $K$ with
$\sum_{t\in U\backslash(\mathcal{O}_F\setminus0)}|N\tilde t|^{-1-2s} \le K(1 + 1/s)$ for $0 < s \le 1$. -/
theorem exists_tsum_absNorm_le : ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
    Summable (fun t : IntOrbits F => absNorm (crep t.1) ^ (-(1 + 2 * s))) ∧
      ∑' t : IntOrbits F, absNorm (crep t.1) ^ (-(1 + 2 * s)) ≤ K * (1 + 1 / s) := by
  set d := Fintype.card (InfinitePlace F)
  have hd : 1 ≤ d := Fintype.card_pos
  set L := intLatF F
  set A := ZLattice.tsumNormRPowBound L
  have hA : 0 < A := ZLattice.tsumNormRPowBound_pos L
  set C := balConst F
  have hC : 0 < C := balConst_pos
  set K := max (C ^ (1 : ℝ)) (C ^ (3 : ℝ)) * max (A ^ (-(3 * d : ℝ))) (A ^ (-(d : ℝ)))
  refine ⟨K, by positivity, fun s hs0 hs1 => ?_⟩
  set r : ℝ := -(d * (1 + 2 * s))
  have hr : r < -Module.finrank ℤ L := by
    rw [finrank_intLatF]; simp only [r]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hLs : Summable fun y : L => ‖y‖ ^ r := ZLattice.summable_norm_rpow L r hr
  -- the pointwise bound
  have hpt : ∀ t : IntOrbits F, absNorm (crep t.1) ^ (-(1 + 2 * s)) ≤
      C ^ (1 + 2 * s) * ‖latPt t‖ ^ r := by
    intro t
    have hc : crep t.1 ≠ 0 := (crep_eq_zero_iff _).not.mpr t.2.2
    have hP := absNorm_pos hc
    have hx0 : 0 < ‖latPt t‖ := norm_pos_iff.mpr (latPt_ne_zero t)
    have hb := norm_realVec_crep_pow_le t.2.2
    rw [← norm_latPt] at hb
    -- `P ≥ ‖x‖^d / C`
    have hlow : ‖latPt t‖ ^ d / C ≤ absNorm (crep t.1) := by rw [div_le_iff₀ hC, mul_comm]; exact hb
    have hlow0 : 0 < ‖latPt t‖ ^ d / C := by positivity
    calc absNorm (crep t.1) ^ (-(1 + 2 * s)) ≤ (‖latPt t‖ ^ d / C) ^ (-(1 + 2 * s)) :=
          Real.rpow_le_rpow_of_nonpos hlow0 hlow (by linarith)
      _ = C ^ (1 + 2 * s) * ‖latPt t‖ ^ r := by
          rw [Real.div_rpow (by positivity) hC.le, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
            Real.rpow_neg hC.le, div_inv_eq_mul]
          simp only [r]; ring_nf
  have hsum : Summable fun t : IntOrbits F => absNorm (crep t.1) ^ (-(1 + 2 * s)) := by
    refine ((hLs.comp_injective latPt_injective).mul_left (C ^ (1 + 2 * s))).of_nonneg_of_le
      (fun t => Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _) hpt
  refine ⟨hsum, ?_⟩
  calc ∑' t : IntOrbits F, absNorm (crep t.1) ^ (-(1 + 2 * s))
      ≤ ∑' t : IntOrbits F, C ^ (1 + 2 * s) * ‖latPt t‖ ^ r :=
        hsum.tsum_le_tsum hpt ((hLs.comp_injective latPt_injective).mul_left _)
    _ = C ^ (1 + 2 * s) * ∑' t : IntOrbits F, ‖latPt t‖ ^ r := tsum_mul_left
    _ ≤ C ^ (1 + 2 * s) * ∑' y : L, ‖y‖ ^ r := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (hLs.comp_injective latPt_injective).tsum_le_tsum_of_inj latPt latPt_injective
          (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) (fun _ => le_rfl) hLs
    _ ≤ C ^ (1 + 2 * s) * (A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r)) :=
        mul_le_mul_of_nonneg_left (ZLattice.tsum_norm_rpow_le L r hr) (by positivity)
    _ ≤ K * (1 + 1 / s) := by
        have hexp : (Module.finrank ℤ L : ℝ) - 1 + r = -1 - 2 * d * s := by
          rw [finrank_intLatF]; simp only [r]; ring
        rw [hexp]
        have hz := (tsum_nat_rpow_neg_le (ε := 2 * d * s) (by positivity)).2
        rw [show -1 - 2 * (d : ℝ) * s = -1 - 2 * d * s from rfl] at hz
        have hz' : ∑' k : ℕ, (k : ℝ) ^ (-1 - 2 * (d : ℝ) * s) ≤ 1 + 1 / s := by
          refine hz.trans ?_
          have : 1 / (2 * (d : ℝ) * s) ≤ 1 / s := by
            apply one_div_le_one_div_of_le hs0
            have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith
          linarith
        have hCb : C ^ (1 + 2 * s) ≤ max (C ^ (1 : ℝ)) (C ^ (3 : ℝ)) := rpow_le_max hC (by linarith) (by linarith)
        have hAb : A ^ r ≤ max (A ^ (-(3 * d : ℝ))) (A ^ (-(d : ℝ))) := by
          refine rpow_le_max hA ?_ ?_
          · simp only [r]
            have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith
          · simp only [r]
            have : (0 : ℝ) ≤ d := by positivity
            nlinarith
        have hz0 : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (-1 - 2 * (d : ℝ) * s) :=
          tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc C ^ (1 + 2 * s) * (A ^ r * ∑' k : ℕ, (k : ℝ) ^ (-1 - 2 * (d : ℝ) * s))
            ≤ max (C ^ (1 : ℝ)) (C ^ (3 : ℝ)) * (max (A ^ (-(3 * d : ℝ))) (A ^ (-(d : ℝ))) * (1 + 1 / s)) := by
              gcongr
          _ = K * (1 + 1 / s) := by ring

/-- $\sum_{y\in\sigma(\mathcal{O}_F)}e^{-a\|y\|} < \infty$ for $a > 0$. -/
lemma summable_exp_neg_norm_intLatF {a : ℝ} (ha : 0 < a) :
    Summable fun y : intLatF F => Real.exp (-a * ‖y‖) := by
  classical
  set d := Fintype.card (InfinitePlace F)
  set L := intLatF F
  have hr : (-(d + 1 : ℝ)) < -Module.finrank ℤ L := by rw [finrank_intLatF]; linarith
  have hLs := ZLattice.summable_norm_rpow L (-(d + 1 : ℝ)) hr
  set K := ((d + 1).factorial : ℝ) * a⁻¹ ^ (d + 1)
  have hbound : ∀ y : L, Real.exp (-a * ‖y‖) ≤ K * ‖y‖ ^ (-(d + 1 : ℝ)) + if y = 0 then 1 else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp only [norm_zero, mul_zero, Real.exp_zero, ↓reduceIte]
      have : (0 : ℝ) ≤ K * (0 : ℝ) ^ (-(d + 1 : ℝ)) := by positivity
      linarith
    · simp only [hy, ↓reduceIte, add_zero]
      have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h1 := Real.pow_div_factorial_le_exp (x := a * ‖y‖) (by positivity) (d + 1)
      rw [show -a * ‖y‖ = -(a * ‖y‖) by ring, Real.exp_neg]
      have hpos : 0 < (a * ‖y‖) ^ (d + 1) / ((d + 1).factorial : ℝ) := by positivity
      calc (Real.exp (a * ‖y‖))⁻¹ ≤ ((a * ‖y‖) ^ (d + 1) / ((d + 1).factorial : ℝ))⁻¹ :=
            inv_anti₀ hpos h1
        _ = K * ‖y‖ ^ (-(d + 1 : ℝ)) := by
            rw [Real.rpow_neg hy0.le, show ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
              Real.rpow_natCast]
            simp only [K]
            rw [mul_pow, inv_pow]
            field_simp
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hbound ?_
  refine (hLs.mul_left K).add ?_
  exact summable_of_ne_finset_zero (s := {0}) fun y hy => by
    simp only [Finset.mem_singleton] at hy; simp [hy]

/-! ### Bounds for the row coefficients, uniform in $s \in [0, 1]$ -/

lemma norm_rowR_le {W : F × F → ℂ} {k : ℤ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W k 𝔐) {B : ℝ}
    (hB : ∀ x, ‖W x‖ ≤ B) (c : F) (ν : InfinitePlace F → ℝ) :
    ‖rowR W 𝔐 c ν‖ ≤ Nat.card (𝓞 F ⧸ 𝔐) * B := by
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔐 hW.ne
  let _ : Fintype (𝓞 F ⧸ 𝔐) := Fintype.ofFinite _
  rw [rowR, finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le _ _).trans ?_
  rw [Fintype.card, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_mul, show (2 * π * Complex.I * (pair ν (realVec (algebraMap (𝓞 F) F (Quotient.out r))) : ℂ)) =
    ((2 * π * pair ν (realVec (algebraMap (𝓞 F) F (Quotient.out r))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hB _

lemma rowR_eq_zero_of_not_int {W : F × F → ℂ} {k : ℤ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W k 𝔐)
    {c : F} (hc : ¬ ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = c) (ν : InfinitePlace F → ℝ) :
    rowR W 𝔐 c ν = 0 := by
  rw [rowR]
  refine finsum_eq_zero_of_forall_eq_zero fun r => ?_
  have : W (c, algebraMap (𝓞 F) F (Quotient.out r)) = 0 := by
    by_contra h
    obtain ⟨p, hp⟩ := hW.supp _ h
    exact hc ⟨p.1, congrArg Prod.fst hp⟩
  rw [this, zero_mul]

lemma not_isIntOrbit_crep {t : UOrbitF F} (ht : ¬ IsIntOrbit t) :
    ¬ ∃ x : 𝓞 F, algebraMap (𝓞 F) F x = crep t := by
  rintro ⟨x, hx⟩
  apply ht
  refine ⟨(((exists_crep_unit t).choose⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * x, ?_⟩
  rw [map_mul, hx, crep, ← mul_assoc]
  rw [show algebraMap (𝓞 F) F (((exists_crep_unit t).choose⁻¹ : (𝓞 F)ˣ) : 𝓞 F) *
      ((exists_crep_unit t).choose : F) = 1 by
    rw [show ((exists_crep_unit t).choose : F) = algebraMap (𝓞 F) F ((exists_crep_unit t).choose : 𝓞 F) from rfl,
      ← map_mul, Units.inv_mul, map_one], one_mul]

/-- $\|\sigma(\tilde t)\| \ge 1$ for integral nonzero orbits, and $|\sigma_v\tilde t| \ge \|\sigma(\tilde t)\|/C$. -/
lemma crep_place_bounds (t : IntOrbits F) :
    1 ≤ ‖latPt t‖ ∧ ∀ v, ‖latPt t‖ / balConst F ≤ |realEmb F v (crep t.1)| := by
  set d := Fintype.card (InfinitePlace F)
  have hd : 1 ≤ d := Fintype.card_pos
  obtain ⟨x, hx⟩ := crep_int t.2.1
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx
    exact t.2.2 ((crep_eq_zero_iff _).mp hx.symm)
  have hP1 : 1 ≤ absNorm (crep t.1) := by rw [← hx]; exact one_le_prod_abs_realEmb hx0
  have hnorm : ∀ v, |realEmb F v (crep t.1)| ≤ ‖latPt t‖ := fun v => by
    rw [norm_latPt]; simpa [realVec, Real.norm_eq_abs] using norm_le_pi_norm (realVec (crep t.1)) v
  have hPle : absNorm (crep t.1) ≤ ‖latPt t‖ ^ d := by
    rw [absNorm, show ‖latPt t‖ ^ d = ∏ _v : InfinitePlace F, ‖latPt t‖ by
      rw [Finset.prod_const, Finset.card_univ]]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun v _ => hnorm v
  have h1 : 1 ≤ ‖latPt t‖ := by
    by_contra h
    push Not at h
    have : ‖latPt t‖ ^ d < 1 := pow_lt_one₀ (norm_nonneg _) h (by omega)
    linarith
  refine ⟨h1, fun v => ?_⟩
  have hC := balConst_pos (F := F)
  have hb := norm_realVec_crep_pow_le t.2.2
  have hb2 := absNorm_le_pow_crep t.2.2 v
  rw [← norm_latPt] at hb
  have h3 : ‖latPt t‖ ^ d ≤ balConst F ^ d * |realEmb F v (crep t.1)| ^ d := by
    calc ‖latPt t‖ ^ d ≤ balConst F * absNorm (crep t.1) := hb
      _ ≤ balConst F * (balConst F ^ (d - 1) * |realEmb F v (crep t.1)| ^ d) :=
          mul_le_mul_of_nonneg_left hb2 hC.le
      _ = balConst F ^ d * |realEmb F v (crep t.1)| ^ d := by
          rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hd]
  have h4 : (‖latPt t‖ / balConst F) ^ d ≤ |realEmb F v (crep t.1)| ^ d := by
    rw [div_pow, div_le_iff₀ (pow_pos hC d)]; linarith [mul_comm (balConst F ^ d) (|realEmb F v (crep t.1)| ^ d)]
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) (by omega)).mp h4

lemma rowCoeff_eq_zero_of_not_int {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) (s : ℝ)
    {t : UOrbitF F} (ht : ¬ IsIntOrbit t) (z : InfinitePlace F → ℍ) (n : Fin (Module.finrank ℚ F) → ℤ) :
    rowCoeff W 𝔐 hW.ne 2 s (crep t) z n = 0 := by
  rw [rowCoeff, rowR_eq_zero_of_not_int hW (not_isIntOrbit_crep ht), mul_zero, zero_mul, zero_mul]

lemma norm_cexp_two_pi_I_real (r : ℝ) : ‖cexp (2 * π * Complex.I * (r : ℂ))‖ = 1 := by
  rw [show (2 * π * Complex.I * (r : ℂ)) = ((2 * π * r : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Uniform bound for the terms $\nu \ne 0$** ($0 \le s \le 1$, $\operatorname{Im}z_v \ge y_0$):
$|\texttt{rowCoeff}(\tilde t, n)| \le K\,e^{-a_1\|\nu_n\|_1}e^{-a_2\|\sigma(\tilde t)\|}$. -/
theorem norm_rowCoeff_two_le {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {y₀ : ℝ}
    (hy₀ : 0 < y₀) : ∃ K₀ a₁ a₂ : ℝ, 0 ≤ K₀ ∧ 0 < a₁ ∧ 0 < a₂ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ z : InfinitePlace F → ℍ, (∀ v, y₀ ≤ (z v).im) → ∀ (t : IntOrbits F)
        (n : Fin (Module.finrank ℚ F) → ℤ), n ≠ 0 →
          ‖rowCoeff W 𝔐 hW.ne 2 s (crep t.1) z n‖ ≤
            K₀ * Real.exp (-a₁ * l1 (dualVec (levelBasis 𝔐 hW.ne) n)) * Real.exp (-a₂ * ‖latPt t‖) := by
  obtain ⟨B, hB⟩ := hW.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨ρ, hρ, hρn⟩ := exists_l1_dualVec_ge (levelBasis 𝔐 hW.ne)
  set C := balConst F
  have hC : 0 < C := balConst_pos
  set h₀ := y₀ / C
  have hh₀ : 0 < h₀ := div_pos hy₀ hC
  set C₂ := (2 : ℝ) ^ 2 * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)
  have hC₂ : 0 ≤ C₂ := by
    have : 0 ≤ ∫ u : ℝ, (1 + u ^ 2)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  set M₀ := h₀⁻¹ * max 1 (h₀ ^ 2)⁻¹ * C₂
  set d := Fintype.card (InfinitePlace F)
  set Kl := (latConst (levelBasis 𝔐 hW.ne) : ℝ)
  refine ⟨Kl * (Nat.card (𝓞 F ⧸ 𝔐) * B) * M₀ ^ d * Real.exp (π * y₀ * ρ / C), π * y₀ / C,
    π * y₀ * ρ / C, by positivity, by positivity, by positivity, fun s hs0 hs1 z hz t n hn => ?_⟩
  set c := crep t.1
  set ν := dualVec (levelBasis 𝔐 hW.ne) n
  obtain ⟨hx1, hplace⟩ := crep_place_bounds t
  set X := ‖latPt t‖
  have hhv : ∀ v, X / C * y₀ ≤ |realEmb F v c * (z v).im| := by
    intro v
    rw [abs_mul, abs_of_pos (z v).im_pos]
    exact mul_le_mul (hplace v) (hz v) hy₀.le (abs_nonneg _)
  have hh0v : ∀ v, h₀ ≤ |realEmb F v c * (z v).im| := by
    intro v
    refine le_trans ?_ (hhv v)
    simp only [h₀]
    rw [div_mul_eq_mul_div, mul_comm]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hy₀.le hx1) hC.le
  have hhne : ∀ v, realEmb F v c * (z v).im ≠ 0 := fun v h => by
    have := hh0v v; rw [h, abs_zero] at this; linarith
  rw [rowCoeff, norm_mul, norm_mul, norm_mul, norm_cexp_two_pi_I_real, mul_one, Complex.norm_real,
    NNReal.norm_eq, norm_prod]
  -- each place
  have hplace' : ∀ v, ‖lineFT 2 s (ν v) (realEmb F v c * (z v).im)‖ ≤
      M₀ * Real.exp (-π * (|ν v| * |realEmb F v c * (z v).im|)) := by
    intro v
    refine (norm_lineFT_le le_rfl hs0 hs1 _ (hhne v)).trans ?_
    set h := |realEmb F v c * (z v).im|
    have hh : 0 < h := hh₀.trans_le (hh0v v)
    have e1 : h * (h ^ 2)⁻¹ = h⁻¹ := by field_simp
    rw [e1]
    have e2 : h⁻¹ ≤ h₀⁻¹ := inv_anti₀ hh₀ (hh0v v)
    have e3 : max 1 (h ^ 2)⁻¹ ≤ max 1 (h₀ ^ 2)⁻¹ :=
      max_le_max le_rfl (inv_anti₀ (by positivity) (pow_le_pow_left₀ hh₀.le (hh0v v) 2))
    have : h⁻¹ * max 1 (h ^ 2)⁻¹ * C₂ ≤ M₀ :=
      mul_le_mul (mul_le_mul e2 e3 (by positivity) (by positivity)) le_rfl hC₂ (by positivity)
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hprod : ∏ v, ‖lineFT 2 s (ν v) (realEmb F v c * (z v).im)‖ ≤
      M₀ ^ d * Real.exp (-π * ∑ v, |ν v| * |realEmb F v c * (z v).im|) := by
    calc ∏ v, ‖lineFT 2 s (ν v) (realEmb F v c * (z v).im)‖
        ≤ ∏ v, (M₀ * Real.exp (-π * (|ν v| * |realEmb F v c * (z v).im|))) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => hplace' v
      _ = M₀ ^ d * Real.exp (-π * ∑ v, |ν v| * |realEmb F v c * (z v).im|) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.mul_sum, ← Real.exp_sum]
  have hexp : Real.exp (-π * ∑ v, |ν v| * |realEmb F v c * (z v).im|) ≤
      Real.exp (π * y₀ * ρ / C) * (Real.exp (-(π * y₀ / C) * l1 ν) * Real.exp (-(π * y₀ * ρ / C) * X)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hsum : X / C * y₀ * l1 ν ≤ ∑ v, |ν v| * |realEmb F v c * (z v).im| := by
      rw [l1, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [mul_comm (|ν v|)]
      exact mul_le_mul_of_nonneg_right (hhv v) (abs_nonneg _)
    have hl1 : ρ ≤ l1 ν := hρn n hn
    have hX : l1 ν + (X - 1) * ρ ≤ X * l1 ν := by nlinarith [l1_nonneg ν]
    have h5 : (y₀ / C) * (l1 ν + (X - 1) * ρ) ≤ ∑ v, |ν v| * |realEmb F v c * (z v).im| := by
      calc (y₀ / C) * (l1 ν + (X - 1) * ρ) ≤ (y₀ / C) * (X * l1 ν) :=
            mul_le_mul_of_nonneg_left hX (by positivity)
        _ = X / C * y₀ * l1 ν := by ring
        _ ≤ _ := hsum
    have h6 := mul_le_mul_of_nonneg_left h5 Real.pi_pos.le
    have rhs_eq : π * y₀ * ρ / C + (-(π * y₀ / C) * l1 ν + -(π * y₀ * ρ / C) * X) =
        -(π * ((y₀ / C) * (l1 ν + (X - 1) * ρ))) := by ring
    rw [rhs_eq]
    linarith
  have hR := norm_rowR_le hW hB c ν
  calc Kl * ‖rowR W 𝔐 c ν‖ * ∏ v, ‖lineFT 2 s (ν v) (realEmb F v c * (z v).im)‖
      ≤ Kl * (Nat.card (𝓞 F ⧸ 𝔐) * B) * (M₀ ^ d * Real.exp (-π * ∑ v, |ν v| * |realEmb F v c * (z v).im|)) := by
        gcongr
    _ ≤ Kl * (Nat.card (𝓞 F ⧸ 𝔐) * B) * (M₀ ^ d * (Real.exp (π * y₀ * ρ / C) *
          (Real.exp (-(π * y₀ / C) * l1 ν) * Real.exp (-(π * y₀ * ρ / C) * X)))) := by
        gcongr
    _ = _ := by ring

lemma dualVec_zero {J : Type*} [Fintype J] (b : Module.Basis J ℝ (InfinitePlace F → ℝ)) :
    dualVec b 0 = 0 := by
  rw [dualVec]
  convert map_zero (pairEquiv b).symm
  simp

/-- **The terms $\nu = 0$ are $O(s^d)$** ($0 < s \le 1$, $\operatorname{Im}z_v \ge y_0$):
$|\texttt{rowCoeff}(\tilde t, 0)| \le K\,s^d\,|N\tilde t|^{-1-2s}$. -/
theorem norm_rowCoeff_two_zero_le {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {y₀ : ℝ}
    (hy₀ : 0 < y₀) : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ z : InfinitePlace F → ℍ, (∀ v, y₀ ≤ (z v).im) → ∀ t : IntOrbits F,
        ‖rowCoeff W 𝔐 hW.ne 2 s (crep t.1) z 0‖ ≤
          K₁ * s ^ Fintype.card (InfinitePlace F) * absNorm (crep t.1) ^ (-(1 + 2 * s)) := by
  obtain ⟨B, hB⟩ := hW.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set κ := 4 * ∫ u : ℝ, (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)
  have hκ : 0 ≤ κ := by
    have : 0 ≤ ∫ u : ℝ, (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
      integral_nonneg fun u => Real.rpow_nonneg (by positivity) _
    positivity
  set Y := max (y₀ ^ (-(3 : ℝ))) (y₀ ^ (-(1 : ℝ)))
  set d := Fintype.card (InfinitePlace F)
  set Kl := (latConst (levelBasis 𝔐 hW.ne) : ℝ)
  refine ⟨Kl * (Nat.card (𝓞 F ⧸ 𝔐) * B) * κ ^ d * Y ^ d, by positivity, fun s hs0 hs1 z hz t => ?_⟩
  set c := crep t.1
  have hc : c ≠ 0 := (crep_eq_zero_iff _).not.mpr t.2.2
  have hcv : ∀ v, realEmb F v c ≠ 0 := fun v => (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  rw [rowCoeff, dualVec_zero]
  simp only [Pi.zero_apply]
  rw [norm_mul, norm_mul, norm_mul, norm_cexp_two_pi_I_real, mul_one, Complex.norm_real, NNReal.norm_eq,
    norm_prod]
  have hplace : ∀ v, ‖lineFT 2 s 0 (realEmb F v c * (z v).im)‖ ≤
      s * κ * (|realEmb F v c| ^ (-(1 + 2 * s)) * Y) := by
    intro v
    have hh : realEmb F v c * (z v).im ≠ 0 := mul_ne_zero (hcv v) (z v).im_pos.ne'
    rw [lineFT_scale 2 s 0 hh, zero_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (abs_nonneg _), norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    set h := |realEmb F v c * (z v).im|
    have hpos : 0 < h := abs_pos.mpr hh
    have e1 : h * (h ^ 2)⁻¹ * h ^ (-2 * s) = h ^ (-(1 + 2 * s)) := by
      rw [show -(1 + 2 * s) = -1 + -2 * s by ring, Real.rpow_add hpos, Real.rpow_neg_one]
      field_simp
    rw [e1]
    have hh' : h = |realEmb F v c| * (z v).im := by
      simp only [h]; rw [abs_mul, abs_of_pos (z v).im_pos]
    have hy : (z v).im ^ (-(1 + 2 * s)) ≤ Y := by
      refine (Real.rpow_le_rpow_of_nonpos hy₀ (hz v) (by linarith)).trans ?_
      exact rpow_le_max hy₀ (by linarith) (by linarith)
    rw [hh', Real.mul_rpow (abs_nonneg _) (z v).im_pos.le]
    have hT := norm_lineFT_two_zero_le hs0.le hs1
    calc |realEmb F v c| ^ (-(1 + 2 * s)) * (z v).im ^ (-(1 + 2 * s)) * ‖lineFT 2 s 0 1‖
        ≤ |realEmb F v c| ^ (-(1 + 2 * s)) * Y * (s * κ) := by
          gcongr
    _ = s * κ * (|realEmb F v c| ^ (-(1 + 2 * s)) * Y) := by ring
  have hprod : ∏ v, ‖lineFT 2 s 0 (realEmb F v c * (z v).im)‖ ≤
      (s * κ) ^ d * (absNorm c ^ (-(1 + 2 * s)) * Y ^ d) := by
    calc ∏ v, ‖lineFT 2 s 0 (realEmb F v c * (z v).im)‖
        ≤ ∏ v, (s * κ * (|realEmb F v c| ^ (-(1 + 2 * s)) * Y)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun v _ => hplace v
      _ = (s * κ) ^ d * (absNorm c ^ (-(1 + 2 * s)) * Y ^ d) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_mul_distrib,
            Finset.prod_const, Finset.card_univ, absNorm,
            Real.finset_prod_rpow _ _ (fun _ _ => abs_nonneg _)]
  have hR := norm_rowR_le hW hB c 0
  calc Kl * ‖rowR W 𝔐 c 0‖ * ∏ v, ‖lineFT 2 s 0 (realEmb F v c * (z v).im)‖
      ≤ Kl * (Nat.card (𝓞 F ⧸ 𝔐) * B) * ((s * κ) ^ d * (absNorm c ^ (-(1 + 2 * s)) * Y ^ d)) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-! ### Termwise limits -/

/-- $T_{k,s}(\xi, h) \to T_{k,0}(\xi, h)$ as $s \to 0^+$, any $h \ne 0$. -/
lemma tendsto_lineFT_zero' {k : ℕ} (hk : 2 ≤ k) (ξ : ℝ) {h : ℝ} (hh : h ≠ 0) :
    Tendsto (fun s => lineFT k s ξ h) (𝓝[>] 0) (𝓝 (lineFT k 0 ξ h)) := by
  have e : ∀ s, lineFT k s ξ h = ((|h| : ℝ) : ℂ) * ((h : ℂ) ^ k)⁻¹ * ((|h| ^ (-2 * s) : ℝ) : ℂ) *
      lineFT k s (ξ * h) 1 := fun s => lineFT_scale k s ξ hh
  simp_rw [e]
  have hc : Tendsto (fun s : ℝ => ((|h| ^ (-2 * s) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (((|h| ^ (-2 * (0 : ℝ))) : ℝ) : ℂ)) := by
    have : Continuous fun s : ℝ => ((|h| ^ (-2 * s) : ℝ) : ℂ) :=
      continuous_ofReal.comp (continuous_const.rpow (by fun_prop) fun _ => Or.inl (abs_pos.mpr hh).ne')
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ((tendsto_const_nhds.mul hc).mul (tendsto_lineFT_zero hk (ξ * h)))

/-- The row coefficients converge termwise as $s \to 0^+$. -/
lemma tendsto_rowCoeff_zero {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) {k : ℕ} (hk : 2 ≤ k)
    {c : F} (hc : c ≠ 0) (z : InfinitePlace F → ℍ) (n : Fin (Module.finrank ℚ F) → ℤ) :
    Tendsto (fun s => rowCoeff W 𝔐 h𝔐 k s c z n) (𝓝[>] 0) (𝓝 (rowCoeff W 𝔐 h𝔐 k 0 c z n)) := by
  have hcv : ∀ v, realEmb F v c ≠ 0 := fun v => (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  unfold rowCoeff
  refine ((tendsto_const_nhds.mul ?_).mul tendsto_const_nhds)
  exact tendsto_finset_prod _ fun v _ =>
    tendsto_lineFT_zero' hk _ (mul_ne_zero (hcv v) (z v).im_pos.ne')

lemma rowCoeff_two_zero_zero {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) {c : F} (hc : c ≠ 0)
    (z : InfinitePlace F → ℍ) : rowCoeff W 𝔐 h𝔐 2 0 c z 0 = 0 := by
  have hcv : ∀ v, realEmb F v c ≠ 0 := fun v => (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  rw [rowCoeff, dualVec_zero]
  simp only [Pi.zero_apply]
  rw [Finset.prod_eq_zero (Finset.mem_univ v)]
  · simp
  · rw [lineFT_zero_eq le_rfl 0 (mul_ne_zero (hcv v) (z v).im_pos.ne')]
    simp

/-! ### The majorant on $U\backslash F \times \mathbb{Z}^d$ -/

open Classical in
/-- $G(t, n) = K\,e^{-a_1\|\nu_n\|_1}e^{-a_2\|\sigma(\tilde t)\|}$ on integral nonzero orbits, $0$ elsewhere. -/
noncomputable def heckeMaj (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (K a₁ a₂ : ℝ)
    (p : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ)) : ℝ :=
  if h : IsIntOrbit p.1 ∧ p.1.out ≠ 0 then
    K * Real.exp (-a₁ * l1 (dualVec (levelBasis 𝔐 h𝔐) p.2)) * Real.exp (-a₂ * ‖latPt ⟨p.1, h⟩‖) else 0

lemma heckeMaj_nonneg (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) {K : ℝ} (hK : 0 ≤ K) (a₁ a₂ : ℝ) (p) :
    0 ≤ heckeMaj 𝔐 h𝔐 K a₁ a₂ p := by
  unfold heckeMaj; split_ifs <;> positivity

theorem summable_heckeMaj (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) {K a₁ a₂ : ℝ} (hK : 0 ≤ K) (ha₁ : 0 < a₁)
    (ha₂ : 0 < a₂) : Summable (heckeMaj 𝔐 h𝔐 K a₁ a₂) := by
  classical
  set f : UOrbitF F → ℝ := fun t => if h : IsIntOrbit t ∧ t.out ≠ 0 then
    Real.exp (-a₂ * ‖latPt ⟨t, h⟩‖) else 0
  set g : (Fin (Module.finrank ℚ F) → ℤ) → ℝ := fun n =>
    K * Real.exp (-a₁ * l1 (dualVec (levelBasis 𝔐 h𝔐) n))
  have hf : Summable f := by
    have hsub : Summable fun t : IntOrbits F => Real.exp (-a₂ * ‖latPt t‖) :=
      (summable_exp_neg_norm_intLatF (F := F) ha₂).comp_injective latPt_injective
    have hsupp : Function.support f ⊆ Set.range (Subtype.val : IntOrbits F → UOrbitF F) := by
      intro t ht
      by_cases h : IsIntOrbit t ∧ t.out ≠ 0
      · exact ⟨⟨t, h⟩, rfl⟩
      · exact absurd (by simp only [f, dif_neg h]) ht
    have hzero : ∀ t ∉ Set.range (Subtype.val : IntOrbits F → UOrbitF F), f t = 0 := by
      intro t ht; by_contra hne; exact ht (hsupp hne)
    refine ((Subtype.val_injective (p := fun t : UOrbitF F => IsIntOrbit t ∧ t.out ≠ 0)).summable_iff
      hzero).mp ?_
    refine hsub.congr fun t => ?_
    simp only [Function.comp, f, dif_pos t.2]
  have hg : Summable g := (summable_exp_neg_l1 (levelBasis 𝔐 h𝔐) (by positivity : 0 < a₁)).mul_left K
  refine (Summable.mul_of_nonneg hf hg (fun t => by simp only [f]; split_ifs <;> positivity)
    (fun n => by simp only [g]; positivity)).congr fun p => ?_
  simp only [f, g, heckeMaj]
  split_ifs <;> ring

/-! ### Splitting off the terms $\nu = 0$ -/

open Classical in
/-- The terms with $\nu \ne 0$, on $U\backslash F \times \mathbb{Z}^d$. -/
noncomputable def heckeOsc (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (s : ℝ) (z : InfinitePlace F → ℍ)
    (p : UOrbitF F × (Fin (Module.finrank ℚ F) → ℤ)) : ℂ :=
  if p.1.out = 0 ∨ p.2 = 0 then 0 else rowCoeff W 𝔐 h𝔐 2 s (crep p.1) z p.2

lemma norm_heckeOsc_le {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {y₀ : ℝ}
    {K₀ a₁ a₂ : ℝ} (hK₀ : 0 ≤ K₀)
    (hM1 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ z : InfinitePlace F → ℍ, (∀ v, y₀ ≤ (z v).im) → ∀ (t : IntOrbits F)
      (n : Fin (Module.finrank ℚ F) → ℤ), n ≠ 0 →
        ‖rowCoeff W 𝔐 hW.ne 2 s (crep t.1) z n‖ ≤
          K₀ * Real.exp (-a₁ * l1 (dualVec (levelBasis 𝔐 hW.ne) n)) * Real.exp (-a₂ * ‖latPt t‖))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : InfinitePlace F → ℍ} (hz : ∀ v, y₀ ≤ (z v).im) (p) :
    ‖heckeOsc W 𝔐 hW.ne s z p‖ ≤ heckeMaj 𝔐 hW.ne K₀ a₁ a₂ p := by
  classical
  unfold heckeOsc heckeMaj
  by_cases h0 : p.1.out = 0 ∨ p.2 = 0
  · rw [if_pos h0, norm_zero]; split_ifs <;> positivity
  · rw [if_neg h0]
    push Not at h0
    by_cases hint : IsIntOrbit p.1
    · rw [dif_pos ⟨hint, h0.1⟩]
      exact hM1 s hs0 hs1 z hz ⟨p.1, hint, h0.1⟩ p.2 h0.2
    · rw [rowCoeff_eq_zero_of_not_int hW s hint, norm_zero]; split_ifs <;> positivity

open Classical in
lemma rows_split {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) {y₀ : ℝ}
    {K₀ a₁ a₂ : ℝ} (hK₀ : 0 ≤ K₀) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hM1 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ z : InfinitePlace F → ℍ, (∀ v, y₀ ≤ (z v).im) → ∀ (t : IntOrbits F)
      (n : Fin (Module.finrank ℚ F) → ℤ), n ≠ 0 →
        ‖rowCoeff W 𝔐 hW.ne 2 s (crep t.1) z n‖ ≤
          K₀ * Real.exp (-a₁ * l1 (dualVec (levelBasis 𝔐 hW.ne) n)) * Real.exp (-a₂ * ‖latPt t‖))
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {z : InfinitePlace F → ℍ} (hz : ∀ v, y₀ ≤ (z v).im)
    (hZ : Summable fun t : UOrbitF F => if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 s (crep t) z 0) :
    ∑' t : UOrbitF F, (if t.out = 0 then 0 else ∑' n, rowCoeff W 𝔐 hW.ne 2 s (crep t) z n) =
      ∑' t : UOrbitF F, (if t.out = 0 then 0 else rowCoeff W 𝔐 hW.ne 2 s (crep t) z 0) +
        ∑' p, heckeOsc W 𝔐 hW.ne s z p := by
  have hG := summable_heckeMaj 𝔐 hW.ne hK₀ ha₁ ha₂
  have hosc : Summable (heckeOsc W 𝔐 hW.ne s z) :=
    Summable.of_norm_bounded hG (norm_heckeOsc_le hW hK₀ hM1 hs0 hs1 hz)
  have hrow : ∀ t, Summable fun n => heckeOsc W 𝔐 hW.ne s z (t, n) := fun t => hosc.prod_factor t
  have hrowsum : Summable fun t => ∑' n, heckeOsc W 𝔐 hW.ne s z (t, n) := hosc.prod
  have hpt : ∀ t : UOrbitF F, (if t.out = 0 then 0 else ∑' n, rowCoeff W 𝔐 hW.ne 2 s (crep t) z n) =
      (if t.out = 0 then 0 else rowCoeff W 𝔐 hW.ne 2 s (crep t) z 0) +
        ∑' n, heckeOsc W 𝔐 hW.ne s z (t, n) := by
    intro t
    by_cases ht : t.out = 0
    · simp only [ht, ↓reduceIte, zero_add]
      have : (fun n => heckeOsc W 𝔐 hW.ne s z (t, n)) = fun _ => 0 := by
        funext n; simp [heckeOsc, ht]
      rw [this, tsum_zero]
    · simp only [ht, ↓reduceIte]
      have hs : Summable fun n => rowCoeff W 𝔐 hW.ne 2 s (crep t) z n := by
        have : (fun n => rowCoeff W 𝔐 hW.ne 2 s (crep t) z n) = fun n =>
            heckeOsc W 𝔐 hW.ne s z (t, n) + if n = 0 then rowCoeff W 𝔐 hW.ne 2 s (crep t) z 0 else 0 := by
          funext n
          by_cases hn : n = 0
          · subst hn; simp [heckeOsc]
          · simp [heckeOsc, ht, hn]
        rw [this]
        exact (hrow t).add (summable_of_ne_finset_zero (s := {0}) fun n hn => by
          simp only [Finset.mem_singleton] at hn; simp [hn])
      rw [hs.tsum_eq_add_tsum_ite 0]
      congr 1
      refine tsum_congr fun n => ?_
      by_cases hn : n = 0
      · simp [hn, heckeOsc]
      · simp [hn, heckeOsc, ht]
  simp_rw [hpt]
  rw [hZ.tsum_add hrowsum, hosc.tsum_prod' hrow]

/-! ### The terms $c = 0$ -/

lemma absNorm_crep (t : UOrbitF F) : absNorm (crep t) = absNorm t.out := by
  rw [crep, absNorm, absNorm]
  simp only [map_mul, abs_mul, Finset.prod_mul_distrib]
  have hu : ∀ ε : (𝓞 F)ˣ, ∏ x, |realEmb F x (algebraMap (𝓞 F) F (ε : 𝓞 F))| = 1 := by
    intro ε
    have := abs_unitNorm ε
    rw [unitNorm, Finset.abs_prod] at this
    exact this
  rw [hu, one_mul]

lemma heckeTerm_zero_fst (W : F × F → ℂ) (k : ℕ) (s : ℝ) (x : F) (Z : InfinitePlace F → ℂ) :
    heckeTerm W k s ((0 : F), x) Z = W ((0 : F), x) * ∏ v, phiKS k s (realEmb F v x : ℂ) := by
  simp [heckeTerm]

/-- **The constant part converges**: $\sum_tW(0,t)N(t)^{-2}|N(t)|^{-2s} \to \mathrm{c}_\infty(W)$ as $s \to 0^+$. -/
theorem tendsto_heckeSeries_cpart {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐)
    (z : InfinitePlace F → ℍ) :
    Tendsto (fun s => ∑' t : UOrbitF F, heckeTerm W 2 s ((0 : F), t.out) (fun v => (z v : ℂ)))
      (𝓝[>] 0) (𝓝 (eisConst W 2)) := by
  classical
  obtain ⟨B, hB⟩ := hW.bdd
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨K₄, -, hE4⟩ := exists_tsum_absNorm_le (F := F)
  have hsub := (hE4 (1 / 2) (by norm_num) (by norm_num)).1
  set g : UOrbitF F → ℝ := fun t => if h : IsIntOrbit t ∧ t.out ≠ 0 then
    B * absNorm (crep (⟨t, h⟩ : IntOrbits F).1) ^ (-(1 + 2 * (1 / 2 : ℝ))) else 0 with hg
  have hgs : Summable g := by
    have hsupp : ∀ t ∉ Set.range (Subtype.val : IntOrbits F → UOrbitF F), g t = 0 := by
      intro t ht
      by_cases h : IsIntOrbit t ∧ t.out ≠ 0
      · exact absurd ⟨⟨t, h⟩, rfl⟩ ht
      · simp only [hg, dif_neg h]
    refine ((Subtype.val_injective (p := fun t : UOrbitF F => IsIntOrbit t ∧ t.out ≠ 0)).summable_iff
      hsupp).mp ?_
    refine (hsub.mul_left B).congr fun t => ?_
    simp only [Function.comp, hg, dif_pos t.2]
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t; simp only [hg]; split_ifs
    · exact mul_nonneg hB0 (Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _)
    · exact le_rfl
  have hlim0 : ∑' t : UOrbitF F, heckeTerm W 2 0 ((0 : F), t.out) (fun v => (z v : ℂ)) = eisConst W 2 := by
    rw [eisConst_eq_tsum_orbitF hW.unit]
    refine tsum_congr fun t => ?_
    rw [heckeTerm_zero, eisTerm, eisDen_of_fst_eq_zero rfl]
    rfl
  rw [← hlim0]
  refine tendsto_tsum_of_dominated_convergence hgs (fun t => ?_) ?_
  · -- termwise
    simp only [heckeTerm_zero_fst]
    refine tendsto_const_nhds.mul (tendsto_finset_prod _ fun v _ => ?_)
    by_cases hx : realEmb F v t.out = 0
    · simp [phiKS, hx]
    · unfold phiKS
      refine tendsto_const_nhds.mul ?_
      have hn : ‖((realEmb F v t.out : ℝ) : ℂ)‖ ≠ 0 := by simpa using hx
      have : Continuous fun s : ℝ => ((‖((realEmb F v t.out : ℝ) : ℂ)‖ ^ (-2 * s) : ℝ) : ℂ) :=
        continuous_ofReal.comp (continuous_const.rpow (by fun_prop) fun _ => Or.inl hn)
      exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs t
    rw [norm_heckeTerm, eisDen_of_fst_eq_zero rfl, norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [show (∏ v, |realEmb F v t.out|) = absNorm t.out from rfl]
    by_cases hW0 : W ((0 : F), t.out) = 0
    · rw [hW0, norm_zero, zero_mul, zero_mul]; exact hg0 t
    · obtain ⟨p, hp⟩ := hW.supp _ hW0
      have hx : algebraMap (𝓞 F) F p.2 = t.out := congrArg Prod.snd hp
      by_cases hx0 : t.out = 0
      · rw [hx0, show absNorm (0 : F) = 0 by
          obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
          exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, _root_.inv_zero, mul_zero,
          zero_mul]
        exact hg0 t
      · have hint : IsIntOrbit t ∧ t.out ≠ 0 := ⟨⟨p.2, hx⟩, hx0⟩
        simp only [hg, dif_pos hint]
        rw [absNorm_crep]
        have hA : 1 ≤ absNorm t.out := by
          rw [← hx]; exact one_le_prod_abs_realEmb fun h => hx0 (by rw [← hx, h, map_zero])
        have hA0 : 0 < absNorm t.out := by linarith
        have h1 : absNorm t.out ^ (-2 * s) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hA (by linarith [hs.1])
        have h2 : (absNorm t.out ^ 2)⁻¹ = absNorm t.out ^ (-(1 + 2 * (1 / 2 : ℝ))) := by
          rw [show -(1 + 2 * (1 / 2 : ℝ)) = -(2 : ℝ) by norm_num, Real.rpow_neg hA0.le]; norm_cast
        rw [← h2]
        calc ‖W ((0 : F), t.out)‖ * (absNorm t.out ^ 2)⁻¹ * absNorm t.out ^ (-2 * s)
            ≤ B * (absNorm t.out ^ 2)⁻¹ * 1 := by gcongr; exact hB _
          _ = B * (absNorm t.out ^ 2)⁻¹ := mul_one _

/-! ### Hecke's limit -/

open Classical in
/-- **The parallel weight 2 Eisenstein series** of an integral weight $W$ (for $d \ge 2$ it is the Hecke limit,
`tendsto_heckeSeries_two`):
$$E_{W,2}(z) = \mathrm{c}_\infty(W) + \sum_{t\ne0}\sum_n\texttt{rowCoeff}(W, \mathfrak M, 2, 0, \tilde t, z, n).$$ -/
@[kb "shimura1978" "Prop. 3.4 (weight 2 by Hecke's trick) [unverified]"]
noncomputable def eis2 (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (z : InfinitePlace F → ℍ) : ℂ :=
  eisConst W 2 + ∑' t : UOrbitF F, (if t.out = 0 then 0 else ∑' n, rowCoeff W 𝔐 h𝔐 2 0 (crep t) z n)

open Classical in
/-- **Hecke's trick in parallel weight 2, $d \ge 2$**: for an integral weight $W$ of weight $2$,
$$\lim_{s\to0^+}\sum_{x\in U\backslash F^2}W(x)\,N(cz+d)^{-2}|N(cz+d)|^{-2s} = E_{W,2}(z),$$
with **no non-holomorphic correction** (the $\nu = 0$ terms are $O(s^{d-1})$). -/
@[kb "hecke1927" "Hecke's trick; the case d ≥ 2 has no correction term (Shimura 1978, Prop. 3.4) [unverified]"]
theorem tendsto_heckeSeries_two (hd : 2 ≤ Fintype.card (InfinitePlace F)) {W : F × F → ℂ}
    {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W 2 𝔐) (z : InfinitePlace F → ℍ) :
    Tendsto (fun s => heckeSeries W 2 s z) (𝓝[>] 0) (𝓝 (eis2 W 𝔐 hW.ne z)) := by
  classical
  set d := Fintype.card (InfinitePlace F)
  obtain ⟨y₀, hy₀, hy₀v⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  have hz : ∀ v, y₀ ≤ (z v).im := fun v => (hy₀v v).le
  obtain ⟨K₀, a₁, a₂, hK₀, ha₁, ha₂, hM1⟩ := norm_rowCoeff_two_le hW hy₀
  obtain ⟨K₁, hK₁, hM0⟩ := norm_rowCoeff_two_zero_le hW hy₀
  obtain ⟨K₄, hK₄, hE4⟩ := exists_tsum_absNorm_le (F := F)
  set Z : ℝ → UOrbitF F → ℂ := fun s t => if t.out = 0 then 0 else rowCoeff W 𝔐 hW.ne 2 s (crep t) z 0
  -- the `ν = 0` terms: summable, and `O(s^{d-1})`
  have hZbound : ∀ s, 0 < s → s ≤ 1 → ∀ t, ‖Z s t‖ ≤ (if h : IsIntOrbit t ∧ t.out ≠ 0 then
      K₁ * s ^ d * absNorm (crep (⟨t, h⟩ : IntOrbits F).1) ^ (-(1 + 2 * s)) else 0) := by
    intro s hs0 hs1 t
    simp only [Z]
    by_cases ht : t.out = 0
    · rw [if_pos ht, norm_zero]; split_ifs
      · exact mul_nonneg (by positivity) (Real.rpow_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) _)
      · exact le_rfl
    · rw [if_neg ht]
      by_cases hint : IsIntOrbit t
      · rw [dif_pos ⟨hint, ht⟩]; exact hM0 s hs0 hs1 z hz ⟨t, hint, ht⟩
      · rw [rowCoeff_eq_zero_of_not_int hW s hint, norm_zero, dif_neg (fun h => hint h.1)]
  have hZsum : ∀ s, 0 < s → s ≤ 1 → Summable (Z s) ∧ ‖∑' t, Z s t‖ ≤ K₁ * s ^ d * (K₄ * (1 + 1 / s)) := by
    intro s hs0 hs1
    obtain ⟨hsub, hle⟩ := hE4 s hs0 hs1
    set b : UOrbitF F → ℝ := fun t => if h : IsIntOrbit t ∧ t.out ≠ 0 then
      K₁ * s ^ d * absNorm (crep (⟨t, h⟩ : IntOrbits F).1) ^ (-(1 + 2 * s)) else 0
    have hzero : ∀ t ∉ Set.range (Subtype.val : IntOrbits F → UOrbitF F), b t = 0 := by
      intro t ht
      by_cases h : IsIntOrbit t ∧ t.out ≠ 0
      · exact absurd ⟨⟨t, h⟩, rfl⟩ ht
      · simp only [b, dif_neg h]
    have hcomp : (b ∘ Subtype.val) = fun t : IntOrbits F => K₁ * s ^ d * absNorm (crep t.1) ^ (-(1 + 2 * s)) := by
      funext t; simp only [Function.comp, b, dif_pos t.2]
    have hbs : Summable b := by
      refine ((Subtype.val_injective (p := fun t : UOrbitF F => IsIntOrbit t ∧ t.out ≠ 0)).summable_iff
        hzero).mp ?_
      rw [hcomp]; exact hsub.mul_left _
    have hbsum : ∑' t, b t = K₁ * s ^ d * ∑' t : IntOrbits F, absNorm (crep t.1) ^ (-(1 + 2 * s)) := by
      have hsupp : Function.support b ⊆ Set.range (Subtype.val : IntOrbits F → UOrbitF F) := by
        intro t ht
        by_cases h : IsIntOrbit t ∧ t.out ≠ 0
        · exact ⟨⟨t, h⟩, rfl⟩
        · exact absurd (by simp only [b, dif_neg h]) ht
      rw [← (Subtype.val_injective (p := fun t : UOrbitF F => IsIntOrbit t ∧ t.out ≠ 0)).tsum_eq hsupp,
        ← tsum_mul_left]
      congr 1
    have hZs : Summable (Z s) := Summable.of_norm_bounded hbs (hZbound s hs0 hs1)
    refine ⟨hZs, ?_⟩
    calc ‖∑' t, Z s t‖ ≤ ∑' t, b t :=
          tsum_of_norm_bounded hbs.hasSum (hZbound s hs0 hs1)
      _ = K₁ * s ^ d * ∑' t : IntOrbits F, absNorm (crep t.1) ^ (-(1 + 2 * s)) := hbsum
      _ ≤ K₁ * s ^ d * (K₄ * (1 + 1 / s)) := mul_le_mul_of_nonneg_left hle (by positivity)
  have hZlim : Tendsto (fun s => ∑' t, Z s t) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : Tendsto (fun s : ℝ => K₁ * K₄ * (s ^ d + s ^ (d - 1))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => s ^ d + s ^ (d - 1)) (𝓝[>] 0) (𝓝 (0 ^ d + 0 ^ (d - 1))) :=
        ((continuous_pow d).add (continuous_pow (d - 1))).tendsto 0 |>.mono_left nhdsWithin_le_nhds
      rw [zero_pow (by omega), zero_pow (by omega), add_zero] at h1
      simpa using h1.const_mul (K₁ * K₄)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbd
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    refine (hZsum s hs.1 hs.2.le).2.trans (le_of_eq ?_)
    have hs0 : s ≠ 0 := hs.1.ne'
    rw [show s ^ d = s * s ^ (d - 1) by rw [← pow_succ', Nat.sub_add_cancel (by omega)]]
    field_simp
  -- the oscillating terms
  have hG := summable_heckeMaj 𝔐 hW.ne hK₀ ha₁ ha₂
  have hOlim : Tendsto (fun s => ∑' p, heckeOsc W 𝔐 hW.ne s z p) (𝓝[>] 0)
      (𝓝 (∑' p, heckeOsc W 𝔐 hW.ne 0 z p)) := by
    refine tendsto_tsum_of_dominated_convergence hG (fun p => ?_) ?_
    · unfold heckeOsc
      split_ifs with h0
      · exact tendsto_const_nhds
      · push Not at h0
        exact tendsto_rowCoeff_zero hW.ne le_rfl ((crep_eq_zero_iff _).not.mpr h0.1) z p.2
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs p
      exact norm_heckeOsc_le hW hK₀ hM1 hs.1.le hs.2.le hz p
  have hsplit : ∀ s, 0 < s → s ≤ 1 → heckeSeries W 2 s z =
      ∑' t : UOrbitF F, heckeTerm W 2 s ((0 : F), t.out) (fun v => (z v : ℂ)) +
        (∑' t, Z s t + ∑' p, heckeOsc W 𝔐 hW.ne s z p) := by
    intro s hs0 hs1
    rw [heckeSeries_eq_fourier hW le_rfl hs0.le hs1 (by push_cast; linarith),
      rows_split hW hK₀ ha₁ ha₂ hM1 hs0.le hs1 hz (hZsum s hs0 hs1).1]
  have hval : eis2 W 𝔐 hW.ne z = eisConst W 2 + (0 + ∑' p, heckeOsc W 𝔐 hW.ne 0 z p) := by
    have hZ0 : ∀ t : UOrbitF F, (if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 0 (crep t) z 0) = 0 := by
      intro t
      split_ifs with ht
      · rfl
      · exact rowCoeff_two_zero_zero hW.ne ((crep_eq_zero_iff _).not.mpr ht) z
    have hZ0f : (fun t : UOrbitF F => if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 0 (crep t) z 0) = 0 :=
      funext hZ0
    have hZ0s : Summable fun t : UOrbitF F => if t.out = 0 then (0 : ℂ) else rowCoeff W 𝔐 hW.ne 2 0 (crep t) z 0 := by
      rw [hZ0f]; exact summable_zero
    rw [eis2, rows_split hW hK₀ ha₁ ha₂ hM1 le_rfl zero_le_one hz hZ0s, hZ0f,
      show (0 : UOrbitF F → ℂ) = fun _ => 0 from rfl, tsum_zero]
  rw [hval]
  refine ((tendsto_heckeSeries_cpart hW z).add (hZlim.add hOlim)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact (hsplit s hs.1 hs.2.le).symm

end QuadFormsKB.HilbertModular
