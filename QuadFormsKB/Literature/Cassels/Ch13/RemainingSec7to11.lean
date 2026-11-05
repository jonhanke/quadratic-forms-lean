/-
# Cassels, Chapter 13: remaining statements of §§7, 9, 10 and the Haar measure of §11

Formalization of the remaining statements of Cassels, *Rational Quadratic Forms* (1978), Ch. 13, that are not in
`Sec7.lean`, `Sec9.lean`, `Sec10.lean`:

* §10 (10.4)–(10.5), p. 320: the group $K$ of the block automorphs $\operatorname{diag}(U, V)$ is compact
  (`blockOrth_isCompact`);
* §7 (7.10)–(7.11), p. 311: the infinitesimal form of the invariant distance (`hypDist_sq_div_tendsto`,
  `lineElement_polar`);
* §7, Appendix, pp. 312–313: the upper half plane model (`upperHalfEquivDisc`, `actH_spec`, `actH_eq_slAction`,
  `halfToDisc_cayley`);
* §9, pp. 317–319: the action of $O_{\mathbb{R}}(f_{3,1})$ on the ball (`ballAct`), the group $\Theta$ of the
  $T(A)$ acts transitively with stabilizer the unitary group (`theta_transitive`, `theta_stabilizer`,
  `theta_point_stabilizer`), and $\Theta/K \cong$ two copies of $SL_2(\mathbb{R})/K_2$ for $f_{2,2}$
  (`theta22_quotient`, `theta22_disc`);
* §11, p. 324: existence and uniqueness up to a scalar of the Haar measure on $O_{\mathbb{R}}(f)$
  (`exists_haar_unique`).

**Not formalized.** (i) §9, p. 318: "$\Theta$ has finite index in $O^+_{\mathbb{R}}(f)$" (this needs that the unitary
$A$ give all of $SO(3)$, i.e. the surjection $SU(2) \to SO(3)$, which is not in the library); (ii) §9, p. 319, the
"alternative approach" to $f_{2,2}$ through the two pencils of lines on the quadric: a remark on method with no
precise statement; (iii) the explicit description of the Haar measure and the quotient measure of §11 (p. 324).

**Conventions.** Indices are 0-based. Cassels' $\vec\xi = (\xi_1, \xi_2)$ is `ξ 0, ξ 1`, his $x_1, \dots, x_4$ are
`x 0, …, x 3`, and the unit ball of §9 has coordinates $\xi_j = x_j/x_3$ ($0 \le j \le 2$).
-/
import QuadFormsKB.Literature.Cassels.Ch13.Basic
import QuadFormsKB.Literature.Cassels.Ch13.Sec7
import QuadFormsKB.Literature.Cassels.Ch13.Sec9
import QuadFormsKB.Literature.Cassels.Ch13.Sec10

open Matrix Filter Topology MeasureTheory

namespace QuadFormsKB.Reduction

/-! ### §10: compactness of $K$ -/

/-- Helper: the real orthogonal matrices $U^{\mathsf T}U = I$ form a compact set. -/
theorem isCompact_orthSet (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact {U : Matrix n n ℝ | Uᵀ * U = 1} := by
  have hc : IsClosed {U : Matrix n n ℝ | Uᵀ * U = 1} :=
    isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const
  have hsub : {U : Matrix n n ℝ | Uᵀ * U = 1} ⊆
      Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n => Set.Icc (-1 : ℝ) 1 := by
    intro U hU i _ j _
    have h := congrFun (congrFun hU j) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    have h2 : U i j * U i j ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun k => U k j * U k j) (fun _ _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    constructor <;> nlinarith
  exact (isCompact_univ_pi fun i : n => isCompact_univ_pi fun j : n => isCompact_Icc).of_isClosed_subset
    hc hsub

/-- **The group $K$ is compact** (Cassels, Ch. 13, §10, (10.4)–(10.5), p. 320: "The group $K$ of such $W$ is
compact"). Here $K$ is `blockOrth m l`, the subgroup of $\mathrm{GL}_{m+l}(\mathbb{R})$ of the block matrices
$\operatorname{diag}(U, V)$ with $U^{\mathsf T}U = I_m$, $V^{\mathsf T}V = I_l$, in the topology of the units of the
matrix ring (the subspace topology of $\mathrm{GL}$, which is the topology of $(W, W^{-1})$). The statement has two
equivalent forms: $K$ is a compact subset of $\mathrm{GL}_{m+l}(\mathbb{R})$, and its image in the
$(m+l) \times (m+l)$ real matrices is compact. -/
@[kb "cassels1978" "Ch. 13, §10, (10.4)–(10.5), p. 320 (K is compact)"]
theorem blockOrth_isCompact (m l : ℕ) :
    IsCompact (blockOrth m l : Set (GL (Fin m ⊕ Fin l) ℝ)) ∧
      IsCompact (Units.val '' (blockOrth m l : Set (GL (Fin m ⊕ Fin l) ℝ))) := by
  set C : Set (Matrix (Fin m ⊕ Fin l) (Fin m ⊕ Fin l) ℝ) :=
    (fun p : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin l) (Fin l) ℝ => fromBlocks p.1 0 0 p.2) ''
      ({U | Uᵀ * U = 1} ×ˢ {V | Vᵀ * V = 1}) with hC
  have hCc : IsCompact C :=
    ((isCompact_orthSet (Fin m)).prod (isCompact_orthSet (Fin l))).image
      (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd)
  have hmem : ∀ M, M ∈ C ↔ ∃ U V, Uᵀ * U = 1 ∧ Vᵀ * V = 1 ∧ M = fromBlocks U 0 0 V := by
    intro M
    constructor
    · rintro ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
      exact ⟨U, V, hU, hV, rfl⟩
    · rintro ⟨U, V, hU, hV, rfl⟩
      exact ⟨⟨U, V⟩, ⟨hU, hV⟩, rfl⟩
  have hK : (blockOrth m l : Set (GL (Fin m ⊕ Fin l) ℝ)) =
      Units.embedProduct _ ⁻¹' (C ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' C)) := by
    ext W
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply]
    constructor
    · intro hW
      exact ⟨(hmem _).2 hW, (hmem _).2 ((blockOrth m l).inv_mem hW)⟩
    · intro h
      exact ((hmem _).1 h.1)
  have hcomp : IsCompact (blockOrth m l : Set (GL (Fin m ⊕ Fin l) ℝ)) := by
    rw [hK]
    exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hCc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hCc))
  exact ⟨hcomp, hcomp.image Units.continuous_val⟩



/-! ### §7: the infinitesimal metric (7.10)–(7.11) -/


/-- **The line element (7.11), in Cartesian form**: for a point $\vec\xi \in \mathcal{D}$ and a direction
$\vec v$,
$$\Lambda(\vec\xi, \vec v) = \frac{|\vec v|^2}{1 - |\vec\xi|^2} + \frac{(\vec\xi \cdot \vec v)^2}{(1 - |\vec\xi|^2)^2}.$$
In polar coordinates $\vec\xi = r(\cos\theta, \sin\theta)$ with $\vec v = (dr)(\cos\theta, \sin\theta) +
(r\,d\theta)(-\sin\theta, \cos\theta)$ (radial and tangential components $dr$ and $r\,d\theta$) this equals
$(1-r^2)^{-2}(dr)^2 + (1-r^2)^{-1}(r\,d\theta)^2$ (`lineElement_polar`), and at the origin it is $|\vec v|^2$. This
form is polynomial in the components, so it also covers $\vec\xi = 0$ where the polar angle is undefined. -/
@[kb "cassels1978" "Ch. 13, §7, (7.11), p. 311 (the line element)"]
noncomputable def lineElement (ξ v : Fin 2 → ℝ) : ℝ :=
  (v 0 ^ 2 + v 1 ^ 2) / (1 - ξ 0 ^ 2 - ξ 1 ^ 2) +
    (ξ 0 * v 0 + ξ 1 * v 1) ^ 2 / (1 - ξ 0 ^ 2 - ξ 1 ^ 2) ^ 2

/-- Helper: $\cosh^2 d - 1 = t^2 N/(uw)$ for $\vec\eta = \vec\xi + t\vec v$, with $u = 1 - |\vec\xi|^2$,
$w = 1 - |\vec\eta|^2$ and $N = |\vec v|^2 - (\xi_0v_1 - \xi_1v_0)^2$. -/
theorem coshDist_sq_sub_one {ξ v : Fin 2 → ℝ} (hξ : ξ ∈ disc) {t : ℝ}
    (hη : ξ + t • v ∈ disc) :
    coshDist ξ (ξ + t • v) ^ 2 - 1 =
      t ^ 2 * ((v 0 ^ 2 + v 1 ^ 2) - (ξ 0 * v 1 - ξ 1 * v 0) ^ 2) /
        ((1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - (ξ + t • v) 0 ^ 2 - (ξ + t • v) 1 ^ 2)) := by
  have hu := disc_u_pos hξ
  have hw := disc_u_pos hη
  have hpos : 0 < (1 - ξ 0 ^ 2 - ξ 1 ^ 2) * (1 - (ξ + t • v) 0 ^ 2 - (ξ + t • v) 1 ^ 2) := mul_pos hu hw
  unfold coshDist
  rw [div_pow, Real.sq_sqrt hpos.le, div_sub_one hpos.ne']
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The infinitesimal invariant distance** (Cassels, Ch. 13, §7, (7.10)–(7.11), p. 311): for $\vec\xi \in \mathcal{D}$
and a direction $\vec v \in \mathbb{R}^2$, the squared distance $d(\vec\xi, \vec\xi + t\vec v)^2$ ($d$ = `hypDist`,
(7.9)) is asymptotic to $\Lambda(\vec\xi, \vec v)\,t^2$ as $t \to 0$:
$$\lim_{t \to 0,\ t \neq 0} \frac{d(\vec\xi, \vec\xi + t\vec v)^2}{t^2} = \Lambda(\vec\xi, \vec v)
= \frac{(dr)^2}{(1-r^2)^2} + \frac{(r\,d\theta)^2}{1 - r^2},$$
the last expression in polar coordinates (`lineElement_polar`). This is the faithful limit form of "$(ds)^2 =
(1-r^2)^{-2}(dr)^2 + (1-r^2)^{-1}(r\,d\theta)^2$"; Cassels calls the derivation "verified" and does not prove it. -/
@[kb "cassels1978" "Ch. 13, §7, (7.10)–(7.11), p. 311 (infinitesimal form of the metric)"]
theorem hypDist_sq_div_tendsto {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (v : Fin 2 → ℝ) :
    Tendsto (fun t : ℝ => hypDist ξ (ξ + t • v) ^ 2 / t ^ 2) (𝓝[≠] 0) (𝓝 (lineElement ξ v)) := by
  by_cases hv : v = 0
  · subst hv
    have h1 : coshDist ξ ξ = 1 := (coshDist_eq_one_iff hξ hξ).2 rfl
    simp [hypDist, h1, lineElement]
  have hu := disc_u_pos hξ
  set u : ℝ := 1 - ξ 0 ^ 2 - ξ 1 ^ 2 with hudef
  set N : ℝ := (v 0 ^ 2 + v 1 ^ 2) - (ξ 0 * v 1 - ξ 1 * v 0) ^ 2 with hN
  set w : ℝ → ℝ := fun t => 1 - (ξ + t • v) 0 ^ 2 - (ξ + t • v) 1 ^ 2 with hw
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hw0 : w 0 = u := by simp [hw, hudef]
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), ξ + t • v ∈ disc := by
    have hc : Continuous fun t : ℝ => (ξ + t • v) 0 ^ 2 + (ξ + t • v) 1 ^ 2 := by fun_prop
    have h0 : (fun t : ℝ => (ξ + t • v) 0 ^ 2 + (ξ + t • v) 1 ^ 2) 0 < 1 := by
      have : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
      simpa using this
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  -- the limit of sinh² d / t²
  have hQ : lineElement ξ v = N / (u * u) := by
    simp only [lineElement, hN, hudef]
    have hu' : (1 - ξ 0 ^ 2 - ξ 1 ^ 2) ≠ 0 := hu.ne'
    field_simp
    ring
  have hlim1 : Tendsto (fun t : ℝ => N / (u * w t)) (𝓝 0) (𝓝 (lineElement ξ v)) := by
    rw [hQ]
    have : Tendsto (fun t : ℝ => u * w t) (𝓝 0) (𝓝 (u * u)) := by
      have := (hwc.tendsto 0).const_mul u
      rwa [hw0] at this
    exact tendsto_const_nhds.div this (mul_pos hu hu).ne'
  have hsinh : ∀ᶠ t in 𝓝 (0 : ℝ), Real.sinh (hypDist ξ (ξ + t • v)) ^ 2 = t ^ 2 * (N / (u * w t)) := by
    filter_upwards [hmem] with t ht
    have h1 := one_le_coshDist hξ ht
    unfold hypDist
    rw [Real.sinh_arcosh h1, Real.sq_sqrt (by nlinarith), coshDist_sq_sub_one hξ ht]
    simp only [hN, hudef, hw]
    ring
  have hlim2 : Tendsto (fun t : ℝ => Real.sinh (hypDist ξ (ξ + t • v)) ^ 2 / t ^ 2) (𝓝[≠] 0)
      (𝓝 (lineElement ξ v)) := by
    refine (hlim1.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hsinh, self_mem_nhdsWithin] with t ht ht0
    have : t ≠ 0 := ht0
    rw [ht]
    field_simp
  -- hypDist → 0
  have hc : Tendsto (fun t : ℝ => coshDist ξ (ξ + t • v)) (𝓝 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => coshDist ξ (ξ + t • v)) 0 := by
      unfold coshDist
      apply ContinuousAt.div (by fun_prop) _ _
      · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousAt
      · exact (Real.sqrt_pos.2 (by simpa using mul_pos hu hu)).ne'
    have h1 : coshDist ξ (ξ + (0:ℝ) • v) = 1 := (coshDist_eq_one_iff hξ (by simpa using hξ)).2 (by simp)
    rw [← h1]; exact hcont.tendsto
  have hd0 : Tendsto (fun t : ℝ => hypDist ξ (ξ + t • v)) (𝓝[≠] 0) (𝓝 0) := by
    have h := (Real.continuousOn_arcosh.continuousWithinAt (Set.mem_Ici.mpr (le_refl (1:ℝ)))).tendsto
    rw [Real.arcosh_zero] at h
    refine h.comp (tendsto_nhdsWithin_iff.2 ⟨(hc.mono_left nhdsWithin_le_nhds), ?_⟩)
    filter_upwards [nhdsWithin_le_nhds hmem] with t ht
    exact one_le_coshDist hξ ht
  have hdne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), hypDist ξ (ξ + t • v) ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with t ht ht0
    have : t ≠ 0 := ht0
    intro h
    have := (hypDist_eq_zero_iff hξ ht).1 h
    have h2 : t • v = 0 := by
      have := congrArg (fun x => x - ξ) this
      simpa using this.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact ‹t ≠ 0› h3
    · exact hv h3
  have hslope : Tendsto (fun x : ℝ => x⁻¹ * Real.sinh x) (𝓝[≠] 0) (𝓝 1) := by
    have := (Real.hasDerivAt_sinh 0).tendsto_slope_zero
    simpa using this
  have hratio : Tendsto (fun t : ℝ => (hypDist ξ (ξ + t • v))⁻¹ * Real.sinh (hypDist ξ (ξ + t • v)))
      (𝓝[≠] 0) (𝓝 1) :=
    hslope.comp (tendsto_nhdsWithin_iff.2 ⟨hd0, hdne⟩)
  have hfin := hlim2.div (hratio.pow 2) (by norm_num)
  simp only [one_pow, div_one] at hfin
  refine hfin.congr' ?_
  filter_upwards [hdne] with t ht
  have hs : Real.sinh (hypDist ξ (ξ + t • v)) ≠ 0 := by
    intro h; exact ht (Real.sinh_eq_zero.1 h)
  simp only [Pi.div_apply]
  field_simp


/-- **(7.11) in polar coordinates**: at $\vec\xi = r(\cos\theta, \sin\theta)$ ($0 \le r < 1$) the displacement
with radial component $a = dr$ and tangential component $r\,b$, $b = d\theta$, namely
$\vec v = a(\cos\theta, \sin\theta) + rb(-\sin\theta, \cos\theta)$, has
$\Lambda(\vec\xi, \vec v) = a^2/(1-r^2)^2 + (rb)^2/(1-r^2)$. -/
@[kb "cassels1978" "Ch. 13, §7, (7.11), p. 311 (polar form)"]
theorem lineElement_polar {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ a b : ℝ) :
    lineElement ![r * Real.cos θ, r * Real.sin θ]
      ![a * Real.cos θ - r * b * Real.sin θ, a * Real.sin θ + r * b * Real.cos θ] =
    a ^ 2 / (1 - r ^ 2) ^ 2 + (r * b) ^ 2 / (1 - r ^ 2) := by
  have h := Real.sin_sq_add_cos_sq θ
  have hu : 1 - r ^ 2 ≠ 0 := by nlinarith
  have e1 : (a * Real.cos θ - r * b * Real.sin θ) ^ 2 + (a * Real.sin θ + r * b * Real.cos θ) ^ 2
      = a ^ 2 + (r * b) ^ 2 := by linear_combination (a ^ 2 + (r * b) ^ 2) * h
  have e2 : r * Real.cos θ * (a * Real.cos θ - r * b * Real.sin θ) +
      r * Real.sin θ * (a * Real.sin θ + r * b * Real.cos θ) = r * a := by
    linear_combination (r * a) * h
  have e3 : 1 - (r * Real.cos θ) ^ 2 - (r * Real.sin θ) ^ 2 = 1 - r ^ 2 := by
    linear_combination (-(r ^ 2)) * h
  simp only [lineElement, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [e1, e2, e3]
  have : (r * a) ^ 2 = r ^ 2 * a ^ 2 := by ring
  rw [this]
  field_simp
  ring

/-- **(7.11), limit form in polar coordinates** (Cassels, Ch. 13, §7, (7.10)–(7.11), p. 311):
for $\vec\xi = r(\cos\theta, \sin\theta)$, $0 \le r < 1$, and $\vec v = (dr)(\cos\theta, \sin\theta) +
(r\,d\theta)(-\sin\theta, \cos\theta)$ (here $dr = a$, $d\theta = b$),
$d(\vec\xi, \vec\xi + t\vec v)^2/t^2 \to (1-r^2)^{-2}a^2 + (1-r^2)^{-1}(rb)^2$ as $t \to 0$. -/
@[kb "cassels1978" "Ch. 13, §7, (7.10)–(7.11), p. 311 (infinitesimal metric in polar coordinates)"]
theorem hypDist_infinitesimal_polar {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ a b : ℝ) :
    Tendsto (fun t : ℝ => hypDist ![r * Real.cos θ, r * Real.sin θ]
        (![r * Real.cos θ, r * Real.sin θ] +
          t • ![a * Real.cos θ - r * b * Real.sin θ, a * Real.sin θ + r * b * Real.cos θ]) ^ 2 / t ^ 2)
      (𝓝[≠] 0) (𝓝 (a ^ 2 / (1 - r ^ 2) ^ 2 + (r * b) ^ 2 / (1 - r ^ 2))) := by
  rw [← lineElement_polar hr0 hr θ a b]
  apply hypDist_sq_div_tendsto
  have h := Real.sin_sq_add_cos_sq θ
  show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 < 1
  have e : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by linear_combination r ^ 2 * h
  rw [e]; nlinarith

/-- **The infinitesimal distance $ds$** (Cassels, Ch. 13, §7, p. 311): $d(\vec\xi, \vec\xi + t\vec v)/|t| \to
\sqrt{\Lambda(\vec\xi, \vec v)}$ as $t \to 0$ (the square-root form of `hypDist_sq_div_tendsto`). -/
@[kb "cassels1978" "Ch. 13, §7, (7.11), p. 311 (ds as a limit)"]
theorem hypDist_div_abs_tendsto {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) (v : Fin 2 → ℝ) :
    Tendsto (fun t : ℝ => hypDist ξ (ξ + t • v) / |t|) (𝓝[≠] 0) (𝓝 (√(lineElement ξ v))) := by
  have h := (hypDist_sq_div_tendsto hξ v).sqrt
  refine h.congr' ?_
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), ξ + t • v ∈ disc := by
    have hc : Continuous fun t : ℝ => (ξ + t • v) 0 ^ 2 + (ξ + t • v) 1 ^ 2 := by fun_prop
    have h0 : (fun t : ℝ => (ξ + t • v) 0 ^ 2 + (ξ + t • v) 1 ^ 2) 0 < 1 := by
      have : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
      simpa using this
    exact hc.continuousAt.eventually_lt continuousAt_const h0
  filter_upwards [nhdsWithin_le_nhds hmem] with t ht
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (hypDist_nonneg' hξ ht), Real.sqrt_sq_eq_abs]


/-! ### The upper half plane model (Appendix to §7, pp. 312–313) -/

/-- **The coefficients of the form $g_z$** (Cassels, Ch. 13, §7, Appendix, p. 312): for $z = x + iy$ with $y > 0$
the positive definite form $g_z(\mathbf{u}) = (u_1 + zu_2)(u_1 + \bar z u_2) = x_1u_1^2 + 2x_2u_1u_2 + x_3u_2^2$ has
coefficients $(x_1, x_2, x_3) = (1, \operatorname{Re} z, |z|^2)$ (`normSq_form`); here the vector
$(x_1, x_2, x_3)$ indexed from $0$. -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 312 (the form g_z)"]
noncomputable def formCoeffs (z : ℂ) : Fin 3 → ℝ := ![1, z.re, Complex.normSq z]

/-- **The point of $\mathcal{D}$ of a form, by (7.7)–(7.8)** (Cassels, Ch. 13, §7, p. 310, used on p. 312): with
$f_0 = x_2^2 - x_1x_3$ and $X_1 = \frac12(x_3 - x_1)$, $X_2 = x_2$, $X_3 = \frac12(x_3 + x_1)$,
$\xi_1 = X_1/X_3$, $\xi_2 = -X_2/X_3$. In 0-based form `(x 0, x 1, x 2)` $= (x_1, x_2, x_3)$ and
$\vec\xi = \big((x_3 - x_1)/(x_3 + x_1),\ -2x_2/(x_3 + x_1)\big)$. (*Reading note:* the minus sign in
$\xi_2 = -X_2/X_3$ is the one consistent with the statement about $w = (z-i)/(z+i)$ on p. 313, see
`halfToDisc_cayley`.) -/
noncomputable def discOfForm (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(x 2 - x 0) / (x 2 + x 0), -2 * x 1 / (x 2 + x 0)]

/-- **The point $\vec\xi(z) \in \mathcal{D}$ of $z \in H$** (Cassels, Ch. 13, §7, Appendix, p. 312): the point of
$\mathcal{D}$ attached by (7.7)–(7.8) to the form $g_z$. Explicitly
$\vec\xi(z) = \big((|z|^2 - 1)/(|z|^2 + 1),\ -2\operatorname{Re} z/(|z|^2 + 1)\big)$ (`halfToDisc_zero_apply`). -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 312 (the point ξ(z))"]
noncomputable def halfToDisc (z : ℂ) : Fin 2 → ℝ := discOfForm (formCoeffs z)

/-- **$g_z$ in coordinates** (Cassels, Ch. 13, §7, Appendix, p. 312): $|u_1 + zu_2|^2 = u_1^2 + 2(\operatorname{Re} z)u_1u_2
+ |z|^2u_2^2$ for real $u_1, u_2$, i.e. $g_z$ has coefficients `formCoeffs z`. -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 312 (g_z(u) = x₁u₁² + 2x₂u₁u₂ + x₃u₂²)"]
theorem normSq_form (z : ℂ) (u₁ u₂ : ℝ) :
    Complex.normSq ((u₁ : ℂ) + z * u₂) = u₁ ^ 2 + 2 * z.re * u₁ * u₂ + Complex.normSq z * u₂ ^ 2 := by
  simp [Complex.normSq_apply]; ring

/-- Helper: the coordinates of $\vec\xi(z)$. -/
theorem halfToDisc_zero_apply (z : ℂ) :
    halfToDisc z = ![(Complex.normSq z - 1) / (Complex.normSq z + 1), -2 * z.re / (Complex.normSq z + 1)] := by
  simp [halfToDisc, discOfForm, formCoeffs]

/-- Helper: $\vec\xi(z) \in \mathcal{D}$ for $\operatorname{Im} z > 0$. -/
theorem halfToDisc_mem {z : ℂ} (hz : 0 < z.im) : halfToDisc z ∈ disc := by
  rw [halfToDisc_zero_apply]
  have hr : 0 < Complex.normSq z + 1 := by have := Complex.normSq_nonneg z; linarith
  show ((Complex.normSq z - 1) / (Complex.normSq z + 1)) ^ 2 + (-2 * z.re / (Complex.normSq z + 1)) ^ 2 < 1
  rw [div_pow, div_pow, ← add_div, div_lt_one (pow_pos hr 2)]
  rw [Complex.normSq_apply]
  nlinarith [mul_pos hz hz]

/-- Helper: the inverse $\vec\xi \mapsto z$ of $z \mapsto \vec\xi(z)$:
$z = -\xi_1/(1-\xi_0) + i\sqrt{1 - |\vec\xi|^2}/(1 - \xi_0)$. -/
noncomputable def discToHalf (ξ : Fin 2 → ℝ) : ℂ :=
  ⟨-ξ 1 / (1 - ξ 0), √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (1 - ξ 0)⟩

/-- Helper: $1 - \xi_0 > 0$ on $\mathcal{D}$. -/
theorem halfPlane_one_sub_pos {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) : 0 < 1 - ξ 0 := by
  have : ξ 0 ^ 2 + ξ 1 ^ 2 < 1 := hξ
  nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 0 - 1)]

/-- Helper: $\operatorname{Im} z > 0$ for the preimage of a point of $\mathcal{D}$. -/
theorem discToHalf_im_pos {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) : 0 < (discToHalf ξ).im := by
  show 0 < √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (1 - ξ 0)
  exact div_pos (Real.sqrt_pos.2 (disc_u_pos hξ)) (halfPlane_one_sub_pos hξ)

/-- Helper: `discToHalf` is a right inverse of `halfToDisc`. -/
theorem halfToDisc_discToHalf {ξ : Fin 2 → ℝ} (hξ : ξ ∈ disc) : halfToDisc (discToHalf ξ) = ξ := by
  have hp := halfPlane_one_sub_pos hξ
  have hu := disc_u_pos hξ
  have hs2 : √(1 - ξ 0 ^ 2 - ξ 1 ^ 2) ^ 2 = 1 - ξ 0 ^ 2 - ξ 1 ^ 2 := Real.sq_sqrt hu.le
  have hnq : Complex.normSq (discToHalf ξ) = (1 + ξ 0) / (1 - ξ 0) := by
    rw [Complex.normSq_apply]
    show (-ξ 1 / (1 - ξ 0)) * (-ξ 1 / (1 - ξ 0)) + (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (1 - ξ 0)) *
      (√(1 - ξ 0 ^ 2 - ξ 1 ^ 2) / (1 - ξ 0)) = _
    field_simp
    nlinarith [hs2]
  rw [halfToDisc_zero_apply, hnq]
  have hre : (discToHalf ξ).re = -ξ 1 / (1 - ξ 0) := rfl
  rw [hre]
  have h1 : 1 + ξ 0 + (1 - ξ 0) = 2 := by ring
  ext i; fin_cases i
  · show ((1 + ξ 0) / (1 - ξ 0) - 1) / ((1 + ξ 0) / (1 - ξ 0) + 1) = ξ 0
    field_simp
    ring
  · show -2 * (-ξ 1 / (1 - ξ 0)) / ((1 + ξ 0) / (1 - ξ 0) + 1) = ξ 1
    field_simp
    ring

/-- Helper: `discToHalf` is a left inverse of `halfToDisc`. -/
theorem discToHalf_halfToDisc {z : ℂ} (hz : 0 < z.im) : discToHalf (halfToDisc z) = z := by
  rw [halfToDisc_zero_apply]
  have hr : 0 < Complex.normSq z + 1 := by have := Complex.normSq_nonneg z; linarith
  have hnq := Complex.normSq_apply z
  have hu : 1 - ((Complex.normSq z - 1) / (Complex.normSq z + 1)) ^ 2 - (-2 * z.re / (Complex.normSq z + 1)) ^ 2
      = (2 * z.im / (Complex.normSq z + 1)) ^ 2 := by
    field_simp
    rw [hnq]; ring
  apply Complex.ext
  · show -(-2 * z.re / (Complex.normSq z + 1)) / (1 - (Complex.normSq z - 1) / (Complex.normSq z + 1)) = z.re
    field_simp
    ring
  · show √(1 - ((Complex.normSq z - 1) / (Complex.normSq z + 1)) ^ 2 - (-2 * z.re / (Complex.normSq z + 1)) ^ 2)
      / (1 - (Complex.normSq z - 1) / (Complex.normSq z + 1)) = z.im
    rw [hu, Real.sqrt_sq (by positivity)]
    field_simp
    ring

/-- **The bijection between $H$ and $\mathcal{D}$** (Cassels, Ch. 13, §7, Appendix, p. 312: "This is clearly a
bijection of $\mathcal{D}$ and $H$"): the upper half plane $H = \{z : \operatorname{Im} z > 0\}$ (Mathlib
`UpperHalfPlane`) and the disc $\mathcal{D}$ correspond by $z \mapsto \vec\xi(z)$ (`halfToDisc`), with inverse
`discToHalf`. -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 312 (the bijection 𝒟 ↔ H)"]
noncomputable def upperHalfEquivDisc : UpperHalfPlane ≃ disc where
  toFun z := ⟨halfToDisc z, halfToDisc_mem z.im_pos⟩
  invFun ξ := ⟨discToHalf ξ, discToHalf_im_pos ξ.2⟩
  left_inv z := UpperHalfPlane.ext (discToHalf_halfToDisc z.im_pos)
  right_inv ξ := Subtype.ext (halfToDisc_discToHalf ξ.2)


/-- **The adjugate of $\mathbf{S}$**: $\begin{pmatrix}\delta & -\beta\\ -\gamma & \alpha\end{pmatrix}$ for
$\mathbf{S} = \begin{pmatrix}\alpha & \beta\\ \gamma & \delta\end{pmatrix}$ (so $\mathbf{S}^{-1} =
\lambda(\mathbf{S})^{-1}\operatorname{adj}\mathbf{S}$). The element $\mathbf{S}$ of $SL^{\pm}_2(\mathbb{R})$ acts on
$\mathcal{D}$ through the Lorentz matrix `symMat (adjS S)` (the action of Lemma 7.2 composed with the identification
of the appendix: the identification is not displayed in the book, and this is the one for which the displayed formula
$z \mapsto (\beta + \delta z)/(\alpha + \gamma z)$ holds). -/
noncomputable def adjS (S : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![S 1 1, -S 0 1; -S 1 0, S 0 0]

open scoped ComplexConjugate in
/-- **The action of $\mathbf{S}$ on $H$** (Cassels, Ch. 13, §7, Appendix, p. 313): for
$\mathbf{S} = \begin{pmatrix}\alpha & \beta\\ \gamma & \delta\end{pmatrix}$ with $\lambda = \det\mathbf{S} = \pm 1$,
$z \mapsto (\beta + \delta z)/(\alpha + \gamma z)$ if $\lambda = +1$ (the conformal action) and
$z \mapsto (\beta + \delta\bar z)/(\alpha + \gamma\bar z)$ otherwise (the anti-conformal action). (For $\lambda
\ne \pm 1$ the second branch is used; it is only meaningful for $\lambda = \pm 1$.) -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (the action of S on H)"]
noncomputable def actH (S : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((S 0 1 : ℂ) + S 1 1 * (if S.det = 1 then z else conj z)) /
    ((S 0 0 : ℂ) + S 1 0 * (if S.det = 1 then z else conj z))

/-- Helper: the lift of $\vec\xi(z)$ is a rescaling of $(|z|^2 - 1, -2\operatorname{Re} z, |z|^2 + 1)$. -/
theorem liftPt_halfToDisc (z : ℂ) :
    liftPt (halfToDisc z) = (Complex.normSq z + 1)⁻¹ •
      ![Complex.normSq z - 1, -2 * z.re, Complex.normSq z + 1] := by
  have hr : Complex.normSq z + 1 ≠ 0 := by have := Complex.normSq_nonneg z; linarith
  rw [halfToDisc_zero_apply]
  ext i; fin_cases i
  · simp [liftPt, div_eq_inv_mul]
  · simp [liftPt, div_eq_inv_mul]
  · simp [liftPt, hr]

/-- Helper: the Lorentz matrix `symMat (adjS S)` applied to $(|w|^2 - 1, -2x, |w|^2 + 1)$. -/
theorem symMat_adj_vec (S : Matrix (Fin 2) (Fin 2) ℝ) (x Y : ℝ) :
    symMat (adjS S) *ᵥ ![x ^ 2 + Y ^ 2 - 1, -2 * x, x ^ 2 + Y ^ 2 + 1] =
      ![((S 0 1 + S 1 1 * x) ^ 2 + (S 1 1 * Y) ^ 2) - ((S 0 0 + S 1 0 * x) ^ 2 + (S 1 0 * Y) ^ 2),
        -2 * ((S 0 1 + S 1 1 * x) * (S 0 0 + S 1 0 * x) + S 1 1 * S 1 0 * Y ^ 2),
        ((S 0 1 + S 1 1 * x) ^ 2 + (S 1 1 * Y) ^ 2) + ((S 0 0 + S 1 0 * x) ^ 2 + (S 1 0 * Y) ^ 2)] := by
  ext i; fin_cases i <;>
    simp [symMat, adjS, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- Helper: the algebra of the action of $\mathbf{S}$ on $H$, for $w \in \{z, \bar z\}$. -/
theorem actH_core (S : Matrix (Fin 2) (Fin 2) ℝ) (hdet : S.det ≠ 0) (z w : ℂ) (hre : w.re = z.re)
    (him : w.im ^ 2 = z.im ^ 2) (hw : w.im ≠ 0) :
    ((S 0 0 : ℂ) + S 1 0 * w) ≠ 0 ∧
    (((S 0 1 : ℂ) + S 1 1 * w) / ((S 0 0 : ℂ) + S 1 0 * w)).im =
      S.det * w.im / Complex.normSq ((S 0 0 : ℂ) + S 1 0 * w) ∧
    halfToDisc (((S 0 1 : ℂ) + S 1 1 * w) / ((S 0 0 : ℂ) + S 1 0 * w)) =
      flt (symMat (adjS S)) (halfToDisc z) := by
  have hdet' : S 0 0 * S 1 1 - S 0 1 * S 1 0 ≠ 0 := by rwa [Matrix.det_fin_two] at hdet
  have hD : ((S 0 0 : ℂ) + S 1 0 * w) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    rcases h2 with h2 | h2
    · apply hdet'
      rw [h2] at h1 ⊢
      simp at h1
      rw [h1]; ring
    · exact hw h2
  have hnD : Complex.normSq ((S 0 0 : ℂ) + S 1 0 * w) = (S 0 0 + S 1 0 * w.re) ^ 2 + (S 1 0 * w.im) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have hnN : Complex.normSq ((S 0 1 : ℂ) + S 1 1 * w) = (S 0 1 + S 1 1 * w.re) ^ 2 + (S 1 1 * w.im) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have hDpos : 0 < Complex.normSq ((S 0 0 : ℂ) + S 1 0 * w) := Complex.normSq_pos.2 hD
  refine ⟨hD, ?_, ?_⟩
  · rw [Complex.div_im]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [Matrix.det_fin_two]
    field_simp
    ring
  · have hr : Complex.normSq z + 1 ≠ 0 := by have := Complex.normSq_nonneg z; linarith
    have hx : z.re = w.re := hre.symm
    have hnorm : Complex.normSq z = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.normSq_apply, hx]; linear_combination (-1 : ℝ) * him
    have hnq' : Complex.normSq (((S 0 1 : ℂ) + S 1 1 * w) / ((S 0 0 : ℂ) + S 1 0 * w)) =
        ((S 0 1 + S 1 1 * w.re) ^ 2 + (S 1 1 * w.im) ^ 2) /
          ((S 0 0 + S 1 0 * w.re) ^ 2 + (S 1 0 * w.im) ^ 2) := by
      rw [map_div₀, hnN, hnD]
    have hre' : (((S 0 1 : ℂ) + S 1 1 * w) / ((S 0 0 : ℂ) + S 1 0 * w)).re =
        ((S 0 1 + S 1 1 * w.re) * (S 0 0 + S 1 0 * w.re) + S 1 1 * S 1 0 * w.im ^ 2) /
          ((S 0 0 + S 1 0 * w.re) ^ 2 + (S 1 0 * w.im) ^ 2) := by
      rw [Complex.div_re, hnD]
      simp only [Complex.add_im, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]
      rw [hnD] at hDpos
      field_simp
      ring
    have hr2 : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
    rw [halfToDisc_zero_apply, hnq', hre']
    unfold flt
    rw [liftPt_halfToDisc, hnorm, hx, Matrix.mulVec_smul, projPt_smul (inv_ne_zero hr2), symMat_adj_vec]
    rw [hnD] at hDpos
    have hNn : 0 ≤ (S 0 1 + S 1 1 * w.re) ^ 2 + (S 1 1 * w.im) ^ 2 := by positivity
    generalize (S 0 1 + S 1 1 * w.re) ^ 2 + (S 1 1 * w.im) ^ 2 = nN at *
    generalize (S 0 0 + S 1 0 * w.re) ^ 2 + (S 1 0 * w.im) ^ 2 = nD at *
    generalize (S 0 1 + S 1 1 * w.re) * (S 0 0 + S 1 0 * w.re) + S 1 1 * S 1 0 * w.im ^ 2 = c at *
    have hs : nN + nD ≠ 0 := by positivity
    have hd : nD ≠ 0 := hDpos.ne'
    ext i; fin_cases i
    · simp [projPt]
      field_simp
    · simp [projPt]
      field_simp


open scoped ComplexConjugate in
/-- **The action of $SL^{\pm}_2(\mathbb{R})$ on $H$ corresponds to the action on $\mathcal{D}$** (Cassels, Ch. 13, §7,
Appendix, p. 313): for $\mathbf{S} \in SL^{\pm}_2(\mathbb{R})$ ($\det\mathbf{S} = \pm 1$) and $z \in H$, the point
$z' = $ `actH S z` again lies in $H$, and $\vec\xi(z')$ is the image of $\vec\xi(z)$ under the fractional-linear
transformation of $\mathcal{D}$ given by the Lorentz matrix `symMat (adjS S)` (the element of $\mathcal{M}$ attached to
$\mathbf{S}$ by Lemma 7.2, see `adjS`). For $\det = +1$ the action on $H$ is the conformal one (a Moebius map,
`actH_eq_slAction`), for $\det = -1$ the anti-conformal one. -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (SL₂^± acts on H compatibly with 𝒟)"]
theorem actH_spec {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.det = 1 ∨ S.det = -1) {z : ℂ} (hz : 0 < z.im) :
    0 < (actH S z).im ∧ halfToDisc (actH S z) = flt (symMat (adjS S)) (halfToDisc z) := by
  have hdet : S.det ≠ 0 := by rcases hS with h | h <;> simp [h]
  by_cases h1 : S.det = 1
  · have h := actH_core S hdet z z rfl rfl hz.ne'
    unfold actH
    simp only [h1, ↓reduceIte]
    refine ⟨?_, h.2.2⟩
    rw [h.2.1, h1, one_mul]
    exact div_pos hz (Complex.normSq_pos.2 h.1)
  · have h2 : S.det = -1 := hS.resolve_left h1
    have h := actH_core S hdet z (conj z) (by simp) (by simp) (by simpa using hz.ne')
    unfold actH
    simp only [h1, ↓reduceIte]
    refine ⟨?_, h.2.2⟩
    rw [h.2.1, h2]
    have : 0 < Complex.normSq ((S 0 0 : ℂ) + S 1 0 * conj z) := Complex.normSq_pos.2 h.1
    have h3 : (conj z).im = -z.im := by simp
    rw [h3]
    apply div_pos (by linarith) this

/-- Helper: the matrix $\begin{pmatrix}\delta & \beta\\ \gamma & \alpha\end{pmatrix} \in SL_2(\mathbb{R})$ of the
action of $\mathbf{S}$ ($\det\mathbf{S} = 1$) on $H$. -/
def slOfDet (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.det = 1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![S 1 1, S 0 1; S 1 0, S 0 0], by
    rw [Matrix.det_fin_two] at hS ⊢; simp; linarith⟩

/-- **For $\lambda(\mathbf{S}) = +1$ the action on $H$ is the Moebius action** (Cassels, Ch. 13, §7, Appendix,
p. 313: "the corresponding action on $H$ is the conformal one: $z \mapsto (\beta + \delta z)/(\alpha + \gamma z)$"): the
formula `actH S z` is the action of the matrix $\begin{pmatrix}\delta & \beta\\ \gamma & \alpha\end{pmatrix}$ of
$SL_2(\mathbb{R})$ on the upper half plane $H$ (Mathlib's `UpperHalfPlane` Moebius action). -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (conformal action for λ = +1)"]
theorem actH_eq_slAction {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.det = 1) (z : UpperHalfPlane) :
    actH S z = ((slOfDet S hS • z : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [actH, hS, add_comm, slOfDet]

/-- **The Cayley transform $w = (z - i)/(z + i)$** (Cassels, Ch. 13, §7, Appendix, p. 313). -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (the transformation w = (z−i)/(z+i))"]
noncomputable def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- **The Cayley transform takes $H$ into the unit disc** (Cassels, Ch. 13, §7, Appendix, p. 313: "takes $H$ into the
unit disc $|w| < 1$"): $|w|^2 < 1$ for $\operatorname{Im} z > 0$. -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (|w| < 1)"]
theorem normSq_cayley_lt {z : ℂ} (hz : 0 < z.im) : Complex.normSq (cayley z) < 1 := by
  have h : z + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  unfold cayley
  rw [map_div₀, div_lt_one (Complex.normSq_pos.2 h)]
  simp [Complex.normSq_apply]
  nlinarith

/-- **The relation between $w = u + iv$ and $\vec\xi$** (Cassels, Ch. 13, §7, Appendix, p. 313): for $z \in H$ and
$w = (z - i)/(z + i) = u + iv$,
$$\vec\xi(z) = \Big(\frac{2u}{1 + u^2 + v^2},\ \frac{2v}{1 + u^2 + v^2}\Big),$$
i.e. $\vec\xi = 2w/(1 + |w|^2)$ (the Beltrami–Klein point of the Poincare disc point $w$).
*Erratum:* the book prints "$u = 2\xi_1/(1 + \xi_1^2 + \xi_2^2)$, $v = 2\xi_2/(1 + \xi_1^2 + \xi_2^2)$" for the point $w$
"corresponding to $\xi$"; that formula is the inverse of the correct one. Example: $z = 2i$ has $w = 1/3$ and
$\vec\xi(z) = (3/5, 0)$, whereas the printed formula would give $u = (6/5)/(34/25) \ne 1/3$. The correct inverse is
$w = \vec\xi/(1 + \sqrt{1 - |\vec\xi|^2})$. (Proved here: the displayed relation, for the identification $\vec\xi(z)$
of (7.7)–(7.8).) -/
@[kb "cassels1978" "Ch. 13, §7, Appendix, p. 313 (relation of w = u + iv to ξ)"]
theorem halfToDisc_cayley {z : ℂ} (hz : 0 < z.im) :
    halfToDisc z = ![2 * (cayley z).re / (1 + Complex.normSq (cayley z)),
      2 * (cayley z).im / (1 + Complex.normSq (cayley z))] := by
  have h : z + Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hD : 0 < Complex.normSq (z + Complex.I) := Complex.normSq_pos.2 h
  have hD' : Complex.normSq (z + Complex.I) = z.re ^ 2 + (z.im + 1) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have hN : Complex.normSq (z - Complex.I) = z.re ^ 2 + (z.im - 1) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have hre : (cayley z).re = (z.re ^ 2 + z.im ^ 2 - 1) / (z.re ^ 2 + (z.im + 1) ^ 2) := by
    unfold cayley
    rw [Complex.div_re, hD']
    simp [Complex.normSq_apply] at hD' ⊢
    field_simp
    ring
  have him : (cayley z).im = -2 * z.re / (z.re ^ 2 + (z.im + 1) ^ 2) := by
    unfold cayley
    rw [Complex.div_im, hD']
    simp [Complex.normSq_apply] at hD' ⊢
    field_simp
    ring
  have hn : Complex.normSq (cayley z) = (z.re ^ 2 + (z.im - 1) ^ 2) / (z.re ^ 2 + (z.im + 1) ^ 2) := by
    unfold cayley; rw [map_div₀, hN, hD']
  rw [hD'] at hD
  rw [halfToDisc_zero_apply, hre, him, hn]
  have e : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by rw [Complex.normSq_apply]; ring
  rw [e]
  have hr : z.re ^ 2 + z.im ^ 2 + 1 ≠ 0 := by positivity
  ext i; fin_cases i
  · simp
    field_simp
    ring
  · simp
    field_simp
    ring


/-! ### §9: the form $f_{3,1}$ (pp. 317–318) -/

/-- **The matrix of $f = f_{3,1} = x_0^2 + x_1^2 + x_2^2 - x_3^2$** (Cassels, Ch. 13, §9, (9.1), p. 317; his
$x_1, \dots, x_4$ are $x_0, \dots, x_3$ here): $\operatorname{diag}(1, 1, 1, -1)$. Its real automorph group is
`realAut lor4` and the proper automorphs form `realAutPlus lor4`. -/
@[kb "cassels1978" "Ch. 13, §9, (9.1), p. 317 (the form f_{3,1})"]
def lor4 : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1, 1, 1, -1]

/-- The form $f_{3,1}(\vec x) = x_0^2 + x_1^2 + x_2^2 - x_3^2$ as a function (so $\vec x^{\mathsf T}\texttt{lor4}\,\vec x$,
`dot_lor4`). -/
def q4 (x : Fin 4 → ℝ) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - x 3 ^ 2

/-- **The open unit ball $\mathcal{B}$** (Cassels, Ch. 13, §9, (9.3), p. 317): $\xi_0^2 + \xi_1^2 + \xi_2^2 < 1$ with
$\xi_j = x_j/x_3$ (9.2). -/
@[kb "cassels1978" "Ch. 13, §9, (9.2)–(9.3), p. 317 (the unit ball ℬ)"]
def ball : Set (Fin 3 → ℝ) := {ξ | ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 < 1}

/-- The point $(\xi_0, \xi_1, \xi_2, 1)$ of $\mathbb{R}^4$ over $\vec\xi$. -/
def liftB (ξ : Fin 3 → ℝ) : Fin 4 → ℝ := ![ξ 0, ξ 1, ξ 2, 1]

/-- **The projection** $(\xi_j) = (x_j/x_3)_{j \le 2}$ of (9.2). -/
noncomputable def projB (Y : Fin 4 → ℝ) : Fin 3 → ℝ := ![Y 0 / Y 3, Y 1 / Y 3, Y 2 / Y 3]

/-- **The fractional-linear transformation of $\mathbb{R}^3$ given by a $4 \times 4$ matrix $T$**:
$\vec\xi \mapsto \pi(T(\xi_0, \xi_1, \xi_2, 1))$ (the analogue of `flt` for the ball, §9 (9.2); generalizes the
pattern of `Reduction.flt`/`actD` for the disc). -/
noncomputable def fltB (T : Matrix (Fin 4) (Fin 4) ℝ) (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  projB (T *ᵥ liftB ξ)

theorem dot_lor4 (x : Fin 4 → ℝ) : x ⬝ᵥ (lor4 *ᵥ x) = q4 x := by
  simp [lor4, q4, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four]; ring

theorem lor4_transpose : lor4ᵀ = lor4 := by simp [lor4]

theorem quadForm_conj_mulVec {n : Type*} [Fintype n] (F T : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ ((Tᵀ * F * T) *ᵥ x) = (T *ᵥ x) ⬝ᵥ (F *ᵥ (T *ᵥ x)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem q4_mulVec {T : Matrix (Fin 4) (Fin 4) ℝ} (hT : Tᵀ * lor4 * T = lor4) (x : Fin 4 → ℝ) :
    q4 (T *ᵥ x) = q4 x := by
  rw [← dot_lor4, ← dot_lor4, ← quadForm_conj_mulVec, hT]

theorem liftB_projB {Y : Fin 4 → ℝ} (h : Y 3 ≠ 0) : liftB (projB Y) = (Y 3)⁻¹ • Y := by
  ext i; fin_cases i <;> simp [liftB, projB] <;> field_simp

theorem projB_liftB (ξ : Fin 3 → ℝ) : projB (liftB ξ) = ξ := by
  ext i; fin_cases i <;> simp [liftB, projB]

theorem projB_smul {Y : Fin 4 → ℝ} {c : ℝ} (hc : c ≠ 0) : projB (c • Y) = projB Y := by
  ext i; fin_cases i <;> simp [projB] <;> field_simp

theorem q4_liftB (ξ : Fin 3 → ℝ) : q4 (liftB ξ) = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 - 1 := by
  simp [q4, liftB]

theorem ball_map {T : Matrix (Fin 4) (Fin 4) ℝ} (hT : Tᵀ * lor4 * T = lor4) {ξ : Fin 3 → ℝ}
    (hξ : ξ ∈ ball) : (T *ᵥ liftB ξ) 3 ≠ 0 ∧ fltB T ξ ∈ ball := by
  have h := q4_mulVec hT (liftB ξ)
  rw [q4_liftB] at h
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 < 1 := hξ
  set Y := T *ᵥ liftB ξ with hY
  have hlt : Y 0 ^ 2 + Y 1 ^ 2 + Y 2 ^ 2 < Y 3 ^ 2 := by unfold q4 at h; nlinarith
  have h3 : Y 3 ≠ 0 := by
    intro h0; rw [h0] at hlt; nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1), sq_nonneg (Y 2)]
  refine ⟨h3, ?_⟩
  have hpos : 0 < Y 3 ^ 2 := by positivity
  show (Y 0 / Y 3) ^ 2 + (Y 1 / Y 3) ^ 2 + (Y 2 / Y 3) ^ 2 < 1
  rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, div_lt_one hpos]
  exact hlt

theorem fltB_mul {T T' : Matrix (Fin 4) (Fin 4) ℝ} {ξ : Fin 3 → ℝ} (h1 : (T' *ᵥ liftB ξ) 3 ≠ 0) :
    fltB T (fltB T' ξ) = fltB (T * T') ξ := by
  unfold fltB
  rw [show liftB (projB (T' *ᵥ liftB ξ)) = _ from liftB_projB h1, Matrix.mulVec_smul,
    projB_smul (inv_ne_zero h1), Matrix.mulVec_mulVec]


/-- Helper: membership in `realAut lor4`. -/
theorem mem_realAut_lor4 {T : GL (Fin 4) ℝ} : T ∈ realAut lor4 ↔ T.valᵀ * lor4 * T.val = lor4 := Iff.rfl

/-- Helper: the permutation of the ball induced by `T`. -/
noncomputable def ballPerm (T : realAut lor4) : Equiv.Perm ball where
  toFun ξ := ⟨fltB T.1.val ξ, (ball_map (mem_realAut_lor4.1 T.2) ξ.2).2⟩
  invFun ξ := ⟨fltB (T⁻¹).1.val ξ, (ball_map (mem_realAut_lor4.1 (T⁻¹).2) ξ.2).2⟩
  left_inv ξ := by
    apply Subtype.ext
    have h : ((T⁻¹ : ↥(realAut lor4)).1).val * T.1.val = 1 := by
      rw [Subgroup.coe_inv]; exact Units.inv_mul T.1
    show fltB (T⁻¹).1.val (fltB T.1.val ξ) = ξ
    rw [fltB_mul (ball_map (mem_realAut_lor4.1 T.2) ξ.2).1, h]
    simp [fltB, projB_liftB]
  right_inv ξ := by
    apply Subtype.ext
    have h : T.1.val * ((T⁻¹ : ↥(realAut lor4)).1).val = 1 := by
      rw [Subgroup.coe_inv]; exact Units.mul_inv T.1
    show fltB T.1.val (fltB (T⁻¹).1.val ξ) = ξ
    rw [fltB_mul (ball_map (mem_realAut_lor4.1 (T⁻¹).2) ξ.2).1, h]
    simp [fltB, projB_liftB]

/-- **$O_{\mathbb{R}}(f_{3,1})$ acts on the ball $\mathcal{B}$ by fractional-linear transformations**
(Cassels, Ch. 13, §9, p. 317: "The $T \in O^+_{\mathbb{R}}(f)$ act as fractional-linear transformations of $\mathcal{B}$
onto itself"): the homomorphism $O_{\mathbb{R}}(f_{3,1}) \to \mathrm{Perm}(\mathcal{B})$ with
$T(\vec\xi) = \pi(T(\xi_0, \xi_1, \xi_2, 1))$ (`ballAct_apply`); each $T$ maps $\mathcal{B}$ bijectively onto itself.
It is stated for all of $O_{\mathbb{R}}(f)$, which contains $O^+_{\mathbb{R}}(f)$ (`realAutPlus`). -/
@[kb "cassels1978" "Ch. 13, §9, p. 317 (O_ℝ(f) acts on ℬ by fractional-linear maps)"]
noncomputable def ballAct : realAut lor4 →* Equiv.Perm ball where
  toFun := ballPerm
  map_one' := by
    refine Equiv.ext fun ξ => Subtype.ext ?_
    show fltB (1 : GL (Fin 4) ℝ).val ξ = ξ
    simp [fltB, projB_liftB]
  map_mul' T T' := by
    refine Equiv.ext fun ξ => Subtype.ext ?_
    show fltB (T * T' : ↥(realAut lor4)).1.val ξ = fltB T.1.val (fltB T'.1.val ξ)
    rw [fltB_mul (ball_map (mem_realAut_lor4.1 T'.2) ξ.2).1]
    rfl

/-- The action `ballAct` is the fractional-linear map $\vec\xi \mapsto \pi(T(\xi_0, \xi_1, \xi_2, 1))$ of (9.2). -/
@[kb "cassels1978" "Ch. 13, §9, p. 317 (the action is ξ ↦ π(T(ξ,1)))"]
theorem ballAct_apply (T : realAut lor4) (ξ : ball) : (ballAct T ξ : Fin 3 → ℝ) = fltB T.1.val ξ := rfl


/-- Helper (polarization): a symmetric matrix with vanishing quadratic form is zero. -/
theorem symm_eq_zero_of_quad_zero {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (hM : Mᵀ = M)
    (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = 0) : M = 0 := by
  ext i j
  have key : ∀ a b : n, (Pi.single a (1 : ℝ)) ⬝ᵥ (M *ᵥ (Pi.single b 1)) = M a b := by
    intro a b; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have h2 := h (Pi.single i 1)
  have h3 := h (Pi.single j 1)
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, key] at h1 h2 h3
  have hji : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [transpose_apply] using this
  simp only [Matrix.zero_apply]
  linarith

/-- Helper: a linear map preserving $f_{3,1}$ as a function satisfies $T^{\mathsf T}\texttt{lor4}\,T = \texttt{lor4}$. -/
theorem automorph_of_quad {T : Matrix (Fin 4) (Fin 4) ℝ} (h : ∀ x, q4 (T *ᵥ x) = q4 x) :
    Tᵀ * lor4 * T = lor4 := by
  have hs : (Tᵀ * lor4 * T - lor4)ᵀ = Tᵀ * lor4 * T - lor4 := by
    simp [Matrix.transpose_mul, lor4_transpose, Matrix.mul_assoc]
  have := symm_eq_zero_of_quad_zero _ hs (fun x => by
    rw [Matrix.sub_mulVec, dotProduct_sub, quadForm_conj_mulVec, dot_lor4, dot_lor4, h x, sub_self])
  exact sub_eq_zero.1 this


/-- Helper: $X(0,0,0,1) = I$. -/
theorem hermOf_e4 : hermOf ![0, 0, 0, 1] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hermOf]

/-- Helper: the Hermitian matrix $X(\vec x)$ determines $\vec x$. -/
theorem hermOf_inj {x y : Fin 4 → ℝ} (h : hermOf x = hermOf y) : x = y := by
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  have h01r := congrArg Complex.re h01
  have h01i := congrArg Complex.im h01
  simp [hermOf] at h00 h11 h01r h01i
  have h00' : x 3 + x 0 = y 3 + y 0 := by exact_mod_cast h00
  have h11' : x 3 - x 0 = y 3 - y 0 := by exact_mod_cast h11
  ext i; fin_cases i <;> simp <;> linarith

/-- **The group $\Theta$ of the automorphs $T(A)$ of $f_{3,1}$** (Cassels, Ch. 13, §9, (9.5)–(9.9), pp. 317–318):
$T \in \mathrm{GL}_4(\mathbb{R})$ lies in $\Theta$ iff there is a complex $2 \times 2$ matrix $A$ with $\det A = 1$ and
$X(T\vec x) = AX(\vec x)A^{*}$ for all real $\vec x$ (`hermOf` is the Hermitian matrix of (9.4), $A^{*}$ = `Aᴴ`).
*Convention.* Cassels allows $|\det A| = 1$ (9.6) and writes the substitution as $X \mapsto \bar A'XA$ (9.8); a
unimodular scalar multiple of $A$ gives the same $T$, so $\det A = 1$ is no loss, and replacing $A$ by $A^{*}$
interchanges the two forms of the unitary condition $AA^{*} = I$ and $A^{*}A = I$. By `exists_automorph_hermOf`
every $A$ of determinant $1$ gives an element of $\Theta$ (`theta_transitive`'s proof uses it), and
`theta_le_realAutPlus` shows $\Theta \le O^+_{\mathbb{R}}(f_{3,1})$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.5)–(9.9), pp. 317–318 (the group Θ)"]
def thetaGrp : Subgroup (GL (Fin 4) ℝ) where
  carrier := {T | ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
    ∀ x, hermOf (T.val *ᵥ x) = A * hermOf x * Aᴴ}
  mul_mem' := by
    rintro T T' ⟨A, hA, hT⟩ ⟨A', hA', hT'⟩
    refine ⟨A * A', by rw [Matrix.det_mul, hA, hA', one_mul], fun x => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hT, hT']
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, by simp, fun x => by simp⟩
  inv_mem' := by
    rintro T ⟨A, hA, hT⟩
    have hu : IsUnit A.det := by rw [hA]; exact isUnit_one
    refine ⟨A⁻¹, by rw [Matrix.det_nonsing_inv, hA]; simp, fun x => ?_⟩
    have e := hT ((T⁻¹).val *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at e
    have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hu
    have h2 : Aᴴ * (A⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc hermOf ((T⁻¹).val *ᵥ x) = (A⁻¹ * A) * hermOf ((T⁻¹).val *ᵥ x) * (Aᴴ * (A⁻¹)ᴴ) := by
          rw [h1, h2]; simp
      _ = A⁻¹ * (A * hermOf ((T⁻¹).val *ᵥ x) * Aᴴ) * (A⁻¹)ᴴ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * hermOf x * (A⁻¹)ᴴ := by rw [← e]

/-- Helper: $T \in \Theta$ preserves $f_{3,1}$ ($\det X(\vec x) = -f_{3,1}(\vec x)$ and $|\det A| = 1$). -/
theorem q4_of_theta {T : GL (Fin 4) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1)
    (hT : ∀ x, hermOf (T.val *ᵥ x) = A * hermOf x * Aᴴ) (x : Fin 4 → ℝ) :
    q4 (T.val *ᵥ x) = q4 x := by
  have h := congrArg Matrix.det (hT x)
  rw [det_hermOf, Matrix.det_mul, Matrix.det_mul, hA, det_hermOf, Matrix.det_conjTranspose, hA] at h
  simp at h
  unfold q4
  have h' : (T.val *ᵥ x) 3 ^ 2 - ((T.val *ᵥ x) 0 ^ 2 + (T.val *ᵥ x) 1 ^ 2 + (T.val *ᵥ x) 2 ^ 2) =
      x 3 ^ 2 - (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by exact_mod_cast h
  linarith

/-- Helper: $\det T = 1$ for $T \in \Theta$ (uniqueness of $T(A)$, and `exists_automorph_hermOf`). -/
theorem theta_det {T : GL (Fin 4) ℝ} (hT : T ∈ thetaGrp) : T.val.det = 1 := by
  obtain ⟨A, hA, hTA⟩ := hT
  obtain ⟨T₀, h₀, -, hd, -⟩ := exists_automorph_hermOf hA
  have : T.val = T₀ := by
    ext i j
    have := hermOf_inj ((hTA (Pi.single j 1)).trans (h₀ (Pi.single j 1)).symm)
    have := congrFun this i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  rw [this, hd]

/-- **$\Theta$ is a subgroup of $O^+_{\mathbb{R}}(f_{3,1})$** (Cassels, Ch. 13, §9, p. 318: "The set of $\mathbf{T}(\mathbf{A})$
form a subgroup $\Theta$ of ... $O^+_{\mathbb{R}}(f)$"; the "finite index" part is not formalized, see the module
header): every $T(A)$ is a real automorph of determinant $+1$. -/
@[kb "cassels1978" "Ch. 13, §9, p. 318 (Θ is a subgroup of O⁺_ℝ(f))"]
theorem theta_le_realAutPlus : thetaGrp ≤ realAutPlus lor4 := by
  intro T hT
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA, hTA⟩ := hT
    exact automorph_of_quad (q4_of_theta hA hTA)
  · show Matrix.GeneralLinearGroup.det T = 1
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simpa using theta_det hT

/-- **The $A$ stabilizing $(0,0,0,1)$ are the unitary ones** (Cassels, Ch. 13, §9, p. 318: "The $\mathbf{A}$ stabilizing
$\mathbf{x} = (0,0,0,1)$ are those with $\bar{\mathbf{A}}'\mathbf{A} = \mathbf{I}$; that is, those in the unitary group
$K$"): if $X(T\vec x) = AX(\vec x)A^{*}$ for all $\vec x$ then $T$ fixes the vector $(0,0,0,1)$ iff $AA^{*} = I$ (with
the book's convention for $T(A)$ interchanged, $A^{*}A = I$; the two are equivalent for square matrices). -/
@[kb "cassels1978" "Ch. 13, §9, p. 318 (the stabilizer of (0,0,0,1) is the unitary group)"]
theorem theta_stabilizer {T : GL (Fin 4) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hT : ∀ x, hermOf (T.val *ᵥ x) = A * hermOf x * Aᴴ) :
    T.val *ᵥ ![0, 0, 0, 1] = ![0, 0, 0, 1] ↔ A * Aᴴ = 1 := by
  constructor
  · intro h
    have := hT ![0, 0, 0, 1]
    rw [h, hermOf_e4, mul_one] at this
    exact this.symm
  · intro h
    apply hermOf_inj
    rw [hT, hermOf_e4, mul_one, h]


theorem liftB_zero : liftB 0 = ![0, 0, 0, 1] := by
  ext i; fin_cases i <;> simp [liftB]

/-- Helper: every point of $\mathcal{B}$ is the image of the origin $(0,0,0)$ under some $T(A)$, $\det A = 1$
(Cholesky factor $A$ of the Hermitian matrix of $\gamma(\xi, 1)$, $\gamma = (1 - |\vec\xi|^2)^{-1/2}$). -/
theorem exists_theta_boost {ξ : Fin 3 → ℝ} (hξ : ξ ∈ ball) :
    ∃ T ∈ thetaGrp, fltB T.val 0 = ξ := by
  have hξ' : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 < 1 := hξ
  have hu : 0 < 1 - (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) := by linarith
  set γ : ℝ := (√(1 - (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)))⁻¹ with hγ
  have hγpos : 0 < γ := inv_pos.2 (Real.sqrt_pos.2 hu)
  have hγ2 : γ ^ 2 * (1 - (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) = 1 := by
    rw [hγ, inv_pow, Real.sq_sqrt hu.le]; field_simp
  set y : Fin 4 → ℝ := γ • liftB ξ with hy
  have hy0 : y 0 = γ * ξ 0 := by simp [hy, liftB]
  have hy1 : y 1 = γ * ξ 1 := by simp [hy, liftB]
  have hy2 : y 2 = γ * ξ 2 := by simp [hy, liftB]
  have hy3 : y 3 = γ := by simp [hy, liftB]
  have hq : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - y 3 ^ 2 = -1 := by
    rw [hy0, hy1, hy2, hy3]; nlinarith [hγ2]
  have hξ0 : 0 < 1 + ξ 0 := by nlinarith [sq_nonneg (ξ 1), sq_nonneg (ξ 2), sq_nonneg (ξ 0 + 1)]
  have hs : 0 < y 3 + y 0 := by rw [hy0, hy3]; nlinarith
  set p : ℝ := √(y 3 + y 0) with hp
  have hppos : 0 < p := Real.sqrt_pos.2 hs
  have hp2 : p ^ 2 = y 3 + y 0 := Real.sq_sqrt hs.le
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hppos.ne'
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![(p : ℂ), 0; ((y 1 : ℂ) - (y 2 : ℂ) * Complex.I) / p, (p : ℂ)⁻¹] with hA
  have hdet : A.det = 1 := by
    rw [hA, Matrix.det_fin_two_of]; field_simp; simp
  have hq' : (y 0 : ℂ) ^ 2 + (y 1 : ℂ) ^ 2 + (y 2 : ℂ) ^ 2 - (y 3 : ℂ) ^ 2 = -1 := by exact_mod_cast hq
  have hp2' : (p : ℂ) ^ 2 = (y 3 : ℂ) + (y 0 : ℂ) := by exact_mod_cast hp2
  have hAA : A * Aᴴ = hermOf y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, hermOf, map_div₀,
        Complex.conj_ofReal]
    · rw [← sq]; exact hp2'
    · field_simp
    · field_simp
    · field_simp
      rw [hp2']
      linear_combination hq' + (-(y 2 : ℂ) ^ 2) * Complex.I_sq
  obtain ⟨T, hT, -, hdetT, -⟩ := exists_automorph_hermOf hdet
  have hTy : T *ᵥ ![0, 0, 0, 1] = y := by
    apply hermOf_inj
    rw [hT, hermOf_e4, mul_one, hAA]
  have hdU : IsUnit T.det := by rw [hdetT]; exact isUnit_one
  refine ⟨Matrix.nonsingInvUnit T hdU, ⟨A, hdet, hT⟩, ?_⟩
  show projB (T *ᵥ liftB 0) = ξ
  rw [liftB_zero, hTy, hy]
  ext i; fin_cases i <;> simp [projB, liftB] <;> field_simp


/-- Helper: the origin lies in $\mathcal{B}$. -/
theorem zero_mem_ball3 : (0 : Fin 3 → ℝ) ∈ ball := by simp [ball]

/-- **$\Theta$ acts transitively on $\mathcal{B}$** (Cassels, Ch. 13, §9, p. 318: "$\Theta$ acts transitively on
$\mathcal{B}$"): for any two points $\vec\xi, \vec\eta$ of the open unit ball there is $T \in \Theta$ with
$T(\vec\xi) = \vec\eta$ (the fractional-linear action `fltB`; it agrees with `ballAct` since $\Theta \le
O_{\mathbb{R}}(f)$). Together with `theta_point_stabilizer` this identifies $\mathcal{B}$ with $G/K$,
$G = \{A : \det A = 1\}$ and $K$ the unitary group. -/
@[kb "cassels1978" "Ch. 13, §9, p. 318 (Θ acts transitively on ℬ)"]
theorem theta_transitive {ξ η : Fin 3 → ℝ} (hξ : ξ ∈ ball) (hη : η ∈ ball) :
    ∃ T ∈ thetaGrp, fltB T.val ξ = η := by
  obtain ⟨Tξ, hTξ, e1⟩ := exists_theta_boost hξ
  obtain ⟨Tη, hTη, e2⟩ := exists_theta_boost hη
  refine ⟨Tη * Tξ⁻¹, thetaGrp.mul_mem hTη (thetaGrp.inv_mem hTξ), ?_⟩
  have hξr : Tξ ∈ realAut lor4 := (theta_le_realAutPlus hTξ).1
  have hξr' : Tξ⁻¹ ∈ realAut lor4 := (realAut lor4).inv_mem hξr
  have h0 : fltB (Tξ⁻¹).val ξ = 0 := by
    rw [← e1, fltB_mul (ball_map (mem_realAut_lor4.1 hξr) zero_mem_ball3).1, Units.inv_mul]
    simp [fltB, projB_liftB]
  rw [Units.val_mul, ← fltB_mul (ball_map (mem_realAut_lor4.1 hξr') hξ).1, h0, e2]

/-- **The stabilizer of the origin of $\mathcal{B}$ in $\Theta$ is the unitary group** (Cassels, Ch. 13, §9, p. 318): for
$T \in \Theta$ with $X(T\vec x) = AX(\vec x)A^{*}$ and $\det A = 1$, $T(\vec 0) = \vec 0$ (as a point of $\mathcal{B}$,
i.e. $T$ fixes the line of $(0,0,0,1)$) iff $AA^{*} = I$. (Stronger than `theta_stabilizer`, which is about the
vector.) -/
@[kb "cassels1978" "Ch. 13, §9, p. 318 (stabilizer of the origin of ℬ)"]
theorem theta_point_stabilizer {T : GL (Fin 4) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1)
    (hT : ∀ x, hermOf (T.val *ᵥ x) = A * hermOf x * Aᴴ) :
    fltB T.val 0 = 0 ↔ A * Aᴴ = 1 := by
  constructor
  · intro h
    have h' : projB (T.val *ᵥ ![0, 0, 0, 1]) = 0 := by rw [← liftB_zero]; exact h
    have hq := q4_of_theta hA hT ![0, 0, 0, 1]
    have hq4e : q4 ![0, 0, 0, 1] = -1 := by simp [q4]
    rw [hq4e] at hq
    set Y := T.val *ᵥ ![0, 0, 0, 1] with hY
    have hY3 : Y 3 ≠ 0 := by
      intro h0; unfold q4 at hq; rw [h0] at hq
      nlinarith [sq_nonneg (Y 0), sq_nonneg (Y 1), sq_nonneg (Y 2)]
    have hi : ∀ i : Fin 3, Y i.castSucc = 0 := by
      intro i
      have := congrFun h' i
      fin_cases i <;> simpa [projB, hY3] using this
    have hY0 := hi 0
    have hY1 := hi 1
    have hY2 := hi 2
    simp only [Fin.castSucc_zero, Fin.castSucc_one] at hY0 hY1
    have hY2' : Y 2 = 0 := by simpa using hY2
    have hsq : Y 3 ^ 2 = 1 := by unfold q4 at hq; rw [hY0, hY1, hY2'] at hq; nlinarith
    have e := hT ![0, 0, 0, 1]
    rw [hermOf_e4, mul_one] at e
    have e00 := congrFun (congrFun e 0) 0
    simp [hermOf, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.mul_conj] at e00
    have hnn : 0 ≤ Y 3 := by
      have := congrArg Complex.re e00
      simp at this
      rw [← hY, hY0] at this
      linarith [Complex.normSq_nonneg (A 0 0), Complex.normSq_nonneg (A 0 1)]
    have hY33 : Y 3 = 1 := by nlinarith
    have hYe : Y = ![0, 0, 0, 1] := by
      ext i; fin_cases i <;> simp [hY0, hY1, hY2', hY33]
    exact (theta_stabilizer hT).1 hYe
  · intro h
    have := (theta_stabilizer hT).2 h
    show projB (T.val *ᵥ liftB 0) = 0
    rw [liftB_zero, this]
    ext i; fin_cases i <;> simp [projB]


/-! ### §9: the form $f_{2,2}$ (pp. 318–319) -/

/-- **The matrix $X$ of (9.11)** (Cassels, Ch. 13, §9, p. 318): $\det X(\vec x) = f_{2,2}(\vec x) =
x_0^2 + x_1^2 - x_2^2 - x_3^2$ (9.10), in 0-based form
$X = \begin{pmatrix} x_0 + x_2 & x_3 + x_1\\ x_3 - x_1 & x_0 - x_2\end{pmatrix}$. -/
@[kb "cassels1978" "Ch. 13, §9, (9.10)–(9.11), p. 318 (the matrix X of f_{2,2})"]
def X22 (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x 0 + x 2, x 3 + x 1; x 3 - x 1, x 0 - x 2]

/-- **(9.10)–(9.11)**: $\det X(\vec x) = x_0^2 + x_1^2 - x_2^2 - x_3^2 = f_{2,2}(\vec x)$. -/
theorem det_X22 (x : Fin 4 → ℝ) : (X22 x).det = x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2 := by
  simp [X22, Matrix.det_fin_two_of]; ring

/-- Helper: the coordinates $\vec x$ with $X(\vec x) = Y$. -/
noncomputable def coord22 (Y : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → ℝ :=
  ![(Y 0 0 + Y 1 1) / 2, (Y 0 1 - Y 1 0) / 2, (Y 0 0 - Y 1 1) / 2, (Y 0 1 + Y 1 0) / 2]

theorem X22_coord22 (Y : Matrix (Fin 2) (Fin 2) ℝ) : X22 (coord22 Y) = Y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X22, coord22] <;> ring

theorem coord22_X22 (x : Fin 4 → ℝ) : coord22 (X22 x) = x := by
  ext i; fin_cases i <;> simp [X22, coord22]

/-- Helper: the real $4 \times 4$ matrix of $X \mapsto AXB^{\mathsf T}$ in the coordinates of (9.11) (so that
$T(A, B^{\mathsf T})$ of (9.13) is `T22 A Bᵀ`; the transpose makes `T22` multiplicative in $(A, B)$). -/
noncomputable def T22 (A B : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => coord22 (A * X22 (Pi.single j 1) * Bᵀ) i

theorem T22_mulVec (A B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 4 → ℝ) :
    T22 A B *ᵥ x = coord22 (A * X22 x * Bᵀ) := by
  ext i
  fin_cases i <;>
  · simp [T22, coord22, Matrix.mulVec, dotProduct, Fin.sum_univ_four, X22, Matrix.mul_apply,
      Fin.sum_univ_two, Pi.single_apply]
    ring

theorem X22_T22 (A B : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 4 → ℝ) :
    X22 (T22 A B *ᵥ x) = A * X22 x * Bᵀ := by
  rw [T22_mulVec, X22_coord22]

theorem mat_ext_of_mulVec {M N : Matrix (Fin 4) (Fin 4) ℝ} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem T22_mul (A B A' B' : Matrix (Fin 2) (Fin 2) ℝ) :
    T22 (A * A') (B * B') = T22 A B * T22 A' B' := by
  apply mat_ext_of_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, T22_mulVec, T22_mulVec, T22_mulVec, X22_coord22]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

theorem T22_one : T22 1 1 = 1 := by
  apply mat_ext_of_mulVec
  intro x
  rw [T22_mulVec, Matrix.one_mulVec]
  simp [coord22_X22]

/-- Helper: the homomorphism $SL_2(\mathbb{R}) \times SL_2(\mathbb{R}) \to \mathrm{GL}_4(\mathbb{R})$,
$(A, B) \mapsto [X \mapsto AXB^{\mathsf T}]$. -/
noncomputable def psi22 : Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ →*
    GL (Fin 4) ℝ :=
  MonoidHom.toHomUnits
    { toFun := fun g => T22 g.1.1 g.2.1
      map_one' := T22_one
      map_mul' := fun g g' => by
        simp only [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact T22_mul _ _ _ _ }

theorem psi22_val (g : Matrix.SpecialLinearGroup (Fin 2) ℝ × Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (psi22 g).val = T22 g.1.1 g.2.1 := rfl


/-- **The group $\Theta$ for $f_{2,2}$** (Cassels, Ch. 13, §9, (9.12)–(9.13), p. 318): the $T \in \mathrm{GL}_4(\mathbb{R})$
for which there are real $2 \times 2$ matrices $A, B$ with $\det A = \det B = 1$ and $X(T\vec x) = AX(\vec x)B$ for
all $\vec x$; these $T(A, B)$ are real automorphs of $f_{2,2}$ (`det_mul_mul_eq`). (The finite-index statement is
not formalized, see the module header.) -/
@[kb "cassels1978" "Ch. 13, §9, (9.12)–(9.13), p. 318 (the group Θ for f_{2,2})"]
def theta22 : Subgroup (GL (Fin 4) ℝ) where
  carrier := {T | ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A.det = 1 ∧ B.det = 1 ∧
    ∀ x, X22 (T.val *ᵥ x) = A * X22 x * B}
  mul_mem' := by
    rintro T T' ⟨A, B, hA, hB, h⟩ ⟨A', B', hA', hB', h'⟩
    refine ⟨A * A', B' * B, by rw [Matrix.det_mul, hA, hA', one_mul],
      by rw [Matrix.det_mul, hB, hB', one_mul], fun x => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, h']
    simp [Matrix.mul_assoc]
  one_mem' := ⟨1, 1, by simp, by simp, fun x => by simp⟩
  inv_mem' := by
    rintro T ⟨A, B, hA, hB, h⟩
    have hAu : IsUnit A.det := by rw [hA]; exact isUnit_one
    have hBu : IsUnit B.det := by rw [hB]; exact isUnit_one
    refine ⟨A⁻¹, B⁻¹, by rw [Matrix.det_nonsing_inv, hA]; simp,
      by rw [Matrix.det_nonsing_inv, hB]; simp, fun x => ?_⟩
    have e := h ((T⁻¹).val *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at e
    calc X22 ((T⁻¹).val *ᵥ x) = (A⁻¹ * A) * X22 ((T⁻¹).val *ᵥ x) * (B * B⁻¹) := by
          rw [Matrix.nonsing_inv_mul A hAu, Matrix.mul_nonsing_inv B hBu]; simp
      _ = A⁻¹ * (A * X22 ((T⁻¹).val *ᵥ x) * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * X22 x * B⁻¹ := by rw [← e]

/-- Helper: $\operatorname{Tr}X(\vec x)^{\mathsf T}X(\vec x) = 2(x_0^2 + x_1^2 + x_2^2 + x_3^2)$ (9.14). -/
noncomputable def trX (x : Fin 4 → ℝ) : ℝ := ((X22 x)ᵀ * X22 x).trace

/-- Helper: the subgroup of $\mathrm{GL}_4$ preserving $\operatorname{Tr}X^{\mathsf T}X$ (9.14). -/
noncomputable def traceStab : Subgroup (GL (Fin 4) ℝ) where
  carrier := {T | ∀ x, trX (T.val *ᵥ x) = trX x}
  mul_mem' := fun {T T'} h h' x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]; exact (h _).trans (h' x)
  one_mem' := fun x => by simp
  inv_mem' := fun {T} h x => by
    have := h ((T⁻¹).val *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

/-- **The subgroup $K$ of $\Theta$ for $f_{2,2}$** (Cassels, Ch. 13, §9, (9.14), p. 318): the elements of $\Theta$ which
preserve $\operatorname{Trace}X^{\mathsf T}X = 2(x_0^2 + x_1^2 + x_2^2 + x_3^2)$; it lies in the orthogonal group of
$x_0^2 + \cdots + x_3^2$, hence is compact. -/
@[kb "cassels1978" "Ch. 13, §9, (9.14), p. 318 (the subgroup K of Θ for f_{2,2})"]
noncomputable def K22 : Subgroup (GL (Fin 4) ℝ) := theta22 ⊓ traceStab

/-- $SL_2(\mathbb{R})$ (Cassels' $SL^{+}_2$, real $2 \times 2$ matrices of determinant $1$). -/
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- **$K_2$** (Cassels, Ch. 13, §9, p. 319): the $A \in SL_2(\mathbb{R})$ with $A^{\mathsf T}A = I$; the group $K^{+}$ of
Lemma 7.2 (`kPM` restricted to $SL_2$). -/
def K2 : Subgroup SL2R := kPM.comap Matrix.SpecialLinearGroup.toGL

/-- Helper: the image of $\psi$ lies in $\Theta$. -/
theorem psi22_mem (g : SL2R × SL2R) : psi22 g ∈ theta22 :=
  ⟨g.1.1, g.2.1ᵀ, g.1.2, by simp, fun x => by rw [psi22_val, X22_T22]⟩

/-- Helper: $\psi$ maps onto $\Theta$. -/
theorem psi22_surj (T : theta22) : ∃ g : SL2R × SL2R, psi22 g = T := by
  obtain ⟨A, B, hA, hB, h⟩ := T.2
  refine ⟨(⟨A, hA⟩, ⟨Bᵀ, by simp [hB]⟩), ?_⟩
  apply Units.ext
  apply mat_ext_of_mulVec
  intro x
  rw [psi22_val, T22_mulVec]
  simp only [Matrix.transpose_transpose]
  rw [← h, coord22_X22]

/-- Helper: $\psi(A, B) \in K$ iff $A, B \in K_2$ (this is `trace_preserved_iff`, (9.15)–(9.16)). -/
theorem psi22_mem_K22_iff (g : SL2R × SL2R) : psi22 g ∈ K22 ↔ g ∈ K2.prod K2 := by
  rw [Subgroup.mem_prod]
  have hmem : psi22 g ∈ K22 ↔ psi22 g ∈ traceStab := ⟨fun h => h.2, fun h => ⟨psi22_mem g, h⟩⟩
  rw [hmem]
  have key : psi22 g ∈ traceStab ↔ ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      ((g.1.1 * X * g.2.1ᵀ)ᵀ * (g.1.1 * X * g.2.1ᵀ)).trace = (Xᵀ * X).trace := by
    constructor
    · intro h X
      have := h (coord22 X)
      simp only [trX, psi22_val, X22_T22, X22_coord22] at this
      exact this
    · intro h x
      simp only [trX, psi22_val, X22_T22]
      exact h _
  rw [key, trace_preserved_iff g.1.2 (by simp)]
  simp only [Matrix.transpose_transpose]
  exact Iff.rfl


/-- **$\Theta/K$ is a product of two copies of $SL_2(\mathbb{R})/K_2$** (Cassels, Ch. 13, §9, p. 319: "We have thus
identified $\Theta/K$ with the product of two copies of $SL^{+}_2/K_2$"): the coset space $\Theta/K$ of the
automorphs $T(A, B)$ of $f_{2,2}$ modulo those preserving $\operatorname{Tr}X^{\mathsf T}X$ is in bijection with
$(SL_2(\mathbb{R})/K_2) \times (SL_2(\mathbb{R})/K_2)$ (left cosets), $K_2 = \{A : A^{\mathsf T}A = I\}$. The bijection
comes from the surjection $(A, B) \mapsto T(A, B^{\mathsf T})$ of $SL_2 \times SL_2$ onto $\Theta$, under which $K$ pulls
back to $K_2 \times K_2$ (the necessity of (9.16) is `trace_preserved_iff`). -/
@[kb "cassels1978" "Ch. 13, §9, pp. 318–319 (Θ/K is two copies of SL₂⁺/K₂)"]
theorem theta22_quotient :
    Nonempty (↥theta22 ⧸ K22.subgroupOf theta22 ≃ (SL2R ⧸ K2) × (SL2R ⧸ K2)) := by
  let ψ : SL2R × SL2R →* theta22 := psi22.codRestrict theta22 psi22_mem
  have hψ : ∀ g, ((ψ g : theta22) : GL (Fin 4) ℝ) = psi22 g := fun g => rfl
  have hpre : ∀ g, ψ g ∈ K22.subgroupOf theta22 ↔ g ∈ K2.prod K2 := fun g => by
    rw [Subgroup.mem_subgroupOf, hψ]; exact psi22_mem_K22_iff g
  have hsurj : Function.Surjective ψ := fun T => by
    obtain ⟨g, hg⟩ := psi22_surj T
    exact ⟨g, Subtype.ext (by rw [hψ, hg])⟩
  let f : (SL2R × SL2R) ⧸ (K2.prod K2) → ↥theta22 ⧸ K22.subgroupOf theta22 := fun q =>
    Quotient.liftOn' q (fun g => (QuotientGroup.mk (ψ g) : ↥theta22 ⧸ K22.subgroupOf theta22))
      (fun a b hab => by
        have h := QuotientGroup.leftRel_apply.1 hab
        apply QuotientGroup.eq.2
        rw [← map_inv, ← map_mul]
        exact (hpre _).2 h)
  have hfm : ∀ g, f (QuotientGroup.mk g) = QuotientGroup.mk (ψ g) := fun g => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      intro h
      rw [hfm, hfm] at h
      have h2 := QuotientGroup.eq.1 h
      rw [QuotientGroup.eq]
      apply (hpre _).1
      rw [map_mul, map_inv]; exact h2
    · intro q
      induction q using QuotientGroup.induction_on with | H t => ?_
      obtain ⟨g, hg⟩ := hsurj t
      exact ⟨QuotientGroup.mk g, by rw [hfm, hg]⟩
  let u : (SL2R × SL2R) ⧸ (K2.prod K2) → (SL2R ⧸ K2) × (SL2R ⧸ K2) := fun q =>
    Quotient.liftOn' q (fun g => ((QuotientGroup.mk g.1 : SL2R ⧸ K2), (QuotientGroup.mk g.2 : SL2R ⧸ K2)))
      (fun a b hab => by
        have h := Subgroup.mem_prod.1 (QuotientGroup.leftRel_apply.1 hab)
        exact Prod.ext (QuotientGroup.eq.2 h.1) (QuotientGroup.eq.2 h.2))
  have hum : ∀ g, u (QuotientGroup.mk g) = (QuotientGroup.mk g.1, QuotientGroup.mk g.2) := fun g => rfl
  have hu : Function.Bijective u := by
    constructor
    · intro a b
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      intro h
      rw [hum, hum] at h
      have h1 := QuotientGroup.eq.1 (Prod.ext_iff.1 h).1
      have h2 := QuotientGroup.eq.1 (Prod.ext_iff.1 h).2
      rw [QuotientGroup.eq]
      exact Subgroup.mem_prod.2 ⟨h1, h2⟩
    · rintro ⟨q1, q2⟩
      induction q1 using QuotientGroup.induction_on with | H a => ?_
      induction q2 using QuotientGroup.induction_on with | H b => ?_
      exact ⟨QuotientGroup.mk (a, b), rfl⟩
  exact ⟨(Equiv.ofBijective f hf).symm.trans (Equiv.ofBijective u hu)⟩


/-- **$\Theta/K$ is the product of two copies of the non-Euclidean plane** (Cassels, Ch. 13, §9, p. 319: "Comparison
with Lemma 7.2, Corollary, shows that $\Theta/K$ is the direct product of two copies of the non-Euclidean plane"):
$\Theta/K \cong \mathcal{D} \times \mathcal{D}$ as sets, by `theta22_quotient` and
`disc_equiv_slPM_quotient` (which identifies $SL_2(\mathbb{R})/K_2$ with the disc $\mathcal{D}$). -/
@[kb "cassels1978" "Ch. 13, §9, p. 319 (Θ/K ≅ 𝒟 × 𝒟)"]
theorem theta22_disc :
    Nonempty (↥theta22 ⧸ K22.subgroupOf theta22 ≃ disc × disc) := by
  obtain ⟨e⟩ := theta22_quotient
  obtain ⟨d⟩ := disc_equiv_slPM_quotient.2
  exact ⟨e.trans (Equiv.prodCongr d d)⟩


/-! ### §11: the Haar measure of $O_{\mathbb{R}}(f)$ -/

/-- Helper: `O_ℝ(F)` is closed in `GL`. -/
theorem realAut_isClosed {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ) :
    IsClosed (realAut F : Set (GL ι ℝ)) := by
  have hc : Continuous fun S : GL ι ℝ => S.valᵀ * F * S.val :=
    ((Units.continuous_val.matrix_transpose).matrix_mul continuous_const).matrix_mul Units.continuous_val
  exact isClosed_eq hc continuous_const

/-- Helper: $\mathrm{GL}_n(\mathbb{R})$ is locally compact. -/
instance glReal_locallyCompact {ι : Type*} [Fintype ι] [DecidableEq ι] : LocallyCompactSpace (GL ι ℝ) := by
  have : LocallyCompactSpace (Matrix ι ι ℝ) := inferInstanceAs (LocallyCompactSpace (ι → ι → ℝ))
  have : T1Space (Matrix ι ι ℝ) := inferInstanceAs (T1Space (ι → ι → ℝ))
  infer_instance

/-- Helper: $\mathrm{GL}_n(\mathbb{R})$ is second countable. -/
instance glReal_secondCountable {ι : Type*} [Fintype ι] [DecidableEq ι] : SecondCountableTopology (GL ι ℝ) := by
  have : SecondCountableTopology (Matrix ι ι ℝ) := inferInstanceAs (SecondCountableTopology (ι → ι → ℝ))
  have : SecondCountableTopology (Matrix ι ι ℝ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- **Haar measure on $O_{\mathbb{R}}(f)$** (Cassels, Ch. 13, §11, p. 324: "the group $O_{\mathbb{R}}(f)$ has not merely a
topology but an invariant (Haar) measure which is unique up to a multiplicative constant"): for the real symmetric
matrix $F$ of a form, the group $O_{\mathbb{R}}(f)$ = `realAut F`, with the topology induced from
$\mathrm{GL}_n(\mathbb{R})$ (the natural topology; it is a closed subgroup, hence locally compact, and second
countable), and any Borel $\sigma$-algebra, (i) has a Haar measure (left invariant, finite on compacta, positive on
open sets), and (ii) any two Haar measures $\mu, \nu$ satisfy $\nu = c\mu$ for a constant $c > 0$. The explicit description of
the measure and the quotient measure of p. 324 are not part of this statement. -/
@[kb "cassels1978" "Ch. 13, §11, p. 324 (Haar measure on O_ℝ(f), unique up to a constant)"]
theorem exists_haar_unique {ι : Type*} [Fintype ι] [DecidableEq ι] (F : Matrix ι ι ℝ)
    [MeasurableSpace (realAut F)] [BorelSpace (realAut F)] :
    (∃ μ : Measure (realAut F), μ.IsHaarMeasure) ∧
      ∀ μ ν : Measure (realAut F), μ.IsHaarMeasure → ν.IsHaarMeasure →
        ∃ c : NNReal, c ≠ 0 ∧ ν = c • μ := by
  have : LocallyCompactSpace (realAut F) :=
    (realAut_isClosed F).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (realAut F) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  refine ⟨⟨Measure.haar, inferInstance⟩, fun μ ν hμ hν => ?_⟩
  have h := Measure.isMulLeftInvariant_eq_smul ν μ
  refine ⟨Measure.haarScalarFactor ν μ, ?_, h⟩
  intro h0
  rw [h0, zero_smul] at h
  have h1 := hν.open_pos Set.univ isOpen_univ Set.univ_nonempty
  rw [h] at h1
  exact h1 (by simp)


end QuadFormsKB.Reduction
