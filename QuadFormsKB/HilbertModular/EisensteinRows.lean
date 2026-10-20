/-
# Hilbert Eisenstein series VI: the Fourier expansion of a row

**Integral weights** (`IntWeight W k 𝔐`): $W$ is unit-equivariant of weight $k$, bounded, supported on $\mathcal{O}_F^2$ and
periodic modulo $\mathfrak M^2$ for an integral ideal $\mathfrak M \ne 0$ ($W(c + m_1, d + m_2) = W(c, d)$ for $m_i \in \mathfrak M$). They are
the weights $w : (\mathcal{O}_F/\mathfrak M)^2 \to \mathbb{C}$ of Diamond–Shurman's $E_{W}$ over $\mathbb{Q}$ (`EisensteinWt2`); e.g. $W_\chi$
(`intWeight_chiWeight`).

**The row expansion** (`hasSum_row`). Fix $c \in F^\times$ and $z = x + iy \in \mathbb{H}^d$, and put $a_v = \sigma_v(c)x_v$,
$h_v = \sigma_v(c)y_v$. For $k \ge 2$, $0 \le s \le 1$, $k + 2s > 2$:
$$\sum_{d\in F}W(c, d)\prod_v\varphi_{k,s}\big(\sigma_v(c)z_v + \sigma_v(d)\big)
  = \sum_{\nu\in\mathfrak M^\vee}c_{\mathfrak M}\,R_W(c, \nu)\prod_vT_{k,s}(\nu_v, h_v)\,e(\langle\nu, a\rangle),$$
$R_W(c, \nu) = \sum_{r\in\mathcal{O}_F/\mathfrak M}W(c, r)\,e(\operatorname{Tr}\nu r)$ (`rowR`, a finite sum), $\mathfrak M^\vee$ the trace dual (the
points $\nu_n$ = `dualVec`), $c_{\mathfrak M}$ = `latConst` (the inverse covolume), $T_{k,s}$ = `lineFT`. *Proof:* split $d = r + m$,
$m \in \mathfrak M$, and apply Poisson summation over $\mathfrak M$ (`hasSum_lattice_fourier`) to the product function
$u \mapsto \prod_v\varphi_{k,s}(a_v + u_v + ih_v)$; its Fourier transform is $\prod_vT_{k,s}(\nu_v, h_v)e(\langle\nu, a\rangle)$ (Fubini), and
it decays exponentially (`norm_lineFT_one_le`). The local uniform summability of the row comes from the orbit majorant
(`exists_summable_bound_rpow`).
-/
import QuadFormsKB.HilbertModular.EisensteinHecke
import QuadFormsKB.HilbertModular.RowPoisson
import QuadFormsKB.HilbertModular.EisensteinChar

open Complex Matrix NumberField UpperHalfPlane Filter Topology MeasureTheory
open scoped MatrixGroups ModularForm nonZeroDivisors Real

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Integral weights -/

/-- **An integral weight of parallel weight $k$ and level $\mathfrak M$**: unit-equivariant, bounded, supported on $\mathcal{O}_F^2$ and
$\mathfrak M^2$-periodic. Fields: `unit`, `supp`, `per`, `bdd`, `ne` ($\mathfrak M \ne 0$). -/
structure IntWeight (W : F × F → ℂ) (k : ℤ) (𝔐 : Ideal (𝓞 F)) : Prop where
  unit : IsUnitEquivariant W k
  supp : ∀ x, W x ≠ 0 → ∃ p : 𝓞 F × 𝓞 F, (algebraMap (𝓞 F) F p.1, algebraMap (𝓞 F) F p.2) = x
  per : ∀ (x : F × F) (m₁ m₂ : 𝓞 F), m₁ ∈ 𝔐 → m₂ ∈ 𝔐 →
    W (x.1 + algebraMap (𝓞 F) F m₁, x.2 + algebraMap (𝓞 F) F m₂) = W x
  bdd : ∃ B : ℝ, ∀ x, ‖W x‖ ≤ B
  ne : 𝔐 ≠ ⊥

lemma IntWeight.eisWeight {W : F × F → ℂ} {k : ℤ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W k 𝔐) :
    EisWeight W k := by
  refine ⟨hW.unit, ⟨1, fun x hx => ?_⟩, hW.bdd⟩
  obtain ⟨p, rfl⟩ := hW.supp x hx
  exact ⟨(FractionalIdeal.mem_one_iff _).mpr ⟨p.1, rfl⟩, (FractionalIdeal.mem_one_iff _).mpr ⟨p.2, rfl⟩⟩

/-- $W_\chi$ is an integral weight of level $\mathfrak N$. -/
theorem intWeight_chiWeight {𝔑 : Ideal (𝓞 F)} {χ : MulChar (𝓞 F ⧸ 𝔑) ℂ} (h𝔑 : 𝔑 ≠ ⊥) {k : ℤ}
    (hχ : ∀ ε : (𝓞 F)ˣ, χ (Ideal.Quotient.mk 𝔑 (ε : 𝓞 F)) = ((unitNorm ε : ℝ) : ℂ) ^ k) :
    IntWeight (chiWeight 𝔑 χ) k 𝔑 := by
  have hE := eisWeight_chiWeight h𝔑 hχ
  refine ⟨hE.unit, fun x hx => ?_, fun x m₁ m₂ hm₁ hm₂ => ?_, hE.bdd, h𝔑⟩
  · by_contra h
    apply hx
    refine chiWeight_of_not fun ⟨p, _, hp⟩ => h ⟨p, hp⟩
  · by_cases hx : InLevel 𝔑 x
    · obtain ⟨p, hp, rfl⟩ := hx
      rw [show (algebraMap (𝓞 F) F p.1 + algebraMap (𝓞 F) F m₁,
          algebraMap (𝓞 F) F p.2 + algebraMap (𝓞 F) F m₂) =
          (algebraMap (𝓞 F) F (p.1 + m₁), algebraMap (𝓞 F) F (p.2 + m₂)) by simp,
        chiWeight_coe (𝔑.add_mem hp hm₁), chiWeight_coe hp]
      congr 2
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hm₂, add_zero]
    · have hx' : ¬ InLevel 𝔑 (x.1 + algebraMap (𝓞 F) F m₁, x.2 + algebraMap (𝓞 F) F m₂) := by
        rintro ⟨p, hp, hpx⟩
        apply hx
        refine ⟨(p.1 - m₁, p.2 - m₂), 𝔑.sub_mem hp hm₁, ?_⟩
        have h1 := (Prod.ext_iff.mp hpx).1
        have h2 := (Prod.ext_iff.mp hpx).2
        simp only at h1 h2
        ext <;> simp [map_sub, h1, h2]
      rw [chiWeight_of_not hx', chiWeight_of_not hx]

/-! ### The row data -/

/-- The level as a unit fractional ideal. -/
noncomputable def levelUnit (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (𝔐 : FractionalIdeal (𝓞 F)⁰ F) (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔐)

/-- **The row sum** $R_W(c, \nu) = \sum_{r\in\mathcal{O}_F/\mathfrak M}W(c, r)\,e(\langle\nu, \sigma(r)\rangle)$ (representatives `Quotient.out`;
a finite sum, `finsum`). -/
noncomputable def rowR (W : F × F → ℂ) (𝔐 : Ideal (𝓞 F)) (c : F) (ν : InfinitePlace F → ℝ) : ℂ :=
  ∑ᶠ r : 𝓞 F ⧸ 𝔐, W (c, algebraMap (𝓞 F) F (Quotient.out r)) *
    cexp (2 * π * Complex.I * (pair ν (realVec (algebraMap (𝓞 F) F (Quotient.out r))) : ℂ))

/-- The product function $u \mapsto \prod_v\varphi_{k,s}(a_v + u_v + ih_v)$. -/
noncomputable def rowPhi (k : ℕ) (s : ℝ) (a h : InfinitePlace F → ℝ) (u : InfinitePlace F → ℝ) : ℂ :=
  ∏ v, phiKS k s (((a v + u v : ℝ) : ℂ) + (h v : ℂ) * Complex.I)

lemma heckeTerm_eq_rowPhi (W : F × F → ℂ) (k : ℕ) (s : ℝ) (c d : F) (z : InfinitePlace F → ℍ) :
    heckeTerm W k s (c, d) (fun v => (z v : ℂ)) =
      W (c, d) * rowPhi k s (fun v => realEmb F v c * (z v).re) (fun v => realEmb F v c * (z v).im)
        (realVec d) := by
  rw [heckeTerm, rowPhi]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 1
  conv_lhs => rw [← Complex.re_add_im ((z v : ℂ))]
  simp only [realVec, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  push_cast
  ring

/-! ### The product function: continuity, integrability, Fourier transform, decay -/

lemma continuous_rowPhi (k : ℕ) (s : ℝ) (a : InfinitePlace F → ℝ) {h : InfinitePlace F → ℝ}
    (hh : ∀ v, h v ≠ 0) : Continuous (rowPhi k s a h) := by
  unfold rowPhi
  refine continuous_finset_prod _ fun v _ => ?_
  have := continuous_phiKS_line k s (hh v)
  exact this.comp ((continuous_const.add (continuous_apply v)))

lemma integrable_rowPhi {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (a : InfinitePlace F → ℝ) {h : InfinitePlace F → ℝ} (hh : ∀ v, h v ≠ 0) :
    Integrable (rowPhi k s a h) := by
  have hv : ∀ v, Integrable fun t : ℝ => phiKS k s (((a v + t : ℝ) : ℂ) + (h v : ℂ) * Complex.I) := by
    intro v
    have h1 := integrable_phiKS_line hk hs0 hs1 (hh v) 0
    simp only [ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h1
    have h2 := h1.comp_add_left (a v)
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp
  have := Integrable.fintype_prod (f := fun v t => phiKS k s (((a v + t : ℝ) : ℂ) + (h v : ℂ) * Complex.I))
    (μ := fun _ => (volume : Measure ℝ)) hv
  rw [← volume_pi] at this
  exact this

/-- **The Fourier transform of the product function**:
$\int_{\mathbb{R}^\iota}\prod_v\varphi_{k,s}(a_v + u_v + ih_v)\,e(-\langle\nu, u\rangle)\,du = \prod_vT_{k,s}(\nu_v, h_v)\cdot e(\langle\nu, a\rangle)$. -/
theorem integral_rowPhi_mul_exp (k : ℕ) (s : ℝ) (a h ν : InfinitePlace F → ℝ) :
    ∫ u, rowPhi k s a h u * cexp (-(2 * π * Complex.I) * (pair ν u : ℂ)) =
      (∏ v, lineFT k s (ν v) (h v)) * cexp (2 * π * Complex.I * (pair ν a : ℂ)) := by
  have hprod : ∀ u : InfinitePlace F → ℝ, rowPhi k s a h u * cexp (-(2 * π * Complex.I) * (pair ν u : ℂ)) =
      ∏ v, (phiKS k s (((a v + u v : ℝ) : ℂ) + (h v : ℂ) * Complex.I) *
        cexp (-2 * π * Complex.I * ν v * u v)) := by
    intro u
    rw [rowPhi, Finset.prod_mul_distrib, pair, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => by ring
  simp_rw [hprod]
  rw [integral_fintype_prod_volume_eq_prod (fun v (t : ℝ) =>
    phiKS k s (((a v + t : ℝ) : ℂ) + (h v : ℂ) * Complex.I) * cexp (-2 * π * Complex.I * ν v * t))]
  have h1 : ∀ v, ∫ t : ℝ, phiKS k s (((a v + t : ℝ) : ℂ) + (h v : ℂ) * Complex.I) *
      cexp (-2 * π * Complex.I * ν v * t) =
      lineFT k s (ν v) (h v) * cexp (2 * π * Complex.I * ν v * a v) := by
    intro v
    set G : ℝ → ℂ := fun u : ℝ => phiKS k s ((u : ℂ) + (h v : ℂ) * Complex.I) *
        cexp (-2 * π * Complex.I * ν v * (u - a v : ℝ)) with hG
    have hshift := integral_add_left_eq_self (μ := (volume : Measure ℝ)) G (a v)
    calc ∫ t : ℝ, phiKS k s (((a v + t : ℝ) : ℂ) + (h v : ℂ) * Complex.I) *
          cexp (-2 * π * Complex.I * ν v * t)
        = ∫ t : ℝ, G (a v + t) := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only [hG, add_sub_cancel_left]
      _ = ∫ u : ℝ, G u := hshift
      _ = ∫ u : ℝ, phiKS k s ((u : ℂ) + (h v : ℂ) * Complex.I) * cexp (-2 * π * Complex.I * ν v * u) *
            cexp (2 * π * Complex.I * ν v * a v) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          simp only [hG]
          rw [mul_assoc (phiKS k s _), ← Complex.exp_add]
          congr 2
          push_cast; ring
      _ = lineFT k s (ν v) (h v) * cexp (2 * π * Complex.I * ν v * a v) := by
          rw [integral_mul_const, lineFT]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, pair, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => by ring

/-- **Decay of $T_{k,s}(\xi, h)$**: for $k \ge 2$, $0 \le s \le 1$, $h \ne 0$,
$|T_{k,s}(\xi, h)| \le M(h)\,e^{-\pi|\xi||h|}$ with $M(h) = |h|^{1-k}\max(1, |h|^{-2})\,2^k\frac43\pi_0$. -/
lemma norm_lineFT_le {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ξ : ℝ) {h : ℝ}
    (hh : h ≠ 0) :
    ‖lineFT k s ξ h‖ ≤ |h| * (|h| ^ k)⁻¹ * max 1 (|h| ^ 2)⁻¹ *
      (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) * Real.exp (-π * (|ξ| * |h|)) := by
  rw [lineFT_scale k s ξ hh, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (abs_nonneg _), norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hh0 : 0 < |h| := abs_pos.mpr hh
  have h2s : |h| ^ (-2 * s) ≤ max 1 (|h| ^ 2)⁻¹ := by
    rcases le_or_gt 1 |h| with h1 | h1
    · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      calc |h| ^ (-2 * s) ≤ |h| ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hh0 h1.le (by linarith)
        _ = (|h| ^ 2)⁻¹ := by rw [Real.rpow_neg hh0.le]; norm_cast
  have hdec := norm_lineFT_one_le hk hs0 hs1 (ξ * h)
  rw [abs_mul] at hdec
  have hC : 0 ≤ 2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
    have : 0 ≤ ∫ u : ℝ, (1 + u ^ 2)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  calc |h| * (|h| ^ k)⁻¹ * |h| ^ (-2 * s) * ‖lineFT k s (ξ * h) 1‖
      ≤ |h| * (|h| ^ k)⁻¹ * max 1 (|h| ^ 2)⁻¹ *
          (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹) * Real.exp (-π * (|ξ| * |h|))) := by
        gcongr
    _ = _ := by ring

/-! ### Splitting $\mathcal{O}_F$ into residues modulo $\mathfrak M$ -/

lemma latElt_injective (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    Function.Injective (QuadFormsKB.Analysis.latElt I) := by
  intro n n' h
  apply (QuadFormsKB.Analysis.latEquiv I).injective
  apply Subtype.ext
  rw [QuadFormsKB.Analysis.latEquiv_coe, QuadFormsKB.Analysis.latEquiv_coe, h]

lemma latElt_level_mem {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (n : Fin (Module.finrank ℚ F) → ℤ) :
    ∃ m ∈ 𝔐, algebraMap (𝓞 F) F m = QuadFormsKB.Analysis.latElt (levelUnit 𝔐 h𝔐) n := by
  have := latElt_mem (levelUnit 𝔐 h𝔐) n
  rw [levelUnit, Units.val_mk0, FractionalIdeal.mem_coeIdeal] at this
  exact this

/-- **The splitting map** $(r, n) \mapsto \tilde r + m_n$, $\tilde r$ the representative of $r \in \mathcal{O}_F/\mathfrak M$ and
$m_n \in \mathfrak M$ the lattice point with coordinates $n$. -/
noncomputable def splitMap (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) (p : (𝓞 F ⧸ 𝔐) × (Fin (Module.finrank ℚ F) → ℤ)) : F :=
  algebraMap (𝓞 F) F (Quotient.out p.1) + QuadFormsKB.Analysis.latElt (levelUnit 𝔐 h𝔐) p.2

lemma splitMap_injective {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) : Function.Injective (splitMap 𝔐 h𝔐) := by
  rintro ⟨r, n⟩ ⟨r', n'⟩ h
  obtain ⟨m, hm, hmn⟩ := latElt_level_mem h𝔐 n
  obtain ⟨m', hm', hmn'⟩ := latElt_level_mem h𝔐 n'
  simp only [splitMap] at h
  rw [← hmn, ← hmn', ← map_add, ← map_add] at h
  have h1 := IsFractionRing.injective (𝓞 F) F h
  have hr : r = r' := by
    have := congrArg (Ideal.Quotient.mk 𝔐) h1
    rw [map_add, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hm, Ideal.Quotient.eq_zero_iff_mem.mpr hm',
      add_zero, add_zero] at this
    have e1 : Ideal.Quotient.mk 𝔐 (Quotient.out r) = r := Quotient.out_eq r
    have e2 : Ideal.Quotient.mk 𝔐 (Quotient.out r') = r' := Quotient.out_eq r'
    rw [e1, e2] at this; exact this
  subst hr
  have : m = m' := by linear_combination h1
  subst this
  rw [hmn] at hmn'
  exact Prod.ext rfl (latElt_injective _ hmn')

lemma mem_range_splitMap {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (d : 𝓞 F) :
    algebraMap (𝓞 F) F d ∈ Set.range (splitMap 𝔐 h𝔐) := by
  set r : 𝓞 F ⧸ 𝔐 := Ideal.Quotient.mk 𝔐 d
  have hm : d - Quotient.out r ∈ 𝔐 := by
    rw [← Ideal.Quotient.eq]; exact (Quotient.out_eq r).symm
  have hmem : algebraMap (𝓞 F) F (d - Quotient.out r) ∈ ((levelUnit 𝔐 h𝔐 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) := by
    rw [levelUnit, Units.val_mk0]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hm, rfl⟩
  obtain ⟨n, hn⟩ := latElt_surj _ hmem
  exact ⟨(r, n), by simp only [splitMap, hn, map_sub]; ring⟩

/-- On the image of `splitMap`, an $\mathfrak M$-periodic row of an integral weight is constant on residues. -/
lemma IntWeight.row_splitMap {W : F × F → ℂ} {k : ℤ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W k 𝔐)
    (c : F) (p : (𝓞 F ⧸ 𝔐) × (Fin (Module.finrank ℚ F) → ℤ)) :
    W (c, splitMap 𝔐 hW.ne p) = W (c, algebraMap (𝓞 F) F (Quotient.out p.1)) := by
  obtain ⟨m, hm, hmn⟩ := latElt_level_mem hW.ne p.2
  have := hW.per (c, algebraMap (𝓞 F) F (Quotient.out p.1)) 0 m 𝔐.zero_mem hm
  simp only [map_zero, add_zero] at this
  rw [splitMap, ← hmn, this]

/-! ### Majorants for a row -/

lemma eisDen_ne_zero_of_fst {c : F} (hc : c ≠ 0) (d : F) (z : InfinitePlace F → ℍ) :
    eisDen (c, d) (fun v => (z v : ℂ)) ≠ 0 :=
  eisDen_ne_zero (fun h => hc (congrArg Prod.fst h)) fun v => (z v).im_pos

/-- $|N(cz + d)|^{-k}|N(cz+d)|^{-2s} = |N(cz+d)|^{-(k+2s)}$ for $c \ne 0$. -/
lemma norm_heckeTerm_of_fst {W : F × F → ℂ} {k : ℕ} {s : ℝ} {c : F} (hc : c ≠ 0) (d : F)
    (z : InfinitePlace F → ℍ) :
    ‖heckeTerm W k s (c, d) (fun v => (z v : ℂ))‖ =
      ‖W (c, d)‖ * ‖eisDen (c, d) (fun v => (z v : ℂ))‖ ^ (-((k : ℝ) + 2 * s)) := by
  rw [norm_heckeTerm, mul_assoc]
  congr 1
  have hpos := norm_pos_iff.mpr (eisDen_ne_zero_of_fst hc d z)
  rw [← Real.rpow_natCast, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
  congr 1; ring

/-- The fractional ideal $c\mathcal{O}_F + \mathcal{O}_F$ (contains $c$ and $\mathcal{O}_F$). -/
noncomputable def rowIdeal (c : F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ c + 1) (by
    intro h
    have : (1 : F) ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ c + 1 :=
      (FractionalIdeal.mem_add _ _ _).mpr ⟨0, Submodule.zero_mem _, 1, FractionalIdeal.one_mem_one _, by simp⟩
    rw [h, FractionalIdeal.mem_zero_iff] at this; exact one_ne_zero this)

lemma mem_rowIdeal_left (c : F) : c ∈ ((rowIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [rowIdeal, Units.val_mk0]
  exact (FractionalIdeal.mem_add _ _ _).mpr ⟨c, FractionalIdeal.mem_spanSingleton_self _ _, 0,
    Submodule.zero_mem _, by simp⟩

lemma mem_rowIdeal_of_O (c : F) (d : 𝓞 F) :
    algebraMap (𝓞 F) F d ∈ ((rowIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [rowIdeal, Units.val_mk0]
  exact (FractionalIdeal.mem_add _ _ _).mpr ⟨0, Submodule.zero_mem _, _,
    (FractionalIdeal.mem_one_iff _).mpr ⟨d, rfl⟩, by simp⟩

open Classical in
/-- The indicator weight of $J^2$, $J = c\mathcal{O}_F + \mathcal{O}_F$ (an admissible weight of weight $0$). -/
noncomputable def rowIndW (c : F) (x : F × F) : ℂ :=
  if x.1 ∈ ((rowIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    x.2 ∈ ((rowIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) then 1 else 0

lemma eisWeight_rowIndW (c : F) : EisWeight (rowIndW c) 0 := by
  classical
  set J := ((rowIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)
  have hJ : ∀ (ε : (𝓞 F)ˣ) (y : F), y ∈ J ↔ (ε : F) * y ∈ J := by
    intro ε y
    have key : ∀ (u : (𝓞 F)ˣ) (y : F), y ∈ J → (u : F) * y ∈ J := by
      intro u y hy
      rw [← FractionalIdeal.mem_coe] at hy ⊢
      have := Submodule.smul_mem _ (u : 𝓞 F) hy
      rwa [Algebra.smul_def] at this
    refine ⟨key ε y, fun h => ?_⟩
    have := key ε⁻¹ _ h
    rwa [← mul_assoc, show ((ε⁻¹ : (𝓞 F)ˣ) : F) * (ε : F) = 1 by
      rw [show ((ε⁻¹ : (𝓞 F)ˣ) : F) = algebraMap (𝓞 F) F ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) from rfl,
        show (ε : F) = algebraMap (𝓞 F) F (ε : 𝓞 F) from rfl, ← map_mul, Units.inv_mul, map_one],
      one_mul] at this
  refine ⟨fun ε x => ?_, ⟨rowIdeal c, fun x hx => ?_⟩, ⟨1, fun x => ?_⟩⟩
  · have hiff : ((ε • x).1 ∈ J ∧ (ε • x).2 ∈ J) ↔ (x.1 ∈ J ∧ x.2 ∈ J) := by
      rw [smul_fst, smul_snd, ← hJ ε, ← hJ ε]
    simp only [rowIndW, zpow_zero, one_mul]
    exact if_congr hiff rfl rfl
  · by_contra h
    exact hx (by simp only [rowIndW]; rw [if_neg h])
  · simp only [rowIndW]; split_ifs <;> simp

/-- **The row majorant**: for $c \ne 0$ and $\sigma > 2$ there is a summable $u$ on $F$ with
$|N(cz + d)|^{-\sigma} \le u(d)$ for all $d \in \mathcal{O}_F$ and all $z$ in a vertical strip. -/
theorem exists_row_majorant {c : F} (hc : c ≠ 0) {σ : ℝ} (hσ : 2 < σ) (A : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ u : F → ℝ, Summable u ∧ (∀ d, 0 ≤ u d) ∧ ∀ z : InfinitePlace F → ℍ,
      (∀ v, z v ∈ verticalStrip A B) → ∀ d : 𝓞 F,
        ‖eisDen (c, algebraMap (𝓞 F) F d) (fun v => (z v : ℂ))‖ ^ (-σ) ≤ u (algebraMap (𝓞 F) F d) := by
  classical
  obtain ⟨h, hs, hb⟩ := exists_summable_bound_rpow (eisWeight_rowIndW c) hσ A hB
  set ι : F → UOrbit F := fun d => Quotient.mk _ (c, d)
  have hι : Function.Injective ι := by
    intro d d' hdd
    obtain ⟨ε, hε⟩ := orbitRel_iff.mp (Quotient.exact hdd)
    have h1 : (ε : F) * c = c := by
      have := congrArg Prod.fst hε; rwa [smul_fst] at this
    have hε1 : (ε : F) = 1 := by
      have := mul_right_cancel₀ hc (h1.trans (one_mul c).symm); exact this
    have h2 := congrArg Prod.snd hε
    simp only [smul_snd, hε1, one_mul] at h2
    exact h2.symm
  refine ⟨fun d => |h (ι d)|, (hs.comp_injective hι).abs, fun d => abs_nonneg _, fun z hz d => ?_⟩
  have hbd := hb z hz (ι d)
  obtain ⟨ε, hεo⟩ := exists_smul_out (c, algebraMap (𝓞 F) F d)
  have hW1 : ‖rowIndW c (ι d).out‖ = 1 := by
    change ‖rowIndW c (Quotient.mk _ (c, algebraMap (𝓞 F) F d) : UOrbit F).out‖ = 1
    rw [← hεo]
    have hx : rowIndW c (c, algebraMap (𝓞 F) F d) = 1 := by
      simp only [rowIndW, mem_rowIdeal_left, mem_rowIdeal_of_O, and_self, ite_true]
    have := (eisWeight_rowIndW c).unit ε (c, algebraMap (𝓞 F) F d)
    rw [this, hx]; simp
  have hD : ‖eisDen (ι d).out fun v => (z v : ℂ)‖ = ‖eisDen (c, algebraMap (𝓞 F) F d) fun v => (z v : ℂ)‖ := by
    change ‖eisDen (Quotient.mk _ (c, algebraMap (𝓞 F) F d) : UOrbit F).out fun v => (z v : ℂ)‖ = _
    rw [← hεo, eisDen_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm, one_mul]
  rw [hW1, hD, one_mul] at hbd
  exact hbd.trans (le_abs_self _)

/-! ### The row expansion -/

/-- The lattice basis of the level $\mathfrak M$. -/
noncomputable abbrev levelBasis (𝔐 : Ideal (𝓞 F)) (h𝔐 : 𝔐 ≠ ⊥) :
    Module.Basis (Fin (Module.finrank ℚ F)) ℝ (InfinitePlace F → ℝ) :=
  koecherBasis (levelUnit 𝔐 h𝔐)

lemma splitMap_eq_algebraMap {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (p : (𝓞 F ⧸ 𝔐) × (Fin (Module.finrank ℚ F) → ℤ)) :
    ∃ e : 𝓞 F, splitMap 𝔐 h𝔐 p = algebraMap (𝓞 F) F e := by
  obtain ⟨m, -, hm⟩ := latElt_level_mem h𝔐 p.2
  exact ⟨Quotient.out p.1 + m, by rw [splitMap, ← hm, map_add]⟩

lemma realVec_splitMap {𝔐 : Ideal (𝓞 F)} (h𝔐 : 𝔐 ≠ ⊥) (p : (𝓞 F ⧸ 𝔐) × (Fin (Module.finrank ℚ F) → ℤ)) :
    realVec (splitMap 𝔐 h𝔐 p) = realVec (algebraMap (𝓞 F) F (Quotient.out p.1)) +
      (levelBasis 𝔐 h𝔐).equivFun.symm (fun j => (p.2 j : ℝ)) := by
  rw [splitMap, realVec_add, koecherBasis_symm]

lemma min_abs_pos (f : InfinitePlace F → ℝ) (hf : ∀ v, f v ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ v, m ≤ |f v| := by
  obtain ⟨m, hm, hmv⟩ := exists_pos_lt_min (y := fun v => |f v|) fun v => abs_pos.mpr (hf v)
  exact ⟨m, hm, fun v => (hmv v).le⟩

/-- **The Fourier expansion of a row** of an integral weight (`IntWeight`), for $c \ne 0$, $k \ge 2$, $0 \le s \le 1$,
$k + 2s > 2$:
$$\sum_{d\in F}W(c, d)\,N(cz + d)^{-k}|N(cz+d)|^{-2s} = \sum_{n}c_{\mathfrak M}\,R_W(c, \nu_n)
  \prod_vT_{k,s}\big(\nu_{n,v}, \sigma_v(c)y_v\big)\,e\Big(\sum_v\nu_{n,v}\sigma_v(c)x_v\Big),$$
$\nu_n$ = `dualVec` of the lattice basis of $\mathfrak M$ (the trace dual $\mathfrak M^\vee$), $z = x + iy$. -/
theorem hasSum_row {W : F × F → ℂ} {k : ℕ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W (k : ℤ) 𝔐)
    (hk : 2 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hks : 2 < (k : ℝ) + 2 * s) {c : F} (hc : c ≠ 0)
    (z : InfinitePlace F → ℍ) :
    HasSum (fun n : Fin (Module.finrank ℚ F) → ℤ =>
        (latConst (levelBasis 𝔐 hW.ne) : ℂ) * rowR W 𝔐 c (dualVec (levelBasis 𝔐 hW.ne) n) *
          (∏ v, lineFT k s (dualVec (levelBasis 𝔐 hW.ne) n v) (realEmb F v c * (z v).im)) *
            cexp (2 * π * Complex.I *
              (pair (dualVec (levelBasis 𝔐 hW.ne) n) (fun v => realEmb F v c * (z v).re) : ℂ)))
      (∑' d : F, heckeTerm W k s (c, d) fun v => (z v : ℂ)) := by
  classical
  have h𝔐 := hW.ne
  have := Ideal.finiteQuotientOfFreeOfNeBot 𝔐 h𝔐
  letI : Fintype (𝓞 F ⧸ 𝔐) := Fintype.ofFinite _
  set kb := levelBasis 𝔐 h𝔐 with hkb
  set a : InfinitePlace F → ℝ := fun v => realEmb F v c * (z v).re with ha
  set h : InfinitePlace F → ℝ := fun v => realEmb F v c * (z v).im with hh_def
  have hcv : ∀ v, realEmb F v c ≠ 0 := fun v => (map_ne_zero_iff _ (realEmb_injective F v)).mpr hc
  have hh : ∀ v, h v ≠ 0 := fun v => mul_ne_zero (hcv v) (z v).im_pos.ne'
  set Φ := rowPhi k s a h with hΦ
  set K := (latConst kb : ℂ)
  set f : F → ℂ := fun d => heckeTerm W k s (c, d) fun v => (z v : ℂ) with hf
  obtain ⟨BW, hBW⟩ := hW.bdd
  have hBW0 : 0 ≤ BW := (norm_nonneg _).trans (hBW 0)
  obtain ⟨cmin, hcmin, hcminv⟩ := min_abs_pos (fun v => realEmb F v c) hcv
  obtain ⟨ymin, hymin, hyminv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  -- S1: the row is summable
  have hsumf : Summable fun d => ‖f d‖ := by
    obtain ⟨u, hu, hu0, hub⟩ := exists_row_majorant hc hks (∑ v, |(z v).re| + 1) hymin
    refine (hu.mul_left BW).of_nonneg_of_le (fun _ => norm_nonneg _) fun d => ?_
    by_cases hd : W (c, d) = 0
    · simp only [hf, heckeTerm, hd, zero_mul, norm_zero]; exact mul_nonneg hBW0 (hu0 d)
    · obtain ⟨p, hp⟩ := hW.supp _ hd
      have hd' : d = algebraMap (𝓞 F) F p.2 := (congrArg Prod.snd hp).symm
      rw [hf, norm_heckeTerm_of_fst hc, hd']
      refine mul_le_mul (hBW _) (hub z (fun v => ⟨?_, (hyminv v).le⟩) p.2)
        (Real.rpow_nonneg (norm_nonneg _) _) hBW0
      have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      linarith
  -- S2, S3: split the row
  have hsupp : Function.support f ⊆ Set.range (splitMap 𝔐 h𝔐) := by
    intro d hd
    have hW0 : W (c, d) ≠ 0 := by
      intro h0; apply hd; simp only [hf, heckeTerm, h0, zero_mul]
    obtain ⟨p, hp⟩ := hW.supp _ hW0
    have hd' : d = algebraMap (𝓞 F) F p.2 := (congrArg Prod.snd hp).symm
    rw [hd']
    exact mem_range_splitMap h𝔐 p.2
  have hsplit : ∑' d, f d = ∑ r : 𝓞 F ⧸ 𝔐, ∑' n : Fin (Module.finrank ℚ F) → ℤ, f (splitMap 𝔐 h𝔐 (r, n)) := by
    rw [← (splitMap_injective h𝔐).tsum_eq hsupp]
    have hs2 : Summable fun p => f (splitMap 𝔐 h𝔐 p) :=
      (hsumf.comp_injective (splitMap_injective h𝔐)).of_norm
    rw [hs2.tsum_prod' fun r => hs2.comp_injective (Prod.mk_right_injective r), tsum_fintype]
  -- S4: the terms
  have hterm : ∀ r n, f (splitMap 𝔐 h𝔐 (r, n)) = W (c, algebraMap (𝓞 F) F (Quotient.out r)) *
      Φ (realVec (algebraMap (𝓞 F) F (Quotient.out r)) + kb.equivFun.symm fun j => (n j : ℝ)) := by
    intro r n
    simp only [hf]
    rw [heckeTerm_eq_rowPhi, hW.row_splitMap c (r, n), realVec_splitMap]
  -- S5: Poisson for each residue
  have hFT : ∀ ν : InfinitePlace F → ℝ, ∫ x, Φ x * cexp (-(2 * π * Complex.I) * (pair ν x : ℂ)) =
      (∏ v, lineFT k s (ν v) (h v)) * cexp (2 * π * Complex.I * (pair ν a : ℂ)) :=
    fun ν => integral_rowPhi_mul_exp k s a h ν
  have hpoisson : ∀ r : 𝓞 F ⧸ 𝔐, HasSum (fun n => K * (∫ x, Φ x * cexp (-(2 * π * Complex.I) *
      (pair (dualVec kb n) x : ℂ))) * cexp (2 * π * Complex.I *
        (pair (dualVec kb n) (realVec (algebraMap (𝓞 F) F (Quotient.out r))) : ℂ)))
      (∑' n : Fin (Module.finrank ℚ F) → ℤ,
        Φ (realVec (algebraMap (𝓞 F) F (Quotient.out r)) + kb.equivFun.symm fun j => (n j : ℝ))) := by
    intro r
    refine hasSum_lattice_fourier kb (continuous_rowPhi k s a hh) (integrable_rowPhi hk hs0 hs1 a hh) _
      ?_ ?_
    · -- local uniform summability, from the row majorant at shifted points
      intro R
      set Cop := ‖(kb.equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
        (InfinitePlace F → ℝ))‖
      set A' := ∑ v, |(z v).re| + Cop * |R| / cmin + 1
      obtain ⟨u, hu, hu0, hub⟩ := exists_row_majorant hc hks A' hymin
      refine ⟨fun n => u (splitMap 𝔐 h𝔐 (r, n)),
        hu.comp_injective ((splitMap_injective h𝔐).comp (Prod.mk_right_injective r)), fun t ht n => ?_⟩
      set δ := kb.equivFun.symm t
      set z' : InfinitePlace F → ℍ := fun v => (δ v / realEmb F v c) +ᵥ z v
      have hz're : ∀ v, realEmb F v c * (z' v).re = a v + δ v := by
        intro v; simp only [z', UpperHalfPlane.vadd_re, ha]; field_simp [hcv v]; ring
      have hz'im : ∀ v, realEmb F v c * (z' v).im = h v := by
        intro v; simp [z', hh_def]
      obtain ⟨e, he⟩ := splitMap_eq_algebraMap h𝔐 (r, n)
      have hΦeq : rowPhi k s a h (realVec (algebraMap (𝓞 F) F (Quotient.out r)) +
          kb.equivFun.symm (t + fun j => (n j : ℝ))) =
          heckeTerm (fun _ => (1 : ℂ)) k s (c, algebraMap (𝓞 F) F e) fun v => (z' v : ℂ) := by
        rw [heckeTerm_eq_rowPhi, one_mul, ← he, realVec_splitMap, map_add]
        simp only [hΦ, rowPhi, hz're, hz'im]
        refine Finset.prod_congr rfl fun v _ => ?_
        congr 3
        simp only [Pi.add_apply, δ]; ring
      rw [hΦeq, norm_heckeTerm_of_fst hc, norm_one, one_mul]
      show _ ≤ u (splitMap 𝔐 h𝔐 (r, n))
      rw [he]
      refine hub z' (fun v => ⟨?_, ?_⟩) e
      · -- the real parts stay bounded
        have hre : (z' v).re = (z v).re + δ v / realEmb F v c := by
          simp only [z', UpperHalfPlane.vadd_re]; ring
        rw [hre]
        have hδ : |δ v| ≤ Cop * |R| := by
          refine (norm_le_pi_norm δ v).trans ?_
          calc ‖δ‖ = ‖(kb.equivFun.symm.toContinuousLinearEquiv : (Fin (Module.finrank ℚ F) → ℝ) →L[ℝ]
                (InfinitePlace F → ℝ)) t‖ := rfl
            _ ≤ Cop * ‖t‖ := ContinuousLinearMap.le_opNorm _ t
            _ ≤ Cop * |R| := by gcongr; exact ht.trans (le_abs_self R)
        have h1 : |δ v / realEmb F v c| ≤ Cop * |R| / cmin := by
          rw [abs_div]
          exact div_le_div₀ (by positivity) hδ hcmin (hcminv v)
        have h2 := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ v)
        have := abs_add_le (z v).re (δ v / realEmb F v c)
        simp only [A']; linarith
      · show ymin ≤ (z' v).im
        simp only [z', UpperHalfPlane.vadd_im]; exact (hyminv v).le
    · -- summability of the transforms: exponential decay
      set M := ∏ v, (|h v| * (|h v| ^ k)⁻¹ * max 1 (|h v| ^ 2)⁻¹ *
        (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)))
      obtain ⟨hmin, hhmin, hhminv⟩ := min_abs_pos h hh
      refine ((summable_exp_neg_l1 kb (a := π * hmin) (by positivity)).mul_left M).of_nonneg_of_le
        (fun _ => norm_nonneg _) fun n => ?_
      rw [hFT, norm_mul, show (2 * π * Complex.I * (pair (dualVec kb n) a : ℂ)) =
        ((2 * π * pair (dualVec kb n) a : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one, norm_prod]
      calc ∏ v, ‖lineFT k s (dualVec kb n v) (h v)‖
          ≤ ∏ v, (|h v| * (|h v| ^ k)⁻¹ * max 1 (|h v| ^ 2)⁻¹ *
              (2 ^ k * (4 / 3) * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) *
                Real.exp (-π * (|dualVec kb n v| * |h v|))) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
              fun v _ => norm_lineFT_le hk hs0 hs1 _ (hh v)
        _ = M * Real.exp (-π * ∑ v, |dualVec kb n v| * |h v|) := by
            rw [Finset.prod_mul_distrib, Finset.mul_sum, ← Real.exp_sum]
        _ ≤ M * Real.exp (-(π * hmin) * l1 (dualVec kb n)) := by
            have hM0 : 0 ≤ M := Finset.prod_nonneg fun v _ => by
              have : 0 ≤ ∫ u : ℝ, (1 + u ^ 2)⁻¹ := integral_nonneg fun u => by positivity
              positivity
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM0
            simp only [l1]
            rw [Finset.mul_sum, Finset.mul_sum]
            have : ∑ v, π * hmin * |dualVec kb n v| ≤ ∑ v, π * (|dualVec kb n v| * |h v|) :=
              Finset.sum_le_sum fun v _ => by
                have := mul_le_mul_of_nonneg_left (hhminv v) (abs_nonneg (dualVec kb n v))
                nlinarith [Real.pi_pos, abs_nonneg (dualVec kb n v)]
            have e1 : ∑ v, -(π * hmin) * |dualVec kb n v| = -∑ v, π * hmin * |dualVec kb n v| := by
              rw [← Finset.sum_neg_distrib]; congr 1; funext v; ring
            have e2 : ∑ v, -π * (|dualVec kb n v| * |h v|) = -∑ v, π * (|dualVec kb n v| * |h v|) := by
              rw [← Finset.sum_neg_distrib]; congr 1; funext v; ring
            rw [e1, e2]; linarith
  -- S6: combine the residues
  have hall := hasSum_sum (s := Finset.univ) fun r (_ : r ∈ Finset.univ) =>
    (hpoisson r).mul_left (W (c, algebraMap (𝓞 F) F (Quotient.out r)))
  rw [hsplit]
  simp_rw [hterm, tsum_mul_left]
  convert hall using 1
  funext n
  simp only [hFT]
  rw [rowR, finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => by ring

end QuadFormsKB.HilbertModular
