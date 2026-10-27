import Mathlib
import QuadFormsKB.Citation

/-!
# The orbit fibration of a Haar measure

**Generic, Mathlib-only hypotheses (upstreamable).** Let a group $G$ act (on the left) on a measurable space $X$,
transitively, with base point $x_0$, stabilizer $H = G_{x_0}$, and a *measurable section* $s : X\to G$ of the orbit
map, $s(x)\,x_0 = x$ (`OrbitSection`). Then
$$ \Psi : X\times H\xrightarrow{\ \sim\ } G,\qquad \Psi(x, h) = s(x)\,h $$
is a measurable equivalence (`OrbitSection.coordEquiv`), and left translation by $g_0$ is the skew product
$g_0\Psi(x, h) = \Psi\big(g_0x,\ c(g_0, x)\,h\big)$ with the cocycle $c(g_0, x) = s(g_0x)^{-1}g_0\,s(x)\in H$
(`OrbitSection.mul_ofCoord`). For a $G$-invariant measure $\nu$ on $X$ and a left-invariant measure $\mu_H$ on $H$:

* **`OrbitSection.isMulLeftInvariant_fibMeasure`**: $\mu := \Psi_*(\nu\otimes\mu_H)$ (`fibMeasure`) is left invariant;
* **`OrbitSection.fibMeasure_eq_smul`**: $\mu = c\,\mu_G$ for every σ-finite left-invariant $\mu_G$ on $G$
  (uniqueness of Haar measure in the measurable form, `measure_eq_div_smul`);
* **`OrbitSection.lintegral_fibMeasure`** (the fibration formula, Weil's Lemma 2.4.1 / Thm 2.4.3):
  $$ \int_G f\,d\mu = \int_X\int_H f(s(x)h)\,d\mu_H(h)\,d\nu(x), $$
  and the inner integral depends only on the coset $gH$, not on the section (`OrbitSection.fibInt_eq_of_smul`,
  `OrbitSection.fibMeasure_eq_of_sections`);
* **`OrbitSection.fibMeasure_injective`**, **`OrbitSection.eq_smul_of_smulInvariant`**: the $G$-invariant measure
  $\nu$ on $X = G/H$ is determined by $\mu_G$ and $\mu_H$, hence is unique up to a scalar;
* **`OrbitSection.isHaarMeasure_fibMeasure`**: for $G$ a locally compact second countable topological group, $\mu$ is
  a Haar measure as soon as it is nonzero and finite on one nonempty open set;
* **`smulInvariantMeasure_comap_subMulAction`**: the orbit form used by Weil for $\mathrm{SO}(V)$ on spheres/cones and
  $\mathrm{SL}_2$ on $\mathbb A^2\setminus 0$ — if $G$ acts on a vector space (any measurable space) $V$ preserving a
  measure $\lambda$, and $O\subseteq V$ is a measurable $G$-stable set, then $\lambda|_O$ is $G$-invariant on $O$;
* **Normal subgroups** (Weil's Thm 2.4.4): for a homomorphism $\pi : G\to Q$ with a measurable set-theoretic section
  $\sigma$, `homSection` is the orbit section of $G$ acting on $Q$ through $\pi$; its stabilizer is $\ker\pi$
  (`mem_stab_homSection`), and **`isMulLeftInvariant_homFibMeasure`**: $(q, k)\mapsto\sigma(q)k$ carries
  $\mu_Q\otimes\mu_{\ker\pi}$ to a left-invariant measure on $G$, i.e. $\mu_G = \mu_Q\times\mu_{\ker\pi}$ in the
  fibration sense.

No topology is needed for the measure-theoretic statements; σ-finiteness replaces local compactness. The existence of
a measurable section is a hypothesis (data): in the applications it is explicit (e.g. the section of
$g\mapsto g e_1$ on $\mathrm{SL}_2(\mathbb A_F)$, `SL2Section.lean`).

Reference: Weil, *Adeles and algebraic groups* (1982), §2.4, Lemma 2.4.1, Thms 2.4.3–2.4.4 [unverified pages].
-/

open MeasureTheory Measure Set Function
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- **A measurable section of the orbit map of a transitive action.** Fields: the base point `base` $= x_0$, the
section `sec` $= s : X\to G$ with `sec_smul` : $s(x)\,x_0 = x$ for every $x$ (so the action is transitive), and the
measurability of $s$ (`measurable_sec`) and of the orbit map $g\mapsto g\,x_0$ (`measurable_orbit`). The stabilizer of
$x_0$ is `OrbitSection.stab`. -/
structure OrbitSection (G X : Type*) [Group G] [MulAction G X] [MeasurableSpace G] [MeasurableSpace X] where
  /-- The base point $x_0$. -/
  base : X
  /-- The section $s : X\to G$ of the orbit map. -/
  sec : X → G
  /-- $s(x)\,x_0 = x$. -/
  sec_smul : ∀ x, sec x • base = x
  /-- $s$ is measurable. -/
  measurable_sec : Measurable sec
  /-- The orbit map $g\mapsto g\,x_0$ is measurable. -/
  measurable_orbit : Measurable fun g : G => g • base

/-- A subgroup of a group with measurable multiplication has measurable multiplication. -/
instance Subgroup.measurableMul₂' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (H : Subgroup G) :
    MeasurableMul₂ H :=
  ⟨((measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩

instance Subgroup.measurableInv' {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G] (H : Subgroup G) :
    MeasurableInv H :=
  ⟨measurable_subtype_coe.inv.subtype_mk⟩

namespace OrbitSection

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace G] [MeasurableSpace X]
variable (S : OrbitSection G X)

/-- The stabilizer $H = G_{x_0}$ of the base point. -/
abbrev stab : Subgroup G := MulAction.stabilizer G S.base

theorem mem_stab_iff {g : G} : g ∈ S.stab ↔ g • S.base = S.base := MulAction.mem_stabilizer_iff

theorem inv_sec_mul_mem (g : G) : (S.sec (g • S.base))⁻¹ * g ∈ S.stab := by
  rw [mem_stab_iff, mul_smul, inv_smul_eq_iff, S.sec_smul]

/-- The fibre coordinate $g\mapsto s(gx_0)^{-1}g\in H$. -/
def fib (g : G) : S.stab := ⟨(S.sec (g • S.base))⁻¹ * g, S.inv_sec_mul_mem g⟩

/-- The coordinates $g\mapsto(gx_0,\ s(gx_0)^{-1}g)\in X\times H$. -/
def toCoord (g : G) : X × S.stab := (g • S.base, S.fib g)

/-- The inverse coordinates $\Psi(x, h) = s(x)\,h$. -/
def ofCoord (p : X × S.stab) : G := S.sec p.1 * p.2

theorem ofCoord_toCoord (g : G) : S.ofCoord (S.toCoord g) = g := by
  simp [ofCoord, toCoord, fib]

theorem ofCoord_smul (p : X × S.stab) : S.ofCoord p • S.base = p.1 := by
  have hp : (p.2 : G) • S.base = S.base := (S.mem_stab_iff).1 p.2.2
  rw [ofCoord, mul_smul, hp, S.sec_smul]

theorem toCoord_ofCoord (p : X × S.stab) : S.toCoord (S.ofCoord p) = p := by
  obtain ⟨x, h⟩ := p
  refine Prod.ext (S.ofCoord_smul (x, h)) (Subtype.ext ?_)
  show (S.sec (S.ofCoord (x, h) • S.base))⁻¹ * S.ofCoord (x, h) = h
  rw [S.ofCoord_smul (x, h)]
  simp [ofCoord]

section Measurable

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurable_fib : Measurable S.fib :=
  ((S.measurable_sec.comp S.measurable_orbit).inv.mul measurable_id).subtype_mk

theorem measurable_toCoord : Measurable S.toCoord := S.measurable_orbit.prodMk S.measurable_fib

theorem measurable_ofCoord : Measurable S.ofCoord :=
  (S.measurable_sec.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)

/-- **The coordinates $G\simeq X\times H$** as a measurable equivalence. -/
def coordEquiv : G ≃ᵐ X × S.stab where
  toFun := S.toCoord
  invFun := S.ofCoord
  left_inv := S.ofCoord_toCoord
  right_inv := S.toCoord_ofCoord
  measurable_toFun := S.measurable_toCoord
  measurable_invFun := S.measurable_ofCoord

include S in
/-- The action map $x\mapsto g_0x$ is measurable (it is $x\mapsto(g_0s(x))x_0$). -/
theorem measurable_const_smul (g₀ : G) : Measurable fun x : X => g₀ • x := by
  have h : (fun x : X => g₀ • x) = fun x => (g₀ * S.sec x) • S.base := by
    funext x; rw [mul_smul, S.sec_smul]
  rw [h]
  exact S.measurable_orbit.comp (S.measurable_sec.const_mul g₀)

end Measurable

/-! ### The skew product -/

/-- The cocycle $c(g_0, x) = s(g_0x)^{-1}g_0\,s(x)\in H$. -/
def coc (g₀ : G) (x : X) : S.stab := S.fib (g₀ * S.sec x)

theorem mul_smul_base (g₀ : G) (x : X) : (g₀ * S.sec x) • S.base = g₀ • x := by
  rw [mul_smul, S.sec_smul]

/-- **Left translation is a skew product:** $g_0\Psi(x, h) = \Psi(g_0x,\ c(g_0, x)h)$. -/
theorem mul_ofCoord (g₀ : G) (p : X × S.stab) :
    g₀ * S.ofCoord p = S.ofCoord (g₀ • p.1, S.coc g₀ p.1 * p.2) := by
  simp only [ofCoord, coc, fib, Subgroup.coe_mul, S.mul_smul_base]
  group

/-- **The fibration measure** $\Psi_*(\nu\otimes\mu_H)$ on $G$. -/
def fibMeasure (ν : Measure X) (μH : Measure S.stab) : Measure G := (ν.prod μH).map S.ofCoord

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem fibMeasure_apply (ν : Measure X) (μH : Measure S.stab) {s : Set G} (hs : MeasurableSet s) :
    S.fibMeasure ν μH s = (ν.prod μH) (S.ofCoord ⁻¹' s) :=
  Measure.map_apply S.measurable_ofCoord hs

instance (ν : Measure X) (μH : Measure S.stab) [SigmaFinite ν] [SigmaFinite μH] :
    SigmaFinite (S.fibMeasure ν μH) :=
  S.coordEquiv.symm.sigmaFinite_map

include S in
theorem map_smul_eq (ν : Measure X) [SMulInvariantMeasure G X ν] (g₀ : G) :
    ν.map (fun x => g₀ • x) = ν := by
  ext t ht
  rw [map_apply (S.measurable_const_smul g₀) ht]
  exact SMulInvariantMeasure.measure_preimage_smul g₀ ht

/-- **The fibration measure is left invariant** ($\nu$ $G$-invariant, $\mu_H$ left invariant). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 and Thm 2.4.3 [unverified page]"]
theorem map_mul_left_fibMeasure (ν : Measure X) (μH : Measure S.stab) [SFinite ν] [SFinite μH]
    [SMulInvariantMeasure G X ν] [μH.IsMulLeftInvariant] (g₀ : G) :
    (S.fibMeasure ν μH).map (g₀ * ·) = S.fibMeasure ν μH := by
  have hbase : MeasurePreserving (fun x : X => g₀ • x) ν ν :=
    ⟨S.measurable_const_smul g₀, S.map_smul_eq ν g₀⟩
  have hcoc : Measurable (S.coc g₀) := S.measurable_fib.comp (S.measurable_sec.const_mul g₀)
  have hgm : Measurable (uncurry fun (x : X) (h : S.stab) => S.coc g₀ x * h) :=
    (hcoc.comp measurable_fst).mul measurable_snd
  have hT := hbase.skew_product (μc := μH) (μd := μH) hgm
    (Filter.Eventually.of_forall fun x => map_mul_left_eq_self μH _)
  have e1 : (S.fibMeasure ν μH).map (g₀ * ·) = (ν.prod μH).map (fun p => g₀ * S.ofCoord p) :=
    Measure.map_map (measurable_const_mul g₀) S.measurable_ofCoord
  have e2 : (fun p => g₀ * S.ofCoord p) =
      S.ofCoord ∘ fun p : X × S.stab => (g₀ • p.1, S.coc g₀ p.1 * p.2) :=
    funext (S.mul_ofCoord g₀)
  rw [e1, e2, ← Measure.map_map S.measurable_ofCoord hT.measurable, hT.map_eq]
  rfl

instance isMulLeftInvariant_fibMeasure (ν : Measure X) (μH : Measure S.stab) [SFinite ν] [SFinite μH]
    [SMulInvariantMeasure G X ν] [μH.IsMulLeftInvariant] : (S.fibMeasure ν μH).IsMulLeftInvariant :=
  ⟨S.map_mul_left_fibMeasure ν μH⟩

/-- **Uniqueness:** the fibration measure is a scalar multiple of every σ-finite left-invariant measure $\mu_G$,
$\Psi_*(\nu\otimes\mu_H) = \big(\mu(U)/\mu_G(U)\big)\,\mu_G$ for any $U$ with $0 < \mu_G(U) < \infty$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 and Thm 2.4.3 [unverified page]"]
theorem fibMeasure_eq_smul (ν : Measure X) (μH : Measure S.stab) [SigmaFinite ν] [SigmaFinite μH]
    [SMulInvariantMeasure G X ν] [μH.IsMulLeftInvariant] (μG : Measure G) [SigmaFinite μG]
    [μG.IsMulLeftInvariant] {U : Set G} (h0 : μG U ≠ 0) (htop : μG U ≠ ∞) :
    S.fibMeasure ν μH = (S.fibMeasure ν μH U / μG U) • μG :=
  measure_eq_div_smul (S.fibMeasure ν μH) μG h0 htop

/-- **The fibration formula** (Weil's Lemma 2.4.1, measurable-section form):
$\int_G f\,d\Psi_*(\nu\otimes\mu_H) = \int_X\int_H f(s(x)h)\,d\mu_H(h)\,d\nu(x)$. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 [unverified page]"]
theorem lintegral_fibMeasure (ν : Measure X) (μH : Measure S.stab) [SFinite μH] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ g, f g ∂S.fibMeasure ν μH = ∫⁻ x, ∫⁻ h, f (S.sec x * h) ∂μH ∂ν := by
  rw [fibMeasure, lintegral_map hf S.measurable_ofCoord]
  exact lintegral_prod (fun p => f (S.ofCoord p)) (hf.comp S.measurable_ofCoord).aemeasurable

/-- The fibre integral $x\mapsto\int_H f(s(x)h)\,d\mu_H(h)$. -/
def fibInt (μH : Measure S.stab) (f : G → ℝ≥0∞) (x : X) : ℝ≥0∞ := ∫⁻ h, f (S.sec x * h) ∂μH

/-- **The fibre integral depends only on the coset $gH$:** if $g\,x_0 = x$ then
$\int_H f(s(x)h)\,d\mu_H(h) = \int_H f(gh)\,d\mu_H(h)$ ($\mu_H$ left invariant). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 [unverified page]"]
theorem fibInt_eq_of_smul (μH : Measure S.stab) [μH.IsMulLeftInvariant] (f : G → ℝ≥0∞) {g : G} {x : X}
    (hg : g • S.base = x) : S.fibInt μH f x = ∫⁻ h, f (g * h) ∂μH := by
  set h₀ : S.stab := S.fib g
  have hsec : S.sec x = g * ((h₀ : G))⁻¹ := by
    simp [h₀, fib, hg]
  rw [fibInt, hsec]
  have := lintegral_mul_left_eq_self (μ := μH) (fun h : S.stab => f (g * (h : G))) h₀⁻¹
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  simp_rw [mul_assoc]
  exact this

/-- **Independence of the section:** replacing the section $s$ by another measurable section $s'$ with the same base
point does not change the fibration measure. -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 [unverified page]"]
theorem fibMeasure_eq_of_sec (s' : X → G) (hs' : ∀ x, s' x • S.base = x) (hm : Measurable s') (ν : Measure X)
    (μH : Measure S.stab) [SFinite μH] [μH.IsMulLeftInvariant] :
    ({ S with sec := s', sec_smul := hs', measurable_sec := hm } : OrbitSection G X).fibMeasure ν μH =
      S.fibMeasure ν μH := by
  set S' : OrbitSection G X := { S with sec := s', sec_smul := hs', measurable_sec := hm }
  ext A hA
  have hi : Measurable (A.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
    S'.lintegral_fibMeasure ν μH hi, S.lintegral_fibMeasure ν μH hi]
  refine lintegral_congr fun x => ?_
  exact (S.fibInt_eq_of_smul μH _ (hs' x)).symm

/-! ### Uniqueness of the invariant measure on $G/H$ -/

theorem exists_pos_lt_top (μ : Measure X) [SigmaFinite μ] (hμ : μ ≠ 0) :
    ∃ B, MeasurableSet B ∧ μ B ≠ 0 ∧ μ B ≠ ∞ := by
  by_contra hcon
  push Not at hcon
  apply hμ
  refine Measure.measure_univ_eq_zero.1 ?_
  rw [← iUnion_spanningSets μ]
  refine measure_iUnion_null fun n => ?_
  by_contra h0
  exact (measure_spanningSets_lt_top μ n).ne (hcon _ (measurableSet_spanningSets μ n) h0)

/-- **The invariant measure on $X = G/H$ is determined by $\mu_G$ and $\mu_H$:** if two measures on $X$ give the same
fibration measure, they are equal ($\mu_H\ne 0$ σ-finite). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 (uniqueness of the quotient measure) [unverified page]"]
theorem fibMeasure_injective (μH : Measure S.stab) [SigmaFinite μH] (hμH : μH ≠ 0) {ν₁ ν₂ : Measure X}
    [SFinite ν₁] [SFinite ν₂] (h : S.fibMeasure ν₁ μH = S.fibMeasure ν₂ μH) : ν₁ = ν₂ := by
  have hp : ν₁.prod μH = ν₂.prod μH := by
    have := congrArg (fun μ => μ.map S.toCoord) h
    simp only [fibMeasure] at this
    rwa [Measure.map_map S.measurable_toCoord S.measurable_ofCoord,
      Measure.map_map S.measurable_toCoord S.measurable_ofCoord,
      show S.toCoord ∘ S.ofCoord = id from funext S.toCoord_ofCoord, Measure.map_id, Measure.map_id] at this
  obtain ⟨B, hB, hB0, hBt⟩ := exists_pos_lt_top μH hμH
  ext A hA
  have := congrArg (fun μ => μ (A ×ˢ B)) hp
  simp only [Measure.prod_prod] at this
  exact (ENNReal.mul_left_inj hB0 hBt).1 this

theorem fibMeasure_smul (ν : Measure X) (μH : Measure S.stab) [SFinite μH] (c : ℝ≥0∞) :
    S.fibMeasure (c • ν) μH = c • S.fibMeasure ν μH := by
  ext A hA
  rw [Measure.smul_apply, S.fibMeasure_apply _ _ hA, S.fibMeasure_apply _ _ hA, Measure.prod_smul_left,
    Measure.smul_apply]

/-- **Uniqueness up to a scalar of the $G$-invariant measure on $X = G/H$:** two σ-finite $G$-invariant measures
$\nu_1,\nu_2$ on $X$ are proportional, $\nu_1 = c\,\nu_2$, provided the fibration measure of $\nu_2$ is positive and finite
on some set $U$ (then $c = \Psi_*(\nu_1\otimes\mu_H)(U)/\Psi_*(\nu_2\otimes\mu_H)(U)$). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 (uniqueness of the quotient measure) [unverified page]"]
theorem eq_smul_of_smulInvariant (μH : Measure S.stab) [SigmaFinite μH] [μH.IsMulLeftInvariant] (hμH : μH ≠ 0)
    (ν₁ ν₂ : Measure X) [SigmaFinite ν₁] [SigmaFinite ν₂] [SMulInvariantMeasure G X ν₁]
    [SMulInvariantMeasure G X ν₂] {U : Set G} (h0 : S.fibMeasure ν₂ μH U ≠ 0)
    (htop : S.fibMeasure ν₂ μH U ≠ ∞) :
    ν₁ = (S.fibMeasure ν₁ μH U / S.fibMeasure ν₂ μH U) • ν₂ := by
  refine S.fibMeasure_injective μH hμH ?_
  rw [S.fibMeasure_smul]
  exact measure_eq_div_smul (S.fibMeasure ν₁ μH) (S.fibMeasure ν₂ μH) h0 htop

/-- **Normalization:** given a σ-finite left-invariant $\mu_G$ and a set $U$ with $0 < \mu_G(U) < \infty$ on which the
fibration measure is positive and finite, the rescaled measure $\nu' = c^{-1}\nu$ satisfies
$\Psi_*(\nu'\otimes\mu_H) = \mu_G$ exactly (and is unique by `fibMeasure_injective`). -/
@[kb "weil1982" "§2.4, Lemma 2.4.1 [unverified page]"]
theorem fibMeasure_normalized (ν : Measure X) (μH : Measure S.stab) [SigmaFinite ν] [SigmaFinite μH]
    [SMulInvariantMeasure G X ν] [μH.IsMulLeftInvariant] (μG : Measure G) [SigmaFinite μG]
    [μG.IsMulLeftInvariant] {U : Set G} (h0 : μG U ≠ 0) (htop : μG U ≠ ∞)
    (h0' : S.fibMeasure ν μH U ≠ 0) (htop' : S.fibMeasure ν μH U ≠ ∞) :
    S.fibMeasure ((S.fibMeasure ν μH U / μG U)⁻¹ • ν) μH = μG := by
  set c := S.fibMeasure ν μH U / μG U with hc
  rw [S.fibMeasure_smul]
  conv_lhs => rw [S.fibMeasure_eq_smul ν μH μG h0 htop, ← hc]
  rw [smul_smul, ENNReal.inv_mul_cancel (ENNReal.div_pos h0' htop).ne' (ENNReal.div_ne_top htop' h0), one_smul]

/-! ### Haar measures -/

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G]

/-- **The fibration measure is a Haar measure** on a locally compact second countable group, as soon as it is
nonzero and finite on one nonempty open set. -/
@[kb "weil1982" "§2.4, Thm 2.4.3 [unverified page]"]
theorem isHaarMeasure_fibMeasure (ν : Measure X) (μH : Measure S.stab) [SigmaFinite ν] [SigmaFinite μH]
    [SMulInvariantMeasure G X ν] [μH.IsMulLeftInvariant] (hne : S.fibMeasure ν μH ≠ 0) {U : Set G}
    (hU : IsOpen U) (hUne : U.Nonempty) (hUfin : S.fibMeasure ν μH U ≠ ∞) :
    (S.fibMeasure ν μH).IsHaarMeasure := by
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
  set μG : Measure G := Measure.haar
  have h0 : μG (interior K) ≠ 0 := (isOpen_interior.measure_pos μG ⟨x, hxK⟩).ne'
  have htop : μG (interior K) ≠ ∞ := (lt_of_le_of_lt (measure_mono interior_subset) hK.measure_lt_top).ne
  have hfin : S.fibMeasure ν μH (interior K) ≠ ∞ :=
    ne_top_of_le_ne_top hUfin (measure_mono (interior_subset.trans hKU))
  have heq := S.fibMeasure_eq_smul ν μH μG h0 htop
  have hc0 : S.fibMeasure ν μH (interior K) / μG (interior K) ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at heq
    exact hne heq
  rw [heq]
  exact Measure.IsHaarMeasure.smul _ hc0 (ENNReal.div_ne_top hfin h0)

end Topological

end OrbitSection

/-! ### Orbits in a space with an invariant measure -/

/-- **Weil's orbit form:** if $G$ acts on $V$ preserving $\lambda$ and $O\subseteq V$ is a measurable $G$-stable set
(e.g. an orbit), the restriction $\lambda|_O$ (as a measure on the subtype) is $G$-invariant. -/
@[kb "weil1982" "§2.4 (orbits of SO(V) on spheres and cones) [unverified page]"]
theorem smulInvariantMeasure_comap_subMulAction {G V : Type*} [Group G] [MulAction G V] [MeasurableSpace V]
    (lam : Measure V) [SMulInvariantMeasure G V lam] (O : SubMulAction G V) (hO : MeasurableSet (O : Set V)) :
    SMulInvariantMeasure G O (lam.comap Subtype.val) := by
  refine ⟨fun g t ht => ?_⟩
  have hemb : MeasurableEmbedding (Subtype.val : O → V) := MeasurableEmbedding.subtype_coe hO
  rw [hemb.comap_apply, hemb.comap_apply]
  have hset : Subtype.val '' ((fun x : O => g • x) ⁻¹' t) = (fun v : V => g • v) ⁻¹' (Subtype.val '' t) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g • x, hx, rfl⟩
    · rintro ⟨y, hy, hyv⟩
      have hv : v ∈ O := by
        have : v = g⁻¹ • (y : V) := by rw [hyv, inv_smul_smul]
        rw [this]; exact O.smul_mem _ y.2
      exact ⟨⟨v, hv⟩, by
        show g • (⟨v, hv⟩ : O) ∈ t
        have : g • (⟨v, hv⟩ : O) = y := Subtype.ext (by rw [SubMulAction.val_smul]; exact hyv.symm)
        rw [this]; exact hy, rfl⟩
  rw [hset]
  exact SMulInvariantMeasure.measure_preimage_smul g (hemb.measurableSet_image.2 ht)

theorem sigmaFinite_comap_subtype {V : Type*} [MeasurableSpace V] (lam : Measure V) [SigmaFinite lam]
    {O : Set V} (hO : MeasurableSet O) : SigmaFinite (lam.comap (Subtype.val : O → V)) := by
  refine ⟨⟨{ set := fun n => Subtype.val ⁻¹' spanningSets lam n,
              set_mem := fun _ => trivial,
              finite := fun n => ?_,
              spanning := ?_ }⟩⟩
  · rw [(MeasurableEmbedding.subtype_coe hO).comap_apply]
    exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top _ n)
  · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]

/-! ### Normal subgroups: splitting along a homomorphism (Weil's Thm 2.4.4) -/

section Hom

variable {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]

/-- $G$ acting on $Q$ through $\pi$: $g\cdot q = \pi(g)\,q$. -/
abbrev homAction (π : G →* Q) : MulAction G Q := MulAction.compHom Q π

/-- **The orbit section of a homomorphism** $\pi : G\to Q$ with a measurable set-theoretic section $\sigma$
($\pi\circ\sigma = \mathrm{id}$), for $G$ acting on $Q$ through $\pi$, base point $1$. Its stabilizer is $\ker\pi$
(`mem_stab_homSection`). -/
def homSection [MeasurableMul₂ Q] (π : G →* Q) (hπ : Measurable π) (σ : Q → G) (hσ : ∀ q, π (σ q) = q)
    (hσm : Measurable σ) : @OrbitSection G Q _ (homAction π) _ _ :=
  @OrbitSection.mk G Q _ (homAction π) _ _ 1 σ (fun q => by
      show π (σ q) * 1 = q
      rw [mul_one, hσ]) hσm (by
      show Measurable fun g : G => π g * 1
      simpa using hπ)

theorem mem_stab_homSection [MeasurableMul₂ Q] (π : G →* Q) (hπ : Measurable π) (σ : Q → G)
    (hσ : ∀ q, π (σ q) = q) (hσm : Measurable σ) (g : G) :
    g ∈ @OrbitSection.stab G Q _ (homAction π) _ _ (homSection π hπ σ hσ hσm) ↔ g ∈ π.ker := by
  let _ := homAction π
  rw [OrbitSection.mem_stab_iff, MonoidHom.mem_ker]
  show π g * 1 = 1 ↔ _
  rw [mul_one]

/-- A left-invariant measure on $Q$ is invariant for the action of $G$ through $\pi$. -/
theorem smulInvariantMeasure_homAction [MeasurableMul Q] (π : G →* Q) (μQ : Measure Q) [μQ.IsMulLeftInvariant] :
    @SMulInvariantMeasure G Q (homAction π).toSMul _ μQ := by
  let _ := homAction π
  refine ⟨fun g t ht => ?_⟩
  show μQ ((fun q => π g * q) ⁻¹' t) = μQ t
  rw [← Measure.map_apply (measurable_const_mul (π g)) ht, map_mul_left_eq_self]

/-- **Weil's Thm 2.4.4 (measure split along a homomorphism):** for $\pi : G\to Q$ with a measurable section $\sigma$
and left-invariant $\mu_Q$, $\mu_{\ker\pi}$, the image of $\mu_Q\otimes\mu_{\ker\pi}$ under $(q, k)\mapsto\sigma(q)k$ is a
left-invariant measure on $G$ (so it is the Haar measure of $G$, `OrbitSection.fibMeasure_eq_smul`). -/
@[kb "weil1982" "§2.4, Thm 2.4.4 [unverified page]"]
theorem isMulLeftInvariant_homFibMeasure [MeasurableMul₂ Q] [MeasurableMul₂ G] [MeasurableInv G] (π : G →* Q)
    (hπ : Measurable π) (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (hσm : Measurable σ) (μQ : Measure Q)
    [SFinite μQ] [μQ.IsMulLeftInvariant]
    (μK : Measure (@OrbitSection.stab G Q _ (homAction π) _ _ (homSection π hπ σ hσ hσm))) [SFinite μK]
    [μK.IsMulLeftInvariant] :
    (@OrbitSection.fibMeasure G Q _ (homAction π) _ _ (homSection π hπ σ hσ hσm) μQ μK).IsMulLeftInvariant := by
  let _ := homAction π
  have := smulInvariantMeasure_homAction π μQ
  infer_instance

end Hom

end

end QuadFormsKB.Tamagawa.Measure.Weil
