/-
# Weil's additive zeta function of a lattice as an Epstein zeta function

**Layer:** $F$ totally real with $\mathcal O_F$ a PID, $L = \bigoplus_iJ_ie_i \subset F^n$ (`latVec`) with totally positive Gram matrix $A$,
$Q(\xi) = \xi^{\mathsf T}A\xi$; $U = \mathcal O_F^\times$ acting on $L\setminus0$ by scalars.

$$Z^+_L(s) = |d_F|^{-1/2}\,\pi^{-d(\frac n2+s)}\,\Gamma\big(\tfrac n2+s\big)^d\;E_L\big(\tfrac n2+s\big),\qquad
  E_L(t) = \sum_{\xi\in U\backslash(L\setminus0)}|N_{F/\mathbb Q}(Q(\xi))|^{-t}\qquad(\texttt{additiveZeta\_eq\_epstein}),$$
for $n + 2s > 1$, an equality in $[0,\infty]$. *Proof.* the unfolding `additiveZeta_eq_tsum_sqClasses` writes $Z^+_L(s)$ as a sum over the
square classes $\rho$ and the fractional ideals $\mathfrak b$ of $N\mathfrak b^{-n-2s}\#\{\eta \in \mathfrak b^{-1}L : Q(\eta) = \rho\}$, with the evaluation of the archimedean factor (`archMellin_eq`). With $h_F = 1$, $\mathfrak b = (\lambda)$, and the pairs $(\lambda,\eta)$ cover each
$U$-orbit in the shell $Q(\xi)\in\rho F^{\times2}$ exactly twice (`tsum_shell_eq`, and one representative per orbit, `tsum_fiber_rep`).

Source: Weil 1982, §4.5, p. 109 (unfolding over $T(\rho)$) and §3.1, pp. 39–40; Voight 2021, §26.5, (26.5.9) (the Epstein zeta functions of
the ideal classes). Locators checked in the authors' texts.
-/
import QuadFormsKB.Tamagawa.QuatClassFinite
import QuadFormsKB.Tamagawa.SphericalUnfold
import QuadFormsKB.Tamagawa.SphericalFibration

open NumberField NumberField.InfinitePlace MeasureTheory Matrix
open scoped ENNReal Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalUnfold

/-! ### Free actions: sums over orbit representatives -/

section Reps

variable {G X : Type*} [Group G] [MulAction G X]

/-- `x` is the chosen representative (`Quotient.out`) of its orbit. -/
def IsRep (x : X) : Prop := (Quotient.mk (MulAction.orbitRel G X) x).out = x

theorem isRep_out (q : MulAction.orbitRel.Quotient G X) : IsRep (G := G) q.out := by
  unfold IsRep; rw [Quotient.out_eq]

open Classical in
/-- **A sum over the representatives is a sum over the orbits.** -/
theorem tsum_isRep (h : X → ℝ≥0∞) :
    ∑' x : X, (if IsRep (G := G) x then h x else 0) = ∑' q : MulAction.orbitRel.Quotient G X, h q.out := by
  have h1 : ∑' x : X, (if IsRep (G := G) x then h x else 0) =
      ∑' x : ({x | IsRep (G := G) x} : Set X), h x := by
    rw [tsum_subtype]
    refine tsum_congr fun x => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [h1]
  let e : ({x | IsRep (G := G) x} : Set X) ≃ MulAction.orbitRel.Quotient G X :=
    { toFun := fun x => Quotient.mk _ x.1
      invFun := fun q => ⟨q.out, isRep_out q⟩
      left_inv := fun x => Subtype.ext x.2
      right_inv := fun q => Quotient.out_eq q }
  rw [← e.symm.tsum_eq]
  rfl

/-- **Exactly one element of a free orbit is the representative.** -/
theorem existsUnique_smul_isRep (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) (y : X) :
    ∃! g : G, IsRep (G := G) (g • y) := by
  obtain ⟨g, hg⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G X) y))
  -- hg : g • y = ⟦y⟧.out
  have hrep : ∀ g' : G, IsRep (G := G) (g' • y) ↔ g' • y = (Quotient.mk (MulAction.orbitRel G X) y).out := by
    intro g'
    have : (Quotient.mk (MulAction.orbitRel G X) (g' • y)) = Quotient.mk _ y := Quotient.sound ⟨g', rfl⟩
    unfold IsRep; rw [this]; exact eq_comm
  refine ⟨g, (hrep g).2 hg, fun g' hg' => ?_⟩
  have h1 : g' • y = g • y := ((hrep g').1 hg').trans hg.symm
  have h2 : (g⁻¹ * g') • y = y := by rw [mul_smul, h1, inv_smul_smul]
  have := hfree _ _ h2
  calc g' = g * (g⁻¹ * g') := by group
    _ = g := by rw [this, mul_one]

end Reps

/-! ### Lattice points modulo units -/

section LatUnits

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

variable (F) in
/-- **The units $\mathcal O_F^\times \subseteq F^\times$.** -/
def unitsF : Subgroup Fˣ := (Units.map (algebraMap (𝓞 F) F).toMonoidHom).range

/-- **The nonzero points of $L = \bigoplus_iJ_ie_i$.** -/
abbrev LatPt (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) := {ξ : Fin n → F // ξ ≠ 0 ∧ LatMem J ξ}

theorem latMem_smul_unit (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {u : Fˣ} (hu : u ∈ unitsF F) {ξ : Fin n → F}
    (hξ : LatMem J ξ) : LatMem J ((u : F) • ξ) := by
  obtain ⟨w, rfl⟩ := hu
  intro i
  have : (w : 𝓞 F) • ξ i ∈ (J i : FractionalIdeal (𝓞 F)⁰ F) := Submodule.smul_mem _ _ (hξ i)
  rw [Algebra.smul_def] at this
  exact this

instance (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : MulAction (unitsF F) (LatPt J) where
  smul u ξ := ⟨((u : Fˣ) : F) • ξ.1, smul_ne_zero (Units.ne_zero _) ξ.2.1, latMem_smul_unit J u.2 ξ.2.2⟩
  one_smul ξ := Subtype.ext (one_smul _ _)
  mul_smul u w ξ := Subtype.ext (by
    show (((u * w : unitsF F) : Fˣ) : F) • ξ.1 = ((u : Fˣ) : F) • (((w : Fˣ) : F) • ξ.1)
    rw [Subgroup.coe_mul, Units.val_mul, mul_smul])

theorem smul_latPt_val {J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ} (u : unitsF F) (ξ : LatPt J) :
    (u • ξ).1 = ((u : Fˣ) : F) • ξ.1 := rfl

theorem latPt_free (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : unitsF F) (ξ : LatPt J) (h : u • ξ = ξ) :
    u = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, ξ.1 i ≠ 0 := by
    by_contra hc; push Not at hc; exact ξ.2.1 (funext hc)
  have h1 := congrFun (congrArg Subtype.val h) i
  rw [smul_latPt_val, Pi.smul_apply, smul_eq_mul] at h1
  have : ((u : Fˣ) : F) = 1 := by
    have := mul_right_cancel₀ hi (h1.trans (one_mul _).symm)
    exact this
  exact Subtype.ext (Units.ext this)

/-- **The Epstein zeta function of the lattice** $E_L(t) = \sum_{\xi\in\mathcal O_F^\times\backslash(L\setminus0)}|N(Q(\xi))|^{-t}$, in $[0,\infty]$. -/
def epsteinLat (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) : ℝ≥0∞ :=
  ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
    ENNReal.ofReal (|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| ^ (-t))

variable [IsPrincipalIdealRing (𝓞 F)]

/-- Every fractional ideal is principal ($h_F = 1$). -/
theorem exists_toPrincipalIdeal_eq (𝔟 : FracIdeal F) : ∃ l : Fˣ, toPrincipalIdeal (𝓞 F) F l = 𝔟 := by
  obtain ⟨g, hg⟩ := (𝔟 : FractionalIdeal (𝓞 F)⁰ F).isPrincipal
  refine (mem_principal_ideals_iff (R := 𝓞 F) (K := F)).2 ⟨g, ?_⟩
  apply FractionalIdeal.coeToSubmodule_injective
  show ((FractionalIdeal.spanSingleton (𝓞 F)⁰ g : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) =
    ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
  rw [FractionalIdeal.coe_spanSingleton, hg]

/-- The fibres of $\lambda \mapsto (\lambda)$ are the cosets of $\mathcal O_F^\times$. -/
theorem toPrincipalIdeal_eq_toPrincipalIdeal_iff (l l' : Fˣ) :
    toPrincipalIdeal (𝓞 F) F l' = toPrincipalIdeal (𝓞 F) F l ↔ l' * l⁻¹ ∈ unitsF F := by
  rw [toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    -- z • l' = l
    refine ⟨z⁻¹, Units.ext ?_⟩
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← hz, Units.smul_def, Algebra.smul_def]
    have hz0 : algebraMap (𝓞 F) F (z : 𝓞 F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 z.ne_zero
    have hl : (l' : F) ≠ 0 := l'.ne_zero
    rw [mul_inv, ← mul_assoc]
    field_simp
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨w, hw⟩
    refine ⟨w⁻¹, ?_⟩
    have hw' := congrArg (fun u : Fˣ => (u : F)) hw
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul,
      Units.val_inv_eq_inv_val] at hw'
    have hinv : algebraMap (𝓞 F) F ((w⁻¹ : (𝓞 F)ˣ) : 𝓞 F) = (algebraMap (𝓞 F) F (w : 𝓞 F))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [Units.smul_def, Algebra.smul_def, hinv, hw']
    have hl : (l : F) ≠ 0 := l.ne_zero
    have hl' : (l' : F) ≠ 0 := l'.ne_zero
    field_simp

theorem twist_one (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : twist 1 J = J := by
  funext i; simp [twist]

theorem idealNorm_toPrincipalIdeal (l : Fˣ) :
    idealNorm F (toPrincipalIdeal (𝓞 F) F l) = |((Algebra.norm ℚ (l : F) : ℚ) : ℝ)| := by
  have h := idealNorm_principalSMulFin F l 1
  rw [principalSMulFin, mul_one] at h
  rw [h]
  have : idealNorm F (1 : FracIdeal F) = 1 := by simp [idealNorm]
  rw [this, mul_one]

theorem latMem_twist_toPrincipalIdeal (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (l : Fˣ) (η : Fin n → F) :
    LatMem (twist (toPrincipalIdeal (𝓞 F) F l) J) η ↔ LatMem J ((l : F) • η) := by
  have h := latMem_twist_principal J l 1 η
  rwa [principalSMulFin, mul_one, twist_one] at h

open Classical in
/-- **One representative per fibre**: for $\eta \ne 0$ with $\eta \in \mathfrak b^{-1}L$, exactly one $\lambda$ with $(\lambda) = \mathfrak b$ makes
$\lambda\eta$ the chosen representative of its $\mathcal O_F^\times$-orbit. -/
theorem tsum_fiber_rep (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (𝔟 : FracIdeal F) {η : Fin n → F} (hη0 : η ≠ 0)
    (hL : LatMem (twist 𝔟 J) η) :
    ∑' l : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟},
      (if h : ((l : Fˣ) : F) • η ≠ 0 ∧ LatMem J (((l : Fˣ) : F) • η) then
        (if IsRep (G := unitsF F) (⟨_, h⟩ : LatPt J) then (1 : ℝ≥0∞) else 0) else 0) = 1 := by
  obtain ⟨l0, hl0⟩ := exists_toPrincipalIdeal_eq 𝔟
  have hL0 : LatMem J ((l0 : F) • η) := (latMem_twist_toPrincipalIdeal J l0 η).1 (hl0 ▸ hL)
  set y : LatPt J := ⟨(l0 : F) • η, smul_ne_zero (Units.ne_zero _) hη0, hL0⟩
  obtain ⟨u, hu, huniq⟩ := existsUnique_smul_isRep (latPt_free J) y
  let e : unitsF F ≃ {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟} :=
    { toFun := fun w => ⟨(w : Fˣ) * l0, by
        rw [← hl0, toPrincipalIdeal_eq_toPrincipalIdeal_iff, mul_inv_cancel_right]; exact w.2⟩
      invFun := fun l => ⟨l.1 * l0⁻¹, (toPrincipalIdeal_eq_toPrincipalIdeal_iff l0 l.1).1 (l.2.trans hl0.symm)⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun l => Subtype.ext (by simp) }
  rw [← e.tsum_eq]
  have hterm : ∀ w : unitsF F, (if h : (((e w : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟}) : Fˣ) : F) • η ≠ 0 ∧
      LatMem J ((((e w : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟}) : Fˣ) : F) • η) then
        (if IsRep (G := unitsF F) (⟨_, h⟩ : LatPt J) then (1 : ℝ≥0∞) else 0) else 0) =
      if IsRep (G := unitsF F) (w • y) then 1 else 0 := by
    intro w
    have hval : (((e w : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟}) : Fˣ) : F) • η = (w • y).1 := by
      show (((w : Fˣ) * l0 : Fˣ) : F) • η = ((w : Fˣ) : F) • ((l0 : F) • η)
      rw [Units.val_mul, mul_smul]
    have hmem : (((e w : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟}) : Fˣ) : F) • η ≠ 0 ∧
        LatMem J ((((e w : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟}) : Fˣ) : F) • η) := by
      rw [hval]; exact (w • y).2
    rw [dif_pos hmem]
    congr 2
    exact Subtype.ext hval
  simp_rw [hterm]
  rw [tsum_eq_single u (fun w hw => by rw [if_neg]; intro h; exact hw (huniq w h)), if_pos hu]

open Classical in
/-- The weight on vectors used with `tsum_shell_eq`: $w(\xi) = (|NQ(\xi)|/|N\rho|)^{-a/2}$ on the chosen orbit representatives in $L\setminus0$. -/
def repWeight (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ρ : F) (a : ℝ)
    (ξ : Fin n → F) : ℝ≥0∞ :=
  if h : ξ ≠ 0 ∧ LatMem J ξ then
    (if IsRep (G := unitsF F) (⟨ξ, h⟩ : LatPt J) then
      ENNReal.ofReal ((|(Algebra.norm ℚ (qv A ξ) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0) else 0

theorem abs_norm_qv_smul (A : Matrix (Fin n) (Fin n) F) (l : F) (η : Fin n → F) :
    |(Algebra.norm ℚ (qv A (l • η)) : ℝ)| = |(Algebra.norm ℚ l : ℝ)| ^ 2 * |(Algebra.norm ℚ (qv A η) : ℝ)| := by
  rw [SphericalUnfold.qv_smul, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow]

open Classical in
/-- **The $\rho$-sum over fractional ideals as an orbit sum** ($h_F = 1$, $\rho \ne 0$):
$$\sum_{\mathfrak b}N\mathfrak b^{-a}\,\#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho\} = 2\sum_{\xi\in U\backslash(L\setminus0),\ Q(\xi)\in\rho F^{\times2}}
  \Big(\frac{|NQ(\xi)|}{|N\rho|}\Big)^{-a/2}.$$ -/
theorem tsum_sphereCount_eq (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {ρ : F}
    (hρ : ρ ≠ 0) (a : ℝ) :
    ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) * sphereCount A J ρ 𝔟 =
      2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
        (if qv A q.out.1 ∈ sqClass ρ then
          ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0) := by
  set W := repWeight A J ρ a
  -- Step 1: the orbit sum as a vector sum
  have step1 : ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
      (if qv A q.out.1 ∈ sqClass ρ then
        ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0) =
      ∑' ξ : Fin n → F, (if qv A ξ ∈ sqClass ρ then W ξ else 0) := by
    have hsupp : Function.support (fun ξ : Fin n → F => if qv A ξ ∈ sqClass ρ then W ξ else 0) ⊆
        {ξ | ξ ≠ 0 ∧ LatMem J ξ} := by
      intro ξ hξ
      by_contra h
      apply hξ
      show (if qv A ξ ∈ sqClass ρ then repWeight A J ρ a ξ else 0) = 0
      rw [repWeight, dif_neg (show ¬(ξ ≠ 0 ∧ LatMem J ξ) from h)]; simp
    refine Eq.trans ?_ (tsum_subtype_eq_of_support_subset hsupp)
    rw [← tsum_isRep (G := unitsF F) (fun x : LatPt J => if qv A x.1 ∈ sqClass ρ then
        ENNReal.ofReal ((|(Algebra.norm ℚ (qv A x.1) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0)]
    refine tsum_congr fun x => ?_
    show _ = (if qv A x.1 ∈ sqClass ρ then W x.1 else 0)
    simp only [W, repWeight, dif_pos x.2]
    by_cases hr : IsRep (G := unitsF F) x
    · simp [hr]
    · simp [hr]
  -- Step 2: the shell is covered twice
  have step2 := tsum_shell_eq (qv A) (SphericalUnfold.qv_smul A) hρ W
  -- Step 3: the double sum over (λ, η)
  have step3 : ∑' l : Fˣ, ∑' η : Fin n → F, (if qv A η = ρ then W ((l : F) • η) else 0) =
      ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) * sphereCount A J ρ 𝔟 := by
    rw [ENNReal.tsum_comm]
    have hη : ∀ η : Fin n → F, ∑' l : Fˣ, (if qv A η = ρ then W ((l : F) • η) else 0) =
        ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) *
          (if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then 1 else 0) := by
      intro η
      by_cases hq : qv A η = ρ
      swap
      · simp [hq]
      have hη0 : η ≠ 0 := by rintro rfl; apply hρ; rw [← hq]; simp [qv]
      simp only [hq, if_true, true_and]
      rw [← (Equiv.sigmaFiberEquiv (toPrincipalIdeal (𝓞 F) F)).tsum_eq, ENNReal.tsum_sigma']
      refine tsum_congr fun 𝔟 => ?_
      have hW : ∀ l : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟},
          W (((Equiv.sigmaFiberEquiv (toPrincipalIdeal (𝓞 F) F)) ⟨𝔟, l⟩ : F) • η) =
            ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) *
              (if h : ((l : Fˣ) : F) • η ≠ 0 ∧ LatMem J (((l : Fˣ) : F) • η) then
                (if IsRep (G := unitsF F) (⟨_, h⟩ : LatPt J) then (1 : ℝ≥0∞) else 0) else 0) := by
        intro l
        rw [Equiv.sigmaFiberEquiv_apply]
        simp only [W, repWeight]
        split_ifs with h1 h2
        · have hn := idealNorm_toPrincipalIdeal (F := F) (l : Fˣ)
          rw [l.2] at hn
          rw [mul_one, abs_norm_qv_smul, hq, hn]
          have hN : 0 < |(Algebra.norm ℚ ρ : ℝ)| := abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hρ)
          rw [mul_div_assoc, div_self hN.ne', mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
          congr 2; push_cast; ring
        · rw [mul_zero]
        · rw [mul_zero]
      simp_rw [hW]
      rw [ENNReal.tsum_mul_left]
      congr 1
      by_cases hL : LatMem (twist 𝔟 J) η
      · rw [if_pos hL, tsum_fiber_rep J 𝔟 hη0 hL]
      · rw [if_neg hL]
        refine ENNReal.tsum_eq_zero.2 fun l => ?_
        rw [dif_neg]
        rintro ⟨-, h⟩
        exact hL ((latMem_twist_toPrincipalIdeal J l η).2 h |> fun h' => l.2 ▸ h')
    simp_rw [hη]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun 𝔟 => ?_
    rw [sphereCount, ← ENNReal.tsum_mul_left]
  rw [step1, step2, step3, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

omit [IsPrincipalIdealRing (𝓞 F)] in
/-- $\prod_v\sigma_v(\rho) = |N_{F/\mathbb Q}(\rho)|$ for $\rho$ totally positive. -/
theorem prod_realEmb_eq {ρ : F} (hρ : ∀ v : InfinitePlace F, 0 < realEmb F v ρ) :
    ∏ v : InfinitePlace F, realEmb F v ρ = |(Algebra.norm ℚ ρ : ℝ)| := by
  have h := InfinitePlace.prod_eq_abs_norm ρ
  rw [← Rat.cast_abs, ← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hm : v.mult = 1 := by unfold InfinitePlace.mult; rw [if_pos (IsTotallyReal.isReal v)]
  rw [hm, pow_one, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]
  exact (abs_of_pos (hρ v)).symm

/-- **Weil's additive zeta function of a lattice is an Epstein zeta function** ($h_F = 1$, $A$ totally positive, $n + 2s > 1$):
$$Z^+_L(s) = |d_F|^{-1/2}\big(\pi^{-(\frac n2+s)}\Gamma(\tfrac n2+s)\big)^{d}\,E_L\big(\tfrac n2+s\big).$$ -/
@[kb "weil1982" "§4.5, p. 109; §3.1, pp. 39–40"]
theorem additiveZeta_eq_epstein {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 1 < (n : ℝ) + 2 * s) :
    additiveZeta A J s = ENNReal.ofReal (ideleConst F * (π ^ (-((n : ℝ) + 2 * s) / 2) *
      Real.Gamma (((n : ℝ) + 2 * s) / 2)) ^ Fintype.card (InfinitePlace F)) *
        epsteinLat A J (((n : ℝ) + 2 * s) / 2) := by
  classical
  rw [additiveZeta_eq_tsum_sqClasses hA]
  set a : ℝ := (n : ℝ) + 2 * s with ha
  have h2 : ∀ c : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
      ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) * sphereCount A J (rep c) 𝔟 =
      ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
        (if qv A q.out.1 ∈ sqClass (rep c) then ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
          ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c) : ℝ)|) ^ (-(a / 2)))
          else 0) := by
    intro c
    rw [tsum_sphereCount_eq A J (rep_ne_zero c) a, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun q => ?_
    split_ifs
    · rw [← mul_assoc, mul_comm (2⁻¹ * _ * _) 2, ← mul_assoc, ← mul_assoc,
        ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    · simp
  rw [tsum_congr h2]
  rw [ENNReal.tsum_comm, epsteinLat, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun q => ?_
  set ξ := q.out.1
  have hξ0 : ξ ≠ 0 := q.out.2.1
  have hQ0 : qv A ξ ≠ 0 := qv_ne_zero hA hξ0
  set c0 := sqCls (qv A ξ)
  rw [tsum_eq_single c0 (fun c hc => by rw [if_neg]; intro h; exact hc ((sqClass_out_iff hQ0 c).1 h).symm)]
  rw [if_pos ((sqClass_out_iff hQ0 c0).2 rfl)]
  set ρ := rep c0
  obtain ⟨y, hy0, hQy⟩ := (sqClass_out_iff hQ0 c0).2 rfl
  have hρpos : ∀ v : InfinitePlace F, 0 < realEmb F v ρ := by
    intro v
    have h1 := realEmb_qv_pos hA v hξ0
    rw [hQy, map_mul, map_pow] at h1
    have hy : 0 < realEmb F v y ^ 2 := by
      have : realEmb F v y ≠ 0 := (map_ne_zero_iff _ (realEmb F v).injective).2 hy0
      positivity
    exact (pos_iff_pos_of_mul_pos h1).2 hy
  rw [archMellin_eq hρpos hs]
  have hρ0 : ρ ≠ 0 := rep_ne_zero c0
  have hρN : 0 < |(Algebra.norm ℚ ρ : ℝ)| :=
    abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hρ0)
  have hQN : 0 ≤ |(Algebra.norm ℚ (qv A ξ) : ℝ)| := abs_nonneg _
  have hΓ : 0 ≤ Real.Gamma (a / 2) := Real.Gamma_nonneg_of_nonneg (by linarith)
  have hC : 0 < ideleConst F := by
    rw [SphericalFibration.ideleConst_eq]
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)) _
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg (Real.rpow_nonneg (mul_pos Real.pi_pos (hρpos v)).le _)
    hΓ), ← ENNReal.ofReal_mul hC.le, ← ENNReal.ofReal_mul (mul_nonneg hC.le (Finset.prod_nonneg fun v _ =>
    mul_nonneg (Real.rpow_nonneg (mul_pos Real.pi_pos (hρpos v)).le _) hΓ)),
    ← ENNReal.ofReal_mul (mul_nonneg hC.le (pow_nonneg (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hΓ) _))]
  congr 1
  have hprod : ∏ v : InfinitePlace F, (π * realEmb F v ρ) ^ (-a / 2) * Real.Gamma (a / 2) =
      (π ^ (-a / 2) * Real.Gamma (a / 2)) ^ Fintype.card (InfinitePlace F) * |(Algebra.norm ℚ ρ : ℝ)| ^ (-a / 2) := by
    rw [← prod_realEmb_eq hρpos, ← Real.finset_prod_rpow _ _ (fun v _ => (hρpos v).le), ← Finset.card_univ,
      ← Finset.prod_const,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Real.mul_rpow Real.pi_pos.le (hρpos v).le]; ring
  rw [hprod, Real.div_rpow hQN hρN.le, (by ring : -(a / 2) = -a / 2)]
  have hρa : 0 < |(Algebra.norm ℚ ρ : ℝ)| ^ (-a / 2) := Real.rpow_pos_of_pos hρN _
  field_simp

/-- The archimedean constant $K(s) = |d_F|^{-1/2}(\pi^{-(n+2s)/2}\Gamma(\frac{n+2s}2))^{d}$. -/
def epsteinConst (F : Type) [Field F] [NumberField F] (n : ℕ) (s : ℝ) : ℝ :=
  ideleConst F * (π ^ (-((n : ℝ) + 2 * s) / 2) * Real.Gamma (((n : ℝ) + 2 * s) / 2)) ^ Fintype.card (InfinitePlace F)

omit [IsPrincipalIdealRing (𝓞 F)] in
theorem epsteinConst_pos (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) : 0 < epsteinConst F n s := by
  have hC : 0 < ideleConst F := by
    rw [SphericalFibration.ideleConst_eq]
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)) _
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact mul_pos hC (pow_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))) _)

omit [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] in
theorem continuousAt_epsteinConst (hn : 1 ≤ n) : ContinuousAt (epsteinConst F n) 0 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epsteinConst
  refine continuousAt_const.mul (ContinuousAt.pow (ContinuousAt.mul ?_ ?_) _)
  · exact (Real.continuousAt_const_rpow Real.pi_pos.ne').comp (by fun_prop)
  · refine ((Real.differentiableAt_Gamma fun m => ?_).continuousAt).comp (f := fun s : ℝ => ((n : ℝ) + 2 * s) / 2)
      (by fun_prop)
    have : (0 : ℝ) < ((n : ℝ) + 2 * 0) / 2 := by linarith
    intro h; rw [h] at this; have := Nat.cast_nonneg (α := ℝ) m; linarith

/-- $E_L(t) < \infty$ for $t > n/2$. -/
theorem epsteinLat_lt_top {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) {t : ℝ} (ht : (n : ℝ) / 2 < t) :
    epsteinLat A J t < ⊤ := by
  set s := t - n / 2
  have hs : 0 < s := by simp only [s]; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : additiveZeta A J s = ENNReal.ofReal (epsteinConst F n s) * epsteinLat A J (((n : ℝ) + 2 * s) / 2) :=
    additiveZeta_eq_epstein hA J (by linarith)
  have hst : ((n : ℝ) + 2 * s) / 2 = t := by simp only [s]; ring
  rw [hst] at h
  have hlt := additiveZeta_lt_top hA J hs
  rw [h] at hlt
  have hK := epsteinConst_pos (F := F) hn hs.le
  exact (ENNReal.mul_lt_top_iff.1 hlt).elim (fun h' => h'.2)
    (fun h' => h'.elim (fun h0 => absurd h0 (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hK))
      (fun h0 => by rw [h0]; exact ENNReal.zero_lt_top))

/-- **The residue of the Epstein zeta function** at $t = n/2$ (from `tendsto_mul_additiveZeta`):
$$\lim_{t\to n/2^+}(t - \tfrac n2)E_L(t) = \frac{\rho_F}{2}\,\frac{c_L}{|d_F|^{-1/2}(\pi^{-n/2}\Gamma(\frac n2))^{d}}.$$ -/
@[kb "weil1982" "§4.4, pp. 97–98; §4.5, p. 109"]
theorem tendsto_sub_mul_epsteinLat {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun t : ℝ => (t - n / 2) * (epsteinLat A J t).toReal) (nhdsWithin ((n : ℝ) / 2) (Set.Ioi ((n : ℝ) / 2)))
      (nhds (dedekindZeta_residue F / 2 * latConst A J / epsteinConst F n 0)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := tendsto_mul_additiveZeta hA J hn
  have hK0 := epsteinConst_pos (F := F) hn le_rfl
  have h2 : Filter.Tendsto (epsteinConst F n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (epsteinConst F n 0)) :=
    (continuousAt_epsteinConst hn).tendsto.mono_left nhdsWithin_le_nhds
  have h3 := h1.div h2 hK0.ne'
  -- the shift t = n/2 + s
  have hmap : Filter.Tendsto (fun t : ℝ => t - n / 2) (nhdsWithin ((n : ℝ) / 2) (Set.Ioi ((n : ℝ) / 2)))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    have hc : Filter.Tendsto (fun t : ℝ => t - n / 2) (nhds ((n : ℝ) / 2)) (nhds ((n : ℝ) / 2 - n / 2)) :=
      ((continuous_id.sub continuous_const : Continuous fun t : ℝ => t - n / 2).tendsto _)
    rw [sub_self] at hc
    refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.2 (Set.mem_Ioi.1 ht)
  refine (h3.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (n : ℝ) / 2 < t := Set.mem_Ioi.1 ht
  simp only [Function.comp_apply, Pi.div_apply]
  set s := t - n / 2
  have hs : 0 < s := by simp only [s]; linarith
  have h : additiveZeta A J s = ENNReal.ofReal (epsteinConst F n s) * epsteinLat A J (((n : ℝ) + 2 * s) / 2) :=
    additiveZeta_eq_epstein hA J (by linarith)
  have hst : ((n : ℝ) + 2 * s) / 2 = t := by simp only [s]; ring
  rw [hst] at h
  have hK := epsteinConst_pos (F := F) hn hs.le
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le]
  field_simp

end LatUnits

end QuadFormsKB.QuatOrder
