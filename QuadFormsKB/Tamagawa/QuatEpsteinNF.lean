/-
# Weil's additive zeta function as a sum of Epstein zeta functions over the ideal classes

**Layer:** $F$ totally real (any class number), $L = \bigoplus_iJ_ie_i \subset F^n$ with totally positive Gram matrix $A$, $U = \mathcal O_F^\times$.
`QuatEpstein.additiveZeta_eq_epstein` writes $Z^+_L$ as a *single* Epstein zeta function when $h_F = 1$ (every fractional ideal $\mathfrak b$ is
$(\lambda)$). Here, for any class number, with $\mathfrak c_q$ ($q \in \mathrm{Cl}_F$) the chosen class representatives (`classRep`):
$$Z^+_L(s) = K(s)\sum_{q\in \mathrm{Cl}_F}N(\mathfrak c_q)^{-(n+2s)}\;E_{\mathfrak c_q^{-1}L}\big(\tfrac{n+2s}2\big)\qquad(\texttt{Gen.additiveZeta\_eq\_epstein\_cls}),$$
$E_{M}(t) = \sum_{\xi\in U\backslash(M\setminus0)}|N_{F/\mathbb Q}Q(\xi)|^{-t}$ (`epsteinLat`) for the *non-free* lattices $\mathfrak c_q^{-1}L$
(`twist (classRep q) J`).

*Proof.* Same as in the PID case, class by class: a fractional ideal is $\mathfrak b = (\lambda)\mathfrak c_q$ for a unique class $q$, and
$\eta \in \mathfrak b^{-1}L \iff \lambda\eta \in \mathfrak c_q^{-1}L$ (`latMem_twist_principal`), so the pairs $(\lambda,\eta)$ cover each $U$-orbit of the
shell $Q(\xi)\in\rho F^{\times2}$ of $\mathfrak c_q^{-1}L$ exactly twice (`tsum_shell_eq`, `tsum_fiber_rep_cls`).

Source: Weil 1982, §4.5, p. 109 and §3.1; Voight, *Quaternion Algebras* (2021), (26.5.9) (the Epstein zeta functions of the ideal classes).
-/
import QuadFormsKB.Tamagawa.QuatEpstein

open NumberField NumberField.InfinitePlace MeasureTheory Matrix
open scoped ENNReal Real nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.HilbertModular QuadFormsKB.IdeleClass QuadFormsKB.AdditiveZeta QuadFormsKB.SphericalZeta
  QuadFormsKB.SphericalUnfold

namespace Gen

section Classes

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

/-- A fractional ideal is principal. -/
def Prin (𝔟 : FracIdeal F) : Prop := ∃ l : Fˣ, toPrincipalIdeal (𝓞 F) F l = 𝔟

/-- The fibres of $\lambda \mapsto (\lambda)$ are the cosets of $\mathcal O_F^\times$. -/
theorem toPrincipalIdeal_eq_iff_cls (l l' : Fˣ) :
    toPrincipalIdeal (𝓞 F) F l' = toPrincipalIdeal (𝓞 F) F l ↔ l' * l⁻¹ ∈ unitsF F := by
  rw [toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z⁻¹, Units.ext ?_⟩
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul,
      Units.val_inv_eq_inv_val]
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

theorem twist_one_cls (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) : twist 1 J = J := by
  funext i; simp [twist]

theorem idealNorm_toPrincipalIdeal_cls (l : Fˣ) :
    idealNorm F (toPrincipalIdeal (𝓞 F) F l) = |((Algebra.norm ℚ (l : F) : ℚ) : ℝ)| := by
  have h := idealNorm_principalSMulFin F l 1
  rw [principalSMulFin, mul_one] at h
  rw [h]
  have : idealNorm F (1 : FracIdeal F) = 1 := by simp [idealNorm]
  rw [this, mul_one]

theorem latMem_twist_toPrincipalIdeal_cls (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (l : Fˣ) (η : Fin n → F) :
    LatMem (twist (toPrincipalIdeal (𝓞 F) F l) J) η ↔ LatMem J ((l : F) • η) := by
  have h := latMem_twist_principal J l 1 η
  rwa [principalSMulFin, mul_one, twist_one_cls] at h

theorem abs_norm_qv_smul_cls (A : Matrix (Fin n) (Fin n) F) (l : F) (η : Fin n → F) :
    |(Algebra.norm ℚ (qv A (l • η)) : ℝ)| = |(Algebra.norm ℚ l : ℝ)| ^ 2 * |(Algebra.norm ℚ (qv A η) : ℝ)| := by
  rw [SphericalUnfold.qv_smul, map_mul, map_pow, Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow]

open Classical in
/-- **One representative per fibre**, for any fractional ideal $\mathfrak b$ that is principal. -/
theorem tsum_fiber_rep_cls (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (𝔟 : FracIdeal F) (hprin : Prin 𝔟)
    {η : Fin n → F} (hη0 : η ≠ 0) (hL : LatMem (twist 𝔟 J) η) :
    ∑' l : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟},
      (if h : ((l : Fˣ) : F) • η ≠ 0 ∧ LatMem J (((l : Fˣ) : F) • η) then
        (if IsRep (G := unitsF F) (⟨_, h⟩ : LatPt J) then (1 : ℝ≥0∞) else 0) else 0) = 1 := by
  obtain ⟨l0, hl0⟩ := hprin
  have hL0 : LatMem J ((l0 : F) • η) := (latMem_twist_toPrincipalIdeal_cls J l0 η).1 (hl0 ▸ hL)
  set y : LatPt J := ⟨(l0 : F) • η, smul_ne_zero (Units.ne_zero _) hη0, hL0⟩
  obtain ⟨u, hu, huniq⟩ := existsUnique_smul_isRep (latPt_free J) y
  let e : unitsF F ≃ {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟} :=
    { toFun := fun w => ⟨(w : Fˣ) * l0, by
        rw [← hl0, toPrincipalIdeal_eq_iff_cls, mul_inv_cancel_right]; exact w.2⟩
      invFun := fun l => ⟨l.1 * l0⁻¹, (toPrincipalIdeal_eq_iff_cls l0 l.1).1 (l.2.trans hl0.symm)⟩
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
/-- **The $\rho$-sum over the principal fractional ideals as an orbit sum** ($\rho \ne 0$, any class number):
$$\sum_{\mathfrak b\text{ principal}}N\mathfrak b^{-a}\,\#\{\eta\in\mathfrak b^{-1}L : Q(\eta) = \rho\} = 2\sum_{\xi\in U\backslash(L\setminus0),\ Q(\xi)\in\rho F^{\times2}}
  \Big(\frac{|NQ(\xi)|}{|N\rho|}\Big)^{-a/2}.$$ -/
theorem tsum_sphereCount_prin (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {ρ : F}
    (hρ : ρ ≠ 0) (a : ℝ) :
    ∑' 𝔟 : FracIdeal F, (if Prin 𝔟 then ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) else 0) * sphereCount A J ρ 𝔟 =
      2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
        (if qv A q.out.1 ∈ sqClass ρ then
          ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0) := by
  set W := repWeight A J ρ a
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
  have step2 := tsum_shell_eq (qv A) (SphericalUnfold.qv_smul A) hρ W
  have step3 : ∑' l : Fˣ, ∑' η : Fin n → F, (if qv A η = ρ then W ((l : F) • η) else 0) =
      ∑' 𝔟 : FracIdeal F, (if Prin 𝔟 then ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) else 0) * sphereCount A J ρ 𝔟 := by
    rw [ENNReal.tsum_comm]
    have hη : ∀ η : Fin n → F, ∑' l : Fˣ, (if qv A η = ρ then W ((l : F) • η) else 0) =
        ∑' 𝔟 : FracIdeal F, (if Prin 𝔟 then ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) else 0) *
          (if qv A η = ρ ∧ LatMem (twist 𝔟 J) η then 1 else 0) := by
      intro η
      by_cases hq : qv A η = ρ
      swap
      · simp [hq]
      have hη0 : η ≠ 0 := by rintro rfl; apply hρ; rw [← hq]; simp [qv]
      simp only [hq, if_true, true_and]
      rw [← (Equiv.sigmaFiberEquiv (toPrincipalIdeal (𝓞 F) F)).tsum_eq, ENNReal.tsum_sigma']
      refine tsum_congr fun 𝔟 => ?_
      by_cases hprin : Prin 𝔟
      · rw [if_pos hprin]
        have hW : ∀ l : {l : Fˣ // toPrincipalIdeal (𝓞 F) F l = 𝔟},
            W (((Equiv.sigmaFiberEquiv (toPrincipalIdeal (𝓞 F) F)) ⟨𝔟, l⟩ : F) • η) =
              ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) *
                (if h : ((l : Fˣ) : F) • η ≠ 0 ∧ LatMem J (((l : Fˣ) : F) • η) then
                  (if IsRep (G := unitsF F) (⟨_, h⟩ : LatPt J) then (1 : ℝ≥0∞) else 0) else 0) := by
          intro l
          rw [Equiv.sigmaFiberEquiv_apply]
          simp only [W, repWeight]
          split_ifs with h1 h2
          · have hn := idealNorm_toPrincipalIdeal_cls (F := F) (l : Fˣ)
            rw [l.2] at hn
            rw [mul_one, abs_norm_qv_smul_cls, hq, hn]
            have hN : 0 < |(Algebra.norm ℚ ρ : ℝ)| :=
              abs_pos.2 (by exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ)).2 hρ)
            rw [mul_div_assoc, div_self hN.ne', mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
            congr 2; push_cast; ring
          · rw [mul_zero]
          · rw [mul_zero]
        simp_rw [hW]
        rw [ENNReal.tsum_mul_left]
        congr 1
        by_cases hL : LatMem (twist 𝔟 J) η
        · rw [if_pos hL, tsum_fiber_rep_cls J 𝔟 hprin hη0 hL]
        · rw [if_neg hL]
          refine ENNReal.tsum_eq_zero.2 fun l => ?_
          rw [dif_neg]
          rintro ⟨-, h⟩
          exact hL ((latMem_twist_toPrincipalIdeal_cls J l η).2 h |> fun h' => l.2 ▸ h')
      · rw [if_neg hprin, zero_mul]
        refine ENNReal.tsum_eq_zero.2 fun l => ?_
        exact absurd ⟨l.1, l.2⟩ hprin
    simp_rw [hη]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun 𝔟 => ?_
    rw [sphereCount, ← ENNReal.tsum_mul_left]
  rw [step1, step2, step3, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]


theorem prin_iff_mk_eq_one (𝔟 : FracIdeal F) : Prin 𝔟 ↔ ClassGroup.mk F 𝔟 = 1 := by
  constructor
  · rintro ⟨l, rfl⟩
    refine (ClassGroup.mk_eq_one_iff).2 ?_
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  · intro h
    rw [ClassGroup.mk_eq_one_iff] at h
    obtain ⟨⟨x, hx⟩⟩ := h
    have hx0 : x ≠ 0 := by
      rintro rfl
      have : ((𝔟 : FracIdeal F) : FractionalIdeal (𝓞 F)⁰ F) = 0 := by
        rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_zero, hx]; simp
      exact 𝔟.ne_zero this
    refine ⟨Units.mk0 x hx0, ?_⟩
    rw [toPrincipalIdeal_eq_iff, ← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton, hx,
      Units.val_mk0]

open Classical in
/-- **A sum over all fractional ideals is a sum over the ideal classes of sums over principal ideals** (translated by the class
representative): $\sum_{\mathfrak b}f(\mathfrak b) = \sum_{c\in\mathrm{Cl}}\sum_{\mathfrak b'\text{ principal}}f(\mathfrak b'\mathfrak c_c)$. -/
theorem tsum_fracIdeal_cls (f : FracIdeal F → ℝ≥0∞) :
    ∑' 𝔟 : FracIdeal F, f 𝔟 = ∑' c : ClassGroup (𝓞 F),
      ∑' 𝔟' : FracIdeal F, (if Prin 𝔟' then f (𝔟' * classRep F c) else 0) := by
  rw [← (Equiv.sigmaFiberEquiv (ClassGroup.mk F)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun c => ?_
  let e : {𝔟' : FracIdeal F // Prin 𝔟'} ≃ {𝔟 : FracIdeal F // ClassGroup.mk F 𝔟 = c} :=
    { toFun := fun 𝔟' => ⟨𝔟'.1 * classRep F c, by
        rw [map_mul, mk_classRep, (prin_iff_mk_eq_one _).1 𝔟'.2, one_mul]⟩
      invFun := fun 𝔟 => ⟨𝔟.1 * (classRep F c)⁻¹, (prin_iff_mk_eq_one _).2 (by
        rw [map_mul, map_inv, mk_classRep, 𝔟.2, mul_inv_cancel])⟩
      left_inv := fun 𝔟' => Subtype.ext (by simp)
      right_inv := fun 𝔟 => Subtype.ext (by simp) }
  rw [← e.tsum_eq]
  have : ∑' 𝔟' : FracIdeal F, (if Prin 𝔟' then f (𝔟' * classRep F c) else 0) =
      ∑' 𝔟' : ({𝔟' : FracIdeal F | Prin 𝔟'} : Set (FracIdeal F)), f (𝔟'.1 * classRep F c) := by
    rw [tsum_subtype {𝔟' : FracIdeal F | Prin 𝔟'} (fun 𝔟' => f (𝔟' * classRep F c))]
    refine tsum_congr fun 𝔟' => ?_
    simp [Set.indicator_apply]
  rw [this]
  rfl


theorem idealNorm_mul_cls (𝔟 𝔠 : FracIdeal F) : idealNorm F (𝔟 * 𝔠) = idealNorm F 𝔟 * idealNorm F 𝔠 := by
  simp only [idealNorm, Units.val_mul, map_mul, Rat.cast_mul]

theorem sphereCount_mul_cls (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ρ : F)
    (𝔟' 𝔠 : FracIdeal F) : sphereCount A J ρ (𝔟' * 𝔠) = sphereCount A (twist 𝔠 J) ρ 𝔟' := by
  have : twist (𝔟' * 𝔠) J = twist 𝔟' (twist 𝔠 J) := by
    funext i; simp only [twist, mul_inv, mul_assoc]
  unfold sphereCount
  refine tsum_congr fun η => ?_
  rw [this]

open Classical in
/-- **The tail of the unfolding** (no class number hypothesis): summing the orbit sums over the square classes gives the Epstein zeta function. -/
theorem sum_sqClasses_orbit_eq {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 1 < (n : ℝ) + 2 * s) :
    ∑' c : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
        (2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
          (if qv A q.out.1 ∈ sqClass (rep c) then
            ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c) : ℝ)|) ^
              (-(((n : ℝ) + 2 * s) / 2))) else 0)) =
      ENNReal.ofReal (ideleConst F * (π ^ (-((n : ℝ) + 2 * s) / 2) *
        Real.Gamma (((n : ℝ) + 2 * s) / 2)) ^ Fintype.card (InfinitePlace F)) *
        epsteinLat A J (((n : ℝ) + 2 * s) / 2) := by
  set a : ℝ := (n : ℝ) + 2 * s with ha
  have h2 : ∀ c : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
      (2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
          (if qv A q.out.1 ∈ sqClass (rep c) then
            ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c) : ℝ)|) ^
              (-(a / 2))) else 0)) =
      ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt J),
        (if qv A q.out.1 ∈ sqClass (rep c) then ENNReal.ofReal (ideleConst F) * archMellin n s (rep c) *
          ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c) : ℝ)|) ^ (-(a / 2)))
          else 0) := by
    intro c
    rw [← mul_assoc, mul_comm (2⁻¹ * _ * _) 2, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun q => ?_
    split_ifs
    · rfl
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


open Classical in
/-- The $\rho$-sum over **all** fractional ideals, as a sum over the classes of orbit sums. -/
theorem tsum_sphereCount_cls (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {ρ : F}
    (hρ : ρ ≠ 0) (a : ℝ) :
    ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) * sphereCount A J ρ 𝔟 =
      ∑' c : ClassGroup (𝓞 F), ENNReal.ofReal (idealNorm F (classRep F c) ^ (-a)) *
        (2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist (classRep F c) J)),
          (if qv A q.out.1 ∈ sqClass ρ then
            ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ ρ : ℝ)|) ^ (-(a / 2))) else 0)) := by
  rw [tsum_fracIdeal_cls]
  refine tsum_congr fun c => ?_
  rw [← tsum_sphereCount_prin A (twist (classRep F c) J) hρ a, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun 𝔟' => ?_
  by_cases hp : Prin 𝔟'
  · rw [if_pos hp, if_pos hp, sphereCount_mul_cls, idealNorm_mul_cls,
      Real.mul_rpow (idealNorm_pos F _).le (idealNorm_pos F _).le, ENNReal.ofReal_mul (Real.rpow_nonneg
        (idealNorm_pos F _).le _)]
    ring
  · rw [if_neg hp, if_neg hp, zero_mul, mul_zero]

open Classical in
/-- **Weil's additive zeta function as a sum of Epstein zeta functions over the ideal classes** (any class number, $A$ totally positive,
$n + 2s > 1$):
$$Z^+_L(s) = |d_F|^{-1/2}\big(\pi^{-\frac{n+2s}2}\Gamma(\tfrac{n+2s}2)\big)^{d}\sum_{c\in\mathrm{Cl}_F}N(\mathfrak c_c)^{-(n+2s)}\,
  E_{\mathfrak c_c^{-1}L}\big(\tfrac{n+2s}2\big).$$ -/
@[kb "weil1982" "§4.5, p. 109; §3.1, pp. 39–40"]
theorem additiveZeta_eq_epstein_cls {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 1 < (n : ℝ) + 2 * s) :
    additiveZeta A J s = ENNReal.ofReal (ideleConst F * (π ^ (-((n : ℝ) + 2 * s) / 2) *
      Real.Gamma (((n : ℝ) + 2 * s) / 2)) ^ Fintype.card (InfinitePlace F)) *
        ∑' c : ClassGroup (𝓞 F), ENNReal.ofReal (idealNorm F (classRep F c) ^ (-((n : ℝ) + 2 * s))) *
          epsteinLat A (twist (classRep F c) J) (((n : ℝ) + 2 * s) / 2) := by
  rw [additiveZeta_eq_tsum_sqClasses hA]
  set a : ℝ := (n : ℝ) + 2 * s with ha
  have h1 : ∀ c' : SqClasses F, 2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c') *
      ∑' 𝔟 : FracIdeal F, ENNReal.ofReal (idealNorm F 𝔟 ^ (-a)) * sphereCount A J (rep c') 𝔟 =
      ∑' c : ClassGroup (𝓞 F), ENNReal.ofReal (idealNorm F (classRep F c) ^ (-a)) *
        (2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c') *
          (2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist (classRep F c) J)),
            (if qv A q.out.1 ∈ sqClass (rep c') then
              ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c') : ℝ)|) ^
                (-(a / 2))) else 0))) := by
    intro c'
    rw [tsum_sphereCount_cls A J (rep_ne_zero c') a, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun c => ?_
    ring
  rw [tsum_congr h1, ENNReal.tsum_comm]
  have h2 : ∀ c : ClassGroup (𝓞 F), ∑' c' : SqClasses F, ENNReal.ofReal (idealNorm F (classRep F c) ^ (-a)) *
      (2⁻¹ * ENNReal.ofReal (ideleConst F) * archMellin n s (rep c') *
        (2 * ∑' q : MulAction.orbitRel.Quotient (unitsF F) (LatPt (twist (classRep F c) J)),
          (if qv A q.out.1 ∈ sqClass (rep c') then
            ENNReal.ofReal ((|(Algebra.norm ℚ (qv A q.out.1) : ℝ)| / |(Algebra.norm ℚ (rep c') : ℝ)|) ^
              (-(a / 2))) else 0))) =
      ENNReal.ofReal (ideleConst F * (π ^ (-a / 2) * Real.Gamma (a / 2)) ^ Fintype.card (InfinitePlace F)) *
        (ENNReal.ofReal (idealNorm F (classRep F c) ^ (-a)) *
          epsteinLat A (twist (classRep F c) J) (a / 2)) := by
    intro c
    rw [ENNReal.tsum_mul_left, sum_sqClasses_orbit_eq hA (twist (classRep F c) J) hs]
    ring
  rw [tsum_congr h2, ENNReal.tsum_mul_left]


/-- **The class-weighted Epstein sum** $\sum_{c\in\mathrm{Cl}_F}N(\mathfrak c_c)^{-2t}E_{\mathfrak c_c^{-1}L}(t)$ of a lattice $L$. -/
def epsteinClsSum (A : Matrix (Fin n) (Fin n) F) (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (t : ℝ) : ℝ≥0∞ :=
  ∑' c : ClassGroup (𝓞 F), ENNReal.ofReal (idealNorm F (classRep F c) ^ (-(2 * t))) *
    epsteinLat A (twist (classRep F c) J) t

/-- $Z^+_L(s) = K(s)\cdot\texttt{epsteinClsSum}(\frac{n+2s}2)$. -/
theorem additiveZeta_eq_epsteinClsSum {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) {s : ℝ} (hs : 1 < (n : ℝ) + 2 * s) :
    additiveZeta A J s = ENNReal.ofReal (epsteinConst F n s) * epsteinClsSum A J (((n : ℝ) + 2 * s) / 2) := by
  rw [additiveZeta_eq_epstein_cls hA J hs, epsteinClsSum, epsteinConst]
  have : -(2 * (((n : ℝ) + 2 * s) / 2)) = -((n : ℝ) + 2 * s) := by ring
  simp only [this]

/-- **Finiteness**: every class Epstein zeta function converges for $t > n/2$ (and so does the class sum). -/
theorem epsteinClsSum_lt_top {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) {t : ℝ} (ht : (n : ℝ) / 2 < t) :
    epsteinClsSum A J t < ⊤ := by
  set s := t - n / 2
  have hs : 0 < s := by simp only [s]; linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := additiveZeta_eq_epsteinClsSum hA J (s := s) (by linarith)
  have hst : ((n : ℝ) + 2 * s) / 2 = t := by simp only [s]; ring
  rw [hst] at h
  have hlt := additiveZeta_lt_top hA J hs
  rw [h] at hlt
  have hK := epsteinConst_pos (F := F) hn hs.le
  exact (ENNReal.mul_lt_top_iff.1 hlt).elim (fun h' => h'.2)
    (fun h' => h'.elim (fun h0 => absurd h0 (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hK))
      (fun h0 => by rw [h0]; exact ENNReal.zero_lt_top))

theorem epsteinLat_cls_lt_top {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) {t : ℝ} (ht : (n : ℝ) / 2 < t)
    (c : ClassGroup (𝓞 F)) : epsteinLat A (twist (classRep F c) J) t < ⊤ := by
  have h := epsteinClsSum_lt_top hA J hn ht
  have h1 : ENNReal.ofReal (idealNorm F (classRep F c) ^ (-(2 * t))) * epsteinLat A (twist (classRep F c) J) t ≤
      epsteinClsSum A J t := ENNReal.le_tsum (f := fun c : ClassGroup (𝓞 F) =>
        ENNReal.ofReal (idealNorm F (classRep F c) ^ (-(2 * t))) * epsteinLat A (twist (classRep F c) J) t) c
  have h2 := lt_of_le_of_lt h1 h
  have hpos : 0 < idealNorm F (classRep F c) ^ (-(2 * t)) := Real.rpow_pos_of_pos (idealNorm_pos F _) _
  rcases (ENNReal.mul_lt_top_iff.1 h2) with h3 | h3 | h3
  · exact h3.2
  · exact absurd h3 (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hpos)
  · rw [h3]; exact ENNReal.zero_lt_top

/-- **The residue of the class-weighted Epstein sum** at $t = n/2$: $\lim_{t\to n/2^+}(t - \frac n2)\sum_cN(\mathfrak c_c)^{-2t}E_{\mathfrak c_c^{-1}L}(t)
= \frac{\rho_F}2c_L/K$, $K$ = `epsteinConst F n 0` (from `tendsto_mul_additiveZeta`). -/
@[kb "weil1982" "§4.4, pp. 97–98; §4.5, p. 109"]
theorem tendsto_sub_mul_epsteinClsSum {A : Matrix (Fin n) (Fin n) F} (hA : IsTotPosGram A)
    (J : Fin n → (FractionalIdeal (𝓞 F)⁰ F)ˣ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun t : ℝ => (t - n / 2) * (epsteinClsSum A J t).toReal)
      (nhdsWithin ((n : ℝ) / 2) (Set.Ioi ((n : ℝ) / 2)))
      (nhds (dedekindZeta_residue F / 2 * latConst A J / epsteinConst F n 0)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := tendsto_mul_additiveZeta hA J hn
  have hK0 := epsteinConst_pos (F := F) hn le_rfl
  have h2 : Filter.Tendsto (epsteinConst F n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (epsteinConst F n 0)) :=
    (continuousAt_epsteinConst hn).tendsto.mono_left nhdsWithin_le_nhds
  have h3 := h1.div h2 hK0.ne'
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
  have h := additiveZeta_eq_epsteinClsSum hA J (s := s) (by linarith)
  have hst : ((n : ℝ) + 2 * s) / 2 = t := by simp only [s]; ring
  rw [hst] at h
  have hK := epsteinConst_pos (F := F) hn hs.le
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK.le]
  field_simp


end Classes

end Gen

end QuadFormsKB.QuatOrder
