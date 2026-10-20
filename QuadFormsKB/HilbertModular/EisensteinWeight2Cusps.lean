/-
# Hilbert Eisenstein series X: weight-2 constant terms at every cusp, $d \ge 2$

For an integral weight $W$ of weight 2 and level $\mathfrak M$ (`IntWeight W 2 𝔐`) and $A \in \mathrm{SL}_2(F)$, the slashed weight
$W_A(x) = W(xA^{-1})$ is supported on $\mathcal{O}_F^2A$, not on $\mathcal{O}_F^2$, so the weight-2 theory does not apply to it directly.
**Rescaling** fixes this: for $0 \ne D \in \mathcal{O}_F$ with $DA \in M_2(\mathcal{O}_F)$ (`exists_denom_SL2`),
$$W'(x) = W_A(D^{-1}x)\qquad(\texttt{scaleWeight})$$
is an integral weight of level $D^2\mathfrak M$ (`intWeight_scale_slashWeight`), and $x \mapsto Dx$ on $U\backslash F^2$ gives
$H_{W',2}(z, s) = N(D)^{-2}\prod_v|\sigma_v(D)|^{-2s}H_{W_A,2}(z, s)$ (`heckeSeries_scaleWeight`), $\mathrm c(W') = N(D)^{-2}\mathrm c(W_A)$
(`eisConst_scaleWeight`). With the exact transformation law of the Hecke series (`heckeSeries_smul`) and $s \to 0^+$:
$$E_{W,2}\,|_2\,A = N(D)^2\,E_{W',2}\qquad(\texttt{eis2\_slash\_eq\_scale}),$$
and hence (`tendsto_eis2_atImInfty` for $W'$)
$$\lim(E_{W,2}\,|_2\,A)(z) = N(D)^2\mathrm c(W') = \mathrm c(W_A)\qquad(\textbf{\texttt{tendsto\_eis2\_slash}}),$$
the same formula as for $k \ge 3$ (`tendsto_eisSeries_slash`, `eisConst_slashWeight`).

Sources: Hecke (1927) [unverified]; Shimura (Duke 1978), Prop. 3.4 [unverified]; Freitag (1990), Ch. I §5 [unverified].
-/
import QuadFormsKB.HilbertModular.EisensteinWeight2Forms
import QuadFormsKB.HilbertModular.CuspValues

open Complex Matrix NumberField UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm nonZeroDivisors

set_option linter.unusedSectionVars false

namespace QuadFormsKB.HilbertModular

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/-! ### Scaling on $U\backslash F^2$ -/

/-- $x \mapsto tx$ on $F^2$, $t \in F^\times$. -/
def scaleEquiv (t : Fˣ) : F × F ≃ F × F where
  toFun x := ((t : F) * x.1, (t : F) * x.2)
  invFun x := (((t⁻¹ : Fˣ) : F) * x.1, ((t⁻¹ : Fˣ) : F) * x.2)
  left_inv x := by simp
  right_inv x := by simp

lemma scaleEquiv_smul (t : Fˣ) (ε : (𝓞 F)ˣ) (x : F × F) : scaleEquiv t (ε • x) = ε • scaleEquiv t x := by
  ext <;> simp [scaleEquiv, Units.smul_def, Algebra.smul_def, mul_left_comm]

/-- **Scaling on orbits**: $Ux \mapsto U(tx)$. -/
noncomputable def orbitScaleEquiv (t : Fˣ) : UOrbit F ≃ UOrbit F :=
  Quotient.congr (scaleEquiv t) fun a b => by
    simp only [orbitRel_iff]
    constructor
    · rintro ⟨ε, rfl⟩; exact ⟨ε, (scaleEquiv_smul t ε b).symm⟩
    · rintro ⟨ε, hε⟩
      refine ⟨ε, ?_⟩
      have := congrArg (scaleEquiv t).symm hε
      rwa [← scaleEquiv_smul, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this

lemma orbitScaleEquiv_mk (t : Fˣ) (x : F × F) :
    orbitScaleEquiv t (Quotient.mk _ x) = Quotient.mk _ (scaleEquiv t x) := rfl

/-- **Reindexing by scaling**: for $g$ constant on $U$-orbits, $\sum_{U\backslash F^2}g(x) = \sum_{U\backslash F^2}g(tx)$. -/
lemma tsum_orbit_scale {g : F × F → ℂ} (hg : ∀ (ε : (𝓞 F)ˣ) x, g (ε • x) = g x) (t : Fˣ) :
    ∑' o : UOrbit F, g o.out = ∑' o : UOrbit F, g (scaleEquiv t o.out) := by
  rw [← (orbitScaleEquiv t).tsum_eq]
  refine tsum_congr fun o => ?_
  conv_lhs => rw [← Quotient.out_eq o, orbitScaleEquiv_mk]
  obtain ⟨ε, hε⟩ := exists_smul_out (scaleEquiv t o.out)
  rw [← hε, hg]

/-! ### The rescaled weight -/

/-- **The rescaled weight** $V_t(x) = V(t^{-1}x)$. -/
def scaleWeight (V : F × F → ℂ) (t : Fˣ) : F × F → ℂ := fun x => V ((scaleEquiv t).symm x)

lemma IsUnitEquivariant.scaleWeight {V : F × F → ℂ} {k : ℤ} (hV : IsUnitEquivariant V k) (t : Fˣ) :
    IsUnitEquivariant (scaleWeight V t) k := by
  intro ε x
  simp only [HilbertModular.scaleWeight]
  have : (scaleEquiv t).symm (ε • x) = ε • (scaleEquiv t).symm x := by
    apply (scaleEquiv t).injective
    rw [Equiv.apply_symm_apply, scaleEquiv_smul, Equiv.apply_symm_apply]
  rw [this, hV]

lemma prod_ofReal_realEmb (t : F) : (∏ v, (realEmb F v t : ℂ)) = ((∏ v, realEmb F v t : ℝ) : ℂ) := by
  rw [Complex.ofReal_prod]

/-- **The Hecke series of a rescaled weight**: $H_{V_t,k}(z, s) = N(t)^{-k}\prod_v|\sigma_v(t)|^{-2s}H_{V,k}(z, s)$. -/
theorem heckeSeries_scaleWeight {V : F × F → ℂ} {k : ℕ} (hV : IsUnitEquivariant V (k : ℤ)) (t : Fˣ)
    (s : ℝ) (z : InfinitePlace F → ℍ) :
    heckeSeries (scaleWeight V t) k s z =
      ((∏ v, (realEmb F v t : ℂ)) ^ k)⁻¹ * (∏ v, ((|realEmb F v t| ^ (-2 * s) : ℝ) : ℂ)) *
        heckeSeries V k s z := by
  rw [heckeSeries, heckeSeries, ← tsum_mul_left]
  refine (tsum_orbit_scale (g := fun x => heckeTerm (scaleWeight V t) k s x fun v => (z v : ℂ))
    (fun ε x => heckeTerm_smul (hV.scaleWeight t) s ε x _) t).trans ?_
  refine tsum_congr fun o => ?_
  simp only [heckeTerm, HilbertModular.scaleWeight, Equiv.symm_apply_apply]
  have ht : ∀ v, realEmb F v t ≠ 0 := fun v =>
    (map_ne_zero_iff _ (realEmb_injective F v)).mpr t.ne_zero
  have hplace : ∀ v, phiKS k s ((realEmb F v (scaleEquiv t o.out).1 : ℂ) * (z v : ℂ) +
      (realEmb F v (scaleEquiv t o.out).2 : ℂ)) =
      ((realEmb F v t : ℂ) ^ k)⁻¹ * ((|realEmb F v t| ^ (-2 * s) : ℝ) : ℂ) *
        phiKS k s ((realEmb F v o.out.1 : ℂ) * (z v : ℂ) + (realEmb F v o.out.2 : ℂ)) := by
    intro v
    rw [← phiKS_real_mul k s (ht v)]
    congr 1
    simp only [scaleEquiv, Equiv.coe_fn_mk, map_mul, ofReal_mul]
    ring
  simp_rw [hplace]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow]
  ring

open Classical in
/-- The summand of the constant term is constant on $U$-orbits. -/
lemma eisConstTerm_smul {V : F × F → ℂ} {k : ℤ} (hV : IsUnitEquivariant V k) (ε : (𝓞 F)ˣ) (x : F × F) :
    (if (ε • x).1 = 0 then V (ε • x) * (∏ v, (realEmb F v (ε • x).2 : ℂ)) ^ (-k) else 0) =
      (if x.1 = 0 then V x * (∏ v, (realEmb F v x.2 : ℂ)) ^ (-k) else 0) := by
  have hε : ((ε : 𝓞 F) : F) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr ε.ne_zero
  have h1 : (ε • x).1 = 0 ↔ x.1 = 0 := by rw [smul_fst, mul_eq_zero]; simp [hε]
  by_cases hx : x.1 = 0
  · simp only [show (ε • x).1 = 0 from h1.mpr hx, hx, ↓reduceIte]
    rw [hV, smul_snd]
    have hN : (∏ v, (realEmb F v ((ε : 𝓞 F) : F) : ℂ)) = ((unitNorm ε : ℝ) : ℂ) := by
      rw [unitNorm, Complex.ofReal_prod]
    have hN0 : ((unitNorm ε : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact unitNorm_ne_zero ε
    simp only [map_mul, ofReal_mul, Finset.prod_mul_distrib, hN, mul_zpow]
    rw [show ((unitNorm ε : ℝ) : ℂ) ^ k * V x * (((unitNorm ε : ℝ) : ℂ) ^ (-k) *
        (∏ v, (realEmb F v x.2 : ℂ)) ^ (-k)) = (((unitNorm ε : ℝ) : ℂ) ^ k *
        ((unitNorm ε : ℝ) : ℂ) ^ (-k)) * (V x * (∏ v, (realEmb F v x.2 : ℂ)) ^ (-k)) by ring,
      ← zpow_add₀ hN0, add_neg_cancel, zpow_zero, one_mul]
  · simp only [show ¬ (ε • x).1 = 0 from fun h => hx (h1.mp h), hx, ↓reduceIte]

open Classical in
/-- **The constant term of a rescaled weight**: $\mathrm c(V_t) = N(t)^{-k}\mathrm c(V)$. -/
theorem eisConst_scaleWeight {V : F × F → ℂ} {k : ℤ} (hV : IsUnitEquivariant V k) (t : Fˣ) :
    eisConst (scaleWeight V t) k = (∏ v, (realEmb F v t : ℂ)) ^ (-k) * eisConst V k := by
  rw [eisConst, eisConst, ← tsum_mul_left]
  refine (tsum_orbit_scale (g := fun x => if x.1 = 0 then scaleWeight V t x *
      (∏ v, (realEmb F v x.2 : ℂ)) ^ (-k) else 0) (fun ε x => eisConstTerm_smul (hV.scaleWeight t) ε x)
      t).trans ?_
  refine tsum_congr fun o => ?_
  have ht : (t : F) ≠ 0 := t.ne_zero
  have h1 : (scaleEquiv t o.out).1 = 0 ↔ o.out.1 = 0 := by
    simp [scaleEquiv, ht]
  by_cases h : o.out.1 = 0
  · simp only [show (scaleEquiv t o.out).1 = 0 from h1.mpr h, h, ↓reduceIte, HilbertModular.scaleWeight,
      Equiv.symm_apply_apply]
    simp only [scaleEquiv, Equiv.coe_fn_mk, map_mul, ofReal_mul, Finset.prod_mul_distrib, mul_zpow]
    ring
  · simp only [show ¬ (scaleEquiv t o.out).1 = 0 from fun h' => h (h1.mp h'), h, ↓reduceIte, mul_zero]

/-! ### Rescaling a slashed integral weight -/

/-- A common denominator of $A \in \mathrm{SL}_2(F)$: $0 \ne D \in \mathcal{O}_F$ with $DA_{ij} \in \mathcal{O}_F$ for all $i, j$. -/
lemma exists_denom_SL2 (A : SL(2, F)) : ∃ D : 𝓞 F, D ≠ 0 ∧
    ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * A i j := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (𝓞 F)⁰
    (Finset.univ.image fun p : Fin 2 × Fin 2 => A p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i j => ?_⟩
  obtain ⟨a, ha⟩ := hb (A i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
  exact ⟨a, by rw [ha, Algebra.smul_def]⟩

lemma algebraMap_unit_ne (D : 𝓞 F) (hD : D ≠ 0) : algebraMap (𝓞 F) F D ≠ 0 :=
  (map_ne_zero_iff _ algebraMap_O_injective).mpr hD

/-- **The rescaled slashed weight is integral**: for an integral weight $W$ of level $\mathfrak M$, $A \in \mathrm{SL}_2(F)$ and
$0 \ne D \in \mathcal{O}_F$ with $DA$ integral, $x \mapsto W_A(D^{-1}x)$ is an integral weight of level $D^2\mathfrak M$. -/
theorem intWeight_scale_slashWeight {W : F × F → ℂ} {k : ℤ} {𝔐 : Ideal (𝓞 F)} (hW : IntWeight W k 𝔐)
    (A : SL(2, F)) {D : 𝓞 F} (hD : D ≠ 0)
    (hDA : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * A i j) :
    IntWeight (scaleWeight (slashWeight W A) (Units.mk0 _ (algebraMap_unit_ne D hD)))
      k (Ideal.span {D ^ 2} * 𝔐) := by
  set t : Fˣ := Units.mk0 _ (algebraMap_unit_ne D hD)
  have htF : (t : F) = algebraMap (𝓞 F) F D := rfl
  have htinv : ((t⁻¹ : Fˣ) : F) = (algebraMap (𝓞 F) F D)⁻¹ := rfl
  have hDF := algebraMap_unit_ne D hD
  choose a ha using hDA
  obtain ⟨i0, i1, i2, i3⟩ := sl2_inv_apply A
  refine ⟨(hW.unit.slashWeight A).scaleWeight t, fun x hx => ?_, fun x m₁ m₂ hm₁ hm₂ => ?_, ?_, ?_⟩
  · -- support in `𝓞_F²`
    obtain ⟨p, hp⟩ := hW.supp _ hx
    -- `D⁻¹ x A⁻¹ = p`, so `x = D · (p A)`
    have hx' : (scaleEquiv t).symm x = rowMul (algebraMap (𝓞 F) F p.1, algebraMap (𝓞 F) F p.2) A := by
      rw [hp, rowMul_inv_rowMul]
    refine ⟨(p.1 * a 0 0 + p.2 * a 1 0, p.1 * a 0 1 + p.2 * a 1 1), ?_⟩
    have hx'' : x = scaleEquiv t ((scaleEquiv t).symm x) := (Equiv.apply_symm_apply _ _).symm
    rw [hx'', hx']
    ext <;> simp only [scaleEquiv, Equiv.coe_fn_mk, rowMul_fst, rowMul_snd, map_add, map_mul, ha, htF] <;> ring
  · -- periodicity modulo `D²𝔐`
    obtain ⟨μ₁, hμ₁, rfl⟩ := Ideal.mem_span_singleton_mul.mp hm₁
    obtain ⟨μ₂, hμ₂, rfl⟩ := Ideal.mem_span_singleton_mul.mp hm₂
    simp only [HilbertModular.scaleWeight, slashWeight]
    set y := rowMul ((scaleEquiv t).symm x) A⁻¹
    -- the shift `D⁻¹ (D²μ) A⁻¹ = μ (D A⁻¹)` is integral in `𝔐`
    have hshift : rowMul ((scaleEquiv t).symm (x.1 + algebraMap (𝓞 F) F (D ^ 2 * μ₁),
        x.2 + algebraMap (𝓞 F) F (D ^ 2 * μ₂))) A⁻¹ =
        (y.1 + algebraMap (𝓞 F) F (μ₁ * a 1 1 - μ₂ * a 1 0),
          y.2 + algebraMap (𝓞 F) F (-(μ₁ * a 0 1) + μ₂ * a 0 0)) := by
      ext
      · simp only [y, scaleEquiv, Equiv.coe_fn_symm_mk, rowMul_fst, i0, i2,
          map_mul, map_sub, map_pow, ha, htinv]
        field_simp
        ring
      · simp only [y, scaleEquiv, Equiv.coe_fn_symm_mk, rowMul_snd, i1, i3, map_add,
          map_mul, map_neg, map_pow, ha, htinv]
        field_simp
        ring
    rw [hshift]
    exact hW.per y _ _ (Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hμ₁) (Ideal.mul_mem_right _ _ hμ₂))
      (Ideal.add_mem _ (Submodule.neg_mem _ (Ideal.mul_mem_right _ _ hμ₁)) (Ideal.mul_mem_right _ _ hμ₂))
  · obtain ⟨B, hB⟩ := hW.bdd
    exact ⟨B, fun x => hB _⟩
  · exact mul_ne_zero (by simpa using pow_ne_zero 2 hD) hW.ne

/-! ### Weight 2 at every cusp -/

section Weight2

variable {W : F × F → ℂ} {𝔐 : Ideal (𝓞 F)}

lemma prod_rpow_mul_neg {D : F} (hD : D ≠ 0) (s : ℝ) :
    (∏ v, ((|realEmb F v D| ^ (2 * s) : ℝ) : ℂ)) * ∏ v, ((|realEmb F v D| ^ (-2 * s) : ℝ) : ℂ) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hpos : 0 < |realEmb F v D| := abs_pos.mpr ((map_ne_zero_iff _ (realEmb_injective F v)).mpr hD)
  rw [← ofReal_mul, ← Real.rpow_add hpos, show 2 * s + -2 * s = 0 by ring, Real.rpow_zero, ofReal_one]

/-- **The weight-2 Eisenstein series slashed by any $A \in \mathrm{SL}_2(F)$** ($d \ge 2$): with $D$ a common denominator of $A$,
$E_{W,2}\,|_2\,A = N(D)^2E_{W',2}$ for the integral weight $W'(x) = W_A(D^{-1}x)$ of level $D^2\mathfrak M$. -/
theorem eis2_slash_eq_scale (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hW : IntWeight W 2 𝔐)
    (A : SL(2, F)) {D : 𝓞 F} (hD : D ≠ 0)
    (hDA : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * A i j) :
    eis2 W 𝔐 hW.ne ∣[(2 : ℤ)] slHom (realEmb F) A =
      ((∏ v, (realEmb F v (algebraMap (𝓞 F) F D) : ℂ)) ^ 2) •
        eis2 (scaleWeight (slashWeight W A) (Units.mk0 _ (algebraMap_unit_ne D hD)))
          (Ideal.span {D ^ 2} * 𝔐) (intWeight_scale_slashWeight hW A hD hDA).ne := by
  set t : Fˣ := Units.mk0 _ (algebraMap_unit_ne D hD)
  have hW' := intWeight_scale_slashWeight hW A hD hDA
  set N : ℂ := ∏ v, (realEmb F v (algebraMap (𝓞 F) F D) : ℂ)
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => by
    rw [Ne, Complex.ofReal_eq_zero]
    exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr (algebraMap_unit_ne D hD)
  funext z
  rw [slash_apply, Pi.smul_apply, smul_eq_mul]
  set j : InfinitePlace F → ℂ := fun v => denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v)
  have hj : ∀ v, j v ≠ 0 := fun v => denom_ne_zero _ _
  have hfac : ∏ v, ((((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ).det.val ^ ((2 : ℤ) - 1) : ℝ) : ℂ) *
      denom ((slHom (realEmb F) A v : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) (z v) ^ (-(2 : ℤ)) =
      ∏ v, (j v ^ 2)⁻¹ := by
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [slHom_det, _root_.one_zpow, ofReal_one, one_mul, _root_.zpow_neg, zpow_ofNat]
  rw [hfac]
  have hunitA : IsUnitEquivariant (slashWeight W A) ((2 : ℕ) : ℤ) := hW.unit.slashWeight A
  have hrel : ∀ s : ℝ, heckeSeries (slashWeight W A) 2 s z =
      (N ^ 2 * ∏ v, ((|realEmb F v (algebraMap (𝓞 F) F D)| ^ (2 * s) : ℝ) : ℂ)) *
        heckeSeries (scaleWeight (slashWeight W A) t) 2 s z := by
    intro s
    rw [heckeSeries_scaleWeight hunitA t s z]
    have hc := prod_rpow_mul_neg (algebraMap_unit_ne D hD) s
    rw [neg_mul] at hc
    simp only [t, Units.val_mk0]
    field_simp
    rw [mul_assoc, hc, mul_one]
    show _ = _ * N ^ 2 / N ^ 2
    rw [mul_div_assoc, div_self (pow_ne_zero 2 hN), mul_one]
  have h1 := (tendsto_heckeSeries_two hd hW (slHom (realEmb F) A • z)).mul_const (∏ v, (j v ^ 2)⁻¹)
  have h2 : Tendsto (fun s : ℝ => (∏ v, (((‖j v‖ ^ (2 * s) : ℝ)) : ℂ)) *
      ((N ^ 2 * ∏ v, ((|realEmb F v (algebraMap (𝓞 F) F D)| ^ (2 * s) : ℝ) : ℂ)) *
        heckeSeries (scaleWeight (slashWeight W A) t) 2 s z)) (𝓝[>] 0)
      (𝓝 ((∏ v, (((‖j v‖ ^ (2 * (0 : ℝ)) : ℝ)) : ℂ)) *
        ((N ^ 2 * ∏ v, ((|realEmb F v (algebraMap (𝓞 F) F D)| ^ (2 * (0 : ℝ)) : ℝ) : ℂ)) *
          eis2 (scaleWeight (slashWeight W A) t) (Ideal.span {D ^ 2} * 𝔐) hW'.ne z))) := by
    have hc1 : Continuous fun s : ℝ => ∏ v, (((‖j v‖ ^ (2 * s) : ℝ)) : ℂ) :=
      continuous_finsetProd _ fun v _ => continuous_ofReal.comp
        (continuous_const.rpow (by fun_prop) fun _ => Or.inl (norm_ne_zero_iff.mpr (hj v)))
    have hc2 : Continuous fun s : ℝ => ∏ v, ((|realEmb F v (algebraMap (𝓞 F) F D)| ^ (2 * s) : ℝ) : ℂ) :=
      continuous_finsetProd _ fun v _ => continuous_ofReal.comp
        (continuous_const.rpow (by fun_prop) fun _ => Or.inl (abs_ne_zero.mpr
          ((map_ne_zero_iff _ (realEmb_injective F v)).mpr (algebraMap_unit_ne D hD))))
    refine Tendsto.mul ((hc1.tendsto 0).mono_left nhdsWithin_le_nhds) (Tendsto.mul
      (((hc2.tendsto 0).mono_left nhdsWithin_le_nhds).const_mul _)
      (tendsto_heckeSeries_two hd hW' z))
  simp only [mul_zero, Real.rpow_zero, ofReal_one, Finset.prod_const_one, one_mul, mul_one] at h2
  have heq : ∀ s : ℝ, heckeSeries W 2 s (slHom (realEmb F) A • z) * ∏ v, (j v ^ 2)⁻¹ =
      (∏ v, (((‖j v‖ ^ (2 * s) : ℝ)) : ℂ)) *
        ((N ^ 2 * ∏ v, ((|realEmb F v (algebraMap (𝓞 F) F D)| ^ (2 * s) : ℝ) : ℂ)) *
          heckeSeries (scaleWeight (slashWeight W A) t) 2 s z) := by
    intro s
    rw [← hrel]
    exact heckeSeries_smul hW.unit s A z
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Weight-2 constant terms at every cusp** ($d \ge 2$): for an integral weight $W$ of weight 2 and every
$A \in \mathrm{SL}_2(F)$, $(E_{W,2}\,|_2\,A)(z) \to \mathrm c_\infty(W_A) = \sum_{t\in U\backslash F^\times}W(-tA_{10}, tA_{00})N(t)^{-2}$
(`eisConst_slashWeight`) as $\min_v\operatorname{Im}z_v \to \infty$: the same formula as in weight $k \ge 3$. -/
@[kb "shimura1978" "Prop. 3.4, constant terms of the weight-2 Eisenstein series at every cusp [unverified]"]
theorem tendsto_eis2_slash (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hW : IntWeight W 2 𝔐)
    (A : SL(2, F)) :
    Tendsto (eis2 W 𝔐 hW.ne ∣[(2 : ℤ)] slHom (realEmb F) A) atImInftyPi
      (𝓝 (eisConst (slashWeight W A) 2)) := by
  obtain ⟨D, hD, hDA⟩ := exists_denom_SL2 A
  rw [eis2_slash_eq_scale hd hW A hD hDA]
  have h := (tendsto_eis2_atImInfty (intWeight_scale_slashWeight hW A hD hDA)).const_smul
    ((∏ v, (realEmb F v (algebraMap (𝓞 F) F D) : ℂ)) ^ 2)
  convert h using 2
  rw [eisConst_scaleWeight (hW.unit.slashWeight A), smul_eq_mul, ← mul_assoc]
  have hN : (∏ v, (realEmb F v ((Units.mk0 _ (algebraMap_unit_ne D hD) : Fˣ) : F) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => by
      rw [Ne, Complex.ofReal_eq_zero]
      exact (map_ne_zero_iff _ (realEmb_injective F v)).mpr (algebraMap_unit_ne D hD)
  rw [show ((∏ v, (realEmb F v (algebraMap (𝓞 F) F D) : ℂ)) ^ 2) =
    (∏ v, (realEmb F v ((Units.mk0 _ (algebraMap_unit_ne D hD) : Fˣ) : F) : ℂ)) ^ (2 : ℤ) by
      rw [zpow_ofNat]; rfl, ← zpow_add₀ hN, add_neg_cancel, zpow_zero, one_mul]

/-- **The weight-2 Eisenstein series has a constant term at every cusp** ($d \ge 2$). -/
theorem hasCuspLimits_eis2 (hd : 2 ≤ Fintype.card (InfinitePlace F)) (hW : IntWeight W 2 𝔐) :
    HasCuspLimits (eis2 W 𝔐 hW.ne) 2 :=
  fun A => ⟨_, tendsto_eis2_slash hd hW A⟩

end Weight2

end QuadFormsKB.HilbertModular
