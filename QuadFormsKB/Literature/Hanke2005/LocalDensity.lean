/-
# Hanke 2005, §2–§3: the local densities $\beta_\mathfrak p(\Lambda,\psi)$ in Gram coordinates

J. Hanke, *An exact mass formula for quadratic forms over number fields*, J. Reine Angew. Math. 584 (2005);
locators refer to the 1999 thesis of the same title.

**Setting.** $F$ a number field, $v$ a finite place, $F_v$ = `v.adicCompletion F`, $\mathfrak o_v$ its valuation ring,
$q = \#(\mathfrak o_v/\mathfrak p_v)$. Hanke represents a quadratic space $(V_v,\varphi_v)$ in a basis by the symmetric
matrix $\varphi$ of its bilinear form, $\varphi_{ij} = \varphi(v_i, v_j)$ with $\varphi(x,x) = \varphi[x]$ (the Gram matrix;
for a form with Hessian $H$, $\varphi = \tfrac12H$), and lets $X_v = M_n(F_v)$ act on columns. The map
$F(x) = {}^tx\varphi x$ (2.5) has fibre $O(\varphi)$ over $\varphi$.

**Definition (2.8)/(3.1).** For a lattice $\Lambda_\mathfrak p\subseteq F_v^n$ and an open neighbourhood $U$ of $\varphi$ in the
symmetric matrices $T_v$, $U' = F^{-1}(U)\cap\{x : x\Lambda_\mathfrak p = \Lambda_\mathfrak p\}$, and
$$\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi) = \frac12\lim_{U\to\varphi}\frac{\int_{U'}dX}{\int_UdT},\qquad
dX = \prod_{i,j}dx_{ij},\quad dT = \prod_{i\le j}dt_{ij},$$
the measures normalized by $\mathrm{vol}(\mathfrak o_v) = 1$ ($(d'x)_v$ of §2). Following §3 (p. 7: "we have a natural
choice of neighborhoods $U_i = \varphi + P_i$ where $P_i = (\mathfrak p^i)^n_n\cap T_\mathfrak p$"), the limit is taken along
$U_i$; then $\int_{U_i}dT = q^{-i\,n(n+1)/2}$ and
$$\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi) = \frac12\lim_{i\to\infty}q^{i\,n(n+1)/2}\,
\mathrm{vol}\{x\in M_n(F_v) : x\Lambda_\mathfrak p = \Lambda_\mathfrak p,\ {}^tx\varphi x - \varphi\in(\mathfrak p^i)^n_n\}$$
(`hankeBeta`). *Normalization:* these are **Gram** coordinates $t_{ij}$; the repository's densities
(`NF.localDensityForm`, `DVR.localDensityForm`, `siegelDensity`) use the coefficients $c_{ii} = t_{ii}$, $c_{ij} = 2t_{ij}$
of the quadratic form. The two differ by $|2|_v^{n(n-1)/2}$ (`hankeBeta_std_hessian`).

**Defines** `StabLat` ($x\Lambda = \Lambda$), `gramFiber` ($U'_i$), `gramRatio`, `hankeBeta`, Shimura's count and density
`shimuraCount`, `shimuraE` ([Shi, §8] as quoted in Lemma 3.2).

**Proves** Lemma 3.1 (`hankeBeta_smul`), Lemma 3.2 (`hankeBeta_std_eq_half_shimuraE`), (3.2) (`hankeBeta_std_eq_two`),
invariance under $\mathrm{GL}_n(\mathfrak o_v)$ (`hankeBeta_std_congr_unit`), the comparison with the repository's density
(`hankeBeta_std_hessian`, `hankeBeta_gramV`), and the existence of the limit (`gramRatio_std_eventually_eq`).
-/
import QuadFormsKB.Tamagawa.Measure.LerayPadic
import QuadFormsKB.Tamagawa.OrbitHensel


open IsDedekindDomain NumberField MeasureTheory Filter Topology WithZero Matrix
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Hanke2005

open QuadFormsKB.LocalDensity QuadFormsKB.Lattices QuadFormsKB.Tamagawa.Measure.LerayPadic

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- **$x\Lambda_\mathfrak p = \Lambda_\mathfrak p$** for a matrix $x\in M_n(F_v)$ acting on columns and an
$\mathfrak o_v$-submodule $\Lambda_\mathfrak p\subseteq F_v^n$ (the condition defining $U'$ in (2.8)). -/
def StabLat (Λ : Submodule 𝔬 (Fin n → Fv)) (x : Matrix (Fin n) (Fin n) Fv) : Prop :=
  Λ.map ((Matrix.mulVecLin x).restrictScalars 𝔬) = Λ

/-- **Hanke's $U'_i$** (thesis (2.8), (3.1), p. 7): the $x\in M_n(F_v)$ with $x\Lambda_\mathfrak p = \Lambda_\mathfrak p$ and
${}^tx\varphi x\in\varphi + P_i$, i.e. every entry of ${}^tx\varphi x - \varphi$ lies in $\mathfrak p_v^i$. -/
@[kb "hanke2005crelle" "(2.8), p. 5; (3.1) and the neighbourhoods U_i, p. 7"]
def gramFiber (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv) (i : ℕ) :
    Set (Matrix (Fin n) (Fin n) Fv) :=
  {x | StabLat v Λ x ∧ ∀ a b, Valued.v ((xᵀ * φ * x - φ) a b) ≤ exp (-(i : ℤ))}

/-- The ratio $\int_{U'_i}dX/\int_{U_i}dT = q^{i\,n(n+1)/2}\,\mathrm{vol}(U'_i)$ ($dX$ = `volM`, $\mathrm{vol}(M_n(\mathfrak o_v)) = 1$). -/
def gramRatio (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv) (i : ℕ) : ℝ :=
  (DVR.q 𝔬 : ℝ) ^ (i * (n * (n + 1) / 2)) * (volM v (gramFiber v Λ φ i)).toReal

/-- **Hanke's local density** $\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi)$ (thesis (2.8), p. 5, with the natural
neighbourhoods of (3.1), p. 7): $\tfrac12\lim_i q^{i\,n(n+1)/2}\mathrm{vol}(U'_i)$, in Gram coordinates (see the module
docstring). Lean's `limUnder`; the limit exists (and is attained) for $\Lambda_\mathfrak p = \mathfrak o_v^n$ and
nondegenerate symmetric $\varphi$ (`gramRatio_std_eventually_eq`). -/
@[kb "hanke2005crelle" "(2.8), p. 5; (3.1), p. 7"]
def hankeBeta (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv) : ℝ :=
  (1 / 2 : ℝ) * limUnder atTop (gramRatio v Λ φ)

/-- **The Gram matrix** $\varphi = \tfrac12H$ of a form $Q$ over $\mathfrak o_v$, as a matrix over $F_v$ (Hanke's matrix of
$(\Lambda_\mathfrak p,\varphi_\mathfrak p)$ in the basis $e_0,\dots,e_{n-1}$ of $\mathfrak o_v^n$). -/
def gramOf (Q : QuadForm 𝔬 n) : Matrix (Fin n) (Fin n) Fv :=
  (1 / 2 : Fv) • Q.hessian.map (algebraMap 𝔬 Fv)

/-! ### Helpers (Haar invariance, StabLat, scaling, the core computation) -/

section HaarInv

open QuadFormsKB.Analysis

/-- The coordinate equivalence `Y ↦ (of Y)ᵀ`. -/
def f1_eY : (Fin n → Fin n → Fv) ≃ₜ+ Matrix (Fin n) (Fin n) Fv where
  toFun Y := (Matrix.of Y)ᵀ
  invFun X := fun i j => X j i
  left_inv Y := by ext i j; rfl
  right_inv X := by ext i j; rfl
  map_add' Y Y' := by ext i j; rfl
  continuous_toFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply i).comp (continuous_apply j)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_id.matrix_elem j i

instance f1_haar : (volM v : Measure (Matrix (Fin n) (Fin n) Fv)).IsAddHaarMeasure := by
  have h1 : (Measure.pi fun _ : Fin n => haarV v).IsAddHaarMeasure := inferInstance
  have h2 : MeasurableAdd (Fin n → Fv) := inferInstance
  have h3 : ∀ _ : Fin n, (Measure.pi fun _ : Fin n => haarV v).IsAddHaarMeasure := fun _ => h1
  have : (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => haarV v).IsAddHaarMeasure := inferInstance
  have h := (f1_eY (v := v) (n := n)).isAddHaarMeasure_map (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => haarV v)
  exact h

theorem f1_pres (e : Matrix (Fin n) (Fin n) Fv ≃ₜ+ Matrix (Fin n) (Fin n) Fv)
    (he : e ⁻¹' (intM v) = intM v) : MeasurePreserving e (volM v) (volM v) := by
  have hm : Measurable e := e.continuous.measurable
  have hH : (Measure.map e (volM v)).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have hc := Measure.isAddLeftInvariant_eq_smul (Measure.map e (volM v)) (volM v)
  set c := Measure.addHaarScalarFactor (Measure.map e (volM v)) (volM v)
  have hopen : IsOpen (intM v : Set (Matrix (Fin n) (Fin n) Fv)) := QuadFormsKB.Tamagawa.Measure.isOpen_intMat v
  have hcomp : IsCompact (intM v : Set (Matrix (Fin n) (Fin n) Fv)) := QuadFormsKB.Tamagawa.Measure.isCompact_intMat v
  have hne : (intM v : Set (Matrix (Fin n) (Fin n) Fv)).Nonempty := ⟨0, fun i j => by simp⟩
  have h0 : volM v (intM v) ≠ 0 := (hopen.measure_pos _ hne).ne'
  have ht : volM v (intM v) ≠ ⊤ := hcomp.measure_lt_top.ne
  refine ⟨hm, ?_⟩
  have h1 := congrArg (fun μ => μ (intM v)) hc
  simp only [Measure.map_apply hm hopen.measurableSet, he, Measure.smul_apply, ] at h1
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have := ENNReal.mul_left_inj h0 ht |>.mp (by rw [one_mul]; exact h1.symm.trans rfl : (c : ℝ≥0∞) * _ = 1 * _)
    exact this
  have hc2 : c = 1 := by exact_mod_cast hc1
  rw [hc, hc2, one_smul]

theorem f1_pres' (f f' : Matrix (Fin n) (Fin n) Fv → Matrix (Fin n) (Fin n) Fv)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) (hadd' : ∀ X Y, f' (X + Y) = f' X + f' Y)
    (hc : Continuous f) (hc' : Continuous f') (hl : ∀ X, f' (f X) = X) (hr : ∀ X, f (f' X) = X)
    (hm : ∀ X ∈ intM v, f X ∈ intM v) (hm' : ∀ X ∈ intM v, f' X ∈ intM v) :
    MeasurePreserving f (volM v) (volM v) := by
  let e : Matrix (Fin n) (Fin n) Fv ≃ₜ+ Matrix (Fin n) (Fin n) Fv :=
    { toFun := f, invFun := f', left_inv := hl, right_inv := hr, map_add' := hadd,
      continuous_toFun := hc, continuous_invFun := hc' }
  have := f1_pres v e (by
    ext X
    refine ⟨fun h => ?_, fun h => hm X h⟩
    have h2 := hm' _ h
    have : f' (e X) = X := hl X
    rwa [← this])
  exact this

theorem f1_mul_mem {A B : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intM v) (hB : B ∈ intM v) : A * B ∈ intM v := by
  intro i j
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hA i k) (hB k j)

theorem f1_inv_data {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1) :
    g⁻¹ ∈ intM v ∧ IsUnit g.det := by
  refine ⟨inv_mem_intM v hg hd, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h
  rw [h, map_zero] at hd
  exact zero_ne_one hd

theorem measurePreserving_mulLeftM {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1) :
    MeasurePreserving (fun X : Matrix (Fin n) (Fin n) Fv => g * X) (volM v) (volM v) := by
  obtain ⟨hgi, hu⟩ := f1_inv_data v hg hd
  refine f1_pres' v _ (fun X => g⁻¹ * X) (fun X Y => Matrix.mul_add _ _ _) (fun X Y => Matrix.mul_add _ _ _)
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id) ?_ ?_
    (fun X hX => f1_mul_mem v hg hX) (fun X hX => f1_mul_mem v hgi hX)
  · intro X; show _ = _; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  · intro X; show _ = _; rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem measurePreserving_mulRightM {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1) :
    MeasurePreserving (fun X : Matrix (Fin n) (Fin n) Fv => X * g) (volM v) (volM v) := by
  obtain ⟨hgi, hu⟩ := f1_inv_data v hg hd
  refine f1_pres' v _ (fun X => X * g⁻¹) (fun X Y => Matrix.add_mul _ _ _) (fun X Y => Matrix.add_mul _ _ _)
    (continuous_id.matrix_mul continuous_const) (continuous_id.matrix_mul continuous_const) ?_ ?_
    (fun X hX => f1_mul_mem v hX hg) (fun X hX => f1_mul_mem v hX hgi)
  · intro X; show _ = _; rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  · intro X; show _ = _; rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem measurePreserving_conjM {g : Matrix (Fin n) (Fin n) Fv} (hg : g ∈ intM v) (hd : Valued.v g.det = 1) :
    MeasurePreserving (fun X : Matrix (Fin n) (Fin n) Fv => g * X * g⁻¹) (volM v) (volM v) :=
  (measurePreserving_mulRightM v (g := g⁻¹) (f1_inv_data v hg hd).1 (by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, hd, inv_one])).comp (measurePreserving_mulLeftM v hg hd)

end HaarInv

theorem f2_mulVec_mem_std {A : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intM v) {y : Fin n → Fv}
    (hy : y ∈ std v) : A *ᵥ y ∈ std v := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  have h1 := hA i j
  have h2 := hy j
  simp only [neg_zero, exp_zero] at h2
  calc Valued.v (A i j) * Valued.v (y j) ≤ 1 * 1 := mul_le_mul' h1 h2
    _ = _ := by simp

theorem stabLat_std_iff (x : Matrix (Fin n) (Fin n) Fv) :
    StabLat v (std v) x ↔ x ∈ intM v ∧ Valued.v x.det = 1 := by
  constructor
  · intro h
    have hsub : ∀ y ∈ std v, x *ᵥ y ∈ std v := by
      intro y hy
      have : x *ᵥ y ∈ (std v).map ((Matrix.mulVecLin x).restrictScalars 𝔬) :=
        Submodule.mem_map_of_mem hy
      rw [h] at this
      exact this
    have hsur : ∀ y ∈ std v, ∃ z ∈ std v, x *ᵥ z = y := by
      intro y hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact ⟨z, hz, hzy⟩
    have hsingle : ∀ j, (Pi.single j (1 : Fv) : Fin n → Fv) ∈ std v := by
      intro j i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    have hx : x ∈ intM v := by
      intro i j
      have := hsub _ (hsingle j) i
      simpa [Matrix.mulVec_single_one] using this
    choose z hz hzx using fun j => hsur _ (hsingle j)
    let Y : Matrix (Fin n) (Fin n) Fv := Matrix.of fun i j => z j i
    have hY : Y ∈ intM v := by
      intro i j
      have := hz j i
      simp only [neg_zero, exp_zero] at this
      exact this
    have hxY : x * Y = 1 := by
      ext i j
      have := congrFun (hzx j) i
      simp only [Matrix.mulVec, dotProduct, Pi.single_apply] at this
      simp only [Matrix.mul_apply, Y, Matrix.of_apply, Matrix.one_apply]
      rw [this]
    have hd : x.det * Y.det = 1 := by rw [← Matrix.det_mul, hxY, Matrix.det_one]
    have h1 : Valued.v x.det ≤ 1 := by
      rw [← det_toOM v x hx]; exact (toOM v x hx).det.2
    have h2 : Valued.v Y.det ≤ 1 := by
      rw [← det_toOM v Y hY]; exact (toOM v Y hY).det.2
    refine ⟨hx, le_antisymm h1 ?_⟩
    have := congrArg Valued.v hd
    rw [map_mul, map_one] at this
    calc (1 : ℤᵐ⁰) = Valued.v x.det * Valued.v Y.det := this.symm
      _ ≤ Valued.v x.det * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  · rintro ⟨hx, hd⟩
    have hxi := inv_mem_intM v hx hd
    have hdet : x.det ≠ 0 := by intro h0; rw [h0, map_zero] at hd; simp at hd
    have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hdet
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact f2_mulVec_mem_std v hx hy
    · intro y hy
      refine ⟨x⁻¹ *ᵥ y, f2_mulVec_mem_std v hxi hy, ?_⟩
      show x *ᵥ (x⁻¹ *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

theorem f2_norm_of_valued {c : Fv} (o : ℤ) (hc : Valued.v c = exp (-o)) :
    ‖c‖ = (DVR.q 𝔬 : ℝ) ^ (-o) := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact exp_ne_zero hc.symm
  rw [QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hc0, hc, WithZero.log_exp, NF.q_completion]

theorem f2_gramFiber_smul (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv) {c : Fv}
    (o : ℤ) (hc : Valued.v c = exp (-o)) {i j : ℕ} (hij : (i : ℤ) + o = j) :
    gramFiber v Λ φ i = gramFiber v Λ (c • φ) j := by
  ext x
  simp only [gramFiber, Set.mem_setOf_eq]
  refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
  have h1 : (xᵀ * (c • φ) * x - c • φ) = c • (xᵀ * φ * x - φ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  rw [h1, Matrix.smul_apply, smul_eq_mul, map_mul, hc]
  have h2 : exp (-(j : ℤ)) = exp (-o) * exp (-(i : ℤ)) := by
    rw [← exp_add]; congr 1; omega
  rw [h2]
  exact (mul_le_mul_iff_right₀ (zero_lt_iff.mpr exp_ne_zero)).symm

theorem f2_gramRatio_smul (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv) {c : Fv}
    (o : ℤ) (hc : Valued.v c = exp (-o)) {i j : ℕ} (hij : (i : ℤ) + o = j) :
    gramRatio v Λ φ i = ‖c‖ ^ (n * (n + 1) / 2) * gramRatio v Λ (c • φ) j := by
  unfold gramRatio
  rw [f2_gramFiber_smul v Λ φ o hc hij, f2_norm_of_valued v o hc]
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast DVR.q_pos (R := 𝔬)
  have hq0 : (DVR.q 𝔬 : ℝ) ≠ 0 := hq.ne'
  have key : ((DVR.q 𝔬 : ℝ) ^ (-o)) ^ (n * (n + 1) / 2) * (DVR.q 𝔬 : ℝ) ^ (j * (n * (n + 1) / 2)) =
      (DVR.q 𝔬 : ℝ) ^ (i * (n * (n + 1) / 2)) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, ← zpow_natCast (DVR.q 𝔬 : ℝ) (j * _),
      ← zpow_natCast (DVR.q 𝔬 : ℝ) (i * _), ← zpow_add₀ hq0]
    congr 1
    have hj : (j : ℤ) = i + o := hij.symm
    push_cast
    rw [hj]; ring
  rw [← mul_assoc, key]

theorem f2_tendsto_pair {s t : ℕ → ℝ} {L C : ℝ} (hC : C ≠ 0) (o : ℤ)
    (h : ∀ i j : ℕ, (i : ℤ) + o = j → s i = C * t j) (hs : Tendsto s atTop (𝓝 L)) :
    Tendsto t atTop (𝓝 (L / C)) := by
  rcases le_or_gt 0 o with ho | ho
  · set m := o.toNat with hm
    have h1 : ∀ i, t (i + m) = s i / C := fun i => by
      rw [h i (i + m) (by omega)]; field_simp
    refine (Filter.tendsto_add_atTop_iff_nat m).mp ?_
    exact Tendsto.congr (fun i => (h1 i).symm) (hs.div_const C)
  · set m := (-o).toNat with hm
    have h1 : ∀ j, t j = s (j + m) / C := fun j => by
      rw [h (j + m) j (by omega)]; field_simp
    have : Tendsto (fun j => s (j + m)) atTop (𝓝 L) := (Filter.tendsto_add_atTop_iff_nat m).mpr hs
    exact Tendsto.congr (fun j => (h1 j).symm) (this.div_const C)

theorem f2_limUnder_eq_of_eventually_eq {f : ℕ → ℝ} {L : ℝ} (h : ∀ᶠ i in atTop, f i = L) :
    limUnder atTop f = L :=
  (tendsto_const_nhds.congr' (h.mono fun _ h => h.symm)).limUnder_eq

theorem f2_exists_o {c : Fv} (hc : c ≠ 0) : ∃ o : ℤ, Valued.v c = exp (-o) := by
  refine ⟨-WithZero.log (Valued.v c), ?_⟩
  rw [neg_neg, WithZero.exp_log ((Valued.v).ne_zero_iff.mpr hc)]

section Core

open QuadFormsKB.Analysis QuadFormsKB.LocalZeta

theorem core_dvd_iff (k : ℕ) (z : 𝔬) : NF.π v ^ k ∣ z ↔ Valued.v (z : Fv) ≤ exp (-(k : ℤ)) := by
  rw [← NF.mem_span_π_pow, Ideal.mem_span_singleton]

theorem core_valued_le_one (z : 𝔬) : Valued.v (z : Fv) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp z.2

theorem core_exists_kappa : ∃ κ : ℕ, Valued.v (2 : Fv) = exp (-(κ : ℤ)) := by
  have h0 : Valued.v (2 : Fv) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact two_ne_zero
  have h1 : Valued.v (2 : Fv) ≤ 1 := by
    have := core_valued_le_one v 2
    have e : ((2 : 𝔬) : Fv) = 2 := by norm_cast
    rwa [e] at this
  obtain ⟨L, hL⟩ : ∃ L : ℤ, Valued.v (2 : Fv) = exp L := ⟨_, (WithZero.exp_log h0).symm⟩
  refine ⟨(-L).toNat, ?_⟩
  rw [hL] at h1 ⊢
  rw [← exp_zero, exp_le_exp] at h1
  congr 1
  omega

theorem core_norm_of_valued {x : Fv} {e : ℕ} (hx : Valued.v x = exp (-(e : ℤ))) :
    ‖x‖ = ((DVR.q 𝔬 : ℝ) ^ e)⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hx; exact WithZero.zero_ne_coe hx
  rw [LocalZeta.norm_eq_absNorm_pow v hx0, hx, WithZero.log_exp, NF.q_completion, _root_.zpow_neg, zpow_natCast]

/-! ### Congruence sets for a local form -/

/-- The base change of a local form to `Fv`. -/
abbrev QF (Q : QuadForm 𝔬 n) : QuadForm Fv n := Q.map (algebraMap 𝔬 Fv)

/-- `{X | Q ∘ X ≡ T mod 𝔭^k}` (all coefficients). -/
def thickF (Q : QuadForm 𝔬 n) (T : QuadForm Fv n) (k : ℕ) : Set (Matrix (Fin n) (Fin n) Fv) :=
  {X | ∀ i j, Valued.v (((QF v Q).compMat X).coeff i j - T.coeff i j) ≤ exp (-(k : ℤ))}

theorem thickF_eq (Q : QuadForm 𝔬 n) (T : QuadForm Fv n) (k : ℕ) : thickF v Q T k = ⋂ i, ⋂ j,
    (fun X : Matrix (Fin n) (Fin n) Fv => ((QF v Q).compMat X).coeff i j - T.coeff i j) ⁻¹'
      (latticeV v (k : ℤ) : Set Fv) := by
  ext X
  simp only [thickF, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, valued_le_iff_mem_latticeV]

theorem isClosed_thickF (Q : QuadForm 𝔬 n) (T : QuadForm Fv n) (k : ℕ) : IsClosed (thickF v Q T k) := by
  rw [thickF_eq]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    (isCompact_latticeV v k).isClosed.preimage ((continuous_compMat_coeff v _ i j).sub continuous_const)

theorem measurableSet_thickF (Q : QuadForm 𝔬 n) (T : QuadForm Fv n) (k : ℕ) :
    MeasurableSet (thickF v Q T k) := (isClosed_thickF v Q T k).measurableSet

theorem core_mem_thickF_iff_redM (Q : QuadForm 𝔬 n) {k : ℕ} {X : Matrix (Fin n) (Fin n) Fv} (hX : X ∈ intM v) :
    X ∈ thickF v Q (QF v Q) k ↔ (Q.map (Ideal.Quotient.mk _)).compMat (redM v k X hX) =
      Q.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k})) := by
  have e1 : (QF v Q).compMat X = (Q.compMat (toOM v X hX)).map (algebraMap 𝔬 Fv) := by
    conv_lhs => rw [← map_toOM v X hX]
    exact QuadForm.map_compMat _ _ _
  have e2 : (Q.map (Ideal.Quotient.mk _)).compMat (redM v k X hX) =
      (Q.compMat (toOM v X hX)).map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k})) :=
    QuadForm.map_compMat _ _ _
  have cm : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (S : QuadForm A n) (i j : Fin n),
      (S.map f).coeff i j = f (S.coeff i j) := fun _ _ _ _ => rfl
  rw [e2]
  constructor
  · intro h
    refine QuadForm.ext_upper fun i j _ => ?_
    rw [cm, cm, valued_sub_le_iff_mk_eq]
    have := h i j
    rw [e1, cm] at this
    exact this
  · intro h i j
    have := congrArg (fun S : QuadForm (RQ v k) n => S.coeff i j) h
    simp only [cm] at this
    rw [valued_sub_le_iff_mk_eq] at this
    rw [e1, cm]
    exact this

open Classical in
theorem core_intM_inter_thickF_eq (Q : QuadForm 𝔬 n) (k : ℕ) [Fintype (RQ v k)] :
    intM v ∩ thickF v Q (QF v Q) k = ⋃ Y ∈ (Finset.univ.filter fun Y : Matrix (Fin n) (Fin n) (RQ v k) =>
      (Q.map (Ideal.Quotient.mk _)).compMat Y =
        Q.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ k}))), fiberM v k Y := by
  ext X
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_univ, true_and, exists_prop,
    Finset.mem_filter]
  constructor
  · rintro ⟨hX, hT⟩
    exact ⟨redM v k X hX, (core_mem_thickF_iff_redM v Q hX).mp hT, (mem_fiberM_iff v).mpr ⟨hX, rfl⟩⟩
  · rintro ⟨Y, hY, hXY⟩
    obtain ⟨hX, rfl⟩ := (mem_fiberM_iff v).mp hXY
    exact ⟨hX, (core_mem_thickF_iff_redM v Q hX).mpr hY⟩

theorem core_volM_thickF (Q : QuadForm 𝔬 n) (k : ℕ) :
    volM v (intM v ∩ thickF v Q (QF v Q) k) =
      (DVR.repCountForm Q Q (NF.π v) k : ℝ≥0∞) * haarV v (latticeV v (k : ℤ)) ^ (n * n) := by
  classical
  have := DVR.finite_quot_pow (NF.π v) (NF.irreducible_π v) k
  let _ : Fintype (RQ v k) := Fintype.ofFinite _
  rw [core_intM_inter_thickF_eq v Q k, measure_biUnion_finset]
  · simp only [volM_fiberM, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [DVR.repCountForm, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · intro Y _ Y' _ h
    exact fiberM_disjoint v h
  · intro Y _; exact measurableSet_fiberM v k Y

/-! ### Gram coordinates versus coefficient coordinates -/

/-- The coefficient difference $(Q\circ x - Q)_{ab}$ over `Fv`. -/
def cd (Q : QuadForm 𝔬 n) (x : Matrix (Fin n) (Fin n) Fv) (a b : Fin n) : Fv :=
  ((QF v Q).compMat x).coeff a b - (QF v Q).coeff a b

theorem cd_eq_zero_of_lt (Q : QuadForm 𝔬 n) (x : Matrix (Fin n) (Fin n) Fv) {a b : Fin n} (h : b < a) :
    cd v Q x a b = 0 := by
  unfold cd
  rw [((QF v Q).compMat x).upper (show id b < id a from h), (QF v Q).upper (show id b < id a from h), sub_zero]

theorem core_gram_entry (Q : QuadForm 𝔬 n) (x : Matrix (Fin n) (Fin n) Fv) (a b : Fin n) :
    (xᵀ * gramOf v Q * x - gramOf v Q) a b = (1 / 2 : Fv) * (cd v Q x a b + cd v Q x b a) := by
  have h1 : gramOf v Q = (1 / 2 : Fv) • (QF v Q).hessian := by
    unfold gramOf; rw [QuadForm.hessian_map]
  have h2 : xᵀ * gramOf v Q * x = (1 / 2 : Fv) • ((QF v Q).compMat x).hessian := by
    rw [QuadForm.hessian_compMat, h1, Matrix.mul_smul, Matrix.smul_mul]
  rw [h2, Matrix.sub_apply, h1, Matrix.smul_apply, Matrix.smul_apply, ← smul_sub]
  simp only [QuadForm.hessian, cd, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  ring

theorem core_valued_half {κ : ℕ} (hκ : Valued.v (2 : Fv) = exp (-(κ : ℤ))) :
    Valued.v (1 / 2 : Fv) = exp (κ : ℤ) := by
  rw [one_div, map_inv₀, hκ, ← WithZero.exp_neg, neg_neg]

theorem core_gram_le_iff (Q : QuadForm 𝔬 n) {κ : ℕ} (hκ : Valued.v (2 : Fv) = exp (-(κ : ℤ)))
    (x : Matrix (Fin n) (Fin n) Fv) (i : ℕ) :
    (∀ a b, Valued.v ((xᵀ * gramOf v Q * x - gramOf v Q) a b) ≤ exp (-(i : ℤ))) ↔
      ∀ a b, a ≤ b → Valued.v (cd v Q x a b) ≤ exp (-((if a = b then i else i + κ : ℕ) : ℤ)) := by
  have hh := core_valued_half v hκ
  have key : ∀ a b, a < b → (Valued.v ((xᵀ * gramOf v Q * x - gramOf v Q) a b) ≤ exp (-(i : ℤ)) ↔
      Valued.v (cd v Q x a b) ≤ exp (-((i : ℤ) + κ))) := by
    intro a b hab
    rw [core_gram_entry, cd_eq_zero_of_lt v Q x hab, add_zero, map_mul, hh]
    constructor
    · intro h
      have := mul_le_mul_right h (exp (-(κ : ℤ)))
      rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul, ← exp_add] at this
      rw [show -((i : ℤ) + κ) = -(κ : ℤ) + -(i : ℤ) by ring]; exact this
    · intro h
      have := mul_le_mul_right h (exp (κ : ℤ))
      rw [← exp_add] at this
      rw [show (κ : ℤ) + -((i : ℤ) + κ) = -(i : ℤ) by ring] at this
      exact this
  have diag : ∀ a, Valued.v ((xᵀ * gramOf v Q * x - gramOf v Q) a a) ≤ exp (-(i : ℤ)) ↔
      Valued.v (cd v Q x a a) ≤ exp (-(i : ℤ)) := by
    intro a
    rw [core_gram_entry, ← two_mul, ← mul_assoc, one_div, inv_mul_cancel₀ two_ne_zero, one_mul]
  constructor
  · intro h a b hab
    rcases hab.lt_or_eq with hlt | rfl
    · rw [if_neg hlt.ne]; push_cast; exact (key a b hlt).mp (h a b)
    · rw [if_pos rfl]; exact (diag a).mp (h a a)
  · intro h a b
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · have := h a b hlt.le
      rw [if_neg hlt.ne] at this; push_cast at this
      exact (key a b hlt).mpr this
    · have := h a a le_rfl
      rw [if_pos rfl] at this
      exact (diag a).mpr this
    · have e : (xᵀ * gramOf v Q * x - gramOf v Q) a b = (xᵀ * gramOf v Q * x - gramOf v Q) b a := by
        rw [core_gram_entry, core_gram_entry, add_comm]
      rw [e]
      have := h b a hgt.le
      rw [if_neg hgt.ne] at this; push_cast at this
      exact (key b a hgt).mpr this

/-! ### Composition with an integral matrix preserves closeness -/

theorem core_bound_mul (c : ℤᵐ⁰) {M h : Matrix (Fin n) (Fin n) Fv} (hh : ∀ i j, Valued.v (h i j) ≤ 1)
    (hM : ∀ i j, Valued.v (M i j) ≤ c) (a b : Fin n) : Valued.v ((hᵀ * M * h) a b) ≤ c := by
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  have h1 : Valued.v (∑ k, hᵀ a k * M k l) ≤ c := by
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    have := mul_le_mul' (hh k a) (hM k l)
    simpa using this
  have := mul_le_mul' h1 (hh l b)
  simpa using this

theorem core_compMat_coeff (P : QuadForm Fv n) (h : Matrix (Fin n) (Fin n) Fv) (a b : Fin n) :
    (P.compMat h).coeff a b = if a ≤ b then (if a = b then (hᵀ * P.coeff * h) a a
      else (hᵀ * (P.coeff + P.coeffᵀ) * h) a b) else 0 := by
  rw [QuadForm.compMat_coeff]
  split_ifs with h1 h2
  · subst h2
    rw [QuadForm.eval_eq_dotProduct', ← QuadForm.transpose_mul_mul_apply]
  · rw [← QuadForm.transpose_mul_mul_apply]; rfl
  · rfl

theorem core_compMat_close (c : ℤᵐ⁰) {P P' : QuadForm Fv n} {h : Matrix (Fin n) (Fin n) Fv}
    (hh : ∀ i j, Valued.v (h i j) ≤ 1) (hd : ∀ a b, Valued.v (P.coeff a b - P'.coeff a b) ≤ c) (a b : Fin n) :
    Valued.v ((P.compMat h).coeff a b - (P'.compMat h).coeff a b) ≤ c := by
  have hc : 0 ≤ c := zero_le
  rw [core_compMat_coeff, core_compMat_coeff]
  split_ifs with h1 h2
  · rw [← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact core_bound_mul v c hh (fun k l => hd k l) a a
  · rw [← Matrix.sub_apply, ← Matrix.sub_mul, ← Matrix.mul_sub]
    refine core_bound_mul v c hh (fun k l => ?_) a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.transpose_apply]
    rw [show P.coeff k l + P.coeff l k - (P'.coeff k l + P'.coeff l k) =
      (P.coeff k l - P'.coeff k l) + (P.coeff l k - P'.coeff l k) by ring]
    exact Valuation.map_add_le _ (hd k l) (hd l k)
  · simpa using hc

theorem core_mul_mem_intM {x y : Matrix (Fin n) (Fin n) Fv} (hx : x ∈ intM v) (hy : y ∈ intM v) :
    x * y ∈ intM v := by
  intro i j
  simp only [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  have := mul_le_mul' (hx i k) (hy k j)
  simpa using this

theorem core_mul_mem_thickF (Q : QuadForm 𝔬 n) {T : QuadForm Fv n} {k : ℕ} {x h : Matrix (Fin n) (Fin n) Fv}
    (hh : h ∈ intM v) (hx : x ∈ thickF v Q T k) : x * h ∈ thickF v Q (T.compMat h) k := by
  intro a b
  rw [← QuadForm.compMat_mul]
  exact core_compMat_close v _ hh hx a b

/-! ### Hensel: realizing a diagonal perturbation by an isometry-like change of variables -/

/-- The form $Q + \sum_a \delta_a x_a^2$. -/
def addDiag (Q : QuadForm 𝔬 n) (δ : Fin n → 𝔬) : QuadForm 𝔬 n :=
  ⟨Q.coeff + Matrix.diagonal δ, fun i j h => by
    have h1 : Q.coeff i j = 0 := Q.upper h
    have h2 : (Matrix.diagonal δ) i j = 0 := Matrix.diagonal_apply_ne _ (ne_of_gt h)
    simp [h1, h2]⟩

theorem addDiag_zero (Q : QuadForm 𝔬 n) : addDiag v Q 0 = Q := by
  ext i j; simp [addDiag]

theorem core_hensel (Q : QuadForm 𝔬 n) {d K : ℕ} (hd : NF.π v ^ d ∣ Q.hessian.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ Q.hessian.det) (hK : 2 * d + 1 ≤ K) (δ : Fin n → 𝔬)
    (hδ : ∀ a, NF.π v ^ K ∣ δ a) :
    ∃ g : Matrix (Fin n) (Fin n) 𝔬, Q.compMat g = addDiag v Q δ ∧
      ∀ i j, NF.π v ^ (K - d) ∣ g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j := by
  have hπ := NF.irreducible_π v
  set T := addDiag v Q δ with hT
  have hTh : T.hessian = Q.hessian + Matrix.diagonal (fun a => 2 * δ a) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp only [hT, addDiag, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.diagonal_apply_eq]
      ring
    · simp only [hT, addDiag, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply,
        Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), add_zero]
  have hdetT : NF.π v ^ K ∣ T.hessian.det - Q.hessian.det := by
    have hmap : (Ideal.Quotient.mk (Ideal.span {NF.π v ^ K})).mapMatrix T.hessian =
        (Ideal.Quotient.mk (Ideal.span {NF.π v ^ K})).mapMatrix Q.hessian := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, hTh, Matrix.add_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h; rw [add_sub_cancel_left]; exact dvd_mul_of_dvd_right (hδ a) 2
      · rw [add_zero, sub_self]; exact dvd_zero _
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, hmap]
  obtain ⟨u, hu, huu⟩ := DVR.dvr_exact hπ hd hd'
  obtain ⟨s, hs⟩ := hdetT
  have hTdet : T.hessian.det = NF.π v ^ d * (u + NF.π v ^ (K - d) * s) := by
    rw [mul_add, ← mul_assoc, ← pow_add, show d + (K - d) = K by omega, ← hs, ← hu]; ring
  have hdT : NF.π v ^ d ∣ T.hessian.det := ⟨_, hTdet⟩
  have hdT' : ¬ NF.π v ^ (d + 1) ∣ T.hessian.det := by
    intro h
    rw [hTdet, pow_succ] at h
    have h2 := (mul_dvd_mul_iff_left (pow_ne_zero d hπ.ne_zero)).mp h
    apply DVR.dvr_not_dvd_of_isUnit hπ huu
    have : NF.π v ∣ NF.π v ^ (K - d) * s :=
      dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) s
    simpa using dvd_sub h2 this
  have hx : ∀ p : DVR.UpperIdx n, NF.π v ^ K ∣
      DVR.formF Q (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) p - T.coeff p.1.1 p.1.2 := by
    intro p
    have e : DVR.toMat (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) = 1 := rfl
    simp only [DVR.formF, e, QuadForm.compMat_one, hT, addDiag, Matrix.add_apply, Matrix.diagonal_apply]
    split_ifs with h
    · rw [sub_add_cancel_left]; exact (dvd_neg).mpr (hδ _)
    · rw [add_zero, sub_self]; exact dvd_zero _
  obtain ⟨y, hy, hyx⟩ := DVR.newton_lift hπ (DVR.formF Q) (DVR.formD Q) (DVR.formF_add_smul Q)
    (fun p : DVR.UpperIdx n => T.coeff p.1.1 p.1.2) d K hK
    (fun x hx' c => DVR.formD_surj Q T (NF.π v) hπ d K hdT hdT' (by omega) x hx' c)
    (fun li : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) 𝔬) li.1 li.2) hx
  refine ⟨DVR.toMat y, QuadForm.ext_upper fun i j hij => ?_, fun i j => hyx (i, j)⟩
  exact congrFun hy ⟨(i, j), hij⟩

/-! ### The translates $T(\delta)$ all have the volume of $T(0)$ -/

/-- $T(\delta) = M_n(\mathfrak o)\cap\{x : Q\circ x\equiv Q+\operatorname{diag}\delta \bmod \mathfrak p^k\}$. -/
def Tset (Q : QuadForm 𝔬 n) (δ : Fin n → 𝔬) (k : ℕ) : Set (Matrix (Fin n) (Fin n) Fv) :=
  intM v ∩ thickF v Q ((addDiag v Q δ).map (algebraMap 𝔬 Fv)) k

theorem Tset_zero (Q : QuadForm 𝔬 n) (k : ℕ) : Tset v Q 0 k = intM v ∩ thickF v Q (QF v Q) k := by
  rw [Tset, addDiag_zero]

theorem measurableSet_intM : MeasurableSet (intM v : Set (Matrix (Fin n) (Fin n) Fv)) :=
  (QuadFormsKB.Tamagawa.Measure.isOpen_intMat v).measurableSet

theorem core_g_mem_ballOne {g : Matrix (Fin n) (Fin n) 𝔬} {m : ℕ}
    (hg : ∀ i j, NF.π v ^ m ∣ g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j) :
    g.map (algebraMap 𝔬 Fv) ∈ ballOne v m := by
  intro i j
  have h := (core_dvd_iff v m _).mp (hg i j)
  have e : (((g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j : 𝔬)) : Fv) =
      g.map (algebraMap 𝔬 Fv) i j - (1 : Matrix (Fin n) (Fin n) Fv) i j := by
    push_cast
    rw [coe_one_apply]
    rfl
  rwa [e] at h

theorem core_Tset_eq (Q : QuadForm 𝔬 n) {δ : Fin n → 𝔬} {g : Matrix (Fin n) (Fin n) 𝔬} {m : ℕ} (hm : 1 ≤ m)
    (hg : Q.compMat g = addDiag v Q δ) (hgm : ∀ i j, NF.π v ^ m ∣ g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j)
    (k : ℕ) :
    Tset v Q δ k = (fun x => x * (g.map (algebraMap 𝔬 Fv))⁻¹) ⁻¹' Tset v Q 0 k := by
  set g' := g.map (algebraMap 𝔬 Fv) with hg'
  have hb : g' ∈ ballOne v m := core_g_mem_ballOne v hgm
  have hdet := valued_det_eq_one v hm hb
  have hu : IsUnit g'.det := isUnit_iff_ne_zero.mpr (by intro h; rw [h, map_zero] at hdet; exact zero_ne_one hdet)
  obtain ⟨hbi, hinv⟩ := inv_mem_ballOne v hm hb
  have hgi : g' ∈ intM v := ballOne_subset_intM v m hb
  have hgii : g'⁻¹ ∈ intM v := ballOne_subset_intM v m hbi
  have hcomp : (QF v Q).compMat g' = (addDiag v Q δ).map (algebraMap 𝔬 Fv) := by
    rw [← hg, hg']
    exact QuadForm.map_compMat _ _ _
  have hmulinv : g' * g'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  ext x
  simp only [Tset_zero, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨hx, hT⟩
    refine ⟨core_mul_mem_intM v hx hgii, ?_⟩
    have := core_mul_mem_thickF v Q hgii hT
    rwa [← hcomp, QuadForm.compMat_mul, hmulinv, QuadForm.compMat_one] at this
  · rintro ⟨hy, hT⟩
    have hx : x * g'⁻¹ * g' ∈ intM v := core_mul_mem_intM v hy hgi
    have e : x * g'⁻¹ * g' = x := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    rw [e] at hx
    refine ⟨hx, ?_⟩
    have := core_mul_mem_thickF v Q hgi hT
    rwa [e, hcomp] at this

theorem core_vol_Tset (Q : QuadForm 𝔬 n) {δ : Fin n → 𝔬} {g : Matrix (Fin n) (Fin n) 𝔬} {m : ℕ} (hm : 1 ≤ m)
    (hg : Q.compMat g = addDiag v Q δ) (hgm : ∀ i j, NF.π v ^ m ∣ g i j - (1 : Matrix (Fin n) (Fin n) 𝔬) i j)
    (k : ℕ) : volM v (Tset v Q δ k) = volM v (Tset v Q 0 k) := by
  rw [core_Tset_eq v Q hm hg hgm k]
  have hb : g.map (algebraMap 𝔬 Fv) ∈ ballOne v m := core_g_mem_ballOne v hgm
  obtain ⟨hbi, _⟩ := inv_mem_ballOne v hm hb
  refine (measurePreserving_mulRightM v (ballOne_subset_intM v m hbi) (valued_det_eq_one v hm hbi)).measure_preimage ?_
  rw [Tset_zero]
  exact ((measurableSet_intM v).inter (measurableSet_thickF v Q _ k)).nullMeasurableSet

/-! ### The decomposition of the Gram fibre into translates -/

/-- The set $G_i$ in coefficient coordinates: diagonal coefficients of $Q\circ x - Q$ in $\mathfrak p^i$, off-diagonal
ones in $\mathfrak p^{i+\kappa}$. -/
def Gset (Q : QuadForm 𝔬 n) (κ i : ℕ) : Set (Matrix (Fin n) (Fin n) Fv) :=
  intM v ∩ {x | ∀ a b, a ≤ b → Valued.v (cd v Q x a b) ≤ exp (-((if a = b then i else i + κ : ℕ) : ℤ))}

/-- Representatives of the diagonal perturbations $\pi^i\cdot(\mathfrak o/\pi^\kappa)^n$. -/
def repDelta (κ i : ℕ) (r : Fin n → RQ v κ) : Fin n → 𝔬 := fun a => NF.π v ^ i * Quotient.out (r a)

theorem core_coeff_addDiag (Q : QuadForm 𝔬 n) (δ : Fin n → 𝔬) (a b : Fin n) :
    ((addDiag v Q δ).map (algebraMap 𝔬 Fv)).coeff a b =
      (QF v Q).coeff a b + (Matrix.diagonal (fun a => ((δ a : 𝔬) : Fv))) a b := by
  by_cases h : a = b
  · subst h
    simp [addDiag, QuadForm.map, QF]
  · simp [addDiag, QuadForm.map, QF, Matrix.diagonal_apply_ne _ h]

theorem core_mem_thickF_addDiag_iff (Q : QuadForm 𝔬 n) (δ : Fin n → 𝔬) (k : ℕ) (x : Matrix (Fin n) (Fin n) Fv) :
    x ∈ thickF v Q ((addDiag v Q δ).map (algebraMap 𝔬 Fv)) k ↔
      ∀ a b, Valued.v (cd v Q x a b - (Matrix.diagonal (fun a => ((δ a : 𝔬) : Fv))) a b) ≤ exp (-(k : ℤ)) := by
  have e : ∀ a b, ((QF v Q).compMat x).coeff a b - ((addDiag v Q δ).map (algebraMap 𝔬 Fv)).coeff a b =
      cd v Q x a b - (Matrix.diagonal (fun a => ((δ a : 𝔬) : Fv))) a b := by
    intro a b
    rw [core_coeff_addDiag, cd]; ring
  constructor
  · intro h a b; rw [← e]; exact h a b
  · intro h a b; rw [e]; exact h a b

theorem core_valued_pow_pi (i : ℕ) : Valued.v (((NF.π v ^ i : 𝔬)) : Fv) = exp (-(i : ℤ)) := by
  push_cast
  rw [map_pow, NF.valued_π, ← WithZero.exp_nsmul]
  congr 1; simp

theorem core_Tset_subset_Gset (Q : QuadForm 𝔬 n) (κ i : ℕ) (r : Fin n → RQ v κ) :
    Tset v Q (repDelta v κ i r) (i + κ) ⊆ Gset v Q κ i := by
  rintro x ⟨hx, hT⟩
  refine ⟨hx, fun a b hab => ?_⟩
  rw [core_mem_thickF_addDiag_iff] at hT
  have hk : ∀ a b, Valued.v (cd v Q x a b - (Matrix.diagonal (fun a => ((repDelta v κ i r a : 𝔬) : Fv))) a b)
      ≤ exp (-(i + κ : ℕ) : ℤ) := fun a b => by exact_mod_cast hT a b
  rcases hab.lt_or_eq with hlt | rfl
  · have h1 := hk a b
    rw [Matrix.diagonal_apply_ne _ hlt.ne, sub_zero] at h1
    rw [if_neg hlt.ne]; exact h1
  · have h1 := hk a a
    rw [Matrix.diagonal_apply_eq] at h1
    rw [if_pos rfl]
    have h2 : Valued.v (((repDelta v κ i r a : 𝔬)) : Fv) ≤ exp (-(i : ℤ)) := by
      rw [repDelta]
      exact (core_dvd_iff v i _).mp (dvd_mul_right _ _)
    have h3 : cd v Q x a a = (cd v Q x a a - ((repDelta v κ i r a : 𝔬) : Fv)) + ((repDelta v κ i r a : 𝔬) : Fv) := by
      ring
    rw [h3]
    refine Valuation.map_add_le _ (h1.trans ?_) h2
    rw [exp_le_exp]; push_cast; omega

theorem core_Gset_subset_iUnion (Q : QuadForm 𝔬 n) (κ i : ℕ) :
    Gset v Q κ i ⊆ ⋃ r : Fin n → RQ v κ, Tset v Q (repDelta v κ i r) (i + κ) := by
  rintro x ⟨hx, hG⟩
  have hp : Valued.v (((NF.π v ^ i : 𝔬)) : Fv) = exp (-(i : ℤ)) := core_valued_pow_pi v i
  have hp0 : (((NF.π v ^ i : 𝔬)) : Fv) ≠ 0 := by
    intro h; rw [h, map_zero] at hp; exact WithZero.zero_ne_coe hp
  have hz : ∀ a, ∃ z : 𝔬, cd v Q x a a = (((NF.π v ^ i * z : 𝔬)) : Fv) := by
    intro a
    have h := hG a a le_rfl
    rw [if_pos rfl] at h
    have hc : Valued.v (cd v Q x a a / (((NF.π v ^ i : 𝔬)) : Fv)) ≤ 1 := by
      rw [map_div₀, hp]
      exact (div_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr h
    refine ⟨toO v _ hc, ?_⟩
    show cd v Q x a a = (((NF.π v ^ i : 𝔬)) : Fv) * (cd v Q x a a / (((NF.π v ^ i : 𝔬)) : Fv))
    field_simp
  choose z hz using hz
  refine Set.mem_iUnion.2 ⟨fun a => Ideal.Quotient.mk _ (z a), hx, ?_⟩
  rw [core_mem_thickF_addDiag_iff]
  intro a b
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · rw [Matrix.diagonal_apply_ne _ hlt.ne, sub_zero]
    have := hG a b hlt.le
    rw [if_neg hlt.ne] at this
    exact_mod_cast this
  · rw [Matrix.diagonal_apply_eq, hz a]
    have hd : NF.π v ^ (i + κ) ∣ NF.π v ^ i * z a - repDelta v κ i (fun a => Ideal.Quotient.mk _ (z a)) a := by
      rw [repDelta, ← mul_sub, pow_add]
      refine mul_dvd_mul_left _ ?_
      have := Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {NF.π v ^ κ}) (z a))
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
      rw [← dvd_neg, neg_sub]
      exact this
    have := (core_dvd_iff v _ _).mp hd
    push_cast at this ⊢
    exact this
  · rw [cd_eq_zero_of_lt v Q x hgt, Matrix.diagonal_apply_ne _ hgt.ne', sub_zero, map_zero]
    exact zero_le

theorem core_Tset_disjoint (Q : QuadForm 𝔬 n) (κ i : ℕ) {r r' : Fin n → RQ v κ} (h : r ≠ r') :
    Disjoint (Tset v Q (repDelta v κ i r) (i + κ)) (Tset v Q (repDelta v κ i r') (i + κ)) := by
  rw [Set.disjoint_left]
  rintro x ⟨_, h1⟩ ⟨_, h2⟩
  obtain ⟨a, ha⟩ := Function.ne_iff.mp h
  rw [core_mem_thickF_addDiag_iff] at h1 h2
  have h1a := h1 a a
  have h2a := h2 a a
  rw [Matrix.diagonal_apply_eq] at h1a h2a
  have h3 : Valued.v (((repDelta v κ i r a : 𝔬) : Fv) - ((repDelta v κ i r' a : 𝔬) : Fv)) ≤ exp (-((i + κ : ℕ) : ℤ)) := by
    have := Valuation.map_sub_le _ h2a h1a
    have e : (cd v Q x a a - ((repDelta v κ i r' a : 𝔬) : Fv)) - (cd v Q x a a - ((repDelta v κ i r a : 𝔬) : Fv))
        = ((repDelta v κ i r a : 𝔬) : Fv) - ((repDelta v κ i r' a : 𝔬) : Fv) := by ring
    rw [e] at this
    simpa using this
  have h4 : NF.π v ^ (i + κ) ∣ repDelta v κ i r a - repDelta v κ i r' a := by
    rw [core_dvd_iff]; push_cast; exact_mod_cast h3
  rw [repDelta, repDelta, ← mul_sub, pow_add] at h4
  have h5 := (mul_dvd_mul_iff_left (pow_ne_zero i (NF.irreducible_π v).ne_zero)).mp h4
  apply ha
  rw [← Ideal.Quotient.mk_out (r a), ← Ideal.Quotient.mk_out (r' a), Ideal.Quotient.eq,
    Ideal.mem_span_singleton]
  exact h5

theorem core_Gset_eq (Q : QuadForm 𝔬 n) (κ i : ℕ) :
    Gset v Q κ i = ⋃ r : Fin n → RQ v κ, Tset v Q (repDelta v κ i r) (i + κ) :=
  Set.Subset.antisymm (core_Gset_subset_iUnion v Q κ i)
    (Set.iUnion_subset fun r => core_Tset_subset_Gset v Q κ i r)

theorem core_vol_Gset (Q : QuadForm 𝔬 n) {d : ℕ} (hd : NF.π v ^ d ∣ Q.hessian.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ Q.hessian.det) (κ i : ℕ) (hi : 2 * d + 1 ≤ i) :
    volM v (Gset v Q κ i) = ((DVR.q 𝔬 : ℝ≥0∞) ^ κ) ^ n * volM v (Tset v Q 0 (i + κ)) := by
  classical
  have hfin := DVR.finite_quot_pow (NF.π v) (NF.irreducible_π v) κ
  let _ : Fintype (RQ v κ) := Fintype.ofFinite _
  have hmeas : ∀ (δ : Fin n → 𝔬) (k : ℕ), MeasurableSet (Tset v Q δ k) := fun δ k =>
    (measurableSet_intM v).inter (measurableSet_thickF v Q _ k)
  rw [core_Gset_eq, measure_iUnion (fun r r' h => core_Tset_disjoint v Q κ i h) (fun r => hmeas _ _),
    tsum_fintype]
  have hvol : ∀ r : Fin n → RQ v κ, volM v (Tset v Q (repDelta v κ i r) (i + κ)) =
      volM v (Tset v Q 0 (i + κ)) := by
    intro r
    obtain ⟨g, hg, hgm⟩ := core_hensel v Q hd hd' hi (repDelta v κ i r) (fun a => dvd_mul_right _ _)
    exact core_vol_Tset v Q (m := i - d) (by omega) hg hgm _
  simp only [hvol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
  congr 2
  rw [← Nat.card_eq_fintype_card, NF.card_quot_π_pow, ← NF.q_completion]
  push_cast
  rfl

/-! ### Matrices that are isometries modulo $\pi^i$ ($i > d$) have unit determinant -/

theorem core_isUnit_det (H X : Matrix (Fin n) (Fin n) 𝔬) {d i : ℕ} (hd : NF.π v ^ d ∣ H.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ H.det) (hi : d < i)
    (h : ∀ a b, NF.π v ^ i ∣ (Xᵀ * H * X) a b - H a b) : IsUnit X.det := by
  have hπ := NF.irreducible_π v
  have hdet : NF.π v ^ i ∣ (Xᵀ * H * X).det - H.det := by
    have hmap : (Ideal.Quotient.mk (Ideal.span {NF.π v ^ i})).mapMatrix (Xᵀ * H * X) =
        (Ideal.Quotient.mk (Ideal.span {NF.π v ^ i})).mapMatrix H := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact h a b
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, hmap]
  obtain ⟨u, hu, huu⟩ := DVR.dvr_exact hπ hd hd'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hu] at hdet
  have e : X.det * (NF.π v ^ d * u) * X.det - NF.π v ^ d * u = NF.π v ^ d * (u * (X.det ^ 2 - 1)) := by ring
  rw [e, show i = d + (i - d) by omega, pow_add] at hdet
  have h1 := (mul_dvd_mul_iff_left (pow_ne_zero d hπ.ne_zero)).mp hdet
  have h2 : NF.π v ^ (i - d) ∣ X.det ^ 2 - 1 := by
    obtain ⟨w, hw⟩ := huu
    obtain ⟨c, hc⟩ := h1
    refine ⟨↑w⁻¹ * c, ?_⟩
    calc X.det ^ 2 - 1 = (↑w⁻¹ * ↑w) * (X.det ^ 2 - 1) := by rw [Units.inv_mul, one_mul]
      _ = ↑w⁻¹ * (u * (X.det ^ 2 - 1)) := by rw [hw]; ring
      _ = _ := by rw [hc]; ring
  have h3 : NF.π v ∣ X.det ^ 2 - 1 := (dvd_pow_self _ (by omega : i - d ≠ 0)).trans h2
  apply DVR.dvr_isUnit_of_not_dvd hπ
  intro h4
  have h5 : NF.π v ∣ X.det ^ 2 := dvd_pow h4 two_ne_zero
  have : NF.π v ∣ 1 := by simpa using dvd_sub h5 h3
  exact hπ.not_isUnit (isUnit_of_dvd_one this)

theorem core_det_valued_one (Q : QuadForm 𝔬 n) {d i : ℕ} (hd : NF.π v ^ d ∣ Q.hessian.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ Q.hessian.det) (hi : d < i) {x : Matrix (Fin n) (Fin n) Fv} (hx : x ∈ intM v)
    (hc : ∀ a b, a ≤ b → Valued.v (cd v Q x a b) ≤ exp (-(i : ℤ))) : Valued.v x.det = 1 := by
  have hall : ∀ a b, Valued.v (cd v Q x a b) ≤ exp (-(i : ℤ)) := by
    intro a b
    rcases le_or_gt a b with h | h
    · exact hc a b h
    · rw [cd_eq_zero_of_lt v Q x h, map_zero]; exact zero_le
  set X := toOM v x hx with hX
  have hmap : xᵀ * (QF v Q).hessian * x - (QF v Q).hessian =
      (Xᵀ * Q.hessian * X - Q.hessian).map (algebraMap 𝔬 Fv) := by
    rw [Matrix.map_sub _ (fun a b => map_sub (algebraMap 𝔬 Fv) a b), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hX, map_toOM,
      QF, QuadForm.hessian_map]
  have h : ∀ a b, NF.π v ^ i ∣ (Xᵀ * Q.hessian * X) a b - Q.hessian a b := by
    intro a b
    rw [core_dvd_iff]
    have e : (((Xᵀ * Q.hessian * X) a b - Q.hessian a b : 𝔬) : Fv) =
        (xᵀ * (QF v Q).hessian * x - (QF v Q).hessian) a b := by
      rw [hmap]; rfl
    rw [e, ← QuadForm.hessian_compMat]
    simp only [Matrix.sub_apply, QuadForm.hessian, Matrix.add_apply, Matrix.transpose_apply]
    have e2 : ((QF v Q).compMat x).coeff a b + ((QF v Q).compMat x).coeff b a -
        ((QF v Q).coeff a b + (QF v Q).coeff b a) = cd v Q x a b + cd v Q x b a := by
      unfold cd; ring
    rw [e2]
    exact Valuation.map_add_le _ (hall a b) (hall b a)
  have hu := core_isUnit_det v Q.hessian X hd hd' hi h
  have := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu
  rwa [det_toOM v x hx] at this

theorem core_gramFiber_eq (Q : QuadForm 𝔬 n) {d : ℕ} (hd : NF.π v ^ d ∣ Q.hessian.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ Q.hessian.det) {κ : ℕ} (hκ : Valued.v (2 : Fv) = exp (-(κ : ℤ))) {i : ℕ}
    (hi : d < i) : gramFiber v (std v) (gramOf v Q) i = Gset v Q κ i := by
  ext x
  simp only [gramFiber, Gset, Set.mem_ofPred_eq, Set.mem_inter_iff, stabLat_std_iff]
  constructor
  · rintro ⟨⟨hx, _⟩, hg⟩
    exact ⟨hx, (core_gram_le_iff v Q hκ x i).mp hg⟩
  · rintro ⟨hx, hG⟩
    have hdet : Valued.v x.det = 1 := by
      refine core_det_valued_one v Q hd hd' hi hx fun a b hab => (hG a b hab).trans ?_
      rw [exp_le_exp]
      split_ifs <;> push_cast <;> omega
    exact ⟨⟨hx, hdet⟩, (core_gram_le_iff v Q hκ x i).mpr hG⟩

theorem core_N_eq (n : ℕ) : n * (n + 1) / 2 = n * (n - 1) / 2 + n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (m + 1) * (m + 1 + 1) = (m + 1) * m + 2 * (m + 1) := by ring
  rw [this, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

theorem core_arith (q A : ℝ) (hq : q ≠ 0) (i κ n M N : ℕ) (h1 : N = M + n) (h2 : n * n = N + M) :
    q ^ (i * N) * (q ^ κ) ^ n * (A * ((q ^ (i + κ))⁻¹) ^ (n * n)) =
      ((q ^ κ)⁻¹) ^ M * (A / q ^ ((i + κ) * M)) := by
  rw [h2]
  subst h1
  rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  have key : q ^ (i * (M + n)) * (q ^ κ) ^ n * ((q ^ κ) ^ M * q ^ ((i + κ) * M)) =
      q ^ ((i + κ) * (M + n + M)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [← key]
  field_simp
  rw [← pow_mul, mul_comm]

theorem core_gramRatio_eventually (Q : QuadForm 𝔬 n) (hQ : Q.hessian.det ≠ 0) :
    ∃ I : ℕ, ∀ i ≥ I, gramRatio v (std v) (gramOf v Q) i =
      ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) * DVR.localDensityForm Q Q (NF.π v) := by
  have hπ := NF.irreducible_π v
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hQ
  obtain ⟨κ, hκ⟩ := core_exists_kappa v
  refine ⟨2 * d + 1, fun i hi => ?_⟩
  have hq0 : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast DVR.q_pos (R := 𝔬)
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hq0' : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq0.ne'
  -- the volume
  have hvol : volM v (gramFiber v (std v) (gramOf v Q) i) =
      ((DVR.q 𝔬 : ℝ≥0∞) ^ κ) ^ n * ((DVR.repCountForm Q Q (NF.π v) (i + κ) : ℝ≥0∞) *
        ((DVR.q 𝔬 : ℝ≥0∞) ^ (i + κ))⁻¹ ^ (n * n)) := by
    rw [core_gramFiber_eq v Q hd hd' hκ (by omega), core_vol_Gset v Q hd hd' κ i hi, Tset_zero,
      core_volM_thickF, haarV_latticeV_nat]
  have hLD := DVR.localDensityForm_eq Q Q (NF.π v) hπ d hd hd' le_rfl (i + κ) (by omega)
  rw [gramRatio, hvol, hLD, core_norm_of_valued v hκ]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_inv]
  have hNM : n * n - n * (n + 1) / 2 = n * (n - 1) / 2 := by
    have := two_mul_choose n; omega
  rw [hNM]
  have h1 := core_N_eq n
  have h2 := two_mul_choose n
  have := core_arith (DVR.q 𝔬 : ℝ) (DVR.repCountForm Q Q (NF.π v) (i + κ) : ℝ) hq0.ne' i κ n
    (n * (n - 1) / 2) (n * (n + 1) / 2) h1 h2.symm
  rw [← mul_assoc]
  exact this

end Core

/-- **The limit exists and is attained** for $\Lambda_\mathfrak p = \mathfrak o_v^n$ (`std v`) and symmetric nondegenerate
$\varphi$: the ratios $q^{i\,n(n+1)/2}\mathrm{vol}(U'_i)$ are eventually equal to $2\beta_\mathfrak p(\mathfrak o_v^n,\varphi)$. -/
theorem gramRatio_std_eventually_eq {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) :
    ∀ᶠ i in atTop, gramRatio v (std v) φ i = 2 * hankeBeta v (std v) φ := by
  have hsym : ∀ a b, φ b a = φ a b := fun a b => by
    have := congrFun (congrFun hφ a) b
    simpa using this
  -- a bound on the denominators
  have hm : ∀ p : Fin n × Fin n, ∃ m : ℕ, Valued.v (φ p.1 p.2) ≤ exp (m : ℤ) := by
    intro p
    by_cases h0 : Valued.v (φ p.1 p.2) = 0
    · exact ⟨0, by rw [h0]; exact zero_le⟩
    · refine ⟨(WithZero.log (Valued.v (φ p.1 p.2))).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h0]
      rw [exp_le_exp]; omega
  choose m hm using hm
  set a : ℕ := Finset.univ.sup m with ha
  have hbound : ∀ i j, Valued.v (φ i j) ≤ exp (a : ℤ) := fun i j =>
    (hm (i, j)).trans (by rw [exp_le_exp]; exact_mod_cast Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
  set c : Fv := ((NF.π v ^ a : 𝔬) : Fv) with hcdef
  have hc : Valued.v c = exp (-(a : ℤ)) := core_valued_pow_pi v a
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact WithZero.zero_ne_coe hc
  have hint : ∀ i j, Valued.v (c * φ i j) ≤ 1 := by
    intro i j
    rw [map_mul, hc]
    calc exp (-(a : ℤ)) * Valued.v (φ i j) ≤ exp (-(a : ℤ)) * exp (a : ℤ) := mul_le_mul_right (hbound i j) _
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  let ψ : Matrix (Fin n) (Fin n) 𝔬 := fun i j => toO v (c * φ i j) (hint i j)
  have hψ : ψ.map (algebraMap 𝔬 Fv) = c • φ := by
    ext i j; rfl
  have hψsym : ∀ x y, ψ y x = ψ x y := fun x y => Subtype.ext (by
    show c * φ y x = c * φ x y
    rw [hsym])
  let Q : QuadForm 𝔬 n := QuadForm.ofUpper fun i j => if i = j then ψ i i else 2 * ψ i j
  have hH : ∀ x y, Q.hessian x y = 2 * ψ x y := by
    intro x y
    simp only [QuadForm.hessian, Q, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy x y with h | h | h
    · simp [h.le, not_le.mpr h, h.ne, h.ne']
    · subst h; simp; ring
    · simp [h.le, not_le.mpr h, h.ne', h.ne, hψsym x y]
  have hHm : Q.hessian = (2 : 𝔬) • ψ := by
    ext x y; rw [hH]; rfl
  have hgram : gramOf v Q = c • φ := by
    rw [← hψ]
    ext x y
    simp only [gramOf, Matrix.smul_apply, Matrix.map_apply, hHm, smul_eq_mul]
    rw [map_mul, map_ofNat]
    field_simp
  have hdetψ : (ψ.map (algebraMap 𝔬 Fv)).det ≠ 0 := by
    rw [hψ, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc0) hdet
  have hdetψ' : ψ.det ≠ 0 := by
    intro h0
    apply hdetψ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hQ : Q.hessian.det ≠ 0 := by
    rw [hHm, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (NF.two_ne_zero' v)) hdetψ'
  obtain ⟨I, hI⟩ := core_gramRatio_eventually v Q hQ
  set K := ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) * DVR.localDensityForm Q Q (NF.π v)
  have hev : ∀ᶠ i in atTop, gramRatio v (std v) φ i = ‖c‖ ^ (n * (n + 1) / 2) * K := by
    filter_upwards [eventually_ge_atTop I] with i hi
    rw [f2_gramRatio_smul v (std v) φ (a : ℤ) hc (i := i) (j := i + a) (by push_cast; ring)]
    have := hI (i + a) (by omega)
    rw [hgram] at this
    rw [this]
  have hlim : hankeBeta v (std v) φ = (1 / 2 : ℝ) * (‖c‖ ^ (n * (n + 1) / 2) * K) := by
    unfold hankeBeta
    rw [f2_limUnder_eq_of_eventually_eq hev]
  filter_upwards [hev] with i hi
  rw [hi, hlim]; ring


/-- **Lemma 3.1** (Hanke thesis, p. 7): for $c\in F_v^\times$,
$\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi) = |c|_\mathfrak p^{n(n+1)/2}\,\beta_\mathfrak p(\Lambda_\mathfrak p,c\varphi)
= |\det(c\cdot1_n)|_\mathfrak p^{(n+1)/2}\,\beta_\mathfrak p(\Lambda_\mathfrak p,c\varphi)$.
For an arbitrary lattice the hypothesis is that the limit defining $\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi)$ exists
(Hanke's definition presupposes it); the proof is $U'_i(\varphi) = U'_{i+\mathrm{ord}(c)}(c\varphi)$. For
$\Lambda_\mathfrak p = \mathfrak o_v^n$ and nondegenerate symmetric $\varphi$ it holds unconditionally (`hankeBeta_std_smul`). -/
@[kb "hanke2005crelle" "Lemma 3.1, p. 7"]
theorem hankeBeta_smul (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv)
    (hconv : ∃ L, Tendsto (gramRatio v Λ φ) atTop (𝓝 L)) {c : Fv} (hc : c ≠ 0) :
    hankeBeta v Λ φ = ‖c‖ ^ (n * (n + 1) / 2) * hankeBeta v Λ (c • φ) := by
  obtain ⟨L, hL⟩ := hconv
  obtain ⟨o, ho⟩ := f2_exists_o v hc
  have hC : ‖c‖ ^ (n * (n + 1) / 2) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  have ht := f2_tendsto_pair hC o (fun i j hij => f2_gramRatio_smul v Λ φ o ho hij) hL
  unfold hankeBeta
  rw [hL.limUnder_eq, ht.limUnder_eq]
  field_simp

/-- The second form of Lemma 3.1: $|c|^{n(n+1)/2} = |\det(c\cdot1_n)|^{(n+1)/2}$. -/
@[kb "hanke2005crelle" "Lemma 3.1, p. 7"]
theorem hankeBeta_smul' (Λ : Submodule 𝔬 (Fin n → Fv)) (φ : Matrix (Fin n) (Fin n) Fv)
    (hconv : ∃ L, Tendsto (gramRatio v Λ φ) atTop (𝓝 L)) {c : Fv} (hc : c ≠ 0) :
    hankeBeta v Λ φ = ‖(c • (1 : Matrix (Fin n) (Fin n) Fv)).det‖ ^ (((n : ℝ) + 1) / 2) *
      hankeBeta v Λ (c • φ) := by
  rw [hankeBeta_smul v Λ φ hconv hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow,
    ← Real.rpow_natCast ‖c‖ n, ← Real.rpow_mul (norm_nonneg c), ← Real.rpow_natCast ‖c‖ (n * (n + 1) / 2)]
  congr 2
  have h := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
  have h' : (2 : ℝ) * ((n * (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (n + 1) := by exact_mod_cast h
  push_cast
  linarith

/-- **Lemma 3.1 for $\Lambda_\mathfrak p = \mathfrak o_v^n$** (no convergence hypothesis): $\varphi$ symmetric, $\det\varphi\ne0$. -/
@[kb "hanke2005crelle" "Lemma 3.1, p. 7"]
theorem hankeBeta_std_smul {φ : Matrix (Fin n) (Fin n) Fv} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) {c : Fv} (hc : c ≠ 0) :
    hankeBeta v (std v) φ = ‖c‖ ^ (n * (n + 1) / 2) * hankeBeta v (std v) (c • φ) := by
  refine hankeBeta_smul v (std v) φ ⟨2 * hankeBeta v (std v) φ, ?_⟩ hc
  exact tendsto_const_nhds.congr' ((gramRatio_std_eventually_eq v hφ hdet).mono fun _ h => h.symm)

/-- **Shimura's count** $N'_i = \#\{x\in(\mathcal O_\mathfrak p/\mathfrak p^i)^n_n : {}^tx\varphi x\equiv\varphi\bmod P_i\}$ for an
integral matrix $\varphi$ (Hanke thesis, proof of Lemma 3.2, p. 8, quoting [Shi, §8]). -/
@[kb "hanke2005crelle" "Lemma 3.2 and its proof, p. 8 (N'_i, quoting Shimura 1999, §8)"]
def shimuraCount (φ : Matrix (Fin n) (Fin n) 𝔬) (i : ℕ) : ℕ :=
  Nat.card {x : Matrix (Fin n) (Fin n) (𝔬 ⧸ Ideal.span {NF.π v ^ i}) //
    xᵀ * φ.map (Ideal.Quotient.mk _) * x = φ.map (Ideal.Quotient.mk _)}

/-- **Shimura's local factor** $e_\mathfrak p(\varphi) = \lim_iq^{-i\,n(n-1)/2}N'_i$ (Hanke thesis, Lemma 3.2, p. 8, quoting
[Shi, §8]). *Erratum (thesis text):* the definition is printed with $q^{-n(n-1)/2}$; the exponent is $-i\,n(n-1)/2$, as
in the proof of Lemma 3.2. -/
@[kb "hanke2005crelle" "Lemma 3.2, p. 8 (e_p, quoting Shimura 1999, §8)"]
def shimuraE (φ : Matrix (Fin n) (Fin n) 𝔬) : ℝ :=
  limUnder atTop fun i : ℕ => (shimuraCount v φ i : ℝ) / (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2))

theorem f3_isUnit_det_of_congr {i d : ℕ} (φ : Matrix (Fin n) (Fin n) 𝔬) (hd : NF.π v ^ d ∣ φ.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ φ.det) (hi : d < i) (X : Matrix (Fin n) (Fin n) 𝔬)
    (h : (X.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ i})))ᵀ * φ.map (Ideal.Quotient.mk _) * X.map (Ideal.Quotient.mk _) =
      φ.map (Ideal.Quotient.mk _)) : IsUnit X.det := by
  have hπ := NF.irreducible_π v
  have h0 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h0
  have h1 : Ideal.Quotient.mk (Ideal.span {NF.π v ^ i}) (X.det * X.det * φ.det) =
      Ideal.Quotient.mk (Ideal.span {NF.π v ^ i}) φ.det := by
    have e : ∀ M : Matrix (Fin n) (Fin n) 𝔬, Ideal.Quotient.mk (Ideal.span {NF.π v ^ i}) M.det =
        (M.map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ i}))).det := fun M => RingHom.map_det _ M
    rw [map_mul, map_mul, e, e]
    linear_combination h0
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨u, hu, hu1⟩ := DVR.dvr_exact hπ hd hd'
  have h2 : NF.π v ^ d * NF.π v ^ (i - d) ∣ NF.π v ^ d * (u * (X.det * X.det - 1)) := by
    rw [← pow_add, show d + (i - d) = i by omega]
    convert h1 using 1
    rw [hu]; ring
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero d hπ.ne_zero)).mp h2
  have h4 : NF.π v ∣ u * (X.det * X.det - 1) :=
    (dvd_pow_self _ (by omega : i - d ≠ 0)).trans h3
  have hpr := hπ.prime
  rcases hpr.dvd_or_dvd h4 with h5 | h5
  · exact absurd h5 (DVR.dvr_not_dvd_of_isUnit hπ hu1)
  · apply DVR.dvr_isUnit_of_not_dvd hπ
    intro h6
    have : NF.π v ∣ X.det * X.det := dvd_mul_of_dvd_left h6 _
    exact hπ.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_sub this h5))

theorem f3_entry_iff {i : ℕ} (φ : Matrix (Fin n) (Fin n) 𝔬) (x : Matrix (Fin n) (Fin n) Fv) (hx : x ∈ intM v) :
    (∀ a b, Valued.v ((xᵀ * φ.map (algebraMap 𝔬 Fv) * x - φ.map (algebraMap 𝔬 Fv)) a b) ≤ exp (-(i : ℤ))) ↔
      (redM v i x hx)ᵀ * φ.map (Ideal.Quotient.mk _) * redM v i x hx = φ.map (Ideal.Quotient.mk _) := by
  set Xo := toOM v x hx
  have hxo : x = Xo.map (algebraMap 𝔬 Fv) := (map_toOM v x hx).symm
  have e1 : xᵀ * φ.map (algebraMap 𝔬 Fv) * x - φ.map (algebraMap 𝔬 Fv) =
      (Xoᵀ * φ * Xo - φ).map (algebraMap 𝔬 Fv) := by
    have : ∀ M : Matrix (Fin n) (Fin n) 𝔬, M.map (algebraMap 𝔬 Fv) = (algebraMap 𝔬 Fv).mapMatrix M := fun _ => rfl
    rw [hxo, ← Matrix.transpose_map]
    simp only [this, map_sub, map_mul]
  have e2 : (redM v i x hx)ᵀ * φ.map (Ideal.Quotient.mk _) * redM v i x hx =
      (Xoᵀ * φ * Xo).map (Ideal.Quotient.mk (Ideal.span {NF.π v ^ i})) := by
    simp [redM, Xo, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2]
  constructor
  · intro h
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, NF.mem_span_π_pow]
    have := h a b
    simpa [Matrix.map_apply] using this
  · intro h a b
    have := congrFun (congrFun h a) b
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq, NF.mem_span_π_pow] at this
    simpa [Matrix.map_apply] using this

theorem f3_gramFiber_eq {d i : ℕ} (φ : Matrix (Fin n) (Fin n) 𝔬) (hd : NF.π v ^ d ∣ φ.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ φ.det) (hi : d < i) :
    gramFiber v (std v) (φ.map (algebraMap 𝔬 Fv)) i =
      ⋃ Y ∈ {Y : Matrix (Fin n) (Fin n) (LocalZeta.RQ v i) | Yᵀ * φ.map (Ideal.Quotient.mk _) * Y =
        φ.map (Ideal.Quotient.mk _)}, fiberM v i Y := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨hs, hv⟩
    obtain ⟨hx, -⟩ := (stabLat_std_iff v x).mp hs
    exact ⟨redM v i x hx, (f3_entry_iff v φ x hx).mp hv, (mem_fiberM_iff v).mpr ⟨hx, rfl⟩⟩
  · rintro ⟨Y, hY, hxY⟩
    obtain ⟨hx, rfl⟩ := (mem_fiberM_iff v).mp hxY
    refine ⟨(stabLat_std_iff v x).mpr ⟨hx, ?_⟩, (f3_entry_iff v φ x hx).mpr hY⟩
    have hu := f3_isUnit_det_of_congr v φ hd hd' hi (toOM v x hx) hY
    rw [← det_toOM v x hx]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hu

open Classical in
theorem f3_gramRatio_eq {d i : ℕ} (φ : Matrix (Fin n) (Fin n) 𝔬) (hd : NF.π v ^ d ∣ φ.det)
    (hd' : ¬ NF.π v ^ (d + 1) ∣ φ.det) (hi : d < i) :
    gramRatio v (std v) (φ.map (algebraMap 𝔬 Fv)) i =
      (shimuraCount v φ i : ℝ) / (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2)) := by
  have hfin := DVR.finite_quot_pow (NF.π v) (NF.irreducible_π v) i
  let _ : Fintype (LocalZeta.RQ v i) := Fintype.ofFinite _
  have hset : gramFiber v (std v) (φ.map (algebraMap 𝔬 Fv)) i =
      ⋃ Y ∈ (Finset.univ.filter fun Y : Matrix (Fin n) (Fin n) (LocalZeta.RQ v i) =>
        Yᵀ * φ.map (Ideal.Quotient.mk _) * Y = φ.map (Ideal.Quotient.mk _)), fiberM v i Y := by
    rw [f3_gramFiber_eq v φ hd hd' hi]
    ext x; simp
  have hvol : volM v (gramFiber v (std v) (φ.map (algebraMap 𝔬 Fv)) i) =
      (shimuraCount v φ i : ℝ≥0∞) * Analysis.haarV v (Analysis.latticeV v (i : ℤ)) ^ (n * n) := by
    rw [hset, measure_biUnion_finset]
    · simp only [volM_fiberM, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [shimuraCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
    · intro Y _ Y' _ h
      exact fiberM_disjoint v h
    · intro Y _; exact measurableSet_fiberM v i Y
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast LocalZeta.q_pos v
  rw [gramRatio, hvol, haarV_latticeV_nat, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have h2 : (DVR.q 𝔬 : ℝ) ^ (i * (n * (n + 1) / 2)) * (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2)) =
      ((DVR.q 𝔬 : ℝ) ^ i) ^ (n * n) := by
    rw [← pow_add, ← mul_add, two_mul_choose, pow_mul]
  have key : (DVR.q 𝔬 : ℝ) ^ (i * (n * (n + 1) / 2)) * (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2)) *
      (((DVR.q 𝔬 : ℝ) ^ i)⁻¹ ^ (n * n)) = 1 := by
    rw [h2, ← mul_pow, mul_inv_cancel₀ (pow_pos hq _).ne', one_pow]
  rw [eq_div_iff (pow_pos hq _).ne']
  calc _ = (shimuraCount v φ i : ℝ) * ((DVR.q 𝔬 : ℝ) ^ (i * (n * (n + 1) / 2)) *
        (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2)) * (((DVR.q 𝔬 : ℝ) ^ i)⁻¹ ^ (n * n))) := by ring
    _ = _ := by rw [key, mul_one]

theorem f3_limUnder_eq {f : ℕ → ℝ} {L : ℝ} (h : ∀ᶠ i in atTop, f i = L) : limUnder atTop f = L :=
  (tendsto_const_nhds.congr' (h.mono fun _ h => h.symm)).limUnder_eq

/-- **Lemma 3.2** (Hanke thesis, p. 8): if $\Lambda_\mathfrak p = \sum_i\mathcal O_\mathfrak pv_i$ (here: $\mathfrak o_v^n$ in the
basis $e_i$), then $\beta_\mathfrak p(\Lambda_\mathfrak p,\varphi) = \tfrac12e_\mathfrak p(\varphi)$.
*Update (hypothesis):* $\varphi$ must be integral for $N'_i$ to be defined (Hanke applies the lemma to $2\varphi_\mathfrak p$,
which is integral); it is also symmetric and nondegenerate (it represents $(V_\mathfrak p,\varphi_\mathfrak p)$). -/
@[kb "hanke2005crelle" "Lemma 3.2, p. 8"]
theorem hankeBeta_std_eq_half_shimuraE {φ : Matrix (Fin n) (Fin n) 𝔬} (hφ : φᵀ = φ) (hdet : φ.det ≠ 0) :
    hankeBeta v (std v) (φ.map (algebraMap 𝔬 Fv)) = (1 / 2 : ℝ) * shimuraE v φ := by
  have hπ := NF.irreducible_π v
  obtain ⟨d, hd, hd'⟩ := DVR.exists_pow_dvd_not_dvd (NF.π v) hπ hdet
  have hsym : (φ.map (algebraMap 𝔬 Fv))ᵀ = φ.map (algebraMap 𝔬 Fv) := by
    rw [← Matrix.transpose_map, hφ]
  have hdet' : (φ.map (algebraMap 𝔬 Fv)).det ≠ 0 := by
    have : (φ.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv φ.det := (RingHom.map_det _ φ).symm
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hdet
  have h1 := gramRatio_std_eventually_eq v hsym hdet'
  have h2 : ∀ᶠ i in atTop, (shimuraCount v φ i : ℝ) / (DVR.q 𝔬 : ℝ) ^ (i * (n * (n - 1) / 2)) =
      2 * hankeBeta v (std v) (φ.map (algebraMap 𝔬 Fv)) := by
    filter_upwards [h1, eventually_gt_atTop d] with i hi hdi
    rw [← f3_gramRatio_eq v φ hd hd' hdi]; exact hi
  have : shimuraE v φ = 2 * hankeBeta v (std v) (φ.map (algebraMap 𝔬 Fv)) := f3_limUnder_eq h2
  rw [this]; ring

/-- **(3.2)** (Hanke thesis, p. 8): $\beta_\mathfrak p(\varphi_\mathfrak p) = |\det(2\cdot1_n)|_\mathfrak p^{(n+1)/2}\,
e_\mathfrak p(2\varphi_\mathfrak p)/2$ for $\Lambda_\mathfrak p = \mathfrak o_v^n$, whenever $2\varphi_\mathfrak p$ is integral and
nondegenerate (Lemmas 3.1 and 3.2 with $c = 2$). Here $\varphi_\mathfrak p$ is any symmetric matrix over $F_v$ with
$2\varphi_\mathfrak p = \psi$ integral. -/
@[kb "hanke2005crelle" "(3.2), p. 8"]
theorem hankeBeta_std_eq_two {ψ : Matrix (Fin n) (Fin n) 𝔬} (hψ : ψᵀ = ψ) (hdet : ψ.det ≠ 0)
    {φ : Matrix (Fin n) (Fin n) Fv} (hφ : (2 : Fv) • φ = ψ.map (algebraMap 𝔬 Fv)) :
    hankeBeta v (std v) φ = ‖((2 : Fv) • (1 : Matrix (Fin n) (Fin n) Fv)).det‖ ^ (((n : ℝ) + 1) / 2) *
      shimuraE v ψ / 2 := by
  have h2 : (2 : Fv) ≠ 0 := two_ne_zero
  have hsym : φᵀ = φ := by
    have h : (2 : Fv) • φᵀ = (2 : Fv) • φ := by
      rw [← Matrix.transpose_smul, hφ, ← Matrix.transpose_map, hψ]
    exact smul_right_injective _ h2 h
  have hdetψ : (ψ.map (algebraMap 𝔬 Fv)).det ≠ 0 := by
    have : (ψ.map (algebraMap 𝔬 Fv)).det = algebraMap 𝔬 Fv ψ.det := (RingHom.map_det _ ψ).symm
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective 𝔬 Fv)).mpr hdet
  have hdetφ : φ.det ≠ 0 := by
    intro h0
    apply hdetψ
    rw [← hφ, Matrix.det_smul, h0, mul_zero]
  rw [hankeBeta_std_smul v hsym hdetφ h2, hφ, hankeBeta_std_eq_half_shimuraE v hψ hdet]
  have hN : ((n * (n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) * (((n : ℝ) + 1) / 2) := by
    have := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self n)
    have h : (2 : ℝ) * ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) := by exact_mod_cast this
    linarith
  have hn : ‖((2 : Fv) • (1 : Matrix (Fin n) (Fin n) Fv)).det‖ ^ (((n : ℝ) + 1) / 2) =
      ‖(2 : Fv)‖ ^ (n * (n + 1) / 2) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, norm_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast ‖(2 : Fv)‖ (n * (n + 1) / 2), hN]
  rw [hn]; ring

theorem f2_mul_intM {A B : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intM v) (hB : B ∈ intM v) :
    A * B ∈ intM v := by
  intro i j
  have := valued_mul_apply_le v (a := 1) (b := 1) (fun i j => hA i j) (fun i j => hB i j) i j
  simpa using this

theorem f2_mul_bound {A M B : Matrix (Fin n) (Fin n) Fv} (hA : A ∈ intM v) (hB : B ∈ intM v) {i : ℕ}
    (hM : ∀ a b, Valued.v (M a b) ≤ exp (-(i : ℤ))) : ∀ a b, Valued.v ((A * M * B) a b) ≤ exp (-(i : ℤ)) := by
  intro a b
  have := valued_mul_apply_le v (valued_mul_apply_le v (fun i j => hA i j) hM) (fun i j => hB i j) a b
  simpa using this

def f2_conjEquiv (g : Matrix (Fin n) (Fin n) Fv) (h1 : g * g⁻¹ = 1) (h2 : g⁻¹ * g = 1) :
    Matrix (Fin n) (Fin n) Fv ≃ᵐ Matrix (Fin n) (Fin n) Fv where
  toFun X := g * X * g⁻¹
  invFun X := g⁻¹ * X * g
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  measurable_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  measurable_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable

theorem f2_conj_mem (U : Matrix (Fin n) (Fin n) 𝔬) (hU : IsUnit U.det) (φ : Matrix (Fin n) (Fin n) Fv)
    (i : ℕ) (x : Matrix (Fin n) (Fin n) Fv) :
    x ∈ gramFiber v (std v) ((U.map (algebraMap 𝔬 Fv))ᵀ * φ * U.map (algebraMap 𝔬 Fv)) i ↔
      (U.map (algebraMap 𝔬 Fv)) * x * (U.map (algebraMap 𝔬 Fv))⁻¹ ∈ gramFiber v (std v) φ i := by
  set u : Matrix (Fin n) (Fin n) Fv := U.map (algebraMap 𝔬 Fv) with hu_def
  have hu : u ∈ intM v := fun a b => (U a b).2
  have hdu : Valued.v u.det = 1 := by
    have : u.det = ((U.det : 𝔬) : Fv) := (RingHom.map_det (algebraMap 𝔬 Fv) U).symm
    rw [this]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hU
  have hui : u⁻¹ ∈ intM v := inv_mem_intM v hu hdu
  have hdet0 : u.det ≠ 0 := by intro h0; rw [h0, map_zero] at hdu; simp at hdu
  have hdetU : IsUnit u.det := isUnit_iff_ne_zero.mpr hdet0
  have h1 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
  have h4 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ hdetU
  have h2 : (u⁻¹)ᵀ * uᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : uᵀ * (u⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, h4, Matrix.transpose_one]
  have huT : uᵀ ∈ intM v := fun a b => hu b a
  have huiT : (u⁻¹)ᵀ ∈ intM v := fun a b => hui b a
  have hφ : (u⁻¹)ᵀ * (uᵀ * φ * u) * u⁻¹ = φ := by
    calc _ = ((u⁻¹)ᵀ * uᵀ) * φ * (u * u⁻¹) := by simp only [Matrix.mul_assoc]
      _ = φ := by rw [h2, h1, Matrix.one_mul, Matrix.mul_one]
  have e1 : (u * x * u⁻¹)ᵀ * φ * (u * x * u⁻¹) = (u⁻¹)ᵀ * (xᵀ * (uᵀ * φ * u) * x) * u⁻¹ := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have e2 : (u * x * u⁻¹)ᵀ * φ * (u * x * u⁻¹) - φ =
      (u⁻¹)ᵀ * (xᵀ * (uᵀ * φ * u) * x - uᵀ * φ * u) * u⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hφ, ← e1]
  have e3 : xᵀ * (uᵀ * φ * u) * x - uᵀ * φ * u =
      uᵀ * ((u * x * u⁻¹)ᵀ * φ * (u * x * u⁻¹) - φ) * u := by
    rw [e2]
    calc _ = (uᵀ * (u⁻¹)ᵀ) * (xᵀ * (uᵀ * φ * u) * x - uᵀ * φ * u) * (u⁻¹ * u) := by
          rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hdy : (u * x * u⁻¹).det = x.det := by
    have : u.det * u⁻¹.det = 1 := by rw [← Matrix.det_mul, h1, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul]
    calc _ = x.det * (u.det * u⁻¹.det) := by ring
      _ = _ := by rw [this, mul_one]
  simp only [gramFiber, Set.mem_ofPred_eq]
  rw [stabLat_std_iff, stabLat_std_iff, hdy]
  constructor
  · rintro ⟨⟨hx, hd⟩, hg⟩
    refine ⟨⟨f2_mul_intM v (f2_mul_intM v hu hx) hui, hd⟩, ?_⟩
    rw [e2]
    exact f2_mul_bound v huiT hui hg
  · rintro ⟨⟨hy, hd⟩, hg⟩
    have hx : x ∈ intM v := by
      have := f2_mul_intM v (f2_mul_intM v hui hy) hu
      have e : u⁻¹ * (u * x * u⁻¹) * u = x := by
        simp only [Matrix.mul_assoc]
        rw [h4, Matrix.mul_one, ← Matrix.mul_assoc, h4, Matrix.one_mul]
      rwa [e] at this
    refine ⟨⟨hx, hd⟩, ?_⟩
    rw [e3]
    exact f2_mul_bound v huT hu hg

/-- **Invariance under $\mathrm{GL}_n(\mathfrak o_v)$** (the case $|\det A|_v = 1$ of Lemma 2.2, p. 6): a change of basis of
$\mathfrak o_v^n$ does not change $\beta_\mathfrak p(\mathfrak o_v^n,\cdot)$. -/
@[kb "hanke2005crelle" "Lemma 2.2, p. 6 (case A ∈ GL_n(O_p))"]
theorem hankeBeta_std_congr_unit (φ : Matrix (Fin n) (Fin n) Fv) {U : Matrix (Fin n) (Fin n) 𝔬}
    (hU : IsUnit U.det) :
    hankeBeta v (std v) ((U.map (algebraMap 𝔬 Fv))ᵀ * φ * U.map (algebraMap 𝔬 Fv)) = hankeBeta v (std v) φ := by
  set u : Matrix (Fin n) (Fin n) Fv := U.map (algebraMap 𝔬 Fv) with hu_def
  have hu : u ∈ intM v := fun a b => (U a b).2
  have hdu : Valued.v u.det = 1 := by
    have : u.det = ((U.det : 𝔬) : Fv) := (RingHom.map_det (algebraMap 𝔬 Fv) U).symm
    rw [this]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).mp hU
  have hdet0 : u.det ≠ 0 := by intro h0; rw [h0, map_zero] at hdu; simp at hdu
  have hdetU : IsUnit u.det := isUnit_iff_ne_zero.mpr hdet0
  have h1 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
  have h4 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ hdetU
  let e := f2_conjEquiv v u h1 h4
  have hmp : MeasurePreserving e (volM v) (volM v) := measurePreserving_conjM v hu hdu
  have key : ∀ i, gramFiber v (std v) (uᵀ * φ * u) i = e ⁻¹' gramFiber v (std v) φ i := by
    intro i; ext x
    exact f2_conj_mem v U hU φ i x
  have hseq : gramRatio v (std v) (uᵀ * φ * u) = gramRatio v (std v) φ := by
    funext i
    unfold gramRatio
    rw [key, hmp.measure_preimage_emb e.measurableEmbedding]
  unfold hankeBeta
  rw [hseq]

/-- **Comparison with the repository's local density** (coefficient coordinates): for a nondegenerate form $Q$ over
$\mathfrak o_v$ with Gram matrix $\varphi = \tfrac12H_Q$,
$$\beta_\mathfrak p(\mathfrak o_v^n,\varphi) = |2|_v^{n(n-1)/2}\,\alpha_\mathfrak p(Q,Q),\qquad
\alpha_\mathfrak p = \tfrac12\beta^{\mathrm{coef}}_\mathfrak p = \text{`DVR.siegelDensity Q Q π`}.$$
The factor $|2|_v^{n(n-1)/2}$ is the Jacobian of $t_{ij}\mapsto c_{ij} = 2t_{ij}$ ($i<j$); it is $1$ unless $v\mid2$. -/
@[kb "hanke2005crelle" "(2.8), p. 5; (3.1), p. 7 (Gram versus coefficient normalization)"]
theorem hankeBeta_std_hessian (Q : QuadForm 𝔬 n) (hQ : Q.hessian.det ≠ 0) :
    hankeBeta v (std v) (gramOf v Q) = ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) * DVR.siegelDensity Q Q (NF.π v) := by
  obtain ⟨I, hI⟩ := core_gramRatio_eventually v Q hQ
  have hev : ∀ᶠ i in atTop, gramRatio v (std v) (gramOf v Q) i =
      ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) * DVR.localDensityForm Q Q (NF.π v) :=
    (eventually_ge_atTop I).mono fun i hi => hI i hi
  unfold hankeBeta DVR.siegelDensity
  rw [f2_limUnder_eq_of_eventually_eq hev, if_pos rfl]
  ring

/-- The comparison for a global form $Q_0$ over $\mathcal O_F$ (`NF.siegelDensity`, the repository's $\alpha_\mathfrak p$). -/
theorem hankeBeta_gramV (Q₀ : QuadForm (𝓞 F) n) (hQ : Q₀.Nondegenerate) :
    hankeBeta v (std v) (gramOf v (NF.Qp v Q₀)) = ‖(2 : Fv)‖ ^ (n * (n - 1) / 2) * NF.siegelDensity v Q₀ Q₀ := by
  rw [hankeBeta_std_hessian v (NF.Qp v Q₀) (NF.nondegenerate_Qp v hQ)]
  unfold NF.siegelDensity DVR.siegelDensity
  rw [NF.localDensityForm_eq_completion]

end QuadFormsKB.Hanke2005
