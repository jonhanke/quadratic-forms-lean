import QuadFormsKB.Tamagawa.Measure.Weil.AdditiveScaling

/-!
# Adelic Minkowski

Weil, *Adeles and Algebraic Groups* (1982), §2.1 (the measure of $\mathbb A_k/k$)
(adelic Minkowski drives the finiteness for $\mathrm{SL}_2$ and Fujisaki's lemma).

**Generic part** (namespace `MeasureTheory`, imports only Mathlib material; upstreamable):
* `exists_ne_zero_mem_of_sub_mem` (Blichfeldt, difference form): if $\mu(S) > \mu(D)$ for a fundamental domain $D$ of a
  countable subgroup $L$, and $S - S\subseteq C$, then $C$ contains a nonzero point of $L$.
* `exists_ne_zero_map_mem_of_sub_mem`: the same after an additive measurable map $T$ with $T_*\mu = c\,\mu$
  ($\mu(T^{-1}S) = c\,\mu(S)$); this is the form "for every $g$ with bounded modulus there is $0\ne\xi$ with
  $g\xi\in C$".
* `exists_ne_zero_mem_prod_of_measure_lt` (Minkowski for $E\times K$): $E$ a finite-dimensional real space, $K$ any
  measurable additive group, $C\subseteq E$ convex symmetric, $H\le K$ a subgroup; if
  $\mu(D)\,2^{\dim E} < \mu_E(C)\,\nu(H)$ then $C\times H$ meets $L\setminus 0$. Twisted version
  `exists_ne_zero_map_mem_prod_of_measure_lt`.

**Adelic part** ($F$ any number field, $V = F$, $F^\iota$, $\mathbb H[F,a,b]$ through coordinates; the self-dual
measures, covolume $1$):
* `adelicBlichfeldt`: $\mu(S) > 1$ ⇒ $S - S$ contains a nonzero $\xi\in F^\iota$.
* **`adelicMinkowski`**: $C_\infty\subseteq F_\infty^\iota$ convex symmetric, $H\le\mathbb A_f^\iota$ a subgroup,
  $2^{n} < \mu_\infty(C_\infty)\,\mu_f(H)$ with $n = |\iota|\,[F:\mathbb Q]$ ⇒ $0\ne\xi\in F^\iota$ with $\xi\in C_\infty\times H$.
* **`adelicMinkowski_smul`**: for $g\in(\mathbb A_F^\iota)^\times$ with $2^n\|N g\| < \mu_\infty(C_\infty)\mu_f(H)$ there is
  $0\ne\xi$ with $g\xi\in C_\infty\times H$; **`exists_isCompact_forall_smul_mem`**: for every $M$ there is a compact
  $\mathcal C$ such that every $g$ with $\|N g\|\le M$ has $g\xi\in\mathcal C$ for some $0\ne\xi\in F^\iota$.
* $A = F$ directly on `Adeles F`: `adelicMinkowski_idele`, `exists_isCompact_forall_idele_smul_mem` (the input to the
  compactness of $\mathbb A^1/F^\times$).
* $A = \mathbb H[F,a,b]$: `adelicMinkowski_quat` (untwisted; the twisted form needs the scaling by
  $(\mathbb H\otimes\mathbb A)^\times$).
-/

open MeasureTheory Module NumberField NumberField.mixedEmbedding IsDedekindDomain Filter Topology
open scoped Pointwise ENNReal NNReal Classical Quaternion

namespace MeasureTheory

section Generic

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] {μ : Measure E}

/-- **Blichfeldt, difference form.** If `D` is a fundamental domain of a countable subgroup `L`, `μ D < μ S` and every
difference of two points of `S` lies in `C`, then `C` contains a nonzero point of `L`. -/
theorem exists_ne_zero_mem_of_sub_mem {L : AddSubgroup E} [Countable L] [MeasurableConstVAdd L E]
    [VAddInvariantMeasure L E μ] {D S C : Set E} (fund : IsAddFundamentalDomain L D μ)
    (hS : NullMeasurableSet S μ) (h : μ D < μ S) (hSC : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ C) :
    ∃ ξ : L, ξ ≠ 0 ∧ (ξ : E) ∈ C := by
  let _ : MeasurableSpace L := ⊤
  have : MeasurableVAdd L E :=
    { measurable_const_vadd := fun c => measurable_const_vadd c
      measurable_vadd_const := fun _ => measurable_from_top }
  obtain ⟨x, y, hxy, hd⟩ := exists_pair_mem_lattice_not_disjoint_vadd fund hS h
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := Set.not_disjoint_iff.mp hd
  refine ⟨x - y, sub_ne_zero.2 hxy, ?_⟩
  have hvw' : (y : E) + w = (x : E) + v := hvw
  have : ((x - y : L) : E) = w - v := by
    rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, add_comm w]; exact hvw'.symm
  rw [this]; exact hSC w hw v hv

/-- **Blichfeldt after a scaling map.** If `T : E →+ E` is measurable with `T_* μ = c • μ`, `S` is measurable with
`μ D < c * μ S` and `S - S ⊆ C`, then `T ξ ∈ C` for some nonzero `ξ ∈ L`. -/
theorem exists_ne_zero_map_mem_of_sub_mem {L : AddSubgroup E} [Countable L] [MeasurableConstVAdd L E]
    [VAddInvariantMeasure L E μ] {D S C : Set E} (fund : IsAddFundamentalDomain L D μ)
    (T : E →+ E) (hT : Measurable T) {c : ℝ≥0∞} (hTμ : Measure.map T μ = c • μ)
    (hS : MeasurableSet S) (h : μ D < c * μ S) (hSC : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ C) :
    ∃ ξ : L, ξ ≠ 0 ∧ T ξ ∈ C := by
  have hmeas : μ (T ⁻¹' S) = c * μ S := by
    rw [← Measure.map_apply hT hS, hTμ, Measure.smul_apply, smul_eq_mul]
  obtain ⟨ξ, hξ, hξC⟩ := exists_ne_zero_mem_of_sub_mem (C := T ⁻¹' C) fund
    (hT hS).nullMeasurableSet (by rwa [hmeas]) (fun x hx y hy => by
      show T (x - y) ∈ C
      rw [map_sub]; exact hSC _ hx _ hy)
  exact ⟨ξ, hξ, hξC⟩

/-- Differences of points of `½ C` lie in `C`, for `C` convex and symmetric. -/
theorem sub_mem_of_mem_inv_two_smul {V : Type*} [AddCommGroup V] [Module ℝ V] {C : Set V}
    (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C) {x y : V} (hx : x ∈ (2⁻¹ : ℝ) • C)
    (hy : y ∈ (2⁻¹ : ℝ) • C) : x - y ∈ C := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [sub_eq_add_neg, ← smul_neg]
  exact h_conv ha (h_symm b hb) (by norm_num) (by norm_num) (by norm_num)

section Half
variable {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] {μV : Measure V} [μV.IsAddHaarMeasure]
  [AddCommGroup K] [MeasurableSpace K] {ν : Measure K} [SFinite ν]

omit [AddCommGroup K] in
/-- `μ_V(½ C) ν(H) = 2^{-n} μ_V(C) ν(H)` and the resulting strict inequality. -/
theorem lt_measure_half_prod {C : Set V} {H : Set K} {a : ℝ≥0∞}
    (h : a * 2 ^ finrank ℝ V < μV C * ν H) :
    a < (μV.prod ν) (((2⁻¹ : ℝ) • C) ×ˢ H) := by
  rw [Measure.prod_prod, Measure.addHaar_smul_of_nonneg μV (by norm_num : (0 : ℝ) ≤ 2⁻¹),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat,
    mul_assoc]
  have h2 : (2 : ℝ≥0∞) ^ finrank ℝ V ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ finrank ℝ V ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [← ENNReal.inv_pow, ← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl h2) (Or.inl h2')]
  exact h

omit [AddCommGroup K] in
/-- The twisted form of `lt_measure_half_prod`: `a 2^n < c μ_V(C) ν(H)` gives `a < c (μ_V × ν)(½C × H)`. -/
theorem lt_mul_measure_half_prod {C : Set V} {H : Set K} {a c : ℝ≥0∞}
    (h : a * 2 ^ finrank ℝ V < c * (μV C * ν H)) :
    a < c * (μV.prod ν) (((2⁻¹ : ℝ) • C) ×ˢ H) := by
  rw [Measure.prod_prod, Measure.addHaar_smul_of_nonneg μV (by norm_num : (0 : ℝ) ≤ 2⁻¹),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
  have h2 : (2 : ℝ≥0∞) ^ finrank ℝ V ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2' : (2 : ℝ≥0∞) ^ finrank ℝ V ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [show c * ((2⁻¹ : ℝ≥0∞) ^ finrank ℝ V * μV C * ν H) = c * (μV C * ν H) / 2 ^ finrank ℝ V by
    rw [← ENNReal.inv_pow, ENNReal.div_eq_inv_mul]; ring,
    ENNReal.lt_div_iff_mul_lt (Or.inl h2) (Or.inl h2')]
  exact h

/-- **Minkowski on `V × K`.** `V` a finite-dimensional real space with Haar measure, `K` a measurable additive group,
`L ≤ V × K` countable with fundamental domain `D` for `μ_V × ν`. If `C ⊆ V` is convex and symmetric, `H ≤ K` is a
null-measurable subgroup and `μ(D) 2^{dim V} < μ_V(C) ν(H)`, then `C × H` contains a nonzero point of `L`. -/
theorem exists_ne_zero_mem_prod_of_measure_lt {L : AddSubgroup (V × K)} [Countable L]
    [MeasurableConstVAdd L (V × K)] [VAddInvariantMeasure L (V × K) (μV.prod ν)] {D : Set (V × K)}
    (fund : IsAddFundamentalDomain L D (μV.prod ν)) {C : Set V} (h_symm : ∀ x ∈ C, -x ∈ C)
    (h_conv : Convex ℝ C) (H : AddSubgroup K) (hH : NullMeasurableSet (H : Set K) ν)
    (h : (μV.prod ν) D * 2 ^ finrank ℝ V < μV C * ν H) :
    ∃ ξ : L, ξ ≠ 0 ∧ (ξ : V × K) ∈ C ×ˢ (H : Set K) := by
  refine exists_ne_zero_mem_of_sub_mem fund (((h_conv.smul _).nullMeasurableSet (μ := μV)).prod hH)
    (lt_measure_half_prod h) ?_
  rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
  exact ⟨sub_mem_of_mem_inv_two_smul h_symm h_conv hx₁ hy₁, H.sub_mem hx₂ hy₂⟩

/-- **Twisted Minkowski on `V × K`.** As `exists_ne_zero_mem_prod_of_measure_lt`, after a measurable additive map `T`
with `T_* μ = c • μ`: if `μ(D) 2^{dim V} < c μ_V(C) ν(H)` (`C`, `H` measurable), then `T ξ ∈ C × H` for some
nonzero `ξ ∈ L`. -/
theorem exists_ne_zero_map_mem_prod_of_measure_lt {L : AddSubgroup (V × K)} [Countable L]
    [MeasurableConstVAdd L (V × K)] [VAddInvariantMeasure L (V × K) (μV.prod ν)] {D : Set (V × K)}
    (fund : IsAddFundamentalDomain L D (μV.prod ν)) (T : V × K →+ V × K) (hT : Measurable T)
    {c : ℝ≥0∞} (hTμ : Measure.map T (μV.prod ν) = c • μV.prod ν) {C : Set V}
    (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C) (hC : MeasurableSet C) (H : AddSubgroup K)
    (hH : MeasurableSet (H : Set K)) (h : (μV.prod ν) D * 2 ^ finrank ℝ V < c * (μV C * ν H)) :
    ∃ ξ : L, ξ ≠ 0 ∧ T ξ ∈ C ×ˢ (H : Set K) := by
  have hC2 : MeasurableSet ((2⁻¹ : ℝ) • C) :=
    hC.const_smul_of_ne_zero (by norm_num)
  refine exists_ne_zero_map_mem_of_sub_mem fund T hT hTμ (hC2.prod hH) (lt_mul_measure_half_prod h) ?_
  · rintro ⟨x₁, x₂⟩ ⟨hx₁, hx₂⟩ ⟨y₁, y₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨sub_mem_of_mem_inv_two_smul h_symm h_conv hx₁ hy₁, H.sub_mem hx₂ hy₂⟩

end Half

end Generic

end MeasureTheory

namespace MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V] (μV : Measure V) [μV.IsAddHaarMeasure]

/-- Large balls have large measure: for `0 < b < ∞` and `a < ∞` there is `R > 0` with `a < μ(B(0,R)) b`
(`dim V ≥ 1`). -/
theorem exists_lt_measure_closedBall_mul (hn : 0 < finrank ℝ V) {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb0 : b ≠ 0)
    (hbt : b ≠ ⊤) : ∃ R : ℝ, 0 < R ∧ a < μV (Metric.closedBall (0 : V) R) * b := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hn
  set k := μV (Metric.closedBall (0 : V) 1) * b with hk
  have hk0 : k ≠ 0 := mul_ne_zero (Metric.measure_closedBall_pos μV 0 one_pos).ne' hb0
  have hkt : k ≠ ⊤ := ENNReal.mul_ne_top measure_closedBall_lt_top.ne hbt
  set R : ℝ := (a / k).toReal + 1
  have hR1 : 1 ≤ R := by
    have : 0 ≤ (a / k).toReal := ENNReal.toReal_nonneg
    simp only [R]; linarith
  refine ⟨R, by linarith, ?_⟩
  rw [Measure.addHaar_closedBall' μV 0 (by linarith : (0 : ℝ) ≤ R), mul_assoc, ← hk]
  have hRn : (a / k).toReal < R ^ finrank ℝ V :=
    (lt_add_one _).trans_le (le_self_pow₀ hR1 hn.ne')
  have h1 : a / k < ENNReal.ofReal (R ^ finrank ℝ V) :=
    (ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.div_ne_top ha hk0)).mpr hRn
  calc a = a / k * k := (ENNReal.div_mul_cancel hk0 hkt).symm
    _ < ENNReal.ofReal (R ^ finrank ℝ V) * k := ENNReal.mul_lt_mul_left hk0 hkt h1

end MeasureTheory

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

variable {F : Type} [Field F] [NumberField F]

local notation "AF" => FiniteAdeleRing (𝓞 F) F

set_option synthInstance.maxHeartbeats 400000

/-! ### $A = F$: Minkowski on $\mathbb A_F = F_\infty\times\mathbb A_f$ -/

instance : MeasurableConstVAdd (diagSub F) (Adeles F) := AddSubgroup.instMeasurableConstVAdd _

instance : VAddInvariantMeasure (diagSub F) (Adeles F) ((Analysis.selfDualInf (F := F)).prod (muFin F)) :=
  inferInstanceAs (VAddInvariantMeasure (diagSub F).toAddSubmonoid (Adeles F)
    ((Analysis.selfDualInf (F := F)).prod (muFin F)))

/-- $\hat{\mathcal O}$ as an additive subgroup of $\mathbb A_f$. -/
def OHatSub : AddSubgroup AF where
  carrier := OHat
  zero_mem' := zero_mem_OHat
  add_mem' := add_mem_OHat
  neg_mem' := neg_mem_OHat

@[simp] theorem coe_OHatSub : ((OHatSub (F := F) : AddSubgroup AF) : Set AF) = OHat := rfl

theorem finrank_mixedSpace_pos : 0 < finrank ℝ (mixedSpace F) := by
  rw [mixedEmbedding.finrank]; exact Module.finrank_pos

private theorem exists_of_mem_diagSub {P : Adeles F → Prop} {ξ : diagSub F} (hξ : ξ ≠ 0) (hP : P ξ) :
    ∃ x : F, x ≠ 0 ∧ P (diag F x) := by
  obtain ⟨_, x, rfl⟩ := ξ
  refine ⟨x, fun h0 => hξ ?_, hP⟩
  subst h0; exact Subtype.ext (map_zero _)

/-- **Adelic Minkowski for $F$.** If $C\subseteq F_\infty$ is convex and symmetric, $H\le\mathbb A_f$ is a (null-measurable)
subgroup and $2^{[F:\mathbb Q]} < \mu_\infty(C)\,\mu_f(H)$ (self-dual measures, $\operatorname{vol}(\mathbb A_F/F) = 1$), then
some $0\ne\xi\in F$ has $\xi\in C\times H$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_F {C : Set (mixedSpace F)} (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C)
    (H : AddSubgroup AF) (hH : NullMeasurableSet (H : Set AF) (muFin F))
    (h : 2 ^ finrank ℚ F < Analysis.selfDualInf C * muFin F H) :
    ∃ ξ : F, ξ ≠ 0 ∧ diag F ξ ∈ C ×ˢ (H : Set AF) := by
  obtain ⟨ξ, hne, hmem⟩ := exists_ne_zero_mem_prod_of_measure_lt (L := diagSub F)
    (isAddFundamentalDomain_fundDom ((Analysis.selfDualInf (F := F)).prod (muFin F))) h_symm h_conv H hH
    (by
      change muAdd F (fundDom F) * _ < _
      rwa [muAdd_fundDom, one_mul, mixedEmbedding.finrank])
  exact exists_of_mem_diagSub hne hmem

/-- The strict inequality after scaling by $\|g\|^{-1}$. -/
private theorem lt_ofReal_inv_mul {n : ℕ} {N : ℝ} (hN : 0 < N) {X : ℝ≥0∞}
    (h : 2 ^ n * ENNReal.ofReal N < X) : 1 * 2 ^ n < ENNReal.ofReal N⁻¹ * X := by
  rw [one_mul, ENNReal.ofReal_inv_of_pos hN, ← ENNReal.div_eq_inv_mul,
    ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.mpr hN).ne') (Or.inl ENNReal.ofReal_ne_top)]
  exact h

/-- **Twisted adelic Minkowski for $F$ (ideles).** For $g\in\mathbb A_F^\times$, $C\subseteq F_\infty$ convex symmetric
measurable and $H\le\mathbb A_f$ a measurable subgroup with $2^{[F:\mathbb Q]}\,\|g\|_{\mathbb A} < \mu_\infty(C)\,\mu_f(H)$,
some $0\ne\xi\in F$ has $g\xi\in C\times H$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_idele (g : (Adeles F)ˣ) {C : Set (mixedSpace F)} (h_symm : ∀ x ∈ C, -x ∈ C)
    (h_conv : Convex ℝ C) (hC : MeasurableSet C) (H : AddSubgroup AF) (hH : MeasurableSet (H : Set AF))
    (h : 2 ^ finrank ℚ F * ENNReal.ofReal (ideleNorm F g) < Analysis.selfDualInf C * muFin F H) :
    ∃ ξ : F, ξ ≠ 0 ∧ g • diag F ξ ∈ C ×ˢ (H : Set AF) := by
  have hT : Measurable (AddMonoidHom.mulLeft (g : Adeles F)) :=
    (continuous_const.mul continuous_id).measurable
  obtain ⟨ξ, hne, hmem⟩ := exists_ne_zero_map_mem_prod_of_measure_lt (L := diagSub F)
    (isAddFundamentalDomain_fundDom ((Analysis.selfDualInf (F := F)).prod (muFin F)))
    (AddMonoidHom.mulLeft (g : Adeles F)) hT (map_smul_muAdd g) h_symm h_conv hC H hH
    (by
      change muAdd F (fundDom F) * _ < _
      rw [muAdd_fundDom, mixedEmbedding.finrank]
      exact lt_ofReal_inv_mul (ideleNorm_pos g) h)
  exact exists_of_mem_diagSub (P := fun x => g • x ∈ C ×ˢ (H : Set AF)) hne hmem

/-- **Idelic Minkowski, compact form.** For every $M$ there is a compact $\mathcal C\subseteq\mathbb A_F$ such that every
idele $g$ with $\|g\|_{\mathbb A}\le M$ has $g\xi\in\mathcal C$ for some $0\ne\xi\in F$. (This is the input to the
compactness of $\mathbb A_F^1/F^\times$.) -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem exists_isCompact_forall_idele_smul_mem (M : ℝ) :
    ∃ K : Set (Adeles F), IsCompact K ∧
      ∀ g : (Adeles F)ˣ, ideleNorm F g ≤ M → ∃ ξ : F, ξ ≠ 0 ∧ g • diag F ξ ∈ K := by
  obtain ⟨R, hR, hlt⟩ := exists_lt_measure_closedBall_mul (Analysis.selfDualInf (F := F))
    finrank_mixedSpace_pos (a := 2 ^ finrank ℚ F * ENNReal.ofReal M) (b := muFin F OHat)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top)
    muFin_OHat_ne_zero muFin_OHat_ne_top
  refine ⟨Metric.closedBall 0 R ×ˢ OHat, (isCompact_closedBall _ _).prod isCompact_OHat,
    fun g hg => ?_⟩
  refine adelicMinkowski_idele g (fun x hx => by simpa using hx) (convex_closedBall _ _)
    Metric.isClosed_closedBall.measurableSet OHatSub measurableSet_OHat (lt_of_le_of_lt ?_ hlt)
  gcongr

/-! ### $A = F^\iota$: Minkowski on $\mathbb A_F^\iota$ -/

section Vec

set_option synthInstance.maxHeartbeats 400000

variable {ι : Type} [Fintype ι]

instance borelSpace_infVec : BorelSpace (ι → mixedSpace F) := Pi.borelSpace

instance measurableAdd_mixedSpace : MeasurableAdd (mixedSpace F) := ContinuousAdd.measurableAdd

instance isAddHaarMeasure_muInfVec :
    (Measure.pi fun _ : ι => Analysis.selfDualInf (F := F)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

variable (F) in
/-- The self-dual measure $\mu_\infty^\iota$ on $F_\infty^\iota$. -/
abbrev muInfVec (ι : Type) [Fintype ι] : Measure (ι → mixedSpace F) :=
  Measure.pi fun _ : ι => Analysis.selfDualInf (F := F)

variable (F) in
/-- The self-dual measure $\mu_f^\iota$ on $\mathbb A_f^\iota$. -/
abbrev muFinVec (ι : Type) [Fintype ι] : Measure (ι → AF) := Measure.pi fun _ : ι => muFin F

/-- The set $C_\infty\times H\subseteq\mathbb A_F^\iota$: archimedean components in $C_\infty\subseteq F_\infty^\iota$, finite
components in $H\subseteq\mathbb A_f^\iota$. -/
def boxSet (C : Set (ι → mixedSpace F)) (H : Set (ι → AF)) : Set (AdeleSpace F ι) :=
  MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι ⁻¹' (C ×ˢ H)

omit [Fintype ι] in
theorem mem_boxSet {C : Set (ι → mixedSpace F)} {H : Set (ι → AF)} {x : AdeleSpace F ι} :
    x ∈ boxSet C H ↔ (fun i => (x i).1) ∈ C ∧ (fun i => (x i).2) ∈ H := Iff.rfl

theorem measurePreserving_arrowProd :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι) (muAddVec F ι)
      ((muInfVec F ι).prod (muFinVec F ι)) :=
  measurePreserving_arrowProdEquivProdArrow _ _ ι (fun _ => Analysis.selfDualInf) (fun _ => muFin F)

/-- $\mu(C_\infty\times H) = \mu_\infty^\iota(C_\infty)\,\mu_f^\iota(H)$. -/
theorem muAddVec_boxSet (C : Set (ι → mixedSpace F)) (H : Set (ι → AF)) :
    muAddVec F ι (boxSet C H) = muInfVec F ι C * muFinVec F ι H := by
  rw [boxSet, ← MeasurableEquiv.map_apply, (measurePreserving_arrowProd (F := F) (ι := ι)).map_eq,
    Measure.prod_prod]

theorem finrank_infVec : finrank ℝ (ι → mixedSpace F) = Fintype.card ι * finrank ℚ F := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, mixedEmbedding.finrank]

omit [Fintype ι] in
private theorem exists_of_mem_diagVecSub {P : AdeleSpace F ι → Prop} {ξ : diagVecSub F ι} (hξ : ξ ≠ 0)
    (hP : P ξ) : ∃ x : ι → F, x ≠ 0 ∧ P (diagVec F ι x) := by
  obtain ⟨_, x, rfl⟩ := ξ
  refine ⟨x, fun h0 => hξ ?_, hP⟩
  subst h0; exact Subtype.ext (map_zero _)

/-- **Adelic Blichfeldt for $V = F^\iota$.** If $S\subseteq\mathbb A_F^\iota$ has self-dual measure $> 1 =
\operatorname{vol}(\mathbb A_F^\iota/F^\iota)$, then $S - S$ contains a nonzero $\xi\in F^\iota$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicBlichfeldt {S : Set (AdeleSpace F ι)} (hS : NullMeasurableSet S (muAddVec F ι))
    (h : 1 < muAddVec F ι S) : ∃ ξ : ι → F, ξ ≠ 0 ∧ ∃ x ∈ S, ∃ y ∈ S, x - y = diagVec F ι ξ := by
  obtain ⟨ξ, hne, hmem⟩ := exists_ne_zero_mem_of_sub_mem (C := S - S)
    (isAddFundamentalDomain_fundDomVec (muAddVec F ι)) hS (by rwa [muAddVec_fundDomVec])
    (fun x hx y hy => Set.sub_mem_sub hx hy)
  exact exists_of_mem_diagVecSub (P := fun z => ∃ x ∈ S, ∃ y ∈ S, x - y = z) hne hmem

/-- **Adelic Minkowski for $V = F^\iota$.** Let $C_\infty\subseteq F_\infty^\iota$ be convex and symmetric and
$H\le\mathbb A_f^\iota$ a null-measurable subgroup (e.g. an open compact one). If
$2^{|\iota|[F:\mathbb Q]} < \mu_\infty^\iota(C_\infty)\,\mu_f^\iota(H)$ (self-dual measures, covolume $1$), then some
$0\ne\xi\in F^\iota$ lies in $C_\infty\times H$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski {C : Set (ι → mixedSpace F)} (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C)
    (H : AddSubgroup (ι → AF)) (hH : NullMeasurableSet (H : Set (ι → AF)) (muFinVec F ι))
    (h : 2 ^ (Fintype.card ι * finrank ℚ F) < muInfVec F ι C * muFinVec F ι H) :
    ∃ ξ : ι → F, ξ ≠ 0 ∧ diagVec F ι ξ ∈ boxSet C (H : Set (ι → AF)) := by
  have hS : NullMeasurableSet (boxSet ((2⁻¹ : ℝ) • C) (H : Set (ι → AF))) (muAddVec F ι) :=
    (((h_conv.smul _).nullMeasurableSet (μ := muInfVec F ι)).prod hH).preimage
      (measurePreserving_arrowProd (F := F) (ι := ι)).quasiMeasurePreserving
  obtain ⟨ξ, hne, hmem⟩ := exists_ne_zero_mem_of_sub_mem (C := boxSet C (H : Set (ι → AF)))
    (isAddFundamentalDomain_fundDomVec (muAddVec F ι)) hS
    (by
      rw [muAddVec_fundDomVec, muAddVec_boxSet, ← Measure.prod_prod]
      exact lt_measure_half_prod (by rwa [one_mul, finrank_infVec]))
    (fun x hx y hy => ⟨sub_mem_of_mem_inv_two_smul h_symm h_conv hx.1 hy.1, H.sub_mem hx.2 hy.2⟩)
  exact exists_of_mem_diagVecSub (P := fun z => z ∈ boxSet C (H : Set (ι → AF))) hne hmem

/-- **Twisted adelic Minkowski for $V = F^\iota$** (the form used for finiteness and Fujisaki). For
$g\in(F^\iota\otimes\mathbb A)^\times$ with $2^{|\iota|[F:\mathbb Q]}\,\|N_{A/F}(g)\|_{\mathbb A} <
\mu_\infty^\iota(C_\infty)\,\mu_f^\iota(H)$ ($C_\infty$ convex symmetric measurable, $H$ a measurable subgroup), some
$0\ne\xi\in F^\iota$ has $g\xi\in C_\infty\times H$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_smul (g : (AdeleSpace F ι)ˣ) {C : Set (ι → mixedSpace F)}
    (h_symm : ∀ x ∈ C, -x ∈ C) (h_conv : Convex ℝ C) (hC : MeasurableSet C) (H : AddSubgroup (ι → AF))
    (hH : MeasurableSet (H : Set (ι → AF)))
    (h : 2 ^ (Fintype.card ι * finrank ℚ F) * ENNReal.ofReal (ideleNormVec g) <
      muInfVec F ι C * muFinVec F ι H) :
    ∃ ξ : ι → F, ξ ≠ 0 ∧ g • diagVec F ι ξ ∈ boxSet C (H : Set (ι → AF)) := by
  have hT : Measurable (AddMonoidHom.mulLeft (g : AdeleSpace F ι)) :=
    (continuous_const.mul continuous_id).measurable
  have hC2 : MeasurableSet ((2⁻¹ : ℝ) • C) := hC.const_smul_of_ne_zero (by norm_num)
  have hS : MeasurableSet (boxSet ((2⁻¹ : ℝ) • C) (H : Set (ι → AF))) :=
    (MeasurableEquiv.arrowProdEquivProdArrow (mixedSpace F) AF ι).measurable (hC2.prod hH)
  obtain ⟨ξ, hne, hmem⟩ := exists_ne_zero_map_mem_of_sub_mem (C := boxSet C (H : Set (ι → AF)))
    (isAddFundamentalDomain_fundDomVec (muAddVec F ι)) (AddMonoidHom.mulLeft (g : AdeleSpace F ι)) hT
    (map_smul_muAddVec g) hS
    (by
      rw [muAddVec_fundDomVec, muAddVec_boxSet, ← Measure.prod_prod]
      exact lt_mul_measure_half_prod (by rw [finrank_infVec]; exact lt_ofReal_inv_mul (ideleNormVec_pos g) h))
    (fun x hx y hy => ⟨sub_mem_of_mem_inv_two_smul h_symm h_conv hx.1 hy.1, H.sub_mem hx.2 hy.2⟩)
  exact exists_of_mem_diagVecSub (P := fun z => g • z ∈ boxSet C (H : Set (ι → AF))) hne hmem

/-- **Adelic Minkowski for $F^\iota$, compact form** (the form used for $\mathrm{SL}_2$-finiteness and Fujisaki). For every
$M$ there is a compact $\mathcal C\subseteq\mathbb A_F^\iota$ such that every $g\in(F^\iota\otimes\mathbb A)^\times$ with
$\|N_{A/F}(g)\|_{\mathbb A}\le M$ has $g\xi\in\mathcal C$ for some $0\ne\xi\in F^\iota$ ($\iota$ nonempty). -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem exists_isCompact_forall_smul_mem [Nonempty ι] (M : ℝ) :
    ∃ K : Set (AdeleSpace F ι), IsCompact K ∧
      ∀ g : (AdeleSpace F ι)ˣ, ideleNormVec g ≤ M → ∃ ξ : ι → F, ξ ≠ 0 ∧ g • diagVec F ι ξ ∈ K := by
  have hn : 0 < finrank ℝ (ι → mixedSpace F) := by
    rw [finrank_infVec]; exact Nat.mul_pos Fintype.card_pos Module.finrank_pos
  set H : AddSubgroup (ι → AF) := AddSubgroup.pi Set.univ fun _ => OHatSub
  have hHcoe : (H : Set (ι → AF)) = Set.univ.pi fun _ => OHat := by
    ext x; simp [H, AddSubgroup.mem_pi]; rfl
  have hHm : MeasurableSet (H : Set (ι → AF)) := by
    rw [hHcoe]; exact MeasurableSet.univ_pi fun _ => measurableSet_OHat
  have hHvol : muFinVec F ι H = ∏ _i : ι, muFin F OHat := by
    rw [hHcoe, Measure.pi_pi]
  have hH0 : muFinVec F ι H ≠ 0 := by
    rw [hHvol]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => muFin_OHat_ne_zero
  have hHt : muFinVec F ι H ≠ ⊤ := by
    rw [hHvol]; exact ENNReal.prod_ne_top fun _ _ => muFin_OHat_ne_top
  obtain ⟨R, hR, hlt⟩ := exists_lt_measure_closedBall_mul (muInfVec F ι) hn
    (a := 2 ^ (Fintype.card ι * finrank ℚ F) * ENNReal.ofReal M)
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top) hH0 hHt
  refine ⟨Set.univ.pi fun _ => Metric.closedBall (0 : mixedSpace F) R ×ˢ OHat,
    isCompact_univ_pi fun _ => (isCompact_closedBall _ _).prod isCompact_OHat, fun g hg => ?_⟩
  obtain ⟨ξ, hξ, hmem⟩ := adelicMinkowski_smul g (fun x hx => by simpa using hx) (convex_closedBall _ _)
    Metric.isClosed_closedBall.measurableSet H hHm (lt_of_le_of_lt (by gcongr) hlt)
  refine ⟨ξ, hξ, fun i _ => ⟨?_, ?_⟩⟩
  · have h1 := hmem.1
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (norm_le_pi_norm (fun i => ((g • diagVec F ι ξ) i).1) i).trans h1
  · have h2 := hmem.2
    rw [hHcoe] at h2
    exact h2 i (Set.mem_univ i)

/-- **Adelic Minkowski for $A = \mathbb H[F,a,b]$** (coordinates $1,i,j,k$, coordinate self-dual measure, covolume $1$):
under the hypotheses of `adelicMinkowski` with $\iota = \mathrm{Fin}\,4$, some $0\ne x\in\mathbb H[F,a,b]$ lies in
$C_\infty\times H$. -/
@[kb "weil1982" "§2.1 [unverified page]"]
theorem adelicMinkowski_quat (a b : F) {C : Set (Fin 4 → mixedSpace F)} (h_symm : ∀ x ∈ C, -x ∈ C)
    (h_conv : Convex ℝ C) (H : AddSubgroup (Fin 4 → AF))
    (hH : NullMeasurableSet (H : Set (Fin 4 → AF)) (muFinVec F (Fin 4)))
    (h : 2 ^ (Fintype.card (Fin 4) * finrank ℚ F) < muInfVec F (Fin 4) C * muFinVec F (Fin 4) H) :
    ∃ x : ℍ[F,a,b], x ≠ 0 ∧ diagQuat a b x ∈ boxSet C (H : Set (Fin 4 → AF)) := by
  obtain ⟨ξ, hξ, hmem⟩ := adelicMinkowski h_symm h_conv H hH h
  refine ⟨(QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm ξ, ?_, ?_⟩
  · exact fun h0 => hξ ((LinearEquiv.map_eq_zero_iff _).mp h0)
  · change diagVec F (Fin 4) ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b)
      ((QuaternionAlgebra.linearEquivTuple (R := F) a 0 b).symm ξ)) ∈ _
    rwa [LinearEquiv.apply_symm_apply]

end Vec
