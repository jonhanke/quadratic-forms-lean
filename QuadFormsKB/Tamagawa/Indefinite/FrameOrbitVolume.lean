/-
# The volume of an orbit of integral frames

**Layer:** abstract group and measure theory. $G = A\times B$ ($A = G_\infty$, $B = G_f$) acts on $Y_A\times Y_B$ with base
point $(a_0, b_0)$, $H = A'\times B'$, $\iota = \iota_A\times\iota_B$, orbit coordinates $C$ (stabilizer $\iota(H)$) with
Weil's fibration $\mu_A\otimes\mu_B = C_*(\sigma\otimes(\mu_{A'}\otimes\mu_{B'}))$, $\mu_{B'}$ right invariant. This file
computes the part of $\sigma$ over one $K$-orbit $O = K\,g_Ob_0$ of $Y_B$ ($K\le B$ a subgroup, e.g. $SO(\hat L)$):

* `measure_fibreB`: $\mu_{B'}\{h : \iota_B(h)c\in g_O^{-1}K\} = \mu_{B'}(K_O)$ if $c^{-1}b_0\in O$, else $0$, with
  $K_O = \iota_B^{-1}(g_O^{-1}Kg_O)$ (`orbitStab`);
* **`measure_prod_orbit`**: for measurable $X\subseteq A$,
  $\mu_A(X)\,\mu_B(K) = \int\mu_{A'}\{h : \iota_A(h)\,C(p,1)_A\in X\}\cdot1_O(\tau(p)_B)\,\mu_{B'}(K_O)\,d\sigma(p)$;
* **`map_restrict_orbit`**: with the archimedean factor $C_A$ (`OrbitCoord.fstFactor`) and a measure $\sigma_A$ with
  $\mu_A = C_{A*}(\sigma_A\otimes\mu_{A'})$, the archimedean projection of $\sigma$ over $O$ is
  $$\pi_*(\sigma|_{\tau_B\in O}) = \frac{\mu_B(K)}{\mu_{B'}(K_O)}\,\sigma_A.$$

So the adelic measure of a set of frames with integrality conditions at the finite places is the archimedean measure
times a sum over the orbits of $\mu_B(K)/\mu_{B'}(K_O)$; no local measure on frame varieties is needed.
-/
import QuadFormsKB.Tamagawa.Indefinite.FrameCoordCompose

open MeasureTheory Set MulAction
open scoped ENNReal Pointwise
open Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Indefinite

open QuadFormsKB.Tamagawa.Measure.Weil

section Fibre

variable {B B' : Type*} [Group B] [Group B'] [MeasurableSpace B'] [MeasurableMul B'] {YB : Type*} [MulAction B YB]
  {ιB : B' →* B} {b₀ : YB}

/-- **The stabilizer of the orbit** $K_O = \iota_B^{-1}(g_O^{-1}Kg_O)$ in $B'$. -/
def orbitStab (ιB : B' →* B) (K : Subgroup B) (gO : B) : Subgroup B' := (K.comap (MulAut.conj gO).toMonoidHom).comap ιB

theorem mem_orbitStab {K : Subgroup B} {gO : B} {h : B'} : h ∈ orbitStab ιB K gO ↔ gO * ιB h * gO⁻¹ ∈ K := by
  simp [orbitStab, MulAut.conj_apply]

/-- **The fibre over one orbit** (group theory): if $\iota_B(B')$ fixes $b_0$ and is its full stabilizer, then
$\{h : \iota_B(h)\,c\in g_O^{-1}K\}$ is a right translate of $K_O$ when $c^{-1}b_0\in Kg_Ob_0$ and is empty otherwise. -/
theorem measure_fibreB (hfix : ∀ h : B', ιB h • b₀ = b₀) (hst : ∀ g : B, g • b₀ = b₀ → ∃ h, ιB h = g)
    (μB' : Measure B') [μB'.IsMulRightInvariant] (K : Subgroup B) (gO c : B) :
    μB' {h : B' | ιB h * c ∈ gO⁻¹ • (K : Set B)} =
      if c⁻¹ • b₀ ∈ (K : Set B) • ({gO • b₀} : Set YB) then μB' (orbitStab ιB K gO) else 0 := by
  split_ifs with hc
  · obtain ⟨k, hk, y, hy, hky⟩ := Set.mem_smul.1 hc
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hfx : ((k * gO)⁻¹ * c⁻¹) • b₀ = b₀ := by
      rw [mul_smul, ← hky, ← mul_smul k gO b₀, inv_smul_smul]
    obtain ⟨h₁, hh₁⟩ := hst _ hfx
    have hset : {h : B' | ιB h * c ∈ gO⁻¹ • (K : Set B)} =
        (fun h => h * h₁⁻¹) ⁻¹' (orbitStab ιB K gO : Set B') := by
      ext h
      have hc' : c = (ιB h₁)⁻¹ * gO⁻¹ * k⁻¹ := by
        rw [hh₁]; group
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, mem_orbitStab, mem_leftCoset_iff,
        inv_inv, map_mul, map_inv]
      rw [hc']
      have : gO * (ιB h * ((ιB h₁)⁻¹ * gO⁻¹ * k⁻¹)) = (gO * (ιB h * (ιB h₁)⁻¹) * gO⁻¹) * k⁻¹ := by
        group
      rw [this]
      exact mul_mem_cancel_right (K.inv_mem hk)
    rw [hset]
    exact measure_preimage_mul_right μB' h₁⁻¹ _
  · have : {h : B' | ιB h * c ∈ gO⁻¹ • (K : Set B)} = ∅ := by
      ext h
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hmem
      obtain ⟨k, hk, hkk⟩ := Set.mem_smul_set.1 hmem
      apply hc
      refine Set.mem_smul.2 ⟨k⁻¹, K.inv_mem hk, gO • b₀, rfl, ?_⟩
      have hc' : c⁻¹ = (ιB h * c)⁻¹ * ιB h := by group
      rw [hc', ← hkk]
      simp only [smul_eq_mul]
      rw [mul_smul, hfix]
      rw [mul_inv_rev, inv_inv, mul_smul]
    rw [this]; simp

end Fibre

variable {A B A' B' : Type*} [Group A] [Group B] [Group A'] [Group B']
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B']
  [MeasurableMul A] [MeasurableMul B] [MeasurableMul A'] [MeasurableMul B']
  {YA YB : Type*} [MulAction A YA] [MulAction B YB] [MeasurableSpace YA]
  {T : Type*} [MeasurableSpace T] {ιA : A' →* A} {ιB : B' →* B} {τ : T → YA × YB} {a₀ : YA} {b₀ : YB}

theorem fix_iotaB (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) (h : B') : ιB h • b₀ = b₀ :=
  congrArg Prod.snd (C.iota_smul_base (1, h))

theorem stab_iotaB (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (g : B) (hg : g • b₀ = b₀) :
    ∃ h, ιB h = g := by
  obtain ⟨h, hh⟩ := hst ((1 : A), g) (Prod.ext (one_smul _ _) hg)
  exact ⟨h.2, congrArg Prod.snd hh⟩

/-- $\tau(p)_B = C(p,1)_B^{-1}b_0$. -/
theorem τ_snd_eq (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) (p : T) :
    (τ p).2 = ((C.coord (p, 1)).2)⁻¹ • b₀ := by
  rw [← C.orbit p 1]; rfl

/-- **The measure of a box over one orbit**: for measurable $X\subseteq A$ and a measurable subgroup $K\le B$,
$$\mu_A(X)\,\mu_B(K) = \int\mu_{A'}\{h : \iota_A(h)\,C(p,1)_A\in X\}\cdot1_{O}(\tau(p)_B)\,\mu_{B'}(K_O)\,d\sigma(p),
  \qquad O = Kg_Ob_0.$$ -/
theorem measure_prod_orbit (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (μA : Measure A) (μB : Measure B) (μA' : Measure A')
    (μB' : Measure B') (σ : Measure T) [SFinite μA] [SFinite μB] [SFinite μA'] [SFinite μB'] [SFinite σ]
    [μB.IsMulLeftInvariant] [μB'.IsMulRightInvariant]
    (hfib : μA.prod μB = (σ.prod (μA'.prod μB')).map C.coord) (K : Subgroup B) (hK : MeasurableSet (K : Set B))
    (gO : B) {X : Set A} (hX : MeasurableSet X) :
    μA X * μB K = ∫⁻ p, μA' {h | ιA h * (C.coord (p, 1)).1 ∈ X} *
      (if (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) then μB' (orbitStab ιB K gO) else 0) ∂σ := by
  have hS : MeasurableSet (gO⁻¹ • (K : Set B)) := hK.const_smul gO⁻¹
  have h1 : μA X * μB K = (μA.prod μB) (X ×ˢ (gO⁻¹ • (K : Set B))) := by
    rw [Measure.prod_prod, measure_smul]
  have hm : MeasurableSet (X ×ˢ (gO⁻¹ • (K : Set B))) := hX.prod hS
  rw [h1, hfib, Measure.map_apply C.coord.measurable hm, Measure.prod_apply (C.coord.measurable hm)]
  refine lintegral_congr fun p => ?_
  have hset : Prod.mk p ⁻¹' (C.coord ⁻¹' (X ×ˢ (gO⁻¹ • (K : Set B)))) =
      {h | ιA h * (C.coord (p, 1)).1 ∈ X} ×ˢ {h | ιB h * (C.coord (p, 1)).2 ∈ gO⁻¹ • (K : Set B)} := by
    ext ⟨u, v⟩
    simp only [mem_preimage, mem_prod, mem_setOf_eq]
    rw [C.coord_eq p (u, v)]
    rfl
  rw [hset, Measure.prod_prod, measure_fibreB (fix_iotaB C) (stab_iotaB hst) μB' K gO, ← τ_snd_eq C p]

/-- The archimedean point of a parameter, in the archimedean parameter space $T_A = A\,a_0$. -/
def projA (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀)) [MeasurableSpace YB] (p : T) : factorT τ b₀ :=
  ⟨(τ p).1, (C.coord.symm ((C.coord (p, 1)).1, 1)).1, by
    rw [τ_symm_eq C, ← C.orbit p 1]; rfl⟩

variable [MeasurableSpace YB]

/-- **The archimedean projection of $\sigma$ over one orbit** (the adelic measure of frames over a $K$-orbit is the
archimedean quotient measure times $\mu_B(K)/\mu_{B'}(K_O)$): for orbit coordinates $C_A$ of the archimedean factor with
$\mu_A = C_{A*}(\sigma_A\otimes\mu_{A'})$, $\mu_{A'}$ right invariant, and $0 < \mu_{B'}(K_O) < \infty$,
$$\pi_*(\sigma|_{\{\tau_B\in Kg_Ob_0\}}) = \frac{\mu_B(K)}{\mu_{B'}(K_O)}\,\sigma_A.$$ -/
theorem map_restrict_orbit (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (μA : Measure A) (μB : Measure B) (μA' : Measure A')
    (μB' : Measure B') (σ : Measure T) [SFinite μA] [SFinite μB] [SFinite μA'] [SFinite μB'] [SFinite σ]
    [μB.IsMulLeftInvariant] [μA'.IsMulRightInvariant] [μB'.IsMulRightInvariant]
    (hfib : μA.prod μB = (σ.prod (μA'.prod μB')).map C.coord)
    (CA : OrbitCoord ιA (Subtype.val : factorT τ b₀ → YA) a₀) (σA : Measure (factorT τ b₀)) [SFinite σA]
    (hA : μA = (σA.prod μA').map CA.coord) (hπ : Measurable (projA C))
    (K : Subgroup B) (hK : MeasurableSet (K : Set B)) (gO : B)
    (hO : MeasurableSet {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)})
    (hKO : μB' (orbitStab ιB K gO) ≠ 0) (hKO' : μB' (orbitStab ιB K gO) ≠ ∞)
    (hU : ∃ U : Set A', MeasurableSet U ∧ μA' U ≠ 0 ∧ μA' U ≠ ∞) :
    (σ.restrict {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)}).map (projA C) =
      (μB K / μB' (orbitStab ιB K gO)) • σA := by
  obtain ⟨U, hUm, hU0, hUt⟩ := hU
  ext S hS
  have hXm : MeasurableSet (CA.coord '' (S ×ˢ U)) := CA.coord.measurableSet_image.2 (hS.prod hUm)
  have hμX : μA (CA.coord '' (S ×ˢ U)) = σA S * μA' U := by
    rw [hA, Measure.map_apply CA.coord.measurable hXm, MeasurableEquiv.preimage_image, Measure.prod_prod]
  have slice : ∀ p, μA' {h | ιA h * (C.coord (p, 1)).1 ∈ CA.coord '' (S ×ˢ U)} =
      S.indicator (fun _ => μA' U) (projA C p) := by
    intro p
    set y := projA C p with hy
    set c := (C.coord (p, 1)).1 with hc
    have hc1 : c⁻¹ • a₀ = (τ p).1 := congrArg Prod.fst (C.orbit p 1)
    have hc2 : (CA.coord (y, 1))⁻¹ • a₀ = (τ p).1 := CA.orbit y 1
    have hg : (CA.coord (y, 1) * c⁻¹) • a₀ = a₀ := by
      rw [mul_smul, hc1, ← hc2, smul_inv_smul]
    obtain ⟨h, hh⟩ := hst ((CA.coord (y, 1) * c⁻¹), 1) (Prod.ext hg (one_smul _ _))
    have hh1 : ιA h.1 = CA.coord (y, 1) * c⁻¹ := congrArg Prod.fst hh
    have hcc : c = (ιA h.1)⁻¹ * CA.coord (y, 1) := by rw [hh1]; group
    have hset : {h' | ιA h' * c ∈ CA.coord '' (S ×ˢ U)} =
        (fun h' => h' * h.1⁻¹) ⁻¹' {h' | CA.coord (y, h') ∈ CA.coord '' (S ×ˢ U)} := by
      ext h'
      have : ιA h' * c = CA.coord (y, h' * h.1⁻¹) := by
        rw [CA.coord_eq y (h' * h.1⁻¹), hcc, map_mul, map_inv, mul_assoc]
      simp only [mem_setOf_eq, mem_preimage]
      rw [this]
    rw [hset, measure_preimage_mul_right]
    by_cases hyS : y ∈ S
    · have : {h' | CA.coord (y, h') ∈ CA.coord '' (S ×ˢ U)} = U := by
        ext h'
        simp only [mem_setOf_eq]
        rw [CA.coord.injective.mem_set_image]
        simp [hyS]
      rw [this, Set.indicator_of_mem hyS]
    · have : {h' | CA.coord (y, h') ∈ CA.coord '' (S ×ˢ U)} = ∅ := by
        ext h'
        simp only [mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [CA.coord.injective.mem_set_image]
        simp [hyS]
      rw [this, Set.indicator_of_notMem hyS]
      simp
  have hmain := measure_prod_orbit C hst μA μB μA' μB' σ hfib K hK gO hXm
  rw [hμX] at hmain
  simp_rw [slice] at hmain
  have hint : (fun p => S.indicator (fun _ => μA' U) (projA C p) *
      (if (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) then μB' (orbitStab ιB K gO) else 0)) =
      (projA C ⁻¹' S ∩ {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)}).indicator
        (fun _ => μA' U * μB' (orbitStab ιB K gO)) := by
    funext p
    by_cases h1 : projA C p ∈ S <;> by_cases h2 : (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB) <;>
      simp only [Set.indicator_apply, mem_inter_iff, mem_preimage, mem_setOf_eq, h1, h2, true_and, and_true,
        and_false, false_and, if_true, if_false, mul_zero, zero_mul, ↓reduceIte]
  rw [hint, lintegral_indicator_const ((hπ hS).inter hO)] at hmain
  rw [Measure.map_apply hπ hS, Measure.restrict_apply (hπ hS), Measure.smul_apply, smul_eq_mul]
  have hdm : μB K / μB' (orbitStab ιB K gO) * σA S = μB K * σA S / μB' (orbitStab ιB K gO) := by
    simp only [ENNReal.div_eq_inv_mul]; ring
  rw [hdm, ENNReal.eq_div_iff hKO hKO']
  have : μA' U * (μB' (orbitStab ιB K gO) * σ (projA C ⁻¹' S ∩ {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)})) =
      μA' U * (μB K * σA S) := by
    calc _ = μA' U * μB' (orbitStab ιB K gO) * σ (projA C ⁻¹' S ∩ {p | (τ p).2 ∈ (K : Set B) • ({gO • b₀} : Set YB)}) := by ring
      _ = σA S * μA' U * μB K := hmain.symm
      _ = _ := by ring
  exact (ENNReal.mul_right_inj hU0 hUt).1 this

/-- **The integral of a test function with an integrality condition, as a sum over orbits**: if the points of the
$B$-orbit of $b_0$ in $\Lambda\subseteq Y_B$ are the disjoint union of the countably many $K$-orbits $Kg_ib_0$, then for
measurable $\Phi\ge0$ on $Y_A$,
$$\int\Phi(\tau(p)_A)\,1_\Lambda(\tau(p)_B)\,d\sigma(p) = \sum_i\frac{\mu_B(K)}{\mu_{B'}(K_{O_i})}\int\Phi\,d\sigma_A.$$ -/
theorem lintegral_testFn_orbits (C : OrbitCoord (MonoidHom.prodMap ιA ιB) τ (a₀, b₀))
    (hst : StabIn (MonoidHom.prodMap ιA ιB) (a₀, b₀)) (μA : Measure A) (μB : Measure B) (μA' : Measure A')
    (μB' : Measure B') (σ : Measure T) [SFinite μA] [SFinite μB] [SFinite μA'] [SFinite μB'] [SFinite σ]
    [μB.IsMulLeftInvariant] [μA'.IsMulRightInvariant] [μB'.IsMulRightInvariant]
    (hfib : μA.prod μB = (σ.prod (μA'.prod μB')).map C.coord)
    (CA : OrbitCoord ιA (Subtype.val : factorT τ b₀ → YA) a₀) (σA : Measure (factorT τ b₀)) [SFinite σA]
    (hA : μA = (σA.prod μA').map CA.coord) (hπ : Measurable (projA C))
    (K : Subgroup B) (hK : MeasurableSet (K : Set B)) {I : Type*} [Countable I] (g : I → B)
    (hO : ∀ i, MeasurableSet {p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)})
    (hKO : ∀ i, μB' (orbitStab ιB K (g i)) ≠ 0) (hKO' : ∀ i, μB' (orbitStab ιB K (g i)) ≠ ∞)
    (hU : ∃ U : Set A', MeasurableSet U ∧ μA' U ≠ 0 ∧ μA' U ≠ ∞)
    (Λ : Set YB) (hdisj : Pairwise fun i j => Disjoint ((K : Set B) • ({g i • b₀} : Set YB))
      ((K : Set B) • ({g j • b₀} : Set YB)))
    (hcov : ∀ p, (τ p).2 ∈ Λ ↔ ∃ i, (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB))
    (Φ : YA → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ p, Φ (τ p).1 * Λ.indicator 1 (τ p).2 ∂σ =
      ∑' i, (μB K / μB' (orbitStab ιB K (g i))) * ∫⁻ t, Φ t.1 ∂σA := by
  have hmap := fun i => map_restrict_orbit C hst μA μB μA' μB' σ hfib CA σA hA hπ K hK (g i) (hO i)
    (hKO i) (hKO' i) hU
  have hΦ' : Measurable fun t : factorT τ b₀ => Φ t.1 := hΦ.comp measurable_subtype_coe
  have hpt : ∀ p, Φ (τ p).1 * Λ.indicator 1 (τ p).2 =
      ∑' i, ({p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)}).indicator (fun p => Φ (projA C p).1) p := by
    intro p
    have hind : Λ.indicator (1 : YB → ℝ≥0∞) (τ p).2 =
        ∑' i, ({p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)}).indicator (1 : T → ℝ≥0∞) p := by
      by_cases hp : (τ p).2 ∈ Λ
      · obtain ⟨i, hi⟩ := (hcov p).1 hp
        rw [Set.indicator_of_mem hp, tsum_eq_single i]
        · rw [Set.indicator_of_mem (show p ∈ {p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)} from hi)]
          rfl
        · intro j hj
          have : p ∉ {p | (τ p).2 ∈ (K : Set B) • ({g j • b₀} : Set YB)} := fun hj' =>
            Set.disjoint_left.1 (hdisj (Ne.symm hj)) hi hj'
          rw [Set.indicator_of_notMem this]
      · rw [Set.indicator_of_notMem hp]
        symm
        refine ENNReal.tsum_eq_zero.2 fun i => ?_
        have : p ∉ {p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)} := fun h =>
          hp ((hcov p).2 ⟨i, h⟩)
        rw [Set.indicator_of_notMem this]
    rw [hind, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    by_cases h : p ∈ {p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      simp [projA]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  simp_rw [hpt]
  have hm : ∀ i, AEMeasurable (fun p => ({p | (τ p).2 ∈ (K : Set B) • ({g i • b₀} : Set YB)}).indicator
      (fun p => Φ (projA C p).1) p) σ := fun i => ((hΦ'.comp hπ).indicator (hO i)).aemeasurable
  rw [lintegral_tsum hm]
  refine tsum_congr fun i => ?_
  rw [lintegral_indicator (hO i)]
  refine ((lintegral_map hΦ' hπ).symm).trans ?_
  rw [hmap i, lintegral_smul_measure, smul_eq_mul]

end QuadFormsKB.Tamagawa.Indefinite
