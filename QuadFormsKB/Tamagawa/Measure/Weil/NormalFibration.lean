import QuadFormsKB.Tamagawa.Measure.Weil.OrbitFibration

/-!
# Haar measures fibred along a surjective homomorphism, without a section

**Generic, Mathlib-only hypotheses (upstreamable).** Let $N : G\to Q$ be a surjective measurable homomorphism onto a
group (commutative in the use; generalized to any $Q$, e.g. $PD^\times(\mathbb A)$), $K = \ker N$, $\mu_K$ a left-invariant measure on $K$ and $\mu_Q$ a left-invariant measure on $Q$.
Weil's measure on $G$ "fibred over $Q$ with fibre measure $\mu_K$" (Weil 1982, §2.4, Thm 2.4.4 [unverified page]) is
$$\nu(E) = \int_Q \mu_K\{k\in K : g_q k\in E\}\,d\mu_Q(q),\qquad N(g_q) = q,$$
and the inner integrand does not depend on the choice of $g_q$ in the coset $g_qK$ (left invariance of $\mu_K$).
Unlike `homSection`, **no measurable section of $N$ is needed**: the integrand is a $K$-invariant measurable
function of $g\in G$, and such a function descends to a measurable function on $Q$ as soon as $G$ is standard Borel
and $Q$ is countably separated (Mathlib's `Measurable.measurable_comp_iff_of_surjective`, a consequence of Suslin's
theorem). This matters for $\operatorname{nrd} : \mathbb H_{\mathbb A}^1\to\mathbb A^1_+$, where an explicit measurable
section through the restricted product is awkward.

Main results:
* **`NormalFib.fibMeas`** $=\nu$, as the Giry bind $\mu_Q\gg\!\!= \kappa$ with the kernel $\kappa(q) = (g_q\cdot)_*\mu_K$
  (`NormalFib.kern`, measurable by `NormalFib.measurable_kern`);
* **`NormalFib.isMulLeftInvariant_fibMeas`**: $\nu$ is left invariant;
* **`NormalFib.fibMeas_compact_lt_top`**: $\nu$ is finite on compact sets (topological groups, $\mu_K$, $\mu_Q$ finite on
  compacts), hence σ-finite;
* **`NormalFib.map_conj_fibMeas`**: conjugation by $g$ multiplies $\nu$ by the modulus $m$ of $\operatorname{Ad}(g)$ on $K$;
  **`NormalFib.map_adK_eq_of_conj`**: if $\nu$ is conjugation invariant then $\operatorname{Ad}(g)_*\mu_K = \mu_K$;
* **`NormalFib.isMulRightInvariant_of_exactFD`** ("a group with a lattice is unimodular"): a left Haar measure with an
  exact fundamental domain of finite positive measure for a countable subgroup is right invariant;
* **`NormalFib.fibMeas_exactFD`** (the covolume identity, Weil's fibration of $\Gamma\backslash G$ over
  $N(\Gamma)\backslash Q$ with fibre $(\Gamma\cap K)\backslash K$): for exact fundamental domains $D$, $D_K$, $D_Q$ of
  $\Gamma$, $\Gamma\cap K$ and $N(\Gamma)$,
  $$\nu(D) = \mu_K(D_K)\cdot\mu_Q(D_Q),$$
  provided $\operatorname{Ad}(g)_*\mu_K = \mu_K$ for all $g$.

The proof of the covolume identity is the classical one: unfold $\int_Q$ over $N(\Gamma)$; for fixed $q = N(g)$ the
sets $E_\delta = \{k : \gamma_\delta g k\in D\}$ ($N(\gamma_\delta) = \delta$) are disjoint and their union is an exact
fundamental domain for $g^{-1}(\Gamma\cap K)g$ in $K$, i.e. after conjugation for $\Gamma\cap K$.
-/

open MeasureTheory Measure Set Function
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

/-- A locally compact, second countable, Hausdorff topological group is Polish (complete for its right uniformity,
which is countably generated). -/
theorem polishSpace_of_isTopologicalGroup (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] : PolishSpace G := by
  let _ := IsTopologicalGroup.rightUniformSpace G
  have : IsRightUniformGroup G := { toIsTopologicalGroup := ‹_›, uniformity_eq := rfl }
  have : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (uniformity G).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
  infer_instance

/-- An exact measurable fundamental domain: `D` is measurable and meets every orbit in exactly one point. -/
def IsExactFD {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] (D : Set α) : Prop :=
  MeasurableSet D ∧ ∀ x : α, ∃! γ : Γ, γ • x ∈ D

theorem IsExactFD.isFundamentalDomain {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] [Countable Γ]
    {D : Set α} (hD : IsExactFD (Γ := Γ) D) (μ : Measure α) : IsFundamentalDomain Γ D μ :=
  IsFundamentalDomain.mk' hD.1.nullMeasurableSet hD.2

namespace NormalFib

variable {G Q : Type*} [Group G] [Group Q] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableMul Q]

/-- The measure $\mu_K$ transported to the coset $gK$: $(k\mapsto gk)_*\mu_K$. -/
def fibK (N : G →* Q) (μK : Measure N.ker) (g : G) : Measure G := μK.map fun k : N.ker => g * (k : G)

theorem measurable_mul_val (N : G →* Q) (g : G) : Measurable fun k : N.ker => g * (k : G) :=
  (measurable_const_mul g).comp measurable_subtype_coe

theorem fibK_apply (N : G →* Q) (μK : Measure N.ker) (g : G) {s : Set G} (hs : MeasurableSet s) :
    fibK N μK g s = μK ((fun k : N.ker => g * (k : G)) ⁻¹' s) :=
  Measure.map_apply (measurable_mul_val N g) hs

/-- **The fibre measure only depends on the coset**: $N(g) = N(g')\Rightarrow (g\cdot)_*\mu_K = (g'\cdot)_*\mu_K$. -/
theorem fibK_eq_of_eq (N : G →* Q) (μK : Measure N.ker) [μK.IsMulLeftInvariant] {g g' : G} (h : N g = N g') :
    fibK N μK g = fibK N μK g' := by
  have hk : g⁻¹ * g' ∈ N.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  set k₀ : N.ker := ⟨g⁻¹ * g', hk⟩
  have : (fun k : N.ker => g' * (k : G)) = (fun k : N.ker => g * (k : G)) ∘ (fun k => k₀ * k) := by
    funext k; simp [k₀, mul_assoc]
  rw [fibK, fibK, this, ← Measure.map_map (measurable_mul_val N g) (measurable_const_mul k₀),
    map_mul_left_eq_self]

variable (N : G →* Q) (hN : Surjective N)

/-- **The fibre kernel** $\kappa(q) = (g_q\cdot)_*\mu_K$ for any (here: a chosen, non-measurable) $g_q\in N^{-1}(q)$. -/
def kern (μK : Measure N.ker) (q : Q) : Measure G := fibK N μK (surjInv hN q)

theorem kern_apply_N (μK : Measure N.ker) [μK.IsMulLeftInvariant] (g : G) : kern N hN μK (N g) = fibK N μK g :=
  fibK_eq_of_eq N μK (surjInv_eq hN (N g))

/-- The $K$-invariant function $g\mapsto\mu_K\{k : gk\in s\}$ is measurable on $G$. -/
theorem measurable_fibK_apply (μK : Measure N.ker) [SFinite μK] {s : Set G} (hs : MeasurableSet s) :
    Measurable fun g : G => μK ((fun k : N.ker => g * (k : G)) ⁻¹' s) := by
  have hT : MeasurableSet {p : G × N.ker | p.1 * (p.2 : G) ∈ s} :=
    hs.preimage (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))
  exact measurable_measure_prodMk_left hT

variable [StandardBorelSpace G] [MeasurableSpace.CountablySeparated Q]

/-- **The kernel is measurable** (descends from the $K$-invariant measurable function on $G$; Suslin). -/
theorem measurable_kern (hNm : Measurable N) (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] :
    Measurable (kern N hN μK) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  refine (hNm.measurable_comp_iff_of_surjective hN).1 ?_
  have : (fun q => kern N hN μK q s) ∘ N = fun g : G => μK ((fun k : N.ker => g * (k : G)) ⁻¹' s) := by
    funext g; simp only [comp_apply, kern_apply_N, fibK_apply N μK g hs]
  rw [this]; exact measurable_fibK_apply N μK hs

/-- **Weil's fibred measure** $\nu = \int_Q (g_q\cdot)_*\mu_K\,d\mu_Q(q)$ on $G$. -/
def fibMeas (μQ : Measure Q) (μK : Measure N.ker) : Measure G := μQ.bind (kern N hN μK)

theorem fibMeas_apply (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK]
    [μK.IsMulLeftInvariant] {s : Set G} (hs : MeasurableSet s) :
    fibMeas N hN μQ μK s = ∫⁻ q, kern N hN μK q s ∂μQ :=
  Measure.bind_apply hs (measurable_kern N hN hNm μK).aemeasurable

theorem measurable_kern_apply (hNm : Measurable N) (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant]
    {s : Set G} (hs : MeasurableSet s) : Measurable fun q => kern N hN μK q s :=
  Measure.measurable_coe hs |>.comp (measurable_kern N hN hNm μK)

/-- **The fibred measure is left invariant.** -/
theorem isMulLeftInvariant_fibMeas (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant]
    (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] : (fibMeas N hN μQ μK).IsMulLeftInvariant := by
  refine ⟨fun g₀ => ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_const_mul g₀) hs, fibMeas_apply N hN hNm μQ μK hs,
    fibMeas_apply N hN hNm μQ μK (hs.preimage (measurable_const_mul g₀))]
  have : ∀ q, kern N hN μK q ((fun x => g₀ * x) ⁻¹' s) = kern N hN μK (N g₀ * q) s := by
    intro q
    have h1 : N g₀ * q = N (g₀ * surjInv hN q) := by rw [map_mul, surjInv_eq hN q]
    rw [h1, kern_apply_N, kern, fibK_apply N μK _ (hs.preimage (measurable_const_mul g₀)),
      fibK_apply N μK _ hs]
    congr 1
    ext k; simp [mul_assoc]
  simp_rw [this]
  exact lintegral_mul_left_eq_self (fun q => kern N hN μK q s) (N g₀)

/-- **Linearity in the fibre measure**: $\nu(\mu_Q, c\,\mu_K) = c\,\nu(\mu_Q,\mu_K)$. -/
theorem fibMeas_smul (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK]
    [μK.IsMulLeftInvariant] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    fibMeas N hN μQ (c • μK) = c • fibMeas N hN μQ μK := by
  have : SFinite (c • μK) := by
    lift c to ℝ≥0 using hc
    infer_instance
  ext s hs
  rw [fibMeas_apply N hN hNm μQ _ hs, Measure.smul_apply, fibMeas_apply N hN hNm μQ μK hs, smul_eq_mul,
    ← lintegral_const_mul _ (measurable_kern_apply N hN hNm μK hs)]
  congr 1; funext q
  rw [kern, kern, fibK_apply N _ _ hs, fibK_apply N _ _ hs, Measure.smul_apply, smul_eq_mul]

/-- The total mass: $\nu(G) = \mu_K(K)\,\mu_Q(Q)$. -/
theorem fibMeas_univ (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK]
    [μK.IsMulLeftInvariant] : fibMeas N hN μQ μK univ = μK univ * μQ univ := by
  rw [fibMeas_apply N hN hNm μQ μK MeasurableSet.univ]
  have : ∀ q, kern N hN μK q univ = μK univ := fun q => by
    rw [kern, fibK_apply N μK _ MeasurableSet.univ, preimage_univ]
  simp_rw [this, lintegral_const]

/-! ### Conjugation -/

/-- Conjugation by $g$ on the normal subgroup $K = \ker N$. -/
def adK (g : G) : N.ker → N.ker := fun k =>
  ⟨g * (k : G) * g⁻¹, by rw [MonoidHom.mem_ker, map_mul, map_mul, k.2, mul_one, map_inv, mul_inv_cancel]⟩

@[simp] theorem coe_adK (g : G) (k : N.ker) : ((adK N g k : N.ker) : G) = g * (k : G) * g⁻¹ := rfl

theorem measurable_adK (g : G) : Measurable (adK N g) :=
  (((measurable_const_mul g).comp measurable_subtype_coe).mul_const g⁻¹).subtype_mk


section TopAd

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by $g$ on $K = \ker N$ as an isomorphism of topological groups. -/
def adKEquiv (g : G) : N.ker ≃ₜ* N.ker where
  toFun := adK N g
  invFun := adK N g⁻¹
  left_inv k := Subtype.ext (by rw [coe_adK, coe_adK]; group)
  right_inv k := Subtype.ext (by rw [coe_adK, coe_adK]; group)
  map_mul' k l := Subtype.ext (by rw [coe_adK, Subgroup.coe_mul, Subgroup.coe_mul, coe_adK, coe_adK]; group)
  continuous_toFun :=
    (((continuous_const_mul g).comp continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    (((continuous_const_mul g⁻¹).comp continuous_subtype_val).mul continuous_const).subtype_mk _

theorem coe_adKEquiv (g : G) : (adKEquiv N g : N.ker → N.ker) = adK N g := rfl

end TopAd

/-- **Conjugation multiplies the fibred measure by the modulus of $\operatorname{Ad}(g)$ on $K$**: if
$\operatorname{Ad}(g)_*\mu_K = m\,\mu_K$ then $\nu(g^{-1}Eg) = m\,\nu(E)$. -/
theorem map_conj_fibMeas (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK]
    [μK.IsMulLeftInvariant] (g : G) (hgc : ∀ q : Q, N g * q = q * N g) (m : ℝ≥0∞)
    (hm : μK.map (adK N g) = m • μK) :
    (fibMeas N hN μQ μK).map (fun x => g * x * g⁻¹) = m • fibMeas N hN μQ μK := by
  have hc : Measurable fun x : G => g * x * g⁻¹ := (measurable_const_mul g).mul_const g⁻¹
  ext s hs
  rw [Measure.map_apply hc hs, fibMeas_apply N hN hNm μQ μK (hs.preimage hc), Measure.smul_apply,
    fibMeas_apply N hN hNm μQ μK hs, smul_eq_mul, ← lintegral_const_mul _ (measurable_kern_apply N hN hNm μK hs)]
  congr 1; funext q
  set x := surjInv hN q
  have hq : N (g * x * g⁻¹) = q := by
    rw [map_mul, map_mul, map_inv, hgc (N x), mul_assoc, mul_inv_cancel, mul_one, surjInv_eq hN q]
  have h1 : kern N hN μK q ((fun y => g * y * g⁻¹) ⁻¹' s) =
      μK (adK N g ⁻¹' ((fun k : N.ker => g * x * g⁻¹ * (k : G)) ⁻¹' s)) := by
    rw [kern, fibK_apply N μK _ (hs.preimage hc)]
    congr 1; ext k; simp [adK, x, mul_assoc]
  have h2 : μK (adK N g ⁻¹' ((fun k : N.ker => g * x * g⁻¹ * (k : G)) ⁻¹' s)) =
      m * μK ((fun k : N.ker => g * x * g⁻¹ * (k : G)) ⁻¹' s) := by
    rw [← Measure.map_apply (measurable_adK N g) (hs.preimage (measurable_mul_val N _)), hm,
      Measure.smul_apply, smul_eq_mul]
  rw [h1, h2, ← fibK_apply N μK _ hs, ← kern_apply_N N hN μK, hq]

/-- **If the fibred measure is conjugation invariant and nondegenerate, then $\operatorname{Ad}(g)$ preserves $\mu_K$**
(given that $\operatorname{Ad}(g)_*\mu_K$ is some multiple of $\mu_K$). -/
theorem map_adK_eq_of_conj (hNm : Measurable N) (μQ : Measure Q) (μK : Measure N.ker) [SFinite μK]
    [μK.IsMulLeftInvariant] (g : G) (hgc : ∀ q : Q, N g * q = q * N g) (m : ℝ≥0∞)
    (hm : μK.map (adK N g) = m • μK)
    (hconj : (fibMeas N hN μQ μK).map (fun x => g * x * g⁻¹) = fibMeas N hN μQ μK)
    {s : Set G} (hs0 : fibMeas N hN μQ μK s ≠ 0) (hstop : fibMeas N hN μQ μK s ≠ ∞) :
    μK.map (adK N g) = μK := by
  have h := map_conj_fibMeas N hN hNm μQ μK g hgc m hm
  rw [hconj] at h
  have := congrArg (fun μ => μ s) h
  simp only [Measure.smul_apply, smul_eq_mul] at this
  have hm1 : m = 1 := by
    have h' : m * fibMeas N hN μQ μK s = 1 * fibMeas N hN μQ μK s := by rw [one_mul]; exact this.symm
    exact (ENNReal.mul_left_inj hs0 hstop).1 h'
  rw [hm, hm1, one_smul]

/-! ### Unimodularity from a lattice -/

/-- **A left Haar measure with an exact fundamental domain of finite positive measure is right invariant**
("a group with a lattice is unimodular"): the right translate $Dg$ is again an exact fundamental domain, and the right
translate of $\mu$ is a multiple of $\mu$ (`measure_eq_div_smul`). -/
theorem isMulRightInvariant_of_exactFD (μ : Measure G) [μ.IsMulLeftInvariant] [SigmaFinite μ] (Γ : Subgroup G)
    [Countable Γ] {D : Set G} (hD : IsExactFD (Γ := Γ) D) (h0 : μ D ≠ 0) (htop : μ D ≠ ∞) :
    μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmeas : Measurable fun x : G => x * g := measurable_mul_const g
  have : SigmaFinite (μ.map fun x => x * g) :=
    (MeasurableEquiv.mulRight g).sigmaFinite_map
  have h := measure_eq_div_smul (μ.map fun x => x * g) μ h0 htop
  have hD' : IsExactFD (Γ := Γ) ((fun x : G => x * g) ⁻¹' D) := by
    refine ⟨hD.1.preimage hmeas, fun x => ?_⟩
    obtain ⟨γ, hγ, huniq⟩ := hD.2 (x * g)
    refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
    · simpa [Subgroup.smul_def, mul_assoc] using hγ
    · simpa [Subgroup.smul_def, mul_assoc] using hγ'
  have heq : μ ((fun x : G => x * g) ⁻¹' D) = μ D :=
    (hD'.isFundamentalDomain μ).measure_eq (hD.isFundamentalDomain μ)
  rw [Measure.map_apply hmeas hD.1, heq, ENNReal.div_self h0 htop, one_smul] at h
  exact h

/-- A left and right invariant measure is conjugation invariant. -/
theorem map_conj_eq_self (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (g : G) :
    μ.map (fun x => g * x * g⁻¹) = μ := by
  have : (fun x : G => g * x * g⁻¹) = (fun x => x * g⁻¹) ∘ (fun x => g * x) := rfl
  rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

/-! ### The covolume identity -/

section Covolume

variable (Γ : Subgroup G) [Countable Γ]

/-- $\Gamma\cap K$ as a subgroup of $K$. -/
abbrev gammaK : Subgroup N.ker := Γ.comap N.ker.subtype

/-- $N(\Gamma)$ as a subgroup of $Q$. -/
abbrev gammaQ : Subgroup Q := Γ.map N

instance : Countable (gammaK N Γ) :=
  Function.Injective.countable (f := fun x : gammaK N Γ => (⟨((x : N.ker) : G), x.2⟩ : Γ))
    fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))

instance : Countable (gammaQ N Γ) := by
  have : Surjective fun γ : Γ => (⟨N γ, γ, γ.2, rfl⟩ : gammaQ N Γ) := by
    rintro ⟨q, γ, hγ, rfl⟩; exact ⟨⟨γ, hγ⟩, rfl⟩
  exact this.countable

theorem coe_smul_gammaK (ε : gammaK N Γ) (k : N.ker) : ((ε • k : N.ker) : G) = ((ε : N.ker) : G) * (k : G) :=
  rfl

/-- **The fibre sum**: for every $q$, $\sum_{\delta\in N(\Gamma)}\kappa(\delta q)(D) = \mu_K(D_K)$. -/
theorem tsum_kern_exactFD (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant]
    (hconj : ∀ g : G, μK.map (adK N g) = μK) {D : Set G} (hD : IsExactFD (Γ := Γ) D)
    {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK) (q : Q) :
    ∑' δ : gammaQ N Γ, kern N hN μK ((δ : Q) * q) D = μK DK := by
  classical
  set g := surjInv hN q
  -- lifts γ_δ
  have hlift : ∀ δ : gammaQ N Γ, ∃ γ : Γ, N γ = δ := by
    rintro ⟨_, γ, hγ, rfl⟩; exact ⟨⟨γ, hγ⟩, rfl⟩
  choose γd hγd using hlift
  let E : gammaQ N Γ → Set N.ker := fun δ => (fun k : N.ker => (γd δ : G) * g * (k : G)) ⁻¹' D
  have hEm : ∀ δ, MeasurableSet (E δ) := fun δ =>
    hD.1.preimage (measurable_mul_val N _)
  have hkern : ∀ δ : gammaQ N Γ, kern N hN μK ((δ : Q) * q) D = μK (E δ) := by
    intro δ
    have : (δ : Q) * q = N ((γd δ : G) * g) := by rw [map_mul, hγd, surjInv_eq hN q]
    rw [this, kern_apply_N, fibK_apply N μK _ hD.1]
  have hdisj : Pairwise (Disjoint on E) := by
    intro δ₁ δ₂ hne
    refine Set.disjoint_left.2 fun k h₁ h₂ => hne ?_
    have h₁' : (γd δ₁) • (g * (k : G)) ∈ D := by simpa [Subgroup.smul_def, E, mul_assoc] using h₁
    have h₂' : (γd δ₂) • (g * (k : G)) ∈ D := by simpa [Subgroup.smul_def, E, mul_assoc] using h₂
    have := (hD.2 (g * (k : G))).unique h₁' h₂'
    apply Subtype.ext; rw [← hγd δ₁, ← hγd δ₂, this]
  simp_rw [hkern]
  rw [← measure_iUnion hdisj hEm]
  -- the union, conjugated by g, is an exact fundamental domain for Γ ∩ K
  set U := ⋃ δ, E δ
  set U' := adK N g⁻¹ ⁻¹' U
  have hU'm : MeasurableSet U' := (MeasurableSet.iUnion hEm).preimage (measurable_adK N _)
  have hmU : μK U' = μK U := by
    rw [← Measure.map_apply (measurable_adK N _) (MeasurableSet.iUnion hEm), hconj]
  have hmemU' : ∀ k : N.ker, k ∈ U' ↔ ∃ δ, (γd δ : G) * (k : G) * g ∈ D := by
    intro k
    simp only [U', U, E, mem_preimage, mem_iUnion, adK, inv_inv]
    refine exists_congr fun δ => ?_
    rw [show (γd δ : G) * g * (g⁻¹ * (k : G) * g) = (γd δ : G) * (k : G) * g by group]
  have hU' : IsExactFD (Γ := gammaK N Γ) U' := by
    refine ⟨hU'm, fun k => ?_⟩
    obtain ⟨γ, hγ, huniq⟩ := hD.2 ((k : G) * g)
    set δ : gammaQ N Γ := ⟨N γ, γ, γ.2, rfl⟩
    have hεK : (γd δ : G)⁻¹ * γ ∈ N.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hγd δ, inv_mul_cancel]
    have hεΓ : ((⟨(γd δ : G)⁻¹ * γ, hεK⟩ : N.ker) : G) ∈ Γ := Γ.mul_mem (Γ.inv_mem (γd δ).2) γ.2
    let ε : gammaK N Γ := ⟨⟨(γd δ : G)⁻¹ * γ, hεK⟩, hεΓ⟩
    refine ⟨ε, ?_, fun ε' hε' => ?_⟩
    · show ε • k ∈ U'
      rw [hmemU']
      refine ⟨δ, ?_⟩
      have : (γd δ : G) * ((ε • k : N.ker) : G) * g = γ • ((k : G) * g) := by
        rw [coe_smul_gammaK, Subgroup.smul_def, smul_eq_mul]
        simp only [ε]; group
      rw [this]; exact hγ
    · change ε' • k ∈ U' at hε'
      rw [hmemU'] at hε'
      obtain ⟨δ', hδ'⟩ := hε'
      have h1 : (⟨(γd δ' : G) * ((ε' : N.ker) : G), Γ.mul_mem (γd δ').2 ε'.2⟩ : Γ) • ((k : G) * g) ∈ D := by
        rw [coe_smul_gammaK] at hδ'
        rw [Subgroup.smul_def, smul_eq_mul]
        convert hδ' using 1
        simp only [mul_assoc]
      have h2 := huniq _ h1
      -- apply N to get δ' = δ
      have hN' : (δ' : Q) = δ := by
        have := congrArg (fun x : Γ => N (x : G)) h2
        simp only [map_mul] at this
        have hε'1 : N (((ε' : N.ker) : G)) = 1 := (ε' : N.ker).2
        rw [hε'1, mul_one, hγd δ'] at this
        exact this
      have hδeq : δ' = δ := Subtype.ext hN'
      subst hδeq
      apply Subtype.ext; apply Subtype.ext
      have := congrArg (fun x : Γ => (x : G)) h2
      simp only at this
      simp only [ε]
      rw [← this]; group
  rw [← hmU]
  exact (hU'.isFundamentalDomain μK).measure_eq (hDK.isFundamentalDomain μK)

/-- **The covolume identity (Weil's fibration of $\Gamma\backslash G$)**: for exact fundamental domains $D$ of
$\Gamma$ in $G$, $D_K$ of $\Gamma\cap K$ in $K$ and $D_Q$ of $N(\Gamma)$ in $Q$, if conjugation preserves $\mu_K$, then
$\nu(D) = \mu_K(D_K)\,\mu_Q(D_Q)$. -/
@[kb "weil1982" "§2.4, Thm 2.4.4 and Lemma 2.4.1 [unverified page]"]
theorem fibMeas_exactFD (hNm : Measurable N) (μQ : Measure Q) [μQ.IsMulLeftInvariant] (μK : Measure N.ker)
    [SFinite μK] [μK.IsMulLeftInvariant] (hconj : ∀ g : G, μK.map (adK N g) = μK)
    {D : Set G} (hD : IsExactFD (Γ := Γ) D) {DK : Set N.ker} (hDK : IsExactFD (Γ := gammaK N Γ) DK)
    {DQ : Set Q} (hDQ : IsExactFD (Γ := gammaQ N Γ) DQ) :
    fibMeas N hN μQ μK D = μK DK * μQ DQ := by
  rw [fibMeas_apply N hN hNm μQ μK hD.1,
    (hDQ.isFundamentalDomain μQ).lintegral_eq_tsum'' (fun q => kern N hN μK q D)]
  have hm := measurable_kern_apply N hN hNm μK hD.1
  simp_rw [Subgroup.smul_def, smul_eq_mul]
  have h := lintegral_tsum (μ := μQ.restrict DQ)
    (f := fun (δ : gammaQ N Γ) x => kern N hN μK ((δ : Q) * x) D)
    (fun δ => (hm.comp (measurable_const_mul (δ : Q))).aemeasurable)
  rw [← h]
  simp_rw [tsum_kern_exactFD N hN Γ μK hconj hD hDK]
  rw [setLIntegral_const]

end Covolume

/-! ### Finiteness on compacts -/

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [BorelSpace G] [TopologicalSpace Q] [T2Space Q]
  [BorelSpace Q]

/-- **The fibred measure is finite on compact sets**: $\nu(C)\le\mu_Q(N(C))\,\mu_K(K\cap C^{-1}C)$. -/
theorem fibMeas_compact_lt_top (hNc : Continuous N) (μQ : Measure Q) [IsFiniteMeasureOnCompacts μQ]
    (μK : Measure N.ker) [SFinite μK] [μK.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μK]
    (hK : IsClosed (N.ker : Set G)) {C : Set G} (hC : IsCompact C) :
    fibMeas N hN μQ μK C < ∞ := by
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  set L : Set N.ker := Subtype.val ⁻¹' (C⁻¹ * C)
  have hLc : IsCompact L :=
    hK.isClosedEmbedding_subtypeVal.isCompact_preimage (hC.inv.mul hC)
  have hNC : IsCompact (N '' C) := hC.image hNc
  have hbound : ∀ q, kern N hN μK q C ≤ (N '' C).indicator (fun _ => μK L) q := by
    intro q
    rw [kern, fibK_apply N μK _ hCm]
    by_cases hne : ((fun k : N.ker => surjInv hN q * (k : G)) ⁻¹' C).Nonempty
    · obtain ⟨k₁, hk₁⟩ := hne
      have hq : q ∈ N '' C := ⟨_, hk₁, by
        rw [map_mul, surjInv_eq hN q, (k₁ : N.ker).2, mul_one]⟩
      rw [indicator_of_mem hq]
      calc μK ((fun k : N.ker => surjInv hN q * (k : G)) ⁻¹' C)
          ≤ μK ((fun k => k₁⁻¹ * k) ⁻¹' L) := by
            refine measure_mono fun k hk => ?_
            simp only [mem_preimage, L, Subgroup.coe_mul, Subgroup.coe_inv] at hk hk₁ ⊢
            refine ⟨(surjInv hN q * (k₁ : G))⁻¹, inv_mem_inv.2 hk₁, surjInv hN q * (k : G), hk, ?_⟩
            group
        _ = μK L := measure_preimage_mul μK k₁⁻¹ L
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty]; exact zero_le
  rw [fibMeas_apply N hN hNc.measurable μQ μK hCm]
  calc ∫⁻ q, kern N hN μK q C ∂μQ ≤ ∫⁻ q, (N '' C).indicator (fun _ => μK L) q ∂μQ := lintegral_mono hbound
    _ = μK L * μQ (N '' C) := by
        rw [lintegral_indicator_const hNC.isClosed.measurableSet]
    _ < ∞ := ENNReal.mul_lt_top hLc.measure_lt_top hNC.measure_lt_top

end Topological

end NormalFib

end

end QuadFormsKB.Tamagawa.Measure.Weil
