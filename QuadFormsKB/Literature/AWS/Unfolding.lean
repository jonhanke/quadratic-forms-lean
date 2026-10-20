/-
# Hanke, AWS 2009 notes, §4.6: unfolding the integral over $O(V)\backslash O(V_\mathbb{A})$

The computation (4.5)–(4.17) (pp. 63–64) of J. Hanke, *Quadratic Forms and Automorphic Forms*
(bibkey `hanke2011aws`), for an abstract group. The list D1, D2, … of the notes' derivations is in
`AWS/Overview.lean`; this file is **D18** and **D24**.

**Setting.** A group $G$ ($= O(V_\mathbb{A})$) with a measure $\mu$ ($= dh_\mathbb{A}$), a subgroup $\Gamma$
($= O(V)$, diagonally) and a subgroup $K$ ($= K_\mathbb{A} = \mathrm{Stab}_\mathbb{A}(L)$) of volume $1$.
The integral over $\Gamma\backslash G$ is not constructed here: it is an **input**
(`QuotientIntegralInputs`), a functional $I$ on functions $G \to \mathbb{C}$ related to $\mu$ by
**Weil's formula** $I\bigl(g \mapsto \sum_{\gamma\in\Gamma} f(\gamma g)\bigr) = \int_G f\,d\mu$
(the defining property of the quotient measure, with counting measure on the discrete group $\Gamma$).

**Main result** (`integral_eq_sum_doset`, (4.5)–(4.13)): if $G = \bigsqcup_{i\in I}\Gamma\alpha_iK$
(finitely many double cosets: the class number is finite) and each
$\Gamma_i := \Gamma \cap \alpha_iK\alpha_i^{-1}$ is finite, then for every left-$\Gamma$-invariant $F$
$$\int_{\Gamma\backslash G} F(h)\,dh = \sum_{i \in I} \frac{1}{|\Gamma_i|}\int_K F(\alpha_i h)\,dh .$$
With $F = \Phi_{L_j}\,\theta$ only $i = j$ survives ((4.14)–(4.17), `integral_indicator_mul`).
With $F = 1$: $\mathrm{vol}(\Gamma\backslash G) = \sum_i 1/|\mathrm{Aut}(L_i)| = \mathrm{Mass}(L)$
(`integral_one_eq_mass`, D24).

*Simplification (candidate; pending author):* the notes pass through right cosets
$\Gamma\backslash\Gamma\alpha_iK\alpha_i^{-1}$ ((4.8)) and use right-invariance of $dh_\mathbb{A}$
("the orthogonal group is unimodular", p. 64). Working with the left translates $\alpha_i K$ instead, as
here, only **left** invariance of $\mu$ (and Weil's formula) is used, and (4.13) follows in one step.
-/
import QuadFormsKB.Literature.AWS.DoubleCosets

open MeasureTheory
open scoped Pointwise

namespace QuadFormsKB.AWS

variable {G : Type*} [Group G]

/-- **Input: the integral over $\Gamma\backslash G$** (§4.4, (4.3); §4.6, (4.4)–(4.11)).

Fields:
- `I`: the integral $F \mapsto \int_{\Gamma\backslash G} F(h)\,dh$, applied to left-$\Gamma$-invariant
  $F : G \to \mathbb{C}$ (its values on other functions are irrelevant);
- `weil`: **Weil's formula** relating `I` to the measure $\mu$ on $G$: for every $\mu$-integrable $f$,
  $I\bigl(g \mapsto \sum_{\gamma \in \Gamma} f(\gamma g)\bigr) = \int_G f\,d\mu$
  (A. Weil, *L'intégration dans les groupes topologiques*, §9; Bourbaki, *Intégration* VII §2;
  for discrete $\Gamma$ the quotient measure is characterized by it). It is used here only for
  $f$ supported on finitely many translates $\alpha K$, where the sum over $\gamma$ has finitely many
  nonzero terms;
- `left_invariant`: $\mu$ is left-invariant (a left Haar measure);
- `measurableSet_K`, `measure_K`: $K$ is measurable and $\mu(K) = 1$ (the notes' normalization
  "giving the adelic stabilizer $\mathrm{Stab}_\mathbb{A}(L)$ volume $1$", p. 61).

The notes take $\mu$ to be a Haar measure on $O(V_\mathbb{A})$, which exists because $O(V_\mathbb{A})$ is
locally compact, and the quotient measure exists because $\Gamma$ is discrete (and $G$ unimodular);
neither existence statement is in Mathlib for adelic groups. -/
structure QuotientIntegralInputs [MeasurableSpace G] (Γ K : Subgroup G) (μ : Measure G) where
  I : (G → ℂ) → ℂ
  weil : ∀ f : G → ℂ, Integrable f μ → I (fun g => ∑' γ : Γ, f (γ * g)) = ∫ g, f g ∂μ
  left_invariant : μ.IsMulLeftInvariant
  measurableSet_K : MeasurableSet (K : Set G)
  measure_K : μ K = 1

variable {Γ K : Subgroup G}

/-- The elements $\gamma \in \Gamma$ with $\gamma g \in \alpha K$ form a coset of
$\Gamma \cap \alpha K \alpha^{-1}$ when $g \in \Gamma \alpha K$; in particular there are
$|\Gamma \cap \alpha K\alpha^{-1}|$ of them. -/
theorem card_setOf_mul_mem (α g : G) (hg : g ∈ DoubleCoset.doubleCoset α Γ K) :
    Nat.card {γ : Γ | (γ : G) * g ∈ α • (K : Set G)} =
      Nat.card (Γ ⊓ conjSub α K : Subgroup G) := by
  obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  have key : ∀ γ : G, γ * (γ₀ * α * k₀) ∈ α • (K : Set G) ↔ γ * γ₀ ∈ conjSub α K := by
    intro γ
    rw [mem_conjSub, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]
    constructor
    · intro h
      have := K.mul_mem h (K.inv_mem hk₀)
      convert this using 1; group
    · intro h
      have := K.mul_mem h hk₀
      convert this using 1; group
  refine Nat.card_congr
    { toFun := fun γ => ⟨γ.1 * γ₀, Γ.mul_mem γ.1.2 hγ₀, (key γ.1).mp γ.2⟩
      invFun := fun δ => ⟨⟨δ.1 * γ₀⁻¹, Γ.mul_mem δ.2.1 (Γ.inv_mem hγ₀)⟩, by
        show δ.1 * γ₀⁻¹ * (γ₀ * α * k₀) ∈ α • (K : Set G)
        rw [key]; simpa using δ.2.2⟩
      left_inv := fun γ => by ext; simp
      right_inv := fun δ => by ext; simp }

/-- If $g \notin \Gamma\alpha K$, no $\gamma \in \Gamma$ has $\gamma g \in \alpha K$. -/
theorem setOf_mul_mem_eq_empty (α g : G) (hg : g ∉ DoubleCoset.doubleCoset α Γ K) :
    {γ : Γ | (γ : G) * g ∈ α • (K : Set G)} = ∅ := by
  ext γ
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨k, hk, e⟩ := Set.mem_smul_set.mp h
  apply hg
  refine DoubleCoset.mem_doubleCoset.mpr ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, k, hk, ?_⟩
  rw [smul_eq_mul] at e
  rw [mul_assoc, e]; group

variable [MeasurableSpace G]

/-- A tsum of a constant over a finite subset. -/
private theorem tsum_indicator_const {β : Type*} (S : Set β) [Finite S] (a : ℂ) :
    ∑' b, S.indicator (fun _ => a) b = Nat.card S * a := by
  rw [← tsum_subtype S (fun _ => a), tsum_const, nsmul_eq_mul]

/-- **D18: the unfolding (4.5)–(4.13) (pp. 63–64).** Suppose $G = \bigsqcup_{i \in I} \Gamma\alpha_iK$
with $I$ finite (`hcov`: every $g$ lies in some $\Gamma\alpha_iK$; `hdisj`: the double cosets
$\Gamma\alpha_iK$ are distinct), and each $\Gamma_i := \Gamma \cap \alpha_iK\alpha_i^{-1}$ is finite
(`hfin`; for $\Gamma = O(V)$ this is the finite group $\mathrm{Aut}(L_i)$). Then for every
left-$\Gamma$-invariant $F$ which is integrable on each $\alpha_iK$,
$$I(F) = \sum_{i\in I} \frac{1}{|\Gamma_i|}\int_K F(\alpha_i h)\,d\mu(h).$$
This is (4.13) (with the summand written as in (4.13), i.e. after the change of variables
$h \mapsto \alpha_i h \alpha_i^{-1}$ of (4.12)–(4.13)). -/
@[kb "hanke2011aws" "§4.6, (4.5)-(4.13), pp. 63-64"]
theorem integral_eq_sum_doset {μ : Measure G} [MeasurableMul G] (inp : QuotientIntegralInputs Γ K μ)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G))
    (F : G → ℂ) (hF : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hint : ∀ i, IntegrableOn F (α i • (K : Set G)) μ) :
    inp.I F = ∑ i, ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹ *
      ∫ h in (K : Set G), F (α i * h) ∂μ := by
  classical
  have := inp.left_invariant
  set c : ι → ℂ := fun i => ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹
  have hmeas : ∀ i, MeasurableSet (α i • (K : Set G)) := fun i => inp.measurableSet_K.const_smul _
  -- the function to integrate over G
  set f : G → ℂ := fun g => ∑ i, c i * (α i • (K : Set G)).indicator F g with hf
  have hfint : Integrable f μ :=
    integrable_finsetSum _ fun i _ => ((hint i).integrable_indicator (hmeas i)).const_mul _
  -- uniqueness of the double coset of g
  have huniq : ∀ g i j, g ∈ DoubleCoset.doubleCoset (α i) Γ K →
      g ∈ DoubleCoset.doubleCoset (α j) Γ K → i = j := by
    intro g i j hi hj
    apply hdisj
    exact (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hi)).symm.trans
      (DoubleCoset.mk_eq_of_doubleCoset_eq (DoubleCoset.doubleCoset_eq_of_mem hj))
  -- the periodization of f is F
  have hper : ∀ g, ∑' γ : Γ, f (γ * g) = F g := by
    intro g
    obtain ⟨i₀, hi₀⟩ := hcov g
    set S := {γ : Γ | (γ : G) * g ∈ α i₀ • (K : Set G)}
    have hS : Nat.card S = Nat.card (Γ ⊓ conjSub (α i₀) K : Subgroup G) :=
      card_setOf_mul_mem (α i₀) g hi₀
    haveI : Finite S := by
      apply Nat.finite_of_card_ne_zero
      rw [hS]
      haveI := hfin i₀
      exact Nat.card_pos.ne'
    have hterm : ∀ γ : Γ, f (γ * g) = S.indicator (fun _ => c i₀ * F g) γ := by
      intro γ
      simp only [hf]
      rw [Finset.sum_eq_single i₀]
      · by_cases hγ : γ ∈ S
        · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem (s := α i₀ • (K : Set G)) hγ, hF _ γ.2]
        · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem (s := α i₀ • (K : Set G)) hγ,
            mul_zero]
      · intro j _ hj
        have : (α j • (K : Set G)).indicator F (γ * g) = 0 := by
          apply Set.indicator_of_notMem
          intro hmem
          have hg' : g ∈ DoubleCoset.doubleCoset (α j) Γ K := by
            by_contra hn
            have := setOf_mul_mem_eq_empty (Γ := Γ) (K := K) (α j) g hn
            exact (Set.eq_empty_iff_forall_notMem.mp this) γ hmem
          exact hj (huniq g j i₀ hg' hi₀)
        rw [this, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hterm]
    rw [tsum_indicator_const, hS]
    haveI := hfin i₀
    have hpos : (Nat.card (Γ ⊓ conjSub (α i₀) K : Subgroup G) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    simp only [c]
    field_simp
  have hI : inp.I F = ∫ g, f g ∂μ := by
    rw [← inp.weil f hfint]
    congr 1
    funext g
    exact (hper g).symm
  rw [hI, integral_finsetSum _ fun i _ => ((hint i).integrable_indicator (hmeas i)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_indicator (hmeas i)]
  congr 1
  -- left invariance: ∫_{αK} F = ∫_K F(α ·)
  rw [← integral_indicator (hmeas i), ← integral_indicator inp.measurableSet_K,
    ← integral_mul_left_eq_self _ (α i)]
  congr 1
  funext h
  by_cases hh : h ∈ (K : Set G)
  · rw [Set.indicator_of_mem hh]
    exact Set.indicator_of_mem (Set.smul_mem_smul_set (a := α i) hh) F
  · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem]
    intro hmem
    apply hh
    obtain ⟨k, hk, e⟩ := Set.mem_smul_set.mp hmem
    rw [smul_eq_mul, mul_left_cancel_iff] at e
    exact e ▸ hk

/-- **D19, (4.14)–(4.17) (p. 64): only the $j$-th double coset contributes.** For the integrand
$F = \Phi_{L_j}\cdot\theta$, with $\Phi_{L_j}$ the characteristic function of $\Gamma\alpha_jK$ and $\theta$
left-$\Gamma$-invariant ($= \theta_\phi(g_\mathbb{A}, \cdot)$, Lemma 4.4.1),
$$\int_{\Gamma\backslash G} \Phi_{L_j}(h)\,\theta(h)\,dh = \frac{1}{|\Gamma_j|}\int_K \theta(\alpha_j h)\,d\mu(h).$$

*Erratum (candidate; pending author):* the definition (4.3) of the theta lift prints the integrand as
$F(g_\mathbb{A})\,\theta_\varphi(g_\mathbb{A}, h_\mathbb{A})$; it should be $F(h_\mathbb{A})\,\theta_\varphi(g_\mathbb{A}, h_\mathbb{A})$,
as in (4.4) and here. -/
@[kb "hanke2011aws" "§4.6, (4.14)-(4.17), p. 64"]
theorem integral_indicator_mul {μ : Measure G} [MeasurableMul G]
    (inp : QuotientIntegralInputs Γ K μ) {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G)) (j : ι)
    (θ : G → ℂ) (hθ : ∀ γ ∈ Γ, ∀ g, θ (γ * g) = θ g)
    (hint : ∀ i, IntegrableOn (fun h => dosetIndicator Γ K (α j) h * θ h) (α i • (K : Set G)) μ) :
    inp.I (fun h => dosetIndicator Γ K (α j) h * θ h) =
      ((Nat.card (Γ ⊓ conjSub (α j) K : Subgroup G) : ℂ))⁻¹ *
        ∫ h in (K : Set G), θ (α j * h) ∂μ := by
  rw [integral_eq_sum_doset inp α hcov hdisj hfin _
    (fun γ hγ g => by rw [dosetIndicator_left Γ K (α j) hγ, hθ γ hγ]) hint,
    Finset.sum_eq_single j]
  · congr 1
    refine setIntegral_congr_fun inp.measurableSet_K fun h hh => ?_
    simp only [dosetIndicator]
    rw [Set.indicator_of_mem ((mem_doset_mul_iff Γ K α hdisj hh j j).mpr rfl), Pi.one_apply, one_mul]
  · intro i _ hij
    rw [setIntegral_congr_fun (g := fun _ => (0 : ℂ)) inp.measurableSet_K fun h hh => ?_]
    · simp
    simp only [dosetIndicator]
    rw [Set.indicator_of_notMem (fun hm => hij ((mem_doset_mul_iff Γ K α hdisj hh i j).mp hm)),
      zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **D24 (p. 62 with §2.6): the volume of $\Gamma\backslash G$ is the mass.** With the normalization
$\mu(K) = 1$,
$$\int_{\Gamma\backslash G} 1\,dh = \sum_{i \in I}\frac{1}{|\Gamma_i|},$$
which for $G = O(V_\mathbb{A})$ is $\sum_{L_i} 1/|\mathrm{Aut}(L_i)| = \mathrm{Mass}(L)$, the mass of §2.6
(p. 34). (The notes do not state this; it is the case $F = 1$ of the unfolding.) -/
@[kb "hanke2011aws" "§4.6 with §2.6, p. 34"]
theorem integral_one_eq_mass {μ : Measure G} [MeasurableMul G] (inp : QuotientIntegralInputs Γ K μ)
    {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G)) :
    inp.I (fun _ => 1) = ∑ i, ((Nat.card (Γ ⊓ conjSub (α i) K : Subgroup G) : ℂ))⁻¹ := by
  have := inp.left_invariant
  have hK : μ (K : Set G) ≠ ⊤ := by rw [inp.measure_K]; exact ENNReal.one_ne_top
  rw [integral_eq_sum_doset inp α hcov hdisj hfin _ (fun _ _ _ => rfl) (fun i => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_const, Measure.real, inp.measure_K]
    simp
  · refine integrableOn_const ?_
    rw [measure_smul]; exact hK

/-- **D24: the theta lift of $1$ is the sum of the theta lifts of the $\Phi_{L_j}$** (p. 62, "the
constant function $1$ … play[s] a special role"): for left-$\Gamma$-invariant $\theta$,
$$\int_{\Gamma\backslash G}\theta = \sum_j \int_{\Gamma\backslash G}\Phi_{L_j}\,\theta .$$
Together with (4.37) (`AWS.thetaLift_indicator_eq`) this is
$\Theta(1) \leftrightarrow \sum_j \Theta_{L_j}/|\mathrm{Aut}(L_j)|$, the weighted genus theta series. -/
@[kb "hanke2011aws" "§4.5-§4.6, pp. 62-66"]
theorem integral_eq_sum_integral_indicator_mul {μ : Measure G} [MeasurableMul G]
    (inp : QuotientIntegralInputs Γ K μ) {ι : Type*} [Fintype ι] (α : ι → G)
    (hcov : ∀ g, ∃ i, g ∈ DoubleCoset.doubleCoset (α i) Γ K)
    (hdisj : ∀ i j, DoubleCoset.mk Γ K (α i) = DoubleCoset.mk Γ K (α j) → i = j)
    (hfin : ∀ i, Finite (Γ ⊓ conjSub (α i) K : Subgroup G))
    (θ : G → ℂ) (hθ : ∀ γ ∈ Γ, ∀ g, θ (γ * g) = θ g)
    (hint : ∀ i, IntegrableOn θ (α i • (K : Set G)) μ)
    (hint' : ∀ i j, IntegrableOn (fun h => dosetIndicator Γ K (α j) h * θ h) (α i • (K : Set G)) μ) :
    inp.I θ = ∑ j, inp.I (fun h => dosetIndicator Γ K (α j) h * θ h) := by
  rw [integral_eq_sum_doset inp α hcov hdisj hfin θ hθ hint]
  exact Finset.sum_congr rfl fun j _ =>
    (integral_indicator_mul inp α hcov hdisj hfin j θ hθ (hint' · j)).symm

end QuadFormsKB.AWS
