/-
# Orbit decompositions for Weil's induction

**Layer:** pure group theory (any group acting on any set), extending `Tamagawa/OrbitMass.lean`.

These are the three counting steps in Weil's proof of the mass formula by induction on the dimension
(Weil, *Adeles and Algebraic Groups*, §§3.4–3.5 [unverified locator]; Kneser's lectures; Kitaoka 1993, §6.8 [unverified]):

* `orbitMass_eq_finsum_fiber` (**weighted fibration**): for an $H$-equivariant $f : X' \to X$ with finitely many
  orbits on $X$, finite stabilizers and finite fibres,
  $$\mathrm{mass}_H(X') = \sum_{\omega \in H\backslash X}\frac{|f^{-1}(x_\omega)|}{|\mathrm{Stab}_H(x_\omega)|}.$$
  With $X' = \{(M, v) : v \in M,\ Q(v) = m\}$ and $X$ the genus, this is the weighted representation number
  $\sum_{M} r_M(m)/|O(M)|$.
* `orbitMass_eq_fiber_of_transitive` (**transitive base**): if $H$ is transitive on $X$, then
  $\mathrm{mass}_H(X') = \mathrm{mass}_{\mathrm{Stab}_H(x_0)}(f^{-1}(x_0))$. No finiteness is needed. With
  $X = \{v : Q(v) = m\}$ (one orbit by Witt's theorem) this replaces pairs $(M, v)$ by lattices containing the fixed
  vector $x_0$, acted on by the stabilizer $O(x_0^\perp)$.
* `orbitMass_eq_finsum_dcMass` (**decomposition by a larger group**): for $\Gamma \le G$ with $\Gamma\backslash Y$ finite,
  $$\mathrm{mass}_\Gamma(Y) = \sum_{t \in G\backslash Y}\mathrm{dcMass}(\Gamma, \mathrm{Stab}_G(y_t)).$$
  With $G$ the adelic stabilizer and $\Gamma$ its rational points, the $G$-orbits are the local types of the pairs.
* `dcMass_mul_idxVol` (**the volume of $\Gamma\backslash G$ is well defined**): for $K$ commensurable with $K_0$,
  $\mathrm{dcMass}(\Gamma, K)\cdot\mu(K) = \mu(K_0)\cdot\mathrm{dcMass}(\Gamma, K_0)$ for the Haar measure $\mu$ =
  `idxVol K₀ c`. This extends `mass_mul_vol_eq` from $K \le K_0$ to commensurable $K$.

Finiteness transfers: `finite_orbits_of_fiber`, `finite_orbits_of_map`, `finite_stabilizer_of_commensurable`,
`finite_orbits_of_commensurable`.
-/
import QuadFormsKB.Tamagawa.LocalVolume

open MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

variable {H X : Type*} [Group H] [MulAction H X]

/-! ### Finiteness transfers -/

/-- **Finitely many orbits upstairs:** if $f : X' \to X$ is equivariant, $H\backslash X$ is finite and every fibre
$f^{-1}(x)$ is finite, then $H\backslash X'$ is finite. -/
theorem finite_orbits_of_fiber {X' : Type*} [MulAction H X'] (f : X' → X)
    (hf : ∀ (h : H) (y : X'), f (h • y) = h • f y) [Finite (orbitRel.Quotient H X)]
    (hfin : ∀ x, Finite {y : X' // f y = x}) : Finite (orbitRel.Quotient H X') := by
  classical
  let Fm : orbitRel.Quotient H X' → orbitRel.Quotient H X :=
    Quotient.map' f (fun a b hab => by
      rw [orbitRel_apply] at hab ⊢
      obtain ⟨h, rfl⟩ := hab
      exact ⟨h, (hf h b).symm⟩)
  have hFout : ∀ ω', Fm ω' = Quotient.mk'' (f ω'.out) := by
    intro ω'; conv_lhs => rw [← Quotient.out_eq' ω']
    rfl
  have hFfib : ∀ ω : orbitRel.Quotient H X, (Fm ⁻¹' {ω}).Finite := by
    intro ω
    have : Finite {y : X' // f y = ω.out} := hfin _
    have hsub : Fm ⁻¹' {ω} ⊆ Set.range (fun y : {y : X' // f y = ω.out} =>
        (Quotient.mk'' y.1 : orbitRel.Quotient H X')) := by
      intro ω' hω'
      have hω'' : Fm ω' = ω := hω'
      have : (Quotient.mk'' (f ω'.out) : orbitRel.Quotient H X) = Quotient.mk'' ω.out := by
        rw [Quotient.out_eq', ← hω'', hFout]
      have := Quotient.exact' this
      rw [orbitRel_apply] at this
      obtain ⟨h, hh⟩ := this
      refine ⟨⟨h⁻¹ • ω'.out, by rw [hf, ← hh, inv_smul_smul]⟩, ?_⟩
      conv_rhs => rw [← Quotient.out_eq' ω']
      exact Quotient.sound' (by rw [orbitRel_apply]; exact ⟨h⁻¹, rfl⟩)
    exact (Set.finite_range _).subset hsub
  have h := Set.Finite.preimage' (Set.finite_univ (α := orbitRel.Quotient H X)) (fun ω _ => hFfib ω)
  rw [Set.preimage_univ] at h
  exact Set.finite_univ_iff.mp h

/-- **Finitely many orbits along an orbit-injective map:** if $g : X_1 \to X_2$ satisfies
$g(a) \in H_2 g(b) \Rightarrow a \in H_1 b$ and $H_2\backslash X_2$ is finite, then so is $H_1\backslash X_1$. -/
theorem finite_orbits_of_map {H₁ X₁ H₂ X₂ : Type*} [Group H₁] [MulAction H₁ X₁] [Group H₂]
    [MulAction H₂ X₂] (g : X₁ → X₂) (horb : ∀ a b : X₁, g a ∈ orbit H₂ (g b) → a ∈ orbit H₁ b)
    [Finite (orbitRel.Quotient H₂ X₂)] : Finite (orbitRel.Quotient H₁ X₁) := by
  let G : orbitRel.Quotient H₁ X₁ → orbitRel.Quotient H₂ X₂ :=
    fun ω => Quotient.mk'' (g ω.out)
  refine Finite.of_injective G fun ω₁ ω₂ h => ?_
  have := Quotient.exact' h
  rw [orbitRel_apply] at this
  rw [← Quotient.out_eq' ω₁, ← Quotient.out_eq' ω₂]
  exact Quotient.sound' (by rw [orbitRel_apply]; exact horb _ _ this)

/-! ### The weighted fibration formula -/

section Fiber

variable {X' : Type*} [MulAction H X'] (f : X' → X) (hf : ∀ (h : H) (y : X'), f (h • y) = h • f y)

include hf

/-- **The weighted fibration formula:** for an $H$-equivariant $f : X' \to X$ with $H\backslash X$ finite, finite
stabilizers on $X$ and finite fibres,
$$\mathrm{mass}_H(X') = \sum_{\omega \in H\backslash X}\frac{|f^{-1}(x_\omega)|}{|\mathrm{Stab}_H(x_\omega)|}.$$
(`orbitMass_fiber` is the case of constant fibre size.) For pairs $(M, v)$ over the genus this is
$\sum_{\mathrm{cls}(M)} r_M(m)/|O(M)|$ (Siegel 1935, §1 [unverified]). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem orbitMass_eq_finsum_fiber [Finite (orbitRel.Quotient H X)]
    (hstab : ∀ x : X, Finite (stabilizer H x)) (hfin : ∀ x, Finite {y : X' // f y = x}) :
    orbitMass H X' = ∑ᶠ ω : orbitRel.Quotient H X,
      (Nat.card {y : X' // f y = ω.out} : ℝ) / Nat.card (stabilizer H ω.out) := by
  classical
  let Fm : orbitRel.Quotient H X' → orbitRel.Quotient H X :=
    Quotient.map' f (fun a b hab => by
      rw [orbitRel_apply] at hab ⊢
      obtain ⟨h, rfl⟩ := hab
      exact ⟨h, (hf h b).symm⟩)
  have hFout : ∀ ω', Fm ω' = Quotient.mk'' (f ω'.out) := by
    intro ω'; conv_lhs => rw [← Quotient.out_eq' ω']
    rfl
  have := finite_orbits_of_fiber f hf hfin
  have : Fintype (orbitRel.Quotient H X') := Fintype.ofFinite _
  have : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  unfold orbitMass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  rw [← Finset.sum_fiberwise Finset.univ Fm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hsf := sum_fiber f hf ω.out (hstab _) (hfin _)
  rw [Quotient.out_eq'] at hsf
  rw [← hsf, finsum_mem_eq_toFinset_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
  rw [hFout]

/-- **Transitive base:** if $H$ acts transitively on $X$ (every $x$ is $h x_0$), then the $H$-orbits on $X'$ are the
$\mathrm{Stab}_H(x_0)$-orbits on the fibre $f^{-1}(x_0)$, with the same stabilizers, so
$$\mathrm{mass}_H(X') = \mathrm{mass}_{\mathrm{Stab}_H(x_0)}\big(f^{-1}(x_0)\big).$$
No finiteness is assumed (both sides are `finsum`s over matching index sets). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem orbitMass_eq_fiber_of_transitive (x₀ : X) (htr : ∀ x : X, ∃ h : H, h • x₀ = x) :
    orbitMass H X' = @orbitMass (stabilizer H x₀) {y : X' // f y = x₀} _ (fiberAction f hf x₀) := by
  let _ := fiberAction f hf x₀
  symm
  refine orbitMass_eq_of_map (fun y : {y : X' // f y = x₀} => y.1) ?_ ?_ ?_
  · intro a b
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨(s : H), congrArg Subtype.val hs⟩
    · rintro ⟨h, hh⟩
      have hh' : h • b.1 = a.1 := hh
      have hhs : h ∈ stabilizer H x₀ := by
        rw [mem_stabilizer_iff]
        have := congrArg f hh'
        rw [hf, b.2, a.2] at this
        exact this
      exact ⟨⟨h, hhs⟩, Subtype.ext hh'⟩
  · intro y
    obtain ⟨h, hh⟩ := htr (f y)
    exact ⟨⟨h⁻¹ • y, by rw [hf, ← hh, inv_smul_smul]⟩, ⟨h⁻¹, rfl⟩⟩
  · intro x
    have hS : ∀ h : stabilizer H x.1, (h : H) ∈ stabilizer H x₀ := by
      intro h
      rw [mem_stabilizer_iff]
      have := congrArg f (mem_stabilizer_iff.mp h.2)
      rw [hf, x.2] at this
      exact this
    refine Nat.card_congr
      { toFun := fun h => ⟨⟨h.1, hS h⟩, mem_stabilizer_iff.mpr (Subtype.ext (mem_stabilizer_iff.mp h.2))⟩
        invFun := fun s => ⟨s.1.1, mem_stabilizer_iff.mpr (congrArg Subtype.val (mem_stabilizer_iff.mp s.2))⟩
        left_inv := fun s => rfl
        right_inv := fun h => rfl }

end Fiber

/-! ### Decomposition by a larger group -/

section Decomp

variable {G Y : Type*} [Group G] [MulAction G Y]

/-- The coset map $G/\mathrm{Stab}_G(y) \to Y$, $g\,\mathrm{Stab} \mapsto g y$. -/
def orbitMap (y : Y) : G ⧸ stabilizer G y → Y :=
  Quotient.lift (fun g => g • y) (fun a b hab => by
    have hab : a⁻¹ * b ∈ stabilizer G y := QuotientGroup.leftRel_apply.mp hab
    rw [mem_stabilizer_iff, mul_smul] at hab
    calc a • y = a • (a⁻¹ • b • y) := by rw [hab]
      _ = b • y := by rw [smul_inv_smul])

theorem orbitMap_mk (y : Y) (g : G) : orbitMap y (QuotientGroup.mk g : G ⧸ stabilizer G y) = g • y := rfl

theorem orbitMap_injective (y : Y) : Function.Injective (orbitMap (G := G) y) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [orbitMap_mk, orbitMap_mk] at hab
  rw [QuotientGroup.eq, mem_stabilizer_iff, mul_smul, ← hab, inv_smul_smul]

theorem orbitMap_smul (y : Y) (g : G) (x : G ⧸ stabilizer G y) :
    orbitMap y (g • x) = g • orbitMap y x := by
  induction x using QuotientGroup.induction_on with | H a => ?_
  show (g * a) • y = g • a • y
  rw [mul_smul]

theorem orbitMap_smul' (Γ : Subgroup G) (y : Y) (γ : Γ) (x : G ⧸ stabilizer G y) :
    orbitMap y (γ • x) = γ • orbitMap y x :=
  orbitMap_smul y (γ : G) x

/-- **Decomposition of a mass by the orbits of a larger group:** for a subgroup $\Gamma \le G$ (acting on $Y$ by
restriction) with finitely many orbits,
$$\mathrm{mass}_\Gamma(Y) = \sum_{t \in G\backslash Y}\mathrm{dcMass}\big(\Gamma, \mathrm{Stab}_G(y_t)\big),\qquad
  y_t = $ `t.out`.$$
*Proof:* the $\Gamma$-orbits inside $G y_t \cong G/\mathrm{Stab}_G(y_t)$ are the double cosets
$\Gamma\backslash G/\mathrm{Stab}_G(y_t)$, with the same stabilizers (`orbitMap`). In Weil's induction $G$ is the
adelic stabilizer of a vector, $\Gamma$ its rational points, and the $G$-orbits are the genera of the pairs. -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem orbitMass_eq_finsum_dcMass (Γ : Subgroup G) [Finite (orbitRel.Quotient Γ Y)] :
    orbitMass Γ Y = ∑ᶠ t : orbitRel.Quotient G Y, dcMass Γ (stabilizer G t.out) := by
  classical
  have : Fintype (orbitRel.Quotient Γ Y) := Fintype.ofFinite _
  -- the projection of Γ-orbits to G-orbits
  let P : orbitRel.Quotient Γ Y → orbitRel.Quotient G Y := fun ω => Quotient.mk'' ω.out
  -- each G-orbit: the Γ-orbits in it versus the double cosets
  have key : ∀ t : orbitRel.Quotient G Y,
      dcMass Γ (stabilizer G t.out) =
        ∑ ω ∈ Finset.univ.filter (fun ω => P ω = t), ((Nat.card (stabilizer Γ ω.out) : ℝ))⁻¹ := by
    intro t
    set y := t.out
    let Φ : orbitRel.Quotient Γ (G ⧸ stabilizer G y) → orbitRel.Quotient Γ Y :=
      fun η => Quotient.mk'' (orbitMap y η.out)
    have hΦinj : Function.Injective Φ := by
      intro η₁ η₂ h
      have := Quotient.exact' h
      rw [orbitRel_apply] at this
      obtain ⟨γ, hγ⟩ := this
      have hγ' : γ • orbitMap y η₂.out = orbitMap y η₁.out := hγ
      rw [← Quotient.out_eq' η₁, ← Quotient.out_eq' η₂]
      apply Quotient.sound'
      rw [orbitRel_apply]
      refine ⟨γ, orbitMap_injective y ?_⟩
      show orbitMap y (γ • η₂.out) = _
      rw [orbitMap_smul' Γ]
      exact hγ'
    have hΦrange : ∀ ω, P ω = t ↔ ∃ η, Φ η = ω := by
      intro ω
      constructor
      · intro hω
        have : (Quotient.mk'' ω.out : orbitRel.Quotient G Y) = Quotient.mk'' y := by
          rw [Quotient.out_eq']; exact hω
        have := Quotient.exact' this
        rw [orbitRel_apply] at this
        obtain ⟨g, hg⟩ := this
        have hg' : g • y = ω.out := hg
        refine ⟨Quotient.mk'' (QuotientGroup.mk g), ?_⟩
        show Quotient.mk'' (orbitMap y _) = ω
        conv_rhs => rw [← Quotient.out_eq' ω]
        apply Quotient.sound'
        rw [orbitRel_apply]
        have h1 : (Quotient.mk'' (QuotientGroup.mk g : G ⧸ stabilizer G y) :
            orbitRel.Quotient Γ (G ⧸ stabilizer G y)).out ∈ orbit Γ (QuotientGroup.mk g) :=
          out_mem_orbit _ _ rfl
        obtain ⟨γ, hγ⟩ := h1
        have hγ' : γ • (QuotientGroup.mk g : G ⧸ stabilizer G y) = _ := hγ
        refine ⟨γ, ?_⟩
        show γ • ω.out = _
        rw [← hγ', orbitMap_smul' Γ, orbitMap_mk, hg']
      · rintro ⟨η, rfl⟩
        show (Quotient.mk'' (Quotient.mk'' (orbitMap y η.out) : orbitRel.Quotient Γ Y).out :
          orbitRel.Quotient G Y) = t
        have h1 : (Quotient.mk'' (orbitMap y η.out) : orbitRel.Quotient Γ Y).out ∈
            orbit Γ (orbitMap y η.out) := out_mem_orbit _ _ rfl
        obtain ⟨γ, hγ⟩ := h1
        have hγ' : γ • orbitMap y η.out = _ := hγ
        conv_rhs => rw [← Quotient.out_eq' t]
        apply Quotient.sound'
        rw [orbitRel_apply]
        rw [← hγ']
        induction η.out using QuotientGroup.induction_on with | H g => ?_
        refine ⟨(γ : G) * g, ?_⟩
        show ((γ : G) * g) • y = γ • orbitMap y (QuotientGroup.mk g)
        rw [orbitMap_mk, mul_smul]
        rfl
    have : Finite (orbitRel.Quotient Γ (G ⧸ stabilizer G y)) := Finite.of_injective Φ hΦinj
    have : Fintype (orbitRel.Quotient Γ (G ⧸ stabilizer G y)) := Fintype.ofFinite _
    unfold dcMass orbitMass
    rw [finsum_eq_sum_of_fintype]
    have himg : Finset.univ.filter (fun ω => P ω = t) = Finset.univ.image Φ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact hΦrange ω
    rw [himg, Finset.sum_image (fun a _ b _ h => hΦinj h)]
    refine Finset.sum_congr rfl fun η _ => ?_
    -- stabilizers agree
    have h1 : (Φ η).out ∈ orbit Γ (orbitMap y η.out) := out_mem_orbit _ _ rfl
    rw [card_stabilizer_of_mem_orbit h1]
    congr 2
    refine Nat.card_congr
      { toFun := fun γ => ⟨γ.1, ?_⟩
        invFun := fun γ => ⟨γ.1, ?_⟩
        left_inv := fun γ => rfl
        right_inv := fun γ => rfl }
    · rw [mem_stabilizer_iff]
      show γ.1 • orbitMap y η.out = orbitMap y η.out
      rw [← orbitMap_smul' Γ]
      exact congrArg (orbitMap y) (mem_stabilizer_iff.mp γ.2)
    · rw [mem_stabilizer_iff]
      apply orbitMap_injective y
      rw [orbitMap_smul' Γ]
      exact mem_stabilizer_iff.mp γ.2
  -- assemble
  have hsupp : (Function.support fun t : orbitRel.Quotient G Y => dcMass Γ (stabilizer G t.out)) ⊆
      (Finset.univ.image P : Set _) := by
    intro t ht
    by_contra hne
    apply ht
    show dcMass Γ (stabilizer G t.out) = 0
    rw [key t]
    refine Finset.sum_eq_zero fun ω hω => ?_
    exfalso; apply hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨ω, hω⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  unfold orbitMass
  rw [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image P) (g := P)
    (fun ω _ => Finset.mem_image_of_mem P (Finset.mem_univ ω))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [key t]

end Decomp

/-! ### The volume of $\Gamma\backslash G$ is independent of the compact open subgroup -/

section Commensurable

variable {G : Type*} [Group G]

/-- The fibre of $G/J \to G/K$ over a point is finite when $[K : J] < \infty$. -/
theorem finite_fiber_quotient {J K : Subgroup G} (h : J ≤ K) (hfin : J.relIndex K ≠ 0) (x : G ⧸ K) :
    Finite {y : G ⧸ J // (Subgroup.quotientEquivProdOfLE h y).1 = x} := by
  apply Nat.finite_of_card_ne_zero
  rw [card_fiber_quotient h]
  exact hfin

/-- **Stabilizers stay finite under passage to a commensurable subgroup:** if $\Gamma \cap \alpha K_0\alpha^{-1}$ is
finite for every $\alpha$ and $K$ is commensurable with $K_0$, then every $\Gamma \cap \alpha K\alpha^{-1}$ is finite.
*Proof:* with $J = K \cap K_0$, $\Gamma\cap\alpha J\alpha^{-1}$ is finite (inside $\Gamma\cap\alpha K_0\alpha^{-1}$) and has
index at most $[K : J]$ in $\Gamma\cap\alpha K\alpha^{-1}$ (orbit–stabilizer on the fibre of $G/J \to G/K$). -/
theorem finite_stabilizer_of_commensurable (Γ K₀ K : Subgroup G) (hK : K.Commensurable K₀)
    (hstab : ∀ x : G ⧸ K₀, Finite (stabilizer Γ x)) (x : G ⧸ K) : Finite (stabilizer Γ x) := by
  classical
  induction x using QuotientGroup.induction_on with | H g => ?_
  set J := K ⊓ K₀
  have hJK : J ≤ K := inf_le_left
  have hJK₀ : J ≤ K₀ := inf_le_right
  have hJfin : J.relIndex K ≠ 0 := by
    rw [show J = K₀ ⊓ K from inf_comm _ _, Subgroup.inf_relIndex_right]
    exact hK.2.relIndex_ne_zero
  let f : G ⧸ J → G ⧸ K := fun y => (Subgroup.quotientEquivProdOfLE hJK y).1
  have hf : ∀ (γ : Γ) (y : G ⧸ J), f (γ • y) = γ • f y := by
    intro γ y
    induction y using QuotientGroup.induction_on with | H a => rfl
  set x : G ⧸ K := QuotientGroup.mk g
  set S := stabilizer Γ x
  let _ := fiberAction f hf x
  have hFb : Finite {y : G ⧸ J // f y = x} := finite_fiber_quotient hJK hJfin x
  let y₀ : {y : G ⧸ J // f y = x} := ⟨QuotientGroup.mk g, rfl⟩
  have hT : Finite (stabilizer S y₀) := by
    have := hstab (QuotientGroup.mk g)
    refine Finite.of_injective (fun s : stabilizer S y₀ =>
      (⟨s.1.1, ?_⟩ : stabilizer Γ (QuotientGroup.mk g : G ⧸ K₀)))
      (fun a b h => by
        apply Subtype.ext; apply Subtype.ext
        have h' := congrArg (fun z : stabilizer Γ (QuotientGroup.mk g : G ⧸ K₀) => (z : Γ)) h
        exact h')
    have h1 : (s.1.1 : Γ) • (QuotientGroup.mk g : G ⧸ J) = QuotientGroup.mk g :=
      congrArg Subtype.val (mem_stabilizer_iff.mp s.2)
    have h2 : s.1.1 ∈ stabilizer Γ (QuotientGroup.mk g : G ⧸ J) := mem_stabilizer_iff.mpr h1
    rw [mem_stabilizer_coset] at h2 ⊢
    exact hJK₀ h2
  have hidx : (stabilizer S y₀).index ≠ 0 := by
    rw [index_stabilizer]
    have : (orbit S y₀).Finite := Set.toFinite _
    exact (Set.ncard_pos this).mpr ⟨y₀, mem_orbit_self y₀⟩ |>.ne'
  have hcard := (stabilizer S y₀).card_mul_index
  apply Nat.finite_of_card_ne_zero
  rw [← hcard]
  exact mul_ne_zero Nat.card_pos.ne' hidx

/-- **Finitely many double cosets stay finitely many** for a commensurable subgroup. -/
theorem finite_orbits_of_commensurable (Γ K₀ K : Subgroup G) (hK : K.Commensurable K₀)
    [Finite (orbitRel.Quotient Γ (G ⧸ K₀))] : Finite (orbitRel.Quotient Γ (G ⧸ K)) := by
  set J := K ⊓ K₀
  have hJK : J ≤ K := inf_le_left
  have hJK₀ : J ≤ K₀ := inf_le_right
  have hJfin₀ : J.relIndex K₀ ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]; exact hK.1.relIndex_ne_zero
  have : Finite (orbitRel.Quotient Γ (G ⧸ J)) :=
    finite_orbits_of_fiber (fun y => (Subgroup.quotientEquivProdOfLE hJK₀ y).1)
      (fun γ y => by induction y using QuotientGroup.induction_on with | H a => rfl)
      (finite_fiber_quotient hJK₀ hJfin₀)
  let π : orbitRel.Quotient Γ (G ⧸ J) → orbitRel.Quotient Γ (G ⧸ K) :=
    Quotient.map' (fun y => (Subgroup.quotientEquivProdOfLE hJK y).1) (fun a b hab => by
      rw [orbitRel_apply] at hab ⊢
      obtain ⟨γ, rfl⟩ := hab
      refine ⟨γ, ?_⟩
      induction b using QuotientGroup.induction_on with | H a => rfl)
  refine Finite.of_surjective π fun ω => ?_
  induction ω using Quotient.inductionOn' with | h x => ?_
  induction x using QuotientGroup.induction_on with | H g => ?_
  exact ⟨Quotient.mk'' (QuotientGroup.mk g), rfl⟩

/-- **$\mathrm{vol}(\Gamma\backslash G)$ does not depend on the compact open subgroup:** for $K$ commensurable with $K_0$
and the Haar measure $\mu$ = `idxVol K₀ c` ($\mu(K_0) = c$), with finitely many double cosets
$\Gamma\backslash G/K_0$ and finite $\Gamma\cap\alpha K_0\alpha^{-1}$,
$$\mathrm{dcMass}(\Gamma, K)\cdot\mu(K) = c\cdot\mathrm{dcMass}(\Gamma, K_0).$$
(Weil 1982, §2.4, p. 23 and Lemma 2.4.2, p. 26 (discrete version); this extends `mass_mul_vol_eq` from $K \le K_0$ to commensurable $K$.)
*Proof:* compare both with $J = K \cap K_0$ (`dcMass_of_le` twice). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem dcMass_mul_idxVol (Γ K₀ K : Subgroup G) (c : ℝ) (hK : K.Commensurable K₀)
    [Finite (orbitRel.Quotient Γ (G ⧸ K₀))] (hstab : ∀ x : G ⧸ K₀, Finite (stabilizer Γ x)) :
    dcMass Γ K * idxVol K₀ c K = c * dcMass Γ K₀ := by
  set J := K ⊓ K₀
  have hJK : J ≤ K := inf_le_left
  have hJK₀ : J ≤ K₀ := inf_le_right
  have hJfin : J.relIndex K ≠ 0 := by
    rw [show J = K₀ ⊓ K from inf_comm _ _, Subgroup.inf_relIndex_right]
    exact hK.2.relIndex_ne_zero
  have hJfin₀ : J.relIndex K₀ ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]; exact hK.1.relIndex_ne_zero
  have := finite_orbits_of_commensurable Γ K₀ K hK
  have e1 := dcMass_of_le Γ hJK₀ hJfin₀ hstab
  have e2 := dcMass_of_le Γ hJK hJfin (finite_stabilizer_of_commensurable Γ K₀ K hK hstab)
  have hr1 : J.relIndex K = K₀.relIndex K := by
    rw [show J = K₀ ⊓ K from inf_comm _ _, Subgroup.inf_relIndex_right]
  have hr2 : J.relIndex K₀ = K.relIndex K₀ := Subgroup.inf_relIndex_right K K₀
  unfold idxVol
  rw [← hr1, ← hr2]
  have h1 : (J.relIndex K : ℝ) ≠ 0 := by exact_mod_cast hJfin
  have h2 : (J.relIndex K₀ : ℝ) ≠ 0 := by exact_mod_cast hJfin₀
  have : dcMass Γ K = (J.relIndex K₀ : ℝ) / J.relIndex K * dcMass Γ K₀ := by
    rw [e1] at e2
    field_simp
    linarith
  rw [this]
  field_simp

end Commensurable

end QuadFormsKB.Tamagawa
