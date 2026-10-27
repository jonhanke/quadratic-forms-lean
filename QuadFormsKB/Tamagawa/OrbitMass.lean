/-
# Orbit masses and double-coset masses

**Layer:** pure group theory (any group $H$ acting on any set $X$).

**Defines**
* `orbitMass H X` $= \sum_{\omega \in H\backslash X} 1/|\mathrm{Stab}_H(x_\omega)|$, the **mass** of the action (a `finsum`
  over the orbits; $x_\omega$ = `ω.out` is any point of the orbit, the stabilizer order does not depend on it,
  `card_stabilizer_of_mem_orbit`). For a finite group it is $|X|/|H|$ (`orbitMass_of_finite`).
* `dcMass Γ K` $= \sum_{\Gamma\alpha K \in \Gamma\backslash G/K} 1/|\Gamma \cap \alpha K\alpha^{-1}|$, the mass of $\Gamma$ acting on
  $G/K$ (`dcMass`, `stabilizer_coset`).

**Proves**
* `orbitMass_eq_of_map`: masses agree along a map inducing a bijection of orbits and preserving stabilizer orders;
* `orbitMass_fiber` (**fibration**): for an $H$-equivariant $f : X' \to X$ all of whose fibres have $d$ elements,
  $\mathrm{mass}_H(X') = d \cdot \mathrm{mass}_H(X)$;
* `orbitMass_subgroup` (**restriction**): for $H' \le H$ of finite index, $\mathrm{mass}_{H'}(X) = [H : H']\,\mathrm{mass}_H(X)$;
* `dcMass_of_le`: for $K' \le K$ of finite index, $\mathrm{mass}(\Gamma\backslash G/K') = [K:K']\,\mathrm{mass}(\Gamma\backslash G/K)$;
* `dcMass_normal`: if $G = N K$ then $\mathrm{mass}(\Gamma\cap N \backslash N / K \cap N) = [\Gamma : \Gamma \cap N]\,\mathrm{mass}(\Gamma\backslash G/K)$
  (used with $G = O(V)(\mathbb A_f)$, $N = SO(V)(\mathbb A_f)$: the factor $2$ between the $O$- and $SO$-masses).

These are the discrete content of "volume of $\Gamma\backslash G$" for a group with a compact open subgroup $K$ and
a discrete $\Gamma$ with finite $\Gamma \cap \alpha K \alpha^{-1}$: $\mathrm{vol}(\Gamma\backslash G) = \mu(K) \cdot \mathrm{dcMass}(\Gamma, K)$,
independent of $K$ by `dcMass_of_le` (Weil, *Adeles and Algebraic Groups*, §2.4, p. 23 and Lemma 2.4.2, p. 26 (discrete version); Hanke AWS notes §4.6).
-/
import Mathlib
import QuadFormsKB.Citation

open MulAction

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

/-! ### The orbit mass -/

/-- **The mass of a group action** $H \curvearrowright X$:
$$\mathrm{mass}_H(X) = \sum_{\omega \in H\backslash X} \frac{1}{|\mathrm{Stab}_H(x_\omega)|},$$
a `finsum` over the orbit space `orbitRel.Quotient H X`, with $x_\omega$ = `ω.out` (any point of $\omega$:
`card_stabilizer_of_mem_orbit`). Infinite stabilizers contribute $0$ (`Nat.card` of an infinite type is $0$),
and the `finsum` is $0$ if infinitely many orbits contribute; the theorems below assume finitely many orbits and
finite stabilizers. For $X$ the genus of a lattice and $H = O(V)(F)$ this is the mass of the genus
(`Tamagawa.mass_eq_orbitMass`). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
def orbitMass (H X : Type*) [Group H] [MulAction H X] : ℝ :=
  ∑ᶠ ω : orbitRel.Quotient H X, ((Nat.card (stabilizer H ω.out) : ℝ))⁻¹

variable {H X : Type*} [Group H] [MulAction H X]

/-- Points of one orbit have stabilizers of the same order (they are conjugate). -/
theorem card_stabilizer_of_mem_orbit {x y : X} (h : y ∈ orbit H x) :
    Nat.card (stabilizer H y) = Nat.card (stabilizer H x) := by
  obtain ⟨g, rfl⟩ := h
  exact (Nat.card_congr (stabilizerEquivStabilizer (G := H) (a := x) rfl).toEquiv).symm

theorem out_mem_orbit (ω : orbitRel.Quotient H X) (x : X) (hx : Quotient.mk'' x = ω) :
    ω.out ∈ orbit H x := by
  rw [← orbitRel_apply]
  have : (Quotient.mk'' ω.out : orbitRel.Quotient H X) = Quotient.mk'' x := by
    rw [Quotient.out_eq', hx]
  exact Quotient.exact' this

/-- **Transfer of masses** along a map $g : X_1 \to X_2$ (for actions of possibly different groups) which induces
a bijection of orbit spaces ($a \sim b \iff g(a) \sim g(b)$, and every orbit of $X_2$ meets $g(X_1)$) and preserves the
orders of stabilizers. -/
theorem orbitMass_eq_of_map {H₁ X₁ H₂ X₂ : Type*} [Group H₁] [MulAction H₁ X₁] [Group H₂]
    [MulAction H₂ X₂] (g : X₁ → X₂) (horb : ∀ a b : X₁, a ∈ orbit H₁ b ↔ g a ∈ orbit H₂ (g b))
    (hsurj : ∀ y : X₂, ∃ x, g x ∈ orbit H₂ y)
    (hstab : ∀ x, Nat.card (stabilizer H₂ (g x)) = Nat.card (stabilizer H₁ x)) :
    orbitMass H₁ X₁ = orbitMass H₂ X₂ := by
  let G : orbitRel.Quotient H₁ X₁ → orbitRel.Quotient H₂ X₂ :=
    Quotient.map' g (fun a b hab => by
      rw [orbitRel_apply] at hab ⊢; exact (horb a b).1 hab)
  have hG : ∀ x, G (Quotient.mk'' x) = Quotient.mk'' (g x) := fun _ => rfl
  have hbij : Function.Bijective G := by
    constructor
    · intro ω₁ ω₂ h
      induction ω₁ using Quotient.inductionOn' with | h a => ?_
      induction ω₂ using Quotient.inductionOn' with | h b => ?_
      rw [hG, hG] at h
      apply Quotient.sound'
      rw [orbitRel_apply]
      have := Quotient.exact' h
      rw [orbitRel_apply] at this
      exact (horb a b).2 this
    · intro ω
      induction ω using Quotient.inductionOn' with | h y => ?_
      obtain ⟨x, hx⟩ := hsurj y
      exact ⟨Quotient.mk'' x, by rw [hG]; exact Quotient.sound' (by rw [orbitRel_apply]; exact hx)⟩
  unfold orbitMass
  rw [← finsum_comp_equiv (Equiv.ofBijective G hbij)]
  congr 1
  ext ω
  simp only [Equiv.ofBijective_apply]
  have h1 : (G ω).out ∈ orbit H₂ (g ω.out) := by
    apply out_mem_orbit
    conv_rhs => rw [← Quotient.out_eq' ω]
    exact (hG _).symm
  rw [card_stabilizer_of_mem_orbit h1, hstab]

/-- **Class formula, mass form:** for a finite group $S$ acting on a finite set $Y$,
$\sum_{\eta \in S\backslash Y} 1/|\mathrm{Stab}_S(y_\eta)| = |Y|/|S|$. -/
theorem orbitMass_of_finite (S Y : Type*) [Group S] [MulAction S Y] [Finite S] [Finite Y] :
    orbitMass S Y = (Nat.card Y : ℝ) / Nat.card S := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have : Fintype Y := Fintype.ofFinite Y
  have hS : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
  have hY : Nat.card Y = ∑ η : orbitRel.Quotient S Y, Nat.card (S ⧸ stabilizer S η.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbitsQuotientStabilizer S Y), Nat.card_sigma]
  unfold orbitMass
  rw [finsum_eq_sum_of_fintype, hY, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun η _ => ?_
  have h := (stabilizer S η.out).card_mul_index
  have hpos : (0 : ℝ) < Nat.card (stabilizer S η.out) := by exact_mod_cast Nat.card_pos
  rw [Subgroup.index] at h
  rw [eq_div_iff hS.ne', ← h]
  push_cast
  field_simp

/-! ### Fibrations -/

section Fiber

variable {X' : Type*} [MulAction H X'] (f : X' → X) (hf : ∀ (h : H) (y : X'), f (h • y) = h • f y)

include hf

/-- The stabilizer of $x$ acts on the fibre $f^{-1}(x)$. -/
@[instance_reducible]
def fiberAction (x : X) : MulAction (stabilizer H x) {y : X' // f y = x} where
  smul s y := ⟨(s : H) • y.1, by rw [hf, y.2]; exact s.2⟩
  one_smul y := Subtype.ext (one_smul H y.1)
  mul_smul a b y := Subtype.ext (mul_smul (a : H) (b : H) y.1)

/-- **Orbits in a fibre.** For $x \in X$ with stabilizer $S$, the $S$-orbits on $f^{-1}(x)$ are in bijection with the
$H$-orbits in $X'$ lying over the orbit of $x$, and stabilizers correspond: $\mathrm{Stab}_H(y) = \mathrm{Stab}_S(y)$. -/
theorem sum_fiber [Finite (orbitRel.Quotient H X')] (x : X) (hS : Finite (stabilizer H x))
    (hY : Finite {y : X' // f y = x}) :
    ∑ᶠ ω' ∈ {ω' : orbitRel.Quotient H X' | (Quotient.mk'' (f ω'.out) : orbitRel.Quotient H X) =
      Quotient.mk'' x}, ((Nat.card (stabilizer H ω'.out) : ℝ))⁻¹ =
      (Nat.card {y : X' // f y = x} : ℝ) / Nat.card (stabilizer H x) := by
  classical
  let _ := fiberAction f hf x
  let S := stabilizer H x
  let Y := {y : X' // f y = x}
  rw [← orbitMass_of_finite S Y]
  -- the map Y → X' (inclusion) and the restriction of masses
  set T : Set (orbitRel.Quotient H X') :=
    {ω' | (Quotient.mk'' (f ω'.out) : orbitRel.Quotient H X) = Quotient.mk'' x}
  have hT : ∀ ω' : orbitRel.Quotient H X', ω' ∈ T ↔ ∃ y : Y, Quotient.mk'' y.1 = ω' := by
    intro ω'
    constructor
    · intro hω
      have := Quotient.exact' hω
      rw [orbitRel_apply] at this
      obtain ⟨h, hh⟩ := this
      refine ⟨⟨h⁻¹ • ω'.out, by rw [hf, ← hh, inv_smul_smul]⟩, ?_⟩
      conv_rhs => rw [← Quotient.out_eq' ω']
      exact Quotient.sound' (by rw [orbitRel_apply]; exact ⟨h⁻¹, rfl⟩)
    · rintro ⟨y, rfl⟩
      show (Quotient.mk'' (f (Quotient.mk'' y.1 : orbitRel.Quotient H X').out) :
        orbitRel.Quotient H X) = _
      have h1 : (Quotient.mk'' y.1 : orbitRel.Quotient H X').out ∈ orbit H y.1 :=
        out_mem_orbit _ _ rfl
      obtain ⟨h, hh⟩ := h1
      apply Quotient.sound'
      rw [orbitRel_apply]
      refine ⟨h, ?_⟩
      change h • x = f ((Quotient.mk'' y.1 : orbitRel.Quotient H X').out)
      have hy : f y.1 = x := y.2
      calc h • x = h • f y.1 := by rw [hy]
        _ = f (h • y.1) := (hf h y.1).symm
        _ = _ := congrArg f hh
  -- the bijection between S-orbits on Y and T
  let G : orbitRel.Quotient S Y → T := fun η =>
    ⟨Quotient.mk'' (η.out : Y).1, (hT _).2 ⟨_, rfl⟩⟩
  have hGinj : Function.Injective G := by
    intro η₁ η₂ h
    have h' := congrArg Subtype.val h
    simp only [G] at h'
    have := Quotient.exact' h'
    rw [orbitRel_apply] at this
    obtain ⟨g, hg⟩ := this
    have hgS : g ∈ S := by
      rw [mem_stabilizer_iff]
      have := congrArg f hg
      rw [hf, (η₂.out).2, (η₁.out).2] at this
      exact this
    rw [← Quotient.out_eq' η₁, ← Quotient.out_eq' η₂]
    apply Quotient.sound'
    rw [orbitRel_apply]
    exact ⟨⟨g, hgS⟩, Subtype.ext hg⟩
  have hGsurj : Function.Surjective G := by
    rintro ⟨ω', hω'⟩
    obtain ⟨y, rfl⟩ := (hT ω').1 hω'
    refine ⟨Quotient.mk'' y, Subtype.ext ?_⟩
    simp only [G]
    apply Quotient.sound'
    rw [orbitRel_apply]
    have h1 : (Quotient.mk'' y : orbitRel.Quotient S Y).out ∈ orbit S y := out_mem_orbit _ _ rfl
    obtain ⟨s, hs⟩ := h1
    exact ⟨(s : H), congrArg Subtype.val hs⟩
  have hfinT : (T).Finite := Set.toFinite T
  rw [finsum_mem_eq_finite_toFinset_sum _ hfinT, orbitMass]
  have : Finite (orbitRel.Quotient S Y) := Quotient.finite _
  have : Fintype (orbitRel.Quotient S Y) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_coe_sort hfinT.toFinset]
  refine (Fintype.sum_bijective (fun η => (⟨(G η).1, by simp [(G η).2]⟩ : hfinT.toFinset))
    ?_ _ _ ?_).symm
  · constructor
    · intro a b hab
      apply hGinj
      have := congrArg Subtype.val hab
      exact Subtype.ext this
    · rintro ⟨ω', hω'⟩
      obtain ⟨η, hη⟩ := hGsurj ⟨ω', by simpa using hω'⟩
      exact ⟨η, Subtype.ext (show (G η).1 = ω' from congrArg Subtype.val hη)⟩
  · intro η
    simp only [G]
    -- Stab_H of the out of the H-orbit of y equals Stab_S(y)
    have h1 : (Quotient.mk'' (η.out : Y).1 : orbitRel.Quotient H X').out ∈ orbit H (η.out : Y).1 :=
      out_mem_orbit _ _ rfl
    rw [card_stabilizer_of_mem_orbit h1]
    congr 2
    refine Nat.card_congr
      { invFun := fun h => ⟨⟨h.1, ?_⟩, ?_⟩
        toFun := fun s => ⟨s.1.1, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun h => rfl }
    · rw [mem_stabilizer_iff]
      exact congrArg Subtype.val (mem_stabilizer_iff.mp s.2)
    · rw [mem_stabilizer_iff]
      have := congrArg f (mem_stabilizer_iff.mp h.2)
      rw [hf, (η.out).2] at this
      exact this
    · rw [mem_stabilizer_iff]
      exact Subtype.ext (mem_stabilizer_iff.mp h.2)

/-- **The fibration formula** for masses: if $f : X' \to X$ is $H$-equivariant, $H\backslash X$ is finite, all
stabilizers in $X$ are finite and every fibre $f^{-1}(x)$ has exactly $d$ elements, then
$$\mathrm{mass}_H(X') = d \cdot \mathrm{mass}_H(X).$$
*Proof:* the $H$-orbits over the orbit of $x$ are the $\mathrm{Stab}_H(x)$-orbits on $f^{-1}(x)$ (`sum_fiber`), and the
class formula gives $\sum 1/|\mathrm{Stab}| = d/|\mathrm{Stab}_H(x)|$ there (`orbitMass_of_finite`). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem orbitMass_fiber [Finite (orbitRel.Quotient H X)] (hstab : ∀ x : X, Finite (stabilizer H x))
    (d : ℕ) (hd : ∀ x : X, Nat.card {y : X' // f y = x} = d) (hfin : ∀ x, Finite {y : X' // f y = x}) :
    orbitMass H X' = d * orbitMass H X := by
  classical
  -- finiteness of the orbits of X'
  let F : orbitRel.Quotient H X' → orbitRel.Quotient H X :=
    Quotient.map' f (fun a b hab => by
      rw [orbitRel_apply] at hab ⊢
      obtain ⟨h, rfl⟩ := hab
      exact ⟨h, (hf h b).symm⟩)
  have hF : ∀ x, F (Quotient.mk'' x) = Quotient.mk'' (f x) := fun _ => rfl
  have hFout : ∀ ω', F ω' = Quotient.mk'' (f ω'.out) := by
    intro ω'; conv_lhs => rw [← Quotient.out_eq' ω']
    exact hF _
  have hFfib : ∀ ω : orbitRel.Quotient H X, (F ⁻¹' {ω}).Finite := by
    intro ω
    let _ := fiberAction f hf ω.out
    have : Finite {y : X' // f y = ω.out} := hfin _
    have hsub : F ⁻¹' {ω} ⊆ Set.range (fun y : {y : X' // f y = ω.out} =>
        (Quotient.mk'' y.1 : orbitRel.Quotient H X')) := by
      intro ω' hω'
      have hω'' : F ω' = ω := hω'
      have : (Quotient.mk'' (f ω'.out) : orbitRel.Quotient H X) = Quotient.mk'' ω.out := by
        rw [Quotient.out_eq', ← hω'', hFout]
      have := Quotient.exact' this
      rw [orbitRel_apply] at this
      obtain ⟨h, hh⟩ := this
      refine ⟨⟨h⁻¹ • ω'.out, by rw [hf, ← hh, inv_smul_smul]⟩, ?_⟩
      conv_rhs => rw [← Quotient.out_eq' ω']
      exact Quotient.sound' (by rw [orbitRel_apply]; exact ⟨h⁻¹, rfl⟩)
    exact (Set.finite_range _).subset hsub
  have : Finite (orbitRel.Quotient H X') := by
    have h := Set.Finite.preimage' (Set.finite_univ (α := orbitRel.Quotient H X)) (fun ω _ => hFfib ω)
    rw [Set.preimage_univ] at h
    exact Set.finite_univ_iff.mp h
  have : Fintype (orbitRel.Quotient H X') := Fintype.ofFinite _
  have : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  unfold orbitMass
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ F]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hsf := sum_fiber f hf ω.out (hstab _) (hfin _)
  rw [hd, Quotient.out_eq'] at hsf
  rw [div_eq_mul_inv] at hsf
  rw [← hsf]
  rw [finsum_mem_eq_toFinset_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset, Set.mem_ofPred_eq]
  rw [hFout]

end Fiber

/-! ### Restriction to a subgroup of finite index -/

section Subgroup

/-- **Restriction of masses to a subgroup of finite index:** for $H' \le H$ with $[H : H'] < \infty$, finitely many
$H$-orbits on $X$ and finite stabilizers,
$$\mathrm{mass}_{H'}(X) = [H : H']\cdot\mathrm{mass}_H(X).$$
*Proof:* $H'ackslash X \simeq Hackslash(H/H' 	imes X)$ with equal stabilizers, and the projection
$H/H' 	imes X 	o X$ has fibres of size $[H:H']$ (`orbitMass_fiber`). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem orbitMass_subgroup (H' : Subgroup H) [H'.FiniteIndex] [Finite (orbitRel.Quotient H X)]
    (hstab : ∀ x : X, Finite (stabilizer H x)) :
    orbitMass H' X = H'.index * orbitMass H X := by
  classical
  -- step 1: H' acting on X versus H acting on H/H' × X
  have h1 : orbitMass H' X = orbitMass H ((H ⧸ H') × X) := by
    refine orbitMass_eq_of_map (fun x => ((QuotientGroup.mk 1 : H ⧸ H'), x)) ?_ ?_ ?_
    · intro a b
      constructor
      · rintro ⟨h, rfl⟩
        refine ⟨(h : H), ?_⟩
        show ((h : H) • (QuotientGroup.mk 1 : H ⧸ H'), (h : H) • b) = _
        refine Prod.ext ?_ rfl
        show (QuotientGroup.mk ((h : H) * 1) : H ⧸ H') = QuotientGroup.mk 1
        rw [QuotientGroup.eq]; simp
      · rintro ⟨h, hh⟩
        have e1 := congrArg Prod.fst hh
        have e2 := congrArg Prod.snd hh
        change (QuotientGroup.mk (h * 1) : H ⧸ H') = QuotientGroup.mk 1 at e1
        rw [QuotientGroup.eq] at e1
        refine ⟨⟨h, by simpa using e1⟩, ?_⟩
        exact e2
    · rintro ⟨c, y⟩
      induction c using QuotientGroup.induction_on with | H g => ?_
      refine ⟨g⁻¹ • y, g⁻¹, ?_⟩
      show (g⁻¹ • (QuotientGroup.mk g : H ⧸ H'), g⁻¹ • y) = _
      refine Prod.ext ?_ rfl
      show (QuotientGroup.mk (g⁻¹ * g) : H ⧸ H') = _
      rw [inv_mul_cancel]
    · intro x
      refine Nat.card_congr
        { toFun := fun h => ⟨⟨h.1, ?_⟩, ?_⟩
          invFun := fun h => ⟨h.1.1, ?_⟩
          left_inv := fun h => rfl
          right_inv := fun h => rfl }
      · have e1 := congrArg Prod.fst (mem_stabilizer_iff.mp h.2)
        change (QuotientGroup.mk (h.1 * 1) : H ⧸ H') = QuotientGroup.mk 1 at e1
        rw [QuotientGroup.eq] at e1
        simpa using e1
      · rw [mem_stabilizer_iff]
        exact congrArg Prod.snd (mem_stabilizer_iff.mp h.2)
      · rw [mem_stabilizer_iff]
        refine Prod.ext ?_ (mem_stabilizer_iff.mp h.2)
        show (QuotientGroup.mk (h.1.1 * 1) : H ⧸ H') = QuotientGroup.mk 1
        rw [QuotientGroup.eq]; simp
  -- step 2: the projection to X
  have h2 := orbitMass_fiber (X' := (H ⧸ H') × X) (Prod.snd) (fun h y => rfl) hstab H'.index
    (fun x => by
      rw [Subgroup.index, ← Nat.card_congr
        { toFun := fun p => p.1.1
          invFun := fun c => ⟨(c, x), rfl⟩
          left_inv := fun p => by
            rcases p with ⟨⟨c, y⟩, hy⟩
            simp only at hy; subst hy; rfl
          right_inv := fun c => rfl : {p : (H ⧸ H') × X // p.2 = x} ≃ H ⧸ H'}])
    (fun x => Finite.of_injective (fun p : {p : (H ⧸ H') × X // p.2 = x} => p.1.1) (by
      rintro ⟨⟨c, y⟩, hy⟩ ⟨⟨c', y'⟩, hy'⟩ h
      simp only at hy hy' h
      subst hy hy' h; rfl))
  rw [h1, h2]

end Subgroup

/-! ### Double cosets -/

section DoubleCoset

variable {G : Type*} [Group G]

/-- **The mass of a double coset space** $\Gammaackslash G/K$:
$$\mathrm{dcMass}(\Gamma, K) = \sum_{\Gammalpha K} rac{1}{|\Gamma \cap lpha K lpha^{-1}|},$$
the mass of $\Gamma$ acting on $G/K$ by left multiplication (the stabilizer of $lpha K$ is $\Gamma \cap lpha Klpha^{-1}$,
`mem_stabilizer_coset`). For a unimodular locally compact $G$ with compact open $K$ and discrete $\Gamma$ with finite
$\Gamma \cap lpha Klpha^{-1}$, $\mathrm{vol}(\Gammaackslash G) = \mu(K)\cdot\mathrm{dcMass}(\Gamma, K)$, since
$\Gammaackslash\Gammalpha K \cong (\Gamma\caplpha Klpha^{-1})ackslashlpha K$ (Weil 1982, §2.4, p. 23 and Lemma 2.4.2, p. 26 (discrete version); AWS notes
(4.11)). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
def dcMass (Γ K : Subgroup G) : ℝ := orbitMass Γ (G ⧸ K)

/-- The stabilizer of $lpha K$ in $\Gamma$ is $\Gamma \cap lpha Klpha^{-1}$. -/
theorem mem_stabilizer_coset (Γ K : Subgroup G) (α : G) (γ : Γ) :
    γ ∈ stabilizer Γ (QuotientGroup.mk α : G ⧸ K) ↔ α⁻¹ * (γ : G) * α ∈ K := by
  rw [mem_stabilizer_iff]
  show (QuotientGroup.mk ((γ : G) * α) : G ⧸ K) = QuotientGroup.mk α ↔ _
  rw [QuotientGroup.eq, ← K.inv_mem_iff]
  simp [mul_assoc]

/-- The fibre of $G/K' 	o G/K$ ($K' \le K$) over any point has $[K : K']$ elements. -/
theorem card_fiber_quotient {K' K : Subgroup G} (h : K' ≤ K) (x : G ⧸ K) :
    Nat.card {y : G ⧸ K' // (Subgroup.quotientEquivProdOfLE h y).1 = x} = K'.relIndex K := by
  rw [Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr ((Equiv.subtypeEquiv (q := fun p : (G ⧸ K) × (K ⧸ K'.subgroupOf K) => p.1 = x)
    (Subgroup.quotientEquivProdOfLE h) (fun _ => Iff.rfl)).trans
    { toFun := fun p => p.1.2
      invFun := fun c => ⟨(x, c), rfl⟩
      left_inv := fun p => by
        rcases p with ⟨⟨a, c⟩, ha⟩
        obtain rfl : a = x := ha
        rfl
      right_inv := fun c => rfl })

/-- **Change of the compact open subgroup:** for $K' \le K$ of finite index (and finitely many double cosets
$\Gammaackslash G/K$ with finite $\Gamma \cap lpha Klpha^{-1}$),
$$\mathrm{dcMass}(\Gamma, K') = [K : K']\cdot\mathrm{dcMass}(\Gamma, K).$$
So $\mu(K)\cdot\mathrm{dcMass}(\Gamma, K)$ is the same for every $K$ in a commensurability class whenever
$\mu(K') = \mu(K)/[K:K']$, i.e. "$\mathrm{vol}(\Gammaackslash G)$" is well defined (`quotVol_eq`). -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem dcMass_of_le (Γ : Subgroup G) {K' K : Subgroup G} (h : K' ≤ K) (hfin : K'.relIndex K ≠ 0)
    [Finite (orbitRel.Quotient Γ (G ⧸ K))] (hstab : ∀ x : G ⧸ K, Finite (stabilizer Γ x)) :
    dcMass Γ K' = K'.relIndex K * dcMass Γ K := by
  have hfib := card_fiber_quotient h
  unfold dcMass
  refine orbitMass_fiber (fun y => (Subgroup.quotientEquivProdOfLE h y).1) ?_ hstab _ hfib ?_
  · intro γ y
    induction y using QuotientGroup.induction_on with | H g => rfl
  · intro x
    apply Nat.finite_of_card_ne_zero
    rw [hfib]; exact hfin

/-- **Passing to a normal-type subgroup $N$ with $G = NK$:** if every $g \in G$ is $nk$ with $n \in N$, $k \in K$, then
$N/(K\cap N) \cong G/K$ and
$$\mathrm{dcMass}_N(\Gamma \cap N, K \cap N) = [\Gamma : \Gamma\cap N]\cdot\mathrm{dcMass}_G(\Gamma, K),$$
where the left side is the mass of $\Gamma \cap N$ (`Γ.subgroupOf N`) acting on $N/(K \cap N)$. With
$G = O(V)(\mathbb A_f)$, $N = SO(V)(\mathbb A_f)$, $\Gamma = O(V)(F)$, $K = O(\hat L)$ this is $\mathrm{mass}_{SO} = 2\,\mathrm{mass}_O$. -/
@[kb "weil1982" "§2.4, p. 23 (τ = volume of the quotient); Lemma 2.4.2, p. 26 (unfolding over a discrete group, discrete version)"]
theorem dcMass_normal (Γ K N : Subgroup G) (hNK : ∀ g : G, ∃ n ∈ N, ∃ k ∈ K, g = n * k)
    [(N.subgroupOf Γ).FiniteIndex] [Finite (orbitRel.Quotient Γ (G ⧸ K))]
    (hstab : ∀ x : G ⧸ K, Finite (stabilizer Γ x)) :
    dcMass (Γ.subgroupOf N) (K.subgroupOf N) = (N.subgroupOf Γ).index * dcMass Γ K := by
  classical
  unfold dcMass
  rw [← orbitMass_subgroup (N.subgroupOf Γ) hstab]
  -- the map N/(K ∩ N) → G/K
  let ι : N ⧸ K.subgroupOf N → G ⧸ K :=
    Quotient.map' (fun n : N => (n : G)) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply] at hab ⊢
      exact (Subgroup.mem_subgroupOf).mp hab)
  have hι : ∀ n : N, ι (QuotientGroup.mk n) = QuotientGroup.mk (n : G) := fun _ => rfl
  have hιinj : Function.Injective ι := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hι, hι, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hab
  refine orbitMass_eq_of_map ι ?_ ?_ ?_
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    constructor
    · rintro ⟨γ, hγ⟩
      refine ⟨⟨⟨((γ : N) : G), γ.2⟩, by simp [Subgroup.mem_subgroupOf]⟩, ?_⟩
      rw [← hγ]
      rfl
    · rintro ⟨γ, hγ⟩
      have hγN : ((γ : Γ) : G) ∈ N := Subgroup.mem_subgroupOf.mp γ.2
      refine ⟨⟨⟨((γ : Γ) : G), hγN⟩, by simp [Subgroup.mem_subgroupOf]⟩, ?_⟩
      apply hιinj
      rw [← hγ]
      rfl
  · intro y
    induction y using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨n, hn, k, hk, rfl⟩ := hNK g
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, 1, ?_⟩
    show (QuotientGroup.mk (1 * (n * k)) : G ⧸ K) = QuotientGroup.mk n
    rw [one_mul, QuotientGroup.eq]
    simpa using hk
  · have hcomm : ∀ (γ : Γ.subgroupOf N) (y : N ⧸ K.subgroupOf N),
        ι (γ • y) = ((γ : N) : G) • ι y := by
      intro γ y
      induction y using QuotientGroup.induction_on with | H a => rfl
    intro x
    refine Nat.card_congr
      { toFun := fun γ => ⟨⟨⟨((γ.1 : Γ) : G), Subgroup.mem_subgroupOf.mp γ.1.2⟩, by
            simp [Subgroup.mem_subgroupOf]⟩, ?_⟩
        invFun := fun γ => ⟨⟨⟨((γ.1 : N) : G), γ.1.2⟩, by
            simp [Subgroup.mem_subgroupOf]⟩, ?_⟩
        left_inv := fun γ => rfl
        right_inv := fun γ => rfl }
    · rw [mem_stabilizer_iff]
      apply hιinj
      rw [hcomm]
      exact mem_stabilizer_iff.mp γ.2
    · rw [mem_stabilizer_iff]
      have := congrArg ι (mem_stabilizer_iff.mp γ.2)
      rw [hcomm] at this
      exact this

end DoubleCoset

end QuadFormsKB.Tamagawa
