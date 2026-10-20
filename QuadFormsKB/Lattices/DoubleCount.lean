/-
# Averaging a symmetric invariant relation over orbits

**Setting.** A group $G$ acts on a set $X$; $R$ is a $G$-invariant symmetric relation on $X$ with finite fibres
$N(x) = \{y : R(x, y)\}$ (in the application: $X$ = lattices, $G = O(V)(F)$, $R$ = "is a $\mathfrak p$-neighbour of"); $s \subseteq X$ is a finite set
of representatives of distinct orbits, closed under $R$ up to $G$ (the classes of a genus, which neighbours do not leave), with
finite stabilizers $G_x$ (the groups $O(M)$).

**Theorem** (`sum_inv_card_stab_sum_nb`, the double-counting identity behind the Eichler commutation relation averaged over a
genus). For every $G$-invariant $f : X \to \mathbb C$,
$$\sum_{x\in s}\frac1{|G_x|}\sum_{y\in N(x)}f(y) = \sum_{x\in s}\frac{|N(x)|}{|G_x|}\,f(x).$$

*Proof.* Let $N(x, x') = \#\{y \in N(x) : y \in Gx'\}$. The set $P(x, x') = \{g \in G : R(x, gx')\}$ is in bijection with
$\{y \in N(x) \cap Gx'\} \times G_{x'}$ (`card_P`), and $g \mapsto g^{-1}$ maps it onto $P(x', x)$ (invariance and symmetry); hence
$N(x, x')|G_{x'}| = N(x', x)|G_x|$ (`nbCount_mul_card_stab`). Group $N(x)$ by orbits and exchange the sums.

Over $\mathbb Q$ this is `Siegel.Kneser.card_nbMats` / `genus_sum_neighbors`, done there with matrices.
-/
import Mathlib
import QuadFormsKB.Citation

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Lattices.DoubleCount

open MulAction Classical

variable {G X : Type*} [Group G] [MulAction G X] (R : X → X → Prop)

/-- The pairs $(g, \cdot)$: $P(x, x') = \{g \in G : R(x, g x')\}$. -/
def P (x x' : X) : Type _ := {g : G // R x (g • x')}

/-- The neighbours of $x$ in the orbit of $x'$. -/
def Y (x x' : X) : Type _ := {y : X // R x y ∧ ∃ g : G, g • x' = y}

/-- **$Y(x, x') \times G_{x'} \simeq P(x, x')$**: $(y, s) \mapsto g_ys$ for a chosen $g_y$ with $g_yx' = y$. -/
noncomputable def equivP (x x' : X) : Y (G := G) R x x' × stabilizer G x' ≃ P (G := G) R x x' :=
  Equiv.ofBijective (fun p => ⟨p.1.2.2.choose * p.2.1, by
      rw [mul_smul, mem_stabilizer_iff.mp p.2.2, p.1.2.2.choose_spec]; exact p.1.2.1⟩) (by
    constructor
    · rintro ⟨⟨y, hy, hg⟩, ⟨s, hs⟩⟩ ⟨⟨y', hy', hg'⟩, ⟨s', hs'⟩⟩ h
      have h1 : hg.choose * s = hg'.choose * s' := congrArg Subtype.val h
      have hyy : y = y' := by
        have := congrArg (· • x') h1
        simp only [mul_smul, mem_stabilizer_iff.mp hs, mem_stabilizer_iff.mp hs', hg.choose_spec,
          hg'.choose_spec] at this
        exact this
      subst hyy
      have : s = s' := mul_left_cancel h1
      subst this
      rfl
    · rintro ⟨g, hg⟩
      have hy : R x (g • x') ∧ ∃ g' : G, g' • x' = g • x' := ⟨hg, g, rfl⟩
      refine ⟨(⟨g • x', hy⟩, ⟨hy.2.choose⁻¹ * g, ?_⟩), ?_⟩
      · rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]; exact hy.2.choose_spec.symm
      · apply Subtype.ext; simp)

variable {R}

/-- **Inversion:** $g \mapsto g^{-1}$ maps $P(x, x')$ onto $P(x', x)$. -/
noncomputable def equivPinv (hinv : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (hsymm : ∀ x y, R x y → R y x) (x x' : X) : P (G := G) R x x' ≃ P (G := G) R x' x where
  toFun g := ⟨g.1⁻¹, by
    have h := (hinv g.1⁻¹ x (g.1 • x')).mpr g.2
    rw [inv_smul_smul] at h; exact hsymm _ _ h⟩
  invFun g := ⟨g.1⁻¹, by
    have h := (hinv g.1⁻¹ x' (g.1 • x)).mpr g.2
    rw [inv_smul_smul] at h; exact hsymm _ _ h⟩
  left_inv g := Subtype.ext (inv_inv g.1)
  right_inv g := Subtype.ext (inv_inv g.1)

/-- **The double-counting identity** $N(x, x')\,|G_{x'}| = N(x', x)\,|G_x|$, with $N(x, x') = |Y(x, x')|$. -/
theorem card_Y_mul_card_stab (hinv : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (hsymm : ∀ x y, R x y → R y x) (x x' : X) :
    Nat.card (Y (G := G) R x x') * Nat.card (stabilizer G x') =
      Nat.card (Y (G := G) R x' x) * Nat.card (stabilizer G x) := by
  rw [← Nat.card_prod, ← Nat.card_prod, Nat.card_congr (equivP R x x'), Nat.card_congr (equivP R x' x),
    Nat.card_congr (equivPinv hinv hsymm x x')]

/-- **Averaging a symmetric invariant relation over orbit representatives.** Let $R$ be $G$-invariant and symmetric with
finite fibres (`hfin`), $s$ a finite set of points in distinct orbits (`hdist`) such that every $R$-neighbour of a point of $s$
is in the orbit of a point of $s$ (`hclos`), with finite stabilizers (`hstab`: $|G_x| > 0$, i.e. $G_x$ finite). Then for $G$-invariant $f$,
$$\sum_{x\in s}|G_x|^{-1}\sum_{y : R(x,y)}f(y) = \sum_{x\in s}|G_x|^{-1}\,\#\{y : R(x,y)\}\,f(x).$$ -/
@[kb "kneser1957" "§2, the neighbour relation averaged over a genus (double counting) [unverified]"]
theorem sum_inv_card_stab_sum_nb (hinv : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (hsymm : ∀ x y, R x y → R y x) (hfin : ∀ x, {y | R x y}.Finite) (s : Finset X)
    (hdist : ∀ x ∈ s, ∀ x' ∈ s, (∃ g : G, g • x' = x) → x = x')
    (hclos : ∀ x ∈ s, ∀ y, R x y → ∃ x' ∈ s, ∃ g : G, g • x' = y)
    (hstab : ∀ x ∈ s, 0 < Nat.card (stabilizer G x))
    (f : X → ℂ) (hf : ∀ (g : G) x, f (g • x) = f x) :
    ∑ x ∈ s, ((Nat.card (stabilizer G x) : ℂ))⁻¹ * ∑ y ∈ (hfin x).toFinset, f y =
      ∑ x ∈ s, ((Nat.card (stabilizer G x) : ℂ))⁻¹ * ((hfin x).toFinset.card : ℂ) * f x := by
  -- the orbit representative of a neighbour
  have hrep : ∀ x ∈ s, ∀ y ∈ (hfin x).toFinset, ∃ x' ∈ s, ∃ g : G, g • x' = y := fun x hx y hy =>
    hclos x hx y ((Set.Finite.mem_toFinset _).mp hy)
  -- `N(x, x')` as a filter count
  set N : X → X → ℕ := fun x x' => ((hfin x).toFinset.filter fun y => ∃ g : G, g • x' = y).card with hN
  have hNY : ∀ x x', N x x' = Nat.card (Y (G := G) R x x') := by
    intro x x'
    simp only [hN]
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp [Set.Finite.mem_toFinset]
  -- the orbit of `y` contains exactly one point of `s`
  have huniq : ∀ y, ∀ x₁ ∈ s, ∀ x₂ ∈ s, (∃ g : G, g • x₁ = y) → (∃ g : G, g • x₂ = y) → x₁ = x₂ := by
    rintro y x₁ h₁ x₂ h₂ ⟨g₁, rfl⟩ ⟨g₂, hg₂⟩
    refine hdist x₁ h₁ x₂ h₂ ⟨g₁⁻¹ * g₂, ?_⟩
    rw [mul_smul, hg₂, inv_smul_smul]
  -- step 1: group each inner sum by orbits
  have hgroup : ∀ x ∈ s, ∑ y ∈ (hfin x).toFinset, f y = ∑ x' ∈ s, (N x x' : ℂ) * f x' := by
    intro x hx
    rw [← Finset.sum_fiberwise_of_maps_to (s := (hfin x).toFinset) (t := s)
      (g := fun y => if h : ∃ x' ∈ s, ∃ g : G, g • x' = y then h.choose else x) (fun y hy => by
        simp only [dif_pos (hrep x hx y hy)]; exact (hrep x hx y hy).choose_spec.1)]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    rw [hN]
    simp only
    rw [Finset.cast_card, Finset.sum_mul, one_mul]
    -- the fibre over `x'` is the set of neighbours in its orbit
    have hfib : ((hfin x).toFinset.filter fun y =>
        (if h : ∃ x' ∈ s, ∃ g : G, g • x' = y then h.choose else x) = x') =
        ((hfin x).toFinset.filter fun y => ∃ g : G, g • x' = y) := by
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, he⟩
        refine ⟨hy, ?_⟩
        rw [dif_pos (hrep x hx y hy)] at he
        have := (hrep x hx y hy).choose_spec.2
        rwa [he] at this
      · rintro ⟨hy, hg⟩
        refine ⟨hy, ?_⟩
        rw [dif_pos (hrep x hx y hy)]
        exact huniq y _ (hrep x hx y hy).choose_spec.1 x' hx' (hrep x hx y hy).choose_spec.2 hg
    rw [hfib]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨g, rfl⟩ := (Finset.mem_filter.mp hy).2
    exact hf g x'
  -- step 2: the double counting identity in `ℂ`
  have hsym : ∀ x ∈ s, ∀ x' ∈ s, ((Nat.card (stabilizer G x) : ℂ))⁻¹ * (N x x' : ℂ) =
      ((Nat.card (stabilizer G x') : ℂ))⁻¹ * (N x' x : ℂ) := by
    intro x hx x' hx'
    have h := card_Y_mul_card_stab hinv hsymm x x'
    rw [← hNY, ← hNY] at h
    have h1 : (Nat.card (stabilizer G x) : ℂ) ≠ 0 := by exact_mod_cast (hstab x hx).ne'
    have h2 : (Nat.card (stabilizer G x') : ℂ) ≠ 0 := by exact_mod_cast (hstab x' hx').ne'
    have h' : (N x x' : ℂ) * Nat.card (stabilizer G x') = (N x' x : ℂ) * Nat.card (stabilizer G x) := by
      exact_mod_cast h
    field_simp
    linear_combination h'
  -- step 3: `∑_{x'} N(x, x') = |N(x)|`
  have htot : ∀ x ∈ s, ∑ x' ∈ s, (N x x' : ℂ) = ((hfin x).toFinset.card : ℂ) := by
    intro x hx
    have hc : ((hfin x).toFinset.card : ℕ) = ∑ x' ∈ s, N x x' := by
      rw [hN]
      rw [Finset.card_eq_sum_card_fiberwise (f := fun y => if h : ∃ x' ∈ s, ∃ g : G, g • x' = y
        then h.choose else x) (t := s) (fun y hy => by
          simp only [dif_pos (hrep x hx y hy)]; exact (hrep x hx y hy).choose_spec.1)]
      refine Finset.sum_congr rfl fun x' hx' => ?_
      congr 1
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hy, he⟩
        refine ⟨hy, ?_⟩
        rw [dif_pos (hrep x hx y hy)] at he
        have := (hrep x hx y hy).choose_spec.2
        rwa [he] at this
      · rintro ⟨hy, hg⟩
        refine ⟨hy, ?_⟩
        rw [dif_pos (hrep x hx y hy)]
        exact huniq y _ (hrep x hx y hy).choose_spec.1 x' hx' (hrep x hx y hy).choose_spec.2 hg
    rw [hc]; push_cast; rfl
  calc ∑ x ∈ s, ((Nat.card (stabilizer G x) : ℂ))⁻¹ * ∑ y ∈ (hfin x).toFinset, f y
      = ∑ x ∈ s, ∑ x' ∈ s, ((Nat.card (stabilizer G x) : ℂ))⁻¹ * (N x x' : ℂ) * f x' := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [hgroup x hx, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => by ring
    _ = ∑ x ∈ s, ∑ x' ∈ s, ((Nat.card (stabilizer G x') : ℂ))⁻¹ * (N x' x : ℂ) * f x' := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun x' hx' => ?_
        rw [hsym x hx x' hx']
    _ = ∑ x' ∈ s, ((Nat.card (stabilizer G x') : ℂ))⁻¹ * (∑ x ∈ s, (N x' x : ℂ)) * f x' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
        refine Finset.sum_congr rfl fun x' hx' => ?_
        rw [htot x' hx']

end QuadFormsKB.Lattices.DoubleCount
