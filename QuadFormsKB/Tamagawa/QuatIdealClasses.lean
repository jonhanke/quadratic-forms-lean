/-
# Left ideal classes of a quaternion order and the unfolding of $\zeta_{\mathcal O}$

**Layer:** $R \subseteq K$ a domain and its fraction field (for the applications $R = \mathcal O_F$), $D = (a,b)_K$, $\mathcal O \subset D$ an
$R$-subalgebra (an order). Left ideals of $\mathcal O$ are Mathlib's `Ideal O` (ideals of a noncommutative ring are left ideals).

Two left ideals $J, J'$ are in the same (right) class if $J' = J\beta$ for some $\beta \in D^\times$ (`IdealRel`); right multiplication
preserves the left $\mathcal O$-module structure. For a fixed $J$ put
* $(\mathcal O : J) = \{\alpha \in D : J\alpha \subseteq \mathcal O\}$ (`colon`),
* $\Gamma_J = \{\gamma \in D^\times : J\gamma = J\}$ (`rStab`; the unit group of the right order of $J$),
* $Y_J = \{\beta \in D^\times : \beta \in (\mathcal O : J)\}$ (`ColonUnits`), on which $\Gamma_J$ acts by left multiplication.

**The unfolding** (`classEquiv`): $\beta \mapsto J\beta$ is a bijection
$$\Gamma_J\backslash Y_J \;\simeq\; \{J' \subseteq \mathcal O \text{ left ideal} : J' \sim J\},$$
and, for a subgroup $H \le \Gamma_J$ of finite index (for the applications the central units $R^\times$, `centralUnits`), every class sum
unfolds as (`tsum_class_eq`)
$$\sum_{J' \sim J}f(J') = [\Gamma_J : H]^{-1}\sum_{\beta \in H\backslash Y_J}f(J\beta).$$
The counting step is a general fact about free actions (`tsum_orbitRel_subgroup`): the fibres of $H\backslash Y \to G\backslash Y$ are
copies of $H\backslash G$.

Source: Voight, *Quaternion Algebras* (2021), §17.4 (classes of invertible lattices: $J \sim J'$ iff $J' = J\beta$), §26.5, proof of
Thm. 26.5.4, (26.5.6)–(26.5.8) (there with right ideals and $\alpha J$); Weil 1982 §3.1, pp. 39–40 (the additive calculation:
$D^\times$ acts simply transitively on $D\setminus 0$). Locators checked in the author's PDF.
-/
import QuadFormsKB.Tamagawa.QuatZetaEuler

open Quaternion
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.QuatOrder

open QuadFormsKB.Quat

/-! ### Free actions: orbit sums for a subgroup of finite index -/

section FreeAction

variable {G Y : Type*} [Group G] [MulAction G Y]

/-- The projection $H\backslash Y \to G\backslash Y$ for $H \le G$. -/
def orbitProj (H : Subgroup G) : MulAction.orbitRel.Quotient H Y → MulAction.orbitRel.Quotient G Y :=
  Quotient.map id fun _ _ ⟨h, hh⟩ => ⟨(h : G), hh⟩

theorem orbitProj_mk (H : Subgroup G) (y : Y) :
    orbitProj H (Quotient.mk _ y : MulAction.orbitRel.Quotient H Y) = Quotient.mk _ y := rfl

/-- **The fibres of $H\backslash Y \to G\backslash Y$ are copies of $H\backslash G$** when $G$ acts freely: for $y_0 \in Y$,
$Hg \mapsto H(g\cdot y_0)$ is a bijection from the right cosets onto the fibre over $Gy_0$. -/
theorem nat_card_fiber_orbitProj (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) (H : Subgroup G)
    (p : MulAction.orbitRel.Quotient G Y) :
    Nat.card {q // orbitProj H q = p} = H.index := by
  set y₀ := p.out
  have hy₀ : (Quotient.mk _ y₀ : MulAction.orbitRel.Quotient G Y) = p := Quotient.out_eq p
  -- the map from right cosets
  let φ : G → {q // orbitProj H q = p} := fun g =>
    ⟨Quotient.mk _ (g • y₀), by
      rw [orbitProj_mk, ← hy₀]
      exact Quotient.sound ⟨g, rfl⟩⟩
  have hφ : ∀ g g', φ g = φ g' ↔ g' * g⁻¹ ∈ H := by
    intro g g'
    constructor
    · intro h
      have h1 : (Quotient.mk _ (g • y₀) : MulAction.orbitRel.Quotient H Y) = Quotient.mk _ (g' • y₀) :=
        congrArg Subtype.val h
      obtain ⟨k, hk⟩ := Quotient.exact h1.symm
      -- hk : k • (g • y₀) = g' • y₀
      have hk' : (k : G) • (g • y₀) = g' • y₀ := hk
      have : (g'⁻¹ * ((k : G) * g)) • y₀ = y₀ := by
        rw [mul_smul, mul_smul, hk', inv_smul_smul]
      have h2 := hfree _ _ this
      have h3 : (k : G) * g = g' := by
        have := congrArg (g' * ·) h2
        simpa [← mul_assoc] using this
      rw [← h3, mul_assoc, mul_inv_cancel, mul_one]; exact k.2
    · intro h
      apply Subtype.ext
      show (Quotient.mk _ (g • y₀) : MulAction.orbitRel.Quotient H Y) = Quotient.mk _ (g' • y₀)
      have h' : g * g'⁻¹ ∈ H := by simpa using H.inv_mem h
      refine Quotient.sound ⟨⟨g * g'⁻¹, h'⟩, ?_⟩
      change (g * g'⁻¹) • (g' • y₀) = g • y₀
      rw [mul_smul, inv_smul_smul]
  have hsurj : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h y =>
      rw [orbitProj_mk, ← hy₀] at hq
      obtain ⟨g, hg⟩ := Quotient.exact hq
      -- hg : g • y₀ = y
      exact ⟨g, Subtype.ext (by simp only [φ]; rw [show g • y₀ = y from hg])⟩
  let ψ : Quotient (QuotientGroup.rightRel H) → {q // orbitProj H q = p} :=
    Quotient.lift φ fun g g' h => (hφ g g').2 (QuotientGroup.rightRel_apply.1 h)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y hxy => ?_, fun q => ?_⟩
    · induction x using Quotient.inductionOn with
      | h g =>
        induction y using Quotient.inductionOn with
        | h g' => exact Quotient.sound (QuotientGroup.rightRel_apply.2 ((hφ g g').1 hxy))
    · obtain ⟨g, hg⟩ := hsurj q; exact ⟨Quotient.mk _ g, hg⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), Subgroup.index,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)]

/-- **Orbit sums for a subgroup of finite index** ($G$ acting freely on $Y$, $H \le G$, $[G:H] < \infty$):
$$\sum_{q \in H\backslash Y}f(Gq) = [G:H]\sum_{p \in G\backslash Y}f(p).$$ -/
theorem tsum_orbitRel_subgroup (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) (H : Subgroup G) [H.FiniteIndex]
    (f : MulAction.orbitRel.Quotient G Y → ℝ≥0∞) :
    ∑' q : MulAction.orbitRel.Quotient H Y, f (orbitProj H q) = H.index * ∑' p, f p := by
  rw [← (Equiv.sigmaFiberEquiv (orbitProj H)).tsum_eq, ENNReal.tsum_sigma', ← ENNReal.tsum_mul_left]
  refine tsum_congr fun p => ?_
  have e : ∀ q : {q // orbitProj H q = p}, f (orbitProj H ((Equiv.sigmaFiberEquiv (orbitProj H)) ⟨p, q⟩)) = f p :=
    fun q => by rw [Equiv.sigmaFiberEquiv_apply, q.2]
  have hfin : Finite {q // orbitProj H q = p} :=
    Nat.finite_of_card_ne_zero (by rw [nat_card_fiber_orbitProj hfree H p]; exact Subgroup.FiniteIndex.index_ne_zero)
  rw [tsum_congr e, ENNReal.tsum_const, ENat.card_eq_coe_natCard, nat_card_fiber_orbitProj hfree H p]
  rfl

end FreeAction

/-! ### Left ideals as subsets of $D$, right translates, classes -/

section Classes

-- The algebra structure is an implicit argument (unified from `O`), so that the lemmas apply to orders `O` whose
-- `Algebra` instance was found along a different (definitionally equal) path, e.g. `RingOfIntegers.instAlgebra`.
variable {R K : Type*} [CommRing R] [Field K] {a b : K} {_i : Algebra R ℍ[K,a,b]} {O : Subalgebra R ℍ[K,a,b]}

/-- **The left ideal $J$ as a subset of $D$.** -/
def idealSet (J : Ideal O) : Set ℍ[K,a,b] := {x | ∃ h : x ∈ O, (⟨x, h⟩ : O) ∈ J}

theorem coe_mem_idealSet {J : Ideal O} {x : O} : (x : ℍ[K,a,b]) ∈ idealSet J ↔ x ∈ J :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem idealSet_injective : Function.Injective (idealSet (O := O)) := by
  intro J J' h; ext x; rw [← coe_mem_idealSet, ← coe_mem_idealSet, h]

theorem idealSet_subset (J : Ideal O) : idealSet J ⊆ O := fun _ ⟨h, _⟩ => h

theorem zero_mem_idealSet (J : Ideal O) : (0 : ℍ[K,a,b]) ∈ idealSet J := ⟨O.zero_mem, J.zero_mem⟩

theorem add_mem_idealSet {J : Ideal O} {x y : ℍ[K,a,b]} (hx : x ∈ idealSet J) (hy : y ∈ idealSet J) :
    x + y ∈ idealSet J := by
  obtain ⟨hx, hJx⟩ := hx; obtain ⟨hy, hJy⟩ := hy
  exact ⟨O.add_mem hx hy, J.add_mem hJx hJy⟩

theorem mul_mem_idealSet {J : Ideal O} {y x : ℍ[K,a,b]} (hy : y ∈ O) (hx : x ∈ idealSet J) : y * x ∈ idealSet J := by
  obtain ⟨h, hJ⟩ := hx
  exact ⟨O.mul_mem hy h, J.mul_mem_left ⟨y, hy⟩ hJ⟩

/-- **Right translate** $Seta = \{xeta : x \in S\}$. -/
def rTrans (S : Set ℍ[K,a,b]) (β : ℍ[K,a,b]) : Set ℍ[K,a,b] := (· * β) '' S

theorem rTrans_rTrans (S : Set ℍ[K,a,b]) (β γ : ℍ[K,a,b]) : rTrans (rTrans S β) γ = rTrans S (β * γ) := by
  simp only [rTrans, Set.image_image, mul_assoc]

theorem rTrans_one (S : Set ℍ[K,a,b]) : rTrans S 1 = S := by simp [rTrans]

/-- **The colon set** $(\mathcal O : J) = \{lpha \in D : Jlpha \subseteq \mathcal O\}$. -/
def colon (J : Ideal O) : Set ℍ[K,a,b] := {α | ∀ x ∈ idealSet J, x * α ∈ O}

/-- **The left ideal $Jlpha \cap \mathcal O$** (equal to $Jlpha$ for $lpha \in (\mathcal O : J)$, `idealSet_rmulIdeal`). -/
def rmulIdeal (J : Ideal O) (α : ℍ[K,a,b]) : Ideal O where
  carrier := {y | ∃ x ∈ idealSet J, (y : ℍ[K,a,b]) = x * α}
  add_mem' := by
    rintro y z ⟨x, hx, hy⟩ ⟨x', hx', hz⟩
    exact ⟨x + x', add_mem_idealSet hx hx', by rw [Subalgebra.coe_add, hy, hz, add_mul]⟩
  zero_mem' := ⟨0, zero_mem_idealSet J, by simp⟩
  smul_mem' := by
    rintro c y ⟨x, hx, hy⟩
    exact ⟨c * x, mul_mem_idealSet c.2 hx, by rw [smul_eq_mul, Subalgebra.coe_mul, hy, mul_assoc]⟩

theorem idealSet_rmulIdeal {J : Ideal O} {α : ℍ[K,a,b]} (hα : α ∈ colon J) :
    idealSet (rmulIdeal J α) = rTrans (idealSet J) α := by
  ext y
  constructor
  · rintro ⟨hy, x, hx, hxy⟩
    exact ⟨x, hx, hxy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hα x hx, x, hx, rfl⟩

/-- **Two left ideals are in the same class** if $J' = Jeta$ for some $eta \in D^	imes$. -/
def IdealRel (J J' : Ideal O) : Prop := ∃ β : (ℍ[K,a,b])ˣ, idealSet J' = rTrans (idealSet J) β

theorem idealRel_refl (J : Ideal O) : IdealRel J J := ⟨1, by rw [Units.val_one, rTrans_one]⟩

theorem IdealRel.symm {J J' : Ideal O} (h : IdealRel J J') : IdealRel J' J := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β⁻¹, ?_⟩
  rw [hβ, rTrans_rTrans, Units.mul_inv, rTrans_one]

theorem IdealRel.trans {J J' J'' : Ideal O} (h : IdealRel J J') (h' : IdealRel J' J'') : IdealRel J J'' := by
  obtain ⟨β, hβ⟩ := h; obtain ⟨γ, hγ⟩ := h'
  exact ⟨β * γ, by rw [hγ, hβ, rTrans_rTrans, Units.val_mul]⟩

/-- The class relation as a setoid on left ideals. -/
def idealSetoid (O : Subalgebra R ℍ[K,a,b]) : Setoid (Ideal O) where
  r := IdealRel
  iseqv := ⟨idealRel_refl, IdealRel.symm, IdealRel.trans⟩

/-- **The right-order units** $\Gamma_J = \{\gamma \in D^	imes : J\gamma = J\}$. -/
def rStab (J : Ideal O) : Subgroup (ℍ[K,a,b])ˣ where
  carrier := {γ | rTrans (idealSet J) γ = idealSet J}
  mul_mem' := by
    intro γ δ hγ hδ
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, ← rTrans_rTrans, hγ, hδ]
  one_mem' := by simp only [Set.mem_ofPred_eq, Units.val_one, rTrans_one]
  inv_mem' := by
    intro γ hγ
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hγ]
    rw [rTrans_rTrans, Units.mul_inv, rTrans_one]

theorem mem_rStab {J : Ideal O} {γ : (ℍ[K,a,b])ˣ} : γ ∈ rStab J ↔ rTrans (idealSet J) γ = idealSet J := Iff.rfl

/-- **$Y_J$**: the units $eta$ with $Jeta \subseteq \mathcal O$. -/
abbrev ColonUnits (J : Ideal O) := {β : (ℍ[K,a,b])ˣ // (β : ℍ[K,a,b]) ∈ colon J}

instance (J : Ideal O) : MulAction (rStab J) (ColonUnits J) where
  smul g β := ⟨(g : (ℍ[K,a,b])ˣ) * β.1, by
    intro x hx
    have : x * ((g : (ℍ[K,a,b])ˣ) : ℍ[K,a,b]) ∈ idealSet J := by
      rw [← (mem_rStab.1 g.2)]; exact ⟨x, hx, rfl⟩
    rw [Units.val_mul, ← mul_assoc]; exact β.2 _ this⟩
  one_smul β := Subtype.ext (one_mul _)
  mul_smul g h β := Subtype.ext (mul_assoc _ _ _)

theorem smul_colonUnits_val {J : Ideal O} (g : rStab J) (β : ColonUnits J) :
    (g • β).1 = (g : (ℍ[K,a,b])ˣ) * β.1 := rfl

theorem colonUnits_free {J : Ideal O} (g : rStab J) (β : ColonUnits J) (h : g • β = β) : g = 1 := by
  have h1 : (g : (ℍ[K,a,b])ˣ) * β.1 = β.1 := congrArg Subtype.val h
  exact Subtype.ext (mul_eq_right.1 h1)

/-- $eta \mapsto Jeta$. -/
def classMap (J : Ideal O) (β : ColonUnits J) : {J' : Ideal O // IdealRel J J'} :=
  ⟨rmulIdeal J β.1, β.1, idealSet_rmulIdeal β.2⟩

theorem classMap_eq_iff {J : Ideal O} (β β' : ColonUnits J) :
    classMap J β = classMap J β' ↔ ∃ g : rStab J, g • β' = β := by
  constructor
  · intro h
    have h1 : rTrans (idealSet J) (β.1 : ℍ[K,a,b]) = rTrans (idealSet J) (β'.1 : ℍ[K,a,b]) := by
      rw [← idealSet_rmulIdeal β.2, ← idealSet_rmulIdeal β'.2]
      exact congrArg (fun J'' : {J' : Ideal O // IdealRel J J'} => idealSet J''.1) h
    have hg : β.1 * β'.1⁻¹ ∈ rStab J := by
      rw [mem_rStab, Units.val_mul, ← rTrans_rTrans, h1, rTrans_rTrans, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, rTrans_one]
    refine ⟨⟨_, hg⟩, Subtype.ext ?_⟩
    rw [smul_colonUnits_val]; simp
  · rintro ⟨g, rfl⟩
    apply Subtype.ext; apply idealSet_injective
    change idealSet (rmulIdeal J _) = idealSet (rmulIdeal J _)
    rw [idealSet_rmulIdeal (g • β').2, idealSet_rmulIdeal β'.2, smul_colonUnits_val, Units.val_mul,
      ← rTrans_rTrans, mem_rStab.1 g.2]

theorem classMap_surjective (J : Ideal O) : Function.Surjective (classMap J) := by
  rintro ⟨J', β, hβ⟩
  have hc : (β : ℍ[K,a,b]) ∈ colon J := fun x hx => idealSet_subset J' (hβ ▸ ⟨x, hx, rfl⟩)
  refine ⟨⟨β, hc⟩, Subtype.ext (idealSet_injective ?_)⟩
  change idealSet (rmulIdeal J β) = idealSet J'
  rw [idealSet_rmulIdeal hc, hβ]

/-- **The unfolding bijection** $\Gamma_Jackslash Y_J \simeq \{J' : J' \sim J\}$, $\Gamma_Jeta \mapsto Jeta$
(Voight 2021, (26.5.6)–(26.5.7), for left ideals). -/
def classEquiv (J : Ideal O) : MulAction.orbitRel.Quotient (rStab J) (ColonUnits J) ≃ {J' : Ideal O // IdealRel J J'} :=
  Equiv.ofBijective
    (Quotient.lift (classMap J) fun β β' h => by
      obtain ⟨g, hg⟩ := h
      exact (classMap_eq_iff β β').2 ⟨g, hg⟩)
    ⟨fun x y hxy => by
      induction x using Quotient.inductionOn with
      | h β =>
        induction y using Quotient.inductionOn with
        | h β' =>
          obtain ⟨g, hg⟩ := (classMap_eq_iff β β').1 hxy
          exact Quotient.sound ⟨g, hg⟩,
     fun J' => by
      obtain ⟨β, hβ⟩ := classMap_surjective J J'
      exact ⟨Quotient.mk _ β, hβ⟩⟩

theorem classEquiv_mk (J : Ideal O) (β : ColonUnits J) : classEquiv J (Quotient.mk _ β) = classMap J β := rfl

/-- **The central units** $R^	imes \subseteq D^	imes$. -/
def centralUnits (R : Type*) {K : Type*} [CommRing R] [Field K] (a b : K) [Algebra R ℍ[K,a,b]] :
    Subgroup (ℍ[K,a,b])ˣ :=
  (Units.map (algebraMap R ℍ[K,a,b]).toMonoidHom).range

theorem rTrans_algebraMap_subset (J : Ideal O) (r : R) :
    rTrans (idealSet J) (algebraMap R ℍ[K,a,b] r) ⊆ idealSet J := by
  rintro _ ⟨x, hx, rfl⟩
  simp only
  rw [← Algebra.commutes]
  exact mul_mem_idealSet (O.algebraMap_mem r) hx

theorem centralUnits_le_rStab (J : Ideal O) : centralUnits R a b ≤ rStab J := by
  rintro _ ⟨u, rfl⟩
  rw [mem_rStab]
  refine le_antisymm (rTrans_algebraMap_subset J (u : R)) fun x hx => ?_
  refine ⟨x * algebraMap R ℍ[K,a,b] ((u⁻¹ : Rˣ) : R), rTrans_algebraMap_subset J _ ⟨x, hx, rfl⟩, ?_⟩
  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_ofClass]
  rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

/-- $H = R^	imes$ as a subgroup of $\Gamma_J$. -/
def centralUnitsIn (J : Ideal O) : Subgroup (rStab J) := (centralUnits R a b).subgroupOf (rStab J)

/-- **The unfolded class sum** (Voight 2021, (26.5.8)): if $[\Gamma_J : R^	imes] < \infty$, then for every $f \ge 0$ on left ideals,
$$[\Gamma_J : R^	imes]\sum_{J' \sim J}f(J') = \sum_{eta \in R^	imesackslash Y_J}f(Jeta).$$ -/
theorem index_mul_tsum_class (J : Ideal O) [(centralUnitsIn (R := R) J).FiniteIndex] (f : Ideal O → ℝ≥0∞) :
    (centralUnitsIn (R := R) J).index * ∑' J' : {J' : Ideal O // IdealRel J J'}, f J'.1 =
      ∑' q : MulAction.orbitRel.Quotient (centralUnitsIn (R := R) J) (ColonUnits J),
        f (rmulIdeal J (orbitProj _ q).out.1) := by
  rw [← (classEquiv J).tsum_eq (fun J' => f J'.1), ← tsum_orbitRel_subgroup colonUnits_free]
  refine tsum_congr fun q => ?_
  congr 1
  conv_lhs => rw [← Quotient.out_eq (orbitProj _ q)]
  rfl

/-- **The units in $J$**: $\{x \in D^\times : x \in J\}$, on which $R^\times$ acts by multiplication. -/
abbrev IdealUnits (J : Ideal O) := {x : (ℍ[K,a,b])ˣ // (x : ℍ[K,a,b]) ∈ idealSet J}

instance (J : Ideal O) : MulAction (centralUnits R a b) (IdealUnits J) where
  smul u x := ⟨(u : (ℍ[K,a,b])ˣ) * x.1, by
    obtain ⟨w, hw⟩ := u.2
    rw [Units.val_mul, ← hw]
    exact mul_mem_idealSet (O.algebraMap_mem (w : R)) x.2⟩
  one_smul x := Subtype.ext (one_mul _)
  mul_smul u w x := Subtype.ext (mul_assoc _ _ _)

theorem smul_idealUnits_val {J : Ideal O} (u : centralUnits R a b) (x : IdealUnits J) :
    (u • x).1 = (u : (ℍ[K,a,b])ˣ) * x.1 := rfl

/-- The unfolded class sum with the representative of the $R^\times$-orbit (equivalent to `index_mul_tsum_class`, since
$J\beta$ depends only on the $\Gamma_J$-orbit of $\beta$). -/
theorem index_mul_tsum_class' (J : Ideal O) [(centralUnitsIn (R := R) J).FiniteIndex] (f : Ideal O → ℝ≥0∞) :
    (centralUnitsIn (R := R) J).index * ∑' J' : {J' : Ideal O // IdealRel J J'}, f J'.1 =
      ∑' q : MulAction.orbitRel.Quotient (centralUnitsIn (R := R) J) (ColonUnits J), f (rmulIdeal J q.out.1) := by
  rw [index_mul_tsum_class]
  refine tsum_congr fun q => ?_
  congr 1
  have h : (classMap J (orbitProj _ q).out).1 = (classMap J q.out).1 := by
    congr 1
    rw [← classEquiv_mk, ← classEquiv_mk, Quotient.out_eq]
    rw [← orbitProj_mk (centralUnitsIn (R := R) J) q.out, Quotient.out_eq]
  exact h

/-- **Sum over left ideals = sum over classes of class sums.** -/
theorem tsum_ideal_eq_tsum_class (f : Ideal O → ℝ≥0∞) :
    ∑' J : Ideal O, f J = ∑' c : Quotient (idealSetoid O), ∑' J' : {J' : Ideal O // IdealRel c.out J'}, f J'.1 := by
  rw [← (Equiv.sigmaFiberEquiv (Quotient.mk (idealSetoid O))).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun c => ?_
  let e : {J // Quotient.mk (idealSetoid O) J = c} ≃ {J' : Ideal O // IdealRel c.out J'} :=
    Equiv.subtypeEquivRight fun J => by
      constructor
      · intro h
        have : Quotient.mk (idealSetoid O) J = Quotient.mk (idealSetoid O) c.out := by rw [h, Quotient.out_eq]
        exact (Quotient.exact this).symm
      · intro h
        rw [← Quotient.out_eq c]
        exact Quotient.sound (IdealRel.symm h)
  rw [← e.tsum_eq]
  rfl

end Classes

end QuadFormsKB.QuatOrder
