/-
# Counting solutions mod $\pi^k$ near orbits: Weil's orbit measure in finite form

**Layer:** a DVR $R$ with uniformizer $\pi$ and finite residue field (every residue characteristic, dyadic included);
completeness only where Hensel lifting is used.

For a quadratic form $Q$ over $R$ in $N$ variables, $m \in R$ and a set $A \subseteq R^N$ of solutions of $Q = m$, the
**near count** (`nearCount`)
$$N_{k,r}(A) = \#\{z \in (R/\pi^k)^N : Q(z) \equiv m \bmod \pi^k,\ z \equiv a \bmod \pi^r \text{ for some } a \in A\}$$
is the finite-level stand-in for the measure $\nu(A)$ of $A$ for the invariant (Leray) measure on $\{Q = m\}$, scaled by
$q^{kn}$. This file proves the three properties of $\nu$ that Weil's orbit-measure argument uses (Weil 1982, §3.4
[unverified]; Kitaoka 1993, §5.6 [unverified]), in finite form:

* `nearCount_mul_relIndex` (**the orbit of $y$ against the orbit of an open subgroup**): for a group $\mathcal K$ acting by integral
  isometries ($\rho : \mathcal K \to M_N(R)$, $Q \circ \rho(\kappa) = Q$), a subgroup $J$ and a solution $y$ such that every element of
  $\mathcal K$ moving $y$ by $\equiv 0 \bmod \pi^r$ agrees on $y$ with an element of $J$ (openness),
  $$N_{k,r}(\mathcal Ky)\cdot[\mathrm{Stab}(y) : \mathrm{Stab}(y)\cap J] = [\mathcal K : J]\cdot N_{k,r}(Jy).$$
  *Proof:* both counts are (number of residue classes mod $\pi^r$ of the orbit) $\times$ (the number of solutions mod $\pi^k$
  above one class), and the class counts are indices of the congruence stabilizer $A_r(y)$ (`card_redOrbit`); openness gives
  $A_r(y) = (J \cap A_r(y))\,\mathrm{Stab}(y)$, whence the index identity `index_mul_relIndex_eq`.
* `nearCount_eq_of_involution` (**invariance under an involution of $V$**): if $\sigma = \pi^{-c}\sigma'$ is an isometry of
  $V = K^N$ with $\sigma^2 = 1$ and $\sigma A = A'$, and $A$, $A'$ are saturated (every solution $\equiv a \bmod \pi^{r_0}$ with $a \in A$ lies in
  $A$), then $N_{k,r}(A) = N_{k,r}(A')$ for $k \gg r \ge r_0$. *Proof:* count instead in the $\sigma$-stable lattice
  $L_0 = R^N\cap\sigma R^N$ with a basis (`Submodule.basisOfPid`), where $\sigma$ acts integrally; the count in $L_0$ is
  $|\ker|$ times the count in $R^N$ (`card_preimage_eq`), because by Hensel and saturation every solution near $A$ is
  $\pi^{k-e}$-close to $A \subseteq L_0$.
* `repCount_eq_sum_nearCount` (**the level set is the disjoint union of the orbits**) and
  `card_orbitSet_eq_nearCount` (**the orbit of $e_0$ under $O(Q \bmod \pi^k)$ is the set of solutions near $\mathcal K e_0$**, for the split
  form $\langle m\rangle\perp Q'$, from the exact Hensel lifting of isometries and `exists_compMat_mulVec_e₀`).
Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.OrbitOpenness

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {N : ℕ}

/-! ### The near count -/

/-- **The near count** $N_{k,r}(A)$: the solutions $z$ of $Q(z) \equiv m \bmod \pi^k$ in $(R/\pi^k)^N$ that are $\equiv a \bmod \pi^r$ for
some $a \in A$ (conditions on the chosen lift `liftI`; they do not depend on it when $r \le k$). -/
def nearCount (Q : QuadForm R N) (π m : R) (k r : ℕ) (A : Set (Fin N → R)) : ℕ :=
  Nat.card {z : Fin N → R ⧸ Ideal.span {π ^ k} //
    π ^ k ∣ Q.eval (liftI π k z) - m ∧ ∃ a ∈ A, ∀ i, π ^ r ∣ liftI π k z i - a i}

theorem eval_congr_of_dvd (Q : QuadForm R N) {π : R} {k : ℕ} {x y : Fin N → R} (h : ∀ i, π ^ k ∣ x i - y i) :
    π ^ k ∣ Q.eval x - Q.eval y := by
  rw [← mk_eq_mk_iff, ← evalIn_redV, ← evalIn_redV]
  congr 1
  funext i
  exact (mk_eq_mk_iff π k _ _).2 (h i)

theorem near_congr {π : R} {k r : ℕ} (hrk : r ≤ k) {x y : Fin N → R} (h : ∀ i, π ^ k ∣ x i - y i)
    (A : Set (Fin N → R)) :
    (∃ a ∈ A, ∀ i, π ^ r ∣ x i - a i) ↔ ∃ a ∈ A, ∀ i, π ^ r ∣ y i - a i := by
  have h' : ∀ i, π ^ r ∣ x i - y i := fun i => (pow_dvd_pow π hrk).trans (h i)
  constructor
  · rintro ⟨a, ha, hxa⟩
    refine ⟨a, ha, fun i => ?_⟩
    have := (hxa i).sub (h' i)
    rwa [show x i - a i - (x i - y i) = y i - a i by ring] at this
  · rintro ⟨a, ha, hya⟩
    refine ⟨a, ha, fun i => ?_⟩
    have := (hya i).add (h' i)
    rwa [show y i - a i + (x i - y i) = x i - a i by ring] at this

theorem liftI_redI_dvd (π : R) (k : ℕ) (x : Fin N → R) : ∀ i, π ^ k ∣ liftI π k (redI π k x) i - x i := by
  intro i
  obtain ⟨w, hw⟩ := liftI_redI π k x
  rw [hw]; simp

theorem redI_mulVec (π : R) (k : ℕ) (M : Matrix (Fin N) (Fin N) R) (x : Fin N → R) :
    redI π k (M *ᵥ x) = M.map (Ideal.Quotient.mk _) *ᵥ redI π k x := by
  funext i
  exact RingHom.map_mulVec (Ideal.Quotient.mk (Ideal.span {π ^ k})) M x i

theorem dvd_mulVec_sub {π : R} {k : ℕ} (M : Matrix (Fin N) (Fin N) R) {x y : Fin N → R}
    (h : ∀ i, π ^ k ∣ x i - y i) : ∀ i, π ^ k ∣ (M *ᵥ x) i - (M *ᵥ y) i := by
  intro i
  rw [← Pi.sub_apply, ← mulVec_sub]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (by simpa using h j) _

/-! ### Fibres of a homomorphism of finite groups -/

/-- **Preimages under a homomorphism of finite groups:** $|\varphi^{-1}(T)| = |\ker\varphi|\cdot|T|$ for $T \subseteq \mathrm{im}\,\varphi$. -/
theorem card_fiber_eq_ker {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) {t : H} (g : G) (hg : φ g = t) :
    Nat.card {x : G // φ x = t} = Nat.card φ.ker :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1 - g, by rw [AddMonoidHom.mem_ker, map_sub, x.2, hg, sub_self]⟩
      invFun := fun y => ⟨y.1 + g, by rw [map_add, (AddMonoidHom.mem_ker).mp y.2, zero_add, hg]⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem card_preimage_eq {G H : Type*} [AddGroup G] [AddGroup H] [Finite G] (φ : G →+ H) (T : Set H)
    (hT : T ⊆ Set.range φ) : Nat.card (φ ⁻¹' T) = Nat.card φ.ker * Nat.card T := by
  classical
  have : Finite T := Finite.of_surjective (fun x : φ ⁻¹' T => (⟨φ x, x.2⟩ : T)) (fun t => by
    obtain ⟨g, hg⟩ := hT t.2
    exact ⟨⟨g, by simp [Set.mem_preimage, hg]⟩, Subtype.ext hg⟩)
  let _ : Fintype T := Fintype.ofFinite _
  let f : φ ⁻¹' T → T := fun x => ⟨φ x, x.2⟩
  have hfib : ∀ t : T, Nat.card {x // f x = t} = Nat.card φ.ker := by
    intro t
    obtain ⟨g, hg⟩ := hT t.2
    rw [← card_fiber_eq_ker φ g hg]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, by simp only [Set.mem_preimage, y.2]; exact t.2⟩, Subtype.ext y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp_rw [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, mul_comm]


/-! ### Index identities -/

section Index

variable {G : Type*} [Group G]

/-- If $U = S\,(J \cap U)$ (every $u \in U$ has $s^{-1}u \in J$ for some $s \in S$) and $S \le U$, then
$[U : J\cap U] = [S : J \cap S]$. -/
theorem relIndex_eq_of_forall_exists (S U J : Subgroup G) (hSU : S ≤ U)
    (h : ∀ u ∈ U, ∃ s ∈ S, s⁻¹ * u ∈ J) : J.relIndex U = J.relIndex S := by
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' (Subgroup.inclusion hSU) (fun a b hab => ?_)) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    simpa using hab
  · intro a b hab
    induction a using Quotient.inductionOn' with | h a => ?_
    induction b using Quotient.inductionOn' with | h b => ?_
    have := Quotient.exact' hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at this ⊢
    simpa using this
  · intro x
    induction x using Quotient.inductionOn' with | h u => ?_
    obtain ⟨s, hs, hsu⟩ := h u u.2
    refine ⟨Quotient.mk'' ⟨s, hs⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    simpa using hsu

/-- **The index identity behind the orbit comparison:** if $S \le U$ and $U = S\,(J\cap U)$ then
$[G : U]\,[S : S\cap J] = [G : J]\,[J : J \cap U]$. -/
theorem index_mul_relIndex_eq (S U J : Subgroup G) (hSU : S ≤ U) (h : ∀ u ∈ U, ∃ s ∈ S, s⁻¹ * u ∈ J) :
    U.index * J.relIndex S = J.index * U.relIndex J := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_right : J ⊓ U ≤ U)
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : J ⊓ U ≤ J)
  rw [Subgroup.inf_relIndex_right] at h1
  rw [Subgroup.inf_relIndex_left] at h2
  rw [← relIndex_eq_of_forall_exists S U J hSU h, mul_comm, h1, ← h2, mul_comm]

end Index

/-! ### Orbits of a group of integral isometries -/

section Orbit

variable {𝒦 : Type*} [Group 𝒦] (ρ : 𝒦 →* Matrix (Fin N) (Fin N) R)

/-- The orbit $Hy = \{\rho(\kappa)y : \kappa \in H\}$. -/
def orbitOf (H : Subgroup 𝒦) (y : Fin N → R) : Set (Fin N → R) := {z | ∃ κ ∈ H, ρ κ *ᵥ y = z}

theorem mulVec_inv_mulVec' (κ : 𝒦) (y : Fin N → R) : ρ κ⁻¹ *ᵥ (ρ κ *ᵥ y) = y := by
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

theorem mulVec_mulVec_inv' (κ : 𝒦) (y : Fin N → R) : ρ κ *ᵥ (ρ κ⁻¹ *ᵥ y) = y := by
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]

/-- The stabilizer $\mathrm{Stab}(y) = \{\kappa : \rho(\kappa)y = y\}$. -/
def stabOf (y : Fin N → R) : Subgroup 𝒦 where
  carrier := {κ | ρ κ *ᵥ y = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ← mulVec_mulVec, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    exact mulVec_inv_mulVec' ρ a y

/-- **The congruence stabilizer** $A_r(y) = \{\kappa : \rho(\kappa)y \equiv y \bmod \pi^r\}$. -/
def congrSub (π : R) (r : ℕ) (y : Fin N → R) : Subgroup 𝒦 where
  carrier := {κ | ∀ i, π ^ r ∣ (ρ κ *ᵥ y) i - y i}
  mul_mem' {a b} ha hb := by
    intro i
    have h1 := dvd_mulVec_sub (ρ a) hb i
    have := h1.add (ha i)
    rw [map_mul, ← mulVec_mulVec]
    rwa [sub_add_sub_cancel] at this
  one_mem' := by simp
  inv_mem' {a} ha := by
    intro i
    have h1 := dvd_mulVec_sub (ρ a⁻¹) ha i
    rw [mulVec_inv_mulVec'] at h1
    rw [← dvd_neg, neg_sub]
    exact h1

theorem stabOf_le_congrSub (π : R) (r : ℕ) (y : Fin N → R) : stabOf ρ y ≤ congrSub ρ π r y := by
  intro κ hκ i
  rw [show ρ κ *ᵥ y = y from hκ, sub_self]
  exact dvd_zero _

variable [Finite (IsLocalRing.ResidueField R)]

/-- The number of solutions mod $\pi^k$ above a residue class $\zeta$ mod $\pi^r$. -/
def fiberCount (Q : QuadForm R N) (π m : R) (k r : ℕ) (ζ : Fin N → R ⧸ Ideal.span {π ^ r}) : ℕ :=
  Nat.card {z : Fin N → R ⧸ Ideal.span {π ^ k} //
    π ^ k ∣ Q.eval (liftI π k z) - m ∧ redI π r (liftI π k z) = ζ}

theorem nearCount_eq_card_sigma (Q : QuadForm R N) (π m : R) (k r : ℕ) (A : Set (Fin N → R)) :
    nearCount Q π m k r A = Nat.card (Σ ζ : redI π r '' A, {z : Fin N → R ⧸ Ideal.span {π ^ k} //
      π ^ k ∣ Q.eval (liftI π k z) - m ∧ redI π r (liftI π k z) = ζ}) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨⟨redI π r (liftI π k z.1), by
          obtain ⟨a, ha, hza⟩ := z.2.2
          exact ⟨a, ha, ((redI_eq_iff π r _ _).mpr hza).symm⟩⟩, ⟨z.1, z.2.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1, by
          obtain ⟨a, ha, hza⟩ := p.1.2
          exact ⟨a, ha, (redI_eq_iff π r _ _).mp (p.2.2.2.trans hza.symm)⟩⟩
      left_inv := fun z => rfl
      right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2.2) rfl }


/-- The lift of $\bar M z$ is $\equiv M\,\tilde z \bmod \pi^k$. -/
theorem liftI_mulVec_dvd (π : R) (k : ℕ) (M : Matrix (Fin N) (Fin N) R) (z : Fin N → R ⧸ Ideal.span {π ^ k}) :
    ∀ i, π ^ k ∣ liftI π k (M.map (Ideal.Quotient.mk _) *ᵥ z) i - (M *ᵥ liftI π k z) i := by
  have : M.map (Ideal.Quotient.mk _) *ᵥ z = redI π k (M *ᵥ liftI π k z) := by
    rw [redI_mulVec, redI_liftI]
  rw [this]
  exact liftI_redI_dvd π k _

/-- **The fibres are constant along orbits:** $\rho(\kappa)$ maps the solutions above $\bar y$ bijectively to those above
$\overline{\rho(\kappa)y}$. -/
theorem fiberCount_mulVec (Q : QuadForm R N) (hρQ : ∀ κ, Q.compMat (ρ κ) = Q) (π m : R) {k r : ℕ}
    (hrk : r ≤ k) (κ : 𝒦) (y : Fin N → R) :
    fiberCount Q π m k r (redI π r (ρ κ *ᵥ y)) = fiberCount Q π m k r (redI π r y) := by
  have key : ∀ (κ : 𝒦) (y : Fin N → R) (z : Fin N → R ⧸ Ideal.span {π ^ k}),
      (π ^ k ∣ Q.eval (liftI π k z) - m ∧ redI π r (liftI π k z) = redI π r y) →
      (π ^ k ∣ Q.eval (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) - m ∧
        redI π r (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) = redI π r (ρ κ *ᵥ y)) := by
    intro κ y z ⟨h1, h2⟩
    have hl := liftI_mulVec_dvd π k (ρ κ) z
    refine ⟨?_, ?_⟩
    · have := (eval_congr_of_dvd Q hl).add h1
      rwa [← eval_compMat, hρQ, sub_add_sub_cancel] at this
    · have e1 : redI π r (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) = redI π r (ρ κ *ᵥ liftI π k z) :=
        (redI_eq_iff π r _ _).mpr fun i => (pow_dvd_pow π hrk).trans (hl i)
      rw [e1, redI_mulVec, h2, ← redI_mulVec]
  have hinv : ∀ (κ : 𝒦) (z : Fin N → R ⧸ Ideal.span {π ^ k}),
      (ρ κ⁻¹).map (Ideal.Quotient.mk _) *ᵥ ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z) = z := by
    intro κ z
    rw [mulVec_mulVec, ← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
  refine Nat.card_congr
    { toFun := fun z => ⟨(ρ κ⁻¹).map (Ideal.Quotient.mk _) *ᵥ z.1, by
        have := key κ⁻¹ (ρ κ *ᵥ y) z.1 z.2
        rwa [mulVec_inv_mulVec'] at this⟩
      invFun := fun z => ⟨(ρ κ).map (Ideal.Quotient.mk _) *ᵥ z.1, key κ y z.1 z.2⟩
      left_inv := fun z => Subtype.ext (by
        show (ρ κ).map _ *ᵥ ((ρ κ⁻¹).map _ *ᵥ z.1) = z.1
        have := hinv κ⁻¹ z.1
        rwa [inv_inv] at this)
      right_inv := fun z => Subtype.ext (hinv κ z.1) }

/-- **Residue classes of an orbit:** $\#\{\bar z : z \in Hy\} = [H : H\cap A_r(y)]$. -/
theorem card_redOrbit (π : R) (r : ℕ) (H : Subgroup 𝒦) (y : Fin N → R) :
    Nat.card (redI π r '' orbitOf ρ H y) = (congrSub ρ π r y).relIndex H := by
  have hiff : ∀ a b : 𝒦, redI π r (ρ a *ᵥ y) = redI π r (ρ b *ᵥ y) ↔ a⁻¹ * b ∈ congrSub ρ π r y := by
    intro a b
    rw [redI_eq_iff]
    constructor
    · intro h i
      have := dvd_mulVec_sub (ρ a⁻¹) (fun i => by rw [← dvd_neg, neg_sub]; exact h i) i
      rwa [mulVec_mulVec, ← map_mul, mulVec_inv_mulVec'] at this
    · intro h i
      have := dvd_mulVec_sub (ρ a) h i
      rw [map_mul, ← mulVec_mulVec, mulVec_mulVec_inv'] at this
      rw [← dvd_neg, neg_sub]; exact this
  rw [Subgroup.relIndex, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun h : H => (⟨redI π r (ρ h *ᵥ y), ⟨ρ h *ᵥ y, ⟨h, h.2, rfl⟩, rfl⟩⟩ :
      redI π r '' orbitOf ρ H y)) (fun a b hab => ?_)) ⟨?_, ?_⟩)
  · apply Subtype.ext
    have hab' := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf] at hab'
    exact (hiff a b).mpr (by simpa using hab')
  · intro a b hab
    induction a using Quotient.inductionOn' with | h a => ?_
    induction b using Quotient.inductionOn' with | h b => ?_
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    simpa using (hiff a b).mp (congrArg Subtype.val hab)
  · rintro ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩⟩
    exact ⟨Quotient.mk'' ⟨h, hh⟩, rfl⟩

/-- **The near count of an orbit** = (residue classes of the orbit) $\times$ (the fibre above $\bar y$). -/
theorem nearCount_orbitOf (Q : QuadForm R N) (hρQ : ∀ κ, Q.compMat (ρ κ) = Q) (π m : R) {k r : ℕ}
    (hrk : r ≤ k) (hπ : Irreducible π) (H : Subgroup 𝒦) (y : Fin N → R) :
    nearCount Q π m k r (orbitOf ρ H y) =
      (congrSub ρ π r y).relIndex H * fiberCount Q π m k r (redI π r y) := by
  classical
  have := finite_vec (ι := Fin N) π hπ r
  have := finite_vec (ι := Fin N) π hπ k
  have hfin : Finite (redI π r '' orbitOf ρ H y) := Subtype.finite
  let _ : Fintype (redI π r '' orbitOf ρ H y) := Fintype.ofFinite _
  rw [nearCount_eq_card_sigma, Nat.card_sigma]
  have hconst : ∀ ζ : redI π r '' orbitOf ρ H y,
      Nat.card {z : Fin N → R ⧸ Ideal.span {π ^ k} //
        π ^ k ∣ Q.eval (liftI π k z) - m ∧ redI π r (liftI π k z) = ζ} = fiberCount Q π m k r (redI π r y) := by
    rintro ⟨_, ⟨_, ⟨h, -, rfl⟩, rfl⟩⟩
    exact fiberCount_mulVec ρ Q hρQ π m hrk h y
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, card_redOrbit]

/-- **Weil's orbit comparison in finite form** (Weil 1982, §3.4 [unverified]): for a group $\mathcal K$ of integral isometries,
a subgroup $J$, and a solution $y$ such that every $\kappa$ with $\rho(\kappa)y \equiv y \bmod \pi^r$ agrees on $y$ with some $\gamma \in J$,
$$N_{k,r}(\mathcal Ky)\cdot[\mathrm{Stab}(y) : \mathrm{Stab}(y)\cap J] = [\mathcal K : J]\cdot N_{k,r}(Jy)\qquad(r \le k).$$ -/
@[kb "weil1982" "§3.4 (orbit measures) [unverified]"]
theorem nearCount_mul_relIndex (Q : QuadForm R N) (hρQ : ∀ κ, Q.compMat (ρ κ) = Q) (π m : R) {k r : ℕ}
    (hrk : r ≤ k) (hπ : Irreducible π) (J : Subgroup 𝒦) (y : Fin N → R)
    (hopen : ∀ κ ∈ congrSub ρ π r y, ∃ γ ∈ J, ρ γ *ᵥ y = ρ κ *ᵥ y) :
    nearCount Q π m k r (orbitOf ρ ⊤ y) * J.relIndex (stabOf ρ y) =
      J.index * nearCount Q π m k r (orbitOf ρ J y) := by
  rw [nearCount_orbitOf ρ Q hρQ π m hrk hπ, nearCount_orbitOf ρ Q hρQ π m hrk hπ,
    Subgroup.relIndex_top_right]
  have h := index_mul_relIndex_eq (stabOf ρ y) (congrSub ρ π r y) J (stabOf_le_congrSub ρ π r y)
    (fun u hu => by
      obtain ⟨γ, hγ, hγu⟩ := hopen u⁻¹ ((congrSub ρ π r y).inv_mem hu)
      refine ⟨u * γ, ?_, ?_⟩
      · show ρ (u * γ) *ᵥ y = y
        rw [map_mul, ← mulVec_mulVec, hγu, mulVec_mulVec_inv']
      · rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact J.inv_mem hγ)
  calc (congrSub ρ π r y).index * fiberCount Q π m k r (redI π r y) * J.relIndex (stabOf ρ y)
      = ((congrSub ρ π r y).index * J.relIndex (stabOf ρ y)) * fiberCount Q π m k r (redI π r y) := by ring
    _ = (J.index * (congrSub ρ π r y).relIndex J) * fiberCount Q π m k r (redI π r y) := by rw [h]
    _ = _ := by ring

end Orbit


/-! ### Invariance under an involution of $V$ (the lattice comparison) -/

section Involution

variable [Finite (IsLocalRing.ResidueField R)]

theorem redI_mulVec_gen {ι ι' : Type*} [Fintype ι'] (π : R) (k : ℕ) (M : Matrix ι ι' R) (x : ι' → R) :
    redI π k (M *ᵥ x) = M.map (Ideal.Quotient.mk _) *ᵥ redI π k x := by
  funext i
  exact RingHom.map_mulVec (Ideal.Quotient.mk (Ideal.span {π ^ k})) M x i

theorem liftI_redI_dvd_gen {ι : Type*} (π : R) (k : ℕ) (x : ι → R) :
    ∀ i, π ^ k ∣ liftI π k (redI π k x) i - x i := by
  intro i
  obtain ⟨w, hw⟩ := liftI_redI π k x
  rw [hw]; simp

theorem dvd_mulVec_sub_gen {ι ι' : Type*} [Fintype ι'] {π : R} {k : ℕ} (M : Matrix ι ι' R) {x y : ι' → R}
    (h : ∀ i, π ^ k ∣ x i - y i) : ∀ i, π ^ k ∣ (M *ᵥ x) i - (M *ᵥ y) i := by
  intro i
  rw [← Pi.sub_apply, ← mulVec_sub]
  simp only [mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (by simpa using h j) _

theorem liftI_mulVec_dvd_gen {ι ι' : Type*} [Fintype ι'] (π : R) (k : ℕ) (M : Matrix ι ι' R)
    (z : ι' → R ⧸ Ideal.span {π ^ k}) :
    ∀ i, π ^ k ∣ liftI π k (M.map (Ideal.Quotient.mk _) *ᵥ z) i - (M *ᵥ liftI π k z) i := by
  have : M.map (Ideal.Quotient.mk _) *ᵥ z = redI π k (M *ᵥ liftI π k z) := by
    rw [redI_mulVec_gen, redI_liftI]
  rw [this]
  exact liftI_redI_dvd_gen π k _

/-- **Hensel and saturation:** a solution mod $\pi^k$ that is $\equiv a \bmod \pi^r$ for some $a \in A$, $A$ saturated, is
$\equiv a^* \bmod \pi^{k-e}$ for some $a^* \in A$. -/
theorem exists_mem_of_near [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (Q : QuadForm R N) {m : R} {e : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m)
    {A : Set (Fin N → R)} {r₀ : ℕ} (hsat : ∀ a ∈ A, ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - a i) → z ∈ A)
    {k r : ℕ} (hr : r₀ ≤ r) (hrk : r + e ≤ k) (hk2 : 2 * e + 1 ≤ k) {z : Fin N → R}
    (hz : π ^ k ∣ Q.eval z - m) (hza : ∃ a ∈ A, ∀ i, π ^ r ∣ z i - a i) :
    ∃ a ∈ A, ∀ i, π ^ (k - e) ∣ z i - a i := by
  obtain ⟨a, ha, hza⟩ := hza
  obtain ⟨z', hz', hzz⟩ := exists_eval_eq_of_dvd hπ Q he he' hk2 z hz
  refine ⟨z', hsat a ha z' hz' fun i => ?_, fun i => by rw [← dvd_neg, neg_sub]; exact hzz i⟩
  have h1 := (pow_dvd_pow π (show r₀ ≤ k - e by omega)).trans (hzz i)
  have h2 := (pow_dvd_pow π hr).trans (hza i)
  have := h1.add h2
  rwa [sub_add_sub_cancel] at this

/-- **The near count is invariant under an involution of $V$** (the finite form of the invariance of Weil's measure on
$\{Q = m\}$ under $O(V)$): let $\sigma = \pi^{-c}\sigma'$ ($\sigma'$ integral) satisfy $\sigma^2 = 1$ and $Q\circ\sigma = Q$, and let
$\sigma A = A'$, $\sigma A' = A$ for sets $A, A'$ of solutions of $Q = m$ that are saturated at radius $r_0$. Then
$N_{k,r}(A) = N_{k,r}(A')$ for $r \ge r_0$, $k \ge r + c + e$, $k \ge 2e+1$ ($\pi^e \,\Vert\, 2m$). -/
@[kb "weil1982" "§3.4 (invariance of the orbit measure) [unverified]"]
theorem nearCount_eq_of_involution [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (Q : QuadForm R N) {m : R} {e : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m)
    (σ' : Matrix (Fin N) (Fin N) R) (c : ℕ) (hσσ : ∀ z, σ' *ᵥ (σ' *ᵥ z) = (π ^ c) ^ 2 • z)
    (hσQ : ∀ z, Q.eval (σ' *ᵥ z) = (π ^ c) ^ 2 * Q.eval z)
    {A A' : Set (Fin N → R)} (hAA' : ∀ a ∈ A, ∃ a' ∈ A', σ' *ᵥ a = π ^ c • a')
    (hA'A : ∀ a' ∈ A', ∃ a ∈ A, σ' *ᵥ a' = π ^ c • a)
    {r₀ : ℕ} (hsat : ∀ a ∈ A, ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - a i) → z ∈ A)
    (hsat' : ∀ a ∈ A', ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - a i) → z ∈ A')
    {k r : ℕ} (hr : r₀ ≤ r) (hk : r + c + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    nearCount Q π m k r A = nearCount Q π m k r A' := by
  classical
  have hπ0 := hπ.ne_zero
  have hc0 : (π ^ c : R) ≠ 0 := pow_ne_zero _ hπ0
  -- the lattice `L₀ = R^N ∩ σ R^N`
  let L₀ : Submodule R (Fin N → R) :=
    { carrier := {z | ∀ i, π ^ c ∣ (σ' *ᵥ z) i}
      add_mem' := fun ha hb i => by rw [mulVec_add]; exact dvd_add (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun t z hz i => by rw [mulVec_smul]; exact dvd_mul_of_dvd_right (hz i) t }
  have hmemL : ∀ z, z ∈ L₀ ↔ ∀ i, π ^ c ∣ (σ' *ᵥ z) i := fun z => Iff.rfl
  have hcL : ∀ u : Fin N → R, π ^ c • u ∈ L₀ := fun u i => by
    rw [mulVec_smul]; exact dvd_mul_right _ _
  have hcancel : ∀ u v : Fin N → R, π ^ c • u = π ^ c • v → u = v := fun u v h =>
    funext fun i => mul_left_cancel₀ hc0 (by simpa using congrFun h i)
  -- `σ` on `L₀`
  have hdiv : ∀ z : L₀, ∃ w : Fin N → R, σ' *ᵥ (z : Fin N → R) = π ^ c • w := fun z =>
    ⟨fun i => Classical.choose (z.2 i), funext fun i => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact Classical.choose_spec (z.2 i)⟩
  choose sw hsw using hdiv
  have hσsw : ∀ z : L₀, σ' *ᵥ sw z = π ^ c • (z : Fin N → R) := by
    intro z
    apply hcancel
    rw [← mulVec_smul, ← hsw, hσσ, smul_smul, sq]
  have hswL : ∀ z : L₀, sw z ∈ L₀ := by
    intro z i
    rw [hσsw]; exact dvd_mul_right _ _
  let σL : L₀ →ₗ[R] L₀ :=
    { toFun := fun z => ⟨sw z, hswL z⟩
      map_add' := fun z₁ z₂ => Subtype.ext (hcancel _ _ (by
        show π ^ c • sw (z₁ + z₂) = π ^ c • (sw z₁ + sw z₂)
        rw [← hsw (z₁ + z₂), smul_add, ← hsw z₁, ← hsw z₂, Submodule.coe_add, mulVec_add]))
      map_smul' := fun t z => Subtype.ext (hcancel _ _ (by
        show π ^ c • sw (t • z) = π ^ c • (t • sw z)
        rw [← hsw (t • z), smul_comm, ← hsw z, Submodule.coe_smul, mulVec_smul])) }
  have hσLv : ∀ z : L₀, ((σL z : L₀) : Fin N → R) = sw z := fun z => rfl
  have hσσL : ∀ z : L₀, σL (σL z) = z := by
    intro z
    apply Subtype.ext
    apply hcancel
    rw [hσLv, ← hsw, hσLv, hσsw]
  have hQσL : ∀ z : L₀, Q.eval (σL z : Fin N → R) = Q.eval z := by
    intro z
    have h1 := hσQ (z : Fin N → R)
    rw [hsw, eval_smul_gen] at h1
    exact mul_left_cancel₀ (pow_ne_zero 2 hc0) h1
  have hAL : ∀ a ∈ A, a ∈ L₀ := fun a ha i => by
    obtain ⟨a', -, h⟩ := hAA' a ha; rw [h]; exact dvd_mul_right _ _
  have hA'L : ∀ a ∈ A', a ∈ L₀ := fun a ha i => by
    obtain ⟨a', -, h⟩ := hA'A a ha; rw [h]; exact dvd_mul_right _ _
  -- the predicate: solution mod `π^k`, `≡ a mod π^r L₀`
  let Pred : Set (Fin N → R) → (Fin N → R) → Prop := fun B z =>
    π ^ k ∣ Q.eval z - m ∧ ∃ a ∈ B, ∃ w ∈ L₀, z - a = π ^ r • w
  have hPred_congr : ∀ B z z', (∀ i, π ^ k ∣ z i - z' i) → (Pred B z ↔ Pred B z') := by
    have one : ∀ B z z', (∀ i, π ^ k ∣ z i - z' i) → Pred B z → Pred B z' := by
      intro B z z' hzz ⟨h1, a, ha, w, hw, hza⟩
      refine ⟨?_, a, ha, ?_⟩
      · have := (eval_congr_of_dvd Q fun i => by rw [← dvd_neg, neg_sub]; exact hzz i).add h1
        rwa [sub_add_sub_cancel] at this
      · choose u hu using fun i => (show π ^ k ∣ z' i - z i by rw [← dvd_neg, neg_sub]; exact hzz i)
        refine ⟨w + π ^ (k - r) • u, L₀.add_mem hw ?_, ?_⟩
        · rw [show k - r = c + (k - r - c) by omega, pow_add, mul_smul]
          exact hcL _
        · funext i
          have := congrFun hza i
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
          rw [show z' i = z i + (z' i - z i) by ring, hu i, mul_add, ← mul_assoc, ← pow_add,
            show r + (k - r) = k by omega]
          linear_combination this
    exact fun B z z' h => ⟨one B z z' h, one B z' z fun i => by rw [← dvd_neg, neg_sub]; exact h i⟩
  -- `σ` exchanges the predicates
  have hPredσ : ∀ (B B' : Set (Fin N → R)), (∀ a ∈ B, ∃ a' ∈ B', σ' *ᵥ a = π ^ c • a') →
      (∀ a ∈ B, a ∈ L₀) → ∀ z : L₀, Pred B z → Pred B' (σL z) := by
    intro B B' hBB' hBL z ⟨h1, a, ha, w, hw, hza⟩
    refine ⟨by rw [hQσL]; exact h1, ?_⟩
    obtain ⟨a', ha', hσa⟩ := hBB' a ha
    have hsa : sw ⟨a, hBL a ha⟩ = a' := hcancel _ _ (by rw [← hsw]; exact hσa)
    refine ⟨a', ha', sw ⟨w, hw⟩, hswL _, ?_⟩
    have := congrArg (fun v => (σL v : Fin N → R)) (show z - ⟨a, hBL a ha⟩ = π ^ r • ⟨w, hw⟩ from
      Subtype.ext (by simpa using hza))
    simp only [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, hσLv] at this
    rw [← hsa]; exact this
  -- a basis of `L₀`
  obtain ⟨n₀, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin N)) L₀
  let P : Matrix (Fin N) (Fin n₀) R := Matrix.of fun i j => ((b j : L₀) : Fin N → R) i
  have hP : ∀ y, P *ᵥ y = ((b.equivFun.symm y : L₀) : Fin N → R) := by
    intro y
    funext i
    rw [Module.Basis.equivFun_symm_apply]
    simp [P, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  let F : Matrix (Fin n₀) (Fin n₀) R :=
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ σL ∘ₗ b.equivFun.symm.toLinearMap)
  have hF : ∀ y, F *ᵥ y = b.equivFun (σL (b.equivFun.symm y)) := by
    intro y; simp [F, LinearMap.toMatrix'_mulVec]
  have hFF : F * F = 1 := by
    ext i j
    have h := congrFun (show F *ᵥ (F *ᵥ Pi.single j 1) = Pi.single j 1 by
      rw [hF, hF, LinearEquiv.symm_apply_apply, hσσL, LinearEquiv.apply_symm_apply]) i
    rw [mulVec_mulVec, mulVec_single_one] at h
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h
  have := finite_vec (ι := Fin n₀) π hπ k
  have := finite_vec (ι := Fin N) π hπ k
  -- the count in `L₀`
  let count₀ : Set (Fin N → R) → ℕ := fun B =>
    Nat.card {y : Fin n₀ → R ⧸ Ideal.span {π ^ k} // Pred B (P *ᵥ liftI π k y)}
  -- (a) σ preserves it
  have hσcount : count₀ A = count₀ A' := by
    let Fb := F.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))
    have hFb : ∀ y, Fb *ᵥ (Fb *ᵥ y) = y := by
      intro y
      rw [mulVec_mulVec, ← Matrix.map_mul, hFF, Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
    have key : ∀ (B B' : Set (Fin N → R)), (∀ a ∈ B, ∃ a' ∈ B', σ' *ᵥ a = π ^ c • a') →
        (∀ a ∈ B, a ∈ L₀) → ∀ y, Pred B (P *ᵥ liftI π k y) → Pred B' (P *ᵥ liftI π k (Fb *ᵥ y)) := by
      intro B B' hBB' hBL y hy
      have h1 := hPredσ B B' hBB' hBL (b.equivFun.symm (liftI π k y)) (by rwa [← hP])
      rw [← LinearEquiv.symm_apply_apply b.equivFun (σL _), ← hF, ← hP] at h1
      refine (hPred_congr B' _ _ ?_).mp h1
      exact dvd_mulVec_sub_gen P fun i => by
        rw [← dvd_neg, neg_sub]; exact liftI_mulVec_dvd_gen π k F y i
    refine Nat.card_congr
      { toFun := fun y => ⟨Fb *ᵥ y.1, key A A' hAA' hAL y.1 y.2⟩
        invFun := fun y => ⟨Fb *ᵥ y.1, key A' A hA'A hA'L y.1 y.2⟩
        left_inv := fun y => Subtype.ext (hFb y.1)
        right_inv := fun y => Subtype.ext (hFb y.1) }
  -- (b) the count in `L₀` is `|ker|` times the near count
  let Φ : (Fin n₀ → R ⧸ Ideal.span {π ^ k}) →+ (Fin N → R ⧸ Ideal.span {π ^ k}) :=
    (P.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).mulVecLin.toAddMonoidHom
  have hΦ : ∀ y, Φ y = P.map (Ideal.Quotient.mk _) *ᵥ y := fun y => rfl
  have hcount : ∀ (B : Set (Fin N → R)), (∀ a ∈ B, a ∈ L₀) →
      (∀ a ∈ B, ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - a i) → z ∈ B) →
      count₀ B = Nat.card Φ.ker * nearCount Q π m k r B := by
    intro B hBL hBsat
    let T : Set (Fin N → R ⧸ Ideal.span {π ^ k}) := {z | Pred B (liftI π k z)}
    have h1 : count₀ B = Nat.card (Φ ⁻¹' T) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
      show _ ↔ Pred B (liftI π k (Φ y))
      rw [hΦ]
      exact hPred_congr B _ _ fun i => by
        rw [← dvd_neg, neg_sub]; exact liftI_mulVec_dvd_gen π k P y i
    have hT : T ⊆ Set.range Φ := by
      intro z ⟨_, a, ha, w, hw, hza⟩
      have hzL : liftI π k z ∈ L₀ := by
        rw [show liftI π k z = a + π ^ r • w by rw [← hza]; abel]
        exact L₀.add_mem (hBL a ha) (L₀.smul_mem _ hw)
      refine ⟨redI π k (b.equivFun ⟨_, hzL⟩), ?_⟩
      rw [hΦ, ← redI_mulVec_gen, hP, LinearEquiv.symm_apply_apply, redI_liftI]
    have h2 : Nat.card T = nearCount Q π m k r B := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
      show Pred B (liftI π k z) ↔ _
      constructor
      · rintro ⟨h1, a, ha, w, -, hza⟩
        refine ⟨h1, a, ha, fun i => ⟨w i, ?_⟩⟩
        have := congrFun hza i
        simpa using this
      · rintro ⟨h1, hnear⟩
        obtain ⟨a, ha, hza⟩ := exists_mem_of_near hπ Q he he' hBsat hr (by omega) hk2 h1 hnear
        refine ⟨h1, a, ha, ?_⟩
        choose u hu using hza
        refine ⟨π ^ (k - e - r) • u, ?_, ?_⟩
        · rw [show k - e - r = c + (k - e - r - c) by omega, pow_add, mul_smul]
          exact hcL _
        · funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          rw [hu i, ← mul_assoc, ← pow_add, show r + (k - e - r) = k - e by omega]
    rw [h1, card_preimage_eq Φ T hT, h2]
  have hker : Nat.card Φ.ker ≠ 0 := by
    have : Finite Φ.ker := Subtype.finite
    exact Nat.card_ne_zero.mpr ⟨⟨⟨0, Φ.map_zero⟩⟩, this⟩
  have := hσcount
  rw [hcount A hAL hsat, hcount A' hA'L hsat'] at this
  exact mul_left_cancel₀ hker this

end Involution


/-! ### The level set as a disjoint union of orbits; the orbit of $e_0$ mod $\pi^k$ -/

section Partition

variable [Finite (IsLocalRing.ResidueField R)]

theorem evalIn_quot_eq_mk_iff (Q : QuadForm R N) (π m : R) (k : ℕ) (z : Fin N → R ⧸ Ideal.span {π ^ k}) :
    Q.evalIn (R ⧸ Ideal.span {π ^ k}) z = Ideal.Quotient.mk _ m ↔ π ^ k ∣ Q.eval (liftI π k z) - m := by
  have : z = redV π k (liftI π k z) := (redI_liftI π k z).symm
  rw [this, evalIn_redV, mk_eq_mk_iff, ← this]

/-- **The level set mod $\pi^k$ is the disjoint union of the near sets of the orbits** (every prime, dyadic included): if the
sets $A_t$ ($t$ in a finite type) cover the solutions of $Q = m$ in $R^N$, and points of $A_t$, $A_{t'}$ congruent mod $\pi^r$ force
$t = t'$, then for $k \ge r + e$, $k \ge 2e + 1$ ($\pi^e \,\Vert\, 2m$), $r_{\pi^k}(m) = \sum_t N_{k,r}(A_t)$. *Proof:* Hensel lifting
(`exists_eval_eq_of_dvd`) puts every solution mod $\pi^k$ near exactly one $A_t$. -/
@[kb "weil1982" "§3.4 (decomposition into orbits) [unverified]"]
theorem repCount_eq_sum_nearCount [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (Q : QuadForm R N) {m : R} {e : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m)
    {ι : Type*} [Fintype ι] (A : ι → Set (Fin N → R))
    (hcover : ∀ y, Q.eval y = m → ∃ t, y ∈ A t) {r : ℕ}
    (hdisj : ∀ t t', ∀ a ∈ A t, ∀ a' ∈ A t', (∀ i, π ^ r ∣ a i - a' i) → t = t')
    {k : ℕ} (hrk : r + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    DVR.repCount Q π k m = ∑ t, nearCount Q π m k r (A t) := by
  classical
  have := finite_vec (ι := Fin N) π hπ k
  let P : (Fin N → R ⧸ Ideal.span {π ^ k}) → Prop := fun z => π ^ k ∣ Q.eval (liftI π k z) - m
  have hrep : DVR.repCount Q π k m = Nat.card {z // P z} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => evalIn_quot_eq_mk_iff Q π m k z)
  have hex : ∀ z : {z // P z}, ∃ t, ∃ a ∈ A t, ∀ i, π ^ r ∣ liftI π k z.1 i - a i := by
    intro z
    obtain ⟨y, hy, hyz⟩ := exists_eval_eq_of_dvd hπ Q he he' hk2 _ z.2
    obtain ⟨t, ht⟩ := hcover y hy
    exact ⟨t, y, ht, fun i => by
      rw [← dvd_neg, neg_sub]; exact (pow_dvd_pow π (by omega)).trans (hyz i)⟩
  choose τ hτ using hex
  have huniq : ∀ (z : {z // P z}) t, (∃ a ∈ A t, ∀ i, π ^ r ∣ liftI π k z.1 i - a i) → τ z = t := by
    intro z t ⟨a, ha, hza⟩
    obtain ⟨a', ha', hza'⟩ := hτ z
    refine hdisj _ _ a' ha' a ha fun i => ?_
    have := (hza i).sub (hza' i)
    rwa [show liftI π k z.1 i - a i - (liftI π k z.1 i - a' i) = a' i - a i by ring] at this
  rw [hrep, ← Nat.card_congr (Equiv.sigmaFiberEquiv τ), Nat.card_sigma]
  refine Finset.sum_congr rfl fun t _ => Nat.card_congr ?_
  exact
    { toFun := fun z => ⟨z.1.1, z.1.2, by have := hτ z.1; rw [z.2] at this; exact this⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, huniq ⟨z.1, z.2.1⟩ t z.2.2⟩
      left_inv := fun z => rfl
      right_inv := fun z => rfl }

variable {𝒦 : Type*} [Group 𝒦] (ρ : 𝒦 →* Matrix (Fin N) (Fin N) R)

/-- **The orbit of $e_0$ under $O(Q\bmod\pi^k)$ is the set of solutions near $\mathcal K e_0$** for $Q = \langle m\rangle\perp Q'$ over a complete
DVR (every prime, dyadic included), where $\mathcal K$ acts through all integral isometries ($\rho$ onto
$\{X : Q\circ X = Q\}$): with $\pi^f \,\Vert\, 4m$, $\pi^d \,\Vert\, \det H_Q$, $f + 1 \le r \le k - d$, $k \ge 2d + 1$, $k \ge f + 1$,
$$|O(Q\bmod\pi^k)\,e_0| = N_{k,r}(\mathcal K e_0).$$
*Proof:* "$\subseteq$": an isometry mod $\pi^k$ is $\equiv$ an integral isometry mod $\pi^{k-d}$ (`exists_compMat_eq_of_dvd`);
"$\supseteq$": translate by $\rho(\kappa)^{-1}$ to a point $\equiv e_0 \bmod \pi^r$ and use `exists_compMat_mulVec_e₀`. -/
@[kb "weil1982" "§3.4 (orbit of e₀ mod π^k) [unverified]"]
theorem card_orbitSet_eq_nearCount [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    {n : ℕ} (ρ : 𝒦 →* Matrix (Fin (n + 1)) (Fin (n + 1)) R) {m : R} (Q' : QuadForm R n)
    (hρQ : ∀ κ, (splitForm m Q').compMat (ρ κ) = splitForm m Q')
    (hsurj : ∀ X, (splitForm m Q').compMat X = splitForm m Q' → ∃ κ, ρ κ = X)
    {f d r k : ℕ} (hf : π ^ f ∣ 4 * m) (hf' : ¬ π ^ (f + 1) ∣ 4 * m)
    (hd : π ^ d ∣ (splitForm m Q').hessian.det) (hd' : ¬ π ^ (d + 1) ∣ (splitForm m Q').hessian.det)
    (hfr : f + 1 ≤ r) (hrk : r + d ≤ k) (hk2 : 2 * d + 1 ≤ k) :
    Nat.card (orbitSet ((splitForm m Q').map (Ideal.Quotient.mk (Ideal.span {π ^ k}))) e₀) =
      nearCount (splitForm m Q') π m k r (orbitOf ρ ⊤ e₀) := by
  set Q := splitForm m Q'
  set mk := Ideal.Quotient.mk (Ideal.span {π ^ k})
  have he₀ : (e₀ : Fin (n + 1) → R ⧸ Ideal.span {π ^ k}) = redI π k e₀ := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [redI]
  have hQe : Q.eval (e₀ : Fin (n + 1) → R) = m := by
    have := evalIn_splitForm_e₀ R m Q'
    simpa [QuadForm.evalIn, QuadForm.eval] using this
  have hevalq : ∀ (z : Fin (n + 1) → R), (Q.map mk).eval (redI π k z) = mk (Q.eval z) := by
    intro z
    rw [← evalIn_eq_eval_map' mk Q _ (Ideal.Quotient.algebraMap_eq _), show redI π k z = redV π k z from rfl,
      evalIn_redV]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · rintro ⟨X, hX, hXx⟩
    -- lift `X`
    let X' : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i j => liftI π k (fun p : Fin (n + 1) × Fin (n + 1) => X p.1 p.2) (i, j)
    have hX'm : X'.map mk = X := by
      ext i j
      exact congrFun (redI_liftI π k (fun p : Fin (n + 1) × Fin (n + 1) => X p.1 p.2)) (i, j)
    have hcoeff : ∀ i j, π ^ k ∣ (Q.compMat X').coeff i j - Q.coeff i j := by
      intro i j
      have this : ((Q.map mk).compMat X).coeff i j = (Q.map mk).coeff i j := by rw [hX]
      rw [← hX'm, map_compMat] at this
      have h2 : mk ((Q.compMat X').coeff i j) = mk (Q.coeff i j) := this
      exact (mk_eq_mk_iff π k _ _).mp h2
    obtain ⟨Y, hY, hYX⟩ := exists_compMat_eq_of_dvd hπ Q hd hd' (by omega) X' hcoeff
    obtain ⟨κ, rfl⟩ := hsurj Y hY
    have hxlift : ∀ i, π ^ k ∣ liftI π k x i - (X' *ᵥ e₀) i := by
      have : x = redI π k (X' *ᵥ e₀) := by rw [redI_mulVec, ← he₀, hX'm, hXx]
      rw [this]; exact liftI_redI_dvd π k _
    refine ⟨?_, ρ κ *ᵥ e₀, ⟨κ, Subgroup.mem_top κ, rfl⟩, fun i => ?_⟩
    · rw [← hXx, ← evalIn_quot_eq_mk_iff, evalIn_eq_eval_map' mk Q _ (Ideal.Quotient.algebraMap_eq _),
        ← eval_compMat, hX, he₀, hevalq, hQe]
    · have h1 := (pow_dvd_pow π (show r ≤ k by omega)).trans (hxlift i)
      have h2 : π ^ r ∣ (X' *ᵥ e₀) i - (ρ κ *ᵥ e₀) i := by
        rw [← Pi.sub_apply, ← sub_mulVec]
        simp only [mulVec, dotProduct]
        refine Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left ?_ _
        have := (pow_dvd_pow π (show r ≤ k - d by omega)).trans (hYX i j)
        rw [← dvd_neg, neg_sub] at this
        simpa using this
      have := h1.add h2
      rwa [sub_add_sub_cancel] at this
  · rintro ⟨hx, _, ⟨κ, -, rfl⟩, hxκ⟩
    -- `y = ρ(κ⁻¹) x̃ ≡ e₀ mod π^r`
    set y := ρ κ⁻¹ *ᵥ liftI π k x
    have hy : π ^ k ∣ Q.eval y - m := by
      rw [show y = ρ κ⁻¹ *ᵥ liftI π k x from rfl, ← eval_compMat, hρQ]; exact hx
    have hye : ∀ i, π ^ r ∣ y i - (e₀ : Fin (n + 1) → R) i := by
      intro i
      have := dvd_mulVec_sub (ρ κ⁻¹) hxκ i
      rwa [mulVec_inv_mulVec'] at this
    obtain ⟨X, hXe, hXQ⟩ := exists_compMat_mulVec_e₀ hπ Q' hf hf' hfr (by omega) hy hye
    refine ⟨(ρ κ * X).map mk, eq_of_eval_eq fun v => ?_, ?_⟩
    · obtain ⟨v', rfl⟩ : ∃ v', redI π k v' = v := ⟨liftI π k v, redI_liftI π k v⟩
      rw [eval_compMat, ← redI_mulVec, hevalq, hevalq, mk_eq_mk_iff, ← mulVec_mulVec, ← eval_compMat, hρQ]
      exact hXQ v'
    · rw [he₀, ← redI_mulVec, ← mulVec_mulVec, hXe, mulVec_mulVec_inv', redI_liftI]

end Partition

end QuadFormsKB.Tamagawa
