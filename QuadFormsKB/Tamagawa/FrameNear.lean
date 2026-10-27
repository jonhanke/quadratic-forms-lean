/-
# Near counts of frames and the orbit comparison

**Layer:** a DVR $R$ with uniformizer $\pi$ and finite residue field (every residue characteristic, dyadic included).

The near count (`nearCount`) measures sets of solutions of one equation $Q(x) = m$. For representations of a form $T$ of
rank $r$ by a form $Q$ of rank $n$ the unknowns are **frames** $X \in M_{n\times r}(R)$, written as vectors
$x \in R^{\mathrm{Fin}\,n \times \mathrm{Fin}\,r}$ (`toMat`), and the equations are $Q\circ X = T$ coefficientwise on and above the
diagonal (`formF`, as in `DVR.repCountForm_eq_card_sol`). This file states the orbit comparison once, for an arbitrary
finite
coordinate type $\iota$ and an arbitrary level map $\Phi : R^\iota \to R^\kappa$ compatible with congruences, and specializes it to
frames, on which a matrix $M \in M_n(R)$ acts by left multiplication (`frameMat`).

**Defines**
* `gNear Φ t π k s A` $= N_{k,s}(A)$: the $z \in (R/\pi^k)^\iota$ with $\Phi(z) \equiv t \bmod \pi^k$ and $z \equiv a \bmod \pi^s$ for some
  $a \in A$ (conditions on the chosen lift `liftI`);
* `gOrbit`, `gStab`, `gCongr`: orbits, stabilizers and congruence stabilizers for a group acting through $\rho : \mathcal K \to M_\iota(R)$;
* `frameMat M`: $X \mapsto MX$ in the coordinates $\mathrm{Fin}\,n \times \mathrm{Fin}\,r$.

**Proves**
* `gNear_mul_relIndex` (**orbit comparison**, Weil 1982, §3.4 [unverified]): for $\Phi$ invariant under $\rho(\mathcal K)$, a subgroup
  $J$ and $y$ such that every $\kappa$ moving $y$ by $\equiv 0 \bmod \pi^s$ agrees on $y$ with an element of $J$,
  $N_{k,s}(\mathcal Ky)\,[\mathrm{Stab}(y) : \mathrm{Stab}(y)\cap J] = [\mathcal K : J]\,N_{k,s}(Jy)$ (the
  `nearCount_mul_relIndex`, same proof);
* `formF_frameMat`: $Q\circ(MX) = (Q\circ M)\circ X$; `isCongr_formF`: `formF` is compatible with congruences.

Indices are 0-based (`Fin n`, `Fin r`).
-/
import QuadFormsKB.Tamagawa.OrbitCount

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ### Near counts for a level map -/

section General

variable [Finite (IsLocalRing.ResidueField R)] {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- **A level map compatible with congruences:** $x \equiv y \bmod \pi^k$ implies $\Phi(x) \equiv \Phi(y) \bmod \pi^k$ (true for every
polynomial map with coefficients in $R$). -/
def IsCongr (Φ : (ι → R) → (κ → R)) (π : R) : Prop :=
  ∀ (k : ℕ) (x y : ι → R), (∀ i, π ^ k ∣ x i - y i) → ∀ p, π ^ k ∣ Φ x p - Φ y p

/-- **The near count** $N_{k,s}(A)$ for the system $\Phi = t$: the $z \in (R/\pi^k)^\iota$ with $\Phi(z) \equiv t \bmod \pi^k$ that are
$\equiv a \bmod \pi^s$ for some $a \in A$ (conditions on the chosen lift `liftI`; independent of it when $s \le k$ and $\Phi$ is
compatible with congruences). -/
def gNear (Φ : (ι → R) → (κ → R)) (t : κ → R) (π : R) (k s : ℕ) (A : Set (ι → R)) : ℕ :=
  Nat.card {z : ι → R ⧸ Ideal.span {π ^ k} //
    (∀ p, π ^ k ∣ Φ (liftI π k z) p - t p) ∧ ∃ a ∈ A, ∀ i, π ^ s ∣ liftI π k z i - a i}

/-- The number of solutions mod $\pi^k$ above a residue class $\zeta$ mod $\pi^s$. -/
def gFiber (Φ : (ι → R) → (κ → R)) (t : κ → R) (π : R) (k s : ℕ) (ζ : ι → R ⧸ Ideal.span {π ^ s}) : ℕ :=
  Nat.card {z : ι → R ⧸ Ideal.span {π ^ k} //
    (∀ p, π ^ k ∣ Φ (liftI π k z) p - t p) ∧ redI π s (liftI π k z) = ζ}

theorem gNear_eq_card_sigma (Φ : (ι → R) → (κ → R)) (t : κ → R) (π : R) (k s : ℕ) (A : Set (ι → R)) :
    gNear Φ t π k s A = Nat.card (Σ ζ : redI π s '' A, {z : ι → R ⧸ Ideal.span {π ^ k} //
      (∀ p, π ^ k ∣ Φ (liftI π k z) p - t p) ∧ redI π s (liftI π k z) = ζ}) := by
  refine Nat.card_congr
    { toFun := fun z => ⟨⟨redI π s (liftI π k z.1), by
          obtain ⟨a, ha, hza⟩ := z.2.2
          exact ⟨a, ha, ((redI_eq_iff π s _ _).mpr hza).symm⟩⟩, ⟨z.1, z.2.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, p.2.2.1, by
          obtain ⟨a, ha, hza⟩ := p.1.2
          exact ⟨a, ha, (redI_eq_iff π s _ _).mp (p.2.2.2.trans hza.symm)⟩⟩
      left_inv := fun z => rfl
      right_inv := fun p => Sigma.subtype_ext (Subtype.ext p.2.2.2) rfl }

variable {𝒦 : Type*} [Group 𝒦] (ρ : 𝒦 →* Matrix ι ι R)

/-- The orbit $Hy = \{\rho(\kappa)y : \kappa \in H\}$. -/
def gOrbit (H : Subgroup 𝒦) (y : ι → R) : Set (ι → R) := {z | ∃ κ ∈ H, ρ κ *ᵥ y = z}

theorem mulVec_inv_mulVec_g (κ : 𝒦) (y : ι → R) : ρ κ⁻¹ *ᵥ (ρ κ *ᵥ y) = y := by
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

theorem mulVec_mulVec_inv_g (κ : 𝒦) (y : ι → R) : ρ κ *ᵥ (ρ κ⁻¹ *ᵥ y) = y := by
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]

/-- The stabilizer $\mathrm{Stab}(y) = \{\kappa : \rho(\kappa)y = y\}$. -/
def gStab (y : ι → R) : Subgroup 𝒦 where
  carrier := {κ | ρ κ *ᵥ y = y}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, ← mulVec_mulVec, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    exact mulVec_inv_mulVec_g ρ a y

/-- **The congruence stabilizer** $A_s(y) = \{\kappa : \rho(\kappa)y \equiv y \bmod \pi^s\}$. -/
def gCongr (π : R) (s : ℕ) (y : ι → R) : Subgroup 𝒦 where
  carrier := {κ | ∀ i, π ^ s ∣ (ρ κ *ᵥ y) i - y i}
  mul_mem' {a b} ha hb := by
    intro i
    have h1 := dvd_mulVec_sub_gen (ρ a) hb i
    have := h1.add (ha i)
    rw [map_mul, ← mulVec_mulVec]
    rwa [sub_add_sub_cancel] at this
  one_mem' := by simp
  inv_mem' {a} ha := by
    intro i
    have h1 := dvd_mulVec_sub_gen (ρ a⁻¹) ha i
    rw [mulVec_inv_mulVec_g] at h1
    rw [← dvd_neg, neg_sub]
    exact h1

theorem gStab_le_gCongr (π : R) (s : ℕ) (y : ι → R) : gStab ρ y ≤ gCongr ρ π s y := by
  intro κ hκ i
  rw [show ρ κ *ᵥ y = y from hκ, sub_self]
  exact dvd_zero _

/-- **The fibres are constant along orbits.** -/
theorem gFiber_mulVec {Φ : (ι → R) → (κ → R)} {π : R} (hΦ : IsCongr Φ π) (hρΦ : ∀ κ x, Φ (ρ κ *ᵥ x) = Φ x)
    (t : κ → R) {k s : ℕ} (hsk : s ≤ k) (κ : 𝒦) (y : ι → R) :
    gFiber Φ t π k s (redI π s (ρ κ *ᵥ y)) = gFiber Φ t π k s (redI π s y) := by
  have key : ∀ (κ : 𝒦) (y : ι → R) (z : ι → R ⧸ Ideal.span {π ^ k}),
      ((∀ p, π ^ k ∣ Φ (liftI π k z) p - t p) ∧ redI π s (liftI π k z) = redI π s y) →
      ((∀ p, π ^ k ∣ Φ (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) p - t p) ∧
        redI π s (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) = redI π s (ρ κ *ᵥ y)) := by
    intro κ y z ⟨h1, h2⟩
    have hl := liftI_mulVec_dvd_gen π k (ρ κ) z
    refine ⟨fun p => ?_, ?_⟩
    · have := (hΦ k _ _ hl p).add (h1 p)
      rwa [hρΦ, sub_add_sub_cancel] at this
    · have e1 : redI π s (liftI π k ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z)) = redI π s (ρ κ *ᵥ liftI π k z) :=
        (redI_eq_iff π s _ _).mpr fun i => (pow_dvd_pow π hsk).trans (hl i)
      rw [e1, redI_mulVec_gen, h2, ← redI_mulVec_gen]
  have hinv : ∀ (κ : 𝒦) (z : ι → R ⧸ Ideal.span {π ^ k}),
      (ρ κ⁻¹).map (Ideal.Quotient.mk _) *ᵥ ((ρ κ).map (Ideal.Quotient.mk _) *ᵥ z) = z := by
    intro κ z
    rw [mulVec_mulVec, ← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.map_one _ (map_zero _) (map_one _), one_mulVec]
  refine Nat.card_congr
    { toFun := fun z => ⟨(ρ κ⁻¹).map (Ideal.Quotient.mk _) *ᵥ z.1, by
        have := key κ⁻¹ (ρ κ *ᵥ y) z.1 z.2
        rwa [mulVec_inv_mulVec_g] at this⟩
      invFun := fun z => ⟨(ρ κ).map (Ideal.Quotient.mk _) *ᵥ z.1, key κ y z.1 z.2⟩
      left_inv := fun z => Subtype.ext (by
        show (ρ κ).map _ *ᵥ ((ρ κ⁻¹).map _ *ᵥ z.1) = z.1
        have := hinv κ⁻¹ z.1
        rwa [inv_inv] at this)
      right_inv := fun z => Subtype.ext (hinv κ z.1) }

/-- **Residue classes of an orbit:** $\#\{\bar z : z \in Hy\} = [H : H\cap A_s(y)]$. -/
theorem card_gRedOrbit (π : R) (s : ℕ) (H : Subgroup 𝒦) (y : ι → R) :
    Nat.card (redI π s '' gOrbit ρ H y) = (gCongr ρ π s y).relIndex H := by
  have hiff : ∀ a b : 𝒦, redI π s (ρ a *ᵥ y) = redI π s (ρ b *ᵥ y) ↔ a⁻¹ * b ∈ gCongr ρ π s y := by
    intro a b
    rw [redI_eq_iff]
    constructor
    · intro h i
      have := dvd_mulVec_sub_gen (ρ a⁻¹) (fun i => by rw [← dvd_neg, neg_sub]; exact h i) i
      rwa [mulVec_mulVec, ← map_mul, mulVec_inv_mulVec_g] at this
    · intro h i
      have := dvd_mulVec_sub_gen (ρ a) h i
      rw [map_mul, ← mulVec_mulVec, mulVec_mulVec_inv_g] at this
      rw [← dvd_neg, neg_sub]; exact this
  rw [Subgroup.relIndex, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (fun h : H => (⟨redI π s (ρ h *ᵥ y), ⟨ρ h *ᵥ y, ⟨h, h.2, rfl⟩, rfl⟩⟩ :
      redI π s '' gOrbit ρ H y)) (fun a b hab => ?_)) ⟨?_, ?_⟩)
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
theorem gNear_orbit {Φ : (ι → R) → (κ → R)} {π : R} (hΦ : IsCongr Φ π) (hρΦ : ∀ κ x, Φ (ρ κ *ᵥ x) = Φ x)
    (t : κ → R) {k s : ℕ} (hsk : s ≤ k) (hπ : Irreducible π) (H : Subgroup 𝒦) (y : ι → R) :
    gNear Φ t π k s (gOrbit ρ H y) = (gCongr ρ π s y).relIndex H * gFiber Φ t π k s (redI π s y) := by
  classical
  have := finite_vec (ι := ι) π hπ s
  have := finite_vec (ι := ι) π hπ k
  have hfin : Finite (redI π s '' gOrbit ρ H y) := Subtype.finite
  let _ : Fintype (redI π s '' gOrbit ρ H y) := Fintype.ofFinite _
  rw [gNear_eq_card_sigma, Nat.card_sigma]
  have hconst : ∀ ζ : redI π s '' gOrbit ρ H y,
      Nat.card {z : ι → R ⧸ Ideal.span {π ^ k} //
        (∀ p, π ^ k ∣ Φ (liftI π k z) p - t p) ∧ redI π s (liftI π k z) = ζ} = gFiber Φ t π k s (redI π s y) := by
    rintro ⟨_, ⟨_, ⟨h, -, rfl⟩, rfl⟩⟩
    exact gFiber_mulVec ρ hΦ hρΦ t hsk h y
  simp_rw [hconst]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, card_gRedOrbit]

/-- **Weil's orbit comparison in finite form** (Weil 1982, §3.4 [unverified]), for an arbitrary level map: for a group $\mathcal K$
acting through $\rho$ with $\Phi\circ\rho(\kappa) = \Phi$, a subgroup $J$, and $y$ such that every $\kappa$ with $\rho(\kappa)y \equiv y
\bmod \pi^s$ agrees on $y$ with some $\gamma \in J$,
$$N_{k,s}(\mathcal Ky)\cdot[\mathrm{Stab}(y) : \mathrm{Stab}(y)\cap J] = [\mathcal K : J]\cdot N_{k,s}(Jy)\qquad(s \le k).$$ -/
@[kb "weil1982" "§3.4 (orbit measures) [unverified]"]
theorem gNear_mul_relIndex {Φ : (ι → R) → (κ → R)} {π : R} (hΦ : IsCongr Φ π)
    (hρΦ : ∀ κ x, Φ (ρ κ *ᵥ x) = Φ x) (t : κ → R) {k s : ℕ} (hsk : s ≤ k) (hπ : Irreducible π)
    (J : Subgroup 𝒦) (y : ι → R) (hopen : ∀ κ ∈ gCongr ρ π s y, ∃ γ ∈ J, ρ γ *ᵥ y = ρ κ *ᵥ y) :
    gNear Φ t π k s (gOrbit ρ ⊤ y) * J.relIndex (gStab ρ y) = J.index * gNear Φ t π k s (gOrbit ρ J y) := by
  rw [gNear_orbit ρ hΦ hρΦ t hsk hπ, gNear_orbit ρ hΦ hρΦ t hsk hπ, Subgroup.relIndex_top_right]
  have h := index_mul_relIndex_eq (gStab ρ y) (gCongr ρ π s y) J (gStab_le_gCongr ρ π s y)
    (fun u hu => by
      obtain ⟨γ, hγ, hγu⟩ := hopen u⁻¹ ((gCongr ρ π s y).inv_mem hu)
      refine ⟨u * γ, ?_, ?_⟩
      · show ρ (u * γ) *ᵥ y = y
        rw [map_mul, ← mulVec_mulVec, hγu, mulVec_mulVec_inv_g]
      · rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact J.inv_mem hγ)
  calc (gCongr ρ π s y).index * gFiber Φ t π k s (redI π s y) * J.relIndex (gStab ρ y)
      = ((gCongr ρ π s y).index * J.relIndex (gStab ρ y)) * gFiber Φ t π k s (redI π s y) := by ring
    _ = (J.index * (gCongr ρ π s y).relIndex J) * gFiber Φ t π k s (redI π s y) := by rw [h]
    _ = _ := by ring

end General

/-! ### Frames -/

section Frames

variable {n r : ℕ}

/-- **Left multiplication on frames** in the coordinates $\mathrm{Fin}\,n\times\mathrm{Fin}\,r$: $(MX)_{(l,i)} = \sum_j M_{lj}X_{(j,i)}$. -/
def frameMat (r : ℕ) {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) :
    Matrix (Fin n × Fin r) (Fin n × Fin r) A :=
  Matrix.of fun p q => if p.2 = q.2 then M p.1 q.1 else 0

theorem frameMat_mulVec {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) (x : Fin n × Fin r → A) :
    frameMat r M *ᵥ x = fun p => ∑ l, M p.1 l * x (l, p.2) := by
  funext p
  simp only [frameMat, mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem toMat_frameMat_mulVec {A : Type*} [CommRing A] (M : Matrix (Fin n) (Fin n) A) (x : Fin n × Fin r → A) :
    toMat (frameMat r M *ᵥ x) = M * toMat x := by
  ext l i
  rw [frameMat_mulVec]
  simp [toMat, Matrix.mul_apply]

theorem frameMat_mul {A : Type*} [CommRing A] (M N : Matrix (Fin n) (Fin n) A) :
    frameMat r (M * N) = frameMat r M * frameMat r N := by
  ext p q
  simp only [frameMat, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    mul_zero, zero_mul]
  by_cases h : p.2 = q.2
  · simp only [h, ite_true]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  · simp only [h, ite_false]
    symm
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with h1 h2 <;> simp_all

theorem frameMat_one {A : Type*} [CommRing A] : frameMat r (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  ext p q
  simp only [frameMat, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- `frameMat` as a monoid homomorphism. -/
def frameHom (r : ℕ) (A : Type*) [CommRing A] :
    Matrix (Fin n) (Fin n) A →* Matrix (Fin n × Fin r) (Fin n × Fin r) A where
  toFun := frameMat r
  map_one' := frameMat_one
  map_mul' := frameMat_mul

theorem frameMat_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    (frameMat r M).map f = frameMat r (M.map f) := by
  ext p q
  simp only [frameMat, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- $Q\circ(MX) = (Q\circ M)\circ X$ in coefficients. -/
theorem formF_frameMat (Q : QuadForm R n) (M : Matrix (Fin n) (Fin n) R) (x : Fin n × Fin r → R) :
    formF Q (frameMat r M *ᵥ x) = formF (Q.compMat M) x := by
  funext p
  simp only [formF, toMat_frameMat_mulVec, compMat_mul]

/-- $Q\circ(MX) = Q\circ X$ for an isometry $M$. -/
theorem formF_frameMat_of_compMat (Q : QuadForm R n) {M : Matrix (Fin n) (Fin n) R} (hM : Q.compMat M = Q)
    (x : Fin n × Fin r → R) : formF Q (frameMat r M *ᵥ x) = formF Q x := by
  rw [formF_frameMat, hM]

/-- **`formF` is compatible with congruences.** -/
theorem isCongr_formF (Q : QuadForm R n) (π : R) : IsCongr (formF Q (r := r)) π := by
  intro k x y hxy p
  have hX : (toMat x).map (Ideal.Quotient.mk (Ideal.span {π ^ k})) =
      (toMat y).map (Ideal.Quotient.mk (Ideal.span {π ^ k})) := by
    ext l i
    simp only [Matrix.map_apply, toMat, Matrix.of_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hxy (l, i)
  have h := congrArg (fun X => ((Q.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).compMat X).coeff p.1.1 p.1.2) hX
  simp only [map_compMat] at h
  simp only [QuadForm.map, Matrix.map_apply] at h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  exact h

end Frames

end QuadFormsKB.Tamagawa.Frames
