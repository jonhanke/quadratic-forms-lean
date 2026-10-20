/-
# Lattice change for near counts

**Layer:** a DVR $R$ with uniformizer $\pi$ and finite residue field of size $q$ (every residue characteristic, dyadic
included); completeness only where Hensel lifting is used.

The near count $N_{k,r}(A)$ (`nearCount`) is the finite-level stand-in for the invariant measure of a set $A$ of solutions of
$Q = m$, **in the coordinates of a lattice** ($R^N$). This file proves how it changes when the lattice is replaced by a
sublattice $\Lambda_1 = PR^N$ ($P$ integral, $\det P \ne 0$): in the coordinates of $\Lambda_1$ the form is $Q\circ P$, and
$$N^{Q\circ P}_{k,r}(A) = [R^N : PR^N]\cdot N^{Q}_{k,r}(PA)\qquad(k \gg r \gg 0,\ PA \text{ saturated}),$$
the finite form of "the coordinate measure of $\Lambda_1$ is $[\Lambda_2:\Lambda_1]$ times that of $\Lambda_2$" (Hanke 2004, §3, pp. 359–360, the
Bad-type reduction maps change the lattice in the same way [unverified]). The index is
$[R^N : PR^N] = \#R/(\det P) = q^{\mathrm{ord}\det P}$ (Smith normal form).

**Proves**
* `nearCount_compMat` (**the lattice change of near counts**), extracted from the proof of `nearCount_eq_of_involution` and stated for an arbitrary sublattice;
* `card_ker_redMat`: the kernel of $P \bmod \pi^k$ on $(R/\pi^k)^N$ has $[R^N : PR^N]$ elements for $\pi^kR^N \subseteq PR^N$;
* `card_quot_range`: $[R^N : PR^N] = \#R/(\det P)$ (Smith normal form, `Submodule.quotientEquivPiSpan`);
* `card_quot_span_eq`: $\#R/(x) = q^e$ for $\pi^e\,\Vert\,x$.

Sources: Weil 1982, §3.4 [unverified]; Hanke 2004, §3, Def. 3.1 and the maps $\pi_Z$, $\pi_{B'}$, $\pi_{B''}$, pp. 358–361. Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.ImprimitiveOrbital

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity LocalDensity.DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {N : ℕ}

/-! ### Basic facts on integral matrices with nonzero determinant -/

section Basic

/-- $x \mapsto Px$ is injective on $R^N$ when $\det P \ne 0$ ($\mathrm{adj}(P)P = \det P$). -/
theorem mulVec_injective_of_det_ne_zero (P : Matrix (Fin N) (Fin N) R) (hP : P.det ≠ 0) :
    Function.Injective (P *ᵥ ·) := by
  intro x y hxy
  have h := congrArg (P.adjugate *ᵥ ·) hxy
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec] at h
  exact smul_right_injective _ hP h

/-- **$\pi^cR^N \subseteq PR^N$** for $\det P \mid \pi^c$ (via the adjugate). -/
theorem exists_mulVec_eq_smul (P : Matrix (Fin N) (Fin N) R) {π : R} {c : ℕ} (hc : P.det ∣ π ^ c)
    (u : Fin N → R) : ∃ w, P *ᵥ w = π ^ c • u := by
  obtain ⟨d, hd⟩ := hc
  refine ⟨d • (P.adjugate *ᵥ u), ?_⟩
  rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, smul_smul, mul_comm d, ← hd]

end Basic

/-! ### The lattice change of near counts -/

section NearCount

variable [Finite (IsLocalRing.ResidueField R)]

/-- **$P \bmod \pi^k$** as an additive endomorphism of $(R/\pi^k)^N$. -/
def redMat (π : R) (k : ℕ) (P : Matrix (Fin N) (Fin N) R) :
    (Fin N → R ⧸ Ideal.span {π ^ k}) →+ (Fin N → R ⧸ Ideal.span {π ^ k}) :=
  (P.map (Ideal.Quotient.mk (Ideal.span {π ^ k}))).mulVecLin.toAddMonoidHom

theorem redMat_apply (π : R) (k : ℕ) (P : Matrix (Fin N) (Fin N) R) (z : Fin N → R ⧸ Ideal.span {π ^ k}) :
    redMat π k P z = P.map (Ideal.Quotient.mk _) *ᵥ z := rfl

/-- **The lattice change of near counts** (Weil 1982, §3.4 [unverified]: the invariant measure on $\{Q = m\}$ in the coordinates
of a sublattice). Let $P$ be integral with $\det P \ne 0$ and $\pi^cR^N \subseteq PR^N$, and let $A \subseteq R^N$ be such that $PA$ is
saturated at radius $r_0$ for $Q = m$ ($\pi^e\,\Vert\,2m$). Then for $r \ge r_0$, $k \ge r + c + e$, $k \ge 2e + 1$,
$$N^{Q\circ P}_{k,r}(A) = |\ker(P \bmod \pi^k)|\cdot N^{Q}_{k,r}(PA).$$
*Proof:* as in `nearCount_eq_of_involution`: the left side counts the $y \bmod \pi^k$ with $Py$ a solution mod $\pi^k$ that is
$\equiv Pa \bmod \pi^rPR^N$; this condition on $z = Py$ is well defined mod $\pi^k$, the count is $|\ker|$ times the number of such
$z \bmod \pi^k$ (`card_preimage_eq`), and by Hensel lifting and saturation these $z$ are exactly the solutions near $PA$. -/
@[kb "weil1982" "§3.4 (the invariant measure in the coordinates of a sublattice) [unverified]"]
theorem nearCount_compMat [IsAdicComplete (IsLocalRing.maximalIdeal R) R] {π : R} (hπ : Irreducible π)
    (Q : QuadForm R N) {m : R} {e : ℕ} (he : π ^ e ∣ 2 * m) (he' : ¬ π ^ (e + 1) ∣ 2 * m)
    (P : Matrix (Fin N) (Fin N) R) (hP : P.det ≠ 0) {c : ℕ} (hc : ∀ u : Fin N → R, ∃ w, P *ᵥ w = π ^ c • u)
    {A : Set (Fin N → R)} {r₀ : ℕ}
    (hsat : ∀ a ∈ A, ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - (P *ᵥ a) i) → ∃ a' ∈ A, z = P *ᵥ a')
    {k r : ℕ} (hr : r₀ ≤ r) (hk : r + c + e ≤ k) (hk2 : 2 * e + 1 ≤ k) :
    nearCount (Q.compMat P) π m k r A =
      Nat.card (redMat π k P).ker * nearCount Q π m k r ((P *ᵥ ·) '' A) := by
  classical
  have hinj := mulVec_injective_of_det_ne_zero P hP
  have := finite_vec (ι := Fin N) π hπ k
  -- the predicate: a solution mod `π^k` that is `≡ P a mod π^r P R^N`
  let Pred : (Fin N → R) → Prop := fun z =>
    π ^ k ∣ Q.eval z - m ∧ ∃ a ∈ A, ∃ w : Fin N → R, z - P *ᵥ a = π ^ r • (P *ᵥ w)
  have hkk : ∀ u : Fin N → R, π ^ r * π ^ (k - r - c) * π ^ c = π ^ k := fun _ => by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hPred_congr : ∀ z z', (∀ i, π ^ k ∣ z i - z' i) → Pred z → Pred z' := by
    intro z z' hzz ⟨h1, a, ha, w, hw⟩
    refine ⟨?_, a, ha, ?_⟩
    · have := (eval_congr_of_dvd Q fun i => by rw [← dvd_neg, neg_sub]; exact hzz i).add h1
      rwa [sub_add_sub_cancel] at this
    · choose u hu using fun i => (show π ^ k ∣ z' i - z i by rw [← dvd_neg, neg_sub]; exact hzz i)
      obtain ⟨w', hw'⟩ := hc u
      refine ⟨w + π ^ (k - r - c) • w', funext fun i => ?_⟩
      have h1 := congrFun hw i
      have h2 := congrFun hw' i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_add, mulVec_smul, Pi.add_apply]
      linear_combination h1 + hu i - π ^ r * π ^ (k - r - c) * h2 - u i * hkk u
  have hPred_iff : ∀ z z', (∀ i, π ^ k ∣ z i - z' i) → (Pred z ↔ Pred z') := fun z z' h =>
    ⟨hPred_congr z z' h, hPred_congr z' z fun i => by rw [← dvd_neg, neg_sub]; exact h i⟩
  set Φ := redMat π k P
  -- (1) the left side is the preimage count
  have h1 : nearCount (Q.compMat P) π m k r A = Nat.card (Φ ⁻¹' {z | Pred (liftI π k z)}) := by
    unfold nearCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    show _ ↔ Pred (liftI π k (Φ y))
    rw [← hPred_iff (P *ᵥ liftI π k y) _ (fun i => by
      rw [← dvd_neg, neg_sub]; exact liftI_mulVec_dvd π k P y i), eval_compMat]
    constructor
    · rintro ⟨h, a, ha, hya⟩
      choose w hw using hya
      refine ⟨h, a, ha, w, ?_⟩
      rw [← mulVec_sub, ← mulVec_smul]
      congr 1
      funext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; exact hw i
    · rintro ⟨h, a, ha, w, hw⟩
      refine ⟨h, a, ha, fun i => ⟨w i, ?_⟩⟩
      have : liftI π k y - a = π ^ r • w := hinj (by
        show P *ᵥ (liftI π k y - a) = P *ᵥ (π ^ r • w)
        rw [mulVec_sub, mulVec_smul]; exact hw)
      have := congrFun this i
      simpa using this
  -- (2) the target set lies in the range of `Φ`
  have hT : {z | Pred (liftI π k z)} ⊆ Set.range Φ := by
    rintro z ⟨_, a, ha, w, hw⟩
    refine ⟨redI π k (a + π ^ r • w), ?_⟩
    rw [redMat_apply, ← redI_mulVec, mulVec_add, mulVec_smul, ← hw, add_sub_cancel, redI_liftI]
  -- (3) the target set is the near set of `PA`
  have hBsat : ∀ b ∈ (P *ᵥ ·) '' A, ∀ z, Q.eval z = m → (∀ i, π ^ r₀ ∣ z i - b i) → z ∈ (P *ᵥ ·) '' A := by
    rintro _ ⟨a, ha, rfl⟩ z hz hza
    obtain ⟨a', ha', rfl⟩ := hsat a ha z hz hza
    exact ⟨a', ha', rfl⟩
  have h3 : Nat.card {z | Pred (liftI π k z)} = nearCount Q π m k r ((P *ᵥ ·) '' A) := by
    unfold nearCount
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    show Pred (liftI π k z) ↔ _
    constructor
    · rintro ⟨h, a, ha, w, hw⟩
      refine ⟨h, P *ᵥ a, ⟨a, ha, rfl⟩, fun i => ⟨(P *ᵥ w) i, ?_⟩⟩
      have := congrFun hw i
      simpa using this
    · rintro ⟨h, hnear⟩
      obtain ⟨_, ⟨a', ha', rfl⟩, hza'⟩ := exists_mem_of_near hπ Q he he' hBsat hr (by omega) hk2 h hnear
      choose u hu using hza'
      obtain ⟨w', hw'⟩ := hc u
      refine ⟨h, a', ha', π ^ (k - e - r - c) • w', funext fun i => ?_⟩
      have h2 := congrFun hw' i
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul]
      have hpow : π ^ r * π ^ (k - e - r - c) * π ^ c = π ^ (k - e) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      linear_combination hu i - π ^ r * π ^ (k - e - r - c) * h2 - u i * hpow
  rw [h1, card_preimage_eq Φ _ hT, h3]

end NearCount

/-! ### The index $[R^N : PR^N]$ -/

section Index

variable [Finite (IsLocalRing.ResidueField R)]

/-- **$|\ker(P \bmod \pi^k)| = [R^N : PR^N]$** when $\pi^kR^N \subseteq PR^N$ (a finite group has $|\ker| = |\mathrm{coker}|$, and
$\mathrm{coker}(P \bmod \pi^k) = R^N/(PR^N + \pi^kR^N) = R^N/PR^N$). -/
theorem card_ker_redMat {π : R} (hπ : Irreducible π) (P : Matrix (Fin N) (Fin N) R) {k : ℕ}
    (hc : ∀ u : Fin N → R, ∃ w, P *ᵥ w = π ^ k • u) :
    Nat.card (redMat π k P).ker = Nat.card ((Fin N → R) ⧸ LinearMap.range P.mulVecLin) := by
  classical
  have := finite_vec (ι := Fin N) π hπ k
  set G := Fin N → R ⧸ Ideal.span {π ^ k}
  set Φ := redMat π k P
  -- `|G| = |ker| |range|` and `|G| = |range| |G/range|`
  have e1 : Nat.card G = Nat.card Φ.ker * Nat.card Φ.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv, mul_comm]
  have e2 : Nat.card G = Nat.card Φ.range * Nat.card (G ⧸ Φ.range) := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.range, mul_comm]
  have hpos : 0 < Nat.card Φ.range := Nat.card_pos
  have e3 : Nat.card Φ.ker = Nat.card (G ⧸ Φ.range) := by
    have := e1.symm.trans e2
    rw [mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [e3]
  -- `G / range ≃ R^N / P R^N`
  let ψ : (Fin N → R) →+ G ⧸ Φ.range :=
    (QuotientAddGroup.mk' Φ.range).comp
      { toFun := redI π k, map_zero' := by funext i; simp [redI], map_add' := fun x y => by funext i; simp [redI] }
  have hψ : Function.Surjective ψ := by
    intro z
    induction z using QuotientAddGroup.induction_on with | H z => ?_
    exact ⟨liftI π k z, by simp [ψ, redI_liftI]⟩
  have hker : ψ.ker = (LinearMap.range P.mulVecLin).toAddSubgroup := by
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range, mulVecLin_apply]
    show (((redI π k x : G)) : G ⧸ Φ.range) = 0 ↔ _
    rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      -- `P ỹ ≡ x mod π^k`
      have hd : ∀ i, π ^ k ∣ x i - (P *ᵥ liftI π k y) i := by
        intro i
        have h1 := liftI_mulVec_dvd π k P y i
        rw [show P.map (Ideal.Quotient.mk _) *ᵥ y = Φ y from rfl, hy] at h1
        have h2 : π ^ k ∣ liftI π k (redI π k x) i - x i := liftI_redI_dvd π k x i
        have := h2.sub h1
        rw [← dvd_neg]; convert this using 1; ring
      choose u hu using hd
      obtain ⟨w, hw⟩ := hc u
      refine ⟨liftI π k y + w, ?_⟩
      rw [mulVec_add, hw]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination -(hu i)
    · rintro ⟨y, rfl⟩
      exact ⟨redI π k y, by rw [redMat_apply, ← redI_mulVec]⟩
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, hker]
  rfl

/-- $\#R/(x) = q^e$ for $\pi^e\,\Vert\,x$. -/
theorem card_quot_span_eq {π : R} (hπ : Irreducible π) {x : R} {e : ℕ} (he : π ^ e ∣ x) (he' : ¬ π ^ (e + 1) ∣ x) :
    Nat.card (R ⧸ Ideal.span {x}) = q R ^ e := by
  obtain ⟨u, rfl⟩ := he
  have hu : IsUnit u := by
    refine dvr_isUnit_of_not_dvd hπ fun h => he' ?_
    rw [pow_succ]; exact mul_dvd_mul_left _ h
  rw [Ideal.span_singleton_mul_right_unit hu, natCard_quot_pow π hπ]

/-- $\#R/(xy) = \#R/(x)\cdot\#R/(y)$ for $x, y \ne 0$. -/
theorem card_quot_span_mul {π : R} (hπ : Irreducible π) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    Nat.card (R ⧸ Ideal.span {x * y}) = Nat.card (R ⧸ Ideal.span {x}) * Nat.card (R ⧸ Ideal.span {y}) := by
  obtain ⟨a, ha, ha'⟩ := exists_pow_dvd_not_dvd π hπ hx
  obtain ⟨b, hb, hb'⟩ := exists_pow_dvd_not_dvd π hπ hy
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  have hu : IsUnit u := dvr_isUnit_of_not_dvd hπ fun h => ha' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hw : IsUnit w := dvr_isUnit_of_not_dvd hπ fun h => hb' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  rw [show π ^ a * u * (π ^ b * w) = π ^ (a + b) * (u * w) by ring,
    Ideal.span_singleton_mul_right_unit (hu.mul hw), Ideal.span_singleton_mul_right_unit hu,
    Ideal.span_singleton_mul_right_unit hw, natCard_quot_pow π hπ, natCard_quot_pow π hπ,
    natCard_quot_pow π hπ, pow_add]

theorem card_quot_span_prod {π : R} (hπ : Irreducible π) {ι : Type*} (s : Finset ι) (a : ι → R)
    (ha : ∀ i, a i ≠ 0) :
    Nat.card (R ⧸ Ideal.span {∏ i ∈ s, a i}) = ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {a i}) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Ideal.span_singleton_one]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.2 rfl
    exact Nat.card_unique
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      card_quot_span_mul hπ (ha i) (Finset.prod_ne_zero_iff.mpr fun j _ => ha j), ih]

/-- **$[R^N : PR^N] = \#R/(\det P)$** for $\det P \ne 0$ (Smith normal form: $R^N/PR^N \cong \bigoplus_iR/(a_i)$ with
$\prod_ia_i \sim \det P$; as Mathlib's `Submodule.natAbs_det_equiv` over $\mathbb Z$). -/
theorem card_quot_range {π : R} (hπ : Irreducible π) (P : Matrix (Fin N) (Fin N) R) (hP : P.det ≠ 0) :
    Nat.card ((Fin N → R) ⧸ LinearMap.range P.mulVecLin) = Nat.card (R ⧸ Ideal.span {P.det}) := by
  classical
  have hinj : Function.Injective P.mulVecLin := mulVec_injective_of_det_ne_zero P hP
  set Nsub := LinearMap.range P.mulVecLin
  have h : Module.finrank R Nsub = Module.finrank R (Fin N → R) := LinearMap.finrank_range_of_inj hinj
  let b := Pi.basisFun R (Fin N)
  let a := Submodule.smithNormalFormCoeffs b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
  -- the quotient
  have hq : Nat.card ((Fin N → R) ⧸ Nsub) = ∏ i, Nat.card (R ⧸ Ideal.span {a i}) := by
    rw [Nat.card_congr (Submodule.quotientEquivPiSpan Nsub b h).toEquiv, Nat.card_pi]
  rw [hq, ← card_quot_span_prod hπ Finset.univ a ha]
  -- `det P ∼ ∏ a i`
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : (Fin N → R) ≃ₗ[R] Nsub := b'.equiv ab (Equiv.refl _)
  let f : (Fin N → R) →ₗ[R] (Fin N → R) := Nsub.subtype.comp (e' : (Fin N → R) →ₗ[R] Nsub)
  have hf : ∀ i, f (b' i) = a i • b' i := by
    intro i
    show ((b'.equiv ab (Equiv.refl _) (b' i) : Nsub) : Fin N → R) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdetf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, hf, map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  let e : (Fin N → R) ≃ₗ[R] Nsub := LinearEquiv.ofInjective P.mulVecLin hinj
  have hP' : Nsub.subtype.comp (e : (Fin N → R) →ₗ[R] Nsub) = P.mulVecLin := by
    ext x; rfl
  have hassoc : Associated (LinearMap.det (Nsub.subtype.comp (e : (Fin N → R) →ₗ[R] Nsub)))
      (LinearMap.det f) := LinearMap.associated_det_comp_equiv _ e e'
  rw [hP', show P.mulVecLin = Matrix.toLin' P from rfl, LinearMap.det_toLin', hdetf] at hassoc
  rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]

end Index

end QuadFormsKB.Tamagawa
