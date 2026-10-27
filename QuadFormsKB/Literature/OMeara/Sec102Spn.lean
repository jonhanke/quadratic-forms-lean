/-
# O'Meara Example 102:2: the numbers $g(L)$ and $g^+(L)$ of spinor genera

**Layer:** as in `Literature/OMeara/Sec102.lean`: $V = F^n$ over a number field, lattices `Lat F n`, the spinor genus
`SameSpinorGenus` and the proper spinor genus `SameProperSpinorGenus`.

**Defines** (O'Meara 1973, §102A, pp. 298–299) the number $g(L)$ of spinor genera in $\operatorname{gen}L$
(`spinorGenusNumber`) and the number $g^+(L)$ of proper spinor genera in $\operatorname{gen}L$
(`properSpinorGenusNumber`), as `Set.ncard` of the corresponding sets of equivalence classes (so $0$ for an infinite
number; both are finite by 103:4).

**Proves** Example 102:2, second part: $g(L) \le g^+(L) \le 2g(L)$, and in fact $g^+(L) = g(L)$ or $g^+(L) = 2g(L)$
(`spinorGenusNumber_le`, `properSpinorGenusNumber_le_two_mul`, `properSpinorGenusNumber_eq`). O'Meara's argument via
102:1 is used in the form: for a fixed improper rational isometry $\tau$, whether $\tau M \in \operatorname{spn}^+M$
does not depend on $M \in \operatorname{gen}L$, because $\Sigma^{-1}\tau\Sigma\tau^{-1}$ is a commutator and lies in
$J'_V$.
-/
import QuadFormsKB.Literature.OMeara.Sec102

open NumberField IsDedekindDomain Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

variable {F : Type} [Field F] [NumberField F] {n : ℕ} (Q : QuadForm F n)

/-- The spinor genus as a setoid on lattices. -/
def spnSetoid : Setoid (Lat F n) where
  r := SameSpinorGenus Q
  iseqv := ⟨SameSpinorGenus.refl Q, SameSpinorGenus.symm Q, SameSpinorGenus.trans Q⟩

/-- The proper spinor genus as a setoid on lattices. -/
def properSpnSetoid : Setoid (Lat F n) where
  r := SameProperSpinorGenus Q
  iseqv := ⟨SameProperSpinorGenus.refl Q, SameProperSpinorGenus.symm Q, SameProperSpinorGenus.trans Q⟩

/-- The spinor genera in $\operatorname{gen}L$. -/
def genusSpinorGenera (L : Lat F n) : Set (Quotient (spnSetoid Q)) :=
  {c | ∃ M : Lat F n, Quotient.mk _ M = c ∧ SameGenus Q L.1 M.1}

/-- The proper spinor genera in $\operatorname{gen}L$. -/
def genusProperSpinorGenera (L : Lat F n) : Set (Quotient (properSpnSetoid Q)) :=
  {c | ∃ M : Lat F n, Quotient.mk _ M = c ∧ SameGenus Q L.1 M.1}

/-- **$g(L)$**, the number of spinor genera in $\operatorname{gen}L$ (O'Meara 1973, §102A, p. 298). -/
@[kb "omeara1963" "§102A, p. 298 (g(L))"]
def spinorGenusNumber (L : Lat F n) : ℕ := (genusSpinorGenera Q L).ncard

/-- **$g^+(L)$**, the number of proper spinor genera in $\operatorname{gen}L$ (O'Meara 1973, §102A, p. 299). -/
@[kb "omeara1963" "§102A, p. 299 (g⁺(L))"]
def properSpinorGenusNumber (L : Lat F n) : ℕ := (genusProperSpinorGenera Q L).ncard

/-- The spinor genus of a proper spinor genus. -/
def properSpnToSpn : Quotient (properSpnSetoid Q) → Quotient (spnSetoid Q) :=
  Quotient.map id fun _ _ h => SameProperSpinorGenus.sameSpinorGenus Q h

theorem image_properSpnToSpn (L : Lat F n) :
    properSpnToSpn Q '' genusProperSpinorGenera Q L = genusSpinorGenera Q L := by
  ext c
  constructor
  · rintro ⟨_, ⟨M, rfl, hM⟩, rfl⟩
    exact ⟨M, rfl, hM⟩
  · rintro ⟨M, rfl, hM⟩
    exact ⟨Quotient.mk _ M, ⟨M, rfl, hM⟩, rfl⟩

section Improper

variable {Q} (τ : orthGroup Q F)

/-- The two candidate proper spinor genera inside the spinor genus $c$: those of $M$ and of $\tau M$. -/
def spnLift₁ (c : Quotient (spnSetoid Q)) : Quotient (properSpnSetoid Q) := Quotient.mk _ c.out

def spnLift₂ (c : Quotient (spnSetoid Q)) : Quotient (properSpnSetoid Q) :=
  Quotient.mk _ (Lat.image (τ : GL (Fin n) F) c.out)

theorem properSpnToSpn_spnLift₁ (c : Quotient (spnSetoid Q)) : properSpnToSpn Q (spnLift₁ c) = c := by
  conv_rhs => rw [← Quotient.out_eq c]
  rfl

theorem properSpnToSpn_spnLift₂ (c : Quotient (spnSetoid Q)) : properSpnToSpn Q (spnLift₂ τ c) = c := by
  conv_rhs => rw [← Quotient.out_eq c]
  refine Quotient.sound ?_
  change SameSpinorGenus Q _ _
  exact SameSpinorGenus.symm Q (IsIsometric.sameSpinorGenus Q ⟨τ, τ.2, rfl⟩)

/-- $\tau^{-1}$ conjugates $J'_V$ into itself, and $\sigma\tau^{-1}$ is a rotation when $\det\sigma = \det\tau = -1$. -/
theorem sameProperSpinorGenus_image_of_sameSpinorGenus (hQ : Q.Nondegenerate)
    (hτ : ((τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1) {M M' : Lat F n}
    (h : SameSpinorGenus Q M M') :
    SameProperSpinorGenus Q M M' ∨ SameProperSpinorGenus Q (Lat.image (τ : GL (Fin n) F) M) M' := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  obtain ⟨γ, k, hk, rfl⟩ := (mem_latSpinorGenus Q).mp h
  rcases Tamagawa.det_eq_one_or_neg_one Q hQ γ with h1 | h1
  · exact Or.inl ((sameProperSpinorGenus_iff Q).mpr ⟨γ, h1, k, hk, rfl⟩)
  · right
    have hN := spinorKernelAf_normal Q
    refine (sameProperSpinorGenus_iff Q).mpr ⟨γ * τ⁻¹, ?_, diagF Q τ * k * (diagF Q τ)⁻¹,
      hN.conj_mem _ hk _, ?_⟩
    · rw [Tamagawa.mem_soSub, Subgroup.coe_mul, Units.val_mul, det_mul]
      have hinv : (((τ⁻¹ : orthGroup Q F) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 := by
        have h := congrArg Matrix.det (Units.mul_inv (τ : GL (Fin n) F))
        rw [det_mul, hτ, det_one] at h
        rw [Subgroup.coe_inv]; linear_combination -h
      change ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det * _ = 1
      rw [show ((γ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1 from h1, hinv]; ring
    · rw [← diagF_smul]
      change diagF Q γ • k • M = diagF Q (γ * τ⁻¹) • (diagF Q τ * k * (diagF Q τ)⁻¹) • diagF Q τ • M
      rw [← mul_smul, ← mul_smul, ← mul_smul, map_mul, map_inv]
      congr 1; group

/-- Every spinor genus in the genus contains at most the two proper spinor genera `spnLift₁ c`, `spnLift₂ τ c`. -/
theorem genusProperSpinorGenera_subset (hQ : Q.Nondegenerate)
    (hτ : ((τ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = -1) (L : Lat F n) :
    genusProperSpinorGenera Q L ⊆ spnLift₁ '' genusSpinorGenera Q L ∪ spnLift₂ τ '' genusSpinorGenera Q L := by
  rintro _ ⟨M, rfl, hM⟩
  set c : Quotient (spnSetoid Q) := Quotient.mk _ M
  have hc : c ∈ genusSpinorGenera Q L := ⟨M, rfl, hM⟩
  have hrel : SameSpinorGenus Q c.out M := Quotient.exact (Quotient.out_eq c)
  rcases sameProperSpinorGenus_image_of_sameSpinorGenus τ hQ hτ hrel with h | h
  · exact Or.inl ⟨c, hc, Quotient.sound h⟩
  · exact Or.inr ⟨c, hc, Quotient.sound h⟩

theorem spnLift_mem (L : Lat F n) {c : Quotient (spnSetoid Q)} (hc : c ∈ genusSpinorGenera Q L) :
    spnLift₁ c ∈ genusProperSpinorGenera Q L ∧ spnLift₂ τ c ∈ genusProperSpinorGenera Q L := by
  obtain ⟨M, rfl, hM⟩ := hc
  have h1 : SameGenus Q L.1 (Quotient.out (Quotient.mk (spnSetoid Q) M)).1 :=
    SameGenus.trans Q hM (SameSpinorGenus.sameGenus Q
      (Quotient.exact (Quotient.out_eq (Quotient.mk (spnSetoid Q) M))).symm)
  refine ⟨⟨_, rfl, h1⟩, ⟨_, rfl, SameGenus.trans Q h1 (IsIsometric.sameGenus Q ⟨τ, τ.2, rfl⟩)⟩⟩

/-- **Whether $\tau M \in \operatorname{spn}^+M$ is the same for all $M \in \operatorname{gen}L$** (O'Meara 1973,
proof of 102:2, via 102:1). For $M = \Sigma L$: $\Sigma^{-1}\tau\Sigma = \tau\,(\tau^{-1}\Sigma^{-1}\tau\Sigma)$ and the
commutator lies in $J'_V$. -/
theorem sameProperSpinorGenus_image_iff (hQ : Q.Nondegenerate) (L M : Lat F n) (hM : SameGenus Q L.1 M.1) :
    SameProperSpinorGenus Q M (Lat.image (τ : GL (Fin n) F) M) ↔
      SameProperSpinorGenus Q L (Lat.image (τ : GL (Fin n) F) L) := by
  let _ : MulAction (OAf Q) (Lat F n) := latAction Q
  have hmul : ∀ (a b : OAf Q) (N : Lat F n), latSMul Q (a * b) N = latSMul Q a (latSMul Q b N) :=
    fun a b N => (latAction Q).mul_smul a b N
  have hMo : M ∈ MulAction.orbit (OAf Q) L := by rw [orbit_eq_genus]; exact hM
  obtain ⟨S₀, rfl⟩ := hMo
  change SameProperSpinorGenus Q (latSMul Q S₀ L) (Lat.image _ (latSMul Q S₀ L)) ↔ _
  set t := diagF Q τ
  have hcomm : t⁻¹ * S₀⁻¹ * t * S₀ ∈ spinorKernelAf Q := by
    have := commutator_mem_spinorKernelAf Q hQ t⁻¹ S₀⁻¹
    simpa using this
  have hN := spnPlusGroup_normal Q hQ
  have hc : S₀⁻¹ * t * S₀ * t⁻¹ ∈ spnPlusGroup Q := by
    have : S₀⁻¹ * t * S₀ * t⁻¹ = t * (t⁻¹ * S₀⁻¹ * t * S₀) * t⁻¹ := by group
    rw [this]
    exact hN.conj_mem _ (le_sup_right (a := (Tamagawa.soSub Q F).map (diagF Q)) hcomm) _
  have key : ∀ N : Lat F n, Lat.image (τ : GL (Fin n) F) N = latSMul Q t N := fun N => (diagF_smul Q τ N).symm
  simp only [SameProperSpinorGenus, key]
  constructor
  · rintro ⟨g, hg, he⟩
    refine ⟨(S₀⁻¹ * t * S₀ * t⁻¹)⁻¹ * (S₀⁻¹ * g * S₀), (spnPlusGroup Q).mul_mem ((spnPlusGroup Q).inv_mem hc)
      (hN.conj_mem' _ hg S₀), ?_⟩
    calc latSMul Q ((S₀⁻¹ * t * S₀ * t⁻¹)⁻¹ * (S₀⁻¹ * g * S₀)) L
        = latSMul Q ((S₀⁻¹ * t * S₀ * t⁻¹)⁻¹ * S₀⁻¹) (latSMul Q g (latSMul Q S₀ L)) := by
          rw [← hmul, ← hmul]; congr 1; group
      _ = latSMul Q ((S₀⁻¹ * t * S₀ * t⁻¹)⁻¹ * S₀⁻¹) (latSMul Q t (latSMul Q S₀ L)) := by rw [he]
      _ = latSMul Q t L := by rw [← hmul, ← hmul]; congr 1; group
  · rintro ⟨g, hg, he⟩
    have h2 : S₀ * ((S₀⁻¹ * t * S₀ * t⁻¹) * g) * S₀⁻¹ ∈ spnPlusGroup Q :=
      hN.conj_mem _ ((spnPlusGroup Q).mul_mem hc hg) S₀
    refine ⟨S₀ * ((S₀⁻¹ * t * S₀ * t⁻¹) * g) * S₀⁻¹, h2, ?_⟩
    calc latSMul Q (S₀ * ((S₀⁻¹ * t * S₀ * t⁻¹) * g) * S₀⁻¹) (latSMul Q S₀ L)
        = latSMul Q (S₀ * (S₀⁻¹ * t * S₀ * t⁻¹)) (latSMul Q g L) := by
          rw [← hmul, ← hmul]; congr 1; group
      _ = latSMul Q (S₀ * (S₀⁻¹ * t * S₀ * t⁻¹)) (latSMul Q t L) := by rw [he]
      _ = latSMul Q t (latSMul Q S₀ L) := by rw [← hmul, ← hmul]; congr 1; group

end Improper

/-- **Example 102:2, $g(L) \le g^+(L)$** (O'Meara 1973, §102A, p. 299). -/
@[kb "omeara1963" "§102A, 102:2, p. 299 (g(L) ≤ g⁺(L))"]
theorem spinorGenusNumber_le (hQ : Q.Nondegenerate) (L : Lat F n) :
    spinorGenusNumber Q L ≤ properSpinorGenusNumber Q L := by
  unfold spinorGenusNumber properSpinorGenusNumber
  by_cases hfin : (genusProperSpinorGenera Q L).Finite
  · rw [← image_properSpnToSpn]
    exact Set.ncard_image_le hfin
  · have hinf : ¬ (genusSpinorGenera Q L).Finite := by
      intro hG
      apply hfin
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        refine (hG.image spnLift₁).subset ?_
        rintro _ ⟨M, rfl, hM⟩
        set c : Quotient (spnSetoid Q) := Quotient.mk _ M
        obtain ⟨γ, k, hk, he⟩ := (mem_latSpinorGenus Q).mp (Quotient.exact (Quotient.out_eq c))
        exact ⟨c, ⟨M, rfl, hM⟩, Quotient.sound ((sameProperSpinorGenus_iff Q).mpr
          ⟨γ, by simp [Tamagawa.mem_soSub], k, hk, he⟩)⟩
      · obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
        exact ((hG.image _).union (hG.image _)).subset (genusProperSpinorGenera_subset τ hQ hτ L)
    rw [Set.Infinite.ncard hinf]
    exact Nat.zero_le _

/-- **Example 102:2, $g^+(L) = g(L)$ or $g^+(L) = 2g(L)$** (O'Meara 1973, §102A, p. 299): either every spinor genus
in $\operatorname{gen}L$ is a single proper spinor genus, or every one of them contains exactly two. -/
@[kb "omeara1963" "§102A, 102:2, p. 299 (g⁺(L) is g(L) or 2g(L))"]
theorem properSpinorGenusNumber_eq (hQ : Q.Nondegenerate) (L : Lat F n) :
    properSpinorGenusNumber Q L = spinorGenusNumber Q L ∨
      properSpinorGenusNumber Q L = 2 * spinorGenusNumber Q L := by
  unfold spinorGenusNumber properSpinorGenusNumber
  by_cases hG : (genusSpinorGenera Q L).Finite
  swap
  · have hinf : ¬ (genusProperSpinorGenera Q L).Finite := fun hP => hG (by
      rw [← image_properSpnToSpn]; exact hP.image _)
    left; rw [Set.Infinite.ncard hinf, Set.Infinite.ncard hG]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: every isometry is a rotation
    left
    subst hn
    rw [← image_properSpnToSpn]
    refine (Set.InjOn.ncard_image ?_).symm
    rintro _ ⟨M, rfl, -⟩ _ ⟨M', rfl, -⟩ h
    obtain ⟨γ, k, hk, he⟩ := (mem_latSpinorGenus Q).mp (Quotient.exact h)
    exact Quotient.sound ((sameProperSpinorGenus_iff Q).mpr ⟨γ, by simp [Tamagawa.mem_soSub], k, hk, he⟩)
  obtain ⟨τ, hτ⟩ := Tamagawa.exists_orthGroup_det_neg_one Q hQ hn
  have hsub := genusProperSpinorGenera_subset τ hQ hτ L
  have hinj₁ : Set.InjOn spnLift₁ (genusSpinorGenera Q L) := fun c _ c' _ h => by
    rw [← properSpnToSpn_spnLift₁ (Q := Q) c, h, properSpnToSpn_spnLift₁]
  have hinj₂ : Set.InjOn (spnLift₂ τ) (genusSpinorGenera Q L) := fun c _ c' _ h => by
    rw [← properSpnToSpn_spnLift₂ τ c, h, properSpnToSpn_spnLift₂]
  have himg : spnLift₁ '' genusSpinorGenera Q L ∪ spnLift₂ τ '' genusSpinorGenera Q L =
      genusProperSpinorGenera Q L := by
    refine le_antisymm ?_ hsub
    rintro _ (⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    exacts [(spnLift_mem τ L hc).1, (spnLift_mem τ L hc).2]
  by_cases hP : SameProperSpinorGenus Q L (Lat.image (τ : GL (Fin n) F) L)
  · -- every spinor genus is one proper spinor genus
    left
    have heq : spnLift₂ τ '' genusSpinorGenera Q L ⊆ spnLift₁ '' genusSpinorGenera Q L := by
      rintro _ ⟨c, hc, rfl⟩
      refine ⟨c, hc, Quotient.sound ?_⟩
      obtain ⟨M, rfl, hM⟩ := id hc
      have hM' : SameGenus Q L.1 (Quotient.out (Quotient.mk (spnSetoid Q) M)).1 :=
        SameGenus.trans Q hM (SameSpinorGenus.sameGenus Q
          (Quotient.exact (Quotient.out_eq (Quotient.mk (spnSetoid Q) M))).symm)
      exact (sameProperSpinorGenus_image_iff τ hQ L _ hM').mpr hP
    rw [← himg, Set.union_eq_left.mpr heq, Set.InjOn.ncard_image hinj₁]
  · -- every spinor genus contains two proper spinor genera
    right
    have hdisj : Disjoint (spnLift₁ '' genusSpinorGenera Q L) (spnLift₂ τ '' genusSpinorGenera Q L) := by
      rw [Set.disjoint_left]
      rintro _ ⟨c, hc, rfl⟩ ⟨c', hc', he⟩
      have hcc : c' = c := by
        rw [← properSpnToSpn_spnLift₂ τ c', he, properSpnToSpn_spnLift₁]
      subst hcc
      obtain ⟨M, rfl, hM⟩ := id hc
      have hM' : SameGenus Q L.1 (Quotient.out (Quotient.mk (spnSetoid Q) M)).1 :=
        SameGenus.trans Q hM (SameSpinorGenus.sameGenus Q
          (Quotient.exact (Quotient.out_eq (Quotient.mk (spnSetoid Q) M))).symm)
      exact hP ((sameProperSpinorGenus_image_iff τ hQ L _ hM').mp
        (SameProperSpinorGenus.symm Q (Quotient.exact he)))
    rw [← himg, Set.ncard_union_eq hdisj (hG.image _) (hG.image _), Set.InjOn.ncard_image hinj₁,
      Set.InjOn.ncard_image hinj₂]
    ring

/-- **Example 102:2, $g^+(L) \le 2g(L)$** (O'Meara 1973, §102A, p. 299). -/
@[kb "omeara1963" "§102A, 102:2, p. 299 (g⁺(L) ≤ 2g(L))"]
theorem properSpinorGenusNumber_le_two_mul (hQ : Q.Nondegenerate) (L : Lat F n) :
    properSpinorGenusNumber Q L ≤ 2 * spinorGenusNumber Q L := by
  rcases properSpinorGenusNumber_eq Q hQ L with h | h <;> omega

end QuadFormsKB.Lattices
