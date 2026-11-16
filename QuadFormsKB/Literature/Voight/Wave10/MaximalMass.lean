/-
# All maximal orders have the same mass, from Proposition 26.6.4 (Voight, Theorems 25.1.1, 26.1.12)

Source: J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer 2021 (key `voight2021`): Proposition 23.4.14 and 23.4.13
(p. 384), Proposition 26.6.4 (p. 445), Theorem 25.1.1 (p. 415), Theorems 25.3.18 (p. 423) and 26.1.12 (p. 433).

**Setting.** $F$ a totally real number field, $B = (a,b)_F$ = `QuatF F a b` totally definite,
$\operatorname{mass}(\operatorname{Cls}\mathcal O)$ = `clsMass O`, completions $\mathcal O_v$ = `localOrder`.

**Contents.**
* `unitIdx_inf_symm_mat`, `unitIdx_inf_symm_local` (local): for maximal orders $\mathcal M_1, \mathcal M_2$ of
  $\mathrm M_2(F_v)$ (or of a split $B_v$),
  $[\mathcal M_1^\times : (\mathcal M_1 \cap \mathcal M_2)^\times] = [\mathcal M_2^\times : (\mathcal M_1 \cap \mathcal M_2)^\times] \ne 0$.
  *Proof.* $\mathcal M_1 \cap \mathcal M_2$ is conjugate to $\mathcal O_0(\pi^e)$ (Proposition 23.4.3), whose only two maximal
  superorders are $\mathrm M_2(R_v)$ and $\mathcal O_e$ (`Wave5.stdEichlerOrder_eq_inf_iff`); the Atkin–Lehner element
  $\varpi$ fixes $\mathcal O_0(\pi^e)$ and exchanges them (23.4.13).
* `clsMass_chain`: assuming Proposition 26.6.4, for orders $\mathcal O_0 \subseteq \mathcal O_1$ that agree outside a finite set
  $S$ of primes, $\operatorname{mass}(\operatorname{Cls}\mathcal O_0) = \prod_{v \in S}[\mathcal O_{1,v}^\times : \mathcal O_{0,v}^\times]\,
  \operatorname{mass}(\operatorname{Cls}\mathcal O_1)$.
* `clsMass_eq_of_maximal`: assuming Proposition 26.6.4 and $\mathbb Z_F$ a principal ideal domain, any two maximal orders
  have the same mass (compare both with $\mathcal O \cap \mathcal O'$).
* Consequences: the maximal-order mass formula for **every** maximal order (`eichlerMassFormulaMaximal_of`, previously
  proved only for maximal orders containing $\mathbb Z_F\langle i, j\rangle$), and the Eichler mass formula for Eichler orders
  conditional on Proposition 26.6.4 alone, over $\mathbb Q$ (`eichlerMassFormulaEichlerOrdersRat_of_massSuperorder`,
  Theorem 25.3.18) and over a totally real field with $\mathbb Z_F$ a principal ideal domain
  (`eichlerMassFormulaEichlerOrders_of_massSuperorder`, Theorem 26.1.12).
-/
import QuadFormsKB.Literature.Voight.Wave10.EichlerMass
import QuadFormsKB.Literature.Voight.Wave5.EichlerNormalizer
import QuadFormsKB.Literature.Voight.Wave3.MassFormula

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Quaternion

noncomputable section

namespace QuadFormsKB.Voight.Wave10

open QuadFormsKB.Quat QuadFormsKB.QuatOrder QuadFormsKB.Voight QuadFormsKB.Voight.Wave3 QuadFormsKB.Voight.Wave4
  QuadFormsKB.Voight.Wave5 QuadFormsKB.Voight.Wave9 QuadFormsKB.Voight.MassWave2 QuadFormsKB.NFEuler
  QuadFormsKB.Lattices

/-! ### Unit indices -/

section UnitIdx

variable {R X Y : Type*} [CommRing R] [Ring X] [Algebra R X] [Ring Y] [Algebra R Y]

/-- The unit index is transported by an algebra isomorphism $\psi$ with $\psi(A) = A'$, $\psi(B) = B'$. -/
theorem unitIdx_eq_of_map (ψ : X ≃ₐ[R] Y) {A B : Subalgebra R X} (h : A ≤ B) {A' B' : Subalgebra R Y}
    (h' : A' ≤ B') (hA : A.map (ψ : X →ₐ[R] Y) = A') (hB : B.map (ψ : X →ₐ[R] Y) = B') :
    unitIdx h = unitIdx h' := by
  rw [← unitIdx_map ψ h]
  exact unitIdx_congr _ _ hA hB

/-- $[A^\times : A^\times] = 1$. -/
theorem unitIdx_self {A : Subalgebra R X} (h : A ≤ A) : unitIdx h = 1 := by
  unfold unitIdx
  refine Subgroup.index_eq_one.2 (eq_top_iff.2 fun u _ => ⟨u, ?_⟩)
  ext
  rfl

end UnitIdx

/-! ### Two maximal orders of $\mathrm M_2(F_v)$ -/

section LocalMat

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Finite (IsLocalRing.ResidueField R)]

/-- The unit index of the standard Eichler order $\mathcal O_0(\pi^e)$ in $\mathrm M_2(R)$ is nonzero. -/
theorem unitIdx_std_ne_zero {π : R} (hπ : Irreducible π) (e : ℕ) :
    unitIdx (stdEichlerOrder_le_matOrder (K := K) π e) ≠ 0 := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have := index_units_stdEichlerOrder_zero (K := K) π
    unfold unitIdx
    rw [this]
    exact one_ne_zero
  · have := index_units_stdEichlerOrder (K := K) hπ he
    unfold unitIdx
    rw [this]
    have : 0 < LocalDensity.DVR.q R := Nat.card_pos
    positivity

/-- **Two maximal orders have the same unit index in their intersection** (Voight 2021, 23.4.13 and Proposition 23.4.3):
for maximal $R$-orders $\mathcal M_1, \mathcal M_2 \subseteq \mathrm M_2(F)$ ($R$ a discrete valuation ring with finite residue
field), $[\mathcal M_1^\times : (\mathcal M_1 \cap \mathcal M_2)^\times] = [\mathcal M_2^\times : (\mathcal M_1 \cap \mathcal M_2)^\times]$, and
this index is nonzero. -/
@[kb "voight2021" "23.4.13, p. 384; Proposition 23.4.3, p. 382"]
theorem unitIdx_inf_symm_mat {π : R} (hπ : Irreducible π) {M₁ M₂ : Subalgebra R (Matrix (Fin 2) (Fin 2) K)}
    (h₁ : IsMaximalOrder R K M₁) (h₂ : IsMaximalOrder R K M₂) :
    unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) = unitIdx (inf_le_right : M₁ ⊓ M₂ ≤ M₂) ∧
      unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) ≠ 0 := by
  have hπ0 := hπ.ne_zero
  obtain ⟨e, P, Q, hPQ, hQP, hO⟩ := localEichlerStructure (K := K) hπ (M₁ ⊓ M₂) ⟨M₁, M₂, h₁, h₂, rfl⟩
  let ψ : Matrix (Fin 2) (Fin 2) K ≃ₐ[R] Matrix (Fin 2) (Fin 2) K := (conjAlgEquiv Q P hQP hPQ).restrictScalars R
  have hψ : (ψ : Matrix (Fin 2) (Fin 2) K →ₐ[R] Matrix (Fin 2) (Fin 2) K) = conjMap Q P hQP hPQ := rfl
  have hstd : (M₁ ⊓ M₂).map (ψ : Matrix (Fin 2) (Fin 2) K →ₐ[R] Matrix (Fin 2) (Fin 2) K) =
      stdEichlerOrder R K π e := by
    rw [hψ, hO]
    exact map_map_conj hPQ hQP
  have hm₁ := h₁.map (conjAlgEquiv Q P hQP hPQ)
  have hm₂ := h₂.map (conjAlgEquiv Q P hQP hPQ)
  have hinf : stdEichlerOrder R K π e =
      M₁.map (ψ : Matrix (Fin 2) (Fin 2) K →ₐ[R] Matrix (Fin 2) (Fin 2) K) ⊓
        M₂.map (ψ : Matrix (Fin 2) (Fin 2) K →ₐ[R] Matrix (Fin 2) (Fin 2) K) := by
    rw [← hstd, Algebra.map_inf _ ψ.injective]
  have hle' : stdEichlerOrder R K π e ≤ conjMatOrder hπ0 e :=
    (stdEichlerOrder_eq_inf hπ0 e).le.trans inf_le_right
  -- the Atkin–Lehner element exchanges the two maximal orders and fixes the Eichler order
  let α : Matrix (Fin 2) (Fin 2) K ≃ₐ[R] Matrix (Fin 2) (Fin 2) K :=
    (conjAlgEquiv (alElt π e) (alEltInv π e) (alElt_mul_alEltInv hπ0 e) (alEltInv_mul_alElt hπ0 e)).restrictScalars R
  have hJ : unitIdx (stdEichlerOrder_le_matOrder (K := K) π e) = unitIdx hle' :=
    unitIdx_eq_of_map α _ hle' (map_alElt_stdEichlerOrder hπ0 e) (map_alElt_matOrder hπ0 e)
  have hJ0 := unitIdx_std_ne_zero (K := K) hπ e
  rcases (stdEichlerOrder_eq_inf_iff hπ e hm₁ hm₂).1 hinf with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
  · have l : unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) = unitIdx (stdEichlerOrder_le_matOrder (K := K) π e) :=
      unitIdx_eq_of_map ψ _ _ hstd e₁
    have r : unitIdx (inf_le_right : M₁ ⊓ M₂ ≤ M₂) = unitIdx hle' := unitIdx_eq_of_map ψ _ _ hstd e₂
    exact ⟨by rw [l, r, hJ], by rw [l]; exact hJ0⟩
  · have l : unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) = unitIdx hle' := unitIdx_eq_of_map ψ _ _ hstd e₁
    have r : unitIdx (inf_le_right : M₁ ⊓ M₂ ≤ M₂) = unitIdx (stdEichlerOrder_le_matOrder (K := K) π e) :=
      unitIdx_eq_of_map ψ _ _ hstd e₂
    exact ⟨by rw [l, r, hJ], by rw [l, ← hJ]; exact hJ0⟩

end LocalMat

/-! ### Two maximal orders of a split completion -/

section Local

variable {F : Type} [Field F] [NumberField F] {a b : 𝓞 F} (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

/-- The symmetric unit index for two maximal orders of a split completion $B_v \cong \mathrm M_2(F_v)$. -/
theorem unitIdx_inf_symm_local {M₁ M₂ : Subalgebra 𝔬 (QuatV v a b)} (h₁ : IsMaximalOrder 𝔬 Fv M₁)
    (h₂ : IsMaximalOrder 𝔬 Fv M₂) (φ : QuatV v a b ≃ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv) :
    unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) = unitIdx (inf_le_right : M₁ ⊓ M₂ ≤ M₂) ∧
      unitIdx (inf_le_left : M₁ ⊓ M₂ ≤ M₁) ≠ 0 := by
  let ψ : QuatV v a b ≃ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv := φ.restrictScalars 𝔬
  have hψ : (ψ : QuatV v a b →ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv) =
      (φ : QuatV v a b →ₐ[Fv] Matrix (Fin 2) (Fin 2) Fv).restrictScalars 𝔬 := rfl
  have hm₁ := h₁.map φ
  have hm₂ := h₂.map φ
  rw [← hψ] at hm₁ hm₂
  obtain ⟨hs, hn⟩ := unitIdx_inf_symm_mat (LocalDensity.NF.irreducible_π v) hm₁ hm₂
  have hinf : (M₁ ⊓ M₂).map (ψ : QuatV v a b →ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv) =
      M₁.map (ψ : QuatV v a b →ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv) ⊓
        M₂.map (ψ : QuatV v a b →ₐ[𝔬] Matrix (Fin 2) (Fin 2) Fv) :=
    Algebra.map_inf _ ψ.injective _ _
  have l := unitIdx_eq_of_map ψ (inf_le_left : M₁ ⊓ M₂ ≤ M₁) inf_le_left hinf rfl
  have r := unitIdx_eq_of_map ψ (inf_le_right : M₁ ⊓ M₂ ≤ M₂) inf_le_right hinf rfl
  exact ⟨by rw [l, r, hs], by rw [l]; exact hn⟩

end Local

/-! ### Chains of orders -/

section Chain

variable {F : Type} [Field F] [NumberField F]

/-- **Mass along a chain of orders** (Voight 2021, Proposition 26.6.4 applied prime by prime): assuming
`Wave6.MassSuperorder F`, if $\mathcal O_0 \subseteq \mathcal O_1$ are orders of a totally definite $B = (a,b)_F$ whose
completions agree outside a finite set $S$ of primes, then
$\operatorname{mass}(\operatorname{Cls}\mathcal O_0) = \prod_{v \in S}[\mathcal O_{1,v}^\times : \mathcal O_{0,v}^\times]\,
\operatorname{mass}(\operatorname{Cls}\mathcal O_1)$. -/
@[kb "voight2021" "Proposition 26.6.4, p. 445"]
theorem clsMass_chain [IsTotallyReal F] (H : Wave6.MassSuperorder F) {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdef : IsTotDefinite a b) {O₀ O₁ : Subalgebra (𝓞 F) (QuatF F a b)} (h₀ : IsOrder (𝓞 F) F O₀)
    (h₁ : IsOrder (𝓞 F) F O₁) (hle : O₀ ≤ O₁) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, localOrder (v := v) a b O₀ = localOrder (v := v) a b O₁) :
    clsMass O₀ = (∏ v ∈ S, (unitIdx (Wave6.localOrder_mono v hle) : ℝ)) * clsMass O₁ := by
  classical
  let G : Finset (HeightOneSpectrum (𝓞 F)) →
      ∀ v : HeightOneSpectrum (𝓞 F), Subalgebra (v.adicCompletionIntegers F) (QuatV v a b) :=
    fun T v => if v ∈ T then localOrder (v := v) a b O₁ else localOrder (v := v) a b O₀
  have hex : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ∃ O' : Subalgebra (𝓞 F) (QuatF F a b),
      IsOrder (𝓞 F) F O' ∧ ∀ v, localOrder (v := v) a b O' = G T v := by
    intro T
    refine exists_order_localOrder_eq h₀ (G T) (fun v => ?_) ?_
    · simp only [G]
      split_ifs
      · exact Gen.isOrder_localOrder_gen v h₁
      · exact Gen.isOrder_localOrder_gen v h₀
    · filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
      exact if_neg hv
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ O' : Subalgebra (𝓞 F) (QuatF F a b),
      IsOrder (𝓞 F) F O' → (∀ v, localOrder (v := v) a b O' = G T v) →
      clsMass O₀ = (∏ v ∈ T, (unitIdx (Wave6.localOrder_mono v hle) : ℝ)) * clsMass O' := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro O' hO' hloc'
      have : O₀ = O' := order_eq_of_localOrder_eq h₀ hO' fun v => by
        rw [hloc' v]
        exact (if_neg (Finset.notMem_empty v)).symm
      subst this
      rw [Finset.prod_empty, one_mul]
    | insert w T hw ih =>
      intro O' hO' hloc'
      obtain ⟨Oₜ, hOₜ, hlocₜ⟩ := hex T
      have hw₀ : localOrder (v := w) a b Oₜ = localOrder (v := w) a b O₀ := by
        rw [hlocₜ w]
        simp only [G]
        rw [if_neg hw]
      have hw' : localOrder (v := w) a b O' = localOrder (v := w) a b O₁ := by
        rw [hloc' w]
        simp only [G]
        rw [if_pos (Finset.mem_insert_self w T)]
      have hagree : ∀ v, v ≠ w → localOrder (v := v) a b Oₜ = localOrder (v := v) a b O' := by
        intro v hvw
        rw [hlocₜ v, hloc' v]
        simp only [G, Finset.mem_insert, hvw, false_or]
      have hle' : Oₜ ≤ O' := order_le_of_localOrder_le hO' fun v => by
        by_cases hvw : v = w
        · subst hvw
          rw [hw₀, hw']
          exact Wave6.localOrder_mono v hle
        · exact (hagree v hvw).le
      have hm := H inferInstance a b ha hb hdef Oₜ O' hOₜ hO' hle' w hagree
      have hidx : Wave6.localUnitIndex w hle' = unitIdx (Wave6.localOrder_mono w hle) :=
        unitIdx_congr _ _ hw₀ hw'
      rw [ih Oₜ hOₜ hlocₜ, hm, hidx, Finset.prod_insert hw]
      ring
  refine key S O₁ h₁ fun v => ?_
  simp only [G]
  split_ifs with hv
  · rfl
  · exact (hS v hv).symm

end Chain

/-! ### All maximal orders have the same mass -/

section Maximal

variable {F : Type} [Field F] [NumberField F]

/-- **The local unit indices of two maximal orders in their intersection agree** at every prime $v$, and are nonzero:
$[\mathcal O_v^\times : (\mathcal O \cap \mathcal O')_v^\times] = [\mathcal O_v'^\times : (\mathcal O \cap \mathcal O')_v^\times] \ne 0$. -/
theorem unitIdx_inf_symm_global {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) {O O' : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hO' : IsMaximalOrder (𝓞 F) F O') (v : HeightOneSpectrum (𝓞 F)) :
    unitIdx (Wave6.localOrder_mono v (inf_le_left : O ⊓ O' ≤ O)) =
        unitIdx (Wave6.localOrder_mono v (inf_le_right : O ⊓ O' ≤ O')) ∧
      unitIdx (Wave6.localOrder_mono v (inf_le_left : O ⊓ O' ≤ O)) ≠ 0 := by
  have hinf := localOrder_inf hO.1 hO'.1 v
  have l : unitIdx (Wave6.localOrder_mono v (inf_le_left : O ⊓ O' ≤ O)) =
      unitIdx (inf_le_left : localOrder (v := v) a b O ⊓ localOrder (v := v) a b O' ≤ localOrder (v := v) a b O) :=
    unitIdx_congr _ _ hinf rfl
  have r : unitIdx (Wave6.localOrder_mono v (inf_le_right : O ⊓ O' ≤ O')) =
      unitIdx (inf_le_right : localOrder (v := v) a b O ⊓ localOrder (v := v) a b O' ≤ localOrder (v := v) a b O') :=
    unitIdx_congr _ _ hinf rfl
  rw [l, r]
  have hm := isMaximalOrder_localOrder_nf (v := v) hO
  have hm' := isMaximalOrder_localOrder_nf (v := v) hO'
  rcases localOrder_ramified_or_split_nf (v := v) ha hb hO with ⟨hdiv, h1⟩ | ⟨φ, -⟩
  · have h2 := eq_valOrder_of_isMaximalOrder (R := v.adicCompletionIntegers F) hdiv
      (algebraMap_two_mul_ne_zero_nf (v := v) ha hb) hm'
    have heq : localOrder (v := v) a b O' = localOrder (v := v) a b O := h2.trans h1.symm
    have hself : localOrder (v := v) a b O ⊓ localOrder (v := v) a b O' = localOrder (v := v) a b O := by
      rw [heq, inf_idem]
    refine ⟨unitIdx_congr _ _ rfl heq.symm, ?_⟩
    rw [unitIdx_congr _ (le_refl (localOrder (v := v) a b O)) hself rfl, unitIdx_self]
    exact one_ne_zero
  · exact unitIdx_inf_symm_local v hm hm' φ

/-- **All maximal orders have the same mass** (Voight 2021, consequence of Proposition 26.6.4; cf. Lemma 26.6.2 and the
proof of Theorem 26.1.12): assuming `Wave6.MassSuperorder F` (Proposition 26.6.4), for a totally real number field $F$ whose
ring of integers is a principal ideal domain, $B = (a,b)_F$ totally definite and maximal orders $\mathcal O, \mathcal O'$,
$\operatorname{mass}(\operatorname{Cls}\mathcal O) = \operatorname{mass}(\operatorname{Cls}\mathcal O')$.

*Proof.* Compare both with $\mathcal O \cap \mathcal O'$ (`clsMass_chain`): the local unit indices at every prime agree
(`unitIdx_inf_symm_global`) and are nonzero. -/
@[kb "voight2021" "Proposition 26.6.4, p. 445"]
theorem clsMass_eq_of_maximal [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] (H : Wave6.MassSuperorder F)
    {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) (hdef : IsTotDefinite a b) {O O' : Subalgebra (𝓞 F) (QuatF F a b)}
    (hO : IsMaximalOrder (𝓞 F) F O) (hO' : IsMaximalOrder (𝓞 F) F O') : clsMass O = clsMass O' := by
  classical
  have hI : IsOrder (𝓞 F) F (O ⊓ O') := isOrder_of_isEichlerOrder ⟨O, O', hO, hO', rfl⟩
  have hev : ∀ᶠ v in Filter.cofinite, localOrder (v := v) a b (O ⊓ O') = localOrder (v := v) a b O ∧
      localOrder (v := v) a b (O ⊓ O') = localOrder (v := v) a b O' := by
    filter_upwards [loc_eventually_std (isLattice_latOf hI), loc_eventually_std (isLattice_latOf hO.1),
      loc_eventually_std (isLattice_latOf hO'.1)] with v h1 h2 h3
    exact ⟨(loc_latOf_eq_iff v).1 (h1.trans h2.symm), (loc_latOf_eq_iff v).1 (h1.trans h3.symm)⟩
  set S := (Filter.eventually_cofinite.1 hev).toFinset
  have hS : ∀ v ∉ S, localOrder (v := v) a b (O ⊓ O') = localOrder (v := v) a b O ∧
      localOrder (v := v) a b (O ⊓ O') = localOrder (v := v) a b O' := by
    intro v hv
    simpa [S] using hv
  have m₁ := clsMass_chain H ha hb hdef hI hO.1 inf_le_left S fun v hv => (hS v hv).1
  have m₂ := clsMass_chain H ha hb hdef hI hO'.1 inf_le_right S fun v hv => (hS v hv).2
  have hprod : (∏ v ∈ S, (unitIdx (Wave6.localOrder_mono v (inf_le_left : O ⊓ O' ≤ O)) : ℝ)) =
      ∏ v ∈ S, (unitIdx (Wave6.localOrder_mono v (inf_le_right : O ⊓ O' ≤ O')) : ℝ) :=
    Finset.prod_congr rfl fun v _ => by rw [(unitIdx_inf_symm_global ha hb hO hO' v).1]
  have hne : (∏ v ∈ S, (unitIdx (Wave6.localOrder_mono v (inf_le_left : O ⊓ O' ≤ O)) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => by exact_mod_cast (unitIdx_inf_symm_global ha hb hO hO' v).2
  rw [m₁, ← hprod] at m₂
  exact mul_left_cancel₀ hne m₂

/-- **The Eichler mass formula for every maximal order, from Proposition 26.6.4** (Voight 2021, Theorem 26.1.12 with
$\mathfrak M = R$): for a totally real number field $F$ whose ring of integers is a principal ideal domain,
`Wave6.MassSuperorder F` implies `EichlerMassFormulaMaximal F`. The formula was proved for maximal orders containing
$\mathbb Z_F\langle i, j\rangle$ (`Wave3.classMass_eq_maximal`); every maximal order has the same mass as one of those
(`clsMass_eq_of_maximal`). -/
@[kb "voight2021" "Main Theorem 26.1.5, p. 432; Theorem 26.1.12, p. 433; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaMaximal_of [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)] (H : Wave6.MassSuperorder F) :
    EichlerMassFormulaMaximal F := by
  intro a b ha hb hdef O hO
  have h2ab : algebraMap (𝓞 F) F (2 * a * b) ≠ 0 := by
    simpa [ha, hb] using
      mul_ne_zero (mul_ne_zero (two_ne_zero) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 ha))
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hb)
  obtain ⟨O'', hO'', hstd⟩ := exists_isMaximalOrder_ge_stdOrder (R := 𝓞 F) (K := F) h2ab
  rw [← Wave4.clsMass_eq_classMass ha hb hdef hO, clsMass_eq_of_maximal H ha hb hdef hO hO'',
    Wave4.clsMass_eq_classMass ha hb hdef hO'']
  exact classMass_eq_maximal ha hb hdef hO'' hstd

/-- **The Eichler mass formula over $\mathbb Q$ for every maximal order, from Proposition 26.6.4** (Voight 2021,
Theorem 25.1.1): `Wave6.MassSuperorder ℚ` implies `EichlerMassFormulaRat`. -/
@[kb "voight2021" "Theorem 25.1.1, p. 415; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaRat_of (H : Wave6.MassSuperorder ℚ) : EichlerMassFormulaRat := by
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom
      Rat.ringOfIntegersEquiv.symm.surjective
  intro a b ha hb hdef O hO
  have h2ab : algebraMap (𝓞 ℚ) ℚ (2 * a * b) ≠ 0 := by
    simpa [ha, hb] using
      mul_ne_zero (mul_ne_zero (two_ne_zero) ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 ha))
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 hb)
  obtain ⟨O'', hO'', hstd⟩ := exists_isMaximalOrder_ge_stdOrder (R := 𝓞 ℚ) (K := ℚ) h2ab
  rw [← Wave4.clsMass_eq_classMass ha hb hdef hO, clsMass_eq_of_maximal H ha hb hdef hO hO'',
    Wave4.clsMass_eq_classMass ha hb hdef hO'']
  exact classMass_eq_rat_maximal ha hb hdef hO'' hstd

/-- **H2 over $\mathbb Q$: the Eichler mass formula for Eichler orders, conditional on Proposition 26.6.4 only**
(Voight 2021, Theorem 25.3.18): `Wave6.MassSuperorder ℚ` implies `EichlerMassFormulaEichlerOrdersRat`, i.e. for a definite
$B = (a,b)_{\mathbb Q}$ of discriminant $D$ and an Eichler order $\mathcal O$ of level $M$,
$\sum_{[J] \in \operatorname{Cls}\mathcal O} 1/w_J = \varphi(D)\psi(M)/12$. -/
@[kb "voight2021" "Theorem 25.3.18, p. 423; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaEichlerOrdersRat_of_massSuperorder (H : Wave6.MassSuperorder ℚ) :
    EichlerMassFormulaEichlerOrdersRat :=
  eichlerMassFormulaEichlerOrdersRat_of H (eichlerMassFormulaRat_of H)

/-- **H2 over a totally real field with class number one: the Eichler mass formula for Eichler orders, conditional on
Proposition 26.6.4 only** (Voight 2021, Theorem 26.1.12): for a totally real number field $F$ whose ring of integers is a
principal ideal domain, `Wave6.MassSuperorder F` implies `EichlerMassFormulaEichlerOrders F`. -/
@[kb "voight2021" "Theorem 26.1.12, p. 433; Proposition 26.6.4, p. 445"]
theorem eichlerMassFormulaEichlerOrders_of_massSuperorder [IsTotallyReal F] [IsPrincipalIdealRing (𝓞 F)]
    (H : Wave6.MassSuperorder F) : EichlerMassFormulaEichlerOrders F :=
  eichlerMassFormulaEichlerOrders_of H (eichlerMassFormulaMaximal_of H)

end Maximal

end QuadFormsKB.Voight.Wave10
