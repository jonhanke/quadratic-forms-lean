/-
# O'Meara 93:28, sufficiency: the reduction chain for lattices with a bounded scale gap

**Setting** (as in `Sec93FSuffGood.lean`, `Sec93FSuffDim4.lean`, `Sec93FCore8.lean`): $R$ a Henselian discrete
valuation ring with finite residue field, $F$ its fraction field of characteristic $0$, $2$ not a unit of $R$.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 1/2, p. 272, keeping track of a property of the
scales so that the induction of step 8 can also decrease the scale gap): copies of the reduction chain
`GoodSuffNP 8 P t → GoodSuff4P P t → GoodSuffP P t → SuffP P t` in which every statement carries the extra hypothesis
`P t (fun k => scale Q (Ls k))` on the splitting `Ls` of $L$, for an arbitrary property `P` of the sequence of scales
that is `ScaleClosed` (kept when all scales are multiplied by one fractional ideal; `Sec93FGap.lean`). All reductions
(adjunctions, scaling the form, removing a hyperbolic plane, moving by an isometry, passing to a subspace) keep the
scales up to one common factor, hence keep `P`. Examples are the gap bound `gapP R G` and `firstP R`.
-/
import QuadFormsKB.Literature.OMeara.Sec93FGap

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Gap

universe u v

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass Dim4

section Defs

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **`Suff t` restricted by a property of the scales**: the sufficiency in 93:28 for $t$ Jordan components, for $L$
whose splitting `Ls` has scales satisfying `P t (fun k => scale Q (Ls k))`, where `P` is a property of the sequence of
scales (fractional ideals). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def SuffP (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → P t (fun k => scale Q (Ls k)) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- **`GoodSuff t` restricted by a property `P` of the scales**. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def GoodSuffP (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → P t (fun k => scale Q (Ls k)) → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- **`Dim4.GoodSuff4 t` restricted by a property `P` of the scales**. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def GoodSuff4P (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → P t (fun k => scale Q (Ls k)) → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- **`Core8.GoodSuffN n t` restricted by a property `P` of the scales**. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def GoodSuffNP (n : ℕ) (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → P t (fun k => scale Q (Ls k)) → (∀ k, finrank R (Ls k) = n) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- `GoodSuffP` for the lattices whose total rank is at most $4t + N$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
def GoodSuffBdP (P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop) (t N : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → P t (fun k => scale Q (Ls k)) → (∀ k, 3 ≤ finrank R (Ls k)) →
      ∑ k, finrank R (Ls k) ≤ 4 * t + N →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

end Defs

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)] {P : ∀ t : ℕ, (Fin t → Submodule R F) → Prop}

set_option maxHeartbeats 1000000 in
/-- **Reduction to good lattices, restricted by a property of the scales** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 2, p. 272): `SuffGood.suff_of_good` with the property `P` of the scales threaded through the
adjunctions (which keep the scales) and the scaling of the form (which multiplies all scales by one factor). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem suff_of_goodP (hHil : LocalHilbertField F) (hPc : ScaleClosed P) {t : ℕ} (hG : GoodSuffP.{u, v} R F P t) :
    SuffP.{u, v} R F P t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hL hK hGap hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hL k) (fundSub_ne_bot Q hLfg hL k)
  -- (A1) all dimensions `≥ 3`
  obtain ⟨h1L, h1K, h1S, h1C, h1d, h1s, h1b⟩ := suff_adj_dims Q hLfg hKfg hL hK ha0 hS hC
  set Q1 := Q.prod (Q.prod Q) with hQ1
  have hQ1n : (QuadraticMap.associated Q1).Nondegenerate :=
    nondegenerate_prod Q (Q.prod Q) hQ (nondegenerate_prod Q Q hQ hQ)
  have hLL : (L.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hL1 : (L.prod (L.prod L)).IsLattice F := isLattice_prod ‹_› hLL
  have hK1 : (K.prod (L.prod L)).IsLattice F := isLattice_prod ‹_› hLL
  have hL1fg : (L.prod (L.prod L)).FG := Submodule.IsLattice.fg (A := F)
  have hK1fg : (K.prod (L.prod L)).FG := Submodule.IsLattice.fg (A := F)
  -- (A2) saturated splittings
  obtain ⟨Js, hJs⟩ := (saturatedSplittingExistence hHil Q1).exists_saturated h2p hQ1n _ _ h1L h1d
  obtain ⟨h2L, h2K, h2S, h2C, h2d, h2s, h2b⟩ := suff_adj_sat Q1 hL1fg hK1fg h1L h1K hJs ha0 h1S h1C
  set Q2 := Q1.prod Q1 with hQ2
  have hQ2n : (QuadraticMap.associated Q2).Nondegenerate := nondegenerate_prod Q1 Q1 hQ1n hQ1n
  have hL2 : ((L.prod (L.prod L)).prod (L.prod (L.prod L))).IsLattice F := isLattice_prod ‹_› ‹_›
  have hK2 : ((K.prod (L.prod L)).prod (L.prod (L.prod L))).IsLattice F := isLattice_prod ‹_› ‹_›
  have hL2fg : ((L.prod (L.prod L)).prod (L.prod (L.prod L))).FG := Submodule.IsLattice.fg (A := F)
  have hK2fg : ((K.prod (L.prod L)).prod (L.prod (L.prod L))).FG := Submodule.IsLattice.fg (A := F)
  -- (A3) hyperbolic spaces
  obtain ⟨h3L, h3K, h3S, h3C, h3d, h3s, h3T, h3b⟩ := suff_adj_hyp Q2 hL2fg hK2fg h2L h2K ha0 h2S h2C
  set Q3 := Q2.prod ((-1 : F) • Q2) with hQ3
  have hQ3n : (QuadraticMap.associated Q3).Nondegenerate :=
    nondegenerate_prod Q2 _ hQ2n (nondegenerate_smul Q2 (by norm_num) hQ2n)
  set L2 := (L.prod (L.prod L)).prod (L.prod (L.prod L)) with hL2def
  set K2 := (K.prod (L.prod L)).prod (L.prod (L.prod L)) with hK2def
  have hL3 : (L2.prod L2).IsLattice F := isLattice_prod ‹_› ‹_›
  have hK3 : (K2.prod L2).IsLattice F := isLattice_prod ‹_› ‹_›
  set Ls3 := fun k => ((Ls k).prod ((Ls k).prod (Ls k))).prod (Js k) with hLs3
  have hL3fg : (L2.prod L2).FG := Submodule.IsLattice.fg (A := F)
  -- scaling by `(s L_1)⁻¹`
  obtain ⟨σ, hσ0, hσ⟩ : ∃ σ : F, σ ≠ 0 ∧ ∀ k : Fin t, (k : ℕ) = 0 →
      scale Q3 ((Ls3 k).prod (Ls3 k)) = R ∙ σ := by
    rcases t with _ | t
    · exact ⟨1, one_ne_zero, fun k => k.elim0⟩
    · have hk0 : ((Ls3 0).prod (Ls3 0)).FG :=
        FG.of_le hL3fg (h3L.1.split.iSup_eq ▸ le_iSup (fun k => (Ls3 k).prod (Ls3 k)) 0)
      obtain ⟨x, -, y, -, hxy⟩ := exists_scale_eq Q3 hk0
      have hne : scale Q3 ((Ls3 0).prod (Ls3 0)) ≠ ⊥ := (h3L.1.modular 0).2.1 ▸ (h3L.1.modular 0).1
      refine ⟨bil Q3 x y, fun h => hne (by rw [hxy, h, span_singleton_eq_bot]), fun k hk => ?_⟩
      rw [show k = 0 from Fin.ext hk]; exact hxy
  have hσi : σ⁻¹ ≠ 0 := inv_ne_zero hσ0
  have hreg3 := isRegular_of_lattice_max Q3 hQ3n hL3
  have hrk3 : ∀ k, finrank R ((Ls3 k).prod (Ls3 k)) = finrank R ((((Ks k).prod ((Ls k).prod (Ls k))).prod
      (Js k)).prod (Ls3 k)) := fun k => by
    obtain ⟨⟨h0, hT⟩, -, -⟩ := h3S
    have := (hT k).1; rwa [show Fin.cast h0 k = k from Fin.ext (by simp)] at this
  -- the gap bound survives: the scales of `(Ls3 k).prod (Ls3 k)` for `σ⁻¹ • Q3` are those of `Ls k` times `σ⁻¹`
  have hs3 : ∀ k, scale Q3 ((Ls3 k).prod (Ls3 k)) = scale Q (Ls k) := fun k =>
    (h3s k).trans ((h2s k).trans (h1s k))
  have hGap3 : P t (fun k => scale (σ⁻¹ • Q3) ((Ls3 k).prod (Ls3 k))) :=
    hPc.of_eq_mul (R ∙ σ⁻¹) (fun k => by rw [scale_smul_form, hs3 k]) hGap
  have hiso := hG (σ⁻¹ • Q3) h2p (nondegenerate_smul Q3 hσi hQ3n) (L2.prod L2) (K2.prod L2) _ _ _
    ((isSaturated_smul_form_iff Q3 hσi).mpr h3L) ((isSaturated_smul_form_iff Q3 hσi).mpr h3K) hGap3
    (fun k => le_trans (h1d k) (le_trans (h2d k) (h3d k)))
    (fun k => by
      obtain ⟨T, hT0, hTs, hTd⟩ := h3T k
      exact ⟨T, fun x hx => by simp [hT0 x hx], hTs, hTd⟩)
    (fun k hk => by
      rw [scale_smul_form, hσ k hk, Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hσ0,
        ← Submodule.one_eq_span])
    (sameFund_smul Q3 hσi h3S)
    (cond_smul Q3 hσi hL3fg (Submodule.IsLattice.fg (A := F)) h2p hreg3 h3L.1 h3K.1 hrk3 h3S.2.1 h3C)
  exact h1b (h2b (h3b (isometricLat_of_smul Q3 hσi hiso)))

set_option maxHeartbeats 1000000 in
/-- **The plane-removal step, restricted by a property of the scales** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 2, p. 272): `Dim4.step_plane` with the property `P` of the scales carried to the splitting of the
subspace $P^\perp$ (the scales are those of `Ls`, by `scale_repl_eq`). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem step_planeP (hHil : LocalHilbertField F) (hPc : ScaleClosed P) {t N : ℕ}
    (ih : GoodSuffBdP.{u, v} R F P t N)
    {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (h2p : ¬ IsUnit (2 : R)) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [hLl : L.IsLattice F] [hKl : K.IsLattice F] (Ls Ks : Fin t → Submodule R V)
    (a : Fin t → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks)
    (hGap : P t (fun k => scale Q (Ls k))) (hd : ∀ k, 3 ≤ finrank R (Ls k))
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : ∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond93 Q L Ls Ks a) (hbd : ∑ k, finrank R (Ls k) ≤ 4 * t + N + 1) (k0 : Fin t)
    (hk0 : 5 ≤ finrank R (Ls k0)) : IsometricLat Q Q L K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hKle : ∀ k, Ks k ≤ K := fun k => hKs.1.split.iSup_eq ▸ le_iSup Ks k
  have hregL := isRegular_of_lattice_max Q hQ hLl
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  have hk0fg : (Ls k0).FG := FG.of_le hLfg (hLle k0)
  have hKk0fg : (Ks k0).FG := FG.of_le hKfg (hKle k0)
  obtain ⟨x₀, -, y₀, -, hxy₀⟩ := exists_scale_eq Q hk0fg
  have hne : scale Q (Ls k0) ≠ ⊥ := (hLs.1.modular k0).1
  have hα : bil Q x₀ y₀ ≠ 0 := fun h => hne (by rw [hxy₀, h, span_singleton_eq_bot.mpr rfl])
  set α := bil Q x₀ y₀ with hαdef
  have hLmod : IsModular Q (R ∙ α) (Ls k0) := by rw [← hxy₀]; exact hLs.1.modular k0
  obtain ⟨⟨h0, hTy⟩, -, -⟩ := id hS
  have hc0 : Fin.cast h0 k0 = k0 := Fin.ext rfl
  have hscK : scale Q (Ks k0) = R ∙ α := by
    have := (hTy k0).2.1; rw [hc0] at this; rw [← this, hxy₀]
  have hKmod : IsModular Q (R ∙ α) (Ks k0) := by rw [← hscK]; exact hKs.1.modular k0
  have hrkK : finrank R (Ls k0) = finrank R (Ks k0) := by have := (hTy k0).1; rwa [hc0] at this
  obtain ⟨x, y, L', hx, hy, hxy, hOSL, hL'mod', hL'fg, hrkL⟩ := exists_plane_split Q hHil h2p hk0fg hα hLmod hk0
  obtain ⟨x', y', K', hx', hy', hxy', hOSK, hK'mod', hK'fg, hrkK'⟩ :=
    exists_plane_split Q hHil h2p hKk0fg hα hKmod (hrkK ▸ hk0)
  obtain ⟨σ, hσ, hσP⟩ := exists_orth_plane (R := R) Q hQ hx hy hx' hy' hxy hxy' hα
  have hinj : Function.Injective (σ : V →ₗ[F] V) := σ.injective
  have hφ : ∀ z, Q ((σ : V →ₗ[F] V) z) = Q z := fun z => hσ z
  -- move `K`
  haveI : (latMap σ K).IsLattice F := SuffSub.isLattice_latMap
  have hK₁fg : (latMap σ K).FG := Submodule.IsLattice.fg (A := F)
  have hKs₁ : IsSaturated Q (latMap σ K) (fun k => latMap σ (Ks k)) :=
    SuffSub.isSaturated_latMap Q hσ hKle hKfg hKs
  have hS₁ : SameFundamentalInvariants Q Q L (latMap σ K) Ls (fun k => latMap σ (Ks k)) a :=
    sameFund_moveK Q hσ hKle hS
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin t → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hC₁ : Cond93 Q L Ls (fun k => latMap σ (Ks k)) a :=
    cond93_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
      (fun i => by rw [← SuffSub.jordanChain_latMap]; exact isometricLat_latMap Q hσ _) hC
  have hOSK₁ : IsOrthSum Q ((fun k => latMap σ (Ks k)) k0) (span R {x, y}) (latMap σ K') := by
    have := isOrthSum_latMap Q hσ hOSK
    rwa [hσP] at this
  have hK₁'fg : (latMap σ K').FG := hK'fg.map _
  have hscK₁ : scale Q (latMap σ (Ks k0)) = R ∙ α := by
    rw [SuffSub.scale_map Q Q hinj hφ (hKle k0), hscK]
  have hK₁'mod : IsModular Q (scale Q ((fun k => latMap σ (Ks k)) k0)) (latMap σ K') := by
    show IsModular Q (scale Q (latMap σ (Ks k0))) (latMap σ K')
    rw [hscK₁]
    exact IsometricLat.isModular Q Q (adj_isometricLat_trans Q Q Q ⟨LinearEquiv.refl R _, fun x => rfl⟩
      (isometricLat_latMap Q hσ K')) hK'fg hK'mod'
  have hPl : IsPlane Q (span R {x, y}) (R ∙ α) := isPlane_span hx hy hxy hα
  have hL'mod : IsModular Q (scale Q (Ls k0)) L' := by rw [hxy₀]; exact hL'mod'
  have hsumL := isOrthSum_plane Q hLs.1.split hOSL hPl.regular
  have hsumK := isOrthSum_plane Q hKs₁.1.split hOSK₁ hPl.regular
  have hLs' := isSaturated_repl Q hLfg hLs hOSL hPl hL'mod
  have hKs' := isSaturated_repl Q hK₁fg hKs₁ hOSK₁ hPl hK₁'mod
  have hS' := sameFund_repl Q hLfg hK₁fg hLs.1 hKs₁.1 hOSL hOSK₁ hPl hL'mod hK₁'mod hS₁
  have hC' := cond93_repl Q hLfg hK₁fg hLs.1 hKs₁.1 hOSL hOSK₁ hPl hL'mod hK₁'mod ha0 hC₁
  have hLsfg := fg_repl Q hLfg hLs.1 hOSL hPl
  have hKsfg := fg_repl Q hK₁fg hKs₁.1 hOSK₁ hPl
  -- restrict to `W = P^⊥`
  have hspL := span_eq_perpF Q hPl.regular hsumL
  have hspK := span_eq_perpF Q hPl.regular hsumK
  set W := perpF Q (span R {x, y} : Submodule R V) with hW
  have hLW : (⨆ k, repl Ls k0 L' k) ≤ W.restrictScalars R := fun z hz => hspL ▸ subset_span hz
  have hKW : (⨆ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k) ≤ W.restrictScalars R :=
    fun z hz => hspK ▸ subset_span hz
  have hLWl := SuffSub.isLattice_subLatIn hLW hLsfg hspL
  have hKWl := SuffSub.isLattice_subLatIn hKW hKsfg hspK
  have hQW : (QuadraticMap.associated (SuffSub.QW Q W)).Nondegenerate :=
    SuffSub.nondegenerate_QW Q hQ (span_sup_perpF Q hPl.regular hsumL) fun w hw u hu => perpF_orth_span Q hw hu
  have hsLs : ∀ k, repl Ls k0 L' k ≤ ⨆ k, repl Ls k0 L' k := fun k => le_iSup (repl Ls k0 L') k
  have hsKs : ∀ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k ≤
      ⨆ k, repl (fun k => latMap σ (Ks k)) k0 (latMap σ K') k :=
    fun k => le_iSup (repl (fun k => latMap σ (Ks k)) k0 (latMap σ K')) k
  have hSatL := SuffSub.isSaturated_subLatIn Q hLW hsLs hLsfg hLs'
  have hSatK := SuffSub.isSaturated_subLatIn Q hKW hsKs hKsfg hKs'
  have hSW := (SuffSub.sameFundamentalInvariants_subLatIn Q hLW hKW hsLs hsKs _).mp hS'
  have hCW := (SuffSub.cond93_subLatIn Q hLW hKW hsLs hsKs hLsfg hKsfg _).mp hC'
  -- the hypotheses of the induction hypothesis
  have hrkP : finrank R (span R {x, y} : Submodule R V) = 2 := hPl.finrank_eq
  have hsum := sum_finrank_repl Q hOSL
  have hd' : ∀ k, 3 ≤ finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) := fun k => by
    rw [SuffSub.finrank_subLatIn (X := ⨆ k, repl Ls k0 L' k) hLW (hsLs k)]
    by_cases h : k = k0
    · subst h; rw [repl_self]; omega
    · rw [repl_of_ne Ls L' h]; exact hd k
  have hHyp : ∀ k, ∃ T : Submodule F V, (∀ z ∈ T, Q z = 0) ∧ (∀ z ∈ T, z ∈ span F (repl Ls k0 L' k : Set V)) ∧
      finrank R (repl Ls k0 L' k) ≤ 2 * finrank F T := fun k => by
    by_cases h : k = k0
    · subst h
      obtain ⟨T, hT0, hTM, hrk⟩ := hT k
      have hMreg : IsRegular Q (Ls k) := (hLs.1.modular k).isRegular Q hk0fg
      obtain ⟨T', h1, h2, h3⟩ := hyp_descent Q hMreg hk0fg hx hy hxy hα hOSL hrkL T hT0 hTM hrk
      exact ⟨T', h1, by rw [repl_self]; exact h2, by rw [repl_self]; exact h3⟩
    · rw [repl_of_ne Ls L' h]; exact hT k
  have hT' : ∀ k, ∃ T : Submodule F W, (∀ z ∈ T, SuffSub.QW Q W z = 0) ∧
      (∀ z ∈ T, z ∈ span F ((SuffSub.subLatIn W (repl Ls k0 L' k) : Submodule R W) : Set W)) ∧
      finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) ≤ 2 * finrank F T := fun k => by
    obtain ⟨T, h1, h2, h3⟩ := hHyp k
    exact hyp_to_sub Q ((hsLs k).trans hLW) h1 h2 h3
  have hsc' : ∀ k : Fin t, (k : ℕ) = 0 → scale (SuffSub.QW Q W) (SuffSub.subLatIn W (repl Ls k0 L' k)) = 1 :=
    fun k hk => by
      rw [SuffSub.scale_subLatIn Q hLW (hsLs k), scale_repl_eq Q hL'mod]; exact hsc k hk
  have hbd' : ∑ k, finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) ≤ 4 * t + N := by
    have : ∀ k, finrank R (SuffSub.subLatIn W (repl Ls k0 L' k)) = finrank R (repl Ls k0 L' k) := fun k =>
      SuffSub.finrank_subLatIn (X := ⨆ k, repl Ls k0 L' k) hLW (hsLs k)
    simp only [this]
    omega
  -- the gap bound: the scales of the new splitting are those of `Ls`
  have hGap' : P t (fun k => scale (SuffSub.QW Q W) (SuffSub.subLatIn W (repl Ls k0 L' k))) :=
    hPc.of_eq (fun k => by rw [SuffSub.scale_subLatIn Q hLW (hsLs k), scale_repl_eq Q hL'mod]) hGap
  haveI := hLWl
  haveI := hKWl
  have hisoW := ih (SuffSub.QW Q W) h2p hQW _ _ _ _ a hSatL hSatK hGap' hd' hbd' hT' hsc' hSW hCW
  have hiso := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK₁ := isometricLat_of_tail Q hPl.fg hLsfg hsumL hsumK hiso
  exact adj_isometricLat_trans Q Q Q hLK₁ (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))

/-- `GoodSuff4P` gives the case $N = 0$ of `GoodSuffBdP`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem goodSuffBdP_zero {t : ℕ} (h4 : GoodSuff4P.{u, v} R F P t) : GoodSuffBdP.{u, v} R F P t 0 := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hGap hd hbd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hrk4 : ∀ k, 4 ≤ finrank R (Ls k) := fun k => by
    obtain ⟨T, hT0, hTM, hrk⟩ := hT k
    have hfg : (Ls k).FG := FG.of_le hLfg (hLle k)
    have hreg : IsRegular Q (Ls k) := (hLs.1.modular k).isRegular Q hfg
    have := two_finrank_le_rank Q hfg hreg T hT0 hTM
    have := hd k
    omega
  have h4' : ∀ k, finrank R (Ls k) = 4 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := hcon
    have : 4 * t < ∑ k, finrank R (Ls k) := by
      calc 4 * t = ∑ _k : Fin t, 4 := by simp [mul_comm]
        _ < ∑ k, finrank R (Ls k) :=
          Finset.sum_lt_sum (fun k _ => hrk4 k) ⟨k, Finset.mem_univ _, lt_of_le_of_ne (hrk4 k) (Ne.symm hk)⟩
    omega
  exact h4 Q h2p hQ L K Ls Ks a hLs hKs hGap hd h4' hT hsc hS hC

/-- The case $N+1$ of `GoodSuffBdP` from the case $N$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem goodSuffBdP_succ (hHil : LocalHilbertField F) (hPc : ScaleClosed P) {t N : ℕ}
    (ih : GoodSuffBdP.{u, v} R F P t N) : GoodSuffBdP.{u, v} R F P t (N + 1) := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hGap hd hbd hT hsc hS hC
  by_cases hle : ∑ k, finrank R (Ls k) ≤ 4 * t + N
  · exact ih Q h2p hQ L K Ls Ks a hLs hKs hGap hd hle hT hsc hS hC
  · have : ∃ k0, 5 ≤ finrank R (Ls k0) := by
      by_contra hcon
      push_neg at hcon
      have : ∑ k, finrank R (Ls k) ≤ 4 * t :=
        calc ∑ k, finrank R (Ls k) ≤ ∑ _k : Fin t, 4 := Finset.sum_le_sum fun k _ => by have := hcon k; omega
          _ = 4 * t := by simp [mul_comm]
      omega
    obtain ⟨k0, hk0⟩ := this
    exact step_planeP hHil hPc ih Q h2p hQ L K Ls Ks a hLs hKs hGap hd hT hsc hS hC (by omega) k0 hk0

/-- **Reduction of the good situation to dimension exactly $4$, restricted by a property of the scales** (O'Meara
1963, §93F, proof of 93:28, sufficiency, step 2, p. 272). -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem goodSuff_of_goodSuff4P (hHil : LocalHilbertField F) (hPc : ScaleClosed P) {t : ℕ}
    (h4 : GoodSuff4P.{u, v} R F P t) : GoodSuffP.{u, v} R F P t := by
  have hall : ∀ N, GoodSuffBdP.{u, v} R F P t N := fun N => by
    induction N with
    | zero => exact goodSuffBdP_zero h4
    | succ N ih => exact goodSuffBdP_succ hHil hPc ih
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hGap hd hT hsc hS hC
  exact hall (∑ k, finrank R (Ls k)) Q h2p hQ L K Ls Ks a hLs hKs hGap hd (by omega) hT hsc hS hC

/-- **From rank $8$ to rank $4$, restricted by a property of the scales** (O'Meara 1963, §93F, proof of 93:28,
sufficiency, step 2, p. 272): adjoining $L$ with the form $-Q$ keeps the scales. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1/2, p. 272 (gap-bounded)"]
theorem goodSuff4_of_goodSuff8P (hPc : ScaleClosed P) {t : ℕ} (h8 : GoodSuffNP.{u, v} R F 8 P t) :
    GoodSuff4P.{u, v} R F P t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hLs hKs hGap _ hd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hLs.1 k) (fundSub_ne_bot Q hLfg hLs.1 k)
  obtain ⟨h3L, h3K, h3S, h3C, -, h3s, h3T, h3b⟩ := suff_adj_hyp Q hLfg hKfg hLs hKs ha0 hS hC
  have hLk : ∀ k, (Ls k).FG := fun k => FG.of_le hLfg (hLs.1.split.iSup_eq ▸ le_iSup Ls k)
  have hLL : (L.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hKL : (K.prod L).IsLattice F := isLattice_prod ‹_› ‹_›
  have hQn : (QuadraticMap.associated (Q.prod ((-1 : F) • Q))).Nondegenerate :=
    nondegenerate_prod Q _ hQ (nondegenerate_smul Q (by norm_num) hQ)
  refine h3b (h8 (Q.prod ((-1 : F) • Q)) h2p hQn (L.prod L) (K.prod L) _ _ a h3L h3K
    (hPc.of_eq (fun k => h3s k) hGap) (fun k => ?_) h3T
    (fun k hk => by rw [h3s k]; exact hsc k hk) h3S h3C)
  have hm1 : (-1 : F) ≠ 0 := by norm_num
  have hspan1 : (R ∙ (-1 : F)) = 1 := by
    rw [Submodule.one_eq_span]; apply le_antisymm
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
    · rw [span_singleton_le_iff_mem]; exact mem_span_singleton.2 ⟨-1, by simp⟩
  have hLn : IsJordanSplitting ((-1 : F) • Q) L Ls := isJordanSplitting_smul_form Q hm1 hLs.1
  have hscn : scale ((-1 : F) • Q) (Ls k) = scale Q (Ls k) := by rw [scale_smul_form, hspan1, one_mul]
  have hmod : IsModular ((-1 : F) • Q) (scale Q (Ls k)) (Ls k) := hscn ▸ hLn.modular k
  rw [(isModular_prod Q ((-1 : F) • Q) (hLs.1.modular k) hmod (hLk k) (hLk k)).2, hd k]

end QuadFormsKB.OMeara.Gap
