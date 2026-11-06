/-
# O'Meara 93:29 over a 2-adic field: reduction to dimension 4

**Setting** (as in `Sec93G29Good.lean`).

**Proves** (O'Meara 1963, §93G, proof of 93:29, sufficiency, p. 278: "By making suitable hyperbolic cancellations we can
assume that $\dim L_i = \dim K_i = 4$"): the copy of `Dim4.step_plane`, `Dim4.goodSuff_of_goodSuff4` with conditions (i),
(ii) of 93:29 in place of (i)–(iii) of 93:28: `GoodSuff29Four t` implies `GoodSuff29 t`.
-/
import QuadFormsKB.Literature.OMeara.Sec93G29Good

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.G29

universe u v

section Dim4

open Sat93 Adjoin28 NecI Suff28 SuffRed SuffGood SuffStep SuffMain PadicClass Nec93 Dim4



variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The sufficiency of 93:29 for good lattices of dimension exactly $4$** (O'Meara 1963, §93G, p. 278, "we can assume that $\dim L_i = \dim K_i = 4$"): `GoodSuff29` with the extra hypothesis that every component has rank $4$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
def GoodSuff29Four (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) → (∀ k, finrank R (Ls k) = 4) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond29 Q Ls Ks → IsometricLat Q Q L K

/-- `GoodSuff29` for the lattices whose total rank $\sum_k \operatorname{rank} L_k$ is at most $4t + N$. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
def GoodSuff29Bd (t N : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      ∑ k, finrank R (Ls k) ≤ 4 * t + N →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond29 Q Ls Ks → IsometricLat Q Q L K

variable {R F}

/-- **The plane-removal step for 93:29** (O'Meara 1963, §93G, p. 278): in a good situation with a component of rank $\ge 5$, split a hyperbolic plane off $L_{k_0}$ and (after Witt) off $K_{k_0}$, pass to $P^\perp$ and apply the induction hypothesis (`Dim4.step_plane` with conditions (i), (ii) of 93:29). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
theorem step_plane29 (hHil : LocalHilbertField F) {t N : ℕ} (ih : GoodSuff29Bd.{u, v} R F t N)
    {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V) (h2tw : IsTwoAdic R) (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [hLl : L.IsLattice F] [hKl : K.IsLattice F] (Ls Ks : Fin t → Submodule R V)
    (a : Fin t → F) (hLs : IsSaturated Q L Ls) (hKs : IsSaturated Q K Ks) (hd : ∀ k, 3 ≤ finrank R (Ls k))
    (hT : ∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
      finrank R (Ls k) ≤ 2 * finrank F T)
    (hsc : ∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) (hS : SameFundamentalInvariants Q Q L K Ls Ks a)
    (hC : Cond29 Q Ls Ks) (hbd : ∑ k, finrank R (Ls k) ≤ 4 * t + N + 1) (k0 : Fin t)
    (hk0 : 5 ≤ finrank R (Ls k0)) : IsometricLat Q Q L K := by
  have h2p : ¬ IsUnit (2 : R) := (twoAdic_irreducible h2tw).not_isUnit
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
  have hC₁ : Cond29 Q Ls (fun k => latMap σ (Ks k)) :=
    cond29_congr_right Q (hchfg hLfg hLle) (hchfg hKfg hKle)
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
  have hC' := cond29_repl Q hLfg hK₁fg hLs.1 hKs₁.1 hOSL hOSK₁ hPl hL'mod hK₁'mod hC₁
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
  have hCW := (cond29_subLatIn Q hLW hKW hsLs hsKs hLsfg hKsfg).mp hC'
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
  haveI := hLWl
  haveI := hKWl
  have hisoW := ih (SuffSub.QW Q W) h2tw hQW _ _ _ _ a hSatL hSatK hd' hbd' hT' hsc' hSW hCW
  have hiso := (SuffSub.isometricLat_subLatIn Q hLW hKW).mpr hisoW
  have hLK₁ := isometricLat_of_tail Q hPl.fg hLsfg hsumL hsumK hiso
  exact adj_isometricLat_trans Q Q Q hLK₁ (adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ K))


/-- `GoodSuff29Four` gives the case $N = 0$ of `GoodSuff29Bd`. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
theorem goodSuff29Bd_zero {t : ℕ} (h4 : GoodSuff29Four.{u, v} R F t) : GoodSuff29Bd.{u, v} R F t 0 := by
  intro V _ _ _ _ _ Q h2tw hQ L K _ _ Ls Ks a hLs hKs hd hbd hT hsc hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hLle : ∀ k, Ls k ≤ L := fun k => hLs.1.split.iSup_eq ▸ le_iSup Ls k
  have hrk4 : ∀ k, 4 ≤ finrank R (Ls k) := fun k => by
    obtain ⟨T, hT0, hTM, hrk⟩ := hT k
    have hfg : (Ls k).FG := FG.of_le hLfg (hLle k)
    have hreg : IsRegular Q (Ls k) := (hLs.1.modular k).isRegular Q hfg
    have := Dim4.two_finrank_le_rank Q hfg hreg T hT0 hTM
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
  exact h4 Q h2tw hQ L K Ls Ks a hLs hKs hd h4' hT hsc hS hC

/-- The case $N+1$ of `GoodSuff29Bd` from the case $N$: if some component has rank $\ge 5$, remove a plane (`step_plane29`). -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
theorem goodSuff29Bd_succ (hHil : LocalHilbertField F) {t N : ℕ} (ih : GoodSuff29Bd.{u, v} R F t N) :
    GoodSuff29Bd.{u, v} R F t (N + 1) := by
  intro V _ _ _ _ _ Q h2tw hQ L K _ _ Ls Ks a hLs hKs hd hbd hT hsc hS hC
  by_cases hle : ∑ k, finrank R (Ls k) ≤ 4 * t + N
  · exact ih Q h2tw hQ L K Ls Ks a hLs hKs hd hle hT hsc hS hC
  · have : ∃ k0, 5 ≤ finrank R (Ls k0) := by
      by_contra hcon
      push_neg at hcon
      have : ∑ k, finrank R (Ls k) ≤ 4 * t :=
        calc ∑ k, finrank R (Ls k) ≤ ∑ _k : Fin t, 4 := Finset.sum_le_sum fun k _ => by have := hcon k; omega
          _ = 4 * t := by simp [mul_comm]
      omega
    obtain ⟨k0, hk0⟩ := this
    exact step_plane29 hHil ih Q h2tw hQ L K Ls Ks a hLs hKs hd hT hsc hS hC (by omega) k0 hk0

/-- **Reduction of the good situation to dimension exactly $4$ for 93:29** (O'Meara 1963, §93G, p. 278: "by suitable cancellations we can assume that $\dim L_i = \dim K_i = 4$"): `GoodSuff29Four t` implies `GoodSuff29 t`. -/
@[kb "omeara1963" "§93G, proof of 93:29, sufficiency, p. 278 (reduction to dimension 4)"]
theorem goodSuff29_of_four (hHil : LocalHilbertField F) {t : ℕ} (h4 : GoodSuff29Four.{u, v} R F t) :
    GoodSuff29.{u, v} R F t := by
  have hall : ∀ N, GoodSuff29Bd.{u, v} R F t N := fun N => by
    induction N with
    | zero => exact goodSuff29Bd_zero h4
    | succ N ih => exact goodSuff29Bd_succ hHil ih
  intro V _ _ _ _ _ Q h2tw hQ L K _ _ Ls Ks a hLs hKs hd hT hsc hS hC
  exact hall (∑ k, finrank R (Ls k)) Q h2tw hQ L K Ls Ks a hLs hKs hd (by omega) hT hsc hS hC

end Dim4

end QuadFormsKB.OMeara.G29
