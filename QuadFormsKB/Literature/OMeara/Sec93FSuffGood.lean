/-
# O'Meara 93:28, sufficiency, step 2: reduction to good lattices

**Setting** (as in `Sec93FSuff.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$ of characteristic $0$, $2 \in F^\times$, $(V, Q)$ a regular finite-dimensional quadratic space.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272: "by making suitable hyperbolic
adjunctions we can increase all the fundamental dimensions ... take a saturated splitting ... A similar argument
involving the adjunction of the lattice $L^{-1}$ allows us to assume that each space $FL_i$ is hyperbolic. ... we can
assume that $L_1$ and $K_1$ are unimodular")
* `Suff`, `GoodSuff`: the sufficiency of (i)–(iii) for Jordan splittings with $t$ components, and for *good* ones
  (saturated, all dimensions $\ge 3$, every $FL_k$ hyperbolic, $\mathfrak sL_1 = \mathfrak o$);
* `suff_of_good`: `GoodSuff t` implies `Suff t` (adjunctions A1–A3 and scaling).
-/
import QuadFormsKB.Literature.OMeara.Sec93FSuffRed
import QuadFormsKB.Literature.OMeara.Sec93SatProof

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.SuffGood

open Sat93 Adjoin28 NecI Suff28 SuffRed PadicClass

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The sufficiency in 93:28 for $t$ Jordan components**: if $L$, $K$ are lattices on a regular quadratic space over
a dyadic field with Jordan splittings `Ls`, `Ks` (of $t$ components) of the same fundamental invariants (norm
generators `a`) and conditions (i)–(iii) hold, then $L \cong K$. -/
def Suff (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → SameFundamentalInvariants Q Q L K Ls Ks a →
      Cond93 Q L Ls Ks a → IsometricLat Q Q L K

/-- **The sufficiency in 93:28 for good lattices** (O'Meara 1963, p. 272, the situation after step 2): as `Suff`, for
saturated splittings with all dimensions $\ge 3$, every space $FL_k$ hyperbolic (a totally isotropic subspace
$T \subseteq FL_k$ with $\dim L_k \le 2 \dim T$) and $L_1$ ($0$-based: `Ls 0`) of scale $\mathfrak o$. -/
def GoodSuff (t : ℕ) : Prop :=
  ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (Ls Ks : Fin t → Submodule R V) (a : Fin t → F),
      IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      (∀ k : Fin t, (k : ℕ) = 0 → scale Q (Ls k) = 1) →
      SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a → IsometricLat Q Q L K

variable {R F}

omit [HenselianLocalRing R] [Finite (ResidueField R)] [CharZero F] in
/-- Scaling the form does not change isometry of lattices. -/
theorem isometricLat_of_smul {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    (Q : QuadraticForm F V) {α : F} (hα : α ≠ 0) {L K : Submodule R V} (h : IsometricLat (α • Q) (α • Q) L K) :
    IsometricLat Q Q L K := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun x => by
    have := hf x
    simp only [smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hα this⟩

set_option maxHeartbeats 1000000 in
/-- **Reduction to good lattices** (O'Meara 1963, §93F, proof of 93:28, sufficiency, step 2, p. 272): the
sufficiency for good lattices with $t$ components implies it for all lattices with $t$ components. The adjunctions
are $L \perp L$ (dimensions), a saturated splitting of $L$ (93:21), $L^{-1}$ (hyperbolic spaces), each cancelled by
93:14a, followed by scaling the form by $\mathfrak sL_1^{-1}$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 2, p. 272 (the reductions)"]
theorem suff_of_good (hHil : LocalHilbertField F) {t : ℕ} (hG : GoodSuff.{u, v} R F t) : Suff.{u, v} R F t := by
  intro V _ _ _ _ _ Q h2p hQ L K _ _ Ls Ks a hL hK hS hC
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hregL := isRegular_of_lattice_max Q hQ ‹L.IsLattice F›
  have ha0 : ∀ k, a k ≠ 0 := fun k =>
    (hS.2.1 k).ne_zero Q (isRegular_fundSub Q hLfg hregL hL k) (fundSub_ne_bot Q hLfg hL k)
  -- (A1) all dimensions `≥ 3`
  obtain ⟨h1L, h1K, h1S, h1C, h1d, -, h1b⟩ := suff_adj_dims Q hLfg hKfg hL hK ha0 hS hC
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
  obtain ⟨h2L, h2K, h2S, h2C, h2d, -, h2b⟩ := suff_adj_sat Q1 hL1fg hK1fg h1L h1K hJs ha0 h1S h1C
  set Q2 := Q1.prod Q1 with hQ2
  have hQ2n : (QuadraticMap.associated Q2).Nondegenerate := nondegenerate_prod Q1 Q1 hQ1n hQ1n
  have hL2 : ((L.prod (L.prod L)).prod (L.prod (L.prod L))).IsLattice F := isLattice_prod ‹_› ‹_›
  have hK2 : ((K.prod (L.prod L)).prod (L.prod (L.prod L))).IsLattice F := isLattice_prod ‹_› ‹_›
  have hL2fg : ((L.prod (L.prod L)).prod (L.prod (L.prod L))).FG := Submodule.IsLattice.fg (A := F)
  have hK2fg : ((K.prod (L.prod L)).prod (L.prod (L.prod L))).FG := Submodule.IsLattice.fg (A := F)
  -- (A3) hyperbolic spaces
  obtain ⟨h3L, h3K, h3S, h3C, h3d, -, h3T, h3b⟩ := suff_adj_hyp Q2 hL2fg hK2fg h2L h2K ha0 h2S h2C
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
  have hiso := hG (σ⁻¹ • Q3) h2p (nondegenerate_smul Q3 hσi hQ3n) (L2.prod L2) (K2.prod L2) _ _ _
    ((isSaturated_smul_form_iff Q3 hσi).mpr h3L) ((isSaturated_smul_form_iff Q3 hσi).mpr h3K)
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

end QuadFormsKB.OMeara.SuffGood
