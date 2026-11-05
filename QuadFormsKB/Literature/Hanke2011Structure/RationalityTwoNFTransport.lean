/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import Mathlib
import QuadFormsKB.Literature.Hanke2011Structure.LocalGeneraNF
import QuadFormsKB.Literature.Hanke2011Structure.RationalityNondyadicGenusNF
import QuadFormsKB.Literature.Hanke2011Structure.RationalityTwoNFIso

/-!
# Paper 6, Theorem 5.4 at $F_{\mathfrak p} = \mathbb Q_2$ of a number field: transport of local genera

J. Hanke, *The structure of masses of rank n quadratic lattices of varying determinant over number fields*,
arXiv:1108.3580 (`hanke2011structure`), Thm. 5.4, p. 23-24.

Let $\sigma : \mathfrak o_{\mathfrak p} \cong \mathfrak o_{\mathfrak p'}$ be a ring isomorphism of the integers of two
completions (of two number fields).  It extends to the fraction fields $\hat\sigma : F_{\mathfrak p} \cong F_{\mathfrak p'}$
(`fracIso`).  This file transports along $\sigma$ the data of the local genera:

* `locMap σ : LocGenus v n ≃ LocGenus v' n`, $T \mapsto \sigma_*T$;
* `Nondeg`, `Prim` are preserved (`nondeg_locMap`, `prim_locMap`);
* the squareclass group: `sqMap σ : LocalSqCl v → LocalSqCl v'` (injective), with $\det_H(\sigma_*G) = \hat\sigma(\det_HG)$
  (`det_locMap`);
* the Hasse invariant is preserved (`hasse_locMap`): the Hilbert symbol $(a,b)_K$ is defined algebraically
  (`hilbertSymbol_equiv`), so $\hat\sigma$ preserves $c(g)$ (`hasseC_map_equiv`).

The density $\beta$ is treated in `RationalityTwoNFBeta.lean`.
-/

open IsDedekindDomain NumberField Matrix QuadFormsKB.Siegel QuadFormsKB.Lattices

namespace QuadFormsKB.Hanke2011Structure.RatTwoNF

noncomputable section

/-! ### The Hilbert symbol and the Hasse invariant under a field isomorphism -/

section Hasse

variable {K K' : Type*} [Field K] [Field K']

theorem hilbert_aux (τ : K ≃+* K') (a b : K)
    (h : ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) :
    ∃ x y z : K', (x, y, z) ≠ 0 ∧ z ^ 2 = τ a * x ^ 2 + τ b * y ^ 2 := by
  obtain ⟨x, y, z, hne, hz⟩ := h
  refine ⟨τ x, τ y, τ z, ?_, ?_⟩
  · intro h0
    apply hne
    simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, map_eq_zero_iff _ τ.injective] at h0 ⊢
    exact h0
  · simpa using congrArg τ hz

/-- **The Hilbert symbol is invariant under field isomorphisms** ($(a,b)_K$ is defined algebraically). -/
theorem hilbertSymbol_equiv (τ : K ≃+* K') (a b : K) : hilbertSymbol K' (τ a) (τ b) = hilbertSymbol K a b := by
  unfold hilbertSymbol
  have : (∃ x y z : K', (x, y, z) ≠ 0 ∧ z ^ 2 = τ a * x ^ 2 + τ b * y ^ 2) ↔
      (∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2) := by
    constructor
    · intro h
      simpa using hilbert_aux τ.symm (τ a) (τ b) h
    · exact hilbert_aux τ a b
  by_cases h : ∃ x y z : K, (x, y, z) ≠ 0 ∧ z ^ 2 = a * x ^ 2 + b * y ^ 2
  · rw [if_pos (this.2 h), if_pos h]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h]

theorem hasseVec_equiv (τ : K ≃+* K') {n : ℕ} (a : Fin n → K) :
    PadicClass.hasseVec (fun i => τ (a i)) = PadicClass.hasseVec a := by
  unfold PadicClass.hasseVec
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · exact hilbertSymbol_equiv τ _ _
  · rfl

variable [CharZero K] [CharZero K']

theorem diag_map {n : ℕ} (τ : K →+* K') (a : Fin n → K) :
    (QuadForm.diag a).map τ = QuadForm.diag (fun i => τ (a i)) := by
  ext i j
  simp only [QuadForm.map, QuadForm.diag, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; rfl
  · simp

/-- **The Hasse–Minkowski invariant is invariant under a field isomorphism** between fields satisfying the local
Hilbert-symbol axioms. -/
theorem hasseC_map_equiv (hK : PadicClass.LocalHilbertField K) (hK' : PadicClass.LocalHilbertField K')
    (τ : K ≃+* K') {n : ℕ} (g : QuadForm K n) :
    Composition.hasseC (g.map (τ : K →+* K')) = Composition.hasseC g := by
  classical
  have hdet : (g.map (τ : K →+* K')).hessian.det = τ g.hessian.det := by
    rw [QuadForm.hessian_map']; exact (RingHom.map_det (τ : K →+* K') g.hessian).symm
  by_cases hg : g.Nondegenerate
  · have hg' : (g.map (τ : K →+* K')).Nondegenerate := by
      unfold QuadForm.Nondegenerate at hg ⊢
      rw [hdet]; exact fun h => hg (τ.injective (by rw [h, map_zero]))
    unfold Composition.hasseC
    simp only [hg, hg', ↓reduceDIte]
    obtain ⟨ha0, haiso⟩ := Classical.choose_spec (FieldGen.exists_isometric_diag g hg)
    obtain ⟨hb0, hbiso⟩ := Classical.choose_spec (FieldGen.exists_isometric_diag (g.map (τ : K →+* K')) hg')
    set a := Classical.choose (FieldGen.exists_isometric_diag g hg)
    set b := Classical.choose (FieldGen.exists_isometric_diag (g.map (τ : K →+* K')) hg')
    have hmap : (g.map (τ : K →+* K')).IsometricIn K' (QuadForm.diag fun i => τ (a i)) := by
      obtain ⟨P, hP, hx⟩ := haiso
      refine ⟨P.map τ, ?_, fun y => ?_⟩
      · have := hP.map (τ : K →+* K')
        rw [RingHom.map_det] at this
        exact this
      · obtain ⟨x, rfl⟩ : ∃ x, y = fun i => τ (x i) := ⟨fun i => τ.symm (y i), by ext; simp⟩
        have e1 : (P.map τ) *ᵥ (fun i => τ (x i)) = fun i => τ ((P *ᵥ x) i) := by
          funext i
          exact (RingHom.map_mulVec (τ : K →+* K') P x i).symm
        rw [e1]
        refine (Lattices.eval_map_comp (τ : K →+* K') g (P *ᵥ x)).trans ((congrArg τ (hx x)).trans ?_)
        have h2 := Lattices.eval_map_comp (τ : K →+* K') (QuadForm.diag a) x
        rw [diag_map] at h2
        exact h2.symm
    have hb : PadicClass.hasseVec b = PadicClass.hasseVec (fun i => τ (a i)) :=
      PadicClass.hasseVec_eq_of_isometric hK' n b _ hb0 (fun i => by simpa using ha0 i)
        (QuadForm.isometricIn_trans _ (QuadForm.isometricIn_symm _ hbiso) hmap)
    rw [hb, hasseVec_equiv]
  · have hg' : ¬ (g.map (τ : K →+* K')).Nondegenerate := by
      unfold QuadForm.Nondegenerate at hg ⊢
      rw [hdet]; intro h; apply h
      push Not at hg; rw [hg, map_zero]
    unfold Composition.hasseC
    simp only [hg, hg', ↓reduceDIte]

end Hasse

/-! ### Transport of local genera along a ring isomorphism of the completions' integers -/

section Genus

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F']
  {v : HeightOneSpectrum (𝓞 F)} {v' : HeightOneSpectrum (𝓞 F')} {n : ℕ}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "Fv'" => v'.adicCompletion F'
local notation "𝔬'" => v'.adicCompletionIntegers F'
local notation "Fw" => v'.adicCompletion F'
local notation "𝔮" => v'.adicCompletionIntegers F'

variable (σ : v.adicCompletionIntegers F ≃+* v'.adicCompletionIntegers F')
include σ

/-- **The extension $\hat\sigma : F_{\mathfrak p} \cong F_{\mathfrak p'}$** of a ring isomorphism of the integers
(the completions are the fraction fields of their rings of integers). -/
def fracIso : Fv ≃+* Fv' := IsFractionRing.ringEquivOfRingEquiv (A := 𝔬) (B := 𝔬') (K := Fv) (L := Fv') σ

theorem fracIso_algebraMap (x : 𝔬) : fracIso σ (algebraMap 𝔬 Fv x) = algebraMap 𝔬' Fv' (σ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x

theorem fracIso_comp :
    ((fracIso σ : Fv ≃+* Fv') : Fv →+* Fv').comp (algebraMap 𝔬 Fv) = (algebraMap 𝔬' Fv').comp (σ : 𝔬 →+* 𝔬') :=
  RingHom.ext (fracIso_algebraMap σ)

/-- **Transport of local genera** $G \mapsto \sigma_*G$ along $\sigma : \mathfrak o_{\mathfrak p} \cong \mathfrak o_{\mathfrak p'}$. -/
def locMap : LocGenus v n ≃ LocGenus v' n where
  toFun G := Quotient.liftOn G (fun T => LocGenus.mk (T.map (σ : 𝔬 →+* 𝔬')))
    (fun _ _ h => LocGenus.mk_eq_mk.2 (IsometricGL.map_ringEquiv σ h))
  invFun G := Quotient.liftOn G (fun T => LocGenus.mk (T.map (σ.symm : 𝔬' →+* 𝔬)))
    (fun _ _ h => LocGenus.mk_eq_mk.2 (IsometricGL.map_ringEquiv σ.symm h))
  left_inv G := by
    induction G using Quotient.inductionOn with
    | _ T =>
      show LocGenus.mk ((T.map (σ : 𝔬 →+* 𝔬')).map (σ.symm : 𝔬' →+* 𝔬)) = LocGenus.mk T
      rw [QuadForm.map_map]
      have e : (σ.symm : 𝔬' →+* 𝔬).comp (σ : 𝔬 →+* 𝔬') = RingHom.id 𝔬 := RingHom.ext fun x => σ.symm_apply_apply x
      rw [e, QuadForm.map_id']
  right_inv G := by
    induction G using Quotient.inductionOn with
    | _ T =>
      show LocGenus.mk ((T.map (σ.symm : 𝔬' →+* 𝔬)).map (σ : 𝔬 →+* 𝔬')) = LocGenus.mk T
      rw [QuadForm.map_map]
      have e : (σ : 𝔬 →+* 𝔬').comp (σ.symm : 𝔬' →+* 𝔬) = RingHom.id 𝔬' := RingHom.ext fun x => σ.apply_symm_apply x
      rw [e, QuadForm.map_id']

theorem locMap_mk (T : QuadForm 𝔬 n) : locMap σ (LocGenus.mk T) = LocGenus.mk (T.map (σ : 𝔬 →+* 𝔬')) := rfl

theorem hessian_det_map (T : QuadForm 𝔬 n) :
    (T.map (σ : 𝔬 →+* 𝔬')).hessian.det = σ T.hessian.det := by
  rw [QuadForm.hessian_map']; exact (RingHom.map_det (σ : 𝔬 →+* 𝔬') T.hessian).symm

/-- Nondegeneracy is preserved by $\sigma_*$. -/
theorem nondeg_locMap (G : LocGenus v n) : (locMap σ G).Nondeg ↔ G.Nondeg := by
  induction G using Quotient.inductionOn with
  | _ T =>
    change (locMap σ (LocGenus.mk T)).Nondeg ↔ (LocGenus.mk T).Nondeg
    rw [locMap_mk, LocGenus.nondeg_mk, LocGenus.nondeg_mk, hessian_det_map]
    exact (map_ne_zero_iff _ σ.injective)

/-- Primitivity is preserved by $\sigma_*$. -/
theorem prim_map (T : QuadForm 𝔬 n) : IsPrimitiveForm (T.map (σ : 𝔬 →+* 𝔬')) ↔ IsPrimitiveForm T := by
  unfold IsPrimitiveForm
  have e : Ideal.span (Set.range fun p : Fin n × Fin n => (T.map (σ : 𝔬 →+* 𝔬')).coeff p.1 p.2) =
      Ideal.map (σ : 𝔬 →+* 𝔬') (Ideal.span (Set.range fun p : Fin n × Fin n => T.coeff p.1 p.2)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [e]
  constructor
  · intro h
    have := Ideal.comap_map_of_bijective (f := (σ : 𝔬 →+* 𝔬')) σ.bijective
      (I := Ideal.span (Set.range fun p : Fin n × Fin n => T.coeff p.1 p.2))
    rw [h, Ideal.comap_top] at this
    exact this.symm
  · intro h
    rw [h, Ideal.map_top]

theorem prim_locMap (G : LocGenus v n) : (locMap σ G).Prim ↔ G.Prim := by
  induction G using Quotient.inductionOn with
  | _ T =>
    change (locMap σ (LocGenus.mk T)).Prim ↔ (LocGenus.mk T).Prim
    rw [locMap_mk, LocGenus.prim_mk, LocGenus.prim_mk, prim_map]

/-! #### Squareclasses -/

/-- The induced isomorphism of unit groups $F_{\mathfrak p}^\times \to F_{\mathfrak p'}^\times$. -/
def unitsMap : Fvˣ →* Fv'ˣ := Units.map ((fracIso σ : Fv ≃+* Fv') : Fv →* Fv')

theorem unitsMap_val (x : Fvˣ) : ((unitsMap σ x : Fv'ˣ) : Fv') = fracIso σ (x : Fv) := rfl

theorem unitsMap_localUnits {u : Fvˣ} (hu : u ∈ localUnits v) : unitsMap σ u ∈ localUnits v' := by
  obtain ⟨t, rfl⟩ := hu
  refine ⟨Units.map (σ : 𝔬 →* 𝔬') t, ?_⟩
  apply Units.ext
  simp only [Units.coe_map, unitsMap_val]
  exact (fracIso_algebraMap σ (t : 𝔬)).symm

/-- **The map of squareclass groups** $\mathrm{SqCl}(F_{\mathfrak p}^\times,\mathcal O_{\mathfrak p}^\times) \to
\mathrm{SqCl}(F_{\mathfrak p'}^\times,\mathcal O_{\mathfrak p'}^\times)$ induced by $\hat\sigma$. -/
def sqMap : LocalSqCl v →* LocalSqCl v' :=
  QuotientGroup.map _ _ (unitsMap σ) (by
    rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_comap.2 ⟨unitsMap σ u, unitsMap_localUnits σ hu, ?_⟩
    simp [powMonoidHom_apply, map_pow])

theorem sqMap_mk (x : Fvˣ) : sqMap σ (SqCl.mk x) = SqCl.mk (unitsMap σ x) := rfl

theorem sqMap_injective : Function.Injective (sqMap σ) := by
  intro S S' h
  obtain ⟨x, rfl⟩ := SqCl.mk_surjective S
  obtain ⟨y, rfl⟩ := SqCl.mk_surjective S'
  rw [sqMap_mk, sqMap_mk] at h
  obtain ⟨t, ht⟩ := (RatND.sqCl_mk_eq_iff_nf _ _).1 h
  refine (RatND.sqCl_mk_eq_iff_nf x y).2 ⟨Units.map (σ.symm : 𝔮 →* 𝔬) t, ?_⟩
  apply (fracIso σ).injective
  rw [map_mul, map_pow]
  have : fracIso σ (((Units.map (σ.symm : 𝔮 →* 𝔬) t : 𝔬ˣ) : 𝔬) : Fv) = ((t : 𝔮) : Fw) := by
    show fracIso σ (algebraMap 𝔬 Fv _) = algebraMap 𝔮 Fw _
    rw [fracIso_algebraMap]
    simp
  rw [this]
  exact ht

/-- $\det_H(\sigma_*G) = \hat\sigma(\det_HG)$. -/
theorem det_locMap (G : LocGenus v n) : (locMap σ G).det = sqMap σ G.det := by
  induction G using Quotient.inductionOn with
  | _ T =>
    change (locMap σ (LocGenus.mk T)).det = sqMap σ (LocGenus.mk T).det
    rw [locMap_mk, LocGenus.det_mk, LocGenus.det_mk]
    by_cases h : algebraMap 𝔬 Fv T.hessian.det ≠ 0
    · have h' : algebraMap 𝔮 Fw (T.map (σ : 𝔬 →+* 𝔮)).hessian.det ≠ 0 := by
        rw [algebraMap_ne_zero_iff, hessian_det_map]
        exact (map_ne_zero_iff _ σ.injective).2 (algebraMap_ne_zero_iff.1 h)
      rw [detSqForm_of_ne h, detSqForm_of_ne h', sqMap_mk]
      congr 1
      apply Units.ext
      show algebraMap 𝔮 Fw _ = fracIso σ (algebraMap 𝔬 Fv _)
      rw [fracIso_algebraMap, hessian_det_map]
    · have h' : ¬ algebraMap 𝔮 Fw (T.map (σ : 𝔬 →+* 𝔮)).hessian.det ≠ 0 := by
        rw [algebraMap_ne_zero_iff, hessian_det_map]
        intro h2
        exact h (algebraMap_ne_zero_iff.2 (fun h0 => h2 (by rw [h0, map_zero])))
      unfold detSqForm
      rw [dif_neg h, dif_neg h', map_one]

/-- The Hasse invariant is preserved by $\sigma_*$. -/
theorem hasse_locMap (G : LocGenus v n) : (locMap σ G).hasse = G.hasse := by
  induction G using Quotient.inductionOn with
  | _ T =>
    change (locMap σ (LocGenus.mk T)).hasse = (LocGenus.mk T).hasse
    rw [locMap_mk, LocGenus.hasse_mk, LocGenus.hasse_mk]
    unfold hasseForm
    have e : (T.map (σ : 𝔬 →+* 𝔮)).map (algebraMap 𝔮 Fw) =
        (T.map (algebraMap 𝔬 Fv)).map ((fracIso σ : Fv ≃+* Fw) : Fv →+* Fw) := by
      rw [QuadForm.map_map, QuadForm.map_map, fracIso_comp]
    rw [e]
    exact hasseC_map_equiv (HasseIsoNF.localHilbertField_adicCompletion v)
      (HasseIsoNF.localHilbertField_adicCompletion v') (fracIso σ) _

/-- **$G_{\mathfrak p} \in \mathrm{Gen}^*_{\mathfrak p}(S,\varepsilon;n)$ is transported by $\sigma_*$, $S \mapsto \hat\sigma S$.** -/
theorem isGenStar_locMap (S : LocalSqCl v) (ε : ℤ) (G : LocGenus v n) :
    (locMap σ G).IsGenStar (sqMap σ S) ε ↔ G.IsGenStar S ε := by
  unfold LocGenus.IsGenStar
  rw [nondeg_locMap, prim_locMap, det_locMap, (sqMap_injective σ).eq_iff, hasse_locMap]

end Genus

end

end QuadFormsKB.Hanke2011Structure.RatTwoNF

#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.hasseC_map_equiv
#print axioms QuadFormsKB.Hanke2011Structure.RatTwoNF.isGenStar_locMap
