/-
# O'Meara 93:28 from its computational core

**Setting** (as in `Sec93E.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction
field $F$, $2$ not a unit of $R$ (dyadic), $V$ a regular quadratic space over $F$.

**Proves** (O'Meara 1963, §93F, Theorem 93:28, pp. 267–276)
* `charZero_of_dyadic`: a dyadic $F$ (with $2 \ne 0$ in $F$) has characteristic $0$;
* `necessity`: $\operatorname{cls} L = \operatorname{cls} K$ implies conditions (i)–(iii) (pp. 268–272), proved
  (for fields with `LocalHilbertField`);
* `sufficiency`: conditions (i)–(iii) imply $\operatorname{cls} L = \operatorname{cls} K$, proved from the named
  statement `SuffCore` (steps 4–8 of the proof, pp. 274–276);
* `dyadicClassification_of_core`: `DyadicClassification` from `SuffCore`;
* `dyadicClassification_nf`: the same over the completion $F_\mathfrak p$ of a number field, where `LocalHilbertField`
  is proved.
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecRepPrev
import QuadFormsKB.Literature.OMeara.Sec93FSuffMain

open QuadraticMap Submodule Module IsLocalRing

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Main28

open Suff28 SuffGood SuffMain

section CharZero

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]

/-- **A dyadic field has characteristic $0$**: if $2$ is invertible in the fraction field $F$ of $R$ but not a unit
of $R$, then $F$ has characteristic $0$ (in characteristic $p \ne 2$, $2 \cdot \frac{p+1}{2} = 1$ in the prime
ring, which lies in $R$). -/
theorem charZero_of_dyadic (h2p : ¬ IsUnit (2 : R)) : CharZero F := by
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases CharP.char_is_prime_or_zero F p with hpr | h0
  · exfalso
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact two_ne_zero' F (by exact_mod_cast CharP.cast_eq_zero F 2) |>.elim
    have hodd : Odd p := hpr.odd_of_ne_two hp2
    have hk : 2 * ((p + 1) / 2) = p + 1 := Nat.two_mul_div_two_of_even (hodd.add_one)
    have hm : (2 : R) * (((p + 1) / 2 : ℕ) : R) = 1 := by
      apply IsFractionRing.injective R F
      have : ((2 * ((p + 1) / 2) : ℕ) : F) = 1 := by
        rw [hk]; push_cast; rw [CharP.cast_eq_zero F p, zero_add]
      rw [map_mul, map_ofNat, map_natCast, map_one]
      exact_mod_cast this
    exact h2p ⟨⟨2, _, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  · subst h0
    exact CharP.charP_to_charZero F

omit [IsFractionRing R F] [Invertible (2 : F)] in
/-- $2 \ne 0$ in $R$ when $2$ is invertible in the field $F$. -/
theorem two_ne_zero_R (F : Type*) [Field F] [Algebra R F] [Invertible (2 : F)] : (2 : R) ≠ 0 := by
  intro h
  have h' := congrArg (algebraMap R F) h
  rw [map_ofNat, map_zero] at h'
  exact two_ne_zero' F (by exact_mod_cast h') |>.elim

end CharZero

section Main

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **93:28, necessity** (O'Meara 1963, §93F, proof of 93:28, necessity, pp. 268–272): if $L$, $K$ are lattices on a
regular quadratic space over a dyadic field (with `LocalHilbertField`) with Jordan splittings of the same fundamental
invariants and $\operatorname{cls} L = \operatorname{cls} K$, then conditions (i)–(iii) hold. Write $L = \sigma K$
with $\sigma \in O(V)$; then $\sigma K_1 \perp \cdots \perp \sigma K_t$ is a second Jordan splitting of $L$, and the
conditions for two splittings of one lattice are `NecI.nec_disc` (i), `NecRepNext.nec_rep_next` (ii) and
`NecRepPrev.nec_rep_prev` (iii). -/
@[kb "omeara1963" "§93F, proof of 93:28, necessity, pp. 268–272"]
theorem necessity (hHil : PadicClass.LocalHilbertField F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [hLl : L.IsLattice F] [K.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (h : cls Q L = cls Q K) :
    Cond93 Q L Ls Ks a := by
  have hLK : L ∈ cls Q K := h ▸ mem_cls_self Q L
  obtain ⟨σ, hσ, hσK⟩ := hLK
  have hLfg : L.FG := hLl.fg
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  have hKle : ∀ k, Ks k ≤ K := fun k => hK.split.iSup_eq ▸ le_iSup Ks k
  have hLle : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  set Ks' : Fin t → Submodule R V := fun k => latMap σ (Ks k) with hKs'
  have hK' : IsJordanSplitting Q L Ks' := by
    rw [hσK]; exact SuffSub.isJordanSplitting_latMap Q hσ hKfg hK
  have h2 : (2 : R) ≠ 0 := two_ne_zero_R F
  have hC' : Cond93 Q L Ls Ks' a := fun i j hij =>
    ⟨NecI.nec_disc Q hHil h2p h2 hQ hL hK' i j hij.symm,
      fun hlt => NecRepNext.nec_rep_next Q hHil h2p h2 hQ hL hK' hS.2.1 i j hij.symm hlt,
      fun hlt => NecRepPrev.nec_rep_prev Q hHil h2p h2 hQ hL hK' hS.2.1 i j hij.symm hlt⟩
  have hchfg : ∀ {X : Submodule R V} {Xs : Fin t → Submodule R V}, X.FG → (∀ k, Xs k ≤ X) →
      ∀ i, (jordanChain Xs i).FG := fun hX hle i => FG.of_le hX (iSup₂_le fun j _ => hle j)
  have hK'le : ∀ k, Ks' k ≤ L := fun k => hK'.split.iSup_eq ▸ le_iSup Ks' k
  exact cond93_congr_right Q (hchfg hLfg hLle) (hchfg hLfg hK'le)
    (fun i => by
      rw [hKs', ← SuffSub.jordanChain_latMap]
      exact adj_isometricLat_symm Q Q (isometricLat_latMap Q hσ _)) hC'

/-- **93:28, sufficiency, granted the core** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 272–276): conditions
(i)–(iii) imply $\operatorname{cls} L = \operatorname{cls} K$. Steps 1–3 (the induction, the reductions and the passage
to $L^*_{(2)}$, $K^*_{(2)}$) are proved (`SuffMain.suff_all`); steps 4–8 are the named statement `SuffCore`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, pp. 272–276"]
theorem sufficiency (hHil : PadicClass.LocalHilbertField F) (hcore : SuffCore.{u, v} R F) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F]
    {t : ℕ} {Ls Ks : Fin t → Submodule R V} {a : Fin t → F} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q K Ks) (hS : SameFundamentalInvariants Q Q L K Ls Ks a) (hC : Cond93 Q L Ls Ks a) :
    cls Q L = cls Q K :=
  (cls_eq_of_mem Q (mem_cls_of_isometricLat Q (suff_all hHil hcore t Q h2p hQ L K Ls Ks a hL hK hS hC))).symm

end Main

section Classification

universe u v

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Theorem 93:28 from its computational core** (O'Meara 1963, §93F, pp. 267–276): over a dyadic field with
`LocalHilbertField`, the named statement `SuffCore` (steps 4–8 of the sufficiency) implies `DyadicClassification`.
The necessity is proved unconditionally (`necessity`), the rest of the sufficiency from `SuffCore` (`sufficiency`). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276"]
theorem dyadicClassification_of_core
    (hHil : ∀ [CharZero F], PadicClass.LocalHilbertField F)
    (hcore : ∀ [CharZero F], SuffCore.{u, v} R F) : DyadicClassification R Q := by
  refine ⟨fun h2p hQ L K _ _ t Ls Ks a hL hK hS => ?_⟩
  have : CharZero F := charZero_of_dyadic (R := R) h2p
  exact ⟨necessity Q hHil h2p hQ hL hK hS, sufficiency Q hHil hcore h2p hQ hL hK hS⟩

end Classification

section NumberField

open NumberField IsDedekindDomain

universe v

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type v} [AddCommGroup V] [Module (v.adicCompletion F) V] [FiniteDimensional (v.adicCompletion F) V]
  [Module (v.adicCompletionIntegers F) V] [IsScalarTower (v.adicCompletionIntegers F) (v.adicCompletion F) V]

/-- **Theorem 93:28 over the completion $F_\mathfrak p$ of a number field, from its computational core** (O'Meara
1963, §93F, pp. 267–276): `SuffCore` for $F_\mathfrak p$ implies `DyadicClassification` for every quadratic space
over $F_\mathfrak p$ (the dyadic hypothesis is part of the statement). -/
@[kb "omeara1963" "§93F, 93:28, pp. 267–276 (completion of a number field)"]
theorem dyadicClassification_nf (hcore : SuffCore.{0, v} (v.adicCompletionIntegers F) (v.adicCompletion F))
    (Q : QuadraticForm (v.adicCompletion F) V) :
    DyadicClassification (v.adicCompletionIntegers F) Q :=
  dyadicClassification_of_core Q (HasseIsoNF.localHilbertField_adicCompletion v) hcore

end NumberField

end QuadFormsKB.OMeara.Main28
