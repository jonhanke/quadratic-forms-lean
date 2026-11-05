/-
# O'Meara §65B, §65D: Proposition 65:10 and the idèle-class indices 65:13, 65:14, 65:21, 65:22

**Setting** as in `Sec65Ideles.lean`: $F$ a number field, $\theta$ a non-square, $E = F(\sqrt\theta)$, and a set $S$
of finite spots satisfying the conventions of §65A (`SConventions S`). The finite complement $\Omega_{fin} - S$ is
`hS.cofinite.toFinset`; O'Meara's $S$-units $\mathfrak u$ are the library's `HN.SUnit` of that finite set, and the
$S$-units $\mathfrak U$ of $E$ are `HN.SUnit` of the spots of $E$ over it (`HN.overS`).

**Defines** `normSUnits`: $N_{E/F}\mathfrak U \subseteq \dot F$.

**Proves**
* `normSUnits_le` (65.r13): $N_{E/F}\mathfrak U \subseteq \mathfrak u$;
* **Proposition 65:10** `relIndex_normSUnits` ($b \ge 1$ and $(\mathfrak u : N_{E/F}\mathfrak U) = 2^{b-1}$) and
  `relIndex_map_principalSIdeles` ($(P^S : N_{E/F}P_E^S) = (\mathfrak u : N_{E/F}\mathfrak U)$).
-/
import QuadFormsKB.Literature.OMeara.Sec65Units
import QuadFormsKB.Literature.OMeara.Sec65B
import QuadFormsKB.Literature.HasseNorm.Places
import QuadFormsKB.Literature.HasseNorm.GoodPrimes

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/-- **The norms of the $S$-units of $E$** $N_{E/F}\mathfrak U \subseteq \dot F$, for the finite set $T = \Omega_{fin} -
S$ of spots of $F$ ($\mathfrak U$ = the units of $E$ outside the spots over $T$). -/
@[kb "omeara1963" "§65A, p. 175 (N_{E/F} 𝔘, the norms of the S-units of E)"]
def normSUnits (T : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (HN.SUnit (F := E) (HN.overS (L := E) T)).map (Units.map (Algebra.norm F : E →* F))

/-- **$N_{E/F}\mathfrak U \subseteq \mathfrak u$** (O'Meara 1963, §65A, p. 175): $\lvert N_{E/F}\alpha\rvert_\mathfrak p =
\prod_{\mathfrak P|\mathfrak p} \lvert\alpha\rvert_\mathfrak P = 1$ for $\mathfrak p \in S$. -/
@[kb "omeara1963" "§65A, p. 175 (N_{E/F} 𝔘 ⊆ 𝔲)"]
theorem normSUnits_le (T : Finset (HeightOneSpectrum (𝓞 F))) :
    normSUnits E T ≤ HN.SUnit (F := F) T := by
  rintro _ ⟨X, hX, rfl⟩
  rw [HN.mem_sUnit_iff]
  intro v hv
  -- `|N X|_v = ∏_{w | v} |X|_w = 1`
  have hprod := prod_localNormFin_eq_norm E v ((X : Eˣ) : E)
  have hnorm : ‖algebraMap F (v.adicCompletion F) (Algebra.norm F ((X : Eˣ) : E))‖ = 1 := by
    rw [← hprod, norm_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [norm_localNormFin]
    have hw : w.1 ∉ HN.overS (L := E) T := by
      rw [HN.mem_overS]
      have : HN.under (F := F) w.1 = v := (eq_spotBelow_of_liesOver v w.1).symm
      rw [this]; exact hv
    have := (HN.mem_sUnit_iff _ _).1 hX w.1 hw
    rw [norm_eq_one_iff_valued, show algebraMap E (w.1.adicCompletion E) ((X : Eˣ) : E) =
      (((X : Eˣ) : E) : w.1.adicCompletion E) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← HeightOneSpectrum.valuationOfNeZero_eq, this]
    rfl
  rw [norm_eq_one_iff_valued, show algebraMap F (v.adicCompletion F) (Algebra.norm F ((X : Eˣ) : E)) =
      ((Algebra.norm F ((X : Eˣ) : E) : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hnorm
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq]
  exact hnorm

/-- In a quadratic extension with nontrivial automorphism $\sigma$, $N_{E/F}(x) = x\,\sigma(x)$. -/
lemma algebraMap_norm_eq_mul (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) (x : E) :
    algebraMap F E (Algebra.norm F x) = x * σ x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair (Ne.symm hσ)]
  rw [huniv, Finset.prod_pair (Ne.symm hσ)]
  rfl

/-- The library's additive norm group `HN.normsF` is $N_{E/F}\mathfrak U$. -/
lemma normsF_eq (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    HN.normsF σ T = Subgroup.toAddSubgroup ((normSUnits E T).subgroupOf (HN.SUnit (F := F) T)) := by
  ext x
  rw [show (x ∈ Subgroup.toAddSubgroup ((normSUnits E T).subgroupOf (HN.SUnit (F := F) T))) ↔
    Additive.toMul x ∈ (normSUnits E T).subgroupOf (HN.SUnit (F := F) T) from Iff.rfl, Subgroup.mem_subgroupOf]
  simp only [HN.normsF, AddSubgroup.mem_comap, AddMonoidHom.mem_range, normSUnits, Subgroup.mem_map]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨(Additive.toMul X : HN.SUnit _), (Additive.toMul X).2, ?_⟩
    apply Units.ext
    apply (algebraMap F E).injective
    have := congrArg (fun z => (((Additive.toMul z : HN.SUnit _) : Eˣ) : E)) hX
    simp only [HN.normHom_apply, toMul_add, Subgroup.coe_mul, Units.val_mul, HN.σS_apply] at this
    rw [Units.coe_map]
    erw [algebraMap_norm_eq_mul E σ hσ, this]
    rfl
  · rintro ⟨X, hX, hXu⟩
    refine ⟨Additive.ofMul ⟨X, hX⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    simp only [HN.normHom_apply, toMul_add, Subgroup.coe_mul, Units.val_mul, HN.σS_apply, toMul_ofMul]
    rw [← algebraMap_norm_eq_mul E σ hσ]
    have := congrArg (fun z : Fˣ => algebraMap F E (z : F)) hXu
    simp only [Units.coe_map] at this
    rw [this]
    rfl

variable {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

/-- A finite spot splits in $E$ (two spots above it) iff $\theta$ is a square there. -/
lemma splitsFin_iff (σ : E ≃ₐ[F] E) (hσs : σ s = -s) (v : HeightOneSpectrum (𝓞 F)) :
    HN.SplitsFin (L := E) v ↔ IsSquare (algebraMap F (v.adicCompletion F) θ) := by
  constructor
  · rintro ⟨w, w', hne, hw, hw'⟩
    by_contra hsq
    have i1 : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
    have i2 : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
    have hc := card_spotsOver_mul_finrank hθ hs v ⟨w, i1⟩
    rw [(finrank_eq_two_iff_not_isSquare hθ hs v w).2 hsq] at hc
    have hc1 : Fintype.card (SpotsOver E v) = 1 := by omega
    have : (⟨w, i1⟩ : SpotsOver E v) = ⟨w', i2⟩ :=
      (Fintype.card_le_one_iff_subsingleton.1 hc1.le).elim _ _
    exact hne (congrArg Subtype.val this)
  · intro hsq
    exact HN.two_primes_of_isSquare σ s θ hs hσs hθ v hsq

/-- An infinite spot splits in $E$ iff $\theta$ is a square there. -/
lemma splitsInf_iff (v : InfinitePlace F) :
    HN.SplitsInf (L := E) v ↔ IsSquare (algebraMap F v.Completion θ) := by
  have hsum := sum_finrank_infSpotsOver E v
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hsum
  constructor
  · rintro ⟨w, w', hne, hw, hw'⟩
    by_contra hsq
    have i1 : w.LiesOver v := liesOver_of_comap_eq w v hw
    have i2 : w'.LiesOver v := liesOver_of_comap_eq w' v hw'
    have h2 : ∀ u : InfSpotsOver E v, Module.finrank v.Completion u.1.Completion = 2 := fun u =>
      (finrank_eq_two_iff_not_isSquare_inf hθ hs v u.1).2 hsq
    rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
    have hc1 : Fintype.card (InfSpotsOver E v) = 1 := by omega
    have : (⟨w, i1⟩ : InfSpotsOver E v) = ⟨w', i2⟩ :=
      (Fintype.card_le_one_iff_subsingleton.1 hc1.le).elim _ _
    exact hne (congrArg Subtype.val this)
  · intro hsq
    have h1 : ∀ u : InfSpotsOver E v, Module.finrank v.Completion u.1.Completion = 1 := fun u =>
      (finrank_eq_one_iff_isSquare_inf hθ hs v u.1).2 hsq
    rw [Finset.sum_congr rfl (fun u _ => h1 u), Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_one] at hsum
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card (InfSpotsOver E v))
    exact ⟨a.1, b.1, fun h => hab (Subtype.ext h), comap_eq_of_liesOver E v a.1, comap_eq_of_liesOver E v b.1⟩

/-- **Proposition 65:10 (ii)** (O'Meara 1963, p. 179): if $S$ satisfies the conventions of §65A and $\theta$ is a
unit at all spots of $S$, then $b \ge 1$ and $(\mathfrak u : N_{E/F}\mathfrak U) = 2^{b-1}$. (Proved from the library's
Herbrand-quotient computation `HN.index_normsF_eq`; O'Meara's 65:10 (i) is `relIndex_map_principalSIdeles`.) -/
@[kb "omeara1963" "§65B, 65:10, p. 179 (b ≥ 1 and (𝔲 : N_{E/F} 𝔘) = 2^{b-1})"]
theorem relIndex_normSUnits {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    (hθS : ∀ v ∈ S, v.valuation F θ = 1) :
    1 ≤ (splitB θ S).ncard ∧
      (normSUnits E hS.cofinite.toFinset).relIndex (HN.SUnit (F := F) hS.cofinite.toFinset) =
        2 ^ ((splitB θ S).ncard - 1) := by
  classical
  obtain ⟨_, σ, hσ, hσs⟩ := HN.quadData θ hθ s hs (exists_eq_add_mul_sqrt hθ hs)
  set T := hS.cofinite.toFinset with hT
  have hU := exists_uniformizer hS
  have hram : ∀ w : HeightOneSpectrum (𝓞 E), HN.under (F := F) w ∉ T →
      w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    intro w hw
    have hwS : HN.under (F := F) w ∈ S := by simpa [hT] using hw
    have h2 : (HN.under (F := F) w).valuation F 2 = 1 := by
      have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (HN.under (F := F) w) (r := 2)).2
        (hS.nondyadic _ hwS)
      rwa [map_ofNat] at this
    exact HN.ramificationIdx_eq_one σ s θ hs hσs w h2 (hθS _ hwS)
  have h := HN.index_normsF_eq σ hσ T hU hram
  rw [normsF_eq E σ hσ T, Subgroup.index_toAddSubgroup] at h
  have hb : (Finset.univ.filter fun v : InfinitePlace F => ¬ HN.SplitsInf (L := E) v).card +
      (T.filter fun p => ¬ HN.SplitsFin (L := E) p).card = (splitB θ S).ncard := by
    rw [ncard_splitB_eq hS.cofinite, add_comm]
    congr 2
    · exact Finset.filter_congr fun p _ => not_congr (splitsFin_iff E hθ hs σ hσs p)
    · exact Finset.filter_congr fun v _ => not_congr (splitsInf_iff E hθ hs v)
  rw [hb] at h
  have hrel : (normSUnits E T).relIndex (HN.SUnit (F := F) T) =
      ((normSUnits E T).subgroupOf (HN.SUnit (F := F) T)).index := rfl
  rw [← hrel] at h
  rcases Nat.eq_zero_or_pos (splitB θ S).ncard with h0 | hpos
  · rw [h0, pow_zero] at h; omega
  · refine ⟨hpos, ?_⟩
    have : 2 ^ (splitB θ S).ncard = 2 ^ ((splitB θ S).ncard - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h

omit hθ hs in
/-- The finite spots of $E$ outside `spotsAbove S` are those over $\Omega_{fin} - S$ (`HN.overS`). -/
lemma spotsAbove_compl_finite {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    (spotsAbove (E := E) S)ᶜ.Finite :=
  finite_preimage_spotBelow E hS

omit hθ hs in
lemma toFinset_spotsAbove_compl {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    (spotsAbove_compl_finite E hS).toFinset = HN.overS (L := E) hS.toFinset := by
  ext w
  rw [Set.Finite.mem_toFinset, HN.mem_overS, Set.Finite.mem_toFinset]
  rfl

omit hθ hs in
/-- **Proposition 65:10 (i)** (O'Meara 1963, p. 179): $(P^S : N_{E/F}P_E^S) = (\mathfrak u : N_{E/F}\mathfrak U)$,
from the commutative diagram of §65A ($\mathfrak u \cong P^S$, $\mathfrak U \cong P_E^S$, and 64.r11). -/
@[kb "omeara1963" "§65B, 65:10 (i), p. 179 ((P^S : N_{E/F} P_E^S) = (𝔲 : N_{E/F} 𝔘))"]
theorem relIndex_map_principalSIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    ((principalSIdeles (spotsAbove (E := E) S)).map (ideleNorm (F := F) (E := E))).relIndex
        (principalSIdeles S) =
      (normSUnits E hS.toFinset).relIndex (HN.SUnit (F := F) hS.toFinset) := by
  rw [← range_unitEmbedding_sUnit hS, ← range_unitEmbedding_sUnit (spotsAbove_compl_finite E hS),
    toFinset_spotsAbove_compl E hS, MonoidHom.map_range]
  have hcomp : (ideleNorm (F := F) (E := E)).comp ((IdeleGroup.unitEmbedding (𝓞 E) E).comp
      (HN.SUnit (F := E) (HN.overS (L := E) hS.toFinset)).subtype) =
      (IdeleGroup.unitEmbedding (𝓞 F) F).comp ((Units.map (Algebra.norm F : E →* F)).comp
        (HN.SUnit (F := E) (HN.overS (L := E) hS.toFinset)).subtype) := by
    ext X
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [ideleNorm_unitEmbedding]
  rw [hcomp, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
    Subgroup.range_subtype]
  exact Subgroup.relIndex_map_map_of_injective _ _ unitEmbedding_injective

end QuadFormsKB.OMeara
