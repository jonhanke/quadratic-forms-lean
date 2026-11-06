/-
# O'Meara §65A–§65B: Examples 65:1 (ii), 65:4, the index of $I_\mathfrak p \cap N_{E/F}J_E$, Proposition 65:8

**Setting** as in `Sec65Ideles.lean`.

**Proves**
* **Example 65:1 (ii)** `exists_unit_localNormFin_eq`: at a discrete non-dyadic spot $\mathfrak p$ at which $\theta$ is a
  unit, $N_{\mathfrak P|\mathfrak p}\mathfrak U_\mathfrak P = \mathfrak u_\mathfrak p$ (the local units are local norms of
  local units);
* **Example 65:4** `mem_map_sIdeles_iff_of_unit`: if every spot of $S$ is non-dyadic and $\theta$ is a unit at all
  $\mathfrak p \in S$, then $N_{E/F}J_E^S$ is the set of $i \in J^S$ that are local norms at every $\mathfrak p \in
  \Omega - S$ with $n_\mathfrak p = 2$;
* `relIndex_ideleSupportedAt_inf_range` (65.r30, §65A, p. 176): $(I_\mathfrak p : I_\mathfrak p \cap N_{E/F}J_E) = 1$
  or $2$ according as $n_\mathfrak p = 1$ or $2$ (finite spots);
* **Proposition 65:8** `relIndex_map_sIdeles`: $(J^S : N_{E/F}J_E^S) = 2^b$, $b = \lvert B\rvert$.
-/
import QuadFormsKB.Literature.OMeara.Sec65Ideles
import QuadFormsKB.Tamagawa.SquareClassDuality

open NumberField IsDedekindDomain InfinitePlace WithZero

open scoped NumberField.LiesOver TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in
/-- Units of $F_\mathfrak p$ at a non-dyadic spot have Hilbert symbol $1$ with a global unit $a$. -/
lemma hilbertSymbol_unit_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (h2 : (2 : 𝓞 K) ∉ v.asIdeal) (a : K) (ha : v.valuation K a = 1) (x : v.adicCompletion K) (hx : ‖x‖ = 1) :
    hilbertSymbol (v.adicCompletion K) (algebraMap K _ a) x = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hvx : Valued.v x = 1 := (norm_eq_one_iff_valued v x).1 hx
  obtain ⟨b, hb0, d, hd0, hxbd⟩ := HN.exists_global_mul_sq v x hx0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by rintro rfl; rw [map_zero] at hπ; exact exp_ne_zero hπ.symm
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v d = exp k := ⟨log _, (exp_log ((Valuation.ne_zero_iff _).2 hd0)).symm⟩
  set b' : K := b * π ^ (-(2 * k))
  have hπv : Valued.v (algebraMap K (v.adicCompletion K) π) = exp (-1 : ℤ) := by
    rw [show algebraMap K (v.adicCompletion K) π = (π : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hx' : x = algebraMap K _ b' * (algebraMap K _ π ^ k * d) ^ 2 := by
    rw [hxbd]
    simp only [b', map_mul, map_zpow₀]
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul]
    have hπ' : algebraMap K (v.adicCompletion K) π ≠ 0 := (map_ne_zero _).2 hπ0
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl]
    field_simp
    rw [mul_assoc, ← zpow_add₀ hπ', show -(2 * k) + k * 2 = 0 by ring, zpow_zero, mul_one]
  clear_value b'
  have hb'v : v.valuation K b' = 1 := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have h1 : Valued.v x = Valued.v (algebraMap K (v.adicCompletion K) b') *
        (exp (-1 : ℤ) ^ k * exp k) ^ 2 := by
      rw [hx']
      simp only [Valuation.map_mul, Valuation.map_pow, map_zpow₀]
      rw [hπv, hk]
    rw [← exp_zsmul, smul_neg, smul_eq_mul, mul_one, ← exp_add, neg_add_cancel, exp_zero, one_pow,
      mul_one, hvx] at h1
    exact h1.symm
  have hb'0 : algebraMap K (v.adicCompletion K) π ^ k * d ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ ((map_ne_zero _).2 hπ0)) hd0
  rw [hx', SqDual.hilbertSymbol_mul_sq_right _ _ _ _ hb'0]
  exact SqDual.hilbert_units_nondyadic v h2 a b' ha hb'v

variable [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

/-- **Example 65:1 (ii)** (O'Meara 1963, p. 177): if $\mathfrak p$ is a discrete non-dyadic spot at which $\theta$ is
a unit, then $N_{\mathfrak P|\mathfrak p}\mathfrak U_\mathfrak P = \mathfrak u_\mathfrak p$: every unit of
$F_\mathfrak p$ is the local norm of a unit of $E_\mathfrak P$ (and local norms of units are units,
`norm_localNormFin_eq_one`). -/
@[kb "omeara1963" "§65A, 65:1 (ii), p. 177 (N_{𝔓|𝔭} 𝔘_𝔓 = 𝔲_𝔭)"]
theorem exists_unit_localNormFin_eq (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (hθv : v.valuation F θ = 1)
    (x : v.adicCompletion F) (hx : ‖x‖ = 1) : ∃ y : w.adicCompletion E, ‖y‖ = 1 ∧ localNormFin v w y = x := by
  by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
  · obtain ⟨y, hy⟩ := localNormFin_surjective_of_isSquare hθ hs v w hv x
    exact ⟨y, by rw [← norm_localNormFin v w, hy, hx], hy⟩
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hhil := hilbertSymbol_unit_eq_one v h2 θ hθv x hx
    obtain ⟨y, hy⟩ := (mem_range_localNormFin_iff hθ hs v w hv (Units.mk0 x hx0)).2 hhil
    have hy' : localNormFin v w (y : w.adicCompletion E) = x := congrArg Units.val hy
    exact ⟨y, by rw [← norm_localNormFin v w, hy', hx], hy'⟩

/-- **Example 65:4** (O'Meara 1963, p. 177): suppose every spot of $S$ is non-dyadic (65A (i)) and $\theta$ is a unit
at all $\mathfrak p \in S$. Then $N_{E/F}J_E^S$ is the set of idèles $i \in J^S$ that are local norms at all
$\mathfrak p \in \Omega - S$ with $n_\mathfrak p = 2$. -/
@[kb "omeara1963" "§65A, 65:4, p. 177"]
theorem mem_map_sIdeles_iff_of_unit (S : Set (HeightOneSpectrum (𝓞 F)))
    (h2S : ∀ v ∈ S, (2 : 𝓞 F) ∉ v.asIdeal) (hθS : ∀ v ∈ S, v.valuation F θ = 1) (i : IdeleGroup (𝓞 F) F) :
    i ∈ (sIdeles (spotsAbove (E := E) S)).map (ideleNorm (F := F) (E := E)) ↔
      i ∈ sIdeles S ∧
      (∀ v ∉ S, ∀ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 →
        IsLocalNormIdeleAt E i v) ∧
      (∀ v (w : InfSpotsOver E v), Module.finrank v.Completion w.1.Completion = 2 →
        IsLocalNormIdeleAtInf E i v) := by
  rw [mem_map_sIdeles_iff E hθ hs]
  refine ⟨fun ⟨hS, hfin, hinf⟩ => ⟨hS, fun v _ w h => hfin v w h, hinf⟩, fun ⟨hS, hfin, hinf⟩ =>
    ⟨hS, fun v w h => ?_, hinf⟩⟩
  by_cases hv : v ∈ S
  · intro w'
    have hx : ‖ideleAt i v‖ = 1 := (norm_eq_one_iff_valued v _).2 (hS v hv)
    obtain ⟨y, -, hy⟩ := exists_unit_localNormFin_eq E hθ hs v w'.1 (h2S v hv) (hθS v hv) _ hx
    exact ⟨y, hy⟩
  · exact hfin v hv w h

open scoped Classical in
/-- **The index of $I_\mathfrak p \cap N_{E/F}J_E$ in $I_\mathfrak p$** (O'Meara 1963, §65A, p. 176):
$(I_\mathfrak p : I_\mathfrak p \cap N_{E/F}J_E) = 1$ if $n_\mathfrak p = 1$ and $2$ if $n_\mathfrak p = 2$
($\mathfrak p$ a finite spot). -/
@[kb "omeara1963" "§65A, p. 176 ((I_𝔭 : I_𝔭 ∩ N_{E/F} J_E) = 1 if n_𝔭 = 1, 2 if n_𝔭 = 2)"]
theorem relIndex_ideleSupportedAt_inf_range (v : HeightOneSpectrum (𝓞 F)) :
    ((ideleNorm (F := F) (E := E)).range ⊓ ideleSupportedAt v).relIndex (ideleSupportedAt v) =
      if IsSquare (algebraMap F (v.adicCompletion F) θ) then 1 else 2 := by
  rw [Subgroup.inf_relIndex_right, ideleSupportedAt, ← Subgroup.index_comap, ← index_localNormGroup E hθ hs v]
  congr 1
  ext x
  rw [Subgroup.mem_comap, mem_range_ideleNorm_iff E hθ hs, mem_localNormGroup_iff]
  constructor
  · rintro ⟨hfin, -⟩
    by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
    · exact isLocalNormAt_of_isSquare E hθ hs v hv _
    · obtain ⟨w₀⟩ := nonempty_spotsOver hθ hs v
      have := hfin v w₀ ((finrank_eq_two_iff_not_isSquare hθ hs v w₀.1).2 hv)
      unfold IsLocalNormIdeleAt at this
      rwa [ideleAt_ofAdic_self] at this
  · intro hx
    refine ⟨fun v' w _ w' => ?_, fun v' w _ w' => ⟨1, ?_⟩⟩
    · by_cases hv' : v' = v
      · subst hv'
        have := hx w'
        rwa [ideleAt_ofAdic_self]
      · exact ⟨1, by rw [ideleAt_ofAdic_ne v v' hv', map_one]⟩
    · rw [map_one, ideleAtInf_ofAdic]

omit hθ hs in
open scoped Classical in
/-- $b = \lvert B\rvert$ counts the finite spots outside $S$ and the infinite spots at which $\theta$ is a
non-square. -/
lemma ncard_splitB_eq {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    (splitB θ S).ncard = (hS.toFinset.filter fun v => ¬ IsSquare (algebraMap F (v.adicCompletion F) θ)).card +
      (Finset.univ.filter fun w : InfinitePlace F => ¬ IsSquare (algebraMap F w.Completion θ)).card := by
  have : splitB θ S = ↑(((hS.toFinset.filter fun v => ¬ IsSquare (algebraMap F (v.adicCompletion F) θ)).map
      ⟨NFPlace.finite, fun _ _ h => NFPlace.finite.inj h⟩) ∪
      ((Finset.univ.filter fun w : InfinitePlace F => ¬ IsSquare (algebraMap F w.Completion θ)).map
        ⟨NFPlace.infinite, fun _ _ h => NFPlace.infinite.inj h⟩)) := by
    ext p
    cases p with
    | infinite w =>
      simp [splitB, outsideS, NFPlace.atPlace]
      exact ⟨fun h => ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩, fun ⟨x, hx, e⟩ => by cases e; exact (Finset.mem_filter.1 hx).2⟩
    | finite v =>
      simp [splitB, outsideS, NFPlace.atPlace]
      exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨x, hx, e⟩ => by cases e; exact hx⟩
  rw [this, Set.ncard_coe_finset, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [Finset.mem_map] at hp hq
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨b, _, h⟩ := hq
  cases h

/-- A local norm at every spot with $n_\mathfrak p = 2$ is a local norm at every spot. -/
lemma isLocalNormAt_iff_of_finrank (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    (∀ w : SpotsOver E v, Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 →
      IsLocalNormAt E v x) ↔ IsLocalNormAt E v x := by
  refine ⟨fun h => ?_, fun h _ _ => h⟩
  by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
  · exact isLocalNormAt_of_isSquare E hθ hs v hv x
  · obtain ⟨w₀⟩ := nonempty_spotsOver hθ hs v
    exact h w₀ ((finrank_eq_two_iff_not_isSquare hθ hs v w₀.1).2 hv)

lemma isLocalNormAtInf_iff_of_finrank (v : InfinitePlace F) (x : v.Completion) :
    (∀ w : InfSpotsOver E v, Module.finrank v.Completion w.1.Completion = 2 → IsLocalNormAtInf E v x) ↔
      IsLocalNormAtInf E v x := by
  refine ⟨fun h => ?_, fun h _ _ => h⟩
  by_cases hv : IsSquare (algebraMap F v.Completion θ)
  · exact isLocalNormAtInf_of_isSquare E hθ hs v hv x
  · obtain ⟨w₀⟩ := nonempty_infSpotsOver E v
    exact h w₀ ((finrank_eq_two_iff_not_isSquare_inf hθ hs v w₀.1).2 hv)

/-- **Proposition 65:8** (O'Meara 1963, p. 178): if $S$ satisfies the conventions of §65A and $\theta$ is a unit at
all spots of $S$, then $(J^S : N_{E/F}J_E^S) = 2^b$, $b = \lvert B\rvert$ the number of spots of $\Omega - S$ with
$n_\mathfrak p = 2$. (O'Meara's proof: $J^S \to \prod_{\mathfrak p \in \Omega - S}\dot F_\mathfrak p$ is onto with kernel
$K^S \subseteq N_{E/F}J_E^S$, and by 65:4 the image of $N_{E/F}J_E^S$ is $\prod_A \dot F_\mathfrak p \times \prod_B
N_{\mathfrak P|\mathfrak p}\dot E_\mathfrak P$.) -/
@[kb "omeara1963" "§65B, 65:8, p. 178 ((J^S : N_{E/F} J_E^S) = 2^b)"]
theorem relIndex_map_sIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    (hθS : ∀ v ∈ S, v.valuation F θ = 1) :
    ((sIdeles (spotsAbove (E := E) S)).map (ideleNorm (F := F) (E := E))).relIndex (sIdeles S) =
      2 ^ (splitB θ S).ncard := by
  classical
  set T := hS.cofinite.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
  let ψ : IdeleGroup (𝓞 F) F →* (∀ v : T, (v.1.adicCompletion F)ˣ) × (∀ w : InfinitePlace F, w.Completionˣ) :=
    MonoidHom.prod (MonoidHom.pi fun v => idAtHom v.1) (MonoidHom.pi fun w => idAtInfHom w)
  let NS : Subgroup ((∀ v : T, (v.1.adicCompletion F)ˣ) × (∀ w : InfinitePlace F, w.Completionˣ)) :=
    (Subgroup.pi Set.univ fun v : T => localNormGroup E v.1).prod
      (Subgroup.pi Set.univ fun w : InfinitePlace F => localNormGroupInf E w)
  have hker : NS.comap ψ ⊓ sIdeles S = (sIdeles (spotsAbove (E := E) S)).map (ideleNorm (F := F) (E := E)) := by
    ext i
    rw [mem_map_sIdeles_iff_of_unit E hθ hs S hS.nondyadic hθS]
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, NS, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
      true_implies]
    constructor
    · rintro ⟨⟨h1, h2⟩, hi⟩
      refine ⟨hi, fun v hv => (isLocalNormAt_iff_of_finrank E hθ hs v _).2 ?_,
        fun w => (isLocalNormAtInf_iff_of_finrank E hθ hs w _).2 ?_⟩
      · exact (mem_localNormGroup_iff E v (idAtHom v i)).1 (h1 ⟨v, (hmemT v).2 hv⟩)
      · exact (mem_localNormGroupInf_iff E w (idAtInfHom w i)).1 (h2 w)
    · rintro ⟨hi, h1, h2⟩
      refine ⟨⟨fun v => (mem_localNormGroup_iff E v.1 (idAtHom v.1 i)).2
          ((isLocalNormAt_iff_of_finrank E hθ hs v.1 _).1 (h1 v.1 ((hmemT v.1).1 v.2))),
        fun w => (mem_localNormGroupInf_iff E w (idAtInfHom w i)).2
          ((isLocalNormAtInf_iff_of_finrank E hθ hs w _).1 (h2 w))⟩, hi⟩
  have hsurj : ∀ g, ∃ i ∈ sIdeles S, ψ i = g := by
    rintro ⟨a, b⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := exists_idele hS.cofinite (fun v => if h : v ∈ T then a ⟨v, h⟩ else 1) b
    have hjS : j ∈ sIdeles S := fun v hv => by rw [hj2 v hv]; simp
    refine ⟨j, hjS, Prod.ext (funext fun v => ?_) (funext fun w => ?_)⟩
    · exact Units.ext ((hj1 v.1 ((hmemT v.1).mp v.2)).trans (by simp [v.2]))
    · exact Units.ext (hj3 w)
  have hmap : (sIdeles S).map ψ = ⊤ :=
    eq_top_iff.mpr fun g _ => let ⟨i, hi, e⟩ := hsurj g; ⟨i, hi, e⟩
  rw [← hker, Subgroup.inf_relIndex_right, Subgroup.relIndex_comap, hmap, Subgroup.relIndex_top_right,
    Subgroup.index_prod, index_pi_dep, index_pi_dep]
  simp only [index_localNormGroup E hθ hs, index_localNormGroupInf E hθ hs]
  rw [Finset.prod_coe_sort T (fun v => if IsSquare (algebraMap F (v.adicCompletion F) θ) then 1 else 2),
    Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const_one, one_mul, one_mul,
    Finset.prod_const, Finset.prod_const, ← pow_add, ncard_splitB_eq hS.cofinite]

end QuadFormsKB.OMeara
