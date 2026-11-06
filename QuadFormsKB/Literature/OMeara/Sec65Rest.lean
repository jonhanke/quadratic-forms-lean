/-
# O'Meara §65A–§65B: running-text items (existence of $S$, $J^S$ as a product, unramified spots, conjugation)

**Setting.** $F$ is a number field, $J_F = $ `IdeleGroup (𝓞 F) F`, $S$ a set of finite spots (see `Sec64.lean`,
`Sec65A.lean`). For an extension $E/F$ of number fields the spots over $S$ are `spotsAbove S` and the local
objects are those of `Sec64Local.lean`. In the quadratic part, $\theta \in F$ is a non-square, $E = F(\sqrt\theta)$
(`[Algebra.IsQuadraticExtension F E]`, $s \in E$ with $s^2 = \theta$) and $\sigma$ is the conjugation, taken as an
$F$-algebra automorphism of $E$ with $\sigma s = -s$.

**Proves**
* 65.r2 (§65A, p. 174): there is a set $S$ with O'Meara's conventions (i)–(iv) (`exists_sConventions`), and, for
  $E/F$ finite and finitely many nonzero $\theta_i \in F$, one with moreover $\lvert\theta_i\rvert_\mathfrak p = 1$ on
  $S$ and $J_E = P_EJ_E^S$ (`exists_sConventions_strong`);
* 65.r4 (§65A, p. 174): $J^S = K^S\cdot\prod_{\mathfrak p \in \Omega - S}I_\mathfrak p$ (`sIdeles_eq_kIdeles_sup`);
* 65.r17/r18 (§65A, p. 175): ramification indices and inertia degrees of two spots over the same $\mathfrak p$ agree
  (`ramificationIdx_eq_of_liesOver`, `inertiaDeg_eq_of_liesOver`), and $e_\mathfrak p f_\mathfrak p = n_\mathfrak p$
  with the possible values (`ramification_inertia_cases`);
* 65.r20/r21 (§65A, p. 176): `IsUnramifiedAt`, `IsUnramifiedLocal` and their equivalence
  (`isUnramifiedAt_iff`); $E/F$ is unramified at $\mathfrak p$ when $n_\mathfrak p = 1$
  (`isUnramifiedAt_of_isSquare`);
* 65.r22 (§65A, p. 176): $\lvert\sigma\Gamma\rvert_\mathfrak P = \lvert\Gamma\rvert_\mathfrak P$ if there is one spot
  over $\mathfrak p$ (`valuation_conj_eq_of_not_isSquare`), $\lvert\Gamma\rvert_{\mathfrak P_1} =
  \lvert\sigma\Gamma\rvert_{\mathfrak P_2}$ if there are two (`valuation_conj_eq_of_isSquare`);
* 65.r31 (§65B, footnote p. 181): 65:11 from 65:18a (`isSquare_of_unit_of_isSquare_outside'`).
-/
import QuadFormsKB.Literature.OMeara.Sec65Units
import QuadFormsKB.Literature.OMeara.Sec65D
import QuadFormsKB.Literature.OMeara.Sec33D
import QuadFormsKB.Literature.HasseNorm.Places

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

/-! ### 65.r2: existence of $S$ -/

section R2

variable {F : Type} [Field F] [NumberField F]

/-- There are only finitely many dyadic spots. -/
lemma finite_dyadic : {v : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ v.asIdeal}.Finite := by
  refine (Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)).subset ?_
  intro p hp
  rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp

/-- A nonzero element of $F$ is a unit at all but finitely many finite spots. -/
lemma finite_valuation_ne_one {θ : F} (hθ : θ ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F θ ≠ 1}.Finite := by
  have h := hasFiniteMulSupport_norm_ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F (Units.mk0 θ hθ))
  refine h.subset ?_
  intro v hv
  simp only [Function.mem_mulSupport]
  change ‖(algebraMap F (v.adicCompletion F) θ)‖ ≠ 1
  rw [Ne, norm_eq_one_iff_valued, QuadFormsKB.HN.valued_algebraMap]
  exact hv

/-- From $(J : P J^S) = 1$: every idèle is a product of a principal idèle and an $S$-idèle. -/
lemma exists_decomp_of_index_eq_one {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (h : (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ sIdeles S).index = 1) (i : IdeleGroup (𝓞 K) K) :
    ∃ p ∈ IdeleGroup.principalSubgroup (𝓞 K) K, ∃ j ∈ sIdeles S, i = p * j := by
  have hi : i ∈ IdeleGroup.principalSubgroup (𝓞 K) K ⊔ sIdeles S := by
    rw [Subgroup.index_eq_one.1 h]; exact Subgroup.mem_top _
  obtain ⟨p, hp, j, hj, rfl⟩ := Subgroup.mem_sup.1 hi
  exact ⟨p, hp, j, hj, rfl⟩

/-- **65.r2, strong form** (O'Meara 1963, §65A, p. 174, "take a small enough set $S$"). Let $E/F$ be an extension of
number fields and $\Theta \subseteq F^\times$ a finite set. Then there is a set $S$ of finite spots of $F$ with
O'Meara's conventions (i)–(iv) (`SConventions S`: non-dyadic, $\Omega - S$ finite, $J_F = P_FJ_F^S$) such that
moreover $\lvert\theta\rvert_\mathfrak p = 1$ for all $\theta \in \Theta$ and $\mathfrak p \in S$, and
$J_E = P_EJ_E^S$ where $S$ also denotes the spots of $E$ over $S$ (`spotsAbove S`). Proof: take the finite set $T_F$
of 33:14a for $F$ and $T_E$ for $E$, and let $S$ be the complement of $T_F$, the spots below $T_E$, the dyadic
spots and the spots where some $\theta$ is not a unit. -/
@[kb "omeara1963" "§65A, p. 174 (a small enough S satisfies (i)–(iv), is a unit set for θ, and J_E = P_E J_E^S)"]
theorem exists_sConventions_strong (E : Type) [Field E] [NumberField E] [Algebra F E] (Θ : Finset F)
    (hΘ : ∀ θ ∈ Θ, θ ≠ 0) :
    ∃ S : Set (HeightOneSpectrum (𝓞 F)), SConventions S ∧ (∀ θ ∈ Θ, ∀ v ∈ S, v.valuation F θ = 1) ∧
      ∀ i : IdeleGroup (𝓞 E) E, ∃ p ∈ IdeleGroup.principalSubgroup (𝓞 E) E, ∃ j ∈ sIdeles (spotsAbove S),
        i = p * j := by
  obtain ⟨TF, hTF⟩ := exists_index_sup_sIdeles_eq_one (F := F)
  obtain ⟨TE, hTE⟩ := exists_index_sup_sIdeles_eq_one (F := E)
  let B : Set (HeightOneSpectrum (𝓞 F)) :=
    (↑TF ∪ {v | (2 : 𝓞 F) ∈ v.asIdeal}) ∪ (⋃ θ ∈ Θ, {v | v.valuation F θ ≠ 1}) ∪ spotBelow (E := E) '' ↑TE
  have hB : B.Finite :=
    (((TF.finite_toSet).union finite_dyadic).union
      (Set.Finite.biUnion Θ.finite_toSet fun θ hθ => finite_valuation_ne_one (hΘ θ hθ))).union
      (TE.finite_toSet.image _)
  refine ⟨Bᶜ, ⟨fun v hv h2 => hv (Or.inl (Or.inl (Or.inr h2))), by simpa using hB, ?_⟩, ?_, ?_⟩
  · refine exists_decomp_of_index_eq_one (hTF _ ?_)
    refine Set.disjoint_left.2 fun v hv hvT => hv (Or.inl (Or.inl (Or.inl hvT)))
  · intro θ hθ v hv
    by_contra h
    exact hv (Or.inl (Or.inr (Set.mem_biUnion hθ h)))
  · refine exists_decomp_of_index_eq_one (hTE _ ?_)
    refine Set.disjoint_left.2 fun w hw hwT => hw (Or.inr ⟨w, hwT, rfl⟩)

/-- **65.r2** (O'Meara 1963, §65A, p. 174): every number field has a set $S$ of finite spots with the conventions
(i)–(iv) of §65A (Corollary 33:14a). -/
@[kb "omeara1963" "§65A, p. 174 (a set S with conventions (i)–(iv) exists, by 33:14a)"]
theorem exists_sConventions : ∃ S : Set (HeightOneSpectrum (𝓞 F)), SConventions S := by
  obtain ⟨S, hS, -, -⟩ := exists_sConventions_strong (F := F) F ∅ (by simp)
  exact ⟨S, hS⟩

end R2

/-! ### 65.r4: $J^S = K^S\prod I_\mathfrak p$ -/

section R4

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
lemma ideleAt_prod_ofAdic (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (s : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (∏ u ∈ s, IdeleGroup.ofAdicCompletion (𝓞 F) F u (x u)) v =
      if v ∈ s then (x v : v.adicCompletion F) else 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ideleAt_mul, ih]
    by_cases hv : v = a
    · subst hv; simp [ha, ideleAt_ofAdic_self]
    · simp [hv, ideleAt_ofAdic_ne a v hv]

open scoped Classical in
lemma ideleAt_prod_ofCompletion (y : ∀ w : InfinitePlace F, w.Completionˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (∏ w : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w (y w)) v = 1 := by
  induction (Finset.univ : Finset (InfinitePlace F)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ideleAt_mul, ih, ideleAt_ofCompletion]; simp

lemma ideleAtInf_prod_ofAdic (x : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (s : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    ideleAtInf (∏ u ∈ s, IdeleGroup.ofAdicCompletion (𝓞 F) F u (x u)) w = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ideleAtInf_mul, ih, ideleAtInf_ofAdic]; simp

open scoped Classical in
lemma ideleAtInf_prod_ofCompletion (y : ∀ w : InfinitePlace F, w.Completionˣ) (w : InfinitePlace F) :
    ideleAtInf (∏ w' : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w' (y w')) w = y w := by
  have : ∀ (s : Finset (InfinitePlace F)),
      ideleAtInf (∏ w' ∈ s, IdeleGroup.ofCompletion (𝓞 F) F w' (y w')) w =
        if w ∈ s then (y w : w.Completion) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ideleAtInf_mul, ih]
      by_cases hv : w = a
      · subst hv; simp [ha, ideleAtInf_ofCompletion_self]
      · simp [hv, ideleAtInf_ofCompletion_ne a w hv]
  rw [this]; simp

/-- **65.r4** (O'Meara 1963, §65A, p. 174): if $\Omega - S$ is finite, then
$J_F^S = K_F^S\cdot\prod_{\mathfrak p \in \Omega - S}I_\mathfrak p$. Here the product is over the finite spots
$\mathfrak p \notin S$ (`ideleSupportedAt`) and the infinite spots $w$, where O'Meara's $I_w$ is the image of
$\dot F_w$ (`IdeleGroup.ofCompletion`), and the product of subgroups of the commutative group $J_F$ is the supremum
(for finitely many factors it is the set of products). -/
@[kb "omeara1963" "§65A, p. 174 (J_F^S = K_F^S · ∏_{𝔭 ∈ Ω−S} I_𝔭 when Ω − S is finite)"]
theorem sIdeles_eq_kIdeles_sup {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    sIdeles S = kIdeles S ⊔ (⨆ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S), ideleSupportedAt v) ⊔
      ⨆ w : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F w).range := by
  classical
  apply le_antisymm
  · intro i hi
    set T := hS.toFinset with hT
    have hmem : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
    set j : IdeleGroup (𝓞 F) F := (∏ u ∈ T, IdeleGroup.ofAdicCompletion (𝓞 F) F u (idAtHom u i)) *
      ∏ w : InfinitePlace F, IdeleGroup.ofCompletion (𝓞 F) F w (idAtInfHom w i) with hj
    have hjA : ∀ v, ideleAt j v = if v ∈ T then ideleAt i v else 1 := by
      intro v
      rw [hj, ideleAt_mul, ideleAt_prod_ofAdic, ideleAt_prod_ofCompletion]
      split_ifs <;> simp
    have hjInf : ∀ w, ideleAtInf j w = ideleAtInf i w := by
      intro w
      rw [hj, ideleAtInf_mul, ideleAtInf_prod_ofAdic, ideleAtInf_prod_ofCompletion]
      simp
    have hjmem : j ∈ (⨆ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S), ideleSupportedAt v) ⊔
        ⨆ w : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F w).range := by
      refine Subgroup.mul_mem_sup (Subgroup.prod_mem _ fun u hu => ?_) (Subgroup.prod_mem _ fun w _ => ?_)
      · exact Subgroup.mem_iSup_of_mem u (Subgroup.mem_iSup_of_mem ((hmem u).1 hu) ⟨_, rfl⟩)
      · exact Subgroup.mem_iSup_of_mem w ⟨_, rfl⟩
    have hk : i * j⁻¹ ∈ kIdeles S := by
      refine ⟨fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
      · have : v ∉ T := fun h => (hmem v).1 h hv
        rw [ideleAt_mul, ideleAt_inv, hjA v]
        simp only [this, ↓reduceIte, inv_one, mul_one]
        exact hi v hv
      · have : v ∈ T := (hmem v).2 hv
        rw [ideleAt_mul, ideleAt_inv, hjA v]
        simp only [this, ↓reduceIte]
        exact mul_inv_cancel₀ (idAtHom v i).ne_zero
      · rw [ideleAtInf_mul, ideleAtInf_inv, hjInf w]
        exact mul_inv_cancel₀ (idAtInfHom w i).ne_zero
    rw [sup_assoc]
    exact Subgroup.mem_sup.2 ⟨i * j⁻¹, hk, j, hjmem, inv_mul_cancel_right i j⟩
  · refine sup_le (sup_le (kIdeles_le_sIdeles S) (iSup₂_le fun v hv => ?_)) (iSup_le fun w => ?_)
    · exact (ideleSupportedAt_le_sIdeles_iff S v).2 hv
    · rintro _ ⟨y, rfl⟩ v hv
      rw [ideleAt_ofCompletion]; simp

end R4

/-! ### 65.r17–r22: the quadratic extension $E = F(\sqrt\theta)$ at a finite spot -/

section Quadratic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

section Spots

variable (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
  [w'.asIdeal.LiesOver v.asIdeal]

/-- If $\theta$ is a non-square at $\mathfrak p$, there is only one spot of $E$ over $\mathfrak p$ (O'Meara 1963,
§65A, p. 175: $n_\mathfrak p = 2$, $\sum_{\mathfrak P|\mathfrak p} n_\mathfrak p = 2$). -/
lemma eq_of_not_isSquare (hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) θ)) : w = w' := by
  have h := card_spotsOver_mul_finrank hθ hs v ⟨w, inferInstance⟩
  rw [(finrank_eq_two_iff_not_isSquare hθ hs v w).2 hv] at h
  have hc : Fintype.card (SpotsOver E v) = 1 := by omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hc
  have h1 : (⟨w, inferInstance⟩ : SpotsOver E v) = a := ha _
  have h2 : (⟨w', inferInstance⟩ : SpotsOver E v) = a := ha _
  exact congrArg Subtype.val (h1.trans h2.symm)

/-- $e f = 1$ when $\theta$ is a square at $\mathfrak p$, and $e = f = 1$ then. -/
lemma ef_eq_one_of_isSquare (hv : IsSquare (algebraMap F (v.adicCompletion F) θ)) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  have h := finrank_adicCompletion_eq_ef v w
  rw [(finrank_eq_one_iff_isSquare hθ hs v w).2 hv] at h
  exact mul_eq_one.1 h.symm

include v in
/-- **65.r17** (O'Meara 1963, §65A, p. 175): for $E = F(\sqrt\theta)$ and two finite spots
$\mathfrak P, \mathfrak P'$ of $E$ over the same spot $\mathfrak p$ of $F$, the ramification indices and the inertia
degrees agree: $e(\mathfrak P|\mathfrak p) = e(\mathfrak P'|\mathfrak p)$ and $f(\mathfrak P|\mathfrak p) =
f(\mathfrak P'|\mathfrak p)$ (O'Meara's $e_\mathfrak p$, $f_\mathfrak p$). If $\theta$ is a square at $\mathfrak p$
both are $1$; otherwise $\mathfrak P = \mathfrak P'$. -/
@[kb "omeara1963" "§65A, p. 175 (e(𝔓|𝔭) and f(𝔓|𝔭) depend only on 𝔭, quadratic case)"]
theorem ramificationIdx_inertiaDeg_eq_of_liesOver :
    w.asIdeal.ramificationIdx (𝓞 F) = w'.asIdeal.ramificationIdx (𝓞 F) ∧
      w.asIdeal.inertiaDeg (𝓞 F) = w'.asIdeal.inertiaDeg (𝓞 F) := by
  by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
  · obtain ⟨h1, h2⟩ := ef_eq_one_of_isSquare hθ hs v w hv
    obtain ⟨h3, h4⟩ := ef_eq_one_of_isSquare hθ hs v w' hv
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · obtain rfl := eq_of_not_isSquare hθ hs v w w' hv
    exact ⟨rfl, rfl⟩

/-- **65.r17, local form** (O'Meara 1963, §65A, p. 175: "$e_\mathfrak p$ is also the ramification index of
$E_\mathfrak P/F_\mathfrak p$; similarly for $f_\mathfrak p$"): the exponent by which the normalized valuation of
$F_\mathfrak p$ extends to $E_\mathfrak P$ (`valued_localMap`), which is the ramification index of the local
extension, is $e_\mathfrak p$ for every $\mathfrak P \mid \mathfrak p$, and $[E_\mathfrak P : F_\mathfrak p] =
e_\mathfrak pf_\mathfrak p$ (so $f_\mathfrak p$ is the residue degree of the local extension). -/
@[kb "omeara1963" "§65A, p. 175 (e_𝔭 and f_𝔭 are also those of E_𝔓/F_𝔭)"]
theorem ramification_inertia_local :
    (∀ x : v.adicCompletion F, Valued.v (localMap v w x) = Valued.v x ^ w'.asIdeal.ramificationIdx (𝓞 F)) ∧
      (∀ x : v.adicCompletion F, Valued.v (localMap v w' x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 F)) ∧
      Module.finrank (v.adicCompletion F) (w.adicCompletion E) =
        w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) := by
  obtain ⟨h1, h2⟩ := ramificationIdx_inertiaDeg_eq_of_liesOver hθ hs v w w'
  refine ⟨fun x => ?_, fun x => ?_, ?_⟩
  · rw [valued_localMap, h1]
  · rw [valued_localMap, ← h1]
  · rw [finrank_adicCompletion_eq_ef v w, h1, h2]

/-- **65.r18** (O'Meara 1963, §65A, p. 175): $e_\mathfrak p f_\mathfrak p = n_\mathfrak p$ with
$e_\mathfrak p = f_\mathfrak p = n_\mathfrak p = 1$ if $\theta$ is a square at $\mathfrak p$, while for a non-square
$n_\mathfrak p = 2$ and $(e_\mathfrak p, f_\mathfrak p) = (1, 2)$ or $(2, 1)$. -/
@[kb "omeara1963" "§65A, p. 175 (e_𝔭 = f_𝔭 = n_𝔭 = 1, or n_𝔭 = 2 and (e,f) = (1,2) or (2,1))"]
theorem ramification_inertia_cases :
    (IsSquare (algebraMap F (v.adicCompletion F) θ) →
      w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1) ∧
    (¬ IsSquare (algebraMap F (v.adicCompletion F) θ) →
      Module.finrank (v.adicCompletion F) (w.adicCompletion E) = 2 ∧
      ((w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 2) ∨
        (w.asIdeal.ramificationIdx (𝓞 F) = 2 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1))) := by
  refine ⟨ef_eq_one_of_isSquare hθ hs v w, fun hv => ?_⟩
  have h2 := (finrank_eq_two_iff_not_isSquare hθ hs v w).2 hv
  refine ⟨h2, ?_⟩
  have h := finrank_adicCompletion_eq_ef v w
  rw [h2] at h
  have he := ramificationIdx_pos v w
  have hf : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Nat.pos_of_ne_zero (inertiaDeg_ne_zero v w)
  have hle : w.asIdeal.ramificationIdx (𝓞 F) ≤ 2 := by nlinarith
  generalize w.asIdeal.ramificationIdx (𝓞 F) = e at *
  generalize w.asIdeal.inertiaDeg (𝓞 F) = f at *
  interval_cases e <;> omega

end Spots

end Quadratic

/-! ### 65.r20, 65.r21: unramified extensions -/

section Unramified

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- **$E/F$ is unramified at the discrete spot $\mathfrak p$** (O'Meara 1963, §65A, p. 176): $e(\mathfrak P|\mathfrak p)
= 1$ and $f(\mathfrak P|\mathfrak p) = n(\mathfrak P|\mathfrak p)$ for every spot $\mathfrak P \mid \mathfrak p$ of $E$.
O'Meara writes $e_\mathfrak p = 1$, $f_\mathfrak p = n_\mathfrak p$ for the values common to all $\mathfrak P \mid
\mathfrak p$ (valid for abelian $E/F$); for a general finite $E/F$ the condition is imposed at each $\mathfrak P$,
with $n(\mathfrak P|\mathfrak p) = [E_\mathfrak P : F_\mathfrak p]$. -/
@[kb "omeara1963" "§65A, p. 176 (E/F is unramified at the discrete spot 𝔭: e_𝔭 = 1, f_𝔭 = n_𝔭)"]
def IsUnramifiedAt (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal],
    w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
      w.asIdeal.inertiaDeg (𝓞 F) = Module.finrank (v.adicCompletion F) (w.adicCompletion E)

/-- **$E_\mathfrak P/F_\mathfrak p$ is an unramified extension of local fields** (O'Meara 1963, §65A, p. 176), in the
form: the normalized valuation of $E_\mathfrak P$ restricts to that of $F_\mathfrak p$, i.e. a prime element of
$F_\mathfrak p$ remains a prime element of $E_\mathfrak P$ ($e = 1$). For a finite extension of local fields this is
equivalent to $e = 1$ and $f = [E_\mathfrak P : F_\mathfrak p]$ (`isUnramifiedLocal_iff`). -/
@[kb "omeara1963" "§65A, p. 176 (E_𝔓/F_𝔭 is an unramified extension of local fields)"]
def IsUnramifiedLocal (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] : Prop :=
  ∀ x : v.adicCompletion F, Valued.v (localMap v w x) = Valued.v x

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- The local form of unramifiedness is $e = 1$. -/
lemma isUnramifiedLocal_iff_ramificationIdx_eq_one :
    IsUnramifiedLocal v w ↔ w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have h1 := h (algebraMap F (v.adicCompletion F) π)
    rw [valued_localMap, QuadFormsKB.HN.valued_algebraMap, hπ] at h1
    rw [← WithZero.exp_nsmul] at h1
    have := WithZero.exp_injective (by simpa using h1 : WithZero.exp (-(w.asIdeal.ramificationIdx (𝓞 F) : ℤ)) =
      WithZero.exp (-1 : ℤ))
    omega
  · intro h x
    rw [valued_localMap, h, pow_one]

/-- **65.r20, local form** (O'Meara 1963, §65A, p. 176): for a single $\mathfrak P \mid \mathfrak p$, ($e = 1$ and
$f = n(\mathfrak P|\mathfrak p)$) if and only if $E_\mathfrak P/F_\mathfrak p$ is unramified. -/
theorem unramified_iff_isUnramifiedLocal :
    (w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧
      w.asIdeal.inertiaDeg (𝓞 F) = Module.finrank (v.adicCompletion F) (w.adicCompletion E)) ↔
      IsUnramifiedLocal v w := by
  rw [isUnramifiedLocal_iff_ramificationIdx_eq_one]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [finrank_adicCompletion_eq_ef v w, h, one_mul]

/-- **65.r20** (O'Meara 1963, §65A, p. 176): $E/F$ is unramified at $\mathfrak p$ if and only if $E_\mathfrak P/F_\mathfrak
p$ is an unramified extension of local fields at each $\mathfrak P$ dividing $\mathfrak p$. *Update (generalization):* stated
and proved for every extension $E/F$ of number fields (O'Meara: $E = F(\sqrt\theta)$). -/
@[kb "omeara1963" "§65A, p. 176 (E/F unramified at 𝔭 iff E_𝔓/F_𝔭 unramified at each 𝔓 | 𝔭)"]
theorem isUnramifiedAt_iff :
    IsUnramifiedAt (E := E) v ↔
      ∀ (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedLocal v w :=
  forall_congr' fun w => forall_congr' fun _ => unramified_iff_isUnramifiedLocal v w

/-- **65.r21** (O'Meara 1963, §65A, p. 176): for $E = F(\sqrt\theta)$, $E/F$ is unramified at $\mathfrak p$ whenever
the local degree $n_\mathfrak p$ is $1$, i.e. $\theta$ is a square at $\mathfrak p$. -/
@[kb "omeara1963" "§65A, p. 176 (E/F is unramified at 𝔭 whenever n_𝔭 = 1)"]
theorem isUnramifiedAt_of_isSquare [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E}
    (hs : s ^ 2 = algebraMap F E θ) (hv : IsSquare (algebraMap F (v.adicCompletion F) θ)) :
    IsUnramifiedAt (E := E) v := by
  intro w _
  obtain ⟨h1, h2⟩ := ef_eq_one_of_isSquare hθ hs v w hv
  exact ⟨h1, h2.trans ((finrank_eq_one_iff_isSquare hθ hs v w).2 hv).symm⟩

end Unramified

/-! ### 65.r22: the conjugation acts on the valuations -/

section Conjugation

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
  (σ : E ≃ₐ[F] E) (hσ : σ s = -s)
include hθ hs hσ

omit hσ in
lemma ne_zero_of_sq : s ≠ 0 := by
  rintro rfl
  exact hθ ⟨0, (algebraMap F E).injective (by rw [← hs]; simp)⟩

/-- The conjugation $\sigma$ with $\sigma\sqrt\theta = -\sqrt\theta$ is not the identity. -/
lemma conj_ne_one : σ ≠ 1 := by
  intro h
  rw [h] at hσ
  have h2 : (2 : E) * s = 0 := by
    have : s = -s := hσ
    linear_combination this
  rcases mul_eq_zero.1 h2 with h | h
  · exact two_ne_zero h
  · exact ne_zero_of_sq hθ hs h

variable (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- The $\sigma$-conjugate spot lies over the same spot of $F$. -/
lemma liesOver_conj :
    (QuadFormsKB.HN.comapEquiv (QuadFormsKB.HN.σO σ) w).asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  have h1 := QuadFormsKB.HN.under_comapEquiv σ w
  have h2 : v = QuadFormsKB.HN.under (F := F) w := eq_spotBelow_of_liesOver v w
  have h3 := congrArg HeightOneSpectrum.asIdeal (h2.trans h1.symm)
  exact h3

/-- **65.r22, one spot over $\mathfrak p$** (O'Meara 1963, §65A, p. 176): if $\theta$ is a non-square at
$\mathfrak p$ (so $n_\mathfrak p = 2$ and there is a single spot $\mathfrak P \mid \mathfrak p$), then
$\lvert\sigma\Gamma\rvert_\mathfrak P = \lvert\Gamma\rvert_\mathfrak P$ for all $\Gamma \in E$, with $\sigma$ the
conjugation of $E/F$ ($\sigma\sqrt\theta = -\sqrt\theta$). Here $\lvert\cdot\rvert_\mathfrak P$ is the
$\mathfrak P$-adic valuation `w.valuation E`. -/
@[kb "omeara1963" "§65A, p. 176 (|Γ'|_𝔓 = |Γ|_𝔓 for all Γ ∈ E when n_𝔭 = 2)"]
theorem valuation_conj_eq_of_not_isSquare (hv : ¬ IsSquare (algebraMap F (v.adicCompletion F) θ)) (Γ : E) :
    w.valuation E (σ Γ) = w.valuation E Γ := by
  have := liesOver_conj hθ hs σ hσ v w
  have := eq_of_not_isSquare hθ hs v (QuadFormsKB.HN.comapEquiv (QuadFormsKB.HN.σO σ) w) w hv
  rw [QuadFormsKB.HN.valuation_galois, this]

/-- **65.r22, two spots over $\mathfrak p$** (O'Meara 1963, §65A, p. 176): if $\mathfrak P_1 \ne \mathfrak P_2$ are two
spots over $\mathfrak p$ (which happens exactly when $\theta$ is a square at $\mathfrak p$, $n_\mathfrak p = 1$), then
$\lvert\Gamma\rvert_{\mathfrak P_1} = \lvert\sigma\Gamma\rvert_{\mathfrak P_2}$ for all $\Gamma \in E$. (O'Meara
writes "it can be verified that $\lvert\Gamma\rvert_{\mathfrak P_1} = \lvert\Gamma'\rvert_{\mathfrak P_2}$".) -/
@[kb "omeara1963" "§65A, p. 176 (|Γ|_{𝔓₁} = |Γ'|_{𝔓₂} for all Γ ∈ E when n_𝔭 = 1)"]
theorem valuation_conj_eq_of_isSquare (w₁ w₂ : HeightOneSpectrum (𝓞 E)) [w₁.asIdeal.LiesOver v.asIdeal]
    [w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) (Γ : E) :
    w₁.valuation E Γ = w₂.valuation E (σ Γ) := by
  have h1 : QuadFormsKB.HN.under (F := F) w₂ = QuadFormsKB.HN.under (F := F) w₁ :=
    ((eq_spotBelow_of_liesOver v w₂).symm.trans (eq_spotBelow_of_liesOver v w₁))
  rcases QuadFormsKB.HN.over_eq_or σ (conj_ne_one hθ hs σ hσ) w₂ w₁ h1 with h | h
  · exact absurd h hne
  · rw [QuadFormsKB.HN.valuation_galois, ← h]

end Conjugation

/-! ### 65.r31: Proposition 65:11 from Corollary 65:18a -/

section R31

variable {F : Type} [Field F] [NumberField F]

/-- **Proposition 65:11 from Corollary 65:18a** (O'Meara 1963, §65B, footnote on p. 181: "65:11 can be obtained from
Corollary 65:18a"). Under the conventions (i)–(iv) of §65A, if $\alpha \in F^\times$ is a unit at every spot of $S$
and a square at every spot of $\Omega - S$, then $\alpha$ is a square in $F$. Proof: put $T = $ the finite spots
outside $S$, choose generators of $\mathfrak u$ modulo squares (`exists_isGenModSq`) and dual spots
$\mathfrak p_1, \dots, \mathfrak p_s$ (65:18, `exists_dual_spots`), and apply 65:18a (`isSquare_of_dual_spots`), the
unit hypothesis holding at every spot of $S$. Same statement as `isSquare_of_unit_of_isSquare_outside`. -/
@[kb "omeara1963" "§65B, p. 181, footnote (65:11 follows from 65:18a)"]
theorem isSquare_of_unit_of_isSquare_outside' {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {α : F} (hα : α ≠ 0) (hunit : ∀ v ∈ S, v.valuation F α = 1)
    (hsq : ∀ v ∉ S, IsSquare (algebraMap F (v.adicCompletion F) α))
    (hinf : ∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion α)) : IsSquare α := by
  classical
  set T := hS.cofinite.toFinset with hT
  have hmem : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
  have hTc : ((T : Set (HeightOneSpectrum (𝓞 F))))ᶜ = S := by
    ext v; simp [hmem]
  have hS' : SConventions (F := F) (↑T)ᶜ := hTc ▸ hS
  obtain ⟨e, he⟩ := exists_isGenModSq T
  obtain ⟨p, -, hp, hpe⟩ := exists_dual_spots T he
  exact isSquare_of_dual_spots T hS' he (fun i => (hp i).1) hpe hα
    (fun v hv => hsq v ((hmem v).1 hv)) hinf
    (fun v hvT _ => hunit v (by by_contra h; exact hvT ((hmem v).2 h)))

end R31

end QuadFormsKB.OMeara
