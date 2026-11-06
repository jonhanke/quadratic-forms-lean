/-
# O'Meara §64: the norm of an idèle, $N_{E/F}\colon J_E \to J_F$

**Setting.** $E/F$ is an extension of number fields (finite separable, O'Meara §64, p. 173). Idèles are Mathlib's
`IdeleGroup (𝓞 F) F` $= \mathbb A_F^\times$ (see `Sec64.lean`); the local norms $N_{\mathfrak P|\mathfrak p}$ are
`localNormFin` (finite spots, `Sec64Local.lean`) and `localNormInf` (infinite spots, `Sec64Inf.lean`).

**Defines**
* `spotBelow w`: the finite spot $\mathfrak p$ of $F$ below a finite spot $\mathfrak P$ of $E$; `spotsAbove S`: the set of
  finite spots of $E$ lying over a set $S$ of finite spots of $F$ (O'Meara's "$S$ also denotes the spots $\mathfrak P$
  with $\mathfrak P \mid S$");
* `adeleNorm`: $\mathbb A_E \to \mathbb A_F$, $\mathfrak I \mapsto \bigl(\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak
  P|\mathfrak p}\mathfrak I_\mathfrak P\bigr)_{\mathfrak p}$, a multiplicative map;
* `ideleNorm`: **the norm of an idèle** $N_{E/F}\colon J_E \to J_F$ (O'Meara §64, p. 173), a group homomorphism.

**Proves** (§64, p. 173)
* `ideleAt_ideleNorm`, `ideleAtInf_ideleNorm`: the components of $N_{E/F}\mathfrak I$;
* `ideleNorm_mem_sIdeles`: $N_{E/F}J_E^S \subseteq J_F^S$;
* `ideleNorm_unitEmbedding`: the square $\dot E \to J_E$, $\dot F \to J_F$ with $N_{E/F}$ on both sides commutes
  (from Theorem 15:3), and `map_principalSubgroup_le`: $N_{E/F}P_E \subseteq P_F$;
* `map_principalSIdeles_le`: $N_{E/F}P_E^S \subseteq P_F^S$.
-/
import QuadFormsKB.Literature.OMeara.Sec64Inf

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-! ### Spots below and above -/

/-- The finite spot $\mathfrak p = \mathfrak P \cap \mathcal O_F$ of $F$ below a finite spot $\mathfrak P$ of $E$. -/
def spotBelow (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.IsIntegral.under_ne_bot (𝓞 F) w.ne_bot

instance (w : HeightOneSpectrum (𝓞 E)) : w.asIdeal.LiesOver (spotBelow (F := F) w).asIdeal := ⟨rfl⟩

lemma eq_spotBelow_of_liesOver (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
    [h : w.asIdeal.LiesOver v.asIdeal] : v = spotBelow w :=
  HeightOneSpectrum.ext h.over

/-- The finite spots of $E$ lying over a set $S$ of finite spots of $F$. -/
def spotsAbove (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 E)) :=
  {w | spotBelow w ∈ S}

lemma mem_spotsAbove_of_liesOver {S : Set (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S)
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] : w ∈ spotsAbove S := by
  show spotBelow w ∈ S
  rwa [← eq_spotBelow_of_liesOver v w]

/-! ### Norms and integrality -/

lemma norm_le_one_iff_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FinitePlace.norm_def, NNReal.coe_le_one,
    WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)]

lemma norm_eq_one_iff_valued {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : ‖x‖ = 1 ↔ Valued.v x = 1 := by
  rw [FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ (HeightOneSpectrum.absNorm_ne_zero v)
      (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne']

/-! ### The norm of an adèle -/

/-- The component $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}\mathfrak I_\mathfrak P$ at a finite spot. -/
def finNormComp (x : (w : HeightOneSpectrum (𝓞 E)) → w.adicCompletion E) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F :=
  ∏ w : SpotsOver E v, localNormFin v w.1 (x w.1)

/-- The component $\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}\mathfrak I_\mathfrak P$ at an infinite
spot. -/
def infNormComp (x : (w : InfinitePlace E) → w.Completion) (v : InfinitePlace F) : v.Completion :=
  ∏ w : InfSpotsOver E v, localNormInf E v w.1 (x w.1)

/-- If $\mathfrak I_\mathfrak P$ is integral at almost all $\mathfrak P$, then the norm is integral at almost all
$\mathfrak p$. -/
lemma eventually_finNormComp_mem (x : (w : HeightOneSpectrum (𝓞 E)) → w.adicCompletion E)
    (hx : ∀ᶠ w in Filter.cofinite, x w ∈ w.adicCompletionIntegers E) :
    ∀ᶠ v in Filter.cofinite, finNormComp x v ∈ v.adicCompletionIntegers F := by
  have hfin : Set.Finite {w | x w ∉ w.adicCompletionIntegers E} := hx
  refine Filter.mem_of_superset (hfin.image spotBelow).compl_mem_cofinite ?_
  intro v hv
  simp only [Set.mem_compl_iff, Set.mem_image, Set.mem_setOf_eq, not_exists, not_and] at hv
  show finNormComp x v ∈ v.adicCompletionIntegers F
  rw [← norm_le_one_iff_mem, finNormComp, norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun w _ => ?_
  refine norm_localNormFin_le_one v w.1 ((norm_le_one_iff_mem w.1 _).2 ?_)
  by_contra hw
  exact hv w.1 hw (eq_spotBelow_of_liesOver v w.1).symm

/-- **The norm of an adèle** $\mathbb A_E \to \mathbb A_F$: the product of the local norms at each spot of $F$. -/
def adeleNorm : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 F) F where
  toFun x := (infNormComp x.1, ⟨finNormComp (fun w => x.2 w), eventually_finNormComp_mem _ x.2.2⟩)
  map_one' := by
    refine Prod.ext ?_ ?_
    · funext v
      change ∏ w : InfSpotsOver E v, localNormInf E v w.1 (1 : w.1.Completion) = (1 : v.Completion)
      simp
    · apply RestrictedProduct.ext; intro v
      change ∏ w : SpotsOver E v, localNormFin v w.1 (1 : w.1.adicCompletion E) = (1 : v.adicCompletion F)
      simp
  map_mul' x y := by
    refine Prod.ext ?_ ?_
    · funext v
      change ∏ w : InfSpotsOver E v, localNormInf E v w.1 (x.1 w.1 * y.1 w.1) =
        (∏ w : InfSpotsOver E v, localNormInf E v w.1 (x.1 w.1)) *
          ∏ w : InfSpotsOver E v, localNormInf E v w.1 (y.1 w.1)
      simp only [map_mul, Finset.prod_mul_distrib]
    · apply RestrictedProduct.ext; intro v
      change ∏ w : SpotsOver E v, localNormFin v w.1 (x.2 w.1 * y.2 w.1) =
        (∏ w : SpotsOver E v, localNormFin v w.1 (x.2 w.1)) *
          ∏ w : SpotsOver E v, localNormFin v w.1 (y.2 w.1)
      simp only [map_mul, Finset.prod_mul_distrib]

/-- **The norm of an idèle** $N_{E/F}\colon J_E \to J_F$ (O'Meara 1963, §64, p. 173): $N_{E/F}\mathfrak I =
\bigl(\prod_{\mathfrak P|\mathfrak p} N_{\mathfrak P|\mathfrak p}\mathfrak I_\mathfrak P\bigr)_{\mathfrak p \in \Omega_F}$, an
idèle since $\lvert N_{\mathfrak P|\mathfrak p}\mathfrak I_\mathfrak P\rvert_\mathfrak p = \lvert\mathfrak
I_\mathfrak P\rvert_\mathfrak P$ (`norm_localNormFin`); a group homomorphism. -/
@[kb "omeara1963" "§64, p. 173 (the norm N_{E/F} 𝔍 of an idèle; the homomorphism N_{E/F} : J_E → J_F)"]
def ideleNorm : IdeleGroup (𝓞 E) E →* IdeleGroup (𝓞 F) F := Units.map adeleNorm

/-- The component of $N_{E/F}\mathfrak I$ at a finite spot $\mathfrak p$. -/
@[kb "omeara1963" "§64, p. 173 ((N_{E/F}𝔍)_𝔭 = ∏_{𝔓|𝔭} N_{𝔓|𝔭} 𝔍_𝔓, finite spot)"]
theorem ideleAt_ideleNorm (i : IdeleGroup (𝓞 E) E) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (ideleNorm i) v = ∏ w : SpotsOver E v, localNormFin v w.1 (ideleAt i w.1) := rfl

/-- The component of $N_{E/F}\mathfrak I$ at an infinite spot $\mathfrak p$. -/
@[kb "omeara1963" "§64, p. 173 ((N_{E/F}𝔍)_𝔭 = ∏_{𝔓|𝔭} N_{𝔓|𝔭} 𝔍_𝔓, infinite spot)"]
theorem ideleAtInf_ideleNorm (i : IdeleGroup (𝓞 E) E) (v : InfinitePlace F) :
    ideleAtInf (ideleNorm i) v = ∏ w : InfSpotsOver E v, localNormInf E v w.1 (ideleAtInf i w.1) := rfl

/-- **$N_{E/F}J_E^S \subseteq J_F^S$** (O'Meara 1963, §64, p. 173), where on $E$ the letter $S$ denotes the spots
over $S$ (`spotsAbove S`). -/
@[kb "omeara1963" "§64, p. 173 (N_{E/F} J_E^S ⊆ J_F^S)"]
theorem ideleNorm_mem_sIdeles (S : Set (HeightOneSpectrum (𝓞 F))) {i : IdeleGroup (𝓞 E) E}
    (hi : i ∈ sIdeles (spotsAbove S)) : ideleNorm i ∈ sIdeles S := by
  intro v hv
  rw [← norm_eq_one_iff_valued, ideleAt_ideleNorm, norm_prod]
  refine Finset.prod_eq_one fun w _ => norm_localNormFin_eq_one v w.1 ?_
  rw [norm_eq_one_iff_valued]
  exact hi w.1 (mem_spotsAbove_of_liesOver hv w.1)

/-- The map form of `ideleNorm_mem_sIdeles`. -/
theorem map_sIdeles_le (S : Set (HeightOneSpectrum (𝓞 F))) :
    (sIdeles (spotsAbove S)).map (ideleNorm (F := F) (E := E)) ≤ sIdeles S := by
  rintro _ ⟨i, hi, rfl⟩
  exact ideleNorm_mem_sIdeles S hi

/-- The finite component of a principal idèle. -/
lemma ideleAt_unitEmbedding_nf {K : Type} [Field K] [NumberField K] (a : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ideleAt (IdeleGroup.unitEmbedding (𝓞 K) K a) v = algebraMap K (v.adicCompletion K) a := rfl

/-- The infinite component of a principal idèle. -/
lemma ideleAtInf_unitEmbedding_nf {K : Type} [Field K] [NumberField K] (a : Kˣ) (w : InfinitePlace K) :
    ideleAtInf (IdeleGroup.unitEmbedding (𝓞 K) K a) w = algebraMap K w.Completion a := rfl

/-- **The norm of a principal idèle** (O'Meara 1963, §64, p. 173): the square $\dot E \to J_E$, $\dot F \to J_F$ with
$N_{E/F}$ on both sides commutes ("an immediate consequence of the definition and of Theorem 15:3"). -/
@[kb "omeara1963" "§64, p. 173 (the commutative square Ė → J_E, Ḟ → J_F with N_{E/F}, from 15:3)"]
theorem ideleNorm_unitEmbedding (a : Eˣ) :
    ideleNorm (IdeleGroup.unitEmbedding (𝓞 E) E a) =
      IdeleGroup.unitEmbedding (𝓞 F) F (Units.map (Algebra.norm F : E →* F) a) := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext v
    exact prod_localNormInf_eq_norm E v (a : E)
  · apply RestrictedProduct.ext
    intro v
    exact prod_localNormFin_eq_norm E v (a : E)

/-- **$N_{E/F}P_E \subseteq P_F$** (O'Meara 1963, §64, p. 173). -/
@[kb "omeara1963" "§64, p. 173 (N_{E/F} P_E ⊆ P_F)"]
theorem map_principalSubgroup_le :
    (IdeleGroup.principalSubgroup (𝓞 E) E).map (ideleNorm (F := F) (E := E)) ≤
      IdeleGroup.principalSubgroup (𝓞 F) F := by
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  exact ⟨_, (ideleNorm_unitEmbedding a).symm⟩

/-- **$N_{E/F}P_E^S \subseteq P_F^S$** (O'Meara 1963, §65A, p. 175, from §64). -/
@[kb "omeara1963" "§65A, p. 175 (N_{E/F} P_E^S ⊆ P_F^S, from the commutative diagram of §64)"]
theorem map_principalSIdeles_le (S : Set (HeightOneSpectrum (𝓞 F))) :
    (principalSIdeles (spotsAbove S)).map (ideleNorm (F := F) (E := E)) ≤ principalSIdeles S := by
  rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
  exact ⟨ideleNorm_mem_sIdeles S hi1, map_principalSubgroup_le ⟨i, hi2, rfl⟩⟩

end QuadFormsKB.OMeara
