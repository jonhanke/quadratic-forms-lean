/-
# O'Meara §65A: local norms of idèles, Examples 65:2–65:4

**Setting** as in `Sec65Local.lean`: $F$ a number field, $\theta$ a non-square of $F$, $E = F(\sqrt\theta)$ with
$s^2 = \theta$; idèles and their norm $N_{E/F}\colon J_E \to J_F$ as in `Sec64Norm.lean`.

**Defines** (§65A, p. 176)
* `IsLocalNormAt E v x`: $x \in F_\mathfrak p$ is a *local norm* at the finite spot $\mathfrak p$:
  $x \in N_{\mathfrak P|\mathfrak p}E_\mathfrak P$ for all $\mathfrak P \mid \mathfrak p$; `IsLocalNormAtInf` at an
  infinite spot;
* `localNormGroup E v` ($\subseteq \dot F_\mathfrak p$), `localNormGroupInf E v`: the group of local norms.

**Proves**
* `isLocalNormAt_of_isSquare` (65.r26): every element is a local norm when $n_\mathfrak p = 1$;
* `isLocalNormAt_iff_hilbertSymbol` (65.r28, 65.r29): $x \ne 0$ is a local norm at $\mathfrak p$ iff
  $(\theta, x)_\mathfrak p = 1$ (finite spots; `isLocalNormAtInf_iff_hilbertSymbol` at infinite spots);
* `index_localNormGroup` (65.r27): $(\dot F_\mathfrak p : \text{local norms}) = 1$ or $2$ according as $n_\mathfrak p = 1$ or $2$;
* **Example 65:2** `mem_range_ideleNorm_iff`: an idèle is in $N_{E/F}J_E$ iff it is a local norm at every spot with
  $n_\mathfrak p = 2$, and `exists_ideleNorm_eq` (the "incidentally" of 65:2);
* **Example 65:3** `mem_map_sIdeles_iff`: $N_{E/F}J_E^S = \{i \in J_F^S : i$ a local norm wherever $n_\mathfrak p = 2\}$.
-/
import QuadFormsKB.Literature.OMeara.Sec65Local
import QuadFormsKB.Literature.OMeara.Sec65A
import QuadFormsKB.Literature.OMeara.Sec64Tower

open NumberField IsDedekindDomain InfinitePlace

open scoped NumberField.LiesOver TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

/-! ### Local norms -/

/-- **Local norm at a finite spot** (O'Meara 1963, §65A, p. 176): $x \in F_\mathfrak p$ is a local norm of $E/F$ at
$\mathfrak p$ if $x \in N_{\mathfrak P|\mathfrak p}E_\mathfrak P$ for every $\mathfrak P \mid \mathfrak p$. -/
@[kb "omeara1963" "§65A, p. 176 (α ∈ F_𝔭 is a local norm at 𝔭 if α ∈ N_{𝔓|𝔭} E_𝔓 for all 𝔓 | 𝔭; finite spot)"]
def IsLocalNormAt (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : Prop :=
  ∀ w : SpotsOver E v, ∃ y : w.1.adicCompletion E, localNormFin v w.1 y = x

/-- **Local norm at an infinite spot** (O'Meara 1963, §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (α ∈ F_𝔭 is a local norm at 𝔭 if α ∈ N_{𝔓|𝔭} E_𝔓 for all 𝔓 | 𝔭; infinite spot)"]
def IsLocalNormAtInf (v : InfinitePlace F) (x : v.Completion) : Prop :=
  ∀ w : InfSpotsOver E v, ∃ y : w.1.Completion, localNormInf E v w.1 y = x

/-- The group of local norms in $\dot F_\mathfrak p$ at a finite spot. -/
def localNormGroup (v : HeightOneSpectrum (𝓞 F)) : Subgroup (v.adicCompletion F)ˣ :=
  ⨅ w : SpotsOver E v, (Units.map (localNormFin v w.1)).range

/-- The group of local norms in $\dot F_\mathfrak p$ at an infinite spot. -/
def localNormGroupInf (v : InfinitePlace F) : Subgroup v.Completionˣ :=
  ⨅ w : InfSpotsOver E v, (Units.map (localNormInf E v w.1)).range

lemma mem_localNormGroup_iff (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    x ∈ localNormGroup E v ↔ IsLocalNormAt E v x := by
  simp only [localNormGroup, Subgroup.mem_iInf, MonoidHom.mem_range]
  refine forall_congr' fun w => ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Units.val hy⟩, fun ⟨y, hy⟩ => ?_⟩
  have hy0 : y ≠ 0 := by rintro rfl; rw [localNormFin_apply, Algebra.norm_zero] at hy; exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext hy⟩

lemma mem_localNormGroupInf_iff (v : InfinitePlace F) (x : v.Completionˣ) :
    x ∈ localNormGroupInf E v ↔ IsLocalNormAtInf E v x := by
  simp only [localNormGroupInf, Subgroup.mem_iInf, MonoidHom.mem_range]
  refine forall_congr' fun w => ⟨fun ⟨y, hy⟩ => ⟨y, congrArg Units.val hy⟩, fun ⟨y, hy⟩ => ?_⟩
  have hy0 : y ≠ 0 := by rintro rfl; rw [localNormInf_apply, Algebra.norm_zero] at hy; exact x.ne_zero hy.symm
  exact ⟨Units.mk0 y hy0, Units.ext hy⟩

/-- **An idèle $i$ is a local norm at $\mathfrak p$ if $i_\mathfrak p$ is** (O'Meara 1963, §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (the idèle 𝔦 is a local norm at 𝔭 if 𝔦_𝔭 is)"]
def IsLocalNormIdeleAt (i : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  IsLocalNormAt E v (ideleAt i v)

/-- An idèle is a local norm at an infinite spot $\mathfrak p$ if $i_\mathfrak p$ is. -/
def IsLocalNormIdeleAtInf (i : IdeleGroup (𝓞 F) F) (v : InfinitePlace F) : Prop :=
  IsLocalNormAtInf E v (ideleAtInf i v)

/-- A square has Hilbert symbol $1$ with everything. -/
lemma hilbertSymbol_of_isSquare {K : Type*} [Field K] {a : K} (ha : IsSquare a) (b : K) :
    hilbertSymbol K a b = 1 := by
  obtain ⟨c, rfl⟩ := ha
  unfold hilbertSymbol
  rw [if_pos ⟨1, 0, c, by simp, by ring⟩]

lemma nonempty_infSpotsOver [Algebra.IsQuadraticExtension F E] (v : InfinitePlace F) :
    Nonempty (InfSpotsOver E v) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_infSpotsOver E v
  rw [Finset.univ_eq_empty, Finset.sum_empty, Algebra.IsQuadraticExtension.finrank_eq_two] at this
  exact absurd this (by norm_num)

variable [Algebra.IsQuadraticExtension F E] {θ : F} (hθ : ¬ IsSquare θ) {s : E} (hs : s ^ 2 = algebraMap F E θ)
include hθ hs

/-- **Every element of $F_\mathfrak p$ is a local norm when $n_\mathfrak p = 1$** (O'Meara 1963, §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (every element of F_𝔭 is a local norm at 𝔭 when n_𝔭 = 1)"]
theorem isLocalNormAt_of_isSquare (v : HeightOneSpectrum (𝓞 F))
    (hv : IsSquare (algebraMap F (v.adicCompletion F) θ)) (x : v.adicCompletion F) : IsLocalNormAt E v x :=
  fun w => localNormFin_surjective_of_isSquare hθ hs v w.1 hv x

theorem isLocalNormAtInf_of_isSquare (v : InfinitePlace F)
    (hv : IsSquare (algebraMap F v.Completion θ)) (x : v.Completion) : IsLocalNormAtInf E v x :=
  fun w => localNormInf_surjective_of_isSquare hθ hs v w.1 hv x

/-- **Local norms and the Hilbert symbol** (O'Meara 1963, §65A, p. 176): $x \in \dot F_\mathfrak p$ is a local norm
at the finite spot $\mathfrak p$ iff $(\theta, x)_\mathfrak p = 1$. -/
@[kb "omeara1963" "§65A, p. 176 (α ∈ Ḟ_𝔭 is a local norm at 𝔭 iff (α, θ)_𝔭 = 1, all finite spots)"]
theorem isLocalNormAt_iff_hilbertSymbol (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    IsLocalNormAt E v x ↔ hilbertSymbol (v.adicCompletion F) (algebraMap F _ θ) x = 1 := by
  by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
  · exact ⟨fun _ => hilbertSymbol_of_isSquare hv _, fun _ => isLocalNormAt_of_isSquare E hθ hs v hv _⟩
  · rw [← mem_localNormGroup_iff]
    simp only [localNormGroup, Subgroup.mem_iInf]
    obtain ⟨w₀⟩ := nonempty_spotsOver hθ hs v
    exact ⟨fun h => (mem_range_localNormFin_iff hθ hs v w₀.1 hv x).1 (h w₀),
      fun h w => (mem_range_localNormFin_iff hθ hs v w.1 hv x).2 h⟩

/-- **Local norms and the Hilbert symbol at an infinite spot** (O'Meara 1963, §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (α ∈ Ḟ_𝔭 is a local norm at 𝔭 iff (α, θ)_𝔭 = 1, infinite spots)"]
theorem isLocalNormAtInf_iff_hilbertSymbol (v : InfinitePlace F) (x : v.Completionˣ) :
    IsLocalNormAtInf E v x ↔ hilbertSymbol v.Completion (algebraMap F _ θ) x = 1 := by
  by_cases hv : IsSquare (algebraMap F v.Completion θ)
  · exact ⟨fun _ => hilbertSymbol_of_isSquare hv _, fun _ => isLocalNormAtInf_of_isSquare E hθ hs v hv _⟩
  · rw [← mem_localNormGroupInf_iff]
    simp only [localNormGroupInf, Subgroup.mem_iInf]
    obtain ⟨w₀⟩ := nonempty_infSpotsOver E v
    exact ⟨fun h => (mem_range_localNormInf_iff hθ hs v w₀.1 hv x).1 (h w₀),
      fun h w => (mem_range_localNormInf_iff hθ hs v w.1 hv x).2 h⟩

/-- **An idèle is a local norm at $\mathfrak p$ iff $(\mathfrak i_\mathfrak p, \theta)_\mathfrak p = 1$** (O'Meara
1963, §65A, p. 176). -/
@[kb "omeara1963" "§65A, p. 176 (𝔦 is a local norm at 𝔭 iff (𝔦_𝔭, θ)_𝔭 = 1)"]
theorem isLocalNormIdeleAt_iff (i : IdeleGroup (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    IsLocalNormIdeleAt E i v ↔ hilbertSymbol (v.adicCompletion F) (algebraMap F _ θ) (ideleAt i v) = 1 :=
  isLocalNormAt_iff_hilbertSymbol E hθ hs v (idAtHom v i)

open scoped Classical in
/-- **The local norm index** (O'Meara 1963, §65A, p. 176, Corollary 63:13a): $(\dot F_\mathfrak p : \text{local
norms}) = 1$ if $n_\mathfrak p = 1$ and $2$ if $n_\mathfrak p = 2$. -/
@[kb "omeara1963" "§65A, p. 176 ((Ḟ_𝔭 : N_{𝔓|𝔭} Ė_𝔓) = 1 if n_𝔭 = 1, 2 if n_𝔭 = 2; finite spots)"]
theorem index_localNormGroup (v : HeightOneSpectrum (𝓞 F)) :
    (localNormGroup E v).index = if IsSquare (algebraMap F (v.adicCompletion F) θ) then 1 else 2 := by
  split_ifs with hv
  · rw [Subgroup.index_eq_one]
    exact eq_top_iff.2 fun x _ => (mem_localNormGroup_iff E v x).2 (isLocalNormAt_of_isSquare E hθ hs v hv x)
  · obtain ⟨w₀⟩ := nonempty_spotsOver hθ hs v
    have : localNormGroup E v = (Units.map (localNormFin v w₀.1)).range := by
      ext x
      rw [mem_localNormGroup_iff, isLocalNormAt_iff_hilbertSymbol E hθ hs, mem_range_localNormFin_iff hθ hs v w₀.1 hv]
    rw [this, index_localNormFin_eq_two hθ hs v w₀.1 hv]

open scoped Classical in
theorem index_localNormGroupInf (v : InfinitePlace F) :
    (localNormGroupInf E v).index = if IsSquare (algebraMap F v.Completion θ) then 1 else 2 := by
  split_ifs with hv
  · rw [Subgroup.index_eq_one]
    exact eq_top_iff.2 fun x _ =>
      (mem_localNormGroupInf_iff E v x).2 (isLocalNormAtInf_of_isSquare E hθ hs v hv x)
  · obtain ⟨w₀⟩ := nonempty_infSpotsOver E v
    have : localNormGroupInf E v = (Units.map (localNormInf E v w₀.1)).range := by
      ext x
      rw [mem_localNormGroupInf_iff, isLocalNormAtInf_iff_hilbertSymbol E hθ hs,
        mem_range_localNormInf_iff hθ hs v w₀.1 hv]
    rw [this, index_localNormInf_eq_two hθ hs v w₀.1 hv]

/-! ### Example 65:2 -/

omit [Algebra.IsQuadraticExtension F E] hθ hs in
/-- An idèle with prescribed nonzero components, almost all of norm $1$. -/
theorem exists_idele_of_components {K : Type} [Field K] [NumberField K]
    (x : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K) (y : ∀ w : InfinitePlace K, w.Completion)
    (hx0 : ∀ w, x w ≠ 0) (hy0 : ∀ w, y w ≠ 0) (hx1 : ∀ᶠ w in Filter.cofinite, ‖x w‖ = 1) :
    ∃ j : IdeleGroup (𝓞 K) K, (∀ w, ideleAt j w = x w) ∧ ∀ w, ideleAtInf j w = y w := by
  have hint : ∀ᶠ w in Filter.cofinite, x w ∈ w.adicCompletionIntegers K :=
    hx1.mono fun w h => (norm_le_one_iff_mem w _).1 h.le
  let a : AdeleRing (𝓞 K) K := (y, ⟨x, hint⟩)
  have ha : IsUnit a := by
    rw [AdeleRing.isUnit_iff]
    exact ⟨hy0, hx0, hx1.mono fun w h => (norm_eq_one_iff_valued w _).1 h⟩
  exact ⟨ha.unit, fun w => rfl, fun w => rfl⟩

omit [Algebra.IsQuadraticExtension F E] hθ hs in
/-- Almost all components of an idèle have norm $1$. -/
lemma eventually_norm_ideleAt_eq_one {K : Type} [Field K] [NumberField K] (i : IdeleGroup (𝓞 K) K) :
    ∀ᶠ v in Filter.cofinite, ‖ideleAt i v‖ = 1 := by
  have := (AdeleRing.isUnit_iff.1 i.isUnit).2.2
  exact this.mono fun v h => (norm_eq_one_iff_valued v _).2 h

omit [Algebra.IsQuadraticExtension F E] hθ hs in
/-- Finitely many finite spots of $E$ lie over a finite set of spots of $F$. -/
lemma finite_preimage_spotBelow {T : Set (HeightOneSpectrum (𝓞 F))} (hT : T.Finite) :
    (spotBelow (F := F) (E := E) ⁻¹' T).Finite := by
  refine hT.preimage' fun v _ => ?_
  have : spotBelow (F := F) (E := E) ⁻¹' {v} ⊆ Set.range (fun w : SpotsOver E v => w.1) := by
    intro w hw
    have hv : spotBelow w = v := hw
    subst hv
    exact ⟨⟨w, inferInstance⟩, rfl⟩
  exact (Set.finite_range _).subset this

omit [Algebra.IsQuadraticExtension F E] hθ hs in
lemma localNormFin_eq_ideleAt_congr (i : IdeleGroup (𝓞 F) F) (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) {v v' : HeightOneSpectrum (𝓞 F)} (h : v = v') [w.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver v'.asIdeal] (hy : localNormFin v w y = ideleAt i v) :
    localNormFin v' w y = ideleAt i v' := by
  subst h; exact hy

omit [Algebra.IsQuadraticExtension F E] hθ hs in
lemma localNormInf_eq_ideleAtInf_congr (i : IdeleGroup (𝓞 F) F) (w : InfinitePlace E) (y : w.Completion)
    {v v' : InfinitePlace F} (h : v = v') [w.LiesOver v] [w.LiesOver v']
    (hy : localNormInf E v w y = ideleAtInf i v) : localNormInf E v' w y = ideleAtInf i v' := by
  subst h; exact hy

omit [Algebra.IsQuadraticExtension F E] hθ hs in
lemma prod_eq_single_of_card_eq_one {α M : Type*} [Fintype α] [CommMonoid M] (h : Fintype.card α = 1)
    (f : α → M) (a : α) : ∏ b, f b = f a := by
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.1 h.le
  exact Fintype.prod_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb

omit [Algebra.IsQuadraticExtension F E] hθ hs in
lemma comap_eq_of_liesOver (v : InfinitePlace F) (w : InfinitePlace E) [h : w.LiesOver v] :
    w.comap (algebraMap F E) = v := by
  obtain ⟨h⟩ := h
  apply Subtype.ext
  exact h

/-- **The "incidentally" of Example 65:2** (O'Meara 1963, p. 177): if $i$ is a local norm at every spot with
$n_\mathfrak p = 2$, then $i = N_{E/F}\mathfrak J$ for an idèle $\mathfrak J$ with
$\lvert\mathfrak J_\mathfrak P\rvert_\mathfrak P$ equal to $\lvert i_\mathfrak p\rvert_\mathfrak p$ or $1$ whenever
$\mathfrak P \mid \mathfrak p$ (finite spots). -/
@[kb "omeara1963" "§65A, 65:2, p. 177 (the idèle 𝔍 constructed has |𝔍_𝔓|_𝔓 = |𝔦_𝔭|_𝔭 or 1)"]
theorem exists_ideleNorm_eq (i : IdeleGroup (𝓞 F) F)
    (hfin : ∀ v (w : SpotsOver E v), Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 →
      IsLocalNormIdeleAt E i v)
    (hinf : ∀ v (w : InfSpotsOver E v), Module.finrank v.Completion w.1.Completion = 2 →
      IsLocalNormIdeleAtInf E i v) :
    ∃ j : IdeleGroup (𝓞 E) E, ideleNorm j = i ∧
      ∀ w, ‖ideleAt j w‖ = ‖ideleAt i (spotBelow w)‖ ∨ ‖ideleAt j w‖ = 1 := by
  classical
  -- local preimages at every spot
  have hlocF : ∀ v (w : SpotsOver E v), ∃ y, localNormFin v w.1 y = ideleAt i v := by
    intro v w
    by_cases hv : IsSquare (algebraMap F (v.adicCompletion F) θ)
    · exact localNormFin_surjective_of_isSquare hθ hs v w.1 hv _
    · exact hfin v w ((finrank_eq_two_iff_not_isSquare hθ hs v w.1).2 hv) w
  have hlocI : ∀ v (w : InfSpotsOver E v), ∃ y, localNormInf E v w.1 y = ideleAtInf i v := by
    intro v w
    by_cases hv : IsSquare (algebraMap F v.Completion θ)
    · exact localNormInf_surjective_of_isSquare hθ hs v w.1 hv _
    · exact hinf v w ((finrank_eq_two_iff_not_isSquare_inf hθ hs v w.1).2 hv) w
  choose YF hYF using hlocF
  choose YI hYI using hlocI
  let wselF : ∀ v : HeightOneSpectrum (𝓞 F), SpotsOver E v := fun v => (nonempty_spotsOver hθ hs v).some
  let wselI : ∀ v : InfinitePlace F, InfSpotsOver E v := fun v => (nonempty_infSpotsOver E v).some
  have hI : ∀ w : InfinitePlace E, w.LiesOver (w.comap (algebraMap F E)) := fun w =>
    liesOver_of_comap_eq w _ rfl
  let x : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E := fun w =>
    if (wselF (spotBelow w)).1 = w then YF (spotBelow w) ⟨w, inferInstance⟩ else 1
  let y : ∀ w : InfinitePlace E, w.Completion := fun w =>
    if (wselI (w.comap (algebraMap F E))).1 = w then YI (w.comap (algebraMap F E)) ⟨w, hI w⟩ else 1
  have hYF0 : ∀ v (w : SpotsOver E v), YF v w ≠ 0 := fun v w h0 => by
    have := hYF v w; rw [h0, localNormFin_apply, Algebra.norm_zero] at this
    exact (idAtHom v i).ne_zero this.symm
  have hYI0 : ∀ v (w : InfSpotsOver E v), YI v w ≠ 0 := fun v w h0 => by
    have := hYI v w; rw [h0, localNormInf_apply, Algebra.norm_zero] at this
    exact (idAtInfHom v i).ne_zero this.symm
  have hx0 : ∀ w, x w ≠ 0 := fun w => by
    simp only [x]; split_ifs
    · exact hYF0 _ _
    · exact one_ne_zero
  have hy0 : ∀ w, y w ≠ 0 := fun w => by
    simp only [y]; split_ifs
    · exact hYI0 _ _
    · exact one_ne_zero
  have hxnorm : ∀ w, ‖x w‖ = ‖ideleAt i (spotBelow w)‖ ∨ ‖x w‖ = 1 := fun w => by
    simp only [x]; split_ifs
    · left; rw [← norm_localNormFin (spotBelow (F := F) w) w]
      exact congrArg norm (hYF (spotBelow w) ⟨w, inferInstance⟩)
    · right; exact norm_one
  have hx1 : ∀ᶠ w in Filter.cofinite, ‖x w‖ = 1 := by
    have hfinT : {v | ‖ideleAt i v‖ ≠ 1}.Finite := eventually_norm_ideleAt_eq_one i
    refine Filter.mem_of_superset (finite_preimage_spotBelow E hfinT).compl_mem_cofinite ?_
    intro w hw
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, not_not] at hw
    rcases hxnorm w with h | h
    · exact h.trans hw
    · exact h
  obtain ⟨j, hjF, hjI⟩ := exists_idele_of_components x y hx0 hy0 hx1
  refine ⟨j, ?_, fun w => by rw [hjF]; exact hxnorm w⟩
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext v
    show ideleAtInf (ideleNorm j) v = ideleAtInf i v
    rw [ideleAtInf_ideleNorm, Fintype.prod_eq_single (wselI v)]
    · have hw : (wselI v).1.comap (algebraMap F E) = v := comap_eq_of_liesOver E v (wselI v).1
      have hsel : (wselI ((wselI v).1.comap (algebraMap F E))).1 = (wselI v).1 := by rw [hw]
      rw [hjI]
      simp only [y]
      rw [if_pos hsel]
      exact localNormInf_eq_ideleAtInf_congr E i _ _ hw
        (hYI ((wselI v).1.comap (algebraMap F E)) ⟨(wselI v).1, hI _⟩)
    · intro w hw
      rw [hjI]
      simp only [y]
      have hw' : w.1.comap (algebraMap F E) = v := comap_eq_of_liesOver E v w.1
      rw [if_neg, map_one]
      intro h
      apply hw
      apply Subtype.ext
      rw [← h, hw']
  · apply RestrictedProduct.ext
    intro v
    show ideleAt (ideleNorm j) v = ideleAt i v
    rw [ideleAt_ideleNorm, Fintype.prod_eq_single (wselF v)]
    · have hw : v = spotBelow (wselF v).1 := eq_spotBelow_of_liesOver v (wselF v).1
      have hsel : (wselF (spotBelow (wselF v).1)).1 = (wselF v).1 := by rw [← hw]
      rw [hjF]
      simp only [x]
      rw [if_pos hsel]
      exact localNormFin_eq_ideleAt_congr E i _ _ hw.symm
        (hYF (spotBelow (wselF v).1) ⟨(wselF v).1, inferInstance⟩)
    · intro w hw
      rw [hjF]
      simp only [x]
      have hw' : v = spotBelow w.1 := eq_spotBelow_of_liesOver v w.1
      rw [if_neg, map_one]
      intro h
      apply hw
      apply Subtype.ext
      rw [← h, ← hw']

/-- **Example 65:2** (O'Meara 1963, p. 177): an idèle $i \in J_F$ is in $N_{E/F}J_E$ if and only if it is a local
norm at all $\mathfrak p$ for which $n_\mathfrak p = 2$ (finite and infinite spots). -/
@[kb "omeara1963" "§65A, 65:2, p. 177"]
theorem mem_range_ideleNorm_iff (i : IdeleGroup (𝓞 F) F) :
    i ∈ (ideleNorm (F := F) (E := E)).range ↔
      (∀ v (w : SpotsOver E v), Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 →
        IsLocalNormIdeleAt E i v) ∧
      (∀ v (w : InfSpotsOver E v), Module.finrank v.Completion w.1.Completion = 2 →
        IsLocalNormIdeleAtInf E i v) := by
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨fun v w h2 w' => ⟨ideleAt j w'.1, ?_⟩, fun v w h2 w' => ⟨ideleAtInf j w'.1, ?_⟩⟩
    · have hc : Fintype.card (SpotsOver E v) = 1 := by
        have := card_spotsOver_mul_finrank hθ hs v w
        rw [h2] at this; omega
      show localNormFin v w'.1 (ideleAt j w'.1) = ideleAt (ideleNorm j) v
      rw [ideleAt_ideleNorm, prod_eq_single_of_card_eq_one hc _ w']
    · have hc : Fintype.card (InfSpotsOver E v) = 1 := by
        have h := sum_finrank_infSpotsOver E v
        rw [Algebra.IsQuadraticExtension.finrank_eq_two,
          Finset.sum_congr rfl (fun u _ => ?_ : ∀ u ∈ (Finset.univ : Finset (InfSpotsOver E v)),
            Module.finrank v.Completion u.1.Completion = 2), Finset.sum_const, Finset.card_univ,
          smul_eq_mul] at h
        · omega
        · rw [finrank_eq_two_iff_not_isSquare_inf hθ hs v u.1, ← finrank_eq_two_iff_not_isSquare_inf hθ hs v w.1]
          exact h2
      show localNormInf E v w'.1 (ideleAtInf j w'.1) = ideleAtInf (ideleNorm j) v
      rw [ideleAtInf_ideleNorm, prod_eq_single_of_card_eq_one hc _ w']
  · rintro ⟨hfin, hinf⟩
    obtain ⟨j, hj, -⟩ := exists_ideleNorm_eq E hθ hs i hfin hinf
    exact ⟨j, hj⟩

/-- **Example 65:3** (O'Meara 1963, p. 177): $N_{E/F}J_E^S$ is the set of idèles $i \in J_F^S$ that are local norms
wherever $n_\mathfrak p = 2$. -/
@[kb "omeara1963" "§65A, 65:3, p. 177"]
theorem mem_map_sIdeles_iff (S : Set (HeightOneSpectrum (𝓞 F))) (i : IdeleGroup (𝓞 F) F) :
    i ∈ (sIdeles (spotsAbove (E := E) S)).map (ideleNorm (F := F) (E := E)) ↔
      i ∈ sIdeles S ∧
      (∀ v (w : SpotsOver E v), Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 2 →
        IsLocalNormIdeleAt E i v) ∧
      (∀ v (w : InfSpotsOver E v), Module.finrank v.Completion w.1.Completion = 2 →
        IsLocalNormIdeleAtInf E i v) := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨ideleNorm_mem_sIdeles S hj, (mem_range_ideleNorm_iff E hθ hs _).1 ⟨j, rfl⟩⟩
  · rintro ⟨hS, hfin, hinf⟩
    obtain ⟨j, hj, hjn⟩ := exists_ideleNorm_eq E hθ hs i hfin hinf
    refine ⟨j, fun w hw => ?_, hj⟩
    rw [← norm_eq_one_iff_valued]
    rcases hjn w with h | h
    · rw [h, norm_eq_one_iff_valued]; exact hS _ hw
    · exact h

end QuadFormsKB.OMeara
