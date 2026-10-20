/-
# Hasse norm theorem, step 5b: the auxiliary set $T$

For $S$ a finite set of primes and $a \in \mathcal O_F$ not a square, with $\langle a\rangle F_S^{\times 2}$ = `aSq`:

* `sqAt`, `ρ`, `index_sqAt_le`: reduction $F_S^\times \to \mathcal O_t^\times/\mathcal O_t^{\times2}$ ($t \notin S$, $t \nmid 2$), a group of
  order $2$;
* `exists_T`: a finite set $T$ of good primes ($t \notin S$, $t \nmid 2$, $a \in F_t^{\times2}$) such that the $S$-units
  that are squares at all $t \in T$ are exactly $\langle a\rangle F_S^{\times 2}$, with index $2^{|T|}$ (induction with
  `exists_new_good`, i.e. `exists_good_prime`);
* `ρT_surjective`: $F_S^\times \to \prod_{t \in T} \mathcal O_t^\times/\mathcal O_t^{\times 2}$ is onto (Milne VII, Lemma 6.9);
* `card_T_ge`: $|T| \ge r_\infty + |S| - 1$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.GoodPrimes

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

/-- The element of `F` underlying an `S`-unit (additive notation). -/
def toF {S : Finset (HeightOneSpectrum (𝓞 F))} (x : Additive (SUnit (F := F) S)) : F :=
  (((Additive.toMul x : SUnit S) : Fˣ) : F)

/-- `toF` is multiplicative. -/
@[simp] lemma toF_add {S : Finset (HeightOneSpectrum (𝓞 F))} (x y : Additive (SUnit (F := F) S)) :
    toF (x + y) = toF x * toF y := rfl
/-- `toF 0 = 1`. -/
@[simp] lemma toF_zero {S : Finset (HeightOneSpectrum (𝓞 F))} : toF (0 : Additive (SUnit (F := F) S)) = 1 := rfl
/-- `toF (-x) = (toF x)⁻¹`. -/
@[simp] lemma toF_neg {S : Finset (HeightOneSpectrum (𝓞 F))} (x : Additive (SUnit (F := F) S)) :
    toF (-x) = (toF x)⁻¹ := by
  simp [toF, toMul_neg, Units.val_inv_eq_inv_val]
/-- `S`-units are nonzero. -/
lemma toF_ne_zero {S : Finset (HeightOneSpectrum (𝓞 F))} (x : Additive (SUnit (F := F) S)) :
    toF x ≠ 0 := Units.ne_zero _

/-- The `S`-units that are squares in `F_t`. -/
def sqAt (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) :
    AddSubgroup (Additive (SUnit (F := F) S)) where
  carrier := {x | IsSquare (algebraMap F (t.adicCompletion F) (toF x))}
  zero_mem' := ⟨1, by simp⟩
  add_mem' {x y} hx hy := by
    obtain ⟨u, hu⟩ := hx; obtain ⟨w, hw⟩ := hy
    exact ⟨u * w, by simp only [Set.mem_ofPred_eq, toF_add, map_mul, hu, hw]; ring⟩
  neg_mem' {x} hx := by
    obtain ⟨u, hu⟩ := hx
    exact ⟨u⁻¹, by simp only [Set.mem_ofPred_eq, toF_neg, map_inv₀, hu, mul_inv]⟩

/-- Membership in `sqAt`. -/
lemma mem_sqAt {S : Finset (HeightOneSpectrum (𝓞 F))} {t : HeightOneSpectrum (𝓞 F)}
    {x : Additive (SUnit (F := F) S)} :
    x ∈ sqAt S t ↔ IsSquare (algebraMap F (t.adicCompletion F) (toF x)) := Iff.rfl


/-- An `S`-unit is a unit of $\mathcal O_t$ for $t \notin S$. -/
def unitAtHom (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) (ht : t ∉ S) :
    SUnit (F := F) S →* U0 t where
  toFun x := ⟨Units.map (algebraMap F (t.adicCompletion F) : F →* t.adicCompletion F) (x : Fˣ), by
    rw [mem_U0]
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [valued_algebraMap]
    exact x.2 t (by simpa using ht)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/-- Reduction of `S`-units to $\mathcal O_t^\times/\mathcal O_t^{\times 2}$ ($t \notin S$). -/
def ρ (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) (ht : t ∉ S) :
    SUnit (F := F) S →* (U0 t ⧸ (powMonoidHom 2 : U0 t →* U0 t).range) :=
  (QuotientGroup.mk' _).comp (unitAtHom S t ht)

/-- The kernel of `ρ` is `sqAt`. -/
lemma ρ_ker (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) (ht : t ∉ S) :
    Subgroup.toAddSubgroup (ρ S t ht).ker = sqAt S t := by
  ext x
  change Additive.toMul x ∈ (ρ S t ht).ker ↔ x ∈ sqAt S t
  rw [MonoidHom.mem_ker, mem_sqAt]
  simp only [ρ, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply]
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨((y : U0 t) : (t.adicCompletion F)ˣ), ?_⟩
    have := congrArg (fun z : U0 t => (((z : (t.adicCompletion F)ˣ)) : t.adicCompletion F)) hy
    simp only [powMonoidHom_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val] at this
    rw [← pow_two, this]
    rfl
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp only [mul_zero, map_eq_zero_iff _ (algebraMap F _).injective] at hr
      exact toF_ne_zero x hr
    have hrv : Valued.v r = 1 := by
      have h1 : Valued.v (algebraMap F (t.adicCompletion F) (toF x)) = 1 := by
        rw [valued_algebraMap]; exact (Additive.toMul x).2 t (by simpa using ht)
      rw [hr, map_mul] at h1
      exact eq_one_of_pow_eq_one two_ne_zero (by rw [pow_two]; exact h1)
    refine ⟨⟨Units.mk0 r hr0, (mem_U0 t).mpr hrv⟩, ?_⟩
    apply Subtype.ext; apply Units.ext
    simp only [powMonoidHom_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [pow_two, ← hr]
    rfl

/-- $[\mathcal O_t^\times : \mathcal O_t^{\times 2}] = 2$ for $t \nmid 2$. -/
lemma index_sq_U0_of_not_dvd (t : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ t.asIdeal) :
    (powMonoidHom 2 : U0 t →* U0 t).range.index = 2 := by
  rw [index_sq_U0]
  have : ordTwo t = 0 := by
    have e := HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity t (two_ne_zero : (2 : 𝓞 F) ≠ 0)
    rw [(HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl t 2).mpr h2, ← exp_zero,
      exp_inj] at e
    unfold ordTwo; omega
  rw [this, pow_zero, mul_one]

/-- **$[F_S^\times : F_S^\times \cap F_t^{\times 2}] \le 2$** for $t \notin S$ non-dyadic. -/
lemma index_sqAt_le (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) (ht : t ∉ S)
    (h2 : (2 : 𝓞 F) ∉ t.asIdeal) : (sqAt S t).index ≤ 2 := by
  rw [← ρ_ker S t ht, Subgroup.index_toAddSubgroup, Subgroup.index_ker]
  have hfin : Finite (U0 t ⧸ (powMonoidHom 2 : U0 t →* U0 t).range) := by
    apply Nat.finite_of_card_ne_zero
    rw [← Subgroup.index, index_sq_U0_of_not_dvd t h2]; norm_num
  calc Nat.card (ρ S t ht).range ≤ Nat.card (U0 t ⧸ (powMonoidHom 2 : U0 t →* U0 t).range) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := index_sq_U0_of_not_dvd t h2


/-- `sqAt` has finite index. -/
lemma index_sqAt_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F))
    (ht : t ∉ S) : (sqAt S t).index ≠ 0 := by
  rw [← ρ_ker S t ht, Subgroup.index_toAddSubgroup, Subgroup.index_ker]
  have : Finite (U0 t ⧸ (powMonoidHom 2 : U0 t →* U0 t).range) := by
    apply Nat.finite_of_card_ne_zero
    rw [← Subgroup.index, index_sq_U0]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero t.ne_bot)))
  exact Nat.card_pos.ne'

/-- The subgroup $\langle a \rangle F_S^{\times 2}$ (additive notation): $S$-units $x$ with $x$ or $ax$ a square. -/
def aSq (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0) :
    AddSubgroup (Additive (SUnit (F := F) S)) where
  carrier := {x | IsSquare (toF x) ∨ IsSquare (a * toF x)}
  zero_mem' := Or.inl ⟨1, by simp⟩
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, toF_add] at hx hy ⊢
    rcases hx with ⟨u, hu⟩ | ⟨u, hu⟩ <;> rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨u * w, by rw [hu, hw]; ring⟩
    · exact Or.inr ⟨u * w, by rw [← mul_assoc, mul_comm a, mul_assoc, hw, hu]; ring⟩
    · exact Or.inr ⟨u * w, by rw [← mul_assoc, hu, hw]; ring⟩
    · refine Or.inl ⟨u * w / a, ?_⟩
      field_simp
      linear_combination (toF y * a) * hu + (u * u) * hw
  neg_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, toF_neg] at hx ⊢
    have hx0 := toF_ne_zero x
    rcases hx with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact Or.inl ⟨u⁻¹, by rw [hu, mul_inv]⟩
    · refine Or.inr ⟨u / toF x, ?_⟩
      field_simp
      linear_combination hu


/-- The $S$-units that are squares at every $t \in T$. -/
def kerT (S T : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (Additive (SUnit (F := F) S)) where
  carrier := {x | ∀ t ∈ T, x ∈ sqAt S t}
  zero_mem' t _ := zero_mem _
  add_mem' hx hy t ht := add_mem (hx t ht) (hy t ht)
  neg_mem' hx t ht := neg_mem (hx t ht)

/-- `kerT S ∅ = ⊤`. -/
lemma kerT_empty (S : Finset (HeightOneSpectrum (𝓞 F))) : kerT S ∅ = ⊤ := by
  ext x; simp [kerT]

open scoped Classical in
/-- `kerT` of an insertion. -/
lemma kerT_insert (S T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F)) :
    kerT S (insert t T) = kerT S T ⊓ sqAt S t := by
  classical
  ext x
  simp only [kerT, AddSubgroup.mem_mk, AddSubgroup.mem_inf, Finset.mem_insert]
  constructor
  · intro h; exact ⟨fun t' ht' => h t' (Or.inr ht'), h t (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ t' (rfl | ht')
    · exact h2
    · exact h1 t' ht'

/-- Good primes for `T`: outside `S`, non-dyadic, and `a` is a square there. -/
def GoodT (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (T : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ t ∈ T, t ∉ S ∧ (2 : 𝓞 F) ∉ t.asIdeal ∧ IsSquare (algebraMap F (t.adicCompletion F) a)

/-- $\langle a\rangle F_S^{\times 2}$ consists of squares wherever $a$ is a square. -/
lemma aSq_le_sqAt (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0)
    (t : HeightOneSpectrum (𝓞 F)) (hat : IsSquare (algebraMap F (t.adicCompletion F) a)) :
    aSq S a ha ≤ sqAt S t := by
  intro x hx
  rw [mem_sqAt]
  rcases hx with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact ⟨algebraMap F _ u, by rw [hu, map_mul]⟩
  · obtain ⟨r, hr⟩ := hat
    have hr0 : r ≠ 0 := by
      rintro rfl; simp [map_eq_zero_iff _ (algebraMap F _).injective] at hr; exact ha hr
    refine ⟨algebraMap F _ u / r, ?_⟩
    have : algebraMap F (t.adicCompletion F) (toF x) =
        algebraMap F _ (a * toF x) / algebraMap F _ a := by
      rw [map_mul]; field_simp [show algebraMap F (t.adicCompletion F) a ≠ 0 by
        rw [hr]; exact mul_ne_zero hr0 hr0]
    rw [this, hu, map_mul, hr]; field_simp

/-- $\langle a\rangle F_S^{\times 2} \le$ `kerT` for good `T`. -/
lemma aSq_le_kerT (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : GoodT S a T) : aSq S a ha ≤ kerT S T :=
  fun x hx t ht => aSq_le_sqAt S a ha t (hT t ht).2.2 hx


open scoped Classical in
/-- **Induction step for `T`:** an $S$-unit $x \in \ker_T \setminus \langle a\rangle F_S^{\times 2}$ is not a square at
some new good prime. -/
lemma exists_new_good (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) {L : Type} [Field L] [NumberField L]
    [Algebra F L] (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (S T : Finset (HeightOneSpectrum (𝓞 F))) (ha0 : (a : F) ≠ 0)
    (x : Additive (SUnit (F := F) S)) (hxA : x ∉ aSq S (a : F) ha0) :
    ∃ t : HeightOneSpectrum (𝓞 F), t ∉ T ∧ t ∉ S ∧ (2 : 𝓞 F) ∉ t.asIdeal ∧
      IsSquare (algebraMap F (t.adicCompletion F) a) ∧ x ∉ sqAt S t := by
  obtain ⟨n, d, hdmem, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (toF x)
  have hd0 : (d : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdmem
  set xO : 𝓞 F := n * d
  have hxO : (xO : F) = toF x * (d : F) ^ 2 := by
    simp only [xO, map_mul]
    change (n : F) * (d : F) = _
    rw [← hnd]; field_simp
  have hxA' : ¬ IsSquare (toF x) ∧ ¬ IsSquare ((a : F) * toF x) := by
    have : ¬ (IsSquare (toF x) ∨ IsSquare ((a : F) * toF x)) := hxA
    exact not_or.mp this
  have hx' : ¬ IsSquare (xO : F) := by
    rintro ⟨r, hr⟩
    apply hxA'.1
    refine ⟨r / d, ?_⟩
    have : toF x = (xO : F) / (d : F) ^ 2 := by rw [hxO]; field_simp
    rw [this, hr]; field_simp
  have hax' : ¬ IsSquare ((a : F) * xO) := by
    rintro ⟨r, hr⟩
    apply hxA'.2
    refine ⟨r / d, ?_⟩
    have : (a : F) * toF x = (a : F) * xO / (d : F) ^ 2 := by rw [hxO]; field_simp
    rw [this, hr]; field_simp
  obtain ⟨t, htB, h2ax, hat, hxt⟩ := exists_good_prime a hd s hs hspan xO hx' hax' (S ∪ T)
  refine ⟨t, fun h => htB (Finset.mem_union_right _ h), fun h => htB (Finset.mem_union_left _ h),
    ?_, hat, ?_⟩
  · intro h; apply h2ax
    exact t.asIdeal.mul_mem_right _ (t.asIdeal.mul_mem_right _ h)
  · intro hsq
    apply hxt
    obtain ⟨r, hr⟩ := (mem_sqAt).mp hsq
    refine ⟨r * algebraMap F _ (d : F), ?_⟩
    rw [hxO, map_mul, hr, map_pow]; ring


/-- $F_S^{\times 2} \le \langle a\rangle F_S^{\times 2}$. -/
lemma two_le_aSq (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0) :
    (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).range ≤ aSq S a ha := by
  rintro _ ⟨y, rfl⟩
  exact Or.inl ⟨toF y, by simp [two_nsmul]⟩

/-- $\langle a\rangle F_S^{\times 2}$ has finite index. -/
lemma index_aSq_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0) :
    (aSq S a ha).index ≠ 0 := by
  intro h
  have := AddSubgroup.index_dvd_of_le (two_le_aSq S a ha)
  rw [h, zero_dvd_iff, index_sq_sUnit] at this
  exact pow_ne_zero _ two_ne_zero this

open scoped Classical in
/-- **Choice of $T$** (Milne VII, Lemmas 6.2 and 6.9 for $n = 2$): a finite set $T$ of good primes (outside
$S$, non-dyadic, $a$ a square there) such that an $S$-unit is a square at every $t \in T$ iff it lies in
$\langle a \rangle F_S^{\times 2}$, and $[F_S^\times : \langle a\rangle F_S^{\times 2}] = 2^{|T|}$. -/
@[kb "milne2020cft" "Ch. VII, Lemmas 6.2, 6.9 (n = 2) [unverified]"]
theorem exists_T (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) {L : Type} [Field L] [NumberField L]
    [Algebra F L] (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (ha0 : (a : F) ≠ 0) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), GoodT S (a : F) T ∧ kerT S T = aSq S (a : F) ha0 ∧
      (kerT S T).index = 2 ^ T.card := by
  set A := aSq S (a : F) ha0
  have hA0 := index_aSq_ne_zero S (a : F) ha0
  suffices H : ∀ n : ℕ, ∀ T : Finset (HeightOneSpectrum (𝓞 F)), GoodT S (a : F) T →
      (kerT S T).index = 2 ^ T.card → A.relIndex (kerT S T) = n →
      ∃ T' : Finset (HeightOneSpectrum (𝓞 F)), GoodT S (a : F) T' ∧ kerT S T' = A ∧
        (kerT S T').index = 2 ^ T'.card by
    exact H _ ∅ (fun t ht => by simp at ht) (by rw [kerT_empty]; simp) rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT hidx hn
    have hAT := aSq_le_kerT S (a : F) ha0 T hT
    by_cases heq : kerT S T = A
    · exact ⟨T, hT, heq, hidx⟩
    obtain ⟨x, hxK, hxA⟩ : ∃ x ∈ kerT S T, x ∉ A := by
      by_contra hc; push Not at hc
      exact heq (le_antisymm hc hAT)
    obtain ⟨t, htT, htS, ht2, hat, hxt⟩ := exists_new_good a hd s hs hspan S T ha0 x hxA
    set T' := insert t T
    have hT' : GoodT S (a : F) T' := by
      intro t' ht'
      rcases Finset.mem_insert.mp ht' with rfl | h
      · exact ⟨htS, ht2, hat⟩
      · exact hT t' h
    have hK' : kerT S T' = kerT S T ⊓ sqAt S t := kerT_insert S T t
    -- the relative index of the new kernel is 2
    have hrel : (sqAt S t).relIndex (kerT S T) = 2 := by
      have hdvd := AddSubgroup.relIndex_dvd_index_of_normal (sqAt S t) (kerT S T)
      have hle := index_sqAt_le S t htS ht2
      have hne0 := index_sqAt_ne_zero S t htS
      have h1 : (sqAt S t).relIndex (kerT S T) ≠ 1 := by
        rw [Ne, AddSubgroup.relIndex_eq_one]
        intro h; exact hxt (h hxK)
      have h0 : (sqAt S t).relIndex (kerT S T) ≠ 0 := by
        intro h; rw [h, zero_dvd_iff] at hdvd; exact hne0 hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hdvd
      omega
    have hrel' : (kerT S T').relIndex (kerT S T) = 2 := by
      rw [hK', AddSubgroup.relIndex, AddSubgroup.inf_addSubgroupOf_left, ← AddSubgroup.relIndex, hrel]
    have hidx' : (kerT S T').index = 2 ^ T'.card := by
      have := AddSubgroup.relIndex_mul_index (show kerT S T' ≤ kerT S T by rw [hK']; exact inf_le_left)
      rw [hrel', hidx] at this
      rw [← this, Finset.card_insert_of_notMem htT, pow_succ]; ring
    have hAT' : A ≤ kerT S T' := aSq_le_kerT S (a : F) ha0 T' hT'
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hAT'
      (show kerT S T' ≤ kerT S T by rw [hK']; exact inf_le_left)
    rw [hrel', hn] at hmul
    have hn0 : n ≠ 0 := by
      intro h0; rw [← hn] at h0
      have := AddSubgroup.relIndex_mul_index hAT
      rw [h0, zero_mul] at this; exact hA0 this.symm
    exact ih (A.relIndex (kerT S T')) (by omega) T' hT' hidx' rfl


/-- The reduction map to $\prod_{t \in T} \mathcal O_t^\times/\mathcal O_t^{\times 2}$. -/
def ρT (S T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ t ∈ T, t ∉ S) :
    SUnit (F := F) S →* ((t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) where
  toFun x t := ρ S t.1 (hT t.1 t.2) x
  map_one' := by funext t; exact (ρ S t.1 (hT t.1 t.2)).map_one
  map_mul' x y := by funext t; exact (ρ S t.1 (hT t.1 t.2)).map_mul x y

/-- The kernel of `ρT` is `kerT`. -/
lemma ρT_ker (S T : Finset (HeightOneSpectrum (𝓞 F))) (hT : ∀ t ∈ T, t ∉ S) :
    Subgroup.toAddSubgroup (ρT S T hT).ker = kerT S T := by
  ext x
  change Additive.toMul x ∈ (ρT S T hT).ker ↔ x ∈ kerT S T
  rw [MonoidHom.mem_ker]
  simp only [kerT, AddSubgroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · intro h t ht
    have := congrFun h ⟨t, ht⟩
    rw [← ρ_ker S t (hT t ht)]
    exact (MonoidHom.mem_ker).mpr this
  · intro h
    funext t
    have := h t.1 t.2
    rw [← ρ_ker S t.1 (hT t.1 t.2)] at this
    exact (MonoidHom.mem_ker).mp this

/-- **The $T$-reduction is onto** (Milne VII, Lemma 6.9): every family of units at $t \in T$ is congruent
mod squares to a single $S$-unit. -/
theorem ρT_surjective (S T : Finset (HeightOneSpectrum (𝓞 F))) (a : F)
    (hT : GoodT S a T) (hidx : (kerT S T).index = 2 ^ T.card) :
    Function.Surjective (ρT S T fun t ht => (hT t ht).1) := by
  classical
  set f := ρT S T fun t ht => (hT t ht).1
  have hfin : ∀ t : T, Nat.card (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range) = 2 :=
    fun t => index_sq_U0_of_not_dvd t.1 (hT t.1 t.2).2.1
  have hfinite : ∀ t : T, Finite (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range) :=
    fun t => Nat.finite_of_card_ne_zero (by rw [hfin]; norm_num)
  have hcardT : Nat.card ((t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) =
      2 ^ T.card := by
    rw [Nat.card_pi, Finset.prod_congr rfl (fun t _ => hfin t), Finset.prod_const,
      Finset.card_univ, Fintype.card_coe]
  have hrange : Nat.card (MonoidHom.range (G := SUnit (F := F) S)
      (N := (t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) f) = 2 ^ T.card := by
    rw [← Subgroup.index_ker, ← Subgroup.index_toAddSubgroup, ρT_ker, hidx]
  have htop : MonoidHom.range (G := SUnit (F := F) S)
      (N := (t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) f = ⊤ := by
    have : Finite ((t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) := Pi.finite
    apply Subgroup.eq_top_of_card_eq
    rw [hrange, hcardT]
  intro y
  have : y ∈ MonoidHom.range (G := SUnit (F := F) S)
      (N := (t : T) → (U0 t.1 ⧸ (powMonoidHom 2 : U0 t.1 →* U0 t.1).range)) f :=
    htop ▸ Subgroup.mem_top y
  exact this

/-- A square root of an `S`-unit is an `S`-unit. -/
lemma sqrt_mem_sUnit (S : Finset (HeightOneSpectrum (𝓞 F))) (r : Fˣ) (hr : r ^ 2 ∈ SUnit (F := F) S) :
    r ∈ SUnit (F := F) S := by
  intro p hp
  have := hr p hp
  simp only [Units.val_pow_eq_pow_val, map_pow] at this
  exact eq_one_of_pow_eq_one two_ne_zero this


/-- $[\langle a\rangle F_S^{\times2} : F_S^{\times 2}] \le 2$ when $a \in F_S^\times$. -/
lemma relIndex_two_aSq_le (S : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0)
    (aS : SUnit (F := F) S) (haS : ((aS : Fˣ) : F) = a) :
    (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).range.relIndex (aSq S a ha) ≤ 2 := by
  classical
  set A := aSq S a ha
  set K := (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).range
  have hsq : ∀ x : Additive (SUnit (F := F) S), IsSquare (toF x) → x ∈ K := by
    intro x ⟨r, hr⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact toF_ne_zero x hr
    have hrS : Units.mk0 r hr0 ∈ SUnit (F := F) S := by
      apply sqrt_mem_sUnit
      have : (Units.mk0 r hr0) ^ 2 = ((Additive.toMul x : SUnit S) : Fˣ) := by
        ext; simp [pow_two, ← hr, toF]
      rw [this]; exact (Additive.toMul x).2
    refine ⟨Additive.ofMul ⟨Units.mk0 r hr0, hrS⟩, ?_⟩
    apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
    simp [two_nsmul, toF] at hr ⊢
    rw [← hr]
  have haA : Additive.ofMul aS ∈ A := Or.inr ⟨a, by simp [toF, haS]⟩
  let g : Bool → A ⧸ K.addSubgroupOf A := fun b =>
    if b then QuotientAddGroup.mk ⟨Additive.ofMul aS, haA⟩ else 0
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    rcases hx with hx | hx
    · refine ⟨false, ?_⟩
      simp only [g, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact hsq x hx
    · refine ⟨true, ?_⟩
      simp only [g, ↓reduceIte]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      apply hsq
      obtain ⟨r, hr⟩ := hx
      refine ⟨r / a, ?_⟩
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, toF_add, toF_neg]
      have : toF (Additive.ofMul aS) = a := by simp [toF, haS]
      rw [this]
      field_simp
      linear_combination hr
  rw [AddSubgroup.relIndex]
  calc (K.addSubgroupOf A).index = Nat.card (A ⧸ K.addSubgroupOf A) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective g hg
    _ = 2 := by simp

/-- With `T` from `exists_T`: $|T| \ge r_\infty + |S| - 1$ (`Units.rank F` $= r_\infty - 1$). -/
lemma card_T_ge (S T : Finset (HeightOneSpectrum (𝓞 F))) (a : F) (ha : a ≠ 0)
    (aS : SUnit (F := F) S) (haS : ((aS : Fˣ) : F) = a)
    (hker : kerT S T = aSq S a ha) (hidx : (kerT S T).index = 2 ^ T.card) :
    Units.rank F + S.card ≤ T.card := by
  have h1 := AddSubgroup.relIndex_mul_index (two_le_aSq S a ha)
  rw [index_sq_sUnit, ← hker, hidx] at h1
  rw [hker] at h1
  have h2 := relIndex_two_aSq_le S a ha aS haS
  have : 2 ^ (Units.rank F + S.card + 1) ≤ 2 ^ (T.card + 1) := by
    rw [← h1, pow_succ 2 T.card, mul_comm (2 ^ T.card) 2]
    exact Nat.mul_le_mul_right _ h2
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
  omega

end QuadFormsKB.HN

end
