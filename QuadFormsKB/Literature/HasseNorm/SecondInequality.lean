/-
# Hasse norm theorem, step 5d: the second inequality, counted

With $S' = S \cup T$:

* `locNorms L S S'`: $S'$-units that are local norms from $L$ at every $v \in S$ and every infinite place;
  `locSq S S'`: those that are local squares there;
* `relIndex_locSq_le`: $[\,\text{locNorms} : \text{locSq}\,] \le \prod_v [N_v : F_v^{\times 2}]$;
* `two_pow_le_index_locNorms`: $[F_{S'}^\times : \text{locNorms}] \ge 2^{s'-1}$, $s'$ the number of non-split places in
  $S \cup \infty$, given that locSq consists of global squares (Prop. 6.10) and $|T| \ge r_\infty - 1 + |S|$.

Proof of the last: $\text{locSq} = F_{S'}^{\times 2}$ has index $2^{r_\infty + |S'|}$ (`index_sq_sUnit`), the local square
indices multiply to $4^{|S| + r_\infty}$ (`prod_index_sq`), and $[F_v^\times : N_v] \ge 2$ at non-split $v$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.KummerSquares
import QuadFormsKB.Literature.LocalGlobal.HasseNormQuadratic

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

/-- The index of a kernel is at most the size of a finite target. -/
lemma index_ker_le {G H : Type*} [Group G] [Group H] [Finite H] (f : G →* H) :
    f.ker.index ≤ Nat.card H := by
  rw [Subgroup.index_ker]
  exact Nat.card_le_card_of_injective _ Subtype.val_injective

/-- Scaling by a square does not change the Hilbert symbol. -/
lemma hilbertSymbol_mul_sq_left (K : Type*) [Field K] (a b d : K) (hd : d ≠ 0) :
    hilbertSymbol K (a * d ^ 2) b = hilbertSymbol K a b := by
  unfold hilbertSymbol
  congr 1
  apply propext
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x * d, y, z, ?_, by rw [h]; ring⟩
    intro h0; apply hne
    simp only [Prod.mk_eq_zero, mul_eq_zero, hd, or_false] at h0 ⊢
    exact h0
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x / d, y, z, ?_, by rw [h]; field_simp⟩
    intro h0; apply hne
    simp only [Prod.mk_eq_zero, div_eq_zero_iff, hd, or_false] at h0 ⊢
    exact h0

/-- A norm $b = b_0^2 - a b_1^2$ has $(a,b)_F = 1$. -/
lemma hilbertSymbol_eq_one_of_norm (K : Type*) [Field K] (a b b₀ b₁ : K) (h : b = b₀ ^ 2 - a * b₁ ^ 2) :
    hilbertSymbol K a b = 1 := by
  unfold hilbertSymbol
  exact if_pos ⟨b₁, 1, b₀, fun h0 => by simp [Prod.ext_iff] at h0, by rw [h]; ring⟩


section Count

variable {F : Type} [Field F] [NumberField F]

/-- $F_{S'}^\times \to F_v^\times$. -/
def Φf (S' : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    SUnit (F := F) S' →* (v.adicCompletion F)ˣ where
  toFun x := Units.map (algebraMap F (v.adicCompletion F) : F →* v.adicCompletion F) (x : Fˣ)
  map_one' := by simp
  map_mul' x y := by simp

/-- $F_{S'}^\times \to F_w^\times$ at an infinite place. -/
def Φi (S' : Finset (HeightOneSpectrum (𝓞 F))) (w : InfinitePlace F) :
    SUnit (F := F) S' →* (w.Completion)ˣ where
  toFun x := Units.map (algebraMap F w.Completion : F →* w.Completion) (x : Fˣ)
  map_one' := by simp
  map_mul' x y := by simp

/-- The squares of a unit group. -/
abbrev sqG (M : Type*) [CommGroup M] : Subgroup M := (powMonoidHom 2 : M →* M).range

/-- The $S'$-units that are local norms from $L$ at every $v \in S$ and every infinite place. -/
def locNorms (L : Type) [Field L] [Algebra F L] (S S' : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup (SUnit (F := F) S') :=
  (⨅ v : S, (normGroup (F := F) L (v.1.adicCompletion F)).comap (Φf S' v.1)) ⊓
    (⨅ w : InfinitePlace F, (normGroup (F := F) L w.Completion).comap (Φi S' w))

/-- The $S'$-units that are local squares at every $v \in S$ and every infinite place. -/
def locSq (S S' : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (SUnit (F := F) S') :=
  (⨅ v : S, (sqG (v.1.adicCompletion F)ˣ).comap (Φf S' v.1)) ⊓
    (⨅ w : InfinitePlace F, (sqG (w.Completion)ˣ).comap (Φi S' w))


/-- Membership in `locNorms`. -/
lemma mem_locNorms {L : Type} [Field L] [Algebra F L] {S S' : Finset (HeightOneSpectrum (𝓞 F))}
    {x : SUnit (F := F) S'} :
    x ∈ locNorms L S S' ↔ (∀ v : S, Φf S' v.1 x ∈ normGroup (F := F) L (v.1.adicCompletion F)) ∧
      ∀ w : InfinitePlace F, Φi S' w x ∈ normGroup (F := F) L w.Completion := by
  simp [locNorms, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- Membership in `locSq`. -/
lemma mem_locSq {S S' : Finset (HeightOneSpectrum (𝓞 F))} {x : SUnit (F := F) S'} :
    x ∈ locSq S S' ↔ (∀ v : S, Φf S' v.1 x ∈ sqG (v.1.adicCompletion F)ˣ) ∧
      ∀ w : InfinitePlace F, Φi S' w x ∈ sqG (w.Completion)ˣ := by
  simp [locSq, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- **$[A : B] \le \prod_v [N_v : F_v^{\times 2}]$** for the local-norm and local-square subgroups. -/
theorem relIndex_locSq_le (L : Type) [Field L] [Algebra F L] (S S' : Finset (HeightOneSpectrum (𝓞 F)))
    (_hsqf : ∀ v : HeightOneSpectrum (𝓞 F), sqG (v.adicCompletion F)ˣ ≤ normGroup (F := F) L (v.adicCompletion F))
    (_hsqi : ∀ w : InfinitePlace F, sqG (w.Completion)ˣ ≤ normGroup (F := F) L w.Completion)
    (hfinf : ∀ v : HeightOneSpectrum (𝓞 F),
      (sqG (v.adicCompletion F)ˣ).relIndex (normGroup (F := F) L (v.adicCompletion F)) ≠ 0)
    (hfini : ∀ w : InfinitePlace F, (sqG (w.Completion)ˣ).relIndex (normGroup (F := F) L w.Completion) ≠ 0) :
    (locSq S S').relIndex (locNorms L S S') ≤
      (∏ v : S, (sqG (v.1.adicCompletion F)ˣ).relIndex (normGroup (F := F) L (v.1.adicCompletion F))) *
        ∏ w : InfinitePlace F, (sqG (w.Completion)ˣ).relIndex (normGroup (F := F) L w.Completion) := by
  classical
  set A := locNorms L S S'
  set B := locSq S S'
  let Hf : S → Type := fun v => (normGroup (F := F) L (v.1.adicCompletion F)) ⧸
    (sqG (v.1.adicCompletion F)ˣ).subgroupOf (normGroup (F := F) L (v.1.adicCompletion F))
  let Hi : InfinitePlace F → Type := fun w => (normGroup (F := F) L w.Completion) ⧸
    (sqG (w.Completion)ˣ).subgroupOf (normGroup (F := F) L w.Completion)
  have hHf : ∀ v : S, Finite (Hf v) := fun v => Nat.finite_of_card_ne_zero (hfinf v.1)
  have hHi : ∀ w, Finite (Hi w) := fun w => Nat.finite_of_card_ne_zero (hfini w)
  let f : A → ((v : S) → Hf v) × ((w : InfinitePlace F) → Hi w) := fun x =>
    (fun v => QuotientGroup.mk ⟨Φf S' v.1 x, (mem_locNorms.mp x.2).1 v⟩,
      fun w => QuotientGroup.mk ⟨Φi S' w x, (mem_locNorms.mp x.2).2 w⟩)
  have hf : ∀ x y : A, f x = f y ↔ x⁻¹ * y ∈ B.subgroupOf A := by
    intro x y
    rw [Subgroup.mem_subgroupOf, mem_locSq, Prod.ext_iff, funext_iff, funext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v => ?_, fun w => ?_⟩
      · have := h1 v
        simp only [f] at this
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
        simpa [map_mul, map_inv] using this
      · have := h2 w
        simp only [f] at this
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
        simpa [map_mul, map_inv] using this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v => ?_, fun w => ?_⟩
      · simp only [f]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [map_mul, map_inv] using h1 v
      · simp only [f]
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [map_mul, map_inv] using h2 w
  let g : A ⧸ B.subgroupOf A → ((v : S) → Hf v) × ((w : InfinitePlace F) → Hi w) :=
    Quotient.lift f (fun x y hxy => (hf x y).mpr (QuotientGroup.leftRel_apply.mp hxy))
  have hg : Function.Injective g := by
    intro p q hpq
    induction p using Quotient.inductionOn with | h x =>
    induction q using Quotient.inductionOn with | h y =>
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hf x y).mp hpq))
  rw [Subgroup.relIndex, Subgroup.index]
  refine (Nat.card_le_card_of_injective g hg).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
  rfl


/-- $\prod_v x_v \ge 2^{\#\{v : P v\}}$ when $x_v \ge 2$ on $P$ and $x_v \ge 1$ everywhere. -/
lemma two_pow_card_le_prod {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] (x : ι → ℕ)
    (h1 : ∀ i, 1 ≤ x i) (h2 : ∀ i, P i → 2 ≤ x i) :
    2 ^ (Finset.univ.filter P).card ≤ ∏ i, x i := by
  rw [← Finset.prod_const, ← Finset.prod_filter_mul_prod_filter_not Finset.univ P]
  calc ∏ _i ∈ Finset.univ.filter P, 2 = (∏ _i ∈ Finset.univ.filter P, 2) * ∏ _i ∈ Finset.univ.filter (¬ P ·), 1 := by
        simp
    _ ≤ _ := Nat.mul_le_mul (Finset.prod_le_prod' fun i hi => h2 i (Finset.mem_filter.mp hi).2)
        (Finset.prod_le_prod' fun i _ => h1 i)


/-- Finset version of `two_pow_card_le_prod`. -/
lemma two_pow_card_le_prod' {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P] (x : ι → ℕ)
    (h1 : ∀ i ∈ s, 1 ≤ x i) (h2 : ∀ i ∈ s, P i → 2 ≤ x i) :
    2 ^ (s.filter P).card ≤ ∏ i ∈ s, x i := by
  rw [← Finset.prod_const, ← Finset.prod_filter_mul_prod_filter_not s P]
  calc ∏ _i ∈ s.filter P, 2 = (∏ _i ∈ s.filter P, 2) * ∏ _i ∈ s.filter (¬ P ·), 1 := by simp
    _ ≤ _ := Nat.mul_le_mul
        (Finset.prod_le_prod' fun i hi => h2 i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
        (Finset.prod_le_prod' fun i hi => h1 i (Finset.mem_filter.mp hi).1)

/-- Multiplicative squares of $S$-units are the additive doubles. -/
lemma sqG_sUnit_toAddSubgroup (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup.toAddSubgroup (sqG (SUnit (F := F) S)) =
      (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).range := by
  ext x
  rw [Additive.mem_toAddSubgroup]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    rw [← hy]; simp [two_nsmul, pow_two]
  · rintro ⟨y, hy⟩
    refine ⟨Additive.toMul y, ?_⟩
    rw [← hy]; simp [two_nsmul, pow_two]

open scoped Classical in
/-- **The second inequality, counted** (Milne VII, §6 for $n = 2$, in $S$-unit form): for $T$ with
$|T| \ge r_\infty - 1 + |S|$ and the Kummer property (`hBsq`, from `isSquare_of_isSquare_local`), the
$(S\cup T)$-units that are local norms at $S \cup \infty$ have index $\ge 2^{s'-1}$, $s'$ = number of non-split
places of $S \cup \infty$. -/
@[kb "milne2020cft" "Ch. VII, §6 (second inequality, n = 2) [unverified]; omeara1963 §65D, 65:21, p. 185"]
theorem two_pow_le_index_locNorms {L : Type} [Field L] [NumberField L] [Algebra F L]
    [Algebra.IsQuadraticExtension F L] (a : F) (hd : ¬ IsSquare a) (s : L)
    (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (σ : L ≃ₐ[F] L) (hσs : σ s = -s) (S T : Finset (HeightOneSpectrum (𝓞 F)))
    (hST : Disjoint S T) (h2S : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (hTcard : Units.rank F + S.card ≤ T.card)
    (hBsq : ∀ y ∈ locSq S (S ∪ T), IsSquare ((y : Fˣ) : F)) :
    2 ^ ((Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card +
        (S.filter fun p => ¬ SplitsFin (L := L) p).card) ≤ (locNorms L S (S ∪ T)).index * 2 := by
  set S' := S ∪ T with hS'
  set A := locNorms L S S'
  set B := locSq S S'
  have ha0 : a ≠ 0 := by rintro rfl; exact hd ⟨0, by simp⟩
  have hsqf : ∀ v : HeightOneSpectrum (𝓞 F),
      sqG (v.adicCompletion F)ˣ ≤ normGroup (F := F) L (v.adicCompletion F) := by
    rintro v _ ⟨c, rfl⟩; exact sq_mem_normGroup a hd s hs hspan _ c
  have hsqi : ∀ w : InfinitePlace F, sqG (w.Completion)ˣ ≤ normGroup (F := F) L w.Completion := by
    rintro w _ ⟨c, rfl⟩; exact sq_mem_normGroup a hd s hs hspan _ c
  have hsqidxf : ∀ v : HeightOneSpectrum (𝓞 F), (sqG (v.adicCompletion F)ˣ).index ≠ 0 := by
    intro v; rw [index_sq_completion]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ ((Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors).mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)))
  have hsqidxi : ∀ w : InfinitePlace F, (sqG (w.Completion)ˣ).index ≠ 0 := by
    intro w; rw [index_sq_infinite]; split_ifs <;> norm_num
  have hrelf : ∀ v : HeightOneSpectrum (𝓞 F), (sqG (v.adicCompletion F)ˣ).relIndex
      (normGroup (F := F) L (v.adicCompletion F)) * (normGroup (F := F) L (v.adicCompletion F)).index =
      (sqG (v.adicCompletion F)ˣ).index := fun v => Subgroup.relIndex_mul_index (hsqf v)
  have hreli : ∀ w : InfinitePlace F, (sqG (w.Completion)ˣ).relIndex
      (normGroup (F := F) L w.Completion) * (normGroup (F := F) L w.Completion).index =
      (sqG (w.Completion)ˣ).index := fun w => Subgroup.relIndex_mul_index (hsqi w)
  have hfinf : ∀ v : HeightOneSpectrum (𝓞 F), (sqG (v.adicCompletion F)ˣ).relIndex
      (normGroup (F := F) L (v.adicCompletion F)) ≠ 0 := fun v h => by
    have := hrelf v; rw [h, zero_mul] at this; exact hsqidxf v this.symm
  have hfini : ∀ w : InfinitePlace F, (sqG (w.Completion)ˣ).relIndex
      (normGroup (F := F) L w.Completion) ≠ 0 := fun w h => by
    have := hreli w; rw [h, zero_mul] at this; exact hsqidxi w this.symm
  have hNf : ∀ v : HeightOneSpectrum (𝓞 F), (normGroup (F := F) L (v.adicCompletion F)).index ≠ 0 :=
    fun v h => by have := hrelf v; rw [h, mul_zero] at this; exact hsqidxf v this.symm
  have hNi : ∀ w : InfinitePlace F, (normGroup (F := F) L w.Completion).index ≠ 0 :=
    fun w h => by have := hreli w; rw [h, mul_zero] at this; exact hsqidxi w this.symm
  -- B is the group of squares
  have hBeq : B = sqG (SUnit (F := F) S') := by
    apply le_antisymm
    · intro y hy
      obtain ⟨r, hr⟩ := hBsq y hy
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr
      have hrS : Units.mk0 r hr0 ∈ SUnit (F := F) S' := by
        apply sqrt_mem_sUnit
        have : (Units.mk0 r hr0) ^ 2 = (y : Fˣ) := by ext; simp [pow_two, hr]
        rw [this]; exact y.2
      exact ⟨⟨Units.mk0 r hr0, hrS⟩, by ext; simp [pow_two, hr]⟩
    · rintro _ ⟨z, rfl⟩
      rw [mem_locSq]
      exact ⟨fun v => ⟨Φf S' v.1 z, by simp [pow_two]⟩, fun w => ⟨Φi S' w z, by simp [pow_two]⟩⟩
  have hBidx : B.index = 2 ^ (Units.rank F + S'.card + 1) := by
    rw [hBeq, ← Subgroup.index_toAddSubgroup, sqG_sUnit_toAddSubgroup, index_sq_sUnit]
  have hBA : B ≤ A := by
    intro y hy
    rw [mem_locSq] at hy
    rw [mem_locNorms]
    exact ⟨fun v => hsqf v.1 (hy.1 v), fun w => hsqi w (hy.2 w)⟩
  have hAB := Subgroup.relIndex_mul_index hBA
  have hrel := relIndex_locSq_le L S S' hsqf hsqi hfinf hfini
  classical
  set Yf := ∏ v : S, (sqG (v.1.adicCompletion F)ˣ).relIndex (normGroup (F := F) L (v.1.adicCompletion F))
  set Yi := ∏ w : InfinitePlace F, (sqG (w.Completion)ˣ).relIndex (normGroup (F := F) L w.Completion)
  set Xf := ∏ v : S, (normGroup (F := F) L (v.1.adicCompletion F)).index
  set Xi := ∏ w : InfinitePlace F, (normGroup (F := F) L w.Completion).index
  have hZ := prod_index_sq S h2S
  rw [← Finset.prod_coe_sort S] at hZ
  have hYXf : Yf * Xf = ∏ v : S, (sqG (v.1.adicCompletion F)ˣ).index := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun v _ => hrelf v.1
  have hYXi : Yi * Xi = ∏ w : InfinitePlace F, (sqG (w.Completion)ˣ).index := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun w _ => hreli w
  have hXf : 2 ^ (S.filter fun p => ¬ SplitsFin (L := L) p).card ≤ Xf := by
    have : Xf = ∏ v ∈ S, (normGroup (F := F) L (v.adicCompletion F)).index :=
      Finset.prod_coe_sort S (fun v => (normGroup (F := F) L (v.adicCompletion F)).index)
    rw [this]
    refine two_pow_card_le_prod' S _ _ (fun v _ => Nat.one_le_iff_ne_zero.mpr (hNf v)) ?_
    intro v _ hns
    apply two_le_index_normGroup a hd s hs hspan v
    intro hsq
    exact hns (two_primes_of_isSquare σ s a hs hσs hd v hsq)
  have hXi : 2 ^ (Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card ≤ Xi := by
    refine two_pow_card_le_prod _ _ (fun w => Nat.one_le_iff_ne_zero.mpr (hNi w)) ?_
    intro w hns
    apply two_le_index_norm_inf a hd s hs hspan w
    intro hsq
    exact hns (splitsInf_of_isSquare σ s a hs hσs ha0 w hsq)
  have hcardS' : S'.card = S.card + T.card := Finset.card_union_of_disjoint hST
  have hr : Fintype.card (InfinitePlace F) = Units.rank F + 1 := by
    have := (Fintype.card_pos : 0 < Fintype.card (InfinitePlace F))
    simp only [Units.rank]; omega
  set nI := (Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L) v).card
  set nS := (S.filter fun p => ¬ SplitsFin (L := L) p).card
  have h1 : B.index ≤ A.index * (Yf * Yi) := by
    rw [← hAB, mul_comm]; exact Nat.mul_le_mul_left _ hrel
  have h2 : 2 ^ (Units.rank F + S.card + T.card + 1) * 2 ^ (nI + nS) ≤
      A.index * 4 ^ (S.card + (Units.rank F + 1)) := by
    rw [← hr, ← hZ, ← hYXf, ← hYXi,
      show Units.rank F + S.card + T.card + 1 = Units.rank F + S'.card + 1 by omega, ← hBidx, pow_add]
    calc B.index * (2 ^ nI * 2 ^ nS) ≤ (A.index * (Yf * Yi)) * (Xi * Xf) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul hXi hXf)
      _ = A.index * (Yf * Xf * (Yi * Xi)) := by ring
  have h3 : 2 ^ (2 * Units.rank F + 2 * S.card + 1) * 2 ^ (nI + nS) ≤
      2 ^ (Units.rank F + S.card + T.card + 1) * 2 ^ (nI + nS) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4 : 4 ^ (S.card + (Units.rank F + 1)) = 2 ^ (2 * Units.rank F + 2 * S.card + 1) * 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]; congr 1; ring
  rw [h4] at h2
  have h5 := h3.trans h2
  have hpos : 0 < 2 ^ (2 * Units.rank F + 2 * S.card + 1) := pow_pos two_pos _
  rw [mul_comm (2 ^ (2 * Units.rank F + 2 * S.card + 1)) (2 ^ (nI + nS))] at h5
  have : 2 ^ (nI + nS) * 2 ^ (2 * Units.rank F + 2 * S.card + 1) ≤
      (A.index * 2) * 2 ^ (2 * Units.rank F + 2 * S.card + 1) := by
    calc _ ≤ _ := h5
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end Count

end QuadFormsKB.HN

end
