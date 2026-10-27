/-
# Hasse norm theorem, step 5c: $(S \cup T)$-units that are local squares are squares

* `normGroup`: the local norm group $N(M \otimes_F L)^\times \subseteq M^\times$;
* `mem_normGroup_of_global`, `sq_mem_normGroup`: global norms and squares are local norms;
* `two_le_index_normGroup`: $[F_t^\times : N_t] \ge 2$ where $a$ is not a square;
* `exists_approx`: families $(z_t)_{t \in N}$, $N \subseteq T$, are congruent mod squares to one $(S\cup T)$-unit;
* `isSquare_of_isSquare_local` (Milne VII, Prop. 6.10 for $n = 2$): an $(S \cup T)$-unit that is a square at
  every $v \in S$ and at every infinite place is a square in $F$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.TChoice

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

/-- The local norm group $N(F_v \otimes_F L)^\times \subseteq F_v^\times$ for any field `M` over `F`. -/
def normGroup (L : Type) [Field L] [Algebra F L] (M : Type) [Field M] [Algebra F M] : Subgroup Mˣ :=
  (Units.map (Algebra.norm M : M ⊗[F] L →* M)).range

/-- **Global norms are local norms:** if $c = x\,\sigma(x)$ with $x \in L = F(s)$, $s^2 = a$, $\sigma s = -s$, then
$c$ is a norm from $M \otimes_F L$ for every field $M \supseteq F$. -/
theorem mem_normGroup_of_global {L : Type} [Field L] [NumberField L] [Algebra F L]
    [Algebra.IsQuadraticExtension F L] (a : F) (hd : ¬ IsSquare a)
    (s : L) (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (σ : L ≃ₐ[F] L) (hσs : σ s = -s) (M : Type) [Field M] [Algebra F M]
    (x : Lˣ) (c : Fˣ) (hc : algebraMap F L (c : F) = (x : L) * σ x) :
    Units.map (algebraMap F M : F →* M) c ∈ normGroup (F := F) L M := by
  obtain ⟨t, ht, ht2, hspanT, huniqT, hnormT, hrank⟩ := tensor_structure a hd s hs hspan M
  obtain ⟨b₀, b₁, hx⟩ := hspan (x : L)
  set inc := (Algebra.TensorProduct.includeRight : L →ₐ[F] M ⊗[F] L)
  have hinc : inc (x : L) = algebraMap M _ (algebraMap F M b₀) + algebraMap M _ (algebraMap F M b₁) * t := by
    rw [hx, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
    have e : inc s = t := by rw [ht]; rfl
    rw [e, IsScalarTower.algebraMap_apply F M (M ⊗[F] L), IsScalarTower.algebraMap_apply F M (M ⊗[F] L)]
  have hcval : (c : F) = b₀ ^ 2 - a * b₁ ^ 2 := by
    apply (algebraMap F L).injective
    have hσx : σ (x : L) = algebraMap F L b₀ - algebraMap F L b₁ * s := by
      rw [hx, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσs]; ring
    rw [hc, hσx, hx]
    simp only [map_sub, map_mul, map_pow]
    rw [← hs]; ring
  refine ⟨Units.map (inc : L →* M ⊗[F] L) x, ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  change Algebra.norm M (inc (x : L)) = algebraMap F M (c : F)
  rw [hinc, hnormT, hcval]
  simp [map_sub, map_mul, map_pow]


/-- An element of valuation $-1$ at $t$ and $0$ at the other primes off $S_0$. -/
lemma exists_unif (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hS₀ : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S₀ → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S₀ → w ≠ p → c ∉ w.asIdeal)
    (t : HeightOneSpectrum (𝓞 F)) (ht : t ∉ S₀) :
    ∃ π : Fˣ, t.valuationOfNeZero π = Multiplicative.ofAdd (-1 : ℤ) ∧
      ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S₀ → q ≠ t → q.valuationOfNeZero π = 1 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := hS₀ t ht
  have hc0 : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
    rintro rfl; exact hc2 (zero_mem _)
  refine ⟨Units.mk0 _ hc0, ?_, ?_⟩
  · rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, Units.val_mk0,
      valuation_of_mem_not_sq t hc1 hc2]
    rfl
  · intro q hq hqt
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, Units.val_mk0,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem q).mpr (hc3 q hq hqt)]
    rfl

/-- Valuations of units of $F_t$ are powers of `exp 1`. -/
lemma valued_units_exp {t : HeightOneSpectrum (𝓞 F)} (z : (t.adicCompletion F)ˣ) :
    ∃ k : ℤ, Valued.v (z : t.adicCompletion F) = exp k :=
  exists_exp_eq t z.ne_zero

/-- The valuation of $F_t$ on $F^\times$. -/
lemma valued_algebraMap_units (t : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    Valued.v (algebraMap F (t.adicCompletion F) (x : F)) = (t.valuationOfNeZero x : ℤᵐ⁰) := by
  rw [valued_algebraMap, HeightOneSpectrum.valuationOfNeZero_eq]


/-- $F_S^\times \subseteq F_{S'}^\times$ for $S \subseteq S'$. -/
lemma sUnit_mono {S S' : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ S') :
    SUnit (F := F) S ≤ SUnit (F := F) S' := fun x hx p hp =>
  hx p (fun h' => hp (h h'))

open scoped Classical in
/-- **Approximation at `N ⊆ T` by `(S ∪ T)`-units modulo squares** (the surjectivity in Milne VII,
Prop. 6.10): any family $z_t \in F_t^\times$ ($t \in N$) is congruent mod squares to one $(S\cup T)$-unit. -/
theorem exists_approx (a : F) (S₀ S T N : Finset (HeightOneSpectrum (𝓞 F)))
    (hS₀ : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S₀ → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S₀ → w ≠ p → c ∉ w.asIdeal)
    (hS₀S : S₀ ⊆ S) (hT : GoodT S a T) (hidx : (kerT S T).index = 2 ^ T.card) (hN : N ⊆ T)
    (z : (t : N) → (t.1.adicCompletion F)ˣ) :
    ∃ y : SUnit (F := F) (S ∪ T), ∀ t : N,
      IsSquare (algebraMap F (t.1.adicCompletion F) (((y : Fˣ) : F)) / z t) := by
  have hTS₀ : ∀ t ∈ T, t ∉ S₀ := fun t ht h => (hT t ht).1 (hS₀S h)
  choose! π hπ1 hπ2 using exists_unif S₀ hS₀
  choose k hk using fun t : N => valued_units_exp (z t)
  set y₁ : Fˣ := ∏ t : N, (π t.1) ^ (-(k t)) with hy₁
  have hy₁val_out : ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S₀ → q ∉ T →
      q.valuationOfNeZero y₁ = 1 := by
    intro q hq hqT
    rw [hy₁, map_prod]
    refine Finset.prod_eq_one fun t _ => ?_
    rw [map_zpow, hπ2 t.1 (hTS₀ t.1 (hN t.2)) q hq (fun h => hqT (h ▸ hN t.2)), one_zpow]
  have hy₁val_N : ∀ t : N, t.1.valuationOfNeZero y₁ = Multiplicative.ofAdd (k t) := by
    intro t
    rw [hy₁, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ t)]
    rw [Finset.prod_eq_one, one_mul, map_zpow, hπ1 t.1 (hTS₀ t.1 (hN t.2))]
    · rw [← ofAdd_zsmul]; simp
    · intro t' ht'
      have hne : t' ≠ t := Finset.ne_of_mem_erase ht'
      have hne' : t.1 ≠ t'.1 := fun h => hne (Subtype.ext h.symm)
      rw [map_zpow, hπ2 t'.1 (hTS₀ t'.1 (hN t'.2)) t.1 (hTS₀ t.1 (hN t.2)) hne', one_zpow]
  have hy₁S : y₁ ∈ SUnit (F := F) (S ∪ T) := by
    rw [mem_sUnit_iff]
    intro q hq
    simp only [Finset.mem_union, not_or] at hq
    exact hy₁val_out q (fun h => hq.1 (hS₀S h)) hq.2
  -- the unit parts
  have hdval : ∀ t : N, Valued.v (((z t * (Units.map (algebraMap F (t.1.adicCompletion F) : F →*
      t.1.adicCompletion F) y₁)⁻¹ : (t.1.adicCompletion F)ˣ)) : t.1.adicCompletion F) = 1 := by
    intro t
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_map,
      MonoidHom.coe_ofClass, valued_algebraMap_units, hy₁val_N, hk t]
    exact mul_inv_cancel₀ (by exact exp_ne_zero)
  let d : (t : T) → U0 t.1 := fun t =>
    if h : t.1 ∈ N then ⟨z ⟨t.1, h⟩ * (Units.map (algebraMap F (t.1.adicCompletion F) :
      F →* t.1.adicCompletion F) y₁)⁻¹, (mem_U0 t.1).mpr (hdval ⟨t.1, h⟩)⟩ else 1
  obtain ⟨u, hu⟩ := ρT_surjective S T a hT hidx (fun t => QuotientGroup.mk (d t))
  refine ⟨⟨(u : Fˣ) * y₁, mul_mem (sUnit_mono Finset.subset_union_left u.2) hy₁S⟩, fun t => ?_⟩
  have htT : t.1 ∈ T := hN t.2
  have h1 := congrFun hu ⟨t.1, htT⟩
  simp only [ρT, ρ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, QuotientGroup.coe_mk',
    Function.comp_apply] at h1
  rw [QuotientGroup.eq] at h1
  obtain ⟨r, hr⟩ := h1
  have hdt : d ⟨t.1, htT⟩ = ⟨z t * (Units.map (algebraMap F (t.1.adicCompletion F) :
      F →* t.1.adicCompletion F) y₁)⁻¹, (mem_U0 t.1).mpr (hdval t)⟩ := by
    simp only [d, dif_pos t.2]
  rw [hdt] at hr
  have hr' := congrArg (fun w : U0 t.1 => (((w : (t.1.adicCompletion F)ˣ)) : t.1.adicCompletion F)) hr
  simp only [powMonoidHom_apply, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hr'
  simp only [unitAtHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, MonoidHom.coe_ofClass] at hr'
  refine ⟨((((r : U0 t.1) : (t.1.adicCompletion F)ˣ) : t.1.adicCompletion F))⁻¹, ?_⟩
  have hz0 : ((z t : (t.1.adicCompletion F)ˣ) : t.1.adicCompletion F) ≠ 0 := Units.ne_zero _
  have hu0 : algebraMap F (t.1.adicCompletion F) (((u : Fˣ)) : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F _).injective]; exact Units.ne_zero _
  have hy0 : algebraMap F (t.1.adicCompletion F) ((y₁ : Fˣ) : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F _).injective]; exact Units.ne_zero _
  have hr0 : (((r : U0 t.1) : (t.1.adicCompletion F)ˣ) : t.1.adicCompletion F) ≠ 0 := Units.ne_zero _
  simp only [Units.val_mul, map_mul]
  set R := (((r : U0 t.1) : (t.1.adicCompletion F)ˣ) : t.1.adicCompletion F)
  have key : R ^ 2 * (algebraMap F (t.1.adicCompletion F) (((u : Fˣ)) : F) *
      algebraMap F (t.1.adicCompletion F) ((y₁ : Fˣ) : F)) = ((z t : (t.1.adicCompletion F)ˣ) : _) := by
    rw [hr']; field_simp
  rw [div_eq_iff hz0, ← key]
  field_simp


/-- Squares are local norms. -/
lemma sq_mem_normGroup {L : Type} [Field L] [NumberField L] [Algebra F L]
    [Algebra.IsQuadraticExtension F L] (a : F) (hd : ¬ IsSquare a) (s : L)
    (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (M : Type) [Field M] [Algebra F M] (c : Mˣ) : c ^ 2 ∈ normGroup (F := F) L M := by
  obtain ⟨t, -, -, -, -, -, hrank⟩ := tensor_structure a hd s hs hspan M
  refine ⟨Units.map (algebraMap M (M ⊗[F] L) : M →* M ⊗[F] L) c, ?_⟩
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val]
  rw [Algebra.norm_algebraMap, hrank]

/-- At a finite place where `a` is not a square, the local norms have index $\ge 2$ (restated for an
arbitrary prime of `F`). -/
lemma two_le_index_normGroup {L : Type} [Field L] [NumberField L] [Algebra F L]
    [Algebra.IsQuadraticExtension F L] (a : F) (hd : ¬ IsSquare a) (s : L)
    (hs : s ^ 2 = algebraMap F L a)
    (hspan : ∀ y : L, ∃ b₀ b₁ : F, y = algebraMap F L b₀ + algebraMap F L b₁ * s)
    (t : HeightOneSpectrum (𝓞 F)) (ht : ¬ IsSquare (algebraMap F (t.adicCompletion F) a)) :
    2 ≤ (normGroup (F := F) L (t.adicCompletion F)).index := by
  obtain ⟨w, rfl⟩ := exists_over (L := L) t
  exact two_le_index_norm a hd s hs hspan w ht


open scoped Classical in
/-- **Milne VII, Prop. 6.10 for $n = 2$:** with $T$ as in `exists_T`, an $(S \cup T)$-unit that is a square
at every $v \in S$ and every infinite place is a square in $F$.

*Proof.* Otherwise let $L' = F(\sqrt y)$. It is unramified outside $S \cup T$ (`ramificationIdx_eq_one`),
split at $S$ and at infinity (`two_primes_of_isSquare`, `splitsInf_of_isSquare`), so by `index_normsF_eq`
$2\,[F_{S\cup T}^\times : N] = 2^{|N_T|}$ where $N_T \subseteq T$ are the non-split primes. But the global norms are
local norms (`mem_normGroup_of_global`) and $F_{S \cup T}^\times \to \prod_{t \in N_T} F_t^\times/N_t$ is onto
(`exists_approx`, squares being norms), with each factor of order $\ge 2$ (`two_le_index_normGroup`), so
$[F_{S\cup T}^\times : N] \ge 2^{|N_T|}$. -/
@[kb "milne2020cft" "Ch. VII, Prop. 6.10 (n = 2) [unverified]"]
theorem isSquare_of_isSquare_local (a : F) (S₀ S T : Finset (HeightOneSpectrum (𝓞 F)))
    (hS₀ : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S₀ → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S₀ → w ≠ p → c ∉ w.asIdeal)
    (hS₀S : S₀ ⊆ S) (h2S : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (hT : GoodT S a T) (hidx : (kerT S T).index = 2 ^ T.card)
    (y : Fˣ) (hy : y ∈ SUnit (F := F) (S ∪ T))
    (hyS : ∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) (y : F)))
    (hyInf : ∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion (y : F))) :
    IsSquare (y : F) := by
  by_contra hns
  obtain ⟨L', _, _, _, s', hs', hspan'⟩ := QuadFormsKB.Lam.exists_quadExt (y : F) hns
  obtain ⟨hQ, σ', hσ', hσs'⟩ := quadData (y : F) hns s' hs' hspan'
  set S' := S ∪ T with hS'def
  have hS' : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S' → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧
      c ∉ p.asIdeal ^ 2 ∧ ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S' → q ≠ p → c ∉ q.asIdeal := by
    intro p hp
    have hp0 : p ∉ S₀ := fun h => hp (Finset.mem_union_left _ (hS₀S h))
    obtain ⟨c, h1, h2, h3⟩ := hS₀ p hp0
    exact ⟨c, h1, h2, fun q hq hqp => h3 q (fun h => hq (Finset.mem_union_left _ (hS₀S h))) hqp⟩
  have hram' : ∀ w : HeightOneSpectrum (𝓞 L'), under (F := F) w ∉ S' →
      w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    intro w hw
    apply ramificationIdx_eq_one σ' s' (y : F) hs' hσs' w
    · have h2 : (2 : 𝓞 F) ∉ (under (F := F) w).asIdeal := fun h =>
        hw (Finset.mem_union_left _ (h2S _ h))
      have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (under (F := F) w)).mpr h2
      rwa [map_ofNat] at this
    · exact hy _ (by simpa using hw)
  have hcount := index_normsF_eq σ' hσ' S' hS' hram'
  have hInf : (Finset.univ.filter fun v : InfinitePlace F => ¬ SplitsInf (L := L') v) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v _ hv
    exact hv (splitsInf_of_isSquare σ' s' (y : F) hs' hσs' (Units.ne_zero y) v (hyInf v))
  rw [hInf, Finset.card_empty, zero_add] at hcount
  set N := S'.filter fun p => ¬ SplitsFin (L := L') p with hNdef
  have hNsq : ∀ t ∈ N, ¬ IsSquare (algebraMap F (t.adicCompletion F) (y : F)) := by
    intro t ht hsq
    simp only [hNdef, Finset.mem_filter] at ht
    exact ht.2 (two_primes_of_isSquare σ' s' (y : F) hs' hσs' hns t hsq)
  have hNT : N ⊆ T := by
    intro t ht
    have ht' := ht
    simp only [hNdef, Finset.mem_filter, hS'def, Finset.mem_union] at ht'
    rcases ht'.1 with h | h
    · exact absurd (hyS t h) (hNsq t ht)
    · exact h
  -- the map to the local norm residue groups at N
  let Q : N → Type := fun t =>
    (t.1.adicCompletion F)ˣ ⧸ normGroup (F := F) L' (t.1.adicCompletion F)
  let ψ : SUnit (F := F) S' →* ((t : N) → Q t) :=
    { toFun := fun x t => QuotientGroup.mk (Units.map (algebraMap F (t.1.adicCompletion F) :
          F →* t.1.adicCompletion F) (x : Fˣ))
      map_one' := by funext t; simp
      map_mul' := fun x y => by funext t; simp }
  have hsurj : Function.Surjective ψ := by
    intro q
    choose z hz using fun t : N => QuotientGroup.mk_surjective (q t)
    obtain ⟨y', hy'⟩ := exists_approx a S₀ S T N hS₀ hS₀S hT hidx hNT z
    refine ⟨y', ?_⟩
    funext t
    rw [← hz t]
    change QuotientGroup.mk _ = QuotientGroup.mk _
    rw [QuotientGroup.eq]
    obtain ⟨r, hr⟩ := hy' t
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero, div_eq_zero_iff] at hr
      rcases hr with h | h
      · rw [map_eq_zero_iff _ (algebraMap F _).injective] at h; exact Units.ne_zero _ h
      · exact Units.ne_zero _ h
    have hsq := sq_mem_normGroup (y : F) hns s' hs' hspan' (t.1.adicCompletion F) (Units.mk0 r hr0)⁻¹
    convert hsq using 1
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    have hz0 : ((z t : (t.1.adicCompletion F)ˣ) : t.1.adicCompletion F) ≠ 0 := Units.ne_zero _
    have hy0 : algebraMap F (t.1.adicCompletion F) (((y' : Fˣ)) : F) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap F _).injective]; exact Units.ne_zero _
    rw [div_eq_iff hz0] at hr
    field_simp
    rw [hr]; ring
  -- global norms lie in the kernel
  have hK : normsF σ' S' ≤ Subgroup.toAddSubgroup ψ.ker := by
    intro c hc
    obtain ⟨x, hx⟩ := hc
    rw [Additive.mem_toAddSubgroup, MonoidHom.mem_ker]
    funext t
    change (QuotientGroup.mk _ : Q t) = 1
    rw [QuotientGroup.eq_one_iff]
    have hxc : algebraMap F L' ((((Additive.toMul c : SUnit S') : Fˣ)) : F) =
        (((Additive.toMul x : SUnit _) : L'ˣ) : L') * σ' (((Additive.toMul x : SUnit _) : L'ˣ) : L') := by
      have := congrArg (fun z => (((Additive.toMul z : SUnit _) : L'ˣ) : L')) hx
      simp only [normHom_apply, toMul_add, Subgroup.coe_mul, Units.val_mul, inclS_apply,
        σS_apply] at this
      exact this.symm
    exact mem_normGroup_of_global (y : F) hns s' hs' hspan' σ' hσs' _ _ _ hxc
  -- indices
  have hfinQ : ∀ t : N, Nat.card (Q t) = (normGroup (F := F) L' (t.1.adicCompletion F)).index :=
    fun t => rfl
  have hQ2 : ∀ t : N, 2 ≤ Nat.card (Q t) := fun t => by
    rw [hfinQ]; exact two_le_index_normGroup (y : F) hns s' hs' hspan' t.1 (hNsq t.1 t.2)
  have hQfin : ∀ t : N, Finite (Q t) := fun t =>
    Nat.finite_of_card_ne_zero (by have := hQ2 t; omega)
  have hidxK : ψ.ker.index = ∏ t : N, Nat.card (Q t) := by
    have h1 := Subgroup.index_ker (G := SUnit (F := F) S') (G' := (t : N) → Q t) ψ
    rw [h1, MonoidHom.range_eq_top_of_surjective (G := SUnit (F := F) S') (N := (t : N) → Q t) _ hsurj,
      Subgroup.card_top, Nat.card_pi]
  have hge : 2 ^ N.card ≤ ψ.ker.index := by
    rw [hidxK]
    calc 2 ^ N.card = ∏ _t : N, 2 := by simp
      _ ≤ ∏ t : N, Nat.card (Q t) := Finset.prod_le_prod' fun t _ => hQ2 t
  have hdvd := AddSubgroup.index_dvd_of_le hK
  rw [Subgroup.index_toAddSubgroup] at hdvd
  have hn0 : (normsF σ' S').index ≠ 0 := by
    intro h; rw [h, zero_mul] at hcount; exact (pow_ne_zero _ two_ne_zero) hcount.symm
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have : 2 ^ N.card * 2 ≤ 2 ^ N.card := by
    calc 2 ^ N.card * 2 ≤ (normsF σ' S').index * 2 := Nat.mul_le_mul_right _ (hge.trans hle)
      _ = 2 ^ N.card := hcount
  have hpos : 0 < 2 ^ N.card := pow_pos two_pos _
  omega

end QuadFormsKB.HN

end
