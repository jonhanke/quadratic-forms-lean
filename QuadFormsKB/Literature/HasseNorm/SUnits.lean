/-
# Hasse norm theorem, step 2: `S`-units

For a number field $F$ and a finite set $S$ of finite primes (the infinite places are always
allowed), the group $F_S^\times$ = Mathlib's `Set.unit` (`SUnit S`) of elements that are units at every
prime outside $S$:

* `finrank_sUnit`: $F_S^\times$ is finitely generated of $\mathbb Z$-rank $r_\infty - 1 + |S|$ (Dirichlet's unit
  theorem `NumberField.Units.finrank_eq` for the kernel of the valuation vector `ordVec`, plus a
  finite-index image in $\mathbb Z^S$ built from generators of $\mathfrak p^{h}$, $h$ the class number);
* `index_sq_sUnit`: $[F_S^\times : F_S^{\times 2}] = 2^{r_\infty + |S|}$ (the torsion contains exactly the square
  roots $\pm 1$ of $1$);
* `exists_classGroup_generators`: a finite $S_0$ with $\mathrm{Cl}_{S_0}(F) = 1$, in the form needed later
  ("$S_0$-uniformizers" at every prime outside $S_0$).

Mathlib v4.35.0 has `Set.unit` and the unit theorem but no rank or finite generation of $S$-units.
See `Herbrand.lean` for the overall plan. Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.Herbrand

open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace QuadFormsKB.HN

variable {F : Type*} [Field F] [NumberField F]

/-- **An element of exactly one prime:** for every prime $\mathfrak p$ of $\mathcal O_F$ there is $\pi \in \mathcal O_F$, $\pi \ne 0$,
with $\pi \in \mathfrak p$ and $\pi \notin \mathfrak w$ for every prime $\mathfrak w \ne \mathfrak p$ (a generator of $\mathfrak p^h$, $h$
the class number). -/
theorem exists_mem_only (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : 𝓞 F, π ≠ 0 ∧ π ∈ v.asIdeal ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → π ∉ w.asIdeal := by
  classical
  set n := Fintype.card (ClassGroup (𝓞 F)) with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hI : v.asIdeal ^ n ∈ (Ideal (𝓞 F))⁰ := pow_mem hv0 n
  have hp : (v.asIdeal ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff hI]
    have : (⟨v.asIdeal ^ n, hI⟩ : (Ideal (𝓞 F))⁰) = ⟨v.asIdeal, hv0⟩ ^ n := rfl
    rw [this, map_pow, hn, pow_card_eq_one]
  obtain ⟨π, hπ⟩ := hp
  have hπI : v.asIdeal ^ n = Ideal.span {π} := hπ
  have hπmem : π ∈ v.asIdeal ^ n := by rw [hπI]; exact Ideal.mem_span_singleton_self π
  refine ⟨π, ?_, Ideal.pow_le_self hn0.ne' hπmem, ?_⟩
  · rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hπI
    exact (pow_ne_zero n v.ne_bot) hπI
  · intro w hw hπw
    apply hw
    have hle : v.asIdeal ^ n ≤ w.asIdeal := by
      rw [hπI, Ideal.span_le, Set.singleton_subset_iff]; exact hπw
    have := w.isPrime.le_of_pow_le hle
    exact (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top this)).symm


/-- The group $F_S^\times$ of `S`-units ($S$ a finite set of finite primes; the infinite places are
always allowed): Mathlib's `Set.unit`. -/
abbrev SUnit (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup Fˣ :=
  (↑S : Set (HeightOneSpectrum (𝓞 F))).unit F

/-- The valuation vector $x \mapsto (\operatorname{ord}_v x)_{v \in S}$ on $S$-units (additive notation). -/
def ordVec (S : Finset (HeightOneSpectrum (𝓞 F))) : Additive (SUnit (F := F) S) →+ (S → ℤ) where
  toFun x v := Multiplicative.toAdd (v.1.valuationOfNeZero ((Additive.toMul x : SUnit S) : Fˣ))
  map_zero' := by ext v; simp
  map_add' x y := by ext v; simp [toMul_add]

/-- If the $v$-coordinate of `ordVec` vanishes, the $v$-adic valuation is $1$. -/
lemma valuation_eq_one_of_ordVec (S : Finset (HeightOneSpectrum (𝓞 F)))
    (x : Additive (SUnit (F := F) S)) (v : S) (h : ordVec S x v = 0) :
    v.1.valuation F (((Additive.toMul x : SUnit S) : Fˣ) : F) = 1 := by
  rw [← HeightOneSpectrum.valuationOfNeZero_eq]
  simp only [ordVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rw [show v.1.valuationOfNeZero ((Additive.toMul x : SUnit S) : Fˣ) = 1 from by
    rw [← ofAdd_toAdd (v.1.valuationOfNeZero _), h, ofAdd_zero]]
  rfl

/-- Integral units $\mathcal O_F^\times \to F_S^\times$ (additive notation). -/
def unitsToSUnit (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Additive (𝓞 F)ˣ →+ Additive (SUnit (F := F) S) where
  toFun u := Additive.ofMul ⟨Units.map (algebraMap (𝓞 F) F : 𝓞 F →* F) (Additive.toMul u),
    fun v _ => by
      have := v.valuation_of_unit_eq (K := F) (Additive.toMul u)
      rw [← HeightOneSpectrum.valuationOfNeZero_eq, this]; rfl⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- `unitsToSUnit` is injective. -/
lemma unitsToSUnit_injective (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Function.Injective (unitsToSUnit (F := F) S) := by
  intro x y h
  have := congrArg (fun z => (((Additive.toMul z : SUnit S) : Fˣ) : F)) h
  simp only [unitsToSUnit, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Units.coe_map,
    MonoidHom.coe_ofClass] at this
  apply Additive.toMul.injective
  apply Units.ext
  exact (FaithfulSMul.algebraMap_injective (𝓞 F) F) this

/-- The kernel of the valuation vector is exactly $\mathcal O_F^\times$ (valuations $1$ at every prime give
integrality of $x$ and $x^{-1}$). -/
lemma range_unitsToSUnit (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (unitsToSUnit (F := F) S).range = (ordVec S).ker := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    ext v
    simp only [ordVec, unitsToSUnit, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul,
      Pi.zero_apply]
    rw [HeightOneSpectrum.valuation_of_unit_eq]; rfl
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    set y : Fˣ := ((Additive.toMul x : SUnit S) : Fˣ) with hy
    have hval : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (y : F) = 1 := by
      intro v
      by_cases hv : v ∈ S
      · exact valuation_eq_one_of_ordVec S x ⟨v, hv⟩ (congrFun hx ⟨v, hv⟩)
      · exact (Additive.toMul x).2 v hv
    have hval' : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((y⁻¹ : Fˣ) : F) = 1 := by
      intro v; rw [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one]
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (y : F)
      (fun v => (hval v).le)
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F ((y⁻¹ : Fˣ) : F)
      (fun v => (hval' v).le)
    have hab : a * b = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    refine ⟨Additive.ofMul ⟨a, b, hab, by rw [mul_comm, hab]⟩, ?_⟩
    apply Additive.toMul.injective
    ext
    simp only [unitsToSUnit, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Units.coe_map,
      MonoidHom.coe_ofClass]
    exact ha


/-- **Rank–nullity** for a homomorphism of abelian groups with finitely generated source. -/
theorem finrank_eq_finrank_ker_add_range' {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module.Finite ℤ M] (f : M →+ N) :
    finrank ℤ M = finrank ℤ f.ker + finrank ℤ f.range := by
  let g := f.toIntLinearMap
  have h1 := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [g.quotKerEquivRange.finrank_eq] at h1
  rw [← h1, add_comm]
  congr 1

open scoped Classical in
/-- Each coordinate direction of $\mathbb Z^S$ meets the image of `ordVec` in a nonzero multiple. -/
lemma ordVec_single (S : Finset (HeightOneSpectrum (𝓞 F))) (v : S) :
    ∃ c : ℤ, c ≠ 0 ∧ c • (Pi.single v 1 : S → ℤ) ∈ (ordVec S).range := by
  classical
  obtain ⟨π, hπ0, hπv, hπw⟩ := exists_mem_only v.1
  have hπF : (algebraMap (𝓞 F) F π) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hπ0
  let y : Fˣ := Units.mk0 _ hπF
  have hy : y ∈ SUnit (F := F) S := by
    intro w hw
    have hwv : w ≠ v.1 := fun h => hw (h ▸ v.2)
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr (hπw w hwv)
  set x : Additive (SUnit (F := F) S) := Additive.ofMul ⟨y, hy⟩ with hx
  refine ⟨ordVec S x v, ?_, ?_⟩
  · intro h
    have := valuation_eq_one_of_ordVec S x v h
    simp only [hx, toMul_ofMul, y, Units.val_mk0] at this
    exact ((HeightOneSpectrum.valuation_eq_one_iff_notMem v.1).mp this) hπv
  · refine ⟨x, ?_⟩
    ext w
    by_cases hw : w = v
    · subst hw; simp
    · rw [Pi.smul_apply, Pi.single_eq_of_ne hw, smul_zero]
      have hw' : w.1 ≠ v.1 := fun h => hw (Subtype.ext h)
      have h1 : w.1.valuation F (y : F) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem w.1).mpr (hπw w.1 hw')
      rw [← HeightOneSpectrum.valuationOfNeZero_eq] at h1
      have h2 : w.1.valuationOfNeZero y = 1 := by exact_mod_cast h1
      simp only [ordVec, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hx, toMul_ofMul]
      rw [h2]; rfl

/-- The image of the valuation vector has finite index in $\mathbb Z^S$. -/
theorem index_range_ordVec_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (ordVec S).range.index ≠ 0 := by
  classical
  choose c hc0 hc using ordVec_single (F := F) S
  set C : ℤ := ∏ v, c v with hC
  have hsingle : ∀ v : S, C • (Pi.single v 1 : S → ℤ) ∈ (ordVec S).range := by
    intro v
    have : C = (∏ w ∈ Finset.univ.erase v, c w) * c v := by
      rw [hC, ← Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
    rw [this, mul_smul]
    exact AddSubgroup.zsmul_mem _ (hc v) _
  have hall : ∀ y : S → ℤ, C • y ∈ (ordVec S).range := by
    intro y
    rw [← Finset.univ_sum_single y, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun v _ => ?_
    have : C • Pi.single v (y v) = y v • (C • (Pi.single v 1 : S → ℤ)) := by
      ext w; by_cases h : w = v
      · subst h; simp [mul_comm]
      · simp [Pi.single_eq_of_ne h]
    rw [this]; exact AddSubgroup.zsmul_mem _ (hsingle v) _
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hc0 v
  have hle : (nsmulAddMonoidHom (α := S → ℤ) C.natAbs).range ≤ (ordVec S).range := by
    rintro _ ⟨y, rfl⟩
    simp only [nsmulAddMonoidHom_apply]
    rcases Int.natAbs_eq C with h | h
    · rw [← Nat.cast_smul_eq_nsmul ℤ, ← h]; exact hall y
    · rw [← Nat.cast_smul_eq_nsmul ℤ, show ((C.natAbs : ℕ) : ℤ) = -C by omega, neg_smul]
      exact neg_mem (hall y)
  intro h0
  have := AddSubgroup.index_dvd_of_le hle
  rw [h0, zero_dvd_iff, AddSubgroup.index_range_nsmul] at this
  exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr hC0) this

/-- $F_S^\times$ is finitely generated. -/
instance (S : Finset (HeightOneSpectrum (𝓞 F))) : Module.Finite ℤ (Additive (SUnit (F := F) S)) := by
  let f := (ordVec (F := F) S).toIntLinearMap
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker f (Submodule.FG.of_finite) ?_⟩
  rw [top_inf_eq]
  have : LinearMap.ker f = LinearMap.range (unitsToSUnit (F := F) S).toIntLinearMap := by
    ext x
    change x ∈ (ordVec S).ker ↔ x ∈ (unitsToSUnit S).range
    rw [range_unitsToSUnit]
  rw [this, LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map _

/-- **Rank of the `S`-units:** $\operatorname{rk} F_S^\times = r_\infty - 1 + |S|$, where $r_\infty$ is the number of
infinite places and $S$ is the set of finite primes allowed. -/
@[kb "milne2020cft" "Ch. VII §6 (unit theorem for S-units) [unverified]"]
theorem finrank_sUnit (S : Finset (HeightOneSpectrum (𝓞 F))) :
    finrank ℤ (Additive (SUnit (F := F) S)) = Units.rank F + S.card := by
  rw [finrank_eq_finrank_ker_add_range' (ordVec S)]
  congr 1
  · rw [← Units.finrank_eq F]
    rw [← range_unitsToSUnit]
    exact (AddMonoidHom.ofInjective (unitsToSUnit_injective S)).toIntLinearEquiv.finrank_eq.symm
  · rw [finrank_eq_of_relIndex_ne_zero (le_top) (by rw [AddSubgroup.relIndex_top_right]; exact index_range_ordVec_ne_zero S)]
    rw [AddSubgroup.topEquiv.toIntLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]


/-- The only square roots of $1$ in $F_S^\times$ are $\pm 1$, so the $2$-torsion has exactly two elements. -/
theorem card_ker_two_sUnit (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).ker = 2 := by
  classical
  have hm1 : (-1 : Fˣ) ∈ SUnit (F := F) S := by
    intro v _
    simp
  set m : Additive (SUnit (F := F) S) := Additive.ofMul ⟨-1, hm1⟩
  have hm : m ∈ (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).ker := by
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
    apply Additive.toMul.injective
    ext; simp [m]
  rw [Nat.card_eq_two_iff]
  refine ⟨0, ⟨m, hm⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun z => ((((Additive.toMul z.1 : SUnit S) : Fˣ)) : F)) h
    simp [m] at this
    have h2 : (2 : F) = 0 := by linear_combination this
    exact two_ne_zero h2
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply] at hx
    have h1 : (((Additive.toMul x : SUnit S) : Fˣ) : F) * (((Additive.toMul x : SUnit S) : Fˣ) : F) = 1 := by
      have := congrArg (fun z => ((((Additive.toMul z : SUnit S) : Fˣ)) : F)) hx
      simpa [two_nsmul] using this
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · left
      apply Subtype.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
      simpa using h
    · right
      apply Subtype.ext; apply Additive.toMul.injective; apply Subtype.ext; apply Units.ext
      simpa [m] using h


/-- **Squares in the `S`-units:** $[F_S^\times : F_S^{\times 2}] = 2^{r_\infty + |S|}$ ($= 2^{\#\text{all places in } S}$
when $S$ is completed by the $r_\infty$ infinite places). From `index_range_two`, `finrank_sUnit`
and `card_ker_two_sUnit` ($\mathrm{rk} = r_\infty - 1 + |S|$, and the torsion contains $-1$). -/
@[kb "milne2020cft" "Ch. VII §6, proof of Lemma 6.7 [unverified]"]
theorem index_sq_sUnit (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (nsmulAddMonoidHom (α := Additive (SUnit (F := F) S)) 2).range.index =
      2 ^ (Units.rank F + S.card + 1) := by
  rw [index_range_two, finrank_sUnit, card_ker_two_sUnit, pow_succ]


/-- **A finite set of primes generating the class group** (so $\mathrm{Cl}_{S}(F) = 1$ for $S \supseteq S_0$): there is a
finite set $S_0$ of primes such that every prime $\mathfrak p \notin S_0$ has an "$S_0$-uniformizer" $c \in \mathcal O_F$:
$c \in \mathfrak p \setminus \mathfrak p^2$ and $c \notin \mathfrak w$ for every other prime $\mathfrak w \notin S_0$.

*Proof.* Pick an integral ideal $J_C$ in each ideal class $C$ (the class group is finite) and let $S_0$ be
the primes containing some $J_C$. For $\mathfrak p \notin S_0$, $\mathfrak p J$ is principal, $= (c)$, for $J$ the
representative of $[\mathfrak p]^{-1}$; $c \notin \mathfrak p^2$ since $J \not\subseteq \mathfrak p$, and $c \notin \mathfrak w$
since neither $\mathfrak p$ nor $J$ is contained in $\mathfrak w$. -/
@[kb "milne2020cft" "Ch. V, Prop. 4.2 / Ch. VII §6 condition (d) [unverified]"]
theorem exists_classGroup_generators :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S₀ →
      ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S₀ → w ≠ p → c ∉ w.asIdeal := by
  classical
  choose J hJ using (ClassGroup.mk0_surjective (R := 𝓞 F))
  have hfin : ∀ C : ClassGroup (𝓞 F),
      {v : HeightOneSpectrum (𝓞 F) | (J C : Ideal (𝓞 F)) ≤ v.asIdeal}.Finite := by
    intro C
    have hne : (J C : Ideal (𝓞 F)) ≠ 0 := nonZeroDivisors.coe_ne_zero (J C)
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_iff_le.mpr hv
  let S₀ : Finset (HeightOneSpectrum (𝓞 F)) :=
    Finset.univ.biUnion fun C => (hfin C).toFinset
  have hS₀ : ∀ v, v ∉ S₀ → ∀ C, ¬ (J C : Ideal (𝓞 F)) ≤ v.asIdeal := by
    intro v hv C hC
    apply hv
    simp only [S₀, Finset.mem_biUnion, Finset.mem_univ, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      true_and]
    exact ⟨C, hC⟩
  refine ⟨S₀, fun p hp => ?_⟩
  have hp0 : p.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero p.ne_bot
  set C := (ClassGroup.mk0 ⟨p.asIdeal, hp0⟩)⁻¹ with hC
  set Jp : Ideal (𝓞 F) := (J C : Ideal (𝓞 F)) with hJpdef
  have hprod : (p.asIdeal * Jp).IsPrincipal := by
    have hm : p.asIdeal * Jp ∈ (Ideal (𝓞 F))⁰ := mul_mem hp0 (J C).2
    rw [← ClassGroup.mk0_eq_one_iff hm]
    have : (⟨p.asIdeal * Jp, hm⟩ : (Ideal (𝓞 F))⁰) = ⟨p.asIdeal, hp0⟩ * J C :=
      Subtype.ext (by rw [Submonoid.coe_mul])
    rw [this, map_mul, hJ, hC, mul_inv_cancel]
  obtain ⟨c, hc⟩ := hprod
  have hcI : p.asIdeal * Jp = Ideal.span {c} := hc
  have hcmem : c ∈ p.asIdeal * Jp := by rw [hcI]; exact Ideal.mem_span_singleton_self c
  have hJp : ¬ Jp ≤ p.asIdeal := hS₀ p hp C
  refine ⟨c, (Ideal.mul_le_left : p.asIdeal * Jp ≤ p.asIdeal) hcmem, ?_, ?_⟩
  · intro hc2
    apply hJp
    have hle : p.asIdeal * Jp ≤ p.asIdeal * p.asIdeal := by
      rw [hcI, Ideal.span_le, Set.singleton_subset_iff, ← pow_two]; exact hc2
    exact le_of_mul_le_mul_left hle (bot_lt_iff_ne_bot.mpr p.ne_bot)
  · intro w hw hwp hcw
    have hle : p.asIdeal * Jp ≤ w.asIdeal := by
      rw [hcI, Ideal.span_le, Set.singleton_subset_iff]; exact hcw
    rcases w.isPrime.mul_le.mp hle with h | h
    · exact hwp (HeightOneSpectrum.ext (p.isMaximal.eq_of_le w.isPrime.ne_top h)).symm
    · exact hS₀ w hw C h

end QuadFormsKB.HN

end
