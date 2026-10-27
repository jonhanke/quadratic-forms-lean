/-
# The Hasse norm theorem for quadratic extensions: our own proof

`HasseNorm.hilbert_eq_one_of_everywhere`: for $a, b \in F^\times$, if the local Hilbert symbol $(a,b)_v = 1$ at
every place $v$ of the number field $F$, then $(a,b)_F = 1$; equivalently, a local norm from $F(\sqrt a)$
everywhere is a global norm. This replaces the Yamaguchi-derived proof
(`hilbert_eq_one_of_everywhere_yamaguchi`, now archived in `archive/yamaguchi/`) in `lamInputs`, so `hasseMinkowski_nf`
depends only on Mathlib and this repository.

**Route** (plan in `Herbrand.lean`; Chevalley's algebraic second inequality, Milne VII §§3–6 with
$n = 2$, written with $S$-units instead of idèles):

1. order-2 index algebra (`Herbrand.lean`), $S$-units (`SUnits.lean`);
2. the global count $2\,[F_{S'}^\times : N L_{S'}^\times] = 2^{s'}$ (`FirstInequality.lean`, `Places.lean`);
3. local square classes and local norm indices (`SquareClasses.lean`, `LocalNorm.lean`, `Infinite.lean`);
4. the auxiliary set $T$ (`GoodPrimes.lean`, `TChoice.lean`, using Dedekind's density argument
   `SqLG.not_almost_all_split`), Prop. 6.10 (`KummerSquares.lean`) and the second inequality
   (`SecondInequality.lean`);
5. here: local norms in $F_{S'}^\times$ are global norms (`HN.hasse_norm_integral`), and the scaling of $a$.

Locators are from memory and still `[unverified]`.
-/
import QuadFormsKB.Literature.HasseNorm.SecondInequality

open Module NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.HN

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
/-- **The Hasse norm theorem for $F(\sqrt a)$, $a \in \mathcal O_F$** (core of `hilbert_eq_one_of_everywhere`):
for $a \in \mathcal O_F$ not a square and $b \in F^\times$ with $(a,b)_v = 1$ at every place, $(a, b)_F = 1$. -/
@[kb "milne2020cft" "Ch. VII §6 and Hasse norm theorem (n = 2) [unverified]; omeara1963 §65D, 65:23, p. 186"]
theorem hasse_norm_integral (a : 𝓞 F) (hd : ¬ IsSquare (a : F)) (b : F) (hb : b ≠ 0)
    (h : ∀ v : NFPlace F, v.hilbert (a : F) b = 1) : hilbertSymbol F (a : F) b = 1 := by
  classical
  have ha0 : (a : F) ≠ 0 := by rintro h0; exact hd ⟨0, by simp [h0]⟩
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (a : F) hd
  obtain ⟨hQ, σ, hσ, hσs⟩ := quadData (a : F) hd s hs hspan
  obtain ⟨S₀, hS₀⟩ := exists_classGroup_generators (F := F)
  -- the bad primes
  set aU : Fˣ := Units.mk0 (a : F) ha0
  set bU : Fˣ := Units.mk0 b hb
  have h2fin : {p : HeightOneSpectrum (𝓞 F) | (2 : 𝓞 F) ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(2 : 𝓞 F)}) (by simp)).subset ?_
    intro p hp; rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  set S : Finset (HeightOneSpectrum (𝓞 F)) :=
    S₀ ∪ h2fin.toFinset ∪ (finite_support aU).toFinset ∪ (finite_support bU).toFinset with hSdef
  have hS₀S : S₀ ⊆ S := fun p hp => by simp [hSdef, hp]
  have h2S : ∀ v : HeightOneSpectrum (𝓞 F), (2 : 𝓞 F) ∈ v.asIdeal → v ∈ S := fun v hv => by
    simp [hSdef, hv]
  have haS : aU ∈ SUnit (F := F) S := by
    rw [mem_sUnit_iff]; intro p hp; by_contra hne; exact hp (by simp [hSdef, hne])
  have hbS : bU ∈ SUnit (F := F) S := by
    rw [mem_sUnit_iff]; intro p hp; by_contra hne; exact hp (by simp [hSdef, hne])
  obtain ⟨T, hT, hker, hidx⟩ := exists_T a hd s hs hspan S ha0
  have hTcard := card_T_ge S T (a : F) ha0 ⟨aU, haS⟩ rfl hker hidx
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]; intro p hpS hpT; exact (hT p hpT).1 hpS
  set S' := S ∪ T with hS'def
  -- Prop. 6.10
  have hBsq : ∀ y ∈ locSq S S', IsSquare ((y : Fˣ) : F) := by
    intro y hy
    rw [mem_locSq] at hy
    apply isSquare_of_isSquare_local (a : F) S₀ S T hS₀ hS₀S h2S hT hidx (y : Fˣ) y.2
    · intro v hv
      obtain ⟨c, hc⟩ := hy.1 ⟨v, hv⟩
      exact ⟨(c : v.adicCompletion F), by
        have := congrArg Units.val hc
        simpa [Φf, pow_two] using this.symm⟩
    · intro w
      obtain ⟨c, hc⟩ := hy.2 w
      exact ⟨(c : w.Completion), by
        have := congrArg Units.val hc
        simpa [Φi, pow_two] using this.symm⟩
  have hcount := two_pow_le_index_locNorms (a : F) hd s hs hspan σ hσs S T hST h2S hTcard hBsq
  -- the global count
  have hS' : ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S' → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧
      c ∉ p.asIdeal ^ 2 ∧ ∀ q : HeightOneSpectrum (𝓞 F), q ∉ S' → q ≠ p → c ∉ q.asIdeal := by
    intro p hp
    have hp0 : p ∉ S₀ := fun h => hp (Finset.mem_union_left _ (hS₀S h))
    obtain ⟨c, h1, h2, h3⟩ := hS₀ p hp0
    exact ⟨c, h1, h2, fun q hq hqp => h3 q (fun h => hq (Finset.mem_union_left _ (hS₀S h))) hqp⟩
  have hram : ∀ w : HeightOneSpectrum (𝓞 L), under (F := F) w ∉ S' →
      w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    intro w hw
    apply ramificationIdx_eq_one σ s (a : F) hs hσs w
    · have h2 : (2 : 𝓞 F) ∉ (under (F := F) w).asIdeal := fun h =>
        hw (Finset.mem_union_left _ (h2S _ h))
      have := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (under (F := F) w)).mpr h2
      rwa [map_ofNat] at this
    · have := (mem_sUnit_iff S aU).mp haS (under (F := F) w)
        (fun h => hw (Finset.mem_union_left _ h))
      rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq] at this
      simpa [aU] using this
  have hglob := index_normsF_eq σ hσ S' hS' hram
  have hfilt : (S'.filter fun p => ¬ SplitsFin (L := L) p) = S.filter fun p => ¬ SplitsFin (L := L) p := by
    rw [hS'def, Finset.filter_union]
    have : (T.filter fun p => ¬ SplitsFin (L := L) p) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t ht hns
      exact hns (two_primes_of_isSquare σ s (a : F) hs hσs hd t (hT t ht).2.2)
    rw [this, Finset.union_empty]
  rw [hfilt] at hglob
  -- global norms are local norms
  have hglobal : ∀ c : Additive (SUnit (F := F) S'), c ∈ normsF σ S' →
      ∃ x : Lˣ, algebraMap F L ((((Additive.toMul c : SUnit S') : Fˣ)) : F) = (x : L) * σ x := by
    intro c hc
    obtain ⟨x, hx⟩ := hc
    refine ⟨((Additive.toMul x : SUnit _) : Lˣ), ?_⟩
    have := congrArg (fun z => (((Additive.toMul z : SUnit _) : Lˣ) : L)) hx
    simp only [normHom_apply, toMul_add, Subgroup.coe_mul, Units.val_mul, inclS_apply,
      σS_apply] at this
    exact this.symm
  have hle : normsF σ S' ≤ Subgroup.toAddSubgroup (locNorms L S S') := by
    intro c hc
    obtain ⟨x, hxc⟩ := hglobal c hc
    rw [Additive.mem_toAddSubgroup, mem_locNorms]
    exact ⟨fun v => mem_normGroup_of_global (a : F) hd s hs hspan σ hσs _ x _ hxc,
      fun w => mem_normGroup_of_global (a : F) hd s hs hspan σ hσs _ x _ hxc⟩
  have hdvd := AddSubgroup.index_dvd_of_le hle
  rw [Subgroup.index_toAddSubgroup] at hdvd
  have hn0 : (normsF σ S').index ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hglob; exact (pow_ne_zero _ two_ne_zero) hglob.symm
  have hle1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have hge : (normsF σ S').index ≤ (locNorms L S S').index := by
    rw [← hglob] at hcount
    exact Nat.le_of_mul_le_mul_right hcount two_pos
  have heq : (locNorms L S S').index = (normsF σ S').index := le_antisymm hle1 hge
  have hrel := AddSubgroup.relIndex_mul_index hle
  rw [Subgroup.index_toAddSubgroup, heq] at hrel
  have hrel1 : (normsF σ S').relIndex (Subgroup.toAddSubgroup (locNorms L S S')) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) (hrel.trans (one_mul _).symm)
    exact this
  rw [AddSubgroup.relIndex_eq_one] at hrel1
  -- b is a local norm
  set bS : SUnit (F := F) S' := ⟨bU, sUnit_mono Finset.subset_union_left hbS⟩
  have hbloc : bS ∈ locNorms L S S' := by
    rw [mem_locNorms]
    constructor
    · intro v
      have hv := h (NFPlace.finite v.1)
      obtain ⟨y, hy⟩ := (QuadFormsKB.HasseNorm.norm_tensor_iff_hilbert (a : F) hd s hs hspan
        (v.1.adicCompletion F) b hb).mpr hv
      exact ⟨y, by apply Units.ext; simpa [Φf, bS, bU] using hy⟩
    · intro w
      have : CharZero w.Completion :=
        charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
      have hv := h (NFPlace.infinite w)
      obtain ⟨y, hy⟩ := (QuadFormsKB.HasseNorm.norm_tensor_iff_hilbert (a : F) hd s hs hspan
        w.Completion b hb).mpr hv
      exact ⟨y, by apply Units.ext; simpa [Φi, bS, bU] using hy⟩
  have hbN : Additive.ofMul bS ∈ normsF σ S' := hrel1 ((Additive.mem_toAddSubgroup _ _).mpr hbloc)
  obtain ⟨x, hx⟩ := hglobal _ hbN
  -- conclude
  obtain ⟨b₀, b₁, hxb⟩ := hspan (x : L)
  have hσx : σ (x : L) = algebraMap F L b₀ - algebraMap F L b₁ * s := by
    rw [hxb, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσs]; ring
  have hbval : b = b₀ ^ 2 - (a : F) * b₁ ^ 2 := by
    apply (algebraMap F L).injective
    have hx' : algebraMap F L b = (x : L) * σ (x : L) := hx
    rw [hx', hσx, hxb]
    simp only [map_sub, map_mul, map_pow]
    rw [← hs]; ring
  exact hilbertSymbol_eq_one_of_norm F (a : F) b b₀ b₁ hbval

end QuadFormsKB.HN

namespace QuadFormsKB.HasseNorm

open HN

variable {F : Type} [Field F] [NumberField F]

/-- **The Hasse norm theorem for quadratic extensions** (our own proof): for $a, b \in F^\times$, if
$(a,b)_v = 1$ at every place $v$ of $F$, then $(a,b)_F = 1$. This is the input
`NFInputs.hilbert_eq_one_of_everywhere_nf`; it does not use Yamaguchi's formalization (compare the
archived `hilbert_eq_one_of_everywhere_yamaguchi`, `archive/yamaguchi/`).

*Proof.* If $a$ is a square there is nothing to prove; otherwise scale $a$ by a square into $\mathcal O_F$
(`hilbertSymbol_mul_sq_left`) and apply `HN.hasse_norm_integral`: with $L = F(\sqrt a)$, a finite set $S$ of
places (class group generators, dyadic primes, supports of $a, b$) and the auxiliary $T$ (`exists_T`), the
$(S \cup T)$-units that are local norms at $S \cup \infty$ have index $\ge 2^{s'-1}$
(`two_pow_le_index_locNorms`, the second inequality), which is exactly the index $2^{s'-1}$ of the global
norms (`index_normsF_eq`, the first-inequality count); so local norms are global norms, and $b$ is one. -/
@[kb "omeara1963" "§65D, 65:23, p. 186 (Hasse Norm Theorem)"]
theorem hilbert_eq_one_of_everywhere (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ v : NFPlace F, v.hilbert a b = 1) : hilbertSymbol F a b = 1 := by
  classical
  by_cases hsq : IsSquare a
  · obtain ⟨c, rfl⟩ := hsq
    unfold hilbertSymbol
    exact if_pos ⟨1, 0, c, fun h => by simp [Prod.ext_iff] at h, by ring⟩
  obtain ⟨n, d, hdmem, hnd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  have hd0 : (d : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdmem
  set a' : 𝓞 F := n * d
  have ha' : (a' : F) = a * (d : F) ^ 2 := by
    simp only [a', map_mul]
    change (n : F) * (d : F) = _
    rw [← hnd]; field_simp
  have hd' : ¬ IsSquare (a' : F) := by
    rintro ⟨r, hr⟩
    apply hsq
    refine ⟨r / d, ?_⟩
    have : a = (a' : F) / (d : F) ^ 2 := by rw [ha']; field_simp
    rw [this, hr]; field_simp
  have h' : ∀ v : NFPlace F, v.hilbert (a' : F) b = 1 := by
    intro v
    have hv := h v
    cases v with
    | infinite w =>
      simp only [NFPlace.hilbert] at hv ⊢
      rw [ha', map_mul, map_pow, hilbertSymbol_mul_sq_left _ _ _ _
        ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hd0)]
      exact hv
    | finite v =>
      simp only [NFPlace.hilbert] at hv ⊢
      rw [ha', map_mul, map_pow, hilbertSymbol_mul_sq_left _ _ _ _
        ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hd0)]
      exact hv
  have := hasse_norm_integral a' hd' b hb h'
  rw [ha', hilbertSymbol_mul_sq_left _ _ _ _ hd0] at this
  exact this

end QuadFormsKB.HasseNorm

end
