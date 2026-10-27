/-
# O'Meara §65B–§65C: squares of $S$-units, the index $(J_F : P_F J^{S,2}) = 2^s$, and squares at infinitely many spots

**Setting** (as in `Sec65A.lean`): $F$ a number field, $J_F$ = Mathlib's `IdeleGroup (𝓞 F) F`, $S$ a set of finite
spots satisfying O'Meara's conventions (i)–(iv) of §65A (`SConventions S`), $s = \lvert\Omega - S\rvert$.

**Proves**
* Proposition 65:11 (p. 181): an element that is a unit at every spot of $S$ and a square at every spot of
  $\Omega - S$ is a square (`isSquare_of_unit_of_isSquare_outside`). O'Meara deduces it from 65:10 (Herbrand's lemma
  and the Dirichlet unit theorem); here it is deduced from the library's Milne VII, Proposition 6.10 for $n = 2$
  (`HN.isSquare_of_isSquare_local`, with empty auxiliary set $T$), whose proof is the same first-inequality argument;
  condition (iv) supplies the uniformizers it needs;
* Corollary 65:11a (p. 181): $P^S \cap J^{S,2} = (P^S)^2$ (`principalSIdeles_inf_sqSIdeles`);
* Proposition 65:12 (p. 181): $(J_F : P_F J^{S,2}) = (J^S : P^S J^{S,2}) = 2^{s}$ (`index_principal_sup_sqSIdeles`,
  `relIndex_principalSIdeles_sup_sqSIdeles`);
* Proposition 65:19 (p. 184): every element of $F$ is a square at infinitely many spots (`infinite_isSquare_at`).
  O'Meara derives it from 65:17; here it follows from the library's `HN.exists_good_prime` (Milne VII, Lemma 6.2 for
  $n = 2$).
-/
import QuadFormsKB.Literature.OMeara.Sec65A
import QuadFormsKB.Literature.HasseNorm.KummerSquares
import QuadFormsKB.Literature.HasseNorm.GoodPrimes

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {F : Type} [Field F] [NumberField F]

local notation "J" => IdeleGroup (𝓞 F) F

/-! ### Auxiliary lemmas -/

/-- The number field has infinitely many finite spots. -/
theorem infinite_heightOneSpectrum : Infinite (HeightOneSpectrum (𝓞 F)) := by
  classical
  have key : ∀ ℓ : ℕ, ℓ.Prime → ∃ P : HeightOneSpectrum (𝓞 F), ((ℓ : ℕ) : 𝓞 F) ∈ P.asIdeal := by
    intro ℓ hℓ
    have := Fact.mk hℓ
    obtain ⟨Q, hQ, hQℓ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 F)
      (Ideal.span {(ℓ : ℤ)}) (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 F)).injective_int]
        exact bot_le)
    have hmem : (ℓ : ℤ) ∈ Ideal.span {(ℓ : ℤ)} := Ideal.mem_span_singleton_self _
    rw [← hQℓ, Ideal.under, Ideal.mem_comap] at hmem
    have hQ0 : Q ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hmem
      have : ((ℓ : ℤ) : 𝓞 F) = 0 := hmem
      have h2 : (ℓ : ℤ) = 0 := by exact_mod_cast this
      exact hℓ.ne_zero (by exact_mod_cast h2)
    refine ⟨⟨Q, hQ.isPrime, hQ0⟩, ?_⟩
    simpa using hmem
  choose g hg using key
  have hinj : Function.Injective (fun ℓ : {ℓ : ℕ // ℓ.Prime} => g ℓ.1 ℓ.2) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    by_contra hne
    have hne' : a ≠ b := fun e => hne (Subtype.ext e)
    simp only at h
    have h1 := hg a ha
    have h2 := hg b hb
    rw [h] at h1
    have hcop : IsCoprime (a : ℤ) (b : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes ha hb).mpr hne')
    obtain ⟨u, v, huv⟩ := hcop
    have : (1 : 𝓞 F) ∈ (g b hb).asIdeal := by
      have e : (1 : 𝓞 F) = (u : 𝓞 F) * (a : 𝓞 F) + (v : 𝓞 F) * (b : 𝓞 F) := by
        have := congrArg (Int.cast : ℤ → 𝓞 F) huv
        push_cast at this
        exact this.symm
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    exact (g b hb).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have : Infinite {ℓ : ℕ // ℓ.Prime} := Nat.infinite_setOfPred_prime.to_subtype
  exact Infinite.of_injective _ hinj

/-- An element of valuation $\exp(-1)$ at some spot is not a square. -/
theorem not_isSquare_of_valuation {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (h : v.valuation F x = WithZero.exp (-1 : ℤ)) : ¬ IsSquare x := by
  rintro ⟨y, rfl⟩
  rw [map_mul] at h
  have hy : v.valuation F y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at h; exact WithZero.exp_ne_zero h.symm
  have := WithZero.exp_log hy
  rw [← this, ← WithZero.exp_add] at h
  have := WithZero.exp_injective h
  omega

theorem isSquare_mul_sq_iff {K : Type*} [Field K] (u c : K) (hc : c ≠ 0) :
    IsSquare (u * c ^ 2) ↔ IsSquare u := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y / c, by field_simp; linear_combination hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y * c, by ring⟩

theorem ideleAt_unitEmbedding (γ : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ideleAt (IdeleGroup.unitEmbedding (𝓞 F) F γ) v = algebraMap F (v.adicCompletion F) (γ : F) := rfl

theorem ideleAtInf_unitEmbedding (γ : Fˣ) (w : InfinitePlace F) :
    ideleAtInf (IdeleGroup.unitEmbedding (𝓞 F) F γ) w = algebraMap F w.Completion (γ : F) := rfl

theorem valued_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
  QuadFormsKB.HN.valued_algebraMap v x

/-- From condition (iv): for $\mathfrak p \in S$ there is $\gamma \in F^\times$ with
$\lvert\gamma\rvert_\mathfrak p$ of a uniformizer and $\lvert\gamma\rvert_w = 1$ at the other $w \in S$. -/
theorem exists_gamma {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {p : HeightOneSpectrum (𝓞 F)} (hp : p ∈ S) :
    ∃ γ : Fˣ, p.valuation F (γ : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w ∈ S, w ≠ p → w.valuation F (γ : F) = 1 := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  have hπ0 : π ≠ 0 := by
    rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hπ0' : algebraMap F (p.adicCompletion F) π ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F _).injective]; exact hπ0
  obtain ⟨g, ⟨γ, rfl⟩, j, hj, hij⟩ :=
    hS.ideles (IdeleGroup.ofAdicCompletion (𝓞 F) F p (Units.mk0 _ hπ0'))
  refine ⟨γ, ?_, ?_⟩
  · have h := congrArg (fun i => ideleAt i p) hij
    simp only [ideleAt_mul, ideleAt_unitEmbedding, ideleAt_ofAdic_self, Units.val_mk0] at h
    have h2 := congrArg Valued.v h
    rw [map_mul, hj p hp, mul_one, valued_alg, valued_alg] at h2
    exact h2.symm.trans hπ
  · intro w hw hwp
    have h := congrArg (fun i => ideleAt i w) hij
    simp only [ideleAt_mul, ideleAt_unitEmbedding, ideleAt_ofAdic_ne p w hwp] at h
    have h2 := congrArg Valued.v h
    rw [map_mul, hj w hw, mul_one, valued_alg, map_one] at h2
    exact h2.symm

/-- **The $S_0$-uniformizers** needed by `HN.isSquare_of_isSquare_local`, for $S_0 = $ the finite spots outside $S$,
from condition (iv). -/
theorem exists_uniformizer {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S) :
    ∀ p : HeightOneSpectrum (𝓞 F), p ∉ hS.cofinite.toFinset → ∃ c : 𝓞 F, c ∈ p.asIdeal ∧
      c ∉ p.asIdeal ^ 2 ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ∉ hS.cofinite.toFinset → w ≠ p →
        c ∉ w.asIdeal := by
  classical
  intro p hp
  set T := hS.cofinite.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
  have hpS : p ∈ S := by by_contra h; exact hp ((hmemT p).mpr h)
  obtain ⟨γ, hγp, hγw⟩ := exists_gamma hS hpS
  choose x hx0 hxm hxo using fun q : HeightOneSpectrum (𝓞 F) => QuadFormsKB.HN.exists_mem_only q
  have hn : ∀ q : HeightOneSpectrum (𝓞 F), ∃ n : ℕ,
      q.valuation F (γ : F) ≤ WithZero.exp (n : ℤ) := by
    intro q
    have h0 : q.valuation F (γ : F) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact γ.ne_zero
    refine ⟨(WithZero.log (q.valuation F (γ : F))).toNat, ?_⟩
    calc q.valuation F (γ : F) = WithZero.exp (WithZero.log (q.valuation F (γ : F))) :=
          (WithZero.exp_log h0).symm
      _ ≤ _ := WithZero.exp_le_exp.mpr (by exact_mod_cast Int.self_le_toNat _)
  choose n hn using hn
  set N : ℕ := ∑ q ∈ T, n q with hN
  set d : 𝓞 F := ∏ q ∈ T, x q ^ N with hd
  have hdF : ∀ w : HeightOneSpectrum (𝓞 F),
      w.valuation F (d : F) = ∏ q ∈ T, (w.valuation F (x q : F)) ^ N := by
    intro w
    show w.valuation F (algebraMap (𝓞 F) F d) = _
    rw [hd, map_prod]
    simp [map_pow]
  have hdout : ∀ w, w ∉ T → w.valuation F (d : F) = 1 := by
    intro w hw
    rw [hdF]
    refine Finset.prod_eq_one fun q hq => ?_
    have hwq : w ≠ q := fun h => hw (h ▸ hq)
    rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr (hxo q w hwq), one_pow]
  have hxle : ∀ q : HeightOneSpectrum (𝓞 F), q.valuation F (x q : F) ≤ WithZero.exp (-1 : ℤ) := by
    intro q
    show q.valuation F (algebraMap (𝓞 F) F (x q)) ≤ _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (HeightOneSpectrum.intValuation_le_pow_iff_mem q (x q) 1).mpr (by simpa using hxm q)
    simpa using this
  have hdin : ∀ w ∈ T, w.valuation F (d : F) ≤ WithZero.exp (-(N : ℤ)) := by
    intro w hw
    rw [hdF, ← Finset.mul_prod_erase T _ hw]
    rw [Finset.prod_eq_one (fun q hq => by
      have hwq : w ≠ q := fun h => (Finset.mem_erase.mp hq).1 h.symm
      rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr (hxo q w hwq), one_pow]), mul_one]
    calc (w.valuation F (x w : F)) ^ N ≤ (WithZero.exp (-1 : ℤ)) ^ N := pow_le_pow_left' (hxle w) N
      _ = WithZero.exp (-(N : ℤ)) := by
        rw [← WithZero.exp_nsmul]; congr 1; simp
  have hint : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F ((γ : F) * (d : F)) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · calc w.valuation F (γ : F) * w.valuation F (d : F)
            ≤ WithZero.exp (N : ℤ) * WithZero.exp (-(N : ℤ)) := by
            refine mul_le_mul' ?_ (hdin w hw)
            exact (hn w).trans (WithZero.exp_le_exp.mpr (by
              exact_mod_cast Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) hw))
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · rw [hdout w hw]
      have hwS : w ∈ S := by by_contra h; exact hw ((hmemT w).mpr h)
      by_cases hwp : w = p
      · subst hwp; rw [hγp, mul_one]
        exact (WithZero.exp_lt_exp.mpr (by norm_num : (-1 : ℤ) < 0)).le.trans (by simp)
      · rw [hγw w hwS hwp]; simp
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
    ((γ : F) * (d : F)) hint
  have hvc : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F (algebraMap (𝓞 F) F c) =
      w.valuation F (γ : F) * w.valuation F (d : F) := by
    intro w; rw [hc, map_mul]
  have hvp : p.valuation F (algebraMap (𝓞 F) F c) = WithZero.exp (-1 : ℤ) := by
    rw [hvc, hγp, hdout p hp, mul_one]
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hvp, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  · intro h2
    have := (HeightOneSpectrum.intValuation_le_pow_iff_mem p c 2).mpr h2
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F), hvp] at this
    simp at this
  · intro w hw hwp hcw
    have hwS : w ∈ S := by by_contra h; exact hw ((hmemT w).mpr h)
    have hv1 : w.valuation F (algebraMap (𝓞 F) F c) = 1 := by
      rw [hvc, hγw w hwS hwp, hdout w hw, one_mul]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w (K := F)).mp hv1 hcw

theorem eq_one_of_mul_self_eq_one (x : WithZero (Multiplicative ℤ)) (h : x * x = 1) : x = 1 := by
  have hx : x ≠ 0 := by rintro rfl; simp at h
  have := WithZero.exp_log hx
  rw [← this, ← WithZero.exp_add, ← WithZero.exp_zero] at h
  have := WithZero.exp_injective h
  rw [← WithZero.exp_log hx, show WithZero.log x = 0 by omega, WithZero.exp_zero]

theorem unitEmbedding_injective : Function.Injective (IdeleGroup.unitEmbedding (𝓞 F) F) :=
  fun a b h => by
    have : Infinite (HeightOneSpectrum (𝓞 F)) := infinite_heightOneSpectrum
    have v0 : HeightOneSpectrum (𝓞 F) := Classical.arbitrary _
    apply Units.ext
    have := congrArg (fun i => ideleAt i v0) h
    simp only [ideleAt_unitEmbedding] at this
    exact (algebraMap F (v0.adicCompletion F)).injective this

/-- $P^S$ is the image of the $S'$-units, $S' = \Omega_{fin} - S$. -/
theorem range_unitEmbedding_sUnit {S : Set (HeightOneSpectrum (𝓞 F))} (hS : Sᶜ.Finite) :
    ((IdeleGroup.unitEmbedding (𝓞 F) F).comp
      (QuadFormsKB.HN.SUnit (F := F) hS.toFinset).subtype).range = principalSIdeles S := by
  have hmemT : ∀ v, v ∈ hS.toFinset ↔ v ∉ S := fun v => by simp
  ext i
  constructor
  · rintro ⟨⟨γ, hγ⟩, rfl⟩
    refine ⟨fun v hv => ?_, γ, rfl⟩
    have := (QuadFormsKB.HN.mem_sUnit_iff _ _).mp hγ v (fun h => (hmemT v).mp h hv)
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply]
    rw [ideleAt_unitEmbedding, valued_alg, ← HeightOneSpectrum.valuationOfNeZero_eq, this]
    rfl
  · rintro ⟨his, γ, rfl⟩
    refine ⟨⟨γ, ?_⟩, rfl⟩
    rw [QuadFormsKB.HN.mem_sUnit_iff]
    intro w hw
    have hwS : w ∈ S := by by_contra h; exact hw ((hmemT w).mpr h)
    have := his w hwS
    rw [ideleAt_unitEmbedding, valued_alg] at this
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, this]
    rfl

/-- $(P^S : (P^S)^2) = 2^s$, from $\mathfrak u = F_{S'}^\times$ and `HN.index_sq_sUnit` (65:6). -/
theorem relIndex_principal_sq {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S) :
    ((principalSIdeles S).map (powMonoidHom 2)).relIndex (principalSIdeles S) =
      2 ^ (outsideS S).ncard := by
  set T := hS.cofinite.toFinset
  set f := (IdeleGroup.unitEmbedding (𝓞 F) F).comp (QuadFormsKB.HN.SUnit (F := F) T).subtype with hf
  have hinj : Function.Injective f := unitEmbedding_injective.comp Subtype.val_injective
  have h := Subgroup.relIndex_map_map_of_injective (f := f)
    (powMonoidHom 2 : (QuadFormsKB.HN.SUnit (F := F) T) →* _).range ⊤ hinj
  have h1 : (⊤ : Subgroup (QuadFormsKB.HN.SUnit (F := F) T)).map f = principalSIdeles S := by
    rw [← MonoidHom.range_eq_map]; exact range_unitEmbedding_sUnit hS.cofinite
  have h2 : (powMonoidHom 2 : (QuadFormsKB.HN.SUnit (F := F) T) →* _).range.map f =
      (principalSIdeles S).map (powMonoidHom 2) := by
    rw [← range_unitEmbedding_sUnit hS.cofinite, ← hf]
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨f y, ⟨y, rfl⟩, by simp [powMonoidHom]⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y ^ 2, ⟨y, rfl⟩, by simp [powMonoidHom]⟩
  rw [h1, h2, Subgroup.relIndex_top_right] at h
  rw [h]
  have h3 := QuadFormsKB.HN.index_sq_sUnit (F := F) T
  have h4 : Subgroup.toAddSubgroup (powMonoidHom 2 : (QuadFormsKB.HN.SUnit (F := F) T) →* _).range =
      (nsmulAddMonoidHom (α := Additive (QuadFormsKB.HN.SUnit (F := F) T)) 2).range := by
    ext z
    simp only [Additive.mem_toAddSubgroup, MonoidHom.mem_range, AddMonoidHom.mem_range,
      nsmulAddMonoidHom_apply, powMonoidHom_apply]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Additive.ofMul a, by apply Additive.toMul.injective; simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨Additive.toMul a, by simpa using congrArg Additive.toMul ha⟩
  rw [← h4, Subgroup.index_toAddSubgroup] at h3
  have e : (outsideS S).ncard = T.card + Fintype.card (InfinitePlace F) := ncard_outsideS hS.cofinite
  rw [h3, e]
  congr 1
  have : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  unfold NumberField.Units.rank
  omega

/-- **Proposition 65:11** (O'Meara 1963, p. 181): under the conventions (i)–(iv) of §65A, if $\alpha \in F$ is a unit
at every spot of $S$ and a square at every spot of $\Omega - S$ (the finite spots outside $S$ and the infinite
spots), then $\alpha$ is a square in $F$. -/
@[kb "omeara1963" "§65B, 65:11, p. 181 (a unit on S that is a square outside S is a square)"]
theorem isSquare_of_unit_of_isSquare_outside {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S)
    {α : F} (hα : α ≠ 0) (hunit : ∀ v ∈ S, v.valuation F α = 1)
    (hsq : ∀ v ∉ S, IsSquare (algebraMap F (v.adicCompletion F) α))
    (hinf : ∀ w : InfinitePlace F, IsSquare (algebraMap F w.Completion α)) : IsSquare α := by
  classical
  set T := hS.cofinite.toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ v ∉ S := fun v => by simp [hT]
  have := QuadFormsKB.HN.isSquare_of_isSquare_local α T T ∅ (exists_uniformizer hS) (subset_refl _)
    (fun v hv => by
      rw [hmemT]; intro hvS; exact hS.nondyadic v hvS hv)
    (fun t ht => absurd ht (Finset.notMem_empty t))
    (by rw [QuadFormsKB.HN.kerT_empty]; simp)
    (Units.mk0 α hα) (by
      rw [QuadFormsKB.HN.mem_sUnit_iff]
      intro w hw
      simp only [Finset.union_empty, hmemT, not_not] at hw
      rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, Units.val_mk0, hunit w hw]
      rfl)
    (fun v hv => hsq v ((hmemT v).mp hv)) (fun w => hinf w)
  simpa using this

/-- **Corollary 65:11a** (O'Meara 1963, p. 181): $P^S \cap J^{S,2} = (P^S)^2$. -/
@[kb "omeara1963" "§65B, 65:11a, p. 181 (P^S ∩ J^{S,2} = (P^S)²)"]
theorem principalSIdeles_inf_sqSIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S) :
    principalSIdeles S ⊓ sqSIdeles S = (principalSIdeles S).map (powMonoidHom 2) := by
  apply le_antisymm
  · rintro i ⟨⟨his, γ, rfl⟩, -, hsq, hsqinf⟩
    have hγ0 : (γ : F) ≠ 0 := γ.ne_zero
    have hb := isSquare_of_unit_of_isSquare_outside hS hγ0
      (fun v hv => by
        have := his v hv
        rwa [ideleAt_unitEmbedding, valued_alg] at this)
      (fun v hv => by
        have := hsq v hv
        rwa [ideleAt_unitEmbedding] at this)
      (fun w => by
        have := hsqinf w
        rwa [ideleAtInf_unitEmbedding] at this)
    obtain ⟨b, hb⟩ := hb
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    refine ⟨IdeleGroup.unitEmbedding (𝓞 F) F (Units.mk0 b hb0), ⟨?_, ⟨_, rfl⟩⟩, ?_⟩
    · intro v hv
      have h1 := his v hv
      rw [ideleAt_unitEmbedding, valued_alg, hb, map_mul] at h1
      rw [ideleAt_unitEmbedding, valued_alg]
      exact eq_one_of_mul_self_eq_one _ h1
    · simp only [powMonoidHom_apply, pow_two, ← map_mul]
      congr 1
      exact Units.ext hb.symm
  · rintro _ ⟨j, ⟨hjs, hjp⟩, rfl⟩
    refine ⟨⟨(sIdeles S).pow_mem hjs 2, (IdeleGroup.principalSubgroup (𝓞 F) F).pow_mem hjp 2⟩,
      (sIdeles S).pow_mem hjs 2, fun v _ => ⟨ideleAt j v, ?_⟩, fun w => ⟨ideleAtInf j w, ?_⟩⟩
    · simp [powMonoidHom, pow_two]
    · simp [powMonoidHom, pow_two]

/-- **Proposition 65:12, second index** (O'Meara 1963, p. 181): $(J^S : P^S J^{S,2}) = 2^{s}$. -/
@[kb "omeara1963" "§65B, 65:12, p. 181 ((J^S : P^S J^{S,2}) = 2^s)"]
theorem relIndex_principalSIdeles_sup_sqSIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S) :
    (principalSIdeles S ⊔ sqSIdeles S).relIndex (sIdeles S) = 2 ^ (outsideS S).ncard := by
  have hA : sqSIdeles S ≤ sIdeles S := sqSIdeles_le_sIdeles S
  have hP : principalSIdeles S ≤ sIdeles S := inf_le_left
  have hle : principalSIdeles S ⊔ sqSIdeles S ≤ sIdeles S := sup_le hP hA
  have h1 := Subgroup.relIndex_mul_relIndex (sqSIdeles S) (principalSIdeles S ⊔ sqSIdeles S)
    (sIdeles S) le_sup_right hle
  have h2 : (sqSIdeles S).relIndex (principalSIdeles S ⊔ sqSIdeles S) = 2 ^ (outsideS S).ncard := by
    rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right (H := sqSIdeles S)
      (K := principalSIdeles S), inf_comm, principalSIdeles_inf_sqSIdeles hS]
    exact relIndex_principal_sq hS
  rw [h2, relIndex_sqSIdeles hS.nondyadic hS.cofinite] at h1
  have h4 : (4 : ℕ) ^ (outsideS S).ncard = 2 ^ (outsideS S).ncard * 2 ^ (outsideS S).ncard := by
    rw [← mul_pow]; norm_num
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h1

/-- **Proposition 65:12, first index** (O'Meara 1963, p. 181): $(J_F : P_F J^{S,2}) = 2^{s}$. -/
@[kb "omeara1963" "§65B, 65:12, p. 181 ((J_F : P_F J^{S,2}) = 2^s)"]
theorem index_principal_sup_sqSIdeles {S : Set (HeightOneSpectrum (𝓞 F))} (hS : SConventions S) :
    (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sqSIdeles S).index = 2 ^ (outsideS S).ncard := by
  set H := IdeleGroup.principalSubgroup (𝓞 F) F ⊔ sqSIdeles S with hH
  have hJ : sIdeles S ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro i _
    obtain ⟨p, hp, j, hj, rfl⟩ := hS.ideles i
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hp)) (Subgroup.mem_sup_left hj)
  have hHG : H ⊓ sIdeles S = principalSIdeles S ⊔ sqSIdeles S := by
    apply le_antisymm
    · rintro i ⟨hiH, hiG⟩
      obtain ⟨p, hp, a, ha, rfl⟩ := Subgroup.mem_sup.mp hiH
      have hpG : p ∈ sIdeles S := by
        have := (sIdeles S).mul_mem hiG ((sIdeles S).inv_mem (sqSIdeles_le_sIdeles S ha))
        simpa using this
      exact Subgroup.mem_sup.mpr ⟨p, ⟨hpG, hp⟩, a, ha, rfl⟩
    · exact le_inf (sup_le (fun x hx => Subgroup.mem_sup_left hx.2)
        (fun x hx => Subgroup.mem_sup_right hx)) (sup_le (fun x hx => hx.1) (sqSIdeles_le_sIdeles S))
  have h := Subgroup.relIndex_sup_right (K := H) (sIdeles S)
  rw [hJ, Subgroup.relIndex_top_right, ← Subgroup.inf_relIndex_right, hHG] at h
  rw [h]
  exact relIndex_principalSIdeles_sup_sqSIdeles hS

/-- **Proposition 65:19** (O'Meara 1963, p. 184): every element $\theta$ of a number field is a square at infinitely
many (finite) spots. -/
@[kb "omeara1963" "§65C, 65:19, p. 184 (every element is a square at infinitely many spots)"]
theorem infinite_isSquare_at (θ : F) :
    {v : HeightOneSpectrum (𝓞 F) | IsSquare (algebraMap F (v.adicCompletion F) θ)}.Infinite := by
  classical
  have : Infinite (HeightOneSpectrum (𝓞 F)) := infinite_heightOneSpectrum
  by_cases hall : ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) θ)
  · have : {v : HeightOneSpectrum (𝓞 F) | IsSquare (algebraMap F (v.adicCompletion F) θ)} = Set.univ :=
      Set.eq_univ_of_forall hall
    rw [this]; exact Set.infinite_univ
  push Not at hall
  obtain ⟨v0, hv0⟩ := hall
  have hθns : ¬ IsSquare θ := fun ⟨r, hr⟩ => hv0 ⟨algebraMap F _ r, by rw [hr, map_mul]⟩
  obtain ⟨a₀, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (K := F) θ
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : (b : F) ≠ 0 := by
    rw [ne_eq]; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hb0
  set a : 𝓞 F := a₀ * b with ha
  have haθ : (a : F) = θ * (b : F) ^ 2 := by
    have h1 : θ = (a₀ : F) / (b : F) := hab.symm
    rw [ha]; push_cast; rw [h1]; field_simp
  have hans : ¬ IsSquare (a : F) := by rw [haθ, isSquare_mul_sq_iff _ _ hbF]; exact hθns
  have ha0 : a ≠ 0 := by rintro h0; apply hans; rw [h0]; exact ⟨0, by simp⟩
  have hbad : {p : HeightOneSpectrum (𝓞 F) | a ∈ p.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha0)).subset ?_
    intro p hp
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]; exact hp
  obtain ⟨p, hp⟩ := hbad.infinite_compl.nonempty
  have hpa : a ∉ p.asIdeal := hp
  obtain ⟨x, hx1, hx2⟩ := IsConcreteLE.exists_of_lt
    (Ideal.pow_succ_lt_pow (P := p.asIdeal) p.ne_bot 1)
  have hx1' : x ∈ p.asIdeal := by simpa using hx1
  have hvx : p.valuation F (x : F) = WithZero.exp (-1 : ℤ) :=
    QuadFormsKB.HN.valuation_of_mem_not_sq p hx1' hx2
  have hva : p.valuation F (a : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem p).mpr hpa
  have hxns : ¬ IsSquare (x : F) := not_isSquare_of_valuation hvx
  have haxns : ¬ IsSquare ((a : F) * x) :=
    not_isSquare_of_valuation (by rw [map_mul, hva, hvx, one_mul])
  obtain ⟨L, _, _, _, s, hs, hspan⟩ := QuadFormsKB.Lam.exists_quadExt (a : F) hans
  intro hfin
  obtain ⟨t, htB, -, hts, -⟩ :=
    QuadFormsKB.HN.exists_good_prime a hans s hs hspan x hxns haxns hfin.toFinset
  apply htB
  rw [Set.Finite.mem_toFinset]
  show IsSquare (algebraMap F (t.adicCompletion F) θ)
  have hb' : algebraMap F (t.adicCompletion F) (b : F) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap F _).injective]; exact hbF
  have : algebraMap F (t.adicCompletion F) (a : F) =
      algebraMap F (t.adicCompletion F) θ * (algebraMap F (t.adicCompletion F) (b : F)) ^ 2 := by
    rw [haθ, map_mul, map_pow]
  rw [this, isSquare_mul_sq_iff _ _ hb'] at hts
  exact hts

end QuadFormsKB.OMeara
