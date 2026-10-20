/-
# Parametrizing $F^\times/F^{\times2}$ by $(T, \Lambda_S)$

**Layer:** global arithmetic of a number field $F$; finite places = `HeightOneSpectrum (𝓞 F)`.

For a finite set $S$ of finite places containing a set $S_0$ whose primes generate the class group
(`HN.exists_classGroup_generators`), every $\mathfrak p \notin S$ has an "$S_0$-uniformizer" $c_\mathfrak p \in \mathcal O_F$
($\operatorname{ord}_\mathfrak p c_\mathfrak p = 1$, $\operatorname{ord}_\mathfrak w c_\mathfrak p = 0$ for $\mathfrak w \notin S_0 \cup \{\mathfrak p\}$). Then
(Weil 1982, proof of Lemma 4.5.3, p. 105, "we can write $\mathfrak m$ as $\lambda\mathfrak m'$"):

* `exists_sUnit_mul_sq`: an element with even order at every prime outside $S$ is an $S$-unit times a square;
* `exists_sqKernelCond`: for all $S$ containing a suitable finite set, an $S$-unit that is a square at every place of
  $S \cup \infty$ is a square ("$k^\times \cap H_S = k^{\times2}$", Lemma 4.5.3), via the local–global principle for squares
  (`SqLG.isSquare_iff_everywhere`) applied to the finitely many classes of $E_{S_0}/E_{S_0}^2$;
* `sqParam`: the bijection $\{T \subseteq \{\mathfrak p \notin S\}\text{ finite}\} \times \Lambda_S \to F^\times/F^{\times2}$,
  $(T, \lambda) \mapsto [\prod_{\mathfrak p\in T}c_\mathfrak p\cdot u_\lambda]$ ($u_\lambda$ an $S$-unit lifting $\lambda$); $T$ is the set of
  $\mathfrak p \notin S$ where the class has odd order.

Orders: `ordL v x` $= \log v(x) \in \mathbb Z$ (Mathlib's multiplicative valuation $v(x) = \exp(-\operatorname{ord}_v x)$; only parity matters).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.Tamagawa.SquareClassDuality

open Finset NumberField IsDedekindDomain WithZero

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SqDual

variable {F : Type} [Field F] [NumberField F]

/-! ### Orders -/

/-- $\log v(x) \in \mathbb Z$ for $x \in F^\times$ ($= -\operatorname{ord}_v x$). -/
def ordL (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ℤ := WithZero.log (v.valuation F (x : F))

lemma valuation_ne_zero' (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : v.valuation F (x : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr x.ne_zero

lemma valuation_eq_exp_ordL (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = exp (ordL v x) := (exp_log (valuation_ne_zero' v x)).symm

lemma ordL_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) : ordL v (x * y) = ordL v x + ordL v y := by
  unfold ordL
  rw [Units.val_mul, map_mul, log_mul (valuation_ne_zero' v x) (valuation_ne_zero' v y)]

lemma ordL_one (v : HeightOneSpectrum (𝓞 F)) : ordL v 1 = 0 := by simp [ordL]

lemma ordL_inv (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordL v x⁻¹ = -ordL v x := by
  have := ordL_mul v x x⁻¹
  rw [mul_inv_cancel, ordL_one] at this; linarith

lemma ordL_zpow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (k : ℤ) : ordL v (x ^ k) = k * ordL v x := by
  induction k using Int.induction_on with
  | zero => simp [ordL_one]
  | succ k ih => rw [zpow_add_one, ordL_mul, ih]; ring
  | pred k ih =>
    rw [zpow_sub_one, ordL_mul, ih, ordL_inv]; ring

lemma ordL_pow (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) (k : ℕ) : ordL v (x ^ k) = k * ordL v x := by
  rw [← zpow_natCast, ordL_zpow]

lemma ordL_prod (v : HeightOneSpectrum (𝓞 F)) {ι : Type*} (s : Finset ι) (f : ι → Fˣ) :
    ordL v (∏ i ∈ s, f i) = ∑ i ∈ s, ordL v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordL_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ordL_mul, ih]

lemma ordL_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordL v x = 0 ↔ v.valuation F (x : F) = 1 := by
  rw [valuation_eq_exp_ordL, ← exp_zero, exp_inj]

lemma ordL_sUnit {S : Finset (HeightOneSpectrum (𝓞 F))} {u : Fˣ} (hu : u ∈ HN.SUnit S)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : ordL v u = 0 :=
  (ordL_eq_zero_iff v u).mpr (hu v hv)

lemma mem_sUnit_iff {S : Finset (HeightOneSpectrum (𝓞 F))} {u : Fˣ} :
    u ∈ HN.SUnit S ↔ ∀ v ∉ S, ordL v u = 0 :=
  ⟨fun hu v hv => ordL_sUnit hu hv, fun h v hv => (ordL_eq_zero_iff v u).mp (h v hv)⟩

lemma finite_ordL_ne_zero (x : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordL v x ≠ 0}.Finite := by
  refine (HN.finite_support x).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv ⊢
  intro h
  apply hv
  rw [ordL_eq_zero_iff, ← HeightOneSpectrum.valuationOfNeZero_eq, h]
  rfl

/-- A local square has even order. -/
lemma even_ordL_of_isSquare (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ)
    (h : IsSquare (algebraMap F (v.adicCompletion F) (x : F))) : Even (ordL v x) := by
  obtain ⟨z, hz⟩ := h
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [mul_zero, map_eq_zero_iff _ (algebraMap F _).injective] at hz; exact x.ne_zero hz
  have hv := congrArg Valued.v hz
  have hz' : Valued.v z = exp (log (Valued.v z)) := (exp_log ((Valuation.ne_zero_iff _).mpr hz0)).symm
  rw [HN.valued_algebraMap, map_mul, valuation_eq_exp_ordL, hz', ← exp_add, exp_inj] at hv
  exact ⟨_, hv⟩

/-! ### $S_0$-uniformizers -/

/-- **$S_0$-uniformizers** (`HN.exists_classGroup_generators`): a finite set $S_0$ and, for every $\mathfrak p \notin S_0$, an element
$c_\mathfrak p \in \mathcal O_F$ with $\operatorname{ord}_\mathfrak p c_\mathfrak p = 1$ and $c_\mathfrak p \notin \mathfrak w$ for $\mathfrak w \notin S_0$, $\mathfrak w \ne \mathfrak p$. -/
def GenProp (S₀ : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ p : HeightOneSpectrum (𝓞 F), p ∉ S₀ →
    ∃ c : 𝓞 F, c ∈ p.asIdeal ∧ c ∉ p.asIdeal ^ 2 ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S₀ → w ≠ p → c ∉ w.asIdeal

lemma exists_genProp : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), GenProp S₀ := HN.exists_classGroup_generators

/-- The chosen $S_0$-uniformizer at $\mathfrak p \notin S_0$, as an element of $F^\times$. -/
def unifS {S₀ : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (p : HeightOneSpectrum (𝓞 F))
    (hp : p ∉ S₀) : Fˣ :=
  Units.mk0 ((hS₀ p hp).choose : F) (by
    intro h
    have h0 : (hS₀ p hp).choose = 0 := by exact_mod_cast h
    exact (hS₀ p hp).choose_spec.2.1 (h0 ▸ Ideal.zero_mem _))

lemma ordL_unifS_self {S₀ : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ S₀) : ordL p (unifS hS₀ p hp) = -1 := by
  obtain ⟨h1, h2, -⟩ := (hS₀ p hp).choose_spec
  have hle : p.intValuation (hS₀ p hp).choose ≤ exp (-((1 : ℕ) : ℤ)) :=
    (p.intValuation_le_pow_iff_mem _ 1).mpr (by rwa [pow_one])
  have hnle : ¬ p.intValuation (hS₀ p hp).choose ≤ exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((p.intValuation_le_pow_iff_mem _ 2).mp h)
  have hv : p.valuation F ((unifS hS₀ p hp : Fˣ) : F) = p.intValuation (hS₀ p hp).choose :=
    p.valuation_of_algebraMap _
  rw [valuation_eq_exp_ordL] at hv
  rw [← hv, exp_le_exp] at hle hnle
  push_cast at hle hnle
  omega

lemma ordL_unifS_other {S₀ : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ S₀) {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S₀) (hwp : w ≠ p) :
    ordL w (unifS hS₀ p hp) = 0 := by
  obtain ⟨-, -, h3⟩ := (hS₀ p hp).choose_spec
  rw [ordL_eq_zero_iff]
  show w.valuation F (((hS₀ p hp).choose : 𝓞 F) : F) = 1
  rw [w.valuation_of_algebraMap]
  exact (w.intValuation_eq_one_iff_mem_primeCompl _).mpr (h3 w hw hwp)

/-- **Even order outside $S$ means $S$-unit times a square** ($S_0 \subseteq S$; Weil 1982, p. 105): if $\operatorname{ord}_\mathfrak q\sigma$ is
even for every $\mathfrak q \notin S$, then $\sigma = u\,y^2$ with $u \in E_S$. -/
theorem exists_sUnit_mul_sq {S₀ S : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (hsub : S₀ ⊆ S)
    (σ : Fˣ) (heven : ∀ q ∉ S, Even (ordL q σ)) : ∃ u ∈ HN.SUnit S, ∃ y : Fˣ, σ = u * y ^ 2 := by
  classical
  set B := (finite_ordL_ne_zero σ).toFinset.filter (· ∉ S)
  have hBS : ∀ q ∈ B, q ∉ S₀ := fun q hq => fun h => (Finset.mem_filter.mp hq).2 (hsub h)
  set y : Fˣ := ∏ q ∈ B.attach, unifS hS₀ q.1 (hBS q.1 q.2) ^ (-(ordL q.1 σ / 2))
  refine ⟨σ * (y ^ 2)⁻¹, ?_, y, by group⟩
  rw [mem_sUnit_iff]
  intro w hw
  have hwS0 : w ∉ S₀ := fun h => hw (hsub h)
  rw [ordL_mul, ordL_inv, ordL_pow, ordL_prod]
  have hterm : ∀ q ∈ B.attach, ordL w (unifS hS₀ q.1 (hBS q.1 q.2) ^ (-(ordL q.1 σ / 2))) =
      if q.1 = w then ordL w σ / 2 else 0 := by
    intro q _
    rw [ordL_zpow]
    split_ifs with hqw
    · subst hqw; rw [ordL_unifS_self]; ring
    · rw [ordL_unifS_other hS₀ q.1 _ hwS0 (Ne.symm hqw), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_attach B (fun q => if q = w then ordL w σ / 2 else 0),
    Finset.sum_ite_eq' B w]
  split_ifs with hwB
  · obtain ⟨k, hk⟩ := heven w hw
    rw [hk]; push_cast; omega
  · have h0 : ordL w σ = 0 := by
      by_contra h
      exact hwB (Finset.mem_filter.mpr ⟨(finite_ordL_ne_zero σ).mem_toFinset.mpr h, hw⟩)
    rw [h0]; simp

/-! ### The kernel condition for large $S$ (Lemma 4.5.3, $k^\times \cap H_S = k^{\times2}$) -/

lemma isSquare_of_locMap_eq_one_fin {S : Finset (HeightOneSpectrum (𝓞 F))} {u : Fˣ} (hu : locMap S u = 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : IsSquare (algebraMap F (v.adicCompletion F) (u : F)) := by
  have h := congrFun (congrArg Prod.fst hu) ⟨v, hv⟩
  exact (mk_eq_one_iff_isSquare _ (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom u)).mp h

lemma isSquare_of_locMap_eq_one_inf {S : Finset (HeightOneSpectrum (𝓞 F))} {u : Fˣ} (hu : locMap S u = 1)
    (w : InfinitePlace F) : IsSquare (algebraMap F w.Completion (u : F)) := by
  have h := congrFun (congrArg Prod.snd hu) w
  exact (mk_eq_one_iff_isSquare _ (Units.map (algebraMap F w.Completion).toMonoidHom u)).mp h

instance finite_sUnit_sq (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Finite (HN.SUnit S ⧸ (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range) := by
  have h := HN.index_sq_sUnit S
  have hne : (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range.index ≠ 0 := by
    rw [show (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range.index =
      (nsmulAddMonoidHom (α := Additive (HN.SUnit S)) 2).range.index by
        rw [← Subgroup.index_toAddSubgroup]; congr 1, h]
    positivity
  have : (powMonoidHom 2 : HN.SUnit S →* HN.SUnit S).range.FiniteIndex := ⟨hne⟩
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The kernel condition holds for all large $S$** (Weil 1982, Lemma 4.5.3, p. 104: $k^\times \cap H_S = k^{\times2}$ for $S$
large; Weil chooses $S$ so that every unramified quadratic extension has a non-split prime in $S$). Here: for each of the
finitely many non-square classes of $E_{S_0}/E_{S_0}^2$ pick a place where it is not a local square
(`SqLG.isSquare_iff_everywhere`, Dedekind's density argument) and put the finite ones into $S_1$. -/
@[kb "weil1982" "§4.5, Lemma 4.5.3, pp. 104–105 (k^* ∩ H_S = k^{*2} for S large)"]
theorem exists_sqKernelCond {S₀ : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧ ∀ S, S₁ ⊆ S → SqKernelCond S := by
  classical
  set Q₀ := HN.SUnit S₀ ⧸ (powMonoidHom 2 : HN.SUnit S₀ →* HN.SUnit S₀).range
  haveI : Fintype Q₀ := Fintype.ofFinite _
  -- a witnessing place for each non-square class
  have hwit : ∀ q : Q₀, ¬ IsSquare (((Quotient.out q : HN.SUnit S₀) : Fˣ) : F) →
      ∃ v : NFPlace F, ¬ v.atPlace fun K _ _ =>
        IsSquare (algebraMap F K (((Quotient.out q : HN.SUnit S₀) : Fˣ) : F)) := by
    intro q hq
    by_contra h
    push Not at h
    exact hq ((SqLG.isSquare_iff_everywhere _).mpr h)
  set fin : Q₀ → Finset (HeightOneSpectrum (𝓞 F)) := fun q =>
    if hq : ¬ IsSquare (((Quotient.out q : HN.SUnit S₀) : Fˣ) : F) then
      (match (hwit q hq).choose with
        | NFPlace.finite v => {v}
        | NFPlace.infinite _ => ∅)
    else ∅
  refine ⟨S₀ ∪ Finset.univ.biUnion fin, Finset.subset_union_left, fun S hS u hu hloc => ?_⟩
  have hsub : S₀ ⊆ S := Finset.subset_union_left.trans hS
  -- u has even order outside S₀
  have heven : ∀ q ∉ S₀, Even (ordL q u) := by
    intro q _
    by_cases hqS : q ∈ S
    · exact even_ordL_of_isSquare q u (isSquare_of_locMap_eq_one_fin hloc hqS)
    · rw [ordL_sUnit hu hqS]; exact ⟨0, rfl⟩
  obtain ⟨u₀, hu₀, y, rfl⟩ := exists_sUnit_mul_sq hS₀ (Finset.Subset.refl S₀) u heven
  -- u₀ = r * t²
  set q : Q₀ := QuotientGroup.mk ⟨u₀, hu₀⟩
  set r : HN.SUnit S₀ := Quotient.out q
  obtain ⟨t, ht⟩ : ∃ t : HN.SUnit S₀, (⟨u₀, hu₀⟩ : HN.SUnit S₀) = r * t ^ 2 := by
    have : (QuotientGroup.mk r : Q₀) = QuotientGroup.mk ⟨u₀, hu₀⟩ := Quotient.out_eq q
    rw [QuotientGroup.eq] at this
    obtain ⟨t, ht⟩ := this
    refine ⟨t, ?_⟩
    rw [powMonoidHom_apply] at ht
    rw [ht]; group
  have hu₀eq : (u₀ : F) = (r : Fˣ) * ((t : Fˣ) : F) ^ 2 := by
    have := congrArg (fun z : HN.SUnit S₀ => ((z : Fˣ) : F)) ht
    simpa using this
  by_cases hr : IsSquare (((r : HN.SUnit S₀) : Fˣ) : F)
  · obtain ⟨a, ha⟩ := hr
    refine ⟨a * (t : Fˣ) * (y : F), ?_⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, hu₀eq, ha]; ring
  · exfalso
    have hv := (hwit q hr).choose_spec
    have hfin : fin q = (match (hwit q hr).choose with
        | NFPlace.finite v => {v}
        | NFPlace.infinite _ => ∅) := dif_pos hr
    -- r is a local square wherever u₀ y² is
    have key : ∀ (K : Type) [Field K] [Algebra F K], IsSquare (algebraMap F K ((u₀ * y ^ 2 : Fˣ) : F)) →
        IsSquare (algebraMap F K (((r : HN.SUnit S₀) : Fˣ) : F)) := by
      intro K _ _ hK
      obtain ⟨z, hz⟩ := hK
      refine ⟨z * (algebraMap F K (((t : Fˣ) : F) * y))⁻¹, ?_⟩
      have h1 : algebraMap F K (((t : Fˣ) : F) * y) ≠ 0 :=
        (map_ne_zero _).mpr (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
      have h2 : algebraMap F K ((u₀ * y ^ 2 : Fˣ) : F) =
          algebraMap F K (((r : HN.SUnit S₀) : Fˣ) : F) * (algebraMap F K (((t : Fˣ) : F) * y)) ^ 2 := by
        rw [Units.val_mul, Units.val_pow_eq_pow_val, hu₀eq, ← map_pow, ← map_mul]; congr 1; ring
      rw [h2] at hz
      field_simp
      linear_combination hz
    revert hv hfin
    rcases (hwit q hr).choose with w | v
    · intro hv _
      exact hv (key _ (isSquare_of_locMap_eq_one_inf hloc w))
    · intro hv hfin
      have hvS : v ∈ S := by
        apply hS
        refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, ?_⟩)
        rw [hfin]; exact Finset.mem_singleton_self v
      exact hv (key _ (isSquare_of_locMap_eq_one_fin hloc hvS))

lemma GS_mul_sq {S : Finset (HeightOneSpectrum (𝓞 F))} (x z : GS F S) : x * z ^ 2 = x := by
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · show x.1 v * (z.1 v) ^ 2 = x.1 v
    rw [sqCl_sq]; exact mul_one (M := SqCl (v.1.adicCompletion F)) _
  · show x.2 w * (z.2 w) ^ 2 = x.2 w
    rw [sqCl_sq]; exact mul_one (M := SqCl w.Completion) _

/-! ### The parametrization of $F^\times/F^{\times2}$ -/

section Param

open Classical

variable {S₀ S : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (hsub : S₀ ⊆ S)

/-- The finite places outside $S$. -/
abbrev PS (S : Finset (HeightOneSpectrum (𝓞 F))) : Type := {p : HeightOneSpectrum (𝓞 F) // p ∉ S}

include hsub in
lemma not_mem_S₀ (p : PS S) : p.1 ∉ S₀ := fun h => p.2 (hsub h)

/-- $c_\mathfrak p$ for $\mathfrak p \notin S$. -/
def cU (p : PS S) : Fˣ := unifS hS₀ p.1 (not_mem_S₀ hsub p)

/-- $\rho_T = \prod_{\mathfrak p\in T}c_\mathfrak p$. -/
def rhoT (T : Finset (PS S)) : Fˣ := ∏ p ∈ T, cU hS₀ hsub p

lemma ordL_rhoT (T : Finset (PS S)) (q : PS S) : ordL q.1 (rhoT hS₀ hsub T) = if q ∈ T then -1 else 0 := by
  classical
  rw [rhoT, ordL_prod]
  have hterm : ∀ p ∈ T, ordL q.1 (cU hS₀ hsub p) = if p = q then -1 else 0 := by
    intro p _
    split_ifs with hpq
    · subst hpq; exact ordL_unifS_self hS₀ p.1 _
    · exact ordL_unifS_other hS₀ p.1 _ (not_mem_S₀ hsub q) (fun h => hpq (Subtype.ext h.symm))
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' T q]

/-- A lift of $\lambda \in \Lambda_S$ to an $S$-unit. -/
def liftU (d : LamS S) : Fˣ := (Subgroup.mem_map.mp d.2).choose

lemma liftU_mem (d : LamS S) : liftU d ∈ HN.SUnit S := (Subgroup.mem_map.mp d.2).choose_spec.1

lemma locMap_liftU (d : LamS S) : locMap S (liftU d) = d := (Subgroup.mem_map.mp d.2).choose_spec.2

/-- **The parametrization** $(T, \lambda) \mapsto [\rho_T u_\lambda] \in F^\times/F^{\times2}$. -/
def sqParamFun (x : Finset (PS S) × LamS S) : Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range :=
  QuotientGroup.mk (rhoT hS₀ hsub x.1 * liftU x.2)

lemma ordL_rhoT_mul_sUnit (T : Finset (PS S)) {u : Fˣ} (hu : u ∈ HN.SUnit S) (q : PS S) :
    ordL q.1 (rhoT hS₀ hsub T * u) = if q ∈ T then -1 else 0 := by
  rw [ordL_mul, ordL_rhoT, ordL_sUnit hu q.2, add_zero]

include hS₀ hsub in
theorem sqParamFun_injective : Function.Injective (sqParamFun (S := S) hS₀ hsub) := by
  classical
  rintro ⟨T, d⟩ ⟨T', d'⟩ h
  simp only [sqParamFun, QuotientGroup.eq, MonoidHom.mem_range, powMonoidHom_apply] at h
  obtain ⟨y, hy⟩ := h
  have hT : T = T' := by
    ext q
    have h1 := congrArg (ordL q.1) hy
    rw [ordL_pow, ordL_mul, ordL_inv, ordL_rhoT_mul_sUnit hS₀ hsub T (liftU_mem d),
      ordL_rhoT_mul_sUnit hS₀ hsub T' (liftU_mem d')] at h1
    push_cast at h1
    by_cases hq : q ∈ T <;> by_cases hq' : q ∈ T'
    · exact ⟨fun _ => hq', fun _ => hq⟩
    · rw [if_pos hq, if_neg hq'] at h1; omega
    · rw [if_neg hq, if_pos hq'] at h1; omega
    · exact ⟨fun h => absurd h hq, fun h => absurd h hq'⟩
  subst hT
  have hd : d = d' := by
    have h2 : liftU d' = liftU d * y ^ 2 := by
      rw [hy]; group
    have h3 := congrArg (locMap S) h2
    rw [map_mul, map_pow, GS_mul_sq, locMap_liftU, locMap_liftU] at h3
    exact Subtype.ext h3.symm
  rw [hd]

include hS₀ hsub in
theorem sqParamFun_surjective (hker : SqKernelCond S) : Function.Surjective (sqParamFun (S := S) hS₀ hsub) := by
  classical
  intro c
  induction c using QuotientGroup.induction_on with
  | H ρ =>
  have hfinT : {q : PS S | Odd (ordL q.1 ρ)}.Finite := by
    refine ((finite_ordL_ne_zero ρ).preimage Subtype.val_injective.injOn).subset fun q hq => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hq ⊢
    intro h0; rw [h0] at hq; exact (Int.not_odd_iff_even.mpr ⟨0, rfl⟩) hq
  set T := hfinT.toFinset
  set σ := ρ * (rhoT hS₀ hsub T)⁻¹
  have heven : ∀ q ∉ S, Even (ordL q σ) := by
    intro q hq
    have := ordL_rhoT hS₀ hsub T ⟨q, hq⟩
    rw [ordL_mul, ordL_inv, this]
    by_cases hqT : (⟨q, hq⟩ : PS S) ∈ T
    · have hodd : Odd (ordL q ρ) := by simpa [T] using hqT
      rw [if_pos hqT]; simpa using hodd.add_one
    · have hev : ¬ Odd (ordL q ρ) := by simpa [T] using hqT
      rw [if_neg hqT, neg_zero, add_zero]; exact Int.not_odd_iff_even.mp hev
  obtain ⟨u, hu, y, hσ⟩ := exists_sUnit_mul_sq hS₀ hsub σ heven
  set d : LamS S := ⟨locMap S u, Subgroup.mem_map_of_mem _ hu⟩
  refine ⟨(T, d), ?_⟩
  -- u = liftU d * z²
  have hk : (liftU d)⁻¹ * u ∈ HN.SUnit S := (HN.SUnit S).mul_mem ((HN.SUnit S).inv_mem (liftU_mem d)) hu
  have hk1 : locMap S ((liftU d)⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, locMap_liftU]; exact inv_mul_cancel (G := GS F S) _
  obtain ⟨z, hz⟩ := hker _ hk hk1
  have hz0 : z ≠ 0 := by
    rintro rfl; rw [mul_zero] at hz
    exact Units.ne_zero _ hz
  simp only [sqParamFun]
  rw [QuotientGroup.eq, MonoidHom.mem_range]
  refine ⟨Units.mk0 z hz0 * y, ?_⟩
  apply Units.ext
  have hρ : ρ = rhoT hS₀ hsub T * u * y ^ 2 := by
    have : ρ = σ * rhoT hS₀ hsub T := by simp [σ]
    rw [this, hσ, mul_comm, ← mul_assoc]
  have hu' : (u : F) = liftU d * (z * z) := by
    have := congrArg Units.val (show u = liftU d * ((liftU d)⁻¹ * u) by rw [← mul_assoc, mul_inv_cancel, one_mul])
    rw [this, Units.val_mul, hz]
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul,
    Units.val_mk0, hρ]
  rw [hu']
  have h1 : ((rhoT hS₀ hsub T : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h2 : ((liftU d : Fˣ) : F) ≠ 0 := Units.ne_zero _
  have h3 : ((y : Fˣ) : F) ≠ 0 := Units.ne_zero _
  field_simp

/-- **The parametrization** $\{T\} \times \Lambda_S \simeq F^\times/F^{\times2}$ (Weil 1982, Lemma 4.5.3, p. 105; under the kernel
condition). -/
@[kb "weil1982" "§4.5, proof of Lemma 4.5.3, p. 105 (Cl_S = 1: every class is ρ_T times an S-unit)"]
def sqParam (hker : SqKernelCond S) : Finset (PS S) × LamS S ≃ Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range :=
  Equiv.ofBijective _ ⟨sqParamFun_injective hS₀ hsub, sqParamFun_surjective hS₀ hsub hker⟩

lemma sqParam_apply (hker : SqKernelCond S) (x : Finset (PS S) × LamS S) :
    sqParam hS₀ hsub hker x = QuotientGroup.mk (rhoT hS₀ hsub x.1 * liftU x.2) := rfl

end Param

/-! ### $(u, \pi)_v = -1$ for a non-square unit $u$ at a non-dyadic place -/

section Tame

lemma log_valued_sq {K : Type*} [Field K] [Valued K ℤᵐ⁰] {t : K} (ht : t ≠ 0) :
    WithZero.log (Valued.v (t ^ 2)) = 2 * WithZero.log (Valued.v t) := by
  rw [map_pow, WithZero.log_pow]; push_cast; ring

/-- **The tame symbol of a non-square unit and a uniformizer** (Serre III §1.2, Thm. 1, at a non-dyadic place of a number field):
if $v \nmid 2$, $v(a) = 1$, $\operatorname{ord}_v\pi$ is odd and $a$ is not a square in $F_v$, then $(a,\pi)_v = -1$. *Proof:* in
$z^2 = ax^2 + \pi y^2$ the term $\pi y^2$ has odd order, so it is strictly smaller than $z^2$ and $ax^2$; then
$a(x/z)^2 \equiv 1$ to positive order, a square by the local square theorem. -/
@[kb "serre1973" "Ch. III §1.2, Thm. 1 (tame symbol, p odd) [unverified]"]
theorem hilbert_unit_unif_eq_neg_one (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a c : Fˣ)
    (ha : ordL v a = 0) (hc : Odd (ordL v c))
    (hsq : ¬ IsSquare (algebraMap F (v.adicCompletion F) (a : F))) :
    (NFPlace.finite v).hilbert (a : F) (c : F) = -1 := by
  rw [NFPlace.hilbert]
  unfold hilbertSymbol
  split_ifs with h
  · exfalso
    obtain ⟨x, y, z, hne, hxyz⟩ := h
    set A := algebraMap F (v.adicCompletion F) (a : F)
    set C := algebraMap F (v.adicCompletion F) (c : F)
    have hA0 : A ≠ 0 := (map_ne_zero _).mpr a.ne_zero
    have hC0 : C ≠ 0 := (map_ne_zero _).mpr c.ne_zero
    have hvA : Valued.v A = 1 := by
      rw [HN.valued_algebraMap, ← ordL_eq_zero_iff]; exact ha
    have hlogC : Odd (WithZero.log (Valued.v C)) := by
      rw [HN.valued_algebraMap]; unfold ordL at hc; exact hc
    by_cases hy : y = 0
    · -- z² = A x²
      subst hy
      have hx : x ≠ 0 := by
        rintro rfl; apply hne; simp only [zero_pow two_ne_zero, mul_zero, add_zero] at hxyz
        simp [pow_eq_zero_iff two_ne_zero |>.mp hxyz]
      simp only [zero_pow two_ne_zero, mul_zero, add_zero] at hxyz
      apply hsq
      refine ⟨z / x, ?_⟩
      rw [div_mul_div_comm, ← sq, ← sq, hxyz]
      field_simp
    · have hB0 : C * y ^ 2 ≠ 0 := mul_ne_zero hC0 (pow_ne_zero 2 hy)
      have hlogB : Odd (WithZero.log (Valued.v (C * y ^ 2))) := by
        rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hC0)
          ((Valuation.ne_zero_iff _).mpr (pow_ne_zero 2 hy)), log_valued_sq hy]
        exact hlogC.add_even ⟨_, by ring⟩
      by_cases hx : x = 0
      · subst hx
        simp only [zero_pow two_ne_zero, mul_zero, zero_add] at hxyz
        have hz : z ≠ 0 := by rintro rfl; exact hB0 (by rw [← hxyz]; ring)
        have := congrArg (fun t => WithZero.log (Valued.v t)) hxyz
        rw [log_valued_sq hz] at this
        rw [← this] at hlogB
        exact (Int.not_odd_iff_even.mpr ⟨_, by ring⟩) hlogB
      · have hAx0 : A * x ^ 2 ≠ 0 := mul_ne_zero hA0 (pow_ne_zero 2 hx)
        have hlogAx : Even (WithZero.log (Valued.v (A * x ^ 2))) := by
          rw [map_mul, hvA, one_mul, log_valued_sq hx]; exact ⟨_, by ring⟩
        have hne' : Valued.v (A * x ^ 2) ≠ Valued.v (C * y ^ 2) := by
          intro h; rw [h] at hlogAx; exact (Int.not_odd_iff_even.mpr hlogAx) hlogB
        have hmax := Valuation.map_add_of_distinct_val Valued.v hne'
        have hz : z ≠ 0 := by
          rintro rfl
          simp only [zero_pow two_ne_zero] at hxyz
          rw [← hxyz, map_zero] at hmax
          exact (Valuation.ne_zero_iff _).mpr hAx0 (le_antisymm (hmax ▸ le_max_left _ _) zero_le')
        -- the maximum is the even one
        have hlt : Valued.v (C * y ^ 2) < Valued.v (A * x ^ 2) := by
          rcases lt_or_gt_of_ne hne' with h | h
          · exact absurd h (by
              intro hlt'
              have : Valued.v (z ^ 2) = Valued.v (C * y ^ 2) := by rw [hxyz, hmax, max_eq_right hlt'.le]
              have hz2 := log_valued_sq hz
              rw [this] at hz2
              exact (Int.not_odd_iff_even.mpr ⟨_, by rw [hz2]; ring⟩) hlogB)
          · exact h
        -- A x² / z² ≡ 1
        have hz2 : Valued.v (z ^ 2) = Valued.v (A * x ^ 2) := by rw [hxyz, hmax, max_eq_left hlt.le]
        have hz20 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
        have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
          rw [show (4 : v.adicCompletion F) = algebraMap F (v.adicCompletion F) ((4 : 𝓞 F) : F) by
            rw [show ((4 : 𝓞 F) : F) = (4 : F) from map_ofNat (algebraMap (𝓞 F) F) 4, map_ofNat],
            HN.valued_algebraMap, v.valuation_of_algebraMap, v.intValuation_eq_one_iff_mem_primeCompl]
          intro h4
          have : (4 : 𝓞 F) = 2 * 2 := by norm_num
          rw [this] at h4
          exact h2 ((v.isPrime.mem_or_mem h4).elim id id)
        have hsmall : Valued.v (A * x ^ 2 / z ^ 2 - 1) < Valued.v (4 : v.adicCompletion F) := by
          have e : A * x ^ 2 / z ^ 2 - 1 = -(C * y ^ 2) / z ^ 2 := by
            field_simp; linear_combination -hxyz
          rw [e, h4, map_div₀, Valuation.map_neg, hz2, div_lt_one₀ ((Valuation.pos_iff _).mpr hAx0)]
          exact hlt
        obtain ⟨w, hw⟩ := HN.isSquare_of_valued_sub_one_lt v _ hsmall
        apply hsq
        refine ⟨w * z / x, ?_⟩
        have : A = (A * x ^ 2 / z ^ 2) * (z / x) ^ 2 := by field_simp
        rw [this, hw]; ring
  · rfl

end Tame

/-! ### The quadratic characters $\chi_\lambda(\mathfrak p) = \langle\lambda, [c_\mathfrak p]\rangle_S$ -/

section Chars

open Classical

/-- **Reciprocity with one extra place:** if $(a,b)_v = 1$ at every finite $v \notin S \cup \{\mathfrak p\}$ ($\mathfrak p \notin S$), then
$\prod_{v\in S\cup\infty}(a,b)_v = (a,b)_\mathfrak p$ (`HN.hilbert_product_formula_nf`). -/
theorem prod_hilbert_S_inf_eq (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ S)
    (a b : Fˣ) (hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ≠ p → (NFPlace.finite v).hilbert (a : F) (b : F) = 1) :
    (∏ v : S, (NFPlace.finite v.1).hilbert (a : F) (b : F)) *
      ∏ w : InfinitePlace F, (NFPlace.infinite w).hilbert (a : F) (b : F) = (NFPlace.finite p).hilbert (a : F) (b : F) := by
  set hf : S → ℤ := fun v => (NFPlace.finite v.1).hilbert (a : F) (b : F)
  set hi : InfinitePlace F → ℤ := fun w => (NFPlace.infinite w).hilbert (a : F) (b : F)
  have hpm : ∀ v : NFPlace F, v.hilbert (a : F) (b : F) = 1 ∨ v.hilbert (a : F) (b : F) = -1 := by
    intro v; cases v <;> exact HN.hilbertSymbol_eq_one_or _ _ _
  rw [prod_pm_eq_pow hf fun v => hpm _, prod_pm_eq_pow hi fun w => hpm _, ← pow_add]
  obtain ⟨-, heven⟩ := HN.hilbert_product_formula_nf (a : F) (b : F) a.ne_zero b.ne_zero
  set A := Finset.univ.filter fun v : S => hf v = -1
  set B := Finset.univ.filter fun w : InfinitePlace F => hi w = -1
  set P : Set (NFPlace F) := if (NFPlace.finite p).hilbert (a : F) (b : F) = -1 then {NFPlace.finite p} else ∅
  have hE : {v : NFPlace F | v.hilbert (a : F) (b : F) = -1} =
      ((fun v : S => NFPlace.finite v.1) '' (A : Set S) ∪ NFPlace.infinite '' (B : Set (InfinitePlace F))) ∪ P := by
    ext v
    cases v with
    | infinite w => simp [B, hi, P]
    | finite v =>
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
        reduceCtorEq, and_false, exists_false, or_false, A, hf, P]
      constructor
      · intro h
        by_cases hv : v ∈ S
        · exact Or.inl ⟨⟨v, hv⟩, h, rfl⟩
        · by_cases hvp : v = p
          · subst hvp; right; rw [if_pos h]; rfl
          · rw [hout v hv hvp] at h; norm_num at h
      · rintro (⟨v', h, hv'⟩ | h)
        · cases hv'; exact h
        · split_ifs at h with hp'
          · rw [Set.mem_singleton_iff] at h; cases h; exact hp'
          · exact absurd h (Set.notMem_empty _)
  have hinj1 : Function.Injective fun v : S => (NFPlace.finite v.1 : NFPlace F) := fun x y h =>
    Subtype.ext (NFPlace.finite.inj h)
  have hinj2 : Function.Injective (NFPlace.infinite (F := F)) := fun x y h => by cases h; rfl
  have hdisj : Disjoint ((fun v : S => NFPlace.finite v.1) '' (A : Set S))
      (NFPlace.infinite '' (B : Set (InfinitePlace F))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, -, rfl⟩ ⟨w, -, h⟩
    cases h
  have hdisjP : Disjoint ((fun v : S => NFPlace.finite v.1) '' (A : Set S) ∪
      NFPlace.infinite '' (B : Set (InfinitePlace F))) P := by
    simp only [P]
    split_ifs
    · rw [Set.disjoint_singleton_right]
      rintro (⟨v, -, hv⟩ | ⟨w, -, hw⟩)
      · exact hp (by rw [← NFPlace.finite.inj hv]; exact v.2)
      · cases hw
    · exact Set.disjoint_empty _
  have hPfin : P.Finite := by simp only [P]; split_ifs <;> simp
  rw [hE, Set.ncard_union_eq hdisjP (Set.toFinite _) hPfin,
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2,
    Set.ncard_coe_finset, Set.ncard_coe_finset] at heven
  rcases hpm (NFPlace.finite p) with h | h
  · have hP : P = ∅ := by simp [P, h]
    rw [hP, Set.ncard_empty, add_zero] at heven
    rw [heven.neg_one_pow, h]
  · have hP : P = {NFPlace.finite p} := by simp [P, h]
    rw [hP, Set.ncard_singleton] at heven
    have : Odd (A.card + B.card) := by
      rcases heven with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
    rw [this.neg_one_pow, h]

variable {S₀ S : Finset (HeightOneSpectrum (𝓞 F))} (hS₀ : GenProp S₀) (hsub : S₀ ⊆ S)

/-- **The quadratic character** $\chi_\lambda(\mathfrak p) = \langle\lambda, [c_\mathfrak p]\rangle_S$ of $\lambda \in \Lambda_S$ at $\mathfrak p \notin S$. By
reciprocity it equals $(u_\lambda, c_\mathfrak p)_\mathfrak p$, the character of $F(\sqrt{u_\lambda})/F$ at $\mathfrak p$ (`isSquare_of_chiS`). -/
def chiS (d : LamS S) (p : PS S) : ℤ := BS S d (locMap S (cU hS₀ hsub p))

lemma chiS_pm (d : LamS S) (p : PS S) : chiS hS₀ hsub d p = 1 ∨ chiS hS₀ hsub d p = -1 := BS_pm S _ _

lemma BS_one_left (S : Finset (HeightOneSpectrum (𝓞 F))) (y : GS F S) : BS S 1 y = 1 := by
  unfold BS
  show (∏ v : S, hilbCl _ 1 (y.1 v)) * ∏ w : InfinitePlace F, hilbCl _ 1 (y.2 w) = 1
  rw [Finset.prod_eq_one fun v _ => hilbCl_one_left _ _, Finset.prod_eq_one fun w _ => hilbCl_one_left _ _]
  norm_num

lemma chiS_one (p : PS S) : chiS hS₀ hsub 1 p = 1 := BS_one_left S _

lemma BS_mul_right (S : Finset (HeightOneSpectrum (𝓞 F))) (x y y' : GS F S) :
    BS S x (y * y') = BS S x y * BS S x y' := by
  rw [BS_symm, BS_mul, BS_symm S y, BS_symm S y']

/-- $\langle\lambda, [\rho_T]\rangle_S = \prod_{\mathfrak p\in T}\chi_\lambda(\mathfrak p)$. -/
lemma BS_rhoT (d : LamS S) (T : Finset (PS S)) :
    BS S d (locMap S (rhoT hS₀ hsub T)) = ∏ p ∈ T, chiS hS₀ hsub d p := by
  induction T using Finset.induction_on with
  | empty =>
    rw [rhoT, Finset.prod_empty, map_one, Finset.prod_empty, BS_symm]; exact BS_one_left S _
  | insert a T ha ih =>
    rw [rhoT, Finset.prod_insert ha, map_mul, BS_mul_right, ← rhoT, ih, Finset.prod_insert ha, chiS]

/-- **$\chi_\lambda(\mathfrak p) = 1$ forces $u_\lambda$ to be a square at $\mathfrak p$** ($S \supseteq$ dyadic places): by reciprocity
$\chi_\lambda(\mathfrak p) = (u_\lambda, c_\mathfrak p)_\mathfrak p$ (the symbols at the other places outside $S$ are symbols of units), and the
tame symbol of a non-square unit with $c_\mathfrak p$ is $-1$ (`hilbert_unit_unif_eq_neg_one`). So $\mathfrak p$ splits in
$F(\sqrt{u_\lambda})$ whenever $\chi_\lambda(\mathfrak p) = 1$. -/
theorem isSquare_of_chiS (hS : ∀ v : HeightOneSpectrum (𝓞 F), 2 ∈ v.asIdeal → v ∈ S) (d : LamS S) (p : PS S)
    (h : chiS hS₀ hsub d p = 1) :
    IsSquare (algebraMap F (p.1.adicCompletion F) ((liftU d : Fˣ) : F)) := by
  set u := liftU d
  set c := cU hS₀ hsub p
  have hu := liftU_mem d
  have hout : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ≠ p.1 → (NFPlace.finite v).hilbert (u : F) (c : F) = 1 := by
    intro v hv hvp
    refine hilbert_units_nondyadic v (fun h2 => hv (hS v h2)) _ _ (hu v hv) ?_
    rw [← ordL_eq_zero_iff]
    exact ordL_unifS_other hS₀ p.1 _ (fun h0 => hv (hsub h0)) hvp
  have hrec := prod_hilbert_S_inf_eq S p.1 p.2 u c hout
  have hchi : chiS hS₀ hsub d p = (NFPlace.finite p.1).hilbert (u : F) (c : F) := by
    rw [chiS, ← locMap_liftU d, BS_locMap]; exact hrec
  by_contra hsq
  have := hilbert_unit_unif_eq_neg_one p.1 (fun h2 => p.2 (hS _ h2)) u c (ordL_sUnit hu p.2)
    (by simp only [c, cU]; rw [ordL_unifS_self]; exact ⟨-1, by ring⟩) hsq
  rw [hchi, this] at h
  norm_num at h

end Chars

end QuadFormsKB.SqDual
