/-
# O'Meara §93E: basic properties of the fundamental invariants

**Setting** (as in `Sec93E.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$ (dyadic
local field: `¬ IsUnit (2 : R)`, `[HenselianLocalRing R]`, `[Finite (ResidueField R)]`, only where needed). A lattice
$L$ is a `Submodule R V`, a Jordan splitting is `hL : IsJordanSplitting Q L Ls`. **Indices are $0$-based**.

**Proves** (O'Meara 1963, §93E, pp. 263–264)
* `fundNormGroup_antitone`, `fundWeight_antitone`: $\mathfrak g_1 \supseteq \cdots \supseteq \mathfrak g_t$ and
  $\mathfrak w_1 \supseteq \cdots \supseteq \mathfrak w_t$;
* `fundNormGroup_zero`: $\mathfrak g_1 = \mathfrak gL$;
* `isRegular_fundSub`, `fundSub_ne_bot`, `fundSub_fg`, `scale_fundSub`: $L^{\mathfrak s_i}$ is regular, non-zero,
  finitely generated, of scale $\mathfrak s_i$ (regularity is a hypothesis on $L$, `IsRegular Q L`);
* `fundNormGroup_eq_sq_add`: $\mathfrak g_i = a_i\mathfrak o^2 + \mathfrak w_i$;
* `isFundNormGenerators_iff`: fundamental norm generators are unique up to $\cong \bmod \mathfrak w_i$ (93:6);
* `normGroup_le_fundNormGroup`: $\mathfrak gL_i \subseteq \mathfrak g_i$;
* `normIdeal_eq_scale_iff_fund`: $\mathfrak nL_i = \mathfrak s_i \iff \mathfrak nL^{\mathfrak s_i} = \mathfrak s_i$;
* `SameFundamentalType.sameJordanType`: the same fundamental type implies the same Jordan type;
* `IsSaturated.isNormGenerator`: for a saturated splitting, $a_i$ is a norm generator of $L_i$ and
  $\mathfrak w_i = \mathfrak wL_i$;
* `sameFundamentalType_iff`: the equivalent form of the same fundamental type.

**Hypotheses added.** Throughout, lattices are finitely generated (`L.FG`), and where regularity of $L^{\mathfrak s_i}$
is used, $L$ is regular (`IsRegular Q L`); O'Meara's lattices on a regular space are regular.
-/
import QuadFormsKB.Literature.OMeara.Sec93Weight
import QuadFormsKB.Literature.OMeara.Sec82Sub

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- The norm $\mathfrak nL$ is the $R$-span of the norm group $\mathfrak gL$ (O'Meara 1963, §93A, p. 252: $\mathfrak nL
= a\mathfrak o$ for $a \in \mathfrak gL$ of largest value). -/
theorem normIdeal_eq_span_normGroup (L : Submodule R V) : normIdeal Q L = span R (normGroup Q L : Set F) := by
  apply le_antisymm
  · exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact Q_mem_normGroup Q hx)
  · rw [span_le]; exact normGroup_subset_normIdeal Q L

theorem fundSub_le (L : Submodule R V) {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    fundSub Q L Ls i ≤ L := fun _ hx => hx.1

theorem le_fundSub {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : Ls i ≤ fundSub Q L Ls i :=
  le_of_le_of_eq le_sup_left (isOrthSum_subA Q hfg hL i).1.sup_eq

theorem fundSub_antitone {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i ≤ j) : fundSub Q L Ls j ≤ fundSub Q L Ls i :=
  subA_mono Q (hL.scale_strictAnti.antitone hij) L

/-- **$\mathfrak g_1 \supseteq \cdots \supseteq \mathfrak g_t$** (O'Meara 1963, §93E, p. 263), from
$L^{\mathfrak s_j} \subseteq L^{\mathfrak s_i}$ for $i \le j$. -/
@[kb "omeara1963" "§93E, p. 263 (g_1 ⊇ ⋯ ⊇ g_t and w_1 ⊇ ⋯ ⊇ w_t)"]
theorem fundNormGroup_antitone {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i ≤ j) :
    fundNormGroup Q L Ls j ≤ fundNormGroup Q L Ls i :=
  normGroup_mono Q (fundSub_antitone Q hL hij)

/-- **$\mathfrak w_1 \supseteq \cdots \supseteq \mathfrak w_t$** (O'Meara 1963, §93E, p. 263). -/
@[kb "omeara1963" "§93E, p. 263 (g_1 ⊇ ⋯ ⊇ g_t and w_1 ⊇ ⋯ ⊇ w_t)"]
theorem fundWeight_antitone {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i ≤ j) :
    fundWeight Q L Ls j ≤ fundWeight Q L Ls i :=
  weight_mono Q (fundSub_antitone Q hL hij)

/-- **$\mathfrak g_1 = \mathfrak gL$** (O'Meara 1963, §93E, p. 263): $\mathfrak sL = \mathfrak sL_1$ so
$L^{\mathfrak s_1} = L$. (`0 : Fin (k+1)` is O'Meara's index $1$.) -/
@[kb "omeara1963" "§93E, p. 263 (the norm group of L is the first fundamental norm group)"]
theorem fundNormGroup_zero {L : Submodule R V} {k : ℕ} {Ls : Fin (k + 1) → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : fundNormGroup Q L Ls 0 = normGroup Q L := by
  have h : fundSub Q L Ls 0 = L := by
    refine subA_eq_self Q ?_
    rw [← hL.split.iSup_eq]
    refine (scale_iSup_le Q hL.split.orth).trans (iSup_le fun j => ?_)
    exact hL.scale_strictAnti.antitone (Fin.zero_le j)
  unfold fundNormGroup
  rw [h]

/-- **$L^{\mathfrak s_i}$ has scale $\mathfrak s_i$** (O'Meara 1963, §93E, p. 263). -/
@[kb "omeara1963" "§93E, p. 263 (L^{s_i} is regular and non-zero)"]
theorem scale_fundSub {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : scale Q (fundSub Q L Ls i) = scale Q (Ls i) :=
  le_antisymm (scale_subA_le Q _ L) (scale_mono Q (le_fundSub Q hfg hL i))

/-- $L^{\mathfrak s_i}$ is finitely generated. -/
@[kb "omeara1963" "§93E, p. 263 (L^{s_i} is regular and non-zero)"]
theorem fundSub_fg {L : Submodule R V} (hfg : L.FG) {t : ℕ} (Ls : Fin t → Submodule R V) (i : Fin t) :
    (fundSub Q L Ls i).FG :=
  FG.of_le hfg (fundSub_le Q L Ls i)

/-- $L^{\mathfrak s_i} \ne 0$. -/
@[kb "omeara1963" "§93E, p. 263 (L^{s_i} is regular and non-zero)"]
theorem fundSub_ne_bot {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : fundSub Q L Ls i ≠ ⊥ := by
  intro h
  have h1 : Ls i = ⊥ := eq_bot_iff.2 (h ▸ le_fundSub Q hfg hL i)
  exact (hL.modular i).1 ((hL.modular i).2.1.symm.trans (h1 ▸ scale_bot Q))

/-- For a non-zero ideal $\mathfrak a$ and a finitely generated lattice $L$, every $y \in L$ has a non-zero
multiple $d y \in L^{\mathfrak a}$, $d \in F^\times$ (the argument of `span_subA`, without finite-dimensionality). -/
theorem exists_smul_mem_subA {a : Submodule R F} (ha0 : a ≠ ⊥) {L : Submodule R V} (hL : L.FG) (y : V)
    (hy : y ∈ L) : ∃ d : F, d ≠ 0 ∧ d • y ∈ subA Q a L := by
  obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
  obtain ⟨⟨n, m⟩, hnm⟩ := IsLocalization.surj (S := F) (nonZeroDivisors R) α
  have hm0 : algebraMap R F (m : R) ≠ 0 := by
    have : (m : R) ≠ 0 := nonZeroDivisors.coe_ne_zero m
    exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 this
  have hnmem : algebraMap R F n ∈ a := by
    rw [← hnm]; exact a.smul_mem (m : R) hα |> fun h => by simpa [Algebra.smul_def, mul_comm] using h
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnm
    exact hα0 ((mul_eq_zero.1 hnm).resolve_right hm0)
  obtain ⟨b, hb0', hb⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors R) (scale_fg Q hL)
  have hd : ∀ s ∈ scale Q L, algebraMap R F (n * b) * s ∈ a := by
    intro s hs
    obtain ⟨r, hr⟩ := hb s hs
    have : algebraMap R F (n * b) * s = algebraMap R F r * algebraMap R F n := by
      have hr' : algebraMap R F r = algebraMap R F b * s := by rw [hr, Algebra.smul_def]
      rw [map_mul, hr']; ring
    rw [this]
    simpa [Algebra.smul_def] using a.smul_mem r hnmem
  have hdb : algebraMap R F (n * b) ≠ 0 := by
    refine (map_ne_zero_iff _ (IsFractionRing.injective R F)).2 (mul_ne_zero hn0 ?_)
    exact nonZeroDivisors.ne_zero hb0'
  refine ⟨algebraMap R F (n * b), hdb, ?_, fun z hz => ?_⟩
  · rw [algebraMap_smul]; exact L.smul_mem _ hy
  · rw [bil_smul_left]; exact hd _ (bil_mem_scale Q hy hz)

/-- **$L^{\mathfrak s_i}$ is regular** (O'Meara 1963, §93E, p. 263) when $L$ is regular. -/
@[kb "omeara1963" "§93E, p. 263 (L^{s_i} is regular and non-zero)"]
theorem isRegular_fundSub {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    IsRegular Q (fundSub Q L Ls i) := by
  intro x hx hxo
  refine hreg x (fundSub_le Q L Ls i hx) fun y hy => ?_
  obtain ⟨d, hd0, hd⟩ := exists_smul_mem_subA Q (hL.modular i).1 hfg y hy
  have := hxo _ hd
  rw [bil_smul_right] at this
  exact (mul_eq_zero.1 this).resolve_left hd0

/-- **$\mathfrak gL_i \subseteq \mathfrak g_i$** (O'Meara 1963, §93E, p. 264), since $L_i \subseteq L^{\mathfrak s_i}$. -/
@[kb "omeara1963" "§93E, p. 264 (gL_i ⊆ g_i)"]
theorem normGroup_le_fundNormGroup {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : normGroup Q (Ls i) ≤ fundNormGroup Q L Ls i :=
  normGroup_mono Q (le_fundSub Q hfg hL i)

/-- **$\mathfrak nL_i = \mathfrak s_i$ if and only if $\mathfrak nL^{\mathfrak s_i} = \mathfrak s_i$**
(O'Meara 1963, §93E, p. 264), from $L^{\mathfrak s_i} = L_i \perp M'$ with $\mathfrak sM' \subsetneq \mathfrak s_i$
and the fact that the fractional ideals of $R$ are totally ordered. -/
@[kb "omeara1963" "§93E, p. 264 (nL_i = s_i iff nL^{s_i} = s_i)"]
theorem normIdeal_eq_scale_iff_fund {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    normIdeal Q (Ls i) = scale Q (Ls i) ↔ fundNormIdeal Q L Ls i = scale Q (Ls i) := by
  have hfgi : (Ls i).FG := FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  have hscale : scale Q (fundSub Q L Ls i) = scale Q (Ls i) := scale_fundSub Q hfg hL i
  constructor
  · intro h
    refine le_antisymm ((normIdeal_le_scale Q _).trans hscale.le) ?_
    rw [← h]; exact normIdeal_mono Q (le_fundSub Q hfg hL i)
  · intro h
    obtain ⟨hsum, hnot⟩ := isOrthSum_subA Q hfg hL i
    generalize (⨆ j : {j // j ≠ i}, subA Q (scale Q (Ls i)) (Ls j)) = M' at hsum hnot
    by_contra hne
    obtain ⟨α, hα0, hαa⟩ := exists_eq_span_singleton (R := R) (scale_fg Q hfgi) (hL.modular i).1
    have hαmem : α ∈ normIdeal Q (fundSub Q L Ls i) := by
      have : α ∈ fundNormIdeal Q L Ls i := by
        rw [h, hαa]; exact mem_span_singleton_self α
      exact this
    rw [fundSub, ← hsum.sup_eq, normIdeal_sup_of_orth Q hsum.orth] at hαmem
    have hM'le : M' ≤ L := (le_sup_right.trans_eq hsum.sup_eq).trans (fundSub_le Q L Ls i)
    have hS1 : (normIdeal Q (Ls i)).FG := FG.of_le (scale_fg Q hfgi) (normIdeal_le_scale Q _)
    have hS2 : (normIdeal Q M').FG :=
      FG.of_le (scale_fg Q (FG.of_le hfg hM'le)) (normIdeal_le_scale Q _)
    have h1 : α ∉ normIdeal Q (Ls i) := by
      intro hm
      apply hne
      refine le_antisymm (normIdeal_le_scale Q _) ?_
      rw [hαa]; exact (span_singleton_le_iff_mem _ _).2 hm
    have h2 : α ∉ normIdeal Q M' := by
      intro hm
      apply hnot
      rw [hαa]
      exact (span_singleton_le_iff_mem _ _).2 (normIdeal_le_scale Q _ hm)
    have key := notMem_iSup_of_fg (S := fun b : Bool => bif b then normIdeal Q (Ls i) else normIdeal Q M')
      (fun b => by cases b <;> assumption) hα0 (fun b => by cases b <;> assumption)
    rw [iSup_bool_eq] at key
    exact key hαmem

/-- **The same fundamental type implies the same Jordan type** (O'Meara 1963, §93E, p. 264): the norm ideal is the
$R$-span of the norm group, so $\mathfrak g_i = \mathfrak g_i'$ gives $\mathfrak nL^{\mathfrak s_i} =
\mathfrak nL'^{\mathfrak s_i}$, and then `normIdeal_eq_scale_iff_fund` applies. -/
@[kb "omeara1963" "§93E, p. 264 (lattices of the same fundamental type are of the same Jordan type)"]
theorem SameFundamentalType.sameJordanType {L : Submodule R V} {L' : Submodule R V'} (hfg : L.FG)
    (hfg' : L'.FG) {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q' L' Ks)
    (h : SameFundamentalType Q Q' L L' Ls Ks) : SameJordanType Q Q' Ls Ks := by
  obtain ⟨ht, hi⟩ := h
  refine ⟨ht, fun i => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hi i
  refine ⟨h2, h1, ?_⟩
  have e : fundNormIdeal Q L Ls i = fundNormIdeal Q' L' Ks (Fin.cast ht i) := by
    unfold fundNormIdeal
    rw [normIdeal_eq_span_normGroup, normIdeal_eq_span_normGroup]
    exact congrArg (fun g : AddSubgroup F => span R (g : Set F)) h3
  rw [normIdeal_eq_scale_iff_fund Q hfg hL i, normIdeal_eq_scale_iff_fund Q' hfg' hK (Fin.cast ht i), ← e, ← h2]

/-- **Saturated splittings** (O'Meara 1963, §93E, p. 264): if $\mathfrak gL_i = \mathfrak g_i$ for all $i$, then any
fundamental norm generators $a_i$ are norm generators of $L_i$ and $\mathfrak w_i = \mathfrak wL_i$. -/
@[kb "omeara1963" "§93E, p. 264 (saturated: a_i is a norm generator of L_i and w_i = wL_i)"]
theorem IsSaturated.isNormGenerator_and_weight {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hs : IsSaturated Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i : Fin t) :
    IsNormGenerator Q (Ls i) (a i) ∧ fundWeight Q L Ls i = weight Q (Ls i) := by
  have hg := hs.2 i
  refine ⟨⟨by rw [hg]; exact (ha i).1, ?_⟩, ?_⟩
  · rw [(ha i).2, normIdeal_eq_span_normGroup Q (Ls i), hg]
    exact normIdeal_eq_span_normGroup Q _
  · have hI : normGroupIdeal Q (fundSub Q L Ls i) = normGroupIdeal Q (Ls i) :=
      le_antisymm (fun z hz r => by rw [hg]; exact hz r) (normGroupIdeal_mono Q (le_fundSub Q hfg hs.1 i))
    show weight Q (fundSub Q L Ls i) = weight Q (Ls i)
    unfold weight
    rw [scale_fundSub Q hfg hs.1 i, hI]

theorem weight_congr {M : Submodule R V} {N : Submodule R V'} (hg : normGroup Q M = normGroup Q' N)
    (hs : scale Q M = scale Q' N) : weight Q M = weight Q' N := by
  have hI : normGroupIdeal Q M = normGroupIdeal Q' N := by
    ext z
    show (∀ r : R, r • z ∈ normGroup Q M) ↔ ∀ r : R, r • z ∈ normGroup Q' N
    rw [hg]
  unfold weight
  rw [hI, hs]

end Basic

section Dyadic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- **$\mathfrak g_i = a_i\mathfrak o^2 + \mathfrak w_i$** (O'Meara 1963, §93E, p. 263), from 93:4 applied to
$L^{\mathfrak s_i}$: for any norm generator $a$ of $L^{\mathfrak s_i}$, the elements of $\mathfrak g_i$ are exactly
the $a\varepsilon^2 + w$ with $\varepsilon \in \mathfrak o$, $w \in \mathfrak w_i$. -/
@[kb "omeara1963" "§93E, p. 263 (g_i = a_i o² + w_i)"]
theorem fundNormGroup_eq_sq_add (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t)
    {a : F} (ha : IsNormGenerator Q (fundSub Q L Ls i) a) :
    (fundNormGroup Q L Ls i : Set F) =
      {z | ∃ ε : R, ∃ w ∈ fundWeight Q L Ls i, z = a * algebraMap R F ε ^ 2 + w} := by
  have hreg' := isRegular_fundSub Q hfg hreg hL i
  have ha0 := ha.ne_zero Q hreg' (fundSub_ne_bot Q hfg hL i)
  ext z
  constructor
  · intro hz
    obtain ⟨ε, hε⟩ := exists_sub_sq_mem_weight Q h2p ha ha0 hz
    exact ⟨ε, z - a * algebraMap R F ε ^ 2, hε, by ring⟩
  · rintro ⟨ε, w, hw, rfl⟩
    refine add_mem ?_ ?_
    · rw [mul_comm]; exact mul_sq_mem_normGroup Q ha.1 ⟨ε, rfl⟩
    · exact normGroupIdeal_subset Q _ ((weight_bounds Q _).2.1 hw)

/-- **Fundamental norm generators are unique up to $\cong \bmod \mathfrak w_i$** (O'Meara 1963, §93E, p. 263, by
93:6): if $a$ are fundamental norm generators, then $a'$ are too iff $a_i \cong a_i' \bmod \mathfrak w_i$ for all
$i$ (`SqEquivMod` with the argument order of 93:6, `isNormGenerator_iff_sqEquivMod`). -/
@[kb "omeara1963" "§93E, p. 263 (a'_i ≅ a_i mod w_i: fundamental norm generators, by 93:6)"]
theorem isFundNormGenerators_iff (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    {a a' : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) :
    IsFundNormGenerators Q L Ls a' ↔ ∀ i, SqEquivMod (fundWeight Q L Ls i) (a i) (a' i) :=
  forall_congr' fun i => isNormGenerator_iff_sqEquivMod Q h2p (isRegular_fundSub Q hfg hreg hL i)
    (fundSub_ne_bot Q hfg hL i) (ha i)

/-- If the fundamental norm groups agree, a fundamental norm generator of $L'$ is a norm generator of
$L^{\mathfrak s_i}$. -/
theorem isNormGenerator_fundSub_of_eq {L : Submodule R V} {L' : Submodule R V'} {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} {i : Fin t} {j : Fin t'}
    (h3 : fundNormGroup Q L Ls i = fundNormGroup Q' L' Ks j) {b : F}
    (hb : IsNormGenerator Q' (fundSub Q' L' Ks j) b) : IsNormGenerator Q (fundSub Q L Ls i) b := by
  refine ⟨?_, ?_⟩
  · have : b ∈ fundNormGroup Q' L' Ks j := hb.1
    exact (show b ∈ fundNormGroup Q L Ls i from h3 ▸ this)
  · rw [hb.2, normIdeal_eq_span_normGroup Q, normIdeal_eq_span_normGroup Q']
    exact congrArg (fun g : AddSubgroup F => span R (g : Set F)) h3.symm

/-- **Equivalent form of the same fundamental type** (O'Meara 1963, §93E, p. 264). For finitely generated regular
lattices $L$, $L'$ with Jordan splittings and fundamental norm generators $a$, $a'$ (over a dyadic local field), $L$
and $L'$ are of the same fundamental type iff $t = t'$ and for all $i$: $\dim L_i = \dim L_i'$,
$\mathfrak s_i = \mathfrak s_i'$, $\mathfrak w_i = \mathfrak w_i'$ and $a_i \cong a_i' \bmod \mathfrak w_i$. -/
@[kb "omeara1963" "§93E, p. 264 (equivalent form of the same fundamental type)"]
theorem sameFundamentalType_iff (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} {L' : Submodule R V'}
    (hfg : L.FG) (hfg' : L'.FG) (hreg : IsRegular Q L) (hreg' : IsRegular Q' L') {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' L' Ks) {a : Fin t → F} {a' : Fin t' → F}
    (ha : IsFundNormGenerators Q L Ls a) (ha' : IsFundNormGenerators Q' L' Ks a') :
    SameFundamentalType Q Q' L L' Ls Ks ↔
      ∃ h : t = t', ∀ i : Fin t, finrank R (Ls i) = finrank R (Ks (Fin.cast h i)) ∧
        scale Q (Ls i) = scale Q' (Ks (Fin.cast h i)) ∧
        fundWeight Q L Ls i = fundWeight Q' L' Ks (Fin.cast h i) ∧
        SqEquivMod (fundWeight Q L Ls i) (a i) (a' (Fin.cast h i)) := by
  have hsc : ∀ (i : Fin t) (j : Fin t'), scale Q (Ls i) = scale Q' (Ks j) →
      scale Q (fundSub Q L Ls i) = scale Q' (fundSub Q' L' Ks j) := fun i j h => by
    rw [scale_fundSub Q hfg hL, scale_fundSub Q' hfg' hK, h]
  constructor
  · rintro ⟨ht, hi⟩
    refine ⟨ht, fun i => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hi i
    refine ⟨h1, h2, weight_congr Q Q' h3 (hsc i _ h2), ?_⟩
    exact (isNormGenerator_iff_sqEquivMod Q h2p (isRegular_fundSub Q hfg hreg hL i)
      (fundSub_ne_bot Q hfg hL i) (ha i)).1 (isNormGenerator_fundSub_of_eq Q Q' h3 (ha' _))
  · rintro ⟨ht, hi⟩
    refine ⟨ht, fun i => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hi i
    refine ⟨h1, h2, ?_⟩
    have hn : IsNormGenerator Q (fundSub Q L Ls i) (a' (Fin.cast ht i)) :=
      (isNormGenerator_iff_sqEquivMod Q h2p (isRegular_fundSub Q hfg hreg hL i)
        (fundSub_ne_bot Q hfg hL i) (ha i)).2 h4
    have e1 := fundNormGroup_eq_sq_add Q h2p hfg hreg hL i hn
    have e2 := fundNormGroup_eq_sq_add Q' h2p hfg' hreg' hK (Fin.cast ht i) (ha' _)
    exact SetLike.coe_injective (by rw [e1, e2, h3])

end Dyadic

end QuadFormsKB.OMeara
