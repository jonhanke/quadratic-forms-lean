/-
# O'Meara §93G: basic consequences of $2\mathfrak o = \mathfrak p$ (pp. 276–277)

**Setting** (as in `Sec93G.lean`): $R$ a discrete valuation ring with fraction field $F$, `IsTwoAdic R` ($2$ is a prime
element of $R$, so $\pi = 2$ is a uniformizer and $\operatorname{ord} 2 = 1$), `[HenselianLocalRing R]` and
`[Finite (ResidueField R)]` where the weight is involved. Lattices are `Submodule R V`; indices are $0$-based.

**Proves** (O'Meara 1963, §93G, pp. 276–277)
* `twoAdic_no_ideal_between`, `normIdeal_eq_scale_or_two_smul`: there is no fractional ideal strictly between
  $2\mathfrak a$ and $\mathfrak a$, so $\mathfrak nL = \mathfrak sL$ or $\mathfrak nL = 2(\mathfrak sL)$;
* `sameJordanInvariants_iff_sameJordanType`: same Jordan invariants $\iff$ same Jordan type;
* `normIdeal_antitone_of_lt`, `scale_le_two_smul_scale_of_lt`, `scale_succ_le_two_smul_scale`:
  $\mathfrak nL_j \subseteq \mathfrak nL_i$ for $i < j$ and $\mathfrak sL_{i+1} \subseteq 2(\mathfrak sL_i)$;
* `normGroup_eq_normIdeal_twoAdic`, `weight_eq_two_smul_scale_twoAdic`: $\mathfrak gL = \mathfrak nL$ and
  $\mathfrak wL = 2(\mathfrak sL)$;
* `fundNormGroup_eq_normIdeal_twoAdic`, `fundNormIdeal_eq_normIdeal_twoAdic`, `fundWeight_eq_two_smul_scale_twoAdic`:
  $\mathfrak g_i = \mathfrak nL_i$, $\mathfrak nL^{\mathfrak s_i} = \mathfrak nL_i$, $\mathfrak w_i = 2\mathfrak s_i$;
* `isFundNormGenerators_two_pow`: $a_i = 2^{u_i}$ with $u_i = \operatorname{ord}\mathfrak n_i$ are fundamental norm
  generators;
* `sameFundamentalType_of_sameJordanInvariants`, `sameFundamentalInvariants_of_sameJordanInvariants`: lattices with
  the same Jordan invariants have the same fundamental invariants.

**Hypotheses added.** Lattices are finitely generated (`L.FG`) and regular (`IsRegular Q L`), which is O'Meara's
standing assumption of lattices on a regular space; for item 4 also `L ≠ ⊥`. These are the hypotheses already
used in `Sec93EBasic.lean`.
-/
import QuadFormsKB.Literature.OMeara.Sec93G
import QuadFormsKB.Literature.OMeara.Sec93EBasic

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

omit [Invertible (2 : F)] in
theorem twoAdic_irreducible (h2 : IsTwoAdic R) : Irreducible (2 : R) := h2

omit [Invertible (2 : F)] in
theorem twoAdic_dord_two (h2 : IsTwoAdic R) : dord (twoAdic_irreducible h2) (2 : F) = 1 := by
  have := dord_pi (R := R) (F := F) (twoAdic_irreducible h2)
  rwa [map_ofNat] at this

omit [Invertible (2 : F)] in
theorem twoAdic_two_smul_span (α : F) : (2 : F) • (R ∙ α) = R ∙ ((2 : F) * α) := by
  rw [Submodule.smul_span, Set.smul_set_singleton, smul_eq_mul]

/-- If $\beta\mathfrak o \subseteq \alpha\mathfrak o$ then $\beta\mathfrak o = \alpha\mathfrak o$ or
$\beta\mathfrak o \subseteq 2\alpha\mathfrak o$ (since $\operatorname{ord} 2 = 1$). -/
theorem twoAdic_span_cases (h2 : IsTwoAdic R) {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0) (h : (R ∙ β) ≤ R ∙ α) :
    R ∙ β = R ∙ α ∨ R ∙ β ≤ R ∙ ((2 : F) * α) := by
  have hπ := twoAdic_irreducible h2
  have h2ne : (2 : F) ≠ 0 := two_ne_zero' F
  have hd : dord hπ α ≤ dord hπ β := (mem_span_iff hπ hβ hα).mp (h (mem_span_singleton_self β))
  have hd2 : dord hπ (2 * α) = dord hπ α + 1 := by
    rw [dord_mul hπ h2ne hα, twoAdic_dord_two h2]; ring
  rcases eq_or_lt_of_le hd with he | hlt
  · left; exact span_eq_of_dord_eq hπ hβ hα he.symm
  · right
    rw [span_singleton_le_iff_mem, mem_span_iff hπ hβ (mul_ne_zero h2ne hα)]
    omega

/-- **No fractional ideal strictly between $2\mathfrak a$ and $\mathfrak a$** (O'Meara 1963, §93G, p. 276): over a
2-adic field, if $\mathfrak a = \alpha\mathfrak o$ ($\alpha \ne 0$) and $2\mathfrak a \subseteq \mathfrak b \subseteq
\mathfrak a$ for an $\mathfrak o$-submodule $\mathfrak b$ of $F$, then $\mathfrak b = \mathfrak a$ or
$\mathfrak b = 2\mathfrak a$. -/
@[kb "omeara1963" "§93G, p. 276 (no fractional ideal strictly between 2a and a; nL = sL or nL = 2(sL))"]
theorem twoAdic_no_ideal_between (h2 : IsTwoAdic R) {a : Submodule R F} {α : F} (hα : α ≠ 0) (ha : a = R ∙ α)
    {b : Submodule R F} (h1 : (2 : F) • a ≤ b) (h2' : b ≤ a) : b = a ∨ b = (2 : F) • a := by
  subst ha
  have h2ne : (2 : F) ≠ 0 := two_ne_zero' F
  have hb0 : b ≠ ⊥ := by
    intro hb
    have hmem : (2 : F) * α ∈ (2 : F) • (R ∙ α) := by
      rw [twoAdic_two_smul_span]; exact mem_span_singleton_self _
    have := h1 hmem
    rw [hb] at this
    exact mul_ne_zero h2ne hα ((Submodule.mem_bot R).mp this)
  obtain ⟨β, hβ0, rfl⟩ := exists_gen_of_le h2' hb0
  rcases twoAdic_span_cases h2 hα hβ0 h2' with h | h
  · left; exact h
  · right
    rw [twoAdic_two_smul_span] at h1 ⊢
    exact le_antisymm h h1

/-- If $\mathfrak b \subsetneq \alpha\mathfrak o$ then $\mathfrak b \subseteq 2\alpha\mathfrak o$ (consequence of
`twoAdic_span_cases`). -/
theorem twoAdic_le_two_smul_of_lt (h2 : IsTwoAdic R) {a : Submodule R F} {α : F} (hα : α ≠ 0) (ha : a = R ∙ α)
    {b : Submodule R F} (hb : b < a) : b ≤ (2 : F) • a := by
  subst ha
  by_cases hb0 : b = ⊥
  · rw [hb0]; exact bot_le
  obtain ⟨β, hβ0, rfl⟩ := exists_gen_of_le hb.le hb0
  rcases twoAdic_span_cases h2 hα hβ0 hb.le with h | h
  · exact absurd h hb.ne
  · rw [twoAdic_two_smul_span]; exact h

/-- $2(\mathfrak sL) \subseteq \mathfrak nL$. -/
theorem two_smul_scale_le_normIdeal (L : Submodule R V) : (2 : F) • scale Q L ≤ normIdeal Q L :=
  (two_smul_scale_le_normGroupIdeal Q L).trans (normGroupIdeal_le_normIdeal Q L)

/-- **$\mathfrak nL = \mathfrak sL$ or $\mathfrak nL = 2(\mathfrak sL)$** (O'Meara 1963, §93G, p. 276): for a
non-zero regular finitely generated lattice over a 2-adic field, from $2(\mathfrak sL) \subseteq \mathfrak nL
\subseteq \mathfrak sL$ and `twoAdic_no_ideal_between`. -/
@[kb "omeara1963" "§93G, p. 276 (no fractional ideal strictly between 2a and a; nL = sL or nL = 2(sL))"]
theorem normIdeal_eq_scale_or_two_smul (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    normIdeal Q L = scale Q L ∨ normIdeal Q L = (2 : F) • scale Q L := by
  obtain ⟨α, hα, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q hfg) (scale_ne_bot Q hreg hne)
  exact twoAdic_no_ideal_between h2 hα hs (two_smul_scale_le_normIdeal Q L) (normIdeal_le_scale Q L)

/-- The components of a Jordan splitting of a finitely generated lattice are finitely generated, regular, non-zero. -/
theorem twoAdic_component_facts {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    (Ls i).FG ∧ IsRegular Q (Ls i) ∧ Ls i ≠ ⊥ := by
  have hfgi : (Ls i).FG := FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls i)
  exact ⟨hfgi, (hL.modular i).isRegular Q hfgi,
    fun h => (hL.modular i).1 (by rw [h]; exact scale_bot Q)⟩

/-- **Same Jordan invariants $\iff$ same Jordan type** (O'Meara 1963, §93G, p. 276): for Jordan splittings
$L = L_1 \perp \cdots \perp L_t$ and $K = K_1 \perp \cdots \perp K_{t'}$ of finitely generated lattices over a
2-adic field, $t = t'$, $\dim L_i = \dim K_i$, $\mathfrak sL_i = \mathfrak sK_i$, $\mathfrak nL_i = \mathfrak nK_i$ for
all $i$ if and only if the splittings are of the same type (`SameJordanType`): by `normIdeal_eq_scale_or_two_smul`,
$\mathfrak nL_i \in \{\mathfrak sL_i, 2\mathfrak sL_i\}$ is determined by $\mathfrak sL_i$ and whether
$\mathfrak nL_i = \mathfrak sL_i$. -/
@[kb "omeara1963" "§93G, p. 276 (the Jordan invariants: same Jordan invariants iff same Jordan type)"]
theorem sameJordanInvariants_iff_sameJordanType (h2 : IsTwoAdic R) {L : Submodule R V} {K : Submodule R V'}
    (hfg : L.FG) (hfg' : K.FG) {t t' : ℕ} {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'}
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q' K Ks) :
    SameJordanInvariants Q Q' Ls Ks ↔ SameJordanType Q Q' Ls Ks := by
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, fun i => ?_⟩
    obtain ⟨a, b, c⟩ := hi i
    exact ⟨b, a, by rw [b, c]⟩
  · rintro ⟨h, hi⟩
    refine ⟨h, fun i => ?_⟩
    obtain ⟨hs, hr, hn⟩ := hi i
    refine ⟨hr, hs, ?_⟩
    obtain ⟨hfgi, hregi, hnei⟩ := twoAdic_component_facts Q hfg hL i
    obtain ⟨hfgj, hregj, hnej⟩ := twoAdic_component_facts Q' hfg' hK (Fin.cast h i)
    by_cases hc : normIdeal Q (Ls i) = scale Q (Ls i)
    · rw [hc, hn.mp hc, hs]
    · have e1 := (normIdeal_eq_scale_or_two_smul Q h2 hfgi hregi hnei).resolve_left hc
      have e2 := (normIdeal_eq_scale_or_two_smul Q' h2 hfgj hregj hnej).resolve_left (fun h' => hc (hn.mpr h'))
      rw [e1, e2, hs]

/-- **$\mathfrak sL_j \subseteq 2(\mathfrak sL_i)$ for $i < j$** (O'Meara 1963, §93G, p. 276): the scales of a Jordan
splitting are strictly decreasing and there is no fractional ideal strictly between $2\mathfrak a$ and $\mathfrak a$. -/
theorem scale_le_two_smul_scale_of_lt (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i < j) :
    scale Q (Ls j) ≤ (2 : F) • scale Q (Ls i) := by
  obtain ⟨hfgi, -, -⟩ := twoAdic_component_facts Q hfg hL i
  obtain ⟨α, hα, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q hfgi) (hL.modular i).1
  exact twoAdic_le_two_smul_of_lt h2 hα hs (hL.scale_strictAnti hij)

/-- **Consecutive scales** (O'Meara 1963, §93G, p. 276): $\mathfrak sL_{i+1} \subseteq 2(\mathfrak sL_i)$. -/
@[kb "omeara1963" "§93G, p. 276 (nL_{i+1} ⊆ sL_{i+1} ⊆ 2(sL_i) ⊆ nL_i, so n_1 ⊇ ⋯ ⊇ n_t)"]
theorem scale_succ_le_two_smul_scale (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : (j : ℕ) = i + 1) :
    scale Q (Ls j) ≤ (2 : F) • scale Q (Ls i) :=
  scale_le_two_smul_scale_of_lt Q h2 hfg hL (Fin.lt_def.mpr (by omega))

/-- **$\mathfrak n_1 \supseteq \cdots \supseteq \mathfrak n_t$** (O'Meara 1963, §93G, p. 276): for $i < j$,
$\mathfrak nL_j \subseteq \mathfrak sL_j \subseteq 2(\mathfrak sL_i) \subseteq \mathfrak nL_i$. -/
@[kb "omeara1963" "§93G, p. 276 (nL_{i+1} ⊆ sL_{i+1} ⊆ 2(sL_i) ⊆ nL_i, so n_1 ⊇ ⋯ ⊇ n_t)"]
theorem normIdeal_antitone_of_lt (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : i < j) :
    normIdeal Q (Ls j) ≤ normIdeal Q (Ls i) :=
  (normIdeal_le_scale Q _).trans
    ((scale_le_two_smul_scale_of_lt Q h2 hfg hL hij).trans (two_smul_scale_le_normIdeal Q _))

/-- **$\mathfrak nL^{\mathfrak s_i} = \mathfrak nL_i$** (O'Meara 1963, §93G, p. 277): $L^{\mathfrak s_i} = L_i \perp M'$
with $\mathfrak sM' \subsetneq \mathfrak s_i$, so $\mathfrak nM' \subseteq \mathfrak sM' \subseteq 2\mathfrak s_i \subseteq
\mathfrak nL_i$. -/
@[kb "omeara1963" "§93G, p. 277 (g_i = n_i, w_i = 2s_i)"]
theorem fundNormIdeal_eq_normIdeal_twoAdic (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    fundNormIdeal Q L Ls i = normIdeal Q (Ls i) := by
  obtain ⟨hfgi, -, -⟩ := twoAdic_component_facts Q hfg hL i
  obtain ⟨hsum, hnot⟩ := isOrthSum_subA Q hfg hL i
  generalize (⨆ j : {j // j ≠ i}, subA Q (scale Q (Ls i)) (Ls j)) = M' at hsum hnot
  have hM'le : M' ≤ fundSub Q L Ls i := le_sup_right.trans_eq hsum.sup_eq
  have hsc : scale Q M' < scale Q (Ls i) :=
    lt_of_le_of_ne ((scale_mono Q hM'le).trans (scale_fundSub Q hfg hL i).le) (fun h => hnot h.ge)
  obtain ⟨σ, hσ0, hσ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q hfgi) (hL.modular i).1
  have h2s : scale Q M' ≤ (2 : F) • scale Q (Ls i) := twoAdic_le_two_smul_of_lt h2 hσ0 hσ hsc
  have hM'n : normIdeal Q M' ≤ normIdeal Q (Ls i) :=
    (normIdeal_le_scale Q M').trans (h2s.trans (two_smul_scale_le_normIdeal Q _))
  have : fundNormIdeal Q L Ls i = normIdeal Q (Ls i) ⊔ normIdeal Q M' := by
    unfold fundNormIdeal fundSub
    rw [← hsum.sup_eq, normIdeal_sup_of_orth Q hsum.orth]
  rw [this]
  exact sup_eq_left.mpr hM'n

end Basic

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable {V' : Type*} [AddCommGroup V'] [Module F V'] [Module R V'] [IsScalarTower R F V']
variable (Q : QuadraticForm F V) (Q' : QuadraticForm F V')

/-- Core of $\mathfrak gL = \mathfrak nL$ and $\mathfrak wL = 2(\mathfrak sL)$: $\mathfrak mL = \mathfrak nL$ and
$\mathfrak wL = 2(\mathfrak sL)$. With $a$ a norm generator, $\mathfrak mL = m\mathfrak o$, $\mathfrak sL = \sigma\mathfrak o$:
$\operatorname{ord}\sigma \le \operatorname{ord} a \le \operatorname{ord} m \le \operatorname{ord}\sigma + 1$ (from
$2(\mathfrak sL) \subseteq \mathfrak mL \subseteq \mathfrak nL \subseteq \mathfrak sL$) and
$\operatorname{ord} a + \operatorname{ord} m$ even force $\operatorname{ord} a = \operatorname{ord} m$. -/
theorem twoAdic_normGroupIdeal_and_weight (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) :
    normGroupIdeal Q L = normIdeal Q L ∧ weight Q L = (2 : F) • scale Q L := by
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  have h2ne : (2 : F) ≠ 0 := two_ne_zero' F
  have hπ2 : algebraMap R F (2 : R) = (2 : F) := map_ofNat _ 2
  obtain ⟨x, -, ha⟩ := exists_isNormGenerator_Q Q hfg
  have ha0 := ha.ne_zero Q hreg hne
  obtain ⟨σ, hσ0, hσ⟩ := exists_eq_span_singleton (R := R) (scale_fg Q hfg) (scale_ne_bot Q hreg hne)
  obtain ⟨m, hm0, hm, hev, hcase⟩ := weight_cases Q h2p hπ ha ha0
  rw [hπ2] at hcase
  have h2σ0 : (2 : F) * σ ≠ 0 := mul_ne_zero h2ne hσ0
  have h2σ : dord hπ (2 * σ) = dord hπ σ + 1 := by
    rw [dord_mul hπ h2ne hσ0, twoAdic_dord_two h2]; ring
  have h2σmem : (2 : F) * σ ∈ (2 : F) • scale Q L := by
    rw [hσ, twoAdic_two_smul_span]; exact mem_span_singleton_self _
  have d1 : dord hπ σ ≤ dord hπ (Q x) := by
    refine (mem_span_iff hπ ha0 hσ0).mp ?_
    rw [← hσ]
    exact normIdeal_le_scale Q L (ha.2 ▸ mem_span_singleton_self (Q x))
  have d2 : dord hπ (Q x) ≤ dord hπ m := by
    refine (mem_span_iff hπ hm0 ha0).mp ?_
    rw [ha.2]
    exact normGroupIdeal_le_normIdeal Q L (hm ▸ mem_span_singleton_self m)
  have d3 : dord hπ m ≤ dord hπ σ + 1 := by
    rw [← h2σ]
    refine (mem_span_iff hπ h2σ0 hm0).mp ?_
    rw [← hm]
    exact two_smul_scale_le_normGroupIdeal Q L h2σmem
  have d4 : dord hπ (Q x) = dord hπ m := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hmn : normGroupIdeal Q L = normIdeal Q L := by
    rw [hm, ← ha.2]; exact (span_eq_of_dord_eq hπ hm0 ha0 d4.symm)
  refine ⟨hmn, ?_⟩
  rcases hcase with hA | ⟨hB1, hB2⟩
  · have hdm : dord hπ m = dord hπ σ := by
      by_contra hne'
      have hd1 : dord hπ m = dord hπ σ + 1 := by omega
      have hmem : (2 : F) * σ ∈ weight Q L := (weight_bounds Q L).2.2.1 h2σmem
      have h2m : (2 : F) * m ≠ 0 := mul_ne_zero h2ne hm0
      rw [hA, mem_span_iff hπ h2σ0 h2m, dord_mul hπ h2ne hm0, h2σ, twoAdic_dord_two h2] at hmem
      omega
    rw [hA, hσ, ← twoAdic_two_smul_span, span_eq_of_dord_eq hπ hm0 hσ0 hdm]
  · exact hB1.trans hB2

/-- **$\mathfrak gL = \mathfrak nL$** (O'Meara 1963, §93G, p. 277): over a 2-adic local field, for a non-zero regular
finitely generated lattice $L$, the norm group equals the norm, as sets. From $2(\mathfrak sL) \subseteq \mathfrak mL
\subseteq \mathfrak gL \subseteq \mathfrak nL$, $\operatorname{ord}\mathfrak mL + \operatorname{ord}\mathfrak nL$ even
and no ideal strictly between $2\mathfrak sL$ and $\mathfrak sL \supseteq \mathfrak nL \supseteq 2\mathfrak sL$. -/
@[kb "omeara1963" "§93G, p. 277 (gL = nL and wL = 2(sL) in the 2-adic case)"]
theorem normGroup_eq_normIdeal_twoAdic (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) : (normGroup Q L : Set F) = normIdeal Q L := by
  have h := (twoAdic_normGroupIdeal_and_weight Q h2 hfg hreg hne).1
  refine Set.Subset.antisymm (normGroup_subset_normIdeal Q L) ?_
  rw [← h]
  exact normGroupIdeal_subset Q L

/-- **$\mathfrak wL = 2(\mathfrak sL)$** (O'Meara 1963, §93G, p. 277): over a 2-adic local field, for a non-zero regular
finitely generated lattice $L$. -/
@[kb "omeara1963" "§93G, p. 277 (gL = nL and wL = 2(sL) in the 2-adic case)"]
theorem weight_eq_two_smul_scale_twoAdic (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) (hne : L ≠ ⊥) : weight Q L = (2 : F) • scale Q L :=
  (twoAdic_normGroupIdeal_and_weight Q h2 hfg hreg hne).2

/-- **$\mathfrak g_i = \mathfrak nL_i$** (O'Meara 1963, §93G, p. 277): the fundamental norm group
$\mathfrak g_i = \mathfrak gL^{\mathfrak s_i}$ of a Jordan splitting of a finitely generated regular lattice over a
2-adic field is the norm of $L_i$ (as sets). -/
@[kb "omeara1963" "§93G, p. 277 (g_i = n_i, w_i = 2s_i)"]
theorem fundNormGroup_eq_normIdeal_twoAdic (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    (fundNormGroup Q L Ls i : Set F) = normIdeal Q (Ls i) := by
  have h := normGroup_eq_normIdeal_twoAdic Q h2 (fundSub_fg Q hfg Ls i) (isRegular_fundSub Q hfg hreg hL i)
    (fundSub_ne_bot Q hfg hL i)
  exact h.trans (congrArg (fun S : Submodule R F => (S : Set F))
    (fundNormIdeal_eq_normIdeal_twoAdic Q h2 hfg hL i))

/-- **$\mathfrak w_i = 2\mathfrak s_i$** (O'Meara 1963, §93G, p. 277). -/
@[kb "omeara1963" "§93G, p. 277 (g_i = n_i, w_i = 2s_i)"]
theorem fundWeight_eq_two_smul_scale_twoAdic (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (i : Fin t) :
    fundWeight Q L Ls i = (2 : F) • scale Q (Ls i) := by
  have h := weight_eq_two_smul_scale_twoAdic Q h2 (fundSub_fg Q hfg Ls i) (isRegular_fundSub Q hfg hreg hL i)
    (fundSub_ne_bot Q hfg hL i)
  exact h.trans (by rw [scale_fundSub Q hfg hL i])

/-- **$a_i = 2^{u_i}$ are fundamental norm generators** (O'Meara 1963, §93G, p. 277): if $2^{u_i}\mathfrak o =
\mathfrak nL_i$ ($u_i = \operatorname{ord}\mathfrak n_i$) for every $i$, then $a_i = 2^{u_i}$ is a norm generator of
$L^{\mathfrak s_i}$ for every $i$. -/
@[kb "omeara1963" "§93G, p. 277 (u_i = ord n_i; a_i = 2^{u_i} are fundamental norm generators)"]
theorem isFundNormGenerators_two_pow (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    {u : Fin t → ℤ} (hu : ∀ i, R ∙ ((2 : F) ^ u i) = normIdeal Q (Ls i)) :
    IsFundNormGenerators Q L Ls (fun i => (2 : F) ^ u i) := by
  intro i
  refine ⟨?_, (hu i).trans (fundNormIdeal_eq_normIdeal_twoAdic Q h2 hfg hL i).symm⟩
  have h : (2 : F) ^ u i ∈ (fundNormGroup Q L Ls i : Set F) := by
    rw [fundNormGroup_eq_normIdeal_twoAdic Q h2 hfg hreg hL i, ← hu i]
    exact mem_span_singleton_self _
  exact h

/-- **The same Jordan invariants give the same fundamental type** (O'Meara 1963, §93G, p. 277): for finitely generated
regular lattices $L$, $K$ with Jordan splittings having the same Jordan invariants, $\mathfrak g_i = \mathfrak nL_i =
\mathfrak nK_i = \mathfrak g_i'$, so $L$ and $K$ are of the same fundamental type. -/
@[kb "omeara1963" "§93G, p. 277 (lattices with the same Jordan invariants have the same fundamental invariants)"]
theorem sameFundamentalType_of_sameJordanInvariants (h2 : IsTwoAdic R) {L : Submodule R V}
    {K : Submodule R V'} (hfg : L.FG) (hfg' : K.FG) (hreg : IsRegular Q L) (hreg' : IsRegular Q' K) {t t' : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t' → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (h : SameJordanInvariants Q Q' Ls Ks) :
    SameFundamentalType Q Q' L K Ls Ks := by
  obtain ⟨ht, hi⟩ := h
  refine ⟨ht, fun i => ?_⟩
  obtain ⟨h1, h2', h3⟩ := hi i
  refine ⟨h1, h2', ?_⟩
  apply SetLike.coe_injective
  rw [fundNormGroup_eq_normIdeal_twoAdic Q h2 hfg hreg hL i,
    fundNormGroup_eq_normIdeal_twoAdic Q' h2 hfg' hreg' hK (Fin.cast ht i), h3]

/-- **The same Jordan invariants give the same fundamental invariants** (O'Meara 1963, §93G, p. 277): with the
hypotheses of `sameFundamentalType_of_sameJordanInvariants` (and the same number $t$ of components), if
$2^{u_i}\mathfrak o = \mathfrak nL_i$ for all $i$, then $L$ and $K$ have the same set of fundamental invariants, with
fundamental norm generators $a_i = 2^{u_i}$. -/
@[kb "omeara1963" "§93G, p. 277 (lattices with the same Jordan invariants have the same fundamental invariants)"]
theorem sameFundamentalInvariants_of_sameJordanInvariants (h2 : IsTwoAdic R) {L : Submodule R V}
    {K : Submodule R V'} (hfg : L.FG) (hfg' : K.FG) (hreg : IsRegular Q L) (hreg' : IsRegular Q' K) {t : ℕ}
    {Ls : Fin t → Submodule R V} {Ks : Fin t → Submodule R V'} (hL : IsJordanSplitting Q L Ls)
    (hK : IsJordanSplitting Q' K Ks) (h : SameJordanInvariants Q Q' Ls Ks) {u : Fin t → ℤ}
    (hu : ∀ i, R ∙ ((2 : F) ^ u i) = normIdeal Q (Ls i)) :
    SameFundamentalInvariants Q Q' L K Ls Ks (fun i => (2 : F) ^ u i) := by
  refine ⟨sameFundamentalType_of_sameJordanInvariants Q Q' h2 hfg hfg' hreg hreg' hL hK h,
    isFundNormGenerators_two_pow Q h2 hfg hreg hL hu, ?_⟩
  obtain ⟨ht, hi⟩ := h
  refine isFundNormGenerators_two_pow Q' h2 hfg' hreg' hK (fun i => ?_)
  have hc : Fin.cast ht i = i := Fin.ext rfl
  have := (hi i).2.2
  rw [hc] at this
  rw [hu i, this]

end Main

end QuadFormsKB.OMeara
