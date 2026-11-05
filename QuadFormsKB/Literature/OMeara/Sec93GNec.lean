/-
# O'Meara §93G: necessity in 93:29 from 93:28 (p. 277)

**Setting** (as in `Sec93G.lean`, `Sec93GBasic.lean`): $R$ a discrete valuation ring with fraction field $F$,
`IsTwoAdic R` ($2\mathfrak o = \mathfrak p$, so $\pi = 2$ is a uniformizer), `[HenselianLocalRing R]` and
`[Finite (ResidueField R)]`; lattices are `Submodule R V`; indices are $0$-based and `j = i + 1` stands for
O'Meara's consecutive indices $i, i+1$.

**Proves** (O'Meara 1963, §93G, proof of 93:29, step 1, p. 277)
* `normIdeal_mul_le_scale_sq_mul_fIdeal`: $\mathfrak n_i\mathfrak n_{i+1} \subseteq \mathfrak s_i^2\mathfrak f_i$
  ("direct calculation from Example 93:26");
* `fIdeal_le_eight_of_lt`: $\mathfrak n_i\mathfrak n_{i+1} \subsetneq \mathfrak s_i^2\mathfrak f_i \Rightarrow
  \mathfrak f_i \subseteq 8\mathfrak o$;
* `fIdeal_lt_four_mul_of_normIdeal_lt`: $\mathfrak n_{i+1} \subsetneq 4\mathfrak n_i \Rightarrow \mathfrak f_i \subsetneq
  4\mathfrak n_i\mathfrak w_i^{-1}$ (with $\mathfrak n_i = a\mathfrak o$, in the form `(4 * a) • (1 / w_i)` of 93:28 (iii));
* `cls_eq_imp_of_dyadicClassification`: the "only if" half of 93:29, conditional on the named statement
  `DyadicClassification` (93:28); the Local Square Theorem is `isSquare_one_add_four_mul`.

Proof idea. With $a_i = 2^{u_i}$, $\mathfrak n_i = 2^{u_i}\mathfrak o$ and $\mathfrak s_i = \sigma\mathfrak o$ one has
$s \le u_i \le s + 1$ ($s = \operatorname{ord}\sigma$), and $\operatorname{ord}\tau \ge s + 1$ for $\mathfrak s_{i+1} =
\tau\mathfrak o$. By 93:26 (`mul_fIdeal_of_odd`, `mul_fIdeal_of_even`) $\mathfrak s_i^2\mathfrak f_i = 2^k\mathfrak o$ with
$k = u_i + u_{i+1}$ if that is odd and $k = \frac12(u_i + u_{i+1}) + s + 1$ if it is even (in the even case the terms
$\mathfrak d(a_ia_{i+1})$, $a_i\mathfrak w_{i+1}$, $a_{i+1}\mathfrak w_i$ all lie in $a_ia_{i+1}\mathfrak o \subseteq
2\mathfrak p^{\frac12(u_i+u_{i+1})+s}$). Everything else is order arithmetic.

**Hypotheses added.** None to the statements asked for. The lattice $L$ is finitely generated and regular
(`IsRegular Q L`), which is O'Meara's standing assumption (and automatic for a lattice on a regular space); the main
theorem assumes `[FiniteDimensional F V]` as `DyadicClassification` does.
-/
import QuadFormsKB.Literature.OMeara.Sec93EFund
import QuadFormsKB.Literature.OMeara.Sec93GBasic

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

namespace Nec93

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

lemma dord_two_zpow (h2 : IsTwoAdic R) (u : ℤ) :
    dord (twoAdic_irreducible h2) ((2 : F) ^ u) = u := by
  have := dord_zpow (R := R) (F := F) (twoAdic_irreducible h2) u
  rwa [map_ofNat] at this

lemma two_zpow_ne_zero (u : ℤ) : (2 : F) ^ u ≠ 0 := zpow_ne_zero _ (two_ne_zero' F)

lemma mem_span_two_zpow_iff (h2 : IsTwoAdic R) {x : F} (hx : x ≠ 0) (k : ℤ) :
    x ∈ R ∙ ((2 : F) ^ k) ↔ k ≤ dord (twoAdic_irreducible h2) x := by
  have := mem_span_zpow_iff (R := R) (F := F) (twoAdic_irreducible h2) hx k
  rwa [map_ofNat] at this

lemma four_mul_two_zpow (u : ℤ) : (4 : F) * (2 : F) ^ u = (2 : F) ^ (u + 2) := by
  have h : (2 : F) ^ (2 : ℤ) = 4 := by norm_num
  rw [zpow_add₀ (two_ne_zero' F), h]; ring

lemma one_div_span {w : F} (hw : w ≠ 0) : (1 : Submodule R F) / (R ∙ w) = R ∙ w⁻¹ := by
  ext z
  rw [FIdealAux.mem_div_span_iff, Submodule.mem_one, mem_span_singleton]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [Algebra.smul_def, hr]; field_simp⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [Algebra.smul_def]; field_simp⟩

lemma mul_div_span_cancel {c : F} (hc : c ≠ 0) (f : Submodule R F) : ((R ∙ c) * f) / (R ∙ c) = f := by
  ext z
  rw [FIdealAux.mem_div_span_iff, mul_comm z c, FundAux.mul_mem_span_mul_iff hc]

omit [Invertible (2 : F)] in
/-- The Local Square Theorem consequence: if $\alpha \cong 1 \bmod \mathfrak f$ with $\mathfrak f \subseteq 8\mathfrak o$
then $\alpha \cong 1 \bmod \mathfrak a$ for every $\mathfrak a$ (indeed $\alpha$ is a unit square). -/
lemma sqEquivMod_of_le_eight [HenselianLocalRing R] (h2 : IsTwoAdic R) {f N : Submodule R F}
    (hf : f ≤ R ∙ (8 : F)) {α : F} (h : SqEquivMod f α 1) : SqEquivMod N α 1 := by
  obtain ⟨⟨u, hu, hα⟩, ε, hε, hmem⟩ := h
  have h2p : ¬ IsUnit (2 : R) := (twoAdic_irreducible h2).not_isUnit
  obtain ⟨r, hr⟩ := mem_span_singleton.1 (hf hmem)
  rw [Algebra.smul_def, hα] at hr
  have e : u = ε ^ 2 + 8 * r := by
    apply IsFractionRing.injective R F
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination -hr
  obtain ⟨η, hη⟩ := hε.exists_right_inv
  have hx : 2 * (r * η ^ 2) ∈ maximalIdeal R :=
    Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 h2p)
  obtain ⟨y, hy⟩ := isSquare_one_add_four_mul hx
  have hu2 : u = (y * ε) ^ 2 := by
    have h1 : u * η ^ 2 = y * y := by
      rw [← hy, e]
      linear_combination (ε * η + 1) * hη
    linear_combination (-u * (ε * η + 1)) * hη + ε ^ 2 * h1
  have hyu : IsUnit (y * ε) := (isUnit_pow_iff two_ne_zero).1 (hu2 ▸ hu)
  refine ⟨⟨u, hu, hα⟩, y * ε, hyu, ?_⟩
  rw [hα, one_mul, mul_one, ← map_pow, ← hu2, sub_self]
  exact zero_mem _

/-- The scale of a component of a Jordan splitting of a finitely generated lattice is a non-zero principal ideal. -/
lemma scale_gen {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (i : Fin t) : ∃ σ : F, σ ≠ 0 ∧ scale Q (Ls i) = R ∙ σ := by
  have hLs : ∀ k, Ls k ≤ L := fun k => hL.split.iSup_eq ▸ le_iSup Ls k
  obtain ⟨σ, hσ, hs⟩ := exists_eq_span_singleton (R := R) (scale_fg Q (FG.of_le hfg (hLs i)))
    (hL.modular i).1
  exact ⟨σ, hσ, hs⟩

/-- Over a 2-adic ring every non-zero component norm is $2^u\mathfrak o$ for some $u \in \mathbb Z$. -/
lemma exists_two_pow_eq (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (k : Fin t) :
    ∃ u : ℤ, R ∙ ((2 : F) ^ u) = normIdeal Q (Ls k) := by
  obtain ⟨hfgi, hregi, hnei⟩ := twoAdic_component_facts Q hfg hL k
  have hπ := twoAdic_irreducible h2
  obtain ⟨σ, hσ0, hσ⟩ := scale_gen Q hfg hL k
  have key : ∃ ν : F, ν ≠ 0 ∧ normIdeal Q (Ls k) = R ∙ ν := by
    rcases normIdeal_eq_scale_or_two_smul Q h2 hfgi hregi hnei with h | h
    · exact ⟨σ, hσ0, h.trans hσ⟩
    · exact ⟨2 * σ, mul_ne_zero (two_ne_zero' F) hσ0, by rw [h, hσ, FIdealAux.smul_span_singleton]⟩
  obtain ⟨ν, hν0, hν⟩ := key
  refine ⟨dord hπ ν, ?_⟩
  rw [hν]
  exact span_eq_of_dord_eq hπ (two_zpow_ne_zero _) hν0 (by rw [dord_two_zpow h2])

/-- $s \le u \le s + 1$ for $\mathfrak n = 2^u\mathfrak o$, $\mathfrak s = \sigma\mathfrak o$, $s = \operatorname{ord}\sigma$. -/
lemma ord_bounds (h2 : IsTwoAdic R) {t : ℕ} {Ls : Fin t → Submodule R V}
    (k : Fin t) {u : ℤ} (hu : R ∙ ((2 : F) ^ u) = normIdeal Q (Ls k)) {σ : F} (hσ0 : σ ≠ 0)
    (hσ : scale Q (Ls k) = R ∙ σ) :
    dord (twoAdic_irreducible h2) σ ≤ u ∧ u ≤ dord (twoAdic_irreducible h2) σ + 1 := by
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have m1 : (2 : F) ^ u ∈ scale Q (Ls k) :=
    normIdeal_le_scale Q _ (by rw [← hu]; exact mem_span_singleton_self _)
  rw [hσ, mem_span_iff hπ (two_zpow_ne_zero u) hσ0, dord_two_zpow h2] at m1
  have m2 : (2 : F) * σ ∈ R ∙ ((2 : F) ^ u) := by
    rw [hu]
    refine two_smul_scale_le_normIdeal Q _ ?_
    rw [hσ]
    exact Submodule.smul_mem_pointwise_smul σ (2 : F) _ (mem_span_singleton_self σ)
  rw [mem_span_two_zpow_iff h2 (mul_ne_zero h2F hσ0), dord_mul hπ h2F hσ0, twoAdic_dord_two h2] at m2
  omega

/-- $\operatorname{ord}\sigma + 1 \le \operatorname{ord}\tau$ for $\mathfrak s_i = \sigma\mathfrak o$,
$\mathfrak s_{i+1} = \tau\mathfrak o$ (from $\mathfrak s_{i+1} \subseteq 2\mathfrak s_i$). -/
lemma dord_succ_le (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : (j : ℕ) = i + 1)
    {σ τ : F} (hσ0 : σ ≠ 0) (hτ0 : τ ≠ 0) (hσ : scale Q (Ls i) = R ∙ σ) (hτ : scale Q (Ls j) = R ∙ τ) :
    dord (twoAdic_irreducible h2) σ + 1 ≤ dord (twoAdic_irreducible h2) τ := by
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have h := scale_succ_le_two_smul_scale Q h2 hfg hL hij
  rw [hσ, hτ, FIdealAux.smul_span_singleton, Submodule.span_singleton_le_iff_mem,
    mem_span_iff hπ hτ0 (mul_ne_zero h2F hσ0), dord_mul hπ h2F hσ0, twoAdic_dord_two h2] at h
  omega

end Aux

section Main

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **$\mathfrak s_i^2\mathfrak f_i = 2^k\mathfrak o$** (93:26 in the 2-adic case): with $a_i = 2^{u_i}$,
$k = u_i + u_j$ if that is odd, and $k = \frac12(u_i + u_j) + \operatorname{ord}\sigma + 1$ if it is even. -/
theorem core (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {u : Fin t → ℤ}
    (hu : ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k)) {i j : Fin t} (hij : (j : ℕ) = i + 1) {σ τ : F}
    (hσ0 : σ ≠ 0) (hτ0 : τ ≠ 0) (hσ : scale Q (Ls i) = R ∙ σ) (hτ : scale Q (Ls j) = R ∙ τ) :
    ∃ k : ℤ, scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = R ∙ ((2 : F) ^ k) ∧
      ((Odd (u i + u j) ∧ k = u i + u j) ∨
        (Even (u i + u j) ∧ k = (u i + u j) / 2 + dord (twoAdic_irreducible h2) σ + 1)) := by
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have hπ2 : algebraMap R F (2 : R) = (2 : F) := map_ofNat _ 2
  have ha := isFundNormGenerators_two_pow Q h2 hfg hreg hL hu
  rcases Int.even_or_odd (u i + u j) with he | ho
  · refine ⟨(u i + u j) / 2 + dord hπ σ + 1, ?_, Or.inr ⟨he, rfl⟩⟩
    have hE : scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j =
        quadDefect R ((2 : F) ^ u i * (2 : F) ^ u j) ⊔ ((2 : F) ^ u i) • fundWeight Q L Ls j ⊔
          ((2 : F) ^ u j) • fundWeight Q L Ls i ⊔
          R ∙ (2 * algebraMap R F 2 ^
            ((dord hπ ((2 : F) ^ u i) + dord hπ ((2 : F) ^ u j)) / 2 + dord hπ σ)) :=
      mul_fIdeal_of_even Q hπ h2p hfg hreg hL ha i j hij hσ
        (by rw [dord_two_zpow (F := F) h2 (u i), dord_two_zpow (F := F) h2 (u j)]; exact he)
    rw [dord_two_zpow (F := F) h2 (u i), dord_two_zpow (F := F) h2 (u j), hπ2] at hE
    obtain ⟨p1, p2⟩ := ord_bounds Q h2 i (hu i) hσ0 hσ
    obtain ⟨q1, q2⟩ := ord_bounds Q h2 j (hu j) hτ0 hτ
    have hs := dord_succ_le Q h2 hfg hL hij hσ0 hτ0 hσ hτ
    obtain ⟨m, hm⟩ := he
    have hEeq : (2 : F) * (2 : F) ^ ((u i + u j) / 2 + dord hπ σ) =
        (2 : F) ^ ((u i + u j) / 2 + dord hπ σ + 1) := by
      rw [zpow_add_one₀ h2F]; ring
    rw [hEeq] at hE
    rw [hE]
    refine sup_eq_right.2 (sup_le (sup_le ?_ ?_) ?_)
    · refine (quadDefect_le_span _).trans ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
      rw [mem_span_two_zpow_iff h2 (mul_ne_zero (z2 _) (z2 _)), dord_mul hπ (z2 _) (z2 _),
        dord_two_zpow (F := F) h2, dord_two_zpow (F := F) h2]
      omega
    · rw [fundWeight_eq_two_smul_scale_twoAdic Q h2 hfg hreg hL j, hτ, FIdealAux.smul_span_singleton,
        FIdealAux.smul_span_singleton, Submodule.span_singleton_le_iff_mem,
        mem_span_two_zpow_iff h2 (mul_ne_zero (z2 _) (mul_ne_zero h2F hτ0)),
        dord_mul hπ (z2 _) (mul_ne_zero h2F hτ0), dord_mul hπ h2F hτ0, dord_two_zpow (F := F) h2,
        twoAdic_dord_two h2]
      omega
    · rw [fundWeight_eq_two_smul_scale_twoAdic Q h2 hfg hreg hL i, hσ, FIdealAux.smul_span_singleton,
        FIdealAux.smul_span_singleton, Submodule.span_singleton_le_iff_mem,
        mem_span_two_zpow_iff h2 (mul_ne_zero (z2 _) (mul_ne_zero h2F hσ0)),
        dord_mul hπ (z2 _) (mul_ne_zero h2F hσ0), dord_mul hπ h2F hσ0, dord_two_zpow (F := F) h2,
        twoAdic_dord_two h2]
      omega
  · refine ⟨u i + u j, ?_, Or.inl ⟨ho, rfl⟩⟩
    have hO : scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = R ∙ ((2 : F) ^ u i * (2 : F) ^ u j) :=
      mul_fIdeal_of_odd Q hπ hfg hL ha i j
        (by rw [dord_two_zpow (F := F) h2 (u i), dord_two_zpow (F := F) h2 (u j)]; exact ho)
    rw [hO, zpow_add₀ h2F]

/-- All the data needed for the three statements: generators `u`, `σ`, `τ`, the exponent `k` of
$\mathfrak s_i^2\mathfrak f_i = 2^k\mathfrak o$, and the order inequalities. -/
theorem exists_data (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) {i j : Fin t} (hij : (j : ℕ) = i + 1) :
    ∃ (u : Fin t → ℤ) (σ τ : F) (k : ℤ), (∀ m, R ∙ ((2 : F) ^ u m) = normIdeal Q (Ls m)) ∧ σ ≠ 0 ∧ τ ≠ 0 ∧
      scale Q (Ls i) = R ∙ σ ∧ scale Q (Ls j) = R ∙ τ ∧
      scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = R ∙ ((2 : F) ^ k) ∧
      dord (twoAdic_irreducible h2) σ ≤ u i ∧ u i ≤ dord (twoAdic_irreducible h2) σ + 1 ∧
      dord (twoAdic_irreducible h2) τ ≤ u j ∧ u j ≤ dord (twoAdic_irreducible h2) τ + 1 ∧
      dord (twoAdic_irreducible h2) σ + 1 ≤ dord (twoAdic_irreducible h2) τ ∧
      ((Odd (u i + u j) ∧ k = u i + u j) ∨
        (Even (u i + u j) ∧ k = (u i + u j) / 2 + dord (twoAdic_irreducible h2) σ + 1)) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin t → ℤ, ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k) :=
    ⟨fun k => (exists_two_pow_eq Q h2 hfg hL k).choose, fun k => (exists_two_pow_eq Q h2 hfg hL k).choose_spec⟩
  obtain ⟨σ, hσ0, hσ⟩ := scale_gen Q hfg hL i
  obtain ⟨τ, hτ0, hτ⟩ := scale_gen Q hfg hL j
  obtain ⟨k, hk, hcase⟩ := core Q h2 hfg hreg hL hu hij hσ0 hτ0 hσ hτ
  obtain ⟨p1, p2⟩ := ord_bounds Q h2 i (hu i) hσ0 hσ
  obtain ⟨q1, q2⟩ := ord_bounds Q h2 j (hu j) hτ0 hτ
  exact ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2,
    dord_succ_le Q h2 hfg hL hij hσ0 hτ0 hσ hτ, hcase⟩

/-- **$\mathfrak s_i^2\mathfrak f_i \supseteq \mathfrak n_i\mathfrak n_{i+1}$** (O'Meara 1963, §93G, proof of 93:29,
step 1, p. 277; "by direct calculation from Example 93:26"). Over a 2-adic local field, for a finitely generated
regular lattice $L$ with Jordan splitting, $\mathfrak n_i\mathfrak n_{i+1} \subseteq \mathfrak s_i^2\mathfrak f_i$
(indices $0$-based, `j = i + 1`). In the odd case the two sides are equal; in the even case $\mathfrak s_i^2\mathfrak f_i
= 2\mathfrak p^{\frac12(u_i+u_{i+1})+s_i}$ and $\frac12(u_i + u_{i+1}) + s_i + 1 \le u_i + u_{i+1}$. -/
@[kb "omeara1963" "§93G, proof of 93:29, p. 277 (s_i² f_i ⊇ n_i n_{i+1}; strict ⇒ f_i ⊆ 8o)"]
theorem normIdeal_mul_le_scale_sq_mul_fIdeal (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (i j : Fin t) (hij : (j : ℕ) = i + 1) :
    normIdeal Q (Ls i) * normIdeal Q (Ls j) ≤ scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j := by
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hs, hcase⟩ :=
    exists_data Q h2 hfg hreg hL hij
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  rw [hk, ← hu i, ← hu j, FIdealAux.span_mul_span', ← zpow_add₀ h2F, Submodule.span_singleton_le_iff_mem,
    mem_span_two_zpow_iff h2 (two_zpow_ne_zero _), dord_two_zpow h2]
  rcases hcase with ⟨_, hk'⟩ | ⟨he, hk'⟩
  · omega
  · obtain ⟨m, hm⟩ := he
    omega

/-- **$\mathfrak s_i^2\mathfrak f_i \supsetneq \mathfrak n_i\mathfrak n_{i+1} \Rightarrow \mathfrak f_i \subseteq
8\mathfrak o$** (O'Meara 1963, §93G, proof of 93:29, step 1, p. 277). Same hypotheses as
`normIdeal_mul_le_scale_sq_mul_fIdeal`. In the odd case there is equality, so the hypothesis fails; in the even case
$\mathfrak s_i^2\mathfrak f_i = 2^k\mathfrak o$ with $k < u_i + u_{i+1}$ forces $\operatorname{ord} z \ge 3$ for the
non-zero $z \in \mathfrak f_i$. -/
@[kb "omeara1963" "§93G, proof of 93:29, p. 277 (s_i² f_i ⊇ n_i n_{i+1}; strict ⇒ f_i ⊆ 8o)"]
theorem fIdeal_le_eight_of_lt (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (i j : Fin t) (hij : (j : ℕ) = i + 1)
    (hlt : normIdeal Q (Ls i) * normIdeal Q (Ls j) < scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j) :
    fIdeal Q L Ls i j ≤ R ∙ (8 : F) := by
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hs, hcase⟩ :=
    exists_data Q h2 hfg hreg hL hij
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have e1 : normIdeal Q (Ls i) * normIdeal Q (Ls j) = R ∙ ((2 : F) ^ (u i + u j)) := by
    rw [← hu i, ← hu j, FIdealAux.span_mul_span', zpow_add₀ h2F]
  rw [e1, hk] at hlt
  have hk_le : k ≤ u i + u j := by
    have := hlt.le
    rwa [Submodule.span_singleton_le_iff_mem, mem_span_two_zpow_iff h2 (two_zpow_ne_zero _),
      dord_two_zpow h2] at this
  have hne : k ≠ u i + u j := fun h => hlt.ne (by rw [h])
  rcases hcase with ⟨_, hk'⟩ | ⟨he, hk'⟩
  · exact absurd hk' hne
  · intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact zero_mem _
    have hm : σ * σ * z ∈ R ∙ ((2 : F) ^ k) := by
      rw [← hk, hσ]
      exact Submodule.mul_mem_mul (Submodule.mul_mem_mul (mem_span_singleton_self σ)
        (mem_span_singleton_self σ)) hz
    rw [mem_span_two_zpow_iff h2 (mul_ne_zero (mul_ne_zero hσ0 hσ0) hz0),
      dord_mul hπ (mul_ne_zero hσ0 hσ0) hz0, dord_mul hπ hσ0 hσ0] at hm
    have h8 : (8 : F) = (2 : F) ^ (3 : ℤ) := by norm_num
    rw [h8, mem_span_two_zpow_iff h2 hz0]
    obtain ⟨m, hm'⟩ := he
    omega

/-- **$\mathfrak n_{i+1} \subsetneq 4\mathfrak n_i \Rightarrow \mathfrak f_i \subsetneq 4\mathfrak n_i\mathfrak w_i^{-1}$**
(O'Meara 1963, §93G, proof of 93:29, step 1, p. 277). With $\mathfrak n_i = a\mathfrak o$ and $\mathfrak w_i^{-1}$ the
`Submodule` division `1 / w_i`; the right-hand side is written `(4 * a) • (1 / w_i)` as in condition (iii) of 93:28
(`DyadicClassification`). Over a 2-adic field $\mathfrak w_i = 2\mathfrak s_i$, so the right-hand side is generated by
an element of order $u_i - s_i + 1$, while $\mathfrak n_{i+1} \subsetneq 4\mathfrak n_i$ means $u_{i+1} \ge u_i + 3$ and
every non-zero element of $\mathfrak f_i$ has order $\ge u_i - s_i + 2$. -/
@[kb "omeara1963" "§93G, proof of 93:29, p. 277 (n_{i+1} ⊊ 4n_i ⇒ f_i ⊂ 4 n_i w_i⁻¹)"]
theorem fIdeal_lt_four_mul_of_normIdeal_lt (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (i j : Fin t) (hij : (j : ℕ) = i + 1) {a : F} (ha : R ∙ a = normIdeal Q (Ls i))
    (hlt : normIdeal Q (Ls j) < (4 : F) • normIdeal Q (Ls i)) :
    fIdeal Q L Ls i j < (4 * a) • (1 / fundWeight Q L Ls i) := by
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hs, hcase⟩ :=
    exists_data Q h2 hfg hreg hL hij
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have huj : u i + 3 ≤ u j := by
    by_contra hcon
    apply hlt.not_ge
    rw [← hu i, ← hu j, FIdealAux.smul_span_singleton, four_mul_two_zpow,
      Submodule.span_singleton_le_iff_mem, mem_span_two_zpow_iff h2 (z2 _), dord_two_zpow h2]
    omega
  have hA : R ∙ (4 * a) = R ∙ ((2 : F) ^ (u i + 2)) := by
    rw [← FIdealAux.smul_span_singleton, ha, ← hu i, FIdealAux.smul_span_singleton, four_mul_two_zpow]
  have hw : fundWeight Q L Ls i = R ∙ (2 * σ) := by
    rw [fundWeight_eq_two_smul_scale_twoAdic Q h2 hfg hreg hL i, hσ, FIdealAux.smul_span_singleton]
  have hσ2 : (2 : F) * σ ≠ 0 := mul_ne_zero h2F hσ0
  have hrhs : (4 * a) • (1 / fundWeight Q L Ls i) = R ∙ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) := by
    rw [hw, one_div_span hσ2, FundAux.smul_eq_span_mul, hA, FIdealAux.span_mul_span']
  rw [hrhs]
  have hg0 : (2 : F) ^ (u i + 2) * (2 * σ)⁻¹ ≠ 0 := mul_ne_zero (z2 _) (inv_ne_zero hσ2)
  have hdg : dord hπ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) = u i + 2 - (1 + dord hπ σ) := by
    rw [dord_mul hπ (z2 _) (inv_ne_zero hσ2), B63.dord_inv' hπ hσ2, dord_mul hπ h2F hσ0,
      dord_two_zpow h2, twoAdic_dord_two h2]
    ring
  have key : ∀ z ∈ fIdeal Q L Ls i j, z ≠ 0 →
      dord hπ ((2 : F) ^ (u i + 2) * (2 * σ)⁻¹) + 1 ≤ dord hπ z := by
    intro z hz hz0
    have hm : σ * σ * z ∈ R ∙ ((2 : F) ^ k) := by
      rw [← hk, hσ]
      exact Submodule.mul_mem_mul (Submodule.mul_mem_mul (mem_span_singleton_self σ)
        (mem_span_singleton_self σ)) hz
    rw [mem_span_two_zpow_iff h2 (mul_ne_zero (mul_ne_zero hσ0 hσ0) hz0),
      dord_mul hπ (mul_ne_zero hσ0 hσ0) hz0, dord_mul hπ hσ0 hσ0] at hm
    rw [hdg]
    rcases hcase with ⟨_, hk'⟩ | ⟨he, hk'⟩
    · omega
    · obtain ⟨m, hm'⟩ := he
      omega
  refine lt_of_le_of_ne ?_ ?_
  · intro z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact zero_mem _
    rw [mem_span_iff hπ hz0 hg0]
    have := key z hz hz0
    omega
  · intro heq
    have hmem : (2 : F) ^ (u i + 2) * (2 * σ)⁻¹ ∈ fIdeal Q L Ls i j := by
      rw [heq]; exact mem_span_singleton_self _
    have := key _ hmem hg0
    omega

end Main

/-- A lattice on a regular space is regular (the proof of `isRegular_of_lattice_max`, repeated to avoid the import). -/
lemma isRegular_of_isLattice {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
    (Q : QuadraticForm F V) (hV : (QuadraticMap.associated Q).Nondegenerate) {K : Submodule R V}
    (hK : K.IsLattice F) : IsRegular Q K := by
  intro x hx hx0
  have hall : ∀ y, bil Q x y = 0 := by
    intro y
    have hy : y ∈ span F (K : Set V) := by rw [hK.span_eq_top]; trivial
    exact bil_zero_of_mem_span_F Q hx0 hy
  exact hV.1 x fun y => by simpa [bil] using hall y

end Nec93

section Necessity

open Nec93

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **93:29, necessity, from 93:28** (O'Meara 1963, §93G, proof of 93:29, step 1, p. 277): "We obtain the necessity by
suitably interpreting Theorem 93:28. Take $a_i = 2^{u_i}$." Let $F$ be 2-adic (`IsTwoAdic R`) and $L$, $K$ lattices on
a regular quadratic space with Jordan splittings having the same Jordan invariants. *Assuming the named statement
`DyadicClassification R Q` (93:28)*, if $\operatorname{cls} L = \operatorname{cls} K$ then for all consecutive
$i, i+1$ conditions (i) and (ii) of 93:29 hold, exactly as in the field of `TwoAdicClassification`.
Proof: with $a_i = 2^{u_i}$ the lattices have the same set of fundamental invariants
(`sameFundamentalInvariants_of_sameJordanInvariants`), so 93:28 applies. Condition (i): $\mathfrak n_i\mathfrak n_{i+1}/
\mathfrak s_i^2 \subseteq \mathfrak f_i$ (`normIdeal_mul_le_scale_sq_mul_fIdeal`); if equal, (i) of 93:28 is (i); if
strict then $\mathfrak f_i \subseteq 8\mathfrak o$ (`fIdeal_le_eight_of_lt`) and by the Local Square Theorem
($1 + 4\alpha$ is a square for $\alpha \in \mathfrak p$) $d \cong 1 \bmod \mathfrak f_i$ makes $d$ a square, hence
$d \cong 1 \bmod$ anything (`sqEquivMod_of_le_eight`). Condition (ii) follows from (iii) of 93:28 and
`fIdeal_lt_four_mul_of_normIdeal_lt`. The sufficiency of 93:29 is not covered here. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (necessity, from 93:28)"]
theorem cls_eq_imp_of_dyadicClassification (h : DyadicClassification R Q) (h2 : IsTwoAdic R)
    (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] {t : ℕ} (Ls Ks : Fin t → Submodule R V)
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hJ : SameJordanInvariants Q Q Ls Ks) :
    cls Q L = cls Q K → ∀ i j : Fin t, (j : ℕ) = i + 1 →
      DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i)
        (normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i))) ∧
      (normIdeal Q (Ls j) < (4 : F) • normIdeal Q (Ls i) → ∀ u : ℤ,
        R ∙ ((2 : F) ^ u) = normIdeal Q (Ls i) →
        SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) ((2 : F) ^ u)) := by
  intro hcls i j hij
  have hLl : L.IsLattice F := inferInstance
  have hKl : K.IsLattice F := inferInstance
  have hfgL := hLl.fg
  have hfgK := hKl.fg
  have hregL := isRegular_of_isLattice Q hQ hLl
  have hregK := isRegular_of_isLattice Q hQ hKl
  have hπ := twoAdic_irreducible h2
  have h2p : ¬ IsUnit (2 : R) := hπ.not_isUnit
  obtain ⟨u, hu⟩ : ∃ u : Fin t → ℤ, ∀ k, R ∙ ((2 : F) ^ u k) = normIdeal Q (Ls k) :=
    ⟨fun k => (exists_two_pow_eq Q h2 hfgL hL k).choose,
      fun k => (exists_two_pow_eq Q h2 hfgL hL k).choose_spec⟩
  have hfund := sameFundamentalInvariants_of_sameJordanInvariants Q Q h2 hfgL hfgK hregL hregK hL hK hJ hu
  obtain ⟨k1, -, k3⟩ := (h.cls_eq_iff h2p hQ L K Ls Ks _ hL hK hfund).1 hcls i j hij
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, hσ0, hσ⟩ := scale_gen Q hfgL hL i
    by_cases hlt : normIdeal Q (Ls i) * normIdeal Q (Ls j) <
        scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j
    · have h8 := fIdeal_le_eight_of_lt Q h2 hfgL hregL hL i j hij hlt
      obtain ⟨b, b', hb⟩ := k1
      exact ⟨b, b', sqEquivMod_of_le_eight h2 h8 hb⟩
    · have heq := (lt_or_eq_of_le
        (normIdeal_mul_le_scale_sq_mul_fIdeal Q h2 hfgL hregL hL i j hij)).resolve_left hlt
      rw [heq, hσ, FIdealAux.span_mul_span', mul_div_span_cancel (mul_ne_zero hσ0 hσ0)]
      exact k1
  · intro hlt u0 hu0
    have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
    have hui : u0 = u i := by
      have := (FIdealAux.span_eq_iff_dord hπ (z2 u0) (z2 (u i))).1 (hu0.trans (hu i).symm)
      rwa [dord_two_zpow h2, dord_two_zpow h2] at this
    rw [hui]
    exact k3 (fIdeal_lt_four_mul_of_normIdeal_lt Q h2 hfgL hregL hL i j hij (a := (2 : F) ^ u i) (hu i) hlt)

end Necessity

end QuadFormsKB.OMeara
