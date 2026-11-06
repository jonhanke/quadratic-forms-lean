/-
# O'Meara 93:28, sufficiency, steps 4–7: the ideal $\mathfrak f_1$ as products $\gamma\lambda$

**Setting** (as in `Sec93EFund.lean`): $R$ a discrete valuation ring with fraction field $F$, $2 \in F^\times$, $\pi$ an
irreducible element, `dord hπ` the order function; lattices `Submodule R V`; indices $0$-based (`i`, `j = i + 1` are
O'Meara's $1, 2$), $\mathfrak s_i = \mathfrak o$.

In steps 4, 6 and 7 of the sufficiency (pp. 274–275) O'Meara arranges $dK_1 = 1$ by the move
$\langle A(0,0)\rangle \perp K_1 \perp K_2 \cong \langle A(-\lambda, a_2)\rangle \perp K_1 \perp K_2'$, which multiplies
$dK_1$ by $1 + a_2\lambda$. This works because, by 93:27, every element of $\mathfrak f_1$ is a product $\gamma\lambda$
with $\gamma \in \mathfrak g_2$ and $\lambda \in \mathfrak g_1$. In step 5 ($a_1\mathfrak o = 2\mathfrak o$) instead
$\mathfrak f_1 \subseteq 4\mathfrak p$.

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4–7, pp. 274–275)
* `smul_pi_mem_fundWeight`: if $u_2 = u_1 + 1$ then $a_1\pi \in \mathfrak w_1$ (O'Meara, step 6: "$a_2\mathfrak o$ is the
  maximal ideal in $\mathfrak g_1$");
* `exists_factor`: if $u_2 = u_1$, or $u_2 = u_1 + 1$, or $\mathfrak s_2 = \mathfrak p$ and $u_2 = u_1 + 2$, every
  $f \in \mathfrak f_1$ is $\gamma\lambda$ with $\gamma \in \mathfrak g_2$, $\lambda \in \mathfrak g_1$;
* `dord_le_add_two`: $u_2 \le u_1 + 2$ when $\mathfrak s_2 = \mathfrak p$ (93:25);
* `fIdeal_le_four_pi`: if $a_1\mathfrak o = 2\mathfrak o$ and $u_2 > u_1$ then $\mathfrak f_1 \subseteq 4\mathfrak p$.
-/
import QuadFormsKB.Literature.OMeara.Sec93FCore8
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwo

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.CoreFactor

open FundAux FIdealAux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)] {π : R}
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

include Q in
omit [Invertible (2 : F)] [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- If $\operatorname{ord} x \ne \operatorname{ord} y$, then $x + y \ne 0$ and $\operatorname{ord}(x + y) \le
\operatorname{ord} x$. -/
lemma dord_add_le_of_ne (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hne : dord hπ x ≠ dord hπ y) : x + y ≠ 0 ∧ dord hπ (x + y) ≤ dord hπ x := by
  have hxy : x + y ≠ 0 := by
    intro h
    have : y = -x := by linear_combination h
    rw [this, dord_neg hπ hx] at hne
    exact hne rfl
  refine ⟨hxy, ?_⟩
  rcases lt_or_gt_of_ne hne with h | h
  · rw [dord_add_of_lt hπ hx hy hxy h]
  · rw [add_comm, dord_add_of_lt hπ hy hx (by rwa [add_comm]) h]; omega

/-- **Step 6: $a_1\pi \in \mathfrak w_1$ when $u_2 = u_1 + 1$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 6, p. 274: "$a_2 \in \mathfrak g_2 \subseteq \mathfrak g_1$ with $\operatorname{ord}_\mathfrak p a_1 +
\operatorname{ord}_\mathfrak p a_2$ odd, hence $a_2\mathfrak o = \mathfrak p a_1$ is contained in $\mathfrak w_1$"):
write $a_2 = a_1\varepsilon^2 + w$ with $w \in \mathfrak w_1$ ($\mathfrak g_1 = a_1\mathfrak o^2 + \mathfrak w_1$); the
orders of $a_2$ and $a_1\varepsilon^2$ have different parity, so $\operatorname{ord} w \le u_2 = u_1 + 1$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 6, p. 274 (a₂𝔬 = 𝔭a₁ ⊆ 𝔴₁)"]
theorem smul_pi_mem_fundWeight (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) {i j : Fin t} (hij : i ≤ j)
    (hu : dord hπ (a j) = dord hπ (a i) + 1) :
    a i * algebraMap R F π ∈ fundWeight Q L Ls i := by
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have hmem : a j ∈ fundNormGroup Q L Ls i := fundNormGroup_antitone Q hJ hij (ha j).1
  obtain ⟨ε, w, hw, hεw⟩ := fund_rep Q h2p hfg hreg hJ ha i hmem
  -- `w = a j + (-(a i ε²))` has order `≤ u_j = u_i + 1`
  have hwdef : w = a j + -(a i * algebraMap R F ε ^ 2) := by rw [hεw]; ring
  have hw0 : w ≠ 0 ∧ dord hπ w ≤ dord hπ (a i) + 1 := by
    by_cases hε : algebraMap R F ε = 0
    · rw [hwdef, hε]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
        add_zero]
      exact ⟨haj, hu.le⟩
    · have hn : -(a i * algebraMap R F ε ^ 2) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hai (pow_ne_zero _ hε))
      have hd : dord hπ (-(a i * algebraMap R F ε ^ 2)) = dord hπ (a i) + 2 * dord hπ (algebraMap R F ε) := by
        rw [dord_neg hπ (mul_ne_zero hai (pow_ne_zero _ hε)), dord_mul hπ hai (pow_ne_zero _ hε), dord_sq hπ hε]
      obtain ⟨h1, h2⟩ := dord_add_le_of_ne Q hπ haj hn (by rw [hd, hu]; omega)
      rw [hwdef]; exact ⟨h1, by omega⟩
  obtain ⟨hw0, hwle⟩ := hw0
  have hx0 : a i * algebraMap R F π ≠ 0 := mul_ne_zero hai hpi
  have hxw : a i * algebraMap R F π ∈ R ∙ w := by
    rw [mem_span_iff hπ hx0 hw0, dord_mul hπ hai hpi, show dord hπ (algebraMap R F π) = 1 from dord_pi hπ]
    exact hwle
  obtain ⟨r, hr⟩ := mem_span_singleton.mp hxw
  rw [← hr]
  exact (fundWeight Q L Ls i).smul_mem r hw

/-- A fundamental weight lies in the fundamental norm group. -/
lemma fundWeight_subset {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} (k : Fin t) {w : F}
    (hw : w ∈ fundWeight Q L Ls k) : w ∈ fundNormGroup Q L Ls k :=
  normGroupIdeal_subset Q _ ((weight_bounds Q _).2.1 hw)

/-- **The elements of $\mathfrak f_1$ are products $\gamma\lambda$, $\gamma \in \mathfrak g_2$, $\lambda \in
\mathfrak g_1$** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275, from 93:27), when
$\mathfrak s_1 = \mathfrak o$ and either $u_2 = u_1$ ($\mathfrak f_1 = a_2\mathfrak w_1$: $\gamma = a_2$), or
$u_2 = u_1 + 1$ ($\mathfrak f_1 = a_1a_2\mathfrak o$: $\gamma = a_2$, $\lambda = a_1r \in a_1\mathfrak o^2 + a_1\mathfrak p
\subseteq \mathfrak g_1$ by the perfectness of the residue field and `smul_pi_mem_fundWeight`), or $\mathfrak s_2 =
\mathfrak p$ and $u_2 = u_1 + 2$ ($\mathfrak f_1 = a_1\mathfrak w_2$: $\lambda = a_1$). Indices $0$-based: `i`, `j`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275 (f₁ ⊆ g₂ g₁ by 93:27)"]
theorem exists_factor (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : (j : ℕ) = i + 1) (hs : scale Q (Ls i) = 1)
    (hcase : dord hπ (a j) = dord hπ (a i) ∨ dord hπ (a j) = dord hπ (a i) + 1 ∨
      ∃ τ : F, scale Q (Ls j) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a j) = dord hπ (a i) + 2)
    {f : F} (hf : f ∈ fIdeal Q L Ls i j) :
    ∃ γ ∈ fundNormGroup Q L Ls j, ∃ l ∈ fundNormGroup Q L Ls i, f = γ * l := by
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hσ : scale Q (Ls i) = R ∙ (1 : F) := by rw [hs, Submodule.one_eq_span]
  have hone : scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = fIdeal Q L Ls i j := by
    rw [hs, one_mul, one_mul]
  rcases hcase with hu | hu | ⟨τ, hτ, hτ1, hu⟩
  · have h := mul_fIdeal_of_dord_eq Q hπ h2p hfg hreg hJ ha i j hij hσ hu
    rw [hone] at h
    rw [h] at hf
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hf
    exact ⟨a j, (ha j).1, w, fundWeight_subset Q i hw, by rw [smul_eq_mul]⟩
  · have h := mul_fIdeal_of_dord_succ Q hπ hfg hJ ha i j hu
    rw [hone] at h
    rw [h] at hf
    obtain ⟨r, rfl⟩ := mem_span_singleton.mp hf
    refine ⟨a j, (ha j).1, a i * algebraMap R F r, ?_, by rw [Algebra.smul_def]; ring⟩
    have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h2p
    obtain ⟨c, hc⟩ := CoreTwo.exists_sq_residue h2m r
    have hmax : maximalIdeal R = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
    rw [hmax] at hc
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hc
    have hw : m • (a i * algebraMap R F π) ∈ fundWeight Q L Ls i :=
      (fundWeight Q L Ls i).smul_mem m (smul_pi_mem_fundWeight Q hπ h2p hfg hreg hJ ha hij' hu)
    have hset := fundNormGroup_eq_sq_add Q h2p hfg hreg hJ i (ha i)
    have hmem : a i * algebraMap R F r ∈ (fundNormGroup Q L Ls i : Set F) := by
      rw [hset]
      refine ⟨c, _, hw, ?_⟩
      have : r = c ^ 2 + m * π := by linear_combination -hm
      rw [this, Algebra.smul_def]; simp only [map_add, map_pow, map_mul]; ring
    exact hmem
  · have hτ0 : dord hπ τ = dord hπ (1 : F) + 1 := by
      rw [hτ1, show (1 : F) = algebraMap R F 1 by simp, dord_unit hπ isUnit_one]; simp
    have h := mul_fIdeal_of_dord_add_two Q hπ h2p hfg hreg hJ ha i j hij hσ hτ hu hτ0
    rw [hone] at h
    rw [h] at hf
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp hf
    exact ⟨w, fundWeight_subset Q j hw, a i, (ha i).1, by rw [smul_eq_mul, mul_comm]⟩

include Q in
omit [Invertible (2 : F)] [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- Membership in a principal fractional ideal by orders. -/
lemma mem_span_of_dord (hπ : Irreducible π) {x y : F} (hy : y ≠ 0) (h : x ≠ 0 → dord hπ y ≤ dord hπ x) :
    x ∈ R ∙ y := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_mem _
  · exact (mem_span_iff hπ hx hy).2 (h hx)

include Q in
omit [Invertible (2 : F)] [HenselianLocalRing R] [Finite (ResidueField R)] in
/-- For principal fractional ideals, $\neg(x\mathfrak o \subsetneq y\mathfrak o)$ means
$\operatorname{ord} x \le \operatorname{ord} y$. -/
lemma dord_le_of_not_lt (hπ : Irreducible π) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (h : ¬ (R ∙ x < R ∙ y)) :
    dord hπ x ≤ dord hπ y := by
  by_contra hc
  push Not at hc
  refine h (lt_of_le_of_ne ((span_singleton_le_iff_mem _ _).2 ((mem_span_iff hπ hx hy).2 hc.le)) ?_)
  intro he
  have := (span_eq_iff_dord hπ hx hy).1 he
  omega

include Q in
omit [Invertible (2 : F)] [HenselianLocalRing R] [Finite (ResidueField R)] in
lemma dord_one (hπ : Irreducible π) : dord hπ (1 : F) = 0 := by
  rw [show (1 : F) = algebraMap R F 1 by simp]; exact dord_unit hπ isUnit_one

/-- **93:25 with $\mathfrak s_2 = \mathfrak p$: $u_2 \le u_1 + 2$** (O'Meara 1963, §93F, proof of 93:28, sufficiency,
step 7, p. 275: "$\pi^2\mathfrak g_1 \subseteq \mathfrak g_2 \subseteq \mathfrak g_1$"): $\pi^2a_1 \in \mathfrak g_2
\subseteq a_2\mathfrak o$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 7, p. 275 (π²g₁ ⊆ g₂)"]
theorem dord_le_add_two (hπ : Irreducible π) {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) {i j : Fin t}
    (hs : scale Q (Ls i) = 1) {τ : F} (hτ : scale Q (Ls j) = R ∙ τ) (hτ1 : dord hπ τ = 1) :
    dord hπ (a j) ≤ dord hπ (a i) + 2 := by
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have hτ0 : τ ≠ 0 := by rintro rfl; have := hτ1; simp [dord] at this
  have hc : scale Q (Ls j) = (R ∙ algebraMap R F π) * scale Q (Ls i) := by
    rw [hs, mul_one, hτ]
    exact (span_eq_iff_dord hπ hτ0 hpi).2 (by rw [hτ1, dord_pi hπ])
  have hmem : algebraMap R F π ^ 2 * a i ∈ fundNormGroup Q L Ls j :=
    fundNormGroup_sq_smul_le Q hfg hJ hc ⟨a i, (ha i).1, rfl⟩
  have hn : algebraMap R F π ^ 2 * a i ∈ R ∙ a j := by
    rw [(ha j).2]; exact normGroup_subset_normIdeal Q _ hmem
  have := (mem_span_iff hπ (mul_ne_zero (pow_ne_zero _ hpi) hai) haj).1 hn
  rw [dord_mul hπ (pow_ne_zero _ hpi) hai, dord_sq hπ hpi, dord_pi hπ] at this
  omega

/-- **Step 5: $\mathfrak f_1 \subseteq 4\mathfrak p$ when $a_1\mathfrak o = 2\mathfrak o$ and $u_2 > u_1$** (O'Meara 1963,
§93F, proof of 93:28, sufficiency, step 5, p. 274: "$a_1\mathfrak o = 2\mathfrak o$ … $a_2\mathfrak o \subseteq
2\mathfrak p$. Hence $\mathfrak f_1 \subseteq 4\mathfrak p$"), from 93:26: every term of $\mathfrak s_1^2\mathfrak f_1$
($\mathfrak d(a_1a_2)$, $a_1\mathfrak w_2$, $a_2\mathfrak w_1$, $a_1a_2\mathfrak o$, $2\mathfrak p^{(u_1+u_2)/2}$) has
order $\ge 2e + 1$, $e = \operatorname{ord} 2$. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 5, p. 274 (f₁ ⊆ 4p)"]
theorem fIdeal_le_four_pi (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls) {a : Fin t → F}
    (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : (j : ℕ) = i + 1) (hs : scale Q (Ls i) = 1)
    (ha2 : dord hπ (a i) = dord hπ (2 : F)) (hu : dord hπ (a i) + 1 ≤ dord hπ (a j)) :
    fIdeal Q L Ls i j ≤ R ∙ (4 * algebraMap R F π) := by
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have h4F : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2F h2F
  have h4pi : (4 : F) * algebraMap R F π ≠ 0 := mul_ne_zero h4F hpi
  have hd4 : dord hπ ((4 : F) * algebraMap R F π) = 2 * dord hπ (2 : F) + 1 := by
    rw [dord_mul hπ h4F hpi, show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F, dord_pi hπ]; ring
  have hσ : scale Q (Ls i) = R ∙ (1 : F) := by rw [hs, Submodule.one_eq_span]
  have hone : scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = fIdeal Q L Ls i j := by
    rw [hs, one_mul, one_mul]
  -- `a_i a_j 𝔬 ⊆ 4𝔭`
  have hprod : R ∙ (a i * a j) ≤ R ∙ (4 * algebraMap R F π) := by
    rw [span_singleton_le_iff_mem, mem_span_iff hπ (mul_ne_zero hai haj) h4pi, hd4, dord_mul hπ hai haj]
    omega
  have hprod' : R ∙ (a j * a i) ≤ R ∙ (4 * algebraMap R F π) := by rw [mul_comm]; exact hprod
  have hw : ∀ k : Fin t, fundWeight Q L Ls k ≤ R ∙ a k := fun k => by
    rw [(ha k).2]; exact (weight_bounds Q _).2.2.2
  rcases Int.even_or_odd (dord hπ (a i) + dord hπ (a j)) with hev | hodd
  · have h := mul_fIdeal_of_even Q hπ h2p hfg hreg hJ ha i j hij hσ hev
    rw [hone] at h
    rw [h]
    refine sup_le (sup_le (sup_le ((quadDefect_le_span _).trans hprod) ?_) ?_) ?_
    · exact (smul_mono_aux (a i) (hw j)).trans (by rw [smul_span_singleton]; exact hprod)
    · exact (smul_mono_aux (a j) (hw i)).trans (by rw [smul_span_singleton]; exact hprod')
    · rw [span_singleton_le_iff_mem]
      have hz : (2 : F) * algebraMap R F π ^ ((dord hπ (a i) + dord hπ (a j)) / 2 + dord hπ (1 : F)) ≠ 0 :=
        mul_ne_zero h2F (zpow_ne_zero _ hpi)
      rw [mem_span_iff hπ hz h4pi, hd4, dord_mul hπ h2F (zpow_ne_zero _ hpi), dord_zpow, dord_one Q hπ]
      obtain ⟨m, hm⟩ := hev
      omega
  · have h := mul_fIdeal_of_odd Q hπ hfg hJ ha i j hodd
    rw [hone] at h
    rw [h]; exact hprod

/-- **The elements $4\rho/a_1$, $4\rho/b_1$ lie in $\mathfrak g_2$ when neither (ii) nor (iii) applies at the first
index** (O'Meara 1963, §93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275: "Otherwise $\mathfrak w_2
\supseteq 4\mathfrak w_1^{-1}$ … Now $K_2'$ represents a number whose order is equal to the order of
$4a_1^{-1}\mathfrak o$"; and "if $\mathfrak w_2 \supseteq 4a_1^{-1}\mathfrak o$ we can proceed as in step 4"). Here
$\mathfrak s_1 = \mathfrak o$, $\mathfrak w_1 = b\mathfrak o$, $\mathfrak w_2 = b_2\mathfrak o$, and either $u_2 = u_1$
(then $\mathfrak f_1 = a_2\mathfrak w_1$ and $\neg$(ii) gives $\mathfrak w_1\mathfrak w_2 \supseteq 4\mathfrak o$), or
$u_2 = u_1 + 1$ with $a_1\mathfrak o \supsetneq 2\mathfrak o$ ($\mathfrak f_1 = a_1a_2\mathfrak o$, $\neg$(ii) gives
$\mathfrak w_2 \supseteq 4a_1^{-1}\mathfrak o$; if $\mathfrak w_1 = a_1\mathfrak p$, the element $4\rho/b$ is
$a_2\varepsilon^2$ plus an element of $\mathfrak w_2$ by the perfectness of the residue field), or
$\mathfrak s_2 = \mathfrak p$ and $u_2 = u_1 + 2$ ($\mathfrak f_1 = a_1\mathfrak w_2$, $\neg$(iii) gives
$\mathfrak w_1\mathfrak w_2 \supseteq 4\mathfrak o$). Indices $0$-based: `i`, `j`. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 4, 6, 7, pp. 274–275 (4ρ/a₁, 4ρ/b₁ ∈ g₂)"]
theorem mem_fundNormGroup_of_not_cond (hπ : Irreducible π) (h2p : ¬ IsUnit (2 : R)) {L : Submodule R V}
    (hfg : L.FG) (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hJ : IsJordanSplitting Q L Ls)
    {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) (i j : Fin t) (hij : (j : ℕ) = i + 1)
    (hs : scale Q (Ls i) = 1) {b bj : F} (hb0 : b ≠ 0) (hb : fundWeight Q L Ls i = R ∙ b) (hbj0 : bj ≠ 0)
    (hbj : fundWeight Q L Ls j = R ∙ bj)
    (hcase : dord hπ (a j) = dord hπ (a i) ∨ (dord hπ (a j) = dord hπ (a i) + 1 ∧ dord hπ (a i) < dord hπ (2 : F)) ∨
      ∃ τ : F, scale Q (Ls j) = R ∙ τ ∧ dord hπ τ = 1 ∧ dord hπ (a j) = dord hπ (a i) + 2)
    (hnii : ¬ fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j))
    (hniii : ¬ fIdeal Q L Ls i j < (4 * a i) • (1 / fundWeight Q L Ls i)) (ρ : R) :
    4 * algebraMap R F ρ / a i ∈ fundNormGroup Q L Ls j ∧ 4 * algebraMap R F ρ / b ∈ fundNormGroup Q L Ls j := by
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hpi := alg_pi_ne_zero (R := R) (F := F) hπ
  have hai := fundNormGenerator_ne_zero Q hfg hJ ha i
  have haj := fundNormGenerator_ne_zero Q hfg hJ ha j
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have h4F : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2F h2F
  have hd4 : dord hπ (4 : F) = 2 * dord hπ (2 : F) := by
    rw [show (4 : F) = 2 * 2 by norm_num, dord_mul hπ h2F h2F]; ring
  have hσ : scale Q (Ls i) = R ∙ (1 : F) := by rw [hs, Submodule.one_eq_span]
  have hone : scale Q (Ls i) * scale Q (Ls i) * fIdeal Q L Ls i j = fIdeal Q L Ls i j := by
    rw [hs, one_mul, one_mul]
  -- `ord a_i ≤ ord b`
  have hbai : dord hπ (a i) ≤ dord hπ b := by
    have : b ∈ R ∙ a i := by
      rw [(ha i).2]; exact (weight_bounds Q _).2.2.2 (by rw [fundWeight] at hb; rw [hb]; exact mem_span_singleton_self b)
    exact (mem_span_iff hπ hb0 hai).1 this
  -- membership in `𝔴_j ⊆ 𝔤_j` by orders
  have hmemw : ∀ x : F, (x ≠ 0 → dord hπ bj ≤ dord hπ x) → x ∈ fundNormGroup Q L Ls j := fun x hx =>
    fundWeight_subset Q j (hbj ▸ mem_span_of_dord Q hπ hbj0 hx)
  have hx1 : ∀ x : F, x ≠ 0 → x = 4 * algebraMap R F ρ / a i → dord hπ x ≥ dord hπ (4 : F) - dord hπ (a i) := by
    intro x hx hxe
    have hρ : algebraMap R F ρ ≠ 0 := fun h => hx (by rw [hxe, h]; simp)
    rw [hxe, div_eq_mul_inv, dord_mul hπ (mul_ne_zero h4F hρ) (inv_ne_zero hai), dord_mul hπ h4F hρ]
    have h1 := dord_alg_nonneg (F := F) hπ (fun h : ρ = 0 => hρ (by rw [h, map_zero]))
    have h2 : dord hπ (a i)⁻¹ = - dord hπ (a i) := by
      have := dord_mul hπ hai (inv_ne_zero hai); rw [mul_inv_cancel₀ hai, dord_one Q hπ] at this; omega
    omega
  have hx2 : ∀ x : F, x ≠ 0 → x = 4 * algebraMap R F ρ / b → dord hπ x ≥ dord hπ (4 : F) - dord hπ b ∧
      (dord hπ x = dord hπ (4 : F) - dord hπ b ∨ dord hπ (4 : F) - dord hπ b + 1 ≤ dord hπ x) := by
    intro x hx hxe
    have hρ : algebraMap R F ρ ≠ 0 := fun h => hx (by rw [hxe, h]; simp)
    rw [hxe, div_eq_mul_inv, dord_mul hπ (mul_ne_zero h4F hρ) (inv_ne_zero hb0), dord_mul hπ h4F hρ]
    have h1 := dord_alg_nonneg (F := F) hπ (fun h : ρ = 0 => hρ (by rw [h, map_zero]))
    have h2 : dord hπ b⁻¹ = - dord hπ b := by
      have := dord_mul hπ hb0 (inv_ne_zero hb0); rw [mul_inv_cancel₀ hb0, dord_one Q hπ] at this; omega
    omega
  rcases hcase with hu | ⟨hu, hlt2⟩ | ⟨τ, hτ, hτ1, hu⟩
  · -- `u_j = u_i`: `𝔣 = a_j b 𝔬`, `¬(ii)`: `ord b + ord b_j ≤ ord 4`
    have h := mul_fIdeal_of_dord_eq Q hπ h2p hfg hreg hJ ha i j hij hσ hu
    rw [hone, hb, smul_span_singleton] at h
    rw [h, hbj, NecBase.smul_one_div_span hbj0] at hnii
    have hk := dord_le_of_not_lt Q hπ (mul_ne_zero haj hb0) (mul_ne_zero (mul_ne_zero h4F haj) (inv_ne_zero hbj0)) hnii
    have hbjinv : dord hπ bj⁻¹ = - dord hπ bj := by
      have := dord_mul hπ hbj0 (inv_ne_zero hbj0); rw [mul_inv_cancel₀ hbj0, dord_one Q hπ] at this; omega
    rw [dord_mul hπ haj hb0, dord_mul hπ (mul_ne_zero h4F haj) (inv_ne_zero hbj0), dord_mul hπ h4F haj,
      hbjinv] at hk
    exact ⟨hmemw _ fun hx => by have := hx1 _ hx rfl; omega, hmemw _ fun hx => by have := (hx2 _ hx rfl).1; omega⟩
  · -- `u_j = u_i + 1`: `𝔣 = a_i a_j 𝔬`, `¬(ii)`: `u_i + ord b_j ≤ ord 4`
    have h := mul_fIdeal_of_dord_succ Q hπ hfg hJ ha i j hu
    rw [hone] at h
    rw [h, hbj, NecBase.smul_one_div_span hbj0] at hnii
    have hk := dord_le_of_not_lt Q hπ (mul_ne_zero hai haj) (mul_ne_zero (mul_ne_zero h4F haj) (inv_ne_zero hbj0)) hnii
    have hbjinv : dord hπ bj⁻¹ = - dord hπ bj := by
      have := dord_mul hπ hbj0 (inv_ne_zero hbj0); rw [mul_inv_cancel₀ hbj0, dord_one Q hπ] at this; omega
    rw [dord_mul hπ hai haj, dord_mul hπ (mul_ne_zero h4F haj) (inv_ne_zero hbj0), dord_mul hπ h4F haj,
      hbjinv] at hk
    refine ⟨hmemw _ fun hx => by have := hx1 _ hx rfl; omega, ?_⟩
    -- `ord b ≤ u_i + 1` since `a_i π ∈ 𝔴_i = b𝔬`
    have hbu : dord hπ b ≤ dord hπ (a i) + 1 := by
      have hm := smul_pi_mem_fundWeight Q hπ h2p hfg hreg hJ ha hij' hu
      rw [hb] at hm
      have := (mem_span_iff hπ (mul_ne_zero hai hpi) hb0).1 hm
      rw [dord_mul hπ hai hpi, dord_pi hπ] at this; exact this
    set x := 4 * algebraMap R F ρ / b with hxdef
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    by_cases hbig : dord hπ bj ≤ dord hπ x
    · exact hmemw _ fun _ => hbig
    -- the remaining case: `ord x = ord 4 - u_i - 1`, `x = a_j · π^{2k} · v`
    push Not at hbig
    obtain ⟨hge, -⟩ := hx2 x hx0 rfl
    have hxe : dord hπ x = dord hπ (4 : F) - dord hπ (a i) - 1 := by omega
    have hy0 : x / a j ≠ 0 := div_ne_zero hx0 haj
    have hyd : dord hπ (x / a j) = 2 * (dord hπ (2 : F) - dord hπ (a i) - 1) := by
      have := dord_mul hπ hy0 haj
      rw [div_mul_cancel₀ _ haj] at this; omega
    obtain ⟨k, hk'⟩ : ∃ k : ℕ, (k : ℤ) = dord hπ (2 : F) - dord hπ (a i) - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨v, hv, hve⟩ := dord_spec hπ hy0
    have h2m : (2 : R) ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h2p
    obtain ⟨s, hsv⟩ := CoreTwo.exists_sq_residue h2m v
    have hmax : maximalIdeal R = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
    rw [hmax] at hsv
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hsv
    have hset := fundNormGroup_eq_sq_add Q h2p hfg hreg hJ j (ha j)
    have hxeq : x = a j * algebraMap R F (π ^ k * s) ^ 2 +
        a j * algebraMap R F (m * π ^ (2 * k + 1)) := by
      have hpk : algebraMap R F π ^ dord hπ (x / a j) = algebraMap R F π ^ (2 * k) := by
        rw [hyd, ← hk', show (2 : ℤ) * k = ((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      have : x = a j * (x / a j) := by field_simp
      rw [this, hve, hpk]
      have hvs : v = s ^ 2 + m * π := by linear_combination -hm
      rw [hvs]; simp only [map_add, map_mul, map_pow]; ring
    have hmemx : x ∈ (fundNormGroup Q L Ls j : Set F) := by
      rw [hset]
      refine ⟨π ^ k * s, _, ?_, hxeq⟩
      rw [hbj]
      refine mem_span_of_dord Q hπ hbj0 fun hw0 => ?_
      have hw' : algebraMap R F (m * π ^ (2 * k + 1)) ≠ 0 := right_ne_zero_of_mul hw0
      have hm0 : algebraMap R F m ≠ 0 := by intro h; apply hw'; rw [map_mul, h, zero_mul]
      rw [dord_mul hπ haj hw', map_mul, map_pow, dord_mul hπ hm0 (pow_ne_zero _ hpi)]
      have := dord_alg_nonneg (F := F) hπ (fun h : m = 0 => hm0 (by rw [h, map_zero]))
      rw [show algebraMap R F π ^ (2 * k + 1) = algebraMap R F π ^ ((2 * k + 1 : ℕ) : ℤ) by norm_cast, dord_zpow]
      push_cast; omega
    exact hmemx
  · -- `𝔰_j = 𝔭`, `u_j = u_i + 2`: `𝔣 = a_i b_j 𝔬`, `¬(iii)`: `ord b + ord b_j ≤ ord 4`
    have hτ0 : dord hπ τ = dord hπ (1 : F) + 1 := by rw [hτ1, dord_one Q hπ]; simp
    have h := mul_fIdeal_of_dord_add_two Q hπ h2p hfg hreg hJ ha i j hij hσ hτ hu hτ0
    rw [hone, hbj, smul_span_singleton] at h
    rw [h, hb, NecBase.smul_one_div_span hb0] at hniii
    have hk := dord_le_of_not_lt Q hπ (mul_ne_zero hai hbj0) (mul_ne_zero (mul_ne_zero h4F hai) (inv_ne_zero hb0))
      hniii
    have hbinv : dord hπ b⁻¹ = - dord hπ b := by
      have := dord_mul hπ hb0 (inv_ne_zero hb0); rw [mul_inv_cancel₀ hb0, dord_one Q hπ] at this; omega
    rw [dord_mul hπ hai hbj0, dord_mul hπ (mul_ne_zero h4F hai) (inv_ne_zero hb0), dord_mul hπ h4F hai,
      hbinv] at hk
    exact ⟨hmemw _ fun hx => by have := hx1 _ hx rfl; omega, hmemw _ fun hx => by have := (hx2 _ hx rfl).1; omega⟩

include Q in
/-- An element of $4\mathfrak p$ is $4\mu$ with $\mu \in \mathfrak p$. -/
lemma exists_four_mul_of_le (hπ : Irreducible π) {X : Submodule R F} (h : X ≤ R ∙ (4 * algebraMap R F π)) :
    ∀ x ∈ X, ∃ m ∈ maximalIdeal R, x = 4 * algebraMap R F m := by
  intro x hx
  obtain ⟨r, hr⟩ := mem_span_singleton.mp (h hx)
  refine ⟨r * π, Ideal.mul_mem_left _ _ hπ.not_isUnit, ?_⟩
  rw [← hr, Algebra.smul_def, map_mul]; ring

end CoreFactor
