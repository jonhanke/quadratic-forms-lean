/-
# O'Meara 93:24: the dual of a lattice with a Jordan splitting

**Setting** (as in `Sec93E.lean`, `Sec93Sat.lean`): $R$ a discrete valuation ring with fraction field $F$,
$2 \in F^\times$, $(V, Q)$ a finite-dimensional quadratic space over $F$; lattices are `Submodule R V`; $L^\#$ is
`dual Q L` (§82F). Indices are $0$-based, so O'Meara's $i \mapsto t - i + 1$ is `Fin.rev`.

**Proves** (O'Meara 1963, §93E, 93:24, p. 266)
* `isJordanSplitting_dual`: a Jordan splitting $L = L_1 \perp \cdots \perp L_t$ with $\mathfrak s_i = \sigma_i\mathfrak o$
  gives the Jordan splitting $L^\# = \pi^{-s_t}L_t \perp \cdots \perp \pi^{-s_1}L_1$, i.e. components
  $\sigma_{t-i+1}^{-1}L_{t-i+1}$, with scales $\mathfrak s_{t-i+1}^{-1}$;
* `isSaturated_dual`, `fundNormGroup_dual`, `fundWeight_dual`, `isFundNormGenerators_dual`, `fIdeal_dual`: when all
  $\dim L_i \ge 3$, the splitting of $L$ is saturated and 93:21 (`SaturatedSplittingExistence`) holds, the splitting of
  $L^\#$ is saturated, $\mathfrak g_i^\# = \sigma_{t-i+1}^{-2}\mathfrak g_{t-i+1}$, $\mathfrak w_i^\# =
  \sigma_{t-i+1}^{-2}\mathfrak w_{t-i+1}$, $a_i^\# = \sigma_{t-i+1}^{-2}a_{t-i+1}$ and $\mathfrak f_i^\# =
  \mathfrak f_{t-i}$.

**Hypotheses added.** The book first reduces to $\dim L_i \ge 3$ by $\mathfrak s_i$-modular hyperbolic adjunctions; that
reduction is not formalized, so the dimension hypothesis `3 ≤ finrank R (Ls i)` is kept (the book's case after its
reduction).
-/
import QuadFormsKB.Literature.OMeara.Sec93EFund
import QuadFormsKB.Literature.OMeara.Sec93Sat

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

open FIdealAux FundAux

namespace Dual93

section Aux

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

lemma one_div_span {σ : F} (hσ : σ ≠ 0) : (1 : Submodule R F) / (R ∙ σ) = R ∙ σ⁻¹ := by
  ext z
  rw [mem_div_span_iff, Submodule.mem_span_singleton, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [Algebra.smul_def, hr]; field_simp⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [Algebra.smul_def]; field_simp⟩

lemma one_div_lt_one_div {A B : Submodule R F} (hA : A.FG) (hA0 : A ≠ ⊥) (hB : B.FG) (hB0 : B ≠ ⊥)
    (h : A < B) : 1 / B < 1 / A := by
  have hle : 1 / B ≤ 1 / A := by
    intro z hz
    rw [Submodule.mem_div_iff_forall_mul_mem] at hz ⊢
    exact fun w hw => hz w (h.le hw)
  refine lt_of_le_of_ne hle fun heq => ?_
  have := congrArg (fun X => 1 / X) heq
  simp only [one_div_one_div hB hB0, one_div_one_div hA hA0] at this
  exact h.ne this.symm

lemma exists_components {t : ℕ} {Ls : Fin t → Submodule R V} {L : Submodule R V} (hL : ⨆ i, Ls i = L) {x : V}
    (hx : x ∈ span F (L : Set V)) :
    ∃ f : Fin t → V, (∀ j, f j ∈ span F (Ls j : Set V)) ∧ x = ∑ j, f j := by
  classical
  subst hL
  let P : V → Prop := fun x => ∃ f : Fin t → V, (∀ j, f j ∈ span F (Ls j : Set V)) ∧ x = ∑ j, f j
  have hzero : P 0 := ⟨0, fun j => zero_mem _, by simp⟩
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, fun j => add_mem (hf j) (hg j), by simp [Finset.sum_add_distrib]⟩
  refine span_induction (p := fun x _ => P x) (fun l hl => ?_) hzero (fun a b _ _ ha hb => hadd a b ha hb)
    (fun c a _ ha => ?_) hx
  · refine Submodule.iSup_induction Ls (motive := P) hl (fun j y hy => ?_) hzero hadd
    exact ⟨fun k => if k = j then y else 0, fun k => by
      by_cases hk : k = j
      · subst hk; simpa using subset_span hy
      · simp [hk], by simp⟩
  · obtain ⟨f, hf, rfl⟩ := ha
    exact ⟨fun j => c • f j, fun j => smul_mem _ _ (hf j), by simp [Finset.smul_sum]⟩

lemma bil_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (y : V) :
    bil Q (∑ k ∈ s, f k) y = ∑ k ∈ s, bil Q (f k) y := by
  simp [bil, map_sum, LinearMap.sum_apply]

lemma bil_span_orth {t : ℕ} {Ls : Fin t → Submodule R V} {L : Submodule R V} (hL : IsOrthSplit Q L Ls)
    {j k : Fin t} (hjk : j ≠ k) {x : V} (hx : x ∈ span F (Ls j : Set V)) {y : V} (hy : y ∈ Ls k) :
    bil Q x y = 0 := by
  rw [bil_comm]
  exact bil_zero_of_mem_span_F Q (fun z hz => hL.orth k j hjk.symm y hy z hz) hx

lemma dual_eq_iSup_of_orth {t : ℕ} {Ls : Fin t → Submodule R V} {L : Submodule R V}
    (hL : IsOrthSplit Q L Ls) : dual Q L = ⨆ j, dual Q (Ls j) := by
  have hLle : ∀ j, Ls j ≤ L := fun j => hL.iSup_eq ▸ le_iSup Ls j
  apply le_antisymm
  · rintro x ⟨hx, hB⟩
    obtain ⟨f, hf, rfl⟩ := exists_components hL.iSup_eq hx
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem j ⟨hf j, fun y hy => ?_⟩
    have h1 := hB y (hLle j hy)
    rw [bil_sum_left, Finset.sum_eq_single j (fun k _ hk => bil_span_orth Q hL hk (hf k) hy)
      (fun h => absurd (Finset.mem_univ j) h)] at h1
    exact h1
  · refine iSup_le fun j => ?_
    rintro x ⟨hx, hB⟩
    refine ⟨span_mono (hLle j) hx, fun y hy => ?_⟩
    refine Submodule.iSup_induction Ls (motive := fun y => bil Q x y ∈ (1 : Submodule R F)) (hL.iSup_eq ▸ hy)
      (fun k z hz => ?_) (by simp [bil]) (fun a b ha hb => by
        rw [bil_add_right]; exact add_mem ha hb)
    by_cases hk : j = k
    · subst hk; exact hB z hz
    · rw [bil_span_orth Q hL hk hx hz]; exact zero_mem _

lemma isRegular_of_orthSplit {t : ℕ} {Ls : Fin t → Submodule R V} {L : Submodule R V}
    (hL : IsOrthSplit Q L Ls) (hreg : ∀ j, IsRegular Q (Ls j)) : IsRegular Q L := by
  intro x hx hxo
  obtain ⟨f, hf, rfl⟩ := exists_components hL.iSup_eq (subset_span (R := F) hx)
  have : ∀ j, f j = 0 := fun j => by
    refine (isRegular_iff_span Q (Ls j)).1 (hreg j) (f j) (hf j) fun z hz => ?_
    refine bil_zero_of_mem_span_F Q (fun w hw => ?_) hz
    have h1 := hxo w (hL.iSup_eq ▸ le_iSup Ls j hw)
    rw [bil_sum_left, Finset.sum_eq_single j (fun k _ hk => bil_span_orth Q hL hk (hf k) hw)
      (fun h => absurd (Finset.mem_univ j) h)] at h1
    exact h1
  simp [this]

/-- If `M` is `R ∙ σ`-modular and finitely generated then `M^# = σ⁻¹ M`. -/
lemma dual_eq_smul {σ : F} (hσ : σ ≠ 0) {M : Submodule R V} (hM : IsModular Q (R ∙ σ) M) (hfg : M.FG) :
    dual Q M = (R ∙ σ⁻¹) • M := by
  rw [dual_eq_of_isModular Q hM hfg, one_div_span hσ]

lemma dual_ne_bot {σ : F} {M : Submodule R V} (hM : IsModular Q (R ∙ σ) M) (hfg : M.FG) :
    dual Q M ≠ ⊥ := by
  intro h
  have hreg := isRegular_of_isModular Q hM hfg
  have hM0 : M = ⊥ := by
    have h1 : dual Q (dual Q M) = M := dual_dual Q hfg hreg
    rw [h] at h1
    rw [← h1]
    ext x
    simp only [mem_dual, Submodule.mem_bot]
    constructor
    · rintro ⟨hx, -⟩
      have : (↑(⊥ : Submodule R V) : Set V) = {0} := by ext; simp
      rw [this, Submodule.span_zero_singleton, Submodule.mem_bot] at hx
      exact hx
    · rintro rfl
      exact ⟨zero_mem _, fun y hy => by simp [bil]⟩
  have := hM.2.1
  rw [hM0, scale_bot] at this
  exact hM.1 this.symm

lemma isModular_dual {σ : F} (hσ : σ ≠ 0) {M : Submodule R V} (hM : IsModular Q (R ∙ σ) M) (hfg : M.FG) :
    IsModular Q (R ∙ σ⁻¹) (dual Q M) := by
  have hreg := isRegular_of_isModular Q hM hfg
  refine (isModular_iff_smul_dual Q (dual_fg Q hfg hreg) (dual_ne_bot Q hM hfg) (isRegular_dual Q hfg hreg)
    (fg_span_singleton _) (by simpa using hσ)).2 ?_
  rw [dual_dual Q hfg hreg, dual_eq_smul Q hσ hM hfg]

end Aux

end Dual93

section Part1

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Dual93

/-- **93:24, the Jordan splitting of $L^\#$** (O'Meara 1963, §93E, 93:24, p. 266): "Consider a Jordan splitting
$L = L_1 \perp \cdots \perp L_t$. Then by §82F and 82:14 we get a Jordan splitting $L^\# = L_t^\# \perp \cdots \perp
L_1^\# = \pi^{-s_t}L_t \perp \cdots \perp \pi^{-s_1}L_1$ in which the fundamental scales of $L^\#$ are
$\mathfrak s_t^{-1} \supset \cdots \supset \mathfrak s_1^{-1}$." Here $\mathfrak s_i = \sigma_i\mathfrak o$ and the $i$-th
component of the splitting of $L^\#$ is $\sigma_{t-i+1}^{-1}L_{t-i+1}$ (`Fin.rev` reverses the $0$-based index). The
scales are $\sigma_{\mathrm{rev}\, i}^{-1}\mathfrak o = \mathfrak s_{\mathrm{rev}\,i}^{-1}$. -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (Jordan splitting of L^#)"]
theorem isJordanSplitting_dual {L : Submodule R V} [L.IsLattice F] {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) {σ : Fin t → F} (hσ : ∀ i, scale Q (Ls i) = R ∙ σ i) :
    IsJordanSplitting Q (dual Q L) (fun i => (R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)) ∧
      ∀ i, scale Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)) = R ∙ (σ (Fin.rev i))⁻¹ ∧
        scale Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)) = 1 / scale Q (Ls (Fin.rev i)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hfgi : ∀ j, (Ls j).FG := fun j => FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls j)
  have hmod : ∀ j, IsModular Q (R ∙ σ j) (Ls j) := fun j => by
    have := hL.modular j; rwa [hσ j] at this
  have hσ0 : ∀ j, σ j ≠ 0 := fun j h => (hmod j).1 (by rw [h]; simp)
  have hd : ∀ i, dual Q (Ls (Fin.rev i)) = (R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i) := fun i =>
    dual_eq_smul Q (hσ0 _) (hmod _) (hfgi _)
  have hreg : ∀ j, IsRegular Q (Ls j) := fun j => isRegular_of_isModular Q (hmod j) (hfgi j)
  have hscale : ∀ i, scale Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)) = R ∙ (σ (Fin.rev i))⁻¹ := fun i => by
    rw [← hd]; exact (isModular_dual Q (hσ0 _) (hmod _) (hfgi _)).2.1
  have hone : ∀ i, R ∙ (σ (Fin.rev i))⁻¹ = 1 / scale Q (Ls (Fin.rev i)) := fun i => by
    rw [hσ, one_div_span (hσ0 _)]
  refine ⟨⟨⟨fun i j hij x hx y hy => ?_, ?_, ?_⟩, fun i => ?_, fun i j hij => ?_⟩, fun i => ⟨hscale i, ?_⟩⟩
  · obtain ⟨a, ha, rfl⟩ := mem_span_singleton_smul_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_span_singleton_smul_iff.1 hy
    rw [bil_smul_left, bil_smul_right, hL.split.orth _ _ (fun h => hij (Fin.rev_injective h)) a ha b hb]
    simp
  · refine iSupIndep_of_orth Q (fun i j hij x hx y hy => ?_) fun i => ?_
    · obtain ⟨a, ha, rfl⟩ := mem_span_singleton_smul_iff.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_span_singleton_smul_iff.1 hy
      rw [bil_smul_left, bil_smul_right, hL.split.orth _ _ (fun h => hij (Fin.rev_injective h)) a ha b hb]
      simp
    · rw [← hd]; exact isRegular_dual Q (hfgi _) (hreg _)
  · rw [dual_eq_iSup_of_orth Q hL.split]
    simp only [← hd]
    exact Equiv.iSup_comp (g := fun j => dual Q (Ls j)) Fin.revPerm
  · have h := isModular_dual Q (hσ0 (Fin.rev i)) (hmod _) (hfgi _)
    rw [hscale i, ← hd i]
    exact h
  · have hlt : scale Q (Ls (Fin.rev i)) < scale Q (Ls (Fin.rev j)) :=
      hL.scale_strictAnti (Fin.rev_lt_rev.2 hij)
    show scale Q ((R ∙ (σ (Fin.rev j))⁻¹) • Ls (Fin.rev j)) < scale Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i))
    rw [hscale, hscale, hone, hone]
    refine Dual93.one_div_lt_one_div ?_ ?_ ?_ ?_ hlt
    all_goals first
      | (rw [hσ]; exact fg_span_singleton _)
      | (rw [hσ]; intro h; exact hσ0 _ (Submodule.span_singleton_eq_bot.1 h))
  · rw [hscale, hone]

end Part1

namespace Dual93

section Alg

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]

lemma defect_iSup_smul2 (p q : F) (g g' : AddSubgroup F) :
    (⨆ (x : F) (_ : x ∈ g.map (AddMonoidHom.mulLeft (p ^ 2))) (y : F)
        (_ : y ∈ g'.map (AddMonoidHom.mulLeft (q ^ 2))), quadDefect R (x * y)) =
      (R ∙ ((p * q) ^ 2)) * ⨆ (x : F) (_ : x ∈ g) (y : F) (_ : y ∈ g'), quadDefect R (x * y) := by
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hy
    have e : (AddMonoidHom.mulLeft (p ^ 2)) a * (AddMonoidHom.mulLeft (q ^ 2)) b = (p * q) ^ 2 * (a * b) := by
      simp only [AddMonoidHom.coe_mulLeft]; ring
    rw [e, quadDefect_sq_mul]
    refine mul_le_mul' le_rfl ?_
    exact le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup_of_le b <| le_iSup_of_le hb le_rfl
  · simp only [Submodule.mul_iSup]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb => ?_
    rw [← quadDefect_sq_mul]
    have e : (p * q) ^ 2 * (a * b) = (AddMonoidHom.mulLeft (p ^ 2)) a * (AddMonoidHom.mulLeft (q ^ 2)) b := by
      simp only [AddMonoidHom.coe_mulLeft]; ring
    rw [e]
    exact le_iSup_of_le _ <| le_iSup_of_le (AddSubgroup.mem_map.2 ⟨a, ha, rfl⟩) <| le_iSup_of_le _ <|
      le_iSup_of_le (AddSubgroup.mem_map.2 ⟨b, hb, rfl⟩) le_rfl

lemma defect_iSup_comm (g g' : AddSubgroup F) :
    (⨆ (x : F) (_ : x ∈ g) (y : F) (_ : y ∈ g'), quadDefect R (x * y)) =
      ⨆ (y : F) (_ : y ∈ g') (x : F) (_ : x ∈ g), quadDefect R (y * x) := by
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb => ?_
    rw [mul_comm]
    exact le_iSup_of_le b <| le_iSup_of_le hb <| le_iSup_of_le a <| le_iSup_of_le ha le_rfl
  · refine iSup_le fun a => iSup_le fun ha => iSup_le fun b => iSup_le fun hb => ?_
    rw [mul_comm]
    exact le_iSup_of_le b <| le_iSup_of_le hb <| le_iSup_of_le a <| le_iSup_of_le ha le_rfl

lemma sqRoots_dual {p q : F} (hp : p ≠ 0) (hq : q ≠ 0) (n n' : Submodule R F) :
    span R {z : F | (R ∙ z) * (R ∙ z) = ((R ∙ (p ^ 2)) * n) * ((R ∙ (q ^ 2)) * n')} =
      (R ∙ (p * q)) * span R {z : F | (R ∙ z) * (R ∙ z) = n * n'} := by
  rw [← sqRoots_span_smul (mul_ne_zero hp hq) n n']
  have h1 : (R ∙ (p ^ 2)) * (R ∙ (q ^ 2)) = (R ∙ (p * q)) * (R ∙ (p * q)) := by
    rw [span_mul_span', span_mul_span', show p ^ 2 * q ^ 2 = p * q * (p * q) by ring]
  have e : ((R ∙ (p ^ 2)) * n) * ((R ∙ (q ^ 2)) * n') = ((R ∙ (p * q)) * n) * ((R ∙ (p * q)) * n') := by
    calc ((R ∙ (p ^ 2)) * n) * ((R ∙ (q ^ 2)) * n') = ((R ∙ (p ^ 2)) * (R ∙ (q ^ 2))) * (n * n') := by ring
      _ = ((R ∙ (p * q)) * (R ∙ (p * q))) * (n * n') := by rw [h1]
      _ = _ := by ring
  rw [e]

/-- The algebraic core of `fIdeal_dual`: the ideal $\mathfrak f$ of invariants scaled by $p^2$, $q^2$ equals the
ideal of the unscaled invariants in the opposite order. -/
lemma fIdealOf_dual {p q : F} (hp : p ≠ 0) (hq : q ≠ 0) (g g' : AddSubgroup F) (n n' : Submodule R F) :
    fIdealOf R (R ∙ p) (g.map (AddMonoidHom.mulLeft (p ^ 2))) (g'.map (AddMonoidHom.mulLeft (q ^ 2)))
      ((R ∙ (p ^ 2)) * n) ((R ∙ (q ^ 2)) * n') = fIdealOf R (R ∙ q⁻¹) g' g n' n := by
  unfold fIdealOf
  rw [defect_iSup_smul2, sqRoots_dual hp hq, defect_iSup_comm g g', mul_comm n n']
  generalize (⨆ (y : F) (_ : y ∈ g') (x : F) (_ : x ∈ g), quadDefect R (y * x)) = D
  generalize span R {z : F | (R ∙ z) * (R ∙ z) = n' * n} = C
  have hSq : (R ∙ q) * (R ∙ q⁻¹) = 1 := by
    rw [span_mul_span', mul_inv_cancel₀ hq, ← Submodule.one_eq_span]
  have hq2 : (R ∙ (q ^ 2)) = (R ∙ q) * (R ∙ q) := by rw [span_mul_span', _root_.sq]
  have hpq1 : (R ∙ (p * q)) = (R ∙ p) * (R ∙ q) := (span_mul_span' p q).symm
  have hpq2 : (R ∙ ((p * q) ^ 2)) = ((R ∙ p) * (R ∙ q)) * ((R ∙ p) * (R ∙ q)) := by
    rw [← hpq1, span_mul_span', _root_.sq]
  have hAA : (R ∙ p) * (R ∙ p) = R ∙ (p * p) := span_mul_span' p p
  rw [hpq2, hpq1]
  set A := R ∙ p
  set B := R ∙ q
  set Bi := R ∙ q⁻¹
  have key1 : (A * B) * (A * B) * D ⊔ (2 : F) • (A * B * C * A) =
      (A * A) * ((B * B) * D ⊔ (2 : F) • (B * C)) := by
    rw [Submodule.mul_sup, mul_smul_comm]
    exact congrArg₂ (· ⊔ ·) (by ring) (congrArg (fun X => (2 : F) • X) (by ring))
  have key2 : (B * B) * (D ⊔ (2 : F) • (C * Bi)) = (B * B) * D ⊔ (2 : F) • (B * C) := by
    rw [Submodule.mul_sup, mul_smul_comm]
    refine congrArg (fun X => (B * B) * D ⊔ (2 : F) • X) ?_
    calc B * B * (C * Bi) = B * C * (B * Bi) := by ring
      _ = B * C := by rw [hSq, mul_one]
  have key3 : (B * B) * (Bi * Bi) = 1 := by
    calc (B * B) * (Bi * Bi) = (B * Bi) * (B * Bi) := by ring
      _ = 1 := by rw [hSq, one_mul]
  have h1 := div_span_mul_cancel (R := R) (mul_ne_zero hp hp) ((B * B) * D ⊔ (2 : F) • (B * C)) 1
  rw [mul_one, ← hAA] at h1
  have h2 := div_span_mul_cancel (R := R) (pow_ne_zero 2 hq) (D ⊔ (2 : F) • (C * Bi)) (Bi * Bi)
  rw [hq2, key2, key3] at h2
  rw [key1, h1]
  exact h2

end Alg

section Comp

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **The Jordan splitting of $L^\#$ of 93:24**: its $i$-th component is $\sigma_{t-i+1}^{-1}L_{t-i+1}$ (`Fin.rev`
is $i \mapsto t-i+1$ on $0$-based indices). -/
abbrev dualSplit {t : ℕ} (σ : Fin t → F) (Ls : Fin t → Submodule R V) : Fin t → Submodule R V :=
  fun i => (R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)

lemma fg_component {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) (j : Fin t) : (Ls j).FG :=
  FG.of_le hfg (hL.split.iSup_eq ▸ le_iSup Ls j)

lemma isRegular_of_jordan {L : Submodule R V} (hfg : L.FG) {t : ℕ} {Ls : Fin t → Submodule R V}
    (hL : IsJordanSplitting Q L Ls) : IsRegular Q L :=
  isRegular_of_orthSplit Q hL.split fun j => isRegular_of_isModular Q (hL.modular j) (fg_component Q hfg hL j)

lemma sigma_ne_zero {L : Submodule R V} {t : ℕ} {Ls : Fin t → Submodule R V} {σ : Fin t → F}
    (hL : IsJordanSplitting Q L Ls) (hσ : ∀ i, scale Q (Ls i) = R ∙ σ i) (j : Fin t) : σ j ≠ 0 :=
  fun h => (hL.modular j).1 (by rw [hσ j, h]; simp)

lemma isLattice_dual {L : Submodule R V} [L.IsLattice F] (hreg : IsRegular Q L) : (dual Q L).IsLattice F :=
  ⟨dual_fg Q (Submodule.IsLattice.fg (A := F)) hreg, by
    rw [span_dual Q (Submodule.IsLattice.fg (A := F)) hreg]; exact Submodule.IsLattice.span_eq_top⟩

lemma fundNormIdeal_eq_of_sat {K : Submodule R V} {t : ℕ} {Ks : Fin t → Submodule R V}
    (hsat : IsSaturated Q K Ks) (i : Fin t) : fundNormIdeal Q K Ks i = normIdeal Q (Ks i) := by
  unfold fundNormIdeal
  rw [normIdeal_eq_span_normGroup Q (fundSub Q K Ks i), normIdeal_eq_span_normGroup Q (Ks i)]
  exact congrArg (fun g : AddSubgroup F => span R (g : Set F)) (hsat.2 i).symm

lemma fundWeight_eq_of_sat {K : Submodule R V} (hfg : K.FG) {t : ℕ} {Ks : Fin t → Submodule R V}
    (hsat : IsSaturated Q K Ks) (i : Fin t) : fundWeight Q K Ks i = weight Q (Ks i) :=
  weight_congr Q Q (hsat.2 i).symm (scale_fundSub Q hfg hsat.1 i)

lemma isNormGenerator_fundSub_of_sat {K : Submodule R V} {t : ℕ} {Ks : Fin t → Submodule R V}
    (hsat : IsSaturated Q K Ks) (i : Fin t) {b : F} (h : IsNormGenerator Q (Ks i) b) :
    IsNormGenerator Q (fundSub Q K Ks i) b := by
  refine ⟨?_, ?_⟩
  · show b ∈ fundNormGroup Q K Ks i
    rw [← hsat.2 i]; exact h.1
  · show R ∙ b = fundNormIdeal Q K Ks i
    rw [fundNormIdeal_eq_of_sat Q hsat i]; exact h.2

end Comp

end Dual93

section Part2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

open Dual93

/-- **93:24, the Jordan splitting of $L^\#$ is saturated** (O'Meara 1963, §93E, 93:24, p. 266): "Suppose the given
Jordan splitting of $L$ is saturated; then it follows easily from 93:22 and $L^{\#\#} = L$ that the Jordan splitting
$L^\# = \pi^{-s_t}L_t \perp \cdots \perp \pi^{-s_1}L_1$ is saturated." Hypotheses: all $\dim L_i \ge 3$ (the book's
case after its reduction by hyperbolic adjunctions, which is not formalized) and the named statement 93:21 (used
through 93:22, `isSaturated_iff_forall_normGroup_le`, applied to $L^\#$). -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (invariants of L^#)"]
theorem isSaturated_dual (hS : SaturatedSplittingExistence R Q) (h2p : ¬ IsUnit (2 : R))
    (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
    {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hdim : ∀ i, 3 ≤ finrank R (Ls i))
    (hsat : IsSaturated Q L Ls) {σ : Fin t → F} (hσ : ∀ i, scale Q (Ls i) = R ∙ σ i) :
    IsSaturated Q (dual Q L) (dualSplit σ Ls) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hreg : IsRegular Q L := isRegular_of_jordan Q hfg hL
  have : (dual Q L).IsLattice F := isLattice_dual Q hreg
  have hfgM : (dual Q L).FG := dual_fg Q hfg hreg
  have hσ0 := sigma_ne_zero Q hL hσ
  obtain ⟨hM, hscale⟩ := isJordanSplitting_dual Q hL hσ
  have hdimM : ∀ i, 3 ≤ finrank R (dualSplit σ Ls i) := fun i => by
    have hmod : IsModular Q (R ∙ σ (Fin.rev i)) (Ls (Fin.rev i)) := by
      have := hL.modular (Fin.rev i); rwa [hσ] at this
    have hd : dualSplit σ Ls i = dual Q (Ls (Fin.rev i)) :=
      (dual_eq_smul Q (hσ0 _) hmod (fg_component Q hfg hL _)).symm
    rw [hd, finrank_dual Q (fg_component Q hfg hL _) (isRegular_of_isModular Q hmod (fg_component Q hfg hL _))]
    exact hdim _
  refine (isSaturated_iff_forall_normGroup_le hS h2p hQ hM hdimM).2 ?_
  intro t' Ks hK i j hij
  obtain ⟨h, hs⟩ := hM.sameJordanType Q hfgM hK
  subst h
  have hij' : i = j := Fin.ext hij
  subst hij'
  have hτ : ∀ k, scale Q (Ks k) = R ∙ (σ (Fin.rev k))⁻¹ := fun k => by
    have := (hs k).1
    simp only [Fin.cast_eq_self] at this
    rw [← this]; exact (hscale k).1
  have hK' : IsJordanSplitting Q L (fun j => (R ∙ σ j) • Ks (Fin.rev j)) := by
    have := (isJordanSplitting_dual Q hK (σ := fun k => (σ (Fin.rev k))⁻¹) hτ).1
    simpa only [Fin.rev_rev, inv_inv, dual_dual Q hfg hreg] using this
  have hle := hsat.normGroup_le hfg _ hK' (Fin.rev i) (Fin.rev i) rfl
  intro z hz
  show z ∈ normGroup Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i))
  have hσi := hσ0 (Fin.rev i)
  rw [mem_normGroup_smul_lattice Q (inv_ne_zero hσi)]
  apply hle
  show z / ((σ (Fin.rev i))⁻¹) ^ 2 ∈ normGroup Q ((R ∙ σ (Fin.rev i)) • Ks (Fin.rev (Fin.rev i)))
  rw [mem_normGroup_smul_lattice Q hσi, Fin.rev_rev]
  convert hz using 1
  field_simp

section Invariants

variable (hS : SaturatedSplittingExistence R Q) (h2p : ¬ IsUnit (2 : R))
  (hQ : (QuadraticMap.associated Q).Nondegenerate) {L : Submodule R V} [L.IsLattice F] {t : ℕ}
  {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls) (hdim : ∀ i, 3 ≤ finrank R (Ls i))
  (hsat : IsSaturated Q L Ls) {σ : Fin t → F} (hσ : ∀ i, scale Q (Ls i) = R ∙ σ i)

include hS h2p hQ hL hdim hsat hσ

/-- **93:24, fundamental norm groups of $L^\#$** (O'Meara 1963, §93E, 93:24, p. 266): $\mathfrak g_i^\# =
\sigma_{t-i+1}^{-2}\mathfrak g_{t-i+1}$ (the image of $\mathfrak g_{t-i+1}$ under multiplication by
$\sigma_{t-i+1}^{-2}$), for the splitting `dualSplit σ Ls` of $L^\#$ (`Fin.rev` is $i \mapsto t-i+1$). From the
saturation of both splittings and 93:7 (`normGroup_smul_lattice`). -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (invariants of L^#)"]
theorem fundNormGroup_dual (i : Fin t) :
    fundNormGroup Q (dual Q L) (dualSplit σ Ls) i =
      (fundNormGroup Q L Ls (Fin.rev i)).map (AddMonoidHom.mulLeft ((σ (Fin.rev i))⁻¹ ^ 2)) := by
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  rw [← hsatM.2 i, ← hsat.2 (Fin.rev i)]
  exact normGroup_smul_lattice Q _ _

/-- **93:24, fundamental weights of $L^\#$** (O'Meara 1963, §93E, 93:24, p. 266): $\mathfrak w_i^\# =
\sigma_{t-i+1}^{-2}\mathfrak w_{t-i+1}$. -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (invariants of L^#)"]
theorem fundWeight_dual (i : Fin t) :
    fundWeight Q (dual Q L) (dualSplit σ Ls) i = (σ (Fin.rev i))⁻¹ ^ 2 • fundWeight Q L Ls (Fin.rev i) := by
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hreg : IsRegular Q L := isRegular_of_jordan Q hfg hL
  have : (dual Q L).IsLattice F := isLattice_dual Q hreg
  rw [fundWeight_eq_of_sat Q (Submodule.IsLattice.fg (A := F)) hsatM i, fundWeight_eq_of_sat Q hfg hsat,
    smul_eq_span_mul]
  exact weight_smul_lattice Q (inv_ne_zero (sigma_ne_zero Q hL hσ _)) _

/-- The norm ideals $\mathfrak nL^{\mathfrak s_i}$ of $L^\#$: $\sigma_{t-i+1}^{-2}\mathfrak o \cdot
\mathfrak nL^{\mathfrak s_{t-i+1}}$ (from 93:7 for `normIdeal`). -/
theorem fundNormIdeal_dual (i : Fin t) :
    fundNormIdeal Q (dual Q L) (dualSplit σ Ls) i =
      (R ∙ ((σ (Fin.rev i))⁻¹ ^ 2)) * fundNormIdeal Q L Ls (Fin.rev i) := by
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  rw [fundNormIdeal_eq_of_sat Q hsatM i, fundNormIdeal_eq_of_sat Q hsat (Fin.rev i)]
  show normIdeal Q ((R ∙ (σ (Fin.rev i))⁻¹) • Ls (Fin.rev i)) = _
  rw [normIdeal_smul Q _ (fg_component Q hfg hL _), span_singleton_sq']

/-- **93:24, fundamental norm generators of $L^\#$** (O'Meara 1963, §93E, 93:24, p. 266): if $a_i$ are fundamental
norm generators of $L$, then $a_i^\# = \sigma_{t-i+1}^{-2}a_{t-i+1}$ are fundamental norm generators of $L^\#$. -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (invariants of L^#)"]
theorem isFundNormGenerators_dual {a : Fin t → F} (ha : IsFundNormGenerators Q L Ls a) :
    IsFundNormGenerators Q (dual Q L) (dualSplit σ Ls) (fun i => (σ (Fin.rev i))⁻¹ ^ 2 * a (Fin.rev i)) := by
  have hsatM := isSaturated_dual Q hS h2p hQ hL hdim hsat hσ
  have hfg : L.FG := Submodule.IsLattice.fg (A := F)
  intro i
  exact isNormGenerator_fundSub_of_sat Q hsatM i
    (IsNormGenerator.smul_lattice Q (fg_component Q hfg hL _)
      (hsat.isNormGenerator_and_weight Q hfg ha (Fin.rev i)).1 _)

/-- **93:24, the ideals $\mathfrak f_i$ of $L^\#$** (O'Meara 1963, §93E, 93:24, p. 266): $\mathfrak f_i^\# =
\mathfrak f_{t-i}$. In `fIdeal Q L Ls j i` form (first index the smaller one) this reads
`fIdeal Q (dual Q L) _ i j = fIdeal Q L Ls (Fin.rev j) (Fin.rev i)`; it holds for all pairs `i j`, in particular for
`(j : ℕ) = i + 1`, where `Fin.rev j` is `Fin.rev i - 1`. -/
@[kb "omeara1963" "§93E, 93:24, p. 266 (invariants of L^#)"]
theorem fIdeal_dual (i j : Fin t) :
    fIdeal Q (dual Q L) (dualSplit σ Ls) i j = fIdeal Q L Ls (Fin.rev j) (Fin.rev i) := by
  have hσ0 := sigma_ne_zero Q hL hσ
  unfold fIdeal
  rw [fundNormGroup_dual Q hS h2p hQ hL hdim hsat hσ i, fundNormGroup_dual Q hS h2p hQ hL hdim hsat hσ j,
    fundNormIdeal_dual Q hS h2p hQ hL hdim hsat hσ i, fundNormIdeal_dual Q hS h2p hQ hL hdim hsat hσ j,
    (isJordanSplitting_dual Q hL hσ).2 i |>.1]
  rw [fIdealOf_dual (inv_ne_zero (hσ0 _)) (inv_ne_zero (hσ0 _)), inv_inv, ← hσ]

end Invariants

end Part2

end QuadFormsKB.OMeara
