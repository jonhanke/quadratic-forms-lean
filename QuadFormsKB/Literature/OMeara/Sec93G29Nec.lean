/-
# O'Meara 93:29 over a 2-adic field: the corrected statement and its necessity

**Setting** (as in `Sec93G.lean`): $R$ a Henselian discrete valuation ring with finite residue field and fraction field
$F$, $2$ a prime element of $R$ (`IsTwoAdic R`), $V$ a regular quadratic space.

**Reading of the printed statement** (O'Meara 1963, §93G, 93:29, p. 277, PDF p. 285). Condition (ii) is printed
"$FL_{(i)} \to FK_{(i)} \perp \langle 2^{u_i}\rangle$ when $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$" with the
*non-strict* inclusion glyph (the same glyph as in "$2(\mathfrak sL) \subseteq \mathfrak mL \subseteq \mathfrak nL$"
on the same page; the strict inclusions of the text are written $\subset$, e.g. "$\mathfrak f_i \subset 4\mathfrak
n_i\mathfrak w_i^{-1}$"). `TwoAdicClassification` in `Sec93G.lean` reads it as the strict $\subsetneq$. With the strict reading the
"if" direction is not the book's theorem: for $\mathfrak n_1 = \mathfrak o$, $\mathfrak n_2 = 4\mathfrak o$
(so $\mathfrak n_2 = 4\mathfrak n_1$) condition (ii) is then vacuous while it is needed (O'Meara p. 278: "But
$\mathfrak n_2 = 4\mathfrak o \subseteq 4\mathfrak n_1$, hence $FL_1 \perp \langle\varepsilon\rangle \cong FK_1 \perp \langle 1\rangle$";
without it $K_1 \cong A(1,0) \perp A(2, 2\rho)$ is not excluded, see `CoreTwoLast.no_rep_aniso`).

**Defines**
* `Cond29`: conditions (i), (ii) of 93:29 (non-strict reading), for the Jordan chains of two splittings;
* `TwoAdicClassificationLe`: the statement of 93:29 with the non-strict reading.

**Proves** (O'Meara 1963, §93G, proof of 93:29, step 1, p. 277)
* `fIdeal_lt_four_mul_of_normIdeal_le`: $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i \Rightarrow \mathfrak f_i \subsetneq
  4\mathfrak n_i\mathfrak w_i^{-1}$;
* `cond29_of_cls_eq`: necessity, from 93:28 (`DyadicClassification`).
-/
import QuadFormsKB.Literature.OMeara.Sec93GNec
import QuadFormsKB.Literature.OMeara.Sec93FCoreTwoLast

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

section Defs

variable {R : Type*} [CommRing R] {F : Type*} [Field F] [Algebra R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **Conditions (i), (ii) of 93:29** (O'Meara 1963, §93G, p. 277, non-strict reading of (ii)) for the Jordan chains of
splittings `Ls`, `Ks` ($0$-based, `j = i + 1`): (i) $dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak n_i\mathfrak n_{i+1}/\mathfrak
s_i^2$; (ii) $FL_{(i)} \to FK_{(i)} \perp \langle 2^u\rangle$ when $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$, for the
$u$ with $2^u\mathfrak o = \mathfrak n_i$. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (conditions (i), (ii))"]
def Cond29 {t : ℕ} (Ls Ks : Fin t → Submodule R V) : Prop :=
  ∀ i j : Fin t, (j : ℕ) = i + 1 →
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i)
      (normIdeal Q (Ls i) * normIdeal Q (Ls j) / (scale Q (Ls i) * scale Q (Ls i))) ∧
    (normIdeal Q (Ls j) ≤ (4 : F) • normIdeal Q (Ls i) → ∀ u : ℤ, R ∙ ((2 : F) ^ u) = normIdeal Q (Ls i) →
      SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) ((2 : F) ^ u))

end Defs

section Classification

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **Theorem 93:29 with the non-strict reading of (ii)** (O'Meara 1963, §93G, p. 277): as `TwoAdicClassification`, with
condition (ii) required when $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$. See the file header for the reading. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (non-strict reading of (ii))"]
structure TwoAdicClassificationLe : Prop where
  cls_eq_iff : IsTwoAdic R → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] {t : ℕ} (Ls Ks : Fin t → Submodule R V),
      IsJordanSplitting Q L Ls → IsJordanSplitting Q K Ks → SameJordanInvariants Q Q Ls Ks →
      (cls Q L = cls Q K ↔ Cond29 Q Ls Ks)

end Classification

section Necessity

open Nec93

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **$\mathfrak n_{i+1} \subseteq 4\mathfrak n_i \Rightarrow \mathfrak f_i \subsetneq 4\mathfrak n_i\mathfrak w_i^{-1}$**
(O'Meara 1963, §93G, proof of 93:29, step 1, p. 277: "We find that $\mathfrak n_{i+1} \subseteq 4\mathfrak n_i$ implies
$\mathfrak f_i \subset 4\mathfrak n_i\mathfrak w_i^{-1}$"). The non-strict version of
`fIdeal_lt_four_mul_of_normIdeal_lt`. -/
@[kb "omeara1963" "§93G, proof of 93:29, p. 277 (n_{i+1} ⊆ 4n_i ⇒ f_i ⊂ 4 n_i w_i⁻¹)"]
theorem fIdeal_lt_four_mul_of_normIdeal_le (h2 : IsTwoAdic R) {L : Submodule R V} (hfg : L.FG)
    (hreg : IsRegular Q L) {t : ℕ} {Ls : Fin t → Submodule R V} (hL : IsJordanSplitting Q L Ls)
    (i j : Fin t) (hij : (j : ℕ) = i + 1) {a : F} (ha : R ∙ a = normIdeal Q (Ls i))
    (hle : normIdeal Q (Ls j) ≤ (4 : F) • normIdeal Q (Ls i)) :
    fIdeal Q L Ls i j < (4 * a) • (1 / fundWeight Q L Ls i) := by
  obtain ⟨u, σ, τ, k, hu, hσ0, hτ0, hσ, hτ, hk, p1, p2, q1, q2, hs, hcase⟩ :=
    exists_data Q h2 hfg hreg hL hij
  have hπ := twoAdic_irreducible h2
  have h2F : (2 : F) ≠ 0 := two_ne_zero' F
  have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
  have huj : u i + 2 ≤ u j := by
    have h1 : (2 : F) ^ (u j) ∈ (4 : F) • normIdeal Q (Ls i) :=
      hle (by rw [← hu j]; exact mem_span_singleton_self _)
    rw [← hu i, FIdealAux.smul_span_singleton, four_mul_two_zpow, mem_span_two_zpow_iff h2 (z2 _),
      dord_two_zpow h2] at h1
    exact h1
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
    rcases hcase with ⟨ho, hk'⟩ | ⟨he, hk'⟩
    · obtain ⟨m, hm'⟩ := ho
      omega
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

/-- **93:29, necessity, from 93:28** (O'Meara 1963, §93G, proof of 93:29, step 1, p. 277): equal classes give
`Cond29` (non-strict reading of (ii)); see `cls_eq_imp_of_dyadicClassification` for the proof outline. -/
@[kb "omeara1963" "§93G, 93:29, p. 277 (necessity, from 93:28, non-strict reading)"]
theorem cond29_of_cls_eq (h : DyadicClassification R Q) (h2 : IsTwoAdic R)
    (hQ : (QuadraticMap.associated Q).Nondegenerate)
    (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] {t : ℕ} (Ls Ks : Fin t → Submodule R V)
    (hL : IsJordanSplitting Q L Ls) (hK : IsJordanSplitting Q K Ks)
    (hJ : SameJordanInvariants Q Q Ls Ks) (hcls : cls Q L = cls Q K) : Cond29 Q Ls Ks := by
  intro i j hij
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
  · intro hle u0 hu0
    have z2 : ∀ w : ℤ, (2 : F) ^ w ≠ 0 := fun w => two_zpow_ne_zero w
    have hui : u0 = u i := by
      have := (FIdealAux.span_eq_iff_dord hπ (z2 u0) (z2 (u i))).1 (hu0.trans (hu i).symm)
      rwa [dord_two_zpow h2, dord_two_zpow h2] at this
    rw [hui]
    exact k3 (fIdeal_lt_four_mul_of_normIdeal_le Q h2 hfgL hregL hL i j hij (a := (2 : F) ^ u i) (hu i) hle)

end Necessity

end QuadFormsKB.OMeara
