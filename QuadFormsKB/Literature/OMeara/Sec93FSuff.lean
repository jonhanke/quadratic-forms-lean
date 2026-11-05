/-
# O'Meara 93:28, proof of the sufficiency

**Setting** (as in `Sec93E.lean`).

**Proves** (O'Meara 1963, §93F, proof of 93:28, sufficiency, pp. 272–276)
* `suff_base` (step 1, the case $s_t = s_1$): two $\mathfrak s$-modular lattices on $V$ with the same norm group are
  isometric (93:16 after scaling).
-/
import QuadFormsKB.Literature.OMeara.Sec93FNecII

open QuadraticMap Submodule Module IsLocalRing
open scoped Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara.Suff28

section Base

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
variable (Q : QuadraticForm F V)

/-- **93:28, sufficiency, step 1, the case $s_t = s_1$** (O'Meara 1963, p. 272): "Then $L$ and $K$ are modular of the
same scale. And $\mathfrak gL = \mathfrak gK$ since $L$ and $K$ have the same fundamental invariants. Hence
$\operatorname{cls}L = \operatorname{cls}K$ by Theorem 93:16." -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, step 1, p. 272 (the case s_t = s_1)"]
theorem suff_base {L K : Submodule R V} [L.IsLattice F] [K.IsLattice F] {σ : F} (hσ : σ ≠ 0)
    (hL : IsModular Q (R ∙ σ) L) (hK : IsModular Q (R ∙ σ) K) (hg : normGroup Q L = normGroup Q K) :
    cls Q L = cls Q K := by
  have hLfg : L.FG := Submodule.IsLattice.fg (A := F)
  have hKfg : K.FG := Submodule.IsLattice.fg (A := F)
  set Q' : QuadraticForm F V := σ⁻¹ • Q with hQ'
  have hL' := isUnimodular_smul_of_isModular Q hσ hLfg hL
  have hK' := isUnimodular_smul_of_isModular Q hσ hKfg hK
  have hg' : normGroup Q' L = normGroup Q' K := by rw [hQ', normGroup_smul_form, normGroup_smul_form, hg]
  obtain ⟨f, hf⟩ := isometricLat_of_normGroup_eq Q' hL' hK' hg'
  have hiso : IsometricLat Q Q L K := ⟨f, fun x => by
    have := hf x
    simp only [hQ', smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (inv_ne_zero hσ) this⟩
  exact (cls_eq_of_mem Q (mem_cls_of_isometricLat Q hiso)).symm

end Base

section Defs

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] [Invertible (2 : F)]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable (Q : QuadraticForm F V)

/-- **The conditions (i)–(iii) of 93:28** (O'Meara 1963, §93F, p. 268) for Jordan splittings `Ls` of $L$ and `Ks` of
$K$ with fundamental norm generators `a`: for consecutive indices $i$, $j = i+1$ ($0$-based),
(i) $dL_{(i)}/dK_{(i)} \cong 1 \bmod \mathfrak f_i$; (ii) $FL_{(i)} \to FK_{(i)} \perp \langle a_{i+1}\rangle$ when
$\mathfrak f_i \subsetneq 4a_{i+1}\mathfrak w_{i+1}^{-1}$; (iii) $FL_{(i)} \to FK_{(i)} \perp \langle a_i\rangle$ when
$\mathfrak f_i \subsetneq 4a_i\mathfrak w_i^{-1}$. This is the right-hand side of `DyadicClassification`. -/
def Cond93 (L : Submodule R V) {t : ℕ} (Ls Ks : Fin t → Submodule R V) (a : Fin t → F) : Prop :=
  ∀ i j : Fin t, (j : ℕ) = i + 1 →
    DiscQuotSqEquivMod Q (jordanChain Ls i) (jordanChain Ks i) (fIdeal Q L Ls i j) ∧
    (fIdeal Q L Ls i j < (4 * a j) • (1 / fundWeight Q L Ls j) →
      SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a j)) ∧
    (fIdeal Q L Ls i j < (4 * a i) • (1 / fundWeight Q L Ls i) →
      SpanRepresents Q (jordanChain Ls i) (jordanChain Ks i) (a i))

end Defs

section Core

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
  [Finite (ResidueField R)] (F : Type u) [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
  [Invertible (2 : F)]

/-- **The computational core of the sufficiency in 93:28** (O'Meara 1963, §93F, proof of the sufficiency, steps 3–8,
pp. 273–276), *named statement*: in the situation reached by the reductions of step 2 — both Jordan splittings
saturated, all fundamental dimensions $\ge 3$, every space $FL_k$ hyperbolic (a totally isotropic subspace of half
the dimension), $L_1$ and $K_1$ unimodular, the same fundamental invariants and conditions (i)–(iii) — $K$ has a new
saturated Jordan splitting $K = K_1' \perp \cdots \perp K_t'$ with $K_1' \cong L_1$ for which (i)–(iii) still hold.
O'Meara: "This shows that we will be through once we obtain a new saturated Jordan splitting
$K = K_1 \perp \cdots \perp K_t$ in which $L_1 \cong K_1$" (p. 273); steps 4–8 obtain it. The rest of the sufficiency
(step 1, the induction on $s_t - s_1$; step 2, the reductions; step 3, the passage to $L^*_{(2)}$, $K^*_{(2)}$) is
proved from this statement. -/
@[kb "omeara1963" "§93F, proof of 93:28, sufficiency, steps 3–8, pp. 273–276"]
structure SuffCore : Prop where
  core : ∀ {V : Type v} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), ¬ IsUnit (2 : R) → (QuadraticMap.associated Q).Nondegenerate →
    ∀ (L K : Submodule R V) [L.IsLattice F] [K.IsLattice F] (m : ℕ) (Ls Ks : Fin (m + 2) → Submodule R V)
      (a : Fin (m + 2) → F), IsSaturated Q L Ls → IsSaturated Q K Ks → (∀ k, 3 ≤ finrank R (Ls k)) →
      (∀ k, ∃ T : Submodule F V, (∀ x ∈ T, Q x = 0) ∧ (∀ x ∈ T, x ∈ span F (Ls k : Set V)) ∧
        finrank R (Ls k) ≤ 2 * finrank F T) →
      scale Q (Ls 0) = 1 → SameFundamentalInvariants Q Q L K Ls Ks a → Cond93 Q L Ls Ks a →
      ∃ Ks' : Fin (m + 2) → Submodule R V, IsSaturated Q K Ks' ∧ IsometricLat Q Q (Ls 0) (Ks' 0) ∧
        Cond93 Q L Ls Ks' a

end Core

end QuadFormsKB.OMeara.Suff28
