/-
# O'Meara §81D: uniqueness of the invariant factors (Theorem 81:11, second part)

**Setting** (as in `Sec81.lean`): $R$ a Dedekind domain with fraction field $F$, $V$ a vector space over $F$,
fractional ideals are non-zero finitely generated $R$-submodules of $F$.

**Index convention.** O'Meara's $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ are `t 0, …, t (n-1)`, and
"$\mathfrak t_1 \supseteq \mathfrak t_2 \supseteq \cdots$" is `Antitone t`.

**Proves** (O'Meara 1963, §81D, pp. 215–216):
* `prod_eq_of_adapted`: the product of the "invariant factors" of $J$ in $L$ computed in a base adapted to both does
  not depend on the base (O'Meara: "the reader may easily verify this by using Proposition 81:8");
* `invariant_factors_unique` (**Theorem 81:11**, uniqueness).
-/
import QuadFormsKB.Literature.OMeara.Sec81Change

open Submodule Module

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.OMeara

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

/-- Multiplying by a non-zero finitely generated submodule of `F` is cancellable. -/
theorem mul_cancel_fg_aux {p q r : Submodule R F} (hp : p.FG) (hne : p ≠ ⊥) (h : p * q = p * r) : q = r := by
  have := congrArg (fun m => (1 / p) * m) h
  simp only [← mul_assoc, mul_comm (1 / p) p, mul_one_div_cancel_of_fg hp hne, one_mul] at this
  exact this

/-- Right-cancellation of a non-zero finitely generated submodule of `F` in an inequality. -/
theorem mul_le_cancel_fg_aux {p q r : Submodule R F} (hp : p.FG) (hne : p ≠ ⊥) (h : q * p ≤ r * p) : q ≤ r := by
  calc q = q * (p * (1 / p)) := by rw [mul_one_div_cancel_of_fg hp hne, mul_one]
    _ = (q * p) * (1 / p) := by rw [mul_assoc]
    _ ≤ (r * p) * (1 / p) := mul_le_mul' h le_rfl
    _ = r := by rw [mul_assoc, mul_one_div_cancel_of_fg hp hne, mul_one]

/-- The product of two non-zero finitely generated submodules of `F` is such. -/
theorem mul_fg_ne_bot_aux {p q : Submodule R F} (hp : p.FG ∧ p ≠ ⊥) (hq : q.FG ∧ q ≠ ⊥) :
    (p * q).FG ∧ p * q ≠ ⊥ := by
  refine ⟨hp.1.mul hq.1, ?_⟩
  rw [← Submodule.zero_eq_bot] at *
  exact mul_ne_zero hp.2 hq.2

/-- Adding `c • L` to `K` in a base adapted to `L` and `K` replaces the ratio `u i` by `u i ⊔ c`. -/
theorem iSup_sup_smul_aux {ι : Type*} (x : Basis ι F V) (a u : ι → Submodule R F) (c : Submodule R F) :
    (⨆ i, (a i * u i) • span R {x i}) ⊔ c • (⨆ i, a i • span R {x i}) =
      ⨆ i, (a i * (u i ⊔ c)) • span R {x i} := by
  rw [Submodule.smul_iSup, ← iSup_sup_eq]
  congr 1
  ext1 i
  rw [Submodule.mul_sup, Submodule.sup_smul, ← Submodule.smul_assoc, smul_eq_mul, mul_comm c (a i)]

/-- **The product of the invariant factors is invariant** (O'Meara 1963, §81D, p. 216, step 4 of the proof of
81:11). If $L = \sum\mathfrak a_ix_i = \sum\mathfrak a'_ix'_i$ and $J = \sum\mathfrak a_i\mathfrak s_ix_i =
\sum\mathfrak a'_i\mathfrak s'_ix'_i$ for bases $x$, $x'$ of $V$ and fractional ideals $\mathfrak a_i, \mathfrak a'_i,
\mathfrak s_i, \mathfrak s'_i$, then $\mathfrak s_1 \cdots \mathfrak s_n = \mathfrak s'_1 \cdots \mathfrak s'_n$. (That the
$\mathfrak s_i$ are fractional ideals is not needed.) -/
@[kb "omeara1963" "§81D, p. 216 (the product of the invariant factors is invariant)"]
theorem prod_eq_of_adapted {ι : Type*} [Fintype ι] [DecidableEq ι] (x x' : Basis ι F V)
    (a a' s s' : ι → Submodule R F) (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (ha' : ∀ i, (a' i).FG ∧ a' i ≠ ⊥)
    (hs' : ∀ i, (s' i).FG ∧ s' i ≠ ⊥)
    (hL : (⨆ i, a i • span R {x i}) = ⨆ i, a' i • span R {x' i})
    (hJ : (⨆ i, (a i * s i) • span R {x i}) = ⨆ i, (a' i * s' i) • span R {x' i}) :
    ∏ i, s i = ∏ i, s' i := by
  classical
  have hm : ∀ i, (a' i * s' i).FG ∧ a' i * s' i ≠ ⊥ := fun i => mul_fg_ne_bot_aux (ha' i) (hs' i)
  have h1 := (eq_iff_prod_of_adapted x x' a a' ha' hL.ge).mp hL.symm
  have h2 := (eq_iff_prod_of_adapted x x' (fun i => a i * s i) (fun i => a' i * s' i) hm hJ.ge).mp hJ.symm
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at h2
  obtain ⟨hPf, hPn⟩ := prod_fg_ne_bot Finset.univ a ha
  refine mul_cancel_fg_aux hPf hPn ?_
  calc (∏ i, a i) * ∏ i, s i = (∏ i, a' i) * (∏ i, s' i) * span R {(x.toMatrix x').det} := h2
    _ = ((∏ i, a' i) * span R {(x.toMatrix x').det}) * ∏ i, s' i := by ring
    _ = (∏ i, a i) * ∏ i, s' i := by rw [h1]

/-- Key step: if the factors agree below `i`, then `t i ≤ t' i`. -/
theorem unique_aux {n : ℕ} (x x' : Basis (Fin n) F V) (a a' t t' : Fin n → Submodule R F)
    (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (ha' : ∀ i, (a' i).FG ∧ a' i ≠ ⊥)
    (ht : ∀ i, (t i).FG ∧ t i ≠ ⊥) (ht' : ∀ i, (t' i).FG ∧ t' i ≠ ⊥) (hta' : Antitone t')
    (hL : (⨆ i, a i • span R {x i}) = ⨆ i, a' i • span R {x' i})
    (hK : (⨆ i, (a i * t i) • span R {x i}) = ⨆ i, (a' i * t' i) • span R {x' i})
    (i : Fin n) (hprev : ∀ j < i, t j = t' j) : t i ≤ t' i := by
  by_contra hlt
  have hs1 : ∀ j, (t j ⊔ t' i).FG ∧ t j ⊔ t' i ≠ ⊥ := fun j =>
    ⟨(ht j).1.sup (ht' i).1, fun h => (ht j).2 (eq_bot_iff.mpr (le_sup_left.trans h.le))⟩
  have hs2 : ∀ j, (t' j ⊔ t' i).FG ∧ t' j ⊔ t' i ≠ ⊥ := fun j =>
    ⟨(ht' j).1.sup (ht' i).1, fun h => (ht' j).2 (eq_bot_iff.mpr (le_sup_left.trans h.le))⟩
  have hJ : (⨆ j, (a j * (t j ⊔ t' i)) • span R {x j}) = ⨆ j, (a' j * (t' j ⊔ t' i)) • span R {x' j} := by
    rw [← iSup_sup_smul_aux x a t (t' i), ← iSup_sup_smul_aux x' a' t' (t' i), hK, hL]
  have hs : ∏ j, (t j ⊔ t' i) = ∏ j, (t' j ⊔ t' i) :=
    prod_eq_of_adapted x x' a a' _ _ ha ha' hs2 hL hJ
  have hle : ∀ j, t' j ⊔ t' i ≤ t j ⊔ t' i := by
    intro j
    by_cases hj : j < i
    · rw [hprev j hj]
    · exact (sup_le (hta' (not_lt.mp hj)) le_rfl).trans le_sup_right
  have e1 := Finset.mul_prod_erase Finset.univ (fun j => t j ⊔ t' i) (Finset.mem_univ i)
  have e2 := Finset.mul_prod_erase Finset.univ (fun j => t' j ⊔ t' i) (Finset.mem_univ i)
  obtain ⟨hPf, hPn⟩ := prod_fg_ne_bot (Finset.univ.erase i) (fun j => t j ⊔ t' i) hs1
  have hle2 : ∏ j ∈ Finset.univ.erase i, (t' j ⊔ t' i) ≤ ∏ j ∈ Finset.univ.erase i, (t j ⊔ t' i) :=
    prod_le_prod_submodule _ _ _ hle
  have hfin : (t i ⊔ t' i) * ∏ j ∈ Finset.univ.erase i, (t j ⊔ t' i) ≤
      (t' i ⊔ t' i) * ∏ j ∈ Finset.univ.erase i, (t j ⊔ t' i) := by
    calc (t i ⊔ t' i) * ∏ j ∈ Finset.univ.erase i, (t j ⊔ t' i) = ∏ j, (t j ⊔ t' i) := e1
      _ = ∏ j, (t' j ⊔ t' i) := hs
      _ = (t' i ⊔ t' i) * ∏ j ∈ Finset.univ.erase i, (t' j ⊔ t' i) := e2.symm
      _ ≤ _ := mul_le_mul' le_rfl hle2
  have := mul_le_cancel_fg_aux hPf hPn (by simpa only [mul_comm _ (∏ j ∈ Finset.univ.erase i, (t j ⊔ t' i))] using hfin)
  exact hlt (le_sup_left.trans (this.trans (by simp)))

/-- **Theorem 81:11, uniqueness** (O'Meara 1963, pp. 215–216). If $L = \sum_i\mathfrak a_ix_i = \sum_i\mathfrak a'_ix'_i$
and $K = \sum_i\mathfrak a_i\mathfrak t_ix_i = \sum_i\mathfrak a'_i\mathfrak t'_ix'_i$ for bases $x$, $x'$ of $V$ and
fractional ideals with $\mathfrak t_1 \supseteq \cdots \supseteq \mathfrak t_n$ and
$\mathfrak t'_1 \supseteq \cdots \supseteq \mathfrak t'_n$, then $\mathfrak t_i = \mathfrak t'_i$ for all $i$. -/
@[kb "omeara1963" "§81D, 81:11, pp. 215–216 (uniqueness of the invariant factors)"]
theorem invariant_factors_unique {n : ℕ} (x x' : Basis (Fin n) F V) (a a' t t' : Fin n → Submodule R F)
    (ha : ∀ i, (a i).FG ∧ a i ≠ ⊥) (ha' : ∀ i, (a' i).FG ∧ a' i ≠ ⊥)
    (ht : ∀ i, (t i).FG ∧ t i ≠ ⊥) (ht' : ∀ i, (t' i).FG ∧ t' i ≠ ⊥) (hta : Antitone t) (hta' : Antitone t')
    (hL : (⨆ i, a i • span R {x i}) = ⨆ i, a' i • span R {x' i})
    (hK : (⨆ i, (a i * t i) • span R {x i}) = ⨆ i, (a' i * t' i) • span R {x' i}) :
    t = t' := by
  funext i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    exact le_antisymm (unique_aux x x' a a' t t' ha ha' ht ht' hta' hL hK i ih)
      (unique_aux x' x a' a t' t ha' ha ht' ht hta hL.symm hK.symm i fun j hj => (ih j hj).symm)

end QuadFormsKB.OMeara
