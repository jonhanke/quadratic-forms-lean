import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.LocalDensity.Explicit

/-!
# Local densities are invariant under multiplying $m$ by the square of a $p$-adic unit

For a prime $p$, an integer $u$ with $p \nmid u$, and any integral form $Q$:
$\beta_p(Q; u^2 m) = \beta_p(Q; m)$, since $\vec x \mapsto u\vec x$ is a bijection of
$(\mathbb{Z}/p^k)^n$ with $Q(u \vec x) = u^2 Q(\vec x)$. Used in the proof of Berkovich–Hanke–Jagy,
Theorem 6.1 (bib key `berkovich2012`), to compare $\beta_p(m)$ and $\beta_p(m/W^2)$.
-/

namespace QuadFormsKB.Berkovich2012

open QuadFormsKB QuadFormsKB.LocalDensity

lemma isUnit_intCast_zmod_pow (p : ℕ) [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (k : ℕ) :
    IsUnit ((u : ZMod (p ^ k))) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact isUnit_of_subsingleton _
  have hn : ¬ p ∣ u.natAbs := fun h => hu (Int.ofNat_dvd_left.2 h)
  have h := (ZMod.isUnit_natCast_iff_not_dvd_pow (a := u.natAbs) (Fact.out : p.Prime) hk).2 hn
  rcases Int.natAbs_eq u with e | e
  · rw [e, Int.cast_natCast]; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast]; exact h.neg

/-- $r_{p^k}(u^2 m) = r_{p^k}(m)$ for $p \nmid u$. -/
theorem repCount_unit_sq_mul {n : ℕ} (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] {u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (k : ℕ) (m : ℤ) : repCount Q p k (u ^ 2 * m) = repCount Q p k m := by
  set V := (isUnit_intCast_zmod_pow p hu k).unit
  have hV : (V : ZMod (p ^ k)) = u := IsUnit.unit_spec _
  unfold repCount
  refine Nat.card_congr
    { toFun := fun x => ⟨fun j => (V⁻¹ : (ZMod (p ^ k))ˣ) * x.1 j, ?_⟩
      invFun := fun y => ⟨fun j => (V : ZMod (p ^ k)) * y.1 j, ?_⟩
      left_inv := fun x => by ext1; funext j; simp [← mul_assoc]
      right_inv := fun y => by ext1; funext j; simp [← mul_assoc] }
  · rw [evalIn_const_mul, x.2]
    push_cast
    rw [← hV, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  · rw [evalIn_const_mul, y.2, hV]; push_cast; ring

/-- **$\beta_p(Q; u^2 m) = \beta_p(Q; m)$** for a prime $p$ and $p \nmid u$. -/
theorem localDensity_unit_sq_mul {n : ℕ} (Q : QuadForm ℤ n) (p : ℕ) [Fact p.Prime] {u : ℤ}
    (hu : ¬ (p : ℤ) ∣ u) (m : ℤ) : localDensity Q p (u ^ 2 * m) = localDensity Q p m := by
  unfold localDensity
  simp only [repCount_unit_sq_mul Q p hu]

end QuadFormsKB.Berkovich2012
