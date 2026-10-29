/-
# Kneser connectivity on the nose

**Layer:** integral forms `QuadForm ℤ n`, the $p$-neighbour graph on forms (`Siegel/KneserClosure.lean`).

**Proves**
- `exists_isotropic_of_three_le`: a quadratic form in $n \ge 3$ variables over a finite field has a nonzero zero
  (Chevalley–Warning);
- `exists_isNbrForm_symm`: if $p \nmid 2\det H$ (and $n \ge 3$), $Q$ has a $p$-neighbour form $Q_1$, and $Q$ is in turn a
  $p$-neighbour form of $Q_1$ (symmetry of the neighbour relation, `isNeighbor_inv`);
- **`kneserConnected_of_spinorGenus`**: under the hypotheses of `exists_nbrReach_intEquiv`, `KneserConnected p Q`: every form of the genus
  is reachable from $Q$ itself, not only up to equivalence. If the reaching chain of `exists_nbrReach_intEquiv` is empty
  ($Q \cong Q'$), one goes out to a neighbour and back.
-/
import QuadFormsKB.Siegel.KneserBridge
import QuadFormsKB.Siegel.EichlerGenus
import Mathlib.FieldTheory.ChevalleyWarning

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Siegel.Kneser

open QuadFormsKB.Siegel QuadFormsKB.Tamagawa.RatBridge QuadFormsKB.Lattices QuadFormsKB.HilbertModular

variable {n : ℕ}

/-- **A form in $n \ge 3$ variables over a finite field is isotropic** (Chevalley–Warning): there is $\vec{z} \ne 0$ with
$S(\vec{z}) = 0$. -/
theorem exists_isotropic_of_three_le {K : Type*} [Field K] [Finite K] (hn : 3 ≤ n) (S : QuadForm K n) :
    ∃ z : Fin n → K, z ≠ 0 ∧ S.eval z = 0 := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial (Fin n) K, f = ∑ i, ∑ j, if i ≤ j then
      MvPolynomial.C (S.coeff i j) * MvPolynomial.X i * MvPolynomial.X j else 0 := ⟨_, rfl⟩
  have hev : ∀ z, MvPolynomial.eval z f = S.eval z := by
    intro z
    simp only [hf, map_sum, QuadForm.eval, QuadForm.evalIn, Algebra.algebraMap_self, RingHom.id_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hterm : ∀ (c : K) (i j : Fin n),
      (MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin n) K).totalDegree ≤ 2 := by
    intro c i j
    calc _ ≤ (MvPolynomial.C c * MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree +
          (MvPolynomial.X j : MvPolynomial (Fin n) K).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C c : MvPolynomial (Fin n) K).totalDegree +
          (MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree) +
          (MvPolynomial.X j : MvPolynomial (Fin n) K).totalDegree :=
            Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ = 2 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  have hdeg : f.totalDegree < Fintype.card (Fin n) := by
    rw [Fintype.card_fin, hf]
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
    refine lt_of_le_of_lt (Finset.sup_le fun i _ => ?_ : _ ≤ 2) (by omega)
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun j _ => ?_)
    split_ifs
    · exact hterm _ _ _
    · simp
  set p := ringChar K with hp
  have hdvd := char_dvd_card_solutions (K := K) p hdeg
  have hp2 : 2 ≤ p := (CharP.char_is_prime K p).two_le
  by_contra hne
  push Not at hne
  have hsub : ∀ z : {z : Fin n → K // MvPolynomial.eval z f = 0}, z = ⟨0, by rw [hev]; simp [QuadForm.eval,
      QuadForm.evalIn]⟩ := by
    intro z
    apply Subtype.ext
    by_contra h
    exact hne z.1 h (by rw [← hev]; exact z.2)
  have h1 : Fintype.card {z : Fin n → K // MvPolynomial.eval z f = 0} = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨_, hsub⟩
  rw [h1] at hdvd
  have := Nat.le_of_dvd one_pos hdvd
  omega

/-- **A $p$-neighbour form and the way back:** for $n \ge 3$, $p$ an odd prime with $p \nmid \det H$, there is $Q_1$ with
$Q_1$ a $p$-neighbour form of $Q$ and $Q$ a $p$-neighbour form of $Q_1$. -/
theorem exists_isNbrForm_symm (hn : 3 ≤ n) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Q : QuadForm ℤ n}
    (hdet : ¬ (p : ℤ) ∣ Q.hessian.det) : ∃ Q₁ : QuadForm ℤ n, IsNbrForm p Q Q₁ ∧ IsNbrForm p Q₁ Q := by
  obtain ⟨z, hz0, hz⟩ := exists_isotropic_of_three_le hn (Q.map (Int.castRingHom (ZMod p)))
  have hmem : z ∈ isoSet Q p := by
    rw [mem_isoSet]
    refine ⟨hz0, ?_⟩
    rw [← hz]
    simp [qv, QuadForm.eval, QuadForm.evalIn, QuadForm.map]
  have hL : nbOf Q p z ∈ neighbors Q p := Finset.mem_image_of_mem _ hmem
  obtain ⟨g, hg, hLg, Q₁, hQ₁, -⟩ := exists_gram_of_mem_neighbors hp2 hdet hL
  have hnb : IsNeighbor Q p (imgLat g) := hLg ▸ (mem_neighbors_iff hdet).mp hL
  refine ⟨Q₁, ⟨g, hg, hnb, hQ₁⟩, ?_⟩
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hg)
  set G : GL (Fin n) ℚ := hu.unit
  have hG : (G : Matrix (Fin n) (Fin n) ℚ) = g := rfl
  have hinv := isNeighbor_inv (Q := Q) (Q' := Q₁) (g := G) (by rw [hG]; exact hnb) (by rw [hG]; exact hQ₁)
  refine ⟨((G⁻¹ : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ), (Matrix.isUnits_det_units G⁻¹).ne_zero, hinv, fun x => ?_⟩
  rw [hQ₁, hG.symm, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

/-- **Kneser's theorem with connectivity on the nose** (Kneser 1957, Satz 2 [unverified]). Let $Q$ be a positive definite integral form in
$n \ge 3$ variables, $p$ an odd prime with $p \nmid \det H$ (`hdet`), and assume the genus of $\mathbb Z^n$ in $(\mathbb Q^n, Q)$ is a
single spinor genus (`hgs`; a condition on $Q$, not an input). Then every form $Q'$ in the genus of $Q$ is reachable from $Q$
itself in the $p$-neighbour graph: `KneserConnected p Q`. Unconditional; the only hypotheses are those named here. This
upgrades `exists_nbrReach_intEquiv` (reachability up to $\mathrm{GL}_n(\mathbb Z)$-equivalence): if the chain there is
empty, $Q \cong Q'$, and one goes to a $p$-neighbour and back (`exists_isNbrForm_symm`). -/
@[kb "kneser1957" "Satz 2 [unverified]; Kneser connectivity on the nose"]
theorem kneserConnected_of_spinorGenus (Q : QuadForm ℤ n) (hQ : IntQF.PosDef Q) (hn : 3 ≤ n) (p : ℕ)
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ Q.hessian.det)
    (hgs : ∀ M : Lat ℚ n, Lattices.SameGenus (formF (up Q)) intVec M.1 →
      SameSpinorGenus (formF (up Q)) (HilbertModular.stdLat (F := ℚ)) M) :
    KneserConnected p Q := by
  intro Q' hg
  obtain ⟨Q'', hr, he⟩ := Bridge.exists_nbrReach_intEquiv Q hQ hn p hp2 hdet hgs hg
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨b, hb, Q₁, h1, h2⟩
  · subst Q''
    obtain ⟨Q₁, hf, hb⟩ := exists_isNbrForm_symm hn hp2 hdet (Q := Q)
    exact (Relation.ReflTransGen.single ⟨Q₁, hf, IsometricGL.refl _⟩).tail ⟨Q, hb, he⟩
  · exact hb.tail ⟨Q₁, h1, IsometricGL.trans h2 he⟩

end QuadFormsKB.Siegel.Kneser
