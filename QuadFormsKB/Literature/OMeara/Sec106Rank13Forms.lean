/-
# O'Meara §106F, toward 106.r38: the genus of $I_n$ for $n \le 13$, on the side of integral forms

**Layer:** integral forms `QuadForm ℤ n` given by Gram matrices (`LocalDensity.ofMatrixZ A`, $x \mapsto x^{\mathsf T}Ax$),
$\mathrm{GL}_n(\mathbb Z)$-classes, the genus `Siegel.SameGenus`, the mass `Siegel.mass`
$= \sum_{[Q'] \in \mathrm{Gen}} 1/|\mathrm{Aut}(Q')|$. $I_n$ is `Siegel.sumSq n`, $A \oplus I_k$ is `ConwaySloane.Mass.sumI A k`.
Indices are 0-based.

**Proves** (all unconditional)
* `sumSq_eq_ofMatrixZ_one`: $I_n$ is the form with Gram matrix $1$.
* `sameGenus_sumSq_of_det_one`: a positive definite odd Gram matrix of determinant $1$ is in the genus of $I_n$
  (Conway–Sloane 1988, §11, Lemma 2, `ConwaySloane.Mass.lemma2`, with trivial discriminant groups).
* `repNum_sumI_one`: if $A$ is positive definite with no vector of norm $1$, then $A \oplus I_k$ has exactly $2k$ vectors of
  norm $1$.
* `mass_sumSq_nine`, …, `mass_sumSq_thirteen`: the masses of the genus of $I_n$ for $9 \le n \le 13$, from the
  Conway–Sloane mass formula (`ConwaySloane.Mass.mass_eq_stdMass_mul_symbols_unconditional`) with the $2$-adic symbol
  $1^{+n}_{n}$ of $I_n$.
-/
import QuadFormsKB.Literature.ConwaySloane.Mass.GenusLemmasHold
import QuadFormsKB.Literature.ConwaySloane.Mass.VineLattices
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicFinal
import QuadFormsKB.Literature.ConwaySloane.Mass.TwoAdicSymbol
import QuadFormsKB.Literature.ConwaySloane.Mass.Table6
import QuadFormsKB.Siegel.KneserMass
import QuadFormsKB.Siegel.FourSquaresJacobi
import QuadFormsKB.Siegel.EvenUnimodularRank
import QuadFormsKB.Literature.Cassels.AppB.SumSquaresGenus

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Lattices

open Siegel LocalDensity ConwaySloane ConwaySloane.Mass

variable {n : ℕ}

/-- $I_n$ is the integral form with Gram matrix $1$. -/
theorem sumSq_eq_ofMatrixZ_one (n : ℕ) : sumSq n = ofMatrixZ (1 : Matrix (Fin n) (Fin n) ℤ) := by
  ext i j
  simp only [sumSq, QuadForm.diag, ofMatrixZ, Matrix.of_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rcases lt_or_gt_of_ne h with h' | h'
    · simp [h, h', Ne.symm h]
    · simp [h, not_lt.mpr h'.le]

/-- A Gram matrix of determinant $1$ has trivial discriminant group. -/
theorem subsingleton_discGroup_of_det_one {A : Matrix (Fin n) (Fin n) ℤ} (hA : A.det = 1) :
    Subsingleton (DiscGroup A) := by
  have h := card_discGroup (A := A) (by rw [hA]; norm_num)
  rw [hA] at h
  exact (Nat.card_eq_one_iff_unique.mp h).1

/-- **Discriminant forms of determinant-one lattices are isomorphic**, preserving norms mod $1$. -/
theorem discIso_one_of_det_one {A B : Matrix (Fin n) (Fin n) ℤ} (hsA : Aᵀ = A) (hsB : Bᵀ = B)
    (hA : A.det = 1) (hB : B.det = 1) : DiscIso 1 A B := by
  haveI := subsingleton_discGroup_of_det_one hA
  haveI := subsingleton_discGroup_of_det_one hB
  let φ : DiscGroup A ≃+ DiscGroup B :=
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim _ _ }
  refine ⟨φ, fun y z _ => ?_⟩
  have hdA : A.det ≠ 0 := by rw [hA]; norm_num
  have hdB : B.det ≠ 0 := by rw [hB]; norm_num
  obtain ⟨a, ha⟩ := dualNorm_congr_one hsA hdA (y := 0) (y' := y) (Subsingleton.elim _ _)
  obtain ⟨b, hb⟩ := dualNorm_congr_one hsB hdB (y := 0) (y' := z) (Subsingleton.elim _ _)
  have h0 : ∀ C : Matrix (Fin n) (Fin n) ℤ, dualNorm C 0 = 0 := fun C => by simp [dualNorm]
  rw [h0] at ha hb
  exact ⟨b - a, by rw [ha, hb]; push_cast; ring⟩

/-- The type of $1 \in M_n(\mathbb Z)$ ($n \ge 1$) is $1$ (odd). -/
theorem gramType_one (hn : 1 ≤ n) : gramType (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
  unfold gramType
  rw [if_neg]
  intro h
  have := h ⟨0, hn⟩
  simp at this

/-- A Gram matrix with an odd diagonal entry has type $1$. -/
theorem gramType_eq_one_of_odd {A : Matrix (Fin n) (Fin n) ℤ} (i : Fin n) (hi : Odd (A i i)) : gramType A = 1 := by
  unfold gramType
  rw [if_neg]
  intro h
  exact (Int.not_even_iff_odd.mpr hi) (h i)

/-- **A positive definite odd Gram matrix of determinant $1$ is in the genus of $I_n$** (Conway–Sloane 1988, §11,
Lemma 2: same type, trivial discriminant groups). -/
theorem sameGenus_sumSq_of_det_one (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℤ} (hA : PosDefGram A)
    (hdet : A.det = 1) (hodd : gramType A = 1) : Siegel.SameGenus (sumSq n) (ofMatrixZ A) := by
  rw [sumSq_eq_ofMatrixZ_one]
  have h1 : PosDefGram (1 : Matrix (Fin n) (Fin n) ℤ) := by
    refine ⟨by simp, fun x hx => ?_⟩
    have : gramQ (1 : Matrix (Fin n) (Fin n) ℤ) = 1 := by
      ext i j; simp [gramQ, Matrix.one_apply]
    rw [this, Matrix.one_mulVec]
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Ne.symm fun h => hx (dotProduct_self_eq_zero.mp h))
  refine sameGenus_of_discIso h1 hA (by rw [gramType_one hn, hodd]) ?_
  rw [gramType_one hn]
  exact discIso_one_of_det_one (by simp) hA.1 (by simp) hdet

/-- **$A \oplus I_k$ has exactly $2k$ vectors of norm $1$** when $A$ is positive definite with no vector of norm $1$. -/
theorem repNum_sumI_one {m : ℕ} {A : Matrix (Fin m) (Fin m) ℤ} (hA : PosDefGram A)
    (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1) (k : ℕ) : repNum (ofMatrixZ (sumI A k)) 1 = 2 * k := by
  rw [← repNum_sumSq_one k, repNum, repNum]
  have hsq : ∀ z : Fin k → ℤ, (sumSq k).eval z = ∑ i, z i ^ 2 := fun z => by
    rw [sumSq_eq_ofMatrixZ_one, eval_ofMatrixZ]; simp [dotProduct, sq]
  refine Nat.card_congr
    { toFun := fun x => ⟨fun j => x.1 (Fin.natAdd m j), ?_⟩
      invFun := fun z => ⟨Fin.append (0 : Fin m → ℤ) z.1, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun z => ?_ }
  · have hx : x.1 ⬝ᵥ (sumI A k *ᵥ x.1) = 1 := by
      have := x.2
      change (ofMatrixZ (sumI A k)).eval x.1 = 1 at this
      rwa [eval_ofMatrixZ] at this
    obtain ⟨j, s, hs, he⟩ := (norm_one_vectors hA h1 x.1).mp hx
    change (sumSq k).eval _ = 1
    rw [hsq, he]
    have : ∀ i : Fin k, ((s • (Pi.single (Fin.natAdd m j) 1 : Fin (m + k) → ℤ)) (Fin.natAdd m i)) ^ 2
        = if i = j then 1 else 0 := by
      intro i
      by_cases hij : i = j
      · subst hij; rcases hs with rfl | rfl <;> simp
      · simp [Pi.single_apply, hij]
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  · change (ofMatrixZ (sumI A k)).eval _ = 1
    rw [eval_ofMatrixZ, norm_sumI]
    have e1 : (fun a => (Fin.append (0 : Fin m → ℤ) z.1 : Fin (m + k) → ℤ) (Fin.castAdd k a)) = 0 := by
      funext a; simp
    have e2 : (fun b => (Fin.append (0 : Fin m → ℤ) z.1 : Fin (m + k) → ℤ) (Fin.natAdd m b)) = z.1 := by
      funext b; simp
    simp only [e1, Matrix.mulVec_zero, dotProduct_zero, zero_add]
    have := z.2
    change (sumSq k).eval z.1 = 1 at this
    rw [hsq] at this
    simpa using this
  · apply Subtype.ext
    have hx : x.1 ⬝ᵥ (sumI A k *ᵥ x.1) = 1 := by
      have := x.2
      change (ofMatrixZ (sumI A k)).eval x.1 = 1 at this
      rwa [eval_ofMatrixZ] at this
    obtain ⟨j, s, hs, he⟩ := (norm_one_vectors hA h1 x.1).mp hx
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [Fin.append_left, Pi.zero_apply]
      rw [he]
      simp [Pi.single_apply, castAdd_ne_natAdd]
    · simp
  · apply Subtype.ext
    funext j
    simp

/-- $I_n$ has a vector of norm $1$ for $n \ge 1$; hence it is not equivalent to $A \oplus I_k$ unless $k = n$. -/
theorem not_intEquiv_sumSq_sumI {m k : ℕ} {A : Matrix (Fin m) (Fin m) ℤ} (hA : PosDefGram A)
    (h1 : ∀ x, x ⬝ᵥ (A *ᵥ x) ≠ 1) (hm : 1 ≤ m) : ¬ IntEquiv (sumSq (m + k)) (ofMatrixZ (sumI A k)) := by
  intro h
  have := repNum_eq_of_intEquiv h 1
  rw [repNum_sumSq_one, repNum_sumI_one hA h1] at this
  omega

end QuadFormsKB.Lattices
