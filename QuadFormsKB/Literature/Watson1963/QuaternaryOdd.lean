/-
# Watson (1963), §7, Lemmas 9, 10 and §9, Lemma 14: the quaternary form splits off at odd primes

Watson, *The class-number of a positive quadratic form*, Proc. London Math. Soc. (3) 13 (1963), pp. 559-565.
This is the odd-prime part of the named input `WatsonQuaternaryLocal`: for a Watson-minimal positive definite $f$ in
$4 + m$ variables, $m \ge 8$, and a quaternary $g$ with $\det H_g = q^2$ and $r_q(g) = 2$, over $\mathbb Z_p$ with
$p$ odd the form $f$ is $g \perp \psi_p$.

* $p \ne q$: $\det H_g$ is a unit and $r_p(f) \ge (4 + m)/2 \ge 6 > 4$, so $f$ represents $g$ over $\mathbb Z_p$
  (`repOver_of_unimodular`), and a representation of a form of unit determinant splits off
  (`exists_isometricGL_orthSum_of_rep_padic`).
* $p = q$: $g \cong \langle a_0, a_1, q b_0, q b_1\rangle$ over $\mathbb Z_q$ (`exists_diag_quaternary_padic`: the
  exponents sum to $v_q(\det H_g) = 2$ and $r_q(g) = 2$ forces two of them to be $0$), while
  $f \cong \langle u_0, \dots, u_{r-1}, q u_r, \dots\rangle$ with $6 \le r = r_q(f) \le 9$. The unit blocks may be
  changed freely as long as their determinants are kept (classification of unimodular forms), so the first block can
  be made to start with $a_0, a_1$ and the second to start with $b_0, b_1$; moving these four coordinates to the front
  gives $f \cong g \perp \psi$ (`exists_orthSum_diagShape`).

*Notation.* `diagShape p r u` is the diagonal with entries $u_i$ for $i < r$ and $p\,u_i$ for $i \ge r$.
-/
import QuadFormsKB.Literature.Watson1963.ProbesOdd
import QuadFormsKB.Literature.Watson1963.TwoAdic

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Watson1963

open Siegel DefiniteForms

/-! ### Orthogonal sums of diagonal forms and block isometries -/

section Blocks

variable {K : Type*} [CommRing K]

/-- The block diagonal matrix $\begin{pmatrix} S & 0 \\ 0 & P \end{pmatrix}$ on `Fin (a + m)`. -/
def blkMat {a m : ℕ} (S : Matrix (Fin a) (Fin a) K) (P : Matrix (Fin m) (Fin m) K) :
    Matrix (Fin (a + m)) (Fin (a + m)) K :=
  Matrix.of fun i j =>
    Fin.addCases (motive := fun _ => K)
      (fun i₁ => Fin.addCases (motive := fun _ => K) (fun j₁ => S i₁ j₁) (fun _ => 0) j)
      (fun i₂ => Fin.addCases (motive := fun _ => K) (fun _ => 0) (fun j₂ => P i₂ j₂) j) i

theorem blkMat_mulVec_left {a m : ℕ} (S : Matrix (Fin a) (Fin a) K) (P : Matrix (Fin m) (Fin m) K)
    (x : Fin (a + m) → K) (i : Fin a) :
    (blkMat S P *ᵥ x) (Fin.castAdd m i) = (S *ᵥ fun j => x (Fin.castAdd m j)) i := by
  simp [blkMat, mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

theorem blkMat_mulVec_right {a m : ℕ} (S : Matrix (Fin a) (Fin a) K) (P : Matrix (Fin m) (Fin m) K)
    (x : Fin (a + m) → K) (i : Fin m) :
    (blkMat S P *ᵥ x) (Fin.natAdd a i) = (P *ᵥ fun j => x (Fin.natAdd a j)) i := by
  simp [blkMat, mulVec, dotProduct, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

theorem blkMat_mul {a m : ℕ} (S S' : Matrix (Fin a) (Fin a) K) (P P' : Matrix (Fin m) (Fin m) K) :
    blkMat S P * blkMat S' P' = blkMat (S * S') (P * P') := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_add]

theorem blkMat_one {a m : ℕ} : blkMat (1 : Matrix (Fin a) (Fin a) K) (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  have h1 : ∀ (i : Fin a) (j : Fin m), Fin.castAdd m i ≠ Fin.natAdd a j := fun i j h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h2 : ∀ (i : Fin m) (j : Fin a), Fin.natAdd a i ≠ Fin.castAdd m j := fun i j h => (h1 j i) h.symm
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkMat, Matrix.one_apply, h1, h2]

/-- **Orthogonal sums respect isometry:** $f \cong f'$ and $g \cong g'$ imply $f \perp g \cong f' \perp g'$. -/
theorem isometricGL_orthSum_of {a m : ℕ} {f f' : QuadForm K a} {g g' : QuadForm K m}
    (hf : IsometricGL f f') (hg : IsometricGL g g') :
    IsometricGL (QuadForm.orthSum f g) (QuadForm.orthSum f' g') := by
  obtain ⟨S, hS⟩ := hf
  obtain ⟨P, hP⟩ := hg
  refine ⟨⟨blkMat S.val P.val, blkMat (S⁻¹).val (P⁻¹).val, ?_, ?_⟩, fun x => ?_⟩
  · rw [blkMat_mul, Units.mul_inv, Units.mul_inv, blkMat_one]
  · rw [blkMat_mul, Units.inv_mul, Units.inv_mul, blkMat_one]
  · show (QuadForm.orthSum f g).evalIn K (blkMat S.val P.val *ᵥ x) = (QuadForm.orthSum f' g').evalIn K x
    rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_orthSum]
    have h1 : (fun i => (blkMat S.val P.val *ᵥ x) (Fin.castAdd m i)) = S.val *ᵥ fun j => x (Fin.castAdd m j) :=
      funext fun i => blkMat_mulVec_left _ _ _ i
    have h2 : (fun i => (blkMat S.val P.val *ᵥ x) (Fin.natAdd a i)) = P.val *ᵥ fun j => x (Fin.natAdd a j) :=
      funext fun i => blkMat_mulVec_right _ _ _ i
    rw [h1, h2]
    exact congrArg₂ (· + ·) (hS _) (hP _)

/-- **The orthogonal sum of diagonal forms is the diagonal form of the concatenation.** -/
theorem isometricGL_orthSum_diag {a m : ℕ} (u : Fin a → K) (v : Fin m → K) :
    IsometricGL (QuadForm.orthSum (QuadForm.diag u) (QuadForm.diag v)) (QuadForm.diag (Fin.append u v)) := by
  refine ⟨1, fun x => ?_⟩
  rw [Units.val_one, Matrix.one_mulVec]
  show (QuadForm.orthSum (QuadForm.diag u) (QuadForm.diag v)).evalIn K x = (QuadForm.diag (Fin.append u v)).eval x
  rw [QuadForm.evalIn_orthSum]
  show (QuadForm.diag u).eval _ + (QuadForm.diag v).eval _ = _
  rw [eval_diag', eval_diag', eval_diag', Fin.sum_univ_add]
  simp

/-- Scaling a diagonal isometry by a constant. -/
theorem isometricGL_diag_mul {k : ℕ} (c : K) {x y : Fin k → K}
    (h : IsometricGL (QuadForm.diag x) (QuadForm.diag y)) :
    IsometricGL (QuadForm.diag fun i => c * x i) (QuadForm.diag fun i => c * y i) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun z => ?_⟩
  have := hg z
  rw [eval_diag', eval_diag'] at this
  rw [eval_diag', eval_diag']
  simp only [mul_assoc, ← Finset.mul_sum, this]

end Blocks

/-! ### Unimodular blocks over $\mathbb Z_p$ -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- **Unit diagonal forms with the same determinant are isometric** ($p$ odd). -/
theorem isometricGL_diag_of_prod (hp : p ≠ 2) {k : ℕ} (x y : Fin k → ℤ_[p]) (hx : ∀ i, IsUnit (x i))
    (h : ∏ i, x i = ∏ i, y i) : IsometricGL (QuadForm.diag x) (QuadForm.diag y) := by
  refine Siegel.Kneser.isometricGL_of_unimodular hp _ _ ?_ ?_
  · rw [LocalDensity.DVR.det_hessian_diag]
    exact (isUnit_iff_not_dvd p _).1 (((isUnit_two_padic p hp).pow _).mul (isUnit_prod_padic p x hx))
  · rw [LocalDensity.DVR.det_hessian_diag, LocalDensity.DVR.det_hessian_diag, h]

/-- **The shape of a minimal form at an odd prime:** the diagonal with entries $u_i$ for $i < r$ and $p\,u_i$
for $i \ge r$. -/
def diagShape {N : ℕ} (r : ℕ) (u : Fin N → ℤ_[p]) : Fin N → ℤ_[p] :=
  fun i => if (i : ℕ) < r then u i else (p : ℤ_[p]) * u i

/-- **Changing the unit blocks:** two shapes with the same $r$ whose unit blocks have the same products (on the
indices $< r$ and on those $\ge r$) are isometric ($p$ odd). -/
theorem isometricGL_diagShape (hp : p ≠ 2) {n r : ℕ} (hr : r ≤ n) (u v : Fin n → ℤ_[p])
    (hu : ∀ i, IsUnit (u i)) (hv : ∀ i, IsUnit (v i))
    (h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < r), u i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < r), v i)
    (h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < r), u i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < r), v i) :
    IsometricGL (QuadForm.diag (diagShape p r u)) (QuadForm.diag (diagShape p r v)) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_add, Fin.prod_univ_add] at h1 h2
  have e1 : ∏ i : Fin r, u (Fin.castAdd s i) = ∏ i : Fin r, v (Fin.castAdd s i) := by simpa using h1
  have e2 : ∏ i : Fin s, u (Fin.natAdd r i) = ∏ i : Fin s, v (Fin.natAdd r i) := by simpa using h2
  have hshape : ∀ w : Fin (r + s) → ℤ_[p], diagShape p r w =
      Fin.append (fun i => w (Fin.castAdd s i)) (fun j => (p : ℤ_[p]) * w (Fin.natAdd r j)) := by
    intro w
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp [diagShape]
    · simp [diagShape]
  rw [hshape u, hshape v]
  have hA := isometricGL_diag_of_prod p hp (fun i : Fin r => u (Fin.castAdd s i))
    (fun i => v (Fin.castAdd s i)) (fun i => hu _) e1
  have hB := isometricGL_diag_mul (p : ℤ_[p]) (isometricGL_diag_of_prod p hp (fun i : Fin s => u (Fin.natAdd r i))
    (fun i => v (Fin.natAdd r i)) (fun i => hu _) e2)
  exact (isometricGL_orthSum_diag _ _).symm.trans
    ((isometricGL_orthSum_of hA hB).trans (isometricGL_orthSum_diag _ _))

/-- **Adjusting one unit:** given units $w_j$, a finite set $S$, $i \in S$ and a unit $Q$, change $w$ at $i$ only so
that $\prod_{j \in S} w'_j = Q$ and all $w'_j$ remain units. -/
theorem exists_adjust_unit {N : ℕ} (w : Fin N → ℤ_[p]) (hw : ∀ i, IsUnit (w i)) (S : Finset (Fin N))
    (i : Fin N) (hi : i ∈ S) (Q : ℤ_[p]) (hQ : IsUnit Q) :
    ∃ w' : Fin N → ℤ_[p], (∀ j, j ≠ i → w' j = w j) ∧ (∀ j, IsUnit (w' j)) ∧ ∏ j ∈ S, w' j = Q := by
  classical
  have hP : IsUnit (∏ j ∈ S.erase i, w j) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j _ => hw j)
  refine ⟨Function.update w i (Q * ↑(hP.unit⁻¹)), fun j hj => Function.update_of_ne hj _ _, fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact hQ.mul (Units.isUnit _)
    · rw [Function.update_of_ne hj]
      exact hw j
  · rw [← Finset.mul_prod_erase S _ hi, Function.update_self]
    have : ∏ j ∈ S.erase i, Function.update w i (Q * ↑(hP.unit⁻¹)) j = ∏ j ∈ S.erase i, w j :=
      Finset.prod_congr rfl fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [this]
    linear_combination Q * hP.mul_val_inv

/-- **Splitting off four prescribed coordinates:** if $3 \le r$ and $r + 3 \le 4 + m$, and $u_i$, $w_i$ are units,
then $\langle \mathrm{diagShape}\ r\ u\rangle \cong \langle \mathrm{diagShape}\ 2\ w\rangle \perp \psi$ for some form
$\psi$ in $m$ variables ($p$ odd). *Proof:* replace the unit blocks of $u$ by units starting with $w_0, w_1$ (resp.
$w_2, w_3$) with the same products (`exists_adjust_unit`, `isometricGL_diagShape`), then move the coordinates
$0, 1, r, r + 1$ to the front by a permutation. -/
theorem exists_orthSum_diagShape (hp : p ≠ 2) {m r : ℕ} (hr : 3 ≤ r) (hrN : r + 3 ≤ 4 + m)
    (u : Fin (4 + m) → ℤ_[p]) (hu : ∀ i, IsUnit (u i)) (w : Fin 4 → ℤ_[p]) (hw : ∀ i, IsUnit (w i)) :
    ∃ ψ : QuadForm ℤ_[p] m,
      IsometricGL (QuadForm.diag (diagShape p r u))
        (QuadForm.orthSum (QuadForm.diag (diagShape p 2 w)) ψ) := by
  classical
  have fne : ∀ a b : Fin (4 + m), (a : ℕ) ≠ b → a ≠ b := fun a b h e => h (by rw [e])
  obtain ⟨i0, hi0⟩ : ∃ i : Fin (4 + m), (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin (4 + m), (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i : Fin (4 + m), (i : ℕ) = 2 := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨i3, hi3⟩ : ∃ i : Fin (4 + m), (i : ℕ) = 3 := ⟨⟨3, by omega⟩, rfl⟩
  obtain ⟨j0, hj0⟩ : ∃ i : Fin (4 + m), (i : ℕ) = r := ⟨⟨r, by omega⟩, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ i : Fin (4 + m), (i : ℕ) = r + 1 := ⟨⟨r + 1, by omega⟩, rfl⟩
  obtain ⟨j2, hj2⟩ : ∃ i : Fin (4 + m), (i : ℕ) = r + 2 := ⟨⟨r + 2, by omega⟩, rfl⟩
  -- first modification of u
  set w1 : Fin (4 + m) → ℤ_[p] := fun i => if i = i0 then w 0 else if i = i1 then w 1 else
    if i = j0 then w 2 else if i = j1 then w 3 else u i with hw1
  have hw1u : ∀ i, IsUnit (w1 i) := by
    intro i
    simp only [hw1]
    split_ifs <;> first | exact hw _ | exact hu _
  have hw1_0 : w1 i0 = w 0 := by simp [hw1]
  have hw1_1 : w1 i1 = w 1 := by simp [hw1, fne i1 i0 (by omega)]
  have hw1_2 : w1 j0 = w 2 := by simp [hw1, fne j0 i0 (by omega), fne j0 i1 (by omega)]
  have hw1_3 : w1 j1 = w 3 := by
    simp [hw1, fne j1 i0 (by omega), fne j1 i1 (by omega), fne j1 j0 (by omega)]
  have hQ1 : IsUnit (∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => (i : ℕ) < r), u i) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j _ => hu j)
  have hQ2 : IsUnit (∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => ¬ (i : ℕ) < r), u i) :=
    Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j _ => hu j)
  obtain ⟨w2, hw2e, hw2u, hw2p⟩ := exists_adjust_unit p w1 hw1u
    (Finset.univ.filter (fun i : Fin (4 + m) => (i : ℕ) < r)) i2
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) _ hQ1
  obtain ⟨w3, hw3e, hw3u, hw3p⟩ := exists_adjust_unit p w2 hw2u
    (Finset.univ.filter (fun i : Fin (4 + m) => ¬ (i : ℕ) < r)) j2
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) _ hQ2
  have h1 : ∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => (i : ℕ) < r), u i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => (i : ℕ) < r), w3 i := by
    rw [← hw2p]
    refine Finset.prod_congr rfl fun j hj => (hw3e j ?_).symm
    have := (Finset.mem_filter.1 hj).2
    exact fne j j2 (by omega)
  have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => ¬ (i : ℕ) < r), u i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin (4 + m) => ¬ (i : ℕ) < r), w3 i := hw3p.symm
  have hiso1 := isometricGL_diagShape p hp (by omega : r ≤ 4 + m) u w3 hu hw3u h1 h2
  have hw3_0 : w3 i0 = w 0 := by
    rw [hw3e i0 (fne _ _ (by omega)), hw2e i0 (fne _ _ (by omega))]; exact hw1_0
  have hw3_1 : w3 i1 = w 1 := by
    rw [hw3e i1 (fne _ _ (by omega)), hw2e i1 (fne _ _ (by omega))]; exact hw1_1
  have hw3_2 : w3 j0 = w 2 := by
    rw [hw3e j0 (fne _ _ (by omega)), hw2e j0 (fne _ _ (by omega))]; exact hw1_2
  have hw3_3 : w3 j1 = w 3 := by
    rw [hw3e j1 (fne _ _ (by omega)), hw2e j1 (fne _ _ (by omega))]; exact hw1_3
  -- the permutation
  set σ : Equiv.Perm (Fin (4 + m)) := Equiv.swap i2 j0 * Equiv.swap i3 j1 with hσ
  have hσ0 : σ i0 = i0 := by
    show Equiv.swap i2 j0 (Equiv.swap i3 j1 i0) = i0
    rw [Equiv.swap_apply_of_ne_of_ne (fne i0 i3 (by omega)) (fne i0 j1 (by omega)),
      Equiv.swap_apply_of_ne_of_ne (fne i0 i2 (by omega)) (fne i0 j0 (by omega))]
  have hσ1 : σ i1 = i1 := by
    show Equiv.swap i2 j0 (Equiv.swap i3 j1 i1) = i1
    rw [Equiv.swap_apply_of_ne_of_ne (fne i1 i3 (by omega)) (fne i1 j1 (by omega)),
      Equiv.swap_apply_of_ne_of_ne (fne i1 i2 (by omega)) (fne i1 j0 (by omega))]
  have hσ2 : σ i2 = j0 := by
    show Equiv.swap i2 j0 (Equiv.swap i3 j1 i2) = j0
    rw [Equiv.swap_apply_of_ne_of_ne (fne i2 i3 (by omega)) (fne i2 j1 (by omega)), Equiv.swap_apply_left]
  have hσ3 : σ i3 = j1 := by
    show Equiv.swap i2 j0 (Equiv.swap i3 j1 i3) = j1
    rw [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (fne j1 i2 (by omega)) (fne j1 j0 (by omega))]
  set d : Fin (4 + m) → ℤ_[p] := fun k => diagShape p r w3 (σ k) with hdd
  have hperm : IsometricGL (QuadForm.diag (diagShape p r w3)) (QuadForm.diag d) :=
    isometricGL_diag_perm (diagShape p r w3) σ
  have hlt : ∀ i : Fin (4 + m), (i : ℕ) < r → diagShape p r w3 i = w3 i := fun i h => by
    simp [diagShape, h]
  have hge : ∀ i : Fin (4 + m), ¬ (i : ℕ) < r → diagShape p r w3 i = (p : ℤ_[p]) * w3 i := fun i h => by
    simp [diagShape, h]
  have hd : (d ∘ Fin.castAdd m) = diagShape p 2 w := by
    funext k
    obtain ⟨k, hk⟩ := k
    interval_cases k
    · have e : (Fin.castAdd m (⟨0, hk⟩ : Fin 4) : Fin (4 + m)) = i0 := Fin.ext (by simp [hi0])
      simp only [Function.comp, hdd, e, hσ0]
      rw [hlt i0 (by omega), hw3_0]
      simp [diagShape]
    · have e : (Fin.castAdd m (⟨1, hk⟩ : Fin 4) : Fin (4 + m)) = i1 := Fin.ext (by simp [hi1])
      simp only [Function.comp, hdd, e, hσ1]
      rw [hlt i1 (by omega), hw3_1]
      simp [diagShape]
    · have e : (Fin.castAdd m (⟨2, hk⟩ : Fin 4) : Fin (4 + m)) = i2 := Fin.ext (by simp [hi2])
      simp only [Function.comp, hdd, e, hσ2]
      rw [hge j0 (by omega), hw3_2]
      simp [diagShape]
    · have e : (Fin.castAdd m (⟨3, hk⟩ : Fin 4) : Fin (4 + m)) = i3 := Fin.ext (by simp [hi3])
      simp only [Function.comp, hdd, e, hσ3]
      rw [hge j1 (by omega), hw3_3]
      simp [diagShape]
  have hsplit := isometricGL_orthSum_diag (d ∘ Fin.castAdd m) (d ∘ Fin.natAdd 4)
  have eapp : Fin.append (d ∘ Fin.castAdd m) (d ∘ Fin.natAdd 4) = d := Fin.append_castAdd_natAdd
  rw [eapp, hd] at hsplit
  exact ⟨_, hiso1.trans (hperm.trans hsplit.symm)⟩

/-- **A diagonal form over $\mathbb F_p$ has rank at least the number of nonzero coefficients** ($p$ odd): if
$\bar F(T\vec y) = \sum_i e_i y_i^2$ for an invertible $T$ then $\#\{i : e_i \ne 0\} \le r_p(F)$. *Proof:* the
inverse of $T$ maps the radical $R_p(F)$ injectively into the vectors supported on $\{e_i = 0\}$
(`rad_support_of_diag`). Together with `rankModP_le_card_of_diag` this is $r_p(F) = \#\{e_i \ne 0\}$. -/
theorem card_le_rankModP_of_diag (hp : p ≠ 2) {n : ℕ} (F : QuadForm ℤ n)
    (T T' : Matrix (Fin n) (Fin n) (ZMod p)) (hTT : T * T' = 1) (e : Fin n → ZMod p)
    (h : ∀ y, F.evalIn (ZMod p) (T *ᵥ y) = ∑ i, e i * y i ^ 2) :
    (Finset.univ.filter fun i => e i ≠ 0).card ≤ rankModP p F := by
  classical
  have hTT' : T' * T = 1 := mul_eq_one_comm.mp hTT
  let Φ : radModP p F →ₗ[ZMod p] ({i // e i = 0} → ZMod p) :=
    (LinearMap.funLeft (ZMod p) (ZMod p) (Subtype.val : {i // e i = 0} → Fin n)) ∘ₗ T'.mulVecLin ∘ₗ
      (radModP p F).subtype
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    have hz : T' *ᵥ (x : Fin n → ZMod p) = 0 := by
      funext j
      by_cases hj : e j = 0
      · have := congrFun hx ⟨j, hj⟩
        simpa [Φ] using this
      · exact rad_support_of_diag p hp F T T' hTT e h x.2 j hj
    apply Subtype.ext
    have : (x : Fin n → ZMod p) = T *ᵥ (T' *ᵥ (x : Fin n → ZMod p)) := by
      rw [mulVec_mulVec, hTT, one_mulVec]
    rw [this, hz, mulVec_zero]
    rfl
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Fintype.card {i // e i = 0} = (Finset.univ.filter fun i => e i = 0).card := by
    rw [Fintype.card_subtype]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => e i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at h3
  have h5 : (Finset.univ.filter fun i => ¬ e i = 0) = (Finset.univ.filter fun i => e i ≠ 0) := rfl
  rw [h5] at h3
  have h4 := rankModP_add_finrank p F
  omega

/-- **Exponents of $p$ are determined by a unit-times-power identity:** $p^k U = p^e V$ with $U, V$ units forces
$k = e$. -/
theorem exp_eq_of_unit_mul {k e : ℕ} {U V : ℤ_[p]} (hU : IsUnit U) (hV : IsUnit V)
    (h : (p : ℤ_[p]) ^ k * U = (p : ℤ_[p]) ^ e * V) : k = e := by
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have key : ∀ k e : ℕ, ∀ U V : ℤ_[p], IsUnit U →
      (p : ℤ_[p]) ^ k * U = (p : ℤ_[p]) ^ (k + e + 1) * V → False := by
    intro k e U V hU h
    have : U = (p : ℤ_[p]) ^ (e + 1) * V := by
      apply mul_left_cancel₀ (pow_ne_zero k hp0)
      rw [h]; ring
    exact (isUnit_iff_not_dvd p U).1 hU ⟨(p : ℤ_[p]) ^ e * V, by rw [this]; ring⟩
  rcases lt_trichotomy k e with hlt | rfl | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, e = k + d + 1 := ⟨e - k - 1, by omega⟩
    exact (key k d U V hU h).elim
  · rfl
  · obtain ⟨d, rfl⟩ : ∃ d, k = e + d + 1 := ⟨k - e - 1, by omega⟩
    exact (key e d V U hV h.symm).elim

/-- **The quaternary form $g(4, q^2)$ at the prime $q$** ($q$ odd): an integral quaternary form with
$\det H_g = q^2$ and $r_q(g) = 2$ is $\mathbb Z_q$-equivalent to $\langle w_0, w_1, q w_2, q w_3\rangle$ with units
$w_i$. *Proof:* diagonalize $g \cong \langle q^{\nu_i} w_i\rangle$ (`exists_diag_padic`); comparing determinants,
$\sum \nu_i = 2$; the number of $i$ with $\nu_i = 0$ is at most $r_q(g) = 2$ (`card_le_rankModP_of_diag`) and at least
$2$ (as $\sum \nu_i = 2$), so exactly two exponents vanish and the other two are $1$; sort them
(`exists_perm_of_card`, `isometricGL_diag_perm`). -/
theorem exists_diag_quaternary_padic (hp : p ≠ 2) {g : QuadForm ℤ 4} (hdet : g.hessian.det = (p : ℤ) ^ 2)
    (hr : rankModP p g = 2) :
    ∃ w : Fin 4 → ℤ_[p], (∀ i, IsUnit (w i)) ∧
      IsometricGL (g.map (Int.castRingHom ℤ_[p])) (QuadForm.diag (diagShape p 2 w)) := by
  classical
  have hpp : p.Prime := Fact.out
  have hA : g.hessian.det ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by exact_mod_cast hpp.ne_zero)
  obtain ⟨T, T', ν, w, hTT, hw, hT⟩ := exists_diag_padic p hp g hA
  set a : Fin 4 → ℤ_[p] := fun i => (p : ℤ_[p]) ^ ν i * w i with ha
  have hTu : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hTT
  have hevalT : ∀ x, (QuadForm.diag a).eval x = (g.map (Int.castRingHom ℤ_[p])).eval (T *ᵥ x) := by
    intro x
    rw [eval_diag', eval_map_padic, hT]
  have step1 : IsometricGL (g.map (Int.castRingHom ℤ_[p])) (QuadForm.diag a) := by
    rw [isometricGL_iff_isometricIn]
    exact ⟨T, hTu, fun x => (hevalT x).symm⟩
  have hdetA : ((g.hessian.det : ℤ) : ℤ_[p]) = (p : ℤ_[p]) ^ 2 := by rw [hdet]; push_cast; ring
  have hdetEq := congrArg Matrix.det (LocalDensity.DVR.hessian_eq_of_eval hevalT)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LocalDensity.DVR.det_hessian_diag,
    hessian_map_det_padic, hdetA] at hdetEq
  have hprod : ∏ i, a i = (p : ℤ_[p]) ^ (∑ i, ν i) * ∏ i, w i := by
    simp only [ha, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod] at hdetEq
  have hs : (∑ i, ν i) = 2 := by
    refine exp_eq_of_unit_mul p (U := (2 : ℤ_[p]) ^ 4 * ∏ i, w i) (V := T.det * T.det) ?_ ?_ ?_
    · exact ((isUnit_two_padic p hp).pow _).mul (isUnit_prod_padic p w hw)
    · exact hTu.mul hTu
    · linear_combination hdetEq
  -- the number of unit exponents
  have hred : ∀ (X Y : Matrix (Fin 4) (Fin 4) ℤ_[p]), X * Y = 1 →
      X.map PadicInt.toZMod * Y.map PadicInt.toZMod = 1 := by
    intro X Y h
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have hT1 := toZMod_diag p g T (fun i => (p : ℤ_[p]) ^ ν i * w i) hT
  have he0 : ∀ i, PadicInt.toZMod ((p : ℤ_[p]) ^ ν i * w i) ≠ 0 ↔ ν i = 0 := fun i =>
    toZMod_pow_mul_ne_zero p (hw i)
  have hfilt : (Finset.univ.filter fun i => PadicInt.toZMod ((p : ℤ_[p]) ^ ν i * w i) ≠ 0) =
      Finset.univ.filter fun i => ν i = 0 := Finset.filter_congr fun i _ => he0 i
  have hZ : (Finset.univ.filter fun i => ν i = 0).card ≤ 2 := by
    have := card_le_rankModP_of_diag p hp g _ _ (hred T T' hTT) _ hT1
    rw [hfilt, hr] at this
    exact this
  have hc : (Finset.univ.filter fun i => ν i = 0).card +
      (Finset.univ.filter fun i => ¬ ν i = 0).card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4))) (fun i => ν i = 0)
    simpa using this
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin 4)), (if ν i = 0 then 0 else 1) ≤ ν i := by
    intro i _
    split_ifs with h <;> omega
  have hsum : ∑ i, (if ν i = 0 then 0 else 1) = (Finset.univ.filter fun i => ¬ ν i = 0).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> rfl
  have hle2 : (Finset.univ.filter fun i => ¬ ν i = 0).card ≤ 2 := by
    rw [← hsum, ← hs]
    exact Finset.sum_le_sum hle
  have heq : ∑ i, (if ν i = 0 then 0 else 1) = ∑ i, ν i := by omega
  have hν : ∀ i, ν i = if ν i = 0 then 0 else 1 := fun i =>
    ((Finset.sum_eq_sum_iff_of_le hle).1 heq i (Finset.mem_univ i)).symm
  have hZ2 : (Finset.univ.filter fun i => ν i = 0).card = 2 := by omega
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (fun i => ν i = 0) hZ2
  have hshape : (fun k => a (σ k)) = diagShape p 2 (fun k => w (σ k)) := by
    funext k
    have hk := hσ k
    simp only [ha, diagShape]
    by_cases hlt : (k : ℕ) < 2
    · have : ν (σ k) = 0 := hk.1 hlt
      simp [hlt, this]
    · have h0 : ν (σ k) ≠ 0 := fun h0 => hlt (hk.2 h0)
      have : ν (σ k) = 1 := by
        have := hν (σ k)
        simpa [h0] using this
      simp [hlt, this]
  refine ⟨fun k => w (σ k), fun k => hw _, ?_⟩
  have step2 := isometricGL_diag_perm a σ
  rw [hshape] at step2
  exact step1.trans step2

end Padic

/-- **The odd-prime part of `WatsonQuaternaryLocal`** (Watson 1963, §7, Lemmas 9, 10, pp. 559-565): let $f$ be a
Watson-minimal positive definite form in $4 + m$ variables, $m \ge 8$, let $q$ be a prime with $r_q(f) \le 9$ and
let $g$ be a quaternary integral form with $\det H_g = q^2$ and $r_q(g) = 2$ (e.g. Watson's $g(4, q^2)$). Then for
every odd prime $p$ there is a form $\psi_p$ in $m$ variables over $\mathbb Z_p$ with
$f \cong g \perp \psi_p$ over $\mathbb Z_p$. *Proof:* if $p \ne q$, $\det H_g$ is a unit and $r_p(f) \ge 6$, so $f$
represents $g$ (`repOver_of_unimodular`) and $g$ splits off
(`exists_isometricGL_orthSum_of_rep_padic`); if $p = q$, $f \cong \langle u_0, \dots, u_{r-1}, q u_r, \dots\rangle$
with $6 \le r \le 9$ (`exists_diag_of_minimal_odd`) and $g \cong \langle w_0, w_1, q w_2, q w_3\rangle$
(`exists_diag_quaternary_padic`), and `exists_orthSum_diagShape` splits $g$ off. -/
@[kb "watson1963" "§7, Lemmas 9, 10, pp. 559–565 (g(4, q²) splits off at odd p)"]
theorem quaternary_split_odd {m : ℕ} {f : QuadForm ℤ (4 + m)} (hf : IntQF.PosDef f) (hmin : IsWatsonMinimal f)
    (hm : 8 ≤ m) {q : ℕ} [Fact q.Prime] (hr : rankModP q f ≤ 9) {g : QuadForm ℤ 4}
    (hdet : g.hessian.det = (q : ℤ) ^ 2) (hgq : rankModP q g = 2)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ ψp : QuadForm ℤ_[p] m,
      IsometricGL (f.map (Int.castRingHom ℤ_[p])) (QuadForm.orthSum (g.map (Int.castRingHom ℤ_[p])) ψp) := by
  classical
  have hpp : p.Prime := Fact.out
  have hqq : q.Prime := Fact.out
  by_cases hpq : p = q
  · subst hpq
    have hN := IsWatsonMinimal.le_two_mul_rankModP p hf hmin
    obtain ⟨u, hu, hiso⟩ := exists_diag_of_minimal_odd hf hmin p hp
    obtain ⟨w, hw, hg⟩ := exists_diag_quaternary_padic p hp hdet hgq
    obtain ⟨ψ, hψ⟩ := exists_orthSum_diagShape p hp (m := m) (r := rankModP p f) (by omega) (by omega) u hu w hw
    exact ⟨ψ, hiso.trans (hψ.trans (isometricGL_orthSum_of hg.symm (IsometricGL.refl ψ)))⟩
  · have hN := IsWatsonMinimal.le_two_mul_rankModP p hf hmin
    have hnd : ¬ (p : ℤ) ∣ g.hessian.det := by
      rw [hdet]
      intro h
      have h1 : (p : ℤ) ∣ (q : ℤ) := (Nat.prime_iff_prime_int.mp hpp).dvd_of_dvd_pow h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hpp hqq).mp (by exact_mod_cast h1))
    obtain ⟨H, hH⟩ := repOver_of_unimodular p hf hmin hp g hnd (by omega)
    have hunit : IsUnit (g.map (Int.castRingHom ℤ_[p])).hessian.det := by
      rw [hessian_map_det_padic, isUnit_iff_not_dvd]
      intro h
      apply hnd
      have := (toZMod_eq_zero_iff_dvd p _).2 h
      rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    obtain ⟨m', hm', ψ, hiso⟩ := exists_isometricGL_orthSum_of_rep_padic p H
      (fun y => by rw [eval_map_padic, eval_map_padic]; exact hH y) hunit
    have hmm : m' = m := by omega
    subst hmm
    exact ⟨ψ, hiso⟩

end QuadFormsKB.Watson1963
