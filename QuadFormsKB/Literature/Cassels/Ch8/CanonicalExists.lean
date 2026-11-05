/-
# Cassels, Chapter 8, Theorem 3.1, existence of the canonical form ($p \ne 2$)

Cassels' proof (pp. 116–117): by Lemma 3.1 put a coefficient of maximal absolute value at $f_{11}$; since $p \ne 2$,
$\lvert f_{1j}\rvert \le \lvert f_{11}\rvert$, so completing the square splits off $f_{11}x_1^{2}$; by induction $f$ is
equivalent to a diagonal form with $\lvert f_{11}\rvert \ge \lvert f_{22}\rvert \ge \cdots$; lumping the terms with the
same $\lvert f_{jj}\rvert$, Lemma 3.4 turns each group into $p^{e}(y_1^{2} + \cdots + y_{m-1}^{2} + uy_m^{2})$, and
$u = v^{2}$ or $rv^{2}$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Canonical
import QuadFormsKB.Siegel.UnimodularPadic
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-! **Proof organisation.** Helper matrices `blk`/`blk2` border a matrix by one/two coordinates; `split_step` is
Cassels' completion of the square after Lemma 3.1; `LEq` compares diagonal matrices of lists, with the rotation of
Lemma 3.4 (via `Siegel.Kneser.exists_binary_one`) in `LEq.rot` and `merge`; `main_claim` is the induction. -/

/-- Bordering a matrix by a corner entry `a`: `diag(a) ⊕ A` on `Fin (n+1)`. -/
private def blk {R : Type*} [Zero R] (a : R) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases a (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

private theorem blk_mul {R : Type*} [Semiring R] (a b : R) (A B : Matrix (Fin n) (Fin n) R) :
    blk a A * blk b B = blk (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem blk_transpose {R : Type*} [Zero R] (a : R) (A : Matrix (Fin n) (Fin n) R) :
    (blk a A)ᵀ = blk a Aᵀ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blk]

private theorem blk_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (a : R) (A : Matrix (Fin n) (Fin n) R) :
    (blk a A).map φ = blk (φ a) (A.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [blk]

private theorem blk_one {R : Type*} [Semiring R] : blk (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blk, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private theorem blk_det {R : Type*} [CommRing R] (a : R) (A : Matrix (Fin n) (Fin n) R) :
    (blk a A).det = a * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blk]
  congr 2

private theorem blk_diagonal {R : Type*} [Zero R] (a : R) (d : Fin n → R) :
    blk a (Matrix.diagonal d) = Matrix.diagonal (Fin.cons a d : Fin (n + 1) → R) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blk, Matrix.diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- Two-coordinate bordering. -/
private def blk2 {R : Type*} [Zero R] (q00 q01 q10 q11 : R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases q00 (fun j' => Fin.cases q01 (fun _ => 0) j') j)
    (fun i' => Fin.cases (Fin.cases q10 (fun j' => Fin.cases q11 (fun _ => 0) j') j)
      (fun i'' => Fin.cases 0 (fun j' => Fin.cases 0 (fun j'' => A i'' j'') j') j) i') i

@[elab_as_elim] private theorem fin3 {motive : Fin (n + 2) → Prop} (i : Fin (n + 2)) (h0 : motive 0)
    (h1 : motive 1) (h2 : ∀ i : Fin n, motive i.succ.succ) : motive i := by
  refine Fin.cases h0 (fun i => ?_) i
  exact Fin.cases h1 h2 i

section
variable {R : Type*} [Zero R] (a b c d : R) (A : Matrix (Fin n) (Fin n) R)
@[simp] private theorem blk2_00 : blk2 a b c d A 0 0 = a := rfl
@[simp] private theorem blk2_01 : blk2 a b c d A 0 1 = b := rfl
@[simp] private theorem blk2_10 : blk2 a b c d A 1 0 = c := rfl
@[simp] private theorem blk2_11 : blk2 a b c d A 1 1 = d := rfl
@[simp] private theorem blk2_0s (j : Fin n) : blk2 a b c d A 0 j.succ.succ = 0 := rfl
@[simp] private theorem blk2_1s (j : Fin n) : blk2 a b c d A 1 j.succ.succ = 0 := rfl
@[simp] private theorem blk2_s0 (i : Fin n) : blk2 a b c d A i.succ.succ 0 = 0 := rfl
@[simp] private theorem blk2_s1 (i : Fin n) : blk2 a b c d A i.succ.succ 1 = 0 := rfl
@[simp] private theorem blk2_ss (i j : Fin n) : blk2 a b c d A i.succ.succ j.succ.succ = A i j := rfl
end

private theorem blk2_mul {R : Type*} [Semiring R] (a b c d a' b' c' d' : R) (A B : Matrix (Fin n) (Fin n) R) :
    blk2 a b c d A * blk2 a' b' c' d' B =
      blk2 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') (A * B) := by
  ext i j
  refine fin3 i ?_ ?_ ?_ <;> refine fin3 j ?_ ?_ ?_ <;> intros <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

private theorem blk2_transpose {R : Type*} [Zero R] (a b c d : R) (A : Matrix (Fin n) (Fin n) R) :
    (blk2 a b c d A)ᵀ = blk2 a c b d Aᵀ := by
  ext i j
  refine fin3 i ?_ ?_ ?_ <;> refine fin3 j ?_ ?_ ?_ <;> intros <;> simp

private theorem blk2_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (a b c d : R)
    (A : Matrix (Fin n) (Fin n) R) :
    (blk2 a b c d A).map φ = blk2 (φ a) (φ b) (φ c) (φ d) (A.map φ) := by
  ext i j
  refine fin3 i ?_ ?_ ?_ <;> refine fin3 j ?_ ?_ ?_ <;> intros <;> simp

private theorem blk2_one {R : Type*} [Semiring R] :
    blk2 (1 : R) 0 0 1 (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine fin3 i ?_ ?_ ?_ <;> refine fin3 j ?_ ?_ ?_ <;> intros <;>
    simp [Matrix.one_apply, Fin.ext_iff]

private theorem blk2_diag {R : Type*} [Zero R] (x y : R) (d : Fin n → R) :
    blk2 x 0 0 y (Matrix.diagonal d) = Matrix.diagonal (Fin.cons x (Fin.cons y d) : Fin (n + 2) → R) := by
  ext i j
  refine fin3 i ?_ ?_ ?_ <;> refine fin3 j ?_ ?_ ?_ <;> intros <;>
    simp [Matrix.diagonal_apply, Fin.ext_iff]


/-! ### Equivalence combinators -/

private theorem zpEquiv_of_isUnit {F G : Matrix (Fin n) (Fin n) ℚ_[p]} (T : Matrix (Fin n) (Fin n) ℤ_[p])
    (hT : IsUnit T) (h : (T.map PadicInt.Coe.ringHom)ᵀ * F * T.map PadicInt.Coe.ringHom = G) : ZpEquiv F G := by
  obtain ⟨u, rfl⟩ := hT
  exact ⟨u, h⟩

private theorem isUnit_blk {a : ℤ_[p]} (ha : IsUnit a) {A : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : IsUnit A) :
    IsUnit (blk a A) := by
  obtain ⟨u, rfl⟩ := hA
  obtain ⟨v, rfl⟩ := ha
  exact ⟨⟨blk (v : ℤ_[p]) (u : Matrix (Fin n) (Fin n) ℤ_[p]),
    blk ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ((u⁻¹ : (Matrix (Fin n) (Fin n) ℤ_[p])ˣ) : Matrix (Fin n) (Fin n) ℤ_[p]),
    by rw [blk_mul, Units.mul_inv, Units.mul_inv, blk_one], by rw [blk_mul, Units.inv_mul, Units.inv_mul, blk_one]⟩,
    rfl⟩

private theorem zp_cons (a : ℚ_[p]) {F G : Matrix (Fin n) (Fin n) ℚ_[p]} (h : ZpEquiv F G) :
    ZpEquiv (blk a F) (blk a G) := by
  obtain ⟨T, hT⟩ := h
  refine zpEquiv_of_isUnit (blk 1 T.val) (isUnit_blk isUnit_one T.isUnit) ?_
  rw [blk_map, map_one, blk_transpose, blk_mul, blk_mul, hT]
  simp

private theorem zp_scale (w : ℤ_[p]) (hw : IsUnit w) (a : ℚ_[p]) (G : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ZpEquiv (blk a G) (blk (((w : ℤ_[p]) : ℚ_[p]) ^ 2 * a) G) := by
  refine zpEquiv_of_isUnit (blk w 1) (isUnit_blk hw isUnit_one) ?_
  rw [blk_map, blk_transpose, blk_mul, blk_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  congr 1
  simp only [PadicInt.Coe.ringHom_apply]
  ring

private theorem ZpEquiv.det_ne {F G : Matrix (Fin n) (Fin n) ℚ_[p]} (h : ZpEquiv F G) (hF : F.det ≠ 0) :
    G.det ≠ 0 := by
  obtain ⟨T, hT⟩ := h
  have h1 : (T.val.map PadicInt.Coe.ringHom) * ((T⁻¹).val.map PadicInt.Coe.ringHom) = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (T.val.map PadicInt.Coe.ringHom).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero h2 hF) h2

private theorem zp_rot (c : ℚ_[p]) (a b X Y : ℤ_[p]) (h : a * X ^ 2 + b * Y ^ 2 = 1)
    (D : Matrix (Fin n) (Fin n) ℚ_[p]) :
    ZpEquiv (blk2 (c * (a : ℚ_[p])) 0 0 (c * (b : ℚ_[p])) D) (blk2 c 0 0 (c * ((a : ℚ_[p]) * b)) D) := by
  have hq : (a : ℚ_[p]) * X ^ 2 + b * Y ^ 2 = 1 := by
    have := congrArg (PadicInt.Coe.ringHom (p := p)) h
    simpa using this
  have hU : IsUnit (blk2 X (-(b * Y)) Y (a * X) (1 : Matrix (Fin n) (Fin n) ℤ_[p])) := by
    refine ⟨⟨blk2 X (-(b * Y)) Y (a * X) (1 : Matrix (Fin n) (Fin n) ℤ_[p]),
      blk2 (a * X) (b * Y) (-Y) X (1 : Matrix (Fin n) (Fin n) ℤ_[p]), ?_, ?_⟩, rfl⟩
    · rw [blk2_mul, Matrix.mul_one, ← blk2_one]
      congr 1 <;> first | ring1 | linear_combination h
    · rw [blk2_mul, Matrix.mul_one, ← blk2_one]
      congr 1 <;> first | ring1 | linear_combination h
  refine zpEquiv_of_isUnit _ hU ?_
  rw [blk2_map, blk2_transpose, blk2_mul, blk2_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_neg, map_mul, PadicInt.Coe.ringHom_apply]
  congr 1
  · linear_combination c * hq
  · ring1
  · ring1
  · linear_combination (c * a * b) * hq

/-! ### Lists of diagonal entries -/

/-- The diagonal matrix of a list with `m` entries. -/
private noncomputable def dg'(L : List ℚ_[p]) (m : ℕ) (h : L.length = m) : Matrix (Fin m) (Fin m) ℚ_[p] :=
  Matrix.diagonal fun i => L[(i : ℕ)]'(h ▸ i.2)

private theorem dg'_cons (a : ℚ_[p]) (L : List ℚ_[p]) (m : ℕ) (h : (a :: L).length = m + 1) :
    dg' (a :: L) (m + 1) h = blk a (dg' L m (by simpa using h)) := by
  rw [dg', dg', blk_diagonal]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

private theorem dg'_cons2 (x y : ℚ_[p]) (S : List ℚ_[p]) (m : ℕ) (h : (x :: y :: S).length = m + 2) :
    dg' (x :: y :: S) (m + 2) h = blk2 x 0 0 y (dg' S m (by simpa using h)) := by
  rw [dg', dg', blk2_diag]
  congr 1
  funext i
  refine fin3 i ?_ ?_ ?_ <;> intros <;> simp

/-- `Z_p`-equivalence of the diagonal matrices of two lists. -/
private def LEq (L L' : List ℚ_[p]) : Prop :=
  L.length = L'.length ∧ ∀ m (h : L.length = m) (h' : L'.length = m), ZpEquiv (dg' L m h) (dg' L' m h')

private theorem LEq.refl (L : List ℚ_[p]) : LEq L L := ⟨rfl, fun _ _ _ => ZpEquiv.refl _⟩

private theorem LEq.trans {L L' L'' : List ℚ_[p]} (h₁ : LEq L L') (h₂ : LEq L' L'') : LEq L L'' :=
  ⟨h₁.1.trans h₂.1, fun m h h'' => (h₁.2 m h (h₁.1.symm.trans h)).trans (h₂.2 m (h₁.1.symm.trans h) h'')⟩

private theorem LEq.cons (a : ℚ_[p]) {L L' : List ℚ_[p]} (h : LEq L L') : LEq (a :: L) (a :: L') := by
  refine ⟨by simp [h.1], fun m hm hm' => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨L.length, by simpa using hm.symm⟩
  rw [dg'_cons, dg'_cons]
  exact zp_cons a (h.2 _ (by simpa using hm) (by simpa using hm'))

private theorem LEq.scale (w : ℤ_[p]) (hw : IsUnit w) (x : ℚ_[p]) (S : List ℚ_[p]) :
    LEq (x :: S) ((((w : ℤ_[p]) : ℚ_[p]) ^ 2 * x) :: S) := by
  refine ⟨rfl, fun m hm hm' => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨S.length, by simpa using hm.symm⟩
  rw [dg'_cons, dg'_cons]
  exact zp_scale w hw x _

private theorem LEq.rot (hp2 : p ≠ 2) (c u s : ℚ_[p]) (hu : ‖u‖ = 1) (hs : ‖s‖ = 1) (S : List ℚ_[p]) :
    LEq (c * u :: c * s :: S) (c :: c * (u * s) :: S) := by
  refine ⟨rfl, fun m hm hm' => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨S.length, by simpa using hm.symm⟩
  rw [dg'_cons2, dg'_cons2]
  set a : ℤ_[p] := ⟨u, hu.le⟩ with ha
  set b : ℤ_[p] := ⟨s, hs.le⟩ with hb
  have ha1 : IsUnit a := PadicInt.isUnit_iff.2 hu
  have hb1 : IsUnit b := PadicInt.isUnit_iff.2 hs
  obtain ⟨X, Y, hXY⟩ := Siegel.Kneser.exists_binary_one hp2 ha1 hb1
  exact zp_rot c a b X Y hXY _

/-! ### Square classes of units -/

private theorem unit_of_norm {u : ℚ_[p]} (hu : ‖u‖ = 1) : ∃ v : ℤ_[p]ˣ, ((v : ℤ_[p]) : ℚ_[p]) = u :=
  ⟨(PadicInt.isUnit_iff.2 (show ‖(⟨u, hu.le⟩ : ℤ_[p])‖ = 1 from hu)).unit, rfl⟩

private theorem sq_class (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r) (u : ℚ_[p])
    (hu : ‖u‖ = 1) : ∃ (ε : Fin 2) (w : ℤ_[p]), IsUnit w ∧ u = r ^ (ε : ℕ) * ((w : ℤ_[p]) : ℚ_[p]) ^ 2 := by
  obtain ⟨uu, rfl⟩ := unit_of_norm hu
  obtain ⟨rr, rfl⟩ := unit_of_norm hr1
  have hnorm : ∀ {x : ℚ_[p]}, ∀ {y : ℚ_[p]}, x * x = y → ‖y‖ = 1 → ‖x‖ = 1 := by
    intro x y hxy hy
    rw [← hxy, norm_mul] at hy
    nlinarith [norm_nonneg x]
  by_cases hsq : IsSquare (((uu : ℤ_[p]) : ℚ_[p]))
  · obtain ⟨x, hx⟩ := hsq
    have hx1 : ‖x‖ = 1 := hnorm hx.symm hu
    refine ⟨0, ⟨x, hx1.le⟩, PadicInt.isUnit_iff.2 hx1, ?_⟩
    simp only [Fin.val_zero, pow_zero, one_mul]
    rw [hx]; ring
  · have hA : ¬ IsSquare (PadicInt.toZMod (uu : ℤ_[p])) :=
      fun h => hsq ((QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 uu).2 h)
    have hB : ¬ IsSquare (PadicInt.toZMod (rr : ℤ_[p])) :=
      fun h => hr ((QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 rr).2 h)
    have hA0 : PadicInt.toZMod (uu : ℤ_[p]) ≠ 0 := Siegel.Kneser.toZMod_ne_zero_of_isUnit uu.isUnit
    have hB0 : PadicInt.toZMod (rr : ℤ_[p]) ≠ 0 := Siegel.Kneser.toZMod_ne_zero_of_isUnit rr.isUnit
    have hAB : IsSquare (PadicInt.toZMod ((uu * rr : ℤ_[p]ˣ) : ℤ_[p])) := by
      rw [Units.val_mul, map_mul]
      rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hA0 hB0), map_mul,
        quadraticChar_neg_one_iff_not_isSquare.2 hA, quadraticChar_neg_one_iff_not_isSquare.2 hB]
      norm_num
    obtain ⟨x, hx⟩ := (QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 (uu * rr)).2 hAB
    have hx' : ((uu : ℤ_[p]) : ℚ_[p]) * ((rr : ℤ_[p]) : ℚ_[p]) = x * x := by
      rw [← hx]; simp
    have hx1 : ‖x‖ = 1 := by
      refine hnorm hx'.symm ?_
      rw [norm_mul, hu, hr1, one_mul]
    have hr0 : ((rr : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
      intro h; rw [h, norm_zero] at hr1; exact zero_ne_one hr1
    have hxr : ‖x / ((rr : ℤ_[p]) : ℚ_[p])‖ = 1 := by rw [norm_div, hx1, hr1, div_one]
    refine ⟨1, ⟨x / ((rr : ℤ_[p]) : ℚ_[p]), hxr.le⟩, PadicInt.isUnit_iff.2 hxr, ?_⟩
    show _ = _ ^ 1 * (x / ((rr : ℤ_[p]) : ℚ_[p])) ^ 2
    field_simp
    linear_combination hx'

/-! ### Splitting off the maximal coefficient -/

private theorem qf_conj (F : Matrix (Fin n) (Fin n) ℚ_[p]) (T : Matrix (Fin n) (Fin n) ℤ_[p])
    (x : Fin n → ℤ_[p]) :
    qf ((T.map PadicInt.Coe.ringHom)ᵀ * F * T.map PadicInt.Coe.ringHom) (toQ x) = qf F (toQ (T *ᵥ x)) := by
  have hmv : toQ (T *ᵥ x) = T.map PadicInt.Coe.ringHom *ᵥ toQ x := by
    funext k; exact RingHom.map_mulVec PadicInt.Coe.ringHom T x k
  rw [hmv]
  simp only [qf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mul_assoc]
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]

private theorem qf_blk (g x : ℚ_[p]) (A : Matrix (Fin n) (Fin n) ℚ_[p]) (v : Fin n → ℚ_[p]) :
    qf (blk g A) (Fin.cons x v : Fin (n + 1) → ℚ_[p]) = g * x * x + qf A v := by
  simp [qf, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, blk, Finset.mul_sum]
  ring

private theorem toQ_cons (a : Fin n → ℤ_[p]) :
    toQ (Fin.cons (0 : ℤ_[p]) a : Fin (n + 1) → ℤ_[p]) = Fin.cons 0 (toQ a) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [toQ]

private theorem norm_two (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have : (2 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) := by norm_num
  rw [this, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2

private theorem toQ_single (i : Fin n) : toQ (Pi.single i (1 : ℤ_[p])) = Pi.single i 1 := by
  funext j
  by_cases h : j = i <;> simp [toQ, h]

private theorem norm_sub3 (a b c : ℚ_[p]) (C : ℝ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) :
    ‖a - b - c‖ ≤ C := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le ha ?_)) ?_)
  · rwa [norm_neg]
  · rwa [norm_neg]

private theorem entry_bound(hp2 : p ≠ 2) (G : Matrix (Fin n) (Fin n) ℚ_[p]) (hG : Gᵀ = G) {C : ℝ}
    (hmax : ∀ a, ‖qf G (toQ a)‖ ≤ C) (i j : Fin n) : ‖G i j‖ ≤ C := by
  have hs : G j i = G i j := by simpa using congrFun (congrFun hG i) j
  have hqi : qf G (toQ (Pi.single i 1)) = G i i := by
    simp [toQ_single, qf, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hqj : qf G (toQ (Pi.single j 1)) = G j j := by
    simp [toQ_single, qf, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hb : bil G (toQ (Pi.single i (1 : ℤ_[p]))) (toQ (Pi.single j (1 : ℤ_[p]))) = 2 * G i j := by
    simp only [toQ_single, bil, Matrix.mulVec, dotProduct, Pi.single_apply]
    simp [hs]
    ring
  have hadd : toQ (Pi.single i (1 : ℤ_[p]) + Pi.single j 1) =
      toQ (Pi.single i (1 : ℤ_[p])) + toQ (Pi.single j 1) := by
    funext k; simp [toQ]
  have h2 : 2 * G i j = qf G (toQ (Pi.single i (1 : ℤ_[p]) + Pi.single j 1)) - qf G (toQ (Pi.single i 1)) -
      qf G (toQ (Pi.single j 1)) := by
    rw [hadd, qf_add, ← hb]; ring
  have := norm_sub3 (qf G (toQ (Pi.single i (1 : ℤ_[p]) + Pi.single j 1))) (qf G (toQ (Pi.single i 1)))
    (qf G (toQ (Pi.single j 1))) C (hmax _) (hmax _) (hmax _)
  rw [← h2, norm_mul, norm_two hp2, one_mul] at this
  exact this

private theorem split_step (hp2 : p ≠ 2) (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ_[p]) (hG : Gᵀ = G)
    (hmax : ∀ a, ‖qf G (toQ a)‖ ≤ ‖G 0 0‖) (hdet : G.det ≠ 0) :
    G 0 0 ≠ 0 ∧ ∃ G' : Matrix (Fin n) (Fin n) ℚ_[p], G'ᵀ = G' ∧ G'.det ≠ 0 ∧ ZpEquiv G (blk (G 0 0) G') ∧
      ∀ a, ‖qf G' (toQ a)‖ ≤ ‖G 0 0‖ := by
  have hb := entry_bound hp2 G hG hmax
  have g0ne : G 0 0 ≠ 0 := by
    intro h0
    apply hdet
    have : G = 0 := by
      ext i j
      have := hb i j
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.1 this
    rw [this]
    exact Matrix.det_zero
  refine ⟨g0ne, ?_⟩
  have hcb : ∀ j : Fin n, ‖-(G 0 j.succ / G 0 0)‖ ≤ 1 := by
    intro j
    rw [norm_neg, norm_div, div_le_one (norm_pos_iff.2 g0ne)]
    exact hb 0 j.succ
  set c : Fin n → ℤ_[p] := fun j => ⟨-(G 0 j.succ / G 0 0), hcb j⟩ with hc
  set s : Fin (n + 1) → ℤ_[p] := Fin.cons 0 c with hs
  have hs0 : s 0 = 0 := by simp [hs]
  set E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p] := Matrix.of fun i j => if i = 0 then s j else 0 with hE
  have hEE : E * E = 0 := by
    ext i j
    by_cases hi : i = 0 <;> simp [hE, Matrix.mul_apply, hi, hs0]
  have hS : IsUnit (1 + E) := by
    refine ⟨⟨1 + E, 1 - E, ?_, ?_⟩, rfl⟩
    · calc (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
        _ = 1 := by rw [hEE, sub_zero]
    · calc (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
        _ = 1 := by rw [hEE, sub_zero]
  set Sq : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ_[p] := (1 + E).map PadicInt.Coe.ringHom with hSq
  have hSqa : ∀ b j, Sq b j = (if b = j then 1 else 0) + (if b = 0 then ((s j : ℤ_[p]) : ℚ_[p]) else 0) := by
    intro b j
    by_cases hb0 : b = 0 <;> by_cases hbj : b = j <;> simp [hSq, hE, Matrix.one_apply, hb0, hbj] <;>
      split_ifs <;> simp
  set H := Sqᵀ * G * Sq with hH
  have hrow : ∀ b, (Sqᵀ * G) 0 b = G 0 b := by
    intro b
    simp [Matrix.mul_apply, hSqa, hs0]
  have hH0 : ∀ j, H 0 j = G 0 j + G 0 0 * ((s j : ℤ_[p]) : ℚ_[p]) := by
    intro j
    simp [hH, Matrix.mul_apply, hrow, hSqa, mul_add, Finset.sum_add_distrib]
  have hHs : Hᵀ = H := by
    simp [hH, Matrix.transpose_mul, hG, Matrix.mul_assoc]
  have hH00 : H 0 0 = G 0 0 := by
    rw [hH0]; simp [hs0]
  have hH0s : ∀ j : Fin n, H 0 j.succ = 0 := by
    intro j
    rw [hH0]
    have : s j.succ = c j := by simp [hs]
    rw [this]
    simp only [hc]
    field_simp
    ring
  have hHblk : H = blk (G 0 0) (H.submatrix Fin.succ Fin.succ) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blk, hH00]
    · simp [blk, hH0s]
    · have := hH0s i
      have h2 : H i.succ 0 = H 0 i.succ := by simpa using congrFun (congrFun hHs 0) i.succ
      simp [blk, h2, this]
    · simp [blk]
  have hzp : ZpEquiv G H := zpEquiv_of_isUnit (1 + E) hS rfl
  refine ⟨H.submatrix Fin.succ Fin.succ, ?_, ?_, ?_, ?_⟩
  · ext i j
    simpa using congrFun (congrFun hHs i.succ) j.succ
  · have hd := hzp.det_ne hdet
    rw [hHblk, blk_det] at hd
    exact right_ne_zero_of_mul hd
  · rw [← hHblk]; exact hzp
  · intro a
    have h1 : qf (H.submatrix Fin.succ Fin.succ) (toQ a) = qf H (toQ (Fin.cons 0 a : Fin (n + 1) → ℤ_[p])) := by
      rw [toQ_cons]
      conv_rhs => rw [hHblk]
      rw [qf_blk]; simp
    rw [h1, hH]
    rw [qf_conj]
    exact hmax _

/-! ### Merging a unit into a block -/

private theorem merge (hp2 : p ≠ 2) (e : ℤ) (u s t : ℚ_[p]) (hu : ‖u‖ = 1) (hs : ‖s‖ = 1) (w : ℤ_[p])
    (hw : IsUnit w) (hts : t = ((w : ℤ_[p]) : ℚ_[p]) ^ 2 * (u * s)) (rest : List ℚ_[p]) :
    ∀ k : ℕ, LEq ((p : ℚ_[p]) ^ e * u :: (List.replicate k ((p : ℚ_[p]) ^ e) ++ ((p : ℚ_[p]) ^ e * s) :: rest))
      (List.replicate (k + 1) ((p : ℚ_[p]) ^ e) ++ ((p : ℚ_[p]) ^ e * t) :: rest) := by
  intro k
  induction k with
  | zero =>
    have h1 := LEq.rot hp2 ((p : ℚ_[p]) ^ e) u s hu hs rest
    have h2 := (LEq.scale w hw ((p : ℚ_[p]) ^ e * (u * s)) rest).cons ((p : ℚ_[p]) ^ e)
    have e2 : ((w : ℤ_[p]) : ℚ_[p]) ^ 2 * ((p : ℚ_[p]) ^ e * (u * s)) = (p : ℚ_[p]) ^ e * t := by
      rw [hts]; ring
    rw [e2] at h2
    simpa using h1.trans h2
  | succ k ih =>
    have h1 := LEq.rot hp2 ((p : ℚ_[p]) ^ e) u 1 hu (by simp)
      (List.replicate k ((p : ℚ_[p]) ^ e) ++ ((p : ℚ_[p]) ^ e * s) :: rest)
    simp only [mul_one] at h1
    have h2 := ih.cons ((p : ℚ_[p]) ^ e)
    have := h1.trans h2
    simpa [List.replicate_succ] using this

private theorem LEq.symm {L L' : List ℚ_[p]} (h : LEq L L') : LEq L' L :=
  ⟨h.1.symm, fun m h1 h2 => (h.2 m h2 h1).symm⟩

private theorem sq_class' (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r) (u : ℚ_[p])
    (hu : ‖u‖ = 1) : ∃ (ε : Fin 2) (w : ℤ_[p]), IsUnit w ∧ r ^ (ε : ℕ) = ((w : ℤ_[p]) : ℚ_[p]) ^ 2 * u := by
  obtain ⟨ε, w, hw, h⟩ := sq_class hp2 hr1 hr u hu
  obtain ⟨v, rfl⟩ := hw
  refine ⟨ε, ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), Units.isUnit _, ?_⟩
  have h1 : (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, Units.inv_mul]; simp
  rw [h]
  linear_combination (-(r ^ (ε : ℕ)) * (1 + (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * ((v : ℤ_[p]) : ℚ_[p]))) * h1

private theorem canonEntries_cons (r : ℚ_[p]) (b : CanonBlock) (D : List CanonBlock) :
    canonEntries p r (b :: D) = List.replicate (b.m - 1) ((p : ℚ_[p]) ^ b.e) ++
      ((p : ℚ_[p]) ^ b.e * r ^ (b.ε : ℕ)) :: canonEntries p r D := by
  simp [canonEntries]

private theorem qf_single_val (G : Matrix (Fin n) (Fin n) ℚ_[p]) (i : Fin n) :
    qf G (toQ (Pi.single i (1 : ℤ_[p]))) = G i i := by
  simp [toQ_single, qf, Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem norm_pe_mul {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (e : ℤ) (j : ℕ) :
    ‖(p : ℚ_[p]) ^ e * r ^ j‖ = (p : ℝ) ^ (-e) := by
  rw [norm_mul, Padic.norm_p_zpow, norm_pow, hr1, one_pow, mul_one]

/-! ### The induction -/

private theorem main_claim (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r) :
    ∀ n : ℕ, ∀ F : Matrix (Fin n) (Fin n) ℚ_[p], Fᵀ = F → F.det ≠ 0 →
      ∃ D : List CanonBlock, IsCanon D ∧ ∃ h : (canonEntries p r D).length = n,
        ZpEquiv F (dg' (canonEntries p r D) n h) ∧
        ∀ C : ℝ, (∀ a, ‖qf F (toQ a)‖ ≤ C) → ∀ x ∈ canonEntries p r D, ‖x‖ ≤ C := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  intro n
  induction n with
  | zero =>
    intro F _ _
    exact ⟨[], by simp [IsCanon], by simp [canonEntries], ⟨1, Subsingleton.elim _ _⟩, by simp [canonEntries]⟩
  | succ n ih =>
    intro F hF hdet
    obtain ⟨T, hT⟩ := exists_equiv_sup_first (Nat.succ_pos n) F
    set G := (T.val.map PadicInt.Coe.ringHom)ᵀ * F * T.val.map PadicInt.Coe.ringHom with hGdef
    have hFG : ZpEquiv F G := ⟨T, rfl⟩
    have hGs : Gᵀ = G := by simp [hGdef, Matrix.transpose_mul, hF, Matrix.mul_assoc]
    have hGdet := hFG.det_ne hdet
    have h00 : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    have hmaxG : ∀ a, ‖qf G (toQ a)‖ ≤ ‖G 0 0‖ := by
      intro a
      have := hT a
      rw [qf_single_val, h00] at this
      exact this
    obtain ⟨g0ne, G', hG's, hG'det, hzp, hbd⟩ := split_step hp2 G hGs hmaxG hGdet
    obtain ⟨D', hD', h', hzp', hbd'⟩ := ih G' hG's hG'det
    have hE' : ∀ x ∈ canonEntries p r D', ‖x‖ ≤ ‖G 0 0‖ := hbd' _ hbd
    set g0 := G 0 0 with hg0
    set e := g0.valuation with he
    have hne : ‖g0‖ = (p : ℝ) ^ (-e) := Padic.norm_eq_zpow_neg_valuation g0ne
    have hpe : ‖(p : ℚ_[p]) ^ e‖ = (p : ℝ) ^ (-e) := Padic.norm_p_zpow e
    have hpe0 : (p : ℚ_[p]) ^ e ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    set u := g0 / (p : ℚ_[p]) ^ e with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_div, hne, hpe, div_self (zpow_ne_zero _ (by positivity))]
    obtain ⟨ε, w, hw, hwu⟩ := sq_class hp2 hr1 hr u hu
    set g0' := (p : ℚ_[p]) ^ e * r ^ (ε : ℕ) with hg0'
    have hg0eq : g0 = ((w : ℤ_[p]) : ℚ_[p]) ^ 2 * g0' := by
      have : g0 = (p : ℚ_[p]) ^ e * u := by rw [hu_def]; field_simp
      rw [this, hwu, hg0']; ring
    have hnorm0' : ‖g0'‖ = ‖g0‖ := by rw [hg0', norm_pe_mul hr1, hne]
    have hF1 : ZpEquiv F (blk g0' (dg' (canonEntries p r D') n h')) := by
      have h3 : ZpEquiv (blk g0 G') (blk g0' G') := by
        have := zp_scale w hw g0' G'
        rw [← hg0eq] at this
        exact this.symm
      exact hFG.trans (hzp.trans (h3.trans (zp_cons g0' hzp')))
    have hlen : (g0' :: canonEntries p r D').length = n + 1 := by simp [h']
    have hF2 : ZpEquiv F (dg' (g0' :: canonEntries p r D') (n + 1) hlen) := by
      rw [dg'_cons]; exact hF1
    have hC' : ∀ C : ℝ, (∀ a, ‖qf F (toQ a)‖ ≤ C) → ‖g0‖ ≤ C := by
      intro C hC
      have := hC (T.val *ᵥ Pi.single 0 1)
      rw [← qf_conj, qf_single_val] at this
      exact this
    have key : ∃ D, IsCanon D ∧ LEq (g0' :: canonEntries p r D') (canonEntries p r D) ∧
        ∀ x ∈ canonEntries p r D, ‖x‖ ≤ ‖g0‖ := by
      rcases D' with _ | ⟨b, D''⟩
      · refine ⟨[⟨e, ε, 1⟩], by simp [IsCanon], ?_, ?_⟩
        · have : canonEntries p r [⟨e, ε, 1⟩] = g0' :: canonEntries p r [] := by simp [canonEntries, g0']
          rw [this]; exact LEq.refl _
        · intro x hx
          simp only [canonEntries, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.sub_self,
            List.replicate_zero, List.nil_append, List.mem_singleton] at hx
          rw [hx, norm_pe_mul hr1, hne]
      · obtain ⟨eb, εb, m⟩ := b
        have hm1 : 1 ≤ m := hD'.2 _ (List.mem_cons_self)
        rcases lt_trichotomy e eb with hlt | heq | hgt
        · refine ⟨⟨e, ε, 1⟩ :: ⟨eb, εb, m⟩ :: D'', ⟨List.isChain_cons_cons.2 ⟨hlt, hD'.1⟩, ?_⟩, ?_, ?_⟩
          · intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · exact le_rfl
            · exact hD'.2 c hc
          · have : canonEntries p r (⟨e, ε, 1⟩ :: ⟨eb, εb, m⟩ :: D'') =
                g0' :: canonEntries p r (⟨eb, εb, m⟩ :: D'') := by
              rw [canonEntries_cons (b := ⟨e, ε, 1⟩)]; simp [g0']
            rw [this]; exact LEq.refl _
          · intro x hx
            rw [canonEntries_cons (b := ⟨e, ε, 1⟩)] at hx
            simp only [Nat.sub_self, List.replicate_zero, List.nil_append, List.mem_cons] at hx
            rcases hx with hx | hx
            · rw [hx, norm_pe_mul hr1, hne]
            · exact hE' x hx
        · subst heq
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
          have hu1 : ‖r ^ (ε : ℕ)‖ = 1 := by rw [norm_pow, hr1, one_pow]
          have hs1 : ‖r ^ (εb : ℕ)‖ = 1 := by rw [norm_pow, hr1, one_pow]
          obtain ⟨ε'', w'', hw'', hrw⟩ :=
            sq_class' hp2 hr1 hr (r ^ (ε : ℕ) * r ^ (εb : ℕ)) (by rw [norm_mul, hu1, hs1, mul_one])
          have hmerge := merge hp2 e (r ^ (ε : ℕ)) (r ^ (εb : ℕ)) (r ^ (ε'' : ℕ)) hu1 hs1 w'' hw'' hrw
            (canonEntries p r D'') k
          have e1 : canonEntries p r (⟨e, ε'', k + 2⟩ :: D'') = List.replicate (k + 1) ((p : ℚ_[p]) ^ e) ++
              ((p : ℚ_[p]) ^ e * r ^ (ε'' : ℕ)) :: canonEntries p r D'' := by
            rw [canonEntries_cons]; simp
          have e2 : canonEntries p r (⟨e, εb, k + 1⟩ :: D'') = List.replicate k ((p : ℚ_[p]) ^ e) ++
              ((p : ℚ_[p]) ^ e * r ^ (εb : ℕ)) :: canonEntries p r D'' := by
            rw [canonEntries_cons]; simp
          have hch : List.IsChain (fun a b : CanonBlock => a.e < b.e) (⟨e, ε'', k + 2⟩ :: D'') := by
            rcases D'' with _ | ⟨c, l⟩
            · exact List.isChain_singleton _
            · exact List.isChain_cons_cons.2 (List.isChain_cons_cons.1 hD'.1)
          refine ⟨⟨e, ε'', k + 2⟩ :: D'', ⟨hch, ?_⟩, ?_, ?_⟩
          · intro c hc
            rcases List.mem_cons.1 hc with rfl | hc
            · show 1 ≤ k + 2
              omega
            · exact hD'.2 c (List.mem_cons_of_mem _ hc)
          · rw [e1, e2]
            exact hmerge
          · intro x hx
            rw [e1, List.mem_append] at hx
            rcases hx with hx | hx
            · rw [List.eq_of_mem_replicate hx, Padic.norm_p_zpow, hne]
            · rcases List.mem_cons.1 hx with hx | hx
              · rw [hx, norm_pe_mul hr1, hne]
              · refine hE' x ?_
                rw [e2]
                exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
        · exfalso
          have hmem : (p : ℚ_[p]) ^ eb * r ^ (εb : ℕ) ∈ canonEntries p r (⟨eb, εb, m⟩ :: D'') := by
            rw [canonEntries_cons]; simp
          have := hE' _ hmem
          rw [norm_pe_mul hr1, hne] at this
          have := (zpow_le_zpow_iff_right₀ hp1).1 this
          omega
    obtain ⟨D, hD, hL, hall⟩ := key
    have hlenD : (canonEntries p r D).length = n + 1 := hL.1.symm.trans hlen
    exact ⟨D, hD, hlenD, hF2.trans (hL.2 (n + 1) hlen hlenD), fun C hC x hx => (hall x hx).trans (hC' C hC)⟩

/-- **Cassels, Ch. 8, Theorem 3.1, existence** ($p \ne 2$): every non-singular form is $\mathbb Z_p$-equivalent to a
canonical form (3.11). -/
@[kb "cassels1978" "Ch. 8, Thm. 3.1, pp. 115–117 (existence)"]
theorem exists_canonical (hp2 : p ≠ 2) {r : ℚ_[p]} (hr1 : ‖r‖ = 1) (hr : ¬ IsSquare r)
    (F : Matrix (Fin n) (Fin n) ℚ_[p]) (hF : Fᵀ = F) (hdet : F.det ≠ 0) :
    ∃ D : List CanonBlock, IsCanon D ∧ ∃ h : (canonEntries p r D).length = n, ZpEquiv F (canonMat r D h) := by
  obtain ⟨D, hD, h, hzp, -⟩ := main_claim hp2 hr1 hr n F hF hdet
  exact ⟨D, hD, h, hzp⟩

end QuadFormsKB.Cassels
