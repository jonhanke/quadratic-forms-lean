/-
# Cassels, Chapter 8, Lemma 5.2: congruent forms with the same determinant class, $p \ne 2$

**Setting** (as in `Ch8/Congruent.lean`): $F, G$ symmetric $n \times n$ matrices over $\mathbb Z_p$ (classically
integral forms $f, g$), $d = \det F \ne 0$, $\lvert d\rvert_p = p^{-\delta}$, i.e. $\delta = v_p(d)$ (Cassels' (5.1)).

**Proves** `exists_equiv_of_congr_det` (**Lemma 5.2**, p. 123, for $p \ne 2$): if $d(g) = du^{2}$ for a unit $u$
((5.6)) and $G \equiv F \pmod{p^{\delta}}$, then $f$ and $g$ are $\mathbb Z_p$-equivalent.

**The precision (5.7).** The machine-read text lost the exponent in Cassels' (5.7); the page image (read
2026-10-30) gives $g_{ij} \equiv f_{ij} \pmod{p^{\delta + 2\lambda}}$ ($\lambda = 1$ for $p = 2$, $0$ otherwise), which for
$p \ne 2$ is the precision $p^{\delta}$ used here (it is the weakest possible: for $p = 2$, congruence mod $2^{\delta + 1}$
is not enough, as $\langle 1, 1\rangle$ and $\langle 3, 3\rangle$ show). For $p = 2$ Cassels gives no proof ("somewhat
more difficult"); the lemma for every $p$, including $p = 2$, is `exists_equiv_of_congr_det_all` in
`Ch8/Lemma52.lean`.

**Proof** (Cassels: "almost immediate for $p \ne 2$" from the canonical form): by induction on $n$, after a
$\mathbb Z_p$-equivalence making $F$ diagonal with $\lvert F_{00}\rvert = \max\lvert F_{ij}\rvert$: if $\delta = 0$ both forms
are unimodular with determinants differing by a unit square (Corollary to Theorem 3.1); otherwise $G_{00}$ has the same
absolute value as $F_{00}$ and dominates its row, completing the square splits off $\langle G_{00}\rangle$ with
$G_{00}/F_{00} \equiv 1 \pmod p$ a square, and the complements are congruent modulo $p^{\delta}$, a power at least
$p^{\delta - v(F_{00})}$.
-/
import QuadFormsKB.Literature.Cassels.Ch8.Congruent
import QuadFormsKB.Literature.Cassels.Ch8.Canonical
import QuadFormsKB.Lattices.UnimodularDVR
import QuadFormsKB.Literature.LocalGlobal.HilbertLocal

namespace QuadFormsKB.Cassels

open Matrix

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-! ### Integral equivalence -/

/-- Equivalence over $\mathbb Z_p$ of symmetric matrices over $\mathbb Z_p$: $G = T^{t}FT$, $T \in \mathrm{GL}_n(\mathbb Z_p)$. -/
private def IEq (F G : Matrix (Fin n) (Fin n) ℤ_[p]) : Prop := ∃ T : GL (Fin n) ℤ_[p], (T.val)ᵀ * F * T.val = G

private theorem IEq.refl (F : Matrix (Fin n) (Fin n) ℤ_[p]) : IEq F F := ⟨1, by simp⟩

private theorem IEq.symm {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (h : IEq F G) : IEq G F := by
  obtain ⟨T, rfl⟩ := h
  refine ⟨T⁻¹, ?_⟩
  have hM : T.val * (T⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc _ = (T.val * (T⁻¹).val)ᵀ * F * (T.val * (T⁻¹).val) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = F := by rw [hM]; simp

private theorem IEq.trans {F G H : Matrix (Fin n) (Fin n) ℤ_[p]} (h₁ : IEq F G) (h₂ : IEq G H) : IEq F H := by
  obtain ⟨T, rfl⟩ := h₁
  obtain ⟨S, rfl⟩ := h₂
  refine ⟨T * S, ?_⟩
  rw [Units.val_mul]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

private theorem IEq.of_isUnit {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (T : Matrix (Fin n) (Fin n) ℤ_[p])
    (hT : IsUnit T) (h : Tᵀ * F * T = G) : IEq F G := by
  obtain ⟨u, rfl⟩ := hT
  exact ⟨u, h⟩

private theorem IEq.det {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (h : IEq F G) :
    ∃ e : ℤ_[p], IsUnit e ∧ G.det = F.det * e ^ 2 := by
  obtain ⟨T, rfl⟩ := h
  refine ⟨T.val.det, (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

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

private theorem blk_one {R : Type*} [Semiring R] : blk (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [blk, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private theorem blk_det {R : Type*} [CommRing R] (a : R) (A : Matrix (Fin n) (Fin n) R) :
    (blk a A).det = a * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blk]
  congr 2

private theorem isUnit_blk {a : ℤ_[p]} (ha : IsUnit a) {A : Matrix (Fin n) (Fin n) ℤ_[p]} (hA : IsUnit A) :
    IsUnit (blk a A) := by
  obtain ⟨u, rfl⟩ := hA
  obtain ⟨v, rfl⟩ := ha
  exact ⟨⟨blk (v : ℤ_[p]) (u : Matrix (Fin n) (Fin n) ℤ_[p]),
    blk ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) ((u⁻¹ : (Matrix (Fin n) (Fin n) ℤ_[p])ˣ) : Matrix (Fin n) (Fin n) ℤ_[p]),
    by rw [blk_mul, Units.mul_inv, Units.mul_inv, blk_one], by rw [blk_mul, Units.inv_mul, Units.inv_mul, blk_one]⟩,
    rfl⟩

private theorem IEq.cons (a : ℤ_[p]) {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (h : IEq F G) :
    IEq (blk a F) (blk a G) := by
  obtain ⟨T, hT⟩ := h
  refine IEq.of_isUnit (blk 1 T.val) (isUnit_blk isUnit_one T.isUnit) ?_
  rw [blk_transpose, blk_mul, blk_mul, hT]
  simp

private theorem IEq.scale (w : ℤ_[p]) (hw : IsUnit w) (a : ℤ_[p]) (G : Matrix (Fin n) (Fin n) ℤ_[p]) :
    IEq (blk a G) (blk (w ^ 2 * a) G) := by
  refine IEq.of_isUnit (blk w 1) (isUnit_blk hw isUnit_one) ?_
  rw [blk_transpose, blk_mul, blk_mul]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ring

/-! ### Valuations -/

private theorem valuation_unit {e : ℤ_[p]} (he : IsUnit e) : e.valuation = 0 := by
  have h0 : e ≠ 0 := he.ne_zero
  have h1 := PadicInt.norm_eq_zpow_neg_valuation h0
  rw [PadicInt.isUnit_iff.1 he] at h1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have := (zpow_eq_one_iff_right₀ (by positivity) hp1.ne').1 h1.symm
  omega

private theorem valuation_mul_unit_sq {d e : ℤ_[p]} (hd : d ≠ 0) (he : IsUnit e) :
    (d * e ^ 2).valuation = d.valuation := by
  rw [PadicInt.valuation_mul hd (pow_ne_zero 2 he.ne_zero), PadicInt.valuation_pow, valuation_unit he]
  simp

/-! ### The unimodular case -/

private theorem unimodular_case (hp2 : p ≠ 2) {F G : Matrix (Fin n) (Fin n) ℤ_[p]} (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hu : IsUnit F.det) {s : ℤ_[p]} (hs : IsUnit s) (hdet : G.det = F.det * s ^ 2) : IEq F G := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField ℤ_[p]) :=
    Fintype.ofEquiv (ZMod p) PadicInt.residueField.symm.toEquiv
  have h2A : ((2 : ℤ_[p]) • F)ᵀ = (2 : ℤ_[p]) • F := by rw [transpose_smul, hF]
  have h2B : ((2 : ℤ_[p]) • G)ᵀ = (2 : ℤ_[p]) • G := by rw [transpose_smul, hG]
  set Q : QuadForm ℤ_[p] n := QuadForm.ofUpper fun i j => if i = j then F i i else (2 : ℤ_[p]) * F i j
  set Q' : QuadForm ℤ_[p] n := QuadForm.ofUpper fun i j => if i = j then G i i else (2 : ℤ_[p]) * G i j
  have hess : ∀ (M : Matrix (Fin n) (Fin n) ℤ_[p]), Mᵀ = M →
      (QuadForm.ofUpper fun i j => if i = j then M i i else (2 : ℤ_[p]) * M i j).hessian = (2 : ℤ_[p]) • M := by
    intro M hM
    ext i j
    simp only [QuadForm.hessian, QuadForm.ofUpper, Matrix.add_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [hij.le, hij.ne, not_le.2 hij]
    · simp [two_mul]
    · simp only [not_le.2 hij, hij.le, ite_false, ite_true, hij.ne, hij.ne', zero_add]
      rw [← transpose_apply M i j, hM]
  have hQ : Q.hessian = (2 : ℤ_[p]) • F := hess F hF
  have hQ' : Q'.hessian = (2 : ℤ_[p]) • G := hess G hG
  have h2u : IsUnit (2 : ℤ_[p]) :=
    (PadicInt.isUnit_iff.2 (by
      have : ¬ (p : ℤ_[p]) ∣ 2 := Siegel.Kneser.not_p_dvd_two hp2
      rw [← PadicInt.norm_lt_one_iff_dvd] at this
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)))
  have hunit : IsUnit ((2 : ℤ_[p]) • F).det := by
    rw [det_smul]; exact (h2u.pow _).mul hu
  have hnd : ¬ (p : ℤ_[p]) ∣ Q.hessian.det := by
    rw [hQ]
    intro hd
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_unit hd hunit)
  have hiso := Lattices.Nbr.isometricGL_of_unimodular_dvr PadicInt.irreducible_p (Siegel.Kneser.not_p_dvd_two hp2)
    Q Q' hnd hs (by rw [hQ, hQ', det_smul, det_smul, hdet]; ring)
  obtain ⟨g, hg⟩ := hiso
  have hH := Lattices.Nbr.hessian_eq_of_eval' (Q := Q) (Q' := Q') (U := g.val) (fun x => (hg x).symm)
  rw [hQ, hQ', Matrix.mul_smul, Matrix.smul_mul] at hH
  refine ⟨g, Matrix.ext fun i j => ?_⟩
  have := congrFun (congrFun hH i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_left_cancel₀ (two_ne_zero : (2 : ℤ_[p]) ≠ 0) this).symm

/-! ### Splitting off the corner -/

/-- The unipotent matrix with first row $(1, c)$. -/
private noncomputable def Sg (c : Fin n → ℤ_[p]) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p] :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun j' => c j') j) (fun i' => Fin.cases 0 (fun j' => if i' = j' then 1 else 0) j) i

private theorem Sg_mul (c c' : Fin n → ℤ_[p]) : Sg c * Sg c' = Sg (c + c') := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Sg, Matrix.mul_apply, Fin.sum_univ_succ] <;> try ring

private theorem Sg_zero : Sg (0 : Fin n → ℤ_[p]) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Sg, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

private theorem isUnit_Sg (c : Fin n → ℤ_[p]) : IsUnit (Sg c) :=
  ⟨⟨Sg c, Sg (-c), by rw [Sg_mul, add_neg_cancel, Sg_zero], by rw [Sg_mul, neg_add_cancel, Sg_zero]⟩, rfl⟩

private theorem split_eq (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (hF : Fᵀ = F) (c : Fin n → ℤ_[p])
    (hc : ∀ j, F 0 j.succ = F 0 0 * c j) :
    (Sg (-c))ᵀ * F * Sg (-c) = blk (F 0 0) (Matrix.of fun i j => F i.succ j.succ - F 0 0 * c i * c j) := by
  have hs : ∀ i j, F i j = F j i := fun i j => by simpa using congrFun (congrFun hF j) i
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [Sg, blk, Matrix.mul_apply, Fin.sum_univ_succ, hc]
  · simp [Sg, blk, Matrix.mul_apply, Fin.sum_univ_succ, hc]
  · simp [Sg, blk, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs _ 0]
    ring
  · simp [Sg, blk, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs _ 0]
    ring

private theorem Sg_det (c : Fin n → ℤ_[p]) : (Sg c).det = 1 := by
  have h : (Sg c).BlockTriangular id := by
    intro i j hij
    induction i using Fin.cases with
    | zero => exact absurd hij (Fin.not_lt_zero _)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [Sg]
      | succ j =>
        have hlt : j < i := Fin.succ_lt_succ_iff.1 hij
        simp [Sg, hlt.ne']
  rw [Matrix.det_of_isUpperTriangular h]
  refine Finset.prod_eq_one fun i _ => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [Sg]

private theorem split_int' (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (hF : Fᵀ = F) (c : Fin n → ℤ_[p])
    (hc : ∀ j, F 0 j.succ = F 0 0 * c j) :
    IEq F (blk (F 0 0) (Matrix.of fun i j => F i.succ j.succ - F 0 0 * c i * c j)) ∧
      F.det = F 0 0 * (Matrix.of fun i j => F i.succ j.succ - F 0 0 * c i * c j).det := by
  have h := split_eq F hF c hc
  refine ⟨IEq.of_isUnit (Sg (-c)) (isUnit_Sg _) h, ?_⟩
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Sg_det, blk_det] at this
  simpa using this

/-! ### Auxiliary facts -/

/-- A unit congruent to $1$ modulo $p$ is a square ($p$ odd). -/
private theorem exists_sq_one_add (hp2 : p ≠ 2) (s : ℤ_[p]) : ∃ w : ℤ_[p], IsUnit w ∧ w ^ 2 = 1 + p * s := by
  have hru : IsUnit (1 + (p : ℤ_[p]) * s) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_)
    have hd : (p : ℤ_[p]) ∣ 1 + (p : ℤ_[p]) * s := (PadicInt.norm_lt_one_iff_dvd _).1 hlt
    have : (p : ℤ_[p]) ∣ 1 := by
      have := dvd_sub hd (dvd_mul_right (p : ℤ_[p]) s)
      simpa using this
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one this)
  have hres : PadicInt.toZMod ((hru.unit : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [IsUnit.unit_spec, map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
  obtain ⟨x, hx⟩ := (QuadFormsKB.HilbertLocal.isSquare_unit_iff hp2 hru.unit).2 ⟨1, by rw [hres]; simp⟩
  have hn1 : ‖(((1 + (p : ℤ_[p]) * s : ℤ_[p]) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
    rw [PadicInt.norm_coe]; exact PadicInt.isUnit_iff.1 hru
  rw [IsUnit.unit_spec] at hx
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_mul] at hn1
    nlinarith [norm_nonneg x]
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[p], (w : ℚ_[p]) = x := ⟨⟨x, hx1.le⟩, rfl⟩
  refine ⟨w, PadicInt.isUnit_iff.2 (by rw [← PadicInt.norm_coe, hw, hx1]), ?_⟩
  apply Subtype.ext
  have this : (((1 + (p : ℤ_[p]) * s : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = x * x := hx
  have h2 : ((w ^ 2 : ℤ_[p]) : ℚ_[p]) = x * x := by rw [PadicInt.coe_pow, hw, sq]
  exact h2.trans this.symm

/-- Conjugating a matrix with entries divisible by $p^k$ keeps the entries divisible by $p^k$. -/
private theorem dvd_conj {m : ℕ} (A M B : Matrix (Fin m) (Fin m) ℤ_[p]) (k : ℕ)
    (h : ∀ i j, (p : ℤ_[p]) ^ k ∣ M i j) : ∀ i j, (p : ℤ_[p]) ^ k ∣ (Aᵀ * M * B) i j := by
  choose N hN using h
  have : M = (p : ℤ_[p]) ^ k • Matrix.of N := by ext i j; simp [hN i j]
  intro i j
  rw [this, Matrix.mul_smul, Matrix.smul_mul]
  exact ⟨(Aᵀ * Matrix.of N * B) i j, by simp⟩

private theorem toQ_single (i : Fin n) : toQ (Pi.single i (1 : ℤ_[p])) = Pi.single i 1 := by
  funext j
  by_cases h : j = i <;> simp [toQ, h]

private theorem norm_two (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have : (2 : ℚ_[p]) = ((2 : ℕ) : ℚ_[p]) := by norm_num
  rw [this, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes hp.out Nat.prime_two).2 hp2

private theorem norm_sub3 (a b c : ℚ_[p]) (C : ℝ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) :
    ‖a - b - c‖ ≤ C := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le ha ?_)) ?_)
  · rwa [norm_neg]
  · rwa [norm_neg]

private theorem qf_single_val (G : Matrix (Fin n) (Fin n) ℚ_[p]) (i : Fin n) :
    qf G (toQ (Pi.single i (1 : ℤ_[p]))) = G i i := by
  simp [toQ_single, qf, Matrix.mulVec, dotProduct, Pi.single_apply]

private theorem entry_bound (hp2 : p ≠ 2) (G : Matrix (Fin n) (Fin n) ℚ_[p]) (hG : Gᵀ = G) {C : ℝ}
    (hmax : ∀ a, ‖qf G (toQ a)‖ ≤ C) (i j : Fin n) : ‖G i j‖ ≤ C := by
  have hs : G j i = G i j := by simpa using congrFun (congrFun hG i) j
  have hqi : qf G (toQ (Pi.single i 1)) = G i i := qf_single_val G i
  have hqj : qf G (toQ (Pi.single j 1)) = G j j := qf_single_val G j
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

/-- Lemma 3.1 for matrices over $\mathbb Z_p$: after a change of variables the corner entry has maximal absolute
value among all entries ($p$ odd). -/
private theorem exists_max_conj (hp2 : p ≠ 2) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (hF : Fᵀ = F) :
    ∃ T : GL (Fin (n + 1)) ℤ_[p],
      ∀ i j, ‖((T.val)ᵀ * F * T.val) i j‖ ≤ ‖((T.val)ᵀ * F * T.val) 0 0‖ := by
  obtain ⟨T, hT⟩ := exists_equiv_sup_first (Nat.succ_pos n) (F.map PadicInt.Coe.ringHom)
  refine ⟨T, fun i j => ?_⟩
  set F' := (T.val)ᵀ * F * T.val with hF'
  have hmap : (T.val.map PadicInt.Coe.ringHom)ᵀ * F.map PadicInt.Coe.ringHom * T.val.map PadicInt.Coe.ringHom =
      F'.map PadicInt.Coe.ringHom := by
    simp [hF', Matrix.map_mul, Matrix.transpose_map]
  rw [hmap] at hT
  have hsym : (F'.map PadicInt.Coe.ringHom)ᵀ = F'.map PadicInt.Coe.ringHom := by
    rw [← Matrix.transpose_map]
    congr 1
    simp [hF', Matrix.transpose_mul, hF, Matrix.mul_assoc]
  have h00 : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
  rw [qf_single_val, h00] at hT
  have := entry_bound hp2 _ hsym hT i j
  simpa [PadicInt.norm_coe] using this

/-! ### The inductive step -/

private def Claim (p : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  ∀ (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (k : ℕ), Fᵀ = F → Gᵀ = G → F.det ≠ 0 → ∀ {u : ℤ_[p]}, IsUnit u →
    G.det = F.det * u ^ 2 → F.det.valuation ≤ k → (∀ i j, (p : ℤ_[p]) ^ k ∣ F i j - G i j) → IEq F G

private theorem step (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) (ih : Claim p n)
    (F G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ_[p]) (k : ℕ) (hF : Fᵀ = F) (hG : Gᵀ = G) (hdet : F.det ≠ 0)
    {u : ℤ_[p]} (hu : IsUnit u) (hd : G.det = F.det * u ^ 2) (hk : F.det.valuation ≤ k)
    (hcong : ∀ i j, (p : ℤ_[p]) ^ k ∣ F i j - G i j) (hmax : ∀ i j, ‖F i j‖ ≤ ‖F 0 0‖)
    (hv : 0 < F.det.valuation) : IEq F G := by
  have ha : F 0 0 ≠ 0 := by
    intro h0
    apply hdet
    have : F = 0 := by
      ext i j
      have := hmax i j
      rw [h0, norm_zero] at this
      exact norm_le_zero_iff.1 this
    rw [this]
    exact Matrix.det_zero
  have hadvd : ∀ i j, F 0 0 ∣ F i j := fun i j => by
    obtain ⟨z, hz⟩ := padicInt_dvd_of_norm_le ha (hmax i j)
    exact ⟨z, hz⟩
  have hasp := PadicInt.unitCoeff_spec ha
  set a₀ : ℤ_[p]ˣ := PadicInt.unitCoeff ha with ha₀
  set e1 := (F 0 0).valuation with he1
  have hpe : (p : ℤ_[p]) ^ e1 ∣ F 0 0 := ⟨a₀, by rw [hasp]; ring⟩
  have hdetdvd : (p : ℤ_[p]) ^ ((n + 1) * e1) ∣ F.det := by
    choose M hM using fun i j => hpe.trans (hadvd i j)
    have : F = (p : ℤ_[p]) ^ e1 • Matrix.of M := by ext i j; simp [hM i j]
    rw [this, Matrix.det_smul, Fintype.card_fin, ← pow_mul, mul_comm e1]
    exact dvd_mul_right _ _
  have hle : (n + 1) * e1 ≤ F.det.valuation :=
    (PadicInt.mem_span_pow_iff_le_valuation _ hdet _).1 (Ideal.mem_span_singleton.2 hdetdvd)
  have he1k : e1 < k := by
    rcases Nat.eq_zero_or_pos e1 with h | h
    · omega
    · nlinarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt he1k
  choose c hc using fun j : Fin n => hadvd 0 j.succ
  -- the corner of G
  obtain ⟨t, ht⟩ := hcong 0 0
  obtain ⟨w, hw, hw2⟩ := exists_sq_one_add hp2
    (-((p : ℤ_[p]) ^ m * t * ((a₀⁻¹ : ℤ_[p]ˣ) : ℤ_[p])))
  have hai : (a₀ : ℤ_[p]) * ((a₀⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by simp
  have hb : G 0 0 = F 0 0 * w ^ 2 := by
    rw [hw2]
    rw [hm, pow_succ, pow_add] at ht
    rw [hasp] at ht ⊢
    linear_combination (-1 : ℤ_[p]) * ht + ((p : ℤ_[p]) ^ e1 * p * p ^ m * t) * hai
  have hk' : k = e1 + (m + 1) := by omega
  have hbne : G 0 0 ≠ 0 := by rw [hb]; exact mul_ne_zero ha (pow_ne_zero 2 hw.ne_zero)
  obtain ⟨winv, hwi⟩ : ∃ winv : ℤ_[p], w * winv = 1 := by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), by simp⟩
  have hwinv : IsUnit winv := ⟨⟨winv, w, by rw [mul_comm]; exact hwi, hwi⟩, rfl⟩
  have hapk : F 0 0 ∣ (p : ℤ_[p]) ^ k := by
    refine ⟨((a₀⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * p ^ (m + 1), ?_⟩
    rw [hk', pow_add]
    rw [hasp]
    linear_combination (-((p : ℤ_[p]) ^ e1 * p ^ (m + 1))) * hai
  have hadvdG : ∀ j : Fin n, F 0 0 ∣ G 0 j.succ := fun j => by
    have e : G 0 j.succ = F 0 j.succ - (F 0 j.succ - G 0 j.succ) := by ring
    rw [e]
    exact dvd_sub (hadvd 0 j.succ) (hapk.trans (hcong 0 j.succ))
  have hab : G 0 0 ∣ F 0 0 := ⟨winv ^ 2, by
    linear_combination (-(F 0 0) * (w * winv + 1)) * hwi + (-winv ^ 2) * hb⟩
  choose d hd' using fun j : Fin n => hab.trans (hadvdG j)
  obtain ⟨hFi, hFdet⟩ := split_int' F hF c hc
  obtain ⟨hGi, hGdet⟩ := split_int' G hG d hd'
  set F1 : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun i j => F i.succ j.succ - F 0 0 * c i * c j with hF1
  set G1 : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun i j => G i.succ j.succ - G 0 0 * d i * d j with hG1
  have hsF : ∀ i j, F i j = F j i := fun i j => by simpa using congrFun (congrFun hF j) i
  have hsG : ∀ i j, G i j = G j i := fun i j => by simpa using congrFun (congrFun hG j) i
  have hF1s : F1ᵀ = F1 := by
    ext i j
    simp only [Matrix.transpose_apply, hF1, Matrix.of_apply]
    rw [hsF i.succ j.succ]; ring
  have hG1s : G1ᵀ = G1 := by
    ext i j
    simp only [Matrix.transpose_apply, hG1, Matrix.of_apply]
    rw [hsG i.succ j.succ]; ring
  have hF1ne : F1.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hFdet
    exact hdet hFdet
  have h1 : F 0 0 * (w ^ 2 * G1.det) = F 0 0 * (F1.det * u ^ 2) := by
    have := hd
    rw [hGdet, hFdet, hb] at this
    linear_combination this
  have h2 := mul_left_cancel₀ ha h1
  have hdet1 : G1.det = F1.det * (u * winv) ^ 2 := by
    linear_combination (-(G1.det) * (w * winv + 1)) * hwi + winv ^ 2 * h2
  have hk1 : F1.det.valuation ≤ k := by
    have := PadicInt.valuation_mul ha hF1ne
    rw [← hFdet] at this
    omega
  have H1 : (p : ℤ_[p]) ^ k ∣ F 0 0 - G 0 0 := hcong 0 0
  have H2 : ∀ j : Fin n, (p : ℤ_[p]) ^ k ∣ F 0 0 * c j - G 0 0 * d j := fun j => by
    have := hcong 0 j.succ
    rwa [hc j, hd' j] at this
  have H3 : ∀ j : Fin n, (p : ℤ_[p]) ^ k ∣ F 0 0 * (d j - c j) := fun j => by
    have e : F 0 0 * (d j - c j) = (F 0 0 - G 0 0) * d j - (F 0 0 * c j - G 0 0 * d j) := by ring
    rw [e]
    exact dvd_sub (H1.mul_right _) (H2 j)
  have hcong1 : ∀ i j, (p : ℤ_[p]) ^ k ∣ F1 i j - G1 i j := fun i j => by
    have e : F1 i j - G1 i j = (F i.succ j.succ - G i.succ j.succ) - (F 0 0 - G 0 0) * d i * d j +
        d i * (F 0 0 * (d j - c j)) + c j * (F 0 0 * (d i - c i)) := by
      simp only [hF1, hG1, Matrix.of_apply]; ring
    rw [e]
    exact dvd_add (dvd_add (dvd_sub (hcong _ _) ((H1.mul_right _).mul_right _))
      (dvd_mul_of_dvd_right (H3 j) _)) (dvd_mul_of_dvd_right (H3 i) _)
  have v1 := ih F1 G1 k hF1s hG1s hF1ne (hu.mul hwinv) hdet1 hk1 hcong1
  have e1' : IEq (blk (F 0 0) F1) (blk (F 0 0) G1) := v1.cons _
  have e2 : IEq (blk (F 0 0) G1) (blk (G 0 0) G1) := by
    have := IEq.scale w hw (F 0 0) G1
    rw [hb, mul_comm (F 0 0)]
    exact this
  exact ((hFi.trans e1').trans e2).trans hGi.symm

/-! ### The induction -/

private theorem main_claim (hp2 : p ≠ 2) : ∀ n : ℕ, Claim p n := by
  intro n
  induction n with
  | zero => intro F G k hF hG hdet u hu hd hk hcong; exact ⟨1, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro F G k hF hG hdet u hu hd hk hcong
    by_cases hv : F.det.valuation = 0
    · have hunit : IsUnit F.det := by
        have h1 := PadicInt.norm_eq_zpow_neg_valuation hdet
        rw [hv] at h1
        exact PadicInt.isUnit_iff.2 (by simpa using h1)
      exact unimodular_case hp2 hF hG hunit hu hd
    · have hvpos : 0 < F.det.valuation := Nat.pos_of_ne_zero hv
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- one variable
        have hFd : F.det = F 0 0 := by simp [Matrix.det_unique]
        have hGd : G.det = G 0 0 := by simp [Matrix.det_unique]
        have hG00 : G 0 0 = F 0 0 * u ^ 2 := by rw [← hGd, hd, hFd]
        refine IEq.of_isUnit (Matrix.diagonal fun _ => u)
          ((Matrix.isUnit_iff_isUnit_det _).2 (by simpa [Matrix.det_diagonal] using hu)) ?_
        ext i j
        have hi : i = 0 := Fin.fin_one_eq_zero i
        have hj : j = 0 := Fin.fin_one_eq_zero j
        subst hi hj
        rw [hG00]
        simp [Matrix.mul_apply]
        ring
      · obtain ⟨T, hT⟩ := exists_max_conj hp2 F hF
        set F' := (T.val)ᵀ * F * T.val with hF'
        set G' := (T.val)ᵀ * G * T.val with hG'
        have heT : IsUnit T.val.det := (Matrix.isUnit_iff_isUnit_det _).1 T.isUnit
        have hF's : F'ᵀ = F' := by
          simp [hF', Matrix.transpose_mul, hF, Matrix.mul_assoc]
        have hG's : G'ᵀ = G' := by
          simp [hG', Matrix.transpose_mul, hG, Matrix.mul_assoc]
        have hdF : F'.det = F.det * T.val.det ^ 2 := by
          rw [hF', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
        have hdG : G'.det = G.det * T.val.det ^ 2 := by
          rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]; ring
        have hne : F'.det ≠ 0 := by
          rw [hdF]; exact mul_ne_zero hdet (pow_ne_zero 2 heT.ne_zero)
        have hval : F'.det.valuation = F.det.valuation := by
          rw [hdF]; exact valuation_mul_unit_sq hdet heT
        have hcong' : ∀ i j, (p : ℤ_[p]) ^ k ∣ F' i j - G' i j := by
          intro i j
          have e : F' - G' = (T.val)ᵀ * (F - G) * T.val := by
            rw [hF', hG', Matrix.mul_sub, Matrix.sub_mul]
          have := dvd_conj T.val (F - G) T.val k (fun i j => by simpa using hcong i j) i j
          rw [← e] at this
          simpa using this
        have hmain := step hp2 n hn ih F' G' k hF's hG's hne hu (by rw [hdG, hdF, hd]; ring)
          (by rw [hval]; exact hk) hcong' hT (by rw [hval]; exact hvpos)
        exact (show IEq F F' from ⟨T, rfl⟩).trans (hmain.trans (show IEq G G' from ⟨T, rfl⟩).symm)

/-- **Cassels, Ch. 8, Lemma 5.2** ($p \ne 2$): *let $f$ be a classically integral form with $d(f) = d \ne 0$,
$\lvert d\rvert = p^{-\delta}$, and let $g$ be another integral form. Suppose that $d(g) = du^{2}$ for some unit $u$ and
that $G \equiv F \pmod{p^{\delta}}$. Then $f$ and $g$ are $\mathbb Z_p$-equivalent.* For $p \ne 2$ the printed precision
(5.7), $p^{\delta + 2\lambda}$, is $p^{\delta}$ (see the module docstring; every $p$: `exists_equiv_of_congr_det_all`). Here $\delta$ is
`F.det.valuation`, congruence is entrywise divisibility of $F - G$, and the conclusion is $T^{t}FT = G$ with
$T \in \mathrm{GL}_n(\mathbb Z_p)$. -/
@[kb "cassels1978" "Ch. 8, Lemma 5.2, p. 123 (p ≠ 2)"]
theorem exists_equiv_of_congr_det (hp2 : p ≠ 2) (F G : Matrix (Fin n) (Fin n) ℤ_[p]) (hF : Fᵀ = F) (hG : Gᵀ = G)
    (hdet : F.det ≠ 0) {u : ℤ_[p]} (hu : IsUnit u) (hd : G.det = F.det * u ^ 2)
    (hcong : ∀ i j, (p : ℤ_[p]) ^ F.det.valuation ∣ F i j - G i j) :
    ∃ T : GL (Fin n) ℤ_[p], (T.val)ᵀ * F * T.val = G :=
  main_claim hp2 n F G _ hF hG hdet hu hd le_rfl hcong

end QuadFormsKB.Cassels
