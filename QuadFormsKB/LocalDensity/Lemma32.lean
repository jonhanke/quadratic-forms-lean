/-
# Local densities over a DVR: Lemma 3.2, Good-type solutions lift uniformly

**Layer:** DVR. **Proves** Hanke 2004, Lemma 3.2, eq. (3.1), p. 358 (`DVR.repCountGood_add`): for $Q$ in normal
form `IsJordanFormW Q π P w`, $e = \mathrm{ord}_\pi(2)$, $k \ge 2e + 1$ and $l \ge 0$,
$r^{\mathrm{Good}}_{\pi^{k+l}}(m) = q^{(n-1)l}\, r^{\mathrm{Good}}_{\pi^k}(m)$, Good type relative to $S_0 = \{i : w_i = 0\}$.
Valid at every prime with $2 \ne 0$. The count runs through classes mod $\pi^{K-v}$, $v \le e$ the gradient
valuation (not reduction mod $\pi^K$, whose fibres are not uniform at dyadic primes).
**Depends on** `Hensel.lean`.
-/
import QuadFormsKB.LocalDensity.Hensel

namespace QuadFormsKB.LocalDensity.DVR

open QuadForm Matrix

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-! ### Reduction and lifting of vectors -/

/-- Reduction of a vector of `R` mod `π ^ k`. -/
def redV (π : R) (k : ℕ) (x : Fin n → R) : Fin n → R ⧸ Ideal.span {π ^ k} :=
  fun i => Ideal.Quotient.mk _ (x i)

/-- A (chosen) lift of a vector mod `π ^ k` to `R`. -/
noncomputable def liftV (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) : Fin n → R :=
  fun i => Function.surjInv Ideal.Quotient.mk_surjective (x i)

theorem redV_liftV (π : R) (k : ℕ) (x : Fin n → R ⧸ Ideal.span {π ^ k}) :
    redV π k (liftV π k x) = x := by
  funext i
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective (x i)

theorem redV_eq_iff (π : R) (k : ℕ) (x y : Fin n → R) :
    redV π k x = redV π k y ↔ ∀ i, π ^ k ∣ x i - y i := by
  simp only [redV, funext_iff, Ideal.Quotient.eq, Ideal.mem_span_singleton]

theorem liftV_redV (π : R) (k : ℕ) (x : Fin n → R) :
    ∃ w : Fin n → R, liftV π k (redV π k x) = x + π ^ k • w := by
  have h : ∀ i, π ^ k ∣ liftV π k (redV π k x) i - x i :=
    (redV_eq_iff π k _ _).mp (redV_liftV π k _)
  refine ⟨fun i => Classical.choose (h i), funext fun i => ?_⟩
  have := Classical.choose_spec (h i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← this]; ring

/-- **Fibration lemma.** Let `P` be invariant under translation by `π ^ a R^n` and `P' → P` invariant
under `π ^ N R^n` (`N = a + b`). If, over every `c` with `P c`, the lifts `c + π ^ a y` (`y` mod `π ^ b`)
satisfying `P'` are in bijection with a fixed type `F`, then the classes mod `π ^ N` satisfying `P'` are
in bijection with (classes mod `π ^ a` satisfying `P`) `× F`. No finiteness is needed. -/
theorem fiber_equiv (π : R) (hπ : π ≠ 0) (a b N : ℕ) (hN : a + b = N)
    (P P' : (Fin n → R) → Prop) (F : Type*)
    (hP : ∀ x y, P x → P (x + π ^ a • y))
    (hP'P : ∀ x, P' x → P x)
    (hP' : ∀ x y, P' x → P' (x + π ^ N • y))
    (hF : ∀ c, P c → Nonempty ({y : Fin n → R ⧸ Ideal.span {π ^ b} //
      P' (c + π ^ a • liftV π b y)} ≃ F)) :
    Nonempty ({x : Fin n → R ⧸ Ideal.span {π ^ N} // P' (liftV π N x)} ≃
      {c : Fin n → R ⧸ Ideal.span {π ^ a} // P (liftV π a c)} × F) := by
  classical
  have hpa : π ^ a ≠ 0 := pow_ne_zero _ hπ
  have hNab : π ^ N = π ^ a * π ^ b := by rw [← hN, pow_add]
  let φ : {x : Fin n → R ⧸ Ideal.span {π ^ N} // P' (liftV π N x)} →
      {c : Fin n → R ⧸ Ideal.span {π ^ a} // P (liftV π a c)} := fun x =>
    ⟨redV π a (liftV π N x.1), by
      obtain ⟨w, hw⟩ := liftV_redV π a (liftV π N x.1)
      rw [hw]; exact hP _ _ (hP'P _ x.2)⟩
  -- the fibre of `φ` over `c`
  have hfib : ∀ c : {c : Fin n → R ⧸ Ideal.span {π ^ a} // P (liftV π a c)},
      Nonempty ({x // φ x = c} ≃
        {y : Fin n → R ⧸ Ideal.span {π ^ b} // P' (liftV π a c.1 + π ^ a • liftV π b y)}) := by
    intro c
    let ψ : {y : Fin n → R ⧸ Ideal.span {π ^ b} // P' (liftV π a c.1 + π ^ a • liftV π b y)} →
        {x // φ x = c} := fun y =>
      ⟨⟨redV π N (liftV π a c.1 + π ^ a • liftV π b y.1), by
        obtain ⟨w, hw⟩ := liftV_redV π N (liftV π a c.1 + π ^ a • liftV π b y.1)
        rw [hw]; exact hP' _ _ y.2⟩, by
        apply Subtype.ext
        show redV π a (liftV π N (redV π N _)) = c.1
        obtain ⟨w, hw⟩ := liftV_redV π N (liftV π a c.1 + π ^ a • liftV π b y.1)
        rw [hw]
        refine Eq.trans ((redV_eq_iff π a _ (liftV π a c.1)).mpr fun i => ?_) (redV_liftV π a c.1)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hNab]
        exact ⟨liftV π b y.1 i + π ^ b * w i, by ring⟩⟩
    refine ⟨(Equiv.ofBijective ψ ⟨?_, ?_⟩).symm⟩
    · intro y y' h
      have h1 := congrArg (fun z => z.1.1) h
      simp only [ψ] at h1
      rw [redV_eq_iff] at h1
      apply Subtype.ext
      rw [← redV_liftV π b y.1, ← redV_liftV π b y'.1, redV_eq_iff]
      intro i
      have := h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hNab] at this
      rw [show liftV π a c.1 i + π ^ a * liftV π b y.1 i -
          (liftV π a c.1 i + π ^ a * liftV π b y'.1 i) =
          π ^ a * (liftV π b y.1 i - liftV π b y'.1 i) by ring] at this
      exact (mul_dvd_mul_iff_left hpa).mp this
    · rintro ⟨⟨x, hx⟩, hφ⟩
      have h0 : redV π a (liftV π N x) = redV π a (liftV π a c.1) := by
        rw [redV_liftV]; exact congrArg Subtype.val hφ
      rw [redV_eq_iff] at h0
      let w : Fin n → R := fun i => Classical.choose (h0 i)
      have hw : ∀ i, liftV π N x i = liftV π a c.1 i + π ^ a * w i := fun i => by
        have := Classical.choose_spec (h0 i); rw [← this]; ring
      obtain ⟨w', hw'⟩ := liftV_redV π b w
      have hmem : P' (liftV π a c.1 + π ^ a • liftV π b (redV π b w)) := by
        have : liftV π a c.1 + π ^ a • liftV π b (redV π b w) = liftV π N x + π ^ N • w' := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw', hw, hNab]; ring
        rw [this]; exact hP' _ _ hx
      refine ⟨⟨redV π b w, hmem⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show redV π N _ = x
      rw [← redV_liftV π N x, redV_eq_iff]
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw', hw, hNab]
      exact ⟨w' i, by ring⟩
  exact ⟨(Equiv.sigmaFiberEquiv φ).symm.trans
    ((Equiv.sigmaCongrRight fun c => (hfib c).some.trans (hF _ c.2).some).trans
      (Equiv.sigmaEquivProd _ _))⟩

/-! ### The Taylor expansion over `R` and the valuation of the gradient -/

theorem hessian_transpose (Q : QuadForm R n) : Q.hessianᵀ = Q.hessian := by
  simp only [QuadForm.hessian, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

/-- `Q(x + s y) = Q(x) + s (H x)·y + s² Q(y)` over `R`. -/
theorem eval_add_smul' (Q : QuadForm R n) (x y : Fin n → R) (s : R) :
    Q.eval (x + s • y) = Q.eval x + s * ((Q.hessian *ᵥ x) ⬝ᵥ y) + s ^ 2 * Q.eval y := by
  have h := evalIn_add_smul R Q x y s
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at h
  rw [dotProduct_mulVec, ← mulVec_transpose, hessian_transpose] at h
  exact h

/-- **The valuation of a vector** `g`: the least `v` with `π ^ (v + 1) ∤ g j` for some `j` (or `0`). -/
noncomputable def dval (π : R) (g : Fin n → R) : ℕ := by
  classical
  exact if h : ∃ v, ∃ j, ¬ π ^ (v + 1) ∣ g j then Nat.find h else 0

theorem dval_spec (π : R) (g : Fin n → R) (h : ∃ v, ∃ j, ¬ π ^ (v + 1) ∣ g j) :
    (∃ j, ¬ π ^ (dval π g + 1) ∣ g j) ∧ ∀ i, π ^ dval π g ∣ g i := by
  classical
  have hd : dval π g = Nat.find h := by simp only [dval, h, ↓reduceDIte]
  rw [hd]
  refine ⟨Nat.find_spec h, fun i => ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
  · rw [h0, pow_zero]; exact one_dvd _
  · have := Nat.find_min h (Nat.sub_lt h0 one_pos)
    push Not at this
    have h1 := this i
    rwa [show Nat.find h - 1 + 1 = Nat.find h by omega] at h1

theorem dval_le (π : R) (g : Fin n → R) (e : ℕ) (h : ∃ j, ¬ π ^ (e + 1) ∣ g j) :
    dval π g ≤ e := by
  classical
  have h' : ∃ v, ∃ j, ¬ π ^ (v + 1) ∣ g j := ⟨e, h⟩
  have hd : dval π g = Nat.find h' := by simp only [dval, h', ↓reduceDIte]
  rw [hd]; exact Nat.find_min' h' h

theorem dval_eq (π : R) (g : Fin n → R) (v : ℕ) (h1 : ∃ j, ¬ π ^ (v + 1) ∣ g j)
    (h2 : ∀ i, π ^ v ∣ g i) : dval π g = v := by
  classical
  have h' : ∃ v, ∃ j, ¬ π ^ (v + 1) ∣ g j := ⟨v, h1⟩
  have hd : dval π g = Nat.find h' := by simp only [dval, h', ↓reduceDIte]
  rw [hd, Nat.find_eq_iff]
  refine ⟨h1, fun w hw => ?_⟩
  push Not
  intro i
  exact dvd_trans (pow_dvd_pow π hw) (h2 i)

/-- Good vectors (relative to coordinates `S₀`) over `R`: some `x i`, `i ∈ S₀`, is a unit. -/
def GoodR (S₀ : Finset (Fin n)) (π : R) (x : Fin n → R) : Prop := ∃ i ∈ S₀, ¬ π ∣ x i

theorem goodR_add_iff (S₀ : Finset (Fin n)) (π : R) (x y : Fin n → R) (s : ℕ) (hs : 1 ≤ s) :
    GoodR S₀ π (x + π ^ s • y) ↔ GoodR S₀ π x := by
  have hd : ∀ i, π ∣ π ^ s * y i := fun i => dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
  simp only [GoodR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dvd_add_left (hd _)]

/-- For a Good vector, the gradient valuation `dval π (H x)` is at most `e` (`exists_hessian_not_dvd`). -/
theorem dval_hessian_le (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    (x : Fin n → R) (hx : GoodR (unimodularCoords ν) π x) :
    ∃ j, ¬ π ^ (e + 1) ∣ (Q.hessian *ᵥ x) j := by
  obtain ⟨i, hi, hxi⟩ := hx
  exact exists_hessian_not_dvd Q π hπ P ν hJ e he x
    ⟨i, (Finset.mem_filter.mp hi).2, hxi⟩

theorem dval_hessian_add (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    (x y : Fin n → R) (hx : GoodR (unimodularCoords ν) π x) (s : ℕ) (hs : e + 1 ≤ s) :
    dval π (Q.hessian *ᵥ (x + π ^ s • y)) = dval π (Q.hessian *ᵥ x) := by
  have hb := dval_hessian_le Q π hπ P ν hJ e he x hx
  obtain ⟨⟨j, hj⟩, hall⟩ := dval_spec π _ ⟨e, hb⟩
  have hle := dval_le π _ e hb
  set v := dval π (Q.hessian *ᵥ x)
  rw [mulVec_add, mulVec_smul]
  apply dval_eq
  · refine ⟨j, fun h => hj ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    exact (dvd_add_left (dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)).mp h
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact dvd_add (hall i) (dvd_mul_of_dvd_left (pow_dvd_pow π (by omega)) _)

/-- The predicate on `R^n` cut out by the Good solutions mod `π ^ K` with gradient valuation `v`. -/
def PK (Q : QuadForm R n) (S₀ : Finset (Fin n)) (π : R) (m : R) (K v : ℕ) (x : Fin n → R) : Prop :=
  π ^ K ∣ Q.eval x - m ∧ GoodR S₀ π x ∧ dval π (Q.hessian *ᵥ x) = v

theorem sol_add (Q : QuadForm R n) (π m : R) (K : ℕ) (x y : Fin n → R) (h : π ^ K ∣ Q.eval x - m) :
    π ^ K ∣ Q.eval (x + π ^ K • y) - m := by
  rw [eval_add_smul']
  have : Q.eval x + π ^ K * ((Q.hessian *ᵥ x) ⬝ᵥ y) + (π ^ K) ^ 2 * Q.eval y - m =
      (Q.eval x - m) + π ^ K * ((Q.hessian *ᵥ x) ⬝ᵥ y + π ^ K * Q.eval y) := by ring
  rw [this]; exact dvd_add h (dvd_mul_right _ _)

section Key

variable (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R)

include hπ hJ he

theorem PK_le {K v : ℕ} {x : Fin n → R} (hx : PK Q (unimodularCoords ν) π m K v x) : v ≤ e := by
  rw [← hx.2.2]; exact dval_le π _ e (dval_hessian_le Q π hπ P ν hJ e he x hx.2.1)

/-- **Invariance of a Good solution class** (key step 1): a Good solution `x` mod `π ^ K` with gradient
valuation `v` stays one after adding anything in `π ^ (K - v) R^n`, when `K ≥ 2e + 1`. -/
theorem PK_add {K v : ℕ} (hk : 2 * e + 1 ≤ K) (x y : Fin n → R)
    (hx : PK Q (unimodularCoords ν) π m K v x) :
    PK Q (unimodularCoords ν) π m K v (x + π ^ (K - v) • y) := by
  have hle := PK_le Q π hπ P ν hJ e he m hx
  obtain ⟨hsol, hgood, hd⟩ := hx
  have hall : ∀ i, π ^ v ∣ (Q.hessian *ᵥ x) i := by
    have := (dval_spec π _ ⟨e, dval_hessian_le Q π hπ P ν hJ e he x hgood⟩).2
    rwa [hd] at this
  refine ⟨?_, (goodR_add_iff _ π x y _ (by omega)).mpr hgood, ?_⟩
  · rw [eval_add_smul']
    have hD : π ^ v ∣ (Q.hessian *ᵥ x) ⬝ᵥ y :=
      Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (hall i) _
    obtain ⟨D, hD⟩ := hD
    have hK : π ^ K = π ^ (K - v) * π ^ v := by rw [← pow_add]; congr 1; omega
    have h2 : (π ^ (K - v)) ^ 2 = π ^ K * π ^ (K - 2 * v) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hD, h2, show Q.eval x + π ^ (K - v) * (π ^ v * D) + π ^ K * π ^ (K - 2 * v) * Q.eval y - m
      = (Q.eval x - m) + (π ^ (K - v) * π ^ v) * D + π ^ K * π ^ (K - 2 * v) * Q.eval y by ring, ← hK]
    exact dvd_add (dvd_add hsol (dvd_mul_right _ _)) (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  · rw [dval_hessian_add Q π hπ P ν hJ e he x y hgood _ (by omega), hd]

/-- **Lifting condition** (key step 2): for a Good solution `c` mod `π ^ K` with gradient
`H c = π ^ v g'` and `Q c - m = π ^ K t`, the translate `c + π ^ (K - v) z` is a solution mod `π ^ (K + 1)`
iff `π ∣ t + g'·z` (a linear congruence mod `π`). -/
theorem PK_succ_iff {K v : ℕ} (hk : 2 * e + 1 ≤ K) (c : Fin n → R)
    (hc : PK Q (unimodularCoords ν) π m K v c) (t : R) (ht : Q.eval c - m = π ^ K * t)
    (g' : Fin n → R) (hg : Q.hessian *ᵥ c = π ^ v • g') (z : Fin n → R) :
    PK Q (unimodularCoords ν) π m (K + 1) v (c + π ^ (K - v) • z) ↔ π ∣ t + g' ⬝ᵥ z := by
  have hle := PK_le Q π hπ P ν hJ e he m hc
  have hz := PK_add Q π hπ P ν hJ e he m hk c z hc
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hiff : π ^ (K + 1) ∣ Q.eval (c + π ^ (K - v) • z) - m ↔ π ∣ t + g' ⬝ᵥ z := by
    rw [eval_add_smul', hg, smul_dotProduct, smul_eq_mul]
    have hK : π ^ (K - v) * π ^ v = π ^ K := by rw [← pow_add]; congr 1; omega
    have h2 : (π ^ (K - v)) ^ 2 = π ^ (K + 1) * π ^ (K - 2 * v - 1) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [h2, show Q.eval c + π ^ (K - v) * (π ^ v * (g' ⬝ᵥ z)) +
        π ^ (K + 1) * π ^ (K - 2 * v - 1) * Q.eval z - m =
        (Q.eval c - m) + (π ^ (K - v) * π ^ v) * (g' ⬝ᵥ z) +
        π ^ (K + 1) * (π ^ (K - 2 * v - 1) * Q.eval z) by ring, hK, ht,
      ← mul_add, dvd_add_left (dvd_mul_right _ _), pow_succ,
      mul_dvd_mul_iff_left (pow_ne_zero _ hπ0)]
  exact ⟨fun h => hiff.mp h.1, fun h => ⟨hiff.mpr h, hz.2⟩⟩

end Key

/-! ### Counting pieces -/

/-- **Solving a linear equation in one unit coefficient**: the solutions of `b + ∑ a_i z_i = 0` with `a_j`
a unit are parametrized by the coordinates `z_i`, `i ≠ j`. -/
theorem linear_equiv_aux {S : Type*} [CommRing S] (a : Fin n → S) (b : S) (j : Fin n)
    (hj : IsUnit (a j)) :
    Nonempty ({z : Fin n → S // b + ∑ i, a i * z i = 0} ≃ ({i // i ≠ j} → S)) := by
  classical
  have hu : a j * (↑hj.unit⁻¹ : S) = 1 := hj.mul_val_inv
  refine ⟨{ toFun := fun z i => z.1 i.1
            invFun := fun w => ⟨fun i => if h : i = j then
                -(↑hj.unit⁻¹ : S) * (b + ∑ i : {i // i ≠ j}, a i * w i) else w ⟨i, h⟩, ?_⟩
            left_inv := ?_
            right_inv := ?_ }⟩
  · rw [Fintype.sum_eq_add_sum_subtype_ne _ j]
    simp only [dite_true]
    have : ∀ i : {i // i ≠ j}, (a i * if h : (i : Fin n) = j then
        -(↑hj.unit⁻¹ : S) * (b + ∑ i : {i // i ≠ j}, a i * w i) else w ⟨i, h⟩) = a i * w i :=
      fun i => by simp only [i.2, ↓reduceDIte]
    rw [Finset.sum_congr rfl fun i _ => this i]
    linear_combination (-(b + ∑ i : {i // i ≠ j}, a i * w i)) * hu
  · rintro ⟨z, hz⟩
    apply Subtype.ext
    funext i
    by_cases h : i = j
    · subst h
      simp only [dite_true]
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at hz
      linear_combination (-(↑hj.unit⁻¹ : S)) * hz + z i * hu
    · simp only [h, dite_false]
  · intro w
    funext i
    simp only [i.2, ↓reduceDIte]

theorem isUnit_of_not_dvd (π : R) (hπ : Irreducible π) (y : R) (hy : ¬ π ∣ y) : IsUnit y := by
  by_contra hnu
  have hm : y ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal y).mpr hnu
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hy hm

theorem card_W (π : R) (hπ : Irreducible π) :
    Nat.card (Fin (n - 1) → R ⧸ Ideal.span {π ^ 1}) = q R ^ (n - 1) := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin (n - 1)), Fintype.card_fin]
  congr 1
  have h : Ideal.span {π ^ 1} = IsLocalRing.maximalIdeal R := by rw [pow_one, hπ.maximalIdeal_eq]
  exact Nat.card_congr (Ideal.quotEquivOfEq h).toEquiv

theorem evalIn_redV (Q : QuadForm R n) (π : R) (k : ℕ) (x : Fin n → R) :
    Q.evalIn (R ⧸ Ideal.span {π ^ k}) (redV π k x) = Ideal.Quotient.mk _ (Q.eval x) := by
  simp [QuadForm.evalIn, redV, map_sum, apply_ite, Ideal.Quotient.algebraMap_eq]

theorem mk_pi_dvd_iff (π : R) (K : ℕ) (hK : 1 ≤ K) (a : R) :
    Ideal.Quotient.mk (Ideal.span {π ^ K}) π ∣ Ideal.Quotient.mk _ a ↔ π ∣ a := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    have h1 : π ∣ a - π * c := dvd_trans (dvd_pow_self π (by omega)) hc
    simpa using dvd_add h1 (dvd_mul_right π c)
  · rintro ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ b, map_mul _ _ _⟩

theorem repCountOf_good_eq (Q : QuadForm R n) (S₀ : Finset (Fin n)) (π : R) (K : ℕ) (hK : 1 ≤ K)
    (m : R) :
    repCountOf Q π K m (IsGoodType S₀ π K) = Nat.card {x : Fin n → R ⧸ Ideal.span {π ^ K} //
      π ^ K ∣ Q.eval (liftV π K x) - m ∧ GoodR S₀ π (liftV π K x)} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  have hx : ∀ i, x i = Ideal.Quotient.mk _ (liftV π K x i) := fun i =>
    (congrFun (redV_liftV π K x) i).symm
  have hev : Q.evalIn (R ⧸ Ideal.span {π ^ K}) x = Ideal.Quotient.mk _ (Q.eval (liftV π K x)) := by
    conv_lhs => rw [← redV_liftV π K x]
    exact evalIn_redV Q π K _
  have hgood : IsGoodType S₀ π K x ↔ GoodR S₀ π (liftV π K x) := by
    simp only [IsGoodType, IsZeroType, GoodR]
    constructor
    · rintro ⟨-, i, hi, h⟩
      exact ⟨i, hi, by rwa [hx i, mk_pi_dvd_iff π K hK] at h⟩
    · rintro ⟨i, hi, h⟩
      have h' : ¬ Ideal.Quotient.mk _ π ∣ x i := by rwa [hx i, mk_pi_dvd_iff π K hK]
      exact ⟨fun hz => h' (hz i), i, hi, h'⟩
  rw [hev, Ideal.Quotient.eq, Ideal.mem_span_singleton, hgood]

/-! ### The lifting step `K → K + 1` -/

section Step

variable (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2) (m : R)

include hπ hJ he

/-- **The lifting step for one gradient valuation `v`**: the Good solutions mod `π ^ (K + 1)` with
gradient valuation `v` are in bijection with (those mod `π ^ K`) `× (R/π)^(n-1)`. Both are fibred over the
classes mod `π ^ (K - v)` (on which `v` and solvability mod `π ^ K` are constant): the fibre mod `π ^ K` is
all of `π^(K-v)R^n / π^K R^n`, the fibre mod `π ^ (K+1)` is cut out by one linear congruence mod `π`
with a unit coefficient. -/
theorem step_equiv_v {K : ℕ} (hk : 2 * e + 1 ≤ K) (v : ℕ) :
    Nonempty ({x : Fin n → R ⧸ Ideal.span {π ^ (K + 1)} //
        PK Q (unimodularCoords ν) π m (K + 1) v (liftV π (K + 1) x)} ≃
      {x : Fin n → R ⧸ Ideal.span {π ^ K} // PK Q (unimodularCoords ν) π m K v (liftV π K x)} ×
        (Fin (n - 1) → R ⧸ Ideal.span {π ^ 1})) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  by_cases hv : v ≤ e
  swap
  · have : IsEmpty {x : Fin n → R ⧸ Ideal.span {π ^ (K + 1)} //
        PK Q (unimodularCoords ν) π m (K + 1) v (liftV π (K + 1) x)} :=
      ⟨fun x => hv (PK_le Q π hπ P ν hJ e he m x.2)⟩
    have : IsEmpty {x : Fin n → R ⧸ Ideal.span {π ^ K} //
        PK Q (unimodularCoords ν) π m K v (liftV π K x)} :=
      ⟨fun x => hv (PK_le Q π hπ P ν hJ e he m x.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩
  set S₀ := unimodularCoords ν
  have hP : ∀ x y, PK Q S₀ π m K v x → PK Q S₀ π m K v (x + π ^ (K - v) • y) :=
    fun x y hx => PK_add Q π hπ P ν hJ e he m hk x y hx
  have hPK : ∀ x y, PK Q S₀ π m K v x → PK Q S₀ π m K v (x + π ^ K • y) := by
    intro x y hx
    have : π ^ K • y = π ^ (K - v) • (π ^ v • y) := by
      rw [smul_smul, ← pow_add]; congr 2; omega
    rw [this]; exact hP x _ hx
  have hPK1 : ∀ x y, PK Q S₀ π m (K + 1) v x → PK Q S₀ π m (K + 1) v (x + π ^ (K + 1) • y) := by
    rintro x y ⟨h1, h2, h3⟩
    exact ⟨sol_add Q π m _ x y h1, (goodR_add_iff _ π x y _ (by omega)).mpr h2,
      by rw [dval_hessian_add Q π hπ P ν hJ e he x y h2 _ (by omega), h3]⟩
  have hP1P : ∀ x, PK Q S₀ π m (K + 1) v x → PK Q S₀ π m K v x := by
    rintro x ⟨h1, h2, h3⟩
    exact ⟨dvd_trans (pow_dvd_pow π (by omega)) h1, h2, h3⟩
  -- mod π^K
  obtain ⟨e1⟩ := fiber_equiv π hπ0 (K - v) v K (by omega) (PK Q S₀ π m K v) (PK Q S₀ π m K v)
    (Fin n → R ⧸ Ideal.span {π ^ v}) hP (fun _ h => h) hPK
    (fun c hc => ⟨Equiv.subtypeUnivEquiv fun y => hP c _ hc⟩)
  have hF2 : ∀ c, PK Q S₀ π m K v c → Nonempty ({y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} //
      PK Q S₀ π m (K + 1) v (c + π ^ (K - v) • liftV π (v + 1) y)} ≃
      (Fin (n - 1) → R ⧸ Ideal.span {π ^ 1}) × (Fin n → R ⧸ Ideal.span {π ^ v})) := by
    intro c hc
    obtain ⟨t, ht⟩ := hc.1
    have hgood := hc.2.1
    obtain ⟨⟨j, hj⟩, hall⟩ := dval_spec π _ ⟨e, dval_hessian_le Q π hπ P ν hJ e he c hgood⟩
    rw [hc.2.2] at hj hall
    let g' : Fin n → R := fun i => Classical.choose (hall i)
    have hg : Q.hessian *ᵥ c = π ^ v • g' := funext fun i => by
      simp only [Pi.smul_apply, smul_eq_mul, g']; exact Classical.choose_spec (hall i)
    have hgj : ¬ π ∣ g' j := by
      intro h; apply hj
      rw [show (Q.hessian *ᵥ c) j = π ^ v * g' j from congrFun hg j, pow_succ]
      exact mul_dvd_mul_left _ h
    -- step a: the lifting condition is a linear congruence mod π
    have ea : {y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} //
        PK Q S₀ π m (K + 1) v (c + π ^ (K - v) • liftV π (v + 1) y)} ≃
        {y : Fin n → R ⧸ Ideal.span {π ^ (v + 1)} // π ∣ t + g' ⬝ᵥ liftV π (v + 1) y} :=
      Equiv.subtypeEquivRight fun y => PK_succ_iff Q π hπ P ν hJ e he m hk c hc t ht g' hg _
    -- step b: the congruence only sees y mod π
    have hPl : ∀ z y, π ∣ t + g' ⬝ᵥ z → ∀ s, 1 ≤ s → π ∣ t + g' ⬝ᵥ (z + π ^ s • y) := by
      intro z y hz s hs
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ← add_assoc]
      exact dvd_add hz (dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _)
    obtain ⟨eb⟩ := fiber_equiv π hπ0 1 v (v + 1) (by omega) (fun z => π ∣ t + g' ⬝ᵥ z)
      (fun z => π ∣ t + g' ⬝ᵥ z) (Fin n → R ⧸ Ideal.span {π ^ v})
      (fun z y hz => hPl z y hz 1 le_rfl) (fun _ h => h) (fun z y hz => hPl z y hz _ (by omega))
      (fun c' hc' => ⟨Equiv.subtypeUnivEquiv fun y => hPl c' _ hc' 1 le_rfl⟩)
    -- step c: rewrite the congruence in R/π
    have ec : {z : Fin n → R ⧸ Ideal.span {π ^ 1} // π ∣ t + g' ⬝ᵥ liftV π 1 z} ≃
        {z : Fin n → R ⧸ Ideal.span {π ^ 1} //
          Ideal.Quotient.mk _ t + ∑ i, Ideal.Quotient.mk _ (g' i) * z i = 0} := by
      refine Equiv.subtypeEquivRight fun z => ?_
      have hz : ∀ i, z i = Ideal.Quotient.mk _ (liftV π 1 z i) := fun i =>
        (congrFun (redV_liftV π 1 z) i).symm
      have key : Ideal.Quotient.mk (Ideal.span {π ^ 1}) t +
          ∑ i, Ideal.Quotient.mk (Ideal.span {π ^ 1}) (g' i) * z i =
          Ideal.Quotient.mk (Ideal.span {π ^ 1}) (t + g' ⬝ᵥ liftV π 1 z) := by
        simp only [map_add, map_sum, map_mul, dotProduct, ← hz]
      rw [key, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
    obtain ⟨ed⟩ := linear_equiv_aux (fun i => Ideal.Quotient.mk (Ideal.span {π ^ 1}) (g' i))
      (Ideal.Quotient.mk _ t) j ((isUnit_of_not_dvd π hπ _ hgj).map _)
    have hcard : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    let ee := Fintype.equivFinOfCardEq hcard
    exact ⟨ea.trans (eb.trans (Equiv.prodCongr (ec.trans (ed.trans
      (Equiv.arrowCongr ee (Equiv.refl _)))) (Equiv.refl _)))⟩
  -- mod π^(K+1)
  obtain ⟨e2⟩ := fiber_equiv π hπ0 (K - v) (v + 1) (K + 1) (by omega) (PK Q S₀ π m K v)
    (PK Q S₀ π m (K + 1) v)
    ((Fin (n - 1) → R ⧸ Ideal.span {π ^ 1}) × (Fin n → R ⧸ Ideal.span {π ^ v})) hP hP1P hPK1 hF2
  exact ⟨e2.trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr e1.symm (Equiv.refl _))))⟩

/-- **The lifting step** `r^Good_{π^(K+1)}(m) = q^(n-1) r^Good_{π^K}(m)` for `K ≥ 2e + 1`. -/
theorem repCountGood_succ {K : ℕ} (hk : 2 * e + 1 ≤ K) :
    repCountOf Q π (K + 1) m (IsGoodType (unimodularCoords ν) π (K + 1)) =
      q R ^ (n - 1) * repCountOf Q π K m (IsGoodType (unimodularCoords ν) π K) := by
  classical
  rw [repCountOf_good_eq Q _ π (K + 1) (by omega), repCountOf_good_eq Q _ π K (by omega),
    ← card_W π hπ, mul_comm, ← Nat.card_prod]
  apply Nat.card_congr
  set S₀ := unimodularCoords ν
  -- split by the gradient valuation
  have split : ∀ N : ℕ, {x : Fin n → R ⧸ Ideal.span {π ^ N} //
      π ^ N ∣ Q.eval (liftV π N x) - m ∧ GoodR S₀ π (liftV π N x)} ≃
      Σ v : ℕ, {x : Fin n → R ⧸ Ideal.span {π ^ N} // PK Q S₀ π m N v (liftV π N x)} := fun N =>
    (Equiv.sigmaFiberEquiv fun x : {x : Fin n → R ⧸ Ideal.span {π ^ N} //
        π ^ N ∣ Q.eval (liftV π N x) - m ∧ GoodR S₀ π (liftV π N x)} =>
      dval π (Q.hessian *ᵥ liftV π N x.1)).symm.trans
    (Equiv.sigmaCongrRight fun v => (Equiv.subtypeSubtypeEquivSubtypeInter _
      (fun x => dval π (Q.hessian *ᵥ liftV π N x) = v)).trans
      (Equiv.subtypeEquivRight fun x => by simp only [PK, and_assoc]))
  exact (split (K + 1)).trans ((Equiv.sigmaCongrRight fun v =>
    (step_equiv_v Q π hπ P ν hJ e he m hk v).some).trans
    ((Equiv.sigmaProdDistrib _ _).symm.trans (Equiv.prodCongr (split K).symm (Equiv.refl _))))

end Step

/-- **Lemma 3.2 over $R$** (Hanke 2004, (3.1), p. 358): for $Q$ in local normal form, $e = \mathrm{ord}_\pi(2)$
and $k \ge 2e + 1$: $r^{\mathrm{Good}}_{\pi^{k+l}}(m) = q^{(n-1)l}\, r^{\mathrm{Good}}_{\pi^k}(m)$. Proof as for $\mathbb{Z}$
(`LocalDensity.repCountGood_add`): Hensel in the variable whose partial derivative is a unit.

*Proof* (this file): by `exists_hessian_not_dvd` a Good $\vec{x}$ has a gradient entry of valuation
$\le e$. Group the Good solutions mod $\pi^{k+l}$ by their class mod $\pi^{k+l-e}$ (**not** by reduction mod
$\pi^k$: at dyadic primes those fibres are not uniform, e.g. $x^2 \equiv 1$ mod 16 vs. mod 8 in $\mathbb{Z}_2$).
Each class is stable under shifts in $\pi^{K-v}R^n$ (`PK_add`), and lifting one level is a single linear
congruence mod $\pi$ with a unit coefficient (`PK_succ_iff`), giving `repCountGood_succ`; induct on $l$.
All counts are explicit bijections, so no finiteness of the residue field is needed. -/
@[kb "hanke2004" "Lemma 3.2, eq. (3.1), p. 358"]
theorem repCountGood_add (Q : QuadForm R n) (π : R) (hπ : Irreducible π) (P : Finset (Fin n × Fin n))
    (ν : Fin n → ℕ) (hJ : IsJordanFormW Q π P ν) (e : ℕ) (he : π ^ e ∣ 2 ∧ ¬ π ^ (e + 1) ∣ 2)
    (m : R) (k l : ℕ) (hk : 2 * e + 1 ≤ k) :
    repCountOf Q π (k + l) m (IsGoodType (unimodularCoords ν) π (k + l)) =
      q R ^ ((n - 1) * l) * repCountOf Q π k m (IsGoodType (unimodularCoords ν) π k) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [← Nat.add_assoc, repCountGood_succ Q π hπ P ν hJ e he m (by omega), ih, ← mul_assoc,
      ← pow_add, Nat.mul_succ, Nat.add_comm (n - 1)]


end QuadFormsKB.LocalDensity.DVR
