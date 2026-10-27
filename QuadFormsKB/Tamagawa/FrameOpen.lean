/-
# Openness of the orbits on frames, and transitivity at unimodular odd primes

**Layer:** a DVR $R$ with uniformizer $\pi$ (every residue characteristic, dyadic included); no completeness.

The lemma `exists_openMat` moves one vector $y$ to a nearby $y'$ of the same value by an integral isometry
$T \equiv 1$ (the integral
form of $\tau_{y+y'}\tau_y$). Over the fraction field $T$ is a product of two reflections in vectors of $\mathrm{span}(y, y')$, so it
**fixes every vector orthogonal to $y$ and $y'$** (`exists_openMat_fix`). For a frame this allows an induction along an orthogonal
basis of the frame: if $T\circ P = \langle d_0, \dots, d_{r-1}\rangle$ ($P$ integral, $\det P \ne 0$, all $d_i \ne 0$), the columns
$y_i$ of $XP$ are pairwise orthogonal with $Q(y_i) = d_i$; moving them one at a time by isometries that fix the columns already moved
gives an isometry $M \equiv 1$ with $MXP = X'P$, hence $MX = X'$.

**Proves**
* `exists_openMat_fix`: `exists_openMat` with the extra conclusion $Tv = v$ whenever $B(v, y) = B(v, y') = 0$;
* `exists_frame_openMat` (**quantitative openness on frames**): genuine frames $X \equiv X' \bmod \pi^s$ of $T$, $s \ge rf + 1$ ($\pi^{f+1} \nmid 4d_i$),
  are related by an integral isometry $M \equiv 1 \bmod \pi^{s - rf}$;
* `exists_refl_fix`, `exists_frame_isometry_of_unimodular` (**transitivity at $\mathfrak p \nmid 2$**): if $2$ and all $d_i$ are units, any
  two integral frames of $T$ are related by an integral isometry (a reflection $\tau_{y-y'}$ or $\tau_{y'}\tau_{y+y'}$ per column; cf. O'Meara
  1963, §92, pp. 246–250).

Indices are 0-based.
-/
import QuadFormsKB.Tamagawa.FrameHensel

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa.Frames

open QuadForm LocalDensity LocalDensity.DVR QuadFormsKB.Tamagawa

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n r : ℕ}

/-! ### Helper lemmas -/

theorem bil_eq_hess (Q : QuadForm R n) (v y : Fin n → R) : bil Q v y = (Q.hessian *ᵥ v) ⬝ᵥ y := by
  unfold bil
  rw [dotProduct_comm, hess_dot_comm]

theorem bil_add_smul (Q : QuadForm R n) (v y y' : Fin n → R) (c : R) :
    bil Q v (y + c • y') = bil Q v y + c * bil Q v y' := by
  simp only [bil, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]

theorem compMat_one_eq (Q : QuadForm R n) : Q.compMat (1 : Matrix (Fin n) (Fin n) R) = Q :=
  eq_of_eval_eq fun y => by rw [eval_compMat, one_mulVec]

theorem bil_compMat (Q : QuadForm R n) {M : Matrix (Fin n) (Fin n) R} (hM : Q.compMat M = Q) (u v : Fin n → R) :
    bil Q (M *ᵥ u) (M *ᵥ v) = bil Q u v := by
  have h := hessian_compMat Q M
  rw [hM] at h
  calc bil Q (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ (Q.hessian *ᵥ (M *ᵥ v)) := rfl
    _ = u ⬝ᵥ ((Mᵀ * Q.hessian * M) *ᵥ v) := by
        symm
        rw [← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, vecMul_transpose]
    _ = bil Q u v := by rw [← h]; rfl

theorem diag_facts (Q : QuadForm R n) (Y : Matrix (Fin n) (Fin r) R) {dg : Fin r → R}
    (h : Q.compMat Y = QuadForm.diag dg) :
    (∀ i, Q.eval (DVR.col Y i) = dg i) ∧ ∀ i j, i ≠ j → bil Q (DVR.col Y i) (DVR.col Y j) = 0 := by
  have key : ∀ i j, i ≤ j → (Q.compMat Y).coeff i j = if i = j then dg i else 0 := by
    intro i j _
    rw [h]
    show Matrix.diagonal dg i j = _
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · have := key i i le_rfl
    rw [compMat_coeff, if_pos le_rfl, if_pos rfl, if_pos rfl] at this
    exact this
  · rcases lt_or_gt_of_ne hij with hlt | hgt
    · have := key i j hlt.le
      rw [compMat_coeff, if_pos hlt.le, if_neg hij, if_neg hij] at this
      exact this
    · have := key j i hgt.le
      rw [compMat_coeff, if_pos hgt.le, if_neg hij.symm, if_neg hij.symm] at this
      rw [bil_comm]
      exact this

/-- The inductive step of a frame induction. -/
abbrev FrameStep (Q : QuadForm R n) (Y Y' : Matrix (Fin n) (Fin r) R)
    (C : ℕ → Matrix (Fin n) (Fin n) R → Prop) : Prop :=
  ∀ (j : ℕ) (hj : j < r) (M : Matrix (Fin n) (Fin n) R), Q.compMat M = Q → C j M →
    (∀ i : Fin r, i.val < j → M *ᵥ DVR.col Y i = DVR.col Y' i) →
    ∃ T : Matrix (Fin n) (Fin n) R, Q.compMat T = Q ∧ T *ᵥ (M *ᵥ DVR.col Y ⟨j, hj⟩) = DVR.col Y' ⟨j, hj⟩ ∧
      (∀ v, bil Q v (M *ᵥ DVR.col Y ⟨j, hj⟩) = 0 → bil Q v (DVR.col Y' ⟨j, hj⟩) = 0 → T *ᵥ v = v) ∧
      C (j + 1) (T * M)

theorem frame_induct (Q : QuadForm R n) (Y Y' : Matrix (Fin n) (Fin r) R)
    (hY : ∀ i j, i ≠ j → bil Q (DVR.col Y i) (DVR.col Y j) = 0)
    (hY' : ∀ i j, i ≠ j → bil Q (DVR.col Y' i) (DVR.col Y' j) = 0)
    (C : ℕ → Matrix (Fin n) (Fin n) R → Prop) (h0 : C 0 1) (step : FrameStep Q Y Y' C) :
    ∃ M : Matrix (Fin n) (Fin n) R, Q.compMat M = Q ∧ C r M ∧ ∀ i, M *ᵥ DVR.col Y i = DVR.col Y' i := by
  have key : ∀ k, k ≤ r → ∃ M : Matrix (Fin n) (Fin n) R, Q.compMat M = Q ∧ C k M ∧
      ∀ i : Fin r, i.val < k → M *ᵥ DVR.col Y i = DVR.col Y' i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨1, compMat_one_eq Q, h0, fun i hi => absurd hi (by omega)⟩
    | succ j ih =>
      intro hj
      obtain ⟨M, hM, hC, hfix⟩ := ih (by omega)
      obtain ⟨T, hT, hTy, hTfix, hC'⟩ := step j (by omega) M hM hC hfix
      refine ⟨T * M, by rw [← compMat_mul, hT, hM], hC', fun i hi => ?_⟩
      rw [← mulVec_mulVec]
      by_cases hij : i.val < j
      · have hne : i ≠ ⟨j, by omega⟩ := fun h => by rw [h] at hij; exact lt_irrefl _ hij
        rw [hfix i hij]
        apply hTfix
        · rw [← hfix i hij, bil_compMat Q hM]
          exact hY _ _ hne
        · exact hY' _ _ hne
      · have : i = ⟨j, by omega⟩ := Fin.ext (by simp only; omega)
        rw [this]
        exact hTy
  obtain ⟨M, hM, hC, hfix⟩ := key r le_rfl
  exact ⟨M, hM, hC, fun i => hfix i i.2⟩

theorem frame_main {Q : QuadForm R n} {T : QuadForm R r} {P : Matrix (Fin r) (Fin r) R} (hPdet : P.det ≠ 0)
    {dg : Fin r → R} (hP : T.compMat P = QuadForm.diag dg)
    {x x' : Fin n × Fin r → R} (hx : formF Q x = tc T) (hx' : formF Q x' = tc T)
    (C : ℕ → Matrix (Fin n) (Fin n) R → Prop) (h0 : C 0 1)
    (step : FrameStep Q (toMat x * P) (toMat x' * P) C) :
    ∃ M : Matrix (Fin n) (Fin n) R, Q.compMat M = Q ∧ C r M ∧ frameMat r M *ᵥ x = x' := by
  have hcomp : ∀ z, formF Q z = tc T → Q.compMat (toMat z * P) = QuadForm.diag dg := fun z hz => by
    rw [← compMat_mul, (formF_eq_tc_iff Q T z).mp hz, hP]
  obtain ⟨M, hM, hC, hcol⟩ := frame_induct Q _ _ (diag_facts Q _ (hcomp x hx)).2
    (diag_facts Q _ (hcomp x' hx')).2 C h0 step
  refine ⟨M, hM, hC, ?_⟩
  have hMP : M * toMat x * P = toMat x' * P := by
    ext l i
    have := congrFun (hcol i) l
    rw [Matrix.mul_assoc]
    simpa [Matrix.mul_apply, mulVec, dotProduct, DVR.col] using this
  have hA : (M * toMat x - toMat x') * P = 0 := by rw [Matrix.sub_mul, hMP, sub_self]
  have h2 : P.det • (M * toMat x - toMat x') = 0 := by
    calc P.det • (M * toMat x - toMat x') = (M * toMat x - toMat x') * (P * P.adjugate) := by
          rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, hA, Matrix.zero_mul]
  have hMx : M * toMat x = toMat x' := by
    ext l i
    have := congrFun (congrFun h2 l) i
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.zero_apply, mul_eq_zero, hPdet,
      false_or] at this
    exact sub_eq_zero.mp this
  funext ⟨l, i⟩
  have h := toMat_frameMat_mulVec (r := r) M x
  rw [hMx] at h
  exact congrFun (congrFun h l) i

/-- The reflection in a vector with unit value, with its action on `v` with `B(v, u) = k Q(u)`. -/
theorem refl_data (Q : QuadForm R n) {u : Fin n → R} (hu : IsUnit (Q.eval u)) :
    ∃ τ : Matrix (Fin n) (Fin n) R, Q.compMat τ = Q ∧
      ∀ (v : Fin n → R) (k : R), bil Q v u = k * Q.eval u → τ *ᵥ v = v - k • u := by
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨QuadForm.reflMat u (c • (Q.hessian *ᵥ u)), ?_, fun v k hk => ?_⟩
  · apply QuadForm.compMat_reflMat
    rw [smul_smul, mul_comm (Q.eval u) c, hc, one_smul]
  · rw [QuadForm.reflMat_mulVec, smul_dotProduct, smul_eq_mul, dotProduct_comm (Q.hessian *ᵥ u) v]
    have : c * (v ⬝ᵥ (Q.hessian *ᵥ u)) = k := by
      show c * bil Q v u = k
      rw [hk]; linear_combination k * hc
    rw [this]

/-- **Quantitative openness, fixing the orthogonal complement:** as `exists_openMat` ($Q(y) = Q(y') = m \ne 0$, $\pi^f\,\Vert\,4m$,
$y' \equiv y \bmod \pi^s$, $s \ge f+1$), and moreover $Tv = v$ for every $v$ with $B(v, y) = B(v, y') = 0$. -/
theorem exists_openMat_fix {π : R} (hπ : Irreducible π) (Q : QuadForm R n) {m : R} (hm0 : m ≠ 0) {f s : ℕ}
    (hf : π ^ f ∣ 4 * m) (hf' : ¬ π ^ (f + 1) ∣ 4 * m) (hs : f + 1 ≤ s) {y y' : Fin n → R}
    (hy : Q.eval y = m) (hy' : Q.eval y' = m) (hyy : ∀ i, π ^ s ∣ y' i - y i) :
    ∃ T : Matrix (Fin n) (Fin n) R, Q.compMat T = Q ∧ T *ᵥ y = y' ∧
      (∀ i j, π ^ (s - f) ∣ T i j - (1 : Matrix (Fin n) (Fin n) R) i j) ∧
      ∀ v, bil Q v y = 0 → bil Q v y' = 0 → T *ᵥ v = v := by
  have hπ0 := hπ.ne_zero
  choose w hw using hyy
  have hy'w : y' = y + π ^ s • w := funext fun i => by
    have := hw i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination this
  obtain ⟨μ, ν, hm, hν⟩ := DVR.dvr_eq_pow_mul_unit hπ hm0
  have hμf : μ ≤ f := by
    by_contra h
    apply hf'
    have : π ^ (f + 1) ∣ m := by rw [hm]; exact Dvd.dvd.mul_right (pow_dvd_pow π (by omega)) ν
    exact Dvd.dvd.mul_left this 4
  obtain ⟨ρ₀, hρ₀, hρ₀u⟩ := DVR.dvr_exact hπ hf hf'
  set ρ := ρ₀ - π ^ (2 * s - f) * Q.eval w
  have hρ : ρ * π ^ f = 4 * m - (π ^ s) ^ 2 * Q.eval w := by
    rw [hρ₀, ← pow_mul, mul_comm s 2]
    have : π ^ (2 * s) = π ^ (2 * s - f) * π ^ f := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hρu : IsUnit ρ := by
    apply DVR.dvr_isUnit_of_not_dvd hπ
    intro h
    apply DVR.dvr_not_dvd_of_isUnit hπ hρ₀u
    have : π ∣ π ^ (2 * s - f) * Q.eval w := dvd_mul_of_dvd_left (dvd_pow_self π (by omega)) _
    have := dvd_add h this
    simpa [ρ] using this
  obtain ⟨r, hr⟩ := hρu.exists_right_inv
  obtain ⟨ν', hν'⟩ := hν.exists_right_inv
  have hyw' : Q.eval (y + π ^ s • w) = m := by rw [← hy'w, hy']
  refine ⟨openMat π s f μ ν' r Q y w, compMat_openMat hπ0 (by omega) (by omega) hm hν' hy hyw' hρ hr,
    by rw [openMat_mulVec hπ0 (by omega) (by omega) hm hν' hy hyw' hρ hr, hy'w], fun i j => ?_, ?_⟩
  · rw [openMat, Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    exact dvd_mul_right _ _
  · intro v hv hv'
    rw [bil_eq_hess] at hv hv'
    rw [hy'w, dotProduct_add, dotProduct_smul, hv, smul_eq_mul, zero_add] at hv'
    have hBw : (Q.hessian *ᵥ v) ⬝ᵥ w = 0 := by
      rcases mul_eq_zero.mp hv' with h | h
      · exact absurd h (pow_ne_zero _ hπ0)
      · exact h
    rw [openMat_mulVec_apply, openA_dot, openB_dot, hv, hBw]
    simp

/-- **Quantitative openness of the orbits on frames** (every prime, dyadic included). Let $T\circ P = \langle d_0, \dots, d_{r-1}\rangle$ with
$P$ integral, $\det P \ne 0$, all $d_i \ne 0$ and $\pi^{f+1} \nmid 4d_i$. If $X, X'$ are frames with $Q\circ X = Q\circ X' = T$ and
$X' \equiv X \bmod \pi^s$, $s \ge rf + 1$, there is an integral $M$ with $Q\circ M = Q$, $MX = X'$ and $M \equiv 1 \bmod \pi^{s - rf}$. -/
@[kb "weil1982" "§3.4 (orbits are open) [unverified]"]
theorem exists_frame_openMat {π : R} (hπ : Irreducible π) (Q : QuadForm R n) (T : QuadForm R r)
    {P : Matrix (Fin r) (Fin r) R} (hPdet : P.det ≠ 0) {dg : Fin r → R} (hP : T.compMat P = QuadForm.diag dg)
    (hdg : ∀ i, dg i ≠ 0) {f : ℕ} (hf : ∀ i, ¬ π ^ (f + 1) ∣ 4 * dg i) {s : ℕ} (hs : r * f + 1 ≤ s)
    {x x' : Fin n × Fin r → R} (hx : formF Q x = tc T) (hx' : formF Q x' = tc T)
    (hxx : ∀ i, π ^ s ∣ x' i - x i) :
    ∃ M : Matrix (Fin n) (Fin n) R, Q.compMat M = Q ∧ frameMat r M *ᵥ x = x' ∧
      ∀ i j, π ^ (s - r * f) ∣ M i j - (1 : Matrix (Fin n) (Fin n) R) i j := by
  have hcomp : ∀ z, formF Q z = tc T → Q.compMat (toMat z * P) = QuadForm.diag dg := fun z hz => by
    rw [← compMat_mul, (formF_eq_tc_iff Q T z).mp hz, hP]
  obtain ⟨hev, -⟩ := diag_facts Q _ (hcomp x hx)
  obtain ⟨hev', -⟩ := diag_facts Q _ (hcomp x' hx')
  obtain ⟨M, hM, hC, hMx⟩ := frame_main hPdet hP hx hx'
    (fun j M => ∀ a b, π ^ (s - j * f) ∣ M a b - (1 : Matrix (Fin n) (Fin n) R) a b)
    (fun a b => by simp) (by
    intro j hj M hM hC _
    set jj : Fin r := ⟨j, hj⟩ with hjj
    have hu : Q.eval (M *ᵥ DVR.col (toMat x * P) jj) = dg jj := by rw [← eval_compMat, hM, hev]
    have hjf : (j + 1) * f ≤ r * f := Nat.mul_le_mul_right f hj
    have e : (j + 1) * f = j * f + f := by ring
    have hcong : ∀ i, π ^ (s - j * f) ∣ DVR.col (toMat x' * P) jj i -
        (M *ᵥ DVR.col (toMat x * P) jj) i := by
      intro i
      have h1 : DVR.col (toMat x' * P) jj i - DVR.col (toMat x * P) jj i =
          ∑ k, (x' (i, k) - x (i, k)) * P k jj := by
        simp only [DVR.col, Matrix.mul_apply, toMat, Matrix.of_apply, ← Finset.sum_sub_distrib, sub_mul]
      have h1' : π ^ (s - j * f) ∣ DVR.col (toMat x' * P) jj i - DVR.col (toMat x * P) jj i := by
        rw [h1]
        exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left
          ((pow_dvd_pow π (Nat.sub_le _ _)).trans (hxx (i, k))) _
      have h2 : (M *ᵥ DVR.col (toMat x * P) jj) i - DVR.col (toMat x * P) jj i =
          ∑ b, (M i b - (1 : Matrix (Fin n) (Fin n) R) i b) * DVR.col (toMat x * P) jj b := by
        have : (M *ᵥ DVR.col (toMat x * P) jj) i - DVR.col (toMat x * P) jj i =
            ((M - 1) *ᵥ DVR.col (toMat x * P) jj) i := by
          rw [sub_mulVec, one_mulVec]; rfl
        rw [this]
        simp only [mulVec, dotProduct, Matrix.sub_apply]
      have h2' : π ^ (s - j * f) ∣ (M *ᵥ DVR.col (toMat x * P) jj) i - DVR.col (toMat x * P) jj i := by
        rw [h2]
        exact Finset.dvd_sum fun b _ => dvd_mul_of_dvd_left (hC i b) _
      have := dvd_sub h1' h2'
      rwa [sub_sub_sub_cancel_right] at this
    obtain ⟨fj, hfj, hfj'⟩ := exists_pow_dvd_not_dvd π hπ
      (show 4 * dg jj ≠ 0 from fun h0 => hf jj (h0 ▸ dvd_zero _))
    have hfjf : fj ≤ f := by
      by_contra hcon
      exact hf jj ((pow_dvd_pow π (by omega)).trans hfj)
    obtain ⟨T, hT, hTy, hTc, hTfix⟩ := exists_openMat_fix hπ Q (hdg jj) hfj hfj' (s := s - j * f)
      (by omega) hu (hev' jj) hcong
    refine ⟨T, hT, hTy, hTfix, fun a b => ?_⟩
    have hTM : T * M - 1 = T * (M - 1) + (T - 1) := by rw [Matrix.mul_sub, Matrix.mul_one]; abel
    rw [← Matrix.sub_apply, hTM, Matrix.add_apply, Matrix.mul_apply]
    refine dvd_add (Finset.dvd_sum fun c _ => dvd_mul_of_dvd_right ?_ _) ?_
    · rw [Matrix.sub_apply]
      exact (pow_dvd_pow π (by omega)).trans (hC c b)
    · rw [Matrix.sub_apply]
      exact (pow_dvd_pow π (by omega)).trans (hTc a b))
  exact ⟨M, hM, hMx, hC⟩

/-- **A reflection pair at $\mathfrak p \nmid 2$:** if $2$ and $m$ are units and $Q(y) = Q(y') = m$, there is an integral isometry $T$ with
$Ty = y'$ fixing every $v$ with $B(v,y) = B(v,y') = 0$: $\tau_{y-y'}$ if $Q(y-y')$ is a unit, else $\tau_{y'}\tau_{y+y'}$
($Q(y-y') + Q(y+y') = 4m$). -/
theorem exists_refl_fix {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (Q : QuadForm R n) {m : R} (hm : IsUnit m)
    {y y' : Fin n → R} (hy : Q.eval y = m) (hy' : Q.eval y' = m) :
    ∃ T : Matrix (Fin n) (Fin n) R, Q.compMat T = Q ∧ T *ᵥ y = y' ∧
      ∀ v, bil Q v y = 0 → bil Q v y' = 0 → T *ᵥ v = v := by
  have hyy : bil Q y y = 2 * m := by
    show y ⬝ᵥ (Q.hessian *ᵥ y) = _
    rw [dotProduct_hessian_self, hy]
  have hyy' : bil Q y' y' = 2 * m := by
    show y' ⬝ᵥ (Q.hessian *ᵥ y') = _
    rw [dotProduct_hessian_self, hy']
  have hB : (Q.hessian *ᵥ y) ⬝ᵥ y' = bil Q y y' := by
    rw [hess_dot_comm]; exact dotProduct_comm _ _
  set B := bil Q y y'
  set a : Fin n → R := y + (-1 : R) • y'
  set b : Fin n → R := y + (1 : R) • y'
  have hQa : Q.eval a = 2 * m - B := by
    have := eval_add_smul_gen Q y y' (-1)
    rw [hB, hy, hy'] at this
    simp only [a]; rw [this]; ring
  have hQb : Q.eval b = 2 * m + B := by
    have := eval_add_smul_gen Q y y' 1
    rw [hB, hy, hy'] at this
    simp only [b]; rw [this]; ring
  have hya : bil Q y a = 1 * Q.eval a := by
    simp only [a]; rw [bil_add_smul, hyy, hQa]
    show 2 * m + -1 * B = 1 * (2 * m - B)
    ring
  have hyb : bil Q y b = 1 * Q.eval b := by
    simp only [b]; rw [bil_add_smul, hyy, hQb]
    show 2 * m + 1 * B = 1 * (2 * m + B)
    ring
  have hsum : Q.eval a + Q.eval b = 4 * m := by rw [hQa, hQb]; ring
  by_cases hda : π ∣ Q.eval a
  · -- `Q(y + y')` is a unit
    have hub : IsUnit (Q.eval b) := by
      apply DVR.dvr_isUnit_of_not_dvd hπ
      intro hdb
      have h4 : π ∣ 4 * m := by rw [← hsum]; exact dvd_add hda hdb
      have hπp := hπ.prime
      rcases hπp.dvd_or_dvd h4 with h | h
      · apply h2
        have : (4 : R) = 2 * 2 := by norm_num
        rw [this] at h
        rcases hπp.dvd_or_dvd h with h | h <;> exact h
      · exact DVR.dvr_not_dvd_of_isUnit hπ hm h
    obtain ⟨τ₁, hτ₁, hτ₁v⟩ := refl_data Q hub
    obtain ⟨τ₂, hτ₂, hτ₂v⟩ := refl_data Q (u := y') (by rw [hy']; exact hm)
    have h1 : τ₁ *ᵥ y = -y' := by
      rw [hτ₁v y 1 hyb]
      simp only [b]
      rw [one_smul, one_smul]; abel
    have h2' : τ₂ *ᵥ (-y') = y' := by
      rw [hτ₂v (-y') (-2)]
      · rw [neg_smul, two_smul]; abel
      · rw [hy']
        show (-y') ⬝ᵥ (Q.hessian *ᵥ y') = _
        rw [neg_dotProduct]
        show -(y' ⬝ᵥ (Q.hessian *ᵥ y')) = _
        rw [dotProduct_hessian_self, hy']; ring
    refine ⟨τ₂ * τ₁, by rw [← compMat_mul, hτ₂, hτ₁], by rw [← mulVec_mulVec, h1, h2'], ?_⟩
    intro v hv hv'
    have hvb : bil Q v b = 0 * Q.eval b := by
      simp only [b]; rw [bil_add_smul, hv, hv']; ring
    rw [← mulVec_mulVec, hτ₁v v 0 hvb, zero_smul, sub_zero, hτ₂v v 0 (by rw [hv', zero_mul]), zero_smul,
      sub_zero]
  · have hua : IsUnit (Q.eval a) := DVR.dvr_isUnit_of_not_dvd hπ hda
    obtain ⟨τ, hτ, hτv⟩ := refl_data Q hua
    refine ⟨τ, hτ, ?_, ?_⟩
    · rw [hτv y 1 hya]
      simp only [a]
      rw [one_smul, neg_smul, one_smul]; abel
    · intro v hv hv'
      have hva : bil Q v a = 0 * Q.eval a := by
        simp only [a]; rw [bil_add_smul, hv, hv']; ring
      rw [hτv v 0 hva, zero_smul, sub_zero]

/-- **Transitivity on the integral frames of a unimodular $T$ at $\mathfrak p \nmid 2$:** if $T\circ P = \langle d_0, \dots, d_{r-1}\rangle$
with $\det P \ne 0$ and all $d_i$ units, and $2$ is a unit, then any two frames $X, X'$ with $Q\circ X = Q\circ X' = T$ are related by an
integral isometry: $MX = X'$, $Q\circ M = Q$ (cf. O'Meara 1963, §92, pp. 246–250). -/
@[kb "omeara1963" "§92, pp. 246–249 (non-dyadic lattices)"]
theorem exists_frame_isometry_of_unimodular {π : R} (hπ : Irreducible π) (h2 : ¬ π ∣ 2) (Q : QuadForm R n)
    (T : QuadForm R r) {P : Matrix (Fin r) (Fin r) R} (hPdet : P.det ≠ 0) {dg : Fin r → R}
    (hP : T.compMat P = QuadForm.diag dg) (hdg : ∀ i, IsUnit (dg i))
    {x x' : Fin n × Fin r → R} (hx : formF Q x = tc T) (hx' : formF Q x' = tc T) :
    ∃ M : Matrix (Fin n) (Fin n) R, Q.compMat M = Q ∧ frameMat r M *ᵥ x = x' := by
  have hcomp : ∀ z, formF Q z = tc T → Q.compMat (toMat z * P) = QuadForm.diag dg := fun z hz => by
    rw [← compMat_mul, (formF_eq_tc_iff Q T z).mp hz, hP]
  obtain ⟨hev, -⟩ := diag_facts Q _ (hcomp x hx)
  obtain ⟨hev', -⟩ := diag_facts Q _ (hcomp x' hx')
  obtain ⟨M, hM, -, hMx⟩ := frame_main hPdet hP hx hx' (fun _ _ => True) trivial (by
    intro j hj M hM _ _
    obtain ⟨T, hT, hTy, hTfix⟩ := exists_refl_fix hπ h2 Q (hdg ⟨j, hj⟩)
      (show Q.eval (M *ᵥ DVR.col (toMat x * P) ⟨j, hj⟩) = dg ⟨j, hj⟩ by
        rw [← eval_compMat, hM, hev])
      (hev' ⟨j, hj⟩)
    exact ⟨T, hT, hTy, hTfix, trivial⟩)
  exact ⟨M, hM, hMx⟩

end QuadFormsKB.Tamagawa.Frames
