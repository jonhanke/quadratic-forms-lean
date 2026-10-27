/-
# Quantitative openness of the orbits of $O(L_\mathfrak p)$ on $\{Q = m\}$, and isometries mod $\pi^k$ moving $e_0$

**Layer:** forms over a commutative ring $A$ (the algebra), then a DVR $R$ with uniformizer $\pi$ (every residue
characteristic, dyadic included). No completeness is used here.

**Proves**
* `compMat_openMat`, `openMat_mulVec` (**the product of two reflections, integrally**): for $Q(y) = Q(y') = m$ with
  $y' = y + \pi^s w$, the matrix
  $$T = 1 + \pi^{s-f}\rho'^{-1}\big(y\,\tilde a^{\mathsf T} + w\,\tilde b^{\mathsf T}\big)$$
  (`openMat`; $4m - \pi^{2s}Q(w) = \pi^f\rho'$, $m = \pi^\mu\nu$) satisfies $Q \circ T = Q$ and $Ty = y'$. Over the fraction field it
  is $\tau_{y+y'}\tau_y$ (Weil 1982, §3.4 [unverified]; O'Meara 1963, §42E, pp. 96–97); written this way it is visibly
  integral and $\equiv 1 \bmod \pi^{s-f}$. The identity behind $Q \circ T = Q$ is a polynomial identity (`open_key`).
* `exists_openMat` (**quantitative openness**): if $Q(y) = Q(y') = m \ne 0$, $\pi^f \,\Vert\, 4m$ and $y' \equiv y \bmod \pi^s$ with
  $s \ge f + 1$, there is $T \in M_{n}(R)$ with $Q\circ T = Q$, $Ty = y'$ and $T \equiv 1 \bmod \pi^{s-f}$.
* `exists_compMat_mulVec_e₀` (**isometries mod $\pi^k$ moving $e_0$**, for $Q = \langle m\rangle\perp Q'$): if $Q(z) \equiv m \bmod \pi^k$ and
  $z \equiv e_0 \bmod \pi^s$ with $s, k \ge f + 1$, there is $X \in M_{n+1}(R)$ with $Q \circ X \equiv Q \bmod \pi^k$ and $Xe_0 = z$. *Proof:*
  $u = z + e_0$ has $Q(u) = \pi^f\cdot$unit and $H_Qu \in \pi^fR^{n+1}$ (the splitting $L = Re_0 \perp L'$), so the reflections
  $\tau_u$, $\tau_{e_0}$ are integral; $T = \tau_u\tau_{e_0}$ is an isometry with $Te_0 = z - \theta u$, $\theta = (Q(z) - m)/Q(u)$, and
  $X = T + \theta\,u\,e_0^{\mathsf T}$ works because $B(Tv, u) \in \pi^f R$.
Indices are 0-based ($e_0$ is the first basis vector).
-/
import QuadFormsKB.Tamagawa.OrbitHensel
import QuadFormsKB.Tamagawa.LocalOrbital

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Tamagawa

open QuadForm LocalDensity

/-! ### Algebra over a commutative ring -/

section Algebra

variable {A : Type*} [CommRing A] {n : ℕ}

theorem eval_smul_gen (Q : QuadForm A n) (c : A) (x : Fin n → A) : Q.eval (c • x) = c ^ 2 * Q.eval x := by
  rw [eval_eq_dotProduct', eval_eq_dotProduct', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  ring

theorem hess_dot_comm (Q : QuadForm A n) (x y : Fin n → A) :
    (Q.hessian *ᵥ x) ⬝ᵥ y = (Q.hessian *ᵥ y) ⬝ᵥ x := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, QuadForm.hessian_transpose]

/-- $Q(x + c y) = Q(x) + c\,(H x)\cdot y + c^2 Q(y)$ over any commutative ring. -/
theorem eval_add_smul_gen (Q : QuadForm A n) (x y : Fin n → A) (c : A) :
    Q.eval (x + c • y) = Q.eval x + c * ((Q.hessian *ᵥ x) ⬝ᵥ y) + c ^ 2 * Q.eval y := by
  have h := eval_polar Q x (c • y)
  rw [eval_smul_gen, mulVec_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm, hess_dot_comm Q y x] at h
  linear_combination h

/-- $Q(v + by + cw)$ expanded. -/
theorem eval_add_smul_add_smul (Q : QuadForm A n) (v y w : Fin n → A) (b c : A) :
    Q.eval (v + b • y + c • w) = Q.eval v + b ^ 2 * Q.eval y + c ^ 2 * Q.eval w +
      b * ((Q.hessian *ᵥ v) ⬝ᵥ y) + c * ((Q.hessian *ᵥ v) ⬝ᵥ w) + b * c * ((Q.hessian *ᵥ y) ⬝ᵥ w) := by
  rw [eval_add_smul_gen, eval_add_smul_gen, mulVec_add, add_dotProduct, mulVec_smul, smul_dotProduct,
    smul_eq_mul]
  ring

/-- **The polynomial identity behind $Q\circ T = Q$** (checked symbolically): with $P_s = P_2P_\mu$, $m = P_\mu\nu$,
$\nu\nu' = 1$, $\tilde a = -(P_2\nu' B_y Q_w + 2B_w)$, $\tilde b = 2B_y - P_sB_w - P_sP_2\nu' B_yQ_w$,
$$P_s(\tilde a^2 m + \tilde b^2Q_w - \tilde a\tilde b P_sQ_w) + (4m - P_s^2Q_w)(\tilde aB_y + \tilde bB_w) = 0.$$ -/
theorem open_key (P2 Pμ ν ν' By Bw Qw : A) (hν : ν * ν' = 1) :
    let Ps := P2 * Pμ
    let m := Pμ * ν
    let a := -(P2 * ν' * By * Qw + 2 * Bw)
    let b := 2 * By - Ps * Bw - Ps * P2 * ν' * By * Qw
    Ps * (a ^ 2 * m + b ^ 2 * Qw - a * b * Ps * Qw) + (4 * m - Ps ^ 2 * Qw) * (a * By + b * Bw) = 0 := by
  intro Ps m a b
  simp only [Ps, m, a, b]
  linear_combination (By ^ 2 * P2 * Pμ * Qw * (P2 ^ 2 * Pμ * Qw * ν' - 4)) * hν

end Algebra

/-! ### The integral product of two reflections -/

section Open

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ}

/-- The vector $\tilde a$: $\tilde a_j = -(\pi^{s-\mu}\nu' (H y)_j Q(w) + 2(H w)_j)$. -/
def openA (π : A) (s μ : ℕ) (ν' : A) (Q : QuadForm A n) (y w : Fin n → A) : Fin n → A :=
  fun j => -(π ^ (s - μ) * ν' * (Q.hessian *ᵥ y) j * Q.eval w + 2 * (Q.hessian *ᵥ w) j)

/-- The vector $\tilde b$: $\tilde b_j = 2(H y)_j - \pi^s (H w)_j - \pi^s\pi^{s-\mu}\nu'(H y)_jQ(w)$. -/
def openB (π : A) (s μ : ℕ) (ν' : A) (Q : QuadForm A n) (y w : Fin n → A) : Fin n → A :=
  fun j => 2 * (Q.hessian *ᵥ y) j - π ^ s * (Q.hessian *ᵥ w) j -
    π ^ s * π ^ (s - μ) * ν' * (Q.hessian *ᵥ y) j * Q.eval w

/-- **The integral form of $\tau_{y+y'}\tau_y$** ($y' = y + \pi^s w$): $T = 1 + \pi^{s-f} r\,(y\tilde a^{\mathsf T} + w\tilde b^{\mathsf T})$,
$r = \rho'^{-1}$. -/
def openMat (π : A) (s f μ : ℕ) (ν' r : A) (Q : QuadForm A n) (y w : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  1 + (π ^ (s - f) * r) • (vecMulVec y (openA π s μ ν' Q y w) + vecMulVec w (openB π s μ ν' Q y w))

theorem openMat_mulVec_apply (π : A) (s f μ : ℕ) (ν' r : A) (Q : QuadForm A n) (y w v : Fin n → A) :
    openMat π s f μ ν' r Q y w *ᵥ v = v + (π ^ (s - f) * r * (openA π s μ ν' Q y w ⬝ᵥ v)) • y +
      (π ^ (s - f) * r * (openB π s μ ν' Q y w ⬝ᵥ v)) • w := by
  rw [openMat, add_mulVec, one_mulVec, smul_mulVec, add_mulVec, QuadForm.vecMulVec_mulVec,
    QuadForm.vecMulVec_mulVec, smul_add, smul_smul, smul_smul, add_assoc]

theorem openA_dot (π : A) (s μ : ℕ) (ν' : A) (Q : QuadForm A n) (y w v : Fin n → A) :
    openA π s μ ν' Q y w ⬝ᵥ v = -(π ^ (s - μ) * ν' * ((Q.hessian *ᵥ v) ⬝ᵥ y) * Q.eval w +
      2 * ((Q.hessian *ᵥ v) ⬝ᵥ w)) := by
  rw [hess_dot_comm Q v y, hess_dot_comm Q v w]
  simp only [openA, dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem openB_dot (π : A) (s μ : ℕ) (ν' : A) (Q : QuadForm A n) (y w v : Fin n → A) :
    openB π s μ ν' Q y w ⬝ᵥ v = 2 * ((Q.hessian *ᵥ v) ⬝ᵥ y) - π ^ s * ((Q.hessian *ᵥ v) ⬝ᵥ w) -
      π ^ s * π ^ (s - μ) * ν' * ((Q.hessian *ᵥ v) ⬝ᵥ y) * Q.eval w := by
  rw [hess_dot_comm Q v y, hess_dot_comm Q v w]
  simp only [openB, dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

variable {π : A} {Q : QuadForm A n} {m ν ν' ρ r : A} {s f μ : ℕ} {y w : Fin n → A}

/-- $B(y, w) = -\pi^sQ(w)$ when $Q(y + \pi^s w) = Q(y)$. -/
theorem hess_y_w (hπ0 : π ≠ 0) (hy' : Q.eval (y + π ^ s • w) = Q.eval y) :
    (Q.hessian *ᵥ y) ⬝ᵥ w = -(π ^ s * Q.eval w) := by
  rw [eval_add_smul_gen] at hy'
  have h : π ^ s * ((Q.hessian *ᵥ y) ⬝ᵥ w + π ^ s * Q.eval w) = 0 := by linear_combination hy'
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (pow_ne_zero _ hπ0)
  · linear_combination h

/-- **$T$ is an isometry:** $Q \circ T = Q$. -/
theorem compMat_openMat (hπ0 : π ≠ 0) (hμs : μ ≤ s) (hfs : f ≤ s) (hm : m = π ^ μ * ν) (hν : ν * ν' = 1)
    (hy : Q.eval y = m) (hy' : Q.eval (y + π ^ s • w) = m)
    (hρ : ρ * π ^ f = 4 * m - (π ^ s) ^ 2 * Q.eval w) (hr : ρ * r = 1) :
    Q.compMat (openMat π s f μ ν' r Q y w) = Q := by
  refine eq_of_eval_eq fun v => ?_
  rw [eval_compMat, openMat_mulVec_apply, eval_add_smul_add_smul, openA_dot, openB_dot,
    hess_y_w hπ0 (hy'.trans hy.symm), hy]
  set By := (Q.hessian *ᵥ v) ⬝ᵥ y
  set Bw := (Q.hessian *ᵥ v) ⬝ᵥ w
  set Qw := Q.eval w
  set P2 := π ^ (s - μ)
  set P1 := π ^ (s - f)
  have hPs : π ^ s = P2 * π ^ μ := by rw [← pow_add, Nat.sub_add_cancel hμs]
  have hP1 : P1 * π ^ f = π ^ s := by rw [← pow_add, Nat.sub_add_cancel hfs]
  have key := open_key P2 (π ^ μ) ν ν' By Bw Qw hν
  simp only at key
  rw [← hPs, ← hm] at key
  set a := -(P2 * ν' * By * Qw + 2 * Bw)
  set b := 2 * By - π ^ s * Bw - π ^ s * P2 * ν' * By * Qw
  set X := a ^ 2 * m + b ^ 2 * Qw - a * b * π ^ s * Qw
  set Y := a * By + b * Bw
  -- `D (P1 r X + Y) = 0` with `D = ρ π^f ≠ 0`
  have hD : ρ * π ^ f * (P1 * r * X + Y) = 0 := by
    rw [hρ]
    have : (4 * m - (π ^ s) ^ 2 * Qw) * (P1 * r * X + Y) =
        P1 * (r * (ρ * π ^ f)) * X + (4 * m - (π ^ s) ^ 2 * Qw) * Y := by rw [hρ]; ring
    rw [this, show r * (ρ * π ^ f) = π ^ f by rw [← mul_assoc, mul_comm r ρ, hr, one_mul], mul_assoc P1,
      ← mul_assoc P1, hP1]
    linear_combination key
  have hρ0 : ρ ≠ 0 := left_ne_zero_of_mul_eq_one hr
  have h0 : P1 * r * X + Y = 0 := by
    rcases mul_eq_zero.mp hD with h | h
    · exact absurd h (mul_ne_zero hρ0 (pow_ne_zero _ hπ0))
    · exact h
  have : P1 * r * (P1 * r * X + Y) = 0 := by rw [h0, mul_zero]
  linear_combination this

/-- **$T$ moves $y$ to $y'$:** $Ty = y + \pi^sw$. -/
theorem openMat_mulVec (hπ0 : π ≠ 0) (hμs : μ ≤ s) (hfs : f ≤ s) (hm : m = π ^ μ * ν) (hν : ν * ν' = 1)
    (hy : Q.eval y = m) (hy' : Q.eval (y + π ^ s • w) = m)
    (hρ : ρ * π ^ f = 4 * m - (π ^ s) ^ 2 * Q.eval w) (hr : ρ * r = 1) :
    openMat π s f μ ν' r Q y w *ᵥ y = y + π ^ s • w := by
  have hyw := hess_y_w hπ0 (hy'.trans hy.symm)
  have hyy : (Q.hessian *ᵥ y) ⬝ᵥ y = 2 * m := by rw [dotProduct_comm, dotProduct_hessian_self, hy]
  have hPs : π ^ (s - μ) * π ^ μ = π ^ s := by rw [← pow_add, Nat.sub_add_cancel hμs]
  have hP1 : π ^ (s - f) * π ^ f = π ^ s := by rw [← pow_add, Nat.sub_add_cancel hfs]
  rw [openMat_mulVec_apply, openA_dot, openB_dot, hyy, hyw]
  have ha : -(π ^ (s - μ) * ν' * (2 * m) * Q.eval w + 2 * -(π ^ s * Q.eval w)) = 0 := by
    rw [hm, ← hPs]; linear_combination (-2 * π ^ (s - μ) * π ^ μ * Q.eval w) * hν
  have hb : π ^ (s - f) * r * (2 * (2 * m) - π ^ s * -(π ^ s * Q.eval w) -
      π ^ s * π ^ (s - μ) * ν' * (2 * m) * Q.eval w) = π ^ s := by
    have e1 : 2 * (2 * m) - π ^ s * -(π ^ s * Q.eval w) - π ^ s * π ^ (s - μ) * ν' * (2 * m) * Q.eval w =
        ρ * π ^ f := by
      rw [hρ, hm, ← hPs]; linear_combination (-2 * (π ^ (s - μ) * π ^ μ) ^ 2 * Q.eval w) * hν
    rw [e1, ← hP1]; linear_combination (π ^ (s - f) * π ^ f) * hr
  rw [ha, mul_zero, zero_smul, add_zero, hb]

end Open

/-! ### Quantitative openness over a DVR -/

section DVROpen

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

/-- **Quantitative openness of the orbits on $\{Q = m\}$** (every prime, dyadic included): if $Q(y) = Q(y') = m \ne 0$,
$\pi^f \,\Vert\, 4m$, and $y' \equiv y \bmod \pi^s$ with $s \ge f + 1$, there is an integral $T$ with $Q \circ T = Q$, $Ty = y'$ and
$T \equiv 1 \bmod \pi^{s - f}$ (the integral form of $\tau_{y+y'}\tau_y$, `openMat`). -/
@[kb "weil1982" "§3.4 (orbits are open) [unverified]"]
theorem exists_openMat {π : R} (hπ : Irreducible π) (Q : QuadForm R n) {m : R} (hm0 : m ≠ 0) {f s : ℕ}
    (hf : π ^ f ∣ 4 * m) (hf' : ¬ π ^ (f + 1) ∣ 4 * m) (hs : f + 1 ≤ s) {y y' : Fin n → R}
    (hy : Q.eval y = m) (hy' : Q.eval y' = m) (hyy : ∀ i, π ^ s ∣ y' i - y i) :
    ∃ T : Matrix (Fin n) (Fin n) R, Q.compMat T = Q ∧ T *ᵥ y = y' ∧
      ∀ i j, π ^ (s - f) ∣ T i j - (1 : Matrix (Fin n) (Fin n) R) i j := by
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
  -- `4m - π^(2s) Q(w) = π^f ρ'` with `ρ'` a unit
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
    by rw [openMat_mulVec hπ0 (by omega) (by omega) hm hν' hy hyw' hρ hr, hy'w], fun i j => ?_⟩
  rw [openMat, Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  exact dvd_mul_right _ _

end DVROpen

/-! ### Isometries mod $\pi^k$ moving $e_0$ (the split form) -/

section Split

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}

theorem hessian_splitForm_mulVec (a : R) (Q' : QuadForm R n) (t : R) (x : Fin n → R) :
    (splitForm a Q').hessian *ᵥ (Fin.cons t x : Fin (n + 1) → R) = Fin.cons (2 * a * t) (Q'.hessian *ᵥ x) := by
  rw [hessian_splitForm, cornerMat_mulVec]

/-- **Isometries mod $\pi^k$ moving $e_0$** ($Q = \langle m\rangle\perp Q'$, every prime, dyadic included): if $\pi^f \,\Vert\, 4m$,
$Q(z) \equiv m \bmod \pi^k$ and $z \equiv e_0 \bmod \pi^s$ with $s, k \ge f + 1$, there is $X \in M_{n+1}(R)$ with
$Q\circ X \equiv Q \bmod \pi^k$ (values at every integral vector) and $Xe_0 = z$. -/
@[kb "weil1982" "§3.4 (orbit of e₀ mod π^k) [unverified]"]
theorem exists_compMat_mulVec_e₀ {π : R} (hπ : Irreducible π) {m : R} (Q' : QuadForm R n) {f s k : ℕ}
    (hf : π ^ f ∣ 4 * m) (hf' : ¬ π ^ (f + 1) ∣ 4 * m) (hs : f + 1 ≤ s) (hk : f + 1 ≤ k)
    {z : Fin (n + 1) → R} (hz : π ^ k ∣ (splitForm m Q').eval z - m)
    (hze : ∀ i, π ^ s ∣ z i - (e₀ : Fin (n + 1) → R) i) :
    ∃ X : Matrix (Fin (n + 1)) (Fin (n + 1)) R, X *ᵥ (e₀ : Fin (n + 1) → R) = z ∧
      ∀ v, π ^ k ∣ (splitForm m Q').eval (X *ᵥ v) - (splitForm m Q').eval v := by
  set Q := splitForm m Q'
  have hπ0 := hπ.ne_zero
  obtain ⟨ρ₀, hρ₀, hρ₀u⟩ := DVR.dvr_exact hπ hf hf'
  set u : Fin (n + 1) → R := z + e₀
  -- coordinates of `z`
  set δ₀ := z 0 - 1
  have hz0 : z 0 = 1 + δ₀ := by ring
  have hδ₀ : π ^ s ∣ δ₀ := by simpa [δ₀] using hze 0
  have hztail : ∀ i : Fin n, π ^ s ∣ z i.succ := fun i => by simpa using hze i.succ
  have hzc : z = Fin.cons (1 + δ₀) (Fin.tail z) := by
    rw [← hz0]; exact (Fin.cons_self_tail z).symm
  have hu : u = Fin.cons (2 + δ₀) (Fin.tail z) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [u, hz0]; ring
    · simp [u, Fin.tail]
  -- `Q(z) = m + η`
  obtain ⟨η', hη'⟩ := hz
  set η := Q.eval z - m
  -- `Q(u) = π^f ρ₁` with `ρ₁` a unit
  have hQu : Q.eval u = η + 2 * m * (2 + δ₀) := by
    have h1 := eval_add_smul_gen Q z (e₀ : Fin (n + 1) → R) 1
    rw [one_smul, one_mul, one_pow, one_mul] at h1
    have he : Q.eval (e₀ : Fin (n + 1) → R) = m := by
      have := evalIn_splitForm_e₀ R m Q'
      simpa [QuadForm.evalIn, QuadForm.eval] using this
    have hHz : (Q.hessian *ᵥ z) ⬝ᵥ (e₀ : Fin (n + 1) → R) = 2 * m * (1 + δ₀) := by
      have h2 := hessian_splitForm_mulVec m Q' (z 0) (Fin.tail z)
      rw [Fin.cons_self_tail] at h2
      rw [show Q.hessian = (splitForm m Q').hessian from rfl, h2, e₀_eq_single, dotProduct_single, mul_one,
        Fin.cons_zero, hz0]
    rw [show u = z + e₀ from rfl, h1, he, hHz]
    simp only [η]
    ring
  have hfs : π ^ (f + 1) ∣ 2 * m * δ₀ := by
    have : π ^ (f + 1) ∣ δ₀ := (pow_dvd_pow π hs).trans hδ₀
    exact dvd_mul_of_dvd_right this _
  have hfk : π ^ (f + 1) ∣ η := by rw [hη']; exact dvd_mul_of_dvd_left (pow_dvd_pow π hk) _
  obtain ⟨c1, hc1⟩ := hfs
  obtain ⟨c2, hc2⟩ := hfk
  set ρ₁ := ρ₀ + π * (c1 + c2)
  have hQu' : Q.eval u = π ^ f * ρ₁ := by
    rw [hQu, show 2 * m * (2 + δ₀) = 4 * m + 2 * m * δ₀ by ring, hρ₀, hc1, hc2, pow_succ]; ring
  have hρ₁ : IsUnit ρ₁ := by
    apply DVR.dvr_isUnit_of_not_dvd hπ
    intro h
    apply DVR.dvr_not_dvd_of_isUnit hπ hρ₀u
    have := dvd_sub h (dvd_mul_right π (c1 + c2))
    simpa [ρ₁] using this
  -- `H u = π^f h`
  have hHu : ∀ i, π ^ f ∣ (Q.hessian *ᵥ u) i := by
    intro i
    rw [hu, hessian_splitForm_mulVec]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]
      rw [show 2 * m * (2 + δ₀) = 4 * m + 2 * m * δ₀ by ring]
      exact dvd_add hf ((pow_dvd_pow π (Nat.le_succ f)).trans ⟨c1, hc1⟩)
    · simp only [Fin.cons_succ, mulVec, dotProduct]
      refine Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right ?_ _
      exact (pow_dvd_pow π (by omega)).trans (hztail j)
  choose h hh using hHu
  obtain ⟨ρ₁', hρ₁'⟩ := hρ₁.exists_right_inv
  set wu : Fin (n + 1) → R := ρ₁' • h
  have hwu : Q.hessian *ᵥ u = Q.eval u • wu := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, wu, hQu', hh i]
    rw [show π ^ f * ρ₁ * (ρ₁' * h i) = π ^ f * h i * (ρ₁ * ρ₁') by ring, hρ₁', mul_one]
  set w₀ : Fin (n + 1) → R := Pi.single 0 2
  have hw₀ : Q.hessian *ᵥ (e₀ : Fin (n + 1) → R) = Q.eval e₀ • w₀ := by
    have he : Q.eval (e₀ : Fin (n + 1) → R) = m := by
      have := evalIn_splitForm_e₀ R m Q'
      simpa [QuadForm.evalIn, QuadForm.eval] using this
    rw [he]
    funext i
    rw [show (e₀ : Fin (n + 1) → R) = Fin.cons 1 0 from rfl, hessian_splitForm_mulVec]
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [w₀, Fin.succ_ne_zero, mul_comm]
  -- `θ Q(u) = η`
  set θ := π ^ (k - f) * η' * ρ₁'
  have hθ : θ * Q.eval u = η := by
    rw [hQu', hη']
    have : π ^ (k - f) * π ^ f = π ^ k := by rw [← pow_add]; congr 1; omega
    linear_combination (π ^ (k - f) * π ^ f * η') * hρ₁' + η' * this
  have hQu0 : Q.eval u ≠ 0 := by
    rw [hQu']; exact mul_ne_zero (pow_ne_zero _ hπ0) hρ₁.ne_zero
  set T := reflMat u wu * reflMat (e₀ : Fin (n + 1) → R) w₀
  have hT : Q.compMat T = Q := by
    rw [← compMat_mul, compMat_reflMat Q hwu, compMat_reflMat Q hw₀]
  have hTv : ∀ v, Q.eval (T *ᵥ v) = Q.eval v := fun v => by rw [← eval_compMat, hT]
  -- `T e₀ = z - θ u`
  have hwu0 : wu 0 = 1 - θ := by
    have h1 := congrFun hwu 0
    rw [Pi.smul_apply, smul_eq_mul, hu, hessian_splitForm_mulVec, Fin.cons_zero, ← hu] at h1
    have h2 : Q.eval u * (wu 0 - (1 - θ)) = 0 := by
      linear_combination -h1 - hQu + hθ
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hQu0
    · linear_combination h
  have hTe : T *ᵥ (e₀ : Fin (n + 1) → R) = z - θ • u := by
    rw [← mulVec_mulVec, reflMat_mulVec (e₀ : Fin (n + 1) → R) w₀, reflMat_mulVec]
    have hw₀e : w₀ ⬝ᵥ (e₀ : Fin (n + 1) → R) = 2 := by
      rw [e₀_eq_single]; simp [w₀]
    rw [hw₀e, show (e₀ : Fin (n + 1) → R) - (2 : R) • e₀ = -e₀ by rw [two_smul]; abel, dotProduct_neg,
      neg_smul, sub_neg_eq_add]
    have : wu ⬝ᵥ (e₀ : Fin (n + 1) → R) = wu 0 := by rw [e₀_eq_single, dotProduct_single, mul_one]
    rw [this, hwu0, sub_smul, one_smul]
    simp only [u]
    abel
  refine ⟨T + vecMulVec (θ • u) (Pi.single 0 1), ?_, fun v => ?_⟩
  · rw [add_mulVec, hTe, QuadForm.vecMulVec_mulVec, e₀_eq_single, single_dotProduct, one_mul,
      Pi.single_eq_same, one_smul]
    abel
  · rw [add_mulVec, QuadForm.vecMulVec_mulVec, single_dotProduct, one_mul, smul_smul, eval_add_smul_gen, hTv]
    -- `B(Tv, u) ∈ π^f R`
    have hB : (Q.hessian *ᵥ (T *ᵥ v)) ⬝ᵥ u = π ^ f * (h ⬝ᵥ (T *ᵥ v)) := by
      rw [hess_dot_comm, dotProduct_comm]
      simp only [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hh i]; ring
    rw [hB, show (v 0 * θ) ^ 2 * Q.eval u = v 0 ^ 2 * θ * (θ * Q.eval u) by ring, hθ, hη']
    have : π ^ (k - f) * π ^ f = π ^ k := by rw [← pow_add]; congr 1; omega
    refine ⟨v 0 * η' * ρ₁' * (h ⬝ᵥ (T *ᵥ v)) + v 0 ^ 2 * θ * η', ?_⟩
    simp only [θ]
    linear_combination (v 0 * η' * ρ₁' * (h ⬝ᵥ (T *ᵥ v))) * this

end Split

end QuadFormsKB.Tamagawa
