/-
# Cassels, Chapter 10, Theorem 7.1 for $n \ge 5$, and Lemma 7.2

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Ch. 10, §7: Theorem 7.1 (p. 186), the proof for $n \ge 4$
(pp. 189–190) and Lemma 7.2 (p. 190).

**Setting.** $V$ a finite-dimensional $\mathbb Q$-vector space with a regular quadratic form $Q$ and a basis $e_0, \dots, e_{n-1}$
of a $\mathbb Z$-lattice $\Lambda$; coordinates $\xi \in \mathbb Q_p^n$ give the vector $\sum_i \xi_i (1 \otimes e_i)$ of $V_p$
(`vecP`). $D\,Q$ has the symmetric integral Gram matrix $N$ (`hND`), and $f$ = `LocalDensity.ofMatrixZ N` is the integral form
$\xi \mapsto \xi^{\mathsf T}N\xi = D\,Q(\sum_i\xi_ie_i)$ (Cassels' $f$, up to the factor $D$). $C(V_p)$ carries its vector space
topology.

**Proves.**
* the approximation property `SpinApprox T t` of a family $t_p \in C(V_p)$ at a finite set $T$ of primes: every family of
  neighbourhoods of the $t_p$ ($p \in T$) contains the image of some $u \in \operatorname{Spin}(V)$ with
  $u \in \operatorname{Spin}(\Lambda_p)$ for $p \notin T$; it is closed under products (`SpinApprox.mul`, `SpinApprox.list_prod`);
* **Lemma 7.2** (`lemma72`): for $n \ge 4$, $V$ indefinite and $T$ containing $2$ and the primes dividing the Hessian determinant of
  $f$, families of Cassels' commutators $w_p = \{Q(a_p)\}^{-1}\{Q(b_p)\}^{-1}a_pb_pa_pb_p$ have the approximation property;
* **Theorem 7.1 for $n \ge 5$** (`spinStrongApproximation_five`): there every $V_p$ is isotropic, so every
  $u^{(p)} \in \mathcal U_p$ is a product of commutators (Lemma 3.4, `Thm71Spin.exists_list_vcomm`), and Lemma 7.2 applies at
  every $p \in T$. (Cassels' first stage, the approximation of $u^{(p)}$ by products of vectors with $\prod\phi(a_i) = 1$, is only
  needed at the primes where $V_p$ is anisotropic, which occur only for $n \le 4$.)
-/
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Spin
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Coords
import QuadFormsKB.Literature.Cassels.Ch10.Thm71Approx

open CliffordAlgebra TensorProduct Module Matrix Topology Filter

set_option linter.unusedSectionVars false

namespace QuadFormsKB.Cassels.Thm71Five

open QuadFormsKB.Cassels Thm71Ternary Thm71Spin Thm71Coords Thm71Approx

/-- Helper (file-local): the vector space topology on $C(V_p)$. -/
noncomputable local instance cliffTop {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : TopologicalSpace (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  cliffordTopology (Q.baseChange ℚ_[p])

local instance cliffModTop {V : Type} [AddCommGroup V] [Module ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : IsModuleTopology ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) := ⟨rfl⟩

local instance cliffFin {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
    (p : ℕ) [Fact p.Prime] : Module.Finite ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  finiteDimensional_clifford (Q.baseChange ℚ_[p])

local instance cliffTopRing {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (Q : QuadraticForm ℚ V) (p : ℕ) [Fact p.Prime] : IsTopologicalRing (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
  IsModuleTopology.isTopologicalRing ℚ_[p] _

section Setup

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)

variable {n : ℕ} (e : Basis (Fin n) ℚ V)

/-- The vector $\sum_i \xi_i(1 \otimes e_i)$ of $V_p$ with coordinates $\xi$. -/
noncomputable def vecP (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℚ_[p]) : ℚ_[p] ⊗[ℚ] V :=
  ∑ i, ξ i • ((1 : ℚ_[p]) ⊗ₜ[ℚ] e i)

/-- The vector $\sum_i y_ie_i$ of $V$ with rational coordinates $y$. -/
noncomputable def vecG (y : Fin n → ℚ) : V := ∑ i, y i • e i

theorem one_tmul_vecG (p : ℕ) [Fact p.Prime] (y : Fin n → ℚ) :
    (1 : ℚ_[p]) ⊗ₜ[ℚ] vecG e y = vecP e p (fun i => (y i : ℚ_[p])) := by
  simp only [vecG, vecP, tmul_sum, tmul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul ℚ_[p] (y i), eq_ratCast]

theorem vecP_eq (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℚ_[p]) :
    vecP e p ξ = (Algebra.TensorProduct.basis ℚ_[p] e).equivFun.symm ξ := by
  simp [vecP, Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply]

theorem Q_vecP (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℚ_[p]) :
    Q.baseChange ℚ_[p] (vecP e p ξ) = ξ ⬝ᵥ (gram Q e).map (algebraMap ℚ ℚ_[p]) *ᵥ ξ := by
  rw [eq_dotProduct_gram _ (Algebra.TensorProduct.basis ℚ_[p] e), vecP_eq, LinearEquiv.apply_symm_apply]
  have : ⇑(Algebra.TensorProduct.basis ℚ_[p] e) = fun i => (1 : ℚ_[p]) ⊗ₜ[ℚ] e i := by
    funext i; exact Algebra.TensorProduct.basis_apply e i
  rw [this, gram_baseChange]

theorem Q_vecG (y : Fin n → ℚ) : Q (vecG e y) = y ⬝ᵥ gram Q e *ᵥ y := by
  have : vecG e y = e.equivFun.symm y := by simp [vecG, Basis.equivFun_symm_apply]
  rw [eq_dotProduct_gram _ e, this, LinearEquiv.apply_symm_apply]

variable {Q e}

/-- The integral form `ofMatrixZ N` is $D\,Q$ in the coordinates of $V_p$. -/
theorem f_vecP {N : Matrix (Fin n) (Fin n) ℤ} (hNs : Nᵀ = N) {D : ℕ}
    (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e) (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℚ_[p]) :
    (LocalDensity.ofMatrixZ N).evalIn ℚ_[p] ξ = D * Q.baseChange ℚ_[p] (vecP e p ξ) := by
  rw [evalIn_ofMatrixZ N hNs, Q_vecP]
  have : N.map (Int.cast : ℤ → ℚ_[p]) = (D : ℚ_[p]) • (gram Q e).map (algebraMap ℚ ℚ_[p]) := by
    ext i j
    have := congrFun (congrFun hND i) j
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [← Rat.cast_intCast, this, Rat.cast_mul, Rat.cast_natCast, eq_ratCast]
  rw [this, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The integral form `ofMatrixZ N` is $D\,Q$ in rational coordinates. -/
theorem f_vecG {N : Matrix (Fin n) (Fin n) ℤ} (hNs : Nᵀ = N) {D : ℕ}
    (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e) (y : Fin n → ℚ) :
    (LocalDensity.ofMatrixZ N).evalIn ℚ y = D * Q (vecG e y) := by
  rw [evalIn_ofMatrixZ N hNs, Q_vecG, hND, smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Evaluation of an integral form commutes with $\mathbb Q \to \mathbb Q_p$. -/
theorem evalIn_cast {m : ℕ} (f : QuadForm ℤ m) (p : ℕ) [Fact p.Prime] (y : Fin m → ℚ) :
    f.evalIn ℚ_[p] (fun i => (y i : ℚ_[p])) = (f.evalIn ℚ y : ℚ_[p]) := by
  simp only [QuadForm.evalIn, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- The map $\xi \mapsto \iota(\sum_i \xi_i(1 \otimes e_i))$ is continuous. -/
theorem continuous_ι_vecP (p : ℕ) [Fact p.Prime] :
    Continuous fun ξ : Fin n → ℚ_[p] => ι (Q.baseChange ℚ_[p]) (vecP e p ξ) := by
  have : ContinuousAdd (CliffordAlgebra (Q.baseChange ℚ_[p])) := IsModuleTopology.toContinuousAdd ℚ_[p] _
  have : ContinuousSMul ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
    IsModuleTopology.toContinuousSMul ℚ_[p] _
  simp only [vecP, map_sum, map_smul]
  fun_prop

/-- The map $\xi \mapsto Q(\sum_i \xi_i(1 \otimes e_i))$ is continuous. -/
theorem continuous_Q_vecP (p : ℕ) [Fact p.Prime] :
    Continuous fun ξ : Fin n → ℚ_[p] => Q.baseChange ℚ_[p] (vecP e p ξ) := by
  simp only [Q_vecP, dotProduct, mulVec]
  fun_prop

end Setup

section Close

variable {n : ℕ} (p : ℕ) [Fact p.Prime]

/-- **$p$-adic closeness of coordinates**: $|x_i - y_i|_p \le p^{-K}$ for all $i$. -/
def Close (K : ℕ) (x y : Fin n → ℚ_[p]) : Prop := ∀ i, ‖x i - y i‖ ≤ (p : ℝ) ^ (-(K : ℤ))

variable {p}

theorem Close.mono {K K' : ℕ} (h : K' ≤ K) {x y : Fin n → ℚ_[p]} (hc : Close p K x y) : Close p K' x y := by
  intro i
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact (hc i).trans (zpow_le_zpow_right₀ hp1 (by omega))

theorem Close.trans {K : ℕ} {x y z : Fin n → ℚ_[p]} (h1 : Close p K x y) (h2 : Close p K y z) :
    Close p K x z := by
  intro i
  have := Padic.nonarchimedean (x i - y i) (y i - z i)
  rw [sub_add_sub_cancel] at this
  exact this.trans (max_le (h1 i) (h2 i))

theorem Close.symm {K : ℕ} {x y : Fin n → ℚ_[p]} (h : Close p K x y) : Close p K y x := by
  intro i; rw [← norm_neg, neg_sub]; exact h i

theorem close_self (K : ℕ) (x : Fin n → ℚ_[p]) : Close p K x x := by
  intro i; simp

/-- Helper: $p^{-K} < \varepsilon$ for large $K$. -/
theorem exists_pow_lt {ε : ℝ} (hε : 0 < ε) : ∃ K : ℕ, (p : ℝ) ^ (-(K : ℤ)) < ε := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  exact ⟨K, by rwa [_root_.zpow_neg, zpow_natCast, ← inv_pow]⟩

theorem dist_lt_of_close {K : ℕ} {ε : ℝ} (hε : 0 < ε) (hK : (p : ℝ) ^ (-(K : ℤ)) < ε) {x y : Fin n → ℚ_[p]}
    (h : Close p K x y) : dist x y < ε := by
  rw [dist_pi_lt_iff hε]
  intro i
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (h i) hK

/-- **Closeness neighbourhoods of a continuous function of one coordinate vector.** -/
theorem exists_close₁ {X : Type*} [TopologicalSpace X] {F : (Fin n → ℚ_[p]) → X} {x₀ : Fin n → ℚ_[p]}
    (hF : ContinuousAt F x₀) {S : Set X} (hS : S ∈ 𝓝 (F x₀)) :
    ∃ K : ℕ, ∀ x, Close p K x x₀ → F x ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hF hS)
  obtain ⟨K, hK⟩ := exists_pow_lt (p := p) hε
  exact ⟨K, fun x hx => hball (dist_lt_of_close hε hK hx)⟩

/-- **Closeness neighbourhoods of a continuous function of two coordinate vectors.** -/
theorem exists_close₂ {X : Type*} [TopologicalSpace X] {F : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) → X}
    {x₀ y₀ : Fin n → ℚ_[p]} (hF : ContinuousAt F (x₀, y₀)) {S : Set X} (hS : S ∈ 𝓝 (F (x₀, y₀))) :
    ∃ K : ℕ, ∀ x y, Close p K x x₀ → Close p K y y₀ → F (x, y) ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hF hS)
  obtain ⟨K, hK⟩ := exists_pow_lt (p := p) hε
  refine ⟨K, fun x y hx hy => hball ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨dist_lt_of_close hε hK hx, dist_lt_of_close hε hK hy⟩

/-- The closeness set is a neighbourhood. -/
theorem close_mem_nhds (K : ℕ) (x₀ : Fin n → ℚ_[p]) : {x | Close p K x x₀} ∈ 𝓝 x₀ := by
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(K : ℤ)) := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hpos) fun x hx => ?_
  intro i
  have := (dist_pi_lt_iff hpos).1 (Metric.mem_ball.1 hx) i
  rw [dist_eq_norm] at this
  exact this.le

end Close

section Reflect

variable {k W : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup W] [Module k W] (Q : QuadraticForm k W)

/-- **Cassels' vector $c = -\tau_b a$** (p. 190: $bab = \phi(b)c$): $c = Q(b)^{-1}(B(b, a)b - Q(b)a)$ with the polar form
$B(x, y) = Q(x + y) - Q(x) - Q(y)$. Arguments: `Q`, `b`, `a`. -/
noncomputable def cvec (b a : W) : W := (Q b)⁻¹ • (QuadraticMap.polar Q b a • b - Q b • a)

variable {Q}

/-- $bab = Q(b)\,c$ (Cassels (3.1), p. 190). -/
theorem ι_mul_ι_mul_ι_eq_cvec {a b : W} (hb : Q b ≠ 0) :
    ι Q b * ι Q a * ι Q b = Q b • ι Q (cvec Q b a) := by
  rw [ι_mul_ι_mul_ι, cvec, map_smul, smul_smul, mul_inv_cancel₀ hb, one_smul]

/-- $\phi(c) = \phi(a)$ (Cassels (7.12)). -/
theorem Q_cvec {a b : W} (hb : Q b ≠ 0) : Q (cvec Q b a) = Q a := by
  set t := QuadraticMap.polar Q b a
  have h1 : Q (t • b - Q b • a) = t ^ 2 * Q b + Q b ^ 2 * Q a - t * Q b * t := by
    have hp : QuadraticMap.polar Q (t • b) (-(Q b • a)) = -(t * Q b * t) := by
      rw [QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul, t]; ring
    unfold QuadraticMap.polar at hp
    rw [QuadraticMap.map_neg, QuadraticMap.map_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul] at hp
    rw [sub_eq_add_neg]
    linear_combination hp
  rw [cvec, QuadraticMap.map_smul, h1, smul_eq_mul]
  field_simp
  ring

end Reflect

section Coords2

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}
  {n : ℕ} (e : Basis (Fin n) ℚ V)

theorem vecP_sub (p : ℕ) [Fact p.Prime] (x y : Fin n → ℚ_[p]) : vecP e p (x - y) = vecP e p x - vecP e p y := by
  simp only [vecP, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem vecP_smul (p : ℕ) [Fact p.Prime] (c : ℚ_[p]) (x : Fin n → ℚ_[p]) : vecP e p (c • x) = c • vecP e p x := by
  simp only [vecP, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vecG_sub (x y : Fin n → ℚ) : vecG e (x - y) = vecG e x - vecG e y := by
  simp only [vecG, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem vecG_smul (c : ℚ) (x : Fin n → ℚ) : vecG e (c • x) = c • vecG e x := by
  simp only [vecG, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vecG_injective : Function.Injective (vecG e) := by
  intro x y h
  have : e.equivFun.symm x = e.equivFun.symm y := by simpa [vecG, Basis.equivFun_symm_apply] using h
  exact e.equivFun.symm.injective this

variable (Q)

/-- The coordinates of Cassels' $c$ in $V_p$: $\mathrm{cco}(\zeta, \xi)$ has `vecP` equal to `cvec` of the vectors with
coordinates $\zeta$ ($b$) and $\xi$ ($a$). -/
noncomputable def ccoP (p : ℕ) [Fact p.Prime] (ζ ξ : Fin n → ℚ_[p]) : Fin n → ℚ_[p] :=
  (Q.baseChange ℚ_[p] (vecP e p ζ))⁻¹ •
    (QuadraticMap.polar (Q.baseChange ℚ_[p]) (vecP e p ζ) (vecP e p ξ) • ζ - Q.baseChange ℚ_[p] (vecP e p ζ) • ξ)

/-- The rational coordinates of Cassels' $c$. -/
noncomputable def ccoG (ζ ξ : Fin n → ℚ) : Fin n → ℚ :=
  (Q (vecG e ζ))⁻¹ • (QuadraticMap.polar Q (vecG e ζ) (vecG e ξ) • ζ - Q (vecG e ζ) • ξ)

variable {Q}

theorem vecP_ccoP (p : ℕ) [Fact p.Prime] (ζ ξ : Fin n → ℚ_[p]) :
    vecP e p (ccoP Q e p ζ ξ) = cvec (Q.baseChange ℚ_[p]) (vecP e p ζ) (vecP e p ξ) := by
  rw [ccoP, vecP_smul, vecP_sub, vecP_smul, vecP_smul, cvec]

theorem vecG_ccoG (ζ ξ : Fin n → ℚ) : vecG e (ccoG Q e ζ ξ) = cvec Q (vecG e ζ) (vecG e ξ) := by
  rw [ccoG, vecG_smul, vecG_sub, vecG_smul, vecG_smul, cvec]

theorem Q_one_tmul (p : ℕ) [Fact p.Prime] (x : V) :
    Q.baseChange ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ[ℚ] x) = (Q x : ℚ_[p]) := by
  rw [QuadraticForm.baseChange_tmul, mul_one, Algebra.smul_def, mul_one, eq_ratCast]

theorem polar_one_tmul (p : ℕ) [Fact p.Prime] (x y : V) :
    QuadraticMap.polar (Q.baseChange ℚ_[p]) ((1 : ℚ_[p]) ⊗ₜ[ℚ] x) ((1 : ℚ_[p]) ⊗ₜ[ℚ] y) =
      (((QuadraticMap.polar (⇑Q) x y : ℚ)) : ℚ_[p]) := by
  simp only [QuadraticMap.polar, ← tmul_add, Q_one_tmul, Rat.cast_sub]

theorem Q_vecP_cast (p : ℕ) [Fact p.Prime] (y : Fin n → ℚ) :
    Q.baseChange ℚ_[p] (vecP e p fun i => (y i : ℚ_[p])) = (Q (vecG e y) : ℚ_[p]) := by
  rw [← one_tmul_vecG, Q_one_tmul]

theorem ccoG_cast (p : ℕ) [Fact p.Prime] (ζ ξ : Fin n → ℚ) :
    (fun i => (ccoG Q e ζ ξ i : ℚ_[p])) = ccoP Q e p (fun i => (ζ i : ℚ_[p])) (fun i => (ξ i : ℚ_[p])) := by
  funext i
  simp only [ccoG, ccoP, ← one_tmul_vecG, Q_one_tmul, polar_one_tmul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- Continuity of the coordinates of Cassels' $c$ at a point where $Q(b) \ne 0$. -/
theorem continuousAt_ccoP (p : ℕ) [Fact p.Prime] {ζ₀ ξ₀ : Fin n → ℚ_[p]} (h : Q.baseChange ℚ_[p] (vecP e p ζ₀) ≠ 0) :
    ContinuousAt (fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) => ccoP Q e p z.1 z.2) (ζ₀, ξ₀) := by
  have hQc := continuous_Q_vecP (Q := Q) (e := e) p
  have hpol : Continuous fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) =>
      QuadraticMap.polar (Q.baseChange ℚ_[p]) (vecP e p z.1) (vecP e p z.2) := by
    have : ∀ z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]), QuadraticMap.polar (Q.baseChange ℚ_[p]) (vecP e p z.1)
        (vecP e p z.2) = Q.baseChange ℚ_[p] (vecP e p (z.1 + z.2)) - Q.baseChange ℚ_[p] (vecP e p z.1) -
          Q.baseChange ℚ_[p] (vecP e p z.2) := by
      intro z
      have : vecP e p (z.1 + z.2) = vecP e p z.1 + vecP e p z.2 := by
        simp only [vecP, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      rw [this]; rfl
    simp only [this]
    exact ((hQc.comp (continuous_fst.add continuous_snd)).sub (hQc.comp continuous_fst)).sub
      (hQc.comp continuous_snd)
  have hinv : ContinuousAt (fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) =>
      (Q.baseChange ℚ_[p] (vecP e p z.1))⁻¹) (ζ₀, ξ₀) :=
    ((hQc.comp continuous_fst).continuousAt).inv₀ h
  unfold ccoP
  exact hinv.smul ((hpol.continuousAt.smul continuous_fst.continuousAt).sub
    ((hQc.comp continuous_fst).continuousAt.smul continuous_snd.continuousAt))

end Coords2

section Approx

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (Q : QuadraticForm ℚ V)
  (Λ : Submodule ℤ V)

/-- **The approximation property at a finite set $T$ of primes** of a family $t_p \in C(V_p)$: for all open
$\mathcal O_p \ni t_p$ ($p \in T$) there is $u \in \operatorname{Spin}(V)$ with $u \in \mathcal O_p$ for $p \in T$ and
$u \in \operatorname{Spin}(\Lambda_p)$ for $p \notin T$. Arguments: `Q`, `Λ`, `T`, the family `t`. -/
def SpinApprox (T : Finset Nat.Primes) (t : ∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])) : Prop :=
  ∀ O : ∀ p : Nat.Primes, Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])),
    (∀ p ∈ T, IsOpen (O p) ∧ t p ∈ O p) →
    ∃ u : spinGroup Q, (∀ p ∈ T, (spinBaseChange ℚ_[(p : ℕ)] Q u : CliffordAlgebra _) ∈ O p) ∧
      ∀ p : Nat.Primes, p ∉ T →
        spinBaseChange ℚ_[(p : ℕ)] Q u ∈ intSpin (Q := Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ)

variable {Q Λ}

theorem SpinApprox.one (T : Finset Nat.Primes) : SpinApprox Q Λ T fun _ => 1 := by
  intro O hO
  refine ⟨1, fun p hp => ?_, fun p _ => ?_⟩
  · rw [map_one]; exact (hO p hp).2
  · rw [map_one]; exact one_mem _

theorem SpinApprox.mul {T : Finset Nat.Primes} {t t' : ∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])}
    (h : SpinApprox Q Λ T t) (h' : SpinApprox Q Λ T t') : SpinApprox Q Λ T fun p => t p * t' p := by
  intro O hO
  have key : ∀ p : Nat.Primes, ∃ O₁ O₂ : Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])),
      p ∈ T → IsOpen O₁ ∧ t p ∈ O₁ ∧ IsOpen O₂ ∧ t' p ∈ O₂ ∧ ∀ x ∈ O₁, ∀ y ∈ O₂, x * y ∈ O p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨hOo, hOm⟩ := hO p hp
      have hpre : IsOpen ((fun z : CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)]) × _ => z.1 * z.2) ⁻¹' O p) :=
        hOo.preimage continuous_mul
      obtain ⟨O₁, O₂, h₁, h₂, hm₁, hm₂, hsub⟩ := isOpen_prod_iff.1 hpre (t p) (t' p) hOm
      exact ⟨O₁, O₂, fun _ => ⟨h₁, hm₁, h₂, hm₂, fun x hx y hy => hsub (Set.mk_mem_prod hx hy)⟩⟩
    · exact ⟨∅, ∅, fun h => absurd h hp⟩
  choose O₁ O₂ hO₁₂ using key
  obtain ⟨u, hu₁, hu₂⟩ := h O₁ fun p hp => ⟨(hO₁₂ p hp).1, (hO₁₂ p hp).2.1⟩
  obtain ⟨u', hu₁', hu₂'⟩ := h' O₂ fun p hp => ⟨(hO₁₂ p hp).2.2.1, (hO₁₂ p hp).2.2.2.1⟩
  refine ⟨u * u', fun p hp => ?_, fun p hp => ?_⟩
  · rw [map_mul, Submonoid.coe_mul]
    exact (hO₁₂ p hp).2.2.2.2 _ (hu₁ p hp) _ (hu₁' p hp)
  · rw [map_mul]; exact mul_mem (hu₂ p hp) (hu₂' p hp)

theorem SpinApprox.list_prod {T : Finset Nat.Primes}
    (L : List (∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])))
    (h : ∀ t ∈ L, SpinApprox Q Λ T t) : SpinApprox Q Λ T fun p => (L.map fun t => t p).prod := by
  induction L with
  | nil => simpa using SpinApprox.one (Q := Q) (Λ := Λ) T
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h t List.mem_cons_self).mul (ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))

/-- **Theorem 7.1 from the approximation property**: if a family $t_p \in \mathcal U_p$ ($p \in T$) has the approximation
property and $\mathcal U_p = \operatorname{Spin}(\Lambda_p)$ outside $T$, some $u \in \operatorname{Spin}(V)$ lies in every $\mathcal U_p$. -/
theorem SpinApprox.exists_mem {T : Finset Nat.Primes}
    {t : ∀ p : Nat.Primes, CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])} (h : SpinApprox Q Λ T t)
    (U : ∀ (p : ℕ) [Fact p.Prime], Set (spinGroup (Q.baseChange ℚ_[p])))
    (hopen : ∀ (p : ℕ) [Fact p.Prime],
      @IsOpen _ (@instTopologicalSpaceSubtype _ _ (cliffordTopology (Q.baseChange ℚ_[p]))) (U p))
    (ht : ∀ p ∈ T, ∃ w ∈ U p, (w : CliffordAlgebra _) = t p)
    (hout : ∀ p : Nat.Primes, p ∉ T →
      U p = (intSpin (Q := Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ) : Set _)) :
    ∃ u : spinGroup Q, ∀ (p : ℕ) [Fact p.Prime], spinBaseChange ℚ_[p] Q u ∈ U p := by
  classical
  have key : ∀ p : Nat.Primes, ∃ O : Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)])),
      IsOpen O ∧ Subtype.val ⁻¹' O = U p :=
    fun p => isOpen_induced_iff.1 (hopen p)
  choose O hO hOU using key
  obtain ⟨u, hu₁, hu₂⟩ := h O fun p hp => by
    refine ⟨hO p, ?_⟩
    obtain ⟨w, hw, hwt⟩ := ht p hp
    rw [← hwt]
    have : w ∈ Subtype.val ⁻¹' O p := by rw [hOU]; exact hw
    exact this
  refine ⟨u, fun p hp => ?_⟩
  set pp : Nat.Primes := ⟨p, hp.out⟩
  by_cases hT : pp ∈ T
  · have := hu₁ pp hT
    change spinBaseChange ℚ_[p] Q u ∈ U p
    rw [← hOU pp]
    exact this
  · have := hu₂ pp hT
    change spinBaseChange ℚ_[p] Q u ∈ U p
    rw [hout pp hT]
    exact this

end Approx

section RatNorm

variable {p : ℕ} [Fact p.Prime]

/-- Helper: a rational whose denominator is prime to $p$ is a $p$-adic integer. -/
theorem norm_rat_le_one (r : ℚ) (h : ¬ p ∣ r.den) : ‖(r : ℚ_[p])‖ ≤ 1 := by
  rw [Rat.cast_def, norm_div]
  have hd : ‖((r.den : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h
  rw [hd, div_one]
  exact Padic.norm_int_le_one _

/-- Helper: a rational whose numerator and denominator are prime to $p$ is a $p$-adic unit. -/
theorem norm_rat_eq_one (r : ℚ) (h₁ : ¬ p ∣ r.den) (h₂ : ¬ p ∣ r.num.natAbs) : ‖(r : ℚ_[p])‖ = 1 := by
  rw [Rat.cast_def, norm_div]
  have hd : ‖((r.den : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h₁
  have hn : ‖((r.num : ℤ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_intCast_eq_one_iff, Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simp only [Int.gcd, Int.natAbs_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h₂
  rw [hd, hn, div_one]

end RatNorm

section Lemma72

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] {Q : QuadraticForm ℚ V}
  {Λ : Submodule ℤ V} {n : ℕ} (e : Basis (Fin n) ℚ V)

variable (Q) in
/-- The element $\phi(a)^{-1}ac$ of $C(V_p)$ for coordinates $\xi$ of $a$ and $\eta$ of $c$ (Cassels, p. 190:
$u = m^{-1}ad$). -/
noncomputable def phiP (p : ℕ) [Fact p.Prime] (ξ η : Fin n → ℚ_[p]) : CliffordAlgebra (Q.baseChange ℚ_[p]) :=
  (Q.baseChange ℚ_[p] (vecP e p ξ))⁻¹ • (ι _ (vecP e p ξ) * ι _ (vecP e p η))

theorem continuousAt_phiP (p : ℕ) [Fact p.Prime] {ξ₀ η₀ : Fin n → ℚ_[p]}
    (h : Q.baseChange ℚ_[p] (vecP e p ξ₀) ≠ 0) :
    ContinuousAt (fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) => phiP Q e p z.1 z.2) (ξ₀, η₀) := by
  have : ContinuousSMul ℚ_[p] (CliffordAlgebra (Q.baseChange ℚ_[p])) :=
    IsModuleTopology.toContinuousSMul ℚ_[p] _
  have hQc := continuous_Q_vecP (Q := Q) (e := e) p
  have hι := continuous_ι_vecP (Q := Q) (e := e) p
  have h1 : ContinuousAt (fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) =>
      (Q.baseChange ℚ_[p] (vecP e p z.1))⁻¹) (ξ₀, η₀) :=
    ContinuousAt.inv₀ (hQc.comp continuous_fst).continuousAt h
  have h2 : Continuous (fun z : (Fin n → ℚ_[p]) × (Fin n → ℚ_[p]) =>
      ι (Q.baseChange ℚ_[p]) (vecP e p z.1) * ι (Q.baseChange ℚ_[p]) (vecP e p z.2)) :=
    (hι.comp continuous_fst).mul (hι.comp continuous_snd)
  exact h1.smul h2.continuousAt

/-- Cassels' commutator in terms of $c$: $\{\phi(a)\}^{-1}\{\phi(b)\}^{-1}abab = \phi(a)^{-1}ac$. -/
theorem vprod_vcommList_eq_phiP (p : ℕ) [Fact p.Prime] (ξ ζ : Fin n → ℚ_[p])
    (hb : Q.baseChange ℚ_[p] (vecP e p ζ) ≠ 0) :
    vprod (Q.baseChange ℚ_[p]) (vcommList (Q.baseChange ℚ_[p]) (vecP e p ξ) (vecP e p ζ)) =
      phiP Q e p ξ (ccoP Q e p ζ ξ) := by
  rw [phiP, vecP_ccoP]
  set A := vecP e p ξ
  set B := vecP e p ζ
  have hc := ι_mul_ι_mul_ι_eq_cvec (a := A) hb
  have hc' : ι (Q.baseChange ℚ_[p]) (cvec (Q.baseChange ℚ_[p]) B A) =
      (Q.baseChange ℚ_[p] B)⁻¹ • (ι _ B * ι _ A * ι _ B) := by
    rw [hc, smul_smul, inv_mul_cancel₀ hb, one_smul]
  rw [hc']
  simp only [vprod, vcommList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_smul]
  simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
  exact smul_comm _ _ _

theorem phiP_self (p : ℕ) [Fact p.Prime] (ξ : Fin n → ℚ_[p]) (h : Q.baseChange ℚ_[p] (vecP e p ξ) ≠ 0) :
    phiP Q e p ξ ξ = 1 := by
  rw [phiP, ι_sq_scalar, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- Helper: vectors with $p$-integral coordinates lie in $\Lambda_p$. -/
theorem vecP_mem (he : ∀ i, e i ∈ Λ) (p : ℕ) [Fact p.Prime] {ξ : Fin n → ℚ_[p]} (hξ : ∀ i, ‖ξ i‖ ≤ 1) :
    vecP e p ξ ∈ baseChangeLat ℚ_[p] ℤ_[p] Λ := by
  refine Submodule.sum_mem _ fun i _ => ?_
  have : ξ i • ((1 : ℚ_[p]) ⊗ₜ[ℚ] e i) = toZp (ξ i) • ((1 : ℚ_[p]) ⊗ₜ[ℚ] e i) := by
    rw [← algebraMap_smul ℚ_[p] (toZp (ξ i))]
    congr 1
    exact (coe_toZp (hξ i)).symm
  rw [this]
  exact Submodule.smul_mem _ _ (one_tmul_mem_baseChangeLat (he i))

/-- Helper: $\Lambda_p$ spans $V_p$. -/
theorem span_baseChangeLat (he : ∀ i, e i ∈ Λ) (p : ℕ) [Fact p.Prime] :
    Submodule.span ℚ_[p] ((baseChangeLat ℚ_[p] ℤ_[p] Λ : Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)) : Set (ℚ_[p] ⊗[ℚ] V)) =
      ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = vecP e p ((Algebra.TensorProduct.basis ℚ_[p] e).equivFun x) := by
    rw [vecP_eq, LinearEquiv.symm_apply_apply]
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact one_tmul_mem_baseChangeLat (he i)

/-- Helper: the integral model of a regular form is regular. -/
theorem det_hessian_ne_zero (hQ : (QuadraticMap.associated Q).Nondegenerate) {N : Matrix (Fin n) (Fin n) ℤ}
    (hNs : Nᵀ = N) {D : ℕ} (hD : 0 < D) (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e) :
    (LocalDensity.ofMatrixZ N).hessian.det ≠ 0 := by
  rw [det_hessian_ofMatrixZ N hNs]
  have h1 : ((N.det : ℤ) : ℚ) = (D : ℚ) ^ n * (gram Q e).det := by
    rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]
    change (N.map (Int.cast : ℤ → ℚ)).det = _
    rw [hND, det_smul, Fintype.card_fin]
  have h2 : (N.det : ℚ) ≠ 0 := by
    rw [h1]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD.ne')) (det_gram_ne_zero hQ e)
  have h3 : N.det ≠ 0 := by exact_mod_cast h2
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero) h3

/-- **Cassels, Ch. 10, Lemma 7.2** (p. 190), as an approximation property. Let $n \ge 4$ ($e$ a basis of $V$ in $\Lambda$, `he`),
$Q$ regular and indefinite (`hfind`, for the integral model $f$ = `ofMatrixZ N` of $D\,Q$), and let the finite set $T$ of primes
contain $2$ and every prime dividing the Hessian determinant of $f$ (`hT2`, `hTd`; Cassels' (i)–(iii)). For $p \in T$ let
$a_p, b_p \in V_p$ (coordinates `a p`, `b p`) be anisotropic (`ha`, `hb`). Then the family of commutators
$w_p = \{\phi(a_p)\}^{-1}\{\phi(b_p)\}^{-1}a_pb_pa_pb_p$ has the approximation property at $T$: there is $u \in \operatorname{Spin}(V)$
arbitrarily close to every $w_p$, $p \in T$, with $u \in \operatorname{Spin}(\Lambda_p)$ for $p \notin T$. Proof: Cassels' (rational
$a$, $b$ close to $a_p$, $b_p$; $c = -\tau_ba$; $d$ from Lemma 7.1 with $\phi(d) = \phi(a) = m$, close to $c$ on $T$ and to $a$ on
the finite set $P_0$ of (7.13), (7.14); $u = m^{-1}ad$). -/
@[kb "cassels1978" "Ch. 10, Lemma 7.2, p. 190"]
theorem lemma72 (hQ : (QuadraticMap.associated Q).Nondegenerate) (hn : 4 ≤ n) (he : ∀ i, e i ∈ Λ)
    {N : Matrix (Fin n) (Fin n) ℤ} (hNs : Nᵀ = N) {D : ℕ} (hD : 0 < D)
    (hND : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • gram Q e)
    (hfind : ∃ x y : Fin n → ℝ, (LocalDensity.ofMatrixZ N).evalIn ℝ x < 0 ∧ 0 < (LocalDensity.ofMatrixZ N).evalIn ℝ y)
    (T : Finset Nat.Primes) (hT2 : ∀ p : Nat.Primes, p ∉ T → (p : ℕ) ≠ 2)
    (hTd : ∀ p : Nat.Primes, p ∉ T → ¬ ((p : ℕ) : ℤ) ∣ (LocalDensity.ofMatrixZ N).hessian.det)
    (a b : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)])
    (ha : ∀ p ∈ T, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p)) ≠ 0)
    (hb : ∀ p ∈ T, Q.baseChange ℚ_[(p : ℕ)] (vecP e p (b p)) ≠ 0) :
    SpinApprox Q Λ T fun p =>
      vprod (Q.baseChange ℚ_[(p : ℕ)]) (vcommList (Q.baseChange ℚ_[(p : ℕ)]) (vecP e p (a p)) (vecP e p (b p))) := by
  classical
  intro O hO
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · exact ⟨1, fun p hp => by simp [hTe] at hp, fun p _ => by rw [map_one]; exact one_mem _⟩
  set f := LocalDensity.ofMatrixZ N with hfdef
  have hfdet : f.hessian.det ≠ 0 := det_hessian_ne_zero e hQ hNs hD hND
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  set cP : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)] := fun p => ccoP Q e p (b p) (a p) with hcP
  -- precision for the target $w_p = \phi(a)^{-1}ac$
  have hK1 : ∀ p : Nat.Primes, ∃ K : ℕ, p ∈ T → ∀ x y, Close p K x (a p) → Close p K y (cP p) →
      phiP Q e p x y ∈ O p := by
    intro p
    by_cases hp : p ∈ T
    · have hmem : phiP Q e p (a p) (cP p) ∈ O p := by
        rw [← vprod_vcommList_eq_phiP e p _ _ (hb p hp)]; exact (hO p hp).2
      obtain ⟨K, hK⟩ := exists_close₂ (continuousAt_phiP e p (η₀ := cP p) (ha p hp))
        ((hO p hp).1.mem_nhds hmem)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose K1 hK1 using hK1
  -- precision for $c$
  have hK2 : ∀ p : Nat.Primes, ∃ K : ℕ, p ∈ T → ∀ ζ ξ, Close p K ζ (b p) → Close p K ξ (a p) →
      Close p (K1 p) (ccoP Q e p ζ ξ) (cP p) := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨K, hK⟩ := exists_close₂ (continuousAt_ccoP e p (ξ₀ := a p) (hb p hp)) (close_mem_nhds (K1 p) (cP p))
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose K2 hK2 using hK2
  -- precision for anisotropy
  have hK0 : ∀ p : Nat.Primes, ∃ K : ℕ, p ∈ T → ∀ ξ ζ, Close p K ξ (a p) → Close p K ζ (b p) →
      Q.baseChange ℚ_[(p : ℕ)] (vecP e p ξ) ≠ 0 ∧ Q.baseChange ℚ_[(p : ℕ)] (vecP e p ζ) ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · have hc : Continuous fun z : (Fin n → ℚ_[(p : ℕ)]) × (Fin n → ℚ_[(p : ℕ)]) =>
          (Q.baseChange ℚ_[(p : ℕ)] (vecP e p z.1), Q.baseChange ℚ_[(p : ℕ)] (vecP e p z.2)) :=
        ((continuous_Q_vecP (Q := Q) (e := e) p).comp continuous_fst).prodMk
          ((continuous_Q_vecP (Q := Q) (e := e) p).comp continuous_snd)
      have hS : {w : ℚ_[(p : ℕ)] × ℚ_[(p : ℕ)] | w.1 ≠ 0 ∧ w.2 ≠ 0} ∈
          𝓝 (Q.baseChange ℚ_[(p : ℕ)] (vecP e p (a p)), Q.baseChange ℚ_[(p : ℕ)] (vecP e p (b p))) :=
        ((isOpen_ne.preimage continuous_fst).inter (isOpen_ne.preimage continuous_snd)).mem_nhds
          ⟨ha p hp, hb p hp⟩
      obtain ⟨K, hK⟩ := exists_close₂ hc.continuousAt hS
      exact ⟨K, fun _ ξ ζ h1 h2 => hK ξ ζ h1 h2⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose K0 hK0 using hK0
  set KA : ℕ := T.sup fun p => max (K1 p) (max (K2 p) (K0 p)) with hKA
  have hKA1 : ∀ p ∈ T, K1 p ≤ KA := fun p hp => le_trans (le_max_left _ _) (Finset.le_sup (f := fun p =>
    max (K1 p) (max (K2 p) (K0 p))) hp)
  have hKA2 : ∀ p ∈ T, K2 p ≤ KA := fun p hp => le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (Finset.le_sup (f := fun p => max (K1 p) (max (K2 p) (K0 p))) hp)
  have hKA0 : ∀ p ∈ T, K0 p ≤ KA := fun p hp => le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (Finset.le_sup (f := fun p => max (K1 p) (max (K2 p) (K0 p))) hp)
  -- global $a$, $b$ (weak approximation)
  have hya := fun i => exists_rat_approx T (fun p => a p i) KA
  have hyb := fun i => exists_rat_approx T (fun p => b p i) KA
  choose ya hya using hya
  choose yb hyb using hyb
  have hcya : ∀ p ∈ T, Close p KA (fun i => (ya i : ℚ_[(p : ℕ)])) (a p) := fun p hp i => hya i p hp
  have hcyb : ∀ p ∈ T, Close p KA (fun i => (yb i : ℚ_[(p : ℕ)])) (b p) := fun p hp i => hyb i p hp
  set m : ℚ := Q (vecG e ya) with hm
  obtain ⟨p₀, hp₀⟩ := hTne
  have hnz := hK0 p₀ hp₀ _ _ ((hcya p₀ hp₀).mono (hKA0 p₀ hp₀)) ((hcyb p₀ hp₀).mono (hKA0 p₀ hp₀))
  rw [Q_vecP_cast, Q_vecP_cast] at hnz
  have hm0 : m ≠ 0 := fun h => hnz.1 (by rw [← hm, h, Rat.cast_zero])
  have hQb : Q (vecG e yb) ≠ 0 := fun h => hnz.2 (by rw [h, Rat.cast_zero])
  -- global $c$
  set yc := ccoG Q e yb ya with hyc
  have hQc : Q (vecG e yc) = m := by rw [hyc, vecG_ccoG, Q_cvec hQb]
  have hcyc : ∀ p ∈ T, Close p (K1 p) (fun i => (yc i : ℚ_[(p : ℕ)])) (cP p) := by
    intro p hp
    rw [hyc, ccoG_cast]
    exact hK2 p hp _ _ ((hcyb p hp).mono (hKA2 p hp)) ((hcya p hp).mono (hKA2 p hp))
  -- the finite set $P_0$ of (7.13), (7.14)
  set Bad : ℕ := (∏ i, (ya i).den * (yc i).den) * (((D : ℚ) * m).num.natAbs * ((D : ℚ) * m).den) with hBad
  have hDm : (D : ℚ) * m ≠ 0 := mul_ne_zero hD' hm0
  have hBad0 : Bad ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (ya i).den_nz (yc i).den_nz)
      (mul_ne_zero (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hDm)) ((D : ℚ) * m).den_nz)
  set P₀ : Finset Nat.Primes := Bad.primeFactors.subtype Nat.Prime with hP₀
  have hgood : ∀ p : Nat.Primes, p ∉ P₀ → (∀ i, ‖(ya i : ℚ_[(p : ℕ)])‖ ≤ 1) ∧ (∀ i, ‖(yc i : ℚ_[(p : ℕ)])‖ ≤ 1) ∧
      ‖(((D : ℚ) * m : ℚ) : ℚ_[(p : ℕ)])‖ = 1 := by
    intro p hp
    have hnd : ¬ (p : ℕ) ∣ Bad := fun h => hp (Finset.mem_subtype.2 (Nat.mem_primeFactors.2 ⟨p.2, h, hBad0⟩))
    have hprod : ∀ i, ¬ (p : ℕ) ∣ (ya i).den * (yc i).den := fun i h => hnd (dvd_mul_of_dvd_left
      (h.trans (Finset.dvd_prod_of_mem (fun j => (ya j).den * (yc j).den) (Finset.mem_univ i))) _)
    refine ⟨fun i => norm_rat_le_one _ fun h => hprod i (dvd_mul_of_dvd_left h _),
      fun i => norm_rat_le_one _ fun h => hprod i (dvd_mul_of_dvd_right h _),
      norm_rat_eq_one _ (fun h => hnd (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h _) _))
        (fun h => hnd (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _))⟩
  -- precision at $P_0$: $m^{-1}ad$ close to $m^{-1}aa = 1 \in C(\Lambda_p)$
  have hK3 : ∀ p : Nat.Primes, ∃ K : ℕ, ∀ y, Close p K y (fun i => (ya i : ℚ_[(p : ℕ)])) →
      phiP Q e p (fun i => (ya i : ℚ_[(p : ℕ)])) y ∈
        (intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ) :
          Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)]))) := by
    intro p
    have hQa : Q.baseChange ℚ_[(p : ℕ)] (vecP e p fun i => (ya i : ℚ_[(p : ℕ)])) ≠ 0 := by
      rw [Q_vecP_cast]; exact_mod_cast hm0
    have hopen := (isOpen_and_isClosed_intClifford (Q := Q.baseChange ℚ_[(p : ℕ)])
      (span_baseChangeLat e he p)).1
    have hc : ContinuousAt (fun y => phiP Q e p (fun i => (ya i : ℚ_[(p : ℕ)])) y)
        (fun i => (ya i : ℚ_[(p : ℕ)])) := by
      have := continuousAt_phiP e p (η₀ := fun i => (ya i : ℚ_[(p : ℕ)])) hQa
      exact this.comp (f := fun y => ((fun i => (ya i : ℚ_[(p : ℕ)])), y)) (by fun_prop)
    have hmem : phiP Q e p (fun i => (ya i : ℚ_[(p : ℕ)])) (fun i => (ya i : ℚ_[(p : ℕ)])) ∈
        (intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ) :
          Set (CliffordAlgebra (Q.baseChange ℚ_[(p : ℕ)]))) := by
      rw [phiP_self e p _ hQa]; exact one_mem _
    exact exists_close₁ hc (hopen.mem_nhds hmem)
  choose K3 hK3 using hK3
  set T' : Finset Nat.Primes := T ∪ P₀ with hT'
  set KK : ℕ := T'.sup fun p => max (K1 p) (K3 p) with hKK
  set z : ∀ p : Nat.Primes, Fin n → ℚ_[(p : ℕ)] := fun p =>
    if p ∈ T then (fun i => (yc i : ℚ_[(p : ℕ)])) else fun i => (ya i : ℚ_[(p : ℕ)]) with hz
  have hfz : ∀ p ∈ T', f.evalIn ℚ_[(p : ℕ)] (z p) = (((D : ℚ) * m : ℚ) : ℚ_[(p : ℕ)]) := by
    intro p _
    simp only [hz]
    split_ifs
    · rw [evalIn_cast, f_vecG hNs hND, hQc]
    · rw [evalIn_cast, f_vecG hNs hND]
  -- Lemma 7.1
  obtain ⟨yd, hyd, hydT, hydout⟩ := lemma71 f hn hfdet hfind T'
    (fun p hp => hT2 p fun h => hp (Finset.mem_union_left _ h))
    (fun p hp => hTd p fun h => hp (Finset.mem_union_left _ h)) ((D : ℚ) * m) hDm
    (fun p hp => (hgood p fun h => hp (Finset.mem_union_right _ h)).2.2.le) z hfz KK
  have hQd : Q (vecG e yd) = m := by
    rw [f_vecG hNs hND] at hyd
    exact mul_left_cancel₀ hD' hyd
  -- the element $u = m^{-1}ad$
  have : Nontrivial V := by
    have : 0 < Module.finrank ℚ V := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin]; omega
    exact Module.nontrivial_of_finrank_pos this
  have hu : vprod Q [m⁻¹ • vecG e ya, vecG e yd] ∈ spinGroup Q := by
    refine vprod_mem_spinGroup hQ (by simp) ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, QuadraticMap.map_smul, hQd, ← hm,
      smul_eq_mul, mul_one]
    field_simp
  have himg : ∀ p : Nat.Primes, (spinBaseChange ℚ_[(p : ℕ)] Q ⟨_, hu⟩ : CliffordAlgebra _) =
      phiP Q e p (fun i => (ya i : ℚ_[(p : ℕ)])) (fun i => (yd i : ℚ_[(p : ℕ)])) := by
    intro p
    rw [coe_spinBaseChange, ofBaseChangeAux_vprod]
    simp only [List.map_cons, List.map_nil, vprod, List.prod_cons, List.prod_nil, mul_one, tmul_smul]
    rw [phiP, Q_vecP_cast, ← hm, one_tmul_vecG, one_tmul_vecG, ← algebraMap_smul ℚ_[(p : ℕ)] m⁻¹, map_smul,
      smul_mul_assoc, eq_ratCast, Rat.cast_inv]
  refine ⟨⟨_, hu⟩, fun p hp => ?_, fun p hp => ?_⟩
  · rw [himg]
    refine hK1 p hp _ _ ((hcya p hp).mono (hKA1 p hp)) ?_
    have h1 : Close p KK (fun i => (yd i : ℚ_[(p : ℕ)])) (z p) := fun i => hydT p (Finset.mem_union_left _ hp) i
    have h2 : Close p (K1 p) (fun i => (yd i : ℚ_[(p : ℕ)])) (fun i => (yc i : ℚ_[(p : ℕ)])) := by
      have := h1.mono (le_trans (le_max_left _ _) (Finset.le_sup (f := fun p => max (K1 p) (K3 p))
        (Finset.mem_union_left _ hp)))
      simpa [hz, hp] using this
    exact h2.trans (hcyc p hp)
  · show (spinBaseChange ℚ_[(p : ℕ)] Q ⟨_, hu⟩ : CliffordAlgebra _) ∈
      intClifford (Q.baseChange ℚ_[(p : ℕ)]) (baseChangeLat ℚ_[(p : ℕ)] ℤ_[(p : ℕ)] Λ)
    rw [himg]
    by_cases hp0 : p ∈ P₀
    · refine hK3 p _ ?_
      have h1 : Close p KK (fun i => (yd i : ℚ_[(p : ℕ)])) (z p) :=
        fun i => hydT p (Finset.mem_union_right _ hp0) i
      have := h1.mono (le_trans (le_max_right _ _) (Finset.le_sup (f := fun p => max (K1 p) (K3 p))
        (Finset.mem_union_right _ hp0)))
      simpa [hz, hp] using this
    · obtain ⟨hga, -, hgm⟩ := hgood p hp0
      have hpT' : p ∉ T' := by simp [hT', hp, hp0]
      have hgd := hydout p hpT'
      have hminv : ‖((m⁻¹ : ℚ) : ℚ_[(p : ℕ)])‖ ≤ 1 := by
        have : (m⁻¹ : ℚ) = D * ((D : ℚ) * m)⁻¹ := by field_simp
        rw [this, Rat.cast_mul, norm_mul, Rat.cast_inv, norm_inv, hgm, inv_one, mul_one, Rat.cast_natCast]
        have := Padic.norm_int_le_one (p := (p : ℕ)) (D : ℤ)
        simpa using this
      rw [phiP, Q_vecP_cast, ← hm, ← Rat.cast_inv]
      have hs : ((m⁻¹ : ℚ) : ℚ_[(p : ℕ)]) = algebraMap ℤ_[(p : ℕ)] ℚ_[(p : ℕ)] (toZp ((m⁻¹ : ℚ) : ℚ_[(p : ℕ)])) :=
        (coe_toZp hminv).symm
      rw [hs, algebraMap_smul]
      exact Subalgebra.smul_mem _ (mul_mem (ι_mem_intClifford (vecP_mem e he p hga))
        (ι_mem_intClifford (vecP_mem e he p hgd))) _

end Lemma72

end QuadFormsKB.Cassels.Thm71Five
