/-
# Cassels, Chapter 6, §9: an approximation theorem

**Setting.** A rational form `Q : RatQF n`, regular = `Nondegenerate`, evaluated over $\mathbb Q_p$ or $\mathbb R$ with
`evalIn`. Vectors in $\mathbb Q_p^n$ and $\mathbb R^n$ carry the sup norm, which is Cassels'
$\lvert\vec a\rvert_p = \max_j\lvert a_j\rvert_p$; a rational vector $\vec c$ is viewed in them coordinatewise. The finite
set $P$ of places is a finite set $S$ of primes together with $\infty$: Cassels allows $\infty \notin P$, which is the
case $\vec b_\infty = \vec 0$ of the statements here.

**Proves** (Cassels, *Rational Quadratic Forms*, Chapter 6)
* Lemma 9.1 (a global zero close to given local zeros): `approx_zero`;
* its Corollary (a global representation close to given local representations): `approx_rep`.

**Proof notes.** As Cassels': fix a rational zero $\vec c \ne \vec 0$. Move each local zero $\vec b_v$ slightly so that
$f(\vec c, \vec b_v) \ne 0$ (Ch. 4, Lemma 2.8, `exists_zero_near_linear_ne_zero`, and its analogue over $\mathbb R$),
choose $\vec d \in \mathbb Q^n$ close to every $\vec b_v$ (weak approximation, Ch. 3, Lemma 3.2, `weak_approximation`,
coordinatewise), and take $\vec b = \lambda\vec c + \vec d$ with $\lambda = -f(\vec d)/2f(\vec c, \vec d)$, a zero of $f$
which tends to $\vec b_v$ as $\vec d \to \vec b_v$. The Corollary applies the Lemma to $g(\vec x) - az^2$ at the points
$(\vec a_p, 1)$ and divides by $z$.
-/
import QuadFormsKB.Literature.LocalGlobal.HasseMinkowski
import QuadFormsKB.Literature.Cassels.Ch3.WeakApprox
import QuadFormsKB.Literature.Cassels.Ch4.ZeroNear

namespace QuadFormsKB.Cassels.Ch6

/-- $\mathbb Q_p$ for `p : Nat.Primes` (as in `Ch3/WeakApprox.lean`). -/
local instance factPrimesSec9 (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable {n : ℕ}

section Aux

open Matrix Filter Topology

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] {n : ℕ}

/-- Cassels Ch. 4, Lemma 2.8 over an arbitrary nontrivially normed field of characteristic zero. -/
private theorem zero_near_linear_ne_zero (hn : 3 ≤ n) (F : Fin n → Fin n → K)
    (hsymm : ∀ i j, F i j = F j i) (hdet : (Matrix.of F).det ≠ 0)
    (h : Fin n → K) (hh : h ≠ 0) (b : Fin n → K) (hb : b ≠ 0) (hfb : coeffQf F b = 0) :
    ∀ U ∈ 𝓝 b, ∃ c ∈ U, coeffQf F c = 0 ∧ ∑ i, h i * c i ≠ 0 := by
  intro U hU
  by_cases hhb : h ⬝ᵥ b ≠ 0
  · exact ⟨b, mem_of_mem_nhds hU, hfb, hhb⟩
  push Not at hhb
  set M := Matrix.of F with hM
  have hsym := dotProduct_mulVec_comm_of_symm hsymm
  set u := M *ᵥ b with hu_def
  have hu : u ≠ 0 := fun h0 => hb (eq_zero_of_mulVec_eq_zero hdet h0)
  have exists_ne : ∀ v : Fin n → K, v ≠ 0 → ∃ x, v ⬝ᵥ x ≠ 0 := fun v hv => by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨Pi.single i 1, by simpa [dotProduct_single] using hi⟩
  obtain ⟨e, hue, hhe⟩ : ∃ e, u ⬝ᵥ e ≠ 0 ∧ h ⬝ᵥ e ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne u hu
    obtain ⟨y, hy⟩ := exists_ne h hh
    by_cases h1 : h ⬝ᵥ x = 0
    · by_cases h2 : u ⬝ᵥ y = 0
      · exact ⟨x + y, by simpa [dotProduct_add, h2] using hx, by simpa [dotProduct_add, h1] using hy⟩
      · exact ⟨y, h2, hy⟩
    · exact ⟨x, hx, h1⟩
  obtain ⟨w, huw, hfw⟩ : ∃ w, u ⬝ᵥ w = 0 ∧ coeffQf F w ≠ 0 := by
    set e₀ := (u ⬝ᵥ e)⁻¹ • e with he₀
    have hue₀ : u ⬝ᵥ e₀ = 1 := by
      rw [he₀, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hue]
    set L := Matrix.toLin' (Matrix.of ![u, M *ᵥ e₀]) with hL
    have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
    obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, hL, Matrix.toLin'_apply] at hvker
    have hv1 : u ⬝ᵥ v = 0 := by
      have := congrFun hvker 0
      exact this
    have hv2 : (M *ᵥ e₀) ⬝ᵥ v = 0 := by
      have := congrFun hvker 1
      exact this
    have hMv : M *ᵥ v ≠ 0 := fun h0 => hv0 (eq_zero_of_mulVec_eq_zero hdet h0)
    obtain ⟨y, hy⟩ := exists_ne _ hMv
    set y' := y - (u ⬝ᵥ y) • e₀ with hy'_def
    have huy' : u ⬝ᵥ y' = 0 := by
      rw [hy'_def, dotProduct_sub, dotProduct_smul, smul_eq_mul, hue₀, mul_one, sub_self]
    have he₀v : e₀ ⬝ᵥ (M *ᵥ v) = 0 := by rw [hsym, dotProduct_comm]; exact hv2
    have hy' : y' ⬝ᵥ (M *ᵥ v) ≠ 0 := by
      rw [hy'_def, sub_dotProduct, smul_dotProduct, he₀v, smul_zero, sub_zero, dotProduct_comm]
      exact hy
    have hexp : coeffQf F (v + y') = coeffQf F v + coeffQf F y' + 2 * (y' ⬝ᵥ (M *ᵥ v)) := by
      rw [coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, coeffQf_eq_dotProduct, ← hM, mulVec_add,
        dotProduct_add, add_dotProduct, add_dotProduct, hsym v y']
      ring
    by_cases h1 : coeffQf F v = 0
    · by_cases h2 : coeffQf F y' = 0
      · refine ⟨v + y', by rw [dotProduct_add, hv1, huy', add_zero], ?_⟩
        rw [hexp, h1, h2, zero_add, zero_add]
        exact mul_ne_zero two_ne_zero hy'
      · exact ⟨y', huy', h2⟩
    · exact ⟨v, hv1, h1⟩
  set P := u ⬝ᵥ e with hP
  set q : K → (Fin n → K) := fun μ => μ • e + w with hq
  set z : K → (Fin n → K) := fun μ => b + (-(2 * μ * P) / coeffQf F (q μ)) • q μ with hz
  have hqc : Continuous fun μ => coeffQf F (q μ) := by
    show Continuous fun μ : K => coeffQf F (μ • e + w)
    unfold coeffQf; fun_prop
  have hq0 : coeffQf F (q 0) ≠ 0 := by simpa [hq] using hfw
  have hzc : ContinuousAt z 0 := by
    show ContinuousAt (fun μ : K => b + (-(2 * μ * P) / coeffQf F (μ • e + w)) • (μ • e + w)) 0
    have hd : ContinuousAt (fun μ : K => -(2 * μ * P) / coeffQf F (μ • e + w)) 0 :=
      ContinuousAt.div (by fun_prop) hqc.continuousAt hq0
    exact continuousAt_const.add (hd.smul (by fun_prop))
  have hz0 : z 0 = b := by simp [hz]
  have h1 : ∀ᶠ μ in 𝓝 (0 : K), z μ ∈ U := hzc (by rw [hz0]; exact hU)
  have h2 : ∀ᶠ μ in 𝓝 (0 : K), coeffQf F (q μ) ≠ 0 := hqc.continuousAt.eventually_ne hq0
  have h3 : ∀ᶠ μ in 𝓝[≠] (0 : K), h ⬝ᵥ q μ ≠ 0 := by
    by_cases hw : h ⬝ᵥ w = 0
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      simp only [hq, dotProduct_add, dotProduct_smul, hw, add_zero, smul_eq_mul]
      exact mul_ne_zero hμ hhe
    · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      have : Continuous fun μ : K => h ⬝ᵥ q μ := by
        show Continuous fun μ : K => ∑ i, h i * (μ • e + w) i
        fun_prop
      exact this.continuousAt.eventually_ne (by simpa [hq] using hw)
  obtain ⟨μ, hμ0, hzU, hfq, hhq⟩ := ((eventually_mem_nhdsWithin).and ((h1.filter_mono nhdsWithin_le_nhds).and
    ((h2.filter_mono nhdsWithin_le_nhds).and h3))).exists
  have hμ0' : μ ≠ 0 := hμ0
  refine ⟨z μ, hzU, ?_, ?_⟩
  · have hbq : b ⬝ᵥ (M *ᵥ q μ) = μ * P := by
      rw [hsym, ← hu_def, hq]
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm w u, huw, add_zero,
        dotProduct_comm e u, hP]
    simp only [hz]
    rw [coeffQf_add_smul, hfb, coeffPolar_eq_two_mul_dotProduct hsymm, ← hM, hbq]
    field_simp
    ring
  · show h ⬝ᵥ z μ ≠ 0
    simp only [hz, dotProduct_add, dotProduct_smul, hhb, zero_add, smul_eq_mul]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hμ0') hue)) hfq) hhq

end Aux

section Local

open Matrix Filter Topology QuadForm

/-- The polar value `Q(x+y) - Q(x) - Q(y)` over `K`. -/
private def bil {n : ℕ} (Q : RatQF n) (K : Type*) [Field K] [Algebra ℚ K] (x y : Fin n → K) : K :=
  Q.evalIn K (x + y) - Q.evalIn K x - Q.evalIn K y

/-- The coordinatewise image of a rational vector in `K`. -/
private def ratVec {n : ℕ} (K : Type*) [Field K] [Algebra ℚ K] (c : Fin n → ℚ) : Fin n → K :=
  fun i => algebraMap ℚ K (c i)

/-- The correction factor `λ(d) = -Q(d) / B(c, d)`. -/
private def lam {n : ℕ} (Q : RatQF n) (c d : Fin n → ℚ) : ℚ :=
  -(Q.eval d) / (Q.eval (c + d) - Q.eval c - Q.eval d)

variable {n : ℕ} (Q : RatQF n) {K : Type*}

section Field
variable [Field K] [Algebra ℚ K]

/-- `bil` is the polar form of Mathlib's quadratic form. -/
private theorem bil_eq_polar (x y : Fin n → K) :
    bil Q K x y = QuadraticMap.polar (Q.toQuadraticFormIn K) x y := by
  simp [bil, QuadraticMap.polar, toQuadraticFormIn_apply]

/-- `bil` is symmetric. -/
private theorem bil_comm (x y : Fin n → K) : bil Q K x y = bil Q K y x := by
  rw [bil_eq_polar, bil_eq_polar, QuadraticMap.polar_comm]

/-- `bil` is additive in the second variable. -/
private theorem bil_add_right (x y z : Fin n → K) : bil Q K x (y + z) = bil Q K x y + bil Q K x z := by
  simp only [bil_eq_polar, QuadraticMap.polar_add_right]

/-- `bil` is homogeneous in the second variable. -/
private theorem bil_smul_right (t : K) (x y : Fin n → K) : bil Q K x (t • y) = t * bil Q K x y := by
  simp only [bil_eq_polar, QuadraticMap.polar_smul_right, smul_eq_mul]

/-- `B(x, x) = 2 Q(x)`. -/
private theorem bil_self (x : Fin n → K) : bil Q K x x = 2 * Q.evalIn K x := by
  rw [bil_eq_polar, QuadraticMap.polar_self, toQuadraticFormIn_apply]
  simp

/-- `Q(x + t y) = Q(x) + t B(x, y) + t² Q(y)`. -/
private theorem evalIn_add_smul (x y : Fin n → K) (t : K) :
    Q.evalIn K (x + t • y) = Q.evalIn K x + t * bil Q K x y + t ^ 2 * Q.evalIn K y := by
  have e := QuadraticMap.map_add (Q.toQuadraticFormIn K) x (t • y)
  have e2 := QuadraticMap.map_smul (Q.toQuadraticFormIn K) t y
  have e3 := QuadraticMap.polar_smul_right (Q.toQuadraticFormIn K) t x y
  simp only [toQuadraticFormIn_apply, ← bil_eq_polar, smul_eq_mul] at e e2 e3
  rw [e, e2, e3]
  ring

/-- `Q(t x) = t² Q(x)`. -/
private theorem evalIn_smul' (t : K) (x : Fin n → K) : Q.evalIn K (t • x) = t ^ 2 * Q.evalIn K x :=
  QuadForm.evalIn_smul K Q t x

/-- Evaluation of a rational vector in `K`. -/
private theorem evalIn_ratVec (c : Fin n → ℚ) : Q.evalIn K (ratVec K c) = algebraMap ℚ K (Q.eval c) := by
  simp only [QuadForm.evalIn, ratVec, map_sum, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp only [map_mul, map_zero]

private theorem ratVec_add (c d : Fin n → ℚ) : ratVec K (c + d) = ratVec K c + ratVec K d := by
  funext i; simp only [ratVec, Pi.add_apply, map_add]

/-- `B` commutes with the image of rational vectors. -/
private theorem bil_ratVec (c d : Fin n → ℚ) :
    bil Q K (ratVec K c) (ratVec K d) = algebraMap ℚ K (bil Q ℚ c d) := by
  unfold bil
  rw [← ratVec_add, evalIn_ratVec, evalIn_ratVec, evalIn_ratVec]
  simp only [map_sub]

/-- `B(x, y) = x · (H y)` where `H` is the Hessian. -/
private theorem bil_eq_dot (x y : Fin n → K) :
    bil Q K x y = (x ᵥ* Q.hessian.map (algebraMap ℚ K)) ⬝ᵥ y := by
  rw [← dotProduct_mulVec]
  exact polar_eq_hessian K Q x y

/-- Nondegeneracy: the Hessian over `K` has nonzero determinant. -/
private theorem hessian_det_ne (hQ : Q.Nondegenerate) : (Q.hessian.map (algebraMap ℚ K)).det ≠ 0 := by
  have := (algebraMap ℚ K).map_det Q.hessian
  have h2 : (Q.hessian.map (algebraMap ℚ K)).det = algebraMap ℚ K Q.hessian.det := by
    rw [this]; rfl
  rw [h2]
  exact (map_ne_zero _).2 hQ

/-- A nonzero vector has a nonzero linear form `B(c, ·)`. -/
private theorem vecMul_hessian_ne (hQ : Q.Nondegenerate) (c : Fin n → K) (hc : c ≠ 0) :
    (c ᵥ* Q.hessian.map (algebraMap ℚ K)) ≠ 0 := fun h0 =>
  hessian_det_ne Q hQ (Matrix.exists_vecMul_eq_zero_iff.1 ⟨c, hc, h0⟩)

/-- The Hessian over `K` is symmetric. -/
private theorem hessian_symm (i j : Fin n) :
    Q.hessian.map (algebraMap ℚ K) i j = Q.hessian.map (algebraMap ℚ K) j i := by
  simp [QuadForm.hessian, add_comm]

end Field

section Normed
variable [NontriviallyNormedField K] [Algebra ℚ K]

/-- `Q` is continuous on `K^n`. -/
private theorem continuous_evalIn : Continuous fun d : Fin n → K => Q.evalIn K d := by
  unfold QuadForm.evalIn
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs <;> fun_prop

/-- `B(c, ·)` is continuous on `K^n`. -/
private theorem continuous_bil (c : Fin n → K) : Continuous fun d : Fin n → K => bil Q K c d := by
  unfold bil
  exact (((continuous_evalIn Q).comp (continuous_const.add continuous_id)).sub continuous_const).sub
    (continuous_evalIn Q)

/-- Near a zero `v'` of `Q` with `B(c, v') ≠ 0`, the map `d ↦ λ(d) c + d` stays within `ε` of `v'`. -/
private theorem near_zero_cont (c v' : Fin n → K) (hv' : Q.evalIn K v' = 0) (hB : bil Q K c v' ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ d : Fin n → K, ‖d - v'‖ < δ → bil Q K c d ≠ 0 ∧
      ‖(-(Q.evalIn K d) / bil Q K c d) • c + d - v'‖ < ε := by
  set g : (Fin n → K) → (Fin n → K) := fun d => (-(Q.evalIn K d) / bil Q K c d) • c + d with hg
  have hgc : ContinuousAt g v' := by
    have hd : ContinuousAt (fun d : Fin n → K => -(Q.evalIn K d) / bil Q K c d) v' :=
      ContinuousAt.div (continuous_evalIn Q).neg.continuousAt (continuous_bil Q c).continuousAt hB
    exact (hd.smul continuousAt_const).add continuousAt_id
  have hgv : g v' = v' := by simp [hg, hv']
  have h1 : ∀ᶠ d in 𝓝 v', bil Q K c d ≠ 0 := (continuous_bil Q c).continuousAt.eventually_ne hB
  have h2 : ∀ᶠ d in 𝓝 v', g d ∈ Metric.ball v' ε :=
    hgc (by rw [hgv]; exact Metric.ball_mem_nhds _ hε)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  refine ⟨δ, hδ, fun d hd => ?_⟩
  have := hδ' (by rwa [dist_eq_norm])
  refine ⟨this.1, ?_⟩
  have h3 := this.2
  rwa [Metric.mem_ball, dist_eq_norm] at h3

end Normed

/-- `B(x, y) = x · (H y)` where `H` is the Hessian. -/
private theorem bil_eq_dot' [Field K] [Algebra ℚ K] (x y : Fin n → K) :
    bil Q K x y = x ⬝ᵥ (Q.hessian.map (algebraMap ℚ K) *ᵥ y) :=
  polar_eq_hessian K Q x y

/-- `ratVec` is the coordinatewise cast. -/
private theorem ratVec_eq [Field K] [Algebra ℚ K] (c : Fin n → ℚ) :
    ratVec K c = fun i => (c i : K) := by
  funext i; exact eq_ratCast (algebraMap ℚ K) (c i)

section Normed2
variable [NontriviallyNormedField K] [Algebra ℚ K]

/-- A zero near `v` with `B(c, ·) ≠ 0`, for a rational zero `c ≠ 0`. -/
private theorem exists_shift (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (c : Fin n → ℚ) (hc0 : c ≠ 0)
    (hc : Q.eval c = 0) (v : Fin n → K) (hv : Q.evalIn K v = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ v' : Fin n → K, Q.evalIn K v' = 0 ∧ bil Q K (ratVec K c) v' ≠ 0 ∧ ‖v' - v‖ < ε := by
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hck0 : ratVec K c ≠ 0 := by
    intro h
    apply hc0
    funext i
    have := congrFun h i
    exact (algebraMap ℚ K).injective (this.trans (map_zero _).symm)
  by_cases h1 : bil Q K (ratVec K c) v ≠ 0
  · exact ⟨v, hv, h1, by simpa using hε⟩
  push Not at h1
  by_cases hv0 : v = 0
  · subst hv0
    have hne := vecMul_hessian_ne Q hQ c hc0 (K := ℚ)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    set w₀ : Fin n → ℚ := Pi.single i 1 with hw₀
    have hB0 : bil Q ℚ c w₀ ≠ 0 := by
      rw [bil_eq_dot]
      simpa [hw₀, dotProduct_single] using hi
    set B0 := bil Q ℚ c w₀ with hB0def
    set t : ℚ := -(Q.eval w₀) / B0 with ht
    set w : Fin n → ℚ := w₀ + t • c with hw
    have hQw : Q.eval w = 0 := by
      rw [hw]
      refine (evalIn_add_smul (K := ℚ) Q w₀ c t).trans ?_
      have hc' : Q.evalIn ℚ c = 0 := hc
      rw [bil_comm, hc']
      change Q.eval w₀ + t * B0 + t ^ 2 * 0 = 0
      rw [mul_zero, add_zero, ht]
      field_simp
      ring
    have hBw : bil Q ℚ c w ≠ 0 := by
      rw [hw, bil_add_right, bil_smul_right, bil_self]
      change B0 + t * (2 * Q.eval c) ≠ 0
      rw [hc]
      simpa using hB0
    obtain ⟨s, hs0, hsr⟩ := NormedField.exists_norm_lt K
      (show 0 < ε / (‖ratVec K w‖ + 1) from div_pos hε (by positivity))
    have hs0' : s ≠ 0 := norm_pos_iff.1 hs0
    refine ⟨s • ratVec K w, ?_, ?_, ?_⟩
    · rw [evalIn_smul', evalIn_ratVec, hQw, map_zero, mul_zero]
    · rw [bil_smul_right, bil_ratVec]
      exact mul_ne_zero hs0' (by simpa using hBw)
    · rw [sub_zero, norm_smul]
      have hp : 0 < ‖ratVec K w‖ + 1 := by positivity
      calc ‖s‖ * ‖ratVec K w‖ ≤ ‖s‖ * (‖ratVec K w‖ + 1) := by gcongr; linarith
        _ < ε / (‖ratVec K w‖ + 1) * (‖ratVec K w‖ + 1) := by gcongr
        _ = ε := by field_simp
  · set Hk := Q.hessian.map (algebraMap ℚ K) with hHk
    set F : Fin n → Fin n → K := fun i j => 2⁻¹ * Hk i j with hF
    have hsymm : ∀ i j, F i j = F j i := fun i j => by
      simp only [hF, hHk, hessian_symm Q i j]
    have hM : Matrix.of F = (2⁻¹ : K) • Hk := by ext i j; simp [hF]
    have hdet : (Matrix.of F).det ≠ 0 := by
      rw [hM, det_smul]
      exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero two_ne_zero)) (hessian_det_ne Q hQ)
    have hFq : ∀ x, coeffQf F x = Q.evalIn K x := by
      intro x
      rw [coeffQf_eq_dotProduct, hM, smul_mulVec, dotProduct_smul, smul_eq_mul, ← bil_eq_dot', bil_self]
      field_simp
    obtain ⟨c', hc'U, hc'0, hc'h⟩ := zero_near_linear_ne_zero hn F hsymm hdet
      (ratVec K c ᵥ* Hk) (vecMul_hessian_ne Q hQ _ hck0) v hv0 (by rw [hFq]; exact hv)
      (Metric.ball v ε) (Metric.ball_mem_nhds _ hε)
    refine ⟨c', by rw [← hFq]; exact hc'0, ?_, ?_⟩
    · rw [bil_eq_dot]; exact hc'h
    · simpa [dist_eq_norm] using hc'U

/-- Local data at one place: a nearby zero `v'` and a radius `δ` for rational approximations of `v'`. -/
private theorem local_data (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (c : Fin n → ℚ) (hc0 : c ≠ 0)
    (hc : Q.eval c = 0) (v : Fin n → K) (hv : Q.evalIn K v = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ v' : Fin n → K, ∃ δ > 0, ∀ d : Fin n → ℚ, ‖ratVec K d - v'‖ < δ →
      bil Q ℚ c d ≠ 0 ∧ ‖ratVec K (fun i => lam Q c d * c i + d i) - v‖ < ε := by
  obtain ⟨v', hv'0, hv'B, hv'v⟩ := exists_shift Q hn hQ c hc0 hc v hv (half_pos hε)
  obtain ⟨δ, hδ, hδ'⟩ := near_zero_cont Q (ratVec K c) v' hv'0 hv'B (half_pos hε)
  refine ⟨v', δ, hδ, fun d hd => ?_⟩
  obtain ⟨hB, hn'⟩ := hδ' (ratVec K d) hd
  have hBq : bil Q ℚ c d ≠ 0 := fun h0 => hB (by rw [bil_ratVec, h0, map_zero])
  refine ⟨hBq, ?_⟩
  have hl : algebraMap ℚ K (lam Q c d) =
      -(Q.evalIn K (ratVec K d)) / bil Q K (ratVec K c) (ratVec K d) := by
    rw [evalIn_ratVec, bil_ratVec]
    simp only [lam, map_div₀, map_neg]
    rfl
  have e : ratVec K (fun i => lam Q c d * c i + d i) =
      algebraMap ℚ K (lam Q c d) • ratVec K c + ratVec K d := by
    funext i
    simp only [ratVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  rw [e, hl]
  calc _ ≤ ‖(-(Q.evalIn K (ratVec K d)) / bil Q K (ratVec K c) (ratVec K d)) • ratVec K c + ratVec K d
        - v'‖ + ‖v' - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hn' hv'v
    _ = ε := by ring

end Normed2

end Local

section Rep

/-- A positive radius below finitely many given positive radii. -/
private theorem exists_common_delta (S : Finset Nat.Primes) (δ : Nat.Primes → ℝ) (hδ : ∀ p, 0 < δ p)
    (δI : ℝ) (hδI : 0 < δI) : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ δI ∧ ∀ p ∈ S, δ0 ≤ δ p := by
  induction S using Finset.induction_on with
  | empty => exact ⟨δI, hδI, le_rfl, by simp⟩
  | insert a T ha ih =>
    obtain ⟨δ0, h0, h1, h2⟩ := ih
    refine ⟨min δ0 (δ a), lt_min h0 (hδ a), (min_le_left _ _).trans h1, fun p hp => ?_⟩
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h2 p hp)

/-- Continuity of `(w, z) ↦ z⁻¹ w` at `(x, 1)`, with an explicit estimate. -/
private theorem div_close {K : Type*} [NormedField K] {n : ℕ} (x : Fin n → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (w : Fin n → K) (z : K), ‖w - x‖ < δ → ‖z - 1‖ < δ →
      z ≠ 0 ∧ ‖z⁻¹ • w - x‖ < ε := by
  refine ⟨min (1 / 2) (ε / (2 * (1 + ‖x‖))), lt_min (by norm_num) (by positivity), fun w z hw hz => ?_⟩
  set δ : ℝ := min (1 / 2) (ε / (2 * (1 + ‖x‖))) with hδdef
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * (1 + ‖x‖)) := min_le_right _ _
  have hx1 : 0 < 2 * (1 + ‖x‖) := by positivity
  rw [le_div_iff₀ hx1] at hδ2
  have hz1 : 1 / 2 < ‖z‖ := by
    have := norm_sub_norm_le (1 : K) z
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hpos
  refine ⟨hz0, ?_⟩
  have e0 : (w - x) - (z - 1) • x = w - z • x := by rw [sub_smul, one_smul]; abel
  have e : z⁻¹ • w - x = z⁻¹ • ((w - x) - (z - 1) • x) := by
    rw [e0, smul_sub, inv_smul_smul₀ hz0]
  have hN : ‖(w - x) - (z - 1) • x‖ < δ * (1 + ‖x‖) := by
    calc ‖(w - x) - (z - 1) • x‖ ≤ ‖w - x‖ + ‖(z - 1) • x‖ := norm_sub_le _ _
      _ = ‖w - x‖ + ‖z - 1‖ * ‖x‖ := by rw [norm_smul]
      _ < δ * (1 + ‖x‖) := by
        have := mul_le_mul_of_nonneg_right hz.le (norm_nonneg x)
        nlinarith
  rw [e, norm_smul, norm_inv, inv_mul_eq_div, div_lt_iff₀ hpos]
  have := mul_lt_mul_of_pos_left hz1 hε
  nlinarith

/-- The value of `Q ⊥ ⟨-a⟩` in terms of the two blocks. -/
private theorem evalIn_aug {n : ℕ} {K : Type*} [Field K] [Algebra ℚ K] (Q : RatQF n) (a : ℚ)
    (y : Fin (n + 1) → K) :
    (QuadForm.orthSum Q (QuadForm.diag ![-a])).evalIn K y =
      Q.evalIn K (fun i => y (Fin.castAdd 1 i)) - algebraMap ℚ K a * y (Fin.natAdd n 0) ^ 2 := by
  rw [QuadForm.evalIn_orthSum, QuadForm.evalIn_diag]
  simp
  ring

/-- `Q ⊥ ⟨-a⟩` vanishes at `(y, 1)` when `Q(y) = a`. -/
private theorem evalIn_aug_append {n : ℕ} {K : Type*} [Field K] [Algebra ℚ K] (Q : RatQF n) (a : ℚ)
    (y : Fin n → K) (hy : Q.evalIn K y = algebraMap ℚ K a) :
    (QuadForm.orthSum Q (QuadForm.diag ![-a])).evalIn K (Fin.append y (fun _ : Fin 1 => (1 : K))) = 0 := by
  rw [evalIn_aug]
  simp [hy]

/-- Splitting the closeness to `(x, 1)` into closeness of the two blocks. -/
private theorem split_close {K : Type*} [NormedField K] {n : ℕ} (x : Fin n → K) (y : Fin (n + 1) → K)
    {ε : ℝ} (hε : 0 < ε) (h : ‖y - Fin.append x (fun _ : Fin 1 => (1 : K))‖ < ε) :
    ‖(fun i => y (Fin.castAdd 1 i)) - x‖ < ε ∧ ‖y (Fin.natAdd n 0) - 1‖ < ε := by
  have key : ∀ j, ‖y j - Fin.append x (fun _ : Fin 1 => (1 : K)) j‖ < ε := fun j =>
    lt_of_le_of_lt (norm_le_pi_norm (y - Fin.append x fun _ : Fin 1 => (1 : K)) j) h
  refine ⟨(pi_norm_lt_iff hε).2 fun i => ?_, ?_⟩
  · simpa [Fin.append_left] using key (Fin.castAdd 1 i)
  · simpa [Fin.append_right] using key (Fin.natAdd n 0)

end Rep

/-- **Cassels, Ch. 6, Lemma 9.1**: *let $f$ be an isotropic (regular) form over $\mathbb Q$ in $n \ge 3$ variables, let
$\varepsilon > 0$ and let $P$ be a finite set of places; for $p \in P$ let $\vec b_p \in \mathbb Q_p^n$ with
$f(\vec b_p) = 0$. Then there is $\vec b \in \mathbb Q^n$ with $f(\vec b) = 0$ and $\lvert\vec b - \vec b_p\rvert_p <
\varepsilon$ for all $p \in P$.* Here $P = S \cup \{\infty\}$ (see the module docstring). -/
@[kb "cassels1978" "Ch. 6, Lemma 9.1, pp. 89–90"]
theorem approx_zero (Q : RatQF n) (hn : 3 ≤ n) (hQ : Q.Nondegenerate) (hiso : Q.IsotropicIn ℚ)
    (S : Finset Nat.Primes) (b : ∀ p : Nat.Primes, Fin n → ℚ_[p]) (hb : ∀ p ∈ S, Q.evalIn ℚ_[p] (b p) = 0)
    (bInf : Fin n → ℝ) (hbInf : Q.evalIn ℝ bInf = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Fin n → ℚ, Q.eval c = 0 ∧ (∀ p ∈ S, ‖(fun i => (c i : ℚ_[p])) - b p‖ < ε) ∧
      ‖(fun i => (c i : ℝ)) - bInf‖ < ε := by
  obtain ⟨c, hc0, hc⟩ := hiso
  have hp : ∀ p : Nat.Primes, ∃ v' : Fin n → ℚ_[p], ∃ δ : ℝ, 0 < δ ∧ (p ∈ S → ∀ d : Fin n → ℚ,
      ‖ratVec ℚ_[p] d - v'‖ < δ → bil Q ℚ c d ≠ 0 ∧
        ‖ratVec ℚ_[p] (fun i => lam Q c d * c i + d i) - b p‖ < ε) := by
    intro p
    by_cases hpS : p ∈ S
    · obtain ⟨v', δ, hδ, h⟩ := local_data Q hn hQ c hc0 hc (b p) (hb p hpS) hε
      exact ⟨v', δ, hδ, fun _ => h⟩
    · exact ⟨0, 1, one_pos, fun h => absurd h hpS⟩
  choose v' δ hδ hv' using hp
  obtain ⟨vI, δI, hδI, hvI⟩ := local_data (K := ℝ) Q hn hQ c hc0 hc bInf hbInf hε
  obtain ⟨δ0, hδ0, hδ0I, hδ0p⟩ := exists_common_delta S δ hδ δI hδI
  have hw := fun i : Fin n => weak_approximation S (fun p => v' p i) (vI i) hδ0
  choose r hr using hw
  have hdp : ∀ p ∈ S, ‖ratVec ℚ_[p] r - v' p‖ < δ p := by
    intro p hp
    rw [ratVec_eq]
    exact lt_of_lt_of_le ((pi_norm_lt_iff hδ0).2 fun i => (hr i).1 p hp) (hδ0p p hp)
  have hdI : ‖ratVec ℝ r - vI‖ < δI := by
    rw [ratVec_eq]
    refine lt_of_lt_of_le ((pi_norm_lt_iff hδ0).2 fun i => ?_) hδ0I
    simpa [Real.norm_eq_abs] using (hr i).2
  have hB : bil Q ℚ c r ≠ 0 := (hvI r hdI).1
  have hbe : (fun i => lam Q c r * c i + r i) = r + lam Q c r • c := by
    funext i
    simp [add_comm]
  have hb0 : Q.eval (fun i => lam Q c r * c i + r i) = 0 := by
    rw [hbe]
    refine (evalIn_add_smul (K := ℚ) Q r c (lam Q c r)).trans ?_
    have hc' : Q.evalIn ℚ c = 0 := hc
    rw [bil_comm, hc']
    have hl : lam Q c r = -(Q.eval r) / bil Q ℚ c r := rfl
    rw [hl]
    change Q.eval r + (-(Q.eval r) / bil Q ℚ c r) * bil Q ℚ c r + (-(Q.eval r) / bil Q ℚ c r) ^ 2 * 0 = 0
    field_simp
    ring
  refine ⟨fun i => lam Q c r * c i + r i, hb0, fun p hp => ?_, ?_⟩
  · have := (hv' p hp r (hdp p hp)).2
    rwa [ratVec_eq] at this
  · have := (hvI r hdI).2
    rwa [ratVec_eq] at this

/-- **Cassels, Ch. 6, Corollary to Lemma 9.1**: *let $g$ be a regular rational form in $n \ge 2$ variables and let
$a \in \mathbb Q^\times$ be represented rationally by $g$; for $p \in P$ let $\vec a_p \in \mathbb Q_p^n$ with
$g(\vec a_p) = a$. Then there is $\vec a \in \mathbb Q^n$ with $g(\vec a) = a$ and $\lvert\vec a - \vec a_p\rvert_p <
\varepsilon$ for all $p \in P$.* Here $P = S \cup \{\infty\}$; for $\infty \notin P$ take any real $\vec a_\infty$ with
$g(\vec a_\infty) = a$ (one exists, the rational representation). -/
@[kb "cassels1978" "Ch. 6, Cor. to Lemma 9.1, p. 90"]
theorem approx_rep (Q : RatQF n) (hn : 2 ≤ n) (hQ : Q.Nondegenerate) {a : ℚ} (ha : a ≠ 0)
    (hrep : Q.RepresentsIn ℚ a) (S : Finset Nat.Primes) (x : ∀ p : Nat.Primes, Fin n → ℚ_[p])
    (hx : ∀ p ∈ S, Q.evalIn ℚ_[p] (x p) = a) (xInf : Fin n → ℝ) (hxInf : Q.evalIn ℝ xInf = a) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : Fin n → ℚ, Q.eval c = a ∧ (∀ p ∈ S, ‖(fun i => (c i : ℚ_[p])) - x p‖ < ε) ∧
      ‖(fun i => (c i : ℝ)) - xInf‖ < ε := by
  have hQ' : (QuadForm.orthSum Q (QuadForm.diag ![-a])).Nondegenerate :=
    QuadForm.nondegenerate_orthSum hQ (QuadForm.nondegenerate_diag (fun i => by
      fin_cases i; simpa using ha))
  have hiso := (QuadForm.representsIn_iff_isotropicIn_orthSum ℚ hQ a).1 hrep
  have hp : ∀ p : Nat.Primes, ∃ δ : ℝ, 0 < δ ∧ ∀ (w : Fin n → ℚ_[p]) (z : ℚ_[p]),
      ‖w - x p‖ < δ → ‖z - 1‖ < δ → z ≠ 0 ∧ ‖z⁻¹ • w - x p‖ < ε := by
    intro p
    obtain ⟨δ, hδ, h⟩ := div_close (x p) hε
    exact ⟨δ, hδ, h⟩
  choose δ hδ hδ' using hp
  obtain ⟨δI, hδI, hI⟩ := div_close xInf hε
  obtain ⟨ε', hε', hε'I, hε'p⟩ := exists_common_delta S δ hδ δI hδI
  obtain ⟨c, hc, hcp, hcI⟩ := approx_zero (n := n + 1) (QuadForm.orthSum Q (QuadForm.diag ![-a]))
    (by omega) hQ' hiso S (fun p => Fin.append (x p) (fun _ : Fin 1 => (1 : ℚ_[p])))
    (fun p hp => evalIn_aug_append Q a (x p)
      (by rw [hx p hp]; exact (eq_ratCast (algebraMap ℚ ℚ_[p]) a).symm))
    (Fin.append xInf (fun _ : Fin 1 => (1 : ℝ)))
    (evalIn_aug_append Q a xInf (by rw [hxInf]; exact (eq_ratCast (algebraMap ℚ ℝ) a).symm)) hε'
  set z : ℚ := c (Fin.natAdd n 0) with hz
  obtain ⟨hIc1, hIc2⟩ := split_close xInf (fun i => (c i : ℝ)) hε' hcI
  obtain ⟨hz0I, hyI⟩ := hI (fun i => (c (Fin.castAdd 1 i) : ℝ)) (z : ℝ)
    (lt_of_lt_of_le hIc1 hε'I) (lt_of_lt_of_le hIc2 hε'I)
  have hz0 : z ≠ 0 := fun h => hz0I (by rw [h]; simp)
  refine ⟨fun i => z⁻¹ * c (Fin.castAdd 1 i), ?_, fun p hp => ?_, ?_⟩
  · have h0 : Q.evalIn ℚ (fun i => c (Fin.castAdd 1 i)) - a * z ^ 2 = 0 := by
      have := hc
      change (QuadForm.orthSum Q (QuadForm.diag ![-a])).evalIn ℚ c = 0 at this
      rw [evalIn_aug] at this
      simpa using this
    have e : (fun i => z⁻¹ * c (Fin.castAdd 1 i)) = z⁻¹ • (fun i => c (Fin.castAdd 1 i)) := by
      funext i; simp
    rw [e]
    have := evalIn_smul' Q z⁻¹ (fun i => c (Fin.castAdd 1 i))
    change Q.evalIn ℚ _ = a
    rw [this]
    have h1 : Q.evalIn ℚ (fun i => c (Fin.castAdd 1 i)) = a * z ^ 2 := by linarith
    rw [h1]
    field_simp
  · obtain ⟨hc1, hc2⟩ := split_close (x p) (fun i => (c i : ℚ_[p])) hε' (hcp p hp)
    obtain ⟨-, hy⟩ := hδ' p (fun i => (c (Fin.castAdd 1 i) : ℚ_[p])) (z : ℚ_[p])
      (lt_of_lt_of_le hc1 (hε'p p hp)) (lt_of_lt_of_le hc2 (hε'p p hp))
    convert hy using 2
    funext i
    simp
  · convert hyI using 2
    funext i
    simp

end QuadFormsKB.Cassels.Ch6
