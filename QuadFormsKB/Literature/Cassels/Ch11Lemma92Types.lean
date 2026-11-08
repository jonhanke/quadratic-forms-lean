/-
# Cassels, Chapter 11, proof of Lemma 9.2: the local options at the primes of $P \cup \{q\}$

**Source.** J. W. S. Cassels, *Rational Quadratic Forms* (1978), Chapter 11, proof of Lemma 9.2, p. 245: "There are only
a finite number of classes of $z \in \mathbb Z_p$ modulo $U_p^2$ for which $|z|_p \ge |f(\mathbf u_0)|_p$ … If $p \in P$ but $f$ is
anisotropic over $\mathbb Q_p$, then $f$ represents primitively only a finite number of classes of $\mathbb Z_p$ modulo $U_p^2$."

**Proves.**
* `exists_bound_of_anisotropic`: if $f$ is anisotropic over $\mathbb Q_p$, the values $f(x)$ at primitive $x \in \mathbb Z_p^4$ are not
  divisible by $p^{2\delta + 1}$, $\delta = v_p(\det H_f)$ (Hensel's lemma along a coordinate with $v_p(B(x, e_i)) \le \delta$).
-/
import QuadFormsKB.Literature.Cassels.Ch11Lemma92Pi

open NumberField IsDedekindDomain Matrix QuadFormsKB.Cassels.Ch11L93

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.Cassels.Ch11L92

/-- **Primitive values of an anisotropic form have bounded valuation** (Cassels, p. 245): if the quaternary form $Q$ over
$\mathbb Z_p$ has $\det H_Q = p^\delta w \ne 0$ and is anisotropic over $\mathbb Q_p$, then $p^{2\delta + 1} \nmid Q(x)$ for every
primitive $x$. -/
theorem not_dvd_of_anisotropic {p : ℕ} [Fact p.Prime] (Q : QuadForm ℤ_[p] 4) {δ : ℕ} {w : ℤ_[p]} (hw : IsUnit w)
    (hdet : Q.hessian.det = (p : ℤ_[p]) ^ δ * w)
    (haniso : ¬ (Q.map PadicInt.Coe.ringHom).IsotropicIn ℚ_[p]) (x : Fin 4 → ℤ_[p]) (hx : ∃ i, IsUnit (x i)) :
    ¬ (p : ℤ_[p]) ^ (2 * δ + 1) ∣ Q.eval x := by
  classical
  intro hdiv
  apply haniso
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- some partial derivative has valuation at most `δ`
  have hsymm : ∀ a b, Q.hessian a b = Q.hessian b a := fun a b => by simp [QuadForm.hessian, add_comm]
  have hblH : ∀ i, bl Q x (Pi.single i 1) = (Q.hessian *ᵥ x) i := by
    intro i
    rw [bl, mulVec_single_one]
    simp only [dotProduct, Matrix.col_apply, mulVec]
    exact Finset.sum_congr rfl fun k _ => by rw [hsymm]; ring
  obtain ⟨wi, hwi⟩ := hw.exists_right_inv
  obtain ⟨i, hi⟩ : ∃ i, ¬ (p : ℤ_[p]) ^ (δ + 1) ∣ bl Q x (Pi.single i 1) := by
    by_contra hall
    push Not at hall
    choose y hy using hall
    obtain ⟨j, hj⟩ := hx
    have hHx : Q.hessian *ᵥ x = (p : ℤ_[p]) ^ (δ + 1) • y := by
      funext i; rw [← hblH, hy]; rfl
    have hadj : Q.hessian.det • x = (p : ℤ_[p]) ^ (δ + 1) • (Matrix.adjugate Q.hessian *ᵥ y) := by
      rw [← mulVec_smul, ← hHx, mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, one_mulVec]
    have hj' := congrFun hadj j
    simp only [Pi.smul_apply, smul_eq_mul, hdet] at hj'
    have hxj : x j = (p : ℤ_[p]) * ((Matrix.adjugate Q.hessian *ᵥ y) j * wi) := by
      have h1 : (p : ℤ_[p]) ^ δ * (w * x j) = (p : ℤ_[p]) ^ δ * ((p : ℤ_[p]) * (Matrix.adjugate Q.hessian *ᵥ y) j) := by
        linear_combination hj'
      have h2 := mul_left_cancel₀ (pow_ne_zero δ hp0) h1
      linear_combination (wi) * h2 - x j * hwi
    rw [hxj] at hj
    exact PadicInt.p_nonunit (isUnit_of_mul_isUnit_left hj)
  -- Hensel along `e_i`
  set F : Polynomial ℤ_[p] := Polynomial.C (Q.eval (Pi.single i 1)) * Polynomial.X ^ 2 +
    Polynomial.C (bl Q x (Pi.single i 1)) * Polynomial.X + Polynomial.C (Q.eval x) with hF
  have hFev : ∀ z, F.aeval z = Q.eval (x + z • Pi.single i 1) := by
    intro z; rw [eval_add, eval_smul, bl_smul_right, hF]; simp; ring
  have hF' : F.derivative.aeval 0 = bl Q x (Pi.single i 1) := by
    simp [hF, Polynomial.derivative_X_pow]
  have hd1 : ‖bl Q x (Pi.single i 1)‖ ≥ ‖(p : ℤ_[p]) ^ δ‖ := by
    by_contra hlt; push Not at hlt
    exact hi (dvd_of_norm_lt_pow hlt)
  have hsmall : ‖F.aeval (0 : ℤ_[p])‖ < ‖F.derivative.aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hFev, zero_smul, add_zero, hF']
    have h1 : ‖Q.eval x‖ < ‖(p : ℤ_[p]) ^ (2 * δ)‖ := norm_lt_of_dvd_pow (by simpa using hdiv)
    have h2 : ‖(p : ℤ_[p]) ^ (2 * δ)‖ = ‖(p : ℤ_[p]) ^ δ‖ ^ 2 := by rw [pow_mul', norm_pow]
    have h3 : 0 ≤ ‖(p : ℤ_[p]) ^ δ‖ := norm_nonneg _
    nlinarith
  obtain ⟨z, hz, hz1, -⟩ := hensels_lemma hsmall
  rw [sub_zero, hF'] at hz1
  have hz1' : ‖z‖ < 1 := lt_of_lt_of_le hz1 (PadicInt.norm_le_one _)
  set X : Fin 4 → ℤ_[p] := x + z • Pi.single i 1 with hX
  refine ⟨fun k => ((X k : ℤ_[p]) : ℚ_[p]), ?_, ?_⟩
  · intro h0
    obtain ⟨j, hj⟩ := hx
    have hj0 := congrFun h0 j
    simp only [Pi.zero_apply, PadicInt.coe_eq_zero, hX, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj0
    by_cases hij : j = i
    · subst hij
      simp at hj0
      have : x j = -z := by linear_combination hj0
      rw [this, PadicInt.isUnit_iff, norm_neg] at hj
      linarith
    · simp [Pi.single_apply, hij] at hj0
      exact hj.ne_zero hj0
  · rw [hFev] at hz
    have := eval_map_hom PadicInt.Coe.ringHom Q X
    rw [hz, map_zero] at this
    simpa [QuadForm.evalIn] using this

/-- Helper: $p^n \mid x - y$ iff $x \equiv y$ in $\mathbb Z/p^n$. -/
theorem pow_dvd_sub_iff_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) (x y : ℤ_[p]) :
    (p : ℤ_[p]) ^ n ∣ x - y ↔ PadicInt.toZModPow n x = PadicInt.toZModPow n y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

/-- **Finitely many square classes cover the primitively represented values of bounded valuation** (Cassels, p. 245):
for every $K$ there are finitely many primitive $x_j \in \mathbb Z_p^4$ with $Q(x_j) \ne 0$ such that every $a \in \mathbb Z_p$ with
$p^{K+1} \nmid a$ that is $Q(x)$ for a primitive $x$ is $Q(x_j)\beta^2$ for some $j$ and some unit $\beta$. -/
theorem exists_class_reps {p : ℕ} [Fact p.Prime] (Q : QuadForm ℤ_[p] 4) (K : ℕ) :
    ∃ (N : ℕ) (x : Fin N → Fin 4 → ℤ_[p]), (∀ j, (∃ i, IsUnit (x j i)) ∧ Q.eval (x j) ≠ 0 ∧
        ¬ (p : ℤ_[p]) ^ (K + 1) ∣ Q.eval (x j)) ∧
      ∀ a : ℤ_[p], (∃ y : Fin 4 → ℤ_[p], (∃ i, IsUnit (y i)) ∧ Q.eval y = a) → ¬ (p : ℤ_[p]) ^ (K + 1) ∣ a →
        ∃ j, ∃ β : ℤ_[p], IsUnit β ∧ a = Q.eval (x j) * β ^ 2 := by
  classical
  -- the realized classes `(k, w mod p³)`
  let Real : Fin (K + 1) × ZMod (p ^ 3) → Prop := fun kr => ∃ y : Fin 4 → ℤ_[p], (∃ i, IsUnit (y i)) ∧
    ∃ w : ℤ_[p], IsUnit w ∧ Q.eval y = (p : ℤ_[p]) ^ (kr.1 : ℕ) * w ∧ PadicInt.toZModPow 3 w = kr.2
  set I : Finset (Fin (K + 1) × ZMod (p ^ 3)) := Finset.univ.filter Real with hI
  have hchoose : ∀ kr : I, Real kr.1 := fun kr => (Finset.mem_filter.mp kr.2).2
  choose y hy w hw hyw hwr using hchoose
  let e := I.equivFin
  refine ⟨I.card, fun j => y (e.symm j), fun j => ⟨hy _, ?_, ?_⟩, fun a ⟨y0, hy0, hy0a⟩ hK => ?_⟩
  · rw [hyw]; exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) (hw _).ne_zero
  · rw [hyw]
    intro hd
    have hk : ((e.symm j).1.1 : ℕ) ≤ K := Nat.lt_succ_iff.mp (e.symm j).1.1.2
    have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    obtain ⟨t, ht⟩ := hd
    have : (p : ℤ_[p]) ^ ((e.symm j).1.1 : ℕ) * w (e.symm j) =
        (p : ℤ_[p]) ^ ((e.symm j).1.1 : ℕ) * ((p : ℤ_[p]) * ((p : ℤ_[p]) ^ (K - ((e.symm j).1.1 : ℕ)) * t)) := by
      rw [ht, ← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_add]; congr 2; omega
    have h2 := mul_left_cancel₀ (pow_ne_zero _ hp0) this
    exact PadicInt.p_nonunit (isUnit_of_dvd_unit ⟨_, h2⟩ (hw _))
  · have ha0 : a ≠ 0 := fun h0 => hK (by rw [h0]; exact dvd_zero _)
    obtain ⟨k, w0, hw0, hka⟩ := decomp ha0
    have hk : k ≤ K := by
      by_contra hlt
      exact hK (by rw [hka]; exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _)
    set kr : Fin (K + 1) × ZMod (p ^ 3) := (⟨k, by omega⟩, PadicInt.toZModPow 3 w0)
    have hkr : kr ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, y0, hy0, w0, hw0, by rw [hy0a, hka], rfl⟩
    refine ⟨e ⟨kr, hkr⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    -- `w0 / w ≡ 1 (mod p³)` is a square
    obtain ⟨wi, hwi⟩ := (hw ⟨kr, hkr⟩).exists_right_inv
    have hcong : (p : ℤ_[p]) ^ 3 ∣ w0 - w ⟨kr, hkr⟩ := by
      rw [pow_dvd_sub_iff_toZModPow, hwr]
    obtain ⟨β, hβ⟩ := exists_sq_of_pow_three_dvd (p := p) (x := w0 * wi)
      (by obtain ⟨t, ht⟩ := hcong; exact ⟨t * wi, by linear_combination wi * ht + hwi⟩)
    have hβu : IsUnit β := by
      have : IsUnit (β ^ 2) := by rw [hβ]; exact hw0.mul (isUnit_of_mul_eq_one_right' hwi)
      exact (isUnit_pow_iff (by norm_num)).mp this
    refine ⟨β, hβu, ?_⟩
    rw [hyw, hβ, hka]
    linear_combination (-((p : ℤ_[p]) ^ k * w0)) * hwi

end QuadFormsKB.Cassels.Ch11L92
