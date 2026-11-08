/-
# Tsen–Lang for systems, and the $C_2$ property of global function fields

**Theorems.**
* `Tsen.main_poly_system`: $r$ quadratic forms over $k[t]$ ($k$ a finite field) in $n > 4r$ variables
  have a common nontrivial zero in $k[t]^n$.
* `isotropic_system_ratFunc`: $r$ quadratic forms over $k(t)$ in $n > 4r$ variables have a common
  nontrivial zero in $k(t)^n$ (the $C_2$ property of $k(t)$, for systems).
* `exists_isotropic_of_functionField`: over a finite extension $F$ of $k(t)$, every quadratic form
  $Q$ on a vector space $V$ with $\dim_F V \ge 5$ has a nontrivial zero. No characteristic or
  nondegeneracy hypothesis.

*Proof.* The system version is the Chevalley–Warning counting of `RatFuncTsen.lean`: with
$R$ the maximal degree of the coefficients of the $r$ forms and $s = 2rR + 3$, look for
$x_i = \sum_{l \le s} y_{i,l} t^l$. The $r(R + 2s + 1)$ coefficient polynomials of the forms are of
degree $\le 2$ in the $n(s+1)$ unknowns $y_{i,l}$, and $2r(R+2s+1) < n(s+1)$ because $n \ge 4r+1$.
For $F/k(t)$ finite we restrict scalars: choose a $k(t)$-basis $\omega_0, \dots, \omega_{m-1}$ of $F$
and an $F$-basis of $V$ (dimension $N$); together they give a $k(t)$-basis of $V$ of size $mN$ and
$Q = \sum_{l < m} \Phi_l\, \omega_l$ with each $\Phi_l$ a quadratic form over $k(t)$ in $mN > 4m$
variables, so the system version applies.

Indices are 0-based.
-/
import Mathlib
import QuadFormsKB.Defs.QuadForm
import QuadFormsKB.FunctionField.RatFuncTsen

open Polynomial

namespace QuadFormsKB.RatFuncPlace

namespace Tsen

variable {k : Type} [Field k] [Fintype k]

/-- **Tsen–Lang for systems of forms over $k[t]$.** If $r$ quadratic forms
$\sum_{i \le j} p_{l,i,j}\, x_i x_j$ ($l < r$) over $k[t]$ in $n > 4r$ variables are given, there is a
nonzero $x \in k[t]^n$ at which all of them vanish. -/
theorem main_poly_system {r n : ℕ} (hn : 4 * r < n) (p : Fin r → Fin n → Fin n → k[X]) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧
      ∀ l, ∑ i, ∑ j, (if i ≤ j then p l i j * x i * x j else 0) = 0 := by
  classical
  set R : ℕ := Finset.univ.sup
    (fun t : Fin r × Fin n × Fin n => (p t.1 t.2.1 t.2.2).natDegree) with hR
  have hpr : ∀ l i j, (p l i j).natDegree ≤ R := fun l i j =>
    Finset.le_sup (f := fun t : Fin r × Fin n × Fin n => (p t.1 t.2.1 t.2.2).natDegree)
      (Finset.mem_univ (l, i, j))
  set s : ℕ := 2 * (r * R) + 3 with hs
  have hG : ∀ l, CoeffDeg 2 (Gform s (p l)) := by
    intro l
    refine CoeffDeg.sum _ fun i _ => CoeffDeg.sum _ fun j _ => ?_
    split_ifs
    · have := ((coeffDeg_C_map (n := n) s (p l i j)).mul (coeffDeg_genPoly (k := k) s i)).mul
        (coeffDeg_genPoly (k := k) s j)
      exact this.mono (by norm_num)
    · exact CoeffDeg.zero
  let S : Finset (Fin r × ℕ) := Finset.univ ×ˢ Finset.range (R + 2 * s + 1)
  let f : Fin r × ℕ → MvPolynomial (Fin n × Fin (s + 1)) k := fun lm => (Gform s (p lm.1)).coeff lm.2
  have hcard : ∑ lm ∈ S, (f lm).totalDegree < Fintype.card (Fin n × Fin (s + 1)) := by
    calc ∑ lm ∈ S, (f lm).totalDegree
        ≤ ∑ lm ∈ S, 2 := Finset.sum_le_sum fun lm _ => hG lm.1 lm.2
      _ = 2 * (r * (R + 2 * s + 1)) := by simp [S, Finset.card_product, mul_comm]
      _ < n * (s + 1) := by
        have h1 : (4 * r + 1) * (s + 1) ≤ n * (s + 1) := Nat.mul_le_mul_right _ hn
        nlinarith
      _ = _ := by simp
  obtain ⟨q, hq⟩ := CharP.exists k
  have hdvd := char_dvd_card_solutions_of_sum_lt q hcard
  have hprime : q.Prime := CharP.char_is_prime k q
  have hcoef : ∀ (y : Fin n × Fin (s + 1) → k) l m,
      MvPolynomial.eval y (f (l, m)) =
        (∑ i, ∑ j, if i ≤ j then p l i j * xs s y i * xs s y j else 0).coeff m := by
    intro y l m
    rw [← map_Gform, coeff_map]
  have hz0 : ∀ lm ∈ S, MvPolynomial.eval (0 : Fin n × Fin (s + 1) → k) (f lm) = 0 := by
    rintro ⟨l, m⟩ _
    rw [hcoef]
    have : ∀ i, xs s (0 : Fin n × Fin (s + 1) → k) i = 0 := fun i => by simp [xs]
    simp [this]
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_of_dvd_card _ hprime.one_lt hz0 hdvd
  refine ⟨xs s y, ?_, ?_⟩
  · intro h
    apply hy0
    funext ⟨i, l⟩
    have := coeff_xs s y i l
    rw [h] at this
    simpa using this.symm
  · intro l
    rw [← map_Gform]
    ext m
    rw [coeff_map, coeff_zero]
    by_cases hm : m < R + 2 * s + 1
    · exact hy (l, m) (by simp [S, hm])
    · have hdeg : (∑ i, ∑ j, if i ≤ j then p l i j * xs s y i * xs s y j else (0 : k[X])).natDegree
          ≤ R + 2 * s := by
        refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
        refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
        split_ifs
        · refine (natDegree_mul_le.trans (add_le_add (natDegree_mul_le.trans
            (add_le_add (hpr l i j) (natDegree_xs s y i))) (natDegree_xs s y j))).trans (by omega)
        · simp
      rw [← map_Gform] at hdeg
      have := coeff_eq_zero_of_natDegree_lt (p := (Gform s (p l)).map (MvPolynomial.eval y))
        (n := m) (by omega)
      rw [coeff_map] at this
      exact this

end Tsen

/-- **$C_2$ for systems of quadratic forms over $k(t)$.** For a finite field $k$ (any
characteristic), $r$ quadratic forms $Q_0, \dots, Q_{r-1}$ over $k(t)$ in $n > 4r$ variables have a
common nontrivial zero in $k(t)^n$. No nondegeneracy hypothesis. -/
theorem isotropic_system_ratFunc {k : Type} [Field k] [Fintype k] {r n : ℕ} (hn : 4 * r < n)
    (Q : Fin r → QuadForm (RatFunc k) n) :
    ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ l, (Q l).evalIn (RatFunc k) x = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors k[X])
    (Finset.univ : Finset (Fin r × Fin n × Fin n)) (fun t => (Q t.1).coeff t.2.1 t.2.2)
  have hb' : ∀ l i j, ∃ a : k[X], algebraMap k[X] (RatFunc k) a = (b : k[X]) • (Q l).coeff i j :=
    fun l i j => hb (l, i, j) (Finset.mem_univ _)
  choose p hp using hb'
  obtain ⟨x, hx0, hx⟩ := Tsen.main_poly_system hn p
  refine ⟨fun i => algebraMap k[X] (RatFunc k) (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact (map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mp
      (by simpa using congrFun h i)
  · intro l
    have hbne : algebraMap k[X] (RatFunc k) (b : k[X]) ≠ 0 := by
      intro h
      exact nonZeroDivisors.coe_ne_zero b
        ((map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mp h)
    have key : algebraMap k[X] (RatFunc k) (b : k[X]) * (Q l).evalIn (RatFunc k)
        (fun i => algebraMap k[X] (RatFunc k) (x i)) = 0 := by
      have h2 := congrArg (algebraMap k[X] (RatFunc k)) (hx l)
      rw [map_zero, map_sum] at h2
      rw [← h2, QuadForm.evalIn, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · have e : algebraMap k[X] (RatFunc k) (p l i j) = algebraMap k[X] (RatFunc k) (b : k[X]) *
            (Q l).coeff i j := by
          rw [hp l i j, Algebra.smul_def]
        rw [map_mul, map_mul, e, Algebra.algebraMap_self, RingHom.id_apply]
        ring
      · simp
    exact (mul_eq_zero.mp key).resolve_left hbne

/-- **Every quadratic map on $K^d$ with values in $K$ is a polynomial form.** For a field $K$ and
a quadratic map $\Phi : K^d \to K$ there is an upper-triangular `QuadForm K d` whose value at $z$ is
$\Phi(z)$ (no characteristic hypothesis; the coefficients are $\Phi(e_i)$ and the polar values
$\Phi(e_i + e_j) - \Phi(e_i) - \Phi(e_j)$). -/
theorem exists_quadForm_eval {K : Type*} [Field K] {d : ℕ}
    (Φ : QuadraticMap K (Fin d → K) K) :
    ∃ Q : QuadForm K d, ∀ z, Q.evalIn K z = Φ z := by
  classical
  let bm := Pi.basisFun K (Fin d)
  let Bf := Φ.toBilin bm
  refine ⟨⟨Matrix.of fun i j => Bf (bm i) (bm j), ?_⟩, fun z => ?_⟩
  · intro i j h
    have h' : j < i := h
    simp [Bf, QuadraticMap.toBilin_apply, h'.ne', not_lt.mpr h'.le]
  · rw [QuadForm.evalIn_eq_dotProduct]
    conv_rhs => rw [← QuadraticMap.toQuadraticMap_toBilin Φ bm]
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    have hz : z = ∑ i, z i • bm i := by
      conv_lhs => rw [← bm.sum_repr z]
      simp [bm]
    have : Bf z z = ∑ i, ∑ j, z i * z j * Bf (bm i) (bm j) := by
      conv_lhs => rw [hz]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **$C_2$ for quadratic forms over a global function field.** Let $k$ be a finite field and $F$ a
finite extension of $k(t)$. Every quadratic form $Q$ on a finite-dimensional $F$-vector space $V$ of
dimension $\ge 5$ has a nontrivial zero. No characteristic or nondegeneracy hypothesis.

*Proof.* Restriction of scalars (see the module docstring): $Q$ becomes $m = [F : k(t)]$ quadratic
forms over $k(t)$ in $m \dim_F V > 4m$ variables, and `isotropic_system_ratFunc` applies. -/
theorem exists_isotropic_of_functionField {k : Type} [Field k] [Fintype k] {F : Type} [Field F]
    [Algebra (RatFunc k) F] [FunctionField k F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticMap F V F) (hV : 5 ≤ Module.finrank F V) :
    ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  classical
  let _ : Module (RatFunc k) V := Module.compHom V (algebraMap (RatFunc k) F)
  have : IsScalarTower (RatFunc k) F V := ⟨fun a b v => by
    show (a • b) • v = (algebraMap (RatFunc k) F a) • b • v
    rw [Algebra.smul_def, mul_smul]⟩
  let e : Module.Basis (Fin (Module.finrank F V)) F V := Module.finBasis F V
  let ω : Module.Basis (Fin (Module.finrank (RatFunc k) F)) (RatFunc k) F :=
    Module.finBasis (RatFunc k) F
  let m := Module.finrank (RatFunc k) F
  let N := Module.finrank F V
  have hm : 0 < m := Module.finrank_pos
  let B : Module.Basis (Fin (m * N)) (RatFunc k) V :=
    (ω.smulTower e).reindex finProdFinEquiv
  let E : (Fin (m * N) → RatFunc k) ≃ₗ[RatFunc k] V := B.equivFun.symm
  let Φ : Fin m → QuadraticMap (RatFunc k) (Fin (m * N) → RatFunc k) (RatFunc k) := fun l =>
    (ω.coord l).compQuadraticMap
      ((Q.restrictScalars (S := RatFunc k)).comp (E : (Fin (m * N) → RatFunc k) →ₗ[RatFunc k] V))
  choose Ql hQl using fun l => exists_quadForm_eval (Φ l)
  obtain ⟨z, hz0, hz⟩ := isotropic_system_ratFunc (r := m) (n := m * N)
    (by nlinarith) Ql
  refine ⟨E z, ?_, ?_⟩
  · intro h
    exact hz0 (E.injective (by simpa using h))
  · have : ω.repr (Q (E z)) = 0 := by
      ext l
      have h1 := hz l
      rw [hQl] at h1
      simpa [Φ] using h1
    simpa using this

end QuadFormsKB.RatFuncPlace
