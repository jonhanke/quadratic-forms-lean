/-
# Counting: the gauge-form volume of $K_m$ for $\langle1,-a,-b,ab\rangle$

**Layer:** a number field $F$, a finite place $v$ (dyadic and ramified places included), $a, b\in\mathcal O_F\setminus0$ with
$|2|_v = q^{-s}$, $|a|_v = q^{-e_a}$, $|b|_v = q^{-e_b}$, $\mu = \min(e_a,e_b)$.

* **`card_kerD_diag4`**: for a diagonal quaternary Hessian $\mathrm{diag}(h_0,\dots,h_3)$ with $\pi^{e_i}\,\|\,h_i$, $e_i\le j$,
  $\#\{Z\in M_4(\mathfrak o/\pi^j) : D_1Z\equiv0\} = q^{\sum e_i}\prod_{i<l}q^{\min(e_i,e_l)}q^j$ (the 4-variable analogue of
  `card_kerD_diag3`; $D_1$ = the differential of $X\mapsto Q\circ X$ at $1$, whose kernel is $\mathfrak{so}(Q)$).
* **`muLoc_congSub_qSq_mul`** ($m\ge 2(4s+2e_a+2e_b)+1$): $\mu_v(K_m)\cdot q^{6m} = q^{10s+3e_a+3e_b+\mu}$ for
  $Q_0 = \langle1,-a,-b,ab\rangle$ (`qSq a b`), by `muLoc_congSub_eq`.
* **`muLoc_congSub_pureFormO_mul`** ($m\ge 2(3s+2e_a+2e_b)+1$): $\mu_v(K_m)\cdot q^{3m} = q^{6s+3e_a+3e_b+\mu}$ for
  $\langle-a,-b,ab\rangle$.
* Hence (**`muLoc_congSub_qSq_eq`**) $\mu^{(4)}_v(K_m)\cdot q^{3m} = q^{4s}\,\mu^{(3)}_v(K_m)$: the quotient of the two gauge-form
  volumes is the volume $q^{-3m}|2|_v^{-4}$ of the "sphere" part.

Source: Weil 1982, §2.2 (gauge-form volumes by counting mod $\pi^k$) [unverified page].
-/
import QuadFormsKB.Tamagawa.Measure.Weil.PDCongruence
import QuadFormsKB.Tamagawa.Measure.Weil.GnatTamagawa

open Matrix NumberField IsDedekindDomain WithZero MeasureTheory Set
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Measure.LerayPadic

open QuadFormsKB.Analysis QuadFormsKB.LocalDensity QuadFormsKB.LocalZeta QuadFormsKB.Lattices
open QuadFormsKB.LocalDensity.DVR (formF formD UpperIdx liftI redI toMat lift1)

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

theorem forall_upperIdx_four (P : UpperIdx 4 → Prop) :
    (∀ p, P p) ↔ (P ⟨(0, 0), le_rfl⟩ ∧ P ⟨(1, 1), le_rfl⟩ ∧ P ⟨(2, 2), le_rfl⟩ ∧ P ⟨(3, 3), le_rfl⟩) ∧
      (P ⟨(0, 1), by decide⟩ ∧ P ⟨(0, 2), by decide⟩ ∧ P ⟨(0, 3), by decide⟩ ∧ P ⟨(1, 2), by decide⟩ ∧
        P ⟨(1, 3), by decide⟩ ∧ P ⟨(2, 3), by decide⟩) := by
  constructor
  · intro h; exact ⟨⟨h _, h _, h _, h _⟩, h _, h _, h _, h _, h _, h _⟩
  · rintro ⟨⟨h00, h11, h22, h33⟩, h01, h02, h03, h12, h13, h23⟩ ⟨⟨i, l⟩, hil⟩
    fin_cases i <;> fin_cases l <;> first | assumption | exact absurd hil (by decide)

/-- $D_1$ for a diagonal quaternary Hessian $\mathrm{diag}(h_0,\dots,h_3)$. -/
theorem formD_oneVec_diag4 (Q : QuadForm 𝔬 4) (h : Fin 4 → 𝔬) (hH : Q.hessian = Matrix.diagonal h)
    (w : Fin 4 × Fin 4 → 𝔬) (i l : Fin 4) (hil : i ≤ l) :
    formD Q (oneVec v) w ⟨(i, l), hil⟩ = if i = l then h i * w (i, i) else h i * w (i, l) + h l * w (l, i) := by
  fin_cases i <;> fin_cases l <;>
  first
  | exact absurd hil (by decide)
  | (simp [formD, DVR.bil, DVR.col, toMat, oneVec, hH, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply]; try ring)

/-- The block decomposition $M_4(A)\cong A^4\times(A^2)^6$. -/
def blockEquiv4 (A : Type*) : (Fin 4 × Fin 4 → A) ≃
    (A × A × A × A) × ((A × A) × (A × A) × (A × A) × (A × A) × (A × A) × (A × A)) where
  toFun z := ((z (0, 0), z (1, 1), z (2, 2), z (3, 3)), ((z (0, 1), z (1, 0)), (z (0, 2), z (2, 0)),
    (z (0, 3), z (3, 0)), (z (1, 2), z (2, 1)), (z (1, 3), z (3, 1)), (z (2, 3), z (3, 2))))
  invFun t := fun p => match p with
    | (0, 0) => t.1.1 | (1, 1) => t.1.2.1 | (2, 2) => t.1.2.2.1 | (3, 3) => t.1.2.2.2
    | (0, 1) => t.2.1.1 | (1, 0) => t.2.1.2 | (0, 2) => t.2.2.1.1 | (2, 0) => t.2.2.1.2
    | (0, 3) => t.2.2.2.1.1 | (3, 0) => t.2.2.2.1.2 | (1, 2) => t.2.2.2.2.1.1 | (2, 1) => t.2.2.2.2.1.2
    | (1, 3) => t.2.2.2.2.2.1.1 | (3, 1) => t.2.2.2.2.2.1.2 | (2, 3) => t.2.2.2.2.2.2.1
    | (3, 2) => t.2.2.2.2.2.2.2
  left_inv z := by
    funext ⟨i, l⟩
    fin_cases i <;> fin_cases l <;> rfl
  right_inv t := rfl

/-- **The kernel of $D_1\bmod\pi^j$ for a diagonal quaternary form** $\mathrm{diag}(h_0,\dots,h_3)$, $\pi^{e_i}\,\|\,h_i$,
$e_i\le j$: $q^{e_0+e_1+e_2+e_3}\prod_{i<l}q^{\min(e_i,e_l)}q^j$ elements. -/
theorem card_kerD_diag4 (Q : QuadForm 𝔬 4) (h : Fin 4 → 𝔬) (hH : Q.hessian = Matrix.diagonal h) (j : ℕ)
    (e : Fin 4 → ℕ) (he : ∀ i, πv ^ e i ∣ h i) (he' : ∀ i, ¬ πv ^ (e i + 1) ∣ h i) (hej : ∀ i, e i ≤ j) :
    Nat.card {z : Fin 4 × Fin 4 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} =
      (DVR.q 𝔬 ^ e 0 * DVR.q 𝔬 ^ e 1 * DVR.q 𝔬 ^ e 2 * DVR.q 𝔬 ^ e 3) *
        ((DVR.q 𝔬 ^ min (e 0) (e 1) * DVR.q 𝔬 ^ j) * (DVR.q 𝔬 ^ min (e 0) (e 2) * DVR.q 𝔬 ^ j) *
          (DVR.q 𝔬 ^ min (e 0) (e 3) * DVR.q 𝔬 ^ j) * (DVR.q 𝔬 ^ min (e 1) (e 2) * DVR.q 𝔬 ^ j) *
          (DVR.q 𝔬 ^ min (e 1) (e 3) * DVR.q 𝔬 ^ j) * (DVR.q 𝔬 ^ min (e 2) (e 3) * DVR.q 𝔬 ^ j)) := by
  have hπ := NF.irreducible_π v
  set C1 := fun i : Fin 4 => {x : RQ v j // πv ^ j ∣ h i * lift1 πv j x}
  set C2 := fun i l : Fin 4 => {p : RQ v j × RQ v j // πv ^ j ∣ h i * lift1 πv j p.1 + h l * lift1 πv j p.2}
  have e1 : {z : Fin 4 × Fin 4 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} ≃
      (C1 0 × C1 1 × C1 2 × C1 3) × (C2 0 1 × C2 0 2 × C2 0 3 × C2 1 2 × C2 1 3 × C2 2 3) := by
    refine (Equiv.subtypeEquiv (blockEquiv4 _) fun z => ?_).trans
      ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr
        ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _)
          ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _) Equiv.subtypeProdEquivProd))))
        ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _)
          ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _)
            ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _)
              ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.refl _)
                Equiv.subtypeProdEquivProd))))))))))
    rw [forall_upperIdx_four]
    simp only [formD_oneVec_diag4 v Q h hH, blockEquiv4, Equiv.coe_fn_mk, ite_true, Fin.reduceEq, ite_false]
    rfl
  rw [Nat.card_congr e1]
  simp only [Nat.card_prod, C1, C2]
  rw [DVR.card_dvd_mul_lift1 πv hπ (he 0) (he' 0) (hej 0), DVR.card_dvd_mul_lift1 πv hπ (he 1) (he' 1) (hej 1),
    DVR.card_dvd_mul_lift1 πv hπ (he 2) (he' 2) (hej 2), DVR.card_dvd_mul_lift1 πv hπ (he 3) (he' 3) (hej 3),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 1) (he' 1) (hej 0) (hej 1),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 2) (he' 2) (hej 0) (hej 2),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 3) (he' 3) (hej 0) (hej 3),
    DVR.card_dvd_add_lift1' πv hπ (he 1) (he' 1) (he 2) (he' 2) (hej 1) (hej 2),
    DVR.card_dvd_add_lift1' πv hπ (he 1) (he' 1) (he 3) (he' 3) (hej 1) (hej 3),
    DVR.card_dvd_add_lift1' πv hπ (he 2) (he' 2) (he 3) (he' 3) (hej 2) (hej 3)]
  ring

end QuadFormsKB.Tamagawa.Measure.LerayPadic

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Quat QuadFormsKB.Lattices LocalDensity LerayPadic LocalZeta

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {a b : 𝓞 F}

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v
local notation "Av" => algebraMap F (v.adicCompletion F) (a : F)
local notation "Bv" => algebraMap F (v.adicCompletion F) (b : F)

omit [NumberField F] in
theorem hessian_qSq (a b : 𝓞 F) :
    (qSq a b).hessian = Matrix.diagonal ![2, -2 * a, -2 * b, 2 * (a * b)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuadForm.hessian, qSq, QuadForm.diag, Matrix.diagonal, map_ofNat] <;> ring

theorem hessian_Qp_qSq (a b : 𝓞 F) : (NF.Qp v (qSq a b)).hessian =
    Matrix.diagonal (fun i => NF.ι v (![2, -2 * a, -2 * b, 2 * (a * b)] i)) := by
  rw [NF.Qp, QuadForm.hessian_map, hessian_qSq, Matrix.diagonal_map (map_zero _)]

theorem valued_ι_two {s : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) :
    Valued.v ((NF.ι v (2 : 𝓞 F) : 𝔬) : Fv) = exp (-(s : ℤ)) := by
  rw [coe_ι, show ((2 : 𝓞 F) : F) = 2 by
    rw [show ((2 : 𝓞 F) : F) = algebraMap (𝓞 F) F 2 from rfl, map_ofNat], map_ofNat, hs]

theorem valued_ι_neg_two_mul {s e : ℕ} {x : 𝓞 F} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hx : Valued.v (algebraMap F Fv (x : F)) = exp (-(e : ℤ))) :
    Valued.v ((NF.ι v (-2 * x) : 𝔬) : Fv) = exp (-((s + e : ℕ) : ℤ)) := by
  rw [coe_ι, show ((-2 * x : 𝓞 F) : F) = -(2 * (x : F)) by
    rw [show ((-2 * x : 𝓞 F) : F) = algebraMap (𝓞 F) F (-2 * x) from rfl, map_mul, map_neg, map_ofNat]; ring,
    map_neg, map_mul, map_ofNat, Valuation.map_neg, map_mul, hs, hx, ← WithZero.exp_add]
  congr 1; push_cast; ring

theorem valued_ι_two_mul_mul {s eA eB : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hA : Valued.v Av = exp (-(eA : ℤ))) (hB : Valued.v Bv = exp (-(eB : ℤ))) :
    Valued.v ((NF.ι v (2 * (a * b)) : 𝔬) : Fv) = exp (-((s + eA + eB : ℕ) : ℤ)) := by
  rw [coe_ι, show ((2 * (a * b) : 𝓞 F) : F) = 2 * ((a : F) * (b : F)) by
    rw [show ((2 * (a * b) : 𝓞 F) : F) = algebraMap (𝓞 F) F (2 * (a * b)) from rfl, map_mul, map_mul,
      map_ofNat], map_mul, map_mul, map_ofNat, map_mul, map_mul, hs, hA, hB, ← WithZero.exp_add,
    ← WithZero.exp_add]
  congr 1; push_cast; ring

/-- **The gauge-form volume of $K_m$ for $\langle1,-a,-b,ab\rangle$** ($m\ge 2(4s+2e_a+2e_b)+1$):
$\mu_v(K_m)\cdot q^{6m} = q^{10s+3e_a+3e_b+\min(e_a,e_b)}$. -/
@[kb "weil1982" "§2.2 (gauge-form volumes by counting) [unverified]"]
theorem muLoc_congSub_qSq_mul {s eA eB m : ℕ} (hQ : (qSq a b).Nondegenerate)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v Av = exp (-(eA : ℤ)))
    (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : 2 * (4 * s + 2 * eA + 2 * eB) + 1 ≤ m) :
    Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) m (by omega) : Set _) * (DVR.q 𝔬 : ℝ≥0∞) ^ (6 * m) =
      (DVR.q 𝔬 : ℝ≥0∞) ^ (10 * s + 3 * eA + 3 * eB + min eA eB) := by
  set d := 4 * s + 2 * eA + 2 * eB
  set j := 2 * d + 1
  set μ := min eA eB
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set h : Fin 4 → 𝔬 := fun i => NF.ι v (![2, -2 * a, -2 * b, 2 * (a * b)] i)
  set e : Fin 4 → ℕ := ![s, s + eA, s + eB, s + eA + eB]
  have hval : ∀ i, Valued.v ((h i : 𝔬) : Fv) = exp (-(e i : ℤ)) := by
    intro i
    fin_cases i
    · exact valued_ι_two hs
    · exact valued_ι_neg_two_mul hs hA
    · exact valued_ι_neg_two_mul hs hB
    · exact valued_ι_two_mul_mul hs hA hB
  have hdiv := fun i => pow_dvd_of_valued (hval i)
  have hdet : Valued.v (((NF.Qp v (qSq a b)).hessian.det : 𝔬) : Fv) = exp (-(d : ℤ)) := by
    rw [hessian_Qp_qSq, Matrix.det_diagonal, Fin.prod_univ_four]
    change Valued.v ((h 0 : Fv) * (h 1 : Fv) * (h 2 : Fv) * (h 3 : Fv)) = _
    rw [map_mul, map_mul, map_mul, hval 0, hval 1, hval 2, hval 3, ← WithZero.exp_add, ← WithZero.exp_add,
      ← WithZero.exp_add]
    congr 1; simp [d, e]; push_cast; ring
  obtain ⟨hd, hd'⟩ := pow_dvd_of_valued hdet
  rw [muLoc_congSub_eq v _ hQ m (by omega) d j hd hd' le_rfl (by omega),
    card_kerD_diag4 v _ h (hessian_Qp_qSq a b) j e (fun i => (hdiv i).1) (fun i => (hdiv i).2)
      (fun i => by
        have : e i ≤ s + eA + eB := by fin_cases i <;> simp [e] <;> omega
        omega)]
  have he0 : e 0 = s := rfl
  have he1 : e 1 = s + eA := rfl
  have he2 : e 2 = s + eB := rfl
  have he3 : e 3 = s + eA + eB := rfl
  have m01 : min (e 0) (e 1) = s := by rw [he0, he1]; exact min_eq_left (by omega)
  have m02 : min (e 0) (e 2) = s := by rw [he0, he2]; exact min_eq_left (by omega)
  have m03 : min (e 0) (e 3) = s := by rw [he0, he3]; exact min_eq_left (by omega)
  have m12 : min (e 1) (e 2) = s + μ := by rw [he1, he2, min_add_add_left]
  have m13 : min (e 1) (e 3) = s + eA := by rw [he1, he3]; exact min_eq_left (by omega)
  have m23 : min (e 2) (e 3) = s + eB := by rw [he2, he3]; exact min_eq_left (by omega)
  rw [m01, m02, m03, m12, m13, m23, he0, he1, he2, he3]
  set q := (DVR.q 𝔬 : ℝ≥0∞)
  simp only [Nat.cast_mul, Nat.cast_pow, ← pow_add]
  have hμ : μ ≤ eA := min_le_left _ _
  rw [show (4 * (4 - 1) / 2) = 6 by norm_num,
    show s + (s + eA) + (s + eB) + (s + eA + eB) + (s + j + (s + j) + (s + j) + (s + μ + j) + (s + eA + j) +
      (s + eB + j)) = (10 * s + 3 * eA + 3 * eB + μ) + 6 * j by ring,
    show (m + j) * 6 = 6 * j + 6 * m by ring, pow_add, pow_add q (6 * j), div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))]
  calc q ^ (10 * s + 3 * eA + 3 * eB + μ) * q ^ (6 * j) * ((q ^ (6 * j))⁻¹ * (q ^ (6 * m))⁻¹) * q ^ (6 * m)
      = q ^ (10 * s + 3 * eA + 3 * eB + μ) * (q ^ (6 * j) * (q ^ (6 * j))⁻¹) *
          ((q ^ (6 * m))⁻¹ * q ^ (6 * m)) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt),
        ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one, mul_one]

/-- **The gauge-form volume of $K_m$ for $\langle-a,-b,ab\rangle$** ($m\ge 2(3s+2e_a+2e_b)+1$):
$\mu_v(K_m)\cdot q^{3m} = q^{6s+3e_a+3e_b+\min(e_a,e_b)}$. -/
@[kb "weil1982" "§2.2 (gauge-form volumes by counting) [unverified]"]
theorem muLoc_congSub_pureFormO_mul {s eA eB m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v Av = exp (-(eA : ℤ)))
    (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : 2 * (3 * s + 2 * eA + 2 * eB) + 1 ≤ m) :
    Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) m (by omega) : Set _) *
        (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * m) = (DVR.q 𝔬 : ℝ≥0∞) ^ (6 * s + 3 * eA + 3 * eB + min eA eB) := by
  set d := 3 * s + 2 * eA + 2 * eB
  set j := 2 * d + 1
  set μ := min eA eB
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set h : Fin 3 → 𝔬 := fun i => NF.ι v (![-2 * a, -2 * b, 2 * (a * b)] i)
  set e : Fin 3 → ℕ := ![s + eA, s + eB, s + eA + eB]
  have hval : ∀ i, Valued.v ((h i : 𝔬) : Fv) = exp (-(e i : ℤ)) := by
    intro i
    fin_cases i
    · exact valued_ι_neg_two_mul hs hA
    · exact valued_ι_neg_two_mul hs hB
    · exact valued_ι_two_mul_mul hs hA hB
  have hdiv := fun i => pow_dvd_of_valued (hval i)
  have hdet : Valued.v (((NF.Qp v (QuatZeta.pureFormO a b)).hessian.det : 𝔬) : Fv) = exp (-(d : ℤ)) := by
    rw [hessian_Qp_pureFormO, Matrix.det_diagonal, Fin.prod_univ_three]
    change Valued.v ((h 0 : Fv) * (h 1 : Fv) * (h 2 : Fv)) = _
    rw [map_mul, map_mul, hval 0, hval 1, hval 2, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; simp [d, e]; ring
  obtain ⟨hd, hd'⟩ := pow_dvd_of_valued hdet
  have hQ := nondegenerate_pureFormO a b ha hb
  rw [muLoc_congSub_eq v _ hQ m (by omega) d j hd hd' le_rfl (by omega),
    card_kerD_diag3 v _ h (hessian_Qp_pureFormO a b) j e (fun i => (hdiv i).1) (fun i => (hdiv i).2)
      (fun i => by
        have : e i ≤ s + eA + eB := by fin_cases i <;> simp [e] <;> omega
        omega)]
  have he0 : e 0 = s + eA := rfl
  have he1 : e 1 = s + eB := rfl
  have he2 : e 2 = s + eA + eB := rfl
  have m01 : min (e 0) (e 1) = s + μ := by rw [he0, he1, min_add_add_left]
  have m02 : min (e 0) (e 2) = s + eA := by rw [he0, he2]; exact min_eq_left (by omega)
  have m12 : min (e 1) (e 2) = s + eB := by rw [he1, he2]; exact min_eq_left (by omega)
  rw [m01, m02, m12, he0, he1, he2]
  set q := (DVR.q 𝔬 : ℝ≥0∞)
  simp only [Nat.cast_mul, Nat.cast_pow, ← pow_add]
  have hμ : μ ≤ eA := min_le_left _ _
  rw [show (3 * (3 - 1) / 2) = 3 by norm_num,
    show s + eA + (s + eB) + (s + eA + eB) + (s + μ + j + (s + eA + j) + (s + eB + j)) =
      (6 * s + 3 * eA + 3 * eB + μ) + 3 * j by ring,
    show (m + j) * 3 = 3 * j + 3 * m by ring, pow_add, pow_add q (3 * j), div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0)) (Or.inl (ENNReal.pow_ne_top hqt))]
  calc q ^ (6 * s + 3 * eA + 3 * eB + μ) * q ^ (3 * j) * ((q ^ (3 * j))⁻¹ * (q ^ (3 * m))⁻¹) * q ^ (3 * m)
      = q ^ (6 * s + 3 * eA + 3 * eB + μ) * (q ^ (3 * j) * (q ^ (3 * j))⁻¹) *
          ((q ^ (3 * m))⁻¹ * q ^ (3 * m)) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt),
        ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one, mul_one]

/-- **The quaternary and ternary congruence volumes** ($m\ge2(4s+2e_a+2e_b)+1$):
$\mu^{\langle1,-a,-b,ab\rangle}_v(K_m)\cdot q^{3m} = q^{4s}\,\mu^{\langle-a,-b,ab\rangle}_v(K_m)$. -/
@[kb "weil1982" "§2.2 [unverified]"]
theorem muLoc_congSub_qSq_eq {s eA eB m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hQ : (qSq a b).Nondegenerate)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hA : Valued.v Av = exp (-(eA : ℤ)))
    (hB : Valued.v Bv = exp (-(eB : ℤ))) (hm : 2 * (4 * s + 2 * eA + 2 * eB) + 1 ≤ m) :
    Measure.muLoc v (qSq a b) 1 (congSub v (qSq a b) m (by omega) : Set _) * (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * m) =
      (DVR.q 𝔬 : ℝ≥0∞) ^ (4 * s) *
        Measure.muLoc v (QuatZeta.pureFormO a b) 1 (congSub v (QuatZeta.pureFormO a b) m (by omega) : Set _) := by
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h4 := muLoc_congSub_qSq_mul hQ hs hA hB hm
  have h3 := muLoc_congSub_pureFormO_mul ha hb hs hA hB (by omega : 2 * (3 * s + 2 * eA + 2 * eB) + 1 ≤ m)
  have h3m : (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * m) ≠ 0 := pow_ne_zero _ hq0
  have h3t : (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * m) ≠ ⊤ := ENNReal.pow_ne_top hqt
  refine (ENNReal.mul_left_inj h3m h3t).1 ?_
  rw [mul_assoc, ← pow_add, show 3 * m + 3 * m = 6 * m by ring, h4, mul_assoc, h3, ← pow_add]
  congr 1; ring

end QuadFormsKB.Tamagawa.Measure.Weil
