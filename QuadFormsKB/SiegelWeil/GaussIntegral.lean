/-
# Local Gauss integrals and the global Gauss average

**Layer:** local at each finite place $v$ of a number field $F$, then global by the Chinese remainder theorem.

**Setting.** $Q = \sum_{i<n}a_ix_i^2$ with $n = 2m$ (0-based indices), $L_v = \mathcal O_v^n$, $\psi_v = \psi_p\circ\operatorname{Tr}$
(`psiV`), the self-dual measure on $F_v$ and its $n$-fold product (`muN`). For $b \in F_v$ the **local Gauss integral** is
$$I_v(b) = \int_{L_v}\psi_v(b\,Q(x))\,dx,$$
which is the integral in $f_v(wn(b)) = \gamma_Vc_B\,I_v(b)$ (`wfun_eq`).

**Results.**
* `integral_psiV_Qform_oneV` (every finite place, dyadic included): if $|b|_v \le q_v^{j}$, the integrand is constant on the
  cosets of $(\mathfrak p_v^j)^n$, so $I_v(b) = \operatorname{vol}(\mathfrak p_v^j)^n\sum_{y\in(\mathcal O_v/\mathfrak p_v^j)^n}\psi_v(b\,Q(\tilde y))$.
* `sum_RQ_eq_sum_quot`: the residues may be taken in $\mathcal O_F/\mathfrak p^j$ (`NF.quotEquiv`); `wfun_eq_locAvg`: for $u \in F$ with
  $|u|_v \le q_v^e$, $f_v(wn(u)) = \gamma_{V,v}c_{B,v}\operatorname{vol}(\mathcal O_v)^n\,A_v(u; e)$, $A_v(u; e) = N\mathfrak p^{-en}\sum_{r\in(\mathcal O_F/\mathfrak p^e)^n}\psi_v(uQ(\tilde r))$.
* `finsum_prod_crt` (the Chinese remainder theorem for sums of products) and `eTr_neg_eq_finprod` ($e(-\operatorname{Tr}y) = \prod_v\psi_v(y)$).
* **`finSec_wMat_nMat`**: for $Q = \sum_ib_ix_i^2$ over $\mathcal O_F$ and $u \in F$, the finite section on the big Bruhat cell is the
  global Gauss average, $f_f(wn(u), s_0) = \kappa_f\,G_Q(-u)$, $\kappa_f = \prod_{v<\infty}\gamma_{V,v}c_{B,v}\operatorname{vol}(\mathcal O_v)^n$
  (`kappaF`), $G_Q$ = `SingularNF.gaussAvg`. No limit and no convergence issue: both sides are finite.

Sources: Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. Math. 36 (1935), §3 [unverified]; Weil, Acta
Math. 113 (1965), Ch. II [unverified]; Tate's thesis (Cassels–Fröhlich Ch. XV), §4.1, Lemma 4.1.5 (the product formula for $\psi$).
-/
import Mathlib
import QuadFormsKB.Citation
import QuadFormsKB.SiegelWeil.LocalWhittaker
import QuadFormsKB.SiegelWeil.Eisenstein
import QuadFormsKB.SiegelWeil.SingularSeriesNF

open IsDedekindDomain NumberField MeasureTheory WithZero Filter Topology
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

/-! ### The integrand is locally constant -/

/-- $Q(x) - Q(x') = \sum_ia_i(x_i - x_i')(x_i + x_i')$. -/
lemma Qform_sub (x x' : Fin (2 * m) → Fv) :
    Qform a x - Qform a x' = ∑ i, (a i : Fv) * ((x i - x' i) * (x i + x' i)) := by
  unfold Qform
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **The local Gauss integrand is constant on cosets**: if $|a_i|_v \le 1$, $x, x' \in L_v$, $x \equiv x' \bmod \mathfrak p_v^j$ and
$|b|_v \le q_v^j$, then $\psi_v(bQ(x)) = \psi_v(bQ(x'))$. -/
lemma psiV_Qform_congr (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) {b : Fv} {j : ℕ}
    (hb : Valued.v b ≤ exp (j : ℤ)) {x x' : Fin (2 * m) → Fv} (hx : ∀ i, Valued.v (x i) ≤ 1)
    (hx' : ∀ i, Valued.v (x' i) ≤ 1) (hxx : ∀ i, Valued.v (x i - x' i) ≤ exp (-(j : ℤ))) :
    psiV v (b * Qform a x) = psiV v (b * Qform a x') := by
  have hd : Valued.v (Qform a x - Qform a x') ≤ exp (-(j : ℤ)) := by
    rw [Qform_sub]
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [map_mul, map_mul]
    have h1 : Valued.v (x i + x' i) ≤ 1 := (Valuation.map_add _ _ _).trans (max_le (hx i) (hx' i))
    calc Valued.v (a i : Fv) * (Valued.v (x i - x' i) * Valued.v (x i + x' i))
        ≤ 1 * (exp (-(j : ℤ)) * 1) := by gcongr <;> first | exact ha i | exact hxx i
      _ = exp (-(j : ℤ)) := by simp
  have hprod : Valued.v (b * (Qform a x - Qform a x')) ≤ 1 := by
    rw [map_mul]
    calc Valued.v b * Valued.v (Qform a x - Qform a x') ≤ exp (j : ℤ) * exp (-(j : ℤ)) := by gcongr
      _ = 1 := by rw [← exp_add]; simp
  have h := psiV_eq_one_of_le_one v hprod
  have e : b * Qform a x = b * Qform a x' + b * (Qform a x - Qform a x') := by ring
  rw [e, AddChar.map_add_eq_mul, h, mul_one]

lemma oneV_eq_ite (x : Fin (2 * m) → Fv) :
    oneV v (2 * m) x = if ∀ i, Valued.v (x i) ≤ 1 then 1 else 0 := by
  unfold oneV ptensor
  split_ifs with h
  · exact Finset.prod_eq_one fun i _ => by
      change ballIndV v 0 0 (x i) = 1
      rw [ballIndV, Set.indicator_of_mem (by simpa using h i)]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      change ballIndV v 0 0 (x i) = 0
      rw [ballIndV, Set.indicator_of_notMem (by simpa using hi)])

lemma selfDualV_latticeV_ne_top (k : ℤ) : selfDualV v (latticeV v k) ≠ ⊤ :=
  (isCompact_latticeV v k).measure_lt_top.ne

/-- **An integral over $\mathcal O_v^n$ of a function constant on the cosets of $(\mathfrak p_v^j)^n$** is a finite sum:
if $\psi_v(q(x)) = \psi_v(q(x'))$ whenever $x, x' \in \mathcal O_v^n$ and $x \equiv x' \bmod \mathfrak p_v^j$, then
$\int_{\mathcal O_v^n}\psi_v(q(x))\,dx = \operatorname{vol}(\mathfrak p_v^j)^n\sum_{y\in(\mathcal O_v/\mathfrak p_v^j)^n}\psi_v(q(\tilde y))$. -/
theorem integral_psiV_oneV_of_congr (q : (Fin (2 * m) → Fv) → Fv) (j : ℕ) [Fintype (RQ v j)]
    (hq : ∀ x x' : Fin (2 * m) → Fv, (∀ i, Valued.v (x i) ≤ 1) → (∀ i, Valued.v (x' i) ≤ 1) →
      (∀ i, Valued.v (x i - x' i) ≤ exp (-(j : ℤ))) → psiV v (q x) = psiV v (q x')) :
    ∫ x, (psiV v (q x) : ℂ) * oneV v (2 * m) x ∂(localDataV v).muN (2 * m) =
      (((selfDualV v).real (latticeV v j) ^ (2 * m) : ℝ) : ℂ) *
        ∑ y : Fin (2 * m) → RQ v j, (psiV v (q (liftR v j y)) : ℂ) := by
  classical
  have hlift : ∀ (y : Fin (2 * m) → RQ v j) i, Valued.v (liftR v j y i) ≤ 1 := fun y i =>
    (Quotient.out (y i)).2
  have hpt : ∀ x, (psiV v (q x) : ℂ) * oneV v (2 * m) x =
      ∑ y : Fin (2 * m) → RQ v j,
        (fiberR v j y).indicator (fun _ => (psiV v (q (liftR v j y)) : ℂ)) x := by
    intro x
    rw [oneV_eq_ite]
    split_ifs with hx
    · rw [mul_one, Finset.sum_eq_single (redR v j x hx)]
      · have hmem : x ∈ fiberR v j (redR v j x hx) := (mem_fiberR_iff v j).mpr ⟨hx, rfl⟩
        rw [Set.indicator_of_mem hmem]
        rw [hq _ _ hx (hlift _) fun i => hmem i (Set.mem_univ _)]
      · intro y _ hy
        refine Set.indicator_of_notMem (fun hmem => hy ?_) _
        obtain ⟨hx', e⟩ := (mem_fiberR_iff v j).mp hmem
        rw [← e]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [mul_zero]
      refine (Finset.sum_eq_zero fun y _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm
      exact valued_le_one_of_mem_fiberR v j hmem
  simp_rw [hpt]
  have hfin : ∀ y : Fin (2 * m) → RQ v j, (localDataV v).muN (2 * m) (fiberR v j y) ≠ ⊤ := fun y => by
    rw [measure_fiberR]
    exact ENNReal.pow_ne_top (selfDualV_latticeV_ne_top v j)
  rw [integral_finsetSum _ fun y _ =>
    (integrable_indicator_iff (measurableSet_fiberR v j y)).mpr (integrableOn_const (hfin y))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_indicator_const _ (measurableSet_fiberR v j y), Measure.real, measure_fiberR,
    ENNReal.toReal_pow, ← Measure.real, Complex.real_smul]

/-- **The local Gauss integral as a finite sum** (every finite place, dyadic included): for $|a_i|_v \le 1$, $j \ge 0$ and
$|b|_v \le q_v^j$,
$$\int_{\mathcal O_v^n}\psi_v(b\,Q(x))\,dx = \operatorname{vol}(\mathfrak p_v^j)^n\sum_{y\in(\mathcal O_v/\mathfrak p_v^j)^n}\psi_v(b\,Q(\tilde y)),$$
$\tilde y$ = `liftR` (any lift). *Proof:* $\mathcal O_v^n$ is the disjoint union of the cosets $\tilde y + (\mathfrak p_v^j)^n$, on each of which
the integrand is constant (`psiV_Qform_congr`). -/
@[kb "siegel1935" "§1 (Gauss sums as integrals over the p-adic integers) [unverified]"]
theorem integral_psiV_Qform_oneV (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) (j : ℕ) [Fintype (RQ v j)] {b : Fv}
    (hb : Valued.v b ≤ exp (j : ℤ)) :
    ∫ x, (psiV v (b * Qform a x) : ℂ) * oneV v (2 * m) x ∂(localDataV v).muN (2 * m) =
      (((selfDualV v).real (latticeV v j) ^ (2 * m) : ℝ) : ℂ) *
        ∑ y : Fin (2 * m) → RQ v j, (psiV v (b * Qform a (liftR v j y)) : ℂ) :=
  integral_psiV_oneV_of_congr v (fun x => b * Qform a x) j fun _ _ hx hx' hxx =>
    psiV_Qform_congr v a ha hb hx hx' hxx

/-- **Congruence for any form over $\mathcal O_F$** (every finite place, dyadic included): if $x, x' \in \mathcal O_v^n$,
$x \equiv x' \bmod \mathfrak p_v^j$ and $|b|_v \le q_v^j$, then $\psi_v(bQ(x)) = \psi_v(bQ(x'))$. -/
lemma psiV_evalIn_congr (Q : QuadForm (𝓞 F) (2 * m)) {b : Fv} {j : ℕ} (hb : Valued.v b ≤ exp (j : ℤ))
    {x y : Fin (2 * m) → Fv} (hx : ∀ i, Valued.v (x i) ≤ 1) (hy : ∀ i, Valued.v (y i) ≤ 1)
    (hxy : ∀ i, Valued.v (x i - y i) ≤ exp (-(j : ℤ))) :
    psiV v (b * Q.evalIn Fv x) = psiV v (b * Q.evalIn Fv y) := by
  have hc : ∀ i k, Valued.v (algebraMap (𝓞 F) Fv (Q.coeff i k)) ≤ 1 := fun i k => by
    have := valued_algebraMap_int_le_of_mem v (b := Q.coeff i k) (n := 0) (by simp)
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F Fv]
    simpa using this
  have hd : Valued.v (Q.evalIn Fv x - Q.evalIn Fv y) ≤ exp (-(j : ℤ)) := by
    unfold QuadForm.evalIn
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_le _ fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_le _ fun k _ => ?_
    split_ifs
    · have e : algebraMap (𝓞 F) Fv (Q.coeff i k) * x i * x k - algebraMap (𝓞 F) Fv (Q.coeff i k) * y i * y k =
          algebraMap (𝓞 F) Fv (Q.coeff i k) * (x i * (x k - y k) + (x i - y i) * y k) := by ring
      rw [e, map_mul]
      have h1 : Valued.v (x i * (x k - y k)) ≤ exp (-(j : ℤ)) := by
        rw [map_mul]
        calc Valued.v (x i) * Valued.v (x k - y k) ≤ 1 * exp (-(j : ℤ)) := by
              gcongr
              · exact hx i
              · exact hxy k
          _ = _ := one_mul _
      have h2 : Valued.v ((x i - y i) * y k) ≤ exp (-(j : ℤ)) := by
        rw [map_mul]
        calc Valued.v (x i - y i) * Valued.v (y k) ≤ exp (-(j : ℤ)) * 1 := by
              gcongr
              · exact hxy i
              · exact hy k
          _ = _ := mul_one _
      calc Valued.v (algebraMap (𝓞 F) Fv (Q.coeff i k)) * Valued.v (x i * (x k - y k) + (x i - y i) * y k)
          ≤ 1 * exp (-(j : ℤ)) := by
            gcongr
            · exact hc i k
            · exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
        _ = _ := one_mul _
    · simp
  have hprod : Valued.v (b * (Q.evalIn Fv x - Q.evalIn Fv y)) ≤ 1 := by
    rw [map_mul]
    calc Valued.v b * Valued.v (Q.evalIn Fv x - Q.evalIn Fv y) ≤ exp (j : ℤ) * exp (-(j : ℤ)) := by gcongr
      _ = 1 := by rw [← exp_add]; simp
  have h := psiV_eq_one_of_le_one v hprod
  have e : b * Q.evalIn Fv x = b * Q.evalIn Fv y + b * (Q.evalIn Fv x - Q.evalIn Fv y) := by ring
  rw [e, AddChar.map_add_eq_mul, h, mul_one]

end Local

/-! ### The global Gauss average as a product of local sums -/

section Global

open SingularNF

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

lemma eval_diag_eq {R : Type*} [CommRing R] {n : ℕ} (b : Fin n → R) (z : Fin n → R) :
    (QuadForm.diag b).eval z = ∑ i, b i * z i ^ 2 := by
  simp only [QuadForm.eval, QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

variable (v : HeightOneSpectrum (𝓞 F))

lemma valued_algebraMap_O_le_one (x : 𝓞 F) : Valued.v (algebraMap F (v.adicCompletion F) (ιO x)) ≤ 1 := by
  have := valued_algebraMap_int_le_of_mem v (b := x) (n := 0) (by simp)
  simpa using this

/-- $v(c) = q_v^{-v_\mathfrak p(c)}$ for $c \in \mathcal O_F\setminus0$, with $v_\mathfrak p(c)$ = `ordI v (span {c})`. -/
lemma valued_algebraMap_eq_ordI {c : 𝓞 F} (hc : c ≠ 0) :
    Valued.v (algebraMap F (v.adicCompletion F) (ιO c)) = exp (-(ordI v (Ideal.span {c}) : ℤ)) :=
  (HN.valued_algebraMap_int v c).trans (v.intValuation_if_neg hc)

/-- If $cu \in \mathcal O_F$ then $|u|_v \le q_v^{v_\mathfrak p(c)}$. -/
lemma valued_le_of_isDen {c : 𝓞 F} (hc : c ≠ 0) {u : F} (h : IsDen c u) :
    Valued.v (algebraMap F (v.adicCompletion F) u) ≤ exp (ordI v (Ideal.span {c}) : ℤ) := by
  obtain ⟨a, ha⟩ := h
  have hc' : ιO c ≠ 0 := algebraMap_ne_zero hc
  have hu : u = ιO a * (ιO c)⁻¹ := by rw [ha]; field_simp
  rw [hu, map_mul, map_mul, map_inv₀, map_inv₀, valued_algebraMap_eq_ordI v hc, exp_neg, inv_inv]
  calc Valued.v (algebraMap F (v.adicCompletion F) (ιO a)) * exp (ordI v (Ideal.span {c}) : ℤ)
      ≤ 1 * exp (ordI v (Ideal.span {c}) : ℤ) := by gcongr; exact valued_algebraMap_O_le_one v a
    _ = _ := one_mul _

variable {m : ℕ}

lemma evalIn_diag_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (b : Fin n → R) (z : Fin n → S) :
    (QuadForm.diag b).evalIn S z = ∑ i, algebraMap R S (b i) * z i ^ 2 := by
  simp only [QuadForm.evalIn, QuadForm.diag, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- Evaluation of a form over $\mathcal O_F$ commutes with $\mathcal O_F \to F_v$. -/
lemma evalIn_algebraMap (Q : QuadForm (𝓞 F) (2 * m)) (x : Fin (2 * m) → 𝓞 F) :
    Q.evalIn (v.adicCompletion F) (fun i => algebraMap F (v.adicCompletion F) (ιO (x i))) =
      algebraMap F (v.adicCompletion F) (ιO (Q.eval x)) := by
  simp only [QuadForm.eval, QuadForm.evalIn, map_sum, apply_ite (algebraMap F (v.adicCompletion F)),
    apply_ite ιO, map_mul, map_zero, Algebra.algebraMap_self, RingHom.id_apply,
    IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]

/-- **Local residues and global residues**: for any form $Q$ over $\mathcal O_F$ and $u \in F$ with $|u|_v \le q_v^j$, the sum over
$(\mathcal O_v/\mathfrak p_v^j)^n$ of the local Gauss integrand equals the sum over $(\mathcal O_F/\mathfrak p^j)^n$ (via `NF.quotEquiv`). -/
theorem sum_RQ_eq_sum_quot (Q : QuadForm (𝓞 F) (2 * m)) (j : ℕ) [Fintype (RQ v j)] [Fintype (𝓞 F ⧸ v.asIdeal ^ j)]
    {u : F} (hu : Valued.v (algebraMap F (v.adicCompletion F) u) ≤ exp (j : ℤ)) :
    ∑ y : Fin (2 * m) → RQ v j,
        (psiV v (algebraMap F (v.adicCompletion F) u * Q.evalIn (v.adicCompletion F) (liftR v j y)) : ℂ) =
      ∑ r : Fin (2 * m) → 𝓞 F ⧸ v.asIdeal ^ j,
        (psiV v (algebraMap F (v.adicCompletion F) (u * ιO (Q.eval (liftV r)))) : ℂ) := by
  symm
  refine Fintype.sum_equiv (LocalDensity.NF.vecEquiv v j) _ _ fun r => ?_
  rw [map_mul, ← evalIn_algebraMap v Q]
  congr 1
  refine psiV_evalIn_congr v Q hu (fun i => valued_algebraMap_O_le_one v _)
    (fun i => (Quotient.out (LocalDensity.NF.vecEquiv v j r i)).2) (fun i => ?_)
  have h1 : LocalDensity.NF.quotEquiv v j (r i) =
      Ideal.Quotient.mk _ (LocalDensity.NF.ι v (Quotient.out (r i))) := by
    conv_lhs => rw [← Ideal.Quotient.mk_out (r i)]
    exact LocalDensity.NF.quotEquiv_mk v j _
  have h2 := (valued_sub_le_iff_mk_eq v j (LocalDensity.NF.ι v (Quotient.out (r i)))
    (Quotient.out (LocalDensity.NF.quotEquiv v j (r i)))).mp (by rw [Ideal.Quotient.mk_out, h1])
  exact h2

variable (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)

/-- The diagonal model form is the diagonal form over $\mathcal O_F$ evaluated in $F_v$. -/
lemma Qform_aV_eq_evalIn (x : Fin (2 * m) → v.adicCompletion F) :
    Qform (aV (unitsOfInt b hb) v) x = (QuadForm.diag b).evalIn (v.adicCompletion F) x := by
  rw [evalIn_diag_eq]
  simp [Qform, aV_val, unitsOfInt, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]

lemma valued_aV_unitsOfInt_le (i : Fin (2 * m)) :
    Valued.v ((aV (unitsOfInt b hb) v i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≤ 1 :=
  valued_algebraMap_O_le_one v (b i)

/-- **The product formula for $\psi$ in the form $e(-\operatorname{Tr}y) = \prod_v\psi_v(y)$** ($y \in F$). -/
lemma eTr_neg_eq_finprod (y : F) :
    eTr (-y) = ∏ᶠ v : HeightOneSpectrum (𝓞 F), (psiV v (algebraMap F (v.adicCompletion F) y) : ℂ) := by
  have hm : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), psiV v (algebraMap F (v.adicCompletion F) y) : Circle) : ℂ) =
      ∏ᶠ v, (psiV v (algebraMap F (v.adicCompletion F) y) : ℂ) :=
    MonoidHom.map_finprod Circle.coeHom (hasFiniteMulSupport_psiV y)
  rw [← hm, finprod_psiV_eq_fourierChar, Real.fourierChar_apply, eTr, map_neg]
  push_cast
  ring_nf

/-- **The Chinese remainder theorem for sums of products**: if $I = \prod_{\mathfrak p\in T}\mathfrak p^{e_\mathfrak p}$ (distinct primes) and
each $\varphi_\mathfrak p$ on $\mathcal O_F^n$ depends only on the class mod $\mathfrak p^{e_\mathfrak p}$, then
$$\sum_{r\in(\mathcal O/I)^n}\prod_{\mathfrak p\in T}\varphi_\mathfrak p(\tilde r) = \prod_{\mathfrak p\in T}\sum_{s\in(\mathcal O/\mathfrak p^{e_\mathfrak p})^n}\varphi_\mathfrak p(\tilde s).$$ -/
theorem finsum_prod_crt {n : ℕ} {T : Finset (HeightOneSpectrum (𝓞 F))} (e : HeightOneSpectrum (𝓞 F) → ℕ)
    {I : Ideal (𝓞 F)} (hI : ∏ v ∈ T, v.asIdeal ^ e v = I)
    (φ : HeightOneSpectrum (𝓞 F) → (Fin n → 𝓞 F) → ℂ)
    (hφ : ∀ v ∈ T, ∀ x x' : Fin n → 𝓞 F, (∀ i, x i - x' i ∈ v.asIdeal ^ e v) → φ v x = φ v x') :
    ∑ᶠ r : Fin n → 𝓞 F ⧸ I, ∏ v ∈ T, φ v (liftV r) =
      ∏ v ∈ T, ∑ᶠ s : Fin n → 𝓞 F ⧸ v.asIdeal ^ e v, φ v (liftV s) := by
  classical
  have hprod : ∏ v : T, (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v = I := by
    rw [← hI]; exact Finset.prod_coe_sort T fun v => v.asIdeal ^ e v
  let E := HeightOneSpectrum.quotientEquivPiOfProdEq I (fun v : T => (v : HeightOneSpectrum (𝓞 F)))
    (fun v => e v) (fun a b h => Subtype.coe_injective.ne h) hprod
  have hE : ∀ (a : 𝓞 F) (v : T), E (Ideal.Quotient.mk I a) v = Ideal.Quotient.mk _ a := fun a v => rfl
  let V : (Fin n → 𝓞 F ⧸ I) ≃ (∀ v : T, Fin n → 𝓞 F ⧸ (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v) :=
    (Equiv.piCongrRight fun _ => E.toEquiv).trans (Equiv.piComm _)
  have hV : ∀ r (v : T) i, V r v i = Ideal.Quotient.mk _ (Quotient.out (r i)) := by
    intro r v i
    change E (r i) v = _
    conv_lhs => rw [← Ideal.Quotient.mk_out (r i)]
    exact hE _ v
  have hfin : ∀ (w : HeightOneSpectrum (𝓞 F)) (k : ℕ), Finite (𝓞 F ⧸ w.asIdeal ^ k) := fun w k =>
    finite_quot (pow_ne_zero _ w.ne_bot)
  let _ : ∀ (w : HeightOneSpectrum (𝓞 F)) (k : ℕ), Fintype (𝓞 F ⧸ w.asIdeal ^ k) := fun w k =>
    @Fintype.ofFinite _ (hfin w k)
  have : Finite (𝓞 F ⧸ I) := Finite.of_equiv _ E.symm.toEquiv
  let _ : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  simp_rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ r : Fin n → 𝓞 F ⧸ I, ∏ v ∈ T, φ v (liftV r) =
      ∏ v : T, φ v (liftV (V r v)) := by
    intro r
    rw [← Finset.prod_coe_sort T]
    refine Finset.prod_congr rfl fun v _ => hφ v v.2 _ _ fun i => ?_
    rw [← Ideal.Quotient.eq]
    simp only [liftV, Ideal.Quotient.mk_out, hV]
  simp_rw [hterm]
  rw [Fintype.sum_equiv V (fun r => ∏ v : T, φ v (liftV (V r v))) (fun s => ∏ v : T, φ v (liftV (s v)))
    (fun r => rfl)]
  rw [← Finset.prod_coe_sort T fun v => ∑ s : Fin n → 𝓞 F ⧸ v.asIdeal ^ e v, φ v (liftV s)]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]

/-- **The local Gauss average** at $v$ with exponent $e$: for $u \in F$,
$$A_v(Q; u, e) = N\mathfrak p^{-en}\sum_{r\in(\mathcal O_F/\mathfrak p^e)^n}\psi_v\big(u\,Q(\tilde r)\big),\qquad n = 2m,$$
for a form $Q$ over $\mathcal O_F$. -/
def locAvg (Q : QuadForm (𝓞 F) (2 * m)) (u : F) (e : ℕ) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℂ) ^ (e * (2 * m)))⁻¹ *
    ∑ᶠ r : Fin (2 * m) → 𝓞 F ⧸ v.asIdeal ^ e,
      (psiV v (algebraMap F (v.adicCompletion F) (u * ιO (Q.eval (liftV r)))) : ℂ)

lemma selfDualV_real_latticeV_nat (j : ℕ) :
    (selfDualV v).real (latticeV v j) =
      (selfDualV v).real (latticeV v 0) * ((Ideal.absNorm v.asIdeal : ℝ) ^ j)⁻¹ := by
  rw [selfDualV_real_latticeV, selfDualV_real_latticeV, zpow_zero, mul_one, zpow_natCast, modV_eq, inv_pow]

/-- **The local Gauss integral is the local Gauss average** (every finite place, dyadic included): for $u \in F$ with
$|u|_v \le q_v^e$,
$$f_v(wn(u)) = \gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^n\cdot A_v(u; e).$$ -/
theorem wfun_eq_locAvg (u : F) (e : ℕ) (hu : Valued.v (algebraMap F (v.adicCompletion F) u) ≤ exp (e : ℤ)) :
    wfun v (aV (unitsOfInt b hb) v) (algebraMap F (v.adicCompletion F) u) =
      (localDataV v).gammaV (aV (unitsOfInt b hb) v) * (localDataV v).cB (aV (unitsOfInt b hb) v) *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ) * locAvg v (QuadForm.diag b) u e := by
  classical
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) e
  let _ : Fintype (RQ v e) := Fintype.ofFinite _
  have hfin : Finite (𝓞 F ⧸ v.asIdeal ^ e) := finite_quot (pow_ne_zero _ v.ne_bot)
  let _ : Fintype (𝓞 F ⧸ v.asIdeal ^ e) := Fintype.ofFinite _
  rw [wfun_eq, integral_psiV_Qform_oneV v _ (valued_aV_unitsOfInt_le v b hb) e hu]
  simp_rw [Qform_aV_eq_evalIn v b hb]
  rw [sum_RQ_eq_sum_quot v (QuadForm.diag b) e hu, locAvg, finsum_eq_sum_of_fintype, selfDualV_real_latticeV_nat]
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  push_cast
  rw [mul_pow, inv_pow, ← pow_mul]
  ring

/-- With exponent $0$ the local Gauss average is $1$ when $u \in \mathcal O_v$. -/
lemma locAvg_zero (Q : QuadForm (𝓞 F) (2 * m)) {u : F} (hu : Valued.v (algebraMap F (v.adicCompletion F) u) ≤ 1) :
    locAvg v Q u 0 = 1 := by
  classical
  have hsub : Subsingleton (𝓞 F ⧸ v.asIdeal ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  have : Unique (Fin (2 * m) → 𝓞 F ⧸ v.asIdeal ^ 0) :=
    { default := fun _ => 0, uniq := fun x => funext fun i => Subsingleton.elim _ _ }
  rw [locAvg, zero_mul, pow_zero, inv_one, one_mul, finsum_unique]
  rw [psiV_eq_one_of_le_one v (by
    rw [map_mul, map_mul]
    exact mul_le_one' hu (valued_algebraMap_O_le_one v _)), Circle.coe_one]

/-! ### The finite section on the big Bruhat cell -/

omit [IsTotallyReal F] in
/-- The image of $w$ in $\mathrm{SL}_2(F_v)$ is $w$. -/
lemma locSL_wMat (v : HeightOneSpectrum (𝓞 F)) : locSL v (wMat : SL(2, F)) = wMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [locSL_apply]

omit [IsTotallyReal F] in
/-- At $s = s_0 = m - 1$ the standard section is the Weil-representation section. -/
lemma secS_s₀' (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)
    (Φ : (localDataV v).Sn (2 * m)) (g : SL(2, v.adicCompletion F)) :
    secS v a Φ g ((m : ℂ) - 1) = secV v a Φ g := by
  simp [secS]

variable (m) in
/-- **The finite constant of the big cell**: $\kappa_f = \prod_{v<\infty}\gamma_{V,v}\,c_{B,v}\operatorname{vol}(\mathcal O_v)^n$ (a finite product). -/
def kappaF (a : Fin (2 * m) → Fˣ) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), (localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
    (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ)

omit [IsTotallyReal F] in
lemma hasFiniteMulSupport_kappa (a : Fin (2 * m) → Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
        (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ) := by
  have hvol : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ) :=
    (hasFiniteMulSupport_vol (F := F)).subset fun v hv h' => hv (by simp only at h' ⊢; rw [h']; simp)
  exact ((hasFiniteMulSupport_gammaV a).mul (hasFiniteMulSupport_cB a)).mul hvol

/-- The exponent of $\mathfrak p_v$ in the fixed denominator $(\mathrm{den}\,u)$ of $u \in F$. -/
abbrev denExp (u : F) (v : HeightOneSpectrum (𝓞 F)) : ℕ := ordI v (Ideal.span {den u})

lemma denExp_eq_zero {u : F} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ suppI (span_ne_bot (den_ne_zero u))) :
    denExp u v = 0 := by
  by_contra h
  exact hv ((mem_suppI _ v).mpr ((ordI_ne_zero_iff (span_ne_bot (den_ne_zero u)) v).mp h))

lemma valued_le_one_of_not_mem_suppI {u : F} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ suppI (span_ne_bot (den_ne_zero u))) :
    Valued.v (algebraMap F (v.adicCompletion F) u) ≤ 1 := by
  have := valued_le_of_isDen v (den_ne_zero u) (isDen_den u)
  rwa [show (ordI v (Ideal.span {den u}) : ℤ) = 0 by exact_mod_cast denExp_eq_zero hv, exp_zero] at this

lemma mulSupport_locAvg_subset (Q : QuadForm (𝓞 F) (2 * m)) (u : F) :
    Function.mulSupport (fun v => locAvg v Q u (denExp u v)) ⊆ suppI (span_ne_bot (den_ne_zero u)) := by
  intro v hv
  by_contra hvT
  apply hv
  simp only
  rw [denExp_eq_zero hvT]
  exact locAvg_zero v Q (valued_le_one_of_not_mem_suppI hvT)

lemma hasFiniteMulSupport_locAvg (Q : QuadForm (𝓞 F) (2 * m)) (u : F) :
    Function.HasFiniteMulSupport fun v => locAvg v Q u (denExp u v) :=
  (suppI (span_ne_bot (den_ne_zero u))).finite_toSet.subset (mulSupport_locAvg_subset Q u)

/-- **The product of the local Gauss averages is the global Gauss average** (every form $Q$ over $\mathcal O_F$ in $n = 2m$ variables,
every finite place, dyadic included): for $u \in F$ with denominator $c$,
$$\prod_{v<\infty}A_v(Q; u, v(c)) = G_Q(-u) = N(c)^{-n}\sum_{r\in(\mathcal O/c)^n}e\big(-\operatorname{Tr}(u\,Q(\tilde r))\big).$$
*Proof:* the Chinese remainder theorem (`finsum_prod_crt`) and $\prod_v\psi_v(y) = e(-\operatorname{Tr}y)$ (`eTr_neg_eq_finprod`). -/
@[kb "siegel1935" "§3 (the Gauss sums of the singular series are products of local Gauss sums) [unverified]"]
theorem finprod_locAvg (Q : QuadForm (𝓞 F) (2 * m)) (u : F) :
    ∏ᶠ v, locAvg v Q u (denExp u v) = gaussAvg Q (-u) := by
  classical
  set c := den u
  have hc : c ≠ 0 := den_ne_zero u
  have hcu : IsDen c u := isDen_den u
  have hcu' : IsDen c (-u) := by
    obtain ⟨t, ht⟩ := hcu; exact ⟨-t, by rw [map_neg, ht]; ring⟩
  set I : Ideal (𝓞 F) := Ideal.span {c}
  have hI : I ≠ ⊥ := span_ne_bot hc
  set T := suppI hI
  set e : HeightOneSpectrum (𝓞 F) → ℕ := fun v => ordI v I
  have hT : ∏ v ∈ T, v.asIdeal ^ e v = I := prod_suppI hI subset_rfl
  rw [finprod_eq_prod_of_mulSupport_subset _ (mulSupport_locAvg_subset Q u)]
  rw [gaussAvg_eq Q hc hcu', gAvg]
  have hψ : ∀ r : Fin (2 * m) → 𝓞 F ⧸ I, eTr (-u * ιO (Q.eval (liftV r))) =
      ∏ v ∈ T, (psiV v (algebraMap F (v.adicCompletion F) (u * ιO (Q.eval (liftV r)))) : ℂ) := by
    intro r
    rw [neg_mul, eTr_neg_eq_finprod]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    apply hv
    simp only
    rw [psiV_eq_one_of_le_one v (by
      rw [map_mul, map_mul]
      exact mul_le_one' (valued_le_one_of_not_mem_suppI hvT) (valued_algebraMap_O_le_one v _)), Circle.coe_one]
  simp_rw [hψ]
  rw [finsum_prod_crt e hT (fun v x => (psiV v (algebraMap F (v.adicCompletion F)
    (u * ιO (Q.eval x))) : ℂ)) ?_]
  · -- the norms
    have hN : (Ideal.absNorm I : ℂ) ^ (2 * m) = ∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℂ) ^ (e v * (2 * m)) := by
      rw [← hT, map_prod, Nat.cast_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_pow, Nat.cast_pow, ← pow_mul]
    rw [hN, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rfl
  · intro v _ x y hxy
    refine congrArg (fun z : Circle => (z : ℂ)) ?_
    rw [show u * ιO (Q.eval x) = u * ιO (Q.eval y) + u * (ιO (Q.eval x) - ιO (Q.eval y)) by ring,
      map_add, AddChar.map_add_eq_mul]
    rw [psiV_eq_one_of_le_one v (x := algebraMap F _ (u * (ιO (Q.eval x) - ιO (Q.eval y)))) ?_, mul_one]
    have hQ : Q.eval x - Q.eval y ∈ v.asIdeal ^ e v := by
      rw [← Ideal.Quotient.eq, mk_eval, mk_eval]
      congr 1; funext i; exact Ideal.Quotient.eq.mpr (hxy i)
    have h1 := valued_algebraMap_int_le_of_mem v hQ
    have h2 := valued_le_of_isDen v hc hcu
    rw [← map_sub, map_mul, map_mul]
    calc Valued.v (algebraMap F (v.adicCompletion F) u) *
          Valued.v (algebraMap F (v.adicCompletion F) (ιO (Q.eval x - Q.eval y)))
        ≤ exp (e v : ℤ) * exp (-(e v : ℤ)) := by gcongr
      _ = 1 := by rw [← exp_add]; simp

/-- **The finite section on the big cell is the global Gauss average** (every finite place, dyadic included; no
convergence issue: a finite product). For $Q = \sum_{i<n}b_ix_i^2$, $b_i \in \mathcal O_F\setminus0$, $n = 2m$, and $u \in F$,
$$f_f(wn(u), s_0) = \prod_{v<\infty}f_v(wn(u)) = \kappa_f\cdot G_Q(-u),\qquad
  G_Q(-u) = N(c)^{-n}\sum_{r\in(\mathcal O/c)^n}e\big(-\operatorname{Tr}(u\,Q(\tilde r))\big)\ (cu \in \mathcal O),$$
$G_Q$ = `SingularNF.gaussAvg`. *Proof:* at each $v$, $f_v(wn(u)) = \gamma_vc_v\int_{L_v}\psi_v(uQ)$ is $\gamma_vc_v\operatorname{vol}(\mathcal O_v)^n$ times the
local Gauss average modulo $\mathfrak p^{v(c)}$ (`wfun_eq_locAvg`); the product of the local averages is the global one by the
Chinese remainder theorem (`finsum_prod_crt`) and $\prod_v\psi_v(y) = e(-\operatorname{Tr}y)$ (`eTr_neg_eq_finprod`). -/
@[kb "weil1965" "Ch. II (the local factors of the Eisenstein series at the big cell) [unverified]; Siegel (1935), §3 (Gauss sums) [unverified]"]
theorem finSec_wMat_nMat (u : F) :
    finSec (unitsOfInt b hb) (wMat * nMat u) ((m : ℂ) - 1) =
      kappaF m (unitsOfInt b hb) * gaussAvg (QuadForm.diag b) (-u) := by
  classical
  set a := unitsOfInt b hb
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      secS v (aV a v) (oneS v m) (locSL v (wMat * nMat u)) ((m : ℂ) - 1) =
        ((localDataV v).gammaV (aV a v) * (localDataV v).cB (aV a v) *
          (((selfDualV v).real (latticeV v 0) ^ (2 * m) : ℝ) : ℂ)) *
            locAvg v (QuadForm.diag b) u (denExp u v) := by
    intro v
    rw [map_mul, locSL_wMat, locSL_nMat, secS_s₀']
    exact wfun_eq_locAvg v b hb u _ (valued_le_of_isDen v (den_ne_zero u) (isDen_den u))
  unfold finSec
  simp_rw [hloc]
  rw [finprod_mul_distrib (hasFiniteMulSupport_kappa a) (hasFiniteMulSupport_locAvg _ u), kappaF,
    finprod_locAvg]

end Global

end QuadFormsKB.SiegelWeil
