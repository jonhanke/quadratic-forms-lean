import QuadFormsKB.Tamagawa.Measure.Weil.PDCongruence
import QuadFormsKB.Tamagawa.BinaryRegChange

/-!
# Binary $\tau = 2$, non-compact case: the Tamagawa measure of the principal congruence subgroups of $SO(\langle1,D\rangle)(F_v)$

**Layer:** number fields. $F$ is a number field, $v$ a finite place (`HeightOneSpectrum (𝓞 F)`, dyadic and ramified places
included), $F_v$ = `v.adicCompletion F`, $\mathfrak o_v$ = `v.adicCompletionIntegers F`, $\varpi$ = `LocalDensity.NF.π v` a
uniformizer, $q = N(v)$ (`DVR.q 𝔬`), $D\in\mathcal O_F\setminus0$, $Q_0 = \langle1,D\rangle = x_0^2 + Dx_1^2$ =
`diagForm1 D` (Hessian $\mathrm{diag}(2, 2D)$), and the exponents $s,\delta\in\mathbb N$ are given by
$|2|_v = q^{-s}$ and $|D|_v = q^{-\delta}$ (hypotheses `hs`, `hδ`, stated as `Valued.v _ = exp (-s)`, `exp (-δ)`).
$\mu_v$ is the gauge-form measure `Measure.muLoc v Q₀ 1` on $O(V)(F_v)$ and $\mu^{SO}_v$ = `Measure.muLocSO v Q₀ 1` the
measure on $SO(V)(F_v)$ (the restriction of $\mu_v$, `muLocSO_eq_comap`).

**Defines**
* `congSubSOBin v D m hm` ($m\ge1$): the subgroup $K_m\cap SO(V)(F_v)$ of `SOv v (diagForm1 D)`, where
  $K_m = O(V)(F_v)\cap(1 + \varpi^mM_2(\mathfrak o_v))$ is `LerayPadic.congSub`.

**Proves**
* `congSub_le_soSub_binary`, `coe_congSubSO`: for $m > s$ (indeed $m > v(2)$) every element of $K_m$ has determinant
  $+1$ (it is $\equiv1\bmod\varpi^m$ and equals $\pm1$, and $-1\not\equiv1$), so $K_m\subseteq SO(V)(F_v)$ and the
  subgroup `congSubSOBin` is exactly $K_m$;
* `isOpen_congSubSO`, `isCompact_congSubSO`: `congSubSOBin` is open and compact in $SO(V)(F_v)$;
* `card_kerD_diag2`: for a diagonal binary Hessian $\mathrm{diag}(h_0,h_1)$ with $\varpi^{e_i}\,\|\,h_i$, $e_i\le j$,
  $\#\{Z\in M_2(\mathfrak o_v/\varpi^j) : D_1Z\equiv0\} = q^{e_0+e_1}\,q^{\min(e_0,e_1)}\,q^j$ (the binary analogue of
  `card_kerD_diag3`: the diagonal entries $z_{00},z_{11}$ and the pair $(z_{01},z_{10})$ with
  $h_0z_{01} + h_1z_{10}\equiv0$);
* `muLoc_congSub_diagForm1`: for $m\ge 4s+2\delta+1$, $\mu_v(K_m) = q^{3s+\delta}/q^{m}$ (in $[0,\infty]$);
* **`muLocSO_congSubSO`** (the main theorem): for $D\ne0$, $|2|_v = q^{-s}$, $|D|_v = q^{-\delta}$ and $m\ge4s+2\delta+1$,
  $$\mu^{SO}_v(K_m\cap SO) = c_v\,q^{-m},\qquad c_v = q^{3s+\delta} = |2|_v^{-3}|D|_v^{-1} = |8D|_v^{-1};$$
  `muLocSO_congSubSO_norm` states the same with the norms $\lVert2\rVert$, $\lVert D\rVert$ of $F_v$:
  $\mu^{SO}_v = \lVert 2\rVert^{-3}\lVert D\rVert^{-1}\,(q^{-1})^m$.
  `exists_valued_eq_exp_neg` shows that every $D\in\mathcal O_F\setminus0$ has such an exponent $\delta$.

*Proof.* The Hessian is $\mathrm{diag}(2,2D)$, so $\varpi^d\,\|\,\det H$ with $d = 2s+\delta$ and
`muLoc_congSub_eq` (with $j = 2d+1\le m$) gives $\mu_v(K_m) = \#S_j/q^{m+j}$, $S_j$ the solutions mod $\varpi^j$ of
$D_1Z\equiv0$, where $D_1Z = (2z_{00},\ 2D z_{11},\ 2z_{01} + 2Dz_{10})$ is the coefficient vector of
$Z^{\mathsf T}H + HZ$. The count factors over $z_{00}$, $z_{11}$ and the pair $(z_{01},z_{10})$:
$q^{s}\cdot q^{s+\delta}\cdot q^{\min(s,s+\delta)}q^j = q^{3s+\delta+j}$. Dividing by $q^{m+j}$ gives $q^{3s+\delta-m}$.

Source: Weil 1982, §2.2 (gauge-form volumes of congruence subgroups) [unverified].
-/

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

theorem forall_upperIdx_two (P : UpperIdx 2 → Prop) :
    (∀ p, P p) ↔ (P ⟨(0, 0), le_rfl⟩ ∧ P ⟨(1, 1), le_rfl⟩) ∧ P ⟨(0, 1), by decide⟩ := by
  constructor
  · intro h; exact ⟨⟨h _, h _⟩, h _⟩
  · rintro ⟨⟨h00, h11⟩, h01⟩ ⟨⟨i, l⟩, hil⟩
    fin_cases i <;> fin_cases l <;> first | assumption | exact absurd hil (by decide)

/-- $D_1$ for a diagonal binary Hessian $\mathrm{diag}(h_0,h_1)$: $(D_1Z)_{ii} = h_iZ_{ii}$,
$(D_1Z)_{01} = h_0Z_{01} + h_1Z_{10}$. -/
theorem formD_oneVec_diag2 (Q : QuadForm 𝔬 2) (h : Fin 2 → 𝔬) (hH : Q.hessian = Matrix.diagonal h)
    (w : Fin 2 × Fin 2 → 𝔬) (i l : Fin 2) (hil : i ≤ l) :
    formD Q (oneVec v) w ⟨(i, l), hil⟩ = if i = l then h i * w (i, i) else h i * w (i, l) + h l * w (l, i) := by
  fin_cases i <;> fin_cases l <;>
  first
  | exact absurd hil (by decide)
  | (simp [formD, DVR.bil, DVR.col, toMat, oneVec, hH, Matrix.mulVec, dotProduct,
      Matrix.diagonal_apply]; try ring)

/-- The block decomposition $M_2(A)\cong A^2\times A^2$ (diagonal entries $(z_{00},z_{11})$; the pair $(z_{01},z_{10})$). -/
def blockEquiv2 (A : Type*) : (Fin 2 × Fin 2 → A) ≃ (A × A) × (A × A) where
  toFun z := ((z (0, 0), z (1, 1)), (z (0, 1), z (1, 0)))
  invFun t := fun p => match p with
    | (0, 0) => t.1.1 | (1, 1) => t.1.2 | (0, 1) => t.2.1 | (1, 0) => t.2.2
  left_inv z := by
    funext ⟨i, l⟩
    fin_cases i <;> fin_cases l <;> rfl
  right_inv t := rfl

/-- **The kernel of $D_1\bmod\varpi^j$ for a diagonal binary form** $\mathrm{diag}(h_0,h_1)$ with
$\varpi^{e_i}\,\|\,h_i$, $e_i\le j$: it has $q^{e_0+e_1}\cdot q^{\min(e_0,e_1)}q^j$ elements. -/
theorem card_kerD_diag2 (Q : QuadForm 𝔬 2) (h : Fin 2 → 𝔬) (hH : Q.hessian = Matrix.diagonal h) (j : ℕ)
    (e : Fin 2 → ℕ) (he : ∀ i, πv ^ e i ∣ h i) (he' : ∀ i, ¬ πv ^ (e i + 1) ∣ h i) (hej : ∀ i, e i ≤ j) :
    Nat.card {z : Fin 2 × Fin 2 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} =
      (DVR.q 𝔬 ^ e 0 * DVR.q 𝔬 ^ e 1) * (DVR.q 𝔬 ^ min (e 0) (e 1) * DVR.q 𝔬 ^ j) := by
  have hπ := NF.irreducible_π v
  set C1 := fun i : Fin 2 => {x : RQ v j // πv ^ j ∣ h i * lift1 πv j x}
  set C2 := fun i l : Fin 2 => {p : RQ v j × RQ v j // πv ^ j ∣ h i * lift1 πv j p.1 + h l * lift1 πv j p.2}
  have e1 : {z : Fin 2 × Fin 2 → RQ v j // ∀ p, πv ^ j ∣ formD Q (oneVec v) (liftI πv j z) p} ≃
      (C1 0 × C1 1) × C2 0 1 := by
    refine (Equiv.subtypeEquiv (blockEquiv2 _) fun z => ?_).trans
      ((Equiv.subtypeProdEquivProd).trans (Equiv.prodCongr (Equiv.subtypeProdEquivProd) (Equiv.refl _)))
    rw [forall_upperIdx_two]
    simp only [formD_oneVec_diag2 v Q h hH, blockEquiv2, Equiv.coe_fn_mk, ite_true, Fin.reduceEq, ite_false]
    rfl
  rw [Nat.card_congr e1]
  simp only [Nat.card_prod, C1, C2]
  rw [DVR.card_dvd_mul_lift1 πv hπ (he 0) (he' 0) (hej 0), DVR.card_dvd_mul_lift1 πv hπ (he 1) (he' 1) (hej 1),
    DVR.card_dvd_add_lift1' πv hπ (he 0) (he' 0) (he 1) (he' 1) (hej 0) (hej 1)]

end QuadFormsKB.Tamagawa.Measure.LerayPadic

namespace QuadFormsKB.Tamagawa.Measure.Weil

open QuadFormsKB.Lattices LocalDensity LerayPadic LocalZeta QuadFormsKB.Tamagawa

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F
local notation "πv" => LocalDensity.NF.π v

/-! ### The subgroup $K_m\cap SO(V)(F_v)$ -/

variable (D : 𝓞 F)

/-- **The principal congruence subgroup of $SO(\langle1,D\rangle)(F_v)$:** $K_m\cap SO(V)(F_v)$, where
$K_m = O(V)(F_v)\cap(1 + \varpi^mM_2(\mathfrak o_v))$ (`LerayPadic.congSub`), $m\ge1$, as a subgroup of
$SO(V)(F_v)$ = `Measure.SOv v (diagForm1 D)`. For $m > v(2)$ it equals $K_m$ (`coe_congSubSO`). -/
def congSubSOBin (m : ℕ) (hm : 1 ≤ m) : Subgroup (Measure.SOv v (diagForm1 D)) :=
  (congSub v (diagForm1 D) m hm).subgroupOf (soSub ((diagForm1 D).map (algebraMap (𝓞 F) F)) (v.adicCompletion F))

variable {D}

/-- **$K_m\subseteq SO(V)(F_v)$ for $m > v(2)$:** an element of $K_m$ has determinant $\equiv1\bmod\varpi^m$ and
$\det = \pm1$; since $-1 - 1 = -2$ has valuation $q^{-v(2)}$, $\det = -1$ would force $m\le v(2)$. Here
$|2|_v = q^{-s}$ and $s < m$. -/
theorem congSub_le_soSub_binary (hQ : (diagForm1 D).Nondegenerate) {s m : ℕ}
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hsm : s < m) (hm : 1 ≤ m)
    {g : orthGroup ((diagForm1 D).map (algebraMap (𝓞 F) F)) Fv} (hg : g ∈ congSub v (diagForm1 D) m hm) :
    g ∈ soSub ((diagForm1 D).map (algebraMap (𝓞 F) F)) Fv := by
  have hd := valued_det_sub_one_le v ((mem_congSub v (diagForm1 D)).1 hg)
  rcases det_eq_one_or_neg_one _ (Measure.nondegenerate_QF (diagForm1 D) hQ) g with h | h
  · exact h
  · exfalso
    rw [h, show (-1 : Fv) - 1 = -2 by ring, Valuation.map_neg, hs, exp_le_exp] at hd
    omega

/-- For $m > s$ the subgroup `congSubSOBin` is the whole of $K_m$ (as sets of $SO(V)(F_v)$, the preimage of $K_m$ under the
inclusion), and the image under the inclusion is $K_m$. -/
theorem coe_congSubSO (m : ℕ) (hm : 1 ≤ m) :
    (congSubSOBin v D m hm : Set (Measure.SOv v (diagForm1 D))) =
      Subtype.val ⁻¹' (congSub v (diagForm1 D) m hm : Set (orthGroup ((diagForm1 D).map (algebraMap (𝓞 F) F)) Fv)) :=
  rfl

theorem image_congSubSO (hQ : (diagForm1 D).Nondegenerate) {s m : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hsm : s < m) (hm : 1 ≤ m) :
    Subtype.val '' (congSubSOBin v D m hm : Set (Measure.SOv v (diagForm1 D))) =
      (congSub v (diagForm1 D) m hm : Set (orthGroup ((diagForm1 D).map (algebraMap (𝓞 F) F)) Fv)) := by
  rw [coe_congSubSO, Set.image_preimage_eq_inter_range, Subtype.range_coe, Set.inter_eq_left]
  exact fun g hg => congSub_le_soSub_binary v hQ hs hsm hm hg

/-- `congSubSOBin` is open in $SO(V)(F_v)$. -/
theorem isOpen_congSubSO (m : ℕ) (hm : 1 ≤ m) :
    IsOpen (congSubSOBin v D m hm : Set (Measure.SOv v (diagForm1 D))) :=
  (isOpen_congSub v (diagForm1 D) m hm).preimage continuous_subtype_val

/-- `congSubSOBin` is compact in $SO(V)(F_v)$ (a closed subset of the compact group $SO(L_v)$-neighbourhood
$O(L_v)\supseteq K_m$). -/
theorem isCompact_congSubSO (m : ℕ) (hm : 1 ≤ m) :
    IsCompact (congSubSOBin v D m hm : Set (Measure.SOv v (diagForm1 D))) := by
  have hc : IsCompact (congSub v (diagForm1 D) m hm : Set (orthGroup ((diagForm1 D).map (algebraMap (𝓞 F) F)) Fv)) :=
    (isCompact_stdStab v _).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_congSub v (diagForm1 D) m hm))
      (congSub_le_stdStab v (diagForm1 D) m hm)
  exact (isClosed_soSub v ((diagForm1 D).map (algebraMap (𝓞 F) F))).isClosedEmbedding_subtypeVal.isCompact_preimage hc

/-! ### The count -/

omit [NumberField F] in
theorem hessian_diagForm1_diagonal :
    (diagForm1 D).hessian = Matrix.diagonal ![2, 2 * D] := by
  rw [hessian_diagForm1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem hessian_Qp_diagForm1 : (NF.Qp v (diagForm1 D)).hessian =
    Matrix.diagonal (fun i => NF.ι v (![2, 2 * D] i)) := by
  rw [NF.Qp, QuadForm.hessian_map, hessian_diagForm1_diagonal, Matrix.diagonal_map (map_zero _)]

theorem valued_ι_two_binary {s : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) :
    Valued.v ((NF.ι v (2 : 𝓞 F) : 𝔬) : Fv) = exp (-(s : ℤ)) := by
  rw [coe_ι, show ((2 : 𝓞 F) : F) = 2 by
    rw [show ((2 : 𝓞 F) : F) = algebraMap (𝓞 F) F 2 from rfl, map_ofNat], map_ofNat, hs]

theorem valued_ι_two_mul_binary {s δ : ℕ} (hs : Valued.v (2 : Fv) = exp (-(s : ℤ)))
    (hδ : Valued.v (algebraMap F Fv (D : F)) = exp (-(δ : ℤ))) :
    Valued.v ((NF.ι v (2 * D) : 𝔬) : Fv) = exp (-((s + δ : ℕ) : ℤ)) := by
  rw [coe_ι, show ((2 * D : 𝓞 F) : F) = 2 * (D : F) by
    rw [show ((2 * D : 𝓞 F) : F) = algebraMap (𝓞 F) F (2 * D) from rfl, map_mul, map_ofNat],
    map_mul, map_ofNat, map_mul, hs, hδ, ← WithZero.exp_add]
  congr 1; push_cast; ring

/-- **The gauge-form volume of $K_m$ for $\langle1,D\rangle$** ($|2|_v = q^{-s}$, $|D|_v = q^{-\delta}$,
$m\ge 4s+2\delta+1$): $\mu_v(K_m) = q^{3s+\delta}/q^m$ in $[0,\infty]$. -/
theorem muLoc_congSub_diagForm1 {s δ m : ℕ} (hD : D ≠ 0)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hδ : Valued.v (algebraMap F Fv (D : F)) = exp (-(δ : ℤ)))
    (hm : 4 * s + 2 * δ + 1 ≤ m) :
    Measure.muLoc v (diagForm1 D) 1 (congSub v (diagForm1 D) m (by omega) : Set _) =
      (DVR.q 𝔬 : ℝ≥0∞) ^ (3 * s + δ) / (DVR.q 𝔬 : ℝ≥0∞) ^ m := by
  have hQ : (diagForm1 D).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1]
    exact mul_ne_zero (by norm_num) hD
  set d := 2 * s + δ
  set j := 2 * d + 1
  have hq0 : (DVR.q 𝔬 : ℝ≥0∞) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  have hqt : (DVR.q 𝔬 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set h : Fin 2 → 𝔬 := fun i => NF.ι v (![2, 2 * D] i)
  set e : Fin 2 → ℕ := ![s, s + δ]
  have hval : ∀ i, Valued.v ((h i : 𝔬) : Fv) = exp (-(e i : ℤ)) := by
    intro i
    fin_cases i
    · exact valued_ι_two_binary v hs
    · exact valued_ι_two_mul_binary v hs hδ
  have hdiv := fun i => pow_dvd_of_valued (hval i)
  have hdet : Valued.v (((NF.Qp v (diagForm1 D)).hessian.det : 𝔬) : Fv) = exp (-(d : ℤ)) := by
    rw [hessian_Qp_diagForm1, Matrix.det_diagonal, Fin.prod_univ_two]
    change Valued.v ((h 0 : Fv) * (h 1 : Fv)) = _
    rw [map_mul, hval 0, hval 1, ← WithZero.exp_add]
    congr 1; simp [d, e]; ring
  obtain ⟨hd, hd'⟩ := pow_dvd_of_valued hdet
  rw [muLoc_congSub_eq v _ hQ m (by omega) d j hd hd' le_rfl (by omega),
    card_kerD_diag2 v _ h (hessian_Qp_diagForm1 v) j e (fun i => (hdiv i).1) (fun i => (hdiv i).2)
      (fun i => by
        have : e i ≤ s + δ := by fin_cases i <;> simp [e]
        omega)]
  have he0 : e 0 = s := rfl
  have he1 : e 1 = s + δ := rfl
  have m01 : min (e 0) (e 1) = s := by rw [he0, he1]; exact min_eq_left (by omega)
  rw [m01, he0, he1]
  set q := (DVR.q 𝔬 : ℝ≥0∞)
  simp only [Nat.cast_pow, ← pow_add]
  rw [show (2 * (2 - 1) / 2) = 1 by norm_num,
    show s + (s + δ) + (s + j) = (3 * s + δ) + j by ring, mul_one, add_comm m j,
    ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [pow_add q (3 * s + δ) j, pow_add q j m, ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0))
    (Or.inl (ENNReal.pow_ne_top hqt))]
  calc (q ^ j)⁻¹ * (q ^ m)⁻¹ * (q ^ (3 * s + δ) * q ^ j)
      = q ^ (3 * s + δ) * (q ^ j * (q ^ j)⁻¹) * (q ^ m)⁻¹ := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), mul_one, mul_comm]

/-- **The Tamagawa measure of the principal congruence subgroups of $SO(\langle1,D\rangle)(F_v)$** (every finite
place, dyadic and ramified included): for $D\ne0$, $|2|_v = q^{-s}$, $|D|_v = q^{-\delta}$ and $m\ge4s+2\delta+1$,
$$\mu^{SO}_v(K_m\cap SO(V)(F_v)) = c_v\,q^{-m},\qquad c_v = q^{3s+\delta} = |2|_v^{-3}\,|D|_v^{-1} = |8D|_v^{-1}.$$
(Here $\mu^{SO}_v$ is `Measure.muLocSO v (diagForm1 D) 1`, the restriction of the gauge-form measure.) -/
@[kb "weil1982" "§2.2 (gauge-form volumes of congruence subgroups) [unverified]"]
theorem muLocSO_congSubSO {s δ m : ℕ} (hD : D ≠ 0)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hδ : Valued.v (algebraMap F Fv (D : F)) = exp (-(δ : ℤ)))
    (hm : 4 * s + 2 * δ + 1 ≤ m) :
    Measure.muLocSO v (diagForm1 D) 1 (congSubSOBin v D m (by omega) : Set _) =
      ENNReal.ofReal ((DVR.q 𝔬 : ℝ) ^ (3 * s + δ) * ((DVR.q 𝔬 : ℝ)⁻¹) ^ m) := by
  have hQ : (diagForm1 D).Nondegenerate := by
    rw [QuadForm.Nondegenerate, hessian_det_diagForm1]
    exact mul_ne_zero (by norm_num) hD
  have hq : (0 : ℝ) < (DVR.q 𝔬 : ℝ) := by exact_mod_cast q_pos v
  rw [Measure.muLocSO_eq_comap v _ hQ (by norm_num) one_pos,
    (Measure.measurableEmbedding_soSub v _ hQ).comap_apply,
    image_congSubSO v hQ hs (by omega) (by omega), muLoc_congSub_diagForm1 v hD hs hδ hm,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hq.le, ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_inv_of_pos hq, ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul,
    ← ENNReal.inv_pow, mul_comm]

theorem norm_of_valued_exp_binary {x : Fv} {k : ℕ} (hx : Valued.v x = exp (-(k : ℤ))) :
    ‖x‖ = ((DVR.q 𝔬 : ℝ)⁻¹) ^ k := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero] at hx; exact exp_ne_zero hx.symm
  rw [QuadFormsKB.LocalZeta.norm_eq_absNorm_pow v hx0, hx, log_exp, NF.q_completion, _root_.zpow_neg, zpow_natCast,
    inv_pow]

/-- **The same with norms** ($\lVert\cdot\rVert$ the norm of $F_v$, $\lVert x\rVert = q^{-v(x)}$):
$\mu^{SO}_v(K_m\cap SO(V)(F_v)) = \lVert2\rVert^{-3}\,\lVert D\rVert^{-1}\,(q^{-1})^m = \lVert8D\rVert^{-1}\,(q^{-1})^m$. -/
theorem muLocSO_congSubSO_norm {s δ m : ℕ} (hD : D ≠ 0)
    (hs : Valued.v (2 : Fv) = exp (-(s : ℤ))) (hδ : Valued.v (algebraMap F Fv (D : F)) = exp (-(δ : ℤ)))
    (hm : 4 * s + 2 * δ + 1 ≤ m) :
    Measure.muLocSO v (diagForm1 D) 1 (congSubSOBin v D m (by omega) : Set _) =
      ENNReal.ofReal ((‖(2 : Fv)‖⁻¹) ^ 3 * ‖algebraMap F Fv (D : F)‖⁻¹ * ((DVR.q 𝔬 : ℝ)⁻¹) ^ m) := by
  rw [muLocSO_congSubSO v hD hs hδ hm, norm_of_valued_exp_binary v hs, norm_of_valued_exp_binary v hδ]
  congr 1
  have hq : (DVR.q 𝔬 : ℝ) ≠ 0 := by exact_mod_cast (q_pos v).ne'
  simp only [inv_pow, inv_inv]
  ring

/-- Every $D\in\mathcal O_F\setminus0$ has an exponent $\delta\in\mathbb N$ with $|D|_v = q^{-\delta}$ (as `Valued.v`). -/
theorem exists_valued_eq_exp_neg (hD : D ≠ 0) :
    ∃ δ : ℕ, Valued.v (algebraMap F Fv (D : F)) = exp (-(δ : ℤ)) := by
  have hD' : (algebraMap F Fv (D : F)) ≠ 0 := by
    rw [map_ne_zero]; exact_mod_cast hD
  have hle : Valued.v (algebraMap F Fv (D : F)) ≤ 1 := by
    rw [← coe_ι]; exact (NF.ι v D).2
  have hne : Valued.v (algebraMap F Fv (D : F)) ≠ 0 := (map_ne_zero _).mpr hD'
  have hlog : WithZero.log (Valued.v (algebraMap F Fv (D : F))) ≤ 0 := by
    have := (WithZero.exp_le_exp (a := WithZero.log (Valued.v (algebraMap F Fv (D : F)))) (b := 0)).mp
      (by rw [WithZero.exp_log hne, WithZero.exp_zero]; exact hle)
    exact this
  refine ⟨(-WithZero.log (Valued.v (algebraMap F Fv (D : F)))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]

end QuadFormsKB.Tamagawa.Measure.Weil
