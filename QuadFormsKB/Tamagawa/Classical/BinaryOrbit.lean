/-
# One class of representations of $1$ by the norm forms $x_0^2 - c\,x_1^2$ over $\mathbb Q$

**Layer:** $\mathbb Q$. For $Q_c = x_0^2 - c\,x_1^2$ over $\mathbb Z$ and $T_0 = \langle 1\rangle$, the $SO(\hat L)$-orbits of
integral finite-adelic frames form a single orbit: the norm-one matrix $M(y) = \begin{pmatrix} y_0 & c y_1\\ y_1 & y_0\end{pmatrix}$
of $y = g e_0\in\hat L$ lies in $SO(\hat L)$ and sends $e_0$ to $y$. Hence $\sum_i n(M_i, 1) = 1$ for
$x_0^2+x_1^2$ and $x_0^2-2x_1^2$.
-/
import QuadFormsKB.Tamagawa.Classical.Basic

open Matrix IsDedekindDomain MulAction NumberField
open scoped ENNReal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

noncomputable section

namespace QuadFormsKB.Tamagawa.Classical

open QuadFormsKB QuadFormsKB.Lattices QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Indefinite QuadFormsKB.Tamagawa.Measure
  QuadFormsKB.Tamagawa.Measure.Weil

section Local

variable {R : Type*} [CommRing R] (c : ℤ)

/-- $M_c(a,b) = \begin{pmatrix} a & cb\\ b & a\end{pmatrix}$, multiplication by $a + b\sqrt c$. -/
def normMat (a b : R) : Matrix (Fin 2) (Fin 2) R := !![a, c * b; b, a]

/-- The Hessian $\mathrm{diag}(2, -2c)$ of $x_0^2 - c x_1^2$. -/
def hessMat : Matrix (Fin 2) (Fin 2) R := !![2, 0; 0, -2 * c]

theorem normMat_orth {a b : R} (h : a ^ 2 - c * b ^ 2 = 1) :
    (normMat c a b)ᵀ * hessMat c * normMat c a b = hessMat (R := R) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normMat, hessMat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h | linear_combination 2 * h | linear_combination (-2 * (c : R)) * h

theorem normMat_mul_neg {a b : R} (h : a ^ 2 - c * b ^ 2 = 1) :
    normMat c a b * normMat c a (-b) = (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normMat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h

theorem normMat_neg_mul {a b : R} (h : a ^ 2 - c * b ^ 2 = 1) :
    normMat c a (-b) * normMat c a b = (1 : Matrix (Fin 2) (Fin 2) R) := by
  simpa using normMat_mul_neg c (a := a) (b := -b) (by simpa using h)

end Local

section Global

variable {F : Type} [Field F] [NumberField F] (c : ℤ) (Q₀ : QuadForm (𝓞 F) 2) (hH : Q₀.hessian = hessMat c) (v : HeightOneSpectrum (𝓞 F))

local notation "QF" => Q₀.map (algebraMap (𝓞 F) F)
local notation "Fv" => v.adicCompletion F
local notation "Ov" => v.adicCompletionIntegers F

include hH in
theorem hessian_loc :
    (QF).hessian.map (algebraMap F Fv) = hessMat c := by
  have h1 : (QF).hessian = Q₀.hessian.map (algebraMap (𝓞 F) F) := by
    ext i j; simp [QuadForm.hessian, QuadForm.map]
  rw [h1, hH]
  ext i j
  have e2 : (algebraMap (𝓞 F) F) 2 = 2 := map_ofNat _ 2
  have e3 : (algebraMap F (v.adicCompletion F)) 2 = 2 := map_ofNat _ 2
  fin_cases i <;> fin_cases j <;> simp [hessMat, e2, e3, map_intCast]

/-- The local isometry $M_c(a, b)$ of norm one. -/
def locElt (a b : Fv) (h : a ^ 2 - c * b ^ 2 = 1) : orthGroup QF Fv :=
  ⟨⟨normMat c a b, normMat c a (-b), normMat_mul_neg c h, normMat_neg_mul c h⟩, by
    rw [mem_orthGroup, hessian_loc c Q₀ hH v]
    exact normMat_orth c h⟩

theorem locElt_val (a b : Fv) (h : a ^ 2 - c * b ^ 2 = 1) :
    ((locElt c Q₀ hH v a b h : orthGroup QF Fv) : GL (Fin 2) Fv).val = normMat c a b := rfl

theorem locElt_mem_stdStab (a b : Fv) (h : a ^ 2 - c * b ^ 2 = 1)
    (ha : a ∈ Ov) (hb : b ∈ Ov) : (locElt c Q₀ hH v a b h : orthGroup QF Fv) ∈ stdStab QF v := by
  refine mem_stdStab_of_integral v QF _ (normMat c ⟨a, ha⟩ ⟨b, hb⟩) (normMat c ⟨a, ha⟩ ⟨-b, neg_mem hb⟩) ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [normMat, locElt]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [normMat, locElt]

/-- The finite-adelic vector $e_0 = (1, 0)$. -/
def eAF : Fin 2 → FiniteAdeleRing (𝓞 F) F := fun i => if i = 0 then 1 else 0

include hH in
/-- **The norm-one element of $SO(\hat L)$ taking $e_0$ to $y$** (placewise $M_c(y_0, y_1)$). -/
theorem exists_mem_KSO_smul_eAF (y : Fin 2 → FiniteAdeleRing (𝓞 F) F) (hy : y ∈ latHat F 2)
    (hq : ∀ v : HeightOneSpectrum (𝓞 F), (y 0 v) ^ 2 - c * (y 1 v) ^ 2 = 1) :
    ∃ k ∈ KSO Q₀, k • eAF = y := by
  let g : OAf QF := ⟨fun v => locElt c Q₀ hH v (y 0 v) (y 1 v) (hq v),
    Filter.Eventually.of_forall fun v => locElt_mem_stdStab c Q₀ hH v _ _ (hq v) (hy 0 v) (hy 1 v)⟩
  have hg : g ∈ soAf QF := fun v => by
    show (normMat c (y 0 v) (y 1 v)).det = 1
    rw [normMat, Matrix.det_fin_two]
    simp
    linear_combination hq v
  refine ⟨⟨g, hg⟩, ?_, ?_⟩
  · rw [KSO, Subgroup.mem_subgroupOf]
    exact (mem_locStab_intVec QF g).2 fun v => locElt_mem_stdStab c Q₀ hH v _ _ (hq v) (hy 0 v) (hy 1 v)
  · funext i
    apply Subtype.ext; funext v
    show (matV Q₀ ((1 : GInfSO Q₀), (⟨g, hg⟩ : SOAf Q₀)) v *ᵥ fun j => (eAF j) v) i = (y i) v
    have h1 : ((1 : FiniteAdeleRing (𝓞 F) F) v) = 1 := rfl
    have h0 : ((0 : FiniteAdeleRing (𝓞 F) F) v) = 0 := rfl
    fin_cases i <;> simp [h1, h0, matV, g, locElt_val, normMat, eAF, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

include hH in
theorem coeff_eq : Q₀.coeff = !![1, 0; 0, -(c : 𝓞 F)] := by
  have h := fun i j => congrFun (congrFun hH i) j
  have h00 := h 0 0
  have h11 := h 1 1
  have h01 := h 0 1
  have u : Q₀.coeff 1 0 = 0 := Q₀.upper (show (0 : Fin 2) < 1 by decide)
  simp [QuadForm.hessian, hessMat, u] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u]
  · have : (2 : 𝓞 F) * Q₀.coeff 0 0 = 2 * 1 := by rw [two_mul, ← h00]; ring
    exact mul_left_cancel₀ two_ne_zero this
  · exact h01
  · have : (2 : 𝓞 F) * Q₀.coeff 1 1 = 2 * (-(c : 𝓞 F)) := by rw [two_mul, h11]; ring
    rw [mul_left_cancel₀ two_ne_zero this]; simp

include hH in
/-- $Q(x) = x_0^2 - c x_1^2$ over any $F$-algebra. -/
theorem evalIn_form {K : Type*} [CommRing K] [Algebra F K] (x : Fin 2 → K) :
    (QF).evalIn K x = x 0 ^ 2 - c * x 1 ^ 2 := by
  rw [QuadForm.evalIn_eq_dotProduct]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, QuadForm.map, coeff_eq c Q₀ hH]
  ring

include hH in
/-- **The rational frame $e_0$** of $\langle 1\rangle$: $Q_0(e_0) = 1$. -/
def e0Frame : RatFrame Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) :=
  ⟨Matrix.of fun i _ => if i = 0 then (1 : F) else 0, by
    refine (compMat_unary_iff (n' := 1) Q₀ 1 _).2 ?_
    have := evalIn_form c Q₀ hH (K := F) (fun i => if i = 0 then (1 : F) else 0)
    show (QF).evalIn F (fun i => if i = 0 then (1 : F) else 0) = _
    rw [this]; simp⟩

include hH in
theorem ratFT_e0Frame : ratFT Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) (e0Frame c Q₀ hH) 0 = eAF := by
  funext j
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) (if j = 0 then (1 : F) else 0) = eAF j
  unfold eAF
  split_ifs <;> simp

theorem eAF_mem_latHat : eAF ∈ latHat F 2 := fun j v => by
  unfold eAF
  split_ifs
  · exact one_mem _
  · exact zero_mem _

include hH in
/-- **$\mathrm{FinOrbit}$ is a singleton** for $x_0^2 - c x_1^2$ and $T_0 = \langle 1\rangle$, $\Xi = e_0$. -/
theorem finOrbit_unique :
    Nonempty (Unique (FinOrbit (n' := 1) Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) (e0Frame c Q₀ hH))) := by
  set Ξ := e0Frame c Q₀ hH with hΞ
  have h1 : (1 : SOAf Q₀) • ratFT Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) Ξ ∈ latHatT F (1 + 1) 1 := by
    rw [one_smul]
    intro j
    rw [Subsingleton.elim j 0, ratFT_e0Frame c Q₀ hH]
    exact eAF_mem_latHat
  refine ⟨⟨⟨Quotient.mk _ ⟨1, h1⟩⟩, fun O => ?_⟩⟩
  induction O using Quotient.inductionOn with | _ b => ?_
  symm
  apply Quotient.sound
  obtain ⟨b, hb⟩ := b
  have hy : (b • ratFT Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) Ξ) 0 = b • eAF := by
    show b • (ratFT Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) Ξ 0) = _
    rw [ratFT_e0Frame c Q₀ hH]
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), ((b • eAF) 0 v) ^ 2 - c * ((b • eAF) 1 v) ^ 2 = 1 := fun v => by
    have key := evalIn_mulVec_of_mem (QF) (((b : OAf QF) v : orthGroup QF (v.adicCompletion F))).2
      (fun j => (eAF j) v)
    rw [evalIn_form c Q₀ hH, evalIn_form c Q₀ hH] at key
    have h0 : ((0 : FiniteAdeleRing (𝓞 F) F) v) = 0 := rfl
    have h1 : ((1 : FiniteAdeleRing (𝓞 F) F) v) = 1 := rfl
    have he0 : eAF 0 v = 1 := by simp [eAF, h1]
    have he1 : eAF 1 v = 0 := by simp [eAF, h0]
    have hre : ∀ i, ((b • eAF) i) v = ((((b : OAf QF) v : orthGroup QF (v.adicCompletion F)) :
        GL (Fin 2) (v.adicCompletion F)).val *ᵥ fun j => (eAF j) v) i := fun i => rfl
    rw [hre, hre, key]
    simp only [he0, he1]
    ring
  obtain ⟨k, hk, hkb⟩ := exists_mem_KSO_smul_eAF c Q₀ hH (b • eAF) (by rw [← hy]; exact hb 0) hq
  refine Set.mem_smul.2 ⟨k, hk, _, rfl, ?_⟩
  funext j
  rw [Subsingleton.elim j 0]
  show k • ((1 : SOAf Q₀) • ratFT Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) Ξ 0) = (b • ratFT Q₀ _ Ξ) 0
  rw [one_smul, ratFT_e0Frame c Q₀ hH, hy, hkb]

include hH in
/-- **One class of representations of $1$** by $x_0^2 - c x_1^2$ ($c \ne 0$) over the genus of $\mathcal O_F^2$:
$\sum_i n(M_i, 1) = 1$. -/
theorem tsum_repCount_one_norm (hc : c ≠ 0) :
    ∑' i, Indefinite.repCount Q₀ (LocalDensity.DVR.unary (1 : 𝓞 F)) i = 1 := by
  have hQ : Q₀.Nondegenerate := by
    unfold QuadForm.Nondegenerate
    rw [hH, hessMat, Matrix.det_fin_two]
    simp [hc]
  have hT : (LocalDensity.DVR.unary (1 : 𝓞 F)).Nondegenerate := by
    unfold QuadForm.Nondegenerate
    simp [LocalDensity.DVR.unary, QuadForm.hessian, QuadForm.diag]
  obtain ⟨u⟩ := finOrbit_unique c Q₀ hH
  rw [tsum_repCount_eq (r := 1) Q₀ hQ _ hT (e0Frame c Q₀ hH)]
  rw [tsum_fintype]
  simp

end Global

section Rat

theorem hessian_up_diag (c : ℤ) :
    (RatBridge.up (QuadForm.diag ![1, -c])).hessian = hessMat (R := 𝓞 ℚ) c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuadForm.hessian, hessMat, RatBridge.up, Siegel.toOQ, QuadForm.map, QuadForm.diag, Matrix.diagonal, map_ofNat]
  all_goals ring1

/-- **One class of representations of $1$ by $x_0^2 + x_1^2$ over the genus**: $\sum_i n(M_i, 1) = 1$. -/
theorem tsum_repCount_one_sumTwoSq :
    ∑' i, Indefinite.repCount (RatBridge.up sumTwoSqZ) (LocalDensity.DVR.unary (1 : 𝓞 ℚ)) i = 1 := by
  have h : sumTwoSqZ = QuadForm.diag ![1, -(-1 : ℤ)] := by
    simp [sumTwoSqZ]
  rw [h]
  exact tsum_repCount_one_norm (-1) _ (hessian_up_diag (-1)) (by norm_num)

/-- **One class of representations of $1$ by $x_0^2 - 2x_1^2$ over the genus**: $\sum_i n(M_i, 1) = 1$. -/
theorem tsum_repCount_one_pell2 :
    ∑' i, Indefinite.repCount (RatBridge.up pell2Z) (LocalDensity.DVR.unary (1 : 𝓞 ℚ)) i = 1 :=
  tsum_repCount_one_norm 2 _ (hessian_up_diag 2) (by norm_num)

end Rat

end QuadFormsKB.Tamagawa.Classical
