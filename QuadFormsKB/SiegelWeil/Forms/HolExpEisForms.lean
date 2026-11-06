/-
# Integer frequencies in the coordinates $t$ are forms over $F$
**Layer:** algebraic (trace duality over a totally real number field $F$).

**Setting.** $(\omega_j)_{j<d}$ = `bq 1` is the $\mathbb Z$-basis of $\mathcal O_F$ behind `oBasis F` ($(b_j)_w = \sigma_w(\omega_j)$, `koecherBasis_apply`) and
$(\omega_j^\vee)_j$ its trace-dual basis ($\operatorname{Tr}_{F/\mathbb Q}(\omega_i\omega_j^\vee) = \delta_{ij}$; `dualElt`). For $n \in \mathbb Z^J$, $J = \{(p, j)\}$,
let $T_n$ be the form with upper coefficients $c_p = \sum_jn_{p,j}\omega_j^\vee$ (`formZ`).

**Results.**
* **`trPair_formZ_zC`**: $\sum_w\operatorname{tr}(\sigma_w(T_{n,G})Z_w(t)) = \sum_{p,j}n_{p,j}t_{p,j}$, hence **`eT_formZ_zC`**: $e_{T_n}(Z(t)) = e^{2\pi i\,n\cdot t}$ (the
  character `HolExp.charZ n t` of `HolExpTorus.lean`).
* `formZ_injective`.
* **`isTotPSD_formZ`**: if $n\cdot y \ge 0$ for every $y$ in the cone $K$ of `coneK`, then $T_n$ is totally positive semidefinite.

Sources: Neukirch, *Algebraic Number Theory*, Ch. III §2 (the trace-dual basis) [unverified]; Freitag, *Siegelsche Modulfunktionen* (1983),
Ch. I [unverified].
-/
import QuadFormsKB.SiegelWeil.Forms.HolExpEisCoord
import QuadFormsKB.SiegelWeil.Forms.FourierPhi
import QuadFormsKB.SiegelWeil.Forms.HolExpConeSum

open Matrix NumberField
open scoped nonZeroDivisors
open QuadFormsKB.HilbertModular QuadFormsKB.WeilRep.Genus QuadFormsKB.SiegelWeil.Forms.HolExp

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil.Forms

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {r : ℕ}

local notation "bq1" => QuadFormsKB.Analysis.bq (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
local notation "dual1" => QuadFormsKB.Analysis.dualElt (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

/-- **The form $T_n$** with upper coefficients $c_p = \sum_jn_{p,j}\omega_j^\vee$. -/
def formZ (n : JR F r → ℤ) : QuadForm F r where
  coeff := fun i k => if h : i ≤ k then dual1 (fun j => n (⟨(i, k), h⟩, j)) else 0
  upper := by
    intro i k hik
    exact dif_neg (not_le.mpr hik)

/-- Symmetrizing: $\sum_{i,k}\sigma(T_G)_{ik}S_{ki} = \sum_{i,k}\sigma(c_{ik})S_{ik}$ for $S$ symmetric. -/
lemma sum_gramT_sym (T : QuadForm F r) (w : InfinitePlace F) (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᵀ = S) :
    ∑ i, ∑ k, (realEmb F w (gramT T i k) : ℂ) * S k i = ∑ i, ∑ k, (realEmb F w (T.coeff i k) : ℂ) * S i k := by
  have hS' : ∀ i k, S k i = S i k := fun i k => congrFun (congrFun hS i) k
  simp only [gramT, QuadForm.hessian, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul,
    map_mul, map_add, Complex.ofReal_mul, Complex.ofReal_add]
  have h2 : ∑ i, ∑ k, (realEmb F w (T.coeff k i) : ℂ) * S k i = ∑ i, ∑ k, (realEmb F w (T.coeff i k) : ℂ) * S i k :=
    Finset.sum_comm
  have hhalf : ((realEmb F w (1 / 2 : F) : ℝ) : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]; push_cast; ring
  calc ∑ i, ∑ k, ((realEmb F w (1 / 2) : ℝ) : ℂ) * ((realEmb F w (T.coeff i k) : ℂ) + (realEmb F w (T.coeff k i) : ℂ)) * S k i
      = (1 / 2) * (∑ i, ∑ k, (realEmb F w (T.coeff i k) : ℂ) * S i k) +
          (1 / 2) * ∑ i, ∑ k, (realEmb F w (T.coeff k i) : ℂ) * S k i := by
        rw [hhalf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hS' i k]; ring
    _ = _ := by rw [h2]; ring

/-- Over an upper triangular coefficient matrix, $\sum_{i,k}c_{ik}\,\mathrm{symOf}(u)_{ik} = \sum_pc_pu_p$. -/
lemma sum_upper_symOf {R : Type*} [CommRing R] (c : Fin r → Fin r → R) (hc : ∀ i k, k < i → c i k = 0)
    (u : SymIdx r → R) :
    ∑ i, ∑ k, c i k * symOf u i k = ∑ p : SymIdx r, c p.1.1 p.1.2 * u p := by
  set f : Fin r × Fin r → R := fun x => c x.1 x.2 * symOf u x.1 x.2 with hf
  have e1 : ∑ i, ∑ k, c i k * symOf u i k = ∑ x, f x := (Fintype.sum_prod_type' (fun i k => c i k * symOf u i k)).symm
  rw [e1, ← Fintype.sum_subtype_add_sum_subtype (fun x : Fin r × Fin r => x.1 ≤ x.2) f]
  have h0 : ∑ x : {x : Fin r × Fin r // ¬ x.1 ≤ x.2}, f x = 0 :=
    Finset.sum_eq_zero fun x _ => by simp only [hf]; rw [hc _ _ (not_le.mp x.2), zero_mul]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [hf, symOf, of_apply, dif_pos p.2]

/-- **The trace pairing in coordinates**: $\sum_w\operatorname{tr}(\sigma_w(T_{n,G})Z_w(t)) = \sum_{p,j}n_{p,j}t_{p,j}$. -/
theorem trPair_formZ_zC (n : JR F r → ℤ) (t : JR F r → ℂ) : trPair (formZ n) (zC t) = dotZ n t := by
  unfold trPair dotZ
  have hsym : ∀ w, (zC t w)ᵀ = zC t w := fun w => symOf_transpose _
  simp_rw [sum_gramT_sym (formZ n) _ _ (hsym _)]
  have hup : ∀ w, ∀ i k : Fin r, k < i → (realEmb F w ((formZ n).coeff i k) : ℂ) = 0 := by
    intro w i k hki; rw [(formZ n).upper hki, map_zero, Complex.ofReal_zero]
  simp_rw [zC, sum_upper_symOf _ (hup _)]
  have hc : ∀ p : SymIdx r, (formZ n).coeff p.1.1 p.1.2 = dual1 (fun j => n (p, j)) := fun p => by
    simp only [formZ, dif_pos p.2]
  simp_rw [hc]
  rw [Finset.sum_comm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : ∀ w, ((oBasis F) j w : ℂ) = (realEmb F w (bq1 j) : ℂ) := fun w => by
    rw [koecherBasis_apply]; rfl
  simp_rw [hb]
  have htr : ∑ w, ((realEmb F w (dual1 (fun j => n (p, j))) : ℂ) * (realEmb F w (bq1 j) : ℂ)) = (n (p, j) : ℂ) := by
    have := sum_realEmb (F := F) (bq1 j * dual1 (fun j => n (p, j)))
    rw [QuadFormsKB.Analysis.trace_bq_mul_dualElt] at this
    simp only [map_mul] at this
    have e : ∑ w, ((realEmb F w (dual1 (fun j => n (p, j))) : ℂ) * (realEmb F w (bq1 j) : ℂ)) =
        ((∑ w, realEmb F w (bq1 j) * realEmb F w (dual1 (fun j => n (p, j))) : ℝ) : ℂ) := by
      push_cast; exact Finset.sum_congr rfl fun w _ => by ring
    rw [e, this]; push_cast; rfl
  calc ∑ w, (realEmb F w (dual1 fun j => n (p, j)) : ℂ) * (t (p, j) * (realEmb F w (bq1 j) : ℂ))
      = t (p, j) * ∑ w, ((realEmb F w (dual1 (fun j => n (p, j))) : ℂ) * (realEmb F w (bq1 j) : ℂ)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    _ = (n (p, j) : ℂ) * t (p, j) := by rw [htr]; ring

/-- **$e_{T_n}(Z(t)) = e^{2\pi i\,n\cdot t}$.** -/
theorem eT_formZ_zC (n : JR F r → ℤ) (t : JR F r → ℂ) : eT (formZ n) (zC t) = charZ n t := by
  rw [eT, trPair_formZ_zC, charZ]

lemma trace_bq_formZ (n : JR F r → ℤ) (p : SymIdx r) (j : Fin (Module.finrank ℚ F)) :
    Algebra.trace ℚ F (bq1 j * (formZ n).coeff p.1.1 p.1.2) = n (p, j) := by
  simp only [formZ, dif_pos p.2]
  exact QuadFormsKB.Analysis.trace_bq_mul_dualElt _ j _

theorem formZ_injective : Function.Injective (formZ (F := F) (r := r)) := by
  intro n n' h
  funext q
  have h1 := trace_bq_formZ n q.1 q.2
  rw [h, trace_bq_formZ] at h1
  exact_mod_cast h1.symm

open Classical in
/-- **The dual cone is the totally positive semidefinite cone**: if $n\cdot y \ge 0$ for all $y \in K$, then $T_n$ is totally positive
semidefinite (test with $Y_{w_0} = vv^{\mathsf T} + \varepsilon$, $Y_w = \varepsilon$ otherwise, and let $\varepsilon \to 0$). -/
theorem isTotPSD_formZ (n : JR F r → ℤ) (hn : ∀ y ∈ coneK F r, 0 ≤ ∑ q, (n q : ℝ) * y q) :
    IsTotPSD (formZ n) := by
  intro w0
  set A : Matrix (Fin r) (Fin r) ℝ := (gramT (formZ n)).map (realEmb F w0) with hA
  have hAs : Aᵀ = A := by rw [hA, ← transpose_map, gramT_transpose]
  refine PosSemidef.of_dotProduct_mulVec_nonneg (by rw [isHermitian_iff_isSymm]; exact hAs) fun v => ?_
  simp only [star_trivial]
  refine HolExp.nonneg_of_forall_pos_add (b := ∑ w, ∑ i, realEmb F w (gramT (formZ n) i i)) fun ε hε => ?_
  set Y : InfinitePlace F → Matrix (Fin r) (Fin r) ℝ :=
    fun w => (if w = w0 then vecMulVec v v else 0) + ε • (1 : Matrix (Fin r) (Fin r) ℝ) with hYdef
  have hYs : ∀ w, (Y w)ᵀ = Y w := fun w => by
    simp only [hYdef, transpose_add, transpose_smul, transpose_one]
    split_ifs <;> simp [transpose_vecMulVec]
  have hYpd : ∀ w, (Y w).PosDef := fun w => by
    have h1 : (ε • (1 : Matrix (Fin r) (Fin r) ℝ)).PosDef := PosDef.one.smul hε
    refine PosDef.posSemidef_add ?_ h1
    split_ifs
    · simpa using posSemidef_vecMulVec_self_star v
    · exact PosSemidef.zero
  obtain ⟨y, hy⟩ := exists_xMat_eq Y hYs
  have hyK : y ∈ coneK F r := fun w => by rw [hy]; exact hYpd w
  have h0 := hn y hyK
  -- the pairing at the real point `y`
  have hpair := trPair_formZ_zC n (cplx y 0)
  have hz : zC (cplx y 0) = fun w => (Y w).map (fun x => (x : ℂ)) := by
    rw [zC_cplx]; funext w; ext i k; simp [zPt, hy, xMat_zero']
  rw [hz] at hpair
  have hdot : dotZ n (cplx y 0) = ((∑ q, (n q : ℝ) * y q : ℝ) : ℂ) := by
    simp [dotZ, cplx]
  rw [hdot] at hpair
  have hreal : ∑ q, (n q : ℝ) * y q =
      ∑ w, ∑ i, ∑ k, realEmb F w (gramT (formZ n) i k) * Y w k i := by
    have e : (trPair (formZ n) fun w => (Y w).map fun x => (x : ℂ)) =
        ((∑ w, ∑ i, ∑ k, realEmb F w (gramT (formZ n) i k) * Y w k i : ℝ) : ℂ) := by
      unfold trPair; push_cast; rfl
    rw [e] at hpair
    exact_mod_cast hpair.symm
  rw [hreal] at h0
  have hcalc : ∑ w, ∑ i, ∑ k, realEmb F w (gramT (formZ n) i k) * Y w k i =
      v ⬝ᵥ A *ᵥ v + ε * ∑ w, ∑ i, realEmb F w (gramT (formZ n) i i) := by
    simp only [hYdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single w0 (fun w _ hw => by simp [hw]) (fun h => absurd (Finset.mem_univ w0) h)]
      simp only [if_true, vecMulVec_apply, dotProduct, mulVec, hA, Matrix.map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ i) h)]
      simp; ring
  linarith [hcalc ▸ h0]

end QuadFormsKB.SiegelWeil.Forms
