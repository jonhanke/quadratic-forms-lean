/-
# Convergence of the degree-one Siegel Eisenstein series for $\operatorname{Re}s > 1$
**Layer:** local bounds at each finite place $v$ of a number field $F$, then global over a totally real $F$.

**Setting.** $Q = \sum_{i<n}a_ix_i^2$, $n = 2m$ (0-based indices), $L_v = \mathcal O_v^n$, $f_v(g, s) = (\omega_v(g)\mathbf 1_{L_v})(0)\,\|g\|_v^{-(s-s_0)}$
(`secS`), $\|g\|_v = \max(|c|_v, |d|_v)$ (`htV`), $\sigma = \operatorname{Re}s$.

**Results (local).**
* `iwasawa`: every $g \in \mathrm{SL}_2(F_v)$ is $n(x)m(t)k$ with $k = \begin{pmatrix}1&0\\y&1\end{pmatrix}$ or $k = w^{-1}n(y)$, $|y|_v \le 1$.
* `exists_norm_secS_le` (every finite place, dyadic included): $|f_v(g, s)| \le C_v\|g\|_v^{-(\sigma+1)}$ with $C_v$ independent of $g$ and $s$.
* `norm_secS_of_good`: at a good place ($v \nmid 2\mathfrak d_F$, $a_i$ units) $|f_v(g, s)| = \|g\|_v^{-(\sigma+1)}$.

**Results (global, $F$ totally real).**
* `archSecS`: the archimedean section of weight $m$ at any $s$ (`isArchSection_archSecS`; at $s_0$ it is `archSec`).
* `exists_norm_finSec_le`: $|f_f(\gamma, s)| \le K\,H_f(\gamma)^{-(\sigma+1)}$, $H_f(\gamma) = \prod_v\|\gamma\|_v$.
* `div_le_finprod_htV`: $H_f(wn(\beta)) \ge |N(c)|/|N(e)|$ for $d = c\beta$, $e = rc + sd \ne 0$ (product formula).
* **`summable_norm_globalSec_archSecS`**, **`eisenstein_archSecS_converges`**: for $\operatorname{Re}s > 1$, $E(g_z, s, \Phi)$ converges absolutely
  over $B(F)\backslash\mathrm{SL}_2(F)$ and equals its Bruhat expansion. The height zeta function $\sum_{P^1(F)}H^{-\sigma}$ (Schanuel) is replaced by the
  Hilbert Eisenstein majorant over the reduced vectors (one per ideal class).

Sources: Weil, Acta Math. 113 (1965), Ch. II [unverified]; Godement (the convergence of Eisenstein series) [unverified]; Bump (1997),
§3.7 [unverified]; Kudla (2008), §1 [unverified].
-/
import QuadFormsKB.SiegelWeil.SiegelWeilFormula

open IsDedekindDomain NumberField MeasureTheory Filter WithZero
open QuadFormsKB.Analysis QuadFormsKB.WeilRep QuadFormsKB.WeilRep.LocalData
open scoped MatrixGroups

set_option linter.unusedSectionVars false

noncomputable section

namespace QuadFormsKB.SiegelWeil

/-! ### The Iwasawa decomposition of $\mathrm{SL}_2(F_v)$ -/

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F
local notation "𝔬" => v.adicCompletionIntegers F

lemma lowerMat_mul_wMat_inv (y : Fv) :
    lowerMat y * (wMat : SL(2, Fv))⁻¹ = (wMat : SL(2, Fv))⁻¹ * nMat (-y) := by
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, nMat, wMat, lowerMat]

lemma lowerMat_add (y y' : Fv) : lowerMat (y + y') = lowerMat y * lowerMat y' := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lowerMat, add_comm]

/-- **The Iwasawa decomposition** of $\mathrm{SL}_2(F_v)$, with an explicit $k$: if $|c|_v \le |d|_v$ then
$g = n(b/d)\,m(d^{-1})\begin{pmatrix}1&0\\c/d&1\end{pmatrix}$ (`eq_n_m_lower`); otherwise $gw = n(\cdot)m(c^{-1})\begin{pmatrix}1&0\\-d/c&1\end{pmatrix}$, so
$g = n(\cdot)m(c^{-1})\,w^{-1}n(d/c)$. -/
@[kb "bump1997" "§3.7 (the Iwasawa decomposition) [unverified]"]
theorem iwasawa (g : SL(2, Fv)) : ∃ (x : Fv) (t : Fvˣ) (y : Fv), ‖y‖ ≤ 1 ∧
    (g = nMat x * mMat t * lowerMat y ∨ g = nMat x * mMat t * ((wMat : SL(2, Fv))⁻¹ * nMat y)) := by
  have hdet := det_eq g
  set c := (g : Matrix (Fin 2) (Fin 2) Fv) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) Fv) 1 1
  by_cases hcd : ‖c‖ ≤ ‖d‖
  · have hd : d ≠ 0 := by
      intro h0
      have hc : c = 0 := norm_le_zero_iff.mp (by rw [h0, norm_zero] at hcd; exact hcd)
      rw [h0, hc] at hdet
      simp at hdet
    refine ⟨_, _, c / d, ?_, Or.inl (eq_n_m_lower g hd)⟩
    rw [norm_div]
    exact div_le_one_of_le₀ hcd (norm_nonneg _)
  · push Not at hcd
    have hc : c ≠ 0 := fun h => by rw [h, norm_zero] at hcd; exact (not_lt.mpr (norm_nonneg d)) hcd
    have h11 : ((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 1 = c := by
      simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two, wMat, c]
    have h10 : ((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 0 = -d := by
      simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two, wMat, d]
    have he := eq_n_m_lower (g * wMat) (by rw [h11]; exact hc)
    rw [h10] at he
    refine ⟨((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 0 1 / ((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 1,
      (Units.mk0 (((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 1) (by rw [h11]; exact hc))⁻¹, d / ((g * wMat : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) 1 1, ?_, Or.inr ?_⟩
    · rw [h11, norm_div]; exact div_le_one_of_le₀ hcd.le (norm_nonneg _)
    · calc g = (g * wMat) * (wMat : SL(2, Fv))⁻¹ := by rw [mul_inv_cancel_right]
        _ = _ := by
          conv_lhs => rw [he]
          rw [mul_assoc _ (lowerMat _), lowerMat_mul_wMat_inv, neg_div, neg_neg]

/-! ### The local bound -/

variable {m : ℕ} (a : Fin (2 * m) → (v.adicCompletion F)ˣ)

lemma norm_chiV_V (t : Fv) : ‖(localDataV v).chiV a t‖ = 1 := by
  show ‖((hilbertSymbol Fv t ((discV a : Fvˣ) : Fv) : ℤ) : ℂ)‖ = 1
  unfold hilbertSymbol; split_ifs <;> simp

lemma norm_chiLoc (d : Fv) : ‖chiLoc v a d‖ = 1 := by
  unfold chiLoc; split_ifs
  · exact norm_chiV_V v a d
  · simp

/-- At a place $v$ there is a level exponent $N$: $|y|_v \le q_v^{-N}$ implies $y$ is in the local level (`LevelV`). -/
lemma exists_levelV : ∃ N : ℕ, ∀ y : Fv, Valued.v y ≤ exp (-(N : ℤ)) → LevelV v a y := by
  have h0 : ∀ i, Valued.v (4 * (a i : Fv)) ≠ 0 := fun i => by
    rw [Valuation.ne_zero_iff]; exact mul_ne_zero (by norm_num) (a i).ne_zero
  set N : ℕ := (∑ i, |log (Valued.v (4 * (a i : Fv)))| + (diffExp v : ℤ)).toNat
  refine ⟨N, fun y hy i => hy.trans ?_⟩
  rw [← exp_log (h0 i), ← exp_add, exp_le_exp]
  have h1 : |log (Valued.v (4 * (a i : Fv)))| ≤ ∑ j, |log (Valued.v (4 * (a j : Fv)))| :=
    Finset.single_le_sum (f := fun j => |log (Valued.v (4 * (a j : Fv)))|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (∑ i, |log (Valued.v (4 * (a i : Fv)))| + (diffExp v : ℤ)) ≤ N := Int.self_le_toNat _
  have h3 := neg_abs_le (log (Valued.v (4 * (a i : Fv))))
  omega

lemma valued_le_one_of_norm {y : Fv} (hy : ‖y‖ ≤ 1) : Valued.v y ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).mp hy

lemma int_lowerMat {y : Fv} (hy : Valued.v y ≤ 1) :
    ∀ i j, Valued.v ((lowerMat y : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [lowerMat, hy]

lemma int_nMat {y : Fv} (hy : Valued.v y ≤ 1) :
    ∀ i j, Valued.v ((nMat y : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [nMat, hy]

lemma wMat_inv_eq : (wMat : SL(2, Fv))⁻¹ = mMat (-1) * wMat := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [mul_assoc, wMat_mul_wMat]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp only [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mMat]

lemma int_wInv_nMat {y : Fv} (hy : Valued.v y ≤ 1) :
    ∀ i j, Valued.v ((((wMat : SL(2, Fv))⁻¹ * nMat y : SL(2, Fv)) : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1 := by
  intro i j
  rw [wMat_inv_eq]
  fin_cases i <;> fin_cases j <;> simp only [Matrix.SpecialLinearGroup.coe_mul] <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, nMat, wMat, mMat, hy]

/-- For integral $k$ the standard section does not depend on $s$: $f_v(k, s) = f_v(k)$ ($\|k\|_v = 1$). -/
lemma secS_of_int (Φ : (localDataV v).Sn (2 * m)) {k : SL(2, Fv)}
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1) (s : ℂ) :
    secS v a Φ k s = secV v a Φ k := by
  unfold secS; rw [htV_eq_one_of_int k hk]; simp

lemma exists_rep_RQ (N : ℕ) (y : Fv) (hy : Valued.v y ≤ 1) :
    ∃ r : RQ v N, Valued.v (y - ((Quotient.out r : 𝔬) : Fv)) ≤ exp (-(N : ℤ)) := by
  let y' : 𝔬 := ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hy⟩
  exact ⟨Ideal.Quotient.mk _ y', (valued_sub_le_iff_mk_eq v N y' _).mp (Ideal.Quotient.mk_out _).symm⟩

/-- **The section is bounded on $\mathrm{SL}_2(\mathcal O_v)$** (every finite place, dyadic included): there is $C$ with
$|f_v(k)| \le C$ for the Iwasawa factors $k = \begin{pmatrix}1&0\\y&1\end{pmatrix}$ and $k = w^{-1}n(y)$, $|y|_v \le 1$. *Proof:* right
$K_0(\mathfrak N_v)$-equivariance (`secS_oneS_mul_K0`): $f_v(w^{-1}n(y)) = f_v(w^{-1})$, and $f_v$ on the lower unipotents depends only on
$y \bmod \mathfrak p_v^N$, a finite set. -/
theorem exists_bound_secV_int (hm : 0 < m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fv, Valued.v y ≤ 1 →
      ‖secV v a (oneS v m) (lowerMat y)‖ ≤ C ∧ ‖secV v a (oneS v m) ((wMat : SL(2, Fv))⁻¹ * nMat y)‖ ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_levelV v a
  have := LocalDensity.DVR.finite_quot_pow (LocalDensity.NF.π v) (LocalDensity.NF.irreducible_π v) N
  let _ : Fintype (RQ v N) := Fintype.ofFinite _
  set C := ‖secV v a (oneS v m) (wMat : SL(2, Fv))⁻¹‖ +
    ∑ r : RQ v N, ‖secV v a (oneS v m) (lowerMat ((Quotient.out r : 𝔬) : Fv))‖
  have hC0 : 0 ≤ C := add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  refine ⟨C, hC0, fun y hy => ⟨?_, ?_⟩⟩
  · obtain ⟨r, hyr⟩ := exists_rep_RQ v N y hy
    set lr : Fv := ((Quotient.out r : 𝔬) : Fv) with hlr
    have hd1 : Valued.v (y - lr) ≤ 1 := hyr.trans (by rw [← exp_zero, exp_le_exp]; omega)
    have hsplit : lowerMat y = lowerMat (lr) * lowerMat (y - lr) := by
      rw [← lowerMat_add, add_sub_cancel]
    have h := secS_oneS_mul_K0 v a hm ha (lowerMat (lr)) (lowerMat (y - lr))
      (int_lowerMat v hd1) (hN _ (by simpa [lowerMat] using hyr)) ((m : ℂ) - 1)
    rw [secS_s₀, secS_s₀, ← hsplit] at h
    rw [h, norm_mul, norm_chiLoc, one_mul]
    refine le_add_of_nonneg_of_le (norm_nonneg _) ?_
    exact Finset.single_le_sum (f := fun r : RQ v N => ‖secV v a (oneS v m) (lowerMat ((Quotient.out r : 𝔬) : Fv))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ r)
  · have h := secS_oneS_mul_K0 v a hm ha (wMat : SL(2, Fv))⁻¹ (nMat y) (int_nMat v hy)
      (by intro i; simp [nMat]) ((m : ℂ) - 1)
    rw [secS_s₀, secS_s₀] at h
    rw [h, norm_mul, norm_chiLoc, one_mul]
    exact le_add_of_le_of_nonneg le_rfl (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- **The section along an Iwasawa decomposition**: for $g = n(x)m(t)k$ with $k$ integral,
$|f_v(g, s)| = \|g\|_v^{-(\sigma+1)}|f_v(k)|$. -/
lemma norm_secS_iwasawa (Φ : (localDataV v).Sn (2 * m)) (x : Fv) (t : Fvˣ) {k : SL(2, Fv)}
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1) (s : ℂ) :
    ‖secS v a Φ (nMat x * mMat t * k) s‖ =
      htV v (nMat x * mMat t * k) ^ (-(s.re + 1)) * ‖secV v a Φ k‖ := by
  have ht : 0 < ‖(t : Fv)‖ := norm_pos_iff.mpr t.ne_zero
  rw [secS_borel, secS_of_int v a Φ hk, htV_borel, htV_eq_one_of_int k hk, mul_one, norm_mul, norm_mul,
    norm_chiV_V, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.inv_rpow ht.le, Real.rpow_neg ht.le,
    inv_inv]
  simp

/-- **The local bound** (every finite place, dyadic included; Godement): there is $C_v \ge 0$ with
$|f_v(g, s)| \le C_v\,\|g\|_v^{-(\operatorname{Re}s+1)}$ for every $g \in \mathrm{SL}_2(F_v)$ and $s \in \mathbb C$,
$f_v$ = `secS` of $\mathbf 1_{\mathcal O_v^{2m}}$, $|a_i|_v \le 1$. -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; bump1997 §3.7 [unverified]"]
theorem exists_norm_secS_le (hm : 0 < m) (ha : ∀ i, Valued.v (a i : Fv) ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SL(2, Fv)) (s : ℂ), ‖secS v a (oneS v m) g s‖ ≤ C * htV v g ^ (-(s.re + 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_secV_int v a hm ha
  refine ⟨C, hC0, fun g s => ?_⟩
  obtain ⟨x, t, y, hy, h | h⟩ := iwasawa v g
  · have hk := int_lowerMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC y (valued_le_one_of_norm v hy)).1 (Real.rpow_nonneg (htV_pos v _).le _)
  · have hk := int_wInv_nMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC y (valued_le_one_of_norm v hy)).2 (Real.rpow_nonneg (htV_pos v _).le _)

/-- **The local factor at a good place**: if $d_v = 0$, $v \nmid 2$ and the $a_i$ are units, then
$|f_v(g, s)| = \|g\|_v^{-(\operatorname{Re}s+1)}$. -/
theorem norm_secS_of_good (hg : IsGoodV v a) (g : SL(2, Fv)) (s : ℂ) :
    ‖secS v a (oneS v m) g s‖ = htV v g ^ (-(s.re + 1)) := by
  have hone : ∀ k : SL(2, Fv), (∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) Fv) i j) ≤ 1) →
      secV v a (oneS v m) k = 1 := by
    intro k hk
    unfold secV sec
    rw [show weilRep (isModel_V v) (a := a) (RingHom.id _) k (oneS v m) = weilRepV v a k (oneS v m) from rfl,
      weilRepV_oneS_of_good v a hg _ hk]
    simp [oneV, ptensor, ballIndV]
  obtain ⟨x, t, y, hy, h | h⟩ := iwasawa v g
  · have hk := int_lowerMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, hone _ hk, norm_one, mul_one]
  · have hk := int_wInv_nMat v (valued_le_one_of_norm v hy)
    rw [h, norm_secS_iwasawa v a _ x t hk, hone _ hk, norm_one, mul_one]

end Local

/-! ### The archimedean section at general $s$ -/

section Arch

open HilbertModular QuadFormsKB.Lattices NumberField.mixedEmbedding
open scoped Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "RP" => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "ιO" => algebraMap (𝓞 F) F

variable (m : ℕ) in
/-- **The archimedean section of weight $m$ at $s$ through $g_z$** ($z \in \mathbb H^d$, $s \in \mathbb C$):
$$f_\infty(\gamma g_z, s) = \prod_wy_w^{(s+1)/2}\cdot\prod_w(c_wz_w + d_w)^{-m}\cdot\Big(\prod_w|c_wz_w + d_w|\Big)^{m-(s+1)},
\qquad \gamma = \begin{pmatrix}a&b\\c&d\end{pmatrix} \in \mathrm{SL}_2(F),$$
the standard section of $I(s, \chi_V)$ of weight $m$ (`archSecS_s₀`: at $s_0 = m - 1$ it is `archSec`). -/
@[kb "kudla2008" "§1 (the standard section of weight l in I(s, χ)) [unverified]; bump1997 §3.7 [unverified]"]
def archSecS (z : InfinitePlace F → UpperHalfPlane) (s : ℂ) (γ : SL(2, F)) : ℂ :=
  (∏ v, ((z v).im : ℂ) ^ ((s + 1) / 2)) *
    eisDen ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1) (fun v => (z v : ℂ)) ^ (-(m : ℤ)) *
      ((‖eisDen ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1)
        (fun v => (z v : ℂ))‖ : ℝ) : ℂ) ^ ((m : ℂ) - (s + 1))

/-- At $s_0 = m - 1$ the section of weight $m$ is the Weil-representation section `archSec`. -/
theorem archSecS_s₀ (m : ℕ) (z : InfinitePlace F → UpperHalfPlane) : archSecS m z ((m : ℂ) - 1) = archSec m z := by
  funext γ
  unfold archSecS archSec
  rw [show (m : ℂ) - ((m : ℂ) - 1 + 1) = 0 by ring, Complex.cpow_zero, mul_one,
    show ((m : ℂ) - 1 + 1) / 2 = (m : ℂ) / 2 by ring]

/-- $|N(t)|_\infty = \prod_v|\sigma_v(t)|$ for the norm of the archimedean model. -/
lemma mixedNorm_eq_prod (t : F) : mixedEmbedding.norm (mixedEmbedding F t) = ∏ v, |realEmb F v t| := by
  rw [norm_eq_prod_real, ← prod_RP_eq (fun v => |realEmb F v t|)]
  exact Finset.prod_congr rfl fun w _ => by rw [← ew_eq_realEmbF]; rfl

/-- **The archimedean section has the Borel law of $I(s, \chi_V)$** for every $s$: `archSecS` is an `IsArchSection` at $s$
($Q$ totally positive). -/
theorem isArchSection_archSecS {m : ℕ} (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (z : InfinitePlace F → UpperHalfPlane) (s : ℂ) :
    IsArchSection (unitsOfInt b hb) (archSecS m z s) s := by
  intro β t γ
  have hpos : ∀ i (w : RP), 0 < ((aInf (unitsOfInt b hb) i : (mixedSpace F)ˣ) : mixedSpace F).1 w := fun i w => by
    show 0 < ew w _
    rw [ew_eq_realEmbF]; exact hbpos i w.1
  have hχ := chiV_mul_md_pow hpos (mixedEmbedding F (t : F)) (fun w => by
    rw [mixedEmbedding_fst]; exact (map_ne_zero _).mpr t.ne_zero)
  have hRP : ∏ w : RP, ((((mixedEmbedding F (t : F)).1 w : ℝ)) : ℂ) ^ m =
      ∏ v, ((realEmb F v (t : F) : ℝ) : ℂ) ^ m := by
    rw [← prod_RP_eq]; exact Finset.prod_congr rfl fun w _ => by rw [mixedEmbedding_fst, ew_eq_realEmbF]
  rw [hRP] at hχ
  set N : ℝ := mixedEmbedding.norm (mixedEmbedding F (t : F))
  have hNeq : N = ∏ v, |realEmb F v (t : F)| := mixedNorm_eq_prod _
  have hN0 : 0 < N := by
    rw [hNeq]; exact Finset.prod_pos fun v _ => abs_pos.mpr ((map_ne_zero _).mpr t.ne_zero)
  have hmd : (localDataInf (F := F)).md (mixedEmbedding F (t : F)) = N := rfl
  rw [hmd] at hχ
  obtain ⟨h0, h1⟩ := bottom_nMat_mMat_mul β t γ
  set E := eisDen ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1) (fun v => (z v : ℂ))
  set P : ℂ := ∏ v, (realEmb F v (((t⁻¹ : Fˣ) : F)) : ℂ) with hPdef
  have hPn : ‖P‖ = N⁻¹ := by
    rw [hPdef, norm_prod, hNeq, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.ofReal_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hPz : P ^ (-(m : ℤ)) = ∏ v, ((realEmb F v (t : F) : ℝ) : ℂ) ^ m := by
    rw [hPdef, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.ofReal_inv, inv_pow, inv_inv]
  unfold archSecS
  rw [h0, h1, eisDen_smul_scalar (((t⁻¹ : Fˣ) : F))
    ((γ : Matrix (Fin 2) (Fin 2) F) 1 0, (γ : Matrix (Fin 2) (Fin 2) F) 1 1)]
  rw [mul_zpow, norm_mul, hPn, hPz, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hN0.le) (norm_nonneg _), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hN0.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_sub _ _ (by exact_mod_cast hN0.ne'), Complex.cpow_natCast, ← hχ]
  have hNm : ((N : ℝ) : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN0.ne')
  have hNs : ((N : ℝ) : ℂ) ^ (s + 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (by exact_mod_cast hN0.ne' : ((N : ℝ) : ℂ) ≠ 0) h.1
  field_simp

/-! ### The finite part: the bound by the height -/

/-- $|N_{F/\mathbb Q}(y)| = \prod_v|\sigma_v(y)|$. -/
def normAbs (y : F) : ℝ := ∏ v, |realEmb F v y|

lemma normAbs_pos {y : F} (hy : y ≠ 0) : 0 < normAbs y :=
  Finset.prod_pos fun v _ => abs_pos.mpr ((map_ne_zero _).mpr hy)

lemma hasFiniteMulSupport_normV {y : F} (hy : y ≠ 0) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (v.adicCompletion F) y‖ :=
  (hasFiniteMulSupport_modK hy).subset fun v hv h' => hv (by
    have e := norm_algebraMap_eq_modK v (Units.mk0 y hy)
    rw [Units.val_mk0] at e
    simp only at h' ⊢; rw [e]; exact h')

/-- **The product formula in norms**: $\prod_v|y|_v = |N(y)|^{-1}$ for $y \in F^\times$. -/
lemma finprod_normV {y : F} (hy : y ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) y‖ = (normAbs y)⁻¹ := by
  have h := prod_modulus_eq_one hy
  rw [mixedNorm_eq_prod] at h
  have e : ∀ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (v.adicCompletion F) y‖ =
      Analysis.Weil.modK (v.adicCompletion F) (algebraMap F (v.adicCompletion F) y) := fun v => by
    have := norm_algebraMap_eq_modK v (Units.mk0 y hy); rwa [Units.val_mk0] at this
  simp_rw [e]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm]
  exact h

lemma htV_locSL_wMat_nMat (v : HeightOneSpectrum (𝓞 F)) (β : F) :
    htV v (locSL v (wMat * nMat β)) = max 1 ‖algebraMap F (v.adicCompletion F) β‖ := by
  rw [map_mul, locSL_wMat, locSL_nMat, htV]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [Matrix.mul_apply, Fin.sum_univ_two, wMat, nMat]

/-- **A lower bound for the height of $wn(\beta)$**: if $c \ne 0$, $d = c\beta$ and $e = rc + sd \ne 0$ with $r, s \in \mathcal O_F$, then
$$\prod_v\max(1, |\beta|_v) \ge |N(c)|/|N(e)|.$$ -/
lemma div_le_finprod_htV (β c e : F) (hc : c ≠ 0) (he : e ≠ 0)
    (hrs : ∃ r s : 𝓞 F, e = ιO r * c + ιO s * (c * β)) :
    normAbs c / normAbs e ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), htV v (locSL v (wMat * nMat β)) := by
  classical
  obtain ⟨r, s, hrs⟩ := hrs
  set g : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    ‖algebraMap F (v.adicCompletion F) e‖ * (‖algebraMap F (v.adicCompletion F) c‖)⁻¹
  have hle : ∀ v, g v ≤ htV v (locSL v (wMat * nMat β)) := by
    intro v
    rw [htV_locSL_wMat_nMat]
    have hcv : 0 < ‖algebraMap F (v.adicCompletion F) c‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr hc)
    have hr : ‖algebraMap F (v.adicCompletion F) (ιO r)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr (valued_algebraMap_O_le_one v r)
    have hs : ‖algebraMap F (v.adicCompletion F) (ιO s)‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).mpr (valued_algebraMap_O_le_one v s)
    have h1 : ‖algebraMap F (v.adicCompletion F) e‖ ≤
        ‖algebraMap F (v.adicCompletion F) c‖ * max 1 ‖algebraMap F (v.adicCompletion F) β‖ := by
      rw [hrs, map_add, map_mul, map_mul, map_mul]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        calc _ ≤ 1 * ‖algebraMap F (v.adicCompletion F) c‖ := by gcongr
          _ ≤ _ := by rw [one_mul]; exact le_mul_of_one_le_right hcv.le (le_max_left _ _)
      · rw [norm_mul, norm_mul]
        calc _ ≤ 1 * (‖algebraMap F (v.adicCompletion F) c‖ * ‖algebraMap F (v.adicCompletion F) β‖) := by
              gcongr
          _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hcv.le
    simp only [g]
    rw [mul_inv_le_iff₀ hcv, mul_comm]
    exact h1
  have hge : ∀ v, 0 ≤ g v := fun v => by positivity
  have hfe := hasFiniteMulSupport_normV he
  have hfc := hasFiniteMulSupport_normV hc
  have hfg : Function.HasFiniteMulSupport g := hfe.mul (hfc.inv)
  have hfh : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => htV v (locSL v (wMat * nMat β)) := by
    by_cases hβ : β = 0
    · subst hβ
      have : (fun v : HeightOneSpectrum (𝓞 F) => htV v (locSL v (wMat * nMat (0 : F)))) = fun _ => 1 := by
        funext v; rw [htV_locSL_wMat_nMat]; simp
      rw [this]; show (Function.mulSupport fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℝ)).Finite; simp
    · refine (hasFiniteMulSupport_normV hβ).subset fun v hv h' => hv ?_
      simp only at h' ⊢
      rw [htV_locSL_wMat_nMat, h', max_self]
  have hS1 : Function.mulSupport g ⊆ ((hfg : (Function.mulSupport g).Finite).toFinset ∪
      (hfh : (Function.mulSupport fun v => htV v (locSL v (wMat * nMat β))).Finite).toFinset : Finset _) := by
    intro v hv; exact Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl ((Set.Finite.mem_toFinset _).mpr hv)))
  have hS2 : (Function.mulSupport fun v => htV v (locSL v (wMat * nMat β))) ⊆
      ((hfg : (Function.mulSupport g).Finite).toFinset ∪
      (hfh : (Function.mulSupport fun v => htV v (locSL v (wMat * nMat β))).Finite).toFinset : Finset _) := by
    intro v hv; exact Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inr ((Set.Finite.mem_toFinset _).mpr hv)))
  have hg : ∏ᶠ v, g v = normAbs c / normAbs e := by
    have hfci : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
        (‖algebraMap F (v.adicCompletion F) c‖)⁻¹ := hfc.inv
    simp only [g]
    rw [finprod_mul_distrib hfe hfci, finprod_inv_distrib, finprod_normV he, finprod_normV hc, inv_inv,
      div_eq_mul_inv, mul_comm]
  rw [← hg, finprod_eq_prod_of_mulSupport_subset _ hS1, finprod_eq_prod_of_mulSupport_subset _ hS2]
  exact Finset.prod_le_prod₀ (fun v _ => hge v) (fun v _ => hle v)

end Arch

/-! ### Absolute convergence of $E(g_z, s)$ for $\operatorname{Re}s > 1$ -/

section Global

open HilbertModular QuadFormsKB.Lattices NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

local notation "ιO" => algebraMap (𝓞 F) F

lemma cvNorm_finprod {ι : Type*} {f : ι → ℂ} (hf : Function.HasFiniteMulSupport f) :
    ‖∏ᶠ i, f i‖ = ∏ᶠ i, ‖f i‖ := by
  have hf' : (Function.mulSupport f).Finite := hf
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf'.toFinset) (fun i hi => hf'.mem_toFinset.mpr hi),
    finprod_eq_prod_of_mulSupport_subset (fun i => ‖f i‖) (s := hf'.toFinset)
      (fun i hi => hf'.mem_toFinset.mpr fun h => hi (by simp only; rw [h, norm_one])), norm_prod]

lemma cvFinprod_rpow {ι : Type*} {f : ι → ℝ} (hf : Function.HasFiniteMulSupport f) (h0 : ∀ i, 0 ≤ f i) (r : ℝ) :
    ∏ᶠ i, f i ^ r = (∏ᶠ i, f i) ^ r := by
  have hf' : (Function.mulSupport f).Finite := hf
  rw [finprod_eq_prod_of_mulSupport_subset (fun i => f i ^ r) (s := hf'.toFinset)
      (fun i hi => hf'.mem_toFinset.mpr fun h => hi (by simp only; rw [h, Real.one_rpow])),
    finprod_eq_prod_of_mulSupport_subset f (s := hf'.toFinset) (fun i hi => hf'.mem_toFinset.mpr hi)]
  exact Real.finsetProd_rpow _ _ (fun i _ => h0 i) r

lemma cvFinprod_le {ι : Type*} {f g : ι → ℝ} (hf : Function.HasFiniteMulSupport f)
    (hg : Function.HasFiniteMulSupport g) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ g i) :
    ∏ᶠ i, f i ≤ ∏ᶠ i, g i := by
  have hf' : (Function.mulSupport f).Finite := hf
  have hg' : (Function.mulSupport g).Finite := hg
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hf'.toFinset ∪ hg'.toFinset)
      (fun i hi => Finset.mem_union.mpr (Or.inl (hf'.mem_toFinset.mpr hi))),
    finprod_eq_prod_of_mulSupport_subset g (s := hf'.toFinset ∪ hg'.toFinset)
      (fun i hi => Finset.mem_union.mpr (Or.inr (hg'.mem_toFinset.mpr hi)))]
  exact Finset.prod_le_prod₀ (fun i _ => h0 i) (fun i _ => h i)

variable {m : ℕ}

lemma hasFiniteMulSupport_htV (γ : SL(2, F)) {a : Fin (2 * m) → Fˣ} :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => htV v (locSL v γ) :=
  (badPlaces_finite a γ).subset fun v hv => by
    by_contra h
    exact hv (htV_eq_one_of_int _ (locSL_int_of_not_bad a h))

/-- **The finite part of the section is bounded by the height** (every finite place, dyadic included): there is $K \ge 0$ with
$$|f_f(\gamma, s)| \le K\,H_f(\gamma)^{-(\operatorname{Re}s+1)},\qquad H_f(\gamma) = \prod_{v<\infty}\|\gamma\|_v,$$
for all $\gamma \in \mathrm{SL}_2(F)$, $s \in \mathbb C$ ($Q = \sum_ib_ix_i^2$ over $\mathcal O_F$, $b_i \ne 0$, $m > 0$). *Proof:* the local bound
`exists_norm_secS_le` at the finitely many places where $V$ is not good, and `norm_secS_of_good` ($C_v = 1$) elsewhere. -/
@[kb "kudla2008" "§1 (the standard section; the bound by the height) [unverified]; Weil (1965) [unverified]"]
theorem exists_norm_finSec_le (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (γ : SL(2, F)) (s : ℂ), ‖finSec (unitsOfInt b hb) γ s‖ ≤
      K * (∏ᶠ v, htV v (locSL v γ)) ^ (-(s.re + 1)) := by
  set a := unitsOfInt b hb
  have hC : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SL(2, v.adicCompletion F)) (s : ℂ),
      ‖secS v (aV a v) (oneS v m) g s‖ ≤ C * htV v g ^ (-(s.re + 1)) :=
    fun v => exists_norm_secS_le v (aV a v) hm (valued_aV_unitsOfInt_le v b hb)
  choose C hC0 hC using hC
  set S := badPlaces a 1
  have hS := badPlaces_finite a 1
  set C' : HeightOneSpectrum (𝓞 F) → ℝ := fun v => if v ∈ S then C v else 1 with hC'
  have hC'0 : ∀ v, 0 ≤ C' v := fun v => by simp only [hC']; split_ifs; exacts [hC0 v, zero_le_one]
  have hC'fin : Function.HasFiniteMulSupport C' :=
    hS.subset fun v hv => by by_contra h; exact hv (show (if v ∈ S then C v else 1) = 1 from ite_eq_right_iff.mpr fun h' => absurd h' h)
  refine ⟨∏ᶠ v, C' v, finprod_nonneg hC'0, fun γ s => ?_⟩
  have hle : ∀ v, ‖secS v (aV a v) (oneS v m) (locSL v γ) s‖ ≤ C' v * htV v (locSL v γ) ^ (-(s.re + 1)) := by
    intro v
    by_cases hv : v ∈ S
    · simp only [hC', hv, ite_true]; exact hC v _ s
    · simp only [hC', hv, ite_false, one_mul]
      exact (norm_secS_of_good v (aV a v) (isGoodV_of_not_bad a (γ := 1) hv) _ s).le
  have hH := hasFiniteMulSupport_htV γ (a := a)
  have hHr : Function.HasFiniteMulSupport fun v => htV v (locSL v γ) ^ (-(s.re + 1)) :=
    hH.subset fun v hv h => hv (by simp only at h ⊢; rw [h, Real.one_rpow])
  have hsec := hasFiniteMulSupport_secS a γ s
  have hnsec : Function.HasFiniteMulSupport fun v => ‖secS v (aV a v) (oneS v m) (locSL v γ) s‖ :=
    hsec.subset fun v hv h => hv (by simp only at h ⊢; rw [h, norm_one])
  unfold finSec
  rw [cvNorm_finprod hsec, ← cvFinprod_rpow hH (fun v => (htV_pos v _).le), ← finprod_mul_distrib hC'fin hHr]
  exact cvFinprod_le hnsec (hC'fin.mul hHr) (fun v => norm_nonneg _) hle

lemma eisDen_one_ne_zero (u : F) (z : InfinitePlace F → UpperHalfPlane) :
    eisDen ((1 : F), u) (fun v => (z v : ℂ)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun v _ => fun h => ?_
  have := congrArg Complex.im h
  simp only [map_one, Complex.ofReal_one, one_mul, Complex.add_im, Complex.ofReal_im, add_zero,
    Complex.zero_im] at this
  exact (z v).im_pos.ne' this

/-- $|f_\infty(wn(u)g_z, s)| = \prod_wy_w^{(\sigma+1)/2}\,|N(z + u)|^{-(\sigma+1)}$, $\sigma = \operatorname{Re}s$. -/
lemma norm_archSecS_wMat_nMat (z : InfinitePlace F → UpperHalfPlane) (s : ℂ) (u : F) :
    ‖archSecS m z s (wMat * nMat u)‖ = (∏ v, (z v).im ^ ((s.re + 1) / 2)) *
      ‖eisDen ((1 : F), u) (fun v => (z v : ℂ))‖ ^ (-(s.re + 1)) := by
  have h0 : ((wMat * nMat u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = (-1) * ((1 : F), u).1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [wMat, nMat, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ((wMat * nMat u : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = (-1) * ((1 : F), u).2 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]; simp [wMat, nMat, Matrix.mul_apply, Fin.sum_univ_two]
  set D := eisDen ((1 : F), u) (fun v => (z v : ℂ))
  have hD : 0 < ‖D‖ := norm_pos_iff.mpr (eisDen_one_ne_zero u z)
  have hN : ‖(∏ v, (realEmb F v (-1 : F) : ℂ))‖ = 1 := by
    simp
  unfold archSecS
  rw [h0, h1, eisDen_smul_scalar, norm_mul (∏ v, (realEmb F v (-1 : F) : ℂ)), hN, one_mul, norm_mul, norm_mul,
    norm_prod, norm_zpow, norm_mul, hN, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have hy : ∀ v, ‖((z v).im : ℂ) ^ ((s + 1) / 2)‖ = (z v).im ^ ((s.re + 1) / 2) := fun v => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (z v).im_pos]; congr 1; simp
  simp_rw [hy]
  rw [mul_assoc]
  congr 1
  have e : ((m : ℂ) - (s + 1)).re = (m : ℝ) - (s.re + 1) := by simp
  rw [e, ← Real.rpow_intCast, Real.rpow_sub hD, Real.rpow_natCast, Int.cast_neg, Int.cast_natCast,
    Real.rpow_neg hD.le, Real.rpow_natCast, Real.rpow_neg hD.le]
  have hm : ‖D‖ ^ m ≠ 0 := pow_ne_zero _ hD.ne'
  have hs : ‖D‖ ^ (s.re + 1) ≠ 0 := (Real.rpow_pos_of_pos hD _).ne'
  field_simp

/-- The weight $W = \mathbf 1_{\text{reduced vectors}}$ (one reduced vector per orbit $U\cdot x$, `IsRedVec`) is admissible of weight $0$. -/
lemma eisWeight_redInd : EisWeight (fun x : F × F => if IsRedVec x then (1 : ℂ) else 0) 0 := by
  refine ⟨fun ε x => by simp [isRedVec_unit_smul_iff], ⟨1, fun x hx => ?_⟩, ⟨1, fun x => by split_ifs <;> simp⟩⟩
  have h : IsRedVec x := by by_contra h; exact hx (by simp [h])
  have hle : ((repIdeal (cuspClass x.1 x.2) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 :=
    FractionalIdeal.coeIdeal_le_one
  have h1 : x.1 ∈ cuspIdeal x.1 x.2 := mem_cuspIdeal_fst _ _
  have h2 : x.2 ∈ cuspIdeal x.1 x.2 := mem_cuspIdeal_snd _ _
  rw [h.2] at h1 h2
  exact ⟨hle h1, hle h2⟩

/-- **Absolute convergence of the Siegel Eisenstein series for $\operatorname{Re}s > 1$** (Godement; Weil 1965), at $g = (g_z, 1)$:
for $F$ totally real, $Q = \sum_{i<n}b_ix_i^2$ totally positive over $\mathcal O_F$, $n = 2m \ge 2$, $z \in \mathbb H^d$ and
$\operatorname{Re}s > 1$, the big-cell terms $f(wn(u)g_z, s)$, $u \in F$, of
$E(g_z, s, \Phi) = \sum_{\gamma\in B(F)\backslash\mathrm{SL}_2(F)}f_\infty(\gamma g_z, s)f_f(\gamma, s)$ are absolutely summable
($f_\infty$ = `archSecS`, the section of weight $m$; $f_v$ = `secS` of $\mathbf 1_{\mathcal O_v^n}$).
*Proof (Weil's, made explicit):* $|f(wn(u)g_z, s)| \le K\prod_wy_w^{(\sigma+1)/2}\big(|N(z+u)|H_f(u)\big)^{-(\sigma+1)}$ by the local bounds
(`exists_norm_finSec_le`); with $(c, d) = t_u(1, u)$ the reduced vector of ratio $u$ (its ideal $c\mathcal O + d\mathcal O$ is one of the
finitely many fixed ideals $\mathfrak b_C$), the product formula gives $H_f(u) \ge |N(c)|/|N(e_C)|$ for a fixed $e_C \in \mathfrak b_C$
(`div_le_finprod_htV`), so the term is at most a constant times $|N(cz + d)|^{-(\sigma+1)}$, summable over $U\backslash F^2$ for
$\sigma + 1 > 2$ (`exists_summable_bound_rpow`). This replaces Schanuel's height zeta function by the Hilbert Eisenstein series. -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series for Re s large) [unverified]; Kudla (2008), §1 [unverified]"]
theorem summable_norm_globalSec_archSecS (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable fun u : F => ‖globalSec (unitsOfInt b hb) (archSecS m z s) s (wMat * nMat u)‖ := by
  set α := s.re + 1 with hα
  have hα0 : 0 < α := by linarith
  obtain ⟨K, hK0, hK⟩ := exists_norm_finSec_le hm b hb
  have hrep : ∀ C : ClassGroup (𝓞 F), ∃ e : 𝓞 F, e ∈ repIdeal C ∧ e ≠ 0 :=
    fun C => Submodule.exists_mem_ne_zero_of_ne_bot (repIdeal_ne_bot C)
  choose e he he0 using hrep
  set E : ℝ := ∑ C, normAbs (ιO (e C)) with hE
  have heE : ∀ C, normAbs (ιO (e C)) ≤ E := fun C =>
    Finset.single_le_sum (f := fun C => normAbs (ιO (e C)))
      (fun C _ => Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ C)
  set W : F × F → ℂ := fun x => if IsRedVec x then 1 else 0 with hW
  obtain ⟨B, hB, hBv⟩ := exists_pos_lt_min (y := imVec z) (imVec_pos z)
  obtain ⟨h, hsum, hbd⟩ := exists_summable_bound_rpow (eisWeight_redInd (F := F)) (σ := α) (by linarith)
    (∑ v, |(z v).re| + 1) hB
  have hz : ∀ v, z v ∈ UpperHalfPlane.verticalStrip (∑ v, |(z v).re| + 1) B := fun v => ⟨by
    have := Finset.single_le_sum (f := fun v => |(z v).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    linarith, (hBv v).le⟩
  set Y := ∏ v, (z v).im ^ (α / 2) with hY
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun v _ => Real.rpow_nonneg (z v).im_pos.le _
  refine ((hsum.comp_injective rho_injective).mul_left (Y * K * E ^ α)).of_nonneg_of_le
    (fun _ => norm_nonneg _) fun u => ?_
  -- the reduced vector of ratio `u`
  set c := redT u with hc
  have hc0 : c ≠ 0 := redT_ne_zero u
  set x : F × F := (c * 1, c * u) with hx
  have hred : IsRedVec x := isRedVec_redT u
  set C := cuspClass x.1 x.2
  have hmem : ιO (e C) ∈ cuspIdeal x.1 x.2 := by
    rw [hred.2]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨e C, he C, rfl⟩
  obtain ⟨r, s', hrs⟩ := mem_cuspIdeal_iff.mp hmem
  have he0' : ιO (e C) ≠ 0 := (map_ne_zero_iff _ algebraMap_O_injective).mpr (he0 C)
  have hlow := div_le_finprod_htV u c (ιO (e C)) hc0 he0' ⟨r, s', by
    rw [hrs, Algebra.smul_def, Algebra.smul_def]; simp [x]⟩
  set H := ∏ᶠ v : HeightOneSpectrum (𝓞 F), htV v (locSL v (wMat * nMat u))
  have hNe : 0 < normAbs (ιO (e C)) := normAbs_pos he0'
  have hNc : 0 < normAbs c := normAbs_pos hc0
  have hE0 : 0 < E := hNe.trans_le (heE C)
  set D := ‖eisDen ((1 : F), u) (fun v => (z v : ℂ))‖
  have hD : 0 < D := norm_pos_iff.mpr (eisDen_one_ne_zero u z)
  -- the orbit term
  have hDx : ‖eisDen (rho u).out (fun v => (z v : ℂ))‖ = D * normAbs c := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε, eisDen_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_unitNorm, one_mul,
      show x = (c * ((1 : F), u).1, c * ((1 : F), u).2) from rfl, eisDen_smul_scalar, norm_mul, norm_prod, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hWo : ‖W (rho u).out‖ = 1 := by
    obtain ⟨ε, hε⟩ := exists_smul_out x
    rw [rho, ← hε]
    simp [hW, isRedVec_unit_smul_iff, hred]
  have hho := hbd z hz (rho u)
  rw [hWo, one_mul, hDx] at hho
  -- the bound
  have hterm : ‖globalSec (unitsOfInt b hb) (archSecS m z s) s (wMat * nMat u)‖ ≤ Y * K * (D * H) ^ (-α) := by
    rw [globalSec, norm_mul, norm_archSecS_wMat_nMat, Real.mul_rpow hD.le (le_trans (by positivity) hlow)]
    calc Y * D ^ (-α) * ‖finSec (unitsOfInt b hb) (wMat * nMat u) s‖ ≤ Y * D ^ (-α) * (K * H ^ (-α)) :=
          mul_le_mul_of_nonneg_left (hK _ s) (mul_nonneg hY0 (Real.rpow_nonneg hD.le _))
      _ = Y * K * (D ^ (-α) * H ^ (-α)) := by ring
  have hlow' : D * normAbs c / E ≤ D * H := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_left hNc.le hNe (heE C)).trans hlow) hD.le
  have hpos : 0 < D * normAbs c / E := by positivity
  have hkey : (D * H) ^ (-α) ≤ E ^ α * (D * normAbs c) ^ (-α) := by
    refine (Real.rpow_le_rpow_of_nonpos hpos hlow' (by linarith)).trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) hE0.le, Real.rpow_neg hE0.le, div_inv_eq_mul, mul_comm]
  calc _ ≤ Y * K * (D * H) ^ (-α) := hterm
    _ ≤ Y * K * (E ^ α * (D * normAbs c) ^ (-α)) := mul_le_mul_of_nonneg_left hkey (mul_nonneg hY0 hK0)
    _ ≤ Y * K * E ^ α * h (rho u) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hho (mul_nonneg (mul_nonneg hY0 hK0) (Real.rpow_nonneg hE0.le _))

/-- **The Siegel Eisenstein series for $\operatorname{Re}s > 1$ converges absolutely over $B(F)\backslash\mathrm{SL}_2(F)$** (at $g = (g_z, 1)$,
same setting as `summable_norm_globalSec_archSecS`), and equals its Bruhat expansion:
$$E(g_z, s, \Phi) = f_\infty(g_z, s) + \sum_{u\in F}f(wn(u)g_z, s).$$
The terms are indexed by the cosets $q \in B(F)\backslash\mathrm{SL}_2(F)$ through any representative $q.\mathrm{out}$. -/
@[kb "weil1965" "Ch. II (convergence of the Eisenstein series) [unverified]; Kudla (2008), §1 [unverified]"]
theorem eisenstein_archSecS_converges (hm : 0 < m) (b : Fin (2 * m) → 𝓞 F) (hb : ∀ i, b i ≠ 0)
    (hbpos : ∀ i v, 0 < realEmb F v (ιO (b i))) (z : InfinitePlace F → UpperHalfPlane) {s : ℂ} (hs : 1 < s.re) :
    (Summable fun q : BQuot F => ‖globalSec (unitsOfInt b hb) (archSecS m z s) s q.out‖) ∧
      eisenstein (unitsOfInt b hb) (isArchSection_archSecS b hb hbpos z s) =
        archSecS m z s 1 + ∑' u : F, globalSec (unitsOfInt b hb) (archSecS m z s) s (wMat * nMat u) := by
  have hsum := summable_norm_globalSec_archSecS hm b hb z hs
  refine ⟨?_, eisenstein_eq_bruhat _ _ hsum.of_norm⟩
  have hInv : ∀ x : Unit ⊕ F, globalSec (unitsOfInt b hb) (archSecS m z s) s (bruhatEquiv (k := F) x).out =
      globalSec (unitsOfInt b hb) (archSecS m z s) s (bruhatRep x) := by
    intro x
    have hrel : QuotientGroup.rightRel (borel F) (bruhatEquiv (k := F) x).out (bruhatRep x) :=
      Quotient.exact (Quotient.out_eq (bruhatEquiv (k := F) x))
    rw [QuotientGroup.rightRel_apply] at hrel
    have := globalSec_borel (unitsOfInt b hb) (isArchSection_archSecS b hb hbpos z s) hrel
      (bruhatEquiv (k := F) x).out
    rw [inv_mul_cancel_right] at this
    exact this.symm
  rw [← (bruhatEquiv (k := F)).summable_iff]
  simp only [Function.comp_def, hInv]
  have h1 : Summable fun u : Unit => ‖globalSec (unitsOfInt b hb) (archSecS m z s) s (bruhatRep (Sum.inl u))‖ :=
    (hasSum_fintype _).summable
  exact (HasSum.sum (f := fun x : Unit ⊕ F =>
    ‖globalSec (unitsOfInt b hb) (archSecS m z s) s (bruhatRep x)‖) h1.hasSum hsum.hasSum).summable

end Global

end QuadFormsKB.SiegelWeil
